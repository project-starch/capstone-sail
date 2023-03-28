/** Revocation node for Capstone */

type capnodelen : Int = 128
type capnodebits = bits(capnodelen)


/* limit to the number of nodes */
let capnode_lim : int = 65536

let capnode_id_invalid : capnodeidbits = ~(EXTZ(0b0) : capnodeidbits)

register capnode_n : int = 0
/* head of the free list */
register capnode_free_head : capnodeidbits = capnode_id_invalid

let capnodelen_bytes_v : int = 16
let capnodelen_bytes_w : int = 4
let capnode_region_base : xlenbits = 0xffffffff00000000 /* TODO: adjust this value */

type capnodecounterlen : Int = 33
let capnodecounterlen_v = sizeof(capnodecounterlen)
type capnodecounterbits = bits(capnodecounterlen)


struct capnode_t = {
  depth: capnodeidbits,
  next: capnodeidbits,
  prev: capnodeidbits,
  counter: capnodecounterbits,
  freed: bits(1),
  valid: bits(1)
}

val capnode_bits : capnode_t <-> capnodebits

function capnode_bits_forwards(n: capnode_t) -> capnodebits = {
  n.depth @ n.next @ n.prev @ n.counter @ n.freed @ n.valid
}

function capnode_bits_forwards_matches(n: capnode_t) -> bool = {
  true
}

function capnode_bits_backwards(b: capnodebits) -> capnode_t = {
  let depth : capnodeidbits @ next : capnodeidbits @ prev : capnodeidbits
    @ counter : capnodecounterbits @ freed : bits(1) @ valid : bits(1) = b in
  struct {
    depth = depth,
    next = next,
    prev = prev,
    counter = counter,
    freed = freed,
    valid = valid
  }
}

function capnode_bits_backwards_matches(b: capnodebits) -> bool = {
  true
}

function capnode_addr(node_id : capnodeidbits) -> xlenbits = {
  capnode_region_base + (EXTZ(node_id) : xlenbits << to_bits(xlen_val, capnodelen_bytes_w))
}

function capnode_read(node_id : capnodeidbits) -> capnode_t = {
  /* the metadata is not used currently */
  let (data, _) = read_ram(Read_plain, capnode_addr(node_id), 16, false) in /* can only use 16 here for some reason */
    capnode_bits(data)
}

function capnode_write(node_id : capnodeidbits, node : capnode_t) -> bool = {
  write_ram(Write_plain, capnode_addr(node_id), 16, capnode_bits(node), ())
}

function capnode_query(node_id : capnodeidbits) -> bits(1) = {
  let n = capnode_read(node_id) in
    n.valid
}

/* returns a new node potentially from the free list */
function capnode_alloc() -> option(capnodeidbits) = {
  if (capnode_n >= capnode_lim & capnode_free_head == capnode_id_invalid) then {
    None()
  } else {
    let new_node_id =
      if(capnode_n < capnode_lim) then {
        let v = capnode_n;
        capnode_n = v + 1;
        to_bits(capnodeidlen_v, v)
      } else {
        let n = capnode_free_head;
        let node = capnode_read(n);
        capnode_free_head = node.next;
        n
      }
    in
      Some(new_node_id)
  }
}

/* revoke with a given node, which invalidates all nodes in the subtree */
function capnode_revoke(node_id : capnodeidbits) -> unit = {
  let root_node = capnode_read(node_id);
  cur_node_id : capnodeidbits = root_node.next;
  cur_node_intree : bool = true;
  while(cur_node_id != capnode_id_invalid & cur_node_intree) do {
    let cur_node = capnode_read(cur_node_id); 
    if(unsigned(cur_node.depth) <= unsigned(root_node.depth)) then {
      cur_node_intree = false;
    } else {
      let new_node = {cur_node with valid = 0b0}; /* invalidate the node */
      assert(capnode_write(cur_node_id, new_node));
      cur_node_id = cur_node.next;
    }
  };
  let new_root_node = {root_node with next = cur_node_id} in
    assert(capnode_write(node_id, new_root_node));
  if(cur_node_id != capnode_id_invalid) then {
    let cur_node = capnode_read(cur_node_id) in
      assert(capnode_write(cur_node_id, {cur_node with prev = node_id}));
  };
}

/* updates the reference count */
function capnode_rcupdate(node_id : capnodeidbits, delta : capnodecounterbits) -> unit = {
  let node = capnode_read(node_id);
  new_node = {node with counter = node.counter + delta};
  if (new_node.counter == EXTZ(0b0)) then {
    /* free the node when the counter reaches zero */
    new_node.freed = 0b1;
    new_node.next = capnode_free_head;
    capnode_free_head = node_id;
    assert(capnode_write(node_id, new_node));
  };
}

/* special rc update functions for convenience */
function capnode_rc_inc(node_id : capnodeidbits) -> unit = {
  capnode_rcupdate(node_id, to_bits(capnodecounterlen_v, 1));
}

function capnode_rc_dec(node_id : capnodeidbits) -> unit = {
  capnode_rcupdate(node_id, to_bits(capnodecounterlen_v, -1));
}

/* duplicate node */
function capnode_duplicate(node_id : capnodeidbits, as_child : bool) -> option(capnodeidbits) = {
  let alloc = capnode_alloc();
  match(alloc) {
    Some(new_node_id) => {
      old_node = capnode_read(node_id);
      new_node = {old_node with prev = node_id};
      if not(as_child) then
        new_node.depth = old_node.depth + 1;
      old_node.next = new_node_id;
      assert(capnode_write(node_id, old_node));
      assert(capnode_write(new_node_id, new_node));
    },
    None() => {
      ()
    }
  };
  alloc
}
