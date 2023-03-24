/** Revocation node for Capstone */

type capnodelen : Int = 128
type capnodebits = bits(capnodelen)

let capnodelen_bytes_v : int = 16
let capnodelen_bytes_w : int = 4
let capnode_region_base : xlenbits = 0xffffffff00000000 /* TODO: adjust this value */

type capnodecounterlen : Int = 33
type capnodecounterbits = bits(capnodecounterlen)

type capnode_t = (capnodeidbits, capnodeidbits, capnodeidbits,
  capnodecounterbits, bits(1), bits(1))

mapping capnode_bits : capnode_t <-> capnodebits = {
  (depth, next, prev, counter, freed, valid) <->
    depth @ next @ prev @ counter @ freed @ valid
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
