/* Auxiliary utilities for Capstone */

/* overwrite a register with value v. If v is a capability, the corresponding reference count
is decremented */
function reg_overwrite(v: regtype) -> unit = {
    match(v) {
        CapVal(c) => {
            let (_, _, _, node_id, _, _) = decode_cap(c);
            capnode_rc_dec(node_id); /* when the value is a cap, dec the ref count */
        },
        _ => { () /* nothing to do */ }
    }
}

/* overwrite [addr, addr + size). This will decrement the reference counts of all capabilities stored
in overlapping locations */
function mem_overwrite(addr: xlenbits, size: xlenbits) -> unit = {
    let end_addr = (addr + size - EXTZ(0b1)) & ~(EXTZ(ones(caplen_bytes_w)));
    start_addr = addr & ~(EXTZ(ones(caplen_bytes_w)));
    while(unsigned(start_addr) <= unsigned(end_addr)) do {
        /* load the data */
        let tag = mem_tag_get(start_addr);
        if(tag == 0b1) then {
            /* get the data */
            let (data, _) = read_ram(Read_plain, addr, caplen_bytes_v, false);
            assert(mem_tag_set(start_addr, 0b0)); /* clear the tag */
            /* decrement the reference count */
            capnode_rc_dec(cap_nodeid(data));
        };
        start_addr = start_addr + to_bits(xlen_val, caplen_bytes_v);
    }
}

function reg_moved(v: regtype) -> regtype = {
    match(v) {
        CapVal(c) => {
            if captype_is_linear(cap_type(c)) then {
                RawVal(EXTZ(0b0))
            } else {
                /* if it turns out to be duplicated, increment the ref count */
                capnode_rc_inc(cap_nodeid(c));
                v
            }
        },
        _ => {
            v
        }
    }
}

/* control-flow related */

function redirect_to_cap(c: cap_t) -> unit = {
    /* replace the PC capability */
    let (cursor, start_addr, end_addr, node_id, perm, ty) = decode_cap(c);
    /* the cursor does not matter so we set it to the start address */
    PCCap = encode_cap((start_addr, start_addr, end_addr, node_id, perm, ty));
    /* set the next PC value */
    nextPC = cursor;
}

function get_next_pc_cap() -> cap_t = {
    cap_set_cursor(PCCap, nextPC)
}

/* memory-access related */

function cap_access_allowed(c: cap_t, width: int, req_perm: capperm_t) -> bool = {
    let (cursor, start_addr, end_addr, ni, perm, ty) = decode_cap(c) in
        cap_in_bound(c, cap_cursor(c), width) &
        req_perm <=_p perm & captype_grants_access(ty, capperm_involves_write(req_perm))
}

function capstone_load_mem forall 'n, 0 < 'n & 'n <= 16. (addr: xlenbits, width: atom('n)) -> regtype = {
    let (data, _) = read_ram(Read_plain, addr, width, false);   
    if(width == 16) then {
        if mem_tag(addr) == 0b1 then {
            CapVal(data)
        } else {
            RawVal(data[63..0])
        }
    } else if(width <= 8) then {
        RawVal(EXTZ(data))
    } else {
        assert(false, "Invalid width for load");
        RawVal(EXTZ(0b0))
    }
}

function capstone_store_mem forall 'n, 0 < 'n & 'n <= 16. (addr: xlenbits, width: atom('n), v: regtype) -> bool = {
    match(v) {
        CapVal(c) if width == 16 => {
            write_ram(Write_plain, addr, 16, c, ()) & mem_tag_set(addr, 0b1)
        },
        RawVal(rv) => {
            if width == 8 then {
                write_ram(Write_plain, addr, width, rv[63..0], ())
            } else if width == 4 then {
                write_ram(Write_plain, addr, width, rv[31..0], ())
            } else if width == 2 then {
                write_ram(Write_plain, addr, width, rv[15..0], ())
            } else if width == 1 then {
                write_ram(Write_plain, addr, width, rv[7..0], ())
            } else {
                assert(false, "Invalid width for store");
                false
            }
        },
        _ => {
            false
        }
    }
}

function mem_moved(addr: xlenbits, v: regtype) -> bool = {
    match(v) {
        CapVal(c) => {
            if captype_is_linear(cap_type(c)) then {
                capstone_store_mem(addr, 16, RawVal(EXTZ(0b0)))
            } else {
                /* duplicated, increment the ref count */
                capnode_rc_inc(cap_nodeid(c));
                true
            }
        },
        _ => {
            true
        }
    }
}

/* PC checks */
function check_pc_cap(pc: xlenbits, pc_cap: cap_t) -> bool = {
    cap_in_bound(pc_cap, pc, 4) & captype_grants_access(cap_type(pc_cap), false) &
        CAP_PERM_RX <=_p cap_perm(pc_cap)
}

/* Capstone sysinit */
val init_capstone : unit -> unit effect {wreg} 
function init_capstone() = {
    PCCap = encode_cap((EXTZ(0b0) : xlenbits,
                        EXTZ(0b0) : xlenbits,
                        EXTZ(0b1) : xlenbits << to_bits(xlen_val, xlen_val - 1),
                        EXTZ(0b0) : capnodeidbits,
                        CAP_PERM_RX,
                        CAP_TYPE_LIN));
}

