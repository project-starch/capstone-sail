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
            if width == 16 | width == 8 then {
                /* here we still store 8 bytes only even if the requested
                data width is 16 bytes */
                write_ram(Write_plain, addr, 8, rv[63..0], ())
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
        CAP_PERM_RX <=_p cap_perm(pc_cap) & capnode_query(cap_nodeid(pc_cap)) == 0b1 &
        check_phys_addr_in_partition(pc, false)
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

/* implementation for call, return, and retseal instructions */
/* TODO: do something different for return and retseal */
/* TODO: might need to do something about normal_npc and normal_sp */
function capstone_call(rd: bits(5), rs1: bits(5), calltype: capstone_calltype) -> Retired = {
    let rs1_v : regtype = X(rs1);
    let rd_v : regtype = X(rd);

    let rd_v_moved = reg_moved(rd_v);
    let rs1_v_moved = reg_moved(rs1_v);


    if calltype == CAPSTONE_CALL_CAPEXIT then {
        /* no need to do anything for capexit */
        RETIRE_SUCCESS
    } else if(rs1 == rd) then {
        /* we do not allow the two operands to be the same */
        handle_illegal();
        RETIRE_FAIL
    } else
    match(rd_v) {
        CapVal(c) if captype_is_sealed(cap_type(c)) & capnode_query(cap_nodeid(c)) == 0b1 &
            /* check that the size is sufficient for a context */
            unsigned(cap_bound_size(c)) >= capstone_context_size => {

            let (start_addr, _) = cap_bounds(c);

            let next_pc_cap = get_next_pc_cap();
            let target_val = capstone_load_mem(start_addr, caplen_bytes_v);
            match(target_val) {
                CapVal(pc_c) => { redirect_to_cap(pc_c); },
                _ => {
                    handle_illegal();
                    return RETIRE_FAIL;
                }
            };

            /* TODO: for capenter and capexit, do we save the context? */
            /* TODO: actually, for secure world domain switches, there might also be some more
            clever interface designs which allow the caller to perform register save by itself */
            reg_idx : int = 1;
            while reg_idx < 32 do {
                let cur_addr = start_addr + to_bits(xlen_val, reg_idx * caplen_bytes_v);
                let reg_idx_bits = to_bits(5, reg_idx);
                /* swap the register value */
                let v_to_save : regtype = if reg_idx_bits == rs1 then rs1_v_moved
                    else if reg_idx_bits == rd then rd_v_moved
                    else X(reg_idx_bits);
                if reg_idx == capstone_reg_ret then {
                    /* the original value at the memory location is hence destroyed */
                    mem_overwrite(cur_addr, to_bits(xlen_val, caplen_bytes_v));
                    X(reg_idx_bits) = rd_v; /* TODO: change the type to sealed-ret */
                } else if reg_idx == capstone_reg_arg then {
                    mem_overwrite(cur_addr, to_bits(xlen_val, caplen_bytes_v));
                    X(reg_idx_bits) = rs1_v;
                } else {
                    X(reg_idx_bits) = capstone_load_mem(cur_addr, caplen_bytes_v);
                };
                assert(capstone_store_mem(cur_addr, caplen_bytes_v, v_to_save));
                reg_idx = reg_idx + 1;
            };

            /* save next PC cap */
            assert(capstone_store_mem(start_addr, caplen_bytes_v, CapVal(next_pc_cap)));

            RETIRE_SUCCESS
        },
        _ => {
            handle_illegal();
            RETIRE_FAIL
        }
    }

}

function capstone_gen_genesis() -> cap_t = {
    match(capnode_alloc()) {
        Some(node_id) => {
            encode_cap((sec_mem_base(),
                sec_mem_base(), sec_mem_end(), node_id, CAP_PERM_RWX, CAP_TYPE_LIN));
        },
        None() => {
            assert(false, "cannot allocate a node for genesis capability");
            encode_cap((EXTZ(0b0), EXTZ(0b0), EXTZ(0b0), 
                capnode_id_invalid, CAP_PERM_NA, CAP_TYPE_LIN))
        }
    };
}
