/* Auxiliary utilities for Capstone */

/* overwrite a register with value v. If v is a capability, the corresponding reference count
is decremented */
function reg_overwrite(v: regtype) -> unit = {
    match(v) {
        CapVal(c) => {
            let node_id = cap_nodeid(c);
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
    cap_in_bound(c, cap_cursor(c), width) &
        req_perm <=_p cap_perm(c) & captype_grants_access(cap_type(c), capperm_involves_write(req_perm))
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

function capstone_write_ram forall 'n, 0 < 'n & 'n <= 16. (addr: xlenbits, width: atom('n), data: bits('n * 8)) -> bool = {
    let eares = mem_write_ea(addr, width, false, false, false);
    match(eares) {
        MemException(_) => {
            /* TODO: handle this */
            false
        },
        MemValue(_) => {
            let res = mem_write_value(addr, width, data, false, false, false);
            match(res) {
                MemValue(true) => true,
                _ => false /* TODO: handle this */
            }
        }
    }
}

function capstone_store_mem forall 'n, 0 < 'n & 'n <= 16. (addr: xlenbits, width: atom('n), v: regtype) -> bool = {
    match(v) {
        CapVal(c) if width == 16 => {
            capstone_write_ram(addr, 16, c) & mem_tag_set(addr, 0b1)
        },
        RawVal(rv) => {
            if width == 16 | width == 8 then {
                /* here we still store 8 bytes only even if the requested
                data width is 16 bytes */
                capstone_write_ram(addr, 8, rv[63..0])
            } else if width == 4 then {
                capstone_write_ram(addr, width, rv[31..0])
            } else if width == 2 then {
                capstone_write_ram(addr, width, rv[15..0])
            } else if width == 1 then {
                capstone_write_ram(addr, width, rv[7..0])
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
    PCCap = c;
    /* set the next PC value */
    nextPC = cap_cursor(c);
}

function get_next_pc_cap() -> cap_t = {
    cap_set_cursor(PCCap, nextPC)
}


function capstone_calltype_match(calltype: capstone_calltype, captype: captype_t) -> bool = {
    match(calltype, captype) {
        (CAPSTONE_CALL_NORMAL, CAP_TYPE_SEALED) => true,
        (CAPSTONE_CALL_RETURN, CAP_TYPE_SEALEDRET) => true,
        (CAPSTONE_CALL_RETSEAL, CAP_TYPE_SEALEDRET) => true,
        (CAPSTONE_CALL_CAPENTER, CAP_TYPE_SEALED) => true,
        (CAPSTONE_CALL_CAPEXIT, CAP_TYPE_SEALEDRET) => true,
        (CAPSTONE_CALL_ASYNCEXIT, CAP_TYPE_SEALEDRET) => true,
        _ => false
    }
}

function capstone_sealed_gprs_n(ty: captype_t, size: bits(5)) -> int = {
    match(ty, size == EXTZ(0b0)) {
        (CAP_TYPE_SEALED, _) => unsigned(size),
        (CAP_TYPE_SEALEDRET, true) => 31,
        (CAP_TYPE_SEALEDRET, false) => 0,
        _ => 0
    }
}

/* implementation for call, return, and retseal instructions */
function capstone_call(rd: bits(5), rs1: bits(5), rs2: bits(5), calltype: capstone_calltype) -> Retired = {
    let rs1_v : regtype = X(rs1);
    let rs2_v : xlenbits = X(rs2);
    let rd_v : regtype = X(rd);

    let rd_v_moved = reg_moved(rd_v);
    let rs1_v_moved = reg_moved(rs1_v);

    if calltype == CAPSTONE_CALL_CAPEXIT then {
        /* no need to do anything for capexit */
        RETIRE_SUCCESS
    } else if(calltype != CAPSTONE_CALL_ASYNCEXIT & rs1 == rd) then {
        /* we do not allow the two operands to be the same */
        handle_illegal();
        RETIRE_FAIL
    } else {
        let tv = if calltype == CAPSTONE_CALL_ASYNCEXIT then
            CapVal(switch_buffer_cap)
        else
            rd_v;
        match(rd_v) {
            CapVal(c) if capnode_query(cap_nodeid(c)) == 0b1
                & capstone_calltype_match(calltype, cap_type(c)) /* calltype and cap type must match */
                    /* no need to check the size */
                    /* check when sealing instead */
                    => {
                
                let (ty, _, metadata) = decode_cap(c);
                match(metadata) {
                    SealedCapMetadata(base_addr, size) => {
                        let (out_valid, out_type, out_size, store_to_regs, load_from_regs) :
                                (bool, captype_t, bits(5), bool, bool) = match(calltype) {
                            CAPSTONE_CALL_NORMAL => (true, CAP_TYPE_SEALEDRET, EXTZ(0b0), false, false),
                            CAPSTONE_CALL_RETURN => (false, CAP_TYPE_SEALED, EXTZ(0b0), false, false),
                            CAPSTONE_CALL_RETSEAL => (true, CAP_TYPE_SEALED, rs2_v[4..0], false, false),
                            CAPSTONE_CALL_CAPENTER => (true, CAP_TYPE_SEALEDRET, EXTZ(0b0), true, false), /* TODO: deal with this in details */
                            CAPSTONE_CALL_CAPEXIT => (false, CAP_TYPE_SEALED, EXTZ(0b0), false, true),
                            CAPSTONE_CALL_CAPEXITSEAL => (true, CAP_TYPE_SEALED, rs2_v[4..0], false, true),
                            CAPSTONE_CALL_ASYNCEXIT => (true, CAP_TYPE_SEALED, to_bits(5, 31), false, true)
                        };

                        /* store context. Scenarios: */
                        /* a) call: pc, sp */
                        /* b) return/capexit: nothing */
                        /* c) retsealed/capexitsealed: pc, n GPRs */
                        /* d) capenter: pc, sp in dedicated registers */
                        /* e) asyncexit: full context */

                        /* load remaining context. Scenarios: */
                        /* a) call/capenter: load `size` values */
                        /* b) return/retsealed (size != 0): load nothing */
                        /* c) return/retsealed (size = 0): load full context */
                        /* d) asyncexit/capexit/capexitsealed: load nothing */

                        /* load PC and SP */
                        let (loaded_next_pc_cap, loaded_sp) : (regtype, regtype) = if load_from_regs then {
                            /* load from the special registers */
                            (RawVal(normal_npc), normal_sp)
                        } else {
                            /* load from the sealed region */
                            (capstone_load_mem(base_addr, caplen_bytes_v), capstone_load_mem(base_addr + to_bits(xlen_val, caplen_bytes_v), caplen_bytes_v))
                        };

                        /* store PC and SP */
                        let next_pc_cap = get_next_pc_cap();
                        if store_to_regs then {
                            /* store those to the special registers */
                            normal_npc = nextPC;
                            normal_sp = X(2); /* x2 = sp */
                        } else if out_valid then {
                            /* if this will produce a valid sealed/sealed-ret capability */
                            /* we will need to store them in the sealed region */
                            /* TODO: we are not considering rcupdate yet */
                            assert(capstone_store_mem(base_addr, caplen_bytes_v, CapVal(next_pc_cap)));
                            assert(capstone_store_mem(base_addr + to_bits(xlen_val, caplen_bytes_v), caplen_bytes_v, X(2)));
                        };

                        /* writeback PC and SP */
                        match(loaded_next_pc_cap) {
                            CapVal(pc_c) => { redirect_to_cap(pc_c); },
                            RawVal(v) => {
                                nextPC = v;
                                /* invalidate the original PC capability */
                                /* TODO: handle rcupdate */
                                PCCap = CAP_INVALID;
                            }
                        };

                        /* swap the remaining context */

                        /* compute the number of GPRs to load and store */
                        /* depending on the input and output sealed types and sizes */
                        let n_gprs_to_load : int = capstone_sealed_gprs_n(ty, size);
                        let n_gprs_to_store : int = if out_valid then capstone_sealed_gprs_n(out_type, out_size) else 0;

                        reg_idx : int = 3; /* skipping x0, x1 (ra), and x2 (sp) */
                        /* for now we are making this straightforward */
                        /* TODO: offset */
                        while reg_idx < 32 do {
                            let reg_idx_bits = to_bits(5, reg_idx);
                            let cur_addr = base_addr + to_bits(xlen_val, reg_idx * caplen_bytes_v);
                            let reg_val : regtype = X(reg_idx_bits);
                            let reg_n : int = reg_idx - 3; /* number of regs already considered */
                            if reg_n < n_gprs_to_load then {
                                /* we need to load the value */
                                X(reg_idx_bits) = capstone_load_mem(cur_addr, caplen_bytes_v);
                            };
                            if reg_n < n_gprs_to_store then {
                                /* we need to store the value */
                                assert(capstone_store_mem(cur_addr, caplen_bytes_v, reg_val));
                                /* NOTE: if we store a value that is not loaded, we zero it to avoid secret leakage */
                                if reg_n >= n_gprs_to_load then {
                                    X(reg_idx_bits) = RawVal(EXTZ(0b0));
                                };
                            };
                            reg_idx = reg_idx + 1;
                        };

                        /* deal with ra */
                        let ra_v : regtype = X(1);
                        let cur_addr = base_addr + to_bits(xlen_val, 31 * caplen_bytes_v); /* TODO: double check */
                        if calltype != CAPSTONE_CALL_CAPENTER & out_valid then {
                            /* if we want a valid sealed capability in ra, the capability will reside in ra */
                            /* NOTE: for capenter, the ra will be placed in a special register */
                            /* TODO: check if it is okay to ignore n_gprs_to_load at this point */
                            X(1) = rd_v;
                        } else if n_gprs_to_load == 31 then {
                            /* need to load ra from memory */
                            X(1) = capstone_load_mem(cur_addr, caplen_bytes_v);
                        } else if n_gprs_to_store == 31 then {
                            /* stored but not loaded, we zero the register to protect the data */
                            X(1) = RawVal(EXTZ(0b0));
                        };
                        if n_gprs_to_store == 31 then {
                            /* we need to store ra */
                            assert(capstone_store_mem(cur_addr, caplen_bytes_v, ra_v));
                        };

                        if calltype == CAPSTONE_CALL_CAPENTER then {
                            /* store the invoked sealed capability as switch_buffer_cap */
                            switch_buffer_cap = c;
                        };

                        /* for return types, we need to place the sealed capability in a register */
                        if ty == CAP_TYPE_SEALEDRET then {
                            X(size) = ra_v;
                        };

                        RETIRE_SUCCESS
                    },
                    _ => {
                        handle_illegal();
                        RETIRE_FAIL
                    }
                }

            },
            _ => {
                handle_illegal();
                RETIRE_FAIL
            }
        }
    }
}

function capstone_gen_genesis() -> cap_t = {
    match(capnode_duplicate(capnode_id_invalid, true)) {
        Some(node_id) => {
            encode_cap((CAP_TYPE_LIN, node_id,
                        CommonCapMetadata((sec_mem_base(), sec_mem_base(), sec_mem_end(), CAP_PERM_RWX))));
        },
        None() => {
            assert(false, "cannot allocate a node for genesis capability");
            encode_cap((CAP_TYPE_LIN, capnode_id_invalid,
                        CommonCapMetadata((EXTZ(0b0), EXTZ(0b0), EXTZ(0b0), CAP_PERM_NA))));
        }
    };
}

function capstone_cap_initialised(c: cap_t) -> bool = {
    let (_, end_addr) = cap_bounds(c);
    let cursor = cap_cursor(c);
    /* uninitialised capability with cursor reaching the end address */
    cap_type(c) == CAP_TYPE_UNINIT & cursor == end_addr;
}


function capstone_initialise_nocheck(c: cap_t) -> cap_t = {
    cap_set_type(c, CAP_TYPE_LIN)
}

function capstone_async_exit() -> unit = {
    let _ = capstone_call(EXTZ(0b0), EXTZ(0b0), EXTZ(0b0), CAPSTONE_CALL_ASYNCEXIT);
}
