/* Auxiliary utilities for Capstone */

function capstone_cap_is_valid(c: cap_t) -> bool = {
    capnode_query(cap_nodeid(c)) == 0b1
}

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

function cap_access_allowed_offset(c: cap_t, width: int, req_perm: capperm_t, offset: xlenbits) -> bool = {
    cap_in_bound(c, cap_cursor(c) + offset, width) &
        req_perm <=_p cap_perm(c) & captype_grants_access(cap_type(c), capperm_involves_write(req_perm))
}

function cap_access_allowed(c: cap_t, width: int, req_perm: capperm_t) -> bool = {
    cap_access_allowed_offset(c, width, req_perm, EXTZ(0b0))
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


function capstone_load_mem_virt forall 'n, 0 < 'n & 'n <= 16. (vaddr: xlenbits, width: atom('n)) -> (xlenbits, regtype) = {
    /* TODO: check alignment, exception handling */
    match translateAddr(vaddr, Read(Data)) {
        TR_Failure(e, _) => {
            (EXTZ(0b0), RawVal(EXTZ(0b0)))
        },
        TR_Address(paddr, _) => {
            (paddr, capstone_load_mem(paddr, width))
        }
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

function capstone_store_mem_virt forall 'n, 0 < 'n & 'n <= 16. (vaddr: xlenbits, width: atom('n), v: regtype) -> (xlenbits, bool) = {
    match translateAddr(vaddr, Write(Data)) {
        TR_Failure(e, _) => {
            (EXTZ(0b0), false)
        },
        TR_Address(paddr, _) => {
            (paddr, capstone_store_mem(paddr, width, v))
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
        CAP_PERM_RX <=_p cap_perm(pc_cap) & capstone_cap_is_valid(pc_cap) &
        check_phys_addr_in_partition(pc, false)
}


/* control-flow related */

function capstone_redirect_to_cap(c: cap_t) -> unit = {
    /* replace the PC capability */
    PCCap = c;
    /* set the next PC value */
    nextPC = cap_cursor(c);
}

function capstone_redirect_to_addr(addr: xlenbits) -> unit = {
    /* replace the PC capability */
    PCCap = CAP_INVALID;
    /* set the next PC value */
    nextPC = addr;
}


function capstone_redirect(v: regtype) -> unit = {
    match(v) {
        CapVal(c) => {
            capstone_redirect_to_cap(c)
        },
        RawVal(rv) => {
            capstone_redirect_to_addr(rv)
        }
    }
}

function get_next_pc_cap() -> cap_t = {
    cap_set_cursor(PCCap, nextPC)
}

function capstone_calltype_match(calltype: capstone_calltype, captype: captype_t) -> bool = {
    match(calltype, captype) {
        (CAPSTONE_CALL_NORMAL, CAP_TYPE_SEALED) => true,
        (CAPSTONE_CALL_RETURN, CAP_TYPE_SEALEDRET) => true,
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

function capstone_load_mem_n(base_addr: xlenbits, start: int, count: int) -> unit = {
    reg_idx : int = start;
    while reg_idx <= count do {
        let addr = base_addr + reg_idx * caplen_bytes_v;
        let v = capstone_load_mem(addr, caplen_bytes_v);
        X(to_bits(5, reg_idx)) = v;
        reg_idx = reg_idx + 1;
    }
}

function capstone_store_mem_n(base_addr: xlenbits, start: int, count: int) -> unit = {
    reg_idx : int = start;
    while reg_idx <= count do {
        let addr = base_addr + reg_idx * caplen_bytes_v;
        let v : regtype = X(to_bits(5, reg_idx));
        assert(capstone_store_mem(addr, caplen_bytes_v, v));
        reg_idx = reg_idx + 1;
    }
}

function capstone_swap_mem_n(base_addr: xlenbits, start: int, count: int) -> unit = {
    reg_idx : int = start;
    while reg_idx <= count do {
        let addr = base_addr + reg_idx * caplen_bytes_v;
        let v : regtype = X(to_bits(5, reg_idx));
        let old_v = capstone_load_mem(addr, caplen_bytes_v);
        assert(capstone_store_mem(addr, caplen_bytes_v, v));
        X(to_bits(5, reg_idx)) = old_v;
        reg_idx = reg_idx + 1;
    }
}

function capstone_scrub_reg_n(start: int, count: int) -> unit = {
    reg_idx : int = start;
    while reg_idx <= count do {
        X(to_bits(5, reg_idx)) = RawVal(EXTZ(0b0));
        reg_idx = reg_idx + 1;
    }
}

/* swap a regtype value at a memory location */
function capstone_mem_xchg(base: xlenbits, slot: int, v: regtype) -> regtype = {
    let addr = base + to_bits(xlen_val, slot * caplen_bytes_v);
    let old_v = capstone_load_mem(addr, caplen_bytes_v);
    assert(capstone_store_mem(addr, caplen_bytes_v, v));
    old_v
}

function capstone_gen_genesis() -> cap_t = {
    match(capnode_duplicate(capnode_id_invalid, true)) {
        Some(node_id) => {
            encode_cap((node_id,
                        LinearCapMetadata((sec_mem_base(), sec_mem_base(), sec_mem_end(), CAP_PERM_RWX))));
        },
        None() => {
            assert(false, "cannot allocate a node for genesis capability");
            encode_cap((capnode_id_invalid,
                        LinearCapMetadata((EXTZ(0b0), EXTZ(0b0), EXTZ(0b0), CAP_PERM_NA))));
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
    /* TODO: do something here */
    ()
}
