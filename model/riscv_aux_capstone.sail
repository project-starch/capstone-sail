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
            let (_, _, _, node_id, _, _) = decode_cap(data);
            assert(mem_tag_set(start_addr, 0b0)); /* clear the tag */
            /* decrement the reference count */
            capnode_rc_dec(node_id);
        };
        start_addr = start_addr + to_bits(xlen_val, caplen_bytes_v);
    }
}
