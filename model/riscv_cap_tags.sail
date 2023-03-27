/* Maintaining tags for memory locations to identify Capstone capabilities. */


let cap_tag_base : xlenbits = 0xffffffffff000000 /* TODO: adjust this value */

function regval_tag(v: regtype) -> bits(1) = {
    match(v) {
        CapVal(c) => 0b1,
        _ => 0b0
    }
}

/* check if the memory address is aligned */
function mem_tag_aligned(addr: xlenbits) -> bool = {
    addr[3..0] == EXTZ(0b0) /* FIXME: should not hardcode */
}

/* get location (address) of the tag for a given address */
function mem_tag_addr(addr: xlenbits) -> (xlenbits, bits(3)) = {
    let bit_n = addr >> to_bits(xlen_val, caplen_bytes_w) in
    ((bit_n >> to_bits(xlen_val, 3)) + cap_tag_base, bit_n[2..0])
}

function mem_tag_get(addr: xlenbits) -> bits(1) = {
    if not(mem_tag_aligned(addr)) then
        0b0
    else {
        let (tag_addr, offset) = mem_tag_addr(addr);
        let (data, _) = read_ram(Read_plain, tag_addr, 1, false);
        bit_to_bits(data[unsigned(offset)])
    }
}

function mem_tag_set(addr: xlenbits, tag: bits(1)) -> bool = {
    if mem_tag_aligned(addr) then {
        let (tag_addr, offset) = mem_tag_addr(addr);
        let (data, _) = read_ram(Read_plain, tag_addr, 1, false);
        let new_data : bits(8) = match(tag) {
            0b0 => {
                data & ~(to_bits(8, 1) << EXTZ(offset) : bits(8))
            },
            0b1 => {
                data | (to_bits(8, 1) << EXTZ(offset) : bits(8))
            }
        };
        write_ram(Write_plain, tag_addr, 1, new_data, ())
    } else
        false
}

overload mem_tag = {mem_tag_get, mem_tag_set}
