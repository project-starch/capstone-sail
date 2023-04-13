type cap_t = caplenbits

enum capperm_t = {
    CAP_PERM_NA,
    CAP_PERM_RO,
    CAP_PERM_RX,
    CAP_PERM_RW,
    CAP_PERM_RWX
}

type cappermlen : Int = 3
type cappermbits = bits(cappermlen)

mapping capperm_bits : capperm_t <-> cappermbits = {
    CAP_PERM_NA <-> 0b000,
    CAP_PERM_RO <-> 0b001,
    CAP_PERM_RX <-> 0b010,
    CAP_PERM_RW <-> 0b011,
    CAP_PERM_RWX <-> 0b100
}

mapping capperm_string : capperm_t <-> string = {
    CAP_PERM_NA <-> "no access",
    CAP_PERM_RO <-> "read-only",
    CAP_PERM_RX <-> "read-execute",
    CAP_PERM_RW <-> "read-write",
    CAP_PERM_RWX <-> "read-write-execute"
}

infix 4 <=_p
function operator <=_p (perm_a : capperm_t, perm_b : capperm_t) -> bool = {
    match((perm_a, perm_b)) {
        (p1, p2) if p1 == p2 => true,
        (CAP_PERM_NA, _) => true,
        (CAP_PERM_RO, p2) if p2 != CAP_PERM_NA => true,
        (CAP_PERM_RX, CAP_PERM_RWX) => true,
        (CAP_PERM_RW, CAP_PERM_RWX) => true,
        _ => false
    }
}

function capperm_involves_write(perm : capperm_t) -> bool = {
    perm == CAP_PERM_RW | perm == CAP_PERM_RWX
}

enum captype_t = {
    CAP_TYPE_LIN,
    CAP_TYPE_NONLIN,
    CAP_TYPE_REV,
    CAP_TYPE_UNINIT,
    CAP_TYPE_SEALED,
    CAP_TYPE_SEALEDRET
}


type captypelen : Int = 3
type captypebits = bits(captypelen)

mapping captype_string : captype_t <-> string = {
    CAP_TYPE_LIN <-> "linear",
    CAP_TYPE_NONLIN <-> "non-linear",
    CAP_TYPE_REV <-> "revocation",
    CAP_TYPE_UNINIT <-> "uninitialised",
    CAP_TYPE_SEALED <-> "sealed",
    CAP_TYPE_SEALEDRET <-> "sealed-return"
}

mapping captype_bits : captype_t <-> captypebits = {
    CAP_TYPE_LIN <->     0b000,
    CAP_TYPE_NONLIN <->  0b001,
    CAP_TYPE_REV <->     0b010,
    CAP_TYPE_UNINIT <->  0b011,
    CAP_TYPE_SEALED <->  0b100,
    CAP_TYPE_SEALEDRET <-> 0b101
}

function captype_grants_access(ty: captype_t, is_write: bool) -> bool = {
    /* FIXME: the handling of uninitialised cap is not properly done yet */
    /* uninitialised cap is only allowed to be written to */
    ty == CAP_TYPE_LIN | ty == CAP_TYPE_NONLIN | (is_write & ty == CAP_TYPE_UNINIT)
}

/* does the capability type not allow duplicating? */
function captype_is_linear(ty: captype_t) -> bool = {
    ty != CAP_TYPE_NONLIN
}

function captype_is_sealed(ty: captype_t) -> bool = {
    ty == CAP_TYPE_SEALED | ty == CAP_TYPE_SEALEDRET
}

type capnodeidlen : Int = 31
let capnodeidlen_v = sizeof(capnodeidlen)
type capnodeidbits = bits(capnodeidlen)


/* cursor, base addr, end addr, permissions, type */
type decodedcap_t = (xlenbits, xlenbits, xlenbits, capnodeidbits,
                    capperm_t, captype_t)

function decode_cap(cap: cap_t) -> decodedcap_t = {
    let ni : capnodeidbits @ ty : captypebits @ perm : cappermbits @
        iE : bits(1) @ t : bits(9) @ tE : bits(3) @ b : bits(11) @
        bE : bits(3) @ cursor : xlenbits = cap;

    T : xlenbits = EXTZ(t);
    T = T << 3;

    B : xlenbits = EXTZ(b);
    B = B << 3;
    E : xlenbits = EXTZ(0b0);
    Lmsb = if(iE == 0b0) then {
        T = T | EXTZ(tE);
        B = B | EXTZ(bE);
        0b0
    } else {
        E = (EXTZ(tE) : xlenbits << 3) | EXTZ(bE) : xlenbits;
        0b1
    };

    Lcarry = if(unsigned(T) < unsigned(B[11..0])) then 0b1 else 0b0;

    T = T | (((B >> 12) + (EXTZ(Lcarry) : xlenbits) + (EXTZ(Lmsb) : xlenbits)) << 12);

    top : xlenbits = (cursor & (((EXTS(0b1) : xlenbits) >> (unsigned(E) + 14)) << (unsigned(E) + 14))) | (T << unsigned(E));
    base : xlenbits = (cursor & (((EXTS(0b1) : xlenbits) >> (unsigned(E) + 14)) << (unsigned(E) + 14))) | (B << unsigned(E));

    let R : xlenbits = (B >> 11) - (EXTZ(0b1) : xlenbits);
    let A : xlenbits = (cursor >> (unsigned(E) + 11)) & (EXTZ(0b111) : xlenbits);
    let T3 : xlenbits = (T >> 11) & (EXTZ(0b111) : xlenbits);
    let B3 : xlenbits = (B >> 11) & (EXTZ(0b111) : xlenbits);

    let condAR = unsigned(A) < unsigned(R);
    let condTR = unsigned(T3) < unsigned(R);
    let condBR = unsigned(B3) < unsigned(R);

    if(not(condAR) & condTR) then {
        top = top + ((EXTZ(0b1) : xlenbits) << (unsigned(E) + 14));
    } else if(condAR & not(condTR)) then {
        top = top - ((EXTZ(0b1) : xlenbits) << (unsigned(E) + 14));
    };

    if(not(condAR) & condBR) then {
        base = base + ((EXTZ(0b1) : xlenbits) << (unsigned(E) + 14));
    } else if(condAR & not(condBR)) then {
        base = base - ((EXTZ(0b1) : xlenbits) << (unsigned(E) + 14));
    };

    (cursor, base, top, ni, 
        capperm_bits(perm), captype_bits(ty))
}

function encode_cap(dcap: decodedcap_t) -> cap_t = {
    let (cursor, start_addr, end_addr, ni, perm, ty) = dcap;

    assert(unsigned(end_addr) >= unsigned(start_addr), "Capability end address must not be lower than the start address.");

    let len : xlenbits = end_addr - start_addr;

    E: bits(6) = to_bits(6, 51);
    i: bits(6) = to_bits(6, 63);
    while(unsigned(i) >= 13 & not(bit_to_bool(len[unsigned(i)]))) do {
        i = i - 1;
        E = E - 1;
    };

    if (unsigned(E) == 0 & not(bit_to_bool(len[12]))) then {
        let iE : bits(1) = 0b0;
        let B : xlenbits = EXTZ(start_addr[13..0]);
        let T : xlenbits = EXTZ(end_addr[11..0]);
        let bE : xlenbits = EXTZ(B[2..0]); 
        let b : xlenbits = B >> 3;
        let tE : xlenbits = EXTZ(T[2..0]);
        let t : xlenbits = T >> 3;

        ni @ captype_bits(ty) @ capperm_bits(perm) @ iE @ t[8..0] @
        tE[2..0] @ b[10..0] @ bE[2..0] @ cursor
    } else {
        let iE : bits(1) = 0b1;
        B : xlenbits = EXTZ((start_addr >> (E + 3))[10..0]);
        T : xlenbits = EXTZ((end_addr >> (E + 3))[8..0]);
        if(unsigned(end_addr) > unsigned((end_addr >> (E + 3)) << (E + 3))) then {
            T = T + 1;
            j : int = 1;
            while(j <= 9) do {
                if(T == (EXTZ(0b1) : xlenbits) << to_bits(6, j)) then {
                    T = EXTZ(0x0) : xlenbits;
                    B = B >> 1;
                    E = E + 1;
                };
                j = j + 1;
            };
        };
        let bE : xlenbits = EXTZ(E[2..0]);
        let tE : xlenbits = EXTZ(E) : xlenbits >> 3;

        ni @ captype_bits(ty) @ capperm_bits(perm) @ iE @ T[8..0] @
        tE[2..0] @ B[10..0] @ bE[2..0] @ cursor
    }
}


type capxlen : Int = caplen - xlen

function cap_set_type(cap: cap_t, new_ty: captype_t) -> cap_t = {
    let (cursor, start_addr, end_addr, ni, perm, ty) = decode_cap(cap) in
        encode_cap((cursor, start_addr, end_addr, ni, perm, new_ty))
}

function cap_set_nodeid(cap: cap_t, new_ni: capnodeidbits) -> cap_t = {
    let (cursor, start_addr, end_addr, ni, perm, ty) = decode_cap(cap) in
        encode_cap((cursor, start_addr, end_addr, new_ni, perm, ty))
}

function cap_set_perm(cap: cap_t, new_perm: capperm_t) -> cap_t = {
    let (cursor, start_addr, end_addr, ni, perm, ty) = decode_cap(cap) in
        encode_cap((cursor, start_addr, end_addr, ni, new_perm, ty))
}

function cap_set_bound(cap: cap_t, new_start: xlenbits, new_end: xlenbits) -> cap_t = {
    let (cursor, start_addr, end_addr, ni, perm, ty) = decode_cap(cap) in
        /* encode_cap((cursor, new_start, new_end, ni, perm, ty)) */
        encode_cap((new_start, new_start, new_end, ni, perm, ty))
}

function cap_set_cursor(cap: cap_t, new_cursor: xlenbits) -> cap_t = {
    let (cursor, start_addr, end_addr, ni, perm, ty) = decode_cap(cap) in
        encode_cap((new_cursor, start_addr, end_addr, ni, perm, ty))
}

/** set both the bound and the cursor at the same time */
function cap_set_bound_cursor(cap: cap_t, new_cursor: xlenbits, new_start: xlenbits, new_end: xlenbits) -> cap_t = {
    let (cursor, start_addr, end_addr, ni, perm, ty) = decode_cap(cap) in
        encode_cap((new_cursor, new_start, new_end, ni, perm, ty))
}


function cap_shrink(cap: cap_t, new_start: xlenbits, new_end: xlenbits) -> option(cap_t) = {
    let (cursor, start_addr, end_addr, ni, perm, ty) = decode_cap(cap);
    if unsigned(start_addr) <= unsigned(new_start) & 
        unsigned(new_start) <= unsigned(new_end) &
        unsigned(new_end) <= unsigned(end_addr) then
        Some(encode_cap((cursor, new_start, new_end, ni, perm, ty)))
    else
        None()
}

function cap_tighten(cap: cap_t, new_perm: capperm_t) -> option(cap_t) = {
    let (cursor, start_addr, end_addr, ni, perm, ty) = decode_cap(cap);
    if new_perm <=_p perm then
        Some(encode_cap((cursor, start_addr, end_addr, ni, new_perm, ty)))
    else
        None()
}

function cap_type(cap: cap_t) -> captype_t = {
    let (_, _, _, _, _, ty) = decode_cap(cap) in ty
}

function cap_perm(cap: cap_t) -> capperm_t = {
    let (_, _, _, _, perm, _) = decode_cap(cap) in perm
}

function cap_cursor(cap: cap_t) -> xlenbits = {
    let (cursor, _, _, _, _, _) = decode_cap(cap) in cursor
}

function cap_nodeid(cap: cap_t) -> capnodeidbits = {
    let (_, _, _, nid, _, _) = decode_cap(cap) in nid
}

function cap_bounds(cap: cap_t) -> (xlenbits, xlenbits) = {
    let (_, start_addr, end_addr, _, _, _) = decode_cap(cap) in
        (start_addr, end_addr)
}

function cap_bound_size(cap: cap_t) -> xlenbits = {
    let (_, start_addr, end_addr, _, _, _) = decode_cap(cap) in
        end_addr - start_addr
}

function cap_in_bound(cap: cap_t, addr: xlenbits, width: int) -> bool = {
    let (_, start_addr, end_addr, _, _, _) = decode_cap(cap) in
        unsigned(addr) >= unsigned(start_addr) & unsigned(addr) + width <= unsigned(end_addr)
}


/* capability-related errors */

enum caperror_t = {
    CAP_ERROR_INVALID_PC
}

/* pretty-print capability */

function print_cap(s: string, cap: cap_t) -> unit = {
    /* print out bounds for now */
    let (_, start_addr, end_addr, _, perm, ty) = decode_cap(cap);
    print_string("Print Cap ", s);
    print_string("Type = ", captype_string(ty));
    print_string("Perm = ", capperm_string(perm));
    print_bits("Start address = ", start_addr);
    print_bits("End address = ", end_addr);
}

function cap_string(cap: cap_t) -> string = {
    let (cursor, start_addr, end_addr, ni, perm, ty) = decode_cap(cap) in
        "Cap(" ^ BitStr(cursor) ^ sep() ^
        BitStr(start_addr) ^ sep() ^
        BitStr(end_addr) ^ sep() ^
        BitStr(ni) ^ sep() ^
        capperm_string(perm) ^ sep() ^
        captype_string(ty) ^ ")"
}
