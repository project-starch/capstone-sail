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


mapping captype_bits : captype_t <-> captypebits = {
    CAP_TYPE_LIN <->     0b000,
    CAP_TYPE_NONLIN <->  0b001,
    CAP_TYPE_REV <->     0b010,
    CAP_TYPE_UNINIT <->  0b011,
    CAP_TYPE_SEALED <->  0b100,
    CAP_TYPE_SEALEDRET <-> 0b101
}

type capnodeidlen : Int = 31
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
    Lmsb = 0b0;

    if(iE == 0b0) then {
        T = T | EXTZ(tE);
        B = B | EXTZ(bE);
        Lmsb = 0b0;
    } else {
        E = (EXTZ(tE) : xlenbits << 3) | EXTZ(bE) : xlenbits;
        Lmsb = 0b0;
    };

    Lcarry = 0b0;

    if(unsigned(T) < unsigned(B & ((EXTZ(0b1) : xlenbits << 12) - EXTZ(0b1) : xlenbits))) then {
        Lcarry = 0b0;
    };

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

    // TODO: complete definition
    let len : xlenbits = end_addr - start_addr;

    E: bits(6) = to_bits(6, 51);
    i: int = 63;
    while(i >= 13 & not(bit_to_bool(len[unsigned(E)]))) do {
        i = i - 1;
        E = E - 1;
    };

    if (unsigned(E) == 0 & not(bit_to_bool(len[12]))) then {
        let iE : bits(1) = 0b0;
        let B : xlenbits = start_addr & (EXTZ(EXTS(0b1) : bits(14)) : xlenbits);
        let T : xlenbits = end_addr & (EXTZ(EXTS(0b1) : bits(12)) : xlenbits);
        let bE : xlenbits = B & EXTZ(0b111) : xlenbits; 
        let b : xlenbits = B >> 3;
        let tE : xlenbits = T & EXTZ(0b111) : xlenbits;
        let t : xlenbits = T >> 3;

        ni @ captype_bits(ty) @ capperm_bits(perm) @ iE @ t[8..0] @
        tE[2..0] @ b[10..0] @ bE[2..0] @ cursor
    } else {
        let iE : bits(1) = 0b1;
        B : xlenbits = (start_addr >> (E + 3)) & EXTZ(EXTS(0b1) : bits(11)) : xlenbits;
        T : xlenbits = (end_addr >> (E + 3)) & EXTZ(EXTS(0b1) : bits(9)) : xlenbits;
        if(unsigned(end_addr) > unsigned((end_addr >> (E + 3)) << (E + 3))) then {
            T = T + EXTZ(0xb1) : xlenbits;
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
        let bE : xlenbits = EXTZ(E) : xlenbits & EXTZ(0b111) : xlenbits;
        let tE : xlenbits = EXTZ(E) : xlenbits >> 3;

        ni @ captype_bits(ty) @ capperm_bits(perm) @ iE @ T[8..0] @
        tE[2..0] @ B[10..0] @ bE[2..0] @ cursor
    }
}


type capxlen : Int = caplen - xlen


