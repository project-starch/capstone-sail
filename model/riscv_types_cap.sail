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

/*mapping capperm_bits : capperm_t <-> cappermbits = {*/
    /*CAP_PERM_NA <-> 0b000,*/
    /*CAP_PERM_RO <-> 0b001,*/
    /*CAP_PERM_RX <-> 0b010,*/
    /*CAP_PERM_RW <-> 0b011,*/
    /*CAP_PERM_RWX <-> 0b100*/
/*}*/

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


/*mapping captype_bits : captype_t <-> captypebits = {*/
    /*CAP_TYPE_LIN <->     0b000,*/
    /*CAP_TYPE_NONLIN <->  0b001,*/
    /*CAP_TYPE_REV <->     0b010,*/
    /*CAP_TYPE_UNINIT <->  0b011,*/
    /*CAP_TYPE_SEALED <->  0b100,*/
    /*CAP_TYPE_SEALEDRET <-> 0b101*/
/*}*/

// FIXME: somehow those mappings do not reliably work in Ocaml output. Could be a bug in Sail

type capnodeidlen : Int = 31
type capnodeidbits = bits(capnodeidlen)


/* cursor, base addr, end addr, permissions, type */
type decodedcap_t = (xlenbits, xlenbits, xlenbits, capperm_t, captype_t) // FIXME: node id is not included yet

function decode_cap(cap: cap_t) -> decodedcap_t = {
    let ni : capnodeidbits @ ty : captypebits @ perm : cappermbits @
        iE : bits(1) @ t : bits(9) @ tE : bits(3) @ b : bits(11) @
        bE : bits(3) @ cursor : xlenbits = cap;

    T : xlenbits = EXTZ(t);
    T = T << 3;

    B : xlenbits = EXTZ(b);
    B = B << 3;
    E : xlenbits = EXTZ(0b0);
    Lmsb = 0;

    /*if(iE == 0b0) then {*/
        /*T = T | EXTZ(tE);*/
        /*B = B | EXTZ(bE);*/
        /*Lmsb = 0;*/
    /*} else {*/
        /*E = (tE << 3) | bE;*/
        /*Lmsb = 1;*/
    /*};*/

    /*Lcarry = 0;*/

    /*if(T < (B & ((1 << 12) - 1))) then {*/
        /*Lcarry = 1;*/
    /*};*/

    /*T = T | (((B >> 12) + Lcarry + Lmsb) << 12);*/

    // TODO: complete definition

    /*(cursor, EXTZ(0b0) : xlenbits, EXTZ(0b0) : xlenbits, capperm_bits(perm), captype_bits(ty))*/
    (cursor, EXTZ(0b0) : xlenbits, EXTZ(0b0) : xlenbits, CAP_PERM_NA, CAP_TYPE_LIN)
}

function encode_cap(dcap: decodedcap_t) -> cap_t = {
    let (cursor, start_addr, end_addr, perm, ty) = dcap;

    // TODO: complete definition

    EXTZ(0b0)
}

