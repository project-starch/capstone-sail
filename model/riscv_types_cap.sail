type cap_t = caplenbits

enum capperm_t = {
    CAP_PERM_NA,
    CAP_PERM_XO,
    CAP_PERM_WO,
    CAP_PERM_WX,
    CAP_PERM_RO,
    CAP_PERM_RX,
    CAP_PERM_RW,
    CAP_PERM_RWX
}

type cappermlen : Int = 3
type cappermbits = bits(cappermlen)

mapping capperm_bits : capperm_t <-> cappermbits = {
    CAP_PERM_NA <-> 0b000,
    CAP_PERM_XO <-> 0b001,
    CAP_PERM_WO <-> 0b010,
    CAP_PERM_RO <-> 0b100,
    CAP_PERM_WX <-> 0b011,
    CAP_PERM_RX <-> 0b101,
    CAP_PERM_RW <-> 0b110,
    CAP_PERM_RWX <-> 0b111
}

mapping capperm_string : capperm_t <-> string = {
    CAP_PERM_NA <-> "no access",
    CAP_PERM_XO <-> "execute-only",
    CAP_PERM_WO <-> "write-only",
    CAP_PERM_RO <-> "read-only",
    CAP_PERM_WX <-> "write-execute",
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
    CAP_TYPE_SEALEDRET,
    CAP_TYPE_EXIT /* new type for TransCapstone */
}


type captypelen : Int = 3
type captypebits = bits(captypelen)

mapping captype_string : captype_t <-> string = {
    CAP_TYPE_LIN <-> "linear",
    CAP_TYPE_NONLIN <-> "non-linear",
    CAP_TYPE_REV <-> "revocation",
    CAP_TYPE_UNINIT <-> "uninitialised",
    CAP_TYPE_SEALED <-> "sealed",
    CAP_TYPE_SEALEDRET <-> "sealed-return",
    CAP_TYPE_EXIT <-> "exit"
}

mapping captype_bits : captype_t <-> captypebits = {
    CAP_TYPE_LIN <->     0b000,
    CAP_TYPE_NONLIN <->  0b001,
    CAP_TYPE_REV <->     0b010,
    CAP_TYPE_UNINIT <->  0b011,
    CAP_TYPE_SEALED <->  0b100,
    CAP_TYPE_SEALEDRET <-> 0b101,
    CAP_TYPE_EXIT <->   0b110
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

type common_metadata_t = (xlenbits, xlenbits, xlenbits, capperm_t)

/* metadata for decoded capability without type and node id (which are common)*/
union decodedcap_metadata_t = {
    /* cursor, base addr, end addr, permissions */
    LinearCapMetadata : common_metadata_t,
    /* cursor, base addr, end addr, permissions */
    NonLinearCapMetadata : common_metadata_t,
    /* cursor, base addr, end addr, permissions */
    RevocationCapMetadata : common_metadata_t,
    /* cursor, base addr, end addr, permissions */
    UninitialisedCapMetadata : common_metadata_t,
    /* base addr, async */
    SealedCapMetadata : (xlenbits, bits(2)),
    /* cursor, base addr, async, reg */
    SealedRetCapMetadata : (xlenbits, xlenbits, bits(2), bits(5)),
    /* cursor, base addr */
    ExitCapMetadata : (xlenbits, xlenbits)
}

/* cursor, base addr, end addr, permissions, type */
type decodedcap_t = (capnodeidbits, decodedcap_metadata_t)
/* captype omitted as it is already included in decodedcap_metadata_t */

function decode_common_cap(metadata_bits : bits(94))
        -> (xlenbits, xlenbits, xlenbits, capperm_t) = {

    let perm : cappermbits @
    iE : bits(1) @ t : bits(9) @ tE : bits(3) @ b : bits(11) @
    bE : bits(3) @ cursor : xlenbits = metadata_bits;

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

    (cursor, base, top, capperm_bits(perm))
}

function decode_cap(cap: cap_t) -> decodedcap_t = {
    let ni : capnodeidbits @ ty : captypebits @ metadata_bits : bits(94) = cap;

    let metadata : decodedcap_metadata_t = match captype_bits(ty) {
        CAP_TYPE_LIN => {
            LinearCapMetadata(decode_common_cap(metadata_bits))
        },
        CAP_TYPE_NONLIN => {
            NonLinearCapMetadata(decode_common_cap(metadata_bits))
        },
        CAP_TYPE_REV => {
            RevocationCapMetadata(decode_common_cap(metadata_bits))
        },
        CAP_TYPE_UNINIT => {
            UninitialisedCapMetadata(decode_common_cap(metadata_bits))
        },
        CAP_TYPE_SEALED => {
            let async : bits(2)
                @ _ : bits(28) /* reserved */
                @ base_addr : xlenbits = metadata_bits;
            SealedCapMetadata((base_addr, async))
        },
        CAP_TYPE_SEALEDRET => {
            /* TODO: */
            SealedRetCapMetadata(EXTZ(0b0), EXTZ(0b0), EXTZ(0b0), EXTZ(0b0))
        }, 
        CAP_TYPE_EXIT => {
            /* TODO: */
            ExitCapMetadata(EXTZ(0b0), EXTZ(0b0))
        }
    } in (ni, metadata)
}

function encode_common_cap(ni : capnodeidbits, ty : captype_t, 
                          cursor : xlenbits, start_addr : xlenbits,
                          end_addr : xlenbits, perm : capperm_t) -> cap_t = {

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

function encode_cap(dcap: decodedcap_t) -> cap_t = {
    /* let (cursor, start_addr, end_addr, ni, perm, ty) = dcap; */
    let (ni, metadata) = dcap;
    match(metadata) {
        LinearCapMetadata(cursor, base_addr, end_addr, perm) => {
            encode_common_cap(ni, CAP_TYPE_LIN, cursor, base_addr, end_addr, perm)
        },
        NonLinearCapMetadata(cursor, base_addr, end_addr, perm) => {
            encode_common_cap(ni, CAP_TYPE_NONLIN, cursor, base_addr, end_addr, perm)
        },
        RevocationCapMetadata(cursor, base_addr, end_addr, perm) => {
            encode_common_cap(ni, CAP_TYPE_REV, cursor, base_addr, end_addr, perm)
        },
        UninitialisedCapMetadata(cursor, base_addr, end_addr, perm) => {
            encode_common_cap(ni, CAP_TYPE_UNINIT, cursor, base_addr, end_addr, perm)
        },
        SealedCapMetadata(base_addr, async) => {
            ni @ captype_bits(CAP_TYPE_SEALED) @ async @ EXTZ(0b0) : bits(28) /* reserved*/ @ base_addr
        },
        SealedRetCapMetadata(cursor, base_addr, async, reg) => {
            /* size of region is 128 * 34, we allow 128 * (64 - 34) / 2 = 128 * 15 bytes below or above */
            /* we do not check for now */
            //let offset = (cursor - base_addr + ((EXTZ(0xf) : xlenbits) << (EXTZ(0x7) : xlenbits))) : bits(13);
            // ni @ captype_bits(ty) @ async @ reg @ EXTZ(0b0) : bits(10) /* reserved*/ @ offset @ cursor
            /* TODO: this is not quite right */
            EXTZ(0b0)
        },
        ExitCapMetadata(cursor, base_addr) => {
            /* TODO: */
            EXTZ(0b0)
        },
        _ => {
            EXTZ(0b0)
        }
    }

}

function cap_type(cap: cap_t) -> captype_t = {
    let (_, metadata) = decode_cap(cap) in
    match metadata {
        LinearCapMetadata(_) => CAP_TYPE_LIN,
        NonLinearCapMetadata(_) => CAP_TYPE_NONLIN,
        RevocationCapMetadata(_) => CAP_TYPE_REV,
        UninitialisedCapMetadata(_) => CAP_TYPE_UNINIT,
        SealedCapMetadata(_) => CAP_TYPE_SEALED,
        SealedRetCapMetadata(_) => CAP_TYPE_SEALEDRET,
        ExitCapMetadata(_) => CAP_TYPE_EXIT,
        _ => CAP_TYPE_LIN
    }
}

function cap_type_is_common(cap: cap_t) -> bool = {
    let ty = cap_type(cap);
    match ty {
        CAP_TYPE_LIN => true,
        CAP_TYPE_NONLIN => true,
        CAP_TYPE_REV => true,
        CAP_TYPE_UNINIT => true,
        _ => false
    }
}

function cap_perm(cap: cap_t) -> capperm_t = {
    let (_, metadata) = decode_cap(cap) in
        match(metadata) {
            LinearCapMetadata(_, _, _, perm) => perm,
            NonLinearCapMetadata(_, _, _, perm) => perm,
            RevocationCapMetadata(_, _, _, perm) => perm,
            UninitialisedCapMetadata(_, _, _, perm) => CAP_PERM_WO,
            _ => CAP_PERM_NA
        }
}

function cap_cursor(cap: cap_t) -> xlenbits = {
    let (_, metadata) = decode_cap(cap) in
        match(metadata) {
            LinearCapMetadata(cursor, _, _, _) => cursor,
            NonLinearCapMetadata(cursor, _, _, _) => cursor,
            RevocationCapMetadata(cursor, _, _, _) => cursor,
            UninitialisedCapMetadata(cursor, _, _, _) => cursor,
            SealedRetCapMetadata(cursor, _, _, _) => cursor,
            ExitCapMetadata(cursor, _) => cursor,
            _ => EXTZ(0b0)
        }
}

function cap_nodeid(cap: cap_t) -> capnodeidbits = {
    let (ni, _) = decode_cap(cap) in ni
}

function cap_bounds(cap: cap_t) -> (xlenbits, xlenbits) = {
    let (_, metadata) = decode_cap(cap) in
        match(metadata) {
            LinearCapMetadata(_, start_addr, end_addr, _) => (start_addr, end_addr),
            NonLinearCapMetadata(_, start_addr, end_addr, _) => (start_addr, end_addr),
            RevocationCapMetadata(_, start_addr, end_addr, _) => (start_addr, end_addr),
            UninitialisedCapMetadata(_, start_addr, end_addr, _) => (start_addr, end_addr),
            SealedCapMetadata(base_addr, _) => (base_addr, base_addr + to_bits(sizeof(xlen), caplen_bytes_v * 34)),
            SealedRetCapMetadata(_, base_addr, _, _) => (base_addr, base_addr + to_bits(sizeof(xlen), caplen_bytes_v * 34)),
            ExitCapMetadata(_, base_addr) => (base_addr, base_addr + to_bits(sizeof(xlen), caplen_bytes_v * 34)),
            _ => (EXTZ(0b0), EXTZ(0b0))
        }
}

function cap_bound_size(cap: cap_t) -> xlenbits = {
    let (_, metadata) = decode_cap(cap) in
        match(metadata) {
            LinearCapMetadata(_, start_addr, end_addr, _) => end_addr - start_addr,
            NonLinearCapMetadata(_, start_addr, end_addr, _) => end_addr - start_addr,
            RevocationCapMetadata(_, start_addr, end_addr, _) => end_addr - start_addr,
            UninitialisedCapMetadata(_, start_addr, end_addr, _) => end_addr - start_addr,
            SealedCapMetadata(_, _) => to_bits(sizeof(xlen), caplen_bytes_v * 34),
            SealedRetCapMetadata(_, _, _, _) => to_bits(sizeof(xlen), caplen_bytes_v * 34),
            ExitCapMetadata(_, _) => to_bits(sizeof(xlen), caplen_bytes_v * 34),
            _ => EXTZ(0b0)
        }
}

function cap_in_bound(cap: cap_t, addr: xlenbits, width: int) -> bool = {
    let (start_addr, end_addr) = cap_bounds(cap) in
        unsigned(start_addr) <= unsigned(addr) & unsigned(addr) + width <= unsigned(end_addr)
}


type capxlen : Int = caplen - xlen

function cap_set_type(cap: cap_t, new_ty: captype_t) -> cap_t = {
    /* directly change the type bitfield */
    let _ : captypebits @ cap_no_type : bits(125) = cap in
        captype_bits(new_ty) @ cap_no_type
}

function cap_set_nodeid(cap: cap_t, new_ni: capnodeidbits) -> cap_t = {
    let (_, metadata) = decode_cap(cap) in
        encode_cap((new_ni, metadata))
}

function cap_set_perm(cap: cap_t, new_perm: capperm_t) -> cap_t = {
    let (ni, metadata) = decode_cap(cap);
    let new_metadata : decodedcap_metadata_t = match(metadata) {
        LinearCapMetadata(cursor, start_addr, end_addr, _) =>
            LinearCapMetadata(cursor, start_addr, end_addr, new_perm),
        NonLinearCapMetadata(cursor, start_addr, end_addr, _) =>
            NonLinearCapMetadata(cursor, start_addr, end_addr, new_perm),
        RevocationCapMetadata(cursor, start_addr, end_addr, _) =>
            RevocationCapMetadata(cursor, start_addr, end_addr, new_perm),
        UninitialisedCapMetadata(cursor, start_addr, end_addr, _) =>
            UninitialisedCapMetadata(cursor, start_addr, end_addr, new_perm),
        _ => metadata
    };
    encode_cap((ni, new_metadata))
}

function cap_set_bound(cap: cap_t, new_start: xlenbits, new_end: xlenbits) -> cap_t = {
    let (ni, metadata) = decode_cap(cap);
    let new_metadata : decodedcap_metadata_t = match(metadata) {
        LinearCapMetadata(cursor, start_addr, end_addr, perm) =>
            LinearCapMetadata(cursor, new_start, new_end, perm),
        NonLinearCapMetadata(cursor, start_addr, end_addr, perm) =>
            NonLinearCapMetadata(cursor, new_start, new_end, perm),
        RevocationCapMetadata(cursor, start_addr, end_addr, perm) =>
            RevocationCapMetadata(cursor, new_start, new_end, perm),
        UninitialisedCapMetadata(cursor, start_addr, end_addr, perm) =>
            UninitialisedCapMetadata(cursor, new_start, new_end, perm),
        SealedCapMetadata(base_addr, async) =>
            SealedCapMetadata(new_start, async),
        SealedRetCapMetadata(cursor, base_addr, async, reg) =>
            SealedRetCapMetadata(cursor, new_start, async, reg),
        ExitCapMetadata(cursor, base_addr) =>
            ExitCapMetadata(cursor, new_start),
        _ => metadata
    };
    encode_cap((ni, new_metadata))
}

function cap_set_cursor(cap: cap_t, new_cursor: xlenbits) -> cap_t = {
    let (ni, metadata) = decode_cap(cap);
    let new_metadata : decodedcap_metadata_t = match(metadata) {
        LinearCapMetadata(cursor, start_addr, end_addr, perm) =>
            LinearCapMetadata(new_cursor, start_addr, end_addr, perm),
        NonLinearCapMetadata(cursor, start_addr, end_addr, perm) =>
            NonLinearCapMetadata(new_cursor, start_addr, end_addr, perm),
        RevocationCapMetadata(cursor, start_addr, end_addr, perm) =>
            RevocationCapMetadata(new_cursor, start_addr, end_addr, perm),
        UninitialisedCapMetadata(cursor, start_addr, end_addr, perm) =>
            UninitialisedCapMetadata(new_cursor, start_addr, end_addr, perm),
        SealedRetCapMetadata(cursor, base_addr, async, reg) =>
            SealedRetCapMetadata(new_cursor, base_addr, async, reg),
        ExitCapMetadata(cursor, base_addr) =>
            ExitCapMetadata(new_cursor, base_addr),
        _ => metadata
    };
    encode_cap((ni, new_metadata))
}

/** set both the bound and the cursor at the same time */
function cap_set_bound_cursor(cap: cap_t, new_cursor: xlenbits, new_start: xlenbits, new_end: xlenbits) -> cap_t = {
    let (ni, metadata) = decode_cap(cap);
    let new_metadata : decodedcap_metadata_t = match(metadata) {
        LinearCapMetadata(cursor, start_addr, end_addr, perm) =>
            LinearCapMetadata(new_cursor, new_start, new_end, perm),
        NonLinearCapMetadata(cursor, start_addr, end_addr, perm) =>
            NonLinearCapMetadata(new_cursor, new_start, new_end, perm),
        RevocationCapMetadata(cursor, start_addr, end_addr, perm) =>
            RevocationCapMetadata(new_cursor, new_start, new_end, perm),
        UninitialisedCapMetadata(cursor, start_addr, end_addr, perm) =>
            UninitialisedCapMetadata(new_cursor, new_start, new_end, perm),
        SealedCapMetadata(base_addr, async) =>
            SealedCapMetadata(new_start, async),
        SealedRetCapMetadata(cursor, base_addr, async, reg) =>
            SealedRetCapMetadata(new_cursor, new_start, async, reg),
        ExitCapMetadata(cursor, base_addr) =>
            ExitCapMetadata(new_cursor, new_start),
        _ => metadata
    };
    encode_cap((ni, new_metadata))
}

function cap_shrink_common(metadata_raw : common_metadata_t, new_start : xlenbits, new_end : xlenbits) -> option(common_metadata_t) = {
    let (cursor, start_addr, end_addr, perm) = metadata_raw in
    if unsigned(start_addr) <= unsigned(new_start) & 
        unsigned(new_start) <= unsigned(new_end) &
        unsigned(new_end) <= unsigned(end_addr) then
        Some((cursor, new_start, new_end, perm))
    else
        None() 
}

function cap_shrink(cap: cap_t, new_start: xlenbits, new_end: xlenbits) -> option(cap_t) = {
    let (ni, metadata) = decode_cap(cap);
    let result_metadata_raw : option(common_metadata_t) = match(metadata) {
        LinearCapMetadata(metadata_raw) => cap_shrink_common(metadata_raw, new_start, new_end),
        NonLinearCapMetadata(metadata_raw) => cap_shrink_common(metadata_raw, new_start, new_end),
        RevocationCapMetadata(metadata_raw) => cap_shrink_common(metadata_raw, new_start, new_end),
        UninitialisedCapMetadata(metadata_raw) => cap_shrink_common(metadata_raw, new_start, new_end),
        _ => None()
    };
    match (metadata, result_metadata_raw) {
        (LinearCapMetadata(_), Some(metadata_raw)) =>
            Some(encode_cap((ni, LinearCapMetadata(metadata_raw)))),
        (NonLinearCapMetadata(_), Some(metadata_raw)) =>
            Some(encode_cap((ni, NonLinearCapMetadata(metadata_raw)))),
        (RevocationCapMetadata(_), Some(metadata_raw)) =>
            Some(encode_cap((ni, RevocationCapMetadata(metadata_raw)))),
        (UninitialisedCapMetadata(_), Some(metadata_raw)) =>
            Some(encode_cap((ni, UninitialisedCapMetadata(metadata_raw)))),
        _ => None()
    }
}

function cap_tighten(cap: cap_t, new_perm: capperm_t) -> option(cap_t) = {
    let (ni, metadata) = decode_cap(cap);
    match(metadata) {
        LinearCapMetadata(cursor, start_addr, end_addr, perm) if new_perm <=_p perm =>
            Some(encode_cap((ni, LinearCapMetadata((cursor, start_addr, end_addr, new_perm))))),
        NonLinearCapMetadata(cursor, start_addr, end_addr, perm) if new_perm <=_p perm =>
            Some(encode_cap((ni, NonLinearCapMetadata((cursor, start_addr, end_addr, new_perm))))),
        RevocationCapMetadata(cursor, start_addr, end_addr, perm) if new_perm <=_p perm =>
            Some(encode_cap((ni, RevocationCapMetadata((cursor, start_addr, end_addr, new_perm))))),
        UninitialisedCapMetadata(cursor, start_addr, end_addr, perm) if new_perm <=_p perm =>
            Some(encode_cap((ni, UninitialisedCapMetadata((cursor, start_addr, end_addr, new_perm))))),
        _ => None()
    }
}

/* capability-related errors */

enum caperror_t = {
    CAP_ERROR_INVALID_PC
}

/* pretty-print capability */

function print_common_metadata(metadata_raw : common_metadata_t) -> unit = {
    let (cursor, start_addr, end_addr, perm) = metadata_raw;
    print_string("Cursor = ", BitStr(cursor));
    print_string("Start address = ", BitStr(start_addr));
    print_string("End address = ", BitStr(end_addr));
    print_string("Perm = ", capperm_string(perm));
}

function print_cap(s: string, cap: cap_t) -> unit = {
    let (ni, metadata) = decode_cap(cap);
    let ty = cap_type(cap);
    print_string(s, "Cap(");
    print_string("Type = ", captype_string(ty));
    print_string("Node ID = ", BitStr(ni));
    match(metadata) {
        LinearCapMetadata(metadata_raw) => {
            print_common_metadata(metadata_raw);
        },
        NonLinearCapMetadata(metadata_raw) => {
            print_common_metadata(metadata_raw);
        },
        RevocationCapMetadata(metadata_raw) => {
            print_common_metadata(metadata_raw);
        },
        UninitialisedCapMetadata(metadata_raw) => {
            print_common_metadata(metadata_raw);
        },
        SealedCapMetadata(base_addr, async) => {
            print_string("Base address = ", BitStr(base_addr));
            print_string("Async = ", BitStr(async));
        },
        SealedRetCapMetadata(cursor, base_addr, async, reg) => {
            print_string("Cursor = ", BitStr(cursor));
            print_string("Base address = ", BitStr(base_addr));
            print_string("Async = ", BitStr(async));
            print_string("RegId = ", BitStr(reg));
        },
        ExitCapMetadata(cursor, base_addr) => {
            print_string("Cursor = ", BitStr(cursor));
            print_string("Base address = ", BitStr(base_addr));
        }
    };
    print(")");
}

function common_metadata_string(metadata_raw : common_metadata_t) -> string = {
    let (cursor, start_addr, end_addr, perm) = metadata_raw in
    "Cursor = " ^ BitStr(cursor) ^ sep() ^
    "Start address = " ^ BitStr(start_addr) ^ sep() ^
    "End address = " ^ BitStr(end_addr) ^ sep() ^
    "Perm = " ^ capperm_string(perm)
}

function capmetadata_string(metadata: decodedcap_metadata_t) -> string = {
    match metadata {
        LinearCapMetadata(metadata_raw) =>
            common_metadata_string(metadata_raw),
        NonLinearCapMetadata(metadata_raw) =>
            common_metadata_string(metadata_raw),
        RevocationCapMetadata(metadata_raw) =>
            common_metadata_string(metadata_raw),
        UninitialisedCapMetadata(metadata_raw) =>
            common_metadata_string(metadata_raw),
        SealedCapMetadata(base_addr, async) =>
            "Base address = " ^ BitStr(base_addr) ^ sep() ^
            "Async = " ^ BitStr(async),
        SealedRetCapMetadata(cursor, base_addr, async, reg) =>
            "Cursor = " ^ BitStr(cursor) ^ sep() ^
            "Base address = " ^ BitStr(base_addr) ^ sep() ^
            "Async = " ^ BitStr(async) ^ sep() ^
            "RegId = " ^ BitStr(reg),
        ExitCapMetadata(cursor, base_addr) =>
            "Cursor = " ^ BitStr(cursor) ^ sep() ^
            "Base address = " ^ BitStr(base_addr)
    }
}

function cap_string(cap: cap_t) -> string = {
    let (ni, metadata) = decode_cap(cap) in
        "Cap(" ^ captype_string(cap_type(cap)) ^ sep() ^
        BitStr(ni) ^ sep() ^
        capmetadata_string(metadata) ^ ")"
}

let CAP_INVALID : cap_t = EXTZ(0b0)
