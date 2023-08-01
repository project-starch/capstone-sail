/* Control and status related definitions for Capstone */

/* Extended CSRs */

register cis : bits(16)
register ctval : xlenbits
register ccause : xlenbits
register emode : bit


/* CCSRs */

register ceh : regtype
register cih : regtype
register cinit : cap_t
register cepc : cap_t
register switch_cap : cap_t

/* registers for normal world PC and stack pointer */
register normal_pc : xlenbits
register normal_sp  : regtype
register switch_reg : regidx
register exit_reg : regidx

val capstone_in_secure_world : unit -> bool
val capstone_in_normal_world : unit -> bool


function ccsr_idx_matches(idx: imm12) -> bool = {
    unsigned(idx) <= 4
}

function read_ceh() -> regtype = {
    if capstone_in_secure_world() then
        ceh
    else
        RawVal(EXTZ(0b0))
}

function write_ceh(v: regtype) -> unit = {
    if capstone_in_secure_world() then
        ceh = v;
}

function read_cih() -> regtype = {
    RawVal(EXTZ(0b0))
}

function write_cih(v: regtype) -> unit = {
    match cih {
        CapVal(_) => (),
        _ => {
            if capstone_in_secure_world() then
                cih = v;
        }
    }
}

function read_cinit() -> regtype = {
    if capstone_in_normal_world() then {
        let res = cinit;
        cinit = CAP_INVALID;
        CapVal(res)
    } else
        RawVal(EXTZ(0b0))
}

function write_cinit(v: regtype) -> unit = {
    ()
}

function read_cepc() -> regtype = {
    if capstone_in_secure_world() then {
        CapVal(cepc)
    } else {
        RawVal(EXTZ(0b0))
    }
}

function write_cepc(v: regtype) -> unit = {
    if capstone_in_secure_world() then
        match v {
            CapVal(c) =>{
                cepc = c;
            },
            _ => ()
        }
    else ()
}

function read_switch_cap() -> regtype = {
    if capstone_in_normal_world() then {
        CapVal(switch_cap)
    } else {
        RawVal(EXTZ(0b0))
    }
}

function write_switch_cap(v: regtype) -> unit = {
    if capstone_in_normal_world() then
        match v {
            CapVal(c) => {
                switch_cap = c;
            },
            _ => ()
        }
    else ()
}

function read_ccsr(idx: imm12) -> regtype = {
    match unsigned(idx) {
        0 => read_ceh(),
        1 => read_cih(),
        2 => read_cinit(),
        3 => read_cepc(),
        4 => read_switch_cap(),
        _ => RawVal(EXTZ(0b0))
    }
}

function write_ccsr(idx: imm12, v: regtype) -> unit = {
    match unsigned(idx) {
        0 => write_ceh(v),
        1 => write_cih(v),
        2 => write_cinit(v),
        3 => write_cepc(v),
        4 => write_switch_cap(v),
        _ => ()
    }
}
