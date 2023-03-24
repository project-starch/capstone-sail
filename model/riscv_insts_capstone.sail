union clause ast = CAPSTONE_INSN : (regidx, regidx, regidx, capstone_op)

/************************************************************/

/** Backdoor instructions for testing only */

mapping clause encdec = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_CAPCREATE)   <-> 0b0000101 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_CAPCREATE)) = {
    X(rd) = CapVal(EXTZ(0b0));
    RETIRE_SUCCESS
}

mapping clause assembly = CAPSTONE_INSN(rs1, rs2, rd, CAPSTONE_CAPCREATE)
  <-> "capcreate" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)


/************************************************************/

mapping clause encdec = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_CAPTYPE)   <-> 0b0000110 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_CAPTYPE)) = {
    let rd_v : regtype = X(rd);
    let rs1_v : regtype = X(rs1);
    match((rs1_v, rd_v)) {
        (RawVal(v), CapVal(cv)) if captype_bits_backwards_matches(v[2..0]) => { 
            // note that the high bits are not used
            X(rd) = CapVal(cap_set_type(cv, captype_bits(v[2..0])));
            RETIRE_SUCCESS
        },
        _ => {
            // invalid operands
            handle_illegal();
            RETIRE_FAIL
        }
    }
}

mapping clause assembly = CAPSTONE_INSN(rs1, rs2, rd, CAPSTONE_CAPTYPE)
  <-> "captype" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)


/************************************************************/

mapping clause encdec = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_CAPNODE)   <-> 0b0000111 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_CAPNODE)) = {
    let rd_v : regtype = X(rd);
    let rs1_v : regtype = X(rs1);
    match((rs1_v, rd_v)) {
        (RawVal(v), CapVal(cv)) => {
            X(rd) = CapVal(cap_set_nodeid(cv, v[30..0]));
            RETIRE_SUCCESS
        },
        _ => {
            // invalid operands
            handle_illegal();
            RETIRE_FAIL
        }
    }
}

mapping clause assembly = CAPSTONE_INSN(rs1, rs2, rd, CAPSTONE_CAPNODE)
  <-> "capnode" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)


/************************************************************/

mapping clause encdec = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_CAPPERM)   <-> 0b0001000 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_CAPPERM)) = {
    let rd_v : regtype = X(rd);
    let rs1_v : regtype = X(rs1);
    match((rs1_v, rd_v)) {
        (RawVal(v), CapVal(cv)) if capperm_bits_backwards_matches(v[2..0]) => {
            X(rd) = CapVal(cap_set_perm(cv, capperm_bits(v[2..0])));
            RETIRE_SUCCESS
        },
        _ => {
            // invalid operands
            handle_illegal();
            RETIRE_FAIL
        }
    }
}

mapping clause assembly = CAPSTONE_INSN(rs1, rs2, rd, CAPSTONE_CAPPERM)
  <-> "capperm" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)


/************************************************************/

mapping clause encdec = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_CAPBOUND)   <-> 0b0001001 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_CAPBOUND)) = {
    let rd_v : regtype = X(rd);
    let rs1_v : regtype = X(rs1);
    let rs2_v : regtype = X(rs2);
    match((rs1_v, rs2_v, rd_v)) {
        (RawVal(v1), RawVal(v2), CapVal(cv)) => {
            X(rd) = CapVal(cap_set_bound(cv, v1, v2));
            RETIRE_SUCCESS
        },
        _ => {
            // invalid operands
            handle_illegal();
            RETIRE_FAIL
        }
    }
}

mapping clause assembly = CAPSTONE_INSN(rs1, rs2, rd, CAPSTONE_CAPBOUND)
  <-> "capbound" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/************************************************************/

mapping clause encdec = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_CAPBOUND)   <-> 0b0001001 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_CAPBOUND)) = {
    let rd_v : regtype = X(rd);
    let rs1_v : regtype = X(rs1);
    let rs2_v : regtype = X(rs2);
    match((rs1_v, rs2_v, rd_v)) {
        (RawVal(v1), RawVal(v2), CapVal(cv)) => {
            X(rd) = CapVal(cap_set_bound(cv, v1, v2));
            RETIRE_SUCCESS
        },
        _ => {
            // invalid operands
            handle_illegal();
            RETIRE_FAIL
        }
    }
}

mapping clause assembly = CAPSTONE_INSN(rs1, rs2, rd, CAPSTONE_CAPBOUND)
  <-> "capbound" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)


/************************************************************/

mapping clause encdec = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_CAPPRINT)   <-> 0b0001010 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_CAPPRINT)) = {
    let rs1_v : regtype = X(rs1);
    match(rs1_v) {
        RawVal(v) => {
            print_bits("RawVal: ", v);
        },
        CapVal(cv) => {
            print_bits("CapVal: ", cv);
        }
    };
    RETIRE_SUCCESS
}

mapping clause assembly = CAPSTONE_INSN(rs1, rs2, rd, CAPSTONE_CAPPRINT)
  <-> "capprint" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)


/************************************************************/



mapping clause encdec = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_QUERY)   <-> 0b0000000 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_QUERY)) = {
    print("good execution capstone instruction query");
    RETIRE_SUCCESS
}

mapping clause assembly = CAPSTONE_INSN(rs1, rs2, rd, CAPSTONE_QUERY)
  <-> "query" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)


/************************************************************/

mapping clause encdec = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_DROP)   <-> 0b0000001 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_DROP)) = {
    print("good execution capstone instruction drop");
    RETIRE_SUCCESS
}

mapping clause assembly = CAPSTONE_INSN(rs1, rs2, rd, CAPSTONE_DROP)
  <-> "drop" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/************************************************************/

mapping clause encdec = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_CALL)   <-> 0b0000001 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_CALL)) = {
    print("good execution capstone instruction call");
    RETIRE_SUCCESS
}

mapping clause assembly = CAPSTONE_INSN(rs1, rs2, rd, CAPSTONE_CALL)
  <-> "call" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/************************************************************/


mapping clause encdec = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_SHRINK)   <-> 0b0000100 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_SHRINK)) = {
    let rd_v : regtype = X(rd);
    let rs1_v : regtype = X(rs1);
    let rs2_v : regtype = X(rs2);
    match((rd_v, rs1_v, rs2_v)) {
        (CapVal(cv), RawVal(v1), RawVal(v2)) if unsigned(v1) <= unsigned(v2) => {
            match(cap_shrink(cv, v1, v2)) {
                Some(ncv) => {
                    X(rd) = CapVal(ncv);
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

mapping clause assembly = CAPSTONE_INSN(rs1, rs2, rd, CAPSTONE_SHRINK)
  <-> "shrink" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/************************************************************/

mapping clause encdec = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_TIGHTEN)   <-> 0b0000110 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_TIGHTEN)) = {
    let rd_v : regtype = X(rd);
    let rs1_v : regtype = X(rs1);
    match((rd_v, rs1_v)) {
        (CapVal(cv), RawVal(v)) if capperm_bits_backwards_matches(v[2..0]) => {
            match(cap_tighten(cv, capperm_bits(v[2..0]))) {
                Some(ncv) => {
                    X(rd) = CapVal(ncv);
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

mapping clause assembly = CAPSTONE_INSN(rs1, rs2, rd, CAPSTONE_TIGHTEN)
  <-> "tighten" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/************************************************************/

mapping clause encdec = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_DELIN)   <-> 0b0000111 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_DELIN)) = {
    let rd_v : regtype = X(rd);
    match(rd_v) {
        CapVal(cv) if cap_type(cv) == CAP_TYPE_LIN => {
            X(rd) = CapVal(cap_set_type(cv, CAP_TYPE_NONLIN));
            RETIRE_SUCCESS
        },
        _ => {
            handle_illegal();
            RETIRE_FAIL
        }
    }
}

mapping clause assembly = CAPSTONE_INSN(rs1, rs2, rd, CAPSTONE_DELIN)
  <-> "delin" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)


/************************************************************/

mapping clause encdec = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_SCC)   <-> 0b0001000 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_SCC)) = {
    let rd_v : regtype = X(rd);
    let rs1_v : regtype = X(rs1);
    match((rd_v, rs1_v)) {
        (CapVal(cv), RawVal(v)) => {
            X(rd) = CapVal(cap_set_cursor(cv, v));
            RETIRE_SUCCESS
        },
        _ => {
            handle_illegal();
            RETIRE_FAIL
        }
    }
}

mapping clause assembly = CAPSTONE_INSN(rs1, rs2, rd, CAPSTONE_SCC)
  <-> "scc" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/************************************************************/

mapping clause encdec = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_LCC)   <-> 0b0001110 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_LCC)) = {
    let rs1_v : regtype = X(rs1);
    /** TODO: check the original value in rd */
    match(rs1_v) {
        CapVal(cv) => {
            X(rd) = RawVal(cap_cursor(cv));
            RETIRE_SUCCESS
        },
        _ => {
            handle_illegal();
            RETIRE_FAIL
        }
    }
}

mapping clause assembly = CAPSTONE_INSN(rs1, rs2, rd, CAPSTONE_LCC)
  <-> "lcc" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

