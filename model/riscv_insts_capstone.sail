union clause ast = CAPSTONE_INSN : (regidx, regidx, regidx, capstone_op)

/************************************************************/

/** Backdoor instructions for testing only */

mapping clause encdec = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_CAPCREATE)   <-> 0b0000101 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_CAPCREATE)) = {
    X(rd) = CapVal(EXTZ(0b0));
    RETIRE_SUCCESS
}

mapping clause assembly = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_CAPCREATE)
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

mapping clause assembly = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_CAPTYPE)
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

mapping clause assembly = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_CAPNODE)
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

mapping clause assembly = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_CAPPERM)
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

mapping clause assembly = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_CAPBOUND)
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

mapping clause assembly = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_CAPBOUND)
  <-> "capbound" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)


/************************************************************/

mapping clause encdec = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_CAPPRINT)   <-> 0b0001010 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_CAPPRINT)) = {
    let rs1_v : regtype = X(rs1);
    print_string("capprint: ", RegStr(rs1_v));
    RETIRE_SUCCESS
}

mapping clause assembly = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_CAPPRINT)
  <-> "capprint" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/************************************************************/

mapping clause encdec = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_TAGGET)   <-> 0b0001100 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_TAGGET)) = {
    let rs1_v : regtype = X(rs1);
    let rd_v : regtype = X(rd);

    match(rs1_v) {
        RawVal(v) => {
            reg_overwrite(rd_v);
            X(rd) = EXTZ(mem_tag(v));
            RETIRE_SUCCESS
        },
        _ => {
            handle_illegal();
            RETIRE_FAIL
        }
    }
}

mapping clause assembly = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_TAGGET)
  <-> "tagget" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/************************************************************/

mapping clause encdec = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_TAGSET)   <-> 0b0001011 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_TAGSET)) = {
    let rs1_v : regtype = X(rs1);
    let rs2_v : regtype = X(rs2);

    match((rs1_v, rs2_v)) {
        (RawVal(addr), RawVal(tag)) => {
            assert(mem_tag_set(addr, bit_to_bits(tag[0])));
            RETIRE_SUCCESS
        },
        _ => {
            handle_illegal();
            RETIRE_FAIL
        }
    }
}

mapping clause assembly = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_TAGSET)
  <-> "tagset" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/************************************************************/

mapping clause encdec = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_QUERY)   <-> 0b0000000 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_QUERY)) = {
    let rs1_v : regtype = X(rs1);
    match(rs1_v) {
        RawVal(v) => {
            let v = capnode_query(v[(capnodeidlen_v - 1)..0]);
            print_bits("Node query: ", v);
            RETIRE_SUCCESS
        },
        _ => {
            handle_illegal();
            RETIRE_FAIL
        }
    }
}

mapping clause assembly = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_QUERY)
  <-> "query" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)


/************************************************************/

mapping clause encdec = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_RCUPDATE)   <-> 0b0000010 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1011011

/*
update the ref count for a given node id directly
*/
function clause execute (CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_RCUPDATE)) = {
    let rs1_v : regtype = X(rs1);
    let rd_v : regtype = X(rd);
    match((rd_v, rs1_v)) {
        (RawVal(node_id), RawVal(delta)) => {
            capnode_rcupdate(truncate(node_id, capnodeidlen_v), truncate(delta, capnodecounterlen_v));
            RETIRE_SUCCESS
        },
        _ => {
            handle_illegal();
            RETIRE_FAIL
        }
    }
}

mapping clause assembly = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_RCUPDATE)
  <-> "rcupdate" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/************************************************************/

mapping clause encdec = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_ALLOC)   <-> 0b0000011 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1011011

/*
allocates a new child node for a given revocation node and stores the id of the new node
in the destination register
*/
function clause execute (CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_ALLOC)) = {
    let rs1_v : regtype = X(rs1);
    let rd_v : regtype = X(rd);
    match(rs1_v) {
        RawVal(parent_id) => {
            match(capnode_duplicate(truncate(parent_id, capnodeidlen_v), true)) {
                Some(new_node_id) => {
                    reg_overwrite(rd_v);
                    X(rd) = RawVal(EXTZ(new_node_id));
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

mapping clause assembly = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_ALLOC)
  <-> "alloc" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)



/************************************************************/

/* directly invalidate a specific capability (can only be one of the linear types that
would be associated uniquely with a revocation node) */

mapping clause encdec = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_DROP)   <-> 0b0000001 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_DROP)) = {
    let rs1_v : regtype = X(rs1);

    match(rs1_v) {
        CapVal(c) if captype_is_linear(cap_type(c)) => {
            assert(capnode_invalidate(cap_nodeid(c)),
                "drop: unable to invalidate the revocation node"); /* TODO: might also consider removing it from the revocation tree (optional) */
            RETIRE_SUCCESS
        },
        _ => {
            handle_illegal();
            RETIRE_FAIL
        }
    }
}

mapping clause assembly = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_DROP)
  <-> "drop" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/************************************************************/

mapping clause encdec = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_CALL)   <-> 0b0000001 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_CALL)) = capstone_call(rd, rs1, CAPSTONE_CALL_NORMAL)

mapping clause assembly = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_CALL)
  <-> "call" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)


/************************************************************/

mapping clause encdec = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_RETURN)   <-> 0b0010100 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_RETURN)) = capstone_call(rd, rs1, CAPSTONE_CALL_RETURN)

mapping clause assembly = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_RETURN)
  <-> "return" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)


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

mapping clause assembly = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_SHRINK)
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

mapping clause assembly = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_TIGHTEN)
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

mapping clause assembly = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_DELIN)
  <-> "delin" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)


/************************************************************/

mapping clause encdec = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_SCC)   <-> 0b0001000 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_SCC)) = {
    let rd_v : regtype = X(rd);
    let rs1_v : regtype = X(rs1);
    match((rd_v, rs1_v)) {
        /* we do not allow setting cursor of an uninitialised capability */
        (CapVal(cv), RawVal(v)) if cap_type(cv) != CAP_TYPE_UNINIT => {
            X(rd) = CapVal(cap_set_cursor(cv, v));
            RETIRE_SUCCESS
        },
        _ => {
            handle_illegal();
            RETIRE_FAIL
        }
    }
}

mapping clause assembly = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_SCC)
  <-> "scc" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/************************************************************/

mapping clause encdec = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_INIT)  <-> 0b0001001 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_INIT)) = {
    let rd_v : regtype = X(rd);

    match(rd_v) {
        CapVal(cv) if capstone_cap_initialised(cv) => {
            X(rd) = CapVal(capstone_initialise_nocheck(cv));
            RETIRE_SUCCESS
        },
        _ => {
            handle_illegal();
            RETIRE_FAIL
        }
    }
}

mapping clause assembly = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_INIT)
  <-> "init" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/************************************************************/

mapping clause encdec = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_LCC)   <-> 0b0001101 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_LCC)) = {
    let rs1_v : regtype = X(rs1);
    let rd_v : regtype = X(rd);
    match(rs1_v) {
        CapVal(cv) => {
            reg_overwrite(rd_v);
            X(rd) = RawVal(cap_cursor(cv));
            RETIRE_SUCCESS
        },
        _ => {
            handle_illegal();
            RETIRE_FAIL
        }
    }
}

mapping clause assembly = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_LCC)
  <-> "lcc" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)


/************************************************************/

mapping clause encdec = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_SPLIT)   <-> 0b0010010 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_SPLIT)) = {
    let rs1_v : regtype = X(rs1);
    let rs2_v : regtype = X(rs2);
    let rd_v : regtype = X(rd);
    match((rs1_v, rs2_v)) {
        (CapVal(c), RawVal(v)) => {
            let (cursor, start_addr, end_addr, node_id, perm, ty) = decode_cap(c);
            if(unsigned(v) < unsigned(start_addr) | unsigned(v) > unsigned(end_addr) |
                ty != CAP_TYPE_LIN | capnode_query(node_id) == 0b1) then {
                handle_illegal();
                RETIRE_FAIL
            } else {
                let c1_dec = (start_addr, start_addr, v, node_id, perm, ty);
                /* duplicate the node */
                match(capnode_duplicate(node_id, false)) {
                    Some(new_node_id) => {
                        let c2_dec = (v, v, end_addr, new_node_id, perm, ty);
                        X(rs1) = CapVal(encode_cap(c1_dec));
                        reg_overwrite(rd_v);
                        X(rd) = CapVal(encode_cap(c2_dec));
                        RETIRE_SUCCESS
                    },
                    None() => {
                        handle_illegal();
                        RETIRE_FAIL
                    }
                }
            }
        },
        _ => {
            handle_illegal();
            RETIRE_FAIL
        }
    }
}

mapping clause assembly = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_SPLIT)
  <-> "split" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/************************************************************/

mapping clause encdec = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_SEAL)   <-> 0b0001010 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_SEAL)) = {
    let rd_v : regtype = X(rd);
    match(rd_v) {
        CapVal(c) if cap_type(c) == CAP_TYPE_LIN => {
            X(rd) = CapVal(cap_set_type(c, CAP_TYPE_SEALED));
            RETIRE_SUCCESS
        },
        _ => {
            handle_illegal();
            RETIRE_FAIL
        }
    }
}

mapping clause assembly = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_SEAL)
  <-> "seal" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/************************************************************/

mapping clause encdec = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_MREV)   <-> 0b0010001 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_MREV)) = {
    let rd_v : regtype = X(rd);
    let rs1_v : regtype = X(rs1);
    match(rs1_v) {
        CapVal(c) if cap_type(c) == CAP_TYPE_LIN => {
            let (cursor, start_addr, end_addr, node_id, perm, ty) = decode_cap(c);
            match(capnode_duplicate(node_id, true)) {
                Some(new_node_id) => {
                    let old_cap = (cursor, start_addr, end_addr, new_node_id, perm, ty);
                    let new_cap = (cursor, start_addr, end_addr, node_id, perm, CAP_TYPE_REV);
                    X(rs1) = CapVal(encode_cap(old_cap));
                    reg_overwrite(rd_v);
                    X(rd) = CapVal(encode_cap(new_cap));
                    RETIRE_SUCCESS
                },
                None() => {
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

mapping clause assembly = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_MREV)
  <-> "mrev" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)


/************************************************************/

mapping clause encdec = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_MOVC)   <-> 0b0001100 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_MOVC)) = {
    let rd_v : regtype = X(rd);
    let rs1_v : regtype = X(rs1);
    if(rd != rs1) then {
        reg_overwrite(rd_v); /* the dest register is overwritten */
        X(rd) = rs1_v;
        X(rs1) = reg_moved(rs1_v);
    };
    RETIRE_SUCCESS
}

mapping clause assembly = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_MOVC)
  <-> "movc" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)


/************************************************************/

mapping clause encdec = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_REVOKE)   <-> 0b0000000 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_REVOKE)) = {
    let rs1_v : regtype = X(rs1);
    
    match(rs1_v) {
        CapVal(c) if cap_type(c) == CAP_TYPE_REV => {
            let (_, _, _, node_id, _, _) = decode_cap(c);
            capnode_revoke(node_id);
            RETIRE_SUCCESS
        },
        _ => {
            handle_illegal();
            RETIRE_FAIL
        }
    }
}

mapping clause assembly = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_REVOKE)
  <-> "revoke" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)


/************************************************************/

mapping clause encdec = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_JMP)   <-> 0b0000010 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_JMP)) = {
    let rs1_v : regtype = X(rs1);
    
    match(rs1_v) {
        /* we don't check the permission or the type here. invalid values will trigger
        faults later */
        CapVal(c) => {
            reg_overwrite(CapVal(PCCap));
            X(rs1) = reg_moved(rs1_v);
            redirect_to_cap(c);
            RETIRE_SUCCESS
        },
        _ => {
            handle_illegal();
            RETIRE_FAIL
        }
    }
}

mapping clause assembly = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_JMP)
  <-> "jmp" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)


/************************************************************/

mapping clause encdec = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_JNZ)   <-> 0b0000011 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_JNZ)) = {
    let rs1_v : regtype = X(rs1);
    let rs2_v : regtype = X(rs2);
    
    match((rs1_v, rs2_v)) {
        (CapVal(c), RawVal(v)) => {
            if(v != EXTZ(0b0)) then {
                reg_overwrite(CapVal(PCCap));
                X(rs1) = reg_moved(rs1_v);
                redirect_to_cap(c);
            };
            RETIRE_SUCCESS
        },
        _ => {
            handle_illegal();
            RETIRE_FAIL
        }
    }
}

mapping clause assembly = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_JNZ)
  <-> "jnz" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)


/************************************************************/

mapping clause encdec = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_LWC)   <-> 0b0001110 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_LWC)) = {
    let rs1_v : regtype = X(rs1);
    let rd_v : regtype = X(rd);
    
    match(rs1_v) {
        CapVal(c) if cap_access_allowed(c, 16, CAP_PERM_RO) &
            capnode_query(cap_nodeid(c)) == 0b1 => {
            /* load data and tag */
            let addr = cap_cursor(c); 
            let v = capstone_load_mem(addr, 16);
            match(v) {
                CapVal(loaded_c) => {
                    reg_overwrite(rd_v);
                    X(rd) = v;
                    assert(mem_moved(addr, v)); /* the value is moved from the original location */
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

mapping clause assembly = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_LWC)
  <-> "lwc" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/************************************************************/

mapping clause encdec = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_LWS)   <-> 0b0010011 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_LWS)) = {
    let rs1_v : regtype = X(rs1);
    let rd_v : regtype = X(rd);
    
    match(rs1_v) {
        /* load only 8 bytes as here we only load raw data */
        CapVal(c) if cap_access_allowed(c, 8, CAP_PERM_RO) &
                capnode_query(cap_nodeid(c)) == 0b1 => {
            /* load data and tag */
            let addr = cap_cursor(c);
            let v = capstone_load_mem(addr, 8);
            reg_overwrite(rd_v);
            X(rd) = v;
            /* no need to check for linear cap move as only raw data is loaded */
            RETIRE_SUCCESS
        },
        _ => {
            handle_illegal();
            RETIRE_FAIL
        }
    }
}

mapping clause assembly = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_LWS)
  <-> "lws" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)


/************************************************************/

mapping clause encdec = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_SWC)   <-> 0b0001111 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_SWC)) = {
    let rs1_v : regtype = X(rs1);
    let rd_v : regtype = X(rd);

    match(rd_v) {
        CapVal(c) if cap_access_allowed(c, 16, CAP_PERM_RW)
                & capnode_query(cap_nodeid(c)) == 0b1 => {
            let addr = cap_cursor(c);
            mem_overwrite(addr, to_bits(xlen_val, 16));
            assert(capstone_store_mem(addr, 16, rs1_v));
            X(rs1) = reg_moved(rs1_v);
            if cap_type(c) == CAP_TYPE_UNINIT then {
                /* if the capability is uninitialized, then we
                need to increment the cursor by the size of the
                data being stored (16 bytes in this case) */
                X(rd) = CapVal(cap_set_cursor(c, addr + 16));
            };
            RETIRE_SUCCESS
        },
        _ => {
            handle_illegal();
            RETIRE_FAIL
        }
    }
}

mapping clause assembly = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_SWC)
  <-> "swc" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/************************************************************/

mapping clause encdec = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_DROPI)  <-> 0b0010000 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_DROPI)) =
    execute (CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_DROP))

mapping clause assembly = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_DROPI)
  <-> "dropi" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/************************************************************/

mapping clause encdec = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_L16S)  <-> 0b0011000 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_L16S)) = {
    let rs1_v : regtype = X(rs1);
    let rd_v : regtype = X(rd);
    
    match(rs1_v) {
        /* load only 2 bytes as here we only load raw data */
        CapVal(c) if cap_access_allowed(c, 2, CAP_PERM_RO) &
                capnode_query(cap_nodeid(c)) == 0b1 => {
            /* load data and tag */
            let addr = cap_cursor(c);
            let v = capstone_load_mem(addr, 2);
            reg_overwrite(rd_v);
            X(rd) = v;
            /* no need to check for linear cap move as only raw data is loaded */
            RETIRE_SUCCESS
        },
        _ => {
            handle_illegal();
            RETIRE_FAIL
        }
    }
}

mapping clause assembly = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_L16S)
  <-> "l16s" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/************************************************************/

mapping clause encdec = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_L32S)  <-> 0b0011001 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_L32S)) = {
    let rs1_v : regtype = X(rs1);
    let rd_v : regtype = X(rd);
    
    match(rs1_v) {
        /* load only 4 bytes as here we only load raw data */
        CapVal(c) if cap_access_allowed(c, 4, CAP_PERM_RO) &
                capnode_query(cap_nodeid(c)) == 0b1 => {
            /* load data and tag */
            let addr = cap_cursor(c);
            let v = capstone_load_mem(addr, 4);
            reg_overwrite(rd_v);
            X(rd) = v;
            /* no need to check for linear cap move as only raw data is loaded */
            RETIRE_SUCCESS
        },
        _ => {
            handle_illegal();
            RETIRE_FAIL
        }
    }
}

mapping clause assembly = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_L32S)
  <-> "l32s" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/************************************************************/

mapping clause encdec = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_S16S) <-> 0b0011010 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_S16S)) = {
    let rs1_v : regtype = X(rs1);
    let rd_v : regtype = X(rd);

    match(rd_v) {
        CapVal(c) if cap_access_allowed(c, 2, CAP_PERM_RW)
                & capnode_query(cap_nodeid(c)) == 0b1 => {
            let addr = cap_cursor(c);
            mem_overwrite(addr, to_bits(xlen_val, 2));
            assert(capstone_store_mem(addr, 2, rs1_v));
            X(rs1) = reg_moved(rs1_v);
            if cap_type(c) == CAP_TYPE_UNINIT then {
                /* if the capability is uninitialized, then we
                need to increment the cursor by the size of the
                data being stored (2 bytes in this case) */
                X(rd) = CapVal(cap_set_cursor(c, addr + 2));
            };
            RETIRE_SUCCESS
        },
        _ => {
            handle_illegal();
            RETIRE_FAIL
        }
    }
}

mapping clause assembly = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_S16S)
  <-> "s16s" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/************************************************************/

mapping clause encdec = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_S32S) <-> 0b0011011 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_S32S)) = {
    let rs1_v : regtype = X(rs1);
    let rd_v : regtype = X(rd);

    match(rd_v) {
        CapVal(c) if cap_access_allowed(c, 4, CAP_PERM_RW)
                & capnode_query(cap_nodeid(c)) == 0b1 => {
            let addr = cap_cursor(c);
            mem_overwrite(addr, to_bits(xlen_val, 4));
            assert(capstone_store_mem(addr, 4, rs1_v));
            X(rs1) = reg_moved(rs1_v);
            if cap_type(c) == CAP_TYPE_UNINIT then {
                /* if the capability is uninitialized, then we
                need to increment the cursor by the size of the
                data being stored (4 bytes in this case) */
                X(rd) = CapVal(cap_set_cursor(c, addr + 4));
            };
            RETIRE_SUCCESS
        },
        _ => {
            handle_illegal();
            RETIRE_FAIL
        }
    }
}

mapping clause assembly = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_S32S)
  <-> "s32s" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/************************************************************/

mapping clause encdec = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_SHS) <-> 0b0011100 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_SHS)) = {
    let rs1_v : regtype = X(rs1);
    let rd_v : regtype = X(rd);

    match(rd_v) {
        CapVal(c) if cap_access_allowed(c, 8, CAP_PERM_RW)
                & capnode_query(cap_nodeid(c)) == 0b1 => {
            let addr = cap_cursor(c);
            mem_overwrite(addr, to_bits(xlen_val, 8));
            assert(capstone_store_mem(addr, 8, rs1_v));
            X(rs1) = reg_moved(rs1_v);
            if cap_type(c) == CAP_TYPE_UNINIT then {
                /* if the capability is uninitialized, then we
                need to increment the cursor by the size of the
                data being stored (8 bytes in this case) */
                X(rd) = CapVal(cap_set_cursor(c, addr + 8));
            };
            RETIRE_SUCCESS
        },
        _ => {
            handle_illegal();
            RETIRE_FAIL
        }
    }
}

mapping clause assembly = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_SHS)
  <-> "shs" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/************************************************************/

mapping clause encdec = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_SBS) <-> 0b0011101 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_SBS)) = {
    let rs1_v : regtype = X(rs1);
    let rd_v : regtype = X(rd);

    match(rd_v) {
        CapVal(c) if cap_access_allowed(c, 1, CAP_PERM_RW)
                & capnode_query(cap_nodeid(c)) == 0b1 => {
            let addr = cap_cursor(c);
            mem_overwrite(addr, to_bits(xlen_val, 1));
            assert(capstone_store_mem(addr, 1, rs1_v));
            X(rs1) = reg_moved(rs1_v);
            if cap_type(c) == CAP_TYPE_UNINIT then {
                /* if the capability is uninitialized, then we
                need to increment the cursor by the size of the
                data being stored (1 bytes in this case) */
                X(rd) = CapVal(cap_set_cursor(c, addr + 1));
            };
            RETIRE_SUCCESS
        },
        _ => {
            handle_illegal();
            RETIRE_FAIL
        }
    }
}

mapping clause assembly = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_SBS)
  <-> "sbs" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/************************************************************/

mapping clause encdec = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_LBS) <-> 0b0010110 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_LBS)) = {
    let rs1_v : regtype = X(rs1);
    let rd_v : regtype = X(rd);
    
    match(rs1_v) {
        /* load only 1 bytes as here we only load raw data */
        CapVal(c) if cap_access_allowed(c, 1, CAP_PERM_RO) &
                capnode_query(cap_nodeid(c)) == 0b1 => {
            /* load data and tag */
            let addr = cap_cursor(c);
            let v = capstone_load_mem(addr, 1);
            reg_overwrite(rd_v);
            X(rd) = v;
            /* no need to check for linear cap move as only raw data is loaded */
            RETIRE_SUCCESS
        },
        _ => {
            handle_illegal();
            RETIRE_FAIL
        }
    }
}

mapping clause assembly = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_LBS)
  <-> "lbs" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/************************************************************/

mapping clause encdec = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_LHS) <-> 0b0010111 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_LHS)) = {
    let rs1_v : regtype = X(rs1);
    let rd_v : regtype = X(rd);
    
    match(rs1_v) {
        /* load only 8 bytes as here we only load raw data */
        CapVal(c) if cap_access_allowed(c, 8, CAP_PERM_RO) &
                capnode_query(cap_nodeid(c)) == 0b1 => {
            /* load data and tag */
            let addr = cap_cursor(c);
            let v = capstone_load_mem(addr, 8);
            reg_overwrite(rd_v);
            X(rd) = v;
            /* no need to check for linear cap move as only raw data is loaded */
            RETIRE_SUCCESS
        },
        _ => {
            handle_illegal();
            RETIRE_FAIL
        }
    }
}

mapping clause assembly = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_LHS)
  <-> "lhs" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/************************************************************/

/* TODO: details of capenter and capexit require etching out*/

/* capenter does the following
   1. check if the operand contains a sealed capability
   2. store the stack top address and PC in special registers
   3. unseal capability and swap in the context (similar to call)
   4. set the CPU mode to the secure world
Note that capenter does not store the full calling context. It is the
responsibility of the caller to store the calling context
*/

mapping clause encdec = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_CAPENTER)   <-> 0b0100000 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_CAPENTER)) = {
    let cur_npc = nextPC; /* PC address for resuming execution */
    let cur_sp = x2; /* current stack pointer */

    if mmode != CAPSTONE_MODE_NORMAL | capstone_call(rd, rs1, CAPSTONE_CALL_CAPENTER) != RETIRE_SUCCESS
    then {
        handle_illegal();
        RETIRE_FAIL
    } else {
        /* store the PC and stack pointer in special registers */
        normal_npc = cur_npc;
        normal_sp = cur_sp;
        /* set the CPU mode to secure world */
        mmode = CAPSTONE_MODE_SECURE;

        RETIRE_SUCCESS
    }
}

mapping clause assembly = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_CAPENTER)
  <-> "capenter" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)


/************************************************************/

/* capexit does the following
  1. recover the PC and stack top from the special registers
  2. (optional) seal the current context
  3. switch the CPU mode to the normal world

  Note that the capexit instruction does not restore the full context.
*/

mapping clause encdec = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_CAPEXIT)   <-> 0b0100001 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_CAPEXIT)) = {
    if mmode != CAPSTONE_MODE_SECURE | capstone_call(rd, rs1, CAPSTONE_CALL_CAPEXIT) != RETIRE_SUCCESS then {
        handle_illegal();
        RETIRE_FAIL
    } else {
        /* recover the PC and stack pointer from the special registers */
        nextPC = normal_npc;
        x2 = normal_sp;
        /* set the CPU mode to normal world */
        mmode = CAPSTONE_MODE_NORMAL;

        RETIRE_SUCCESS
    }
}

mapping clause assembly = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_CAPEXIT)
  <-> "capexit" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/************************************************************/

/* capget generates the genesis capability for the whole secure memory */

mapping clause encdec = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_CAPGET)   <-> 0b0011110 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_CAPGET)) = {
    let rd_v : regtype = X(rd);

    if mmode != CAPSTONE_MODE_NORMAL & not(capget_executed) then {
        handle_illegal();
        RETIRE_FAIL
    } else {
        /* create the genesis capability based on platform configurations of the memory regions */
        /* see riscv_types.sail */
        let genesis_cap = capstone_gen_genesis();
        reg_overwrite(rd_v);
        X(rd) = CapVal(genesis_cap);
        
        RETIRE_SUCCESS
    }
}

mapping clause assembly = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_CAPGET)
  <-> "capget" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

