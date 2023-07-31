/* Architectural instructions */

mapping clause encdec = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_REVOKE)   <-> 0b0000000 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_REVOKE)) = {
    let rs1_v : regtype = X(rs1);
    
    match(rs1_v) {
        CapVal(c) if cap_type(c) == CAP_TYPE_REV => {
            let (node_id, _) = decode_cap(c);
            capnode_revoke(node_id);
            RETIRE_SUCCESS
        },
        _ => {
            handle_illegal();
            RETIRE_FAIL
        }
    }
}

mapping clause assembly = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_REVOKE)
  <-> "revoke" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/************************************************************/


mapping clause encdec = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_SHRINK)   <-> 0b0000001 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_SHRINK)) = {
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

mapping clause assembly = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_SHRINK)
  <-> "shrink" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/************************************************************/

mapping clause encdec = CAPSTONE_INSN_R(imm, rs1, rd, CAPSTONE_TIGHTEN)   <-> 0b0000010 @ imm @ rs1 @ 0b001 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN_R(imm, rs1, rd, CAPSTONE_TIGHTEN)) = {
    let rd_v : regtype = X(rd);
    let rs1_v : regtype = X(rs1);
    match rs1_v {
        CapVal(cv) if capperm_bits_backwards_matches(imm[2..0]) => {
            match(cap_tighten(cv, capperm_bits(imm[2..0]))) {
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

mapping clause assembly = CAPSTONE_INSN_R(imm, rs1, rd, CAPSTONE_TIGHTEN)
  <-> "tighten" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ hex_bits_5(imm)

/************************************************************/

mapping clause encdec = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_DELIN)   <-> 0b0000011 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_DELIN)) = {
    let rd_v : regtype = X(rd);
    match(rd_v) {
        CapVal(cv) => {
            let (nid, metadata) = decode_cap(cv);
            match metadata {
                LinearCapMetadata(cursor, base_addr, end_addr, perm) => {
                    let nv_metadata = NonLinearCapMetadata(cursor, base_addr, end_addr, perm);
                    X(rd) = CapVal(encode_cap((nid, nv_metadata)));
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

mapping clause assembly = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_DELIN)
  <-> "delin" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/************************************************************/

mapping clause encdec = CAPSTONE_INSN_R(imm, rs1, rd, CAPSTONE_LCC)   <-> 0b0000100 @ imm @ rs1 @ 0b001 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN_R(imm, rs1, rd, CAPSTONE_LCC)) = {
    let rs1_v : regtype = X(rs1);
    let rd_v : regtype = X(rd);
    match rs1_v {
        CapVal(cv) => {
            let res : xlenbits = match unsigned(imm) {
                0 => cap_get_valid_xlenbits(cv),
                1 => cap_get_type_xlenbits(cv),
                2 => cap_get_cursor_xlenbits(cv),
                3 => cap_get_base_xlenbits(cv),
                4 => cap_get_end_xlenbits(cv),
                5 => cap_get_perms_xlenbits(cv),
                6 => cap_get_async_xlenbits(cv),
                7 => cap_get_reg_xlenbits(cv),
                _ => EXTZ(0b0) : xlenbits
            };
            reg_overwrite(rd_v);
            X(rd) = RawVal(res);
            RETIRE_SUCCESS
        },
        _ => {
            handle_illegal();
            RETIRE_FAIL
        }
    }
}

mapping clause assembly = CAPSTONE_INSN_R(imm, rs1, rd, CAPSTONE_LCC)
  <-> "lcc" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ hex_bits_5(imm)

/************************************************************/

mapping clause encdec = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_SCC)   <-> 0b0000101 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_SCC)) = {
    let rd_v : regtype = X(rd);
    let rs1_v : regtype = X(rs1);
    match((rd_v, rs1_v)) {
        /* we do not allow setting cursor of an uninitialised capability */
        /* instead of faulting we do nothing if the type does not have cursor */
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

mapping clause assembly = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_SCC)
  <-> "scc" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/************************************************************/

mapping clause encdec = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_SPLIT)   <-> 0b0000110 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_SPLIT)) = {
    let rs1_v : regtype = X(rs1);
    let rs2_v : regtype = X(rs2);
    let rd_v : regtype = X(rd);
    match((rs1_v, rs2_v)) {
        (CapVal(c), RawVal(v)) => {
            let (node_id, metadata) = decode_cap(c);

            /* only allow linear capabilities for now */
            match metadata {
                LinearCapMetadata(cursor, start_addr, end_addr, perm) => {
                    if(unsigned(v) < unsigned(start_addr) | unsigned(v) > unsigned(end_addr) |
                        capnode_query(node_id) == 0b1) then {
                        handle_illegal();
                        RETIRE_FAIL
                    } else {
                        /* duplicate the node */
                        match(capnode_duplicate(node_id, false)) {
                            Some(new_node_id) => {
                                X(rs1) = CapVal(encode_cap((node_id, LinearCapMetadata(start_addr, start_addr, v, perm))));
                                reg_overwrite(rd_v);
                                X(rd) = CapVal(encode_cap((new_node_id, LinearCapMetadata(v, v, end_addr, perm))));
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
        },
        _ => {
            handle_illegal();
            RETIRE_FAIL
        }
    }
}

mapping clause assembly = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_SPLIT)
  <-> "split" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/************************************************************/

mapping clause encdec = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_SEAL)   <-> 0b0000111 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_SEAL)) = {
    let rd_v : regtype = X(rd);
    let rs1_v : regtype = X(rs1);

    match(rd_v, rs1_v) {
        (CapVal(c), RawVal(v)) => {
            let (node_id, metadata) = decode_cap(c);
            match metadata {
                LinearCapMetadata(_, base_addr, end_addr, perms) if 
                        (unsigned(end_addr - base_addr) >= 33 * caplen_bytes_v) &
                        (CAP_PERM_RW <=_p perms) => {
                    X(rd) = CapVal(encode_cap((node_id, SealedCapMetadata(base_addr, 0b00))));
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

mapping clause assembly = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_SEAL)
  <-> "seal" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/************************************************************/

mapping clause encdec = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_MREV)   <-> 0b0001000 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_MREV)) = {
    let rd_v : regtype = X(rd);
    let rs1_v : regtype = X(rs1);
    match(rs1_v) {
        CapVal(c) if cap_type(c) == CAP_TYPE_LIN => {
            let (node_id, metadata) = decode_cap(c);
            match metadata {
                LinearCapMetadata(cursor, start_addr, end_addr, perm) => {
                    match(capnode_duplicate(node_id, true)) {
                        Some(new_node_id) => {
                            let old_cap = (new_node_id, LinearCapMetadata(cursor, start_addr, end_addr, perm));
                            let new_cap = (node_id, RevocationCapMetadata(cursor, start_addr, end_addr, perm));
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
        },
        _ => {
            handle_illegal();
            RETIRE_FAIL
        }
    }
}

mapping clause assembly = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_MREV)
  <-> "mrev" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/************************************************************/

mapping clause encdec = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_INIT)  <-> 0b0001001 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_INIT)) = {
    let rd_v : regtype = X(rd);
    let rs1_v : regtype = X(rs1);
    let rs2_v : regtype = X(rs2);

    match(rs1_v, rs2_v) {
        (CapVal(cv), RawVal(v)) if capstone_cap_initialised(cv) => {
            let ncv = cap_set_cursor(capstone_initialise_nocheck(cv), v);
            reg_overwrite(rd_v);
            X(rs1) = reg_moved(rs1_v);
            X(rd) = CapVal(ncv);
            RETIRE_SUCCESS
        },
        _ => {
            handle_illegal();
            RETIRE_FAIL
        }
    }
}

mapping clause assembly = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_INIT)
  <-> "init" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/************************************************************/

mapping clause encdec = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_MOVC)   <-> 0b0001010 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_MOVC)) = {
    let rd_v : regtype = X(rd);
    let rs1_v : regtype = X(rs1);
    match(rs1_v) {
        CapVal(_) => {
            if(rd != rs1) then {
                reg_overwrite(rd_v); /* the dest register is overwritten */
                X(rs1) = reg_moved(rs1_v);
                X(rd) = rs1_v;
            };
            RETIRE_SUCCESS
        },
        _ => {
            handle_illegal();
            RETIRE_FAIL
        }
    }
}

mapping clause assembly = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_MOVC)
  <-> "movc" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/************************************************************/
/* directly invalidate a specific capability (can only be one of the linear types that
would be associated uniquely with a revocation node) */

mapping clause encdec = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_DROP)   <-> 0b0001011 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_DROP)) = {
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

mapping clause assembly = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_DROP)
  <-> "drop" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/************************************************************/

mapping clause encdec = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_CINCOFFSET)   <-> 0b0001100 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_CINCOFFSET)) = {
    let rd_v : regtype = X(rd);
    let rs1_v : regtype = X(rs1);
    let rs2_v : regtype = X(rs2);
    match (rs1_v, rs2_v) {
        (CapVal(c), RawVal(offset)) => {
            let new_cursor = cap_cursor(c) + offset;
            X(rd) = CapVal(cap_set_cursor(c, new_cursor));
            reg_overwrite(rd_v);
            if rs1 != rd then X(rs1) = reg_moved(rs1_v); /* only when the source register is not simultaneously written */
            RETIRE_SUCCESS
        },
        _ => {
            handle_illegal();
            RETIRE_FAIL
        }
    }
}

mapping clause assembly = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_CINCOFFSET)
  <-> "cincoffset" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/************************************************************/

mapping clause encdec = CAPSTONE_INSN_I(rs1, rd, imm, CAPSTONE_CINCOFFSETIMM) <-> imm @ rs1 @ 0b010 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN_I(rs1, rd, imm, CAPSTONE_CINCOFFSETIMM)) = {
    let rd_v : regtype = X(rd);
    let rs1_v : regtype = X(rs1);
    let imm_v : xlenbits = EXTS(imm);

    match(rs1_v) {
        CapVal(c) => {
            let new_cursor = cap_cursor(c) + imm_v;
            X(rd) = CapVal(cap_set_cursor(c, new_cursor));
            reg_overwrite(rd_v);
            if rs1 != rd then X(rs1) = reg_moved(rs1_v); /* only when the source register is not simultaneously written */
            RETIRE_SUCCESS
        },
        _ => {
            handle_illegal();
            RETIRE_FAIL
        }
    }
}

mapping clause assembly = CAPSTONE_INSN_I(rs1, rd, imm, CAPSTONE_CINCOFFSETIMM)
  <-> "cincoffsetimm" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ hex_bits_12(imm)
