/* Capability manipulation instructions */

mapping clause encdec = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_REVOKE)   <-> 0b0000000 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_REVOKE)) = {
    let rs1_v : regtype = X(rs1);
    
    match(rs1_v) {
        CapVal(c) => {
            let (node_id, metadata) = decode_cap(c);
            if capnode_query(node_id) == 0b0 then {
                handle_capstone_except(E_Invalid_Cap());
                RETIRE_FAIL
            } else if cap_type(c) != CAP_TYPE_REV then {
                handle_capstone_except(E_Cap_Type_Fault());
                RETIRE_FAIL
            } else {
                match metadata {
                    RevocationCapMetadata(cursor, base_addr, end_addr, perm) => {
                        let new_cap = if capnode_revoke(node_id) then {
                            /* exclusive node invalidated, make the result uninitialised cap */
                            (node_id, UninitialisedCapMetadata(base_addr, base_addr, end_addr, perm))
                        } else {
                            /* the result would be a linear capability */
                            (node_id, LinearCapMetadata(cursor, base_addr, end_addr, perm))
                        };
                        X(rs1) = CapVal(encode_cap(new_cap));
                    },
                    _ => {
                        assert(false);
                    }
                };
                RETIRE_SUCCESS
            }
        },
        _ => {
            handle_capstone_except(E_Op_Type_Fault());
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
    match(rd_v, rs1_v, rs2_v) {
        (CapVal(cv), RawVal(v1), RawVal(v2)) => {
            let ty = cap_type(cv);
            let (base_addr, end_addr) = cap_bounds(cv);

            if ty != CAP_TYPE_LIN & ty != CAP_TYPE_NONLIN & ty != CAP_TYPE_UNINIT then {
                handle_capstone_except(E_Cap_Type_Fault());
                RETIRE_FAIL
            } else if  unsigned(v1) >= unsigned(v2) |
                       unsigned(v1) < unsigned(base_addr) |
                       unsigned(v2) > unsigned(end_addr) then {
                handle_capstone_except(E_Illegal_Op_Val());
                RETIRE_FAIL
            } else {
                let res = cap_shrink(cv, v1, v2);
                match res {
                    Some(ncv) => {
                        X(rd) = CapVal(ncv);
                    },
                    _ => {
                        /* we have done the checks */
                        /* shouldn't fail here */
                        assert(false);
                    }
                };

                RETIRE_SUCCESS
            }
            

        },
        _ => {
            handle_capstone_except(E_Op_Type_Fault());
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
        CapVal(cv) => {
            let ty = cap_type(cv);
            let perm = cap_perm(cv);
            if ty != CAP_TYPE_LIN & ty != CAP_TYPE_NONLIN & ty != CAP_TYPE_UNINIT then {
                handle_capstone_except(E_Cap_Type_Fault());
                RETIRE_FAIL
            } else if unsigned(imm) <= 7 & not(capperm_bits(imm[2..0]) <=_p perm) then {
                handle_capstone_except(E_Illegal_Op_Val());
                RETIRE_FAIL
            } else {
                let perm : capperm_t = if unsigned(imm) > 7 then
                    CAP_PERM_NA
                else
                    capperm_bits(imm[2..0]);

                match(cap_tighten(cv, perm)) {
                    Some(ncv) => {
                        X(rd) = CapVal(ncv);
                    },
                    _ => {
                        /* we have done the checks */
                        /* shouldn't fail here */
                        assert(false);
                    }
                };

                RETIRE_SUCCESS
            }
        },
        _ => {
            handle_capstone_except(E_Op_Type_Fault());
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
                    handle_capstone_except(E_Cap_Type_Fault());
                    RETIRE_FAIL
                }
            }
        },
        _ => {
            handle_capstone_except(E_Op_Type_Fault());
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
            let ty = cap_type(cv) in
            let imm_v = unsigned(imm) in
            let bad_cap_type =
                (imm_v == 2 & ty == CAP_TYPE_SEALED) |
                (imm_v == 4 & (ty == CAP_TYPE_SEALED | ty == CAP_TYPE_SEALEDRET | ty == CAP_TYPE_EXIT)) |
                (imm_v == 5 & (ty == CAP_TYPE_SEALED | ty == CAP_TYPE_SEALEDRET | ty == CAP_TYPE_EXIT)) |
                (imm_v == 6 & ty != CAP_TYPE_SEALED & ty != CAP_TYPE_SEALEDRET) |
                (imm_v == 7 & ty != CAP_TYPE_SEALEDRET) in
            if bad_cap_type then {
                handle_capstone_except(E_Cap_Type_Fault());
                RETIRE_FAIL
            } else {
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
            }
        },
        _ => {
            handle_capstone_except(E_Op_Type_Fault());
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
    let rs2_v : regtype = X(rs2);
    match(rs1_v, rs2_v) {
        /* we do not allow setting cursor of an uninitialised capability */
        /* instead of faulting we do nothing if the type does not have cursor */
        (CapVal(cv), RawVal(v)) => {
            let ty = cap_type(cv);
            if ty == CAP_TYPE_UNINIT | ty == CAP_TYPE_SEALED then {
                handle_capstone_except(E_Cap_Type_Fault());
                RETIRE_FAIL
            } else {
                if rs1 != rd then {
                    X(rs1) = reg_moved(rs1_v);
                    reg_overwrite(rd_v);
                };
                X(rd) = CapVal(cap_set_cursor(cv, v));
                RETIRE_SUCCESS
            }
        },
        _ => {
            handle_capstone_except(E_Op_Type_Fault());
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
    match(rs1_v, rs2_v) {
        (CapVal(c), RawVal(v)) => {
            let node_id = cap_nodeid(c);
            let ty = cap_type(c);
            let (base_addr, end_addr) = cap_bounds(c);
            let perm = cap_perm(c);

            if capnode_query(node_id) == 0b0 then {
                handle_capstone_except(E_Invalid_Cap());
                RETIRE_FAIL
            } else if ty != CAP_TYPE_LIN & ty != CAP_TYPE_NONLIN then {
                handle_capstone_except(E_Cap_Type_Fault());
                RETIRE_FAIL
            } else if unsigned(v) <= unsigned(base_addr) | unsigned(v) >= unsigned(end_addr) then {
                handle_capstone_except(E_Illegal_Op_Val());
                RETIRE_FAIL
            } else {
                if rs1 == rd then ()
                else if ty == CAP_TYPE_LIN then {
                    /* duplicate the node */
                    match capnode_duplicate(node_id, false) {
                        Some(new_node_id) => {
                            X(rs1) = CapVal(encode_cap((node_id, LinearCapMetadata(base_addr, base_addr, v, perm))));
                            reg_overwrite(rd_v);
                            X(rd) = CapVal(encode_cap((new_node_id, LinearCapMetadata(v, v, end_addr, perm))));
                        },
                        None() => {
                            assert(false);
                        }
                    };
                } else {
                    assert(ty == CAP_TYPE_NONLIN);
                    X(rs1) = CapVal(encode_cap((node_id, NonLinearCapMetadata(base_addr, base_addr, v, perm))));
                    reg_overwrite(rd_v);
                    X(rd) = CapVal(encode_cap((node_id, NonLinearCapMetadata(v, v, end_addr, perm))));
                };

                RETIRE_SUCCESS
            }
        },
        _ => {
            handle_capstone_except(E_Op_Type_Fault());
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

    match rs1_v {
        CapVal(c) => {
            let (node_id, metadata) = decode_cap(c);
            match metadata {
                LinearCapMetadata(_, base_addr, end_addr, perms) => {
                    if not(CAP_PERM_RW <=_p perms) then {
                        handle_capstone_except(E_Cap_Perm_Fault());
                        RETIRE_FAIL
                    } else if unsigned(end_addr - base_addr) < 33 * caplen_bytes_v |
                        not(capstone_addr_aligned(base_addr, caplen_bytes_w)) then {
                        /* FIXME: here we do not perform check on the memory content yet */
                        handle_capstone_except(E_Illegal_Op_Val());
                        RETIRE_FAIL
                    } else {
                        if rs1 != rd then {
                            X(rs1) = reg_moved(rs1_v);
                            reg_overwrite(rd_v);
                        };
                        X(rd) = CapVal(encode_cap((node_id, SealedCapMetadata(base_addr, 0b00))));

                        RETIRE_SUCCESS
                    }
                },
                _ => {
                    handle_capstone_except(E_Cap_Type_Fault());
                    RETIRE_FAIL
                }
            }
        },
        _ => {
            handle_capstone_except(E_Op_Type_Fault());
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
    match rs1_v {
        CapVal(c) => {
            let (node_id, metadata) = decode_cap(c);
            if capnode_query(node_id) == 0b0 then {
                handle_capstone_except(E_Invalid_Cap());
                RETIRE_FAIL
            } else
                match metadata {
                    LinearCapMetadata(cursor, start_addr, end_addr, perm) => {
                        match(capnode_duplicate(node_id, true)) {
                            Some(new_node_id) => {
                                let old_cap = (new_node_id, LinearCapMetadata(cursor, start_addr, end_addr, perm));
                                let new_cap = (node_id, RevocationCapMetadata(cursor, start_addr, end_addr, perm));
                                X(rs1) = CapVal(encode_cap(old_cap));
                                reg_overwrite(rd_v); /* this is required no matter if rd = rs1 */
                                X(rd) = CapVal(encode_cap(new_cap));
                            },
                            None() => {
                                assert(false);
                            }
                        };

                        RETIRE_SUCCESS
                    },
                    _ => {
                        handle_capstone_except(E_Cap_Type_Fault());
                        RETIRE_FAIL
                    }
                }
        },
        _ => {
            handle_capstone_except(E_Op_Type_Fault());
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
        (CapVal(cv), RawVal(v)) => {
            let ty = cap_type(cv);
            if ty != CAP_TYPE_UNINIT then {
                handle_capstone_except(E_Cap_Type_Fault());
                RETIRE_FAIL
            } else if not(capstone_cap_initialised(cv)) then {
                handle_capstone_except(E_Illegal_Op_Val());
                RETIRE_FAIL
            } else {
                if rs1 != rd then {
                    reg_overwrite(rd_v);
                    X(rs1) = reg_moved(rs1_v);
                };
                let (base, _) = cap_bounds(cv);
                let ncv = cap_set_cursor(capstone_initialise_nocheck(cv), base + v);
                X(rd) = CapVal(ncv);

                RETIRE_SUCCESS
            }
        },
        _ => {
            handle_capstone_except(E_Op_Type_Fault());
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
    let rs1_v : regtype = if unsigned(rs1) == 0 then CapVal(CAP_INVALID) else X(rs1);
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
            handle_capstone_except(E_Op_Type_Fault());
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
        CapVal(c) => {
            if captype_is_linear(cap_type(c)) then {
                assert(capnode_invalidate(cap_nodeid(c)),
                    "drop: unable to invalidate the revocation node"); /* TODO: might also consider removing it from the revocation tree (optional) */
            };
            RETIRE_SUCCESS
        },
        _ => {
            handle_capstone_except(E_Op_Type_Fault());
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
            let ty = cap_type(c);

            if ty == CAP_TYPE_UNINIT | ty == CAP_TYPE_SEALED then {
                handle_capstone_except(E_Cap_Type_Fault());
                RETIRE_FAIL
            } else {
                if rs1 != rd then {
                    /* only when the source register is not simultaneously written */
                    X(rs1) = reg_moved(rs1_v);
                    reg_overwrite(rd_v);
                };
                let new_cursor = cap_cursor(c) + offset in
                    X(rd) = CapVal(cap_set_cursor(c, new_cursor));

                RETIRE_SUCCESS
            }
        },
        _ => {
            handle_capstone_except(E_Op_Type_Fault());
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
            let ty = cap_type(c);

            if ty == CAP_TYPE_UNINIT | ty == CAP_TYPE_SEALED then {
                handle_capstone_except(E_Cap_Type_Fault());
                RETIRE_FAIL
            } else {
                if rs1 != rd then {
                    /* only when the source register is not simultaneously written */
                    X(rs1) = reg_moved(rs1_v);
                    reg_overwrite(rd_v);
                };
                let new_cursor = cap_cursor(c) + imm_v in
                    X(rd) = CapVal(cap_set_cursor(c, new_cursor));

                RETIRE_SUCCESS
            }
        },
        _ => {
            handle_capstone_except(E_Op_Type_Fault());
            RETIRE_FAIL
        }
    }
}

mapping clause assembly = CAPSTONE_INSN_I(rs1, rd, imm, CAPSTONE_CINCOFFSETIMM)
  <-> "cincoffsetimm" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ hex_bits_12(imm)
