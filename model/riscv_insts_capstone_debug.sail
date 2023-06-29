union clause ast = CAPSTONE_INSN_R : (regidx, regidx, regidx, capstone_op_r)
union clause ast = CAPSTONE_INSN_I : (regidx, regidx, imm12, capstone_op_i)

/************************************************************/

/** Instructions for testing only */

mapping clause encdec = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_QUERY)   <-> 0b0000000 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_QUERY)) = {
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

mapping clause assembly = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_QUERY)
  <-> "query" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)


/************************************************************/

mapping clause encdec = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_RCUPDATE)   <-> 0b0000001 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1011011

/*
update the ref count for a given node id directly
*/
function clause execute (CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_RCUPDATE)) = {
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

mapping clause assembly = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_RCUPDATE)
  <-> "rcupdate" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/************************************************************/

mapping clause encdec = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_ALLOC)   <-> 0b0000010 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1011011

/*
allocates a new child node for a given revocation node and stores the id of the new node
in the destination register
*/
function clause execute (CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_ALLOC)) = {
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

mapping clause assembly = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_ALLOC)
  <-> "alloc" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)


/************************************************************/

/* revoke a node with the given id */

mapping clause encdec = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_REV)   <-> 0b0000011 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_REV)) = {
    let rs1_v : regtype = X(rs1);
    match(rs1_v) {
        RawVal(node_id) => {
            capnode_revoke(truncate(node_id, capnodeidlen_v));
            RETIRE_SUCCESS
        },
        _ => {
            handle_illegal();
            RETIRE_FAIL
        }
    }
}

mapping clause assembly = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_REV)
  <-> "rev" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/************************************************************/

mapping clause encdec = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_CAPCREATE)   <-> 0b0000100 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_CAPCREATE)) = {
    X(rd) = CapVal(EXTZ(0b0));
    RETIRE_SUCCESS
}

mapping clause assembly = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_CAPCREATE)
  <-> "capcreate" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)


/************************************************************/

mapping clause encdec = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_CAPTYPE)   <-> 0b0000101 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_CAPTYPE)) = {
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

mapping clause assembly = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_CAPTYPE)
  <-> "captype" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)


/************************************************************/

mapping clause encdec = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_CAPNODE)   <-> 0b0000110 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_CAPNODE)) = {
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

mapping clause assembly = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_CAPNODE)
  <-> "capnode" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)


/************************************************************/

mapping clause encdec = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_CAPPERM)   <-> 0b0000111 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_CAPPERM)) = {
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

mapping clause assembly = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_CAPPERM)
  <-> "capperm" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)


/************************************************************/

mapping clause encdec = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_CAPBOUND)   <-> 0b0001000 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_CAPBOUND)) = {
    let rd_v : regtype = X(rd);
    let rs1_v : regtype = X(rs1);
    let rs2_v : regtype = X(rs2);
    match((rs1_v, rs2_v, rd_v)) {
        (RawVal(v1), RawVal(v2), CapVal(cv)) => {
            X(rd) = CapVal(cap_set_bound_cursor(cv, v1, v1, v2));
            RETIRE_SUCCESS
        },
        _ => {
            // invalid operands
            handle_illegal();
            RETIRE_FAIL
        }
    }
}

mapping clause assembly = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_CAPBOUND)
  <-> "capbound" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/************************************************************/

mapping clause encdec = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_CAPPRINT)   <-> 0b0001001 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_CAPPRINT)) = {
    let rs1_v : regtype = X(rs1);
    print_string("capprint: ", RegStr(rs1_v));
    RETIRE_SUCCESS
}

mapping clause assembly = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_CAPPRINT)
  <-> "capprint" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/************************************************************/

mapping clause encdec = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_TAGSET)   <-> 0b0001010 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_TAGSET)) = {
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

mapping clause assembly = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_TAGSET)
  <-> "tagset" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/************************************************************/

mapping clause encdec = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_TAGGET)   <-> 0b0001011 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_TAGGET)) = {
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

mapping clause assembly = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_TAGGET)
  <-> "tagget" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)
