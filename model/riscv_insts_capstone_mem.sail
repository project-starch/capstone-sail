/* Memory access instructions */

mapping clause encdec = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_LDC)   <-> 0b0010000 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_LDC)) = {
    let rs1_v : regtype = X(rs1);
    let rd_v : regtype = X(rd);

    match(rs1_v) {
        CapVal(c) if cap_access_allowed(c, 16, CAP_PERM_RO) &
            capnode_query(cap_nodeid(c)) == 0b1 => {
            /* load data and tag */
            let addr = cap_cursor(c); 
            let v = capstone_load_mem(addr, 16);
            // match(v) {
            //     CapVal(loaded_c) => {
            reg_overwrite(rd_v);
            X(rd) = v;
            assert(mem_moved(addr, v)); /* the value is moved from the original location */
            RETIRE_SUCCESS
            //     },
            //     _ => {
            //         handle_illegal();
            //         RETIRE_FAIL
            //     }
            // }
        },
        _ => {
            handle_illegal();
            RETIRE_FAIL
        }
    }
}

mapping clause assembly = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_LDC)
  <-> "ldc" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)


/************************************************************/

mapping clause encdec = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_STC)   <-> 0b0010001 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_STC)) = {
    let rs2_v : regtype = X(rs2);
    let rs1_v : regtype = X(rs1);

    match(rs1_v) {
        CapVal(c) if cap_access_allowed(c, 16, CAP_PERM_RW)
                & capnode_query(cap_nodeid(c)) == 0b1 => {
            let addr = cap_cursor(c);
            mem_overwrite(addr, to_bits(xlen_val, 16));
            assert(capstone_store_mem(addr, 16, rs2_v));
            X(rs2) = reg_moved(rs2_v);
            if cap_type(c) == CAP_TYPE_UNINIT then {
                /* if the capability is uninitialized, then we
                need to increment the cursor by the size of the
                data being stored (16 bytes in this case) */
                X(rs1) = CapVal(cap_set_cursor(c, addr + 16));
            };
            RETIRE_SUCCESS
        },
        _ => {
            handle_illegal();
            RETIRE_FAIL
        }
    }
}

mapping clause assembly = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_STC)
  <-> "stc" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/************************************************************/

mapping clause encdec = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_LDD)   <-> 0b0010010 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_LDD)) = {
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

mapping clause assembly = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_LDD)
  <-> "ldd" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/************************************************************/

mapping clause encdec = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_STD) <-> 0b0010011 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_STD)) = {
    let rs2_v : regtype = X(rs2);
    let rs1_v : regtype = X(rs1);

    match(rs1_v) {
        CapVal(c) if cap_access_allowed(c, 8, CAP_PERM_RW)
                & capnode_query(cap_nodeid(c)) == 0b1 => {
            let addr = cap_cursor(c);
            mem_overwrite(addr, to_bits(xlen_val, 8));
            assert(capstone_store_mem(addr, 8, rs2_v));
            X(rs2) = reg_moved(rs2_v);
            if cap_type(c) == CAP_TYPE_UNINIT then {
                /* if the capability is uninitialized, then we
                need to increment the cursor by the size of the
                data being stored (8 bytes in this case) */
                X(rs1) = CapVal(cap_set_cursor(c, addr + 8));
            };
            RETIRE_SUCCESS
        },
        _ => {
            handle_illegal();
            RETIRE_FAIL
        }
    }
}

mapping clause assembly = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_STD)
  <-> "std" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/************************************************************/

mapping clause encdec = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_LDW)  <-> 0b0010100 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_LDW)) = {
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

mapping clause assembly = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_LDW)
  <-> "ldw" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/************************************************************/

mapping clause encdec = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_STW) <-> 0b0010101 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_STW)) = {
    let rs2_v : regtype = X(rs2);
    let rs1_v : regtype = X(rs1);

    match(rs1_v) {
        CapVal(c) if cap_access_allowed(c, 4, CAP_PERM_RW)
                & capnode_query(cap_nodeid(c)) == 0b1 => {
            let addr = cap_cursor(c);
            mem_overwrite(addr, to_bits(xlen_val, 4));
            assert(capstone_store_mem(addr, 4, rs2_v));
            X(rs2) = reg_moved(rs2_v);
            if cap_type(c) == CAP_TYPE_UNINIT then {
                /* if the capability is uninitialized, then we
                need to increment the cursor by the size of the
                data being stored (4 bytes in this case) */
                X(rs1) = CapVal(cap_set_cursor(c, addr + 4));
            };
            RETIRE_SUCCESS
        },
        _ => {
            handle_illegal();
            RETIRE_FAIL
        }
    }
}

mapping clause assembly = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_STW)
  <-> "stw" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/************************************************************/

mapping clause encdec = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_LDH)  <-> 0b0010110 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_LDH)) = {
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

mapping clause assembly = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_LDH)
  <-> "ldh" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/************************************************************/

mapping clause encdec = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_STH) <-> 0b0010111 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_STH)) = {
    let rs2_v : regtype = X(rs2);
    let rs1_v : regtype = X(rs1);

    match(rs1_v) {
        CapVal(c) if cap_access_allowed(c, 2, CAP_PERM_RW)
                & capnode_query(cap_nodeid(c)) == 0b1 => {
            let addr = cap_cursor(c);
            mem_overwrite(addr, to_bits(xlen_val, 2));
            assert(capstone_store_mem(addr, 2, rs2_v));
            X(rs2) = reg_moved(rs2_v);
            if cap_type(c) == CAP_TYPE_UNINIT then {
                /* if the capability is uninitialized, then we
                need to increment the cursor by the size of the
                data being stored (2 bytes in this case) */
                X(rs1) = CapVal(cap_set_cursor(c, addr + 2));
            };
            RETIRE_SUCCESS
        },
        _ => {
            handle_illegal();
            RETIRE_FAIL
        }
    }
}

mapping clause assembly = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_STH)
  <-> "sth" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/************************************************************/

mapping clause encdec = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_LDB) <-> 0b0011000 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_LDB)) = {
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

mapping clause assembly = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_LDB)
  <-> "ldb" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)


/************************************************************/

mapping clause encdec = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_STB) <-> 0b0011001 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_STB)) = {
    let rs2_v : regtype = X(rs2);
    let rs1_v : regtype = X(rs1);

    match(rs1_v) {
        CapVal(c) if cap_access_allowed(c, 1, CAP_PERM_RW)
                & capnode_query(cap_nodeid(c)) == 0b1 => {
            let addr = cap_cursor(c);
            mem_overwrite(addr, to_bits(xlen_val, 1));
            assert(capstone_store_mem(addr, 1, rs2_v));
            X(rs2) = reg_moved(rs2_v);
            if cap_type(c) == CAP_TYPE_UNINIT then {
                /* if the capability is uninitialized, then we
                need to increment the cursor by the size of the
                data being stored (1 bytes in this case) */
                X(rs1) = CapVal(cap_set_cursor(c, addr + 1));
            };
            RETIRE_SUCCESS
        },
        _ => {
            handle_illegal();
            RETIRE_FAIL
        }
    }
}

mapping clause assembly = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_STB)
  <-> "stb" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

