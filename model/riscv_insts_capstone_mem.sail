/* Memory access instructions */

mapping clause encdec = CAPSTONE_INSN_I(rs1, rd, imm, CAPSTONE_LDC) <-> imm @ rs1 @ 0b011 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN_I(rs1, rd, imm, CAPSTONE_LDC)) = {
    let rs1_v : regtype = X(rs1);
    let rd_v : regtype = X(rd);

    let use_cap = capstone_in_secure_world() | emode == bitone;

    match(use_cap, rs1_v) {
        (true, CapVal(c)) => {
            /* load using a capability */
            let ty = cap_type(c); 
            let perm = cap_perm(c);
            if capnode_query(cap_nodeid(c)) == 0b1 then {
                handle_capstone_except(E_Invalid_Cap());
                RETIRE_FAIL
            } else if (ty != CAP_TYPE_LIN &
                      ty != CAP_TYPE_NONLIN &
                      ty != CAP_TYPE_SEALEDRET &
                      ty != CAP_TYPE_EXIT) |
                      (ty == CAP_TYPE_SEALEDRET & cap_async(c) != 0b00) then {
                handle_capstone_except(E_Cap_Type_Fault());
                RETIRE_FAIL
            } else if (ty == CAP_TYPE_LIN | ty == CAP_TYPE_NONLIN) & not(CAP_PERM_RO <=_p perm) then {
                handle_capstone_except(E_Cap_Perm_Fault());
                RETIRE_FAIL
            } else if not(cap_in_bound(c, cap_cursor(c) + EXTS(imm), 16)) then {
                handle_capstone_except(E_Cap_Out_Of_Bounds());
                RETIRE_FAIL
            } else {
                /* load data and tag */
                let addr = cap_cursor(c) + EXTS(imm) : xlenbits; 
                let v = capstone_load_mem(addr, 16);
                
                match v {
                    CapVal(cv) => {
                        if captype_is_linear(cap_type(cv)) & not(CAP_PERM_WO <=_p perm) then {
                            handle_capstone_except(E_Cap_Perm_Fault());
                            RETIRE_FAIL
                        } else {
                            reg_overwrite(rd_v);
                            X(rd) = v;
                            assert(mem_moved(addr, v)); /* the value is moved from the original location */

                            RETIRE_SUCCESS
                        }
                    },
                    _ => {
                        handle_capstone_except(E_Cap_Type_Fault());
                        RETIRE_FAIL
                    }
                }

            }
        },
        (false, RawVal(v)) => {
            /* load using raw address */
            let addr = v + EXTS(imm) : xlenbits;
            let (paddr, cv) = capstone_load_mem_virt(addr, 16);
            /* TODO: check on the physical address range */

            match cv {
                CapVal(_) => {
                    reg_overwrite(rd_v);
                    X(rd) = cv;
                    assert(mem_moved(paddr, cv)); /* the value is moved from the original location */

                    RETIRE_SUCCESS
                },
                _ => {
                    handle_capstone_except(E_Load_Access_Fault());
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

mapping clause assembly = CAPSTONE_INSN_I(rs1, rd, imm, CAPSTONE_LDC)
  <-> "ldc" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ hex_bits_12(imm)


/************************************************************/

mapping clause encdec = CAPSTONE_INSN_S(rs2, rs1, imm7, imm5, CAPSTONE_STC)   <-> imm7 @ rs2 @ rs1 @ 0b110 @ imm5 @ 0b1011011

function clause execute (CAPSTONE_INSN_S(rs2, rs1, imm7, imm5, CAPSTONE_STC)) = {
    let rs2_v : regtype = X(rs2);
    let rs1_v : regtype = X(rs1);
    let imm = imm7 @ imm5;

    let use_cap = capstone_in_secure_world() | emode == bitone;

    match(use_cap, rs1_v, rs2_v) {
        (true, CapVal(c), CapVal(_)) => {
            /* store using a capability */
            let ty = cap_type(c); 
            let perm = cap_perm(c);
            if capnode_query(cap_nodeid(c)) == 0b1 then {
                handle_capstone_except(E_Invalid_Cap());
                RETIRE_FAIL
            } else if (ty != CAP_TYPE_LIN &
                      ty != CAP_TYPE_NONLIN &
                      ty != CAP_TYPE_UNINIT & 
                      ty != CAP_TYPE_SEALEDRET &
                      ty != CAP_TYPE_EXIT) |
                      (ty == CAP_TYPE_SEALEDRET & cap_async(c) != 0b00) then {
                handle_capstone_except(E_Cap_Type_Fault());
                RETIRE_FAIL
            } else if (ty == CAP_TYPE_LIN | ty == CAP_TYPE_NONLIN) & not(CAP_PERM_WO <=_p perm) then {
                handle_capstone_except(E_Cap_Perm_Fault());
                RETIRE_FAIL
            } else if not(cap_in_bound(c, cap_cursor(c) + EXTS(imm), 16)) then {
                handle_capstone_except(E_Cap_Out_Of_Bounds());
                RETIRE_FAIL
            } else if ty == CAP_TYPE_UNINIT & unsigned(imm) != 0 then {
                handle_capstone_except(E_Illegal_Op_Val());
                RETIRE_FAIL
            } else {
                let addr = cap_cursor(c) + EXTS(imm);
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
            }
        },
        (false, RawVal(v), CapVal(_)) => {
            /* store using a raw address */
            let addr = v + EXTS(imm);
            let (paddr, success) = capstone_store_mem_virt(addr, 16, rs2_v);
            assert(success);
            mem_overwrite(paddr, to_bits(xlen_val, 16));
            /* TODO: check paddr range */
            X(rs2) = reg_moved(rs2_v);

            RETIRE_SUCCESS
        },
        _ => {
            handle_capstone_except(E_Op_Type_Fault());
            RETIRE_FAIL
        }
    }
}

mapping clause assembly = CAPSTONE_INSN_S(rs2, rs1, imm7, imm5, CAPSTONE_STC)
  <-> "stc" ^ spc() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2) ^ sep() ^ hex_bits_12(imm7 @ imm5)
