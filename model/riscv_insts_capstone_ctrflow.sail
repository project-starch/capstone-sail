/* Control-flow instructions */

mapping clause encdec = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_CALL)   <-> 0b0100000 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1011011

/* FIXME: all the below implementations need to be atomic with respect to exception handling */

function clause execute (CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_CALL)) = {
    /* PC address for resuming execution */    
    let cur_pc_cap = cap_set_cursor(PCCap, nextPC);

    let rd_v : regtype = X(rd);
    let rs1_v : regtype = X(rs1);
    let ra_v : regtype = x1;

    if not(capstone_in_secure_world()) then {
        handle_illegal();
        return RETIRE_FAIL;
    };

    match rs1_v {
      CapVal(c) => {
        let (nid, metadata) = decode_cap(c);
        if capnode_query(nid) == 0b0 then {
          handle_capstone_except(E_Invalid_Cap());
          RETIRE_FAIL
        } else
          match metadata {
            SealedCapMetadata(base_addr, async) if async == 0b00 => {
              /* Swap pc */
              let new_pc_cap_v = capstone_mem_xchg(base_addr, 0, CapVal(cur_pc_cap));
              capstone_redirect(new_pc_cap_v);

              /* Swap ceh */
              ceh = capstone_mem_xchg(base_addr, 1, ceh);

              /* Swap csp */
              x2 = capstone_mem_xchg(base_addr, 2, x2);

              X(rs1) = reg_moved(rs1_v);
              reg_overwrite(ra_v);
              let new_ra_cap_metadata = SealedRetCapMetadata(base_addr, base_addr, 0b00, rd) in
                x1 = CapVal(encode_cap((nid, new_ra_cap_metadata)));

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

mapping clause assembly = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_CALL)
  <-> "call" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)


/************************************************************/

mapping clause encdec = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_RETURN)   <-> 0b0100001 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_RETURN)) = {
    let cur_pc_cap = PCCap;
    let cur_npc = nextPC; /* PC address for resuming execution */
    let cur_sp = x2; /* current stack pointer */

    let rs1_v : regtype = X(rs1);
    let rs2_v : regtype = X(rs2);

    if not(capstone_in_secure_world()) then {
        handle_illegal();
        return RETIRE_FAIL;
    };

    match (rs1_v, rs2_v) {
      (CapVal(c), RawVal(v)) => {
        let (nid, metadata) = decode_cap(c);
        if capnode_query(nid) == 0b0 then {
          handle_capstone_except(E_Invalid_Cap());
          return RETIRE_FAIL;
        };

        match metadata {
          SealedRetCapMetadata(cursor, base_addr, async, ret_reg) => {
            match async {
              0b00 => {
                let new_sealed_pc_cap = cap_set_cursor(cur_pc_cap, v);
                /* Swap pc */
                let new_pc_cap_v = capstone_mem_xchg(base_addr, 0, CapVal(new_sealed_pc_cap));
                capstone_redirect(new_pc_cap_v);

                /* Swap ceh */
                ceh = capstone_mem_xchg(base_addr, 1, ceh);

                /* Swap csp */
                x2 = capstone_mem_xchg(base_addr, 2, x2);

                reg_overwrite(X(ret_reg));
                let new_sealed_cap = SealedCapMetadata(base_addr, 0b00) in
                  X(ret_reg) = CapVal(encode_cap((nid, new_sealed_cap)));
                
                RETIRE_SUCCESS
              },
              0b01 => {
                let new_sealed_pc_cap = cap_set_cursor(cur_pc_cap, v);
                /* Swap pc */
                let new_pc_cap_v = capstone_mem_xchg(base_addr, 0, CapVal(new_sealed_pc_cap));
                match new_pc_cap_v {
                  CapVal(new_pc_cap) => {
                    capstone_redirect_to_cap(new_pc_cap);
                  },
                  _ => {
                    handle_illegal();
                    return RETIRE_FAIL;
                  }
                };
                
                /* Store ceh */
                assert(capstone_store_mem(base_addr + to_bits(xlen_val, caplen_bytes_v), caplen_bytes_v, ceh));
                ceh = CapVal(encode_cap((nid, SealedCapMetadata(base_addr, 0b00))));
                X(rs1) = reg_moved(rs1_v);

                /* Swap other GPRs */
                reg_idx : int = 1;
                while reg_idx < 32 do {
                  X(to_bits(5, reg_idx)) = capstone_mem_xchg(base_addr, reg_idx + 1, X(to_bits(5, reg_idx)));
                  reg_idx = reg_idx + 1;
                };

                RETIRE_SUCCESS
              },
              0b10 => {
                let new_sealed_pc_cap = cap_set_cursor(cur_pc_cap, v);
                /* Swap pc */
                let new_pc_cap_v = capstone_mem_xchg(base_addr, 0, CapVal(new_sealed_pc_cap));
                match new_pc_cap_v {
                  CapVal(new_pc_cap) => {
                    capstone_redirect_to_cap(new_pc_cap);
                  },
                  _ => {
                    handle_illegal();
                    return RETIRE_FAIL;
                  }
                };
                  
                /* Swap ceh */
                ceh = capstone_mem_xchg(base_addr, 1, ceh);

                /* Set cih */
                cih = CapVal(encode_cap((nid, SealedCapMetadata(base_addr, 0b00))));
                X(rs1) = reg_moved(rs1_v);

                /* Swap other GPRs */
                reg_idx : int = 1;
                while reg_idx < 32 do {
                  X(to_bits(5, reg_idx)) = capstone_mem_xchg(base_addr, reg_idx + 1, X(to_bits(5, reg_idx)));
                  reg_idx = reg_idx + 1;
                };

                RETIRE_SUCCESS
              },
              _ => {
                assert(false);
                RETIRE_FAIL
              }
            }
          },
          _ => {
            handle_capstone_except(E_Cap_Type_Fault());
            RETIRE_FAIL
          }
        }
      },
      (RawVal(vv), RawVal(v)) if vv == EXTZ(0b0) => {
        let new_ceh_cap = cap_set_cursor(cur_pc_cap, v);
        capstone_redirect_to_cap(cepc);
        cepc = CAP_INVALID;

        RETIRE_SUCCESS
      },
      _ => {
        handle_capstone_except(E_Op_Type_Fault());
        RETIRE_FAIL
      }
    }
}

mapping clause assembly = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_RETURN)
  <-> "return" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/************************************************************/

mapping clause encdec = CAPSTONE_INSN_I(rs1, rd, imm, CAPSTONE_CJALR)   <-> imm @ rs1 @ 0b101 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN_I(rs1, rd, imm, CAPSTONE_CJALR)) = {
    let rd_v : regtype = X(rd);
    let rs1_v : regtype = X(rs1);

    if capstone_in_normal_world() then {
      handle_illegal();
      return RETIRE_FAIL;
    };

    match rs1_v {
        /* we don't check the permission or the type here. invalid values will trigger
        faults later */
        CapVal(c) => {
            let old_pc_cap = PCCap;
            let old_npc = nextPC;

            let new_cursor = cap_cursor(c) + EXTS(imm) : xlenbits;
            capstone_redirect_to_cap(cap_set_cursor(c, new_cursor));

            if rs1 != rd then {
              X(rs1) = reg_moved(rs1_v);
              reg_overwrite(rd_v);
            };
            X(rd) = CapVal(cap_set_cursor(old_pc_cap, old_npc)); /* save the original next PC */

            RETIRE_SUCCESS
        },
        _ => {
            handle_capstone_except(E_Op_Type_Fault());
            RETIRE_FAIL
        }
    }
}

mapping clause assembly = CAPSTONE_INSN_I(rs1, rd, imm, CAPSTONE_CJALR)
  <-> "cjalr" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ hex_bits_12(imm)


/************************************************************/

mapping clause encdec = CAPSTONE_INSN_I(rs1, rd, imm, CAPSTONE_CBNZ)   <-> imm @ rs1 @ 0b110 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN_I(rs1, rd, imm, CAPSTONE_CBNZ)) = {
    let rd_v : regtype = X(rd);
    let rs1_v : regtype = X(rs1);

    if capstone_in_normal_world() then {
      handle_illegal();
      return RETIRE_FAIL;
    };
    
    match(rd_v, rs1_v) {
        (CapVal(c), RawVal(v)) => {
            if(v != EXTZ(0b0)) then {
                reg_overwrite(CapVal(PCCap));
                X(rd) = reg_moved(rd_v);
                let new_cursor = cap_cursor(c) + EXTS(imm) : xlenbits;
                capstone_redirect_to_cap(cap_set_cursor(c, new_cursor));
            };
            RETIRE_SUCCESS
        },
        _ => {
            handle_capstone_except(E_Op_Type_Fault());
            RETIRE_FAIL
        }
    }
}

mapping clause assembly = CAPSTONE_INSN_I(rs1, rd, imm, CAPSTONE_CBNZ)
  <-> "cbnz" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ hex_bits_12(imm)

/************************************************************/

mapping clause encdec = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_CAPENTER)   <-> 0b0100010 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_CAPENTER)) = {
    let cur_npc = nextPC; /* PC address for resuming execution */
    let cur_sp = x2; /* current stack pointer */

    if capstone_in_secure_world() then {
      handle_illegal();
      return RETIRE_FAIL;
    };

    let rs1_v : regtype = X(rs1);

    match rs1_v {
      CapVal(c) => {
        let (nid, metadata) = decode_cap(c);
        if capnode_query(nid) == 0b0 then {
          handle_capstone_except(E_Invalid_Cap());
          return RETIRE_FAIL;
        };

        match metadata {
          SealedCapMetadata(base_addr, async) => {
            if async == 0b00 then {
              /* store the pc and sp values */
              normal_pc = cur_npc;
              normal_sp = cur_sp;

              /* load pc */
              let new_pc = capstone_mem_load(base_addr, 0);
              capstone_redirect(new_pc);

              /* load ceh */
              ceh = capstone_mem_load(base_addr, 1);

              /* load sp */
              x2 = capstone_mem_load(base_addr, 2);

              /* set ra */
              let new_ra_cp_metadata = ExitCapMetadata(base_addr, base_addr) in
                x1 = CapVal(encode_cap((nid, new_ra_cp_metadata)));

              /* set switch_reg and exit_reg */
              switch_reg = rs1;
              exit_reg = rd;

              capstone_enter_secure_world();

              RETIRE_SUCCESS
            } else if async == 0b01 | async == 0b10 then {
              /* store the pc and sp values */
              normal_pc = cur_npc;
              normal_sp = cur_sp;

              /* load pc */
              let new_pc = capstone_mem_load(base_addr, 0);
              capstone_redirect(new_pc);

              /* load ceh */
              ceh = capstone_mem_load(base_addr, 1);

              /* load other GPRs */
              reg_idx : int = 1;
              while reg_idx < 32 do {
                X(to_bits(5, reg_idx)) = capstone_mem_load(base_addr, reg_idx + 1);
                reg_idx = reg_idx + 1;
              };

              /* set switch_cap */
              let new_switch_cap_metadata = UninitialisedCapMetadata(base_addr, base_addr, base_addr + to_bits(xlen_val, 33 * caplen_bytes_v), CAP_PERM_RW) in
                switch_cap = encode_cap((nid, new_switch_cap_metadata));
              X(rs1) = RawVal(EXTZ(0b0));

              /* set switch_reg and exit_reg */
              switch_reg = rs1;
              exit_reg = rd;

              capstone_enter_secure_world();

              RETIRE_SUCCESS
            } else {
              assert(false);
              RETIRE_FAIL
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

mapping clause assembly = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_CAPENTER)
  <-> "capenter" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)


/************************************************************/

/* capexit does the following
  1. recover the PC and stack top from the special registers
  2. (optional) seal the current context
  3. switch the CPU mode to the normal world

  Note that the capexit instruction does not restore the full context.
*/

mapping clause encdec = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_CAPEXIT)   <-> 0b0100011 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_CAPEXIT)) = {
    let cur_pc_cap = PCCap;
    let cur_npc = nextPC; /* PC address for resuming execution */    
    let cur_sp = x2; /* current stack pointer */

    if capstone_in_normal_world() then {
      handle_illegal();
      return RETIRE_FAIL;
    };

    let rs1_v : regtype = X(rs1);
    let rs2_v : regtype = X(rs2);

    match (rs1_v, rs2_v) {
      (CapVal(c), RawVal(v)) => {
        let (nid, metadata) = decode_cap(c);
        if capnode_query(nid) == 0b0 then {
          handle_capstone_except(E_Invalid_Cap());
          return RETIRE_FAIL;
        };

        match metadata {
          ExitCapMetadata(cursor, base_addr) => {
            /* store pc with modified cursor */
            let new_sealed_pc_cap = cap_set_cursor(cur_pc_cap, v) in
              assert(capstone_mem_store(base_addr, 0, CapVal(new_sealed_pc_cap)));

            /* store ceh */ 
            assert(capstone_mem_store(base_addr, 1, ceh));

            /* store sp */
            assert(capstone_mem_store(base_addr, 2, cur_sp));

            /* load new pc and sp */
            capstone_redirect_to_addr(normal_pc);
            x2 = normal_sp;

            /* write back to switch_reg */
            let new_sealed_cap_metadata = SealedCapMetadata(base_addr, 0b00) in
              X(switch_reg) = CapVal(encode_cap((nid, new_sealed_cap_metadata)));
              
            /* write exit code */
            X(exit_reg) = RawVal(EXTZ(0b0));

            capstone_enter_normal_world();

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

mapping clause assembly = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_CAPEXIT)
  <-> "capexit" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)
