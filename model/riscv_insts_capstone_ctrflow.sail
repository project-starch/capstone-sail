/* Control-flow instructions */

mapping clause encdec = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_CALL)   <-> 0b0100000 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_CALL)) = {
    let cur_pc_cap = PCCap;
    let cur_npc = nextPC; /* PC address for resuming execution */    
    let cur_sp = x2; /* current stack pointer */

    let rs1_v : regtype = X(rs1);

    match (rs1_v, capstone_in_secure_world()) {
        (CapVal(c), true) if capstone_cap_is_valid(c) => {
            let (ty, node_id, metadata) = decode_cap(c);
            match metadata {
                SealedCapMetadata(base_addr, size) => {
                    /* load the context */
                    capstone_redirect(capstone_load_mem(base_addr, caplen_bytes_v));
                    capstone_load_mem_n(base_addr, 1, unsigned(size));
                    
                    /* store old PC and SP */
                    assert(capstone_store_mem(base_addr, caplen_bytes_v, CapVal(cap_set_cursor(cur_pc_cap, cur_npc))));
                    assert(capstone_store_mem(base_addr + caplen_bytes_v, caplen_bytes_v, cur_sp));

                    /* generate cra */
                    x1 = CapVal(encode_cap((CAP_TYPE_SEALEDRET, node_id, SealedRetCapMetadata(base_addr, size, rs1))));

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

    match (rs1_v, rs2_v, capstone_in_secure_world()) {
        (CapVal(c), RawVal(v), true) if capstone_cap_is_valid(c) => {
            let (ty, node_id, metadata) = decode_cap(c);
            match metadata {
                SealedRetCapMetadata(base_addr, size, reg) => {
                    capstone_redirect(capstone_load_mem(base_addr, caplen_bytes_v));

                    if unsigned(reg) == 0 then {
                        /* asynchronous scenario */
                        /* need to load full context */
                        /* store size GPR values */

                        capstone_swap_mem_n(base_addr, 1, unsigned(size));
                        capstone_load_mem_n(base_addr, unsigned(size) + 1, 31 - unsigned(size));

                    } else {
                        /* synchronous scenario */
                        /* just load SP */
                        /* store size GPR values */
                        let new_sp = capstone_load_mem(base_addr + caplen_bytes_v, caplen_bytes_v);
                        capstone_store_mem_n(base_addr, 1, unsigned(size));
                        x2 = new_sp;
                    };

                    /* store the old PC */
                    assert(capstone_store_mem(base_addr + caplen_bytes_v, caplen_bytes_v, CapVal(cap_set_cursor(cur_pc_cap, cur_npc))));

                    /* generate cra */
                    x1 = CapVal(encode_cap((CAP_TYPE_SEALED, node_id, SealedCapMetadata(base_addr, size))));

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

mapping clause assembly = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_RETURN)
  <-> "return" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/************************************************************/

mapping clause encdec = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_JMP)   <-> 0b0100010 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_JMP)) = {
    let rs1_v : regtype = X(rs1);
    
    match(rs1_v) {
        /* we don't check the permission or the type here. invalid values will trigger
        faults later */
        CapVal(c) => {
            reg_overwrite(CapVal(PCCap));
            X(rs1) = reg_moved(rs1_v);
            capstone_redirect_to_cap(c);
            RETIRE_SUCCESS
        },
        _ => {
            handle_illegal();
            RETIRE_FAIL
        }
    }
}

mapping clause assembly = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_JMP)
  <-> "jmp" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)


/************************************************************/

mapping clause encdec = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_JNZ)   <-> 0b0100011 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_JNZ)) = {
    let rs1_v : regtype = X(rs1);
    let rs2_v : regtype = X(rs2);
    
    match((rs1_v, rs2_v)) {
        (CapVal(c), RawVal(v)) => {
            if(v != EXTZ(0b0)) then {
                reg_overwrite(CapVal(PCCap));
                X(rs1) = reg_moved(rs1_v);
                capstone_redirect_to_cap(c);
            };
            RETIRE_SUCCESS
        },
        _ => {
            handle_illegal();
            RETIRE_FAIL
        }
    }
}

mapping clause assembly = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_JNZ)
  <-> "jnz" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

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

mapping clause encdec = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_CAPENTER)   <-> 0b0100100 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_CAPENTER)) = {
    let cur_npc = nextPC; /* PC address for resuming execution */
    let cur_sp = x2; /* current stack pointer */

    let rs1_v : regtype = X(rs1);

    match (rs1_v, capstone_in_normal_world()) {
        (CapVal(c), true) if capstone_cap_is_valid(c) => {
            /* store the PC and stack pointer in special registers */

            let (ty, _, metadata) = decode_cap(c);

            match(metadata) {
                SealedCapMetadata(base_addr, size) => {
                    capstone_redirect(capstone_load_mem(base_addr, caplen_bytes_v));
                    capstone_load_mem_n(base_addr, 1, unsigned(size));
                    normal_npc = cur_npc;
                    normal_sp = cur_sp;
                    switch_buffer_cap = c;
                    switch_reg = rs1;
                    x1 = CapVal(cap_build_exit());

                    /* set the CPU mode to secure world */
                    capstone_enter_secure_world();
                    
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

mapping clause assembly = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_CAPENTER)
  <-> "capenter" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)


/************************************************************/

/* capexit does the following
  1. recover the PC and stack top from the special registers
  2. (optional) seal the current context
  3. switch the CPU mode to the normal world

  Note that the capexit instruction does not restore the full context.
*/

mapping clause encdec = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_CAPEXIT)   <-> 0b0100101 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_CAPEXIT)) = {
    let cur_pc_cap = PCCap;
    let cur_npc = nextPC; /* PC address for resuming execution */    
    let cur_sp = x2; /* current stack pointer */

    let rs1_v : regtype = X(rs1);
    let rs2_v : regtype = X(rs2);

    match(rs1_v, rs2_v, capstone_in_secure_world()) {
        /* TODO: we are not checking the validity of exit capability here for now */
        (CapVal(c), RawVal(v), true) if capstone_cap_is_valid(c) => {
            let (_, _, metadata) = decode_cap(switch_buffer_cap);
            match(cap_type(c), metadata) {
                (CAP_TYPE_EXIT, SealedCapMetadata(base_addr, size)) => {
                    /* load PC and SP */
                    capstone_redirect_to_addr(normal_npc);
                    
                    assert(capstone_store_mem(base_addr, caplen_bytes_v, CapVal(cap_set_cursor(cur_pc_cap, v))));
                    capstone_store_mem_n(base_addr, 1, unsigned(size));

                    x2 = normal_sp;
                    X(switch_reg) = CapVal(switch_buffer_cap);

                    /* set the CPU mode to normal world */
                    capstone_enter_normal_world();

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

mapping clause assembly = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_CAPEXIT)
  <-> "capexit" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)
