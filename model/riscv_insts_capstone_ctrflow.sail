/* Control-flow instructions */

mapping clause encdec = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_CALL)   <-> 0b0100000 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_CALL)) = capstone_call(rd, rs1, rs2, CAPSTONE_CALL_NORMAL)

mapping clause assembly = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_CALL)
  <-> "call" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)


/************************************************************/

mapping clause encdec = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_RETURN)   <-> 0b0100001 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_RETURN)) = capstone_call(rd, rs1, rs2, CAPSTONE_CALL_RETURN)

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
            redirect_to_cap(c);
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

    if not(capstone_in_normal_world()) | capstone_call(rs1, EXTZ(0b0), EXTZ(0b0), CAPSTONE_CALL_CAPENTER) != RETIRE_SUCCESS
    then {
        handle_illegal();
        RETIRE_FAIL
    } else {
        /* store the PC and stack pointer in special registers */
        normal_npc = cur_npc;
        normal_sp = cur_sp;
        /* set the CPU mode to secure world */
        capstone_enter_secure_world();

        RETIRE_SUCCESS
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
    if not(capstone_in_secure_world()) | capstone_call(rd, rs1, rs2, CAPSTONE_CALL_CAPEXIT) != RETIRE_SUCCESS then {
        handle_illegal();
        RETIRE_FAIL
    } else {
        /* recover the PC and stack pointer from the special registers */
        nextPC = normal_npc;
        let x2_v : regtype = x2;
        x2 = normal_sp;
        reg_overwrite(x2_v); /* the original value in x2 is overwritten */
        /* set the CPU mode to normal world */
        capstone_enter_normal_world();

        RETIRE_SUCCESS
    }
}

mapping clause assembly = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_CAPEXIT)
  <-> "capexit" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/************************************************************/

/* TODO: capexitseal is similar to capexit, but seals the */

mapping clause encdec = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_CAPEXITSEAL)   <-> 0b0100110 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_CAPEXITSEAL)) = {
    if not(capstone_in_secure_world()) | capstone_call(rd, rs1, rs2, CAPSTONE_CALL_CAPEXITSEAL) != RETIRE_SUCCESS then {
        handle_illegal();
        RETIRE_FAIL
    } else {
        /* recover the PC and stack pointer from the special registers */
        nextPC = normal_npc;
        let x2_v : regtype = x2;
        x2 = normal_sp;
        reg_overwrite(x2_v); /* the original value in x2 is overwritten */
        /* set the CPU mode to normal world */
        capstone_enter_normal_world();

        RETIRE_SUCCESS
    }
}