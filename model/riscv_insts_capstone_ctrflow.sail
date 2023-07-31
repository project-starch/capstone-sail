/* Control-flow instructions */

mapping clause encdec = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_CALL)   <-> 0b0100000 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_CALL)) = {
    let cur_pc_cap = PCCap;
    let cur_npc = nextPC; /* PC address for resuming execution */    
    let cur_sp = x2; /* current stack pointer */

    /* TODO: implement new semantics */

    RETIRE_SUCCESS
}

mapping clause assembly = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_CALL)
  <-> "call" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)


/************************************************************/

mapping clause encdec = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_RETURN)   <-> 0b0100001 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_RETURN)) = {
    let cur_pc_cap = PCCap;
    let cur_npc = nextPC; /* PC address for resuming execution */
    let cur_sp = x2; /* current stack pointer */

    
    /* TODO: implement new semantics */

    RETIRE_SUCCESS
}

mapping clause assembly = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_RETURN)
  <-> "return" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/************************************************************/

mapping clause encdec = CAPSTONE_INSN_I(rs1, rd, imm, CAPSTONE_CJALR)   <-> imm @ rs1 @ 0b101 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN_I(rs1, rd, imm, CAPSTONE_CJALR)) = {
    let rd_v : regtype = X(rd);
    let rs1_v : regtype = X(rs1);

    match(rs1_v, capstone_in_secure_world()) {
        /* we don't check the permission or the type here. invalid values will trigger
        faults later */
        (CapVal(c), true) => {
            let old_pc_cap = PCCap;
            let old_npc = nextPC;

            reg_overwrite(rd_v);
            X(rs1) = reg_moved(rs1_v);
            capstone_redirect_to_cap(c);
            X(rd) = CapVal(cap_set_cursor(old_pc_cap, old_npc)); /* save the original next PC */

            RETIRE_SUCCESS
        },
        _ => {
            handle_illegal();
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
    
    match((rd_v, rs1_v, capstone_in_secure_world())) {
        (CapVal(c), RawVal(v), true) => {
            if(v != EXTZ(0b0)) then {
                reg_overwrite(CapVal(PCCap));
                X(rd) = reg_moved(rd_v);
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

mapping clause assembly = CAPSTONE_INSN_I(rs1, rd, imm, CAPSTONE_CBNZ)
  <-> "cbnz" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ hex_bits_12(imm)

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

mapping clause encdec = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_CAPENTER)   <-> 0b0100010 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_CAPENTER)) = {
    let cur_npc = nextPC; /* PC address for resuming execution */
    let cur_sp = x2; /* current stack pointer */

    /* TODO: implement new semantics */
    RETIRE_SUCCESS
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

    let rs1_v : regtype = X(rs1);
    let rs2_v : regtype = X(rs2);

    /* TODO: implement new semantics */
    RETIRE_SUCCESS
}

mapping clause assembly = CAPSTONE_INSN_R(rs2, rs1, rd, CAPSTONE_CAPEXIT)
  <-> "capexit" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)
