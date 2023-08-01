/* Memory access instructions */

mapping clause encdec = CAPSTONE_INSN_I(rs1, rd, imm, CAPSTONE_LDC) <-> imm @ rs1 @ 0b011 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN_I(rs1, rd, imm, CAPSTONE_LDC)) = {
    let rs1_v : regtype = X(rs1);
    let rd_v : regtype = X(rd);

    let use_cap = capstone_in_secure_world() | emode == bitone;

    match(use_cap, rs1_v) {
        (true, CapVal(c)) if cap_access_allowed_offset(c, 16, CAP_PERM_RO, EXTZ(imm)) &
            capnode_query(cap_nodeid(c)) == 0b1 => {
            /* load using a capability */
            /* load data and tag */
            let addr = cap_cursor(c) + EXTS(imm) : xlenbits; 
            let v = capstone_load_mem(addr, 16);
            reg_overwrite(rd_v);
            X(rd) = v;
            assert(mem_moved(addr, v)); /* the value is moved from the original location */
            RETIRE_SUCCESS
        },
        (false, RawVal(v)) => {
            /* load using raw address */
            let addr = v + EXTS(imm) : xlenbits;
            let (paddr, v) = capstone_load_mem_virt(addr, 16);
            reg_overwrite(rd_v);
            X(rd) = v;
            assert(mem_moved(paddr, v)); /* the value is moved from the original location */
            RETIRE_SUCCESS
        },
        _ => {
            handle_illegal();
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

    match(use_cap, rs1_v) {
        (true, CapVal(c)) if cap_access_allowed_offset(c, 16, CAP_PERM_RW, EXTS(imm))
                & capnode_query(cap_nodeid(c)) == 0b1 => {
            /* store using a capability */
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
        },
        (false, RawVal(v)) => {
            /* store using a raw address */
            let addr = v + EXTS(imm);
            let (paddr, success) = capstone_store_mem_virt(addr, 16, rs2_v);
            assert(success);
            mem_overwrite(paddr, to_bits(xlen_val, 16));
            X(rs2) = reg_moved(rs2_v);
            RETIRE_SUCCESS
        },
        _ => {
            handle_illegal();
            RETIRE_FAIL
        }
    }
}

mapping clause assembly = CAPSTONE_INSN_S(rs2, rs1, imm7, imm5, CAPSTONE_STC)
  <-> "stc" ^ spc() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2) ^ sep() ^ hex_bits_12(imm7 @ imm5)
