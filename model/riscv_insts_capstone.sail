union clause ast = CAPSTONE_INSN : (regidx, regidx, regidx, capstone_op)

mapping clause encdec = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_QUERY)   <-> 0b0000000 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_QUERY)) = {
    print("good execution capstone instruction query");
    RETIRE_SUCCESS;
}

mapping clause assembly = CAPSTONE_INSN(rs1, rs2, rd, CAPSTONE_QUERY)
  <-> "query" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

mapping clause encdec = CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_DROP)   <-> 0b0000001 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN(rs2, rs1, rd, CAPSTONE_DROP)) = {
    print("good execution capstone instruction drop");
    RETIRE_SUCCESS;
}

mapping clause assembly = CAPSTONE_INSN(rs1, rs2, rd, CAPSTONE_DROP)
  <-> "drop" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)