/* Control and status instructions */

mapping clause encdec = CAPSTONE_INSN_I(rs1, rd, imm, CAPSTONE_CCSRRW)   <-> imm @ rs1 @ 0b111 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN_I(rs1, rd, imm, CAPSTONE_CCSRRW)) = {
    /* TODO: implement */
    RETIRE_SUCCESS
}

mapping clause assembly = CAPSTONE_INSN_I(rs1, rd, imm, CAPSTONE_CCSRRW)
  <-> "ccsrrw" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ hex_bits_12(imm)

