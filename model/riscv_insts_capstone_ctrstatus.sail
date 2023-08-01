/* Control and status instructions */

mapping clause encdec = CAPSTONE_INSN_I(rs1, rd, imm, CAPSTONE_CCSRRW)   <-> imm @ rs1 @ 0b111 @ rd @ 0b1011011

function clause execute (CAPSTONE_INSN_I(rs1, rd, imm, CAPSTONE_CCSRRW)) = {
    let rs1_v : regtype = X(rs1);

    match rs1_v {
      CapVal(_) => {
        if not(ccsr_idx_matches(imm)) then {
          handle_capstone_except(E_Illegal_Op_Val());
          RETIRE_FAIL
        } else {
          let res = read_ccsr(imm);
          write_ccsr(imm, rs1_v);

          /* write result to rd */
          reg_overwrite(X(rd));
          X(rd) = res;
          
          RETIRE_SUCCESS
        }
      },
      _ => {
        handle_capstone_except(E_Op_Type_Fault());
        RETIRE_FAIL
      }
    }
}

mapping clause assembly = CAPSTONE_INSN_I(rs1, rd, imm, CAPSTONE_CCSRRW)
  <-> "ccsrrw" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ hex_bits_12(imm)

