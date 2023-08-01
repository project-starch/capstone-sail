/* Interrupt/exception handling */

/* Platform-specific handling of instruction faults */

function handle_illegal() -> unit = {
    if capstone_in_secure_world() then {
        capstone_except_transfer(EXTZ(exceptionType_to_bits(E_Illegal_Instr())),
                                 EXTZ(0b1));
    } else {
        let info = if plat_mtval_has_illegal_inst_bits ()
                    then Some(instbits)
                    else None();
        let t : sync_exception = struct { trap    = E_Illegal_Instr(),
                                        excinfo = info,
                                        ext     = None() };
        set_next_pc(exception_handler(cur_privilege, CTL_TRAP(t), PC));
    }
}

function handle_capstone_except(e: ExceptionType) -> unit = {
    if capstone_in_secure_world() then {
        /* perform secure-world-specific control flow transfer */
        capstone_except_transfer(EXTZ(exceptionType_to_bits(e)), EXTZ(0b1));

        /* now we might be in secure world or normal world */
    } else {
        let t : sync_exception = struct { trap    = e,
                                        excinfo = None(),
                                        ext     = None() };
        set_next_pc(exception_handler(cur_privilege, CTL_TRAP(t), PC));
    }
}

