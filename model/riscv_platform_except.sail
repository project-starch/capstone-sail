/* Interrupt/exception handling */

/* Platform-specific handling of instruction faults */

function handle_illegal() -> unit = {
    /* Can only happen in normal world */
    assert(capstone_in_normal_world());

    let info = if plat_mtval_has_illegal_inst_bits ()
                then Some(instbits)
                else None();
    let t : sync_exception = struct { trap    = E_Illegal_Instr(),
                                    excinfo = info,
                                    ext     = None() };
    set_next_pc(exception_handler(cur_privilege, CTL_TRAP(t), PC)) // FIXME: add checks on PC
}

function handle_capstone_except(e: ExceptionType) -> unit = {
    ()
}

