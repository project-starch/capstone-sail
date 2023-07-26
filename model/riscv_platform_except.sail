/* Interrupt/exception handling */

function handle_illegal_in_normal() -> unit = {
    assert(capstone_in_normal_world());

    let info = if plat_mtval_has_illegal_inst_bits ()
                then Some(instbits)
                else None();
    let t : sync_exception = struct { trap    = E_Illegal_Instr(),
                                    excinfo = info,
                                    ext     = None() };
    set_next_pc(exception_handler(cur_privilege, CTL_TRAP(t), PC)) // FIXME: add checks on PC
}

function handle_illegal_in_secure() -> unit = {
    assert(capstone_in_secure_world());

    /* In secure world, we check whether we want to get the normal world involved or not */
    /* It is helpful for testing purposes to disable normal world handling */
    let success = 
        if normalWorldHandling then {
            /* If we want to involve the normal world */
            /* need to set up so when the normal world next CAPENTERs */
            /* the exception handler domain will take over */
            let (switch_cap_node_id, switch_cap_metadata) = decode_cap(switch_buffer_cap);
            let valid_ceh : bool = match (ceh, switch_cap_metadata) {
                (CapVal(c), SealedCapMetadata(switch_cap_base, switch_cap_size))
                        if capstone_cap_is_valid(c) & capstone_cap_is_valid(switch_buffer_cap) => {
                    let (_, ceh_metadata) = decode_cap(c);

                    match ceh_metadata {
                        SealedCapMetadata(ceh_base_addr, ceh_size) => {
                            let cur_pc_cap = PCCap;
                            let epc = PC;

                            assert(capstone_store_mem(switch_cap_base, caplen_bytes_v, CapVal(cap_set_cursor(cur_pc_cap, epc))));
                            capstone_store_mem_n(switch_cap_base, 1, 31);

                            let new_switch_cap = encode_cap((switch_cap_node_id,
                                SealedRetCapMetadata(EXTZ(0b0) : xlenbits, switch_cap_base, EXTZ(0b0) : bits(2), EXTZ(0b0) : bits(5)))); /* for asynchronous */
                            
                            /* FIXME: this could be overwritten when CAPENTER */
                            assert(capstone_store_mem(ceh_base_addr + to_bits(xlen_val, caplen_bytes_v), caplen_bytes_v, CapVal(new_switch_cap)));

                            capstone_scrub_reg_n(1, 31); /* scrub all GPRs */
                            X(switch_reg) = ceh;

                            true
                        },
                        _ => false
                    }
                },
                _ => false /* invalid capability in ceh */
            };

            if not(valid_ceh) then {
                /* If there's no valid secure-world exception handler */
                /* we simply mess up secure world */
                /* but we need to get out to the normal world */
                /* still, we want confidentiality */
                capstone_scrub_reg_n(1, 31); /* scrub all GPRs */
            };

            capstone_redirect_to_addr(normal_npc);
            x2 = normal_sp;

            PC = normal_npc - EXTZ(0x4); /* exception handling in normal world uses PC */

            capstone_enter_normal_world();
            handle_illegal_in_normal();

            true
        } else {
            /* If we don't want to involve the normal world */
            /* follow the pure Capstone exception handling semantics */
            match ceh {
                CapVal(c) if capstone_cap_is_valid(c) => {
                    let (node_id, metadata) = decode_cap(c);

                    match metadata {
                        SealedCapMetadata(base_addr, size) => {
                            let cur_pc_cap = PCCap;
                            let epc = PC;

                            capstone_redirect(capstone_load_mem(base_addr, caplen_bytes_v));
                            capstone_swap_mem_n(base_addr, 1, unsigned(size));
                            capstone_store_mem_n(base_addr, unsigned(size) + 1, 31 - unsigned(size));
                            capstone_scrub_reg_n(unsigned(size) + 1, 31 - unsigned(size));

                            /* store PC */
                            assert(capstone_store_mem(base_addr, caplen_bytes_v, CapVal(cap_set_cursor(cur_pc_cap, epc))));

                            /* generate cra */
                            x1 = CapVal(encode_cap((node_id, SealedRetCapMetadata(base_addr, EXTZ(0b0), EXTZ(0b0), EXTZ(0b0)))));

                            true
                        },
                        _ => false
                    }
                },
                _ => false /* invalid capability in ceh */
            }
        };
    if not(success) then {
        /* cannot handle the exception, panic */
        print("Panic: Capstone exception handler failed to handle the exception\n");
        exit()
    }
}

/* Platform-specific handling of instruction faults */

function handle_illegal() -> unit = {
    if capstone_in_normal_world() then
        handle_illegal_in_normal()
    else
        handle_illegal_in_secure()
}
