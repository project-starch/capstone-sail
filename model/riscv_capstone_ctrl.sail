/* Control and status related definitions for Capstone */

/* Extended CSRs */

register cis : bits(16)
register ctval : xlenbits
register ccause : xlenbits
register emode : bit


/* CCSRs */

register ceh : regtype
register cih : regtype
register cinit : cap_t
register cepc : cap_t
register switch_cap : cap_t

/* registers for normal world PC and stack pointer */
register normal_pc : xlenbits
register normal_sp  : regtype
register switch_reg : bits(5)
register exit_reg : bits(5)
