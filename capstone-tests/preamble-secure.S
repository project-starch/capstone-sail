#include "asm_insn.h"

#define EXTRA_DATA

#define RVTEST_DATA_BEGIN                                               \
        EXTRA_DATA                                                      \
        .pushsection .tohost,"aw",@progbits;                            \
        .align 6; .global tohost; tohost: .dword 0; .size tohost, 8;    \
        .align 6; .global fromhost; fromhost: .dword 0; .size fromhost, 8;\
        .popsection;                                                    \
        .align 4; .global begin_signature; begin_signature:

#define RVTEST_DATA_END .align 4; .global end_signature; end_signature:

#define INIT_CAP(reg, type, perm) \
    li t1, -1; \
    cs.alloc t0, t1; \
    cs.capnode reg, t0; \
    li t0, type; \
    cs.captype reg, t0; \
    li t0, perm; \
    cs.capperm reg, t0;

#define CREATE_CAP(reg, base, top, type, perm) \
    cs.capcreate reg; \
    la t0, base; \
    la t1, top; \
    cs.capbound reg, t0, t1; \
    INIT_CAP(reg, type, perm)

RVTEST_DATA_BEGIN

RVTEST_DATA_END


.section .text
.weak _CHERI_CAPABILITY_TABLE_
_CHERI_CAPABILITY_TABLE_:
.global _start
_start:
    # disable world paritioning
    cs.onpartition x0 

    li a0, 1
    csrw emode, a0 # switch to cap addressing mode

    cs.capcreate ca3
    li a1, CAP_TYPE_LIN
    cs.captype ca3, a1

    li a1, NODE_ID_INVALID
    cs.alloc a2, a1
    cs.capnode ca3, a2

    li a1, CAP_PERM_RW
    cs.capperm ca3, a1

    SETSECUREMEM(ca3, a3, 0, SEAL_SIZE, 0, 0)
    cs.capcreate ca4
    li a1, CAP_TYPE_LIN
    cs.captype ca4, a1
    
    li a1, NODE_ID_INVALID
    cs.alloc a2, a1
    cs.capnode ca4, a2

    li a1, CAP_PERM_RX
    cs.capperm ca4, a1

    la a1, _secure_begin
    la a2, _secure_end
    cs.capbound ca4, a1, a2

    la a1, main
    cs.scc ca4, ca4, a1

    cs.stc 0(ca3), ca4
    cs.seal ca3, ca3

    cs.capenter x0, ca3

    j _exit


.align REG_SIZE_LOG2
_secure_begin:

.global main
main:
