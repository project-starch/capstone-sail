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
    call main

.global main
main:
