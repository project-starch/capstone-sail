_exit_begin:

.section .text
exit:
    cs.capcreate ca4
    la a0, tohost
    la a1, tohost + 8
    cs.capbound ca4, a0, a1
    li a1, -1
    cs.alloc a0, a1
    cs.capnode ca4, a0
    li a0, 1
    cs.captype ca4, a0
    li a0, 4
    cs.capperm ca4, a0

_exit_loop:
    li a7, 9
    li a0, 0
    li t0, 1
    csw t0, 0(ca4)
    cs.cincoffsetimm ca5, ca4, 4
    csw x0, 0(ca5)
    j _exit_loop

_exit_end:
