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
    cs.stw ca4, t0
    cs.cincoffsetimm ca5, ca4, 4
    cs.stw ca5, x0
    j _exit_loop