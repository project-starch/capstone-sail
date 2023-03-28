#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV64U
RVTEST_CODE_BEGIN

.insn r 0x5B, 0x0, 0x0, x0, x1, x0
.insn r 0x5B, 0x0, 0x1, x0, x1, x0

RVTEST_PASS

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
