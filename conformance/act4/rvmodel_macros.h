// ACT4's model interface for leanVM. The machine has no CSRs, no traps, no console
// and no tohost: a test ends in the one ecall it knows, exit (a7 = 93), with the
// output a0..a3. A pass is all zeros. A failure that reaches the model's halt is
// a0 = 1 and a1 = the return address of the call to it, which names the check.
// STANDARD_SM_SUPPORTED stays undefined, so ACT4 emits no CSR code.
// SPDX-License-Identifier: BSD-3-Clause

#ifndef _RVMODEL_MACROS_H
#define _RVMODEL_MACROS_H

// Only Sail's build has a tohost, which sail_macros.h defines.
#define RVMODEL_DATA_SECTION

// Nothing traps, so the trap signature region, 15000 entries by default, holds nothing.
#define TRAP_SIGUPD_COUNT 0

#define RVMODEL_HALT_EXIT \
  li a2, 0                ;\
  li a3, 0                ;\
  li a7, 93               ;\
  ecall                   ;

#define RVMODEL_HALT_PASS \
  li a0, 0                ;\
  li a1, 0                ;\
  RVMODEL_HALT_EXIT

#define RVMODEL_HALT_FAIL \
  li a0, 1                ;\
  mv a1, ra               ;\
  RVMODEL_HALT_EXIT

#define RVMODEL_IO_WRITE_STR(_R1, _R2, _R3, _STR_PTR)

// Required by check_defines.h, expanded only with STANDARD_SM_SUPPORTED.
#define RVMODEL_INTERRUPT_LATENCY 10
#define RVMODEL_TIMER_INT_SOON_DELAY 100
#define RVMODEL_SET_MEXT_INT(_R1, _R2)
#define RVMODEL_CLR_MEXT_INT(_R1, _R2)
#define RVMODEL_SET_MSW_INT(_R1, _R2)
#define RVMODEL_CLR_MSW_INT(_R1, _R2)
#define RVMODEL_SET_SEXT_INT(_R1, _R2)
#define RVMODEL_CLR_SEXT_INT(_R1, _R2)
#define RVMODEL_SET_SSW_INT(_R1, _R2)
#define RVMODEL_CLR_SSW_INT(_R1, _R2)

#endif // _RVMODEL_MACROS_H
