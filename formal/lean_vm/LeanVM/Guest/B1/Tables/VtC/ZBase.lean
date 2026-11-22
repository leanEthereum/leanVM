/-
  LeanVM.Guest.B1.Tables.VtC.ZBase

  The table sumcheck's honest rounds (from the transcript words, the capacity and the target), the
  buffers they fill, and `verify_tables`' statements `g_zc_n ..< x@9` and `nxt[0]@42 ..< ret`.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.Hon
public import LeanVM.Guest.B1.Tables.VtC.ZLoop10
public import LeanVM.Guest.B1.Tables.Vt.ZcRun
public import LeanVM.Guest.B1.Tables.Vt.Pi
public import LeanVM.Guest.Data.NameStrings
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_tables»

/-!
# The table sumcheck, honestly

`zcRec cap0 cl0 xs j`: the capacity and the claim before round `j` of the plain degree-4
sumcheck from the capacity `cap0` and the claim `cl0`, round `j` reading the words
`xs[3j], xs[3j+1], xs[3j+2]` (`c0, c2, c3`); `zcCh`: round `j`'s challenge. The buffers:
`zcRoundsW` (record `j ≤ n`: the capacity, the cursor `cur0·g^(3j)`, the claim), `zcCprodW`
(the challenges' running products), `zcRkW` (the challenges, as `zc_rk` holds them), `zcChis` (the
challenges, last first, as `chi` holds them).

`zc_run`: the rounds are the specification's `sumcheck cl0 4 (replicate n none)`.
`zc_l10B`: on a memory holding the buffers and the words, every iteration of `verify_tables_loop0`
has its facts; `zc_chiRev`: `chi` is `zc_rk` reversed, as `eq_prefix_chain_rev` writes it.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

/-! ## The statements -/

/-- `verify_tables`' statements `g_zc_n ..< x@9` (G:2565-2619). -/
noncomputable def zBlk : List Stmt := [
    .atom (.hint (.witness "zc_tau_max" (.stack [.n (val% «verify_tables» "g_zc_n")]))),
    .atom (.const (.n (val% «verify_tables» "s56.u0.s1#0")) (word 4294967296 0)),
    .atom (.mul (.n (val% «verify_tables» "g_zc_n")) (.n (val% «verify_tables» "s56.u0.s1#1")) (.n (val% «verify_tables» "kb[2]"))),
    .atom (.rangeCheck (.n (val% «verify_tables» "s56.u0.s1#1")) (.n (val% «verify_tables» "s56.u0.s1#2")) (.n (val% «verify_tables» "s56.u0.s1#3")) (.n (val% «verify_tables» "s56.u0.s1#4")) (.n (val% «verify_tables» "s56.u0.s1#0"))),
    .atom (.add (.n (val% «verify_tables» "zc_is_a_tau@1")) (.n (val% «verify_tables» "g_zc_n")) (.n (val% «verify_tables» "kb[2]"))),
    .atom (.const (.n (val% «verify_tables» "s56.u1.s1#0")) (word 4294967296 0)),
    .atom (.mul (.n (val% «verify_tables» "g_zc_n")) (.n (val% «verify_tables» "s56.u1.s1#1")) (.n (val% «verify_tables» "kb[3]"))),
    .atom (.rangeCheck (.n (val% «verify_tables» "s56.u1.s1#1")) (.n (val% «verify_tables» "s56.u1.s1#2")) (.n (val% «verify_tables» "s56.u1.s1#3")) (.n (val% «verify_tables» "s56.u1.s1#4")) (.n (val% «verify_tables» "s56.u1.s1#0"))),
    .atom (.add (.n (val% «verify_tables» "zc_is_a_tau@2~0")) (.n (val% «verify_tables» "g_zc_n")) (.n (val% «verify_tables» "kb[3]"))),
    .atom (.mul (.n (val% «verify_tables» "zc_is_a_tau@2")) (.n (val% «verify_tables» "zc_is_a_tau@1")) (.n (val% «verify_tables» "zc_is_a_tau@2~0"))),
    .atom (.const (.n (val% «verify_tables» "s56.u2.s1#0")) (word 4294967296 0)),
    .atom (.mul (.n (val% «verify_tables» "g_zc_n")) (.n (val% «verify_tables» "s56.u2.s1#1")) (.n (val% «verify_tables» "kb[4]"))),
    .atom (.rangeCheck (.n (val% «verify_tables» "s56.u2.s1#1")) (.n (val% «verify_tables» "s56.u2.s1#2")) (.n (val% «verify_tables» "s56.u2.s1#3")) (.n (val% «verify_tables» "s56.u2.s1#4")) (.n (val% «verify_tables» "s56.u2.s1#0"))),
    .atom (.add (.n (val% «verify_tables» "zc_is_a_tau@3~0")) (.n (val% «verify_tables» "g_zc_n")) (.n (val% «verify_tables» "kb[4]"))),
    .atom (.mul (.n (val% «verify_tables» "zc_is_a_tau@3")) (.n (val% «verify_tables» "zc_is_a_tau@2")) (.n (val% «verify_tables» "zc_is_a_tau@3~0"))),
    .atom (.const (.n (val% «verify_tables» "s56.u3.s1#0")) (word 4294967296 0)),
    .atom (.mul (.n (val% «verify_tables» "g_zc_n")) (.n (val% «verify_tables» "s56.u3.s1#1")) (.n (val% «verify_tables» "kb[5]"))),
    .atom (.rangeCheck (.n (val% «verify_tables» "s56.u3.s1#1")) (.n (val% «verify_tables» "s56.u3.s1#2")) (.n (val% «verify_tables» "s56.u3.s1#3")) (.n (val% «verify_tables» "s56.u3.s1#4")) (.n (val% «verify_tables» "s56.u3.s1#0"))),
    .atom (.add (.n (val% «verify_tables» "zc_is_a_tau@4~0")) (.n (val% «verify_tables» "g_zc_n")) (.n (val% «verify_tables» "kb[5]"))),
    .atom (.mul (.n (val% «verify_tables» "zc_is_a_tau@4")) (.n (val% «verify_tables» "zc_is_a_tau@3")) (.n (val% «verify_tables» "zc_is_a_tau@4~0"))),
    .atom (.const (.n (val% «verify_tables» "s56.u4.s1#0")) (word 4294967296 0)),
    .atom (.mul (.n (val% «verify_tables» "g_zc_n")) (.n (val% «verify_tables» "s56.u4.s1#1")) (.n (val% «verify_tables» "kb[6]"))),
    .atom (.rangeCheck (.n (val% «verify_tables» "s56.u4.s1#1")) (.n (val% «verify_tables» "s56.u4.s1#2")) (.n (val% «verify_tables» "s56.u4.s1#3")) (.n (val% «verify_tables» "s56.u4.s1#4")) (.n (val% «verify_tables» "s56.u4.s1#0"))),
    .atom (.add (.n (val% «verify_tables» "zc_is_a_tau@5~0")) (.n (val% «verify_tables» "g_zc_n")) (.n (val% «verify_tables» "kb[6]"))),
    .atom (.mul (.n (val% «verify_tables» "zc_is_a_tau@5")) (.n (val% «verify_tables» "zc_is_a_tau@4")) (.n (val% «verify_tables» "zc_is_a_tau@5~0"))),
    .atom (.const (.n (val% «verify_tables» "s56.u5.s1#0")) (word 4294967296 0)),
    .atom (.mul (.n (val% «verify_tables» "g_zc_n")) (.n (val% «verify_tables» "s56.u5.s1#1")) (.n (val% «verify_tables» "kb[7]"))),
    .atom (.rangeCheck (.n (val% «verify_tables» "s56.u5.s1#1")) (.n (val% «verify_tables» "s56.u5.s1#2")) (.n (val% «verify_tables» "s56.u5.s1#3")) (.n (val% «verify_tables» "s56.u5.s1#4")) (.n (val% «verify_tables» "s56.u5.s1#0"))),
    .atom (.add (.n (val% «verify_tables» "zc_is_a_tau@6~0")) (.n (val% «verify_tables» "g_zc_n")) (.n (val% «verify_tables» "kb[7]"))),
    .atom (.mul (.n (val% «verify_tables» "zc_is_a_tau@6")) (.n (val% «verify_tables» "zc_is_a_tau@5")) (.n (val% «verify_tables» "zc_is_a_tau@6~0"))),
    .atom (.const (.n (val% «verify_tables» "s57#0")) (word 0 0)),
    .atom (.assertEq (.n (val% «verify_tables» "zc_is_a_tau@6")) (.n (val% «verify_tables» "s57#0"))),
    .atom (.const (.n (val% «verify_tables» "s58#0")) (word 4294967296 0)),
    .atom (.mul (.n (val% «verify_tables» "g_bus_mu")) (.n (val% «verify_tables» "s58#1")) (.n (val% «verify_tables» "g_zc_n"))),
    .atom (.rangeCheck (.n (val% «verify_tables» "s58#1")) (.n (val% «verify_tables» "s58#2")) (.n (val% «verify_tables» "s58#3")) (.n (val% «verify_tables» "s58#4")) (.n (val% «verify_tables» "s58#0"))),
    .atom (.const (.n (val% «verify_tables» "s59.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0")) (word 1 0)),
    .atom (.const (.n (val% «verify_tables» "s59.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[1]")) (word 0 0)),
    .atom (.const (.n (val% «verify_tables» "s59.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[2]")) (word 0 0)),
    .atom (.const (.n (val% «verify_tables» "s59.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[3]")) (word 0 0)),
    .atom (.const (.n (val% «verify_tables» "s59.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[4]")) (word 0 0)),
    .atom (.keccak [.n (val% «verify_tables» "rate[0]@3"), .n (val% «verify_tables» "rate[1]@3"), .n (val% «verify_tables» "s59.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[1]"), .n (val% «verify_tables» "s59.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[1]"), .n (val% «verify_tables» "s59.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[1]"), .n (val% «verify_tables» "s59.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[2]"), .n (val% «verify_tables» "s59.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[3]"), .n (val% «verify_tables» "s59.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[4]"), .n (val% «verify_tables» "sp[0]@2"), .n (val% «verify_tables» "sp[1]@2"), .n (val% «verify_tables» "sp[2]@2"), .n (val% «verify_tables» "sp[3]@2"), .n (val% «verify_tables» "sp[4]@2")] [.n (val% «verify_tables» "nxt[0]@3"), .n (val% «verify_tables» "nxt[1]@3"), .n (val% «verify_tables» "nxt[2]@3"), .n (val% «verify_tables» "nxt[3]@3"), .n (val% «verify_tables» "nxt[4]@3"), .n (val% «verify_tables» "nxt[5]@3"), .n (val% «verify_tables» "nxt[6]@3"), .n (val% «verify_tables» "nxt[7]@3"), .n (val% «verify_tables» "nxt[8]@3"), .n (val% «verify_tables» "nxt[9]@3"), .n (val% «verify_tables» "nxt[10]@3"), .n (val% «verify_tables» "nxt[11]@3"), .n (val% «verify_tables» "nxt[12]@3")] false false),
    .atom (.const (.n (val% «verify_tables» "zc_xi_pows[0]")) (word 1 0)),
    .atom (.mul (.n (val% «verify_tables» "zc_xi_pows[1]")) (.n (val% «verify_tables» "zc_xi_pows[0]")) (.n (val% «verify_tables» "nxt[0]@3"))),
    .atom (.mul (.n (val% «verify_tables» "zc_xi_pows[2]")) (.n (val% «verify_tables» "zc_xi_pows[1]")) (.n (val% «verify_tables» "nxt[0]@3"))),
    .atom (.mul (.n (val% «verify_tables» "zc_xi_pows[3]")) (.n (val% «verify_tables» "zc_xi_pows[2]")) (.n (val% «verify_tables» "nxt[0]@3"))),
    .atom (.mul (.n (val% «verify_tables» "zc_xi_pows[4]")) (.n (val% «verify_tables» "zc_xi_pows[3]")) (.n (val% «verify_tables» "nxt[0]@3"))),
    .atom (.mul (.n (val% «verify_tables» "bus_target@1")) (.n (val% «verify_tables» "zc_xi_pows[2]")) (.n (val% «verify_tables» "bus_table_total[0]"))),
    .atom (.mul (.n (val% «verify_tables» "bus_target@2~0")) (.n (val% «verify_tables» "zc_xi_pows[3]")) (.n (val% «verify_tables» "bus_table_total[1]"))),
    .atom (.add (.n (val% «verify_tables» "bus_target@2")) (.n (val% «verify_tables» "bus_target@1")) (.n (val% «verify_tables» "bus_target@2~0"))),
    .atom (.mul (.n (val% «verify_tables» "bus_target@3~0")) (.n (val% «verify_tables» "zc_xi_pows[4]")) (.n (val% «verify_tables» "bus_table_total[2]"))),
    .atom (.add (.n (val% «verify_tables» "bus_target@3")) (.n (val% «verify_tables» "bus_target@2")) (.n (val% «verify_tables» "bus_target@3~0"))),
    .atom (.hint (.alloc (.n (val% «verify_tables» "zc_rounds")) 245)),
    .atom (.hint (.alloc (.n (val% «verify_tables» "zc_cprod")) 35)),
    .atom (.load (.n (val% «verify_tables» "nxt[8]@3")) (.n (val% «verify_tables» "zc_rounds")) 0),
    .atom (.load (.n (val% «verify_tables» "nxt[9]@3")) (.n (val% «verify_tables» "zc_rounds")) 1),
    .atom (.load (.n (val% «verify_tables» "nxt[10]@3")) (.n (val% «verify_tables» "zc_rounds")) 2),
    .atom (.load (.n (val% «verify_tables» "nxt[11]@3")) (.n (val% «verify_tables» "zc_rounds")) 3),
    .atom (.load (.n (val% «verify_tables» "nxt[12]@3")) (.n (val% «verify_tables» "zc_rounds")) 4),
    .atom (.const (.n (val% «verify_tables» "s68#0")) (word 2 0)),
    .atom (.mul (.n (val% «verify_tables» "s68#1")) (.n (val% «verify_tables» "cursor@4")) (.n (val% «verify_tables» "s68#0"))),
    .atom (.load (.n (val% «verify_tables» "s68#1")) (.n (val% «verify_tables» "zc_rounds")) 5),
    .atom (.load (.n (val% «verify_tables» "bus_target@3")) (.n (val% «verify_tables» "zc_rounds")) 6),
    .atom (.const (.n (val% «verify_tables» "s70#0")) (word 1 0)),
    .atom (.load (.n (val% «verify_tables» "s70#0")) (.n (val% «verify_tables» "zc_cprod")) 0),
    .atom (.hint (.alloc (.n (val% «verify_tables» "zc_rk")) 34)),
    .atom (.const (.n (val% «verify_tables» "s72#0")) (word 1 0)),
    .atom (.add (.n (val% «verify_tables» "s72#1")) (.n (val% «verify_tables» "s72#0")) (.n (val% «verify_tables» "g_zc_n"))),
    .atom (.const (.n (val% «verify_tables» "s72#2")) (word 1 0)),
    .callIf (.n (val% «verify_tables» "s72#1")) name% «verify_tables_loop0» [.n (val% «verify_tables» "s72#2"), .n (val% «verify_tables» "g_zc_n"), .n (val% «verify_tables» "zc_rounds"), .n (val% «verify_tables» "tabs"),
        .n (val% «verify_tables» "zc_rk"), .n (val% «verify_tables» "zc_cprod")],
    .atom (.mul (.n (val% «verify_tables» "zc_last~0")) (.n (val% «verify_tables» "g_zc_n")) (.n (val% «verify_tables» "g_zc_n"))),
    .atom (.mul (.n (val% «verify_tables» "zc_last~1")) (.n (val% «verify_tables» "zc_last~0")) (.n (val% «verify_tables» "g_zc_n"))),
    .atom (.mul (.n (val% «verify_tables» "zc_last~2")) (.n (val% «verify_tables» "zc_last~1")) (.n (val% «verify_tables» "zc_last~1"))),
    .atom (.mul (.n (val% «verify_tables» "zc_last~3")) (.n (val% «verify_tables» "zc_last~2")) (.n (val% «verify_tables» "g_zc_n"))),
    .atom (.mul (.n (val% «verify_tables» "zc_last")) (.n (val% «verify_tables» "zc_rounds")) (.n (val% «verify_tables» "zc_last~3"))),
    .atom (.load (.n (val% «verify_tables» "fs_load.sp[0]")) (.n (val% «verify_tables» "zc_last")) 0),
    .atom (.load (.n (val% «verify_tables» "fs_load.sp[1]")) (.n (val% «verify_tables» "zc_last")) 1),
    .atom (.load (.n (val% «verify_tables» "fs_load.sp[2]")) (.n (val% «verify_tables» "zc_last")) 2),
    .atom (.load (.n (val% «verify_tables» "fs_load.sp[3]")) (.n (val% «verify_tables» "zc_last")) 3),
    .atom (.load (.n (val% «verify_tables» "fs_load.sp[4]")) (.n (val% «verify_tables» "zc_last")) 4),
    .atom (.load (.n (val% «verify_tables» "cursor@5")) (.n (val% «verify_tables» "zc_last")) 5),
    .atom (.load (.n (val% «verify_tables» "claim")) (.n (val% «verify_tables» "zc_last")) 6),
    .atom (.hint (.alloc (.n (val% «verify_tables» "zc_peq")) 35)),
    .call "eq_prefix_chain_rev" [.n (val% «verify_tables» "zc_peq"), .n (val% «verify_tables» "chi"), .n (val% «verify_tables» "zc_rk"), .n (val% «verify_tables» "zeta1"), .n (val% «verify_tables» "g_zc_n")] []]

/-- `verify_tables`' statements `nxt[0]@42 ..< ret` (G:2716-2723). -/
noncomputable def zTail : List Stmt := [
    .atom (.keccak [.n (val% «verify_tables» "rate[0]@42"), .n (val% «verify_tables» "rate[1]@42"), .n (val% «verify_tables» "s59.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[1]"), .n (val% «verify_tables» "s59.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[1]"), .n (val% «verify_tables» "s59.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[1]"), .n (val% «verify_tables» "s59.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[2]"), .n (val% «verify_tables» "s59.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[3]"), .n (val% «verify_tables» "s59.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[4]"), .n (val% «verify_tables» "nxt[8]@41"), .n (val% «verify_tables» "nxt[9]@41"), .n (val% «verify_tables» "nxt[10]@41"), .n (val% «verify_tables» "nxt[11]@41"), .n (val% «verify_tables» "nxt[12]@41")] [.n (val% «verify_tables» "nxt[0]@42"), .n (val% «verify_tables» "nxt[1]@42"), .n (val% «verify_tables» "nxt[2]@42"), .n (val% «verify_tables» "nxt[3]@42"), .n (val% «verify_tables» "nxt[4]@42"), .n (val% «verify_tables» "nxt[5]@42"), .n (val% «verify_tables» "nxt[6]@42"), .n (val% «verify_tables» "nxt[7]@42"), .n (val% «verify_tables» "nxt[8]@42"), .n (val% «verify_tables» "nxt[9]@42"), .n (val% «verify_tables» "nxt[10]@42"), .n (val% «verify_tables» "nxt[11]@42"), .n (val% «verify_tables» "nxt[12]@42")] false false),
    .atom (.hint (.limbs (.n (val% «verify_tables» "pi_0")) [.n (val% «verify_tables» "lo[0]@1")])),
    .atom (.add (.n (val% «verify_tables» "hi@1~0")) (.n (val% «verify_tables» "pi_0")) (.n (val% «verify_tables» "lo[0]@1"))),
    .atom (.const (.n (val% «verify_tables» "hi@1~1")) (word 2 1)),
    .atom (.mul (.n (val% «verify_tables» "hi@1")) (.n (val% «verify_tables» "hi@1~0")) (.n (val% «verify_tables» "hi@1~1"))),
    .atom (.assertInK (.n (val% «verify_tables» "lo[0]@1")) (.n (val% «verify_tables» "hi@1"))),
    .atom (.hint (.limbs (.n (val% «verify_tables» "pi_1")) [.n (val% «verify_tables» "lo[0]@2")])),
    .atom (.add (.n (val% «verify_tables» "hi@2~0")) (.n (val% «verify_tables» "pi_1")) (.n (val% «verify_tables» "lo[0]@2"))),
    .atom (.const (.n (val% «verify_tables» "hi@2~1")) (word 2 1)),
    .atom (.mul (.n (val% «verify_tables» "hi@2")) (.n (val% «verify_tables» "hi@2~0")) (.n (val% «verify_tables» "hi@2~1"))),
    .atom (.assertInK (.n (val% «verify_tables» "lo[0]@2")) (.n (val% «verify_tables» "hi@2"))),
    .atom (.add (.n (val% «verify_tables» "s87#0")) (.n (val% «verify_tables» "lo[0]@1")) (.n (val% «verify_tables» "lo[0]@2"))),
    .atom (.mul (.n (val% «verify_tables» "s87#1")) (.n (val% «verify_tables» "nxt[0]@42")) (.n (val% «verify_tables» "s87#0"))),
    .atom (.add (.n (val% «verify_tables» "s87#2")) (.n (val% «verify_tables» "lo[0]@1")) (.n (val% «verify_tables» "s87#1"))),
    .atom (.load (.n (val% «verify_tables» "s87#2")) (.n (val% «verify_tables» "claim_pool")) 157),
    .atom (.add (.n (val% «verify_tables» "s89#0")) (.n (val% «verify_tables» "hi@1")) (.n (val% «verify_tables» "hi@2"))),
    .atom (.mul (.n (val% «verify_tables» "s89#1")) (.n (val% «verify_tables» "nxt[0]@42")) (.n (val% «verify_tables» "s89#0"))),
    .atom (.add (.n (val% «verify_tables» "s89#2")) (.n (val% «verify_tables» "hi@1")) (.n (val% «verify_tables» "s89#1"))),
    .atom (.load (.n (val% «verify_tables» "s89#2")) (.n (val% «verify_tables» "claim_pool")) 158),
    .atom (.copy (.n (val% «verify_tables» "s91#0")) (.n (val% «verify_tables» "nxt[8]@42"))),
    .atom (.copy (.n (val% «verify_tables» "s91#0[1]")) (.n (val% «verify_tables» "nxt[9]@42"))),
    .atom (.copy (.n (val% «verify_tables» "s91#0[2]")) (.n (val% «verify_tables» "nxt[10]@42"))),
    .atom (.copy (.n (val% «verify_tables» "s91#0[3]")) (.n (val% «verify_tables» "nxt[11]@42"))),
    .atom (.copy (.n (val% «verify_tables» "s91#0[4]")) (.n (val% «verify_tables» "nxt[12]@42"))),
    .atom (.const (.n (val% «verify_tables» "s91#1")) (word 10905190400 0)),
    .atom (.mul (.n (val% «verify_tables» "s91#2")) (.n (val% «verify_tables» "cursor@5")) (.n (val% «verify_tables» "s91#1"))),
    .atom (.copy (.n (val% «verify_tables» "s91#0[5]")) (.n (val% «verify_tables» "s91#2"))),
    .atom (.copy (.n (val% «verify_tables» "s91#0[6]")) (.n (val% «verify_tables» "g_zc_n"))),
    .atom (.copy (.n (val% «verify_tables» "s91#0[7]")) (.n (val% «verify_tables» "x@8"))),
    .atom (.copy (.n (val% «verify_tables» "s91#0[8]")) (.n (val% «verify_tables» "nxt[0]@42"))),
    .atom (.copy (.n (val% «verify_tables» "s91#0[9]")) (.n (val% «verify_tables» "cursor@5")))]

theorem zBlk_at : tbStmtsEqb zBlk ((vtPre.drop (pos% «verify_tables» "g_zc_n")).take zBlk.length) = true := by
  simp only [vtPre_drop]; decide +kernel

theorem zTail_at : tbStmtsEqb zTail ((vtPre.drop (pos% «verify_tables» "nxt[0]@42")).take zTail.length) = true := by
  simp only [vtPre_drop]; decide +kernel

/-! ## The honest rounds -/

/-- The capacity and the claim before round `j`. -/
def zcRec (cap0 : List E) (cl0 : E) (xs : List E) : ℕ → List E × E
  | 0 => (cap0, cl0)
  | j + 1 =>
    let r := zcRec cap0 cl0 xs j
    let c0 := xs.getD (3 * j) 0
    let c2 := xs.getD (3 * j + 1) 0
    let c3 := xs.getD (3 * j + 2) 0
    let s := ((⟨r.1, []⟩ : Fs).absorbAll [c0, c2, c3] dsObserve).squeeze
    (s.2.cap, polyEval [c0, r.2 + sumE [c2, c3], c2, c3] s.1)

/-- Round `j`'s challenge. -/
def zcCh (cap0 : List E) (cl0 : E) (xs : List E) (j : ℕ) : E :=
  ((⟨(zcRec cap0 cl0 xs j).1, []⟩ : Fs).absorbAll
    [xs.getD (3 * j) 0, xs.getD (3 * j + 1) 0, xs.getD (3 * j + 2) 0] dsObserve).squeeze.1

/-- Record `j`: the capacity, the cursor, the claim. -/
def zcRecW (cap0 : List E) (cl0 cur0 : E) (xs : List E) (j : ℕ) : List E :=
  (zcRec cap0 cl0 xs j).1 ++ [cur0 * gen ^ (3 * j), (zcRec cap0 cl0 xs j).2]

/-- The records `0 ..= n` (`zc_rounds`). -/
def zcRoundsW (cap0 : List E) (cl0 cur0 : E) (xs : List E) (n : ℕ) : List E :=
  (List.range (n + 1)).flatMap (zcRecW cap0 cl0 cur0 xs)

/-- The challenges' running products (`zc_cprod`). -/
def zcCprodW (cap0 : List E) (cl0 : E) (xs : List E) (n : ℕ) : List E :=
  (List.range (n + 1)).map fun j ↦ ((List.range j).map (zcCh cap0 cl0 xs)).prod

/-- The challenges, in round order (`zc_rk`). -/
def zcRkW (cap0 : List E) (cl0 : E) (xs : List E) (n : ℕ) : List E :=
  (List.range n).map (zcCh cap0 cl0 xs)

/-- The challenges, last first (`chi`). -/
def zcChis (cap0 : List E) (cl0 : E) (xs : List E) (n : ℕ) : List E :=
  (zcRkW cap0 cl0 xs n).reverse

theorem zcRec_len {cap0 : List E} {cl0 : E} {xs : List E} (h : cap0.length = 5) :
    ∀ j, (zcRec cap0 cl0 xs j).1.length = 5
  | 0 => h
  | _ + 1 => rfl

theorem zcRecW_len {cap0 : List E} {cl0 cur0 : E} {xs : List E} (h : cap0.length = 5) (j : ℕ) :
    (zcRecW cap0 cl0 cur0 xs j).length = 7 := by
  simp [zcRecW, zcRec_len h]

theorem zcRoundsW_len {cap0 : List E} {cl0 cur0 : E} {xs : List E} (h : cap0.length = 5) :
    ∀ n, (zcRoundsW cap0 cl0 cur0 xs n).length = 7 * (n + 1)
  | 0 => by simp [zcRoundsW, zcRecW_len h]
  | n + 1 => by
    rw [zcRoundsW, List.range_succ, List.flatMap_append, List.length_append, ← zcRoundsW,
      zcRoundsW_len h n]
    simp [zcRecW_len h]; ring

/-- **The records**, one by one. -/
theorem zcRoundsW_reads {rd : Reader} {R : E} {cap0 : List E} {cl0 cur0 : E} {xs : List E}
    (h : cap0.length = 5) {n : ℕ} (hR : TbReadsAt rd R (zcRoundsW cap0 cl0 cur0 xs n)) :
    ∀ j ≤ n, TbReadsAt rd (R * gen ^ (7 * j)) (zcRecW cap0 cl0 cur0 xs j) := by
  induction n with
  | zero =>
    intro j hj
    obtain rfl : j = 0 := by omega
    simpa [zcRoundsW] using hR
  | succ n ih =>
    rw [zcRoundsW, List.range_succ, List.flatMap_append, ← zcRoundsW, tbReadsAt_append,
      zcRoundsW_len h] at hR
    intro j hj
    rcases Nat.lt_or_ge j (n + 1) with hj' | hj'
    · exact ih hR.1 j (by omega)
    · obtain rfl : j = n + 1 := by omega
      simpa using hR.2

/-- A record's parts. -/
theorem zc_rec_parts {rd : Reader} {p : E} {cap : List E} {a b : E} (h5 : cap.length = 5)
    (h : TbReadsAt rd p (cap ++ [a, b])) :
    CapAt rd p 0 1 cap ∧ LoadHolds rd p 5 a ∧ LoadHolds rd p 6 b := by
  rw [tbReadsAt_append, h5, tbReadsAt_cons, tbReadsAt_singleton, tb_loadHolds_mul_gen_pow,
    mul_assoc, ← pow_succ, tb_loadHolds_mul_gen_pow] at h
  refine ⟨⟨h5, fun j hj => ?_⟩, h.2.1, h.2.2⟩
  simpa using h.1 j hj

/-- **Every iteration of `verify_tables_loop0` has its facts** on the honest buffers and words. -/
theorem zc_l10B {rd : Reader} {R tabs rkb C : E} {cap0 : List E} {cl0 cur0 : E} {xs : List E} {n : ℕ}
    (h5 : cap0.length = 5)
    (hR : TbReadsAt rd R (zcRoundsW cap0 cl0 cur0 xs n))
    (hC : TbReadsAt rd C (zcCprodW cap0 cl0 xs n)) (hrk : TbReadsAt rd rkb (zcRkW cap0 cl0 xs n))
    (hxs : TbReadsAt rd cur0 xs) (hxl : xs.length = 3 * n) :
    ∀ j < n, L10B rd R tabs rkb C (gen ^ j) := by
  intro j hj
  have e7 : R * (gen ^ j) ^ 7 = R * gen ^ (7 * j) := by rw [← pow_mul, mul_comm j 7]
  obtain ⟨hc0, hcur, hcl⟩ := zc_rec_parts (zcRec_len h5 j) (zcRoundsW_reads h5 hR j (by omega))
  obtain ⟨hc1, hcur1, hcl1⟩ := zc_rec_parts (zcRec_len h5 (j + 1))
    (zcRoundsW_reads h5 hR (j + 1) (by omega))
  have e71 : R * gen ^ (7 * (j + 1)) = R * gen ^ (7 * j) * gen ^ 7 := by ring
  rw [e71] at hc1 hcur1 hcl1
  rw [tb_loadHolds_mul_gen_pow] at hcur1 hcl1
  have hrd : ReadsAt rd (cur0 * gen ^ (3 * j))
      [xs.getD (3 * j) 0, xs.getD (3 * j + 1) 0, xs.getD (3 * j + 2) 0] := by
    intro k hk
    simp only [List.length_cons, List.length_nil] at hk
    rw [tb_loadHolds_mul_gen_pow]
    have hk' := hxs (3 * j + k) (by omega)
    interval_cases k
    · show LoadHolds rd cur0 (3 * j + 0) (xs.getD (3 * j) 0)
      rw [List.getD_eq_getElem _ _ (by omega)]; exact hk'
    · show LoadHolds rd cur0 (3 * j + 1) (xs.getD (3 * j + 1) 0)
      rw [List.getD_eq_getElem _ _ (by omega)]; exact hk'
    · show LoadHolds rd cur0 (3 * j + 2) (xs.getD (3 * j + 2) 0)
      rw [List.getD_eq_getElem _ _ (by omega)]; exact hk'
  refine ⟨cur0 * gen ^ (3 * j), (zcRec cap0 cl0 xs j).2, cur0 * gen ^ (3 * j) * gen ^ 3,
    (zcRec cap0 cl0 xs (j + 1)).2, zcCh cap0 cl0 xs j, by rw [e7]; exact hcur, by rw [e7]; exact hcl,
    ?_, ?_, by rw [e7]; exact hcl1, ?_, ((List.range j).map (zcCh cap0 cl0 xs)).prod, ?_, ?_⟩
  · rw [e7]
    refine (sumcheck_round4_holds rd _ _).mpr ⟨(zcRec cap0 cl0 xs j).1, _, _, _, hc0,
      hrd, hc1, rfl⟩
  · rw [e7, show cur0 * gen ^ (3 * j) * gen ^ 3 = cur0 * gen ^ (3 * (j + 1)) by ring]
    exact hcur1
  · rw [tb_loadHolds_mul_gen_pow, Nat.add_zero]
    simpa [zcRkW] using hrk j (by simp [zcRkW]; omega)
  · rw [tb_loadHolds_mul_gen_pow, Nat.add_zero]
    have := hC j (by simp [zcCprodW]; omega)
    simpa [zcCprodW] using this
  · rw [tb_loadHolds_mul_gen_pow]
    have := hC (j + 1) (by simp [zcCprodW]; omega)
    simp only [zcCprodW, List.getElem_map, List.getElem_range] at this
    rwa [List.range_succ, List.map_append, List.prod_append, List.map_singleton,
      List.prod_singleton] at this

/-- **`chi` is `zc_rk` reversed** on the honest buffers. -/
theorem zc_chiRev {rd : Reader} {rkb chi : E} {cap0 : List E} {cl0 : E} {xs : List E} {n : ℕ}
    (hrk : TbReadsAt rd rkb (zcRkW cap0 cl0 xs n)) (hchi : TbReadsAt rd chi (zcChis cap0 cl0 xs n)) :
    ∀ x < n, ∃ v, LoadHolds rd rkb (n - 1 - x) v ∧ LoadHolds rd chi x v := by
  intro x hx
  refine ⟨zcCh cap0 cl0 xs (n - 1 - x), ?_, ?_⟩
  · simpa [zcRkW] using hrk (n - 1 - x) (by simp [zcRkW]; omega)
  · have := hchi x (by simp [zcChis, zcRkW]; omega)
    simpa [zcChis, zcRkW, List.getElem_reverse] using this

theorem zc_slice {xs : List E} {j k : ℕ} (h : 3 * (j + k + 1) ≤ xs.length) :
    (xs.drop (3 * j)).take (3 * (k + 1)) =
      [xs.getD (3 * j) 0, xs.getD (3 * j + 1) 0, xs.getD (3 * j + 2) 0] ++
        (xs.drop (3 * (j + 1))).take (3 * k) := by
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    simp only [List.getElem_take, List.getElem_drop]
    rcases Nat.lt_or_ge i 3 with hi | hi
    · rw [List.getElem_append_left (by simpa using hi)]
      interval_cases i <;> simp <;> rw [List.getElem?_eq_getElem (by omega)] <;> rfl
    · rw [List.getElem_append_right (by simpa using hi)]
      simp only [List.length_cons, List.length_nil, List.getElem_take, List.getElem_drop]
      congr 1; omega

/-- **The honest rounds are the specification's sumcheck.** -/
theorem zc_run (cap0 : List E) (cl0 : E) {xs : List E} {n : ℕ} (hxl : xs.length = 3 * n) :
    RunsTo (sumcheck cl0 4 (List.replicate n none)) ⟨cap0, []⟩ xs
      ((List.range n).map (zcCh cap0 cl0 xs), (zcRec cap0 cl0 xs n).2)
      ⟨(zcRec cap0 cl0 xs n).1, []⟩ := by
  have key : ∀ k j, j + k = n → RunsTo (sumcheck (zcRec cap0 cl0 xs j).2 4 (List.replicate k none))
      ⟨(zcRec cap0 cl0 xs j).1, []⟩ ((xs.drop (3 * j)).take (3 * k))
      ((List.range k).map (fun i ↦ zcCh cap0 cl0 xs (j + i)), (zcRec cap0 cl0 xs n).2)
      ⟨(zcRec cap0 cl0 xs n).1, []⟩ := by
    intro k
    induction k with
    | zero =>
      intro j hj
      obtain rfl : j = n := by omega
      exact runsTo_sumcheck_nil _ _ _
    | succ k ih =>
      intro j hj
      have h1 := runsTo_roundPolyNone ⟨(zcRec cap0 cl0 xs j).1, []⟩ (zcRec cap0 cl0 xs j).2
        (xs.getD (3 * j) 0) [xs.getD (3 * j + 1) 0, xs.getD (3 * j + 2) 0] 4 rfl (by decide)
      have h2 := ih (j + 1) (by omega)
      have e : ((⟨(zcRec cap0 cl0 xs j).1, []⟩ : Fs).absorb (xs.getD (3 * j) 0) dsObserve).absorbAll
          [xs.getD (3 * j + 1) 0, xs.getD (3 * j + 2) 0] dsObserve =
          (⟨(zcRec cap0 cl0 xs j).1, []⟩ : Fs).absorbAll
            [xs.getD (3 * j) 0, xs.getD (3 * j + 1) 0, xs.getD (3 * j + 2) 0] dsObserve := rfl
      rw [e] at h1
      have h := runsTo_sumcheck_cons h1 h2
      rw [List.replicate_succ, zc_slice (by omega), List.range_succ_eq_map, List.map_cons,
        List.map_map]
      refine h.of_eq rfl rfl ?_ rfl
      rw [Nat.add_zero]
      refine Prod.ext (congrArg₂ List.cons rfl (List.map_congr_left fun i _ => ?_)) rfl
      simp only [Function.comp_apply]
      rw [show j + 1 + i = j + (i + 1) by omega]
  have := key n 0 (by omega)
  simp only [Nat.mul_zero, List.drop_zero, Nat.zero_add] at this
  rw [← hxl, List.take_length] at this
  exact this

end
end LeanVM.Guest.B1.Tables
