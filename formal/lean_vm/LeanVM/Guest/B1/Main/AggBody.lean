/-
  LeanVM.Guest.B1.Main.AggBody

  `aggregate_claims`' body, checked by kernel evaluation, and its baked seed.
-/

module

public import LeanVM.Guest.B1.Main.AggCols
public import LeanVM.Guest.B1.Bits.GrindData
public import LeanVM.Guest.Value.KeccakConst
public import LeanVM.Guest.B1.Main.Body
public import LeanVM.Guest.Data.NameStrings
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«aggregate_claims»

/-!
# `aggregate_claims`' body

`aggregate_claims(n_children_g, child_pi, child_fresh, child_carried, defer_stmt, tabs)`
(`lean_ethereum.py`): its body is its block `aggP`, then `ret []` (`agg_shape`). `aggOk` checks the
block: the batching seed's capacity cells `AGG_SEED_*` and the packed count `n_children_g` with
three zeros in row `0` of `absorb`, the guarded loop `aggregate_claims_loop0` and its tables
(`fresh_row`, `carried_row`), the permutation of the last absorbing row (`aggKi`, `aggKo`), the
nonce `bc_sumcheck_msgs[0]` absorbed with the tag `4` and permuted (`fsNonceT`, `padRunT`, `aggNi`,
`aggNo`), `grind_check` inlined on its cell `1` with `3` bits and the window tables (`aggGrindA`),
the challenge `λ` its cell `0` with `λ²`, the six column challenges squeezed into `col`
(`sqChainOk`, on eight zero rate cells, `aggZs`), their equality table (`eqtree` inlined,
`treeOk`) and its last level `eq_col` at `g^62`, the guarded loop `aggregate_claims_loop1`
(`fresh_val`), record `0` of `bc_chain` (power `1`, claim `0`), the guarded loop
`aggregate_claims_loop2`, `batch_sumcheck__L25` on the last squeeze's capacity with the rounds at
`bc_sumcheck_msgs·g`, the last record's claim and the point, `bc_point1` (`1 + ` each coordinate),
the column factor `eq_cols` (`eqcChainOk`), the guarded loop `aggregate_claims_loop3` (weights
`bc_wsum`), the check that the final claim is `bc_star_hint` times the weight, and the claim
written at `defer_stmt`. `seed_cells`: the five constants are the capacity cells of
`Node.batchSeed` (`aggSeed_cells`).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Node

@[expose] public section

/-- `aggregate_claims`' block: its body without the final `ret []`. -/
noncomputable def aggP : List Stmt := (Fn.body fn% «aggregate_claims»).dropLast

set_option maxRecDepth 100000 in
theorem agg_shape : Fn.body fn% «aggregate_claims» = aggP ++ [Stmt.ret []] :=
  stmtsEqb_sound (by decide +kernel)

/-- The seed's constants `(lo, hi)`. -/
def seedLo : List (ℕ × ℕ) :=
  [(1562680967124014521, 0), (7666384441264927334, 11925545048015809408),
    (14528471851986820829, 15194020773630548750), (6704907289165917069, 10885225211858021658),
    (10587785389206534793, 159208925504336485)]

/-- The permutation of the last absorbing row (`fs_perm_pending`): its rate cells (four copied),
then its capacity. -/
def aggKi : List V := [.n (val% «aggregate_claims» "s15.i0:fs_perm_pending.s1#0"), .n (val% «aggregate_claims» "s15.i0:fs_perm_pending.s1#1"), .n (val% «aggregate_claims» "s15.i0:fs_perm_pending.s1#2"), .n (val% «aggregate_claims» "s15.i0:fs_perm_pending.s1#3"), .n (val% «aggregate_claims» "s15.i0:fs_perm_pending.s1#8"), .n (val% «aggregate_claims» "s15.i0:fs_perm_pending.s1#8[1]"), .n (val% «aggregate_claims» "s15.i0:fs_perm_pending.s1#8[2]"), .n (val% «aggregate_claims» "s15.i0:fs_perm_pending.s1#8[3]"), .n (val% «aggregate_claims» "sp[0]"), .n (val% «aggregate_claims» "sp[1]"), .n (val% «aggregate_claims» "sp[2]"),
  .n (val% «aggregate_claims» "sp[3]"), .n (val% «aggregate_claims» "sp[4]")]

/-- The permutation's outputs. -/
def aggKo : List V := (List.range 13).map fun i => .n ((val% «aggregate_claims» "fs_perm_pending.nxt[0]") + i)

/-- The nonce's permutation (`fs_absorb_nonce`): the nonce's two cells, the zero run, then the
capacity of the last absorbing row's permutation. -/
def aggNi : List V := permIns 1 [.n (val% «aggregate_claims» "nonce_rate[0]"), .n (val% «aggregate_claims» "nonce_rate[1]")] 74 [.n (val% «aggregate_claims» "fs_perm_pending.nxt[8]"), .n (val% «aggregate_claims» "fs_perm_pending.nxt[9]"), .n (val% «aggregate_claims» "fs_perm_pending.nxt[10]"), .n (val% «aggregate_claims» "fs_perm_pending.nxt[11]"), .n (val% «aggregate_claims» "fs_perm_pending.nxt[12]")]

/-- The nonce permutation's outputs. -/
def aggNo : List V := (List.range 13).map fun i => .n ((val% «aggregate_claims» "nxt[0]@2") + i)

/-- The nonce's `fs_pack` (`fsNonceT`) and the zero run (`padRunT`), as atoms. -/
def aggNonceA : List Atom :=
  [.load (.n (val% «aggregate_claims» "s16.e.s1#0")) (.n (val% «aggregate_claims» "bc_msgs")) 0, .copy (.n (val% «aggregate_claims» "nonce_rate[0]")) (.n (val% «aggregate_claims» "s16.e.s1#0")), .const (.n (val% «aggregate_claims» "nonce_rate[1]")) (word 0 dsPowNonce),
    .const (.n (val% «aggregate_claims» "s16.e.s1.i1:fs_absorb_nonce.s1.i0:fs_perm.s2.t.s0#0")) (word 1 0), .const (.n (val% «aggregate_claims» "s16.e.s1.i1:fs_absorb_nonce.s1.i0:fs_perm.s2.t.s0#0[1]")) (word 0 0), .const (.n (val% «aggregate_claims» "s16.e.s1.i1:fs_absorb_nonce.s1.i0:fs_perm.s2.t.s0#0[2]")) (word 0 0),
    .const (.n (val% «aggregate_claims» "s16.e.s1.i1:fs_absorb_nonce.s1.i0:fs_perm.s2.t.s0#0[3]")) (word 0 0), .const (.n (val% «aggregate_claims» "s16.e.s1.i1:fs_absorb_nonce.s1.i0:fs_perm.s2.t.s0#0[4]")) (word 0 0)]

theorem aggNonceA_eq : aggNonceA.map Stmt.atom = fsNonceT (.n (val% «aggregate_claims» "bc_msgs")) 0 (val% «aggregate_claims» "s16.e.s1#0") ++ padRunT 73 := rfl

/-- The first own value of the inlined `grind_check`, the cell after the nonce's permutation. -/
abbrev aggGo : ℕ := val% «aggregate_claims» "nxt[0]@2" + 13

/-- The inlined `grind_check(nxt[1], tabs, 3)`, as atoms (`aggGrindA_eq`). -/
def aggGrindA : List Atom :=
  (gcInlineT 3 aggGo (.n (val% «aggregate_claims» "nxt[1]@2"))
    (.n (val% «aggregate_claims» "tabs"))).filterMap fun s => match s with
    | .atom a => some a
    | _ => none

set_option maxRecDepth 100000 in
theorem aggGrindA_eq : aggGrindA.map Stmt.atom = gcInlineT 3 aggGo
    (.n (val% «aggregate_claims» "nxt[1]@2")) (.n (val% «aggregate_claims» "tabs")) :=
  stmtsEqb_sound (by decide +kernel)

/-- The column squeezes' eight zero rate cells: the zero constants of the nonce's zero run. -/
def aggZs : List V :=
  [.n (val% «aggregate_claims» "s16.e.s1.i1:fs_absorb_nonce.s1.i0:fs_perm.s2.t.s0#0[1]"),
    .n (val% «aggregate_claims» "s16.e.s1.i1:fs_absorb_nonce.s1.i0:fs_perm.s2.t.s0#0[1]"),
    .n (val% «aggregate_claims» "s16.e.s1.i1:fs_absorb_nonce.s1.i0:fs_perm.s2.t.s0#0[1]"),
    .n (val% «aggregate_claims» "s16.e.s1.i1:fs_absorb_nonce.s1.i0:fs_perm.s2.t.s0#0[1]"),
    .n (val% «aggregate_claims» "s16.e.s1.i1:fs_absorb_nonce.s1.i0:fs_perm.s2.t.s0#0[1]"),
    .n (val% «aggregate_claims» "s16.e.s1.i1:fs_absorb_nonce.s1.i0:fs_perm.s2.t.s0#0[2]"),
    .n (val% «aggregate_claims» "s16.e.s1.i1:fs_absorb_nonce.s1.i0:fs_perm.s2.t.s0#0[3]"),
    .n (val% «aggregate_claims» "s16.e.s1.i1:fs_absorb_nonce.s1.i0:fs_perm.s2.t.s0#0[4]")]

/-- The first squeeze's capacity: the nonce permutation's. -/
def aggCap0 : List V := (List.range 5).map fun i => .n ((val% «aggregate_claims» "nxt[0]@2") + 8 + i)

/-- The first value of `eqtree`'s level `t ≥ 1`: `rt@t`. -/
def aggTreeB (t : ℕ) : ℕ := val% «aggregate_claims» "rt@1" + 3 * (t - 1) + 3 * (2 ^ t - 2)

/-- **`aggregate_claims`' block, checked.** -/
noncomputable def aggOk : Bool :=
  let P := aggP
  let A := atomsIn P
  P.all Stmt.flat && decide ((fn% «aggregate_claims»).params = [.n (val% «aggregate_claims» "n_children_g"), .n (val% «aggregate_claims» "child_pi"), .n (val% «aggregate_claims» "child_fresh"), .n (val% «aggregate_claims» "child_carried"), .n (val% «aggregate_claims» "defer_stmt"),
      .n (val% «aggregate_claims» "tabs")]) &&
  (List.range 5).all (fun i => A.any (isConstAt (.n ((val% «aggregate_claims» "seed[0]") + i)) (seedLo.getD i (0, 0)).1
    (seedLo.getD i (0, 0)).2) && A.any (isLoadAt (.n ((val% «aggregate_claims» "seed[0]") + i)) (.n (val% «aggregate_claims» "absorb")) i)) &&
  packIn A (.n (val% «aggregate_claims» "n_children_g")) 15 &&
  (List.range 3).all (fun j => A.any (isConstAt (.n (17 + 2 * j)) 0 0) &&
    packIn A (.n (17 + 2 * j)) (17 + 2 * j)) &&
  (List.range 4).all (fun j => A.any (isLoadAt (.n (15 + 2 * j)) (.n (val% «aggregate_claims» "absorb")) (5 + 2 * j)) &&
    A.any (isLoadAt (.n (16 + 2 * j)) (.n (val% «aggregate_claims» "absorb")) (6 + 2 * j))) &&
  guardOk P (.n (val% «aggregate_claims» "s12#1")) name% «aggregate_claims_loop0» (.n (val% «aggregate_claims» "s12#2")) (.n (val% «aggregate_claims» "n_children_g")) [.n (val% «aggregate_claims» "absorb"), .n (val% «aggregate_claims» "child_fresh"), .n (val% «aggregate_claims» "fresh_row"), .n (val% «aggregate_claims» "child_carried"), .n (val% «aggregate_claims» "carried_row"),
      .n (val% «aggregate_claims» "child_pi")] &&
  monoIs A (.n (val% «aggregate_claims» "absorbed")) (.n (val% «aggregate_claims» "absorb")) (.n (val% «aggregate_claims» "n_children_g")) 13 &&
  A.any (isKeccakAt aggKi aggKo false false) && rowInOk A (.n (val% «aggregate_claims» "absorbed")) aggKi &&
  allIn A aggNonceA &&
  A.any (isKeccakAt aggNi aggNo false false) &&
  allIn A aggGrindA &&
  isMul A (.n (val% «aggregate_claims» "lam_sq")) (.n (val% «aggregate_claims» "nxt[0]@2")) (.n (val% «aggregate_claims» "nxt[0]@2")) &&
  sqChainOk A aggZs aggCap0 (val% «aggregate_claims» "nxt[0]@3") (.n (val% «aggregate_claims» "col")) splitLog &&
  treeOk A (.n (val% «aggregate_claims» "col")) (.n (val% «aggregate_claims» "eq_col_tree")) (val% «aggregate_claims» "r0") aggTreeB splitLog &&
  A.any (isConstAt (.n (val% «aggregate_claims» "s26#3")) 4611686018427387904 0) &&
  isMul A (.n (val% «aggregate_claims» "s26#4")) (.n (val% «aggregate_claims» "eq_col_tree")) (.n (val% «aggregate_claims» "s26#3")) &&
  guardOk P (.n (val% «aggregate_claims» "s26#1")) name% «aggregate_claims_loop1» (.n (val% «aggregate_claims» "s26#2")) (.n (val% «aggregate_claims» "n_children_g")) [.n (val% «aggregate_claims» "fresh_row"), .n (val% «aggregate_claims» "s26#4"), .n (val% «aggregate_claims» "fresh_val")] &&
  A.any (isConstAt (.n (val% «aggregate_claims» "s28#0")) 1 0) && A.any (isLoadAt (.n (val% «aggregate_claims» "s28#0")) (.n (val% «aggregate_claims» "bc_chain")) 0) &&
  A.any (isConstAt (.n (val% «aggregate_claims» "s29#0")) 0 0) && A.any (isLoadAt (.n (val% «aggregate_claims» "s29#0")) (.n (val% «aggregate_claims» "bc_chain")) 1) &&
  guardOk P (.n (val% «aggregate_claims» "s30#1")) name% «aggregate_claims_loop2» (.n (val% «aggregate_claims» "s30#2")) (.n (val% «aggregate_claims» "n_children_g")) [.n (val% «aggregate_claims» "bc_chain"), .n (val% «aggregate_claims» "fresh_row"), .n (val% «aggregate_claims» "carried_row"), .n (val% «aggregate_claims» "lam_sq"),
      .n (val% «aggregate_claims» "fresh_val"), .n (val% «aggregate_claims» "nxt[0]@2")] &&
  monoIs A (.n (val% «aggregate_claims» "bc_end")) (.n (val% «aggregate_claims» "bc_chain")) (.n (val% «aggregate_claims» "n_children_g")) 2 && A.any (isLoadAt (.n (val% «aggregate_claims» "bc_running@1")) (.n (val% «aggregate_claims» "bc_end")) 1) &&
  genMulOk A (.n (val% «aggregate_claims» "fs0~7")) (.n (val% «aggregate_claims» "bc_msgs")) &&
  hasCall P "batch_sumcheck__L25" [.n (val% «aggregate_claims» "nxt[8]@8"), .n (val% «aggregate_claims» "nxt[9]@8"), .n (val% «aggregate_claims» "nxt[10]@8"), .n (val% «aggregate_claims» "nxt[11]@8"), .n (val% «aggregate_claims» "nxt[12]@8"), .n (val% «aggregate_claims» "fs0~7"), .n (val% «aggregate_claims» "bc_running@1"), .n (val% «aggregate_claims» "bc_point"), .n (val% «aggregate_claims» "tabs")]
    [.n (val% «aggregate_claims» "fs0"), .n (val% «aggregate_claims» "fs1"), .n (val% «aggregate_claims» "fs2"), .n (val% «aggregate_claims» "fs3"), .n (val% «aggregate_claims» "fs4"), .n (val% «aggregate_claims» "bc_running@2")] &&
  (List.range 25).all (fun k => A.any (isConstAt (.n ((val% «aggregate_claims» "s36.u0.s0#0") + 3 * k)) 1 0) &&
    A.any (isLoadAt (.n ((val% «aggregate_claims» "s36.u0.s0#0") + 1 + 3 * k)) (.n (val% «aggregate_claims» "bc_point")) k) &&
    A.any (isAddAt (.n ((val% «aggregate_claims» "s36.u0.s0#0") + 2 + 3 * k)) (.n ((val% «aggregate_claims» "s36.u0.s0#0") + 3 * k)) (.n ((val% «aggregate_claims» "s36.u0.s0#0") + 1 + 3 * k))) &&
    A.any (isLoadAt (.n ((val% «aggregate_claims» "s36.u0.s0#0") + 2 + 3 * k)) (.n (val% «aggregate_claims» "bc_point1")) k)) &&
  eqcChainOk A (.n (val% «aggregate_claims» "col")) (.n (val% «aggregate_claims» "bc_point1")) 19 6 (.n (val% «aggregate_claims» "eq_cols@6")) &&
  A.any (isConstAt (.n (val% «aggregate_claims» "s39#0")) 0 0) && A.any (isLoadAt (.n (val% «aggregate_claims» "s39#0")) (.n (val% «aggregate_claims» "bc_wsum")) 0) &&
  guardOk P (.n (val% «aggregate_claims» "s40#1")) name% «aggregate_claims_loop3» (.n (val% «aggregate_claims» "s40#2")) (.n (val% «aggregate_claims» "n_children_g")) [.n (val% «aggregate_claims» "fresh_row"), .n (val% «aggregate_claims» "carried_row"), .n (val% «aggregate_claims» "bc_point1"), .n (val% «aggregate_claims» "bc_chain"),
      .n (val% «aggregate_claims» "bc_wsum"), .n (val% «aggregate_claims» "eq_cols@6"), .n (val% «aggregate_claims» "nxt[0]@2")] &&
  isMul A (.n (val% «aggregate_claims» "s41#0")) (.n (val% «aggregate_claims» "bc_wsum")) (.n (val% «aggregate_claims» "n_children_g")) && A.any (isLoadAt (.n (val% «aggregate_claims» "s41#1")) (.n (val% «aggregate_claims» "s41#0")) 0) &&
  isMul A (.n (val% «aggregate_claims» "s41#2")) (.n (val% «aggregate_claims» "bytecode_star")) (.n (val% «aggregate_claims» "s41#1")) && A.any (isAssertEqAt (.n (val% «aggregate_claims» "bc_running@2")) (.n (val% «aggregate_claims» "s41#2"))) &&
  (List.range 25).all (fun k => A.any (isLoadAt (.n ((val% «aggregate_claims» "s42.u0.s0#0") + k)) (.n (val% «aggregate_claims» "bc_point")) k) &&
    A.any (isLoadAt (.n ((val% «aggregate_claims» "s42.u0.s0#0") + k)) (.n (val% «aggregate_claims» "defer_stmt")) k)) &&
  A.any (isLoadAt (.n (val% «aggregate_claims» "bytecode_star")) (.n (val% «aggregate_claims» "defer_stmt")) 25)

set_option maxRecDepth 100000 in
theorem agg_ok : aggOk = true := by decide +kernel

/-- **The seed's constants are the batching seed's capacity cells.** -/
theorem seed_cells : ∀ i < 5,
    word (seedLo.getD i (0, 0)).1 (seedLo.getD i (0, 0)).2 = (capOf batchSeed).getD i 0 := by
  intro i hi
  have e := fun c : Fin 5 => aggSeed_cells c
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl | rfl | rfl
  · exact (e 0).trans rfl
  · exact (e 1).trans rfl
  · exact (e 2).trans rfl
  · exact (e 3).trans rfl
  · exact (e 4).trans rfl

set_option maxRecDepth 100000 in
/-- `eq_col = eq_col_tree · g^62`'s word. -/
theorem word_g62 : word 4611686018427387904 0 = gen ^ 62 := by
  rw [word_eOfNat, gen_pow_eq_ofK, eOfNat, ← gpowK_eq (by unfold u128Bound; omega)]
  congr 1

end
end LeanVM.Guest.B1.Main
