/-
  LeanVM.Guest.B1.Main.AggBody

  `aggregate_claims`' body (core function `34`), checked by kernel evaluation, and its baked seed.
-/

module

public import LeanVM.Guest.B1.Main.AggSqueeze
public import LeanVM.Guest.Value.KeccakConst
public import LeanVM.Guest.B1.Main.Body
public import LeanVM.Guest.Batch.Def
public import LeanVM.Guest.Data.NameStrings

/-!
# `aggregate_claims`' body

`aggregate_claims(n_children_g, child_pi, child_fresh, child_carried, defer_stmt, tabs)`
(`lean_ethereum.py`, G below): its body is its block `aggP`, then `ret []` (`agg_shape`). `aggOk`
checks the block: the batching seed's capacity cells `AGG_SEED_*` and the packed count
`n_children_g` with three zeros (`fs_pack`: a copy and the tag's cell, a zero's in place) in row `0` of `absorb`
(`.n 30`), the guarded loop `aggregate_claims_loop0` and its tables (`lf = .n 8`, `lc = .n 9`), the
permutation of the last absorbing row (`.n 39`, `aggKi`, `aggKo`), the nonce `bc_sumcheck_msgs[0]`
absorbed with the tag `4` and permuted (`fsNonceT`, `padRunT`, `aggNi`, `aggNo`), `grind_check__L2`
on its cell `1` and the window tables `.n 5`, the challenge `λ` its cell `0` (`.n 78`) with `λ²`
(`.n 91`), record `0` of `bc_chain` (`.n 95`: power `1`, claim `0`), the guarded loop
`aggregate_claims_loop1`, `batch_sumcheck__L23` on the nonce permutation's capacity with the rounds
at `bc_sumcheck_msgs·g` (`.n 106`), the last record's claim and the point at `.n 104`, `bc_point1`
(`.n 113`: `1 + ` each coordinate of the point), the guarded loop `aggregate_claims_loop2` (weights
`w = .n 185`), the check that its final claim is `bc_star_hint (.n 7)` times the weight, and the
claim written at `defer_stmt`. `seed_cells`: the five constants are the capacity cells of
`Node.batchSeed` (G3's `aggSeed_cells`).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
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
def aggKi : List V := [.n 45, .n 46, .n 47, .n 48, .n 53, .n 54, .n 55, .n 56, .n 40, .n 41, .n 42,
  .n 43, .n 44]

/-- The permutation's outputs. -/
def aggKo : List V := (List.range 13).map fun i => .n (57 + i)

/-- The nonce's permutation (`fs_absorb_nonce`): the nonce's two cells, the zero run, then the
capacity of the last absorbing row's permutation. -/
def aggNi : List V := permIns 1 [.n 71, .n 72] 74 [.n 65, .n 66, .n 67, .n 68, .n 69]

/-- The nonce permutation's outputs. -/
def aggNo : List V := (List.range 13).map fun i => .n (78 + i)

/-- The nonce's `fs_pack` (`fsNonceT`) and the zero run (`padRunT`), as atoms. -/
def aggNonceA : List Atom :=
  [.load (.n 70) (.n 6) 0, .copy (.n 71) (.n 70), .const (.n 72) (word 0 dsPowNonce),
    .const (.n 73) (word 1 0), .const (.n 74) (word 0 0), .const (.n 75) (word 0 0),
    .const (.n 76) (word 0 0), .const (.n 77) (word 0 0)]

theorem aggNonceA_eq : aggNonceA.map Stmt.atom = fsNonceT (.n 6) 0 70 ++ padRunT 73 := rfl

/-- **`aggregate_claims`' block, checked.** -/
noncomputable def aggOk : Bool :=
  let P := aggP
  let A := atomsIn P
  P.all Stmt.flat && decide ((fn% «aggregate_claims»).params = [.n 0, .n 1, .n 2, .n 3, .n 4,
      .n 5]) &&
  (List.range 5).all (fun i => A.any (isConstAt (.n (10 + i)) (seedLo.getD i (0, 0)).1
    (seedLo.getD i (0, 0)).2) && A.any (isLoadAt (.n (10 + i)) (.n 30) i)) &&
  packIn A (.n 0) 15 &&
  (List.range 3).all (fun j => A.any (isConstAt (.n (17 + 2 * j)) 0 0) &&
    packIn A (.n (17 + 2 * j)) (17 + 2 * j)) &&
  (List.range 4).all (fun j => A.any (isLoadAt (.n (15 + 2 * j)) (.n 30) (5 + 2 * j)) &&
    A.any (isLoadAt (.n (16 + 2 * j)) (.n 30) (6 + 2 * j))) &&
  guardOk P (.n 32) name% «aggregate_claims_loop0» (.n 33) (.n 0) [.n 30, .n 2, .n 8, .n 3, .n 9,
      .n 1] &&
  monoIs A (.n 39) (.n 30) (.n 0) 13 &&
  A.any (isKeccakAt aggKi aggKo false false) && rowInOk A (.n 39) aggKi &&
  allIn A aggNonceA &&
  A.any (isKeccakAt aggNi aggNo false false) &&
  hasCall P "grind_check__L2" [.n 79, .n 5] [] &&
  isMul A (.n 91) (.n 78) (.n 78) &&
  A.any (isConstAt (.n 96) 1 0) && A.any (isLoadAt (.n 96) (.n 95) 0) &&
  A.any (isConstAt (.n 97) 0 0) && A.any (isLoadAt (.n 97) (.n 95) 1) &&
  guardOk P (.n 99) name% «aggregate_claims_loop1» (.n 100) (.n 0) [.n 95, .n 8, .n 9, .n 91,
      .n 78] &&
  monoIs A (.n 102) (.n 95) (.n 0) 2 && A.any (isLoadAt (.n 103) (.n 102) 1) &&
  genMulOk A (.n 106) (.n 6) &&
  hasCall P "batch_sumcheck__L23" [.n 86, .n 87, .n 88, .n 89, .n 90, .n 106, .n 103, .n 104, .n 5]
    [.n 107, .n 108, .n 109, .n 110, .n 111, .n 112] &&
  (List.range 23).all (fun k => A.any (isConstAt (.n (114 + 3 * k)) 1 0) &&
    A.any (isLoadAt (.n (115 + 3 * k)) (.n 104) k) &&
    A.any (isAddAt (.n (116 + 3 * k)) (.n (114 + 3 * k)) (.n (115 + 3 * k))) &&
    A.any (isLoadAt (.n (116 + 3 * k)) (.n 113) k)) &&
  A.any (isConstAt (.n 186) 0 0) && A.any (isLoadAt (.n 186) (.n 185) 0) &&
  guardOk P (.n 188) name% «aggregate_claims_loop2» (.n 189) (.n 0) [.n 8, .n 9, .n 113, .n 95,
      .n 185, .n 78] &&
  isMul A (.n 190) (.n 185) (.n 0) && A.any (isLoadAt (.n 191) (.n 190) 0) &&
  isMul A (.n 192) (.n 7) (.n 191) && A.any (isAssertEqAt (.n 112) (.n 192)) &&
  (List.range 23).all (fun k => A.any (isLoadAt (.n (193 + k)) (.n 104) k) &&
    A.any (isLoadAt (.n (193 + k)) (.n 4) k)) &&
  A.any (isLoadAt (.n 7) (.n 4) 23)

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

end
end LeanVM.Guest.B1.Main
