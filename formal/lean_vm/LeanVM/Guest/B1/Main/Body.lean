/-
  LeanVM.Guest.B1.Main.Body

  `main`'s body (G:4466-4642): its shape and its facts checked by evaluation.
-/

module

public import LeanVM.Guest.B1.Main.Loops

/-!
# `main`'s body

`Data.core0`'s body is a flat block (`mPre`: the counts, the coverage table's size and their
checks (`assert_gpow`, a load through each; range checks for the children and the direct DA check), the exponent
tables, the claim list digests, the byte table, the raw signatures' loops, `da_digests`), the
direct DA check behind `n_direct_da == g` (`mDa`: `da_verify`, then its claim's digest stored at
`own_da`) or the zero digest stored there (`mDaZ`), a flat block (`mMid`: the children's loop, the
final count, `da_pick` and its two checks), the leaf's deferred claim or the batching behind
`n_children == 1` (`mLeaf`, `mAgg`), and a flat block (`mPost`: the statement's digest against
the public input) (`core0_shape`). `preOk`, `daOk`, `daZOk`, `midOk`, `leafOk`, `postOk` check
every fact the proof reads, by evaluation.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Node

@[expose] public section

/-! ## The shape -/

noncomputable def mPre : List Stmt := (Fn.body Data.core0).take 615
noncomputable def mDa : List Stmt := match (Fn.body Data.core0).getD 615 default with
  | .ite _ z _ => z
  | _ => []
noncomputable def mDaZ : List Stmt := match (Fn.body Data.core0).getD 615 default with
  | .ite _ _ n => n
  | _ => []
noncomputable def mMid : List Stmt := ((Fn.body Data.core0).drop 616).take 39
noncomputable def mLeaf : List Stmt := match (Fn.body Data.core0).getD 655 default with
  | .ite _ z _ => z
  | _ => []
noncomputable def mAgg : List Stmt := match (Fn.body Data.core0).getD 655 default with
  | .ite _ _ n => n
  | _ => []
noncomputable def mPost : List Stmt := ((Fn.body Data.core0).drop 656).take 11

set_option maxRecDepth 100000 in
theorem core0_shape : Fn.body Data.core0 =
    mPre ++ [.ite (.n 368) mDa mDaZ] ++ mMid ++ [.ite (.n 418) mLeaf mAgg] ++ mPost ++ [.ret []] :=
  stmtsEqb_sound (by decide +kernel)

/-! ## The facts, by evaluation -/

/-- `a == b` is asserted. -/
def isAssertEqAt (a b : V) : Atom → Bool
  | .assertEq x y => decide (x = a) && decide (y = b)
  | _ => false

theorem assertEq_sound {rd : Reader} {σ : Val} {atoms : List Atom} {a b : V}
    (h : atoms.any (isAssertEqAt a b) = true) (hat : ∀ x ∈ atoms, x.Holds rd σ) : σ a = σ b := by
  obtain ⟨x, hp, hx⟩ := any_holds h hat
  cases x <;> simp only [isAssertEqAt, Bool.false_eq_true, Bool.and_eq_true,
    decide_eq_true_eq] at hp
  obtain ⟨rfl, rfl⟩ := hp
  exact e_add_eq_zero_iff.mp hx

/-- `x` is range-checked against `b` itself (`assert log x < log (b · g)`, the bound built
directly). -/
theorem rcDir_sound {rd : Reader} (hm : MemOk rd) {σ : Val} {atoms : List Atom} {x b : V}
    (h : decide (rcOf atoms x = some b) = true) (hat : ∀ a ∈ atoms, a.Holds rd σ) :
    ∃ e, σ x = gen ^ e ∧ BelowLog (σ b * gen) e := by
  obtain ⟨y, t1, t2, h1, h2, h3⟩ := rcOf_sound (of_decide_eq_true h) hat
  obtain ⟨e, e', he, he', hx, hk⟩ := rc_sound hm ⟨h1, h2, h3⟩
  exact ⟨e, hx, he, e', he', by rw [hk, ← pow_succ]⟩

/-- `lx_tags` (lean_ethereum.py:4553-4556): the `LX_N_TAGS = 51` constants `.n 304 ..< .n 355`,
the carried chain indices, passed whole to `__loop2` after its four parameters. -/
def lxTagsV : List V := (List.range 51).map fun j => .n (304 + j)

/-- The chain indices `lx_tags` holds, by slot: the carried indices below `LX_V = 58` (neither `0`
nor a power of two), in increasing order (`LX_TAG_SLOT`). -/
def lxTagVals : List ℕ := (List.range 58).filter Sig.lxTagCarried

/-- `lx_tags`' words. -/
def lxTagWords : List E := lxTagVals.map fun i => word i 0

noncomputable def preOk : Bool :=
  let P := mPre
  let A := atomsIn mPre
  P.all Stmt.flat &&
  ((List.range 6).all fun v => isTouch A (.n (8 + v)) (.n v)) &&
  rcConstOk A (.n 6) 65536 && rcConstOk A (.n 7) 2 &&
  isTouch A (.n 25) (.n 24) &&
  isMul A (.n 22) (.n 0) (.n 1) && isMul A (.n 23) (.n 3) (.n 4) &&
  isMul A (.n 24) (.n 22) (.n 23) &&
  hasCall P "exponent_tables" [] [.n 28] &&
  hasCall P "claim_list_digest" [.n 31, .n 0] [.n 35, .n 36] &&
  hasCall P "claim_list_digest" [.n 34, .n 3] [.n 37, .n 38] &&
  ((List.range 256).all fun v => A.any (isConstAt (.n (48 + v)) v 0) &&
    A.any (isLoadAt (.n (48 + v)) (.n 47) v)) &&
  isMul A (.n 46) (.n 45) (.n 22) &&
  guardOk P (.n 356) "__loop2" (.n 357) (.n 2) ([.n 22, .n 45, .n 31] ++ lxTagsV) &&
  ((List.range 58).all fun i => !Sig.lxTagCarried i ||
    A.any (isConstAt (.n (304 + (Sig.lxTagSlot i - 1))) i 0)) &&
  guardOk P (.n 359) "__loop3" (.n 360) (.n 5) [.n 23, .n 46, .n 2, .n 34, .n 47] &&
  isMul A (.n 365) (.n 6) (.n 6) && isMul A (.n 366) (.n 364) (.n 365) &&
  A.any (isAddAt (.n 368) (.n 7) (.n 367)) && A.any (isConstAt (.n 367) 2 0)

noncomputable def daOk : Bool :=
  let D := mDa
  D.all Stmt.flat &&
  hasCall D "da_verify" [.n 28] [.n 369, .n 370, .n 371] &&
  (atomsIn D).any (isConstAt (.n 373) 0 0) &&
  pairHashOk (atomsIn D) (.n 369) (.n 370) (.n 371) (.n 373) (.n 366)

noncomputable def daZOk : Bool :=
  let A := atomsIn mDaZ
  mDaZ.all Stmt.flat &&
  A.any (isConstAt (.n 380) 0 0) && isLoad A (.n 380) (.n 366) 0 &&
  A.any (isConstAt (.n 381) 0 0) && isLoad A (.n 381) (.n 366) 1

noncomputable def midOk : Bool :=
  let M := mMid
  let A := atomsIn mMid
  M.all Stmt.flat &&
  isMul A (.n 399) (.n 2) (.n 5) && isLoad A (.n 399) (.n 398) 0 &&
  guardOk M (.n 401) "__loop4" (.n 402) (.n 6) [.n 398, .n 31, .n 45, .n 22, .n 34, .n 46,
    .n 23, .n 395, .n 364, .n 26, .n 27, .n 383, .n 28, .n 389] &&
  isMul A (.n 403) (.n 398) (.n 6) && isLoad A (.n 404) (.n 403) 0 &&
  A.any (isAssertEqAt (.n 404) (.n 24)) &&
  decide (rcOf A (.n 405) = some (.n 6)) &&
  A.any (isAddAt (.n 409) (.n 405) (.n 6)) && A.any (isAddAt (.n 411) (.n 7) (.n 410)) &&
  A.any (isConstAt (.n 410) 1 0) && isMul A (.n 412) (.n 409) (.n 411) &&
  A.any (isConstAt (.n 413) 0 0) && A.any (isAssertEqAt (.n 412) (.n 413)) &&
  isMul A (.n 414) (.n 405) (.n 405) && isMul A (.n 415) (.n 364) (.n 414) &&
  A.any (isAddAt (.n 418) (.n 6) (.n 417)) && A.any (isConstAt (.n 417) 1 0)

noncomputable def leafOk : Bool :=
  mLeaf.all Stmt.flat &&
  ((List.range 23).all fun k => (atomsIn mLeaf).any (isConstAt (.n (420 + k)) 0 0) &&
    isLoad (atomsIn mLeaf) (.n (420 + k)) (.n 416) k) &&
  isLoad (atomsIn mLeaf) (.n 419) (.n 416) 23 &&
  mAgg.all Stmt.flat &&
  (atomsIn mAgg).any (isConstAt (.n 443) 133823759239872512 0) &&
  isMul (atomsIn mAgg) (.n 444) (.n 28) (.n 443) &&
  hasCall mAgg "aggregate_claims" [.n 6, .n 383, .n 389, .n 395, .n 416, .n 444] []

noncomputable def postOk : Bool :=
  let A := atomsIn mPost
  mPost.all Stmt.flat &&
  isLoad A (.n 445) (.n 415) 0 && isLoad A (.n 446) (.n 415) 1 &&
  hasCall mPost "statement_digest" [.n 26, .n 27, .n 35, .n 36, .n 37, .n 38, .n 445, .n 446, .n 416]
    [.n 447, .n 448] &&
  A.any (isConstAt (.n 449) 1 0) && isLoad A (.n 450) (.n 449) 0 &&
  A.any (isAssertEqAt (.n 450) (.n 447)) &&
  A.any (isConstAt (.n 451) 1 0) && A.any (isConstAt (.n 452) 2 0) &&
  isMul A (.n 453) (.n 451) (.n 452) && isLoad A (.n 454) (.n 453) 0 &&
  A.any (isAssertEqAt (.n 454) (.n 448))

set_option maxRecDepth 100000 in
theorem pre_ok : preOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem da_ok : daOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem daZ_ok : daZOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem mid_ok : midOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem leaf_ok : leafOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem post_ok : postOk = true := by decide +kernel

end
end LeanVM.Guest.B1.Main
