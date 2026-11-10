/-
  LeanVM.Guest.B1.Main.Body

  `main`'s body (G:4491-4667): its shape and its facts checked by evaluation.
-/

module

public import LeanVM.Guest.B1.Main.Loops

/-!
# `main`'s body

`Data.core0`'s body is a flat block (`mPre`: the counts and their range checks, the exponent
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

noncomputable def mPre : List Stmt := (Fn.body Data.core0).take 622
noncomputable def mDa : List Stmt := match (Fn.body Data.core0).getD 622 default with
  | .ite _ z _ => z
  | _ => []
noncomputable def mDaZ : List Stmt := match (Fn.body Data.core0).getD 622 default with
  | .ite _ _ n => n
  | _ => []
noncomputable def mMid : List Stmt := ((Fn.body Data.core0).drop 623).take 39
noncomputable def mLeaf : List Stmt := match (Fn.body Data.core0).getD 662 default with
  | .ite _ z _ => z
  | _ => []
noncomputable def mAgg : List Stmt := match (Fn.body Data.core0).getD 662 default with
  | .ite _ _ n => n
  | _ => []
noncomputable def mPost : List Stmt := ((Fn.body Data.core0).drop 663).take 11

set_option maxRecDepth 100000 in
theorem core0_shape : Fn.body Data.core0 =
    mPre ++ [.ite (.n 389) mDa mDaZ] ++ mMid ++ [.ite (.n 440) mLeaf mAgg] ++ mPost ++ [.ret []] :=
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

/-- `lx_tags` (lean_ethereum.py:4578-4581): the `LX_N_TAGS = 51` constants `.n 325 ..< .n 376`,
the carried chain indices, passed whole to `__loop2` after its four parameters. -/
def lxTagsV : List V := (List.range 51).map fun j => .n (325 + j)

/-- The chain indices `lx_tags` holds, by slot: the carried indices below `LX_V = 58` (neither `0`
nor a power of two), in increasing order (`LX_TAG_SLOT`). -/
def lxTagVals : List ℕ := (List.range 58).filter Sig.lxTagCarried

/-- `lx_tags`' words. -/
def lxTagWords : List E := lxTagVals.map fun i => word i 0

noncomputable def preOk : Bool :=
  let P := mPre
  let A := atomsIn mPre
  P.all Stmt.flat &&
  ((List.range 6).all fun v => rcConstOk A (.n v) 9272771591053052074) &&
  rcConstOk A (.n 6) 65536 && rcConstOk A (.n 7) 2 &&
  rcConstOk A (.n 42) 9272771591053052074 &&
  isMul A (.n 40) (.n 0) (.n 1) && isMul A (.n 41) (.n 3) (.n 4) &&
  isMul A (.n 42) (.n 40) (.n 41) &&
  hasCall P "exponent_tables" [] [.n 49] &&
  hasCall P "claim_list_digest" [.n 52, .n 0] [.n 56, .n 57] &&
  hasCall P "claim_list_digest" [.n 55, .n 3] [.n 58, .n 59] &&
  ((List.range 256).all fun v => A.any (isConstAt (.n (69 + v)) v 0) &&
    A.any (isLoadAt (.n (69 + v)) (.n 68) v)) &&
  isMul A (.n 67) (.n 66) (.n 40) &&
  guardOk P (.n 377) "__loop2" (.n 378) (.n 2) ([.n 40, .n 66, .n 52] ++ lxTagsV) &&
  ((List.range 58).all fun i => !Sig.lxTagCarried i ||
    A.any (isConstAt (.n (325 + (Sig.lxTagSlot i - 1))) i 0)) &&
  guardOk P (.n 380) "__loop3" (.n 381) (.n 5) [.n 41, .n 67, .n 2, .n 55, .n 68] &&
  isMul A (.n 386) (.n 6) (.n 6) && isMul A (.n 387) (.n 385) (.n 386) &&
  A.any (isAddAt (.n 389) (.n 7) (.n 388)) && A.any (isConstAt (.n 388) 2 0)

noncomputable def daOk : Bool :=
  let D := mDa
  D.all Stmt.flat &&
  hasCall D "da_verify" [.n 49] [.n 390, .n 391, .n 392, .n 393] &&
  pairHashOk (atomsIn D) (.n 390) (.n 391) (.n 392) (.n 393) (.n 387)

noncomputable def daZOk : Bool :=
  let A := atomsIn mDaZ
  mDaZ.all Stmt.flat &&
  A.any (isConstAt (.n 402) 0 0) && isLoad A (.n 402) (.n 387) 0 &&
  A.any (isConstAt (.n 403) 0 0) && isLoad A (.n 403) (.n 387) 1

noncomputable def midOk : Bool :=
  let M := mMid
  let A := atomsIn mMid
  M.all Stmt.flat &&
  isMul A (.n 421) (.n 2) (.n 5) && isLoad A (.n 421) (.n 420) 0 &&
  guardOk M (.n 423) "__loop4" (.n 424) (.n 6) [.n 420, .n 52, .n 66, .n 40, .n 55, .n 67,
    .n 41, .n 417, .n 385, .n 47, .n 48, .n 405, .n 49, .n 411] &&
  isMul A (.n 425) (.n 420) (.n 6) && isLoad A (.n 426) (.n 425) 0 &&
  A.any (isAssertEqAt (.n 426) (.n 42)) &&
  decide (rcOf A (.n 427) = some (.n 6)) &&
  A.any (isAddAt (.n 431) (.n 427) (.n 6)) && A.any (isAddAt (.n 433) (.n 7) (.n 432)) &&
  A.any (isConstAt (.n 432) 1 0) && isMul A (.n 434) (.n 431) (.n 433) &&
  A.any (isConstAt (.n 435) 0 0) && A.any (isAssertEqAt (.n 434) (.n 435)) &&
  isMul A (.n 436) (.n 427) (.n 427) && isMul A (.n 437) (.n 385) (.n 436) &&
  A.any (isAddAt (.n 440) (.n 6) (.n 439)) && A.any (isConstAt (.n 439) 1 0)

noncomputable def leafOk : Bool :=
  mLeaf.all Stmt.flat &&
  ((List.range 23).all fun k => (atomsIn mLeaf).any (isConstAt (.n (442 + k)) 0 0) &&
    isLoad (atomsIn mLeaf) (.n (442 + k)) (.n 438) k) &&
  isLoad (atomsIn mLeaf) (.n 441) (.n 438) 23 &&
  mAgg.all Stmt.flat &&
  hasCall mAgg "aggregate_claims" [.n 6, .n 405, .n 411, .n 417, .n 438] []

noncomputable def postOk : Bool :=
  let A := atomsIn mPost
  mPost.all Stmt.flat &&
  isLoad A (.n 465) (.n 437) 0 && isLoad A (.n 466) (.n 437) 1 &&
  hasCall mPost "statement_digest" [.n 47, .n 48, .n 56, .n 57, .n 58, .n 59, .n 465, .n 466, .n 438]
    [.n 467, .n 468] &&
  A.any (isConstAt (.n 469) 1 0) && isLoad A (.n 470) (.n 469) 0 &&
  A.any (isAssertEqAt (.n 470) (.n 467)) &&
  A.any (isConstAt (.n 471) 1 0) && A.any (isConstAt (.n 472) 2 0) &&
  isMul A (.n 473) (.n 471) (.n 472) && isLoad A (.n 474) (.n 473) 0 &&
  A.any (isAssertEqAt (.n 474) (.n 468))

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
