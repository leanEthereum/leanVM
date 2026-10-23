/-
  LeanVM.Guest.B1.Tables.VerifyTablesBase

  `verify_tables`'s body as facts of a valuation: the statements before its `ret`, read by
  position.
-/

module

public import LeanVM.Guest.B1.Tables.GkrBase

/-!
# `verify_tables`'s body (TRIAGE #39)

`verify_tables` (G:1475-1824) is one function of 7900 statements. Its soundness reads each fact
it needs off the statements before the `ret` (`vtPre`), by position (`VtHolds.atom`, …): a
valuation satisfying them is what `verify_tables_holds` gives.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

theorem find_verify_tables : coreProgram.find? "verify_tables" = some Data.core11 :=
  Program.find?_of_indexOf? (j := 11) (by decide +kernel) rfl

/-- `verify_tables`'s statements before its `ret`. -/
noncomputable def vtPre : List Stmt := (Fn.body Data.core11).take 7899

theorem core11_body : Fn.body Data.core11 =
    vtPre ++ [.ret [.n 8171, .n 8172, .n 8175, .n 8176, .n 8177, .n 8178]] :=
  stmtsEqb_sound (by decide +kernel)

theorem vtPre_noRet : Stmt.noRetList vtPre = true := by decide +kernel

/-- The valuation `σ` satisfies every statement of `verify_tables` before its `ret`. -/
def VtHolds (rd : Reader) (σ : Val) : Prop :=
  ∃ kret : List E → Prop, Stmt.HoldsList (coreProgram.Rel rd) rd σ vtPre True kret

theorem verify_tables_holds {rd : Reader} {args rets : List E}
    (h : coreProgram.Rel rd "verify_tables" args rets) :
    ∃ σ : Val, [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 6), σ (.n 7), σ (.n 8), σ (.n 9), σ (.n 10), σ (.n 11), σ (.n 12), σ (.n 13), σ (.n 14), σ (.n 15), σ (.n 16), σ (.n 17), σ (.n 18)] = args ∧ VtHolds rd σ ∧
      [σ (.n 8171), σ (.n 8172), σ (.n 8175), σ (.n 8176), σ (.n 8177), σ (.n 8178)] = rets := by
  obtain ⟨σ, hp, hb, hr⟩ := rel_pre find_verify_tables core11_body vtPre_noRet h
  exact ⟨σ, hp, ⟨_, hb⟩, hr⟩

/-- One atom of the body holds. -/
theorem VtHolds.atom {rd : Reader} {σ : Val} (h : VtHolds rd σ) (n : ℕ) (a : Atom)
    (heq : stmtsEqb [.atom a] ((vtPre.drop n).take 1) = true) : a.Holds rd σ := by
  obtain ⟨k, h⟩ := h
  exact holds_atom vtPre_noRet h n a heq

/-- A run of statements of the body holds. -/
theorem VtHolds.slice {rd : Reader} {σ : Val} (h : VtHolds rd σ) (n : ℕ) (blk : List Stmt)
    (heq : stmtsEqb blk ((vtPre.drop n).take blk.length) = true) :
    ∃ kret : List E → Prop, Stmt.HoldsList (coreProgram.Rel rd) rd σ blk True kret := by
  obtain ⟨k, h⟩ := h
  exact ⟨k, holds_slice vtPre_noRet h n blk heq⟩

theorem vt_fs_chain {X : Digest} {p q r s w : E} (h : (p, q) = digestScalars X)
    (hb : ∃ cv, (p, q) = digestScalars cv ∧ (r, s) = digestScalars (obsCv cv w)) :
    (r, s) = digestScalars (obsCv X w) := by
  obtain ⟨cv, h1, h2⟩ := hb
  rw [digestScalars_injective (h1.symm.trans h)] at h2
  exact h2

/-- A conditional call of the body holds. -/
theorem VtHolds.callIf {rd : Reader} {σ : Val} (h : VtHolds rd σ) (n : ℕ) (c : V) (f : String)
    (args : List V) (heq : stmtsEqb [.callIf c f args] ((vtPre.drop n).take 1) = true) :
    σ c ≠ 0 → coreProgram.Rel rd f (args.map σ) [] := by
  obtain ⟨k, h⟩ := h
  exact holds_callIf vtPre_noRet h n c f args heq

/-- An `fs_next` of the body. -/
theorem VtHolds.fsNext {rd : Reader} {σ : Val} (h : VtHolds rd σ) (n : ℕ) (s0 s1 cur : V) (j b : ℕ)
    (heq : stmtsEqb (fsNextT s0 s1 cur j b) ((vtPre.drop n).take 13) = true) :
    LoadHolds rd (σ cur) j (σ (.n b)) ∧ ∃ cv, (σ s0, σ s1) = digestScalars cv ∧
      (σ (.n (b + 13)), σ (.n (b + 14))) = digestScalars (obsCv cv (σ (.n b))) := by
  obtain ⟨k, h⟩ := h
  exact holds_fsNextAt vtPre_noRet h n s0 s1 cur j b heq

/-- A `squeeze` of the body. -/
theorem VtHolds.squeeze {rd : Reader} {σ : Val} (h : VtHolds rd σ) (n : ℕ) (s0 s1 : V) (b : ℕ)
    (heq : stmtsEqb (squeezeT s0 s1 b) ((vtPre.drop n).take 14) = true) :
    ∃ cv, (σ s0, σ s1) = digestScalars cv ∧
      (σ (.n (b + 5)), σ (.n (b + 6))) = digestScalars (sqCv cv) ∧
      σ (.n (b + 13)) = challengeOf (sqCv cv) := by
  obtain ⟨k, h⟩ := h
  exact holds_squeezeAt vtPre_noRet h n s0 s1 b heq

end
end LeanVM.Guest.B1.VerifySub
