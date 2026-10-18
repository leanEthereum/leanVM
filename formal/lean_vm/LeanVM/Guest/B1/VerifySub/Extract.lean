/-
  LeanVM.Guest.B1.VerifySub.Extract

  `verify_sub`'s body as facts: its relation is a valuation satisfying every statement before its
  final `ret`, and any run of them, found at its position by kernel evaluation, holds.
-/

module

public import LeanVM.Guest.B1.VerifySub.Interface

/-!
# Reading `verify_sub`'s body

`verify_sub`'s body (`Data.core15`, 2137 statements) is straight-line: atoms, calls, a guarded
loop call, one fused dispatch, then `ret []`. Its relation is a valuation satisfying every
statement of `vsPre`, the statements before the `ret` (`verify_sub_holds`). A run of statements
`blk` at position `n` of `vsPre`, checked by `decide +kernel` on `stmtsEqb`, then holds on its own
(`VsHolds.slice`), and each fact the proof needs is read off a run.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

theorem find_verify_sub : coreProgram.find? "verify_sub" = some Data.core15 :=
  Program.find?_of_indexOf? (j := 15) (by decide +kernel) rfl

/-- `verify_sub`'s statements before its final `ret []`. -/
noncomputable def vsPre : List Stmt := (Fn.body Data.core15).take 2136

theorem core15_body : Fn.body Data.core15 = vsPre ++ [.ret []] :=
  stmtsEqb_sound (by decide +kernel)

theorem vsPre_noRet : Stmt.noRetList vsPre = true := by decide +kernel

theorem core15_params : Fn.params Data.core15 = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6] := rfl

/-- The valuation `σ` satisfies every statement of `verify_sub` before its `ret`. -/
def VsHolds (rd : Reader) (σ : Val) : Prop :=
  Stmt.HoldsList (coreProgram.Rel rd) rd σ vsPre True fun rs => rs = []

theorem verify_sub_holds {rd : Reader} {args : List E}
    (h : coreProgram.Rel rd "verify_sub" args []) :
    ∃ σ : Val, [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 6)] = args ∧
      VsHolds rd σ := by
  rw [rel_iff_sem find_verify_sub, core15_body, core15_params] at h
  obtain ⟨σ, hp, hb⟩ := h
  rw [holdsList_append, holdsList_noRet _ vsPre_noRet] at hb
  exact ⟨σ, hp, hb.1⟩

theorem noRetList_append (a b : List Stmt) :
    Stmt.noRetList (a ++ b) = (Stmt.noRetList a && Stmt.noRetList b) := by
  induction a with
  | nil => simp [Stmt.noRetList]
  | cons s a ih => simp [Stmt.noRetList, ih, Bool.and_assoc]

/-- **A run of statements of the body holds**: `blk`, equal to the statements at position `n`. -/
theorem VsHolds.slice {rd : Reader} {σ : Val} (h : VsHolds rd σ) (n : ℕ) (blk : List Stmt)
    (heq : stmtsEqb blk ((vsPre.drop n).take blk.length) = true) :
    Stmt.HoldsList (coreProgram.Rel rd) rd σ blk True fun rs => rs = [] := by
  have hsplit : vsPre = vsPre.take n ++ (((vsPre.drop n).take blk.length) ++
      (vsPre.drop n).drop blk.length) := by simp
  have hnr := vsPre_noRet
  unfold VsHolds at h
  rw [hsplit] at h hnr
  rw [noRetList_append, noRetList_append, Bool.and_eq_true, Bool.and_eq_true] at hnr
  rw [holdsList_append, holdsList_noRet _ hnr.1, holdsList_append,
    holdsList_noRet _ hnr.2.1] at h
  rw [stmtsEqb_sound heq]
  exact h.2.1

/-- One atom of the body holds. -/
theorem VsHolds.atom {rd : Reader} {σ : Val} (h : VsHolds rd σ) (n : ℕ) (a : Atom)
    (heq : stmtsEqb [.atom a] ((vsPre.drop n).take 1) = true) : a.Holds rd σ := by
  have := h.slice n [.atom a] heq
  simpa [Stmt.HoldsList, Stmt.Holds] using this

/-- One call of the body holds. -/
theorem VsHolds.call {rd : Reader} {σ : Val} (h : VsHolds rd σ) (n : ℕ) (f : String)
    (args rets : List V) (heq : stmtsEqb [.call f args rets] ((vsPre.drop n).take 1) = true) :
    coreProgram.Rel rd f (args.map σ) (rets.map σ) := by
  have := h.slice n [.call f args rets] heq
  simpa [Stmt.HoldsList, Stmt.Holds] using this

/-! ## Prefixes of the body -/

mutual
theorem holds_kret : ∀ (s : Stmt), Stmt.noRet s = true → ∀ {rd : Reader} {σ : Val} {C : CallRel}
    (next : Prop) (k k' : List E → Prop), Stmt.Holds C rd σ s next k → Stmt.Holds C rd σ s next k'
  | .atom _, _, _, _, _, _, _, _, h => h
  | .ite _ z n, hr, _, _, _, next, k, k', h => by
      simp only [Stmt.noRet, Bool.and_eq_true] at hr
      exact ⟨h.1, fun hc => holdsList_kret z hr.1 next k k' (h.2.1 hc),
        fun hc => holdsList_kret n hr.2 next k k' (h.2.2 hc)⟩
  | .match_ x arms, hr, _, _, _, next, k, k', h => holdsArms_kret x arms hr 0 next k k' h
  | .call .., _, _, _, _, _, _, _, h => h
  | .callIf .., _, _, _, _, _, _, _, h => h
  | .dispatch .., _, _, _, _, _, _, _, h => h
  | .ret _, hr, _, _, _, _, _, _, _ => by simp [Stmt.noRet] at hr

theorem holdsList_kret : ∀ (ss : List Stmt), Stmt.noRetList ss = true → ∀ {rd : Reader}
    {σ : Val} {C : CallRel} (next : Prop) (k k' : List E → Prop),
    Stmt.HoldsList C rd σ ss next k → Stmt.HoldsList C rd σ ss next k'
  | [], _, _, _, _, _, _, _, h => h
  | s :: ss, hr, _, _, _, next, k, k', h => by
      simp only [Stmt.noRetList, Bool.and_eq_true] at hr
      simp only [Stmt.HoldsList] at h ⊢
      refine holds_kret s hr.1 _ k k' ?_
      rw [holds_noRet s hr.1] at h ⊢
      exact ⟨h.1, holdsList_kret ss hr.2 next k k' h.2⟩

theorem holdsArms_kret (x : V) : ∀ (arms : List (List Stmt)), Stmt.noRetArms arms = true →
    ∀ {rd : Reader} {σ : Val} {C : CallRel} (j : ℕ) (next : Prop) (k k' : List E → Prop),
    Stmt.HoldsArms C rd σ x j arms next k → Stmt.HoldsArms C rd σ x j arms next k'
  | [], _, _, _, _, _, _, _, _, h => h
  | a :: as, hr, _, _, _, j, next, k, k', h => by
      simp only [Stmt.noRetArms, Bool.and_eq_true] at hr
      simp only [Stmt.HoldsArms] at h ⊢
      rcases h with ⟨hx, ha⟩ | h
      · exact Or.inl ⟨hx, holdsList_kret a hr.1 next k k' ha⟩
      · exact Or.inr (holdsArms_kret x as hr.2 (j + 1) next k k' h)
end

theorem noRetList_take : ∀ (n : ℕ) (ss : List Stmt), Stmt.noRetList ss = true →
    Stmt.noRetList (ss.take n) = true
  | 0, _, _ => rfl
  | _ + 1, [], _ => rfl
  | n + 1, s :: ss, h => by
    simp only [Stmt.noRetList, Bool.and_eq_true, List.take_succ_cons] at h ⊢
    exact ⟨h.1, noRetList_take n ss h.2⟩

/-- The valuation `σ` satisfies the first `N` statements of `verify_sub`'s body. -/
def VsHoldsTo (N : ℕ) (rd : Reader) (σ : Val) : Prop :=
  Stmt.HoldsList (coreProgram.Rel rd) rd σ (vsPre.take N) True fun _ => True

theorem VsHoldsTo.mono {N M : ℕ} {rd : Reader} {σ : Val} (h : VsHoldsTo N rd σ) (hM : M ≤ N) :
    VsHoldsTo M rd σ := by
  have hs : vsPre.take N = vsPre.take M ++ (vsPre.take N).drop M := by
    have := List.take_append_drop M (vsPre.take N)
    rw [List.take_take, Nat.min_eq_left hM] at this
    exact this.symm
  unfold VsHoldsTo at h
  rw [hs, holdsList_append, holdsList_noRet _ (noRetList_take M _ vsPre_noRet)] at h
  exact h.1

theorem VsHolds.to {rd : Reader} {σ : Val} (h : VsHolds rd σ) (N : ℕ) : VsHoldsTo N rd σ := by
  have hs : vsPre = vsPre.take N ++ vsPre.drop N := (List.take_append_drop _ _).symm
  have hnr := vsPre_noRet
  unfold VsHolds at h
  rw [hs, holdsList_append, holdsList_noRet _ (noRetList_take N _ hnr)] at h
  exact holdsList_kret _ (noRetList_take N _ hnr) _ _ _ h.1

/-- **A run of statements of a prefix holds**. -/
theorem VsHoldsTo.slice {N : ℕ} {rd : Reader} {σ : Val} (h : VsHoldsTo N rd σ) (n : ℕ)
    (blk : List Stmt) (hb : n + blk.length ≤ N)
    (heq : stmtsEqb blk ((vsPre.drop n).take blk.length) = true) :
    Stmt.HoldsList (coreProgram.Rel rd) rd σ blk True fun _ => True := by
  have h' := h.mono hb
  have hsplit : vsPre.take (n + blk.length) =
      vsPre.take n ++ (vsPre.drop n).take blk.length := by
    rw [List.take_add]
  have hnr := noRetList_take (n + blk.length) _ vsPre_noRet
  unfold VsHoldsTo at h'
  rw [hsplit] at h' hnr
  rw [noRetList_append, Bool.and_eq_true] at hnr
  rw [holdsList_append, holdsList_noRet _ hnr.1] at h'
  rw [stmtsEqb_sound heq]
  exact h'.2

theorem VsHoldsTo.atom {N : ℕ} {rd : Reader} {σ : Val} (h : VsHoldsTo N rd σ) (n : ℕ) (a : Atom)
    (hb : n + 1 ≤ N) (heq : stmtsEqb [.atom a] ((vsPre.drop n).take 1) = true) : a.Holds rd σ := by
  have := h.slice n [.atom a] hb heq
  simpa [Stmt.HoldsList, Stmt.Holds] using this

theorem VsHoldsTo.call {N : ℕ} {rd : Reader} {σ : Val} (h : VsHoldsTo N rd σ) (n : ℕ) (f : String)
    (args rets : List V) (hb : n + 1 ≤ N)
    (heq : stmtsEqb [.call f args rets] ((vsPre.drop n).take 1) = true) :
    coreProgram.Rel rd f (args.map σ) (rets.map σ) := by
  have := h.slice n [.call f args rets] hb heq
  simpa [Stmt.HoldsList, Stmt.Holds] using this

/-- `slice` with the bound checked with the statements. -/
theorem VsHoldsTo.slice' {N : ℕ} {rd : Reader} {σ : Val} (h : VsHoldsTo N rd σ) (n : ℕ)
    (blk : List Stmt)
    (heq : (decide (n + blk.length ≤ N) && stmtsEqb blk ((vsPre.drop n).take blk.length)) = true) :
    Stmt.HoldsList (coreProgram.Rel rd) rd σ blk True fun _ => True := by
  rw [Bool.and_eq_true, decide_eq_true_eq] at heq
  exact h.slice n blk heq.1 heq.2

theorem VsHoldsTo.atom' {N : ℕ} {rd : Reader} {σ : Val} (h : VsHoldsTo N rd σ) (n : ℕ) (a : Atom)
    (heq : (decide (n + 1 ≤ N) && stmtsEqb [.atom a] ((vsPre.drop n).take 1)) = true) :
    a.Holds rd σ := by
  rw [Bool.and_eq_true, decide_eq_true_eq] at heq
  exact h.atom n a heq.1 heq.2

theorem VsHoldsTo.call' {N : ℕ} {rd : Reader} {σ : Val} (h : VsHoldsTo N rd σ) (n : ℕ) (f : String)
    (args rets : List V)
    (heq : (decide (n + 1 ≤ N) && stmtsEqb [.call f args rets] ((vsPre.drop n).take 1)) = true) :
    coreProgram.Rel rd f (args.map σ) (rets.map σ) := by
  rw [Bool.and_eq_true, decide_eq_true_eq] at heq
  exact h.call n f args rets heq.1 heq.2

end
end LeanVM.Guest.B1.VerifySub
