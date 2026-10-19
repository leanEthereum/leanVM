/-
  LeanVM.Guest.B1.Sig.Placed

  The signature verifiers' bodies, syntactically: nothing placed, the only loads the claim's four
  words at the argument, and the only calls the forest keys.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsData
public import LeanVM.Guest.B1.Sig.SphincsKey
public import LeanVM.Guest.B1.Sig.XmssData
public import LeanVM.Guest.Memory.Placed
public import LeanVM.Guest.Memory.Regions

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- A load of the argument `n0` at an offset below 4. -/
def claimLoad (a : Atom) : Bool :=
  match a with
  | .load _ p off => decide (p = .n 0) && decide (off < 4)
  | _ => true

/-- No load at all. -/
def noLoad (a : Atom) : Bool :=
  match a with
  | .load .. => false
  | _ => true

mutual
/-- A statement places nothing, its loads pass `lok`, its calls are dispatches over `D`. -/
def Stmt.sigOk (lok : Atom → Bool) (D : List String) : Stmt → Bool
  | .atom a => atomUnplaced a && lok a
  | .ite _ z n => Stmt.sigOkList lok D z && Stmt.sigOkList lok D n
  | .match_ _ arms => Stmt.sigOkArms lok D arms
  | .call .. => false
  | .callIf .. => false
  | .dispatch _ fs _ _ => decide (fs = D)
  | .ret _ => true

def Stmt.sigOkList (lok : Atom → Bool) (D : List String) : List Stmt → Bool
  | [] => true
  | s :: ss => Stmt.sigOk lok D s && Stmt.sigOkList lok D ss

def Stmt.sigOkArms (lok : Atom → Bool) (D : List String) : List (List Stmt) → Bool
  | [] => true
  | a :: as => Stmt.sigOkList lok D a && Stmt.sigOkArms lok D as
end

theorem xBody_sigOk : Stmt.sigOkList claimLoad [] Data.core16.body = true := by decide +kernel

theorem sBody_sigOk : Stmt.sigOkList claimLoad fkNames Data.core17.body = true := by decide +kernel

theorem sigOkList_eq_all (lok : Atom → Bool) (D : List String) :
    ∀ ss : List Stmt, Stmt.sigOkList lok D ss = ss.all (Stmt.sigOk lok D)
  | [] => rfl
  | s :: ss => by simp only [Stmt.sigOkList, List.all_cons, sigOkList_eq_all lok D ss]

theorem fkChains_sigOk (t : Nat) : ∀ m i b, (fkChains t m i b).1.all (Stmt.sigOk noLoad []) = true
  | 0, _, _ => rfl
  | m + 1, i, b => by
      simp only [fkChains, List.all_append, fkChains_sigOk t m, Bool.and_true]
      simp [fkChain, hintW, cst, addS, ivs, b2s, Stmt.sigOk, atomUnplaced, noLoad]

theorem fkBody_sigOk (t : Nat) : Stmt.sigOkList noLoad [] (fkBody t) = true := by
  rw [sigOkList_eq_all]
  simp only [fkBody, List.all_append, fkChains_sigOk, Bool.true_and]
  simp [cst, addS, ivs, b2s, Stmt.sigOk, atomUnplaced, noLoad]

/-! ## Walks -/

/-- An event of a walk: its load passes `lok`, its call is one of `D`. -/
def EvSigOk (lok : Atom → Bool) (D : List String) : Ev → Prop
  | .atom a => lok a = true
  | .call f _ _ => f ∈ D
  | .skip f _ => f ∈ D
  | .inK _ => True

section Walk

variable {lok : Atom → Bool} {D : List String} {σ : Val}

theorem pick_sigOk {x : V} {args rets : List V} :
    ∀ (gs : List String) (j : ℕ), (∀ f ∈ gs, f ∈ D) → (pick σ x args rets j gs).All (EvSigOk lok D)
  | [], _, _ => trivial
  | g :: gs, j, h => by
      unfold pick
      split_ifs
      · intro e he
        rw [List.mem_singleton] at he
        subst he
        exact h g (List.mem_cons_self ..)
      · exact pick_sigOk gs (j + 1) fun f hf => h f (List.mem_cons_of_mem _ hf)

mutual
theorem walk1_sigOk : ∀ (s : Stmt), Stmt.sigOk lok D s = true → (walk1 σ s).All (EvSigOk lok D)
  | .atom _, h => by
      intro e he
      rw [List.mem_singleton] at he
      subst he
      simp only [Stmt.sigOk, Bool.and_eq_true] at h
      exact h.2
  | .ite c z n, h => by
      simp only [Stmt.sigOk, Bool.and_eq_true] at h
      rw [walk1]
      refine Out.all_pre (fun e he => by rw [List.mem_singleton] at he; subst he; trivial) ?_
      split_ifs
      · exact walk_sigOk z h.1
      · exact walk_sigOk n h.2
  | .match_ x arms, h => walkArms_sigOk x arms 0 h
  | .call .., h => by simp [Stmt.sigOk] at h
  | .callIf .., h => by simp [Stmt.sigOk] at h
  | .dispatch x fs args rets, h => by
      simp only [Stmt.sigOk, decide_eq_true_eq] at h
      exact pick_sigOk fs 0 fun f hf => h ▸ hf
  | .ret _, _ => fun _ he => (List.not_mem_nil he).elim

theorem walk_sigOk : ∀ (ss : List Stmt), Stmt.sigOkList lok D ss = true → (walk σ ss).All (EvSigOk lok D)
  | [], _ => fun _ he => (List.not_mem_nil he).elim
  | s :: ss, h => by
      simp only [Stmt.sigOkList, Bool.and_eq_true] at h
      rw [walk]
      exact Out.all_seq (walk_sigOk ss h.2) (walk1_sigOk s h.1)

theorem walkArms_sigOk (x : V) : ∀ (arms : List (List Stmt)) (j : ℕ), Stmt.sigOkArms lok D arms = true →
    (walkArms σ x j arms).All (EvSigOk lok D)
  | [], _, _ => trivial
  | a :: as, j, h => by
      simp only [Stmt.sigOkArms, Bool.and_eq_true] at h
      unfold walkArms
      split_ifs
      · exact walk_sigOk a h.1
      · exact walkArms_sigOk x as (j + 1) h.2
end

end Walk

/-! ## Purity -/

mutual
theorem sigOk_pure {lok : Atom → Bool} {D S : List String} (hS : ∀ f ∈ D, f ∈ S) :
    ∀ (s : Stmt), Stmt.sigOk lok D s = true → Stmt.pure S s = true
  | .atom _, h => by
      simp only [Stmt.sigOk, Bool.and_eq_true] at h
      exact h.1
  | .ite _ z n, h => by
      simp only [Stmt.sigOk, Bool.and_eq_true] at h
      simp only [Stmt.pure, Bool.and_eq_true]
      exact ⟨sigOkList_pure hS z h.1, sigOkList_pure hS n h.2⟩
  | .match_ _ arms, h => sigOkArms_pure hS arms h
  | .call .., h => by simp [Stmt.sigOk] at h
  | .callIf .., h => by simp [Stmt.sigOk] at h
  | .dispatch _ fs _ _, h => by
      simp only [Stmt.sigOk, decide_eq_true_eq] at h
      subst h
      simp only [Stmt.pure, List.all_eq_true, decide_eq_true_eq]
      exact hS
  | .ret _, _ => rfl

theorem sigOkList_pure {lok : Atom → Bool} {D S : List String} (hS : ∀ f ∈ D, f ∈ S) :
    ∀ (ss : List Stmt), Stmt.sigOkList lok D ss = true → Stmt.pureList S ss = true
  | [], _ => rfl
  | s :: ss, h => by
      simp only [Stmt.sigOkList, Bool.and_eq_true] at h
      simp only [Stmt.pureList, Bool.and_eq_true]
      exact ⟨sigOk_pure hS s h.1, sigOkList_pure hS ss h.2⟩

theorem sigOkArms_pure {lok : Atom → Bool} {D S : List String} (hS : ∀ f ∈ D, f ∈ S) :
    ∀ (arms : List (List Stmt)), Stmt.sigOkArms lok D arms = true → Stmt.pureArms S arms = true
  | [], _ => rfl
  | a :: as, h => by
      simp only [Stmt.sigOkArms, Bool.and_eq_true] at h
      simp only [Stmt.pureArms, Bool.and_eq_true]
      exact ⟨sigOkList_pure hS a h.1, sigOkArms_pure hS as h.2⟩
end

set_option maxRecDepth 10000 in
theorem mem_fkNames {f : String} (hf : f ∈ fkNames) : ∃ t < 256, f = fkNames.getD t "" := by
  obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.mp hf
  exact ⟨t, by have : fkNames.length = 256 := rfl; omega, by rw [List.getD_eq_getElem]⟩

theorem xmss_pure : coreProgram.PureIn ["verify_lean_xmss"] := by
  intro g hg fn hf
  rw [List.mem_singleton] at hg
  subst hg
  rw [find_verify_lean_xmss, Option.some.injEq] at hf
  subst hf
  rw [← xBody_eq]
  exact sigOkList_pure (fun f hf => absurd hf List.not_mem_nil) _ xBody_sigOk

theorem sphincs_pure : coreProgram.PureIn ("verify_sig_lean_sphincs" :: fkNames) := by
  intro g hg fn hf
  have hS : ∀ f ∈ fkNames, f ∈ "verify_sig_lean_sphincs" :: fkNames := fun f hf => List.mem_cons_of_mem _ hf
  rcases List.mem_cons.mp hg with rfl | hg
  · rw [find_verify_sig_lean_sphincs, Option.some.injEq] at hf
    subst hf
    rw [← sBody_eq]
    exact sigOkList_pure hS _ sBody_sigOk
  · obtain ⟨t, ht, rfl⟩ := mem_fkNames hg
    rw [find_fk ht, Option.some.injEq] at hf
    subst hf
    exact sigOkList_pure (fun f hf => absurd hf List.not_mem_nil) _ (fkBody_sigOk t)

end
end LeanVM.Guest.B1.Sig
