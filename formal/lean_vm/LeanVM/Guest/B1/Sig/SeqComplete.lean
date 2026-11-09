/-
  LeanVM.Guest.B1.Sig.SeqComplete

  Blocks of constants, sums, products and copies, each defining the next fresh value from values
  numbered below, complete.
-/

module

public import LeanVM.Guest.B1.Sig.CompleteBasic

/-!
# Sequential blocks

`SeqOK b ss b'`: each atom of `ss` is a constant, a sum, a product or a copy into the next fresh
value from `b`, its inputs numbered below it, ending at `b'`. `seq_complete`: such a block holds of
an extension of any valuation on `b ..< b'`; `SeqOK.numBelow`: its values are numbered below `b'`.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-- `v` is numbered below `b`. -/
abbrev NBv (b : Nat) (v : V) : Prop := ∃ j < b, v = .n j

/-- An atom defining value `b` from values below it. -/
def ASeq (b : Nat) : Atom → Prop
  | .const d _ => d = .n b
  | .add d x y | .mul d x y => d = .n b ∧ NBv b x ∧ NBv b y
  | .copy d x => d = .n b ∧ NBv b x
  | _ => False

/-- A block of atoms each defining the next fresh value. -/
def SeqOK : Nat → List Stmt → Nat → Prop
  | b, [], b' => b' = b
  | b, .atom a :: ss, b' => ASeq b a ∧ SeqOK (b + 1) ss b'
  | _, _ :: _, _ => False

theorem SeqOK.le : ∀ {b : Nat} {ss : List Stmt} {b' : Nat}, SeqOK b ss b' → b ≤ b'
  | _, [], _, h => by simp only [SeqOK] at h; omega
  | _, .atom _ :: _, _, h => by have := SeqOK.le h.2; omega
  | _, .ite .. :: _, _, h | _, .match_ .. :: _, _, h | _, .call .. :: _, _, h
  | _, .callIf .. :: _, _, h | _, .dispatch .. :: _, _, h | _, .ret _ :: _, _, h => h.elim

theorem SeqOK.append : ∀ {b m b' : Nat} {xs ys : List Stmt}, SeqOK b xs m → SeqOK m ys b' →
    SeqOK b (xs ++ ys) b'
  | _, _, _, [], _, h1, h2 => by simp only [SeqOK] at h1; subst h1; exact h2
  | _, _, _, .atom _ :: _, _, h1, h2 => ⟨h1.1, SeqOK.append h1.2 h2⟩
  | _, _, _, .ite .. :: _, _, h, _ | _, _, _, .match_ .. :: _, _, h, _
  | _, _, _, .call .. :: _, _, h, _ | _, _, _, .callIf .. :: _, _, h, _
  | _, _, _, .dispatch .. :: _, _, h, _ | _, _, _, .ret _ :: _, _, h, _ => h.elim

theorem SeqOK.atoms : ∀ {b : Nat} {ss : List Stmt} {b' : Nat}, SeqOK b ss b' → atomsOnly ss = true
  | _, [], _, _ => rfl
  | _, .atom _ :: ss, _, h => (SeqOK.atoms h.2 : atomsOnly ss = true)
  | _, .ite .. :: _, _, h | _, .match_ .. :: _, _, h | _, .call .. :: _, _, h
  | _, .callIf .. :: _, _, h | _, .dispatch .. :: _, _, h | _, .ret _ :: _, _, h => h.elim

theorem ASeq.vals {b : Nat} {a : Atom} (h : ASeq b a) : NumBelow (b + 1) a.vals := by
  cases a with
  | const d c =>
      simp only [ASeq] at h; subst h
      exact .cons ⟨b, by omega, rfl⟩ (.nil _)
  | add d x y =>
      obtain ⟨rfl, ⟨i, hi, rfl⟩, ⟨j, hj, rfl⟩⟩ := h
      exact .cons ⟨b, by omega, rfl⟩ (.cons ⟨i, by omega, rfl⟩ (.cons ⟨j, by omega, rfl⟩ (.nil _)))
  | mul d x y =>
      obtain ⟨rfl, ⟨i, hi, rfl⟩, ⟨j, hj, rfl⟩⟩ := h
      exact .cons ⟨b, by omega, rfl⟩ (.cons ⟨i, by omega, rfl⟩ (.cons ⟨j, by omega, rfl⟩ (.nil _)))
  | copy d x =>
      obtain ⟨rfl, ⟨i, hi, rfl⟩⟩ := h
      exact .cons ⟨b, by omega, rfl⟩ (.cons ⟨i, by omega, rfl⟩ (.nil _))
  | _ => exact h.elim

theorem SeqOK.numBelow : ∀ {b : Nat} {ss : List Stmt} {b' : Nat}, SeqOK b ss b' →
    NumBelow b' (Stmt.valsList ss)
  | _, [], _, _ => NumBelow.nil _
  | _, .atom _ :: _, _, h => by
      rw [valsList_cons]
      exact ((ASeq.vals h.1).mono (SeqOK.le h.2)).append (SeqOK.numBelow h.2)
  | _, .ite .. :: _, _, h | _, .match_ .. :: _, _, h | _, .call .. :: _, _, h
  | _, .callIf .. :: _, _, h | _, .dispatch .. :: _, _, h | _, .ret _ :: _, _, h => h.elim

/-- The value an atom of a sequential block defines. -/
def aVal (σ : Val) : Atom → E
  | .const _ c => c
  | .add _ x y => σ x + σ y
  | .mul _ x y => σ x * σ y
  | .copy _ x => σ x
  | _ => 0

theorem aSeq_holds {b : Nat} {a : Atom} (h : ASeq b a) {σ : Val} (hσ : σ (.n b) = aVal σ a) :
    a.Holds rd σ := by
  cases a with
  | const d c => simp only [ASeq] at h; subst h; exact hσ
  | add d x y => obtain ⟨rfl, -, -⟩ := h; exact hσ
  | mul d x y => obtain ⟨rfl, -, -⟩ := h; exact hσ
  | copy d x => obtain ⟨rfl, -⟩ := h; exact hσ
  | _ => exact h.elim

theorem aVal_congr {b : Nat} {a : Atom} (h : ASeq b a) {σ σ' : Val} (hσ : AgreeBelow b σ σ') :
    aVal σ a = aVal σ' a := by
  cases a with
  | const d c => rfl
  | add d x y =>
      obtain ⟨-, hx, hy⟩ := h
      simp only [aVal, hσ.apply hx, hσ.apply hy]
  | mul d x y =>
      obtain ⟨-, hx, hy⟩ := h
      simp only [aVal, hσ.apply hx, hσ.apply hy]
  | copy d x =>
      obtain ⟨-, hx⟩ := h
      simp only [aVal, hσ.apply hx]
  | _ => exact h.elim

/-- **A sequential block completes.** -/
theorem seq_complete : ∀ {b : Nat} {ss : List Stmt} {b' : Nat}, SeqOK b ss b' → ∀ σ : Val,
    ∃ σ', Ext b b' σ σ' ∧ AtomsHold rd σ' ss
  | _, [], _, h, σ => by
      simp only [SeqOK] at h; subst h
      exact ⟨σ, Ext.refl _ _ _, fun _ ha => absurd ha (by simp)⟩
  | b, .atom a :: ss, b', h, σ => by
      obtain ⟨σ', he, hh⟩ := seq_complete h.2 (Function.update σ (.n b) (aVal σ a))
      have hle := SeqOK.le h.2
      have he1 : Ext b (b + 1) σ (Function.update σ (.n b) (aVal σ a)) := fun v hv =>
        Function.update_of_ne (hv b le_rfl (by omega)) _ _
      refine ⟨σ', he1.trans he (by omega) hle, fun x hx => ?_⟩
      rcases List.mem_cons.mp hx with e | hx
      · cases e
        have hag : AgreeBelow (b + 1) (Function.update σ (.n b) (aVal σ a)) σ' := he.agree
        have hag' : AgreeBelow b σ σ' := fun k hk => by
          rw [← hag k (by omega), Function.update_of_ne (by simp; omega)]
        apply aSeq_holds h.1
        rw [← hag b (by omega), Function.update_self, aVal_congr h.1 hag']
      · exact hh x hx
  | _, .ite .. :: _, _, h, _ | _, .match_ .. :: _, _, h, _ | _, .call .. :: _, _, h, _
  | _, .callIf .. :: _, _, h, _ | _, .dispatch .. :: _, _, h, _ | _, .ret _ :: _, _, h, _ => h.elim

/-- **A sequential block completes**, as `Completes`. -/
theorem seq_completes {b b' : Nat} {ss : List Stmt} (h : SeqOK b ss b') (σ : Val) :
    Completes C rd b b' ss σ (fun σ' => AtomsHold rd σ' ss) := by
  obtain ⟨σ', he, hh⟩ := seq_complete (rd := rd) h σ
  exact completes_atoms h.atoms he hh hh

end
end LeanVM.Guest.B1.Sig
