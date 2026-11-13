/-
  LeanVM.Guest.B1.Sig.FwdComplete

  Blocks of atoms in single-assignment form complete: evaluating each defining atom in order, a
  later atom never redefining a value an earlier one names, makes every atom hold.
-/

module

public import LeanVM.Guest.B1.Sig.CompleteBasic

/-!
# Forward evaluation

`aOuts`, `aReads`: the values an atom defines and reads (a constant, a sum, a product, a
copy, a `KECCAK`, a witness hint; a hint defines its values by keeping them). `fwd`: the atoms
evaluated in order. `SSA`: each atom defines values it does not read and that no earlier atom
names. `fwd_holds`: in single-assignment form, the evaluated block holds; `fwd_of_not_mem`: values no atom defines keep their words.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak

@[expose] public section

variable {rd : Reader}

/-- `v` is numbered below `b`. -/
def NBvF (b : Nat) (v : V) : Prop := ∃ j < b, v = .n j

/-- The values an atom defines. -/
def aOuts : Atom → List V
  | .const d _ | .add d _ _ | .mul d _ _ | .copy d _ => [d]
  | .keccak _ outs _ _ => outs
  | .hint (.witness _ (.stack vs)) => vs
  | _ => []

/-- The values an atom reads. -/
def aReads : Atom → List V
  | .add _ x y | .mul _ x y => [x, y]
  | .copy _ x => [x]
  | .keccak ins _ _ _ => ins
  | _ => []

/-- An atom evaluation defines. -/
def DefOK : Atom → Prop
  | .const _ _ | .add _ _ _ | .mul _ _ _ | .copy _ _ => True
  | .keccak ins outs _ _ =>
      ins.length = 13 ∧ (outs.length = 1 ∨ outs.length = 2 ∨ outs.length = 13) ∧ outs.Nodup
  | .hint (.witness _ (.stack _)) => True
  | _ => False

/-- The values updated to `f 0, f 1, …`, the first entry winning. -/
def updL (σ : Val) : List V → (Nat → E) → Val
  | [], _ => σ
  | v :: vs, f => Function.update (updL σ vs fun j => f (j + 1)) v (f 0)

theorem updL_of_not_mem (σ : Val) : ∀ (vs : List V) (f : Nat → E) {v : V}, v ∉ vs → updL σ vs f v = σ v
  | [], _, _, _ => rfl
  | w :: vs, f, v, hv => by
      simp only [List.mem_cons, not_or] at hv
      simp only [updL]
      rw [Function.update_of_ne hv.1, updL_of_not_mem σ vs _ hv.2]

theorem updL_at (σ : Val) : ∀ (vs : List V) (f : Nat → E), vs.Nodup → ∀ j (hj : j < vs.length),
    updL σ vs f vs[j] = f j
  | [], _, _, j, hj => absurd hj (by simp)
  | w :: vs, f, hn, j, hj => by
      simp only [updL]
      rcases j with _ | j
      · simp
      · have hne : vs[j]'(by simpa using hj) ≠ w := by
          intro e
          have := (List.nodup_cons.mp hn).1
          exact this (e ▸ List.getElem_mem _)
        simp only [List.getElem_cons_succ]
        rw [Function.update_of_ne hne, updL_at σ vs _ (List.nodup_cons.mp hn).2 j]

/-- An atom evaluated. -/
def fwdA (σ : Val) : Atom → Val
  | .const d c => Function.update σ d c
  | .add d x y => Function.update σ d (σ x + σ y)
  | .mul d x y => Function.update σ d (σ x * σ y)
  | .copy d x => Function.update σ d (σ x)
  | .keccak ins outs inOdd outOdd => updL σ outs (kOut (ins.map σ) inOdd outOdd)
  | _ => σ

/-- The atoms of a block evaluated in order. -/
def fwd : List Stmt → Val → Val
  | [], σ => σ
  | .atom a :: ss, σ => fwd ss (fwdA σ a)
  | _ :: ss, σ => fwd ss σ

/-- The values a block defines. -/
def outsList : List Stmt → List V
  | [] => []
  | .atom a :: ss => aOuts a ++ outsList ss
  | _ :: ss => outsList ss

/-- Single-assignment form. -/
def SSA : List Stmt → Prop
  | [] => True
  | .atom a :: ss => DefOK a ∧ (∀ v ∈ aOuts a, v ∉ aReads a) ∧ (∀ v ∈ outsList ss, v ∉ a.vals) ∧ SSA ss
  | _ :: _ => False

theorem fwdA_of_not_mem (σ : Val) (a : Atom) {v : V} (hv : v ∉ aOuts a) : fwdA σ a v = σ v := by
  cases a with
  | const d c => exact Function.update_of_ne (by simpa [aOuts] using hv) _ _
  | add d x y => exact Function.update_of_ne (by simpa [aOuts] using hv) _ _
  | mul d x y => exact Function.update_of_ne (by simpa [aOuts] using hv) _ _
  | copy d x => exact Function.update_of_ne (by simpa [aOuts] using hv) _ _
  | keccak ins outs inOdd outOdd => exact updL_of_not_mem σ outs _ hv
  | _ => rfl

theorem fwd_of_not_mem : ∀ (ss : List Stmt) (σ : Val) {v : V}, v ∉ outsList ss → fwd ss σ v = σ v
  | [], _, _, _ => rfl
  | .atom a :: ss, σ, v, hv => by
      simp only [outsList, List.mem_append, not_or] at hv
      simp only [fwd]
      rw [fwd_of_not_mem ss _ hv.2, fwdA_of_not_mem σ a hv.1]
  | .ite .. :: ss, σ, _, hv | .match_ .. :: ss, σ, _, hv | .call .. :: ss, σ, _, hv
  | .callIf .. :: ss, σ, _, hv | .dispatch .. :: ss, σ, _, hv | .ret _ :: ss, σ, _, hv =>
      fwd_of_not_mem ss σ hv

theorem fwdA_holds {σ : Val} {a : Atom} (hd : DefOK a) (hr : ∀ v ∈ aOuts a, v ∉ aReads a) :
    a.Holds rd (fwdA σ a) := by
  cases a
  case const d c => simp [fwdA, Atom.Holds]
  case add d x y =>
      have h1 : x ≠ d := fun e => hr d (by simp [aOuts]) (by simp [aReads, e])
      have h2 : y ≠ d := fun e => hr d (by simp [aOuts]) (by simp [aReads, e])
      simp only [fwdA, Atom.Holds, Function.update_self]
      rw [Function.update_of_ne h1, Function.update_of_ne h2]
  case mul d x y =>
      have h1 : x ≠ d := fun e => hr d (by simp [aOuts]) (by simp [aReads, e])
      have h2 : y ≠ d := fun e => hr d (by simp [aOuts]) (by simp [aReads, e])
      simp only [fwdA, Atom.Holds, Function.update_self]
      rw [Function.update_of_ne h1, Function.update_of_ne h2]
  case copy d x =>
      have h1 : x ≠ d := fun e => hr d (by simp [aOuts]) (by simp [aReads, e])
      simp only [fwdA, Atom.Holds, Function.update_self]
      rw [Function.update_of_ne h1]
  case keccak ins outs inOdd outOdd =>
      obtain ⟨hl, ho, hn⟩ := hd
      obtain ⟨oc, ho⟩ := exists_cellCount ho
      have hins : ins.map (updL σ outs (kOut (ins.map σ) inOdd outOdd)) = ins.map σ :=
        List.map_congr_left fun v hv => updL_of_not_mem σ outs _ fun h => hr v h hv
      refine ⟨hl, oc, ho, ?_⟩
      show KeccakCellsRelation (cells13 (ins.map (updL σ outs (kOut (ins.map σ) inOdd outOdd)))) inOdd
        (cells13 (outs.map (updL σ outs (kOut (ins.map σ) inOdd outOdd)))) outOdd oc
      rw [hins]
      intro c hco
      simp only [cells13, List.getD_eq_getElem?_getD, List.getElem?_map]
      rw [List.getElem?_eq_getElem (by omega), Option.map_some, Option.getD_some,
        updL_at σ outs _ hn c (by omega), kOut]
      simp [c.isLt]
  case hint h =>
      cases h
      case witness s d =>
        cases d
        case stack vs => trivial
        all_goals exact hd.elim
      all_goals exact hd.elim
  all_goals exact hd.elim

theorem outs_sub_vals (a : Atom) : ∀ v ∈ aOuts a, v ∈ a.vals := by
  intro v hv
  cases a
  case hint h =>
      cases h
      case witness s d =>
        cases d
        case stack vs => simpa [aOuts, Atom.vals, Hint.vals, Dest.vals] using hv
        all_goals simp [aOuts] at hv
      all_goals simp [aOuts] at hv
  all_goals simp_all [aOuts, Atom.vals]

/-- **A block in single-assignment form, evaluated, holds.** -/
theorem fwd_holds : ∀ (ss : List Stmt) (σ : Val), SSA ss → AtomsHold rd (fwd ss σ) ss
  | [], _, _ => fun _ h => absurd h (by simp)
  | .atom a :: ss, σ, h => by
      obtain ⟨hd, hr, hl, hs⟩ := h
      have hag : ∀ v ∈ a.vals, fwd ss (fwdA σ a) v = fwdA σ a v := fun v hv =>
        fwd_of_not_mem ss _ fun h => hl v h hv
      have ih := fwd_holds ss (fwdA σ a) hs
      intro b hb
      rcases List.mem_cons.mp hb with e | hb
      · cases e
        exact (atom_congr a fun v hv => (hag v hv).symm).mp (fwdA_holds hd hr)
      · exact ih b hb
  | .ite .. :: _, _, h | .match_ .. :: _, _, h | .call .. :: _, _, h
  | .callIf .. :: _, _, h | .dispatch .. :: _, _, h | .ret _ :: _, _, h => h.elim

theorem outsList_append : ∀ (xs ys : List Stmt), outsList (xs ++ ys) = outsList xs ++ outsList ys
  | [], _ => rfl
  | .atom a :: xs, ys => by simp [outsList, outsList_append xs ys]
  | .ite .. :: xs, ys | .match_ .. :: xs, ys | .call .. :: xs, ys | .callIf .. :: xs, ys
  | .dispatch .. :: xs, ys | .ret _ :: xs, ys => by simp only [List.cons_append, outsList]; exact outsList_append xs ys

theorem SSA.append : ∀ {xs ys : List Stmt}, SSA xs → SSA ys →
    (∀ v ∈ outsList ys, v ∉ Stmt.valsList xs) → SSA (xs ++ ys)
  | [], _, _, h2, _ => h2
  | .atom a :: xs, ys, h1, h2, h3 => by
      obtain ⟨hd, hr, hl, hs⟩ := h1
      refine ⟨hd, hr, fun v hv hva => ?_, SSA.append hs h2 fun v hv hvx => h3 v hv (by
        simp only [valsList_cons, Stmt.vals, List.mem_append]; exact Or.inr hvx)⟩
      have hv' : v ∈ outsList xs ++ outsList ys := outsList_append xs ys ▸ hv
      rcases List.mem_append.mp hv' with hv | hv
      · exact hl v hv hva
      · exact h3 v hv (by simp only [valsList_cons, Stmt.vals, List.mem_append]; exact Or.inl hva)
  | .ite .. :: _, _, h, _, _ | .match_ .. :: _, _, h, _, _ | .call .. :: _, _, h, _, _
  | .callIf .. :: _, _, h, _, _ | .dispatch .. :: _, _, h, _, _ | .ret _ :: _, _, h, _, _ => h.elim

theorem SSA.atoms : ∀ {ss : List Stmt}, SSA ss → atomsOnly ss = true
  | [], _ => rfl
  | .atom _ :: ss, h => (SSA.atoms h.2.2.2 : atomsOnly ss = true)
  | .ite .. :: _, h | .match_ .. :: _, h | .call .. :: _, h
  | .callIf .. :: _, h | .dispatch .. :: _, h | .ret _ :: _, h => h.elim

/-- **A block in single-assignment form completes**, defining values in `lo ..< hi`. -/
theorem fwd_completes {C : CallRel} {lo hi : Nat} {ss : List Stmt} (h : SSA ss)
    (hout : ∀ v ∈ outsList ss, ∃ k, lo ≤ k ∧ k < hi ∧ v = .n k) (σ : Val) :
    Completes C rd lo hi ss σ (fun σ' => σ' = fwd ss σ) :=
  completes_atoms h.atoms (fun v hv => fwd_of_not_mem ss σ fun hm => by
      obtain ⟨k, h1, h2, rfl⟩ := hout v hm
      exact hv k h1 h2 rfl) rfl (fwd_holds ss σ h)

theorem fwd_append : ∀ (xs ys : List Stmt) (σ : Val), fwd (xs ++ ys) σ = fwd ys (fwd xs σ)
  | [], _, _ => rfl
  | .atom a :: xs, ys, σ => fwd_append xs ys (fwdA σ a)
  | .ite .. :: xs, ys, σ | .match_ .. :: xs, ys, σ | .call .. :: xs, ys, σ | .callIf .. :: xs, ys, σ
  | .dispatch .. :: xs, ys, σ | .ret _ :: xs, ys, σ => fwd_append xs ys σ

theorem SSA.disj : ∀ {xs ys : List Stmt}, SSA (xs ++ ys) → ∀ v ∈ outsList ys, v ∉ Stmt.valsList xs
  | [], _, _, _, _, h => by simp at h
  | .atom a :: xs, ys, h, v, hv, hm => by
      obtain ⟨-, -, hl, hs⟩ := h
      simp only [valsList_cons, Stmt.vals, List.mem_append] at hm
      rcases hm with hm | hm
      · exact hl v (outsList_append xs ys ▸ List.mem_append_right _ hv : v ∈ outsList (xs ++ ys)) hm
      · exact SSA.disj hs v hv hm
  | .ite .. :: _, _, h, _, _, _ | .match_ .. :: _, _, h, _, _, _ | .call .. :: _, _, h, _, _, _
  | .callIf .. :: _, _, h, _, _, _ | .dispatch .. :: _, _, h, _, _, _ | .ret _ :: _, _, h, _, _, _ =>
      h.elim

theorem SSA.left : ∀ {xs ys : List Stmt}, SSA (xs ++ ys) → SSA xs
  | [], _, _ => trivial
  | .atom a :: xs, ys, h => by
      obtain ⟨h1, h2, h3, h4⟩ := h
      exact ⟨h1, h2, fun v hv => h3 v (outsList_append xs ys ▸ List.mem_append_left _ hv :
        v ∈ outsList (xs ++ ys)),
        SSA.left h4⟩
  | .ite .. :: _, _, h | .match_ .. :: _, _, h | .call .. :: _, _, h
  | .callIf .. :: _, _, h | .dispatch .. :: _, _, h | .ret _ :: _, _, h => h.elim

theorem SSA.right : ∀ {xs ys : List Stmt}, SSA (xs ++ ys) → SSA ys
  | [], _, h => h
  | .atom _ :: xs, _, h => SSA.right (xs := xs) h.2.2.2
  | .ite .. :: _, _, h | .match_ .. :: _, _, h | .call .. :: _, _, h
  | .callIf .. :: _, _, h | .dispatch .. :: _, _, h | .ret _ :: _, _, h => h.elim

end
end LeanVM.Guest.B1.Sig
