/-
  LeanVM.Guest.Memory.StaticSplit

  A body's static check in ranges, the constants threaded: `blockB` of a block is the sum of its
  first range's and the rest's from the constants after the first (`blockEnv`).
-/

module

public import LeanVM.Guest.Memory.StaticSound

/-!
# The check in ranges

`blockEnv` replays the top-level atoms of a block on the constants and bounds (`atomB`), as
`blockB` threads them. `blockB_appendE`: a block without a top-level `ret` followed by another is
checked as the sum of the first from `ρ` and the second from `blockEnv ρ` of the first; so a large
body is checked in ranges, each from the constants its predecessors leave (`blockB_dropE`), as the
generated families do (`Memory/GuestWords`, `Memory/GuestCnt*`).
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

/-- **The constants and bounds after a block's top-level atoms**, as `blockB` threads them; an
atom the check rejects leaves them. -/
def blockEnv (α : Bool) (ks : List (V × ℕ)) (ps : List V) : Env × BEnv → List Stmt → Env × BEnv
  | ρ, [] => ρ
  | ρ, s :: ss => match s with
    | .atom a => match atomB α ks ps ρ a with
      | some q => blockEnv α ks ps q.2 ss
      | none => ρ
    | _ => blockEnv α ks ps ρ ss

variable {cert : String → Cert} {wl : String → Option ℕ} {α : Bool} {ks : List (V × ℕ)} {ps : List V}
  {self : String}

/-- **A block is the sum of its ranges**, the first without `ret`, the second from the constants
the first leaves. -/
theorem blockB_appendE : ∀ (ρ : Env × BEnv) (l1 l2 : List Stmt), noTopRet l1 = true →
    blockB cert wl α ks ps self ρ (l1 ++ l2) =
      Option.addAcc (blockB cert wl α ks ps self ρ l1)
        (blockB cert wl α ks ps self (blockEnv α ks ps ρ l1) l2)
  | ρ, [], l2, _ => by
      rw [List.nil_append, blockEnv, show blockB cert wl α ks ps self ρ [] = some Acc.zero by
        rw [blockB]; rfl, addAcc_some_zero]
  | ρ, s :: l1, l2, h => by
      simp only [noTopRet, List.all_cons, Bool.and_eq_true] at h
      rw [List.cons_append]
      cases s with
      | atom a =>
          cases hq : atomB α ks ps ρ a with
          | none => simp only [blockB, hq]; rfl
          | some q =>
              obtain ⟨r, ρ'⟩ := q
              simp only [blockB, blockEnv, hq]
              rw [blockB_appendE ρ' l1 l2 h.2, addAcc_assoc]
      | ite c z n => simp only [blockB, blockEnv]; rw [blockB_appendE ρ l1 l2 h.2, addAcc_assoc]
      | match_ x arms => simp only [blockB, blockEnv]; rw [blockB_appendE ρ l1 l2 h.2, addAcc_assoc]
      | call g a r => simp only [blockB, blockEnv]; rw [blockB_appendE ρ l1 l2 h.2, addAcc_assoc]
      | callIf c g a =>
          simp only [blockB, blockEnv]
          split_ifs
          · rfl
          · rw [blockB_appendE ρ l1 l2 h.2, addAcc_assoc, addAcc_assoc]
      | dispatch x gs a r => simp only [blockB, blockEnv]; rw [blockB_appendE ρ l1 l2 h.2, addAcc_assoc]
      | ret vs => simp at h

/-- The ranges from `a` and from `b = a + n`, the first without `ret`, the second from the
constants `ρ'` the first leaves. -/
theorem blockB_dropE (ρ ρ' : Env × BEnv) (l : List Stmt) (a n b : ℕ)
    (h : noTopRet ((l.drop a).take n) = true) (hb : a + n = b)
    (he : blockEnv α ks ps ρ ((l.drop a).take n) = ρ') :
    blockB cert wl α ks ps self ρ (l.drop a) =
      Option.addAcc (blockB cert wl α ks ps self ρ ((l.drop a).take n))
        (blockB cert wl α ks ps self ρ' (l.drop b)) := by
  subst hb he
  rw [← blockB_appendE ρ _ _ h, ← List.drop_drop, List.take_append_drop]

end
end LeanVM.Guest.Memory
