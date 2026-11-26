/-
  LeanVM.Guest.B1.Fwd.PureIn

  `Program.PureIn` as a kernel check: a set of functions placing nothing.
-/

module

public import LeanVM.Guest.Memory.Uniform

namespace LeanVM.Guest.B1.Tables

open LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

mutual
/-- `Stmt.pure`, a callee's membership by `mem`. -/
def pureBy (mem : String → Bool) : Stmt → Bool
  | .atom a => atomUnplaced a
  | .ite _ z n => pureListBy mem z && pureListBy mem n
  | .match_ _ arms => pureArmsBy mem arms
  | .call f _ _ => mem f
  | .callIf _ f _ => mem f
  | .dispatch _ fs _ _ => fs.all mem
  | .ret _ => true

/-- `Stmt.pureList`, a callee's membership by `mem`. -/
def pureListBy (mem : String → Bool) : List Stmt → Bool
  | [] => true
  | s :: ss => pureBy mem s && pureListBy mem ss

/-- `Stmt.pureArms`, a callee's membership by `mem`. -/
def pureArmsBy (mem : String → Bool) : List (List Stmt) → Bool
  | [] => true
  | a :: as => pureListBy mem a && pureArmsBy mem as
end

mutual
theorem pureBy_eq {S : List String} {mem : String → Bool} (h : ∀ f, mem f = decide (f ∈ S)) :
    ∀ s, pureBy mem s = Stmt.pure S s
  | .atom _ => by simp only [pureBy, Stmt.pure]
  | .ite _ z n => by simp only [pureBy, Stmt.pure, pureListBy_eq h z, pureListBy_eq h n]
  | .match_ _ arms => by simp only [pureBy, Stmt.pure, pureArmsBy_eq h arms]
  | .call f _ _ => by simp only [pureBy, Stmt.pure, h]
  | .callIf _ f _ => by simp only [pureBy, Stmt.pure, h]
  | .dispatch _ fs _ _ => by
      simp only [pureBy, Stmt.pure]
      exact congrArg (fs.all ·) (funext h)
  | .ret _ => by simp only [pureBy, Stmt.pure]

theorem pureListBy_eq {S : List String} {mem : String → Bool} (h : ∀ f, mem f = decide (f ∈ S)) :
    ∀ l, pureListBy mem l = Stmt.pureList S l
  | [] => by simp only [pureListBy, Stmt.pureList]
  | s :: ss => by simp only [pureListBy, Stmt.pureList, pureBy_eq h s, pureListBy_eq h ss]

theorem pureArmsBy_eq {S : List String} {mem : String → Bool} (h : ∀ f, mem f = decide (f ∈ S)) :
    ∀ as, pureArmsBy mem as = Stmt.pureArms S as
  | [] => by simp only [pureArmsBy, Stmt.pureArms]
  | a :: as => by simp only [pureArmsBy, Stmt.pureArms, pureListBy_eq h a, pureArmsBy_eq h as]
end

/-- Membership by the names' encodings is membership. -/
theorem memEnc_eq (S : List String) (f : String) :
    (S.map encS).any (Nat.beq · (encS f)) = decide (f ∈ S) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  constructor
  · intro h
    obtain ⟨x, hx, hb⟩ := List.any_eq_true.mp h
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hx
    rwa [encS_inj (Nat.eq_of_beq_eq_true hb)] at hg
  · exact fun h ↦ List.any_eq_true.mpr ⟨encS f, List.mem_map_of_mem h, Nat.beq_refl _⟩

/-- `Program.find?` by the names' encodings. -/
theorem findEnc_eq (P : Core.Program) (g : String) :
    List.find? (fun fn ↦ Nat.beq (encS fn.name) (encS g)) P = P.find? g := by
  unfold Program.find?
  congr 1
  funext fn
  rw [Bool.eq_iff_iff, beq_iff_eq]
  exact ⟨fun h ↦ encS_inj (Nat.eq_of_beq_eq_true h), fun h ↦ h ▸ Nat.beq_refl _⟩

/-- `Program.PureIn`, as a check: names compared by their encodings (`encS`), numbers where the kernel
would decode strings. -/
def pureInB (P : Core.Program) (S : List String) : Bool :=
  S.all fun g ↦ match List.find? (fun fn ↦ Nat.beq (encS fn.name) (encS g)) P with
    | some fn => pureListBy (fun f ↦ (S.map encS).any (Nat.beq · (encS f))) fn.body
    | none => true

theorem pureIn_of_pureInB {P : Core.Program} {S : List String} (h : pureInB P S = true) :
    P.PureIn S := by
  intro g hg fn hf
  have := List.all_eq_true.mp h g hg
  simp only [findEnc_eq, hf] at this
  rwa [pureListBy_eq (memEnc_eq S)] at this

end
end LeanVM.Guest.B1.Tables
