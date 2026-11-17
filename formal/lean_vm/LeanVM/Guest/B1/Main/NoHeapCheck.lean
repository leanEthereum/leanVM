/-
  LeanVM.Guest.B1.Main.NoHeapCheck

  No witness hint of the program is on the `heap_sizes` stream, by the kernel.
-/

module

public import LeanVM.Guest.Pops
public import LeanVM.Guest.Hints
public import LeanVM.Guest.B2C.ShareSound

/-!
# No witness hint on `heap_sizes`

`atomNoHeap`: an atom is no witness hint on `heap_sizes`; `coreProgram_noHeap`: every atom of every function passes it.
The kernel checks `nhL`, the same test by `Stmt`'s recursor, which builds no list of atoms (`nhL_eq`), a hundred functions
at a time, the last check taking the rest.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- An atom that is no witness hint on `heap_sizes`. -/
def atomNoHeap : Atom → Bool
  | .hint (.witness s _) => s != Hints.heapSizeStream
  | _ => true

/-- `atomNoHeap` on every atom of a statement, by the recursor. -/
noncomputable def nhS : Stmt → Bool :=
  @Stmt.rec (fun _ => Bool) (fun _ => Bool) (fun _ => Bool)
    atomNoHeap (fun _ _ _ z n => z && n) (fun _ _ r => r) (fun _ _ _ => true) (fun _ _ _ => true)
    (fun _ _ _ _ => true) (fun _ => true) true (fun _ _ h t => h && t) true (fun _ _ h t => h && t)

/-- `nhS` on a block. -/
noncomputable def nhL : List Stmt → Bool :=
  @Stmt.rec_1 (fun _ => Bool) (fun _ => Bool) (fun _ => Bool)
    atomNoHeap (fun _ _ _ z n => z && n) (fun _ _ r => r) (fun _ _ _ => true) (fun _ _ _ => true)
    (fun _ _ _ _ => true) (fun _ => true) true (fun _ _ h t => h && t) true (fun _ _ h t => h && t)

/-- `nhS` on arms. -/
noncomputable def nhA : List (List Stmt) → Bool :=
  @Stmt.rec_2 (fun _ => Bool) (fun _ => Bool) (fun _ => Bool)
    atomNoHeap (fun _ _ _ z n => z && n) (fun _ _ r => r) (fun _ _ _ => true) (fun _ _ _ => true)
    (fun _ _ _ _ => true) (fun _ => true) true (fun _ _ h t => h && t) true (fun _ _ h t => h && t)

mutual
theorem nhS_eq : ∀ s : Stmt, (B2C.sAtoms s).all atomNoHeap = nhS s
  | .atom a => by simp only [B2C.sAtoms, List.all_cons, List.all_nil, Bool.and_true]; rfl
  | .ite c z n => by
      simp only [B2C.sAtoms, List.all_append, nhL_eq z, nhL_eq n]; rfl
  | .match_ x arms => by simp only [B2C.sAtoms, nhA_eq arms]; rfl
  | .call .. | .callIf .. | .dispatch .. | .ret _ => rfl

theorem nhL_eq : ∀ ss : List Stmt, (B2C.lAtoms ss).all atomNoHeap = nhL ss
  | [] => rfl
  | s :: ss => by simp only [B2C.lAtoms, List.all_append, nhS_eq s, nhL_eq ss]; rfl

theorem nhA_eq : ∀ arms : List (List Stmt), (B2C.aAtoms arms).all atomNoHeap = nhA arms
  | [] => rfl
  | b :: as => by simp only [B2C.aAtoms, List.all_append, nhL_eq b, nhA_eq as]; rfl
end

theorem all_drop_step {α : Type} {p : α → Bool} {l : List α} {n k : ℕ}
    (hc : ((l.drop (n * k)).take n).all p = true) (ht : (l.drop (n * (k + 1))).all p = true) :
    (l.drop (n * k)).all p = true := by
  rw [← List.take_append_drop n (l.drop (n * k)), List.all_append, hc, List.drop_drop, Bool.true_and]
  rwa [Nat.mul_succ] at ht

private theorem nh0 : ((coreProgram.drop (100 * 0)).take 100).all (fun fn => nhL fn.body) = true := by
  decide +kernel

private theorem nh1 : ((coreProgram.drop (100 * 1)).take 100).all (fun fn => nhL fn.body) = true := by
  decide +kernel

private theorem nh2 : ((coreProgram.drop (100 * 2)).take 100).all (fun fn => nhL fn.body) = true := by
  decide +kernel

private theorem nh3 : ((coreProgram.drop (100 * 3)).take 100).all (fun fn => nhL fn.body) = true := by
  decide +kernel

private theorem nh4 : ((coreProgram.drop (100 * 4)).take 100).all (fun fn => nhL fn.body) = true := by
  decide +kernel

private theorem nh5 : ((coreProgram.drop (100 * 5)).take 100).all (fun fn => nhL fn.body) = true := by
  decide +kernel

private theorem nh6 : ((coreProgram.drop (100 * 6)).take 100).all (fun fn => nhL fn.body) = true := by
  decide +kernel

private theorem nh7 : ((coreProgram.drop (100 * 7)).take 100).all (fun fn => nhL fn.body) = true := by
  decide +kernel

private theorem nh8 : ((coreProgram.drop (100 * 8)).take 100).all (fun fn => nhL fn.body) = true := by
  decide +kernel

private theorem nh9 : ((coreProgram.drop (100 * 9)).take 100).all (fun fn => nhL fn.body) = true := by
  decide +kernel

private theorem nh10 : ((coreProgram.drop (100 * 10)).take 100).all (fun fn => nhL fn.body) = true := by
  decide +kernel

private theorem nh11 : ((coreProgram.drop (100 * 11)).take 100).all (fun fn => nhL fn.body) = true := by
  decide +kernel

private theorem nh12 : ((coreProgram.drop (100 * 12)).take 100).all (fun fn => nhL fn.body) = true := by
  decide +kernel

private theorem nh13 : ((coreProgram.drop (100 * 13)).take 100).all (fun fn => nhL fn.body) = true := by
  decide +kernel

private theorem nh14 : ((coreProgram.drop (100 * 14)).take 100).all (fun fn => nhL fn.body) = true := by
  decide +kernel

private theorem nh15 : ((coreProgram.drop (100 * 15)).take 100).all (fun fn => nhL fn.body) = true := by
  decide +kernel

private theorem nh16 : (coreProgram.drop (100 * 16)).all (fun fn => nhL fn.body) = true := by
  decide +kernel

/-- **No atom of the program is a witness hint on `heap_sizes`.** -/
theorem coreProgram_noHeap : coreProgram.all (fun fn => (B2C.lAtoms fn.body).all atomNoHeap) = true := by
  simp only [nhL_eq]
  exact all_drop_step (k := 0) nh0 <| all_drop_step nh1 <| all_drop_step nh2 <| all_drop_step nh3 <|
    all_drop_step nh4 <| all_drop_step nh5 <| all_drop_step nh6 <| all_drop_step nh7 <| all_drop_step nh8 <|
    all_drop_step nh9 <| all_drop_step nh10 <| all_drop_step nh11 <| all_drop_step nh12 <| all_drop_step nh13 <|
    all_drop_step nh14 <| all_drop_step nh15 nh16

end
end LeanVM.Guest.B1.Main
