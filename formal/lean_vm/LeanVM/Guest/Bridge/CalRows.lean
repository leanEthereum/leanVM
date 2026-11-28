/-
  LeanVM.Guest.Bridge.CalRows

  The listed callees' facts the frame sizes' check reads, by index in a few steps.
-/

module

public import LeanVM.Guest.Bridge.AllocFrDefs
public import LeanVM.Guest.Bridge.IdxData
public import LeanVM.Guest.Bridge.JumpCellsPack
public meta import LeanVM.Guest.KernelLit

/-!
# The listed callees' rows

`frChk` reads, of each listed callee `c`, `calRow c`: its name, frame size, loop flag, loop end and
tail. Read by index (`coreOf c`, `B2C.fsN c`, `B2C.tailN c`), each walks a list of the program's
functions from its start, at every call edge of every function. `calRowAt c` reads the same from
tries by index: the core IR and certificates the generated `idxCores` and `idxCerts`, which the kernel
checks once are the program's lists as tries (`idxCores_eq`, `idxCerts_eq`), and the frame sizes
`idxSizes`. `calRowAt c = calRow c` (`calRowAt_eq`), and the generated checks decide `frChkT` over
`calRowsOf` (`frChk_of_rows`).
-/

namespace LeanVM.Guest.Bridge

open LeanVM.Guest.Core
open LeanVM.Guest.Check (getF)
open LeanVM.Guest.Exec (Trie)

/-- The program's core IR as a trie by compiled index. -/
kernel_rfl idxCores_eq : buildT 11 (default :: coreProgram) = idxCores

/-- The certificates as a trie by compiled index. -/
kernel_rfl idxCerts_eq : buildT 11 Data.certs = idxCerts

@[expose] public section

/-- The frame sizes as a trie by compiled index. -/
kernel_lit idxSizes : Trie ℕ := buildT 11 Data.frameSizes

/-- `calRow c`, read from the tries by index. -/
noncomputable def calRowAt (c : ℕ) : String × ℕ × Bool × Option (Option ℕ) × ℕ :=
  ((getF idxCores c).getD default |>.name,
    bif Nat.beq c 1 then B2C.mainFrame else max 2 ((getF idxSizes c).getD 0),
    ((getF idxCores c).getD default).loop, Res.endOfFn ((getF idxCores c).getD default),
    min (bif Nat.beq c 1 then B2C.mainFrame else max 2 ((getF idxSizes c).getD 0))
      (max (((getF idxCores c).getD default).params.length + 3)
        ((((getF idxCerts c).getD default).facts.env.map (·.1 + 1)).foldr max 0)))

/-- The listed callees' rows, read from the tries. -/
noncomputable def calRowsOf (cs : List ℕ) : List (String × ℕ × Bool × Option (Option ℕ) × ℕ) :=
  cs.map calRowAt

end

public section

private theorem listElementOrDefault_eq {α : Type} : ∀ (l : List α) (n : ℕ) (d : α),
    listElementOrDefault l n d = l.getD n d
  | [], _, _ => rfl
  | _ :: _, 0, _ => rfl
  | _ :: l, n + 1, d => listElementOrDefault_eq l n d

/-- **`calRowAt` is `calRow`**, for every compiled index `c ≥ 1` the tries hold. -/
theorem calRowAt_eq {c : ℕ} (h1 : 1 ≤ c) (h2 : c + 1 < 2 ^ 11) : calRowAt c = calRow c := by
  obtain ⟨i, rfl⟩ : ∃ i, c = i + 1 := ⟨c - 1, by omega⟩
  have hf : (getF idxCores (i + 1)).getD default = coreOf (i + 1) := by
    rw [← idxCores_eq, getF_buildT 11 _ _ h2, List.getElem?_cons_succ, coreOf, Nat.add_sub_cancel,
      listElementOrDefault_eq, List.getD_eq_getElem?_getD]
  have hs : (getF idxSizes (i + 1)).getD 0 = fsAt (i + 1) := by
    rw [← idxSizes_eq, getF_buildT 11 _ _ h2, fsAt, List.getD_eq_getElem?_getD]
  have hC : ((getF idxCerts (i + 1)).getD default).facts.env = (certOf (i + 1)).facts.env := by
    rw [← idxCerts_eq, getF_buildT 11 _ _ h2, certOf, ← List.getD_eq_getElem?_getD, ← listElementOrDefault_eq]
  rw [calRowAt, hf, hs, hC]
  rfl

private theorem nFns_lt : nFns + 1 < 2 ^ 11 := by decide +kernel

/-- The listed callees' rows are their `calTbl`, each a compiled function `c ≥ 1`. -/
theorem calRowsOf_eq {cs : List ℕ} (h : cs.all (fun c ↦ Nat.ble 1 c && Nat.blt c nFns) = true) :
    calRowsOf cs = calTbl cs := by
  refine List.map_congr_left fun c hc ↦ ?_
  have := List.all_eq_true.mp h c hc
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at this
  exact calRowAt_eq this.1 (by have := nFns_lt; omega)

/-- **`frChk` from its fast form over the tries.** -/
theorem frChk_of_rows {X : AlignCtx} {n : ℕ} {cs : List ℕ} {ps : List V} {body : List Stmt}
    {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)} (h : frChkT X n cs (calRowsOf cs) ps body d = true) :
    frChk X n cs ps body d = true := by
  refine frChk_of_tbl ?_
  by_cases hc : cs.all (fun c ↦ Nat.ble 1 c && Nat.blt c nFns) = true
  · rwa [← calRowsOf_eq hc]
  · simp only [frChkT, hc, Bool.false_and, Bool.or_false] at h ⊢
    exact h

end

end LeanVM.Guest.Bridge
