/-
  LeanVM.Guest.Bridge.AddrChk

  The address hints' check of a function (the bus era's `addrOk`), by `decide +kernel` per function,
  and by name at the deployed alignment.
-/

module

public import LeanVM.Guest.Bridge.AllocFnLink

/-!
# The address hints' check

`addrFnChk X fs fn d`: every address hint of the advice `d` names a next frame's address `fs` cells
on, in a loop helper (`frameAddress fs`), or a cell's address below `fs` at a fixed cell below `fs` holding it
(`cellAddress q o`, the context's `statOf q = .fpg o`). The generated checks (`Bridge/AllocChk/`,
`scripts/bridge-cert/alloc.py`) state it over each function's pack data (`Fn.«k».addrFnOk`);
`addrFnJ_of` equates the two, `addrFnChk_alignA` gives it by name at `alignA`.
-/

namespace LeanVM.Guest.Bridge

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- An address hint of a function of frame size `fs`, a loop helper or not: a next frame's address
`fs` cells on, in a loop helper; a cell's address, below `fs`, at a cell below `fs` holding it (`fpg`). -/
noncomputable def addrOkX (X : AlignCtx) (fs : ℕ) (loop : Bool) : Prover.Exec.Hint → Bool
  | .frameAddress o => Nat.beq o fs && loop
  | .cellAddress q o => (match X.statOf q with
      | some (.fpg o') => Nat.beq o' o
      | _ => false) && Nat.blt o fs && Nat.blt q fs
  | _ => true

/-- **A function's address hints' check.** -/
noncomputable def addrFnChk (X : AlignCtx) (fs : ℕ) (fn : Fn) (d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)) :
    Bool :=
  d.2.2.all fun p ↦ p.2.all (addrOkX X fs fn.loop)

/-- **Compiled function `j` passes the address hints' check.** -/
def AddrFnJ (j : ℕ) : Prop := addrFnChk (ctxOf j) (B2C.fsN j) (coreOf j) (adviceOf j) = true

end

public section

/-- **A function's address hints' check from its pack's**, as `allocFnJ_of`. -/
theorem addrFnJ_of {j : ℕ} {f : CompiledFunction} {cf : Core.Fn} {C : Check.Cert} {P : B2C.Plumb}
    {ex : List (ℕ × ℕ)} {en : List (String × ℕ)} {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)} {main : Bool}
    (hf : fnOf j = f) (hcf : coreOf j = cf) (hC : certOf j = C.withPows Data.powTree) (hP : B2C.plumbOf j = P)
    (ht : (extraOf j, entsOf j, adviceOf j) = (ex, en, d)) (hm : (j == 1) = main) {n : ℕ} (hn : B2C.fsN j = n)
    (h : addrFnChk (AlignCtx.ofData C.locs ex f.entryPc main P Data.powTree Data.jtTrie en alignHalt
      f.instructionCount) n cf d = true) : AddrFnJ j := by
  simp only [Prod.mk.injEq] at ht
  obtain ⟨hex, hen, hd⟩ := ht
  have hl : (certOf j).locs = C.locs := by rw [hC]; cases C; rfl
  rw [AddrFnJ, ctxOf, hl, hex, hen, hd, hf, hcf, hP, hm, hn]
  exact h

/-- **Every core function passes the address hints' check at the deployed alignment**, from every
compiled index's. -/
theorem addrFnChk_alignA (hall : ∀ j, 1 ≤ j → j < nFns → AddrFnJ j) :
    ∀ f fn, coreProgram.find? f = some fn → addrFnChk (alignA f).X (B2C.fs f) fn (alignA f).d = true := by
  intro f fn hfn
  obtain ⟨j, hj⟩ := idxOf_of_find' hfn
  obtain ⟨i, rfl, hi, -, hfind, hcore, hfs, -, h1, h2⟩ := B2C.fn_of_idx hj
  rw [hfn] at hfind
  cases hfind
  have h := hall (i + 1) h1 h2
  rw [AddrFnJ, hcore] at h
  rw [alignA_of hj, hfs]
  exact h

end

end LeanVM.Guest.Bridge
