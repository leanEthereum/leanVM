/-
  LeanVM.Guest.B1.Link.Arith.Program

  The program side's identity: the guest's `(program, frame_program)` over the hinted split
  values is `verify_link`'s program side at `Split.ofColumns tables splitv`.
-/

module

public import LeanVM.Guest.B1.Link.Arith.Std

/-!
# The program side

`stdProgram`: the Statement's program side (`programSideG` over `swG` and `ofColumnsG`) at the
standard variables; `program_norm`: its normal forms are `gProgram stdIn`'s, by the kernel.
`tailLets_program`: at a layout of `tables()` and challenges `θ_0`, then `88` entries `f`, then
any rest, and split values `g`, `linkTail`'s `program` and `frameProgram` are `stdProgram`
evaluated at `tailIn`'s inputs (the kernel unfolds both to one term). `programIdentity` assembles
them, the lists first written in that form (`list_canon`).
-/

namespace LeanVM.Guest.B1.Link.Arith

open LeanVM.Parameters LeanVM.Guest LeanVM.Protocol.Verifier

@[expose] public section

/-- The Statement's program side at the standard variables. -/
def stdProgram : Ex × Ex :=
  programSideG (swG tables ((List.range 16).map stdIn.slot) (stdIn.gm0, stdIn.gm1) (muOf stdIn.chal)
    stdIn.etaMem stdIn.etaBc) (ofColumnsG tables ((List.range 36).map stdIn.splitv))

theorem program_norm : (gProgram stdIn).1.norm = stdProgram.1.norm ∧
    (gProgram stdIn).2.norm = stdProgram.2.norm := by decide +kernel

/-- A layout of `tables()`, its other fields given. -/
abbrev layoutOf (lm lb : ℕ) (bc : List K) (rows : List ℕ) (pl : List (Option Placement)) (sl : ℕ)
    (hts : List ℕ) : Layout := ⟨lm, lb, bc, tables, rows, pl, sl, hts⟩

section

variable (lm lb : ℕ) (bc : List K) (rows : List ℕ) (pl : List (Option Placement)) (sl : ℕ)
  (hts : List ℕ) (chunks : Chunks) (theta0 : E) (f : ℕ → E) (rest r : List E) (m1 : E)
  (fresh : List E) (g : ℕ → E) (chi qPoint message : List E)

theorem tailLets_program :
    (tailLets (layoutOf lm lb bc rows pl sl hts) chunks theta0 ((List.range 88).map f ++ rest) r m1
        fresh (Split.ofColumns tables ((List.range 36).map g)) qPoint).program =
      stdProgram.1.eval (envOf (tailIn (layoutOf lm lb bc rows pl sl hts) chunks theta0
        ((List.range 88).map f ++ rest) r m1 fresh ((List.range 36).map g) chi qPoint message)) := by
  kernel_eq

theorem tailLets_frameProgram :
    (tailLets (layoutOf lm lb bc rows pl sl hts) chunks theta0 ((List.range 88).map f ++ rest) r m1
        fresh (Split.ofColumns tables ((List.range 36).map g)) qPoint).frameProgram =
      stdProgram.2.eval (envOf (tailIn (layoutOf lm lb bc rows pl sl hts) chunks theta0
        ((List.range 88).map f ++ rest) r m1 fresh ((List.range 36).map g) chi qPoint message)) := by
  kernel_eq

end

/-- **The program side.** -/
theorem programIdentity : ProgramIdentity := by
  intro layout chunks theta0 drawn r m1 fresh splitv chi qPoint message hs
  obtain ⟨htab, hd, -, hsv, -, -⟩ := hs
  obtain ⟨lm, lb, bc, tbls, rows, pl, sl, hts⟩ := layout
  simp only at htab
  subst htab
  have hsv' : splitv.length = 36 := hsv
  rw [list_canon drawn 88 hd, list_canon_eq splitv 36 hsv']
  refine Prod.ext ?_ ?_
  · rw [gProgram_eval1, tailLets_program lm lb bc rows pl sl hts chunks theta0 _ _ r m1 fresh _ chi
      qPoint message]
    exact eval_eq_of_norm program_norm.1 _
  · rw [gProgram_eval2, tailLets_frameProgram lm lb bc rows pl sl hts chunks theta0 _ _ r m1 fresh _
      chi qPoint message]
    exact eval_eq_of_norm program_norm.2 _

end

end LeanVM.Guest.B1.Link.Arith
