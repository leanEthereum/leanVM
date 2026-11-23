/-
  LeanVM.Guest.Bridge.JumpCellsDeployed

  The jump cells on the deployed guest's reference run, from every function's data check, and the trace of the tree track along the whole run.
-/

module

public import LeanVM.Guest.Bridge.JumpCellsOf
public import LeanVM.Guest.Bridge.JumpCells.All
public import LeanVM.Guest.Bridge.RefHonest

/-!
# The jump cells on the deployed guest

`jumpCells_deployed`: `jumpCells_of` with every function's data check (`JumpCells.jcData_all`), the chained `match`es' arms (`ChainArm`) the one premise left. `trace_deployed'`: `trace_deployed` for the deployed alignment (`alignA`, `progAl`, `alignA_main`), its jump cells discharged but for `ChainArm`.
-/

namespace LeanVM.Guest.Bridge

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Node
open LeanVM.Guest.End (Budget work hdrOf bytecode mainEntry)
open LeanVM.Guest.Budget (MainCompleteP)

public section

variable {hdr : E × E} {rd rd0 : Reader} {T : Tree} {κ : ℕ} {L : MemoryImage κ} {M : ℕ → E}

/-- **The jump cells of the deployed guest**, the chained `match`es' arms given. -/
theorem jumpCells_deployed (hT : T.name = "main")
    (hH : HonestAt coreProgram B2C.fs B2C.H B2C.C hdr T B2C.cert rd [] [])
    (hL : Covers coreProgram B2C.fs B2C.H B2C.C hdr T L)
    (hCh : ChainArm rd0 (honestInsts coreProgram B2C.fs B2C.H hdr T) T M alignA) {pc fp : ℕ} {done : List Pop}
    {e : Ent} {st : List Ent}
    (h : RefOk coreProgram rd0 (honestInsts coreProgram B2C.fs B2C.H hdr T) T M (entOf alignA) (alOf alignA) pc fp
      (done, e :: st)) : JumpCells L alignA e pc :=
  jumpCells_of hT hH hL (fun j h1 h2 ↦ JumpCells.jcData_all j h1 (by have : nFns = fn_count% := rfl; omega)) hCh h

/-- **The trace along the deployed guest's reference run**, the chained `match`es' arms given. -/
theorem trace_deployed' {b : Budget} (hm : MainCompleteP B2C.fs B2C.cert B2C.cnt b) :
    ∀ seed s w, NodeRelation bytecode seed s w → GuestLimits s w → ChildrenOk bytecode seed w →
      b.size (work s w) ≤ 2 ^ 30 →
      ∃ (rd rd0 : Reader) (T : Tree) (X : List Write) (I : Inst) (fn : Fn) (n k0 : ℕ),
        HonestAt coreProgram B2C.fs B2C.H B2C.C (hdrOf (statementDigest seed s)) T B2C.cert rd [] [] ∧
        HonestX coreProgram B2C.fs B2C.H B2C.C (hdrOf (statementDigest seed s)) T rd [] [] X ∧
        T.name = "main" ∧ I.t = T ∧ I.fp = 0 ∧ k0 ≤ n ∧
        run guestProgram (honestX coreProgram B2C.fs B2C.H B2C.C (hdrOf (statementDigest seed s)) T X) k0
          Registers.initial = some (regs mainEntry 0) ∧
        SameStreams (T.pops coreProgram rd0)
          (Hints.honestPushes bytecode seed s w) ∧
        (ChainArm rd0 (honestInsts coreProgram B2C.fs B2C.H (hdrOf (statementDigest seed s)) T) T
            (memOf (honestX coreProgram B2C.fs B2C.H B2C.C (hdrOf (statementDigest seed s)) T X)) alignA →
        ∃ tr : ℕ → ℕ × ℕ × (List Pop × List Ent), tr 0 = (mainEntry, 0, ([], [Ent.enter coreProgram I fn])) ∧
          (∀ k < n - k0, run guestProgram
              (honestX coreProgram B2C.fs B2C.H B2C.C (hdrOf (statementDigest seed s)) T X) k
              (regs mainEntry 0) = some (regs (tr k).1 (tr k).2.1) ∧
            RefOk coreProgram rd0 (honestInsts coreProgram B2C.fs B2C.H (hdrOf (statementDigest seed s)) T) T
              (memOf (honestX coreProgram B2C.fs B2C.H B2C.C (hdrOf (statementDigest seed s)) T X))
              (entOf alignA) (alOf alignA) (tr k).1 (tr k).2.1 (tr k).2.2) ∧
          ∀ k, k + 1 < n - k0 →
            Relation.ReflTransGen
              (Move coreProgram rd0 (honestInsts coreProgram B2C.fs B2C.H (hdrOf (statementDigest seed s)) T))
              (tr k).2.2 (tr (k + 1)).2.2) := by
  intro seed s w hrel hlim hok hbs
  obtain ⟨rd, rd0, T, X, I, fn, n, k0, hH, hX, hname, hIt, hfp, hk, hk0, hss, htr⟩ :=
    trace_deployed hm progAl alignA_main seed s w hrel hlim hok hbs
  exact ⟨rd, rd0, T, X, I, fn, n, k0, hH, hX, hname, hIt, hfp, hk, hk0, hss, fun hCh ↦
    htr fun _ _ _ _ _ h ↦ jumpCells_deployed hname hH hX.covers hCh h⟩

end

end LeanVM.Guest.Bridge
