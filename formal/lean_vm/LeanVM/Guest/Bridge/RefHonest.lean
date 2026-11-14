/-
  LeanVM.Guest.Bridge.RefHonest

  The tree track against the reference run of the deployed guest: the reference memory a valid execution, its prologue to `main`'s entry, the track there at the registers, and the trace along the rest of the run under a step rule.
-/

module

public import LeanVM.Guest.Bridge.RefTrace
public import LeanVM.Guest.Bridge.TrackHonest
public import LeanVM.Prover.ExecuteComplete

/-!
# The tree track against the deployed guest's reference run

`ref_deployed`: under `MainCompleteP`, the honest memory's tree `T` and its extension `img` (`honestX`, as `honest_of_mainP`) are a valid execution of `n` steps on the statement's digest; the run passes `main`'s entry (`regs mainEntry 0`) after the prologue's `k0` steps and reaches the final registers `n - k0` steps later (`run_after`); for any alignment `al` putting `main`'s body at offset `0`, the track at `main`'s instance is at those registers (`refOk_init`), and under a step rule for `RefOk` there is a trace of track states along the run from there (`refTrace`), the `k`-th at the registers of the executor's step `k0 + k`.
-/

namespace LeanVM.Guest.Bridge

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Node
open LeanVM.Guest.End (Budget work hdrOf bytecode mainEntry publicInputOf reach_jumpTables)
open LeanVM.Guest.Budget (MainCompleteP)
open LeanVM.Prover.Exec (refMem)

public section

theorem regs_initial : regs 0 0 = Registers.initial := by
  simp only [regs, addressOfIndex, pow_zero]; rfl

/-- **The track against the deployed guest's reference run.** -/
theorem ref_deployed {b : Budget} (hm : MainCompleteP B2C.fs B2C.cert B2C.cnt b) :
    ∀ seed s w, NodeRelation bytecode seed s w → GuestLimits s w → ChildrenOk bytecode seed w →
      b.size (work s w) ≤ 2 ^ 30 →
      ∃ (rd rd0 : Reader) (T : Tree) (X : List Write) (I : Inst) (fn : Fn) (n k0 : ℕ),
        HonestAt coreProgram B2C.fs B2C.H B2C.C (hdrOf (statementDigest seed s)) T B2C.cert rd [] [] ∧
        HonestX coreProgram B2C.fs B2C.H B2C.C (hdrOf (statementDigest seed s)) T rd [] [] X ∧
        T.name = "main" ∧ I.t = T ∧ I.fp = 0 ∧ I.hdr = hdrOf (statementDigest seed s) ∧
        ValidExecution guestProgram (publicInputOf (statementDigest seed s))
          ⟨_, honestX coreProgram B2C.fs B2C.H B2C.C (hdrOf (statementDigest seed s)) T X, n⟩ ∧
        k0 ≤ n ∧
        run guestProgram (honestX coreProgram B2C.fs B2C.H B2C.C (hdrOf (statementDigest seed s)) T X) k0
          Registers.initial = some (regs mainEntry 0) ∧
        run guestProgram (honestX coreProgram B2C.fs B2C.H B2C.C (hdrOf (statementDigest seed s)) T X) (n - k0)
          (regs mainEntry 0) = some (Registers.final guestProgram) ∧
        SameStreams (T.pops coreProgram rd0)
          ((Hints.honestPushes bytecode seed s w).filter (·.1 != Hints.heapSizeStream)) ∧
        ∀ al : String → ℕ → Option (List Stmt), al "main" 0 = some fn.body →
          RefOk coreProgram rd0 (honestInsts coreProgram B2C.fs B2C.H (hdrOf (statementDigest seed s)) T) T
            (refMem (honestX coreProgram B2C.fs B2C.H B2C.C (hdrOf (statementDigest seed s)) T X)) B2C.entryOf al
            mainEntry 0 ([], [Ent.enter coreProgram I fn]) ∧
          (StepRule guestProgram (honestX coreProgram B2C.fs B2C.H B2C.C (hdrOf (statementDigest seed s)) T X)
              (Move coreProgram rd0 (honestInsts coreProgram B2C.fs B2C.H (hdrOf (statementDigest seed s)) T))
              (RefOk coreProgram rd0 (honestInsts coreProgram B2C.fs B2C.H (hdrOf (statementDigest seed s)) T) T
                (refMem (honestX coreProgram B2C.fs B2C.H B2C.C (hdrOf (statementDigest seed s)) T X)) B2C.entryOf
                al) →
            ∃ tr : ℕ → ℕ × ℕ × (List Pop × List Ent), tr 0 = (mainEntry, 0, ([], [Ent.enter coreProgram I fn])) ∧
              (∀ k < n - k0, run guestProgram
                  (honestX coreProgram B2C.fs B2C.H B2C.C (hdrOf (statementDigest seed s)) T X) k
                  (regs mainEntry 0) = some (regs (tr k).1 (tr k).2.1) ∧
                RefOk coreProgram rd0 (honestInsts coreProgram B2C.fs B2C.H (hdrOf (statementDigest seed s)) T) T
                  (refMem (honestX coreProgram B2C.fs B2C.H B2C.C (hdrOf (statementDigest seed s)) T X))
                  B2C.entryOf al (tr k).1 (tr k).2.1 (tr k).2.2) ∧
              ∀ k, k + 1 < n - k0 →
                Relation.ReflTransGen
                  (Move coreProgram rd0 (honestInsts coreProgram B2C.fs B2C.H (hdrOf (statementDigest seed s)) T))
                  (tr k).2.2 (tr (k + 1)).2.2) := by
  intro seed s w hrel hlim hok hbs
  obtain ⟨rd, rd0, T, X, -, hname, hH, hX, -, -, -, hss⟩ :=
    honest_of_mainP hm B2C.kFactsAll (B2C.cntRetemp coreProgram_fresh) seed s w hrel hlim hok hbs
  obtain ⟨I, hI, hIt, hfp, hhdr⟩ := root_inst (P := coreProgram) (fs := B2C.fs) (H := B2C.H)
    (hdr := hdrOf (statementDigest seed s)) (T := T)
  have hv := hH.valid
  rw [← hIt] at hv
  obtain ⟨fn, hf⟩ : ∃ fn, coreProgram.find? I.t.name = some fn := by
    rcases hIt' : I.t with ⟨f, σ, bufs, kids⟩ | ⟨f, σ⟩
    · rw [hIt'] at hv
      obtain ⟨fn, hf, -⟩ := hv
      exact ⟨fn, hf⟩
    · rw [hIt'] at hv; exact hv.elim
  have htr := trackOk_init (rd := rd0) hI hf hv
  rw [hIt] at htr
  set img := honestX coreProgram B2C.fs B2C.H B2C.C (hdrOf (statementDigest seed s)) T X with himg
  have hjt := B2C.jumpTables_cover hH.toHonest hX.covers hname
  have hb := hX.publicBoundary (prog := guestProgram)
  have hreach := (reach_jumpTables hjt).trans (B2C.b2_completeL B2C.b2Hyps _ rd T hname hH _ hX.covers)
  obtain ⟨n, hv'⟩ := validExecution_of_reach hb hreach
  obtain ⟨k0, hk0⟩ := reach_jumpTables hjt
  have e1 : (1 : K) = addressOfIndex 0 := by simp [addressOfIndex]
  have hn0 : run guestProgram img n (regs 0 0) = some (Registers.final guestProgram) := by
    rw [regs_initial]; exact hv'.2
  rw [e1] at hk0
  have hk0' : run guestProgram img k0 (regs 0 0) = some (regs mainEntry 0) := hk0
  have hrest := run_after hn0 rfl hk0'
  rw [regs_initial] at hk0'
  have hmain : B2C.entryOf I.t.name = mainEntry := by rw [hIt, hname]; exact B2C.entryOf_main
  refine ⟨rd, rd0, T, X, I, fn, n, k0, hH, hX, hname, hIt, hfp, hhdr, hv', hrest.1, hk0', hrest.2, hss,
    fun al hal ↦ ?_⟩
  have h0 := refOk_init (M := refMem img) (ent := B2C.entryOf) (al := al) htr hfp (by rw [hIt, hname]; exact hal)
  rw [hmain] at h0
  exact ⟨h0, fun hR ↦ refTrace hR hrest.2 h0⟩

end

end LeanVM.Guest.Bridge
