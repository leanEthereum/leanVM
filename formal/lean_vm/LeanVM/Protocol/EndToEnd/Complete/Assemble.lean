/-
  LeanVM.Protocol.EndToEnd.Complete.Assemble

  The honest run of the whole verifier program assembled from honest phases: the announcement,
  the stack's commitment, the bus, the table sumcheck, the public input, Flock, ring switching and
  the stacked opening, each following its sub-program to true data, compose into a run that
  accepts.
-/

module

public import LeanVM.Protocol.EndToEnd.Complete.Sizes
public import LeanVM.Protocol.EndToEnd.Complete.Public
public import LeanVM.Protocol.EndToEnd.Complete.Facts

/-!
# Assembling the honest run

`verifyExecution` (`LeanVM.Protocol.Verifier`, `python-verifier/verifier.py:1358-1407` at leanVM
`127510d14c98ade4e8a97646c44fa7f1ff5e752d`) is a sequence of phases. Its honest prover is the
sequence of the phases' honest scripts (`honestRun`), and the simulation composes along `bind`
(`Follows.bind`), each phase handing the next the facts it needs:

| phase | honest script | fact handed on |
| --- | --- | --- |
| `readSizes` | `announce s ρ` | the layout is `verifierLayout prog s`, the rate `ρ` |
| `commitStack` | the stack's word | the commitments are `[stackCommit μ ρ q]` |
| `verifyBusBalance` | `Phases.bus` | `BusGood` |
| `tablePhase` | `Phases.table` | the claims are true (`TrueClaims`) |
| `publicInputPhase` | `hPub` | the claims are true |
| `verifyFlock` | `Phases.flock` | `FlockGood` |
| `ringSwitch` | `Phases.ring` | the ring-switching claim holds and is multilinear |
| `verifyStackedOpening` | `Whir.Complete.honestOpening` | accepts |

`Phases` packages the four phase scripts whose proofs live in their own modules, and
`Phases.Honest` their simulation statements; `follows_verifyExecution` composes them with the
proved steps (`follows_readSizes`, `follows_commitStack`, `follows_publicInputPhase`,
`follows_verifyStackedOpening`). Between the commitment and the opening no phase commits, so
the opening runs from the commitments `[stackCommit μ ρ q]` it needs.
-/

namespace LeanVM.Protocol.EndToEnd.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.Whir.Complete

@[expose] public section

/-- The four phase scripts whose simulations are proved in their own modules: the bus, the table
sumcheck, Flock and ring switching. -/
structure Phases where
  /-- The bus phase. -/
  bus : Script BusResult
  /-- The table sumcheck, from the bus's result. -/
  table : BusResult → Script (List Verifier.ColumnClaim)
  /-- Flock. -/
  flock : Script (List E × List E)
  /-- Ring switching, from Flock's point and slices. -/
  ring : List E → List E → Script (E × (List E → E))

/-- **The phases are honest** for the stack `q`: each follows its sub-program of the verifier
program, at the verifier's layout, to true data. -/
structure Phases.Honest (prog : Program) (s : Sizes) (q : Column (leanIsaμ prog s))
    (P : Phases) : Prop where
  /-- The bus phase ends in a true result. -/
  bus : ∀ cs, Follows (fun cs' a b ↦ cs' = cs ∧ a = b ∧ BusGood prog s q b) P.bus
    (verifyBusBalance .computed (verifierLayout prog s)) cs
  /-- The table sumcheck, from a true bus result, ends in true claims. -/
  table : ∀ bus, BusGood prog s q bus → ∀ cs,
    Follows (fun cs' a b ↦ cs' = cs ∧ a = b ∧ TrueClaims prog s q b) (P.table bus)
      (tablePhase (verifierLayout prog s) bus) cs
  /-- Flock ends in its true point and slices. -/
  flock : ∀ cs, Follows (fun cs' a b ↦ cs' = cs ∧ a = b ∧ FlockGood prog s q b) P.flock
    (verifyFlock .computed (blake2sR1csLogSize + (verifierLayout prog s).tableLogHeights.getD opBlake2s 0))
    cs
  /-- Ring switching, from Flock's true result, ends in a true multilinear claim. -/
  ring : ∀ r, FlockGood prog s q r → ∀ cs,
    Follows (fun cs' a b ↦ cs' = cs ∧ a = b ∧
        StackClaim.Holds (leanIsaμ prog s) (ringSwitchClaim (verifierLayout prog s) b.1 b.2) q ∧
        IsMultilinearFn (leanIsaμ prog s) (ringSwitchClaim (verifierLayout prog s) b.1 b.2).1)
      (P.ring r.1 r.2) (ringSwitch r.1 r.2) cs

/-- The claims the opening receives from the honest run. -/
def openingClaims (prog : Program) (s : Sizes) (rs : E × (List E → E))
    (claims : List Verifier.ColumnClaim) : List StackClaim :=
  ringSwitchClaim (verifierLayout prog s) rs.1 rs.2 ::
    claims.map (·.onStack (verifierLayout prog s))

/-- **The honest run of `verify_execution`**: announce, commit, then the phases in order, then
the stacked opening of every claim the run accumulated. -/
noncomputable def honestRun (prog : Program) (s : Sizes) (ρ : ℕ) (q : Column (leanIsaμ prog s))
    (P : Phases) : Script Unit :=
  (Script.sendList (announce s ρ)).bind fun _ ↦
  (Script.commitS (stackWord (leanIsaμ prog s) q)).bind fun _ ↦
  P.bus.bind fun bus ↦
  (P.table bus).bind fun claims ↦
  (hPub prog s q).bind fun pub ↦
  P.flock.bind fun fl ↦
  (P.ring fl.1 fl.2).bind fun rs ↦
  honestOpening (leanIsaμ prog s) ρ q (openingClaims prog s rs (claims ++ pub))

/-- **The honest run follows `verify_execution`.** For sizes admissible for the program, a valid
rate, a stack satisfying `M3Holds` of the leanISA instance and honest phases, the honest run
follows the verifier program from no commitment: every `require` passes, whatever the
challenges. -/
theorem follows_verifyExecution {prog : Program} {s : Sizes} {input : PublicInput} {ρ : ℕ}
    {q : Column (leanIsaμ prog s)} (hs : s.Admissible prog) (hρ : validRate ρ)
    (hq : M3Holds (inst prog s) input q) (P : Phases) (hP : P.Honest prog s q) :
    Follows (fun _ _ _ ↦ True) (honestRun prog s ρ q P)
      (verifyExecution .computed (bytecodeWords prog) (publicDigest input)) [] := by
  have hadm := whirAdmissible prog hs hρ
  unfold verifyExecution honestRun
  simp only [Prog.bind_eq]
  refine Follows.bind (fun cs₁ _ b hb ↦ ?_) _ _ _ (follows_readSizes prog hs hρ [])
  obtain ⟨rfl, rfl⟩ := hb
  simp only [stackLog_verifierLayout]
  refine Follows.bind (fun cs₂ _ _ hc ↦ ?_) _ _ _ (follows_commitStack hadm q [])
  subst hc
  refine Follows.bind (fun cs₃ bus bus' hb ↦ ?_) _ _ _ (hP.bus _)
  obtain ⟨rfl, rfl, hbus⟩ := hb
  refine Follows.bind (fun cs₄ cl cl' hc ↦ ?_) _ _ _ (hP.table bus hbus _)
  obtain ⟨rfl, rfl, htab⟩ := hc
  refine Follows.bind (fun cs₅ pub pub' hc ↦ ?_) _ _ _ (follows_publicInputPhase hq _)
  obtain ⟨rfl, rfl, hpub⟩ := hc
  refine Follows.bind (fun cs₆ fl fl' hc ↦ ?_) _ _ _ (hP.flock _)
  obtain ⟨rfl, rfl, hfl⟩ := hc
  refine Follows.bind (fun cs₇ rs rs' hc ↦ ?_) _ _ _ (hP.ring fl hfl _)
  obtain ⟨rfl, rfl, hrh, hrm⟩ := hc
  have hall := trueClaims_append htab hpub
  refine (follows_verifyStackedOpening hadm q _ ?_ ?_)
  · intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hrh
    · obtain ⟨cl, hcl, rfl⟩ := List.mem_map.mp hc
      exact (hall cl hcl).holds
  · intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hrm
    · obtain ⟨cl, hcl, rfl⟩ := List.mem_map.mp hc
      exact (hall cl hcl).multilinear

/-! ## The whole program -/

/-- The honest prover of the whole verifier program: the honest run, then accept. -/
noncomputable def honestProver (prog : Program) (s : Sizes) (ρ : ℕ) (q : Column (leanIsaμ prog s))
    (P : Phases) : Script Unit :=
  honestRun prog s ρ q P >>= fun _ ↦ Script.ret ()

/-- The honest strategy: the replay of the honest prover from the empty history. -/
noncomputable def honestStrategy (prog : Program) (s : Sizes) (ρ : ℕ)
    (q : Column (leanIsaμ prog s)) (P : Phases) : Strategy :=
  Strategy.ofScript (honestProver prog s ρ q P) 0

/-- The honest prover follows `leanVmProgram` to `true`. -/
theorem follows_leanVmProgram {prog : Program} {s : Sizes} {input : PublicInput} {ρ : ℕ}
    {q : Column (leanIsaμ prog s)} (hs : s.Admissible prog) (hρ : validRate ρ)
    (hq : M3Holds (inst prog s) input q) (P : Phases) (hP : P.Honest prog s q) :
    Follows (fun _ _ b ↦ b = true) (honestProver prog s ρ q P)
      (leanVmProgram (bytecodeWords prog) (publicDigest input)) [] :=
  Follows.bind_of (follows_verifyExecution hs hρ hq P hP) fun _ _ _ _ ↦ rfl

/-- **The honest strategy wins every interactive run** of the verifier program, with
well-shaped words, from honest phases. -/
theorem runI_leanVmProgram_of {prog : Program} {s : Sizes} {input : PublicInput} {ρ : ℕ}
    {q : Column (leanIsaμ prog s)} (hs : s.Admissible prog) (hρ : validRate ρ)
    (hq : M3Holds (inst prog s) input q) (P : Phases) (hP : P.Honest prog s q)
    (chal : List Ev → E) :
    runI (leanVmProgram (bytecodeWords prog) (publicDigest input))
        (honestStrategy prog s ρ q P) chal = some true ∧
      shapedI (leanVmProgram (bytecodeWords prog) (publicDigest input))
        (honestStrategy prog s ρ q P) chal := by
  obtain ⟨⟨b, hb, _, _, rfl⟩, hsh⟩ := runFrom_of_follows' (h₀ := [])
    (honestStrategy prog s ρ q P) chal (ofScript_agrees _ []) (follows_leanVmProgram hs hρ hq P hP)
  exact ⟨hb, hsh⟩

end
end LeanVM.Protocol.EndToEnd.Complete
