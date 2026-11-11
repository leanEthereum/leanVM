/-
  LeanVM.Protocol.EndToEnd.Complete.Assemble

  The honest run of the whole verifier program assembled from honest phases: the announcement,
  the stack's commitment, the bus, the table sumcheck, the public input, the Keccak reduction, ring
  switching and the stacked opening, each following its sub-program to true data, compose into a
  run that accepts.
-/

module

public import LeanVM.Protocol.Verifier.Claims
public import LeanVM.Protocol.EndToEnd.Complete.Sizes
public import LeanVM.Protocol.EndToEnd.Complete.Public
public import LeanVM.Protocol.EndToEnd.Complete.Facts
public import LeanVM.Protocol.EndToEnd.Complete.KeccakPhase
public import LeanVM.Protocol.Whir.Complete.OpeningProof

/-!
# Assembling the honest run

`verifyExecution` (`LeanVM.Protocol.Verifier`, `crates/verifier/src/lib.rs:243-363` at leanVM
`f128`) is a sequence of phases. Its honest prover is the
sequence of the phases' honest scripts (`honestRun`), and the simulation composes along `bind`
(`Follows.bind`), each phase handing the next the facts it needs:

| phase | honest script | fact handed on |
| --- | --- | --- |
| `readAnnouncedSizes` | `announce s ρ` | the layout is `verifierLayout prog s`, the rate `ρ` |
| `commitStack` | the stack's word | the commitments are `[stackCommit μ ρ q]` |
| `readOod` | `hOod` | the out-of-domain claim holds and is multilinear |
| `verifyBusBalance` | `Phases.bus` | `BusGood`; its claims are on the framework's columns |
| `tablePhase` | `Phases.table` | the claims are true, the output lanes' the honest ones |
| `publicInputPhase` | `hPub` | the claims are true, on the memory columns |
| `keccakPhase` | `Phases.keccak` | true claims on no output lane, the true slices of `q_keccak` |
| `ringSwitch` | `Phases.ring` | the ring-switching claim holds and is multilinear |
| `verifyStackedOpening` | `Whir.Complete.honestOpening` | accepts (`openingComplete`) |

`Phases` packages the four phase scripts whose proofs live in their own modules, and
`Phases.Honest` their simulation statements; `follows_verifyExecution` composes them with the
proved steps (`follows_readSizes`, `follows_commitStack`, `follows_readOod`,
`follows_publicInputPhase`, `follows_verifyStackedOpening`). The stacked opening's completeness is
`Whir.Complete.openingComplete` (`Whir.Complete.OpeningProof`); the opening receives
at most `maxStackedClaims` claims (`length_openingClaims_le`). The bus's and the public input's claims are on the framework's
columns whatever the run (`retOK_busColumns`, `retOK_publicColumns`, through `follows_retOK`), so
the claims on the output lanes the Keccak phase checks are the table's. Between the commitment and
the opening no phase commits, so the opening runs from the commitments `[stackCommit μ ρ q]` it
needs.
-/

namespace LeanVM.Protocol.EndToEnd.Complete

open LeanVM.Prover (Script)

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.Whir.Complete

@[expose] public section

/-- The four phase scripts whose simulations are proved in their own modules: the bus, the table
sumcheck, the Keccak phase and ring switching. -/
structure Phases where
  /-- The bus phase. -/
  bus : Script BusResult
  /-- The table sumcheck, from the bus's result. -/
  table : BusResult → Script (List Verifier.ColumnClaim)
  /-- The Keccak phase, from the claims so far. -/
  keccak : List Verifier.ColumnClaim → Script (List Verifier.ColumnClaim × List E × List E)
  /-- Ring switching, from the Keccak phase's point and slices. -/
  ring : List E → List E → Script (E × (List E → E))

/-- **The phases are honest** for the stack `q`: each follows its sub-program of the verifier
program, at the verifier's layout, to true data. -/
structure Phases.Honest (prog : LeanIsaProgram) (s : Sizes) (q : Column (leanIsaμ prog s))
    (P : Phases) : Prop where
  /-- The bus phase ends in a true result. -/
  bus : ∀ cs, Follows (fun cs' a b ↦ cs' = cs ∧ a = b ∧ BusGood prog s q b) P.bus
    (verifyBusBalance computedBytecodeValue (verifierLayout prog s)) cs
  /-- The table sumcheck, from a true bus result, ends in true claims, its claims on the output
  lanes the honest ones. -/
  table : ∀ bus, BusGood prog s q bus → ∀ cs,
    Follows (fun cs' a b ↦ cs' = cs ∧ a = b ∧ TrueClaims prog s q b ∧
        ∃ tc, b = bus.claims ++ tc ∧ tc.length = 153 ∧ ∃ z : Vector E (s.τ 5),
          tc.filter (fun c ↦ c.column ∈ keccakOutputColumns) = honestLanes prog s q z)
      (P.table bus) (tablePhaseClaims (verifierLayout prog s) bus) cs
  /-- The Keccak phase, from true claims whose output lanes are the honest ones, ends in true
  claims on no output lane and the true slices of `q_keccak`. -/
  keccak : ∀ claims, TrueClaims prog s q claims → ∀ z : Vector E (s.τ 5),
    lanesOf claims = honestLanes prog s q z → ∀ cs,
    Follows (fun cs' a b ↦ cs' = cs ∧ a = b ∧
        (∀ c ∈ b.1, TrueClaim prog s q c ∧ c.column ∉ keccakOutputColumns) ∧
        KeccakGkr.slicesTrue (s.τ 5) (qkH prog s q) b.2.1 b.2.2 ∧ b.1.length ≤ claims.length + 1)
      (P.keccak claims) (keccakPhaseClaims (verifierLayout prog s) claims) cs
  /-- Ring switching, from the true slices, ends in a true multilinear claim. -/
  ring : ∀ r : List E × List E, KeccakGkr.slicesTrue (s.τ 5) (qkH prog s q) r.1 r.2 → ∀ cs,
    Follows (fun cs' a b ↦ cs' = cs ∧ a = b ∧
        StackClaim.Holds (leanIsaμ prog s) (ringSwitchClaim (verifierLayout prog s) b.1 b.2) q ∧
        IsMultilinearFn (leanIsaμ prog s) (ringSwitchClaim (verifierLayout prog s) b.1 b.2).1)
      (P.ring r.1 r.2) (ringSwitch r.1 r.2) cs

/-- The claims the opening receives from the honest run: the ring-switching claim, the column
claims, then the commitment's out-of-domain claim. -/
def openingClaims (prog : LeanIsaProgram) (s : Sizes) (rs : E × (List E → E))
    (claims : List Verifier.ColumnClaim) (ood : StackClaim) : List StackClaim :=
  ringSwitchClaim (verifierLayout prog s) rs.1 rs.2 ::
    claims.map (·.stackClaim (verifierLayout prog s)) ++ [ood]

/-- **The honest run of `verify_execution`**: announce, commit, take the commitment's
out-of-domain sample, then the phases in order, then the stacked opening of every claim the run
accumulated. -/
noncomputable def honestRun (prog : LeanIsaProgram) (s : Sizes) (ρ : ℕ) (q : Column (leanIsaμ
    prog s))
    (P : Phases) : Script Unit :=
  (Script.sendList (announce s ρ)).bind fun _ ↦
  (Script.commitS (stackWord (leanIsaμ prog s) ρ q)).bind fun _ ↦
  (hOod q).bind fun ood ↦
  P.bus.bind fun bus ↦
  (P.table bus).bind fun claims ↦
  (hPub prog s q).bind fun pub ↦
  (P.keccak (claims ++ pub)).bind fun kr ↦
  (P.ring kr.2.1 kr.2.2).bind fun rs ↦
  honestOpening (leanIsaμ prog s) ρ q (openingClaims prog s rs kr.1 ood)

/-- **The honest run follows `verify_execution`.** For sizes admissible for the program, a valid
rate, a stack satisfying `M3Holds` of the leanISA instance, honest phases and the stacked opening's
completeness, the honest run follows the verifier program from no commitment: every `require`
passes, whatever the challenges. -/
theorem follows_verifyExecution {prog : LeanIsaProgram} {s : Sizes}
    {input : PublicInput} {ρ : ℕ} {q : Column (leanIsaμ prog s)} (hs : s.Admissible prog)
    (hρ : validRate ρ) (hq : M3Holds (inst prog s) input q) (P : Phases) (hP : P.Honest prog s q) :
    Follows (fun _ _ _ ↦ True) (honestRun prog s ρ q P)
      (verifyExecutionClaims computedBytecodeValue (bytecodeWords prog) (publicInputDigest input))
          [] := by
  have hadm := whirAdmissible prog hs hρ
  unfold verifyExecutionClaims honestRun
  simp only [VerifierProgram.bind_eq]
  refine Follows.bind (fun cs₁ _ b hb ↦ ?_) _ _ _ (follows_readSizes prog hs hρ [])
  obtain ⟨rfl, rfl⟩ := hb
  simp only [stackLog_verifierLayout]
  refine Follows.bind (fun cs₂ _ _ hc ↦ ?_) _ _ _ (follows_commitStack hadm q [])
  subst hc
  refine Follows.bind (fun cs₂' ood ood' hc ↦ ?_) _ _ _ (follows_readOod q _)
  obtain ⟨rfl, rfl, hoh, hom⟩ := hc
  refine Follows.bind (fun cs₃ bus bus' hb ↦ ?_) _ _ _
    (follows_retOK _ _ _ (hP.bus _) (retOK_busColumns _))
  obtain ⟨⟨rfl, rfl, hbus⟩, hbcol⟩ := hb
  refine Follows.bind (fun cs₄ cl cl' hc ↦ ?_) _ _ _ (hP.table bus hbus _)
  obtain ⟨rfl, rfl, htab, tc, rfl, htc, z, hz⟩ := hc
  refine Follows.bind (fun cs₅ pub pub' hc ↦ ?_) _ _ _
    (follows_retOK _ _ _ (follows_publicInputPhase hq _) (retOK_publicColumns _ _))
  obtain ⟨⟨rfl, rfl, hpub, hpl⟩, hpcol⟩ := hc
  refine Follows.bind (fun cs₆ kr kr' hc ↦ ?_) _ _ _
    (hP.keccak _ (trueClaims_append htab hpub) z
      (lanesOf_honest prog s q hbcol hpcol z hz) _)
  obtain ⟨rfl, rfl, hkc, hsl, hkl⟩ := hc
  refine Follows.bind (fun cs₇ rs rs' hc ↦ ?_) _ _ _ (hP.ring (kr.2.1, kr.2.2) hsl _)
  obtain ⟨rfl, rfl, hrh, hrm⟩ := hc
  refine (follows_verifyStackedOpening Whir.Complete.openingComplete hadm q _ ?_ ?_ ?_)
  · have hl : (openingClaims prog s rs kr.1 ood).length = kr.1.length + 2 := by
      simp [openingClaims]
    rw [hl]
    simp only [List.length_append, hbus.claims_length, htc, hpl] at hkl
    simp only [maxStackedClaims]
    omega
  · intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · rcases List.mem_cons.mp hc with rfl | hc
      · exact hrh
      · obtain ⟨cl, hcl, rfl⟩ := List.mem_map.mp hc
        exact (hkc cl hcl).1.holds (hkc cl hcl).2
    · rw [List.mem_singleton.mp hc]
      exact hoh
  · intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · rcases List.mem_cons.mp hc with rfl | hc
      · exact hrm
      · obtain ⟨cl, hcl, rfl⟩ := List.mem_map.mp hc
        exact (hkc cl hcl).1.multilinear (hkc cl hcl).2
    · rw [List.mem_singleton.mp hc]
      exact hom

/-! ## The whole program -/

/-- The honest prover of the whole verifier program: the honest run, then accept. -/
noncomputable def honestProver (prog : LeanIsaProgram) (s : Sizes) (ρ : ℕ) (q : Column (leanIsaμ
    prog s))
    (P : Phases) : Script Unit :=
  honestRun prog s ρ q P >>= fun _ ↦ Script.ret ()

/-- The honest strategy: the replay of the honest prover from the empty history. -/
noncomputable def honestStrategy (prog : LeanIsaProgram) (s : Sizes) (ρ : ℕ)
    (q : Column (leanIsaμ prog s)) (P : Phases) : Strategy :=
  Strategy.ofScript (honestProver prog s ρ q P) 0

/-- The honest prover follows `leanVmVerifierProgram` to `true`. -/
theorem follows_leanVmProgram {prog : LeanIsaProgram} {s : Sizes}
    {input : PublicInput} {ρ : ℕ}
    {q : Column (leanIsaμ prog s)} (hs : s.Admissible prog) (hρ : validRate ρ)
    (hq : M3Holds (inst prog s) input q) (P : Phases) (hP : P.Honest prog s q) :
    Follows (fun _ _ b ↦ b = true) (honestProver prog s ρ q P)
      (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input)) [] := by
  rw [leanVmProgram_eq]
  exact Follows.bind_of (follows_verifyExecution hs hρ hq P hP) fun _ _ _ _ ↦ rfl

/-- **The honest strategy wins every interactive run** of the verifier program, with
well-shaped words, from honest phases. -/
theorem runI_leanVmProgram_of {prog : LeanIsaProgram} {s : Sizes}
    {input : PublicInput} {ρ : ℕ}
    {q : Column (leanIsaμ prog s)} (hs : s.Admissible prog) (hρ : validRate ρ)
    (hq : M3Holds (inst prog s) input q) (P : Phases) (hP : P.Honest prog s q)
    (chal : List Ev → E) :
    runI (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input))
        (honestStrategy prog s ρ q P) chal = some true ∧
      shapedI (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input))
        (honestStrategy prog s ρ q P) chal := by
  unfold runI shapedI
  -- No local of type `ShapedFrom …`: under 4.35 the elaborator and the linters would unfold the run.
  have h := runFrom_of_follows' (h₀ := []) (H := honestProver prog s ρ q P)
    (honestStrategy prog s ρ q P) chal (ofScript_agrees (honestProver prog s ρ q P) [])
    (follows_leanVmProgram hs hρ hq P hP)
  refine ⟨?_, by with_reducible exact h.2⟩
  obtain ⟨b, hb, -, -, hbt⟩ := h.1
  rw [← hbt]
  with_reducible exact hb

end
end LeanVM.Protocol.EndToEnd.Complete
