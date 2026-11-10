/-
  LeanVM.Wire.Honest

  The honest prover's proofs survive their encoding: `WireDecodable` with the hash they were
  proved with, so the round trip (`LeanVM.Wire.roundTrip`) applies to them.
-/

import LeanVM.Prover.Assemble
import LeanVM.Wire.HonestRun

/-!
# The honest prover's proofs are decodable

`Prover.proveWithHash`, on a valid execution within the cap at a valid rate, is the
specification's honest prover (`proveM`) at the execution's witness with the strategy
`leanVmProver` (`proveWithHash_eq_proveM`, from `corr_honestScript` as `prove_eq_honestComp`
uses it), in any monad; otherwise it makes no proof (`proveWithHash_eq_none`). The strategy wins
against every challenge (`runI_leanVmProgram`), so along its run every committed word is well
shaped (`Strategy.AcceptsFrom`), and the verifier program's openings are within the wire bounds
(`wired_leanVmProgram`). Hence (`proveFrom_phases`, `phaseDecodable_openingAt`,
`proveFrom_stream_le`):

* `proveWithHash_wireDecodable`: a proof of `Prover.proveWithHash (m := Id) h F` is
  `WireDecodable h`: its stream is at most `leanVmCost = 53036` elements, at most
  `wireMaxPhases` phases, each the openings of one tree over `h` within the bounds.

The pruning idea and its formalization on leanerVM's main branch are scaraven's
(https://github.com/scaraven).
-/

namespace LeanVM.Wire

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Protocol.LeanIsa
open LeanVM.Protocol.EndToEnd.Complete LeanVM.Protocol.KeccakHash
open LeanVM.Prover (proveWithHash witness? witness?_spec isSome_witness?_iff corr_honestScript
  runScript_corr runScript_eq_proveM traceSizes traceWitness childFor_trace)

section Monadic

variable {m : Type → Type} [Monad m] (H : Bytes → m Digest) (F : KeccakState → m KeccakState)
  {prog : LeanIsaProgram} {input : PublicInput} {t : Execution prog} {ρ : ℕ}

/-- **The honest prover is the specification's** at the execution's witness, in any monad: on a
valid execution within the cap at a valid rate, `proveWithHash` is `proveM` with the strategy
`leanVmProver` from the seed. -/
theorem proveWithHash_eq_proveM (hv : ValidExecution prog input t)
    (hcap : t.committedSize ≤ 2 ^ 28) (hρ : 1 ≤ ρ ∧ ρ ≤ 4) (fuel : ℕ) :
    proveWithHash H F prog input t ρ fuel =
      seedWithHash H F (bytecodeWords prog) (publicInputDigest input) >>= fun seed ↦
        proveM H F (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input))
          (leanVmProver prog (traceSizes prog input t) ρ
            (stackOf prog (traceSizes prog input t) (traceWitness prog input t))) seed fuel := by
  obtain ⟨W, hW, hspec⟩ := witness?_spec hv hcap
  simp only [proveWithHash, hW, hρ, and_self, ↓reduceIte]
  refine congrArg (fun k : KeccakState → m (Option Proof) ↦
    seedWithHash H F (bytecodeWords prog) (publicInputDigest input) >>= k)
    (funext fun seed ↦ ?_)
  rw [runScript_corr H F fuel _ (corr_honestScript hv hcap hρ hspec) seed, runScript_eq_proveM]
  rfl

/-- **Otherwise the honest prover makes no proof.** -/
theorem proveWithHash_eq_none
    (h : ¬ (ValidExecution prog input t ∧ t.committedSize ≤ 2 ^ 28 ∧ 1 ≤ ρ ∧ ρ ≤ 4))
    (fuel : ℕ) : proveWithHash H F prog input t ρ fuel = pure none := by
  unfold proveWithHash
  cases hW : witness? prog input t with
  | none => rfl
  | some W =>
    have hs := (isSome_witness?_iff prog input t).mp (by rw [hW]; rfl)
    have hρ : ¬ (1 ≤ ρ ∧ ρ ≤ 4) := fun hρ ↦ h ⟨hs.1, hs.2, hρ⟩
    simp only [hρ, ↓reduceIte]

end Monadic

/-- A strategy that wins every interactive run, committing well-shaped words, wins from the
start for every choice of the challenges (`Strategy.acceptsFrom_of_runFrom`, stated on `runI`
so that a concrete program is not unfolded). -/
theorem acceptsFrom_of_runI {S : Strategy} {P : VerifierProgram Bool}
    (h1 : ∀ chal, runI P S chal = some true) (h2 : ∀ chal, shapedI P S chal) :
    S.AcceptsFrom P [] :=
  Strategy.acceptsFrom_of_runFrom P [] h1 h2

/-- The facts of the leanVM verifier program and the strategy `leanVmProver` the proofs below
use, on a valid execution within the cap at a valid rate: the strategy wins every interactive run
with well-shaped words, the program's openings are within the wire bounds, and its cost is at
most `leanVmCost`. Stated for any program equal to the verifier's, so that the proofs below work
on an abstract program (unfolding the concrete one is costly). -/
theorem leanVm_honest_facts {prog : LeanIsaProgram} {input : PublicInput}
    {t : Execution prog} {ρ : ℕ} (hv : ValidExecution prog input t)
    (hcap : t.committedSize ≤ 2 ^ 28) (hρ : 1 ≤ ρ ∧ ρ ≤ 4) :
    ∃ P, P = leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input) ∧
      (∀ chal, runI P (leanVmProver prog (traceSizes prog input t) ρ
          (stackOf prog (traceSizes prog input t) (traceWitness prog input t))) chal =
          some true) ∧
      (∀ chal, shapedI P (leanVmProver prog (traceSizes prog input t) ρ
          (stackOf prog (traceSizes prog input t) (traceWitness prog input t))) chal) ∧
      Wired P [] wireMaxPhases (fun _ _ _ ↦ True) ∧ P.CostLE costHeight leanVmCost := by
  obtain ⟨⟨-, hw, hs, hadm, -⟩, -⟩ := childFor_trace hv hcap hρ
  have hq := m3Honest_stackOf hw hs
  -- The run's two parts are taken only once the program is abstract: under 4.35 a local of type
  -- `shapedI` on the concrete program makes the elaborator unfold it.
  have hr := fun chal ↦ runI_leanVmProgram (input := input) hadm hρ hq chal
  have hwi := wired_leanVmProgram (bytecodeWords prog) (publicInputDigest input)
  have hc := costLE_leanVmProgram (bytecodeWords prog) (publicInputDigest input)
  generalize hP : leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input) = P
    at hr hwi hc
  exact ⟨P, rfl, fun chal ↦ (hr chal).1, fun chal ↦ (hr chal).2, hwi, hc⟩

theorem id_run_eq {α : Type} (x : Id α) : Id.run x = x := rfl

/-- **The honest prover at `Id` is the pure prover** `prove` with the strategy `leanVmProver`,
from the seed. -/
theorem proveWithHash_id_eq_prove (h : Bytes → Digest) (F : KeccakState → KeccakState)
    {prog : LeanIsaProgram} {input : PublicInput} {t : Execution prog} {ρ : ℕ}
    (hv : ValidExecution prog input t) (hcap : t.committedSize ≤ 2 ^ 28) (hρ : 1 ≤ ρ ∧ ρ ≤ 4)
    (fuel : ℕ) :
    Prover.proveWithHash (m := Id) h F prog input t ρ fuel =
      prove h F (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input))
        (leanVmProver prog (traceSizes prog input t) ρ
          (stackOf prog (traceSizes prog input t) (traceWitness prog input t)))
        (F (seedInput (h (versionTag ++ (bytecodeWords prog).flatMap K.toBytes))
          (publicInputDigest input))) fuel := by
  rw [proveWithHash_eq_proveM (m := Id) h F hv hcap hρ fuel]
  change Id.run (_ >>= _) = _
  rw [Id.run_bind, proveM_id, id_run_eq]
  rfl

section Abstract

variable {h : Bytes → Digest} {F : KeccakState → KeccakState} {S : Strategy}
  {P : VerifierProgram Bool} {fuel : ℕ} {Q : Bool → List (ℕ × ℕ) → ℕ → Prop}

/-- **A proof of the pure honest prover is decodable**, for a winning strategy against a program
whose openings are within the wire bounds and whose cost is at most `leanVmCost`. -/
theorem prove_wireDecodable (h1 : ∀ chal, runI P S chal = some true)
    (h2 : ∀ chal, shapedI P S chal) (hw : Wired P [] wireMaxPhases Q)
    (hc : P.CostLE costHeight leanVmCost) {seed : KeccakState} {p : Proof}
    (hp : prove h F P S seed fuel = some p) : WireDecodable h p := by
  have hacc : S.AcceptsFrom P [] := Strategy.acceptsFrom_of_runFrom P [] h1 h2
  obtain ⟨⟨xs, os⟩, hpf, rfl⟩ := Option.map_eq_some_iff.mp hp
  obtain ⟨hlen, hph⟩ := proveFrom_phases h F S fuel _ _ [] wireMaxPhases hacc
    (by simp [commits]) hw hpf
  have hxs := proveFrom_stream_le h F S fuel _ _ [] _ hc hpf
  have hcost : leanVmCost = 53036 := by decide
  refine ⟨lt_of_le_of_lt (hcost ▸ hxs) (by norm_num), hlen, fun phase hphase ↦ ?_⟩
  obtain ⟨ht, w, word, ps, rfl, hws, hne, hql, hht, hwl, hps⟩ := hph phase hphase
  exact ⟨ht, w, phaseDecodable_openingAt hws hne hql hht hwl hps⟩

end Abstract

/-- **The honest prover's proofs are decodable** with the hash they were proved with. -/
theorem proveWithHash_wireDecodable {h : Bytes → Digest} {F : KeccakState → KeccakState}
    {prog : LeanIsaProgram} {input : PublicInput} {t : Execution prog} {ρ fuel : ℕ} {p : Proof}
    (hp : Prover.proveWithHash (m := Id) h F prog input t ρ fuel = some p) : WireDecodable h p := by
  by_cases hcond : ValidExecution prog input t ∧ t.committedSize ≤ 2 ^ 28 ∧ 1 ≤ ρ ∧ ρ ≤ 4
  · obtain ⟨hv, hcap, hρ⟩ := hcond
    rw [proveWithHash_id_eq_prove h F hv hcap hρ fuel] at hp
    obtain ⟨P, hP, h1, h2, hw, hc⟩ := leanVm_honest_facts hv hcap hρ
    rw [← hP] at hp
    exact prove_wireDecodable h1 h2 hw hc hp
  · rw [proveWithHash_eq_none (m := Id) h F hcond fuel] at hp
    cases hp

end LeanVM.Wire
