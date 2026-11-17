/-
  LeanVM.Protocol.EndToEnd.Sound.AgreementExtractor

  The agreement-set extractor, over any near-tuple decoder: it replays the cut verifier on the
  adversary's answers, reads every level's word off them, descends from the final polynomial and
  runs level 0's stack. On an accepted proof whose extracted history is a good run, and whose
  queries the adversary's answers cover, it returns a valid execution.
-/

module

public import LeanVM.Protocol.EndToEnd.Sound.AvailProb
public import LeanVM.Protocol.Extraction.Halting
public import LeanVM.Protocol.Whir.Params.DescentCheck
public import LeanVM.Protocol.Whir.Params.Iface

/-!
# The agreement-set extractor

`extractAS D prog input H F π`, from the adversary's answers `H`, `F` and its proof `π`:

1. the seed, on `ℓ₀`'s answers;
2. the cut verifier's replay (`replayU` on `leanVmProgramCut`), which returns the announced layout
   and rate and the opening's trace, at a state holding the roots read;
3. every root's word, inverted through `ℓ₀`'s hash answers (`Extraction.committedWord`);
4. the descent from the final polynomial (`descendTrace`), each round's near tuple decoded by `D`
   on the agreement set;
5. the stack whose blocks are level 0's tuple's low parts (`tupleStack`), run as the list
   decoder's candidates are (`candidateExecution`).

`extractAS_valid`: without failure, on an accepted proof whose extracted history is a good run,
when `ℓ₀`'s answers cover the seed and the cut verifier's permutations (`Avail`) and no hash
entry past `ℓ₀` answers a root the replay reads (`RootsAnswered`), the extractor returns a valid
execution. The replay is the extracted run's (`replayU_cut`), the words the history's
(`committedWord_eq`), and the descent of a good trace ends on a stack that is not bad
(`descend_good`), whose execution is valid (`Halting.candidateExecution_of_extracted`).
-/

namespace LeanVM.Protocol.EndToEnd.Sound

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol
open LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Verifier
open LeanVM.Protocol.LeanIsa LeanVM.Protocol.Whir LeanVM.Protocol.Whir.Sound
open LeanVM.Protocol.Whir.Params LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.EndToEnd.Complete (publicInputDigest)
open LeanVM.Protocol.KeccakHash LeanVM.Protocol.Rom
open Polynomial

@[expose] public section

/-! ## Level 0's stack -/

/-- **The stack of a level-0 tuple**: block `u` is the `K`-limb of lane `u`'s low part. -/
noncomputable def tupleStack {μ : ℕ} (hμ : laneBits ≤ μ) (U : (Fin laneBits → Bool) → E[X]) :
    Column μ :=
  stackOf hμ fun u x ↦ (lowMsg (μ - laneBits) (U ((bitsEquiv laneBits).symm u)) x).limb 0

/-- A stack whose blocks are a tuple's low parts is the tuple's stack. -/
theorem tupleStack_eq {μ : ℕ} (hμ : laneBits ≤ μ) {U : (Fin laneBits → Bool) → E[X]}
    {q : Column μ} (h : ∀ u, lowMsg (μ - laneBits) (U u) = blockOf q (bitsEquiv laneBits u)) :
    tupleStack hμ U = q := by
  refine eq_of_blockOf_eq hμ fun u ↦ ?_
  rw [tupleStack, blockOf_stackOf]
  funext x
  have hx := congrFun (h ((bitsEquiv laneBits).symm u)) x
  rw [Equiv.apply_symm_apply] at hx
  rw [hx]
  simp [EndToEnd.blockOf, limb_ofK]

/-- **The descent of a good trace ends on a good stack** at the deployed parameters: the
descent returns a tuple of level 0, and its stack is not bad. -/
theorem descend_good {μ R : ℕ} (h : Whir.Admissible μ R) (D : NearDecoder)
    (Bad : Column μ → Prop) (tr : WhirTrace) (cs : List (ℕ × ℕ × Word))
    (hg : traceGood (codesOf μ R) 0 (lvl0Pred μ Bad) tr cs) :
    ∃ m T, descendTrace D (codesOf μ R) cs tr 0 = some ⟨m, T⟩ ∧
      ∃ (hm : m = laneBits) (hμ : laneBits ≤ μ), ¬ Bad (tupleStack hμ (hm ▸ T)) := by
  obtain ⟨level, rest, F⟩ := level0Facts (shapeOK_of_admissible h)
  obtain ⟨T, hd, hT, -⟩ := descendTrace_of_traceGood D (codesOf μ R) cs
    (fun i j h1 h2 ↦ codesOf_thr h i j h1 h2) tr 0 _ hg
  refine ⟨_, T, hd, ?_⟩
  simp only [lvl0Pred] at hT
  push Not at hT
  obtain ⟨hm, q, hq, hb⟩ := hT
  exact ⟨hm, F.hμ, by rwa [tupleStack_eq F.hμ hq]⟩

/-! ## The extractor -/

/-- **The agreement-set extractor**, over the near-tuple decoder `D`: from the adversary's
Keccak-256 and Keccak-f answers `H`, `F` and the proof `π`, the seed and the cut verifier's replay
on them, the roots' words through `H`, the descent of the replay's trace, and the run of level 0's
stack. -/
noncomputable def extractAS (D : NearDecoder) (prog : LeanIsaProgram) (input : PublicInput)
    (H : Bytes → Option Digest) (F : KeccakState → Option KeccakState) (π : Proof) :
    Option (Execution prog) :=
  ((leanVmSeed (bytecodeWords prog) (publicInputDigest input)).run H F).bind fun seed ↦
  (replayU F (leanVmProgramCut (bytecodeWords prog) (publicInputDigest input))
    (startState π seed)).bind fun r ↦
  if hμ : laneBits ≤ r.1.2.1.1.stackLog then
    (descendTrace D (codesOf r.1.2.1.1.stackLog r.1.2.1.2)
      (r.2.roots.map fun x ↦ (x.2.1, x.2.2, Extraction.committedWord H x.1 x.2.1 x.2.2))
      r.1.2.2 0).bind fun T ↦
    if hm : T.1 = laneBits then
      Extraction.candidateExecution prog input r.1.2.1.1 (tupleStack hμ (hm ▸ T.2)).values
    else none
  else none

/-- The candidate execution of a stack read on equal variables is the stack's. -/
theorem candidateExecution_cast {prog : LeanIsaProgram} {input : PublicInput} {L : Verifier.Layout}
    {a b : ℕ} (h : a = b) (q : Column a) :
    Extraction.candidateExecution prog input L (castColumn h q).values =
      Extraction.candidateExecution prog input L q.values := by
  subst h
  rfl

variable {X : Type} {σs : Seeds X}

/-- **The extractor returns a valid execution**: without failure, on an accepted proof whose
extracted history is a good run, when the adversary's answers cover the seed and the cut
verifier's permutations and no hash entry past its log answers a root the replay reads. -/
theorem extractAS_valid (D : NearDecoder) {ℓ ℓ₀ : Log} {prog : LeanIsaProgram}
    {input : PublicInput} {π : Proof} (hf : ¬ Fail σs ℓ) (hpre : ℓ₀ <+: ℓ)
    (hv : Rom.verify (lookH ℓ) (lookF ℓ)
      (leanVmSeed (bytecodeWords prog) (publicInputDigest input))
      (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input)) π = some true)
    (hG : stmtG openingIface prog input (extractedHistory (lookH ℓ) (lookF ℓ)
      (leanVmSeed (bytecodeWords prog) (publicInputDigest input))
      (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input)) π))
    (hav : ∀ seed, (leanVmSeed (bytecodeWords prog) (publicInputDigest input)).run
      (lookH ℓ) (lookF ℓ) = some seed →
      Avail (bytecodeWords prog) (publicInputDigest input) π ℓ ℓ₀.length seed)
    (hroots : ¬ RootsAnswered (bytecodeWords prog) (publicInputDigest input) π ℓ₀ ℓ) :
    ∃ t, extractAS D prog input (lookH ℓ₀) (lookF ℓ₀) π = some t ∧ ValidExecution prog input t := by
  have hℓ₀ : ℓ₀ = ℓ.take ℓ₀.length := List.prefix_iff_eq_take.mp hpre
  obtain ⟨seed, s, hseed, hx⟩ := xrun_of_verify hv
  obtain ⟨hseedk, hink⟩ := hav seed hseed
  rw [← hℓ₀] at hseedk hink
  obtain ⟨d, hxg⟩ := xrun_leanVmProgramG hx
  obtain ⟨s₁, h₁, -, hrep, hcomm, -⟩ := replayU_cut (F' := lookF ℓ₀) hxg (by rfl) hink
  have hrep' : replayU (lookF ℓ₀) (leanVmProgramCut (bytecodeWords prog) (publicInputDigest input))
      (startState π seed) = some ((true, d), s₁) := hrep
  -- The good run's data.
  obtain ⟨l, hl, hafter, -⟩ := xrun_after _ _ _ _ _ hxg
  rw [List.nil_append] at hl
  obtain ⟨hadm, hT⟩ := hG d (by rw [hl]; exact hafter)
  obtain ⟨hlay, hs, hwadm⟩ := hadm.choose_spec
  set s0 := hadm.choose
  -- At most `rootCap` roots.
  have hlen : s₁.roots.length ≤ rootCap := by
    have h2 := commits_length_le_of_costs
      (costLE_leanVmProgram (bytecodeWords prog) (publicInputDigest input))
      (after_extractedHistory (lookH ℓ) (lookF ℓ) hv).1
    rw [hcomm, List.length_map] at h2
    unfold rootCap
    omega
  have hRR : replayRoots (bytecodeWords prog) (publicInputDigest input) π ℓ₀ =
      s₁.roots.map (·.1) := by
    simp only [replayRoots, hseedk, Option.bind_some, hrep', Option.map_some, Option.getD_some]
    exact List.take_of_length_le (by rw [List.length_map]; exact hlen)
  -- The words are the history's.
  have hcs : commits (extractedHistory (lookH ℓ) (lookF ℓ)
      (leanVmSeed (bytecodeWords prog) (publicInputDigest input))
      (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input)) π) =
      s₁.roots.map fun x ↦ (x.2.1, x.2.2, Extraction.committedWord (lookH ℓ₀) x.1 x.2.1 x.2.2) := by
    rw [hcomm]
    refine List.map_congr_left fun x hx ↦ ?_
    have hr : ∀ y, Sum.inl (y, x.1) ∉ ℓ.drop ℓ₀.length := fun y hy ↦
      hroots ⟨x.1, by rw [hRR]; exact List.mem_map_of_mem hx, y, hy⟩
    rw [hℓ₀, committedWord_eq hf hr x.2.1 x.2.2]
  rw [hcs] at hT
  -- The descent.
  have hwadm' : Whir.Admissible (μs prog s0) d.1.2 := by rw [μs, ← hlay]; exact hwadm
  have hT' : traceGood (codesOf (μs prog s0) d.1.2) 0 (lvl0Pred (μs prog s0) (badOf prog input s0))
      d.2 (s₁.roots.map fun x ↦
        (x.2.1, x.2.2, Extraction.committedWord (lookH ℓ₀) x.1 x.2.1 x.2.2)) := hT
  obtain ⟨m, T, hdesc, hm, hμ, hnb⟩ := descend_good hwadm' D _ d.2 _ hT'
  have hM : M3Holds (leanIsaInstance prog s0) input (toI prog s0 (tupleStack hμ (hm ▸ T))) :=
    not_not.mp hnb
  obtain ⟨t, hct, hvt⟩ := Halting.candidateExecution_of_extracted hs hM
  refine ⟨t, ?_, hvt⟩
  rw [toI, candidateExecution_cast] at hct
  simp only [μs] at hdesc hμ
  simp only [extractAS, hseedk, Option.bind_some, hrep']
  rw [hlay, dite_eq_left hμ, hdesc, Option.bind_some, dite_eq_left hm]
  exact hct

end
end LeanVM.Protocol.EndToEnd.Sound
