/-
  LeanVM.Protocol.Relation.AgreementExtractor

  The agreement-set extractor returns a valid execution, on an accepted proof whose extracted
  history is a good run and whose queries the adversary's answers cover.
-/

module

public import LeanVM.Protocol.Relation.AvailProb
public import LeanVM.Protocol.Relation.Statements
public import LeanVM.Protocol.Whir.Sound.DescentGood
import LeanVM.Protocol.Verifier.Cost

/-!
# The agreement-set extractor is correct

From tag `formal-bus-archive`, `EndToEnd/Sound/AgreementExtractor.lean`, on Hotwire's relation.

`extractAS_valid`: without failure, on an accepted proof whose extracted history is a good run
(`GoodRun`, at the deployed opening `Whir.Params.openingIface`), when the first `ℓ₀` entries of
the log answer the seed and the cut verifier's permutations (`Avail`) and no hash entry past
`ℓ₀` answers a root the replay reads (`RootsAnswered`), `extractAS` on `ℓ₀`'s answers returns a
valid execution. The replay is the extracted run's (`replayU_cut`), the words the history's
(`committedWordC_eq`, `committedWord_eq`), the words as arrays are the lane oracles the descent
reads (`laneO_wordArrays`), the compiled descent of a good trace ends on a stack that is not bad
(`descendC_good`), and a stack that is not bad satisfies the relation, whose execution is valid
(`LinkIface.valid`).
-/

namespace LeanVM.Protocol.Relation

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom
open LeanVM.Protocol.Verifier LeanVM.Protocol.Whir LeanVM.Protocol.Whir.Sound
open LeanVM.Protocol.Whir.Params LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.KeccakHash LeanVM.Protocol.Rom

@[expose] public section

/-- **The words as arrays are the lane oracles**: lane `j` of column `v` of commitment `i`. -/
theorem laneO_wordArrays (μ R : ℕ) (cs : List (ℕ × ℕ × Word)) (i j : ℕ)
    (v : Fin (codesOf μ R i).n) :
    laneO i cs (codesOf μ R i).n j v = (((wordArrays μ R cs).getD i #[]).getD v #[]).getD j 0 := by
  unfold wordArrays laneO
  by_cases hi : i < cs.length
  · simp [List.getD_eq_getElem?_getD, hi, Array.getD_eq_getD_getElem?,
      v.isLt]
  · have hw : wordOf cs i v = [] := by
      simp [wordOf, List.getElem?_eq_none (by omega : cs.length ≤ i)]
    rw [hw]
    simp [List.getD_eq_getElem?_getD, hi, lanesOf, extRow]

variable {X : Type} {σs : Seeds X}

/-- **The extractor returns a valid execution**: without failure, on an accepted proof whose
extracted history is a good run, when the adversary's answers cover the seed and the cut
verifier's permutations and no hash entry past its log answers a root the replay reads. -/
theorem extractAS_valid (LI : LinkIface) {ℓ ℓ₀ : Log} {prog : LeanIsaProgram}
    {input : PublicInput} {π : Proof} (hf : ¬ Fail σs ℓ) (hpre : ℓ₀ <+: ℓ)
    (hv : Rom.verify (lookH ℓ) (lookF ℓ)
      (leanVmSeed (bytecodeWords prog) (publicInputDigest input))
      (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input)) π = some true)
    (hG : GoodRun openingIface LI (bytecodeWords prog) input (extractedHistory (lookH ℓ) (lookF ℓ)
      (leanVmSeed (bytecodeWords prog) (publicInputDigest input))
      (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input)) π))
    (hav : ∀ seed, (leanVmSeed (bytecodeWords prog) (publicInputDigest input)).run
      (lookH ℓ) (lookF ℓ) = some seed → Avail (bytecodeWords prog) input π ℓ ℓ₀.length seed)
    (hroots : ¬ RootsAnswered (bytecodeWords prog) input π ℓ₀ ℓ)
    {keys : List Bytes} (hkeys : Extraction.MerkleProofs.KeysCover (lookH ℓ₀) keys) :
    ∃ t, extractAS prog input (lookH ℓ₀) keys (lookF ℓ₀) π = some t ∧
      ValidExecution prog input t := by
  have hℓ₀ : ℓ₀ = ℓ.take ℓ₀.length := List.prefix_iff_eq_take.mp hpre
  have hinj : Extraction.MerkleProofs.AnswersInj (lookH ℓ₀) := by
    rw [hℓ₀]; exact answersInj_lookH (not_fail_take hf _)
  obtain ⟨seed, s, hseed, hx⟩ := xrun_of_verify hv
  obtain ⟨hseedk, hink⟩ := hav seed hseed
  rw [← hℓ₀] at hseedk hink
  obtain ⟨d, hxg⟩ := xrun_leanVmProgramG hx
  obtain ⟨s₁, h₁, -, hrep, hcomm, -⟩ := replayU_cut (F' := lookF ℓ₀) hxg (by rfl) hink
  have hrep' : replayU (lookF ℓ₀) (leanVmProgramCut (bytecodeWords prog) input)
      (startState π seed) = some ((true, d), s₁) := hrep
  -- The good run's data, at announced sizes.
  obtain ⟨l, hl, hafter, -⟩ := xrun_after _ _ _ _ _ hxg
  rw [List.nil_append] at hl
  have hgd := hG d (by rw [hl]; exact hafter)
  obtain ⟨a, l₁, l₂, -, h1, h2⟩ := after_bind_ret hafter
  obtain ⟨tr, m₁, m₂, -, -, h3⟩ := after_bind_ret h2
  obtain ⟨-, hd⟩ := after_ret_eq h3
  simp only [Prod.mk.injEq, true_and] at hd
  subst hd
  have hA : Announced (bytecodeWords prog) a.1 a.2 := returns_of_after h1
  have hadm := (announced_built hA).2
  -- At most `rootCap` roots.
  have hlen : s₁.roots.length ≤ rootCap := by
    have h2 := commits_length_le_of_costs
      (costLE_leanVmProgram (bytecodeWords prog) (publicInputDigest input))
      (after_extractedHistory (lookH ℓ) (lookF ℓ) hv).1
    rw [hcomm, List.length_map] at h2
    unfold rootCap
    omega
  have hRR : replayRoots (bytecodeWords prog) input π ℓ₀ = s₁.roots.map (·.1) := by
    simp only [replayRoots, hseedk, Option.bind_some, hrep', Option.map_some, Option.getD_some]
    exact List.take_of_length_le (by rw [List.length_map]; exact hlen)
  -- The words are the history's.
  have hcs : commits (extractedHistory (lookH ℓ) (lookF ℓ)
      (leanVmSeed (bytecodeWords prog) (publicInputDigest input))
      (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input)) π) =
      s₁.roots.map fun x ↦
        (x.2.1, x.2.2, Extraction.committedWordC (lookH ℓ₀) keys x.1 x.2.1 x.2.2) := by
    rw [hcomm]
    refine List.map_congr_left fun x hx ↦ ?_
    have hr : ∀ y, Sum.inl (y, x.1) ∉ ℓ.drop ℓ₀.length := fun y hy ↦
      hroots ⟨x.1, by rw [hRR]; exact List.mem_map_of_mem hx, y, hy⟩
    rw [Extraction.MerkleProofs.committedWordC_eq hinj hkeys, hℓ₀,
      committedWord_eq hf hr x.2.1 x.2.2]
  rw [hcs] at hgd
  -- The descent.
  have hT : traceGood (codesOf a.1.stackLog a.2) 0 (lvl0Pred a.1.stackLog (StackBad LI input a.1))
      tr (s₁.roots.map fun x ↦
        (x.2.1, x.2.2, Extraction.committedWordC (lookH ℓ₀) keys x.1 x.2.1 x.2.2)) := hgd
  obtain ⟨VA, hdesc, hnb⟩ := descendC_good hadm (StackBad LI input a.1) tr _
    (fun i j v ↦ laneO_wordArrays _ _ _ i j v) hT
  have hrel : StackRel LI input a.1 ⟨stackA a.1.stackLog VA⟩ := not_not.mp hnb
  refine ⟨_, ?_, LI.valid prog input a.1 a.2 _ hA hrel.1 hrel.2.1 hrel.2.2⟩
  simp only [extractAS, hseedk, Option.bind_some, hrep', finishAS]
  rw [hdesc]
  simp

end
end LeanVM.Protocol.Relation
