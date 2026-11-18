/-
  LeanVM.Protocol.EndToEnd.Sound.ExtractorC

  The agreement-set extractor, computable: the descent over values, level 0's stack read off its
  values on `U_κ`. It is the extractor over the decoder the descent's decoder over values
  evaluates.
-/

module

public import LeanVM.Protocol.EndToEnd.Sound.AgreementExtractor
public import LeanVM.Protocol.Whir.Sound.DescentV

/-!
# The agreement-set extractor, computed

`extractASC`: the seed and the cut verifier's replay, the roots' words through the computed leaves
(`Extraction.committedWordC`), the descent over values (`Whir.Sound.descendTraceV`), and level 0's
stack, whose block `u` is the low part of lane `u`, read off its values on `U_κ` through the
inverse transform (`stackV`). Every step is computable when the decoder over values is. It is
`extractAS` over the decoder (`extractASC_eq`): the descent over values is its descent, evaluated
(`descendTraceV_eq`), and
the low parts are the inverse transforms of the values (`lowMsg_eq_novelInvE`).
-/

namespace LeanVM.Protocol.EndToEnd.Sound

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Verifier LeanVM.Protocol.Whir LeanVM.Protocol.Whir.Sound
  LeanVM.Protocol.Whir.Params LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.EndToEnd.Complete (publicInputDigest)
open Polynomial

@[expose] public section

/-- **Level 0's stack from its values**: block `u` is the `K`-limb of the low part of lane `u`,
the inverse transform of its values on `U_κ`. -/
def stackV {μ : ℕ} (hμ : laneBits ≤ μ) {n : ℕ} (hn : 2 ^ (μ - laneBits) ≤ n)
    (V : (Fin laneBits → Bool) → Fin n → E) : Column μ :=
  stackOf hμ fun u x ↦ ((novelInvE (μ - laneBits) (Array.ofFn fun v : Fin (2 ^ (μ - laneBits)) ↦
    V ((bitsEquiv laneBits).symm u) (Fin.castLE hn v))).getD (bitsToNat x) 0).limb 0

theorem stackV_valsT {μ : ℕ} (hμ : laneBits ≤ μ) (P : LevelCode) (hn : 2 ^ (μ - laneBits) ≤ P.n)
    (T : (Fin laneBits → Bool) → E[X]) : stackV hμ hn (valsT P.dom T) = tupleStack hμ T := by
  have h64 : μ - laneBits ≤ 64 := by
    have h1 : 2 ^ (μ - laneBits) ≤ 2 ^ 64 :=
      hn.trans (Nat.pow_le_pow_right (by norm_num) P.h64)
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h1
  have hv : ∀ u, (Array.ofFn fun v : Fin (2 ^ (μ - laneBits)) ↦
      valsT P.dom T u (Fin.castLE hn v)) = valsU (μ - laneBits) (T u) := fun u ↦ rfl
  unfold stackV tupleStack
  simp only [hv]
  congr 1
  funext u x
  rw [lowMsg_eq_novelInvE h64]

variable {D : NearDecoder} (W : ValsDecoder D)

/-- The extractor after the replay: the roots' words, the descent over values, level 0's stack
and its execution, from the replay's value and state. -/
def finishAS (prog : LeanIsaProgram) (input : PublicInput) (H : Bytes → Option Digest)
    (keys : List Bytes) (r : (Bool × ((Verifier.Layout × ℕ) × WhirTrace)) × VerifierProgramState) :
    Option (Execution prog) :=
  if hμ : laneBits ≤ r.1.2.1.1.stackLog then
    if hn : 2 ^ (r.1.2.1.1.stackLog - laneBits) ≤ (codesOf r.1.2.1.1.stackLog r.1.2.1.2 0).n then
      (descendTraceV W (codesOf r.1.2.1.1.stackLog r.1.2.1.2)
        (r.2.roots.map fun x ↦ (x.2.1, x.2.2, Extraction.committedWordC H keys x.1 x.2.1 x.2.2))
        r.1.2.2 0).bind fun T ↦
      if hm : T.1 = laneBits then
        Extraction.candidateExecution prog input r.1.2.1.1 (stackV hμ hn (hm ▸ T.2)).values
      else none
    else none
  else none

/-- **The agreement-set extractor, computed.** -/
def extractASC (prog : LeanIsaProgram) (input : PublicInput) (H : Bytes → Option Digest)
    (keys : List Bytes) (F : KeccakState → Option KeccakState) (π : Proof) :
    Option (Execution prog) :=
  ((leanVmSeed (bytecodeWords prog) (publicInputDigest input)).run H F).bind fun seed ↦
  (replayU F (leanVmProgramCut (bytecodeWords prog) (publicInputDigest input))
    (startState π seed)).bind (finishAS W prog input H keys)

/-- **The computed extractor is the extractor over the decoder.** -/
theorem extractASC_eq (prog : LeanIsaProgram) (input : PublicInput) (H : Bytes → Option Digest)
    (keys : List Bytes) (F : KeccakState → Option KeccakState) (π : Proof) :
    extractASC W prog input H keys F π = extractAS D prog input H keys F π := by
  unfold extractASC extractAS finishAS
  refine congrArg _ (funext fun seed ↦ congrArg _ (funext fun r ↦ ?_))
  by_cases hμ : laneBits ≤ r.1.2.1.1.stackLog
  · rw [dite_eq_left hμ, dite_eq_left hμ]
    by_cases hn : 2 ^ (r.1.2.1.1.stackLog - laneBits) ≤ (codesOf r.1.2.1.1.stackLog r.1.2.1.2 0).n
    · rw [dite_eq_left hn, ite_eq_left hn, descendTraceV_eq W, Option.bind_map]
      refine congrArg _ (funext fun T ↦ ?_)
      obtain ⟨k, T⟩ := T
      simp only [Function.comp, valsS]
      by_cases hm : k = laneBits
      · subst hm
        refine (dite_eq_left (c := laneBits = laneBits) rfl).trans ?_
        refine Eq.trans ?_ (dite_eq_left (c := laneBits = laneBits) rfl).symm
        exact congrArg (fun q : Column _ ↦ Extraction.candidateExecution prog input
          r.1.2.1.1 q.values) (stackV_valsT hμ _ hn T)
      · simp only [hm, ↓reduceDIte]
    · simp only [hn, ↓reduceDIte, ↓reduceIte]
  · simp only [hμ, ↓reduceDIte]

end
end LeanVM.Protocol.EndToEnd.Sound
