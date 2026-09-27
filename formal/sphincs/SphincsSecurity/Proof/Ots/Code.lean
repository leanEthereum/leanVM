import SphincsSecurity.Scheme
import SphincsSecurity.Proof.Base.Prelude
import Mathlib.Tactic.IrreducibleDef

/-!
# The one-time-signature code

Everything the proof knows about the Winternitz code of `Scheme.lean`: which words are valid, how a digest decodes, that two valid words are incomparable, and how many valid words sit one backward step below a given one. The rest of the proof reaches the code only through these names. The definitions are sealed, so no proof elsewhere can depend on how the current target-sum code computes; another code with the same facts only changes this module.
-/

namespace SphincsSecurity

namespace OtsCode

open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

irreducible_def Valid (x : Encoding) : Prop := TargetSum.Valid x

def decode (digest : Digest) : Option Encoding := TargetSum.decodeDigest digest

theorem decode_def (digest : Digest) : decode digest = TargetSum.decodeDigest digest := rfl

attribute [irreducible] decode

theorem decode_valid {digest : Digest} {word : Encoding} (hdecode : decode digest = some word) : Valid word := by
  rw [decode_def] at hdecode
  rw [Valid_def]
  by_cases hvalid : TargetSum.Valid (TargetSum.digestEncoding digest)
  · rw [TargetSum.decodeDigest, if_pos hvalid] at hdecode
    exact Option.some.inj hdecode ▸ hvalid
  · rw [TargetSum.decodeDigest, if_neg hvalid] at hdecode
    simp at hdecode

private theorem digestEncoding_injective {left right : Digest}
    (hencoding : TargetSum.digestEncoding left = TargetSum.digestEncoding right) : left = right := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit hbit
  let chainIdx : ChainIndex := ⟨bit / 2, by
    have := hbit
    norm_num [digestBits, numChains] at *
    omega⟩
  have hchain := congrFun hencoding chainIdx
  change (left.extractLsb' (TargetSum.digitOffset chainIdx) winternitzBits).toFin =
    (right.extractLsb' (TargetSum.digitOffset chainIdx) winternitzBits).toFin at hchain
  have hword := BitVec.toFin_injective hchain
  have hwithin : bit - 2 * chainIdx.val < winternitzBits := by
    dsimp only [chainIdx]
    norm_num [winternitzBits]
    omega
  have hwithin2 : bit - 2 * chainIdx.val < 2 := by simpa [winternitzBits] using hwithin
  have hbitEq := congrArg (fun word : BitVec winternitzBits =>
    word.getLsbD (bit - 2 * chainIdx.val)) hword
  simpa only [TargetSum.digestEncoding, TargetSum.digitOffset, winternitzBits,
    BitVec.getLsbD_extractLsb', hwithin2, decide_true, Bool.true_and,
    show 2 * chainIdx.val + (bit - 2 * chainIdx.val) = bit by
      dsimp only [chainIdx]
      omega] using hbitEq

theorem decode_some_injective {left right : Digest} {word : Encoding}
    (hleft : decode left = some word) (hright : decode right = some word) : left = right := by
  rw [decode_def, TargetSum.decodeDigest] at hleft hright
  split at hleft <;> split at hright
  · exact digestEncoding_injective ((Option.some.inj hleft).trans (Option.some.inj hright).symm)
  all_goals simp at hleft hright

/-- Two valid words cannot be ordered componentwise unless they are equal: walking chains forward from a revealed word never reaches another valid word. -/
theorem eq_of_le_of_valid {x y : Encoding} (hx : Valid x) (hy : Valid y)
    (hle : ∀ i, (x i).val ≤ (y i).val) : x = y := by
  rw [Valid_def] at hx hy
  have hsum : TargetSum.sum x = TargetSum.sum y := hx.trans hy.symm
  funext i
  refine Fin.ext (le_antisymm (hle i) ?_)
  by_contra hlt
  have hstrict : (x i).val < (y i).val := by omega
  have : TargetSum.sum x < TargetSum.sum y :=
    Finset.sum_lt_sum (fun j _ => hle j) ⟨i, Finset.mem_univ i, hstrict⟩
  omega

/-- A valid word, used where the proof needs a word before the reference encoding is known. -/
irreducible_def defaultWord : Encoding :=
  fun index => if index.val < 41 then ⟨3, by decide⟩ else ⟨0, by decide⟩

theorem defaultWord_valid : Valid defaultWord := by
  rw [Valid_def]
  change (∑ index : ChainIndex, (defaultWord index).val) = 123
  simp only [defaultWord_def]
  decide

/-- The chain steps a signer walks to reveal a word. -/
def signingSteps (word : Encoding) : Nat := ∑ index, (word index).val

/-! ### Unit neighbors

A valid word one backward step below the reference at one chain and nowhere else below it. This is the only way a forgery can reuse a one-time key with a single inverted chain step. -/

def UnitNeighborAt (reference candidate : Encoding) (lowered : ChainIndex) : Prop :=
  Valid reference ∧ Valid candidate ∧ (candidate lowered).val + 1 = (reference lowered).val ∧
    ∀ index, index ≠ lowered → (reference index).val ≤ (candidate index).val

theorem UnitNeighborAt.ne {reference candidate : Encoding} {lowered : ChainIndex}
    (h : UnitNeighborAt reference candidate lowered) : candidate ≠ reference := by
  intro he
  have hd := h.2.2.1
  rw [he] at hd
  omega

theorem UnitNeighborAt.lowered_unique {reference candidate : Encoding} {left right : ChainIndex}
    (hleft : UnitNeighborAt reference candidate left) (hright : UnitNeighborAt reference candidate right) : left = right := by
  by_contra hne
  have hle := hleft.2.2.2 right (Ne.symm hne)
  have hd := hright.2.2.1
  omega

noncomputable def unitNeighbors (reference : Encoding) (lowered : ChainIndex) : Finset Encoding :=
  Finset.univ.filter (fun candidate => UnitNeighborAt reference candidate lowered)

theorem mem_unitNeighbors {reference candidate : Encoding} {lowered : ChainIndex} :
    candidate ∈ unitNeighbors reference lowered ↔ UnitNeighborAt reference candidate lowered := by
  simp only [unitNeighbors, Finset.mem_filter, Finset.mem_univ, true_and]

noncomputable def allUnitNeighbors (reference : Encoding) : Finset Encoding :=
  Finset.univ.biUnion (unitNeighbors reference)

theorem mem_allUnitNeighbors {reference candidate : Encoding} :
    candidate ∈ allUnitNeighbors reference ↔ ∃ lowered, UnitNeighborAt reference candidate lowered := by
  simp only [allUnitNeighbors, Finset.mem_biUnion, Finset.mem_univ, true_and, mem_unitNeighbors]

/-- The unit neighbors of a word at one lowered chain. -/
irreducible_def unitNeighborBound : Nat := numChains - 1

/-- The unit neighbors of a word at any chain. -/
irreducible_def neighborBound : Nat := numChains * (numChains - 1)

private theorem two_terms_le_sum (f : ChainIndex → Nat) {left right : ChainIndex} (hne : left ≠ right) :
    f left + f right ≤ ∑ index, f index := by
  have h := Finset.sum_le_sum_of_subset_of_nonneg (f := f) (Finset.subset_univ ({left, right} : Finset ChainIndex))
    (fun _ _ _ => Nat.zero_le _)
  simpa only [Finset.sum_pair hne] using h

private theorem single_of_sum_one (f : ChainIndex → Nat) (hsum : (∑ index, f index) = 1) :
    ∃ index, f index = 1 ∧ ∀ other, other ≠ index → f other = 0 := by
  have hnonzero : ∃ index, f index ≠ 0 := by
    by_contra hnone
    push Not at hnone
    have hz : (∑ index, f index) = 0 := Finset.sum_eq_zero fun index _ => hnone index
    omega
  obtain ⟨index, hi⟩ := hnonzero
  have hle : f index ≤ ∑ other, f other := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ index)
  have hone : f index = 1 := by omega
  refine ⟨index, hone, fun other hne => ?_⟩
  have hpair := two_terms_le_sum f hne
  omega

/-- For the target-sum code a unit neighbor moves exactly one step from the lowered chain to one other chain. -/
private theorem UnitNeighborAt.raised {reference candidate : Encoding} {lowered : ChainIndex}
    (h : UnitNeighborAt reference candidate lowered) :
    ∃ raised, raised ≠ lowered ∧ (reference raised).val + 1 = (candidate raised).val ∧
      ∀ index, index ≠ lowered → index ≠ raised → candidate index = reference index := by
  obtain ⟨hreference, hcandidate, hlow, hup⟩ := h
  rw [Valid_def] at hreference hcandidate
  have hpoint : ∀ index : ChainIndex,
      ((reference index).val - (candidate index).val) + (candidate index).val =
        ((candidate index).val - (reference index).val) + (reference index).val := fun index => by omega
  have hsum := congrArg (fun f : ChainIndex → Nat => ∑ index, f index) (funext hpoint)
  simp only [Finset.sum_add_distrib] at hsum
  have hback : ∑ index, ((reference index).val - (candidate index).val) = 1 := by
    rw [Finset.sum_eq_single lowered]
    · omega
    · intro index _ hne
      have := hup index hne
      omega
    · simp only [Finset.mem_univ, not_true_eq_false, false_implies]
  change _ + TargetSum.sum candidate = _ + TargetSum.sum reference at hsum
  have hsums : TargetSum.sum candidate = TargetSum.sum reference := hcandidate.trans hreference.symm
  have hforward : ∑ index, ((candidate index).val - (reference index).val) = 1 := by omega
  obtain ⟨raised, hraise, hothers⟩ := single_of_sum_one _ hforward
  refine ⟨raised, fun he => ?_, by omega, fun index hl hr => ?_⟩
  · subst raised
    omega
  · have hdown := hothers index hr
    have hle := hup index hl
    apply Fin.ext
    omega

theorem unitNeighbors_card_le (reference : Encoding) (lowered : ChainIndex) :
    (unitNeighbors reference lowered).card ≤ unitNeighborBound := by
  let chooseRaised : {candidate // UnitNeighborAt reference candidate lowered} → {raised : ChainIndex // raised ≠ lowered} :=
    fun candidate => ⟨candidate.property.raised.choose, candidate.property.raised.choose_spec.1⟩
  have hinj : Function.Injective chooseRaised := by
    intro left right he
    apply Subtype.ext
    have he' : left.property.raised.choose = right.property.raised.choose := congrArg Subtype.val he
    obtain ⟨_, hup, hrest⟩ := left.property.raised.choose_spec
    obtain ⟨_, hup', hrest'⟩ := right.property.raised.choose_spec
    rw [he'] at hup hrest
    funext index
    by_cases hl : index = lowered
    · subst index
      apply Fin.ext
      have := left.property.2.2.1
      have := right.property.2.2.1
      omega
    · by_cases hr : index = right.property.raised.choose
      · subst index
        apply Fin.ext
        omega
      · exact (hrest index hl hr).trans (hrest' index hl hr).symm
  have hcard := Fintype.card_le_of_injective chooseRaised hinj
  rw [Fintype.card_subtype, Fintype.card_subtype] at hcard
  have hr : (Finset.univ.filter fun raised : ChainIndex => raised ≠ lowered) = Finset.univ.erase lowered := by
    ext raised
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
  rw [hr, Finset.card_erase_of_mem (Finset.mem_univ lowered), Finset.card_univ, Fintype.card_fin] at hcard
  rw [unitNeighborBound_def]
  simpa only [unitNeighbors] using hcard

theorem allUnitNeighbors_card_le (reference : Encoding) : (allUnitNeighbors reference).card ≤ neighborBound := by
  calc
    _ ≤ ∑ lowered : ChainIndex, (unitNeighbors reference lowered).card := Finset.card_biUnion_le
    _ ≤ ∑ _lowered : ChainIndex, unitNeighborBound :=
      Finset.sum_le_sum fun lowered _ => unitNeighbors_card_le reference lowered
    _ = neighborBound := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, neighborBound_def,
        unitNeighborBound_def]

/-! ### Values, for the closing arithmetic only -/

theorem unitNeighborBound_eq : unitNeighborBound = 63 := by
  rw [unitNeighborBound_def]
  rfl

theorem neighborBound_eq : neighborBound = 4032 := by
  rw [neighborBound_def]
  rfl

/-! ### Parameter facts the rest of the proof needs -/

theorem two_le_chainLength : 2 ≤ chainLength := by decide

theorem two_le_numChains : 2 ≤ numChains := by decide

theorem chainTweakPosition_lt (chainIdx : ChainIndex) (step : ChainStep) :
    chainLength * chainIdx.val + step.val < 2 ^ 32 := by
  have := chainIdx.isLt
  have := step.isLt
  simp only [numChains, chainLength, winternitzBits] at *
  omega

theorem chainTweakPosition_injective {left right : ChainIndex} {leftStep rightStep : ChainStep}
    (h : chainLength * left.val + leftStep.val = chainLength * right.val + rightStep.val) :
    left = right ∧ leftStep = rightStep := by
  have := leftStep.isLt
  have := rightStep.isLt
  simp only [chainLength, winternitzBits] at *
  exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩

/-- A one-time leaf, with one digest per chain, is the widest payload: the few-time roots fit too. -/
theorem ftsRoots_le_numChains : ftsTrees - 1 ≤ numChains := by decide

end OtsCode

/-! ### The encoding and leaf computations over the sealed code -/

namespace Concrete

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

abbrev counterBytes (counter : Counter) : HashInput := bytesLE 4 counter

/-- Hash the message with the counter under the leaf's encoding tweak, and decode. -/
def encodeAttempt (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : Digest) (counter : Counter) : m (Option Encoding) := do
  let digest ← tweakableHash parameter (.encoding lay tree leaf) (bytesLE 16 message ++ counterBytes counter)
  return OtsCode.decode digest

/-- The verifier's one-time leaf, or nothing if the counter does not encode the message. -/
def otsLeafAttempt (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : Digest) (counter : Counter) (values : ChainIndex → Digest) : m (Option Digest) := do
  let some encoding ← encodeAttempt parameter lay tree leaf message counter | return none
  let endpoints ← sequenceFin fun chainIdx =>
    recoverChain parameter lay tree leaf chainIdx (encoding chainIdx) (values chainIdx)
  let value ← leafHash parameter lay tree leaf endpoints
  return some value

theorem encode_eq (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : Digest) (counter : Counter) :
    encode (m := m) parameter lay tree leaf message counter = encodeAttempt parameter lay tree leaf message counter := by
  simp only [encode, encodeAttempt, OtsCode.decode_def]

theorem otsLeaf_eq (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : Digest) (counter : Counter) (values : ChainIndex → Digest) :
    otsLeaf (m := m) parameter lay tree leaf message counter values =
      otsLeafAttempt parameter lay tree leaf message counter values := by
  simp only [otsLeaf, otsLeafAttempt, encode_eq]
  apply bind_congr
  intro result
  cases result <;> rfl

end Concrete

end SphincsSecurity
