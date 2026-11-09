/-
  LeanVM.Guest.B1.Main.AggCMath

  The honest rows, claims and weights of `aggregate_claims`, step by step.
-/

module

public import LeanVM.Guest.B1.Main.AggCLib
public import LeanVM.Guest.Batch.Def

/-!
# Honest values, step by step

`absSt_succ`: the next absorbing row's sponge absorbs the child's words as `__loop33` reads
them; `absSt_pend`: four scalars wait on every row; `absSt_last`: the last row's sponge is the
batching's. `claimAt_succ`, `weightAt_succ`: the running claim and weight on one child.
`kid_reads`: a child's words in memory, as the loops read them. `bsRun_cap`: the sumcheck leaves a
state's capacity and nothing waiting.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Node

@[expose] public section

variable {rd : Reader}

theorem absSt_zero (m : ℕ) (cs : List ChildClaims) :
    absSt m cs 0 = ⟨capOf batchSeed, [gen ^ m, 0, 0, 0].map (·, dsObserve)⟩ := by
  rw [absSt, List.take_zero, List.flatMap_nil, List.append_nil, absorb_head]

theorem absSt_succ {cpi cfresh ccarried : E} {m c : ℕ} {cs : List ChildClaims}
    (hc : c < cs.length) (hcw : ChildWordsAt rd cpi cfresh ccarried c cs[c]) :
    absSt m cs (c + 1) =
      (absSt m cs c).absorbAll (l25Words rd cpi cfresh ccarried (gen ^ c)) dsObserve := by
  obtain ⟨-, -, -, -, hw⟩ := kid_words hcw
  rw [absSt, absSt, List.take_succ_eq_append_getElem hc, List.flatMap_append,
    List.flatMap_singleton, ← List.append_assoc, absorbAll_append, ← hw]

theorem absSt_pend {cpi cfresh ccarried : E} {m : ℕ} {cs : List ChildClaims}
    (hcw : ∀ c (hc : c < cs.length), ChildWordsAt rd cpi cfresh ccarried c cs[c]) :
    ∀ c ≤ cs.length, (absSt m cs c).pend.length = 4
  | 0, _ => by rw [absSt_zero]; rfl
  | c + 1, hc => by
    have ih := absSt_pend (m := m) hcw c (by omega)
    rw [absSt_succ (by omega) (hcw c (by omega)), pend_absorbAll _ _ _ (by omega) (by omega), ih]
    simp [l25Words]

theorem absSt_last {m : ℕ} {cs : List ChildClaims} (hcl : cs.length = m) :
    absSt m cs m = aggAbs cs := by
  rw [absSt, List.take_of_length_le (by omega), aggAbs, Batch.cellsBeforeChallenge, hcl]

theorem claimAt_zero (cs : List ChildClaims) : claimAt cs 0 = 0 := by
  simp [claimAt, sumE, Batch.lambdaPowers]

theorem claimAt_succ {cs : List ChildClaims} {c : ℕ} (hc : c < cs.length) :
    claimAt cs (c + 1) = claimAt cs c + lamA cs ^ (2 * c) *
      (cs[c].freshClaim.bytecodeValue + lamA cs * cs[c].carriedClaim.bytecodeValue) := by
  simp only [claimAt, lambdaPowers_eq]
  rw [zip_prefix _ _ _ hc]
  ring

theorem weightAt_zero (cs : List ChildClaims) (h : BatchingHints) : weightAt cs h 0 = 0 := by
  simp [weightAt, sumE, Batch.lambdaPowers]

theorem weightAt_succ {cs : List ChildClaims} {h : BatchingHints} {c : ℕ} (hc : c < cs.length) :
    weightAt cs h (c + 1) = weightAt cs h c + lamA cs ^ (2 * c) *
      (eqEval cs[c].freshClaim.bytecodePoint (aggRun cs h).1.1 +
        lamA cs * eqEval cs[c].carriedClaim.bytecodePoint (aggRun cs h).1.1) := by
  simp only [weightAt, lambdaPowers_eq]
  rw [zip_prefix _ _ _ hc]
  ring

theorem aggLam_fst {m : ℕ} {cs : List ChildClaims} (hcl : cs.length = m) :
    (aggLam cs).1 = Batch.lambdaPowers (lamA cs) m := by
  rw [aggLam, sqLF, hcl]
  rfl

theorem claimAt_last {m : ℕ} {cs : List ChildClaims} (hcl : cs.length = m) :
    claimAt cs m = Batch.batchedClaim cs (aggLam cs).1 := by
  rw [claimAt, aggLam_fst hcl, List.take_of_length_le (by omega)]
  rfl

theorem weightAt_last {m : ℕ} {cs : List ChildClaims} (hcl : cs.length = m) (h : BatchingHints) :
    weightAt cs h m = Batch.batchedBytecodeWeight cs (aggLam cs).1 (aggRun cs h).1.1 := by
  rw [weightAt, aggLam_fst hcl, List.take_of_length_le (by omega)]
  rfl

/-- The sumcheck leaves a state's capacity and nothing waiting. -/
theorem bsRun_cap : ∀ (rounds : List (E × E)) (claim : E) (s : Fs), rounds ≠ [] →
    ∃ S, (bsRun rounds claim s).2 = ⟨capOf S, []⟩
  | [], _, _, h => absurd rfl h
  | (g1, gInf) :: rest, claim, s, _ => by
    cases rest with
    | nil => exact ⟨((s.absorb g1 dsObserve).absorb gInf dsObserve).perm, rfl⟩
    | cons r rest' =>
      rw [bsRun]
      exact bsRun_cap _ _ _ (by simp)

/-- The sponge after `λ`: the permutation's capacity, nothing waiting. -/
theorem aggLam_snd (cs : List ChildClaims) :
    (aggLam cs).2 = ⟨capOf (aggAbs cs).perm, []⟩ := rfl

/-- **A child's words in memory**, as the loops read them. -/
theorem kid_reads {cpi cfresh ccarried : E} {c : ℕ} {cc : ChildClaims}
    (h : ChildWordsAt rd cpi cfresh ccarried c cc) :
    cc.freshClaim.bytecodePoint.length = 23 ∧ cc.carriedClaim.bytecodePoint.length = 23 ∧
    ReadsAt rd (cfresh * (gen ^ c) ^ 24) cc.freshClaim.bytecodePoint ∧
    ReadsAt rd (ccarried * (gen ^ c) ^ 24) cc.carriedClaim.bytecodePoint ∧
    LoadHolds rd (cfresh * (gen ^ c) ^ 24) 23 cc.freshClaim.bytecodeValue ∧
    LoadHolds rd (ccarried * (gen ^ c) ^ 24) 23 cc.carriedClaim.bytecodeValue ∧
    (∀ o < 2, ∃ v, LoadHolds rd (cpi * (gen ^ c) ^ 2) o v) ∧
    (∀ o < 24, ∃ v, LoadHolds rd (cfresh * (gen ^ c) ^ 24) o v) ∧
    (∀ o < 24, ∃ v, LoadHolds rd (ccarried * (gen ^ c) ^ 24) o v) := by
  obtain ⟨h1, h2, hp0, hp1, hf, hc⟩ := h
  have b23 : bytecodeVars = 23 := rfl
  rw [b23] at h1 h2
  have e24 : (gen ^ c) ^ 24 = gen ^ (24 * c) := by rw [← pow_mul, mul_comm]
  have e2 : (gen ^ c) ^ 2 = gen ^ (2 * c) := by rw [← pow_mul, mul_comm]
  rw [e24, e2]
  have hf' : ReadsAt rd (cfresh * gen ^ (24 * c)) (cc.freshClaim.bytecodePoint ++ [cc.freshClaim.bytecodeValue]) := hf
  have hc' : ReadsAt rd (ccarried * gen ^ (24 * c))
      (cc.carriedClaim.bytecodePoint ++ [cc.carriedClaim.bytecodeValue]) := hc
  have hfl : (cc.freshClaim.bytecodePoint ++ [cc.freshClaim.bytecodeValue]).length = 24 := by simp [h1]
  have hcl : (cc.carriedClaim.bytecodePoint ++ [cc.carriedClaim.bytecodeValue]).length = 24 := by simp [h2]
  refine ⟨h1, h2, (readsAt_append.mp hf').1, (readsAt_append.mp hc').1, ?_, ?_, ?_,
    fun o ho => ⟨_, hf' o (by rw [hfl]; exact ho)⟩, fun o ho => ⟨_, hc' o (by rw [hcl]; exact ho)⟩⟩
  · have := hf' 23 (by rw [hfl]; omega)
    rwa [List.getElem_append_right (by rw [h1]), List.getElem_singleton] at this
  · have := hc' 23 (by rw [hcl]; omega)
    rwa [List.getElem_append_right (by rw [h2]), List.getElem_singleton] at this
  · intro o ho
    rcases (show o = 0 ∨ o = 1 by omega) with rfl | rfl
    · exact ⟨_, (loadHolds_mul_gen_pow rd _ _ _ _).mpr (by rw [add_zero]; exact hp0)⟩
    · exact ⟨_, (loadHolds_mul_gen_pow rd _ _ _ _).mpr hp1⟩

end
end LeanVM.Guest.B1.Main
