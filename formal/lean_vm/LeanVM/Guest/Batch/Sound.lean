/-
  LeanVM.Guest.Batch.Sound

  The batching's soundness: an accepted batching whose deferred claim holds makes every child's
  claims true, unless one of its challenges is bad.
-/

module

public import LeanVM.Guest.Batch.Rounds
public import LeanVM.Guest.AcceptableChild

/-!
# The batching is sound, challenge by challenge

`Node.batch` absorbs the children's claims, checks a proof of work, squeezes one challenge `λ`, whose powers are the
lambdas (`λ^(2i)`, `λ^(2i+1)` for child `i`), and runs one sumcheck on the bytecode, deferring one
claim. `batch_sound`: if the batching accepts and its deferred claim holds, then every child's
claims hold (its proof's, `BytecodeClaim.Holds`, and its
statement's, `DeferredBytecodeClaim.HoldsShaped`), or a challenge is bad (`BatchBad`):

* **the challenge `λ`**: the children's claims leave nonzero gaps (claimed less true values), and
  the lambdas' combination of them vanishes: `λ` is a root of the nonzero polynomial whose
  coefficients are the gaps, of degree below `2n` (`LeanVM.Guest.Batch.RomSpec` counts them);
* **a sumcheck round**: a round's challenge is a root of its gap, a nonzero polynomial of degree
  at most two that the round's claim, message and earlier challenges fix (`BadRound`,
  `badRound_roots`).

Every bad value is fixed before the challenge is squeezed from the sponge, which absorbed what
fixes it. `λ` and the rounds' challenges are Keccak-f[1600] outputs computed by the guest: that a
bad one is improbable is the in-guest hash heuristic, not a theorem here; `LeanVM.Guest.Batch.Rom`
bounds it with Keccak-256 and Keccak-f[1600] random oracles.
-/

namespace LeanVM.Guest.Batch

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

/-! ## The transcript -/

/-- The lambdas, a pair per child: the powers of the one challenge. -/
def lambdasB (cs : List ChildClaims) (h : BatchingHints) : List (E × E) := (sqL cs.length (powB cs h).2).1

/-- The batched claim. -/
def claimB (cs : List ChildClaims) (h : BatchingHints) : E := batchedClaim cs (lambdasB cs h)

/-- The sponge at the sumcheck. -/
def spB (cs : List ChildClaims) (h : BatchingHints) : Sponge := (sqL cs.length (powB cs h).2).2

/-- **`Node.batch` in the transcript's names**: the deferred claim at the sumcheck's
challenges, if the proof of work and the final check pass. -/
theorem batch_eq' (cs : List ChildClaims) (h : BatchingHints) :
    batch cs h =
      if powOk batchLambdaGrindBits (powB cs h).1 then
        if (rsRun h.sumcheckMessages (claimB cs h) (spB cs h)).1.2 = h.finalBytecodeValue *
              batchedBytecodeWeight cs (lambdasB cs h)
                (rsRun h.sumcheckMessages (claimB cs h) (spB cs h)).1.1 then
          some ⟨(rsRun h.sumcheckMessages (claimB cs h) (spB cs h)).1.1, h.finalBytecodeValue⟩
        else none
      else none :=
  batch_eq cs h

/-! ## The bad challenges -/

/-- The gaps the children's claims on the bytecode leave, claimed less true, in the order of
their lambdas. -/
def gapsB (bytecode : List K) (cs : List ChildClaims) : List E :=
  cs.flatMap fun c ↦
    [c.freshClaim.bytecodeValue - multilinearEval (bytecode.map ofK) c.freshClaim.bytecodePoint,
      c.carriedClaim.bytecodeValue - multilinearEval (bytecode.map ofK) c.carriedClaim.bytecodePoint]

/-- **The lambdas are bad** for the gaps: some gap is nonzero, and the lambdas' combination of
the gaps vanishes. -/
def LambdaBad (gaps lambdas : List E) : Prop :=
  (∃ g ∈ gaps, g ≠ 0) ∧ dot lambdas gaps = 0

/-- The flattened pairs of lambdas. -/
abbrev flat2 (l : List (E × E)) : List E := l.flatMap fun p ↦ [p.1, p.2]

/-- **A challenge of the batching is bad**: its lambdas, or a round of its sumcheck. -/
def BatchBad (bytecode : List K) (cs : List ChildClaims) (h : BatchingHints) : Prop :=
  LambdaBad (gapsB bytecode cs) (flat2 (lambdasB cs h)) ∨
    ∃ j < h.sumcheckMessages.length, BadRound h.sumcheckMessages.length
      (bytecodePoly bytecode cs (lambdasB cs h)) h.sumcheckMessages (claimB cs h) (spB cs h) j

/-! ## Soundness -/

/-- Claimed less true values, combined by pairs of lambdas, is the lambdas' combination of the
gaps. -/
theorem sub_pairs {α : Type} (cs : List α) (l : List (E × E)) (hl : l.length = cs.length)
    (a b a' b' : α → E) :
    sumE (List.zipWith (fun c l ↦ l.1 * a c + l.2 * b c) cs l) -
        sumE (List.zipWith (fun c l ↦ l.1 * a' c + l.2 * b' c) cs l) =
      dot (flat2 l) (cs.flatMap fun c ↦ [a c - a' c, b c - b' c]) := by
  induction cs generalizing l with
  | nil => simp
  | cons c cs ih =>
    obtain _ | ⟨x, l⟩ := l
    · simp at hl
    · simp only [List.zipWith_cons_cons, Whir.Complete.sumE_eq, List.sum_cons,
        List.flatMap_cons, List.cons_append, List.nil_append, Whir.Complete.dot_cons] at ih ⊢
      rw [← ih l (by simpa using hl)]
      ring

/-- Either every gap is zero, or the lambdas are bad, or the claimed combination is not the true
one. -/
theorem gaps_cases {gaps lambdas : List E} {claimed true_ : E}
    (h : claimed - true_ = dot lambdas gaps) :
    (∀ g ∈ gaps, g = 0) ∨ LambdaBad gaps lambdas ∨ claimed ≠ true_ := by
  by_cases hz : ∀ g ∈ gaps, g = 0
  · exact Or.inl hz
  · by_cases hd : dot lambdas gaps = 0
    · push Not at hz
      exact Or.inr (Or.inl ⟨hz, hd⟩)
    · exact Or.inr (Or.inr fun he ↦ hd (by rw [← h, he, sub_self]))

/-- The lambdas' combination of the claimed values, less that of the true ones, is their
combination of the gaps. -/
theorem claimB_sub (bytecode : List K) (cs : List ChildClaims) (l : List (E × E))
    (hl : l.length = cs.length) :
    batchedClaim cs l - bytecodeTrue bytecode cs l = dot (flat2 l) (gapsB bytecode cs) :=
  sub_pairs cs l hl (fun c ↦ c.freshClaim.bytecodeValue) (fun c ↦ c.carriedClaim.bytecodeValue)
    (fun c ↦ multilinearEval (bytecode.map ofK) c.freshClaim.bytecodePoint)
    (fun c ↦ multilinearEval (bytecode.map ofK) c.carriedClaim.bytecodePoint)

/-- Zero gaps are true claims, for points of the bytecode's shape. -/
theorem holds_of_gaps {bytecode : List K} {cs : List ChildClaims}
    (hz : ∀ g ∈ gapsB bytecode cs, g = 0) (hpow : 2 ^ Nat.log2 bytecode.length = bytecode.length)
    (hc : ∀ c ∈ cs, c.carriedClaim.HasBytecodeShape bytecode) :
    ∀ c ∈ cs, c.freshClaim.Holds bytecode ∧ c.carriedClaim.HoldsWithShape bytecode := by
  intro c hc'
  have g := fun g hg ↦ hz g (List.mem_flatMap.mpr ⟨c, hc', hg⟩)
  have e1 := sub_eq_zero.mp (g _ (List.mem_cons_self ..))
  have e2 := sub_eq_zero.mp (g _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  refine ⟨e1.symm, hc c hc', ?_, e2.symm⟩
  rw [hc c hc', hpow]

/-- **The batching is sound, challenge by challenge**: an accepted batching whose deferred claim
holds, of children whose claims have the bytecode's shape, makes every child's claims true, or
one of its challenges is bad. -/
theorem batch_sound {bytecode : List K} {cs : List ChildClaims} {h : BatchingHints}
    {d : DeferredBytecodeClaim} (hb : batch cs h = some d) (hd : d.HoldsWithShape bytecode)
    (hf : ∀ c ∈ cs, c.freshClaim.bytecodePoint.length = Nat.log2 bytecode.length)
    (hc : ∀ c ∈ cs, c.carriedClaim.HasBytecodeShape bytecode) :
    (∀ c ∈ cs, c.freshClaim.Holds bytecode ∧ c.carriedClaim.HoldsWithShape bytecode) ∨ BatchBad bytecode cs h := by
  rw [batch_eq'] at hb
  split_ifs at hb with hpow hfin
  injection hb with hd'
  subst hd'
  obtain ⟨hlog, hpow, hval⟩ := hd
  simp only [DeferredBytecodeClaim.HasBytecodeShape] at hlog hpow hval
  rw [length_rsRun] at hlog hpow
  set n := h.sumcheckMessages.length
  have hlog' : Nat.log2 bytecode.length = n := by rw [← hpow, Nat.log2_two_pow]
  have hpB : ∀ c ∈ cs, c.freshClaim.bytecodePoint.length = n ∧ c.carriedClaim.bytecodePoint.length = n :=
    fun c hc' ↦ ⟨(hf c hc').trans hlog', (hc c hc').trans hlog'⟩
  rcases gaps_cases (claimB_sub bytecode cs (lambdasB cs h) (length_sqL _ _)) with hz | hbad | hne
  · exact Or.inl (holds_of_gaps hz (by rw [hlog', hpow]) hc)
  · exact Or.inr (Or.inl hbad)
  · refine Or.inr (Or.inr (rounds_sound rfl ?_ ?_))
    · rw [roundChallenges, hfin, bytecodePoly, hval]
    · rw [bytecode_cubeSum hpow.symm hpB]; exact hne

end
end LeanVM.Guest.Batch
