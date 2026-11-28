/-
  LeanVM.Protocol.Relation.Link.Rounds

  The statement's plain sum-check round by round: a false claim, or a carried fact a challenge
  breaks rarely, survives each round's challenge but for `count − 1` values, after the round's
  grind.
-/

module

public import LeanVM.Protocol.Compile.SpecRules.Leaves
public import LeanVM.Protocol.Compile.SpecRules.Bind
public import LeanVM.Protocol.Compile.SpecRules.Grind
public import LeanVM.Protocol.Link.Sumcheck
import LeanVM.Protocol.Field

/-!
# The sum-check, round by round

`sumcheck claim count (List.replicate k none)` (`Statement/Verifier/Sumcheck.lean`,
`transcript.rs`): each round reads `count − 1` coefficients (the one the claim fixes left out),
grinds `grindingBits (count − 1)` bits, and draws its challenge.

`roundsSpec`: for a table of partial sums `g` of round degrees at most `count − 1`
(`RoundPolys`, `Link/Sumcheck.lean`), meaningful when `Good` holds, and a carried predicate `Carry`
on the challenges drawn so far that each challenge breaks for at most `count − 1` values, doom is
"`Good` and the claim is not `g` at the challenges so far, or `Carry` holds of them". A round's
message sums to the claim at `0` and `1` (`roundMessage_sum`), so with a false claim it is not the
round's polynomial and agrees with it at no more than `count − 1` points (`card_agree_le`); with
`Carry`, its challenge breaks it at no more than `count − 1`. Either way the challenge escapes doom
with probability at most `(count − 1)/|E|`, which the round's grind brings to `εmsg`
(`grindingBits_discount`). The link carries, through its index rounds, the mirror certificate's
polynomial in the challenges not yet drawn, and through its row rounds the Keccak defect's
multilinear extension, both of degree at most a round's (`Link/Spec.lean`).
-/

namespace LeanVM.Protocol.Relation

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Protocol.Link
open Finset
open scoped ENNReal

@[expose] public section

open Classical

/-! ## Reading scalars -/

/-- **Reading `n` scalars** keeps a doom that ignores the history and records their count; its
lead is the follower's. -/
noncomputable def readNSpec (φ : Prop) {T : ℝ≥0∞} (hT : T ≤ εmsg) : (n : ℕ) →
    Spec (VerifierProgram.readScalars n) (fun _ ↦ φ) (fun xs _ ↦ xs.length = n ∧ φ) εmsg T T
  | 0 => (Spec.ret (Post := fun xs _ ↦ xs.length = 0 ∧ φ) []).mono
      (fun _ h ↦ ⟨rfl, h⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  | n + 1 =>
    ((Spec.readE (Pre := fun _ ↦ φ) (Post := fun _ _ ↦ φ) (fun _ _ hp ↦ hp) hT).bind' fun x ↦
      (readNSpec φ hT n).bind' fun xs ↦
        (Spec.ret (Post := fun xs _ ↦ xs.length = n + 1 ∧ φ) (x :: xs)).mono
          (fun _ h ↦ ⟨by simp [h.1], h.2⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).mono
        (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl zero_le le_rfl

/-! ## Tables of partial sums on a range of rounds -/

/-- `g` is a table of partial sums on the rounds `n0 ≤ i < n`, of degrees at most `d`: for each
prefix `p` of that many challenges, `c ↦ g (p ++ [c])` is a polynomial `q` of degree at most `d`
whose values at `0` and `1` sum to `g p`. -/
def RoundsBetween (g : List E → E) (n0 n d : ℕ) : Prop :=
  ∀ p : List E, n0 ≤ p.length → p.length < n → ∃ q : Polynomial E, q.natDegree ≤ d ∧
    q.eval 0 + q.eval 1 = g p ∧ ∀ c, q.eval c = g (p ++ [c])

/-- A table of partial sums is one on any range of its rounds of bounded degree. -/
theorem RoundPolys.between {g : List E → E} {N : ℕ} {deg : ℕ → ℕ} (h : RoundPolys g N deg)
    {n0 n d : ℕ} (hn : n ≤ N) (hd : ∀ i, n0 ≤ i → i < n → deg i ≤ d) : RoundsBetween g n0 n d := by
  intro p hp0 hp
  obtain ⟨q, hq, hsum, hval⟩ := h p (by omega)
  exact ⟨q, hq.trans (hd _ hp0 hp), hsum, hval⟩

/-! ## A round's challenge -/

/-- The error a round's challenge may leave, `(count − 1)/|E|`. -/
noncomputable def roundError (count : ℕ) : ℝ≥0∞ := ((count - 1 : ℕ) : ℝ≥0∞) / cardE

/-- A round's error, through its grind, is within `εmsg`. -/
theorem roundError_grind (count : ℕ) :
    (2 : ℝ≥0∞)⁻¹ ^ grindingBits (count - 1) * roundError count ≤ εmsg :=
  grindingBits_discount (count - 1)

/-- A grind of no bits leaves a round's error within `εmsg`: its numerator is at most `8`. -/
theorem roundError_le_of_grind_zero {count : ℕ} (h : grindingBits (count - 1) = 0) :
    roundError count ≤ εmsg := by
  simpa [h] using roundError_grind count

/-- The message a plain round reads, `[c_0, claim + Σ tail, tail…]`. -/
def roundMessage (claim c0 : E) (tail : List E) : List E := c0 :: (claim + sumE tail) :: tail

/-- The doom of the rounds: `Good` and a claim that is not the table's at the challenges, or
`Carry` of them. -/
def RoundDoom (Good : Prop) (g : List E → E) (Carry : List E → Prop) (claim : E) (pre : List E) :
    Prop :=
  (Good ∧ claim ≠ g pre) ∨ Carry pre

/-- **A round's challenge escapes doom rarely**: if the claim is not the table's or `Carry` holds,
the challenges after which neither holds are at most `count − 1`. -/
theorem card_round_escape {count : ℕ} {n : ℕ} {g : List E → E} {Good : Prop}
    {n0 : ℕ} (hg : Good → RoundsBetween g n0 n (count - 1)) {Carry : List E → Prop}
    (hcarry : ∀ pre : List E, n0 ≤ pre.length → pre.length < n → Carry pre →
      (univ.filter fun c ↦ ¬ Carry (pre ++ [c])).card ≤ count - 1)
    {claim c0 : E} {tail : List E} (htail : tail.length = count - 2) (hc : 2 ≤ count)
    {pre : List E} (hpre0 : n0 ≤ pre.length) (hpre : pre.length < n)
    (hD : RoundDoom Good g Carry claim pre) :
    (univ.filter fun c ↦ ¬ RoundDoom Good g Carry (polyEval (roundMessage claim c0 tail) c)
      (pre ++ [c])).card ≤ count - 1 := by
  classical
  unfold RoundDoom
  rcases hD with ⟨hG, hne⟩ | hC
  · obtain ⟨q, hq, hsum, hval⟩ := hg hG pre hpre0 hpre
    have hmsg : toPoly (roundMessage claim c0 tail) ≠ q := by
      intro h
      apply hne
      rw [← hsum, ← h]
      exact (roundMessage_sum claim c0 tail).symm
    refine le_trans (card_le_card fun c hc' ↦ ?_)
      (card_agree_le _ q hmsg (D := count - 1) ?_ hq)
    · simp only [mem_filter, mem_univ, true_and, not_or, not_and, not_not] at hc' ⊢
      rw [eval_toPoly, hval]
      exact hc'.1 hG
    · refine (natDegree_toPoly _).trans ?_
      simp only [roundMessage, List.length_cons, htail]
      omega
  · exact le_trans (card_le_card fun c hc' ↦ by
      simp only [mem_filter, mem_univ, true_and, not_or] at hc' ⊢
      exact hc'.2) (hcarry pre hpre0 hpre hC)

/-! ## The rounds -/

/-- The program of one plain round's message: `sumcheckRoundPoly count claim none`. -/
theorem sumcheckRoundPoly_none (count : ℕ) (claim : E) :
    sumcheckRoundPoly count claim none = (do
      let c0 ← VerifierProgram.readScalar
      let tail ← VerifierProgram.readScalars (count - 2)
      VerifierProgram.grindProofOfWork (grindingBits (count - 1))
      return roundMessage claim c0 tail) := rfl

/-- One round's message, read and ground: doom kept, the message's form recorded. Its lead is `0`
(it starts with a read), the follower's the round's error. -/
noncomputable def roundMessageSpec (count : ℕ) (φ : Prop) (claim : E) :
    Spec (sumcheckRoundPoly count claim none) (fun _ ↦ φ)
      (fun msg _ ↦ φ ∧ ∃ c0 tail, tail.length = count - 2 ∧ msg = roundMessage claim c0 tail)
      εmsg 0 (roundError count) := by
  rw [sumcheckRoundPoly_none]
  have hG : (2 : ℝ≥0∞)⁻¹ ^ grindingBits (count - 1) * roundError count ≤ εmsg :=
    roundError_grind count
  have hlead : (if grindingBits (count - 1) = 0 then roundError count else 0) ≤ εmsg := by
    split_ifs with h
    · exact roundError_le_of_grind_zero h
    · exact zero_le
  exact (Spec.readE (Pre := fun _ ↦ φ) (Post := fun _ _ ↦ φ) (fun _ _ hp ↦ hp) hlead).bind'
    fun c0 ↦ (readNSpec φ hlead (count - 2)).bind' fun tail ↦
      (Spec.grindP (Pre := fun _ ↦ tail.length = count - 2 ∧ φ)
          (Post := fun _ _ ↦ tail.length = count - 2 ∧ φ) (grindingBits (count - 1))
          (fun _ hp ↦ hp) hG).bind' fun _ ↦
        (Spec.ret (Post := fun msg _ ↦ φ ∧ ∃ c0 tail, tail.length = count - 2 ∧
            msg = roundMessage claim c0 tail) (roundMessage claim c0 tail)).mono
          (fun _ h ↦ ⟨h.2, c0, tail, h.1, rfl⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

/-- The rounds after the first: `sumcheck` on `none :: rest` is a round's message, its challenge,
then the rest. -/
theorem sumcheck_cons_none (claim : E) (count : ℕ) (rest : List (Option E)) :
    sumcheck claim count (none :: rest) = (do
      let message ← sumcheckRoundPoly count claim none
      let challenge ← VerifierProgram.sampleChallenge
      let (point, final) ← sumcheck (polyEval message challenge) count rest
      return (challenge :: point, final)) := rfl

/-- **The plain sum-check, round by round.** From a claim that is not the table `g` at the
challenges `pre` drawn so far (when `Good`), or `Carry` of them, the `k` rounds left end with a
final claim that is not `g` at all the challenges, or with `Carry` of them; each challenge escapes
with probability at most `(count − 1)/|E|`, through its round's grind within `εmsg`. Lead and
follower's lead `0`: it starts and ends with a prover move or a return. -/
noncomputable def roundsSpec (count : ℕ) (hc : 2 ≤ count) {n : ℕ} {g : List E → E} {Good : Prop}
    {n0 : ℕ} (hg : Good → RoundsBetween g n0 n (count - 1)) {Carry : List E → Prop}
    (hcarry : ∀ pre : List E, n0 ≤ pre.length → pre.length < n → Carry pre →
      (univ.filter fun c ↦ ¬ Carry (pre ++ [c])).card ≤ count - 1) :
    (k : ℕ) → (claim : E) → (pre : List E) → n0 ≤ pre.length → pre.length + k = n →
    Spec (sumcheck claim count (List.replicate k none)) (fun _ ↦ RoundDoom Good g Carry claim pre)
      (fun r _ ↦ r.1.length = k ∧ RoundDoom Good g Carry r.2 (pre ++ r.1)) εmsg 0 0
  | 0, claim, pre, _, _ =>
    (Spec.ret (Post := fun r _ ↦ r.1.length = 0 ∧ RoundDoom Good g Carry r.2 (pre ++ r.1))
      ([], claim)).mono (fun _ h ↦ ⟨rfl, by simpa using h⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  | k + 1, claim, pre, hk0, hk => by
    classical
    rw [List.replicate_succ, sumcheck_cons_none]
    refine (roundMessageSpec count (RoundDoom Good g Carry claim pre) claim).bind' fun msg ↦ ?_
    have hS := Spec.sampleE (Pre := fun _ ↦ RoundDoom Good g Carry claim pre ∧
        ∃ c0 tail, tail.length = count - 2 ∧ msg = roundMessage claim c0 tail)
        (Post := fun c _ ↦ RoundDoom Good g Carry (polyEval msg c) (pre ++ [c])) (T := 0)
        (εmax := εmsg) (roundError count) fun _ ⟨hD, c0, tail, htail, hmsg⟩ ↦ by
          subst hmsg
          have hb := card_round_escape (c0 := c0) hg hcarry htail hc hk0
            (show pre.length < n by omega) hD
          rw [roundError, ENNReal.div_eq_inv_mul]
          exact mul_le_mul' le_rfl (by exact_mod_cast hb)
    refine (hS.bind' fun c ↦ ?_).mono (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl (by simp) le_rfl
    exact (roundsSpec count hc hg hcarry k (polyEval msg c) (pre ++ [c]) (by simp; omega) (by simp; omega)).bind'
      fun r ↦ (Spec.ret (Post := fun r _ ↦ r.1.length = k + 1 ∧
          RoundDoom Good g Carry r.2 (pre ++ r.1))
        (c :: r.1, r.2)).mono (fun _ h ↦ ⟨by simp [h.1], by simpa [List.append_assoc] using h.2⟩)
        (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

/-! ## Carried polynomials -/

/-- `f` of `n` variables is a polynomial of degree at most `d` in each variable, the others fixed. -/
def PerVarDeg (f : List E → E) (n d : ℕ) : Prop :=
  ∀ pre rest : List E, pre.length + 1 + rest.length = n →
    ∃ p : Polynomial E, p.natDegree ≤ d ∧ ∀ c, p.eval c = f (pre ++ c :: rest)

/-- `f` restricted to the challenges `pre` drawn so far is not zero on the rest: some completion of
`pre` to `n` variables makes it nonzero. -/
def NonzeroAfter (f : List E → E) (n : ℕ) (pre : List E) : Prop :=
  ∃ rest : List E, pre.length + rest.length = n ∧ f (pre ++ rest) ≠ 0

/-- **A nonzero polynomial survives a challenge** but at its roots: at most `d`. -/
theorem card_nonzeroAfter_escape {f : List E → E} {n d : ℕ} (hf : PerVarDeg f n d)
    (pre : List E) (hpre : pre.length < n) (hnz : NonzeroAfter f n pre) :
    (univ.filter fun c ↦ ¬ NonzeroAfter f n (pre ++ [c])).card ≤ d := by
  obtain ⟨rest, hlen, hne⟩ := hnz
  obtain ⟨c₀, rest', rfl⟩ : ∃ c₀ rest', rest = c₀ :: rest' := by
    cases rest with
    | nil => simp at hlen; omega
    | cons c₀ rest' => exact ⟨c₀, rest', rfl⟩
  obtain ⟨p, hp, hval⟩ := hf pre rest' (by simp at hlen; omega)
  have hp0 : p ≠ 0 := by
    intro h
    apply hne
    rw [← hval c₀, h, Polynomial.eval_zero]
  calc (univ.filter fun c ↦ ¬ NonzeroAfter f n (pre ++ [c])).card
      ≤ p.roots.toFinset.card := by
        refine card_le_card fun c hc ↦ ?_
        simp only [mem_filter, mem_univ, true_and] at hc
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hp0, Polynomial.IsRoot, hval]
        by_contra hc'
        exact hc ⟨rest', by simp at hlen ⊢; omega, by simpa using hc'⟩
    _ ≤ p.roots.card := Multiset.toFinset_card_le _
    _ ≤ p.natDegree := Polynomial.card_roots' _
    _ ≤ d := hp

/-- At all `n` challenges, a nonzero restriction is a nonzero value. -/
theorem nonzeroAfter_full {f : List E → E} {n : ℕ} {pre : List E} (h : pre.length = n)
    (hnz : NonzeroAfter f n pre) : f pre ≠ 0 := by
  obtain ⟨rest, hlen, hne⟩ := hnz
  obtain rfl : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
  simpa using hne

/-- **A carry that is a nonzero restriction of one of a family, or a fixed fact**, breaking at most
`d ≤ count − 1` challenges a round. -/
theorem card_carry_escape {ι : Type} {f : ι → List E → E} {n d count : ℕ}
    (hf : ∀ i, PerVarDeg (f i) n d) (hd : d ≤ count - 1) (φ : Prop) (pre : List E)
    (hpre : pre.length < n) (hC : (∃ i, NonzeroAfter (f i) n pre) ∨ φ) :
    (univ.filter fun c ↦ ¬ ((∃ i, NonzeroAfter (f i) n (pre ++ [c])) ∨ φ)).card ≤ count - 1 := by
  rcases hC with ⟨i, h⟩ | h
  · exact le_trans (card_le_card fun c hc ↦ by
      simp only [mem_filter, mem_univ, true_and, not_or, not_exists] at hc ⊢; exact hc.1 i)
      ((card_nonzeroAfter_escape (hf i) pre hpre h).trans hd)
  · simp [h]

end

end LeanVM.Protocol.Relation
