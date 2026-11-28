/-
  LeanVM.Prover.Complete.Keccak.Sumcheck

  The honest sumcheck rounds win the verifier's `sumcheck`, and the statement's stateful
  sumcheck prover makes their moves.
-/

module

public import LeanVM.Prover.Complete.Keccak.Script
public import LeanVM.Protocol.EndToEnd.Complete.PolyLE
public import LeanVM.Protocol.Field
import Mathlib.Algebra.Polynomial.Roots
import LeanVM.Protocol.Tables
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Honest sumcheck rounds

The verifier's `sumcheck claim count modes` (`Statement/Verifier/Sumcheck.lean`) reads per round a
polynomial of `count` coefficients with one left out (the linear one in plain mode, the constant
one in equality mode), derives it from the running claim, grinds for the round's degree, and
samples the challenge. The honest prover is given the claims as a function `claimOf` of the
challenges so far; it is honest where every next claim is a polynomial of degree below `count` in
the next challenge (`PolyLE`) and the next claims at `0` and `1` split the current one as the mode
reads it (`RoundSplit`).

* `hSumcheck`: the honest rounds, each message the coefficient list of the next claim
  (`coeffsOf`) on the wire (`wire`), then the round's grind (`roundBits`) and the challenge;
  `wins_sumcheck`: they win the verifier's rounds, to the challenges drawn and the final claim.
* `coeffsOf_eq`: `coeffsOf` is any coefficient list of the right length that evaluates as the
  claim; `corr_sumcheckBy_lt`: the statement's stateful prover `sumcheckBy` makes `hSumcheck`'s
  moves, given an invariant under which its coefficients evaluate as the claims.
-/

@[expose] public section

namespace LeanVM.Prover.Complete.Keccak

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Prover
open LeanVM.Protocol.EndToEnd.Complete Polynomial

variable {B : ℕ}

/-! ## Coefficient lists -/

/-- The coefficient list of a polynomial function of degree at most `d`, `d + 1` coefficients,
constant first (zeros if `f` is not one). -/
noncomputable def coeffsOf (d : ℕ) (f : E → E) : List E :=
  open Classical in
  if h : PolyLE d f then (List.range (d + 1)).map (Classical.choose h).coeff
  else List.replicate (d + 1) 0

theorem length_coeffsOf (d : ℕ) (f : E → E) : (coeffsOf d f).length = d + 1 := by
  unfold coeffsOf
  split <;> simp

/-- The coefficient list evaluates as the function. -/
theorem polyEval_coeffsOf {d : ℕ} {f : E → E} (h : PolyLE d f) (x : E) :
    polyEval (coeffsOf d f) x = f x := by
  classical
  have hc : coeffsOf d f = (List.range (d + 1)).map (Classical.choose h).coeff := by
    simp [coeffsOf, h]
  obtain ⟨hdeg, hev⟩ := Classical.choose_spec h
  rw [hc, polyEval_eq_sum, hev, eval_eq_sum_range' (Nat.lt_succ_of_le hdeg)]
  simp only [List.length_map, List.length_range]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp

/-- The polynomial whose coefficients, constant first, are `l`. -/
noncomputable def polyOfList (l : List E) : E[X] :=
  ∑ i ∈ Finset.range l.length, C (l.getD i 0) * X ^ i

theorem eval_polyOfList (l : List E) (x : E) : (polyOfList l).eval x = polyEval l x := by
  rw [polyEval_eq_sum, polyOfList, eval_finsetSum]
  simp

theorem coeff_polyOfList (l : List E) (i : ℕ) : (polyOfList l).coeff i = l.getD i 0 := by
  rw [polyOfList, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split
  · rfl
  · rename_i h
    rw [List.getD_eq_default _ _ (by simpa using h)]

theorem natDegree_polyOfList (l : List E) : (polyOfList l).natDegree ≤ l.length - 1 := by
  refine natDegree_sum_le_of_forall_le _ _ fun i hi ↦ ?_
  refine (natDegree_C_mul_X_pow_le _ _).trans ?_
  have := Finset.mem_range.mp hi
  omega

/-- **`coeffsOf` is any coefficient list of the right length** that evaluates as the function. -/
theorem coeffsOf_eq {d : ℕ} {l : List E} (hl : l.length = d + 1) (hd : d < 2 ^ 128) {f : E → E}
    (hf : ∀ x, polyEval l x = f x) : coeffsOf d f = l := by
  classical
  have hP : PolyLE d f :=
    ⟨polyOfList l, (natDegree_polyOfList l).trans (by omega), fun x ↦ by
      rw [eval_polyOfList, hf]⟩
  have hc : coeffsOf d f = (List.range (d + 1)).map (Classical.choose hP).coeff := by
    simp [coeffsOf, hP]
  obtain ⟨hdeg, hev⟩ := Classical.choose_spec hP
  have hQ : Classical.choose hP = polyOfList l := by
    refine eq_of_natDegree_lt_card_of_eval_eq (ι := E) _ _ Function.injective_id
      (fun x ↦ ?_) ?_
    · simp only [id]
      rw [← hev, eval_polyOfList, hf]
    · rw [LeanVM.Protocol.card_E]
      have := natDegree_polyOfList l
      omega
  rw [hc, hQ]
  refine List.ext_getElem (by simp [hl]) fun i h₁ h₂ ↦ ?_
  simp only [List.getElem_map, List.getElem_range, coeff_polyOfList]
  exact List.getD_eq_getElem _ _ h₂

/-! ## One round -/

/-- The grind after a round of `count` coefficients in the mode `mode`. -/
def roundBits (count : ℕ) (mode : Option E) : ℕ :=
  grindingBits (count - 1 + if mode.isSome then 1 else 0)

/-- The statement's round grind is `roundBits`, for a round of `count` coefficients. -/
theorem roundGrind_eq {count : ℕ} {c : List E} (hc : c.length = count) (mode : Option E) :
    roundGrind mode c = roundBits count mode := by
  subst hc; rfl

/-- A program then a final step that only returns, beside a script with no final step. -/
theorem wins_bind_ret {α β γ : Type} {R : α → β → Bool → List Committed → Prop}
    {Q : γ → β → Bool → List Committed → Prop} {p : VerifierProgram α} {s : Script β}
    {f : α → VerifierProgram γ} {g : Bool} {cs : List Committed} (h : Wins B R p s g cs)
    (hk : ∀ a b g cs, R a b g cs → Wins B Q (f a) (.ret b) g cs) :
    Wins B Q (p.bind f) s g cs := by
  have := LeanVM.Prover.Wins.bind (t := Script.ret) hk p s g cs h
  rwa [sbind_ret] at this

/-- **One round.** A coefficient list whose values at `0` and `1` pass the mode's check, then the
round's grind, wins the verifier's `sumcheckRoundPoly`, which rebuilds the list from the wire. -/
theorem wins_roundPoly (count : ℕ) (claim : E) (mode : Option E) (coeffs : List E)
    (hlen : coeffs.length = count) (hcount : 2 ≤ count) (hB : roundBits count mode ≤ B)
    (hsplit : RoundSplit mode claim (polyEval coeffs 0) (polyEval coeffs 1)) (cs : List Committed) :
    Wins B (fun a _ _ cs' ↦ a = coeffs ∧ cs' = cs) (sumcheckRoundPoly count claim mode)
      ((Script.sendList (wire mode coeffs)).bind fun _ ↦ Script.grindBits (roundBits count mode))
      false cs := by
  obtain ⟨c0, c1, rest, rfl⟩ : ∃ c0 c1 rest, coeffs = c0 :: c1 :: rest := by
    match coeffs, hlen with
    | c0 :: c1 :: rest, _ => exact ⟨c0, c1, rest, rfl⟩
    | [], h => simp at h; omega
    | [_], h => simp at h; omega
  have hrest : rest.length = count - 2 := by simp at hlen; omega
  rw [polyEval_zero_cons, polyEval_one] at hsplit
  cases mode with
  | none =>
    simp only [RoundSplit, List.sum_cons] at hsplit
    have hrb : roundBits count none = grindingBits (count - 1) := by simp [roundBits]
    rw [hrb] at hB ⊢
    show Wins B _ (VerifierProgram.read fun constant ↦
        (VerifierProgram.readScalars (count - 2)).bind fun tail ↦
        (VerifierProgram.grindProofOfWork (grindingBits (count - 1))).bind fun _ ↦
        VerifierProgram.ret (constant :: (claim + sumE tail) :: tail))
      (Script.send c0 ((Script.sendList rest).bind fun _ ↦
        Script.grindBits (grindingBits (count - 1)))) false cs
    refine ⟨rfl, ?_⟩
    rw [← hrest]
    refine LeanVM.Prover.Wins.bind (fun b _ g₁ cs₁ h₁ ↦ ?_) _ _ _ _
      (Wins.sendList_readScalars cs rest)
    obtain ⟨rfl, rfl, rfl⟩ := h₁
    refine wins_bind_ret (Wins.grindBits hB cs₁) fun _ _ g₂ cs₂ h₂ ↦ ?_
    obtain ⟨-, rfl⟩ := h₂
    refine ⟨?_, rfl⟩
    simp only [List.cons.injEq, true_and, and_true]
    rw [LeanVM.Protocol.Tables.sumE_eq, ← hsplit]
    linear_combination (CharTwo.two_eq_zero (R := E)) * (c0 + b.sum)
  | some r =>
    simp only [RoundSplit, List.sum_cons] at hsplit
    have hl : (c1 :: rest).length = count - 1 := by simp; omega
    have hrb : roundBits count (some r) = grindingBits (count - 1 + 1) := by simp [roundBits]
    rw [hrb] at hB ⊢
    show Wins B _ ((VerifierProgram.readScalars (count - 1)).bind fun tail ↦
        (VerifierProgram.grindProofOfWork (grindingBits (count - 1 + 1))).bind fun _ ↦
        VerifierProgram.ret ((claim + r * sumE tail) :: tail))
      ((Script.sendList (c1 :: rest)).bind fun _ ↦
        Script.grindBits (grindingBits (count - 1 + 1))) false cs
    rw [← hl]
    refine LeanVM.Prover.Wins.bind (fun b _ g₁ cs₁ h₁ ↦ ?_) _ _ _ _
      (Wins.sendList_readScalars cs (c1 :: rest))
    obtain ⟨rfl, rfl, rfl⟩ := h₁
    refine wins_bind_ret (Wins.grindBits (by rwa [hl]) cs₁) fun _ _ g₂ cs₂ h₂ ↦ ?_
    obtain ⟨-, rfl⟩ := h₂
    refine ⟨?_, rfl⟩
    simp only [List.cons.injEq, and_true]
    rw [LeanVM.Protocol.Tables.sumE_eq, List.sum_cons, ← hsplit]
    linear_combination (CharTwo.two_eq_zero (R := E)) * (r * c0 + r * c1 + r * rest.sum)

/-! ## The rounds -/

/-- **The honest sumcheck prover** for the rounds `modes`, after the challenges `pre`: per round,
the coefficients of the next claim as a polynomial of degree below `count`, on the wire, and the
round's grind; then the challenge. Returns the challenges drawn and the final claim. -/
noncomputable def hSumcheck (count : ℕ) (claimOf : List E → E) :
    List (Option E) → List E → Script (List E × E)
  | [], pre => .ret ([], claimOf pre)
  | mode :: modes, pre =>
    ((Script.sendList (wire mode (coeffsOf (count - 1) fun x ↦ claimOf (pre ++ [x])))).bind
      fun _ ↦ Script.grindBits (roundBits count mode)).bind fun _ ↦ Script.sampleE.bind fun c ↦
        (hSumcheck count claimOf modes (pre ++ [c])).bind fun r ↦ .ret (c :: r.1, r.2)

/-- **The honest rounds win the verifier's.** If every next claim is a polynomial of degree below
`count` in the next challenge and the next claims at `0, 1` split the current one as the round's
mode checks it, the honest prover wins `sumcheck (claimOf pre) count modes`, to the challenges it
draws and the final claim `claimOf (pre ++ challenges)`. -/
theorem wins_sumcheck (count : ℕ) (hcount : 2 ≤ count) (claimOf : List E → E) :
    ∀ (modes : List (Option E)) (pre : List E) (cs : List Committed),
      (∀ m ∈ modes, roundBits count m ≤ B) →
      (∀ ext : List E, ext.length < modes.length →
        PolyLE (count - 1) fun x ↦ claimOf (pre ++ ext ++ [x])) →
      (∀ ext : List E, (h : ext.length < modes.length) →
        RoundSplit modes[ext.length] (claimOf (pre ++ ext)) (claimOf (pre ++ ext ++ [0]))
          (claimOf (pre ++ ext ++ [1]))) →
      Wins B (fun a b g' cs' ↦ a = b ∧ b.1.length = modes.length ∧ b.2 = claimOf (pre ++ b.1) ∧
          g' = false ∧ cs' = cs)
        (sumcheck (claimOf pre) count modes) (hSumcheck count claimOf modes pre) false cs
  | [], pre, cs, _, _, _ => ⟨rfl, rfl, by simp, rfl, rfl⟩
  | mode :: modes, pre, cs, hB, hdeg, hsplit => by
    have hd := hdeg [] (by simp)
    simp only [List.append_nil] at hd
    have hround := wins_roundPoly (B := B) count (claimOf pre) mode
      (coeffsOf (count - 1) fun x ↦ claimOf (pre ++ [x])) (by rw [length_coeffsOf]; omega) hcount
      (hB mode (by simp))
      (by
        have h := hsplit [] (by simp)
        simp only [List.append_nil, List.length_nil, List.getElem_cons_zero] at h
        rwa [polyEval_coeffsOf hd, polyEval_coeffsOf hd]) cs
    simp only [hSumcheck, sumcheck, VerifierProgram.bind_eq]
    refine LeanVM.Prover.Wins.bind (fun msg _ g₁ cs₁ h₁ ↦ ?_) _ _ _ _ hround
    obtain ⟨rfl, h₁⟩ := h₁
    subst cs₁
    refine LeanVM.Prover.Wins.bind (fun c c' g₂ cs₂ h₂ ↦ ?_) _ _ _ _ (Wins.sampleE g₁ cs)
    obtain ⟨rfl, rfl, h₂⟩ := h₂
    subst cs₂
    rw [polyEval_coeffsOf hd]
    have ih := wins_sumcheck count hcount claimOf modes (pre ++ [c]) cs
      (fun m hm ↦ hB m (by simp [hm]))
      (fun ext hext ↦ by simpa using hdeg (c :: ext) (by simpa using hext))
      (fun ext hext ↦ by simpa using hsplit (c :: ext) (by simpa using hext))
    refine LeanVM.Prover.Wins.bind (fun r r' g₃ cs₃ h₃ ↦ ?_) _ _ _ _ ih
    obtain ⟨rfl, hl, hf, rfl, h₃⟩ := h₃
    subst cs₃
    obtain ⟨pt, fin⟩ := r
    simp only at hl hf ⊢
    exact ⟨rfl, by simp [hl], by simpa using hf, rfl, rfl⟩

/-! ## The stateful prover -/

/-- **The stateful sumcheck over at most `n` rounds** makes the moves of `hSumcheck`, given the
invariant along the rounds before the `n`-th. -/
theorem corr_sumcheckBy_lt {σ : Type} (count : ℕ) (hc : 1 ≤ count) (hc' : count ≤ 2 ^ 128)
    (claimOf : List E → E) (round : σ → List E) (fold : σ → E → σ) (Inv : List E → σ → Prop)
    (n : ℕ)
    (hround : ∀ pre st, Inv pre st → pre.length < n →
      (round st).length = count ∧ ∀ x, polyEval (round st) x = claimOf (pre ++ [x]))
    (hfold : ∀ pre st c, Inv pre st → pre.length < n → Inv (pre ++ [c]) (fold st c)) :
    ∀ (modes : List (Option E)) (pre : List E) (st : σ), Inv pre st →
      pre.length + modes.length ≤ n →
      Corr (fun a b ↦ a.1 = b.1 ∧ Inv (pre ++ a.1) a.2 ∧ b.2 = claimOf (pre ++ b.1) ∧
          a.1.length = modes.length)
        (sumcheckBy round fold modes st) (hSumcheck count claimOf modes pre)
  | [], pre, st, h, _ => Corr.ret_ret ⟨rfl, by simpa using h, by simp, rfl⟩
  | mode :: modes, pre, st, h, hn => by
    have hlt : pre.length < n := by simp at hn; omega
    obtain ⟨hlen, hev⟩ := hround pre st h hlt
    have hco : coeffsOf (count - 1) (fun x ↦ claimOf (pre ++ [x])) = round st :=
      coeffsOf_eq (by omega) (by omega) hev
    simp only [sumcheckBy, hSumcheck, hco, sbind_assoc, roundGrind_eq hlen]
    refine Corr.bind_same _ fun _ ↦ Corr.bind_same _ fun _ ↦ Corr.bind_same _ fun c ↦ ?_
    refine Corr.bind (fun a b hab ↦ ?_) _ _
      (corr_sumcheckBy_lt count hc hc' claimOf round fold Inv n hround hfold modes (pre ++ [c])
        (fold st c) (hfold pre st c h hlt) (by simp at hn ⊢; omega))
    obtain ⟨h1, h2, h3, h4⟩ := hab
    simp only [Corr, List.append_assoc, List.singleton_append] at h2 h3 ⊢
    exact ⟨by rw [h1], h2, h3, by simp [h4]⟩

/-- The challenges drawn. -/
theorem corr_sampleN : ∀ n : ℕ,
    Corr (fun a b ↦ a = b ∧ a.length = n) (Script.sampleN n) (Script.sampleN n)
  | 0 => Corr.ret_ret ⟨rfl, rfl⟩
  | n + 1 => by
    show Corr _ (Script.sampleE.bind fun x ↦ (Script.sampleN n).bind fun xs ↦ .ret (x :: xs))
      (Script.sampleE.bind fun x ↦ (Script.sampleN n).bind fun xs ↦ .ret (x :: xs))
    refine Corr.bind_same _ fun x ↦ Corr.bind (fun a b h ↦ ?_) _ _ (corr_sampleN n)
    obtain ⟨rfl, h⟩ := h
    exact Corr.ret_ret ⟨rfl, by simp [h]⟩

/-- Equal lists sent, then related continuations. -/
theorem corr_sendList {α β : Type} {S : α → β → Prop} {l l' : List E} (h : l = l')
    {f : Unit → Script α} {g : Unit → Script β} (hk : Corr S (f ()) (g ())) :
    Corr S ((Script.sendList l).bind f) ((Script.sendList l').bind g) := by
  subst h
  exact Corr.bind_same _ fun _ ↦ hk

/-- Equal scalars sent, then related continuations. -/
theorem corr_sendE {α β : Type} {S : α → β → Prop} {x x' : E} (h : x = x')
    {f : Unit → Script α} {g : Unit → Script β} (hk : Corr S (f ()) (g ())) :
    Corr S ((Script.sendE x).bind f) ((Script.sendE x').bind g) := by
  subst h
  exact Corr.bind_same _ fun _ ↦ hk

end LeanVM.Prover.Complete.Keccak

end
