/-
  LeanVM.Protocol.ToArkLib.Flock.RingSwitch

  Ring switching with the staged Frobenius map, as components: from claims on the Boolean tables
  packed into one table to one weighted claim on a table the packed one is read from, with its
  completeness. Candidate for ArkLib.
-/

module

public import LeanVM.Protocol.ToArkLib.Flock.Lincheck
public import LeanVM.Protocol.ToArkLib.Flock.FrobeniusMap
public import LeanVM.Protocol.ToArkLib.WeightCombination
public import LeanVM.Protocol.ToCompPoly.Frobenius

/-!
# Ring switching

The lincheck leaves `2 ^ s` claims `s_i = ẑ_i(r')` on Boolean tables `z_i`, which are packed into
one table over a ring `K` by a generator `g`: `col(u) = Σ_i z_i(u) · g^i` (Annex A, §A.1). The
packed table is read off a table `stack` of `μ` variables by a lift of points (`hread`), and only
weighted claims on `stack` can be proved. Ring switching turns the family into one weighted claim
(Annex A, §A.2): the verifier draws the coefficients `f_0, …, f_{s'}` of a staged additive map
`Φ` (`frobMap` with shifts `2 ^ (s' - p)`), and the claim is `⟨W, stack⟩ = T` with
`T = Σ_i g^i · Φ(s_i)` and `W = Σ_{(c, e)} c · eq(lift(r'^(2^e)), ·)` over the terms of `Φ` as a
Frobenius sum. Two components:

1. `ringDraws p`: the first `p` coefficients. The state (`ringRel p`): with
   `δ_i = s_i - ẑ_i(r')` and `Φ_p` the first `p` stages, every
   `π_k = Σ_i g^i · Φ_p(δ_i) ^ 2 ^ k`, `k < 2 ^ (s' + 1 - p)`, is zero.
2. `ringFinal`: the last coefficient, and the weighted claim handed on through `finish`.

Completeness (`ringSwitchComplete`) is the identity `⟨W, stack⟩ = Σ_i g^i · Φ(ẑ_i(r'))`
(`pair_ringWeight`): the read law, the packing, the Frobenius on Boolean tables
(`evalMle_frob_of_bool`) and the Frobenius-sum form of `Φ` (`frobMap_eq_sum`).

Nothing here transcribes a source.
-/

namespace LeanVM.Protocol

namespace Flock

open CompPoly CMlPolynomialEval OracleComp OracleSpec

@[expose] public section

variable {F : Type} [Field F] [DecidableEq F] [SampleableType F] (P : Params F)
  {ι : Type} {O : ι → Type} [∀ i, OracleInterface (O i)] {W : Type}
  (z : (∀ i, O i) → Fin (2 ^ P.s) → CMlPolynomialEval F (P.m + P.κ))
  {S : Type} (side : S → (∀ i, O i) → Prop) (s' : ℕ)

/-- The stages after `p` coefficients: stage `i` has shift `2 ^ (s' - i)` and coefficient
`f_i`. -/
def ringStages {p : ℕ} (fs : Vector F p) : List (ℕ × F) :=
  List.ofFn fun i : Fin p ↦ (2 ^ (s' - i.val), fs[i])

omit [Field F] [DecidableEq F] [SampleableType F] in
theorem ringStages_push {p : ℕ} (fs : Vector F p) (x : F) :
    ringStages s' (fs.push x) = ringStages s' fs ++ [(2 ^ (s' - p), x)] := by
  rw [ringStages, List.ofFn_succ_last]
  simp [ringStages]

/-- The statement while the coefficients are drawn: the lincheck's output and the coefficients
so far. -/
abbrev RingStmt (S F : Type) (n s p : ℕ) : Type := OutStmt S F n s × Vector F p

variable {K : Type} [CommRing K] (φ : K →+* F) (g : K)

/-- The error of slice `i`: the claimed value minus the table's extension at the point. -/
def sliceError (o : ∀ i, O i) (st : OutStmt S F (P.m + P.κ) P.s) (i : Fin (2 ^ P.s)) : F :=
  st.2.2[i] - evalMle (z o i) st.2.1

/-- While the coefficients are drawn: the side condition, and every `π_k`, `k < 2^(s' + 1 - p)`,
of the slices' errors under the stages so far is zero. -/
def ringRel (p : ℕ) : Set ((RingStmt S F (P.m + P.κ) P.s p × ∀ i, O i) × W) :=
  {q | side q.1.1.1.1 q.1.2 ∧ ∀ k < 2 ^ (s' + 1 - p),
    frobPair Finset.univ (fun i : Fin (2 ^ P.s) ↦ φ (g ^ i.val))
      (fun i ↦ frobMap (ringStages s' q.1.1.2) (sliceError P z q.1.2 q.1.1.1 i)) k = 0}

instance [∀ s o, Decidable (side s o)] (p : ℕ)
    (q : (RingStmt S F (P.m + P.κ) P.s p × ∀ i, O i) × W) :
    Decidable (q ∈ ringRel P z side s' φ g p) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- One coefficient, as a typed component. -/
def ringDraw (p : ℕ) :
    Typed.Def O (RingStmt S F (P.m + P.κ) P.s p) W (RingStmt S F (P.m + P.κ) P.s (p + 1)) W
      (Typed.drawSlot F) :=
  Typed.sampleChallenge O F (fun _ ↦ true) fun st x ↦ (st.1, st.2.push x)

/-- The first `p` coefficients, as a typed component. -/
def ringDraws : (p : ℕ) →
    Typed.Def O (OutStmt S F (P.m + P.κ) P.s) W (RingStmt S F (P.m + P.κ) P.s p) W
      (Typed.drawsSlot F p)
  | 0 => Typed.passThrough O fun st ↦ (st, #v[])
  | p + 1 => (ringDraws p).append (ringDraw P p)

variable {μ : ℕ} (lift : Vector F (P.m + P.κ) → Vector F μ)

/-- The weight of the switched claim: `Σ_{(c, e)} c · eq(lift(r'^(2^e)), ·)` over the terms of the
staged map. -/
def ringWeight (r' : Vector F (P.m + P.κ)) (fs : Vector F (s' + 1)) : Weight F μ :=
  Weight.combine
    ((frobTerms (ringStages s' fs)).map fun t ↦ (t.1, eqWeight (lift (frobPoint t.2 r'))))

/-- The target of the switched claim: `Σ_i g^i · Φ(s_i)`. -/
def ringTarget (sv : Vector F (2 ^ P.s)) (fs : Vector F (s' + 1)) : F :=
  ∑ i : Fin (2 ^ P.s), φ (g ^ i.val) * frobMap (ringStages s' fs) sv[i]

/-- The last coefficient, as a typed component. -/
def ringFinal {StmtOut : Type} (finish : S → Weight F μ → F → StmtOut) :
    Typed.Def O (RingStmt S F (P.m + P.κ) P.s s') W StmtOut W (Typed.drawSlot F) :=
  Typed.sampleChallenge O F (fun _ ↦ true) fun st x ↦
    finish st.1.1 (ringWeight P s' lift st.1.2.1 (st.2.push x))
      (ringTarget P s' φ g st.1.2.2 (st.2.push x))

/-- Ring switching, as a typed component. -/
def ringSwitch {StmtOut : Type} (finish : S → Weight F μ → F → StmtOut) :
    Typed.Def O (OutStmt S F (P.m + P.κ) P.s) W StmtOut W (Typed.drawsSlot F (s' + 1)) :=
  (ringDraws P s').append (ringFinal P s' φ g lift finish)

/-! ## Completeness -/

omit [DecidableEq F] [SampleableType F] [∀ i, OracleInterface (O i)] in
/-- Swapping a list sum and a finite sum. -/
private theorem list_sum_finset_sum {α : Type*} {β : Type*} (l : List α) (s : Finset β)
    (f : α → β → F) : (l.map fun a ↦ ∑ b ∈ s, f a b).sum = ∑ b ∈ s, (l.map fun a ↦ f a b).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, Finset.sum_add_distrib]

variable [CharP F 2] (col : (∀ i, O i) → CMlPolynomialEval K (P.m + P.κ))
  (stack : (∀ i, O i) → CMlPolynomialEval K μ)

omit [DecidableEq F] [SampleableType F] [∀ i, OracleInterface (O i)] in
/-- **The ring-switching identity.** If the packed table is the Boolean tables packed by `g` and
is read off `stack` through `lift`, the answer of `stack` to the switched weight is
`Σ_i g^i · Φ(ẑ_i(r'))`. -/
theorem pair_ringWeight
    (hcell : ∀ o (u : Fin (2 ^ (P.m + P.κ))),
      φ (col o)[u] = ∑ i : Fin (2 ^ P.s), φ (g ^ i.val) * (z o i)[u])
    (hbool : ∀ o i (u : Fin (2 ^ (P.m + P.κ))), (z o i)[u] = 0 ∨ (z o i)[u] = 1)
    (hread : ∀ o p, eval₂Mle (col o) φ p = eval₂Mle (stack o) φ (lift p))
    (o : ∀ i, O i) (r' : Vector F (P.m + P.κ)) (fs : Vector F (s' + 1)) :
    (ringWeight P s' lift r' fs).pair φ (stack o) =
      ∑ i : Fin (2 ^ P.s), φ (g ^ i.val) * frobMap (ringStages s' fs) (evalMle (z o i) r') := by
  -- The packed table's extension is the packing of the tables' extensions.
  have hpack : ∀ p, eval₂Mle (col o) φ p = ∑ i : Fin (2 ^ P.s), φ (g ^ i.val) * evalMle (z o i) p :=
    fun p ↦ by
      rw [eval₂Mle, evalMle_eq_sum]
      simp only [CMlPolynomialEval.map, Fin.getElem_fin, Vector.getElem_map, evalMle_eq_sum,
        Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun u _ ↦ ?_
      have := hcell o u
      simp only [Fin.getElem_fin] at this
      rw [this, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ ↦ by ring
  rw [ringWeight, Weight.pair_combine, List.map_map]
  simp only [Function.comp_def, Weight.pair_eqWeight, ← hread, hpack, Finset.mul_sum]
  rw [list_sum_finset_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [frobMap_eq_sum, ← List.sum_map_mul_left]
  congr 1
  refine List.map_congr_left fun t _ ↦ ?_
  rw [← evalMle_frob_of_bool t.2 (z o i) (hbool o i) r']
  ring

omit [DecidableEq F] [SampleableType F] [∀ i, OracleInterface (O i)] [CharP F 2] in
/-- One more stage: the stage with shift `2 ^ (s' - p)` and coefficient `x` after the others. -/
theorem frobMap_ringStages_push {p : ℕ} (fs : Vector F p) (x a : F) :
    frobMap (ringStages s' (fs.push x)) a =
      frobMap (ringStages s' fs) a + x * frobMap (ringStages s' fs) a ^ 2 ^ 2 ^ (s' - p) := by
  rw [ringStages_push, frobMap_append]
  rfl

omit [DecidableEq F] [SampleableType F] [∀ i, OracleInterface (O i)] in
/-- With every `π` of the errors zero before the last stage, the target is the answer of `stack`
to the weight. -/
theorem pair_ringWeight_eq_ringTarget
    (hcell : ∀ o (u : Fin (2 ^ (P.m + P.κ))),
      φ (col o)[u] = ∑ i : Fin (2 ^ P.s), φ (g ^ i.val) * (z o i)[u])
    (hbool : ∀ o i (u : Fin (2 ^ (P.m + P.κ))), (z o i)[u] = 0 ∨ (z o i)[u] = 1)
    (hread : ∀ o p, eval₂Mle (col o) φ p = eval₂Mle (stack o) φ (lift p))
    (o : ∀ i, O i) (st : OutStmt S F (P.m + P.κ) P.s) (fs : Vector F s') (x : F)
    (h0 : frobPair Finset.univ (fun i : Fin (2 ^ P.s) ↦ φ (g ^ i.val))
      (fun i ↦ frobMap (ringStages s' fs) (sliceError P z o st i)) 0 = 0)
    (h1 : frobPair Finset.univ (fun i : Fin (2 ^ P.s) ↦ φ (g ^ i.val))
      (fun i ↦ frobMap (ringStages s' fs) (sliceError P z o st i)) 1 = 0) :
    (ringWeight P s' lift st.2.1 (fs.push x)).pair φ (stack o) =
      ringTarget P s' φ g st.2.2 (fs.push x) := by
  rw [pair_ringWeight P z s' φ g lift col stack hcell hbool hread, ringTarget]
  symm
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
  have hstage := frobPair_stage Finset.univ (fun i : Fin (2 ^ P.s) ↦ φ (g ^ i.val))
    (fun i ↦ frobMap (ringStages s' fs) (sliceError P z o st i)) 1 x 0
  rw [h0, h1, mul_zero, add_zero] at hstage
  have hΦ : ∀ a, frobMap (ringStages s' (fs.push x)) a =
      frobMap (ringStages s' fs) a + x * frobMap (ringStages s' fs) a ^ 2 ^ 1 := fun a ↦ by
    rw [frobMap_ringStages_push, Nat.sub_self, pow_zero]
  rw [← hstage, frobPair]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← mul_sub, pow_zero, pow_one, ← hΦ, sliceError]
  congr 1
  exact (map_sub (frobMapHom (ringStages s' (fs.push x))) _ _).symm

/-! ## The components and their completeness -/

omit [DecidableEq F] [∀ i, OracleInterface (O i)] in
/-- Typed completeness of one coefficient. -/
theorem ringDrawComplete (p : ℕ) (hp : p ≤ s') :
    Typed.Complete (ringDraw P (S := S) (O := O) (W := W) p) (ringRel P z side s' φ g p)
      (ringRel P z side s' φ g (p + 1)) :=
  Typed.sampleChallengeComplete fun st o w h ↦ ⟨rfl, fun x ↦ ⟨h.1, fun k hk ↦ by
    show frobPair _ _ (fun i ↦ frobMap (ringStages s' (st.2.push x)) _) k = 0
    simp only [frobMap_ringStages_push]
    rw [frobPair_stage, h.2 k (by
        have : 2 ^ (s' - p) < 2 ^ (s' + 1 - p) :=
          Nat.pow_lt_pow_right (by norm_num) (by omega)
        have : 2 ^ (s' + 1 - (p + 1)) = 2 ^ (s' - p) := by congr 1; omega
        omega),
      h.2 (2 ^ (s' - p) + k) (by
        have h2 : 2 ^ (s' + 1 - p) = 2 * 2 ^ (s' - p) := by
          rw [show s' + 1 - p = (s' - p) + 1 by omega, pow_succ]
          ring
        have : 2 ^ (s' + 1 - (p + 1)) = 2 ^ (s' - p) := by congr 1; omega
        omega)]
    simp⟩⟩

omit [DecidableEq F] [∀ i, OracleInterface (O i)] in
/-- Typed completeness of the first `p` coefficients. -/
theorem ringDrawsComplete : (p : ℕ) → p ≤ s' →
    Typed.Complete (ringDraws P (S := S) (O := O) (W := W) p) (outRel P z side)
      (ringRel P z side s' φ g p)
  | 0, _ => Typed.passThroughComplete fun st o w h ↦ ⟨h.1, fun k _ ↦ by
      have herr : ∀ i, sliceError P z o st i = 0 := fun i ↦ by
        rw [sliceError, h.2 i, sub_self]
      simp only [ringStages, List.ofFn_zero, frobMap, frobPair, herr]
      simp⟩
  | p + 1, hp =>
    (ringDrawsComplete p (by omega)).append (ringDrawComplete P z side s' φ g p (by omega))

omit [DecidableEq F] [∀ i, OracleInterface (O i)] in
/-- Typed completeness of ring switching. -/
theorem ringSwitchComplete {StmtOut : Type} (finish : S → Weight F μ → F → StmtOut)
    (relOut : Set ((StmtOut × ∀ i, O i) × W))
    (hout : ∀ sIn o w (Wt : Weight F μ) T, side sIn o → Wt.pair φ (stack o) = T →
      ((finish sIn Wt T, o), w) ∈ relOut)
    (hcell : ∀ o (u : Fin (2 ^ (P.m + P.κ))),
      φ (col o)[u] = ∑ i : Fin (2 ^ P.s), φ (g ^ i.val) * (z o i)[u])
    (hbool : ∀ o i (u : Fin (2 ^ (P.m + P.κ))), (z o i)[u] = 0 ∨ (z o i)[u] = 1)
    (hread : ∀ o p, eval₂Mle (col o) φ p = eval₂Mle (stack o) φ (lift p)) :
    Typed.Complete (ringSwitch P s' φ g lift finish (O := O) (W := W)) (outRel P z side)
      relOut :=
  (ringDrawsComplete P z side s' φ g s' le_rfl).append
    (Typed.sampleChallengeComplete fun st o w h ↦ ⟨rfl, fun x ↦
      hout _ _ _ _ _ h.1 (pair_ringWeight_eq_ringTarget P z s' φ g lift col stack hcell hbool
        hread o st.1 st.2 x (h.2 0 (by simp)) (h.2 1 (by simp)))⟩)

end

end Flock

end LeanVM.Protocol
