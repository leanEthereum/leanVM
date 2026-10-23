/-
  LeanVM.Protocol.Whir.Sound.Start

  WHIR's starting relation in terms of the commitment's candidates: if every candidate stack
  violates the opening's claim, every member of the level-0 Johnson list violates the running
  claim the verifier starts from, `A(0, 0)`.
-/

module

public import LeanVM.Protocol.Whir.Sound.LevelFinal
public import LeanVM.Protocol.Whir.Sound.Candidates

/-!
# The starting relation

The opening's input (`verify_whir(log_n, log_inv_rate, target, root, evaluate_basis)`,
`python-verifier/verifier.py:1008` at leanVM `127510d14c98ade4e8a97646c44fa7f1ff5e752d`) is the
level-0 commitment `W₀`, a weight function `w` (the batched `evaluate_basis`, a function of a point
of the stack's cube, bit `0` first) and a target `t`. Its relation, in the terms of
`LeanVM.Protocol.EndToEnd.Candidates`: **every candidate `q` of `W₀` at the Johnson threshold
violates the claim**, `¬ StackClaim.Holds μ (w, t) q`, i.e. `Σ_j w(j) q_j ≠ t`.

The verifier's sumcheck runs in the order (lanes, message bits): the first `ℓ₀ = 6` variables are
the lanes, which are the stack's six high bits, and its weight at a point `p` is
`w(p[6:] ++ p[:6])` (`runW` of the initial state, the terminal check's rotated point).

* `rowsOf_laneO_zero`: the level-0 lane oracle is the candidates' lane word (`laneWord`, leaf
  words reversed) with lanes indexed by their bits.
* `claimSum_encStack`: the running claim of the encoding of a stack `q` is `Σ_j w(j) q_j`: the
  rotation exactly undoes the stack/lane relayout `f(u, x) = q(x, u)`.
* `levelPre_zero`: **the starting doom** `LevelPre` of level `0` from the candidates' violation,
  through the bridge `exists_candidate_of_mem_iList` (a list member is the encoding of a
  candidate: `K`-valuedness and injectivity of the encoder).
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd Finset

@[expose] public section

/-! ## Reindexing -/

/-- Lists are invariant under reindexing the rows. -/
theorem mem_iList_comp {F ι ρ ρ' : Type*} [Field F] [Fintype F] [Fintype ι] [Fintype ρ]
    [Fintype ρ'] (C : Submodule F (ι → F)) (A : ℕ) (e : ρ' ≃ ρ) (O V : ρ' → ι → F) :
    V ∈ iList C A O ↔ (fun r ↦ V (e.symm r)) ∈ iList C A (fun r ↦ O (e.symm r)) := by
  simp only [mem_iList, IsInterleavedCodeword, IsClose, AgreeOn]
  constructor
  · rintro ⟨hc, S, hS, hag⟩
    exact ⟨fun r ↦ hc _, S, hS, fun r x hx ↦ hag _ x hx⟩
  · rintro ⟨hc, S, hS, hag⟩
    refine ⟨fun r ↦ by simpa using hc (e r), S, hS, fun r x hx ↦ by simpa using hag (e r) x hx⟩

theorem bitsToNat_append {m n : ℕ} (x : Fin m → Bool) (u : Fin n → Bool) :
    bitsToNat (Fin.append x u) = bitsToNat x + 2 ^ m * bitsToNat u := by
  simp only [bitsToNat, Fin.sum_univ_add, Fin.append_left, Fin.append_right, Fin.val_castAdd,
    Fin.val_natAdd, pow_add, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ ↦ by ring

theorem boolPoint_bitsToNat {n : ℕ} (p : Fin n → Bool) : boolPoint n (bitsToNat p) = bitsL p := by
  refine List.ext_getElem (by simp [boolPoint]) fun i h₁ h₂ ↦ ?_
  simp only [boolPoint, List.getElem_map, List.getElem_range, bitsL, List.getElem_ofFn, bitE]
  have := testBit_bitsToNat p ⟨i, by simpa [boolPoint] using h₁⟩
  simp only at this
  rw [this]

/-- A sum over `2^(κ+m)` indices is a sum over the low `κ` and the high `m` bits. -/
theorem sum_split (κ m : ℕ) (f : ℕ → E) :
    ∑ j : Fin (2 ^ (κ + m)), f j =
      ∑ u : Fin m → Bool, ∑ x : Fin κ → Bool, f (bitsToNat x + 2 ^ κ * bitsToNat u) := by
  rw [← Equiv.sum_comp (bitsEquiv (κ + m)), ← (splitEquiv κ m).sum_comp, Fintype.sum_prod_type,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ ↦ Finset.sum_congr rfl fun x _ ↦ ?_
  simp [bitsEquiv_val, splitEquiv, bitsToNat_append]

/-! ## The level-0 oracle -/

theorem getD_map_ofK (l : List K) (j : ℕ) : (l.map ofK).getD j 0 = ofK (l.getD j 0) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[j]? <;> simp

/-- **The level-0 lane oracle** is the candidates' lane word. -/
theorem rowsOf_laneO_zero (μ R : ℕ) (cs : List (ℕ × ℕ × Word)) :
    rowsOf laneBits (laneO 0 cs (2 ^ (μ - laneBits + R))) =
      fun u ↦ laneWord μ R (wordOf cs 0) (bitsEquiv laneBits u) := by
  funext u v
  simp only [rowsOf, laneO, lanesOf, ↓reduceIte]
  rw [getD_map_ofK]
  simp [laneWord, laneOf, bitsEquiv_val]

/-- **The running claim of a stack's encoding** is the stack claim: the verifier's rotated
weight undoes the relayout `f(u, x) = q(x, u)`. -/
theorem claimSum_encStack {μ : ℕ} (hμ : laneBits ≤ μ) (w : List E → E) (q : Column μ) :
    claimSum (fun r ↦ w (rotL laneBits r)) (fun u ↦ blockOf q (bitsEquiv laneBits u)) =
      ∑ j : Fin (2 ^ μ), w (boolPoint μ j) * ofK (q.values.getD j 0) := by
  obtain ⟨κ, rfl⟩ : ∃ κ, μ = κ + laneBits := ⟨μ - laneBits, by omega⟩
  rw [sum_split κ laneBits (fun j ↦ w (boolPoint (κ + laneBits) j) * ofK (q.values.getD j 0)),
    claimSum]
  refine Finset.sum_congr rfl fun u _ ↦ Finset.sum_congr rfl fun x _ ↦ ?_
  have hrot : rotL laneBits (bitsL u ++ bitsL x) = bitsL x ++ bitsL u := by
    simp [rotL, List.drop_left' (length_bitsL u), List.take_left' (length_bitsL u)]
  rw [hrot, ← bitsL_append, ← boolPoint_bitsToNat, bitsToNat_append]
  simp [EndToEnd.blockOf, bitsEquiv_val]

/-! ## The starting doom -/

/-- WHIR's starting relation: the level-0 commitment has the right shape and every candidate of
its word violates the claim `(w, t)`. -/
def WhirPre (μ R : ℕ) (P₀ : LevelCode) (w : List E → E) (t : E) (cs : List (ℕ × ℕ × Word)) :
    Prop :=
  ShapeOK 0 P₀ laneBits cs ∧
    ∀ q ∈ Candidates μ R P₀.thr (wordOf cs 0), ¬ StackClaim.Holds μ (w, t) q

/-- **The starting doom**: from the candidates' violation and the first round polynomial,
`LevelPre` of level `0` for the initial state. -/
theorem levelPre_zero {μ R : ℕ} (P₀ : LevelCode) (hκ : P₀.κ = μ - laneBits) (hR : P₀.R = R)
    (hμ : laneBits ≤ μ) (w : List E → E) (t : E) (quad : List E) (cs : List (ℕ × ℕ × Word))
    (hpre : WhirPre μ R P₀ w t cs) (hq : QuadOK quad t) :
    LevelPre μ laneBits w 0 P₀ laneBits 0 ⟨t, quad, [], []⟩ cs := by
  refine ⟨⟨by simp, by simp, by omega, by simp [GluedOK], hq, ?_⟩, hpre.1⟩
  obtain ⟨-, hcand⟩ := hpre
  rcases P₀ with ⟨κ, R', η, h64, hκ1, hR1, hη, hagr⟩
  simp only at hκ hR
  subst hκ hR
  intro V hV
  simp only [List.length_nil, Nat.sub_zero, foldsN, List.foldl_nil] at hV
  have hV' : V ∈ iList (ReedSolomon.code (domain (μ - laneBits) R' h64) (2 ^ (μ - laneBits)))
      (LevelCode.thr ⟨μ - laneBits, R', η, h64, hκ1, hR1, hη, hagr⟩)
      (rowsOf laneBits (laneO 0 cs (2 ^ (μ - laneBits + R')))) := hV
  rw [rowsOf_laneO_zero, mem_iList_comp _ _ (bitsEquiv laneBits)] at hV'
  clear hV
  have hV := hV'
  simp only [Equiv.apply_symm_apply] at hV
  obtain ⟨q, hqc, hVq⟩ := exists_candidate_of_mem_iList hμ h64
    (LevelCode.two_pow_le_thr ⟨μ - laneBits, R', η, h64, hκ1, hR1, hη, hagr⟩) hV
  have hVe : V = fun u ↦ enc (μ - laneBits) R' (blockOf q (bitsEquiv laneBits u)) := by
    funext u
    have := congrFun hVq (bitsEquiv laneBits u)
    simpa [encStack] using this
  have hdec : decode ⟨μ - laneBits, R', η, h64, hκ1, hR1, hη, hagr⟩ V =
      fun u ↦ blockOf q (bitsEquiv laneBits u) := by
    rw [hVe]
    exact decode_enc ⟨μ - laneBits, R', η, h64, hκ1, hR1, hη, hagr⟩ _
  have hrun : runW w laneBits ⟨t, quad, [], []⟩ = fun r ↦ w (rotL laneBits r) := by
    funext r
    simp [runW]
  rw [hdec, hrun, claimSum_encStack hμ]
  exact hcand q hqc

end
end LeanVM.Protocol.Whir.Sound
