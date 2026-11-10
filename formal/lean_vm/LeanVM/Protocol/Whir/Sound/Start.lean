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
`crates/verifier/src/whir.rs:141-149` at leanVM `40f877dc`) is the
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
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd Finset Polynomial

@[expose] public section

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

/-! ## Tuples and codewords -/

/-- The level-0 tuple of a stack: lane `u` is the message polynomial of block `⟨u⟩`. -/
noncomputable def stackTuple {μ : ℕ} (q : Column μ) : (Fin laneBits → Bool) → E[X] :=
  fun u ↦ msgPoly (μ - laneBits) (blockOf q (bitsEquiv laneBits u))

/-- **The tuple of a close candidate.** A tuple of degree below `2^κ` agreeing with the level-0
word on at least `A ≥ 2^κ` columns is the tuple of a candidate. -/
theorem exists_candidate_of_tuple {μ R A : ℕ} (hμ : laneBits ≤ μ) (h : μ - laneBits + R ≤ 64)
    (hA : 2 ^ (μ - laneBits) ≤ A) (cs : List (ℕ × ℕ × Word))
    (U : (Fin laneBits → Bool) → E[X]) (hU : DegLE (2 ^ (μ - laneBits) - 1) U)
    (hag : A ≤ (agreeT (domain (μ - laneBits) R h) U
      (rowsOf laneBits (laneO 0 cs (2 ^ (μ - laneBits + R))))).card) :
    ∃ q ∈ Candidates μ R A (wordOf cs 0), ∀ u, lowMsg (μ - laneBits) (U u) =
      blockOf q (bitsEquiv laneBits u) := by
  have hκ : μ - laneBits ≤ 64 := by omega
  set V : Fin (2 ^ laneBits) → Fin (2 ^ (μ - laneBits + R)) → E :=
    fun u ↦ enc (μ - laneBits) R (lowMsg (μ - laneBits) (U ((bitsEquiv laneBits).symm u)))
  have hV : ∀ u v, V u v = (U ((bitsEquiv laneBits).symm u)).eval (domain (μ - laneBits) R h v) := by
    intro u v
    simp only [V]
    rw [enc_eq_evalOnPoints h, msgPoly_lowMsg_of_deg hκ (hU _)]
    rfl
  have hmem : V ∈ iList (ReedSolomon.code (domain (μ - laneBits) R h) (2 ^ (μ - laneBits))) A
      (laneWord μ R (wordOf cs 0)) := by
    rw [mem_iList]
    refine ⟨fun u ↦ by rw [← range_enc h]; exact LinearMap.mem_range_self _ _, _, hag, ?_⟩
    intro u v hv
    rw [mem_agreeT] at hv
    have := hv ((bitsEquiv laneBits).symm u)
    simp only [rowsOf_laneO_zero, Equiv.apply_symm_apply] at this
    rw [hV, this]
  obtain ⟨q, hq, hVq⟩ := exists_candidate_of_mem_iList hμ h hA hmem
  refine ⟨q, hq, fun u ↦ enc_injective h ?_⟩
  have := congrFun hVq (bitsEquiv laneBits u)
  simpa [V, encStack] using this

/-- The tuple of a candidate lies in the level-0 list. -/
theorem stackTuple_mem {μ R A : ℕ} (h : μ - laneBits + R ≤ 64)
    (cs : List (ℕ × ℕ × Word)) {q : Column μ} (hq : q ∈ Candidates μ R A (wordOf cs 0)) :
    stackTuple q ∈ tlist (domain (μ - laneBits) R h)
      (rowsOf laneBits (laneO 0 cs (2 ^ (μ - laneBits + R)))) A (2 ^ (μ - laneBits) - 1) := by
  have hκ : μ - laneBits ≤ 64 := by omega
  obtain ⟨S, hS, hagree⟩ := hq
  rw [mem_tlist]
  refine ⟨fun u ↦ ?_, hS.trans (card_le_card fun v hv ↦ ?_)⟩
  · have := natDegree_msgPoly_lt hκ (blockOf q (bitsEquiv laneBits u))
    have h1 := Nat.one_le_two_pow (n := μ - laneBits)
    by_cases h0 : stackTuple q u = 0
    · rw [h0, Polynomial.natDegree_zero]; exact Nat.zero_le _
    · have := (Polynomial.natDegree_lt_iff_degree_lt h0).mpr (by exact_mod_cast this)
      omega
  · rw [mem_agreeT]
    intro u
    rw [rowsOf_laneO_zero]
    have := hagree v hv (bitsEquiv laneBits u)
    simp only [laneWord]
    rw [this, enc_eq_evalOnPoints h]
    rfl

/-- **The candidates are finite**, as many as the level-0 list. -/
theorem candidates_ncard_le {μ R A : ℕ} (hμ : laneBits ≤ μ) (h : μ - laneBits + R ≤ 64)
    (cs : List (ℕ × ℕ × Word)) :
    (Candidates μ R A (wordOf cs 0)).Finite ∧ (Candidates μ R A (wordOf cs 0)).ncard ≤
      (tlist (domain (μ - laneBits) R h) (rowsOf laneBits (laneO 0 cs (2 ^ (μ - laneBits + R))))
        A (2 ^ (μ - laneBits) - 1)).card := by
  have hκ : μ - laneBits ≤ 64 := by omega
  have hinj : Set.InjOn stackTuple (Candidates μ R A (wordOf cs 0)) := by
    intro q _ q' _ hqq
    refine eq_of_blockOf_eq hμ fun u ↦ ?_
    have := congrFun hqq ((bitsEquiv laneBits).symm u)
    simp only [stackTuple, Equiv.apply_symm_apply] at this
    exact msgPoly_injective hκ this
  have hsub : stackTuple '' Candidates μ R A (wordOf cs 0) ⊆
      ↑(tlist (domain (μ - laneBits) R h) (rowsOf laneBits (laneO 0 cs (2 ^ (μ - laneBits + R))))
        A (2 ^ (μ - laneBits) - 1)) := by
    rintro _ ⟨q, hq, rfl⟩
    exact stackTuple_mem h cs hq
  have hfin : (Candidates μ R A (wordOf cs 0)).Finite :=
    Set.Finite.of_finite_image ((Finset.finite_toSet _).subset hsub) hinj
  refine ⟨hfin, ?_⟩
  rw [← hinj.ncard_image, ← Set.ncard_coe_finset]
  exact Set.ncard_le_ncard hsub (Finset.finite_toSet _)

/-! ## The starting doom -/

/-- **The starting doom**: from the candidates' violation, `LevelPre` of level `0` for the initial
state. -/
theorem levelPre_zero {μ R : ℕ} (P₀ : LevelCode) (hκ : P₀.κ = μ - laneBits) (hR : P₀.R = R)
    (hℓ : P₀.ℓ = laneBits) (hμ : laneBits ≤ μ) (hthr : 2 ^ P₀.κ ≤ P₀.thr 0) (w : List E → E)
    (t : E) (cs : List (ℕ × ℕ × Word)) (hS : ShapeOK 0 P₀ cs) (hlen : cs.length = 1)
    (hcand : ∀ q ∈ Candidates μ R (P₀.thr 0) (wordOf cs 0), ¬ StackClaim.Holds μ (w, t) q) :
    LevelPre μ laneBits w 0 P₀ 0 ⟨t, [], []⟩ cs := by
  refine ⟨⟨rfl, Nat.zero_le _, by omega, fun _ hc ↦ by simp at hc, ?_⟩, hS, hlen⟩
  obtain ⟨κ, R', ℓ, A, h64, hR1⟩ := P₀
  dsimp only at hκ hR hℓ hthr hcand ⊢
  subst hκ hR hℓ
  simp only [List.length_nil, Nat.sub_zero, foldsA_nil]
  intro U hU hag heq
  obtain ⟨q, hq, hUq⟩ := exists_candidate_of_tuple hμ h64 hthr cs U hU hag
  apply hcand q hq
  have hrun : runW w laneBits ⟨t, [], []⟩ = fun r ↦ w (rotL laneBits r) := by
    funext r
    rw [runW_eq]
    simp
  have hU' : (fun u ↦ lowMsg (μ - laneBits) (U u)) = fun u ↦ blockOf q (bitsEquiv laneBits u) :=
    funext hUq
  rw [tclaim, hrun, hU'] at heq
  rw [StackClaim.Holds, ← claimSum_encStack hμ w q]
  exact heq

end
end LeanVM.Protocol.Whir.Sound
