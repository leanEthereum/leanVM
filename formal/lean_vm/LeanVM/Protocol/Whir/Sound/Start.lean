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
`crates/verifier/src/whir.rs` at leanVM `40f877dc`) is the
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
* `exists_candidate_of_tuple`: a member of level 0's list, at its degree `2^κ − 1 + 6` and a
  threshold above it, is over `K`, and its low parts are the blocks of a candidate (its high
  parts `P div W_κ` the candidate's `H`); `candidates_ncard_le`: conversely each candidate has a
  list member with its blocks as low parts, so there are at most as many candidates as members.
* `levelPre_zero`: **the starting doom** `LevelPre` of level `0` from the candidates' violation:
  the claims weigh only the low parts.
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

/-! ## Tuples and candidates -/

/-- `W_κ` over `K` is monic. -/
theorem vanishing_monic (κ : ℕ) : (vanishing κ).Monic :=
  monic_prod_of_monic _ _ fun _ _ ↦ monic_X_add_C _

/-- A polynomial over `K`, lifted, evaluates at a point of `K` to the lift of its value. -/
theorem eval_map_ofK (p : K[X]) (x : K) :
    (p.map (algebraMap K E)).eval (ofK x) = ofK (p.eval x) := by
  rw [eval_map, show ofK x = algebraMap K E x from rfl, eval₂_hom]
  rfl

/-- The level-0 lanes as polynomials over `E` at a column: the committed word's value. -/
theorem eval_of_mem_agreeT {μ R : ℕ} (h : μ - laneBits + R ≤ 64) (cs : List (ℕ × ℕ × Word))
    {U : (Fin laneBits → Bool) → E[X]} {v : Fin (2 ^ (μ - laneBits + R))}
    (hv : v ∈ agreeT (domain (μ - laneBits) R h) U
      (rowsOf laneBits (laneO 0 cs (2 ^ (μ - laneBits + R))))) (u : Fin laneBits → Bool) :
    (U u).eval (ofK (K.ofBits v)) = laneOf (wordOf cs 0) (bitsEquiv laneBits u) v := by
  rw [mem_agreeT] at hv
  have := hv u
  rw [rowsOf_laneO_zero] at this
  exact this

/-- **The candidate of a close tuple.** A tuple of degree at most `2^κ − 1 + 6` agreeing with the
level-0 word on at least `A` columns, `A` above the degree, has the blocks of a candidate as its
low parts: it is over `K`, its low part `P mod W_κ` a `K`-message and its high part `P div W_κ`
of degree below `6`. -/
theorem exists_candidate_of_tuple {μ R A : ℕ} (hμ : laneBits ≤ μ) (h : μ - laneBits + R ≤ 64)
    (hA : 2 ^ (μ - laneBits) - 1 + laneBits < A) (cs : List (ℕ × ℕ × Word))
    (U : (Fin laneBits → Bool) → E[X]) (hU : DegLE (2 ^ (μ - laneBits) - 1 + laneBits) U)
    (hag : A ≤ (agreeT (domain (μ - laneBits) R h) U
      (rowsOf laneBits (laneO 0 cs (2 ^ (μ - laneBits + R))))).card) :
    ∃ q ∈ Candidates μ R A (wordOf cs 0), ∀ u, lowMsg (μ - laneBits) (U u) =
      blockOf q (bitsEquiv laneBits u) := by
  classical
  set κ := μ - laneBits with hκdef
  have hκ : κ ≤ 64 := by omega
  have hφ : ∀ a : K, algebraMap K E a = ofK a := fun _ ↦ rfl
  set S := agreeT (domain κ R h) U (rowsOf laneBits (laneO 0 cs (2 ^ (κ + R))))
  -- Each lane is over `K`.
  have hK : ∀ u, ∃ P₀ : K[X], U u = P₀.map (algebraMap K E) := fun u ↦ by
    refine exists_map_of_isInK (hU u) (S.image fun v : Fin (2 ^ (κ + R)) ↦ K.ofBits v) ?_ fun x hx ↦ ?_
    · rw [Finset.card_image_of_injOn fun a _ b _ hab ↦
        (domain κ R h).injective (congrArg ofK hab)]
      omega
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
      rw [eval_of_mem_agreeT h cs hv u, laneOf, isInK_iff]
      exact ⟨_, rfl⟩
  choose P₀ hP₀ using hK
  have hdeg₀ : ∀ u, (P₀ u).natDegree ≤ 2 ^ κ - 1 + laneBits := fun u ↦ by
    have := hU u
    rwa [hP₀, natDegree_map_eq_of_injective (algebraMap K E).injective] at this
  -- The low parts are `K`-messages.
  have hlow : ∀ u, msgPoly κ (lowMsg κ (U u)) = (P₀ u %ₘ vanishing κ).map (algebraMap K E) := by
    intro u
    rw [msgPoly_lowMsg hκ, hP₀, Polynomial.map_modByMonic _ (vanishing_monic κ)]
    rfl
  have hinK : ∀ u x, IsInK (lowMsg κ (U u) x) := fun u ↦
    isInK_of_agree h (lowMsg κ (U u)) Finset.univ
      (by rw [Finset.card_univ, Fintype.card_fin]; exact Nat.pow_le_pow_right two_pos (by omega))
      fun v _ ↦ by
        rw [enc_eq_evalOnPoints h, ReedSolomon.evalOnPoints, LinearMap.coe_mk, AddHom.coe_mk, hlow,
          isInK_iff]
        refine ⟨(P₀ u %ₘ vanishing κ).eval (K.ofBits v), ?_⟩
        simp only [domain, Function.Embedding.coeFn_mk]
        exact eval_map_ofK _ _
  let a : Fin (2 ^ laneBits) → (Fin κ → Bool) → K :=
    fun u x ↦ (lowMsg κ (U ((bitsEquiv laneBits).symm u)) x).limb 0
  have hga : ∀ u, lowMsg κ (U u) = fun x ↦ ofK (a (bitsEquiv laneBits u) x) := fun u ↦
    funext fun x ↦ by
      obtain ⟨c, hc⟩ := (isInK_iff _).mp (hinK u x)
      simp [a, hc]
  have hblock : ∀ u, blockOf (stackOf hμ a) (bitsEquiv laneBits u) = lowMsg κ (U u) := fun u ↦ by
    rw [blockOf_stackOf, hga]
  refine ⟨stackOf hμ a, ⟨S, hag, fun u ↦ P₀ ((bitsEquiv laneBits).symm u) /ₘ vanishing κ,
    fun u ↦ ?_, fun v hv u ↦ ?_⟩, fun u ↦ (hblock u).symm⟩
  · -- The high part has degree below `6`.
    refine (degree_le_natDegree).trans_lt ?_
    rw [natDegree_divByMonic _ (vanishing_monic κ), natDegree_vanishing]
    have := hdeg₀ ((bitsEquiv laneBits).symm u)
    have h1 := Nat.one_le_two_pow (n := κ)
    have h6 : laneBits = 6 := rfl
    exact_mod_cast (show (P₀ ((bitsEquiv laneBits).symm u)).natDegree - 2 ^ κ < laneBits by omega)
  · set u' := (bitsEquiv laneBits).symm u with hu'
    have hv' := eval_of_mem_agreeT h cs hv u'
    rw [Equiv.apply_symm_apply] at hv'
    have hb : blockOf (stackOf hμ a) u = lowMsg κ (U u') := by
      rw [← hblock u', Equiv.apply_symm_apply]
    rw [laneValue, hb, ← hv', enc_eq_evalOnPoints h]
    simp only [ReedSolomon.evalOnPoints, LinearMap.coe_mk, AddHom.coe_mk, domain,
      Function.Embedding.coeFn_mk]
    rw [hlow, hP₀ u', eval_map_ofK, eval_map_ofK, ← eval_vanishing, ← eval_mul, ← ofK_add,
      ← eval_add]
    exact (congrArg (fun p ↦ ofK (eval (K.ofBits (v : ℕ)) p))
      (modByMonic_add_div (P₀ u') (vanishing κ))).symm

/-- The level-0 tuple of a stack with high parts `H`: lane `u` is the message polynomial of
block `⟨u⟩` plus `W_κ·H_⟨u⟩`. -/
noncomputable def stackTuple {μ : ℕ} (q : Column μ) (H : Fin (2 ^ laneBits) → K[X]) :
    (Fin laneBits → Bool) → E[X] :=
  fun u ↦ msgPoly (μ - laneBits) (blockOf q (bitsEquiv laneBits u)) +
    vanE (μ - laneBits) * (H (bitsEquiv laneBits u)).map (algebraMap K E)

/-- The low parts of a stack's tuple are its blocks. -/
theorem lowMsg_stackTuple {μ : ℕ} (hκ : μ - laneBits ≤ 64) (q : Column μ)
    (H : Fin (2 ^ laneBits) → K[X]) (u : Fin laneBits → Bool) :
    lowMsg (μ - laneBits) (stackTuple q H u) = blockOf q (bitsEquiv laneBits u) :=
  lowMsg_msgPoly_add hκ _ _

/-- The tuple of a candidate lies in the level-0 list at degree `2^κ − 1 + 6`. -/
theorem stackTuple_mem {μ R A : ℕ} (h : μ - laneBits + R ≤ 64)
    (cs : List (ℕ × ℕ × Word)) {q : Column μ} {S : Finset (Fin (2 ^ (μ - laneBits + R)))}
    (hS : A ≤ S.card) {H : Fin (2 ^ laneBits) → K[X]} (hH : ∀ u, (H u).degree < laneBits)
    (hagree : ∀ v ∈ S, ∀ u, laneOf (wordOf cs 0) u v = laneValue μ R q (H u) u v) :
    stackTuple q H ∈ tlist (domain (μ - laneBits) R h)
      (rowsOf laneBits (laneO 0 cs (2 ^ (μ - laneBits + R)))) A
        (2 ^ (μ - laneBits) - 1 + laneBits) := by
  have hκ : μ - laneBits ≤ 64 := by omega
  have hφ : ∀ a : K, algebraMap K E a = ofK a := fun _ ↦ rfl
  rw [mem_tlist]
  refine ⟨fun u ↦ ?_, hS.trans (card_le_card fun v hv ↦ ?_)⟩
  · have h1 := Nat.one_le_two_pow (n := μ - laneBits)
    refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · have := natDegree_msgPoly_lt hκ (blockOf q (bitsEquiv laneBits u))
      by_cases h0 : msgPoly (μ - laneBits) (blockOf q (bitsEquiv laneBits u)) = 0
      · rw [h0, natDegree_zero]; exact Nat.zero_le _
      · have := (natDegree_lt_iff_degree_lt h0).mpr (by exact_mod_cast this)
        omega
    · refine natDegree_mul_le.trans ?_
      rw [natDegree_vanE, natDegree_map_eq_of_injective (algebraMap K E).injective]
      have hd := hH (bitsEquiv laneBits u)
      have : (H (bitsEquiv laneBits u)).natDegree < laneBits := by
        by_cases h0 : H (bitsEquiv laneBits u) = 0
        · rw [h0, natDegree_zero]; decide
        · exact (natDegree_lt_iff_degree_lt h0).mpr hd
      omega
  · rw [mem_agreeT]
    intro u
    rw [rowsOf_laneO_zero]
    show _ = laneOf (wordOf cs 0) (bitsEquiv laneBits u) v
    rw [hagree v hv, laneValue, stackTuple, eval_add, eval_mul, enc_eq_evalOnPoints h]
    simp only [ReedSolomon.evalOnPoints, LinearMap.coe_mk, AddHom.coe_mk, domain,
      Function.Embedding.coeFn_mk, vanE]
    rw [eval_map_ofK, eval_map_ofK, eval_vanishing, ofK_mul]

/-- **The candidates are finite**, at most as many as the level-0 list at degree
`2^κ − 1 + 6`. -/
theorem candidates_ncard_le {μ R A : ℕ} (hμ : laneBits ≤ μ) (h : μ - laneBits + R ≤ 64)
    (cs : List (ℕ × ℕ × Word)) :
    (Candidates μ R A (wordOf cs 0)).Finite ∧ (Candidates μ R A (wordOf cs 0)).ncard ≤
      (tlist (domain (μ - laneBits) R h) (rowsOf laneBits (laneO 0 cs (2 ^ (μ - laneBits + R))))
        A (2 ^ (μ - laneBits) - 1 + laneBits)).card := by
  classical
  have hκ : μ - laneBits ≤ 64 := by omega
  set L := tlist (domain (μ - laneBits) R h) (rowsOf laneBits (laneO 0 cs (2 ^ (μ - laneBits + R))))
    A (2 ^ (μ - laneBits) - 1 + laneBits)
  let f : Column μ → (Fin laneBits → Bool) → E[X] := fun q ↦
    if hq : q ∈ Candidates μ R A (wordOf cs 0) then stackTuple q hq.choose_spec.2.choose else 0
  have hf : ∀ q ∈ Candidates μ R A (wordOf cs 0), f q ∈ L ∧
      ∀ u, lowMsg (μ - laneBits) (f q u) = blockOf q (bitsEquiv laneBits u) := by
    intro q hq
    simp only [f, hq, dite_true]
    obtain ⟨hS, hHq⟩ := hq.choose_spec
    exact ⟨stackTuple_mem h cs hS hHq.choose_spec.1 hHq.choose_spec.2,
      lowMsg_stackTuple hκ q _⟩
  have hinj : Set.InjOn f (Candidates μ R A (wordOf cs 0)) := by
    intro q hq q' hq' hqq
    refine eq_of_blockOf_eq hμ fun u ↦ ?_
    have := congrArg (fun U ↦ lowMsg (μ - laneBits) (U ((bitsEquiv laneBits).symm u))) hqq
    simp only [(hf q hq).2, (hf q' hq').2, Equiv.apply_symm_apply] at this
    exact this
  have hsub : f '' Candidates μ R A (wordOf cs 0) ⊆ ↑L := by
    rintro _ ⟨q, hq, rfl⟩
    exact (hf q hq).1
  have hfin : (Candidates μ R A (wordOf cs 0)).Finite :=
    Set.Finite.of_finite_image ((Finset.finite_toSet _).subset hsub) hinj
  refine ⟨hfin, ?_⟩
  rw [← hinj.ncard_image, ← Set.ncard_coe_finset]
  exact Set.ncard_le_ncard hsub (Finset.finite_toSet _)

/-! ## The starting doom -/

/-- **The starting doom**: from the candidates' violation, `LevelPre` of level `0` for the initial
state. -/
theorem levelPre_zero {μ R : ℕ} (P₀ : LevelCode) (hκ : P₀.κ = μ - laneBits) (hR : P₀.R = R)
    (hℓ : P₀.ℓ = laneBits) (hμ : laneBits ≤ μ) (hthr : P₀.deg < P₀.thr 0) (w : List E → E)
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
