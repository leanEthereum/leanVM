/-
  LeanVM.Protocol.Whir.Params.Deployed

  The deployed WHIR opening's codes and the round-by-round bounds of every group at `2^-125`,
  read off the kernel-checked parameter check, and the stacked opening's specification at every
  admissible shape.
-/

module

public import LeanVM.Protocol.Whir.Sound.Spec
public import LeanVM.Protocol.Whir.Sound.FoldRoundCywz
public import LeanVM.Protocol.Whir.Params.Check
public import LeanVM.Protocol.Compile.SpecRules.Grind

/-!
# The deployed WHIR parameters

Level `i` of a shape's fold certificate `(κ, R, k, Aend, rounds)` is the code `mkCode`
(`codesOf μ R i`). From `shapeOK μ R = true` (`shapeOK_all`, every admissible shape):

* `roundBoundsOf`: each level's fold rounds, from their certificate (`foldRoundBound_of_ok`),
  at the level's degree, with `(α, β)`'s count at most `2^11 |E|` (the fold budget `2^11`
  times `|E|`), `2^-125` after the `8`-bit grind;
* `ladderOK_of_chain`: the ladder's groups (`MidOK`, `FinalOK`) within `εmsg = 2^-125` after
  their grinds;
* `listMax₀ μ R`, level 0's list bound, at most `166` (`listMax₀_le`), with the out-of-domain and
  batching rows `ood_row`, `lambda_row`, and the candidates' count `card_candidates_le`;
* **`deployedStackedSpec`**: `verifyStackedOpening μ R claims` from `StackedPre` at level 0's
  threshold `thr0Of μ R`, with lead `eBatch J (listMax₀ μ R)`.
-/

namespace LeanVM.Protocol.Whir.Params

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Protocol.Whir
  LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd

@[expose] public section

/-! ## The error arithmetic -/

/-- `N · 2^-b ≤ 2^-k` from `N · 2^k ≤ 2^b`. -/
theorem natMul_inv_pow_le {N b k : ℕ} (h : N * 2 ^ k ≤ 2 ^ b) :
    (N : ENNReal) * 2⁻¹ ^ b ≤ 2⁻¹ ^ k := by
  rcases le_or_gt k b with hkb | hkb
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hkb
    have h' : 2 ^ k * N ≤ 2 ^ k * 2 ^ m := by rw [← pow_add]; linarith
    have hN : N ≤ 2 ^ m := Nat.le_of_mul_le_mul_left h' (by positivity)
    have h1 : (N : ENNReal) * 2⁻¹ ^ m ≤ 1 :=
      calc (N : ENNReal) * 2⁻¹ ^ m ≤ 2 ^ m * 2⁻¹ ^ m := by gcongr; exact_mod_cast hN
        _ = 1 := by rw [← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow]
    calc (N : ENNReal) * 2⁻¹ ^ (k + m) = 2⁻¹ ^ k * ((N : ENNReal) * 2⁻¹ ^ m) := by ring
      _ ≤ 2⁻¹ ^ k * 1 := by gcongr
      _ = _ := mul_one _
  · have hN : N = 0 := by
      by_contra h0
      have h1 := Nat.pow_lt_pow_right (by norm_num : 1 < 2) hkb
      have h2 : 2 ^ k ≤ N * 2 ^ k := Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero h0)
      omega
    simp [hN]

theorem div_card (N : ℕ) : (N : ENNReal) / Fintype.card E = N * 2⁻¹ ^ 128 := by
  rw [card_E, Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv, ENNReal.inv_pow]

/-- The fold group's count `2^11 |E|` over `|E|²` is `2^11/|E|`. -/
theorem budget_div_card_sq :
    (((AffineCombiner.foldBudget * Fintype.card E : ℕ) : ENNReal) / Fintype.card E ^ 2) =
      ((2 ^ 11 : ℕ) : ENNReal) / Fintype.card E := by
  have hq0 : ((Fintype.card E : ℕ) : ENNReal) ≠ 0 := by simp [Fintype.card_ne_zero]
  have hqt : ((Fintype.card E : ℕ) : ENNReal) ≠ ⊤ := by simp
  rw [show (Fintype.card E : ENNReal) ^ 2 = (Fintype.card E : ENNReal) * (Fintype.card E) by
    ring, Nat.cast_mul, ENNReal.mul_div_mul_right _ _ hq0 hqt]

/-- A group of error `N/|E|` ground by `g` bits is within `2^-125` when `N · 2^125 ≤ 2^(g+128)`. -/
theorem grind_div_card_le {g N : ℕ} (h : N * 2 ^ 125 ≤ 2 ^ (g + 128)) :
    (2 : ENNReal)⁻¹ ^ g * ((N : ENNReal) / Fintype.card E) ≤ εmsg := by
  rw [div_card, εmsg, securityBits]
  calc (2 : ENNReal)⁻¹ ^ g * ((N : ENNReal) * 2⁻¹ ^ 128) = N * 2⁻¹ ^ (g + 128) := by
        rw [pow_add]; ring
    _ ≤ _ := natMul_inv_pow_le h

theorem eTail_le : eTail ≤ εmsg := by
  have h := natMul_inv_pow_le (N := 2) (b := 128) (k := 125) (by norm_num)
  rw [eTail, show (2 : ENNReal) = ((2 : ℕ) : ENNReal) by norm_num, div_card, εmsg, securityBits]
  exact h

theorem eQuery_eq (P : LevelCode) (t : ℕ) :
    eQuery P t = (((P.A - 1) ^ t : ℕ) : ENNReal) * 2⁻¹ ^ ((P.κ + P.R) * t) := by
  rw [eQuery, Nat.cast_pow (P.A - 1), pow_mul, ← mul_pow, ← ENNReal.inv_pow, ← div_eq_mul_inv]
  norm_cast

/-- The query group within `2^-125` after its `17`-bit grind. -/
theorem eQ_le {P : LevelCode} {t : ℕ} (h : (P.A - 1) ^ t * 2 ^ 108 ≤ (2 ^ (P.κ + P.R)) ^ t) :
    (2 : ENNReal)⁻¹ ^ Whir.queryGrindingBits * eQuery P t ≤ εmsg := by
  rw [eQuery_eq, εmsg, securityBits, Whir.queryGrindingBits]
  calc (2 : ENNReal)⁻¹ ^ 17 * ((((P.A - 1) ^ t : ℕ) : ENNReal) * 2⁻¹ ^ ((P.κ + P.R) * t)) =
      (((P.A - 1) ^ t : ℕ) : ENNReal) * 2⁻¹ ^ (17 + (P.κ + P.R) * t) := by rw [pow_add]; ring
    _ ≤ _ := natMul_inv_pow_le (by
      rw [pow_add, pow_mul]
      calc (P.A - 1) ^ t * 2 ^ 125 = (P.A - 1) ^ t * 2 ^ 108 * 2 ^ 17 := by ring
        _ ≤ (2 ^ (P.κ + P.R)) ^ t * 2 ^ 17 := Nat.mul_le_mul_right _ h
        _ = _ := by ring)

theorem eQuery_lt_one {P : LevelCode} {t : ℕ}
    (h : (P.A - 1) ^ t * 2 ^ 108 ≤ (2 ^ (P.κ + P.R)) ^ t) : eQuery P t < 1 := by
  rw [eQuery_eq]
  refine lt_of_le_of_lt (natMul_inv_pow_le (k := 1) ?_) (by rw [pow_one, ENNReal.inv_lt_one]; norm_num)
  rw [pow_mul]
  calc (P.A - 1) ^ t * 2 ^ 1 ≤ (P.A - 1) ^ t * 2 ^ 108 := Nat.mul_le_mul_left _ (by norm_num)
    _ ≤ _ := h

/-- The out-of-domain point's escape is `C(L', 2) κ / |E|`. -/
theorem eOod_eq {P P' : LevelCode} (hκ : 1 ≤ P.κ) :
    eOod P P' = ((P'.listMax.choose 2 * P.κ : ℕ) : ENNReal) / Fintype.card E := by
  obtain ⟨m, hm⟩ : ∃ m, P.κ = m + 1 := ⟨P.κ - 1, by omega⟩
  have hq1 : (Fintype.card E : ENNReal)⁻¹ * Fintype.card E = 1 :=
    ENNReal.inv_mul_cancel (by simp [Fintype.card_ne_zero]) (by simp)
  rw [eOod, hm, Nat.add_sub_cancel, ENNReal.div_eq_inv_mul, Nat.cast_mul, Nat.cast_mul,
    Nat.cast_mul, Nat.cast_pow]
  generalize (Fintype.card E : ENNReal) = q at hq1 ⊢
  generalize ((P'.listMax.choose 2 : ℕ) : ENNReal) = C
  generalize ((m + 1 : ℕ) : ENNReal) = k
  calc q⁻¹ ^ (m + 1) * (C * (k * q ^ m)) = q⁻¹ * (C * k) * (q⁻¹ * q) ^ m := by ring
    _ = q⁻¹ * (C * k) := by rw [hq1, one_pow, mul_one]

/-- The next level's out-of-domain point within `2^-125` after its `17`-bit grind, from
`C(L', 2) κ ≤ 2^20`. -/
theorem eOod_le {P P' : LevelCode} (h : P'.listMax.choose 2 * P.κ ≤ 2 ^ 20) (hκ : 1 ≤ P.κ) :
    (2 : ENNReal)⁻¹ ^ Whir.levelOodGrindingBits * eOod P P' ≤ εmsg := by
  rw [eOod_eq hκ, Whir.levelOodGrindingBits]
  exact grind_div_card_le (by
    calc P'.listMax.choose 2 * P.κ * 2 ^ 125 ≤ 2 ^ 20 * 2 ^ 125 := Nat.mul_le_mul_right _ h
      _ = 2 ^ (17 + 128) := by norm_num)

theorem eOod_lt_one {P P' : LevelCode} (h : P'.listMax.choose 2 * P.κ ≤ 2 ^ 20) (hκ : 1 ≤ P.κ) :
    eOod P P' < 1 := by
  rw [eOod_eq hκ, div_card]
  refine lt_of_le_of_lt (natMul_inv_pow_le (k := 1) ?_) (by rw [pow_one, ENNReal.inv_lt_one]; norm_num)
  calc P'.listMax.choose 2 * P.κ * 2 ^ 1 ≤ 2 ^ 20 * 2 ^ 1 := Nat.mul_le_mul_right _ h
    _ ≤ 2 ^ 128 := by norm_num

/-- A non-final level's query message, its positions and the next level's batching `λ`, within
`2^-125` after its `17`-bit grind, from `(A − 1)^t 2^128 + (t + 1) L' n^t ≤ n^t 2^20`. -/
theorem eQL_le {P P' : LevelCode} {t : ℕ}
    (h : (P.A - 1) ^ t * 2 ^ 128 + (t + 1) * P'.listMax * (2 ^ (P.κ + P.R)) ^ t ≤
      (2 ^ (P.κ + P.R)) ^ t * 2 ^ 20) :
    (2 : ENNReal)⁻¹ ^ Whir.queryGrindingBits * (eQuery P t + eLam P' t) ≤ εmsg := by
  rw [eQuery_eq, eLam, div_card]
  rw [← pow_mul] at h
  generalize ha : (P.A - 1) ^ t = a at h ⊢
  generalize hb : (t + 1) * P'.listMax = b at h ⊢
  generalize hK : (P.κ + P.R) * t = K at h ⊢
  have hinv (m : ℕ) : (2 : ENNReal) ^ m * 2⁻¹ ^ m = 1 := by
    rw [← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow]
  have hsum : (a : ENNReal) * 2⁻¹ ^ K + (b : ENNReal) * 2⁻¹ ^ 128 =
      ((a * 2 ^ 128 + b * 2 ^ K : ℕ) : ENNReal) * 2⁻¹ ^ (K + 128) := by
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat]
    calc (a : ENNReal) * 2⁻¹ ^ K + (b : ENNReal) * 2⁻¹ ^ 128 =
        (a : ENNReal) * 2⁻¹ ^ K * (2 ^ 128 * 2⁻¹ ^ 128) + (b : ENNReal) * 2⁻¹ ^ 128 *
          (2 ^ K * 2⁻¹ ^ K) := by rw [hinv, hinv, mul_one, mul_one]
      _ = _ := by ring
  rw [hsum, εmsg, securityBits, Whir.queryGrindingBits]
  calc (2 : ENNReal)⁻¹ ^ 17 * (((a * 2 ^ 128 + b * 2 ^ K : ℕ) : ENNReal) * 2⁻¹ ^ (K + 128)) =
      ((a * 2 ^ 128 + b * 2 ^ K : ℕ) : ENNReal) * 2⁻¹ ^ (17 + (K + 128)) := by
        rw [pow_add (2⁻¹ : ENNReal) 17]; ring
    _ ≤ _ := natMul_inv_pow_le (by
      calc (a * 2 ^ 128 + b * 2 ^ K) * 2 ^ 125 ≤ 2 ^ K * 2 ^ 20 * 2 ^ 125 :=
            Nat.mul_le_mul_right _ h
        _ = 2 ^ (17 + (K + 128)) := by rw [← pow_add, ← pow_add]; congr 1; omega)

/-! ## The codes -/

/-- The fallback level, never read at an admissible shape. -/
def junkLv : Lv := (0, 1, 0, 1, [])

/-- A level's code. -/
def mkCode (lv : Lv) : LevelCode :=
  if h : lv.1 + lv.2.1 ≤ 64 ∧ 1 ≤ lv.2.1 then ⟨lv.1, lv.2.1, lv.2.2.1, lv.2.2.2.1, h.1, h.2⟩
  else ⟨0, 1, 0, 1, by omega, le_rfl⟩

theorem mkCode_eq {lv : Lv} (h : lv.1 + lv.2.1 ≤ 64 ∧ 1 ≤ lv.2.1) :
    mkCode lv = ⟨lv.1, lv.2.1, lv.2.2.1, lv.2.2.2.1, h.1, h.2⟩ := by
  rw [mkCode]
  split_ifs
  rfl

/-- The codes of a shape's levels. -/
def codesOf (μ R : ℕ) (i : ℕ) : LevelCode := mkCode ((levelsOf μ R).getD i junkLv)

/-- Level 0's list bound. -/
def listMax₀ (μ R : ℕ) : ℕ := jlStart ((levelsOf μ R).headD junkLv)

/-! ## The fold rounds -/

/-- The fold rounds of a certified level. -/
noncomputable def roundBoundsMk {κ R k A : ℕ} (h64 : κ + R ≤ 64) (hR : 1 ≤ R) {rs : List (ℕ × ℕ × ℕ)}
    (hlv : AffineCombiner.levelOK AffineCombiner.foldBudget (κ, R, k, A, rs) = true)
    (hkA : k < A) : RoundBounds ⟨κ, R, k, A, h64, hR⟩ εmsg where
  N _ := AffineCombiner.foldBudget * Fintype.card E
  hA := hkA
  bound j hj := by
    have hlen : rs.length = k := by
      have h := hlv
      simp only [AffineCombiner.levelOK, Bool.and_eq_true, beq_iff_eq] at h
      exact h.1
    have hj' : j < k := hj
    exact Sound.foldRoundBound_of_ok h64 (AffineCombiner.levelOK_round hlv j (by omega)).2
  eF j _ := by
    rw [budget_div_card_sq]
    exact grind_div_card_le (by unfold Whir.foldGrindingBits; norm_num)
  eF1 j _ := by
    rw [budget_div_card_sq, div_card]
    exact lt_of_le_of_lt (natMul_inv_pow_le (k := 1) (by norm_num))
      (by rw [pow_one, ENNReal.inv_lt_one]; norm_num)

/-- The fallback code's rounds: none. -/
noncomputable def roundBoundsJunk : RoundBounds ⟨0, 1, 0, 1, by omega, le_rfl⟩ εmsg where
  N _ := 0
  hA := by norm_num
  bound j hj := absurd hj (Nat.not_lt_zero _)
  eF j hj := absurd hj (Nat.not_lt_zero _)
  eF1 j hj := absurd hj (Nat.not_lt_zero _)

/-- The fold rounds of a level whose certificate checks. -/
noncomputable def roundBoundsOf : (lv : Lv) → AffineCombiner.levelOK AffineCombiner.foldBudget lv = true →
    lv.2.2.1 < lv.2.2.2.1 → RoundBounds (mkCode lv) εmsg
  | (κ, R, k, A, rs), hlv, hkA =>
    if h : κ + R ≤ 64 ∧ 1 ≤ R then by
      rw [show mkCode (κ, R, k, A, rs) = ⟨κ, R, k, A, h.1, h.2⟩ from mkCode_eq h]
      exact roundBoundsMk h.1 h.2 hlv hkA
    else by
      rw [show mkCode (κ, R, k, A, rs) = ⟨0, 1, 0, 1, by omega, le_rfl⟩ by
        rw [mkCode]
        split_ifs with h'
        · exact absurd h' h
        · rfl]
      exact roundBoundsJunk

/-! ## The levels -/

/-- What `levelChecks` checks of a level. -/
structure LevelFacts (κprev : ℕ) (lv : Lv) (cfg : Whir.Level) : Prop where
  hκ : lv.1 + lv.2.2.1 = κprev
  hfold : cfg.fold = lv.2.2.1
  hrate : cfg.logInvRate = lv.2.1
  h64 : lv.1 + lv.2.1 ≤ 64
  hR : 1 ≤ lv.2.1
  hk1 : 1 ≤ lv.2.2.1
  hk2 : lv.2.2.1 ≤ 2 ^ lv.1
  hkA : lv.2.2.1 < lv.2.2.2.1
  hlv : AffineCombiner.levelOK AffineCombiner.foldBudget lv = true
  hq : (lv.2.2.2.1 - 1) ^ cfg.queries * 2 ^ 108 ≤ (2 ^ (lv.1 + lv.2.1)) ^ cfg.queries
  hgap : 2 ^ (lv.1 + lv.2.1) * (2 ^ lv.1 - 1 + lv.2.2.1) <
    (lv.2.2.2.1 - lv.2.2.1) * (lv.2.2.2.1 - lv.2.2.1)

theorem levelFacts_of {κprev : ℕ} {lv : Lv} {cfg : Whir.Level}
    (h : levelChecks κprev lv cfg = true) : LevelFacts κprev lv cfg := by
  simp only [levelChecks, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

theorem finalOK_of {κprev : ℕ} {lv : Lv} {cfg : Whir.Level} (F : LevelFacts κprev lv cfg) :
    FinalOK (mkCode lv) cfg.queries εmsg := by
  rw [mkCode_eq ⟨F.h64, F.hR⟩]
  exact { hℓκ := F.hk2, hA := Nat.one_le_of_lt F.hkA, eQ := eQ_le F.hq,
          eQ1 := eQuery_lt_one F.hq, eT := eTail_le }

/-- A level's list bound is `jlStart`. -/
theorem listMax_mkCode {lv : Lv} (h : lv.1 + lv.2.1 ≤ 64 ∧ 1 ≤ lv.2.1) :
    (mkCode lv).listMax = jlStart lv := by
  rw [mkCode_eq h]
  rfl

theorem midOK_of {κprev : ℕ} {lv lv' : Lv} {c c' : Whir.Level} (F : LevelFacts κprev lv c)
    (F' : LevelFacts lv.1 lv' c')
    (hl : (lv.2.2.2.1 - 1) ^ c.queries * 2 ^ 128 +
        (c.queries + 1) * jlStart lv' * (2 ^ (lv.1 + lv.2.1)) ^ c.queries ≤
      (2 ^ (lv.1 + lv.2.1)) ^ c.queries * 2 ^ 20)
    (ho : (jlStart lv').choose 2 * lv.1 ≤ 2 ^ 20) (h1 : 1 ≤ lv.1) :
    MidOK (mkCode lv) (mkCode lv') c.queries εmsg := by
  have hL := listMax_mkCode ⟨F'.h64, F'.hR⟩
  have eO : (2 : ENNReal)⁻¹ ^ Whir.levelOodGrindingBits * eOod (mkCode lv) (mkCode lv') ≤ εmsg :=
    eOod_le (by rw [hL, mkCode_eq ⟨F.h64, F.hR⟩]; exact ho)
      (by rw [mkCode_eq ⟨F.h64, F.hR⟩]; exact h1)
  have eQL : (2 : ENNReal)⁻¹ ^ Whir.queryGrindingBits *
      (eQuery (mkCode lv) c.queries + eLam (mkCode lv') c.queries) ≤ εmsg :=
    eQL_le (by rw [hL, mkCode_eq ⟨F.h64, F.hR⟩]; exact hl)
  have eO1 : eOod (mkCode lv) (mkCode lv') < 1 :=
    eOod_lt_one (by rw [hL, mkCode_eq ⟨F.h64, F.hR⟩]; exact ho)
      (by rw [mkCode_eq ⟨F.h64, F.hR⟩]; exact h1)
  rw [mkCode_eq ⟨F.h64, F.hR⟩, mkCode_eq ⟨F'.h64, F'.hR⟩] at *
  refine { hκ := ?_, hℓ := F.hk1, hℓκ := F.hk2, hA := Nat.one_le_of_lt F.hkA, gap := ?_,
           eO := eO, eO1 := eO1, eQ := eQL, eQ1 := eQuery_lt_one F.hq }
  · have := F'.hκ; dsimp only; omega
  · have := F'.hgap
    simp only [LevelCode.n, LevelCode.deg, LevelCode.thr, Nat.sub_zero]
    exact this

theorem levelChecks_of_chain {κp : ℕ} {lv : Lv} {rest : List Lv} {c : Whir.Level}
    {crest : List Whir.Level} (h : chainChecks κp (lv :: rest) (c :: crest) = true) :
    levelChecks κp lv c = true := by
  match rest, crest, h with
  | [], [], h => exact h
  | [], _ :: _, h => simp [chainChecks] at h
  | _ :: _, [], h => simp [chainChecks] at h
  | _ :: _, _ :: _, h =>
    simp only [chainChecks, Bool.and_eq_true] at h
    exact h.1.1.1.1

/-- **The ladder's groups** from the chain's checks. -/
theorem ladderOK_of_chain (codes : ℕ → LevelCode) :
    ∀ (lvs : List Lv) (cfg : List Whir.Level) (κp i : ℕ), chainChecks κp lvs cfg = true →
      (∀ j (hj : j < lvs.length), codes (i + j) = mkCode lvs[j]) → LadderOK codes εmsg i cfg
  | [], _, _, _, h, _ => by simp [chainChecks] at h
  | [_], [], _, _, h, _ => by simp [chainChecks] at h
  | [_], _ :: _ :: _, _, _, h, _ => by simp [chainChecks] at h
  | _ :: _ :: _, [], _, _, h, _ => by simp [chainChecks] at h
  | _ :: _ :: _, [_], _, _, h, _ => by simp [chainChecks] at h
  | [lv], [c], κp, i, h, hc => by
    have F := levelFacts_of (κprev := κp) (lv := lv) (cfg := c) h
    have h0 : codes i = mkCode lv := hc 0 (by simp)
    rw [LadderOK, h0, mkCode_eq ⟨F.h64, F.hR⟩]
    refine ⟨F.hfold, F.hrate, ?_⟩
    rw [← mkCode_eq ⟨F.h64, F.hR⟩]
    exact finalOK_of F
  | lv :: lv' :: rest, c :: c' :: crest, κp, i, h, hc => by
    have h' := h
    simp only [chainChecks, Bool.and_eq_true, decide_eq_true_eq] at h'
    obtain ⟨⟨⟨⟨h1, hl⟩, ho⟩, hκ1⟩, hrest⟩ := h'
    have F := levelFacts_of h1
    have F' := levelFacts_of (levelChecks_of_chain hrest)
    have h0 : codes i = mkCode lv := hc 0 (by simp)
    have h1' : codes (i + 1) = mkCode lv' := hc 1 (by simp)
    rw [LadderOK, h0, h1']
    refine ⟨by rw [mkCode_eq ⟨F.h64, F.hR⟩]; exact F.hfold,
      by rw [mkCode_eq ⟨F.h64, F.hR⟩]; exact F.hrate, midOK_of F F' hl ho hκ1, ?_⟩
    exact ladderOK_of_chain codes (lv' :: rest) (c' :: crest) lv.1 (i + 1) hrest fun j hj ↦ by
      rw [show i + 1 + j = i + (j + 1) by omega]
      exact hc (j + 1) (by simp only [List.length_cons] at hj ⊢; omega)

/-- Every level of a chain checks its fold rounds. -/
theorem chain_mem : ∀ (lvs : List Lv) (cfg : List Whir.Level) (κp : ℕ),
    chainChecks κp lvs cfg = true → ∀ lv ∈ lvs,
      AffineCombiner.levelOK AffineCombiner.foldBudget lv = true ∧ lv.2.2.1 < lv.2.2.2.1
  | [], _, _, h => by simp [chainChecks] at h
  | [_], [], _, h => by simp [chainChecks] at h
  | [_], _ :: _ :: _, _, h => by simp [chainChecks] at h
  | _ :: _ :: _, [], _, h => by simp [chainChecks] at h
  | _ :: _ :: _, [_], _, h => by simp [chainChecks] at h
  | [lv], [c], κp, h => fun x hx ↦ by
    have F := levelFacts_of (κprev := κp) (lv := lv) (cfg := c) h
    rw [List.mem_singleton] at hx
    subst hx
    exact ⟨F.hlv, F.hkA⟩
  | lv :: lv' :: rest, c :: c' :: crest, κp, h => fun x hx ↦ by
    have h' := h
    simp only [chainChecks, Bool.and_eq_true, decide_eq_true_eq] at h'
    obtain ⟨⟨⟨⟨h1, -⟩, -⟩, -⟩, hrest⟩ := h'
    rcases List.mem_cons.mp hx with rfl | hx
    · have F := levelFacts_of h1
      exact ⟨F.hlv, F.hkA⟩
    · exact chain_mem (lv' :: rest) (c' :: crest) lv.1 hrest x hx

/-! ## The shapes -/

/-- What `shapeOK` checks. -/
theorem shapeOK_facts {μ R : ℕ} (hok : shapeOK μ R = true) :
    ∃ cfg lv rest, Whir.ladder μ R = some cfg ∧ levelsOf μ R = lv :: rest ∧
      chainChecks μ (lv :: rest) cfg = true ∧ lv.2.1 = R ∧ lv.2.2.1 = 6 ∧
      degOf lv < lv.2.2.2.1 - lv.2.2.1 ∧ jlStart lv ≤ 166 ∧ 513 * jlStart lv ≤ 2 ^ 16 ∧
      (jlStart lv).choose 2 * μ ≤ 2 ^ 18 := by
  unfold shapeOK at hok
  rcases hc : Whir.ladder μ R with _ | cfg <;> rcases hl : levelsOf μ R with _ | ⟨lv, rest⟩ <;>
    rw [hc, hl] at hok <;> simp only [Bool.false_eq_true] at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hok
  exact ⟨cfg, lv, rest, rfl, rfl, h1, h2, h3, h4, h5, h6, h7⟩

theorem shapeOK_of_admissible {μ R : ℕ} (h : Whir.Admissible μ R) : shapeOK μ R = true :=
  shapeOK_all μ (Nat.lt_succ_of_le h.2.1) R (Nat.lt_succ_of_le h.2.2.2) h

/-- Each code's fold rounds. -/
noncomputable def deployedBounds {μ R : ℕ} (hok : shapeOK μ R = true) (j : ℕ) :
    RoundBounds (codesOf μ R j) εmsg :=
  roundBoundsOf _ (facts j).1 (facts j).2
where
  facts (j : ℕ) : AffineCombiner.levelOK AffineCombiner.foldBudget ((levelsOf μ R).getD j junkLv) =
      true ∧ ((levelsOf μ R).getD j junkLv).2.2.1 < ((levelsOf μ R).getD j junkLv).2.2.2.1 := by
    obtain ⟨cfg, lv, rest, -, hl, hch, -⟩ := shapeOK_facts hok
    rcases lt_or_ge j (levelsOf μ R).length with hj | hj
    · rw [List.getD_eq_getElem _ _ hj]
      exact chain_mem _ cfg μ (hl ▸ hch) _ (List.getElem_mem hj)
    · rw [List.getD_eq_default _ _ hj]
      exact ⟨by decide, by decide⟩

/-- Level 0 of an admissible shape. -/
structure Level0Facts (μ R : ℕ) (level : Whir.Level) (rest : List Whir.Level) : Prop where
  hc : Whir.ladder μ R = some (level :: rest)
  hℓ : level.fold = laneBits
  hμ : laneBits ≤ μ
  hκ₀ : (codesOf μ R 0).κ = μ - laneBits
  hR₀ : (codesOf μ R 0).R = R
  hthr : (codesOf μ R 0).deg < (codesOf μ R 0).thr 0
  hthr₀ : (codesOf μ R 0).thr 0 = thr0Of μ R
  h64 : μ - laneBits + R ≤ 64
  hgap : 2 ^ (μ - laneBits + R) * (2 ^ (μ - laneBits) - 1 + laneBits) < thr0Of μ R * thr0Of μ R
  hL : listMax₀ μ R =
    jl (2 ^ (μ - laneBits + R)) (thr0Of μ R) (2 ^ (μ - laneBits) - 1 + laneBits)
  hA : LadderOK (codesOf μ R) εmsg 0 (level :: rest)

theorem level0Facts {μ R : ℕ} (hok : shapeOK μ R = true) :
    ∃ level rest, Level0Facts μ R level rest := by
  obtain ⟨cfg, lv, rest, hc, hl, hch, hR, hk, hthr, -⟩ := shapeOK_facts hok
  obtain ⟨level, crest, rfl⟩ : ∃ level crest, cfg = level :: crest := by
    rcases cfg with _ | ⟨level, crest⟩
    · rcases rest <;> simp [chainChecks] at hch
    · exact ⟨level, crest, rfl⟩
  have F := levelFacts_of (levelChecks_of_chain hch)
  have h0 : codesOf μ R 0 = mkCode lv := by simp [codesOf, hl]
  have hκ : lv.1 = μ - laneBits := by show lv.1 = μ - 6; have := F.hκ; omega
  have hthr0 : thr0Of μ R = lv.2.2.2.1 - lv.2.2.1 := by simp [thr0Of, thrStart, hl]
  refine ⟨level, crest, ⟨hc, by rw [F.hfold, hk], by show 6 ≤ μ; have := F.hκ; omega, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ladderOK_of_chain _ (lv :: rest) _ μ 0 hch fun j hj ↦ by
      simp only [codesOf, hl, Nat.zero_add, List.getD_eq_getElem _ _ hj]⟩⟩
  · rw [h0, mkCode_eq ⟨F.h64, F.hR⟩]; exact hκ
  · rw [h0, mkCode_eq ⟨F.h64, F.hR⟩]; exact hR
  · rw [h0, mkCode_eq ⟨F.h64, F.hR⟩]
    simp only [LevelCode.deg, LevelCode.thr, Nat.sub_zero]
    simpa only [degOf] using hthr
  · rw [h0, mkCode_eq ⟨F.h64, F.hR⟩, hthr0]; rfl
  · have := F.h64; omega
  · rw [hthr0, ← hκ, ← hR, show laneBits = lv.2.2.1 from hk.symm]
    exact F.hgap
  · rw [listMax₀, hl, hthr0, ← hκ, ← hR]
    simp only [jlStart, degOf, hk, List.headD_cons]
    rfl

/-! ## Level 0's list -/

/-- **Level 0's list bound is at most `166`.** -/
theorem listMax₀_le {μ R : ℕ} (h : Whir.Admissible μ R) : listMax₀ μ R ≤ 166 := by
  obtain ⟨cfg, lv, rest, -, hl, -, -, -, -, h166, -⟩ := shapeOK_facts (shapeOK_of_admissible h)
  rw [listMax₀, hl]
  exact h166

/-- The commitment's out-of-domain row: `C(L₀, 2)·μ ≤ 2^18`. -/
theorem ood_row {μ R : ℕ} (h : Whir.Admissible μ R) : (listMax₀ μ R).choose 2 * μ ≤ 2 ^ 18 := by
  obtain ⟨cfg, lv, rest, -, hl, -, -, -, -, -, -, ho⟩ := shapeOK_facts (shapeOK_of_admissible h)
  rw [listMax₀, hl]
  exact ho

/-- The stacked opening's batching row with the ring's map: `513·L₀ ≤ 2^16`. -/
theorem lambda_row {μ R : ℕ} (h : Whir.Admissible μ R) : 513 * listMax₀ μ R ≤ 2 ^ 16 := by
  obtain ⟨cfg, lv, rest, -, hl, -, -, -, -, -, hlam, -⟩ := shapeOK_facts (shapeOK_of_admissible h)
  rw [listMax₀, hl]
  exact hlam

/-- **The candidates at level 0's threshold** are finite, at most `listMax₀`. -/
theorem candidates_facts {μ R : ℕ} (h : Whir.Admissible μ R) (W : Word) :
    (Candidates μ R (thr0Of μ R) W).Finite ∧
      (Candidates μ R (thr0Of μ R) W).ncard ≤ listMax₀ μ R := by
  obtain ⟨_, _, F⟩ := level0Facts (shapeOK_of_admissible h)
  have hc := candidates_ncard_le (A := thr0Of μ R) F.hμ F.h64 [(0, 0, W)]
  refine ⟨hc.1, hc.2.trans ?_⟩
  rw [F.hL]
  exact card_tlist_le_jl _ _ _ _ F.hgap

/-! ## The stacked opening -/

/-- **The deployed stacked opening's specification**: from `StackedPre` at level 0's threshold,
every group within `εmsg = 2^-125` after its grind, the batching challenge with lead
`(J − 1)·L₀/|E|`. -/
noncomputable def deployedStackedSpec {μ R : ℕ} (h : Whir.Admissible μ R)
    (claims : List StackClaim) (hcl : ∀ c ∈ claims, IsMultiaffine μ c.1) (T : ENNReal) :
    Spec (verifyStackedOpening μ R claims)
      (fun h ↦ StackedPre μ R (thr0Of μ R) claims (commits h)) (fun _ _ ↦ False) εmsg
      (eBatch claims.length (listMax₀ μ R)) T :=
  match hc : Whir.ladder μ R with
  | some (level :: rest) =>
    have F : Level0Facts μ R level rest := by
      obtain ⟨level', rest', F⟩ := level0Facts (shapeOK_of_admissible h)
      have heq := F.hc
      rw [hc, Option.some.injEq, List.cons.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      exact F
    (stackedSpec claims hcl F.hc F.hℓ F.hμ F.hκ₀ F.hR₀ F.hthr
      (deployedBounds (shapeOK_of_admissible h)) F.hA (listMax₀ μ R)
      (fun W ↦ F.hthr₀ ▸ (candidates_facts h W).1)
      (fun W ↦ F.hthr₀ ▸ (candidates_facts h W).2) T).mono
      (fun _ hp ↦ by rw [F.hthr₀]; exact hp) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  | some [] => False.elim (by
      obtain ⟨level', rest', F⟩ := level0Facts (shapeOK_of_admissible h)
      have h' := F.hc
      rw [hc] at h'
      simp at h')
  | none => False.elim (by
      obtain ⟨level', rest', F⟩ := level0Facts (shapeOK_of_admissible h)
      have h' := F.hc
      rw [hc] at h'
      simp at h')

end
end LeanVM.Protocol.Whir.Params
