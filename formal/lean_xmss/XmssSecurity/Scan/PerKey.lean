import XmssSecurity.Scan.Phase

/-!
# One key: the cached-selection collision against the encoding queries

From a key cache with no encoding input, the adversary phase followed by a final computation (the
verification) has a first entry whose selected cached input is partnered, or whose selected digest a
later query repeats, with probability at most the source game's expected encoding queries over
`2^128`.
-/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.Ghost

open Partner

local notation "N" => ((2 ^ digestBits : ℕ) : ℝ≥0∞)

variable (publicKey : PublicKey) (secretKey : SecretKey) {cache0 : QueryCache HashSpec}
  (hc0 : ∀ e y, cache0 (input secretKey.parameter e y) = none)

section Initial

include hc0

theorem C_initial (e : LeafIndex) : C cache0 secretKey.parameter e = 0 := by
  unfold C
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro y _ h
  rw [hc0] at h
  exact Bool.false_ne_true h

theorem V_initial (e : LeafIndex) : V cache0 secretKey.parameter e = 0 := by
  classical
  unfold V
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro y _ ⟨o, ho, -⟩
  rw [hc0] at ho
  cases ho

theorem Φ_initial (e : LeafIndex) : Φ cache0 secretKey.parameter e = 0 := by
  unfold Φ
  refine Finset.sum_eq_zero fun y _ => ite_eq_right ?_
  rintro ⟨o, ho, -⟩
  rw [hc0] at ho
  cases ho

theorem f1_initial : f1 secretKey ((cache0, []), 0) = 0 := by
  have hpre : ¬PreBad secretKey [] := by rintro ⟨e, entry, h, -⟩; cases h
  unfold f1 openΦ
  rw [ite_eq_right hpre, mul_zero, zero_add, Finset.sum_eq_zero fun e _ => by rw [Φ_initial secretKey hc0, ite_self],
    mul_zero]

theorem f2_initial : f2 secretKey ((cache0, []), 0) = 0 := by
  unfold f2 hvSum
  exact Finset.sum_eq_zero fun e _ => by
    rw [show frozen cache0 [] e = cache0 from rfl, V_initial secretKey hc0, Nat.cast_zero, zero_mul]

theorem counts_initial :
    nCount secretKey.parameter cache0 [] = 0 ∧ vCount secretKey.parameter cache0 [] = 0 :=
  ⟨Finset.sum_eq_zero fun e _ => C_initial secretKey hc0 e,
    Finset.sum_eq_zero fun e _ => V_initial secretKey hc0 e⟩

theorem f3_initial (Q : ℕ) : f3 secretKey Q ((cache0, []), 0) = 0 := by
  unfold f3
  rw [(counts_initial secretKey hc0).1, (counts_initial secretKey hc0).2]
  exact F3_zero _ _

theorem inv_initial : Inv secretKey ((cache0, []), 0) := by
  unfold Inv
  rw [(counts_initial secretKey hc0).1]

end Initial

theorem postPot_nil (cache : QueryCache HashSpec) : postPot secretKey.parameter [] cache = 0 := by
  unfold postPot
  rw [ite_eq_right]
  rintro ⟨-, e, entry, h, -⟩
  cases h

/-- The adversary's fresh encoding queries at unsigned leaf indices. -/
noncomputable def openCost : (OracleWorld + SigningSpec).Domain → State → ℝ≥0∞ :=
  onHash fun x s => openInd secretKey.parameter x s.1.1 s.1.2

/-- The adversary's encoding queries at signed leaf indices. -/
noncomputable def signedCost : (OracleWorld + SigningSpec).Domain → State → ℝ≥0∞ :=
  onHash fun x s => signedInd secretKey.parameter x s.1.2

include hc0 in
/-- **Before signing.** -/
theorem preBad_le (Q : ℕ) (hQ : Q ≤ 2 ^ 127) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (hbound : HashQueryBound (simulateQ (cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey)
      computation) cache0 Q) :
    N * N * Pr{let r ← (simulateQ (impl publicKey secretKey) computation).run ((cache0, []), 0)}[PreBad secretKey r.2.1.2] ≤
      ENNReal.ofReal (momentA pReal Q) *
        expectedSimulatedCost (impl publicKey secretKey) (openCost secretKey) computation ((cache0, []), 0) := by
  classical
  set s0 : State := ((cache0, []), 0)
  set I := impl publicKey secretKey
  set cost := expectedSimulatedCost I (cost1 secretKey) computation s0
  have hpre : N * N * Pr{let r ← (simulateQ I computation).run s0}[PreBad secretKey r.2.1.2] ≤ cost := by
    refine (const_mul_probEvent_le_expectedFinal I (f1 secretKey) (fun s => PreBad secretKey s.1.2) (N * N)
      (fun s h => ?_) computation s0).trans ?_
    · unfold f1; rw [ite_eq_left h, mul_one]; exact le_self_add
    · refine (expectedFinal_le I (Inv := fun _ => True) (fun _ _ _ _ _ => trivial) (f1 secretKey)
        (cost1 secretKey) (fun input s _ => f1_step publicKey secretKey input s) computation s0 trivial).trans ?_
      rw [f1_initial secretKey hc0, zero_add]
  have h2 : landing * cost ≤ expectedFinal I (f2 secretKey) computation s0 := by
    have h := expectedFinal_ge I (Inv := fun _ => True) (fun _ _ _ _ _ => trivial) (f2 secretKey)
      (fun input s => landing * cost1 secretKey input s) (fun input s _ => f2_step publicKey secretKey input s)
      computation s0 trivial
    rwa [f2_initial secretKey hc0, zero_add, expectedSimulatedCost_const_mul] at h
  have h23 : landing * expectedFinal I (f2 secretKey) computation s0 ≤
      landing ^ 2 * expectedFinal I (f3 secretKey Q) computation s0 := by
    unfold expectedFinal
    rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun r => ?_
    rw [mul_left_comm, mul_left_comm (landing ^ 2)]
    exact mul_le_mul' le_rfl (landing_mul_hvSum_le Q (k := r.2.2) secretKey.parameter r.2.1.1 r.2.1.2)
  have h3 : expectedFinal I (f3 secretKey Q) computation s0 ≤
      ENNReal.ofReal (momentA pReal Q) * expectedSimulatedCost I (openCost secretKey) computation s0 := by
    refine (expectedFinal_le I (inv_step publicKey secretKey) (f3 secretKey Q) (cost3 secretKey Q)
      (fun input s hs => f3_step publicKey secretKey Q hQ input s hs) computation s0
      (inv_initial secretKey hc0)).trans (le_of_eq ?_)
    rw [f3_initial secretKey hc0, zero_add]
    unfold cost3
    rw [expectedSimulatedCost_add, expectedSimulatedCost_const_mul,
      expectedSimulatedCost_overBudget_eq_zero publicKey secretKey Q computation cache0 [] 0
        (by simpa using hbound) (Nat.zero_le _), zero_add]
    rfl
  have hl0 : landing ^ 2 ≠ 0 := pow_ne_zero 2 landing_ne_zero
  have hlt : landing ^ 2 ≠ ⊤ := pow_ne_top landing_ne_top
  have hcost : cost ≤ ENNReal.ofReal (momentA pReal Q) *
      expectedSimulatedCost I (openCost secretKey) computation s0 := by
    rw [← ENNReal.mul_le_mul_iff_right hl0 hlt]
    calc landing ^ 2 * cost = landing * (landing * cost) := by ring
      _ ≤ landing * expectedFinal I (f2 secretKey) computation s0 := mul_le_mul' le_rfl h2
      _ ≤ _ := h23.trans (mul_le_mul' le_rfl h3)
  exact hpre.trans hcost

/-- **After signing.** The final computation's encoding queries each repeat a selected digest with
probability `2^-128`. -/
theorem postPot_final_le (trace : SigningCacheTrace) (computation : OracleComp OracleWorld β)
    (cache : QueryCache HashSpec) :
    ∑' y, Pr{let x ← (simulateQ romImpl computation).run cache}[x = y] * (N * N * postPot secretKey.parameter trace y.2) ≤
      N * N * postPot secretKey.parameter trace cache +
        N * expectedSimulatedQueryCount romImpl
          (CappedEncodingMonitor.IsEncodingHashQuery secretKey.parameter) computation cache := by
  refine (expectedFinal_le romImpl (Inv := fun _ => True) (fun _ _ _ _ _ => trivial)
    (fun c => N * N * postPot secretKey.parameter trace c)
    (fun w _ => N * worldSigned secretKey.parameter trace w) (fun w c _ => ?_) computation cache trivial).trans ?_
  · calc _ = N * N * ∑' r, Pr{let x ← (romImpl w).run c}[x = r] * postPot secretKey.parameter trace r.2 := by
          rw [← ENNReal.tsum_mul_left]
          exact tsum_congr fun r => mul_left_comm _ _ _
      _ ≤ N * N * (postPot secretKey.parameter trace c + worldSigned secretKey.parameter trace w * N⁻¹) :=
          mul_le_mul' le_rfl (postPot_romImpl _ _ _ _)
      _ = _ := by rw [mul_add, N_mul_N_mul_inv]
  · refine add_le_add le_rfl ?_
    rw [expectedSimulatedCost_const_mul, ← expectedSimulatedCost_indicator]
    exact mul_le_mul' le_rfl (expectedSimulatedCost_mono romImpl
      (fun w _ => worldSigned_le secretKey.parameter trace w) computation cache)

theorem momentA_le_N {Q : ℕ} (hQ : Q < 2 ^ 127) : ENNReal.ofReal (momentA pReal Q) ≤ N := by
  have hd : digestBits = 128 := rfl
  have hN : N = ENNReal.ofReal ((2 : ℝ) ^ digestBits) := by
    rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat, Nat.cast_pow, Nat.cast_ofNat]
  rw [hN]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [hd]
  have hQ' : (Q : ℝ) ≤ 2 ^ 127 := by exact_mod_cast hQ.le
  have hp := pReal_ge
  have hp1 := pReal_le_one
  have hQ0 : (0 : ℝ) ≤ Q := Nat.cast_nonneg Q
  unfold momentA momentK
  by_cases hsmall : (Q : ℝ) ≤ 2 ^ 127 - 2 ^ 75
  · nlinarith
  · nlinarith

theorem hashQueryBound_left {first : OracleComp OracleWorld α} {next : α → OracleComp OracleWorld β}
    {cache : QueryCache HashSpec} {q : ℕ} (h : HashQueryBound (first >>= next) cache q) :
    HashQueryBound first cache q := by
  rw [hashQueryBound_iff_run]
  exact fun result hresult => (hashQueryBound_bind first next cache q h result hresult).1

theorem openCost_add_signedCost_le (input : (OracleWorld + SigningSpec).Domain) (s : State) :
    openCost secretKey input s + signedCost secretKey input s ≤
      if IsAdvEncoding secretKey.parameter input then 1 else 0 := by
  rcases input with (n | x) | request
  · rw [openCost, signedCost, onHash_unif, onHash_unif, add_zero]; exact zero_le
  · rw [openCost, signedCost, onHash_hash, onHash_hash]
    refine (openInd_add_signedInd_le x s.1.1 s.1.2).trans ?_
    split_ifs with hd henc
    · exact le_rfl
    · exfalso
      obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hd
      have h := encodingInputLeafIndex?_encodingInput secretKey.parameter p.1 p.2
      have h' : encodingInputLeafIndex? secretKey.parameter x = some p.1 := by
        rw [dec_eq_some secretKey.parameter hp]; exact h
      apply henc
      change (encodingInputLeafIndex? secretKey.parameter x).isSome
      rw [h']
      rfl
    · exact zero_le
    · exact le_rfl
  · rw [openCost, signedCost, onHash_sign, onHash_sign, add_zero]; exact zero_le

include hc0 in
/-- **One key.** -/
theorem collision_le (Q : ℕ) (hQ : Q < 2 ^ 127) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (cont : α → OracleComp OracleWorld β)
    (hbound : HashQueryBound (simulateQ (cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey)
      computation >>= cont) cache0 Q) :
    N * N * Pr{let y ← ((simulateQ (impl publicKey secretKey) computation).run ((cache0, []), 0) >>= fun r =>
        (fun v => (r, v)) <$> (simulateQ romImpl (cont r.1)).run r.2.1.1)}[y.1.2.1.2.leafIndices.Nodup ∧
        (PreBad secretKey y.1.2.1.2 ∨ PostBad secretKey.parameter y.1.2.1.2 y.2.2)] ≤
      N * expectedSimulatedQueryCount romImpl (CappedEncodingMonitor.IsEncodingHashQuery secretKey.parameter)
        (simulateQ (cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey) computation >>= cont)
        cache0 := by
  classical
  set s0 : State := ((cache0, []), 0)
  set I := impl publicKey secretKey
  set run := (simulateQ I computation).run s0
  set P := secretKey.parameter
  set Ecount := fun (r : α × State) =>
    expectedSimulatedQueryCount romImpl (CappedEncodingMonitor.IsEncodingHashQuery P) (cont r.1) r.2.1.1
  have hhead := hashQueryBound_left hbound
  -- the event against the two potentials
  have hsplit : N * N * Pr{let y ← run >>= fun r => (fun v => (r, v)) <$> (simulateQ romImpl (cont r.1)).run r.2.1.1}[y.1.2.1.2.leafIndices.Nodup ∧
        (PreBad secretKey y.1.2.1.2 ∨ PostBad P y.1.2.1.2 y.2.2)] ≤
      ∑' r, Pr{let x ← run}[x = r] * (N * N * (if PreBad secretKey r.2.1.2 then 1 else 0) +
        (f4 secretKey r.2 + N * Ecount r)) := by
    rw [OracleComp.prEvent_bind_eq_tsum, ← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun r => ?_
    rw [mul_left_comm]
    refine mul_le_mul' le_rfl ?_
    rw [prEvent_map, OracleComp.prEvent_eq_tsum_ite, ← ENNReal.tsum_mul_left]
    calc ∑' v, N * N * (if (fun y : (α × State) × (β × QueryCache HashSpec) => y.1.2.1.2.leafIndices.Nodup ∧
            (PreBad secretKey y.1.2.1.2 ∨ PostBad P y.1.2.1.2 y.2.2)) ((fun v => (r, v)) v) then
            Pr{let x ← (simulateQ romImpl (cont r.1)).run r.2.1.1}[x = v] else 0) ≤
          ∑' v, Pr{let x ← (simulateQ romImpl (cont r.1)).run r.2.1.1}[x = v] *
            (N * N * (if PreBad secretKey r.2.1.2 then 1 else 0) + N * N * postPot P r.2.1.2 v.2) := by
          refine ENNReal.tsum_le_tsum fun v => ?_
          dsimp only
          by_cases h1 : r.2.1.2.leafIndices.Nodup ∧ (PreBad secretKey r.2.1.2 ∨ PostBad P r.2.1.2 v.2)
          · rw [ite_eq_left h1, mul_comm]
            refine mul_le_mul' le_rfl ?_
            by_cases h2 : PreBad secretKey r.2.1.2
            · rw [ite_eq_left h2, mul_one]; exact le_self_add
            · rw [ite_eq_right h2, mul_zero, zero_add]
              unfold postPot
              rw [ite_eq_left ⟨h1.1, h1.2.resolve_left h2⟩, mul_one]
          · rw [ite_eq_right h1, mul_zero]; exact zero_le
      _ = (∑' v, Pr{let x ← (simulateQ romImpl (cont r.1)).run r.2.1.1}[x = v]) *
              (N * N * (if PreBad secretKey r.2.1.2 then 1 else 0)) +
            ∑' v, Pr{let x ← (simulateQ romImpl (cont r.1)).run r.2.1.1}[x = v] * (N * N * postPot P r.2.1.2 v.2) := by
          simp_rw [mul_add]
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
      _ ≤ 1 * (N * N * (if PreBad secretKey r.2.1.2 then 1 else 0)) +
            (N * N * postPot P r.2.1.2 r.2.1.1 + N * Ecount r) :=
          add_le_add (mul_le_mul' (OracleComp.tsum_prEvent_le_one _) le_rfl)
            (postPot_final_le secretKey r.2.1.2 (cont r.1) r.2.1.1)
      _ = _ := by rw [one_mul]; rfl
  have hpre := preBad_le publicKey secretKey hc0 Q hQ.le computation hhead
  have hf4 : expectedFinal I (f4 secretKey) computation s0 ≤
      N * expectedSimulatedCost I (signedCost secretKey) computation s0 := by
    refine (expectedFinal_le I (Inv := fun _ => True) (fun _ _ _ _ _ => trivial) (f4 secretKey) (cost4 secretKey)
      (fun input s _ => f4_step publicKey secretKey input s) computation s0 trivial).trans (le_of_eq ?_)
    rw [show f4 secretKey s0 = 0 by rw [f4, postPot_nil, mul_zero], zero_add, ← expectedSimulatedCost_const_mul]
    rfl
  have hadv : expectedSimulatedCost I (openCost secretKey) computation s0 +
      expectedSimulatedCost I (signedCost secretKey) computation s0 ≤
      expectedSimulatedQueryCount romImpl (CappedEncodingMonitor.IsEncodingHashQuery P)
        (simulateQ (cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey) computation) cache0 := by
    rw [← expectedSimulatedCost_add]
    exact (expectedSimulatedCost_mono I (openCost_add_signedCost_le secretKey) computation s0).trans
      (expectedSimulatedCost_advEncoding_le publicKey secretKey P computation cache0 [] 0)
  have hcont : ∑' r, Pr{let x ← run}[x = r] * Ecount r =
      ∑' y, Pr{let x ← ((simulateQ romImpl (simulateQ (cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey)
        computation)).run cache0)}[x = y] *
        expectedSimulatedQueryCount romImpl (CappedEncodingMonitor.IsEncodingHashQuery P) (cont y.1) y.2 := by
    rw [← impl_run_proj, OracleComp.tsum_prEvent_map_mul]
  refine hsplit.trans ?_
  calc ∑' r, Pr{let x ← run}[x = r] * (N * N * (if PreBad secretKey r.2.1.2 then 1 else 0) +
        (f4 secretKey r.2 + N * Ecount r)) =
      N * N * Pr{let r ← run}[PreBad secretKey r.2.1.2] + expectedFinal I (f4 secretKey) computation s0 +
        N * ∑' r, Pr{let x ← run}[x = r] * Ecount r := by
        simp_rw [mul_add]
        rw [ENNReal.tsum_add, ENNReal.tsum_add, add_assoc, expectedFinal, ← ENNReal.tsum_mul_left,
          OracleComp.prEvent_eq_tsum_ite, ← ENNReal.tsum_mul_left]
        congr 1
        · refine tsum_congr fun r => ?_
          split_ifs <;> ring
        · congr 1
          exact tsum_congr fun r => mul_left_comm _ _ _
    _ ≤ N * expectedSimulatedCost I (openCost secretKey) computation s0 +
          N * expectedSimulatedCost I (signedCost secretKey) computation s0 + N * ∑' r, Pr{let x ← run}[x = r] * Ecount r :=
        add_le_add (add_le_add (hpre.trans (mul_le_mul' (momentA_le_N hQ) le_rfl)) hf4) le_rfl
    _ ≤ _ := by
        rw [← mul_add, ← mul_add, expectedSimulatedQueryCount_bind, hcont]
        exact mul_le_mul' le_rfl (add_le_add hadv le_rfl)

end XmssSecurity.Ghost
