module

public import Quantum.Qrom.Sphincs.Multi.CovMaxCert

@[expose] public section

/-!
# The worst user's FORS coverage price

`rhoMaxQ n` is the mean over `n` independent users, each with a uniform stream of
`signatureLimit` regrouped `H_msg` pairs, of the largest price `max_i price(S★_i)`.

* `rhoMaxQ_one`: one user, the single-user mean `rhoCov / 2^128`.
* `uavg_sq_add_sqrt_starCoverN_table_le`: Minkowski over the `n` streams held by a table at
  injective positions, with instability `2^-128 + max_i price_i` (as
  `uavg_sq_add_sqrt_starCover_table_le` for one user).
* `rhoMaxQ_le_of`: for a rate `λ > 0` and a cut `k0`, `E max_i Y_i ≤ t + n E(Y - t)^+`,
  `(A - t)^+ ≤ e^{λ(A - t)} / (e λ)` for the capped part `A` and the excess beyond the cut
  (`uavg_price_sub_le`), with `t = (max(log n + κ, 1) - 1)/λ`: the bound
  `(max(log n + κ, 1)/λ + n β) / 2^128` from `E Π loadFactor ≤ e^κ` and the binomial tail `β`.
* `rhoMaxR n`: the least of `n · rhoCov` and the 34 certified pieces of `covTable`
  (`rhoMaxQ_le`, `rhoMaxR_mono`), with values at `n = 2^10, …, 2^64` (`rhoMaxR_two_pow_*`).
-/

open Finset
open scoped ENNReal
open HashSig hiding PublicKey
open Sphincs hiding HashDomain
open Quantum.Sphincs (View price revealed rhoCov coverProb binomMean)
open Quantum.Xmss.Hybrid (uavg uavg_add uavg_const_mul uavg_mono)

namespace Quantum.Qrom.Sphincs.Multi

/-- The averaged worst-user price: n users, each with a uniform stream of `signatureLimit`
pairs. -/
noncomputable def rhoMaxQ (n : ℕ) : ℝ≥0∞ :=
  Quantum.Xmss.Hybrid.uavg (fun d : Fin n → Fin signatureLimit → HashOutput × HashOutput ↦
    ⨆ i, ENNReal.ofReal (price (starCover (d i))))

/-! ## One user, and the table -/

theorem rhoMaxQ_one : rhoMaxQ 1 ≤ ENNReal.ofReal (rhoCov / 2 ^ 128) := by
  unfold rhoMaxQ
  simp only [iSup_unique]
  rw [uavg_comp_apply default fun d ↦ ENNReal.ofReal (price (starCover d))]
  exact uavg_price_starCover_le

/-- **Minkowski over the worst S★, on a table** holding the `n` streams at injective positions. -/
theorem uavg_sq_add_sqrt_starCoverN_table_le {n : ℕ} {P : Type*} [Fintype P] [DecidableEq P]
    (pos : Fin n × Fin signatureLimit → P) (hpos : Function.Injective pos) (a c : ℝ≥0∞) :
    uavg (fun θ : P → HashOutput × HashOutput ↦ (a + (c * ((2 ^ 128)⁻¹ +
      ⨆ i, ENNReal.ofReal (price (starCover fun j ↦ θ (pos (i, j)))))) ^ (2⁻¹ : ℝ)) ^ 2) ≤
      (a + (c * ((2 ^ 128)⁻¹ + rhoMaxQ n)) ^ (2⁻¹ : ℝ)) ^ 2 := by
  set g : (Fin n → Fin signatureLimit → HashOutput × HashOutput) → ℝ≥0∞ := fun d ↦
    c * ((2 ^ 128)⁻¹ + ⨆ i, ENNReal.ofReal (price (starCover (d i))))
  calc uavg (fun θ : P → HashOutput × HashOutput ↦ (a + (c * ((2 ^ 128)⁻¹ +
        ⨆ i, ENNReal.ofReal (price (starCover fun j ↦ θ (pos (i, j)))))) ^ (2⁻¹ : ℝ)) ^ 2)
      = uavg (fun D : Fin n × Fin signatureLimit → HashOutput × HashOutput ↦
          (a + g (Function.curry D) ^ (2⁻¹ : ℝ)) ^ 2) :=
        uavg_comp_restrict pos hpos fun D ↦ (a + g (Function.curry D) ^ (2⁻¹ : ℝ)) ^ 2
    _ = uavg (fun d ↦ (a + g d ^ (2⁻¹ : ℝ)) ^ 2) :=
        Quantum.Sphincs.uavg_comp_equiv (Equiv.curry _ _ _) fun d ↦ (a + g d ^ (2⁻¹ : ℝ)) ^ 2
    _ ≤ (a + uavg g ^ (2⁻¹ : ℝ)) ^ 2 := uavg_sq_add_rpow_le a g
    _ ≤ _ := by
        refine pow_le_pow_left₀ zero_le (add_le_add le_rfl
          (ENNReal.rpow_le_rpow ?_ (by norm_num : (0 : ℝ) ≤ 2⁻¹))) 2
        rw [uavg_const_mul, uavg_add]
        gcongr
        · exact uavg_const_le _
        · exact le_rfl

/-! ## Uniform streams through equal fibers -/

/-- Streams of outputs whose map `g` has fibers of equal size average as streams of images. -/
theorem uavg_comp_fiber {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] (g : Ω → V)
    (c : ℕ) (hc : 0 < c) (hg : ∀ v, #(univ.filter fun ω ↦ g ω = v) = c) (n : ℕ)
    (Φ : (Fin n → V) → ℝ≥0∞) : uavg (fun d : Fin n → Ω ↦ Φ fun j ↦ g (d j)) = uavg Φ := by
  have hsum : ∑ d : Fin n → Ω, Φ (fun j ↦ g (d j)) = (c : ℝ≥0∞) ^ n * ∑ v, Φ v := by
    calc ∑ d : Fin n → Ω, Φ (fun j ↦ g (d j))
        = ∑ v : Fin n → V, ∑ d ∈ univ.filter (fun d : Fin n → Ω ↦ (fun j ↦ g (d j)) = v), Φ v :=
          (sum_fiberwise_of_maps_to' (fun d _ ↦ mem_univ fun j ↦ g (d j)) Φ).symm
      _ = ∑ v : Fin n → V, (c : ℝ≥0∞) ^ n * Φ v := by
          refine sum_congr rfl fun v _ ↦ ?_
          have hfib : (univ.filter fun d : Fin n → Ω ↦ (fun j ↦ g (d j)) = v) =
              Fintype.piFinset fun j ↦ univ.filter fun ω ↦ g ω = v j := by
            ext d
            simp [funext_iff]
          rw [sum_const, nsmul_eq_mul, hfib, Fintype.card_piFinset]
          simp [hg]
      _ = _ := (mul_sum _ _ _).symm
  have hcard : Fintype.card Ω = c * Fintype.card V := by
    rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := g) (t := univ)
      fun _ _ ↦ mem_coe.2 (mem_univ _)]
    simp [hg, mul_comm]
  have hc0 : (c : ℝ≥0∞) ^ n ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hc.ne')
  have hct : (c : ℝ≥0∞) ^ n ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top c)
  have hcancel : ∀ a b S : ℝ≥0∞, a ≠ 0 → a ≠ ⊤ → (a * b)⁻¹ * (a * S) = b⁻¹ * S :=
    fun a b S ha hat ↦ by
      rw [ENNReal.mul_inv (Or.inl ha) (Or.inl hat), mul_mul_mul_comm,
        ENNReal.inv_mul_cancel ha hat, one_mul]
  unfold uavg
  rw [hsum, Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, hcard, mul_pow, Nat.cast_mul,
    Nat.cast_pow c n]
  exact hcancel _ _ _ hc0 hct

/-! ## The bound through one parameter set -/

theorem binomMean_cut_nonneg (k0 : ℕ) :
    (0 : ℝ) ≤ ((binomMean signatureLimit (1 / 2 ^ 26) fun m ↦
      if k0 < m then coverProb m else 0 : ℚ) : ℝ) := by
  have h : (0 : ℚ) ≤ binomMean signatureLimit (1 / 2 ^ 26) fun m ↦
      if k0 < m then coverProb m else 0 := by
    unfold binomMean
    refine sum_nonneg fun m _ ↦ mul_nonneg (by positivity) ?_
    show (0 : ℚ) ≤ if k0 < m then coverProb m else 0
    split_ifs
    · exact Quantum.Sphincs.coverProb_nonneg m
    · exact le_rfl
  exact_mod_cast h

/-- **The worst user's price through a rate `λ` and a cut `k0`**: with `E Π loadFactor ≤ e^κ`
and the binomial tail `2^128 · E[coverProb · 1{load > k0}] ≤ β`,
`rhoMaxQ n ≤ (max(log n + κ, 1)/λ + n β) / 2^128`. -/
theorem rhoMaxQ_le_of {lam kap bet : ℝ} {k0 : ℕ} (hlam : 0 < lam)
    (hM : loadSum (fun m ↦ ENNReal.ofReal (loadFactor (lam * 2 ^ 102) k0 m))
        (Fin signatureLimit) (2 ^ indexBits) / ((2 ^ indexBits : ℕ) : ℝ≥0∞) ^ signatureLimit ≤
      ENNReal.ofReal (Real.exp kap))
    (hB : ((binomMean signatureLimit (1 / 2 ^ 26) fun m ↦
      if k0 < m then coverProb m else 0 : ℚ) : ℝ) * 2 ^ 128 ≤ bet) (n : ℕ) :
    rhoMaxQ n ≤ ENNReal.ofReal ((max (Real.log n + kap) 1 / lam + n * bet) / 2 ^ 128) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : ∀ d : Fin 0 → Fin signatureLimit → HashOutput × HashOutput,
        (⨆ i, ENNReal.ofReal (price (starCover (d i)))) = 0 := fun d ↦ by simp
    calc rhoMaxQ 0 = uavg (fun _ : Fin 0 → Fin signatureLimit → HashOutput × HashOutput ↦
          (0 : ℝ≥0∞)) := by unfold rhoMaxQ; simp only [h0]
      _ ≤ 0 := uavg_const_le 0
      _ ≤ _ := zero_le
  set M := max (Real.log n + kap) 1 with hMdef
  set T := (M - 1) / lam with hTdef
  have hT0 : 0 ≤ T := div_nonneg (by linarith [le_max_right (Real.log n + kap) 1]) hlam.le
  set t := T / 2 ^ 128 with htdef
  have ht0 : 0 ≤ t := by positivity
  set s := lam * 2 ^ 102 with hsdef
  have hs : 0 < s := by positivity
  set bm : ℝ := ((binomMean signatureLimit (1 / 2 ^ 26) fun m ↦
    if k0 < m then coverProb m else 0 : ℚ) : ℝ) with hbm
  have hbm0 : 0 ≤ bm := binomMean_cut_nonneg k0
  set F : (Fin signatureLimit → HashOutput × HashOutput) → ℝ≥0∞ := fun d ↦
    ENNReal.ofReal ((price (starCover d) : ℝ) - t) with hF
  -- many users through one
  have hstep1 : rhoMaxQ n ≤ ENNReal.ofReal t + n * uavg F := by
    unfold rhoMaxQ
    calc uavg (fun d : Fin n → Fin signatureLimit → HashOutput × HashOutput ↦
          ⨆ i, ENNReal.ofReal (price (starCover (d i))))
        ≤ uavg (fun d : Fin n → Fin signatureLimit → HashOutput × HashOutput ↦
            ENNReal.ofReal t + ∑ i, F (d i)) := uavg_mono fun d ↦ iSup_le fun i ↦ by
          calc ENNReal.ofReal (price (starCover (d i)))
              ≤ ENNReal.ofReal (t + ((price (starCover (d i)) : ℝ) - t)) :=
                ENNReal.ofReal_le_ofReal (by linarith)
            _ ≤ ENNReal.ofReal t + F (d i) := ENNReal.ofReal_add_le
            _ ≤ _ := add_le_add le_rfl (single_le_sum (f := fun j ↦ F (d j))
                (fun _ _ ↦ zero_le) (mem_univ i))
      _ = uavg (fun _ : Fin n → Fin signatureLimit → HashOutput × HashOutput ↦
            ENNReal.ofReal t) + ∑ i, uavg (fun d : Fin n → Fin signatureLimit →
              HashOutput × HashOutput ↦ F (d i)) := by
          rw [uavg_add, uavg_sum]
      _ ≤ ENNReal.ofReal t + ∑ _i : Fin n, uavg F :=
          add_le_add (uavg_const_le _) (le_of_eq (sum_congr rfl fun i _ ↦ uavg_comp_apply i F))
      _ = ENNReal.ofReal t + n * uavg F := by
          rw [sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- one user
  have hstep2 : uavg F ≤ ENNReal.ofReal (expCoef s t) * ENNReal.ofReal (Real.exp kap) +
      ENNReal.ofReal bm := by
    have hfib := uavg_comp_fiber pairView (2 ^ 246) (by positivity) card_fiber_pairView
      signatureLimit fun v ↦ ENNReal.ofReal ((price (revealed v) : ℝ) - t)
    have hFe : F = fun d : Fin signatureLimit → HashOutput × HashOutput ↦
        ENNReal.ofReal ((price (revealed fun j ↦ pairView (d j)) : ℝ) - t) := rfl
    rw [hFe, hfib]
    refine (uavg_price_sub_le signatureLimit k0 hs t).trans ?_
    gcongr
  -- the arithmetic
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have e1 : s * 2 ^ 26 * t = M - 1 := by
    rw [hsdef, htdef, hTdef]
    field_simp
  have e2 : s * 2 ^ 26 = lam * 2 ^ 128 := by rw [hsdef]; ring
  have hA : n * (expCoef s t * Real.exp kap) ≤ 1 / (lam * 2 ^ 128) := by
    have hx : Real.exp (-(M - 1)) * Real.exp kap ≤ Real.exp 1 / n := by
      rw [← Real.exp_add, ← Real.exp_log hn', ← Real.exp_sub]
      exact Real.exp_le_exp.2 (by linarith [le_max_left (Real.log n + kap) 1])
    rw [expCoef, e1, e2]
    calc (n : ℝ) * (Real.exp (-(M - 1)) / (Real.exp 1 * (lam * 2 ^ 128)) * Real.exp kap)
        = n * (Real.exp (-(M - 1)) * Real.exp kap) / (Real.exp 1 * (lam * 2 ^ 128)) := by ring
      _ ≤ n * (Real.exp 1 / n) / (Real.exp 1 * (lam * 2 ^ 128)) := by gcongr
      _ = 1 / (lam * 2 ^ 128) := by field_simp
  have hB' : n * bm ≤ n * bet / 2 ^ 128 := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (by rw [le_div_iff₀ (by positivity)]; exact hB) hn'.le
  have hreal : t + n * (expCoef s t * Real.exp kap + bm) ≤ (M / lam + n * bet) / 2 ^ 128 := by
    have ht' : t = (M - 1) / lam / 2 ^ 128 := rfl
    calc t + n * (expCoef s t * Real.exp kap + bm)
        = t + n * (expCoef s t * Real.exp kap) + n * bm := by ring
      _ ≤ t + 1 / (lam * 2 ^ 128) + n * bet / 2 ^ 128 := by linarith
      _ = _ := by rw [ht']; field_simp; ring
  have hE0 : 0 ≤ expCoef s t * Real.exp kap :=
    mul_nonneg (expCoef_nonneg hs.le t) (Real.exp_pos _).le
  calc rhoMaxQ n ≤ ENNReal.ofReal t + n * uavg F := hstep1
    _ ≤ ENNReal.ofReal t + n * (ENNReal.ofReal (expCoef s t) * ENNReal.ofReal (Real.exp kap) +
          ENNReal.ofReal bm) := by gcongr
    _ = ENNReal.ofReal (t + n * (expCoef s t * Real.exp kap + bm)) := by
        rw [← ENNReal.ofReal_mul (expCoef_nonneg hs.le t), ← ENNReal.ofReal_add hE0 hbm0,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ← ENNReal.ofReal_add ht0 (mul_nonneg (Nat.cast_nonneg _) (add_nonneg hE0 hbm0))]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hreal

/-! ## The certified bound -/

/-- The bound of one parameter set: `max(log n + κ, 1)/λ + n β` (units `2^-128`). -/
noncomputable def covPiece (P : CovParam) (n : ℕ) : ℝ :=
  max (Real.log n + P.kap) 1 / P.lam + n * P.bet

theorem CovParam.lam_pos {P : CovParam} (hP : P.Cert) : (0 : ℝ) < P.lam := by
  have : (0 : ℝ) < P.lamN := Nat.cast_pos.2 hP.1
  rw [CovParam.lam]
  push_cast
  positivity

theorem CovParam.bet_nonneg (P : CovParam) : (0 : ℝ) ≤ P.bet := by
  rw [CovParam.bet]
  push_cast
  positivity

theorem rhoMaxQ_le_covPiece (P : CovParam) (hP : P.Cert) (n : ℕ) :
    rhoMaxQ n ≤ ENNReal.ofReal (covPiece P n / 2 ^ 128) :=
  rhoMaxQ_le_of (CovParam.lam_pos hP) (loadMean_le P hP) (binomTail_le P hP) n

/-- The union bound: `E max_i price_i ≤ n · E price ≤ n · rhoCov / 2^128`. -/
theorem rhoMaxQ_le_mul (n : ℕ) : rhoMaxQ n ≤ ENNReal.ofReal (n * rhoCov / 2 ^ 128) := by
  unfold rhoMaxQ
  calc uavg (fun d : Fin n → Fin signatureLimit → HashOutput × HashOutput ↦
        ⨆ i, ENNReal.ofReal (price (starCover (d i))))
      ≤ uavg (fun d : Fin n → Fin signatureLimit → HashOutput × HashOutput ↦
          ∑ i, ENNReal.ofReal (price (starCover (d i)))) := uavg_mono fun d ↦ iSup_le fun i ↦
        single_le_sum (f := fun j ↦ ENNReal.ofReal (price (starCover (d j))))
          (fun _ _ ↦ zero_le) (mem_univ i)
    _ = ∑ _i : Fin n, uavg (fun d : Fin signatureLimit → HashOutput × HashOutput ↦
          ENNReal.ofReal (price (starCover d))) := by
        rw [uavg_sum]
        exact sum_congr rfl fun i _ ↦
          uavg_comp_apply i fun d ↦ ENNReal.ofReal (price (starCover d))
    _ ≤ ∑ _i : Fin n, ENNReal.ofReal (rhoCov / 2 ^ 128) :=
        sum_le_sum fun _ _ ↦ uavg_price_starCover_le
    _ = ENNReal.ofReal (n * rhoCov / 2 ^ 128) := by
        rw [sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _), mul_div_assoc]

/-- **The certified worst-user price** (units `2^-128`): the least of `n · rhoCov` and the
pieces of `covTable`. -/
noncomputable def rhoMaxR (n : ℕ) : ℝ :=
  covTable.foldr (fun P r ↦ min (covPiece P n) r) (n * rhoCov)

private theorem rhoMaxQ_le_foldr (n : ℕ) :
    ∀ l : List CovParam, (∀ P ∈ l, P.Cert) →
      rhoMaxQ n ≤ ENNReal.ofReal (l.foldr (fun P r ↦ min (covPiece P n) r) (n * rhoCov) / 2 ^ 128)
  | [], _ => rhoMaxQ_le_mul n
  | P :: l, h => by
    rw [List.foldr_cons]
    rcases min_choice (covPiece P n) (l.foldr (fun P r ↦ min (covPiece P n) r) (n * rhoCov))
      with he | he <;> rw [he]
    · exact rhoMaxQ_le_covPiece P (h P List.mem_cons_self) n
    · exact rhoMaxQ_le_foldr n l fun Q hQ ↦ h Q (List.mem_cons_of_mem _ hQ)

/-- **The worst user's price is at most `rhoMaxR n / 2^128`.** -/
theorem rhoMaxQ_le (n : ℕ) : rhoMaxQ n ≤ ENNReal.ofReal (rhoMaxR n / 2 ^ 128) :=
  rhoMaxQ_le_foldr n covTable covTable_cert

theorem log_natCast_mono : Monotone fun n : ℕ ↦ Real.log n := fun a b h ↦ by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simpa using Real.log_natCast_nonneg b
  · exact Real.log_le_log (Nat.cast_pos.2 ha) (Nat.cast_le.2 h)

theorem covPiece_mono {P : CovParam} (hP : P.Cert) : Monotone (covPiece P) := fun a b h ↦ by
  unfold covPiece
  have h1 := log_natCast_mono h
  have h2 : (a : ℝ) ≤ b := Nat.cast_le.2 h
  have hl := CovParam.lam_pos hP
  have hb := P.bet_nonneg
  gcongr

private theorem rhoMaxR_mono_foldr :
    ∀ l : List CovParam, (∀ P ∈ l, P.Cert) →
      Monotone fun n : ℕ ↦ l.foldr (fun P r ↦ min (covPiece P n) r) ((n : ℝ) * rhoCov)
  | [], _ => fun a b h ↦ by
    have : (0 : ℝ) ≤ rhoCov := by norm_num [rhoCov]
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.2 h) this
  | P :: l, hl => fun a b h ↦ by
    simp only [List.foldr_cons]
    exact min_le_min (covPiece_mono (hl P List.mem_cons_self) h)
      (rhoMaxR_mono_foldr l (fun Q hQ ↦ hl Q (List.mem_cons_of_mem _ hQ)) h)

/-- `rhoMaxR` is monotone in the number of users. -/
theorem rhoMaxR_mono : Monotone rhoMaxR := rhoMaxR_mono_foldr covTable covTable_cert

private theorem foldr_le_of_mem (n : ℕ) (P : CovParam) :
    ∀ l : List CovParam, P ∈ l →
      l.foldr (fun P r ↦ min (covPiece P n) r) ((n : ℝ) * rhoCov) ≤ covPiece P n
  | [], h => absurd h List.not_mem_nil
  | Q :: l, h => by
    rw [List.foldr_cons]
    rcases List.mem_cons.1 h with rfl | h'
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (foldr_le_of_mem n P l h')

theorem rhoMaxR_le_covPiece {P : CovParam} (hP : P ∈ covTable) (n : ℕ) :
    rhoMaxR n ≤ covPiece P n :=
  foldr_le_of_mem n P covTable hP

theorem rhoMaxR_le_mul (n : ℕ) : rhoMaxR n ≤ n * rhoCov := by
  unfold rhoMaxR
  induction covTable with
  | nil => exact le_rfl
  | cons P l ih => exact (min_le_right _ _).trans ih

theorem rhoMaxR_one : rhoMaxR 1 ≤ rhoCov := by
  simpa using rhoMaxR_le_mul 1

/-- A piece at `n = 2^e` through `log 2 < 0.6931471808`. -/
theorem covPiece_two_pow_le {P : CovParam} (hP : P.Cert) (e : ℕ)
    (h1 : 1 ≤ e * 0.6931471808 + (P.kap : ℝ)) :
    covPiece P (2 ^ e) ≤ (e * 0.6931471808 + P.kap) / P.lam + 2 ^ e * P.bet := by
  have hlog : Real.log ((2 ^ e : ℕ) : ℝ) ≤ e * 0.6931471808 := by
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
    exact mul_le_mul_of_nonneg_left Real.log_two_lt_d9.le (Nat.cast_nonneg e)
  unfold covPiece
  rw [Nat.cast_pow, Nat.cast_ofNat] at hlog ⊢
  gcongr
  · exact (CovParam.lam_pos hP).le
  · exact max_le (by linarith) h1

theorem rhoMaxR_two_pow_10 : rhoMaxR (2 ^ 10) ≤ 2.31 := by
  have hm : (⟨16246581, 20, 52, 25489323, 20, 9636353, 35⟩ : CovParam) ∈ covTable := by
    simp [covTable]
  have hc := covTable_cert _ hm
  refine (rhoMaxR_le_covPiece hm _).trans ((covPiece_two_pow_le hc 10 ?_).trans ?_) <;>
    norm_num [CovParam.kap, CovParam.lam, CovParam.bet]

theorem rhoMaxR_two_pow_20 : rhoMaxR (2 ^ 20) ≤ 10.95 := by
  have hm : (⟨1199683, 19, 58, 4689321, 20, 12292235, 42⟩ : CovParam) ∈ covTable := by
    simp [covTable]
  have hc := covTable_cert _ hm
  refine (rhoMaxR_le_covPiece hm _).trans ((covPiece_two_pow_le hc 20 ?_).trans ?_) <;>
    norm_num [CovParam.kap, CovParam.lam, CovParam.bet]

theorem rhoMaxR_two_pow_32 : rhoMaxR (2 ^ 32) ≤ 116.4 := by
  have hm : (⟨256115, 20, 65, 1464823, 20, 10395917, 51⟩ : CovParam) ∈ covTable := by
    simp [covTable]
  have hc := covTable_cert _ hm
  refine (rhoMaxR_le_covPiece hm _).trans ((covPiece_two_pow_le hc 32 ?_).trans ?_) <;>
    norm_num [CovParam.kap, CovParam.lam, CovParam.bet]

theorem rhoMaxR_two_pow_40 : rhoMaxR (2 ^ 40) ≤ 483.3 := by
  have hm : (⟨37713, 19, 69, 1082085, 20, 21865269, 58⟩ : CovParam) ∈ covTable := by
    simp [covTable]
  have hc := covTable_cert _ hm
  refine (rhoMaxR_le_covPiece hm _).trans ((covPiece_two_pow_le hc 40 ?_).trans ?_) <;>
    norm_num [CovParam.kap, CovParam.lam, CovParam.bet]

theorem rhoMaxR_two_pow_48 : rhoMaxR (2 ^ 48) ≤ 1791 := by
  have hm : (⟨23505, 20, 73, 1086867, 20, 17058089, 64⟩ : CovParam) ∈ covTable := by
    simp [covTable]
  have hc := covTable_cert _ hm
  refine (rhoMaxR_le_covPiece hm _).trans ((covPiece_two_pow_le hc 48 ?_).trans ?_) <;>
    norm_num [CovParam.kap, CovParam.lam, CovParam.bet]

theorem rhoMaxR_two_pow_56 : rhoMaxR (2 ^ 56) ≤ 6059 := by
  have hm : (⟨3835, 19, 77, 132177, 17, 10060851, 70⟩ : CovParam) ∈ covTable := by
    simp [covTable]
  have hc := covTable_cert _ hm
  refine (rhoMaxR_le_covPiece hm _).trans ((covPiece_two_pow_le hc 56 ?_).trans ?_) <;>
    norm_num [CovParam.kap, CovParam.lam, CovParam.bet]

theorem rhoMaxR_two_pow_64 : rhoMaxR (2 ^ 64) ≤ 17861 := by
  have hm : (⟨851, 18, 80, 897285, 20, 32207519, 77⟩ : CovParam) ∈ covTable := by
    simp [covTable]
  have hc := covTable_cert _ hm
  refine (rhoMaxR_le_covPiece hm _).trans ((covPiece_two_pow_le hc 64 ?_).trans ?_) <;>
    norm_num [CovParam.kap, CovParam.lam, CovParam.bet]

end Quantum.Qrom.Sphincs.Multi

end
