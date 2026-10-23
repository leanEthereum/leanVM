/-
  LeanVM.Protocol.Whir.Params.Check

  Certificates for the codes of a WHIR ladder: a level's Johnson slack as a dyadic rational and a
  dyadic bracket of `√ρ₋`, the natural-number bounds they give on the threshold, the list size,
  and ArkLib's exception count, and a Boolean check of a whole ladder whose success implies
  `LadderArith` and `whirEps ≤ 2^-B`.
-/

module

public import LeanVM.Protocol.Whir.Sound.Spec

/-!
# Checked level codes

The escape bound `whirEps codes config` of `LeanVM.Protocol.Whir.Sound.Spec` is a maximum of
group escapes built from three noncomputable naturals per level: the Johnson threshold
`thr = ⌈(√ρ₋ + η) n⌉`, the list bound `listMax = ⌊1/(2η√ρ₋)⌋` and ArkLib's exception count
`mcaMax = ⌊johnsonExceptionCount n D thr η⌋`. A `Cert` fixes a level's `κ`, `R`, the slack
`η = e / 2^22` and a bracket `s / 2^40 ≤ √ρ₋ ≤ (s + 1) / 2^40`, and computes natural bounds
`thrLo ≤ thr ≤ thrHi`, `listMax ≤ listHi`, `mcaMax ≤ excHi` from them by rounding the bracket's
ends outward (`Cert.OK` records the rounding inequalities, each a `Nat` comparison).

* `Cert.toCode`: the `LevelCode` of a checked certificate; `codesOf`: a code per level, the
  certificate's when it checks.
* `Cert.thr_le`, `Cert.thrLo_le`, `Cert.listMax_le`, `Cert.mcaMax_le`: the four bounds.
* `chkLevels B μ cs`: a Boolean check of a ladder against certificates: the ladder arithmetic,
  and every group escape at most `2^-B` as a `Nat` inequality.
* `chkLevels_sound`: **a checked ladder satisfies `LadderArith` and `levelEps ≤ 2^-B`.**
-/

namespace LeanVM.Protocol.Whir.Params

open LeanVM.Parameters LeanVM.Protocol.Whir.Sound ReedSolomon.HiddenDerivative

@[expose] public section

/-- The denominator of the bracket of `√ρ₋`. -/
abbrev sqrtDen : ℕ := 2 ^ 40

/-- The denominator of the Johnson slack. -/
abbrev slackDen : ℕ := 2 ^ 22

/-- A level's certificate: message variables `κ`, rate exponent `R`, Johnson slack
`η = e / 2^22`, and the bracket `s / 2^40 ≤ √ρ₋ ≤ (s + 1) / 2^40`. -/
structure Cert where
  /-- The message variables. -/
  κ : ℕ
  /-- The log inverse rate. -/
  R : ℕ
  /-- The numerator of the slack `η = e / 2^22`. -/
  e : ℕ
  /-- The numerator of the lower end of the bracket of `√ρ₋`. -/
  s : ℕ

namespace Cert

variable (c : Cert)

/-- The block length `2^(κ+R)`. -/
def n : ℕ := 2 ^ (c.κ + c.R)

/-- The degree bound `2^κ − 1`. -/
def D : ℕ := 2 ^ c.κ - 1

/-- `⌈((s + 1)/2^40 + η) n⌉`, above the threshold. -/
def thrHi : ℕ :=
  (((c.s + 1) * slackDen + c.e * sqrtDen) * c.n + sqrtDen * slackDen - 1) / (sqrtDen * slackDen)

/-- `⌈(s/2^40 + η) n⌉`, below the threshold. -/
def thrLo : ℕ :=
  ((c.s * slackDen + c.e * sqrtDen) * c.n + sqrtDen * slackDen - 1) / (sqrtDen * slackDen)

/-- `⌊1/(2η s/2^40)⌋`, above the list bound. -/
def listHi : ℕ := sqrtDen * slackDen / (2 * c.e * c.s)

/-- `max ⌈((s + 1)/2^40)/(2η)⌉ 3`, above ArkLib's multiplicity `johnsonM`. -/
def mHi : ℕ := max (((c.s + 1) * slackDen + 2 * c.e * sqrtDen - 1) / (2 * c.e * sqrtDen)) 3

/-- Above ArkLib's `johnsonMu = ⌈t/√ρ₋⌉ − 1`, `t = johnsonM + 1/2`. -/
def muHi : ℕ := ((2 * c.mHi + 1) * sqrtDen + 2 * c.s - 1) / (2 * c.s) - 1

/-- Above ArkLib's `johnsonH = ⌈t²/(3ρ₋)⌉ − 1`. -/
def hHi : ℕ := ((2 * c.mHi + 1) ^ 2 * c.n + 12 * c.D - 1) / (12 * c.D) - 1

/-- The numerator of the exception count at the bounds, over `thrLo − D`. -/
def excNum : ℕ :=
  ((2 * c.muHi - 1) * c.hHi + (c.n - c.D - 1) * c.muHi) * (c.thrLo - c.D) +
    (c.n - c.D) * (c.hHi + c.muHi + 4 * c.D * c.muHi * c.hHi)

/-- `⌊excNum / (thrLo − D)⌋`, above ArkLib's exception count. -/
def excHi : ℕ := c.excNum / (c.thrLo - c.D)

/-- **A checked certificate**: the code's side conditions, the bracket of `√ρ₋`, the agreement
fraction at most `1`, and the rounding inequalities of the computed bounds. -/
structure OK : Prop where
  /-- The domain fits in `K`. -/
  h64 : c.κ + c.R ≤ 64
  /-- At least one message variable. -/
  hκ : 1 ≤ c.κ
  /-- Rate at most `1/2`. -/
  hR : 1 ≤ c.R
  /-- Positive slack. -/
  he : 0 < c.e
  /-- Positive lower end of the bracket. -/
  hs : 0 < c.s
  /-- `s/2^40 ≤ √(D/n)`. -/
  sqrtLo : c.s ^ 2 * c.n ≤ c.D * sqrtDen ^ 2
  /-- `√(D/n) ≤ (s+1)/2^40`. -/
  sqrtHi : c.D * sqrtDen ^ 2 ≤ (c.s + 1) ^ 2 * c.n
  /-- The agreement fraction's upper end is at most `1`. -/
  agr : (c.s + 1) * slackDen + c.e * sqrtDen ≤ sqrtDen * slackDen
  /-- `thrHi` rounds the threshold's upper end up. -/
  thrHi : ((c.s + 1) * slackDen + c.e * sqrtDen) * c.n ≤ c.thrHi * (sqrtDen * slackDen)
  /-- `thrLo − 1` is below the threshold's lower end. -/
  thrLo : (c.thrLo - 1) * (sqrtDen * slackDen) < (c.s * slackDen + c.e * sqrtDen) * c.n
  /-- `thrLo` is positive. -/
  thrLo_pos : 1 ≤ c.thrLo
  /-- `listHi + 1` exceeds the list bound's upper end. -/
  listHi : sqrtDen * slackDen < (c.listHi + 1) * (2 * c.e * c.s)
  /-- `mHi` is above the multiplicity's ceiling argument. -/
  mHi : (c.s + 1) * slackDen ≤ c.mHi * (2 * c.e * sqrtDen)
  /-- `mHi` is at least `3`. -/
  mHi_ge : 3 ≤ c.mHi
  /-- `muHi + 1` is above `t/√ρ₋`. -/
  muHi : (2 * c.mHi + 1) * sqrtDen ≤ 2 * (c.muHi + 1) * c.s
  /-- `hHi + 1` is above `t²/(3ρ₋)`. -/
  hHi : (2 * c.mHi + 1) ^ 2 * c.n ≤ 12 * c.D * (c.hHi + 1)
  /-- The threshold's lower bound exceeds the degree. -/
  D_lt : c.D < c.thrLo
  /-- `excHi + 1` exceeds the exception count's bound. -/
  excHi : c.excNum < (c.excHi + 1) * (c.thrLo - c.D)

/-- `OK` as a conjunction, for its decision procedure. -/
theorem ok_iff : c.OK ↔
    c.κ + c.R ≤ 64 ∧ 1 ≤ c.κ ∧ 1 ≤ c.R ∧ 0 < c.e ∧ 0 < c.s ∧
      c.s ^ 2 * c.n ≤ c.D * sqrtDen ^ 2 ∧ c.D * sqrtDen ^ 2 ≤ (c.s + 1) ^ 2 * c.n ∧
      (c.s + 1) * slackDen + c.e * sqrtDen ≤ sqrtDen * slackDen ∧
      ((c.s + 1) * slackDen + c.e * sqrtDen) * c.n ≤ c.thrHi * (sqrtDen * slackDen) ∧
      (c.thrLo - 1) * (sqrtDen * slackDen) < (c.s * slackDen + c.e * sqrtDen) * c.n ∧
      1 ≤ c.thrLo ∧ sqrtDen * slackDen < (c.listHi + 1) * (2 * c.e * c.s) ∧
      (c.s + 1) * slackDen ≤ c.mHi * (2 * c.e * sqrtDen) ∧ 3 ≤ c.mHi ∧
      (2 * c.mHi + 1) * sqrtDen ≤ 2 * (c.muHi + 1) * c.s ∧
      (2 * c.mHi + 1) ^ 2 * c.n ≤ 12 * c.D * (c.hHi + 1) ∧ c.D < c.thrLo ∧
      c.excNum < (c.excHi + 1) * (c.thrLo - c.D) :=
  ⟨fun ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18⟩ ↦
    ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18⟩,
   fun ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18⟩ ↦
    ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18⟩⟩

/-- `OK` is decided by its conjunction. -/
instance : Decidable c.OK := decidable_of_iff _ c.ok_iff.symm

/-! ## The bracket in `ℝ` -/

variable {c}

/-- The block length is positive. -/
theorem n_pos : 0 < c.n := Nat.two_pow_pos _

/-- The bracket of `√ρ₋`. -/
theorem sqrt_mem (h : c.OK) :
    (c.s : ℝ) / sqrtDen ≤ √(johnsonRhoMinus c.n c.D) ∧
      √(johnsonRhoMinus c.n c.D) ≤ ((c.s + 1 : ℕ) : ℝ) / sqrtDen := by
  have hlo := h.sqrtLo
  have hhi := h.sqrtHi
  have hn : (0 : ℝ) < c.n := by exact_mod_cast n_pos
  have hS : (0 : ℝ) < sqrtDen := by positivity
  rw [johnsonRhoMinus]
  constructor
  · refine Real.le_sqrt_of_sq_le ?_
    rw [div_pow, div_le_div_iff₀ (by positivity) hn]
    exact_mod_cast hlo
  · rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    rw [div_pow, div_le_div_iff₀ hn (by positivity)]
    exact_mod_cast hhi

/-- The slack as a real. -/
noncomputable def eta : ℝ := (c.e : ℝ) / slackDen

/-- The slack is positive. -/
theorem eta_pos (h : c.OK) : 0 < c.eta := by
  have := h.he
  unfold eta
  positivity

/-- The agreement fraction is below `((s + 1)·2^22 + e·2^40) / 2^62`. -/
theorem agreement_le (h : c.OK) :
    johnsonAgreement c.n c.D c.eta ≤
      (((c.s + 1) * slackDen + c.e * sqrtDen : ℕ) : ℝ) / (sqrtDen * slackDen : ℕ) := by
  rw [johnsonAgreement]
  have h1 := (sqrt_mem h).2
  have : ((c.s + 1 : ℕ) : ℝ) / sqrtDen + c.eta =
      (((c.s + 1) * slackDen + c.e * sqrtDen : ℕ) : ℝ) / (sqrtDen * slackDen : ℕ) := by
    unfold eta
    push_cast
    field_simp
  linarith

/-- The agreement fraction is above `(s·2^22 + e·2^40) / 2^62`. -/
theorem agreement_ge (h : c.OK) :
    (((c.s * slackDen + c.e * sqrtDen : ℕ) : ℝ) / (sqrtDen * slackDen : ℕ)) ≤
      johnsonAgreement c.n c.D c.eta := by
  rw [johnsonAgreement]
  have h1 := (sqrt_mem h).1
  have : (c.s : ℝ) / sqrtDen + c.eta =
      (((c.s * slackDen + c.e * sqrtDen : ℕ) : ℝ) / (sqrtDen * slackDen : ℕ)) := by
    unfold eta
    push_cast
    field_simp
  linarith

/-- The agreement fraction is at most `1` (ArkLib's Johnson range). -/
theorem agreement_le_one (h : c.OK) :
    johnsonAgreement (2 ^ (c.κ + c.R)) (2 ^ c.κ - 1) c.eta ≤ 1 :=
  (agreement_le h).trans (by
    rw [div_le_one (by positivity)]
    exact_mod_cast h.agr)

/-- The level code of a checked certificate. -/
noncomputable def toCode (h : c.OK) : LevelCode :=
  ⟨c.κ, c.R, c.eta, h.h64, h.hκ, h.hR, eta_pos h, agreement_le_one h⟩

/-! ## The four bounds -/

/-- **The threshold is at most `thrHi`.** -/
theorem thr_le (h : c.OK) : (c.toCode h).thr ≤ c.thrHi := by
  have hb := h.thrHi
  refine Nat.ceil_le.mpr ?_
  change johnsonAgreement c.n c.D c.eta * c.n ≤ _
  have hn : (0 : ℝ) ≤ c.n := by positivity
  refine (mul_le_mul_of_nonneg_right (agreement_le h) hn).trans ?_
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  exact_mod_cast hb

/-- **The threshold is at least `thrLo`.** -/
theorem thrLo_le (h : c.OK) : c.thrLo ≤ (c.toCode h).thr := by
  have hb := h.thrLo
  have h1 := h.thrLo_pos
  have hlt : c.thrLo - 1 < (c.toCode h).thr := by
    refine Nat.lt_ceil.mpr ?_
    change ((c.thrLo - 1 : ℕ) : ℝ) < johnsonAgreement c.n c.D c.eta * c.n
    have hn : (0 : ℝ) ≤ c.n := by positivity
    refine lt_of_lt_of_le ?_ (mul_le_mul_of_nonneg_right (agreement_ge h) hn)
    rw [div_mul_eq_mul_div, lt_div_iff₀ (by positivity)]
    exact_mod_cast hb
  omega

/-- **The list bound is at most `listHi`.** -/
theorem listMax_le (h : c.OK) : (c.toCode h).listMax ≤ c.listHi := by
  have hs := h.hs
  have hb := h.listHi
  refine Nat.lt_succ_iff.mp ((Nat.floor_lt' (Nat.succ_ne_zero _)).mpr ?_)
  change 1 / (2 * c.eta * √(johnsonRhoMinus c.n c.D)) < _
  have hlo := (sqrt_mem h).1
  have hpos : (0 : ℝ) < 2 * c.eta * ((c.s : ℝ) / sqrtDen) := by
    have := eta_pos h
    positivity
  refine lt_of_le_of_lt (one_div_le_one_div_of_le hpos
    (mul_le_mul_of_nonneg_left hlo (by have := eta_pos h; positivity))) ?_
  rw [div_lt_iff₀ hpos]
  unfold eta
  have : ((c.listHi.succ : ℕ) : ℝ) * (2 * ((c.e : ℝ) / slackDen) * ((c.s : ℝ) / sqrtDen)) =
      ((c.listHi + 1) * (2 * c.e * c.s) : ℕ) / (sqrtDen * slackDen : ℕ) := by
    push_cast
    field_simp
  rw [this, lt_div_iff₀ (by positivity), one_mul]
  exact_mod_cast hb

/-- ArkLib's multiplicity is at most `mHi`. -/
theorem johnsonM_le (h : c.OK) : johnsonM c.n c.D c.eta ≤ c.mHi := by
  have hb := h.mHi
  have h3 := h.mHi_ge
  refine max_le (Nat.ceil_le.mpr ?_) h3
  have hhi := (sqrt_mem h).2
  have hη := eta_pos h
  rw [div_le_iff₀ (by positivity)]
  refine hhi.trans ?_
  unfold eta
  rw [div_le_iff₀ (by positivity)]
  have : (c.mHi : ℝ) * (2 * ((c.e : ℝ) / slackDen)) * sqrtDen =
      ((c.mHi * (2 * c.e * sqrtDen) : ℕ) : ℝ) / slackDen := by
    push_cast
    field_simp
  rw [this, le_div_iff₀ (by positivity)]
  exact_mod_cast hb

/-- ArkLib's degree bound `johnsonMu` is at most `muHi`. -/
theorem johnsonMu_le (h : c.OK) : johnsonMu c.n c.D c.eta ≤ c.muHi := by
  have hs := h.hs
  have hb := h.muHi
  have hm := johnsonM_le h
  have hlo := (sqrt_mem h).1
  have hlo0 : (0 : ℝ) < (c.s : ℝ) / sqrtDen := by positivity
  suffices hc : ⌈johnsonT c.n c.D c.eta / √(johnsonRhoMinus c.n c.D)⌉₊ ≤ c.muHi + 1 by
    unfold johnsonMu
    omega
  refine Nat.ceil_le.mpr ?_
  have ht : johnsonT c.n c.D c.eta ≤ ((2 * c.mHi + 1 : ℕ) : ℝ) / 2 := by
    unfold johnsonT
    have : (johnsonM c.n c.D c.eta : ℝ) ≤ c.mHi := by exact_mod_cast hm
    push_cast
    linarith
  have ht0 : 0 ≤ johnsonT c.n c.D c.eta := by unfold johnsonT; positivity
  calc johnsonT c.n c.D c.eta / √(johnsonRhoMinus c.n c.D)
      ≤ (((2 * c.mHi + 1 : ℕ) : ℝ) / 2) / ((c.s : ℝ) / sqrtDen) :=
        div_le_div₀ (by positivity) ht hlo0 hlo
    _ ≤ _ := by
        rw [div_div_eq_mul_div, div_le_iff₀ (by positivity), div_mul_eq_mul_div,
          div_le_iff₀ (by positivity)]
        have : ((c.muHi + 1 : ℕ) : ℝ) * c.s * 2 = ((2 * (c.muHi + 1) * c.s : ℕ) : ℝ) := by
          push_cast; ring
        push_cast at this ⊢
        rw [this]
        exact_mod_cast hb

/-- ArkLib's height `johnsonH` is at most `hHi`. -/
theorem johnsonH_le (h : c.OK) : johnsonH c.n c.D c.eta ≤ c.hHi := by
  have hb := h.hHi
  have hm := johnsonM_le h
  have hD : 1 ≤ c.D := (c.toCode h).one_le_D
  have hn := n_pos (c := c)
  suffices hc : ⌈johnsonT c.n c.D c.eta ^ 2 / (3 * johnsonRhoMinus c.n c.D)⌉₊ ≤ c.hHi + 1 by
    unfold johnsonH
    omega
  refine Nat.ceil_le.mpr ?_
  have ht : johnsonT c.n c.D c.eta ≤ ((2 * c.mHi + 1 : ℕ) : ℝ) / 2 := by
    unfold johnsonT
    have : (johnsonM c.n c.D c.eta : ℝ) ≤ c.mHi := by exact_mod_cast hm
    push_cast
    linarith
  have ht0 : 0 ≤ johnsonT c.n c.D c.eta := by unfold johnsonT; positivity
  have hD' : (0 : ℝ) < c.D := by exact_mod_cast hD
  have hn' : (0 : ℝ) < c.n := by exact_mod_cast hn
  rw [johnsonRhoMinus, div_le_iff₀ (by positivity)]
  calc johnsonT c.n c.D c.eta ^ 2 ≤ (((2 * c.mHi + 1 : ℕ) : ℝ) / 2) ^ 2 := by gcongr
    _ ≤ _ := by
        rw [div_pow, div_le_iff₀ (by positivity)]
        have hb' : (((2 * c.mHi + 1) ^ 2 * c.n : ℕ) : ℝ) ≤ ((12 * c.D * (c.hHi + 1) : ℕ) : ℝ) := by
          exact_mod_cast hb
        push_cast at hb'
        have : ((c.hHi + 1 : ℕ) : ℝ) * (3 * ((c.D : ℝ) / c.n)) * 2 ^ 2 =
            (12 * c.D * (c.hHi + 1)) / c.n := by
          push_cast
          field_simp
          ring
        rw [this, le_div_iff₀ hn']
        push_cast
        linarith

/-- **The exception count is at most `excHi`.** -/
theorem mcaMax_le (h : c.OK) : (c.toCode h).mcaMax ≤ c.excHi := by
  have hDA := h.D_lt
  have hb := h.excHi
  have hlo := thrLo_le h
  refine Nat.lt_succ_iff.mp ((Nat.floor_lt' (Nat.succ_ne_zero _)).mpr ?_)
  change johnsonExceptionCount c.n c.D (c.toCode h).thr c.eta < _
  have hmu := johnsonMu_le h
  have hh := johnsonH_le h
  have hθ : johnsonTheta c.n c.D (c.toCode h).thr ≤
      ((c.n - c.D : ℕ) : ℝ) / (c.thrLo - c.D : ℕ) := by
    unfold johnsonTheta
    gcongr
    exact_mod_cast Nat.sub_pos_of_lt hDA
  have hθ0 : 0 ≤ johnsonTheta c.n c.D (c.toCode h).thr := by unfold johnsonTheta; positivity
  have hpos : (0 : ℝ) < (c.thrLo - c.D : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hDA
  calc johnsonExceptionCount c.n c.D (c.toCode h).thr c.eta
      ≤ ((2 * c.muHi - 1 : ℕ) : ℝ) * c.hHi +
          ((c.n - c.D : ℕ) : ℝ) / (c.thrLo - c.D : ℕ) *
            (c.hHi + c.muHi + 4 * c.D * c.muHi * c.hHi) + ((c.n - c.D - 1 : ℕ) : ℝ) * c.muHi := by
        unfold johnsonExceptionCount
        simp only
        gcongr
    _ = (c.excNum : ℝ) / (c.thrLo - c.D : ℕ) := by
        rw [eq_div_iff hpos.ne', excNum]
        push_cast
        field_simp
        ring
    _ < _ := by
        rw [div_lt_iff₀ hpos]
        exact_mod_cast hb

end Cert

/-! ## Codes from certificates -/

/-- A checked certificate: `κ = 1`, `R = 1`, `η = 1/4`, `√ρ₋ = 1/2`. -/
def defaultCert : Cert := ⟨1, 1, 2 ^ 20, 2 ^ 39⟩

/-- The default certificate checks. -/
theorem defaultCert_ok : defaultCert.OK := by decide +kernel

/-- The code of a certificate: its own when it checks, the default's otherwise. -/
noncomputable def mkCode (c : Cert) : LevelCode :=
  if h : c.OK then c.toCode h else defaultCert.toCode defaultCert_ok

/-- A checked certificate's code is its own. -/
theorem mkCode_eq {c : Cert} (h : c.OK) : mkCode c = c.toCode h := by
  simp only [mkCode, h, ↓reduceDIte]

/-- A code per level from a certificate per level. -/
noncomputable def codesOf (cs : ℕ → Cert) (i : ℕ) : LevelCode := mkCode (cs i)

/-! ## Escape bounds in `ℝ≥0∞` -/

theorem card_E_cast : (Fintype.card E : ENNReal) = ((2 ^ 192 : ℕ) : ENNReal) := by
  rw [LeanVM.Protocol.card_E]

/-- `a / d ≤ 2^-B` from `a·2^B ≤ d`. -/
theorem nat_div_le {a d : ℕ} (B : ℕ) (h : a * 2 ^ B ≤ d) :
    (a : ENNReal) / d ≤ (2 : ENNReal)⁻¹ ^ B := by
  refine ENNReal.div_le_of_le_mul ?_
  have h2 : (2 : ENNReal) ^ B * (2 : ENNReal)⁻¹ ^ B = 1 := by
    rw [← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow]
  calc (a : ENNReal) = (a : ENNReal) * 2 ^ B * (2 : ENNReal)⁻¹ ^ B := by
        rw [mul_assoc, h2, mul_one]
    _ ≤ (d : ENNReal) * (2 : ENNReal)⁻¹ ^ B := by
        gcongr
        exact_mod_cast h
    _ = _ := mul_comm _ _

/-- Two fractions over a common denominator. -/
theorem nat_div_add_div {a b q m : ℕ} (hq : 0 < q) (hm : 0 < m) :
    (a : ENNReal) / q + (b : ENNReal) / m = ((a * m + b * q : ℕ) : ENNReal) / (q * m : ℕ) := by
  have hq0 : (q : ENNReal) ≠ 0 := by exact_mod_cast hq.ne'
  have hm0 : (m : ENNReal) ≠ 0 := by exact_mod_cast hm.ne'
  rw [← ENNReal.mul_div_mul_right (a : ENNReal) q hm0 (ENNReal.natCast_ne_top m),
    ← ENNReal.mul_div_mul_right (b : ENNReal) m hq0 (ENNReal.natCast_ne_top q),
    mul_comm (m : ENNReal) q, ENNReal.div_add_div_same, Nat.cast_add, Nat.cast_mul, Nat.cast_mul,
    Nat.cast_mul]

/-- The query part `(x/n)^t + y/|E|` below `2^-B'` from a `Nat` inequality. -/
theorem query_le {x n t y X Y : ℕ} (B' : ℕ) (hn : 0 < n) (hx : x ≤ X) (hy : y ≤ Y)
    (h : (X ^ t * 2 ^ 192 + Y * n ^ t) * 2 ^ B' ≤ n ^ t * 2 ^ 192) :
    ((x : ENNReal) / n) ^ t + (y : ENNReal) / Fintype.card E ≤ (2 : ENNReal)⁻¹ ^ B' := by
  rw [card_E_cast]
  calc ((x : ENNReal) / n) ^ t + (y : ENNReal) / ((2 ^ 192 : ℕ) : ENNReal)
      ≤ ((X : ENNReal) / n) ^ t + (Y : ENNReal) / ((2 ^ 192 : ℕ) : ENNReal) := by
        gcongr
    _ = ((X ^ t : ℕ) : ENNReal) / (n ^ t : ℕ) + (Y : ENNReal) / ((2 ^ 192 : ℕ) : ENNReal) := by
        rw [div_eq_mul_inv, mul_pow, ← ENNReal.inv_pow, ← div_eq_mul_inv]
        simp only [Nat.cast_pow]
    _ ≤ _ := by
        rw [nat_div_add_div (pow_pos hn t) (by positivity)]
        exact nat_div_le B' h

/-- `2^-17·z ≤ 2^-B` from `z ≤ 2^-(B−17)`. -/
theorem grind_le {z : ENNReal} {B : ℕ} (hB : 17 ≤ B) (h : z ≤ (2 : ENNReal)⁻¹ ^ (B - 17)) :
    (2 : ENNReal)⁻¹ ^ Whir.queryGrindingBits * z ≤ (2 : ENNReal)⁻¹ ^ B := by
  rw [show Whir.queryGrindingBits = 17 from rfl]
  calc (2 : ENNReal)⁻¹ ^ 17 * z
      ≤ (2 : ENNReal)⁻¹ ^ 17 * (2 : ENNReal)⁻¹ ^ (B - 17) := by gcongr
    _ = _ := by rw [← pow_add]; congr 1; omega

/-- `2^-k < 1` for `k ≥ 1`. -/
theorem inv_two_pow_lt_one {k : ℕ} (hk : 1 ≤ k) : (2 : ENNReal)⁻¹ ^ k < 1 :=
  pow_lt_one₀ (by positivity) (ENNReal.inv_lt_one.mpr (by norm_num)) (by omega)

/-! ## The ladder check -/

namespace Cert

/-- The fold group of a level with `ℓ` folds at most `2^-B`. -/
def FoldOK (B : ℕ) (c : Cert) (ℓ : ℕ) : Prop :=
  (2 * c.listHi + 2 ^ (ℓ - 1) * c.excHi) * 2 ^ B ≤ 2 ^ 192

/-- The out-of-domain group at most `2^-B`: `listHi'²·κ·2^B ≤ |E|`. -/
def OodOK (B : ℕ) (c c' : Cert) : Prop := c'.listHi * c'.listHi * c.κ * 2 ^ B ≤ 2 ^ 192

/-- The query group with a next level at most `2^-B` (after the `2^-17` of grinding). -/
def QueryOK (B : ℕ) (c c' : Cert) (t : ℕ) : Prop :=
  ((c.thrHi - 1) ^ t * 2 ^ 192 + (t + 1) * c'.listHi * c.n ^ t) * 2 ^ (B - 17) ≤
    c.n ^ t * 2 ^ 192

/-- The final query group at most `2^-B` (after the `2^-17` of grinding). -/
def FinalOK (B : ℕ) (c : Cert) (t : ℕ) : Prop :=
  ((c.thrHi - 1) ^ t * 2 ^ 192 + t * c.n ^ t) * 2 ^ (B - 17) ≤ c.n ^ t * 2 ^ 192

/-- `FoldOK` is a `Nat` comparison. -/
instance {B : ℕ} {c : Cert} {ℓ : ℕ} : Decidable (c.FoldOK B ℓ) := by
  unfold FoldOK; infer_instance

/-- `OodOK` is a `Nat` comparison. -/
instance {B : ℕ} {c c' : Cert} : Decidable (c.OodOK B c') := by
  unfold OodOK; infer_instance

/-- `QueryOK` is a `Nat` comparison. -/
instance {B : ℕ} {c c' : Cert} {t : ℕ} : Decidable (c.QueryOK B c' t) := by
  unfold QueryOK; infer_instance

/-- `FinalOK` is a `Nat` comparison. -/
instance {B : ℕ} {c : Cert} {t : ℕ} : Decidable (c.FinalOK B t) := by
  unfold FinalOK; infer_instance

end Cert

/-- **The check of a ladder** from level `i` (after `pre` folds) against the certificates `cs`:
each level's certificate checks, matches the ladder's arithmetic, and bounds its groups'
escapes by `2^-B`. -/
def chkLevels (B μ : ℕ) (cs : ℕ → Cert) : ℕ → ℕ → List Whir.Level → Bool
  | _, _, [] => true
  | i, pre, [l] => decide ((cs i).OK ∧ (cs i).κ + pre + l.fold = μ ∧ (cs i).R = l.logInvRate ∧
      (cs i).FoldOK B l.fold ∧ (cs i).FinalOK B l.queries)
  | i, pre, l :: l' :: rest => decide ((cs i).OK ∧ (cs i).κ + pre + l.fold = μ ∧
      (cs i).R = l.logInvRate ∧ (cs i).FoldOK B l.fold ∧ (cs i).OodOK B (cs (i + 1)) ∧
      (cs i).QueryOK B (cs (i + 1)) l.queries) &&
    chkLevels B μ cs (i + 1) (pre + l.fold) (l' :: rest)

variable {B μ : ℕ} {cs : ℕ → Cert}

/-- A checked ladder's first certificate checks. -/
theorem chkLevels_head {i pre : ℕ} {l : Whir.Level} {rest : List Whir.Level}
    (h : chkLevels B μ cs i pre (l :: rest) = true) : (cs i).OK := by
  cases rest with
  | nil => exact (of_decide_eq_true h).1
  | cons l' rest =>
    simp only [chkLevels, Bool.and_eq_true] at h
    exact (of_decide_eq_true h.1).1

/-- The fold group of a checked level. -/
theorem eFold_le {c : Cert} (h : c.OK) {ℓ : ℕ} (hf : c.FoldOK B ℓ) :
    eFold (mkCode c) ℓ ≤ (2 : ENNReal)⁻¹ ^ B := by
  rw [eFold, mkCode_eq h, card_E_cast]
  refine le_trans ?_ (nat_div_le B hf)
  gcongr
  · exact Cert.listMax_le h
  · exact Cert.mcaMax_le h

/-- The out-of-domain group of a checked level. -/
theorem eOod_le {c c' : Cert} (h : c.OK) (h' : c'.OK) (ho : c.OodOK B c') :
    eOod (mkCode c') (mkCode c).κ ≤ (2 : ENNReal)⁻¹ ^ B := by
  rw [eOod, mkCode_eq h, mkCode_eq h', card_E_cast]
  refine le_trans ?_ (nat_div_le B ho)
  have hL := Cert.listMax_le h'
  gcongr
  · rw [Nat.choose_two_right]
    calc (c'.toCode h').listMax * ((c'.toCode h').listMax - 1) / 2
        ≤ (c'.toCode h').listMax * ((c'.toCode h').listMax - 1) := Nat.div_le_self _ _
      _ ≤ c'.listHi * c'.listHi := Nat.mul_le_mul hL (by omega)
  · exact le_rfl

/-- The query group of a checked level, before the grinding discount. -/
theorem eQuery_le {c c' : Cert} (h : c.OK) (h' : c'.OK) {t : ℕ} (hq : c.QueryOK B c' t) :
    eQuery (mkCode c) (mkCode c') t ≤ (2 : ENNReal)⁻¹ ^ (B - 17) := by
  rw [eQuery, mkCode_eq h, mkCode_eq h']
  exact query_le (B - 17) (Nat.two_pow_pos _) (Nat.sub_le_sub_right (Cert.thr_le h) 1)
    (Nat.mul_le_mul_left _ (Cert.listMax_le h')) hq

/-- The final query group of a checked level, before the grinding discount. -/
theorem eQueryFinal_le {c : Cert} (h : c.OK) {t : ℕ} (hq : c.FinalOK B t) :
    eQueryFinal (mkCode c) t ≤ (2 : ENNReal)⁻¹ ^ (B - 17) := by
  rw [eQueryFinal, mkCode_eq h]
  exact query_le (B - 17) (Nat.two_pow_pos _) (Nat.sub_le_sub_right (Cert.thr_le h) 1)
    le_rfl hq

/-- A tail round's escape `2/|E|`. -/
theorem eTail_le (hB : B ≤ 191) : eTail ≤ (2 : ENNReal)⁻¹ ^ B := by
  rw [eTail, card_E_cast]
  have h2 : 2 * 2 ^ B ≤ 2 ^ 192 :=
    calc 2 * 2 ^ B ≤ 2 * 2 ^ 191 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hB)
      _ = 2 ^ 192 := by norm_num
  exact_mod_cast nat_div_le (a := 2) B h2

/-- **A checked ladder satisfies the ladder arithmetic and has escapes at most `2^-B`.** -/
theorem chkLevels_sound (hB : 18 ≤ B) (hB' : B ≤ 191) :
    ∀ (levels : List Whir.Level) (i pre : ℕ), chkLevels B μ cs i pre levels = true →
      LadderArith μ (codesOf cs) i pre levels ∧
        levelEps (codesOf cs) i levels ≤ (2 : ENNReal)⁻¹ ^ B
  | [], _, _, _ => ⟨trivial, by simp [levelEps]⟩
  | [l], i, pre, hc => by
    obtain ⟨hok, hκ, hR, hf, hq⟩ := of_decide_eq_true hc
    have hq' := eQueryFinal_le hok hq
    refine ⟨⟨by rw [codesOf, mkCode_eq hok]; exact hκ, by rw [codesOf, mkCode_eq hok]; exact hR,
      lt_of_le_of_lt hq' (inv_two_pow_lt_one (by omega))⟩, ?_⟩
    exact max_le (eFold_le hok hf) (max_le (grind_le (by omega) hq') (eTail_le hB'))
  | l :: l' :: rest, i, pre, hc => by
    simp only [chkLevels, Bool.and_eq_true] at hc
    obtain ⟨⟨hok, hκ, hR, hf, ho, hq⟩, hrest⟩ := And.imp_left of_decide_eq_true hc
    have hok' := chkLevels_head hrest
    have ih := chkLevels_sound hB hB' (l' :: rest) (i + 1) (pre + l.fold) hrest
    have ho' := eOod_le hok hok' ho
    have hq' := eQuery_le hok hok' hq
    refine ⟨⟨by rw [codesOf, mkCode_eq hok]; exact hκ, by rw [codesOf, mkCode_eq hok]; exact hR,
      lt_of_le_of_lt ho' (inv_two_pow_lt_one (by omega)),
      lt_of_le_of_lt hq' (inv_two_pow_lt_one (by omega)), ih.1⟩, ?_⟩
    exact max_le (max_le (eFold_le hok hf) ho') (max_le (grind_le (by omega) hq') ih.2)

end
end LeanVM.Protocol.Whir.Params
