/-
  LeanVM.Protocol.Whir.Sound.Code

  The code of a WHIR level at ArkLib's Johnson radius, its lists, the decoding of list members to
  messages, lane oracles indexed by integers, and the fold step of the round-by-round soundness:
  a fold challenge keeps every list member violating the running claim except at
  `2·L + 2^m·E_mca` challenges.
-/

module

public import LeanVM.Protocol.Whir.Sound.Sumcheck
public import LeanVM.Protocol.Whir.NovelBasis
public import LeanVM.Protocol.ToArkLib.Whir.Fold
public import LeanVM.Protocol.ToArkLib.Whir.Johnson

/-!
# The code of a level and the fold step

Annex B of the leanVM specification (leanVM `127510d14c98ade4e8a97646c44fa7f1ff5e752d`,
`doc/leanvm/body/b-polynomial-commitment-scheme.tex`), proof of Theorem `thm:rbr`, "Fold
challenge", for the deployed code: level `i` uses the novel-basis Reed-Solomon code
`C_i = RS[E, D_{κ,R}, 2^κ]` (`enc κ R`, `range_enc`) on `n = 2^(κ+R)` points, and the analysis
runs at ArkLib's Johnson radius `1 − √ρ₋ − η` with `ρ₋ = (2^κ − 1)/n`
(`ReedSolomon.mcaError_affineLine_johnson_le`).

* `LevelCode`: the parameters `κ, R, η` with the conditions of ArkLib's Johnson count
  (`1 ≤ κ`, `1 ≤ R`, `0 < η`, agreement fraction at most `1`). Its list bound is
  `listMax = ⌊1/(2η√ρ₋)⌋` (`LevelCode.card_iList_le`) and its MCA count is
  `mcaMax = ⌊johnsonExceptionCount n D A η⌋` (`LevelCode.card_foldBad_le`), `A = thr` the
  Johnson threshold. `LevelCode.two_pow_le_thr`: the threshold exceeds the degree, so list
  members are unique on their agreement sets and the level-0 bridge applies.
* `decode`: the message of a codeword row (`enc` is injective), `Viol`: every member of the list
  of a word violates a claim, the invariant `A(i, j)` of the design note.
* Lane oracles are indexed by integers, `O : ℕ → Fin n → E` (lane `j` of column `v`), read on `m`
  lane bits by `rowsOf m O`. One fold binds the low lane bit: `foldN s O j = (1 − s) O(2j) +
  s O(2j+1)`, the order of the verifier's `eq_kernel` (first challenge, low bit).
* `card_foldStep_bad_le`: **the fold step.** If every member of the list of `rowsOf (m+1) O`
  violates `(Φ, σ)` and the prover's quadratic has `h(0) + h(1) = σ`, at most
  `2·listMax + 2^m·mcaMax` challenges `s` leave a member of the list of `rowsOf m (foldN s O)`
  satisfying `(Φ(s, ·), h(s))`. The two terms are the bad events `B₁` (sumcheck, two points per
  member) and `B₂` (the fold-list lemma `card_foldBad_le_johnson`, one pair of rows per lane of
  the folded word) of the Annex. At `127510d1` the Annex bounds `B₂` by `ε` alone (`lem:fold-list`,
  citing Jo, ePrint 2026/891, Thm 4.4), without the row-union factor `2^m` proved here; see
  `LeanVM.Protocol.Whir.Params.Deployed`.
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.Whir Finset
  ReedSolomon.HiddenDerivative

@[expose] public section

/-! ## The code of a level -/

/-- The code of a level at the Johnson radius: message variables `κ`, rate `2^-R`, slack `η`. -/
structure LevelCode where
  /-- The message variables. -/
  κ : ℕ
  /-- The log inverse rate. -/
  R : ℕ
  /-- The Johnson slack. -/
  η : ℝ
  /-- The domain fits in `K`. -/
  h64 : κ + R ≤ 64
  /-- At least one message variable (`ρ₋ > 0`). -/
  hκ : 1 ≤ κ
  /-- Rate at most `1/2`. -/
  hR : 1 ≤ R
  /-- Positive slack. -/
  hη : 0 < η
  /-- The agreement fraction is at most `1`. -/
  hagr : johnsonAgreement (2 ^ (κ + R)) (2 ^ κ - 1) η ≤ 1

namespace LevelCode

variable (P : LevelCode)

/-- The block length `n = 2^(κ+R)`. -/
abbrev n : ℕ := 2 ^ (P.κ + P.R)

/-- The degree bound `D = 2^κ − 1`. -/
abbrev D : ℕ := 2 ^ P.κ - 1

/-- The code `RS[E, D_{κ,R}, 2^κ]`, the range of `enc κ R`. -/
noncomputable abbrev code : Submodule E (Fin P.n → E) :=
  ReedSolomon.code (domain P.κ P.R P.h64) (2 ^ P.κ)

/-- The Johnson agreement threshold `⌈(√ρ₋ + η) n⌉`. -/
noncomputable def thr : ℕ := ⌈johnsonAgreement P.n P.D P.η * P.n⌉₊

/-- The list bound `⌊1/(2η√ρ₋)⌋`. -/
noncomputable def listMax : ℕ := ⌊1 / (2 * P.η * √(johnsonRhoMinus P.n P.D))⌋₊

/-- ArkLib's exceptional count of the MCA event per pair of rows. -/
noncomputable def mcaMax : ℕ := ⌊johnsonExceptionCount P.n P.D P.thr P.η⌋₊

theorem two_pow_κ_eq : 2 ^ P.κ = P.D + 1 := (Nat.sub_add_cancel Nat.one_le_two_pow).symm

theorem one_le_D : 1 ≤ P.D := by
  have : 2 ≤ 2 ^ P.κ := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ P.κ := Nat.pow_le_pow_right (by norm_num) P.hκ
  simp only [D]; omega

theorem D_le : P.D ≤ P.n - 2 := by
  have : 2 * 2 ^ P.κ ≤ 2 ^ (P.κ + P.R) := by
    rw [pow_add, mul_comm]
    exact Nat.mul_le_mul_left _ (by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ P.R := Nat.pow_le_pow_right (by norm_num) P.hR)
  have := P.one_le_D
  simp only [D, n] at *; omega

theorem D_lt_n : P.D < P.n := by
  have := P.D_le; have := P.one_le_D; omega

/-- The code at ArkLib's degree parametrization. -/
theorem code_eq : P.code = ReedSolomon.code (domain P.κ P.R P.h64) (P.D + 1) := by
  rw [code, P.two_pow_κ_eq]

/-- **The list bound.** -/
theorem card_iList_le {ρ : Type*} [Fintype ρ] (O : ρ → Fin P.n → E) :
    (iList P.code P.thr O).card ≤ P.listMax := by
  rw [code_eq]
  exact card_iList_johnsonAgreement_le_floor _ (by have := P.one_le_D; omega)
    (Nat.two_pow_pos _) P.hη O

/-- **The fold-list count**: at most `|ρ|·mcaMax` challenges create new list members. -/
theorem card_foldBad_le {ρ : Type*} [Fintype ρ] (O : Bool × ρ → Fin P.n → E) :
    (foldBad P.code P.thr O).card ≤ Fintype.card ρ * P.mcaMax := by
  rw [code_eq]
  exact card_foldBad_le_johnson _ P.one_le_D P.D_le P.hη P.hagr O

/-- The threshold exceeds the degree: `2^κ ≤ ⌈(√ρ₋ + η) n⌉`. -/
theorem two_pow_le_thr : 2 ^ P.κ ≤ P.thr := by
  rw [P.two_pow_κ_eq, thr, Nat.add_one_le_iff, Nat.lt_ceil]
  have hn : (0 : ℝ) < P.n := by exact_mod_cast Nat.two_pow_pos _
  have hDn : (P.D : ℝ) ≤ P.n := by exact_mod_cast P.D_lt_n.le
  have hD0 : (0 : ℝ) ≤ P.D := Nat.cast_nonneg _
  -- `√(D/n)·n ≥ D`, squaring: `D² ≤ D n`; and `η n > 0`.
  have hs : √(johnsonRhoMinus P.n P.D) ^ 2 = (P.D : ℝ) / P.n :=
    Real.sq_sqrt (div_nonneg hD0 hn.le)
  have hsq : (P.D : ℝ) ≤ √(johnsonRhoMinus P.n P.D) * P.n := by
    refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
    rw [mul_pow, hs, div_mul_eq_mul_div, sq, sq, mul_div_assoc, mul_div_assoc,
      div_self hn.ne', mul_one]
    exact mul_le_mul_of_nonneg_left hDn hD0
  have := mul_pos P.hη hn
  rw [johnsonAgreement, add_mul]
  linarith

end LevelCode

/-! ## Decoding -/

variable (P : LevelCode)

open Classical in
/-- The message of a codeword row: the unique `g` with `enc g = V u` (zero off the code). -/
noncomputable def decode {ρ : Type*} (V : ρ → Fin P.n → E) : ρ → (Fin P.κ → Bool) → E :=
  fun u ↦ if h : ∃ g, enc P.κ P.R g = V u then h.choose else 0

theorem enc_decode {ρ : Type*} {V : ρ → Fin P.n → E} (hV : IsInterleavedCodeword P.code V)
    (u : ρ) : enc P.κ P.R (decode P V u) = V u := by
  have hex : ∃ g, enc P.κ P.R g = V u := by
    have : V u ∈ ReedSolomon.code (domain P.κ P.R P.h64) (2 ^ P.κ) := hV u
    rw [← range_enc P.h64] at this
    exact this
  simp only [decode, hex, dite_true]
  exact hex.choose_spec

/-- Decoding an encoded word gives the messages back. -/
theorem decode_enc {ρ : Type*} (g : ρ → (Fin P.κ → Bool) → E) :
    decode P (fun u ↦ enc P.κ P.R (g u)) = g := by
  funext u
  have hcw : IsInterleavedCodeword P.code fun u ↦ enc P.κ P.R (g u) := fun u ↦ by
    show _ ∈ ReedSolomon.code (domain P.κ P.R P.h64) (2 ^ P.κ)
    rw [← range_enc P.h64]; exact LinearMap.mem_range_self _ _
  exact enc_injective P.h64 (enc_decode P hcw u)

/-- Every member of the list of `O` violates the claim `(Φ, σ)`. -/
def Viol {m : ℕ} (O : (Fin m → Bool) → Fin P.n → E) (Φ : List E → E) (σ : E) : Prop :=
  ∀ V ∈ iList P.code P.thr O, claimSum Φ (decode P V) ≠ σ

/-! ## Lane oracles -/

/-- An integer-indexed lane oracle on `m` lane bits: lane `⟨u⟩` (bit `0` low). -/
def rowsOf (m : ℕ) {ι : Type*} (O : ℕ → ι → E) : (Fin m → Bool) → ι → E :=
  fun u ↦ O (bitsToNat u)

/-- One fold of an integer-indexed lane oracle on the low lane bit. -/
def foldN {ι : Type*} (s : E) (O : ℕ → ι → E) : ℕ → ι → E :=
  fun j x ↦ (1 - s) * O (2 * j) x + s * O (2 * j + 1) x

/-- The folds of a level, first challenge first. -/
def foldsN {ι : Type*} (s : List E) (O : ℕ → ι → E) : ℕ → ι → E :=
  s.foldl (fun O c ↦ foldN c O) O

theorem bitsToNat_cons {m : ℕ} (b : Bool) (u : Fin m → Bool) :
    bitsToNat (Fin.cons b u : Fin (m + 1) → Bool) = b.toNat + 2 * bitsToNat u := by
  simp only [bitsToNat, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.val_zero, pow_zero,
    mul_one, Fin.val_succ, pow_succ, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- The rows of an interleaved word on `m + 1` lane bits, split on the low bit. -/
def consRows {m : ℕ} {ι M : Type*} (Q : (Fin (m + 1) → Bool) → ι → M) :
    Bool × (Fin m → Bool) → ι → M :=
  fun r ↦ Q (Fin.cons r.1 r.2)

/-- Rejoin split rows. -/
def unconsRows {m : ℕ} {ι M : Type*} (Q : Bool × (Fin m → Bool) → ι → M) :
    (Fin (m + 1) → Bool) → ι → M :=
  fun u ↦ Q (u 0, Fin.tail u)

theorem consRows_unconsRows {m : ℕ} {ι M : Type*} (Q : Bool × (Fin m → Bool) → ι → M) :
    consRows (unconsRows Q) = Q := by
  funext r
  simp [consRows, unconsRows]

theorem unconsRows_consRows {m : ℕ} {ι M : Type*} (Q : (Fin (m + 1) → Bool) → ι → M) :
    unconsRows (consRows Q) = Q := by
  funext u
  simp [consRows, unconsRows]

/-- Folding the integer-indexed oracle is folding its split rows. -/
theorem rowsOf_foldN {m : ℕ} {ι : Type*} (s : E) (O : ℕ → ι → E) :
    rowsOf m (foldN s O) = fold s (consRows (rowsOf (m + 1) O)) := by
  funext u x
  simp [rowsOf, foldN, fold, consRows, bitsToNat_cons, add_comm]

/-- Lists are invariant under splitting the rows. -/
theorem consRows_mem_iList {m : ℕ} {ι : Type*} [Fintype ι] (C : Submodule E (ι → E)) (A : ℕ)
    {Q V : (Fin (m + 1) → Bool) → ι → E} :
    consRows V ∈ iList C A (consRows Q) ↔ V ∈ iList C A Q := by
  simp only [mem_iList, IsInterleavedCodeword, IsClose, AgreeOn, consRows]
  constructor
  · rintro ⟨hcw, S, hS, hag⟩
    refine ⟨fun u ↦ by simpa using hcw (u 0, Fin.tail u), S, hS, fun u x hx ↦ ?_⟩
    simpa using hag (u 0, Fin.tail u) x hx
  · rintro ⟨hcw, S, hS, hag⟩
    exact ⟨fun r ↦ hcw _, S, hS, fun r x hx ↦ hag _ x hx⟩

/-- The decoded fold of a codeword is the fold of its messages. -/
theorem decode_fold {m : ℕ} {V : (Fin (m + 1) → Bool) → Fin P.n → E}
    (hV : IsInterleavedCodeword P.code V) (s : E) :
    decode P (fold s (consRows V)) = foldRows s (decode P V) := by
  have hcw : IsInterleavedCodeword P.code (fold s (consRows V)) :=
    isInterleavedCodeword_fold _ (fun r ↦ hV _) s
  funext u
  apply enc_injective P.h64
  have hf : foldRows s (decode P V) u =
      (1 - s) • decode P V (Fin.cons false u) + s • decode P V (Fin.cons true u) := by
    funext x; simp [foldRows]
  rw [enc_decode P hcw u, hf, map_add, map_smul, map_smul, enc_decode P hV, enc_decode P hV,
    fold_apply_eq_smul]
  rfl

/-! ## The fold step -/

open Classical in
/-- **The fold step** (Annex B, proof of `thm:rbr`, "Fold challenge"): if every member of the list
of `rowsOf (m+1) O` violates `(Φ, σ)` and the prover's quadratic `[c₀, c₁, c₂]` has
`h(0) + h(1) = σ`, at most `2·listMax + 2^m·mcaMax` challenges `s` leave a member of the list of
`rowsOf m (foldN s O)` satisfying `(Φ(s, ·), h(s))`. -/
theorem card_foldStep_bad_le {m : ℕ} (Φ : List E → E) (hΦ : IsMultiaffine (m + 1 + P.κ) Φ)
    (O : ℕ → Fin P.n → E) (σ c₀ c₁ c₂ : E)
    (hσ : polyEval [c₀, c₁, c₂] 0 + polyEval [c₀, c₁, c₂] 1 = σ)
    (hviol : Viol P (rowsOf (m + 1) O) Φ σ) :
    (univ.filter fun s ↦
        ¬ Viol P (rowsOf m (foldN s O)) (fun r ↦ Φ (s :: r)) (polyEval [c₀, c₁, c₂] s)).card ≤
      2 * P.listMax + 2 ^ m * P.mcaMax := by
  classical
  set Q := rowsOf (m + 1) O
  set L := iList P.code P.thr Q
  let B₁ : Finset E := univ.filter fun s ↦
    ∃ V ∈ L, polyEval [c₀, c₁, c₂] s = claimSum (fun r ↦ Φ (s :: r)) (foldRows s (decode P V))
  have hB₁ : B₁.card ≤ 2 * P.listMax := by
    refine (card_filter_exists_le L _ (N := 2) fun V hV ↦
      card_sumcheck_bad_le Φ hΦ (decode P V) σ c₀ c₁ c₂ hσ (hviol V hV)).trans ?_
    rw [mul_comm]
    exact Nat.mul_le_mul_left _ (P.card_iList_le Q)
  have hB₂ : (foldBad P.code P.thr (consRows Q)).card ≤ 2 ^ m * P.mcaMax := by
    have := P.card_foldBad_le (consRows Q)
    simpa using this
  refine (Finset.card_le_card fun s hs ↦ ?_).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add hB₁ hB₂))
  rw [Finset.mem_union]
  by_contra hgood
  push Not at hgood
  obtain ⟨hs₁, hs₂⟩ := hgood
  refine (Finset.mem_filter.mp hs).2 fun V' hV' ↦ ?_
  rw [rowsOf_foldN] at hV'
  have hlist := not_not.mp ((not_congr (mem_foldBad _ _ _ s)).mp hs₂)
  rw [hlist] at hV'
  obtain ⟨W', hW', rfl⟩ := Finset.mem_image.mp hV'
  rw [← consRows_unconsRows W', consRows_mem_iList] at hW'
  rw [← consRows_unconsRows W', decode_fold P ((mem_iList _ _ _ _).mp hW').1]
  intro heq
  exact hs₁ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, _, hW', heq.symm⟩)

end
end LeanVM.Protocol.Whir.Sound
