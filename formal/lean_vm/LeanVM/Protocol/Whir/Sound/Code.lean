/-
  LeanVM.Protocol.Whir.Sound.Code

  The code of a WHIR level and its thresholds, and lane oracles indexed by integers.
-/

module

public import LeanVM.Protocol.Whir.Sound.Tuple

/-!
# The code of a level

Annex B of the leanVM specification (`doc/leanvm/body/b-polynomial-commitment-scheme.tex`),
`sec:soundness`, "Thresholds", for the deployed code: level `i` commits `2^ℓ` lanes, each the
encoding `enc κ R` of a message on `κ` variables (`κ` the variables left after the level's
folds), on the domain `D_{κ,R}` of `n = 2^(κ+R)` points (`domain κ R`). Its rounds are analysed
at the degrees `d_j = 2^κ − 1 + j` and thresholds `A_j = A − (ℓ − j)`, `0 ≤ j ≤ ℓ`, `A` the
threshold of the last round (the Rust's `agreement`, `crates/pcs/src/whir_config.rs`).

* `LevelCode`: `κ`, `R`, `ℓ`, `A`, with `κ + R ≤ 64`; `dom`, `n`, `deg j`, `thr j`.
* Lane oracles are indexed by integers, `O : ℕ → Fin n → E` (lane `j` of column `v`), read on `m`
  lane bits by `rowsOf m O`: lane `⟨u⟩`, bit `0` of `u` lowest, which a fold binds first.
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Whir Finset

@[expose] public section

/-- **The code of a level**: message variables `κ` after its folds, log inverse rate `R`, folds
`ℓ`, threshold `A` of its last round. -/
structure LevelCode where
  /-- The message variables after the level's folds. -/
  κ : ℕ
  /-- The log inverse rate. -/
  R : ℕ
  /-- The level's folds. -/
  ℓ : ℕ
  /-- The agreement threshold of the level's last round. -/
  A : ℕ
  /-- The domain fits in `K`. -/
  h64 : κ + R ≤ 64
  /-- Rate at most `1/2`. -/
  hR : 1 ≤ R

namespace LevelCode

variable (P : LevelCode)

/-- The block length `n = 2^(κ+R)`. -/
abbrev n : ℕ := 2 ^ (P.κ + P.R)

/-- The domain `D_{κ,R}`. -/
abbrev dom : Fin P.n ↪ E := domain P.κ P.R P.h64

/-- The degree bound of round `j`, `2^κ − 1 + j`. -/
abbrev deg (j : ℕ) : ℕ := 2 ^ P.κ - 1 + j

/-- The threshold of round `j`, `A − (ℓ − j)`. -/
abbrev thr (j : ℕ) : ℕ := P.A - (P.ℓ - j)

/-- The list bound the level starts on, `jl(n, A_0, d_0)`. -/
abbrev listMax : ℕ := jl P.n (P.thr 0) (P.deg 0)

/-- The message variables are fewer than `64`. -/
theorem κ_lt : P.κ < 64 := by have := P.h64; have := P.hR; omega

end LevelCode

/-! ## Lane oracles -/

/-- An integer-indexed lane oracle on `m` lane bits: lane `⟨u⟩` (bit `0` low). -/
def rowsOf (m : ℕ) {ι : Type*} (O : ℕ → ι → E) : (Fin m → Bool) → ι → E :=
  fun u ↦ O (bitsToNat u)

theorem bitsToNat_cons {m : ℕ} (b : Bool) (u : Fin m → Bool) :
    bitsToNat (Fin.cons b u : Fin (m + 1) → Bool) = b.toNat + 2 * bitsToNat u := by
  simp only [bitsToNat, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.val_zero, pow_zero,
    mul_one, Fin.val_succ, pow_succ, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ ↦ by ring

end
end LeanVM.Protocol.Whir.Sound
