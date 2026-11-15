/-
  LeanVM.Guest.B1.Tables.Vt.Air

  `verify_tables`' air check: each table's weight and form value, and their sum the table
  sumcheck's final claim.

  Do not edit: `scripts/b1c-vt/all.py` writes it (`regen-guest.sh`, step `vt`).
-/

module

public import LeanVM.Guest.B1.Tables.Vt.FormsVal
public import LeanVM.Guest.B1.Tables.Vt.Pi

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

set_option maxRecDepth 10000 in
/-- Table 0's air term: its weight `cprod[x]·peq[τ]` with `g^n = x·τ` (`τ = kb[2]`), times
its form value. -/
theorem vtAir0 {rd : Reader} {σ : Val} (h : VtH rd σ)
    : σ (.n 2545) = σ (.n 2932) * σ (.n 28) ∧
      LoadHolds rd (σ (.n 2631) * σ (.n 2932)) 0 (σ (.n 2934)) ∧
      LoadHolds rd (σ (.n 2656) * σ (.n 28)) 0 (σ (.n 2936)) ∧
      σ (.n 2938) = σ (.n 2934) * σ (.n 2936) *
        (((σ (.n 2614) * σ (.n 2899)) + (σ (.n 2615) * σ (.n 2920))) + (σ (.n 2616) * σ (.n 2929))) := by
  have a2928 := h.atomAt 2928 (.mul (.n 2545) (.n 2932) (.n 28)) (by decide +kernel)
  have a2929 := h.atomAt 2929 (.mul (.n 2933) (.n 2631) (.n 2932)) (by decide +kernel)
  have a2930 := h.atomAt 2930 (.load (.n 2934) (.n 2933) 0) (by decide +kernel)
  have a2931 := h.atomAt 2931 (.mul (.n 2935) (.n 2656) (.n 28)) (by decide +kernel)
  have a2932 := h.atomAt 2932 (.load (.n 2936) (.n 2935) 0) (by decide +kernel)
  have a2933 := h.atomAt 2933 (.mul (.n 2937) (.n 2934) (.n 2936)) (by decide +kernel)
  have a2934 := h.atomAt 2934 (.mul (.n 2938) (.n 2937) (.n 2931)) (by decide +kernel)
  have a2896 := h.atomAt 2896 (.mul (.n 2900) (.n 2614) (.n 2899)) (by decide +kernel)
  have a2917 := h.atomAt 2917 (.mul (.n 2921) (.n 2615) (.n 2920)) (by decide +kernel)
  have a2918 := h.atomAt 2918 (.add (.n 2922) (.n 2900) (.n 2921)) (by decide +kernel)
  have a2926 := h.atomAt 2926 (.mul (.n 2930) (.n 2616) (.n 2929)) (by decide +kernel)
  have a2927 := h.atomAt 2927 (.add (.n 2931) (.n 2922) (.n 2930)) (by decide +kernel)
  simp only [Atom.Holds] at a2928 a2929 a2930 a2931 a2932 a2933 a2934 a2896 a2917 a2918 a2926 a2927
  refine ⟨a2928, by rw [← a2929]; exact a2930, by rw [← a2931]; exact a2932, ?_⟩
  rw [a2934, a2933, a2927, a2926, a2918, a2917, a2896]

set_option maxRecDepth 10000 in
/-- Table 1's air term: its weight `cprod[x]·peq[τ]` with `g^n = x·τ` (`τ = kb[3]`), times
its form value. -/
theorem vtAir1 {rd : Reader} {σ : Val} (h : VtH rd σ)
    : σ (.n 2545) = σ (.n 3221) * σ (.n 29) ∧
      LoadHolds rd (σ (.n 2631) * σ (.n 3221)) 0 (σ (.n 3223)) ∧
      LoadHolds rd (σ (.n 2656) * σ (.n 29)) 0 (σ (.n 3225)) ∧
      σ (.n 3227) = σ (.n 3223) * σ (.n 3225) *
        (((σ (.n 2614) * σ (.n 3188)) + (σ (.n 2615) * σ (.n 3209))) + (σ (.n 2616) * σ (.n 3218))) := by
  have a3181 := h.atomAt 3181 (.mul (.n 2545) (.n 3221) (.n 29)) (by decide +kernel)
  have a3182 := h.atomAt 3182 (.mul (.n 3222) (.n 2631) (.n 3221)) (by decide +kernel)
  have a3183 := h.atomAt 3183 (.load (.n 3223) (.n 3222) 0) (by decide +kernel)
  have a3184 := h.atomAt 3184 (.mul (.n 3224) (.n 2656) (.n 29)) (by decide +kernel)
  have a3185 := h.atomAt 3185 (.load (.n 3225) (.n 3224) 0) (by decide +kernel)
  have a3186 := h.atomAt 3186 (.mul (.n 3226) (.n 3223) (.n 3225)) (by decide +kernel)
  have a3187 := h.atomAt 3187 (.mul (.n 3227) (.n 3226) (.n 3220)) (by decide +kernel)
  have a3149 := h.atomAt 3149 (.mul (.n 3189) (.n 2614) (.n 3188)) (by decide +kernel)
  have a3170 := h.atomAt 3170 (.mul (.n 3210) (.n 2615) (.n 3209)) (by decide +kernel)
  have a3171 := h.atomAt 3171 (.add (.n 3211) (.n 3189) (.n 3210)) (by decide +kernel)
  have a3179 := h.atomAt 3179 (.mul (.n 3219) (.n 2616) (.n 3218)) (by decide +kernel)
  have a3180 := h.atomAt 3180 (.add (.n 3220) (.n 3211) (.n 3219)) (by decide +kernel)
  simp only [Atom.Holds] at a3181 a3182 a3183 a3184 a3185 a3186 a3187 a3149 a3170 a3171 a3179 a3180
  refine ⟨a3181, by rw [← a3182]; exact a3183, by rw [← a3184]; exact a3185, ?_⟩
  rw [a3187, a3186, a3180, a3179, a3171, a3170, a3149]

set_option maxRecDepth 10000 in
/-- Table 2's air term: its weight `cprod[x]·peq[τ]` with `g^n = x·τ` (`τ = kb[4]`), times
its form value. -/
theorem vtAir2 {rd : Reader} {σ : Val} (h : VtH rd σ)
    : σ (.n 2545) = σ (.n 3394) * σ (.n 30) ∧
      LoadHolds rd (σ (.n 2631) * σ (.n 3394)) 0 (σ (.n 3396)) ∧
      LoadHolds rd (σ (.n 2656) * σ (.n 30)) 0 (σ (.n 3398)) ∧
      σ (.n 3400) = σ (.n 3396) * σ (.n 3398) *
        (((σ (.n 2614) * σ (.n 3373)) + (σ (.n 2615) * σ (.n 3386))) + (σ (.n 2616) * σ (.n 3391))) := by
  have a3330 := h.atomAt 3330 (.mul (.n 2545) (.n 3394) (.n 30)) (by decide +kernel)
  have a3331 := h.atomAt 3331 (.mul (.n 3395) (.n 2631) (.n 3394)) (by decide +kernel)
  have a3332 := h.atomAt 3332 (.load (.n 3396) (.n 3395) 0) (by decide +kernel)
  have a3333 := h.atomAt 3333 (.mul (.n 3397) (.n 2656) (.n 30)) (by decide +kernel)
  have a3334 := h.atomAt 3334 (.load (.n 3398) (.n 3397) 0) (by decide +kernel)
  have a3335 := h.atomAt 3335 (.mul (.n 3399) (.n 3396) (.n 3398)) (by decide +kernel)
  have a3336 := h.atomAt 3336 (.mul (.n 3400) (.n 3399) (.n 3393)) (by decide +kernel)
  have a3310 := h.atomAt 3310 (.mul (.n 3374) (.n 2614) (.n 3373)) (by decide +kernel)
  have a3323 := h.atomAt 3323 (.mul (.n 3387) (.n 2615) (.n 3386)) (by decide +kernel)
  have a3324 := h.atomAt 3324 (.add (.n 3388) (.n 3374) (.n 3387)) (by decide +kernel)
  have a3328 := h.atomAt 3328 (.mul (.n 3392) (.n 2616) (.n 3391)) (by decide +kernel)
  have a3329 := h.atomAt 3329 (.add (.n 3393) (.n 3388) (.n 3392)) (by decide +kernel)
  simp only [Atom.Holds] at a3330 a3331 a3332 a3333 a3334 a3335 a3336 a3310 a3323 a3324 a3328 a3329
  refine ⟨a3330, by rw [← a3331]; exact a3332, by rw [← a3333]; exact a3334, ?_⟩
  rw [a3336, a3335, a3329, a3328, a3324, a3323, a3310]

set_option maxRecDepth 10000 in
/-- Table 3's air term: its weight `cprod[x]·peq[τ]` with `g^n = x·τ` (`τ = kb[5]`), times
its form value. -/
theorem vtAir3 {rd : Reader} {σ : Val} (h : VtH rd σ)
    : σ (.n 2545) = σ (.n 3692) * σ (.n 31) ∧
      LoadHolds rd (σ (.n 2631) * σ (.n 3692)) 0 (σ (.n 3694)) ∧
      LoadHolds rd (σ (.n 2656) * σ (.n 31)) 0 (σ (.n 3696)) ∧
      σ (.n 3698) = σ (.n 3694) * σ (.n 3696) *
        (((σ (.n 2614) * σ (.n 3659)) + (σ (.n 2615) * σ (.n 3680))) + (σ (.n 2616) * σ (.n 3689))) := by
  have a3592 := h.atomAt 3592 (.mul (.n 2545) (.n 3692) (.n 31)) (by decide +kernel)
  have a3593 := h.atomAt 3593 (.mul (.n 3693) (.n 2631) (.n 3692)) (by decide +kernel)
  have a3594 := h.atomAt 3594 (.load (.n 3694) (.n 3693) 0) (by decide +kernel)
  have a3595 := h.atomAt 3595 (.mul (.n 3695) (.n 2656) (.n 31)) (by decide +kernel)
  have a3596 := h.atomAt 3596 (.load (.n 3696) (.n 3695) 0) (by decide +kernel)
  have a3597 := h.atomAt 3597 (.mul (.n 3697) (.n 3694) (.n 3696)) (by decide +kernel)
  have a3598 := h.atomAt 3598 (.mul (.n 3698) (.n 3697) (.n 3691)) (by decide +kernel)
  have a3560 := h.atomAt 3560 (.mul (.n 3660) (.n 2614) (.n 3659)) (by decide +kernel)
  have a3581 := h.atomAt 3581 (.mul (.n 3681) (.n 2615) (.n 3680)) (by decide +kernel)
  have a3582 := h.atomAt 3582 (.add (.n 3682) (.n 3660) (.n 3681)) (by decide +kernel)
  have a3590 := h.atomAt 3590 (.mul (.n 3690) (.n 2616) (.n 3689)) (by decide +kernel)
  have a3591 := h.atomAt 3591 (.add (.n 3691) (.n 3682) (.n 3690)) (by decide +kernel)
  simp only [Atom.Holds] at a3592 a3593 a3594 a3595 a3596 a3597 a3598 a3560 a3581 a3582 a3590 a3591
  refine ⟨a3592, by rw [← a3593]; exact a3594, by rw [← a3595]; exact a3596, ?_⟩
  rw [a3598, a3597, a3591, a3590, a3582, a3581, a3560]

set_option maxRecDepth 10000 in
/-- Table 4's air term: its weight `cprod[x]·peq[τ]` with `g^n = x·τ` (`τ = kb[6]`), times
its form value. -/
theorem vtAir4 {rd : Reader} {σ : Val} (h : VtH rd σ) {ev : ℕ → E}
    (hev : ∀ c < 14, σ (.n (vtEvB (47 + c))) = ev c)
    : σ (.n 2545) = σ (.n 4021) * σ (.n 32) ∧
      LoadHolds rd (σ (.n 2631) * σ (.n 4021)) 0 (σ (.n 4023)) ∧
      LoadHolds rd (σ (.n 2656) * σ (.n 32)) 0 (σ (.n 4025)) ∧
      σ (.n 4027) = σ (.n 4023) * σ (.n 4025) *
        (((((σ (.n 2612) * (ev 13 + (ev 5 * ev 12))) + (σ (.n 2613) * (ev 5 * (ev 13 + word 1 0)))) + (σ (.n 2614) * σ (.n 3984))) + (σ (.n 2615) * σ (.n 4009))) + (σ (.n 2616) * σ (.n 4018))) := by
  have a3873 := h.atomAt 3873 (.mul (.n 2545) (.n 4021) (.n 32)) (by decide +kernel)
  have a3874 := h.atomAt 3874 (.mul (.n 4022) (.n 2631) (.n 4021)) (by decide +kernel)
  have a3875 := h.atomAt 3875 (.load (.n 4023) (.n 4022) 0) (by decide +kernel)
  have a3876 := h.atomAt 3876 (.mul (.n 4024) (.n 2656) (.n 32)) (by decide +kernel)
  have a3877 := h.atomAt 3877 (.load (.n 4025) (.n 4024) 0) (by decide +kernel)
  have a3878 := h.atomAt 3878 (.mul (.n 4026) (.n 4023) (.n 4025)) (by decide +kernel)
  have a3879 := h.atomAt 3879 (.mul (.n 4027) (.n 4026) (.n 4020)) (by decide +kernel)
  have a3660 := h.atomAt 3660 (.mul (.n 3808) (.n 3749) (.n 3790)) (by decide +kernel)
  have a3661 := h.atomAt 3661 (.add (.n 3809) (.n 3807) (.n 3808)) (by decide +kernel)
  have a3662 := h.atomAt 3662 (.mul (.n 3810) (.n 2612) (.n 3809)) (by decide +kernel)
  have a3663 := h.atomAt 3663 (.const (.n 3811) (word 1 0)) (by decide +kernel)
  have a3664 := h.atomAt 3664 (.add (.n 3812) (.n 3807) (.n 3811)) (by decide +kernel)
  have a3665 := h.atomAt 3665 (.mul (.n 3813) (.n 3749) (.n 3812)) (by decide +kernel)
  have a3666 := h.atomAt 3666 (.mul (.n 3814) (.n 2613) (.n 3813)) (by decide +kernel)
  have a3667 := h.atomAt 3667 (.add (.n 3815) (.n 3810) (.n 3814)) (by decide +kernel)
  have a3837 := h.atomAt 3837 (.mul (.n 3985) (.n 2614) (.n 3984)) (by decide +kernel)
  have a3838 := h.atomAt 3838 (.add (.n 3986) (.n 3815) (.n 3985)) (by decide +kernel)
  have a3862 := h.atomAt 3862 (.mul (.n 4010) (.n 2615) (.n 4009)) (by decide +kernel)
  have a3863 := h.atomAt 3863 (.add (.n 4011) (.n 3986) (.n 4010)) (by decide +kernel)
  have a3871 := h.atomAt 3871 (.mul (.n 4019) (.n 2616) (.n 4018)) (by decide +kernel)
  have a3872 := h.atomAt 3872 (.add (.n 4020) (.n 4011) (.n 4019)) (by decide +kernel)
  simp only [Atom.Holds] at a3873 a3874 a3875 a3876 a3877 a3878 a3879 a3660 a3661 a3662 a3663 a3664 a3665 a3666 a3667 a3837 a3838 a3862 a3863 a3871 a3872
  have v3749 : σ (.n 3749) = ev 5 := by
    rw [← hev 5 (by norm_num)]; exact (vt_eval h (k := 52) (by norm_num)).2.2
  have v3790 : σ (.n 3790) = ev 12 := by
    rw [← hev 12 (by norm_num)]; exact (vt_eval h (k := 59) (by norm_num)).2.2
  have v3807 : σ (.n 3807) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 60) (by norm_num)).2.2
  refine ⟨a3873, by rw [← a3874]; exact a3875, by rw [← a3876]; exact a3877, ?_⟩
  rw [a3879, a3878, a3872, a3871, a3863, a3862, a3838, a3837, a3667, a3666, a3665, a3664, a3663, a3662, a3661,
    a3660, v3749, v3790, v3807]

set_option maxRecDepth 10000 in
/-- Table 5's air term: its weight `cprod[x]·peq[τ]` with `g^n = x·τ` (`τ = kb[7]`), times
its form value. -/
theorem vtAir5 {rd : Reader} {σ : Val} (h : VtH rd σ)
    : σ (.n 2545) = σ (.n 5945) * σ (.n 33) ∧
      LoadHolds rd (σ (.n 2631) * σ (.n 5945)) 0 (σ (.n 5947)) ∧
      LoadHolds rd (σ (.n 2656) * σ (.n 33)) 0 (σ (.n 5949)) ∧
      σ (.n 5951) = σ (.n 5947) * σ (.n 5949) *
        (((σ (.n 2614) * σ (.n 5774)) + (σ (.n 2615) * σ (.n 5887))) + (σ (.n 2616) * σ (.n 5942))) := by
  have a5521 := h.atomAt 5521 (.mul (.n 2545) (.n 5945) (.n 33)) (by decide +kernel)
  have a5522 := h.atomAt 5522 (.mul (.n 5946) (.n 2631) (.n 5945)) (by decide +kernel)
  have a5523 := h.atomAt 5523 (.load (.n 5947) (.n 5946) 0) (by decide +kernel)
  have a5524 := h.atomAt 5524 (.mul (.n 5948) (.n 2656) (.n 33)) (by decide +kernel)
  have a5525 := h.atomAt 5525 (.load (.n 5949) (.n 5948) 0) (by decide +kernel)
  have a5526 := h.atomAt 5526 (.mul (.n 5950) (.n 5947) (.n 5949)) (by decide +kernel)
  have a5527 := h.atomAt 5527 (.mul (.n 5951) (.n 5950) (.n 5944)) (by decide +kernel)
  have a5351 := h.atomAt 5351 (.mul (.n 5775) (.n 2614) (.n 5774)) (by decide +kernel)
  have a5464 := h.atomAt 5464 (.mul (.n 5888) (.n 2615) (.n 5887)) (by decide +kernel)
  have a5465 := h.atomAt 5465 (.add (.n 5889) (.n 5775) (.n 5888)) (by decide +kernel)
  have a5519 := h.atomAt 5519 (.mul (.n 5943) (.n 2616) (.n 5942)) (by decide +kernel)
  have a5520 := h.atomAt 5520 (.add (.n 5944) (.n 5889) (.n 5943)) (by decide +kernel)
  simp only [Atom.Holds] at a5521 a5522 a5523 a5524 a5525 a5526 a5527 a5351 a5464 a5465 a5519 a5520
  refine ⟨a5521, by rw [← a5522]; exact a5523, by rw [← a5524]; exact a5525, ?_⟩
  rw [a5527, a5526, a5520, a5519, a5465, a5464, a5351]

set_option maxRecDepth 10000 in
/-- **The air check**: the sumcheck's final claim is the six tables' air terms' sum. -/
theorem vt_air_total {rd : Reader} {σ : Val} (h : VtH rd σ) :
    σ (.n 2653) = σ (.n 2938) + σ (.n 3227) + σ (.n 3400) + σ (.n 3698) + σ (.n 4027) + σ (.n 5951) := by
  have a5528 := h.atomAt 5528 (.add (.n 5952) (.n 4028) (.n 5951)) (by decide +kernel)
  have a3880 := h.atomAt 3880 (.add (.n 4028) (.n 3699) (.n 4027)) (by decide +kernel)
  have a3599 := h.atomAt 3599 (.add (.n 3699) (.n 3401) (.n 3698)) (by decide +kernel)
  have a3337 := h.atomAt 3337 (.add (.n 3401) (.n 3228) (.n 3400)) (by decide +kernel)
  have a3188 := h.atomAt 3188 (.add (.n 3228) (.n 2938) (.n 3227)) (by decide +kernel)
  have a5529 := h.atomAt 5529 (.assertEq (.n 5952) (.n 2653)) (by decide +kernel)
  simp only [Atom.Holds] at a5528 a3880 a3599 a3337 a3188 a5529
  rw [eq_neg_of_add_eq_zero_right a5529, CharTwo.neg_eq, a5528, a3880, a3599, a3337, a3188]

end
end LeanVM.Guest.B1.Tables
