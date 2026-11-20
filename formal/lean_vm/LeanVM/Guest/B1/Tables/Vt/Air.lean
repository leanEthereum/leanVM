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
    : σ (.n 2545) = σ (.n 2928) * σ (.n 28) ∧
      LoadHolds rd (σ (.n 2631) * σ (.n 2928)) 0 (σ (.n 2930)) ∧
      LoadHolds rd (σ (.n 2653) * σ (.n 28)) 0 (σ (.n 2932)) ∧
      σ (.n 2934) = σ (.n 2930) * σ (.n 2932) *
        (((σ (.n 2614) * σ (.n 2895)) + (σ (.n 2615) * σ (.n 2916))) + (σ (.n 2616) * σ (.n 2925))) := by
  have a2923 := h.atomAt 2923 (.mul (.n 2545) (.n 2928) (.n 28)) (by decide +kernel)
  have a2924 := h.atomAt 2924 (.mul (.n 2929) (.n 2631) (.n 2928)) (by decide +kernel)
  have a2925 := h.atomAt 2925 (.load (.n 2930) (.n 2929) 0) (by decide +kernel)
  have a2926 := h.atomAt 2926 (.mul (.n 2931) (.n 2653) (.n 28)) (by decide +kernel)
  have a2927 := h.atomAt 2927 (.load (.n 2932) (.n 2931) 0) (by decide +kernel)
  have a2928 := h.atomAt 2928 (.mul (.n 2933) (.n 2930) (.n 2932)) (by decide +kernel)
  have a2929 := h.atomAt 2929 (.mul (.n 2934) (.n 2933) (.n 2927)) (by decide +kernel)
  have a2891 := h.atomAt 2891 (.mul (.n 2896) (.n 2614) (.n 2895)) (by decide +kernel)
  have a2912 := h.atomAt 2912 (.mul (.n 2917) (.n 2615) (.n 2916)) (by decide +kernel)
  have a2913 := h.atomAt 2913 (.add (.n 2918) (.n 2896) (.n 2917)) (by decide +kernel)
  have a2921 := h.atomAt 2921 (.mul (.n 2926) (.n 2616) (.n 2925)) (by decide +kernel)
  have a2922 := h.atomAt 2922 (.add (.n 2927) (.n 2918) (.n 2926)) (by decide +kernel)
  simp only [Atom.Holds] at a2923 a2924 a2925 a2926 a2927 a2928 a2929 a2891 a2912 a2913 a2921 a2922
  refine ⟨a2923, by rw [← a2924]; exact a2925, by rw [← a2926]; exact a2927, ?_⟩
  rw [a2929, a2928, a2922, a2921, a2913, a2912, a2891]

set_option maxRecDepth 10000 in
/-- Table 1's air term: its weight `cprod[x]·peq[τ]` with `g^n = x·τ` (`τ = kb[3]`), times
its form value. -/
theorem vtAir1 {rd : Reader} {σ : Val} (h : VtH rd σ)
    : σ (.n 2545) = σ (.n 3217) * σ (.n 29) ∧
      LoadHolds rd (σ (.n 2631) * σ (.n 3217)) 0 (σ (.n 3219)) ∧
      LoadHolds rd (σ (.n 2653) * σ (.n 29)) 0 (σ (.n 3221)) ∧
      σ (.n 3223) = σ (.n 3219) * σ (.n 3221) *
        (((σ (.n 2614) * σ (.n 3184)) + (σ (.n 2615) * σ (.n 3205))) + (σ (.n 2616) * σ (.n 3214))) := by
  have a3176 := h.atomAt 3176 (.mul (.n 2545) (.n 3217) (.n 29)) (by decide +kernel)
  have a3177 := h.atomAt 3177 (.mul (.n 3218) (.n 2631) (.n 3217)) (by decide +kernel)
  have a3178 := h.atomAt 3178 (.load (.n 3219) (.n 3218) 0) (by decide +kernel)
  have a3179 := h.atomAt 3179 (.mul (.n 3220) (.n 2653) (.n 29)) (by decide +kernel)
  have a3180 := h.atomAt 3180 (.load (.n 3221) (.n 3220) 0) (by decide +kernel)
  have a3181 := h.atomAt 3181 (.mul (.n 3222) (.n 3219) (.n 3221)) (by decide +kernel)
  have a3182 := h.atomAt 3182 (.mul (.n 3223) (.n 3222) (.n 3216)) (by decide +kernel)
  have a3144 := h.atomAt 3144 (.mul (.n 3185) (.n 2614) (.n 3184)) (by decide +kernel)
  have a3165 := h.atomAt 3165 (.mul (.n 3206) (.n 2615) (.n 3205)) (by decide +kernel)
  have a3166 := h.atomAt 3166 (.add (.n 3207) (.n 3185) (.n 3206)) (by decide +kernel)
  have a3174 := h.atomAt 3174 (.mul (.n 3215) (.n 2616) (.n 3214)) (by decide +kernel)
  have a3175 := h.atomAt 3175 (.add (.n 3216) (.n 3207) (.n 3215)) (by decide +kernel)
  simp only [Atom.Holds] at a3176 a3177 a3178 a3179 a3180 a3181 a3182 a3144 a3165 a3166 a3174 a3175
  refine ⟨a3176, by rw [← a3177]; exact a3178, by rw [← a3179]; exact a3180, ?_⟩
  rw [a3182, a3181, a3175, a3174, a3166, a3165, a3144]

set_option maxRecDepth 10000 in
/-- Table 2's air term: its weight `cprod[x]·peq[τ]` with `g^n = x·τ` (`τ = kb[4]`), times
its form value. -/
theorem vtAir2 {rd : Reader} {σ : Val} (h : VtH rd σ)
    : σ (.n 2545) = σ (.n 3390) * σ (.n 30) ∧
      LoadHolds rd (σ (.n 2631) * σ (.n 3390)) 0 (σ (.n 3392)) ∧
      LoadHolds rd (σ (.n 2653) * σ (.n 30)) 0 (σ (.n 3394)) ∧
      σ (.n 3396) = σ (.n 3392) * σ (.n 3394) *
        (((σ (.n 2614) * σ (.n 3369)) + (σ (.n 2615) * σ (.n 3382))) + (σ (.n 2616) * σ (.n 3387))) := by
  have a3325 := h.atomAt 3325 (.mul (.n 2545) (.n 3390) (.n 30)) (by decide +kernel)
  have a3326 := h.atomAt 3326 (.mul (.n 3391) (.n 2631) (.n 3390)) (by decide +kernel)
  have a3327 := h.atomAt 3327 (.load (.n 3392) (.n 3391) 0) (by decide +kernel)
  have a3328 := h.atomAt 3328 (.mul (.n 3393) (.n 2653) (.n 30)) (by decide +kernel)
  have a3329 := h.atomAt 3329 (.load (.n 3394) (.n 3393) 0) (by decide +kernel)
  have a3330 := h.atomAt 3330 (.mul (.n 3395) (.n 3392) (.n 3394)) (by decide +kernel)
  have a3331 := h.atomAt 3331 (.mul (.n 3396) (.n 3395) (.n 3389)) (by decide +kernel)
  have a3305 := h.atomAt 3305 (.mul (.n 3370) (.n 2614) (.n 3369)) (by decide +kernel)
  have a3318 := h.atomAt 3318 (.mul (.n 3383) (.n 2615) (.n 3382)) (by decide +kernel)
  have a3319 := h.atomAt 3319 (.add (.n 3384) (.n 3370) (.n 3383)) (by decide +kernel)
  have a3323 := h.atomAt 3323 (.mul (.n 3388) (.n 2616) (.n 3387)) (by decide +kernel)
  have a3324 := h.atomAt 3324 (.add (.n 3389) (.n 3384) (.n 3388)) (by decide +kernel)
  simp only [Atom.Holds] at a3325 a3326 a3327 a3328 a3329 a3330 a3331 a3305 a3318 a3319 a3323 a3324
  refine ⟨a3325, by rw [← a3326]; exact a3327, by rw [← a3328]; exact a3329, ?_⟩
  rw [a3331, a3330, a3324, a3323, a3319, a3318, a3305]

set_option maxRecDepth 10000 in
/-- Table 3's air term: its weight `cprod[x]·peq[τ]` with `g^n = x·τ` (`τ = kb[5]`), times
its form value. -/
theorem vtAir3 {rd : Reader} {σ : Val} (h : VtH rd σ)
    : σ (.n 2545) = σ (.n 3688) * σ (.n 31) ∧
      LoadHolds rd (σ (.n 2631) * σ (.n 3688)) 0 (σ (.n 3690)) ∧
      LoadHolds rd (σ (.n 2653) * σ (.n 31)) 0 (σ (.n 3692)) ∧
      σ (.n 3694) = σ (.n 3690) * σ (.n 3692) *
        (((σ (.n 2614) * σ (.n 3655)) + (σ (.n 2615) * σ (.n 3676))) + (σ (.n 2616) * σ (.n 3685))) := by
  have a3587 := h.atomAt 3587 (.mul (.n 2545) (.n 3688) (.n 31)) (by decide +kernel)
  have a3588 := h.atomAt 3588 (.mul (.n 3689) (.n 2631) (.n 3688)) (by decide +kernel)
  have a3589 := h.atomAt 3589 (.load (.n 3690) (.n 3689) 0) (by decide +kernel)
  have a3590 := h.atomAt 3590 (.mul (.n 3691) (.n 2653) (.n 31)) (by decide +kernel)
  have a3591 := h.atomAt 3591 (.load (.n 3692) (.n 3691) 0) (by decide +kernel)
  have a3592 := h.atomAt 3592 (.mul (.n 3693) (.n 3690) (.n 3692)) (by decide +kernel)
  have a3593 := h.atomAt 3593 (.mul (.n 3694) (.n 3693) (.n 3687)) (by decide +kernel)
  have a3555 := h.atomAt 3555 (.mul (.n 3656) (.n 2614) (.n 3655)) (by decide +kernel)
  have a3576 := h.atomAt 3576 (.mul (.n 3677) (.n 2615) (.n 3676)) (by decide +kernel)
  have a3577 := h.atomAt 3577 (.add (.n 3678) (.n 3656) (.n 3677)) (by decide +kernel)
  have a3585 := h.atomAt 3585 (.mul (.n 3686) (.n 2616) (.n 3685)) (by decide +kernel)
  have a3586 := h.atomAt 3586 (.add (.n 3687) (.n 3678) (.n 3686)) (by decide +kernel)
  simp only [Atom.Holds] at a3587 a3588 a3589 a3590 a3591 a3592 a3593 a3555 a3576 a3577 a3585 a3586
  refine ⟨a3587, by rw [← a3588]; exact a3589, by rw [← a3590]; exact a3591, ?_⟩
  rw [a3593, a3592, a3586, a3585, a3577, a3576, a3555]

set_option maxRecDepth 10000 in
/-- Table 4's air term: its weight `cprod[x]·peq[τ]` with `g^n = x·τ` (`τ = kb[6]`), times
its form value. -/
theorem vtAir4 {rd : Reader} {σ : Val} (h : VtH rd σ) {ev : ℕ → E}
    (hev : ∀ c < 14, σ (.n (vtEvB (47 + c))) = ev c)
    : σ (.n 2545) = σ (.n 4017) * σ (.n 32) ∧
      LoadHolds rd (σ (.n 2631) * σ (.n 4017)) 0 (σ (.n 4019)) ∧
      LoadHolds rd (σ (.n 2653) * σ (.n 32)) 0 (σ (.n 4021)) ∧
      σ (.n 4023) = σ (.n 4019) * σ (.n 4021) *
        (((((σ (.n 2612) * (ev 13 + (ev 5 * ev 12))) + (σ (.n 2613) * (ev 5 * (ev 13 + word 1 0)))) + (σ (.n 2614) * σ (.n 3980))) + (σ (.n 2615) * σ (.n 4005))) + (σ (.n 2616) * σ (.n 4014))) := by
  have a3868 := h.atomAt 3868 (.mul (.n 2545) (.n 4017) (.n 32)) (by decide +kernel)
  have a3869 := h.atomAt 3869 (.mul (.n 4018) (.n 2631) (.n 4017)) (by decide +kernel)
  have a3870 := h.atomAt 3870 (.load (.n 4019) (.n 4018) 0) (by decide +kernel)
  have a3871 := h.atomAt 3871 (.mul (.n 4020) (.n 2653) (.n 32)) (by decide +kernel)
  have a3872 := h.atomAt 3872 (.load (.n 4021) (.n 4020) 0) (by decide +kernel)
  have a3873 := h.atomAt 3873 (.mul (.n 4022) (.n 4019) (.n 4021)) (by decide +kernel)
  have a3874 := h.atomAt 3874 (.mul (.n 4023) (.n 4022) (.n 4016)) (by decide +kernel)
  have a3655 := h.atomAt 3655 (.mul (.n 3804) (.n 3745) (.n 3786)) (by decide +kernel)
  have a3656 := h.atomAt 3656 (.add (.n 3805) (.n 3803) (.n 3804)) (by decide +kernel)
  have a3657 := h.atomAt 3657 (.mul (.n 3806) (.n 2612) (.n 3805)) (by decide +kernel)
  have a3658 := h.atomAt 3658 (.const (.n 3807) (word 1 0)) (by decide +kernel)
  have a3659 := h.atomAt 3659 (.add (.n 3808) (.n 3803) (.n 3807)) (by decide +kernel)
  have a3660 := h.atomAt 3660 (.mul (.n 3809) (.n 3745) (.n 3808)) (by decide +kernel)
  have a3661 := h.atomAt 3661 (.mul (.n 3810) (.n 2613) (.n 3809)) (by decide +kernel)
  have a3662 := h.atomAt 3662 (.add (.n 3811) (.n 3806) (.n 3810)) (by decide +kernel)
  have a3832 := h.atomAt 3832 (.mul (.n 3981) (.n 2614) (.n 3980)) (by decide +kernel)
  have a3833 := h.atomAt 3833 (.add (.n 3982) (.n 3811) (.n 3981)) (by decide +kernel)
  have a3857 := h.atomAt 3857 (.mul (.n 4006) (.n 2615) (.n 4005)) (by decide +kernel)
  have a3858 := h.atomAt 3858 (.add (.n 4007) (.n 3982) (.n 4006)) (by decide +kernel)
  have a3866 := h.atomAt 3866 (.mul (.n 4015) (.n 2616) (.n 4014)) (by decide +kernel)
  have a3867 := h.atomAt 3867 (.add (.n 4016) (.n 4007) (.n 4015)) (by decide +kernel)
  simp only [Atom.Holds] at a3868 a3869 a3870 a3871 a3872 a3873 a3874 a3655 a3656 a3657 a3658 a3659 a3660 a3661 a3662 a3832 a3833 a3857 a3858 a3866 a3867
  have v3745 : σ (.n 3745) = ev 5 := by
    rw [← hev 5 (by norm_num)]; exact (vt_eval h (k := 52) (by norm_num)).2.2
  have v3786 : σ (.n 3786) = ev 12 := by
    rw [← hev 12 (by norm_num)]; exact (vt_eval h (k := 59) (by norm_num)).2.2
  have v3803 : σ (.n 3803) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 60) (by norm_num)).2.2
  refine ⟨a3868, by rw [← a3869]; exact a3870, by rw [← a3871]; exact a3872, ?_⟩
  rw [a3874, a3873, a3867, a3866, a3858, a3857, a3833, a3832, a3662, a3661, a3660, a3659, a3658, a3657, a3656,
    a3655, v3745, v3786, v3803]

set_option maxRecDepth 10000 in
/-- Table 5's air term: its weight `cprod[x]·peq[τ]` with `g^n = x·τ` (`τ = kb[7]`), times
its form value. -/
theorem vtAir5 {rd : Reader} {σ : Val} (h : VtH rd σ)
    : σ (.n 2545) = σ (.n 5941) * σ (.n 33) ∧
      LoadHolds rd (σ (.n 2631) * σ (.n 5941)) 0 (σ (.n 5943)) ∧
      LoadHolds rd (σ (.n 2653) * σ (.n 33)) 0 (σ (.n 5945)) ∧
      σ (.n 5947) = σ (.n 5943) * σ (.n 5945) *
        (((σ (.n 2614) * σ (.n 5770)) + (σ (.n 2615) * σ (.n 5883))) + (σ (.n 2616) * σ (.n 5938))) := by
  have a5516 := h.atomAt 5516 (.mul (.n 2545) (.n 5941) (.n 33)) (by decide +kernel)
  have a5517 := h.atomAt 5517 (.mul (.n 5942) (.n 2631) (.n 5941)) (by decide +kernel)
  have a5518 := h.atomAt 5518 (.load (.n 5943) (.n 5942) 0) (by decide +kernel)
  have a5519 := h.atomAt 5519 (.mul (.n 5944) (.n 2653) (.n 33)) (by decide +kernel)
  have a5520 := h.atomAt 5520 (.load (.n 5945) (.n 5944) 0) (by decide +kernel)
  have a5521 := h.atomAt 5521 (.mul (.n 5946) (.n 5943) (.n 5945)) (by decide +kernel)
  have a5522 := h.atomAt 5522 (.mul (.n 5947) (.n 5946) (.n 5940)) (by decide +kernel)
  have a5346 := h.atomAt 5346 (.mul (.n 5771) (.n 2614) (.n 5770)) (by decide +kernel)
  have a5459 := h.atomAt 5459 (.mul (.n 5884) (.n 2615) (.n 5883)) (by decide +kernel)
  have a5460 := h.atomAt 5460 (.add (.n 5885) (.n 5771) (.n 5884)) (by decide +kernel)
  have a5514 := h.atomAt 5514 (.mul (.n 5939) (.n 2616) (.n 5938)) (by decide +kernel)
  have a5515 := h.atomAt 5515 (.add (.n 5940) (.n 5885) (.n 5939)) (by decide +kernel)
  simp only [Atom.Holds] at a5516 a5517 a5518 a5519 a5520 a5521 a5522 a5346 a5459 a5460 a5514 a5515
  refine ⟨a5516, by rw [← a5517]; exact a5518, by rw [← a5519]; exact a5520, ?_⟩
  rw [a5522, a5521, a5515, a5514, a5460, a5459, a5346]

set_option maxRecDepth 10000 in
/-- **The air check**: the sumcheck's final claim is the six tables' air terms' sum. -/
theorem vt_air_total {rd : Reader} {σ : Val} (h : VtH rd σ) :
    σ (.n 2650) = σ (.n 2934) + σ (.n 3223) + σ (.n 3396) + σ (.n 3694) + σ (.n 4023) + σ (.n 5947) := by
  have a5523 := h.atomAt 5523 (.add (.n 5948) (.n 4024) (.n 5947)) (by decide +kernel)
  have a3875 := h.atomAt 3875 (.add (.n 4024) (.n 3695) (.n 4023)) (by decide +kernel)
  have a3594 := h.atomAt 3594 (.add (.n 3695) (.n 3397) (.n 3694)) (by decide +kernel)
  have a3332 := h.atomAt 3332 (.add (.n 3397) (.n 3224) (.n 3396)) (by decide +kernel)
  have a3183 := h.atomAt 3183 (.add (.n 3224) (.n 2934) (.n 3223)) (by decide +kernel)
  have a5524 := h.atomAt 5524 (.assertEq (.n 5948) (.n 2650)) (by decide +kernel)
  simp only [Atom.Holds] at a5523 a3875 a3594 a3332 a3183 a5524
  rw [eq_neg_of_add_eq_zero_right a5524, CharTwo.neg_eq, a5523, a3875, a3594, a3332, a3183]

end
end LeanVM.Guest.B1.Tables
