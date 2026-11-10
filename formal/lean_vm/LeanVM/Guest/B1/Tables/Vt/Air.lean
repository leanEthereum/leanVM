/-
  LeanVM.Guest.B1.Tables.Vt.Air

  `verify_tables`' air check: each table's weight and form value, and their sum the table
  sumcheck's final claim.
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
    : σ (.n 2516) = σ (.n 2996) * σ (.n 30) ∧
      LoadHolds rd (σ (.n 2608) * σ (.n 2996)) 0 (σ (.n 2998)) ∧
      LoadHolds rd (σ (.n 2629) * σ (.n 30)) 0 (σ (.n 3000)) ∧
      σ (.n 3002) = σ (.n 2998) * σ (.n 3000) *
        (((σ (.n 2591) * σ (.n 2953)) + (σ (.n 2592) * σ (.n 2984))) + (σ (.n 2593) * σ (.n 2993))) := by
  have a3002 := h.atomAt 3002 (.mul (.n 2516) (.n 2996) (.n 30)) (by decide +kernel)
  have a3003 := h.atomAt 3003 (.mul (.n 2997) (.n 2608) (.n 2996)) (by decide +kernel)
  have a3004 := h.atomAt 3004 (.load (.n 2998) (.n 2997) 0) (by decide +kernel)
  have a3005 := h.atomAt 3005 (.mul (.n 2999) (.n 2629) (.n 30)) (by decide +kernel)
  have a3006 := h.atomAt 3006 (.load (.n 3000) (.n 2999) 0) (by decide +kernel)
  have a3007 := h.atomAt 3007 (.mul (.n 3001) (.n 2998) (.n 3000)) (by decide +kernel)
  have a3008 := h.atomAt 3008 (.mul (.n 3002) (.n 3001) (.n 2995)) (by decide +kernel)
  have a2960 := h.atomAt 2960 (.mul (.n 2954) (.n 2591) (.n 2953)) (by decide +kernel)
  have a2991 := h.atomAt 2991 (.mul (.n 2985) (.n 2592) (.n 2984)) (by decide +kernel)
  have a2992 := h.atomAt 2992 (.add (.n 2986) (.n 2954) (.n 2985)) (by decide +kernel)
  have a3000 := h.atomAt 3000 (.mul (.n 2994) (.n 2593) (.n 2993)) (by decide +kernel)
  have a3001 := h.atomAt 3001 (.add (.n 2995) (.n 2986) (.n 2994)) (by decide +kernel)
  simp only [Atom.Holds] at a3002 a3003 a3004 a3005 a3006 a3007 a3008 a2960 a2991 a2992 a3000 a3001
  refine ⟨a3002, by rw [← a3003]; exact a3004, by rw [← a3005]; exact a3006, ?_⟩
  rw [a3008, a3007, a3001, a3000, a2992, a2991, a2960]

set_option maxRecDepth 10000 in
/-- Table 1's air term: its weight `cprod[x]·peq[τ]` with `g^n = x·τ` (`τ = kb[3]`), times
its form value. -/
theorem vtAir1 {rd : Reader} {σ : Val} (h : VtH rd σ)
    : σ (.n 2516) = σ (.n 3401) * σ (.n 31) ∧
      LoadHolds rd (σ (.n 2608) * σ (.n 3401)) 0 (σ (.n 3403)) ∧
      LoadHolds rd (σ (.n 2629) * σ (.n 31)) 0 (σ (.n 3405)) ∧
      σ (.n 3407) = σ (.n 3403) * σ (.n 3405) *
        (((σ (.n 2591) * σ (.n 3358)) + (σ (.n 2592) * σ (.n 3389))) + (σ (.n 2593) * σ (.n 3398))) := by
  have a3344 := h.atomAt 3344 (.mul (.n 2516) (.n 3401) (.n 31)) (by decide +kernel)
  have a3345 := h.atomAt 3345 (.mul (.n 3402) (.n 2608) (.n 3401)) (by decide +kernel)
  have a3346 := h.atomAt 3346 (.load (.n 3403) (.n 3402) 0) (by decide +kernel)
  have a3347 := h.atomAt 3347 (.mul (.n 3404) (.n 2629) (.n 31)) (by decide +kernel)
  have a3348 := h.atomAt 3348 (.load (.n 3405) (.n 3404) 0) (by decide +kernel)
  have a3349 := h.atomAt 3349 (.mul (.n 3406) (.n 3403) (.n 3405)) (by decide +kernel)
  have a3350 := h.atomAt 3350 (.mul (.n 3407) (.n 3406) (.n 3400)) (by decide +kernel)
  have a3302 := h.atomAt 3302 (.mul (.n 3359) (.n 2591) (.n 3358)) (by decide +kernel)
  have a3333 := h.atomAt 3333 (.mul (.n 3390) (.n 2592) (.n 3389)) (by decide +kernel)
  have a3334 := h.atomAt 3334 (.add (.n 3391) (.n 3359) (.n 3390)) (by decide +kernel)
  have a3342 := h.atomAt 3342 (.mul (.n 3399) (.n 2593) (.n 3398)) (by decide +kernel)
  have a3343 := h.atomAt 3343 (.add (.n 3400) (.n 3391) (.n 3399)) (by decide +kernel)
  simp only [Atom.Holds] at a3344 a3345 a3346 a3347 a3348 a3349 a3350 a3302 a3333 a3334 a3342 a3343
  refine ⟨a3344, by rw [← a3345]; exact a3346, by rw [← a3347]; exact a3348, ?_⟩
  rw [a3350, a3349, a3343, a3342, a3334, a3333, a3302]

set_option maxRecDepth 10000 in
/-- Table 2's air term: its weight `cprod[x]·peq[τ]` with `g^n = x·τ` (`τ = kb[4]`), times
its form value. -/
theorem vtAir2 {rd : Reader} {σ : Val} (h : VtH rd σ)
    : σ (.n 2516) = σ (.n 3618) * σ (.n 32) ∧
      LoadHolds rd (σ (.n 2608) * σ (.n 3618)) 0 (σ (.n 3620)) ∧
      LoadHolds rd (σ (.n 2629) * σ (.n 32)) 0 (σ (.n 3622)) ∧
      σ (.n 3624) = σ (.n 3620) * σ (.n 3622) *
        (((σ (.n 2591) * σ (.n 3591)) + (σ (.n 2592) * σ (.n 3610))) + (σ (.n 2593) * σ (.n 3615))) := by
  have a3529 := h.atomAt 3529 (.mul (.n 2516) (.n 3618) (.n 32)) (by decide +kernel)
  have a3530 := h.atomAt 3530 (.mul (.n 3619) (.n 2608) (.n 3618)) (by decide +kernel)
  have a3531 := h.atomAt 3531 (.load (.n 3620) (.n 3619) 0) (by decide +kernel)
  have a3532 := h.atomAt 3532 (.mul (.n 3621) (.n 2629) (.n 32)) (by decide +kernel)
  have a3533 := h.atomAt 3533 (.load (.n 3622) (.n 3621) 0) (by decide +kernel)
  have a3534 := h.atomAt 3534 (.mul (.n 3623) (.n 3620) (.n 3622)) (by decide +kernel)
  have a3535 := h.atomAt 3535 (.mul (.n 3624) (.n 3623) (.n 3617)) (by decide +kernel)
  have a3503 := h.atomAt 3503 (.mul (.n 3592) (.n 2591) (.n 3591)) (by decide +kernel)
  have a3522 := h.atomAt 3522 (.mul (.n 3611) (.n 2592) (.n 3610)) (by decide +kernel)
  have a3523 := h.atomAt 3523 (.add (.n 3612) (.n 3592) (.n 3611)) (by decide +kernel)
  have a3527 := h.atomAt 3527 (.mul (.n 3616) (.n 2593) (.n 3615)) (by decide +kernel)
  have a3528 := h.atomAt 3528 (.add (.n 3617) (.n 3612) (.n 3616)) (by decide +kernel)
  simp only [Atom.Holds] at a3529 a3530 a3531 a3532 a3533 a3534 a3535 a3503 a3522 a3523 a3527 a3528
  refine ⟨a3529, by rw [← a3530]; exact a3531, by rw [← a3532]; exact a3533, ?_⟩
  rw [a3535, a3534, a3528, a3527, a3523, a3522, a3503]

set_option maxRecDepth 10000 in
/-- Table 3's air term: its weight `cprod[x]·peq[τ]` with `g^n = x·τ` (`τ = kb[5]`), times
its form value. -/
theorem vtAir3 {rd : Reader} {σ : Val} (h : VtH rd σ)
    : σ (.n 2516) = σ (.n 4021) * σ (.n 33) ∧
      LoadHolds rd (σ (.n 2608) * σ (.n 4021)) 0 (σ (.n 4023)) ∧
      LoadHolds rd (σ (.n 2629) * σ (.n 33)) 0 (σ (.n 4025)) ∧
      σ (.n 4027) = σ (.n 4023) * σ (.n 4025) *
        (((σ (.n 2591) * σ (.n 3978)) + (σ (.n 2592) * σ (.n 4009))) + (σ (.n 2593) * σ (.n 4018))) := by
  have a3869 := h.atomAt 3869 (.mul (.n 2516) (.n 4021) (.n 33)) (by decide +kernel)
  have a3870 := h.atomAt 3870 (.mul (.n 4022) (.n 2608) (.n 4021)) (by decide +kernel)
  have a3871 := h.atomAt 3871 (.load (.n 4023) (.n 4022) 0) (by decide +kernel)
  have a3872 := h.atomAt 3872 (.mul (.n 4024) (.n 2629) (.n 33)) (by decide +kernel)
  have a3873 := h.atomAt 3873 (.load (.n 4025) (.n 4024) 0) (by decide +kernel)
  have a3874 := h.atomAt 3874 (.mul (.n 4026) (.n 4023) (.n 4025)) (by decide +kernel)
  have a3875 := h.atomAt 3875 (.mul (.n 4027) (.n 4026) (.n 4020)) (by decide +kernel)
  have a3827 := h.atomAt 3827 (.mul (.n 3979) (.n 2591) (.n 3978)) (by decide +kernel)
  have a3858 := h.atomAt 3858 (.mul (.n 4010) (.n 2592) (.n 4009)) (by decide +kernel)
  have a3859 := h.atomAt 3859 (.add (.n 4011) (.n 3979) (.n 4010)) (by decide +kernel)
  have a3867 := h.atomAt 3867 (.mul (.n 4019) (.n 2593) (.n 4018)) (by decide +kernel)
  have a3868 := h.atomAt 3868 (.add (.n 4020) (.n 4011) (.n 4019)) (by decide +kernel)
  simp only [Atom.Holds] at a3869 a3870 a3871 a3872 a3873 a3874 a3875 a3827 a3858 a3859 a3867 a3868
  refine ⟨a3869, by rw [← a3870]; exact a3871, by rw [← a3872]; exact a3873, ?_⟩
  rw [a3875, a3874, a3868, a3867, a3859, a3858, a3827]

set_option maxRecDepth 10000 in
/-- Table 4's air term: its weight `cprod[x]·peq[τ]` with `g^n = x·τ` (`τ = kb[6]`), times
its form value. -/
theorem vtAir4 {rd : Reader} {σ : Val} (h : VtH rd σ) {ev : ℕ → E}
    (hev : ∀ c < 14, σ (.n (vtEvB (53 + c))) = ev c)
    : σ (.n 2516) = σ (.n 4419) * σ (.n 34) ∧
      LoadHolds rd (σ (.n 2608) * σ (.n 4419)) 0 (σ (.n 4421)) ∧
      LoadHolds rd (σ (.n 2629) * σ (.n 34)) 0 (σ (.n 4423)) ∧
      σ (.n 4425) = σ (.n 4421) * σ (.n 4423) *
        (((((σ (.n 2589) * (ev 13 + (ev 5 * ev 12))) + (σ (.n 2590) * (ev 5 * (ev 13 + word 1 0)))) + (σ (.n 2591) * σ (.n 4363))) + (σ (.n 2592) * σ (.n 4407))) + (σ (.n 2593) * σ (.n 4416))) := by
  have a4217 := h.atomAt 4217 (.mul (.n 2516) (.n 4419) (.n 34)) (by decide +kernel)
  have a4218 := h.atomAt 4218 (.mul (.n 4420) (.n 2608) (.n 4419)) (by decide +kernel)
  have a4219 := h.atomAt 4219 (.load (.n 4421) (.n 4420) 0) (by decide +kernel)
  have a4220 := h.atomAt 4220 (.mul (.n 4422) (.n 2629) (.n 34)) (by decide +kernel)
  have a4221 := h.atomAt 4221 (.load (.n 4423) (.n 4422) 0) (by decide +kernel)
  have a4222 := h.atomAt 4222 (.mul (.n 4424) (.n 4421) (.n 4423)) (by decide +kernel)
  have a4223 := h.atomAt 4223 (.mul (.n 4425) (.n 4424) (.n 4418)) (by decide +kernel)
  have a4020 := h.atomAt 4020 (.mul (.n 4222) (.n 4107) (.n 4210)) (by decide +kernel)
  have a4021 := h.atomAt 4021 (.add (.n 4223) (.n 4221) (.n 4222)) (by decide +kernel)
  have a4022 := h.atomAt 4022 (.mul (.n 4224) (.n 2589) (.n 4223)) (by decide +kernel)
  have a4023 := h.atomAt 4023 (.const (.n 4225) (word 1 0)) (by decide +kernel)
  have a4024 := h.atomAt 4024 (.add (.n 4226) (.n 4221) (.n 4225)) (by decide +kernel)
  have a4025 := h.atomAt 4025 (.mul (.n 4227) (.n 4107) (.n 4226)) (by decide +kernel)
  have a4026 := h.atomAt 4026 (.mul (.n 4228) (.n 2590) (.n 4227)) (by decide +kernel)
  have a4027 := h.atomAt 4027 (.add (.n 4229) (.n 4224) (.n 4228)) (by decide +kernel)
  have a4162 := h.atomAt 4162 (.mul (.n 4364) (.n 2591) (.n 4363)) (by decide +kernel)
  have a4163 := h.atomAt 4163 (.add (.n 4365) (.n 4229) (.n 4364)) (by decide +kernel)
  have a4206 := h.atomAt 4206 (.mul (.n 4408) (.n 2592) (.n 4407)) (by decide +kernel)
  have a4207 := h.atomAt 4207 (.add (.n 4409) (.n 4365) (.n 4408)) (by decide +kernel)
  have a4215 := h.atomAt 4215 (.mul (.n 4417) (.n 2593) (.n 4416)) (by decide +kernel)
  have a4216 := h.atomAt 4216 (.add (.n 4418) (.n 4409) (.n 4417)) (by decide +kernel)
  simp only [Atom.Holds] at a4217 a4218 a4219 a4220 a4221 a4222 a4223 a4020 a4021 a4022 a4023 a4024 a4025 a4026 a4027 a4162 a4163 a4206 a4207 a4215 a4216
  have v4107 : σ (.n 4107) = ev 5 := by
    rw [← hev 5 (by norm_num)]; exact (vt_eval h (k := 58) (by norm_num)).2.2
  have v4210 : σ (.n 4210) = ev 12 := by
    rw [← hev 12 (by norm_num)]; exact (vt_eval h (k := 65) (by norm_num)).2.2
  have v4221 : σ (.n 4221) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 66) (by norm_num)).2.2
  refine ⟨a4217, by rw [← a4218]; exact a4219, by rw [← a4220]; exact a4221, ?_⟩
  rw [a4223, a4222, a4216, a4215, a4207, a4206, a4163, a4162, a4027, a4026, a4025, a4024, a4023, a4022, a4021,
    a4020, v4107, v4210, v4221]

set_option maxRecDepth 10000 in
/-- Table 5's air term: its weight `cprod[x]·peq[τ]` with `g^n = x·τ` (`τ = kb[7]`), times
its form value. -/
theorem vtAir5 {rd : Reader} {σ : Val} (h : VtH rd σ)
    : σ (.n 2516) = σ (.n 6914) * σ (.n 35) ∧
      LoadHolds rd (σ (.n 2608) * σ (.n 6914)) 0 (σ (.n 6916)) ∧
      LoadHolds rd (σ (.n 2629) * σ (.n 35)) 0 (σ (.n 6918)) ∧
      σ (.n 6920) = σ (.n 6916) * σ (.n 6918) *
        (((σ (.n 2591) * σ (.n 6675)) + (σ (.n 2592) * σ (.n 6856))) + (σ (.n 2593) * σ (.n 6911))) := by
  have a6344 := h.atomAt 6344 (.mul (.n 2516) (.n 6914) (.n 35)) (by decide +kernel)
  have a6345 := h.atomAt 6345 (.mul (.n 6915) (.n 2608) (.n 6914)) (by decide +kernel)
  have a6346 := h.atomAt 6346 (.load (.n 6916) (.n 6915) 0) (by decide +kernel)
  have a6347 := h.atomAt 6347 (.mul (.n 6917) (.n 2629) (.n 35)) (by decide +kernel)
  have a6348 := h.atomAt 6348 (.load (.n 6918) (.n 6917) 0) (by decide +kernel)
  have a6349 := h.atomAt 6349 (.mul (.n 6919) (.n 6916) (.n 6918)) (by decide +kernel)
  have a6350 := h.atomAt 6350 (.mul (.n 6920) (.n 6919) (.n 6913)) (by decide +kernel)
  have a6106 := h.atomAt 6106 (.mul (.n 6676) (.n 2591) (.n 6675)) (by decide +kernel)
  have a6287 := h.atomAt 6287 (.mul (.n 6857) (.n 2592) (.n 6856)) (by decide +kernel)
  have a6288 := h.atomAt 6288 (.add (.n 6858) (.n 6676) (.n 6857)) (by decide +kernel)
  have a6342 := h.atomAt 6342 (.mul (.n 6912) (.n 2593) (.n 6911)) (by decide +kernel)
  have a6343 := h.atomAt 6343 (.add (.n 6913) (.n 6858) (.n 6912)) (by decide +kernel)
  simp only [Atom.Holds] at a6344 a6345 a6346 a6347 a6348 a6349 a6350 a6106 a6287 a6288 a6342 a6343
  refine ⟨a6344, by rw [← a6345]; exact a6346, by rw [← a6347]; exact a6348, ?_⟩
  rw [a6350, a6349, a6343, a6342, a6288, a6287, a6106]

set_option maxRecDepth 10000 in
/-- **The air check**: the sumcheck's final claim is the six tables' air terms' sum. -/
theorem vt_air_total {rd : Reader} {σ : Val} (h : VtH rd σ) :
    σ (.n 2626) = σ (.n 3002) + σ (.n 3407) + σ (.n 3624) + σ (.n 4027) + σ (.n 4425) + σ (.n 6920) := by
  have a6351 := h.atomAt 6351 (.add (.n 6921) (.n 4426) (.n 6920)) (by decide +kernel)
  have a4224 := h.atomAt 4224 (.add (.n 4426) (.n 4028) (.n 4425)) (by decide +kernel)
  have a3876 := h.atomAt 3876 (.add (.n 4028) (.n 3625) (.n 4027)) (by decide +kernel)
  have a3536 := h.atomAt 3536 (.add (.n 3625) (.n 3408) (.n 3624)) (by decide +kernel)
  have a3351 := h.atomAt 3351 (.add (.n 3408) (.n 3002) (.n 3407)) (by decide +kernel)
  have a6352 := h.atomAt 6352 (.assertEq (.n 6921) (.n 2626)) (by decide +kernel)
  simp only [Atom.Holds] at a6351 a4224 a3876 a3536 a3351 a6352
  rw [eq_neg_of_add_eq_zero_right a6352, CharTwo.neg_eq, a6351, a4224, a3876, a3536, a3351]

end
end LeanVM.Guest.B1.Tables
