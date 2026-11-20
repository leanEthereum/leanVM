/-
  LeanVM.Guest.B1.Tables.Vt.FormsT3

  Table 3's forms on the three sides, from the guest's statements: each block's value from its
  baked terms, the table's form the blocks' selectors times their values.

  Do not edit: `scripts/b1c-vt/all.py` writes it (`regen-guest.sh`, step `vt`).
-/

module

public import LeanVM.Guest.B1.Tables.Vt.FormsDiff
public import LeanVM.Guest.B1.Tables.Vt.PullSels
public import LeanVM.Guest.B1.Tables.Vt.Pi

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

set_option maxRecDepth 10000 in
theorem vtB03_0 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (33 + c))) = ev c) :
    σ (.n 3575) = σ (.n 959) * vtBlockVal (σ (.n 14)) W ev
      [[([], 1)], [([0], 2)], [([1], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 3392 [
    .atom (.const (.n 3493) (word 1 0)),
    .atom (.const (.n 3494) (word 2 0)),
    .atom (.mul (.n 3495) (.n 3494) (.n 3401)),
    .atom (.copy (.n 3496) (.n 3495)),
    .atom (.copy (.n 3497) (.n 3405))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a3392, a3393, a3394, a3395, a3396, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 3465 [
    .atom (.load (.n 3566) (.n 13) 0),
    .atom (.mul (.n 3567) (.n 3566) (.n 3493)),
    .atom (.load (.n 3568) (.n 13) 1),
    .atom (.mul (.n 3569) (.n 3568) (.n 3496)),
    .atom (.add (.n 3570) (.n 3567) (.n 3569)),
    .atom (.load (.n 3571) (.n 13) 2),
    .atom (.mul (.n 3572) (.n 3571) (.n 3497)),
    .atom (.add (.n 3573) (.n 3570) (.n 3572)),
    .atom (.add (.n 3574) (.n 14) (.n 3573)),
    .atom (.mul (.n 3575) (.n 959) (.n 3574))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a3465, a3466, a3467, a3468, a3469, a3470, a3471, a3472, a3473, a3474, -⟩ := hs1
  have e3465 := tb_loadHolds_unique a3465 (hw 0 (by norm_num))
  have e3467 := tb_loadHolds_unique a3467 (hw 1 (by norm_num))
  have e3470 := tb_loadHolds_unique a3470 (hw 2 (by norm_num))
  have v3401 : σ (.n 3401) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_eval h (k := 33) (by norm_num)).2.2
  have v3405 : σ (.n 3405) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 34) (by norm_num)).2.2
  have hB : σ (.n 3574) = vtBlockVal (σ (.n 14)) W ev [[([], 1)], [([0], 2)], [([1], 1)]] := by
    simp only [v3405, v3401, a3473, a3472, a3471, e3470, a3469, a3468, e3467, a3466, e3465, a3396, a3395,
      a3394, a3393, a3392]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a3474, hB]

set_option maxRecDepth 10000 in
theorem vtB03_1 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (33 + c))) = ev c) :
    σ (.n 3604) = σ (.n 3575) + σ (.n 968) * vtBlockVal (σ (.n 14)) W ev
      [[([], 4)], [([0], 1)], [([13], 2)], [([], 8)], [([2], 1)], [([3], 1)], [([4], 1)], [([5], 1)], [([6], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 3397 [
    .atom (.const (.n 3498) (word 4 0)),
    .atom (.copy (.n 3499) (.n 3401)),
    .atom (.const (.n 3500) (word 2 0)),
    .atom (.mul (.n 3501) (.n 3500) (.n 3492)),
    .atom (.copy (.n 3502) (.n 3501)),
    .atom (.const (.n 3503) (word 8 0)),
    .atom (.copy (.n 3504) (.n 3409)),
    .atom (.copy (.n 3505) (.n 3426)),
    .atom (.copy (.n 3506) (.n 3430)),
    .atom (.copy (.n 3507) (.n 3434)),
    .atom (.copy (.n 3508) (.n 3438))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a3397, a3398, a3399, a3400, a3401, a3402, a3403, a3404, a3405, a3406, a3407, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 3475 [
    .atom (.load (.n 3576) (.n 13) 0),
    .atom (.mul (.n 3577) (.n 3576) (.n 3498)),
    .atom (.load (.n 3578) (.n 13) 1),
    .atom (.mul (.n 3579) (.n 3578) (.n 3499)),
    .atom (.add (.n 3580) (.n 3577) (.n 3579)),
    .atom (.load (.n 3581) (.n 13) 2),
    .atom (.mul (.n 3582) (.n 3581) (.n 3502)),
    .atom (.add (.n 3583) (.n 3580) (.n 3582)),
    .atom (.load (.n 3584) (.n 13) 3),
    .atom (.mul (.n 3585) (.n 3584) (.n 3503)),
    .atom (.add (.n 3586) (.n 3583) (.n 3585)),
    .atom (.load (.n 3587) (.n 13) 4),
    .atom (.mul (.n 3588) (.n 3587) (.n 3504)),
    .atom (.add (.n 3589) (.n 3586) (.n 3588)),
    .atom (.load (.n 3590) (.n 13) 5),
    .atom (.mul (.n 3591) (.n 3590) (.n 3505)),
    .atom (.add (.n 3592) (.n 3589) (.n 3591)),
    .atom (.load (.n 3593) (.n 13) 6),
    .atom (.mul (.n 3594) (.n 3593) (.n 3506)),
    .atom (.add (.n 3595) (.n 3592) (.n 3594)),
    .atom (.load (.n 3596) (.n 13) 7),
    .atom (.mul (.n 3597) (.n 3596) (.n 3507)),
    .atom (.add (.n 3598) (.n 3595) (.n 3597)),
    .atom (.load (.n 3599) (.n 13) 8),
    .atom (.mul (.n 3600) (.n 3599) (.n 3508)),
    .atom (.add (.n 3601) (.n 3598) (.n 3600)),
    .atom (.add (.n 3602) (.n 14) (.n 3601)),
    .atom (.mul (.n 3603) (.n 968) (.n 3602)),
    .atom (.add (.n 3604) (.n 3575) (.n 3603))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a3475, a3476, a3477, a3478, a3479, a3480, a3481, a3482, a3483, a3484, a3485, a3486, a3487, a3488,
    a3489, a3490, a3491, a3492, a3493, a3494, a3495, a3496, a3497, a3498, a3499, a3500, a3501,
    a3502, a3503, -⟩ := hs1
  have e3475 := tb_loadHolds_unique a3475 (hw 0 (by norm_num))
  have e3477 := tb_loadHolds_unique a3477 (hw 1 (by norm_num))
  have e3480 := tb_loadHolds_unique a3480 (hw 2 (by norm_num))
  have e3483 := tb_loadHolds_unique a3483 (hw 3 (by norm_num))
  have e3486 := tb_loadHolds_unique a3486 (hw 4 (by norm_num))
  have e3489 := tb_loadHolds_unique a3489 (hw 5 (by norm_num))
  have e3492 := tb_loadHolds_unique a3492 (hw 6 (by norm_num))
  have e3495 := tb_loadHolds_unique a3495 (hw 7 (by norm_num))
  have e3498 := tb_loadHolds_unique a3498 (hw 8 (by norm_num))
  have v3401 : σ (.n 3401) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_eval h (k := 33) (by norm_num)).2.2
  have v3409 : σ (.n 3409) = ev 2 := by
    rw [← hev 2 (by norm_num)]; exact (vt_eval h (k := 35) (by norm_num)).2.2
  have v3426 : σ (.n 3426) = ev 3 := by
    rw [← hev 3 (by norm_num)]; exact (vt_eval h (k := 36) (by norm_num)).2.2
  have v3430 : σ (.n 3430) = ev 4 := by
    rw [← hev 4 (by norm_num)]; exact (vt_eval h (k := 37) (by norm_num)).2.2
  have v3434 : σ (.n 3434) = ev 5 := by
    rw [← hev 5 (by norm_num)]; exact (vt_eval h (k := 38) (by norm_num)).2.2
  have v3438 : σ (.n 3438) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_eval h (k := 39) (by norm_num)).2.2
  have v3492 : σ (.n 3492) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 46) (by norm_num)).2.2
  have hB : σ (.n 3602) = vtBlockVal (σ (.n 14)) W ev [[([], 4)], [([0], 1)], [([13], 2)], [([], 8)], [([2], 1)], [([3], 1)], [([4], 1)], [([5], 1)], [([6], 1)]] := by
    simp only [v3492, v3438, v3434, v3430, v3426, v3409, v3401, a3501, a3500, a3499, e3498, a3497, a3496,
      e3495, a3494, a3493, e3492, a3491, a3490, e3489, a3488, a3487, e3486, a3485, a3484,
      e3483, a3482, a3481, e3480, a3479, a3478, e3477, a3476, e3475, a3407, a3406, a3405,
      a3404, a3403, a3402, a3401, a3400, a3399, a3398, a3397]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a3503, a3502, hB]

set_option maxRecDepth 10000 in
theorem vtB03_2 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (33 + c))) = ev c) :
    σ (.n 3621) = σ (.n 3604) + σ (.n 977) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 2], 1)], [([10], 2)], [([7], 1)], [([], 0)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 3408 [
    .atom (.const (.n 3509) (word 2 0)),
    .atom (.mul (.n 3510) (.n 3405) (.n 3409)),
    .atom (.copy (.n 3511) (.n 3510)),
    .atom (.const (.n 3512) (word 2 0)),
    .atom (.mul (.n 3513) (.n 3512) (.n 3467)),
    .atom (.copy (.n 3514) (.n 3513)),
    .atom (.copy (.n 3515) (.n 3455)),
    .atom (.const (.n 3516) (word 0 0))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a3408, a3409, a3410, a3411, a3412, a3413, a3414, a3415, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 3504 [
    .atom (.load (.n 3605) (.n 13) 0),
    .atom (.mul (.n 3606) (.n 3605) (.n 3509)),
    .atom (.load (.n 3607) (.n 13) 1),
    .atom (.mul (.n 3608) (.n 3607) (.n 3511)),
    .atom (.add (.n 3609) (.n 3606) (.n 3608)),
    .atom (.load (.n 3610) (.n 13) 2),
    .atom (.mul (.n 3611) (.n 3610) (.n 3514)),
    .atom (.add (.n 3612) (.n 3609) (.n 3611)),
    .atom (.load (.n 3613) (.n 13) 3),
    .atom (.mul (.n 3614) (.n 3613) (.n 3515)),
    .atom (.add (.n 3615) (.n 3612) (.n 3614)),
    .atom (.load (.n 3616) (.n 13) 4),
    .atom (.mul (.n 3617) (.n 3616) (.n 3516)),
    .atom (.add (.n 3618) (.n 3615) (.n 3617)),
    .atom (.add (.n 3619) (.n 14) (.n 3618)),
    .atom (.mul (.n 3620) (.n 977) (.n 3619)),
    .atom (.add (.n 3621) (.n 3604) (.n 3620))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a3504, a3505, a3506, a3507, a3508, a3509, a3510, a3511, a3512, a3513, a3514, a3515, a3516, a3517,
    a3518, a3519, a3520, -⟩ := hs1
  have e3504 := tb_loadHolds_unique a3504 (hw 0 (by norm_num))
  have e3506 := tb_loadHolds_unique a3506 (hw 1 (by norm_num))
  have e3509 := tb_loadHolds_unique a3509 (hw 2 (by norm_num))
  have e3512 := tb_loadHolds_unique a3512 (hw 3 (by norm_num))
  have e3515 := tb_loadHolds_unique a3515 (hw 4 (by norm_num))
  have v3405 : σ (.n 3405) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 34) (by norm_num)).2.2
  have v3409 : σ (.n 3409) = ev 2 := by
    rw [← hev 2 (by norm_num)]; exact (vt_eval h (k := 35) (by norm_num)).2.2
  have v3455 : σ (.n 3455) = ev 7 := by
    rw [← hev 7 (by norm_num)]; exact (vt_eval h (k := 40) (by norm_num)).2.2
  have v3467 : σ (.n 3467) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_eval h (k := 43) (by norm_num)).2.2
  have hB : σ (.n 3619) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 2], 1)], [([10], 2)], [([7], 1)], [([], 0)]] := by
    simp only [v3467, v3455, v3409, v3405, a3518, a3517, a3516, e3515, a3514, a3513, e3512, a3511, a3510,
      e3509, a3508, a3507, e3506, a3505, e3504, a3415, a3414, a3413, a3412, a3411, a3410,
      a3409, a3408]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a3520, a3519, hB]

set_option maxRecDepth 10000 in
theorem vtB03_3 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (33 + c))) = ev c) :
    σ (.n 3638) = σ (.n 3621) + σ (.n 986) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([7, 3], 1)], [([11], 2)], [([8], 1), ([5, 8], 1), ([6, 8], 1), ([5, 0], 4), ([6, 1], 1)], [([9], 1), ([5, 9], 1), ([6, 9], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 3416 [
    .atom (.const (.n 3517) (word 2 0)),
    .atom (.mul (.n 3518) (.n 3455) (.n 3426)),
    .atom (.copy (.n 3519) (.n 3518)),
    .atom (.const (.n 3520) (word 2 0)),
    .atom (.mul (.n 3521) (.n 3520) (.n 3484)),
    .atom (.copy (.n 3522) (.n 3521)),
    .atom (.mul (.n 3523) (.n 3434) (.n 3459)),
    .atom (.add (.n 3524) (.n 3459) (.n 3523)),
    .atom (.mul (.n 3525) (.n 3438) (.n 3459)),
    .atom (.add (.n 3526) (.n 3524) (.n 3525)),
    .atom (.const (.n 3527) (word 4 0)),
    .atom (.mul (.n 3528) (.n 3434) (.n 3401)),
    .atom (.mul (.n 3529) (.n 3527) (.n 3528)),
    .atom (.add (.n 3530) (.n 3526) (.n 3529)),
    .atom (.mul (.n 3531) (.n 3438) (.n 3405)),
    .atom (.add (.n 3532) (.n 3530) (.n 3531)),
    .atom (.copy (.n 3533) (.n 3532)),
    .atom (.mul (.n 3534) (.n 3434) (.n 3463)),
    .atom (.add (.n 3535) (.n 3463) (.n 3534)),
    .atom (.mul (.n 3536) (.n 3438) (.n 3463)),
    .atom (.add (.n 3537) (.n 3535) (.n 3536)),
    .atom (.copy (.n 3538) (.n 3537))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a3416, a3417, a3418, a3419, a3420, a3421, a3422, a3423, a3424, a3425, a3426, a3427, a3428, a3429,
    a3430, a3431, a3432, a3433, a3434, a3435, a3436, a3437, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 3521 [
    .atom (.load (.n 3622) (.n 13) 0),
    .atom (.mul (.n 3623) (.n 3622) (.n 3517)),
    .atom (.load (.n 3624) (.n 13) 1),
    .atom (.mul (.n 3625) (.n 3624) (.n 3519)),
    .atom (.add (.n 3626) (.n 3623) (.n 3625)),
    .atom (.load (.n 3627) (.n 13) 2),
    .atom (.mul (.n 3628) (.n 3627) (.n 3522)),
    .atom (.add (.n 3629) (.n 3626) (.n 3628)),
    .atom (.load (.n 3630) (.n 13) 3),
    .atom (.mul (.n 3631) (.n 3630) (.n 3533)),
    .atom (.add (.n 3632) (.n 3629) (.n 3631)),
    .atom (.load (.n 3633) (.n 13) 4),
    .atom (.mul (.n 3634) (.n 3633) (.n 3538)),
    .atom (.add (.n 3635) (.n 3632) (.n 3634)),
    .atom (.add (.n 3636) (.n 14) (.n 3635)),
    .atom (.mul (.n 3637) (.n 986) (.n 3636)),
    .atom (.add (.n 3638) (.n 3621) (.n 3637))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a3521, a3522, a3523, a3524, a3525, a3526, a3527, a3528, a3529, a3530, a3531, a3532, a3533, a3534,
    a3535, a3536, a3537, -⟩ := hs1
  have e3521 := tb_loadHolds_unique a3521 (hw 0 (by norm_num))
  have e3523 := tb_loadHolds_unique a3523 (hw 1 (by norm_num))
  have e3526 := tb_loadHolds_unique a3526 (hw 2 (by norm_num))
  have e3529 := tb_loadHolds_unique a3529 (hw 3 (by norm_num))
  have e3532 := tb_loadHolds_unique a3532 (hw 4 (by norm_num))
  have v3401 : σ (.n 3401) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_eval h (k := 33) (by norm_num)).2.2
  have v3405 : σ (.n 3405) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 34) (by norm_num)).2.2
  have v3426 : σ (.n 3426) = ev 3 := by
    rw [← hev 3 (by norm_num)]; exact (vt_eval h (k := 36) (by norm_num)).2.2
  have v3434 : σ (.n 3434) = ev 5 := by
    rw [← hev 5 (by norm_num)]; exact (vt_eval h (k := 38) (by norm_num)).2.2
  have v3438 : σ (.n 3438) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_eval h (k := 39) (by norm_num)).2.2
  have v3455 : σ (.n 3455) = ev 7 := by
    rw [← hev 7 (by norm_num)]; exact (vt_eval h (k := 40) (by norm_num)).2.2
  have v3459 : σ (.n 3459) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_eval h (k := 41) (by norm_num)).2.2
  have v3463 : σ (.n 3463) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 42) (by norm_num)).2.2
  have v3484 : σ (.n 3484) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_eval h (k := 44) (by norm_num)).2.2
  have hB : σ (.n 3636) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([7, 3], 1)], [([11], 2)], [([8], 1), ([5, 8], 1), ([6, 8], 1), ([5, 0], 4), ([6, 1], 1)], [([9], 1), ([5, 9], 1), ([6, 9], 1)]] := by
    simp only [v3484, v3463, v3459, v3455, v3438, v3434, v3426, v3405, v3401, a3535, a3534, a3533, e3532,
      a3531, a3530, e3529, a3528, a3527, e3526, a3525, a3524, e3523, a3522, e3521, a3437,
      a3436, a3435, a3434, a3433, a3432, a3431, a3430, a3429, a3428, a3427, a3426, a3425,
      a3424, a3423, a3422, a3421, a3420, a3419, a3418, a3417, a3416]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a3537, a3536, hB]

set_option maxRecDepth 10000 in
theorem vtB03_4 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (33 + c))) = ev c) :
    σ (.n 3655) = σ (.n 3638) + σ (.n 995) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 4], 1)], [([12], 2)], [([8], 1)], [([9], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 3438 [
    .atom (.const (.n 3539) (word 2 0)),
    .atom (.mul (.n 3540) (.n 3405) (.n 3430)),
    .atom (.copy (.n 3541) (.n 3540)),
    .atom (.const (.n 3542) (word 2 0)),
    .atom (.mul (.n 3543) (.n 3542) (.n 3488)),
    .atom (.copy (.n 3544) (.n 3543)),
    .atom (.copy (.n 3545) (.n 3459)),
    .atom (.copy (.n 3546) (.n 3463))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a3438, a3439, a3440, a3441, a3442, a3443, a3444, a3445, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 3538 [
    .atom (.load (.n 3639) (.n 13) 0),
    .atom (.mul (.n 3640) (.n 3639) (.n 3539)),
    .atom (.load (.n 3641) (.n 13) 1),
    .atom (.mul (.n 3642) (.n 3641) (.n 3541)),
    .atom (.add (.n 3643) (.n 3640) (.n 3642)),
    .atom (.load (.n 3644) (.n 13) 2),
    .atom (.mul (.n 3645) (.n 3644) (.n 3544)),
    .atom (.add (.n 3646) (.n 3643) (.n 3645)),
    .atom (.load (.n 3647) (.n 13) 3),
    .atom (.mul (.n 3648) (.n 3647) (.n 3545)),
    .atom (.add (.n 3649) (.n 3646) (.n 3648)),
    .atom (.load (.n 3650) (.n 13) 4),
    .atom (.mul (.n 3651) (.n 3650) (.n 3546)),
    .atom (.add (.n 3652) (.n 3649) (.n 3651)),
    .atom (.add (.n 3653) (.n 14) (.n 3652)),
    .atom (.mul (.n 3654) (.n 995) (.n 3653)),
    .atom (.add (.n 3655) (.n 3638) (.n 3654))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a3538, a3539, a3540, a3541, a3542, a3543, a3544, a3545, a3546, a3547, a3548, a3549, a3550, a3551,
    a3552, a3553, a3554, -⟩ := hs1
  have e3538 := tb_loadHolds_unique a3538 (hw 0 (by norm_num))
  have e3540 := tb_loadHolds_unique a3540 (hw 1 (by norm_num))
  have e3543 := tb_loadHolds_unique a3543 (hw 2 (by norm_num))
  have e3546 := tb_loadHolds_unique a3546 (hw 3 (by norm_num))
  have e3549 := tb_loadHolds_unique a3549 (hw 4 (by norm_num))
  have v3405 : σ (.n 3405) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 34) (by norm_num)).2.2
  have v3430 : σ (.n 3430) = ev 4 := by
    rw [← hev 4 (by norm_num)]; exact (vt_eval h (k := 37) (by norm_num)).2.2
  have v3459 : σ (.n 3459) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_eval h (k := 41) (by norm_num)).2.2
  have v3463 : σ (.n 3463) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 42) (by norm_num)).2.2
  have v3488 : σ (.n 3488) = ev 12 := by
    rw [← hev 12 (by norm_num)]; exact (vt_eval h (k := 45) (by norm_num)).2.2
  have hB : σ (.n 3653) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 4], 1)], [([12], 2)], [([8], 1)], [([9], 1)]] := by
    simp only [v3488, v3463, v3459, v3430, v3405, a3552, a3551, a3550, e3549, a3548, a3547, e3546, a3545,
      a3544, e3543, a3542, a3541, e3540, a3539, e3538, a3445, a3444, a3443, a3442, a3441,
      a3440, a3439, a3438]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a3554, a3553, hB]

set_option maxRecDepth 10000 in
theorem vtSide03 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (33 + c))) = ev c) :
    σ (.n 3655) =
      vtSideVal [σ (.n 959), σ (.n 968), σ (.n 977), σ (.n 986), σ (.n 995)]
        (σ (.n 14)) W ev vtBTerms03 := by
  rw [vtB03_4 h hw hev, vtB03_3 h hw hev, vtB03_2 h hw hev, vtB03_1 h hw hev, vtB03_0 h hw hev]
  simp only [vtSideVal, vtBTerms03, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, add_zero, add_assoc]

set_option maxRecDepth 10000 in
theorem vtD3_0 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (33 + c))) = ev c) :
    σ (.n 3659) = σ (.n 1361) * vtSlots W ev 0
      [[], [([0], 3)], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 3446 [
    .atom (.const (.n 3547) (word 3 0)),
    .atom (.mul (.n 3548) (.n 3547) (.n 3401)),
    .atom (.copy (.n 3549) (.n 3548))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a3446, a3447, a3448, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 3556 [
    .atom (.load (.n 3657) (.n 13) 1),
    .atom (.mul (.n 3658) (.n 3657) (.n 3549)),
    .atom (.mul (.n 3659) (.n 1361) (.n 3658))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a3556, a3557, a3558, -⟩ := hs1
  have e3556 := tb_loadHolds_unique a3556 (hw 1 (by norm_num))
  have v3401 : σ (.n 3401) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_eval h (k := 33) (by norm_num)).2.2
  have hB : σ (.n 3658) = vtSlots W ev 0 [[], [([0], 3)], []] := by
    simp only [v3401, a3557, e3556, a3448, a3447, a3446]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a3558, hB]

set_option maxRecDepth 10000 in
theorem vtD3_1 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (33 + c))) = ev c) :
    σ (.n 3663) = σ (.n 3659) + σ (.n 1363) * vtSlots W ev 0
      [[], [], [([13], 3)], [], [], [], [], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 3449 [
    .atom (.const (.n 3550) (word 3 0)),
    .atom (.mul (.n 3551) (.n 3550) (.n 3492)),
    .atom (.copy (.n 3552) (.n 3551))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a3449, a3450, a3451, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 3559 [
    .atom (.load (.n 3660) (.n 13) 2),
    .atom (.mul (.n 3661) (.n 3660) (.n 3552)),
    .atom (.mul (.n 3662) (.n 1363) (.n 3661)),
    .atom (.add (.n 3663) (.n 3659) (.n 3662))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a3559, a3560, a3561, a3562, -⟩ := hs1
  have e3559 := tb_loadHolds_unique a3559 (hw 2 (by norm_num))
  have v3492 : σ (.n 3492) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 46) (by norm_num)).2.2
  have hB : σ (.n 3661) = vtSlots W ev 0 [[], [], [([13], 3)], [], [], [], [], [], []] := by
    simp only [v3492, a3560, e3559, a3451, a3450, a3449]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a3562, a3561, hB]

set_option maxRecDepth 10000 in
theorem vtD3_2 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (33 + c))) = ev c) :
    σ (.n 3667) = σ (.n 3663) + σ (.n 1365) * vtSlots W ev 0
      [[], [], [([10], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 3452 [
    .atom (.const (.n 3553) (word 3 0)),
    .atom (.mul (.n 3554) (.n 3553) (.n 3467)),
    .atom (.copy (.n 3555) (.n 3554))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a3452, a3453, a3454, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 3563 [
    .atom (.load (.n 3664) (.n 13) 2),
    .atom (.mul (.n 3665) (.n 3664) (.n 3555)),
    .atom (.mul (.n 3666) (.n 1365) (.n 3665)),
    .atom (.add (.n 3667) (.n 3663) (.n 3666))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a3563, a3564, a3565, a3566, -⟩ := hs1
  have e3563 := tb_loadHolds_unique a3563 (hw 2 (by norm_num))
  have v3467 : σ (.n 3467) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_eval h (k := 43) (by norm_num)).2.2
  have hB : σ (.n 3665) = vtSlots W ev 0 [[], [], [([10], 3)], [], []] := by
    simp only [v3467, a3564, e3563, a3454, a3453, a3452]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a3566, a3565, hB]

set_option maxRecDepth 10000 in
theorem vtD3_3 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (33 + c))) = ev c) :
    σ (.n 3671) = σ (.n 3667) + σ (.n 1367) * vtSlots W ev 0
      [[], [], [([11], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 3455 [
    .atom (.const (.n 3556) (word 3 0)),
    .atom (.mul (.n 3557) (.n 3556) (.n 3484)),
    .atom (.copy (.n 3558) (.n 3557))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a3455, a3456, a3457, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 3567 [
    .atom (.load (.n 3668) (.n 13) 2),
    .atom (.mul (.n 3669) (.n 3668) (.n 3558)),
    .atom (.mul (.n 3670) (.n 1367) (.n 3669)),
    .atom (.add (.n 3671) (.n 3667) (.n 3670))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a3567, a3568, a3569, a3570, -⟩ := hs1
  have e3567 := tb_loadHolds_unique a3567 (hw 2 (by norm_num))
  have v3484 : σ (.n 3484) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_eval h (k := 44) (by norm_num)).2.2
  have hB : σ (.n 3669) = vtSlots W ev 0 [[], [], [([11], 3)], [], []] := by
    simp only [v3484, a3568, e3567, a3457, a3456, a3455]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a3570, a3569, hB]

set_option maxRecDepth 10000 in
theorem vtD3_4 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (33 + c))) = ev c) :
    σ (.n 3675) = σ (.n 3671) + σ (.n 1369) * vtSlots W ev 0
      [[], [], [([12], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 3458 [
    .atom (.const (.n 3559) (word 3 0)),
    .atom (.mul (.n 3560) (.n 3559) (.n 3488)),
    .atom (.copy (.n 3561) (.n 3560))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a3458, a3459, a3460, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 3571 [
    .atom (.load (.n 3672) (.n 13) 2),
    .atom (.mul (.n 3673) (.n 3672) (.n 3561)),
    .atom (.mul (.n 3674) (.n 1369) (.n 3673)),
    .atom (.add (.n 3675) (.n 3671) (.n 3674))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a3571, a3572, a3573, a3574, -⟩ := hs1
  have e3571 := tb_loadHolds_unique a3571 (hw 2 (by norm_num))
  have v3488 : σ (.n 3488) = ev 12 := by
    rw [← hev 12 (by norm_num)]; exact (vt_eval h (k := 45) (by norm_num)).2.2
  have hB : σ (.n 3673) = vtSlots W ev 0 [[], [], [([12], 3)], [], []] := by
    simp only [v3488, a3572, e3571, a3460, a3459, a3458]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a3574, a3573, hB]

set_option maxRecDepth 10000 in
theorem vtSide13 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (33 + c))) = ev c) :
    σ (.n 3676) =
      vtSideVal [σ (.n 1361), σ (.n 1363), σ (.n 1365), σ (.n 1367), σ (.n 1369)]
        (σ (.n 14)) W ev vtBTerms13 := by
  have hF0 : σ (.n 3655) =
      vtSideVal [σ (.n 1361), σ (.n 1363), σ (.n 1365), σ (.n 1367), σ (.n 1369)]
        (σ (.n 14)) W ev vtBTerms03 := by
    rw [vtPullSels3 h]; exact vtSide03 h hw hev
  have a3575 := h.atomAt 3575 (.add (.n 3676) (.n 3655) (.n 3675)) (by decide +kernel)
  simp only [Atom.Holds] at a3575
  rw [vtSideVal_pull _ _ _ _ _ _ _ vtPull3, ← hF0, a3575, vtD3_4 h hw hev, vtD3_3 h hw hev, vtD3_2 h hw hev, vtD3_1 h hw hev, vtD3_0 h hw hev]
  simp only [vtDiffSum, vtDTerms3, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, add_zero, add_assoc]

set_option maxRecDepth 10000 in
theorem vtSide23 {rd : Reader} {σ : Val} (h : VtH rd σ) {ev : ℕ → E}
    (hev : ∀ c < 14, σ (.n (vtEvB (33 + c))) = ev c) :
    σ (.n 3685) =
      vtSideVal [σ (.n 1519), σ (.n 1528), σ (.n 1537), σ (.n 1546)]
        (0) (fun _ ↦ 1) ev vtBTerms23 := by
  obtain ⟨_, hs0⟩ := h.sliceAt 3461 [
    .atom (.copy (.n 3562) (.n 3467)),
    .atom (.copy (.n 3563) (.n 3484)),
    .atom (.copy (.n 3564) (.n 3488)),
    .atom (.copy (.n 3565) (.n 3492))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a3461, a3462, a3463, a3464, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 3578 [
    .atom (.mul (.n 3679) (.n 1519) (.n 3562)),
    .atom (.mul (.n 3680) (.n 1528) (.n 3563)),
    .atom (.add (.n 3681) (.n 3679) (.n 3680)),
    .atom (.mul (.n 3682) (.n 1537) (.n 3564)),
    .atom (.add (.n 3683) (.n 3681) (.n 3682)),
    .atom (.mul (.n 3684) (.n 1546) (.n 3565)),
    .atom (.add (.n 3685) (.n 3683) (.n 3684))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a3578, a3579, a3580, a3581, a3582, a3583, a3584, -⟩ := hs1
  have v3467 : σ (.n 3467) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_eval h (k := 43) (by norm_num)).2.2
  have v3484 : σ (.n 3484) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_eval h (k := 44) (by norm_num)).2.2
  have v3488 : σ (.n 3488) = ev 12 := by
    rw [← hev 12 (by norm_num)]; exact (vt_eval h (k := 45) (by norm_num)).2.2
  have v3492 : σ (.n 3492) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 46) (by norm_num)).2.2
  simp only [v3492, v3488, v3484, v3467, a3584, a3583, a3582, a3581, a3580, a3579, a3578, a3464, a3463, a3462,
    a3461]
  simp only [vtSideVal, vtBTerms23, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, vt_ofK_ofBits_one]
  ring

end
end LeanVM.Guest.B1.Tables
