/-
  LeanVM.Guest.B1.Tables.VtC.FForms3

  `Vt/FormsT3.lean` on the window `VtF` (generated: scripts/b1c-vt/gentwins.py).

  Do not edit: `scripts/b1c-vt/all.py` writes it (`regen-guest.sh`, step `vt`).
-/

module

public import LeanVM.Guest.B1.Tables.VtC.FEvals
public import LeanVM.Guest.B1.Tables.Vt.FormsT3

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

set_option maxRecDepth 10000 in
theorem vtB03_0F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (33 + c))) = ev c) :
    σ (.n 3579) = σ (.n 959) * vtBlockVal (σ (.n 14)) W ev
      [[([], 1)], [([0], 2)], [([1], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 3397 [
    .atom (.const (.n 3497) (word 1 0)),
    .atom (.const (.n 3498) (word 2 0)),
    .atom (.mul (.n 3499) (.n 3498) (.n 3405)),
    .atom (.copy (.n 3500) (.n 3499)),
    .atom (.copy (.n 3501) (.n 3409))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a3397, a3398, a3399, a3400, a3401, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 3470 [
    .atom (.load (.n 3570) (.n 13) 0),
    .atom (.mul (.n 3571) (.n 3570) (.n 3497)),
    .atom (.load (.n 3572) (.n 13) 1),
    .atom (.mul (.n 3573) (.n 3572) (.n 3500)),
    .atom (.add (.n 3574) (.n 3571) (.n 3573)),
    .atom (.load (.n 3575) (.n 13) 2),
    .atom (.mul (.n 3576) (.n 3575) (.n 3501)),
    .atom (.add (.n 3577) (.n 3574) (.n 3576)),
    .atom (.add (.n 3578) (.n 14) (.n 3577)),
    .atom (.mul (.n 3579) (.n 959) (.n 3578))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a3470, a3471, a3472, a3473, a3474, a3475, a3476, a3477, a3478, a3479, -⟩ := hs1
  have e3470 := tb_loadHolds_unique a3470 (hw 0 (by norm_num))
  have e3472 := tb_loadHolds_unique a3472 (hw 1 (by norm_num))
  have e3475 := tb_loadHolds_unique a3475 (hw 2 (by norm_num))
  have v3405 : σ (.n 3405) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_evalF h (k := 33) (by norm_num)).2.2
  have v3409 : σ (.n 3409) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 34) (by norm_num)).2.2
  have hB : σ (.n 3578) = vtBlockVal (σ (.n 14)) W ev [[([], 1)], [([0], 2)], [([1], 1)]] := by
    simp only [v3409, v3405, a3478, a3477, a3476, e3475, a3474, a3473, e3472, a3471, e3470, a3401, a3400,
      a3399, a3398, a3397]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a3479, hB]

set_option maxRecDepth 10000 in
theorem vtB03_1F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (33 + c))) = ev c) :
    σ (.n 3608) = σ (.n 3579) + σ (.n 968) * vtBlockVal (σ (.n 14)) W ev
      [[([], 4)], [([0], 1)], [([13], 2)], [([], 8)], [([2], 1)], [([3], 1)], [([4], 1)], [([5], 1)], [([6], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 3402 [
    .atom (.const (.n 3502) (word 4 0)),
    .atom (.copy (.n 3503) (.n 3405)),
    .atom (.const (.n 3504) (word 2 0)),
    .atom (.mul (.n 3505) (.n 3504) (.n 3496)),
    .atom (.copy (.n 3506) (.n 3505)),
    .atom (.const (.n 3507) (word 8 0)),
    .atom (.copy (.n 3508) (.n 3413)),
    .atom (.copy (.n 3509) (.n 3430)),
    .atom (.copy (.n 3510) (.n 3434)),
    .atom (.copy (.n 3511) (.n 3438)),
    .atom (.copy (.n 3512) (.n 3442))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a3402, a3403, a3404, a3405, a3406, a3407, a3408, a3409, a3410, a3411, a3412, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 3480 [
    .atom (.load (.n 3580) (.n 13) 0),
    .atom (.mul (.n 3581) (.n 3580) (.n 3502)),
    .atom (.load (.n 3582) (.n 13) 1),
    .atom (.mul (.n 3583) (.n 3582) (.n 3503)),
    .atom (.add (.n 3584) (.n 3581) (.n 3583)),
    .atom (.load (.n 3585) (.n 13) 2),
    .atom (.mul (.n 3586) (.n 3585) (.n 3506)),
    .atom (.add (.n 3587) (.n 3584) (.n 3586)),
    .atom (.load (.n 3588) (.n 13) 3),
    .atom (.mul (.n 3589) (.n 3588) (.n 3507)),
    .atom (.add (.n 3590) (.n 3587) (.n 3589)),
    .atom (.load (.n 3591) (.n 13) 4),
    .atom (.mul (.n 3592) (.n 3591) (.n 3508)),
    .atom (.add (.n 3593) (.n 3590) (.n 3592)),
    .atom (.load (.n 3594) (.n 13) 5),
    .atom (.mul (.n 3595) (.n 3594) (.n 3509)),
    .atom (.add (.n 3596) (.n 3593) (.n 3595)),
    .atom (.load (.n 3597) (.n 13) 6),
    .atom (.mul (.n 3598) (.n 3597) (.n 3510)),
    .atom (.add (.n 3599) (.n 3596) (.n 3598)),
    .atom (.load (.n 3600) (.n 13) 7),
    .atom (.mul (.n 3601) (.n 3600) (.n 3511)),
    .atom (.add (.n 3602) (.n 3599) (.n 3601)),
    .atom (.load (.n 3603) (.n 13) 8),
    .atom (.mul (.n 3604) (.n 3603) (.n 3512)),
    .atom (.add (.n 3605) (.n 3602) (.n 3604)),
    .atom (.add (.n 3606) (.n 14) (.n 3605)),
    .atom (.mul (.n 3607) (.n 968) (.n 3606)),
    .atom (.add (.n 3608) (.n 3579) (.n 3607))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a3480, a3481, a3482, a3483, a3484, a3485, a3486, a3487, a3488, a3489, a3490, a3491, a3492, a3493,
    a3494, a3495, a3496, a3497, a3498, a3499, a3500, a3501, a3502, a3503, a3504, a3505, a3506,
    a3507, a3508, -⟩ := hs1
  have e3480 := tb_loadHolds_unique a3480 (hw 0 (by norm_num))
  have e3482 := tb_loadHolds_unique a3482 (hw 1 (by norm_num))
  have e3485 := tb_loadHolds_unique a3485 (hw 2 (by norm_num))
  have e3488 := tb_loadHolds_unique a3488 (hw 3 (by norm_num))
  have e3491 := tb_loadHolds_unique a3491 (hw 4 (by norm_num))
  have e3494 := tb_loadHolds_unique a3494 (hw 5 (by norm_num))
  have e3497 := tb_loadHolds_unique a3497 (hw 6 (by norm_num))
  have e3500 := tb_loadHolds_unique a3500 (hw 7 (by norm_num))
  have e3503 := tb_loadHolds_unique a3503 (hw 8 (by norm_num))
  have v3405 : σ (.n 3405) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_evalF h (k := 33) (by norm_num)).2.2
  have v3413 : σ (.n 3413) = ev 2 := by
    rw [← hev 2 (by norm_num)]; exact (vt_evalF h (k := 35) (by norm_num)).2.2
  have v3430 : σ (.n 3430) = ev 3 := by
    rw [← hev 3 (by norm_num)]; exact (vt_evalF h (k := 36) (by norm_num)).2.2
  have v3434 : σ (.n 3434) = ev 4 := by
    rw [← hev 4 (by norm_num)]; exact (vt_evalF h (k := 37) (by norm_num)).2.2
  have v3438 : σ (.n 3438) = ev 5 := by
    rw [← hev 5 (by norm_num)]; exact (vt_evalF h (k := 38) (by norm_num)).2.2
  have v3442 : σ (.n 3442) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_evalF h (k := 39) (by norm_num)).2.2
  have v3496 : σ (.n 3496) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_evalF h (k := 46) (by norm_num)).2.2
  have hB : σ (.n 3606) = vtBlockVal (σ (.n 14)) W ev [[([], 4)], [([0], 1)], [([13], 2)], [([], 8)], [([2], 1)], [([3], 1)], [([4], 1)], [([5], 1)], [([6], 1)]] := by
    simp only [v3496, v3442, v3438, v3434, v3430, v3413, v3405, a3506, a3505, a3504, e3503, a3502, a3501,
      e3500, a3499, a3498, e3497, a3496, a3495, e3494, a3493, a3492, e3491, a3490, a3489,
      e3488, a3487, a3486, e3485, a3484, a3483, e3482, a3481, e3480, a3412, a3411, a3410,
      a3409, a3408, a3407, a3406, a3405, a3404, a3403, a3402]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a3508, a3507, hB]

set_option maxRecDepth 10000 in
theorem vtB03_2F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (33 + c))) = ev c) :
    σ (.n 3625) = σ (.n 3608) + σ (.n 977) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 2], 1)], [([10], 2)], [([7], 1)], [([], 0)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 3413 [
    .atom (.const (.n 3513) (word 2 0)),
    .atom (.mul (.n 3514) (.n 3409) (.n 3413)),
    .atom (.copy (.n 3515) (.n 3514)),
    .atom (.const (.n 3516) (word 2 0)),
    .atom (.mul (.n 3517) (.n 3516) (.n 3471)),
    .atom (.copy (.n 3518) (.n 3517)),
    .atom (.copy (.n 3519) (.n 3459)),
    .atom (.const (.n 3520) (word 0 0))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a3413, a3414, a3415, a3416, a3417, a3418, a3419, a3420, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 3509 [
    .atom (.load (.n 3609) (.n 13) 0),
    .atom (.mul (.n 3610) (.n 3609) (.n 3513)),
    .atom (.load (.n 3611) (.n 13) 1),
    .atom (.mul (.n 3612) (.n 3611) (.n 3515)),
    .atom (.add (.n 3613) (.n 3610) (.n 3612)),
    .atom (.load (.n 3614) (.n 13) 2),
    .atom (.mul (.n 3615) (.n 3614) (.n 3518)),
    .atom (.add (.n 3616) (.n 3613) (.n 3615)),
    .atom (.load (.n 3617) (.n 13) 3),
    .atom (.mul (.n 3618) (.n 3617) (.n 3519)),
    .atom (.add (.n 3619) (.n 3616) (.n 3618)),
    .atom (.load (.n 3620) (.n 13) 4),
    .atom (.mul (.n 3621) (.n 3620) (.n 3520)),
    .atom (.add (.n 3622) (.n 3619) (.n 3621)),
    .atom (.add (.n 3623) (.n 14) (.n 3622)),
    .atom (.mul (.n 3624) (.n 977) (.n 3623)),
    .atom (.add (.n 3625) (.n 3608) (.n 3624))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a3509, a3510, a3511, a3512, a3513, a3514, a3515, a3516, a3517, a3518, a3519, a3520, a3521, a3522,
    a3523, a3524, a3525, -⟩ := hs1
  have e3509 := tb_loadHolds_unique a3509 (hw 0 (by norm_num))
  have e3511 := tb_loadHolds_unique a3511 (hw 1 (by norm_num))
  have e3514 := tb_loadHolds_unique a3514 (hw 2 (by norm_num))
  have e3517 := tb_loadHolds_unique a3517 (hw 3 (by norm_num))
  have e3520 := tb_loadHolds_unique a3520 (hw 4 (by norm_num))
  have v3409 : σ (.n 3409) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 34) (by norm_num)).2.2
  have v3413 : σ (.n 3413) = ev 2 := by
    rw [← hev 2 (by norm_num)]; exact (vt_evalF h (k := 35) (by norm_num)).2.2
  have v3459 : σ (.n 3459) = ev 7 := by
    rw [← hev 7 (by norm_num)]; exact (vt_evalF h (k := 40) (by norm_num)).2.2
  have v3471 : σ (.n 3471) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_evalF h (k := 43) (by norm_num)).2.2
  have hB : σ (.n 3623) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 2], 1)], [([10], 2)], [([7], 1)], [([], 0)]] := by
    simp only [v3471, v3459, v3413, v3409, a3523, a3522, a3521, e3520, a3519, a3518, e3517, a3516, a3515,
      e3514, a3513, a3512, e3511, a3510, e3509, a3420, a3419, a3418, a3417, a3416, a3415,
      a3414, a3413]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a3525, a3524, hB]

set_option maxRecDepth 10000 in
theorem vtB03_3F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (33 + c))) = ev c) :
    σ (.n 3642) = σ (.n 3625) + σ (.n 986) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([7, 3], 1)], [([11], 2)], [([8], 1), ([5, 8], 1), ([6, 8], 1), ([5, 0], 4), ([6, 1], 1)], [([9], 1), ([5, 9], 1), ([6, 9], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 3421 [
    .atom (.const (.n 3521) (word 2 0)),
    .atom (.mul (.n 3522) (.n 3459) (.n 3430)),
    .atom (.copy (.n 3523) (.n 3522)),
    .atom (.const (.n 3524) (word 2 0)),
    .atom (.mul (.n 3525) (.n 3524) (.n 3488)),
    .atom (.copy (.n 3526) (.n 3525)),
    .atom (.mul (.n 3527) (.n 3438) (.n 3463)),
    .atom (.add (.n 3528) (.n 3463) (.n 3527)),
    .atom (.mul (.n 3529) (.n 3442) (.n 3463)),
    .atom (.add (.n 3530) (.n 3528) (.n 3529)),
    .atom (.const (.n 3531) (word 4 0)),
    .atom (.mul (.n 3532) (.n 3438) (.n 3405)),
    .atom (.mul (.n 3533) (.n 3531) (.n 3532)),
    .atom (.add (.n 3534) (.n 3530) (.n 3533)),
    .atom (.mul (.n 3535) (.n 3442) (.n 3409)),
    .atom (.add (.n 3536) (.n 3534) (.n 3535)),
    .atom (.copy (.n 3537) (.n 3536)),
    .atom (.mul (.n 3538) (.n 3438) (.n 3467)),
    .atom (.add (.n 3539) (.n 3467) (.n 3538)),
    .atom (.mul (.n 3540) (.n 3442) (.n 3467)),
    .atom (.add (.n 3541) (.n 3539) (.n 3540)),
    .atom (.copy (.n 3542) (.n 3541))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a3421, a3422, a3423, a3424, a3425, a3426, a3427, a3428, a3429, a3430, a3431, a3432, a3433, a3434,
    a3435, a3436, a3437, a3438, a3439, a3440, a3441, a3442, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 3526 [
    .atom (.load (.n 3626) (.n 13) 0),
    .atom (.mul (.n 3627) (.n 3626) (.n 3521)),
    .atom (.load (.n 3628) (.n 13) 1),
    .atom (.mul (.n 3629) (.n 3628) (.n 3523)),
    .atom (.add (.n 3630) (.n 3627) (.n 3629)),
    .atom (.load (.n 3631) (.n 13) 2),
    .atom (.mul (.n 3632) (.n 3631) (.n 3526)),
    .atom (.add (.n 3633) (.n 3630) (.n 3632)),
    .atom (.load (.n 3634) (.n 13) 3),
    .atom (.mul (.n 3635) (.n 3634) (.n 3537)),
    .atom (.add (.n 3636) (.n 3633) (.n 3635)),
    .atom (.load (.n 3637) (.n 13) 4),
    .atom (.mul (.n 3638) (.n 3637) (.n 3542)),
    .atom (.add (.n 3639) (.n 3636) (.n 3638)),
    .atom (.add (.n 3640) (.n 14) (.n 3639)),
    .atom (.mul (.n 3641) (.n 986) (.n 3640)),
    .atom (.add (.n 3642) (.n 3625) (.n 3641))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a3526, a3527, a3528, a3529, a3530, a3531, a3532, a3533, a3534, a3535, a3536, a3537, a3538, a3539,
    a3540, a3541, a3542, -⟩ := hs1
  have e3526 := tb_loadHolds_unique a3526 (hw 0 (by norm_num))
  have e3528 := tb_loadHolds_unique a3528 (hw 1 (by norm_num))
  have e3531 := tb_loadHolds_unique a3531 (hw 2 (by norm_num))
  have e3534 := tb_loadHolds_unique a3534 (hw 3 (by norm_num))
  have e3537 := tb_loadHolds_unique a3537 (hw 4 (by norm_num))
  have v3405 : σ (.n 3405) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_evalF h (k := 33) (by norm_num)).2.2
  have v3409 : σ (.n 3409) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 34) (by norm_num)).2.2
  have v3430 : σ (.n 3430) = ev 3 := by
    rw [← hev 3 (by norm_num)]; exact (vt_evalF h (k := 36) (by norm_num)).2.2
  have v3438 : σ (.n 3438) = ev 5 := by
    rw [← hev 5 (by norm_num)]; exact (vt_evalF h (k := 38) (by norm_num)).2.2
  have v3442 : σ (.n 3442) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_evalF h (k := 39) (by norm_num)).2.2
  have v3459 : σ (.n 3459) = ev 7 := by
    rw [← hev 7 (by norm_num)]; exact (vt_evalF h (k := 40) (by norm_num)).2.2
  have v3463 : σ (.n 3463) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_evalF h (k := 41) (by norm_num)).2.2
  have v3467 : σ (.n 3467) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_evalF h (k := 42) (by norm_num)).2.2
  have v3488 : σ (.n 3488) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_evalF h (k := 44) (by norm_num)).2.2
  have hB : σ (.n 3640) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([7, 3], 1)], [([11], 2)], [([8], 1), ([5, 8], 1), ([6, 8], 1), ([5, 0], 4), ([6, 1], 1)], [([9], 1), ([5, 9], 1), ([6, 9], 1)]] := by
    simp only [v3488, v3467, v3463, v3459, v3442, v3438, v3430, v3409, v3405, a3540, a3539, a3538, e3537,
      a3536, a3535, e3534, a3533, a3532, e3531, a3530, a3529, e3528, a3527, e3526, a3442,
      a3441, a3440, a3439, a3438, a3437, a3436, a3435, a3434, a3433, a3432, a3431, a3430,
      a3429, a3428, a3427, a3426, a3425, a3424, a3423, a3422, a3421]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a3542, a3541, hB]

set_option maxRecDepth 10000 in
theorem vtB03_4F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (33 + c))) = ev c) :
    σ (.n 3659) = σ (.n 3642) + σ (.n 995) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 4], 1)], [([12], 2)], [([8], 1)], [([9], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 3443 [
    .atom (.const (.n 3543) (word 2 0)),
    .atom (.mul (.n 3544) (.n 3409) (.n 3434)),
    .atom (.copy (.n 3545) (.n 3544)),
    .atom (.const (.n 3546) (word 2 0)),
    .atom (.mul (.n 3547) (.n 3546) (.n 3492)),
    .atom (.copy (.n 3548) (.n 3547)),
    .atom (.copy (.n 3549) (.n 3463)),
    .atom (.copy (.n 3550) (.n 3467))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a3443, a3444, a3445, a3446, a3447, a3448, a3449, a3450, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 3543 [
    .atom (.load (.n 3643) (.n 13) 0),
    .atom (.mul (.n 3644) (.n 3643) (.n 3543)),
    .atom (.load (.n 3645) (.n 13) 1),
    .atom (.mul (.n 3646) (.n 3645) (.n 3545)),
    .atom (.add (.n 3647) (.n 3644) (.n 3646)),
    .atom (.load (.n 3648) (.n 13) 2),
    .atom (.mul (.n 3649) (.n 3648) (.n 3548)),
    .atom (.add (.n 3650) (.n 3647) (.n 3649)),
    .atom (.load (.n 3651) (.n 13) 3),
    .atom (.mul (.n 3652) (.n 3651) (.n 3549)),
    .atom (.add (.n 3653) (.n 3650) (.n 3652)),
    .atom (.load (.n 3654) (.n 13) 4),
    .atom (.mul (.n 3655) (.n 3654) (.n 3550)),
    .atom (.add (.n 3656) (.n 3653) (.n 3655)),
    .atom (.add (.n 3657) (.n 14) (.n 3656)),
    .atom (.mul (.n 3658) (.n 995) (.n 3657)),
    .atom (.add (.n 3659) (.n 3642) (.n 3658))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a3543, a3544, a3545, a3546, a3547, a3548, a3549, a3550, a3551, a3552, a3553, a3554, a3555, a3556,
    a3557, a3558, a3559, -⟩ := hs1
  have e3543 := tb_loadHolds_unique a3543 (hw 0 (by norm_num))
  have e3545 := tb_loadHolds_unique a3545 (hw 1 (by norm_num))
  have e3548 := tb_loadHolds_unique a3548 (hw 2 (by norm_num))
  have e3551 := tb_loadHolds_unique a3551 (hw 3 (by norm_num))
  have e3554 := tb_loadHolds_unique a3554 (hw 4 (by norm_num))
  have v3409 : σ (.n 3409) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 34) (by norm_num)).2.2
  have v3434 : σ (.n 3434) = ev 4 := by
    rw [← hev 4 (by norm_num)]; exact (vt_evalF h (k := 37) (by norm_num)).2.2
  have v3463 : σ (.n 3463) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_evalF h (k := 41) (by norm_num)).2.2
  have v3467 : σ (.n 3467) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_evalF h (k := 42) (by norm_num)).2.2
  have v3492 : σ (.n 3492) = ev 12 := by
    rw [← hev 12 (by norm_num)]; exact (vt_evalF h (k := 45) (by norm_num)).2.2
  have hB : σ (.n 3657) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 4], 1)], [([12], 2)], [([8], 1)], [([9], 1)]] := by
    simp only [v3492, v3467, v3463, v3434, v3409, a3557, a3556, a3555, e3554, a3553, a3552, e3551, a3550,
      a3549, e3548, a3547, a3546, e3545, a3544, e3543, a3450, a3449, a3448, a3447, a3446,
      a3445, a3444, a3443]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a3559, a3558, hB]

set_option maxRecDepth 10000 in
theorem vtSide03F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (33 + c))) = ev c) :
    σ (.n 3659) =
      vtSideVal [σ (.n 959), σ (.n 968), σ (.n 977), σ (.n 986), σ (.n 995)]
        (σ (.n 14)) W ev vtBTerms03 := by
  rw [vtB03_4F h hw hev, vtB03_3F h hw hev, vtB03_2F h hw hev, vtB03_1F h hw hev, vtB03_0F h hw hev]
  simp only [vtSideVal, vtBTerms03, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, add_zero, add_assoc]

set_option maxRecDepth 10000 in
theorem vtD3_0F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (33 + c))) = ev c) :
    σ (.n 3663) = σ (.n 1361) * vtSlots W ev 0
      [[], [([0], 3)], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 3451 [
    .atom (.const (.n 3551) (word 3 0)),
    .atom (.mul (.n 3552) (.n 3551) (.n 3405)),
    .atom (.copy (.n 3553) (.n 3552))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a3451, a3452, a3453, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 3561 [
    .atom (.load (.n 3661) (.n 13) 1),
    .atom (.mul (.n 3662) (.n 3661) (.n 3553)),
    .atom (.mul (.n 3663) (.n 1361) (.n 3662))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a3561, a3562, a3563, -⟩ := hs1
  have e3561 := tb_loadHolds_unique a3561 (hw 1 (by norm_num))
  have v3405 : σ (.n 3405) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_evalF h (k := 33) (by norm_num)).2.2
  have hB : σ (.n 3662) = vtSlots W ev 0 [[], [([0], 3)], []] := by
    simp only [v3405, a3562, e3561, a3453, a3452, a3451]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a3563, hB]

set_option maxRecDepth 10000 in
theorem vtD3_1F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (33 + c))) = ev c) :
    σ (.n 3667) = σ (.n 3663) + σ (.n 1363) * vtSlots W ev 0
      [[], [], [([13], 3)], [], [], [], [], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 3454 [
    .atom (.const (.n 3554) (word 3 0)),
    .atom (.mul (.n 3555) (.n 3554) (.n 3496)),
    .atom (.copy (.n 3556) (.n 3555))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a3454, a3455, a3456, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 3564 [
    .atom (.load (.n 3664) (.n 13) 2),
    .atom (.mul (.n 3665) (.n 3664) (.n 3556)),
    .atom (.mul (.n 3666) (.n 1363) (.n 3665)),
    .atom (.add (.n 3667) (.n 3663) (.n 3666))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a3564, a3565, a3566, a3567, -⟩ := hs1
  have e3564 := tb_loadHolds_unique a3564 (hw 2 (by norm_num))
  have v3496 : σ (.n 3496) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_evalF h (k := 46) (by norm_num)).2.2
  have hB : σ (.n 3665) = vtSlots W ev 0 [[], [], [([13], 3)], [], [], [], [], [], []] := by
    simp only [v3496, a3565, e3564, a3456, a3455, a3454]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a3567, a3566, hB]

set_option maxRecDepth 10000 in
theorem vtD3_2F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (33 + c))) = ev c) :
    σ (.n 3671) = σ (.n 3667) + σ (.n 1365) * vtSlots W ev 0
      [[], [], [([10], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 3457 [
    .atom (.const (.n 3557) (word 3 0)),
    .atom (.mul (.n 3558) (.n 3557) (.n 3471)),
    .atom (.copy (.n 3559) (.n 3558))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a3457, a3458, a3459, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 3568 [
    .atom (.load (.n 3668) (.n 13) 2),
    .atom (.mul (.n 3669) (.n 3668) (.n 3559)),
    .atom (.mul (.n 3670) (.n 1365) (.n 3669)),
    .atom (.add (.n 3671) (.n 3667) (.n 3670))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a3568, a3569, a3570, a3571, -⟩ := hs1
  have e3568 := tb_loadHolds_unique a3568 (hw 2 (by norm_num))
  have v3471 : σ (.n 3471) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_evalF h (k := 43) (by norm_num)).2.2
  have hB : σ (.n 3669) = vtSlots W ev 0 [[], [], [([10], 3)], [], []] := by
    simp only [v3471, a3569, e3568, a3459, a3458, a3457]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a3571, a3570, hB]

set_option maxRecDepth 10000 in
theorem vtD3_3F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (33 + c))) = ev c) :
    σ (.n 3675) = σ (.n 3671) + σ (.n 1367) * vtSlots W ev 0
      [[], [], [([11], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 3460 [
    .atom (.const (.n 3560) (word 3 0)),
    .atom (.mul (.n 3561) (.n 3560) (.n 3488)),
    .atom (.copy (.n 3562) (.n 3561))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a3460, a3461, a3462, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 3572 [
    .atom (.load (.n 3672) (.n 13) 2),
    .atom (.mul (.n 3673) (.n 3672) (.n 3562)),
    .atom (.mul (.n 3674) (.n 1367) (.n 3673)),
    .atom (.add (.n 3675) (.n 3671) (.n 3674))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a3572, a3573, a3574, a3575, -⟩ := hs1
  have e3572 := tb_loadHolds_unique a3572 (hw 2 (by norm_num))
  have v3488 : σ (.n 3488) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_evalF h (k := 44) (by norm_num)).2.2
  have hB : σ (.n 3673) = vtSlots W ev 0 [[], [], [([11], 3)], [], []] := by
    simp only [v3488, a3573, e3572, a3462, a3461, a3460]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a3575, a3574, hB]

set_option maxRecDepth 10000 in
theorem vtD3_4F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (33 + c))) = ev c) :
    σ (.n 3679) = σ (.n 3675) + σ (.n 1369) * vtSlots W ev 0
      [[], [], [([12], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 3463 [
    .atom (.const (.n 3563) (word 3 0)),
    .atom (.mul (.n 3564) (.n 3563) (.n 3492)),
    .atom (.copy (.n 3565) (.n 3564))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a3463, a3464, a3465, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 3576 [
    .atom (.load (.n 3676) (.n 13) 2),
    .atom (.mul (.n 3677) (.n 3676) (.n 3565)),
    .atom (.mul (.n 3678) (.n 1369) (.n 3677)),
    .atom (.add (.n 3679) (.n 3675) (.n 3678))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a3576, a3577, a3578, a3579, -⟩ := hs1
  have e3576 := tb_loadHolds_unique a3576 (hw 2 (by norm_num))
  have v3492 : σ (.n 3492) = ev 12 := by
    rw [← hev 12 (by norm_num)]; exact (vt_evalF h (k := 45) (by norm_num)).2.2
  have hB : σ (.n 3677) = vtSlots W ev 0 [[], [], [([12], 3)], [], []] := by
    simp only [v3492, a3577, e3576, a3465, a3464, a3463]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a3579, a3578, hB]

set_option maxRecDepth 10000 in
theorem vtSide13F {rd : Reader} {σ : Val} (h : VtF rd σ)
    (hq : [σ (.n 1361), σ (.n 1363), σ (.n 1365), σ (.n 1367), σ (.n 1369)] = [σ (.n 959), σ (.n 968), σ (.n 977), σ (.n 986), σ (.n 995)]) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (33 + c))) = ev c) :
    σ (.n 3680) =
      vtSideVal [σ (.n 1361), σ (.n 1363), σ (.n 1365), σ (.n 1367), σ (.n 1369)]
        (σ (.n 14)) W ev vtBTerms13 := by
  have hF0 : σ (.n 3659) =
      vtSideVal [σ (.n 1361), σ (.n 1363), σ (.n 1365), σ (.n 1367), σ (.n 1369)]
        (σ (.n 14)) W ev vtBTerms03 := by
    rw [hq]; exact vtSide03F h hw hev
  have a3580 := h.atomAt 3580 (.add (.n 3680) (.n 3659) (.n 3679)) (by decide +kernel)
  simp only [Atom.Holds] at a3580
  rw [vtSideVal_pull _ _ _ _ _ _ _ vtPull3, ← hF0, a3580, vtD3_4F h hw hev, vtD3_3F h hw hev, vtD3_2F h hw hev, vtD3_1F h hw hev, vtD3_0F h hw hev]
  simp only [vtDiffSum, vtDTerms3, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, add_zero, add_assoc]

set_option maxRecDepth 10000 in
theorem vtSide23F {rd : Reader} {σ : Val} (h : VtF rd σ) {ev : ℕ → E}
    (hev : ∀ c < 14, σ (.n (vtEvB (33 + c))) = ev c) :
    σ (.n 3689) =
      vtSideVal [σ (.n 1519), σ (.n 1528), σ (.n 1537), σ (.n 1546)]
        (0) (fun _ ↦ 1) ev vtBTerms23 := by
  obtain ⟨_, hs0⟩ := h.sliceAt 3466 [
    .atom (.copy (.n 3566) (.n 3471)),
    .atom (.copy (.n 3567) (.n 3488)),
    .atom (.copy (.n 3568) (.n 3492)),
    .atom (.copy (.n 3569) (.n 3496))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a3466, a3467, a3468, a3469, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 3583 [
    .atom (.mul (.n 3683) (.n 1519) (.n 3566)),
    .atom (.mul (.n 3684) (.n 1528) (.n 3567)),
    .atom (.add (.n 3685) (.n 3683) (.n 3684)),
    .atom (.mul (.n 3686) (.n 1537) (.n 3568)),
    .atom (.add (.n 3687) (.n 3685) (.n 3686)),
    .atom (.mul (.n 3688) (.n 1546) (.n 3569)),
    .atom (.add (.n 3689) (.n 3687) (.n 3688))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a3583, a3584, a3585, a3586, a3587, a3588, a3589, -⟩ := hs1
  have v3471 : σ (.n 3471) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_evalF h (k := 43) (by norm_num)).2.2
  have v3488 : σ (.n 3488) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_evalF h (k := 44) (by norm_num)).2.2
  have v3492 : σ (.n 3492) = ev 12 := by
    rw [← hev 12 (by norm_num)]; exact (vt_evalF h (k := 45) (by norm_num)).2.2
  have v3496 : σ (.n 3496) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_evalF h (k := 46) (by norm_num)).2.2
  simp only [v3496, v3492, v3488, v3471, a3589, a3588, a3587, a3586, a3585, a3584, a3583, a3469, a3468, a3467,
    a3466]
  simp only [vtSideVal, vtBTerms23, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, vt_ofK_ofBits_one]
  ring

end
end LeanVM.Guest.B1.Tables
