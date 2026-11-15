/-
  LeanVM.Guest.B1.Tables.Vt.FormsT4

  Table 4's forms on the three sides, from the guest's statements: each block's value from its
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
theorem vtB04_0 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (47 + c))) = ev c) :
    σ (.n 3904) = σ (.n 1004) * vtBlockVal (σ (.n 14)) W ev
      [[([], 1)], [([13, 6], 1), ([13, 0], 2), ([0], 2)], [([13, 7], 1), ([13, 1], 1), ([1], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 3668 [
    .atom (.const (.n 3816) (word 1 0)),
    .atom (.mul (.n 3817) (.n 3807) (.n 3753)),
    .atom (.const (.n 3818) (word 2 0)),
    .atom (.mul (.n 3819) (.n 3807) (.n 3703)),
    .atom (.mul (.n 3820) (.n 3818) (.n 3819)),
    .atom (.add (.n 3821) (.n 3817) (.n 3820)),
    .atom (.const (.n 3822) (word 2 0)),
    .atom (.mul (.n 3823) (.n 3822) (.n 3703)),
    .atom (.add (.n 3824) (.n 3821) (.n 3823)),
    .atom (.copy (.n 3825) (.n 3824)),
    .atom (.mul (.n 3826) (.n 3807) (.n 3757)),
    .atom (.mul (.n 3827) (.n 3807) (.n 3720)),
    .atom (.add (.n 3828) (.n 3826) (.n 3827)),
    .atom (.add (.n 3829) (.n 3828) (.n 3720)),
    .atom (.copy (.n 3830) (.n 3829))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a3668, a3669, a3670, a3671, a3672, a3673, a3674, a3675, a3676, a3677, a3678, a3679, a3680, a3681,
    a3682, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 3747 [
    .atom (.load (.n 3895) (.n 13) 0),
    .atom (.mul (.n 3896) (.n 3895) (.n 3816)),
    .atom (.load (.n 3897) (.n 13) 1),
    .atom (.mul (.n 3898) (.n 3897) (.n 3825)),
    .atom (.add (.n 3899) (.n 3896) (.n 3898)),
    .atom (.load (.n 3900) (.n 13) 2),
    .atom (.mul (.n 3901) (.n 3900) (.n 3830)),
    .atom (.add (.n 3902) (.n 3899) (.n 3901)),
    .atom (.add (.n 3903) (.n 14) (.n 3902)),
    .atom (.mul (.n 3904) (.n 1004) (.n 3903))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a3747, a3748, a3749, a3750, a3751, a3752, a3753, a3754, a3755, a3756, -⟩ := hs1
  have e3747 := tb_loadHolds_unique a3747 (hw 0 (by norm_num))
  have e3749 := tb_loadHolds_unique a3749 (hw 1 (by norm_num))
  have e3752 := tb_loadHolds_unique a3752 (hw 2 (by norm_num))
  have v3703 : σ (.n 3703) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_eval h (k := 47) (by norm_num)).2.2
  have v3720 : σ (.n 3720) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 48) (by norm_num)).2.2
  have v3753 : σ (.n 3753) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_eval h (k := 53) (by norm_num)).2.2
  have v3757 : σ (.n 3757) = ev 7 := by
    rw [← hev 7 (by norm_num)]; exact (vt_eval h (k := 54) (by norm_num)).2.2
  have v3807 : σ (.n 3807) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 60) (by norm_num)).2.2
  have hB : σ (.n 3903) = vtBlockVal (σ (.n 14)) W ev [[([], 1)], [([13, 6], 1), ([13, 0], 2), ([0], 2)], [([13, 7], 1), ([13, 1], 1), ([1], 1)]] := by
    simp only [v3807, v3757, v3753, v3720, v3703, a3755, a3754, a3753, e3752, a3751, a3750, e3749, a3748,
      e3747, a3682, a3681, a3680, a3679, a3678, a3677, a3676, a3675, a3674, a3673, a3672,
      a3671, a3670, a3669, a3668]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a3756, hB]

set_option maxRecDepth 10000 in
theorem vtB04_1 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (47 + c))) = ev c) :
    σ (.n 3933) = σ (.n 3904) + σ (.n 1013) * vtBlockVal (σ (.n 14)) W ev
      [[([], 4)], [([0], 1)], [([11], 2)], [([], 16)], [([2], 1)], [([3], 1)], [([4], 1)], [([], 0)], [([], 0)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 3683 [
    .atom (.const (.n 3831) (word 4 0)),
    .atom (.copy (.n 3832) (.n 3703)),
    .atom (.const (.n 3833) (word 2 0)),
    .atom (.mul (.n 3834) (.n 3833) (.n 3786)),
    .atom (.copy (.n 3835) (.n 3834)),
    .atom (.const (.n 3836) (word 16 0)),
    .atom (.copy (.n 3837) (.n 3724)),
    .atom (.copy (.n 3838) (.n 3728)),
    .atom (.copy (.n 3839) (.n 3732)),
    .atom (.const (.n 3840) (word 0 0)),
    .atom (.const (.n 3841) (word 0 0))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a3683, a3684, a3685, a3686, a3687, a3688, a3689, a3690, a3691, a3692, a3693, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 3757 [
    .atom (.load (.n 3905) (.n 13) 0),
    .atom (.mul (.n 3906) (.n 3905) (.n 3831)),
    .atom (.load (.n 3907) (.n 13) 1),
    .atom (.mul (.n 3908) (.n 3907) (.n 3832)),
    .atom (.add (.n 3909) (.n 3906) (.n 3908)),
    .atom (.load (.n 3910) (.n 13) 2),
    .atom (.mul (.n 3911) (.n 3910) (.n 3835)),
    .atom (.add (.n 3912) (.n 3909) (.n 3911)),
    .atom (.load (.n 3913) (.n 13) 3),
    .atom (.mul (.n 3914) (.n 3913) (.n 3836)),
    .atom (.add (.n 3915) (.n 3912) (.n 3914)),
    .atom (.load (.n 3916) (.n 13) 4),
    .atom (.mul (.n 3917) (.n 3916) (.n 3837)),
    .atom (.add (.n 3918) (.n 3915) (.n 3917)),
    .atom (.load (.n 3919) (.n 13) 5),
    .atom (.mul (.n 3920) (.n 3919) (.n 3838)),
    .atom (.add (.n 3921) (.n 3918) (.n 3920)),
    .atom (.load (.n 3922) (.n 13) 6),
    .atom (.mul (.n 3923) (.n 3922) (.n 3839)),
    .atom (.add (.n 3924) (.n 3921) (.n 3923)),
    .atom (.load (.n 3925) (.n 13) 7),
    .atom (.mul (.n 3926) (.n 3925) (.n 3840)),
    .atom (.add (.n 3927) (.n 3924) (.n 3926)),
    .atom (.load (.n 3928) (.n 13) 8),
    .atom (.mul (.n 3929) (.n 3928) (.n 3841)),
    .atom (.add (.n 3930) (.n 3927) (.n 3929)),
    .atom (.add (.n 3931) (.n 14) (.n 3930)),
    .atom (.mul (.n 3932) (.n 1013) (.n 3931)),
    .atom (.add (.n 3933) (.n 3904) (.n 3932))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a3757, a3758, a3759, a3760, a3761, a3762, a3763, a3764, a3765, a3766, a3767, a3768, a3769, a3770,
    a3771, a3772, a3773, a3774, a3775, a3776, a3777, a3778, a3779, a3780, a3781, a3782, a3783,
    a3784, a3785, -⟩ := hs1
  have e3757 := tb_loadHolds_unique a3757 (hw 0 (by norm_num))
  have e3759 := tb_loadHolds_unique a3759 (hw 1 (by norm_num))
  have e3762 := tb_loadHolds_unique a3762 (hw 2 (by norm_num))
  have e3765 := tb_loadHolds_unique a3765 (hw 3 (by norm_num))
  have e3768 := tb_loadHolds_unique a3768 (hw 4 (by norm_num))
  have e3771 := tb_loadHolds_unique a3771 (hw 5 (by norm_num))
  have e3774 := tb_loadHolds_unique a3774 (hw 6 (by norm_num))
  have e3777 := tb_loadHolds_unique a3777 (hw 7 (by norm_num))
  have e3780 := tb_loadHolds_unique a3780 (hw 8 (by norm_num))
  have v3703 : σ (.n 3703) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_eval h (k := 47) (by norm_num)).2.2
  have v3724 : σ (.n 3724) = ev 2 := by
    rw [← hev 2 (by norm_num)]; exact (vt_eval h (k := 49) (by norm_num)).2.2
  have v3728 : σ (.n 3728) = ev 3 := by
    rw [← hev 3 (by norm_num)]; exact (vt_eval h (k := 50) (by norm_num)).2.2
  have v3732 : σ (.n 3732) = ev 4 := by
    rw [← hev 4 (by norm_num)]; exact (vt_eval h (k := 51) (by norm_num)).2.2
  have v3786 : σ (.n 3786) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_eval h (k := 58) (by norm_num)).2.2
  have hB : σ (.n 3931) = vtBlockVal (σ (.n 14)) W ev [[([], 4)], [([0], 1)], [([11], 2)], [([], 16)], [([2], 1)], [([3], 1)], [([4], 1)], [([], 0)], [([], 0)]] := by
    simp only [v3786, v3732, v3728, v3724, v3703, a3783, a3782, a3781, e3780, a3779, a3778, e3777, a3776,
      a3775, e3774, a3773, a3772, e3771, a3770, a3769, e3768, a3767, a3766, e3765, a3764,
      a3763, e3762, a3761, a3760, e3759, a3758, e3757, a3693, a3692, a3691, a3690, a3689,
      a3688, a3687, a3686, a3685, a3684, a3683]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a3785, a3784, hB]

set_option maxRecDepth 10000 in
theorem vtB04_2 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (47 + c))) = ev c) :
    σ (.n 3950) = σ (.n 3933) + σ (.n 1022) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 2], 1)], [([8], 2)], [([5], 1)], [([], 0)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 3694 [
    .atom (.const (.n 3842) (word 2 0)),
    .atom (.mul (.n 3843) (.n 3720) (.n 3724)),
    .atom (.copy (.n 3844) (.n 3843)),
    .atom (.const (.n 3845) (word 2 0)),
    .atom (.mul (.n 3846) (.n 3845) (.n 3761)),
    .atom (.copy (.n 3847) (.n 3846)),
    .atom (.copy (.n 3848) (.n 3749)),
    .atom (.const (.n 3849) (word 0 0))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a3694, a3695, a3696, a3697, a3698, a3699, a3700, a3701, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 3786 [
    .atom (.load (.n 3934) (.n 13) 0),
    .atom (.mul (.n 3935) (.n 3934) (.n 3842)),
    .atom (.load (.n 3936) (.n 13) 1),
    .atom (.mul (.n 3937) (.n 3936) (.n 3844)),
    .atom (.add (.n 3938) (.n 3935) (.n 3937)),
    .atom (.load (.n 3939) (.n 13) 2),
    .atom (.mul (.n 3940) (.n 3939) (.n 3847)),
    .atom (.add (.n 3941) (.n 3938) (.n 3940)),
    .atom (.load (.n 3942) (.n 13) 3),
    .atom (.mul (.n 3943) (.n 3942) (.n 3848)),
    .atom (.add (.n 3944) (.n 3941) (.n 3943)),
    .atom (.load (.n 3945) (.n 13) 4),
    .atom (.mul (.n 3946) (.n 3945) (.n 3849)),
    .atom (.add (.n 3947) (.n 3944) (.n 3946)),
    .atom (.add (.n 3948) (.n 14) (.n 3947)),
    .atom (.mul (.n 3949) (.n 1022) (.n 3948)),
    .atom (.add (.n 3950) (.n 3933) (.n 3949))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a3786, a3787, a3788, a3789, a3790, a3791, a3792, a3793, a3794, a3795, a3796, a3797, a3798, a3799,
    a3800, a3801, a3802, -⟩ := hs1
  have e3786 := tb_loadHolds_unique a3786 (hw 0 (by norm_num))
  have e3788 := tb_loadHolds_unique a3788 (hw 1 (by norm_num))
  have e3791 := tb_loadHolds_unique a3791 (hw 2 (by norm_num))
  have e3794 := tb_loadHolds_unique a3794 (hw 3 (by norm_num))
  have e3797 := tb_loadHolds_unique a3797 (hw 4 (by norm_num))
  have v3720 : σ (.n 3720) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 48) (by norm_num)).2.2
  have v3724 : σ (.n 3724) = ev 2 := by
    rw [← hev 2 (by norm_num)]; exact (vt_eval h (k := 49) (by norm_num)).2.2
  have v3749 : σ (.n 3749) = ev 5 := by
    rw [← hev 5 (by norm_num)]; exact (vt_eval h (k := 52) (by norm_num)).2.2
  have v3761 : σ (.n 3761) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_eval h (k := 55) (by norm_num)).2.2
  have hB : σ (.n 3948) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 2], 1)], [([8], 2)], [([5], 1)], [([], 0)]] := by
    simp only [v3761, v3749, v3724, v3720, a3800, a3799, a3798, e3797, a3796, a3795, e3794, a3793, a3792,
      e3791, a3790, a3789, e3788, a3787, e3786, a3701, a3700, a3699, a3698, a3697, a3696,
      a3695, a3694]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a3802, a3801, hB]

set_option maxRecDepth 10000 in
theorem vtB04_3 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (47 + c))) = ev c) :
    σ (.n 3967) = σ (.n 3950) + σ (.n 1031) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 3], 1)], [([9], 2)], [([6], 1)], [([], 0)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 3702 [
    .atom (.const (.n 3850) (word 2 0)),
    .atom (.mul (.n 3851) (.n 3720) (.n 3728)),
    .atom (.copy (.n 3852) (.n 3851)),
    .atom (.const (.n 3853) (word 2 0)),
    .atom (.mul (.n 3854) (.n 3853) (.n 3778)),
    .atom (.copy (.n 3855) (.n 3854)),
    .atom (.copy (.n 3856) (.n 3753)),
    .atom (.const (.n 3857) (word 0 0))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a3702, a3703, a3704, a3705, a3706, a3707, a3708, a3709, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 3803 [
    .atom (.load (.n 3951) (.n 13) 0),
    .atom (.mul (.n 3952) (.n 3951) (.n 3850)),
    .atom (.load (.n 3953) (.n 13) 1),
    .atom (.mul (.n 3954) (.n 3953) (.n 3852)),
    .atom (.add (.n 3955) (.n 3952) (.n 3954)),
    .atom (.load (.n 3956) (.n 13) 2),
    .atom (.mul (.n 3957) (.n 3956) (.n 3855)),
    .atom (.add (.n 3958) (.n 3955) (.n 3957)),
    .atom (.load (.n 3959) (.n 13) 3),
    .atom (.mul (.n 3960) (.n 3959) (.n 3856)),
    .atom (.add (.n 3961) (.n 3958) (.n 3960)),
    .atom (.load (.n 3962) (.n 13) 4),
    .atom (.mul (.n 3963) (.n 3962) (.n 3857)),
    .atom (.add (.n 3964) (.n 3961) (.n 3963)),
    .atom (.add (.n 3965) (.n 14) (.n 3964)),
    .atom (.mul (.n 3966) (.n 1031) (.n 3965)),
    .atom (.add (.n 3967) (.n 3950) (.n 3966))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a3803, a3804, a3805, a3806, a3807, a3808, a3809, a3810, a3811, a3812, a3813, a3814, a3815, a3816,
    a3817, a3818, a3819, -⟩ := hs1
  have e3803 := tb_loadHolds_unique a3803 (hw 0 (by norm_num))
  have e3805 := tb_loadHolds_unique a3805 (hw 1 (by norm_num))
  have e3808 := tb_loadHolds_unique a3808 (hw 2 (by norm_num))
  have e3811 := tb_loadHolds_unique a3811 (hw 3 (by norm_num))
  have e3814 := tb_loadHolds_unique a3814 (hw 4 (by norm_num))
  have v3720 : σ (.n 3720) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 48) (by norm_num)).2.2
  have v3728 : σ (.n 3728) = ev 3 := by
    rw [← hev 3 (by norm_num)]; exact (vt_eval h (k := 50) (by norm_num)).2.2
  have v3753 : σ (.n 3753) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_eval h (k := 53) (by norm_num)).2.2
  have v3778 : σ (.n 3778) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 56) (by norm_num)).2.2
  have hB : σ (.n 3965) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 3], 1)], [([9], 2)], [([6], 1)], [([], 0)]] := by
    simp only [v3778, v3753, v3728, v3720, a3817, a3816, a3815, e3814, a3813, a3812, e3811, a3810, a3809,
      e3808, a3807, a3806, e3805, a3804, e3803, a3709, a3708, a3707, a3706, a3705, a3704,
      a3703, a3702]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a3819, a3818, hB]

set_option maxRecDepth 10000 in
theorem vtB04_4 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (47 + c))) = ev c) :
    σ (.n 3984) = σ (.n 3967) + σ (.n 1040) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 4], 1)], [([10], 2)], [([7], 1)], [([], 0)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 3710 [
    .atom (.const (.n 3858) (word 2 0)),
    .atom (.mul (.n 3859) (.n 3720) (.n 3732)),
    .atom (.copy (.n 3860) (.n 3859)),
    .atom (.const (.n 3861) (word 2 0)),
    .atom (.mul (.n 3862) (.n 3861) (.n 3782)),
    .atom (.copy (.n 3863) (.n 3862)),
    .atom (.copy (.n 3864) (.n 3757)),
    .atom (.const (.n 3865) (word 0 0))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a3710, a3711, a3712, a3713, a3714, a3715, a3716, a3717, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 3820 [
    .atom (.load (.n 3968) (.n 13) 0),
    .atom (.mul (.n 3969) (.n 3968) (.n 3858)),
    .atom (.load (.n 3970) (.n 13) 1),
    .atom (.mul (.n 3971) (.n 3970) (.n 3860)),
    .atom (.add (.n 3972) (.n 3969) (.n 3971)),
    .atom (.load (.n 3973) (.n 13) 2),
    .atom (.mul (.n 3974) (.n 3973) (.n 3863)),
    .atom (.add (.n 3975) (.n 3972) (.n 3974)),
    .atom (.load (.n 3976) (.n 13) 3),
    .atom (.mul (.n 3977) (.n 3976) (.n 3864)),
    .atom (.add (.n 3978) (.n 3975) (.n 3977)),
    .atom (.load (.n 3979) (.n 13) 4),
    .atom (.mul (.n 3980) (.n 3979) (.n 3865)),
    .atom (.add (.n 3981) (.n 3978) (.n 3980)),
    .atom (.add (.n 3982) (.n 14) (.n 3981)),
    .atom (.mul (.n 3983) (.n 1040) (.n 3982)),
    .atom (.add (.n 3984) (.n 3967) (.n 3983))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a3820, a3821, a3822, a3823, a3824, a3825, a3826, a3827, a3828, a3829, a3830, a3831, a3832, a3833,
    a3834, a3835, a3836, -⟩ := hs1
  have e3820 := tb_loadHolds_unique a3820 (hw 0 (by norm_num))
  have e3822 := tb_loadHolds_unique a3822 (hw 1 (by norm_num))
  have e3825 := tb_loadHolds_unique a3825 (hw 2 (by norm_num))
  have e3828 := tb_loadHolds_unique a3828 (hw 3 (by norm_num))
  have e3831 := tb_loadHolds_unique a3831 (hw 4 (by norm_num))
  have v3720 : σ (.n 3720) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 48) (by norm_num)).2.2
  have v3732 : σ (.n 3732) = ev 4 := by
    rw [← hev 4 (by norm_num)]; exact (vt_eval h (k := 51) (by norm_num)).2.2
  have v3757 : σ (.n 3757) = ev 7 := by
    rw [← hev 7 (by norm_num)]; exact (vt_eval h (k := 54) (by norm_num)).2.2
  have v3782 : σ (.n 3782) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_eval h (k := 57) (by norm_num)).2.2
  have hB : σ (.n 3982) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 4], 1)], [([10], 2)], [([7], 1)], [([], 0)]] := by
    simp only [v3782, v3757, v3732, v3720, a3834, a3833, a3832, e3831, a3830, a3829, e3828, a3827, a3826,
      e3825, a3824, a3823, e3822, a3821, e3820, a3717, a3716, a3715, a3714, a3713, a3712,
      a3711, a3710]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a3836, a3835, hB]

set_option maxRecDepth 10000 in
theorem vtSide04 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (47 + c))) = ev c) :
    σ (.n 3984) =
      vtSideVal [σ (.n 1004), σ (.n 1013), σ (.n 1022), σ (.n 1031), σ (.n 1040)]
        (σ (.n 14)) W ev vtBTerms04 := by
  rw [vtB04_4 h hw hev, vtB04_3 h hw hev, vtB04_2 h hw hev, vtB04_1 h hw hev, vtB04_0 h hw hev]
  simp only [vtSideVal, vtBTerms04, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, add_zero, add_assoc]

set_option maxRecDepth 10000 in
theorem vtD4_0 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (47 + c))) = ev c) :
    σ (.n 3992) = σ (.n 1371) * vtSlots W ev 0
      [[], [([0], 3), ([0, 13], 2), ([6, 13], 1)], [([1, 13], 1), ([7, 13], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 3718 [
    .atom (.const (.n 3866) (word 3 0)),
    .atom (.mul (.n 3867) (.n 3866) (.n 3703)),
    .atom (.const (.n 3868) (word 2 0)),
    .atom (.mul (.n 3869) (.n 3703) (.n 3807)),
    .atom (.mul (.n 3870) (.n 3868) (.n 3869)),
    .atom (.add (.n 3871) (.n 3867) (.n 3870)),
    .atom (.mul (.n 3872) (.n 3753) (.n 3807)),
    .atom (.add (.n 3873) (.n 3871) (.n 3872)),
    .atom (.copy (.n 3874) (.n 3873)),
    .atom (.mul (.n 3875) (.n 3720) (.n 3807)),
    .atom (.mul (.n 3876) (.n 3757) (.n 3807)),
    .atom (.add (.n 3877) (.n 3875) (.n 3876)),
    .atom (.copy (.n 3878) (.n 3877))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a3718, a3719, a3720, a3721, a3722, a3723, a3724, a3725, a3726, a3727, a3728, a3729, a3730, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 3839 [
    .atom (.load (.n 3987) (.n 13) 1),
    .atom (.mul (.n 3988) (.n 3987) (.n 3874)),
    .atom (.load (.n 3989) (.n 13) 2),
    .atom (.mul (.n 3990) (.n 3989) (.n 3878)),
    .atom (.add (.n 3991) (.n 3988) (.n 3990)),
    .atom (.mul (.n 3992) (.n 1371) (.n 3991))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a3839, a3840, a3841, a3842, a3843, a3844, -⟩ := hs1
  have e3839 := tb_loadHolds_unique a3839 (hw 1 (by norm_num))
  have e3841 := tb_loadHolds_unique a3841 (hw 2 (by norm_num))
  have v3703 : σ (.n 3703) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_eval h (k := 47) (by norm_num)).2.2
  have v3720 : σ (.n 3720) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 48) (by norm_num)).2.2
  have v3753 : σ (.n 3753) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_eval h (k := 53) (by norm_num)).2.2
  have v3757 : σ (.n 3757) = ev 7 := by
    rw [← hev 7 (by norm_num)]; exact (vt_eval h (k := 54) (by norm_num)).2.2
  have v3807 : σ (.n 3807) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 60) (by norm_num)).2.2
  have hB : σ (.n 3991) = vtSlots W ev 0 [[], [([0], 3), ([0, 13], 2), ([6, 13], 1)], [([1, 13], 1), ([7, 13], 1)]] := by
    simp only [v3807, v3757, v3753, v3720, v3703, a3843, a3842, e3841, a3840, e3839, a3730, a3729, a3728,
      a3727, a3726, a3725, a3724, a3723, a3722, a3721, a3720, a3719, a3718]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a3844, hB]

set_option maxRecDepth 10000 in
theorem vtD4_1 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (47 + c))) = ev c) :
    σ (.n 3996) = σ (.n 3992) + σ (.n 1373) * vtSlots W ev 0
      [[], [], [([11], 3)], [], [], [], [], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 3731 [
    .atom (.const (.n 3879) (word 3 0)),
    .atom (.mul (.n 3880) (.n 3879) (.n 3786)),
    .atom (.copy (.n 3881) (.n 3880))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a3731, a3732, a3733, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 3845 [
    .atom (.load (.n 3993) (.n 13) 2),
    .atom (.mul (.n 3994) (.n 3993) (.n 3881)),
    .atom (.mul (.n 3995) (.n 1373) (.n 3994)),
    .atom (.add (.n 3996) (.n 3992) (.n 3995))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a3845, a3846, a3847, a3848, -⟩ := hs1
  have e3845 := tb_loadHolds_unique a3845 (hw 2 (by norm_num))
  have v3786 : σ (.n 3786) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_eval h (k := 58) (by norm_num)).2.2
  have hB : σ (.n 3994) = vtSlots W ev 0 [[], [], [([11], 3)], [], [], [], [], [], []] := by
    simp only [v3786, a3846, e3845, a3733, a3732, a3731]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a3848, a3847, hB]

set_option maxRecDepth 10000 in
theorem vtD4_2 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (47 + c))) = ev c) :
    σ (.n 4000) = σ (.n 3996) + σ (.n 1375) * vtSlots W ev 0
      [[], [], [([8], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 3734 [
    .atom (.const (.n 3882) (word 3 0)),
    .atom (.mul (.n 3883) (.n 3882) (.n 3761)),
    .atom (.copy (.n 3884) (.n 3883))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a3734, a3735, a3736, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 3849 [
    .atom (.load (.n 3997) (.n 13) 2),
    .atom (.mul (.n 3998) (.n 3997) (.n 3884)),
    .atom (.mul (.n 3999) (.n 1375) (.n 3998)),
    .atom (.add (.n 4000) (.n 3996) (.n 3999))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a3849, a3850, a3851, a3852, -⟩ := hs1
  have e3849 := tb_loadHolds_unique a3849 (hw 2 (by norm_num))
  have v3761 : σ (.n 3761) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_eval h (k := 55) (by norm_num)).2.2
  have hB : σ (.n 3998) = vtSlots W ev 0 [[], [], [([8], 3)], [], []] := by
    simp only [v3761, a3850, e3849, a3736, a3735, a3734]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a3852, a3851, hB]

set_option maxRecDepth 10000 in
theorem vtD4_3 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (47 + c))) = ev c) :
    σ (.n 4004) = σ (.n 4000) + σ (.n 1377) * vtSlots W ev 0
      [[], [], [([9], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 3737 [
    .atom (.const (.n 3885) (word 3 0)),
    .atom (.mul (.n 3886) (.n 3885) (.n 3778)),
    .atom (.copy (.n 3887) (.n 3886))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a3737, a3738, a3739, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 3853 [
    .atom (.load (.n 4001) (.n 13) 2),
    .atom (.mul (.n 4002) (.n 4001) (.n 3887)),
    .atom (.mul (.n 4003) (.n 1377) (.n 4002)),
    .atom (.add (.n 4004) (.n 4000) (.n 4003))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a3853, a3854, a3855, a3856, -⟩ := hs1
  have e3853 := tb_loadHolds_unique a3853 (hw 2 (by norm_num))
  have v3778 : σ (.n 3778) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 56) (by norm_num)).2.2
  have hB : σ (.n 4002) = vtSlots W ev 0 [[], [], [([9], 3)], [], []] := by
    simp only [v3778, a3854, e3853, a3739, a3738, a3737]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a3856, a3855, hB]

set_option maxRecDepth 10000 in
theorem vtD4_4 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (47 + c))) = ev c) :
    σ (.n 4008) = σ (.n 4004) + σ (.n 1379) * vtSlots W ev 0
      [[], [], [([10], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 3740 [
    .atom (.const (.n 3888) (word 3 0)),
    .atom (.mul (.n 3889) (.n 3888) (.n 3782)),
    .atom (.copy (.n 3890) (.n 3889))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a3740, a3741, a3742, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 3857 [
    .atom (.load (.n 4005) (.n 13) 2),
    .atom (.mul (.n 4006) (.n 4005) (.n 3890)),
    .atom (.mul (.n 4007) (.n 1379) (.n 4006)),
    .atom (.add (.n 4008) (.n 4004) (.n 4007))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a3857, a3858, a3859, a3860, -⟩ := hs1
  have e3857 := tb_loadHolds_unique a3857 (hw 2 (by norm_num))
  have v3782 : σ (.n 3782) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_eval h (k := 57) (by norm_num)).2.2
  have hB : σ (.n 4006) = vtSlots W ev 0 [[], [], [([10], 3)], [], []] := by
    simp only [v3782, a3858, e3857, a3742, a3741, a3740]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a3860, a3859, hB]

set_option maxRecDepth 10000 in
theorem vtSide14 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (47 + c))) = ev c) :
    σ (.n 4009) =
      vtSideVal [σ (.n 1371), σ (.n 1373), σ (.n 1375), σ (.n 1377), σ (.n 1379)]
        (σ (.n 14)) W ev vtBTerms14 := by
  have hF0 : σ (.n 3984) =
      vtSideVal [σ (.n 1371), σ (.n 1373), σ (.n 1375), σ (.n 1377), σ (.n 1379)]
        (σ (.n 14)) W ev vtBTerms04 := by
    rw [vtPullSels4 h]; exact vtSide04 h hw hev
  have a3861 := h.atomAt 3861 (.add (.n 4009) (.n 3984) (.n 4008)) (by decide +kernel)
  simp only [Atom.Holds] at a3861
  rw [vtSideVal_pull _ _ _ _ _ _ _ vtPull4, ← hF0, a3861, vtD4_4 h hw hev, vtD4_3 h hw hev, vtD4_2 h hw hev, vtD4_1 h hw hev, vtD4_0 h hw hev]
  simp only [vtDiffSum, vtDTerms4, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, add_zero, add_assoc]

set_option maxRecDepth 10000 in
theorem vtSide24 {rd : Reader} {σ : Val} (h : VtH rd σ) {ev : ℕ → E}
    (hev : ∀ c < 14, σ (.n (vtEvB (47 + c))) = ev c) :
    σ (.n 4018) =
      vtSideVal [σ (.n 1555), σ (.n 1564), σ (.n 1573), σ (.n 1582)]
        (0) (fun _ ↦ 1) ev vtBTerms24 := by
  obtain ⟨_, hs0⟩ := h.sliceAt 3743 [
    .atom (.copy (.n 3891) (.n 3761)),
    .atom (.copy (.n 3892) (.n 3778)),
    .atom (.copy (.n 3893) (.n 3782)),
    .atom (.copy (.n 3894) (.n 3786))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a3743, a3744, a3745, a3746, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 3864 [
    .atom (.mul (.n 4012) (.n 1555) (.n 3891)),
    .atom (.mul (.n 4013) (.n 1564) (.n 3892)),
    .atom (.add (.n 4014) (.n 4012) (.n 4013)),
    .atom (.mul (.n 4015) (.n 1573) (.n 3893)),
    .atom (.add (.n 4016) (.n 4014) (.n 4015)),
    .atom (.mul (.n 4017) (.n 1582) (.n 3894)),
    .atom (.add (.n 4018) (.n 4016) (.n 4017))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a3864, a3865, a3866, a3867, a3868, a3869, a3870, -⟩ := hs1
  have v3761 : σ (.n 3761) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_eval h (k := 55) (by norm_num)).2.2
  have v3778 : σ (.n 3778) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 56) (by norm_num)).2.2
  have v3782 : σ (.n 3782) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_eval h (k := 57) (by norm_num)).2.2
  have v3786 : σ (.n 3786) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_eval h (k := 58) (by norm_num)).2.2
  simp only [v3786, v3782, v3778, v3761, a3870, a3869, a3868, a3867, a3866, a3865, a3864, a3746, a3745, a3744,
    a3743]
  simp only [vtSideVal, vtBTerms24, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, vt_ofK_ofBits_one]
  ring

end
end LeanVM.Guest.B1.Tables
