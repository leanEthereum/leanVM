/-
  LeanVM.Guest.B1.Tables.Vt.FormsT4

  Table 4's forms on the three sides, from the guest's statements: each block's value from its
  baked terms, the table's form the blocks' selectors times their values.
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
    σ (.n 3899) = σ (.n 1003) * vtBlockVal (σ (.n 14)) W ev
      [[([], 1)], [([13, 6], 1), ([13, 0], 2), ([0], 2)], [([13, 7], 1), ([13, 1], 1), ([1], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 3663 [
    .atom (.const (.n 3811) (word 1 0)),
    .atom (.mul (.n 3812) (.n 3802) (.n 3748)),
    .atom (.const (.n 3813) (word 2 0)),
    .atom (.mul (.n 3814) (.n 3802) (.n 3698)),
    .atom (.mul (.n 3815) (.n 3813) (.n 3814)),
    .atom (.add (.n 3816) (.n 3812) (.n 3815)),
    .atom (.const (.n 3817) (word 2 0)),
    .atom (.mul (.n 3818) (.n 3817) (.n 3698)),
    .atom (.add (.n 3819) (.n 3816) (.n 3818)),
    .atom (.copy (.n 3820) (.n 3819)),
    .atom (.mul (.n 3821) (.n 3802) (.n 3752)),
    .atom (.mul (.n 3822) (.n 3802) (.n 3715)),
    .atom (.add (.n 3823) (.n 3821) (.n 3822)),
    .atom (.add (.n 3824) (.n 3823) (.n 3715)),
    .atom (.copy (.n 3825) (.n 3824))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a3663, a3664, a3665, a3666, a3667, a3668, a3669, a3670, a3671, a3672, a3673, a3674, a3675, a3676,
    a3677, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 3742 [
    .atom (.load (.n 3890) (.n 13) 0),
    .atom (.mul (.n 3891) (.n 3890) (.n 3811)),
    .atom (.load (.n 3892) (.n 13) 1),
    .atom (.mul (.n 3893) (.n 3892) (.n 3820)),
    .atom (.add (.n 3894) (.n 3891) (.n 3893)),
    .atom (.load (.n 3895) (.n 13) 2),
    .atom (.mul (.n 3896) (.n 3895) (.n 3825)),
    .atom (.add (.n 3897) (.n 3894) (.n 3896)),
    .atom (.add (.n 3898) (.n 14) (.n 3897)),
    .atom (.mul (.n 3899) (.n 1003) (.n 3898))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a3742, a3743, a3744, a3745, a3746, a3747, a3748, a3749, a3750, a3751, -⟩ := hs1
  have e3742 := tb_loadHolds_unique a3742 (hw 0 (by norm_num))
  have e3744 := tb_loadHolds_unique a3744 (hw 1 (by norm_num))
  have e3747 := tb_loadHolds_unique a3747 (hw 2 (by norm_num))
  have v3698 : σ (.n 3698) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_eval h (k := 47) (by norm_num)).2.2
  have v3715 : σ (.n 3715) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 48) (by norm_num)).2.2
  have v3748 : σ (.n 3748) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_eval h (k := 53) (by norm_num)).2.2
  have v3752 : σ (.n 3752) = ev 7 := by
    rw [← hev 7 (by norm_num)]; exact (vt_eval h (k := 54) (by norm_num)).2.2
  have v3802 : σ (.n 3802) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 60) (by norm_num)).2.2
  have hB : σ (.n 3898) = vtBlockVal (σ (.n 14)) W ev [[([], 1)], [([13, 6], 1), ([13, 0], 2), ([0], 2)], [([13, 7], 1), ([13, 1], 1), ([1], 1)]] := by
    simp only [v3802, v3752, v3748, v3715, v3698, a3750, a3749, a3748, e3747, a3746, a3745, e3744, a3743,
      e3742, a3677, a3676, a3675, a3674, a3673, a3672, a3671, a3670, a3669, a3668, a3667,
      a3666, a3665, a3664, a3663]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a3751, hB]

set_option maxRecDepth 10000 in
theorem vtB04_1 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (47 + c))) = ev c) :
    σ (.n 3928) = σ (.n 3899) + σ (.n 1012) * vtBlockVal (σ (.n 14)) W ev
      [[([], 4)], [([0], 1)], [([11], 2)], [([], 16)], [([2], 1)], [([3], 1)], [([4], 1)], [([], 0)], [([], 0)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 3678 [
    .atom (.const (.n 3826) (word 4 0)),
    .atom (.copy (.n 3827) (.n 3698)),
    .atom (.const (.n 3828) (word 2 0)),
    .atom (.mul (.n 3829) (.n 3828) (.n 3781)),
    .atom (.copy (.n 3830) (.n 3829)),
    .atom (.const (.n 3831) (word 16 0)),
    .atom (.copy (.n 3832) (.n 3719)),
    .atom (.copy (.n 3833) (.n 3723)),
    .atom (.copy (.n 3834) (.n 3727)),
    .atom (.const (.n 3835) (word 0 0)),
    .atom (.const (.n 3836) (word 0 0))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a3678, a3679, a3680, a3681, a3682, a3683, a3684, a3685, a3686, a3687, a3688, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 3752 [
    .atom (.load (.n 3900) (.n 13) 0),
    .atom (.mul (.n 3901) (.n 3900) (.n 3826)),
    .atom (.load (.n 3902) (.n 13) 1),
    .atom (.mul (.n 3903) (.n 3902) (.n 3827)),
    .atom (.add (.n 3904) (.n 3901) (.n 3903)),
    .atom (.load (.n 3905) (.n 13) 2),
    .atom (.mul (.n 3906) (.n 3905) (.n 3830)),
    .atom (.add (.n 3907) (.n 3904) (.n 3906)),
    .atom (.load (.n 3908) (.n 13) 3),
    .atom (.mul (.n 3909) (.n 3908) (.n 3831)),
    .atom (.add (.n 3910) (.n 3907) (.n 3909)),
    .atom (.load (.n 3911) (.n 13) 4),
    .atom (.mul (.n 3912) (.n 3911) (.n 3832)),
    .atom (.add (.n 3913) (.n 3910) (.n 3912)),
    .atom (.load (.n 3914) (.n 13) 5),
    .atom (.mul (.n 3915) (.n 3914) (.n 3833)),
    .atom (.add (.n 3916) (.n 3913) (.n 3915)),
    .atom (.load (.n 3917) (.n 13) 6),
    .atom (.mul (.n 3918) (.n 3917) (.n 3834)),
    .atom (.add (.n 3919) (.n 3916) (.n 3918)),
    .atom (.load (.n 3920) (.n 13) 7),
    .atom (.mul (.n 3921) (.n 3920) (.n 3835)),
    .atom (.add (.n 3922) (.n 3919) (.n 3921)),
    .atom (.load (.n 3923) (.n 13) 8),
    .atom (.mul (.n 3924) (.n 3923) (.n 3836)),
    .atom (.add (.n 3925) (.n 3922) (.n 3924)),
    .atom (.add (.n 3926) (.n 14) (.n 3925)),
    .atom (.mul (.n 3927) (.n 1012) (.n 3926)),
    .atom (.add (.n 3928) (.n 3899) (.n 3927))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a3752, a3753, a3754, a3755, a3756, a3757, a3758, a3759, a3760, a3761, a3762, a3763, a3764, a3765,
    a3766, a3767, a3768, a3769, a3770, a3771, a3772, a3773, a3774, a3775, a3776, a3777, a3778,
    a3779, a3780, -⟩ := hs1
  have e3752 := tb_loadHolds_unique a3752 (hw 0 (by norm_num))
  have e3754 := tb_loadHolds_unique a3754 (hw 1 (by norm_num))
  have e3757 := tb_loadHolds_unique a3757 (hw 2 (by norm_num))
  have e3760 := tb_loadHolds_unique a3760 (hw 3 (by norm_num))
  have e3763 := tb_loadHolds_unique a3763 (hw 4 (by norm_num))
  have e3766 := tb_loadHolds_unique a3766 (hw 5 (by norm_num))
  have e3769 := tb_loadHolds_unique a3769 (hw 6 (by norm_num))
  have e3772 := tb_loadHolds_unique a3772 (hw 7 (by norm_num))
  have e3775 := tb_loadHolds_unique a3775 (hw 8 (by norm_num))
  have v3698 : σ (.n 3698) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_eval h (k := 47) (by norm_num)).2.2
  have v3719 : σ (.n 3719) = ev 2 := by
    rw [← hev 2 (by norm_num)]; exact (vt_eval h (k := 49) (by norm_num)).2.2
  have v3723 : σ (.n 3723) = ev 3 := by
    rw [← hev 3 (by norm_num)]; exact (vt_eval h (k := 50) (by norm_num)).2.2
  have v3727 : σ (.n 3727) = ev 4 := by
    rw [← hev 4 (by norm_num)]; exact (vt_eval h (k := 51) (by norm_num)).2.2
  have v3781 : σ (.n 3781) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_eval h (k := 58) (by norm_num)).2.2
  have hB : σ (.n 3926) = vtBlockVal (σ (.n 14)) W ev [[([], 4)], [([0], 1)], [([11], 2)], [([], 16)], [([2], 1)], [([3], 1)], [([4], 1)], [([], 0)], [([], 0)]] := by
    simp only [v3781, v3727, v3723, v3719, v3698, a3778, a3777, a3776, e3775, a3774, a3773, e3772, a3771,
      a3770, e3769, a3768, a3767, e3766, a3765, a3764, e3763, a3762, a3761, e3760, a3759,
      a3758, e3757, a3756, a3755, e3754, a3753, e3752, a3688, a3687, a3686, a3685, a3684,
      a3683, a3682, a3681, a3680, a3679, a3678]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a3780, a3779, hB]

set_option maxRecDepth 10000 in
theorem vtB04_2 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (47 + c))) = ev c) :
    σ (.n 3945) = σ (.n 3928) + σ (.n 1021) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 2], 1)], [([8], 2)], [([5], 1)], [([], 0)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 3689 [
    .atom (.const (.n 3837) (word 2 0)),
    .atom (.mul (.n 3838) (.n 3715) (.n 3719)),
    .atom (.copy (.n 3839) (.n 3838)),
    .atom (.const (.n 3840) (word 2 0)),
    .atom (.mul (.n 3841) (.n 3840) (.n 3756)),
    .atom (.copy (.n 3842) (.n 3841)),
    .atom (.copy (.n 3843) (.n 3744)),
    .atom (.const (.n 3844) (word 0 0))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a3689, a3690, a3691, a3692, a3693, a3694, a3695, a3696, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 3781 [
    .atom (.load (.n 3929) (.n 13) 0),
    .atom (.mul (.n 3930) (.n 3929) (.n 3837)),
    .atom (.load (.n 3931) (.n 13) 1),
    .atom (.mul (.n 3932) (.n 3931) (.n 3839)),
    .atom (.add (.n 3933) (.n 3930) (.n 3932)),
    .atom (.load (.n 3934) (.n 13) 2),
    .atom (.mul (.n 3935) (.n 3934) (.n 3842)),
    .atom (.add (.n 3936) (.n 3933) (.n 3935)),
    .atom (.load (.n 3937) (.n 13) 3),
    .atom (.mul (.n 3938) (.n 3937) (.n 3843)),
    .atom (.add (.n 3939) (.n 3936) (.n 3938)),
    .atom (.load (.n 3940) (.n 13) 4),
    .atom (.mul (.n 3941) (.n 3940) (.n 3844)),
    .atom (.add (.n 3942) (.n 3939) (.n 3941)),
    .atom (.add (.n 3943) (.n 14) (.n 3942)),
    .atom (.mul (.n 3944) (.n 1021) (.n 3943)),
    .atom (.add (.n 3945) (.n 3928) (.n 3944))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a3781, a3782, a3783, a3784, a3785, a3786, a3787, a3788, a3789, a3790, a3791, a3792, a3793, a3794,
    a3795, a3796, a3797, -⟩ := hs1
  have e3781 := tb_loadHolds_unique a3781 (hw 0 (by norm_num))
  have e3783 := tb_loadHolds_unique a3783 (hw 1 (by norm_num))
  have e3786 := tb_loadHolds_unique a3786 (hw 2 (by norm_num))
  have e3789 := tb_loadHolds_unique a3789 (hw 3 (by norm_num))
  have e3792 := tb_loadHolds_unique a3792 (hw 4 (by norm_num))
  have v3715 : σ (.n 3715) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 48) (by norm_num)).2.2
  have v3719 : σ (.n 3719) = ev 2 := by
    rw [← hev 2 (by norm_num)]; exact (vt_eval h (k := 49) (by norm_num)).2.2
  have v3744 : σ (.n 3744) = ev 5 := by
    rw [← hev 5 (by norm_num)]; exact (vt_eval h (k := 52) (by norm_num)).2.2
  have v3756 : σ (.n 3756) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_eval h (k := 55) (by norm_num)).2.2
  have hB : σ (.n 3943) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 2], 1)], [([8], 2)], [([5], 1)], [([], 0)]] := by
    simp only [v3756, v3744, v3719, v3715, a3795, a3794, a3793, e3792, a3791, a3790, e3789, a3788, a3787,
      e3786, a3785, a3784, e3783, a3782, e3781, a3696, a3695, a3694, a3693, a3692, a3691,
      a3690, a3689]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a3797, a3796, hB]

set_option maxRecDepth 10000 in
theorem vtB04_3 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (47 + c))) = ev c) :
    σ (.n 3962) = σ (.n 3945) + σ (.n 1030) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 3], 1)], [([9], 2)], [([6], 1)], [([], 0)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 3697 [
    .atom (.const (.n 3845) (word 2 0)),
    .atom (.mul (.n 3846) (.n 3715) (.n 3723)),
    .atom (.copy (.n 3847) (.n 3846)),
    .atom (.const (.n 3848) (word 2 0)),
    .atom (.mul (.n 3849) (.n 3848) (.n 3773)),
    .atom (.copy (.n 3850) (.n 3849)),
    .atom (.copy (.n 3851) (.n 3748)),
    .atom (.const (.n 3852) (word 0 0))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a3697, a3698, a3699, a3700, a3701, a3702, a3703, a3704, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 3798 [
    .atom (.load (.n 3946) (.n 13) 0),
    .atom (.mul (.n 3947) (.n 3946) (.n 3845)),
    .atom (.load (.n 3948) (.n 13) 1),
    .atom (.mul (.n 3949) (.n 3948) (.n 3847)),
    .atom (.add (.n 3950) (.n 3947) (.n 3949)),
    .atom (.load (.n 3951) (.n 13) 2),
    .atom (.mul (.n 3952) (.n 3951) (.n 3850)),
    .atom (.add (.n 3953) (.n 3950) (.n 3952)),
    .atom (.load (.n 3954) (.n 13) 3),
    .atom (.mul (.n 3955) (.n 3954) (.n 3851)),
    .atom (.add (.n 3956) (.n 3953) (.n 3955)),
    .atom (.load (.n 3957) (.n 13) 4),
    .atom (.mul (.n 3958) (.n 3957) (.n 3852)),
    .atom (.add (.n 3959) (.n 3956) (.n 3958)),
    .atom (.add (.n 3960) (.n 14) (.n 3959)),
    .atom (.mul (.n 3961) (.n 1030) (.n 3960)),
    .atom (.add (.n 3962) (.n 3945) (.n 3961))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a3798, a3799, a3800, a3801, a3802, a3803, a3804, a3805, a3806, a3807, a3808, a3809, a3810, a3811,
    a3812, a3813, a3814, -⟩ := hs1
  have e3798 := tb_loadHolds_unique a3798 (hw 0 (by norm_num))
  have e3800 := tb_loadHolds_unique a3800 (hw 1 (by norm_num))
  have e3803 := tb_loadHolds_unique a3803 (hw 2 (by norm_num))
  have e3806 := tb_loadHolds_unique a3806 (hw 3 (by norm_num))
  have e3809 := tb_loadHolds_unique a3809 (hw 4 (by norm_num))
  have v3715 : σ (.n 3715) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 48) (by norm_num)).2.2
  have v3723 : σ (.n 3723) = ev 3 := by
    rw [← hev 3 (by norm_num)]; exact (vt_eval h (k := 50) (by norm_num)).2.2
  have v3748 : σ (.n 3748) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_eval h (k := 53) (by norm_num)).2.2
  have v3773 : σ (.n 3773) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 56) (by norm_num)).2.2
  have hB : σ (.n 3960) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 3], 1)], [([9], 2)], [([6], 1)], [([], 0)]] := by
    simp only [v3773, v3748, v3723, v3715, a3812, a3811, a3810, e3809, a3808, a3807, e3806, a3805, a3804,
      e3803, a3802, a3801, e3800, a3799, e3798, a3704, a3703, a3702, a3701, a3700, a3699,
      a3698, a3697]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a3814, a3813, hB]

set_option maxRecDepth 10000 in
theorem vtB04_4 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (47 + c))) = ev c) :
    σ (.n 3979) = σ (.n 3962) + σ (.n 1039) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 4], 1)], [([10], 2)], [([7], 1)], [([], 0)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 3705 [
    .atom (.const (.n 3853) (word 2 0)),
    .atom (.mul (.n 3854) (.n 3715) (.n 3727)),
    .atom (.copy (.n 3855) (.n 3854)),
    .atom (.const (.n 3856) (word 2 0)),
    .atom (.mul (.n 3857) (.n 3856) (.n 3777)),
    .atom (.copy (.n 3858) (.n 3857)),
    .atom (.copy (.n 3859) (.n 3752)),
    .atom (.const (.n 3860) (word 0 0))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a3705, a3706, a3707, a3708, a3709, a3710, a3711, a3712, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 3815 [
    .atom (.load (.n 3963) (.n 13) 0),
    .atom (.mul (.n 3964) (.n 3963) (.n 3853)),
    .atom (.load (.n 3965) (.n 13) 1),
    .atom (.mul (.n 3966) (.n 3965) (.n 3855)),
    .atom (.add (.n 3967) (.n 3964) (.n 3966)),
    .atom (.load (.n 3968) (.n 13) 2),
    .atom (.mul (.n 3969) (.n 3968) (.n 3858)),
    .atom (.add (.n 3970) (.n 3967) (.n 3969)),
    .atom (.load (.n 3971) (.n 13) 3),
    .atom (.mul (.n 3972) (.n 3971) (.n 3859)),
    .atom (.add (.n 3973) (.n 3970) (.n 3972)),
    .atom (.load (.n 3974) (.n 13) 4),
    .atom (.mul (.n 3975) (.n 3974) (.n 3860)),
    .atom (.add (.n 3976) (.n 3973) (.n 3975)),
    .atom (.add (.n 3977) (.n 14) (.n 3976)),
    .atom (.mul (.n 3978) (.n 1039) (.n 3977)),
    .atom (.add (.n 3979) (.n 3962) (.n 3978))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a3815, a3816, a3817, a3818, a3819, a3820, a3821, a3822, a3823, a3824, a3825, a3826, a3827, a3828,
    a3829, a3830, a3831, -⟩ := hs1
  have e3815 := tb_loadHolds_unique a3815 (hw 0 (by norm_num))
  have e3817 := tb_loadHolds_unique a3817 (hw 1 (by norm_num))
  have e3820 := tb_loadHolds_unique a3820 (hw 2 (by norm_num))
  have e3823 := tb_loadHolds_unique a3823 (hw 3 (by norm_num))
  have e3826 := tb_loadHolds_unique a3826 (hw 4 (by norm_num))
  have v3715 : σ (.n 3715) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 48) (by norm_num)).2.2
  have v3727 : σ (.n 3727) = ev 4 := by
    rw [← hev 4 (by norm_num)]; exact (vt_eval h (k := 51) (by norm_num)).2.2
  have v3752 : σ (.n 3752) = ev 7 := by
    rw [← hev 7 (by norm_num)]; exact (vt_eval h (k := 54) (by norm_num)).2.2
  have v3777 : σ (.n 3777) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_eval h (k := 57) (by norm_num)).2.2
  have hB : σ (.n 3977) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 4], 1)], [([10], 2)], [([7], 1)], [([], 0)]] := by
    simp only [v3777, v3752, v3727, v3715, a3829, a3828, a3827, e3826, a3825, a3824, e3823, a3822, a3821,
      e3820, a3819, a3818, e3817, a3816, e3815, a3712, a3711, a3710, a3709, a3708, a3707,
      a3706, a3705]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a3831, a3830, hB]

set_option maxRecDepth 10000 in
theorem vtSide04 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (47 + c))) = ev c) :
    σ (.n 3979) =
      vtSideVal [σ (.n 1003), σ (.n 1012), σ (.n 1021), σ (.n 1030), σ (.n 1039)]
        (σ (.n 14)) W ev vtBTerms04 := by
  rw [vtB04_4 h hw hev, vtB04_3 h hw hev, vtB04_2 h hw hev, vtB04_1 h hw hev, vtB04_0 h hw hev]
  simp only [vtSideVal, vtBTerms04, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, add_zero, add_assoc]

set_option maxRecDepth 10000 in
theorem vtD4_0 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (47 + c))) = ev c) :
    σ (.n 3987) = σ (.n 1370) * vtSlots W ev 0
      [[], [([0], 3), ([0, 13], 2), ([6, 13], 1)], [([1, 13], 1), ([7, 13], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 3713 [
    .atom (.const (.n 3861) (word 3 0)),
    .atom (.mul (.n 3862) (.n 3861) (.n 3698)),
    .atom (.const (.n 3863) (word 2 0)),
    .atom (.mul (.n 3864) (.n 3698) (.n 3802)),
    .atom (.mul (.n 3865) (.n 3863) (.n 3864)),
    .atom (.add (.n 3866) (.n 3862) (.n 3865)),
    .atom (.mul (.n 3867) (.n 3748) (.n 3802)),
    .atom (.add (.n 3868) (.n 3866) (.n 3867)),
    .atom (.copy (.n 3869) (.n 3868)),
    .atom (.mul (.n 3870) (.n 3715) (.n 3802)),
    .atom (.mul (.n 3871) (.n 3752) (.n 3802)),
    .atom (.add (.n 3872) (.n 3870) (.n 3871)),
    .atom (.copy (.n 3873) (.n 3872))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a3713, a3714, a3715, a3716, a3717, a3718, a3719, a3720, a3721, a3722, a3723, a3724, a3725, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 3834 [
    .atom (.load (.n 3982) (.n 13) 1),
    .atom (.mul (.n 3983) (.n 3982) (.n 3869)),
    .atom (.load (.n 3984) (.n 13) 2),
    .atom (.mul (.n 3985) (.n 3984) (.n 3873)),
    .atom (.add (.n 3986) (.n 3983) (.n 3985)),
    .atom (.mul (.n 3987) (.n 1370) (.n 3986))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a3834, a3835, a3836, a3837, a3838, a3839, -⟩ := hs1
  have e3834 := tb_loadHolds_unique a3834 (hw 1 (by norm_num))
  have e3836 := tb_loadHolds_unique a3836 (hw 2 (by norm_num))
  have v3698 : σ (.n 3698) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_eval h (k := 47) (by norm_num)).2.2
  have v3715 : σ (.n 3715) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 48) (by norm_num)).2.2
  have v3748 : σ (.n 3748) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_eval h (k := 53) (by norm_num)).2.2
  have v3752 : σ (.n 3752) = ev 7 := by
    rw [← hev 7 (by norm_num)]; exact (vt_eval h (k := 54) (by norm_num)).2.2
  have v3802 : σ (.n 3802) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 60) (by norm_num)).2.2
  have hB : σ (.n 3986) = vtSlots W ev 0 [[], [([0], 3), ([0, 13], 2), ([6, 13], 1)], [([1, 13], 1), ([7, 13], 1)]] := by
    simp only [v3802, v3752, v3748, v3715, v3698, a3838, a3837, e3836, a3835, e3834, a3725, a3724, a3723,
      a3722, a3721, a3720, a3719, a3718, a3717, a3716, a3715, a3714, a3713]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a3839, hB]

set_option maxRecDepth 10000 in
theorem vtD4_1 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (47 + c))) = ev c) :
    σ (.n 3991) = σ (.n 3987) + σ (.n 1372) * vtSlots W ev 0
      [[], [], [([11], 3)], [], [], [], [], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 3726 [
    .atom (.const (.n 3874) (word 3 0)),
    .atom (.mul (.n 3875) (.n 3874) (.n 3781)),
    .atom (.copy (.n 3876) (.n 3875))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a3726, a3727, a3728, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 3840 [
    .atom (.load (.n 3988) (.n 13) 2),
    .atom (.mul (.n 3989) (.n 3988) (.n 3876)),
    .atom (.mul (.n 3990) (.n 1372) (.n 3989)),
    .atom (.add (.n 3991) (.n 3987) (.n 3990))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a3840, a3841, a3842, a3843, -⟩ := hs1
  have e3840 := tb_loadHolds_unique a3840 (hw 2 (by norm_num))
  have v3781 : σ (.n 3781) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_eval h (k := 58) (by norm_num)).2.2
  have hB : σ (.n 3989) = vtSlots W ev 0 [[], [], [([11], 3)], [], [], [], [], [], []] := by
    simp only [v3781, a3841, e3840, a3728, a3727, a3726]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a3843, a3842, hB]

set_option maxRecDepth 10000 in
theorem vtD4_2 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (47 + c))) = ev c) :
    σ (.n 3995) = σ (.n 3991) + σ (.n 1374) * vtSlots W ev 0
      [[], [], [([8], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 3729 [
    .atom (.const (.n 3877) (word 3 0)),
    .atom (.mul (.n 3878) (.n 3877) (.n 3756)),
    .atom (.copy (.n 3879) (.n 3878))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a3729, a3730, a3731, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 3844 [
    .atom (.load (.n 3992) (.n 13) 2),
    .atom (.mul (.n 3993) (.n 3992) (.n 3879)),
    .atom (.mul (.n 3994) (.n 1374) (.n 3993)),
    .atom (.add (.n 3995) (.n 3991) (.n 3994))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a3844, a3845, a3846, a3847, -⟩ := hs1
  have e3844 := tb_loadHolds_unique a3844 (hw 2 (by norm_num))
  have v3756 : σ (.n 3756) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_eval h (k := 55) (by norm_num)).2.2
  have hB : σ (.n 3993) = vtSlots W ev 0 [[], [], [([8], 3)], [], []] := by
    simp only [v3756, a3845, e3844, a3731, a3730, a3729]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a3847, a3846, hB]

set_option maxRecDepth 10000 in
theorem vtD4_3 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (47 + c))) = ev c) :
    σ (.n 3999) = σ (.n 3995) + σ (.n 1376) * vtSlots W ev 0
      [[], [], [([9], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 3732 [
    .atom (.const (.n 3880) (word 3 0)),
    .atom (.mul (.n 3881) (.n 3880) (.n 3773)),
    .atom (.copy (.n 3882) (.n 3881))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a3732, a3733, a3734, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 3848 [
    .atom (.load (.n 3996) (.n 13) 2),
    .atom (.mul (.n 3997) (.n 3996) (.n 3882)),
    .atom (.mul (.n 3998) (.n 1376) (.n 3997)),
    .atom (.add (.n 3999) (.n 3995) (.n 3998))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a3848, a3849, a3850, a3851, -⟩ := hs1
  have e3848 := tb_loadHolds_unique a3848 (hw 2 (by norm_num))
  have v3773 : σ (.n 3773) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 56) (by norm_num)).2.2
  have hB : σ (.n 3997) = vtSlots W ev 0 [[], [], [([9], 3)], [], []] := by
    simp only [v3773, a3849, e3848, a3734, a3733, a3732]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a3851, a3850, hB]

set_option maxRecDepth 10000 in
theorem vtD4_4 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (47 + c))) = ev c) :
    σ (.n 4003) = σ (.n 3999) + σ (.n 1378) * vtSlots W ev 0
      [[], [], [([10], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 3735 [
    .atom (.const (.n 3883) (word 3 0)),
    .atom (.mul (.n 3884) (.n 3883) (.n 3777)),
    .atom (.copy (.n 3885) (.n 3884))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a3735, a3736, a3737, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 3852 [
    .atom (.load (.n 4000) (.n 13) 2),
    .atom (.mul (.n 4001) (.n 4000) (.n 3885)),
    .atom (.mul (.n 4002) (.n 1378) (.n 4001)),
    .atom (.add (.n 4003) (.n 3999) (.n 4002))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a3852, a3853, a3854, a3855, -⟩ := hs1
  have e3852 := tb_loadHolds_unique a3852 (hw 2 (by norm_num))
  have v3777 : σ (.n 3777) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_eval h (k := 57) (by norm_num)).2.2
  have hB : σ (.n 4001) = vtSlots W ev 0 [[], [], [([10], 3)], [], []] := by
    simp only [v3777, a3853, e3852, a3737, a3736, a3735]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a3855, a3854, hB]

set_option maxRecDepth 10000 in
theorem vtSide14 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (47 + c))) = ev c) :
    σ (.n 4004) =
      vtSideVal [σ (.n 1370), σ (.n 1372), σ (.n 1374), σ (.n 1376), σ (.n 1378)]
        (σ (.n 14)) W ev vtBTerms14 := by
  have hF0 : σ (.n 3979) =
      vtSideVal [σ (.n 1370), σ (.n 1372), σ (.n 1374), σ (.n 1376), σ (.n 1378)]
        (σ (.n 14)) W ev vtBTerms04 := by
    rw [vtPullSels4 h]; exact vtSide04 h hw hev
  have a3856 := h.atomAt 3856 (.add (.n 4004) (.n 3979) (.n 4003)) (by decide +kernel)
  simp only [Atom.Holds] at a3856
  rw [vtSideVal_pull _ _ _ _ _ _ _ vtPull4, ← hF0, a3856, vtD4_4 h hw hev, vtD4_3 h hw hev, vtD4_2 h hw hev, vtD4_1 h hw hev, vtD4_0 h hw hev]
  simp only [vtDiffSum, vtDTerms4, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, add_zero, add_assoc]

set_option maxRecDepth 10000 in
theorem vtSide24 {rd : Reader} {σ : Val} (h : VtH rd σ) {ev : ℕ → E}
    (hev : ∀ c < 14, σ (.n (vtEvB (47 + c))) = ev c) :
    σ (.n 4013) =
      vtSideVal [σ (.n 1554), σ (.n 1563), σ (.n 1572), σ (.n 1581)]
        (0) (fun _ ↦ 1) ev vtBTerms24 := by
  obtain ⟨_, hs0⟩ := h.sliceAt 3738 [
    .atom (.copy (.n 3886) (.n 3756)),
    .atom (.copy (.n 3887) (.n 3773)),
    .atom (.copy (.n 3888) (.n 3777)),
    .atom (.copy (.n 3889) (.n 3781))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a3738, a3739, a3740, a3741, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 3859 [
    .atom (.mul (.n 4007) (.n 1554) (.n 3886)),
    .atom (.mul (.n 4008) (.n 1563) (.n 3887)),
    .atom (.add (.n 4009) (.n 4007) (.n 4008)),
    .atom (.mul (.n 4010) (.n 1572) (.n 3888)),
    .atom (.add (.n 4011) (.n 4009) (.n 4010)),
    .atom (.mul (.n 4012) (.n 1581) (.n 3889)),
    .atom (.add (.n 4013) (.n 4011) (.n 4012))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a3859, a3860, a3861, a3862, a3863, a3864, a3865, -⟩ := hs1
  have v3756 : σ (.n 3756) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_eval h (k := 55) (by norm_num)).2.2
  have v3773 : σ (.n 3773) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 56) (by norm_num)).2.2
  have v3777 : σ (.n 3777) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_eval h (k := 57) (by norm_num)).2.2
  have v3781 : σ (.n 3781) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_eval h (k := 58) (by norm_num)).2.2
  simp only [v3781, v3777, v3773, v3756, a3865, a3864, a3863, a3862, a3861, a3860, a3859, a3741, a3740, a3739,
    a3738]
  simp only [vtSideVal, vtBTerms24, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, vt_ofK_ofBits_one]
  ring

end
end LeanVM.Guest.B1.Tables
