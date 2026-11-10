/-
  LeanVM.Guest.B1.Tables.Vt.FormsT3

  Table 3's forms on the three sides, from the guest's statements: each block's value from its
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
theorem vtB03_0 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (38 + c))) = ev c) :
    σ (.n 3853) = σ (.n 1061) * vtBlockVal (σ (.n 14)) W ev
      [[([], 1)], [([0], 2)], [([1], 1)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 3691 [
    .atom (.load (.n 3843) (.n 13) 0),
    .atom (.const (.n 3844) (word 2 0)),
    .atom (.mul (.n 3845) (.n 3844) (.n 3636)),
    .atom (.load (.n 3846) (.n 13) 1),
    .atom (.mul (.n 3847) (.n 3846) (.n 3845)),
    .atom (.add (.n 3848) (.n 3843) (.n 3847)),
    .atom (.load (.n 3849) (.n 13) 2),
    .atom (.mul (.n 3850) (.n 3849) (.n 3647)),
    .atom (.add (.n 3851) (.n 3848) (.n 3850)),
    .atom (.add (.n 3852) (.n 14) (.n 3851)),
    .atom (.mul (.n 3853) (.n 1061) (.n 3852))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a3691, a3692, a3693, a3694, a3695, a3696, a3697, a3698, a3699, a3700, a3701, -⟩ := hs
  have e3691 := tb_loadHolds_unique a3691 (hw 0 (by norm_num))
  have e3694 := tb_loadHolds_unique a3694 (hw 1 (by norm_num))
  have e3697 := tb_loadHolds_unique a3697 (hw 2 (by norm_num))
  have v3636 : σ (.n 3636) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_eval h (k := 38) (by norm_num)).2.2
  have v3647 : σ (.n 3647) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 39) (by norm_num)).2.2
  have hB : σ (.n 3852) = vtBlockVal (σ (.n 14)) W ev [[([], 1)], [([0], 2)], [([1], 1)]] := by
    simp only [v3647, v3636, a3700, a3699, a3698, e3697, a3696, a3695, e3694, a3693, a3692, e3691]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a3701, hB]

set_option maxRecDepth 10000 in
theorem vtB03_1 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (38 + c))) = ev c) :
    σ (.n 3886) = σ (.n 3853) + σ (.n 1070) * vtBlockVal (σ (.n 14)) W ev
      [[([], 4)], [([0], 1)], [([14], 2)], [([], 8)], [([2], 1)], [([3], 1)], [([4], 1)], [([5], 1)], [([6], 1)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 3702 [
    .atom (.load (.n 3854) (.n 13) 0),
    .atom (.const (.n 3855) (word 4 0)),
    .atom (.mul (.n 3856) (.n 3854) (.n 3855)),
    .atom (.load (.n 3857) (.n 13) 1),
    .atom (.mul (.n 3858) (.n 3857) (.n 3636)),
    .atom (.add (.n 3859) (.n 3856) (.n 3858)),
    .atom (.const (.n 3860) (word 2 0)),
    .atom (.mul (.n 3861) (.n 3860) (.n 3842)),
    .atom (.load (.n 3862) (.n 13) 2),
    .atom (.mul (.n 3863) (.n 3862) (.n 3861)),
    .atom (.add (.n 3864) (.n 3859) (.n 3863)),
    .atom (.load (.n 3865) (.n 13) 3),
    .atom (.const (.n 3866) (word 8 0)),
    .atom (.mul (.n 3867) (.n 3865) (.n 3866)),
    .atom (.add (.n 3868) (.n 3864) (.n 3867)),
    .atom (.load (.n 3869) (.n 13) 4),
    .atom (.mul (.n 3870) (.n 3869) (.n 3671)),
    .atom (.add (.n 3871) (.n 3868) (.n 3870)),
    .atom (.load (.n 3872) (.n 13) 5),
    .atom (.mul (.n 3873) (.n 3872) (.n 3682)),
    .atom (.add (.n 3874) (.n 3871) (.n 3873)),
    .atom (.load (.n 3875) (.n 13) 6),
    .atom (.mul (.n 3876) (.n 3875) (.n 3693)),
    .atom (.add (.n 3877) (.n 3874) (.n 3876)),
    .atom (.load (.n 3878) (.n 13) 7),
    .atom (.mul (.n 3879) (.n 3878) (.n 3704)),
    .atom (.add (.n 3880) (.n 3877) (.n 3879)),
    .atom (.load (.n 3881) (.n 13) 8),
    .atom (.mul (.n 3882) (.n 3881) (.n 3728)),
    .atom (.add (.n 3883) (.n 3880) (.n 3882)),
    .atom (.add (.n 3884) (.n 14) (.n 3883)),
    .atom (.mul (.n 3885) (.n 1070) (.n 3884)),
    .atom (.add (.n 3886) (.n 3853) (.n 3885))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a3702, a3703, a3704, a3705, a3706, a3707, a3708, a3709, a3710, a3711, a3712, a3713, a3714, a3715,
    a3716, a3717, a3718, a3719, a3720, a3721, a3722, a3723, a3724, a3725, a3726, a3727, a3728,
    a3729, a3730, a3731, a3732, a3733, a3734, -⟩ := hs
  have e3702 := tb_loadHolds_unique a3702 (hw 0 (by norm_num))
  have e3705 := tb_loadHolds_unique a3705 (hw 1 (by norm_num))
  have e3710 := tb_loadHolds_unique a3710 (hw 2 (by norm_num))
  have e3713 := tb_loadHolds_unique a3713 (hw 3 (by norm_num))
  have e3717 := tb_loadHolds_unique a3717 (hw 4 (by norm_num))
  have e3720 := tb_loadHolds_unique a3720 (hw 5 (by norm_num))
  have e3723 := tb_loadHolds_unique a3723 (hw 6 (by norm_num))
  have e3726 := tb_loadHolds_unique a3726 (hw 7 (by norm_num))
  have e3729 := tb_loadHolds_unique a3729 (hw 8 (by norm_num))
  have v3636 : σ (.n 3636) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_eval h (k := 38) (by norm_num)).2.2
  have v3671 : σ (.n 3671) = ev 2 := by
    rw [← hev 2 (by norm_num)]; exact (vt_eval h (k := 40) (by norm_num)).2.2
  have v3682 : σ (.n 3682) = ev 3 := by
    rw [← hev 3 (by norm_num)]; exact (vt_eval h (k := 41) (by norm_num)).2.2
  have v3693 : σ (.n 3693) = ev 4 := by
    rw [← hev 4 (by norm_num)]; exact (vt_eval h (k := 42) (by norm_num)).2.2
  have v3704 : σ (.n 3704) = ev 5 := by
    rw [← hev 5 (by norm_num)]; exact (vt_eval h (k := 43) (by norm_num)).2.2
  have v3728 : σ (.n 3728) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_eval h (k := 44) (by norm_num)).2.2
  have v3842 : σ (.n 3842) = ev 14 := by
    rw [← hev 14 (by norm_num)]; exact (vt_eval h (k := 52) (by norm_num)).2.2
  have hB : σ (.n 3884) = vtBlockVal (σ (.n 14)) W ev [[([], 4)], [([0], 1)], [([14], 2)], [([], 8)], [([2], 1)], [([3], 1)], [([4], 1)], [([5], 1)], [([6], 1)]] := by
    simp only [v3842, v3728, v3704, v3693, v3682, v3671, v3636, a3732, a3731, a3730, e3729, a3728, a3727,
      e3726, a3725, a3724, e3723, a3722, a3721, e3720, a3719, a3718, e3717, a3716, a3715,
      a3714, e3713, a3712, a3711, e3710, a3709, a3708, a3707, a3706, e3705, a3704, a3703,
      e3702]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a3734, a3733, hB]

set_option maxRecDepth 10000 in
theorem vtB03_2 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (38 + c))) = ev c) :
    σ (.n 3912) = σ (.n 3886) + σ (.n 1079) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 2], 1)], [([11], 2)], [([7], 1)], [([], 0)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 3735 [
    .atom (.load (.n 3887) (.n 13) 0),
    .atom (.const (.n 3888) (word 2 0)),
    .atom (.mul (.n 3889) (.n 3887) (.n 3888)),
    .atom (.mul (.n 3890) (.n 3647) (.n 3671)),
    .atom (.load (.n 3891) (.n 13) 1),
    .atom (.mul (.n 3892) (.n 3891) (.n 3890)),
    .atom (.add (.n 3893) (.n 3889) (.n 3892)),
    .atom (.const (.n 3894) (word 2 0)),
    .atom (.mul (.n 3895) (.n 3894) (.n 3796)),
    .atom (.load (.n 3896) (.n 13) 2),
    .atom (.mul (.n 3897) (.n 3896) (.n 3895)),
    .atom (.add (.n 3898) (.n 3893) (.n 3897)),
    .atom (.load (.n 3899) (.n 13) 3),
    .atom (.mul (.n 3900) (.n 3899) (.n 3739)),
    .atom (.add (.n 3901) (.n 3898) (.n 3900)),
    .atom (.load (.n 3902) (.n 13) 4),
    .atom (.const (.n 3903) (word 0 0)),
    .atom (.mul (.n 3904) (.n 3902) (.n 3903)),
    .atom (.add (.n 3905) (.n 3901) (.n 3904)),
    .atom (.load (.n 3906) (.n 13) 5),
    .atom (.const (.n 3907) (word 0 0)),
    .atom (.mul (.n 3908) (.n 3906) (.n 3907)),
    .atom (.add (.n 3909) (.n 3905) (.n 3908)),
    .atom (.add (.n 3910) (.n 14) (.n 3909)),
    .atom (.mul (.n 3911) (.n 1079) (.n 3910)),
    .atom (.add (.n 3912) (.n 3886) (.n 3911))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a3735, a3736, a3737, a3738, a3739, a3740, a3741, a3742, a3743, a3744, a3745, a3746, a3747, a3748,
    a3749, a3750, a3751, a3752, a3753, a3754, a3755, a3756, a3757, a3758, a3759, a3760, -⟩ := hs
  have e3735 := tb_loadHolds_unique a3735 (hw 0 (by norm_num))
  have e3739 := tb_loadHolds_unique a3739 (hw 1 (by norm_num))
  have e3744 := tb_loadHolds_unique a3744 (hw 2 (by norm_num))
  have e3747 := tb_loadHolds_unique a3747 (hw 3 (by norm_num))
  have e3750 := tb_loadHolds_unique a3750 (hw 4 (by norm_num))
  have e3754 := tb_loadHolds_unique a3754 (hw 5 (by norm_num))
  have v3647 : σ (.n 3647) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 39) (by norm_num)).2.2
  have v3671 : σ (.n 3671) = ev 2 := by
    rw [← hev 2 (by norm_num)]; exact (vt_eval h (k := 40) (by norm_num)).2.2
  have v3739 : σ (.n 3739) = ev 7 := by
    rw [← hev 7 (by norm_num)]; exact (vt_eval h (k := 45) (by norm_num)).2.2
  have v3796 : σ (.n 3796) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_eval h (k := 49) (by norm_num)).2.2
  have hB : σ (.n 3910) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 2], 1)], [([11], 2)], [([7], 1)], [([], 0)], [([], 0)]] := by
    simp only [v3796, v3739, v3671, v3647, a3758, a3757, a3756, a3755, e3754, a3753, a3752, a3751, e3750,
      a3749, a3748, e3747, a3746, a3745, e3744, a3743, a3742, a3741, a3740, e3739, a3738,
      a3737, a3736, e3735]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a3760, a3759, hB]

set_option maxRecDepth 10000 in
theorem vtB03_3 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (38 + c))) = ev c) :
    σ (.n 3954) = σ (.n 3912) + σ (.n 1088) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([7, 3], 1)], [([12], 2)], [([8], 1), ([5, 8], 1), ([6, 8], 1), ([5, 0], 4), ([6, 1], 1)], [([9], 1), ([5, 9], 1), ([6, 9], 1)], [([10], 1), ([5, 10], 1), ([6, 10], 1)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 3761 [
    .atom (.load (.n 3913) (.n 13) 0),
    .atom (.const (.n 3914) (word 2 0)),
    .atom (.mul (.n 3915) (.n 3913) (.n 3914)),
    .atom (.mul (.n 3916) (.n 3739) (.n 3682)),
    .atom (.load (.n 3917) (.n 13) 1),
    .atom (.mul (.n 3918) (.n 3917) (.n 3916)),
    .atom (.add (.n 3919) (.n 3915) (.n 3918)),
    .atom (.const (.n 3920) (word 2 0)),
    .atom (.mul (.n 3921) (.n 3920) (.n 3807)),
    .atom (.load (.n 3922) (.n 13) 2),
    .atom (.mul (.n 3923) (.n 3922) (.n 3921)),
    .atom (.add (.n 3924) (.n 3919) (.n 3923)),
    .atom (.mul (.n 3925) (.n 3704) (.n 3750)),
    .atom (.add (.n 3926) (.n 3750) (.n 3925)),
    .atom (.mul (.n 3927) (.n 3728) (.n 3750)),
    .atom (.add (.n 3928) (.n 3926) (.n 3927)),
    .atom (.const (.n 3929) (word 4 0)),
    .atom (.mul (.n 3930) (.n 3704) (.n 3636)),
    .atom (.mul (.n 3931) (.n 3929) (.n 3930)),
    .atom (.add (.n 3932) (.n 3928) (.n 3931)),
    .atom (.mul (.n 3933) (.n 3728) (.n 3647)),
    .atom (.add (.n 3934) (.n 3932) (.n 3933)),
    .atom (.load (.n 3935) (.n 13) 3),
    .atom (.mul (.n 3936) (.n 3935) (.n 3934)),
    .atom (.add (.n 3937) (.n 3924) (.n 3936)),
    .atom (.mul (.n 3938) (.n 3704) (.n 3761)),
    .atom (.add (.n 3939) (.n 3761) (.n 3938)),
    .atom (.mul (.n 3940) (.n 3728) (.n 3761)),
    .atom (.add (.n 3941) (.n 3939) (.n 3940)),
    .atom (.load (.n 3942) (.n 13) 4),
    .atom (.mul (.n 3943) (.n 3942) (.n 3941)),
    .atom (.add (.n 3944) (.n 3937) (.n 3943)),
    .atom (.mul (.n 3945) (.n 3704) (.n 3785)),
    .atom (.add (.n 3946) (.n 3785) (.n 3945)),
    .atom (.mul (.n 3947) (.n 3728) (.n 3785)),
    .atom (.add (.n 3948) (.n 3946) (.n 3947)),
    .atom (.load (.n 3949) (.n 13) 5),
    .atom (.mul (.n 3950) (.n 3949) (.n 3948)),
    .atom (.add (.n 3951) (.n 3944) (.n 3950)),
    .atom (.add (.n 3952) (.n 14) (.n 3951)),
    .atom (.mul (.n 3953) (.n 1088) (.n 3952)),
    .atom (.add (.n 3954) (.n 3912) (.n 3953))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a3761, a3762, a3763, a3764, a3765, a3766, a3767, a3768, a3769, a3770, a3771, a3772, a3773, a3774,
    a3775, a3776, a3777, a3778, a3779, a3780, a3781, a3782, a3783, a3784, a3785, a3786, a3787,
    a3788, a3789, a3790, a3791, a3792, a3793, a3794, a3795, a3796, a3797, a3798, a3799, a3800,
    a3801, a3802, -⟩ := hs
  have e3761 := tb_loadHolds_unique a3761 (hw 0 (by norm_num))
  have e3765 := tb_loadHolds_unique a3765 (hw 1 (by norm_num))
  have e3770 := tb_loadHolds_unique a3770 (hw 2 (by norm_num))
  have e3783 := tb_loadHolds_unique a3783 (hw 3 (by norm_num))
  have e3790 := tb_loadHolds_unique a3790 (hw 4 (by norm_num))
  have e3797 := tb_loadHolds_unique a3797 (hw 5 (by norm_num))
  have v3636 : σ (.n 3636) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_eval h (k := 38) (by norm_num)).2.2
  have v3647 : σ (.n 3647) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 39) (by norm_num)).2.2
  have v3682 : σ (.n 3682) = ev 3 := by
    rw [← hev 3 (by norm_num)]; exact (vt_eval h (k := 41) (by norm_num)).2.2
  have v3704 : σ (.n 3704) = ev 5 := by
    rw [← hev 5 (by norm_num)]; exact (vt_eval h (k := 43) (by norm_num)).2.2
  have v3728 : σ (.n 3728) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_eval h (k := 44) (by norm_num)).2.2
  have v3739 : σ (.n 3739) = ev 7 := by
    rw [← hev 7 (by norm_num)]; exact (vt_eval h (k := 45) (by norm_num)).2.2
  have v3750 : σ (.n 3750) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_eval h (k := 46) (by norm_num)).2.2
  have v3761 : σ (.n 3761) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 47) (by norm_num)).2.2
  have v3785 : σ (.n 3785) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_eval h (k := 48) (by norm_num)).2.2
  have v3807 : σ (.n 3807) = ev 12 := by
    rw [← hev 12 (by norm_num)]; exact (vt_eval h (k := 50) (by norm_num)).2.2
  have hB : σ (.n 3952) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([7, 3], 1)], [([12], 2)], [([8], 1), ([5, 8], 1), ([6, 8], 1), ([5, 0], 4), ([6, 1], 1)], [([9], 1), ([5, 9], 1), ([6, 9], 1)], [([10], 1), ([5, 10], 1), ([6, 10], 1)]] := by
    simp only [v3807, v3785, v3761, v3750, v3739, v3728, v3704, v3682, v3647, v3636, a3800, a3799, a3798,
      e3797, a3796, a3795, a3794, a3793, a3792, a3791, e3790, a3789, a3788, a3787, a3786,
      a3785, a3784, e3783, a3782, a3781, a3780, a3779, a3778, a3777, a3776, a3775, a3774,
      a3773, a3772, a3771, e3770, a3769, a3768, a3767, a3766, e3765, a3764, a3763, a3762,
      e3761]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a3802, a3801, hB]

set_option maxRecDepth 10000 in
theorem vtB03_4 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (38 + c))) = ev c) :
    σ (.n 3978) = σ (.n 3954) + σ (.n 1097) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 4], 1)], [([13], 2)], [([8], 1)], [([9], 1)], [([10], 1)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 3803 [
    .atom (.load (.n 3955) (.n 13) 0),
    .atom (.const (.n 3956) (word 2 0)),
    .atom (.mul (.n 3957) (.n 3955) (.n 3956)),
    .atom (.mul (.n 3958) (.n 3647) (.n 3693)),
    .atom (.load (.n 3959) (.n 13) 1),
    .atom (.mul (.n 3960) (.n 3959) (.n 3958)),
    .atom (.add (.n 3961) (.n 3957) (.n 3960)),
    .atom (.const (.n 3962) (word 2 0)),
    .atom (.mul (.n 3963) (.n 3962) (.n 3818)),
    .atom (.load (.n 3964) (.n 13) 2),
    .atom (.mul (.n 3965) (.n 3964) (.n 3963)),
    .atom (.add (.n 3966) (.n 3961) (.n 3965)),
    .atom (.load (.n 3967) (.n 13) 3),
    .atom (.mul (.n 3968) (.n 3967) (.n 3750)),
    .atom (.add (.n 3969) (.n 3966) (.n 3968)),
    .atom (.load (.n 3970) (.n 13) 4),
    .atom (.mul (.n 3971) (.n 3970) (.n 3761)),
    .atom (.add (.n 3972) (.n 3969) (.n 3971)),
    .atom (.load (.n 3973) (.n 13) 5),
    .atom (.mul (.n 3974) (.n 3973) (.n 3785)),
    .atom (.add (.n 3975) (.n 3972) (.n 3974)),
    .atom (.add (.n 3976) (.n 14) (.n 3975)),
    .atom (.mul (.n 3977) (.n 1097) (.n 3976)),
    .atom (.add (.n 3978) (.n 3954) (.n 3977))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a3803, a3804, a3805, a3806, a3807, a3808, a3809, a3810, a3811, a3812, a3813, a3814, a3815, a3816,
    a3817, a3818, a3819, a3820, a3821, a3822, a3823, a3824, a3825, a3826, -⟩ := hs
  have e3803 := tb_loadHolds_unique a3803 (hw 0 (by norm_num))
  have e3807 := tb_loadHolds_unique a3807 (hw 1 (by norm_num))
  have e3812 := tb_loadHolds_unique a3812 (hw 2 (by norm_num))
  have e3815 := tb_loadHolds_unique a3815 (hw 3 (by norm_num))
  have e3818 := tb_loadHolds_unique a3818 (hw 4 (by norm_num))
  have e3821 := tb_loadHolds_unique a3821 (hw 5 (by norm_num))
  have v3647 : σ (.n 3647) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 39) (by norm_num)).2.2
  have v3693 : σ (.n 3693) = ev 4 := by
    rw [← hev 4 (by norm_num)]; exact (vt_eval h (k := 42) (by norm_num)).2.2
  have v3750 : σ (.n 3750) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_eval h (k := 46) (by norm_num)).2.2
  have v3761 : σ (.n 3761) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 47) (by norm_num)).2.2
  have v3785 : σ (.n 3785) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_eval h (k := 48) (by norm_num)).2.2
  have v3818 : σ (.n 3818) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 51) (by norm_num)).2.2
  have hB : σ (.n 3976) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 4], 1)], [([13], 2)], [([8], 1)], [([9], 1)], [([10], 1)]] := by
    simp only [v3818, v3785, v3761, v3750, v3693, v3647, a3824, a3823, a3822, e3821, a3820, a3819, e3818,
      a3817, a3816, e3815, a3814, a3813, e3812, a3811, a3810, a3809, a3808, e3807, a3806,
      a3805, a3804, e3803]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a3826, a3825, hB]

set_option maxRecDepth 10000 in
theorem vtSide03 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (38 + c))) = ev c) :
    σ (.n 3978) =
      vtSideVal [σ (.n 1061), σ (.n 1070), σ (.n 1079), σ (.n 1088), σ (.n 1097)]
        (σ (.n 14)) W ev vtBTerms03 := by
  rw [vtB03_4 h hw hev, vtB03_3 h hw hev, vtB03_2 h hw hev, vtB03_1 h hw hev, vtB03_0 h hw hev]
  simp only [vtSideVal, vtBTerms03, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, add_zero, add_assoc]

set_option maxRecDepth 10000 in
theorem vtD3_0 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (38 + c))) = ev c) :
    σ (.n 3984) = σ (.n 1994) * vtSlots W ev 0
      [[], [([0], 3)], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 3828 [
    .atom (.const (.n 3980) (word 3 0)),
    .atom (.mul (.n 3981) (.n 3980) (.n 3636)),
    .atom (.load (.n 3982) (.n 13) 1),
    .atom (.mul (.n 3983) (.n 3982) (.n 3981)),
    .atom (.mul (.n 3984) (.n 1994) (.n 3983))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a3828, a3829, a3830, a3831, a3832, -⟩ := hs
  have e3830 := tb_loadHolds_unique a3830 (hw 1 (by norm_num))
  have v3636 : σ (.n 3636) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_eval h (k := 38) (by norm_num)).2.2
  have hB : σ (.n 3983) = vtSlots W ev 0 [[], [([0], 3)], []] := by
    simp only [v3636, a3831, e3830, a3829, a3828]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a3832, hB]

set_option maxRecDepth 10000 in
theorem vtD3_1 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (38 + c))) = ev c) :
    σ (.n 3990) = σ (.n 3984) + σ (.n 1996) * vtSlots W ev 0
      [[], [], [([14], 3)], [], [], [], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 3833 [
    .atom (.const (.n 3985) (word 3 0)),
    .atom (.mul (.n 3986) (.n 3985) (.n 3842)),
    .atom (.load (.n 3987) (.n 13) 2),
    .atom (.mul (.n 3988) (.n 3987) (.n 3986)),
    .atom (.mul (.n 3989) (.n 1996) (.n 3988)),
    .atom (.add (.n 3990) (.n 3984) (.n 3989))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a3833, a3834, a3835, a3836, a3837, a3838, -⟩ := hs
  have e3835 := tb_loadHolds_unique a3835 (hw 2 (by norm_num))
  have v3842 : σ (.n 3842) = ev 14 := by
    rw [← hev 14 (by norm_num)]; exact (vt_eval h (k := 52) (by norm_num)).2.2
  have hB : σ (.n 3988) = vtSlots W ev 0 [[], [], [([14], 3)], [], [], [], [], [], []] := by
    simp only [v3842, a3836, e3835, a3834, a3833]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a3838, a3837, hB]

set_option maxRecDepth 10000 in
theorem vtD3_2 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (38 + c))) = ev c) :
    σ (.n 3996) = σ (.n 3990) + σ (.n 1998) * vtSlots W ev 0
      [[], [], [([11], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 3839 [
    .atom (.const (.n 3991) (word 3 0)),
    .atom (.mul (.n 3992) (.n 3991) (.n 3796)),
    .atom (.load (.n 3993) (.n 13) 2),
    .atom (.mul (.n 3994) (.n 3993) (.n 3992)),
    .atom (.mul (.n 3995) (.n 1998) (.n 3994)),
    .atom (.add (.n 3996) (.n 3990) (.n 3995))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a3839, a3840, a3841, a3842, a3843, a3844, -⟩ := hs
  have e3841 := tb_loadHolds_unique a3841 (hw 2 (by norm_num))
  have v3796 : σ (.n 3796) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_eval h (k := 49) (by norm_num)).2.2
  have hB : σ (.n 3994) = vtSlots W ev 0 [[], [], [([11], 3)], [], [], []] := by
    simp only [v3796, a3842, e3841, a3840, a3839]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a3844, a3843, hB]

set_option maxRecDepth 10000 in
theorem vtD3_3 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (38 + c))) = ev c) :
    σ (.n 4002) = σ (.n 3996) + σ (.n 2000) * vtSlots W ev 0
      [[], [], [([12], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 3845 [
    .atom (.const (.n 3997) (word 3 0)),
    .atom (.mul (.n 3998) (.n 3997) (.n 3807)),
    .atom (.load (.n 3999) (.n 13) 2),
    .atom (.mul (.n 4000) (.n 3999) (.n 3998)),
    .atom (.mul (.n 4001) (.n 2000) (.n 4000)),
    .atom (.add (.n 4002) (.n 3996) (.n 4001))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a3845, a3846, a3847, a3848, a3849, a3850, -⟩ := hs
  have e3847 := tb_loadHolds_unique a3847 (hw 2 (by norm_num))
  have v3807 : σ (.n 3807) = ev 12 := by
    rw [← hev 12 (by norm_num)]; exact (vt_eval h (k := 50) (by norm_num)).2.2
  have hB : σ (.n 4000) = vtSlots W ev 0 [[], [], [([12], 3)], [], [], []] := by
    simp only [v3807, a3848, e3847, a3846, a3845]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a3850, a3849, hB]

set_option maxRecDepth 10000 in
theorem vtD3_4 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (38 + c))) = ev c) :
    σ (.n 4008) = σ (.n 4002) + σ (.n 2002) * vtSlots W ev 0
      [[], [], [([13], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 3851 [
    .atom (.const (.n 4003) (word 3 0)),
    .atom (.mul (.n 4004) (.n 4003) (.n 3818)),
    .atom (.load (.n 4005) (.n 13) 2),
    .atom (.mul (.n 4006) (.n 4005) (.n 4004)),
    .atom (.mul (.n 4007) (.n 2002) (.n 4006)),
    .atom (.add (.n 4008) (.n 4002) (.n 4007))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a3851, a3852, a3853, a3854, a3855, a3856, -⟩ := hs
  have e3853 := tb_loadHolds_unique a3853 (hw 2 (by norm_num))
  have v3818 : σ (.n 3818) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 51) (by norm_num)).2.2
  have hB : σ (.n 4006) = vtSlots W ev 0 [[], [], [([13], 3)], [], [], []] := by
    simp only [v3818, a3854, e3853, a3852, a3851]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a3856, a3855, hB]

set_option maxRecDepth 10000 in
theorem vtSide13 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (38 + c))) = ev c) :
    σ (.n 4009) =
      vtSideVal [σ (.n 1994), σ (.n 1996), σ (.n 1998), σ (.n 2000), σ (.n 2002)]
        (σ (.n 14)) W ev vtBTerms13 := by
  have hF0 : σ (.n 3978) =
      vtSideVal [σ (.n 1994), σ (.n 1996), σ (.n 1998), σ (.n 2000), σ (.n 2002)]
        (σ (.n 14)) W ev vtBTerms03 := by
    rw [vtPullSels3 h]; exact vtSide03 h hw hev
  have a3857 := h.atomAt 3857 (.add (.n 4009) (.n 3978) (.n 4008)) (by decide +kernel)
  simp only [Atom.Holds] at a3857
  rw [vtSideVal_pull _ _ _ _ _ _ _ vtPull3, ← hF0, a3857, vtD3_4 h hw hev, vtD3_3 h hw hev, vtD3_2 h hw hev, vtD3_1 h hw hev, vtD3_0 h hw hev]
  simp only [vtDiffSum, vtDTerms3, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, add_zero, add_assoc]

set_option maxRecDepth 10000 in
theorem vtSide23 {rd : Reader} {σ : Val} (h : VtH rd σ) {ev : ℕ → E}
    (hev : ∀ c < 15, σ (.n (vtEvB (38 + c))) = ev c) :
    σ (.n 4018) =
      vtSideVal [σ (.n 2155), σ (.n 2164), σ (.n 2173), σ (.n 2182)]
        (0) (fun _ ↦ 1) ev vtBTerms23 := by
  obtain ⟨_, hs⟩ := h.sliceAt 3860 [
    .atom (.mul (.n 4012) (.n 2155) (.n 3796)),
    .atom (.mul (.n 4013) (.n 2164) (.n 3807)),
    .atom (.add (.n 4014) (.n 4012) (.n 4013)),
    .atom (.mul (.n 4015) (.n 2173) (.n 3818)),
    .atom (.add (.n 4016) (.n 4014) (.n 4015)),
    .atom (.mul (.n 4017) (.n 2182) (.n 3842)),
    .atom (.add (.n 4018) (.n 4016) (.n 4017))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a3860, a3861, a3862, a3863, a3864, a3865, a3866, -⟩ := hs
  have v3796 : σ (.n 3796) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_eval h (k := 49) (by norm_num)).2.2
  have v3807 : σ (.n 3807) = ev 12 := by
    rw [← hev 12 (by norm_num)]; exact (vt_eval h (k := 50) (by norm_num)).2.2
  have v3818 : σ (.n 3818) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 51) (by norm_num)).2.2
  have v3842 : σ (.n 3842) = ev 14 := by
    rw [← hev 14 (by norm_num)]; exact (vt_eval h (k := 52) (by norm_num)).2.2
  rw [a3866, a3864, a3862, a3860, a3861, a3863, a3865, v3796, v3807, v3818, v3842]
  simp only [vtSideVal, vtBTerms23, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, vt_ofK_ofBits_one, zero_add,
    one_mul, mul_one, add_zero, add_assoc]

end
end LeanVM.Guest.B1.Tables
