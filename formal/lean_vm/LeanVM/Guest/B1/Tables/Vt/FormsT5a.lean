/-
  LeanVM.Guest.B1.Tables.Vt.FormsT5a

  Table 5's blocks' values on the push side, from the guest's statements.

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
theorem vtB05_0 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5282) = σ (.n 1049) * vtBlockVal (σ (.n 14)) W ev
      [[([], 1)], [([0], 2)], [([1], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4272 [
    .atom (.const (.n 4696) (word 1 0)),
    .atom (.const (.n 4697) (word 2 0)),
    .atom (.mul (.n 4698) (.n 4697) (.n 4032)),
    .atom (.copy (.n 4699) (.n 4698)),
    .atom (.copy (.n 4700) (.n 4036))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4272, a4273, a4274, a4275, a4276, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 4849 [
    .atom (.load (.n 5273) (.n 13) 0),
    .atom (.mul (.n 5274) (.n 5273) (.n 4696)),
    .atom (.load (.n 5275) (.n 13) 1),
    .atom (.mul (.n 5276) (.n 5275) (.n 4699)),
    .atom (.add (.n 5277) (.n 5274) (.n 5276)),
    .atom (.load (.n 5278) (.n 13) 2),
    .atom (.mul (.n 5279) (.n 5278) (.n 4700)),
    .atom (.add (.n 5280) (.n 5277) (.n 5279)),
    .atom (.add (.n 5281) (.n 14) (.n 5280)),
    .atom (.mul (.n 5282) (.n 1049) (.n 5281))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a4849, a4850, a4851, a4852, a4853, a4854, a4855, a4856, a4857, a4858, -⟩ := hs1
  have e4849 := tb_loadHolds_unique a4849 (hw 0 (by norm_num))
  have e4851 := tb_loadHolds_unique a4851 (hw 1 (by norm_num))
  have e4854 := tb_loadHolds_unique a4854 (hw 2 (by norm_num))
  have v4032 : σ (.n 4032) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_eval h (k := 61) (by norm_num)).2.2
  have v4036 : σ (.n 4036) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 62) (by norm_num)).2.2
  have hB : σ (.n 5281) = vtBlockVal (σ (.n 14)) W ev [[([], 1)], [([0], 2)], [([1], 1)]] := by
    simp only [v4036, v4032, a4857, a4856, a4855, e4854, a4853, a4852, e4851, a4850, e4849, a4276, a4275,
      a4274, a4273, a4272]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a4858, hB]

set_option maxRecDepth 10000 in
theorem vtB05_1 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5332) = σ (.n 5282) + σ (.n 1058) * vtBlockVal (σ (.n 14)) W ev
      [[([], 4)], [([0], 1)], [([91], 2)], [([], 32)], [([2], 1)], [([3], 1)], [([4], 1)], [([5], 1)], [([6], 1)], [([7], 1)], [([8], 1)], [([9], 1)], [([10], 1)], [([11], 1)], [([12], 1)], [([13], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4277 [
    .atom (.const (.n 4701) (word 4 0)),
    .atom (.copy (.n 4702) (.n 4032)),
    .atom (.const (.n 4703) (word 2 0)),
    .atom (.mul (.n 4704) (.n 4703) (.n 4695)),
    .atom (.copy (.n 4705) (.n 4704)),
    .atom (.const (.n 4706) (word 32 0)),
    .atom (.copy (.n 4707) (.n 4040)),
    .atom (.copy (.n 4708) (.n 4057)),
    .atom (.copy (.n 4709) (.n 4061)),
    .atom (.copy (.n 4710) (.n 4065)),
    .atom (.copy (.n 4711) (.n 4069)),
    .atom (.copy (.n 4712) (.n 4086)),
    .atom (.copy (.n 4713) (.n 4090)),
    .atom (.copy (.n 4714) (.n 4094)),
    .atom (.copy (.n 4715) (.n 4098)),
    .atom (.copy (.n 4716) (.n 4115)),
    .atom (.copy (.n 4717) (.n 4119)),
    .atom (.copy (.n 4718) (.n 4123))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4277, a4278, a4279, a4280, a4281, a4282, a4283, a4284, a4285, a4286, a4287, a4288, a4289, a4290,
    a4291, a4292, a4293, a4294, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 4859 [
    .atom (.load (.n 5283) (.n 13) 0),
    .atom (.mul (.n 5284) (.n 5283) (.n 4701)),
    .atom (.load (.n 5285) (.n 13) 1),
    .atom (.mul (.n 5286) (.n 5285) (.n 4702)),
    .atom (.add (.n 5287) (.n 5284) (.n 5286)),
    .atom (.load (.n 5288) (.n 13) 2),
    .atom (.mul (.n 5289) (.n 5288) (.n 4705)),
    .atom (.add (.n 5290) (.n 5287) (.n 5289)),
    .atom (.load (.n 5291) (.n 13) 3),
    .atom (.mul (.n 5292) (.n 5291) (.n 4706)),
    .atom (.add (.n 5293) (.n 5290) (.n 5292)),
    .atom (.load (.n 5294) (.n 13) 4),
    .atom (.mul (.n 5295) (.n 5294) (.n 4707)),
    .atom (.add (.n 5296) (.n 5293) (.n 5295)),
    .atom (.load (.n 5297) (.n 13) 5),
    .atom (.mul (.n 5298) (.n 5297) (.n 4708)),
    .atom (.add (.n 5299) (.n 5296) (.n 5298)),
    .atom (.load (.n 5300) (.n 13) 6),
    .atom (.mul (.n 5301) (.n 5300) (.n 4709)),
    .atom (.add (.n 5302) (.n 5299) (.n 5301)),
    .atom (.load (.n 5303) (.n 13) 7),
    .atom (.mul (.n 5304) (.n 5303) (.n 4710)),
    .atom (.add (.n 5305) (.n 5302) (.n 5304)),
    .atom (.load (.n 5306) (.n 13) 8),
    .atom (.mul (.n 5307) (.n 5306) (.n 4711)),
    .atom (.add (.n 5308) (.n 5305) (.n 5307)),
    .atom (.load (.n 5309) (.n 13) 9),
    .atom (.mul (.n 5310) (.n 5309) (.n 4712)),
    .atom (.add (.n 5311) (.n 5308) (.n 5310)),
    .atom (.load (.n 5312) (.n 13) 10),
    .atom (.mul (.n 5313) (.n 5312) (.n 4713)),
    .atom (.add (.n 5314) (.n 5311) (.n 5313)),
    .atom (.load (.n 5315) (.n 13) 11),
    .atom (.mul (.n 5316) (.n 5315) (.n 4714)),
    .atom (.add (.n 5317) (.n 5314) (.n 5316)),
    .atom (.load (.n 5318) (.n 13) 12),
    .atom (.mul (.n 5319) (.n 5318) (.n 4715)),
    .atom (.add (.n 5320) (.n 5317) (.n 5319)),
    .atom (.load (.n 5321) (.n 13) 13),
    .atom (.mul (.n 5322) (.n 5321) (.n 4716)),
    .atom (.add (.n 5323) (.n 5320) (.n 5322)),
    .atom (.load (.n 5324) (.n 13) 14),
    .atom (.mul (.n 5325) (.n 5324) (.n 4717)),
    .atom (.add (.n 5326) (.n 5323) (.n 5325)),
    .atom (.load (.n 5327) (.n 13) 15),
    .atom (.mul (.n 5328) (.n 5327) (.n 4718)),
    .atom (.add (.n 5329) (.n 5326) (.n 5328)),
    .atom (.add (.n 5330) (.n 14) (.n 5329)),
    .atom (.mul (.n 5331) (.n 1058) (.n 5330)),
    .atom (.add (.n 5332) (.n 5282) (.n 5331))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a4859, a4860, a4861, a4862, a4863, a4864, a4865, a4866, a4867, a4868, a4869, a4870, a4871, a4872,
    a4873, a4874, a4875, a4876, a4877, a4878, a4879, a4880, a4881, a4882, a4883, a4884, a4885,
    a4886, a4887, a4888, a4889, a4890, a4891, a4892, a4893, a4894, a4895, a4896, a4897, a4898,
    a4899, a4900, a4901, a4902, a4903, a4904, a4905, a4906, a4907, a4908, -⟩ := hs1
  have e4859 := tb_loadHolds_unique a4859 (hw 0 (by norm_num))
  have e4861 := tb_loadHolds_unique a4861 (hw 1 (by norm_num))
  have e4864 := tb_loadHolds_unique a4864 (hw 2 (by norm_num))
  have e4867 := tb_loadHolds_unique a4867 (hw 3 (by norm_num))
  have e4870 := tb_loadHolds_unique a4870 (hw 4 (by norm_num))
  have e4873 := tb_loadHolds_unique a4873 (hw 5 (by norm_num))
  have e4876 := tb_loadHolds_unique a4876 (hw 6 (by norm_num))
  have e4879 := tb_loadHolds_unique a4879 (hw 7 (by norm_num))
  have e4882 := tb_loadHolds_unique a4882 (hw 8 (by norm_num))
  have e4885 := tb_loadHolds_unique a4885 (hw 9 (by norm_num))
  have e4888 := tb_loadHolds_unique a4888 (hw 10 (by norm_num))
  have e4891 := tb_loadHolds_unique a4891 (hw 11 (by norm_num))
  have e4894 := tb_loadHolds_unique a4894 (hw 12 (by norm_num))
  have e4897 := tb_loadHolds_unique a4897 (hw 13 (by norm_num))
  have e4900 := tb_loadHolds_unique a4900 (hw 14 (by norm_num))
  have e4903 := tb_loadHolds_unique a4903 (hw 15 (by norm_num))
  have v4032 : σ (.n 4032) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_eval h (k := 61) (by norm_num)).2.2
  have v4040 : σ (.n 4040) = ev 2 := by
    rw [← hev 2 (by norm_num)]; exact (vt_eval h (k := 63) (by norm_num)).2.2
  have v4057 : σ (.n 4057) = ev 3 := by
    rw [← hev 3 (by norm_num)]; exact (vt_eval h (k := 64) (by norm_num)).2.2
  have v4061 : σ (.n 4061) = ev 4 := by
    rw [← hev 4 (by norm_num)]; exact (vt_eval h (k := 65) (by norm_num)).2.2
  have v4065 : σ (.n 4065) = ev 5 := by
    rw [← hev 5 (by norm_num)]; exact (vt_eval h (k := 66) (by norm_num)).2.2
  have v4069 : σ (.n 4069) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_eval h (k := 67) (by norm_num)).2.2
  have v4086 : σ (.n 4086) = ev 7 := by
    rw [← hev 7 (by norm_num)]; exact (vt_eval h (k := 68) (by norm_num)).2.2
  have v4090 : σ (.n 4090) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_eval h (k := 69) (by norm_num)).2.2
  have v4094 : σ (.n 4094) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 70) (by norm_num)).2.2
  have v4098 : σ (.n 4098) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_eval h (k := 71) (by norm_num)).2.2
  have v4115 : σ (.n 4115) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_eval h (k := 72) (by norm_num)).2.2
  have v4119 : σ (.n 4119) = ev 12 := by
    rw [← hev 12 (by norm_num)]; exact (vt_eval h (k := 73) (by norm_num)).2.2
  have v4123 : σ (.n 4123) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 74) (by norm_num)).2.2
  have v4695 : σ (.n 4695) = ev 91 := by
    rw [← hev 91 (by norm_num)]; exact (vt_eval h (k := 152) (by norm_num)).2.2
  have hB : σ (.n 5330) = vtBlockVal (σ (.n 14)) W ev [[([], 4)], [([0], 1)], [([91], 2)], [([], 32)], [([2], 1)], [([3], 1)], [([4], 1)], [([5], 1)], [([6], 1)], [([7], 1)], [([8], 1)], [([9], 1)], [([10], 1)], [([11], 1)], [([12], 1)], [([13], 1)]] := by
    simp only [v4695, v4123, v4119, v4115, v4098, v4094, v4090, v4086, v4069, v4065, v4061, v4057, v4040,
      v4032, a4906, a4905, a4904, e4903, a4902, a4901, e4900, a4899, a4898, e4897, a4896,
      a4895, e4894, a4893, a4892, e4891, a4890, a4889, e4888, a4887, a4886, e4885, a4884,
      a4883, e4882, a4881, a4880, e4879, a4878, a4877, e4876, a4875, a4874, e4873, a4872,
      a4871, e4870, a4869, a4868, e4867, a4866, a4865, e4864, a4863, a4862, e4861, a4860,
      e4859, a4294, a4293, a4292, a4291, a4290, a4289, a4288, a4287, a4286, a4285, a4284,
      a4283, a4282, a4281, a4280, a4279, a4278, a4277]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a4908, a4907, hB]

set_option maxRecDepth 10000 in
theorem vtB05_2 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5349) = σ (.n 5332) + σ (.n 1067) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 2], 1)], [([65], 2)], [([15], 1), ([10, 15], 1), ([10, 14], 1)], [([16], 1), ([10, 16], 1), ([10, 15], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4295 [
    .atom (.const (.n 4719) (word 2 0)),
    .atom (.mul (.n 4720) (.n 4036) (.n 4040)),
    .atom (.copy (.n 4721) (.n 4720)),
    .atom (.const (.n 4722) (word 2 0)),
    .atom (.mul (.n 4723) (.n 4722) (.n 4500)),
    .atom (.copy (.n 4724) (.n 4723)),
    .atom (.mul (.n 4725) (.n 4098) (.n 4144)),
    .atom (.add (.n 4726) (.n 4144) (.n 4725)),
    .atom (.mul (.n 4727) (.n 4098) (.n 4127)),
    .atom (.add (.n 4728) (.n 4726) (.n 4727)),
    .atom (.copy (.n 4729) (.n 4728)),
    .atom (.mul (.n 4730) (.n 4098) (.n 4148)),
    .atom (.add (.n 4731) (.n 4148) (.n 4730)),
    .atom (.mul (.n 4732) (.n 4098) (.n 4144)),
    .atom (.add (.n 4733) (.n 4731) (.n 4732)),
    .atom (.copy (.n 4734) (.n 4733))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4295, a4296, a4297, a4298, a4299, a4300, a4301, a4302, a4303, a4304, a4305, a4306, a4307, a4308,
    a4309, a4310, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 4909 [
    .atom (.load (.n 5333) (.n 13) 0),
    .atom (.mul (.n 5334) (.n 5333) (.n 4719)),
    .atom (.load (.n 5335) (.n 13) 1),
    .atom (.mul (.n 5336) (.n 5335) (.n 4721)),
    .atom (.add (.n 5337) (.n 5334) (.n 5336)),
    .atom (.load (.n 5338) (.n 13) 2),
    .atom (.mul (.n 5339) (.n 5338) (.n 4724)),
    .atom (.add (.n 5340) (.n 5337) (.n 5339)),
    .atom (.load (.n 5341) (.n 13) 3),
    .atom (.mul (.n 5342) (.n 5341) (.n 4729)),
    .atom (.add (.n 5343) (.n 5340) (.n 5342)),
    .atom (.load (.n 5344) (.n 13) 4),
    .atom (.mul (.n 5345) (.n 5344) (.n 4734)),
    .atom (.add (.n 5346) (.n 5343) (.n 5345)),
    .atom (.add (.n 5347) (.n 14) (.n 5346)),
    .atom (.mul (.n 5348) (.n 1067) (.n 5347)),
    .atom (.add (.n 5349) (.n 5332) (.n 5348))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a4909, a4910, a4911, a4912, a4913, a4914, a4915, a4916, a4917, a4918, a4919, a4920, a4921, a4922,
    a4923, a4924, a4925, -⟩ := hs1
  have e4909 := tb_loadHolds_unique a4909 (hw 0 (by norm_num))
  have e4911 := tb_loadHolds_unique a4911 (hw 1 (by norm_num))
  have e4914 := tb_loadHolds_unique a4914 (hw 2 (by norm_num))
  have e4917 := tb_loadHolds_unique a4917 (hw 3 (by norm_num))
  have e4920 := tb_loadHolds_unique a4920 (hw 4 (by norm_num))
  have v4036 : σ (.n 4036) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 62) (by norm_num)).2.2
  have v4040 : σ (.n 4040) = ev 2 := by
    rw [← hev 2 (by norm_num)]; exact (vt_eval h (k := 63) (by norm_num)).2.2
  have v4098 : σ (.n 4098) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_eval h (k := 71) (by norm_num)).2.2
  have v4127 : σ (.n 4127) = ev 14 := by
    rw [← hev 14 (by norm_num)]; exact (vt_eval h (k := 75) (by norm_num)).2.2
  have v4144 : σ (.n 4144) = ev 15 := by
    rw [← hev 15 (by norm_num)]; exact (vt_eval h (k := 76) (by norm_num)).2.2
  have v4148 : σ (.n 4148) = ev 16 := by
    rw [← hev 16 (by norm_num)]; exact (vt_eval h (k := 77) (by norm_num)).2.2
  have v4500 : σ (.n 4500) = ev 65 := by
    rw [← hev 65 (by norm_num)]; exact (vt_eval h (k := 126) (by norm_num)).2.2
  have hB : σ (.n 5347) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 2], 1)], [([65], 2)], [([15], 1), ([10, 15], 1), ([10, 14], 1)], [([16], 1), ([10, 16], 1), ([10, 15], 1)]] := by
    simp only [v4500, v4148, v4144, v4127, v4098, v4040, v4036, a4923, a4922, a4921, e4920, a4919, a4918,
      e4917, a4916, a4915, e4914, a4913, a4912, e4911, a4910, e4909, a4310, a4309, a4308,
      a4307, a4306, a4305, a4304, a4303, a4302, a4301, a4300, a4299, a4298, a4297, a4296,
      a4295]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a4925, a4924, hB]

set_option maxRecDepth 10000 in
theorem vtB05_3 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5366) = σ (.n 5349) + σ (.n 1076) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 3], 1)], [([66], 2)], [([17], 1), ([10, 17], 1), ([10, 16], 1)], [([18], 1), ([10, 18], 1), ([10, 17], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4311 [
    .atom (.const (.n 4735) (word 2 0)),
    .atom (.mul (.n 4736) (.n 4036) (.n 4057)),
    .atom (.copy (.n 4737) (.n 4736)),
    .atom (.const (.n 4738) (word 2 0)),
    .atom (.mul (.n 4739) (.n 4738) (.n 4504)),
    .atom (.copy (.n 4740) (.n 4739)),
    .atom (.mul (.n 4741) (.n 4098) (.n 4152)),
    .atom (.add (.n 4742) (.n 4152) (.n 4741)),
    .atom (.mul (.n 4743) (.n 4098) (.n 4148)),
    .atom (.add (.n 4744) (.n 4742) (.n 4743)),
    .atom (.copy (.n 4745) (.n 4744)),
    .atom (.mul (.n 4746) (.n 4098) (.n 4156)),
    .atom (.add (.n 4747) (.n 4156) (.n 4746)),
    .atom (.mul (.n 4748) (.n 4098) (.n 4152)),
    .atom (.add (.n 4749) (.n 4747) (.n 4748)),
    .atom (.copy (.n 4750) (.n 4749))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4311, a4312, a4313, a4314, a4315, a4316, a4317, a4318, a4319, a4320, a4321, a4322, a4323, a4324,
    a4325, a4326, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 4926 [
    .atom (.load (.n 5350) (.n 13) 0),
    .atom (.mul (.n 5351) (.n 5350) (.n 4735)),
    .atom (.load (.n 5352) (.n 13) 1),
    .atom (.mul (.n 5353) (.n 5352) (.n 4737)),
    .atom (.add (.n 5354) (.n 5351) (.n 5353)),
    .atom (.load (.n 5355) (.n 13) 2),
    .atom (.mul (.n 5356) (.n 5355) (.n 4740)),
    .atom (.add (.n 5357) (.n 5354) (.n 5356)),
    .atom (.load (.n 5358) (.n 13) 3),
    .atom (.mul (.n 5359) (.n 5358) (.n 4745)),
    .atom (.add (.n 5360) (.n 5357) (.n 5359)),
    .atom (.load (.n 5361) (.n 13) 4),
    .atom (.mul (.n 5362) (.n 5361) (.n 4750)),
    .atom (.add (.n 5363) (.n 5360) (.n 5362)),
    .atom (.add (.n 5364) (.n 14) (.n 5363)),
    .atom (.mul (.n 5365) (.n 1076) (.n 5364)),
    .atom (.add (.n 5366) (.n 5349) (.n 5365))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a4926, a4927, a4928, a4929, a4930, a4931, a4932, a4933, a4934, a4935, a4936, a4937, a4938, a4939,
    a4940, a4941, a4942, -⟩ := hs1
  have e4926 := tb_loadHolds_unique a4926 (hw 0 (by norm_num))
  have e4928 := tb_loadHolds_unique a4928 (hw 1 (by norm_num))
  have e4931 := tb_loadHolds_unique a4931 (hw 2 (by norm_num))
  have e4934 := tb_loadHolds_unique a4934 (hw 3 (by norm_num))
  have e4937 := tb_loadHolds_unique a4937 (hw 4 (by norm_num))
  have v4036 : σ (.n 4036) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 62) (by norm_num)).2.2
  have v4057 : σ (.n 4057) = ev 3 := by
    rw [← hev 3 (by norm_num)]; exact (vt_eval h (k := 64) (by norm_num)).2.2
  have v4098 : σ (.n 4098) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_eval h (k := 71) (by norm_num)).2.2
  have v4148 : σ (.n 4148) = ev 16 := by
    rw [← hev 16 (by norm_num)]; exact (vt_eval h (k := 77) (by norm_num)).2.2
  have v4152 : σ (.n 4152) = ev 17 := by
    rw [← hev 17 (by norm_num)]; exact (vt_eval h (k := 78) (by norm_num)).2.2
  have v4156 : σ (.n 4156) = ev 18 := by
    rw [← hev 18 (by norm_num)]; exact (vt_eval h (k := 79) (by norm_num)).2.2
  have v4504 : σ (.n 4504) = ev 66 := by
    rw [← hev 66 (by norm_num)]; exact (vt_eval h (k := 127) (by norm_num)).2.2
  have hB : σ (.n 5364) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 3], 1)], [([66], 2)], [([17], 1), ([10, 17], 1), ([10, 16], 1)], [([18], 1), ([10, 18], 1), ([10, 17], 1)]] := by
    simp only [v4504, v4156, v4152, v4148, v4098, v4057, v4036, a4940, a4939, a4938, e4937, a4936, a4935,
      e4934, a4933, a4932, e4931, a4930, a4929, e4928, a4927, e4926, a4326, a4325, a4324,
      a4323, a4322, a4321, a4320, a4319, a4318, a4317, a4316, a4315, a4314, a4313, a4312,
      a4311]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a4942, a4941, hB]

set_option maxRecDepth 10000 in
theorem vtB05_4 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5383) = σ (.n 5366) + σ (.n 1085) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 4], 1)], [([67], 2)], [([19], 1), ([10, 19], 1), ([10, 18], 1)], [([20], 1), ([10, 20], 1), ([10, 19], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4327 [
    .atom (.const (.n 4751) (word 2 0)),
    .atom (.mul (.n 4752) (.n 4036) (.n 4061)),
    .atom (.copy (.n 4753) (.n 4752)),
    .atom (.const (.n 4754) (word 2 0)),
    .atom (.mul (.n 4755) (.n 4754) (.n 4521)),
    .atom (.copy (.n 4756) (.n 4755)),
    .atom (.mul (.n 4757) (.n 4098) (.n 4173)),
    .atom (.add (.n 4758) (.n 4173) (.n 4757)),
    .atom (.mul (.n 4759) (.n 4098) (.n 4156)),
    .atom (.add (.n 4760) (.n 4758) (.n 4759)),
    .atom (.copy (.n 4761) (.n 4760)),
    .atom (.mul (.n 4762) (.n 4098) (.n 4177)),
    .atom (.add (.n 4763) (.n 4177) (.n 4762)),
    .atom (.mul (.n 4764) (.n 4098) (.n 4173)),
    .atom (.add (.n 4765) (.n 4763) (.n 4764)),
    .atom (.copy (.n 4766) (.n 4765))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4327, a4328, a4329, a4330, a4331, a4332, a4333, a4334, a4335, a4336, a4337, a4338, a4339, a4340,
    a4341, a4342, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 4943 [
    .atom (.load (.n 5367) (.n 13) 0),
    .atom (.mul (.n 5368) (.n 5367) (.n 4751)),
    .atom (.load (.n 5369) (.n 13) 1),
    .atom (.mul (.n 5370) (.n 5369) (.n 4753)),
    .atom (.add (.n 5371) (.n 5368) (.n 5370)),
    .atom (.load (.n 5372) (.n 13) 2),
    .atom (.mul (.n 5373) (.n 5372) (.n 4756)),
    .atom (.add (.n 5374) (.n 5371) (.n 5373)),
    .atom (.load (.n 5375) (.n 13) 3),
    .atom (.mul (.n 5376) (.n 5375) (.n 4761)),
    .atom (.add (.n 5377) (.n 5374) (.n 5376)),
    .atom (.load (.n 5378) (.n 13) 4),
    .atom (.mul (.n 5379) (.n 5378) (.n 4766)),
    .atom (.add (.n 5380) (.n 5377) (.n 5379)),
    .atom (.add (.n 5381) (.n 14) (.n 5380)),
    .atom (.mul (.n 5382) (.n 1085) (.n 5381)),
    .atom (.add (.n 5383) (.n 5366) (.n 5382))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a4943, a4944, a4945, a4946, a4947, a4948, a4949, a4950, a4951, a4952, a4953, a4954, a4955, a4956,
    a4957, a4958, a4959, -⟩ := hs1
  have e4943 := tb_loadHolds_unique a4943 (hw 0 (by norm_num))
  have e4945 := tb_loadHolds_unique a4945 (hw 1 (by norm_num))
  have e4948 := tb_loadHolds_unique a4948 (hw 2 (by norm_num))
  have e4951 := tb_loadHolds_unique a4951 (hw 3 (by norm_num))
  have e4954 := tb_loadHolds_unique a4954 (hw 4 (by norm_num))
  have v4036 : σ (.n 4036) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 62) (by norm_num)).2.2
  have v4061 : σ (.n 4061) = ev 4 := by
    rw [← hev 4 (by norm_num)]; exact (vt_eval h (k := 65) (by norm_num)).2.2
  have v4098 : σ (.n 4098) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_eval h (k := 71) (by norm_num)).2.2
  have v4156 : σ (.n 4156) = ev 18 := by
    rw [← hev 18 (by norm_num)]; exact (vt_eval h (k := 79) (by norm_num)).2.2
  have v4173 : σ (.n 4173) = ev 19 := by
    rw [← hev 19 (by norm_num)]; exact (vt_eval h (k := 80) (by norm_num)).2.2
  have v4177 : σ (.n 4177) = ev 20 := by
    rw [← hev 20 (by norm_num)]; exact (vt_eval h (k := 81) (by norm_num)).2.2
  have v4521 : σ (.n 4521) = ev 67 := by
    rw [← hev 67 (by norm_num)]; exact (vt_eval h (k := 128) (by norm_num)).2.2
  have hB : σ (.n 5381) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 4], 1)], [([67], 2)], [([19], 1), ([10, 19], 1), ([10, 18], 1)], [([20], 1), ([10, 20], 1), ([10, 19], 1)]] := by
    simp only [v4521, v4177, v4173, v4156, v4098, v4061, v4036, a4957, a4956, a4955, e4954, a4953, a4952,
      e4951, a4950, a4949, e4948, a4947, a4946, e4945, a4944, e4943, a4342, a4341, a4340,
      a4339, a4338, a4337, a4336, a4335, a4334, a4333, a4332, a4331, a4330, a4329, a4328,
      a4327]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a4959, a4958, hB]

set_option maxRecDepth 10000 in
theorem vtB05_5 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5400) = σ (.n 5383) + σ (.n 1094) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 5], 1)], [([68], 2)], [([21], 1), ([10, 21], 1), ([10, 20], 1)], [([22], 1), ([10, 22], 1), ([10, 21], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4343 [
    .atom (.const (.n 4767) (word 2 0)),
    .atom (.mul (.n 4768) (.n 4036) (.n 4065)),
    .atom (.copy (.n 4769) (.n 4768)),
    .atom (.const (.n 4770) (word 2 0)),
    .atom (.mul (.n 4771) (.n 4770) (.n 4525)),
    .atom (.copy (.n 4772) (.n 4771)),
    .atom (.mul (.n 4773) (.n 4098) (.n 4181)),
    .atom (.add (.n 4774) (.n 4181) (.n 4773)),
    .atom (.mul (.n 4775) (.n 4098) (.n 4177)),
    .atom (.add (.n 4776) (.n 4774) (.n 4775)),
    .atom (.copy (.n 4777) (.n 4776)),
    .atom (.mul (.n 4778) (.n 4098) (.n 4185)),
    .atom (.add (.n 4779) (.n 4185) (.n 4778)),
    .atom (.mul (.n 4780) (.n 4098) (.n 4181)),
    .atom (.add (.n 4781) (.n 4779) (.n 4780)),
    .atom (.copy (.n 4782) (.n 4781))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4343, a4344, a4345, a4346, a4347, a4348, a4349, a4350, a4351, a4352, a4353, a4354, a4355, a4356,
    a4357, a4358, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 4960 [
    .atom (.load (.n 5384) (.n 13) 0),
    .atom (.mul (.n 5385) (.n 5384) (.n 4767)),
    .atom (.load (.n 5386) (.n 13) 1),
    .atom (.mul (.n 5387) (.n 5386) (.n 4769)),
    .atom (.add (.n 5388) (.n 5385) (.n 5387)),
    .atom (.load (.n 5389) (.n 13) 2),
    .atom (.mul (.n 5390) (.n 5389) (.n 4772)),
    .atom (.add (.n 5391) (.n 5388) (.n 5390)),
    .atom (.load (.n 5392) (.n 13) 3),
    .atom (.mul (.n 5393) (.n 5392) (.n 4777)),
    .atom (.add (.n 5394) (.n 5391) (.n 5393)),
    .atom (.load (.n 5395) (.n 13) 4),
    .atom (.mul (.n 5396) (.n 5395) (.n 4782)),
    .atom (.add (.n 5397) (.n 5394) (.n 5396)),
    .atom (.add (.n 5398) (.n 14) (.n 5397)),
    .atom (.mul (.n 5399) (.n 1094) (.n 5398)),
    .atom (.add (.n 5400) (.n 5383) (.n 5399))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a4960, a4961, a4962, a4963, a4964, a4965, a4966, a4967, a4968, a4969, a4970, a4971, a4972, a4973,
    a4974, a4975, a4976, -⟩ := hs1
  have e4960 := tb_loadHolds_unique a4960 (hw 0 (by norm_num))
  have e4962 := tb_loadHolds_unique a4962 (hw 1 (by norm_num))
  have e4965 := tb_loadHolds_unique a4965 (hw 2 (by norm_num))
  have e4968 := tb_loadHolds_unique a4968 (hw 3 (by norm_num))
  have e4971 := tb_loadHolds_unique a4971 (hw 4 (by norm_num))
  have v4036 : σ (.n 4036) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 62) (by norm_num)).2.2
  have v4065 : σ (.n 4065) = ev 5 := by
    rw [← hev 5 (by norm_num)]; exact (vt_eval h (k := 66) (by norm_num)).2.2
  have v4098 : σ (.n 4098) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_eval h (k := 71) (by norm_num)).2.2
  have v4177 : σ (.n 4177) = ev 20 := by
    rw [← hev 20 (by norm_num)]; exact (vt_eval h (k := 81) (by norm_num)).2.2
  have v4181 : σ (.n 4181) = ev 21 := by
    rw [← hev 21 (by norm_num)]; exact (vt_eval h (k := 82) (by norm_num)).2.2
  have v4185 : σ (.n 4185) = ev 22 := by
    rw [← hev 22 (by norm_num)]; exact (vt_eval h (k := 83) (by norm_num)).2.2
  have v4525 : σ (.n 4525) = ev 68 := by
    rw [← hev 68 (by norm_num)]; exact (vt_eval h (k := 129) (by norm_num)).2.2
  have hB : σ (.n 5398) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 5], 1)], [([68], 2)], [([21], 1), ([10, 21], 1), ([10, 20], 1)], [([22], 1), ([10, 22], 1), ([10, 21], 1)]] := by
    simp only [v4525, v4185, v4181, v4177, v4098, v4065, v4036, a4974, a4973, a4972, e4971, a4970, a4969,
      e4968, a4967, a4966, e4965, a4964, a4963, e4962, a4961, e4960, a4358, a4357, a4356,
      a4355, a4354, a4353, a4352, a4351, a4350, a4349, a4348, a4347, a4346, a4345, a4344,
      a4343]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a4976, a4975, hB]

set_option maxRecDepth 10000 in
theorem vtB05_6 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5417) = σ (.n 5400) + σ (.n 1103) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 6], 1)], [([69], 2)], [([23], 1), ([10, 23], 1), ([10, 22], 1)], [([24], 1), ([10, 24], 1), ([10, 23], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4359 [
    .atom (.const (.n 4783) (word 2 0)),
    .atom (.mul (.n 4784) (.n 4036) (.n 4069)),
    .atom (.copy (.n 4785) (.n 4784)),
    .atom (.const (.n 4786) (word 2 0)),
    .atom (.mul (.n 4787) (.n 4786) (.n 4529)),
    .atom (.copy (.n 4788) (.n 4787)),
    .atom (.mul (.n 4789) (.n 4098) (.n 4202)),
    .atom (.add (.n 4790) (.n 4202) (.n 4789)),
    .atom (.mul (.n 4791) (.n 4098) (.n 4185)),
    .atom (.add (.n 4792) (.n 4790) (.n 4791)),
    .atom (.copy (.n 4793) (.n 4792)),
    .atom (.mul (.n 4794) (.n 4098) (.n 4206)),
    .atom (.add (.n 4795) (.n 4206) (.n 4794)),
    .atom (.mul (.n 4796) (.n 4098) (.n 4202)),
    .atom (.add (.n 4797) (.n 4795) (.n 4796)),
    .atom (.copy (.n 4798) (.n 4797))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4359, a4360, a4361, a4362, a4363, a4364, a4365, a4366, a4367, a4368, a4369, a4370, a4371, a4372,
    a4373, a4374, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 4977 [
    .atom (.load (.n 5401) (.n 13) 0),
    .atom (.mul (.n 5402) (.n 5401) (.n 4783)),
    .atom (.load (.n 5403) (.n 13) 1),
    .atom (.mul (.n 5404) (.n 5403) (.n 4785)),
    .atom (.add (.n 5405) (.n 5402) (.n 5404)),
    .atom (.load (.n 5406) (.n 13) 2),
    .atom (.mul (.n 5407) (.n 5406) (.n 4788)),
    .atom (.add (.n 5408) (.n 5405) (.n 5407)),
    .atom (.load (.n 5409) (.n 13) 3),
    .atom (.mul (.n 5410) (.n 5409) (.n 4793)),
    .atom (.add (.n 5411) (.n 5408) (.n 5410)),
    .atom (.load (.n 5412) (.n 13) 4),
    .atom (.mul (.n 5413) (.n 5412) (.n 4798)),
    .atom (.add (.n 5414) (.n 5411) (.n 5413)),
    .atom (.add (.n 5415) (.n 14) (.n 5414)),
    .atom (.mul (.n 5416) (.n 1103) (.n 5415)),
    .atom (.add (.n 5417) (.n 5400) (.n 5416))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a4977, a4978, a4979, a4980, a4981, a4982, a4983, a4984, a4985, a4986, a4987, a4988, a4989, a4990,
    a4991, a4992, a4993, -⟩ := hs1
  have e4977 := tb_loadHolds_unique a4977 (hw 0 (by norm_num))
  have e4979 := tb_loadHolds_unique a4979 (hw 1 (by norm_num))
  have e4982 := tb_loadHolds_unique a4982 (hw 2 (by norm_num))
  have e4985 := tb_loadHolds_unique a4985 (hw 3 (by norm_num))
  have e4988 := tb_loadHolds_unique a4988 (hw 4 (by norm_num))
  have v4036 : σ (.n 4036) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 62) (by norm_num)).2.2
  have v4069 : σ (.n 4069) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_eval h (k := 67) (by norm_num)).2.2
  have v4098 : σ (.n 4098) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_eval h (k := 71) (by norm_num)).2.2
  have v4185 : σ (.n 4185) = ev 22 := by
    rw [← hev 22 (by norm_num)]; exact (vt_eval h (k := 83) (by norm_num)).2.2
  have v4202 : σ (.n 4202) = ev 23 := by
    rw [← hev 23 (by norm_num)]; exact (vt_eval h (k := 84) (by norm_num)).2.2
  have v4206 : σ (.n 4206) = ev 24 := by
    rw [← hev 24 (by norm_num)]; exact (vt_eval h (k := 85) (by norm_num)).2.2
  have v4529 : σ (.n 4529) = ev 69 := by
    rw [← hev 69 (by norm_num)]; exact (vt_eval h (k := 130) (by norm_num)).2.2
  have hB : σ (.n 5415) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 6], 1)], [([69], 2)], [([23], 1), ([10, 23], 1), ([10, 22], 1)], [([24], 1), ([10, 24], 1), ([10, 23], 1)]] := by
    simp only [v4529, v4206, v4202, v4185, v4098, v4069, v4036, a4991, a4990, a4989, e4988, a4987, a4986,
      e4985, a4984, a4983, e4982, a4981, a4980, e4979, a4978, e4977, a4374, a4373, a4372,
      a4371, a4370, a4369, a4368, a4367, a4366, a4365, a4364, a4363, a4362, a4361, a4360,
      a4359]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a4993, a4992, hB]

set_option maxRecDepth 10000 in
theorem vtB05_7 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5434) = σ (.n 5417) + σ (.n 1112) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 6], 2)], [([70], 2)], [([25], 1), ([10, 25], 1), ([10, 24], 1)], [([26], 1), ([10, 26], 1), ([10, 25], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4375 [
    .atom (.const (.n 4799) (word 2 0)),
    .atom (.const (.n 4800) (word 2 0)),
    .atom (.mul (.n 4801) (.n 4036) (.n 4069)),
    .atom (.mul (.n 4802) (.n 4800) (.n 4801)),
    .atom (.copy (.n 4803) (.n 4802)),
    .atom (.const (.n 4804) (word 2 0)),
    .atom (.mul (.n 4805) (.n 4804) (.n 4533)),
    .atom (.copy (.n 4806) (.n 4805)),
    .atom (.mul (.n 4807) (.n 4098) (.n 4210)),
    .atom (.add (.n 4808) (.n 4210) (.n 4807)),
    .atom (.mul (.n 4809) (.n 4098) (.n 4206)),
    .atom (.add (.n 4810) (.n 4808) (.n 4809)),
    .atom (.copy (.n 4811) (.n 4810)),
    .atom (.mul (.n 4812) (.n 4098) (.n 4214)),
    .atom (.add (.n 4813) (.n 4214) (.n 4812)),
    .atom (.mul (.n 4814) (.n 4098) (.n 4210)),
    .atom (.add (.n 4815) (.n 4813) (.n 4814)),
    .atom (.copy (.n 4816) (.n 4815))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4375, a4376, a4377, a4378, a4379, a4380, a4381, a4382, a4383, a4384, a4385, a4386, a4387, a4388,
    a4389, a4390, a4391, a4392, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 4994 [
    .atom (.load (.n 5418) (.n 13) 0),
    .atom (.mul (.n 5419) (.n 5418) (.n 4799)),
    .atom (.load (.n 5420) (.n 13) 1),
    .atom (.mul (.n 5421) (.n 5420) (.n 4803)),
    .atom (.add (.n 5422) (.n 5419) (.n 5421)),
    .atom (.load (.n 5423) (.n 13) 2),
    .atom (.mul (.n 5424) (.n 5423) (.n 4806)),
    .atom (.add (.n 5425) (.n 5422) (.n 5424)),
    .atom (.load (.n 5426) (.n 13) 3),
    .atom (.mul (.n 5427) (.n 5426) (.n 4811)),
    .atom (.add (.n 5428) (.n 5425) (.n 5427)),
    .atom (.load (.n 5429) (.n 13) 4),
    .atom (.mul (.n 5430) (.n 5429) (.n 4816)),
    .atom (.add (.n 5431) (.n 5428) (.n 5430)),
    .atom (.add (.n 5432) (.n 14) (.n 5431)),
    .atom (.mul (.n 5433) (.n 1112) (.n 5432)),
    .atom (.add (.n 5434) (.n 5417) (.n 5433))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a4994, a4995, a4996, a4997, a4998, a4999, a5000, a5001, a5002, a5003, a5004, a5005, a5006, a5007,
    a5008, a5009, a5010, -⟩ := hs1
  have e4994 := tb_loadHolds_unique a4994 (hw 0 (by norm_num))
  have e4996 := tb_loadHolds_unique a4996 (hw 1 (by norm_num))
  have e4999 := tb_loadHolds_unique a4999 (hw 2 (by norm_num))
  have e5002 := tb_loadHolds_unique a5002 (hw 3 (by norm_num))
  have e5005 := tb_loadHolds_unique a5005 (hw 4 (by norm_num))
  have v4036 : σ (.n 4036) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 62) (by norm_num)).2.2
  have v4069 : σ (.n 4069) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_eval h (k := 67) (by norm_num)).2.2
  have v4098 : σ (.n 4098) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_eval h (k := 71) (by norm_num)).2.2
  have v4206 : σ (.n 4206) = ev 24 := by
    rw [← hev 24 (by norm_num)]; exact (vt_eval h (k := 85) (by norm_num)).2.2
  have v4210 : σ (.n 4210) = ev 25 := by
    rw [← hev 25 (by norm_num)]; exact (vt_eval h (k := 86) (by norm_num)).2.2
  have v4214 : σ (.n 4214) = ev 26 := by
    rw [← hev 26 (by norm_num)]; exact (vt_eval h (k := 87) (by norm_num)).2.2
  have v4533 : σ (.n 4533) = ev 70 := by
    rw [← hev 70 (by norm_num)]; exact (vt_eval h (k := 131) (by norm_num)).2.2
  have hB : σ (.n 5432) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 6], 2)], [([70], 2)], [([25], 1), ([10, 25], 1), ([10, 24], 1)], [([26], 1), ([10, 26], 1), ([10, 25], 1)]] := by
    simp only [v4533, v4214, v4210, v4206, v4098, v4069, v4036, a5008, a5007, a5006, e5005, a5004, a5003,
      e5002, a5001, a5000, e4999, a4998, a4997, e4996, a4995, e4994, a4392, a4391, a4390,
      a4389, a4388, a4387, a4386, a4385, a4384, a4383, a4382, a4381, a4380, a4379, a4378,
      a4377, a4376, a4375]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5010, a5009, hB]

set_option maxRecDepth 10000 in
theorem vtB05_8 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5451) = σ (.n 5434) + σ (.n 1121) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 6], 4)], [([71], 2)], [([27], 1), ([10, 27], 1), ([10, 26], 1)], [([28], 1), ([10, 28], 1), ([10, 27], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4393 [
    .atom (.const (.n 4817) (word 2 0)),
    .atom (.const (.n 4818) (word 4 0)),
    .atom (.mul (.n 4819) (.n 4036) (.n 4069)),
    .atom (.mul (.n 4820) (.n 4818) (.n 4819)),
    .atom (.copy (.n 4821) (.n 4820)),
    .atom (.const (.n 4822) (word 2 0)),
    .atom (.mul (.n 4823) (.n 4822) (.n 4550)),
    .atom (.copy (.n 4824) (.n 4823)),
    .atom (.mul (.n 4825) (.n 4098) (.n 4231)),
    .atom (.add (.n 4826) (.n 4231) (.n 4825)),
    .atom (.mul (.n 4827) (.n 4098) (.n 4214)),
    .atom (.add (.n 4828) (.n 4826) (.n 4827)),
    .atom (.copy (.n 4829) (.n 4828)),
    .atom (.mul (.n 4830) (.n 4098) (.n 4235)),
    .atom (.add (.n 4831) (.n 4235) (.n 4830)),
    .atom (.mul (.n 4832) (.n 4098) (.n 4231)),
    .atom (.add (.n 4833) (.n 4831) (.n 4832)),
    .atom (.copy (.n 4834) (.n 4833))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4393, a4394, a4395, a4396, a4397, a4398, a4399, a4400, a4401, a4402, a4403, a4404, a4405, a4406,
    a4407, a4408, a4409, a4410, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5011 [
    .atom (.load (.n 5435) (.n 13) 0),
    .atom (.mul (.n 5436) (.n 5435) (.n 4817)),
    .atom (.load (.n 5437) (.n 13) 1),
    .atom (.mul (.n 5438) (.n 5437) (.n 4821)),
    .atom (.add (.n 5439) (.n 5436) (.n 5438)),
    .atom (.load (.n 5440) (.n 13) 2),
    .atom (.mul (.n 5441) (.n 5440) (.n 4824)),
    .atom (.add (.n 5442) (.n 5439) (.n 5441)),
    .atom (.load (.n 5443) (.n 13) 3),
    .atom (.mul (.n 5444) (.n 5443) (.n 4829)),
    .atom (.add (.n 5445) (.n 5442) (.n 5444)),
    .atom (.load (.n 5446) (.n 13) 4),
    .atom (.mul (.n 5447) (.n 5446) (.n 4834)),
    .atom (.add (.n 5448) (.n 5445) (.n 5447)),
    .atom (.add (.n 5449) (.n 14) (.n 5448)),
    .atom (.mul (.n 5450) (.n 1121) (.n 5449)),
    .atom (.add (.n 5451) (.n 5434) (.n 5450))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5011, a5012, a5013, a5014, a5015, a5016, a5017, a5018, a5019, a5020, a5021, a5022, a5023, a5024,
    a5025, a5026, a5027, -⟩ := hs1
  have e5011 := tb_loadHolds_unique a5011 (hw 0 (by norm_num))
  have e5013 := tb_loadHolds_unique a5013 (hw 1 (by norm_num))
  have e5016 := tb_loadHolds_unique a5016 (hw 2 (by norm_num))
  have e5019 := tb_loadHolds_unique a5019 (hw 3 (by norm_num))
  have e5022 := tb_loadHolds_unique a5022 (hw 4 (by norm_num))
  have v4036 : σ (.n 4036) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 62) (by norm_num)).2.2
  have v4069 : σ (.n 4069) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_eval h (k := 67) (by norm_num)).2.2
  have v4098 : σ (.n 4098) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_eval h (k := 71) (by norm_num)).2.2
  have v4214 : σ (.n 4214) = ev 26 := by
    rw [← hev 26 (by norm_num)]; exact (vt_eval h (k := 87) (by norm_num)).2.2
  have v4231 : σ (.n 4231) = ev 27 := by
    rw [← hev 27 (by norm_num)]; exact (vt_eval h (k := 88) (by norm_num)).2.2
  have v4235 : σ (.n 4235) = ev 28 := by
    rw [← hev 28 (by norm_num)]; exact (vt_eval h (k := 89) (by norm_num)).2.2
  have v4550 : σ (.n 4550) = ev 71 := by
    rw [← hev 71 (by norm_num)]; exact (vt_eval h (k := 132) (by norm_num)).2.2
  have hB : σ (.n 5449) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 6], 4)], [([71], 2)], [([27], 1), ([10, 27], 1), ([10, 26], 1)], [([28], 1), ([10, 28], 1), ([10, 27], 1)]] := by
    simp only [v4550, v4235, v4231, v4214, v4098, v4069, v4036, a5025, a5024, a5023, e5022, a5021, a5020,
      e5019, a5018, a5017, e5016, a5015, a5014, e5013, a5012, e5011, a4410, a4409, a4408,
      a4407, a4406, a4405, a4404, a4403, a4402, a4401, a4400, a4399, a4398, a4397, a4396,
      a4395, a4394, a4393]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5027, a5026, hB]

set_option maxRecDepth 10000 in
theorem vtB05_9 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5468) = σ (.n 5451) + σ (.n 1130) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 6], 8)], [([72], 2)], [([29], 1), ([10, 29], 1), ([10, 28], 1)], [([30], 1), ([10, 30], 1), ([10, 29], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4411 [
    .atom (.const (.n 4835) (word 2 0)),
    .atom (.const (.n 4836) (word 8 0)),
    .atom (.mul (.n 4837) (.n 4036) (.n 4069)),
    .atom (.mul (.n 4838) (.n 4836) (.n 4837)),
    .atom (.copy (.n 4839) (.n 4838)),
    .atom (.const (.n 4840) (word 2 0)),
    .atom (.mul (.n 4841) (.n 4840) (.n 4554)),
    .atom (.copy (.n 4842) (.n 4841)),
    .atom (.mul (.n 4843) (.n 4098) (.n 4239)),
    .atom (.add (.n 4844) (.n 4239) (.n 4843)),
    .atom (.mul (.n 4845) (.n 4098) (.n 4235)),
    .atom (.add (.n 4846) (.n 4844) (.n 4845)),
    .atom (.copy (.n 4847) (.n 4846)),
    .atom (.mul (.n 4848) (.n 4098) (.n 4243)),
    .atom (.add (.n 4849) (.n 4243) (.n 4848)),
    .atom (.mul (.n 4850) (.n 4098) (.n 4239)),
    .atom (.add (.n 4851) (.n 4849) (.n 4850)),
    .atom (.copy (.n 4852) (.n 4851))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4411, a4412, a4413, a4414, a4415, a4416, a4417, a4418, a4419, a4420, a4421, a4422, a4423, a4424,
    a4425, a4426, a4427, a4428, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5028 [
    .atom (.load (.n 5452) (.n 13) 0),
    .atom (.mul (.n 5453) (.n 5452) (.n 4835)),
    .atom (.load (.n 5454) (.n 13) 1),
    .atom (.mul (.n 5455) (.n 5454) (.n 4839)),
    .atom (.add (.n 5456) (.n 5453) (.n 5455)),
    .atom (.load (.n 5457) (.n 13) 2),
    .atom (.mul (.n 5458) (.n 5457) (.n 4842)),
    .atom (.add (.n 5459) (.n 5456) (.n 5458)),
    .atom (.load (.n 5460) (.n 13) 3),
    .atom (.mul (.n 5461) (.n 5460) (.n 4847)),
    .atom (.add (.n 5462) (.n 5459) (.n 5461)),
    .atom (.load (.n 5463) (.n 13) 4),
    .atom (.mul (.n 5464) (.n 5463) (.n 4852)),
    .atom (.add (.n 5465) (.n 5462) (.n 5464)),
    .atom (.add (.n 5466) (.n 14) (.n 5465)),
    .atom (.mul (.n 5467) (.n 1130) (.n 5466)),
    .atom (.add (.n 5468) (.n 5451) (.n 5467))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5028, a5029, a5030, a5031, a5032, a5033, a5034, a5035, a5036, a5037, a5038, a5039, a5040, a5041,
    a5042, a5043, a5044, -⟩ := hs1
  have e5028 := tb_loadHolds_unique a5028 (hw 0 (by norm_num))
  have e5030 := tb_loadHolds_unique a5030 (hw 1 (by norm_num))
  have e5033 := tb_loadHolds_unique a5033 (hw 2 (by norm_num))
  have e5036 := tb_loadHolds_unique a5036 (hw 3 (by norm_num))
  have e5039 := tb_loadHolds_unique a5039 (hw 4 (by norm_num))
  have v4036 : σ (.n 4036) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 62) (by norm_num)).2.2
  have v4069 : σ (.n 4069) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_eval h (k := 67) (by norm_num)).2.2
  have v4098 : σ (.n 4098) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_eval h (k := 71) (by norm_num)).2.2
  have v4235 : σ (.n 4235) = ev 28 := by
    rw [← hev 28 (by norm_num)]; exact (vt_eval h (k := 89) (by norm_num)).2.2
  have v4239 : σ (.n 4239) = ev 29 := by
    rw [← hev 29 (by norm_num)]; exact (vt_eval h (k := 90) (by norm_num)).2.2
  have v4243 : σ (.n 4243) = ev 30 := by
    rw [← hev 30 (by norm_num)]; exact (vt_eval h (k := 91) (by norm_num)).2.2
  have v4554 : σ (.n 4554) = ev 72 := by
    rw [← hev 72 (by norm_num)]; exact (vt_eval h (k := 133) (by norm_num)).2.2
  have hB : σ (.n 5466) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 6], 8)], [([72], 2)], [([29], 1), ([10, 29], 1), ([10, 28], 1)], [([30], 1), ([10, 30], 1), ([10, 29], 1)]] := by
    simp only [v4554, v4243, v4239, v4235, v4098, v4069, v4036, a5042, a5041, a5040, e5039, a5038, a5037,
      e5036, a5035, a5034, e5033, a5032, a5031, e5030, a5029, e5028, a4428, a4427, a4426,
      a4425, a4424, a4423, a4422, a4421, a4420, a4419, a4418, a4417, a4416, a4415, a4414,
      a4413, a4412, a4411]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5044, a5043, hB]

set_option maxRecDepth 10000 in
theorem vtB05_10 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5485) = σ (.n 5468) + σ (.n 1139) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 7], 1)], [([73], 2)], [([31], 1), ([10, 31], 1), ([10, 30], 1)], [([14], 1), ([10, 14], 1), ([10, 31], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4429 [
    .atom (.const (.n 4853) (word 2 0)),
    .atom (.mul (.n 4854) (.n 4036) (.n 4086)),
    .atom (.copy (.n 4855) (.n 4854)),
    .atom (.const (.n 4856) (word 2 0)),
    .atom (.mul (.n 4857) (.n 4856) (.n 4558)),
    .atom (.copy (.n 4858) (.n 4857)),
    .atom (.mul (.n 4859) (.n 4098) (.n 4260)),
    .atom (.add (.n 4860) (.n 4260) (.n 4859)),
    .atom (.mul (.n 4861) (.n 4098) (.n 4243)),
    .atom (.add (.n 4862) (.n 4860) (.n 4861)),
    .atom (.copy (.n 4863) (.n 4862)),
    .atom (.mul (.n 4864) (.n 4098) (.n 4127)),
    .atom (.add (.n 4865) (.n 4127) (.n 4864)),
    .atom (.mul (.n 4866) (.n 4098) (.n 4260)),
    .atom (.add (.n 4867) (.n 4865) (.n 4866)),
    .atom (.copy (.n 4868) (.n 4867))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4429, a4430, a4431, a4432, a4433, a4434, a4435, a4436, a4437, a4438, a4439, a4440, a4441, a4442,
    a4443, a4444, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5045 [
    .atom (.load (.n 5469) (.n 13) 0),
    .atom (.mul (.n 5470) (.n 5469) (.n 4853)),
    .atom (.load (.n 5471) (.n 13) 1),
    .atom (.mul (.n 5472) (.n 5471) (.n 4855)),
    .atom (.add (.n 5473) (.n 5470) (.n 5472)),
    .atom (.load (.n 5474) (.n 13) 2),
    .atom (.mul (.n 5475) (.n 5474) (.n 4858)),
    .atom (.add (.n 5476) (.n 5473) (.n 5475)),
    .atom (.load (.n 5477) (.n 13) 3),
    .atom (.mul (.n 5478) (.n 5477) (.n 4863)),
    .atom (.add (.n 5479) (.n 5476) (.n 5478)),
    .atom (.load (.n 5480) (.n 13) 4),
    .atom (.mul (.n 5481) (.n 5480) (.n 4868)),
    .atom (.add (.n 5482) (.n 5479) (.n 5481)),
    .atom (.add (.n 5483) (.n 14) (.n 5482)),
    .atom (.mul (.n 5484) (.n 1139) (.n 5483)),
    .atom (.add (.n 5485) (.n 5468) (.n 5484))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5045, a5046, a5047, a5048, a5049, a5050, a5051, a5052, a5053, a5054, a5055, a5056, a5057, a5058,
    a5059, a5060, a5061, -⟩ := hs1
  have e5045 := tb_loadHolds_unique a5045 (hw 0 (by norm_num))
  have e5047 := tb_loadHolds_unique a5047 (hw 1 (by norm_num))
  have e5050 := tb_loadHolds_unique a5050 (hw 2 (by norm_num))
  have e5053 := tb_loadHolds_unique a5053 (hw 3 (by norm_num))
  have e5056 := tb_loadHolds_unique a5056 (hw 4 (by norm_num))
  have v4036 : σ (.n 4036) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 62) (by norm_num)).2.2
  have v4086 : σ (.n 4086) = ev 7 := by
    rw [← hev 7 (by norm_num)]; exact (vt_eval h (k := 68) (by norm_num)).2.2
  have v4098 : σ (.n 4098) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_eval h (k := 71) (by norm_num)).2.2
  have v4127 : σ (.n 4127) = ev 14 := by
    rw [← hev 14 (by norm_num)]; exact (vt_eval h (k := 75) (by norm_num)).2.2
  have v4243 : σ (.n 4243) = ev 30 := by
    rw [← hev 30 (by norm_num)]; exact (vt_eval h (k := 91) (by norm_num)).2.2
  have v4260 : σ (.n 4260) = ev 31 := by
    rw [← hev 31 (by norm_num)]; exact (vt_eval h (k := 92) (by norm_num)).2.2
  have v4558 : σ (.n 4558) = ev 73 := by
    rw [← hev 73 (by norm_num)]; exact (vt_eval h (k := 134) (by norm_num)).2.2
  have hB : σ (.n 5483) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 7], 1)], [([73], 2)], [([31], 1), ([10, 31], 1), ([10, 30], 1)], [([14], 1), ([10, 14], 1), ([10, 31], 1)]] := by
    simp only [v4558, v4260, v4243, v4127, v4098, v4086, v4036, a5059, a5058, a5057, e5056, a5055, a5054,
      e5053, a5052, a5051, e5050, a5049, a5048, e5047, a5046, e5045, a4444, a4443, a4442,
      a4441, a4440, a4439, a4438, a4437, a4436, a4435, a4434, a4433, a4432, a4431, a4430,
      a4429]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5061, a5060, hB]

set_option maxRecDepth 10000 in
theorem vtB05_11 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5502) = σ (.n 5485) + σ (.n 1148) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 8], 1)], [([74], 2)], [([32], 1)], [([33], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4445 [
    .atom (.const (.n 4869) (word 2 0)),
    .atom (.mul (.n 4870) (.n 4036) (.n 4090)),
    .atom (.copy (.n 4871) (.n 4870)),
    .atom (.const (.n 4872) (word 2 0)),
    .atom (.mul (.n 4873) (.n 4872) (.n 4562)),
    .atom (.copy (.n 4874) (.n 4873)),
    .atom (.copy (.n 4875) (.n 4264)),
    .atom (.copy (.n 4876) (.n 4268))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4445, a4446, a4447, a4448, a4449, a4450, a4451, a4452, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5062 [
    .atom (.load (.n 5486) (.n 13) 0),
    .atom (.mul (.n 5487) (.n 5486) (.n 4869)),
    .atom (.load (.n 5488) (.n 13) 1),
    .atom (.mul (.n 5489) (.n 5488) (.n 4871)),
    .atom (.add (.n 5490) (.n 5487) (.n 5489)),
    .atom (.load (.n 5491) (.n 13) 2),
    .atom (.mul (.n 5492) (.n 5491) (.n 4874)),
    .atom (.add (.n 5493) (.n 5490) (.n 5492)),
    .atom (.load (.n 5494) (.n 13) 3),
    .atom (.mul (.n 5495) (.n 5494) (.n 4875)),
    .atom (.add (.n 5496) (.n 5493) (.n 5495)),
    .atom (.load (.n 5497) (.n 13) 4),
    .atom (.mul (.n 5498) (.n 5497) (.n 4876)),
    .atom (.add (.n 5499) (.n 5496) (.n 5498)),
    .atom (.add (.n 5500) (.n 14) (.n 5499)),
    .atom (.mul (.n 5501) (.n 1148) (.n 5500)),
    .atom (.add (.n 5502) (.n 5485) (.n 5501))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5062, a5063, a5064, a5065, a5066, a5067, a5068, a5069, a5070, a5071, a5072, a5073, a5074, a5075,
    a5076, a5077, a5078, -⟩ := hs1
  have e5062 := tb_loadHolds_unique a5062 (hw 0 (by norm_num))
  have e5064 := tb_loadHolds_unique a5064 (hw 1 (by norm_num))
  have e5067 := tb_loadHolds_unique a5067 (hw 2 (by norm_num))
  have e5070 := tb_loadHolds_unique a5070 (hw 3 (by norm_num))
  have e5073 := tb_loadHolds_unique a5073 (hw 4 (by norm_num))
  have v4036 : σ (.n 4036) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 62) (by norm_num)).2.2
  have v4090 : σ (.n 4090) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_eval h (k := 69) (by norm_num)).2.2
  have v4264 : σ (.n 4264) = ev 32 := by
    rw [← hev 32 (by norm_num)]; exact (vt_eval h (k := 93) (by norm_num)).2.2
  have v4268 : σ (.n 4268) = ev 33 := by
    rw [← hev 33 (by norm_num)]; exact (vt_eval h (k := 94) (by norm_num)).2.2
  have v4562 : σ (.n 4562) = ev 74 := by
    rw [← hev 74 (by norm_num)]; exact (vt_eval h (k := 135) (by norm_num)).2.2
  have hB : σ (.n 5500) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 8], 1)], [([74], 2)], [([32], 1)], [([33], 1)]] := by
    simp only [v4562, v4268, v4264, v4090, v4036, a5076, a5075, a5074, e5073, a5072, a5071, e5070, a5069,
      a5068, e5067, a5066, a5065, e5064, a5063, e5062, a4452, a4451, a4450, a4449, a4448,
      a4447, a4446, a4445]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5078, a5077, hB]

set_option maxRecDepth 10000 in
theorem vtB05_12 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5519) = σ (.n 5502) + σ (.n 1157) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 8], 2)], [([75], 2)], [([34], 1)], [([35], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4453 [
    .atom (.const (.n 4877) (word 2 0)),
    .atom (.const (.n 4878) (word 2 0)),
    .atom (.mul (.n 4879) (.n 4036) (.n 4090)),
    .atom (.mul (.n 4880) (.n 4878) (.n 4879)),
    .atom (.copy (.n 4881) (.n 4880)),
    .atom (.const (.n 4882) (word 2 0)),
    .atom (.mul (.n 4883) (.n 4882) (.n 4579)),
    .atom (.copy (.n 4884) (.n 4883)),
    .atom (.copy (.n 4885) (.n 4272)),
    .atom (.copy (.n 4886) (.n 4289))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4453, a4454, a4455, a4456, a4457, a4458, a4459, a4460, a4461, a4462, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5079 [
    .atom (.load (.n 5503) (.n 13) 0),
    .atom (.mul (.n 5504) (.n 5503) (.n 4877)),
    .atom (.load (.n 5505) (.n 13) 1),
    .atom (.mul (.n 5506) (.n 5505) (.n 4881)),
    .atom (.add (.n 5507) (.n 5504) (.n 5506)),
    .atom (.load (.n 5508) (.n 13) 2),
    .atom (.mul (.n 5509) (.n 5508) (.n 4884)),
    .atom (.add (.n 5510) (.n 5507) (.n 5509)),
    .atom (.load (.n 5511) (.n 13) 3),
    .atom (.mul (.n 5512) (.n 5511) (.n 4885)),
    .atom (.add (.n 5513) (.n 5510) (.n 5512)),
    .atom (.load (.n 5514) (.n 13) 4),
    .atom (.mul (.n 5515) (.n 5514) (.n 4886)),
    .atom (.add (.n 5516) (.n 5513) (.n 5515)),
    .atom (.add (.n 5517) (.n 14) (.n 5516)),
    .atom (.mul (.n 5518) (.n 1157) (.n 5517)),
    .atom (.add (.n 5519) (.n 5502) (.n 5518))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5079, a5080, a5081, a5082, a5083, a5084, a5085, a5086, a5087, a5088, a5089, a5090, a5091, a5092,
    a5093, a5094, a5095, -⟩ := hs1
  have e5079 := tb_loadHolds_unique a5079 (hw 0 (by norm_num))
  have e5081 := tb_loadHolds_unique a5081 (hw 1 (by norm_num))
  have e5084 := tb_loadHolds_unique a5084 (hw 2 (by norm_num))
  have e5087 := tb_loadHolds_unique a5087 (hw 3 (by norm_num))
  have e5090 := tb_loadHolds_unique a5090 (hw 4 (by norm_num))
  have v4036 : σ (.n 4036) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 62) (by norm_num)).2.2
  have v4090 : σ (.n 4090) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_eval h (k := 69) (by norm_num)).2.2
  have v4272 : σ (.n 4272) = ev 34 := by
    rw [← hev 34 (by norm_num)]; exact (vt_eval h (k := 95) (by norm_num)).2.2
  have v4289 : σ (.n 4289) = ev 35 := by
    rw [← hev 35 (by norm_num)]; exact (vt_eval h (k := 96) (by norm_num)).2.2
  have v4579 : σ (.n 4579) = ev 75 := by
    rw [← hev 75 (by norm_num)]; exact (vt_eval h (k := 136) (by norm_num)).2.2
  have hB : σ (.n 5517) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 8], 2)], [([75], 2)], [([34], 1)], [([35], 1)]] := by
    simp only [v4579, v4289, v4272, v4090, v4036, a5093, a5092, a5091, e5090, a5089, a5088, e5087, a5086,
      a5085, e5084, a5083, a5082, e5081, a5080, e5079, a4462, a4461, a4460, a4459, a4458,
      a4457, a4456, a4455, a4454, a4453]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5095, a5094, hB]

set_option maxRecDepth 10000 in
theorem vtB05_13 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5536) = σ (.n 5519) + σ (.n 1166) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 8], 4)], [([76], 2)], [([36], 1)], [([37], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4463 [
    .atom (.const (.n 4887) (word 2 0)),
    .atom (.const (.n 4888) (word 4 0)),
    .atom (.mul (.n 4889) (.n 4036) (.n 4090)),
    .atom (.mul (.n 4890) (.n 4888) (.n 4889)),
    .atom (.copy (.n 4891) (.n 4890)),
    .atom (.const (.n 4892) (word 2 0)),
    .atom (.mul (.n 4893) (.n 4892) (.n 4583)),
    .atom (.copy (.n 4894) (.n 4893)),
    .atom (.copy (.n 4895) (.n 4293)),
    .atom (.copy (.n 4896) (.n 4297))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4463, a4464, a4465, a4466, a4467, a4468, a4469, a4470, a4471, a4472, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5096 [
    .atom (.load (.n 5520) (.n 13) 0),
    .atom (.mul (.n 5521) (.n 5520) (.n 4887)),
    .atom (.load (.n 5522) (.n 13) 1),
    .atom (.mul (.n 5523) (.n 5522) (.n 4891)),
    .atom (.add (.n 5524) (.n 5521) (.n 5523)),
    .atom (.load (.n 5525) (.n 13) 2),
    .atom (.mul (.n 5526) (.n 5525) (.n 4894)),
    .atom (.add (.n 5527) (.n 5524) (.n 5526)),
    .atom (.load (.n 5528) (.n 13) 3),
    .atom (.mul (.n 5529) (.n 5528) (.n 4895)),
    .atom (.add (.n 5530) (.n 5527) (.n 5529)),
    .atom (.load (.n 5531) (.n 13) 4),
    .atom (.mul (.n 5532) (.n 5531) (.n 4896)),
    .atom (.add (.n 5533) (.n 5530) (.n 5532)),
    .atom (.add (.n 5534) (.n 14) (.n 5533)),
    .atom (.mul (.n 5535) (.n 1166) (.n 5534)),
    .atom (.add (.n 5536) (.n 5519) (.n 5535))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5096, a5097, a5098, a5099, a5100, a5101, a5102, a5103, a5104, a5105, a5106, a5107, a5108, a5109,
    a5110, a5111, a5112, -⟩ := hs1
  have e5096 := tb_loadHolds_unique a5096 (hw 0 (by norm_num))
  have e5098 := tb_loadHolds_unique a5098 (hw 1 (by norm_num))
  have e5101 := tb_loadHolds_unique a5101 (hw 2 (by norm_num))
  have e5104 := tb_loadHolds_unique a5104 (hw 3 (by norm_num))
  have e5107 := tb_loadHolds_unique a5107 (hw 4 (by norm_num))
  have v4036 : σ (.n 4036) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 62) (by norm_num)).2.2
  have v4090 : σ (.n 4090) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_eval h (k := 69) (by norm_num)).2.2
  have v4293 : σ (.n 4293) = ev 36 := by
    rw [← hev 36 (by norm_num)]; exact (vt_eval h (k := 97) (by norm_num)).2.2
  have v4297 : σ (.n 4297) = ev 37 := by
    rw [← hev 37 (by norm_num)]; exact (vt_eval h (k := 98) (by norm_num)).2.2
  have v4583 : σ (.n 4583) = ev 76 := by
    rw [← hev 76 (by norm_num)]; exact (vt_eval h (k := 137) (by norm_num)).2.2
  have hB : σ (.n 5534) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 8], 4)], [([76], 2)], [([36], 1)], [([37], 1)]] := by
    simp only [v4583, v4297, v4293, v4090, v4036, a5110, a5109, a5108, e5107, a5106, a5105, e5104, a5103,
      a5102, e5101, a5100, a5099, e5098, a5097, e5096, a4472, a4471, a4470, a4469, a4468,
      a4467, a4466, a4465, a4464, a4463]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5112, a5111, hB]

set_option maxRecDepth 10000 in
theorem vtB05_14 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5553) = σ (.n 5536) + σ (.n 1175) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 8], 8)], [([77], 2)], [([38], 1)], [([39], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4473 [
    .atom (.const (.n 4897) (word 2 0)),
    .atom (.const (.n 4898) (word 8 0)),
    .atom (.mul (.n 4899) (.n 4036) (.n 4090)),
    .atom (.mul (.n 4900) (.n 4898) (.n 4899)),
    .atom (.copy (.n 4901) (.n 4900)),
    .atom (.const (.n 4902) (word 2 0)),
    .atom (.mul (.n 4903) (.n 4902) (.n 4587)),
    .atom (.copy (.n 4904) (.n 4903)),
    .atom (.copy (.n 4905) (.n 4301)),
    .atom (.copy (.n 4906) (.n 4318))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4473, a4474, a4475, a4476, a4477, a4478, a4479, a4480, a4481, a4482, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5113 [
    .atom (.load (.n 5537) (.n 13) 0),
    .atom (.mul (.n 5538) (.n 5537) (.n 4897)),
    .atom (.load (.n 5539) (.n 13) 1),
    .atom (.mul (.n 5540) (.n 5539) (.n 4901)),
    .atom (.add (.n 5541) (.n 5538) (.n 5540)),
    .atom (.load (.n 5542) (.n 13) 2),
    .atom (.mul (.n 5543) (.n 5542) (.n 4904)),
    .atom (.add (.n 5544) (.n 5541) (.n 5543)),
    .atom (.load (.n 5545) (.n 13) 3),
    .atom (.mul (.n 5546) (.n 5545) (.n 4905)),
    .atom (.add (.n 5547) (.n 5544) (.n 5546)),
    .atom (.load (.n 5548) (.n 13) 4),
    .atom (.mul (.n 5549) (.n 5548) (.n 4906)),
    .atom (.add (.n 5550) (.n 5547) (.n 5549)),
    .atom (.add (.n 5551) (.n 14) (.n 5550)),
    .atom (.mul (.n 5552) (.n 1175) (.n 5551)),
    .atom (.add (.n 5553) (.n 5536) (.n 5552))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5113, a5114, a5115, a5116, a5117, a5118, a5119, a5120, a5121, a5122, a5123, a5124, a5125, a5126,
    a5127, a5128, a5129, -⟩ := hs1
  have e5113 := tb_loadHolds_unique a5113 (hw 0 (by norm_num))
  have e5115 := tb_loadHolds_unique a5115 (hw 1 (by norm_num))
  have e5118 := tb_loadHolds_unique a5118 (hw 2 (by norm_num))
  have e5121 := tb_loadHolds_unique a5121 (hw 3 (by norm_num))
  have e5124 := tb_loadHolds_unique a5124 (hw 4 (by norm_num))
  have v4036 : σ (.n 4036) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 62) (by norm_num)).2.2
  have v4090 : σ (.n 4090) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_eval h (k := 69) (by norm_num)).2.2
  have v4301 : σ (.n 4301) = ev 38 := by
    rw [← hev 38 (by norm_num)]; exact (vt_eval h (k := 99) (by norm_num)).2.2
  have v4318 : σ (.n 4318) = ev 39 := by
    rw [← hev 39 (by norm_num)]; exact (vt_eval h (k := 100) (by norm_num)).2.2
  have v4587 : σ (.n 4587) = ev 77 := by
    rw [← hev 77 (by norm_num)]; exact (vt_eval h (k := 138) (by norm_num)).2.2
  have hB : σ (.n 5551) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 8], 8)], [([77], 2)], [([38], 1)], [([39], 1)]] := by
    simp only [v4587, v4318, v4301, v4090, v4036, a5127, a5126, a5125, e5124, a5123, a5122, e5121, a5120,
      a5119, e5118, a5117, a5116, e5115, a5114, e5113, a4482, a4481, a4480, a4479, a4478,
      a4477, a4476, a4475, a4474, a4473]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5129, a5128, hB]

set_option maxRecDepth 10000 in
theorem vtB05_15 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5570) = σ (.n 5553) + σ (.n 1184) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 9], 1)], [([78], 2)], [([40], 1), ([11, 40], 1)], [([41], 1), ([11, 41], 1), ([11, 40], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4483 [
    .atom (.const (.n 4907) (word 2 0)),
    .atom (.mul (.n 4908) (.n 4036) (.n 4094)),
    .atom (.copy (.n 4909) (.n 4908)),
    .atom (.const (.n 4910) (word 2 0)),
    .atom (.mul (.n 4911) (.n 4910) (.n 4591)),
    .atom (.copy (.n 4912) (.n 4911)),
    .atom (.mul (.n 4913) (.n 4115) (.n 4322)),
    .atom (.add (.n 4914) (.n 4322) (.n 4913)),
    .atom (.copy (.n 4915) (.n 4914)),
    .atom (.mul (.n 4916) (.n 4115) (.n 4326)),
    .atom (.add (.n 4917) (.n 4326) (.n 4916)),
    .atom (.mul (.n 4918) (.n 4115) (.n 4322)),
    .atom (.add (.n 4919) (.n 4917) (.n 4918)),
    .atom (.copy (.n 4920) (.n 4919))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4483, a4484, a4485, a4486, a4487, a4488, a4489, a4490, a4491, a4492, a4493, a4494, a4495, a4496,
    -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5130 [
    .atom (.load (.n 5554) (.n 13) 0),
    .atom (.mul (.n 5555) (.n 5554) (.n 4907)),
    .atom (.load (.n 5556) (.n 13) 1),
    .atom (.mul (.n 5557) (.n 5556) (.n 4909)),
    .atom (.add (.n 5558) (.n 5555) (.n 5557)),
    .atom (.load (.n 5559) (.n 13) 2),
    .atom (.mul (.n 5560) (.n 5559) (.n 4912)),
    .atom (.add (.n 5561) (.n 5558) (.n 5560)),
    .atom (.load (.n 5562) (.n 13) 3),
    .atom (.mul (.n 5563) (.n 5562) (.n 4915)),
    .atom (.add (.n 5564) (.n 5561) (.n 5563)),
    .atom (.load (.n 5565) (.n 13) 4),
    .atom (.mul (.n 5566) (.n 5565) (.n 4920)),
    .atom (.add (.n 5567) (.n 5564) (.n 5566)),
    .atom (.add (.n 5568) (.n 14) (.n 5567)),
    .atom (.mul (.n 5569) (.n 1184) (.n 5568)),
    .atom (.add (.n 5570) (.n 5553) (.n 5569))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5130, a5131, a5132, a5133, a5134, a5135, a5136, a5137, a5138, a5139, a5140, a5141, a5142, a5143,
    a5144, a5145, a5146, -⟩ := hs1
  have e5130 := tb_loadHolds_unique a5130 (hw 0 (by norm_num))
  have e5132 := tb_loadHolds_unique a5132 (hw 1 (by norm_num))
  have e5135 := tb_loadHolds_unique a5135 (hw 2 (by norm_num))
  have e5138 := tb_loadHolds_unique a5138 (hw 3 (by norm_num))
  have e5141 := tb_loadHolds_unique a5141 (hw 4 (by norm_num))
  have v4036 : σ (.n 4036) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 62) (by norm_num)).2.2
  have v4094 : σ (.n 4094) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 70) (by norm_num)).2.2
  have v4115 : σ (.n 4115) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_eval h (k := 72) (by norm_num)).2.2
  have v4322 : σ (.n 4322) = ev 40 := by
    rw [← hev 40 (by norm_num)]; exact (vt_eval h (k := 101) (by norm_num)).2.2
  have v4326 : σ (.n 4326) = ev 41 := by
    rw [← hev 41 (by norm_num)]; exact (vt_eval h (k := 102) (by norm_num)).2.2
  have v4591 : σ (.n 4591) = ev 78 := by
    rw [← hev 78 (by norm_num)]; exact (vt_eval h (k := 139) (by norm_num)).2.2
  have hB : σ (.n 5568) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 9], 1)], [([78], 2)], [([40], 1), ([11, 40], 1)], [([41], 1), ([11, 41], 1), ([11, 40], 1)]] := by
    simp only [v4591, v4326, v4322, v4115, v4094, v4036, a5144, a5143, a5142, e5141, a5140, a5139, e5138,
      a5137, a5136, e5135, a5134, a5133, e5132, a5131, e5130, a4496, a4495, a4494, a4493,
      a4492, a4491, a4490, a4489, a4488, a4487, a4486, a4485, a4484, a4483]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5146, a5145, hB]

set_option maxRecDepth 10000 in
theorem vtB05_16 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5587) = σ (.n 5570) + σ (.n 1193) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 9], 2)], [([79], 1), ([12, 79], 2), ([12, 79], 1)], [([42], 1), ([11, 42], 1), ([11, 41], 1)], [([43], 1), ([11, 43], 1), ([11, 42], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4497 [
    .atom (.const (.n 4921) (word 2 0)),
    .atom (.const (.n 4922) (word 2 0)),
    .atom (.mul (.n 4923) (.n 4036) (.n 4094)),
    .atom (.mul (.n 4924) (.n 4922) (.n 4923)),
    .atom (.copy (.n 4925) (.n 4924)),
    .atom (.const (.n 4926) (word 2 0)),
    .atom (.mul (.n 4927) (.n 4119) (.n 4608)),
    .atom (.mul (.n 4928) (.n 4926) (.n 4927)),
    .atom (.add (.n 4929) (.n 4608) (.n 4928)),
    .atom (.mul (.n 4930) (.n 4119) (.n 4608)),
    .atom (.add (.n 4931) (.n 4929) (.n 4930)),
    .atom (.copy (.n 4932) (.n 4931)),
    .atom (.mul (.n 4933) (.n 4115) (.n 4330)),
    .atom (.add (.n 4934) (.n 4330) (.n 4933)),
    .atom (.mul (.n 4935) (.n 4115) (.n 4326)),
    .atom (.add (.n 4936) (.n 4934) (.n 4935)),
    .atom (.copy (.n 4937) (.n 4936)),
    .atom (.mul (.n 4938) (.n 4115) (.n 4347)),
    .atom (.add (.n 4939) (.n 4347) (.n 4938)),
    .atom (.mul (.n 4940) (.n 4115) (.n 4330)),
    .atom (.add (.n 4941) (.n 4939) (.n 4940)),
    .atom (.copy (.n 4942) (.n 4941))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4497, a4498, a4499, a4500, a4501, a4502, a4503, a4504, a4505, a4506, a4507, a4508, a4509, a4510,
    a4511, a4512, a4513, a4514, a4515, a4516, a4517, a4518, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5147 [
    .atom (.load (.n 5571) (.n 13) 0),
    .atom (.mul (.n 5572) (.n 5571) (.n 4921)),
    .atom (.load (.n 5573) (.n 13) 1),
    .atom (.mul (.n 5574) (.n 5573) (.n 4925)),
    .atom (.add (.n 5575) (.n 5572) (.n 5574)),
    .atom (.load (.n 5576) (.n 13) 2),
    .atom (.mul (.n 5577) (.n 5576) (.n 4932)),
    .atom (.add (.n 5578) (.n 5575) (.n 5577)),
    .atom (.load (.n 5579) (.n 13) 3),
    .atom (.mul (.n 5580) (.n 5579) (.n 4937)),
    .atom (.add (.n 5581) (.n 5578) (.n 5580)),
    .atom (.load (.n 5582) (.n 13) 4),
    .atom (.mul (.n 5583) (.n 5582) (.n 4942)),
    .atom (.add (.n 5584) (.n 5581) (.n 5583)),
    .atom (.add (.n 5585) (.n 14) (.n 5584)),
    .atom (.mul (.n 5586) (.n 1193) (.n 5585)),
    .atom (.add (.n 5587) (.n 5570) (.n 5586))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5147, a5148, a5149, a5150, a5151, a5152, a5153, a5154, a5155, a5156, a5157, a5158, a5159, a5160,
    a5161, a5162, a5163, -⟩ := hs1
  have e5147 := tb_loadHolds_unique a5147 (hw 0 (by norm_num))
  have e5149 := tb_loadHolds_unique a5149 (hw 1 (by norm_num))
  have e5152 := tb_loadHolds_unique a5152 (hw 2 (by norm_num))
  have e5155 := tb_loadHolds_unique a5155 (hw 3 (by norm_num))
  have e5158 := tb_loadHolds_unique a5158 (hw 4 (by norm_num))
  have v4036 : σ (.n 4036) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 62) (by norm_num)).2.2
  have v4094 : σ (.n 4094) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 70) (by norm_num)).2.2
  have v4115 : σ (.n 4115) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_eval h (k := 72) (by norm_num)).2.2
  have v4119 : σ (.n 4119) = ev 12 := by
    rw [← hev 12 (by norm_num)]; exact (vt_eval h (k := 73) (by norm_num)).2.2
  have v4326 : σ (.n 4326) = ev 41 := by
    rw [← hev 41 (by norm_num)]; exact (vt_eval h (k := 102) (by norm_num)).2.2
  have v4330 : σ (.n 4330) = ev 42 := by
    rw [← hev 42 (by norm_num)]; exact (vt_eval h (k := 103) (by norm_num)).2.2
  have v4347 : σ (.n 4347) = ev 43 := by
    rw [← hev 43 (by norm_num)]; exact (vt_eval h (k := 104) (by norm_num)).2.2
  have v4608 : σ (.n 4608) = ev 79 := by
    rw [← hev 79 (by norm_num)]; exact (vt_eval h (k := 140) (by norm_num)).2.2
  have hB : σ (.n 5585) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 9], 2)], [([79], 1), ([12, 79], 2), ([12, 79], 1)], [([42], 1), ([11, 42], 1), ([11, 41], 1)], [([43], 1), ([11, 43], 1), ([11, 42], 1)]] := by
    simp only [v4608, v4347, v4330, v4326, v4119, v4115, v4094, v4036, a5161, a5160, a5159, e5158, a5157,
      a5156, e5155, a5154, a5153, e5152, a5151, a5150, e5149, a5148, e5147, a4518, a4517,
      a4516, a4515, a4514, a4513, a4512, a4511, a4510, a4509, a4508, a4507, a4506, a4505,
      a4504, a4503, a4502, a4501, a4500, a4499, a4498, a4497]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5163, a5162, hB]

set_option maxRecDepth 10000 in
theorem vtB05_17 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5604) = σ (.n 5587) + σ (.n 1202) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 9], 4)], [([80], 1), ([13, 80], 2), ([13, 80], 1)], [([44], 1), ([11, 44], 1), ([11, 43], 1)], [([45], 1), ([11, 45], 1), ([11, 44], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4519 [
    .atom (.const (.n 4943) (word 2 0)),
    .atom (.const (.n 4944) (word 4 0)),
    .atom (.mul (.n 4945) (.n 4036) (.n 4094)),
    .atom (.mul (.n 4946) (.n 4944) (.n 4945)),
    .atom (.copy (.n 4947) (.n 4946)),
    .atom (.const (.n 4948) (word 2 0)),
    .atom (.mul (.n 4949) (.n 4123) (.n 4612)),
    .atom (.mul (.n 4950) (.n 4948) (.n 4949)),
    .atom (.add (.n 4951) (.n 4612) (.n 4950)),
    .atom (.mul (.n 4952) (.n 4123) (.n 4612)),
    .atom (.add (.n 4953) (.n 4951) (.n 4952)),
    .atom (.copy (.n 4954) (.n 4953)),
    .atom (.mul (.n 4955) (.n 4115) (.n 4351)),
    .atom (.add (.n 4956) (.n 4351) (.n 4955)),
    .atom (.mul (.n 4957) (.n 4115) (.n 4347)),
    .atom (.add (.n 4958) (.n 4956) (.n 4957)),
    .atom (.copy (.n 4959) (.n 4958)),
    .atom (.mul (.n 4960) (.n 4115) (.n 4355)),
    .atom (.add (.n 4961) (.n 4355) (.n 4960)),
    .atom (.mul (.n 4962) (.n 4115) (.n 4351)),
    .atom (.add (.n 4963) (.n 4961) (.n 4962)),
    .atom (.copy (.n 4964) (.n 4963))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4519, a4520, a4521, a4522, a4523, a4524, a4525, a4526, a4527, a4528, a4529, a4530, a4531, a4532,
    a4533, a4534, a4535, a4536, a4537, a4538, a4539, a4540, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5164 [
    .atom (.load (.n 5588) (.n 13) 0),
    .atom (.mul (.n 5589) (.n 5588) (.n 4943)),
    .atom (.load (.n 5590) (.n 13) 1),
    .atom (.mul (.n 5591) (.n 5590) (.n 4947)),
    .atom (.add (.n 5592) (.n 5589) (.n 5591)),
    .atom (.load (.n 5593) (.n 13) 2),
    .atom (.mul (.n 5594) (.n 5593) (.n 4954)),
    .atom (.add (.n 5595) (.n 5592) (.n 5594)),
    .atom (.load (.n 5596) (.n 13) 3),
    .atom (.mul (.n 5597) (.n 5596) (.n 4959)),
    .atom (.add (.n 5598) (.n 5595) (.n 5597)),
    .atom (.load (.n 5599) (.n 13) 4),
    .atom (.mul (.n 5600) (.n 5599) (.n 4964)),
    .atom (.add (.n 5601) (.n 5598) (.n 5600)),
    .atom (.add (.n 5602) (.n 14) (.n 5601)),
    .atom (.mul (.n 5603) (.n 1202) (.n 5602)),
    .atom (.add (.n 5604) (.n 5587) (.n 5603))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5164, a5165, a5166, a5167, a5168, a5169, a5170, a5171, a5172, a5173, a5174, a5175, a5176, a5177,
    a5178, a5179, a5180, -⟩ := hs1
  have e5164 := tb_loadHolds_unique a5164 (hw 0 (by norm_num))
  have e5166 := tb_loadHolds_unique a5166 (hw 1 (by norm_num))
  have e5169 := tb_loadHolds_unique a5169 (hw 2 (by norm_num))
  have e5172 := tb_loadHolds_unique a5172 (hw 3 (by norm_num))
  have e5175 := tb_loadHolds_unique a5175 (hw 4 (by norm_num))
  have v4036 : σ (.n 4036) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 62) (by norm_num)).2.2
  have v4094 : σ (.n 4094) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 70) (by norm_num)).2.2
  have v4115 : σ (.n 4115) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_eval h (k := 72) (by norm_num)).2.2
  have v4123 : σ (.n 4123) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 74) (by norm_num)).2.2
  have v4347 : σ (.n 4347) = ev 43 := by
    rw [← hev 43 (by norm_num)]; exact (vt_eval h (k := 104) (by norm_num)).2.2
  have v4351 : σ (.n 4351) = ev 44 := by
    rw [← hev 44 (by norm_num)]; exact (vt_eval h (k := 105) (by norm_num)).2.2
  have v4355 : σ (.n 4355) = ev 45 := by
    rw [← hev 45 (by norm_num)]; exact (vt_eval h (k := 106) (by norm_num)).2.2
  have v4612 : σ (.n 4612) = ev 80 := by
    rw [← hev 80 (by norm_num)]; exact (vt_eval h (k := 141) (by norm_num)).2.2
  have hB : σ (.n 5602) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 9], 4)], [([80], 1), ([13, 80], 2), ([13, 80], 1)], [([44], 1), ([11, 44], 1), ([11, 43], 1)], [([45], 1), ([11, 45], 1), ([11, 44], 1)]] := by
    simp only [v4612, v4355, v4351, v4347, v4123, v4115, v4094, v4036, a5178, a5177, a5176, e5175, a5174,
      a5173, e5172, a5171, a5170, e5169, a5168, a5167, e5166, a5165, e5164, a4540, a4539,
      a4538, a4537, a4536, a4535, a4534, a4533, a4532, a4531, a4530, a4529, a4528, a4527,
      a4526, a4525, a4524, a4523, a4522, a4521, a4520, a4519]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5180, a5179, hB]

set_option maxRecDepth 10000 in
theorem vtB05_18 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5621) = σ (.n 5604) + σ (.n 1211) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 9], 8)], [([81], 1), ([13, 81], 2), ([13, 81], 1)], [([46], 1), ([11, 46], 1), ([11, 45], 1)], [([47], 1), ([11, 47], 1), ([11, 46], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4541 [
    .atom (.const (.n 4965) (word 2 0)),
    .atom (.const (.n 4966) (word 8 0)),
    .atom (.mul (.n 4967) (.n 4036) (.n 4094)),
    .atom (.mul (.n 4968) (.n 4966) (.n 4967)),
    .atom (.copy (.n 4969) (.n 4968)),
    .atom (.const (.n 4970) (word 2 0)),
    .atom (.mul (.n 4971) (.n 4123) (.n 4616)),
    .atom (.mul (.n 4972) (.n 4970) (.n 4971)),
    .atom (.add (.n 4973) (.n 4616) (.n 4972)),
    .atom (.mul (.n 4974) (.n 4123) (.n 4616)),
    .atom (.add (.n 4975) (.n 4973) (.n 4974)),
    .atom (.copy (.n 4976) (.n 4975)),
    .atom (.mul (.n 4977) (.n 4115) (.n 4359)),
    .atom (.add (.n 4978) (.n 4359) (.n 4977)),
    .atom (.mul (.n 4979) (.n 4115) (.n 4355)),
    .atom (.add (.n 4980) (.n 4978) (.n 4979)),
    .atom (.copy (.n 4981) (.n 4980)),
    .atom (.mul (.n 4982) (.n 4115) (.n 4376)),
    .atom (.add (.n 4983) (.n 4376) (.n 4982)),
    .atom (.mul (.n 4984) (.n 4115) (.n 4359)),
    .atom (.add (.n 4985) (.n 4983) (.n 4984)),
    .atom (.copy (.n 4986) (.n 4985))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4541, a4542, a4543, a4544, a4545, a4546, a4547, a4548, a4549, a4550, a4551, a4552, a4553, a4554,
    a4555, a4556, a4557, a4558, a4559, a4560, a4561, a4562, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5181 [
    .atom (.load (.n 5605) (.n 13) 0),
    .atom (.mul (.n 5606) (.n 5605) (.n 4965)),
    .atom (.load (.n 5607) (.n 13) 1),
    .atom (.mul (.n 5608) (.n 5607) (.n 4969)),
    .atom (.add (.n 5609) (.n 5606) (.n 5608)),
    .atom (.load (.n 5610) (.n 13) 2),
    .atom (.mul (.n 5611) (.n 5610) (.n 4976)),
    .atom (.add (.n 5612) (.n 5609) (.n 5611)),
    .atom (.load (.n 5613) (.n 13) 3),
    .atom (.mul (.n 5614) (.n 5613) (.n 4981)),
    .atom (.add (.n 5615) (.n 5612) (.n 5614)),
    .atom (.load (.n 5616) (.n 13) 4),
    .atom (.mul (.n 5617) (.n 5616) (.n 4986)),
    .atom (.add (.n 5618) (.n 5615) (.n 5617)),
    .atom (.add (.n 5619) (.n 14) (.n 5618)),
    .atom (.mul (.n 5620) (.n 1211) (.n 5619)),
    .atom (.add (.n 5621) (.n 5604) (.n 5620))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5181, a5182, a5183, a5184, a5185, a5186, a5187, a5188, a5189, a5190, a5191, a5192, a5193, a5194,
    a5195, a5196, a5197, -⟩ := hs1
  have e5181 := tb_loadHolds_unique a5181 (hw 0 (by norm_num))
  have e5183 := tb_loadHolds_unique a5183 (hw 1 (by norm_num))
  have e5186 := tb_loadHolds_unique a5186 (hw 2 (by norm_num))
  have e5189 := tb_loadHolds_unique a5189 (hw 3 (by norm_num))
  have e5192 := tb_loadHolds_unique a5192 (hw 4 (by norm_num))
  have v4036 : σ (.n 4036) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 62) (by norm_num)).2.2
  have v4094 : σ (.n 4094) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 70) (by norm_num)).2.2
  have v4115 : σ (.n 4115) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_eval h (k := 72) (by norm_num)).2.2
  have v4123 : σ (.n 4123) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 74) (by norm_num)).2.2
  have v4355 : σ (.n 4355) = ev 45 := by
    rw [← hev 45 (by norm_num)]; exact (vt_eval h (k := 106) (by norm_num)).2.2
  have v4359 : σ (.n 4359) = ev 46 := by
    rw [← hev 46 (by norm_num)]; exact (vt_eval h (k := 107) (by norm_num)).2.2
  have v4376 : σ (.n 4376) = ev 47 := by
    rw [← hev 47 (by norm_num)]; exact (vt_eval h (k := 108) (by norm_num)).2.2
  have v4616 : σ (.n 4616) = ev 81 := by
    rw [← hev 81 (by norm_num)]; exact (vt_eval h (k := 142) (by norm_num)).2.2
  have hB : σ (.n 5619) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 9], 8)], [([81], 1), ([13, 81], 2), ([13, 81], 1)], [([46], 1), ([11, 46], 1), ([11, 45], 1)], [([47], 1), ([11, 47], 1), ([11, 46], 1)]] := by
    simp only [v4616, v4376, v4359, v4355, v4123, v4115, v4094, v4036, a5195, a5194, a5193, e5192, a5191,
      a5190, e5189, a5188, a5187, e5186, a5185, a5184, e5183, a5182, e5181, a4562, a4561,
      a4560, a4559, a4558, a4557, a4556, a4555, a4554, a4553, a4552, a4551, a4550, a4549,
      a4548, a4547, a4546, a4545, a4544, a4543, a4542, a4541]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5197, a5196, hB]

set_option maxRecDepth 10000 in
theorem vtB05_19 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5638) = σ (.n 5621) + σ (.n 1220) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 9], 16)], [([82], 1), ([13, 82], 2), ([13, 82], 1)], [([48], 1), ([11, 48], 1), ([11, 47], 1)], [([49], 1), ([11, 49], 1), ([11, 48], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4563 [
    .atom (.const (.n 4987) (word 2 0)),
    .atom (.const (.n 4988) (word 16 0)),
    .atom (.mul (.n 4989) (.n 4036) (.n 4094)),
    .atom (.mul (.n 4990) (.n 4988) (.n 4989)),
    .atom (.copy (.n 4991) (.n 4990)),
    .atom (.const (.n 4992) (word 2 0)),
    .atom (.mul (.n 4993) (.n 4123) (.n 4620)),
    .atom (.mul (.n 4994) (.n 4992) (.n 4993)),
    .atom (.add (.n 4995) (.n 4620) (.n 4994)),
    .atom (.mul (.n 4996) (.n 4123) (.n 4620)),
    .atom (.add (.n 4997) (.n 4995) (.n 4996)),
    .atom (.copy (.n 4998) (.n 4997)),
    .atom (.mul (.n 4999) (.n 4115) (.n 4380)),
    .atom (.add (.n 5000) (.n 4380) (.n 4999)),
    .atom (.mul (.n 5001) (.n 4115) (.n 4376)),
    .atom (.add (.n 5002) (.n 5000) (.n 5001)),
    .atom (.copy (.n 5003) (.n 5002)),
    .atom (.mul (.n 5004) (.n 4115) (.n 4384)),
    .atom (.add (.n 5005) (.n 4384) (.n 5004)),
    .atom (.mul (.n 5006) (.n 4115) (.n 4380)),
    .atom (.add (.n 5007) (.n 5005) (.n 5006)),
    .atom (.copy (.n 5008) (.n 5007))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4563, a4564, a4565, a4566, a4567, a4568, a4569, a4570, a4571, a4572, a4573, a4574, a4575, a4576,
    a4577, a4578, a4579, a4580, a4581, a4582, a4583, a4584, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5198 [
    .atom (.load (.n 5622) (.n 13) 0),
    .atom (.mul (.n 5623) (.n 5622) (.n 4987)),
    .atom (.load (.n 5624) (.n 13) 1),
    .atom (.mul (.n 5625) (.n 5624) (.n 4991)),
    .atom (.add (.n 5626) (.n 5623) (.n 5625)),
    .atom (.load (.n 5627) (.n 13) 2),
    .atom (.mul (.n 5628) (.n 5627) (.n 4998)),
    .atom (.add (.n 5629) (.n 5626) (.n 5628)),
    .atom (.load (.n 5630) (.n 13) 3),
    .atom (.mul (.n 5631) (.n 5630) (.n 5003)),
    .atom (.add (.n 5632) (.n 5629) (.n 5631)),
    .atom (.load (.n 5633) (.n 13) 4),
    .atom (.mul (.n 5634) (.n 5633) (.n 5008)),
    .atom (.add (.n 5635) (.n 5632) (.n 5634)),
    .atom (.add (.n 5636) (.n 14) (.n 5635)),
    .atom (.mul (.n 5637) (.n 1220) (.n 5636)),
    .atom (.add (.n 5638) (.n 5621) (.n 5637))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5198, a5199, a5200, a5201, a5202, a5203, a5204, a5205, a5206, a5207, a5208, a5209, a5210, a5211,
    a5212, a5213, a5214, -⟩ := hs1
  have e5198 := tb_loadHolds_unique a5198 (hw 0 (by norm_num))
  have e5200 := tb_loadHolds_unique a5200 (hw 1 (by norm_num))
  have e5203 := tb_loadHolds_unique a5203 (hw 2 (by norm_num))
  have e5206 := tb_loadHolds_unique a5206 (hw 3 (by norm_num))
  have e5209 := tb_loadHolds_unique a5209 (hw 4 (by norm_num))
  have v4036 : σ (.n 4036) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 62) (by norm_num)).2.2
  have v4094 : σ (.n 4094) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 70) (by norm_num)).2.2
  have v4115 : σ (.n 4115) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_eval h (k := 72) (by norm_num)).2.2
  have v4123 : σ (.n 4123) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 74) (by norm_num)).2.2
  have v4376 : σ (.n 4376) = ev 47 := by
    rw [← hev 47 (by norm_num)]; exact (vt_eval h (k := 108) (by norm_num)).2.2
  have v4380 : σ (.n 4380) = ev 48 := by
    rw [← hev 48 (by norm_num)]; exact (vt_eval h (k := 109) (by norm_num)).2.2
  have v4384 : σ (.n 4384) = ev 49 := by
    rw [← hev 49 (by norm_num)]; exact (vt_eval h (k := 110) (by norm_num)).2.2
  have v4620 : σ (.n 4620) = ev 82 := by
    rw [← hev 82 (by norm_num)]; exact (vt_eval h (k := 143) (by norm_num)).2.2
  have hB : σ (.n 5636) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 9], 16)], [([82], 1), ([13, 82], 2), ([13, 82], 1)], [([48], 1), ([11, 48], 1), ([11, 47], 1)], [([49], 1), ([11, 49], 1), ([11, 48], 1)]] := by
    simp only [v4620, v4384, v4380, v4376, v4123, v4115, v4094, v4036, a5212, a5211, a5210, e5209, a5208,
      a5207, e5206, a5205, a5204, e5203, a5202, a5201, e5200, a5199, e5198, a4584, a4583,
      a4582, a4581, a4580, a4579, a4578, a4577, a4576, a4575, a4574, a4573, a4572, a4571,
      a4570, a4569, a4568, a4567, a4566, a4565, a4564, a4563]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5214, a5213, hB]

set_option maxRecDepth 10000 in
theorem vtB05_20 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5655) = σ (.n 5638) + σ (.n 1229) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 9], 32)], [([83], 1), ([13, 83], 2), ([13, 83], 1)], [([50], 1), ([11, 50], 1), ([11, 49], 1)], [([51], 1), ([11, 51], 1), ([11, 50], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4585 [
    .atom (.const (.n 5009) (word 2 0)),
    .atom (.const (.n 5010) (word 32 0)),
    .atom (.mul (.n 5011) (.n 4036) (.n 4094)),
    .atom (.mul (.n 5012) (.n 5010) (.n 5011)),
    .atom (.copy (.n 5013) (.n 5012)),
    .atom (.const (.n 5014) (word 2 0)),
    .atom (.mul (.n 5015) (.n 4123) (.n 4637)),
    .atom (.mul (.n 5016) (.n 5014) (.n 5015)),
    .atom (.add (.n 5017) (.n 4637) (.n 5016)),
    .atom (.mul (.n 5018) (.n 4123) (.n 4637)),
    .atom (.add (.n 5019) (.n 5017) (.n 5018)),
    .atom (.copy (.n 5020) (.n 5019)),
    .atom (.mul (.n 5021) (.n 4115) (.n 4388)),
    .atom (.add (.n 5022) (.n 4388) (.n 5021)),
    .atom (.mul (.n 5023) (.n 4115) (.n 4384)),
    .atom (.add (.n 5024) (.n 5022) (.n 5023)),
    .atom (.copy (.n 5025) (.n 5024)),
    .atom (.mul (.n 5026) (.n 4115) (.n 4405)),
    .atom (.add (.n 5027) (.n 4405) (.n 5026)),
    .atom (.mul (.n 5028) (.n 4115) (.n 4388)),
    .atom (.add (.n 5029) (.n 5027) (.n 5028)),
    .atom (.copy (.n 5030) (.n 5029))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4585, a4586, a4587, a4588, a4589, a4590, a4591, a4592, a4593, a4594, a4595, a4596, a4597, a4598,
    a4599, a4600, a4601, a4602, a4603, a4604, a4605, a4606, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5215 [
    .atom (.load (.n 5639) (.n 13) 0),
    .atom (.mul (.n 5640) (.n 5639) (.n 5009)),
    .atom (.load (.n 5641) (.n 13) 1),
    .atom (.mul (.n 5642) (.n 5641) (.n 5013)),
    .atom (.add (.n 5643) (.n 5640) (.n 5642)),
    .atom (.load (.n 5644) (.n 13) 2),
    .atom (.mul (.n 5645) (.n 5644) (.n 5020)),
    .atom (.add (.n 5646) (.n 5643) (.n 5645)),
    .atom (.load (.n 5647) (.n 13) 3),
    .atom (.mul (.n 5648) (.n 5647) (.n 5025)),
    .atom (.add (.n 5649) (.n 5646) (.n 5648)),
    .atom (.load (.n 5650) (.n 13) 4),
    .atom (.mul (.n 5651) (.n 5650) (.n 5030)),
    .atom (.add (.n 5652) (.n 5649) (.n 5651)),
    .atom (.add (.n 5653) (.n 14) (.n 5652)),
    .atom (.mul (.n 5654) (.n 1229) (.n 5653)),
    .atom (.add (.n 5655) (.n 5638) (.n 5654))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5215, a5216, a5217, a5218, a5219, a5220, a5221, a5222, a5223, a5224, a5225, a5226, a5227, a5228,
    a5229, a5230, a5231, -⟩ := hs1
  have e5215 := tb_loadHolds_unique a5215 (hw 0 (by norm_num))
  have e5217 := tb_loadHolds_unique a5217 (hw 1 (by norm_num))
  have e5220 := tb_loadHolds_unique a5220 (hw 2 (by norm_num))
  have e5223 := tb_loadHolds_unique a5223 (hw 3 (by norm_num))
  have e5226 := tb_loadHolds_unique a5226 (hw 4 (by norm_num))
  have v4036 : σ (.n 4036) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 62) (by norm_num)).2.2
  have v4094 : σ (.n 4094) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 70) (by norm_num)).2.2
  have v4115 : σ (.n 4115) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_eval h (k := 72) (by norm_num)).2.2
  have v4123 : σ (.n 4123) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 74) (by norm_num)).2.2
  have v4384 : σ (.n 4384) = ev 49 := by
    rw [← hev 49 (by norm_num)]; exact (vt_eval h (k := 110) (by norm_num)).2.2
  have v4388 : σ (.n 4388) = ev 50 := by
    rw [← hev 50 (by norm_num)]; exact (vt_eval h (k := 111) (by norm_num)).2.2
  have v4405 : σ (.n 4405) = ev 51 := by
    rw [← hev 51 (by norm_num)]; exact (vt_eval h (k := 112) (by norm_num)).2.2
  have v4637 : σ (.n 4637) = ev 83 := by
    rw [← hev 83 (by norm_num)]; exact (vt_eval h (k := 144) (by norm_num)).2.2
  have hB : σ (.n 5653) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 9], 32)], [([83], 1), ([13, 83], 2), ([13, 83], 1)], [([50], 1), ([11, 50], 1), ([11, 49], 1)], [([51], 1), ([11, 51], 1), ([11, 50], 1)]] := by
    simp only [v4637, v4405, v4388, v4384, v4123, v4115, v4094, v4036, a5229, a5228, a5227, e5226, a5225,
      a5224, e5223, a5222, a5221, e5220, a5219, a5218, e5217, a5216, e5215, a4606, a4605,
      a4604, a4603, a4602, a4601, a4600, a4599, a4598, a4597, a4596, a4595, a4594, a4593,
      a4592, a4591, a4590, a4589, a4588, a4587, a4586, a4585]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5231, a5230, hB]

set_option maxRecDepth 10000 in
theorem vtB05_21 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5672) = σ (.n 5655) + σ (.n 1238) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 9], 64)], [([84], 1), ([13, 84], 2), ([13, 84], 1)], [([52], 1), ([11, 52], 1), ([11, 51], 1)], [([53], 1), ([11, 53], 1), ([11, 52], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4607 [
    .atom (.const (.n 5031) (word 2 0)),
    .atom (.const (.n 5032) (word 64 0)),
    .atom (.mul (.n 5033) (.n 4036) (.n 4094)),
    .atom (.mul (.n 5034) (.n 5032) (.n 5033)),
    .atom (.copy (.n 5035) (.n 5034)),
    .atom (.const (.n 5036) (word 2 0)),
    .atom (.mul (.n 5037) (.n 4123) (.n 4641)),
    .atom (.mul (.n 5038) (.n 5036) (.n 5037)),
    .atom (.add (.n 5039) (.n 4641) (.n 5038)),
    .atom (.mul (.n 5040) (.n 4123) (.n 4641)),
    .atom (.add (.n 5041) (.n 5039) (.n 5040)),
    .atom (.copy (.n 5042) (.n 5041)),
    .atom (.mul (.n 5043) (.n 4115) (.n 4409)),
    .atom (.add (.n 5044) (.n 4409) (.n 5043)),
    .atom (.mul (.n 5045) (.n 4115) (.n 4405)),
    .atom (.add (.n 5046) (.n 5044) (.n 5045)),
    .atom (.copy (.n 5047) (.n 5046)),
    .atom (.mul (.n 5048) (.n 4115) (.n 4413)),
    .atom (.add (.n 5049) (.n 4413) (.n 5048)),
    .atom (.mul (.n 5050) (.n 4115) (.n 4409)),
    .atom (.add (.n 5051) (.n 5049) (.n 5050)),
    .atom (.copy (.n 5052) (.n 5051))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4607, a4608, a4609, a4610, a4611, a4612, a4613, a4614, a4615, a4616, a4617, a4618, a4619, a4620,
    a4621, a4622, a4623, a4624, a4625, a4626, a4627, a4628, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5232 [
    .atom (.load (.n 5656) (.n 13) 0),
    .atom (.mul (.n 5657) (.n 5656) (.n 5031)),
    .atom (.load (.n 5658) (.n 13) 1),
    .atom (.mul (.n 5659) (.n 5658) (.n 5035)),
    .atom (.add (.n 5660) (.n 5657) (.n 5659)),
    .atom (.load (.n 5661) (.n 13) 2),
    .atom (.mul (.n 5662) (.n 5661) (.n 5042)),
    .atom (.add (.n 5663) (.n 5660) (.n 5662)),
    .atom (.load (.n 5664) (.n 13) 3),
    .atom (.mul (.n 5665) (.n 5664) (.n 5047)),
    .atom (.add (.n 5666) (.n 5663) (.n 5665)),
    .atom (.load (.n 5667) (.n 13) 4),
    .atom (.mul (.n 5668) (.n 5667) (.n 5052)),
    .atom (.add (.n 5669) (.n 5666) (.n 5668)),
    .atom (.add (.n 5670) (.n 14) (.n 5669)),
    .atom (.mul (.n 5671) (.n 1238) (.n 5670)),
    .atom (.add (.n 5672) (.n 5655) (.n 5671))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5232, a5233, a5234, a5235, a5236, a5237, a5238, a5239, a5240, a5241, a5242, a5243, a5244, a5245,
    a5246, a5247, a5248, -⟩ := hs1
  have e5232 := tb_loadHolds_unique a5232 (hw 0 (by norm_num))
  have e5234 := tb_loadHolds_unique a5234 (hw 1 (by norm_num))
  have e5237 := tb_loadHolds_unique a5237 (hw 2 (by norm_num))
  have e5240 := tb_loadHolds_unique a5240 (hw 3 (by norm_num))
  have e5243 := tb_loadHolds_unique a5243 (hw 4 (by norm_num))
  have v4036 : σ (.n 4036) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 62) (by norm_num)).2.2
  have v4094 : σ (.n 4094) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 70) (by norm_num)).2.2
  have v4115 : σ (.n 4115) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_eval h (k := 72) (by norm_num)).2.2
  have v4123 : σ (.n 4123) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 74) (by norm_num)).2.2
  have v4405 : σ (.n 4405) = ev 51 := by
    rw [← hev 51 (by norm_num)]; exact (vt_eval h (k := 112) (by norm_num)).2.2
  have v4409 : σ (.n 4409) = ev 52 := by
    rw [← hev 52 (by norm_num)]; exact (vt_eval h (k := 113) (by norm_num)).2.2
  have v4413 : σ (.n 4413) = ev 53 := by
    rw [← hev 53 (by norm_num)]; exact (vt_eval h (k := 114) (by norm_num)).2.2
  have v4641 : σ (.n 4641) = ev 84 := by
    rw [← hev 84 (by norm_num)]; exact (vt_eval h (k := 145) (by norm_num)).2.2
  have hB : σ (.n 5670) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 9], 64)], [([84], 1), ([13, 84], 2), ([13, 84], 1)], [([52], 1), ([11, 52], 1), ([11, 51], 1)], [([53], 1), ([11, 53], 1), ([11, 52], 1)]] := by
    simp only [v4641, v4413, v4409, v4405, v4123, v4115, v4094, v4036, a5246, a5245, a5244, e5243, a5242,
      a5241, e5240, a5239, a5238, e5237, a5236, a5235, e5234, a5233, e5232, a4628, a4627,
      a4626, a4625, a4624, a4623, a4622, a4621, a4620, a4619, a4618, a4617, a4616, a4615,
      a4614, a4613, a4612, a4611, a4610, a4609, a4608, a4607]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5248, a5247, hB]

set_option maxRecDepth 10000 in
theorem vtB05_22 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5689) = σ (.n 5672) + σ (.n 1247) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 9], 128)], [([85], 1), ([13, 85], 2), ([13, 85], 1)], [([54], 1), ([11, 54], 1), ([11, 53], 1)], [([55], 1), ([11, 55], 1), ([11, 54], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4629 [
    .atom (.const (.n 5053) (word 2 0)),
    .atom (.const (.n 5054) (word 128 0)),
    .atom (.mul (.n 5055) (.n 4036) (.n 4094)),
    .atom (.mul (.n 5056) (.n 5054) (.n 5055)),
    .atom (.copy (.n 5057) (.n 5056)),
    .atom (.const (.n 5058) (word 2 0)),
    .atom (.mul (.n 5059) (.n 4123) (.n 4645)),
    .atom (.mul (.n 5060) (.n 5058) (.n 5059)),
    .atom (.add (.n 5061) (.n 4645) (.n 5060)),
    .atom (.mul (.n 5062) (.n 4123) (.n 4645)),
    .atom (.add (.n 5063) (.n 5061) (.n 5062)),
    .atom (.copy (.n 5064) (.n 5063)),
    .atom (.mul (.n 5065) (.n 4115) (.n 4417)),
    .atom (.add (.n 5066) (.n 4417) (.n 5065)),
    .atom (.mul (.n 5067) (.n 4115) (.n 4413)),
    .atom (.add (.n 5068) (.n 5066) (.n 5067)),
    .atom (.copy (.n 5069) (.n 5068)),
    .atom (.mul (.n 5070) (.n 4115) (.n 4434)),
    .atom (.add (.n 5071) (.n 4434) (.n 5070)),
    .atom (.mul (.n 5072) (.n 4115) (.n 4417)),
    .atom (.add (.n 5073) (.n 5071) (.n 5072)),
    .atom (.copy (.n 5074) (.n 5073))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4629, a4630, a4631, a4632, a4633, a4634, a4635, a4636, a4637, a4638, a4639, a4640, a4641, a4642,
    a4643, a4644, a4645, a4646, a4647, a4648, a4649, a4650, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5249 [
    .atom (.load (.n 5673) (.n 13) 0),
    .atom (.mul (.n 5674) (.n 5673) (.n 5053)),
    .atom (.load (.n 5675) (.n 13) 1),
    .atom (.mul (.n 5676) (.n 5675) (.n 5057)),
    .atom (.add (.n 5677) (.n 5674) (.n 5676)),
    .atom (.load (.n 5678) (.n 13) 2),
    .atom (.mul (.n 5679) (.n 5678) (.n 5064)),
    .atom (.add (.n 5680) (.n 5677) (.n 5679)),
    .atom (.load (.n 5681) (.n 13) 3),
    .atom (.mul (.n 5682) (.n 5681) (.n 5069)),
    .atom (.add (.n 5683) (.n 5680) (.n 5682)),
    .atom (.load (.n 5684) (.n 13) 4),
    .atom (.mul (.n 5685) (.n 5684) (.n 5074)),
    .atom (.add (.n 5686) (.n 5683) (.n 5685)),
    .atom (.add (.n 5687) (.n 14) (.n 5686)),
    .atom (.mul (.n 5688) (.n 1247) (.n 5687)),
    .atom (.add (.n 5689) (.n 5672) (.n 5688))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5249, a5250, a5251, a5252, a5253, a5254, a5255, a5256, a5257, a5258, a5259, a5260, a5261, a5262,
    a5263, a5264, a5265, -⟩ := hs1
  have e5249 := tb_loadHolds_unique a5249 (hw 0 (by norm_num))
  have e5251 := tb_loadHolds_unique a5251 (hw 1 (by norm_num))
  have e5254 := tb_loadHolds_unique a5254 (hw 2 (by norm_num))
  have e5257 := tb_loadHolds_unique a5257 (hw 3 (by norm_num))
  have e5260 := tb_loadHolds_unique a5260 (hw 4 (by norm_num))
  have v4036 : σ (.n 4036) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 62) (by norm_num)).2.2
  have v4094 : σ (.n 4094) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 70) (by norm_num)).2.2
  have v4115 : σ (.n 4115) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_eval h (k := 72) (by norm_num)).2.2
  have v4123 : σ (.n 4123) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 74) (by norm_num)).2.2
  have v4413 : σ (.n 4413) = ev 53 := by
    rw [← hev 53 (by norm_num)]; exact (vt_eval h (k := 114) (by norm_num)).2.2
  have v4417 : σ (.n 4417) = ev 54 := by
    rw [← hev 54 (by norm_num)]; exact (vt_eval h (k := 115) (by norm_num)).2.2
  have v4434 : σ (.n 4434) = ev 55 := by
    rw [← hev 55 (by norm_num)]; exact (vt_eval h (k := 116) (by norm_num)).2.2
  have v4645 : σ (.n 4645) = ev 85 := by
    rw [← hev 85 (by norm_num)]; exact (vt_eval h (k := 146) (by norm_num)).2.2
  have hB : σ (.n 5687) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 9], 128)], [([85], 1), ([13, 85], 2), ([13, 85], 1)], [([54], 1), ([11, 54], 1), ([11, 53], 1)], [([55], 1), ([11, 55], 1), ([11, 54], 1)]] := by
    simp only [v4645, v4434, v4417, v4413, v4123, v4115, v4094, v4036, a5263, a5262, a5261, e5260, a5259,
      a5258, e5257, a5256, a5255, e5254, a5253, a5252, e5251, a5250, e5249, a4650, a4649,
      a4648, a4647, a4646, a4645, a4644, a4643, a4642, a4641, a4640, a4639, a4638, a4637,
      a4636, a4635, a4634, a4633, a4632, a4631, a4630, a4629]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5265, a5264, hB]

set_option maxRecDepth 10000 in
theorem vtB05_23 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5706) = σ (.n 5689) + σ (.n 1256) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 9], 256)], [([86], 1), ([13, 86], 2), ([13, 86], 1)], [([56], 1), ([11, 56], 1), ([11, 55], 1)], [([11, 56], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4651 [
    .atom (.const (.n 5075) (word 2 0)),
    .atom (.const (.n 5076) (word 256 0)),
    .atom (.mul (.n 5077) (.n 4036) (.n 4094)),
    .atom (.mul (.n 5078) (.n 5076) (.n 5077)),
    .atom (.copy (.n 5079) (.n 5078)),
    .atom (.const (.n 5080) (word 2 0)),
    .atom (.mul (.n 5081) (.n 4123) (.n 4649)),
    .atom (.mul (.n 5082) (.n 5080) (.n 5081)),
    .atom (.add (.n 5083) (.n 4649) (.n 5082)),
    .atom (.mul (.n 5084) (.n 4123) (.n 4649)),
    .atom (.add (.n 5085) (.n 5083) (.n 5084)),
    .atom (.copy (.n 5086) (.n 5085)),
    .atom (.mul (.n 5087) (.n 4115) (.n 4438)),
    .atom (.add (.n 5088) (.n 4438) (.n 5087)),
    .atom (.mul (.n 5089) (.n 4115) (.n 4434)),
    .atom (.add (.n 5090) (.n 5088) (.n 5089)),
    .atom (.copy (.n 5091) (.n 5090)),
    .atom (.mul (.n 5092) (.n 4115) (.n 4438)),
    .atom (.copy (.n 5093) (.n 5092))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4651, a4652, a4653, a4654, a4655, a4656, a4657, a4658, a4659, a4660, a4661, a4662, a4663, a4664,
    a4665, a4666, a4667, a4668, a4669, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5266 [
    .atom (.load (.n 5690) (.n 13) 0),
    .atom (.mul (.n 5691) (.n 5690) (.n 5075)),
    .atom (.load (.n 5692) (.n 13) 1),
    .atom (.mul (.n 5693) (.n 5692) (.n 5079)),
    .atom (.add (.n 5694) (.n 5691) (.n 5693)),
    .atom (.load (.n 5695) (.n 13) 2),
    .atom (.mul (.n 5696) (.n 5695) (.n 5086)),
    .atom (.add (.n 5697) (.n 5694) (.n 5696)),
    .atom (.load (.n 5698) (.n 13) 3),
    .atom (.mul (.n 5699) (.n 5698) (.n 5091)),
    .atom (.add (.n 5700) (.n 5697) (.n 5699)),
    .atom (.load (.n 5701) (.n 13) 4),
    .atom (.mul (.n 5702) (.n 5701) (.n 5093)),
    .atom (.add (.n 5703) (.n 5700) (.n 5702)),
    .atom (.add (.n 5704) (.n 14) (.n 5703)),
    .atom (.mul (.n 5705) (.n 1256) (.n 5704)),
    .atom (.add (.n 5706) (.n 5689) (.n 5705))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5266, a5267, a5268, a5269, a5270, a5271, a5272, a5273, a5274, a5275, a5276, a5277, a5278, a5279,
    a5280, a5281, a5282, -⟩ := hs1
  have e5266 := tb_loadHolds_unique a5266 (hw 0 (by norm_num))
  have e5268 := tb_loadHolds_unique a5268 (hw 1 (by norm_num))
  have e5271 := tb_loadHolds_unique a5271 (hw 2 (by norm_num))
  have e5274 := tb_loadHolds_unique a5274 (hw 3 (by norm_num))
  have e5277 := tb_loadHolds_unique a5277 (hw 4 (by norm_num))
  have v4036 : σ (.n 4036) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 62) (by norm_num)).2.2
  have v4094 : σ (.n 4094) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 70) (by norm_num)).2.2
  have v4115 : σ (.n 4115) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_eval h (k := 72) (by norm_num)).2.2
  have v4123 : σ (.n 4123) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 74) (by norm_num)).2.2
  have v4434 : σ (.n 4434) = ev 55 := by
    rw [← hev 55 (by norm_num)]; exact (vt_eval h (k := 116) (by norm_num)).2.2
  have v4438 : σ (.n 4438) = ev 56 := by
    rw [← hev 56 (by norm_num)]; exact (vt_eval h (k := 117) (by norm_num)).2.2
  have v4649 : σ (.n 4649) = ev 86 := by
    rw [← hev 86 (by norm_num)]; exact (vt_eval h (k := 147) (by norm_num)).2.2
  have hB : σ (.n 5704) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 9], 256)], [([86], 1), ([13, 86], 2), ([13, 86], 1)], [([56], 1), ([11, 56], 1), ([11, 55], 1)], [([11, 56], 1)]] := by
    simp only [v4649, v4438, v4434, v4123, v4115, v4094, v4036, a5280, a5279, a5278, e5277, a5276, a5275,
      e5274, a5273, a5272, e5271, a5270, a5269, e5268, a5267, e5266, a4669, a4668, a4667,
      a4666, a4665, a4664, a4663, a4662, a4661, a4660, a4659, a4658, a4657, a4656, a4655,
      a4654, a4653, a4652, a4651]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5282, a5281, hB]

set_option maxRecDepth 10000 in
theorem vtB05_24 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5723) = σ (.n 5706) + σ (.n 1265) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 9], 512)], [([87], 1), ([13, 87], 2), ([13, 87], 1)], [([57], 1)], [([58], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4670 [
    .atom (.const (.n 5094) (word 2 0)),
    .atom (.const (.n 5095) (word 512 0)),
    .atom (.mul (.n 5096) (.n 4036) (.n 4094)),
    .atom (.mul (.n 5097) (.n 5095) (.n 5096)),
    .atom (.copy (.n 5098) (.n 5097)),
    .atom (.const (.n 5099) (word 2 0)),
    .atom (.mul (.n 5100) (.n 4123) (.n 4666)),
    .atom (.mul (.n 5101) (.n 5099) (.n 5100)),
    .atom (.add (.n 5102) (.n 4666) (.n 5101)),
    .atom (.mul (.n 5103) (.n 4123) (.n 4666)),
    .atom (.add (.n 5104) (.n 5102) (.n 5103)),
    .atom (.copy (.n 5105) (.n 5104)),
    .atom (.copy (.n 5106) (.n 4442)),
    .atom (.copy (.n 5107) (.n 4446))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4670, a4671, a4672, a4673, a4674, a4675, a4676, a4677, a4678, a4679, a4680, a4681, a4682, a4683,
    -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5283 [
    .atom (.load (.n 5707) (.n 13) 0),
    .atom (.mul (.n 5708) (.n 5707) (.n 5094)),
    .atom (.load (.n 5709) (.n 13) 1),
    .atom (.mul (.n 5710) (.n 5709) (.n 5098)),
    .atom (.add (.n 5711) (.n 5708) (.n 5710)),
    .atom (.load (.n 5712) (.n 13) 2),
    .atom (.mul (.n 5713) (.n 5712) (.n 5105)),
    .atom (.add (.n 5714) (.n 5711) (.n 5713)),
    .atom (.load (.n 5715) (.n 13) 3),
    .atom (.mul (.n 5716) (.n 5715) (.n 5106)),
    .atom (.add (.n 5717) (.n 5714) (.n 5716)),
    .atom (.load (.n 5718) (.n 13) 4),
    .atom (.mul (.n 5719) (.n 5718) (.n 5107)),
    .atom (.add (.n 5720) (.n 5717) (.n 5719)),
    .atom (.add (.n 5721) (.n 14) (.n 5720)),
    .atom (.mul (.n 5722) (.n 1265) (.n 5721)),
    .atom (.add (.n 5723) (.n 5706) (.n 5722))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5283, a5284, a5285, a5286, a5287, a5288, a5289, a5290, a5291, a5292, a5293, a5294, a5295, a5296,
    a5297, a5298, a5299, -⟩ := hs1
  have e5283 := tb_loadHolds_unique a5283 (hw 0 (by norm_num))
  have e5285 := tb_loadHolds_unique a5285 (hw 1 (by norm_num))
  have e5288 := tb_loadHolds_unique a5288 (hw 2 (by norm_num))
  have e5291 := tb_loadHolds_unique a5291 (hw 3 (by norm_num))
  have e5294 := tb_loadHolds_unique a5294 (hw 4 (by norm_num))
  have v4036 : σ (.n 4036) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 62) (by norm_num)).2.2
  have v4094 : σ (.n 4094) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 70) (by norm_num)).2.2
  have v4123 : σ (.n 4123) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 74) (by norm_num)).2.2
  have v4442 : σ (.n 4442) = ev 57 := by
    rw [← hev 57 (by norm_num)]; exact (vt_eval h (k := 118) (by norm_num)).2.2
  have v4446 : σ (.n 4446) = ev 58 := by
    rw [← hev 58 (by norm_num)]; exact (vt_eval h (k := 119) (by norm_num)).2.2
  have v4666 : σ (.n 4666) = ev 87 := by
    rw [← hev 87 (by norm_num)]; exact (vt_eval h (k := 148) (by norm_num)).2.2
  have hB : σ (.n 5721) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 9], 512)], [([87], 1), ([13, 87], 2), ([13, 87], 1)], [([57], 1)], [([58], 1)]] := by
    simp only [v4666, v4446, v4442, v4123, v4094, v4036, a5297, a5296, a5295, e5294, a5293, a5292, e5291,
      a5290, a5289, e5288, a5287, a5286, e5285, a5284, e5283, a4683, a4682, a4681, a4680,
      a4679, a4678, a4677, a4676, a4675, a4674, a4673, a4672, a4671, a4670]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5299, a5298, hB]

set_option maxRecDepth 10000 in
theorem vtB05_25 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5740) = σ (.n 5723) + σ (.n 1274) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 9], 1024)], [([88], 1), ([13, 88], 2), ([13, 88], 1)], [([59], 1)], [([60], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4684 [
    .atom (.const (.n 5108) (word 2 0)),
    .atom (.const (.n 5109) (word 1024 0)),
    .atom (.mul (.n 5110) (.n 4036) (.n 4094)),
    .atom (.mul (.n 5111) (.n 5109) (.n 5110)),
    .atom (.copy (.n 5112) (.n 5111)),
    .atom (.const (.n 5113) (word 2 0)),
    .atom (.mul (.n 5114) (.n 4123) (.n 4670)),
    .atom (.mul (.n 5115) (.n 5113) (.n 5114)),
    .atom (.add (.n 5116) (.n 4670) (.n 5115)),
    .atom (.mul (.n 5117) (.n 4123) (.n 4670)),
    .atom (.add (.n 5118) (.n 5116) (.n 5117)),
    .atom (.copy (.n 5119) (.n 5118)),
    .atom (.copy (.n 5120) (.n 4463)),
    .atom (.copy (.n 5121) (.n 4467))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4684, a4685, a4686, a4687, a4688, a4689, a4690, a4691, a4692, a4693, a4694, a4695, a4696, a4697,
    -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5300 [
    .atom (.load (.n 5724) (.n 13) 0),
    .atom (.mul (.n 5725) (.n 5724) (.n 5108)),
    .atom (.load (.n 5726) (.n 13) 1),
    .atom (.mul (.n 5727) (.n 5726) (.n 5112)),
    .atom (.add (.n 5728) (.n 5725) (.n 5727)),
    .atom (.load (.n 5729) (.n 13) 2),
    .atom (.mul (.n 5730) (.n 5729) (.n 5119)),
    .atom (.add (.n 5731) (.n 5728) (.n 5730)),
    .atom (.load (.n 5732) (.n 13) 3),
    .atom (.mul (.n 5733) (.n 5732) (.n 5120)),
    .atom (.add (.n 5734) (.n 5731) (.n 5733)),
    .atom (.load (.n 5735) (.n 13) 4),
    .atom (.mul (.n 5736) (.n 5735) (.n 5121)),
    .atom (.add (.n 5737) (.n 5734) (.n 5736)),
    .atom (.add (.n 5738) (.n 14) (.n 5737)),
    .atom (.mul (.n 5739) (.n 1274) (.n 5738)),
    .atom (.add (.n 5740) (.n 5723) (.n 5739))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5300, a5301, a5302, a5303, a5304, a5305, a5306, a5307, a5308, a5309, a5310, a5311, a5312, a5313,
    a5314, a5315, a5316, -⟩ := hs1
  have e5300 := tb_loadHolds_unique a5300 (hw 0 (by norm_num))
  have e5302 := tb_loadHolds_unique a5302 (hw 1 (by norm_num))
  have e5305 := tb_loadHolds_unique a5305 (hw 2 (by norm_num))
  have e5308 := tb_loadHolds_unique a5308 (hw 3 (by norm_num))
  have e5311 := tb_loadHolds_unique a5311 (hw 4 (by norm_num))
  have v4036 : σ (.n 4036) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 62) (by norm_num)).2.2
  have v4094 : σ (.n 4094) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 70) (by norm_num)).2.2
  have v4123 : σ (.n 4123) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 74) (by norm_num)).2.2
  have v4463 : σ (.n 4463) = ev 59 := by
    rw [← hev 59 (by norm_num)]; exact (vt_eval h (k := 120) (by norm_num)).2.2
  have v4467 : σ (.n 4467) = ev 60 := by
    rw [← hev 60 (by norm_num)]; exact (vt_eval h (k := 121) (by norm_num)).2.2
  have v4670 : σ (.n 4670) = ev 88 := by
    rw [← hev 88 (by norm_num)]; exact (vt_eval h (k := 149) (by norm_num)).2.2
  have hB : σ (.n 5738) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 9], 1024)], [([88], 1), ([13, 88], 2), ([13, 88], 1)], [([59], 1)], [([60], 1)]] := by
    simp only [v4670, v4467, v4463, v4123, v4094, v4036, a5314, a5313, a5312, e5311, a5310, a5309, e5308,
      a5307, a5306, e5305, a5304, a5303, e5302, a5301, e5300, a4697, a4696, a4695, a4694,
      a4693, a4692, a4691, a4690, a4689, a4688, a4687, a4686, a4685, a4684]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5316, a5315, hB]

set_option maxRecDepth 10000 in
theorem vtB05_26 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5757) = σ (.n 5740) + σ (.n 1283) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 9], 2048)], [([89], 1), ([13, 89], 2), ([13, 89], 1)], [([61], 1)], [([62], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4698 [
    .atom (.const (.n 5122) (word 2 0)),
    .atom (.const (.n 5123) (word 2048 0)),
    .atom (.mul (.n 5124) (.n 4036) (.n 4094)),
    .atom (.mul (.n 5125) (.n 5123) (.n 5124)),
    .atom (.copy (.n 5126) (.n 5125)),
    .atom (.const (.n 5127) (word 2 0)),
    .atom (.mul (.n 5128) (.n 4123) (.n 4674)),
    .atom (.mul (.n 5129) (.n 5127) (.n 5128)),
    .atom (.add (.n 5130) (.n 4674) (.n 5129)),
    .atom (.mul (.n 5131) (.n 4123) (.n 4674)),
    .atom (.add (.n 5132) (.n 5130) (.n 5131)),
    .atom (.copy (.n 5133) (.n 5132)),
    .atom (.copy (.n 5134) (.n 4471)),
    .atom (.copy (.n 5135) (.n 4475))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4698, a4699, a4700, a4701, a4702, a4703, a4704, a4705, a4706, a4707, a4708, a4709, a4710, a4711,
    -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5317 [
    .atom (.load (.n 5741) (.n 13) 0),
    .atom (.mul (.n 5742) (.n 5741) (.n 5122)),
    .atom (.load (.n 5743) (.n 13) 1),
    .atom (.mul (.n 5744) (.n 5743) (.n 5126)),
    .atom (.add (.n 5745) (.n 5742) (.n 5744)),
    .atom (.load (.n 5746) (.n 13) 2),
    .atom (.mul (.n 5747) (.n 5746) (.n 5133)),
    .atom (.add (.n 5748) (.n 5745) (.n 5747)),
    .atom (.load (.n 5749) (.n 13) 3),
    .atom (.mul (.n 5750) (.n 5749) (.n 5134)),
    .atom (.add (.n 5751) (.n 5748) (.n 5750)),
    .atom (.load (.n 5752) (.n 13) 4),
    .atom (.mul (.n 5753) (.n 5752) (.n 5135)),
    .atom (.add (.n 5754) (.n 5751) (.n 5753)),
    .atom (.add (.n 5755) (.n 14) (.n 5754)),
    .atom (.mul (.n 5756) (.n 1283) (.n 5755)),
    .atom (.add (.n 5757) (.n 5740) (.n 5756))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5317, a5318, a5319, a5320, a5321, a5322, a5323, a5324, a5325, a5326, a5327, a5328, a5329, a5330,
    a5331, a5332, a5333, -⟩ := hs1
  have e5317 := tb_loadHolds_unique a5317 (hw 0 (by norm_num))
  have e5319 := tb_loadHolds_unique a5319 (hw 1 (by norm_num))
  have e5322 := tb_loadHolds_unique a5322 (hw 2 (by norm_num))
  have e5325 := tb_loadHolds_unique a5325 (hw 3 (by norm_num))
  have e5328 := tb_loadHolds_unique a5328 (hw 4 (by norm_num))
  have v4036 : σ (.n 4036) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 62) (by norm_num)).2.2
  have v4094 : σ (.n 4094) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 70) (by norm_num)).2.2
  have v4123 : σ (.n 4123) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 74) (by norm_num)).2.2
  have v4471 : σ (.n 4471) = ev 61 := by
    rw [← hev 61 (by norm_num)]; exact (vt_eval h (k := 122) (by norm_num)).2.2
  have v4475 : σ (.n 4475) = ev 62 := by
    rw [← hev 62 (by norm_num)]; exact (vt_eval h (k := 123) (by norm_num)).2.2
  have v4674 : σ (.n 4674) = ev 89 := by
    rw [← hev 89 (by norm_num)]; exact (vt_eval h (k := 150) (by norm_num)).2.2
  have hB : σ (.n 5755) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 9], 2048)], [([89], 1), ([13, 89], 2), ([13, 89], 1)], [([61], 1)], [([62], 1)]] := by
    simp only [v4674, v4475, v4471, v4123, v4094, v4036, a5331, a5330, a5329, e5328, a5327, a5326, e5325,
      a5324, a5323, e5322, a5321, a5320, e5319, a5318, e5317, a4711, a4710, a4709, a4708,
      a4707, a4706, a4705, a4704, a4703, a4702, a4701, a4700, a4699, a4698]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5333, a5332, hB]

set_option maxRecDepth 10000 in
theorem vtB05_27 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5774) = σ (.n 5757) + σ (.n 1292) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 9], 4096)], [([90], 1), ([13, 90], 2), ([13, 90], 1)], [([63], 1)], [([64], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4712 [
    .atom (.const (.n 5136) (word 2 0)),
    .atom (.const (.n 5137) (word 4096 0)),
    .atom (.mul (.n 5138) (.n 4036) (.n 4094)),
    .atom (.mul (.n 5139) (.n 5137) (.n 5138)),
    .atom (.copy (.n 5140) (.n 5139)),
    .atom (.const (.n 5141) (word 2 0)),
    .atom (.mul (.n 5142) (.n 4123) (.n 4678)),
    .atom (.mul (.n 5143) (.n 5141) (.n 5142)),
    .atom (.add (.n 5144) (.n 4678) (.n 5143)),
    .atom (.mul (.n 5145) (.n 4123) (.n 4678)),
    .atom (.add (.n 5146) (.n 5144) (.n 5145)),
    .atom (.copy (.n 5147) (.n 5146)),
    .atom (.copy (.n 5148) (.n 4492)),
    .atom (.copy (.n 5149) (.n 4496))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4712, a4713, a4714, a4715, a4716, a4717, a4718, a4719, a4720, a4721, a4722, a4723, a4724, a4725,
    -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5334 [
    .atom (.load (.n 5758) (.n 13) 0),
    .atom (.mul (.n 5759) (.n 5758) (.n 5136)),
    .atom (.load (.n 5760) (.n 13) 1),
    .atom (.mul (.n 5761) (.n 5760) (.n 5140)),
    .atom (.add (.n 5762) (.n 5759) (.n 5761)),
    .atom (.load (.n 5763) (.n 13) 2),
    .atom (.mul (.n 5764) (.n 5763) (.n 5147)),
    .atom (.add (.n 5765) (.n 5762) (.n 5764)),
    .atom (.load (.n 5766) (.n 13) 3),
    .atom (.mul (.n 5767) (.n 5766) (.n 5148)),
    .atom (.add (.n 5768) (.n 5765) (.n 5767)),
    .atom (.load (.n 5769) (.n 13) 4),
    .atom (.mul (.n 5770) (.n 5769) (.n 5149)),
    .atom (.add (.n 5771) (.n 5768) (.n 5770)),
    .atom (.add (.n 5772) (.n 14) (.n 5771)),
    .atom (.mul (.n 5773) (.n 1292) (.n 5772)),
    .atom (.add (.n 5774) (.n 5757) (.n 5773))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5334, a5335, a5336, a5337, a5338, a5339, a5340, a5341, a5342, a5343, a5344, a5345, a5346, a5347,
    a5348, a5349, a5350, -⟩ := hs1
  have e5334 := tb_loadHolds_unique a5334 (hw 0 (by norm_num))
  have e5336 := tb_loadHolds_unique a5336 (hw 1 (by norm_num))
  have e5339 := tb_loadHolds_unique a5339 (hw 2 (by norm_num))
  have e5342 := tb_loadHolds_unique a5342 (hw 3 (by norm_num))
  have e5345 := tb_loadHolds_unique a5345 (hw 4 (by norm_num))
  have v4036 : σ (.n 4036) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 62) (by norm_num)).2.2
  have v4094 : σ (.n 4094) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 70) (by norm_num)).2.2
  have v4123 : σ (.n 4123) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 74) (by norm_num)).2.2
  have v4492 : σ (.n 4492) = ev 63 := by
    rw [← hev 63 (by norm_num)]; exact (vt_eval h (k := 124) (by norm_num)).2.2
  have v4496 : σ (.n 4496) = ev 64 := by
    rw [← hev 64 (by norm_num)]; exact (vt_eval h (k := 125) (by norm_num)).2.2
  have v4678 : σ (.n 4678) = ev 90 := by
    rw [← hev 90 (by norm_num)]; exact (vt_eval h (k := 151) (by norm_num)).2.2
  have hB : σ (.n 5772) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 9], 4096)], [([90], 1), ([13, 90], 2), ([13, 90], 1)], [([63], 1)], [([64], 1)]] := by
    simp only [v4678, v4496, v4492, v4123, v4094, v4036, a5348, a5347, a5346, e5345, a5344, a5343, e5342,
      a5341, a5340, e5339, a5338, a5337, e5336, a5335, e5334, a4725, a4724, a4723, a4722,
      a4721, a4720, a4719, a4718, a4717, a4716, a4715, a4714, a4713, a4712]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5350, a5349, hB]

end
end LeanVM.Guest.B1.Tables
