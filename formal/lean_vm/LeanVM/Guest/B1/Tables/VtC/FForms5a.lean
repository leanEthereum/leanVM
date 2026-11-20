/-
  LeanVM.Guest.B1.Tables.VtC.FForms5a

  `Vt/FormsT5a.lean` on the window `VtF` (generated: scripts/b1c-vt/gentwins.py).

  Do not edit: `scripts/b1c-vt/all.py` writes it (`regen-guest.sh`, step `vt`).
-/

module

public import LeanVM.Guest.B1.Tables.VtC.FEvals
public import LeanVM.Guest.B1.Tables.Vt.FormsT5a

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

set_option maxRecDepth 10000 in
theorem vtB05_0F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5278) = σ (.n 1049) * vtBlockVal (σ (.n 14)) W ev
      [[([], 1)], [([0], 2)], [([1], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4267 [
    .atom (.const (.n 4692) (word 1 0)),
    .atom (.const (.n 4693) (word 2 0)),
    .atom (.mul (.n 4694) (.n 4693) (.n 4028)),
    .atom (.copy (.n 4695) (.n 4694)),
    .atom (.copy (.n 4696) (.n 4032))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4267, a4268, a4269, a4270, a4271, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 4844 [
    .atom (.load (.n 5269) (.n 13) 0),
    .atom (.mul (.n 5270) (.n 5269) (.n 4692)),
    .atom (.load (.n 5271) (.n 13) 1),
    .atom (.mul (.n 5272) (.n 5271) (.n 4695)),
    .atom (.add (.n 5273) (.n 5270) (.n 5272)),
    .atom (.load (.n 5274) (.n 13) 2),
    .atom (.mul (.n 5275) (.n 5274) (.n 4696)),
    .atom (.add (.n 5276) (.n 5273) (.n 5275)),
    .atom (.add (.n 5277) (.n 14) (.n 5276)),
    .atom (.mul (.n 5278) (.n 1049) (.n 5277))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a4844, a4845, a4846, a4847, a4848, a4849, a4850, a4851, a4852, a4853, -⟩ := hs1
  have e4844 := tb_loadHolds_unique a4844 (hw 0 (by norm_num))
  have e4846 := tb_loadHolds_unique a4846 (hw 1 (by norm_num))
  have e4849 := tb_loadHolds_unique a4849 (hw 2 (by norm_num))
  have v4028 : σ (.n 4028) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_evalF h (k := 61) (by norm_num)).2.2
  have v4032 : σ (.n 4032) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 62) (by norm_num)).2.2
  have hB : σ (.n 5277) = vtBlockVal (σ (.n 14)) W ev [[([], 1)], [([0], 2)], [([1], 1)]] := by
    simp only [v4032, v4028, a4852, a4851, a4850, e4849, a4848, a4847, e4846, a4845, e4844, a4271, a4270,
      a4269, a4268, a4267]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a4853, hB]

set_option maxRecDepth 10000 in
theorem vtB05_1F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5328) = σ (.n 5278) + σ (.n 1058) * vtBlockVal (σ (.n 14)) W ev
      [[([], 4)], [([0], 1)], [([91], 2)], [([], 32)], [([2], 1)], [([3], 1)], [([4], 1)], [([5], 1)], [([6], 1)], [([7], 1)], [([8], 1)], [([9], 1)], [([10], 1)], [([11], 1)], [([12], 1)], [([13], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4272 [
    .atom (.const (.n 4697) (word 4 0)),
    .atom (.copy (.n 4698) (.n 4028)),
    .atom (.const (.n 4699) (word 2 0)),
    .atom (.mul (.n 4700) (.n 4699) (.n 4691)),
    .atom (.copy (.n 4701) (.n 4700)),
    .atom (.const (.n 4702) (word 32 0)),
    .atom (.copy (.n 4703) (.n 4036)),
    .atom (.copy (.n 4704) (.n 4053)),
    .atom (.copy (.n 4705) (.n 4057)),
    .atom (.copy (.n 4706) (.n 4061)),
    .atom (.copy (.n 4707) (.n 4065)),
    .atom (.copy (.n 4708) (.n 4082)),
    .atom (.copy (.n 4709) (.n 4086)),
    .atom (.copy (.n 4710) (.n 4090)),
    .atom (.copy (.n 4711) (.n 4094)),
    .atom (.copy (.n 4712) (.n 4111)),
    .atom (.copy (.n 4713) (.n 4115)),
    .atom (.copy (.n 4714) (.n 4119))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4272, a4273, a4274, a4275, a4276, a4277, a4278, a4279, a4280, a4281, a4282, a4283, a4284, a4285,
    a4286, a4287, a4288, a4289, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 4854 [
    .atom (.load (.n 5279) (.n 13) 0),
    .atom (.mul (.n 5280) (.n 5279) (.n 4697)),
    .atom (.load (.n 5281) (.n 13) 1),
    .atom (.mul (.n 5282) (.n 5281) (.n 4698)),
    .atom (.add (.n 5283) (.n 5280) (.n 5282)),
    .atom (.load (.n 5284) (.n 13) 2),
    .atom (.mul (.n 5285) (.n 5284) (.n 4701)),
    .atom (.add (.n 5286) (.n 5283) (.n 5285)),
    .atom (.load (.n 5287) (.n 13) 3),
    .atom (.mul (.n 5288) (.n 5287) (.n 4702)),
    .atom (.add (.n 5289) (.n 5286) (.n 5288)),
    .atom (.load (.n 5290) (.n 13) 4),
    .atom (.mul (.n 5291) (.n 5290) (.n 4703)),
    .atom (.add (.n 5292) (.n 5289) (.n 5291)),
    .atom (.load (.n 5293) (.n 13) 5),
    .atom (.mul (.n 5294) (.n 5293) (.n 4704)),
    .atom (.add (.n 5295) (.n 5292) (.n 5294)),
    .atom (.load (.n 5296) (.n 13) 6),
    .atom (.mul (.n 5297) (.n 5296) (.n 4705)),
    .atom (.add (.n 5298) (.n 5295) (.n 5297)),
    .atom (.load (.n 5299) (.n 13) 7),
    .atom (.mul (.n 5300) (.n 5299) (.n 4706)),
    .atom (.add (.n 5301) (.n 5298) (.n 5300)),
    .atom (.load (.n 5302) (.n 13) 8),
    .atom (.mul (.n 5303) (.n 5302) (.n 4707)),
    .atom (.add (.n 5304) (.n 5301) (.n 5303)),
    .atom (.load (.n 5305) (.n 13) 9),
    .atom (.mul (.n 5306) (.n 5305) (.n 4708)),
    .atom (.add (.n 5307) (.n 5304) (.n 5306)),
    .atom (.load (.n 5308) (.n 13) 10),
    .atom (.mul (.n 5309) (.n 5308) (.n 4709)),
    .atom (.add (.n 5310) (.n 5307) (.n 5309)),
    .atom (.load (.n 5311) (.n 13) 11),
    .atom (.mul (.n 5312) (.n 5311) (.n 4710)),
    .atom (.add (.n 5313) (.n 5310) (.n 5312)),
    .atom (.load (.n 5314) (.n 13) 12),
    .atom (.mul (.n 5315) (.n 5314) (.n 4711)),
    .atom (.add (.n 5316) (.n 5313) (.n 5315)),
    .atom (.load (.n 5317) (.n 13) 13),
    .atom (.mul (.n 5318) (.n 5317) (.n 4712)),
    .atom (.add (.n 5319) (.n 5316) (.n 5318)),
    .atom (.load (.n 5320) (.n 13) 14),
    .atom (.mul (.n 5321) (.n 5320) (.n 4713)),
    .atom (.add (.n 5322) (.n 5319) (.n 5321)),
    .atom (.load (.n 5323) (.n 13) 15),
    .atom (.mul (.n 5324) (.n 5323) (.n 4714)),
    .atom (.add (.n 5325) (.n 5322) (.n 5324)),
    .atom (.add (.n 5326) (.n 14) (.n 5325)),
    .atom (.mul (.n 5327) (.n 1058) (.n 5326)),
    .atom (.add (.n 5328) (.n 5278) (.n 5327))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a4854, a4855, a4856, a4857, a4858, a4859, a4860, a4861, a4862, a4863, a4864, a4865, a4866, a4867,
    a4868, a4869, a4870, a4871, a4872, a4873, a4874, a4875, a4876, a4877, a4878, a4879, a4880,
    a4881, a4882, a4883, a4884, a4885, a4886, a4887, a4888, a4889, a4890, a4891, a4892, a4893,
    a4894, a4895, a4896, a4897, a4898, a4899, a4900, a4901, a4902, a4903, -⟩ := hs1
  have e4854 := tb_loadHolds_unique a4854 (hw 0 (by norm_num))
  have e4856 := tb_loadHolds_unique a4856 (hw 1 (by norm_num))
  have e4859 := tb_loadHolds_unique a4859 (hw 2 (by norm_num))
  have e4862 := tb_loadHolds_unique a4862 (hw 3 (by norm_num))
  have e4865 := tb_loadHolds_unique a4865 (hw 4 (by norm_num))
  have e4868 := tb_loadHolds_unique a4868 (hw 5 (by norm_num))
  have e4871 := tb_loadHolds_unique a4871 (hw 6 (by norm_num))
  have e4874 := tb_loadHolds_unique a4874 (hw 7 (by norm_num))
  have e4877 := tb_loadHolds_unique a4877 (hw 8 (by norm_num))
  have e4880 := tb_loadHolds_unique a4880 (hw 9 (by norm_num))
  have e4883 := tb_loadHolds_unique a4883 (hw 10 (by norm_num))
  have e4886 := tb_loadHolds_unique a4886 (hw 11 (by norm_num))
  have e4889 := tb_loadHolds_unique a4889 (hw 12 (by norm_num))
  have e4892 := tb_loadHolds_unique a4892 (hw 13 (by norm_num))
  have e4895 := tb_loadHolds_unique a4895 (hw 14 (by norm_num))
  have e4898 := tb_loadHolds_unique a4898 (hw 15 (by norm_num))
  have v4028 : σ (.n 4028) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_evalF h (k := 61) (by norm_num)).2.2
  have v4036 : σ (.n 4036) = ev 2 := by
    rw [← hev 2 (by norm_num)]; exact (vt_evalF h (k := 63) (by norm_num)).2.2
  have v4053 : σ (.n 4053) = ev 3 := by
    rw [← hev 3 (by norm_num)]; exact (vt_evalF h (k := 64) (by norm_num)).2.2
  have v4057 : σ (.n 4057) = ev 4 := by
    rw [← hev 4 (by norm_num)]; exact (vt_evalF h (k := 65) (by norm_num)).2.2
  have v4061 : σ (.n 4061) = ev 5 := by
    rw [← hev 5 (by norm_num)]; exact (vt_evalF h (k := 66) (by norm_num)).2.2
  have v4065 : σ (.n 4065) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_evalF h (k := 67) (by norm_num)).2.2
  have v4082 : σ (.n 4082) = ev 7 := by
    rw [← hev 7 (by norm_num)]; exact (vt_evalF h (k := 68) (by norm_num)).2.2
  have v4086 : σ (.n 4086) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_evalF h (k := 69) (by norm_num)).2.2
  have v4090 : σ (.n 4090) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_evalF h (k := 70) (by norm_num)).2.2
  have v4094 : σ (.n 4094) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_evalF h (k := 71) (by norm_num)).2.2
  have v4111 : σ (.n 4111) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_evalF h (k := 72) (by norm_num)).2.2
  have v4115 : σ (.n 4115) = ev 12 := by
    rw [← hev 12 (by norm_num)]; exact (vt_evalF h (k := 73) (by norm_num)).2.2
  have v4119 : σ (.n 4119) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_evalF h (k := 74) (by norm_num)).2.2
  have v4691 : σ (.n 4691) = ev 91 := by
    rw [← hev 91 (by norm_num)]; exact (vt_evalF h (k := 152) (by norm_num)).2.2
  have hB : σ (.n 5326) = vtBlockVal (σ (.n 14)) W ev [[([], 4)], [([0], 1)], [([91], 2)], [([], 32)], [([2], 1)], [([3], 1)], [([4], 1)], [([5], 1)], [([6], 1)], [([7], 1)], [([8], 1)], [([9], 1)], [([10], 1)], [([11], 1)], [([12], 1)], [([13], 1)]] := by
    simp only [v4691, v4119, v4115, v4111, v4094, v4090, v4086, v4082, v4065, v4061, v4057, v4053, v4036,
      v4028, a4901, a4900, a4899, e4898, a4897, a4896, e4895, a4894, a4893, e4892, a4891,
      a4890, e4889, a4888, a4887, e4886, a4885, a4884, e4883, a4882, a4881, e4880, a4879,
      a4878, e4877, a4876, a4875, e4874, a4873, a4872, e4871, a4870, a4869, e4868, a4867,
      a4866, e4865, a4864, a4863, e4862, a4861, a4860, e4859, a4858, a4857, e4856, a4855,
      e4854, a4289, a4288, a4287, a4286, a4285, a4284, a4283, a4282, a4281, a4280, a4279,
      a4278, a4277, a4276, a4275, a4274, a4273, a4272]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a4903, a4902, hB]

set_option maxRecDepth 10000 in
theorem vtB05_2F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5345) = σ (.n 5328) + σ (.n 1067) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 2], 1)], [([65], 2)], [([15], 1), ([10, 15], 1), ([10, 14], 1)], [([16], 1), ([10, 16], 1), ([10, 15], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4290 [
    .atom (.const (.n 4715) (word 2 0)),
    .atom (.mul (.n 4716) (.n 4032) (.n 4036)),
    .atom (.copy (.n 4717) (.n 4716)),
    .atom (.const (.n 4718) (word 2 0)),
    .atom (.mul (.n 4719) (.n 4718) (.n 4496)),
    .atom (.copy (.n 4720) (.n 4719)),
    .atom (.mul (.n 4721) (.n 4094) (.n 4140)),
    .atom (.add (.n 4722) (.n 4140) (.n 4721)),
    .atom (.mul (.n 4723) (.n 4094) (.n 4123)),
    .atom (.add (.n 4724) (.n 4722) (.n 4723)),
    .atom (.copy (.n 4725) (.n 4724)),
    .atom (.mul (.n 4726) (.n 4094) (.n 4144)),
    .atom (.add (.n 4727) (.n 4144) (.n 4726)),
    .atom (.mul (.n 4728) (.n 4094) (.n 4140)),
    .atom (.add (.n 4729) (.n 4727) (.n 4728)),
    .atom (.copy (.n 4730) (.n 4729))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4290, a4291, a4292, a4293, a4294, a4295, a4296, a4297, a4298, a4299, a4300, a4301, a4302, a4303,
    a4304, a4305, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 4904 [
    .atom (.load (.n 5329) (.n 13) 0),
    .atom (.mul (.n 5330) (.n 5329) (.n 4715)),
    .atom (.load (.n 5331) (.n 13) 1),
    .atom (.mul (.n 5332) (.n 5331) (.n 4717)),
    .atom (.add (.n 5333) (.n 5330) (.n 5332)),
    .atom (.load (.n 5334) (.n 13) 2),
    .atom (.mul (.n 5335) (.n 5334) (.n 4720)),
    .atom (.add (.n 5336) (.n 5333) (.n 5335)),
    .atom (.load (.n 5337) (.n 13) 3),
    .atom (.mul (.n 5338) (.n 5337) (.n 4725)),
    .atom (.add (.n 5339) (.n 5336) (.n 5338)),
    .atom (.load (.n 5340) (.n 13) 4),
    .atom (.mul (.n 5341) (.n 5340) (.n 4730)),
    .atom (.add (.n 5342) (.n 5339) (.n 5341)),
    .atom (.add (.n 5343) (.n 14) (.n 5342)),
    .atom (.mul (.n 5344) (.n 1067) (.n 5343)),
    .atom (.add (.n 5345) (.n 5328) (.n 5344))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a4904, a4905, a4906, a4907, a4908, a4909, a4910, a4911, a4912, a4913, a4914, a4915, a4916, a4917,
    a4918, a4919, a4920, -⟩ := hs1
  have e4904 := tb_loadHolds_unique a4904 (hw 0 (by norm_num))
  have e4906 := tb_loadHolds_unique a4906 (hw 1 (by norm_num))
  have e4909 := tb_loadHolds_unique a4909 (hw 2 (by norm_num))
  have e4912 := tb_loadHolds_unique a4912 (hw 3 (by norm_num))
  have e4915 := tb_loadHolds_unique a4915 (hw 4 (by norm_num))
  have v4032 : σ (.n 4032) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 62) (by norm_num)).2.2
  have v4036 : σ (.n 4036) = ev 2 := by
    rw [← hev 2 (by norm_num)]; exact (vt_evalF h (k := 63) (by norm_num)).2.2
  have v4094 : σ (.n 4094) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_evalF h (k := 71) (by norm_num)).2.2
  have v4123 : σ (.n 4123) = ev 14 := by
    rw [← hev 14 (by norm_num)]; exact (vt_evalF h (k := 75) (by norm_num)).2.2
  have v4140 : σ (.n 4140) = ev 15 := by
    rw [← hev 15 (by norm_num)]; exact (vt_evalF h (k := 76) (by norm_num)).2.2
  have v4144 : σ (.n 4144) = ev 16 := by
    rw [← hev 16 (by norm_num)]; exact (vt_evalF h (k := 77) (by norm_num)).2.2
  have v4496 : σ (.n 4496) = ev 65 := by
    rw [← hev 65 (by norm_num)]; exact (vt_evalF h (k := 126) (by norm_num)).2.2
  have hB : σ (.n 5343) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 2], 1)], [([65], 2)], [([15], 1), ([10, 15], 1), ([10, 14], 1)], [([16], 1), ([10, 16], 1), ([10, 15], 1)]] := by
    simp only [v4496, v4144, v4140, v4123, v4094, v4036, v4032, a4918, a4917, a4916, e4915, a4914, a4913,
      e4912, a4911, a4910, e4909, a4908, a4907, e4906, a4905, e4904, a4305, a4304, a4303,
      a4302, a4301, a4300, a4299, a4298, a4297, a4296, a4295, a4294, a4293, a4292, a4291,
      a4290]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a4920, a4919, hB]

set_option maxRecDepth 10000 in
theorem vtB05_3F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5362) = σ (.n 5345) + σ (.n 1076) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 3], 1)], [([66], 2)], [([17], 1), ([10, 17], 1), ([10, 16], 1)], [([18], 1), ([10, 18], 1), ([10, 17], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4306 [
    .atom (.const (.n 4731) (word 2 0)),
    .atom (.mul (.n 4732) (.n 4032) (.n 4053)),
    .atom (.copy (.n 4733) (.n 4732)),
    .atom (.const (.n 4734) (word 2 0)),
    .atom (.mul (.n 4735) (.n 4734) (.n 4500)),
    .atom (.copy (.n 4736) (.n 4735)),
    .atom (.mul (.n 4737) (.n 4094) (.n 4148)),
    .atom (.add (.n 4738) (.n 4148) (.n 4737)),
    .atom (.mul (.n 4739) (.n 4094) (.n 4144)),
    .atom (.add (.n 4740) (.n 4738) (.n 4739)),
    .atom (.copy (.n 4741) (.n 4740)),
    .atom (.mul (.n 4742) (.n 4094) (.n 4152)),
    .atom (.add (.n 4743) (.n 4152) (.n 4742)),
    .atom (.mul (.n 4744) (.n 4094) (.n 4148)),
    .atom (.add (.n 4745) (.n 4743) (.n 4744)),
    .atom (.copy (.n 4746) (.n 4745))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4306, a4307, a4308, a4309, a4310, a4311, a4312, a4313, a4314, a4315, a4316, a4317, a4318, a4319,
    a4320, a4321, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 4921 [
    .atom (.load (.n 5346) (.n 13) 0),
    .atom (.mul (.n 5347) (.n 5346) (.n 4731)),
    .atom (.load (.n 5348) (.n 13) 1),
    .atom (.mul (.n 5349) (.n 5348) (.n 4733)),
    .atom (.add (.n 5350) (.n 5347) (.n 5349)),
    .atom (.load (.n 5351) (.n 13) 2),
    .atom (.mul (.n 5352) (.n 5351) (.n 4736)),
    .atom (.add (.n 5353) (.n 5350) (.n 5352)),
    .atom (.load (.n 5354) (.n 13) 3),
    .atom (.mul (.n 5355) (.n 5354) (.n 4741)),
    .atom (.add (.n 5356) (.n 5353) (.n 5355)),
    .atom (.load (.n 5357) (.n 13) 4),
    .atom (.mul (.n 5358) (.n 5357) (.n 4746)),
    .atom (.add (.n 5359) (.n 5356) (.n 5358)),
    .atom (.add (.n 5360) (.n 14) (.n 5359)),
    .atom (.mul (.n 5361) (.n 1076) (.n 5360)),
    .atom (.add (.n 5362) (.n 5345) (.n 5361))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a4921, a4922, a4923, a4924, a4925, a4926, a4927, a4928, a4929, a4930, a4931, a4932, a4933, a4934,
    a4935, a4936, a4937, -⟩ := hs1
  have e4921 := tb_loadHolds_unique a4921 (hw 0 (by norm_num))
  have e4923 := tb_loadHolds_unique a4923 (hw 1 (by norm_num))
  have e4926 := tb_loadHolds_unique a4926 (hw 2 (by norm_num))
  have e4929 := tb_loadHolds_unique a4929 (hw 3 (by norm_num))
  have e4932 := tb_loadHolds_unique a4932 (hw 4 (by norm_num))
  have v4032 : σ (.n 4032) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 62) (by norm_num)).2.2
  have v4053 : σ (.n 4053) = ev 3 := by
    rw [← hev 3 (by norm_num)]; exact (vt_evalF h (k := 64) (by norm_num)).2.2
  have v4094 : σ (.n 4094) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_evalF h (k := 71) (by norm_num)).2.2
  have v4144 : σ (.n 4144) = ev 16 := by
    rw [← hev 16 (by norm_num)]; exact (vt_evalF h (k := 77) (by norm_num)).2.2
  have v4148 : σ (.n 4148) = ev 17 := by
    rw [← hev 17 (by norm_num)]; exact (vt_evalF h (k := 78) (by norm_num)).2.2
  have v4152 : σ (.n 4152) = ev 18 := by
    rw [← hev 18 (by norm_num)]; exact (vt_evalF h (k := 79) (by norm_num)).2.2
  have v4500 : σ (.n 4500) = ev 66 := by
    rw [← hev 66 (by norm_num)]; exact (vt_evalF h (k := 127) (by norm_num)).2.2
  have hB : σ (.n 5360) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 3], 1)], [([66], 2)], [([17], 1), ([10, 17], 1), ([10, 16], 1)], [([18], 1), ([10, 18], 1), ([10, 17], 1)]] := by
    simp only [v4500, v4152, v4148, v4144, v4094, v4053, v4032, a4935, a4934, a4933, e4932, a4931, a4930,
      e4929, a4928, a4927, e4926, a4925, a4924, e4923, a4922, e4921, a4321, a4320, a4319,
      a4318, a4317, a4316, a4315, a4314, a4313, a4312, a4311, a4310, a4309, a4308, a4307,
      a4306]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a4937, a4936, hB]

set_option maxRecDepth 10000 in
theorem vtB05_4F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5379) = σ (.n 5362) + σ (.n 1085) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 4], 1)], [([67], 2)], [([19], 1), ([10, 19], 1), ([10, 18], 1)], [([20], 1), ([10, 20], 1), ([10, 19], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4322 [
    .atom (.const (.n 4747) (word 2 0)),
    .atom (.mul (.n 4748) (.n 4032) (.n 4057)),
    .atom (.copy (.n 4749) (.n 4748)),
    .atom (.const (.n 4750) (word 2 0)),
    .atom (.mul (.n 4751) (.n 4750) (.n 4517)),
    .atom (.copy (.n 4752) (.n 4751)),
    .atom (.mul (.n 4753) (.n 4094) (.n 4169)),
    .atom (.add (.n 4754) (.n 4169) (.n 4753)),
    .atom (.mul (.n 4755) (.n 4094) (.n 4152)),
    .atom (.add (.n 4756) (.n 4754) (.n 4755)),
    .atom (.copy (.n 4757) (.n 4756)),
    .atom (.mul (.n 4758) (.n 4094) (.n 4173)),
    .atom (.add (.n 4759) (.n 4173) (.n 4758)),
    .atom (.mul (.n 4760) (.n 4094) (.n 4169)),
    .atom (.add (.n 4761) (.n 4759) (.n 4760)),
    .atom (.copy (.n 4762) (.n 4761))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4322, a4323, a4324, a4325, a4326, a4327, a4328, a4329, a4330, a4331, a4332, a4333, a4334, a4335,
    a4336, a4337, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 4938 [
    .atom (.load (.n 5363) (.n 13) 0),
    .atom (.mul (.n 5364) (.n 5363) (.n 4747)),
    .atom (.load (.n 5365) (.n 13) 1),
    .atom (.mul (.n 5366) (.n 5365) (.n 4749)),
    .atom (.add (.n 5367) (.n 5364) (.n 5366)),
    .atom (.load (.n 5368) (.n 13) 2),
    .atom (.mul (.n 5369) (.n 5368) (.n 4752)),
    .atom (.add (.n 5370) (.n 5367) (.n 5369)),
    .atom (.load (.n 5371) (.n 13) 3),
    .atom (.mul (.n 5372) (.n 5371) (.n 4757)),
    .atom (.add (.n 5373) (.n 5370) (.n 5372)),
    .atom (.load (.n 5374) (.n 13) 4),
    .atom (.mul (.n 5375) (.n 5374) (.n 4762)),
    .atom (.add (.n 5376) (.n 5373) (.n 5375)),
    .atom (.add (.n 5377) (.n 14) (.n 5376)),
    .atom (.mul (.n 5378) (.n 1085) (.n 5377)),
    .atom (.add (.n 5379) (.n 5362) (.n 5378))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a4938, a4939, a4940, a4941, a4942, a4943, a4944, a4945, a4946, a4947, a4948, a4949, a4950, a4951,
    a4952, a4953, a4954, -⟩ := hs1
  have e4938 := tb_loadHolds_unique a4938 (hw 0 (by norm_num))
  have e4940 := tb_loadHolds_unique a4940 (hw 1 (by norm_num))
  have e4943 := tb_loadHolds_unique a4943 (hw 2 (by norm_num))
  have e4946 := tb_loadHolds_unique a4946 (hw 3 (by norm_num))
  have e4949 := tb_loadHolds_unique a4949 (hw 4 (by norm_num))
  have v4032 : σ (.n 4032) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 62) (by norm_num)).2.2
  have v4057 : σ (.n 4057) = ev 4 := by
    rw [← hev 4 (by norm_num)]; exact (vt_evalF h (k := 65) (by norm_num)).2.2
  have v4094 : σ (.n 4094) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_evalF h (k := 71) (by norm_num)).2.2
  have v4152 : σ (.n 4152) = ev 18 := by
    rw [← hev 18 (by norm_num)]; exact (vt_evalF h (k := 79) (by norm_num)).2.2
  have v4169 : σ (.n 4169) = ev 19 := by
    rw [← hev 19 (by norm_num)]; exact (vt_evalF h (k := 80) (by norm_num)).2.2
  have v4173 : σ (.n 4173) = ev 20 := by
    rw [← hev 20 (by norm_num)]; exact (vt_evalF h (k := 81) (by norm_num)).2.2
  have v4517 : σ (.n 4517) = ev 67 := by
    rw [← hev 67 (by norm_num)]; exact (vt_evalF h (k := 128) (by norm_num)).2.2
  have hB : σ (.n 5377) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 4], 1)], [([67], 2)], [([19], 1), ([10, 19], 1), ([10, 18], 1)], [([20], 1), ([10, 20], 1), ([10, 19], 1)]] := by
    simp only [v4517, v4173, v4169, v4152, v4094, v4057, v4032, a4952, a4951, a4950, e4949, a4948, a4947,
      e4946, a4945, a4944, e4943, a4942, a4941, e4940, a4939, e4938, a4337, a4336, a4335,
      a4334, a4333, a4332, a4331, a4330, a4329, a4328, a4327, a4326, a4325, a4324, a4323,
      a4322]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a4954, a4953, hB]

set_option maxRecDepth 10000 in
theorem vtB05_5F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5396) = σ (.n 5379) + σ (.n 1094) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 5], 1)], [([68], 2)], [([21], 1), ([10, 21], 1), ([10, 20], 1)], [([22], 1), ([10, 22], 1), ([10, 21], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4338 [
    .atom (.const (.n 4763) (word 2 0)),
    .atom (.mul (.n 4764) (.n 4032) (.n 4061)),
    .atom (.copy (.n 4765) (.n 4764)),
    .atom (.const (.n 4766) (word 2 0)),
    .atom (.mul (.n 4767) (.n 4766) (.n 4521)),
    .atom (.copy (.n 4768) (.n 4767)),
    .atom (.mul (.n 4769) (.n 4094) (.n 4177)),
    .atom (.add (.n 4770) (.n 4177) (.n 4769)),
    .atom (.mul (.n 4771) (.n 4094) (.n 4173)),
    .atom (.add (.n 4772) (.n 4770) (.n 4771)),
    .atom (.copy (.n 4773) (.n 4772)),
    .atom (.mul (.n 4774) (.n 4094) (.n 4181)),
    .atom (.add (.n 4775) (.n 4181) (.n 4774)),
    .atom (.mul (.n 4776) (.n 4094) (.n 4177)),
    .atom (.add (.n 4777) (.n 4775) (.n 4776)),
    .atom (.copy (.n 4778) (.n 4777))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4338, a4339, a4340, a4341, a4342, a4343, a4344, a4345, a4346, a4347, a4348, a4349, a4350, a4351,
    a4352, a4353, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 4955 [
    .atom (.load (.n 5380) (.n 13) 0),
    .atom (.mul (.n 5381) (.n 5380) (.n 4763)),
    .atom (.load (.n 5382) (.n 13) 1),
    .atom (.mul (.n 5383) (.n 5382) (.n 4765)),
    .atom (.add (.n 5384) (.n 5381) (.n 5383)),
    .atom (.load (.n 5385) (.n 13) 2),
    .atom (.mul (.n 5386) (.n 5385) (.n 4768)),
    .atom (.add (.n 5387) (.n 5384) (.n 5386)),
    .atom (.load (.n 5388) (.n 13) 3),
    .atom (.mul (.n 5389) (.n 5388) (.n 4773)),
    .atom (.add (.n 5390) (.n 5387) (.n 5389)),
    .atom (.load (.n 5391) (.n 13) 4),
    .atom (.mul (.n 5392) (.n 5391) (.n 4778)),
    .atom (.add (.n 5393) (.n 5390) (.n 5392)),
    .atom (.add (.n 5394) (.n 14) (.n 5393)),
    .atom (.mul (.n 5395) (.n 1094) (.n 5394)),
    .atom (.add (.n 5396) (.n 5379) (.n 5395))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a4955, a4956, a4957, a4958, a4959, a4960, a4961, a4962, a4963, a4964, a4965, a4966, a4967, a4968,
    a4969, a4970, a4971, -⟩ := hs1
  have e4955 := tb_loadHolds_unique a4955 (hw 0 (by norm_num))
  have e4957 := tb_loadHolds_unique a4957 (hw 1 (by norm_num))
  have e4960 := tb_loadHolds_unique a4960 (hw 2 (by norm_num))
  have e4963 := tb_loadHolds_unique a4963 (hw 3 (by norm_num))
  have e4966 := tb_loadHolds_unique a4966 (hw 4 (by norm_num))
  have v4032 : σ (.n 4032) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 62) (by norm_num)).2.2
  have v4061 : σ (.n 4061) = ev 5 := by
    rw [← hev 5 (by norm_num)]; exact (vt_evalF h (k := 66) (by norm_num)).2.2
  have v4094 : σ (.n 4094) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_evalF h (k := 71) (by norm_num)).2.2
  have v4173 : σ (.n 4173) = ev 20 := by
    rw [← hev 20 (by norm_num)]; exact (vt_evalF h (k := 81) (by norm_num)).2.2
  have v4177 : σ (.n 4177) = ev 21 := by
    rw [← hev 21 (by norm_num)]; exact (vt_evalF h (k := 82) (by norm_num)).2.2
  have v4181 : σ (.n 4181) = ev 22 := by
    rw [← hev 22 (by norm_num)]; exact (vt_evalF h (k := 83) (by norm_num)).2.2
  have v4521 : σ (.n 4521) = ev 68 := by
    rw [← hev 68 (by norm_num)]; exact (vt_evalF h (k := 129) (by norm_num)).2.2
  have hB : σ (.n 5394) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 5], 1)], [([68], 2)], [([21], 1), ([10, 21], 1), ([10, 20], 1)], [([22], 1), ([10, 22], 1), ([10, 21], 1)]] := by
    simp only [v4521, v4181, v4177, v4173, v4094, v4061, v4032, a4969, a4968, a4967, e4966, a4965, a4964,
      e4963, a4962, a4961, e4960, a4959, a4958, e4957, a4956, e4955, a4353, a4352, a4351,
      a4350, a4349, a4348, a4347, a4346, a4345, a4344, a4343, a4342, a4341, a4340, a4339,
      a4338]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a4971, a4970, hB]

set_option maxRecDepth 10000 in
theorem vtB05_6F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5413) = σ (.n 5396) + σ (.n 1103) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 6], 1)], [([69], 2)], [([23], 1), ([10, 23], 1), ([10, 22], 1)], [([24], 1), ([10, 24], 1), ([10, 23], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4354 [
    .atom (.const (.n 4779) (word 2 0)),
    .atom (.mul (.n 4780) (.n 4032) (.n 4065)),
    .atom (.copy (.n 4781) (.n 4780)),
    .atom (.const (.n 4782) (word 2 0)),
    .atom (.mul (.n 4783) (.n 4782) (.n 4525)),
    .atom (.copy (.n 4784) (.n 4783)),
    .atom (.mul (.n 4785) (.n 4094) (.n 4198)),
    .atom (.add (.n 4786) (.n 4198) (.n 4785)),
    .atom (.mul (.n 4787) (.n 4094) (.n 4181)),
    .atom (.add (.n 4788) (.n 4786) (.n 4787)),
    .atom (.copy (.n 4789) (.n 4788)),
    .atom (.mul (.n 4790) (.n 4094) (.n 4202)),
    .atom (.add (.n 4791) (.n 4202) (.n 4790)),
    .atom (.mul (.n 4792) (.n 4094) (.n 4198)),
    .atom (.add (.n 4793) (.n 4791) (.n 4792)),
    .atom (.copy (.n 4794) (.n 4793))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4354, a4355, a4356, a4357, a4358, a4359, a4360, a4361, a4362, a4363, a4364, a4365, a4366, a4367,
    a4368, a4369, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 4972 [
    .atom (.load (.n 5397) (.n 13) 0),
    .atom (.mul (.n 5398) (.n 5397) (.n 4779)),
    .atom (.load (.n 5399) (.n 13) 1),
    .atom (.mul (.n 5400) (.n 5399) (.n 4781)),
    .atom (.add (.n 5401) (.n 5398) (.n 5400)),
    .atom (.load (.n 5402) (.n 13) 2),
    .atom (.mul (.n 5403) (.n 5402) (.n 4784)),
    .atom (.add (.n 5404) (.n 5401) (.n 5403)),
    .atom (.load (.n 5405) (.n 13) 3),
    .atom (.mul (.n 5406) (.n 5405) (.n 4789)),
    .atom (.add (.n 5407) (.n 5404) (.n 5406)),
    .atom (.load (.n 5408) (.n 13) 4),
    .atom (.mul (.n 5409) (.n 5408) (.n 4794)),
    .atom (.add (.n 5410) (.n 5407) (.n 5409)),
    .atom (.add (.n 5411) (.n 14) (.n 5410)),
    .atom (.mul (.n 5412) (.n 1103) (.n 5411)),
    .atom (.add (.n 5413) (.n 5396) (.n 5412))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a4972, a4973, a4974, a4975, a4976, a4977, a4978, a4979, a4980, a4981, a4982, a4983, a4984, a4985,
    a4986, a4987, a4988, -⟩ := hs1
  have e4972 := tb_loadHolds_unique a4972 (hw 0 (by norm_num))
  have e4974 := tb_loadHolds_unique a4974 (hw 1 (by norm_num))
  have e4977 := tb_loadHolds_unique a4977 (hw 2 (by norm_num))
  have e4980 := tb_loadHolds_unique a4980 (hw 3 (by norm_num))
  have e4983 := tb_loadHolds_unique a4983 (hw 4 (by norm_num))
  have v4032 : σ (.n 4032) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 62) (by norm_num)).2.2
  have v4065 : σ (.n 4065) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_evalF h (k := 67) (by norm_num)).2.2
  have v4094 : σ (.n 4094) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_evalF h (k := 71) (by norm_num)).2.2
  have v4181 : σ (.n 4181) = ev 22 := by
    rw [← hev 22 (by norm_num)]; exact (vt_evalF h (k := 83) (by norm_num)).2.2
  have v4198 : σ (.n 4198) = ev 23 := by
    rw [← hev 23 (by norm_num)]; exact (vt_evalF h (k := 84) (by norm_num)).2.2
  have v4202 : σ (.n 4202) = ev 24 := by
    rw [← hev 24 (by norm_num)]; exact (vt_evalF h (k := 85) (by norm_num)).2.2
  have v4525 : σ (.n 4525) = ev 69 := by
    rw [← hev 69 (by norm_num)]; exact (vt_evalF h (k := 130) (by norm_num)).2.2
  have hB : σ (.n 5411) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 6], 1)], [([69], 2)], [([23], 1), ([10, 23], 1), ([10, 22], 1)], [([24], 1), ([10, 24], 1), ([10, 23], 1)]] := by
    simp only [v4525, v4202, v4198, v4181, v4094, v4065, v4032, a4986, a4985, a4984, e4983, a4982, a4981,
      e4980, a4979, a4978, e4977, a4976, a4975, e4974, a4973, e4972, a4369, a4368, a4367,
      a4366, a4365, a4364, a4363, a4362, a4361, a4360, a4359, a4358, a4357, a4356, a4355,
      a4354]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a4988, a4987, hB]

set_option maxRecDepth 10000 in
theorem vtB05_7F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5430) = σ (.n 5413) + σ (.n 1112) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 6], 2)], [([70], 2)], [([25], 1), ([10, 25], 1), ([10, 24], 1)], [([26], 1), ([10, 26], 1), ([10, 25], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4370 [
    .atom (.const (.n 4795) (word 2 0)),
    .atom (.const (.n 4796) (word 2 0)),
    .atom (.mul (.n 4797) (.n 4032) (.n 4065)),
    .atom (.mul (.n 4798) (.n 4796) (.n 4797)),
    .atom (.copy (.n 4799) (.n 4798)),
    .atom (.const (.n 4800) (word 2 0)),
    .atom (.mul (.n 4801) (.n 4800) (.n 4529)),
    .atom (.copy (.n 4802) (.n 4801)),
    .atom (.mul (.n 4803) (.n 4094) (.n 4206)),
    .atom (.add (.n 4804) (.n 4206) (.n 4803)),
    .atom (.mul (.n 4805) (.n 4094) (.n 4202)),
    .atom (.add (.n 4806) (.n 4804) (.n 4805)),
    .atom (.copy (.n 4807) (.n 4806)),
    .atom (.mul (.n 4808) (.n 4094) (.n 4210)),
    .atom (.add (.n 4809) (.n 4210) (.n 4808)),
    .atom (.mul (.n 4810) (.n 4094) (.n 4206)),
    .atom (.add (.n 4811) (.n 4809) (.n 4810)),
    .atom (.copy (.n 4812) (.n 4811))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4370, a4371, a4372, a4373, a4374, a4375, a4376, a4377, a4378, a4379, a4380, a4381, a4382, a4383,
    a4384, a4385, a4386, a4387, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 4989 [
    .atom (.load (.n 5414) (.n 13) 0),
    .atom (.mul (.n 5415) (.n 5414) (.n 4795)),
    .atom (.load (.n 5416) (.n 13) 1),
    .atom (.mul (.n 5417) (.n 5416) (.n 4799)),
    .atom (.add (.n 5418) (.n 5415) (.n 5417)),
    .atom (.load (.n 5419) (.n 13) 2),
    .atom (.mul (.n 5420) (.n 5419) (.n 4802)),
    .atom (.add (.n 5421) (.n 5418) (.n 5420)),
    .atom (.load (.n 5422) (.n 13) 3),
    .atom (.mul (.n 5423) (.n 5422) (.n 4807)),
    .atom (.add (.n 5424) (.n 5421) (.n 5423)),
    .atom (.load (.n 5425) (.n 13) 4),
    .atom (.mul (.n 5426) (.n 5425) (.n 4812)),
    .atom (.add (.n 5427) (.n 5424) (.n 5426)),
    .atom (.add (.n 5428) (.n 14) (.n 5427)),
    .atom (.mul (.n 5429) (.n 1112) (.n 5428)),
    .atom (.add (.n 5430) (.n 5413) (.n 5429))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a4989, a4990, a4991, a4992, a4993, a4994, a4995, a4996, a4997, a4998, a4999, a5000, a5001, a5002,
    a5003, a5004, a5005, -⟩ := hs1
  have e4989 := tb_loadHolds_unique a4989 (hw 0 (by norm_num))
  have e4991 := tb_loadHolds_unique a4991 (hw 1 (by norm_num))
  have e4994 := tb_loadHolds_unique a4994 (hw 2 (by norm_num))
  have e4997 := tb_loadHolds_unique a4997 (hw 3 (by norm_num))
  have e5000 := tb_loadHolds_unique a5000 (hw 4 (by norm_num))
  have v4032 : σ (.n 4032) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 62) (by norm_num)).2.2
  have v4065 : σ (.n 4065) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_evalF h (k := 67) (by norm_num)).2.2
  have v4094 : σ (.n 4094) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_evalF h (k := 71) (by norm_num)).2.2
  have v4202 : σ (.n 4202) = ev 24 := by
    rw [← hev 24 (by norm_num)]; exact (vt_evalF h (k := 85) (by norm_num)).2.2
  have v4206 : σ (.n 4206) = ev 25 := by
    rw [← hev 25 (by norm_num)]; exact (vt_evalF h (k := 86) (by norm_num)).2.2
  have v4210 : σ (.n 4210) = ev 26 := by
    rw [← hev 26 (by norm_num)]; exact (vt_evalF h (k := 87) (by norm_num)).2.2
  have v4529 : σ (.n 4529) = ev 70 := by
    rw [← hev 70 (by norm_num)]; exact (vt_evalF h (k := 131) (by norm_num)).2.2
  have hB : σ (.n 5428) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 6], 2)], [([70], 2)], [([25], 1), ([10, 25], 1), ([10, 24], 1)], [([26], 1), ([10, 26], 1), ([10, 25], 1)]] := by
    simp only [v4529, v4210, v4206, v4202, v4094, v4065, v4032, a5003, a5002, a5001, e5000, a4999, a4998,
      e4997, a4996, a4995, e4994, a4993, a4992, e4991, a4990, e4989, a4387, a4386, a4385,
      a4384, a4383, a4382, a4381, a4380, a4379, a4378, a4377, a4376, a4375, a4374, a4373,
      a4372, a4371, a4370]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5005, a5004, hB]

set_option maxRecDepth 10000 in
theorem vtB05_8F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5447) = σ (.n 5430) + σ (.n 1121) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 6], 4)], [([71], 2)], [([27], 1), ([10, 27], 1), ([10, 26], 1)], [([28], 1), ([10, 28], 1), ([10, 27], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4388 [
    .atom (.const (.n 4813) (word 2 0)),
    .atom (.const (.n 4814) (word 4 0)),
    .atom (.mul (.n 4815) (.n 4032) (.n 4065)),
    .atom (.mul (.n 4816) (.n 4814) (.n 4815)),
    .atom (.copy (.n 4817) (.n 4816)),
    .atom (.const (.n 4818) (word 2 0)),
    .atom (.mul (.n 4819) (.n 4818) (.n 4546)),
    .atom (.copy (.n 4820) (.n 4819)),
    .atom (.mul (.n 4821) (.n 4094) (.n 4227)),
    .atom (.add (.n 4822) (.n 4227) (.n 4821)),
    .atom (.mul (.n 4823) (.n 4094) (.n 4210)),
    .atom (.add (.n 4824) (.n 4822) (.n 4823)),
    .atom (.copy (.n 4825) (.n 4824)),
    .atom (.mul (.n 4826) (.n 4094) (.n 4231)),
    .atom (.add (.n 4827) (.n 4231) (.n 4826)),
    .atom (.mul (.n 4828) (.n 4094) (.n 4227)),
    .atom (.add (.n 4829) (.n 4827) (.n 4828)),
    .atom (.copy (.n 4830) (.n 4829))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4388, a4389, a4390, a4391, a4392, a4393, a4394, a4395, a4396, a4397, a4398, a4399, a4400, a4401,
    a4402, a4403, a4404, a4405, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5006 [
    .atom (.load (.n 5431) (.n 13) 0),
    .atom (.mul (.n 5432) (.n 5431) (.n 4813)),
    .atom (.load (.n 5433) (.n 13) 1),
    .atom (.mul (.n 5434) (.n 5433) (.n 4817)),
    .atom (.add (.n 5435) (.n 5432) (.n 5434)),
    .atom (.load (.n 5436) (.n 13) 2),
    .atom (.mul (.n 5437) (.n 5436) (.n 4820)),
    .atom (.add (.n 5438) (.n 5435) (.n 5437)),
    .atom (.load (.n 5439) (.n 13) 3),
    .atom (.mul (.n 5440) (.n 5439) (.n 4825)),
    .atom (.add (.n 5441) (.n 5438) (.n 5440)),
    .atom (.load (.n 5442) (.n 13) 4),
    .atom (.mul (.n 5443) (.n 5442) (.n 4830)),
    .atom (.add (.n 5444) (.n 5441) (.n 5443)),
    .atom (.add (.n 5445) (.n 14) (.n 5444)),
    .atom (.mul (.n 5446) (.n 1121) (.n 5445)),
    .atom (.add (.n 5447) (.n 5430) (.n 5446))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5006, a5007, a5008, a5009, a5010, a5011, a5012, a5013, a5014, a5015, a5016, a5017, a5018, a5019,
    a5020, a5021, a5022, -⟩ := hs1
  have e5006 := tb_loadHolds_unique a5006 (hw 0 (by norm_num))
  have e5008 := tb_loadHolds_unique a5008 (hw 1 (by norm_num))
  have e5011 := tb_loadHolds_unique a5011 (hw 2 (by norm_num))
  have e5014 := tb_loadHolds_unique a5014 (hw 3 (by norm_num))
  have e5017 := tb_loadHolds_unique a5017 (hw 4 (by norm_num))
  have v4032 : σ (.n 4032) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 62) (by norm_num)).2.2
  have v4065 : σ (.n 4065) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_evalF h (k := 67) (by norm_num)).2.2
  have v4094 : σ (.n 4094) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_evalF h (k := 71) (by norm_num)).2.2
  have v4210 : σ (.n 4210) = ev 26 := by
    rw [← hev 26 (by norm_num)]; exact (vt_evalF h (k := 87) (by norm_num)).2.2
  have v4227 : σ (.n 4227) = ev 27 := by
    rw [← hev 27 (by norm_num)]; exact (vt_evalF h (k := 88) (by norm_num)).2.2
  have v4231 : σ (.n 4231) = ev 28 := by
    rw [← hev 28 (by norm_num)]; exact (vt_evalF h (k := 89) (by norm_num)).2.2
  have v4546 : σ (.n 4546) = ev 71 := by
    rw [← hev 71 (by norm_num)]; exact (vt_evalF h (k := 132) (by norm_num)).2.2
  have hB : σ (.n 5445) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 6], 4)], [([71], 2)], [([27], 1), ([10, 27], 1), ([10, 26], 1)], [([28], 1), ([10, 28], 1), ([10, 27], 1)]] := by
    simp only [v4546, v4231, v4227, v4210, v4094, v4065, v4032, a5020, a5019, a5018, e5017, a5016, a5015,
      e5014, a5013, a5012, e5011, a5010, a5009, e5008, a5007, e5006, a4405, a4404, a4403,
      a4402, a4401, a4400, a4399, a4398, a4397, a4396, a4395, a4394, a4393, a4392, a4391,
      a4390, a4389, a4388]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5022, a5021, hB]

set_option maxRecDepth 10000 in
theorem vtB05_9F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5464) = σ (.n 5447) + σ (.n 1130) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 6], 8)], [([72], 2)], [([29], 1), ([10, 29], 1), ([10, 28], 1)], [([30], 1), ([10, 30], 1), ([10, 29], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4406 [
    .atom (.const (.n 4831) (word 2 0)),
    .atom (.const (.n 4832) (word 8 0)),
    .atom (.mul (.n 4833) (.n 4032) (.n 4065)),
    .atom (.mul (.n 4834) (.n 4832) (.n 4833)),
    .atom (.copy (.n 4835) (.n 4834)),
    .atom (.const (.n 4836) (word 2 0)),
    .atom (.mul (.n 4837) (.n 4836) (.n 4550)),
    .atom (.copy (.n 4838) (.n 4837)),
    .atom (.mul (.n 4839) (.n 4094) (.n 4235)),
    .atom (.add (.n 4840) (.n 4235) (.n 4839)),
    .atom (.mul (.n 4841) (.n 4094) (.n 4231)),
    .atom (.add (.n 4842) (.n 4840) (.n 4841)),
    .atom (.copy (.n 4843) (.n 4842)),
    .atom (.mul (.n 4844) (.n 4094) (.n 4239)),
    .atom (.add (.n 4845) (.n 4239) (.n 4844)),
    .atom (.mul (.n 4846) (.n 4094) (.n 4235)),
    .atom (.add (.n 4847) (.n 4845) (.n 4846)),
    .atom (.copy (.n 4848) (.n 4847))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4406, a4407, a4408, a4409, a4410, a4411, a4412, a4413, a4414, a4415, a4416, a4417, a4418, a4419,
    a4420, a4421, a4422, a4423, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5023 [
    .atom (.load (.n 5448) (.n 13) 0),
    .atom (.mul (.n 5449) (.n 5448) (.n 4831)),
    .atom (.load (.n 5450) (.n 13) 1),
    .atom (.mul (.n 5451) (.n 5450) (.n 4835)),
    .atom (.add (.n 5452) (.n 5449) (.n 5451)),
    .atom (.load (.n 5453) (.n 13) 2),
    .atom (.mul (.n 5454) (.n 5453) (.n 4838)),
    .atom (.add (.n 5455) (.n 5452) (.n 5454)),
    .atom (.load (.n 5456) (.n 13) 3),
    .atom (.mul (.n 5457) (.n 5456) (.n 4843)),
    .atom (.add (.n 5458) (.n 5455) (.n 5457)),
    .atom (.load (.n 5459) (.n 13) 4),
    .atom (.mul (.n 5460) (.n 5459) (.n 4848)),
    .atom (.add (.n 5461) (.n 5458) (.n 5460)),
    .atom (.add (.n 5462) (.n 14) (.n 5461)),
    .atom (.mul (.n 5463) (.n 1130) (.n 5462)),
    .atom (.add (.n 5464) (.n 5447) (.n 5463))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5023, a5024, a5025, a5026, a5027, a5028, a5029, a5030, a5031, a5032, a5033, a5034, a5035, a5036,
    a5037, a5038, a5039, -⟩ := hs1
  have e5023 := tb_loadHolds_unique a5023 (hw 0 (by norm_num))
  have e5025 := tb_loadHolds_unique a5025 (hw 1 (by norm_num))
  have e5028 := tb_loadHolds_unique a5028 (hw 2 (by norm_num))
  have e5031 := tb_loadHolds_unique a5031 (hw 3 (by norm_num))
  have e5034 := tb_loadHolds_unique a5034 (hw 4 (by norm_num))
  have v4032 : σ (.n 4032) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 62) (by norm_num)).2.2
  have v4065 : σ (.n 4065) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_evalF h (k := 67) (by norm_num)).2.2
  have v4094 : σ (.n 4094) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_evalF h (k := 71) (by norm_num)).2.2
  have v4231 : σ (.n 4231) = ev 28 := by
    rw [← hev 28 (by norm_num)]; exact (vt_evalF h (k := 89) (by norm_num)).2.2
  have v4235 : σ (.n 4235) = ev 29 := by
    rw [← hev 29 (by norm_num)]; exact (vt_evalF h (k := 90) (by norm_num)).2.2
  have v4239 : σ (.n 4239) = ev 30 := by
    rw [← hev 30 (by norm_num)]; exact (vt_evalF h (k := 91) (by norm_num)).2.2
  have v4550 : σ (.n 4550) = ev 72 := by
    rw [← hev 72 (by norm_num)]; exact (vt_evalF h (k := 133) (by norm_num)).2.2
  have hB : σ (.n 5462) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 6], 8)], [([72], 2)], [([29], 1), ([10, 29], 1), ([10, 28], 1)], [([30], 1), ([10, 30], 1), ([10, 29], 1)]] := by
    simp only [v4550, v4239, v4235, v4231, v4094, v4065, v4032, a5037, a5036, a5035, e5034, a5033, a5032,
      e5031, a5030, a5029, e5028, a5027, a5026, e5025, a5024, e5023, a4423, a4422, a4421,
      a4420, a4419, a4418, a4417, a4416, a4415, a4414, a4413, a4412, a4411, a4410, a4409,
      a4408, a4407, a4406]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5039, a5038, hB]

set_option maxRecDepth 10000 in
theorem vtB05_10F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5481) = σ (.n 5464) + σ (.n 1139) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 7], 1)], [([73], 2)], [([31], 1), ([10, 31], 1), ([10, 30], 1)], [([14], 1), ([10, 14], 1), ([10, 31], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4424 [
    .atom (.const (.n 4849) (word 2 0)),
    .atom (.mul (.n 4850) (.n 4032) (.n 4082)),
    .atom (.copy (.n 4851) (.n 4850)),
    .atom (.const (.n 4852) (word 2 0)),
    .atom (.mul (.n 4853) (.n 4852) (.n 4554)),
    .atom (.copy (.n 4854) (.n 4853)),
    .atom (.mul (.n 4855) (.n 4094) (.n 4256)),
    .atom (.add (.n 4856) (.n 4256) (.n 4855)),
    .atom (.mul (.n 4857) (.n 4094) (.n 4239)),
    .atom (.add (.n 4858) (.n 4856) (.n 4857)),
    .atom (.copy (.n 4859) (.n 4858)),
    .atom (.mul (.n 4860) (.n 4094) (.n 4123)),
    .atom (.add (.n 4861) (.n 4123) (.n 4860)),
    .atom (.mul (.n 4862) (.n 4094) (.n 4256)),
    .atom (.add (.n 4863) (.n 4861) (.n 4862)),
    .atom (.copy (.n 4864) (.n 4863))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4424, a4425, a4426, a4427, a4428, a4429, a4430, a4431, a4432, a4433, a4434, a4435, a4436, a4437,
    a4438, a4439, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5040 [
    .atom (.load (.n 5465) (.n 13) 0),
    .atom (.mul (.n 5466) (.n 5465) (.n 4849)),
    .atom (.load (.n 5467) (.n 13) 1),
    .atom (.mul (.n 5468) (.n 5467) (.n 4851)),
    .atom (.add (.n 5469) (.n 5466) (.n 5468)),
    .atom (.load (.n 5470) (.n 13) 2),
    .atom (.mul (.n 5471) (.n 5470) (.n 4854)),
    .atom (.add (.n 5472) (.n 5469) (.n 5471)),
    .atom (.load (.n 5473) (.n 13) 3),
    .atom (.mul (.n 5474) (.n 5473) (.n 4859)),
    .atom (.add (.n 5475) (.n 5472) (.n 5474)),
    .atom (.load (.n 5476) (.n 13) 4),
    .atom (.mul (.n 5477) (.n 5476) (.n 4864)),
    .atom (.add (.n 5478) (.n 5475) (.n 5477)),
    .atom (.add (.n 5479) (.n 14) (.n 5478)),
    .atom (.mul (.n 5480) (.n 1139) (.n 5479)),
    .atom (.add (.n 5481) (.n 5464) (.n 5480))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5040, a5041, a5042, a5043, a5044, a5045, a5046, a5047, a5048, a5049, a5050, a5051, a5052, a5053,
    a5054, a5055, a5056, -⟩ := hs1
  have e5040 := tb_loadHolds_unique a5040 (hw 0 (by norm_num))
  have e5042 := tb_loadHolds_unique a5042 (hw 1 (by norm_num))
  have e5045 := tb_loadHolds_unique a5045 (hw 2 (by norm_num))
  have e5048 := tb_loadHolds_unique a5048 (hw 3 (by norm_num))
  have e5051 := tb_loadHolds_unique a5051 (hw 4 (by norm_num))
  have v4032 : σ (.n 4032) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 62) (by norm_num)).2.2
  have v4082 : σ (.n 4082) = ev 7 := by
    rw [← hev 7 (by norm_num)]; exact (vt_evalF h (k := 68) (by norm_num)).2.2
  have v4094 : σ (.n 4094) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_evalF h (k := 71) (by norm_num)).2.2
  have v4123 : σ (.n 4123) = ev 14 := by
    rw [← hev 14 (by norm_num)]; exact (vt_evalF h (k := 75) (by norm_num)).2.2
  have v4239 : σ (.n 4239) = ev 30 := by
    rw [← hev 30 (by norm_num)]; exact (vt_evalF h (k := 91) (by norm_num)).2.2
  have v4256 : σ (.n 4256) = ev 31 := by
    rw [← hev 31 (by norm_num)]; exact (vt_evalF h (k := 92) (by norm_num)).2.2
  have v4554 : σ (.n 4554) = ev 73 := by
    rw [← hev 73 (by norm_num)]; exact (vt_evalF h (k := 134) (by norm_num)).2.2
  have hB : σ (.n 5479) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 7], 1)], [([73], 2)], [([31], 1), ([10, 31], 1), ([10, 30], 1)], [([14], 1), ([10, 14], 1), ([10, 31], 1)]] := by
    simp only [v4554, v4256, v4239, v4123, v4094, v4082, v4032, a5054, a5053, a5052, e5051, a5050, a5049,
      e5048, a5047, a5046, e5045, a5044, a5043, e5042, a5041, e5040, a4439, a4438, a4437,
      a4436, a4435, a4434, a4433, a4432, a4431, a4430, a4429, a4428, a4427, a4426, a4425,
      a4424]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5056, a5055, hB]

set_option maxRecDepth 10000 in
theorem vtB05_11F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5498) = σ (.n 5481) + σ (.n 1148) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 8], 1)], [([74], 2)], [([32], 1)], [([33], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4440 [
    .atom (.const (.n 4865) (word 2 0)),
    .atom (.mul (.n 4866) (.n 4032) (.n 4086)),
    .atom (.copy (.n 4867) (.n 4866)),
    .atom (.const (.n 4868) (word 2 0)),
    .atom (.mul (.n 4869) (.n 4868) (.n 4558)),
    .atom (.copy (.n 4870) (.n 4869)),
    .atom (.copy (.n 4871) (.n 4260)),
    .atom (.copy (.n 4872) (.n 4264))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4440, a4441, a4442, a4443, a4444, a4445, a4446, a4447, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5057 [
    .atom (.load (.n 5482) (.n 13) 0),
    .atom (.mul (.n 5483) (.n 5482) (.n 4865)),
    .atom (.load (.n 5484) (.n 13) 1),
    .atom (.mul (.n 5485) (.n 5484) (.n 4867)),
    .atom (.add (.n 5486) (.n 5483) (.n 5485)),
    .atom (.load (.n 5487) (.n 13) 2),
    .atom (.mul (.n 5488) (.n 5487) (.n 4870)),
    .atom (.add (.n 5489) (.n 5486) (.n 5488)),
    .atom (.load (.n 5490) (.n 13) 3),
    .atom (.mul (.n 5491) (.n 5490) (.n 4871)),
    .atom (.add (.n 5492) (.n 5489) (.n 5491)),
    .atom (.load (.n 5493) (.n 13) 4),
    .atom (.mul (.n 5494) (.n 5493) (.n 4872)),
    .atom (.add (.n 5495) (.n 5492) (.n 5494)),
    .atom (.add (.n 5496) (.n 14) (.n 5495)),
    .atom (.mul (.n 5497) (.n 1148) (.n 5496)),
    .atom (.add (.n 5498) (.n 5481) (.n 5497))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5057, a5058, a5059, a5060, a5061, a5062, a5063, a5064, a5065, a5066, a5067, a5068, a5069, a5070,
    a5071, a5072, a5073, -⟩ := hs1
  have e5057 := tb_loadHolds_unique a5057 (hw 0 (by norm_num))
  have e5059 := tb_loadHolds_unique a5059 (hw 1 (by norm_num))
  have e5062 := tb_loadHolds_unique a5062 (hw 2 (by norm_num))
  have e5065 := tb_loadHolds_unique a5065 (hw 3 (by norm_num))
  have e5068 := tb_loadHolds_unique a5068 (hw 4 (by norm_num))
  have v4032 : σ (.n 4032) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 62) (by norm_num)).2.2
  have v4086 : σ (.n 4086) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_evalF h (k := 69) (by norm_num)).2.2
  have v4260 : σ (.n 4260) = ev 32 := by
    rw [← hev 32 (by norm_num)]; exact (vt_evalF h (k := 93) (by norm_num)).2.2
  have v4264 : σ (.n 4264) = ev 33 := by
    rw [← hev 33 (by norm_num)]; exact (vt_evalF h (k := 94) (by norm_num)).2.2
  have v4558 : σ (.n 4558) = ev 74 := by
    rw [← hev 74 (by norm_num)]; exact (vt_evalF h (k := 135) (by norm_num)).2.2
  have hB : σ (.n 5496) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 8], 1)], [([74], 2)], [([32], 1)], [([33], 1)]] := by
    simp only [v4558, v4264, v4260, v4086, v4032, a5071, a5070, a5069, e5068, a5067, a5066, e5065, a5064,
      a5063, e5062, a5061, a5060, e5059, a5058, e5057, a4447, a4446, a4445, a4444, a4443,
      a4442, a4441, a4440]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5073, a5072, hB]

set_option maxRecDepth 10000 in
theorem vtB05_12F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5515) = σ (.n 5498) + σ (.n 1157) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 8], 2)], [([75], 2)], [([34], 1)], [([35], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4448 [
    .atom (.const (.n 4873) (word 2 0)),
    .atom (.const (.n 4874) (word 2 0)),
    .atom (.mul (.n 4875) (.n 4032) (.n 4086)),
    .atom (.mul (.n 4876) (.n 4874) (.n 4875)),
    .atom (.copy (.n 4877) (.n 4876)),
    .atom (.const (.n 4878) (word 2 0)),
    .atom (.mul (.n 4879) (.n 4878) (.n 4575)),
    .atom (.copy (.n 4880) (.n 4879)),
    .atom (.copy (.n 4881) (.n 4268)),
    .atom (.copy (.n 4882) (.n 4285))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4448, a4449, a4450, a4451, a4452, a4453, a4454, a4455, a4456, a4457, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5074 [
    .atom (.load (.n 5499) (.n 13) 0),
    .atom (.mul (.n 5500) (.n 5499) (.n 4873)),
    .atom (.load (.n 5501) (.n 13) 1),
    .atom (.mul (.n 5502) (.n 5501) (.n 4877)),
    .atom (.add (.n 5503) (.n 5500) (.n 5502)),
    .atom (.load (.n 5504) (.n 13) 2),
    .atom (.mul (.n 5505) (.n 5504) (.n 4880)),
    .atom (.add (.n 5506) (.n 5503) (.n 5505)),
    .atom (.load (.n 5507) (.n 13) 3),
    .atom (.mul (.n 5508) (.n 5507) (.n 4881)),
    .atom (.add (.n 5509) (.n 5506) (.n 5508)),
    .atom (.load (.n 5510) (.n 13) 4),
    .atom (.mul (.n 5511) (.n 5510) (.n 4882)),
    .atom (.add (.n 5512) (.n 5509) (.n 5511)),
    .atom (.add (.n 5513) (.n 14) (.n 5512)),
    .atom (.mul (.n 5514) (.n 1157) (.n 5513)),
    .atom (.add (.n 5515) (.n 5498) (.n 5514))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5074, a5075, a5076, a5077, a5078, a5079, a5080, a5081, a5082, a5083, a5084, a5085, a5086, a5087,
    a5088, a5089, a5090, -⟩ := hs1
  have e5074 := tb_loadHolds_unique a5074 (hw 0 (by norm_num))
  have e5076 := tb_loadHolds_unique a5076 (hw 1 (by norm_num))
  have e5079 := tb_loadHolds_unique a5079 (hw 2 (by norm_num))
  have e5082 := tb_loadHolds_unique a5082 (hw 3 (by norm_num))
  have e5085 := tb_loadHolds_unique a5085 (hw 4 (by norm_num))
  have v4032 : σ (.n 4032) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 62) (by norm_num)).2.2
  have v4086 : σ (.n 4086) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_evalF h (k := 69) (by norm_num)).2.2
  have v4268 : σ (.n 4268) = ev 34 := by
    rw [← hev 34 (by norm_num)]; exact (vt_evalF h (k := 95) (by norm_num)).2.2
  have v4285 : σ (.n 4285) = ev 35 := by
    rw [← hev 35 (by norm_num)]; exact (vt_evalF h (k := 96) (by norm_num)).2.2
  have v4575 : σ (.n 4575) = ev 75 := by
    rw [← hev 75 (by norm_num)]; exact (vt_evalF h (k := 136) (by norm_num)).2.2
  have hB : σ (.n 5513) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 8], 2)], [([75], 2)], [([34], 1)], [([35], 1)]] := by
    simp only [v4575, v4285, v4268, v4086, v4032, a5088, a5087, a5086, e5085, a5084, a5083, e5082, a5081,
      a5080, e5079, a5078, a5077, e5076, a5075, e5074, a4457, a4456, a4455, a4454, a4453,
      a4452, a4451, a4450, a4449, a4448]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5090, a5089, hB]

set_option maxRecDepth 10000 in
theorem vtB05_13F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5532) = σ (.n 5515) + σ (.n 1166) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 8], 4)], [([76], 2)], [([36], 1)], [([37], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4458 [
    .atom (.const (.n 4883) (word 2 0)),
    .atom (.const (.n 4884) (word 4 0)),
    .atom (.mul (.n 4885) (.n 4032) (.n 4086)),
    .atom (.mul (.n 4886) (.n 4884) (.n 4885)),
    .atom (.copy (.n 4887) (.n 4886)),
    .atom (.const (.n 4888) (word 2 0)),
    .atom (.mul (.n 4889) (.n 4888) (.n 4579)),
    .atom (.copy (.n 4890) (.n 4889)),
    .atom (.copy (.n 4891) (.n 4289)),
    .atom (.copy (.n 4892) (.n 4293))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4458, a4459, a4460, a4461, a4462, a4463, a4464, a4465, a4466, a4467, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5091 [
    .atom (.load (.n 5516) (.n 13) 0),
    .atom (.mul (.n 5517) (.n 5516) (.n 4883)),
    .atom (.load (.n 5518) (.n 13) 1),
    .atom (.mul (.n 5519) (.n 5518) (.n 4887)),
    .atom (.add (.n 5520) (.n 5517) (.n 5519)),
    .atom (.load (.n 5521) (.n 13) 2),
    .atom (.mul (.n 5522) (.n 5521) (.n 4890)),
    .atom (.add (.n 5523) (.n 5520) (.n 5522)),
    .atom (.load (.n 5524) (.n 13) 3),
    .atom (.mul (.n 5525) (.n 5524) (.n 4891)),
    .atom (.add (.n 5526) (.n 5523) (.n 5525)),
    .atom (.load (.n 5527) (.n 13) 4),
    .atom (.mul (.n 5528) (.n 5527) (.n 4892)),
    .atom (.add (.n 5529) (.n 5526) (.n 5528)),
    .atom (.add (.n 5530) (.n 14) (.n 5529)),
    .atom (.mul (.n 5531) (.n 1166) (.n 5530)),
    .atom (.add (.n 5532) (.n 5515) (.n 5531))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5091, a5092, a5093, a5094, a5095, a5096, a5097, a5098, a5099, a5100, a5101, a5102, a5103, a5104,
    a5105, a5106, a5107, -⟩ := hs1
  have e5091 := tb_loadHolds_unique a5091 (hw 0 (by norm_num))
  have e5093 := tb_loadHolds_unique a5093 (hw 1 (by norm_num))
  have e5096 := tb_loadHolds_unique a5096 (hw 2 (by norm_num))
  have e5099 := tb_loadHolds_unique a5099 (hw 3 (by norm_num))
  have e5102 := tb_loadHolds_unique a5102 (hw 4 (by norm_num))
  have v4032 : σ (.n 4032) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 62) (by norm_num)).2.2
  have v4086 : σ (.n 4086) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_evalF h (k := 69) (by norm_num)).2.2
  have v4289 : σ (.n 4289) = ev 36 := by
    rw [← hev 36 (by norm_num)]; exact (vt_evalF h (k := 97) (by norm_num)).2.2
  have v4293 : σ (.n 4293) = ev 37 := by
    rw [← hev 37 (by norm_num)]; exact (vt_evalF h (k := 98) (by norm_num)).2.2
  have v4579 : σ (.n 4579) = ev 76 := by
    rw [← hev 76 (by norm_num)]; exact (vt_evalF h (k := 137) (by norm_num)).2.2
  have hB : σ (.n 5530) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 8], 4)], [([76], 2)], [([36], 1)], [([37], 1)]] := by
    simp only [v4579, v4293, v4289, v4086, v4032, a5105, a5104, a5103, e5102, a5101, a5100, e5099, a5098,
      a5097, e5096, a5095, a5094, e5093, a5092, e5091, a4467, a4466, a4465, a4464, a4463,
      a4462, a4461, a4460, a4459, a4458]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5107, a5106, hB]

set_option maxRecDepth 10000 in
theorem vtB05_14F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5549) = σ (.n 5532) + σ (.n 1175) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 8], 8)], [([77], 2)], [([38], 1)], [([39], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4468 [
    .atom (.const (.n 4893) (word 2 0)),
    .atom (.const (.n 4894) (word 8 0)),
    .atom (.mul (.n 4895) (.n 4032) (.n 4086)),
    .atom (.mul (.n 4896) (.n 4894) (.n 4895)),
    .atom (.copy (.n 4897) (.n 4896)),
    .atom (.const (.n 4898) (word 2 0)),
    .atom (.mul (.n 4899) (.n 4898) (.n 4583)),
    .atom (.copy (.n 4900) (.n 4899)),
    .atom (.copy (.n 4901) (.n 4297)),
    .atom (.copy (.n 4902) (.n 4314))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4468, a4469, a4470, a4471, a4472, a4473, a4474, a4475, a4476, a4477, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5108 [
    .atom (.load (.n 5533) (.n 13) 0),
    .atom (.mul (.n 5534) (.n 5533) (.n 4893)),
    .atom (.load (.n 5535) (.n 13) 1),
    .atom (.mul (.n 5536) (.n 5535) (.n 4897)),
    .atom (.add (.n 5537) (.n 5534) (.n 5536)),
    .atom (.load (.n 5538) (.n 13) 2),
    .atom (.mul (.n 5539) (.n 5538) (.n 4900)),
    .atom (.add (.n 5540) (.n 5537) (.n 5539)),
    .atom (.load (.n 5541) (.n 13) 3),
    .atom (.mul (.n 5542) (.n 5541) (.n 4901)),
    .atom (.add (.n 5543) (.n 5540) (.n 5542)),
    .atom (.load (.n 5544) (.n 13) 4),
    .atom (.mul (.n 5545) (.n 5544) (.n 4902)),
    .atom (.add (.n 5546) (.n 5543) (.n 5545)),
    .atom (.add (.n 5547) (.n 14) (.n 5546)),
    .atom (.mul (.n 5548) (.n 1175) (.n 5547)),
    .atom (.add (.n 5549) (.n 5532) (.n 5548))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5108, a5109, a5110, a5111, a5112, a5113, a5114, a5115, a5116, a5117, a5118, a5119, a5120, a5121,
    a5122, a5123, a5124, -⟩ := hs1
  have e5108 := tb_loadHolds_unique a5108 (hw 0 (by norm_num))
  have e5110 := tb_loadHolds_unique a5110 (hw 1 (by norm_num))
  have e5113 := tb_loadHolds_unique a5113 (hw 2 (by norm_num))
  have e5116 := tb_loadHolds_unique a5116 (hw 3 (by norm_num))
  have e5119 := tb_loadHolds_unique a5119 (hw 4 (by norm_num))
  have v4032 : σ (.n 4032) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 62) (by norm_num)).2.2
  have v4086 : σ (.n 4086) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_evalF h (k := 69) (by norm_num)).2.2
  have v4297 : σ (.n 4297) = ev 38 := by
    rw [← hev 38 (by norm_num)]; exact (vt_evalF h (k := 99) (by norm_num)).2.2
  have v4314 : σ (.n 4314) = ev 39 := by
    rw [← hev 39 (by norm_num)]; exact (vt_evalF h (k := 100) (by norm_num)).2.2
  have v4583 : σ (.n 4583) = ev 77 := by
    rw [← hev 77 (by norm_num)]; exact (vt_evalF h (k := 138) (by norm_num)).2.2
  have hB : σ (.n 5547) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 8], 8)], [([77], 2)], [([38], 1)], [([39], 1)]] := by
    simp only [v4583, v4314, v4297, v4086, v4032, a5122, a5121, a5120, e5119, a5118, a5117, e5116, a5115,
      a5114, e5113, a5112, a5111, e5110, a5109, e5108, a4477, a4476, a4475, a4474, a4473,
      a4472, a4471, a4470, a4469, a4468]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5124, a5123, hB]

set_option maxRecDepth 10000 in
theorem vtB05_15F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5566) = σ (.n 5549) + σ (.n 1184) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 9], 1)], [([78], 2)], [([40], 1), ([11, 40], 1)], [([41], 1), ([11, 41], 1), ([11, 40], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4478 [
    .atom (.const (.n 4903) (word 2 0)),
    .atom (.mul (.n 4904) (.n 4032) (.n 4090)),
    .atom (.copy (.n 4905) (.n 4904)),
    .atom (.const (.n 4906) (word 2 0)),
    .atom (.mul (.n 4907) (.n 4906) (.n 4587)),
    .atom (.copy (.n 4908) (.n 4907)),
    .atom (.mul (.n 4909) (.n 4111) (.n 4318)),
    .atom (.add (.n 4910) (.n 4318) (.n 4909)),
    .atom (.copy (.n 4911) (.n 4910)),
    .atom (.mul (.n 4912) (.n 4111) (.n 4322)),
    .atom (.add (.n 4913) (.n 4322) (.n 4912)),
    .atom (.mul (.n 4914) (.n 4111) (.n 4318)),
    .atom (.add (.n 4915) (.n 4913) (.n 4914)),
    .atom (.copy (.n 4916) (.n 4915))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4478, a4479, a4480, a4481, a4482, a4483, a4484, a4485, a4486, a4487, a4488, a4489, a4490, a4491,
    -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5125 [
    .atom (.load (.n 5550) (.n 13) 0),
    .atom (.mul (.n 5551) (.n 5550) (.n 4903)),
    .atom (.load (.n 5552) (.n 13) 1),
    .atom (.mul (.n 5553) (.n 5552) (.n 4905)),
    .atom (.add (.n 5554) (.n 5551) (.n 5553)),
    .atom (.load (.n 5555) (.n 13) 2),
    .atom (.mul (.n 5556) (.n 5555) (.n 4908)),
    .atom (.add (.n 5557) (.n 5554) (.n 5556)),
    .atom (.load (.n 5558) (.n 13) 3),
    .atom (.mul (.n 5559) (.n 5558) (.n 4911)),
    .atom (.add (.n 5560) (.n 5557) (.n 5559)),
    .atom (.load (.n 5561) (.n 13) 4),
    .atom (.mul (.n 5562) (.n 5561) (.n 4916)),
    .atom (.add (.n 5563) (.n 5560) (.n 5562)),
    .atom (.add (.n 5564) (.n 14) (.n 5563)),
    .atom (.mul (.n 5565) (.n 1184) (.n 5564)),
    .atom (.add (.n 5566) (.n 5549) (.n 5565))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5125, a5126, a5127, a5128, a5129, a5130, a5131, a5132, a5133, a5134, a5135, a5136, a5137, a5138,
    a5139, a5140, a5141, -⟩ := hs1
  have e5125 := tb_loadHolds_unique a5125 (hw 0 (by norm_num))
  have e5127 := tb_loadHolds_unique a5127 (hw 1 (by norm_num))
  have e5130 := tb_loadHolds_unique a5130 (hw 2 (by norm_num))
  have e5133 := tb_loadHolds_unique a5133 (hw 3 (by norm_num))
  have e5136 := tb_loadHolds_unique a5136 (hw 4 (by norm_num))
  have v4032 : σ (.n 4032) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 62) (by norm_num)).2.2
  have v4090 : σ (.n 4090) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_evalF h (k := 70) (by norm_num)).2.2
  have v4111 : σ (.n 4111) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_evalF h (k := 72) (by norm_num)).2.2
  have v4318 : σ (.n 4318) = ev 40 := by
    rw [← hev 40 (by norm_num)]; exact (vt_evalF h (k := 101) (by norm_num)).2.2
  have v4322 : σ (.n 4322) = ev 41 := by
    rw [← hev 41 (by norm_num)]; exact (vt_evalF h (k := 102) (by norm_num)).2.2
  have v4587 : σ (.n 4587) = ev 78 := by
    rw [← hev 78 (by norm_num)]; exact (vt_evalF h (k := 139) (by norm_num)).2.2
  have hB : σ (.n 5564) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 9], 1)], [([78], 2)], [([40], 1), ([11, 40], 1)], [([41], 1), ([11, 41], 1), ([11, 40], 1)]] := by
    simp only [v4587, v4322, v4318, v4111, v4090, v4032, a5139, a5138, a5137, e5136, a5135, a5134, e5133,
      a5132, a5131, e5130, a5129, a5128, e5127, a5126, e5125, a4491, a4490, a4489, a4488,
      a4487, a4486, a4485, a4484, a4483, a4482, a4481, a4480, a4479, a4478]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5141, a5140, hB]

set_option maxRecDepth 10000 in
theorem vtB05_16F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5583) = σ (.n 5566) + σ (.n 1193) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 9], 2)], [([79], 1), ([12, 79], 2), ([12, 79], 1)], [([42], 1), ([11, 42], 1), ([11, 41], 1)], [([43], 1), ([11, 43], 1), ([11, 42], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4492 [
    .atom (.const (.n 4917) (word 2 0)),
    .atom (.const (.n 4918) (word 2 0)),
    .atom (.mul (.n 4919) (.n 4032) (.n 4090)),
    .atom (.mul (.n 4920) (.n 4918) (.n 4919)),
    .atom (.copy (.n 4921) (.n 4920)),
    .atom (.const (.n 4922) (word 2 0)),
    .atom (.mul (.n 4923) (.n 4115) (.n 4604)),
    .atom (.mul (.n 4924) (.n 4922) (.n 4923)),
    .atom (.add (.n 4925) (.n 4604) (.n 4924)),
    .atom (.mul (.n 4926) (.n 4115) (.n 4604)),
    .atom (.add (.n 4927) (.n 4925) (.n 4926)),
    .atom (.copy (.n 4928) (.n 4927)),
    .atom (.mul (.n 4929) (.n 4111) (.n 4326)),
    .atom (.add (.n 4930) (.n 4326) (.n 4929)),
    .atom (.mul (.n 4931) (.n 4111) (.n 4322)),
    .atom (.add (.n 4932) (.n 4930) (.n 4931)),
    .atom (.copy (.n 4933) (.n 4932)),
    .atom (.mul (.n 4934) (.n 4111) (.n 4343)),
    .atom (.add (.n 4935) (.n 4343) (.n 4934)),
    .atom (.mul (.n 4936) (.n 4111) (.n 4326)),
    .atom (.add (.n 4937) (.n 4935) (.n 4936)),
    .atom (.copy (.n 4938) (.n 4937))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4492, a4493, a4494, a4495, a4496, a4497, a4498, a4499, a4500, a4501, a4502, a4503, a4504, a4505,
    a4506, a4507, a4508, a4509, a4510, a4511, a4512, a4513, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5142 [
    .atom (.load (.n 5567) (.n 13) 0),
    .atom (.mul (.n 5568) (.n 5567) (.n 4917)),
    .atom (.load (.n 5569) (.n 13) 1),
    .atom (.mul (.n 5570) (.n 5569) (.n 4921)),
    .atom (.add (.n 5571) (.n 5568) (.n 5570)),
    .atom (.load (.n 5572) (.n 13) 2),
    .atom (.mul (.n 5573) (.n 5572) (.n 4928)),
    .atom (.add (.n 5574) (.n 5571) (.n 5573)),
    .atom (.load (.n 5575) (.n 13) 3),
    .atom (.mul (.n 5576) (.n 5575) (.n 4933)),
    .atom (.add (.n 5577) (.n 5574) (.n 5576)),
    .atom (.load (.n 5578) (.n 13) 4),
    .atom (.mul (.n 5579) (.n 5578) (.n 4938)),
    .atom (.add (.n 5580) (.n 5577) (.n 5579)),
    .atom (.add (.n 5581) (.n 14) (.n 5580)),
    .atom (.mul (.n 5582) (.n 1193) (.n 5581)),
    .atom (.add (.n 5583) (.n 5566) (.n 5582))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5142, a5143, a5144, a5145, a5146, a5147, a5148, a5149, a5150, a5151, a5152, a5153, a5154, a5155,
    a5156, a5157, a5158, -⟩ := hs1
  have e5142 := tb_loadHolds_unique a5142 (hw 0 (by norm_num))
  have e5144 := tb_loadHolds_unique a5144 (hw 1 (by norm_num))
  have e5147 := tb_loadHolds_unique a5147 (hw 2 (by norm_num))
  have e5150 := tb_loadHolds_unique a5150 (hw 3 (by norm_num))
  have e5153 := tb_loadHolds_unique a5153 (hw 4 (by norm_num))
  have v4032 : σ (.n 4032) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 62) (by norm_num)).2.2
  have v4090 : σ (.n 4090) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_evalF h (k := 70) (by norm_num)).2.2
  have v4111 : σ (.n 4111) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_evalF h (k := 72) (by norm_num)).2.2
  have v4115 : σ (.n 4115) = ev 12 := by
    rw [← hev 12 (by norm_num)]; exact (vt_evalF h (k := 73) (by norm_num)).2.2
  have v4322 : σ (.n 4322) = ev 41 := by
    rw [← hev 41 (by norm_num)]; exact (vt_evalF h (k := 102) (by norm_num)).2.2
  have v4326 : σ (.n 4326) = ev 42 := by
    rw [← hev 42 (by norm_num)]; exact (vt_evalF h (k := 103) (by norm_num)).2.2
  have v4343 : σ (.n 4343) = ev 43 := by
    rw [← hev 43 (by norm_num)]; exact (vt_evalF h (k := 104) (by norm_num)).2.2
  have v4604 : σ (.n 4604) = ev 79 := by
    rw [← hev 79 (by norm_num)]; exact (vt_evalF h (k := 140) (by norm_num)).2.2
  have hB : σ (.n 5581) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 9], 2)], [([79], 1), ([12, 79], 2), ([12, 79], 1)], [([42], 1), ([11, 42], 1), ([11, 41], 1)], [([43], 1), ([11, 43], 1), ([11, 42], 1)]] := by
    simp only [v4604, v4343, v4326, v4322, v4115, v4111, v4090, v4032, a5156, a5155, a5154, e5153, a5152,
      a5151, e5150, a5149, a5148, e5147, a5146, a5145, e5144, a5143, e5142, a4513, a4512,
      a4511, a4510, a4509, a4508, a4507, a4506, a4505, a4504, a4503, a4502, a4501, a4500,
      a4499, a4498, a4497, a4496, a4495, a4494, a4493, a4492]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5158, a5157, hB]

set_option maxRecDepth 10000 in
theorem vtB05_17F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5600) = σ (.n 5583) + σ (.n 1202) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 9], 4)], [([80], 1), ([13, 80], 2), ([13, 80], 1)], [([44], 1), ([11, 44], 1), ([11, 43], 1)], [([45], 1), ([11, 45], 1), ([11, 44], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4514 [
    .atom (.const (.n 4939) (word 2 0)),
    .atom (.const (.n 4940) (word 4 0)),
    .atom (.mul (.n 4941) (.n 4032) (.n 4090)),
    .atom (.mul (.n 4942) (.n 4940) (.n 4941)),
    .atom (.copy (.n 4943) (.n 4942)),
    .atom (.const (.n 4944) (word 2 0)),
    .atom (.mul (.n 4945) (.n 4119) (.n 4608)),
    .atom (.mul (.n 4946) (.n 4944) (.n 4945)),
    .atom (.add (.n 4947) (.n 4608) (.n 4946)),
    .atom (.mul (.n 4948) (.n 4119) (.n 4608)),
    .atom (.add (.n 4949) (.n 4947) (.n 4948)),
    .atom (.copy (.n 4950) (.n 4949)),
    .atom (.mul (.n 4951) (.n 4111) (.n 4347)),
    .atom (.add (.n 4952) (.n 4347) (.n 4951)),
    .atom (.mul (.n 4953) (.n 4111) (.n 4343)),
    .atom (.add (.n 4954) (.n 4952) (.n 4953)),
    .atom (.copy (.n 4955) (.n 4954)),
    .atom (.mul (.n 4956) (.n 4111) (.n 4351)),
    .atom (.add (.n 4957) (.n 4351) (.n 4956)),
    .atom (.mul (.n 4958) (.n 4111) (.n 4347)),
    .atom (.add (.n 4959) (.n 4957) (.n 4958)),
    .atom (.copy (.n 4960) (.n 4959))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4514, a4515, a4516, a4517, a4518, a4519, a4520, a4521, a4522, a4523, a4524, a4525, a4526, a4527,
    a4528, a4529, a4530, a4531, a4532, a4533, a4534, a4535, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5159 [
    .atom (.load (.n 5584) (.n 13) 0),
    .atom (.mul (.n 5585) (.n 5584) (.n 4939)),
    .atom (.load (.n 5586) (.n 13) 1),
    .atom (.mul (.n 5587) (.n 5586) (.n 4943)),
    .atom (.add (.n 5588) (.n 5585) (.n 5587)),
    .atom (.load (.n 5589) (.n 13) 2),
    .atom (.mul (.n 5590) (.n 5589) (.n 4950)),
    .atom (.add (.n 5591) (.n 5588) (.n 5590)),
    .atom (.load (.n 5592) (.n 13) 3),
    .atom (.mul (.n 5593) (.n 5592) (.n 4955)),
    .atom (.add (.n 5594) (.n 5591) (.n 5593)),
    .atom (.load (.n 5595) (.n 13) 4),
    .atom (.mul (.n 5596) (.n 5595) (.n 4960)),
    .atom (.add (.n 5597) (.n 5594) (.n 5596)),
    .atom (.add (.n 5598) (.n 14) (.n 5597)),
    .atom (.mul (.n 5599) (.n 1202) (.n 5598)),
    .atom (.add (.n 5600) (.n 5583) (.n 5599))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5159, a5160, a5161, a5162, a5163, a5164, a5165, a5166, a5167, a5168, a5169, a5170, a5171, a5172,
    a5173, a5174, a5175, -⟩ := hs1
  have e5159 := tb_loadHolds_unique a5159 (hw 0 (by norm_num))
  have e5161 := tb_loadHolds_unique a5161 (hw 1 (by norm_num))
  have e5164 := tb_loadHolds_unique a5164 (hw 2 (by norm_num))
  have e5167 := tb_loadHolds_unique a5167 (hw 3 (by norm_num))
  have e5170 := tb_loadHolds_unique a5170 (hw 4 (by norm_num))
  have v4032 : σ (.n 4032) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 62) (by norm_num)).2.2
  have v4090 : σ (.n 4090) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_evalF h (k := 70) (by norm_num)).2.2
  have v4111 : σ (.n 4111) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_evalF h (k := 72) (by norm_num)).2.2
  have v4119 : σ (.n 4119) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_evalF h (k := 74) (by norm_num)).2.2
  have v4343 : σ (.n 4343) = ev 43 := by
    rw [← hev 43 (by norm_num)]; exact (vt_evalF h (k := 104) (by norm_num)).2.2
  have v4347 : σ (.n 4347) = ev 44 := by
    rw [← hev 44 (by norm_num)]; exact (vt_evalF h (k := 105) (by norm_num)).2.2
  have v4351 : σ (.n 4351) = ev 45 := by
    rw [← hev 45 (by norm_num)]; exact (vt_evalF h (k := 106) (by norm_num)).2.2
  have v4608 : σ (.n 4608) = ev 80 := by
    rw [← hev 80 (by norm_num)]; exact (vt_evalF h (k := 141) (by norm_num)).2.2
  have hB : σ (.n 5598) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 9], 4)], [([80], 1), ([13, 80], 2), ([13, 80], 1)], [([44], 1), ([11, 44], 1), ([11, 43], 1)], [([45], 1), ([11, 45], 1), ([11, 44], 1)]] := by
    simp only [v4608, v4351, v4347, v4343, v4119, v4111, v4090, v4032, a5173, a5172, a5171, e5170, a5169,
      a5168, e5167, a5166, a5165, e5164, a5163, a5162, e5161, a5160, e5159, a4535, a4534,
      a4533, a4532, a4531, a4530, a4529, a4528, a4527, a4526, a4525, a4524, a4523, a4522,
      a4521, a4520, a4519, a4518, a4517, a4516, a4515, a4514]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5175, a5174, hB]

set_option maxRecDepth 10000 in
theorem vtB05_18F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5617) = σ (.n 5600) + σ (.n 1211) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 9], 8)], [([81], 1), ([13, 81], 2), ([13, 81], 1)], [([46], 1), ([11, 46], 1), ([11, 45], 1)], [([47], 1), ([11, 47], 1), ([11, 46], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4536 [
    .atom (.const (.n 4961) (word 2 0)),
    .atom (.const (.n 4962) (word 8 0)),
    .atom (.mul (.n 4963) (.n 4032) (.n 4090)),
    .atom (.mul (.n 4964) (.n 4962) (.n 4963)),
    .atom (.copy (.n 4965) (.n 4964)),
    .atom (.const (.n 4966) (word 2 0)),
    .atom (.mul (.n 4967) (.n 4119) (.n 4612)),
    .atom (.mul (.n 4968) (.n 4966) (.n 4967)),
    .atom (.add (.n 4969) (.n 4612) (.n 4968)),
    .atom (.mul (.n 4970) (.n 4119) (.n 4612)),
    .atom (.add (.n 4971) (.n 4969) (.n 4970)),
    .atom (.copy (.n 4972) (.n 4971)),
    .atom (.mul (.n 4973) (.n 4111) (.n 4355)),
    .atom (.add (.n 4974) (.n 4355) (.n 4973)),
    .atom (.mul (.n 4975) (.n 4111) (.n 4351)),
    .atom (.add (.n 4976) (.n 4974) (.n 4975)),
    .atom (.copy (.n 4977) (.n 4976)),
    .atom (.mul (.n 4978) (.n 4111) (.n 4372)),
    .atom (.add (.n 4979) (.n 4372) (.n 4978)),
    .atom (.mul (.n 4980) (.n 4111) (.n 4355)),
    .atom (.add (.n 4981) (.n 4979) (.n 4980)),
    .atom (.copy (.n 4982) (.n 4981))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4536, a4537, a4538, a4539, a4540, a4541, a4542, a4543, a4544, a4545, a4546, a4547, a4548, a4549,
    a4550, a4551, a4552, a4553, a4554, a4555, a4556, a4557, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5176 [
    .atom (.load (.n 5601) (.n 13) 0),
    .atom (.mul (.n 5602) (.n 5601) (.n 4961)),
    .atom (.load (.n 5603) (.n 13) 1),
    .atom (.mul (.n 5604) (.n 5603) (.n 4965)),
    .atom (.add (.n 5605) (.n 5602) (.n 5604)),
    .atom (.load (.n 5606) (.n 13) 2),
    .atom (.mul (.n 5607) (.n 5606) (.n 4972)),
    .atom (.add (.n 5608) (.n 5605) (.n 5607)),
    .atom (.load (.n 5609) (.n 13) 3),
    .atom (.mul (.n 5610) (.n 5609) (.n 4977)),
    .atom (.add (.n 5611) (.n 5608) (.n 5610)),
    .atom (.load (.n 5612) (.n 13) 4),
    .atom (.mul (.n 5613) (.n 5612) (.n 4982)),
    .atom (.add (.n 5614) (.n 5611) (.n 5613)),
    .atom (.add (.n 5615) (.n 14) (.n 5614)),
    .atom (.mul (.n 5616) (.n 1211) (.n 5615)),
    .atom (.add (.n 5617) (.n 5600) (.n 5616))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5176, a5177, a5178, a5179, a5180, a5181, a5182, a5183, a5184, a5185, a5186, a5187, a5188, a5189,
    a5190, a5191, a5192, -⟩ := hs1
  have e5176 := tb_loadHolds_unique a5176 (hw 0 (by norm_num))
  have e5178 := tb_loadHolds_unique a5178 (hw 1 (by norm_num))
  have e5181 := tb_loadHolds_unique a5181 (hw 2 (by norm_num))
  have e5184 := tb_loadHolds_unique a5184 (hw 3 (by norm_num))
  have e5187 := tb_loadHolds_unique a5187 (hw 4 (by norm_num))
  have v4032 : σ (.n 4032) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 62) (by norm_num)).2.2
  have v4090 : σ (.n 4090) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_evalF h (k := 70) (by norm_num)).2.2
  have v4111 : σ (.n 4111) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_evalF h (k := 72) (by norm_num)).2.2
  have v4119 : σ (.n 4119) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_evalF h (k := 74) (by norm_num)).2.2
  have v4351 : σ (.n 4351) = ev 45 := by
    rw [← hev 45 (by norm_num)]; exact (vt_evalF h (k := 106) (by norm_num)).2.2
  have v4355 : σ (.n 4355) = ev 46 := by
    rw [← hev 46 (by norm_num)]; exact (vt_evalF h (k := 107) (by norm_num)).2.2
  have v4372 : σ (.n 4372) = ev 47 := by
    rw [← hev 47 (by norm_num)]; exact (vt_evalF h (k := 108) (by norm_num)).2.2
  have v4612 : σ (.n 4612) = ev 81 := by
    rw [← hev 81 (by norm_num)]; exact (vt_evalF h (k := 142) (by norm_num)).2.2
  have hB : σ (.n 5615) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 9], 8)], [([81], 1), ([13, 81], 2), ([13, 81], 1)], [([46], 1), ([11, 46], 1), ([11, 45], 1)], [([47], 1), ([11, 47], 1), ([11, 46], 1)]] := by
    simp only [v4612, v4372, v4355, v4351, v4119, v4111, v4090, v4032, a5190, a5189, a5188, e5187, a5186,
      a5185, e5184, a5183, a5182, e5181, a5180, a5179, e5178, a5177, e5176, a4557, a4556,
      a4555, a4554, a4553, a4552, a4551, a4550, a4549, a4548, a4547, a4546, a4545, a4544,
      a4543, a4542, a4541, a4540, a4539, a4538, a4537, a4536]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5192, a5191, hB]

set_option maxRecDepth 10000 in
theorem vtB05_19F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5634) = σ (.n 5617) + σ (.n 1220) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 9], 16)], [([82], 1), ([13, 82], 2), ([13, 82], 1)], [([48], 1), ([11, 48], 1), ([11, 47], 1)], [([49], 1), ([11, 49], 1), ([11, 48], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4558 [
    .atom (.const (.n 4983) (word 2 0)),
    .atom (.const (.n 4984) (word 16 0)),
    .atom (.mul (.n 4985) (.n 4032) (.n 4090)),
    .atom (.mul (.n 4986) (.n 4984) (.n 4985)),
    .atom (.copy (.n 4987) (.n 4986)),
    .atom (.const (.n 4988) (word 2 0)),
    .atom (.mul (.n 4989) (.n 4119) (.n 4616)),
    .atom (.mul (.n 4990) (.n 4988) (.n 4989)),
    .atom (.add (.n 4991) (.n 4616) (.n 4990)),
    .atom (.mul (.n 4992) (.n 4119) (.n 4616)),
    .atom (.add (.n 4993) (.n 4991) (.n 4992)),
    .atom (.copy (.n 4994) (.n 4993)),
    .atom (.mul (.n 4995) (.n 4111) (.n 4376)),
    .atom (.add (.n 4996) (.n 4376) (.n 4995)),
    .atom (.mul (.n 4997) (.n 4111) (.n 4372)),
    .atom (.add (.n 4998) (.n 4996) (.n 4997)),
    .atom (.copy (.n 4999) (.n 4998)),
    .atom (.mul (.n 5000) (.n 4111) (.n 4380)),
    .atom (.add (.n 5001) (.n 4380) (.n 5000)),
    .atom (.mul (.n 5002) (.n 4111) (.n 4376)),
    .atom (.add (.n 5003) (.n 5001) (.n 5002)),
    .atom (.copy (.n 5004) (.n 5003))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4558, a4559, a4560, a4561, a4562, a4563, a4564, a4565, a4566, a4567, a4568, a4569, a4570, a4571,
    a4572, a4573, a4574, a4575, a4576, a4577, a4578, a4579, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5193 [
    .atom (.load (.n 5618) (.n 13) 0),
    .atom (.mul (.n 5619) (.n 5618) (.n 4983)),
    .atom (.load (.n 5620) (.n 13) 1),
    .atom (.mul (.n 5621) (.n 5620) (.n 4987)),
    .atom (.add (.n 5622) (.n 5619) (.n 5621)),
    .atom (.load (.n 5623) (.n 13) 2),
    .atom (.mul (.n 5624) (.n 5623) (.n 4994)),
    .atom (.add (.n 5625) (.n 5622) (.n 5624)),
    .atom (.load (.n 5626) (.n 13) 3),
    .atom (.mul (.n 5627) (.n 5626) (.n 4999)),
    .atom (.add (.n 5628) (.n 5625) (.n 5627)),
    .atom (.load (.n 5629) (.n 13) 4),
    .atom (.mul (.n 5630) (.n 5629) (.n 5004)),
    .atom (.add (.n 5631) (.n 5628) (.n 5630)),
    .atom (.add (.n 5632) (.n 14) (.n 5631)),
    .atom (.mul (.n 5633) (.n 1220) (.n 5632)),
    .atom (.add (.n 5634) (.n 5617) (.n 5633))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5193, a5194, a5195, a5196, a5197, a5198, a5199, a5200, a5201, a5202, a5203, a5204, a5205, a5206,
    a5207, a5208, a5209, -⟩ := hs1
  have e5193 := tb_loadHolds_unique a5193 (hw 0 (by norm_num))
  have e5195 := tb_loadHolds_unique a5195 (hw 1 (by norm_num))
  have e5198 := tb_loadHolds_unique a5198 (hw 2 (by norm_num))
  have e5201 := tb_loadHolds_unique a5201 (hw 3 (by norm_num))
  have e5204 := tb_loadHolds_unique a5204 (hw 4 (by norm_num))
  have v4032 : σ (.n 4032) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 62) (by norm_num)).2.2
  have v4090 : σ (.n 4090) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_evalF h (k := 70) (by norm_num)).2.2
  have v4111 : σ (.n 4111) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_evalF h (k := 72) (by norm_num)).2.2
  have v4119 : σ (.n 4119) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_evalF h (k := 74) (by norm_num)).2.2
  have v4372 : σ (.n 4372) = ev 47 := by
    rw [← hev 47 (by norm_num)]; exact (vt_evalF h (k := 108) (by norm_num)).2.2
  have v4376 : σ (.n 4376) = ev 48 := by
    rw [← hev 48 (by norm_num)]; exact (vt_evalF h (k := 109) (by norm_num)).2.2
  have v4380 : σ (.n 4380) = ev 49 := by
    rw [← hev 49 (by norm_num)]; exact (vt_evalF h (k := 110) (by norm_num)).2.2
  have v4616 : σ (.n 4616) = ev 82 := by
    rw [← hev 82 (by norm_num)]; exact (vt_evalF h (k := 143) (by norm_num)).2.2
  have hB : σ (.n 5632) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 9], 16)], [([82], 1), ([13, 82], 2), ([13, 82], 1)], [([48], 1), ([11, 48], 1), ([11, 47], 1)], [([49], 1), ([11, 49], 1), ([11, 48], 1)]] := by
    simp only [v4616, v4380, v4376, v4372, v4119, v4111, v4090, v4032, a5207, a5206, a5205, e5204, a5203,
      a5202, e5201, a5200, a5199, e5198, a5197, a5196, e5195, a5194, e5193, a4579, a4578,
      a4577, a4576, a4575, a4574, a4573, a4572, a4571, a4570, a4569, a4568, a4567, a4566,
      a4565, a4564, a4563, a4562, a4561, a4560, a4559, a4558]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5209, a5208, hB]

set_option maxRecDepth 10000 in
theorem vtB05_20F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5651) = σ (.n 5634) + σ (.n 1229) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 9], 32)], [([83], 1), ([13, 83], 2), ([13, 83], 1)], [([50], 1), ([11, 50], 1), ([11, 49], 1)], [([51], 1), ([11, 51], 1), ([11, 50], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4580 [
    .atom (.const (.n 5005) (word 2 0)),
    .atom (.const (.n 5006) (word 32 0)),
    .atom (.mul (.n 5007) (.n 4032) (.n 4090)),
    .atom (.mul (.n 5008) (.n 5006) (.n 5007)),
    .atom (.copy (.n 5009) (.n 5008)),
    .atom (.const (.n 5010) (word 2 0)),
    .atom (.mul (.n 5011) (.n 4119) (.n 4633)),
    .atom (.mul (.n 5012) (.n 5010) (.n 5011)),
    .atom (.add (.n 5013) (.n 4633) (.n 5012)),
    .atom (.mul (.n 5014) (.n 4119) (.n 4633)),
    .atom (.add (.n 5015) (.n 5013) (.n 5014)),
    .atom (.copy (.n 5016) (.n 5015)),
    .atom (.mul (.n 5017) (.n 4111) (.n 4384)),
    .atom (.add (.n 5018) (.n 4384) (.n 5017)),
    .atom (.mul (.n 5019) (.n 4111) (.n 4380)),
    .atom (.add (.n 5020) (.n 5018) (.n 5019)),
    .atom (.copy (.n 5021) (.n 5020)),
    .atom (.mul (.n 5022) (.n 4111) (.n 4401)),
    .atom (.add (.n 5023) (.n 4401) (.n 5022)),
    .atom (.mul (.n 5024) (.n 4111) (.n 4384)),
    .atom (.add (.n 5025) (.n 5023) (.n 5024)),
    .atom (.copy (.n 5026) (.n 5025))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4580, a4581, a4582, a4583, a4584, a4585, a4586, a4587, a4588, a4589, a4590, a4591, a4592, a4593,
    a4594, a4595, a4596, a4597, a4598, a4599, a4600, a4601, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5210 [
    .atom (.load (.n 5635) (.n 13) 0),
    .atom (.mul (.n 5636) (.n 5635) (.n 5005)),
    .atom (.load (.n 5637) (.n 13) 1),
    .atom (.mul (.n 5638) (.n 5637) (.n 5009)),
    .atom (.add (.n 5639) (.n 5636) (.n 5638)),
    .atom (.load (.n 5640) (.n 13) 2),
    .atom (.mul (.n 5641) (.n 5640) (.n 5016)),
    .atom (.add (.n 5642) (.n 5639) (.n 5641)),
    .atom (.load (.n 5643) (.n 13) 3),
    .atom (.mul (.n 5644) (.n 5643) (.n 5021)),
    .atom (.add (.n 5645) (.n 5642) (.n 5644)),
    .atom (.load (.n 5646) (.n 13) 4),
    .atom (.mul (.n 5647) (.n 5646) (.n 5026)),
    .atom (.add (.n 5648) (.n 5645) (.n 5647)),
    .atom (.add (.n 5649) (.n 14) (.n 5648)),
    .atom (.mul (.n 5650) (.n 1229) (.n 5649)),
    .atom (.add (.n 5651) (.n 5634) (.n 5650))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5210, a5211, a5212, a5213, a5214, a5215, a5216, a5217, a5218, a5219, a5220, a5221, a5222, a5223,
    a5224, a5225, a5226, -⟩ := hs1
  have e5210 := tb_loadHolds_unique a5210 (hw 0 (by norm_num))
  have e5212 := tb_loadHolds_unique a5212 (hw 1 (by norm_num))
  have e5215 := tb_loadHolds_unique a5215 (hw 2 (by norm_num))
  have e5218 := tb_loadHolds_unique a5218 (hw 3 (by norm_num))
  have e5221 := tb_loadHolds_unique a5221 (hw 4 (by norm_num))
  have v4032 : σ (.n 4032) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 62) (by norm_num)).2.2
  have v4090 : σ (.n 4090) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_evalF h (k := 70) (by norm_num)).2.2
  have v4111 : σ (.n 4111) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_evalF h (k := 72) (by norm_num)).2.2
  have v4119 : σ (.n 4119) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_evalF h (k := 74) (by norm_num)).2.2
  have v4380 : σ (.n 4380) = ev 49 := by
    rw [← hev 49 (by norm_num)]; exact (vt_evalF h (k := 110) (by norm_num)).2.2
  have v4384 : σ (.n 4384) = ev 50 := by
    rw [← hev 50 (by norm_num)]; exact (vt_evalF h (k := 111) (by norm_num)).2.2
  have v4401 : σ (.n 4401) = ev 51 := by
    rw [← hev 51 (by norm_num)]; exact (vt_evalF h (k := 112) (by norm_num)).2.2
  have v4633 : σ (.n 4633) = ev 83 := by
    rw [← hev 83 (by norm_num)]; exact (vt_evalF h (k := 144) (by norm_num)).2.2
  have hB : σ (.n 5649) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 9], 32)], [([83], 1), ([13, 83], 2), ([13, 83], 1)], [([50], 1), ([11, 50], 1), ([11, 49], 1)], [([51], 1), ([11, 51], 1), ([11, 50], 1)]] := by
    simp only [v4633, v4401, v4384, v4380, v4119, v4111, v4090, v4032, a5224, a5223, a5222, e5221, a5220,
      a5219, e5218, a5217, a5216, e5215, a5214, a5213, e5212, a5211, e5210, a4601, a4600,
      a4599, a4598, a4597, a4596, a4595, a4594, a4593, a4592, a4591, a4590, a4589, a4588,
      a4587, a4586, a4585, a4584, a4583, a4582, a4581, a4580]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5226, a5225, hB]

set_option maxRecDepth 10000 in
theorem vtB05_21F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5668) = σ (.n 5651) + σ (.n 1238) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 9], 64)], [([84], 1), ([13, 84], 2), ([13, 84], 1)], [([52], 1), ([11, 52], 1), ([11, 51], 1)], [([53], 1), ([11, 53], 1), ([11, 52], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4602 [
    .atom (.const (.n 5027) (word 2 0)),
    .atom (.const (.n 5028) (word 64 0)),
    .atom (.mul (.n 5029) (.n 4032) (.n 4090)),
    .atom (.mul (.n 5030) (.n 5028) (.n 5029)),
    .atom (.copy (.n 5031) (.n 5030)),
    .atom (.const (.n 5032) (word 2 0)),
    .atom (.mul (.n 5033) (.n 4119) (.n 4637)),
    .atom (.mul (.n 5034) (.n 5032) (.n 5033)),
    .atom (.add (.n 5035) (.n 4637) (.n 5034)),
    .atom (.mul (.n 5036) (.n 4119) (.n 4637)),
    .atom (.add (.n 5037) (.n 5035) (.n 5036)),
    .atom (.copy (.n 5038) (.n 5037)),
    .atom (.mul (.n 5039) (.n 4111) (.n 4405)),
    .atom (.add (.n 5040) (.n 4405) (.n 5039)),
    .atom (.mul (.n 5041) (.n 4111) (.n 4401)),
    .atom (.add (.n 5042) (.n 5040) (.n 5041)),
    .atom (.copy (.n 5043) (.n 5042)),
    .atom (.mul (.n 5044) (.n 4111) (.n 4409)),
    .atom (.add (.n 5045) (.n 4409) (.n 5044)),
    .atom (.mul (.n 5046) (.n 4111) (.n 4405)),
    .atom (.add (.n 5047) (.n 5045) (.n 5046)),
    .atom (.copy (.n 5048) (.n 5047))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4602, a4603, a4604, a4605, a4606, a4607, a4608, a4609, a4610, a4611, a4612, a4613, a4614, a4615,
    a4616, a4617, a4618, a4619, a4620, a4621, a4622, a4623, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5227 [
    .atom (.load (.n 5652) (.n 13) 0),
    .atom (.mul (.n 5653) (.n 5652) (.n 5027)),
    .atom (.load (.n 5654) (.n 13) 1),
    .atom (.mul (.n 5655) (.n 5654) (.n 5031)),
    .atom (.add (.n 5656) (.n 5653) (.n 5655)),
    .atom (.load (.n 5657) (.n 13) 2),
    .atom (.mul (.n 5658) (.n 5657) (.n 5038)),
    .atom (.add (.n 5659) (.n 5656) (.n 5658)),
    .atom (.load (.n 5660) (.n 13) 3),
    .atom (.mul (.n 5661) (.n 5660) (.n 5043)),
    .atom (.add (.n 5662) (.n 5659) (.n 5661)),
    .atom (.load (.n 5663) (.n 13) 4),
    .atom (.mul (.n 5664) (.n 5663) (.n 5048)),
    .atom (.add (.n 5665) (.n 5662) (.n 5664)),
    .atom (.add (.n 5666) (.n 14) (.n 5665)),
    .atom (.mul (.n 5667) (.n 1238) (.n 5666)),
    .atom (.add (.n 5668) (.n 5651) (.n 5667))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5227, a5228, a5229, a5230, a5231, a5232, a5233, a5234, a5235, a5236, a5237, a5238, a5239, a5240,
    a5241, a5242, a5243, -⟩ := hs1
  have e5227 := tb_loadHolds_unique a5227 (hw 0 (by norm_num))
  have e5229 := tb_loadHolds_unique a5229 (hw 1 (by norm_num))
  have e5232 := tb_loadHolds_unique a5232 (hw 2 (by norm_num))
  have e5235 := tb_loadHolds_unique a5235 (hw 3 (by norm_num))
  have e5238 := tb_loadHolds_unique a5238 (hw 4 (by norm_num))
  have v4032 : σ (.n 4032) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 62) (by norm_num)).2.2
  have v4090 : σ (.n 4090) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_evalF h (k := 70) (by norm_num)).2.2
  have v4111 : σ (.n 4111) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_evalF h (k := 72) (by norm_num)).2.2
  have v4119 : σ (.n 4119) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_evalF h (k := 74) (by norm_num)).2.2
  have v4401 : σ (.n 4401) = ev 51 := by
    rw [← hev 51 (by norm_num)]; exact (vt_evalF h (k := 112) (by norm_num)).2.2
  have v4405 : σ (.n 4405) = ev 52 := by
    rw [← hev 52 (by norm_num)]; exact (vt_evalF h (k := 113) (by norm_num)).2.2
  have v4409 : σ (.n 4409) = ev 53 := by
    rw [← hev 53 (by norm_num)]; exact (vt_evalF h (k := 114) (by norm_num)).2.2
  have v4637 : σ (.n 4637) = ev 84 := by
    rw [← hev 84 (by norm_num)]; exact (vt_evalF h (k := 145) (by norm_num)).2.2
  have hB : σ (.n 5666) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 9], 64)], [([84], 1), ([13, 84], 2), ([13, 84], 1)], [([52], 1), ([11, 52], 1), ([11, 51], 1)], [([53], 1), ([11, 53], 1), ([11, 52], 1)]] := by
    simp only [v4637, v4409, v4405, v4401, v4119, v4111, v4090, v4032, a5241, a5240, a5239, e5238, a5237,
      a5236, e5235, a5234, a5233, e5232, a5231, a5230, e5229, a5228, e5227, a4623, a4622,
      a4621, a4620, a4619, a4618, a4617, a4616, a4615, a4614, a4613, a4612, a4611, a4610,
      a4609, a4608, a4607, a4606, a4605, a4604, a4603, a4602]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5243, a5242, hB]

set_option maxRecDepth 10000 in
theorem vtB05_22F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5685) = σ (.n 5668) + σ (.n 1247) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 9], 128)], [([85], 1), ([13, 85], 2), ([13, 85], 1)], [([54], 1), ([11, 54], 1), ([11, 53], 1)], [([55], 1), ([11, 55], 1), ([11, 54], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4624 [
    .atom (.const (.n 5049) (word 2 0)),
    .atom (.const (.n 5050) (word 128 0)),
    .atom (.mul (.n 5051) (.n 4032) (.n 4090)),
    .atom (.mul (.n 5052) (.n 5050) (.n 5051)),
    .atom (.copy (.n 5053) (.n 5052)),
    .atom (.const (.n 5054) (word 2 0)),
    .atom (.mul (.n 5055) (.n 4119) (.n 4641)),
    .atom (.mul (.n 5056) (.n 5054) (.n 5055)),
    .atom (.add (.n 5057) (.n 4641) (.n 5056)),
    .atom (.mul (.n 5058) (.n 4119) (.n 4641)),
    .atom (.add (.n 5059) (.n 5057) (.n 5058)),
    .atom (.copy (.n 5060) (.n 5059)),
    .atom (.mul (.n 5061) (.n 4111) (.n 4413)),
    .atom (.add (.n 5062) (.n 4413) (.n 5061)),
    .atom (.mul (.n 5063) (.n 4111) (.n 4409)),
    .atom (.add (.n 5064) (.n 5062) (.n 5063)),
    .atom (.copy (.n 5065) (.n 5064)),
    .atom (.mul (.n 5066) (.n 4111) (.n 4430)),
    .atom (.add (.n 5067) (.n 4430) (.n 5066)),
    .atom (.mul (.n 5068) (.n 4111) (.n 4413)),
    .atom (.add (.n 5069) (.n 5067) (.n 5068)),
    .atom (.copy (.n 5070) (.n 5069))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4624, a4625, a4626, a4627, a4628, a4629, a4630, a4631, a4632, a4633, a4634, a4635, a4636, a4637,
    a4638, a4639, a4640, a4641, a4642, a4643, a4644, a4645, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5244 [
    .atom (.load (.n 5669) (.n 13) 0),
    .atom (.mul (.n 5670) (.n 5669) (.n 5049)),
    .atom (.load (.n 5671) (.n 13) 1),
    .atom (.mul (.n 5672) (.n 5671) (.n 5053)),
    .atom (.add (.n 5673) (.n 5670) (.n 5672)),
    .atom (.load (.n 5674) (.n 13) 2),
    .atom (.mul (.n 5675) (.n 5674) (.n 5060)),
    .atom (.add (.n 5676) (.n 5673) (.n 5675)),
    .atom (.load (.n 5677) (.n 13) 3),
    .atom (.mul (.n 5678) (.n 5677) (.n 5065)),
    .atom (.add (.n 5679) (.n 5676) (.n 5678)),
    .atom (.load (.n 5680) (.n 13) 4),
    .atom (.mul (.n 5681) (.n 5680) (.n 5070)),
    .atom (.add (.n 5682) (.n 5679) (.n 5681)),
    .atom (.add (.n 5683) (.n 14) (.n 5682)),
    .atom (.mul (.n 5684) (.n 1247) (.n 5683)),
    .atom (.add (.n 5685) (.n 5668) (.n 5684))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5244, a5245, a5246, a5247, a5248, a5249, a5250, a5251, a5252, a5253, a5254, a5255, a5256, a5257,
    a5258, a5259, a5260, -⟩ := hs1
  have e5244 := tb_loadHolds_unique a5244 (hw 0 (by norm_num))
  have e5246 := tb_loadHolds_unique a5246 (hw 1 (by norm_num))
  have e5249 := tb_loadHolds_unique a5249 (hw 2 (by norm_num))
  have e5252 := tb_loadHolds_unique a5252 (hw 3 (by norm_num))
  have e5255 := tb_loadHolds_unique a5255 (hw 4 (by norm_num))
  have v4032 : σ (.n 4032) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 62) (by norm_num)).2.2
  have v4090 : σ (.n 4090) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_evalF h (k := 70) (by norm_num)).2.2
  have v4111 : σ (.n 4111) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_evalF h (k := 72) (by norm_num)).2.2
  have v4119 : σ (.n 4119) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_evalF h (k := 74) (by norm_num)).2.2
  have v4409 : σ (.n 4409) = ev 53 := by
    rw [← hev 53 (by norm_num)]; exact (vt_evalF h (k := 114) (by norm_num)).2.2
  have v4413 : σ (.n 4413) = ev 54 := by
    rw [← hev 54 (by norm_num)]; exact (vt_evalF h (k := 115) (by norm_num)).2.2
  have v4430 : σ (.n 4430) = ev 55 := by
    rw [← hev 55 (by norm_num)]; exact (vt_evalF h (k := 116) (by norm_num)).2.2
  have v4641 : σ (.n 4641) = ev 85 := by
    rw [← hev 85 (by norm_num)]; exact (vt_evalF h (k := 146) (by norm_num)).2.2
  have hB : σ (.n 5683) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 9], 128)], [([85], 1), ([13, 85], 2), ([13, 85], 1)], [([54], 1), ([11, 54], 1), ([11, 53], 1)], [([55], 1), ([11, 55], 1), ([11, 54], 1)]] := by
    simp only [v4641, v4430, v4413, v4409, v4119, v4111, v4090, v4032, a5258, a5257, a5256, e5255, a5254,
      a5253, e5252, a5251, a5250, e5249, a5248, a5247, e5246, a5245, e5244, a4645, a4644,
      a4643, a4642, a4641, a4640, a4639, a4638, a4637, a4636, a4635, a4634, a4633, a4632,
      a4631, a4630, a4629, a4628, a4627, a4626, a4625, a4624]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5260, a5259, hB]

set_option maxRecDepth 10000 in
theorem vtB05_23F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5702) = σ (.n 5685) + σ (.n 1256) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 9], 256)], [([86], 1), ([13, 86], 2), ([13, 86], 1)], [([56], 1), ([11, 56], 1), ([11, 55], 1)], [([11, 56], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4646 [
    .atom (.const (.n 5071) (word 2 0)),
    .atom (.const (.n 5072) (word 256 0)),
    .atom (.mul (.n 5073) (.n 4032) (.n 4090)),
    .atom (.mul (.n 5074) (.n 5072) (.n 5073)),
    .atom (.copy (.n 5075) (.n 5074)),
    .atom (.const (.n 5076) (word 2 0)),
    .atom (.mul (.n 5077) (.n 4119) (.n 4645)),
    .atom (.mul (.n 5078) (.n 5076) (.n 5077)),
    .atom (.add (.n 5079) (.n 4645) (.n 5078)),
    .atom (.mul (.n 5080) (.n 4119) (.n 4645)),
    .atom (.add (.n 5081) (.n 5079) (.n 5080)),
    .atom (.copy (.n 5082) (.n 5081)),
    .atom (.mul (.n 5083) (.n 4111) (.n 4434)),
    .atom (.add (.n 5084) (.n 4434) (.n 5083)),
    .atom (.mul (.n 5085) (.n 4111) (.n 4430)),
    .atom (.add (.n 5086) (.n 5084) (.n 5085)),
    .atom (.copy (.n 5087) (.n 5086)),
    .atom (.mul (.n 5088) (.n 4111) (.n 4434)),
    .atom (.copy (.n 5089) (.n 5088))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4646, a4647, a4648, a4649, a4650, a4651, a4652, a4653, a4654, a4655, a4656, a4657, a4658, a4659,
    a4660, a4661, a4662, a4663, a4664, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5261 [
    .atom (.load (.n 5686) (.n 13) 0),
    .atom (.mul (.n 5687) (.n 5686) (.n 5071)),
    .atom (.load (.n 5688) (.n 13) 1),
    .atom (.mul (.n 5689) (.n 5688) (.n 5075)),
    .atom (.add (.n 5690) (.n 5687) (.n 5689)),
    .atom (.load (.n 5691) (.n 13) 2),
    .atom (.mul (.n 5692) (.n 5691) (.n 5082)),
    .atom (.add (.n 5693) (.n 5690) (.n 5692)),
    .atom (.load (.n 5694) (.n 13) 3),
    .atom (.mul (.n 5695) (.n 5694) (.n 5087)),
    .atom (.add (.n 5696) (.n 5693) (.n 5695)),
    .atom (.load (.n 5697) (.n 13) 4),
    .atom (.mul (.n 5698) (.n 5697) (.n 5089)),
    .atom (.add (.n 5699) (.n 5696) (.n 5698)),
    .atom (.add (.n 5700) (.n 14) (.n 5699)),
    .atom (.mul (.n 5701) (.n 1256) (.n 5700)),
    .atom (.add (.n 5702) (.n 5685) (.n 5701))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5261, a5262, a5263, a5264, a5265, a5266, a5267, a5268, a5269, a5270, a5271, a5272, a5273, a5274,
    a5275, a5276, a5277, -⟩ := hs1
  have e5261 := tb_loadHolds_unique a5261 (hw 0 (by norm_num))
  have e5263 := tb_loadHolds_unique a5263 (hw 1 (by norm_num))
  have e5266 := tb_loadHolds_unique a5266 (hw 2 (by norm_num))
  have e5269 := tb_loadHolds_unique a5269 (hw 3 (by norm_num))
  have e5272 := tb_loadHolds_unique a5272 (hw 4 (by norm_num))
  have v4032 : σ (.n 4032) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 62) (by norm_num)).2.2
  have v4090 : σ (.n 4090) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_evalF h (k := 70) (by norm_num)).2.2
  have v4111 : σ (.n 4111) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_evalF h (k := 72) (by norm_num)).2.2
  have v4119 : σ (.n 4119) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_evalF h (k := 74) (by norm_num)).2.2
  have v4430 : σ (.n 4430) = ev 55 := by
    rw [← hev 55 (by norm_num)]; exact (vt_evalF h (k := 116) (by norm_num)).2.2
  have v4434 : σ (.n 4434) = ev 56 := by
    rw [← hev 56 (by norm_num)]; exact (vt_evalF h (k := 117) (by norm_num)).2.2
  have v4645 : σ (.n 4645) = ev 86 := by
    rw [← hev 86 (by norm_num)]; exact (vt_evalF h (k := 147) (by norm_num)).2.2
  have hB : σ (.n 5700) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 9], 256)], [([86], 1), ([13, 86], 2), ([13, 86], 1)], [([56], 1), ([11, 56], 1), ([11, 55], 1)], [([11, 56], 1)]] := by
    simp only [v4645, v4434, v4430, v4119, v4111, v4090, v4032, a5275, a5274, a5273, e5272, a5271, a5270,
      e5269, a5268, a5267, e5266, a5265, a5264, e5263, a5262, e5261, a4664, a4663, a4662,
      a4661, a4660, a4659, a4658, a4657, a4656, a4655, a4654, a4653, a4652, a4651, a4650,
      a4649, a4648, a4647, a4646]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5277, a5276, hB]

set_option maxRecDepth 10000 in
theorem vtB05_24F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5719) = σ (.n 5702) + σ (.n 1265) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 9], 512)], [([87], 1), ([13, 87], 2), ([13, 87], 1)], [([57], 1)], [([58], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4665 [
    .atom (.const (.n 5090) (word 2 0)),
    .atom (.const (.n 5091) (word 512 0)),
    .atom (.mul (.n 5092) (.n 4032) (.n 4090)),
    .atom (.mul (.n 5093) (.n 5091) (.n 5092)),
    .atom (.copy (.n 5094) (.n 5093)),
    .atom (.const (.n 5095) (word 2 0)),
    .atom (.mul (.n 5096) (.n 4119) (.n 4662)),
    .atom (.mul (.n 5097) (.n 5095) (.n 5096)),
    .atom (.add (.n 5098) (.n 4662) (.n 5097)),
    .atom (.mul (.n 5099) (.n 4119) (.n 4662)),
    .atom (.add (.n 5100) (.n 5098) (.n 5099)),
    .atom (.copy (.n 5101) (.n 5100)),
    .atom (.copy (.n 5102) (.n 4438)),
    .atom (.copy (.n 5103) (.n 4442))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4665, a4666, a4667, a4668, a4669, a4670, a4671, a4672, a4673, a4674, a4675, a4676, a4677, a4678,
    -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5278 [
    .atom (.load (.n 5703) (.n 13) 0),
    .atom (.mul (.n 5704) (.n 5703) (.n 5090)),
    .atom (.load (.n 5705) (.n 13) 1),
    .atom (.mul (.n 5706) (.n 5705) (.n 5094)),
    .atom (.add (.n 5707) (.n 5704) (.n 5706)),
    .atom (.load (.n 5708) (.n 13) 2),
    .atom (.mul (.n 5709) (.n 5708) (.n 5101)),
    .atom (.add (.n 5710) (.n 5707) (.n 5709)),
    .atom (.load (.n 5711) (.n 13) 3),
    .atom (.mul (.n 5712) (.n 5711) (.n 5102)),
    .atom (.add (.n 5713) (.n 5710) (.n 5712)),
    .atom (.load (.n 5714) (.n 13) 4),
    .atom (.mul (.n 5715) (.n 5714) (.n 5103)),
    .atom (.add (.n 5716) (.n 5713) (.n 5715)),
    .atom (.add (.n 5717) (.n 14) (.n 5716)),
    .atom (.mul (.n 5718) (.n 1265) (.n 5717)),
    .atom (.add (.n 5719) (.n 5702) (.n 5718))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5278, a5279, a5280, a5281, a5282, a5283, a5284, a5285, a5286, a5287, a5288, a5289, a5290, a5291,
    a5292, a5293, a5294, -⟩ := hs1
  have e5278 := tb_loadHolds_unique a5278 (hw 0 (by norm_num))
  have e5280 := tb_loadHolds_unique a5280 (hw 1 (by norm_num))
  have e5283 := tb_loadHolds_unique a5283 (hw 2 (by norm_num))
  have e5286 := tb_loadHolds_unique a5286 (hw 3 (by norm_num))
  have e5289 := tb_loadHolds_unique a5289 (hw 4 (by norm_num))
  have v4032 : σ (.n 4032) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 62) (by norm_num)).2.2
  have v4090 : σ (.n 4090) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_evalF h (k := 70) (by norm_num)).2.2
  have v4119 : σ (.n 4119) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_evalF h (k := 74) (by norm_num)).2.2
  have v4438 : σ (.n 4438) = ev 57 := by
    rw [← hev 57 (by norm_num)]; exact (vt_evalF h (k := 118) (by norm_num)).2.2
  have v4442 : σ (.n 4442) = ev 58 := by
    rw [← hev 58 (by norm_num)]; exact (vt_evalF h (k := 119) (by norm_num)).2.2
  have v4662 : σ (.n 4662) = ev 87 := by
    rw [← hev 87 (by norm_num)]; exact (vt_evalF h (k := 148) (by norm_num)).2.2
  have hB : σ (.n 5717) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 9], 512)], [([87], 1), ([13, 87], 2), ([13, 87], 1)], [([57], 1)], [([58], 1)]] := by
    simp only [v4662, v4442, v4438, v4119, v4090, v4032, a5292, a5291, a5290, e5289, a5288, a5287, e5286,
      a5285, a5284, e5283, a5282, a5281, e5280, a5279, e5278, a4678, a4677, a4676, a4675,
      a4674, a4673, a4672, a4671, a4670, a4669, a4668, a4667, a4666, a4665]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5294, a5293, hB]

set_option maxRecDepth 10000 in
theorem vtB05_25F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5736) = σ (.n 5719) + σ (.n 1274) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 9], 1024)], [([88], 1), ([13, 88], 2), ([13, 88], 1)], [([59], 1)], [([60], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4679 [
    .atom (.const (.n 5104) (word 2 0)),
    .atom (.const (.n 5105) (word 1024 0)),
    .atom (.mul (.n 5106) (.n 4032) (.n 4090)),
    .atom (.mul (.n 5107) (.n 5105) (.n 5106)),
    .atom (.copy (.n 5108) (.n 5107)),
    .atom (.const (.n 5109) (word 2 0)),
    .atom (.mul (.n 5110) (.n 4119) (.n 4666)),
    .atom (.mul (.n 5111) (.n 5109) (.n 5110)),
    .atom (.add (.n 5112) (.n 4666) (.n 5111)),
    .atom (.mul (.n 5113) (.n 4119) (.n 4666)),
    .atom (.add (.n 5114) (.n 5112) (.n 5113)),
    .atom (.copy (.n 5115) (.n 5114)),
    .atom (.copy (.n 5116) (.n 4459)),
    .atom (.copy (.n 5117) (.n 4463))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4679, a4680, a4681, a4682, a4683, a4684, a4685, a4686, a4687, a4688, a4689, a4690, a4691, a4692,
    -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5295 [
    .atom (.load (.n 5720) (.n 13) 0),
    .atom (.mul (.n 5721) (.n 5720) (.n 5104)),
    .atom (.load (.n 5722) (.n 13) 1),
    .atom (.mul (.n 5723) (.n 5722) (.n 5108)),
    .atom (.add (.n 5724) (.n 5721) (.n 5723)),
    .atom (.load (.n 5725) (.n 13) 2),
    .atom (.mul (.n 5726) (.n 5725) (.n 5115)),
    .atom (.add (.n 5727) (.n 5724) (.n 5726)),
    .atom (.load (.n 5728) (.n 13) 3),
    .atom (.mul (.n 5729) (.n 5728) (.n 5116)),
    .atom (.add (.n 5730) (.n 5727) (.n 5729)),
    .atom (.load (.n 5731) (.n 13) 4),
    .atom (.mul (.n 5732) (.n 5731) (.n 5117)),
    .atom (.add (.n 5733) (.n 5730) (.n 5732)),
    .atom (.add (.n 5734) (.n 14) (.n 5733)),
    .atom (.mul (.n 5735) (.n 1274) (.n 5734)),
    .atom (.add (.n 5736) (.n 5719) (.n 5735))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5295, a5296, a5297, a5298, a5299, a5300, a5301, a5302, a5303, a5304, a5305, a5306, a5307, a5308,
    a5309, a5310, a5311, -⟩ := hs1
  have e5295 := tb_loadHolds_unique a5295 (hw 0 (by norm_num))
  have e5297 := tb_loadHolds_unique a5297 (hw 1 (by norm_num))
  have e5300 := tb_loadHolds_unique a5300 (hw 2 (by norm_num))
  have e5303 := tb_loadHolds_unique a5303 (hw 3 (by norm_num))
  have e5306 := tb_loadHolds_unique a5306 (hw 4 (by norm_num))
  have v4032 : σ (.n 4032) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 62) (by norm_num)).2.2
  have v4090 : σ (.n 4090) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_evalF h (k := 70) (by norm_num)).2.2
  have v4119 : σ (.n 4119) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_evalF h (k := 74) (by norm_num)).2.2
  have v4459 : σ (.n 4459) = ev 59 := by
    rw [← hev 59 (by norm_num)]; exact (vt_evalF h (k := 120) (by norm_num)).2.2
  have v4463 : σ (.n 4463) = ev 60 := by
    rw [← hev 60 (by norm_num)]; exact (vt_evalF h (k := 121) (by norm_num)).2.2
  have v4666 : σ (.n 4666) = ev 88 := by
    rw [← hev 88 (by norm_num)]; exact (vt_evalF h (k := 149) (by norm_num)).2.2
  have hB : σ (.n 5734) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 9], 1024)], [([88], 1), ([13, 88], 2), ([13, 88], 1)], [([59], 1)], [([60], 1)]] := by
    simp only [v4666, v4463, v4459, v4119, v4090, v4032, a5309, a5308, a5307, e5306, a5305, a5304, e5303,
      a5302, a5301, e5300, a5299, a5298, e5297, a5296, e5295, a4692, a4691, a4690, a4689,
      a4688, a4687, a4686, a4685, a4684, a4683, a4682, a4681, a4680, a4679]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5311, a5310, hB]

set_option maxRecDepth 10000 in
theorem vtB05_26F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5753) = σ (.n 5736) + σ (.n 1283) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 9], 2048)], [([89], 1), ([13, 89], 2), ([13, 89], 1)], [([61], 1)], [([62], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4693 [
    .atom (.const (.n 5118) (word 2 0)),
    .atom (.const (.n 5119) (word 2048 0)),
    .atom (.mul (.n 5120) (.n 4032) (.n 4090)),
    .atom (.mul (.n 5121) (.n 5119) (.n 5120)),
    .atom (.copy (.n 5122) (.n 5121)),
    .atom (.const (.n 5123) (word 2 0)),
    .atom (.mul (.n 5124) (.n 4119) (.n 4670)),
    .atom (.mul (.n 5125) (.n 5123) (.n 5124)),
    .atom (.add (.n 5126) (.n 4670) (.n 5125)),
    .atom (.mul (.n 5127) (.n 4119) (.n 4670)),
    .atom (.add (.n 5128) (.n 5126) (.n 5127)),
    .atom (.copy (.n 5129) (.n 5128)),
    .atom (.copy (.n 5130) (.n 4467)),
    .atom (.copy (.n 5131) (.n 4471))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4693, a4694, a4695, a4696, a4697, a4698, a4699, a4700, a4701, a4702, a4703, a4704, a4705, a4706,
    -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5312 [
    .atom (.load (.n 5737) (.n 13) 0),
    .atom (.mul (.n 5738) (.n 5737) (.n 5118)),
    .atom (.load (.n 5739) (.n 13) 1),
    .atom (.mul (.n 5740) (.n 5739) (.n 5122)),
    .atom (.add (.n 5741) (.n 5738) (.n 5740)),
    .atom (.load (.n 5742) (.n 13) 2),
    .atom (.mul (.n 5743) (.n 5742) (.n 5129)),
    .atom (.add (.n 5744) (.n 5741) (.n 5743)),
    .atom (.load (.n 5745) (.n 13) 3),
    .atom (.mul (.n 5746) (.n 5745) (.n 5130)),
    .atom (.add (.n 5747) (.n 5744) (.n 5746)),
    .atom (.load (.n 5748) (.n 13) 4),
    .atom (.mul (.n 5749) (.n 5748) (.n 5131)),
    .atom (.add (.n 5750) (.n 5747) (.n 5749)),
    .atom (.add (.n 5751) (.n 14) (.n 5750)),
    .atom (.mul (.n 5752) (.n 1283) (.n 5751)),
    .atom (.add (.n 5753) (.n 5736) (.n 5752))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5312, a5313, a5314, a5315, a5316, a5317, a5318, a5319, a5320, a5321, a5322, a5323, a5324, a5325,
    a5326, a5327, a5328, -⟩ := hs1
  have e5312 := tb_loadHolds_unique a5312 (hw 0 (by norm_num))
  have e5314 := tb_loadHolds_unique a5314 (hw 1 (by norm_num))
  have e5317 := tb_loadHolds_unique a5317 (hw 2 (by norm_num))
  have e5320 := tb_loadHolds_unique a5320 (hw 3 (by norm_num))
  have e5323 := tb_loadHolds_unique a5323 (hw 4 (by norm_num))
  have v4032 : σ (.n 4032) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 62) (by norm_num)).2.2
  have v4090 : σ (.n 4090) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_evalF h (k := 70) (by norm_num)).2.2
  have v4119 : σ (.n 4119) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_evalF h (k := 74) (by norm_num)).2.2
  have v4467 : σ (.n 4467) = ev 61 := by
    rw [← hev 61 (by norm_num)]; exact (vt_evalF h (k := 122) (by norm_num)).2.2
  have v4471 : σ (.n 4471) = ev 62 := by
    rw [← hev 62 (by norm_num)]; exact (vt_evalF h (k := 123) (by norm_num)).2.2
  have v4670 : σ (.n 4670) = ev 89 := by
    rw [← hev 89 (by norm_num)]; exact (vt_evalF h (k := 150) (by norm_num)).2.2
  have hB : σ (.n 5751) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 9], 2048)], [([89], 1), ([13, 89], 2), ([13, 89], 1)], [([61], 1)], [([62], 1)]] := by
    simp only [v4670, v4471, v4467, v4119, v4090, v4032, a5326, a5325, a5324, e5323, a5322, a5321, e5320,
      a5319, a5318, e5317, a5316, a5315, e5314, a5313, e5312, a4706, a4705, a4704, a4703,
      a4702, a4701, a4700, a4699, a4698, a4697, a4696, a4695, a4694, a4693]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5328, a5327, hB]

set_option maxRecDepth 10000 in
theorem vtB05_27F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5770) = σ (.n 5753) + σ (.n 1292) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 9], 4096)], [([90], 1), ([13, 90], 2), ([13, 90], 1)], [([63], 1)], [([64], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4707 [
    .atom (.const (.n 5132) (word 2 0)),
    .atom (.const (.n 5133) (word 4096 0)),
    .atom (.mul (.n 5134) (.n 4032) (.n 4090)),
    .atom (.mul (.n 5135) (.n 5133) (.n 5134)),
    .atom (.copy (.n 5136) (.n 5135)),
    .atom (.const (.n 5137) (word 2 0)),
    .atom (.mul (.n 5138) (.n 4119) (.n 4674)),
    .atom (.mul (.n 5139) (.n 5137) (.n 5138)),
    .atom (.add (.n 5140) (.n 4674) (.n 5139)),
    .atom (.mul (.n 5141) (.n 4119) (.n 4674)),
    .atom (.add (.n 5142) (.n 5140) (.n 5141)),
    .atom (.copy (.n 5143) (.n 5142)),
    .atom (.copy (.n 5144) (.n 4488)),
    .atom (.copy (.n 5145) (.n 4492))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4707, a4708, a4709, a4710, a4711, a4712, a4713, a4714, a4715, a4716, a4717, a4718, a4719, a4720,
    -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5329 [
    .atom (.load (.n 5754) (.n 13) 0),
    .atom (.mul (.n 5755) (.n 5754) (.n 5132)),
    .atom (.load (.n 5756) (.n 13) 1),
    .atom (.mul (.n 5757) (.n 5756) (.n 5136)),
    .atom (.add (.n 5758) (.n 5755) (.n 5757)),
    .atom (.load (.n 5759) (.n 13) 2),
    .atom (.mul (.n 5760) (.n 5759) (.n 5143)),
    .atom (.add (.n 5761) (.n 5758) (.n 5760)),
    .atom (.load (.n 5762) (.n 13) 3),
    .atom (.mul (.n 5763) (.n 5762) (.n 5144)),
    .atom (.add (.n 5764) (.n 5761) (.n 5763)),
    .atom (.load (.n 5765) (.n 13) 4),
    .atom (.mul (.n 5766) (.n 5765) (.n 5145)),
    .atom (.add (.n 5767) (.n 5764) (.n 5766)),
    .atom (.add (.n 5768) (.n 14) (.n 5767)),
    .atom (.mul (.n 5769) (.n 1292) (.n 5768)),
    .atom (.add (.n 5770) (.n 5753) (.n 5769))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5329, a5330, a5331, a5332, a5333, a5334, a5335, a5336, a5337, a5338, a5339, a5340, a5341, a5342,
    a5343, a5344, a5345, -⟩ := hs1
  have e5329 := tb_loadHolds_unique a5329 (hw 0 (by norm_num))
  have e5331 := tb_loadHolds_unique a5331 (hw 1 (by norm_num))
  have e5334 := tb_loadHolds_unique a5334 (hw 2 (by norm_num))
  have e5337 := tb_loadHolds_unique a5337 (hw 3 (by norm_num))
  have e5340 := tb_loadHolds_unique a5340 (hw 4 (by norm_num))
  have v4032 : σ (.n 4032) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 62) (by norm_num)).2.2
  have v4090 : σ (.n 4090) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_evalF h (k := 70) (by norm_num)).2.2
  have v4119 : σ (.n 4119) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_evalF h (k := 74) (by norm_num)).2.2
  have v4488 : σ (.n 4488) = ev 63 := by
    rw [← hev 63 (by norm_num)]; exact (vt_evalF h (k := 124) (by norm_num)).2.2
  have v4492 : σ (.n 4492) = ev 64 := by
    rw [← hev 64 (by norm_num)]; exact (vt_evalF h (k := 125) (by norm_num)).2.2
  have v4674 : σ (.n 4674) = ev 90 := by
    rw [← hev 90 (by norm_num)]; exact (vt_evalF h (k := 151) (by norm_num)).2.2
  have hB : σ (.n 5768) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 9], 4096)], [([90], 1), ([13, 90], 2), ([13, 90], 1)], [([63], 1)], [([64], 1)]] := by
    simp only [v4674, v4492, v4488, v4119, v4090, v4032, a5343, a5342, a5341, e5340, a5339, a5338, e5337,
      a5336, a5335, e5334, a5333, a5332, e5331, a5330, e5329, a4720, a4719, a4718, a4717,
      a4716, a4715, a4714, a4713, a4712, a4711, a4710, a4709, a4708, a4707]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5345, a5344, hB]

end
end LeanVM.Guest.B1.Tables
