/-
  LeanVM.Guest.B1.Tables.Vt.FormsT5a

  Table 5's blocks' values on the push side, from the guest's statements.
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
    σ (.n 5277) = σ (.n 1048) * vtBlockVal (σ (.n 14)) W ev
      [[([], 1)], [([0], 2)], [([1], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4267 [
    .atom (.const (.n 4691) (word 1 0)),
    .atom (.const (.n 4692) (word 2 0)),
    .atom (.mul (.n 4693) (.n 4692) (.n 4027)),
    .atom (.copy (.n 4694) (.n 4693)),
    .atom (.copy (.n 4695) (.n 4031))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4267, a4268, a4269, a4270, a4271, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 4844 [
    .atom (.load (.n 5268) (.n 13) 0),
    .atom (.mul (.n 5269) (.n 5268) (.n 4691)),
    .atom (.load (.n 5270) (.n 13) 1),
    .atom (.mul (.n 5271) (.n 5270) (.n 4694)),
    .atom (.add (.n 5272) (.n 5269) (.n 5271)),
    .atom (.load (.n 5273) (.n 13) 2),
    .atom (.mul (.n 5274) (.n 5273) (.n 4695)),
    .atom (.add (.n 5275) (.n 5272) (.n 5274)),
    .atom (.add (.n 5276) (.n 14) (.n 5275)),
    .atom (.mul (.n 5277) (.n 1048) (.n 5276))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a4844, a4845, a4846, a4847, a4848, a4849, a4850, a4851, a4852, a4853, -⟩ := hs1
  have e4844 := tb_loadHolds_unique a4844 (hw 0 (by norm_num))
  have e4846 := tb_loadHolds_unique a4846 (hw 1 (by norm_num))
  have e4849 := tb_loadHolds_unique a4849 (hw 2 (by norm_num))
  have v4027 : σ (.n 4027) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_eval h (k := 61) (by norm_num)).2.2
  have v4031 : σ (.n 4031) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 62) (by norm_num)).2.2
  have hB : σ (.n 5276) = vtBlockVal (σ (.n 14)) W ev [[([], 1)], [([0], 2)], [([1], 1)]] := by
    simp only [v4031, v4027, a4852, a4851, a4850, e4849, a4848, a4847, e4846, a4845, e4844, a4271, a4270,
      a4269, a4268, a4267]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a4853, hB]

set_option maxRecDepth 10000 in
theorem vtB05_1 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5327) = σ (.n 5277) + σ (.n 1057) * vtBlockVal (σ (.n 14)) W ev
      [[([], 4)], [([0], 1)], [([91], 2)], [([], 32)], [([2], 1)], [([3], 1)], [([4], 1)], [([5], 1)], [([6], 1)], [([7], 1)], [([8], 1)], [([9], 1)], [([10], 1)], [([11], 1)], [([12], 1)], [([13], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4272 [
    .atom (.const (.n 4696) (word 4 0)),
    .atom (.copy (.n 4697) (.n 4027)),
    .atom (.const (.n 4698) (word 2 0)),
    .atom (.mul (.n 4699) (.n 4698) (.n 4690)),
    .atom (.copy (.n 4700) (.n 4699)),
    .atom (.const (.n 4701) (word 32 0)),
    .atom (.copy (.n 4702) (.n 4035)),
    .atom (.copy (.n 4703) (.n 4052)),
    .atom (.copy (.n 4704) (.n 4056)),
    .atom (.copy (.n 4705) (.n 4060)),
    .atom (.copy (.n 4706) (.n 4064)),
    .atom (.copy (.n 4707) (.n 4081)),
    .atom (.copy (.n 4708) (.n 4085)),
    .atom (.copy (.n 4709) (.n 4089)),
    .atom (.copy (.n 4710) (.n 4093)),
    .atom (.copy (.n 4711) (.n 4110)),
    .atom (.copy (.n 4712) (.n 4114)),
    .atom (.copy (.n 4713) (.n 4118))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4272, a4273, a4274, a4275, a4276, a4277, a4278, a4279, a4280, a4281, a4282, a4283, a4284, a4285,
    a4286, a4287, a4288, a4289, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 4854 [
    .atom (.load (.n 5278) (.n 13) 0),
    .atom (.mul (.n 5279) (.n 5278) (.n 4696)),
    .atom (.load (.n 5280) (.n 13) 1),
    .atom (.mul (.n 5281) (.n 5280) (.n 4697)),
    .atom (.add (.n 5282) (.n 5279) (.n 5281)),
    .atom (.load (.n 5283) (.n 13) 2),
    .atom (.mul (.n 5284) (.n 5283) (.n 4700)),
    .atom (.add (.n 5285) (.n 5282) (.n 5284)),
    .atom (.load (.n 5286) (.n 13) 3),
    .atom (.mul (.n 5287) (.n 5286) (.n 4701)),
    .atom (.add (.n 5288) (.n 5285) (.n 5287)),
    .atom (.load (.n 5289) (.n 13) 4),
    .atom (.mul (.n 5290) (.n 5289) (.n 4702)),
    .atom (.add (.n 5291) (.n 5288) (.n 5290)),
    .atom (.load (.n 5292) (.n 13) 5),
    .atom (.mul (.n 5293) (.n 5292) (.n 4703)),
    .atom (.add (.n 5294) (.n 5291) (.n 5293)),
    .atom (.load (.n 5295) (.n 13) 6),
    .atom (.mul (.n 5296) (.n 5295) (.n 4704)),
    .atom (.add (.n 5297) (.n 5294) (.n 5296)),
    .atom (.load (.n 5298) (.n 13) 7),
    .atom (.mul (.n 5299) (.n 5298) (.n 4705)),
    .atom (.add (.n 5300) (.n 5297) (.n 5299)),
    .atom (.load (.n 5301) (.n 13) 8),
    .atom (.mul (.n 5302) (.n 5301) (.n 4706)),
    .atom (.add (.n 5303) (.n 5300) (.n 5302)),
    .atom (.load (.n 5304) (.n 13) 9),
    .atom (.mul (.n 5305) (.n 5304) (.n 4707)),
    .atom (.add (.n 5306) (.n 5303) (.n 5305)),
    .atom (.load (.n 5307) (.n 13) 10),
    .atom (.mul (.n 5308) (.n 5307) (.n 4708)),
    .atom (.add (.n 5309) (.n 5306) (.n 5308)),
    .atom (.load (.n 5310) (.n 13) 11),
    .atom (.mul (.n 5311) (.n 5310) (.n 4709)),
    .atom (.add (.n 5312) (.n 5309) (.n 5311)),
    .atom (.load (.n 5313) (.n 13) 12),
    .atom (.mul (.n 5314) (.n 5313) (.n 4710)),
    .atom (.add (.n 5315) (.n 5312) (.n 5314)),
    .atom (.load (.n 5316) (.n 13) 13),
    .atom (.mul (.n 5317) (.n 5316) (.n 4711)),
    .atom (.add (.n 5318) (.n 5315) (.n 5317)),
    .atom (.load (.n 5319) (.n 13) 14),
    .atom (.mul (.n 5320) (.n 5319) (.n 4712)),
    .atom (.add (.n 5321) (.n 5318) (.n 5320)),
    .atom (.load (.n 5322) (.n 13) 15),
    .atom (.mul (.n 5323) (.n 5322) (.n 4713)),
    .atom (.add (.n 5324) (.n 5321) (.n 5323)),
    .atom (.add (.n 5325) (.n 14) (.n 5324)),
    .atom (.mul (.n 5326) (.n 1057) (.n 5325)),
    .atom (.add (.n 5327) (.n 5277) (.n 5326))] (by decide +kernel)
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
  have v4027 : σ (.n 4027) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_eval h (k := 61) (by norm_num)).2.2
  have v4035 : σ (.n 4035) = ev 2 := by
    rw [← hev 2 (by norm_num)]; exact (vt_eval h (k := 63) (by norm_num)).2.2
  have v4052 : σ (.n 4052) = ev 3 := by
    rw [← hev 3 (by norm_num)]; exact (vt_eval h (k := 64) (by norm_num)).2.2
  have v4056 : σ (.n 4056) = ev 4 := by
    rw [← hev 4 (by norm_num)]; exact (vt_eval h (k := 65) (by norm_num)).2.2
  have v4060 : σ (.n 4060) = ev 5 := by
    rw [← hev 5 (by norm_num)]; exact (vt_eval h (k := 66) (by norm_num)).2.2
  have v4064 : σ (.n 4064) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_eval h (k := 67) (by norm_num)).2.2
  have v4081 : σ (.n 4081) = ev 7 := by
    rw [← hev 7 (by norm_num)]; exact (vt_eval h (k := 68) (by norm_num)).2.2
  have v4085 : σ (.n 4085) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_eval h (k := 69) (by norm_num)).2.2
  have v4089 : σ (.n 4089) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 70) (by norm_num)).2.2
  have v4093 : σ (.n 4093) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_eval h (k := 71) (by norm_num)).2.2
  have v4110 : σ (.n 4110) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_eval h (k := 72) (by norm_num)).2.2
  have v4114 : σ (.n 4114) = ev 12 := by
    rw [← hev 12 (by norm_num)]; exact (vt_eval h (k := 73) (by norm_num)).2.2
  have v4118 : σ (.n 4118) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 74) (by norm_num)).2.2
  have v4690 : σ (.n 4690) = ev 91 := by
    rw [← hev 91 (by norm_num)]; exact (vt_eval h (k := 152) (by norm_num)).2.2
  have hB : σ (.n 5325) = vtBlockVal (σ (.n 14)) W ev [[([], 4)], [([0], 1)], [([91], 2)], [([], 32)], [([2], 1)], [([3], 1)], [([4], 1)], [([5], 1)], [([6], 1)], [([7], 1)], [([8], 1)], [([9], 1)], [([10], 1)], [([11], 1)], [([12], 1)], [([13], 1)]] := by
    simp only [v4690, v4118, v4114, v4110, v4093, v4089, v4085, v4081, v4064, v4060, v4056, v4052, v4035,
      v4027, a4901, a4900, a4899, e4898, a4897, a4896, e4895, a4894, a4893, e4892, a4891,
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
theorem vtB05_2 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5344) = σ (.n 5327) + σ (.n 1066) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 2], 1)], [([65], 2)], [([15], 1), ([10, 15], 1), ([10, 14], 1)], [([16], 1), ([10, 16], 1), ([10, 15], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4290 [
    .atom (.const (.n 4714) (word 2 0)),
    .atom (.mul (.n 4715) (.n 4031) (.n 4035)),
    .atom (.copy (.n 4716) (.n 4715)),
    .atom (.const (.n 4717) (word 2 0)),
    .atom (.mul (.n 4718) (.n 4717) (.n 4495)),
    .atom (.copy (.n 4719) (.n 4718)),
    .atom (.mul (.n 4720) (.n 4093) (.n 4139)),
    .atom (.add (.n 4721) (.n 4139) (.n 4720)),
    .atom (.mul (.n 4722) (.n 4093) (.n 4122)),
    .atom (.add (.n 4723) (.n 4721) (.n 4722)),
    .atom (.copy (.n 4724) (.n 4723)),
    .atom (.mul (.n 4725) (.n 4093) (.n 4143)),
    .atom (.add (.n 4726) (.n 4143) (.n 4725)),
    .atom (.mul (.n 4727) (.n 4093) (.n 4139)),
    .atom (.add (.n 4728) (.n 4726) (.n 4727)),
    .atom (.copy (.n 4729) (.n 4728))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4290, a4291, a4292, a4293, a4294, a4295, a4296, a4297, a4298, a4299, a4300, a4301, a4302, a4303,
    a4304, a4305, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 4904 [
    .atom (.load (.n 5328) (.n 13) 0),
    .atom (.mul (.n 5329) (.n 5328) (.n 4714)),
    .atom (.load (.n 5330) (.n 13) 1),
    .atom (.mul (.n 5331) (.n 5330) (.n 4716)),
    .atom (.add (.n 5332) (.n 5329) (.n 5331)),
    .atom (.load (.n 5333) (.n 13) 2),
    .atom (.mul (.n 5334) (.n 5333) (.n 4719)),
    .atom (.add (.n 5335) (.n 5332) (.n 5334)),
    .atom (.load (.n 5336) (.n 13) 3),
    .atom (.mul (.n 5337) (.n 5336) (.n 4724)),
    .atom (.add (.n 5338) (.n 5335) (.n 5337)),
    .atom (.load (.n 5339) (.n 13) 4),
    .atom (.mul (.n 5340) (.n 5339) (.n 4729)),
    .atom (.add (.n 5341) (.n 5338) (.n 5340)),
    .atom (.add (.n 5342) (.n 14) (.n 5341)),
    .atom (.mul (.n 5343) (.n 1066) (.n 5342)),
    .atom (.add (.n 5344) (.n 5327) (.n 5343))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a4904, a4905, a4906, a4907, a4908, a4909, a4910, a4911, a4912, a4913, a4914, a4915, a4916, a4917,
    a4918, a4919, a4920, -⟩ := hs1
  have e4904 := tb_loadHolds_unique a4904 (hw 0 (by norm_num))
  have e4906 := tb_loadHolds_unique a4906 (hw 1 (by norm_num))
  have e4909 := tb_loadHolds_unique a4909 (hw 2 (by norm_num))
  have e4912 := tb_loadHolds_unique a4912 (hw 3 (by norm_num))
  have e4915 := tb_loadHolds_unique a4915 (hw 4 (by norm_num))
  have v4031 : σ (.n 4031) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 62) (by norm_num)).2.2
  have v4035 : σ (.n 4035) = ev 2 := by
    rw [← hev 2 (by norm_num)]; exact (vt_eval h (k := 63) (by norm_num)).2.2
  have v4093 : σ (.n 4093) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_eval h (k := 71) (by norm_num)).2.2
  have v4122 : σ (.n 4122) = ev 14 := by
    rw [← hev 14 (by norm_num)]; exact (vt_eval h (k := 75) (by norm_num)).2.2
  have v4139 : σ (.n 4139) = ev 15 := by
    rw [← hev 15 (by norm_num)]; exact (vt_eval h (k := 76) (by norm_num)).2.2
  have v4143 : σ (.n 4143) = ev 16 := by
    rw [← hev 16 (by norm_num)]; exact (vt_eval h (k := 77) (by norm_num)).2.2
  have v4495 : σ (.n 4495) = ev 65 := by
    rw [← hev 65 (by norm_num)]; exact (vt_eval h (k := 126) (by norm_num)).2.2
  have hB : σ (.n 5342) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 2], 1)], [([65], 2)], [([15], 1), ([10, 15], 1), ([10, 14], 1)], [([16], 1), ([10, 16], 1), ([10, 15], 1)]] := by
    simp only [v4495, v4143, v4139, v4122, v4093, v4035, v4031, a4918, a4917, a4916, e4915, a4914, a4913,
      e4912, a4911, a4910, e4909, a4908, a4907, e4906, a4905, e4904, a4305, a4304, a4303,
      a4302, a4301, a4300, a4299, a4298, a4297, a4296, a4295, a4294, a4293, a4292, a4291,
      a4290]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a4920, a4919, hB]

set_option maxRecDepth 10000 in
theorem vtB05_3 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5361) = σ (.n 5344) + σ (.n 1075) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 3], 1)], [([66], 2)], [([17], 1), ([10, 17], 1), ([10, 16], 1)], [([18], 1), ([10, 18], 1), ([10, 17], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4306 [
    .atom (.const (.n 4730) (word 2 0)),
    .atom (.mul (.n 4731) (.n 4031) (.n 4052)),
    .atom (.copy (.n 4732) (.n 4731)),
    .atom (.const (.n 4733) (word 2 0)),
    .atom (.mul (.n 4734) (.n 4733) (.n 4499)),
    .atom (.copy (.n 4735) (.n 4734)),
    .atom (.mul (.n 4736) (.n 4093) (.n 4147)),
    .atom (.add (.n 4737) (.n 4147) (.n 4736)),
    .atom (.mul (.n 4738) (.n 4093) (.n 4143)),
    .atom (.add (.n 4739) (.n 4737) (.n 4738)),
    .atom (.copy (.n 4740) (.n 4739)),
    .atom (.mul (.n 4741) (.n 4093) (.n 4151)),
    .atom (.add (.n 4742) (.n 4151) (.n 4741)),
    .atom (.mul (.n 4743) (.n 4093) (.n 4147)),
    .atom (.add (.n 4744) (.n 4742) (.n 4743)),
    .atom (.copy (.n 4745) (.n 4744))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4306, a4307, a4308, a4309, a4310, a4311, a4312, a4313, a4314, a4315, a4316, a4317, a4318, a4319,
    a4320, a4321, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 4921 [
    .atom (.load (.n 5345) (.n 13) 0),
    .atom (.mul (.n 5346) (.n 5345) (.n 4730)),
    .atom (.load (.n 5347) (.n 13) 1),
    .atom (.mul (.n 5348) (.n 5347) (.n 4732)),
    .atom (.add (.n 5349) (.n 5346) (.n 5348)),
    .atom (.load (.n 5350) (.n 13) 2),
    .atom (.mul (.n 5351) (.n 5350) (.n 4735)),
    .atom (.add (.n 5352) (.n 5349) (.n 5351)),
    .atom (.load (.n 5353) (.n 13) 3),
    .atom (.mul (.n 5354) (.n 5353) (.n 4740)),
    .atom (.add (.n 5355) (.n 5352) (.n 5354)),
    .atom (.load (.n 5356) (.n 13) 4),
    .atom (.mul (.n 5357) (.n 5356) (.n 4745)),
    .atom (.add (.n 5358) (.n 5355) (.n 5357)),
    .atom (.add (.n 5359) (.n 14) (.n 5358)),
    .atom (.mul (.n 5360) (.n 1075) (.n 5359)),
    .atom (.add (.n 5361) (.n 5344) (.n 5360))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a4921, a4922, a4923, a4924, a4925, a4926, a4927, a4928, a4929, a4930, a4931, a4932, a4933, a4934,
    a4935, a4936, a4937, -⟩ := hs1
  have e4921 := tb_loadHolds_unique a4921 (hw 0 (by norm_num))
  have e4923 := tb_loadHolds_unique a4923 (hw 1 (by norm_num))
  have e4926 := tb_loadHolds_unique a4926 (hw 2 (by norm_num))
  have e4929 := tb_loadHolds_unique a4929 (hw 3 (by norm_num))
  have e4932 := tb_loadHolds_unique a4932 (hw 4 (by norm_num))
  have v4031 : σ (.n 4031) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 62) (by norm_num)).2.2
  have v4052 : σ (.n 4052) = ev 3 := by
    rw [← hev 3 (by norm_num)]; exact (vt_eval h (k := 64) (by norm_num)).2.2
  have v4093 : σ (.n 4093) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_eval h (k := 71) (by norm_num)).2.2
  have v4143 : σ (.n 4143) = ev 16 := by
    rw [← hev 16 (by norm_num)]; exact (vt_eval h (k := 77) (by norm_num)).2.2
  have v4147 : σ (.n 4147) = ev 17 := by
    rw [← hev 17 (by norm_num)]; exact (vt_eval h (k := 78) (by norm_num)).2.2
  have v4151 : σ (.n 4151) = ev 18 := by
    rw [← hev 18 (by norm_num)]; exact (vt_eval h (k := 79) (by norm_num)).2.2
  have v4499 : σ (.n 4499) = ev 66 := by
    rw [← hev 66 (by norm_num)]; exact (vt_eval h (k := 127) (by norm_num)).2.2
  have hB : σ (.n 5359) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 3], 1)], [([66], 2)], [([17], 1), ([10, 17], 1), ([10, 16], 1)], [([18], 1), ([10, 18], 1), ([10, 17], 1)]] := by
    simp only [v4499, v4151, v4147, v4143, v4093, v4052, v4031, a4935, a4934, a4933, e4932, a4931, a4930,
      e4929, a4928, a4927, e4926, a4925, a4924, e4923, a4922, e4921, a4321, a4320, a4319,
      a4318, a4317, a4316, a4315, a4314, a4313, a4312, a4311, a4310, a4309, a4308, a4307,
      a4306]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a4937, a4936, hB]

set_option maxRecDepth 10000 in
theorem vtB05_4 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5378) = σ (.n 5361) + σ (.n 1084) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 4], 1)], [([67], 2)], [([19], 1), ([10, 19], 1), ([10, 18], 1)], [([20], 1), ([10, 20], 1), ([10, 19], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4322 [
    .atom (.const (.n 4746) (word 2 0)),
    .atom (.mul (.n 4747) (.n 4031) (.n 4056)),
    .atom (.copy (.n 4748) (.n 4747)),
    .atom (.const (.n 4749) (word 2 0)),
    .atom (.mul (.n 4750) (.n 4749) (.n 4516)),
    .atom (.copy (.n 4751) (.n 4750)),
    .atom (.mul (.n 4752) (.n 4093) (.n 4168)),
    .atom (.add (.n 4753) (.n 4168) (.n 4752)),
    .atom (.mul (.n 4754) (.n 4093) (.n 4151)),
    .atom (.add (.n 4755) (.n 4753) (.n 4754)),
    .atom (.copy (.n 4756) (.n 4755)),
    .atom (.mul (.n 4757) (.n 4093) (.n 4172)),
    .atom (.add (.n 4758) (.n 4172) (.n 4757)),
    .atom (.mul (.n 4759) (.n 4093) (.n 4168)),
    .atom (.add (.n 4760) (.n 4758) (.n 4759)),
    .atom (.copy (.n 4761) (.n 4760))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4322, a4323, a4324, a4325, a4326, a4327, a4328, a4329, a4330, a4331, a4332, a4333, a4334, a4335,
    a4336, a4337, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 4938 [
    .atom (.load (.n 5362) (.n 13) 0),
    .atom (.mul (.n 5363) (.n 5362) (.n 4746)),
    .atom (.load (.n 5364) (.n 13) 1),
    .atom (.mul (.n 5365) (.n 5364) (.n 4748)),
    .atom (.add (.n 5366) (.n 5363) (.n 5365)),
    .atom (.load (.n 5367) (.n 13) 2),
    .atom (.mul (.n 5368) (.n 5367) (.n 4751)),
    .atom (.add (.n 5369) (.n 5366) (.n 5368)),
    .atom (.load (.n 5370) (.n 13) 3),
    .atom (.mul (.n 5371) (.n 5370) (.n 4756)),
    .atom (.add (.n 5372) (.n 5369) (.n 5371)),
    .atom (.load (.n 5373) (.n 13) 4),
    .atom (.mul (.n 5374) (.n 5373) (.n 4761)),
    .atom (.add (.n 5375) (.n 5372) (.n 5374)),
    .atom (.add (.n 5376) (.n 14) (.n 5375)),
    .atom (.mul (.n 5377) (.n 1084) (.n 5376)),
    .atom (.add (.n 5378) (.n 5361) (.n 5377))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a4938, a4939, a4940, a4941, a4942, a4943, a4944, a4945, a4946, a4947, a4948, a4949, a4950, a4951,
    a4952, a4953, a4954, -⟩ := hs1
  have e4938 := tb_loadHolds_unique a4938 (hw 0 (by norm_num))
  have e4940 := tb_loadHolds_unique a4940 (hw 1 (by norm_num))
  have e4943 := tb_loadHolds_unique a4943 (hw 2 (by norm_num))
  have e4946 := tb_loadHolds_unique a4946 (hw 3 (by norm_num))
  have e4949 := tb_loadHolds_unique a4949 (hw 4 (by norm_num))
  have v4031 : σ (.n 4031) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 62) (by norm_num)).2.2
  have v4056 : σ (.n 4056) = ev 4 := by
    rw [← hev 4 (by norm_num)]; exact (vt_eval h (k := 65) (by norm_num)).2.2
  have v4093 : σ (.n 4093) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_eval h (k := 71) (by norm_num)).2.2
  have v4151 : σ (.n 4151) = ev 18 := by
    rw [← hev 18 (by norm_num)]; exact (vt_eval h (k := 79) (by norm_num)).2.2
  have v4168 : σ (.n 4168) = ev 19 := by
    rw [← hev 19 (by norm_num)]; exact (vt_eval h (k := 80) (by norm_num)).2.2
  have v4172 : σ (.n 4172) = ev 20 := by
    rw [← hev 20 (by norm_num)]; exact (vt_eval h (k := 81) (by norm_num)).2.2
  have v4516 : σ (.n 4516) = ev 67 := by
    rw [← hev 67 (by norm_num)]; exact (vt_eval h (k := 128) (by norm_num)).2.2
  have hB : σ (.n 5376) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 4], 1)], [([67], 2)], [([19], 1), ([10, 19], 1), ([10, 18], 1)], [([20], 1), ([10, 20], 1), ([10, 19], 1)]] := by
    simp only [v4516, v4172, v4168, v4151, v4093, v4056, v4031, a4952, a4951, a4950, e4949, a4948, a4947,
      e4946, a4945, a4944, e4943, a4942, a4941, e4940, a4939, e4938, a4337, a4336, a4335,
      a4334, a4333, a4332, a4331, a4330, a4329, a4328, a4327, a4326, a4325, a4324, a4323,
      a4322]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a4954, a4953, hB]

set_option maxRecDepth 10000 in
theorem vtB05_5 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5395) = σ (.n 5378) + σ (.n 1093) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 5], 1)], [([68], 2)], [([21], 1), ([10, 21], 1), ([10, 20], 1)], [([22], 1), ([10, 22], 1), ([10, 21], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4338 [
    .atom (.const (.n 4762) (word 2 0)),
    .atom (.mul (.n 4763) (.n 4031) (.n 4060)),
    .atom (.copy (.n 4764) (.n 4763)),
    .atom (.const (.n 4765) (word 2 0)),
    .atom (.mul (.n 4766) (.n 4765) (.n 4520)),
    .atom (.copy (.n 4767) (.n 4766)),
    .atom (.mul (.n 4768) (.n 4093) (.n 4176)),
    .atom (.add (.n 4769) (.n 4176) (.n 4768)),
    .atom (.mul (.n 4770) (.n 4093) (.n 4172)),
    .atom (.add (.n 4771) (.n 4769) (.n 4770)),
    .atom (.copy (.n 4772) (.n 4771)),
    .atom (.mul (.n 4773) (.n 4093) (.n 4180)),
    .atom (.add (.n 4774) (.n 4180) (.n 4773)),
    .atom (.mul (.n 4775) (.n 4093) (.n 4176)),
    .atom (.add (.n 4776) (.n 4774) (.n 4775)),
    .atom (.copy (.n 4777) (.n 4776))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4338, a4339, a4340, a4341, a4342, a4343, a4344, a4345, a4346, a4347, a4348, a4349, a4350, a4351,
    a4352, a4353, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 4955 [
    .atom (.load (.n 5379) (.n 13) 0),
    .atom (.mul (.n 5380) (.n 5379) (.n 4762)),
    .atom (.load (.n 5381) (.n 13) 1),
    .atom (.mul (.n 5382) (.n 5381) (.n 4764)),
    .atom (.add (.n 5383) (.n 5380) (.n 5382)),
    .atom (.load (.n 5384) (.n 13) 2),
    .atom (.mul (.n 5385) (.n 5384) (.n 4767)),
    .atom (.add (.n 5386) (.n 5383) (.n 5385)),
    .atom (.load (.n 5387) (.n 13) 3),
    .atom (.mul (.n 5388) (.n 5387) (.n 4772)),
    .atom (.add (.n 5389) (.n 5386) (.n 5388)),
    .atom (.load (.n 5390) (.n 13) 4),
    .atom (.mul (.n 5391) (.n 5390) (.n 4777)),
    .atom (.add (.n 5392) (.n 5389) (.n 5391)),
    .atom (.add (.n 5393) (.n 14) (.n 5392)),
    .atom (.mul (.n 5394) (.n 1093) (.n 5393)),
    .atom (.add (.n 5395) (.n 5378) (.n 5394))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a4955, a4956, a4957, a4958, a4959, a4960, a4961, a4962, a4963, a4964, a4965, a4966, a4967, a4968,
    a4969, a4970, a4971, -⟩ := hs1
  have e4955 := tb_loadHolds_unique a4955 (hw 0 (by norm_num))
  have e4957 := tb_loadHolds_unique a4957 (hw 1 (by norm_num))
  have e4960 := tb_loadHolds_unique a4960 (hw 2 (by norm_num))
  have e4963 := tb_loadHolds_unique a4963 (hw 3 (by norm_num))
  have e4966 := tb_loadHolds_unique a4966 (hw 4 (by norm_num))
  have v4031 : σ (.n 4031) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 62) (by norm_num)).2.2
  have v4060 : σ (.n 4060) = ev 5 := by
    rw [← hev 5 (by norm_num)]; exact (vt_eval h (k := 66) (by norm_num)).2.2
  have v4093 : σ (.n 4093) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_eval h (k := 71) (by norm_num)).2.2
  have v4172 : σ (.n 4172) = ev 20 := by
    rw [← hev 20 (by norm_num)]; exact (vt_eval h (k := 81) (by norm_num)).2.2
  have v4176 : σ (.n 4176) = ev 21 := by
    rw [← hev 21 (by norm_num)]; exact (vt_eval h (k := 82) (by norm_num)).2.2
  have v4180 : σ (.n 4180) = ev 22 := by
    rw [← hev 22 (by norm_num)]; exact (vt_eval h (k := 83) (by norm_num)).2.2
  have v4520 : σ (.n 4520) = ev 68 := by
    rw [← hev 68 (by norm_num)]; exact (vt_eval h (k := 129) (by norm_num)).2.2
  have hB : σ (.n 5393) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 5], 1)], [([68], 2)], [([21], 1), ([10, 21], 1), ([10, 20], 1)], [([22], 1), ([10, 22], 1), ([10, 21], 1)]] := by
    simp only [v4520, v4180, v4176, v4172, v4093, v4060, v4031, a4969, a4968, a4967, e4966, a4965, a4964,
      e4963, a4962, a4961, e4960, a4959, a4958, e4957, a4956, e4955, a4353, a4352, a4351,
      a4350, a4349, a4348, a4347, a4346, a4345, a4344, a4343, a4342, a4341, a4340, a4339,
      a4338]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a4971, a4970, hB]

set_option maxRecDepth 10000 in
theorem vtB05_6 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5412) = σ (.n 5395) + σ (.n 1102) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 6], 1)], [([69], 2)], [([23], 1), ([10, 23], 1), ([10, 22], 1)], [([24], 1), ([10, 24], 1), ([10, 23], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4354 [
    .atom (.const (.n 4778) (word 2 0)),
    .atom (.mul (.n 4779) (.n 4031) (.n 4064)),
    .atom (.copy (.n 4780) (.n 4779)),
    .atom (.const (.n 4781) (word 2 0)),
    .atom (.mul (.n 4782) (.n 4781) (.n 4524)),
    .atom (.copy (.n 4783) (.n 4782)),
    .atom (.mul (.n 4784) (.n 4093) (.n 4197)),
    .atom (.add (.n 4785) (.n 4197) (.n 4784)),
    .atom (.mul (.n 4786) (.n 4093) (.n 4180)),
    .atom (.add (.n 4787) (.n 4785) (.n 4786)),
    .atom (.copy (.n 4788) (.n 4787)),
    .atom (.mul (.n 4789) (.n 4093) (.n 4201)),
    .atom (.add (.n 4790) (.n 4201) (.n 4789)),
    .atom (.mul (.n 4791) (.n 4093) (.n 4197)),
    .atom (.add (.n 4792) (.n 4790) (.n 4791)),
    .atom (.copy (.n 4793) (.n 4792))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4354, a4355, a4356, a4357, a4358, a4359, a4360, a4361, a4362, a4363, a4364, a4365, a4366, a4367,
    a4368, a4369, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 4972 [
    .atom (.load (.n 5396) (.n 13) 0),
    .atom (.mul (.n 5397) (.n 5396) (.n 4778)),
    .atom (.load (.n 5398) (.n 13) 1),
    .atom (.mul (.n 5399) (.n 5398) (.n 4780)),
    .atom (.add (.n 5400) (.n 5397) (.n 5399)),
    .atom (.load (.n 5401) (.n 13) 2),
    .atom (.mul (.n 5402) (.n 5401) (.n 4783)),
    .atom (.add (.n 5403) (.n 5400) (.n 5402)),
    .atom (.load (.n 5404) (.n 13) 3),
    .atom (.mul (.n 5405) (.n 5404) (.n 4788)),
    .atom (.add (.n 5406) (.n 5403) (.n 5405)),
    .atom (.load (.n 5407) (.n 13) 4),
    .atom (.mul (.n 5408) (.n 5407) (.n 4793)),
    .atom (.add (.n 5409) (.n 5406) (.n 5408)),
    .atom (.add (.n 5410) (.n 14) (.n 5409)),
    .atom (.mul (.n 5411) (.n 1102) (.n 5410)),
    .atom (.add (.n 5412) (.n 5395) (.n 5411))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a4972, a4973, a4974, a4975, a4976, a4977, a4978, a4979, a4980, a4981, a4982, a4983, a4984, a4985,
    a4986, a4987, a4988, -⟩ := hs1
  have e4972 := tb_loadHolds_unique a4972 (hw 0 (by norm_num))
  have e4974 := tb_loadHolds_unique a4974 (hw 1 (by norm_num))
  have e4977 := tb_loadHolds_unique a4977 (hw 2 (by norm_num))
  have e4980 := tb_loadHolds_unique a4980 (hw 3 (by norm_num))
  have e4983 := tb_loadHolds_unique a4983 (hw 4 (by norm_num))
  have v4031 : σ (.n 4031) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 62) (by norm_num)).2.2
  have v4064 : σ (.n 4064) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_eval h (k := 67) (by norm_num)).2.2
  have v4093 : σ (.n 4093) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_eval h (k := 71) (by norm_num)).2.2
  have v4180 : σ (.n 4180) = ev 22 := by
    rw [← hev 22 (by norm_num)]; exact (vt_eval h (k := 83) (by norm_num)).2.2
  have v4197 : σ (.n 4197) = ev 23 := by
    rw [← hev 23 (by norm_num)]; exact (vt_eval h (k := 84) (by norm_num)).2.2
  have v4201 : σ (.n 4201) = ev 24 := by
    rw [← hev 24 (by norm_num)]; exact (vt_eval h (k := 85) (by norm_num)).2.2
  have v4524 : σ (.n 4524) = ev 69 := by
    rw [← hev 69 (by norm_num)]; exact (vt_eval h (k := 130) (by norm_num)).2.2
  have hB : σ (.n 5410) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 6], 1)], [([69], 2)], [([23], 1), ([10, 23], 1), ([10, 22], 1)], [([24], 1), ([10, 24], 1), ([10, 23], 1)]] := by
    simp only [v4524, v4201, v4197, v4180, v4093, v4064, v4031, a4986, a4985, a4984, e4983, a4982, a4981,
      e4980, a4979, a4978, e4977, a4976, a4975, e4974, a4973, e4972, a4369, a4368, a4367,
      a4366, a4365, a4364, a4363, a4362, a4361, a4360, a4359, a4358, a4357, a4356, a4355,
      a4354]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a4988, a4987, hB]

set_option maxRecDepth 10000 in
theorem vtB05_7 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5429) = σ (.n 5412) + σ (.n 1111) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 6], 2)], [([70], 2)], [([25], 1), ([10, 25], 1), ([10, 24], 1)], [([26], 1), ([10, 26], 1), ([10, 25], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4370 [
    .atom (.const (.n 4794) (word 2 0)),
    .atom (.const (.n 4795) (word 2 0)),
    .atom (.mul (.n 4796) (.n 4031) (.n 4064)),
    .atom (.mul (.n 4797) (.n 4795) (.n 4796)),
    .atom (.copy (.n 4798) (.n 4797)),
    .atom (.const (.n 4799) (word 2 0)),
    .atom (.mul (.n 4800) (.n 4799) (.n 4528)),
    .atom (.copy (.n 4801) (.n 4800)),
    .atom (.mul (.n 4802) (.n 4093) (.n 4205)),
    .atom (.add (.n 4803) (.n 4205) (.n 4802)),
    .atom (.mul (.n 4804) (.n 4093) (.n 4201)),
    .atom (.add (.n 4805) (.n 4803) (.n 4804)),
    .atom (.copy (.n 4806) (.n 4805)),
    .atom (.mul (.n 4807) (.n 4093) (.n 4209)),
    .atom (.add (.n 4808) (.n 4209) (.n 4807)),
    .atom (.mul (.n 4809) (.n 4093) (.n 4205)),
    .atom (.add (.n 4810) (.n 4808) (.n 4809)),
    .atom (.copy (.n 4811) (.n 4810))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4370, a4371, a4372, a4373, a4374, a4375, a4376, a4377, a4378, a4379, a4380, a4381, a4382, a4383,
    a4384, a4385, a4386, a4387, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 4989 [
    .atom (.load (.n 5413) (.n 13) 0),
    .atom (.mul (.n 5414) (.n 5413) (.n 4794)),
    .atom (.load (.n 5415) (.n 13) 1),
    .atom (.mul (.n 5416) (.n 5415) (.n 4798)),
    .atom (.add (.n 5417) (.n 5414) (.n 5416)),
    .atom (.load (.n 5418) (.n 13) 2),
    .atom (.mul (.n 5419) (.n 5418) (.n 4801)),
    .atom (.add (.n 5420) (.n 5417) (.n 5419)),
    .atom (.load (.n 5421) (.n 13) 3),
    .atom (.mul (.n 5422) (.n 5421) (.n 4806)),
    .atom (.add (.n 5423) (.n 5420) (.n 5422)),
    .atom (.load (.n 5424) (.n 13) 4),
    .atom (.mul (.n 5425) (.n 5424) (.n 4811)),
    .atom (.add (.n 5426) (.n 5423) (.n 5425)),
    .atom (.add (.n 5427) (.n 14) (.n 5426)),
    .atom (.mul (.n 5428) (.n 1111) (.n 5427)),
    .atom (.add (.n 5429) (.n 5412) (.n 5428))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a4989, a4990, a4991, a4992, a4993, a4994, a4995, a4996, a4997, a4998, a4999, a5000, a5001, a5002,
    a5003, a5004, a5005, -⟩ := hs1
  have e4989 := tb_loadHolds_unique a4989 (hw 0 (by norm_num))
  have e4991 := tb_loadHolds_unique a4991 (hw 1 (by norm_num))
  have e4994 := tb_loadHolds_unique a4994 (hw 2 (by norm_num))
  have e4997 := tb_loadHolds_unique a4997 (hw 3 (by norm_num))
  have e5000 := tb_loadHolds_unique a5000 (hw 4 (by norm_num))
  have v4031 : σ (.n 4031) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 62) (by norm_num)).2.2
  have v4064 : σ (.n 4064) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_eval h (k := 67) (by norm_num)).2.2
  have v4093 : σ (.n 4093) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_eval h (k := 71) (by norm_num)).2.2
  have v4201 : σ (.n 4201) = ev 24 := by
    rw [← hev 24 (by norm_num)]; exact (vt_eval h (k := 85) (by norm_num)).2.2
  have v4205 : σ (.n 4205) = ev 25 := by
    rw [← hev 25 (by norm_num)]; exact (vt_eval h (k := 86) (by norm_num)).2.2
  have v4209 : σ (.n 4209) = ev 26 := by
    rw [← hev 26 (by norm_num)]; exact (vt_eval h (k := 87) (by norm_num)).2.2
  have v4528 : σ (.n 4528) = ev 70 := by
    rw [← hev 70 (by norm_num)]; exact (vt_eval h (k := 131) (by norm_num)).2.2
  have hB : σ (.n 5427) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 6], 2)], [([70], 2)], [([25], 1), ([10, 25], 1), ([10, 24], 1)], [([26], 1), ([10, 26], 1), ([10, 25], 1)]] := by
    simp only [v4528, v4209, v4205, v4201, v4093, v4064, v4031, a5003, a5002, a5001, e5000, a4999, a4998,
      e4997, a4996, a4995, e4994, a4993, a4992, e4991, a4990, e4989, a4387, a4386, a4385,
      a4384, a4383, a4382, a4381, a4380, a4379, a4378, a4377, a4376, a4375, a4374, a4373,
      a4372, a4371, a4370]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5005, a5004, hB]

set_option maxRecDepth 10000 in
theorem vtB05_8 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5446) = σ (.n 5429) + σ (.n 1120) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 6], 4)], [([71], 2)], [([27], 1), ([10, 27], 1), ([10, 26], 1)], [([28], 1), ([10, 28], 1), ([10, 27], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4388 [
    .atom (.const (.n 4812) (word 2 0)),
    .atom (.const (.n 4813) (word 4 0)),
    .atom (.mul (.n 4814) (.n 4031) (.n 4064)),
    .atom (.mul (.n 4815) (.n 4813) (.n 4814)),
    .atom (.copy (.n 4816) (.n 4815)),
    .atom (.const (.n 4817) (word 2 0)),
    .atom (.mul (.n 4818) (.n 4817) (.n 4545)),
    .atom (.copy (.n 4819) (.n 4818)),
    .atom (.mul (.n 4820) (.n 4093) (.n 4226)),
    .atom (.add (.n 4821) (.n 4226) (.n 4820)),
    .atom (.mul (.n 4822) (.n 4093) (.n 4209)),
    .atom (.add (.n 4823) (.n 4821) (.n 4822)),
    .atom (.copy (.n 4824) (.n 4823)),
    .atom (.mul (.n 4825) (.n 4093) (.n 4230)),
    .atom (.add (.n 4826) (.n 4230) (.n 4825)),
    .atom (.mul (.n 4827) (.n 4093) (.n 4226)),
    .atom (.add (.n 4828) (.n 4826) (.n 4827)),
    .atom (.copy (.n 4829) (.n 4828))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4388, a4389, a4390, a4391, a4392, a4393, a4394, a4395, a4396, a4397, a4398, a4399, a4400, a4401,
    a4402, a4403, a4404, a4405, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5006 [
    .atom (.load (.n 5430) (.n 13) 0),
    .atom (.mul (.n 5431) (.n 5430) (.n 4812)),
    .atom (.load (.n 5432) (.n 13) 1),
    .atom (.mul (.n 5433) (.n 5432) (.n 4816)),
    .atom (.add (.n 5434) (.n 5431) (.n 5433)),
    .atom (.load (.n 5435) (.n 13) 2),
    .atom (.mul (.n 5436) (.n 5435) (.n 4819)),
    .atom (.add (.n 5437) (.n 5434) (.n 5436)),
    .atom (.load (.n 5438) (.n 13) 3),
    .atom (.mul (.n 5439) (.n 5438) (.n 4824)),
    .atom (.add (.n 5440) (.n 5437) (.n 5439)),
    .atom (.load (.n 5441) (.n 13) 4),
    .atom (.mul (.n 5442) (.n 5441) (.n 4829)),
    .atom (.add (.n 5443) (.n 5440) (.n 5442)),
    .atom (.add (.n 5444) (.n 14) (.n 5443)),
    .atom (.mul (.n 5445) (.n 1120) (.n 5444)),
    .atom (.add (.n 5446) (.n 5429) (.n 5445))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5006, a5007, a5008, a5009, a5010, a5011, a5012, a5013, a5014, a5015, a5016, a5017, a5018, a5019,
    a5020, a5021, a5022, -⟩ := hs1
  have e5006 := tb_loadHolds_unique a5006 (hw 0 (by norm_num))
  have e5008 := tb_loadHolds_unique a5008 (hw 1 (by norm_num))
  have e5011 := tb_loadHolds_unique a5011 (hw 2 (by norm_num))
  have e5014 := tb_loadHolds_unique a5014 (hw 3 (by norm_num))
  have e5017 := tb_loadHolds_unique a5017 (hw 4 (by norm_num))
  have v4031 : σ (.n 4031) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 62) (by norm_num)).2.2
  have v4064 : σ (.n 4064) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_eval h (k := 67) (by norm_num)).2.2
  have v4093 : σ (.n 4093) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_eval h (k := 71) (by norm_num)).2.2
  have v4209 : σ (.n 4209) = ev 26 := by
    rw [← hev 26 (by norm_num)]; exact (vt_eval h (k := 87) (by norm_num)).2.2
  have v4226 : σ (.n 4226) = ev 27 := by
    rw [← hev 27 (by norm_num)]; exact (vt_eval h (k := 88) (by norm_num)).2.2
  have v4230 : σ (.n 4230) = ev 28 := by
    rw [← hev 28 (by norm_num)]; exact (vt_eval h (k := 89) (by norm_num)).2.2
  have v4545 : σ (.n 4545) = ev 71 := by
    rw [← hev 71 (by norm_num)]; exact (vt_eval h (k := 132) (by norm_num)).2.2
  have hB : σ (.n 5444) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 6], 4)], [([71], 2)], [([27], 1), ([10, 27], 1), ([10, 26], 1)], [([28], 1), ([10, 28], 1), ([10, 27], 1)]] := by
    simp only [v4545, v4230, v4226, v4209, v4093, v4064, v4031, a5020, a5019, a5018, e5017, a5016, a5015,
      e5014, a5013, a5012, e5011, a5010, a5009, e5008, a5007, e5006, a4405, a4404, a4403,
      a4402, a4401, a4400, a4399, a4398, a4397, a4396, a4395, a4394, a4393, a4392, a4391,
      a4390, a4389, a4388]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5022, a5021, hB]

set_option maxRecDepth 10000 in
theorem vtB05_9 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5463) = σ (.n 5446) + σ (.n 1129) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 6], 8)], [([72], 2)], [([29], 1), ([10, 29], 1), ([10, 28], 1)], [([30], 1), ([10, 30], 1), ([10, 29], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4406 [
    .atom (.const (.n 4830) (word 2 0)),
    .atom (.const (.n 4831) (word 8 0)),
    .atom (.mul (.n 4832) (.n 4031) (.n 4064)),
    .atom (.mul (.n 4833) (.n 4831) (.n 4832)),
    .atom (.copy (.n 4834) (.n 4833)),
    .atom (.const (.n 4835) (word 2 0)),
    .atom (.mul (.n 4836) (.n 4835) (.n 4549)),
    .atom (.copy (.n 4837) (.n 4836)),
    .atom (.mul (.n 4838) (.n 4093) (.n 4234)),
    .atom (.add (.n 4839) (.n 4234) (.n 4838)),
    .atom (.mul (.n 4840) (.n 4093) (.n 4230)),
    .atom (.add (.n 4841) (.n 4839) (.n 4840)),
    .atom (.copy (.n 4842) (.n 4841)),
    .atom (.mul (.n 4843) (.n 4093) (.n 4238)),
    .atom (.add (.n 4844) (.n 4238) (.n 4843)),
    .atom (.mul (.n 4845) (.n 4093) (.n 4234)),
    .atom (.add (.n 4846) (.n 4844) (.n 4845)),
    .atom (.copy (.n 4847) (.n 4846))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4406, a4407, a4408, a4409, a4410, a4411, a4412, a4413, a4414, a4415, a4416, a4417, a4418, a4419,
    a4420, a4421, a4422, a4423, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5023 [
    .atom (.load (.n 5447) (.n 13) 0),
    .atom (.mul (.n 5448) (.n 5447) (.n 4830)),
    .atom (.load (.n 5449) (.n 13) 1),
    .atom (.mul (.n 5450) (.n 5449) (.n 4834)),
    .atom (.add (.n 5451) (.n 5448) (.n 5450)),
    .atom (.load (.n 5452) (.n 13) 2),
    .atom (.mul (.n 5453) (.n 5452) (.n 4837)),
    .atom (.add (.n 5454) (.n 5451) (.n 5453)),
    .atom (.load (.n 5455) (.n 13) 3),
    .atom (.mul (.n 5456) (.n 5455) (.n 4842)),
    .atom (.add (.n 5457) (.n 5454) (.n 5456)),
    .atom (.load (.n 5458) (.n 13) 4),
    .atom (.mul (.n 5459) (.n 5458) (.n 4847)),
    .atom (.add (.n 5460) (.n 5457) (.n 5459)),
    .atom (.add (.n 5461) (.n 14) (.n 5460)),
    .atom (.mul (.n 5462) (.n 1129) (.n 5461)),
    .atom (.add (.n 5463) (.n 5446) (.n 5462))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5023, a5024, a5025, a5026, a5027, a5028, a5029, a5030, a5031, a5032, a5033, a5034, a5035, a5036,
    a5037, a5038, a5039, -⟩ := hs1
  have e5023 := tb_loadHolds_unique a5023 (hw 0 (by norm_num))
  have e5025 := tb_loadHolds_unique a5025 (hw 1 (by norm_num))
  have e5028 := tb_loadHolds_unique a5028 (hw 2 (by norm_num))
  have e5031 := tb_loadHolds_unique a5031 (hw 3 (by norm_num))
  have e5034 := tb_loadHolds_unique a5034 (hw 4 (by norm_num))
  have v4031 : σ (.n 4031) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 62) (by norm_num)).2.2
  have v4064 : σ (.n 4064) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_eval h (k := 67) (by norm_num)).2.2
  have v4093 : σ (.n 4093) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_eval h (k := 71) (by norm_num)).2.2
  have v4230 : σ (.n 4230) = ev 28 := by
    rw [← hev 28 (by norm_num)]; exact (vt_eval h (k := 89) (by norm_num)).2.2
  have v4234 : σ (.n 4234) = ev 29 := by
    rw [← hev 29 (by norm_num)]; exact (vt_eval h (k := 90) (by norm_num)).2.2
  have v4238 : σ (.n 4238) = ev 30 := by
    rw [← hev 30 (by norm_num)]; exact (vt_eval h (k := 91) (by norm_num)).2.2
  have v4549 : σ (.n 4549) = ev 72 := by
    rw [← hev 72 (by norm_num)]; exact (vt_eval h (k := 133) (by norm_num)).2.2
  have hB : σ (.n 5461) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 6], 8)], [([72], 2)], [([29], 1), ([10, 29], 1), ([10, 28], 1)], [([30], 1), ([10, 30], 1), ([10, 29], 1)]] := by
    simp only [v4549, v4238, v4234, v4230, v4093, v4064, v4031, a5037, a5036, a5035, e5034, a5033, a5032,
      e5031, a5030, a5029, e5028, a5027, a5026, e5025, a5024, e5023, a4423, a4422, a4421,
      a4420, a4419, a4418, a4417, a4416, a4415, a4414, a4413, a4412, a4411, a4410, a4409,
      a4408, a4407, a4406]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5039, a5038, hB]

set_option maxRecDepth 10000 in
theorem vtB05_10 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5480) = σ (.n 5463) + σ (.n 1138) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 7], 1)], [([73], 2)], [([31], 1), ([10, 31], 1), ([10, 30], 1)], [([14], 1), ([10, 14], 1), ([10, 31], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4424 [
    .atom (.const (.n 4848) (word 2 0)),
    .atom (.mul (.n 4849) (.n 4031) (.n 4081)),
    .atom (.copy (.n 4850) (.n 4849)),
    .atom (.const (.n 4851) (word 2 0)),
    .atom (.mul (.n 4852) (.n 4851) (.n 4553)),
    .atom (.copy (.n 4853) (.n 4852)),
    .atom (.mul (.n 4854) (.n 4093) (.n 4255)),
    .atom (.add (.n 4855) (.n 4255) (.n 4854)),
    .atom (.mul (.n 4856) (.n 4093) (.n 4238)),
    .atom (.add (.n 4857) (.n 4855) (.n 4856)),
    .atom (.copy (.n 4858) (.n 4857)),
    .atom (.mul (.n 4859) (.n 4093) (.n 4122)),
    .atom (.add (.n 4860) (.n 4122) (.n 4859)),
    .atom (.mul (.n 4861) (.n 4093) (.n 4255)),
    .atom (.add (.n 4862) (.n 4860) (.n 4861)),
    .atom (.copy (.n 4863) (.n 4862))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4424, a4425, a4426, a4427, a4428, a4429, a4430, a4431, a4432, a4433, a4434, a4435, a4436, a4437,
    a4438, a4439, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5040 [
    .atom (.load (.n 5464) (.n 13) 0),
    .atom (.mul (.n 5465) (.n 5464) (.n 4848)),
    .atom (.load (.n 5466) (.n 13) 1),
    .atom (.mul (.n 5467) (.n 5466) (.n 4850)),
    .atom (.add (.n 5468) (.n 5465) (.n 5467)),
    .atom (.load (.n 5469) (.n 13) 2),
    .atom (.mul (.n 5470) (.n 5469) (.n 4853)),
    .atom (.add (.n 5471) (.n 5468) (.n 5470)),
    .atom (.load (.n 5472) (.n 13) 3),
    .atom (.mul (.n 5473) (.n 5472) (.n 4858)),
    .atom (.add (.n 5474) (.n 5471) (.n 5473)),
    .atom (.load (.n 5475) (.n 13) 4),
    .atom (.mul (.n 5476) (.n 5475) (.n 4863)),
    .atom (.add (.n 5477) (.n 5474) (.n 5476)),
    .atom (.add (.n 5478) (.n 14) (.n 5477)),
    .atom (.mul (.n 5479) (.n 1138) (.n 5478)),
    .atom (.add (.n 5480) (.n 5463) (.n 5479))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5040, a5041, a5042, a5043, a5044, a5045, a5046, a5047, a5048, a5049, a5050, a5051, a5052, a5053,
    a5054, a5055, a5056, -⟩ := hs1
  have e5040 := tb_loadHolds_unique a5040 (hw 0 (by norm_num))
  have e5042 := tb_loadHolds_unique a5042 (hw 1 (by norm_num))
  have e5045 := tb_loadHolds_unique a5045 (hw 2 (by norm_num))
  have e5048 := tb_loadHolds_unique a5048 (hw 3 (by norm_num))
  have e5051 := tb_loadHolds_unique a5051 (hw 4 (by norm_num))
  have v4031 : σ (.n 4031) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 62) (by norm_num)).2.2
  have v4081 : σ (.n 4081) = ev 7 := by
    rw [← hev 7 (by norm_num)]; exact (vt_eval h (k := 68) (by norm_num)).2.2
  have v4093 : σ (.n 4093) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_eval h (k := 71) (by norm_num)).2.2
  have v4122 : σ (.n 4122) = ev 14 := by
    rw [← hev 14 (by norm_num)]; exact (vt_eval h (k := 75) (by norm_num)).2.2
  have v4238 : σ (.n 4238) = ev 30 := by
    rw [← hev 30 (by norm_num)]; exact (vt_eval h (k := 91) (by norm_num)).2.2
  have v4255 : σ (.n 4255) = ev 31 := by
    rw [← hev 31 (by norm_num)]; exact (vt_eval h (k := 92) (by norm_num)).2.2
  have v4553 : σ (.n 4553) = ev 73 := by
    rw [← hev 73 (by norm_num)]; exact (vt_eval h (k := 134) (by norm_num)).2.2
  have hB : σ (.n 5478) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 7], 1)], [([73], 2)], [([31], 1), ([10, 31], 1), ([10, 30], 1)], [([14], 1), ([10, 14], 1), ([10, 31], 1)]] := by
    simp only [v4553, v4255, v4238, v4122, v4093, v4081, v4031, a5054, a5053, a5052, e5051, a5050, a5049,
      e5048, a5047, a5046, e5045, a5044, a5043, e5042, a5041, e5040, a4439, a4438, a4437,
      a4436, a4435, a4434, a4433, a4432, a4431, a4430, a4429, a4428, a4427, a4426, a4425,
      a4424]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5056, a5055, hB]

set_option maxRecDepth 10000 in
theorem vtB05_11 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5497) = σ (.n 5480) + σ (.n 1147) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 8], 1)], [([74], 2)], [([32], 1)], [([33], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4440 [
    .atom (.const (.n 4864) (word 2 0)),
    .atom (.mul (.n 4865) (.n 4031) (.n 4085)),
    .atom (.copy (.n 4866) (.n 4865)),
    .atom (.const (.n 4867) (word 2 0)),
    .atom (.mul (.n 4868) (.n 4867) (.n 4557)),
    .atom (.copy (.n 4869) (.n 4868)),
    .atom (.copy (.n 4870) (.n 4259)),
    .atom (.copy (.n 4871) (.n 4263))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4440, a4441, a4442, a4443, a4444, a4445, a4446, a4447, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5057 [
    .atom (.load (.n 5481) (.n 13) 0),
    .atom (.mul (.n 5482) (.n 5481) (.n 4864)),
    .atom (.load (.n 5483) (.n 13) 1),
    .atom (.mul (.n 5484) (.n 5483) (.n 4866)),
    .atom (.add (.n 5485) (.n 5482) (.n 5484)),
    .atom (.load (.n 5486) (.n 13) 2),
    .atom (.mul (.n 5487) (.n 5486) (.n 4869)),
    .atom (.add (.n 5488) (.n 5485) (.n 5487)),
    .atom (.load (.n 5489) (.n 13) 3),
    .atom (.mul (.n 5490) (.n 5489) (.n 4870)),
    .atom (.add (.n 5491) (.n 5488) (.n 5490)),
    .atom (.load (.n 5492) (.n 13) 4),
    .atom (.mul (.n 5493) (.n 5492) (.n 4871)),
    .atom (.add (.n 5494) (.n 5491) (.n 5493)),
    .atom (.add (.n 5495) (.n 14) (.n 5494)),
    .atom (.mul (.n 5496) (.n 1147) (.n 5495)),
    .atom (.add (.n 5497) (.n 5480) (.n 5496))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5057, a5058, a5059, a5060, a5061, a5062, a5063, a5064, a5065, a5066, a5067, a5068, a5069, a5070,
    a5071, a5072, a5073, -⟩ := hs1
  have e5057 := tb_loadHolds_unique a5057 (hw 0 (by norm_num))
  have e5059 := tb_loadHolds_unique a5059 (hw 1 (by norm_num))
  have e5062 := tb_loadHolds_unique a5062 (hw 2 (by norm_num))
  have e5065 := tb_loadHolds_unique a5065 (hw 3 (by norm_num))
  have e5068 := tb_loadHolds_unique a5068 (hw 4 (by norm_num))
  have v4031 : σ (.n 4031) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 62) (by norm_num)).2.2
  have v4085 : σ (.n 4085) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_eval h (k := 69) (by norm_num)).2.2
  have v4259 : σ (.n 4259) = ev 32 := by
    rw [← hev 32 (by norm_num)]; exact (vt_eval h (k := 93) (by norm_num)).2.2
  have v4263 : σ (.n 4263) = ev 33 := by
    rw [← hev 33 (by norm_num)]; exact (vt_eval h (k := 94) (by norm_num)).2.2
  have v4557 : σ (.n 4557) = ev 74 := by
    rw [← hev 74 (by norm_num)]; exact (vt_eval h (k := 135) (by norm_num)).2.2
  have hB : σ (.n 5495) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 8], 1)], [([74], 2)], [([32], 1)], [([33], 1)]] := by
    simp only [v4557, v4263, v4259, v4085, v4031, a5071, a5070, a5069, e5068, a5067, a5066, e5065, a5064,
      a5063, e5062, a5061, a5060, e5059, a5058, e5057, a4447, a4446, a4445, a4444, a4443,
      a4442, a4441, a4440]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5073, a5072, hB]

set_option maxRecDepth 10000 in
theorem vtB05_12 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5514) = σ (.n 5497) + σ (.n 1156) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 8], 2)], [([75], 2)], [([34], 1)], [([35], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4448 [
    .atom (.const (.n 4872) (word 2 0)),
    .atom (.const (.n 4873) (word 2 0)),
    .atom (.mul (.n 4874) (.n 4031) (.n 4085)),
    .atom (.mul (.n 4875) (.n 4873) (.n 4874)),
    .atom (.copy (.n 4876) (.n 4875)),
    .atom (.const (.n 4877) (word 2 0)),
    .atom (.mul (.n 4878) (.n 4877) (.n 4574)),
    .atom (.copy (.n 4879) (.n 4878)),
    .atom (.copy (.n 4880) (.n 4267)),
    .atom (.copy (.n 4881) (.n 4284))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4448, a4449, a4450, a4451, a4452, a4453, a4454, a4455, a4456, a4457, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5074 [
    .atom (.load (.n 5498) (.n 13) 0),
    .atom (.mul (.n 5499) (.n 5498) (.n 4872)),
    .atom (.load (.n 5500) (.n 13) 1),
    .atom (.mul (.n 5501) (.n 5500) (.n 4876)),
    .atom (.add (.n 5502) (.n 5499) (.n 5501)),
    .atom (.load (.n 5503) (.n 13) 2),
    .atom (.mul (.n 5504) (.n 5503) (.n 4879)),
    .atom (.add (.n 5505) (.n 5502) (.n 5504)),
    .atom (.load (.n 5506) (.n 13) 3),
    .atom (.mul (.n 5507) (.n 5506) (.n 4880)),
    .atom (.add (.n 5508) (.n 5505) (.n 5507)),
    .atom (.load (.n 5509) (.n 13) 4),
    .atom (.mul (.n 5510) (.n 5509) (.n 4881)),
    .atom (.add (.n 5511) (.n 5508) (.n 5510)),
    .atom (.add (.n 5512) (.n 14) (.n 5511)),
    .atom (.mul (.n 5513) (.n 1156) (.n 5512)),
    .atom (.add (.n 5514) (.n 5497) (.n 5513))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5074, a5075, a5076, a5077, a5078, a5079, a5080, a5081, a5082, a5083, a5084, a5085, a5086, a5087,
    a5088, a5089, a5090, -⟩ := hs1
  have e5074 := tb_loadHolds_unique a5074 (hw 0 (by norm_num))
  have e5076 := tb_loadHolds_unique a5076 (hw 1 (by norm_num))
  have e5079 := tb_loadHolds_unique a5079 (hw 2 (by norm_num))
  have e5082 := tb_loadHolds_unique a5082 (hw 3 (by norm_num))
  have e5085 := tb_loadHolds_unique a5085 (hw 4 (by norm_num))
  have v4031 : σ (.n 4031) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 62) (by norm_num)).2.2
  have v4085 : σ (.n 4085) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_eval h (k := 69) (by norm_num)).2.2
  have v4267 : σ (.n 4267) = ev 34 := by
    rw [← hev 34 (by norm_num)]; exact (vt_eval h (k := 95) (by norm_num)).2.2
  have v4284 : σ (.n 4284) = ev 35 := by
    rw [← hev 35 (by norm_num)]; exact (vt_eval h (k := 96) (by norm_num)).2.2
  have v4574 : σ (.n 4574) = ev 75 := by
    rw [← hev 75 (by norm_num)]; exact (vt_eval h (k := 136) (by norm_num)).2.2
  have hB : σ (.n 5512) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 8], 2)], [([75], 2)], [([34], 1)], [([35], 1)]] := by
    simp only [v4574, v4284, v4267, v4085, v4031, a5088, a5087, a5086, e5085, a5084, a5083, e5082, a5081,
      a5080, e5079, a5078, a5077, e5076, a5075, e5074, a4457, a4456, a4455, a4454, a4453,
      a4452, a4451, a4450, a4449, a4448]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5090, a5089, hB]

set_option maxRecDepth 10000 in
theorem vtB05_13 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5531) = σ (.n 5514) + σ (.n 1165) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 8], 4)], [([76], 2)], [([36], 1)], [([37], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4458 [
    .atom (.const (.n 4882) (word 2 0)),
    .atom (.const (.n 4883) (word 4 0)),
    .atom (.mul (.n 4884) (.n 4031) (.n 4085)),
    .atom (.mul (.n 4885) (.n 4883) (.n 4884)),
    .atom (.copy (.n 4886) (.n 4885)),
    .atom (.const (.n 4887) (word 2 0)),
    .atom (.mul (.n 4888) (.n 4887) (.n 4578)),
    .atom (.copy (.n 4889) (.n 4888)),
    .atom (.copy (.n 4890) (.n 4288)),
    .atom (.copy (.n 4891) (.n 4292))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4458, a4459, a4460, a4461, a4462, a4463, a4464, a4465, a4466, a4467, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5091 [
    .atom (.load (.n 5515) (.n 13) 0),
    .atom (.mul (.n 5516) (.n 5515) (.n 4882)),
    .atom (.load (.n 5517) (.n 13) 1),
    .atom (.mul (.n 5518) (.n 5517) (.n 4886)),
    .atom (.add (.n 5519) (.n 5516) (.n 5518)),
    .atom (.load (.n 5520) (.n 13) 2),
    .atom (.mul (.n 5521) (.n 5520) (.n 4889)),
    .atom (.add (.n 5522) (.n 5519) (.n 5521)),
    .atom (.load (.n 5523) (.n 13) 3),
    .atom (.mul (.n 5524) (.n 5523) (.n 4890)),
    .atom (.add (.n 5525) (.n 5522) (.n 5524)),
    .atom (.load (.n 5526) (.n 13) 4),
    .atom (.mul (.n 5527) (.n 5526) (.n 4891)),
    .atom (.add (.n 5528) (.n 5525) (.n 5527)),
    .atom (.add (.n 5529) (.n 14) (.n 5528)),
    .atom (.mul (.n 5530) (.n 1165) (.n 5529)),
    .atom (.add (.n 5531) (.n 5514) (.n 5530))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5091, a5092, a5093, a5094, a5095, a5096, a5097, a5098, a5099, a5100, a5101, a5102, a5103, a5104,
    a5105, a5106, a5107, -⟩ := hs1
  have e5091 := tb_loadHolds_unique a5091 (hw 0 (by norm_num))
  have e5093 := tb_loadHolds_unique a5093 (hw 1 (by norm_num))
  have e5096 := tb_loadHolds_unique a5096 (hw 2 (by norm_num))
  have e5099 := tb_loadHolds_unique a5099 (hw 3 (by norm_num))
  have e5102 := tb_loadHolds_unique a5102 (hw 4 (by norm_num))
  have v4031 : σ (.n 4031) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 62) (by norm_num)).2.2
  have v4085 : σ (.n 4085) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_eval h (k := 69) (by norm_num)).2.2
  have v4288 : σ (.n 4288) = ev 36 := by
    rw [← hev 36 (by norm_num)]; exact (vt_eval h (k := 97) (by norm_num)).2.2
  have v4292 : σ (.n 4292) = ev 37 := by
    rw [← hev 37 (by norm_num)]; exact (vt_eval h (k := 98) (by norm_num)).2.2
  have v4578 : σ (.n 4578) = ev 76 := by
    rw [← hev 76 (by norm_num)]; exact (vt_eval h (k := 137) (by norm_num)).2.2
  have hB : σ (.n 5529) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 8], 4)], [([76], 2)], [([36], 1)], [([37], 1)]] := by
    simp only [v4578, v4292, v4288, v4085, v4031, a5105, a5104, a5103, e5102, a5101, a5100, e5099, a5098,
      a5097, e5096, a5095, a5094, e5093, a5092, e5091, a4467, a4466, a4465, a4464, a4463,
      a4462, a4461, a4460, a4459, a4458]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5107, a5106, hB]

set_option maxRecDepth 10000 in
theorem vtB05_14 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5548) = σ (.n 5531) + σ (.n 1174) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 8], 8)], [([77], 2)], [([38], 1)], [([39], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4468 [
    .atom (.const (.n 4892) (word 2 0)),
    .atom (.const (.n 4893) (word 8 0)),
    .atom (.mul (.n 4894) (.n 4031) (.n 4085)),
    .atom (.mul (.n 4895) (.n 4893) (.n 4894)),
    .atom (.copy (.n 4896) (.n 4895)),
    .atom (.const (.n 4897) (word 2 0)),
    .atom (.mul (.n 4898) (.n 4897) (.n 4582)),
    .atom (.copy (.n 4899) (.n 4898)),
    .atom (.copy (.n 4900) (.n 4296)),
    .atom (.copy (.n 4901) (.n 4313))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4468, a4469, a4470, a4471, a4472, a4473, a4474, a4475, a4476, a4477, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5108 [
    .atom (.load (.n 5532) (.n 13) 0),
    .atom (.mul (.n 5533) (.n 5532) (.n 4892)),
    .atom (.load (.n 5534) (.n 13) 1),
    .atom (.mul (.n 5535) (.n 5534) (.n 4896)),
    .atom (.add (.n 5536) (.n 5533) (.n 5535)),
    .atom (.load (.n 5537) (.n 13) 2),
    .atom (.mul (.n 5538) (.n 5537) (.n 4899)),
    .atom (.add (.n 5539) (.n 5536) (.n 5538)),
    .atom (.load (.n 5540) (.n 13) 3),
    .atom (.mul (.n 5541) (.n 5540) (.n 4900)),
    .atom (.add (.n 5542) (.n 5539) (.n 5541)),
    .atom (.load (.n 5543) (.n 13) 4),
    .atom (.mul (.n 5544) (.n 5543) (.n 4901)),
    .atom (.add (.n 5545) (.n 5542) (.n 5544)),
    .atom (.add (.n 5546) (.n 14) (.n 5545)),
    .atom (.mul (.n 5547) (.n 1174) (.n 5546)),
    .atom (.add (.n 5548) (.n 5531) (.n 5547))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5108, a5109, a5110, a5111, a5112, a5113, a5114, a5115, a5116, a5117, a5118, a5119, a5120, a5121,
    a5122, a5123, a5124, -⟩ := hs1
  have e5108 := tb_loadHolds_unique a5108 (hw 0 (by norm_num))
  have e5110 := tb_loadHolds_unique a5110 (hw 1 (by norm_num))
  have e5113 := tb_loadHolds_unique a5113 (hw 2 (by norm_num))
  have e5116 := tb_loadHolds_unique a5116 (hw 3 (by norm_num))
  have e5119 := tb_loadHolds_unique a5119 (hw 4 (by norm_num))
  have v4031 : σ (.n 4031) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 62) (by norm_num)).2.2
  have v4085 : σ (.n 4085) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_eval h (k := 69) (by norm_num)).2.2
  have v4296 : σ (.n 4296) = ev 38 := by
    rw [← hev 38 (by norm_num)]; exact (vt_eval h (k := 99) (by norm_num)).2.2
  have v4313 : σ (.n 4313) = ev 39 := by
    rw [← hev 39 (by norm_num)]; exact (vt_eval h (k := 100) (by norm_num)).2.2
  have v4582 : σ (.n 4582) = ev 77 := by
    rw [← hev 77 (by norm_num)]; exact (vt_eval h (k := 138) (by norm_num)).2.2
  have hB : σ (.n 5546) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 8], 8)], [([77], 2)], [([38], 1)], [([39], 1)]] := by
    simp only [v4582, v4313, v4296, v4085, v4031, a5122, a5121, a5120, e5119, a5118, a5117, e5116, a5115,
      a5114, e5113, a5112, a5111, e5110, a5109, e5108, a4477, a4476, a4475, a4474, a4473,
      a4472, a4471, a4470, a4469, a4468]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5124, a5123, hB]

set_option maxRecDepth 10000 in
theorem vtB05_15 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5565) = σ (.n 5548) + σ (.n 1183) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 9], 1)], [([78], 2)], [([40], 1), ([11, 40], 1)], [([41], 1), ([11, 41], 1), ([11, 40], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4478 [
    .atom (.const (.n 4902) (word 2 0)),
    .atom (.mul (.n 4903) (.n 4031) (.n 4089)),
    .atom (.copy (.n 4904) (.n 4903)),
    .atom (.const (.n 4905) (word 2 0)),
    .atom (.mul (.n 4906) (.n 4905) (.n 4586)),
    .atom (.copy (.n 4907) (.n 4906)),
    .atom (.mul (.n 4908) (.n 4110) (.n 4317)),
    .atom (.add (.n 4909) (.n 4317) (.n 4908)),
    .atom (.copy (.n 4910) (.n 4909)),
    .atom (.mul (.n 4911) (.n 4110) (.n 4321)),
    .atom (.add (.n 4912) (.n 4321) (.n 4911)),
    .atom (.mul (.n 4913) (.n 4110) (.n 4317)),
    .atom (.add (.n 4914) (.n 4912) (.n 4913)),
    .atom (.copy (.n 4915) (.n 4914))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4478, a4479, a4480, a4481, a4482, a4483, a4484, a4485, a4486, a4487, a4488, a4489, a4490, a4491,
    -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5125 [
    .atom (.load (.n 5549) (.n 13) 0),
    .atom (.mul (.n 5550) (.n 5549) (.n 4902)),
    .atom (.load (.n 5551) (.n 13) 1),
    .atom (.mul (.n 5552) (.n 5551) (.n 4904)),
    .atom (.add (.n 5553) (.n 5550) (.n 5552)),
    .atom (.load (.n 5554) (.n 13) 2),
    .atom (.mul (.n 5555) (.n 5554) (.n 4907)),
    .atom (.add (.n 5556) (.n 5553) (.n 5555)),
    .atom (.load (.n 5557) (.n 13) 3),
    .atom (.mul (.n 5558) (.n 5557) (.n 4910)),
    .atom (.add (.n 5559) (.n 5556) (.n 5558)),
    .atom (.load (.n 5560) (.n 13) 4),
    .atom (.mul (.n 5561) (.n 5560) (.n 4915)),
    .atom (.add (.n 5562) (.n 5559) (.n 5561)),
    .atom (.add (.n 5563) (.n 14) (.n 5562)),
    .atom (.mul (.n 5564) (.n 1183) (.n 5563)),
    .atom (.add (.n 5565) (.n 5548) (.n 5564))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5125, a5126, a5127, a5128, a5129, a5130, a5131, a5132, a5133, a5134, a5135, a5136, a5137, a5138,
    a5139, a5140, a5141, -⟩ := hs1
  have e5125 := tb_loadHolds_unique a5125 (hw 0 (by norm_num))
  have e5127 := tb_loadHolds_unique a5127 (hw 1 (by norm_num))
  have e5130 := tb_loadHolds_unique a5130 (hw 2 (by norm_num))
  have e5133 := tb_loadHolds_unique a5133 (hw 3 (by norm_num))
  have e5136 := tb_loadHolds_unique a5136 (hw 4 (by norm_num))
  have v4031 : σ (.n 4031) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 62) (by norm_num)).2.2
  have v4089 : σ (.n 4089) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 70) (by norm_num)).2.2
  have v4110 : σ (.n 4110) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_eval h (k := 72) (by norm_num)).2.2
  have v4317 : σ (.n 4317) = ev 40 := by
    rw [← hev 40 (by norm_num)]; exact (vt_eval h (k := 101) (by norm_num)).2.2
  have v4321 : σ (.n 4321) = ev 41 := by
    rw [← hev 41 (by norm_num)]; exact (vt_eval h (k := 102) (by norm_num)).2.2
  have v4586 : σ (.n 4586) = ev 78 := by
    rw [← hev 78 (by norm_num)]; exact (vt_eval h (k := 139) (by norm_num)).2.2
  have hB : σ (.n 5563) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 9], 1)], [([78], 2)], [([40], 1), ([11, 40], 1)], [([41], 1), ([11, 41], 1), ([11, 40], 1)]] := by
    simp only [v4586, v4321, v4317, v4110, v4089, v4031, a5139, a5138, a5137, e5136, a5135, a5134, e5133,
      a5132, a5131, e5130, a5129, a5128, e5127, a5126, e5125, a4491, a4490, a4489, a4488,
      a4487, a4486, a4485, a4484, a4483, a4482, a4481, a4480, a4479, a4478]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5141, a5140, hB]

set_option maxRecDepth 10000 in
theorem vtB05_16 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5582) = σ (.n 5565) + σ (.n 1192) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 9], 2)], [([79], 1), ([12, 79], 2), ([12, 79], 1)], [([42], 1), ([11, 42], 1), ([11, 41], 1)], [([43], 1), ([11, 43], 1), ([11, 42], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4492 [
    .atom (.const (.n 4916) (word 2 0)),
    .atom (.const (.n 4917) (word 2 0)),
    .atom (.mul (.n 4918) (.n 4031) (.n 4089)),
    .atom (.mul (.n 4919) (.n 4917) (.n 4918)),
    .atom (.copy (.n 4920) (.n 4919)),
    .atom (.const (.n 4921) (word 2 0)),
    .atom (.mul (.n 4922) (.n 4114) (.n 4603)),
    .atom (.mul (.n 4923) (.n 4921) (.n 4922)),
    .atom (.add (.n 4924) (.n 4603) (.n 4923)),
    .atom (.mul (.n 4925) (.n 4114) (.n 4603)),
    .atom (.add (.n 4926) (.n 4924) (.n 4925)),
    .atom (.copy (.n 4927) (.n 4926)),
    .atom (.mul (.n 4928) (.n 4110) (.n 4325)),
    .atom (.add (.n 4929) (.n 4325) (.n 4928)),
    .atom (.mul (.n 4930) (.n 4110) (.n 4321)),
    .atom (.add (.n 4931) (.n 4929) (.n 4930)),
    .atom (.copy (.n 4932) (.n 4931)),
    .atom (.mul (.n 4933) (.n 4110) (.n 4342)),
    .atom (.add (.n 4934) (.n 4342) (.n 4933)),
    .atom (.mul (.n 4935) (.n 4110) (.n 4325)),
    .atom (.add (.n 4936) (.n 4934) (.n 4935)),
    .atom (.copy (.n 4937) (.n 4936))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4492, a4493, a4494, a4495, a4496, a4497, a4498, a4499, a4500, a4501, a4502, a4503, a4504, a4505,
    a4506, a4507, a4508, a4509, a4510, a4511, a4512, a4513, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5142 [
    .atom (.load (.n 5566) (.n 13) 0),
    .atom (.mul (.n 5567) (.n 5566) (.n 4916)),
    .atom (.load (.n 5568) (.n 13) 1),
    .atom (.mul (.n 5569) (.n 5568) (.n 4920)),
    .atom (.add (.n 5570) (.n 5567) (.n 5569)),
    .atom (.load (.n 5571) (.n 13) 2),
    .atom (.mul (.n 5572) (.n 5571) (.n 4927)),
    .atom (.add (.n 5573) (.n 5570) (.n 5572)),
    .atom (.load (.n 5574) (.n 13) 3),
    .atom (.mul (.n 5575) (.n 5574) (.n 4932)),
    .atom (.add (.n 5576) (.n 5573) (.n 5575)),
    .atom (.load (.n 5577) (.n 13) 4),
    .atom (.mul (.n 5578) (.n 5577) (.n 4937)),
    .atom (.add (.n 5579) (.n 5576) (.n 5578)),
    .atom (.add (.n 5580) (.n 14) (.n 5579)),
    .atom (.mul (.n 5581) (.n 1192) (.n 5580)),
    .atom (.add (.n 5582) (.n 5565) (.n 5581))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5142, a5143, a5144, a5145, a5146, a5147, a5148, a5149, a5150, a5151, a5152, a5153, a5154, a5155,
    a5156, a5157, a5158, -⟩ := hs1
  have e5142 := tb_loadHolds_unique a5142 (hw 0 (by norm_num))
  have e5144 := tb_loadHolds_unique a5144 (hw 1 (by norm_num))
  have e5147 := tb_loadHolds_unique a5147 (hw 2 (by norm_num))
  have e5150 := tb_loadHolds_unique a5150 (hw 3 (by norm_num))
  have e5153 := tb_loadHolds_unique a5153 (hw 4 (by norm_num))
  have v4031 : σ (.n 4031) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 62) (by norm_num)).2.2
  have v4089 : σ (.n 4089) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 70) (by norm_num)).2.2
  have v4110 : σ (.n 4110) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_eval h (k := 72) (by norm_num)).2.2
  have v4114 : σ (.n 4114) = ev 12 := by
    rw [← hev 12 (by norm_num)]; exact (vt_eval h (k := 73) (by norm_num)).2.2
  have v4321 : σ (.n 4321) = ev 41 := by
    rw [← hev 41 (by norm_num)]; exact (vt_eval h (k := 102) (by norm_num)).2.2
  have v4325 : σ (.n 4325) = ev 42 := by
    rw [← hev 42 (by norm_num)]; exact (vt_eval h (k := 103) (by norm_num)).2.2
  have v4342 : σ (.n 4342) = ev 43 := by
    rw [← hev 43 (by norm_num)]; exact (vt_eval h (k := 104) (by norm_num)).2.2
  have v4603 : σ (.n 4603) = ev 79 := by
    rw [← hev 79 (by norm_num)]; exact (vt_eval h (k := 140) (by norm_num)).2.2
  have hB : σ (.n 5580) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 9], 2)], [([79], 1), ([12, 79], 2), ([12, 79], 1)], [([42], 1), ([11, 42], 1), ([11, 41], 1)], [([43], 1), ([11, 43], 1), ([11, 42], 1)]] := by
    simp only [v4603, v4342, v4325, v4321, v4114, v4110, v4089, v4031, a5156, a5155, a5154, e5153, a5152,
      a5151, e5150, a5149, a5148, e5147, a5146, a5145, e5144, a5143, e5142, a4513, a4512,
      a4511, a4510, a4509, a4508, a4507, a4506, a4505, a4504, a4503, a4502, a4501, a4500,
      a4499, a4498, a4497, a4496, a4495, a4494, a4493, a4492]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5158, a5157, hB]

set_option maxRecDepth 10000 in
theorem vtB05_17 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5599) = σ (.n 5582) + σ (.n 1201) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 9], 4)], [([80], 1), ([13, 80], 2), ([13, 80], 1)], [([44], 1), ([11, 44], 1), ([11, 43], 1)], [([45], 1), ([11, 45], 1), ([11, 44], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4514 [
    .atom (.const (.n 4938) (word 2 0)),
    .atom (.const (.n 4939) (word 4 0)),
    .atom (.mul (.n 4940) (.n 4031) (.n 4089)),
    .atom (.mul (.n 4941) (.n 4939) (.n 4940)),
    .atom (.copy (.n 4942) (.n 4941)),
    .atom (.const (.n 4943) (word 2 0)),
    .atom (.mul (.n 4944) (.n 4118) (.n 4607)),
    .atom (.mul (.n 4945) (.n 4943) (.n 4944)),
    .atom (.add (.n 4946) (.n 4607) (.n 4945)),
    .atom (.mul (.n 4947) (.n 4118) (.n 4607)),
    .atom (.add (.n 4948) (.n 4946) (.n 4947)),
    .atom (.copy (.n 4949) (.n 4948)),
    .atom (.mul (.n 4950) (.n 4110) (.n 4346)),
    .atom (.add (.n 4951) (.n 4346) (.n 4950)),
    .atom (.mul (.n 4952) (.n 4110) (.n 4342)),
    .atom (.add (.n 4953) (.n 4951) (.n 4952)),
    .atom (.copy (.n 4954) (.n 4953)),
    .atom (.mul (.n 4955) (.n 4110) (.n 4350)),
    .atom (.add (.n 4956) (.n 4350) (.n 4955)),
    .atom (.mul (.n 4957) (.n 4110) (.n 4346)),
    .atom (.add (.n 4958) (.n 4956) (.n 4957)),
    .atom (.copy (.n 4959) (.n 4958))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4514, a4515, a4516, a4517, a4518, a4519, a4520, a4521, a4522, a4523, a4524, a4525, a4526, a4527,
    a4528, a4529, a4530, a4531, a4532, a4533, a4534, a4535, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5159 [
    .atom (.load (.n 5583) (.n 13) 0),
    .atom (.mul (.n 5584) (.n 5583) (.n 4938)),
    .atom (.load (.n 5585) (.n 13) 1),
    .atom (.mul (.n 5586) (.n 5585) (.n 4942)),
    .atom (.add (.n 5587) (.n 5584) (.n 5586)),
    .atom (.load (.n 5588) (.n 13) 2),
    .atom (.mul (.n 5589) (.n 5588) (.n 4949)),
    .atom (.add (.n 5590) (.n 5587) (.n 5589)),
    .atom (.load (.n 5591) (.n 13) 3),
    .atom (.mul (.n 5592) (.n 5591) (.n 4954)),
    .atom (.add (.n 5593) (.n 5590) (.n 5592)),
    .atom (.load (.n 5594) (.n 13) 4),
    .atom (.mul (.n 5595) (.n 5594) (.n 4959)),
    .atom (.add (.n 5596) (.n 5593) (.n 5595)),
    .atom (.add (.n 5597) (.n 14) (.n 5596)),
    .atom (.mul (.n 5598) (.n 1201) (.n 5597)),
    .atom (.add (.n 5599) (.n 5582) (.n 5598))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5159, a5160, a5161, a5162, a5163, a5164, a5165, a5166, a5167, a5168, a5169, a5170, a5171, a5172,
    a5173, a5174, a5175, -⟩ := hs1
  have e5159 := tb_loadHolds_unique a5159 (hw 0 (by norm_num))
  have e5161 := tb_loadHolds_unique a5161 (hw 1 (by norm_num))
  have e5164 := tb_loadHolds_unique a5164 (hw 2 (by norm_num))
  have e5167 := tb_loadHolds_unique a5167 (hw 3 (by norm_num))
  have e5170 := tb_loadHolds_unique a5170 (hw 4 (by norm_num))
  have v4031 : σ (.n 4031) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 62) (by norm_num)).2.2
  have v4089 : σ (.n 4089) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 70) (by norm_num)).2.2
  have v4110 : σ (.n 4110) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_eval h (k := 72) (by norm_num)).2.2
  have v4118 : σ (.n 4118) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 74) (by norm_num)).2.2
  have v4342 : σ (.n 4342) = ev 43 := by
    rw [← hev 43 (by norm_num)]; exact (vt_eval h (k := 104) (by norm_num)).2.2
  have v4346 : σ (.n 4346) = ev 44 := by
    rw [← hev 44 (by norm_num)]; exact (vt_eval h (k := 105) (by norm_num)).2.2
  have v4350 : σ (.n 4350) = ev 45 := by
    rw [← hev 45 (by norm_num)]; exact (vt_eval h (k := 106) (by norm_num)).2.2
  have v4607 : σ (.n 4607) = ev 80 := by
    rw [← hev 80 (by norm_num)]; exact (vt_eval h (k := 141) (by norm_num)).2.2
  have hB : σ (.n 5597) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 9], 4)], [([80], 1), ([13, 80], 2), ([13, 80], 1)], [([44], 1), ([11, 44], 1), ([11, 43], 1)], [([45], 1), ([11, 45], 1), ([11, 44], 1)]] := by
    simp only [v4607, v4350, v4346, v4342, v4118, v4110, v4089, v4031, a5173, a5172, a5171, e5170, a5169,
      a5168, e5167, a5166, a5165, e5164, a5163, a5162, e5161, a5160, e5159, a4535, a4534,
      a4533, a4532, a4531, a4530, a4529, a4528, a4527, a4526, a4525, a4524, a4523, a4522,
      a4521, a4520, a4519, a4518, a4517, a4516, a4515, a4514]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5175, a5174, hB]

set_option maxRecDepth 10000 in
theorem vtB05_18 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5616) = σ (.n 5599) + σ (.n 1210) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 9], 8)], [([81], 1), ([13, 81], 2), ([13, 81], 1)], [([46], 1), ([11, 46], 1), ([11, 45], 1)], [([47], 1), ([11, 47], 1), ([11, 46], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4536 [
    .atom (.const (.n 4960) (word 2 0)),
    .atom (.const (.n 4961) (word 8 0)),
    .atom (.mul (.n 4962) (.n 4031) (.n 4089)),
    .atom (.mul (.n 4963) (.n 4961) (.n 4962)),
    .atom (.copy (.n 4964) (.n 4963)),
    .atom (.const (.n 4965) (word 2 0)),
    .atom (.mul (.n 4966) (.n 4118) (.n 4611)),
    .atom (.mul (.n 4967) (.n 4965) (.n 4966)),
    .atom (.add (.n 4968) (.n 4611) (.n 4967)),
    .atom (.mul (.n 4969) (.n 4118) (.n 4611)),
    .atom (.add (.n 4970) (.n 4968) (.n 4969)),
    .atom (.copy (.n 4971) (.n 4970)),
    .atom (.mul (.n 4972) (.n 4110) (.n 4354)),
    .atom (.add (.n 4973) (.n 4354) (.n 4972)),
    .atom (.mul (.n 4974) (.n 4110) (.n 4350)),
    .atom (.add (.n 4975) (.n 4973) (.n 4974)),
    .atom (.copy (.n 4976) (.n 4975)),
    .atom (.mul (.n 4977) (.n 4110) (.n 4371)),
    .atom (.add (.n 4978) (.n 4371) (.n 4977)),
    .atom (.mul (.n 4979) (.n 4110) (.n 4354)),
    .atom (.add (.n 4980) (.n 4978) (.n 4979)),
    .atom (.copy (.n 4981) (.n 4980))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4536, a4537, a4538, a4539, a4540, a4541, a4542, a4543, a4544, a4545, a4546, a4547, a4548, a4549,
    a4550, a4551, a4552, a4553, a4554, a4555, a4556, a4557, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5176 [
    .atom (.load (.n 5600) (.n 13) 0),
    .atom (.mul (.n 5601) (.n 5600) (.n 4960)),
    .atom (.load (.n 5602) (.n 13) 1),
    .atom (.mul (.n 5603) (.n 5602) (.n 4964)),
    .atom (.add (.n 5604) (.n 5601) (.n 5603)),
    .atom (.load (.n 5605) (.n 13) 2),
    .atom (.mul (.n 5606) (.n 5605) (.n 4971)),
    .atom (.add (.n 5607) (.n 5604) (.n 5606)),
    .atom (.load (.n 5608) (.n 13) 3),
    .atom (.mul (.n 5609) (.n 5608) (.n 4976)),
    .atom (.add (.n 5610) (.n 5607) (.n 5609)),
    .atom (.load (.n 5611) (.n 13) 4),
    .atom (.mul (.n 5612) (.n 5611) (.n 4981)),
    .atom (.add (.n 5613) (.n 5610) (.n 5612)),
    .atom (.add (.n 5614) (.n 14) (.n 5613)),
    .atom (.mul (.n 5615) (.n 1210) (.n 5614)),
    .atom (.add (.n 5616) (.n 5599) (.n 5615))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5176, a5177, a5178, a5179, a5180, a5181, a5182, a5183, a5184, a5185, a5186, a5187, a5188, a5189,
    a5190, a5191, a5192, -⟩ := hs1
  have e5176 := tb_loadHolds_unique a5176 (hw 0 (by norm_num))
  have e5178 := tb_loadHolds_unique a5178 (hw 1 (by norm_num))
  have e5181 := tb_loadHolds_unique a5181 (hw 2 (by norm_num))
  have e5184 := tb_loadHolds_unique a5184 (hw 3 (by norm_num))
  have e5187 := tb_loadHolds_unique a5187 (hw 4 (by norm_num))
  have v4031 : σ (.n 4031) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 62) (by norm_num)).2.2
  have v4089 : σ (.n 4089) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 70) (by norm_num)).2.2
  have v4110 : σ (.n 4110) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_eval h (k := 72) (by norm_num)).2.2
  have v4118 : σ (.n 4118) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 74) (by norm_num)).2.2
  have v4350 : σ (.n 4350) = ev 45 := by
    rw [← hev 45 (by norm_num)]; exact (vt_eval h (k := 106) (by norm_num)).2.2
  have v4354 : σ (.n 4354) = ev 46 := by
    rw [← hev 46 (by norm_num)]; exact (vt_eval h (k := 107) (by norm_num)).2.2
  have v4371 : σ (.n 4371) = ev 47 := by
    rw [← hev 47 (by norm_num)]; exact (vt_eval h (k := 108) (by norm_num)).2.2
  have v4611 : σ (.n 4611) = ev 81 := by
    rw [← hev 81 (by norm_num)]; exact (vt_eval h (k := 142) (by norm_num)).2.2
  have hB : σ (.n 5614) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 9], 8)], [([81], 1), ([13, 81], 2), ([13, 81], 1)], [([46], 1), ([11, 46], 1), ([11, 45], 1)], [([47], 1), ([11, 47], 1), ([11, 46], 1)]] := by
    simp only [v4611, v4371, v4354, v4350, v4118, v4110, v4089, v4031, a5190, a5189, a5188, e5187, a5186,
      a5185, e5184, a5183, a5182, e5181, a5180, a5179, e5178, a5177, e5176, a4557, a4556,
      a4555, a4554, a4553, a4552, a4551, a4550, a4549, a4548, a4547, a4546, a4545, a4544,
      a4543, a4542, a4541, a4540, a4539, a4538, a4537, a4536]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5192, a5191, hB]

set_option maxRecDepth 10000 in
theorem vtB05_19 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5633) = σ (.n 5616) + σ (.n 1219) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 9], 16)], [([82], 1), ([13, 82], 2), ([13, 82], 1)], [([48], 1), ([11, 48], 1), ([11, 47], 1)], [([49], 1), ([11, 49], 1), ([11, 48], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4558 [
    .atom (.const (.n 4982) (word 2 0)),
    .atom (.const (.n 4983) (word 16 0)),
    .atom (.mul (.n 4984) (.n 4031) (.n 4089)),
    .atom (.mul (.n 4985) (.n 4983) (.n 4984)),
    .atom (.copy (.n 4986) (.n 4985)),
    .atom (.const (.n 4987) (word 2 0)),
    .atom (.mul (.n 4988) (.n 4118) (.n 4615)),
    .atom (.mul (.n 4989) (.n 4987) (.n 4988)),
    .atom (.add (.n 4990) (.n 4615) (.n 4989)),
    .atom (.mul (.n 4991) (.n 4118) (.n 4615)),
    .atom (.add (.n 4992) (.n 4990) (.n 4991)),
    .atom (.copy (.n 4993) (.n 4992)),
    .atom (.mul (.n 4994) (.n 4110) (.n 4375)),
    .atom (.add (.n 4995) (.n 4375) (.n 4994)),
    .atom (.mul (.n 4996) (.n 4110) (.n 4371)),
    .atom (.add (.n 4997) (.n 4995) (.n 4996)),
    .atom (.copy (.n 4998) (.n 4997)),
    .atom (.mul (.n 4999) (.n 4110) (.n 4379)),
    .atom (.add (.n 5000) (.n 4379) (.n 4999)),
    .atom (.mul (.n 5001) (.n 4110) (.n 4375)),
    .atom (.add (.n 5002) (.n 5000) (.n 5001)),
    .atom (.copy (.n 5003) (.n 5002))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4558, a4559, a4560, a4561, a4562, a4563, a4564, a4565, a4566, a4567, a4568, a4569, a4570, a4571,
    a4572, a4573, a4574, a4575, a4576, a4577, a4578, a4579, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5193 [
    .atom (.load (.n 5617) (.n 13) 0),
    .atom (.mul (.n 5618) (.n 5617) (.n 4982)),
    .atom (.load (.n 5619) (.n 13) 1),
    .atom (.mul (.n 5620) (.n 5619) (.n 4986)),
    .atom (.add (.n 5621) (.n 5618) (.n 5620)),
    .atom (.load (.n 5622) (.n 13) 2),
    .atom (.mul (.n 5623) (.n 5622) (.n 4993)),
    .atom (.add (.n 5624) (.n 5621) (.n 5623)),
    .atom (.load (.n 5625) (.n 13) 3),
    .atom (.mul (.n 5626) (.n 5625) (.n 4998)),
    .atom (.add (.n 5627) (.n 5624) (.n 5626)),
    .atom (.load (.n 5628) (.n 13) 4),
    .atom (.mul (.n 5629) (.n 5628) (.n 5003)),
    .atom (.add (.n 5630) (.n 5627) (.n 5629)),
    .atom (.add (.n 5631) (.n 14) (.n 5630)),
    .atom (.mul (.n 5632) (.n 1219) (.n 5631)),
    .atom (.add (.n 5633) (.n 5616) (.n 5632))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5193, a5194, a5195, a5196, a5197, a5198, a5199, a5200, a5201, a5202, a5203, a5204, a5205, a5206,
    a5207, a5208, a5209, -⟩ := hs1
  have e5193 := tb_loadHolds_unique a5193 (hw 0 (by norm_num))
  have e5195 := tb_loadHolds_unique a5195 (hw 1 (by norm_num))
  have e5198 := tb_loadHolds_unique a5198 (hw 2 (by norm_num))
  have e5201 := tb_loadHolds_unique a5201 (hw 3 (by norm_num))
  have e5204 := tb_loadHolds_unique a5204 (hw 4 (by norm_num))
  have v4031 : σ (.n 4031) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 62) (by norm_num)).2.2
  have v4089 : σ (.n 4089) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 70) (by norm_num)).2.2
  have v4110 : σ (.n 4110) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_eval h (k := 72) (by norm_num)).2.2
  have v4118 : σ (.n 4118) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 74) (by norm_num)).2.2
  have v4371 : σ (.n 4371) = ev 47 := by
    rw [← hev 47 (by norm_num)]; exact (vt_eval h (k := 108) (by norm_num)).2.2
  have v4375 : σ (.n 4375) = ev 48 := by
    rw [← hev 48 (by norm_num)]; exact (vt_eval h (k := 109) (by norm_num)).2.2
  have v4379 : σ (.n 4379) = ev 49 := by
    rw [← hev 49 (by norm_num)]; exact (vt_eval h (k := 110) (by norm_num)).2.2
  have v4615 : σ (.n 4615) = ev 82 := by
    rw [← hev 82 (by norm_num)]; exact (vt_eval h (k := 143) (by norm_num)).2.2
  have hB : σ (.n 5631) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 9], 16)], [([82], 1), ([13, 82], 2), ([13, 82], 1)], [([48], 1), ([11, 48], 1), ([11, 47], 1)], [([49], 1), ([11, 49], 1), ([11, 48], 1)]] := by
    simp only [v4615, v4379, v4375, v4371, v4118, v4110, v4089, v4031, a5207, a5206, a5205, e5204, a5203,
      a5202, e5201, a5200, a5199, e5198, a5197, a5196, e5195, a5194, e5193, a4579, a4578,
      a4577, a4576, a4575, a4574, a4573, a4572, a4571, a4570, a4569, a4568, a4567, a4566,
      a4565, a4564, a4563, a4562, a4561, a4560, a4559, a4558]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5209, a5208, hB]

set_option maxRecDepth 10000 in
theorem vtB05_20 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5650) = σ (.n 5633) + σ (.n 1228) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 9], 32)], [([83], 1), ([13, 83], 2), ([13, 83], 1)], [([50], 1), ([11, 50], 1), ([11, 49], 1)], [([51], 1), ([11, 51], 1), ([11, 50], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4580 [
    .atom (.const (.n 5004) (word 2 0)),
    .atom (.const (.n 5005) (word 32 0)),
    .atom (.mul (.n 5006) (.n 4031) (.n 4089)),
    .atom (.mul (.n 5007) (.n 5005) (.n 5006)),
    .atom (.copy (.n 5008) (.n 5007)),
    .atom (.const (.n 5009) (word 2 0)),
    .atom (.mul (.n 5010) (.n 4118) (.n 4632)),
    .atom (.mul (.n 5011) (.n 5009) (.n 5010)),
    .atom (.add (.n 5012) (.n 4632) (.n 5011)),
    .atom (.mul (.n 5013) (.n 4118) (.n 4632)),
    .atom (.add (.n 5014) (.n 5012) (.n 5013)),
    .atom (.copy (.n 5015) (.n 5014)),
    .atom (.mul (.n 5016) (.n 4110) (.n 4383)),
    .atom (.add (.n 5017) (.n 4383) (.n 5016)),
    .atom (.mul (.n 5018) (.n 4110) (.n 4379)),
    .atom (.add (.n 5019) (.n 5017) (.n 5018)),
    .atom (.copy (.n 5020) (.n 5019)),
    .atom (.mul (.n 5021) (.n 4110) (.n 4400)),
    .atom (.add (.n 5022) (.n 4400) (.n 5021)),
    .atom (.mul (.n 5023) (.n 4110) (.n 4383)),
    .atom (.add (.n 5024) (.n 5022) (.n 5023)),
    .atom (.copy (.n 5025) (.n 5024))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4580, a4581, a4582, a4583, a4584, a4585, a4586, a4587, a4588, a4589, a4590, a4591, a4592, a4593,
    a4594, a4595, a4596, a4597, a4598, a4599, a4600, a4601, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5210 [
    .atom (.load (.n 5634) (.n 13) 0),
    .atom (.mul (.n 5635) (.n 5634) (.n 5004)),
    .atom (.load (.n 5636) (.n 13) 1),
    .atom (.mul (.n 5637) (.n 5636) (.n 5008)),
    .atom (.add (.n 5638) (.n 5635) (.n 5637)),
    .atom (.load (.n 5639) (.n 13) 2),
    .atom (.mul (.n 5640) (.n 5639) (.n 5015)),
    .atom (.add (.n 5641) (.n 5638) (.n 5640)),
    .atom (.load (.n 5642) (.n 13) 3),
    .atom (.mul (.n 5643) (.n 5642) (.n 5020)),
    .atom (.add (.n 5644) (.n 5641) (.n 5643)),
    .atom (.load (.n 5645) (.n 13) 4),
    .atom (.mul (.n 5646) (.n 5645) (.n 5025)),
    .atom (.add (.n 5647) (.n 5644) (.n 5646)),
    .atom (.add (.n 5648) (.n 14) (.n 5647)),
    .atom (.mul (.n 5649) (.n 1228) (.n 5648)),
    .atom (.add (.n 5650) (.n 5633) (.n 5649))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5210, a5211, a5212, a5213, a5214, a5215, a5216, a5217, a5218, a5219, a5220, a5221, a5222, a5223,
    a5224, a5225, a5226, -⟩ := hs1
  have e5210 := tb_loadHolds_unique a5210 (hw 0 (by norm_num))
  have e5212 := tb_loadHolds_unique a5212 (hw 1 (by norm_num))
  have e5215 := tb_loadHolds_unique a5215 (hw 2 (by norm_num))
  have e5218 := tb_loadHolds_unique a5218 (hw 3 (by norm_num))
  have e5221 := tb_loadHolds_unique a5221 (hw 4 (by norm_num))
  have v4031 : σ (.n 4031) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 62) (by norm_num)).2.2
  have v4089 : σ (.n 4089) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 70) (by norm_num)).2.2
  have v4110 : σ (.n 4110) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_eval h (k := 72) (by norm_num)).2.2
  have v4118 : σ (.n 4118) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 74) (by norm_num)).2.2
  have v4379 : σ (.n 4379) = ev 49 := by
    rw [← hev 49 (by norm_num)]; exact (vt_eval h (k := 110) (by norm_num)).2.2
  have v4383 : σ (.n 4383) = ev 50 := by
    rw [← hev 50 (by norm_num)]; exact (vt_eval h (k := 111) (by norm_num)).2.2
  have v4400 : σ (.n 4400) = ev 51 := by
    rw [← hev 51 (by norm_num)]; exact (vt_eval h (k := 112) (by norm_num)).2.2
  have v4632 : σ (.n 4632) = ev 83 := by
    rw [← hev 83 (by norm_num)]; exact (vt_eval h (k := 144) (by norm_num)).2.2
  have hB : σ (.n 5648) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 9], 32)], [([83], 1), ([13, 83], 2), ([13, 83], 1)], [([50], 1), ([11, 50], 1), ([11, 49], 1)], [([51], 1), ([11, 51], 1), ([11, 50], 1)]] := by
    simp only [v4632, v4400, v4383, v4379, v4118, v4110, v4089, v4031, a5224, a5223, a5222, e5221, a5220,
      a5219, e5218, a5217, a5216, e5215, a5214, a5213, e5212, a5211, e5210, a4601, a4600,
      a4599, a4598, a4597, a4596, a4595, a4594, a4593, a4592, a4591, a4590, a4589, a4588,
      a4587, a4586, a4585, a4584, a4583, a4582, a4581, a4580]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5226, a5225, hB]

set_option maxRecDepth 10000 in
theorem vtB05_21 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5667) = σ (.n 5650) + σ (.n 1237) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 9], 64)], [([84], 1), ([13, 84], 2), ([13, 84], 1)], [([52], 1), ([11, 52], 1), ([11, 51], 1)], [([53], 1), ([11, 53], 1), ([11, 52], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4602 [
    .atom (.const (.n 5026) (word 2 0)),
    .atom (.const (.n 5027) (word 64 0)),
    .atom (.mul (.n 5028) (.n 4031) (.n 4089)),
    .atom (.mul (.n 5029) (.n 5027) (.n 5028)),
    .atom (.copy (.n 5030) (.n 5029)),
    .atom (.const (.n 5031) (word 2 0)),
    .atom (.mul (.n 5032) (.n 4118) (.n 4636)),
    .atom (.mul (.n 5033) (.n 5031) (.n 5032)),
    .atom (.add (.n 5034) (.n 4636) (.n 5033)),
    .atom (.mul (.n 5035) (.n 4118) (.n 4636)),
    .atom (.add (.n 5036) (.n 5034) (.n 5035)),
    .atom (.copy (.n 5037) (.n 5036)),
    .atom (.mul (.n 5038) (.n 4110) (.n 4404)),
    .atom (.add (.n 5039) (.n 4404) (.n 5038)),
    .atom (.mul (.n 5040) (.n 4110) (.n 4400)),
    .atom (.add (.n 5041) (.n 5039) (.n 5040)),
    .atom (.copy (.n 5042) (.n 5041)),
    .atom (.mul (.n 5043) (.n 4110) (.n 4408)),
    .atom (.add (.n 5044) (.n 4408) (.n 5043)),
    .atom (.mul (.n 5045) (.n 4110) (.n 4404)),
    .atom (.add (.n 5046) (.n 5044) (.n 5045)),
    .atom (.copy (.n 5047) (.n 5046))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4602, a4603, a4604, a4605, a4606, a4607, a4608, a4609, a4610, a4611, a4612, a4613, a4614, a4615,
    a4616, a4617, a4618, a4619, a4620, a4621, a4622, a4623, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5227 [
    .atom (.load (.n 5651) (.n 13) 0),
    .atom (.mul (.n 5652) (.n 5651) (.n 5026)),
    .atom (.load (.n 5653) (.n 13) 1),
    .atom (.mul (.n 5654) (.n 5653) (.n 5030)),
    .atom (.add (.n 5655) (.n 5652) (.n 5654)),
    .atom (.load (.n 5656) (.n 13) 2),
    .atom (.mul (.n 5657) (.n 5656) (.n 5037)),
    .atom (.add (.n 5658) (.n 5655) (.n 5657)),
    .atom (.load (.n 5659) (.n 13) 3),
    .atom (.mul (.n 5660) (.n 5659) (.n 5042)),
    .atom (.add (.n 5661) (.n 5658) (.n 5660)),
    .atom (.load (.n 5662) (.n 13) 4),
    .atom (.mul (.n 5663) (.n 5662) (.n 5047)),
    .atom (.add (.n 5664) (.n 5661) (.n 5663)),
    .atom (.add (.n 5665) (.n 14) (.n 5664)),
    .atom (.mul (.n 5666) (.n 1237) (.n 5665)),
    .atom (.add (.n 5667) (.n 5650) (.n 5666))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5227, a5228, a5229, a5230, a5231, a5232, a5233, a5234, a5235, a5236, a5237, a5238, a5239, a5240,
    a5241, a5242, a5243, -⟩ := hs1
  have e5227 := tb_loadHolds_unique a5227 (hw 0 (by norm_num))
  have e5229 := tb_loadHolds_unique a5229 (hw 1 (by norm_num))
  have e5232 := tb_loadHolds_unique a5232 (hw 2 (by norm_num))
  have e5235 := tb_loadHolds_unique a5235 (hw 3 (by norm_num))
  have e5238 := tb_loadHolds_unique a5238 (hw 4 (by norm_num))
  have v4031 : σ (.n 4031) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 62) (by norm_num)).2.2
  have v4089 : σ (.n 4089) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 70) (by norm_num)).2.2
  have v4110 : σ (.n 4110) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_eval h (k := 72) (by norm_num)).2.2
  have v4118 : σ (.n 4118) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 74) (by norm_num)).2.2
  have v4400 : σ (.n 4400) = ev 51 := by
    rw [← hev 51 (by norm_num)]; exact (vt_eval h (k := 112) (by norm_num)).2.2
  have v4404 : σ (.n 4404) = ev 52 := by
    rw [← hev 52 (by norm_num)]; exact (vt_eval h (k := 113) (by norm_num)).2.2
  have v4408 : σ (.n 4408) = ev 53 := by
    rw [← hev 53 (by norm_num)]; exact (vt_eval h (k := 114) (by norm_num)).2.2
  have v4636 : σ (.n 4636) = ev 84 := by
    rw [← hev 84 (by norm_num)]; exact (vt_eval h (k := 145) (by norm_num)).2.2
  have hB : σ (.n 5665) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 9], 64)], [([84], 1), ([13, 84], 2), ([13, 84], 1)], [([52], 1), ([11, 52], 1), ([11, 51], 1)], [([53], 1), ([11, 53], 1), ([11, 52], 1)]] := by
    simp only [v4636, v4408, v4404, v4400, v4118, v4110, v4089, v4031, a5241, a5240, a5239, e5238, a5237,
      a5236, e5235, a5234, a5233, e5232, a5231, a5230, e5229, a5228, e5227, a4623, a4622,
      a4621, a4620, a4619, a4618, a4617, a4616, a4615, a4614, a4613, a4612, a4611, a4610,
      a4609, a4608, a4607, a4606, a4605, a4604, a4603, a4602]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5243, a5242, hB]

set_option maxRecDepth 10000 in
theorem vtB05_22 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5684) = σ (.n 5667) + σ (.n 1246) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 9], 128)], [([85], 1), ([13, 85], 2), ([13, 85], 1)], [([54], 1), ([11, 54], 1), ([11, 53], 1)], [([55], 1), ([11, 55], 1), ([11, 54], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4624 [
    .atom (.const (.n 5048) (word 2 0)),
    .atom (.const (.n 5049) (word 128 0)),
    .atom (.mul (.n 5050) (.n 4031) (.n 4089)),
    .atom (.mul (.n 5051) (.n 5049) (.n 5050)),
    .atom (.copy (.n 5052) (.n 5051)),
    .atom (.const (.n 5053) (word 2 0)),
    .atom (.mul (.n 5054) (.n 4118) (.n 4640)),
    .atom (.mul (.n 5055) (.n 5053) (.n 5054)),
    .atom (.add (.n 5056) (.n 4640) (.n 5055)),
    .atom (.mul (.n 5057) (.n 4118) (.n 4640)),
    .atom (.add (.n 5058) (.n 5056) (.n 5057)),
    .atom (.copy (.n 5059) (.n 5058)),
    .atom (.mul (.n 5060) (.n 4110) (.n 4412)),
    .atom (.add (.n 5061) (.n 4412) (.n 5060)),
    .atom (.mul (.n 5062) (.n 4110) (.n 4408)),
    .atom (.add (.n 5063) (.n 5061) (.n 5062)),
    .atom (.copy (.n 5064) (.n 5063)),
    .atom (.mul (.n 5065) (.n 4110) (.n 4429)),
    .atom (.add (.n 5066) (.n 4429) (.n 5065)),
    .atom (.mul (.n 5067) (.n 4110) (.n 4412)),
    .atom (.add (.n 5068) (.n 5066) (.n 5067)),
    .atom (.copy (.n 5069) (.n 5068))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4624, a4625, a4626, a4627, a4628, a4629, a4630, a4631, a4632, a4633, a4634, a4635, a4636, a4637,
    a4638, a4639, a4640, a4641, a4642, a4643, a4644, a4645, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5244 [
    .atom (.load (.n 5668) (.n 13) 0),
    .atom (.mul (.n 5669) (.n 5668) (.n 5048)),
    .atom (.load (.n 5670) (.n 13) 1),
    .atom (.mul (.n 5671) (.n 5670) (.n 5052)),
    .atom (.add (.n 5672) (.n 5669) (.n 5671)),
    .atom (.load (.n 5673) (.n 13) 2),
    .atom (.mul (.n 5674) (.n 5673) (.n 5059)),
    .atom (.add (.n 5675) (.n 5672) (.n 5674)),
    .atom (.load (.n 5676) (.n 13) 3),
    .atom (.mul (.n 5677) (.n 5676) (.n 5064)),
    .atom (.add (.n 5678) (.n 5675) (.n 5677)),
    .atom (.load (.n 5679) (.n 13) 4),
    .atom (.mul (.n 5680) (.n 5679) (.n 5069)),
    .atom (.add (.n 5681) (.n 5678) (.n 5680)),
    .atom (.add (.n 5682) (.n 14) (.n 5681)),
    .atom (.mul (.n 5683) (.n 1246) (.n 5682)),
    .atom (.add (.n 5684) (.n 5667) (.n 5683))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5244, a5245, a5246, a5247, a5248, a5249, a5250, a5251, a5252, a5253, a5254, a5255, a5256, a5257,
    a5258, a5259, a5260, -⟩ := hs1
  have e5244 := tb_loadHolds_unique a5244 (hw 0 (by norm_num))
  have e5246 := tb_loadHolds_unique a5246 (hw 1 (by norm_num))
  have e5249 := tb_loadHolds_unique a5249 (hw 2 (by norm_num))
  have e5252 := tb_loadHolds_unique a5252 (hw 3 (by norm_num))
  have e5255 := tb_loadHolds_unique a5255 (hw 4 (by norm_num))
  have v4031 : σ (.n 4031) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 62) (by norm_num)).2.2
  have v4089 : σ (.n 4089) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 70) (by norm_num)).2.2
  have v4110 : σ (.n 4110) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_eval h (k := 72) (by norm_num)).2.2
  have v4118 : σ (.n 4118) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 74) (by norm_num)).2.2
  have v4408 : σ (.n 4408) = ev 53 := by
    rw [← hev 53 (by norm_num)]; exact (vt_eval h (k := 114) (by norm_num)).2.2
  have v4412 : σ (.n 4412) = ev 54 := by
    rw [← hev 54 (by norm_num)]; exact (vt_eval h (k := 115) (by norm_num)).2.2
  have v4429 : σ (.n 4429) = ev 55 := by
    rw [← hev 55 (by norm_num)]; exact (vt_eval h (k := 116) (by norm_num)).2.2
  have v4640 : σ (.n 4640) = ev 85 := by
    rw [← hev 85 (by norm_num)]; exact (vt_eval h (k := 146) (by norm_num)).2.2
  have hB : σ (.n 5682) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 9], 128)], [([85], 1), ([13, 85], 2), ([13, 85], 1)], [([54], 1), ([11, 54], 1), ([11, 53], 1)], [([55], 1), ([11, 55], 1), ([11, 54], 1)]] := by
    simp only [v4640, v4429, v4412, v4408, v4118, v4110, v4089, v4031, a5258, a5257, a5256, e5255, a5254,
      a5253, e5252, a5251, a5250, e5249, a5248, a5247, e5246, a5245, e5244, a4645, a4644,
      a4643, a4642, a4641, a4640, a4639, a4638, a4637, a4636, a4635, a4634, a4633, a4632,
      a4631, a4630, a4629, a4628, a4627, a4626, a4625, a4624]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5260, a5259, hB]

set_option maxRecDepth 10000 in
theorem vtB05_23 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5701) = σ (.n 5684) + σ (.n 1255) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 9], 256)], [([86], 1), ([13, 86], 2), ([13, 86], 1)], [([56], 1), ([11, 56], 1), ([11, 55], 1)], [([11, 56], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4646 [
    .atom (.const (.n 5070) (word 2 0)),
    .atom (.const (.n 5071) (word 256 0)),
    .atom (.mul (.n 5072) (.n 4031) (.n 4089)),
    .atom (.mul (.n 5073) (.n 5071) (.n 5072)),
    .atom (.copy (.n 5074) (.n 5073)),
    .atom (.const (.n 5075) (word 2 0)),
    .atom (.mul (.n 5076) (.n 4118) (.n 4644)),
    .atom (.mul (.n 5077) (.n 5075) (.n 5076)),
    .atom (.add (.n 5078) (.n 4644) (.n 5077)),
    .atom (.mul (.n 5079) (.n 4118) (.n 4644)),
    .atom (.add (.n 5080) (.n 5078) (.n 5079)),
    .atom (.copy (.n 5081) (.n 5080)),
    .atom (.mul (.n 5082) (.n 4110) (.n 4433)),
    .atom (.add (.n 5083) (.n 4433) (.n 5082)),
    .atom (.mul (.n 5084) (.n 4110) (.n 4429)),
    .atom (.add (.n 5085) (.n 5083) (.n 5084)),
    .atom (.copy (.n 5086) (.n 5085)),
    .atom (.mul (.n 5087) (.n 4110) (.n 4433)),
    .atom (.copy (.n 5088) (.n 5087))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4646, a4647, a4648, a4649, a4650, a4651, a4652, a4653, a4654, a4655, a4656, a4657, a4658, a4659,
    a4660, a4661, a4662, a4663, a4664, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5261 [
    .atom (.load (.n 5685) (.n 13) 0),
    .atom (.mul (.n 5686) (.n 5685) (.n 5070)),
    .atom (.load (.n 5687) (.n 13) 1),
    .atom (.mul (.n 5688) (.n 5687) (.n 5074)),
    .atom (.add (.n 5689) (.n 5686) (.n 5688)),
    .atom (.load (.n 5690) (.n 13) 2),
    .atom (.mul (.n 5691) (.n 5690) (.n 5081)),
    .atom (.add (.n 5692) (.n 5689) (.n 5691)),
    .atom (.load (.n 5693) (.n 13) 3),
    .atom (.mul (.n 5694) (.n 5693) (.n 5086)),
    .atom (.add (.n 5695) (.n 5692) (.n 5694)),
    .atom (.load (.n 5696) (.n 13) 4),
    .atom (.mul (.n 5697) (.n 5696) (.n 5088)),
    .atom (.add (.n 5698) (.n 5695) (.n 5697)),
    .atom (.add (.n 5699) (.n 14) (.n 5698)),
    .atom (.mul (.n 5700) (.n 1255) (.n 5699)),
    .atom (.add (.n 5701) (.n 5684) (.n 5700))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5261, a5262, a5263, a5264, a5265, a5266, a5267, a5268, a5269, a5270, a5271, a5272, a5273, a5274,
    a5275, a5276, a5277, -⟩ := hs1
  have e5261 := tb_loadHolds_unique a5261 (hw 0 (by norm_num))
  have e5263 := tb_loadHolds_unique a5263 (hw 1 (by norm_num))
  have e5266 := tb_loadHolds_unique a5266 (hw 2 (by norm_num))
  have e5269 := tb_loadHolds_unique a5269 (hw 3 (by norm_num))
  have e5272 := tb_loadHolds_unique a5272 (hw 4 (by norm_num))
  have v4031 : σ (.n 4031) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 62) (by norm_num)).2.2
  have v4089 : σ (.n 4089) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 70) (by norm_num)).2.2
  have v4110 : σ (.n 4110) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_eval h (k := 72) (by norm_num)).2.2
  have v4118 : σ (.n 4118) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 74) (by norm_num)).2.2
  have v4429 : σ (.n 4429) = ev 55 := by
    rw [← hev 55 (by norm_num)]; exact (vt_eval h (k := 116) (by norm_num)).2.2
  have v4433 : σ (.n 4433) = ev 56 := by
    rw [← hev 56 (by norm_num)]; exact (vt_eval h (k := 117) (by norm_num)).2.2
  have v4644 : σ (.n 4644) = ev 86 := by
    rw [← hev 86 (by norm_num)]; exact (vt_eval h (k := 147) (by norm_num)).2.2
  have hB : σ (.n 5699) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 9], 256)], [([86], 1), ([13, 86], 2), ([13, 86], 1)], [([56], 1), ([11, 56], 1), ([11, 55], 1)], [([11, 56], 1)]] := by
    simp only [v4644, v4433, v4429, v4118, v4110, v4089, v4031, a5275, a5274, a5273, e5272, a5271, a5270,
      e5269, a5268, a5267, e5266, a5265, a5264, e5263, a5262, e5261, a4664, a4663, a4662,
      a4661, a4660, a4659, a4658, a4657, a4656, a4655, a4654, a4653, a4652, a4651, a4650,
      a4649, a4648, a4647, a4646]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5277, a5276, hB]

set_option maxRecDepth 10000 in
theorem vtB05_24 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5718) = σ (.n 5701) + σ (.n 1264) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 9], 512)], [([87], 1), ([13, 87], 2), ([13, 87], 1)], [([57], 1)], [([58], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4665 [
    .atom (.const (.n 5089) (word 2 0)),
    .atom (.const (.n 5090) (word 512 0)),
    .atom (.mul (.n 5091) (.n 4031) (.n 4089)),
    .atom (.mul (.n 5092) (.n 5090) (.n 5091)),
    .atom (.copy (.n 5093) (.n 5092)),
    .atom (.const (.n 5094) (word 2 0)),
    .atom (.mul (.n 5095) (.n 4118) (.n 4661)),
    .atom (.mul (.n 5096) (.n 5094) (.n 5095)),
    .atom (.add (.n 5097) (.n 4661) (.n 5096)),
    .atom (.mul (.n 5098) (.n 4118) (.n 4661)),
    .atom (.add (.n 5099) (.n 5097) (.n 5098)),
    .atom (.copy (.n 5100) (.n 5099)),
    .atom (.copy (.n 5101) (.n 4437)),
    .atom (.copy (.n 5102) (.n 4441))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4665, a4666, a4667, a4668, a4669, a4670, a4671, a4672, a4673, a4674, a4675, a4676, a4677, a4678,
    -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5278 [
    .atom (.load (.n 5702) (.n 13) 0),
    .atom (.mul (.n 5703) (.n 5702) (.n 5089)),
    .atom (.load (.n 5704) (.n 13) 1),
    .atom (.mul (.n 5705) (.n 5704) (.n 5093)),
    .atom (.add (.n 5706) (.n 5703) (.n 5705)),
    .atom (.load (.n 5707) (.n 13) 2),
    .atom (.mul (.n 5708) (.n 5707) (.n 5100)),
    .atom (.add (.n 5709) (.n 5706) (.n 5708)),
    .atom (.load (.n 5710) (.n 13) 3),
    .atom (.mul (.n 5711) (.n 5710) (.n 5101)),
    .atom (.add (.n 5712) (.n 5709) (.n 5711)),
    .atom (.load (.n 5713) (.n 13) 4),
    .atom (.mul (.n 5714) (.n 5713) (.n 5102)),
    .atom (.add (.n 5715) (.n 5712) (.n 5714)),
    .atom (.add (.n 5716) (.n 14) (.n 5715)),
    .atom (.mul (.n 5717) (.n 1264) (.n 5716)),
    .atom (.add (.n 5718) (.n 5701) (.n 5717))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5278, a5279, a5280, a5281, a5282, a5283, a5284, a5285, a5286, a5287, a5288, a5289, a5290, a5291,
    a5292, a5293, a5294, -⟩ := hs1
  have e5278 := tb_loadHolds_unique a5278 (hw 0 (by norm_num))
  have e5280 := tb_loadHolds_unique a5280 (hw 1 (by norm_num))
  have e5283 := tb_loadHolds_unique a5283 (hw 2 (by norm_num))
  have e5286 := tb_loadHolds_unique a5286 (hw 3 (by norm_num))
  have e5289 := tb_loadHolds_unique a5289 (hw 4 (by norm_num))
  have v4031 : σ (.n 4031) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 62) (by norm_num)).2.2
  have v4089 : σ (.n 4089) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 70) (by norm_num)).2.2
  have v4118 : σ (.n 4118) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 74) (by norm_num)).2.2
  have v4437 : σ (.n 4437) = ev 57 := by
    rw [← hev 57 (by norm_num)]; exact (vt_eval h (k := 118) (by norm_num)).2.2
  have v4441 : σ (.n 4441) = ev 58 := by
    rw [← hev 58 (by norm_num)]; exact (vt_eval h (k := 119) (by norm_num)).2.2
  have v4661 : σ (.n 4661) = ev 87 := by
    rw [← hev 87 (by norm_num)]; exact (vt_eval h (k := 148) (by norm_num)).2.2
  have hB : σ (.n 5716) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 9], 512)], [([87], 1), ([13, 87], 2), ([13, 87], 1)], [([57], 1)], [([58], 1)]] := by
    simp only [v4661, v4441, v4437, v4118, v4089, v4031, a5292, a5291, a5290, e5289, a5288, a5287, e5286,
      a5285, a5284, e5283, a5282, a5281, e5280, a5279, e5278, a4678, a4677, a4676, a4675,
      a4674, a4673, a4672, a4671, a4670, a4669, a4668, a4667, a4666, a4665]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5294, a5293, hB]

set_option maxRecDepth 10000 in
theorem vtB05_25 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5735) = σ (.n 5718) + σ (.n 1273) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 9], 1024)], [([88], 1), ([13, 88], 2), ([13, 88], 1)], [([59], 1)], [([60], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4679 [
    .atom (.const (.n 5103) (word 2 0)),
    .atom (.const (.n 5104) (word 1024 0)),
    .atom (.mul (.n 5105) (.n 4031) (.n 4089)),
    .atom (.mul (.n 5106) (.n 5104) (.n 5105)),
    .atom (.copy (.n 5107) (.n 5106)),
    .atom (.const (.n 5108) (word 2 0)),
    .atom (.mul (.n 5109) (.n 4118) (.n 4665)),
    .atom (.mul (.n 5110) (.n 5108) (.n 5109)),
    .atom (.add (.n 5111) (.n 4665) (.n 5110)),
    .atom (.mul (.n 5112) (.n 4118) (.n 4665)),
    .atom (.add (.n 5113) (.n 5111) (.n 5112)),
    .atom (.copy (.n 5114) (.n 5113)),
    .atom (.copy (.n 5115) (.n 4458)),
    .atom (.copy (.n 5116) (.n 4462))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4679, a4680, a4681, a4682, a4683, a4684, a4685, a4686, a4687, a4688, a4689, a4690, a4691, a4692,
    -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5295 [
    .atom (.load (.n 5719) (.n 13) 0),
    .atom (.mul (.n 5720) (.n 5719) (.n 5103)),
    .atom (.load (.n 5721) (.n 13) 1),
    .atom (.mul (.n 5722) (.n 5721) (.n 5107)),
    .atom (.add (.n 5723) (.n 5720) (.n 5722)),
    .atom (.load (.n 5724) (.n 13) 2),
    .atom (.mul (.n 5725) (.n 5724) (.n 5114)),
    .atom (.add (.n 5726) (.n 5723) (.n 5725)),
    .atom (.load (.n 5727) (.n 13) 3),
    .atom (.mul (.n 5728) (.n 5727) (.n 5115)),
    .atom (.add (.n 5729) (.n 5726) (.n 5728)),
    .atom (.load (.n 5730) (.n 13) 4),
    .atom (.mul (.n 5731) (.n 5730) (.n 5116)),
    .atom (.add (.n 5732) (.n 5729) (.n 5731)),
    .atom (.add (.n 5733) (.n 14) (.n 5732)),
    .atom (.mul (.n 5734) (.n 1273) (.n 5733)),
    .atom (.add (.n 5735) (.n 5718) (.n 5734))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5295, a5296, a5297, a5298, a5299, a5300, a5301, a5302, a5303, a5304, a5305, a5306, a5307, a5308,
    a5309, a5310, a5311, -⟩ := hs1
  have e5295 := tb_loadHolds_unique a5295 (hw 0 (by norm_num))
  have e5297 := tb_loadHolds_unique a5297 (hw 1 (by norm_num))
  have e5300 := tb_loadHolds_unique a5300 (hw 2 (by norm_num))
  have e5303 := tb_loadHolds_unique a5303 (hw 3 (by norm_num))
  have e5306 := tb_loadHolds_unique a5306 (hw 4 (by norm_num))
  have v4031 : σ (.n 4031) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 62) (by norm_num)).2.2
  have v4089 : σ (.n 4089) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 70) (by norm_num)).2.2
  have v4118 : σ (.n 4118) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 74) (by norm_num)).2.2
  have v4458 : σ (.n 4458) = ev 59 := by
    rw [← hev 59 (by norm_num)]; exact (vt_eval h (k := 120) (by norm_num)).2.2
  have v4462 : σ (.n 4462) = ev 60 := by
    rw [← hev 60 (by norm_num)]; exact (vt_eval h (k := 121) (by norm_num)).2.2
  have v4665 : σ (.n 4665) = ev 88 := by
    rw [← hev 88 (by norm_num)]; exact (vt_eval h (k := 149) (by norm_num)).2.2
  have hB : σ (.n 5733) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 9], 1024)], [([88], 1), ([13, 88], 2), ([13, 88], 1)], [([59], 1)], [([60], 1)]] := by
    simp only [v4665, v4462, v4458, v4118, v4089, v4031, a5309, a5308, a5307, e5306, a5305, a5304, e5303,
      a5302, a5301, e5300, a5299, a5298, e5297, a5296, e5295, a4692, a4691, a4690, a4689,
      a4688, a4687, a4686, a4685, a4684, a4683, a4682, a4681, a4680, a4679]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5311, a5310, hB]

set_option maxRecDepth 10000 in
theorem vtB05_26 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5752) = σ (.n 5735) + σ (.n 1282) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 9], 2048)], [([89], 1), ([13, 89], 2), ([13, 89], 1)], [([61], 1)], [([62], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4693 [
    .atom (.const (.n 5117) (word 2 0)),
    .atom (.const (.n 5118) (word 2048 0)),
    .atom (.mul (.n 5119) (.n 4031) (.n 4089)),
    .atom (.mul (.n 5120) (.n 5118) (.n 5119)),
    .atom (.copy (.n 5121) (.n 5120)),
    .atom (.const (.n 5122) (word 2 0)),
    .atom (.mul (.n 5123) (.n 4118) (.n 4669)),
    .atom (.mul (.n 5124) (.n 5122) (.n 5123)),
    .atom (.add (.n 5125) (.n 4669) (.n 5124)),
    .atom (.mul (.n 5126) (.n 4118) (.n 4669)),
    .atom (.add (.n 5127) (.n 5125) (.n 5126)),
    .atom (.copy (.n 5128) (.n 5127)),
    .atom (.copy (.n 5129) (.n 4466)),
    .atom (.copy (.n 5130) (.n 4470))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4693, a4694, a4695, a4696, a4697, a4698, a4699, a4700, a4701, a4702, a4703, a4704, a4705, a4706,
    -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5312 [
    .atom (.load (.n 5736) (.n 13) 0),
    .atom (.mul (.n 5737) (.n 5736) (.n 5117)),
    .atom (.load (.n 5738) (.n 13) 1),
    .atom (.mul (.n 5739) (.n 5738) (.n 5121)),
    .atom (.add (.n 5740) (.n 5737) (.n 5739)),
    .atom (.load (.n 5741) (.n 13) 2),
    .atom (.mul (.n 5742) (.n 5741) (.n 5128)),
    .atom (.add (.n 5743) (.n 5740) (.n 5742)),
    .atom (.load (.n 5744) (.n 13) 3),
    .atom (.mul (.n 5745) (.n 5744) (.n 5129)),
    .atom (.add (.n 5746) (.n 5743) (.n 5745)),
    .atom (.load (.n 5747) (.n 13) 4),
    .atom (.mul (.n 5748) (.n 5747) (.n 5130)),
    .atom (.add (.n 5749) (.n 5746) (.n 5748)),
    .atom (.add (.n 5750) (.n 14) (.n 5749)),
    .atom (.mul (.n 5751) (.n 1282) (.n 5750)),
    .atom (.add (.n 5752) (.n 5735) (.n 5751))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5312, a5313, a5314, a5315, a5316, a5317, a5318, a5319, a5320, a5321, a5322, a5323, a5324, a5325,
    a5326, a5327, a5328, -⟩ := hs1
  have e5312 := tb_loadHolds_unique a5312 (hw 0 (by norm_num))
  have e5314 := tb_loadHolds_unique a5314 (hw 1 (by norm_num))
  have e5317 := tb_loadHolds_unique a5317 (hw 2 (by norm_num))
  have e5320 := tb_loadHolds_unique a5320 (hw 3 (by norm_num))
  have e5323 := tb_loadHolds_unique a5323 (hw 4 (by norm_num))
  have v4031 : σ (.n 4031) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 62) (by norm_num)).2.2
  have v4089 : σ (.n 4089) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 70) (by norm_num)).2.2
  have v4118 : σ (.n 4118) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 74) (by norm_num)).2.2
  have v4466 : σ (.n 4466) = ev 61 := by
    rw [← hev 61 (by norm_num)]; exact (vt_eval h (k := 122) (by norm_num)).2.2
  have v4470 : σ (.n 4470) = ev 62 := by
    rw [← hev 62 (by norm_num)]; exact (vt_eval h (k := 123) (by norm_num)).2.2
  have v4669 : σ (.n 4669) = ev 89 := by
    rw [← hev 89 (by norm_num)]; exact (vt_eval h (k := 150) (by norm_num)).2.2
  have hB : σ (.n 5750) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 9], 2048)], [([89], 1), ([13, 89], 2), ([13, 89], 1)], [([61], 1)], [([62], 1)]] := by
    simp only [v4669, v4470, v4466, v4118, v4089, v4031, a5326, a5325, a5324, e5323, a5322, a5321, e5320,
      a5319, a5318, e5317, a5316, a5315, e5314, a5313, e5312, a4706, a4705, a4704, a4703,
      a4702, a4701, a4700, a4699, a4698, a4697, a4696, a4695, a4694, a4693]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5328, a5327, hB]

set_option maxRecDepth 10000 in
theorem vtB05_27 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 92, σ (.n (vtEvB (61 + c))) = ev c) :
    σ (.n 5769) = σ (.n 5752) + σ (.n 1291) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 9], 4096)], [([90], 1), ([13, 90], 2), ([13, 90], 1)], [([63], 1)], [([64], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 4707 [
    .atom (.const (.n 5131) (word 2 0)),
    .atom (.const (.n 5132) (word 4096 0)),
    .atom (.mul (.n 5133) (.n 4031) (.n 4089)),
    .atom (.mul (.n 5134) (.n 5132) (.n 5133)),
    .atom (.copy (.n 5135) (.n 5134)),
    .atom (.const (.n 5136) (word 2 0)),
    .atom (.mul (.n 5137) (.n 4118) (.n 4673)),
    .atom (.mul (.n 5138) (.n 5136) (.n 5137)),
    .atom (.add (.n 5139) (.n 4673) (.n 5138)),
    .atom (.mul (.n 5140) (.n 4118) (.n 4673)),
    .atom (.add (.n 5141) (.n 5139) (.n 5140)),
    .atom (.copy (.n 5142) (.n 5141)),
    .atom (.copy (.n 5143) (.n 4487)),
    .atom (.copy (.n 5144) (.n 4491))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a4707, a4708, a4709, a4710, a4711, a4712, a4713, a4714, a4715, a4716, a4717, a4718, a4719, a4720,
    -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 5329 [
    .atom (.load (.n 5753) (.n 13) 0),
    .atom (.mul (.n 5754) (.n 5753) (.n 5131)),
    .atom (.load (.n 5755) (.n 13) 1),
    .atom (.mul (.n 5756) (.n 5755) (.n 5135)),
    .atom (.add (.n 5757) (.n 5754) (.n 5756)),
    .atom (.load (.n 5758) (.n 13) 2),
    .atom (.mul (.n 5759) (.n 5758) (.n 5142)),
    .atom (.add (.n 5760) (.n 5757) (.n 5759)),
    .atom (.load (.n 5761) (.n 13) 3),
    .atom (.mul (.n 5762) (.n 5761) (.n 5143)),
    .atom (.add (.n 5763) (.n 5760) (.n 5762)),
    .atom (.load (.n 5764) (.n 13) 4),
    .atom (.mul (.n 5765) (.n 5764) (.n 5144)),
    .atom (.add (.n 5766) (.n 5763) (.n 5765)),
    .atom (.add (.n 5767) (.n 14) (.n 5766)),
    .atom (.mul (.n 5768) (.n 1291) (.n 5767)),
    .atom (.add (.n 5769) (.n 5752) (.n 5768))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a5329, a5330, a5331, a5332, a5333, a5334, a5335, a5336, a5337, a5338, a5339, a5340, a5341, a5342,
    a5343, a5344, a5345, -⟩ := hs1
  have e5329 := tb_loadHolds_unique a5329 (hw 0 (by norm_num))
  have e5331 := tb_loadHolds_unique a5331 (hw 1 (by norm_num))
  have e5334 := tb_loadHolds_unique a5334 (hw 2 (by norm_num))
  have e5337 := tb_loadHolds_unique a5337 (hw 3 (by norm_num))
  have e5340 := tb_loadHolds_unique a5340 (hw 4 (by norm_num))
  have v4031 : σ (.n 4031) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 62) (by norm_num)).2.2
  have v4089 : σ (.n 4089) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 70) (by norm_num)).2.2
  have v4118 : σ (.n 4118) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 74) (by norm_num)).2.2
  have v4487 : σ (.n 4487) = ev 63 := by
    rw [← hev 63 (by norm_num)]; exact (vt_eval h (k := 124) (by norm_num)).2.2
  have v4491 : σ (.n 4491) = ev 64 := by
    rw [← hev 64 (by norm_num)]; exact (vt_eval h (k := 125) (by norm_num)).2.2
  have v4673 : σ (.n 4673) = ev 90 := by
    rw [← hev 90 (by norm_num)]; exact (vt_eval h (k := 151) (by norm_num)).2.2
  have hB : σ (.n 5767) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 9], 4096)], [([90], 1), ([13, 90], 2), ([13, 90], 1)], [([63], 1)], [([64], 1)]] := by
    simp only [v4673, v4491, v4487, v4118, v4089, v4031, a5343, a5342, a5341, e5340, a5339, a5338, e5337,
      a5336, a5335, e5334, a5333, a5332, e5331, a5330, e5329, a4720, a4719, a4718, a4717,
      a4716, a4715, a4714, a4713, a4712, a4711, a4710, a4709, a4708, a4707]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a5345, a5344, hB]

end
end LeanVM.Guest.B1.Tables
