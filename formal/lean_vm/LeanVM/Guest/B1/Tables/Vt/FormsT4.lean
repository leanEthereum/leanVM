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
    (hev : ∀ c < 14, σ (.n (vtEvB (53 + c))) = ev c) :
    σ (.n 4250) = σ (.n 1106) * vtBlockVal (σ (.n 14)) W ev
      [[([], 1)], [([13, 6], 1), ([13, 0], 2), ([0], 2)], [([13, 7], 1), ([13, 1], 1), ([1], 1)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 4028 [
    .atom (.load (.n 4230) (.n 13) 0),
    .atom (.mul (.n 4231) (.n 4221) (.n 4118)),
    .atom (.const (.n 4232) (word 2 0 0)),
    .atom (.mul (.n 4233) (.n 4221) (.n 4039)),
    .atom (.mul (.n 4234) (.n 4232) (.n 4233)),
    .atom (.add (.n 4235) (.n 4231) (.n 4234)),
    .atom (.const (.n 4236) (word 2 0 0)),
    .atom (.mul (.n 4237) (.n 4236) (.n 4039)),
    .atom (.add (.n 4238) (.n 4235) (.n 4237)),
    .atom (.load (.n 4239) (.n 13) 1),
    .atom (.mul (.n 4240) (.n 4239) (.n 4238)),
    .atom (.add (.n 4241) (.n 4230) (.n 4240)),
    .atom (.mul (.n 4242) (.n 4221) (.n 4142)),
    .atom (.mul (.n 4243) (.n 4221) (.n 4050)),
    .atom (.add (.n 4244) (.n 4242) (.n 4243)),
    .atom (.add (.n 4245) (.n 4244) (.n 4050)),
    .atom (.load (.n 4246) (.n 13) 2),
    .atom (.mul (.n 4247) (.n 4246) (.n 4245)),
    .atom (.add (.n 4248) (.n 4241) (.n 4247)),
    .atom (.add (.n 4249) (.n 14) (.n 4248)),
    .atom (.mul (.n 4250) (.n 1106) (.n 4249))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a4028, a4029, a4030, a4031, a4032, a4033, a4034, a4035, a4036, a4037, a4038, a4039, a4040, a4041,
    a4042, a4043, a4044, a4045, a4046, a4047, a4048, -⟩ := hs
  have e4028 := tb_loadHolds_unique a4028 (hw 0 (by norm_num))
  have e4037 := tb_loadHolds_unique a4037 (hw 1 (by norm_num))
  have e4044 := tb_loadHolds_unique a4044 (hw 2 (by norm_num))
  have v4039 : σ (.n 4039) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_eval h (k := 53) (by norm_num)).2.2
  have v4050 : σ (.n 4050) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 54) (by norm_num)).2.2
  have v4118 : σ (.n 4118) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_eval h (k := 59) (by norm_num)).2.2
  have v4142 : σ (.n 4142) = ev 7 := by
    rw [← hev 7 (by norm_num)]; exact (vt_eval h (k := 60) (by norm_num)).2.2
  have v4221 : σ (.n 4221) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 66) (by norm_num)).2.2
  have hB : σ (.n 4249) = vtBlockVal (σ (.n 14)) W ev [[([], 1)], [([13, 6], 1), ([13, 0], 2), ([0], 2)], [([13, 7], 1), ([13, 1], 1), ([1], 1)]] := by
    simp only [v4221, v4142, v4118, v4050, v4039, a4047, a4046, a4045, e4044, a4043, a4042, a4041, a4040,
      a4039, a4038, e4037, a4036, a4035, a4034, a4033, a4032, a4031, a4030, a4029, e4028]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a4048, hB]

set_option maxRecDepth 10000 in
theorem vtB04_1 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (53 + c))) = ev c) :
    σ (.n 4285) = σ (.n 4250) + σ (.n 1115) * vtBlockVal (σ (.n 14)) W ev
      [[([], 4)], [([0], 1)], [([11], 2)], [([], 16)], [([2], 1)], [([3], 1)], [([4], 1)], [([], 0)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 4049 [
    .atom (.load (.n 4251) (.n 13) 0),
    .atom (.const (.n 4252) (word 4 0 0)),
    .atom (.mul (.n 4253) (.n 4251) (.n 4252)),
    .atom (.load (.n 4254) (.n 13) 1),
    .atom (.mul (.n 4255) (.n 4254) (.n 4039)),
    .atom (.add (.n 4256) (.n 4253) (.n 4255)),
    .atom (.const (.n 4257) (word 2 0 0)),
    .atom (.mul (.n 4258) (.n 4257) (.n 4199)),
    .atom (.load (.n 4259) (.n 13) 2),
    .atom (.mul (.n 4260) (.n 4259) (.n 4258)),
    .atom (.add (.n 4261) (.n 4256) (.n 4260)),
    .atom (.load (.n 4262) (.n 13) 3),
    .atom (.const (.n 4263) (word 16 0 0)),
    .atom (.mul (.n 4264) (.n 4262) (.n 4263)),
    .atom (.add (.n 4265) (.n 4261) (.n 4264)),
    .atom (.load (.n 4266) (.n 13) 4),
    .atom (.mul (.n 4267) (.n 4266) (.n 4061)),
    .atom (.add (.n 4268) (.n 4265) (.n 4267)),
    .atom (.load (.n 4269) (.n 13) 5),
    .atom (.mul (.n 4270) (.n 4269) (.n 4085)),
    .atom (.add (.n 4271) (.n 4268) (.n 4270)),
    .atom (.load (.n 4272) (.n 13) 6),
    .atom (.mul (.n 4273) (.n 4272) (.n 4096)),
    .atom (.add (.n 4274) (.n 4271) (.n 4273)),
    .atom (.load (.n 4275) (.n 13) 7),
    .atom (.const (.n 4276) (word 0 0 0)),
    .atom (.mul (.n 4277) (.n 4275) (.n 4276)),
    .atom (.add (.n 4278) (.n 4274) (.n 4277)),
    .atom (.load (.n 4279) (.n 13) 8),
    .atom (.const (.n 4280) (word 0 0 0)),
    .atom (.mul (.n 4281) (.n 4279) (.n 4280)),
    .atom (.add (.n 4282) (.n 4278) (.n 4281)),
    .atom (.add (.n 4283) (.n 14) (.n 4282)),
    .atom (.mul (.n 4284) (.n 1115) (.n 4283)),
    .atom (.add (.n 4285) (.n 4250) (.n 4284))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a4049, a4050, a4051, a4052, a4053, a4054, a4055, a4056, a4057, a4058, a4059, a4060, a4061, a4062,
    a4063, a4064, a4065, a4066, a4067, a4068, a4069, a4070, a4071, a4072, a4073, a4074, a4075,
    a4076, a4077, a4078, a4079, a4080, a4081, a4082, a4083, -⟩ := hs
  have e4049 := tb_loadHolds_unique a4049 (hw 0 (by norm_num))
  have e4052 := tb_loadHolds_unique a4052 (hw 1 (by norm_num))
  have e4057 := tb_loadHolds_unique a4057 (hw 2 (by norm_num))
  have e4060 := tb_loadHolds_unique a4060 (hw 3 (by norm_num))
  have e4064 := tb_loadHolds_unique a4064 (hw 4 (by norm_num))
  have e4067 := tb_loadHolds_unique a4067 (hw 5 (by norm_num))
  have e4070 := tb_loadHolds_unique a4070 (hw 6 (by norm_num))
  have e4073 := tb_loadHolds_unique a4073 (hw 7 (by norm_num))
  have e4077 := tb_loadHolds_unique a4077 (hw 8 (by norm_num))
  have v4039 : σ (.n 4039) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_eval h (k := 53) (by norm_num)).2.2
  have v4061 : σ (.n 4061) = ev 2 := by
    rw [← hev 2 (by norm_num)]; exact (vt_eval h (k := 55) (by norm_num)).2.2
  have v4085 : σ (.n 4085) = ev 3 := by
    rw [← hev 3 (by norm_num)]; exact (vt_eval h (k := 56) (by norm_num)).2.2
  have v4096 : σ (.n 4096) = ev 4 := by
    rw [← hev 4 (by norm_num)]; exact (vt_eval h (k := 57) (by norm_num)).2.2
  have v4199 : σ (.n 4199) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_eval h (k := 64) (by norm_num)).2.2
  have hB : σ (.n 4283) = vtBlockVal (σ (.n 14)) W ev [[([], 4)], [([0], 1)], [([11], 2)], [([], 16)], [([2], 1)], [([3], 1)], [([4], 1)], [([], 0)], [([], 0)]] := by
    simp only [v4199, v4096, v4085, v4061, v4039, a4081, a4080, a4079, a4078, e4077, a4076, a4075, a4074,
      e4073, a4072, a4071, e4070, a4069, a4068, e4067, a4066, a4065, e4064, a4063, a4062,
      a4061, e4060, a4059, a4058, e4057, a4056, a4055, a4054, a4053, e4052, a4051, a4050,
      e4049]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a4083, a4082, hB]

set_option maxRecDepth 10000 in
theorem vtB04_2 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (53 + c))) = ev c) :
    σ (.n 4311) = σ (.n 4285) + σ (.n 1124) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 2], 1)], [([8], 2)], [([5], 1)], [([], 0)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 4084 [
    .atom (.load (.n 4286) (.n 13) 0),
    .atom (.const (.n 4287) (word 2 0 0)),
    .atom (.mul (.n 4288) (.n 4286) (.n 4287)),
    .atom (.mul (.n 4289) (.n 4050) (.n 4061)),
    .atom (.load (.n 4290) (.n 13) 1),
    .atom (.mul (.n 4291) (.n 4290) (.n 4289)),
    .atom (.add (.n 4292) (.n 4288) (.n 4291)),
    .atom (.const (.n 4293) (word 2 0 0)),
    .atom (.mul (.n 4294) (.n 4293) (.n 4153)),
    .atom (.load (.n 4295) (.n 13) 2),
    .atom (.mul (.n 4296) (.n 4295) (.n 4294)),
    .atom (.add (.n 4297) (.n 4292) (.n 4296)),
    .atom (.load (.n 4298) (.n 13) 3),
    .atom (.mul (.n 4299) (.n 4298) (.n 4107)),
    .atom (.add (.n 4300) (.n 4297) (.n 4299)),
    .atom (.load (.n 4301) (.n 13) 4),
    .atom (.const (.n 4302) (word 0 0 0)),
    .atom (.mul (.n 4303) (.n 4301) (.n 4302)),
    .atom (.add (.n 4304) (.n 4300) (.n 4303)),
    .atom (.load (.n 4305) (.n 13) 5),
    .atom (.const (.n 4306) (word 0 0 0)),
    .atom (.mul (.n 4307) (.n 4305) (.n 4306)),
    .atom (.add (.n 4308) (.n 4304) (.n 4307)),
    .atom (.add (.n 4309) (.n 14) (.n 4308)),
    .atom (.mul (.n 4310) (.n 1124) (.n 4309)),
    .atom (.add (.n 4311) (.n 4285) (.n 4310))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a4084, a4085, a4086, a4087, a4088, a4089, a4090, a4091, a4092, a4093, a4094, a4095, a4096, a4097,
    a4098, a4099, a4100, a4101, a4102, a4103, a4104, a4105, a4106, a4107, a4108, a4109, -⟩ := hs
  have e4084 := tb_loadHolds_unique a4084 (hw 0 (by norm_num))
  have e4088 := tb_loadHolds_unique a4088 (hw 1 (by norm_num))
  have e4093 := tb_loadHolds_unique a4093 (hw 2 (by norm_num))
  have e4096 := tb_loadHolds_unique a4096 (hw 3 (by norm_num))
  have e4099 := tb_loadHolds_unique a4099 (hw 4 (by norm_num))
  have e4103 := tb_loadHolds_unique a4103 (hw 5 (by norm_num))
  have v4050 : σ (.n 4050) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 54) (by norm_num)).2.2
  have v4061 : σ (.n 4061) = ev 2 := by
    rw [← hev 2 (by norm_num)]; exact (vt_eval h (k := 55) (by norm_num)).2.2
  have v4107 : σ (.n 4107) = ev 5 := by
    rw [← hev 5 (by norm_num)]; exact (vt_eval h (k := 58) (by norm_num)).2.2
  have v4153 : σ (.n 4153) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_eval h (k := 61) (by norm_num)).2.2
  have hB : σ (.n 4309) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 2], 1)], [([8], 2)], [([5], 1)], [([], 0)], [([], 0)]] := by
    simp only [v4153, v4107, v4061, v4050, a4107, a4106, a4105, a4104, e4103, a4102, a4101, a4100, e4099,
      a4098, a4097, e4096, a4095, a4094, e4093, a4092, a4091, a4090, a4089, e4088, a4087,
      a4086, a4085, e4084]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a4109, a4108, hB]

set_option maxRecDepth 10000 in
theorem vtB04_3 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (53 + c))) = ev c) :
    σ (.n 4337) = σ (.n 4311) + σ (.n 1133) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 3], 1)], [([9], 2)], [([6], 1)], [([], 0)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 4110 [
    .atom (.load (.n 4312) (.n 13) 0),
    .atom (.const (.n 4313) (word 2 0 0)),
    .atom (.mul (.n 4314) (.n 4312) (.n 4313)),
    .atom (.mul (.n 4315) (.n 4050) (.n 4085)),
    .atom (.load (.n 4316) (.n 13) 1),
    .atom (.mul (.n 4317) (.n 4316) (.n 4315)),
    .atom (.add (.n 4318) (.n 4314) (.n 4317)),
    .atom (.const (.n 4319) (word 2 0 0)),
    .atom (.mul (.n 4320) (.n 4319) (.n 4164)),
    .atom (.load (.n 4321) (.n 13) 2),
    .atom (.mul (.n 4322) (.n 4321) (.n 4320)),
    .atom (.add (.n 4323) (.n 4318) (.n 4322)),
    .atom (.load (.n 4324) (.n 13) 3),
    .atom (.mul (.n 4325) (.n 4324) (.n 4118)),
    .atom (.add (.n 4326) (.n 4323) (.n 4325)),
    .atom (.load (.n 4327) (.n 13) 4),
    .atom (.const (.n 4328) (word 0 0 0)),
    .atom (.mul (.n 4329) (.n 4327) (.n 4328)),
    .atom (.add (.n 4330) (.n 4326) (.n 4329)),
    .atom (.load (.n 4331) (.n 13) 5),
    .atom (.const (.n 4332) (word 0 0 0)),
    .atom (.mul (.n 4333) (.n 4331) (.n 4332)),
    .atom (.add (.n 4334) (.n 4330) (.n 4333)),
    .atom (.add (.n 4335) (.n 14) (.n 4334)),
    .atom (.mul (.n 4336) (.n 1133) (.n 4335)),
    .atom (.add (.n 4337) (.n 4311) (.n 4336))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a4110, a4111, a4112, a4113, a4114, a4115, a4116, a4117, a4118, a4119, a4120, a4121, a4122, a4123,
    a4124, a4125, a4126, a4127, a4128, a4129, a4130, a4131, a4132, a4133, a4134, a4135, -⟩ := hs
  have e4110 := tb_loadHolds_unique a4110 (hw 0 (by norm_num))
  have e4114 := tb_loadHolds_unique a4114 (hw 1 (by norm_num))
  have e4119 := tb_loadHolds_unique a4119 (hw 2 (by norm_num))
  have e4122 := tb_loadHolds_unique a4122 (hw 3 (by norm_num))
  have e4125 := tb_loadHolds_unique a4125 (hw 4 (by norm_num))
  have e4129 := tb_loadHolds_unique a4129 (hw 5 (by norm_num))
  have v4050 : σ (.n 4050) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 54) (by norm_num)).2.2
  have v4085 : σ (.n 4085) = ev 3 := by
    rw [← hev 3 (by norm_num)]; exact (vt_eval h (k := 56) (by norm_num)).2.2
  have v4118 : σ (.n 4118) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_eval h (k := 59) (by norm_num)).2.2
  have v4164 : σ (.n 4164) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 62) (by norm_num)).2.2
  have hB : σ (.n 4335) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 3], 1)], [([9], 2)], [([6], 1)], [([], 0)], [([], 0)]] := by
    simp only [v4164, v4118, v4085, v4050, a4133, a4132, a4131, a4130, e4129, a4128, a4127, a4126, e4125,
      a4124, a4123, e4122, a4121, a4120, e4119, a4118, a4117, a4116, a4115, e4114, a4113,
      a4112, a4111, e4110]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a4135, a4134, hB]

set_option maxRecDepth 10000 in
theorem vtB04_4 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (53 + c))) = ev c) :
    σ (.n 4363) = σ (.n 4337) + σ (.n 1142) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 4], 1)], [([10], 2)], [([7], 1)], [([], 0)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 4136 [
    .atom (.load (.n 4338) (.n 13) 0),
    .atom (.const (.n 4339) (word 2 0 0)),
    .atom (.mul (.n 4340) (.n 4338) (.n 4339)),
    .atom (.mul (.n 4341) (.n 4050) (.n 4096)),
    .atom (.load (.n 4342) (.n 13) 1),
    .atom (.mul (.n 4343) (.n 4342) (.n 4341)),
    .atom (.add (.n 4344) (.n 4340) (.n 4343)),
    .atom (.const (.n 4345) (word 2 0 0)),
    .atom (.mul (.n 4346) (.n 4345) (.n 4175)),
    .atom (.load (.n 4347) (.n 13) 2),
    .atom (.mul (.n 4348) (.n 4347) (.n 4346)),
    .atom (.add (.n 4349) (.n 4344) (.n 4348)),
    .atom (.load (.n 4350) (.n 13) 3),
    .atom (.mul (.n 4351) (.n 4350) (.n 4142)),
    .atom (.add (.n 4352) (.n 4349) (.n 4351)),
    .atom (.load (.n 4353) (.n 13) 4),
    .atom (.const (.n 4354) (word 0 0 0)),
    .atom (.mul (.n 4355) (.n 4353) (.n 4354)),
    .atom (.add (.n 4356) (.n 4352) (.n 4355)),
    .atom (.load (.n 4357) (.n 13) 5),
    .atom (.const (.n 4358) (word 0 0 0)),
    .atom (.mul (.n 4359) (.n 4357) (.n 4358)),
    .atom (.add (.n 4360) (.n 4356) (.n 4359)),
    .atom (.add (.n 4361) (.n 14) (.n 4360)),
    .atom (.mul (.n 4362) (.n 1142) (.n 4361)),
    .atom (.add (.n 4363) (.n 4337) (.n 4362))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a4136, a4137, a4138, a4139, a4140, a4141, a4142, a4143, a4144, a4145, a4146, a4147, a4148, a4149,
    a4150, a4151, a4152, a4153, a4154, a4155, a4156, a4157, a4158, a4159, a4160, a4161, -⟩ := hs
  have e4136 := tb_loadHolds_unique a4136 (hw 0 (by norm_num))
  have e4140 := tb_loadHolds_unique a4140 (hw 1 (by norm_num))
  have e4145 := tb_loadHolds_unique a4145 (hw 2 (by norm_num))
  have e4148 := tb_loadHolds_unique a4148 (hw 3 (by norm_num))
  have e4151 := tb_loadHolds_unique a4151 (hw 4 (by norm_num))
  have e4155 := tb_loadHolds_unique a4155 (hw 5 (by norm_num))
  have v4050 : σ (.n 4050) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 54) (by norm_num)).2.2
  have v4096 : σ (.n 4096) = ev 4 := by
    rw [← hev 4 (by norm_num)]; exact (vt_eval h (k := 57) (by norm_num)).2.2
  have v4142 : σ (.n 4142) = ev 7 := by
    rw [← hev 7 (by norm_num)]; exact (vt_eval h (k := 60) (by norm_num)).2.2
  have v4175 : σ (.n 4175) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_eval h (k := 63) (by norm_num)).2.2
  have hB : σ (.n 4361) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 4], 1)], [([10], 2)], [([7], 1)], [([], 0)], [([], 0)]] := by
    simp only [v4175, v4142, v4096, v4050, a4159, a4158, a4157, a4156, e4155, a4154, a4153, a4152, e4151,
      a4150, a4149, e4148, a4147, a4146, e4145, a4144, a4143, a4142, a4141, e4140, a4139,
      a4138, a4137, e4136]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a4161, a4160, hB]

set_option maxRecDepth 10000 in
theorem vtSide04 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (53 + c))) = ev c) :
    σ (.n 4363) =
      vtSideVal [σ (.n 1106), σ (.n 1115), σ (.n 1124), σ (.n 1133), σ (.n 1142)]
        (σ (.n 14)) W ev vtBTerms04 := by
  rw [vtB04_4 h hw hev, vtB04_3 h hw hev, vtB04_2 h hw hev, vtB04_1 h hw hev, vtB04_0 h hw hev]
  simp only [vtSideVal, vtBTerms04, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, add_zero, add_assoc]

set_option maxRecDepth 10000 in
theorem vtD4_0 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (53 + c))) = ev c) :
    σ (.n 4382) = σ (.n 2004) * vtSlots W ev 0
      [[], [([0], 3), ([0, 13], 2), ([6, 13], 1)], [([1, 13], 1), ([7, 13], 1)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 4164 [
    .atom (.const (.n 4366) (word 3 0 0)),
    .atom (.mul (.n 4367) (.n 4366) (.n 4039)),
    .atom (.const (.n 4368) (word 2 0 0)),
    .atom (.mul (.n 4369) (.n 4039) (.n 4221)),
    .atom (.mul (.n 4370) (.n 4368) (.n 4369)),
    .atom (.add (.n 4371) (.n 4367) (.n 4370)),
    .atom (.mul (.n 4372) (.n 4118) (.n 4221)),
    .atom (.add (.n 4373) (.n 4371) (.n 4372)),
    .atom (.load (.n 4374) (.n 13) 1),
    .atom (.mul (.n 4375) (.n 4374) (.n 4373)),
    .atom (.mul (.n 4376) (.n 4050) (.n 4221)),
    .atom (.mul (.n 4377) (.n 4142) (.n 4221)),
    .atom (.add (.n 4378) (.n 4376) (.n 4377)),
    .atom (.load (.n 4379) (.n 13) 2),
    .atom (.mul (.n 4380) (.n 4379) (.n 4378)),
    .atom (.add (.n 4381) (.n 4375) (.n 4380)),
    .atom (.mul (.n 4382) (.n 2004) (.n 4381))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a4164, a4165, a4166, a4167, a4168, a4169, a4170, a4171, a4172, a4173, a4174, a4175, a4176, a4177,
    a4178, a4179, a4180, -⟩ := hs
  have e4172 := tb_loadHolds_unique a4172 (hw 1 (by norm_num))
  have e4177 := tb_loadHolds_unique a4177 (hw 2 (by norm_num))
  have v4039 : σ (.n 4039) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_eval h (k := 53) (by norm_num)).2.2
  have v4050 : σ (.n 4050) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 54) (by norm_num)).2.2
  have v4118 : σ (.n 4118) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_eval h (k := 59) (by norm_num)).2.2
  have v4142 : σ (.n 4142) = ev 7 := by
    rw [← hev 7 (by norm_num)]; exact (vt_eval h (k := 60) (by norm_num)).2.2
  have v4221 : σ (.n 4221) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 66) (by norm_num)).2.2
  have hB : σ (.n 4381) = vtSlots W ev 0 [[], [([0], 3), ([0, 13], 2), ([6, 13], 1)], [([1, 13], 1), ([7, 13], 1)]] := by
    simp only [v4221, v4142, v4118, v4050, v4039, a4179, a4178, e4177, a4176, a4175, a4174, a4173, e4172,
      a4171, a4170, a4169, a4168, a4167, a4166, a4165, a4164]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a4180, hB]

set_option maxRecDepth 10000 in
theorem vtD4_1 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (53 + c))) = ev c) :
    σ (.n 4388) = σ (.n 4382) + σ (.n 2006) * vtSlots W ev 0
      [[], [], [([11], 3)], [], [], [], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 4181 [
    .atom (.const (.n 4383) (word 3 0 0)),
    .atom (.mul (.n 4384) (.n 4383) (.n 4199)),
    .atom (.load (.n 4385) (.n 13) 2),
    .atom (.mul (.n 4386) (.n 4385) (.n 4384)),
    .atom (.mul (.n 4387) (.n 2006) (.n 4386)),
    .atom (.add (.n 4388) (.n 4382) (.n 4387))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a4181, a4182, a4183, a4184, a4185, a4186, -⟩ := hs
  have e4183 := tb_loadHolds_unique a4183 (hw 2 (by norm_num))
  have v4199 : σ (.n 4199) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_eval h (k := 64) (by norm_num)).2.2
  have hB : σ (.n 4386) = vtSlots W ev 0 [[], [], [([11], 3)], [], [], [], [], [], []] := by
    simp only [v4199, a4184, e4183, a4182, a4181]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a4186, a4185, hB]

set_option maxRecDepth 10000 in
theorem vtD4_2 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (53 + c))) = ev c) :
    σ (.n 4394) = σ (.n 4388) + σ (.n 2008) * vtSlots W ev 0
      [[], [], [([8], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 4187 [
    .atom (.const (.n 4389) (word 3 0 0)),
    .atom (.mul (.n 4390) (.n 4389) (.n 4153)),
    .atom (.load (.n 4391) (.n 13) 2),
    .atom (.mul (.n 4392) (.n 4391) (.n 4390)),
    .atom (.mul (.n 4393) (.n 2008) (.n 4392)),
    .atom (.add (.n 4394) (.n 4388) (.n 4393))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a4187, a4188, a4189, a4190, a4191, a4192, -⟩ := hs
  have e4189 := tb_loadHolds_unique a4189 (hw 2 (by norm_num))
  have v4153 : σ (.n 4153) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_eval h (k := 61) (by norm_num)).2.2
  have hB : σ (.n 4392) = vtSlots W ev 0 [[], [], [([8], 3)], [], [], []] := by
    simp only [v4153, a4190, e4189, a4188, a4187]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a4192, a4191, hB]

set_option maxRecDepth 10000 in
theorem vtD4_3 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (53 + c))) = ev c) :
    σ (.n 4400) = σ (.n 4394) + σ (.n 2010) * vtSlots W ev 0
      [[], [], [([9], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 4193 [
    .atom (.const (.n 4395) (word 3 0 0)),
    .atom (.mul (.n 4396) (.n 4395) (.n 4164)),
    .atom (.load (.n 4397) (.n 13) 2),
    .atom (.mul (.n 4398) (.n 4397) (.n 4396)),
    .atom (.mul (.n 4399) (.n 2010) (.n 4398)),
    .atom (.add (.n 4400) (.n 4394) (.n 4399))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a4193, a4194, a4195, a4196, a4197, a4198, -⟩ := hs
  have e4195 := tb_loadHolds_unique a4195 (hw 2 (by norm_num))
  have v4164 : σ (.n 4164) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 62) (by norm_num)).2.2
  have hB : σ (.n 4398) = vtSlots W ev 0 [[], [], [([9], 3)], [], [], []] := by
    simp only [v4164, a4196, e4195, a4194, a4193]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a4198, a4197, hB]

set_option maxRecDepth 10000 in
theorem vtD4_4 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (53 + c))) = ev c) :
    σ (.n 4406) = σ (.n 4400) + σ (.n 2012) * vtSlots W ev 0
      [[], [], [([10], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 4199 [
    .atom (.const (.n 4401) (word 3 0 0)),
    .atom (.mul (.n 4402) (.n 4401) (.n 4175)),
    .atom (.load (.n 4403) (.n 13) 2),
    .atom (.mul (.n 4404) (.n 4403) (.n 4402)),
    .atom (.mul (.n 4405) (.n 2012) (.n 4404)),
    .atom (.add (.n 4406) (.n 4400) (.n 4405))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a4199, a4200, a4201, a4202, a4203, a4204, -⟩ := hs
  have e4201 := tb_loadHolds_unique a4201 (hw 2 (by norm_num))
  have v4175 : σ (.n 4175) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_eval h (k := 63) (by norm_num)).2.2
  have hB : σ (.n 4404) = vtSlots W ev 0 [[], [], [([10], 3)], [], [], []] := by
    simp only [v4175, a4202, e4201, a4200, a4199]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a4204, a4203, hB]

set_option maxRecDepth 10000 in
theorem vtSide14 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 14, σ (.n (vtEvB (53 + c))) = ev c) :
    σ (.n 4407) =
      vtSideVal [σ (.n 2004), σ (.n 2006), σ (.n 2008), σ (.n 2010), σ (.n 2012)]
        (σ (.n 14)) W ev vtBTerms14 := by
  have hF0 : σ (.n 4363) =
      vtSideVal [σ (.n 2004), σ (.n 2006), σ (.n 2008), σ (.n 2010), σ (.n 2012)]
        (σ (.n 14)) W ev vtBTerms04 := by
    rw [vtPullSels4 h]; exact vtSide04 h hw hev
  have a4205 := h.atomAt 4205 (.add (.n 4407) (.n 4363) (.n 4406)) (by decide +kernel)
  simp only [Atom.Holds] at a4205
  rw [vtSideVal_pull _ _ _ _ _ _ _ vtPull4, ← hF0, a4205, vtD4_4 h hw hev, vtD4_3 h hw hev, vtD4_2 h hw hev, vtD4_1 h hw hev, vtD4_0 h hw hev]
  simp only [vtDiffSum, vtDTerms4, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, add_zero, add_assoc]

set_option maxRecDepth 10000 in
theorem vtSide24 {rd : Reader} {σ : Val} (h : VtH rd σ) {ev : ℕ → E}
    (hev : ∀ c < 14, σ (.n (vtEvB (53 + c))) = ev c) :
    σ (.n 4416) =
      vtSideVal [σ (.n 2191), σ (.n 2200), σ (.n 2209), σ (.n 2218)]
        (0) (fun _ ↦ 1) ev vtBTerms24 := by
  obtain ⟨_, hs⟩ := h.sliceAt 4208 [
    .atom (.mul (.n 4410) (.n 2191) (.n 4153)),
    .atom (.mul (.n 4411) (.n 2200) (.n 4164)),
    .atom (.add (.n 4412) (.n 4410) (.n 4411)),
    .atom (.mul (.n 4413) (.n 2209) (.n 4175)),
    .atom (.add (.n 4414) (.n 4412) (.n 4413)),
    .atom (.mul (.n 4415) (.n 2218) (.n 4199)),
    .atom (.add (.n 4416) (.n 4414) (.n 4415))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a4208, a4209, a4210, a4211, a4212, a4213, a4214, -⟩ := hs
  have v4153 : σ (.n 4153) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_eval h (k := 61) (by norm_num)).2.2
  have v4164 : σ (.n 4164) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 62) (by norm_num)).2.2
  have v4175 : σ (.n 4175) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_eval h (k := 63) (by norm_num)).2.2
  have v4199 : σ (.n 4199) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_eval h (k := 64) (by norm_num)).2.2
  rw [a4214, a4212, a4210, a4208, a4209, a4211, a4213, v4153, v4164, v4175, v4199]
  simp only [vtSideVal, vtBTerms24, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, vt_ofK_ofBits_one, zero_add,
    one_mul, mul_one, add_zero, add_assoc]

end
end LeanVM.Guest.B1.Tables
