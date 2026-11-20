/-
  LeanVM.Guest.B1.Tables.VtC.FForms2

  `Vt/FormsT2.lean` on the window `VtF` (generated: scripts/b1c-vt/gentwins.py).

  Do not edit: `scripts/b1c-vt/all.py` writes it (`regen-guest.sh`, step `vt`).
-/

module

public import LeanVM.Guest.B1.Tables.VtC.FEvals
public import LeanVM.Guest.B1.Tables.Vt.FormsT2

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

set_option maxRecDepth 10000 in
theorem vtB02_0F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 7, σ (.n (vtEvB (26 + c))) = ev c) :
    σ (.n 3323) = σ (.n 932) * vtBlockVal (σ (.n 14)) W ev
      [[([], 1)], [([0], 2)], [([1], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 3214 [
    .atom (.const (.n 3279) (word 1 0)),
    .atom (.const (.n 3280) (word 2 0)),
    .atom (.mul (.n 3281) (.n 3280) (.n 3228)),
    .atom (.copy (.n 3282) (.n 3281)),
    .atom (.copy (.n 3283) (.n 3232))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a3214, a3215, a3216, a3217, a3218, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 3249 [
    .atom (.load (.n 3314) (.n 13) 0),
    .atom (.mul (.n 3315) (.n 3314) (.n 3279)),
    .atom (.load (.n 3316) (.n 13) 1),
    .atom (.mul (.n 3317) (.n 3316) (.n 3282)),
    .atom (.add (.n 3318) (.n 3315) (.n 3317)),
    .atom (.load (.n 3319) (.n 13) 2),
    .atom (.mul (.n 3320) (.n 3319) (.n 3283)),
    .atom (.add (.n 3321) (.n 3318) (.n 3320)),
    .atom (.add (.n 3322) (.n 14) (.n 3321)),
    .atom (.mul (.n 3323) (.n 932) (.n 3322))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a3249, a3250, a3251, a3252, a3253, a3254, a3255, a3256, a3257, a3258, -⟩ := hs1
  have e3249 := tb_loadHolds_unique a3249 (hw 0 (by norm_num))
  have e3251 := tb_loadHolds_unique a3251 (hw 1 (by norm_num))
  have e3254 := tb_loadHolds_unique a3254 (hw 2 (by norm_num))
  have v3228 : σ (.n 3228) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_evalF h (k := 26) (by norm_num)).2.2
  have v3232 : σ (.n 3232) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 27) (by norm_num)).2.2
  have hB : σ (.n 3322) = vtBlockVal (σ (.n 14)) W ev [[([], 1)], [([0], 2)], [([1], 1)]] := by
    simp only [v3232, v3228, a3257, a3256, a3255, e3254, a3253, a3252, e3251, a3250, e3249, a3218, a3217,
      a3216, a3215, a3214]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a3258, hB]

set_option maxRecDepth 10000 in
theorem vtB02_1F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 7, σ (.n (vtEvB (26 + c))) = ev c) :
    σ (.n 3352) = σ (.n 3323) + σ (.n 941) * vtBlockVal (σ (.n 14)) W ev
      [[([], 4)], [([0], 1)], [([6], 2)], [([], 4)], [([2], 1)], [([3], 1)], [([4], 1)], [([], 0)], [([], 0)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 3219 [
    .atom (.const (.n 3284) (word 4 0)),
    .atom (.copy (.n 3285) (.n 3228)),
    .atom (.const (.n 3286) (word 2 0)),
    .atom (.mul (.n 3287) (.n 3286) (.n 3278)),
    .atom (.copy (.n 3288) (.n 3287)),
    .atom (.const (.n 3289) (word 4 0)),
    .atom (.copy (.n 3290) (.n 3249)),
    .atom (.copy (.n 3291) (.n 3253)),
    .atom (.copy (.n 3292) (.n 3257)),
    .atom (.const (.n 3293) (word 0 0)),
    .atom (.const (.n 3294) (word 0 0))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a3219, a3220, a3221, a3222, a3223, a3224, a3225, a3226, a3227, a3228, a3229, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 3259 [
    .atom (.load (.n 3324) (.n 13) 0),
    .atom (.mul (.n 3325) (.n 3324) (.n 3284)),
    .atom (.load (.n 3326) (.n 13) 1),
    .atom (.mul (.n 3327) (.n 3326) (.n 3285)),
    .atom (.add (.n 3328) (.n 3325) (.n 3327)),
    .atom (.load (.n 3329) (.n 13) 2),
    .atom (.mul (.n 3330) (.n 3329) (.n 3288)),
    .atom (.add (.n 3331) (.n 3328) (.n 3330)),
    .atom (.load (.n 3332) (.n 13) 3),
    .atom (.mul (.n 3333) (.n 3332) (.n 3289)),
    .atom (.add (.n 3334) (.n 3331) (.n 3333)),
    .atom (.load (.n 3335) (.n 13) 4),
    .atom (.mul (.n 3336) (.n 3335) (.n 3290)),
    .atom (.add (.n 3337) (.n 3334) (.n 3336)),
    .atom (.load (.n 3338) (.n 13) 5),
    .atom (.mul (.n 3339) (.n 3338) (.n 3291)),
    .atom (.add (.n 3340) (.n 3337) (.n 3339)),
    .atom (.load (.n 3341) (.n 13) 6),
    .atom (.mul (.n 3342) (.n 3341) (.n 3292)),
    .atom (.add (.n 3343) (.n 3340) (.n 3342)),
    .atom (.load (.n 3344) (.n 13) 7),
    .atom (.mul (.n 3345) (.n 3344) (.n 3293)),
    .atom (.add (.n 3346) (.n 3343) (.n 3345)),
    .atom (.load (.n 3347) (.n 13) 8),
    .atom (.mul (.n 3348) (.n 3347) (.n 3294)),
    .atom (.add (.n 3349) (.n 3346) (.n 3348)),
    .atom (.add (.n 3350) (.n 14) (.n 3349)),
    .atom (.mul (.n 3351) (.n 941) (.n 3350)),
    .atom (.add (.n 3352) (.n 3323) (.n 3351))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a3259, a3260, a3261, a3262, a3263, a3264, a3265, a3266, a3267, a3268, a3269, a3270, a3271, a3272,
    a3273, a3274, a3275, a3276, a3277, a3278, a3279, a3280, a3281, a3282, a3283, a3284, a3285,
    a3286, a3287, -⟩ := hs1
  have e3259 := tb_loadHolds_unique a3259 (hw 0 (by norm_num))
  have e3261 := tb_loadHolds_unique a3261 (hw 1 (by norm_num))
  have e3264 := tb_loadHolds_unique a3264 (hw 2 (by norm_num))
  have e3267 := tb_loadHolds_unique a3267 (hw 3 (by norm_num))
  have e3270 := tb_loadHolds_unique a3270 (hw 4 (by norm_num))
  have e3273 := tb_loadHolds_unique a3273 (hw 5 (by norm_num))
  have e3276 := tb_loadHolds_unique a3276 (hw 6 (by norm_num))
  have e3279 := tb_loadHolds_unique a3279 (hw 7 (by norm_num))
  have e3282 := tb_loadHolds_unique a3282 (hw 8 (by norm_num))
  have v3228 : σ (.n 3228) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_evalF h (k := 26) (by norm_num)).2.2
  have v3249 : σ (.n 3249) = ev 2 := by
    rw [← hev 2 (by norm_num)]; exact (vt_evalF h (k := 28) (by norm_num)).2.2
  have v3253 : σ (.n 3253) = ev 3 := by
    rw [← hev 3 (by norm_num)]; exact (vt_evalF h (k := 29) (by norm_num)).2.2
  have v3257 : σ (.n 3257) = ev 4 := by
    rw [← hev 4 (by norm_num)]; exact (vt_evalF h (k := 30) (by norm_num)).2.2
  have v3278 : σ (.n 3278) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_evalF h (k := 32) (by norm_num)).2.2
  have hB : σ (.n 3350) = vtBlockVal (σ (.n 14)) W ev [[([], 4)], [([0], 1)], [([6], 2)], [([], 4)], [([2], 1)], [([3], 1)], [([4], 1)], [([], 0)], [([], 0)]] := by
    simp only [v3278, v3257, v3253, v3249, v3228, a3285, a3284, a3283, e3282, a3281, a3280, e3279, a3278,
      a3277, e3276, a3275, a3274, e3273, a3272, a3271, e3270, a3269, a3268, e3267, a3266,
      a3265, e3264, a3263, a3262, e3261, a3260, e3259, a3229, a3228, a3227, a3226, a3225,
      a3224, a3223, a3222, a3221, a3220, a3219]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a3287, a3286, hB]

set_option maxRecDepth 10000 in
theorem vtB02_2F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 7, σ (.n (vtEvB (26 + c))) = ev c) :
    σ (.n 3369) = σ (.n 3352) + σ (.n 950) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 2], 1)], [([5], 2)], [([3], 1)], [([4], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 3230 [
    .atom (.const (.n 3295) (word 2 0)),
    .atom (.mul (.n 3296) (.n 3232) (.n 3249)),
    .atom (.copy (.n 3297) (.n 3296)),
    .atom (.const (.n 3298) (word 2 0)),
    .atom (.mul (.n 3299) (.n 3298) (.n 3261)),
    .atom (.copy (.n 3300) (.n 3299)),
    .atom (.copy (.n 3301) (.n 3253)),
    .atom (.copy (.n 3302) (.n 3257))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a3230, a3231, a3232, a3233, a3234, a3235, a3236, a3237, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 3288 [
    .atom (.load (.n 3353) (.n 13) 0),
    .atom (.mul (.n 3354) (.n 3353) (.n 3295)),
    .atom (.load (.n 3355) (.n 13) 1),
    .atom (.mul (.n 3356) (.n 3355) (.n 3297)),
    .atom (.add (.n 3357) (.n 3354) (.n 3356)),
    .atom (.load (.n 3358) (.n 13) 2),
    .atom (.mul (.n 3359) (.n 3358) (.n 3300)),
    .atom (.add (.n 3360) (.n 3357) (.n 3359)),
    .atom (.load (.n 3361) (.n 13) 3),
    .atom (.mul (.n 3362) (.n 3361) (.n 3301)),
    .atom (.add (.n 3363) (.n 3360) (.n 3362)),
    .atom (.load (.n 3364) (.n 13) 4),
    .atom (.mul (.n 3365) (.n 3364) (.n 3302)),
    .atom (.add (.n 3366) (.n 3363) (.n 3365)),
    .atom (.add (.n 3367) (.n 14) (.n 3366)),
    .atom (.mul (.n 3368) (.n 950) (.n 3367)),
    .atom (.add (.n 3369) (.n 3352) (.n 3368))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a3288, a3289, a3290, a3291, a3292, a3293, a3294, a3295, a3296, a3297, a3298, a3299, a3300, a3301,
    a3302, a3303, a3304, -⟩ := hs1
  have e3288 := tb_loadHolds_unique a3288 (hw 0 (by norm_num))
  have e3290 := tb_loadHolds_unique a3290 (hw 1 (by norm_num))
  have e3293 := tb_loadHolds_unique a3293 (hw 2 (by norm_num))
  have e3296 := tb_loadHolds_unique a3296 (hw 3 (by norm_num))
  have e3299 := tb_loadHolds_unique a3299 (hw 4 (by norm_num))
  have v3232 : σ (.n 3232) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 27) (by norm_num)).2.2
  have v3249 : σ (.n 3249) = ev 2 := by
    rw [← hev 2 (by norm_num)]; exact (vt_evalF h (k := 28) (by norm_num)).2.2
  have v3253 : σ (.n 3253) = ev 3 := by
    rw [← hev 3 (by norm_num)]; exact (vt_evalF h (k := 29) (by norm_num)).2.2
  have v3257 : σ (.n 3257) = ev 4 := by
    rw [← hev 4 (by norm_num)]; exact (vt_evalF h (k := 30) (by norm_num)).2.2
  have v3261 : σ (.n 3261) = ev 5 := by
    rw [← hev 5 (by norm_num)]; exact (vt_evalF h (k := 31) (by norm_num)).2.2
  have hB : σ (.n 3367) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 2], 1)], [([5], 2)], [([3], 1)], [([4], 1)]] := by
    simp only [v3261, v3257, v3253, v3249, v3232, a3302, a3301, a3300, e3299, a3298, a3297, e3296, a3295,
      a3294, e3293, a3292, a3291, e3290, a3289, e3288, a3237, a3236, a3235, a3234, a3233,
      a3232, a3231, a3230]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a3304, a3303, hB]

set_option maxRecDepth 10000 in
theorem vtSide02F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 7, σ (.n (vtEvB (26 + c))) = ev c) :
    σ (.n 3369) =
      vtSideVal [σ (.n 932), σ (.n 941), σ (.n 950)]
        (σ (.n 14)) W ev vtBTerms02 := by
  rw [vtB02_2F h hw hev, vtB02_1F h hw hev, vtB02_0F h hw hev]
  simp only [vtSideVal, vtBTerms02, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, add_zero, add_assoc]

set_option maxRecDepth 10000 in
theorem vtD2_0F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 7, σ (.n (vtEvB (26 + c))) = ev c) :
    σ (.n 3373) = σ (.n 1355) * vtSlots W ev 0
      [[], [([0], 3)], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 3238 [
    .atom (.const (.n 3303) (word 3 0)),
    .atom (.mul (.n 3304) (.n 3303) (.n 3228)),
    .atom (.copy (.n 3305) (.n 3304))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a3238, a3239, a3240, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 3306 [
    .atom (.load (.n 3371) (.n 13) 1),
    .atom (.mul (.n 3372) (.n 3371) (.n 3305)),
    .atom (.mul (.n 3373) (.n 1355) (.n 3372))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a3306, a3307, a3308, -⟩ := hs1
  have e3306 := tb_loadHolds_unique a3306 (hw 1 (by norm_num))
  have v3228 : σ (.n 3228) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_evalF h (k := 26) (by norm_num)).2.2
  have hB : σ (.n 3372) = vtSlots W ev 0 [[], [([0], 3)], []] := by
    simp only [v3228, a3307, e3306, a3240, a3239, a3238]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a3308, hB]

set_option maxRecDepth 10000 in
theorem vtD2_1F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 7, σ (.n (vtEvB (26 + c))) = ev c) :
    σ (.n 3377) = σ (.n 3373) + σ (.n 1357) * vtSlots W ev 0
      [[], [], [([6], 3)], [], [], [], [], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 3241 [
    .atom (.const (.n 3306) (word 3 0)),
    .atom (.mul (.n 3307) (.n 3306) (.n 3278)),
    .atom (.copy (.n 3308) (.n 3307))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a3241, a3242, a3243, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 3309 [
    .atom (.load (.n 3374) (.n 13) 2),
    .atom (.mul (.n 3375) (.n 3374) (.n 3308)),
    .atom (.mul (.n 3376) (.n 1357) (.n 3375)),
    .atom (.add (.n 3377) (.n 3373) (.n 3376))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a3309, a3310, a3311, a3312, -⟩ := hs1
  have e3309 := tb_loadHolds_unique a3309 (hw 2 (by norm_num))
  have v3278 : σ (.n 3278) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_evalF h (k := 32) (by norm_num)).2.2
  have hB : σ (.n 3375) = vtSlots W ev 0 [[], [], [([6], 3)], [], [], [], [], [], []] := by
    simp only [v3278, a3310, e3309, a3243, a3242, a3241]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a3312, a3311, hB]

set_option maxRecDepth 10000 in
theorem vtD2_2F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 7, σ (.n (vtEvB (26 + c))) = ev c) :
    σ (.n 3381) = σ (.n 3377) + σ (.n 1359) * vtSlots W ev 0
      [[], [], [([5], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 3244 [
    .atom (.const (.n 3309) (word 3 0)),
    .atom (.mul (.n 3310) (.n 3309) (.n 3261)),
    .atom (.copy (.n 3311) (.n 3310))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a3244, a3245, a3246, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 3313 [
    .atom (.load (.n 3378) (.n 13) 2),
    .atom (.mul (.n 3379) (.n 3378) (.n 3311)),
    .atom (.mul (.n 3380) (.n 1359) (.n 3379)),
    .atom (.add (.n 3381) (.n 3377) (.n 3380))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a3313, a3314, a3315, a3316, -⟩ := hs1
  have e3313 := tb_loadHolds_unique a3313 (hw 2 (by norm_num))
  have v3261 : σ (.n 3261) = ev 5 := by
    rw [← hev 5 (by norm_num)]; exact (vt_evalF h (k := 31) (by norm_num)).2.2
  have hB : σ (.n 3379) = vtSlots W ev 0 [[], [], [([5], 3)], [], []] := by
    simp only [v3261, a3314, e3313, a3246, a3245, a3244]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a3316, a3315, hB]

set_option maxRecDepth 10000 in
theorem vtSide12F {rd : Reader} {σ : Val} (h : VtF rd σ)
    (hq : [σ (.n 1355), σ (.n 1357), σ (.n 1359)] = [σ (.n 932), σ (.n 941), σ (.n 950)]) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 7, σ (.n (vtEvB (26 + c))) = ev c) :
    σ (.n 3382) =
      vtSideVal [σ (.n 1355), σ (.n 1357), σ (.n 1359)]
        (σ (.n 14)) W ev vtBTerms12 := by
  have hF0 : σ (.n 3369) =
      vtSideVal [σ (.n 1355), σ (.n 1357), σ (.n 1359)]
        (σ (.n 14)) W ev vtBTerms02 := by
    rw [hq]; exact vtSide02F h hw hev
  have a3317 := h.atomAt 3317 (.add (.n 3382) (.n 3369) (.n 3381)) (by decide +kernel)
  simp only [Atom.Holds] at a3317
  rw [vtSideVal_pull _ _ _ _ _ _ _ vtPull2, ← hF0, a3317, vtD2_2F h hw hev, vtD2_1F h hw hev, vtD2_0F h hw hev]
  simp only [vtDiffSum, vtDTerms2, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, add_zero, add_assoc]

set_option maxRecDepth 10000 in
theorem vtSide22F {rd : Reader} {σ : Val} (h : VtF rd σ) {ev : ℕ → E}
    (hev : ∀ c < 7, σ (.n (vtEvB (26 + c))) = ev c) :
    σ (.n 3387) =
      vtSideVal [σ (.n 1501), σ (.n 1510)]
        (0) (fun _ ↦ 1) ev vtBTerms22 := by
  obtain ⟨_, hs0⟩ := h.sliceAt 3247 [
    .atom (.copy (.n 3312) (.n 3261)),
    .atom (.copy (.n 3313) (.n 3278))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a3247, a3248, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 3320 [
    .atom (.mul (.n 3385) (.n 1501) (.n 3312)),
    .atom (.mul (.n 3386) (.n 1510) (.n 3313)),
    .atom (.add (.n 3387) (.n 3385) (.n 3386))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a3320, a3321, a3322, -⟩ := hs1
  have v3261 : σ (.n 3261) = ev 5 := by
    rw [← hev 5 (by norm_num)]; exact (vt_evalF h (k := 31) (by norm_num)).2.2
  have v3278 : σ (.n 3278) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_evalF h (k := 32) (by norm_num)).2.2
  simp only [v3278, v3261, a3322, a3321, a3320, a3248, a3247]
  simp only [vtSideVal, vtBTerms22, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, vt_ofK_ofBits_one]
  ring

end
end LeanVM.Guest.B1.Tables
