/-
  LeanVM.Guest.B1.Tables.Vt.FormsT1

  Table 1's forms on the three sides, from the guest's statements: each block's value from its
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
theorem vtB01_0 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (15 + c))) = ev c) :
    σ (.n 3230) = σ (.n 989) * vtBlockVal (σ (.n 14)) W ev
      [[([], 1)], [([0], 2)], [([1], 1)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 3163 [
    .atom (.load (.n 3220) (.n 13) 0),
    .atom (.const (.n 3221) (word 2 0)),
    .atom (.mul (.n 3222) (.n 3221) (.n 3013)),
    .atom (.load (.n 3223) (.n 13) 1),
    .atom (.mul (.n 3224) (.n 3223) (.n 3222)),
    .atom (.add (.n 3225) (.n 3220) (.n 3224)),
    .atom (.load (.n 3226) (.n 13) 2),
    .atom (.mul (.n 3227) (.n 3226) (.n 3037)),
    .atom (.add (.n 3228) (.n 3225) (.n 3227)),
    .atom (.add (.n 3229) (.n 14) (.n 3228)),
    .atom (.mul (.n 3230) (.n 989) (.n 3229))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a3163, a3164, a3165, a3166, a3167, a3168, a3169, a3170, a3171, a3172, a3173, -⟩ := hs
  have e3163 := tb_loadHolds_unique a3163 (hw 0 (by norm_num))
  have e3166 := tb_loadHolds_unique a3166 (hw 1 (by norm_num))
  have e3169 := tb_loadHolds_unique a3169 (hw 2 (by norm_num))
  have v3013 : σ (.n 3013) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_eval h (k := 15) (by norm_num)).2.2
  have v3037 : σ (.n 3037) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 16) (by norm_num)).2.2
  have hB : σ (.n 3229) = vtBlockVal (σ (.n 14)) W ev [[([], 1)], [([0], 2)], [([1], 1)]] := by
    simp only [v3037, v3013, a3172, a3171, a3170, e3169, a3168, a3167, e3166, a3165, a3164, e3163]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a3173, hB]

set_option maxRecDepth 10000 in
theorem vtB01_1 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (15 + c))) = ev c) :
    σ (.n 3265) = σ (.n 3230) + σ (.n 998) * vtBlockVal (σ (.n 14)) W ev
      [[([], 4)], [([0], 1)], [([14], 2)], [([], 2)], [([2], 1)], [([3], 1)], [([4], 1)], [([], 0)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 3174 [
    .atom (.load (.n 3231) (.n 13) 0),
    .atom (.const (.n 3232) (word 4 0)),
    .atom (.mul (.n 3233) (.n 3231) (.n 3232)),
    .atom (.load (.n 3234) (.n 13) 1),
    .atom (.mul (.n 3235) (.n 3234) (.n 3013)),
    .atom (.add (.n 3236) (.n 3233) (.n 3235)),
    .atom (.const (.n 3237) (word 2 0)),
    .atom (.mul (.n 3238) (.n 3237) (.n 3219)),
    .atom (.load (.n 3239) (.n 13) 2),
    .atom (.mul (.n 3240) (.n 3239) (.n 3238)),
    .atom (.add (.n 3241) (.n 3236) (.n 3240)),
    .atom (.load (.n 3242) (.n 13) 3),
    .atom (.const (.n 3243) (word 2 0)),
    .atom (.mul (.n 3244) (.n 3242) (.n 3243)),
    .atom (.add (.n 3245) (.n 3241) (.n 3244)),
    .atom (.load (.n 3246) (.n 13) 4),
    .atom (.mul (.n 3247) (.n 3246) (.n 3048)),
    .atom (.add (.n 3248) (.n 3245) (.n 3247)),
    .atom (.load (.n 3249) (.n 13) 5),
    .atom (.mul (.n 3250) (.n 3249) (.n 3059)),
    .atom (.add (.n 3251) (.n 3248) (.n 3250)),
    .atom (.load (.n 3252) (.n 13) 6),
    .atom (.mul (.n 3253) (.n 3252) (.n 3070)),
    .atom (.add (.n 3254) (.n 3251) (.n 3253)),
    .atom (.load (.n 3255) (.n 13) 7),
    .atom (.const (.n 3256) (word 0 0)),
    .atom (.mul (.n 3257) (.n 3255) (.n 3256)),
    .atom (.add (.n 3258) (.n 3254) (.n 3257)),
    .atom (.load (.n 3259) (.n 13) 8),
    .atom (.const (.n 3260) (word 0 0)),
    .atom (.mul (.n 3261) (.n 3259) (.n 3260)),
    .atom (.add (.n 3262) (.n 3258) (.n 3261)),
    .atom (.add (.n 3263) (.n 14) (.n 3262)),
    .atom (.mul (.n 3264) (.n 998) (.n 3263)),
    .atom (.add (.n 3265) (.n 3230) (.n 3264))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a3174, a3175, a3176, a3177, a3178, a3179, a3180, a3181, a3182, a3183, a3184, a3185, a3186, a3187,
    a3188, a3189, a3190, a3191, a3192, a3193, a3194, a3195, a3196, a3197, a3198, a3199, a3200,
    a3201, a3202, a3203, a3204, a3205, a3206, a3207, a3208, -⟩ := hs
  have e3174 := tb_loadHolds_unique a3174 (hw 0 (by norm_num))
  have e3177 := tb_loadHolds_unique a3177 (hw 1 (by norm_num))
  have e3182 := tb_loadHolds_unique a3182 (hw 2 (by norm_num))
  have e3185 := tb_loadHolds_unique a3185 (hw 3 (by norm_num))
  have e3189 := tb_loadHolds_unique a3189 (hw 4 (by norm_num))
  have e3192 := tb_loadHolds_unique a3192 (hw 5 (by norm_num))
  have e3195 := tb_loadHolds_unique a3195 (hw 6 (by norm_num))
  have e3198 := tb_loadHolds_unique a3198 (hw 7 (by norm_num))
  have e3202 := tb_loadHolds_unique a3202 (hw 8 (by norm_num))
  have v3013 : σ (.n 3013) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_eval h (k := 15) (by norm_num)).2.2
  have v3048 : σ (.n 3048) = ev 2 := by
    rw [← hev 2 (by norm_num)]; exact (vt_eval h (k := 17) (by norm_num)).2.2
  have v3059 : σ (.n 3059) = ev 3 := by
    rw [← hev 3 (by norm_num)]; exact (vt_eval h (k := 18) (by norm_num)).2.2
  have v3070 : σ (.n 3070) = ev 4 := by
    rw [← hev 4 (by norm_num)]; exact (vt_eval h (k := 19) (by norm_num)).2.2
  have v3219 : σ (.n 3219) = ev 14 := by
    rw [← hev 14 (by norm_num)]; exact (vt_eval h (k := 29) (by norm_num)).2.2
  have hB : σ (.n 3263) = vtBlockVal (σ (.n 14)) W ev [[([], 4)], [([0], 1)], [([14], 2)], [([], 2)], [([2], 1)], [([3], 1)], [([4], 1)], [([], 0)], [([], 0)]] := by
    simp only [v3219, v3070, v3059, v3048, v3013, a3206, a3205, a3204, a3203, e3202, a3201, a3200, a3199,
      e3198, a3197, a3196, e3195, a3194, a3193, e3192, a3191, a3190, e3189, a3188, a3187,
      a3186, e3185, a3184, a3183, e3182, a3181, a3180, a3179, a3178, e3177, a3176, a3175,
      e3174]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a3208, a3207, hB]

set_option maxRecDepth 10000 in
theorem vtB01_2 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (15 + c))) = ev c) :
    σ (.n 3289) = σ (.n 3265) + σ (.n 1007) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 2], 1)], [([11], 2)], [([5], 1)], [([6], 1)], [([7], 1)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 3209 [
    .atom (.load (.n 3266) (.n 13) 0),
    .atom (.const (.n 3267) (word 2 0)),
    .atom (.mul (.n 3268) (.n 3266) (.n 3267)),
    .atom (.mul (.n 3269) (.n 3037) (.n 3048)),
    .atom (.load (.n 3270) (.n 13) 1),
    .atom (.mul (.n 3271) (.n 3270) (.n 3269)),
    .atom (.add (.n 3272) (.n 3268) (.n 3271)),
    .atom (.const (.n 3273) (word 2 0)),
    .atom (.mul (.n 3274) (.n 3273) (.n 3173)),
    .atom (.load (.n 3275) (.n 13) 2),
    .atom (.mul (.n 3276) (.n 3275) (.n 3274)),
    .atom (.add (.n 3277) (.n 3272) (.n 3276)),
    .atom (.load (.n 3278) (.n 13) 3),
    .atom (.mul (.n 3279) (.n 3278) (.n 3094)),
    .atom (.add (.n 3280) (.n 3277) (.n 3279)),
    .atom (.load (.n 3281) (.n 13) 4),
    .atom (.mul (.n 3282) (.n 3281) (.n 3105)),
    .atom (.add (.n 3283) (.n 3280) (.n 3282)),
    .atom (.load (.n 3284) (.n 13) 5),
    .atom (.mul (.n 3285) (.n 3284) (.n 3116)),
    .atom (.add (.n 3286) (.n 3283) (.n 3285)),
    .atom (.add (.n 3287) (.n 14) (.n 3286)),
    .atom (.mul (.n 3288) (.n 1007) (.n 3287)),
    .atom (.add (.n 3289) (.n 3265) (.n 3288))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a3209, a3210, a3211, a3212, a3213, a3214, a3215, a3216, a3217, a3218, a3219, a3220, a3221, a3222,
    a3223, a3224, a3225, a3226, a3227, a3228, a3229, a3230, a3231, a3232, -⟩ := hs
  have e3209 := tb_loadHolds_unique a3209 (hw 0 (by norm_num))
  have e3213 := tb_loadHolds_unique a3213 (hw 1 (by norm_num))
  have e3218 := tb_loadHolds_unique a3218 (hw 2 (by norm_num))
  have e3221 := tb_loadHolds_unique a3221 (hw 3 (by norm_num))
  have e3224 := tb_loadHolds_unique a3224 (hw 4 (by norm_num))
  have e3227 := tb_loadHolds_unique a3227 (hw 5 (by norm_num))
  have v3037 : σ (.n 3037) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 16) (by norm_num)).2.2
  have v3048 : σ (.n 3048) = ev 2 := by
    rw [← hev 2 (by norm_num)]; exact (vt_eval h (k := 17) (by norm_num)).2.2
  have v3094 : σ (.n 3094) = ev 5 := by
    rw [← hev 5 (by norm_num)]; exact (vt_eval h (k := 20) (by norm_num)).2.2
  have v3105 : σ (.n 3105) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_eval h (k := 21) (by norm_num)).2.2
  have v3116 : σ (.n 3116) = ev 7 := by
    rw [← hev 7 (by norm_num)]; exact (vt_eval h (k := 22) (by norm_num)).2.2
  have v3173 : σ (.n 3173) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_eval h (k := 26) (by norm_num)).2.2
  have hB : σ (.n 3287) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 2], 1)], [([11], 2)], [([5], 1)], [([6], 1)], [([7], 1)]] := by
    simp only [v3173, v3116, v3105, v3094, v3048, v3037, a3230, a3229, a3228, e3227, a3226, a3225, e3224,
      a3223, a3222, e3221, a3220, a3219, e3218, a3217, a3216, a3215, a3214, e3213, a3212,
      a3211, a3210, e3209]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a3232, a3231, hB]

set_option maxRecDepth 10000 in
theorem vtB01_3 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (15 + c))) = ev c) :
    σ (.n 3313) = σ (.n 3289) + σ (.n 1016) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 3], 1)], [([12], 2)], [([8], 1)], [([9], 1)], [([10], 1)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 3233 [
    .atom (.load (.n 3290) (.n 13) 0),
    .atom (.const (.n 3291) (word 2 0)),
    .atom (.mul (.n 3292) (.n 3290) (.n 3291)),
    .atom (.mul (.n 3293) (.n 3037) (.n 3059)),
    .atom (.load (.n 3294) (.n 13) 1),
    .atom (.mul (.n 3295) (.n 3294) (.n 3293)),
    .atom (.add (.n 3296) (.n 3292) (.n 3295)),
    .atom (.const (.n 3297) (word 2 0)),
    .atom (.mul (.n 3298) (.n 3297) (.n 3184)),
    .atom (.load (.n 3299) (.n 13) 2),
    .atom (.mul (.n 3300) (.n 3299) (.n 3298)),
    .atom (.add (.n 3301) (.n 3296) (.n 3300)),
    .atom (.load (.n 3302) (.n 13) 3),
    .atom (.mul (.n 3303) (.n 3302) (.n 3127)),
    .atom (.add (.n 3304) (.n 3301) (.n 3303)),
    .atom (.load (.n 3305) (.n 13) 4),
    .atom (.mul (.n 3306) (.n 3305) (.n 3151)),
    .atom (.add (.n 3307) (.n 3304) (.n 3306)),
    .atom (.load (.n 3308) (.n 13) 5),
    .atom (.mul (.n 3309) (.n 3308) (.n 3162)),
    .atom (.add (.n 3310) (.n 3307) (.n 3309)),
    .atom (.add (.n 3311) (.n 14) (.n 3310)),
    .atom (.mul (.n 3312) (.n 1016) (.n 3311)),
    .atom (.add (.n 3313) (.n 3289) (.n 3312))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a3233, a3234, a3235, a3236, a3237, a3238, a3239, a3240, a3241, a3242, a3243, a3244, a3245, a3246,
    a3247, a3248, a3249, a3250, a3251, a3252, a3253, a3254, a3255, a3256, -⟩ := hs
  have e3233 := tb_loadHolds_unique a3233 (hw 0 (by norm_num))
  have e3237 := tb_loadHolds_unique a3237 (hw 1 (by norm_num))
  have e3242 := tb_loadHolds_unique a3242 (hw 2 (by norm_num))
  have e3245 := tb_loadHolds_unique a3245 (hw 3 (by norm_num))
  have e3248 := tb_loadHolds_unique a3248 (hw 4 (by norm_num))
  have e3251 := tb_loadHolds_unique a3251 (hw 5 (by norm_num))
  have v3037 : σ (.n 3037) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 16) (by norm_num)).2.2
  have v3059 : σ (.n 3059) = ev 3 := by
    rw [← hev 3 (by norm_num)]; exact (vt_eval h (k := 18) (by norm_num)).2.2
  have v3127 : σ (.n 3127) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_eval h (k := 23) (by norm_num)).2.2
  have v3151 : σ (.n 3151) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 24) (by norm_num)).2.2
  have v3162 : σ (.n 3162) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_eval h (k := 25) (by norm_num)).2.2
  have v3184 : σ (.n 3184) = ev 12 := by
    rw [← hev 12 (by norm_num)]; exact (vt_eval h (k := 27) (by norm_num)).2.2
  have hB : σ (.n 3311) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 3], 1)], [([12], 2)], [([8], 1)], [([9], 1)], [([10], 1)]] := by
    simp only [v3184, v3162, v3151, v3127, v3059, v3037, a3254, a3253, a3252, e3251, a3250, a3249, e3248,
      a3247, a3246, e3245, a3244, a3243, e3242, a3241, a3240, a3239, a3238, e3237, a3236,
      a3235, a3234, e3233]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a3256, a3255, hB]

set_option maxRecDepth 10000 in
theorem vtB01_4 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (15 + c))) = ev c) :
    σ (.n 3358) = σ (.n 3313) + σ (.n 1025) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 4], 1)], [([13], 2)], [([5, 8], 1), ([6, 10], 1), ([7, 9], 1)], [([5, 9], 1), ([6, 8], 1), ([6, 10], 1), ([7, 9], 1), ([7, 10], 1)], [([5, 10], 1), ([6, 9], 1), ([7, 8], 1), ([7, 10], 1)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 3257 [
    .atom (.load (.n 3314) (.n 13) 0),
    .atom (.const (.n 3315) (word 2 0)),
    .atom (.mul (.n 3316) (.n 3314) (.n 3315)),
    .atom (.mul (.n 3317) (.n 3037) (.n 3070)),
    .atom (.load (.n 3318) (.n 13) 1),
    .atom (.mul (.n 3319) (.n 3318) (.n 3317)),
    .atom (.add (.n 3320) (.n 3316) (.n 3319)),
    .atom (.const (.n 3321) (word 2 0)),
    .atom (.mul (.n 3322) (.n 3321) (.n 3208)),
    .atom (.load (.n 3323) (.n 13) 2),
    .atom (.mul (.n 3324) (.n 3323) (.n 3322)),
    .atom (.add (.n 3325) (.n 3320) (.n 3324)),
    .atom (.mul (.n 3326) (.n 3094) (.n 3127)),
    .atom (.mul (.n 3327) (.n 3105) (.n 3162)),
    .atom (.add (.n 3328) (.n 3326) (.n 3327)),
    .atom (.mul (.n 3329) (.n 3116) (.n 3151)),
    .atom (.add (.n 3330) (.n 3328) (.n 3329)),
    .atom (.load (.n 3331) (.n 13) 3),
    .atom (.mul (.n 3332) (.n 3331) (.n 3330)),
    .atom (.add (.n 3333) (.n 3325) (.n 3332)),
    .atom (.mul (.n 3334) (.n 3094) (.n 3151)),
    .atom (.mul (.n 3335) (.n 3105) (.n 3127)),
    .atom (.add (.n 3336) (.n 3334) (.n 3335)),
    .atom (.mul (.n 3337) (.n 3105) (.n 3162)),
    .atom (.add (.n 3338) (.n 3336) (.n 3337)),
    .atom (.mul (.n 3339) (.n 3116) (.n 3151)),
    .atom (.add (.n 3340) (.n 3338) (.n 3339)),
    .atom (.mul (.n 3341) (.n 3116) (.n 3162)),
    .atom (.add (.n 3342) (.n 3340) (.n 3341)),
    .atom (.load (.n 3343) (.n 13) 4),
    .atom (.mul (.n 3344) (.n 3343) (.n 3342)),
    .atom (.add (.n 3345) (.n 3333) (.n 3344)),
    .atom (.mul (.n 3346) (.n 3094) (.n 3162)),
    .atom (.mul (.n 3347) (.n 3105) (.n 3151)),
    .atom (.add (.n 3348) (.n 3346) (.n 3347)),
    .atom (.mul (.n 3349) (.n 3116) (.n 3127)),
    .atom (.add (.n 3350) (.n 3348) (.n 3349)),
    .atom (.mul (.n 3351) (.n 3116) (.n 3162)),
    .atom (.add (.n 3352) (.n 3350) (.n 3351)),
    .atom (.load (.n 3353) (.n 13) 5),
    .atom (.mul (.n 3354) (.n 3353) (.n 3352)),
    .atom (.add (.n 3355) (.n 3345) (.n 3354)),
    .atom (.add (.n 3356) (.n 14) (.n 3355)),
    .atom (.mul (.n 3357) (.n 1025) (.n 3356)),
    .atom (.add (.n 3358) (.n 3313) (.n 3357))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a3257, a3258, a3259, a3260, a3261, a3262, a3263, a3264, a3265, a3266, a3267, a3268, a3269, a3270,
    a3271, a3272, a3273, a3274, a3275, a3276, a3277, a3278, a3279, a3280, a3281, a3282, a3283,
    a3284, a3285, a3286, a3287, a3288, a3289, a3290, a3291, a3292, a3293, a3294, a3295, a3296,
    a3297, a3298, a3299, a3300, a3301, -⟩ := hs
  have e3257 := tb_loadHolds_unique a3257 (hw 0 (by norm_num))
  have e3261 := tb_loadHolds_unique a3261 (hw 1 (by norm_num))
  have e3266 := tb_loadHolds_unique a3266 (hw 2 (by norm_num))
  have e3274 := tb_loadHolds_unique a3274 (hw 3 (by norm_num))
  have e3286 := tb_loadHolds_unique a3286 (hw 4 (by norm_num))
  have e3296 := tb_loadHolds_unique a3296 (hw 5 (by norm_num))
  have v3037 : σ (.n 3037) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 16) (by norm_num)).2.2
  have v3070 : σ (.n 3070) = ev 4 := by
    rw [← hev 4 (by norm_num)]; exact (vt_eval h (k := 19) (by norm_num)).2.2
  have v3094 : σ (.n 3094) = ev 5 := by
    rw [← hev 5 (by norm_num)]; exact (vt_eval h (k := 20) (by norm_num)).2.2
  have v3105 : σ (.n 3105) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_eval h (k := 21) (by norm_num)).2.2
  have v3116 : σ (.n 3116) = ev 7 := by
    rw [← hev 7 (by norm_num)]; exact (vt_eval h (k := 22) (by norm_num)).2.2
  have v3127 : σ (.n 3127) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_eval h (k := 23) (by norm_num)).2.2
  have v3151 : σ (.n 3151) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 24) (by norm_num)).2.2
  have v3162 : σ (.n 3162) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_eval h (k := 25) (by norm_num)).2.2
  have v3208 : σ (.n 3208) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 28) (by norm_num)).2.2
  have hB : σ (.n 3356) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 4], 1)], [([13], 2)], [([5, 8], 1), ([6, 10], 1), ([7, 9], 1)], [([5, 9], 1), ([6, 8], 1), ([6, 10], 1), ([7, 9], 1), ([7, 10], 1)], [([5, 10], 1), ([6, 9], 1), ([7, 8], 1), ([7, 10], 1)]] := by
    simp only [v3208, v3162, v3151, v3127, v3116, v3105, v3094, v3070, v3037, a3299, a3298, a3297, e3296,
      a3295, a3294, a3293, a3292, a3291, a3290, a3289, a3288, a3287, e3286, a3285, a3284,
      a3283, a3282, a3281, a3280, a3279, a3278, a3277, a3276, a3275, e3274, a3273, a3272,
      a3271, a3270, a3269, a3268, a3267, e3266, a3265, a3264, a3263, a3262, e3261, a3260,
      a3259, a3258, e3257]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a3301, a3300, hB]

set_option maxRecDepth 10000 in
theorem vtSide01 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (15 + c))) = ev c) :
    σ (.n 3358) =
      vtSideVal [σ (.n 989), σ (.n 998), σ (.n 1007), σ (.n 1016), σ (.n 1025)]
        (σ (.n 14)) W ev vtBTerms01 := by
  rw [vtB01_4 h hw hev, vtB01_3 h hw hev, vtB01_2 h hw hev, vtB01_1 h hw hev, vtB01_0 h hw hev]
  simp only [vtSideVal, vtBTerms01, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, add_zero, add_assoc]

set_option maxRecDepth 10000 in
theorem vtD1_0 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (15 + c))) = ev c) :
    σ (.n 3364) = σ (.n 1978) * vtSlots W ev 0
      [[], [([0], 3)], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 3303 [
    .atom (.const (.n 3360) (word 3 0)),
    .atom (.mul (.n 3361) (.n 3360) (.n 3013)),
    .atom (.load (.n 3362) (.n 13) 1),
    .atom (.mul (.n 3363) (.n 3362) (.n 3361)),
    .atom (.mul (.n 3364) (.n 1978) (.n 3363))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a3303, a3304, a3305, a3306, a3307, -⟩ := hs
  have e3305 := tb_loadHolds_unique a3305 (hw 1 (by norm_num))
  have v3013 : σ (.n 3013) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_eval h (k := 15) (by norm_num)).2.2
  have hB : σ (.n 3363) = vtSlots W ev 0 [[], [([0], 3)], []] := by
    simp only [v3013, a3306, e3305, a3304, a3303]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a3307, hB]

set_option maxRecDepth 10000 in
theorem vtD1_1 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (15 + c))) = ev c) :
    σ (.n 3370) = σ (.n 3364) + σ (.n 1980) * vtSlots W ev 0
      [[], [], [([14], 3)], [], [], [], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 3308 [
    .atom (.const (.n 3365) (word 3 0)),
    .atom (.mul (.n 3366) (.n 3365) (.n 3219)),
    .atom (.load (.n 3367) (.n 13) 2),
    .atom (.mul (.n 3368) (.n 3367) (.n 3366)),
    .atom (.mul (.n 3369) (.n 1980) (.n 3368)),
    .atom (.add (.n 3370) (.n 3364) (.n 3369))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a3308, a3309, a3310, a3311, a3312, a3313, -⟩ := hs
  have e3310 := tb_loadHolds_unique a3310 (hw 2 (by norm_num))
  have v3219 : σ (.n 3219) = ev 14 := by
    rw [← hev 14 (by norm_num)]; exact (vt_eval h (k := 29) (by norm_num)).2.2
  have hB : σ (.n 3368) = vtSlots W ev 0 [[], [], [([14], 3)], [], [], [], [], [], []] := by
    simp only [v3219, a3311, e3310, a3309, a3308]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a3313, a3312, hB]

set_option maxRecDepth 10000 in
theorem vtD1_2 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (15 + c))) = ev c) :
    σ (.n 3376) = σ (.n 3370) + σ (.n 1982) * vtSlots W ev 0
      [[], [], [([11], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 3314 [
    .atom (.const (.n 3371) (word 3 0)),
    .atom (.mul (.n 3372) (.n 3371) (.n 3173)),
    .atom (.load (.n 3373) (.n 13) 2),
    .atom (.mul (.n 3374) (.n 3373) (.n 3372)),
    .atom (.mul (.n 3375) (.n 1982) (.n 3374)),
    .atom (.add (.n 3376) (.n 3370) (.n 3375))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a3314, a3315, a3316, a3317, a3318, a3319, -⟩ := hs
  have e3316 := tb_loadHolds_unique a3316 (hw 2 (by norm_num))
  have v3173 : σ (.n 3173) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_eval h (k := 26) (by norm_num)).2.2
  have hB : σ (.n 3374) = vtSlots W ev 0 [[], [], [([11], 3)], [], [], []] := by
    simp only [v3173, a3317, e3316, a3315, a3314]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a3319, a3318, hB]

set_option maxRecDepth 10000 in
theorem vtD1_3 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (15 + c))) = ev c) :
    σ (.n 3382) = σ (.n 3376) + σ (.n 1984) * vtSlots W ev 0
      [[], [], [([12], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 3320 [
    .atom (.const (.n 3377) (word 3 0)),
    .atom (.mul (.n 3378) (.n 3377) (.n 3184)),
    .atom (.load (.n 3379) (.n 13) 2),
    .atom (.mul (.n 3380) (.n 3379) (.n 3378)),
    .atom (.mul (.n 3381) (.n 1984) (.n 3380)),
    .atom (.add (.n 3382) (.n 3376) (.n 3381))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a3320, a3321, a3322, a3323, a3324, a3325, -⟩ := hs
  have e3322 := tb_loadHolds_unique a3322 (hw 2 (by norm_num))
  have v3184 : σ (.n 3184) = ev 12 := by
    rw [← hev 12 (by norm_num)]; exact (vt_eval h (k := 27) (by norm_num)).2.2
  have hB : σ (.n 3380) = vtSlots W ev 0 [[], [], [([12], 3)], [], [], []] := by
    simp only [v3184, a3323, e3322, a3321, a3320]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a3325, a3324, hB]

set_option maxRecDepth 10000 in
theorem vtD1_4 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (15 + c))) = ev c) :
    σ (.n 3388) = σ (.n 3382) + σ (.n 1986) * vtSlots W ev 0
      [[], [], [([13], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 3326 [
    .atom (.const (.n 3383) (word 3 0)),
    .atom (.mul (.n 3384) (.n 3383) (.n 3208)),
    .atom (.load (.n 3385) (.n 13) 2),
    .atom (.mul (.n 3386) (.n 3385) (.n 3384)),
    .atom (.mul (.n 3387) (.n 1986) (.n 3386)),
    .atom (.add (.n 3388) (.n 3382) (.n 3387))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a3326, a3327, a3328, a3329, a3330, a3331, -⟩ := hs
  have e3328 := tb_loadHolds_unique a3328 (hw 2 (by norm_num))
  have v3208 : σ (.n 3208) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 28) (by norm_num)).2.2
  have hB : σ (.n 3386) = vtSlots W ev 0 [[], [], [([13], 3)], [], [], []] := by
    simp only [v3208, a3329, e3328, a3327, a3326]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a3331, a3330, hB]

set_option maxRecDepth 10000 in
theorem vtSide11 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (15 + c))) = ev c) :
    σ (.n 3389) =
      vtSideVal [σ (.n 1978), σ (.n 1980), σ (.n 1982), σ (.n 1984), σ (.n 1986)]
        (σ (.n 14)) W ev vtBTerms11 := by
  have hF0 : σ (.n 3358) =
      vtSideVal [σ (.n 1978), σ (.n 1980), σ (.n 1982), σ (.n 1984), σ (.n 1986)]
        (σ (.n 14)) W ev vtBTerms01 := by
    rw [vtPullSels1 h]; exact vtSide01 h hw hev
  have a3332 := h.atomAt 3332 (.add (.n 3389) (.n 3358) (.n 3388)) (by decide +kernel)
  simp only [Atom.Holds] at a3332
  rw [vtSideVal_pull _ _ _ _ _ _ _ vtPull1, ← hF0, a3332, vtD1_4 h hw hev, vtD1_3 h hw hev, vtD1_2 h hw hev, vtD1_1 h hw hev, vtD1_0 h hw hev]
  simp only [vtDiffSum, vtDTerms1, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, add_zero, add_assoc]

set_option maxRecDepth 10000 in
theorem vtSide21 {rd : Reader} {σ : Val} (h : VtH rd σ) {ev : ℕ → E}
    (hev : ∀ c < 15, σ (.n (vtEvB (15 + c))) = ev c) :
    σ (.n 3398) =
      vtSideVal [σ (.n 2101), σ (.n 2110), σ (.n 2119), σ (.n 2128)]
        (0) (fun _ ↦ 1) ev vtBTerms21 := by
  obtain ⟨_, hs⟩ := h.sliceAt 3335 [
    .atom (.mul (.n 3392) (.n 2101) (.n 3173)),
    .atom (.mul (.n 3393) (.n 2110) (.n 3184)),
    .atom (.add (.n 3394) (.n 3392) (.n 3393)),
    .atom (.mul (.n 3395) (.n 2119) (.n 3208)),
    .atom (.add (.n 3396) (.n 3394) (.n 3395)),
    .atom (.mul (.n 3397) (.n 2128) (.n 3219)),
    .atom (.add (.n 3398) (.n 3396) (.n 3397))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a3335, a3336, a3337, a3338, a3339, a3340, a3341, -⟩ := hs
  have v3173 : σ (.n 3173) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_eval h (k := 26) (by norm_num)).2.2
  have v3184 : σ (.n 3184) = ev 12 := by
    rw [← hev 12 (by norm_num)]; exact (vt_eval h (k := 27) (by norm_num)).2.2
  have v3208 : σ (.n 3208) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_eval h (k := 28) (by norm_num)).2.2
  have v3219 : σ (.n 3219) = ev 14 := by
    rw [← hev 14 (by norm_num)]; exact (vt_eval h (k := 29) (by norm_num)).2.2
  rw [a3341, a3339, a3337, a3335, a3336, a3338, a3340, v3173, v3184, v3208, v3219]
  simp only [vtSideVal, vtBTerms21, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, vt_ofK_ofBits_one, zero_add,
    one_mul, mul_one, add_zero, add_assoc]

end
end LeanVM.Guest.B1.Tables
