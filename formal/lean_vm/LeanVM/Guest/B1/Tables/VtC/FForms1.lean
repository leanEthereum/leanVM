/-
  LeanVM.Guest.B1.Tables.VtC.FForms1

  `Vt/FormsT1.lean` on the window `VtF` (generated: scripts/b1c-vt/gentwins.py).

  Do not edit: `scripts/b1c-vt/all.py` writes it (`regen-guest.sh`, step `vt`).
-/

module

public import LeanVM.Guest.B1.Tables.VtC.FEvals
public import LeanVM.Guest.B1.Tables.Vt.FormsT1

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

set_option maxRecDepth 10000 in
theorem vtB01_0F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 13, σ (.n (vtEvB (13 + c))) = ev c) :
    σ (.n 3108) = σ (.n 887) * vtBlockVal (σ (.n 14)) W ev
      [[([], 1)], [([0], 2)], [([1], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 2990 [
    .atom (.const (.n 3030) (word 1 0)),
    .atom (.const (.n 3031) (word 2 0)),
    .atom (.mul (.n 3032) (.n 3031) (.n 2942)),
    .atom (.copy (.n 3033) (.n 3032)),
    .atom (.copy (.n 3034) (.n 2946))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a2990, a2991, a2992, a2993, a2994, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 3059 [
    .atom (.load (.n 3099) (.n 13) 0),
    .atom (.mul (.n 3100) (.n 3099) (.n 3030)),
    .atom (.load (.n 3101) (.n 13) 1),
    .atom (.mul (.n 3102) (.n 3101) (.n 3033)),
    .atom (.add (.n 3103) (.n 3100) (.n 3102)),
    .atom (.load (.n 3104) (.n 13) 2),
    .atom (.mul (.n 3105) (.n 3104) (.n 3034)),
    .atom (.add (.n 3106) (.n 3103) (.n 3105)),
    .atom (.add (.n 3107) (.n 14) (.n 3106)),
    .atom (.mul (.n 3108) (.n 887) (.n 3107))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a3059, a3060, a3061, a3062, a3063, a3064, a3065, a3066, a3067, a3068, -⟩ := hs1
  have e3059 := tb_loadHolds_unique a3059 (hw 0 (by norm_num))
  have e3061 := tb_loadHolds_unique a3061 (hw 1 (by norm_num))
  have e3064 := tb_loadHolds_unique a3064 (hw 2 (by norm_num))
  have v2942 : σ (.n 2942) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_evalF h (k := 13) (by norm_num)).2.2
  have v2946 : σ (.n 2946) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 14) (by norm_num)).2.2
  have hB : σ (.n 3107) = vtBlockVal (σ (.n 14)) W ev [[([], 1)], [([0], 2)], [([1], 1)]] := by
    simp only [v2946, v2942, a3067, a3066, a3065, e3064, a3063, a3062, e3061, a3060, e3059, a2994, a2993,
      a2992, a2991, a2990]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a3068, hB]

set_option maxRecDepth 10000 in
theorem vtB01_1F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 13, σ (.n (vtEvB (13 + c))) = ev c) :
    σ (.n 3137) = σ (.n 3108) + σ (.n 896) * vtBlockVal (σ (.n 14)) W ev
      [[([], 4)], [([0], 1)], [([12], 2)], [([], 2)], [([2], 1)], [([3], 1)], [([4], 1)], [([], 0)], [([], 0)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 2995 [
    .atom (.const (.n 3035) (word 4 0)),
    .atom (.copy (.n 3036) (.n 2942)),
    .atom (.const (.n 3037) (word 2 0)),
    .atom (.mul (.n 3038) (.n 3037) (.n 3029)),
    .atom (.copy (.n 3039) (.n 3038)),
    .atom (.const (.n 3040) (word 2 0)),
    .atom (.copy (.n 3041) (.n 2950)),
    .atom (.copy (.n 3042) (.n 2967)),
    .atom (.copy (.n 3043) (.n 2971)),
    .atom (.const (.n 3044) (word 0 0)),
    .atom (.const (.n 3045) (word 0 0))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a2995, a2996, a2997, a2998, a2999, a3000, a3001, a3002, a3003, a3004, a3005, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 3069 [
    .atom (.load (.n 3109) (.n 13) 0),
    .atom (.mul (.n 3110) (.n 3109) (.n 3035)),
    .atom (.load (.n 3111) (.n 13) 1),
    .atom (.mul (.n 3112) (.n 3111) (.n 3036)),
    .atom (.add (.n 3113) (.n 3110) (.n 3112)),
    .atom (.load (.n 3114) (.n 13) 2),
    .atom (.mul (.n 3115) (.n 3114) (.n 3039)),
    .atom (.add (.n 3116) (.n 3113) (.n 3115)),
    .atom (.load (.n 3117) (.n 13) 3),
    .atom (.mul (.n 3118) (.n 3117) (.n 3040)),
    .atom (.add (.n 3119) (.n 3116) (.n 3118)),
    .atom (.load (.n 3120) (.n 13) 4),
    .atom (.mul (.n 3121) (.n 3120) (.n 3041)),
    .atom (.add (.n 3122) (.n 3119) (.n 3121)),
    .atom (.load (.n 3123) (.n 13) 5),
    .atom (.mul (.n 3124) (.n 3123) (.n 3042)),
    .atom (.add (.n 3125) (.n 3122) (.n 3124)),
    .atom (.load (.n 3126) (.n 13) 6),
    .atom (.mul (.n 3127) (.n 3126) (.n 3043)),
    .atom (.add (.n 3128) (.n 3125) (.n 3127)),
    .atom (.load (.n 3129) (.n 13) 7),
    .atom (.mul (.n 3130) (.n 3129) (.n 3044)),
    .atom (.add (.n 3131) (.n 3128) (.n 3130)),
    .atom (.load (.n 3132) (.n 13) 8),
    .atom (.mul (.n 3133) (.n 3132) (.n 3045)),
    .atom (.add (.n 3134) (.n 3131) (.n 3133)),
    .atom (.add (.n 3135) (.n 14) (.n 3134)),
    .atom (.mul (.n 3136) (.n 896) (.n 3135)),
    .atom (.add (.n 3137) (.n 3108) (.n 3136))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a3069, a3070, a3071, a3072, a3073, a3074, a3075, a3076, a3077, a3078, a3079, a3080, a3081, a3082,
    a3083, a3084, a3085, a3086, a3087, a3088, a3089, a3090, a3091, a3092, a3093, a3094, a3095,
    a3096, a3097, -⟩ := hs1
  have e3069 := tb_loadHolds_unique a3069 (hw 0 (by norm_num))
  have e3071 := tb_loadHolds_unique a3071 (hw 1 (by norm_num))
  have e3074 := tb_loadHolds_unique a3074 (hw 2 (by norm_num))
  have e3077 := tb_loadHolds_unique a3077 (hw 3 (by norm_num))
  have e3080 := tb_loadHolds_unique a3080 (hw 4 (by norm_num))
  have e3083 := tb_loadHolds_unique a3083 (hw 5 (by norm_num))
  have e3086 := tb_loadHolds_unique a3086 (hw 6 (by norm_num))
  have e3089 := tb_loadHolds_unique a3089 (hw 7 (by norm_num))
  have e3092 := tb_loadHolds_unique a3092 (hw 8 (by norm_num))
  have v2942 : σ (.n 2942) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_evalF h (k := 13) (by norm_num)).2.2
  have v2950 : σ (.n 2950) = ev 2 := by
    rw [← hev 2 (by norm_num)]; exact (vt_evalF h (k := 15) (by norm_num)).2.2
  have v2967 : σ (.n 2967) = ev 3 := by
    rw [← hev 3 (by norm_num)]; exact (vt_evalF h (k := 16) (by norm_num)).2.2
  have v2971 : σ (.n 2971) = ev 4 := by
    rw [← hev 4 (by norm_num)]; exact (vt_evalF h (k := 17) (by norm_num)).2.2
  have v3029 : σ (.n 3029) = ev 12 := by
    rw [← hev 12 (by norm_num)]; exact (vt_evalF h (k := 25) (by norm_num)).2.2
  have hB : σ (.n 3135) = vtBlockVal (σ (.n 14)) W ev [[([], 4)], [([0], 1)], [([12], 2)], [([], 2)], [([2], 1)], [([3], 1)], [([4], 1)], [([], 0)], [([], 0)]] := by
    simp only [v3029, v2971, v2967, v2950, v2942, a3095, a3094, a3093, e3092, a3091, a3090, e3089, a3088,
      a3087, e3086, a3085, a3084, e3083, a3082, a3081, e3080, a3079, a3078, e3077, a3076,
      a3075, e3074, a3073, a3072, e3071, a3070, e3069, a3005, a3004, a3003, a3002, a3001,
      a3000, a2999, a2998, a2997, a2996, a2995]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a3097, a3096, hB]

set_option maxRecDepth 10000 in
theorem vtB01_2F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 13, σ (.n (vtEvB (13 + c))) = ev c) :
    σ (.n 3154) = σ (.n 3137) + σ (.n 905) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 2], 1)], [([9], 2)], [([5], 1)], [([6], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 3006 [
    .atom (.const (.n 3046) (word 2 0)),
    .atom (.mul (.n 3047) (.n 2946) (.n 2950)),
    .atom (.copy (.n 3048) (.n 3047)),
    .atom (.const (.n 3049) (word 2 0)),
    .atom (.mul (.n 3050) (.n 3049) (.n 3004)),
    .atom (.copy (.n 3051) (.n 3050)),
    .atom (.copy (.n 3052) (.n 2975)),
    .atom (.copy (.n 3053) (.n 2979))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a3006, a3007, a3008, a3009, a3010, a3011, a3012, a3013, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 3098 [
    .atom (.load (.n 3138) (.n 13) 0),
    .atom (.mul (.n 3139) (.n 3138) (.n 3046)),
    .atom (.load (.n 3140) (.n 13) 1),
    .atom (.mul (.n 3141) (.n 3140) (.n 3048)),
    .atom (.add (.n 3142) (.n 3139) (.n 3141)),
    .atom (.load (.n 3143) (.n 13) 2),
    .atom (.mul (.n 3144) (.n 3143) (.n 3051)),
    .atom (.add (.n 3145) (.n 3142) (.n 3144)),
    .atom (.load (.n 3146) (.n 13) 3),
    .atom (.mul (.n 3147) (.n 3146) (.n 3052)),
    .atom (.add (.n 3148) (.n 3145) (.n 3147)),
    .atom (.load (.n 3149) (.n 13) 4),
    .atom (.mul (.n 3150) (.n 3149) (.n 3053)),
    .atom (.add (.n 3151) (.n 3148) (.n 3150)),
    .atom (.add (.n 3152) (.n 14) (.n 3151)),
    .atom (.mul (.n 3153) (.n 905) (.n 3152)),
    .atom (.add (.n 3154) (.n 3137) (.n 3153))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a3098, a3099, a3100, a3101, a3102, a3103, a3104, a3105, a3106, a3107, a3108, a3109, a3110, a3111,
    a3112, a3113, a3114, -⟩ := hs1
  have e3098 := tb_loadHolds_unique a3098 (hw 0 (by norm_num))
  have e3100 := tb_loadHolds_unique a3100 (hw 1 (by norm_num))
  have e3103 := tb_loadHolds_unique a3103 (hw 2 (by norm_num))
  have e3106 := tb_loadHolds_unique a3106 (hw 3 (by norm_num))
  have e3109 := tb_loadHolds_unique a3109 (hw 4 (by norm_num))
  have v2946 : σ (.n 2946) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 14) (by norm_num)).2.2
  have v2950 : σ (.n 2950) = ev 2 := by
    rw [← hev 2 (by norm_num)]; exact (vt_evalF h (k := 15) (by norm_num)).2.2
  have v2975 : σ (.n 2975) = ev 5 := by
    rw [← hev 5 (by norm_num)]; exact (vt_evalF h (k := 18) (by norm_num)).2.2
  have v2979 : σ (.n 2979) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_evalF h (k := 19) (by norm_num)).2.2
  have v3004 : σ (.n 3004) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_evalF h (k := 22) (by norm_num)).2.2
  have hB : σ (.n 3152) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 2], 1)], [([9], 2)], [([5], 1)], [([6], 1)]] := by
    simp only [v3004, v2979, v2975, v2950, v2946, a3112, a3111, a3110, e3109, a3108, a3107, e3106, a3105,
      a3104, e3103, a3102, a3101, e3100, a3099, e3098, a3013, a3012, a3011, a3010, a3009,
      a3008, a3007, a3006]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a3114, a3113, hB]

set_option maxRecDepth 10000 in
theorem vtB01_3F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 13, σ (.n (vtEvB (13 + c))) = ev c) :
    σ (.n 3171) = σ (.n 3154) + σ (.n 914) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 3], 1)], [([10], 2)], [([7], 1)], [([8], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 3014 [
    .atom (.const (.n 3054) (word 2 0)),
    .atom (.mul (.n 3055) (.n 2946) (.n 2967)),
    .atom (.copy (.n 3056) (.n 3055)),
    .atom (.const (.n 3057) (word 2 0)),
    .atom (.mul (.n 3058) (.n 3057) (.n 3008)),
    .atom (.copy (.n 3059) (.n 3058)),
    .atom (.copy (.n 3060) (.n 2996)),
    .atom (.copy (.n 3061) (.n 3000))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a3014, a3015, a3016, a3017, a3018, a3019, a3020, a3021, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 3115 [
    .atom (.load (.n 3155) (.n 13) 0),
    .atom (.mul (.n 3156) (.n 3155) (.n 3054)),
    .atom (.load (.n 3157) (.n 13) 1),
    .atom (.mul (.n 3158) (.n 3157) (.n 3056)),
    .atom (.add (.n 3159) (.n 3156) (.n 3158)),
    .atom (.load (.n 3160) (.n 13) 2),
    .atom (.mul (.n 3161) (.n 3160) (.n 3059)),
    .atom (.add (.n 3162) (.n 3159) (.n 3161)),
    .atom (.load (.n 3163) (.n 13) 3),
    .atom (.mul (.n 3164) (.n 3163) (.n 3060)),
    .atom (.add (.n 3165) (.n 3162) (.n 3164)),
    .atom (.load (.n 3166) (.n 13) 4),
    .atom (.mul (.n 3167) (.n 3166) (.n 3061)),
    .atom (.add (.n 3168) (.n 3165) (.n 3167)),
    .atom (.add (.n 3169) (.n 14) (.n 3168)),
    .atom (.mul (.n 3170) (.n 914) (.n 3169)),
    .atom (.add (.n 3171) (.n 3154) (.n 3170))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a3115, a3116, a3117, a3118, a3119, a3120, a3121, a3122, a3123, a3124, a3125, a3126, a3127, a3128,
    a3129, a3130, a3131, -⟩ := hs1
  have e3115 := tb_loadHolds_unique a3115 (hw 0 (by norm_num))
  have e3117 := tb_loadHolds_unique a3117 (hw 1 (by norm_num))
  have e3120 := tb_loadHolds_unique a3120 (hw 2 (by norm_num))
  have e3123 := tb_loadHolds_unique a3123 (hw 3 (by norm_num))
  have e3126 := tb_loadHolds_unique a3126 (hw 4 (by norm_num))
  have v2946 : σ (.n 2946) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 14) (by norm_num)).2.2
  have v2967 : σ (.n 2967) = ev 3 := by
    rw [← hev 3 (by norm_num)]; exact (vt_evalF h (k := 16) (by norm_num)).2.2
  have v2996 : σ (.n 2996) = ev 7 := by
    rw [← hev 7 (by norm_num)]; exact (vt_evalF h (k := 20) (by norm_num)).2.2
  have v3000 : σ (.n 3000) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_evalF h (k := 21) (by norm_num)).2.2
  have v3008 : σ (.n 3008) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_evalF h (k := 23) (by norm_num)).2.2
  have hB : σ (.n 3169) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 3], 1)], [([10], 2)], [([7], 1)], [([8], 1)]] := by
    simp only [v3008, v3000, v2996, v2967, v2946, a3129, a3128, a3127, e3126, a3125, a3124, e3123, a3122,
      a3121, e3120, a3119, a3118, e3117, a3116, e3115, a3021, a3020, a3019, a3018, a3017,
      a3016, a3015, a3014]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a3131, a3130, hB]

set_option maxRecDepth 10000 in
theorem vtB01_4F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 13, σ (.n (vtEvB (13 + c))) = ev c) :
    σ (.n 3188) = σ (.n 3171) + σ (.n 923) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 4], 1)], [([11], 2)], [([5, 7], 1), ([6, 8], 1)], [([5, 8], 1), ([6, 7], 1), ([6, 8], 2)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 3022 [
    .atom (.const (.n 3062) (word 2 0)),
    .atom (.mul (.n 3063) (.n 2946) (.n 2971)),
    .atom (.copy (.n 3064) (.n 3063)),
    .atom (.const (.n 3065) (word 2 0)),
    .atom (.mul (.n 3066) (.n 3065) (.n 3025)),
    .atom (.copy (.n 3067) (.n 3066)),
    .atom (.mul (.n 3068) (.n 2975) (.n 2996)),
    .atom (.mul (.n 3069) (.n 2979) (.n 3000)),
    .atom (.add (.n 3070) (.n 3068) (.n 3069)),
    .atom (.copy (.n 3071) (.n 3070)),
    .atom (.mul (.n 3072) (.n 2975) (.n 3000)),
    .atom (.mul (.n 3073) (.n 2979) (.n 2996)),
    .atom (.add (.n 3074) (.n 3072) (.n 3073)),
    .atom (.const (.n 3075) (word 2 0)),
    .atom (.mul (.n 3076) (.n 2979) (.n 3000)),
    .atom (.mul (.n 3077) (.n 3075) (.n 3076)),
    .atom (.add (.n 3078) (.n 3074) (.n 3077)),
    .atom (.copy (.n 3079) (.n 3078))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a3022, a3023, a3024, a3025, a3026, a3027, a3028, a3029, a3030, a3031, a3032, a3033, a3034, a3035,
    a3036, a3037, a3038, a3039, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 3132 [
    .atom (.load (.n 3172) (.n 13) 0),
    .atom (.mul (.n 3173) (.n 3172) (.n 3062)),
    .atom (.load (.n 3174) (.n 13) 1),
    .atom (.mul (.n 3175) (.n 3174) (.n 3064)),
    .atom (.add (.n 3176) (.n 3173) (.n 3175)),
    .atom (.load (.n 3177) (.n 13) 2),
    .atom (.mul (.n 3178) (.n 3177) (.n 3067)),
    .atom (.add (.n 3179) (.n 3176) (.n 3178)),
    .atom (.load (.n 3180) (.n 13) 3),
    .atom (.mul (.n 3181) (.n 3180) (.n 3071)),
    .atom (.add (.n 3182) (.n 3179) (.n 3181)),
    .atom (.load (.n 3183) (.n 13) 4),
    .atom (.mul (.n 3184) (.n 3183) (.n 3079)),
    .atom (.add (.n 3185) (.n 3182) (.n 3184)),
    .atom (.add (.n 3186) (.n 14) (.n 3185)),
    .atom (.mul (.n 3187) (.n 923) (.n 3186)),
    .atom (.add (.n 3188) (.n 3171) (.n 3187))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a3132, a3133, a3134, a3135, a3136, a3137, a3138, a3139, a3140, a3141, a3142, a3143, a3144, a3145,
    a3146, a3147, a3148, -⟩ := hs1
  have e3132 := tb_loadHolds_unique a3132 (hw 0 (by norm_num))
  have e3134 := tb_loadHolds_unique a3134 (hw 1 (by norm_num))
  have e3137 := tb_loadHolds_unique a3137 (hw 2 (by norm_num))
  have e3140 := tb_loadHolds_unique a3140 (hw 3 (by norm_num))
  have e3143 := tb_loadHolds_unique a3143 (hw 4 (by norm_num))
  have v2946 : σ (.n 2946) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 14) (by norm_num)).2.2
  have v2971 : σ (.n 2971) = ev 4 := by
    rw [← hev 4 (by norm_num)]; exact (vt_evalF h (k := 17) (by norm_num)).2.2
  have v2975 : σ (.n 2975) = ev 5 := by
    rw [← hev 5 (by norm_num)]; exact (vt_evalF h (k := 18) (by norm_num)).2.2
  have v2979 : σ (.n 2979) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_evalF h (k := 19) (by norm_num)).2.2
  have v2996 : σ (.n 2996) = ev 7 := by
    rw [← hev 7 (by norm_num)]; exact (vt_evalF h (k := 20) (by norm_num)).2.2
  have v3000 : σ (.n 3000) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_evalF h (k := 21) (by norm_num)).2.2
  have v3025 : σ (.n 3025) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_evalF h (k := 24) (by norm_num)).2.2
  have hB : σ (.n 3186) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 4], 1)], [([11], 2)], [([5, 7], 1), ([6, 8], 1)], [([5, 8], 1), ([6, 7], 1), ([6, 8], 2)]] := by
    simp only [v3025, v3000, v2996, v2979, v2975, v2971, v2946, a3146, a3145, a3144, e3143, a3142, a3141,
      e3140, a3139, a3138, e3137, a3136, a3135, e3134, a3133, e3132, a3039, a3038, a3037,
      a3036, a3035, a3034, a3033, a3032, a3031, a3030, a3029, a3028, a3027, a3026, a3025,
      a3024, a3023, a3022]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a3148, a3147, hB]

set_option maxRecDepth 10000 in
theorem vtSide01F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 13, σ (.n (vtEvB (13 + c))) = ev c) :
    σ (.n 3188) =
      vtSideVal [σ (.n 887), σ (.n 896), σ (.n 905), σ (.n 914), σ (.n 923)]
        (σ (.n 14)) W ev vtBTerms01 := by
  rw [vtB01_4F h hw hev, vtB01_3F h hw hev, vtB01_2F h hw hev, vtB01_1F h hw hev, vtB01_0F h hw hev]
  simp only [vtSideVal, vtBTerms01, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, add_zero, add_assoc]

set_option maxRecDepth 10000 in
theorem vtD1_0F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 13, σ (.n (vtEvB (13 + c))) = ev c) :
    σ (.n 3192) = σ (.n 1345) * vtSlots W ev 0
      [[], [([0], 3)], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 3040 [
    .atom (.const (.n 3080) (word 3 0)),
    .atom (.mul (.n 3081) (.n 3080) (.n 2942)),
    .atom (.copy (.n 3082) (.n 3081))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a3040, a3041, a3042, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 3150 [
    .atom (.load (.n 3190) (.n 13) 1),
    .atom (.mul (.n 3191) (.n 3190) (.n 3082)),
    .atom (.mul (.n 3192) (.n 1345) (.n 3191))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a3150, a3151, a3152, -⟩ := hs1
  have e3150 := tb_loadHolds_unique a3150 (hw 1 (by norm_num))
  have v2942 : σ (.n 2942) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_evalF h (k := 13) (by norm_num)).2.2
  have hB : σ (.n 3191) = vtSlots W ev 0 [[], [([0], 3)], []] := by
    simp only [v2942, a3151, e3150, a3042, a3041, a3040]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a3152, hB]

set_option maxRecDepth 10000 in
theorem vtD1_1F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 13, σ (.n (vtEvB (13 + c))) = ev c) :
    σ (.n 3196) = σ (.n 3192) + σ (.n 1347) * vtSlots W ev 0
      [[], [], [([12], 3)], [], [], [], [], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 3043 [
    .atom (.const (.n 3083) (word 3 0)),
    .atom (.mul (.n 3084) (.n 3083) (.n 3029)),
    .atom (.copy (.n 3085) (.n 3084))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a3043, a3044, a3045, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 3153 [
    .atom (.load (.n 3193) (.n 13) 2),
    .atom (.mul (.n 3194) (.n 3193) (.n 3085)),
    .atom (.mul (.n 3195) (.n 1347) (.n 3194)),
    .atom (.add (.n 3196) (.n 3192) (.n 3195))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a3153, a3154, a3155, a3156, -⟩ := hs1
  have e3153 := tb_loadHolds_unique a3153 (hw 2 (by norm_num))
  have v3029 : σ (.n 3029) = ev 12 := by
    rw [← hev 12 (by norm_num)]; exact (vt_evalF h (k := 25) (by norm_num)).2.2
  have hB : σ (.n 3194) = vtSlots W ev 0 [[], [], [([12], 3)], [], [], [], [], [], []] := by
    simp only [v3029, a3154, e3153, a3045, a3044, a3043]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a3156, a3155, hB]

set_option maxRecDepth 10000 in
theorem vtD1_2F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 13, σ (.n (vtEvB (13 + c))) = ev c) :
    σ (.n 3200) = σ (.n 3196) + σ (.n 1349) * vtSlots W ev 0
      [[], [], [([9], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 3046 [
    .atom (.const (.n 3086) (word 3 0)),
    .atom (.mul (.n 3087) (.n 3086) (.n 3004)),
    .atom (.copy (.n 3088) (.n 3087))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a3046, a3047, a3048, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 3157 [
    .atom (.load (.n 3197) (.n 13) 2),
    .atom (.mul (.n 3198) (.n 3197) (.n 3088)),
    .atom (.mul (.n 3199) (.n 1349) (.n 3198)),
    .atom (.add (.n 3200) (.n 3196) (.n 3199))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a3157, a3158, a3159, a3160, -⟩ := hs1
  have e3157 := tb_loadHolds_unique a3157 (hw 2 (by norm_num))
  have v3004 : σ (.n 3004) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_evalF h (k := 22) (by norm_num)).2.2
  have hB : σ (.n 3198) = vtSlots W ev 0 [[], [], [([9], 3)], [], []] := by
    simp only [v3004, a3158, e3157, a3048, a3047, a3046]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a3160, a3159, hB]

set_option maxRecDepth 10000 in
theorem vtD1_3F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 13, σ (.n (vtEvB (13 + c))) = ev c) :
    σ (.n 3204) = σ (.n 3200) + σ (.n 1351) * vtSlots W ev 0
      [[], [], [([10], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 3049 [
    .atom (.const (.n 3089) (word 3 0)),
    .atom (.mul (.n 3090) (.n 3089) (.n 3008)),
    .atom (.copy (.n 3091) (.n 3090))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a3049, a3050, a3051, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 3161 [
    .atom (.load (.n 3201) (.n 13) 2),
    .atom (.mul (.n 3202) (.n 3201) (.n 3091)),
    .atom (.mul (.n 3203) (.n 1351) (.n 3202)),
    .atom (.add (.n 3204) (.n 3200) (.n 3203))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a3161, a3162, a3163, a3164, -⟩ := hs1
  have e3161 := tb_loadHolds_unique a3161 (hw 2 (by norm_num))
  have v3008 : σ (.n 3008) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_evalF h (k := 23) (by norm_num)).2.2
  have hB : σ (.n 3202) = vtSlots W ev 0 [[], [], [([10], 3)], [], []] := by
    simp only [v3008, a3162, e3161, a3051, a3050, a3049]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a3164, a3163, hB]

set_option maxRecDepth 10000 in
theorem vtD1_4F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 13, σ (.n (vtEvB (13 + c))) = ev c) :
    σ (.n 3208) = σ (.n 3204) + σ (.n 1353) * vtSlots W ev 0
      [[], [], [([11], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 3052 [
    .atom (.const (.n 3092) (word 3 0)),
    .atom (.mul (.n 3093) (.n 3092) (.n 3025)),
    .atom (.copy (.n 3094) (.n 3093))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a3052, a3053, a3054, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 3165 [
    .atom (.load (.n 3205) (.n 13) 2),
    .atom (.mul (.n 3206) (.n 3205) (.n 3094)),
    .atom (.mul (.n 3207) (.n 1353) (.n 3206)),
    .atom (.add (.n 3208) (.n 3204) (.n 3207))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a3165, a3166, a3167, a3168, -⟩ := hs1
  have e3165 := tb_loadHolds_unique a3165 (hw 2 (by norm_num))
  have v3025 : σ (.n 3025) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_evalF h (k := 24) (by norm_num)).2.2
  have hB : σ (.n 3206) = vtSlots W ev 0 [[], [], [([11], 3)], [], []] := by
    simp only [v3025, a3166, e3165, a3054, a3053, a3052]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a3168, a3167, hB]

set_option maxRecDepth 10000 in
theorem vtSide11F {rd : Reader} {σ : Val} (h : VtF rd σ)
    (hq : [σ (.n 1345), σ (.n 1347), σ (.n 1349), σ (.n 1351), σ (.n 1353)] = [σ (.n 887), σ (.n 896), σ (.n 905), σ (.n 914), σ (.n 923)]) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 13, σ (.n (vtEvB (13 + c))) = ev c) :
    σ (.n 3209) =
      vtSideVal [σ (.n 1345), σ (.n 1347), σ (.n 1349), σ (.n 1351), σ (.n 1353)]
        (σ (.n 14)) W ev vtBTerms11 := by
  have hF0 : σ (.n 3188) =
      vtSideVal [σ (.n 1345), σ (.n 1347), σ (.n 1349), σ (.n 1351), σ (.n 1353)]
        (σ (.n 14)) W ev vtBTerms01 := by
    rw [hq]; exact vtSide01F h hw hev
  have a3169 := h.atomAt 3169 (.add (.n 3209) (.n 3188) (.n 3208)) (by decide +kernel)
  simp only [Atom.Holds] at a3169
  rw [vtSideVal_pull _ _ _ _ _ _ _ vtPull1, ← hF0, a3169, vtD1_4F h hw hev, vtD1_3F h hw hev, vtD1_2F h hw hev, vtD1_1F h hw hev, vtD1_0F h hw hev]
  simp only [vtDiffSum, vtDTerms1, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, add_zero, add_assoc]

set_option maxRecDepth 10000 in
theorem vtSide21F {rd : Reader} {σ : Val} (h : VtF rd σ) {ev : ℕ → E}
    (hev : ∀ c < 13, σ (.n (vtEvB (13 + c))) = ev c) :
    σ (.n 3218) =
      vtSideVal [σ (.n 1465), σ (.n 1474), σ (.n 1483), σ (.n 1492)]
        (0) (fun _ ↦ 1) ev vtBTerms21 := by
  obtain ⟨_, hs0⟩ := h.sliceAt 3055 [
    .atom (.copy (.n 3095) (.n 3004)),
    .atom (.copy (.n 3096) (.n 3008)),
    .atom (.copy (.n 3097) (.n 3025)),
    .atom (.copy (.n 3098) (.n 3029))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a3055, a3056, a3057, a3058, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 3172 [
    .atom (.mul (.n 3212) (.n 1465) (.n 3095)),
    .atom (.mul (.n 3213) (.n 1474) (.n 3096)),
    .atom (.add (.n 3214) (.n 3212) (.n 3213)),
    .atom (.mul (.n 3215) (.n 1483) (.n 3097)),
    .atom (.add (.n 3216) (.n 3214) (.n 3215)),
    .atom (.mul (.n 3217) (.n 1492) (.n 3098)),
    .atom (.add (.n 3218) (.n 3216) (.n 3217))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a3172, a3173, a3174, a3175, a3176, a3177, a3178, -⟩ := hs1
  have v3004 : σ (.n 3004) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_evalF h (k := 22) (by norm_num)).2.2
  have v3008 : σ (.n 3008) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_evalF h (k := 23) (by norm_num)).2.2
  have v3025 : σ (.n 3025) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_evalF h (k := 24) (by norm_num)).2.2
  have v3029 : σ (.n 3029) = ev 12 := by
    rw [← hev 12 (by norm_num)]; exact (vt_evalF h (k := 25) (by norm_num)).2.2
  simp only [v3029, v3025, v3008, v3004, a3178, a3177, a3176, a3175, a3174, a3173, a3172, a3058, a3057, a3056,
    a3055]
  simp only [vtSideVal, vtBTerms21, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, vt_ofK_ofBits_one]
  ring

end
end LeanVM.Guest.B1.Tables
