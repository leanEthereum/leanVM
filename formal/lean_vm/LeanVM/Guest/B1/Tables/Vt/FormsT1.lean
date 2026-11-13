/-
  LeanVM.Guest.B1.Tables.Vt.FormsT1

  Table 1's forms on the three sides, from the guest's statements: each block's value from its
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
theorem vtB01_0 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 13, σ (.n (vtEvB (13 + c))) = ev c) :
    σ (.n 3103) = σ (.n 886) * vtBlockVal (σ (.n 14)) W ev
      [[([], 1)], [([0], 2)], [([1], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 2985 [
    .atom (.const (.n 3025) (word 1 0)),
    .atom (.const (.n 3026) (word 2 0)),
    .atom (.mul (.n 3027) (.n 3026) (.n 2937)),
    .atom (.copy (.n 3028) (.n 3027)),
    .atom (.copy (.n 3029) (.n 2941))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a2985, a2986, a2987, a2988, a2989, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 3054 [
    .atom (.load (.n 3094) (.n 13) 0),
    .atom (.mul (.n 3095) (.n 3094) (.n 3025)),
    .atom (.load (.n 3096) (.n 13) 1),
    .atom (.mul (.n 3097) (.n 3096) (.n 3028)),
    .atom (.add (.n 3098) (.n 3095) (.n 3097)),
    .atom (.load (.n 3099) (.n 13) 2),
    .atom (.mul (.n 3100) (.n 3099) (.n 3029)),
    .atom (.add (.n 3101) (.n 3098) (.n 3100)),
    .atom (.add (.n 3102) (.n 14) (.n 3101)),
    .atom (.mul (.n 3103) (.n 886) (.n 3102))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a3054, a3055, a3056, a3057, a3058, a3059, a3060, a3061, a3062, a3063, -⟩ := hs1
  have e3054 := tb_loadHolds_unique a3054 (hw 0 (by norm_num))
  have e3056 := tb_loadHolds_unique a3056 (hw 1 (by norm_num))
  have e3059 := tb_loadHolds_unique a3059 (hw 2 (by norm_num))
  have v2937 : σ (.n 2937) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_eval h (k := 13) (by norm_num)).2.2
  have v2941 : σ (.n 2941) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 14) (by norm_num)).2.2
  have hB : σ (.n 3102) = vtBlockVal (σ (.n 14)) W ev [[([], 1)], [([0], 2)], [([1], 1)]] := by
    simp only [v2941, v2937, a3062, a3061, a3060, e3059, a3058, a3057, e3056, a3055, e3054, a2989, a2988,
      a2987, a2986, a2985]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a3063, hB]

set_option maxRecDepth 10000 in
theorem vtB01_1 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 13, σ (.n (vtEvB (13 + c))) = ev c) :
    σ (.n 3132) = σ (.n 3103) + σ (.n 895) * vtBlockVal (σ (.n 14)) W ev
      [[([], 4)], [([0], 1)], [([12], 2)], [([], 2)], [([2], 1)], [([3], 1)], [([4], 1)], [([], 0)], [([], 0)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 2990 [
    .atom (.const (.n 3030) (word 4 0)),
    .atom (.copy (.n 3031) (.n 2937)),
    .atom (.const (.n 3032) (word 2 0)),
    .atom (.mul (.n 3033) (.n 3032) (.n 3024)),
    .atom (.copy (.n 3034) (.n 3033)),
    .atom (.const (.n 3035) (word 2 0)),
    .atom (.copy (.n 3036) (.n 2945)),
    .atom (.copy (.n 3037) (.n 2962)),
    .atom (.copy (.n 3038) (.n 2966)),
    .atom (.const (.n 3039) (word 0 0)),
    .atom (.const (.n 3040) (word 0 0))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a2990, a2991, a2992, a2993, a2994, a2995, a2996, a2997, a2998, a2999, a3000, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 3064 [
    .atom (.load (.n 3104) (.n 13) 0),
    .atom (.mul (.n 3105) (.n 3104) (.n 3030)),
    .atom (.load (.n 3106) (.n 13) 1),
    .atom (.mul (.n 3107) (.n 3106) (.n 3031)),
    .atom (.add (.n 3108) (.n 3105) (.n 3107)),
    .atom (.load (.n 3109) (.n 13) 2),
    .atom (.mul (.n 3110) (.n 3109) (.n 3034)),
    .atom (.add (.n 3111) (.n 3108) (.n 3110)),
    .atom (.load (.n 3112) (.n 13) 3),
    .atom (.mul (.n 3113) (.n 3112) (.n 3035)),
    .atom (.add (.n 3114) (.n 3111) (.n 3113)),
    .atom (.load (.n 3115) (.n 13) 4),
    .atom (.mul (.n 3116) (.n 3115) (.n 3036)),
    .atom (.add (.n 3117) (.n 3114) (.n 3116)),
    .atom (.load (.n 3118) (.n 13) 5),
    .atom (.mul (.n 3119) (.n 3118) (.n 3037)),
    .atom (.add (.n 3120) (.n 3117) (.n 3119)),
    .atom (.load (.n 3121) (.n 13) 6),
    .atom (.mul (.n 3122) (.n 3121) (.n 3038)),
    .atom (.add (.n 3123) (.n 3120) (.n 3122)),
    .atom (.load (.n 3124) (.n 13) 7),
    .atom (.mul (.n 3125) (.n 3124) (.n 3039)),
    .atom (.add (.n 3126) (.n 3123) (.n 3125)),
    .atom (.load (.n 3127) (.n 13) 8),
    .atom (.mul (.n 3128) (.n 3127) (.n 3040)),
    .atom (.add (.n 3129) (.n 3126) (.n 3128)),
    .atom (.add (.n 3130) (.n 14) (.n 3129)),
    .atom (.mul (.n 3131) (.n 895) (.n 3130)),
    .atom (.add (.n 3132) (.n 3103) (.n 3131))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a3064, a3065, a3066, a3067, a3068, a3069, a3070, a3071, a3072, a3073, a3074, a3075, a3076, a3077,
    a3078, a3079, a3080, a3081, a3082, a3083, a3084, a3085, a3086, a3087, a3088, a3089, a3090,
    a3091, a3092, -⟩ := hs1
  have e3064 := tb_loadHolds_unique a3064 (hw 0 (by norm_num))
  have e3066 := tb_loadHolds_unique a3066 (hw 1 (by norm_num))
  have e3069 := tb_loadHolds_unique a3069 (hw 2 (by norm_num))
  have e3072 := tb_loadHolds_unique a3072 (hw 3 (by norm_num))
  have e3075 := tb_loadHolds_unique a3075 (hw 4 (by norm_num))
  have e3078 := tb_loadHolds_unique a3078 (hw 5 (by norm_num))
  have e3081 := tb_loadHolds_unique a3081 (hw 6 (by norm_num))
  have e3084 := tb_loadHolds_unique a3084 (hw 7 (by norm_num))
  have e3087 := tb_loadHolds_unique a3087 (hw 8 (by norm_num))
  have v2937 : σ (.n 2937) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_eval h (k := 13) (by norm_num)).2.2
  have v2945 : σ (.n 2945) = ev 2 := by
    rw [← hev 2 (by norm_num)]; exact (vt_eval h (k := 15) (by norm_num)).2.2
  have v2962 : σ (.n 2962) = ev 3 := by
    rw [← hev 3 (by norm_num)]; exact (vt_eval h (k := 16) (by norm_num)).2.2
  have v2966 : σ (.n 2966) = ev 4 := by
    rw [← hev 4 (by norm_num)]; exact (vt_eval h (k := 17) (by norm_num)).2.2
  have v3024 : σ (.n 3024) = ev 12 := by
    rw [← hev 12 (by norm_num)]; exact (vt_eval h (k := 25) (by norm_num)).2.2
  have hB : σ (.n 3130) = vtBlockVal (σ (.n 14)) W ev [[([], 4)], [([0], 1)], [([12], 2)], [([], 2)], [([2], 1)], [([3], 1)], [([4], 1)], [([], 0)], [([], 0)]] := by
    simp only [v3024, v2966, v2962, v2945, v2937, a3090, a3089, a3088, e3087, a3086, a3085, e3084, a3083,
      a3082, e3081, a3080, a3079, e3078, a3077, a3076, e3075, a3074, a3073, e3072, a3071,
      a3070, e3069, a3068, a3067, e3066, a3065, e3064, a3000, a2999, a2998, a2997, a2996,
      a2995, a2994, a2993, a2992, a2991, a2990]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a3092, a3091, hB]

set_option maxRecDepth 10000 in
theorem vtB01_2 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 13, σ (.n (vtEvB (13 + c))) = ev c) :
    σ (.n 3149) = σ (.n 3132) + σ (.n 904) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 2], 1)], [([9], 2)], [([5], 1)], [([6], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 3001 [
    .atom (.const (.n 3041) (word 2 0)),
    .atom (.mul (.n 3042) (.n 2941) (.n 2945)),
    .atom (.copy (.n 3043) (.n 3042)),
    .atom (.const (.n 3044) (word 2 0)),
    .atom (.mul (.n 3045) (.n 3044) (.n 2999)),
    .atom (.copy (.n 3046) (.n 3045)),
    .atom (.copy (.n 3047) (.n 2970)),
    .atom (.copy (.n 3048) (.n 2974))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a3001, a3002, a3003, a3004, a3005, a3006, a3007, a3008, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 3093 [
    .atom (.load (.n 3133) (.n 13) 0),
    .atom (.mul (.n 3134) (.n 3133) (.n 3041)),
    .atom (.load (.n 3135) (.n 13) 1),
    .atom (.mul (.n 3136) (.n 3135) (.n 3043)),
    .atom (.add (.n 3137) (.n 3134) (.n 3136)),
    .atom (.load (.n 3138) (.n 13) 2),
    .atom (.mul (.n 3139) (.n 3138) (.n 3046)),
    .atom (.add (.n 3140) (.n 3137) (.n 3139)),
    .atom (.load (.n 3141) (.n 13) 3),
    .atom (.mul (.n 3142) (.n 3141) (.n 3047)),
    .atom (.add (.n 3143) (.n 3140) (.n 3142)),
    .atom (.load (.n 3144) (.n 13) 4),
    .atom (.mul (.n 3145) (.n 3144) (.n 3048)),
    .atom (.add (.n 3146) (.n 3143) (.n 3145)),
    .atom (.add (.n 3147) (.n 14) (.n 3146)),
    .atom (.mul (.n 3148) (.n 904) (.n 3147)),
    .atom (.add (.n 3149) (.n 3132) (.n 3148))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a3093, a3094, a3095, a3096, a3097, a3098, a3099, a3100, a3101, a3102, a3103, a3104, a3105, a3106,
    a3107, a3108, a3109, -⟩ := hs1
  have e3093 := tb_loadHolds_unique a3093 (hw 0 (by norm_num))
  have e3095 := tb_loadHolds_unique a3095 (hw 1 (by norm_num))
  have e3098 := tb_loadHolds_unique a3098 (hw 2 (by norm_num))
  have e3101 := tb_loadHolds_unique a3101 (hw 3 (by norm_num))
  have e3104 := tb_loadHolds_unique a3104 (hw 4 (by norm_num))
  have v2941 : σ (.n 2941) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 14) (by norm_num)).2.2
  have v2945 : σ (.n 2945) = ev 2 := by
    rw [← hev 2 (by norm_num)]; exact (vt_eval h (k := 15) (by norm_num)).2.2
  have v2970 : σ (.n 2970) = ev 5 := by
    rw [← hev 5 (by norm_num)]; exact (vt_eval h (k := 18) (by norm_num)).2.2
  have v2974 : σ (.n 2974) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_eval h (k := 19) (by norm_num)).2.2
  have v2999 : σ (.n 2999) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 22) (by norm_num)).2.2
  have hB : σ (.n 3147) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 2], 1)], [([9], 2)], [([5], 1)], [([6], 1)]] := by
    simp only [v2999, v2974, v2970, v2945, v2941, a3107, a3106, a3105, e3104, a3103, a3102, e3101, a3100,
      a3099, e3098, a3097, a3096, e3095, a3094, e3093, a3008, a3007, a3006, a3005, a3004,
      a3003, a3002, a3001]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a3109, a3108, hB]

set_option maxRecDepth 10000 in
theorem vtB01_3 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 13, σ (.n (vtEvB (13 + c))) = ev c) :
    σ (.n 3166) = σ (.n 3149) + σ (.n 913) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 3], 1)], [([10], 2)], [([7], 1)], [([8], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 3009 [
    .atom (.const (.n 3049) (word 2 0)),
    .atom (.mul (.n 3050) (.n 2941) (.n 2962)),
    .atom (.copy (.n 3051) (.n 3050)),
    .atom (.const (.n 3052) (word 2 0)),
    .atom (.mul (.n 3053) (.n 3052) (.n 3003)),
    .atom (.copy (.n 3054) (.n 3053)),
    .atom (.copy (.n 3055) (.n 2991)),
    .atom (.copy (.n 3056) (.n 2995))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a3009, a3010, a3011, a3012, a3013, a3014, a3015, a3016, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 3110 [
    .atom (.load (.n 3150) (.n 13) 0),
    .atom (.mul (.n 3151) (.n 3150) (.n 3049)),
    .atom (.load (.n 3152) (.n 13) 1),
    .atom (.mul (.n 3153) (.n 3152) (.n 3051)),
    .atom (.add (.n 3154) (.n 3151) (.n 3153)),
    .atom (.load (.n 3155) (.n 13) 2),
    .atom (.mul (.n 3156) (.n 3155) (.n 3054)),
    .atom (.add (.n 3157) (.n 3154) (.n 3156)),
    .atom (.load (.n 3158) (.n 13) 3),
    .atom (.mul (.n 3159) (.n 3158) (.n 3055)),
    .atom (.add (.n 3160) (.n 3157) (.n 3159)),
    .atom (.load (.n 3161) (.n 13) 4),
    .atom (.mul (.n 3162) (.n 3161) (.n 3056)),
    .atom (.add (.n 3163) (.n 3160) (.n 3162)),
    .atom (.add (.n 3164) (.n 14) (.n 3163)),
    .atom (.mul (.n 3165) (.n 913) (.n 3164)),
    .atom (.add (.n 3166) (.n 3149) (.n 3165))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a3110, a3111, a3112, a3113, a3114, a3115, a3116, a3117, a3118, a3119, a3120, a3121, a3122, a3123,
    a3124, a3125, a3126, -⟩ := hs1
  have e3110 := tb_loadHolds_unique a3110 (hw 0 (by norm_num))
  have e3112 := tb_loadHolds_unique a3112 (hw 1 (by norm_num))
  have e3115 := tb_loadHolds_unique a3115 (hw 2 (by norm_num))
  have e3118 := tb_loadHolds_unique a3118 (hw 3 (by norm_num))
  have e3121 := tb_loadHolds_unique a3121 (hw 4 (by norm_num))
  have v2941 : σ (.n 2941) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 14) (by norm_num)).2.2
  have v2962 : σ (.n 2962) = ev 3 := by
    rw [← hev 3 (by norm_num)]; exact (vt_eval h (k := 16) (by norm_num)).2.2
  have v2991 : σ (.n 2991) = ev 7 := by
    rw [← hev 7 (by norm_num)]; exact (vt_eval h (k := 20) (by norm_num)).2.2
  have v2995 : σ (.n 2995) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_eval h (k := 21) (by norm_num)).2.2
  have v3003 : σ (.n 3003) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_eval h (k := 23) (by norm_num)).2.2
  have hB : σ (.n 3164) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 3], 1)], [([10], 2)], [([7], 1)], [([8], 1)]] := by
    simp only [v3003, v2995, v2991, v2962, v2941, a3124, a3123, a3122, e3121, a3120, a3119, e3118, a3117,
      a3116, e3115, a3114, a3113, e3112, a3111, e3110, a3016, a3015, a3014, a3013, a3012,
      a3011, a3010, a3009]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a3126, a3125, hB]

set_option maxRecDepth 10000 in
theorem vtB01_4 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 13, σ (.n (vtEvB (13 + c))) = ev c) :
    σ (.n 3183) = σ (.n 3166) + σ (.n 922) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 4], 1)], [([11], 2)], [([5, 7], 1), ([6, 8], 1)], [([5, 8], 1), ([6, 7], 1), ([6, 8], 2)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 3017 [
    .atom (.const (.n 3057) (word 2 0)),
    .atom (.mul (.n 3058) (.n 2941) (.n 2966)),
    .atom (.copy (.n 3059) (.n 3058)),
    .atom (.const (.n 3060) (word 2 0)),
    .atom (.mul (.n 3061) (.n 3060) (.n 3020)),
    .atom (.copy (.n 3062) (.n 3061)),
    .atom (.mul (.n 3063) (.n 2970) (.n 2991)),
    .atom (.mul (.n 3064) (.n 2974) (.n 2995)),
    .atom (.add (.n 3065) (.n 3063) (.n 3064)),
    .atom (.copy (.n 3066) (.n 3065)),
    .atom (.mul (.n 3067) (.n 2970) (.n 2995)),
    .atom (.mul (.n 3068) (.n 2974) (.n 2991)),
    .atom (.add (.n 3069) (.n 3067) (.n 3068)),
    .atom (.const (.n 3070) (word 2 0)),
    .atom (.mul (.n 3071) (.n 2974) (.n 2995)),
    .atom (.mul (.n 3072) (.n 3070) (.n 3071)),
    .atom (.add (.n 3073) (.n 3069) (.n 3072)),
    .atom (.copy (.n 3074) (.n 3073))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a3017, a3018, a3019, a3020, a3021, a3022, a3023, a3024, a3025, a3026, a3027, a3028, a3029, a3030,
    a3031, a3032, a3033, a3034, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 3127 [
    .atom (.load (.n 3167) (.n 13) 0),
    .atom (.mul (.n 3168) (.n 3167) (.n 3057)),
    .atom (.load (.n 3169) (.n 13) 1),
    .atom (.mul (.n 3170) (.n 3169) (.n 3059)),
    .atom (.add (.n 3171) (.n 3168) (.n 3170)),
    .atom (.load (.n 3172) (.n 13) 2),
    .atom (.mul (.n 3173) (.n 3172) (.n 3062)),
    .atom (.add (.n 3174) (.n 3171) (.n 3173)),
    .atom (.load (.n 3175) (.n 13) 3),
    .atom (.mul (.n 3176) (.n 3175) (.n 3066)),
    .atom (.add (.n 3177) (.n 3174) (.n 3176)),
    .atom (.load (.n 3178) (.n 13) 4),
    .atom (.mul (.n 3179) (.n 3178) (.n 3074)),
    .atom (.add (.n 3180) (.n 3177) (.n 3179)),
    .atom (.add (.n 3181) (.n 14) (.n 3180)),
    .atom (.mul (.n 3182) (.n 922) (.n 3181)),
    .atom (.add (.n 3183) (.n 3166) (.n 3182))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a3127, a3128, a3129, a3130, a3131, a3132, a3133, a3134, a3135, a3136, a3137, a3138, a3139, a3140,
    a3141, a3142, a3143, -⟩ := hs1
  have e3127 := tb_loadHolds_unique a3127 (hw 0 (by norm_num))
  have e3129 := tb_loadHolds_unique a3129 (hw 1 (by norm_num))
  have e3132 := tb_loadHolds_unique a3132 (hw 2 (by norm_num))
  have e3135 := tb_loadHolds_unique a3135 (hw 3 (by norm_num))
  have e3138 := tb_loadHolds_unique a3138 (hw 4 (by norm_num))
  have v2941 : σ (.n 2941) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 14) (by norm_num)).2.2
  have v2966 : σ (.n 2966) = ev 4 := by
    rw [← hev 4 (by norm_num)]; exact (vt_eval h (k := 17) (by norm_num)).2.2
  have v2970 : σ (.n 2970) = ev 5 := by
    rw [← hev 5 (by norm_num)]; exact (vt_eval h (k := 18) (by norm_num)).2.2
  have v2974 : σ (.n 2974) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_eval h (k := 19) (by norm_num)).2.2
  have v2991 : σ (.n 2991) = ev 7 := by
    rw [← hev 7 (by norm_num)]; exact (vt_eval h (k := 20) (by norm_num)).2.2
  have v2995 : σ (.n 2995) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_eval h (k := 21) (by norm_num)).2.2
  have v3020 : σ (.n 3020) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_eval h (k := 24) (by norm_num)).2.2
  have hB : σ (.n 3181) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 4], 1)], [([11], 2)], [([5, 7], 1), ([6, 8], 1)], [([5, 8], 1), ([6, 7], 1), ([6, 8], 2)]] := by
    simp only [v3020, v2995, v2991, v2974, v2970, v2966, v2941, a3141, a3140, a3139, e3138, a3137, a3136,
      e3135, a3134, a3133, e3132, a3131, a3130, e3129, a3128, e3127, a3034, a3033, a3032,
      a3031, a3030, a3029, a3028, a3027, a3026, a3025, a3024, a3023, a3022, a3021, a3020,
      a3019, a3018, a3017]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a3143, a3142, hB]

set_option maxRecDepth 10000 in
theorem vtSide01 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 13, σ (.n (vtEvB (13 + c))) = ev c) :
    σ (.n 3183) =
      vtSideVal [σ (.n 886), σ (.n 895), σ (.n 904), σ (.n 913), σ (.n 922)]
        (σ (.n 14)) W ev vtBTerms01 := by
  rw [vtB01_4 h hw hev, vtB01_3 h hw hev, vtB01_2 h hw hev, vtB01_1 h hw hev, vtB01_0 h hw hev]
  simp only [vtSideVal, vtBTerms01, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, add_zero, add_assoc]

set_option maxRecDepth 10000 in
theorem vtD1_0 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 13, σ (.n (vtEvB (13 + c))) = ev c) :
    σ (.n 3187) = σ (.n 1344) * vtSlots W ev 0
      [[], [([0], 3)], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 3035 [
    .atom (.const (.n 3075) (word 3 0)),
    .atom (.mul (.n 3076) (.n 3075) (.n 2937)),
    .atom (.copy (.n 3077) (.n 3076))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a3035, a3036, a3037, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 3145 [
    .atom (.load (.n 3185) (.n 13) 1),
    .atom (.mul (.n 3186) (.n 3185) (.n 3077)),
    .atom (.mul (.n 3187) (.n 1344) (.n 3186))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a3145, a3146, a3147, -⟩ := hs1
  have e3145 := tb_loadHolds_unique a3145 (hw 1 (by norm_num))
  have v2937 : σ (.n 2937) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_eval h (k := 13) (by norm_num)).2.2
  have hB : σ (.n 3186) = vtSlots W ev 0 [[], [([0], 3)], []] := by
    simp only [v2937, a3146, e3145, a3037, a3036, a3035]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a3147, hB]

set_option maxRecDepth 10000 in
theorem vtD1_1 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 13, σ (.n (vtEvB (13 + c))) = ev c) :
    σ (.n 3191) = σ (.n 3187) + σ (.n 1346) * vtSlots W ev 0
      [[], [], [([12], 3)], [], [], [], [], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 3038 [
    .atom (.const (.n 3078) (word 3 0)),
    .atom (.mul (.n 3079) (.n 3078) (.n 3024)),
    .atom (.copy (.n 3080) (.n 3079))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a3038, a3039, a3040, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 3148 [
    .atom (.load (.n 3188) (.n 13) 2),
    .atom (.mul (.n 3189) (.n 3188) (.n 3080)),
    .atom (.mul (.n 3190) (.n 1346) (.n 3189)),
    .atom (.add (.n 3191) (.n 3187) (.n 3190))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a3148, a3149, a3150, a3151, -⟩ := hs1
  have e3148 := tb_loadHolds_unique a3148 (hw 2 (by norm_num))
  have v3024 : σ (.n 3024) = ev 12 := by
    rw [← hev 12 (by norm_num)]; exact (vt_eval h (k := 25) (by norm_num)).2.2
  have hB : σ (.n 3189) = vtSlots W ev 0 [[], [], [([12], 3)], [], [], [], [], [], []] := by
    simp only [v3024, a3149, e3148, a3040, a3039, a3038]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a3151, a3150, hB]

set_option maxRecDepth 10000 in
theorem vtD1_2 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 13, σ (.n (vtEvB (13 + c))) = ev c) :
    σ (.n 3195) = σ (.n 3191) + σ (.n 1348) * vtSlots W ev 0
      [[], [], [([9], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 3041 [
    .atom (.const (.n 3081) (word 3 0)),
    .atom (.mul (.n 3082) (.n 3081) (.n 2999)),
    .atom (.copy (.n 3083) (.n 3082))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a3041, a3042, a3043, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 3152 [
    .atom (.load (.n 3192) (.n 13) 2),
    .atom (.mul (.n 3193) (.n 3192) (.n 3083)),
    .atom (.mul (.n 3194) (.n 1348) (.n 3193)),
    .atom (.add (.n 3195) (.n 3191) (.n 3194))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a3152, a3153, a3154, a3155, -⟩ := hs1
  have e3152 := tb_loadHolds_unique a3152 (hw 2 (by norm_num))
  have v2999 : σ (.n 2999) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 22) (by norm_num)).2.2
  have hB : σ (.n 3193) = vtSlots W ev 0 [[], [], [([9], 3)], [], []] := by
    simp only [v2999, a3153, e3152, a3043, a3042, a3041]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a3155, a3154, hB]

set_option maxRecDepth 10000 in
theorem vtD1_3 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 13, σ (.n (vtEvB (13 + c))) = ev c) :
    σ (.n 3199) = σ (.n 3195) + σ (.n 1350) * vtSlots W ev 0
      [[], [], [([10], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 3044 [
    .atom (.const (.n 3084) (word 3 0)),
    .atom (.mul (.n 3085) (.n 3084) (.n 3003)),
    .atom (.copy (.n 3086) (.n 3085))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a3044, a3045, a3046, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 3156 [
    .atom (.load (.n 3196) (.n 13) 2),
    .atom (.mul (.n 3197) (.n 3196) (.n 3086)),
    .atom (.mul (.n 3198) (.n 1350) (.n 3197)),
    .atom (.add (.n 3199) (.n 3195) (.n 3198))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a3156, a3157, a3158, a3159, -⟩ := hs1
  have e3156 := tb_loadHolds_unique a3156 (hw 2 (by norm_num))
  have v3003 : σ (.n 3003) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_eval h (k := 23) (by norm_num)).2.2
  have hB : σ (.n 3197) = vtSlots W ev 0 [[], [], [([10], 3)], [], []] := by
    simp only [v3003, a3157, e3156, a3046, a3045, a3044]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a3159, a3158, hB]

set_option maxRecDepth 10000 in
theorem vtD1_4 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 13, σ (.n (vtEvB (13 + c))) = ev c) :
    σ (.n 3203) = σ (.n 3199) + σ (.n 1352) * vtSlots W ev 0
      [[], [], [([11], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 3047 [
    .atom (.const (.n 3087) (word 3 0)),
    .atom (.mul (.n 3088) (.n 3087) (.n 3020)),
    .atom (.copy (.n 3089) (.n 3088))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a3047, a3048, a3049, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 3160 [
    .atom (.load (.n 3200) (.n 13) 2),
    .atom (.mul (.n 3201) (.n 3200) (.n 3089)),
    .atom (.mul (.n 3202) (.n 1352) (.n 3201)),
    .atom (.add (.n 3203) (.n 3199) (.n 3202))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a3160, a3161, a3162, a3163, -⟩ := hs1
  have e3160 := tb_loadHolds_unique a3160 (hw 2 (by norm_num))
  have v3020 : σ (.n 3020) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_eval h (k := 24) (by norm_num)).2.2
  have hB : σ (.n 3201) = vtSlots W ev 0 [[], [], [([11], 3)], [], []] := by
    simp only [v3020, a3161, e3160, a3049, a3048, a3047]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a3163, a3162, hB]

set_option maxRecDepth 10000 in
theorem vtSide11 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 13, σ (.n (vtEvB (13 + c))) = ev c) :
    σ (.n 3204) =
      vtSideVal [σ (.n 1344), σ (.n 1346), σ (.n 1348), σ (.n 1350), σ (.n 1352)]
        (σ (.n 14)) W ev vtBTerms11 := by
  have hF0 : σ (.n 3183) =
      vtSideVal [σ (.n 1344), σ (.n 1346), σ (.n 1348), σ (.n 1350), σ (.n 1352)]
        (σ (.n 14)) W ev vtBTerms01 := by
    rw [vtPullSels1 h]; exact vtSide01 h hw hev
  have a3164 := h.atomAt 3164 (.add (.n 3204) (.n 3183) (.n 3203)) (by decide +kernel)
  simp only [Atom.Holds] at a3164
  rw [vtSideVal_pull _ _ _ _ _ _ _ vtPull1, ← hF0, a3164, vtD1_4 h hw hev, vtD1_3 h hw hev, vtD1_2 h hw hev, vtD1_1 h hw hev, vtD1_0 h hw hev]
  simp only [vtDiffSum, vtDTerms1, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, add_zero, add_assoc]

set_option maxRecDepth 10000 in
theorem vtSide21 {rd : Reader} {σ : Val} (h : VtH rd σ) {ev : ℕ → E}
    (hev : ∀ c < 13, σ (.n (vtEvB (13 + c))) = ev c) :
    σ (.n 3213) =
      vtSideVal [σ (.n 1464), σ (.n 1473), σ (.n 1482), σ (.n 1491)]
        (0) (fun _ ↦ 1) ev vtBTerms21 := by
  obtain ⟨_, hs0⟩ := h.sliceAt 3050 [
    .atom (.copy (.n 3090) (.n 2999)),
    .atom (.copy (.n 3091) (.n 3003)),
    .atom (.copy (.n 3092) (.n 3020)),
    .atom (.copy (.n 3093) (.n 3024))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a3050, a3051, a3052, a3053, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 3167 [
    .atom (.mul (.n 3207) (.n 1464) (.n 3090)),
    .atom (.mul (.n 3208) (.n 1473) (.n 3091)),
    .atom (.add (.n 3209) (.n 3207) (.n 3208)),
    .atom (.mul (.n 3210) (.n 1482) (.n 3092)),
    .atom (.add (.n 3211) (.n 3209) (.n 3210)),
    .atom (.mul (.n 3212) (.n 1491) (.n 3093)),
    .atom (.add (.n 3213) (.n 3211) (.n 3212))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a3167, a3168, a3169, a3170, a3171, a3172, a3173, -⟩ := hs1
  have v2999 : σ (.n 2999) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 22) (by norm_num)).2.2
  have v3003 : σ (.n 3003) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_eval h (k := 23) (by norm_num)).2.2
  have v3020 : σ (.n 3020) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_eval h (k := 24) (by norm_num)).2.2
  have v3024 : σ (.n 3024) = ev 12 := by
    rw [← hev 12 (by norm_num)]; exact (vt_eval h (k := 25) (by norm_num)).2.2
  simp only [v3024, v3020, v3003, v2999, a3173, a3172, a3171, a3170, a3169, a3168, a3167, a3053, a3052, a3051,
    a3050]
  simp only [vtSideVal, vtBTerms21, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, vt_ofK_ofBits_one]
  ring

end
end LeanVM.Guest.B1.Tables
