/-
  LeanVM.Guest.B1.Tables.VtC.FForms0

  `Vt/FormsT0.lean` on the window `VtF` (generated: scripts/b1c-vt/gentwins.py).
-/

module

public import LeanVM.Guest.B1.Tables.VtC.FEvals
public import LeanVM.Guest.B1.Tables.Vt.FormsT0

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

set_option maxRecDepth 10000 in
theorem vtB00_0F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (0 + c))) = ev c) :
    σ (.n 2845) = σ (.n 960) * vtBlockVal (σ (.n 14)) W ev
      [[([], 1)], [([0], 2)], [([1], 1)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 2841 [
    .atom (.load (.n 2835) (.n 13) 0),
    .atom (.const (.n 2836) (word 2 0 0)),
    .atom (.mul (.n 2837) (.n 2836) (.n 2641)),
    .atom (.load (.n 2838) (.n 13) 1),
    .atom (.mul (.n 2839) (.n 2838) (.n 2837)),
    .atom (.add (.n 2840) (.n 2835) (.n 2839)),
    .atom (.load (.n 2841) (.n 13) 2),
    .atom (.mul (.n 2842) (.n 2841) (.n 2652)),
    .atom (.add (.n 2843) (.n 2840) (.n 2842)),
    .atom (.add (.n 2844) (.n 14) (.n 2843)),
    .atom (.mul (.n 2845) (.n 960) (.n 2844))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a2841, a2842, a2843, a2844, a2845, a2846, a2847, a2848, a2849, a2850, a2851, -⟩ := hs
  have e2841 := tb_loadHolds_unique a2841 (hw 0 (by norm_num))
  have e2844 := tb_loadHolds_unique a2844 (hw 1 (by norm_num))
  have e2847 := tb_loadHolds_unique a2847 (hw 2 (by norm_num))
  have v2641 : σ (.n 2641) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_evalF h (k := 0) (by norm_num)).2.2
  have v2652 : σ (.n 2652) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 1) (by norm_num)).2.2
  have hB : σ (.n 2844) = vtBlockVal (σ (.n 14)) W ev [[([], 1)], [([0], 2)], [([1], 1)]] := by
    simp only [v2652, v2641, a2850, a2849, a2848, e2847, a2846, a2845, e2844, a2843, a2842, e2841]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a2851, hB]

set_option maxRecDepth 10000 in
theorem vtB00_1F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (0 + c))) = ev c) :
    σ (.n 2878) = σ (.n 2845) + σ (.n 965) * vtBlockVal (σ (.n 14)) W ev
      [[([], 4)], [([0], 1)], [([14], 2)], [([], 1)], [([2], 1)], [([3], 1)], [([4], 1)], [([], 0)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 2852 [
    .atom (.load (.n 2846) (.n 13) 0),
    .atom (.const (.n 2847) (word 4 0 0)),
    .atom (.mul (.n 2848) (.n 2846) (.n 2847)),
    .atom (.load (.n 2849) (.n 13) 1),
    .atom (.mul (.n 2850) (.n 2849) (.n 2641)),
    .atom (.add (.n 2851) (.n 2848) (.n 2850)),
    .atom (.const (.n 2852) (word 2 0 0)),
    .atom (.mul (.n 2853) (.n 2852) (.n 2834)),
    .atom (.load (.n 2854) (.n 13) 2),
    .atom (.mul (.n 2855) (.n 2854) (.n 2853)),
    .atom (.add (.n 2856) (.n 2851) (.n 2855)),
    .atom (.load (.n 2857) (.n 13) 3),
    .atom (.add (.n 2858) (.n 2856) (.n 2857)),
    .atom (.load (.n 2859) (.n 13) 4),
    .atom (.mul (.n 2860) (.n 2859) (.n 2663)),
    .atom (.add (.n 2861) (.n 2858) (.n 2860)),
    .atom (.load (.n 2862) (.n 13) 5),
    .atom (.mul (.n 2863) (.n 2862) (.n 2674)),
    .atom (.add (.n 2864) (.n 2861) (.n 2863)),
    .atom (.load (.n 2865) (.n 13) 6),
    .atom (.mul (.n 2866) (.n 2865) (.n 2698)),
    .atom (.add (.n 2867) (.n 2864) (.n 2866)),
    .atom (.load (.n 2868) (.n 13) 7),
    .atom (.const (.n 2869) (word 0 0 0)),
    .atom (.mul (.n 2870) (.n 2868) (.n 2869)),
    .atom (.add (.n 2871) (.n 2867) (.n 2870)),
    .atom (.load (.n 2872) (.n 13) 8),
    .atom (.const (.n 2873) (word 0 0 0)),
    .atom (.mul (.n 2874) (.n 2872) (.n 2873)),
    .atom (.add (.n 2875) (.n 2871) (.n 2874)),
    .atom (.add (.n 2876) (.n 14) (.n 2875)),
    .atom (.mul (.n 2877) (.n 965) (.n 2876)),
    .atom (.add (.n 2878) (.n 2845) (.n 2877))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a2852, a2853, a2854, a2855, a2856, a2857, a2858, a2859, a2860, a2861, a2862, a2863, a2864, a2865,
    a2866, a2867, a2868, a2869, a2870, a2871, a2872, a2873, a2874, a2875, a2876, a2877, a2878,
    a2879, a2880, a2881, a2882, a2883, a2884, -⟩ := hs
  have e2852 := tb_loadHolds_unique a2852 (hw 0 (by norm_num))
  have e2855 := tb_loadHolds_unique a2855 (hw 1 (by norm_num))
  have e2860 := tb_loadHolds_unique a2860 (hw 2 (by norm_num))
  have e2863 := tb_loadHolds_unique a2863 (hw 3 (by norm_num))
  have e2865 := tb_loadHolds_unique a2865 (hw 4 (by norm_num))
  have e2868 := tb_loadHolds_unique a2868 (hw 5 (by norm_num))
  have e2871 := tb_loadHolds_unique a2871 (hw 6 (by norm_num))
  have e2874 := tb_loadHolds_unique a2874 (hw 7 (by norm_num))
  have e2878 := tb_loadHolds_unique a2878 (hw 8 (by norm_num))
  have v2641 : σ (.n 2641) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_evalF h (k := 0) (by norm_num)).2.2
  have v2663 : σ (.n 2663) = ev 2 := by
    rw [← hev 2 (by norm_num)]; exact (vt_evalF h (k := 2) (by norm_num)).2.2
  have v2674 : σ (.n 2674) = ev 3 := by
    rw [← hev 3 (by norm_num)]; exact (vt_evalF h (k := 3) (by norm_num)).2.2
  have v2698 : σ (.n 2698) = ev 4 := by
    rw [← hev 4 (by norm_num)]; exact (vt_evalF h (k := 4) (by norm_num)).2.2
  have v2834 : σ (.n 2834) = ev 14 := by
    rw [← hev 14 (by norm_num)]; exact (vt_evalF h (k := 14) (by norm_num)).2.2
  have hB : σ (.n 2876) = vtBlockVal (σ (.n 14)) W ev [[([], 4)], [([0], 1)], [([14], 2)], [([], 1)], [([2], 1)], [([3], 1)], [([4], 1)], [([], 0)], [([], 0)]] := by
    simp only [v2834, v2698, v2674, v2663, v2641, a2882, a2881, a2880, a2879, e2878, a2877, a2876, a2875,
      e2874, a2873, a2872, e2871, a2870, a2869, e2868, a2867, a2866, e2865, a2864, e2863,
      a2862, a2861, e2860, a2859, a2858, a2857, a2856, e2855, a2854, a2853, e2852]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a2884, a2883, hB]

set_option maxRecDepth 10000 in
theorem vtB00_2F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (0 + c))) = ev c) :
    σ (.n 2902) = σ (.n 2878) + σ (.n 970) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 2], 1)], [([11], 2)], [([5], 1)], [([6], 1)], [([7], 1)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 2885 [
    .atom (.load (.n 2879) (.n 13) 0),
    .atom (.const (.n 2880) (word 2 0 0)),
    .atom (.mul (.n 2881) (.n 2879) (.n 2880)),
    .atom (.mul (.n 2882) (.n 2652) (.n 2663)),
    .atom (.load (.n 2883) (.n 13) 1),
    .atom (.mul (.n 2884) (.n 2883) (.n 2882)),
    .atom (.add (.n 2885) (.n 2881) (.n 2884)),
    .atom (.const (.n 2886) (word 2 0 0)),
    .atom (.mul (.n 2887) (.n 2886) (.n 2788)),
    .atom (.load (.n 2888) (.n 13) 2),
    .atom (.mul (.n 2889) (.n 2888) (.n 2887)),
    .atom (.add (.n 2890) (.n 2885) (.n 2889)),
    .atom (.load (.n 2891) (.n 13) 3),
    .atom (.mul (.n 2892) (.n 2891) (.n 2709)),
    .atom (.add (.n 2893) (.n 2890) (.n 2892)),
    .atom (.load (.n 2894) (.n 13) 4),
    .atom (.mul (.n 2895) (.n 2894) (.n 2720)),
    .atom (.add (.n 2896) (.n 2893) (.n 2895)),
    .atom (.load (.n 2897) (.n 13) 5),
    .atom (.mul (.n 2898) (.n 2897) (.n 2731)),
    .atom (.add (.n 2899) (.n 2896) (.n 2898)),
    .atom (.add (.n 2900) (.n 14) (.n 2899)),
    .atom (.mul (.n 2901) (.n 970) (.n 2900)),
    .atom (.add (.n 2902) (.n 2878) (.n 2901))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a2885, a2886, a2887, a2888, a2889, a2890, a2891, a2892, a2893, a2894, a2895, a2896, a2897, a2898,
    a2899, a2900, a2901, a2902, a2903, a2904, a2905, a2906, a2907, a2908, -⟩ := hs
  have e2885 := tb_loadHolds_unique a2885 (hw 0 (by norm_num))
  have e2889 := tb_loadHolds_unique a2889 (hw 1 (by norm_num))
  have e2894 := tb_loadHolds_unique a2894 (hw 2 (by norm_num))
  have e2897 := tb_loadHolds_unique a2897 (hw 3 (by norm_num))
  have e2900 := tb_loadHolds_unique a2900 (hw 4 (by norm_num))
  have e2903 := tb_loadHolds_unique a2903 (hw 5 (by norm_num))
  have v2652 : σ (.n 2652) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 1) (by norm_num)).2.2
  have v2663 : σ (.n 2663) = ev 2 := by
    rw [← hev 2 (by norm_num)]; exact (vt_evalF h (k := 2) (by norm_num)).2.2
  have v2709 : σ (.n 2709) = ev 5 := by
    rw [← hev 5 (by norm_num)]; exact (vt_evalF h (k := 5) (by norm_num)).2.2
  have v2720 : σ (.n 2720) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_evalF h (k := 6) (by norm_num)).2.2
  have v2731 : σ (.n 2731) = ev 7 := by
    rw [← hev 7 (by norm_num)]; exact (vt_evalF h (k := 7) (by norm_num)).2.2
  have v2788 : σ (.n 2788) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_evalF h (k := 11) (by norm_num)).2.2
  have hB : σ (.n 2900) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 2], 1)], [([11], 2)], [([5], 1)], [([6], 1)], [([7], 1)]] := by
    simp only [v2788, v2731, v2720, v2709, v2663, v2652, a2906, a2905, a2904, e2903, a2902, a2901, e2900,
      a2899, a2898, e2897, a2896, a2895, e2894, a2893, a2892, a2891, a2890, e2889, a2888,
      a2887, a2886, e2885]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a2908, a2907, hB]

set_option maxRecDepth 10000 in
theorem vtB00_3F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (0 + c))) = ev c) :
    σ (.n 2926) = σ (.n 2902) + σ (.n 975) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 3], 1)], [([12], 2)], [([8], 1)], [([9], 1)], [([10], 1)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 2909 [
    .atom (.load (.n 2903) (.n 13) 0),
    .atom (.const (.n 2904) (word 2 0 0)),
    .atom (.mul (.n 2905) (.n 2903) (.n 2904)),
    .atom (.mul (.n 2906) (.n 2652) (.n 2674)),
    .atom (.load (.n 2907) (.n 13) 1),
    .atom (.mul (.n 2908) (.n 2907) (.n 2906)),
    .atom (.add (.n 2909) (.n 2905) (.n 2908)),
    .atom (.const (.n 2910) (word 2 0 0)),
    .atom (.mul (.n 2911) (.n 2910) (.n 2812)),
    .atom (.load (.n 2912) (.n 13) 2),
    .atom (.mul (.n 2913) (.n 2912) (.n 2911)),
    .atom (.add (.n 2914) (.n 2909) (.n 2913)),
    .atom (.load (.n 2915) (.n 13) 3),
    .atom (.mul (.n 2916) (.n 2915) (.n 2755)),
    .atom (.add (.n 2917) (.n 2914) (.n 2916)),
    .atom (.load (.n 2918) (.n 13) 4),
    .atom (.mul (.n 2919) (.n 2918) (.n 2766)),
    .atom (.add (.n 2920) (.n 2917) (.n 2919)),
    .atom (.load (.n 2921) (.n 13) 5),
    .atom (.mul (.n 2922) (.n 2921) (.n 2777)),
    .atom (.add (.n 2923) (.n 2920) (.n 2922)),
    .atom (.add (.n 2924) (.n 14) (.n 2923)),
    .atom (.mul (.n 2925) (.n 975) (.n 2924)),
    .atom (.add (.n 2926) (.n 2902) (.n 2925))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a2909, a2910, a2911, a2912, a2913, a2914, a2915, a2916, a2917, a2918, a2919, a2920, a2921, a2922,
    a2923, a2924, a2925, a2926, a2927, a2928, a2929, a2930, a2931, a2932, -⟩ := hs
  have e2909 := tb_loadHolds_unique a2909 (hw 0 (by norm_num))
  have e2913 := tb_loadHolds_unique a2913 (hw 1 (by norm_num))
  have e2918 := tb_loadHolds_unique a2918 (hw 2 (by norm_num))
  have e2921 := tb_loadHolds_unique a2921 (hw 3 (by norm_num))
  have e2924 := tb_loadHolds_unique a2924 (hw 4 (by norm_num))
  have e2927 := tb_loadHolds_unique a2927 (hw 5 (by norm_num))
  have v2652 : σ (.n 2652) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 1) (by norm_num)).2.2
  have v2674 : σ (.n 2674) = ev 3 := by
    rw [← hev 3 (by norm_num)]; exact (vt_evalF h (k := 3) (by norm_num)).2.2
  have v2755 : σ (.n 2755) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_evalF h (k := 8) (by norm_num)).2.2
  have v2766 : σ (.n 2766) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_evalF h (k := 9) (by norm_num)).2.2
  have v2777 : σ (.n 2777) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_evalF h (k := 10) (by norm_num)).2.2
  have v2812 : σ (.n 2812) = ev 12 := by
    rw [← hev 12 (by norm_num)]; exact (vt_evalF h (k := 12) (by norm_num)).2.2
  have hB : σ (.n 2924) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 3], 1)], [([12], 2)], [([8], 1)], [([9], 1)], [([10], 1)]] := by
    simp only [v2812, v2777, v2766, v2755, v2674, v2652, a2930, a2929, a2928, e2927, a2926, a2925, e2924,
      a2923, a2922, e2921, a2920, a2919, e2918, a2917, a2916, a2915, a2914, e2913, a2912,
      a2911, a2910, e2909]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a2932, a2931, hB]

set_option maxRecDepth 10000 in
theorem vtB00_4F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (0 + c))) = ev c) :
    σ (.n 2953) = σ (.n 2926) + σ (.n 980) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 4], 1)], [([13], 2)], [([5], 1), ([8], 1)], [([6], 1), ([9], 1)], [([7], 1), ([10], 1)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 2933 [
    .atom (.load (.n 2927) (.n 13) 0),
    .atom (.const (.n 2928) (word 2 0 0)),
    .atom (.mul (.n 2929) (.n 2927) (.n 2928)),
    .atom (.mul (.n 2930) (.n 2652) (.n 2698)),
    .atom (.load (.n 2931) (.n 13) 1),
    .atom (.mul (.n 2932) (.n 2931) (.n 2930)),
    .atom (.add (.n 2933) (.n 2929) (.n 2932)),
    .atom (.const (.n 2934) (word 2 0 0)),
    .atom (.mul (.n 2935) (.n 2934) (.n 2823)),
    .atom (.load (.n 2936) (.n 13) 2),
    .atom (.mul (.n 2937) (.n 2936) (.n 2935)),
    .atom (.add (.n 2938) (.n 2933) (.n 2937)),
    .atom (.add (.n 2939) (.n 2709) (.n 2755)),
    .atom (.load (.n 2940) (.n 13) 3),
    .atom (.mul (.n 2941) (.n 2940) (.n 2939)),
    .atom (.add (.n 2942) (.n 2938) (.n 2941)),
    .atom (.add (.n 2943) (.n 2720) (.n 2766)),
    .atom (.load (.n 2944) (.n 13) 4),
    .atom (.mul (.n 2945) (.n 2944) (.n 2943)),
    .atom (.add (.n 2946) (.n 2942) (.n 2945)),
    .atom (.add (.n 2947) (.n 2731) (.n 2777)),
    .atom (.load (.n 2948) (.n 13) 5),
    .atom (.mul (.n 2949) (.n 2948) (.n 2947)),
    .atom (.add (.n 2950) (.n 2946) (.n 2949)),
    .atom (.add (.n 2951) (.n 14) (.n 2950)),
    .atom (.mul (.n 2952) (.n 980) (.n 2951)),
    .atom (.add (.n 2953) (.n 2926) (.n 2952))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a2933, a2934, a2935, a2936, a2937, a2938, a2939, a2940, a2941, a2942, a2943, a2944, a2945, a2946,
    a2947, a2948, a2949, a2950, a2951, a2952, a2953, a2954, a2955, a2956, a2957, a2958, a2959, -⟩ := hs
  have e2933 := tb_loadHolds_unique a2933 (hw 0 (by norm_num))
  have e2937 := tb_loadHolds_unique a2937 (hw 1 (by norm_num))
  have e2942 := tb_loadHolds_unique a2942 (hw 2 (by norm_num))
  have e2946 := tb_loadHolds_unique a2946 (hw 3 (by norm_num))
  have e2950 := tb_loadHolds_unique a2950 (hw 4 (by norm_num))
  have e2954 := tb_loadHolds_unique a2954 (hw 5 (by norm_num))
  have v2652 : σ (.n 2652) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 1) (by norm_num)).2.2
  have v2698 : σ (.n 2698) = ev 4 := by
    rw [← hev 4 (by norm_num)]; exact (vt_evalF h (k := 4) (by norm_num)).2.2
  have v2709 : σ (.n 2709) = ev 5 := by
    rw [← hev 5 (by norm_num)]; exact (vt_evalF h (k := 5) (by norm_num)).2.2
  have v2720 : σ (.n 2720) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_evalF h (k := 6) (by norm_num)).2.2
  have v2731 : σ (.n 2731) = ev 7 := by
    rw [← hev 7 (by norm_num)]; exact (vt_evalF h (k := 7) (by norm_num)).2.2
  have v2755 : σ (.n 2755) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_evalF h (k := 8) (by norm_num)).2.2
  have v2766 : σ (.n 2766) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_evalF h (k := 9) (by norm_num)).2.2
  have v2777 : σ (.n 2777) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_evalF h (k := 10) (by norm_num)).2.2
  have v2823 : σ (.n 2823) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_evalF h (k := 13) (by norm_num)).2.2
  have hB : σ (.n 2951) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 4], 1)], [([13], 2)], [([5], 1), ([8], 1)], [([6], 1), ([9], 1)], [([7], 1), ([10], 1)]] := by
    simp only [v2823, v2777, v2766, v2755, v2731, v2720, v2709, v2698, v2652, a2957, a2956, a2955, e2954,
      a2953, a2952, a2951, e2950, a2949, a2948, a2947, e2946, a2945, a2944, a2943, e2942,
      a2941, a2940, a2939, a2938, e2937, a2936, a2935, a2934, e2933]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a2959, a2958, hB]

set_option maxRecDepth 10000 in
theorem vtSide00F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (0 + c))) = ev c) :
    σ (.n 2953) =
      vtSideVal [σ (.n 960), σ (.n 965), σ (.n 970), σ (.n 975), σ (.n 980)]
        (σ (.n 14)) W ev vtBTerms00 := by
  rw [vtB00_4F h hw hev, vtB00_3F h hw hev, vtB00_2F h hw hev, vtB00_1F h hw hev, vtB00_0F h hw hev]
  simp only [vtSideVal, vtBTerms00, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, add_zero, add_assoc]

set_option maxRecDepth 10000 in
theorem vtD0_0F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (0 + c))) = ev c) :
    σ (.n 2959) = σ (.n 1968) * vtSlots W ev 0
      [[], [([0], 3)], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 2961 [
    .atom (.const (.n 2955) (word 3 0 0)),
    .atom (.mul (.n 2956) (.n 2955) (.n 2641)),
    .atom (.load (.n 2957) (.n 13) 1),
    .atom (.mul (.n 2958) (.n 2957) (.n 2956)),
    .atom (.mul (.n 2959) (.n 1968) (.n 2958))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a2961, a2962, a2963, a2964, a2965, -⟩ := hs
  have e2963 := tb_loadHolds_unique a2963 (hw 1 (by norm_num))
  have v2641 : σ (.n 2641) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_evalF h (k := 0) (by norm_num)).2.2
  have hB : σ (.n 2958) = vtSlots W ev 0 [[], [([0], 3)], []] := by
    simp only [v2641, a2964, e2963, a2962, a2961]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a2965, hB]

set_option maxRecDepth 10000 in
theorem vtD0_1F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (0 + c))) = ev c) :
    σ (.n 2965) = σ (.n 2959) + σ (.n 1970) * vtSlots W ev 0
      [[], [], [([14], 3)], [], [], [], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 2966 [
    .atom (.const (.n 2960) (word 3 0 0)),
    .atom (.mul (.n 2961) (.n 2960) (.n 2834)),
    .atom (.load (.n 2962) (.n 13) 2),
    .atom (.mul (.n 2963) (.n 2962) (.n 2961)),
    .atom (.mul (.n 2964) (.n 1970) (.n 2963)),
    .atom (.add (.n 2965) (.n 2959) (.n 2964))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a2966, a2967, a2968, a2969, a2970, a2971, -⟩ := hs
  have e2968 := tb_loadHolds_unique a2968 (hw 2 (by norm_num))
  have v2834 : σ (.n 2834) = ev 14 := by
    rw [← hev 14 (by norm_num)]; exact (vt_evalF h (k := 14) (by norm_num)).2.2
  have hB : σ (.n 2963) = vtSlots W ev 0 [[], [], [([14], 3)], [], [], [], [], [], []] := by
    simp only [v2834, a2969, e2968, a2967, a2966]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a2971, a2970, hB]

set_option maxRecDepth 10000 in
theorem vtD0_2F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (0 + c))) = ev c) :
    σ (.n 2971) = σ (.n 2965) + σ (.n 1972) * vtSlots W ev 0
      [[], [], [([11], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 2972 [
    .atom (.const (.n 2966) (word 3 0 0)),
    .atom (.mul (.n 2967) (.n 2966) (.n 2788)),
    .atom (.load (.n 2968) (.n 13) 2),
    .atom (.mul (.n 2969) (.n 2968) (.n 2967)),
    .atom (.mul (.n 2970) (.n 1972) (.n 2969)),
    .atom (.add (.n 2971) (.n 2965) (.n 2970))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a2972, a2973, a2974, a2975, a2976, a2977, -⟩ := hs
  have e2974 := tb_loadHolds_unique a2974 (hw 2 (by norm_num))
  have v2788 : σ (.n 2788) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_evalF h (k := 11) (by norm_num)).2.2
  have hB : σ (.n 2969) = vtSlots W ev 0 [[], [], [([11], 3)], [], [], []] := by
    simp only [v2788, a2975, e2974, a2973, a2972]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a2977, a2976, hB]

set_option maxRecDepth 10000 in
theorem vtD0_3F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (0 + c))) = ev c) :
    σ (.n 2977) = σ (.n 2971) + σ (.n 1974) * vtSlots W ev 0
      [[], [], [([12], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 2978 [
    .atom (.const (.n 2972) (word 3 0 0)),
    .atom (.mul (.n 2973) (.n 2972) (.n 2812)),
    .atom (.load (.n 2974) (.n 13) 2),
    .atom (.mul (.n 2975) (.n 2974) (.n 2973)),
    .atom (.mul (.n 2976) (.n 1974) (.n 2975)),
    .atom (.add (.n 2977) (.n 2971) (.n 2976))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a2978, a2979, a2980, a2981, a2982, a2983, -⟩ := hs
  have e2980 := tb_loadHolds_unique a2980 (hw 2 (by norm_num))
  have v2812 : σ (.n 2812) = ev 12 := by
    rw [← hev 12 (by norm_num)]; exact (vt_evalF h (k := 12) (by norm_num)).2.2
  have hB : σ (.n 2975) = vtSlots W ev 0 [[], [], [([12], 3)], [], [], []] := by
    simp only [v2812, a2981, e2980, a2979, a2978]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a2983, a2982, hB]

set_option maxRecDepth 10000 in
theorem vtD0_4F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (0 + c))) = ev c) :
    σ (.n 2983) = σ (.n 2977) + σ (.n 1976) * vtSlots W ev 0
      [[], [], [([13], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 2984 [
    .atom (.const (.n 2978) (word 3 0 0)),
    .atom (.mul (.n 2979) (.n 2978) (.n 2823)),
    .atom (.load (.n 2980) (.n 13) 2),
    .atom (.mul (.n 2981) (.n 2980) (.n 2979)),
    .atom (.mul (.n 2982) (.n 1976) (.n 2981)),
    .atom (.add (.n 2983) (.n 2977) (.n 2982))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a2984, a2985, a2986, a2987, a2988, a2989, -⟩ := hs
  have e2986 := tb_loadHolds_unique a2986 (hw 2 (by norm_num))
  have v2823 : σ (.n 2823) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_evalF h (k := 13) (by norm_num)).2.2
  have hB : σ (.n 2981) = vtSlots W ev 0 [[], [], [([13], 3)], [], [], []] := by
    simp only [v2823, a2987, e2986, a2985, a2984]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a2989, a2988, hB]

set_option maxRecDepth 10000 in
theorem vtSide10F {rd : Reader} {σ : Val} (h : VtF rd σ)
    (hq : [σ (.n 1968), σ (.n 1970), σ (.n 1972), σ (.n 1974), σ (.n 1976)] = [σ (.n 960), σ (.n 965), σ (.n 970), σ (.n 975), σ (.n 980)]) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 15, σ (.n (vtEvB (0 + c))) = ev c) :
    σ (.n 2984) =
      vtSideVal [σ (.n 1968), σ (.n 1970), σ (.n 1972), σ (.n 1974), σ (.n 1976)]
        (σ (.n 14)) W ev vtBTerms10 := by
  have hF0 : σ (.n 2953) =
      vtSideVal [σ (.n 1968), σ (.n 1970), σ (.n 1972), σ (.n 1974), σ (.n 1976)]
        (σ (.n 14)) W ev vtBTerms00 := by
    rw [hq]; exact vtSide00F h hw hev
  have a2990 := h.atomAt 2990 (.add (.n 2984) (.n 2953) (.n 2983)) (by decide +kernel)
  simp only [Atom.Holds] at a2990
  rw [vtSideVal_pull _ _ _ _ _ _ _ vtPull0, ← hF0, a2990, vtD0_4F h hw hev, vtD0_3F h hw hev, vtD0_2F h hw hev, vtD0_1F h hw hev, vtD0_0F h hw hev]
  simp only [vtDiffSum, vtDTerms0, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, add_zero, add_assoc]

set_option maxRecDepth 10000 in
theorem vtSide20F {rd : Reader} {σ : Val} (h : VtF rd σ) {ev : ℕ → E}
    (hev : ∀ c < 15, σ (.n (vtEvB (0 + c))) = ev c) :
    σ (.n 2993) =
      vtSideVal [σ (.n 2077), σ (.n 2082), σ (.n 2087), σ (.n 2092)]
        (0) (fun _ ↦ 1) ev vtBTerms20 := by
  obtain ⟨_, hs⟩ := h.sliceAt 2993 [
    .atom (.mul (.n 2987) (.n 2077) (.n 2788)),
    .atom (.mul (.n 2988) (.n 2082) (.n 2812)),
    .atom (.add (.n 2989) (.n 2987) (.n 2988)),
    .atom (.mul (.n 2990) (.n 2087) (.n 2823)),
    .atom (.add (.n 2991) (.n 2989) (.n 2990)),
    .atom (.mul (.n 2992) (.n 2092) (.n 2834)),
    .atom (.add (.n 2993) (.n 2991) (.n 2992))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a2993, a2994, a2995, a2996, a2997, a2998, a2999, -⟩ := hs
  have v2788 : σ (.n 2788) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_evalF h (k := 11) (by norm_num)).2.2
  have v2812 : σ (.n 2812) = ev 12 := by
    rw [← hev 12 (by norm_num)]; exact (vt_evalF h (k := 12) (by norm_num)).2.2
  have v2823 : σ (.n 2823) = ev 13 := by
    rw [← hev 13 (by norm_num)]; exact (vt_evalF h (k := 13) (by norm_num)).2.2
  have v2834 : σ (.n 2834) = ev 14 := by
    rw [← hev 14 (by norm_num)]; exact (vt_evalF h (k := 14) (by norm_num)).2.2
  rw [a2999, a2997, a2995, a2993, a2994, a2996, a2998, v2788, v2812, v2823, v2834]
  simp only [vtSideVal, vtBTerms20, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, vt_ofK_ofBits_one, zero_add,
    one_mul, mul_one, add_zero, add_assoc]

end
end LeanVM.Guest.B1.Tables
