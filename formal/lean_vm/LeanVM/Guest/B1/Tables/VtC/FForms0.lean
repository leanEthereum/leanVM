/-
  LeanVM.Guest.B1.Tables.VtC.FForms0

  `Vt/FormsT0.lean` on the window `VtF` (generated: scripts/b1c-vt/gentwins.py).

  Do not edit: `scripts/b1c-vt/all.py` writes it (`regen-guest.sh`, step `vt`).
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
    (hev : ∀ c < 13, σ (.n (vtEvB (0 + c))) = ev c) :
    σ (.n 2819) = σ (.n 858) * vtBlockVal (σ (.n 14)) W ev
      [[([], 1)], [([0], 2)], [([1], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 2745 [
    .atom (.const (.n 2749) (word 1 0)),
    .atom (.const (.n 2750) (word 2 0)),
    .atom (.mul (.n 2751) (.n 2750) (.n 2661)),
    .atom (.copy (.n 2752) (.n 2751)),
    .atom (.copy (.n 2753) (.n 2665))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a2745, a2746, a2747, a2748, a2749, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 2806 [
    .atom (.load (.n 2810) (.n 13) 0),
    .atom (.mul (.n 2811) (.n 2810) (.n 2749)),
    .atom (.load (.n 2812) (.n 13) 1),
    .atom (.mul (.n 2813) (.n 2812) (.n 2752)),
    .atom (.add (.n 2814) (.n 2811) (.n 2813)),
    .atom (.load (.n 2815) (.n 13) 2),
    .atom (.mul (.n 2816) (.n 2815) (.n 2753)),
    .atom (.add (.n 2817) (.n 2814) (.n 2816)),
    .atom (.add (.n 2818) (.n 14) (.n 2817)),
    .atom (.mul (.n 2819) (.n 858) (.n 2818))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a2806, a2807, a2808, a2809, a2810, a2811, a2812, a2813, a2814, a2815, -⟩ := hs1
  have e2806 := tb_loadHolds_unique a2806 (hw 0 (by norm_num))
  have e2808 := tb_loadHolds_unique a2808 (hw 1 (by norm_num))
  have e2811 := tb_loadHolds_unique a2811 (hw 2 (by norm_num))
  have v2661 : σ (.n 2661) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_evalF h (k := 0) (by norm_num)).2.2
  have v2665 : σ (.n 2665) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 1) (by norm_num)).2.2
  have hB : σ (.n 2818) = vtBlockVal (σ (.n 14)) W ev [[([], 1)], [([0], 2)], [([1], 1)]] := by
    simp only [v2665, v2661, a2814, a2813, a2812, e2811, a2810, a2809, e2808, a2807, e2806, a2749, a2748,
      a2747, a2746, a2745]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a2815, hB]

set_option maxRecDepth 10000 in
theorem vtB00_1F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 13, σ (.n (vtEvB (0 + c))) = ev c) :
    σ (.n 2848) = σ (.n 2819) + σ (.n 863) * vtBlockVal (σ (.n 14)) W ev
      [[([], 4)], [([0], 1)], [([12], 2)], [([], 1)], [([2], 1)], [([3], 1)], [([4], 1)], [([], 0)], [([], 0)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 2750 [
    .atom (.const (.n 2754) (word 4 0)),
    .atom (.copy (.n 2755) (.n 2661)),
    .atom (.const (.n 2756) (word 2 0)),
    .atom (.mul (.n 2757) (.n 2756) (.n 2748)),
    .atom (.copy (.n 2758) (.n 2757)),
    .atom (.const (.n 2759) (word 1 0)),
    .atom (.copy (.n 2760) (.n 2669)),
    .atom (.copy (.n 2761) (.n 2673)),
    .atom (.copy (.n 2762) (.n 2690)),
    .atom (.const (.n 2763) (word 0 0)),
    .atom (.const (.n 2764) (word 0 0))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a2750, a2751, a2752, a2753, a2754, a2755, a2756, a2757, a2758, a2759, a2760, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 2816 [
    .atom (.load (.n 2820) (.n 13) 0),
    .atom (.mul (.n 2821) (.n 2820) (.n 2754)),
    .atom (.load (.n 2822) (.n 13) 1),
    .atom (.mul (.n 2823) (.n 2822) (.n 2755)),
    .atom (.add (.n 2824) (.n 2821) (.n 2823)),
    .atom (.load (.n 2825) (.n 13) 2),
    .atom (.mul (.n 2826) (.n 2825) (.n 2758)),
    .atom (.add (.n 2827) (.n 2824) (.n 2826)),
    .atom (.load (.n 2828) (.n 13) 3),
    .atom (.mul (.n 2829) (.n 2828) (.n 2759)),
    .atom (.add (.n 2830) (.n 2827) (.n 2829)),
    .atom (.load (.n 2831) (.n 13) 4),
    .atom (.mul (.n 2832) (.n 2831) (.n 2760)),
    .atom (.add (.n 2833) (.n 2830) (.n 2832)),
    .atom (.load (.n 2834) (.n 13) 5),
    .atom (.mul (.n 2835) (.n 2834) (.n 2761)),
    .atom (.add (.n 2836) (.n 2833) (.n 2835)),
    .atom (.load (.n 2837) (.n 13) 6),
    .atom (.mul (.n 2838) (.n 2837) (.n 2762)),
    .atom (.add (.n 2839) (.n 2836) (.n 2838)),
    .atom (.load (.n 2840) (.n 13) 7),
    .atom (.mul (.n 2841) (.n 2840) (.n 2763)),
    .atom (.add (.n 2842) (.n 2839) (.n 2841)),
    .atom (.load (.n 2843) (.n 13) 8),
    .atom (.mul (.n 2844) (.n 2843) (.n 2764)),
    .atom (.add (.n 2845) (.n 2842) (.n 2844)),
    .atom (.add (.n 2846) (.n 14) (.n 2845)),
    .atom (.mul (.n 2847) (.n 863) (.n 2846)),
    .atom (.add (.n 2848) (.n 2819) (.n 2847))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a2816, a2817, a2818, a2819, a2820, a2821, a2822, a2823, a2824, a2825, a2826, a2827, a2828, a2829,
    a2830, a2831, a2832, a2833, a2834, a2835, a2836, a2837, a2838, a2839, a2840, a2841, a2842,
    a2843, a2844, -⟩ := hs1
  have e2816 := tb_loadHolds_unique a2816 (hw 0 (by norm_num))
  have e2818 := tb_loadHolds_unique a2818 (hw 1 (by norm_num))
  have e2821 := tb_loadHolds_unique a2821 (hw 2 (by norm_num))
  have e2824 := tb_loadHolds_unique a2824 (hw 3 (by norm_num))
  have e2827 := tb_loadHolds_unique a2827 (hw 4 (by norm_num))
  have e2830 := tb_loadHolds_unique a2830 (hw 5 (by norm_num))
  have e2833 := tb_loadHolds_unique a2833 (hw 6 (by norm_num))
  have e2836 := tb_loadHolds_unique a2836 (hw 7 (by norm_num))
  have e2839 := tb_loadHolds_unique a2839 (hw 8 (by norm_num))
  have v2661 : σ (.n 2661) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_evalF h (k := 0) (by norm_num)).2.2
  have v2669 : σ (.n 2669) = ev 2 := by
    rw [← hev 2 (by norm_num)]; exact (vt_evalF h (k := 2) (by norm_num)).2.2
  have v2673 : σ (.n 2673) = ev 3 := by
    rw [← hev 3 (by norm_num)]; exact (vt_evalF h (k := 3) (by norm_num)).2.2
  have v2690 : σ (.n 2690) = ev 4 := by
    rw [← hev 4 (by norm_num)]; exact (vt_evalF h (k := 4) (by norm_num)).2.2
  have v2748 : σ (.n 2748) = ev 12 := by
    rw [← hev 12 (by norm_num)]; exact (vt_evalF h (k := 12) (by norm_num)).2.2
  have hB : σ (.n 2846) = vtBlockVal (σ (.n 14)) W ev [[([], 4)], [([0], 1)], [([12], 2)], [([], 1)], [([2], 1)], [([3], 1)], [([4], 1)], [([], 0)], [([], 0)]] := by
    simp only [v2748, v2690, v2673, v2669, v2661, a2842, a2841, a2840, e2839, a2838, a2837, e2836, a2835,
      a2834, e2833, a2832, a2831, e2830, a2829, a2828, e2827, a2826, a2825, e2824, a2823,
      a2822, e2821, a2820, a2819, e2818, a2817, e2816, a2760, a2759, a2758, a2757, a2756,
      a2755, a2754, a2753, a2752, a2751, a2750]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a2844, a2843, hB]

set_option maxRecDepth 10000 in
theorem vtB00_2F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 13, σ (.n (vtEvB (0 + c))) = ev c) :
    σ (.n 2865) = σ (.n 2848) + σ (.n 868) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 2], 1)], [([9], 2)], [([5], 1)], [([6], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 2761 [
    .atom (.const (.n 2765) (word 2 0)),
    .atom (.mul (.n 2766) (.n 2665) (.n 2669)),
    .atom (.copy (.n 2767) (.n 2766)),
    .atom (.const (.n 2768) (word 2 0)),
    .atom (.mul (.n 2769) (.n 2768) (.n 2723)),
    .atom (.copy (.n 2770) (.n 2769)),
    .atom (.copy (.n 2771) (.n 2694)),
    .atom (.copy (.n 2772) (.n 2698))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a2761, a2762, a2763, a2764, a2765, a2766, a2767, a2768, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 2845 [
    .atom (.load (.n 2849) (.n 13) 0),
    .atom (.mul (.n 2850) (.n 2849) (.n 2765)),
    .atom (.load (.n 2851) (.n 13) 1),
    .atom (.mul (.n 2852) (.n 2851) (.n 2767)),
    .atom (.add (.n 2853) (.n 2850) (.n 2852)),
    .atom (.load (.n 2854) (.n 13) 2),
    .atom (.mul (.n 2855) (.n 2854) (.n 2770)),
    .atom (.add (.n 2856) (.n 2853) (.n 2855)),
    .atom (.load (.n 2857) (.n 13) 3),
    .atom (.mul (.n 2858) (.n 2857) (.n 2771)),
    .atom (.add (.n 2859) (.n 2856) (.n 2858)),
    .atom (.load (.n 2860) (.n 13) 4),
    .atom (.mul (.n 2861) (.n 2860) (.n 2772)),
    .atom (.add (.n 2862) (.n 2859) (.n 2861)),
    .atom (.add (.n 2863) (.n 14) (.n 2862)),
    .atom (.mul (.n 2864) (.n 868) (.n 2863)),
    .atom (.add (.n 2865) (.n 2848) (.n 2864))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a2845, a2846, a2847, a2848, a2849, a2850, a2851, a2852, a2853, a2854, a2855, a2856, a2857, a2858,
    a2859, a2860, a2861, -⟩ := hs1
  have e2845 := tb_loadHolds_unique a2845 (hw 0 (by norm_num))
  have e2847 := tb_loadHolds_unique a2847 (hw 1 (by norm_num))
  have e2850 := tb_loadHolds_unique a2850 (hw 2 (by norm_num))
  have e2853 := tb_loadHolds_unique a2853 (hw 3 (by norm_num))
  have e2856 := tb_loadHolds_unique a2856 (hw 4 (by norm_num))
  have v2665 : σ (.n 2665) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 1) (by norm_num)).2.2
  have v2669 : σ (.n 2669) = ev 2 := by
    rw [← hev 2 (by norm_num)]; exact (vt_evalF h (k := 2) (by norm_num)).2.2
  have v2694 : σ (.n 2694) = ev 5 := by
    rw [← hev 5 (by norm_num)]; exact (vt_evalF h (k := 5) (by norm_num)).2.2
  have v2698 : σ (.n 2698) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_evalF h (k := 6) (by norm_num)).2.2
  have v2723 : σ (.n 2723) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_evalF h (k := 9) (by norm_num)).2.2
  have hB : σ (.n 2863) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 2], 1)], [([9], 2)], [([5], 1)], [([6], 1)]] := by
    simp only [v2723, v2698, v2694, v2669, v2665, a2859, a2858, a2857, e2856, a2855, a2854, e2853, a2852,
      a2851, e2850, a2849, a2848, e2847, a2846, e2845, a2768, a2767, a2766, a2765, a2764,
      a2763, a2762, a2761]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a2861, a2860, hB]

set_option maxRecDepth 10000 in
theorem vtB00_3F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 13, σ (.n (vtEvB (0 + c))) = ev c) :
    σ (.n 2882) = σ (.n 2865) + σ (.n 873) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 3], 1)], [([10], 2)], [([7], 1)], [([8], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 2769 [
    .atom (.const (.n 2773) (word 2 0)),
    .atom (.mul (.n 2774) (.n 2665) (.n 2673)),
    .atom (.copy (.n 2775) (.n 2774)),
    .atom (.const (.n 2776) (word 2 0)),
    .atom (.mul (.n 2777) (.n 2776) (.n 2727)),
    .atom (.copy (.n 2778) (.n 2777)),
    .atom (.copy (.n 2779) (.n 2702)),
    .atom (.copy (.n 2780) (.n 2719))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a2769, a2770, a2771, a2772, a2773, a2774, a2775, a2776, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 2862 [
    .atom (.load (.n 2866) (.n 13) 0),
    .atom (.mul (.n 2867) (.n 2866) (.n 2773)),
    .atom (.load (.n 2868) (.n 13) 1),
    .atom (.mul (.n 2869) (.n 2868) (.n 2775)),
    .atom (.add (.n 2870) (.n 2867) (.n 2869)),
    .atom (.load (.n 2871) (.n 13) 2),
    .atom (.mul (.n 2872) (.n 2871) (.n 2778)),
    .atom (.add (.n 2873) (.n 2870) (.n 2872)),
    .atom (.load (.n 2874) (.n 13) 3),
    .atom (.mul (.n 2875) (.n 2874) (.n 2779)),
    .atom (.add (.n 2876) (.n 2873) (.n 2875)),
    .atom (.load (.n 2877) (.n 13) 4),
    .atom (.mul (.n 2878) (.n 2877) (.n 2780)),
    .atom (.add (.n 2879) (.n 2876) (.n 2878)),
    .atom (.add (.n 2880) (.n 14) (.n 2879)),
    .atom (.mul (.n 2881) (.n 873) (.n 2880)),
    .atom (.add (.n 2882) (.n 2865) (.n 2881))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a2862, a2863, a2864, a2865, a2866, a2867, a2868, a2869, a2870, a2871, a2872, a2873, a2874, a2875,
    a2876, a2877, a2878, -⟩ := hs1
  have e2862 := tb_loadHolds_unique a2862 (hw 0 (by norm_num))
  have e2864 := tb_loadHolds_unique a2864 (hw 1 (by norm_num))
  have e2867 := tb_loadHolds_unique a2867 (hw 2 (by norm_num))
  have e2870 := tb_loadHolds_unique a2870 (hw 3 (by norm_num))
  have e2873 := tb_loadHolds_unique a2873 (hw 4 (by norm_num))
  have v2665 : σ (.n 2665) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 1) (by norm_num)).2.2
  have v2673 : σ (.n 2673) = ev 3 := by
    rw [← hev 3 (by norm_num)]; exact (vt_evalF h (k := 3) (by norm_num)).2.2
  have v2702 : σ (.n 2702) = ev 7 := by
    rw [← hev 7 (by norm_num)]; exact (vt_evalF h (k := 7) (by norm_num)).2.2
  have v2719 : σ (.n 2719) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_evalF h (k := 8) (by norm_num)).2.2
  have v2727 : σ (.n 2727) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_evalF h (k := 10) (by norm_num)).2.2
  have hB : σ (.n 2880) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 3], 1)], [([10], 2)], [([7], 1)], [([8], 1)]] := by
    simp only [v2727, v2719, v2702, v2673, v2665, a2876, a2875, a2874, e2873, a2872, a2871, e2870, a2869,
      a2868, e2867, a2866, a2865, e2864, a2863, e2862, a2776, a2775, a2774, a2773, a2772,
      a2771, a2770, a2769]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a2878, a2877, hB]

set_option maxRecDepth 10000 in
theorem vtB00_4F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 13, σ (.n (vtEvB (0 + c))) = ev c) :
    σ (.n 2899) = σ (.n 2882) + σ (.n 878) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 4], 1)], [([11], 2)], [([5], 1), ([7], 1)], [([6], 1), ([8], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 2777 [
    .atom (.const (.n 2781) (word 2 0)),
    .atom (.mul (.n 2782) (.n 2665) (.n 2690)),
    .atom (.copy (.n 2783) (.n 2782)),
    .atom (.const (.n 2784) (word 2 0)),
    .atom (.mul (.n 2785) (.n 2784) (.n 2731)),
    .atom (.copy (.n 2786) (.n 2785)),
    .atom (.add (.n 2787) (.n 2694) (.n 2702)),
    .atom (.copy (.n 2788) (.n 2787)),
    .atom (.add (.n 2789) (.n 2698) (.n 2719)),
    .atom (.copy (.n 2790) (.n 2789))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a2777, a2778, a2779, a2780, a2781, a2782, a2783, a2784, a2785, a2786, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 2879 [
    .atom (.load (.n 2883) (.n 13) 0),
    .atom (.mul (.n 2884) (.n 2883) (.n 2781)),
    .atom (.load (.n 2885) (.n 13) 1),
    .atom (.mul (.n 2886) (.n 2885) (.n 2783)),
    .atom (.add (.n 2887) (.n 2884) (.n 2886)),
    .atom (.load (.n 2888) (.n 13) 2),
    .atom (.mul (.n 2889) (.n 2888) (.n 2786)),
    .atom (.add (.n 2890) (.n 2887) (.n 2889)),
    .atom (.load (.n 2891) (.n 13) 3),
    .atom (.mul (.n 2892) (.n 2891) (.n 2788)),
    .atom (.add (.n 2893) (.n 2890) (.n 2892)),
    .atom (.load (.n 2894) (.n 13) 4),
    .atom (.mul (.n 2895) (.n 2894) (.n 2790)),
    .atom (.add (.n 2896) (.n 2893) (.n 2895)),
    .atom (.add (.n 2897) (.n 14) (.n 2896)),
    .atom (.mul (.n 2898) (.n 878) (.n 2897)),
    .atom (.add (.n 2899) (.n 2882) (.n 2898))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a2879, a2880, a2881, a2882, a2883, a2884, a2885, a2886, a2887, a2888, a2889, a2890, a2891, a2892,
    a2893, a2894, a2895, -⟩ := hs1
  have e2879 := tb_loadHolds_unique a2879 (hw 0 (by norm_num))
  have e2881 := tb_loadHolds_unique a2881 (hw 1 (by norm_num))
  have e2884 := tb_loadHolds_unique a2884 (hw 2 (by norm_num))
  have e2887 := tb_loadHolds_unique a2887 (hw 3 (by norm_num))
  have e2890 := tb_loadHolds_unique a2890 (hw 4 (by norm_num))
  have v2665 : σ (.n 2665) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_evalF h (k := 1) (by norm_num)).2.2
  have v2690 : σ (.n 2690) = ev 4 := by
    rw [← hev 4 (by norm_num)]; exact (vt_evalF h (k := 4) (by norm_num)).2.2
  have v2694 : σ (.n 2694) = ev 5 := by
    rw [← hev 5 (by norm_num)]; exact (vt_evalF h (k := 5) (by norm_num)).2.2
  have v2698 : σ (.n 2698) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_evalF h (k := 6) (by norm_num)).2.2
  have v2702 : σ (.n 2702) = ev 7 := by
    rw [← hev 7 (by norm_num)]; exact (vt_evalF h (k := 7) (by norm_num)).2.2
  have v2719 : σ (.n 2719) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_evalF h (k := 8) (by norm_num)).2.2
  have v2731 : σ (.n 2731) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_evalF h (k := 11) (by norm_num)).2.2
  have hB : σ (.n 2897) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 4], 1)], [([11], 2)], [([5], 1), ([7], 1)], [([6], 1), ([8], 1)]] := by
    simp only [v2731, v2719, v2702, v2698, v2694, v2690, v2665, a2893, a2892, a2891, e2890, a2889, a2888,
      e2887, a2886, a2885, e2884, a2883, a2882, e2881, a2880, e2879, a2786, a2785, a2784,
      a2783, a2782, a2781, a2780, a2779, a2778, a2777]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a2895, a2894, hB]

set_option maxRecDepth 10000 in
theorem vtSide00F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 13, σ (.n (vtEvB (0 + c))) = ev c) :
    σ (.n 2899) =
      vtSideVal [σ (.n 858), σ (.n 863), σ (.n 868), σ (.n 873), σ (.n 878)]
        (σ (.n 14)) W ev vtBTerms00 := by
  rw [vtB00_4F h hw hev, vtB00_3F h hw hev, vtB00_2F h hw hev, vtB00_1F h hw hev, vtB00_0F h hw hev]
  simp only [vtSideVal, vtBTerms00, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, add_zero, add_assoc]

set_option maxRecDepth 10000 in
theorem vtD0_0F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 13, σ (.n (vtEvB (0 + c))) = ev c) :
    σ (.n 2903) = σ (.n 1335) * vtSlots W ev 0
      [[], [([0], 3)], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 2787 [
    .atom (.const (.n 2791) (word 3 0)),
    .atom (.mul (.n 2792) (.n 2791) (.n 2661)),
    .atom (.copy (.n 2793) (.n 2792))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a2787, a2788, a2789, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 2897 [
    .atom (.load (.n 2901) (.n 13) 1),
    .atom (.mul (.n 2902) (.n 2901) (.n 2793)),
    .atom (.mul (.n 2903) (.n 1335) (.n 2902))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a2897, a2898, a2899, -⟩ := hs1
  have e2897 := tb_loadHolds_unique a2897 (hw 1 (by norm_num))
  have v2661 : σ (.n 2661) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_evalF h (k := 0) (by norm_num)).2.2
  have hB : σ (.n 2902) = vtSlots W ev 0 [[], [([0], 3)], []] := by
    simp only [v2661, a2898, e2897, a2789, a2788, a2787]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a2899, hB]

set_option maxRecDepth 10000 in
theorem vtD0_1F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 13, σ (.n (vtEvB (0 + c))) = ev c) :
    σ (.n 2907) = σ (.n 2903) + σ (.n 1337) * vtSlots W ev 0
      [[], [], [([12], 3)], [], [], [], [], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 2790 [
    .atom (.const (.n 2794) (word 3 0)),
    .atom (.mul (.n 2795) (.n 2794) (.n 2748)),
    .atom (.copy (.n 2796) (.n 2795))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a2790, a2791, a2792, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 2900 [
    .atom (.load (.n 2904) (.n 13) 2),
    .atom (.mul (.n 2905) (.n 2904) (.n 2796)),
    .atom (.mul (.n 2906) (.n 1337) (.n 2905)),
    .atom (.add (.n 2907) (.n 2903) (.n 2906))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a2900, a2901, a2902, a2903, -⟩ := hs1
  have e2900 := tb_loadHolds_unique a2900 (hw 2 (by norm_num))
  have v2748 : σ (.n 2748) = ev 12 := by
    rw [← hev 12 (by norm_num)]; exact (vt_evalF h (k := 12) (by norm_num)).2.2
  have hB : σ (.n 2905) = vtSlots W ev 0 [[], [], [([12], 3)], [], [], [], [], [], []] := by
    simp only [v2748, a2901, e2900, a2792, a2791, a2790]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a2903, a2902, hB]

set_option maxRecDepth 10000 in
theorem vtD0_2F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 13, σ (.n (vtEvB (0 + c))) = ev c) :
    σ (.n 2911) = σ (.n 2907) + σ (.n 1339) * vtSlots W ev 0
      [[], [], [([9], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 2793 [
    .atom (.const (.n 2797) (word 3 0)),
    .atom (.mul (.n 2798) (.n 2797) (.n 2723)),
    .atom (.copy (.n 2799) (.n 2798))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a2793, a2794, a2795, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 2904 [
    .atom (.load (.n 2908) (.n 13) 2),
    .atom (.mul (.n 2909) (.n 2908) (.n 2799)),
    .atom (.mul (.n 2910) (.n 1339) (.n 2909)),
    .atom (.add (.n 2911) (.n 2907) (.n 2910))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a2904, a2905, a2906, a2907, -⟩ := hs1
  have e2904 := tb_loadHolds_unique a2904 (hw 2 (by norm_num))
  have v2723 : σ (.n 2723) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_evalF h (k := 9) (by norm_num)).2.2
  have hB : σ (.n 2909) = vtSlots W ev 0 [[], [], [([9], 3)], [], []] := by
    simp only [v2723, a2905, e2904, a2795, a2794, a2793]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a2907, a2906, hB]

set_option maxRecDepth 10000 in
theorem vtD0_3F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 13, σ (.n (vtEvB (0 + c))) = ev c) :
    σ (.n 2915) = σ (.n 2911) + σ (.n 1341) * vtSlots W ev 0
      [[], [], [([10], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 2796 [
    .atom (.const (.n 2800) (word 3 0)),
    .atom (.mul (.n 2801) (.n 2800) (.n 2727)),
    .atom (.copy (.n 2802) (.n 2801))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a2796, a2797, a2798, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 2908 [
    .atom (.load (.n 2912) (.n 13) 2),
    .atom (.mul (.n 2913) (.n 2912) (.n 2802)),
    .atom (.mul (.n 2914) (.n 1341) (.n 2913)),
    .atom (.add (.n 2915) (.n 2911) (.n 2914))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a2908, a2909, a2910, a2911, -⟩ := hs1
  have e2908 := tb_loadHolds_unique a2908 (hw 2 (by norm_num))
  have v2727 : σ (.n 2727) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_evalF h (k := 10) (by norm_num)).2.2
  have hB : σ (.n 2913) = vtSlots W ev 0 [[], [], [([10], 3)], [], []] := by
    simp only [v2727, a2909, e2908, a2798, a2797, a2796]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a2911, a2910, hB]

set_option maxRecDepth 10000 in
theorem vtD0_4F {rd : Reader} {σ : Val} (h : VtF rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 13, σ (.n (vtEvB (0 + c))) = ev c) :
    σ (.n 2919) = σ (.n 2915) + σ (.n 1343) * vtSlots W ev 0
      [[], [], [([11], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 2799 [
    .atom (.const (.n 2803) (word 3 0)),
    .atom (.mul (.n 2804) (.n 2803) (.n 2731)),
    .atom (.copy (.n 2805) (.n 2804))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a2799, a2800, a2801, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 2912 [
    .atom (.load (.n 2916) (.n 13) 2),
    .atom (.mul (.n 2917) (.n 2916) (.n 2805)),
    .atom (.mul (.n 2918) (.n 1343) (.n 2917)),
    .atom (.add (.n 2919) (.n 2915) (.n 2918))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a2912, a2913, a2914, a2915, -⟩ := hs1
  have e2912 := tb_loadHolds_unique a2912 (hw 2 (by norm_num))
  have v2731 : σ (.n 2731) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_evalF h (k := 11) (by norm_num)).2.2
  have hB : σ (.n 2917) = vtSlots W ev 0 [[], [], [([11], 3)], [], []] := by
    simp only [v2731, a2913, e2912, a2801, a2800, a2799]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a2915, a2914, hB]

set_option maxRecDepth 10000 in
theorem vtSide10F {rd : Reader} {σ : Val} (h : VtF rd σ)
    (hq : [σ (.n 1335), σ (.n 1337), σ (.n 1339), σ (.n 1341), σ (.n 1343)] = [σ (.n 858), σ (.n 863), σ (.n 868), σ (.n 873), σ (.n 878)]) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 13, σ (.n (vtEvB (0 + c))) = ev c) :
    σ (.n 2920) =
      vtSideVal [σ (.n 1335), σ (.n 1337), σ (.n 1339), σ (.n 1341), σ (.n 1343)]
        (σ (.n 14)) W ev vtBTerms10 := by
  have hF0 : σ (.n 2899) =
      vtSideVal [σ (.n 1335), σ (.n 1337), σ (.n 1339), σ (.n 1341), σ (.n 1343)]
        (σ (.n 14)) W ev vtBTerms00 := by
    rw [hq]; exact vtSide00F h hw hev
  have a2916 := h.atomAt 2916 (.add (.n 2920) (.n 2899) (.n 2919)) (by decide +kernel)
  simp only [Atom.Holds] at a2916
  rw [vtSideVal_pull _ _ _ _ _ _ _ vtPull0, ← hF0, a2916, vtD0_4F h hw hev, vtD0_3F h hw hev, vtD0_2F h hw hev, vtD0_1F h hw hev, vtD0_0F h hw hev]
  simp only [vtDiffSum, vtDTerms0, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, add_zero, add_assoc]

set_option maxRecDepth 10000 in
theorem vtSide20F {rd : Reader} {σ : Val} (h : VtF rd σ) {ev : ℕ → E}
    (hev : ∀ c < 13, σ (.n (vtEvB (0 + c))) = ev c) :
    σ (.n 2929) =
      vtSideVal [σ (.n 1441), σ (.n 1446), σ (.n 1451), σ (.n 1456)]
        (0) (fun _ ↦ 1) ev vtBTerms20 := by
  obtain ⟨_, hs0⟩ := h.sliceAt 2802 [
    .atom (.copy (.n 2806) (.n 2723)),
    .atom (.copy (.n 2807) (.n 2727)),
    .atom (.copy (.n 2808) (.n 2731)),
    .atom (.copy (.n 2809) (.n 2748))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a2802, a2803, a2804, a2805, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 2919 [
    .atom (.mul (.n 2923) (.n 1441) (.n 2806)),
    .atom (.mul (.n 2924) (.n 1446) (.n 2807)),
    .atom (.add (.n 2925) (.n 2923) (.n 2924)),
    .atom (.mul (.n 2926) (.n 1451) (.n 2808)),
    .atom (.add (.n 2927) (.n 2925) (.n 2926)),
    .atom (.mul (.n 2928) (.n 1456) (.n 2809)),
    .atom (.add (.n 2929) (.n 2927) (.n 2928))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a2919, a2920, a2921, a2922, a2923, a2924, a2925, -⟩ := hs1
  have v2723 : σ (.n 2723) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_evalF h (k := 9) (by norm_num)).2.2
  have v2727 : σ (.n 2727) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_evalF h (k := 10) (by norm_num)).2.2
  have v2731 : σ (.n 2731) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_evalF h (k := 11) (by norm_num)).2.2
  have v2748 : σ (.n 2748) = ev 12 := by
    rw [← hev 12 (by norm_num)]; exact (vt_evalF h (k := 12) (by norm_num)).2.2
  simp only [v2748, v2731, v2727, v2723, a2925, a2924, a2923, a2922, a2921, a2920, a2919, a2805, a2804, a2803,
    a2802]
  simp only [vtSideVal, vtBTerms20, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, vt_ofK_ofBits_one]
  ring

end
end LeanVM.Guest.B1.Tables
