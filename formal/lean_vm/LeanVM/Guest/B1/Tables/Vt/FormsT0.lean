/-
  LeanVM.Guest.B1.Tables.Vt.FormsT0

  Table 0's forms on the three sides, from the guest's statements: each block's value from its
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
theorem vtB00_0 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 13, σ (.n (vtEvB (0 + c))) = ev c) :
    σ (.n 2814) = σ (.n 857) * vtBlockVal (σ (.n 14)) W ev
      [[([], 1)], [([0], 2)], [([1], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 2740 [
    .atom (.const (.n 2744) (word 1 0)),
    .atom (.const (.n 2745) (word 2 0)),
    .atom (.mul (.n 2746) (.n 2745) (.n 2656)),
    .atom (.copy (.n 2747) (.n 2746)),
    .atom (.copy (.n 2748) (.n 2660))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a2740, a2741, a2742, a2743, a2744, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 2801 [
    .atom (.load (.n 2805) (.n 13) 0),
    .atom (.mul (.n 2806) (.n 2805) (.n 2744)),
    .atom (.load (.n 2807) (.n 13) 1),
    .atom (.mul (.n 2808) (.n 2807) (.n 2747)),
    .atom (.add (.n 2809) (.n 2806) (.n 2808)),
    .atom (.load (.n 2810) (.n 13) 2),
    .atom (.mul (.n 2811) (.n 2810) (.n 2748)),
    .atom (.add (.n 2812) (.n 2809) (.n 2811)),
    .atom (.add (.n 2813) (.n 14) (.n 2812)),
    .atom (.mul (.n 2814) (.n 857) (.n 2813))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a2801, a2802, a2803, a2804, a2805, a2806, a2807, a2808, a2809, a2810, -⟩ := hs1
  have e2801 := tb_loadHolds_unique a2801 (hw 0 (by norm_num))
  have e2803 := tb_loadHolds_unique a2803 (hw 1 (by norm_num))
  have e2806 := tb_loadHolds_unique a2806 (hw 2 (by norm_num))
  have v2656 : σ (.n 2656) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_eval h (k := 0) (by norm_num)).2.2
  have v2660 : σ (.n 2660) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 1) (by norm_num)).2.2
  have hB : σ (.n 2813) = vtBlockVal (σ (.n 14)) W ev [[([], 1)], [([0], 2)], [([1], 1)]] := by
    simp only [v2660, v2656, a2809, a2808, a2807, e2806, a2805, a2804, e2803, a2802, e2801, a2744, a2743,
      a2742, a2741, a2740]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a2810, hB]

set_option maxRecDepth 10000 in
theorem vtB00_1 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 13, σ (.n (vtEvB (0 + c))) = ev c) :
    σ (.n 2843) = σ (.n 2814) + σ (.n 862) * vtBlockVal (σ (.n 14)) W ev
      [[([], 4)], [([0], 1)], [([12], 2)], [([], 1)], [([2], 1)], [([3], 1)], [([4], 1)], [([], 0)], [([], 0)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 2745 [
    .atom (.const (.n 2749) (word 4 0)),
    .atom (.copy (.n 2750) (.n 2656)),
    .atom (.const (.n 2751) (word 2 0)),
    .atom (.mul (.n 2752) (.n 2751) (.n 2743)),
    .atom (.copy (.n 2753) (.n 2752)),
    .atom (.const (.n 2754) (word 1 0)),
    .atom (.copy (.n 2755) (.n 2664)),
    .atom (.copy (.n 2756) (.n 2668)),
    .atom (.copy (.n 2757) (.n 2685)),
    .atom (.const (.n 2758) (word 0 0)),
    .atom (.const (.n 2759) (word 0 0))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a2745, a2746, a2747, a2748, a2749, a2750, a2751, a2752, a2753, a2754, a2755, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 2811 [
    .atom (.load (.n 2815) (.n 13) 0),
    .atom (.mul (.n 2816) (.n 2815) (.n 2749)),
    .atom (.load (.n 2817) (.n 13) 1),
    .atom (.mul (.n 2818) (.n 2817) (.n 2750)),
    .atom (.add (.n 2819) (.n 2816) (.n 2818)),
    .atom (.load (.n 2820) (.n 13) 2),
    .atom (.mul (.n 2821) (.n 2820) (.n 2753)),
    .atom (.add (.n 2822) (.n 2819) (.n 2821)),
    .atom (.load (.n 2823) (.n 13) 3),
    .atom (.mul (.n 2824) (.n 2823) (.n 2754)),
    .atom (.add (.n 2825) (.n 2822) (.n 2824)),
    .atom (.load (.n 2826) (.n 13) 4),
    .atom (.mul (.n 2827) (.n 2826) (.n 2755)),
    .atom (.add (.n 2828) (.n 2825) (.n 2827)),
    .atom (.load (.n 2829) (.n 13) 5),
    .atom (.mul (.n 2830) (.n 2829) (.n 2756)),
    .atom (.add (.n 2831) (.n 2828) (.n 2830)),
    .atom (.load (.n 2832) (.n 13) 6),
    .atom (.mul (.n 2833) (.n 2832) (.n 2757)),
    .atom (.add (.n 2834) (.n 2831) (.n 2833)),
    .atom (.load (.n 2835) (.n 13) 7),
    .atom (.mul (.n 2836) (.n 2835) (.n 2758)),
    .atom (.add (.n 2837) (.n 2834) (.n 2836)),
    .atom (.load (.n 2838) (.n 13) 8),
    .atom (.mul (.n 2839) (.n 2838) (.n 2759)),
    .atom (.add (.n 2840) (.n 2837) (.n 2839)),
    .atom (.add (.n 2841) (.n 14) (.n 2840)),
    .atom (.mul (.n 2842) (.n 862) (.n 2841)),
    .atom (.add (.n 2843) (.n 2814) (.n 2842))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a2811, a2812, a2813, a2814, a2815, a2816, a2817, a2818, a2819, a2820, a2821, a2822, a2823, a2824,
    a2825, a2826, a2827, a2828, a2829, a2830, a2831, a2832, a2833, a2834, a2835, a2836, a2837,
    a2838, a2839, -⟩ := hs1
  have e2811 := tb_loadHolds_unique a2811 (hw 0 (by norm_num))
  have e2813 := tb_loadHolds_unique a2813 (hw 1 (by norm_num))
  have e2816 := tb_loadHolds_unique a2816 (hw 2 (by norm_num))
  have e2819 := tb_loadHolds_unique a2819 (hw 3 (by norm_num))
  have e2822 := tb_loadHolds_unique a2822 (hw 4 (by norm_num))
  have e2825 := tb_loadHolds_unique a2825 (hw 5 (by norm_num))
  have e2828 := tb_loadHolds_unique a2828 (hw 6 (by norm_num))
  have e2831 := tb_loadHolds_unique a2831 (hw 7 (by norm_num))
  have e2834 := tb_loadHolds_unique a2834 (hw 8 (by norm_num))
  have v2656 : σ (.n 2656) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_eval h (k := 0) (by norm_num)).2.2
  have v2664 : σ (.n 2664) = ev 2 := by
    rw [← hev 2 (by norm_num)]; exact (vt_eval h (k := 2) (by norm_num)).2.2
  have v2668 : σ (.n 2668) = ev 3 := by
    rw [← hev 3 (by norm_num)]; exact (vt_eval h (k := 3) (by norm_num)).2.2
  have v2685 : σ (.n 2685) = ev 4 := by
    rw [← hev 4 (by norm_num)]; exact (vt_eval h (k := 4) (by norm_num)).2.2
  have v2743 : σ (.n 2743) = ev 12 := by
    rw [← hev 12 (by norm_num)]; exact (vt_eval h (k := 12) (by norm_num)).2.2
  have hB : σ (.n 2841) = vtBlockVal (σ (.n 14)) W ev [[([], 4)], [([0], 1)], [([12], 2)], [([], 1)], [([2], 1)], [([3], 1)], [([4], 1)], [([], 0)], [([], 0)]] := by
    simp only [v2743, v2685, v2668, v2664, v2656, a2837, a2836, a2835, e2834, a2833, a2832, e2831, a2830,
      a2829, e2828, a2827, a2826, e2825, a2824, a2823, e2822, a2821, a2820, e2819, a2818,
      a2817, e2816, a2815, a2814, e2813, a2812, e2811, a2755, a2754, a2753, a2752, a2751,
      a2750, a2749, a2748, a2747, a2746, a2745]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a2839, a2838, hB]

set_option maxRecDepth 10000 in
theorem vtB00_2 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 13, σ (.n (vtEvB (0 + c))) = ev c) :
    σ (.n 2860) = σ (.n 2843) + σ (.n 867) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 2], 1)], [([9], 2)], [([5], 1)], [([6], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 2756 [
    .atom (.const (.n 2760) (word 2 0)),
    .atom (.mul (.n 2761) (.n 2660) (.n 2664)),
    .atom (.copy (.n 2762) (.n 2761)),
    .atom (.const (.n 2763) (word 2 0)),
    .atom (.mul (.n 2764) (.n 2763) (.n 2718)),
    .atom (.copy (.n 2765) (.n 2764)),
    .atom (.copy (.n 2766) (.n 2689)),
    .atom (.copy (.n 2767) (.n 2693))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a2756, a2757, a2758, a2759, a2760, a2761, a2762, a2763, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 2840 [
    .atom (.load (.n 2844) (.n 13) 0),
    .atom (.mul (.n 2845) (.n 2844) (.n 2760)),
    .atom (.load (.n 2846) (.n 13) 1),
    .atom (.mul (.n 2847) (.n 2846) (.n 2762)),
    .atom (.add (.n 2848) (.n 2845) (.n 2847)),
    .atom (.load (.n 2849) (.n 13) 2),
    .atom (.mul (.n 2850) (.n 2849) (.n 2765)),
    .atom (.add (.n 2851) (.n 2848) (.n 2850)),
    .atom (.load (.n 2852) (.n 13) 3),
    .atom (.mul (.n 2853) (.n 2852) (.n 2766)),
    .atom (.add (.n 2854) (.n 2851) (.n 2853)),
    .atom (.load (.n 2855) (.n 13) 4),
    .atom (.mul (.n 2856) (.n 2855) (.n 2767)),
    .atom (.add (.n 2857) (.n 2854) (.n 2856)),
    .atom (.add (.n 2858) (.n 14) (.n 2857)),
    .atom (.mul (.n 2859) (.n 867) (.n 2858)),
    .atom (.add (.n 2860) (.n 2843) (.n 2859))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a2840, a2841, a2842, a2843, a2844, a2845, a2846, a2847, a2848, a2849, a2850, a2851, a2852, a2853,
    a2854, a2855, a2856, -⟩ := hs1
  have e2840 := tb_loadHolds_unique a2840 (hw 0 (by norm_num))
  have e2842 := tb_loadHolds_unique a2842 (hw 1 (by norm_num))
  have e2845 := tb_loadHolds_unique a2845 (hw 2 (by norm_num))
  have e2848 := tb_loadHolds_unique a2848 (hw 3 (by norm_num))
  have e2851 := tb_loadHolds_unique a2851 (hw 4 (by norm_num))
  have v2660 : σ (.n 2660) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 1) (by norm_num)).2.2
  have v2664 : σ (.n 2664) = ev 2 := by
    rw [← hev 2 (by norm_num)]; exact (vt_eval h (k := 2) (by norm_num)).2.2
  have v2689 : σ (.n 2689) = ev 5 := by
    rw [← hev 5 (by norm_num)]; exact (vt_eval h (k := 5) (by norm_num)).2.2
  have v2693 : σ (.n 2693) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_eval h (k := 6) (by norm_num)).2.2
  have v2718 : σ (.n 2718) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 9) (by norm_num)).2.2
  have hB : σ (.n 2858) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 2], 1)], [([9], 2)], [([5], 1)], [([6], 1)]] := by
    simp only [v2718, v2693, v2689, v2664, v2660, a2854, a2853, a2852, e2851, a2850, a2849, e2848, a2847,
      a2846, e2845, a2844, a2843, e2842, a2841, e2840, a2763, a2762, a2761, a2760, a2759,
      a2758, a2757, a2756]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a2856, a2855, hB]

set_option maxRecDepth 10000 in
theorem vtB00_3 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 13, σ (.n (vtEvB (0 + c))) = ev c) :
    σ (.n 2877) = σ (.n 2860) + σ (.n 872) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 3], 1)], [([10], 2)], [([7], 1)], [([8], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 2764 [
    .atom (.const (.n 2768) (word 2 0)),
    .atom (.mul (.n 2769) (.n 2660) (.n 2668)),
    .atom (.copy (.n 2770) (.n 2769)),
    .atom (.const (.n 2771) (word 2 0)),
    .atom (.mul (.n 2772) (.n 2771) (.n 2722)),
    .atom (.copy (.n 2773) (.n 2772)),
    .atom (.copy (.n 2774) (.n 2697)),
    .atom (.copy (.n 2775) (.n 2714))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a2764, a2765, a2766, a2767, a2768, a2769, a2770, a2771, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 2857 [
    .atom (.load (.n 2861) (.n 13) 0),
    .atom (.mul (.n 2862) (.n 2861) (.n 2768)),
    .atom (.load (.n 2863) (.n 13) 1),
    .atom (.mul (.n 2864) (.n 2863) (.n 2770)),
    .atom (.add (.n 2865) (.n 2862) (.n 2864)),
    .atom (.load (.n 2866) (.n 13) 2),
    .atom (.mul (.n 2867) (.n 2866) (.n 2773)),
    .atom (.add (.n 2868) (.n 2865) (.n 2867)),
    .atom (.load (.n 2869) (.n 13) 3),
    .atom (.mul (.n 2870) (.n 2869) (.n 2774)),
    .atom (.add (.n 2871) (.n 2868) (.n 2870)),
    .atom (.load (.n 2872) (.n 13) 4),
    .atom (.mul (.n 2873) (.n 2872) (.n 2775)),
    .atom (.add (.n 2874) (.n 2871) (.n 2873)),
    .atom (.add (.n 2875) (.n 14) (.n 2874)),
    .atom (.mul (.n 2876) (.n 872) (.n 2875)),
    .atom (.add (.n 2877) (.n 2860) (.n 2876))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a2857, a2858, a2859, a2860, a2861, a2862, a2863, a2864, a2865, a2866, a2867, a2868, a2869, a2870,
    a2871, a2872, a2873, -⟩ := hs1
  have e2857 := tb_loadHolds_unique a2857 (hw 0 (by norm_num))
  have e2859 := tb_loadHolds_unique a2859 (hw 1 (by norm_num))
  have e2862 := tb_loadHolds_unique a2862 (hw 2 (by norm_num))
  have e2865 := tb_loadHolds_unique a2865 (hw 3 (by norm_num))
  have e2868 := tb_loadHolds_unique a2868 (hw 4 (by norm_num))
  have v2660 : σ (.n 2660) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 1) (by norm_num)).2.2
  have v2668 : σ (.n 2668) = ev 3 := by
    rw [← hev 3 (by norm_num)]; exact (vt_eval h (k := 3) (by norm_num)).2.2
  have v2697 : σ (.n 2697) = ev 7 := by
    rw [← hev 7 (by norm_num)]; exact (vt_eval h (k := 7) (by norm_num)).2.2
  have v2714 : σ (.n 2714) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_eval h (k := 8) (by norm_num)).2.2
  have v2722 : σ (.n 2722) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_eval h (k := 10) (by norm_num)).2.2
  have hB : σ (.n 2875) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 3], 1)], [([10], 2)], [([7], 1)], [([8], 1)]] := by
    simp only [v2722, v2714, v2697, v2668, v2660, a2871, a2870, a2869, e2868, a2867, a2866, e2865, a2864,
      a2863, e2862, a2861, a2860, e2859, a2858, e2857, a2771, a2770, a2769, a2768, a2767,
      a2766, a2765, a2764]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a2873, a2872, hB]

set_option maxRecDepth 10000 in
theorem vtB00_4 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 13, σ (.n (vtEvB (0 + c))) = ev c) :
    σ (.n 2894) = σ (.n 2877) + σ (.n 877) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 4], 1)], [([11], 2)], [([5], 1), ([7], 1)], [([6], 1), ([8], 1)]] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 2772 [
    .atom (.const (.n 2776) (word 2 0)),
    .atom (.mul (.n 2777) (.n 2660) (.n 2685)),
    .atom (.copy (.n 2778) (.n 2777)),
    .atom (.const (.n 2779) (word 2 0)),
    .atom (.mul (.n 2780) (.n 2779) (.n 2726)),
    .atom (.copy (.n 2781) (.n 2780)),
    .atom (.add (.n 2782) (.n 2689) (.n 2697)),
    .atom (.copy (.n 2783) (.n 2782)),
    .atom (.add (.n 2784) (.n 2693) (.n 2714)),
    .atom (.copy (.n 2785) (.n 2784))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a2772, a2773, a2774, a2775, a2776, a2777, a2778, a2779, a2780, a2781, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 2874 [
    .atom (.load (.n 2878) (.n 13) 0),
    .atom (.mul (.n 2879) (.n 2878) (.n 2776)),
    .atom (.load (.n 2880) (.n 13) 1),
    .atom (.mul (.n 2881) (.n 2880) (.n 2778)),
    .atom (.add (.n 2882) (.n 2879) (.n 2881)),
    .atom (.load (.n 2883) (.n 13) 2),
    .atom (.mul (.n 2884) (.n 2883) (.n 2781)),
    .atom (.add (.n 2885) (.n 2882) (.n 2884)),
    .atom (.load (.n 2886) (.n 13) 3),
    .atom (.mul (.n 2887) (.n 2886) (.n 2783)),
    .atom (.add (.n 2888) (.n 2885) (.n 2887)),
    .atom (.load (.n 2889) (.n 13) 4),
    .atom (.mul (.n 2890) (.n 2889) (.n 2785)),
    .atom (.add (.n 2891) (.n 2888) (.n 2890)),
    .atom (.add (.n 2892) (.n 14) (.n 2891)),
    .atom (.mul (.n 2893) (.n 877) (.n 2892)),
    .atom (.add (.n 2894) (.n 2877) (.n 2893))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a2874, a2875, a2876, a2877, a2878, a2879, a2880, a2881, a2882, a2883, a2884, a2885, a2886, a2887,
    a2888, a2889, a2890, -⟩ := hs1
  have e2874 := tb_loadHolds_unique a2874 (hw 0 (by norm_num))
  have e2876 := tb_loadHolds_unique a2876 (hw 1 (by norm_num))
  have e2879 := tb_loadHolds_unique a2879 (hw 2 (by norm_num))
  have e2882 := tb_loadHolds_unique a2882 (hw 3 (by norm_num))
  have e2885 := tb_loadHolds_unique a2885 (hw 4 (by norm_num))
  have v2660 : σ (.n 2660) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 1) (by norm_num)).2.2
  have v2685 : σ (.n 2685) = ev 4 := by
    rw [← hev 4 (by norm_num)]; exact (vt_eval h (k := 4) (by norm_num)).2.2
  have v2689 : σ (.n 2689) = ev 5 := by
    rw [← hev 5 (by norm_num)]; exact (vt_eval h (k := 5) (by norm_num)).2.2
  have v2693 : σ (.n 2693) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_eval h (k := 6) (by norm_num)).2.2
  have v2697 : σ (.n 2697) = ev 7 := by
    rw [← hev 7 (by norm_num)]; exact (vt_eval h (k := 7) (by norm_num)).2.2
  have v2714 : σ (.n 2714) = ev 8 := by
    rw [← hev 8 (by norm_num)]; exact (vt_eval h (k := 8) (by norm_num)).2.2
  have v2726 : σ (.n 2726) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_eval h (k := 11) (by norm_num)).2.2
  have hB : σ (.n 2892) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 4], 1)], [([11], 2)], [([5], 1), ([7], 1)], [([6], 1), ([8], 1)]] := by
    simp only [v2726, v2714, v2697, v2693, v2689, v2685, v2660, a2888, a2887, a2886, e2885, a2884, a2883,
      e2882, a2881, a2880, e2879, a2878, a2877, e2876, a2875, e2874, a2781, a2780, a2779,
      a2778, a2777, a2776, a2775, a2774, a2773, a2772]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a2890, a2889, hB]

set_option maxRecDepth 10000 in
theorem vtSide00 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 13, σ (.n (vtEvB (0 + c))) = ev c) :
    σ (.n 2894) =
      vtSideVal [σ (.n 857), σ (.n 862), σ (.n 867), σ (.n 872), σ (.n 877)]
        (σ (.n 14)) W ev vtBTerms00 := by
  rw [vtB00_4 h hw hev, vtB00_3 h hw hev, vtB00_2 h hw hev, vtB00_1 h hw hev, vtB00_0 h hw hev]
  simp only [vtSideVal, vtBTerms00, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, add_zero, add_assoc]

set_option maxRecDepth 10000 in
theorem vtD0_0 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 13, σ (.n (vtEvB (0 + c))) = ev c) :
    σ (.n 2898) = σ (.n 1334) * vtSlots W ev 0
      [[], [([0], 3)], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 2782 [
    .atom (.const (.n 2786) (word 3 0)),
    .atom (.mul (.n 2787) (.n 2786) (.n 2656)),
    .atom (.copy (.n 2788) (.n 2787))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a2782, a2783, a2784, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 2892 [
    .atom (.load (.n 2896) (.n 13) 1),
    .atom (.mul (.n 2897) (.n 2896) (.n 2788)),
    .atom (.mul (.n 2898) (.n 1334) (.n 2897))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a2892, a2893, a2894, -⟩ := hs1
  have e2892 := tb_loadHolds_unique a2892 (hw 1 (by norm_num))
  have v2656 : σ (.n 2656) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_eval h (k := 0) (by norm_num)).2.2
  have hB : σ (.n 2897) = vtSlots W ev 0 [[], [([0], 3)], []] := by
    simp only [v2656, a2893, e2892, a2784, a2783, a2782]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a2894, hB]

set_option maxRecDepth 10000 in
theorem vtD0_1 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 13, σ (.n (vtEvB (0 + c))) = ev c) :
    σ (.n 2902) = σ (.n 2898) + σ (.n 1336) * vtSlots W ev 0
      [[], [], [([12], 3)], [], [], [], [], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 2785 [
    .atom (.const (.n 2789) (word 3 0)),
    .atom (.mul (.n 2790) (.n 2789) (.n 2743)),
    .atom (.copy (.n 2791) (.n 2790))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a2785, a2786, a2787, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 2895 [
    .atom (.load (.n 2899) (.n 13) 2),
    .atom (.mul (.n 2900) (.n 2899) (.n 2791)),
    .atom (.mul (.n 2901) (.n 1336) (.n 2900)),
    .atom (.add (.n 2902) (.n 2898) (.n 2901))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a2895, a2896, a2897, a2898, -⟩ := hs1
  have e2895 := tb_loadHolds_unique a2895 (hw 2 (by norm_num))
  have v2743 : σ (.n 2743) = ev 12 := by
    rw [← hev 12 (by norm_num)]; exact (vt_eval h (k := 12) (by norm_num)).2.2
  have hB : σ (.n 2900) = vtSlots W ev 0 [[], [], [([12], 3)], [], [], [], [], [], []] := by
    simp only [v2743, a2896, e2895, a2787, a2786, a2785]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a2898, a2897, hB]

set_option maxRecDepth 10000 in
theorem vtD0_2 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 13, σ (.n (vtEvB (0 + c))) = ev c) :
    σ (.n 2906) = σ (.n 2902) + σ (.n 1338) * vtSlots W ev 0
      [[], [], [([9], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 2788 [
    .atom (.const (.n 2792) (word 3 0)),
    .atom (.mul (.n 2793) (.n 2792) (.n 2718)),
    .atom (.copy (.n 2794) (.n 2793))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a2788, a2789, a2790, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 2899 [
    .atom (.load (.n 2903) (.n 13) 2),
    .atom (.mul (.n 2904) (.n 2903) (.n 2794)),
    .atom (.mul (.n 2905) (.n 1338) (.n 2904)),
    .atom (.add (.n 2906) (.n 2902) (.n 2905))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a2899, a2900, a2901, a2902, -⟩ := hs1
  have e2899 := tb_loadHolds_unique a2899 (hw 2 (by norm_num))
  have v2718 : σ (.n 2718) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 9) (by norm_num)).2.2
  have hB : σ (.n 2904) = vtSlots W ev 0 [[], [], [([9], 3)], [], []] := by
    simp only [v2718, a2900, e2899, a2790, a2789, a2788]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a2902, a2901, hB]

set_option maxRecDepth 10000 in
theorem vtD0_3 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 13, σ (.n (vtEvB (0 + c))) = ev c) :
    σ (.n 2910) = σ (.n 2906) + σ (.n 1340) * vtSlots W ev 0
      [[], [], [([10], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 2791 [
    .atom (.const (.n 2795) (word 3 0)),
    .atom (.mul (.n 2796) (.n 2795) (.n 2722)),
    .atom (.copy (.n 2797) (.n 2796))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a2791, a2792, a2793, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 2903 [
    .atom (.load (.n 2907) (.n 13) 2),
    .atom (.mul (.n 2908) (.n 2907) (.n 2797)),
    .atom (.mul (.n 2909) (.n 1340) (.n 2908)),
    .atom (.add (.n 2910) (.n 2906) (.n 2909))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a2903, a2904, a2905, a2906, -⟩ := hs1
  have e2903 := tb_loadHolds_unique a2903 (hw 2 (by norm_num))
  have v2722 : σ (.n 2722) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_eval h (k := 10) (by norm_num)).2.2
  have hB : σ (.n 2908) = vtSlots W ev 0 [[], [], [([10], 3)], [], []] := by
    simp only [v2722, a2904, e2903, a2793, a2792, a2791]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a2906, a2905, hB]

set_option maxRecDepth 10000 in
theorem vtD0_4 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 13, σ (.n (vtEvB (0 + c))) = ev c) :
    σ (.n 2914) = σ (.n 2910) + σ (.n 1342) * vtSlots W ev 0
      [[], [], [([11], 3)], [], []] := by
  obtain ⟨_, hs0⟩ := h.sliceAt 2794 [
    .atom (.const (.n 2798) (word 3 0)),
    .atom (.mul (.n 2799) (.n 2798) (.n 2726)),
    .atom (.copy (.n 2800) (.n 2799))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a2794, a2795, a2796, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 2907 [
    .atom (.load (.n 2911) (.n 13) 2),
    .atom (.mul (.n 2912) (.n 2911) (.n 2800)),
    .atom (.mul (.n 2913) (.n 1342) (.n 2912)),
    .atom (.add (.n 2914) (.n 2910) (.n 2913))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a2907, a2908, a2909, a2910, -⟩ := hs1
  have e2907 := tb_loadHolds_unique a2907 (hw 2 (by norm_num))
  have v2726 : σ (.n 2726) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_eval h (k := 11) (by norm_num)).2.2
  have hB : σ (.n 2912) = vtSlots W ev 0 [[], [], [([11], 3)], [], []] := by
    simp only [v2726, a2908, e2907, a2796, a2795, a2794]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a2910, a2909, hB]

set_option maxRecDepth 10000 in
theorem vtSide10 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 13, σ (.n (vtEvB (0 + c))) = ev c) :
    σ (.n 2915) =
      vtSideVal [σ (.n 1334), σ (.n 1336), σ (.n 1338), σ (.n 1340), σ (.n 1342)]
        (σ (.n 14)) W ev vtBTerms10 := by
  have hF0 : σ (.n 2894) =
      vtSideVal [σ (.n 1334), σ (.n 1336), σ (.n 1338), σ (.n 1340), σ (.n 1342)]
        (σ (.n 14)) W ev vtBTerms00 := by
    rw [vtPullSels0 h]; exact vtSide00 h hw hev
  have a2911 := h.atomAt 2911 (.add (.n 2915) (.n 2894) (.n 2914)) (by decide +kernel)
  simp only [Atom.Holds] at a2911
  rw [vtSideVal_pull _ _ _ _ _ _ _ vtPull0, ← hF0, a2911, vtD0_4 h hw hev, vtD0_3 h hw hev, vtD0_2 h hw hev, vtD0_1 h hw hev, vtD0_0 h hw hev]
  simp only [vtDiffSum, vtDTerms0, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, add_zero, add_assoc]

set_option maxRecDepth 10000 in
theorem vtSide20 {rd : Reader} {σ : Val} (h : VtH rd σ) {ev : ℕ → E}
    (hev : ∀ c < 13, σ (.n (vtEvB (0 + c))) = ev c) :
    σ (.n 2924) =
      vtSideVal [σ (.n 1440), σ (.n 1445), σ (.n 1450), σ (.n 1455)]
        (0) (fun _ ↦ 1) ev vtBTerms20 := by
  obtain ⟨_, hs0⟩ := h.sliceAt 2797 [
    .atom (.copy (.n 2801) (.n 2718)),
    .atom (.copy (.n 2802) (.n 2722)),
    .atom (.copy (.n 2803) (.n 2726)),
    .atom (.copy (.n 2804) (.n 2743))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs0
  obtain ⟨a2797, a2798, a2799, a2800, -⟩ := hs0
  obtain ⟨_, hs1⟩ := h.sliceAt 2914 [
    .atom (.mul (.n 2918) (.n 1440) (.n 2801)),
    .atom (.mul (.n 2919) (.n 1445) (.n 2802)),
    .atom (.add (.n 2920) (.n 2918) (.n 2919)),
    .atom (.mul (.n 2921) (.n 1450) (.n 2803)),
    .atom (.add (.n 2922) (.n 2920) (.n 2921)),
    .atom (.mul (.n 2923) (.n 1455) (.n 2804)),
    .atom (.add (.n 2924) (.n 2922) (.n 2923))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs1
  obtain ⟨a2914, a2915, a2916, a2917, a2918, a2919, a2920, -⟩ := hs1
  have v2718 : σ (.n 2718) = ev 9 := by
    rw [← hev 9 (by norm_num)]; exact (vt_eval h (k := 9) (by norm_num)).2.2
  have v2722 : σ (.n 2722) = ev 10 := by
    rw [← hev 10 (by norm_num)]; exact (vt_eval h (k := 10) (by norm_num)).2.2
  have v2726 : σ (.n 2726) = ev 11 := by
    rw [← hev 11 (by norm_num)]; exact (vt_eval h (k := 11) (by norm_num)).2.2
  have v2743 : σ (.n 2743) = ev 12 := by
    rw [← hev 12 (by norm_num)]; exact (vt_eval h (k := 12) (by norm_num)).2.2
  simp only [v2743, v2726, v2722, v2718, a2920, a2919, a2918, a2917, a2916, a2915, a2914, a2800, a2799, a2798,
    a2797]
  simp only [vtSideVal, vtBTerms20, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, vt_ofK_ofBits_one]
  ring

end
end LeanVM.Guest.B1.Tables
