/-
  LeanVM.Guest.B1.Tables.Vt.PushFw

  `verify_tables`' push side's framework blocks: their fingerprints' accumulator, the three
  memory words read from the stream and pooled, and the index MLE values.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.PushPad

/-!
# The push side's framework blocks (G:2269-2315)

`vt_push_fw`: the accumulator after the state, memory and bytecode blocks is
`Σ_f eq_f·(β + fp_f)` with the state fingerprint `w0 + w1 + w2`, the memory one
`w0·g + w1·idx + w2 + w3·m0 + w4·m1 + w5·m2` and the bytecode one `w0·g² + w1·idx' + w2 + bv`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

set_option maxRecDepth 100000 in
/-- **The push side's framework accumulator.** -/
theorem vt_push_fw {rd : Reader} {σ : Val} (h : VtH rd σ) {W : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i)) :
    σ (.n 955) = σ (.n 794) * (σ (.n 14) + (W 0 + W 1 + W 2)) +
      σ (.n 817) * (σ (.n 14) + (W 0 * gen + W 1 * σ (.n 824) + W 2 + W 3 * σ (.n 830) +
        W 4 * σ (.n 843) + W 5 * σ (.n 856))) +
      σ (.n 887) * (σ (.n 14) + (W 0 * gen ^ 2 + W 1 * σ (.n 894) + W 2 + σ (.n 581))) := by
  have a2424 := h.atomAt 784 (.load (.n 797) (.n 13) 0) (by decide +kernel)
  have a2425 := h.atomAt 785 (.load (.n 798) (.n 13) 1) (by decide +kernel)
  have a2426 := h.atomAt 786 (.add (.n 799) (.n 797) (.n 798)) (by decide +kernel)
  have a2427 := h.atomAt 787 (.load (.n 800) (.n 13) 2) (by decide +kernel)
  have a2428 := h.atomAt 788 (.add (.n 801) (.n 799) (.n 800)) (by decide +kernel)
  have a2429 := h.atomAt 789 (.const (.n 802) (word 0 0 0)) (by decide +kernel)
  have a2430 := h.atomAt 790 (.mul (.n 803) (.n 802) (.n 581)) (by decide +kernel)
  have a2431 := h.atomAt 791 (.add (.n 804) (.n 801) (.n 803)) (by decide +kernel)
  have a2432 := h.atomAt 792 (.add (.n 805) (.n 14) (.n 804)) (by decide +kernel)
  have a2433 := h.atomAt 793 (.mul (.n 806) (.n 794) (.n 805)) (by decide +kernel)
  have a2452 := h.atomAt 807 (.load (.n 821) (.n 13) 0) (by decide +kernel)
  have a2453 := h.atomAt 808 (.const (.n 822) (word 2 0 0)) (by decide +kernel)
  have a2454 := h.atomAt 809 (.mul (.n 823) (.n 821) (.n 822)) (by decide +kernel)
  have a2457 := h.atomAt 812 (.load (.n 825) (.n 13) 1) (by decide +kernel)
  have a2458 := h.atomAt 813 (.mul (.n 826) (.n 825) (.n 824)) (by decide +kernel)
  have a2459 := h.atomAt 814 (.add (.n 827) (.n 823) (.n 826)) (by decide +kernel)
  have a2460 := h.atomAt 815 (.load (.n 828) (.n 13) 2) (by decide +kernel)
  have a2461 := h.atomAt 816 (.add (.n 829) (.n 827) (.n 828)) (by decide +kernel)
  have a2473 := h.atomAt 827 (.load (.n 840) (.n 13) 3) (by decide +kernel)
  have a2474 := h.atomAt 828 (.mul (.n 841) (.n 840) (.n 830)) (by decide +kernel)
  have a2475 := h.atomAt 829 (.add (.n 842) (.n 829) (.n 841)) (by decide +kernel)
  have a2487 := h.atomAt 840 (.load (.n 853) (.n 13) 4) (by decide +kernel)
  have a2488 := h.atomAt 841 (.mul (.n 854) (.n 853) (.n 843)) (by decide +kernel)
  have a2489 := h.atomAt 842 (.add (.n 855) (.n 842) (.n 854)) (by decide +kernel)
  have a2501 := h.atomAt 853 (.load (.n 866) (.n 13) 5) (by decide +kernel)
  have a2502 := h.atomAt 854 (.mul (.n 867) (.n 866) (.n 856)) (by decide +kernel)
  have a2503 := h.atomAt 855 (.add (.n 868) (.n 855) (.n 867)) (by decide +kernel)
  have a2504 := h.atomAt 856 (.const (.n 869) (word 0 0 0)) (by decide +kernel)
  have a2505 := h.atomAt 857 (.mul (.n 870) (.n 869) (.n 581)) (by decide +kernel)
  have a2506 := h.atomAt 858 (.add (.n 871) (.n 868) (.n 870)) (by decide +kernel)
  have a2507 := h.atomAt 859 (.add (.n 872) (.n 14) (.n 871)) (by decide +kernel)
  have a2508 := h.atomAt 860 (.mul (.n 873) (.n 817) (.n 872)) (by decide +kernel)
  have a2509 := h.atomAt 861 (.add (.n 874) (.n 806) (.n 873)) (by decide +kernel)
  have a2528 := h.atomAt 877 (.load (.n 891) (.n 13) 0) (by decide +kernel)
  have a2529 := h.atomAt 878 (.const (.n 892) (word 4 0 0)) (by decide +kernel)
  have a2530 := h.atomAt 879 (.mul (.n 893) (.n 891) (.n 892)) (by decide +kernel)
  have a2533 := h.atomAt 882 (.load (.n 895) (.n 13) 1) (by decide +kernel)
  have a2534 := h.atomAt 883 (.mul (.n 896) (.n 895) (.n 894)) (by decide +kernel)
  have a2535 := h.atomAt 884 (.add (.n 897) (.n 893) (.n 896)) (by decide +kernel)
  have a2536 := h.atomAt 885 (.load (.n 898) (.n 13) 2) (by decide +kernel)
  have a2537 := h.atomAt 886 (.add (.n 899) (.n 897) (.n 898)) (by decide +kernel)
  have a2538 := h.atomAt 887 (.load (.n 900) (.n 13) 3) (by decide +kernel)
  have a2539 := h.atomAt 888 (.const (.n 901) (word 0 0 0)) (by decide +kernel)
  have a2540 := h.atomAt 889 (.mul (.n 902) (.n 900) (.n 901)) (by decide +kernel)
  have a2541 := h.atomAt 890 (.add (.n 903) (.n 899) (.n 902)) (by decide +kernel)
  have a2542 := h.atomAt 891 (.load (.n 904) (.n 13) 4) (by decide +kernel)
  have a2543 := h.atomAt 892 (.const (.n 905) (word 0 0 0)) (by decide +kernel)
  have a2544 := h.atomAt 893 (.mul (.n 906) (.n 904) (.n 905)) (by decide +kernel)
  have a2545 := h.atomAt 894 (.add (.n 907) (.n 903) (.n 906)) (by decide +kernel)
  have a2546 := h.atomAt 895 (.load (.n 908) (.n 13) 5) (by decide +kernel)
  have a2547 := h.atomAt 896 (.const (.n 909) (word 0 0 0)) (by decide +kernel)
  have a2548 := h.atomAt 897 (.mul (.n 910) (.n 908) (.n 909)) (by decide +kernel)
  have a2549 := h.atomAt 898 (.add (.n 911) (.n 907) (.n 910)) (by decide +kernel)
  have a2550 := h.atomAt 899 (.load (.n 912) (.n 13) 6) (by decide +kernel)
  have a2551 := h.atomAt 900 (.const (.n 913) (word 0 0 0)) (by decide +kernel)
  have a2552 := h.atomAt 901 (.mul (.n 914) (.n 912) (.n 913)) (by decide +kernel)
  have a2553 := h.atomAt 902 (.add (.n 915) (.n 911) (.n 914)) (by decide +kernel)
  have a2554 := h.atomAt 903 (.load (.n 916) (.n 13) 7) (by decide +kernel)
  have a2555 := h.atomAt 904 (.const (.n 917) (word 0 0 0)) (by decide +kernel)
  have a2556 := h.atomAt 905 (.mul (.n 918) (.n 916) (.n 917)) (by decide +kernel)
  have a2557 := h.atomAt 906 (.add (.n 919) (.n 915) (.n 918)) (by decide +kernel)
  have a2558 := h.atomAt 907 (.load (.n 920) (.n 13) 8) (by decide +kernel)
  have a2559 := h.atomAt 908 (.const (.n 921) (word 0 0 0)) (by decide +kernel)
  have a2560 := h.atomAt 909 (.mul (.n 922) (.n 920) (.n 921)) (by decide +kernel)
  have a2561 := h.atomAt 910 (.add (.n 923) (.n 919) (.n 922)) (by decide +kernel)
  have a2562 := h.atomAt 911 (.load (.n 924) (.n 13) 9) (by decide +kernel)
  have a2563 := h.atomAt 912 (.const (.n 925) (word 0 0 0)) (by decide +kernel)
  have a2564 := h.atomAt 913 (.mul (.n 926) (.n 924) (.n 925)) (by decide +kernel)
  have a2565 := h.atomAt 914 (.add (.n 927) (.n 923) (.n 926)) (by decide +kernel)
  have a2566 := h.atomAt 915 (.load (.n 928) (.n 13) 10) (by decide +kernel)
  have a2567 := h.atomAt 916 (.const (.n 929) (word 0 0 0)) (by decide +kernel)
  have a2568 := h.atomAt 917 (.mul (.n 930) (.n 928) (.n 929)) (by decide +kernel)
  have a2569 := h.atomAt 918 (.add (.n 931) (.n 927) (.n 930)) (by decide +kernel)
  have a2570 := h.atomAt 919 (.load (.n 932) (.n 13) 11) (by decide +kernel)
  have a2571 := h.atomAt 920 (.const (.n 933) (word 0 0 0)) (by decide +kernel)
  have a2572 := h.atomAt 921 (.mul (.n 934) (.n 932) (.n 933)) (by decide +kernel)
  have a2573 := h.atomAt 922 (.add (.n 935) (.n 931) (.n 934)) (by decide +kernel)
  have a2574 := h.atomAt 923 (.load (.n 936) (.n 13) 12) (by decide +kernel)
  have a2575 := h.atomAt 924 (.const (.n 937) (word 0 0 0)) (by decide +kernel)
  have a2576 := h.atomAt 925 (.mul (.n 938) (.n 936) (.n 937)) (by decide +kernel)
  have a2577 := h.atomAt 926 (.add (.n 939) (.n 935) (.n 938)) (by decide +kernel)
  have a2578 := h.atomAt 927 (.load (.n 940) (.n 13) 13) (by decide +kernel)
  have a2579 := h.atomAt 928 (.const (.n 941) (word 0 0 0)) (by decide +kernel)
  have a2580 := h.atomAt 929 (.mul (.n 942) (.n 940) (.n 941)) (by decide +kernel)
  have a2581 := h.atomAt 930 (.add (.n 943) (.n 939) (.n 942)) (by decide +kernel)
  have b932 := h.atomAt 932 (.const (.n 945) (word 0 0 0)) (by decide +kernel)
  have b933 := h.atomAt 933 (.mul (.n 946) (.n 944) (.n 945)) (by decide +kernel)
  have b934 := h.atomAt 934 (.add (.n 947) (.n 943) (.n 946)) (by decide +kernel)
  have b936 := h.atomAt 936 (.const (.n 949) (word 0 0 0)) (by decide +kernel)
  have b937 := h.atomAt 937 (.mul (.n 950) (.n 948) (.n 949)) (by decide +kernel)
  have b938 := h.atomAt 938 (.add (.n 951) (.n 947) (.n 950)) (by decide +kernel)
  have a2582 := h.atomAt 939 (.add (.n 952) (.n 951) (.n 581)) (by decide +kernel)
  have a2583 := h.atomAt 940 (.add (.n 953) (.n 14) (.n 952)) (by decide +kernel)
  have a2584 := h.atomAt 941 (.mul (.n 954) (.n 887) (.n 953)) (by decide +kernel)
  have a2585 := h.atomAt 942 (.add (.n 955) (.n 874) (.n 954)) (by decide +kernel)
  have e2424 := tb_loadHolds_unique a2424 (hw 0 (by norm_num))
  have e2425 := tb_loadHolds_unique a2425 (hw 1 (by norm_num))
  have e2427 := tb_loadHolds_unique a2427 (hw 2 (by norm_num))
  have e2452 := tb_loadHolds_unique a2452 (hw 0 (by norm_num))
  have e2457 := tb_loadHolds_unique a2457 (hw 1 (by norm_num))
  have e2460 := tb_loadHolds_unique a2460 (hw 2 (by norm_num))
  have e2473 := tb_loadHolds_unique a2473 (hw 3 (by norm_num))
  have e2487 := tb_loadHolds_unique a2487 (hw 4 (by norm_num))
  have e2501 := tb_loadHolds_unique a2501 (hw 5 (by norm_num))
  have e2528 := tb_loadHolds_unique a2528 (hw 0 (by norm_num))
  have e2533 := tb_loadHolds_unique a2533 (hw 1 (by norm_num))
  have e2536 := tb_loadHolds_unique a2536 (hw 2 (by norm_num))
  have e2538 := tb_loadHolds_unique a2538 (hw 3 (by norm_num))
  have e2542 := tb_loadHolds_unique a2542 (hw 4 (by norm_num))
  have e2546 := tb_loadHolds_unique a2546 (hw 5 (by norm_num))
  have e2550 := tb_loadHolds_unique a2550 (hw 6 (by norm_num))
  have e2554 := tb_loadHolds_unique a2554 (hw 7 (by norm_num))
  have e2558 := tb_loadHolds_unique a2558 (hw 8 (by norm_num))
  have e2562 := tb_loadHolds_unique a2562 (hw 9 (by norm_num))
  have e2566 := tb_loadHolds_unique a2566 (hw 10 (by norm_num))
  have e2570 := tb_loadHolds_unique a2570 (hw 11 (by norm_num))
  have e2574 := tb_loadHolds_unique a2574 (hw 12 (by norm_num))
  have e2578 := tb_loadHolds_unique a2578 (hw 13 (by norm_num))
  simp only [Atom.Holds] at a2426 a2428 a2429 a2430 a2431 a2432 a2433 a2453 a2454 a2458
  simp only [Atom.Holds] at a2459 a2461 a2474 a2475 a2488 a2489 a2502 a2503 a2504 a2505
  simp only [Atom.Holds] at a2506 a2507 a2508 a2509 a2529 a2530 a2534 a2535 a2537 a2539
  simp only [Atom.Holds] at a2540 a2541 a2543 a2544 a2545 a2547 a2548 a2549 a2551 a2552
  simp only [Atom.Holds] at a2553 a2555 a2556 a2557 a2559 a2560 a2561 a2563 a2564 a2565
  simp only [Atom.Holds] at a2567 a2568 a2569 a2571 a2572 a2573 a2575 a2576 a2577 a2579
  simp only [Atom.Holds] at a2580 a2581 a2582 a2583 a2584 a2585 b932 b933 b934 b936 b937 b938
  simp only [e2424, e2425, a2426, e2427, a2428, a2429, a2430, a2431, a2432, a2433, e2452, a2453, a2454,
    e2457, a2458, a2459, e2460, a2461, e2473, a2474, a2475, e2487, a2488, a2489, e2501, a2502,
    a2503, a2504, a2505, a2506, a2507, a2508, a2509, e2528, a2529, a2530, e2533, a2534, a2535,
    e2536, a2537, e2538, a2539, a2540, a2541, e2542, a2543, a2544, a2545, e2546, a2547, a2548,
    a2549, e2550, a2551, a2552, a2553, e2554, a2555, a2556, a2557, e2558, a2559, a2560, a2561,
    e2562, a2563, a2564, a2565, e2566, a2567, a2568, a2569, e2570, a2571, a2572, a2573, e2574,
    a2575, a2576, a2577, e2578, a2579, a2580, a2581, a2582, a2583, a2584, a2585, b938, b937, b936,
    b934, b933, b932]
  rw [tb_word_zero, tb_word_gen, show (4 : ℕ) = 2 ^ 2 by norm_num, tb_word_two_pow (by norm_num)]
  ring

end
end LeanVM.Guest.B1.Tables
