/-
  LeanVM.Guest.B1.Tables.Vt.CountTotal

  `verify_tables`' count side total: the padding sum over its blocks, the selector sum and the GKR
  count value.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.PullTotal

/-!
# The count side's total (G:2316-2348)

The count side has no framework blocks and its blocks' padding coefficient is `1`.
`vt_count_total`: `bus_table_total[COUNT]`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- The count side's blocks: block, table, copy value, no padding terms. -/
def vtCountPadData : List (ℕ × ℕ × ℕ × List (ℕ × ℕ)) :=
  [(108, 0, 2077, []), (109, 0, 2082, []), (110, 0, 2087, []), (111, 0, 2092, []),
    (112, 1, 2101, []), (113, 1, 2110, []), (114, 1, 2119, []), (115, 1, 2128, []),
    (116, 2, 2137, []), (117, 2, 2146, []), (118, 3, 2155, []), (119, 3, 2164, []),
    (120, 3, 2173, []), (121, 3, 2182, []), (122, 4, 2191, []), (123, 4, 2200, []),
    (124, 4, 2209, []), (125, 4, 2218, []), (126, 5, 2227, []), (127, 5, 2236, []),
    (128, 5, 2245, []), (129, 5, 2254, []), (130, 5, 2263, []), (131, 5, 2272, []),
    (132, 5, 2281, []), (133, 5, 2290, []), (134, 5, 2299, []), (135, 5, 2308, []),
    (136, 5, 2317, []), (137, 5, 2326, []), (138, 5, 2335, []), (139, 5, 2344, []),
    (140, 5, 2353, []), (141, 5, 2362, []), (142, 5, 2371, []), (143, 5, 2380, []),
    (144, 5, 2389, []), (145, 5, 2398, []), (146, 5, 2407, []), (147, 5, 2416, []),
    (148, 5, 2425, []), (149, 5, 2434, []), (150, 5, 2443, []), (151, 5, 2452, []),
    (152, 5, 2461, [])]

set_option maxRecDepth 100000 in
/-- **The count side's total.** -/
theorem vt_count_total {rd : Reader} {σ : Val} (h : VtH rd σ) (W : ℕ → E) :
    σ (.n 2515) = vtPadSum (fun c ↦ σ (.n c)) (fun t ↦ σ (.n (vtPadV t))) W 1 vtCountPadData +
      (1 + σ (.n 2460)) + σ (.n 27) := by
  have a5098 := h.atomAt 2533 (.add (.n 2462) (.n 2077) (.n 2082)) (by decide +kernel)
  have a5099 := h.atomAt 2534 (.add (.n 2463) (.n 2462) (.n 2087)) (by decide +kernel)
  have a5100 := h.atomAt 2535 (.add (.n 2464) (.n 2463) (.n 2092)) (by decide +kernel)
  have a5101 := h.atomAt 2536 (.mul (.n 2465) (.n 587) (.n 2464)) (by decide +kernel)
  have a5102 := h.atomAt 2537 (.add (.n 2466) (.n 2101) (.n 2110)) (by decide +kernel)
  have a5103 := h.atomAt 2538 (.add (.n 2467) (.n 2466) (.n 2119)) (by decide +kernel)
  have a5104 := h.atomAt 2539 (.add (.n 2468) (.n 2467) (.n 2128)) (by decide +kernel)
  have a5105 := h.atomAt 2540 (.mul (.n 2469) (.n 600) (.n 2468)) (by decide +kernel)
  have a5106 := h.atomAt 2541 (.add (.n 2470) (.n 2465) (.n 2469)) (by decide +kernel)
  have a5107 := h.atomAt 2542 (.add (.n 2471) (.n 2137) (.n 2146)) (by decide +kernel)
  have a5108 := h.atomAt 2543 (.mul (.n 2472) (.n 613) (.n 2471)) (by decide +kernel)
  have a5109 := h.atomAt 2544 (.add (.n 2473) (.n 2470) (.n 2472)) (by decide +kernel)
  have a5110 := h.atomAt 2545 (.add (.n 2474) (.n 2155) (.n 2164)) (by decide +kernel)
  have a5111 := h.atomAt 2546 (.add (.n 2475) (.n 2474) (.n 2173)) (by decide +kernel)
  have a5112 := h.atomAt 2547 (.add (.n 2476) (.n 2475) (.n 2182)) (by decide +kernel)
  have a5113 := h.atomAt 2548 (.mul (.n 2477) (.n 626) (.n 2476)) (by decide +kernel)
  have a5114 := h.atomAt 2549 (.add (.n 2478) (.n 2473) (.n 2477)) (by decide +kernel)
  have a5115 := h.atomAt 2550 (.add (.n 2479) (.n 2191) (.n 2200)) (by decide +kernel)
  have a5116 := h.atomAt 2551 (.add (.n 2480) (.n 2479) (.n 2209)) (by decide +kernel)
  have a5117 := h.atomAt 2552 (.add (.n 2481) (.n 2480) (.n 2218)) (by decide +kernel)
  have a5118 := h.atomAt 2553 (.mul (.n 2482) (.n 639) (.n 2481)) (by decide +kernel)
  have a5119 := h.atomAt 2554 (.add (.n 2483) (.n 2478) (.n 2482)) (by decide +kernel)
  have a5120 := h.atomAt 2555 (.add (.n 2484) (.n 2227) (.n 2236)) (by decide +kernel)
  have a5121 := h.atomAt 2556 (.add (.n 2485) (.n 2484) (.n 2245)) (by decide +kernel)
  have a5122 := h.atomAt 2557 (.add (.n 2486) (.n 2485) (.n 2254)) (by decide +kernel)
  have a5123 := h.atomAt 2558 (.add (.n 2487) (.n 2486) (.n 2263)) (by decide +kernel)
  have a5124 := h.atomAt 2559 (.add (.n 2488) (.n 2487) (.n 2272)) (by decide +kernel)
  have a5125 := h.atomAt 2560 (.add (.n 2489) (.n 2488) (.n 2281)) (by decide +kernel)
  have a5126 := h.atomAt 2561 (.add (.n 2490) (.n 2489) (.n 2290)) (by decide +kernel)
  have a5127 := h.atomAt 2562 (.add (.n 2491) (.n 2490) (.n 2299)) (by decide +kernel)
  have a5128 := h.atomAt 2563 (.add (.n 2492) (.n 2491) (.n 2308)) (by decide +kernel)
  have a5129 := h.atomAt 2564 (.add (.n 2493) (.n 2492) (.n 2317)) (by decide +kernel)
  have a5130 := h.atomAt 2565 (.add (.n 2494) (.n 2493) (.n 2326)) (by decide +kernel)
  have a5131 := h.atomAt 2566 (.add (.n 2495) (.n 2494) (.n 2335)) (by decide +kernel)
  have a5132 := h.atomAt 2567 (.add (.n 2496) (.n 2495) (.n 2344)) (by decide +kernel)
  have a5133 := h.atomAt 2568 (.add (.n 2497) (.n 2496) (.n 2353)) (by decide +kernel)
  have a5134 := h.atomAt 2569 (.add (.n 2498) (.n 2497) (.n 2362)) (by decide +kernel)
  have a5135 := h.atomAt 2570 (.add (.n 2499) (.n 2498) (.n 2371)) (by decide +kernel)
  have a5136 := h.atomAt 2571 (.add (.n 2500) (.n 2499) (.n 2380)) (by decide +kernel)
  have a5137 := h.atomAt 2572 (.add (.n 2501) (.n 2500) (.n 2389)) (by decide +kernel)
  have a5138 := h.atomAt 2573 (.add (.n 2502) (.n 2501) (.n 2398)) (by decide +kernel)
  have a5139 := h.atomAt 2574 (.add (.n 2503) (.n 2502) (.n 2407)) (by decide +kernel)
  have a5140 := h.atomAt 2575 (.add (.n 2504) (.n 2503) (.n 2416)) (by decide +kernel)
  have a5141 := h.atomAt 2576 (.add (.n 2505) (.n 2504) (.n 2425)) (by decide +kernel)
  have a5142 := h.atomAt 2577 (.add (.n 2506) (.n 2505) (.n 2434)) (by decide +kernel)
  have a5143 := h.atomAt 2578 (.add (.n 2507) (.n 2506) (.n 2443)) (by decide +kernel)
  have a5144 := h.atomAt 2579 (.add (.n 2508) (.n 2507) (.n 2452)) (by decide +kernel)
  have a5145 := h.atomAt 2580 (.add (.n 2509) (.n 2508) (.n 2461)) (by decide +kernel)
  have a5146 := h.atomAt 2581 (.mul (.n 2510) (.n 652) (.n 2509)) (by decide +kernel)
  have a5147 := h.atomAt 2582 (.add (.n 2511) (.n 2483) (.n 2510)) (by decide +kernel)
  have a5148 := h.atomAt 2583 (.const (.n 2512) (word 1 0 0)) (by decide +kernel)
  have a5149 := h.atomAt 2584 (.add (.n 2513) (.n 2512) (.n 2460)) (by decide +kernel)
  have a5150 := h.atomAt 2585 (.add (.n 2514) (.n 2511) (.n 2513)) (by decide +kernel)
  have a5151 := h.atomAt 2586 (.add (.n 2515) (.n 2514) (.n 27)) (by decide +kernel)
  simp only [Atom.Holds] at a5098 a5099 a5100 a5101 a5102 a5103 a5104 a5105 a5106 a5107
  simp only [Atom.Holds] at a5108 a5109 a5110 a5111 a5112 a5113 a5114 a5115 a5116 a5117
  simp only [Atom.Holds] at a5118 a5119 a5120 a5121 a5122 a5123 a5124 a5125 a5126 a5127
  simp only [Atom.Holds] at a5128 a5129 a5130 a5131 a5132 a5133 a5134 a5135 a5136 a5137
  simp only [Atom.Holds] at a5138 a5139 a5140 a5141 a5142 a5143 a5144 a5145 a5146 a5147
  simp only [Atom.Holds] at a5148 a5149 a5150 a5151
  simp only [a5098, a5099, a5100, a5101, a5102, a5103, a5104, a5105, a5106, a5107, a5108, a5109, a5110,
    a5111, a5112, a5113, a5114, a5115, a5116, a5117, a5118, a5119, a5120, a5121, a5122, a5123,
    a5124, a5125, a5126, a5127, a5128, a5129, a5130, a5131, a5132, a5133, a5134, a5135, a5136,
    a5137, a5138, a5139, a5140, a5141, a5142, a5143, a5144, a5145, a5146, a5147, a5148, a5149,
    a5150, a5151]
  simp (config := { decide := true }) only [vtPadSum, vtPadTable, vtCountPadData, vtPadV,
    List.filter_cons, List.filter_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    ↓reduceIte, add_zero, mul_one]
  rw [tb_word_one]
  ring

end
end LeanVM.Guest.B1.Tables
