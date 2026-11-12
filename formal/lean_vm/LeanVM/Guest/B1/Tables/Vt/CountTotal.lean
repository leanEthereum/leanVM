/-
  LeanVM.Guest.B1.Tables.Vt.CountTotal

  `verify_tables`' count side total: the padding sum over its blocks (counts alone, at `β = 0`),
  the selector sum and the GKR count value.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.PullTotal

/-!
# The count side's total (G:2471-2530)

`vtCountPadData` lists the count side's blocks with their table and copy. `vt_count_total`:
`bus_table_total[COUNT]` is the padding sum, `1 + selector_sum` and the GKR count value.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- The count side's blocks: block, table, copy value, no padding terms. -/
def vtCountPadData : List (ℕ × ℕ × ℕ × List (ℕ × ℕ)) :=
  [(108, 0, 1440, []), (109, 0, 1445, []), (110, 0, 1450, []), (111, 0, 1455, []),
    (112, 1, 1464, []), (113, 1, 1473, []), (114, 1, 1482, []), (115, 1, 1491, []),
    (116, 2, 1500, []), (117, 2, 1509, []), (118, 3, 1518, []), (119, 3, 1527, []),
    (120, 3, 1536, []), (121, 3, 1545, []), (122, 4, 1554, []), (123, 4, 1563, []),
    (124, 4, 1572, []), (125, 4, 1581, []), (126, 5, 1590, []), (127, 5, 1599, []),
    (128, 5, 1608, []), (129, 5, 1617, []), (130, 5, 1626, []), (131, 5, 1635, []),
    (132, 5, 1644, []), (133, 5, 1653, []), (134, 5, 1662, []), (135, 5, 1671, []),
    (136, 5, 1680, []), (137, 5, 1689, []), (138, 5, 1698, []), (139, 5, 1707, []),
    (140, 5, 1716, []), (141, 5, 1725, []), (142, 5, 1734, []), (143, 5, 1743, []),
    (144, 5, 1752, []), (145, 5, 1761, []), (146, 5, 1770, []), (147, 5, 1779, []),
    (148, 5, 1788, []), (149, 5, 1797, []), (150, 5, 1806, []), (151, 5, 1815, []),
    (152, 5, 1824, [])]

set_option maxRecDepth 100000 in
theorem vt_countPadT0 {rd : Reader} {σ : Val} (h : VtH rd σ) (W : ℕ → E) :
    σ (.n 2491) = vtPadTable (fun c ↦ σ (.n c)) W 1 vtCountPadData 0 := by
  have a2536 := h.atomAt 2536 (.add (.n 2489) (.n 1440) (.n 1445)) (by decide +kernel)
  have a2537 := h.atomAt 2537 (.add (.n 2490) (.n 2489) (.n 1450)) (by decide +kernel)
  have a2538 := h.atomAt 2538 (.add (.n 2491) (.n 2490) (.n 1455)) (by decide +kernel)
  simp only [Atom.Holds] at a2536 a2537 a2538
  simp (config := { decide := true }) only [vtPadTable, vtCountPadData, List.filter_cons,
    List.filter_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ↓reduceIte,
    mul_one, add_zero]
  simp only [a2536, a2537, a2538]
  ring

set_option maxRecDepth 100000 in
theorem vt_countPadT1 {rd : Reader} {σ : Val} (h : VtH rd σ) (W : ℕ → E) :
    σ (.n 2495) = vtPadTable (fun c ↦ σ (.n c)) W 1 vtCountPadData 1 := by
  have a2540 := h.atomAt 2540 (.add (.n 2493) (.n 1464) (.n 1473)) (by decide +kernel)
  have a2541 := h.atomAt 2541 (.add (.n 2494) (.n 2493) (.n 1482)) (by decide +kernel)
  have a2542 := h.atomAt 2542 (.add (.n 2495) (.n 2494) (.n 1491)) (by decide +kernel)
  simp only [Atom.Holds] at a2540 a2541 a2542
  simp (config := { decide := true }) only [vtPadTable, vtCountPadData, List.filter_cons,
    List.filter_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ↓reduceIte,
    mul_one, add_zero]
  simp only [a2540, a2541, a2542]
  ring

set_option maxRecDepth 100000 in
theorem vt_countPadT2 {rd : Reader} {σ : Val} (h : VtH rd σ) (W : ℕ → E) :
    σ (.n 2498) = vtPadTable (fun c ↦ σ (.n c)) W 1 vtCountPadData 2 := by
  have a2545 := h.atomAt 2545 (.add (.n 2498) (.n 1500) (.n 1509)) (by decide +kernel)
  simp only [Atom.Holds] at a2545
  simp (config := { decide := true }) only [vtPadTable, vtCountPadData, List.filter_cons,
    List.filter_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ↓reduceIte,
    mul_one, add_zero]
  simp only [a2545]

set_option maxRecDepth 100000 in
theorem vt_countPadT3 {rd : Reader} {σ : Val} (h : VtH rd σ) (W : ℕ → E) :
    σ (.n 2503) = vtPadTable (fun c ↦ σ (.n c)) W 1 vtCountPadData 3 := by
  have a2548 := h.atomAt 2548 (.add (.n 2501) (.n 1518) (.n 1527)) (by decide +kernel)
  have a2549 := h.atomAt 2549 (.add (.n 2502) (.n 2501) (.n 1536)) (by decide +kernel)
  have a2550 := h.atomAt 2550 (.add (.n 2503) (.n 2502) (.n 1545)) (by decide +kernel)
  simp only [Atom.Holds] at a2548 a2549 a2550
  simp (config := { decide := true }) only [vtPadTable, vtCountPadData, List.filter_cons,
    List.filter_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ↓reduceIte,
    mul_one, add_zero]
  simp only [a2548, a2549, a2550]
  ring

set_option maxRecDepth 100000 in
theorem vt_countPadT4 {rd : Reader} {σ : Val} (h : VtH rd σ) (W : ℕ → E) :
    σ (.n 2508) = vtPadTable (fun c ↦ σ (.n c)) W 1 vtCountPadData 4 := by
  have a2553 := h.atomAt 2553 (.add (.n 2506) (.n 1554) (.n 1563)) (by decide +kernel)
  have a2554 := h.atomAt 2554 (.add (.n 2507) (.n 2506) (.n 1572)) (by decide +kernel)
  have a2555 := h.atomAt 2555 (.add (.n 2508) (.n 2507) (.n 1581)) (by decide +kernel)
  simp only [Atom.Holds] at a2553 a2554 a2555
  simp (config := { decide := true }) only [vtPadTable, vtCountPadData, List.filter_cons,
    List.filter_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ↓reduceIte,
    mul_one, add_zero]
  simp only [a2553, a2554, a2555]
  ring

set_option maxRecDepth 100000 in
theorem vt_countPadT5 {rd : Reader} {σ : Val} (h : VtH rd σ) (W : ℕ → E) :
    σ (.n 2536) = vtPadTable (fun c ↦ σ (.n c)) W 1 vtCountPadData 5 := by
  have a2558 := h.atomAt 2558 (.add (.n 2511) (.n 1590) (.n 1599)) (by decide +kernel)
  have a2559 := h.atomAt 2559 (.add (.n 2512) (.n 2511) (.n 1608)) (by decide +kernel)
  have a2560 := h.atomAt 2560 (.add (.n 2513) (.n 2512) (.n 1617)) (by decide +kernel)
  have a2561 := h.atomAt 2561 (.add (.n 2514) (.n 2513) (.n 1626)) (by decide +kernel)
  have a2562 := h.atomAt 2562 (.add (.n 2515) (.n 2514) (.n 1635)) (by decide +kernel)
  have a2563 := h.atomAt 2563 (.add (.n 2516) (.n 2515) (.n 1644)) (by decide +kernel)
  have a2564 := h.atomAt 2564 (.add (.n 2517) (.n 2516) (.n 1653)) (by decide +kernel)
  have a2565 := h.atomAt 2565 (.add (.n 2518) (.n 2517) (.n 1662)) (by decide +kernel)
  have a2566 := h.atomAt 2566 (.add (.n 2519) (.n 2518) (.n 1671)) (by decide +kernel)
  have a2567 := h.atomAt 2567 (.add (.n 2520) (.n 2519) (.n 1680)) (by decide +kernel)
  have a2568 := h.atomAt 2568 (.add (.n 2521) (.n 2520) (.n 1689)) (by decide +kernel)
  have a2569 := h.atomAt 2569 (.add (.n 2522) (.n 2521) (.n 1698)) (by decide +kernel)
  have a2570 := h.atomAt 2570 (.add (.n 2523) (.n 2522) (.n 1707)) (by decide +kernel)
  have a2571 := h.atomAt 2571 (.add (.n 2524) (.n 2523) (.n 1716)) (by decide +kernel)
  have a2572 := h.atomAt 2572 (.add (.n 2525) (.n 2524) (.n 1725)) (by decide +kernel)
  have a2573 := h.atomAt 2573 (.add (.n 2526) (.n 2525) (.n 1734)) (by decide +kernel)
  have a2574 := h.atomAt 2574 (.add (.n 2527) (.n 2526) (.n 1743)) (by decide +kernel)
  have a2575 := h.atomAt 2575 (.add (.n 2528) (.n 2527) (.n 1752)) (by decide +kernel)
  have a2576 := h.atomAt 2576 (.add (.n 2529) (.n 2528) (.n 1761)) (by decide +kernel)
  have a2577 := h.atomAt 2577 (.add (.n 2530) (.n 2529) (.n 1770)) (by decide +kernel)
  have a2578 := h.atomAt 2578 (.add (.n 2531) (.n 2530) (.n 1779)) (by decide +kernel)
  have a2579 := h.atomAt 2579 (.add (.n 2532) (.n 2531) (.n 1788)) (by decide +kernel)
  have a2580 := h.atomAt 2580 (.add (.n 2533) (.n 2532) (.n 1797)) (by decide +kernel)
  have a2581 := h.atomAt 2581 (.add (.n 2534) (.n 2533) (.n 1806)) (by decide +kernel)
  have a2582 := h.atomAt 2582 (.add (.n 2535) (.n 2534) (.n 1815)) (by decide +kernel)
  have a2583 := h.atomAt 2583 (.add (.n 2536) (.n 2535) (.n 1824)) (by decide +kernel)
  simp only [Atom.Holds] at a2558 a2559 a2560 a2561 a2562 a2563 a2564 a2565 a2566 a2567
  simp only [Atom.Holds] at a2568 a2569 a2570 a2571 a2572 a2573 a2574 a2575 a2576 a2577
  simp only [Atom.Holds] at a2578 a2579 a2580 a2581 a2582 a2583
  simp (config := { decide := true }) only [vtPadTable, vtCountPadData, List.filter_cons,
    List.filter_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ↓reduceIte,
    mul_one, add_zero]
  simp only [a2558, a2559, a2560, a2561, a2562, a2563, a2564, a2565, a2566, a2567, a2568, a2569,
    a2570, a2571, a2572, a2573, a2574, a2575, a2576, a2577, a2578, a2579, a2580, a2581, a2582,
    a2583]
  ring

set_option maxRecDepth 100000 in
/-- **The count side's padding sum.** -/
theorem vt_count_pad {rd : Reader} {σ : Val} (h : VtH rd σ) (W : ℕ → E) :
    σ (.n 2538) = vtPadSum (fun c ↦ σ (.n c)) (fun t ↦ σ (.n (vtPadV t))) W 1 vtCountPadData := by
  have a2539 := h.atomAt 2539 (.mul (.n 2492) (.n 583) (.n 2491)) (by decide +kernel)
  have a2543 := h.atomAt 2543 (.mul (.n 2496) (.n 596) (.n 2495)) (by decide +kernel)
  have a2544 := h.atomAt 2544 (.add (.n 2497) (.n 2492) (.n 2496)) (by decide +kernel)
  have a2546 := h.atomAt 2546 (.mul (.n 2499) (.n 609) (.n 2498)) (by decide +kernel)
  have a2547 := h.atomAt 2547 (.add (.n 2500) (.n 2497) (.n 2499)) (by decide +kernel)
  have a2551 := h.atomAt 2551 (.mul (.n 2504) (.n 622) (.n 2503)) (by decide +kernel)
  have a2552 := h.atomAt 2552 (.add (.n 2505) (.n 2500) (.n 2504)) (by decide +kernel)
  have a2556 := h.atomAt 2556 (.mul (.n 2509) (.n 635) (.n 2508)) (by decide +kernel)
  have a2557 := h.atomAt 2557 (.add (.n 2510) (.n 2505) (.n 2509)) (by decide +kernel)
  have a2584 := h.atomAt 2584 (.mul (.n 2537) (.n 648) (.n 2536)) (by decide +kernel)
  have a2585 := h.atomAt 2585 (.add (.n 2538) (.n 2510) (.n 2537)) (by decide +kernel)
  simp only [Atom.Holds] at a2539 a2543 a2544 a2546 a2547 a2551 a2552 a2556 a2557 a2584
  simp only [Atom.Holds] at a2585
  simp only [a2539, a2543, a2544, a2546, a2547, a2551, a2552, a2556, a2557, a2584, a2585]
  simp only [vtPadSum, vtPadV]
  rw [← vt_countPadT0 h W, ← vt_countPadT1 h W, ← vt_countPadT2 h W, ← vt_countPadT3 h W,
    ← vt_countPadT4 h W, ← vt_countPadT5 h W]

/-- **The count side's total.** -/
theorem vt_count_total {rd : Reader} {σ : Val} (h : VtH rd σ) :
    σ (.n 2543) = σ (.n 2538) + (1 + σ (.n 1825)) + σ (.n 2542) := by
  have a2586 := h.atomAt 2586 (.const (.n 2539) (word 1 0)) (by decide +kernel)
  have a2587 := h.atomAt 2587 (.add (.n 2540) (.n 2539) (.n 1825)) (by decide +kernel)
  have a2588 := h.atomAt 2588 (.add (.n 2541) (.n 2538) (.n 2540)) (by decide +kernel)
  have a2590 := h.atomAt 2590 (.add (.n 2543) (.n 2541) (.n 2542)) (by decide +kernel)
  simp only [Atom.Holds] at a2586 a2587 a2588 a2590
  rw [a2590, a2588, a2587, a2586, tb_word_one]

/-- The count side's selector sum is the running sum's copy. -/
theorem vt_count_sel {rd : Reader} {σ : Val} (h : VtH rd σ) : σ (.n 1825) = σ (.n 1823) := by
  have a := h.atomAt 1912 (.copy (.n 1825) (.n 1823)) (by decide +kernel)
  simpa only [Atom.Holds] using a

end
end LeanVM.Guest.B1.Tables
