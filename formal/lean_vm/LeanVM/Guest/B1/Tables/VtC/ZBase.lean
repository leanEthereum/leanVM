/-
  LeanVM.Guest.B1.Tables.VtC.ZBase

  The table sumcheck's honest rounds (from the transcript words, the capacity and the target), the
  buffers they fill, and `verify_tables`' statements `2587 ..< 2688` and `6353 ..< 6398`.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.Hon
public import LeanVM.Guest.B1.Tables.VtC.ZLoop10
public import LeanVM.Guest.B1.Tables.Vt.ZcRun
public import LeanVM.Guest.B1.Tables.Vt.Pi

/-!
# The table sumcheck, honestly

`zcRec cap0 cl0 xs j`: the capacity and the claim before round `j` of the plain degree-4
sumcheck from the capacity `cap0` and the claim `cl0`, round `j` reading the words
`xs[3j], xs[3j+1], xs[3j+2]` (`c0, c2, c3`); `zcCh`: round `j`'s challenge. The buffers:
`zcRoundsW` (record `j ≤ n`: the capacity, the cursor `cur0·g^(3j)`, the claim), `zcCprodW`
(the challenges' running products), `zcChis` (the challenges, last first, as `chi` holds them).

`zc_run`: the rounds are the specification's `sumcheck cl0 4 (replicate n none)`.
`zc_l10B`: on a memory holding the buffers and the words, every iteration of `__loop9` has
its facts.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

/-! ## The statements -/

/-- `verify_tables`' statements `2587 ..< 2688` (G:2397-2447). -/
noncomputable def zBlk : List Stmt := [
    .atom (.hint (.witness "zc_tau_max" (.stack [.n 2516]))),
    .atom (.const (.n 2517) (word 4294967296 0)),
    .atom (.mul (.n 2516) (.n 2518) (.n 30)),
    .atom (.rangeCheck (.n 2518) (.n 2519) (.n 2520) (.n 2521) (.n 2517)),
    .atom (.add (.n 2522) (.n 2516) (.n 30)),
    .atom (.const (.n 2523) (word 4294967296 0)),
    .atom (.mul (.n 2516) (.n 2524) (.n 31)),
    .atom (.rangeCheck (.n 2524) (.n 2525) (.n 2526) (.n 2527) (.n 2523)),
    .atom (.add (.n 2528) (.n 2516) (.n 31)),
    .atom (.mul (.n 2529) (.n 2522) (.n 2528)),
    .atom (.const (.n 2530) (word 4294967296 0)),
    .atom (.mul (.n 2516) (.n 2531) (.n 32)),
    .atom (.rangeCheck (.n 2531) (.n 2532) (.n 2533) (.n 2534) (.n 2530)),
    .atom (.add (.n 2535) (.n 2516) (.n 32)),
    .atom (.mul (.n 2536) (.n 2529) (.n 2535)),
    .atom (.const (.n 2537) (word 4294967296 0)),
    .atom (.mul (.n 2516) (.n 2538) (.n 33)),
    .atom (.rangeCheck (.n 2538) (.n 2539) (.n 2540) (.n 2541) (.n 2537)),
    .atom (.add (.n 2542) (.n 2516) (.n 33)),
    .atom (.mul (.n 2543) (.n 2536) (.n 2542)),
    .atom (.const (.n 2544) (word 4294967296 0)),
    .atom (.mul (.n 2516) (.n 2545) (.n 34)),
    .atom (.rangeCheck (.n 2545) (.n 2546) (.n 2547) (.n 2548) (.n 2544)),
    .atom (.add (.n 2549) (.n 2516) (.n 34)),
    .atom (.mul (.n 2550) (.n 2543) (.n 2549)),
    .atom (.const (.n 2551) (word 4294967296 0)),
    .atom (.mul (.n 2516) (.n 2552) (.n 35)),
    .atom (.rangeCheck (.n 2552) (.n 2553) (.n 2554) (.n 2555) (.n 2551)),
    .atom (.add (.n 2556) (.n 2516) (.n 35)),
    .atom (.mul (.n 2557) (.n 2550) (.n 2556)),
    .atom (.const (.n 2558) (word 0 0)),
    .atom (.assertEq (.n 2557) (.n 2558)),
    .atom (.const (.n 2559) (word 4294967296 0)),
    .atom (.mul (.n 9) (.n 2560) (.n 2516)),
    .atom (.rangeCheck (.n 2560) (.n 2561) (.n 2562) (.n 2563) (.n 2559)),
    .atom (.const (.n 2564) (word 1 0)),
    .atom (.const (.n 2565) (word 0 0)),
    .atom (.const (.n 2566) (word 0 0)),
    .atom (.const (.n 2567) (word 0 0)),
    .atom (.const (.n 2568) (word 0 0)),
    .atom (.keccak [.n 1905, .n 1907, .n 2565, .n 2565, .n 2565, .n 2566, .n 2567, .n 2568, .n 1893, .n 1894, .n 1895, .n 1896, .n 1897] [.n 2569, .n 2570, .n 2571, .n 2572, .n 2573, .n 2574, .n 2575, .n 2576, .n 2577, .n 2578, .n 2579, .n 2580, .n 2581] false false),
    .atom (.hint (.limbs (.n 2570) [.n 2582])),
    .atom (.add (.n 2583) (.n 2570) (.n 2582)),
    .atom (.const (.n 2584) (word 1 0 1)),
    .atom (.mul (.n 2585) (.n 2583) (.n 2584)),
    .atom (.assertInK (.n 2582) (.n 2585)),
    .atom (.const (.n 2586) (word 0 0 1)),
    .atom (.mul (.n 2587) (.n 2586) (.n 2582)),
    .atom (.add (.n 2588) (.n 2569) (.n 2587)),
    .atom (.const (.n 2589) (word 1 0)),
    .atom (.mul (.n 2590) (.n 2589) (.n 2588)),
    .atom (.mul (.n 2591) (.n 2590) (.n 2588)),
    .atom (.mul (.n 2592) (.n 2591) (.n 2588)),
    .atom (.mul (.n 2593) (.n 2592) (.n 2588)),
    .atom (.mul (.n 2594) (.n 2591) (.n 1820)),
    .atom (.mul (.n 2595) (.n 2592) (.n 2073)),
    .atom (.add (.n 2596) (.n 2594) (.n 2595)),
    .atom (.mul (.n 2597) (.n 2593) (.n 2515)),
    .atom (.add (.n 2598) (.n 2596) (.n 2597)),
    .atom (.const (.n 2599) (word 2 0)),
    .atom (.mul (.n 2600) (.n 2516) (.n 2599)),
    .atom (.mul (.n 2601) (.n 2600) (.n 2600)),
    .atom (.mul (.n 2602) (.n 2601) (.n 2600)),
    .atom (.mul (.n 2603) (.n 2602) (.n 2602)),
    .atom (.mul (.n 2604) (.n 2603) (.n 2600)),
    .atom (.hint (.allocDyn (.n 2605) (.n 2604))),
    .atom (.const (.n 2606) (word 2 0)),
    .atom (.mul (.n 2607) (.n 2516) (.n 2606)),
    .atom (.hint (.allocDyn (.n 2608) (.n 2607))),
    .atom (.load (.n 2577) (.n 2605) 0),
    .atom (.load (.n 2578) (.n 2605) 1),
    .atom (.load (.n 2579) (.n 2605) 2),
    .atom (.load (.n 2580) (.n 2605) 3),
    .atom (.load (.n 2581) (.n 2605) 4),
    .atom (.const (.n 2609) (word 32 0)),
    .atom (.mul (.n 2610) (.n 5) (.n 2609)),
    .atom (.load (.n 2610) (.n 2605) 5),
    .atom (.load (.n 2598) (.n 2605) 6),
    .atom (.const (.n 2611) (word 1 0)),
    .atom (.load (.n 2611) (.n 2608) 0),
    .atom (.const (.n 2612) (word 1 0)),
    .atom (.add (.n 2613) (.n 2612) (.n 2516)),
    .atom (.const (.n 2614) (word 1 0)),
    .callIf (.n 2613) "__loop9" [.n 2614, .n 2516, .n 2605, .n 16, .n 2516, .n 2608],
    .atom (.mul (.n 2615) (.n 2516) (.n 2516)),
    .atom (.mul (.n 2616) (.n 2615) (.n 2516)),
    .atom (.mul (.n 2617) (.n 2616) (.n 2616)),
    .atom (.mul (.n 2618) (.n 2617) (.n 2516)),
    .atom (.mul (.n 2619) (.n 2605) (.n 2618)),
    .atom (.load (.n 2620) (.n 2619) 0),
    .atom (.load (.n 2621) (.n 2619) 1),
    .atom (.load (.n 2622) (.n 2619) 2),
    .atom (.load (.n 2623) (.n 2619) 3),
    .atom (.load (.n 2624) (.n 2619) 4),
    .atom (.load (.n 2625) (.n 2619) 5),
    .atom (.load (.n 2626) (.n 2619) 6),
    .atom (.const (.n 2627) (word 2 0)),
    .atom (.mul (.n 2628) (.n 2516) (.n 2627)),
    .atom (.hint (.allocDyn (.n 2629) (.n 2628))),
    .atom (.const (.n 2630) (word 1 0)),
    .call "eq_prefix_chain" [.n 2629, .n 2630, .n 16, .n 703, .n 2516] []]

/-- `verify_tables`' statements `6353 ..< 6398` (G:2550-2563). -/
noncomputable def zTail : List Stmt := [
    .atom (.const (.n 6922) (word 0 0)),
    .atom (.const (.n 6923) (word 0 0)),
    .atom (.keccak [.n 5712, .n 5714, .n 5723, .n 5725, .n 5734, .n 5736, .n 6922, .n 6923, .n 5700, .n 5701, .n 5702, .n 5703, .n 5704] [.n 6924, .n 6925, .n 6926, .n 6927, .n 6928, .n 6929, .n 6930, .n 6931, .n 6932, .n 6933, .n 6934, .n 6935, .n 6936] false false),
    .atom (.hint (.limbs (.n 6925) [.n 6937])),
    .atom (.add (.n 6938) (.n 6925) (.n 6937)),
    .atom (.const (.n 6939) (word 1 0 1)),
    .atom (.mul (.n 6940) (.n 6938) (.n 6939)),
    .atom (.assertInK (.n 6937) (.n 6940)),
    .atom (.const (.n 6941) (word 0 0 1)),
    .atom (.mul (.n 6942) (.n 6941) (.n 6937)),
    .atom (.add (.n 6943) (.n 6924) (.n 6942)),
    .atom (.hint (.limbs (.n 6) [.n 6944])),
    .atom (.add (.n 6945) (.n 6) (.n 6944)),
    .atom (.const (.n 6946) (word 1 0 1)),
    .atom (.mul (.n 6947) (.n 6945) (.n 6946)),
    .atom (.assertInK (.n 6944) (.n 6947)),
    .atom (.copy (.n 6948) (.n 6944)),
    .atom (.hint (.limbs (.n 7) [.n 6949])),
    .atom (.add (.n 6950) (.n 7) (.n 6949)),
    .atom (.const (.n 6951) (word 1 0 1)),
    .atom (.mul (.n 6952) (.n 6950) (.n 6951)),
    .atom (.assertInK (.n 6949) (.n 6952)),
    .atom (.copy (.n 6953) (.n 6949)),
    .atom (.add (.n 6954) (.n 6948) (.n 6953)),
    .atom (.mul (.n 6955) (.n 6943) (.n 6954)),
    .atom (.add (.n 6956) (.n 6948) (.n 6955)),
    .atom (.load (.n 6956) (.n 15) 164),
    .atom (.add (.n 6957) (.n 6947) (.n 6952)),
    .atom (.mul (.n 6958) (.n 6943) (.n 6957)),
    .atom (.add (.n 6959) (.n 6947) (.n 6958)),
    .atom (.load (.n 6959) (.n 15) 165),
    .atom (.const (.n 6960) (word 0 0)),
    .atom (.load (.n 6960) (.n 15) 166),
    .atom (.copy (.n 6961) (.n 6932)),
    .atom (.copy (.n 6962) (.n 6933)),
    .atom (.copy (.n 6963) (.n 6934)),
    .atom (.copy (.n 6964) (.n 6935)),
    .atom (.copy (.n 6965) (.n 6936)),
    .atom (.const (.n 6966) (word 697932185600 0)),
    .atom (.mul (.n 6967) (.n 2625) (.n 6966)),
    .atom (.copy (.n 6968) (.n 6967)),
    .atom (.copy (.n 6969) (.n 2516)),
    .atom (.copy (.n 6970) (.n 581)),
    .atom (.copy (.n 6971) (.n 6943)),
    .atom (.copy (.n 6972) (.n 2625))]

theorem zBlk_at : tbStmtsEqb zBlk ((vtPre.drop 2587).take zBlk.length) = true := by
  simp only [vtPre_drop]; decide +kernel

theorem zTail_at : tbStmtsEqb zTail ((vtPre.drop 6353).take zTail.length) = true := by
  simp only [vtPre_drop]; decide +kernel

/-! ## The honest rounds -/

/-- The capacity and the claim before round `j`. -/
def zcRec (cap0 : List E) (cl0 : E) (xs : List E) : ℕ → List E × E
  | 0 => (cap0, cl0)
  | j + 1 =>
    let r := zcRec cap0 cl0 xs j
    let c0 := xs.getD (3 * j) 0
    let c2 := xs.getD (3 * j + 1) 0
    let c3 := xs.getD (3 * j + 2) 0
    let s := ((⟨r.1, []⟩ : Fs).absorbAll [c0, c2, c3] dsObserve).squeeze
    (s.2.cap, polyEval [c0, r.2 + sumE [c2, c3], c2, c3] s.1)

/-- Round `j`'s challenge. -/
def zcCh (cap0 : List E) (cl0 : E) (xs : List E) (j : ℕ) : E :=
  ((⟨(zcRec cap0 cl0 xs j).1, []⟩ : Fs).absorbAll
    [xs.getD (3 * j) 0, xs.getD (3 * j + 1) 0, xs.getD (3 * j + 2) 0] dsObserve).squeeze.1

/-- Record `j`: the capacity, the cursor, the claim. -/
def zcRecW (cap0 : List E) (cl0 cur0 : E) (xs : List E) (j : ℕ) : List E :=
  (zcRec cap0 cl0 xs j).1 ++ [cur0 * gen ^ (3 * j), (zcRec cap0 cl0 xs j).2]

/-- The records `0 ..= n` (`zc_rounds`). -/
def zcRoundsW (cap0 : List E) (cl0 cur0 : E) (xs : List E) (n : ℕ) : List E :=
  (List.range (n + 1)).flatMap (zcRecW cap0 cl0 cur0 xs)

/-- The challenges' running products (`zc_cprod`). -/
def zcCprodW (cap0 : List E) (cl0 : E) (xs : List E) (n : ℕ) : List E :=
  (List.range (n + 1)).map fun j ↦ ((List.range j).map (zcCh cap0 cl0 xs)).prod

/-- The challenges, last first (`chi`). -/
def zcChis (cap0 : List E) (cl0 : E) (xs : List E) (n : ℕ) : List E :=
  ((List.range n).map (zcCh cap0 cl0 xs)).reverse

theorem zcRec_len {cap0 : List E} {cl0 : E} {xs : List E} (h : cap0.length = 5) :
    ∀ j, (zcRec cap0 cl0 xs j).1.length = 5
  | 0 => h
  | _ + 1 => rfl

theorem zcRec_canon {cap0 : List E} {cl0 : E} {xs : List E} (h : AllCanonical cap0) :
    ∀ j, AllCanonical (zcRec cap0 cl0 xs j).1
  | 0 => h
  | _ + 1 => tb_capOf_canonical _

theorem zcRecW_len {cap0 : List E} {cl0 cur0 : E} {xs : List E} (h : cap0.length = 5) (j : ℕ) :
    (zcRecW cap0 cl0 cur0 xs j).length = 7 := by
  simp [zcRecW, zcRec_len h]

theorem zcRoundsW_len {cap0 : List E} {cl0 cur0 : E} {xs : List E} (h : cap0.length = 5) :
    ∀ n, (zcRoundsW cap0 cl0 cur0 xs n).length = 7 * (n + 1)
  | 0 => by simp [zcRoundsW, zcRecW_len h]
  | n + 1 => by
    rw [zcRoundsW, List.range_succ, List.flatMap_append, List.length_append, ← zcRoundsW,
      zcRoundsW_len h n]
    simp [zcRecW_len h]; ring

/-- **The records**, one by one. -/
theorem zcRoundsW_reads {rd : Reader} {R : E} {cap0 : List E} {cl0 cur0 : E} {xs : List E}
    (h : cap0.length = 5) {n : ℕ} (hR : TbReadsAt rd R (zcRoundsW cap0 cl0 cur0 xs n)) :
    ∀ j ≤ n, TbReadsAt rd (R * gen ^ (7 * j)) (zcRecW cap0 cl0 cur0 xs j) := by
  induction n with
  | zero =>
    intro j hj
    obtain rfl : j = 0 := by omega
    simpa [zcRoundsW] using hR
  | succ n ih =>
    rw [zcRoundsW, List.range_succ, List.flatMap_append, ← zcRoundsW, tbReadsAt_append,
      zcRoundsW_len h] at hR
    intro j hj
    rcases Nat.lt_or_ge j (n + 1) with hj' | hj'
    · exact ih hR.1 j (by omega)
    · obtain rfl : j = n + 1 := by omega
      simpa using hR.2

/-- A record's parts. -/
theorem zc_rec_parts {rd : Reader} {p : E} {cap : List E} {a b : E} (h5 : cap.length = 5)
    (h : TbReadsAt rd p (cap ++ [a, b])) :
    CapAt rd p 0 1 cap ∧ LoadHolds rd p 5 a ∧ LoadHolds rd p 6 b := by
  rw [tbReadsAt_append, h5, tbReadsAt_cons, tbReadsAt_singleton, tb_loadHolds_mul_gen_pow,
    mul_assoc, ← pow_succ, tb_loadHolds_mul_gen_pow] at h
  refine ⟨⟨h5, fun j hj => ?_⟩, h.2.1, h.2.2⟩
  simpa using h.1 j hj

/-- **Every iteration of `__loop9` has its facts** on the honest buffers and words. -/
theorem zc_l10B {rd : Reader} {R chi C : E} {cap0 : List E} {cl0 cur0 : E} {xs : List E} {n : ℕ}
    (h5 : cap0.length = 5) (hc : AllCanonical cap0)
    (hR : TbReadsAt rd R (zcRoundsW cap0 cl0 cur0 xs n))
    (hC : TbReadsAt rd C (zcCprodW cap0 cl0 xs n)) (hchi : TbReadsAt rd chi (zcChis cap0 cl0 xs n))
    (hxs : TbReadsAt rd cur0 xs) (hxl : xs.length = 3 * n) :
    ∀ j < n, L10B rd R chi (gen ^ n) C (gen ^ j) := by
  intro j hj
  have e7 : R * (gen ^ j) ^ 7 = R * gen ^ (7 * j) := by rw [← pow_mul, mul_comm j 7]
  obtain ⟨hc0, hcur, hcl⟩ := zc_rec_parts (zcRec_len h5 j) (zcRoundsW_reads h5 hR j (by omega))
  obtain ⟨hc1, hcur1, hcl1⟩ := zc_rec_parts (zcRec_len h5 (j + 1))
    (zcRoundsW_reads h5 hR (j + 1) (by omega))
  have e71 : R * gen ^ (7 * (j + 1)) = R * gen ^ (7 * j) * gen ^ 7 := by ring
  rw [e71] at hc1 hcur1 hcl1
  rw [tb_loadHolds_mul_gen_pow] at hcur1 hcl1
  have hrd : ReadsAt rd (cur0 * gen ^ (3 * j))
      [xs.getD (3 * j) 0, xs.getD (3 * j + 1) 0, xs.getD (3 * j + 2) 0] := by
    intro k hk
    simp only [List.length_cons, List.length_nil] at hk
    rw [tb_loadHolds_mul_gen_pow]
    have hk' := hxs (3 * j + k) (by omega)
    interval_cases k
    · show LoadHolds rd cur0 (3 * j + 0) (xs.getD (3 * j) 0)
      rw [List.getD_eq_getElem _ _ (by omega)]; exact hk'
    · show LoadHolds rd cur0 (3 * j + 1) (xs.getD (3 * j + 1) 0)
      rw [List.getD_eq_getElem _ _ (by omega)]; exact hk'
    · show LoadHolds rd cur0 (3 * j + 2) (xs.getD (3 * j + 2) 0)
      rw [List.getD_eq_getElem _ _ (by omega)]; exact hk'
  refine ⟨cur0 * gen ^ (3 * j), (zcRec cap0 cl0 xs j).2, cur0 * gen ^ (3 * j) * gen ^ 3,
    (zcRec cap0 cl0 xs (j + 1)).2, zcCh cap0 cl0 xs j, by rw [e7]; exact hcur, by rw [e7]; exact hcl,
    ?_, ?_, by rw [e7]; exact hcl1, ⟨gen ^ (n - 1 - j), ?_, ?_⟩, ((List.range j).map (zcCh cap0 cl0 xs)).prod, ?_, ?_⟩
  · rw [e7]
    refine (sumcheck_round4_holds rd _ _).mpr ⟨(zcRec cap0 cl0 xs j).1, _, _, _, hc0,
      zcRec_canon hc j, hrd, hc1, rfl⟩
  · rw [e7, show cur0 * gen ^ (3 * j) * gen ^ 3 = cur0 * gen ^ (3 * (j + 1)) by ring]
    exact hcur1
  · have hw := vtWInvGen_mul
    calc gen ^ n * vtWInvGen = gen ^ (n - 1 - j) * gen ^ j * (vtWInvGen * gen) := by
          rw [← pow_add, show n - 1 - j + j = n - 1 by omega, mul_comm vtWInvGen gen, ← mul_assoc,
            ← pow_succ, show n - 1 + 1 = n by omega]
      _ = gen ^ (n - 1 - j) * gen ^ j := by rw [hw, mul_one]
  · rw [tb_loadHolds_mul_gen_pow, Nat.add_zero]
    have := hchi (n - 1 - j) (by simp [zcChis]; omega)
    simp only [zcChis, List.getElem_reverse, List.getElem_map, List.getElem_range,
      List.length_map, List.length_range] at this
    rwa [show n - 1 - (n - 1 - j) = j by omega] at this
  · rw [tb_loadHolds_mul_gen_pow, Nat.add_zero]
    have := hC j (by simp [zcCprodW]; omega)
    simpa [zcCprodW] using this
  · rw [tb_loadHolds_mul_gen_pow]
    have := hC (j + 1) (by simp [zcCprodW]; omega)
    simp only [zcCprodW, List.getElem_map, List.getElem_range] at this
    rwa [List.range_succ, List.map_append, List.prod_append, List.map_singleton,
      List.prod_singleton] at this

theorem zc_slice {xs : List E} {j k : ℕ} (h : 3 * (j + k + 1) ≤ xs.length) :
    (xs.drop (3 * j)).take (3 * (k + 1)) =
      [xs.getD (3 * j) 0, xs.getD (3 * j + 1) 0, xs.getD (3 * j + 2) 0] ++
        (xs.drop (3 * (j + 1))).take (3 * k) := by
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    simp only [List.getElem_take, List.getElem_drop]
    rcases Nat.lt_or_ge i 3 with hi | hi
    · rw [List.getElem_append_left (by simpa using hi)]
      interval_cases i <;> simp <;> rw [List.getElem?_eq_getElem (by omega)] <;> rfl
    · rw [List.getElem_append_right (by simpa using hi)]
      simp only [List.length_cons, List.length_nil, List.getElem_take, List.getElem_drop]
      congr 1; omega

/-- **The honest rounds are the specification's sumcheck.** -/
theorem zc_run (cap0 : List E) (cl0 : E) {xs : List E} {n : ℕ} (hxl : xs.length = 3 * n) :
    RunsTo (sumcheck cl0 4 (List.replicate n none)) ⟨cap0, []⟩ xs
      ((List.range n).map (zcCh cap0 cl0 xs), (zcRec cap0 cl0 xs n).2)
      ⟨(zcRec cap0 cl0 xs n).1, []⟩ := by
  have key : ∀ k j, j + k = n → RunsTo (sumcheck (zcRec cap0 cl0 xs j).2 4 (List.replicate k none))
      ⟨(zcRec cap0 cl0 xs j).1, []⟩ ((xs.drop (3 * j)).take (3 * k))
      ((List.range k).map (fun i ↦ zcCh cap0 cl0 xs (j + i)), (zcRec cap0 cl0 xs n).2)
      ⟨(zcRec cap0 cl0 xs n).1, []⟩ := by
    intro k
    induction k with
    | zero =>
      intro j hj
      obtain rfl : j = n := by omega
      exact runsTo_sumcheck_nil _ _ _
    | succ k ih =>
      intro j hj
      have h1 := runsTo_roundPolyNone ⟨(zcRec cap0 cl0 xs j).1, []⟩ (zcRec cap0 cl0 xs j).2
        (xs.getD (3 * j) 0) [xs.getD (3 * j + 1) 0, xs.getD (3 * j + 2) 0] 4 rfl
      have h2 := ih (j + 1) (by omega)
      have e : ((⟨(zcRec cap0 cl0 xs j).1, []⟩ : Fs).absorb (xs.getD (3 * j) 0) dsObserve).absorbAll
          [xs.getD (3 * j + 1) 0, xs.getD (3 * j + 2) 0] dsObserve =
          (⟨(zcRec cap0 cl0 xs j).1, []⟩ : Fs).absorbAll
            [xs.getD (3 * j) 0, xs.getD (3 * j + 1) 0, xs.getD (3 * j + 2) 0] dsObserve := rfl
      rw [e] at h1
      have h := runsTo_sumcheck_cons h1 h2
      rw [List.replicate_succ, zc_slice (by omega), List.range_succ_eq_map, List.map_cons,
        List.map_map]
      refine h.of_eq rfl rfl ?_ rfl
      rw [Nat.add_zero]
      refine Prod.ext (congrArg₂ List.cons rfl (List.map_congr_left fun i _ => ?_)) rfl
      simp only [Function.comp_apply]
      rw [show j + 1 + i = j + (i + 1) by omega]
  have := key n 0 (by omega)
  simp only [Nat.mul_zero, List.drop_zero, Nat.zero_add] at this
  rw [← hxl, List.take_length] at this
  exact this

end
end LeanVM.Guest.B1.Tables
