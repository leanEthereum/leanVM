/-
  LeanVM.Guest.B1.Tables.VtC.ZBase

  The table sumcheck's honest rounds (from the transcript words, the capacity and the target), the
  buffers they fill, and `verify_tables`' statements `2591 ..< 2685` and `5525 ..< 5559`.
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

/-- `verify_tables`' statements `2591 ..< 2685` (G:2587-2628). -/
noncomputable def zBlk : List Stmt := [
    .atom (.hint (.witness "zc_tau_max" (.stack [.n 2544]))),
    .atom (.const (.n 2545) (word 4294967296 0)),
    .atom (.mul (.n 2544) (.n 2546) (.n 27)),
    .atom (.rangeCheck (.n 2546) (.n 2547) (.n 2548) (.n 2549) (.n 2545)),
    .atom (.add (.n 2550) (.n 2544) (.n 27)),
    .atom (.const (.n 2551) (word 4294967296 0)),
    .atom (.mul (.n 2544) (.n 2552) (.n 28)),
    .atom (.rangeCheck (.n 2552) (.n 2553) (.n 2554) (.n 2555) (.n 2551)),
    .atom (.add (.n 2556) (.n 2544) (.n 28)),
    .atom (.mul (.n 2557) (.n 2550) (.n 2556)),
    .atom (.const (.n 2558) (word 4294967296 0)),
    .atom (.mul (.n 2544) (.n 2559) (.n 29)),
    .atom (.rangeCheck (.n 2559) (.n 2560) (.n 2561) (.n 2562) (.n 2558)),
    .atom (.add (.n 2563) (.n 2544) (.n 29)),
    .atom (.mul (.n 2564) (.n 2557) (.n 2563)),
    .atom (.const (.n 2565) (word 4294967296 0)),
    .atom (.mul (.n 2544) (.n 2566) (.n 30)),
    .atom (.rangeCheck (.n 2566) (.n 2567) (.n 2568) (.n 2569) (.n 2565)),
    .atom (.add (.n 2570) (.n 2544) (.n 30)),
    .atom (.mul (.n 2571) (.n 2564) (.n 2570)),
    .atom (.const (.n 2572) (word 4294967296 0)),
    .atom (.mul (.n 2544) (.n 2573) (.n 31)),
    .atom (.rangeCheck (.n 2573) (.n 2574) (.n 2575) (.n 2576) (.n 2572)),
    .atom (.add (.n 2577) (.n 2544) (.n 31)),
    .atom (.mul (.n 2578) (.n 2571) (.n 2577)),
    .atom (.const (.n 2579) (word 4294967296 0)),
    .atom (.mul (.n 2544) (.n 2580) (.n 32)),
    .atom (.rangeCheck (.n 2580) (.n 2581) (.n 2582) (.n 2583) (.n 2579)),
    .atom (.add (.n 2584) (.n 2544) (.n 32)),
    .atom (.mul (.n 2585) (.n 2578) (.n 2584)),
    .atom (.const (.n 2586) (word 0 0)),
    .atom (.assertEq (.n 2585) (.n 2586)),
    .atom (.const (.n 2587) (word 4294967296 0)),
    .atom (.mul (.n 9) (.n 2588) (.n 2544)),
    .atom (.rangeCheck (.n 2588) (.n 2589) (.n 2590) (.n 2591) (.n 2587)),
    .atom (.const (.n 2592) (word 1 0)),
    .atom (.const (.n 2593) (word 0 0)),
    .atom (.const (.n 2594) (word 0 0)),
    .atom (.const (.n 2595) (word 0 0)),
    .atom (.const (.n 2596) (word 0 0)),
    .atom (.keccak [.n 1906, .n 1907, .n 2593, .n 2593, .n 2593, .n 2594, .n 2595, .n 2596, .n 1900, .n 1901, .n 1902, .n 1903, .n 1904] [.n 2597, .n 2598, .n 2599, .n 2600, .n 2601, .n 2602, .n 2603, .n 2604, .n 2605, .n 2606, .n 2607, .n 2608, .n 2609] false false),
    .atom (.copy (.n 2610) (.n 2597)),
    .atom (.const (.n 2611) (word 1 0)),
    .atom (.mul (.n 2612) (.n 2611) (.n 2610)),
    .atom (.mul (.n 2613) (.n 2612) (.n 2610)),
    .atom (.mul (.n 2614) (.n 2613) (.n 2610)),
    .atom (.mul (.n 2615) (.n 2614) (.n 2610)),
    .atom (.mul (.n 2616) (.n 2613) (.n 2442)),
    .atom (.mul (.n 2617) (.n 2614) (.n 2488)),
    .atom (.add (.n 2618) (.n 2616) (.n 2617)),
    .atom (.mul (.n 2619) (.n 2615) (.n 2543)),
    .atom (.add (.n 2620) (.n 2618) (.n 2619)),
    .atom (.const (.n 2621) (word 2 0)),
    .atom (.mul (.n 2622) (.n 2544) (.n 2621)),
    .atom (.mul (.n 2623) (.n 2622) (.n 2622)),
    .atom (.mul (.n 2624) (.n 2623) (.n 2622)),
    .atom (.mul (.n 2625) (.n 2624) (.n 2624)),
    .atom (.mul (.n 2626) (.n 2625) (.n 2622)),
    .atom (.hint (.allocDyn (.n 2627) (.n 2626))),
    .atom (.const (.n 2628) (word 2 0)),
    .atom (.mul (.n 2629) (.n 2544) (.n 2628)),
    .atom (.hint (.allocDyn (.n 2630) (.n 2629))),
    .atom (.load (.n 2605) (.n 2627) 0),
    .atom (.load (.n 2606) (.n 2627) 1),
    .atom (.load (.n 2607) (.n 2627) 2),
    .atom (.load (.n 2608) (.n 2627) 3),
    .atom (.load (.n 2609) (.n 2627) 4),
    .atom (.const (.n 2631) (word 2 0)),
    .atom (.mul (.n 2632) (.n 1897) (.n 2631)),
    .atom (.load (.n 2632) (.n 2627) 5),
    .atom (.load (.n 2620) (.n 2627) 6),
    .atom (.const (.n 2633) (word 1 0)),
    .atom (.load (.n 2633) (.n 2630) 0),
    .atom (.const (.n 2634) (word 1 0)),
    .atom (.add (.n 2635) (.n 2634) (.n 2544)),
    .atom (.const (.n 2636) (word 1 0)),
    .callIf (.n 2635) "__loop9" [.n 2636, .n 2544, .n 2627, .n 18, .n 16, .n 2544, .n 2630],
    .atom (.mul (.n 2637) (.n 2544) (.n 2544)),
    .atom (.mul (.n 2638) (.n 2637) (.n 2544)),
    .atom (.mul (.n 2639) (.n 2638) (.n 2638)),
    .atom (.mul (.n 2640) (.n 2639) (.n 2544)),
    .atom (.mul (.n 2641) (.n 2627) (.n 2640)),
    .atom (.load (.n 2642) (.n 2641) 0),
    .atom (.load (.n 2643) (.n 2641) 1),
    .atom (.load (.n 2644) (.n 2641) 2),
    .atom (.load (.n 2645) (.n 2641) 3),
    .atom (.load (.n 2646) (.n 2641) 4),
    .atom (.load (.n 2647) (.n 2641) 5),
    .atom (.load (.n 2648) (.n 2641) 6),
    .atom (.const (.n 2649) (word 2 0)),
    .atom (.mul (.n 2650) (.n 2544) (.n 2649)),
    .atom (.hint (.allocDyn (.n 2651) (.n 2650))),
    .atom (.const (.n 2652) (word 1 0)),
    .call "eq_prefix_chain" [.n 2651, .n 2652, .n 16, .n 699, .n 2544] []]

/-- `verify_tables`' statements `5525 ..< 5559` (G:2719-2735). -/
noncomputable def zTail : List Stmt := [
    .atom (.keccak [.n 4688, .n 4689, .n 2593, .n 2593, .n 2593, .n 2594, .n 2595, .n 2596, .n 4682, .n 4683, .n 4684, .n 4685, .n 4686] [.n 5948, .n 5949, .n 5950, .n 5951, .n 5952, .n 5953, .n 5954, .n 5955, .n 5956, .n 5957, .n 5958, .n 5959, .n 5960] false false),
    .atom (.copy (.n 5961) (.n 5948)),
    .atom (.hint (.limbs (.n 6) [.n 5962])),
    .atom (.add (.n 5963) (.n 6) (.n 5962)),
    .atom (.const (.n 5964) (word 2 1)),
    .atom (.mul (.n 5965) (.n 5963) (.n 5964)),
    .atom (.assertInK (.n 5962) (.n 5965)),
    .atom (.copy (.n 5966) (.n 5962)),
    .atom (.hint (.limbs (.n 7) [.n 5967])),
    .atom (.add (.n 5968) (.n 7) (.n 5967)),
    .atom (.const (.n 5969) (word 2 1)),
    .atom (.mul (.n 5970) (.n 5968) (.n 5969)),
    .atom (.assertInK (.n 5967) (.n 5970)),
    .atom (.copy (.n 5971) (.n 5967)),
    .atom (.add (.n 5972) (.n 5966) (.n 5971)),
    .atom (.mul (.n 5973) (.n 5961) (.n 5972)),
    .atom (.add (.n 5974) (.n 5966) (.n 5973)),
    .atom (.load (.n 5974) (.n 15) 157),
    .atom (.add (.n 5975) (.n 5965) (.n 5970)),
    .atom (.mul (.n 5976) (.n 5961) (.n 5975)),
    .atom (.add (.n 5977) (.n 5965) (.n 5976)),
    .atom (.load (.n 5977) (.n 15) 158),
    .atom (.copy (.n 5978) (.n 5956)),
    .atom (.copy (.n 5979) (.n 5957)),
    .atom (.copy (.n 5980) (.n 5958)),
    .atom (.copy (.n 5981) (.n 5959)),
    .atom (.copy (.n 5982) (.n 5960)),
    .atom (.const (.n 5983) (word 10905190400 0)),
    .atom (.mul (.n 5984) (.n 2647) (.n 5983)),
    .atom (.copy (.n 5985) (.n 5984)),
    .atom (.copy (.n 5986) (.n 2544)),
    .atom (.copy (.n 5987) (.n 1905)),
    .atom (.copy (.n 5988) (.n 5961)),
    .atom (.copy (.n 5989) (.n 2647))]

theorem zBlk_at : tbStmtsEqb zBlk ((vtPre.drop 2591).take zBlk.length) = true := by
  simp only [vtPre_drop]; decide +kernel

theorem zTail_at : tbStmtsEqb zTail ((vtPre.drop 5525).take zTail.length) = true := by
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
theorem zc_l10B {rd : Reader} {R tabs chi C : E} {cap0 : List E} {cl0 cur0 : E} {xs : List E} {n : ℕ}
    (h5 : cap0.length = 5)
    (hR : TbReadsAt rd R (zcRoundsW cap0 cl0 cur0 xs n))
    (hC : TbReadsAt rd C (zcCprodW cap0 cl0 xs n)) (hchi : TbReadsAt rd chi (zcChis cap0 cl0 xs n))
    (hxs : TbReadsAt rd cur0 xs) (hxl : xs.length = 3 * n) :
    ∀ j < n, L10B rd R tabs chi (gen ^ n) C (gen ^ j) := by
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
      hrd, hc1, rfl⟩
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
        (xs.getD (3 * j) 0) [xs.getD (3 * j + 1) 0, xs.getD (3 * j + 2) 0] 4 rfl (by decide)
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
