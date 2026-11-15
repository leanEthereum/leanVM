/-
  LeanVM.Guest.B1.Tables.VtC.ZBase

  The table sumcheck's honest rounds (from the transcript words, the capacity and the target), the
  buffers they fill, and `verify_tables`' statements `2591 ..< 2690` and `5530 ..< 5564`.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.Hon
public import LeanVM.Guest.B1.Tables.VtC.ZLoop10
public import LeanVM.Guest.B1.Tables.Vt.ZcRun
public import LeanVM.Guest.B1.Tables.Vt.Pi
public import LeanVM.Guest.Data.NameStrings

/-!
# The table sumcheck, honestly

`zcRec cap0 cl0 xs j`: the capacity and the claim before round `j` of the plain degree-4
sumcheck from the capacity `cap0` and the claim `cl0`, round `j` reading the words
`xs[3j], xs[3j+1], xs[3j+2]` (`c0, c2, c3`); `zcCh`: round `j`'s challenge. The buffers:
`zcRoundsW` (record `j ≤ n`: the capacity, the cursor `cur0·g^(3j)`, the claim), `zcCprodW`
(the challenges' running products), `zcRkW` (the challenges, as `zc_rk` holds them), `zcChis` (the
challenges, last first, as `chi` holds them).

`zc_run`: the rounds are the specification's `sumcheck cl0 4 (replicate n none)`.
`zc_l10B`: on a memory holding the buffers and the words, every iteration of `verify_tables_loop0`
has its facts; `zc_l11C`: `verify_tables_loop1`'s, `chi` being `zc_rk` reversed.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

/-! ## The statements -/

/-- `verify_tables`' statements `2591 ..< 2690` (G:2546-2591). -/
noncomputable def zBlk : List Stmt := [
    .atom (.hint (.witness "zc_tau_max" (.stack [.n 2545]))),
    .atom (.const (.n 2546) (word 4294967296 0)),
    .atom (.mul (.n 2545) (.n 2547) (.n 28)),
    .atom (.rangeCheck (.n 2547) (.n 2548) (.n 2549) (.n 2550) (.n 2546)),
    .atom (.add (.n 2551) (.n 2545) (.n 28)),
    .atom (.const (.n 2552) (word 4294967296 0)),
    .atom (.mul (.n 2545) (.n 2553) (.n 29)),
    .atom (.rangeCheck (.n 2553) (.n 2554) (.n 2555) (.n 2556) (.n 2552)),
    .atom (.add (.n 2557) (.n 2545) (.n 29)),
    .atom (.mul (.n 2558) (.n 2551) (.n 2557)),
    .atom (.const (.n 2559) (word 4294967296 0)),
    .atom (.mul (.n 2545) (.n 2560) (.n 30)),
    .atom (.rangeCheck (.n 2560) (.n 2561) (.n 2562) (.n 2563) (.n 2559)),
    .atom (.add (.n 2564) (.n 2545) (.n 30)),
    .atom (.mul (.n 2565) (.n 2558) (.n 2564)),
    .atom (.const (.n 2566) (word 4294967296 0)),
    .atom (.mul (.n 2545) (.n 2567) (.n 31)),
    .atom (.rangeCheck (.n 2567) (.n 2568) (.n 2569) (.n 2570) (.n 2566)),
    .atom (.add (.n 2571) (.n 2545) (.n 31)),
    .atom (.mul (.n 2572) (.n 2565) (.n 2571)),
    .atom (.const (.n 2573) (word 4294967296 0)),
    .atom (.mul (.n 2545) (.n 2574) (.n 32)),
    .atom (.rangeCheck (.n 2574) (.n 2575) (.n 2576) (.n 2577) (.n 2573)),
    .atom (.add (.n 2578) (.n 2545) (.n 32)),
    .atom (.mul (.n 2579) (.n 2572) (.n 2578)),
    .atom (.const (.n 2580) (word 4294967296 0)),
    .atom (.mul (.n 2545) (.n 2581) (.n 33)),
    .atom (.rangeCheck (.n 2581) (.n 2582) (.n 2583) (.n 2584) (.n 2580)),
    .atom (.add (.n 2585) (.n 2545) (.n 33)),
    .atom (.mul (.n 2586) (.n 2579) (.n 2585)),
    .atom (.const (.n 2587) (word 0 0)),
    .atom (.assertEq (.n 2586) (.n 2587)),
    .atom (.const (.n 2588) (word 4294967296 0)),
    .atom (.mul (.n 9) (.n 2589) (.n 2545)),
    .atom (.rangeCheck (.n 2589) (.n 2590) (.n 2591) (.n 2592) (.n 2588)),
    .atom (.const (.n 2593) (word 1 0)),
    .atom (.const (.n 2594) (word 0 0)),
    .atom (.const (.n 2595) (word 0 0)),
    .atom (.const (.n 2596) (word 0 0)),
    .atom (.const (.n 2597) (word 0 0)),
    .atom (.keccak [.n 1907, .n 1908, .n 2594, .n 2594, .n 2594, .n 2595, .n 2596, .n 2597, .n 1901, .n 1902, .n 1903, .n 1904, .n 1905] [.n 2598, .n 2599, .n 2600, .n 2601, .n 2602, .n 2603, .n 2604, .n 2605, .n 2606, .n 2607, .n 2608, .n 2609, .n 2610] false false),
    .atom (.copy (.n 2611) (.n 2598)),
    .atom (.const (.n 2612) (word 1 0)),
    .atom (.mul (.n 2613) (.n 2612) (.n 2611)),
    .atom (.mul (.n 2614) (.n 2613) (.n 2611)),
    .atom (.mul (.n 2615) (.n 2614) (.n 2611)),
    .atom (.mul (.n 2616) (.n 2615) (.n 2611)),
    .atom (.mul (.n 2617) (.n 2614) (.n 2443)),
    .atom (.mul (.n 2618) (.n 2615) (.n 2489)),
    .atom (.add (.n 2619) (.n 2617) (.n 2618)),
    .atom (.mul (.n 2620) (.n 2616) (.n 2544)),
    .atom (.add (.n 2621) (.n 2619) (.n 2620)),
    .atom (.const (.n 2622) (word 2 0)),
    .atom (.mul (.n 2623) (.n 2545) (.n 2622)),
    .atom (.mul (.n 2624) (.n 2623) (.n 2623)),
    .atom (.mul (.n 2625) (.n 2624) (.n 2623)),
    .atom (.mul (.n 2626) (.n 2625) (.n 2625)),
    .atom (.mul (.n 2627) (.n 2626) (.n 2623)),
    .atom (.hint (.allocDyn (.n 2628) (.n 2627))),
    .atom (.const (.n 2629) (word 2 0)),
    .atom (.mul (.n 2630) (.n 2545) (.n 2629)),
    .atom (.hint (.allocDyn (.n 2631) (.n 2630))),
    .atom (.load (.n 2606) (.n 2628) 0),
    .atom (.load (.n 2607) (.n 2628) 1),
    .atom (.load (.n 2608) (.n 2628) 2),
    .atom (.load (.n 2609) (.n 2628) 3),
    .atom (.load (.n 2610) (.n 2628) 4),
    .atom (.const (.n 2632) (word 2 0)),
    .atom (.mul (.n 2633) (.n 1898) (.n 2632)),
    .atom (.load (.n 2633) (.n 2628) 5),
    .atom (.load (.n 2621) (.n 2628) 6),
    .atom (.const (.n 2634) (word 1 0)),
    .atom (.load (.n 2634) (.n 2631) 0),
    .atom (.hint (.alloc (.n 2635) 34)),
    .atom (.const (.n 2636) (word 1 0)),
    .atom (.add (.n 2637) (.n 2636) (.n 2545)),
    .atom (.const (.n 2638) (word 1 0)),
    .callIf (.n 2637) name% «verify_tables_loop0» [.n 2638, .n 2545, .n 2628, .n 18, .n 2635,
        .n 2631],
    .atom (.const (.n 2639) (word 1 0)),
    .atom (.add (.n 2640) (.n 2639) (.n 2545)),
    .atom (.const (.n 2641) (word 1 0)),
    .callIf (.n 2640) name% «verify_tables_loop1» [.n 2641, .n 2545, .n 16, .n 2635, .n 2545],
    .atom (.mul (.n 2642) (.n 2545) (.n 2545)),
    .atom (.mul (.n 2643) (.n 2642) (.n 2545)),
    .atom (.mul (.n 2644) (.n 2643) (.n 2643)),
    .atom (.mul (.n 2645) (.n 2644) (.n 2545)),
    .atom (.mul (.n 2646) (.n 2628) (.n 2645)),
    .atom (.load (.n 2647) (.n 2646) 0),
    .atom (.load (.n 2648) (.n 2646) 1),
    .atom (.load (.n 2649) (.n 2646) 2),
    .atom (.load (.n 2650) (.n 2646) 3),
    .atom (.load (.n 2651) (.n 2646) 4),
    .atom (.load (.n 2652) (.n 2646) 5),
    .atom (.load (.n 2653) (.n 2646) 6),
    .atom (.const (.n 2654) (word 2 0)),
    .atom (.mul (.n 2655) (.n 2545) (.n 2654)),
    .atom (.hint (.allocDyn (.n 2656) (.n 2655))),
    .atom (.const (.n 2657) (word 1 0)),
    .call "eq_prefix_chain" [.n 2656, .n 2657, .n 16, .n 700, .n 2545] []]

/-- `verify_tables`' statements `5530 ..< 5564` (G:2682-2698). -/
noncomputable def zTail : List Stmt := [
    .atom (.keccak [.n 4693, .n 4694, .n 2594, .n 2594, .n 2594, .n 2595, .n 2596, .n 2597, .n 4687, .n 4688, .n 4689, .n 4690, .n 4691] [.n 5953, .n 5954, .n 5955, .n 5956, .n 5957, .n 5958, .n 5959, .n 5960, .n 5961, .n 5962, .n 5963, .n 5964, .n 5965] false false),
    .atom (.copy (.n 5966) (.n 5953)),
    .atom (.hint (.limbs (.n 6) [.n 5967])),
    .atom (.add (.n 5968) (.n 6) (.n 5967)),
    .atom (.const (.n 5969) (word 2 1)),
    .atom (.mul (.n 5970) (.n 5968) (.n 5969)),
    .atom (.assertInK (.n 5967) (.n 5970)),
    .atom (.copy (.n 5971) (.n 5967)),
    .atom (.hint (.limbs (.n 7) [.n 5972])),
    .atom (.add (.n 5973) (.n 7) (.n 5972)),
    .atom (.const (.n 5974) (word 2 1)),
    .atom (.mul (.n 5975) (.n 5973) (.n 5974)),
    .atom (.assertInK (.n 5972) (.n 5975)),
    .atom (.copy (.n 5976) (.n 5972)),
    .atom (.add (.n 5977) (.n 5971) (.n 5976)),
    .atom (.mul (.n 5978) (.n 5966) (.n 5977)),
    .atom (.add (.n 5979) (.n 5971) (.n 5978)),
    .atom (.load (.n 5979) (.n 15) 157),
    .atom (.add (.n 5980) (.n 5970) (.n 5975)),
    .atom (.mul (.n 5981) (.n 5966) (.n 5980)),
    .atom (.add (.n 5982) (.n 5970) (.n 5981)),
    .atom (.load (.n 5982) (.n 15) 158),
    .atom (.copy (.n 5983) (.n 5961)),
    .atom (.copy (.n 5984) (.n 5962)),
    .atom (.copy (.n 5985) (.n 5963)),
    .atom (.copy (.n 5986) (.n 5964)),
    .atom (.copy (.n 5987) (.n 5965)),
    .atom (.const (.n 5988) (word 10905190400 0)),
    .atom (.mul (.n 5989) (.n 2652) (.n 5988)),
    .atom (.copy (.n 5990) (.n 5989)),
    .atom (.copy (.n 5991) (.n 2545)),
    .atom (.copy (.n 5992) (.n 1906)),
    .atom (.copy (.n 5993) (.n 5966)),
    .atom (.copy (.n 5994) (.n 2652))]

theorem zBlk_at : tbStmtsEqb zBlk ((vtPre.drop 2591).take zBlk.length) = true := by
  simp only [vtPre_drop]; decide +kernel

theorem zTail_at : tbStmtsEqb zTail ((vtPre.drop 5530).take zTail.length) = true := by
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

/-- The challenges, in round order (`zc_rk`). -/
def zcRkW (cap0 : List E) (cl0 : E) (xs : List E) (n : ℕ) : List E :=
  (List.range n).map (zcCh cap0 cl0 xs)

/-- The challenges, last first (`chi`). -/
def zcChis (cap0 : List E) (cl0 : E) (xs : List E) (n : ℕ) : List E :=
  (zcRkW cap0 cl0 xs n).reverse

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

/-- **Every iteration of `verify_tables_loop0` has its facts** on the honest buffers and words. -/
theorem zc_l10B {rd : Reader} {R tabs rkb C : E} {cap0 : List E} {cl0 cur0 : E} {xs : List E} {n : ℕ}
    (h5 : cap0.length = 5)
    (hR : TbReadsAt rd R (zcRoundsW cap0 cl0 cur0 xs n))
    (hC : TbReadsAt rd C (zcCprodW cap0 cl0 xs n)) (hrk : TbReadsAt rd rkb (zcRkW cap0 cl0 xs n))
    (hxs : TbReadsAt rd cur0 xs) (hxl : xs.length = 3 * n) :
    ∀ j < n, L10B rd R tabs rkb C (gen ^ j) := by
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
    ?_, ?_, by rw [e7]; exact hcl1, ?_, ((List.range j).map (zcCh cap0 cl0 xs)).prod, ?_, ?_⟩
  · rw [e7]
    refine (sumcheck_round4_holds rd _ _).mpr ⟨(zcRec cap0 cl0 xs j).1, _, _, _, hc0,
      hrd, hc1, rfl⟩
  · rw [e7, show cur0 * gen ^ (3 * j) * gen ^ 3 = cur0 * gen ^ (3 * (j + 1)) by ring]
    exact hcur1
  · rw [tb_loadHolds_mul_gen_pow, Nat.add_zero]
    simpa [zcRkW] using hrk j (by simp [zcRkW]; omega)
  · rw [tb_loadHolds_mul_gen_pow, Nat.add_zero]
    have := hC j (by simp [zcCprodW]; omega)
    simpa [zcCprodW] using this
  · rw [tb_loadHolds_mul_gen_pow]
    have := hC (j + 1) (by simp [zcCprodW]; omega)
    simp only [zcCprodW, List.getElem_map, List.getElem_range] at this
    rwa [List.range_succ, List.map_append, List.prod_append, List.map_singleton,
      List.prod_singleton] at this

/-- **`chi` is `zc_rk` reversed** on the honest buffers. -/
theorem zc_l11C {rd : Reader} {rkb chi : E} {cap0 : List E} {cl0 : E} {xs : List E} {n : ℕ}
    (hrk : TbReadsAt rd rkb (zcRkW cap0 cl0 xs n)) (hchi : TbReadsAt rd chi (zcChis cap0 cl0 xs n)) :
    ∀ x < n, ∃ v, LoadHolds rd rkb (n - 1 - x) v ∧ LoadHolds rd chi x v := by
  intro x hx
  refine ⟨zcCh cap0 cl0 xs (n - 1 - x), ?_, ?_⟩
  · simpa [zcRkW] using hrk (n - 1 - x) (by simp [zcRkW]; omega)
  · have := hchi x (by simp [zcChis, zcRkW]; omega)
    simpa [zcChis, zcRkW, List.getElem_reverse] using this

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
