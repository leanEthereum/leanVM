/-
  LeanVM.Guest.B1.Tables.VtC.ZBase

  The table sumcheck's honest rounds (from the transcript words, the capacity and the target), the
  buffers they fill, and `verify_tables`' statements `2292 ..< 2385` and `5225 ..< 5256`.
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
(the challenges' running products), `zcChis` (the challenges, last first, as `chi` holds them).

`zc_run`: the rounds are the specification's `sumcheck cl0 4 (replicate n none)`.
`zc_l10B`: on a memory holding the buffers and the words, every iteration of `verify_tables_loop0`
has its facts.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

/-! ## The statements -/

/-- `verify_tables`' statements `2292 ..< 2385`. -/
noncomputable def zBlk : List Stmt := [
    .atom (.hint (.witness "zc_tau_max" (.stack [.n 2245]))),
    .atom (.const (.n 2246) (word 4294967296 0)),
    .atom (.mul (.n 2245) (.n 2247) (.n 27)),
    .atom (.rangeCheck (.n 2247) (.n 2248) (.n 2249) (.n 2250) (.n 2246)),
    .atom (.add (.n 2251) (.n 2245) (.n 27)),
    .atom (.const (.n 2252) (word 4294967296 0)),
    .atom (.mul (.n 2245) (.n 2253) (.n 28)),
    .atom (.rangeCheck (.n 2253) (.n 2254) (.n 2255) (.n 2256) (.n 2252)),
    .atom (.add (.n 2257) (.n 2245) (.n 28)),
    .atom (.mul (.n 2258) (.n 2251) (.n 2257)),
    .atom (.const (.n 2259) (word 4294967296 0)),
    .atom (.mul (.n 2245) (.n 2260) (.n 29)),
    .atom (.rangeCheck (.n 2260) (.n 2261) (.n 2262) (.n 2263) (.n 2259)),
    .atom (.add (.n 2264) (.n 2245) (.n 29)),
    .atom (.mul (.n 2265) (.n 2258) (.n 2264)),
    .atom (.const (.n 2266) (word 4294967296 0)),
    .atom (.mul (.n 2245) (.n 2267) (.n 30)),
    .atom (.rangeCheck (.n 2267) (.n 2268) (.n 2269) (.n 2270) (.n 2266)),
    .atom (.add (.n 2271) (.n 2245) (.n 30)),
    .atom (.mul (.n 2272) (.n 2265) (.n 2271)),
    .atom (.const (.n 2273) (word 4294967296 0)),
    .atom (.mul (.n 2245) (.n 2274) (.n 31)),
    .atom (.rangeCheck (.n 2274) (.n 2275) (.n 2276) (.n 2277) (.n 2273)),
    .atom (.add (.n 2278) (.n 2245) (.n 31)),
    .atom (.mul (.n 2279) (.n 2272) (.n 2278)),
    .atom (.const (.n 2280) (word 4294967296 0)),
    .atom (.mul (.n 2245) (.n 2281) (.n 32)),
    .atom (.rangeCheck (.n 2281) (.n 2282) (.n 2283) (.n 2284) (.n 2280)),
    .atom (.add (.n 2285) (.n 2245) (.n 32)),
    .atom (.mul (.n 2286) (.n 2279) (.n 2285)),
    .atom (.const (.n 2287) (word 0 0)),
    .atom (.assertEq (.n 2286) (.n 2287)),
    .atom (.const (.n 2288) (word 4294967296 0)),
    .atom (.mul (.n 9) (.n 2289) (.n 2245)),
    .atom (.rangeCheck (.n 2289) (.n 2290) (.n 2291) (.n 2292) (.n 2288)),
    .atom (.const (.n 2293) (word 1 0)),
    .atom (.const (.n 2294) (word 0 0)),
    .atom (.const (.n 2295) (word 0 0)),
    .atom (.const (.n 2296) (word 0 0)),
    .atom (.const (.n 2297) (word 0 0)),
    .atom (.keccak [.n 1607, .n 1608, .n 2294, .n 2294, .n 2294, .n 2295, .n 2296, .n 2297, .n 1601, .n 1602, .n 1603, .n 1604, .n 1605] [.n 2298, .n 2299, .n 2300, .n 2301, .n 2302, .n 2303, .n 2304, .n 2305, .n 2306, .n 2307, .n 2308, .n 2309, .n 2310] false false),
    .atom (.const (.n 2311) (word 1 0)),
    .atom (.mul (.n 2312) (.n 2311) (.n 2298)),
    .atom (.mul (.n 2313) (.n 2312) (.n 2298)),
    .atom (.mul (.n 2314) (.n 2313) (.n 2298)),
    .atom (.mul (.n 2315) (.n 2314) (.n 2298)),
    .atom (.mul (.n 2316) (.n 2313) (.n 2143)),
    .atom (.mul (.n 2317) (.n 2314) (.n 2189)),
    .atom (.add (.n 2318) (.n 2316) (.n 2317)),
    .atom (.mul (.n 2319) (.n 2315) (.n 2244)),
    .atom (.add (.n 2320) (.n 2318) (.n 2319)),
    .atom (.const (.n 2321) (word 2 0)),
    .atom (.mul (.n 2322) (.n 2245) (.n 2321)),
    .atom (.mul (.n 2323) (.n 2322) (.n 2322)),
    .atom (.mul (.n 2324) (.n 2323) (.n 2322)),
    .atom (.mul (.n 2325) (.n 2324) (.n 2324)),
    .atom (.mul (.n 2326) (.n 2325) (.n 2322)),
    .atom (.hint (.allocDyn (.n 2327) (.n 2326))),
    .atom (.const (.n 2328) (word 2 0)),
    .atom (.mul (.n 2329) (.n 2245) (.n 2328)),
    .atom (.hint (.allocDyn (.n 2330) (.n 2329))),
    .atom (.load (.n 2306) (.n 2327) 0),
    .atom (.load (.n 2307) (.n 2327) 1),
    .atom (.load (.n 2308) (.n 2327) 2),
    .atom (.load (.n 2309) (.n 2327) 3),
    .atom (.load (.n 2310) (.n 2327) 4),
    .atom (.const (.n 2331) (word 2 0)),
    .atom (.mul (.n 2332) (.n 1598) (.n 2331)),
    .atom (.load (.n 2332) (.n 2327) 5),
    .atom (.load (.n 2320) (.n 2327) 6),
    .atom (.const (.n 2333) (word 1 0)),
    .atom (.load (.n 2333) (.n 2330) 0),
    .atom (.const (.n 2334) (word 1 0)),
    .atom (.add (.n 2335) (.n 2334) (.n 2245)),
    .atom (.const (.n 2336) (word 1 0)),
    .callIf (.n 2335) name% «verify_tables_loop0» [.n 2336, .n 2245, .n 2327, .n 18, .n 16,
        .n 2245, .n 2330],
    .atom (.mul (.n 2337) (.n 2245) (.n 2245)),
    .atom (.mul (.n 2338) (.n 2337) (.n 2245)),
    .atom (.mul (.n 2339) (.n 2338) (.n 2338)),
    .atom (.mul (.n 2340) (.n 2339) (.n 2245)),
    .atom (.mul (.n 2341) (.n 2327) (.n 2340)),
    .atom (.load (.n 2342) (.n 2341) 0),
    .atom (.load (.n 2343) (.n 2341) 1),
    .atom (.load (.n 2344) (.n 2341) 2),
    .atom (.load (.n 2345) (.n 2341) 3),
    .atom (.load (.n 2346) (.n 2341) 4),
    .atom (.load (.n 2347) (.n 2341) 5),
    .atom (.load (.n 2348) (.n 2341) 6),
    .atom (.const (.n 2349) (word 2 0)),
    .atom (.mul (.n 2350) (.n 2245) (.n 2349)),
    .atom (.hint (.allocDyn (.n 2351) (.n 2350))),
    .atom (.const (.n 2352) (word 1 0)),
    .call "eq_prefix_chain" [.n 2351, .n 2352, .n 16, .n 699, .n 2245] []]

/-- `verify_tables`' statements `5225 ..< 5256`. -/
noncomputable def zTail : List Stmt := [
    .atom (.keccak [.n 4388, .n 4389, .n 2294, .n 2294, .n 2294, .n 2295, .n 2296, .n 2297, .n 4382, .n 4383, .n 4384, .n 4385, .n 4386] [.n 5648, .n 5649, .n 5650, .n 5651, .n 5652, .n 5653, .n 5654, .n 5655, .n 5656, .n 5657, .n 5658, .n 5659, .n 5660] false false),
    .atom (.hint (.limbs (.n 6) [.n 5661])),
    .atom (.add (.n 5662) (.n 6) (.n 5661)),
    .atom (.const (.n 5663) (word 2 1)),
    .atom (.mul (.n 5664) (.n 5662) (.n 5663)),
    .atom (.assertInK (.n 5661) (.n 5664)),
    .atom (.hint (.limbs (.n 7) [.n 5665])),
    .atom (.add (.n 5666) (.n 7) (.n 5665)),
    .atom (.const (.n 5667) (word 2 1)),
    .atom (.mul (.n 5668) (.n 5666) (.n 5667)),
    .atom (.assertInK (.n 5665) (.n 5668)),
    .atom (.add (.n 5669) (.n 5661) (.n 5665)),
    .atom (.mul (.n 5670) (.n 5648) (.n 5669)),
    .atom (.add (.n 5671) (.n 5661) (.n 5670)),
    .atom (.load (.n 5671) (.n 15) 157),
    .atom (.add (.n 5672) (.n 5664) (.n 5668)),
    .atom (.mul (.n 5673) (.n 5648) (.n 5672)),
    .atom (.add (.n 5674) (.n 5664) (.n 5673)),
    .atom (.load (.n 5674) (.n 15) 158),
    .atom (.copy (.n 5675) (.n 5656)),
    .atom (.copy (.n 5676) (.n 5657)),
    .atom (.copy (.n 5677) (.n 5658)),
    .atom (.copy (.n 5678) (.n 5659)),
    .atom (.copy (.n 5679) (.n 5660)),
    .atom (.const (.n 5680) (word 10905190400 0)),
    .atom (.mul (.n 5681) (.n 2347) (.n 5680)),
    .atom (.copy (.n 5682) (.n 5681)),
    .atom (.copy (.n 5683) (.n 2245)),
    .atom (.copy (.n 5684) (.n 1606)),
    .atom (.copy (.n 5685) (.n 5648)),
    .atom (.copy (.n 5686) (.n 2347))]

theorem zBlk_at : tbStmtsEqb zBlk ((vtPre.drop 2292).take zBlk.length) = true := by
  simp only [vtPre_drop]; decide +kernel

theorem zTail_at : tbStmtsEqb zTail ((vtPre.drop 5225).take zTail.length) = true := by
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

/-- **Every iteration of `verify_tables_loop0` has its facts** on the honest buffers and words. -/
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
