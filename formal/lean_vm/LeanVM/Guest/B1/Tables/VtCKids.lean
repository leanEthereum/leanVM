/-
  LeanVM.Guest.B1.Tables.VtCKids

  `verify_tables`' 75 callees complete, placed, on its honest buffers (`VtKidsComplete`).
-/

module

public import LeanVM.Guest.B1.Tables.VerifyTablesCKids
public import LeanVM.Guest.B1.Tables.VtCLoopsB
public import LeanVM.Guest.B1.Tables.VtCSel
public import LeanVM.Guest.B1.Tables.VtCGlue
public import LeanVM.Guest.B1.Tables.FlockAt
public import LeanVM.Guest.B1.Tables.GkrOwn

/-!
# The callees, placed

Each taken callee of `vtKids` is one of the lifts `pw_completeAtD`, `sel_completeAtD`,
`idx_completeAtD`, `loop79_completeAtD`, `loop80_completeAtD`; their iterations' words are the
honest buffers' (`vtOwnW`, read through `vtc_own_sel` and `vtc_own_get`): a selector's bits and
chains (`vtc_selBody_honest`), the index chains (`vtc_idxBody_honest`), the table sumcheck's round
states and challenges (`vtc_zcRound_honest`) and its equality prefix (`vtc_peqBody_honest`).
`vt_kids_complete`: `VtKidsComplete`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Memory LeanVM.Guest.B1.Sig
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

/-! ## The honest buffers by index -/

theorem vtc_flatMap_length {α : Type} (g : ℕ → List α) (hg : ∀ i, (g i).length = 3) (m : ℕ) :
    ((List.range m).flatMap g).length = 3 * m := by
  rw [List.length_flatMap]
  simp only [hg, List.map_const', List.length_range, List.sum_replicate, smul_eq_mul]
  ring

theorem vtc_flatMap_getD {α : Type} (d : α) (g : ℕ → List α) (hg : ∀ i, (g i).length = 3) :
    ∀ m q r, q < m → r < 3 → ((List.range m).flatMap g).getD (3 * q + r) d = (g q).getD r d
  | 0, _, _, hq, _ => absurd hq (Nat.not_lt_zero _)
  | m + 1, q, r, hq, hr => by
    have hl := vtc_flatMap_length g hg m
    rw [List.range_succ, List.flatMap_append]
    rcases Nat.lt_or_ge q m with h | h
    · rw [List.getD_append _ _ _ _ (by omega)]
      exact vtc_flatMap_getD d g hg m q r h hr
    · obtain rfl : q = m := by omega
      rw [List.getD_append_right _ _ _ _ (by omega), hl, show 3 * q + r - 3 * q = r by omega]
      simp

/-- The 205 buffers' first part, the selectors' and the table sumcheck's. -/
theorem vtc_own_split (ks : ℕ → ℕ) (point : List E) (logMem n : ℕ) (cvr : ℕ → Digest) (cur : E)
    (cl ch : ℕ → E) (chis : List E) :
    vtOwnW ks point logMem n cvr cur cl ch chis =
      ([sortW ks, sideW, offW ks, idxcW, bimW point logMem] ++ selW ks point 0 ++ selW ks point 1 ++
        [idxChainW point logMem] ++ selW ks point 2 ++ [idxChainW point 18]) ++
      ((List.range 62).flatMap (fun i => selW ks point (i + 3)) ++
        [zcRoundsW cvr cur cl n, zcCprodW ch n, zcPeqW point chis n]) := by
  simp only [vtOwnW, List.append_assoc]

theorem vtc_selW_length (ks : ℕ → ℕ) (point : List E) (i : ℕ) : (selW ks point i).length = 3 := rfl

theorem vtc_ownA_length (ks : ℕ → ℕ) (point : List E) (logMem : ℕ) :
    ([sortW ks, sideW, offW ks, idxcW, bimW point logMem] ++ selW ks point 0 ++ selW ks point 1 ++
      [idxChainW point logMem] ++ selW ks point 2 ++ [idxChainW point 18]).length = 16 := rfl

theorem vtc_own_sel (ks : ℕ → ℕ) (point : List E) (logMem n : ℕ) (cvr : ℕ → Digest) (cur : E)
    (cl ch : ℕ → E) (chis : List E) {i r : ℕ} (hi : i < 65) (hr : r < 3) :
    (vtOwnW ks point logMem n cvr cur cl ch chis).getD (selBuf i + r) [] = (selW ks point i).getD r [] := by
  rcases Nat.lt_or_ge i 3 with h | h
  · interval_cases i <;> interval_cases r <;> rfl
  · rw [vtc_own_split, show selBuf i + r = 16 + (3 * (i - 3) + r) by unfold selBuf; split_ifs <;> omega,
      ← vtc_ownA_length ks point logMem, List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left,
      List.getD_append _ _ _ _ (by rw [vtc_flatMap_length _ (fun j => vtc_selW_length ks point (j + 3))]; omega),
      vtc_flatMap_getD [] _ (fun j => vtc_selW_length ks point (j + 3)) 62 (i - 3) r (by omega) hr,
      show i - 3 + 3 = i by omega]

theorem vtc_own_tail (ks : ℕ → ℕ) (point : List E) (logMem n : ℕ) (cvr : ℕ → Digest) (cur : E)
    (cl ch : ℕ → E) (chis : List E) {r : ℕ} (hr : r < 3) :
    (vtOwnW ks point logMem n cvr cur cl ch chis).getD (202 + r) [] =
      [zcRoundsW cvr cur cl n, zcCprodW ch n, zcPeqW point chis n].getD r [] := by
  rw [vtc_own_split, show 202 + r = 16 + (186 + r) by omega, ← vtc_ownA_length ks point logMem,
    List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left,
    show 186 + r = ((List.range 62).flatMap fun i => selW ks point (i + 3)).length + r by
      rw [vtc_flatMap_length _ (fun j => vtc_selW_length ks point (j + 3))],
    List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left]

theorem vtc_own_length (ks : ℕ → ℕ) (point : List E) (logMem n : ℕ) (cvr : ℕ → Digest) (cur : E)
    (cl ch : ℕ → E) (chis : List E) :
    (vtOwnW ks point logMem n cvr cur cl ch chis).length = (vtSizes n).length :=
  (vtOwnW_fit ks point logMem n cvr cur cl ch chis).length_eq

theorem vtc_sizes_length (n : ℕ) : (vtSizes n).length = 205 := by simp [vtSizes, selSz]

theorem vtc_bufL_mem {b : ℕ} {sizes : List ℕ} {cs : List (List E)} {i : ℕ} (hs : i < sizes.length)
    (hc : cs.length = sizes.length) : ((bases b sizes).getD i 0, cs.getD i []) ∈ bufL b sizes cs := by
  unfold bufL
  rw [List.getD_eq_getElem _ _ (by rw [length_bases]; omega), List.getD_eq_getElem _ _ (by omega)]
  exact List.mem_iff_getElem.mpr ⟨i, by simp [length_bases]; omega, by rw [List.getElem_zip]⟩

/-- Words of the layout, on a memory agreeing there. -/
theorem vtc_reads_mem {L : Main.Layout} {rd rd' : Reader} {a : ℕ} {w : List E} (hL : MemL rd L)
    (hm : (a, w) ∈ L) (hag : ∀ i, RegionL L i → rd' (gpow i) = rd (gpow i)) :
    ReadsAt rd' (ofK (gpow a)) w := fun k hk =>
  loadHolds_agree hag (hL _ hm k hk) ⟨a + k, Main.addr_ofK a k, ⟨(a, w), hm, by simp, by simp; omega⟩⟩

/-- **A buffer's honest words**, on a memory agreeing with one holding the caller's words and the
buffers. -/
theorem vtc_own_reads {Lin : Main.Layout} {b n : ℕ} {own : List (List E)} (hown : own.length = 205)
    {rd rd' : Reader} (hL : MemL rd (Lin ++ bufL b (vtSizes n) own))
    (hag : ∀ i, RegionL (Lin ++ bufL b (vtSizes n) own) i → rd' (gpow i) = rd (gpow i)) {i : ℕ}
    (hi : i < 205) : ReadsAt rd' (vtPtr b n i) (own.getD i []) :=
  vtc_reads_mem hL (List.mem_append_right _ (vtc_bufL_mem (by rw [vtc_sizes_length]; exact hi)
    (by rw [hown, vtc_sizes_length]))) hag

/-! ## The iterations on the honest words -/

/-- **A selector's iteration** on its honest bits and chains. -/
theorem vtc_selBody_honest {rd : Reader} {p12 p15 p16 zeta sq : E} {point : List E} {k off j : ℕ}
    (h12 : ReadsAt rd p12 ((List.range 34).map fun j => bitE (off.testBit j)))
    (h15 : ReadsAt rd p15 ((List.range 42).map fun t => if t ≤ point.length - k then
      ∏ j ∈ Finset.range t, (1 + bitE (off.testBit (k + j)) + point.getD (k + j) 0) else 0))
    (h16 : ReadsAt rd p16 ((List.range 42).map fun t => if t ≤ point.length - k then
      ∏ j ∈ Finset.range t, (1 + bitE (off.testBit (k + j)) * (gen ^ 2 ^ (k + j) + 1)) else 0))
    (hz : ReadsAt rd zeta point) (hsq : ∀ j < 34, LoadHolds rd sq j (gen ^ 2 ^ j)) (hμ : point.length < 33)
    (hj : j < point.length - k) :
    SelBody rd (p12 * gen ^ k) p15 (zeta * gen ^ k) p16 sq (gen ^ k) (gen ^ j) := by
  have L15 : ∀ t ≤ point.length - k, LoadHolds rd p15 t (vtcsC15 off k point t) := fun t ht => by
    have := vtcs_get h15 (t := t) (by omega)
    simpa only [ht, ↓reduceIte, vtcsC15] using this
  have L16 : ∀ t ≤ point.length - k, LoadHolds rd p16 t (vtcsC16 off k t) := fun t ht => by
    have := vtcs_get h16 (t := t) (by omega)
    simpa only [ht, ↓reduceIte, vtcsC16] using this
  refine ⟨bitE (off.testBit (k + j)), vtcsC15 off k point j, point.getD (k + j) 0, vtcsC16 off k j,
    gen ^ 2 ^ (k + j), ?_, vtcs_bitE_mul _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact loadHolds_gen_pow_mul.mpr (loadHolds_gen_pow_mul.mpr (by
      rw [Nat.add_zero]; exact vtcs_get (f := fun j => bitE (off.testBit j)) h12 (by omega)))
  · exact loadHolds_gen_pow_mul.mpr (by rw [Nat.add_zero]; exact L15 j (by omega))
  · exact loadHolds_gen_pow_mul.mpr (loadHolds_gen_pow_mul.mpr (by
      rw [Nat.add_zero, List.getD_eq_getElem _ _ (by omega)]; exact hz _ (by omega)))
  · refine loadHolds_gen_pow_mul.mpr ?_
    have := L15 (j + 1) (by omega)
    rwa [vtcsC15, Finset.prod_range_succ, ← vtcsC15] at this
  · exact loadHolds_gen_pow_mul.mpr (by rw [Nat.add_zero]; exact L16 j (by omega))
  · rw [← pow_add]
    exact loadHolds_gen_pow_mul.mpr (by rw [Nat.add_zero]; exact hsq _ (by omega))
  · refine loadHolds_gen_pow_mul.mpr ?_
    have := L16 (j + 1) (by omega)
    rwa [vtcsC16, Finset.prod_range_succ, ← vtcsC16] at this

theorem vtc_shift {rd : Reader} {p w : E} {a k a' k' : ℕ} (h : LoadHolds rd (p * gen ^ a) k w)
    (he : a + k = a' + k') : LoadHolds rd (p * gen ^ a') k' w :=
  loadHolds_gen_pow_mul.mpr (he ▸ loadHolds_gen_pow_mul.mp h)

theorem vtc_flatMap3_length {wsr : ℕ → List E} {n : ℕ} (h : ∀ r < n, (wsr r).length = 3) :
    ∀ m ≤ n, ((List.range m).flatMap wsr).length = 3 * m
  | 0, _ => by simp
  | m + 1, hm => by
    rw [List.range_succ, List.flatMap_append, List.length_append, vtc_flatMap3_length h m (by omega)]
    simp [h m (by omega)]; ring

/-- **A table sumcheck round** on the honest round states, challenges and their products. -/
theorem vtc_zcRound_honest {rd : Reader} {pR chi pC cur : E} {n j : ℕ} {cvr : ℕ → Digest}
    {cl ch : ℕ → E} {wsr : ℕ → List E} {chis : List E}
    (hR : ReadsAt rd pR (zcRoundsW cvr cur cl n)) (hC : ReadsAt rd pC (zcCprodW ch n))
    (hchi : ReadsAt rd chi chis) (hchis : chis = ((List.range n).map ch).reverse)
    (hws : ReadsAt rd (cur * gen ^ 5) ((List.range n).flatMap wsr))
    (hrun : ∀ r < n, RunsTo (roundPoly 4 (cl r) none) (cvr r) (wsr r) (cl (r + 1), ch r) (cvr (r + 1)))
    (hj : j < n) : ZcRound rd pR chi (gen ^ n) pC (gen ^ j) := by
  have hl3 : ∀ r < n, (wsr r).length = 3 := fun r hr => RunsTo.roundPoly4_inv (hrun r hr)
  have hblk := readsAt_flatMap_block hws hj
  rw [vtc_flatMap3_length hl3 j hj.le, mul_assoc, ← pow_add] at hblk
  obtain ⟨c0, c2, c3, hw⟩ : ∃ a b c, wsr j = [a, b, c] := by
    match h : wsr j, hl3 j hj with
    | [a, b, c], _ => exact ⟨a, b, c, rfl⟩
  rw [hw] at hblk
  have hrn := hrun j hj
  rw [hw] at hrn
  have B : ∀ r ≤ n, ReadsAt rd (pR * gen ^ (4 * r)) [(digestScalars (cvr r)).1, (digestScalars (cvr r)).2,
      cur * gen ^ (5 + 3 * r), cl r] := fun r hr => by
    have hR' : ReadsAt rd pR ((List.range (n + 1)).flatMap fun r => [(digestScalars (cvr r)).1,
        (digestScalars (cvr r)).2, cur * gen ^ (5 + 3 * r), cl r]) := hR
    have := readsAt_flatMap_block hR' (i := r) (by omega)
    rw [length_flatMap_range_const (w := 4) (fun _ => rfl)] at this
    exact this
  have Bj := B j hj.le
  have Bj1 := B (j + 1) hj
  have hx4 : pR * (gen ^ j) ^ 4 = pR * gen ^ (4 * j) := by rw [← pow_mul, Nat.mul_comm]
  have g0 : ∀ {k : ℕ} {w : E}, LoadHolds rd (pR * gen ^ (4 * (j + 1))) k w →
      LoadHolds rd (pR * gen ^ (4 * j)) (4 + k) w := fun h => vtc_shift h (by ring)
  have hq : gen ^ n * wInvG = gen ^ (n - 1 - j) * gen ^ j := by
    have e : gen ^ n = gen ^ (n - 1 - j) * gen ^ j * gen := by
      rw [← pow_add, ← pow_succ]; congr 1; omega
    rw [e, mul_assoc, show gen * wInvG = 1 by rw [mul_comm]; exact wInvG_mul_gen, mul_one]
  have hchj : LoadHolds rd (chi * gen ^ (n - 1 - j)) 0 (ch j) := by
    refine loadHolds_gen_pow_mul.mpr ?_
    have := hchi (n - 1 - j) (by rw [hchis]; simp; omega)
    rw [Nat.add_zero]
    convert this using 1
    subst hchis
    rw [List.getElem_reverse]
    simp only [List.getElem_map, List.getElem_range, List.length_map, List.length_range]
    congr 1; omega
  have Cj : LoadHolds rd (pC * gen ^ j) 0 (∏ r ∈ Finset.range j, ch r) := by
    refine loadHolds_gen_pow_mul.mpr ?_
    have := hC j (by simp [zcCprodW]; omega)
    simpa [zcCprodW] using this
  have Cj1 : LoadHolds rd (pC * gen ^ j) 1 ((∏ r ∈ Finset.range j, ch r) * ch j) := by
    refine loadHolds_gen_pow_mul.mpr ?_
    have := hC (j + 1) (by simp [zcCprodW]; omega)
    simpa [zcCprodW, Finset.prod_range_succ] using this
  refine ⟨cvr j, cur * gen ^ (5 + 3 * j), cl j, c0, c2, c3, cl (j + 1), ch j, cvr (j + 1),
    gen ^ (n - 1 - j), ∏ r ∈ Finset.range j, ch r, ?_, ?_, ?_, ?_, hblk, hrn, hq, hchj, ?_, ?_, ?_, ?_, Cj, Cj1⟩
  · rw [hx4]; exact Bj 0 (by simp)
  · rw [hx4]; exact Bj 1 (by simp)
  · rw [hx4]; exact Bj 2 (by simp)
  · rw [hx4]; exact Bj 3 (by simp)
  · rw [hx4]; exact g0 (k := 0) (Bj1 0 (by simp))
  · rw [hx4]; exact g0 (k := 1) (Bj1 1 (by simp))
  · rw [hx4]
    have := g0 (k := 2) (Bj1 2 (by simp))
    rwa [show cur * gen ^ (5 + 3 * (j + 1)) = cur * gen ^ (5 + 3 * j) * gen ^ 3 by
      rw [mul_assoc, ← pow_add]; ring_nf] at this
  · rw [hx4]; exact g0 (k := 3) (Bj1 3 (by simp))

/-- **The equality prefix's iteration** on its honest products. -/
theorem vtc_peqBody_honest {rd : Reader} {pP zeta chi : E} {point chis : List E} {n j : ℕ}
    (hP : ReadsAt rd pP (zcPeqW point chis n)) (hz : ReadsAt rd zeta point) (hchi : ReadsAt rd chi chis)
    (hj : j < n) (hn : n ≤ point.length) (hcl : chis.length = n) : PeqBody rd pP zeta chi (gen ^ j) := by
  have P : ∀ t ≤ n, LoadHolds rd pP t (∏ r ∈ Finset.range t, (1 + point.getD r 0 + chis.getD r 0)) :=
    fun t ht => by simpa [zcPeqW] using hP t (by simp [zcPeqW]; omega)
  refine ⟨_, point.getD j 0, chis.getD j 0, loadHolds_gen_pow_mul.mpr (by rw [Nat.add_zero]; exact P j hj.le),
    loadHolds_gen_pow_mul.mpr (by rw [Nat.add_zero, List.getD_eq_getElem _ _ (by omega)]; exact hz j (by omega)),
    loadHolds_gen_pow_mul.mpr (by rw [Nat.add_zero, List.getD_eq_getElem _ _ (by omega)]; exact hchi j (by omega)),
    loadHolds_gen_pow_mul.mpr ?_⟩
  have := P (j + 1) hj
  rwa [Finset.prod_range_succ] at this

/-! ## The callees -/

/-- **A selector's kid is complete**, on its honest buffers. -/
theorem vtc_sel_kidD {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ} {Lin : Main.Layout} {b n : ℕ}
    {ks : ℕ → ℕ} {point : List E} {own : List (List E)} {zeta sq : E} {i : ℕ} (hi : i < 65)
    (hown : own.length = 205) (hsel : ∀ r < 3, own.getD (selBuf i + r) [] = (selW ks point i).getD r [])
    (hLin : ∀ rd, LowDef κ rd → MemL rd Lin →
      ReadsAt rd zeta point ∧ ReadsAt rd sq ((List.range 34).map fun j => gen ^ 2 ^ j))
    (hμ : point.length < 33) (hm0 : 0 < point.length - ks (selBlk.getD i 0)) :
    CompleteAtD fs cert κ (selNames.getD i "") (Lin ++ bufL b (vtSizes n) own)
      [1, gen ^ (point.length - ks (selBlk.getD i 0)), vtPtr b n (selBuf i) * gen ^ ks (selBlk.getD i 0),
        vtPtr b n (selBuf i + 1), zeta * gen ^ ks (selBlk.getD i 0), vtPtr b n (selBuf i + 2), sq,
        gen ^ ks (selBlk.getD i 0)] (Returns []) := by
  have hb : selBuf i + 2 < 205 := by unfold selBuf; split_ifs <;> omega
  refine sel_completeAtD (sel_ok i hi) (vtSel_mem i hi) hm0 κ fun rd hlow hL rd' hag j hj => ?_
  obtain ⟨hL1, -⟩ := Main.memL_append.mp hL
  have hagL : ∀ t, RegionL Lin t → rd' (gpow t) = rd (gpow t) := fun t ht =>
    hag t (regionL_append.mpr (Or.inl ht))
  have hz := readsAt_transfer (fun rd h1 h2 => (hLin rd h1 h2).1) hlow hL1 hagL
  have hsq := readsAt_transfer (fun rd h1 h2 => (hLin rd h1 h2).2) hlow hL1 hagL
  have R0 := vtc_own_reads hown hL hag (i := selBuf i + 0) (by omega)
  have R1 := vtc_own_reads hown hL hag (i := selBuf i + 1) (by omega)
  have R2 := vtc_own_reads hown hL hag (i := selBuf i + 2) (by omega)
  rw [hsel 0 (by omega)] at R0
  rw [hsel 1 (by omega)] at R1
  rw [hsel 2 (by omega)] at R2
  exact vtc_selBody_honest R0 R1 R2 hz (fun t ht => vtcs_get (f := fun j => gen ^ 2 ^ j) hsq ht) hμ hj

/-- `vtOwnW`'s buffers `3`, `11`, `15`. -/
theorem vtc_own_idx (ks : ℕ → ℕ) (point : List E) (logMem n : ℕ) (cvr : ℕ → Digest) (cur : E)
    (cl ch : ℕ → E) (chis : List E) :
    (vtOwnW ks point logMem n cvr cur cl ch chis).getD 3 [] = idxcW ∧
      (vtOwnW ks point logMem n cvr cur cl ch chis).getD 11 [] = idxChainW point logMem ∧
      (vtOwnW ks point logMem n cvr cur cl ch chis).getD 15 [] = idxChainW point 18 := ⟨rfl, rfl, rfl⟩

set_option maxHeartbeats 1000000 in
/-- **`verify_tables`' callees are complete, placed**, on its honest buffers. -/
theorem vt_kids_complete : VtKidsComplete := by
  intro fs cert κ hκ Lin b n logMem ks τs nr point chis cvr cur cl ch wsr zeta sq chiP hμ hlm h18 hn hks hτ
    hchis hrun hLin k hk ht
  have hown := (vtc_own_length ks point logMem n cvr cur cl ch chis).trans (vtc_sizes_length n)
  have hzs : ∀ rd, LowDef κ rd → MemL rd Lin →
      ReadsAt rd zeta point ∧ ReadsAt rd sq ((List.range 34).map fun j => gen ^ 2 ^ j) := fun rd h1 h2 =>
    ⟨(hLin rd h1 h2).1, fun t ht => by simpa using (hLin rd h1 h2).2.1 t (by simpa using ht)⟩
  obtain ⟨o3, o11, o15⟩ := vtc_own_idx ks point logMem n cvr cur cl ch chis
  have hidxR : ∀ {rd rd' : Reader}, LowDef κ rd →
      MemL rd (Lin ++ bufL b (vtSizes n) (vtOwnW ks point logMem n cvr cur cl ch chis)) →
      (∀ i, RegionL (Lin ++ bufL b (vtSizes n) (vtOwnW ks point logMem n cvr cur cl ch chis)) i →
        rd' (gpow i) = rd (gpow i)) →
      ReadsAt rd' zeta point ∧ (∀ t < 34, LoadHolds rd' (vtPtr b n 3) t (1 + gen ^ 2 ^ t)) := by
    intro rd rd' hlow hL hag
    obtain ⟨hL1, -⟩ := Main.memL_append.mp hL
    refine ⟨readsAt_transfer (fun rd h1 h2 => (hLin rd h1 h2).1) hlow hL1
      fun t ht => hag t (regionL_append.mpr (Or.inl ht)), fun t ht => ?_⟩
    have R := vtc_own_reads hown hL hag (i := 3) (by omega)
    rw [o3] at R
    exact vtcs_get (f := fun t => 1 + gen ^ 2 ^ t) R ht
  simp only [vtKids, List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false] at hk
  rcases hk with ((⟨t, ht6, rfl⟩ | rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩) | rfl | rfl
  · obtain ⟨h29, hτp, hnr⟩ := hτ t ht6
    have hj : τs t < pwNames.length := by simpa [pwNames] using h29
    show CompleteAtD fs cert κ (pwNames.getD (τs t) "") Lin _ _
    rw [List.getD_eq_getElem _ _ hj]
    exact pw_completeAtD (τs t) hj hnr hτp (fun rd h1 h2 => (hLin rd h1 h2).1)
  · exact vtc_sel_kidD (i := 0) (by norm_num) hown
      (fun r hr => vtc_own_sel ks point logMem n cvr cur cl ch chis (by norm_num) hr) hzs hμ
      (Nat.pos_of_ne_zero (by simpa using ht))
  · exact vtc_sel_kidD (i := 1) (by norm_num) hown
      (fun r hr => vtc_own_sel ks point logMem n cvr cur cl ch chis (by norm_num) hr) hzs hμ
      (Nat.pos_of_ne_zero (by simpa using ht))
  · refine idx_completeAtD idx_ok.1 (by simp) (Nat.pos_of_ne_zero (by simpa using ht)) κ
      fun rd hlow hL rd' hag j hj => ?_
    obtain ⟨hz, hidx⟩ := hidxR hlow hL hag
    have R := vtc_own_reads hown hL hag (i := 11) (by omega)
    rw [o11] at R
    exact vtc_idxBody_honest hz hidx R hj (by omega) (by omega)
  · exact vtc_sel_kidD (i := 2) (by norm_num) hown
      (fun r hr => vtc_own_sel ks point logMem n cvr cur cl ch chis (by norm_num) hr) hzs hμ
      (Nat.pos_of_ne_zero (by simpa using ht))
  · refine idx_completeAtD idx_ok.2 (by simp) (by norm_num) κ fun rd hlow hL rd' hag j hj => ?_
    obtain ⟨hz, hidx⟩ := hidxR hlow hL hag
    have R := vtc_own_reads hown hL hag (i := 15) (by omega)
    rw [o15] at R
    exact vtc_idxBody_honest hz hidx R hj (by omega) (by omega)
  · exact vtc_sel_kidD (i := i + 3) (by omega) hown
      (fun r hr => vtc_own_sel ks point logMem n cvr cur cl ch chis (by omega) hr) hzs hμ
      (Nat.pos_of_ne_zero (by simpa using ht))
  · refine loop79_completeAtD (Nat.pos_of_ne_zero (by simpa using ht)) κ fun rd hlow hL rd' hag j hj => ?_
    obtain ⟨hL1, -⟩ := Main.memL_append.mp hL
    have hagL : ∀ t, RegionL Lin t → rd' (gpow t) = rd (gpow t) := fun t ht =>
      hag t (regionL_append.mpr (Or.inl ht))
    have hchi := readsAt_transfer (fun rd h1 h2 => (hLin rd h1 h2).2.2.1) hlow hL1 hagL
    have hws := readsAt_transfer (fun rd h1 h2 => (hLin rd h1 h2).2.2.2) hlow hL1 hagL
    have R := vtc_own_reads hown hL hag (i := 202 + 0) (by omega)
    have C := vtc_own_reads hown hL hag (i := 202 + 1) (by omega)
    rw [vtc_own_tail ks point logMem n cvr cur cl ch chis (by omega)] at R C
    exact vtc_zcRound_honest R C hchi hchis hws hrun hj
  · refine loop80_completeAtD (Nat.pos_of_ne_zero (by simpa using ht)) κ fun rd hlow hL rd' hag j hj => ?_
    obtain ⟨hL1, -⟩ := Main.memL_append.mp hL
    have hagL : ∀ t, RegionL Lin t → rd' (gpow t) = rd (gpow t) := fun t ht =>
      hag t (regionL_append.mpr (Or.inl ht))
    have hz := readsAt_transfer (fun rd h1 h2 => (hLin rd h1 h2).1) hlow hL1 hagL
    have hchi := readsAt_transfer (fun rd h1 h2 => (hLin rd h1 h2).2.2.1) hlow hL1 hagL
    have P := vtc_own_reads hown hL hag (i := 202 + 2) (by omega)
    rw [vtc_own_tail ks point logMem n cvr cur cl ch chis (by omega)] at P
    exact vtc_peqBody_honest P hz hchi hj hn (by rw [hchis]; simp)

end
end LeanVM.Guest.B1.VerifySub
