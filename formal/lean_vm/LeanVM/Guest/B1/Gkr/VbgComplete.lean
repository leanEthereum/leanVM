/-
  LeanVM.Guest.B1.Gkr.VbgComplete

  `verify_bus_gkr` is complete: on the words an accepting run of the GKR phase reads, at the
  cursor, the point at `zeta`, and its buffers' honest words (as runs, at any bases), it returns
  the run's capacity, the cursor past the words and the three values.
-/

module

public import LeanVM.Guest.B1.Gkr.VbgC
public import LeanVM.Guest.B1.Gkr.WalkC

/-!
# `verify_bus_gkr`, completely (TRIAGE G #43)

The buffers' honest words (`vbgLay`), as functions of the walk read back from the run
(`gk_walk`: the slots `gkSl`, the steps' words `gkD`):

* `layers` (at `g^eL`): the slot before every step of two levels (`L = 2j + sh`), and the root
  slot (`L = 0`) at an odd depth, seventeen words each (`gkSlotWords`);
* the point rows (at `g^eP`): slot `j`'s point at `40·(j + sh)`;
* the round records (at `g^eR`): step `j`'s `L + 1` records from position `gkPos sh j`, field `f`
  `862·f` on (`gkRecW`: the capacity, the cursor and the claim after `r` rounds);
* the tables `k_mod_next` (at `g^eK`), `pairs` (at `g^ePa`) and `depth_shift` (at `g^eD`).

`verify_bus_gkr_complete`: at `1 ≤ depth ≤ 32`, an accepting run of `gkrPhase depth` from a
carried capacity, its words at the cursor, its point at `zeta`, the memory defined at `g^depth`
and `g^(32 - depth)` (the range check) and holding `vbgLay` give the relation.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

open LeanVM.Guest.B1.Fwd

@[expose] public section

/-! ## Words at powers of `g` -/

theorem tb_ofK_gpow_mul (e k : ℕ) : ofK (addressOfIndex e) * gen ^ k = ofK (addressOfIndex (e +
    k)) := by
  rw [gen_pow_eq_ofK, ← ofK_mul, Parameters.addressOfIndex, Parameters.addressOfIndex,
      Parameters.addressOfIndex, ← pow_add]

/-- A run's word at `g^(e + a)`, read from `g^e`. -/
theorem tb_reads_load {rd : Reader} {e a : ℕ} {ws : List E} (h : TbReadsAt rd (ofK (addressOfIndex (e + a))) ws)
    {k : ℕ} (hk : k < ws.length) : LoadHolds rd (ofK (addressOfIndex e)) (a + k) (ws.getD k 0) := by
  rw [← tb_loadHolds_mul_gen_pow, tb_ofK_gpow_mul, List.getD_eq_getElem _ _ hk]
  exact h k hk

/-! ## A slot's words -/

/-- **A slot's seventeen words**: the capacity, the cursor, the values, the row, the position,
`half`, `parity`, the rate cells. -/
def gkSlotWords (s : Fs) (cur : E) (st : GkrState) (row pos half par : E) : List E :=
  s.cap ++ [cur] ++ st.values ++ [row, pos, half, par] ++ (rateOf s.pend).take 4

/-- **A slot from its words.** -/
theorem gkSlotC_of {rd : Reader} {eL L : ℕ} {s : Fs} {cur : E} {st : GkrState}
    {row pos half par : E} (hcl : s.cap.length = 5) (hcan : AllCanonical s.cap)
    (hpe : s.pend.length ≤ 2) (hvl : st.values.length = 3) (hpl : st.point.length = L)
    (hpt : TbReadsAt rd row st.point)
    (hw : TbReadsAt rd (ofK (addressOfIndex (eL + 17 * L))) (gkSlotWords s cur st row pos half
        par)) :
    GkSlotC rd (ofK (addressOfIndex eL)) L s cur st row pos half par := by
  obtain ⟨c0, c1, c2, c3, c4, hc⟩ := tb_list5_eq hcl
  obtain ⟨v0, v1, v2, hv⟩ := tb_list3_eq hvl
  have hrl : ((rateOf s.pend).take 4).length = 4 := by simp [rateOf]
  obtain ⟨r0, r1, r2, r3, hr⟩ : ∃ r0 r1 r2 r3, (rateOf s.pend).take 4 = [r0, r1, r2, r3] := by
    match (rateOf s.pend).take 4, hrl with
    | [r0, r1, r2, r3], _ => exact ⟨r0, r1, r2, r3, rfl⟩
  have hgr : ∀ k < 4, (rateOf s.pend).getD k 0 = [r0, r1, r2, r3].getD k 0 := by
    intro k hk
    rw [← hr, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hk]
  have hwl : (gkSlotWords s cur st row pos half par).length = 17 := by
    simp [gkSlotWords, hcl, hvl, hrl]
  have ld := fun k (hk : k < 17) => tb_reads_load hw (k := k) (by rw [hwl]; exact hk)
  simp only [gkSlotWords, hc, hv, hr, List.cons_append, List.nil_append]
    at ld
  refine ⟨hcl, hcan, hpe, fun k hk => ?_, fun k hk => ?_, ld 5 (by omega), hvl, fun t ht => ?_,
    ld 9 (by omega), hpl, hpt, ld 10 (by omega), ld 11 (by omega), ld 12 (by omega)⟩
  · rw [hc]; interval_cases k <;> exact ld _ (by omega)
  · rw [hgr k hk, Nat.add_assoc]; interval_cases k <;> exact ld _ (by omega)
  · rw [hv, Nat.add_assoc]; interval_cases t <;> exact ld _ (by omega)

/-! ## The round records -/

theorem tb_gkrRun_cap_len : ∀ (cs : List (List E)) (es : List E) (claim : E) (s : Fs),
    s.cap.length = 5 → (gkrRun cs es claim s).2.2.cap.length = 5
  | [], _, _, _, h => by cases ‹List E› <;> exact h
  | c :: cs, [], _, _, h => h
  | c :: cs, e :: es, claim, s, _ => by
    simp only [gkrRun]
    exact tb_gkrRun_cap_len _ _ _ _ (by simp [Fs.squeeze, capOf])

/-- Step `j`'s first record's position: one record for the odd step at an odd depth, then
`L + 1` for each step of `L` rounds. -/
def gkPos (sh : ℕ) : ℕ → ℕ
  | 0 => sh
  | j + 1 => gkPos sh j + (2 * j + sh) + 1

/-- Step `j`'s first `r` rounds: challenges, claim, sponge. -/
def gkRunAt (cap0 xs : List E) (sh j r : ℕ) : List E × E × Fs :=
  gkrRun ((gkD cap0 xs sh j).cs.take r) ((gkSl cap0 xs sh j).2.1.point.take r)
    (polyEval (gkSl cap0 xs sh j).2.1.values (gkSl cap0 xs sh j).1.squeeze.1)
    (gkSl cap0 xs sh j).1.squeeze.2

/-- Field `f` of step `j`'s record `r`: the capacity cells, the cursor, the claim. -/
def gkRecW (cap0 xs : List E) (sh : ℕ) (cur : E) (j f r : ℕ) : E :=
  if f < 5 then (gkRunAt cap0 xs sh j r).2.2.cap.getD f 0
  else if f = 5 then cur * gen ^ ((gkSl cap0 xs sh j).2.2 + 4 * r)
  else (gkRunAt cap0 xs sh j r).2.1

/-- **Step `j`'s records**: field `f` of its `L + 1` records, `862·f` on from its position. -/
def gkRecRuns (cap0 xs : List E) (sh : ℕ) (cur : E) (eR j : ℕ) : TLay :=
  (List.range 7).map fun f ↦
    (eR + 862 * f + gkPos sh j, (List.range (2 * j + sh + 1)).map (gkRecW cap0 xs sh cur j f))

/-- **The records from their runs.** -/
theorem recsAt_of {rd : Reader} {cap0 xs : List E} {sh : ℕ} {cur : E} {eR j : ℕ}
    (hm : MemLay rd (gkRecRuns cap0 xs sh cur eR j))
    (hcs : (gkD cap0 xs sh j).cs.length = 2 * j + sh) :
    RecsAt rd (ofK (addressOfIndex eR) * gen ^ gkPos sh j) (cur * gen ^ (gkSl cap0 xs sh j).2.2)
      (gkD cap0 xs sh j).cs (gkSl cap0 xs sh j).2.1.point
      (polyEval (gkSl cap0 xs sh j).2.1.values (gkSl cap0 xs sh j).1.squeeze.1)
      (gkSl cap0 xs sh j).1.squeeze.2 := by
  intro r hr
  have F : ∀ f < 7, LoadHolds rd (ofK (addressOfIndex eR) * gen ^ gkPos sh j * gen ^ r) (f * 862)
      (gkRecW cap0 xs sh cur j f r) := by
    intro f hf
    have hq := hm _ (List.mem_map.mpr ⟨f, List.mem_range.mpr hf, rfl⟩)
    simp only at hq
    rw [Nat.add_assoc] at hq
    have h := tb_reads_load hq (k := r) (by simp; omega)
    rw [tb_loadHolds_mul_gen_pow, tb_loadHolds_mul_gen_pow,
      show gkPos sh j + (r + f * 862) = 862 * f + gkPos sh j + r by ring]
    simpa [List.getD_eq_getElem?_getD, show r < 2 * j + sh + 1 by omega] using h
  have hcl : (gkRunAt cap0 xs sh j r).2.2.cap.length = 5 :=
    tb_gkrRun_cap_len _ _ _ _ (by simp [Fs.squeeze, capOf])
  refine ⟨⟨hcl, fun i hi => ?_⟩, ?_, ?_⟩
  · have hi5 : i < 5 := lt_of_lt_of_eq hi hcl
    have h := F i (by omega)
    simp only [gkRecW, hi5, ↓reduceIte] at h
    unfold gkRunAt at h
    rw [List.getD_eq_getElem _ _ hi] at h
    rw [Nat.zero_add]
    exact h
  · have h := F 5 (by omega)
    simp only [gkRecW, show ¬ (5 < 5) by omega, ↓reduceIte, pow_add, ← mul_assoc] at h
    exact h
  · have h := F 6 (by omega)
    simp only [gkRecW, show ¬ (6 < 5) by omega, show (6 : ℕ) ≠ 5 by omega, ↓reduceIte] at h
    exact h

/-! ## The walk's slots -/

theorem tb_squeezeN_one (s : Fs) : s.squeezeN 1 = ([challengeOf s.perm], ⟨capOf s.perm, []⟩) :=
  rfl

theorem tb_s'_one (D : GkStepD) (s : Fs) (st : GkrState) :
    (D.s' s st 1).cap.length = 5 ∧ AllCanonical (D.s' s st 1).cap ∧ (D.s' s st 1).pend = [] := by
  rw [show D.s' s st 1 = ((D.sb s st).squeezeN 1).2 from rfl, tb_squeezeN_one]
  exact ⟨by simp [capOf], tb_capOf_canonical _, rfl⟩

theorem tb_s'_two (D : GkStepD) (s : Fs) (st : GkrState) :
    (D.s' s st 2).cap.length = 5 ∧ AllCanonical (D.s' s st 2).cap ∧ (D.s' s st 2).pend = [] := by
  rw [show D.s' s st 2 = ((D.sb s st).squeezeN 2).2 from rfl, tb_squeezeN_two]
  exact ⟨by simp [capOf], tb_capOf_canonical _, rfl⟩

/-- **The slots' sponges and values**: five canonical capacity cells, at most two scalars
waiting, three values. -/
theorem gkSl_inv {cap0 xs : List E} {sh : ℕ} (hcl : cap0.length = 5) (hcan : AllCanonical cap0) :
    ∀ j, (gkSl cap0 xs sh j).1.cap.length = 5 ∧ AllCanonical (gkSl cap0 xs sh j).1.cap ∧
      (gkSl cap0 xs sh j).1.pend.length ≤ 2 ∧ (gkSl cap0 xs sh j).2.1.values.length = 3
  | 0 => by
    unfold gkSl gkSl0
    split
    · obtain ⟨h1, h2, h3⟩ := tb_s'_one (gkOdd xs) (gkRootS cap0 xs) (gkRootSt xs)
      exact ⟨h1, h2, by rw [h3]; simp, by simp [GkStepD.st']⟩
    · exact ⟨hcl, hcan, by simp [gkRootS], by simp [gkRootSt]⟩
  | j + 1 => by
    rw [gkSl_succ]
    obtain ⟨h1, h2, h3⟩ := tb_s'_two (gkD cap0 xs sh j) (gkSl cap0 xs sh j).1
      (gkSl cap0 xs sh j).2.1
    exact ⟨h1, h2, by rw [h3]; simp, by simp [GkStepD.st']⟩

/-- **The slots' point lengths**: `2j + sh` while the steps are taken. -/
theorem gkSl_point_len {cap0 xs : List E} {sh n : ℕ}
    (h0 : (gkSl cap0 xs sh 0).2.1.point.length = sh)
    (hok : ∀ j < n, (gkD cap0 xs sh j).Ok (gkSl cap0 xs sh j).1 (gkSl cap0 xs sh j).2.1 2) :
    ∀ j ≤ n, (gkSl cap0 xs sh j).2.1.point.length = 2 * j + sh := by
  intro j hj
  induction j with
  | zero => simpa using h0
  | succ j ih =>
    rw [gkSl_succ]
    exact (gkStepD_point_length (hok j (by omega))).trans (by rw [ih (by omega)]; ring)

theorem tb_drop_le {xs ys : List E} {a b : ℕ} (h : xs.drop a = ys ++ xs.drop b)
    (hy : ys.length = b - a) (hab : a < b) : b ≤ xs.length := by
  have := congrArg List.length h
  simp only [List.length_drop, List.length_append] at this
  omega

theorem gkStepD_xs_length {D : GkStepD} {s : Fs} {st : GkrState} {n : ℕ} (h : D.Ok s st n) :
    D.xs.length = 4 * st.point.length + 3 * 2 ^ n := by
  obtain ⟨hl, h4, h0, h1, h2, -⟩ := h
  simp [GkStepD.xs, flatten_length_four h4, hl, h0, h1, h2]
  ring

theorem tb_gkrRun_nil_es (cs : List (List E)) (claim : E) (s : Fs) :
    gkrRun cs [] claim s = ([], claim, s) := by
  cases cs <;> rfl

/-- The slot before the steps of two levels: its point, `sh` coordinates. -/
theorem gkSl0_point_len (cap0 xs : List E) (sh : ℕ) (hsh : sh < 2) :
    (gkSl cap0 xs sh 0).2.1.point.length = sh := by
  unfold gkSl gkSl0
  split
  · rename_i h
    show ((gkOdd xs).ys _ _ 1 ++ ((gkOdd xs).run (gkRootS cap0 xs) (gkRootSt xs)).1).length = sh
    rw [GkStepD.run, show (gkRootSt xs).point = [] from rfl, tb_gkrRun_nil_es, h]
    rfl
  · show (gkRootSt xs).point.length = sh
    simp [gkRootSt]; omega

/-- The offset of the slot before the steps of two levels. -/
theorem gkSl0_off (cap0 xs : List E) (sh : ℕ) :
    (gkSl cap0 xs sh 0).2.2 = if sh = 1 then 8 else 2 := by
  unfold gkSl gkSl0
  split <;> rfl

/-! ## The buffers' honest words -/

/-- **The table `k_mod_next`'s eight words** (G:1802-1805): at `r < 4` the next layer index's
`g^((r + 1) % 4)`, at `4 + r` its carry `g^((r + 1) / 4)`. -/
def kmnWords : List E :=
  (List.range 8).map fun i ↦ if i < 4 then gen ^ ((i + 1) % 4) else gen ^ ((i - 4 + 1) / 4)

/-- **The table `k_mod_next` from its words.** -/
theorem kModNext_of {rd : Reader} {kmn : E} (h : TbReadsAt rd kmn kmnWords) : KModNext rd kmn := by
  intro r hr
  have h0 := h r (by simp [kmnWords]; omega)
  have h4 := h (4 + r) (by simp [kmnWords]; omega)
  simp only [kmnWords, List.getElem_map, List.getElem_range] at h0 h4
  have h4r : ¬ (4 + r < 4) := by omega
  simp only [hr, h4r, ↓reduceIte, show 4 + r - 4 = r by omega] at h0 h4
  exact ⟨h4, h0⟩

/-- **`verify_bus_gkr`'s buffers' honest words** on the walk from the carried capacity `cap0`
over the words `xs` at the cursor `cur`: the slots of `layers` at `g^eL`, the point rows at
`g^eP`, the round records at `g^eR`, `k_mod_next` at `g^eK`, `pairs` at `g^ePa` and
`depth_shift` at `g^eD`. -/
def vbgLay (depth : ℕ) (cap0 xs : List E) (cur : E) (eL eR eP eK ePa eD : ℕ) : TLay :=
  (if depth % 2 = 1 then
    [(eL, gkSlotWords (gkRootS cap0 xs) (cur * gen ^ 2) (gkRootSt xs) (ofK (addressOfIndex eP))
        1 1 1)]
  else []) ++
  (List.range (depth / 2 + 1)).map (fun j ↦ (eL + 17 * (2 * j + depth % 2),
    gkSlotWords (gkSl cap0 xs (depth % 2) j).1 (cur * gen ^ (gkSl cap0 xs (depth % 2) j).2.2)
      (gkSl cap0 xs (depth % 2) j).2.1 (ofK (addressOfIndex eP) * gen ^ (40 * (j + depth % 2)))
      (gen ^ gkPos (depth % 2) j) (gen ^ (j / 4)) (gen ^ (j % 4)))) ++
  (List.range (depth / 2 + 1)).map (fun j ↦ (eP + 40 * (j + depth % 2),
    (gkSl cap0 xs (depth % 2) j).2.1.point)) ++
  ((List.range (depth / 2)).map (gkRecRuns cap0 xs (depth % 2) cur eR)).flatten ++
  [(ePa, (List.range 33).map fun k ↦ gen ^ (k / 2)),
    (eD, (List.range 33).map fun k ↦ gen ^ (k % 2)), (eK, kmnWords)]

/-- **`verify_bus_gkr`'s body holds of its honest valuation** (TRIAGE G #43): at `1 ≤ depth ≤ 32`, an accepting run of
`gkrPhase depth` from a carried capacity `cap0` reading `xs`, the words `xs` at the cursor, the
run's point at `zeta`, the memory defined at `g^depth` and `g^(32 - depth)` (the range check) and
holding the buffers' honest words (`vbgLay`, at any bases) give the relation, returning the run's
capacity, the cursor past `xs` and the three values. -/
theorem verify_bus_gkr_body {rd : Reader} {depth : ℕ} (hd1 : 1 ≤ depth) (hd : depth ≤ 32)
    {cap0 xs : List E} {r : E × List E × List E} {cap' : List E}
    (hrun : RunsTo (gkrPhase depth) ⟨cap0, []⟩ xs r ⟨cap', []⟩)
    (hc : ∃ sp, (⟨cap0, []⟩ : Fs).Carries sp) {cur zeta : E} (hx : TbReadsAt rd cur xs)
    (hz : TbReadsAt rd zeta r.2.1) {eL eR eP eK ePa eD : ℕ}
    (hm : MemLay rd (vbgLay depth cap0 xs cur eL eR eP eK ePa eD))
    (hrc : (rd (addressOfIndex depth)).isSome = true ∧ (rd (addressOfIndex (32 - depth))).isSome =
        true) :
    Stmt.HoldsList (coreProgram.Rel rd) rd
        (B1.Val.ofArgs (ev rd (vbgW (ofK (addressOfIndex eL)) (ofK (addressOfIndex eR)) (ofK (addressOfIndex eP)) (ofK (addressOfIndex eK)) (ofK (addressOfIndex ePa)) (ofK (addressOfIndex eD)))
          (cap0 ++ [cur, gen ^ depth, zeta]) vbgEvL)) vbgPre True
        (fun rs => rs = cap' ++ [cur * gen ^ xs.length] ++ r.2.2) ∧
      vbgRets.map (B1.Val.ofArgs (ev rd (vbgW (ofK (addressOfIndex eL)) (ofK (addressOfIndex eR)) (ofK (addressOfIndex eP)) (ofK (addressOfIndex eK)) (ofK (addressOfIndex ePa)) (ofK (addressOfIndex eD)))
        (cap0 ++ [cur, gen ^ depth, zeta]) vbgEvL)) = cap' ++ [cur * gen ^ xs.length] ++ r.2.2 := by
  obtain ⟨hcnt, hx2, hodd, hsteps, hend, hsF, hr, hplm⟩ := gk_walk hrun hc
  obtain ⟨sp, hsp⟩ := hc
  have hsc : capOf sp.state = cap0 := hsp.1
  have hcl : cap0.length = 5 := by rw [← hsc]; simp [capOf]
  have hcan : AllCanonical cap0 := by rw [← hsc]; exact tb_capOf_canonical _
  unfold vbgLay at hm
  rw [memLay_append, memLay_append, memLay_append, memLay_append] at hm
  obtain ⟨⟨⟨⟨hmR, hmS⟩, hmP⟩, hmC⟩, hmT⟩ := hm
  set sh := depth % 2 with hsh
  set m := depth / 2 with hmm
  have hsh2 : sh < 2 := by omega
  have inv := gkSl_inv (xs := xs) (sh := sh) hcl hcan
  have hpl : ∀ j ≤ m, (gkSl cap0 xs sh j).2.1.point.length = 2 * j + sh :=
    gkSl_point_len (gkSl0_point_len cap0 xs sh hsh2) fun j hj => (hsteps j hj).1
  -- the slots
  have SL : ∀ j ≤ m, GkSlotC rd (ofK (addressOfIndex eL)) (2 * j + sh) (gkSl cap0 xs sh j).1
      (cur * gen ^ (gkSl cap0 xs sh j).2.2) (gkSl cap0 xs sh j).2.1
      (ofK (addressOfIndex eP) * gen ^ (40 * (j + sh))) (gen ^ gkPos sh j) (gen ^ (j / 4))
      (gen ^ (j % 4)) := fun j hj =>
    gkSlotC_of (inv j).1 (inv j).2.1 (inv j).2.2.1 (inv j).2.2.2 (hpl j hj)
      (by rw [tb_ofK_gpow_mul]
          exact hmP (eP + 40 * (j + sh), (gkSl cap0 xs sh j).2.1.point)
            (List.mem_map.mpr ⟨j, List.mem_range.mpr (by omega), rfl⟩))
      (hmS (eL + 17 * (2 * j + sh), gkSlotWords (gkSl cap0 xs sh j).1
          (cur * gen ^ (gkSl cap0 xs sh j).2.2) (gkSl cap0 xs sh j).2.1
          (ofK (addressOfIndex eP) * gen ^ (40 * (j + sh))) (gen ^ gkPos sh j) (gen ^ (j / 4))
          (gen ^ (j % 4)))
        (List.mem_map.mpr ⟨j, List.mem_range.mpr (by omega), rfl⟩))
  -- the offsets
  have hOle : ∀ j ≤ m, (gkSl cap0 xs sh j).2.2 ≤ xs.length := by
    intro j hj
    rcases j with _ | j
    · rw [gkSl0_off]
      split
      · rename_i h1
        obtain ⟨hok, hdr⟩ := hodd h1
        have h6 : (gkOdd xs).xs.length = 6 := by
          rw [gkStepD_xs_length hok]; rfl
        exact tb_drop_le hdr (by rw [h6]) (by omega)
      · exact hx2
    · obtain ⟨hok, hdr⟩ := hsteps j (by omega)
      have hO : (gkSl cap0 xs sh (j + 1)).2.2 = (gkSl cap0 xs sh j).2.2 + 4 * (2 * j + sh) + 12 :=
        rfl
      have h12 : (3 : ℕ) * 2 ^ 2 = 12 := by norm_num
      refine tb_drop_le hdr ?_ (by rw [hO]; omega)
      rw [gkStepD_xs_length hok, hpl j (by omega), hO]
      omega
  have hOm : (gkSl cap0 xs sh m).2.2 = xs.length := by
    have := List.drop_eq_nil_iff.mp hend
    exact le_antisymm (hOle m le_rfl) this
  -- the words each step reads
  have hdrop : ∀ a ≤ xs.length, TbReadsAt rd (cur * gen ^ a) (xs.drop a) := by
    intro a ha
    have h := hx
    rw [← List.take_append_drop a xs, tbReadsAt_append, List.length_take_of_le ha] at h
    exact h.2
  -- the relation
  have hx0 : LoadHolds rd cur 0 (xs.getD 0 0) := by
    have := hx 0 (by omega); rwa [← List.getD_eq_getElem _ 0] at this
  have hx1 : LoadHolds rd cur 1 (xs.getD 1 0) := by
    have := hx 1 (by omega); rwa [← List.getD_eq_getElem _ 0] at this
  have hroot : GkSlotC rd (ofK (addressOfIndex eL)) 0 (gkRootS cap0 xs) (cur * gen ^ 2)
      (gkRootSt xs)
      (ofK (addressOfIndex eP)) 1 1 1 := by
    by_cases h1 : sh = 1
    · refine gkSlotC_of hcl hcan (by simp [gkRootS]) (by simp [gkRootSt]) rfl (tbReadsAt_nil _ _) ?_
      rw [show eL + 17 * 0 = eL by ring]
      exact hmR (eL, gkSlotWords (gkRootS cap0 xs) (cur * gen ^ 2) (gkRootSt xs) (ofK
          (addressOfIndex eP))
        1 1 1) (by simp [h1])
    · have h00 : sh = 0 := by omega
      have h0 : gkSl cap0 xs sh 0 = (gkRootS cap0 xs, gkRootSt xs, 2) := by
        unfold gkSl gkSl0; simp [h1]
      have h := SL 0 (by omega)
      rw [h0] at h
      simp only [h00, gkPos, Nat.mul_zero, Nat.zero_add, Nat.zero_div, Nat.zero_mod, pow_zero,
        mul_one] at h
      exact h
  have hlast := SL m le_rfl
  rw [hOm, show 2 * m + sh = depth by omega] at hlast
  have hkmn : KModNext rd (ofK (addressOfIndex eK)) := by
    refine kModNext_of ?_
    have := hmT (eK, kmnWords) (by simp)
    simpa using this
  have hrel := vbg_body_of (rd := rd) (layers := ofK (addressOfIndex eL)) (rows := ofK (addressOfIndex eP)) (rounds := ofK (addressOfIndex eR)) (pairs := ofK (addressOfIndex ePa))
    (dsh := ofK (addressOfIndex eD)) hd1 hd hcl hrc hx0 hx1 hcnt hroot hkmn
    (hmT (ePa, (List.range 33).map fun k ↦ gen ^ (k / 2)) List.mem_cons_self)
    (hmT (eD, (List.range 33).map fun k ↦ gen ^ (k % 2)) (List.mem_cons_of_mem _ List.mem_cons_self))
    (fun h1 => ?_) (fun j hj => ?_) hlast (by rw [hr] at hz; exact hz)
  · obtain ⟨h1, h2⟩ := hrel
    rw [← hsF] at h1 h2
    rw [hr]
    exact ⟨h1, h2⟩
  · -- the binary layer
    obtain ⟨hok, hdr⟩ := hodd h1
    refine ⟨gkOdd xs, hok, ?_, ?_⟩
    · have h := hdrop 2 (by omega)
      rw [hdr, tbReadsAt_append] at h
      exact h.1
    · have hs1 : sh = 1 := h1
      have h0 : gkSl cap0 xs sh 0 = ((gkOdd xs).s' (gkRootS cap0 xs) (gkRootSt xs) 1,
          (gkOdd xs).st' (gkRootS cap0 xs) (gkRootSt xs) 1, 8) := by
        unfold gkSl gkSl0; simp [hs1]
      have h := SL 0 (by omega)
      rw [h0] at h
      simp only [hs1, gkPos, Nat.mul_zero, Nat.zero_add, Nat.zero_div, Nat.zero_mod, pow_one,
        pow_zero, Nat.mul_one] at h
      rw [show cur * gen ^ 8 = cur * gen ^ 2 * gen ^ 6 by rw [mul_assoc, ← pow_add]] at h
      exact h
  · -- the layers
    obtain ⟨hok, hdr⟩ := hsteps j hj
    have hO : (gkSl cap0 xs sh (j + 1)).2.2 = (gkSl cap0 xs sh j).2.2 + 4 * (2 * j + sh) + 12 :=
      rfl
    have hxl : (gkD cap0 xs sh j).xs.length = 4 * (2 * j + sh) + 12 := by
      rw [gkStepD_xs_length hok, hpl j (by omega)]; norm_num
    refine ⟨(gkSl cap0 xs sh j).1, cur * gen ^ (gkSl cap0 xs sh j).2.2, (gkSl cap0 xs sh j).2.1,
      ofK (addressOfIndex eP) * gen ^ (40 * (j + sh)), gen ^ gkPos sh j, gkD cap0 xs sh j, SL j
          (by omega),
      hok, ?_, ?_, ?_⟩
    · have h := hdrop _ (hOle j (by omega))
      rw [hdr, tbReadsAt_append] at h
      exact h.1
    · exact recsAt_of (fun q hq => hmC q (List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨j,
        List.mem_range.mpr hj, rfl⟩, hq⟩)) (hok.1.trans (hpl j (by omega)))
    · have h := SL (j + 1) (by omega)
      rw [gkSl_succ] at h
      rw [show 2 * j + sh + 2 = 2 * (j + 1) + sh by ring, hxl, mul_assoc, ← pow_add,
        show (gkSl cap0 xs sh j).2.2 + (4 * (2 * j + sh) + 12) =
          (gkSl cap0 xs sh j).2.2 + 4 * (2 * j + sh) + 12 by ring,
        mul_assoc (ofK (addressOfIndex eP)), ← pow_add, show 40 * (j + sh) + 40 = 40 * (j + 1 + sh)
            by ring,
        ← pow_add, show gkPos sh j + (2 * j + sh + 1) = gkPos sh (j + 1) by simp [gkPos]; ring]
      exact h

end
end LeanVM.Guest.B1.Tables
