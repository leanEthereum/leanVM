/-
  LeanVM.Guest.B1.Whir.CHonMemLv

  A level's memory, read from the honest buffers: what MidC, FinC and OsHonest read of it.
-/

module

public import LeanVM.Guest.B1.Whir.CHonMem
public import LeanVM.Guest.B1.Whir.LastRun

/-!
# A level's memory, honestly

On a memory holding the honest buffers at `b` (`OsMemF rd c b h.own`), the configuration's facts
`HonStatic c`, for level `l`:

* `mid_sent`, `mid_roots`, `mid_hs`, `mid_glue`: a non-final level's `MidC` memory fields at the
  pointers `osPtrF c b k` (`sent` at `13 + 2l`), `λ = (h.L l).lam h.logN`;
* `rows_mem`, `rows_lo`, `rows_hi`: the squeeze run's rows (`capSq`), at `osIxSqz c l`;
  `rowsMem_at`: OsHonest's form;
* `fin_hs`: the final level's lane in `final_msg` and normalized at `osIxHsF c`;
* `posMem_at`: the decoded positions in `query_positions`;
* `fch_load`, `coefs_load`, `roundsAt_of`, `allRounds_getD`: the fold challenges and the rounds'
  coefficients;
* `hsv_words`, `cap_loads`: the final lane and the query nodes' cap cells and flags.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

theorem getD_mapRange {n e : ℕ} (f : ℕ → E) (he : e < n) : ((List.range n).map f).getD e 0 = f e := by
  simp [List.getD_eq_getElem?_getD, he]

theorem getD_cons2 {a c : E} {l : List E} {j : ℕ} : (a :: c :: l).getD (2 + j) 0 = l.getD j 0 := by
  rw [show 2 + j = j + 1 + 1 by omega]; rfl

theorem capSq_succ (L : LvAt) (logN : ℕ) {j : ℕ} (hj : 1 ≤ j) :
    ((⟨L.capSq logN j, []⟩ : Fs).squeeze.2.cap) = L.capSq logN (j + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  simp only [LvAt.capSq, sqCap, Nat.add_sub_cancel]
  rw [← squeezeN_mk, squeezeN_snoc]

namespace OsHD

variable (h : OsHD) {rd : Reader} {b : ℕ}

/-! ## A non-final level -/

theorem mid_sent (hS : HonStatic h.c) (hm : OsMemF rd h.c b h.own) {l : ℕ} (hl : l < h.c.yrLevel)
    (hR : digestHalves (h.root (l + 1)) = ((h.L l).nw.x0, (h.L l).nw.x1)) :
    LoadHolds rd (osPtrF h.c b (13 + 2 * l)) 0 (h.L l).nw.x0 ∧
      LoadHolds rd (osPtrF h.c b (13 + 2 * l)) 1 (h.L l).nw.x1 ∧
      LoadHolds rd (osPtrF h.c b 3) (2 * l + 2) (h.L l).nw.x0 ∧
      LoadHolds rd (osPtrF h.c b 3) (2 * l + 3) (h.L l).nw.x1 := by
  have hyr := hS.yr
  have hl' : l < h.c.levels.length := by omega
  have hsz := hS.lv0 hl'
  have h3 := hS.head (j := 3) (by omega)
  simp only [show l ≠ h.c.yrLevel by omega, ↓reduceIte] at hsz
  have hw := h.ownW_lv0 hl'
  simp only [show l ≠ h.c.yrLevel by omega, ↓reduceIte] at hw
  have s0 := h.load hm (hS.lvLt hl').1 (by unfold osIxQbp; omega) (e := 0) (by rw [hsz]; omega)
  have s1 := h.load hm (hS.lvLt hl').1 (by unfold osIxQbp; omega) (e := 1) (by rw [hsz]; omega)
  have r0 := h.load hm (hS.headLt (j := 3) (by omega)) (by unfold osIxQbp; omega) (e := 2 * l + 2)
    (by rw [h3]; simp [headSizes]; omega)
  have r1 := h.load hm (hS.headLt (j := 3) (by omega)) (by unfold osIxQbp; omega) (e := 2 * l + 3)
    (by rw [h3]; simp [headSizes]; omega)
  rw [hw] at s0 s1
  rw [ownW_roots, rootsC, getD_mapRange _ (by omega)] at r0 r1
  simp only [sentC, List.getD_cons_zero, List.getD_cons_succ] at s0 s1
  have e2 : (2 * l + 2) / 2 = l + 1 := by omega
  have e3 : (2 * l + 3) / 2 = l + 1 := by omega
  simp only [show (2 * l + 2) % 2 = 0 by omega, show (2 * l + 3) % 2 = 1 by omega, e2, e3, ↓reduceIte,
    one_ne_zero, hR] at r0 r1
  exact ⟨s0, s1, r0, r1⟩

theorem mid_roots (hS : HonStatic h.c) (hm : OsMemF rd h.c b h.own) {l : ℕ} (hl : l < h.c.levels.length) :
    LoadHolds rd (osPtrF h.c b 3) (2 * l) (digestHalves (h.root l)).1 ∧
      LoadHolds rd (osPtrF h.c b 3) (2 * l + 1) (digestHalves (h.root l)).2 := by
  have h3 := hS.head (j := 3) (by omega)
  have r0 := h.load hm (hS.headLt (j := 3) (by omega)) (by unfold osIxQbp; omega) (e := 2 * l)
    (by rw [h3]; simp [headSizes]; omega)
  have r1 := h.load hm (hS.headLt (j := 3) (by omega)) (by unfold osIxQbp; omega) (e := 2 * l + 1)
    (by rw [h3]; simp [headSizes]; omega)
  rw [ownW_roots, rootsC, getD_mapRange _ (by omega)] at r0 r1
  simp only [show 2 * l % 2 = 0 by omega, show (2 * l + 1) % 2 = 1 by omega, show 2 * l / 2 = l by omega,
    show (2 * l + 1) / 2 = l by omega, ↓reduceIte, one_ne_zero] at r0 r1
  exact ⟨r0, r1⟩

theorem mid_hs (hS : HonStatic h.c) (hm : OsMemF rd h.c b h.own) {l : ℕ} (hl : l < h.c.yrLevel) {j : ℕ}
    (hj : j < (osLvAt h.c l).folds) :
    LoadHolds rd (osPtrF h.c b (13 + 2 * l)) (2 + j) ((h.L l).nw.high.getD j 0) ∧
      LoadHolds rd (osPtrF h.c b 8) (l * hsStride + j) ((h.L l).nw.high.getD j 0 *
        word (hsScale (osLvAt h.c l).vanish (osLvAt h.c l).highBits j
          (vanishInv ((osLvAt h.c l).vanish + (osLvAt h.c l).logCols))) 0) := by
  have hyr := hS.yr
  have hl' : l < h.c.levels.length := by omega
  have hj8 : j < 8 := lt_of_lt_of_le hj (hS.mid hl).2
  have hsz := hS.lv0 hl'
  have hny : l ≠ h.c.yrLevel := by omega
  simp only [hny, ↓reduceIte] at hsz
  have hw := h.ownW_lv0 hl'
  simp only [hny, ↓reduceIte] at hw
  have s := h.load hm (hS.lvLt hl').1 (by unfold osIxQbp; omega) (e := 2 + j) (by rw [hsz]; omega)
  rw [hw, sentC, getD_cons2] at s
  have h8 := hS.head (j := 8) (by omega)
  have hlt : l * 8 + j < h.c.levels.length * 8 := by
    have : (l + 1) * 8 ≤ h.c.levels.length * 8 := Nat.mul_le_mul_right _ (by omega)
    omega
  have t := h.load hm (hS.headLt (j := 8) (by omega)) (by unfold osIxQbp; omega) (e := l * 8 + j)
    (by rw [h8]; simp only [headSizes, List.getD_cons_succ, List.getD_cons_zero, hsStride]; exact hlt)
  have e1 : (l * 8 + j) / 8 = l := by omega
  have e2 : (l * 8 + j) % 8 = j := by omega
  rw [ownW_hs, hsC, getD_mapRange _ (by simpa only [hsStride] using hlt)] at t
  simp only [hsStride, e1, e2, hl, hj, and_self, ↓reduceIte] at t
  exact ⟨s, t⟩

theorem mid_glue (hS : HonStatic h.c) (hm : OsMemF rd h.c b h.own) {l : ℕ} (hl : l < h.c.yrLevel) :
    LoadHolds rd (osPtrF h.c b 10) (oodSamples * (l + 1)) ((h.L l).lam h.logN) ∧
      LoadHolds rd (osPtrF h.c b 10) (oodSamples * (l + 1) + 1) ((h.L l).lam h.logN * (h.L l).lam h.logN) ∧
      LoadHolds rd (osPtrF h.c b 6) l ((h.L l).lam h.logN * (h.L l).lam h.logN * (h.L l).lam h.logN *
        (h.L l).lam h.logN ^ (osLvAt h.c l).queries) ∧
      LoadHolds rd (osPtrF h.c b 7) l ((h.L l).lam h.logN)⁻¹ := by
  have hyr := hS.yr
  have h10 := hS.head (j := 10) (by omega)
  have h6 := hS.head (j := 6) (by omega)
  have h7 := hS.head (j := 7) (by omega)
  simp only [headSizes, List.getD_cons_succ, List.getD_cons_zero] at h10 h6 h7
  have a := h.load hm (hS.headLt (j := 10) (by omega)) (by unfold osIxQbp; omega) (e := oodSamples * (l + 1))
    (by rw [h10]; unfold oodSamples; omega)
  have a1 := h.load hm (hS.headLt (j := 10) (by omega)) (by unfold osIxQbp; omega)
    (e := oodSamples * (l + 1) + 1) (by rw [h10]; unfold oodSamples; omega)
  have bt := h.load hm (hS.headLt (j := 6) (by omega)) (by unfold osIxQbp; omega) (e := l) (by rw [h6]; omega)
  have mu := h.load hm (hS.headLt (j := 7) (by omega)) (by unfold osIxQbp; omega) (e := l) (by rw [h7]; omega)
  rw [ownW_ood, oodC, getD_mapRange _ (by unfold oodSamples; omega)] at a a1
  rw [ownW_betas, betasC, getD_mapRange _ (by omega)] at bt
  rw [ownW_mus, musC, getD_mapRange _ (by omega)] at mu
  unfold oodSamples at a a1 ⊢
  simp only [show 2 ≤ 2 * (l + 1) by omega, show 2 ≤ 2 * (l + 1) + 1 by omega,
    show 2 * (l + 1) / 2 - 1 = l by omega, show (2 * (l + 1) + 1) / 2 - 1 = l by omega, hl, and_self,
    ↓reduceIte, show 2 * (l + 1) % 2 = 0 by omega, show (2 * (l + 1) + 1) % 2 = 1 by omega,
    one_ne_zero] at a a1
  simp only [hl, ↓reduceIte, li] at bt mu
  refine ⟨a, by rw [← sq]; exact a1, by convert bt using 1; ring, mu⟩

/-! ## The squeeze runs -/

theorem rows_mem (hS : HonStatic h.c) (hm : OsMemF rd h.c b h.own) {l j i : ℕ} (hl : l < h.c.levels.length)
    (hj1 : 1 ≤ j) (hj : j ≤ (osLvAt h.c l).squeezes) (hi : i < 5) :
    LoadHolds rd (osPtrF h.c b (osIxSqz h.c l)) (5 * j + i) (((h.L l).capSq h.logN j).getD i 0) := by
  have hsq := (hS.sq hl).1
  have e1 : (5 * j + i) / 5 = j := by omega
  have e2 : (5 * j + i) % 5 = i := by omega
  have hlt : 5 * j + i < (h.c.maxSq + 1) * 5 := by
    have : j * 5 ≤ h.c.maxSq * 5 := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul]; omega
  by_cases hy : l = h.c.yrLevel
  · have hsz := hS.lv0 hl
    have hw := h.ownW_lv0 hl
    simp only [show (l = h.c.yrLevel) = True from eq_true hy, ↓reduceIte] at hsz hw
    have hx : osIxSqz h.c l = 13 + 2 * l := by simp [osIxSqz, hy]
    rw [hx]
    have s := h.load hm (hS.lvLt hl).1 (by unfold osIxQbp; omega) (e := 5 * j + i) (by rw [hsz]; exact hlt)
    rw [hw, sqzC, getD_mapRange _ hlt] at s
    simpa only [e1, e2, hj1, hj, and_self, ↓reduceIte] using s
  · have hsz := hS.lv1 hl
    have hw := h.ownW_lv1 hl
    simp only [hy, ↓reduceIte] at hsz hw
    have hx : osIxSqz h.c l = 14 + 2 * l := by simp [osIxSqz, hy]; omega
    rw [hx]
    have s := h.load hm (hS.lvLt hl).2 (by unfold osIxQbp; omega) (e := 5 * j + i) (by rw [hsz]; exact hlt)
    rw [hw, sqzC, getD_mapRange _ hlt] at s
    simpa only [e1, e2, hj1, hj, and_self, ↓reduceIte] using s

/-- MidC's and FinC's rows: the first squeeze's capacity at `5`, the last's at `squeezes · 5`. -/
theorem rows_lo_hi (hS : HonStatic h.c) (hm : OsMemF rd h.c b h.own) {l : ℕ} (hl : l < h.c.levels.length)
    (h1 : 1 ≤ (osLvAt h.c l).squeezes) :
    (∀ i < 5, LoadHolds rd (osPtrF h.c b (osIxSqz h.c l)) (5 + i) (((h.L l).capSq h.logN 1).getD i 0)) ∧
      ∀ i < 5, LoadHolds rd (osPtrF h.c b (osIxSqz h.c l)) ((osLvAt h.c l).squeezes * 5 + i)
        (((h.L l).capSq h.logN (osLvAt h.c l).squeezes).getD i 0) := by
  refine ⟨fun i hi ↦ ?_, fun i hi ↦ ?_⟩
  · have := h.rows_mem hS hm hl le_rfl h1 hi
    simpa using this
  · have := h.rows_mem hS hm hl h1 le_rfl hi
    rwa [Nat.mul_comm] at this

/-- OsHonest's `rowsMem` at level `l`. -/
theorem rowsMem_at (hS : HonStatic h.c) (hm : OsMemF rd h.c b h.own) {l : ℕ} (hl : l < h.c.levels.length)
    {j : ℕ} (hj1 : 1 ≤ j) (hj : j < (osLvAt h.c l).squeezes) :
    (∀ i < 5, LoadHolds rd (osPtrF h.c b (osIxSqz h.c l) * (gen ^ j) ^ 5) i (((h.L l).capSq h.logN j).getD i 0)) ∧
      ∀ i < 5, LoadHolds rd (osPtrF h.c b (osIxSqz h.c l) * (gen ^ j) ^ 5) (5 + i)
        (((⟨(h.L l).capSq h.logN j, []⟩ : Fs).squeeze.2.cap).getD i 0) := by
  rw [← pow_mul]
  refine ⟨fun i hi ↦ ?_, fun i hi ↦ ?_⟩
  · rw [loadHolds_mul_gen_pow, show j * 5 + i = 5 * j + i by ring]
    exact h.rows_mem hS hm hl hj1 hj.le hi
  · rw [loadHolds_mul_gen_pow, capSq_succ _ _ hj1, show j * 5 + (5 + i) = 5 * (j + 1) + i by ring]
    exact h.rows_mem hS hm hl (by omega) hj hi

/-! ## The final level -/

theorem fin_hs (hS : HonStatic h.c) (hm : OsMemF rd h.c b h.own) {j : ℕ}
    (hj : j < h.c.yrLen + (osLvAt h.c h.c.yrLevel).folds) :
    LoadHolds rd (osPtrF h.c b 2) j (h.Lf.fw.fold.getD j 0) ∧
      LoadHolds rd (osPtrF h.c b (osIxHsF h.c)) j (h.Lf.fw.fold.getD j 0 *
        word (hsScale (osLvAt h.c h.c.yrLevel).vanish (h.c.yrLog + 1) j 1) 0) := by
  have hyr := hS.yr
  have hl : h.c.yrLevel < h.c.levels.length := by omega
  have h2 := hS.head (j := 2) (by omega)
  simp only [headSizes, List.getD_cons_succ, List.getD_cons_zero] at h2
  have a := h.load hm (hS.headLt (j := 2) (by omega)) (by unfold osIxQbp; omega) (e := j) (by rw [h2]; exact hj)
  rw [ownW_fmsg, fmsgC] at a
  have hsz := hS.lv1 hl
  have hw := h.ownW_lv1 hl
  simp only [↓reduceIte] at hsz hw
  have hx : osIxHsF h.c = 14 + 2 * h.c.yrLevel := rfl
  rw [hx]
  have t := h.load hm (hS.lvLt hl).2 (by unfold osIxQbp; omega) (e := j) (by rw [hsz]; exact hj)
  rw [hw, hsFC, getD_mapRange _ hj] at t
  exact ⟨a, t⟩

/-- The final level's normalized lane, as `opening_queries` reads it. -/
theorem hsv_words (hS : HonStatic h.c) (hm : OsMemF rd h.c b h.own) :
    WordsAt rd (osHsPtr h.c b h.c.yrLevel) h.hsFC := by
  intro j hj
  have hj' : j < h.c.yrLen + (osLvAt h.c h.c.yrLevel).folds := by simpa [hsFC] using hj
  simp only [osHsPtr, ↓reduceIte, hsFC, getD_mapRange _ hj']
  exact (h.fin_hs hS hm hj').2

/-! ## The positions -/

theorem qpos_seg (hS : HonStatic h.c) {l k : ℕ} (hl : l < h.c.levels.length)
    (hk : k < (osLvAt h.c l).squeezes * sqPer (osLvAt h.c l)) :
    h.qposC.getD ((osLvAt h.c l).posOff + k) 0 =
      eOfNat (qwPosOf (osLvAt h.c l).depth ((h.L l).word h.logN (k / sqPer (osLvAt h.c l)))
        (k % sqPer (osLvAt h.c l))) := by
  obtain ⟨hd, htop⟩ := chain_disj hS.pos
  have := htop l hl
  rw [qposC, getD_mapRange _ (by omega)]
  exact segAt_at hd hl hk

/-- A level's position `k` in `query_positions`. -/
theorem pos_load (hS : HonStatic h.c) (hm : OsMemF rd h.c b h.own) {l k : ℕ} (hl : l < h.c.levels.length)
    (hk : k < (osLvAt h.c l).squeezes * sqPer (osLvAt h.c l)) :
    LoadHolds rd (osPtrF h.c b 11) ((osLvAt h.c l).posOff + k)
      (eOfNat (qwPosOf (osLvAt h.c l).depth ((h.L l).word h.logN (k / sqPer (osLvAt h.c l)))
        (k % sqPer (osLvAt h.c l)))) := by
  obtain ⟨-, htop⟩ := chain_disj hS.pos
  have := htop l hl
  have h11 := hS.head (j := 11) (by omega)
  simp only [headSizes, List.getD_cons_succ, List.getD_cons_zero] at h11
  have a := h.load hm (hS.headLt (j := 11) (by omega)) (by unfold osIxQbp; omega)
    (e := (osLvAt h.c l).posOff + k) (by rw [h11]; omega)
  rwa [ownW_qpos, h.qpos_seg hS hl hk] at a

/-- OsHonest's `posMem` at level `l`. -/
theorem posMem_at (hS : HonStatic h.c) (hm : OsMemF rd h.c b h.own) {l : ℕ} (hl : l < h.c.levels.length)
    {j : ℕ} (hj : j < (osLvAt h.c l).squeezes) {i : ℕ} (hi : i < sqPer (osLvAt h.c l)) :
    LoadHolds rd (osPtrF h.c b 11 * gen ^ (osLvAt h.c l).posOff * (gen ^ j) ^ sqPer (osLvAt h.c l)) i
      (eOfNat (qwPosOf (osLvAt h.c l).depth ((h.L l).word h.logN j) i)) := by
  rw [mul_assoc, ← pow_mul, ← pow_add, loadHolds_mul_gen_pow, Nat.add_assoc]
  have hk : j * sqPer (osLvAt h.c l) + i < (osLvAt h.c l).squeezes * sqPer (osLvAt h.c l) := by
    have : (j + 1) * sqPer (osLvAt h.c l) ≤ (osLvAt h.c l).squeezes * sqPer (osLvAt h.c l) :=
      Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul] at this; omega
  have := h.pos_load hS hm hl hk
  have e1 : (j * sqPer (osLvAt h.c l) + i) / sqPer (osLvAt h.c l) = j := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hi, Nat.zero_add]
  have e2 : (j * sqPer (osLvAt h.c l) + i) % sqPer (osLvAt h.c l) = i := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]
  rwa [e1, e2] at this

/-! ## The fold challenges and the rounds -/

theorem fch_load (hS : HonStatic h.c) (hm : OsMemF rd h.c b h.own) {i : ℕ} (hi : i < h.c.nFolds) :
    LoadHolds rd (osPtrF h.c b 4) i (h.G.getD i 0) := by
  have h4 := hS.head (j := 4) (by omega)
  simp only [headSizes, List.getD_cons_succ, List.getD_cons_zero] at h4
  have a := h.load hm (hS.headLt (j := 4) (by omega)) (by unfold osIxQbp; omega) (e := i) (by rw [h4]; exact hi)
  rwa [ownW_fch, fchC] at a

theorem coefs_load (hS : HonStatic h.c) (hm : OsMemF rd h.c b h.own) {i : ℕ} (hi : i < h.c.nFolds) :
    LoadHolds rd (osPtrF h.c b 5) (3 * i) (h.allRounds.getD i ⟨0, 0, 0⟩).alpha ∧
      LoadHolds rd (osPtrF h.c b 5) (3 * i + 1) (h.allRounds.getD i ⟨0, 0, 0⟩).beta ∧
      LoadHolds rd (osPtrF h.c b 5) (3 * i + 2) (h.allRounds.getD i ⟨0, 0, 0⟩).theta := by
  have h5 := hS.head (j := 5) (by omega)
  simp only [headSizes, List.getD_cons_succ, List.getD_cons_zero] at h5
  have a t := h.load hm (hS.headLt (j := 5) (by omega)) (by unfold osIxQbp; omega) (e := 3 * i + t)
  have a0 := a 0 (by rw [h5]; omega)
  have a1 := a 1 (by rw [h5]; omega)
  have a2 := a 2 (by rw [h5]; omega)
  rw [ownW_coefs, coefsC, getD_mapRange _ (by omega)] at a0 a1 a2
  have d0 : (3 * i + 0) / 3 = i := by omega
  have d1 : (3 * i + 1) / 3 = i := by omega
  have d2 : (3 * i + 2) / 3 = i := by omega
  have m0 : (3 * i + 0) % 3 = 0 := by omega
  have m1 : (3 * i + 1) % 3 = 1 := by omega
  have m2 : (3 * i + 2) % 3 = 2 := by omega
  simp only [d0, d1, d2, m0, m1, m2, ↓reduceIte, one_ne_zero, show (2 : ℕ) ≠ 0 by omega,
    show (2 : ℕ) ≠ 1 by omega] at a0 a1 a2
  exact ⟨a0, a1, a2⟩

/-- A flattened list read at a level's offset. -/
theorem flatMap_getD {α β : Type} (f : α → List β) (d : β) [Inhabited α] :
    ∀ (L : List α) (l j : ℕ), l < L.length → j < (f (L.getD l default)).length →
      (L.flatMap f).getD (((L.take l).map fun a ↦ (f a).length).sum + j) d = (f (L.getD l default)).getD j d
  | [], _, _, hl, _ => absurd hl (by simp)
  | a :: L, 0, j, _, hj => by
    simp only [List.getD_cons_zero] at hj ⊢
    simp only [List.take_zero, List.map_nil, List.sum_nil, Nat.zero_add, List.flatMap_cons,
      List.getD_eq_getElem?_getD, List.getElem?_append_left hj]
  | a :: L, l + 1, j, hl, hj => by
    simp only [List.getD_cons_succ] at hj ⊢
    have ih := flatMap_getD f d L l j (by simp at hl; omega) hj
    simp only [List.flatMap_cons, List.take_succ_cons, List.map_cons, List.sum_cons]
    rw [List.getD_append_right _ _ _ _ (by omega), show (f a).length + (List.map (fun a ↦ (f a).length)
      (List.take l L)).sum + j - (f a).length = (List.map (fun a ↦ (f a).length) (List.take l L)).sum + j by
      omega]
    exact ih

/-- **A level's rounds within every level's**, the rounds counted by the rows. -/
theorem allRounds_getD (hS : HonStatic h.c) (hL : h.Ls.length = h.c.levels.length)
    (hrl : ∀ i < h.c.levels.length, (h.L i).rounds.length = (osLvAt h.c i).folds)
    {l j : ℕ} (hl : l < h.c.levels.length) (hj : j < (osLvAt h.c l).folds) :
    h.allRounds.getD ((osLvAt h.c l).foldsOff + j) ⟨0, 0, 0⟩ = (h.L l).rounds.getD j ⟨0, 0, 0⟩ := by
  have hoff : ∀ l ≤ h.c.levels.length, ((h.Ls.take l).map fun a ↦ a.rounds.length).sum =
      if l = 0 then 0 else (osLvAt h.c (l - 1)).foldsOff + (osLvAt h.c (l - 1)).folds := by
    intro l
    induction l with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      have hm' : m < h.Ls.length := by omega
      rw [List.take_add_one, List.map_append, List.sum_append, ih (by omega), List.getElem?_eq_getElem hm']
      simp only [Option.toList_some, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
        Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      have hr : h.Ls[m].rounds.length = (osLvAt h.c m).folds := by
        have := hrl m (by omega)
        simpa only [OsHD.L, List.getD_eq_getElem _ _ hm'] using this
      rw [hr]
      rcases m with _ | m
      · simpa using hS.fo0
      · simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
        rw [hS.fo (l := m) (by omega)]
  have hl' : ((h.Ls.take l).map fun a ↦ a.rounds.length).sum = (osLvAt h.c l).foldsOff := by
    rw [hoff l hl.le]
    rcases l with _ | l
    · simpa using hS.fo0.symm
    · simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      rw [hS.fo (l := l) hl]
  have := flatMap_getD (fun a : LvAt ↦ a.rounds) ⟨0, 0, 0⟩ h.Ls l j (by omega)
    (by rw [hrl l hl]; exact hj)
  rw [hl'] at this
  exact this

/-- OsHonest's `RoundsAt` of level `l`'s rounds at its coefficients. -/
theorem roundsAt_of (hS : HonStatic h.c) (hm : OsMemF rd h.c b h.own) (hL : h.Ls.length = h.c.levels.length)
    (hrl : ∀ i < h.c.levels.length, (h.L i).rounds.length = (osLvAt h.c i).folds) {l : ℕ}
    (hl : l < h.c.levels.length) :
    RoundsAt rd (osPtrF h.c b 5 * gen ^ (3 * (osLvAt h.c l).foldsOff)) (h.L l).rounds := by
  intro j hj
  rw [hrl l hl] at hj
  have hT : (osLvAt h.c l).foldsOff + (osLvAt h.c l).folds ≤ h.c.nFolds := by
    have hyr := hS.yr
    have key : ∀ d, l + d ≤ h.c.yrLevel →
        (osLvAt h.c l).foldsOff + (osLvAt h.c l).folds ≤
          (osLvAt h.c (l + d)).foldsOff + (osLvAt h.c (l + d)).folds := by
      intro d
      induction d with
      | zero => intro _; exact le_rfl
      | succ d ih =>
        intro hd
        have := ih (by omega)
        rw [show l + (d + 1) = l + d + 1 by omega, hS.fo (l := l + d) (by omega)]
        omega
    have := key (h.c.yrLevel - l) (by omega)
    rw [show l + (h.c.yrLevel - l) = h.c.yrLevel by omega, hS.foT] at this
    exact this
  obtain ⟨a0, a1, a2⟩ := h.coefs_load hS hm (i := (osLvAt h.c l).foldsOff + j) (by omega)
  rw [h.allRounds_getD hS hL hrl hl hj] at a0 a1 a2
  refine ⟨?_, ?_, ?_⟩ <;> rw [loadHolds_mul_gen_pow]
  · rw [show 3 * (osLvAt h.c l).foldsOff + 3 * j = 3 * ((osLvAt h.c l).foldsOff + j) by ring]; exact a0
  · rw [show 3 * (osLvAt h.c l).foldsOff + (3 * j + 1) = 3 * ((osLvAt h.c l).foldsOff + j) + 1 by ring]
    exact a1
  · rw [show 3 * (osLvAt h.c l).foldsOff + (3 * j + 2) = 3 * ((osLvAt h.c l).foldsOff + j) + 2 by ring]
    exact a2

/-! ## The caps -/

/-- Level `l`'s cap cells and flags at the query nodes, from their values there. -/
theorem cap_loads (hS : HonStatic h.c) (hm : OsMemF rd h.c b h.own) {l : ℕ} (hl : l < h.c.levels.length)
    {pd cd q : ℕ} (hcd : cd = (osLvAt h.c l).capDepth) (hcd1 : 1 ≤ cd) (hq : q < 2 ^ (pd + cd))
    {d0 d1 : E} (hv0 : h.cv l (2 * (2 ^ cd + q / 2 ^ pd)) = d0)
    (hv1 : h.cv l (2 * (2 ^ cd + q / 2 ^ pd) + 1) = d1) (hf : h.fv l (2 ^ (cd - 1) + q / 2 ^ (pd + 1)) = 1) :
    LoadHolds rd (osPtrF h.c b 0 * gen ^ (4 * (osLvAt h.c l).capOff)) (2 * (2 ^ cd + q / 2 ^ pd)) d0 ∧
      LoadHolds rd (osPtrF h.c b 0 * gen ^ (4 * (osLvAt h.c l).capOff)) (2 * (2 ^ cd + q / 2 ^ pd) + 1) d1 ∧
      LoadHolds rd (osPtrF h.c b 1 * gen ^ (osLvAt h.c l).capOff) (2 ^ (cd - 1) + q / 2 ^ (pd + 1)) 1 := by
  have hqd : q / 2 ^ pd < 2 ^ cd := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.add_comm]; exact hq
  have hqd1 : q / 2 ^ (pd + 1) < 2 ^ (cd - 1) := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
    rw [show cd - 1 + (pd + 1) = pd + cd by omega]; exact hq
  have hc1 : 2 ^ (cd - 1) * 2 = 2 ^ cd := by rw [← pow_succ, Nat.sub_add_cancel hcd1]
  have hk1 : 2 * (2 ^ cd + q / 2 ^ pd) < 2 ^ (cd + 2) := by rw [pow_add]; omega
  have hk0 : 2 * (2 ^ cd + q / 2 ^ pd) + 1 < 2 ^ (cd + 2) := by rw [pow_add]; omega
  have hf0 : 2 ^ (cd - 1) + q / 2 ^ (pd + 1) < 2 ^ cd := by omega
  obtain ⟨hdc, htc⟩ := chain_disj hS.caps
  obtain ⟨hdf, htf⟩ := chain_disj hS.flags
  have tc := htc l hl
  have tf := htf l hl
  rw [← hcd] at tc tf
  have h0 := hS.head (j := 0) (by omega)
  have h1 := hS.head (j := 1) (by omega)
  simp only [headSizes, List.getD_cons_succ, List.getD_cons_zero] at h0 h1
  have a0 := h.loadOff hm (hS.headLt (j := 0) (by omega)) (by unfold osIxQbp; omega)
    (o := 4 * (osLvAt h.c l).capOff) (e := 2 * (2 ^ cd + q / 2 ^ pd)) (by rw [h0]; omega)
  have a1 := h.loadOff hm (hS.headLt (j := 0) (by omega)) (by unfold osIxQbp; omega)
    (o := 4 * (osLvAt h.c l).capOff) (e := 2 * (2 ^ cd + q / 2 ^ pd) + 1) (by rw [h0]; omega)
  have fl := h.loadOff hm (hS.headLt (j := 1) (by omega)) (by unfold osIxQbp; omega)
    (o := (osLvAt h.c l).capOff) (e := 2 ^ (cd - 1) + q / 2 ^ (pd + 1)) (by rw [h1]; omega)
  rw [ownW_caps, capsC, getD_mapRange _ (by omega),
    segAt_at (val := h.cv) hdc hl (by show _ < 2 ^ ((osLvAt h.c l).capDepth + 2); rw [← hcd]; exact hk1)] at a0
  rw [ownW_caps, capsC, getD_mapRange _ (by omega),
    segAt_at (val := h.cv) hdc hl (by show _ < 2 ^ ((osLvAt h.c l).capDepth + 2); rw [← hcd]; exact hk0)] at a1
  rw [ownW_flags, flagsC, getD_mapRange _ (by omega),
    segAt_at (val := h.fv) hdf hl (by show _ < 2 ^ (osLvAt h.c l).capDepth; rw [← hcd]; exact hf0)] at fl
  rw [hv0] at a0
  rw [hv1] at a1
  rw [hf] at fl
  exact ⟨a0, a1, fl⟩

end OsHD

end
end LeanVM.Guest.B1.Whir
