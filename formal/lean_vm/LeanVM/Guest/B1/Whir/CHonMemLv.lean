/-
  LeanVM.Guest.B1.Whir.CHonMemLv

  A level's memory, read from the honest buffers: what MidC, FinC and OsHonest read of it.
-/

module

public import LeanVM.Guest.B1.Whir.CHonMem
public import LeanVM.Guest.B1.Whir.LastRun

/-!
# A level's memory, honestly

On a memory holding the honest buffers at `b` (`OsMemA rd c b h.own`), the configuration's facts
`HonStatic c`, for level `l`:

* `mid_sent`, `mid_roots`, `mid_hs`, `mid_glue`: a non-final level's `MidC` memory fields at the
  pointers `osPtrA c b k` (`sent` at `13 + 2l`), `λ = (h.L l).lam h.logN`;
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

namespace OsHD

variable (h : OsHD) {rd : Reader} {b : ℕ}

/-! ## A non-final level -/

theorem mid_sent (hS : HonStatic h.c) (hm : OsMemA rd h.c b h.own) {l : ℕ} (hl : l < h.c.yrLevel)
    (hR : digestHalves (h.root (l + 1)) = ((h.L l).nw.x0, (h.L l).nw.x1)) :
    LoadHolds rd (osPtrA h.c b (11 + l)) 0 (h.L l).nw.x0 ∧
      LoadHolds rd (osPtrA h.c b (11 + l)) 1 (h.L l).nw.x1 ∧
      LoadHolds rd (osPtrA h.c b 1) (2 * l + 2) (h.L l).nw.x0 ∧
      LoadHolds rd (osPtrA h.c b 1) (2 * l + 3) (h.L l).nw.x1 := by
  have hyr := hS.yr
  have hl' : l < h.c.levels.length := by omega
  have hsz := hS.sent hl
  have h3 := hS.head (j := 1) (by omega)
  have hw := h.ownW_sent hl
  have s0 := h.load hm (hS.sentLt (le_of_lt hl)) (by unfold osIxQbpA; omega) (e := 0) (by rw [hsz]; omega)
  have s1 := h.load hm (hS.sentLt (le_of_lt hl)) (by unfold osIxQbpA; omega) (e := 1) (by rw [hsz]; omega)
  have r0 := h.load hm (hS.headLt (j := 1) (by omega)) (by unfold osIxQbpA; omega) (e := 2 * l + 2)
    (by rw [h3]; simp [headSizes]; omega)
  have r1 := h.load hm (hS.headLt (j := 1) (by omega)) (by unfold osIxQbpA; omega) (e := 2 * l + 3)
    (by rw [h3]; simp [headSizes]; omega)
  rw [hw] at s0 s1
  rw [ownW_roots, rootsC, getD_mapRange _ (by omega)] at r0 r1
  simp only [sentC, List.getD_cons_zero, List.getD_cons_succ] at s0 s1
  have e2 : (2 * l + 2) / 2 = l + 1 := by omega
  have e3 : (2 * l + 3) / 2 = l + 1 := by omega
  simp only [show (2 * l + 2) % 2 = 0 by omega, show (2 * l + 3) % 2 = 1 by omega, e2, e3, ↓reduceIte,
    one_ne_zero, hR] at r0 r1
  exact ⟨s0, s1, r0, r1⟩

theorem mid_roots (hS : HonStatic h.c) (hm : OsMemA rd h.c b h.own) {l : ℕ} (hl : l < h.c.levels.length) :
    LoadHolds rd (osPtrA h.c b 1) (2 * l) (digestHalves (h.root l)).1 ∧
      LoadHolds rd (osPtrA h.c b 1) (2 * l + 1) (digestHalves (h.root l)).2 := by
  have h3 := hS.head (j := 1) (by omega)
  have r0 := h.load hm (hS.headLt (j := 1) (by omega)) (by unfold osIxQbpA; omega) (e := 2 * l)
    (by rw [h3]; simp [headSizes]; omega)
  have r1 := h.load hm (hS.headLt (j := 1) (by omega)) (by unfold osIxQbpA; omega) (e := 2 * l + 1)
    (by rw [h3]; simp [headSizes]; omega)
  rw [ownW_roots, rootsC, getD_mapRange _ (by omega)] at r0 r1
  simp only [show 2 * l % 2 = 0 by omega, show (2 * l + 1) % 2 = 1 by omega, show 2 * l / 2 = l by omega,
    show (2 * l + 1) / 2 = l by omega, ↓reduceIte, one_ne_zero] at r0 r1
  exact ⟨r0, r1⟩

theorem mid_hs (hS : HonStatic h.c) (hm : OsMemA rd h.c b h.own) {l : ℕ} (hl : l < h.c.yrLevel) {j : ℕ}
    (hj : j < ((h.c.levels.getD l default)).folds) :
    LoadHolds rd (osPtrA h.c b (11 + l)) (2 + j) ((h.L l).nw.high.getD j 0) ∧
      LoadHolds rd (osPtrA h.c b 6) (l * hsStride + j) ((h.L l).nw.high.getD j 0 *
        word (hsScale ((h.c.levels.getD l default)).vanish ((h.c.levels.getD l default)).highBits j
          (vanishInv (((h.c.levels.getD l default)).vanish + ((h.c.levels.getD l default)).logCols))) 0) := by
  have hyr := hS.yr
  have hl' : l < h.c.levels.length := by omega
  have hj8 : j < 8 := lt_of_lt_of_le hj (hS.mid hl).2
  have hsz := hS.sent hl
  have hny : l ≠ h.c.yrLevel := by omega
  have hw := h.ownW_sent hl
  have s := h.load hm (hS.sentLt (le_of_lt hl)) (by unfold osIxQbpA; omega) (e := 2 + j) (by rw [hsz]; omega)
  rw [hw, sentC, getD_cons2] at s
  have h8 := hS.head (j := 6) (by omega)
  have hlt : l * 8 + j < h.c.levels.length * 8 := by
    have : (l + 1) * 8 ≤ h.c.levels.length * 8 := Nat.mul_le_mul_right _ (by omega)
    omega
  have t := h.load hm (hS.headLt (j := 6) (by omega)) (by unfold osIxQbpA; omega) (e := l * 8 + j)
    (by rw [h8]; simp only [headSizes, List.getD_cons_succ, List.getD_cons_zero, hsStride]; exact hlt)
  have e1 : (l * 8 + j) / 8 = l := by omega
  have e2 : (l * 8 + j) % 8 = j := by omega
  rw [ownW_hs, hsC, getD_mapRange _ (by simpa only [hsStride] using hlt)] at t
  simp only [hsStride, e1, e2, hl, hj, and_self, ↓reduceIte] at t
  exact ⟨s, t⟩

theorem mid_glue (hS : HonStatic h.c) (hm : OsMemA rd h.c b h.own) {l : ℕ} (hl : l < h.c.yrLevel) :
    LoadHolds rd (osPtrA h.c b 8) (l + 1) ((h.L l).lam h.logN) ∧
      LoadHolds rd (osPtrA h.c b 4) l ((h.L l).lam h.logN * (h.L l).lam h.logN *
        (h.L l).lam h.logN ^ ((h.c.levels.getD l default)).queries) ∧
      LoadHolds rd (osPtrA h.c b 5) l ((h.L l).lam h.logN)⁻¹ := by
  have hyr := hS.yr
  have h10 := hS.head (j := 8) (by omega)
  have h6 := hS.head (j := 4) (by omega)
  have h7 := hS.head (j := 5) (by omega)
  simp only [headSizes, List.getD_cons_succ, List.getD_cons_zero] at h10 h6 h7
  have a := h.load hm (hS.headLt (j := 8) (by omega)) (by unfold osIxQbpA; omega) (e := l + 1)
    (by rw [h10]; omega)
  have bt := h.load hm (hS.headLt (j := 4) (by omega)) (by unfold osIxQbpA; omega) (e := l) (by rw [h6]; omega)
  have mu := h.load hm (hS.headLt (j := 5) (by omega)) (by unfold osIxQbpA; omega) (e := l) (by rw [h7]; omega)
  rw [ownW_ood, oodC, getD_mapRange _ (by omega)] at a
  rw [ownW_betas, betasC, getD_mapRange _ (by omega)] at bt
  rw [ownW_mus, musC, getD_mapRange _ (by omega)] at mu
  simp only [show 1 ≤ l + 1 by omega, Nat.add_sub_cancel, hl, and_self, ↓reduceIte] at a
  simp only [hl, ↓reduceIte, li] at bt mu
  refine ⟨a, by convert bt using 1; ring, mu⟩

/-! ## The final level -/

theorem fin_hs (hS : HonStatic h.c) (hm : OsMemA rd h.c b h.own) {j : ℕ}
    (hj : j < h.c.yrLen + ((h.c.levels.getD h.c.yrLevel default)).folds) :
    LoadHolds rd (osPtrA h.c b 0) j (h.Lf.fw.fold.getD j 0) ∧
      LoadHolds rd (osPtrA h.c b (osIxLaneA h.c)) j (h.Lf.fw.fold.getD j 0 *
        word (hsScale ((h.c.levels.getD h.c.yrLevel default)).vanish (h.c.yrLog + 1) j 1) 0) := by
  have hyr := hS.yr
  have hl : h.c.yrLevel < h.c.levels.length := by omega
  have h2 := hS.head (j := 0) (by omega)
  simp only [headSizes, List.getD_cons_zero] at h2
  have a := h.load hm (hS.headLt (j := 0) (by omega)) (by unfold osIxQbpA; omega) (e := j) (by rw [h2]; exact hj)
  rw [ownW_fmsg, fmsgC] at a
  have hsz := hS.lane
  have hw := h.ownW_lane
  have hx : osIxLaneA h.c = 11 + h.c.yrLevel := rfl
  rw [hx]
  have t := h.load hm (hS.sentLt le_rfl) (by unfold osIxQbpA; omega) (e := j) (by rw [hsz]; exact hj)
  rw [hw, hsFC, getD_mapRange _ hj] at t
  exact ⟨a, t⟩

/-- The final level's normalized lane, as `opening_queries` reads it. -/
theorem hsv_words (hS : HonStatic h.c) (hm : OsMemA rd h.c b h.own) :
    WordsAt rd (osHsPtrA h.c b h.c.yrLevel) h.hsFC := by
  intro j hj
  have hj' : j < h.c.yrLen + ((h.c.levels.getD h.c.yrLevel default)).folds := by simpa [hsFC] using hj
  simp only [osHsPtrA, ↓reduceIte, hsFC, getD_mapRange _ hj']
  exact (h.fin_hs hS hm hj').2

/-! ## The positions -/

theorem qpos_seg (hS : HonStatic h.c) {l k : ℕ} (hl : l < h.c.levels.length)
    (hk : k < ((h.c.levels.getD l default)).squeezes * sqPer ((h.c.levels.getD l default))) :
    h.qposC.getD (((h.c.levels.getD l default)).posOff + k) 0 =
      eOfNat (qwPosOf ((h.c.levels.getD l default)).depth ((h.L l).word h.logN (k / sqPer ((h.c.levels.getD l default))))
        (k % sqPer ((h.c.levels.getD l default)))) := by
  obtain ⟨hd, htop⟩ := chain_disj hS.pos
  have := htop l hl
  rw [qposC, getD_mapRange _ (by omega)]
  exact segAt_at hd hl hk

/-- A level's position `k` in `query_positions`. -/
theorem pos_load (hS : HonStatic h.c) (hm : OsMemA rd h.c b h.own) {l k : ℕ} (hl : l < h.c.levels.length)
    (hk : k < ((h.c.levels.getD l default)).squeezes * sqPer ((h.c.levels.getD l default))) :
    LoadHolds rd (osPtrA h.c b 9) (((h.c.levels.getD l default)).posOff + k)
      (eOfNat (qwPosOf ((h.c.levels.getD l default)).depth ((h.L l).word h.logN (k / sqPer ((h.c.levels.getD l default))))
        (k % sqPer ((h.c.levels.getD l default))))) := by
  obtain ⟨-, htop⟩ := chain_disj hS.pos
  have := htop l hl
  have h11 := hS.head (j := 9) (by omega)
  simp only [headSizes, List.getD_cons_succ, List.getD_cons_zero] at h11
  have a := h.load hm (hS.headLt (j := 9) (by omega)) (by unfold osIxQbpA; omega)
    (e := ((h.c.levels.getD l default)).posOff + k) (by rw [h11]; omega)
  rwa [ownW_qpos, h.qpos_seg hS hl hk] at a

/-- **A level's stored position**, squeeze `j`'s window `i`. -/
theorem posW_at (hS : HonStatic h.c) {l j i : ℕ} (hl : l < h.c.levels.length)
    (hj : j < (h.c.levels.getD l default).squeezes) (hi : i < sqPer (h.c.levels.getD l default)) :
    (osOwnA h.own osIxQposA).getD ((h.c.levels.getD l default).posOff + j * sqPer (h.c.levels.getD l default) + i) 0 =
      eOfNat (qwPosOf (h.c.levels.getD l default).depth ((h.L l).word h.logN j) i) := by
  have hk : j * sqPer (h.c.levels.getD l default) + i <
      (h.c.levels.getD l default).squeezes * sqPer (h.c.levels.getD l default) := by
    have : (j + 1) * sqPer (h.c.levels.getD l default) ≤
        (h.c.levels.getD l default).squeezes * sqPer (h.c.levels.getD l default) :=
      Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul, Nat.one_mul] at this
    omega
  obtain ⟨-, htop⟩ := chain_disj hS.pos
  have htl := htop l hl
  have h9 := hS.head (j := 9) (by omega)
  show (h.own.getD 9 []).getD _ 0 = _
  rw [h.own_getD (hS.headLt (j := 9) (by omega)), ownAt, fitTo_getD (by rw [h9]; show _ < h.c.levels.length * ligPosCap; omega),
    ownW_qpos, Nat.add_assoc, h.qpos_seg hS hl hk]
  have hP : 0 < sqPer (h.c.levels.getD l default) := by omega
  rw [Nat.add_comm (j * _) i, Nat.add_mul_div_right _ _ hP, Nat.div_eq_of_lt hi, Nat.zero_add,
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]

/-- OsHonest's `posMem` at level `l`. -/
theorem posMem_at (hS : HonStatic h.c) (hm : OsMemA rd h.c b h.own) {l : ℕ} (hl : l < h.c.levels.length)
    {j : ℕ} (hj : j < ((h.c.levels.getD l default)).squeezes) {i : ℕ} (hi : i < sqPer ((h.c.levels.getD l default))) :
    LoadHolds rd (osPtrA h.c b 9 * gen ^ ((h.c.levels.getD l default)).posOff * (gen ^ j) ^ sqPer ((h.c.levels.getD l default))) i
      (eOfNat (qwPosOf ((h.c.levels.getD l default)).depth ((h.L l).word h.logN j) i)) := by
  rw [mul_assoc, ← pow_mul, ← pow_add, loadHolds_mul_gen_pow, Nat.add_assoc]
  have hk : j * sqPer ((h.c.levels.getD l default)) + i < ((h.c.levels.getD l default)).squeezes * sqPer ((h.c.levels.getD l default)) := by
    have : (j + 1) * sqPer ((h.c.levels.getD l default)) ≤ ((h.c.levels.getD l default)).squeezes * sqPer ((h.c.levels.getD l default)) :=
      Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul] at this; omega
  have := h.pos_load hS hm hl hk
  have e1 : (j * sqPer ((h.c.levels.getD l default)) + i) / sqPer ((h.c.levels.getD l default)) = j := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hi, Nat.zero_add]
  have e2 : (j * sqPer ((h.c.levels.getD l default)) + i) % sqPer ((h.c.levels.getD l default)) = i := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]
  rwa [e1, e2] at this

/-! ## The fold challenges and the rounds -/

theorem fch_load (hS : HonStatic h.c) (hm : OsMemA rd h.c b h.own) {i : ℕ} (hi : i < h.c.nFolds) :
    LoadHolds rd (osPtrA h.c b 2) i (h.G.getD i 0) := by
  have h4 := hS.head (j := 2) (by omega)
  simp only [headSizes, List.getD_cons_succ, List.getD_cons_zero] at h4
  have a := h.load hm (hS.headLt (j := 2) (by omega)) (by unfold osIxQbpA; omega) (e := i) (by rw [h4]; exact hi)
  rwa [ownW_fch, fchC] at a

theorem coefs_load (hS : HonStatic h.c) (hm : OsMemA rd h.c b h.own) {i : ℕ} (hi : i < h.c.nFolds) :
    LoadHolds rd (osPtrA h.c b 3) (2 * i) (h.allRounds.getD i ⟨0, 0⟩).alpha ∧
      LoadHolds rd (osPtrA h.c b 3) (2 * i + 1) (h.allRounds.getD i ⟨0, 0⟩).beta := by
  have h5 := hS.head (j := 3) (by omega)
  simp only [headSizes, List.getD_cons_succ, List.getD_cons_zero] at h5
  have a t := h.load hm (hS.headLt (j := 3) (by omega)) (by unfold osIxQbpA; omega) (e := 2 * i + t)
  have a0 := a 0 (by rw [h5]; omega)
  have a1 := a 1 (by rw [h5]; omega)
  rw [ownW_coefs, coefsC, getD_mapRange _ (by omega)] at a0 a1
  have d0 : (2 * i + 0) / 2 = i := by omega
  have d1 : (2 * i + 1) / 2 = i := by omega
  have m0 : (2 * i + 0) % 2 = 0 := by omega
  have m1 : (2 * i + 1) % 2 = 1 := by omega
  simp only [d0, d1, m0, m1, ↓reduceIte, one_ne_zero] at a0 a1
  exact ⟨a0, a1⟩

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
    (hrl : ∀ i < h.c.levels.length, (h.L i).rounds.length = ((h.c.levels.getD i default)).folds)
    {l j : ℕ} (hl : l < h.c.levels.length) (hj : j < ((h.c.levels.getD l default)).folds) :
    h.allRounds.getD (((h.c.levels.getD l default)).foldsOff + j) ⟨0, 0⟩ = (h.L l).rounds.getD j ⟨0, 0⟩ := by
  have hoff : ∀ l ≤ h.c.levels.length, ((h.Ls.take l).map fun a ↦ a.rounds.length).sum =
      if l = 0 then 0 else ((h.c.levels.getD (l - 1) default)).foldsOff + ((h.c.levels.getD (l - 1) default)).folds := by
    intro l
    induction l with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      have hm' : m < h.Ls.length := by omega
      rw [List.take_add_one, List.map_append, List.sum_append, ih (by omega), List.getElem?_eq_getElem hm']
      simp only [Option.toList_some, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
        Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      have hr : h.Ls[m].rounds.length = ((h.c.levels.getD m default)).folds := by
        have := hrl m (by omega)
        simpa only [OsHD.L, List.getD_eq_getElem _ _ hm'] using this
      rw [hr]
      rcases m with _ | m
      · simpa using hS.fo0
      · simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
        rw [hS.fo (l := m) (by omega)]
  have hl' : ((h.Ls.take l).map fun a ↦ a.rounds.length).sum = ((h.c.levels.getD l default)).foldsOff := by
    rw [hoff l hl.le]
    rcases l with _ | l
    · simpa using hS.fo0.symm
    · simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      rw [hS.fo (l := l) hl]
  have := flatMap_getD (fun a : LvAt ↦ a.rounds) ⟨0, 0⟩ h.Ls l j (by omega)
    (by rw [hrl l hl]; exact hj)
  rw [hl'] at this
  exact this

/-- OsHonest's `RoundsAt` of level `l`'s rounds at its coefficients. -/
theorem roundsAt_of (hS : HonStatic h.c) (hm : OsMemA rd h.c b h.own) (hL : h.Ls.length = h.c.levels.length)
    (hrl : ∀ i < h.c.levels.length, (h.L i).rounds.length = ((h.c.levels.getD i default)).folds) {l : ℕ}
    (hl : l < h.c.levels.length) :
    RoundsAt rd (osPtrA h.c b 3 * gen ^ (2 * ((h.c.levels.getD l default)).foldsOff)) (h.L l).rounds := by
  intro j hj
  rw [hrl l hl] at hj
  have hT : ((h.c.levels.getD l default)).foldsOff + ((h.c.levels.getD l default)).folds ≤ h.c.nFolds := by
    have hyr := hS.yr
    have key : ∀ d, l + d ≤ h.c.yrLevel →
        ((h.c.levels.getD l default)).foldsOff + ((h.c.levels.getD l default)).folds ≤
          ((h.c.levels.getD (l + d) default)).foldsOff + ((h.c.levels.getD (l + d) default)).folds := by
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
  obtain ⟨a0, a1⟩ := h.coefs_load hS hm (i := ((h.c.levels.getD l default)).foldsOff + j) (by omega)
  rw [h.allRounds_getD hS hL hrl hl hj] at a0 a1
  refine ⟨?_, ?_⟩ <;> rw [loadHolds_mul_gen_pow]
  · rw [show 2 * ((h.c.levels.getD l default)).foldsOff + 2 * j = 2 * (((h.c.levels.getD l default)).foldsOff + j) by ring]; exact a0
  · rw [show 2 * ((h.c.levels.getD l default)).foldsOff + (2 * j + 1) = 2 * (((h.c.levels.getD l default)).foldsOff + j) + 1 by ring]
    exact a1

end OsHD

end
end LeanVM.Guest.B1.Whir
