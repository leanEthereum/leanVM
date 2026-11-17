/-
  LeanVM.Guest.B1.Whir.CLvB

  A level after its positions honestly: the high part, the queries' dispatch and the glue.
-/

module

public import LeanVM.Guest.B1.Whir.CDisp
public import LeanVM.Guest.B1.Whir.Witness

/-!
# A level after its positions, honestly

* `osStep_of`: a block's state moved on, from its fields.
* `osHsCoefs_complete`, `osHsMid_complete`, `osHsFinal_complete`: a high part's coefficients
  loaded, scaled by their normalizers and stored.
* `osQueries_complete`: the dispatch into `level_queries` at its honest arguments (`osQArgsV`),
  returning the root's cells, `batched` and `λ^n`, the root stored in `level_roots`.
* `osGlue_complete`: a non-final level's claims glued, `λ`, `λ²·λ^n` and `1/λ` stored.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {H : CallRel → Reader → Prop}

/-- **A block's state moved on**, from its fields. -/
theorem osStep_of {σ σ' : Val} {st st' : OsSt} (hsf : st.Sf) (hok : st.Ok σ)
    (hag : AgreeBelow st.k σ σ') (hk : st.k ≤ st'.k) (hfl : st'.fs.length = 5)
    (hfs : ∀ f ∈ st'.fs, f < st'.k) (hcb : st'.cb < st'.k) (hcl : st'.claim < st'.k)
    (hco : st'.co < u128Bound) (hpad : st'.pad = st.pad) (hm : MatsOk σ' st'.mats)
    (hmb : MatsBelow st'.k st'.mats) : OsStep σ σ' st st' := by
  refine ⟨⟨⟨hfl, ⟨hfs, hcb, hcl, hmb⟩, hco, fun p hp ↦ ?_, by have := hsf.k; omega⟩, hm, ?_⟩, hk, hag⟩
  · rw [hpad] at hp; have := hsf.padB p hp; omega
  · intro p hp
    rw [hpad] at hp
    have hb := hsf.padB p hp
    obtain ⟨z1, z2, z3, z4⟩ := hok.pad p hp
    rw [hag _ (by omega), hag _ (by omega), hag _ (by omega), hag _ (by omega)]
    exact ⟨z1, z2, z3, z4⟩

/-! ## The high part -/

theorem osHsCoef_k (src i sc dst o k : ℕ) : k + 1 ≤ (osHsCoef src i sc dst o k).2 := by
  unfold osHsCoef; split_ifs <;> simp

theorem osHsCoefs_k (src dst : ℕ) (sc : ℕ → ℕ) (si di : ℕ) :
    ∀ n i k, k ≤ (osHsCoefs src dst sc si di n i k).2
  | 0, _, _ => le_rfl
  | n + 1, i, k => by
    have := osHsCoef_k src (si + i) (sc i) dst (di + i) k
    have := osHsCoefs_k src dst sc si di n (i + 1) (osHsCoef src (si + i) (sc i) dst (di + i) k).2
    show k ≤ (osHsCoefs src dst sc si di n (i + 1) _).2
    omega

/-- **One coefficient, honestly**: the word `x` loaded from `src·g^i`, times `word sc 0`, stored
at `dst·g^o`. -/
theorem osHsCoef_complete (σ : Val) {src i sc dst o k : ℕ} (x : E) (hs : src < k) (hd : dst < k)
    (hmem : ∀ C rd, H C rd → LoadHolds rd (σ (.n src)) i x ∧ LoadHolds rd (σ (.n dst)) o (x * word sc 0)) :
    BlkA H σ k (osHsCoef src i sc dst o k).2 (osHsCoef src i sc dst o k).1 (fun _ ↦ True) := by
  unfold osHsCoef
  split_ifs with h1
  · refine ⟨lstF k [x], fun C rd hH σ' ha hr ↦ ⟨?_, trivial⟩⟩
    have v0 := lstF_at hr (by simp) 0 (by simp)
    simp only [List.getD_cons_zero, Nat.add_zero] at v0
    obtain ⟨l1, l2⟩ := hmem C rd hH
    rw [h1, word_one, mul_one] at l2
    simp only [allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_load, osLd, v0, ha _ hs, ha _ hd]
    exact ⟨l1, l2⟩
  · refine ⟨lstF k [x, word sc 0, x * word sc 0], fun C rd hH σ' ha hr ↦ ⟨?_, trivial⟩⟩
    have v0 := lstF_at hr (by simp) 0 (by simp)
    have v1 := lstF_at hr (by simp) 1 (by simp)
    have v2 := lstF_at hr (by simp) 2 (by simp)
    simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at v0 v1 v2
    obtain ⟨l1, l2⟩ := hmem C rd hH
    simp only [allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_load, holds_const, holds_mul, osLd,
      osCst, osMul, v0, v1, v2, ha _ hs, ha _ hd]
    exact ⟨l1, trivial, trivial, l2⟩

/-- **A high part's coefficients `i .. i + n - 1`, honestly.** -/
theorem osHsCoefs_complete (src dst : ℕ) (sc : ℕ → ℕ) (si di : ℕ) (xs : ℕ → E) :
    ∀ (n i k : ℕ) (σ : Val), src < k → dst < k →
      (∀ C rd, H C rd → ∀ j, i ≤ j → j < i + n → LoadHolds rd (σ (.n src)) (si + j) (xs j) ∧
        LoadHolds rd (σ (.n dst)) (di + j) (xs j * word (sc j) 0)) →
      BlkA H σ k (osHsCoefs src dst sc si di n i k).2 (osHsCoefs src dst sc si di n i k).1
        (fun _ ↦ True)
  | 0, _, _, _, _, _, _ => BlkA.nil fun _ _ ↦ trivial
  | n + 1, i, k, σ, hs, hd, hmem => by
    have k1 := osHsCoef_k src (si + i) (sc i) dst (di + i) k
    have k2 := osHsCoefs_k src dst sc si di n (i + 1) (osHsCoef src (si + i) (sc i) dst (di + i) k).2
    have h := BlkA.seq (H := H) (by omega) k2
      (osHsCoef_complete (H := H) σ (xs i) hs hd fun C rd hH ↦ hmem C rd hH i le_rfl (by omega))
      fun σ1 ha1 _ ↦ osHsCoefs_complete src dst sc si di xs n (i + 1) _ σ1 (by omega) (by omega)
        fun C rd hH j h1 h2 ↦ by
          rw [ha1 _ hs, ha1 _ hd]
          exact hmem C rd hH j (by omega) (by omega)
    exact h.mono fun _ _ ↦ trivial

/-- **A non-final level's high part, honestly**: word `2 + j` of `sent`, scaled,
into `level_hs[lvl·8 + j]`. -/
theorem osHsMid_complete {lvl : ℕ} {lv : OsLv} {st : OsSt} (σ : Val) (hsf : st.Sf)
    (hok : ∀ C rd, H C rd → st.Ok σ) (hsent : st.sent < st.k) (high : ℕ → E)
    (hmem : ∀ C rd, H C rd → ∀ j < lv.folds, LoadHolds rd (σ (.n st.sent)) (2 + j) (high j) ∧
      LoadHolds rd (σ (.n osHs)) (lvl * hsStride + j) (high j *
        word (hsScale lv.vanish lv.highBits j (vanishInv (lv.vanish + lv.logCols))) 0)) :
    BlkA H σ st.k (osHsMid lvl lv st).2.k (osHsMid lvl lv st).1
      (fun σ' ↦ OsStep σ σ' st (osHsMid lvl lv st).2) := by
  have k36 : 33 ≤ st.k := hsf.k
  set K := (osHsCoefs st.sent osHs
    (fun c ↦ hsScale lv.vanish lv.highBits c (vanishInv (lv.vanish + lv.logCols))) 2 (lvl * hsStride)
    lv.folds 0 st.k).2 with hK
  have kk : st.k ≤ K := osHsCoefs_k _ _ _ _ _ _ _ _
  have h := osHsCoefs_complete (H := H) st.sent osHs
    (fun c ↦ hsScale lv.vanish lv.highBits c (vanishInv (lv.vanish + lv.logCols))) 2 (lvl * hsStride)
    high lv.folds 0 st.k σ hsent (show 24 < st.k by omega)
    fun C rd hH j _ h2 ↦ hmem C rd hH j (by omega)
  refine BlkA.monoH h.agree fun C rd hH σ' _ ⟨_, hag⟩ ↦ ?_
  have hok' := hok C rd hH
  refine osStep_of hsf hok' hag kk hsf.fs (fun f hf ↦ ?_) ?_ ?_ hsf.co rfl
    (matsOk_agree hok'.mats hsf.below.mats fun i hi ↦ hag i hi) ?_
  · have := hsf.below.fs f hf; show f < K; omega
  · have := hsf.below.cb; show st.cb < K; omega
  · have := hsf.below.claim; show st.claim < K; omega
  · intro m hm'; obtain ⟨a, b, d⟩ := hsf.below.mats m hm'
    exact ⟨by show m.out < K; omega,
      by show m.src < K; omega,
      by show m.base < K; omega⟩

/-- **The final level's lane, honestly**: a fresh buffer at `pH`, word `j` of
`final_msg`, scaled, into its word `j`. -/
theorem osHsFinal_complete {c : OsCfg} {lv : OsLv} {st : OsSt} (σ : Val) (hsf : st.Sf)
    (hok : ∀ C rd, H C rd → st.Ok σ) (pH : E) (lane : ℕ → E)
    (hmem : ∀ C rd, H C rd → ∀ j < c.yrLen + lv.folds, LoadHolds rd (σ (.n osFmsg)) j (lane j) ∧
      LoadHolds rd pH j (lane j * word (hsScale lv.vanish (c.yrLog + 1) j 1) 0)) :
    BlkA H σ st.k (osHsFinal c lv st).2.k (osHsFinal c lv st).1
      (fun σ' ↦ OsStep σ σ' st (osHsFinal c lv st).2 ∧ σ' (.n st.k) = gw (c.yrLen + lv.folds) ∧
        σ' (.n (osHsFinal c lv st).2.hs) = pH) := by
  have k36 : 33 ≤ st.k := hsf.k
  set n := c.yrLen + lv.folds with hn
  set K := (osHsCoefs osFmsg (st.k + 1) (fun i ↦ hsScale lv.vanish (c.yrLog + 1) i 1) 0 0 n 0 (st.k + 2)).2 with hK
  have kk : st.k + 2 ≤ K := osHsCoefs_k _ _ _ _ _ _ _ _
  have h := BlkA.seq (H := H) (show st.k ≤ st.k + 2 by omega) kk (heap_blk σ n st.k pH)
    (B := (osHsCoefs osFmsg (st.k + 1) (fun i ↦ hsScale lv.vanish (c.yrLog + 1) i 1) 0 0 n 0 (st.k + 2)).1) (OutB := fun _ ↦ True)
    fun σ1 ha1 ho1 ↦ osHsCoefs_complete osFmsg (st.k + 1) (fun i ↦ hsScale lv.vanish (c.yrLog + 1) i 1) 0 0 lane n 0 (st.k + 2) σ1
      (show 12 < st.k + 2 by omega) (by omega) fun C rd hH j _ h2 ↦ by
        obtain ⟨-, e1⟩ := ho1 C rd hH
        rw [e1, ha1 _ (show 12 < st.k by omega), Nat.zero_add]
        exact hmem C rd hH j (by omega)
  have ek : (osHsFinal c lv st).2.k = K := rfl
  have el : (osHsFinal c lv st).1 = osHeap n st.k ++ (osHsCoefs osFmsg (st.k + 1) (fun i ↦ hsScale lv.vanish (c.yrLog + 1) i 1) 0 0 n 0 (st.k + 2)).1 :=
    rfl
  have eh : (osHsFinal c lv st).2.hs = st.k + 1 := rfl
  rw [ek, el, eh]
  refine BlkA.monoH h.agree fun C rd hH σ' _ ⟨⟨⟨e0, e1⟩, _⟩, hag⟩ ↦ ?_
  have hok' := hok C rd hH
  refine ⟨osStep_of hsf hok' hag (by omega) hsf.fs (fun f hf ↦ ?_) ?_ ?_ hsf.co rfl
    (matsOk_agree hok'.mats hsf.below.mats fun i hi ↦ hag i hi) ?_, e0, e1⟩
  · have := hsf.below.fs f hf; show f < K; omega
  · have := hsf.below.cb; show st.cb < K; omega
  · have := hsf.below.claim; show st.claim < K; omega
  · intro m hm'; obtain ⟨a, b, d⟩ := hsf.below.mats m hm'
    exact ⟨by show m.out < K; omega,
      by show m.src < K; omega,
      by show m.base < K; omega⟩

/-! ## The queries -/

/-- `level_queries`' honest arguments: `λ` and `1/λ` (`0, 0` at the final level), the round
coefficients, the high part, the positions and windows. -/
def osQArgsV (σ : Val) (c : OsCfg) (lvl : ℕ) (lv : OsLv) (st : OsSt) : List E :=
  [if lvl = c.yrLevel then 0 else σ (.n st.lam), if lvl = c.yrLevel then 0 else σ (.n st.lamInv),
    σ (.n osCoefs) * gen ^ (2 * lv.foldsOff),
    if lvl = c.yrLevel then σ (.n st.hs) else σ (.n osHs) * gen ^ (lvl * hsStride),
    σ (.n osQpos) * gen ^ lv.posOff, σ (.n osQbp) * gen ^ lv.posOff]

/-- **The level's queries, honestly**: the dispatch into `level_queries` at its honest arguments
(`osQArgsV`), returning the root's two cells, `batched` and `λ^n`, the root's cells stored into
`level_roots`. -/
theorem osQueries_complete {c : OsCfg} {lvl : ℕ} {lv : OsLv} {st : OsSt} (σ : Val) (hsf : st.Sf)
    (hok : ∀ C rd, H C rd → st.Ok σ) (r0 r1 batched lamPow : E)
    (h3 : 2 * lv.foldsOff < u128Bound) (hpo : lv.posOff < u128Bound)
    (hh8 : lvl * hsStride < u128Bound)
    (hli : lvl ≠ c.yrLevel → st.lam < st.k ∧ st.lamInv < st.k) (hhs : lvl = c.yrLevel → st.hs < st.k)
    (hrate : ∀ C rd, H C rd → LvRate σ c lvl lv)
    (hq : ∀ C rd, H C rd → C (osQueriesName c lvl lv) (osQArgsV σ c lvl lv st) [r0, r1, batched, lamPow])
    (hroots : ∀ C rd, H C rd → LoadHolds rd (σ (.n osRoots)) (2 * lvl) r0 ∧
      LoadHolds rd (σ (.n osRoots)) (2 * lvl + 1) r1) :
    BlkA H σ st.k (osQueries c lvl lv st).2.k (osQueries c lvl lv st).1 (fun σ' ↦
      OsStep σ σ' st (osQueries c lvl lv st).2 ∧
      (osQCallOf c lvl lv st).1.map σ' = osQArgsV σ c lvl lv st ∧
      (osQCallOf c lvl lv st).2.map σ' = [r0, r1, batched, lamPow] ∧
      σ' (.n (osQueries c lvl lv st).2.batched) = batched ∧
      σ' (.n (osQueries c lvl lv st).2.lamPow) = lamPow) := by
  set k := st.k with hk
  set li : List Stmt × ℕ × ℕ × OsSt := if lvl = c.yrLevel then
    ([osCst k (word 0 0), osCst (k + 1) (word 0 0)], k, k + 1, { st with k := k + 2 })
    else ([], st.lam, st.lamInv, st) with hliD
  set cf := osMatS c.plan osCoefs (2 * lv.foldsOff) li.2.2.2 with hcf
  set hp : List Stmt × ℕ × OsSt := if lvl = c.yrLevel then ([], st.hs, cf.2.2)
    else osMatS c.plan osHs (lvl * hsStride) cf.2.2 with hhpD
  set qp := osMatS c.plan osQpos lv.posOff hp.2.2 with hqp
  set wp := osMatS c.plan osQbp lv.posOff qp.2.2 with hwp
  set g := wp.2.2.k with hg
  have k33 : 33 ≤ k := hsf.k
  have k3 : k ≤ li.2.2.2.k := by rw [hliD]; split_ifs <;> dsimp only <;> omega
  have k4 : li.2.2.2.k ≤ cf.2.2.k := osMatS_k _ _ _ _
  have k5 : cf.2.2.k ≤ hp.2.2.k := by
    rw [hhpD]; split_ifs
    · exact le_rfl
    · exact osMatS_k _ _ _ _
  have k6 : hp.2.2.k ≤ qp.2.2.k := osMatS_k _ _ _ _
  have k7 : qp.2.2.k ≤ g := osMatS_k _ _ _ _
  have pli : li.2.1 < li.2.2.2.k ∧ li.2.2.1 < li.2.2.2.k := by
    rw [hliD]; split_ifs with hf
    · simp only; omega
    · have := hli hf; simp only; omega
  have pcf : cf.2.1 < cf.2.2.k := osMatS_ptr_lt _ _ _ _ (show 18 < li.2.2.2.k by omega)
  have php : hp.2.1 < hp.2.2.k := by
    rw [hhpD]; split_ifs with hf
    · have := hhs hf; simp only; omega
    · exact osMatS_ptr_lt _ _ _ _ (show 24 < cf.2.2.k by omega)
  have pqp : qp.2.1 < qp.2.2.k := osMatS_ptr_lt _ _ _ _ (show 30 < hp.2.2.k by omega)
  have pwp : wp.2.1 < g := osMatS_ptr_lt _ _ _ _ (show 32 < qp.2.2.k by omega)
  have mli : li.2.2.2.mats = st.mats := by rw [hliD]; split_ifs <;> rfl
  have mb3 : MatsBelow li.2.2.2.k li.2.2.2.mats := fun m hm ↦ by
    rw [mli] at hm; obtain ⟨a, b, d⟩ := hsf.below.mats m hm; exact ⟨by omega, by omega, by omega⟩
  have mb4 : MatsBelow cf.2.2.k cf.2.2.mats := osMatS_below mb3 (show 18 < li.2.2.2.k by omega)
  have mb5 : MatsBelow hp.2.2.k hp.2.2.mats := by
    rw [hhpD]; split_ifs
    · exact mb4
    · exact osMatS_below mb4 (show 24 < cf.2.2.k by omega)
  have mb6 : MatsBelow qp.2.2.k qp.2.2.mats := osMatS_below mb5 (show 30 < hp.2.2.k by omega)
  -- `λ`, `1/λ`, or `0, 0` at the final level
  have b3 : BlkA H σ k li.2.2.2.k li.1 (fun σ' ↦
      σ' (.n li.2.1) = (if lvl = c.yrLevel then 0 else σ (.n st.lam)) ∧
      σ' (.n li.2.2.1) = (if lvl = c.yrLevel then 0 else σ (.n st.lamInv))) := by
    rw [hliD]
    split_ifs with hf
    · dsimp only
      refine ⟨lstF k [word 0 0, word 0 0], fun C rd hH σ' _ hr ↦ ?_⟩
      have v0 := lstF_at hr (by simp) 0 (by simp)
      have v1 := lstF_at hr (by simp) 1 (by simp)
      simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at v0 v1
      refine ⟨?_, by rw [v0, word_zero], by rw [v1, word_zero]⟩
      simp only [allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_const, osCst, v0, v1]
    · dsimp only
      exact BlkA.nil fun σ' ha ↦ by
        have := hli hf
        exact ⟨ha _ this.1, ha _ this.2⟩
  -- the round coefficients
  have b4 := BlkA.seq (H := H) k3 k4 b3 (B := cf.1)
    (OutB := fun σ' ↦ σ' (.n cf.2.1) = σ (.n osCoefs) * gen ^ (2 * lv.foldsOff) ∧
      MatsOk σ' cf.2.2.mats ∧ MatsBelow cf.2.2.k cf.2.2.mats) fun σ1 ha1 _ ↦ by
      have h := osMatS_blkA (H := H) (P := c.plan) (base := osCoefs) (off := 2 * lv.foldsOff)
        (s := li.2.2.2) σ1 (show 18 < li.2.2.2.k by omega) mb3
        (fun C rd hH ↦ by
          rw [mli]; exact matsOk_agree (hok C rd hH).mats hsf.below.mats fun i hi ↦ ha1 i hi) h3
      rw [ha1 osCoefs (by show 18 < k; omega)] at h
      exact h
  -- the high part
  have b5 := BlkA.seq (H := H) (le_trans k3 k4) k5 b4 (B := hp.1)
    (OutB := fun σ' ↦ σ' (.n hp.2.1) =
      (if lvl = c.yrLevel then σ (.n st.hs) else σ (.n osHs) * gen ^ (lvl * hsStride)) ∧
      MatsOk σ' hp.2.2.mats) fun σ1 ha1 ho1 ↦ by
      rw [hhpD]
      split_ifs with hf
      · dsimp only
        refine BlkA.monoH (BlkA.nil (Out := fun _ ↦ True) fun _ _ ↦ trivial) fun C rd hH σ' ha _ ↦ ?_
        have := hhs hf
        refine ⟨by rw [ha _ (show st.hs < cf.2.2.k by omega), ha1 _ this], ?_⟩
        exact matsOk_agree (ho1 C rd hH).2.2.1 mb4 fun i hi ↦ ha i hi
      · have h := osMatS_blkA (H := H) (P := c.plan) (base := osHs) (off := lvl * hsStride)
          (s := cf.2.2) σ1 (show 24 < cf.2.2.k by omega) mb4 (fun C rd hH ↦ (ho1 C rd hH).2.2.1) hh8
        rw [ha1 osHs (by show 24 < k; omega)] at h
        exact h.mono fun σ' h' ↦ ⟨h'.1, h'.2.1⟩
  -- the positions and windows
  have b6 := BlkA.seq (H := H) (show k ≤ hp.2.2.k by omega) k6 b5 (B := qp.1)
    (OutB := fun σ' ↦ σ' (.n qp.2.1) = σ (.n osQpos) * gen ^ lv.posOff ∧ MatsOk σ' qp.2.2.mats ∧
      MatsBelow qp.2.2.k qp.2.2.mats) fun σ1 ha1 ho1 ↦ by
      have h := osMatS_blkA (H := H) (P := c.plan) (base := osQpos) (off := lv.posOff) (s := hp.2.2) σ1
        (show 30 < hp.2.2.k by omega) mb5 (fun C rd hH ↦ (ho1 C rd hH).2.2) hpo
      rw [ha1 osQpos (by show 30 < k; omega)] at h
      exact h
  have b7 := BlkA.seq (H := H) (show k ≤ qp.2.2.k by omega) k7 b6 (B := wp.1)
    (OutB := fun σ' ↦ σ' (.n wp.2.1) = σ (.n osQbp) * gen ^ lv.posOff ∧ MatsOk σ' wp.2.2.mats ∧
      MatsBelow wp.2.2.k wp.2.2.mats) fun σ1 ha1 ho1 ↦ by
      have h := osMatS_blkA (H := H) (P := c.plan) (base := osQbp) (off := lv.posOff) (s := qp.2.2) σ1
        (show 32 < qp.2.2.k by omega) mb6 (fun C rd hH ↦ (ho1 C rd hH).2.2.1) hpo
      rw [ha1 osQbp (by show 32 < k; omega)] at h
      exact h
  -- the dispatch
  have hargsV : ∀ σ1 : Val, AgreeBelow k σ σ1 → (∀ C rd, H C rd →
      ((((((σ1 (.n li.2.1) = (if lvl = c.yrLevel then 0 else σ (.n st.lam)) ∧
        σ1 (.n li.2.2.1) = (if lvl = c.yrLevel then 0 else σ (.n st.lamInv))) ∧
        σ1 (.n cf.2.1) = σ (.n osCoefs) * gen ^ (2 * lv.foldsOff) ∧ MatsOk σ1 cf.2.2.mats ∧
          MatsBelow cf.2.2.k cf.2.2.mats) ∧
        σ1 (.n hp.2.1) = (if lvl = c.yrLevel then σ (.n st.hs) else σ (.n osHs) * gen ^ (lvl * hsStride)) ∧
          MatsOk σ1 hp.2.2.mats) ∧
        σ1 (.n qp.2.1) = σ (.n osQpos) * gen ^ lv.posOff ∧ MatsOk σ1 qp.2.2.mats ∧
          MatsBelow qp.2.2.k qp.2.2.mats) ∧
        σ1 (.n wp.2.1) = σ (.n osQbp) * gen ^ lv.posOff ∧ MatsOk σ1 wp.2.2.mats ∧
          MatsBelow wp.2.2.k wp.2.2.mats))) → ∀ C rd, H C rd →
      [li.2.1, li.2.2.1, cf.2.1, hp.2.1, qp.2.1, wp.2.1].map (fun i ↦ σ1 (.n i)) =
        osQArgsV σ c lvl lv st := fun σ1 _ ho1 C rd hH ↦ by
    obtain ⟨⟨⟨⟨⟨eli, eli2⟩, ecf, -⟩, ehp, -⟩, eqp, -⟩, ewp, -⟩ := ho1 C rd hH
    simp only [List.map_cons, List.map_nil, eli, eli2, ecf, ehp, eqp, ewp]
    rfl
  have b8 := BlkA.seq (H := H) (show k ≤ g by omega) (show g ≤ g + 4 by omega) b7
    (B := [.dispatch (.n osRate) ((c.lvAt lvl).map (osQueriesName c lvl))
      ([li.2.1, li.2.2.1, cf.2.1, hp.2.1, qp.2.1, wp.2.1].map V.n) (osRun g 4)])
    (OutB := fun σ' ↦ [li.2.1, li.2.2.1, cf.2.1, hp.2.1, qp.2.1, wp.2.1].map (fun i ↦ σ' (.n i)) =
        osQArgsV σ c lvl lv st ∧ ∀ j < 4, σ' (.n (g + j)) = [r0, r1, batched, lamPow].getD j 0)
    fun σ1 ha1 ho1 ↦ BlkA.monoH (Out := fun σ' ↦ ∀ j < 4, σ' (.n (g + j)) = [r0, r1, batched, lamPow].getD j 0)
      (rateDisp_blk (H := H) (σ := σ1) (c := c) (lvl := lvl) (lv := lv) (r := g) (n := 4)
        (osQueriesName c lvl) [r0, r1, batched, lamPow] rfl
        (fun i hi ↦ by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
        (show 0 < g by omega)
        (fun C rd hH ↦ by
          obtain ⟨ri, hri, hx, hlen, hlv⟩ := hrate C rd hH
          exact ⟨ri, hri, by rw [ha1 _ (show 0 < k by omega)]; exact hx, hlen, hlv⟩)
        (fun C rd hH ↦ by rw [hargsV σ1 ha1 ho1 C rd hH]; exact hq C rd hH))
      fun C rd hH σ' ha hv ↦ ⟨by
        rw [← hargsV σ1 ha1 ho1 C rd hH]
        simp only [List.map_cons, List.map_nil]
        rw [ha _ (pli.1.trans_le (by omega)), ha _ (pli.2.trans_le (by omega)),
          ha _ (show cf.2.1 < g by omega), ha _ (show hp.2.1 < g by omega),
          ha _ (show qp.2.1 < g by omega), ha _ pwp], hv⟩
  -- the root into `level_roots`
  have b9 := BlkA.seq (H := H) (show k ≤ g + 4 by omega) (show g + 4 ≤ g + 4 from le_rfl) b8
    (B := [osLd g osRoots (2 * lvl), osLd (g + 1) osRoots (2 * lvl + 1)]) (OutB := fun _ ↦ True)
    fun σ1 ha1 ho1 ↦ stores_blk fun C rd hH σ' ha ↦ by
      have v := (ho1 C rd hH).2.2
      have v0 := v 0 (by omega)
      have v1 := v 1 (by omega)
      simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at v0 v1
      simp only [allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_load, osLd]
      rw [ha _ (show g < g + 4 by omega), ha _ (show g + 1 < g + 4 by omega),
        ha _ (show 14 < g + 4 by omega), v0, v1, ha1 _ (show 14 < k by omega)]
      exact hroots C rd hH
  have hfld : (osQueries c lvl lv st).2.fs = st.fs ∧ (osQueries c lvl lv st).2.cb = st.cb ∧
      (osQueries c lvl lv st).2.co = st.co ∧ (osQueries c lvl lv st).2.claim = st.claim ∧
      (osQueries c lvl lv st).2.pad = st.pad := by
    unfold osQueries; dsimp only; split_ifs <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  have ek : (osQueries c lvl lv st).2.k = g + 4 := rfl
  have em : (osQueries c lvl lv st).2.mats = wp.2.2.mats := rfl
  have eb : (osQueries c lvl lv st).2.batched = g + 2 := rfl
  have elp : (osQueries c lvl lv st).2.lamPow = g + 3 := rfl
  have el : (osQueries c lvl lv st).1 = li.1 ++ cf.1 ++ hp.1 ++ qp.1 ++ wp.1 ++
      [.dispatch (.n osRate) ((c.lvAt lvl).map (osQueriesName c lvl))
        ([li.2.1, li.2.2.1, cf.2.1, hp.2.1, qp.2.1, wp.2.1].map V.n) (osRun g 4)] ++
      [osLd g osRoots (2 * lvl), osLd (g + 1) osRoots (2 * lvl + 1)] := by
    rw [List.append_assoc (li.1 ++ cf.1 ++ hp.1 ++ qp.1 ++ wp.1)]; rfl
  have eq1 : (osQCallOf c lvl lv st).1 = [li.2.1, li.2.2.1, cf.2.1, hp.2.1, qp.2.1, wp.2.1].map V.n := rfl
  have eq2 : (osQCallOf c lvl lv st).2 = osRun g 4 := rfl
  rw [ek, el, eq1, eq2, eb, elp]
  refine BlkA.monoH b9.agree fun C rd hH σ' _ ⟨⟨⟨ho7, eargs, ev⟩, _⟩, hag⟩ ↦ ?_
  obtain ⟨-, -, hm, hb⟩ := ho7
  have hok' := hok C rd hH
  obtain ⟨efs, ecb, eco, ecl, epad⟩ := hfld
  have ev' : ∀ j < 4, σ' (.n (g + j)) = [r0, r1, batched, lamPow].getD j 0 := ev
  refine ⟨osStep_of hsf hok' hag (by rw [ek]; omega) (by rw [efs]; exact hsf.fs) (fun f hf ↦ ?_) ?_ ?_
    (by rw [eco]; exact hsf.co) epad (by rw [em]; exact hm) ?_, ?_, ?_, ev' 2 (by omega), ev' 3 (by omega)⟩
  · rw [efs] at hf; have := hsf.below.fs f hf; rw [ek]; omega
  · rw [ecb, ek]; have := hsf.below.cb; omega
  · rw [ecl, ek]; have := hsf.below.claim; omega
  · rw [em, ek]; intro m hm'; obtain ⟨a, b, d⟩ := hb m hm'
    exact ⟨by omega, by omega, by omega⟩
  · rw [List.map_map]; exact eargs
  · rw [osRun_map, show List.range 4 = [0, 1, 2, 3] from rfl]
    simp only [List.map_cons, List.map_nil]
    rw [ev' 0 (by omega), ev' 1 (by omega), ev' 2 (by omega), ev' 3 (by omega)]
    rfl

/-! ## The glue -/

/-- The glue's values: `λ·y0`, the claim plus it, `λ²`, `λ²·λ^n`, times the batch, the new claim. -/
def glueVals (cl lam y0 lp b : E) : List E :=
  [lam * y0, cl + lam * y0, lam * lam, lam * lam * lp, lam * lam * lp * b, cl + lam * y0 + lam * lam * lp * b]

/-- **A non-final level's claims glued, honestly**: `λ` into `ood_scalars`, `λ²·λ^n` (`λ^n` from
`level_queries`) into `level_scales`, `1/λ` into `level_lam_invs`; the new claim the old plus
`λ·y0 + λ²·λ^n·batched`. -/
theorem osGlue_complete {lvl : ℕ} {st : OsSt} (σ : Val) (hsf : st.Sf)
    (hok : ∀ C rd, H C rd → st.Ok σ) (hlam : st.lam < st.k) (hy0 : st.ys.getD 0 0 < st.k)
    (hbat : st.batched < st.k) (hli : st.lamInv < st.k) (hlp : st.lamPow < st.k)
    (hmem : ∀ C rd, H C rd →
      LoadHolds rd (σ (.n osOodSc)) (lvl + 1) (σ (.n st.lam)) ∧
      LoadHolds rd (σ (.n osBetas)) lvl (σ (.n st.lam) * σ (.n st.lam) * σ (.n st.lamPow)) ∧
      LoadHolds rd (σ (.n osMus)) lvl (σ (.n st.lamInv))) :
    BlkA H σ st.k (osGlue lvl st).2.k (osGlue lvl st).1 (fun σ' ↦
      OsStep σ σ' st (osGlue lvl st).2 ∧
      σ' (.n (osGlue lvl st).2.claim) = σ (.n st.claim) + σ (.n st.lam) * σ (.n (st.ys.getD 0 0)) +
        σ (.n st.lam) * σ (.n st.lam) * σ (.n st.lamPow) * σ (.n st.batched)) := by
  set L := σ (.n st.lam) with hL
  set Y0 := σ (.n (st.ys.getD 0 0)) with hY0
  set cl := σ (.n st.claim) with hcl
  set B := σ (.n st.batched) with hB
  set LP := σ (.n st.lamPow) with hLP
  have k33 : 33 ≤ st.k := hsf.k
  have hclk : st.claim < st.k := hsf.below.claim
  have b1 : BlkA H σ st.k (st.k + 6) (osGlue lvl st).1
      (fun σ' ↦ ∀ j < 6, σ' (.n (st.k + j)) = (glueVals cl L Y0 LP B).getD j 0) := by
    refine ⟨lstF st.k (glueVals cl L Y0 LP B), fun C rd hH σ' ha hr ↦ ?_⟩
    have v : ∀ j < 6, σ' (.n (st.k + j)) = (glueVals cl L Y0 LP B).getD j 0 := fun j hj ↦
      lstF_at hr (by simp [glueVals]) j (by simp [glueVals]; omega)
    refine ⟨?_, v⟩
    have v0 := v 0 (by omega)
    have v1 := v 1 (by omega)
    have v2 := v 2 (by omega)
    have v3 := v 3 (by omega)
    have v4 := v 4 (by omega)
    have v5 := v 5 (by omega)
    simp only [glueVals, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at v0 v1 v2 v3 v4 v5
    obtain ⟨l0, l2, l3⟩ := hmem C rd hH
    simp only [osGlue, allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_load, holds_mul, holds_add,
      osLd, osMul, osAdd, v0, v1, v2, v3, v4, v5, ha _ hlam, ha _ hy0, ha _ hclk, ha _ hbat, ha _ hli,
      ha _ hlp, ha _ (show 28 < st.k by omega), ha _ (show 20 < st.k by omega), ha _ (show 22 < st.k by omega)]
    refine ⟨l0, ?_, ?_, ?_, ?_, ?_, ?_, l2, l3⟩ <;> trivial
  have ek : (osGlue lvl st).2.k = st.k + 6 := rfl
  have ecl : (osGlue lvl st).2.claim = st.k + 5 := rfl
  rw [ek, ecl]
  refine BlkA.monoH b1.agree fun C rd hH σ' _ ⟨ev, hag⟩ ↦ ⟨?_, by simpa [glueVals] using ev 5 (by omega)⟩
  have hok' := hok C rd hH
  refine osStep_of hsf hok' hag (show st.k ≤ st.k + 6 by omega) hsf.fs (fun f hf ↦ ?_) ?_ ?_ hsf.co rfl
    (matsOk_agree hok'.mats hsf.below.mats fun i hi ↦ hag i hi) ?_
  · have := hsf.below.fs f hf; show f < st.k + 6; omega
  · have := hsf.below.cb; show st.cb < st.k + 6; omega
  · show st.k + 5 < st.k + 6; omega
  · intro m hm'; obtain ⟨a, b, d⟩ := hsf.below.mats m hm'
    exact ⟨by show m.out < st.k + 6; omega, by show m.src < st.k + 6; omega,
      by show m.base < st.k + 6; omega⟩

end
end LeanVM.Guest.B1.Whir
