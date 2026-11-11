/-
  LeanVM.Guest.B1.Whir.CLvB

  A level after its squeezes honestly on f128: the cap, the high part, the queries' call and the
  glue.
-/

module

public import LeanVM.Guest.B1.Whir.CLvSq
public import LeanVM.Guest.B1.Place.OsCallV
public import LeanVM.Guest.B1.Whir.CSqLoop

/-!
# A level after its squeezes, honestly (G:1638-1720)

* `osStep_of`: a block's state moved on, from its fields.
* `osCap_complete`: `verify_merkle_cap` on the level's cap and flags, its returns stored in
  `level_roots`.
* `osHsCoefs_complete`, `osHsMid_complete`, `osHsFinal_complete`: a high part's coefficients
  loaded, scaled by their normalizers and stored.
* `osQueries_complete`: `opening_queries` at its honest arguments (`osQCallAt`), returning a
  given `batched`.
* `osGlue_complete`: a non-final level's claims glued, `λ`, `λ²`, `λ³·λ^Q` and `1/λ` stored.
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

/-! ## The cap -/

/-- **The level's cap, honestly** (G:1638-1642): `verify_merkle_cap` returning the root's cells
`r0, r1`, stored in `level_roots`. -/
theorem osCap_complete {c : OsCfg} {lvl : ℕ} {lv : OsLv} {st : OsSt} (σ : Val) (hsf : st.Sf)
    (hok : ∀ C rd, H C rd → st.Ok σ) (r0 r1 : E) (hc4 : 4 * lv.capOff < u128Bound)
    (hcall : ∀ C rd, H C rd → C ("verify_merkle_cap__L" ++ natStr lv.capDepth)
      [σ (.n osCaps) * gen ^ (4 * lv.capOff), σ (.n osFlags) * gen ^ lv.capOff] [r0, r1])
    (hroots : ∀ C rd, H C rd → LoadHolds rd (σ (.n osRoots)) (2 * lvl) r0 ∧
      LoadHolds rd (σ (.n osRoots)) (2 * lvl + 1) r1) :
    BlkA H σ st.k (osCap c lvl lv st).2.k (osCap c lvl lv st).1
      (fun σ' ↦ OsStep σ σ' st (osCap c lvl lv st).2) := by
  set k := st.k with hk
  set cp := osMatS c.plan osCaps (4 * lv.capOff) st with hcp
  set fl := osMatS c.plan osFlags lv.capOff cp.2.2 with hfl
  set r := fl.2.2.k with hr
  have k36 : 36 ≤ k := hsf.k
  have k1 : k ≤ cp.2.2.k := osMatS_k _ _ _ _
  have k2 : cp.2.2.k ≤ r := osMatS_k _ _ _ _
  have pcp : cp.2.1 < cp.2.2.k := osMatS_ptr_lt _ _ _ _ (show 11 < k by omega)
  have pfl : fl.2.1 < r := osMatS_ptr_lt _ _ _ _ (show 13 < cp.2.2.k by omega)
  have hco4 : lv.capOff < u128Bound := lt_of_le_of_lt (by omega) hc4
  have b1 := osMatS_blkA (H := H) (P := c.plan) (base := osCaps) (off := 4 * lv.capOff) (s := st) σ
    (show 11 < k by omega) hsf.below.mats (fun C rd hH ↦ (hok C rd hH).mats) hc4
  have b2 := BlkA.seq (H := H) k1 k2 b1 (B := fl.1)
    (OutB := fun σ' ↦ σ' (.n fl.2.1) = σ (.n osFlags) * gen ^ lv.capOff ∧ MatsOk σ' fl.2.2.mats ∧
      MatsBelow fl.2.2.k fl.2.2.mats) fun σ1 ha1 ho1 ↦ by
      have h := osMatS_blkA (H := H) (P := c.plan) (base := osFlags) (off := lv.capOff) (s := cp.2.2) σ1
        (show 13 < cp.2.2.k by omega) (osMatS_below hsf.below.mats (show 11 < k by omega))
        (fun C rd hH ↦ (ho1 C rd hH).2.1) hco4
      rw [ha1 osFlags (by show 13 < k; omega)] at h
      exact h
  have b3 := BlkA.seq (H := H) (show k ≤ r by omega) (show r ≤ r + 2 by omega) b2
    (B := [.call ("verify_merkle_cap__L" ++ natStr lv.capDepth) [.n cp.2.1, .n fl.2.1] [.n r, .n (r + 1)],
      osLd r osRoots (2 * lvl), osLd (r + 1) osRoots (2 * lvl + 1)])
    (OutB := fun _ ↦ True) fun σ1 ha1 ho1 ↦ by
      refine ⟨lstF r [r0, r1], fun C rd hH σ' ha hr' ↦ ?_⟩
      have v0 := lstF_at hr' (by simp) 0 (by simp)
      have v1 := lstF_at hr' (by simp) 1 (by simp)
      simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at v0 v1
      obtain ⟨⟨e1, -, -⟩, e2, -, -⟩ := ho1 C rd hH
      have ec : σ' (.n cp.2.1) = σ (.n osCaps) * gen ^ (4 * lv.capOff) := by
        rw [ha _ (by omega), e1]
      have ef : σ' (.n fl.2.1) = σ (.n osFlags) * gen ^ lv.capOff := by rw [ha _ pfl, e2]
      have er : σ' (.n osRoots) = σ (.n osRoots) := by
        rw [ha _ (show 17 < r by omega), ha1 _ (show 17 < k by omega)]
      obtain ⟨l0, l1⟩ := hroots C rd hH
      refine ⟨?_, trivial⟩
      simp only [allOk_cons, allOk_nil, and_true, stmtOk_call, stmtOk_atom, holds_load, osLd,
        List.map_cons, List.map_nil, ec, ef, er, v0, v1]
      exact ⟨hcall C rd hH, l0, l1⟩
  refine BlkA.congr (BlkA.monoH b3.agree fun C rd hH σ' ha ⟨⟨⟨_, _, hm, hb⟩, _⟩, hag⟩ ↦ ?_)
    (by simp only [osCap, List.append_assoc]; rfl)
  have hok' := hok C rd hH
  refine osStep_of hsf hok' hag (show k ≤ r + 2 by omega) hsf.fs (fun f hf ↦ ?_) ?_ ?_ hsf.co rfl
    hm ?_
  · have := hsf.below.fs f hf; show f < r + 2; omega
  · have := hsf.below.cb; show st.cb < r + 2; omega
  · have := hsf.below.claim; show st.claim < r + 2; omega
  · intro m hm'; obtain ⟨a, b, d⟩ := hb m hm'
    exact ⟨by show m.out < r + 2; omega, by show m.src < r + 2; omega,
      by show m.base < r + 2; omega⟩

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

/-- **A non-final level's high part, honestly** (G:1684-1691): word `2 + j` of `sent`, scaled,
into `level_hs[lvl·8 + j]`. -/
theorem osHsMid_complete {lvl : ℕ} {lv : OsLv} {st : OsSt} (σ : Val) (hsf : st.Sf)
    (hok : ∀ C rd, H C rd → st.Ok σ) (hsent : st.sent < st.k) (high : ℕ → E)
    (hmem : ∀ C rd, H C rd → ∀ j < lv.folds, LoadHolds rd (σ (.n st.sent)) (2 + j) (high j) ∧
      LoadHolds rd (σ (.n osHs)) (lvl * hsStride + j) (high j *
        word (hsScale lv.vanish lv.highBits j (vanishInv (lv.vanish + lv.logCols))) 0)) :
    BlkA H σ st.k (osHsMid lvl lv st).2.k (osHsMid lvl lv st).1
      (fun σ' ↦ OsStep σ σ' st (osHsMid lvl lv st).2) := by
  have k36 : 36 ≤ st.k := hsf.k
  set K := (osHsCoefs st.sent osHs
    (fun c ↦ hsScale lv.vanish lv.highBits c (vanishInv (lv.vanish + lv.logCols))) 2 (lvl * hsStride)
    lv.folds 0 st.k).2 with hK
  have kk : st.k ≤ K := osHsCoefs_k _ _ _ _ _ _ _ _
  have h := osHsCoefs_complete (H := H) st.sent osHs
    (fun c ↦ hsScale lv.vanish lv.highBits c (vanishInv (lv.vanish + lv.logCols))) 2 (lvl * hsStride)
    high lv.folds 0 st.k σ hsent (show 27 < st.k by omega)
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

/-- **The final level's lane, honestly** (G:1673-1683): a fresh buffer at `pH`, word `j` of
`final_msg`, scaled, into its word `j`. -/
theorem osHsFinal_complete {c : OsCfg} {lv : OsLv} {st : OsSt} (σ : Val) (hsf : st.Sf)
    (hok : ∀ C rd, H C rd → st.Ok σ) (pH : E) (lane : ℕ → E)
    (hmem : ∀ C rd, H C rd → ∀ j < c.yrLen + lv.folds, LoadHolds rd (σ (.n osFmsg)) j (lane j) ∧
      LoadHolds rd pH j (lane j * word (hsScale lv.vanish (c.yrLog + 1) j 1) 0)) :
    BlkA H σ st.k (osHsFinal c lv st).2.k (osHsFinal c lv st).1
      (fun σ' ↦ OsStep σ σ' st (osHsFinal c lv st).2 ∧ σ' (.n st.k) = gw (c.yrLen + lv.folds) ∧
        σ' (.n (osHsFinal c lv st).2.hs) = pH) := by
  have k36 : 36 ≤ st.k := hsf.k
  set n := c.yrLen + lv.folds with hn
  set K := (osHsCoefs osFmsg (st.k + 1) (fun i ↦ hsScale lv.vanish (c.yrLog + 1) i 1) 0 0 n 0 (st.k + 2)).2 with hK
  have kk : st.k + 2 ≤ K := osHsCoefs_k _ _ _ _ _ _ _ _
  have h := BlkA.seq (H := H) (show st.k ≤ st.k + 2 by omega) kk (heap_blk σ n st.k pH)
    (B := (osHsCoefs osFmsg (st.k + 1) (fun i ↦ hsScale lv.vanish (c.yrLog + 1) i 1) 0 0 n 0 (st.k + 2)).1) (OutB := fun _ ↦ True)
    fun σ1 ha1 ho1 ↦ osHsCoefs_complete osFmsg (st.k + 1) (fun i ↦ hsScale lv.vanish (c.yrLog + 1) i 1) 0 0 lane n 0 (st.k + 2) σ1
      (show 15 < st.k + 2 by omega) (by omega) fun C rd hH j _ h2 ↦ by
        obtain ⟨-, e1⟩ := ho1 C rd hH
        rw [e1, ha1 _ (show 15 < st.k by omega), Nat.zero_add]
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

/-- `opening_queries`' honest arguments: the cap, its flags, `1/λ` (`0` at the final level), the
round coefficients, the high part, the positions and windows, `g^pairs`. -/
def osQArgsV (σ : Val) (c : OsCfg) (lvl : ℕ) (lv : OsLv) (st : OsSt) : List E :=
  [σ (.n osCaps) * gen ^ (4 * lv.capOff), σ (.n osFlags) * gen ^ lv.capOff,
    if lvl = c.yrLevel then 0 else σ (.n st.lamInv), σ (.n osCoefs) * gen ^ (2 * lv.foldsOff),
    if lvl = c.yrLevel then σ (.n st.hs) else σ (.n osHs) * gen ^ (lvl * hsStride),
    σ (.n osQpos) * gen ^ lv.posOff, σ (.n osQbp) * gen ^ lv.posOff,
    gen ^ (if lvl = 0 then lv.queries / 2 else lv.queries)]

/-- **The level's queries, honestly** (G:1695-1702): `opening_queries` at its honest arguments
(`osQArgsV`), returning `batched`. -/
theorem osQueries_complete {c : OsCfg} {lvl : ℕ} {lv : OsLv} {st : OsSt} (σ : Val) (hsf : st.Sf)
    (hok : ∀ C rd, H C rd → st.Ok σ) (batched : E) (hc4 : 4 * lv.capOff < u128Bound)
    (h3 : 2 * lv.foldsOff < u128Bound) (hpo : lv.posOff < u128Bound)
    (hh8 : lvl * hsStride < u128Bound)
    (hpq : (if lvl = 0 then lv.queries / 2 else lv.queries) < u128Bound)
    (hli : lvl ≠ c.yrLevel → st.lamInv < st.k) (hhs : lvl = c.yrLevel → st.hs < st.k)
    (hq : ∀ C rd, H C rd → C (osQueriesName c lvl lv) (osQArgsV σ c lvl lv st) [batched]) :
    BlkA H σ st.k (osQueries c lvl lv st).2.k (osQueries c lvl lv st).1 (fun σ' ↦
      OsStep σ σ' st (osQueries c lvl lv st).2 ∧
      (osQCallAt c lvl lv st).2.2.1.map σ' = osQArgsV σ c lvl lv st ∧
      (osQCallAt c lvl lv st).2.2.2.map σ' = [batched] ∧
      σ' (.n (osQueries c lvl lv st).2.batched) = batched) := by
  set k := st.k with hk
  set cp := osMatS c.plan osCaps (4 * lv.capOff) st with hcp
  set fl := osMatS c.plan osFlags lv.capOff cp.2.2 with hfl
  set li : List Stmt × ℕ × OsSt := if lvl = c.yrLevel then
    ([osCst fl.2.2.k (word 0 0)], fl.2.2.k, { fl.2.2 with k := fl.2.2.k + 1 })
    else ([], st.lamInv, fl.2.2) with hliD
  set cf := osMatS c.plan osCoefs (2 * lv.foldsOff) li.2.2 with hcf
  set hp : List Stmt × ℕ × OsSt := if lvl = c.yrLevel then ([], st.hs, cf.2.2)
    else osMatS c.plan osHs (lvl * hsStride) cf.2.2 with hhpD
  set qp := osMatS c.plan osQpos lv.posOff hp.2.2 with hqp
  set wp := osMatS c.plan osQbp lv.posOff qp.2.2 with hwp
  set g := wp.2.2.k with hg
  set pairs := if lvl = 0 then lv.queries / 2 else lv.queries with hpairs
  have k36 : 36 ≤ k := hsf.k
  have hco4 : lv.capOff < u128Bound := lt_of_le_of_lt (by omega) hc4
  have k1 : k ≤ cp.2.2.k := osMatS_k _ _ _ _
  have k2 : cp.2.2.k ≤ fl.2.2.k := osMatS_k _ _ _ _
  have k3 : fl.2.2.k ≤ li.2.2.k := by rw [hliD]; split_ifs <;> simp
  have k4 : li.2.2.k ≤ cf.2.2.k := osMatS_k _ _ _ _
  have k5 : cf.2.2.k ≤ hp.2.2.k := by
    rw [hhpD]; split_ifs
    · exact le_rfl
    · exact osMatS_k _ _ _ _
  have k6 : hp.2.2.k ≤ qp.2.2.k := osMatS_k _ _ _ _
  have k7 : qp.2.2.k ≤ g := osMatS_k _ _ _ _
  have pcp : cp.2.1 < cp.2.2.k := osMatS_ptr_lt _ _ _ _ (show 11 < k by omega)
  have pfl : fl.2.1 < fl.2.2.k := osMatS_ptr_lt _ _ _ _ (show 13 < cp.2.2.k by omega)
  have pli : li.2.1 < li.2.2.k := by
    rw [hliD]; split_ifs with hf
    · simp
    · have := hli hf; simp only; omega
  have pcf : cf.2.1 < cf.2.2.k := osMatS_ptr_lt _ _ _ _ (show 21 < li.2.2.k by omega)
  have php : hp.2.1 < hp.2.2.k := by
    rw [hhpD]; split_ifs with hf
    · have := hhs hf; simp only; omega
    · exact osMatS_ptr_lt _ _ _ _ (show 27 < cf.2.2.k by omega)
  have pqp : qp.2.1 < qp.2.2.k := osMatS_ptr_lt _ _ _ _ (show 33 < hp.2.2.k by omega)
  have pwp : wp.2.1 < g := osMatS_ptr_lt _ _ _ _ (show 35 < qp.2.2.k by omega)
  have mli : li.2.2.mats = fl.2.2.mats := by rw [hliD]; split_ifs <;> rfl
  have mb1 : MatsBelow cp.2.2.k cp.2.2.mats := osMatS_below hsf.below.mats (show 11 < k by omega)
  have mb2 : MatsBelow fl.2.2.k fl.2.2.mats := osMatS_below mb1 (show 13 < cp.2.2.k by omega)
  have mb3 : MatsBelow li.2.2.k li.2.2.mats := fun m hm ↦ by
    rw [mli] at hm; obtain ⟨a, b, d⟩ := mb2 m hm; exact ⟨by omega, by omega, by omega⟩
  have mb4 : MatsBelow cf.2.2.k cf.2.2.mats := osMatS_below mb3 (show 21 < li.2.2.k by omega)
  have mb5 : MatsBelow hp.2.2.k hp.2.2.mats := by
    rw [hhpD]; split_ifs
    · exact mb4
    · exact osMatS_below mb4 (show 27 < cf.2.2.k by omega)
  have mb6 : MatsBelow qp.2.2.k qp.2.2.mats := osMatS_below mb5 (show 33 < hp.2.2.k by omega)
  -- the cap and flags
  have b1 := osMatS_blkA (H := H) (P := c.plan) (base := osCaps) (off := 4 * lv.capOff) (s := st) σ
    (show 11 < k by omega) hsf.below.mats (fun C rd hH ↦ (hok C rd hH).mats) hc4
  have b2 := BlkA.seq (H := H) k1 k2 b1 (B := fl.1)
    (OutB := fun σ' ↦ σ' (.n fl.2.1) = σ (.n osFlags) * gen ^ lv.capOff ∧ MatsOk σ' fl.2.2.mats ∧
      MatsBelow fl.2.2.k fl.2.2.mats) fun σ1 ha1 ho1 ↦ by
      have h := osMatS_blkA (H := H) (P := c.plan) (base := osFlags) (off := lv.capOff) (s := cp.2.2) σ1
        (show 13 < cp.2.2.k by omega) mb1 (fun C rd hH ↦ (ho1 C rd hH).2.1) hco4
      rw [ha1 osFlags (by show 13 < k; omega)] at h
      exact h
  -- `1/λ`, or `0` at the final level
  have b3 := BlkA.seq (H := H) (show k ≤ fl.2.2.k by omega) k3 b2 (B := li.1)
    (OutB := fun σ' ↦ σ' (.n li.2.1) = (if lvl = c.yrLevel then 0 else σ (.n st.lamInv)))
    fun σ1 ha1 _ ↦ by
      rw [hliD]
      split_ifs with hf
      · dsimp only
        refine ⟨lstF fl.2.2.k [word 0 0], fun C rd hH σ' _ hr ↦ ?_⟩
        have v0 := lstF_at hr (by simp) 0 (by simp)
        simp only [List.getD_cons_zero, Nat.add_zero] at v0
        refine ⟨?_, show σ' (.n fl.2.2.k) = 0 by rw [v0, word_zero]⟩
        simp only [allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_const, osCst, v0]
      · dsimp only
        exact BlkA.nil fun σ' ha ↦ by
          have := hli hf
          rw [ha _ (show st.lamInv < fl.2.2.k by omega), ha1 _ this]
  -- the round coefficients
  have b4 := BlkA.seq (H := H) (show k ≤ li.2.2.k by omega) k4 b3 (B := cf.1)
    (OutB := fun σ' ↦ σ' (.n cf.2.1) = σ (.n osCoefs) * gen ^ (2 * lv.foldsOff) ∧
      MatsOk σ' cf.2.2.mats ∧ MatsBelow cf.2.2.k cf.2.2.mats) fun σ1 ha1 ho1 ↦ by
      have h := osMatS_blkA (H := H) (P := c.plan) (base := osCoefs) (off := 2 * lv.foldsOff)
        (s := li.2.2) σ1 (show 21 < li.2.2.k by omega) mb3
        (fun C rd hH ↦ by rw [mli]; exact (ho1 C rd hH).1.2.2.1) h3
      rw [ha1 osCoefs (by show 21 < k; omega)] at h
      exact h
  -- the high part
  have b5 := BlkA.seq (H := H) (show k ≤ cf.2.2.k by omega) k5 b4 (B := hp.1)
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
          (s := cf.2.2) σ1 (show 27 < cf.2.2.k by omega) mb4 (fun C rd hH ↦ (ho1 C rd hH).2.2.1) hh8
        rw [ha1 osHs (by show 27 < k; omega)] at h
        exact h.mono fun σ' h' ↦ ⟨h'.1, h'.2.1⟩
  -- the positions and windows
  have b6 := BlkA.seq (H := H) (show k ≤ hp.2.2.k by omega) k6 b5 (B := qp.1)
    (OutB := fun σ' ↦ σ' (.n qp.2.1) = σ (.n osQpos) * gen ^ lv.posOff ∧ MatsOk σ' qp.2.2.mats ∧
      MatsBelow qp.2.2.k qp.2.2.mats) fun σ1 ha1 ho1 ↦ by
      have h := osMatS_blkA (H := H) (P := c.plan) (base := osQpos) (off := lv.posOff) (s := hp.2.2) σ1
        (show 33 < hp.2.2.k by omega) mb5 (fun C rd hH ↦ (ho1 C rd hH).2.2) hpo
      rw [ha1 osQpos (by show 33 < k; omega)] at h
      exact h
  have b7 := BlkA.seq (H := H) (show k ≤ qp.2.2.k by omega) k7 b6 (B := wp.1)
    (OutB := fun σ' ↦ σ' (.n wp.2.1) = σ (.n osQbp) * gen ^ lv.posOff ∧ MatsOk σ' wp.2.2.mats ∧
      MatsBelow wp.2.2.k wp.2.2.mats) fun σ1 ha1 ho1 ↦ by
      have h := osMatS_blkA (H := H) (P := c.plan) (base := osQbp) (off := lv.posOff) (s := qp.2.2) σ1
        (show 35 < qp.2.2.k by omega) mb6 (fun C rd hH ↦ (ho1 C rd hH).2.2.1) hpo
      rw [ha1 osQbp (by show 35 < k; omega)] at h
      exact h
  -- the call
  have b8 := BlkA.seq (H := H) (show k ≤ g by omega) (show g ≤ g + 2 by omega) b7
    (B := [osCst g (gw pairs), .call (osQueriesName c lvl lv)
      ([cp.2.1, fl.2.1, li.2.1, cf.2.1, hp.2.1, qp.2.1, wp.2.1, g].map V.n) [.n (g + 1)]])
    (OutB := fun σ' ↦ ([cp.2.1, fl.2.1, li.2.1, cf.2.1, hp.2.1, qp.2.1, wp.2.1, g].map V.n).map σ' =
      osQArgsV σ c lvl lv st ∧ σ' (.n (g + 1)) = batched) fun σ1 ha1 ho1 ↦ by
      refine ⟨lstF g [gw pairs, batched], fun C rd hH σ' ha hr ↦ ?_⟩
      have v0 := lstF_at hr (by simp) 0 (by simp)
      have v1 := lstF_at hr (by simp) 1 (by simp)
      simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at v0 v1
      obtain ⟨⟨⟨⟨⟨⟨⟨ecp, -⟩, efl, -⟩, eli⟩, ecf, -⟩, ehp, -⟩, eqp, -⟩, ewp, -⟩ := ho1 C rd hH
      have eargs : ([cp.2.1, fl.2.1, li.2.1, cf.2.1, hp.2.1, qp.2.1, wp.2.1, g].map V.n).map σ' =
          osQArgsV σ c lvl lv st := by
        simp only [List.map_cons, List.map_nil]
        rw [ha _ (show cp.2.1 < g by omega), ha _ (show fl.2.1 < g by omega),
          ha _ (show li.2.1 < g by omega), ha _ (show cf.2.1 < g by omega),
          ha _ (show hp.2.1 < g by omega), ha _ (show qp.2.1 < g by omega), ha _ pwp, v0, ecp, efl,
          eli, ecf, ehp, eqp, ewp, gw_eq hpq]
        rfl
      refine ⟨?_, eargs, v1⟩
      simp only [allOk_cons, allOk_nil, and_true, stmtOk_atom, stmtOk_call, holds_const, osCst, v0]
      refine ⟨trivial, ?_⟩
      rw [eargs]
      simp only [List.map_cons, List.map_nil, v1]
      exact hq C rd hH
  have hfld : (osQueries c lvl lv st).2.fs = st.fs ∧ (osQueries c lvl lv st).2.cb = st.cb ∧
      (osQueries c lvl lv st).2.co = st.co ∧ (osQueries c lvl lv st).2.claim = st.claim ∧
      (osQueries c lvl lv st).2.pad = st.pad := by
    unfold osQueries; dsimp only; split_ifs <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  have ek : (osQueries c lvl lv st).2.k = g + 2 := rfl
  have em : (osQueries c lvl lv st).2.mats = wp.2.2.mats := rfl
  have eb : (osQueries c lvl lv st).2.batched = g + 1 := rfl
  have el : (osQueries c lvl lv st).1 = cp.1 ++ fl.1 ++ li.1 ++ cf.1 ++ hp.1 ++ qp.1 ++ wp.1 ++
      [osCst g (gw pairs), .call (osQueriesName c lvl lv)
        ([cp.2.1, fl.2.1, li.2.1, cf.2.1, hp.2.1, qp.2.1, wp.2.1, g].map V.n) [.n (g + 1)]] := rfl
  have eq1 : (osQCallAt c lvl lv st).2.2.1 =
      [cp.2.1, fl.2.1, li.2.1, cf.2.1, hp.2.1, qp.2.1, wp.2.1, g].map V.n := rfl
  have eq2 : (osQCallAt c lvl lv st).2.2.2 = [.n (g + 1)] := rfl
  rw [ek, el, eq1, eq2, eb]
  refine BlkA.monoH b8.agree fun C rd hH σ' _ ⟨⟨ho7, eargs, ebat⟩, hag⟩ ↦ ?_
  obtain ⟨-, -, hm, hb⟩ := ho7
  have hok' := hok C rd hH
  obtain ⟨efs, ecb, eco, ecl, epad⟩ := hfld
  refine ⟨osStep_of hsf hok' hag (by rw [ek]; omega) (by rw [efs]; exact hsf.fs) (fun f hf ↦ ?_) ?_ ?_
    (by rw [eco]; exact hsf.co) epad (by rw [em]; exact hm) ?_, eargs, by simp [ebat], ebat⟩
  · rw [efs] at hf; have := hsf.below.fs f hf; rw [ek]; omega
  · rw [ecb, ek]; have := hsf.below.cb; omega
  · rw [ecl, ek]; have := hsf.below.claim; omega
  · rw [em, ek]; intro m hm'; obtain ⟨a, b, d⟩ := hb m hm'
    exact ⟨by omega, by omega, by omega⟩

/-! ## The glue -/

theorem osPowSteps_res_lt (x : ℕ) : ∀ (ds : List Bool) (acc k : ℕ), acc < k →
    (osPowSteps x ds acc k).2 < k + powLen ds
  | [], _, _, h => by simp [osPowSteps, powLen]; omega
  | true :: ds, acc, k, _ => by
    have := osPowSteps_res_lt x ds (k + 1) (k + 2) (by omega)
    simp only [osPowSteps, ↓reduceIte, powLen_true]
    omega
  | false :: ds, acc, k, _ => by
    have := osPowSteps_res_lt x ds k (k + 1) (by omega)
    simp only [osPowSteps, Bool.false_eq_true, ↓reduceIte, powLen_false]
    omega

/-- The glue's first values: `λ·y0`, the claim plus it, `λ²`. -/
def glueVals (cl lam y0 : E) : List E :=
  [lam * y0, cl + lam * y0, lam * lam]

/-- The glue's last values: `λ²·λ^Q`, times the batch, the new claim. -/
def glueEnd (cl lam y0 lq b : E) : List E :=
  [lam * lam * lq, lam * lam * lq * b, cl + lam * y0 + lam * lam * lq * b]

/-- **A non-final level's claims glued, honestly** (G:1684-1694): `λ` into `ood_scalars`,
`λ²·λ^Q` into `level_betas`, `1/λ` into `level_mus`; the new claim the old plus
`λ·y0 + λ²·λ^Q·batched`. -/
theorem osGlue_complete {lvl : ℕ} {lv : OsLv} {st : OsSt} (σ : Val) (hsf : st.Sf)
    (hok : ∀ C rd, H C rd → st.Ok σ) (hlam : st.lam < st.k) (hy0 : st.ys.getD 0 0 < st.k)
    (hbat : st.batched < st.k) (hli : st.lamInv < st.k)
    (hpw : digitsVal (osPowDigits lv.queries) 1 = lv.queries)
    (hmem : ∀ C rd, H C rd →
      LoadHolds rd (σ (.n osOodSc)) (lvl + 1) (σ (.n st.lam)) ∧
      LoadHolds rd (σ (.n osBetas)) lvl
        (σ (.n st.lam) * σ (.n st.lam) * σ (.n st.lam) ^ lv.queries) ∧
      LoadHolds rd (σ (.n osMus)) lvl (σ (.n st.lamInv))) :
    BlkA H σ st.k (osGlue lvl lv st).2.k (osGlue lvl lv st).1 (fun σ' ↦
      OsStep σ σ' st (osGlue lvl lv st).2 ∧
      σ' (.n (osGlue lvl lv st).2.claim) = σ (.n st.claim) + σ (.n st.lam) * σ (.n (st.ys.getD 0 0)) +
        σ (.n st.lam) * σ (.n st.lam) * σ (.n st.lam) ^ lv.queries * σ (.n st.batched)) := by
  set k := st.k with hk
  set lam := st.lam with hlamD
  set y0 := st.ys.getD 0 0 with hy0D
  set ds := osPowDigits lv.queries with hds
  set pw := osPowSteps lam ds lam (k + 3) with hpwD
  set k' := k + 3 + powLen ds with hk'
  set L := σ (.n lam) with hL
  set Y0 := σ (.n y0) with hY0
  set cl := σ (.n st.claim) with hcl
  set B := σ (.n st.batched) with hB
  have k36 : 36 ≤ k := hsf.k
  have hclk : st.claim < k := hsf.below.claim
  have hres : pw.2 < k' := osPowSteps_res_lt lam ds lam (k + 3) (by omega)
  have hLQ : powRes L ds L = L ^ lv.queries := by
    rw [← hpw, ← powRes_eq L ds 1, pow_one]
  -- the first values and the store
  have b1 : BlkA H σ k (k + 3) [osLd lam osOodSc (lvl + 1), osMul k lam y0,
      osAdd (k + 1) st.claim k, osMul (k + 2) lam lam]
      (fun σ' ↦ ∀ j < 3, σ' (.n (k + j)) = (glueVals cl L Y0).getD j 0) := by
    refine ⟨lstF k (glueVals cl L Y0), fun C rd hH σ' ha hr ↦ ?_⟩
    have v : ∀ j < 3, σ' (.n (k + j)) = (glueVals cl L Y0).getD j 0 := fun j hj ↦
      lstF_at hr (by simp [glueVals]) j (by simp [glueVals]; omega)
    refine ⟨?_, v⟩
    have v0 := v 0 (by omega)
    have v1 := v 1 (by omega)
    have v2 := v 2 (by omega)
    simp only [glueVals, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at v0 v1 v2
    obtain ⟨l0, -, -⟩ := hmem C rd hH
    simp only [allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_load, holds_mul, holds_add, osLd,
      osMul, osAdd, v0, v1, v2, ha _ hlam, ha _ hy0, ha _ hclk,
      ha _ (show 31 < k by omega), and_true]
    exact ⟨l0, by and_intros <;> rfl⟩
  -- `λ^Q`
  have b2 := BlkA.seq (H := H) (show k ≤ k + 3 by omega) (show k + 3 ≤ k' by omega) b1 (B := pw.1)
    (OutB := fun σ' ↦ σ' (.n pw.2) = L ^ lv.queries) fun σ1 ha1 _ ↦ by
      refine ⟨powVals L ds L (k + 3), fun C rd hH σ' ha hr ↦ ?_⟩
      have h := powSteps_ok (C := C) (rd := rd) lam ds lam (k + 3) L σ' (by omega) (by omega)
        (by rw [ha _ (by omega), ha1 _ hlam]) fun i h1 h2 ↦ by
          rw [hr i h1 (by omega), ha _ (show lam < k + 3 by omega), ha1 _ hlam]
      refine ⟨h.1, ?_⟩
      show σ' (.n (osPowSteps lam ds lam (k + 3)).2) = _
      rw [h.2, ha _ (show lam < k + 3 by omega), ha1 _ hlam, hLQ]
  -- the batch glued, `λ²·λ^Q` and `1/λ` stored
  have b3 := BlkA.seq (H := H) (show k ≤ k' by omega) (show k' ≤ k' + 3 by omega) b2
    (B := [osMul k' (k + 2) pw.2, osMul (k' + 1) k' st.batched, osAdd (k' + 2) (k + 1) (k' + 1),
      osLd k' osBetas lvl, osLd st.lamInv osMus lvl])
    (OutB := fun σ' ↦ σ' (.n (k' + 2)) = cl + L * Y0 + L * L * L ^ lv.queries * B)
    fun σ1 ha1 ho1 ↦ by
      refine ⟨lstF k' (glueEnd cl L Y0 (L ^ lv.queries) B), fun C rd hH σ' ha hr ↦ ?_⟩
      have v0 := lstF_at hr (by simp [glueEnd]) 0 (by simp [glueEnd])
      have v1 := lstF_at hr (by simp [glueEnd]) 1 (by simp [glueEnd])
      have v2 := lstF_at hr (by simp [glueEnd]) 2 (by simp [glueEnd])
      simp only [glueEnd, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at v0 v1 v2
      obtain ⟨w1, w2⟩ := ho1 C rd hH
      have u1 : σ' (.n (k + 1)) = cl + L * Y0 := by
        rw [ha _ (by omega), w1 1 (by omega)]; rfl
      have u2 : σ' (.n (k + 2)) = L * L := by rw [ha _ (by omega), w1 2 (by omega)]; rfl
      have upw : σ' (.n pw.2) = L ^ lv.queries := by rw [ha _ hres, w2]
      obtain ⟨-, l2, l3⟩ := hmem C rd hH
      refine ⟨?_, v2⟩
      simp only [allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_load, holds_mul, holds_add, osLd,
        osMul, osAdd, v0, v1, v2, u1, u2, upw, ha _ (show st.batched < k' by omega),
        ha1 _ hbat, ha _ (show st.lamInv < k' by omega), ha1 _ hli, ha _ (show 23 < k' by omega),
        ha1 _ (show 23 < k by omega), ha _ (show 25 < k' by omega), ha1 _ (show 25 < k by omega)]
      refine ⟨?_, ?_, ?_, l2, l3⟩ <;> trivial
  have ek : (osGlue lvl lv st).2.k = k' + 3 := rfl
  have ecl : (osGlue lvl lv st).2.claim = k' + 2 := rfl
  have el : (osGlue lvl lv st).1 = [osLd lam osOodSc (lvl + 1), osMul k lam y0,
      osAdd (k + 1) st.claim k, osMul (k + 2) lam lam] ++ pw.1 ++
      [osMul k' (k + 2) pw.2, osMul (k' + 1) k' st.batched, osAdd (k' + 2) (k + 1) (k' + 1),
        osLd k' osBetas lvl, osLd st.lamInv osMus lvl] := rfl
  rw [ek, el, ecl]
  refine BlkA.monoH b3.agree fun C rd hH σ' _ ⟨⟨_, ev⟩, hag⟩ ↦ ⟨?_, ev⟩
  have hok' := hok C rd hH
  refine osStep_of hsf hok' hag (show k ≤ k' + 3 by omega) hsf.fs (fun f hf ↦ ?_) ?_ ?_ hsf.co rfl
    (matsOk_agree hok'.mats hsf.below.mats fun i hi ↦ hag i hi) ?_
  · have := hsf.below.fs f hf; show f < k' + 3; omega
  · have := hsf.below.cb; show st.cb < k' + 3; omega
  · show k' + 2 < k' + 3; omega
  · intro m hm'; obtain ⟨a, b, d⟩ := hsf.below.mats m hm'
    exact ⟨by show m.out < k' + 3; omega, by show m.src < k' + 3; omega,
      by show m.base < k' + 3; omega⟩

end
end LeanVM.Guest.B1.Whir
