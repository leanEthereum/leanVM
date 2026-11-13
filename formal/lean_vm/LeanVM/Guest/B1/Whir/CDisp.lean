/-
  LeanVM.Guest.B1.Whir.CDisp

  A dispatch on the rate's selector, honestly: the rate's arm called at fixed returns; the
  positions block (`osPositions`), its slots materialized and its dispatch into
  `level_positions`.
-/

module

public import LeanVM.Guest.B1.Whir.CAtoms
public import LeanVM.Guest.B1.Whir.RateCfg
public import LeanVM.Guest.B1.Whir.CLvCommit

/-!
# The rate's dispatches, honestly

* `stmtOk_dispatch_of`: a dispatch at the selector `g^i`, `i` below its arms' count, holds when its
  `i`-th arm's relation does.
* `rateDisp_blk`: a dispatch on the rate's selector (`LvRate`) over `(c.lvAt lvl).map f`, its
  returns listed from `r`, holds at those returns when `C (f lv)` does.
* `osPositions_complete`: the positions block: the level's slots of `query_positions` and
  `query_win_ptrs` materialized, the dispatch into `level_positions` at its returns, the sponge's
  capacity the returns.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {H : CallRel → Reader → Prop}

/-- **A dispatch at the selector `g^i`** holds when its `i`-th arm's relation does. -/
theorem stmtOk_dispatch_of {C : CallRel} {rd : Reader} {σ : Val} {x : V} {fs : List String}
    {args rets : List V} {i : ℕ} (hx : σ x = ofK (addressOfIndex i)) (hi : i < fs.length)
    (hc : C (fs.getD i "") (args.map σ) (rets.map σ)) :
    StmtOk C rd σ (.dispatch x fs args rets) :=
  ⟨i, hi, hx, by rwa [List.getD_eq_getElem _ _ hi] at hc⟩

/-- **A dispatch on the rate's selector at its returns**: the returns listed from `r`. -/
theorem rateDisp_blk {σ : Val} {c : OsCfg} {lvl : ℕ} {lv : OsLv} {r n : ℕ} (f : OsLv → String)
    {args : List ℕ} (rets : List E) (hl : rets.length = n) (hargs : ∀ i ∈ args, i < r) (h0 : 0 < r)
    (hrate : ∀ C rd, H C rd → LvRate σ c lvl lv)
    (hC : ∀ C rd, H C rd → C (f lv) (args.map fun i ↦ σ (.n i)) rets) :
    BlkA H σ r (r + n) [.dispatch (.n osRate) ((c.lvAt lvl).map f) (args.map V.n) (osRun r n)]
      (fun σ' ↦ ∀ j < n, σ' (.n (r + j)) = rets.getD j 0) := by
  refine ⟨lstF r rets, fun C rd hH σ' ha hr ↦ ?_⟩
  have hv : ∀ j < n, σ' (.n (r + j)) = rets.getD j 0 := fun j hj ↦
    lstF_at hr (by omega) j (by omega)
  refine ⟨?_, hv⟩
  simp only [allOk_cons, allOk_nil, and_true]
  obtain ⟨ri, hri, hx, hlen, hlv⟩ := hrate C rd hH
  have e1 : (args.map V.n).map σ' = args.map fun i ↦ σ (.n i) := by
    simp only [List.map_map]
    exact List.map_congr_left fun i hi ↦ ha i (hargs i hi)
  have e2 : (osRun r n).map σ' = rets := by
    rw [osRun_map]
    refine List.ext_getElem (by simp [hl]) fun j h1 h2 ↦ ?_
    simp only [List.length_map, List.length_range] at h1
    simp only [List.getElem_map, List.getElem_range]
    rw [hv j h1, List.getD_eq_getElem _ _ h2]
  have hx' : σ' (.n osRate) = ofK (addressOfIndex ri) := by rw [ha 0 h0]; exact hx
  have hlt : ri < ((c.lvAt lvl).map f).length := by simp [hlen, hri]
  refine stmtOk_dispatch_of hx' hlt ?_
  rw [List.getD_eq_getElem _ _ hlt, List.getElem_map,
    ← List.getD_eq_getElem _ default (by simpa using hlt), hlv, e1, e2]
  exact hC C rd hH

/-- The capacity after `n` squeezes from `cap`. -/
def sqCapD (cap : List E) (n : ℕ) : List E := ((⟨cap, []⟩ : Fs).squeezeN n).2.cap

theorem sqCapD_length {cap : List E} (h : cap.length = 5) (n : ℕ) : (sqCapD cap n).length = 5 :=
  squeezeN_cap_length n _ h

/-- The arguments and returns of `osPositions c lvl lv s`'s dispatch into `level_positions`. -/
def osPosCall (c : OsCfg) (lv : OsLv) (s : OsSt) : List V × List V :=
  let qp := osMatS c.plan osQpos lv.posOff s
  let wp := osMatS c.plan osQbp lv.posOff qp.2.2
  ((s.word0 :: s.fs ++ [qp.2.1, wp.2.1, osTabs]).map V.n, osRun wp.2.2.k 5)

/-- **The positions, honestly**: the level's slots of `query_positions` and `query_win_ptrs`
materialized, the dispatch into `level_positions` at its returns `capR`, the sponge's capacity
`capR`. -/
theorem osPositions_complete {c : OsCfg} {lvl : ℕ} {lv : OsLv} {st : OsSt} (σ : Val) (hsf : st.Sf)
    (hok : ∀ C rd, H C rd → st.Ok σ) (hw0 : st.word0 < st.k) (hpo : lv.posOff < u128Bound)
    (capR : List E) (hcl : capR.length = 5) (hrate : ∀ C rd, H C rd → LvRate σ c lvl lv)
    (hC : ∀ C rd, H C rd → C (osPositionsName lv)
      (σ (.n st.word0) :: st.fsv σ ++ [σ (.n osQpos) * gen ^ lv.posOff, σ (.n osQbp) * gen ^ lv.posOff,
        σ (.n osTabs)]) capR) :
    BlkA H σ st.k (osPositions c lvl lv st).2.k (osPositions c lvl lv st).1 (fun σ' ↦
      OsStep σ σ' st (osPositions c lvl lv st).2 ∧
      (osPositions c lvl lv st).2.F σ' = ⟨capR, []⟩ ∧
      (osPositions c lvl lv st).2.cur σ' = st.cur σ ∧
      (osPositions c lvl lv st).2.claim = st.claim ∧ (osPositions c lvl lv st).2.pad = st.pad ∧
      (osPositions c lvl lv st).2.co = st.co ∧ (osPositions c lvl lv st).2.cb = st.cb ∧
      (osPosCall c lv st).1.map σ' = σ (.n st.word0) :: st.fsv σ ++
        [σ (.n osQpos) * gen ^ lv.posOff, σ (.n osQbp) * gen ^ lv.posOff, σ (.n osTabs)] ∧
      (osPosCall c lv st).2.map σ' = capR) := by
  set k := st.k with hk
  set qp := osMatS c.plan osQpos lv.posOff st with hqp
  set wp := osMatS c.plan osQbp lv.posOff qp.2.2 with hwp
  set l := wp.2.2.k with hl
  have k33 : 33 ≤ k := hsf.k
  have kq : k ≤ qp.2.2.k := osMatS_k c.plan osQpos lv.posOff st
  have kw : qp.2.2.k ≤ l := osMatS_k c.plan osQbp lv.posOff qp.2.2
  have pqp : qp.2.1 < qp.2.2.k := osMatS_ptr_lt _ _ _ _ (show 30 < k by omega)
  have pwp : wp.2.1 < l := osMatS_ptr_lt _ _ _ _ (show 32 < qp.2.2.k by omega)
  have hfb : ∀ f ∈ st.fs, f < k := hsf.below.fs
  -- the pointers
  have b2 := osMatS_blkA (H := H) (P := c.plan) (base := osQpos) (off := lv.posOff) (s := st) σ
    (show 30 < k by omega) hsf.below.mats (fun C rd hH ↦ (hok C rd hH).mats) hpo
  have b3 := BlkA.seq (H := H) kq kw b2 (B := wp.1)
    (OutB := fun σ' ↦ σ' (.n wp.2.1) = σ (.n osQbp) * gen ^ lv.posOff ∧ MatsOk σ' wp.2.2.mats ∧
      MatsBelow wp.2.2.k wp.2.2.mats) fun σ1 ha1 ho1 ↦ by
      have h := osMatS_blkA (H := H) (P := c.plan) (base := osQbp) (off := lv.posOff) (s := qp.2.2) σ1
        (show 32 < qp.2.2.k by omega) (osMatS_below hsf.below.mats (show 30 < k by omega))
        (fun C rd hH ↦ (ho1 C rd hH).2.1) hpo
      rw [ha1 osQbp (by show 32 < k; omega)] at h
      exact h
  -- the dispatch
  have hargsV : ∀ σ1, AgreeBelow k σ σ1 → (∀ C rd, H C rd →
      σ1 (.n wp.2.1) = σ (.n osQbp) * gen ^ lv.posOff ∧ MatsOk σ1 wp.2.2.mats ∧
        MatsBelow wp.2.2.k wp.2.2.mats) → (∀ C rd, H C rd → (σ1 (.n qp.2.1) =
        σ (.n osQpos) * gen ^ lv.posOff ∧ MatsOk σ1 qp.2.2.mats ∧ MatsBelow qp.2.2.k qp.2.2.mats)) →
      ∀ C rd, H C rd → (st.word0 :: st.fs ++ [qp.2.1, wp.2.1, osTabs]).map (fun i ↦ σ1 (.n i)) =
        σ (.n st.word0) :: st.fsv σ ++
          [σ (.n osQpos) * gen ^ lv.posOff, σ (.n osQbp) * gen ^ lv.posOff, σ (.n osTabs)] := by
    intro σ1 ha1 hw hq C0 rd0 hH0
    have v : ∀ f ∈ st.fs, σ1 (.n f) = σ (.n f) := fun f hf' ↦ ha1 _ (hfb f hf')
    have ef : st.fs.map (fun i ↦ σ1 (.n i)) = st.fsv σ := List.map_congr_left fun f hf ↦ v f hf
    simp only [List.cons_append, List.map_cons, List.map_append, List.map_nil, ef]
    rw [(hq C0 rd0 hH0).1, (hw C0 rd0 hH0).1, ha1 _ hw0, ha1 _ (show 10 < k by omega)]
  have b4 := BlkA.seq (H := H) (le_trans kq kw) (show l ≤ l + 5 by omega) b3
    (B := [.dispatch (.n osRate) ((c.lvAt lvl).map osPositionsName)
      ((st.word0 :: st.fs ++ [qp.2.1, wp.2.1, osTabs]).map V.n) (osRun l 5)])
    (OutB := fun σ' ↦ (st.word0 :: st.fs ++ [qp.2.1, wp.2.1, osTabs]).map (fun i ↦ σ' (.n i)) =
        σ (.n st.word0) :: st.fsv σ ++
          [σ (.n osQpos) * gen ^ lv.posOff, σ (.n osQbp) * gen ^ lv.posOff, σ (.n osTabs)] ∧
      ∀ j < 5, σ' (.n (l + j)) = capR.getD j 0) fun σ1 ha1 ho1 ↦ by
      have hargs : ∀ i ∈ st.word0 :: st.fs ++ [qp.2.1, wp.2.1, osTabs], i < l := fun i hi ↦ by
        simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil,
          or_false] at hi
        rcases hi with rfl | hi | rfl | rfl | rfl
        · omega
        · have := hfb i hi; omega
        · omega
        · omega
        · show 10 < l; omega
      have h := rateDisp_blk (H := H) (σ := σ1) (c := c) (lvl := lvl) (lv := lv) (r := l) (n := 5)
        osPositionsName (args := st.word0 :: st.fs ++ [qp.2.1, wp.2.1, osTabs]) capR hcl hargs
        (show 0 < l by omega)
        (fun C rd hH ↦ by
          obtain ⟨ri, hri, hx, hlen, hlv⟩ := hrate C rd hH
          exact ⟨ri, hri, by rw [ha1 _ (show 0 < k by omega)]; exact hx, hlen, hlv⟩)
        (fun C rd hH ↦ by
          rw [hargsV σ1 ha1 (fun C rd hH ↦ (ho1 C rd hH).2) (fun C rd hH ↦ (ho1 C rd hH).1) C rd hH]
          exact hC C rd hH)
      refine BlkA.monoH h fun C rd hH σ' ha hv ↦ ⟨?_, hv⟩
      rw [← hargsV σ1 ha1 (fun C rd hH ↦ (ho1 C rd hH).2) (fun C rd hH ↦ (ho1 C rd hH).1) C rd hH]
      exact List.map_congr_left fun i hi ↦ ha _ (hargs i hi)
  have ek : (osPositions c lvl lv st).2.k = l + 5 := rfl
  rw [ek]
  refine BlkA.congr (BlkA.monoH b4.agree fun C rd hH σ' ha ⟨ho, hag⟩ ↦ ?_) (by
    simp only [osPositions, List.append_assoc]; rfl)
  obtain ⟨⟨-, -, hmw, hbw⟩, eargs, e4⟩ := ho
  have hok' := hok C rd hH
  refine ⟨⟨⟨⟨rfl, ⟨?_, ?_, ?_, ?_⟩, hsf.co, fun p hp ↦ by have := hsf.padB p hp; omega,
    by omega⟩, hmw, ?_⟩, by omega, hag⟩, ?_, ?_, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro f hf
    have hf' : f ∈ [l, l + 1, l + 2, l + 3, l + 4] := hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf'
    rcases hf' with rfl | rfl | rfl | rfl | rfl <;> omega
  · show st.cb < l + 5; have := hsf.below.cb; omega
  · show st.claim < l + 5; have := hsf.below.claim; omega
  · intro m hm; obtain ⟨a, b, d⟩ := hbw m hm
    exact ⟨by have : m.out < l := a; omega, by have : m.src < l := b; omega,
      by have : m.base < l := d; omega⟩
  · intro p hp
    have hb' := hsf.padB p hp
    obtain ⟨z1, z2, z3, z4⟩ := hok'.pad p hp
    rw [hag _ (by omega), hag _ (by omega), hag _ (by omega), hag _ (by omega)]
    exact ⟨z1, z2, z3, z4⟩
  · show (⟨[l, l + 1, l + 2, l + 3, l + 4].map (fun i ↦ σ' (.n i)), []⟩ : Fs) = _
    rw [five_getD hcl]
    simp only [List.map_cons, List.map_nil]
    rw [show l = l + 0 from rfl, e4 0 (by omega), e4 1 (by omega), e4 2 (by omega), e4 3 (by omega),
      e4 4 (by omega)]
  · show σ' (.n st.cb) * gen ^ st.co = σ (.n st.cb) * gen ^ st.co
    rw [hag _ hsf.below.cb]
  · show ((st.word0 :: st.fs ++ [qp.2.1, wp.2.1, osTabs]).map V.n).map σ' = _
    rw [List.map_map]; exact eargs
  · show (osRun l 5).map σ' = capR
    rw [osRun_map, five_getD hcl, show List.range 5 = [0, 1, 2, 3, 4] from rfl]
    simp only [List.map_cons, List.map_nil]
    rw [e4 0 (by omega), e4 1 (by omega), e4 2 (by omega), e4 3 (by omega), e4 4 (by omega)]

end
end LeanVM.Guest.B1.Whir
