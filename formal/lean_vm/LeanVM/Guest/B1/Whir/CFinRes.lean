/-
  LeanVM.Guest.B1.Whir.CFinRes

  A non-final level's residual in the finish, honestly: its pointers materialized, `λ⁻¹` read, the
  dispatch into `level_residual` on the rate's selector, its sums into `inner_chain`.
-/

module

public import LeanVM.Guest.B1.Whir.CFinRs
public import LeanVM.Guest.B1.Whir.CLevel
public import LeanVM.Guest.B1.Place.OsProtoSpec

/-!
# The residuals, honestly

`osMatP_blkA`: a fixed buffer's shifted pointer, materialized from the materializations `mats`.
`ResMemD`: what memory holds for a level's residual: `λ⁻¹` in `level_lam_invs`, the inner chain's entries
before and after, the scale, `β` and the product of the coordinates, at the dispatch's returns
`P`, `Q`. `osResidual_complete`: one level; `osResiduals_complete`: the levels `lvl ..`, each
dispatch's arguments and returns (`osResCallsL`).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Guest.Memory LeanVM.Protocol.Verifier

@[expose] public section

variable {H : CallRel → Reader → Prop}

/-- **A fixed buffer's shifted pointer, materialized.** -/
theorem osMatP_blkA {P : List (ℕ × ℕ × ℕ)} {mats : List OsMat} {base off k : ℕ} (σ : Val)
    (hbase : base < k) (hmb : MatsBelow k mats) (hm : ∀ C rd, H C rd → MatsOk σ mats)
    (hoff : off < u128Bound) :
    BlkA H σ k (osMatP P mats base off k).2.2 (osMatP P mats base off k).1
      (fun σ' ↦ σ' (.n (osMatP P mats base off k).2.1) = σ (.n base) * gen ^ off ∧
        MatsOk σ' (osMatsAfter P mats base off k) ∧
        MatsBelow (osMatP P mats base off k).2.2 (osMatsAfter P mats base off k)) :=
  osMatS_blkA (s := { (default : OsSt) with k := k, mats := mats }) σ hbase hmb hm hoff

theorem osMatP_k (P : List (ℕ × ℕ × ℕ)) (mats : List OsMat) (base off k : ℕ) :
    k ≤ (osMatP P mats base off k).2.2 :=
  osMatS_k P base off { (default : OsSt) with k := k, mats := mats }

theorem osMatP_lt (P : List (ℕ × ℕ × ℕ)) (mats : List OsMat) (base off k : ℕ) (hb : base < k) :
    (osMatP P mats base off k).2.1 < (osMatP P mats base off k).2.2 :=
  osMatS_ptr_lt P base off { (default : OsSt) with k := k, mats := mats } hb

theorem osMatP_below {P : List (ℕ × ℕ × ℕ)} {mats : List OsMat} {base off k : ℕ}
    (hmb : MatsBelow k mats) (hbase : base < k) :
    MatsBelow (osMatP P mats base off k).2.2 (osMatsAfter P mats base off k) :=
  osMatS_below (s := { (default : OsSt) with k := k, mats := mats }) hmb hbase

theorem osMatP_allocs (P : List (ℕ × ℕ × ℕ)) (mats : List OsMat) (base off k : ℕ) :
    (osMatP P mats base off k).1.filterMap Stmt.allocSz = [] := by
  unfold osMatP; split_ifs <;> rfl

/-- What memory holds for a level's residual, at the dispatches' returns `P`, `Q` and `SL`. -/
structure ResMemD (rd : Reader) (σ : Val) (lvl ich ls la : ℕ) (mu i0 i1 s b a P Q lam SL : E) :
    Prop where
  mus : LoadHolds rd (σ (.n osMus)) lvl mu
  li0 : LoadHolds rd (σ (.n ich)) (2 * lvl) i0
  li1 : LoadHolds rd (σ (.n ich)) (2 * lvl + 1) i1
  lsc : LoadHolds rd (σ (.n ls)) lvl s
  lbe : LoadHolds rd (σ (.n osBetas)) lvl b
  laf : LoadHolds rd (σ (.n la)) lvl a
  lam : LoadHolds rd (σ (.n osOodSc)) (lvl + 1) lam
  st0 : LoadHolds rd (σ (.n ich)) (2 * lvl + 2) (i0 + s * P + SL)
  st1 : LoadHolds rd (σ (.n ich)) (2 * lvl + 3) (i1 + b * a * Q)

theorem ResMemD.agree {rd : Reader} {σ σ' : Val} {lvl ich ls la k : ℕ} {mu i0 i1 s b a P Q lam SL : E}
    (h : ResMemD rd σ lvl ich ls la mu i0 i1 s b a P Q lam SL) (hich : ich < k) (hls : ls < k)
    (hla : la < k) (hk : 33 ≤ k) (ha : AgreeBelow k σ σ') :
    ResMemD rd σ' lvl ich ls la mu i0 i1 s b a P Q lam SL := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ha osMus (by show 22 < k; omega)]; exact h.mus
  · rw [ha _ hich]; exact h.li0
  · rw [ha _ hich]; exact h.li1
  · rw [ha _ hls]; exact h.lsc
  · rw [ha osBetas (by show 20 < k; omega)]; exact h.lbe
  · rw [ha _ hla]; exact h.laf
  · rw [ha osOodSc (by show 28 < k; omega)]; exact h.lam
  · rw [ha _ hich]; exact h.st0
  · rw [ha _ hich]; exact h.st1

/-- The arguments and returns of `osResidual c tch ich bd ls la lvl lv mats k`'s dispatch. -/
def osResCall1 (c : OsCfg) (bd lvl : ℕ) (lv : OsLv) (mats : List OsMat) (k : ℕ) : List V × List V :=
  let qp := osMatP c.plan mats osQpos lv.posOff k
  let m1 := osMatsAfter c.plan mats osQpos lv.posOff k
  let bp := osMatP c.plan m1 bd (lvl * ligColsCap) qp.2.2
  let m2 := osMatsAfter c.plan m1 bd (lvl * ligColsCap) qp.2.2
  let hp := osMatP c.plan m2 osHs (lvl * hsStride) bp.2.2
  ([.n qp.2.1, .n bp.2.1, .n hp.2.1, .n hp.2.2], osRun (hp.2.2 + 1) 2)

theorem osResidual_next (c : OsCfg) (tch ich bd ls la lvl : ℕ) (lv : OsLv) (mats : List OsMat)
    (k : ℕ) : k ≤ (osResidual c tch ich bd ls la lvl lv mats k).2.2 := by
  unfold osResidual
  dsimp only
  generalize hq : osMatP c.plan mats osQpos lv.posOff k = qp
  have a : k ≤ qp.2.2 := hq ▸ osMatP_k _ _ _ _ _
  generalize hb : osMatP c.plan (osMatsAfter c.plan mats osQpos lv.posOff k) bd (lvl * ligColsCap)
    qp.2.2 = bp
  have b : qp.2.2 ≤ bp.2.2 := hb ▸ osMatP_k _ _ _ _ _
  generalize hh : osMatP c.plan _ osHs (lvl * hsStride) bp.2.2 = hp
  have d : bp.2.2 ≤ hp.2.2 := hh ▸ osMatP_k _ _ _ _ _
  generalize hs : osMatP c.plan _ osQpos lv.posOff (hp.2.2 + 5) = sp
  have e : hp.2.2 + 5 ≤ sp.2.2 := hs ▸ osMatP_k _ _ _ _ _
  generalize hf : osMatP c.plan _ osFch lv.resFoldOff sp.2.2 = fp
  have f : sp.2.2 ≤ fp.2.2 := hf ▸ osMatP_k _ _ _ _ _
  omega

theorem osResidual_allocs (c : OsCfg) (tch ich bd ls la lvl : ℕ) (lv : OsLv) (mats : List OsMat)
    (k : ℕ) : (osResidual c tch ich bd ls la lvl lv mats k).1.filterMap Stmt.allocSz = [] := by
  simp only [osResidual, List.filterMap_append, osMatP_allocs, List.nil_append]
  rfl

/-- **A level's residual, honestly**: the dispatch into `level_residual` at its arguments,
returning `P`, `Q`; the zero flag of `a`; the dispatch into `level_residual_slow`, returning `SL`;
the sums stored. -/
theorem osResidual_complete {c : OsCfg} {tch ich bd ls la lvl : ℕ} {lv : OsLv} {mats : List OsMat}
    {k : ℕ} {σ : Val} {mu i0 i1 s b a P Q lam SL : E}
    (hbd : bd < k) (hich : ich < k) (hls : ls < k) (hla : la < k) (htch : tch < k) (hk : 33 ≤ k)
    (hmb : MatsBelow k mats) (hmo : ∀ C rd, H C rd → MatsOk σ mats)
    (hpo : lv.posOff < u128Bound) (hlc : lvl * ligColsCap < u128Bound) (hhs : lvl * hsStride < u128Bound)
    (hro : lv.resFoldOff < u128Bound) (hiz : IsZeroC H)
    (hrate : ∀ C rd, H C rd → LvRate σ c lvl lv)
    (hm : ∀ C rd, H C rd → ResMemD rd σ lvl ich ls la mu i0 i1 s b a P Q lam SL)
    (hC : ∀ C rd, H C rd → C (osResidualName lv)
      [σ (.n osQpos) * gen ^ lv.posOff, σ (.n bd) * gen ^ (lvl * ligColsCap),
        σ (.n osHs) * gen ^ (lvl * hsStride), mu] [P, Q])
    (hS : ∀ C rd, H C rd → C (osSlowName c lv)
      [σ (.n osQpos) * gen ^ lv.posOff, σ (.n osFch) * gen ^ lv.resFoldOff, σ (.n tch), lam, zeroOf a]
        [SL]) :
    BlkA H σ k (osResidual c tch ich bd ls la lvl lv mats k).2.2 (osResidual c tch ich bd ls la lvl lv mats k).1
      (fun σ' ↦ MatsOk σ' (osResidual c tch ich bd ls la lvl lv mats k).2.1 ∧
        MatsBelow (osResidual c tch ich bd ls la lvl lv mats k).2.2 (osResidual c tch ich bd ls la lvl lv mats k).2.1 ∧
        (osResCall1 c bd lvl lv mats k).1.map σ' =
          [σ (.n osQpos) * gen ^ lv.posOff, σ (.n bd) * gen ^ (lvl * ligColsCap),
            σ (.n osHs) * gen ^ (lvl * hsStride), mu] ∧
        (osResCall1 c bd lvl lv mats k).2.map σ' = [P, Q] ∧
        (osSlowCall1 c tch bd lvl lv mats k).1.map σ' =
          [σ (.n osQpos) * gen ^ lv.posOff, σ (.n osFch) * gen ^ lv.resFoldOff, σ (.n tch), lam,
            zeroOf a] ∧
        (osSlowCall1 c tch bd lvl lv mats k).2.map σ' = [SL]) := by
  unfold osResidual osResCall1 osSlowCall1
  dsimp only
  set qp := osMatP c.plan mats osQpos lv.posOff k with hqp
  set m1 := osMatsAfter c.plan mats osQpos lv.posOff k with hm1
  set bp := osMatP c.plan m1 bd (lvl * ligColsCap) qp.2.2 with hbp
  set m2 := osMatsAfter c.plan m1 bd (lvl * ligColsCap) qp.2.2 with hm2
  set hp := osMatP c.plan m2 osHs (lvl * hsStride) bp.2.2 with hhp
  set m3 := osMatsAfter c.plan m2 osHs (lvl * hsStride) bp.2.2 with hm3
  set j := hp.2.2 with hj
  set sp := osMatP c.plan m3 osQpos lv.posOff (j + 5) with hsp
  set m4 := osMatsAfter c.plan m3 osQpos lv.posOff (j + 5) with hm4
  set fp := osMatP c.plan m4 osFch lv.resFoldOff sp.2.2 with hfp
  set m5 := osMatsAfter c.plan m4 osFch lv.resFoldOff sp.2.2 with hm5
  set l := fp.2.2 with hl
  have k1 : k ≤ qp.2.2 := osMatP_k _ _ _ _ _
  have k2 : qp.2.2 ≤ bp.2.2 := osMatP_k _ _ _ _ _
  have k3 : bp.2.2 ≤ j := osMatP_k _ _ _ _ _
  have k4 : j + 5 ≤ sp.2.2 := osMatP_k _ _ _ _ _
  have k5 : sp.2.2 ≤ l := osMatP_k _ _ _ _ _
  have l1 : qp.2.1 < qp.2.2 := osMatP_lt _ _ _ _ _ (show 30 < k by omega)
  have l2 : bp.2.1 < bp.2.2 := osMatP_lt _ _ _ _ _ (show bd < qp.2.2 by omega)
  have l3 : hp.2.1 < j := osMatP_lt _ _ _ _ _ (show 24 < bp.2.2 by omega)
  have l4 : sp.2.1 < sp.2.2 := osMatP_lt _ _ _ _ _ (show 30 < j + 5 by omega)
  have l5 : fp.2.1 < l := osMatP_lt _ _ _ _ _ (show 16 < sp.2.2 by omega)
  have mb1 : MatsBelow qp.2.2 m1 := osMatP_below hmb (show 30 < k by omega)
  have mb2 : MatsBelow bp.2.2 m2 := osMatP_below mb1 (show bd < qp.2.2 by omega)
  have mb3 : MatsBelow j m3 := osMatP_below mb2 (show 24 < bp.2.2 by omega)
  have mb3' : MatsBelow (j + 5) m3 := fun m hm ↦ by
    obtain ⟨x, y, z⟩ := mb3 m hm; exact ⟨by omega, by omega, by omega⟩
  have mb4 : MatsBelow sp.2.2 m4 := osMatP_below mb3' (show 30 < j + 5 by omega)
  have mb5 : MatsBelow l m5 := osMatP_below mb4 (show 16 < sp.2.2 by omega)
  -- the pointers
  have b1 := osMatP_blkA (H := H) (P := c.plan) (mats := mats) (base := osQpos) (off := lv.posOff) (k := k) σ
    (show 30 < k by omega) hmb hmo hpo
  have b2 := BlkA.seq (H := H) k1 k2 b1 (B := bp.1)
    (OutB := fun σ' ↦ σ' (.n bp.2.1) = σ (.n bd) * gen ^ (lvl * ligColsCap) ∧ MatsOk σ' m2 ∧
      MatsBelow bp.2.2 m2) fun σ1 ha1 ho1 ↦ by
      have h := osMatP_blkA (H := H) (P := c.plan) (mats := m1) (base := bd) (off := lvl * ligColsCap)
        (k := qp.2.2) σ1 (by omega) mb1 (fun C rd hH ↦ (ho1 C rd hH).2.1) hlc
      rw [ha1 _ hbd] at h
      exact h
  have b3 := BlkA.seq (H := H) (le_trans k1 k2) k3 b2 (B := hp.1)
    (OutB := fun σ' ↦ σ' (.n hp.2.1) = σ (.n osHs) * gen ^ (lvl * hsStride) ∧ MatsOk σ' m3 ∧
      MatsBelow j m3) fun σ1 ha1 ho1 ↦ by
      have h := osMatP_blkA (H := H) (P := c.plan) (mats := m2) (base := osHs) (off := lvl * hsStride)
        (k := bp.2.2) σ1 (show 24 < bp.2.2 by omega) mb2 (fun C rd hH ↦ (ho1 C rd hH).2.2.1) hhs
      rw [ha1 osHs (by show 24 < k; omega)] at h
      exact h
  -- `μ`
  have b4 := BlkA.seq (H := H) (le_trans (le_trans k1 k2) k3) (show j ≤ j + 1 by omega) b3
    (B := [osLd j osMus lvl]) (OutB := fun σ' ↦ σ' (.n j) = mu) fun σ1 ha1 _ ↦ by
      refine ⟨lstF j [mu], fun C rd hH σ' ha hr ↦ ?_⟩
      have v : σ' (.n j) = mu := by
        have := lstF_at hr (by simp) 0 (by simp)
        simpa using this
      refine ⟨?_, v⟩
      simp only [allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_load, osLd]
      rw [v, ha osMus (by show 22 < j; omega), ha1 osMus (by show 22 < k; omega)]
      exact (hm C rd hH).mus
  -- the dispatch into `level_residual`
  have hargsV : ∀ σ1 : Val, (∀ C rd, H C rd →
      ((σ1 (.n qp.2.1) = σ (.n osQpos) * gen ^ lv.posOff ∧ MatsOk σ1 m1 ∧ MatsBelow qp.2.2 m1) ∧
        σ1 (.n bp.2.1) = σ (.n bd) * gen ^ (lvl * ligColsCap) ∧ MatsOk σ1 m2 ∧ MatsBelow bp.2.2 m2) ∧
        σ1 (.n hp.2.1) = σ (.n osHs) * gen ^ (lvl * hsStride) ∧ MatsOk σ1 m3 ∧ MatsBelow j m3) →
      (∀ C rd, H C rd → σ1 (.n j) = mu) → ∀ C rd, H C rd →
      [qp.2.1, bp.2.1, hp.2.1, j].map (fun i ↦ σ1 (.n i)) =
        [σ (.n osQpos) * gen ^ lv.posOff, σ (.n bd) * gen ^ (lvl * ligColsCap),
          σ (.n osHs) * gen ^ (lvl * hsStride), mu] := fun σ1 h1 h2 C rd hH ↦ by
    obtain ⟨⟨⟨e1, -⟩, e2, -⟩, e3, -⟩ := h1 C rd hH
    simp only [List.map_cons, List.map_nil, e1, e2, e3, h2 C rd hH]
  have b5 := BlkA.seq (H := H) (show k ≤ j + 1 by omega) (show j + 1 ≤ j + 1 + 2 by omega) b4
    (B := [.dispatch (.n osRate) ((c.lvAt lvl).map osResidualName) ([qp.2.1, bp.2.1, hp.2.1, j].map V.n)
      (osRun (j + 1) 2)])
    (OutB := fun σ' ↦ [qp.2.1, bp.2.1, hp.2.1, j].map (fun i ↦ σ' (.n i)) =
        [σ (.n osQpos) * gen ^ lv.posOff, σ (.n bd) * gen ^ (lvl * ligColsCap),
          σ (.n osHs) * gen ^ (lvl * hsStride), mu] ∧
      ∀ j' < 2, σ' (.n (j + 1 + j')) = [P, Q].getD j' 0) fun σ1 ha1 ho1 ↦ by
      have hargs : ∀ i ∈ [qp.2.1, bp.2.1, hp.2.1, j], i < j + 1 := fun i hi ↦ by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl <;> omega
      have h := rateDisp_blk (H := H) (σ := σ1) (c := c) (lvl := lvl) (lv := lv) (r := j + 1) (n := 2)
        osResidualName (args := [qp.2.1, bp.2.1, hp.2.1, j]) [P, Q] rfl hargs (by omega)
        (fun C rd hH ↦ by
          obtain ⟨ri, hri, hx, hlen, hlv⟩ := hrate C rd hH
          exact ⟨ri, hri, by rw [ha1 _ (show 0 < k by omega)]; exact hx, hlen, hlv⟩)
        (fun C rd hH ↦ by
          rw [hargsV σ1 (fun C rd hH ↦ (ho1 C rd hH).1) (fun C rd hH ↦ (ho1 C rd hH).2) C rd hH]
          exact hC C rd hH)
      refine BlkA.monoH h fun C rd hH σ' ha hv ↦ ⟨?_, hv⟩
      rw [← hargsV σ1 (fun C rd hH ↦ (ho1 C rd hH).1) (fun C rd hH ↦ (ho1 C rd hH).2) C rd hH]
      exact List.map_congr_left fun i hi ↦ ha _ (hargs i hi)
  have c5 := b5.mono (Out' := fun σ' ↦ MatsOk σ' m3 ∧
      [qp.2.1, bp.2.1, hp.2.1, j].map (fun i ↦ σ' (.n i)) =
        [σ (.n osQpos) * gen ^ lv.posOff, σ (.n bd) * gen ^ (lvl * ligColsCap),
          σ (.n osHs) * gen ^ (lvl * hsStride), mu] ∧
      σ' (.n (j + 1)) = P ∧ σ' (.n (j + 2)) = Q) fun σ' ho ↦ by
    obtain ⟨⟨⟨⟨-, -⟩, -, mo3, -⟩, -⟩, eargs, erets⟩ := ho
    exact ⟨mo3, eargs, by simpa using erets 0 (by omega), by simpa using erets 1 (by omega)⟩
  -- the zero flag
  have c6 := BlkA.seq (H := H) (show k ≤ j + 1 + 2 by omega) (show j + 1 + 2 ≤ j + 5 by omega) c5
    (B := [osLd (j + 3) la lvl, .call "is_zero" [.n (j + 3)] [.n (j + 4)]])
    (OutB := fun σ' ↦ σ' (.n (j + 4)) = zeroOf a) fun σ1 ha1 _ ↦ by
      have e : j + 1 + 2 = j + 3 := by omega
      rw [e]
      refine blk_lst [a, zeroOf a] (by simp) fun C rd hH σ' ha hv ↦ ?_
      have v0 := hv 0 (by simp)
      have v1 := hv 1 (by simp)
      simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at v0 v1
      simp only [osLd, allOk_cons, allOk_nil, and_true, stmtOk_atom, stmtOk_call, holds_load,
        List.map_cons, List.map_nil]
      rw [show j + 3 + 1 = j + 4 by omega] at v1
      rw [v0, v1, ha _ (show la < j + 3 by omega), ha1 _ hla]
      exact ⟨⟨(hm C rd hH).laf, hiz C rd hH a⟩, rfl⟩
  have c6' := c6.mono (Out' := fun σ' ↦ MatsOk σ' m3 ∧
      [qp.2.1, bp.2.1, hp.2.1, j].map (fun i ↦ σ' (.n i)) =
        [σ (.n osQpos) * gen ^ lv.posOff, σ (.n bd) * gen ^ (lvl * ligColsCap),
          σ (.n osHs) * gen ^ (lvl * hsStride), mu] ∧
      σ' (.n (j + 1)) = P ∧ σ' (.n (j + 2)) = Q ∧ σ' (.n (j + 4)) = zeroOf a) fun σ' ho ↦
    ⟨ho.1.1, ho.1.2.1, ho.1.2.2.1, ho.1.2.2.2, ho.2⟩
  -- the slow call's pointers
  have c7 := BlkA.seq (H := H) (show k ≤ j + 5 by omega) (show j + 5 ≤ sp.2.2 by omega) c6'
    (B := sp.1) (OutB := fun σ' ↦ σ' (.n sp.2.1) = σ (.n osQpos) * gen ^ lv.posOff ∧ MatsOk σ' m4 ∧
      MatsBelow sp.2.2 m4) fun σ1 ha1 ho1 ↦ by
      have h := osMatP_blkA (H := H) (P := c.plan) (mats := m3) (base := osQpos) (off := lv.posOff)
        (k := j + 5) σ1 (show 30 < j + 5 by omega) mb3' (fun C rd hH ↦ (ho1 C rd hH).1) hpo
      rw [ha1 osQpos (by show 30 < k; omega)] at h
      exact h
  have c8 := BlkA.seq (H := H) (show k ≤ sp.2.2 by omega) k5 c7
    (B := fp.1) (OutB := fun σ' ↦ σ' (.n fp.2.1) = σ (.n osFch) * gen ^ lv.resFoldOff ∧
      MatsOk σ' m5 ∧ MatsBelow l m5) fun σ1 ha1 ho1 ↦ by
      have h := osMatP_blkA (H := H) (P := c.plan) (mats := m4) (base := osFch) (off := lv.resFoldOff)
        (k := sp.2.2) σ1 (show 16 < sp.2.2 by omega) mb4 (fun C rd hH ↦ (ho1 C rd hH).2.2.1) hro
      rw [ha1 osFch (by show 16 < k; omega)] at h
      exact h
  have c8' := c8.mono (Out' := fun σ' ↦ MatsOk σ' m5 ∧
      [qp.2.1, bp.2.1, hp.2.1, j].map (fun i ↦ σ' (.n i)) =
        [σ (.n osQpos) * gen ^ lv.posOff, σ (.n bd) * gen ^ (lvl * ligColsCap),
          σ (.n osHs) * gen ^ (lvl * hsStride), mu] ∧
      σ' (.n (j + 1)) = P ∧ σ' (.n (j + 2)) = Q ∧ σ' (.n (j + 4)) = zeroOf a ∧
      σ' (.n sp.2.1) = σ (.n osQpos) * gen ^ lv.posOff ∧
      σ' (.n fp.2.1) = σ (.n osFch) * gen ^ lv.resFoldOff) fun σ' ho ↦
    ⟨ho.2.2.1, ho.1.1.2.1, ho.1.1.2.2.1, ho.1.1.2.2.2.1, ho.1.1.2.2.2.2, ho.1.2.1, ho.2.1⟩
  -- `λ`
  have c9 := BlkA.seq (H := H) (show k ≤ l by omega) (show l ≤ l + 1 by omega) c8'
    (B := [osLd l osOodSc (lvl + 1)]) (OutB := fun σ' ↦ σ' (.n l) = lam) fun σ1 ha1 _ ↦
      blk_lst [lam] (by simp) fun C rd hH σ' ha hv ↦ by
        have v0 := hv 0 (by simp)
        simp only [List.getD_cons_zero, Nat.add_zero] at v0
        simp only [osLd, allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_load]
        rw [v0, ha osOodSc (by show 28 < l; omega), ha1 osOodSc (by show 28 < k; omega)]
        exact ⟨(hm C rd hH).lam, rfl⟩
  -- the dispatch into `level_residual_slow`
  have c10 := BlkA.seq (H := H) (show k ≤ l + 1 by omega) (show l + 1 ≤ l + 1 + 1 by omega) c9
    (B := [.dispatch (.n osRate) ((c.lvAt lvl).map (osSlowName c))
      ([sp.2.1, fp.2.1, tch, l, j + 4].map V.n) (osRun (l + 1) 1)])
    (OutB := fun σ' ↦ ∀ j' < 1, σ' (.n (l + 1 + j')) = [SL].getD j' 0) fun σ1 ha1 ho1 ↦
      rateDisp_blk (H := H) (σ := σ1) (c := c) (lvl := lvl) (lv := lv) (r := l + 1) (n := 1)
        (osSlowName c) (args := [sp.2.1, fp.2.1, tch, l, j + 4]) [SL] rfl
        (fun i hi ↦ by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl | rfl | rfl | rfl <;> omega) (by omega)
        (fun C rd hH ↦ by
          obtain ⟨ri, hri, hx, hlen, hlv⟩ := hrate C rd hH
          exact ⟨ri, hri, by rw [ha1 _ (show 0 < k by omega)]; exact hx, hlen, hlv⟩)
        (fun C rd hH ↦ by
          obtain ⟨⟨-, -, -, -, ez, es, ef⟩, el⟩ := ho1 C rd hH
          simp only [List.map_cons, List.map_nil]
          rw [ez, es, ef, el, ha1 _ htch]
          exact hS C rd hH)
  -- the sums
  have c11 := BlkA.seq (H := H) (show k ≤ l + 1 + 1 by omega) (show l + 1 + 1 ≤ l + 2 + 11 by omega)
    c10 (B := resB ich ls la lvl (j + 1) (j + 2) (l + 1) (l + 2)) (OutB := fun _ ↦ True)
    fun σ2 ha2 ho2 ↦ by
      have e : l + 1 + 1 = l + 2 := by omega
      rw [e]
      exact resB_complete (H := H) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega)
        (fun C rd hH ↦ by
          obtain ⟨⟨⟨-, -, eP, eQ, -⟩, -⟩, eS⟩ := ho2 C rd hH
          exact ⟨eP, eQ, by simpa using eS 0 (by omega)⟩)
        (fun C rd hH ↦ by
          have hM := (hm C rd hH).agree hich hls hla hk (fun i hi ↦ ha2 i (by omega))
          exact ⟨hM.li0, hM.lsc, hM.li1, hM.lbe, hM.laf, hM.st0, hM.st1⟩)
  refine BlkA.congr (BlkA.mono c11.agree fun σ' ho ↦ ?_) (by
    simp only [resB, List.append_assoc, List.cons_append, List.nil_append]; rfl)
  obtain ⟨⟨⟨⟨⟨mo5, eargs, eP, eQ, ez, es, ef⟩, el⟩, eS⟩, -⟩, hag⟩ := ho
  refine ⟨mo5, fun m hm' ↦ ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨x, y, z⟩ := mb5 m hm'; exact ⟨by omega, by omega, by omega⟩
  · show ([V.n qp.2.1, V.n bp.2.1, V.n hp.2.1, V.n j]).map σ' = _
    rw [← eargs]; rfl
  · rw [osRun_map, show List.range 2 = [0, 1] from rfl]
    simp only [List.map_cons, List.map_nil, Nat.add_zero]
    rw [eP, show j + 1 + 1 = j + 2 by omega, eQ]
  · simp only [List.map_cons, List.map_nil]
    have et : σ' (.n tch) = σ (.n tch) := hag _ htch
    rw [es, ef, et, el, ez]
  · rw [osRun_map, show List.range 1 = [0] from rfl]
    simp only [List.map_cons, List.map_nil, Nat.add_zero]
    rw [show SL = [SL].getD 0 0 from rfl, ← eS 0 (by omega), Nat.add_zero]

theorem osResiduals_next (c : OsCfg) (tch ich bd ls la : ℕ) :
    ∀ (lvs : List OsLv) (lvl : ℕ) (mats : List OsMat) (k : ℕ),
      k ≤ (osResiduals c tch ich bd ls la lvl lvs mats k).2
  | [], _, _, _ => le_rfl
  | lv :: rest, lvl, mats, k => by
    simp only [osResiduals]
    exact le_trans (osResidual_next c tch ich bd ls la lvl lv mats k)
      (osResiduals_next c tch ich bd ls la rest (lvl + 1) _ _)

theorem osResiduals_allocs (c : OsCfg) (tch ich bd ls la : ℕ) :
    ∀ (lvl : ℕ) (lvs : List OsLv) (mats : List OsMat) (k : ℕ),
      (osResiduals c tch ich bd ls la lvl lvs mats k).1.filterMap Stmt.allocSz = []
  | _, [], _, _ => rfl
  | lvl, lv :: rest, mats, k => by
    simp only [osResiduals, List.filterMap_append, osResidual_allocs,
      osResiduals_allocs c tch ich bd ls la (lvl + 1), List.nil_append]

/-- **Every non-final level's residual, honestly**, the levels `lvl ..`: each dispatch into
`level_residual` at its arguments, returning `P`, `Q`, and into `level_residual_slow`, returning
`SL`. -/
theorem osResiduals_complete {c : OsCfg} {tch ich bd ls la : ℕ} (hiz : IsZeroC H)
    (mu I0 I1 S B A P Q Lam SL : ℕ → E) :
    ∀ (lvs : List OsLv) (lvl : ℕ) (mats : List OsMat) (k : ℕ) (σ : Val),
      bd < k → ich < k → ls < k → la < k → tch < k → 33 ≤ k → MatsBelow k mats →
      (∀ C rd, H C rd → MatsOk σ mats) →
      (∀ i < lvs.length, (lvs.getD i default).posOff < u128Bound ∧
        (lvl + i) * ligColsCap < u128Bound ∧ (lvl + i) * hsStride < u128Bound ∧
        (lvs.getD i default).resFoldOff < u128Bound) →
      (∀ i < lvs.length, ∀ C rd, H C rd → LvRate σ c (lvl + i) (lvs.getD i default)) →
      (∀ i < lvs.length, ∀ C rd, H C rd → ResMemD rd σ (lvl + i) ich ls la (mu (lvl + i)) (I0 (lvl + i))
        (I1 (lvl + i)) (S (lvl + i)) (B (lvl + i)) (A (lvl + i)) (P (lvl + i)) (Q (lvl + i))
        (Lam (lvl + i)) (SL (lvl + i))) →
      (∀ i < lvs.length, ∀ C rd, H C rd → C (osResidualName (lvs.getD i default))
        [σ (.n osQpos) * gen ^ (lvs.getD i default).posOff, σ (.n bd) * gen ^ ((lvl + i) * ligColsCap),
          σ (.n osHs) * gen ^ ((lvl + i) * hsStride), mu (lvl + i)] [P (lvl + i), Q (lvl + i)]) →
      (∀ i < lvs.length, ∀ C rd, H C rd → C (osSlowName c (lvs.getD i default))
        [σ (.n osQpos) * gen ^ (lvs.getD i default).posOff,
          σ (.n osFch) * gen ^ (lvs.getD i default).resFoldOff, σ (.n tch), Lam (lvl + i),
          zeroOf (A (lvl + i))] [SL (lvl + i)]) →
      BlkA H σ k (osResiduals c tch ich bd ls la lvl lvs mats k).2
        (osResiduals c tch ich bd ls la lvl lvs mats k).1
        (fun σ' ↦ ∀ i < lvs.length,
          ((osResCallsL c tch ich bd ls la lvl lvs mats k).getD i ([], [])).1.map σ' =
            [σ (.n osQpos) * gen ^ (lvs.getD i default).posOff, σ (.n bd) * gen ^ ((lvl + i) * ligColsCap),
              σ (.n osHs) * gen ^ ((lvl + i) * hsStride), mu (lvl + i)] ∧
          ((osResCallsL c tch ich bd ls la lvl lvs mats k).getD i ([], [])).2.map σ' =
            [P (lvl + i), Q (lvl + i)] ∧
          ((osSlowCallsL c tch ich bd ls la lvl lvs mats k).getD i ([], [])).1.map σ' =
            [σ (.n osQpos) * gen ^ (lvs.getD i default).posOff,
              σ (.n osFch) * gen ^ (lvs.getD i default).resFoldOff, σ (.n tch), Lam (lvl + i),
              zeroOf (A (lvl + i))] ∧
          ((osSlowCallsL c tch ich bd ls la lvl lvs mats k).getD i ([], [])).2.map σ' = [SL (lvl + i)])
  | [], _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ =>
    BlkA.nil fun _ _ i hi ↦ absurd hi (by simp)
  | lv :: rest, lvl, mats, k, σ, hbd, hich, hls, hla, htch, hk, hmb, hmo, hoff, hrate, hm, hC, hS => by
    have o0 := hoff 0 (by simp)
    simp only [List.getD_cons_zero, Nat.add_zero] at o0
    have h0 := osResidual_complete (H := H) (c := c) (tch := tch) (ich := ich) (bd := bd) (ls := ls)
      (la := la) (lvl := lvl) (lv := lv) (mats := mats) (k := k) (σ := σ) (mu := mu lvl) (i0 := I0 lvl)
      (i1 := I1 lvl) (s := S lvl) (b := B lvl) (a := A lvl) (P := P lvl) (Q := Q lvl) (lam := Lam lvl)
      (SL := SL lvl) hbd hich hls hla htch hk hmb hmo o0.1 o0.2.1 o0.2.2.1 o0.2.2.2 hiz
      (fun C rd hH ↦ by simpa using hrate 0 (by simp) C rd hH)
      (fun C rd hH ↦ by simpa using hm 0 (by simp) C rd hH)
      (fun C rd hH ↦ by simpa using hC 0 (by simp) C rd hH)
      (fun C rd hH ↦ by simpa using hS 0 (by simp) C rd hH)
    set r := osResidual c tch ich bd ls la lvl lv mats k with hr
    have hn : k ≤ r.2.2 := osResidual_next c tch ich bd ls la lvl lv mats k
    have hn2 := osResiduals_next c tch ich bd ls la rest (lvl + 1) r.2.1 r.2.2
    have hB := BlkA.seq (H := H) hn hn2 h0
      (B := (osResiduals c tch ich bd ls la (lvl + 1) rest r.2.1 r.2.2).1)
      (OutB := fun σ' ↦ ∀ i < rest.length,
        ((osResCallsL c tch ich bd ls la (lvl + 1) rest r.2.1 r.2.2).getD i ([], [])).1.map σ' =
          [σ (.n osQpos) * gen ^ (rest.getD i default).posOff, σ (.n bd) * gen ^ ((lvl + 1 + i) * ligColsCap),
            σ (.n osHs) * gen ^ ((lvl + 1 + i) * hsStride), mu (lvl + 1 + i)] ∧
        ((osResCallsL c tch ich bd ls la (lvl + 1) rest r.2.1 r.2.2).getD i ([], [])).2.map σ' =
          [P (lvl + 1 + i), Q (lvl + 1 + i)] ∧
        ((osSlowCallsL c tch ich bd ls la (lvl + 1) rest r.2.1 r.2.2).getD i ([], [])).1.map σ' =
          [σ (.n osQpos) * gen ^ (rest.getD i default).posOff,
            σ (.n osFch) * gen ^ (rest.getD i default).resFoldOff, σ (.n tch), Lam (lvl + 1 + i),
            zeroOf (A (lvl + 1 + i))] ∧
        ((osSlowCallsL c tch ich bd ls la (lvl + 1) rest r.2.1 r.2.2).getD i ([], [])).2.map σ' =
          [SL (lvl + 1 + i)])
      fun σ1 ha1 ho1 ↦ BlkA.of_ne fun ⟨C0, rd0, hH0⟩ ↦ by
      have e1 : σ1 (.n osQpos) = σ (.n osQpos) := ha1 osQpos (by show 30 < k; omega)
      have e2 : σ1 (.n bd) = σ (.n bd) := ha1 _ hbd
      have e3 : σ1 (.n osHs) = σ (.n osHs) := ha1 osHs (by show 24 < k; omega)
      have e4 : σ1 (.n osFch) = σ (.n osFch) := ha1 osFch (by show 16 < k; omega)
      have e5 : σ1 (.n tch) = σ (.n tch) := ha1 _ htch
      have h := osResiduals_complete hiz mu I0 I1 S B A P Q Lam SL rest (lvl + 1) r.2.1 r.2.2 σ1
        (lt_of_lt_of_le hbd hn) (lt_of_lt_of_le hich hn) (lt_of_lt_of_le hls hn) (lt_of_lt_of_le hla hn)
        (lt_of_lt_of_le htch hn) (le_trans hk hn)
        (ho1 C0 rd0 hH0).2.1 (fun C rd hH ↦ (ho1 C rd hH).1)
        (fun i hi ↦ by
          have := hoff (i + 1) (by simp; omega)
          simpa [show lvl + (i + 1) = lvl + 1 + i by ring] using this)
        (fun i hi C rd hH ↦ by
          obtain ⟨ri, hri, hx, hlen, hlv⟩ := hrate (i + 1) (by simp; omega) C rd hH
          refine ⟨ri, hri, by rw [ha1 _ (show 0 < k by omega)]; exact hx, ?_, ?_⟩
          · simpa [show lvl + (i + 1) = lvl + 1 + i by ring] using hlen
          · simpa [show lvl + (i + 1) = lvl + 1 + i by ring] using hlv)
        (fun i hi C rd hH ↦ by
          have := (hm (i + 1) (by simp; omega) C rd hH).agree hich hls hla hk ha1
          simpa [show lvl + (i + 1) = lvl + 1 + i by ring] using this)
        (fun i hi C rd hH ↦ by
          have := hC (i + 1) (by simp; omega) C rd hH
          rw [e1, e2, e3]
          simpa [show lvl + (i + 1) = lvl + 1 + i by ring] using this)
        fun i hi C rd hH ↦ by
          have := hS (i + 1) (by simp; omega) C rd hH
          rw [e1, e4, e5]
          simpa [show lvl + (i + 1) = lvl + 1 + i by ring] using this
      exact h.mono fun σ' hv i hi ↦ by rw [← e1, ← e2, ← e3, ← e4, ← e5]; exact hv i hi
    refine (hB.congr rfl).mono fun σ' ⟨⟨_, _, a0, r0, s0, t0⟩, hs⟩ ↦ fun i hi ↦ ?_
    rcases i with _ | i
    · have e0 : (osResCallsL c tch ich bd ls la lvl (lv :: rest) mats k).getD 0 ([], []) =
          osResCall1 c bd lvl lv mats k := rfl
      have e0' : (osSlowCallsL c tch ich bd ls la lvl (lv :: rest) mats k).getD 0 ([], []) =
          osSlowCall1 c tch bd lvl lv mats k := rfl
      simp only [List.getD_cons_zero, Nat.add_zero]
      rw [e0, e0']
      exact ⟨a0, r0, s0, t0⟩
    · have e : (osResCallsL c tch ich bd ls la lvl (lv :: rest) mats k).getD (i + 1) ([], []) =
          (osResCallsL c tch ich bd ls la (lvl + 1) rest r.2.1 r.2.2).getD i ([], []) := rfl
      have e' : (osSlowCallsL c tch ich bd ls la lvl (lv :: rest) mats k).getD (i + 1) ([], []) =
          (osSlowCallsL c tch ich bd ls la (lvl + 1) rest r.2.1 r.2.2).getD i ([], []) := rfl
      have := hs i (by simp at hi; omega)
      rw [e, e', List.getD_cons_succ, show lvl + (i + 1) = lvl + 1 + i by ring]
      exact this

end
end LeanVM.Guest.B1.Whir
