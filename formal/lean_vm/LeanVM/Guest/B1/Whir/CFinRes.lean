/-
  LeanVM.Guest.B1.Whir.CFinRes

  A non-final level's residual in the finish, honestly: its pointers materialized, `μ` read, the
  dispatch into `level_residual` on the rate's selector, its sums into `inner_chain`.
-/

module

public import LeanVM.Guest.B1.Whir.CFinRs
public import LeanVM.Guest.B1.Whir.CLevel
public import LeanVM.Guest.B1.Place.OsProtoSpec

/-!
# The residuals, honestly

`osMatP_blkA`: a fixed buffer's shifted pointer, materialized from the materializations `mats`.
`ResMemD`: what memory holds for a level's residual: `μ` in `level_mus`, the inner chain's entries
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

/-- What memory holds for a level's residual, at the dispatch's returns `P`, `Q`. -/
structure ResMemD (rd : Reader) (σ : Val) (lvl ich ls la : ℕ) (mu i0 i1 s b a P Q : E) : Prop where
  mus : LoadHolds rd (σ (.n osMus)) lvl mu
  li0 : LoadHolds rd (σ (.n ich)) (2 * lvl) i0
  li1 : LoadHolds rd (σ (.n ich)) (2 * lvl + 1) i1
  lsc : LoadHolds rd (σ (.n ls)) lvl s
  lbe : LoadHolds rd (σ (.n osBetas)) lvl b
  laf : LoadHolds rd (σ (.n la)) lvl a
  st0 : LoadHolds rd (σ (.n ich)) (2 * lvl + 2) (i0 + s * P)
  st1 : LoadHolds rd (σ (.n ich)) (2 * lvl + 3) (i1 + b * a * Q)

theorem ResMemD.agree {rd : Reader} {σ σ' : Val} {lvl ich ls la k : ℕ} {mu i0 i1 s b a P Q : E}
    (h : ResMemD rd σ lvl ich ls la mu i0 i1 s b a P Q) (hich : ich < k) (hls : ls < k) (hla : la < k)
    (hk : 33 ≤ k) (ha : AgreeBelow k σ σ') : ResMemD rd σ' lvl ich ls la mu i0 i1 s b a P Q := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ha osMus (by show 22 < k; omega)]; exact h.mus
  · rw [ha _ hich]; exact h.li0
  · rw [ha _ hich]; exact h.li1
  · rw [ha _ hls]; exact h.lsc
  · rw [ha osBetas (by show 20 < k; omega)]; exact h.lbe
  · rw [ha _ hla]; exact h.laf
  · rw [ha _ hich]; exact h.st0
  · rw [ha _ hich]; exact h.st1

/-- The arguments and returns of `osResidual c ich bd ls la lvl lv mats k`'s dispatch. -/
def osResCall1 (c : OsCfg) (bd lvl : ℕ) (lv : OsLv) (mats : List OsMat) (k : ℕ) : List V × List V :=
  let qp := osMatP c.plan mats osQpos lv.posOff k
  let m1 := osMatsAfter c.plan mats osQpos lv.posOff k
  let bp := osMatP c.plan m1 bd (lvl * ligColsCap) qp.2.2
  let m2 := osMatsAfter c.plan m1 bd (lvl * ligColsCap) qp.2.2
  let hp := osMatP c.plan m2 osHs (lvl * hsStride) bp.2.2
  ([.n qp.2.1, .n bp.2.1, .n hp.2.1, .n hp.2.2], osRun (hp.2.2 + 1) 2)

theorem osResidual_next (c : OsCfg) (ich bd ls la lvl : ℕ) (lv : OsLv) (mats : List OsMat) (k : ℕ) :
    k ≤ (osResidual c ich bd ls la lvl lv mats k).2.2 := by
  have a := osMatP_k c.plan mats osQpos lv.posOff k
  have b := osMatP_k c.plan (osMatsAfter c.plan mats osQpos lv.posOff k) bd (lvl * ligColsCap)
    (osMatP c.plan mats osQpos lv.posOff k).2.2
  have d := osMatP_k c.plan (osMatsAfter c.plan (osMatsAfter c.plan mats osQpos lv.posOff k) bd
    (lvl * ligColsCap) (osMatP c.plan mats osQpos lv.posOff k).2.2) osHs (lvl * hsStride)
    (osMatP c.plan (osMatsAfter c.plan mats osQpos lv.posOff k) bd (lvl * ligColsCap)
      (osMatP c.plan mats osQpos lv.posOff k).2.2).2.2
  simp only [osResidual]
  omega

theorem osResidual_allocs (c : OsCfg) (ich bd ls la lvl : ℕ) (lv : OsLv) (mats : List OsMat) (k : ℕ) :
    (osResidual c ich bd ls la lvl lv mats k).1.filterMap Stmt.allocSz = [] := by
  simp only [osResidual, List.filterMap_append, osMatP_allocs, List.nil_append]
  rfl

/-- **A level's residual, honestly**: the dispatch at its arguments, returning `P`, `Q`, the sums
stored. -/
theorem osResidual_complete {c : OsCfg} {ich bd ls la lvl : ℕ} {lv : OsLv} {mats : List OsMat} {k : ℕ}
    {σ : Val} {mu i0 i1 s b a P Q : E}
    (hbd : bd < k) (hich : ich < k) (hls : ls < k) (hla : la < k) (hk : 33 ≤ k)
    (hmb : MatsBelow k mats) (hmo : ∀ C rd, H C rd → MatsOk σ mats)
    (hpo : lv.posOff < u128Bound) (hlc : lvl * ligColsCap < u128Bound) (hhs : lvl * hsStride < u128Bound)
    (hrate : ∀ C rd, H C rd → LvRate σ c lvl lv)
    (hm : ∀ C rd, H C rd → ResMemD rd σ lvl ich ls la mu i0 i1 s b a P Q)
    (hC : ∀ C rd, H C rd → C (osResidualName lv)
      [σ (.n osQpos) * gen ^ lv.posOff, σ (.n bd) * gen ^ (lvl * ligColsCap),
        σ (.n osHs) * gen ^ (lvl * hsStride), mu] [P, Q]) :
    BlkA H σ k (osResidual c ich bd ls la lvl lv mats k).2.2 (osResidual c ich bd ls la lvl lv mats k).1
      (fun σ' ↦ MatsOk σ' (osResidual c ich bd ls la lvl lv mats k).2.1 ∧
        MatsBelow (osResidual c ich bd ls la lvl lv mats k).2.2 (osResidual c ich bd ls la lvl lv mats k).2.1 ∧
        (osResCall1 c bd lvl lv mats k).1.map σ' =
          [σ (.n osQpos) * gen ^ lv.posOff, σ (.n bd) * gen ^ (lvl * ligColsCap),
            σ (.n osHs) * gen ^ (lvl * hsStride), mu] ∧
        (osResCall1 c bd lvl lv mats k).2.map σ' = [P, Q]) := by
  set qp := osMatP c.plan mats osQpos lv.posOff k with hqp
  set m1 := osMatsAfter c.plan mats osQpos lv.posOff k with hm1
  set bp := osMatP c.plan m1 bd (lvl * ligColsCap) qp.2.2 with hbp
  set m2 := osMatsAfter c.plan m1 bd (lvl * ligColsCap) qp.2.2 with hm2
  set hp := osMatP c.plan m2 osHs (lvl * hsStride) bp.2.2 with hhp
  set m3 := osMatsAfter c.plan m2 osHs (lvl * hsStride) bp.2.2 with hm3
  set j := hp.2.2 with hj
  have k1 : k ≤ qp.2.2 := osMatP_k _ _ _ _ _
  have k2 : qp.2.2 ≤ bp.2.2 := osMatP_k _ _ _ _ _
  have k3 : bp.2.2 ≤ j := osMatP_k _ _ _ _ _
  have l1 : qp.2.1 < qp.2.2 := osMatP_lt _ _ _ _ _ (show 30 < k by omega)
  have l2 : bp.2.1 < bp.2.2 := osMatP_lt _ _ _ _ _ (show bd < qp.2.2 by omega)
  have l3 : hp.2.1 < j := osMatP_lt _ _ _ _ _ (show 24 < bp.2.2 by omega)
  have mb1 : MatsBelow qp.2.2 m1 := osMatP_below hmb (show 30 < k by omega)
  have mb2 : MatsBelow bp.2.2 m2 := osMatP_below mb1 (show bd < qp.2.2 by omega)
  have mb3 : MatsBelow j m3 := osMatP_below mb2 (show 24 < bp.2.2 by omega)
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
  -- the dispatch
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
  -- the sums
  have b6 := BlkA.seq (H := H) (show k ≤ j + 1 + 2 by omega) (show j + 1 + 2 ≤ j + 3 + 10 by omega) b5
    (B := resB ich ls la lvl (j + 1) (j + 2) (j + 3)) (OutB := fun _ ↦ True) fun σ2 ha2 ho2 ↦ by
      have h := resB_complete (H := H) (ich := ich) (ls := ls) (la := la) (lvl := lvl) (h := j + 1)
        (hh := j + 2) (a := j + 3) (σ := σ2) (i0 := i0) (i1 := i1) (s := s) (b := b) (af := a) (P := P)
        (Q := Q) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (fun C rd hH ↦ by
          have v := (ho2 C rd hH).2.2
          exact ⟨by simpa using v 0 (by omega), by simpa using v 1 (by omega)⟩)
        (fun C rd hH ↦ by
          have hM := (hm C rd hH).agree hich hls hla hk ha2
          exact ⟨hM.li0, hM.lsc, hM.li1, hM.lbe, hM.laf, hM.st0, hM.st1⟩)
      exact BlkA.congr (h.mono fun _ _ ↦ trivial) (by rw [show j + 3 = j + 1 + 2 by omega])
  have ek : (osResidual c ich bd ls la lvl lv mats k).2.2 = j + 3 + 10 := rfl
  have em : (osResidual c ich bd ls la lvl lv mats k).2.1 = m3 := rfl
  rw [ek, em]
  refine BlkA.congr (BlkA.mono b6 fun σ' ho ↦ ?_) (by
    simp only [osResidual, resB, List.append_assoc, List.cons_append, List.nil_append]; rfl)
  obtain ⟨⟨⟨⟨⟨-, -⟩, -, mo3, -⟩, -⟩, eargs, erets⟩, -⟩ := ho
  refine ⟨mo3, fun m hm' ↦ ?_, ?_, ?_⟩
  · obtain ⟨x, y, z⟩ := mb3 m hm'; exact ⟨by omega, by omega, by omega⟩
  · show ([V.n qp.2.1, V.n bp.2.1, V.n hp.2.1, V.n j]).map σ' = _
    rw [← eargs]; rfl
  · show (osRun (j + 1) 2).map σ' = [P, Q]
    rw [osRun_map, show List.range 2 = [0, 1] from rfl]
    simp only [List.map_cons, List.map_nil]
    rw [erets 0 (by omega), erets 1 (by omega)]
    rfl

theorem osResiduals_next (c : OsCfg) (ich bd ls la : ℕ) :
    ∀ (lvs : List OsLv) (lvl : ℕ) (mats : List OsMat) (k : ℕ),
      k ≤ (osResiduals c ich bd ls la lvl lvs mats k).2
  | [], _, _, _ => le_rfl
  | lv :: rest, lvl, mats, k => by
    simp only [osResiduals]
    exact le_trans (osResidual_next c ich bd ls la lvl lv mats k)
      (osResiduals_next c ich bd ls la rest (lvl + 1) _ _)

theorem osResiduals_allocs (c : OsCfg) (ich bd ls la : ℕ) :
    ∀ (lvl : ℕ) (lvs : List OsLv) (mats : List OsMat) (k : ℕ),
      (osResiduals c ich bd ls la lvl lvs mats k).1.filterMap Stmt.allocSz = []
  | _, [], _, _ => rfl
  | lvl, lv :: rest, mats, k => by
    simp only [osResiduals, List.filterMap_append, osResidual_allocs, osResiduals_allocs c ich bd ls la (lvl + 1),
      List.nil_append]

/-- **Every non-final level's residual, honestly**, the levels `lvl ..`: each dispatch into
`level_residual` at its arguments, returning `P`, `Q`. -/
theorem osResiduals_complete {c : OsCfg} {ich bd ls la : ℕ} (mu I0 I1 S B A P Q : ℕ → E) :
    ∀ (lvs : List OsLv) (lvl : ℕ) (mats : List OsMat) (k : ℕ) (σ : Val),
      bd < k → ich < k → ls < k → la < k → 33 ≤ k → MatsBelow k mats →
      (∀ C rd, H C rd → MatsOk σ mats) →
      (∀ i < lvs.length, (lvs.getD i default).posOff < u128Bound ∧
        (lvl + i) * ligColsCap < u128Bound ∧ (lvl + i) * hsStride < u128Bound) →
      (∀ i < lvs.length, ∀ C rd, H C rd → LvRate σ c (lvl + i) (lvs.getD i default)) →
      (∀ i < lvs.length, ∀ C rd, H C rd → ResMemD rd σ (lvl + i) ich ls la (mu (lvl + i)) (I0 (lvl + i))
        (I1 (lvl + i)) (S (lvl + i)) (B (lvl + i)) (A (lvl + i)) (P (lvl + i)) (Q (lvl + i))) →
      (∀ i < lvs.length, ∀ C rd, H C rd → C (osResidualName (lvs.getD i default))
        [σ (.n osQpos) * gen ^ (lvs.getD i default).posOff, σ (.n bd) * gen ^ ((lvl + i) * ligColsCap),
          σ (.n osHs) * gen ^ ((lvl + i) * hsStride), mu (lvl + i)] [P (lvl + i), Q (lvl + i)]) →
      BlkA H σ k (osResiduals c ich bd ls la lvl lvs mats k).2 (osResiduals c ich bd ls la lvl lvs mats k).1
        (fun σ' ↦ ∀ i < lvs.length,
          ((osResCallsL c ich bd ls la lvl lvs mats k).getD i ([], [])).1.map σ' =
            [σ (.n osQpos) * gen ^ (lvs.getD i default).posOff, σ (.n bd) * gen ^ ((lvl + i) * ligColsCap),
              σ (.n osHs) * gen ^ ((lvl + i) * hsStride), mu (lvl + i)] ∧
          ((osResCallsL c ich bd ls la lvl lvs mats k).getD i ([], [])).2.map σ' = [P (lvl + i), Q (lvl + i)])
  | [], _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ =>
    BlkA.nil fun _ _ i hi ↦ absurd hi (by simp)
  | lv :: rest, lvl, mats, k, σ, hbd, hich, hls, hla, hk, hmb, hmo, hoff, hrate, hm, hC => by
    have o0 := hoff 0 (by simp)
    simp only [List.getD_cons_zero, Nat.add_zero] at o0
    have h0 := osResidual_complete (H := H) (c := c) (ich := ich) (bd := bd) (ls := ls) (la := la)
      (lvl := lvl) (lv := lv) (mats := mats) (k := k) (σ := σ) (mu := mu lvl) (i0 := I0 lvl) (i1 := I1 lvl)
      (s := S lvl) (b := B lvl) (a := A lvl) (P := P lvl) (Q := Q lvl) hbd hich hls hla hk hmb hmo o0.1 o0.2.1
      o0.2.2 (fun C rd hH ↦ by simpa using hrate 0 (by simp) C rd hH)
      (fun C rd hH ↦ by simpa using hm 0 (by simp) C rd hH) (fun C rd hH ↦ by simpa using hC 0 (by simp) C rd hH)
    set r := osResidual c ich bd ls la lvl lv mats k with hr
    have hn : k ≤ r.2.2 := osResidual_next c ich bd ls la lvl lv mats k
    have hn2 := osResiduals_next c ich bd ls la rest (lvl + 1) r.2.1 r.2.2
    have hB := BlkA.seq (H := H) hn hn2 h0 (B := (osResiduals c ich bd ls la (lvl + 1) rest r.2.1 r.2.2).1)
      (OutB := fun σ' ↦ ∀ i < rest.length,
        ((osResCallsL c ich bd ls la (lvl + 1) rest r.2.1 r.2.2).getD i ([], [])).1.map σ' =
          [σ (.n osQpos) * gen ^ (rest.getD i default).posOff, σ (.n bd) * gen ^ ((lvl + 1 + i) * ligColsCap),
            σ (.n osHs) * gen ^ ((lvl + 1 + i) * hsStride), mu (lvl + 1 + i)] ∧
        ((osResCallsL c ich bd ls la (lvl + 1) rest r.2.1 r.2.2).getD i ([], [])).2.map σ' =
          [P (lvl + 1 + i), Q (lvl + 1 + i)])
      fun σ1 ha1 ho1 ↦ BlkA.of_ne fun ⟨C0, rd0, hH0⟩ ↦ by
      have e1 : σ1 (.n osQpos) = σ (.n osQpos) := ha1 osQpos (by show 30 < k; omega)
      have e2 : σ1 (.n bd) = σ (.n bd) := ha1 _ hbd
      have e3 : σ1 (.n osHs) = σ (.n osHs) := ha1 osHs (by show 24 < k; omega)
      have h := osResiduals_complete mu I0 I1 S B A P Q rest (lvl + 1) r.2.1 r.2.2 σ1 (lt_of_lt_of_le hbd hn)
        (lt_of_lt_of_le hich hn) (lt_of_lt_of_le hls hn) (lt_of_lt_of_le hla hn) (le_trans hk hn)
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
        fun i hi C rd hH ↦ by
          have := hC (i + 1) (by simp; omega) C rd hH
          rw [e1, e2, e3]
          simpa [show lvl + (i + 1) = lvl + 1 + i by ring] using this
      exact h.mono fun σ' hv i hi ↦ by rw [← e1, ← e2, ← e3]; exact hv i hi
    refine (hB.congr rfl).mono fun σ' ⟨⟨_, _, a0, r0⟩, hs⟩ ↦ fun i hi ↦ ?_
    rcases i with _ | i
    · have e0 : (osResCallsL c ich bd ls la lvl (lv :: rest) mats k).getD 0 ([], []) =
          osResCall1 c bd lvl lv mats k := rfl
      simp only [List.getD_cons_zero, Nat.add_zero]
      rw [e0]
      exact ⟨a0, r0⟩
    · have e : (osResCallsL c ich bd ls la lvl (lv :: rest) mats k).getD (i + 1) ([], []) =
          (osResCallsL c ich bd ls la (lvl + 1) rest r.2.1 r.2.2).getD i ([], []) := rfl
      have := hs i (by simp at hi; omega)
      rw [e, List.getD_cons_succ, show lvl + (i + 1) = lvl + 1 + i by ring]
      exact this

end
end LeanVM.Guest.B1.Whir
