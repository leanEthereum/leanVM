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
dispatch's arguments and returns (`osResCallsL`) and the calls' values (`resCV`).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Guest.Memory LeanVM.Protocol.Verifier

@[expose] public section

variable {M : Reader → Prop} {H : CallRel → Reader → Prop}

/-- **A fixed buffer's shifted pointer, materialized.** -/
theorem osMatP_blkA {P : List (ℕ × ℕ × ℕ)} {mats : List OsMat} {base off k : ℕ} (σ : Val)
    (hbase : base < k) (hmb : MatsBelow k mats) (hm : ∀ C rd, HM M H C rd → MatsOk σ mats)
    (hoff : off < u128Bound) :
    BlkA M H σ k (osMatP P mats base off k).2.2 (osMatP P mats base off k).1
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
    (hla : la < k) (hk : 43 ≤ k) (ha : AgreeBelow k σ σ') :
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

/-- The arguments and returns of `osResidual c rts tch ich bd ls la lvl lv mats k`'s call of
`level_residual`. -/
def osResCall1 (c : OsCfg) (rts : List (List ℕ)) (bd lvl : ℕ) (mats : List OsMat) (k : ℕ) :
    List V × List V :=
  let rt := rts.getD lvl []
  let bp := osMatP c.plan mats bd (lvl * ligColsCap) (k + 1)
  let m2 := osMatsAfter c.plan mats bd (lvl * ligColsCap) (k + 1)
  let hp := osMatP c.plan m2 osHs (lvl * hsStride) bp.2.2
  ([.n k, .n bp.2.1, .n hp.2.1, .n hp.2.2, .n (rt.getD 2 0), .n (rt.getD 3 0)], osRun (hp.2.2 + 1) 2)

theorem osResidual_next (c : OsCfg) (rts : List (List ℕ)) (tch ich bd ls la lvl : ℕ) (lv : OsLv)
    (mats : List OsMat) (k : ℕ) : k ≤ (osResidual c rts tch ich bd ls la lvl lv mats k).2.2 := by
  unfold osResidual
  dsimp only
  generalize hb : osMatP c.plan mats bd (lvl * ligColsCap) (k + 1) = bp
  have b : k + 1 ≤ bp.2.2 := hb ▸ osMatP_k _ _ _ _ _
  generalize hh : osMatP c.plan _ osHs (lvl * hsStride) bp.2.2 = hp
  have d : bp.2.2 ≤ hp.2.2 := hh ▸ osMatP_k _ _ _ _ _
  generalize hf : osMatP c.plan _ osFch lv.resFoldOff (hp.2.2 + 5) = fp
  have f : hp.2.2 + 5 ≤ fp.2.2 := hf ▸ osMatP_k _ _ _ _ _
  omega

theorem osResidual_allocs (c : OsCfg) (rts : List (List ℕ)) (tch ich bd ls la lvl : ℕ) (lv : OsLv)
    (mats : List OsMat) (k : ℕ) :
    (osResidual c rts tch ich bd ls la lvl lv mats k).1.filterMap Stmt.allocSz = [] := by
  simp only [osResidual, List.cons_append, List.filterMap_cons, List.filterMap_append, osMatP_allocs]
  rfl

/-- `level_residual`'s honest arguments at a level. -/
def resArgsV (σ : Val) (bd lvl : ℕ) (lv : OsLv) (mu : E) : List E :=
  [σ (.n osQpos) * gen ^ lv.posOff, σ (.n bd) * gen ^ (lvl * ligColsCap),
    σ (.n osHs) * gen ^ (lvl * hsStride), mu, gen ^ (lv.queries / resBatch), gen ^ (lv.queries % resBatch)]

/-- **The non-final levels' residuals' calls' values**: each level's `level_residual`, `is_zero` of its
product `A` and `level_residual_slow`, at the rate's selector `x` and the pointers of `query_positions`,
`basis_d`, `level_hs`, `fold_challenges` and `tail_challenges`. -/
def resCV (x qp bd hs fch tc : E) (mu A P Q Lam SL : ℕ → E) : List OsLv → ℕ → List (List E)
  | [], _ => []
  | lv :: rest, lvl => [qp * gen ^ lv.posOff, bd * gen ^ (lvl * ligColsCap), hs * gen ^ (lvl * hsStride), mu lvl,
      gen ^ (lv.queries / resBatch), gen ^ (lv.queries % resBatch), P lvl, Q lvl] :: [A lvl, zeroOf (A lvl)] ::
      [x, qp * gen ^ lv.posOff, fch * gen ^ lv.resFoldOff, tc, Lam lvl, zeroOf (A lvl), SL lvl] ::
      resCV x qp bd hs fch tc mu A P Q Lam SL rest (lvl + 1)

/-- **A level's residual, honestly**: the positions' pointer from the level's `g^posOff`, the call of
`level_residual` at its arguments, returning `P`, `Q`; the zero flag of `a`; the dispatch into
`level_residual_slow`, returning `SL`; the sums stored. -/
theorem osResidual_complete {c : OsCfg} {rts : List (List ℕ)} {tch ich bd ls la lvl : ℕ} {lv : OsLv}
    {mats : List OsMat} {k : ℕ} {σ : Val} {mu i0 i1 s b a P Q lam SL : E}
    (hbd : bd < k) (hich : ich < k) (hls : ls < k) (hla : la < k) (htch : tch < k) (hk : 43 ≤ k)
    (hmb : MatsBelow k mats) (hmo : ∀ C rd, HM M H C rd → MatsOk σ mats)
    (hrt : ∀ i < 4, (rts.getD lvl []).getD i 0 < k)
    (hrp : σ (.n ((rts.getD lvl []).getD 0 0)) = gen ^ lv.posOff)
    (hrb : σ (.n ((rts.getD lvl []).getD 2 0)) = gen ^ (lv.queries / resBatch))
    (hrr : σ (.n ((rts.getD lvl []).getD 3 0)) = gen ^ (lv.queries % resBatch))
    (hlc : lvl * ligColsCap < u128Bound) (hhs : lvl * hsStride < u128Bound)
    (hro : lv.resFoldOff < u128Bound) (hiz : IsZeroC (HM M H))
    (hrate : ∀ C rd, HM M H C rd → LvRate σ c lvl lv)
    (hm : ∀ C rd, HM M H C rd → ResMemD rd σ lvl ich ls la mu i0 i1 s b a P Q lam SL)
    (hC : ∀ C rd, HM M H C rd → C (osResidualName lv) (resArgsV σ bd lvl lv mu) [P, Q])
    (hS : ∀ C rd, HM M H C rd → C (osSlowName c lv)
      [σ (.n osQpos) * gen ^ lv.posOff, σ (.n osFch) * gen ^ lv.resFoldOff, σ (.n tch), lam, zeroOf a]
        [SL]) :
    BlkA M H σ k (osResidual c rts tch ich bd ls la lvl lv mats k).2.2
      (osResidual c rts tch ich bd ls la lvl lv mats k).1
      (fun σ' ↦ MatsOk σ' (osResidual c rts tch ich bd ls la lvl lv mats k).2.1 ∧
        MatsBelow (osResidual c rts tch ich bd ls la lvl lv mats k).2.2
          (osResidual c rts tch ich bd ls la lvl lv mats k).2.1 ∧
        (osResCall1 c rts bd lvl mats k).1.map σ' = resArgsV σ bd lvl lv mu ∧
        (osResCall1 c rts bd lvl mats k).2.map σ' = [P, Q] ∧
        (osSlowCall1 c tch bd lvl lv mats k).1.map σ' =
          [σ (.n osQpos) * gen ^ lv.posOff, σ (.n osFch) * gen ^ lv.resFoldOff, σ (.n tch), lam,
            zeroOf a] ∧
        (osSlowCall1 c tch bd lvl lv mats k).2.map σ' = [SL] ∧
        cvOf (osResidual c rts tch ich bd ls la lvl lv mats k).1 σ' =
          [resArgsV σ bd lvl lv mu ++ [P, Q], [a, zeroOf a], σ (.n osRate) ::
            ([σ (.n osQpos) * gen ^ lv.posOff, σ (.n osFch) * gen ^ lv.resFoldOff, σ (.n tch), lam,
              zeroOf a] ++ [SL])]) := by
  unfold osResidual osResCall1 osSlowCall1
  dsimp only
  set rt := rts.getD lvl [] with hrtD
  set bp := osMatP c.plan mats bd (lvl * ligColsCap) (k + 1) with hbp
  set m2 := osMatsAfter c.plan mats bd (lvl * ligColsCap) (k + 1) with hm2
  set hp := osMatP c.plan m2 osHs (lvl * hsStride) bp.2.2 with hhp
  set m3 := osMatsAfter c.plan m2 osHs (lvl * hsStride) bp.2.2 with hm3
  set j := hp.2.2 with hj
  set fp := osMatP c.plan m3 osFch lv.resFoldOff (j + 5) with hfp
  set m5 := osMatsAfter c.plan m3 osFch lv.resFoldOff (j + 5) with hm5
  set l := fp.2.2 with hl
  have r0 := hrt 0 (by omega)
  have r2 := hrt 2 (by omega)
  have r3 := hrt 3 (by omega)
  have k2 : k + 1 ≤ bp.2.2 := osMatP_k _ _ _ _ _
  have k3 : bp.2.2 ≤ j := osMatP_k _ _ _ _ _
  have k5 : j + 5 ≤ l := osMatP_k _ _ _ _ _
  have l2 : bp.2.1 < bp.2.2 := osMatP_lt _ _ _ _ _ (show bd < k + 1 by omega)
  have l3 : hp.2.1 < j := osMatP_lt _ _ _ _ _ (show 24 < bp.2.2 by omega)
  have l5 : fp.2.1 < l := osMatP_lt _ _ _ _ _ (show 16 < j + 5 by omega)
  have mb1 : MatsBelow (k + 1) mats := fun m hm ↦ by
    obtain ⟨x, y, z⟩ := hmb m hm; exact ⟨by omega, by omega, by omega⟩
  have mb2 : MatsBelow bp.2.2 m2 := osMatP_below mb1 (show bd < k + 1 by omega)
  have mb3 : MatsBelow j m3 := osMatP_below mb2 (show 24 < bp.2.2 by omega)
  have mb3' : MatsBelow (j + 5) m3 := fun m hm ↦ by
    obtain ⟨x, y, z⟩ := mb3 m hm; exact ⟨by omega, by omega, by omega⟩
  have mb5 : MatsBelow l m5 := osMatP_below mb3' (show 16 < j + 5 by omega)
  -- the positions' pointer
  have b1 : BlkA M H σ k (k + 1) [osMul k osQpos (rt.getD 0 0)]
      (fun σ' ↦ σ' (.n k) = σ (.n osQpos) * gen ^ lv.posOff ∧ MatsOk σ' mats) :=
    blk_lst [σ (.n osQpos) * gen ^ lv.posOff] (by simp) fun C rd hH σ' ha hv ↦ by
      have v0 := hv 0 (by simp)
      simp only [List.getD_cons_zero, Nat.add_zero] at v0
      refine ⟨?_, v0, matsOk_agree (hmo C rd hH) hmb fun i hi ↦ ha i hi⟩
      simp only [allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_mul, osMul]
      rw [v0, ha osQpos (by show 36 < k; omega), ha _ r0, hrp]
  have b2 := BlkA.seq (M := M) (H := H) (show k ≤ k + 1 by omega) k2 b1 (B := bp.1)
    (OutB := fun σ' ↦ σ' (.n bp.2.1) = σ (.n bd) * gen ^ (lvl * ligColsCap) ∧ MatsOk σ' m2 ∧
      MatsBelow bp.2.2 m2) fun σ1 ha1 ho1 ↦ by
      have h := osMatP_blkA (M := M) (H := H) (P := c.plan) (mats := mats) (base := bd) (off := lvl * ligColsCap)
        (k := k + 1) σ1 (by omega) mb1 (fun C rd hH ↦ (ho1 C rd hH).2) hlc
      rw [ha1 _ hbd] at h
      exact h
  have b3 := BlkA.seq (M := M) (H := H) (by omega) k3 b2 (B := hp.1)
    (OutB := fun σ' ↦ σ' (.n hp.2.1) = σ (.n osHs) * gen ^ (lvl * hsStride) ∧ MatsOk σ' m3 ∧
      MatsBelow j m3) fun σ1 ha1 ho1 ↦ by
      have h := osMatP_blkA (M := M) (H := H) (P := c.plan) (mats := m2) (base := osHs) (off := lvl * hsStride)
        (k := bp.2.2) σ1 (show 24 < bp.2.2 by omega) mb2 (fun C rd hH ↦ (ho1 C rd hH).2.2.1) hhs
      rw [ha1 osHs (by show 24 < k; omega)] at h
      exact h
  -- `μ`
  have b4 := BlkA.seq (M := M) (H := H) (show k ≤ j by omega) (show j ≤ j + 1 by omega) b3
    (B := [osLd j osMus lvl]) (OutB := fun σ' ↦ σ' (.n j) = mu) fun σ1 ha1 _ ↦ by
      refine BlkA.ofHM (lstF j [mu]) fun C rd hH σ' ha hr ↦ ?_
      have v : σ' (.n j) = mu := by
        have := lstF_at hr (by simp) 0 (by simp)
        simpa using this
      refine ⟨?_, v⟩
      simp only [allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_load, osLd]
      rw [v, ha osMus (by show 22 < j; omega), ha1 osMus (by show 22 < k; omega)]
      exact (hm C rd hH).mus
  -- the call of `level_residual`
  have hargsV : ∀ σ1 : Val, AgreeBelow k σ σ1 → (∀ C rd, HM M H C rd →
      ((σ1 (.n k) = σ (.n osQpos) * gen ^ lv.posOff ∧ MatsOk σ1 mats) ∧
        σ1 (.n bp.2.1) = σ (.n bd) * gen ^ (lvl * ligColsCap) ∧ MatsOk σ1 m2 ∧ MatsBelow bp.2.2 m2) ∧
        σ1 (.n hp.2.1) = σ (.n osHs) * gen ^ (lvl * hsStride) ∧ MatsOk σ1 m3 ∧ MatsBelow j m3) →
      (∀ C rd, HM M H C rd → σ1 (.n j) = mu) → ∀ C rd, HM M H C rd →
      [k, bp.2.1, hp.2.1, j, rt.getD 2 0, rt.getD 3 0].map (fun i ↦ σ1 (.n i)) = resArgsV σ bd lvl lv mu :=
    fun σ1 ha1 h1 h2 C rd hH ↦ by
    obtain ⟨⟨⟨e0, -⟩, e2, -⟩, e3, -⟩ := h1 C rd hH
    simp only [List.map_cons, List.map_nil, e0, e2, e3, h2 C rd hH, ha1 _ r2, ha1 _ r3, hrb, hrr]
    rfl
  have b5 := BlkA.seq (M := M) (H := H) (show k ≤ j + 1 by omega) (show j + 1 ≤ j + 1 + 2 by omega) b4
    (B := [.call (osResidualName lv) ([k, bp.2.1, hp.2.1, j, rt.getD 2 0, rt.getD 3 0].map V.n)
      (osRun (j + 1) 2)])
    (OutB := fun σ' ↦ [k, bp.2.1, hp.2.1, j, rt.getD 2 0, rt.getD 3 0].map (fun i ↦ σ' (.n i)) =
        resArgsV σ bd lvl lv mu ∧ ∀ j' < 2, σ' (.n (j + 1 + j')) = [P, Q].getD j' 0) fun σ1 ha1 ho1 ↦ by
      have hargs : ∀ i ∈ [k, bp.2.1, hp.2.1, j, rt.getD 2 0, rt.getD 3 0], i < j + 1 := fun i hi ↦ by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      have hA := hargsV σ1 ha1 (fun C rd hH ↦ (ho1 C rd hH).1) (fun C rd hH ↦ (ho1 C rd hH).2)
      have h := call_blk (M := M) (H := H) (σ := σ1) (r := j + 1) (n := 2) (f := osResidualName lv)
        (args := [k, bp.2.1, hp.2.1, j, rt.getD 2 0, rt.getD 3 0]) [P, Q] rfl hargs
        (fun C rd hH ↦ by rw [hA C rd hH]; exact hC C rd hH)
      refine BlkA.monoH h fun C rd hH σ' ha hv ↦ ⟨?_, hv⟩
      rw [← hA C rd hH]
      exact List.map_congr_left fun i hi ↦ ha _ (hargs i hi)
  have c5 := b5.mono (Out' := fun σ' ↦ MatsOk σ' m3 ∧
      [k, bp.2.1, hp.2.1, j, rt.getD 2 0, rt.getD 3 0].map (fun i ↦ σ' (.n i)) = resArgsV σ bd lvl lv mu ∧
      σ' (.n (j + 1)) = P ∧ σ' (.n (j + 2)) = Q) fun σ' ho ↦ by
    obtain ⟨⟨⟨⟨-, -⟩, -, mo3, -⟩, -⟩, eargs, erets⟩ := ho
    exact ⟨mo3, eargs, by simpa using erets 0 (by omega), by simpa using erets 1 (by omega)⟩
  -- the zero flag
  have c6 := BlkA.seq (M := M) (H := H) (show k ≤ j + 1 + 2 by omega) (show j + 1 + 2 ≤ j + 5 by omega) c5
    (B := [osLd (j + 3) la lvl, .call "is_zero" [.n (j + 3)] [.n (j + 4)]])
    (OutB := fun σ' ↦ σ' (.n (j + 4)) = zeroOf a ∧ σ' (.n (j + 3)) = a) fun σ1 ha1 _ ↦ by
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
      exact ⟨⟨(hm C rd hH).laf, hiz C rd hH a⟩, rfl, rfl⟩
  -- the slow call's pointer
  have c8 := BlkA.seq (M := M) (H := H) (show k ≤ j + 5 by omega) k5 c6
    (B := fp.1) (OutB := fun σ' ↦ σ' (.n fp.2.1) = σ (.n osFch) * gen ^ lv.resFoldOff ∧
      MatsOk σ' m5 ∧ MatsBelow l m5) fun σ1 ha1 ho1 ↦ by
      have h := osMatP_blkA (M := M) (H := H) (P := c.plan) (mats := m3) (base := osFch) (off := lv.resFoldOff)
        (k := j + 5) σ1 (show 16 < j + 5 by omega) mb3' (fun C rd hH ↦ (ho1 C rd hH).1.1) hro
      rw [ha1 osFch (by show 16 < k; omega)] at h
      exact h
  have c8' := c8.mono (Out' := fun σ' ↦ MatsOk σ' m5 ∧
      [k, bp.2.1, hp.2.1, j, rt.getD 2 0, rt.getD 3 0].map (fun i ↦ σ' (.n i)) = resArgsV σ bd lvl lv mu ∧
      σ' (.n (j + 1)) = P ∧ σ' (.n (j + 2)) = Q ∧ σ' (.n (j + 4)) = zeroOf a ∧
      σ' (.n fp.2.1) = σ (.n osFch) * gen ^ lv.resFoldOff ∧ σ' (.n (j + 3)) = a) fun σ' ho ↦
    ⟨ho.2.2.1, ho.1.1.2.1, ho.1.1.2.2.1, ho.1.1.2.2.2, ho.1.2.1, ho.2.1, ho.1.2.2⟩
  -- `λ`
  have c9 := BlkA.seq (M := M) (H := H) (show k ≤ l by omega) (show l ≤ l + 1 by omega) c8'
    (B := [osLd l osOodSc (lvl + 1)]) (OutB := fun σ' ↦ σ' (.n l) = lam) fun σ1 ha1 _ ↦
      blk_lst [lam] (by simp) fun C rd hH σ' ha hv ↦ by
        have v0 := hv 0 (by simp)
        simp only [List.getD_cons_zero, Nat.add_zero] at v0
        simp only [osLd, allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_load]
        rw [v0, ha osOodSc (by show 28 < l; omega), ha1 osOodSc (by show 28 < k; omega)]
        exact ⟨(hm C rd hH).lam, rfl⟩
  -- the dispatch into `level_residual_slow`
  have c10 := BlkA.seq (M := M) (H := H) (show k ≤ l + 1 by omega) (show l + 1 ≤ l + 1 + 1 by omega) c9
    (B := [.dispatch (.n osRate) ((c.lvAt lvl).map (osSlowName c))
      ([k, fp.2.1, tch, l, j + 4].map V.n) (osRun (l + 1) 1)])
    (OutB := fun σ' ↦ ∀ j' < 1, σ' (.n (l + 1 + j')) = [SL].getD j' 0) fun σ1 ha1 ho1 ↦
      rateDisp_blk (M := M) (H := H) (σ := σ1) (c := c) (lvl := lvl) (lv := lv) (r := l + 1) (n := 1)
        (osSlowName c) (args := [k, fp.2.1, tch, l, j + 4]) [SL] rfl
        (fun i hi ↦ by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl | rfl | rfl | rfl <;> omega) (by omega)
        (fun C rd hH ↦ by
          obtain ⟨ri, hri, hx, hlen, hlv⟩ := hrate C rd hH
          exact ⟨ri, hri, by rw [ha1 _ (show 0 < k by omega)]; exact hx, hlen, hlv⟩)
        (fun C rd hH ↦ by
          obtain ⟨⟨-, eargs, -, -, ez, ef, -⟩, el⟩ := ho1 C rd hH
          have ek : σ1 (.n k) = σ (.n osQpos) * gen ^ lv.posOff := by
            have := congrArg List.head? eargs
            simpa [resArgsV] using this
          simp only [List.map_cons, List.map_nil]
          rw [ek, ez, ef, el, ha1 _ htch]
          exact hS C rd hH)
  -- the sums
  have c11 := BlkA.seq (M := M) (H := H) (show k ≤ l + 1 + 1 by omega) (show l + 1 + 1 ≤ l + 2 + 11 by omega)
    c10 (B := resB ich ls la lvl (j + 1) (j + 2) (l + 1) (l + 2)) (OutB := fun _ ↦ True)
    fun σ2 ha2 ho2 ↦ by
      have e : l + 1 + 1 = l + 2 := by omega
      rw [e]
      exact resB_complete (M := M) (H := H) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega)
        (fun C rd hH ↦ by
          obtain ⟨⟨⟨-, -, eP, eQ, -⟩, -⟩, eS⟩ := ho2 C rd hH
          exact ⟨eP, eQ, by simpa using eS 0 (by omega)⟩)
        (fun C rd hH ↦ by
          have hM := (hm C rd hH).agree hich hls hla hk (fun i hi ↦ ha2 i (by omega))
          exact ⟨hM.li0, hM.lsc, hM.li1, hM.lbe, hM.laf, hM.st0, hM.st1⟩)
  refine BlkA.congr (BlkA.mono c11.agree fun σ' ho ↦ ?_) (by
    simp only [resB, List.append_assoc, List.cons_append, List.nil_append]; rfl)
  obtain ⟨⟨⟨⟨⟨mo5, eargs, eP, eQ, ez, ef, ea⟩, el⟩, eS⟩, -⟩, hag⟩ := ho
  have ek : σ' (.n k) = σ (.n osQpos) * gen ^ lv.posOff := by
    have := congrArg List.head? eargs
    simpa [resArgsV] using this
  have ea' : [V.n k, V.n bp.2.1, V.n hp.2.1, V.n j, V.n (rt.getD 2 0), V.n (rt.getD 3 0)].map σ' =
      resArgsV σ bd lvl lv mu := by rw [← eargs]; rfl
  have er' : (osRun (j + 1) 2).map σ' = [P, Q] := by
    rw [osRun_map, show List.range 2 = [0, 1] from rfl]
    simp only [List.map_cons, List.map_nil, Nat.add_zero]
    rw [eP, show j + 1 + 1 = j + 2 by omega, eQ]
  have es1 : [V.n k, V.n fp.2.1, V.n tch, V.n l, V.n (j + 4)].map σ' =
      [σ (.n osQpos) * gen ^ lv.posOff, σ (.n osFch) * gen ^ lv.resFoldOff, σ (.n tch), lam, zeroOf a] := by
    simp only [List.map_cons, List.map_nil]
    rw [ek, ef, hag _ htch, el, ez]
  have es2 : (osRun (l + 1) 1).map σ' = [SL] := by
    rw [osRun_map, show List.range 1 = [0] from rfl]
    simp only [List.map_cons, List.map_nil, Nat.add_zero]
    rw [show SL = [SL].getD 0 0 from rfl, ← eS 0 (by omega), Nat.add_zero]
  refine ⟨mo5, fun m hm' ↦ ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨x, y, z⟩ := mb5 m hm'; exact ⟨by omega, by omega, by omega⟩
  · show ([V.n k, V.n bp.2.1, V.n hp.2.1, V.n j, V.n (rt.getD 2 0), V.n (rt.getD 3 0)]).map σ' = _
    rw [← eargs]; rfl
  · rw [osRun_map, show List.range 2 = [0, 1] from rfl]
    simp only [List.map_cons, List.map_nil, Nat.add_zero]
    rw [eP, show j + 1 + 1 = j + 2 by omega, eQ]
  · simp only [List.map_cons, List.map_nil]
    have et : σ' (.n tch) = σ (.n tch) := hag _ htch
    rw [ek, ef, et, el, ez]
  · rw [osRun_map, show List.range 1 = [0] from rfl]
    simp only [List.map_cons, List.map_nil, Nat.add_zero]
    rw [show SL = [SL].getD 0 0 from rfl, ← eS 0 (by omega), Nat.add_zero]
  · refine (cvOf_of_calls (vs := [[V.n k, V.n bp.2.1, V.n hp.2.1, V.n j, V.n (rt.getD 2 0), V.n (rt.getD 3 0)] ++
      osRun (j + 1) 2, [V.n (j + 3), V.n (j + 4)], V.n osRate :: ([V.n k, V.n fp.2.1, V.n tch, V.n l, V.n (j + 4)] ++
      osRun (l + 1) 1)]) ?_ σ').trans ?_
    · have cb : bp.1.filterMap callVs = [] := osMatP_calls _ _ _ _ _
      have ch : hp.1.filterMap callVs = [] := osMatP_calls _ _ _ _ _
      have cf : fp.1.filterMap callVs = [] := osMatP_calls _ _ _ _ _
      simp only [List.filterMap_cons, List.filterMap_append, cb, ch, cf, List.filterMap_nil, callVs, osLd, osMul,
        osAdd, List.nil_append, List.append_nil, List.cons_append]
    · show [([V.n k, V.n bp.2.1, V.n hp.2.1, V.n j, V.n (rt.getD 2 0), V.n (rt.getD 3 0)] ++
        osRun (j + 1) 2).map σ', [σ' (.n (j + 3)), σ' (.n (j + 4))],
        σ' (.n osRate) :: ([V.n k, V.n fp.2.1, V.n tch, V.n l, V.n (j + 4)] ++ osRun (l + 1) 1).map σ'] = _
      rw [List.map_append, List.map_append, ea', er', es1, es2, ea, ez, hag osRate (by show 0 < k; omega)]

theorem osResiduals_next (c : OsCfg) (rts : List (List ℕ)) (tch ich bd ls la : ℕ) :
    ∀ (lvs : List OsLv) (lvl : ℕ) (mats : List OsMat) (k : ℕ),
      k ≤ (osResiduals c rts tch ich bd ls la lvl lvs mats k).2
  | [], _, _, _ => le_rfl
  | lv :: rest, lvl, mats, k => by
    simp only [osResiduals]
    exact le_trans (osResidual_next c rts tch ich bd ls la lvl lv mats k)
      (osResiduals_next c rts tch ich bd ls la rest (lvl + 1) _ _)

theorem osResiduals_allocs (c : OsCfg) (rts : List (List ℕ)) (tch ich bd ls la : ℕ) :
    ∀ (lvl : ℕ) (lvs : List OsLv) (mats : List OsMat) (k : ℕ),
      (osResiduals c rts tch ich bd ls la lvl lvs mats k).1.filterMap Stmt.allocSz = []
  | _, [], _, _ => rfl
  | lvl, lv :: rest, mats, k => by
    simp only [osResiduals, List.filterMap_append, osResidual_allocs,
      osResiduals_allocs c rts tch ich bd ls la (lvl + 1), List.nil_append]

/-- **Every non-final level's residual, honestly**, the levels `lvl ..`: each call of
`level_residual` at its arguments, returning `P`, `Q`, and dispatch into `level_residual_slow`,
returning `SL`. -/
theorem osResiduals_complete {c : OsCfg} {rts : List (List ℕ)} {tch ich bd ls la : ℕ} (hiz : IsZeroC (HM M H))
    (mu I0 I1 S B A P Q Lam SL : ℕ → E) :
    ∀ (lvs : List OsLv) (lvl : ℕ) (mats : List OsMat) (k : ℕ) (σ : Val),
      bd < k → ich < k → ls < k → la < k → tch < k → 43 ≤ k → MatsBelow k mats →
      (∀ C rd, HM M H C rd → MatsOk σ mats) →
      (∀ i < lvs.length, (lvl + i) * ligColsCap < u128Bound ∧ (lvl + i) * hsStride < u128Bound ∧
        (lvs.getD i default).resFoldOff < u128Bound) →
      (∀ i < lvs.length, RtVals σ rts k (lvl + i) (lvs.getD i default)) →
      (∀ i < lvs.length, ∀ C rd, HM M H C rd → LvRate σ c (lvl + i) (lvs.getD i default)) →
      (∀ i < lvs.length, ∀ C rd, HM M H C rd → ResMemD rd σ (lvl + i) ich ls la (mu (lvl + i)) (I0 (lvl + i))
        (I1 (lvl + i)) (S (lvl + i)) (B (lvl + i)) (A (lvl + i)) (P (lvl + i)) (Q (lvl + i))
        (Lam (lvl + i)) (SL (lvl + i))) →
      (∀ i < lvs.length, ∀ C rd, HM M H C rd → C (osResidualName (lvs.getD i default))
        (resArgsV σ bd (lvl + i) (lvs.getD i default) (mu (lvl + i))) [P (lvl + i), Q (lvl + i)]) →
      (∀ i < lvs.length, ∀ C rd, HM M H C rd → C (osSlowName c (lvs.getD i default))
        [σ (.n osQpos) * gen ^ (lvs.getD i default).posOff,
          σ (.n osFch) * gen ^ (lvs.getD i default).resFoldOff, σ (.n tch), Lam (lvl + i),
          zeroOf (A (lvl + i))] [SL (lvl + i)]) →
      BlkA M H σ k (osResiduals c rts tch ich bd ls la lvl lvs mats k).2
        (osResiduals c rts tch ich bd ls la lvl lvs mats k).1
        (fun σ' ↦ (∀ i < lvs.length,
          ((osResCallsL c rts tch ich bd ls la lvl lvs mats k).getD i ([], [])).1.map σ' =
            resArgsV σ bd (lvl + i) (lvs.getD i default) (mu (lvl + i)) ∧
          ((osResCallsL c rts tch ich bd ls la lvl lvs mats k).getD i ([], [])).2.map σ' =
            [P (lvl + i), Q (lvl + i)] ∧
          ((osSlowCallsL c rts tch ich bd ls la lvl lvs mats k).getD i ([], [])).1.map σ' =
            [σ (.n osQpos) * gen ^ (lvs.getD i default).posOff,
              σ (.n osFch) * gen ^ (lvs.getD i default).resFoldOff, σ (.n tch), Lam (lvl + i),
              zeroOf (A (lvl + i))] ∧
          ((osSlowCallsL c rts tch ich bd ls la lvl lvs mats k).getD i ([], [])).2.map σ' = [SL (lvl + i)]) ∧
          cvOf (osResiduals c rts tch ich bd ls la lvl lvs mats k).1 σ' =
            resCV (σ (.n osRate)) (σ (.n osQpos)) (σ (.n bd)) (σ (.n osHs)) (σ (.n osFch)) (σ (.n tch))
              mu A P Q Lam SL lvs lvl)
  | [], _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ =>
    BlkA.nil fun _ _ ↦ ⟨fun i hi ↦ absurd hi (by simp), rfl⟩
  | lv :: rest, lvl, mats, k, σ, hbd, hich, hls, hla, htch, hk, hmb, hmo, hoff, hrv, hrate, hm, hC, hS => by
    have o0 := hoff 0 (by simp)
    simp only [List.getD_cons_zero, Nat.add_zero] at o0
    have v0 := hrv 0 (by simp)
    simp only [List.getD_cons_zero, Nat.add_zero] at v0
    have h0 := osResidual_complete (M := M) (H := H) (c := c) (rts := rts) (tch := tch) (ich := ich) (bd := bd)
      (ls := ls) (la := la) (lvl := lvl) (lv := lv) (mats := mats) (k := k) (σ := σ) (mu := mu lvl)
      (i0 := I0 lvl) (i1 := I1 lvl) (s := S lvl) (b := B lvl) (a := A lvl) (P := P lvl) (Q := Q lvl)
      (lam := Lam lvl) (SL := SL lvl) hbd hich hls hla htch hk hmb hmo v0.1 v0.2.1 v0.2.2.1 v0.2.2.2
      o0.1 o0.2.1 o0.2.2 hiz
      (fun C rd hH ↦ by simpa using hrate 0 (by simp) C rd hH)
      (fun C rd hH ↦ by simpa using hm 0 (by simp) C rd hH)
      (fun C rd hH ↦ by simpa using hC 0 (by simp) C rd hH)
      (fun C rd hH ↦ by simpa using hS 0 (by simp) C rd hH)
    set r := osResidual c rts tch ich bd ls la lvl lv mats k with hr
    have hn : k ≤ r.2.2 := osResidual_next c rts tch ich bd ls la lvl lv mats k
    have hn2 := osResiduals_next c rts tch ich bd ls la rest (lvl + 1) r.2.1 r.2.2
    have hB := BlkA.seq (M := M) (H := H) hn hn2 h0
      (B := (osResiduals c rts tch ich bd ls la (lvl + 1) rest r.2.1 r.2.2).1)
      (OutB := fun σ' ↦ (∀ i < rest.length,
        ((osResCallsL c rts tch ich bd ls la (lvl + 1) rest r.2.1 r.2.2).getD i ([], [])).1.map σ' =
          resArgsV σ bd (lvl + 1 + i) (rest.getD i default) (mu (lvl + 1 + i)) ∧
        ((osResCallsL c rts tch ich bd ls la (lvl + 1) rest r.2.1 r.2.2).getD i ([], [])).2.map σ' =
          [P (lvl + 1 + i), Q (lvl + 1 + i)] ∧
        ((osSlowCallsL c rts tch ich bd ls la (lvl + 1) rest r.2.1 r.2.2).getD i ([], [])).1.map σ' =
          [σ (.n osQpos) * gen ^ (rest.getD i default).posOff,
            σ (.n osFch) * gen ^ (rest.getD i default).resFoldOff, σ (.n tch), Lam (lvl + 1 + i),
            zeroOf (A (lvl + 1 + i))] ∧
        ((osSlowCallsL c rts tch ich bd ls la (lvl + 1) rest r.2.1 r.2.2).getD i ([], [])).2.map σ' =
          [SL (lvl + 1 + i)]) ∧
        cvOf (osResiduals c rts tch ich bd ls la (lvl + 1) rest r.2.1 r.2.2).1 σ' =
          resCV (σ (.n osRate)) (σ (.n osQpos)) (σ (.n bd)) (σ (.n osHs)) (σ (.n osFch)) (σ (.n tch))
            mu A P Q Lam SL rest (lvl + 1))
      fun σ1 ha1 ho1 ↦ BlkA.of_ne fun ⟨C0, rd0, hH0⟩ ↦ by
      have e1 : σ1 (.n osQpos) = σ (.n osQpos) := ha1 osQpos (by show 36 < k; omega)
      have e2 : σ1 (.n bd) = σ (.n bd) := ha1 _ hbd
      have e3 : σ1 (.n osHs) = σ (.n osHs) := ha1 osHs (by show 24 < k; omega)
      have e4 : σ1 (.n osFch) = σ (.n osFch) := ha1 osFch (by show 16 < k; omega)
      have e5 : σ1 (.n tch) = σ (.n tch) := ha1 _ htch
      have eR : ∀ l lv m, resArgsV σ1 bd l lv m = resArgsV σ bd l lv m := fun l lv m ↦ by
        simp only [resArgsV, e1, e2, e3]
      have h := osResiduals_complete hiz mu I0 I1 S B A P Q Lam SL rest (lvl + 1) r.2.1 r.2.2 σ1
        (lt_of_lt_of_le hbd hn) (lt_of_lt_of_le hich hn) (lt_of_lt_of_le hls hn) (lt_of_lt_of_le hla hn)
        (lt_of_lt_of_le htch hn) (le_trans hk hn)
        (ho1 C0 rd0 hH0).2.1 (fun C rd hH ↦ (ho1 C rd hH).1)
        (fun i hi ↦ by
          have := hoff (i + 1) (by simp; omega)
          simpa [show lvl + (i + 1) = lvl + 1 + i by ring] using this)
        (fun i hi ↦ by
          have := (hrv (i + 1) (by simp; omega)).agree hn ha1
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
          rw [eR]
          simpa [show lvl + (i + 1) = lvl + 1 + i by ring] using this)
        fun i hi C rd hH ↦ by
          have := hS (i + 1) (by simp; omega) C rd hH
          rw [e1, e4, e5]
          simpa [show lvl + (i + 1) = lvl + 1 + i by ring] using this
      have e0 : σ1 (.n osRate) = σ (.n osRate) := ha1 _ (by show 0 < k; omega)
      exact h.mono fun σ' hv ↦ ⟨fun i hi ↦ by rw [← e1, ← e4, ← e5, ← eR]; exact hv.1 i hi,
        by rw [hv.2, e0, e1, e2, e3, e4, e5]⟩
    refine (hB.congr rfl).mono fun σ' ⟨⟨_, _, a0, r0, s0, t0, cv0⟩, hs, hcv⟩ ↦ ⟨fun i hi ↦ ?_, ?_⟩
    rcases i with _ | i
    · have e0 : (osResCallsL c rts tch ich bd ls la lvl (lv :: rest) mats k).getD 0 ([], []) =
          osResCall1 c rts bd lvl mats k := rfl
      have e0' : (osSlowCallsL c rts tch ich bd ls la lvl (lv :: rest) mats k).getD 0 ([], []) =
          osSlowCall1 c tch bd lvl lv mats k := rfl
      simp only [List.getD_cons_zero, Nat.add_zero]
      rw [e0, e0']
      exact ⟨a0, r0, s0, t0⟩
    · have e : (osResCallsL c rts tch ich bd ls la lvl (lv :: rest) mats k).getD (i + 1) ([], []) =
          (osResCallsL c rts tch ich bd ls la (lvl + 1) rest r.2.1 r.2.2).getD i ([], []) := rfl
      have e' : (osSlowCallsL c rts tch ich bd ls la lvl (lv :: rest) mats k).getD (i + 1) ([], []) =
          (osSlowCallsL c rts tch ich bd ls la (lvl + 1) rest r.2.1 r.2.2).getD i ([], []) := rfl
      have := hs i (by simp at hi; omega)
      rw [e, e', List.getD_cons_succ, show lvl + (i + 1) = lvl + 1 + i by ring]
      exact this
    show cvOf (r.1 ++ _) σ' = _
    rw [cvOf_append, cv0, hcv]
    rfl

end
end LeanVM.Guest.B1.Whir
