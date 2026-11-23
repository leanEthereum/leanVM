/-
  LeanVM.Guest.B1.Whir.Residuals

  The non-final levels' residual chains and the inner chain they feed.
-/

module

public import LeanVM.Guest.B1.Whir.ResLoop
public import LeanVM.Guest.B1.Whir.LrSound
public import LeanVM.Guest.B1.Whir.RateCfg
public import LeanVM.Guest.B1.Whir.SlowSpec

/-!
# The residuals

A non-final level's residual (`osResidual`): its positions, row and high part materialized, `λ⁻¹`
read from `level_lam_invs`, the dispatch on the rate into `level_residual` (`MeaningLevelResidual`,
`Whir/LrSound.lean`): the chains over all its positions; its zero flag, `is_zero` of
`level_after`, and the dispatch on the rate into `level_residual_slow` (`SlowRet`): `0` where the
flag is, else its unfactored sum (`osResidual_sound`). The level's sums go into `inner_chain`:
`ich[2l + 2] = ich[2l] + scale_l·h_l + slow_l` and `ich[2l + 3] = ich[2l + 1] + β_l·after_l·hh_l`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-- What a level's residual reads: the rate's row (the dispatches' arms), its `level_residual` and
`level_residual_slow` calls' meanings and `is_zero`'s, its row and high part, its positions, `μ`,
its coordinates `Xs` (the fold challenges after its folds, then the tail challenges at `tch`). -/
structure ResIn (rd : Reader) (C : CallRel) (σ : Val) (c : OsCfg) (tch bd lvl : ℕ) (lv : OsLv)
    (D : ℕ → E) (hsv : List E) (Pos : ℕ → E) (mu : E) (Xs : ℕ → E) : Prop where
  rate : LvRate σ c lvl lv
  call : ∀ a r, C (osResidualName lv) a r →
    MeaningLevelResidual lv.queries lv.logCols lv.folds lv.highBits rd a r
  slow : ∀ a r, C (osSlowName c lv) a r → SlowRet lv.queries lv.prefixLen c.yrLog lv.vanish rd a r
  iz : ∀ a r, C "is_zero" a r → MeaningIsZero a r
  van : lv.vanish = lv.logCols * (lv.logCols + 1) / 2
  read : ResRead rd lvl lv (σ (.n bd)) (σ (.n osHs)) D hsv
  posOff : lv.posOff < u128Bound
  rowOff : lvl * ligColsCap < u128Bound
  hsOff : lvl * hsStride < u128Bound
  resOff : lv.resFoldOff < u128Bound
  pos : ∀ k < lv.queries, LoadHolds rd (σ (.n osQpos)) (lv.posOff + k) (Pos k)
  mus : LoadHolds rd (σ (.n osMus)) lvl mu
  fch : ∀ t < lv.prefixLen, LoadHolds rd (σ (.n osFch)) (lv.resFoldOff + t) (Xs t)
  tch : ∀ j < c.yrLog, LoadHolds rd (σ (.n tch)) j (Xs (lv.prefixLen + j))

/-- The chains over a level's positions. -/
def resAll (lv : OsLv) (D : ℕ → E) (hsv : List E) (Pos : ℕ → E) (mu : E) : E × E :=
  resFold (resP lv D) (resH lv hsv) mu (0, 0) ((List.range lv.queries).map Pos)

/-- A level's slow sum at its zero flag `z` and `λ`. -/
def resSlow (c : OsCfg) (lv : OsLv) (Pos Xs : ℕ → E) (lam z : E) : E :=
  slowVal lv.queries (lv.prefixLen + c.yrLog) lv.vanish Pos Xs lam z

/-- **A level's residual**: the dispatch on the rate into `level_residual` (the chains over the
level's positions) and into `level_residual_slow` at the level's zero flag, the inner chain's two
sums advanced by them. -/
theorem osResidual_sound {c : OsCfg} {tch ich bd ls la lvl : ℕ} {lv : OsLv} {D : ℕ → E}
    {hsv : List E} {Pos : ℕ → E} {mu : E} {Xs : ℕ → E}
    (hin : ResIn rd C σ c tch bd lvl lv D hsv Pos mu Xs)
    {mats : List OsMat} (hm : MatsOk σ mats) {k : ℕ}
    (hok : AllOk C rd σ (osResidual c tch ich bd ls la lvl lv mats k).1) :
    MatsOk σ (osResidual c tch ich bd ls la lvl lv mats k).2.1 ∧
    ∃ i0 i1 s b a lam : E, LoadHolds rd (σ (.n ich)) (2 * lvl) i0 ∧
      LoadHolds rd (σ (.n ich)) (2 * lvl + 1) i1 ∧ LoadHolds rd (σ (.n ls)) lvl s ∧
      LoadHolds rd (σ (.n osBetas)) lvl b ∧ LoadHolds rd (σ (.n la)) lvl a ∧
      LoadHolds rd (σ (.n osOodSc)) (lvl + 1) lam ∧
      LoadHolds rd (σ (.n ich)) (2 * lvl + 2)
        (i0 + s * (resAll lv D hsv Pos mu).1 + resSlow c lv Pos Xs lam (zeroOf a)) ∧
      LoadHolds rd (σ (.n ich)) (2 * lvl + 3) (i1 + b * a * (resAll lv D hsv Pos mu).2) := by
  unfold osResidual at hok ⊢
  simp only at hok ⊢
  simp only [allOk_append] at hok
  obtain ⟨⟨⟨⟨⟨⟨hqp, hbp⟩, hhp⟩, hmid⟩, hsp⟩, hfp⟩, hrest⟩ := hok
  have eq := osMatP_val hm hin.posOff hqp
  have m1 := osMatsAfter_ok hm hin.posOff hqp
  have eb := osMatP_val m1 hin.rowOff hbp
  have m2 := osMatsAfter_ok m1 hin.rowOff hbp
  have eh := osMatP_val m2 hin.hsOff hhp
  have m3 := osMatsAfter_ok m2 hin.hsOff hhp
  have es := osMatP_val m3 hin.posOff hsp
  have m4 := osMatsAfter_ok m3 hin.posOff hsp
  have ef := osMatP_val m4 hin.resOff hfp
  have m5 := osMatsAfter_ok m4 hin.resOff hfp
  refine ⟨m5, ?_⟩
  simp only [allOk_cons, allOk_nil, and_true] at hmid hrest
  obtain ⟨hmu, hd, hla, hz⟩ := hmid
  obtain ⟨hlam, hsd, hfin⟩ := hrest
  simp only [stmtOk_atom, holds_load, osLd] at hmu hla hlam
  have emu := loadHolds_unique hmu hin.mus
  have hc := hin.call _ _ (dispatch_rate hin.rate osResidualName hd)
  have hR := hin.read
  have hres := hc D hsv Pos
    (fun s hs ↦ by simp only [List.map_cons, List.getD_cons_succ, List.getD_cons_zero]
                   rw [eb, loadHolds_mul_gen_pow]; exact hR.D s hs)
    hR.len
    (fun c' hc' ↦ by simp only [List.map_cons, List.getD_cons_succ, List.getD_cons_zero]
                     rw [eh, loadHolds_mul_gen_pow]; exact hR.hs c' hc')
    (fun i hi ↦ by simp only [List.map_cons, List.getD_cons_zero]
                   rw [eq, loadHolds_mul_gen_pow]; exact hin.pos i hi)
  simp only [List.map_cons, List.map_nil, List.getD_cons_succ, List.getD_cons_zero, emu] at hres
  have r1 := congrArg (fun l ↦ l.getD 0 0) hres
  have r2 := congrArg (fun l ↦ l.getD 1 0) hres
  simp only [osRun, List.range_succ, List.range_zero, List.nil_append,
    List.cons_append, List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ,
    Nat.add_zero, Nat.add_assoc, Nat.reduceAdd] at r1 r2
  have hP : lrP lv.logCols D = resP lv D := by unfold lrP resP lrVo; rw [hin.van]
  have hH : lrH lv.logCols lv.folds lv.highBits hsv = resH lv hsv := by
    unfold lrH resH lrVo; rw [hin.van]
  rw [hP, hH] at r1 r2
  -- the zero flag
  have hz' := zeroOf_of_meaning (hin.iz _ _ hz)
  -- the slow sum
  have hsl := hin.slow _ _ (dispatch_rate hin.rate (osSlowName c) hsd) Pos Xs
    (fun i hi ↦ by simp only [List.map_cons, List.getD_cons_zero]
                   rw [es, loadHolds_mul_gen_pow]; exact hin.pos i hi)
    (fun t ht ↦ by simp only [List.map_cons, List.getD_cons_succ, List.getD_cons_zero]
                   rw [ef, loadHolds_mul_gen_pow]; exact hin.fch t ht)
    (fun j hj ↦ by simp only [List.map_cons, List.getD_cons_succ, List.getD_cons_zero]
                   exact hin.tch j hj)
  simp only [List.map_cons, List.map_nil, List.getD_cons_succ, List.getD_cons_zero, osRun,
    List.range_succ, List.range_zero, List.nil_append, Nat.add_zero, List.cons.injEq,
    and_true] at hsl
  simp only [stmtOk_atom, holds_load, holds_mul, holds_add, osLd, osMul, osAdd] at hfin
  obtain ⟨l0, l1, m2', a3, a4, s4, l5, l6, l7, m8, m9, a10, s10⟩ := hfin
  refine ⟨_, _, _, _, _, _, l0, l5, l1, l6, hla, hlam, ?_, ?_⟩
  · rw [a4, a3, m2', r1, hsl, hz'] at s4; exact s4
  · rw [a10, m9, m8, r2, loadHolds_unique l7 hla] at s10; exact s10

/-- **Every level's residual**, the levels `lvl ..`. -/
theorem osResiduals_sound {c : OsCfg} {tch ich bd ls la : ℕ}
    (D : ℕ → ℕ → E) (hsv : ℕ → List E) (Pos : ℕ → ℕ → E) (mu : ℕ → E) (Xs : ℕ → ℕ → E) :
    ∀ (lvs : List OsLv) (lvl : ℕ) (mats : List OsMat) (k : ℕ), MatsOk σ mats →
      (∀ i (hi : i < lvs.length), ResIn rd C σ c tch bd (lvl + i) lvs[i] (D (lvl + i)) (hsv (lvl + i))
        (Pos (lvl + i)) (mu (lvl + i)) (Xs (lvl + i))) →
      AllOk C rd σ (osResiduals c tch ich bd ls la lvl lvs mats k).1 →
      ∀ i (hi : i < lvs.length), ∃ i0 i1 s b a lam : E,
        LoadHolds rd (σ (.n ich)) (2 * (lvl + i)) i0 ∧
        LoadHolds rd (σ (.n ich)) (2 * (lvl + i) + 1) i1 ∧ LoadHolds rd (σ (.n ls)) (lvl + i) s ∧
        LoadHolds rd (σ (.n osBetas)) (lvl + i) b ∧ LoadHolds rd (σ (.n la)) (lvl + i) a ∧
        LoadHolds rd (σ (.n osOodSc)) (lvl + i + 1) lam ∧
        LoadHolds rd (σ (.n ich)) (2 * (lvl + i) + 2)
          (i0 + s * (resAll lvs[i] (D (lvl + i)) (hsv (lvl + i)) (Pos (lvl + i)) (mu (lvl + i))).1 +
            resSlow c lvs[i] (Pos (lvl + i)) (Xs (lvl + i)) lam (zeroOf a)) ∧
        LoadHolds rd (σ (.n ich)) (2 * (lvl + i) + 3)
          (i1 + b * a * (resAll lvs[i] (D (lvl + i)) (hsv (lvl + i)) (Pos (lvl + i)) (mu (lvl + i))).2)
  | [], _, _, _, _, _, _, i, hi => absurd hi (by simp)
  | lv :: rest, lvl, mats, k, hm, hin, hok, i, hi => by
    simp only [osResiduals, allOk_append] at hok
    have h0 := osResidual_sound (hin 0 (by simp)) hm hok.1
    rcases i with _ | i
    · simpa using h0.2
    · have := osResiduals_sound D hsv Pos mu Xs rest (lvl + 1) _ _ h0.1 (fun j hj ↦ by
        have := hin (j + 1) (by simp; omega)
        rwa [show lvl + (j + 1) = lvl + 1 + j by ring] at this) hok.2 i (by simpa using hi)
      rw [show lvl + 1 + i = lvl + (i + 1) by ring] at this
      simpa using this

/-- **The inner chain**: from `ich[0] = 0`, `ich[1] = claim`, after `j` levels `ich[2j]` is the
sum of the scales times the product chains plus the slow sums, and `ich[2j + 1]` the claim plus the
sum of the batching scalars times the products after times the high chains. -/
theorem ich_chain {ich ls la : ℕ} {claim : E} (n : ℕ) (Hp Hh Sl : ℕ → E) (sv bv av : ℕ → E)
    (h0 : LoadHolds rd (σ (.n ich)) 0 0) (h1 : LoadHolds rd (σ (.n ich)) 1 claim)
    (hls : ∀ i < n, LoadHolds rd (σ (.n ls)) i (sv i))
    (hbs : ∀ i < n, LoadHolds rd (σ (.n osBetas)) i (bv i))
    (hla : ∀ i < n, LoadHolds rd (σ (.n la)) i (av i))
    (hstep : ∀ i < n, ∃ i0 i1 s b a : E, LoadHolds rd (σ (.n ich)) (2 * i) i0 ∧
      LoadHolds rd (σ (.n ich)) (2 * i + 1) i1 ∧ LoadHolds rd (σ (.n ls)) i s ∧
      LoadHolds rd (σ (.n osBetas)) i b ∧ LoadHolds rd (σ (.n la)) i a ∧
      LoadHolds rd (σ (.n ich)) (2 * i + 2) (i0 + s * Hp i + Sl i) ∧
      LoadHolds rd (σ (.n ich)) (2 * i + 3) (i1 + b * a * Hh i)) :
    ∀ j ≤ n, LoadHolds rd (σ (.n ich)) (2 * j) (∑ i ∈ Finset.range j, (sv i * Hp i + Sl i)) ∧
      LoadHolds rd (σ (.n ich)) (2 * j + 1) (claim + ∑ i ∈ Finset.range j, bv i * av i * Hh i)
  | 0, _ => by simpa using ⟨h0, h1⟩
  | j + 1, hj => by
    obtain ⟨e0, e1⟩ := ich_chain n Hp Hh Sl sv bv av h0 h1 hls hbs hla hstep j (by omega)
    obtain ⟨i0, i1, s, b, a, l0, l1, ls', lb, la', l2, l3⟩ := hstep j (by omega)
    rw [← loadHolds_unique e0 l0, ← loadHolds_unique (hls j (by omega)) ls'] at l2
    rw [← loadHolds_unique e1 l1, ← loadHolds_unique (hbs j (by omega)) lb,
      ← loadHolds_unique (hla j (by omega)) la'] at l3
    refine ⟨?_, ?_⟩
    · rw [show 2 * (j + 1) = 2 * j + 2 by ring, Finset.sum_range_succ, ← add_assoc]; exact l2
    · rw [show 2 * (j + 1) + 1 = 2 * j + 3 by ring, Finset.sum_range_succ, ← add_assoc]; exact l3

end
end LeanVM.Guest.B1.Whir
