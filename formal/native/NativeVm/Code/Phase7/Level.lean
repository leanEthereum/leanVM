module

public import NativeVm.Code.Phase7.LevelTail

/-!
# A non-final level

`levelC` refines `levelAt logN L sW k` (`levelM` of levels `k` and `k + 1`): the level's parameters,
the fold rounds, `μ` and the queries' depth, the next commitment, the high part, the out-of-domain
sample, the queries, `λ`, the openings; then the computing end (`levelTail_b`). The facts the
pieces establish accumulate in one memory fact, each piece keeping it (`Dep`): none writes a word
an earlier fact reads.
-/

@[expose] public section

namespace NativeVm.Code.P7

open Native NativeVm.Model LeanVM.Parameters
open NativeVm.Transcript (wd Env wdisp wd_inj wd_zero eval_cw wp_load wp_store wp_storei wp_reg ctxWork
  toUInt64_succ)

/-- A word outside a fact's words. -/
macro "ntac" : tactic => `(tactic| (
  intro hj
  try simp only [paramsW, nextW, muW, roundW, tableW, WB, qyW, qW, levelW, gslot, powWritten,
      glueWritten, incW, basisWords, basis_off, vecWords, wvecWords, stackClaimCap, claimCap_val,
      levelsWords_val, rowsWords_val] at *
  oomega))

variable {p : Par}

theorem muAfter_eq {L : List Whir.Level} {logN k : Nat} :
    muAfter logN L k = logN - ((L.take (k + 1)).map (·.fold)).sum := rfl

/-- **A non-final level.** -/
theorem levelC_b {L : List Whir.Level} {logN k : Nat} {scales : Array EW} {sW : WhirStateW}
    (hok : LadderOk logN L) (hlog : logN ≤ 30) (hq : ∀ lv ∈ L, 1 ≤ lv.queries)
    (hk : k + 1 < L.length) (hW : WOk L k sW) :
    Refines (fun t s ↦ Base p t s ∧ (LvB p L logN k scales s.mem ∧
        WhirAt s.mem (whirR.at p.env.work) sW) ∧ t.roots.size < Transcript.maxRoots)
      levelC (levelAt logN L sW k)
      (fun sW' t s ↦ (Base p t s ∧ (LvB p L logN (k + 1) scales s.mem ∧
        WhirAt s.mem (whirR.at p.env.work) sW') ∧
        s.reg .r15 = (L.length - 1 - (k + 1)).toUInt64) ∧ WOk L (k + 1) sW')
      (Err p) := by
  have hl6 : L.length ≤ 6 := hok.len.2
  have hg : sW.glued.size = 2 * k := hW.1
  have ha : sW.alphas.size = ((L.take k).map (·.fold)).sum := hW.2.1
  have hg10 : sW.glued.size ≤ gluedCap := by rw [hg, gluedCap_val]; omega
  have hkl : k < L.length := by omega
  unfold levelAt levelM
  rw [getD_lt hkl, getD_lt hk]
  unfold levelC
  -- the level's parameters
  refine pure_then (X' := fun m ↦ LvB p L logN k scales m ∧ WhirAt m (whirR.at p.env.work) sW)
    (R := fun s ↦ Prm p L[k] s.mem ∧ na p cK L[k].queries s.mem)
    ((dep_LvB hl6 _ _ _).and (dep_whirP sW hg10)) (by ltac) (by ltac) (fun _ h ↦ h)
    (fun t s hb hx _ ↦ (paramsC_spec hb.rdi hb.inp hb.workPtr hx.1.2.1 hx.1.1 hkl).mono
      (fun _ h ↦ ⟨⟨⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2.1⟩, h.2.2.2.1⟩, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1⟩) (fun _ h ↦ h)) ?_
  -- the next level's parameters
  refine pure_then (X' := fun m ↦ (LvB p L logN k scales m ∧ WhirAt m (whirR.at p.env.work) sW) ∧
      (Prm p L[k] m ∧ na p cK L[k].queries m)) (R := fun s ↦ Nxt p L[k + 1] s.mem)
    (((dep_LvB hl6 _ _ _).and (dep_whirP sW hg10)).and ((dep_Prm _).and (dep_na _ _)))
    (by ltac) (by ltac) (fun _ h ↦ h)
    (fun t s hb hx _ ↦ (nextC_spec hb.rdi hb.inp hb.workPtr hx.1.1.2.1 hx.1.1.1 hk).mono
      (fun _ h ↦ ⟨⟨h.1, h.2.1⟩, h.2.2.1, h.2.2.2.1⟩) (fun _ h ↦ h)) ?_
  -- the fold rounds
  have hfold : L[k].fold ≤ 6 := (hok.folds k hkl).2.1
  have hsum := (hok.folds k hkl).2.2
  rw [sum_take_succ L hkl] at hsum
  refine m0_then (X := fun m ↦ ((LvB p L logN k scales m ∧ WhirAt m (whirR.at p.env.work) sW) ∧
      (Prm p L[k] m ∧ na p cK L[k].queries m)) ∧ Nxt p L[k + 1] m)
    (I := fun t ↦ t.roots.size < Transcript.maxRoots)
    (X' := fun m ↦ (LvB p L logN k scales m ∧ (Prm p L[k] m ∧ na p cK L[k].queries m)) ∧
      Nxt p L[k + 1] m)
    (Post := fun (x : WhirStateW × Array FoldRoundW) (t : TState) (s : QState) ↦
      (WRd p x.1 x.2 s.mem ∧ x.1.glued = sW.glued ∧
      x.1.alphas.size = sW.alphas.size + L[k].fold ∧ x.2.size = L[k].fold) ∧
      t.roots.size < Transcript.maxRoots) (Wc := roundW)
    (((dep_LvB hl6 _ _ _).and ((dep_Prm _).and (dep_na _ _))).and (dep_Nxt _))
    (by ltac) (by ltac) (by exact fun _ h ↦ ⟨⟨h.1.1.1, h.1.2⟩, h.2⟩)
    (fun m0 ↦ (Refines.keepRoots (foldRounds_roots _ _) (fun r ↦ r.size < Transcript.maxRoots)
      (foldRoundsC_b (p := p) (m0 := m0) (sW := sW) (n := L[k].fold) hfold
        (by rw [ha, stackCap_val]; omega))).mono
      (by exact fun t s ⟨hb, hm, hx, hr⟩ ↦ ⟨⟨hb, hm, hx.1.2.1.1, hx.1.1.2⟩, hr⟩)
      (by exact fun x t s ⟨⟨hb, ⟨hw, hrs, ho⟩, h1, h2, h3⟩, hr⟩ ↦
        ⟨hb, ⟨⟨⟨hw, hrs⟩, h1, h2, h3⟩, hr⟩, ho⟩)
      (fun _ h ↦ h)) fun x ↦ ?_
  obtain ⟨sW1, rounds⟩ := x
  refine Refines.mono (P := fun t s ↦ (Base p t s ∧ ((((LvB p L logN k scales s.mem ∧
      (Prm p L[k] s.mem ∧ na p cK L[k].queries s.mem)) ∧ Nxt p L[k + 1] s.mem) ∧
      WRd p sW1 rounds s.mem)) ∧ t.roots.size < Transcript.maxRoots) ∧
      (sW1.glued = sW.glued ∧ sW1.alphas.size = sW.alphas.size + L[k].fold ∧
        rounds.size = L[k].fold)) ?_
    (by exact fun t s ⟨hb, hx, ⟨hwr, h1, h2, h3⟩, hr⟩ ↦ ⟨⟨hb, ⟨hx, hwr⟩, hr⟩, h1, h2, h3⟩)
    (fun _ _ _ h ↦ h) (fun _ h ↦ h)
  refine Refines.pull fun ⟨hgl1, hal1, hrs1⟩ ↦ ?_
  -- the numbers
  have hg1 : sW1.glued.size ≤ gluedCap := by rw [hgl1]; exact hg10
  have hg2 : sW1.glued.size + 2 ≤ gluedCap := by rw [hgl1, hg, gluedCap_val]; omega
  have hal2 : sW1.alphas.size = ((L.take (k + 1)).map (·.fold)).sum := by
    rw [hal1, ha, sum_take_succ L hkl]
  have hmuA : logN - sW1.alphas.size = muAfter logN L k := by rw [muAfter_eq, hal2]
  have hrt := hok.rates k hkl
  have hrt1 := hok.rates (k + 1) hk
  have hnx := hok.next k hk
  rw [← hmuA] at hrt hnx
  have hmu30 : logN - sW1.alphas.size ≤ 30 := by omega
  have hqk : 1 ≤ L[k].queries := hq _ (List.getElem_mem hkl)
  have hX0 := (((dep_LvB (p := p) hl6 logN k scales).and ((dep_Prm L[k]).and
    (dep_na cK L[k].queries))).and (dep_Nxt L[k + 1])).and (dep_WRd sW1 hg1 rounds)
  -- `μ` and the depth
  refine pure_then (X' := fun m ↦ ((LvB p L logN k scales m ∧
      (Prm p L[k] m ∧ na p cK L[k].queries m)) ∧ Nxt p L[k + 1] m) ∧ WRd p sW1 rounds m)
    (R := fun s ↦ na p cMu (logN - sW1.alphas.size) s.mem ∧
      na p cDepth (logN - sW1.alphas.size + L[k].logInvRate) s.mem) (Wc := muW)
    hX0 (by ltac) (by ltac) (fun _ h ↦ h)
    (fun t s hb hx _ ↦ (muC_spec hb.rdi hb.inp hb.workPtr hx.1.1.1.2.2.2.1 hx.2.1 hx.1.1.2.1.2.1
      (by omega) (by omega)).mono
      (fun _ h ↦ ⟨⟨h.1, h.2.1⟩, h.2.2.1, h.2.2.2.1⟩) (fun _ h ↦ h)) ?_
  have hX1 := hX0.and ((dep_na (p := p) cMu (logN - sW1.alphas.size)).and
    (dep_na cDepth (logN - sW1.alphas.size + L[k].logInvRate)))
  dsimp only [levelShape]
  set mu := logN - sW1.alphas.size with hmu
  -- the next commitment
  refine m0_then (X := fun m ↦ (((LvB p L logN k scales m ∧
      (Prm p L[k] m ∧ na p cK L[k].queries m)) ∧ Nxt p L[k + 1] m) ∧ WRd p sW1 rounds m) ∧
      (na p cMu mu m ∧ na p cDepth (mu + L[k].logInvRate) m))
    (X' := fun m ↦ (((LvB p L logN k scales m ∧
      (Prm p L[k] m ∧ na p cK L[k].queries m)) ∧ Nxt p L[k + 1] m) ∧ WRd p sW1 rounds m) ∧
      (na p cMu mu m ∧ na p cDepth (mu + L[k].logInvRate) m))
    (I := fun t ↦ t.roots.size < Transcript.maxRoots) (Post := fun _ _ _ ↦ True)
    (Wc := fun _ ↦ False) hX1 (by ltac) (fun _ _ h ↦ h) (fun _ h ↦ h)
    (fun m0 t s ⟨hb, hm, hx, hi⟩ ↦ WP.mono (commitC_spec (p := p) (m0 := m0) (n := t.roots.size)
      hnx.1 (by omega) hmu30 (by omega) t s ⟨hb, hm, rfl, hi, hx.2.1, hx.1.1.2.1, hx.1.1.2.2⟩)
      (fun _ ⟨x, t', hr, hb', hmine, _⟩ ↦ ⟨x, t', hr, hb', trivial, Only.of_mine hmine⟩)
      (fun _ h ↦ h)) fun _ ↦ ?_
  -- the high part
  refine m0_step (Y := fun high m ↦ EWArr m (wd p.env.work hiO) high)
    (R := fun high ↦ high.size = L[k].fold)
    (Wc := fun j ↦ hiO ≤ j ∧ j < hiO + 2 * L[k].fold) hX1 (by ltac) (by ltac)
    (fun m0 ↦ (readScalarsC_spec (p := p) (m0 := m0) (n := L[k].fold) (cnt := cFold) (dst := hiO)
      ⟨by oomega, by oomega⟩ ⟨by oomega, by oomega⟩ (by omega)).mono
      (fun t s ⟨hb, hm, hx, _⟩ ↦ ⟨hb, hm, hx.1.1.1.2.1.1⟩)
      (fun x t s ⟨hb, h1, h2, h3⟩ ↦ ⟨hb, ⟨h1, h2⟩, h3⟩) (fun _ h ↦ h)) fun high hhs ↦ ?_
  have hX2 := hX1.and (dep_ewarr (p := p) hiO high)
  -- the out-of-domain grind and sample
  refine grind_then (Rg := fun _ ↦ True) (k := 15) (by decide) (by decide) (by decide) hX2
    (by ltac) RegOk.true ?_
  refine m0_step (Y := fun op m ↦ EWArr m (wd p.env.work spO) op) (R := fun op ↦ op.size = mu)
    (Wc := fun j ↦ spO ≤ j ∧ j < spO + 2 * mu) hX2 (by ltac) (by ltac)
    (fun m0 ↦ (sampleChallengesC_spec (p := p) (m0 := m0) (n := mu) (cnt := cMu) (dst := spO)
      ⟨by oomega, by oomega⟩ ⟨by oomega, by oomega⟩ (by omega)).mono
      (fun t s ⟨hb, hm, hx, _⟩ ↦ ⟨hb, hm, hx.1.2.1⟩)
      (fun x t s ⟨hb, h1, h2, h3⟩ ↦ ⟨hb, ⟨h1, h2⟩, h3⟩) (fun _ h ↦ h)) fun op hps ↦ ?_
  have hX3 := hX2.and (dep_ewarr (p := p) spO op)
  refine readTo_then (Rg := fun _ ↦ True) hX3 (by ltac) ⟨by ntac, by ntac⟩ ⟨by oomega, by oomega⟩
    RegOk.true fun ov ↦ ?_
  have hX4 := hX3.and (dep_ea (p := p) (tmpO + 28) ov)
  -- the queries
  refine grind_then (Rg := fun _ ↦ True) (k := 17) (by decide) (by decide) (by decide) hX4
    (by ltac) RegOk.true ?_
  refine m0_step (Y := fun qs m ↦ WVec m (wd p.env.work queriesR.off) queryCap qs)
    (R := fun qs ↦ qs.size = L[k].queries) (Wc := qW) hX4 (by ltac) (by ltac)
    (fun m0 ↦ (sampleQueriesC_spec (p := p) (m0 := m0) (depth := mu + L[k].logInvRate)
      (count := L[k].queries) (by omega) (by omega) (by rw [queryCap_val]; omega)).mono
      (fun t s ⟨hb, hm, hx, _⟩ ↦ ⟨hb, hm, hx.1.1.1.2.2, hx.1.1.1.1.1.1.2.2⟩)
      (fun x t s ⟨hb, h1, h2, h3⟩ ↦ ⟨hb, ⟨h1, h2⟩, h3⟩) (fun _ h ↦ h)) fun qs hqs ↦ ?_
  have hX5 := hX4.and (dep_wvec (p := p) queriesR.off qs)
  -- `λ`
  refine sampleTo_then (Rg := fun _ ↦ True) hX5 (by ltac) ⟨by ntac, by ntac⟩
    ⟨by oomega, by oomega⟩ RegOk.true fun lam ↦ ?_
  have hX6 := hX5.and (dep_ea (p := p) (tmpO + 26) lam)
  -- the openings
  refine m0_step (Y := fun rows m ↦ RowsW p rows qs.size m) (R := fun _ ↦ True) (Wc := qyW) hX6
    (by ltac) (by ltac)
    (fun m0 t s ⟨hb, hm, hx, _⟩ ↦ WP.mono (queryC_spec (p := p) (m0 := m0) (k := k) (qs := qs)
      (by omega) (by omega) t s ⟨hb, hm, hx.1.1.1.1.1.1.1.1.1.2.1, hx.1.2⟩)
      (fun _ ⟨x, t', hr, w, hb', h1, h2, h3, h4, h5⟩ ↦ ⟨x, t', hr, hb', ⟨⟨w, h1, h2, h3, h4⟩, trivial⟩, h5⟩)
      (fun _ h ↦ h)) fun rows _ ↦ ?_
  -- the end
  exact (levelTail_b (p := p) (logN := logN) (scales := scales) (sW := sW1) (rounds := rounds)
    (mu := mu) (high := high) (oodPoint := op) (oodValue := ov) (lam := lam) (qs := qs) (rows := rows)
    hl6 hk hg2 hmu30 (by omega) hps (Z := WOk L (k + 1)) (wOk_glue hkl hW hgl1 hal1 hlog)).mono
    (fun t s ⟨hb, ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hL, ⟨_, _, _, hJ⟩, _⟩, _⟩, hWR⟩, hMU, _⟩, hHI⟩, hOP⟩, hOV⟩, hQS⟩, hLM⟩,
      hRW⟩, _⟩ ↦ ⟨hb, ⟨hL, hWR, hMU, by rw [hhs]; exact hJ, hHI, hOP, hOV, hQS, hLM, hRW⟩, trivial⟩)
    (fun _ _ _ h ↦ h) (fun _ h ↦ h)

end NativeVm.Code.P7
