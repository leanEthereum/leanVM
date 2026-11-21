module

public import NativeVm.Code.Phase7.Code
public import NativeVm.Code.Phase7.Link
public import NativeVm.Code.Phase7.Bundles

/-!
# A non-final level's end

After the openings, a level only computes: the query weights (`powC`), the subspace table
(`tableC`), the batched value (`batchC`), the glued claims (`glueC`) and the next index (`incC`).
`levelTail_b`: from the facts the transcript part leaves (`TailX`), these refine the level's result
`glueLevel …`.
-/

@[expose] public section

namespace NativeVm.Code.P7

open Native NativeVm.Model LeanVM.Parameters
open NativeVm.Transcript (wd Env wdisp wd_inj wd_zero eval_cw wp_load wp_store wp_storei wp_reg ctxWork
  toUInt64_succ)

theorem rowsWords_val : rowsWords = 16384 := by decide

/-- The words `incC` writes. -/
def incW (j : Nat) : Prop := j = cIdx ∨ j = cN

/-- Discharge the words' side conditions. -/
macro "ltac" : tactic => `(tactic| (
  intro j hj
  try simp only [paramsW, nextW, muW, roundW, tableW, WB, qyW, qW, levelW, gslot, powWritten,
      glueWritten, incW, basisWords, basis_off, vecWords, wvecWords, stackClaimCap, claimCap_val,
      levelsWords_val, rowsWords_val] at *
  oomega))

variable {p : Par} {s : QState} {F : QState → Prop}

/-! ## The next index -/

theorem incC_core {k n : Nat} (hrdi : s.reg .rdi = p.env.ctx) (hin : Inputs p.env p.inp s.mem)
    (hwp : s.mem (wd p.env.ctx ctxWork) = some p.env.work)
    (hidx : NatAt s.mem (wd p.env.work cIdx) k) (hn : NatAt s.mem (wd p.env.work cN) (n + 1))
    (hk : k + 1 < 2 ^ 64) :
    WP incC s (fun s' ↦ NatAt s'.mem (wd p.env.work cIdx) (k + 1) ∧
      NatAt s'.mem (wd p.env.work cN) n ∧ s'.reg .r15 = n.toUInt64 ∧
      ∀ a, (∀ j, incW j → a ≠ wd p.env.work j) → s'.mem a = s.mem a) F := by
  have hww := workWords_ge p.inp.bytecode.size
  have hsome : ∀ j, mineLo ≤ j → j < dataEnd → (s.mem (wd p.env.work j)).isSome := fun j _ h2 ↦
    hin.workSome j (by rw [dataEnd_val] at h2; omega)
  unfold incC ldW
  refine wp_load (eval_cw hrdi _) hwp ?_
  refine ldw_wp (env := p.env) (by rsimp) (by rsimp; exact hidx.2) ?_
  refine wp_reg rfl ?_
  refine stw_wp (env := p.env) (by rsimp) (by rsimp; exact hsome _ (by oomega) (by oomega)) ?_
  refine ldw_wp (env := p.env) (by rsimp) (by wsimp; exact hn.2) ?_
  refine wp_reg rfl ?_
  refine stw_wp (env := p.env) (by rsimp) (by wsimp; exact hsome _ (by oomega) (by oomega)) ?_
  refine NativeVm.Transcript.wp_done_gen fun s' hs' ↦ ?_
  refine ⟨⟨hk, ?_⟩, ⟨by have := hn.1; omega, ?_⟩, ?_, fun a ha ↦ ?_⟩
  · rw [← hs']; wsimp
    rw [show ((1 : Int64).toUInt64) = 1 from rfl, toUInt64_succ]
  · rw [← hs']; wsimp
    rw [show ((1 : Int64).toUInt64) = 1 from rfl, NativeVm.Field.toUInt64_succ_sub]
  · rw [← hs']; rsimp
    rw [NativeVm.Field.toUInt64_succ_sub]
  · rw [← hs']
    repeat (first | rw [QState.setReg_mem] | rw [setMem_ne _ _ ?_])
    all_goals exact ha _ (by unfold incW; oomega)

/-- **The next index**, `r15` the levels left. -/
theorem incC_spec {k n : Nat} (hrdi : s.reg .rdi = p.env.ctx) (hin : Inputs p.env p.inp s.mem)
    (hwp : s.mem (wd p.env.ctx ctxWork) = some p.env.work)
    (hidx : NatAt s.mem (wd p.env.work cIdx) k) (hn : NatAt s.mem (wd p.env.work cN) (n + 1))
    (hk : k + 1 < 2 ^ 64) :
    WP incC s (fun s' ↦ NatAt s'.mem (wd p.env.work cIdx) (k + 1) ∧
      NatAt s'.mem (wd p.env.work cN) n ∧ s'.reg .r15 = n.toUInt64 ∧
      FrM p.env s s' ∧ Only p.env incW s.mem s'.mem) F :=
  WP.mono (NativeVm.Transcript.WP.frame (incC_core hrdi hin hwp hidx hn hk))
    (fun _ ⟨⟨h1, h2, h3, hm⟩, hd, hreg⟩ ↦ ⟨h1, h2, h3,
      (frM_only (hreg .rdi (by decide)) hd hm (fun j hj ↦ by unfold incW at hj; oomega)).1,
      (frM_only (hreg .rdi (by decide)) hd hm (fun j hj ↦ by unfold incW at hj; oomega)).2⟩)
    fun _ h ↦ h.1

/-! ## The end of a level -/

/-- What the transcript part of a level leaves. -/
abbrev TailX (p : Par) (L : List Whir.Level) (logN k : Nat) (scales : Array EW) (sW : WhirStateW)
    (rounds : Array FoldRoundW) (mu : Nat) (high oodPoint : Array EW) (oodValue : EW)
    (qs : Array UInt64) (lam : EW) (rows : Array (Array UInt64)) (m : UInt64 → Option UInt64) :
    Prop :=
  LvB p L logN k scales m ∧ WRd p sW rounds m ∧ na p cMu mu m ∧ na p cJ high.size m ∧
    EWArr m (wd p.env.work hiO) high ∧ EWArr m (wd p.env.work spO) oodPoint ∧
    ea p (tmpO + 28) oodValue m ∧ WVec m (wd p.env.work queriesR.off) queryCap qs ∧
    ea p (tmpO + 26) lam m ∧ RowsW p rows qs.size m

/-- `LvB` at the next index, after `incC`. -/
theorem lvB_succ {L : List Whir.Level} {logN k : Nat} {scales : Array EW}
    {m m' : UInt64 → Option UInt64} (hl : L.length ≤ 6) (h : LvB p L logN k scales m)
    (ho : Only p.env incW m m') (hi : na p cIdx (k + 1) m') (hn : na p cN (L.length - 1 - (k + 1)) m') :
    LvB p L logN (k + 1) scales m' := by
  have e : ∀ j, mineLo ≤ j → j < dataEnd → ¬ incW j → m' (wd p.env.work j) = m (wd p.env.work j) :=
    ho
  have hb : basisWords = 325 := by decide
  refine ⟨LevelsAt.congr (fun j hj ↦ by
      rw [levelsWords_val] at hj
      rw [wd_wd]; exact e _ (by oomega) (by oomega) (by unfold incW; oomega)) hl h.1,
    hi, hn, h.2.2.2.1.congr (e _ (by oomega) (by oomega) (by unfold incW; oomega)),
    h.2.2.2.2.congr fun j hj ↦ ?_⟩
  have hb' : vecWords stackClaimCap = 325 := by decide
  rw [Region.at, wd_wd]
  exact e _ (by oomega) (by rw [hb'] at hj; oomega) (by unfold incW; oomega)

/-- **A level's end**: the query weights, the subspace table, the batched value, the glued claims,
the next index. -/
theorem levelTail_b {L : List Whir.Level} {logN k : Nat} {scales : Array EW} {sW : WhirStateW}
    {rounds : Array FoldRoundW} {mu : Nat} {high oodPoint : Array EW} {oodValue lam : EW}
    {qs : Array UInt64} {rows : Array (Array UInt64)}
    (hl6 : L.length ≤ 6) (hk : k + 1 < L.length) (hg : sW.glued.size + 2 ≤ gluedCap)
    (hmu30 : mu ≤ 30) (hhs : high.size ≤ 6) (hps : oodPoint.size = mu) {Z : WhirStateW → Prop}
    (hZ : Z (glueLevel sW lam mu oodPoint oodValue qs (powers lam qs.size)
      (batchedW k mu rounds high qs rows (powers lam qs.size)))) :
    Refines (fun t s ↦ Base p t s ∧
        TailX p L logN k scales sW rounds mu high oodPoint oodValue qs lam rows s.mem ∧ True)
      (blk [powC, tableC, batchC, glueC, incC])
      (pure (glueLevel sW lam mu oodPoint oodValue qs (powers lam qs.size)
        (batchedW k mu rounds high qs rows (powers lam qs.size))) : VM WhirStateW)
      (fun sW' t s ↦ (Base p t s ∧ (LvB p L logN (k + 1) scales s.mem ∧
        WhirAt s.mem (whirR.at p.env.work) sW') ∧
        s.reg .r15 = (L.length - 1 - (k + 1)).toUInt64) ∧ Z sW')
      (Err p) := by
  have hg10 : sW.glued.size ≤ gluedCap := by omega
  have hgc : sW.glued.size + 2 ≤ 10 := hg
  have hT := (dep_LvB (p := p) hl6 logN k scales).and ((dep_WRd sW hg10 rounds).and
    ((dep_na cMu mu).and ((dep_na cJ high.size).and ((dep_ewarr hiO high).and
    ((dep_ewarr spO oodPoint).and ((dep_ea (tmpO + 28) oodValue).and
    ((dep_wvec queriesR.off qs).and ((dep_ea (tmpO + 26) lam).and (dep_RowsW rows qs.size)))))))))
  -- the query weights
  refine pure_then (X' := TailX p L logN k scales sW rounds mu high oodPoint oodValue qs lam rows)
    (R := fun s ↦ EVec s.mem (wd p.env.work (gslot (sW.glued.size + 1) + gluedWOff)) queryCap
        (powers lam qs.size) ∧
      s.mem (wd p.env.work cK) = some (wd p.env.work (gslot (sW.glued.size + 1) + gluedWOff + 1)))
    (Wc := powWritten sW.glued.size) hT (by ltac) (by ltac) (fun _ h ↦ h)
    (fun t s hb hx _ ↦ (powC_spec hb.rdi hb.inp hb.workPtr hx.2.1.1 hg hx.2.2.2.2.2.2.2.2.1
      hx.2.2.2.2.2.2.2.1.2.1 hx.2.2.2.2.2.2.2.1.1).mono
      (fun _ h ↦ ⟨⟨h.1, h.2.1⟩, h.2.2.1, h.2.2.2⟩) (fun _ h ↦ h)) ?_
  have hP := hT.and ((dep_evec (p := p) (gslot (sW.glued.size + 1) + gluedWOff) queryCap
    (powers lam qs.size)).and (dep_word (env := p.env) cK
      (some (wd p.env.work (gslot (sW.glued.size + 1) + gluedWOff + 1)))))
  -- the subspace table
  refine pure_then (X := fun m ↦ TailX p L logN k scales sW rounds mu high oodPoint oodValue qs lam
      rows m ∧ (EVec m (wd p.env.work (gslot (sW.glued.size + 1) + gluedWOff)) queryCap
        (powers lam qs.size) ∧
      m (wd p.env.work cK) = some (wd p.env.work (gslot (sW.glued.size + 1) + gluedWOff + 1))))
    (X' := fun m ↦ TailX p L logN k scales sW rounds mu high oodPoint oodValue qs lam
      rows m ∧ (EVec m (wd p.env.work (gslot (sW.glued.size + 1) + gluedWOff)) queryCap
        (powers lam qs.size) ∧
      m (wd p.env.work cK) = some (wd p.env.work (gslot (sW.glued.size + 1) + gluedWOff + 1))))
    (R := fun s ↦ TableAt s.mem (wd p.env.work tabO) (subspaceTable mu)) (Wc := tableW)
    hP (by ltac) (by ltac) (fun _ h ↦ h)
    (fun t s hb hx _ ↦ (tableC_spec hb.rdi hb.inp hb.workPtr hx.1.2.2.1 hmu30)) ?_
  have hQ := hP.and (dep_table (p := p) mu hmu30)
  -- the batched value
  refine pure_then (X := fun m ↦ (TailX p L logN k scales sW rounds mu high oodPoint oodValue qs lam
      rows m ∧ (EVec m (wd p.env.work (gslot (sW.glued.size + 1) + gluedWOff)) queryCap
        (powers lam qs.size) ∧
      m (wd p.env.work cK) = some (wd p.env.work (gslot (sW.glued.size + 1) + gluedWOff + 1)))) ∧
      TableAt m (wd p.env.work tabO) (subspaceTable mu))
    (X' := fun m ↦ (TailX p L logN k scales sW rounds mu high oodPoint oodValue qs lam
      rows m ∧ (EVec m (wd p.env.work (gslot (sW.glued.size + 1) + gluedWOff)) queryCap
        (powers lam qs.size) ∧
      m (wd p.env.work cK) = some (wd p.env.work (gslot (sW.glued.size + 1) + gluedWOff + 1)))) ∧
      TableAt m (wd p.env.work tabO) (subspaceTable mu))
    (R := fun s ↦ EWAt s.mem (wd p.env.work (tmpO + 16))
      (batchedW k mu rounds high qs rows (powers lam qs.size))) (Wc := WB)
    hQ (by ltac) (by ltac) (fun _ h ↦ h)
    (fun t s hb hx _ ↦ ?_) ?_
  · obtain ⟨⟨⟨hL, ⟨-, hR⟩, hmu, hcj, hhi, -, -, hq, -, w, hrows, hrs, hwid, hwd⟩, hqw, hcK⟩, htab⟩ := hx
    exact batchC_spec hb.rdi hb.inp hb.workPtr hL.2.1 hmu hmu30 hq hrows hrs hwid hwd hR hhi hhs hcj
      htab hcK (by have := hqw.2.2; rwa [wd_wd] at this) (powers_size' _ _) (by
        rw [powers_size']; have := hq.1; simp only [gslot] at *; vomega)
  -- the glued claims
  refine pure_then (X := fun m ↦ ((TailX p L logN k scales sW rounds mu high oodPoint oodValue qs
      lam rows m ∧ (EVec m (wd p.env.work (gslot (sW.glued.size + 1) + gluedWOff)) queryCap
        (powers lam qs.size) ∧
      m (wd p.env.work cK) = some (wd p.env.work (gslot (sW.glued.size + 1) + gluedWOff + 1)))) ∧
      TableAt m (wd p.env.work tabO) (subspaceTable mu)) ∧ EWAt m (wd p.env.work (tmpO + 16))
        (batchedW k mu rounds high qs rows (powers lam qs.size)))
    (X' := LvB p L logN k scales)
    (R := fun s ↦ WhirAt s.mem (whirR.at p.env.work) (glueLevel sW lam mu oodPoint oodValue qs
      (powers lam qs.size) (batchedW k mu rounds high qs rows (powers lam qs.size))))
    (Wc := glueWritten sW.glued.size)
    (dep_LvB hl6 logN k scales) (by ltac) (by ltac) (fun _ h ↦ h.1.1.1.1)
    (fun t s hb hx _ ↦ ?_) ?_
  · obtain ⟨⟨⟨⟨-, ⟨hw, -⟩, hmu, -, -, hpt, hov, hq, hlam, -⟩, hqw, -⟩, -⟩, hbt⟩ := hx
    exact glueC_spec hb.rdi hb.inp hb.workPtr hw hg hlam hov hbt hmu hmu30 hpt hps hq hqw
  -- the next index
  have hgs : (glueLevel sW lam mu oodPoint oodValue qs (powers lam qs.size)
      (batchedW k mu rounds high qs rows (powers lam qs.size))).glued.size = sW.glued.size + 2 := by
    simp [glueLevel]
  refine Refines.pure fun t s ⟨hb, ⟨hL, hW⟩, _⟩ ↦ WP.blk_cons (WP.mono (incC_spec (k := k)
    (n := L.length - 1 - (k + 1)) hb.rdi hb.inp hb.workPtr hL.2.1 (by
      have := hL.2.2.1; rwa [show L.length - 1 - k = L.length - 1 - (k + 1) + 1 by omega] at this)
    (by omega)) (fun s' ⟨h1, h2, h3, hf, ho⟩ ↦ WP.blk_nil ⟨⟨hb.frM hf, ⟨lvB_succ hl6 hL ho h1 h2,
      keepX (dep_whirP _ (by rw [hgs]; exact hg))
        (by intro j hj; simp only [hgs, gslot] at hj; oomega)
        (by intro j hj hw; simp only [hgs, gslot] at hj; unfold incW at hw; oomega) ho hW⟩, h3⟩,
      hZ⟩) (fun _ h ↦ h))

/-- The model's facts after a non-final level. -/
theorem wOk_glue {L : List Whir.Level} {k logN : Nat} {sW sW1 : WhirStateW} {lam oodValue batched : EW}
    {oodPoint : Array EW} {qs : Array UInt64} {qw : Array EW} (hkl : k < L.length)
    (hW : WOk L k sW) (hgl : sW1.glued = sW.glued)
    (hal : sW1.alphas.size = sW.alphas.size + L[k].fold) (hlog : logN ≤ 30) :
    WOk L (k + 1) (glueLevel sW1 lam (logN - sW1.alphas.size) oodPoint oodValue qs qw batched) := by
  obtain ⟨h1, h2, h3⟩ := hW
  refine ⟨by simp [glueLevel, hgl, h1]; omega, by simp only [glueLevel]; rw [hal, h2, sum_take_succ L hkl],
    fun g hg ↦ ?_⟩
  simp only [glueLevel, Array.mem_append, hgl] at hg
  rcases hg with hg | hg
  · obtain ⟨a, b⟩ := h3 g hg
    exact ⟨by simp only [glueLevel]; omega, b⟩
  · simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact ⟨le_rfl, fun _ _ _ h ↦ by cases h⟩
    · exact ⟨le_rfl, fun _ _ _ h ↦ by cases h; omega⟩

end NativeVm.Code.P7
