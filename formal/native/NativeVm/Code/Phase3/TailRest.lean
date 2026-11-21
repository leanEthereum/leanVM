module

public import NativeVm.Code.Phase3.TailSide
public import NativeVm.Code.Phase3.Claims
public import NativeVm.Code.Phase3.BusInit

/-!
# Phase 3 after the transcript: the claims, the forms, the totals

`tlBus`: the bus `verifyBusBalance` returns, by sides (`tlAcc`). `tl_rest`: from the values and the
fingerprints (`TlVals`), `tailCode`'s last six parts store the claims at `claimsR` and the bus at
`busR`. The forms of a side other than the one `accumulateSide` adds to are kept (`tl_acc_other`).
-/

@[expose] public section

namespace NativeVm.Code.P3

open Native NativeVm.Model NativeVm.Code NativeVm.Transcript LeanVM.Parameters
  LeanVM.Protocol.Verifier

variable {env : Env} {inp : Input} {s : QState}

/-- **The bus by sides**: the claims, the GKR point, the forms after the three sides, the totals. -/
def tlBus (layout : LayoutW) (weights : Array EW) (beta : EW) (point trees memory : Array EW)
    (mf bf share : EW) (bp : Array EW) : BusResultW :=
  ⟨#[⟨memory0, point.extract 0 layout.logMemory, memory.getD 0 0⟩,
      ⟨memory1, point.extract 0 layout.logMemory, memory.getD 1 0⟩,
      ⟨memoryFinalCounters, point.extract 0 layout.logMemory, mf⟩,
      ⟨bytecodeFinalCounters, point.extract 0 layout.logBytecode, bf⟩],
    bp, point,
    (tlAcc (tlAcc (tlAcc forms0 0 layout weights beta point
      (fingerprints weights memory (point.extract 0 layout.logMemory)
        (point.extract 0 layout.logBytecode) share (gpow 0) 1 1) (trees.getD 0 0)).1 1 layout
      weights beta point
      (fingerprints weights memory (point.extract 0 layout.logMemory)
        (point.extract 0 layout.logBytecode) share (gpow (2 ^ layout.logBytecode - 1)) mf bf)
      (trees.getD 1 0)).1 2 layout weights beta point #[] (trees.getD 2 0)).1,
    #[(tlAcc forms0 0 layout weights beta point
        (fingerprints weights memory (point.extract 0 layout.logMemory)
          (point.extract 0 layout.logBytecode) share (gpow 0) 1 1) (trees.getD 0 0)).2,
      (tlAcc (tlAcc forms0 0 layout weights beta point
        (fingerprints weights memory (point.extract 0 layout.logMemory)
          (point.extract 0 layout.logBytecode) share (gpow 0) 1 1) (trees.getD 0 0)).1 1 layout
        weights beta point
        (fingerprints weights memory (point.extract 0 layout.logMemory)
          (point.extract 0 layout.logBytecode) share (gpow (2 ^ layout.logBytecode - 1)) mf bf)
        (trees.getD 1 0)).2,
      (tlAcc (tlAcc (tlAcc forms0 0 layout weights beta point
        (fingerprints weights memory (point.extract 0 layout.logMemory)
          (point.extract 0 layout.logBytecode) share (gpow 0) 1 1) (trees.getD 0 0)).1 1 layout
        weights beta point
        (fingerprints weights memory (point.extract 0 layout.logMemory)
          (point.extract 0 layout.logBytecode) share (gpow (2 ^ layout.logBytecode - 1)) mf bf)
        (trees.getD 1 0)).1 2 layout weights beta point #[] (trees.getD 2 0)).2]⟩

/-! ## The forms of the other sides -/

theorem tl_forms0 (t side : Nat) : (forms0.getD t #[]).getD side #[] = #[] := by
  simp only [forms0, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases tablesW[t]? with
  | none => rfl
  | some _ => rcases side with _ | _ | _ | side <;> rfl

theorem tl_sfStep_other {side s' t : Nat} {ws : Array EW} {β : EW} (h : s' ≠ side)
    (acc : Array (Array FormW) × EW) (x : (EW × EW) × BusBlockW) :
    (((sfStep side ws β acc x).1).getD t #[]).getD s' #[] = (acc.1.getD t #[]).getD s' #[] := by
  unfold sfStep
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_modify]
  split
  · cases acc.1[t]? with
    | none => rfl
    | some row =>
      simp only [Option.map_some, Option.getD_some, Array.getElem?_modify, Ne.symm h, ↓reduceIte]
  · rfl

theorem tl_fold_other {side s' t : Nat} {ws : Array EW} {β : EW} (h : s' ≠ side) :
    ∀ (l : List ((EW × EW) × BusBlockW)) (acc : Array (Array FormW) × EW),
      ((l.foldl (sfStep side ws β) acc).1.getD t #[]).getD s' #[] = (acc.1.getD t #[]).getD s' #[]
  | [], _ => rfl
  | x :: l, acc => by rw [List.foldl_cons, tl_fold_other h l, tl_sfStep_other h]

/-- **`accumulateSide` keeps the forms of the other sides.** -/
theorem tl_acc_other {forms : Array (Array FormW)} {side s' t : Nat} {layout : LayoutW}
    {weights : Array EW} {beta : EW} {point ffp : Array EW} {tv : EW} (h : s' ≠ side) :
    ((tlAcc forms side layout weights beta point ffp tv).1.getD t #[]).getD s' #[] =
      (forms.getD t #[]).getD s' #[] := by
  rw [tlAcc, accumulateSide_split, sideFold_eq]
  exact tl_fold_other h _ _

/-! ## The rest of `tailCode` -/

theorem tl_claimsAt {ws : List Region} {s' : QState} {cs : Array ColumnClaimW}
    (hw : Wrote env ws s s') (hc : ∀ r ∈ ws, 15569 + 12161 ≤ r.off ∨ r.stop ≤ 15569)
    (hws : ∀ r ∈ ws, r.stop ≤ 2 ^ 61) (h : ClaimsAt s.mem (claimsR.at env.work) cs) :
    ClaimsAt s'.mem (claimsR.at env.work) cs := by
  refine h.congr ?_
  rw [Region.at, claimsR_off, show claimsWords = 12161 by decide]
  exact tl_same hw hc (by norm_num) hws

theorem tl_claimsR : claimsR = ⟨15569, 12161⟩ := by
  rw [show claimsR = ⟨claimsR.off, claimsR.size⟩ from rfl, claimsR_off, claimsR_size]

theorem tl_busTailR : busTailR = ⟨13960, 133⟩ := by
  unfold busTailR; rw [busR_off]; rfl

theorem tl_memFinalAt : memFinalR.at env.work = wd env.work 52844 := by
  show wd env.work (scratchR.off + 174) = _; rw [scratchR_off]
theorem tl_bcFinalAt : bcFinalR.at env.work = wd env.work 52846 := by
  show wd env.work (scratchR.off + 176) = _; rw [scratchR_off]
theorem tl_totalsAt : totalsR.at env.work = wd env.work 52872 := by
  show wd env.work (scratchR.off + 202) = _; rw [scratchR_off]

/-- **The claims, the forms, the totals**: `tailCode`'s last six parts. -/
theorem tl_rest {layout : LayoutW} {rate : Nat} {point weights trees memory bp : Array EW}
    {beta mf bf share : EW}
    (h : TlIn env inp layout rate point weights trees memory beta mf bf share s)
    (hps : point.size < 64) (hws : weights.size = 16) (hts : trees.size = 3) (hms : memory.size = 2)
    (v : TlVals env layout point weights memory mf bf share s) :
    WP (blk [claimsCode, formsInit, blk [selCode 0, formsCode 0, totalCode 0],
        blk [selCode 1, formsCode 1, totalCode 1], blk [selCode 2, formsCode 2, totalCode 2],
        busTail]) s
      (fun s' ↦
        BusAt s'.mem (busR.at env.work)
          (tlBus layout weights beta point trees memory mf bf share bp) ∧
        ClaimsAt s'.mem (claimsR.at env.work)
          (tlBus layout weights beta point trees memory mf bf share bp).claims ∧
        Wrote env tlW s s')
      (fun _ ↦ False) := by
  obtain ⟨m0, m1, rfl⟩ : ∃ m0 m1, memory = #[m0, m1] := ⟨memory[0], memory[1], by
    apply Array.ext
    · simp [hms]
    · intro i h1 h2
      rw [hms] at h1
      interval_cases i <;> rfl⟩
  have hb := tl_stop
  -- the claims
  refine wp_then (claims_spec (pt := point) (lm := layout.logMemory) (lb := layout.logBytecode)
    (m0 := m0) (m1 := m1) (mf := mf) (bf := bf) h.rdi h.wp h.hin (by rw [Region.at, pc_pointR_off]; exact h.pt) hps
    v.hl0 v.hl1 h.lay.logMemoryBound.2 h.lay.logBytecodeBound
    (by rw [Region.at, memR_off]; exact h.mem) (by rw [tl_memFinalAt]; exact h.mf)
    (by rw [tl_bcFinalAt]; exact h.bf)) fun s1 ⟨cl1, w1'⟩ ↦ ?_
  have w1 : Wrote env tlW s s1 := tl_widen w1' (by rw [tl_claimsR]; decide)
  have hb1 : ∀ r ∈ [claimsR], r.stop ≤ 2 ^ 61 := by rw [tl_claimsR]; decide
  have h1 := h.keep hps hws hts hms w1
  -- the empty forms
  refine wp_then (formsInit_spec h1.rdi h1.wp h1.hin) fun s2 ⟨f2, w2'⟩ ↦ ?_
  have hb2 : ∀ r ∈ [busR], r.stop ≤ 2 ^ 61 := by rw [tl_busR]; decide
  have w2 : Wrote env tlW s s2 := w1.trans (tl_widen w2' (by rw [tl_busR]; decide))
  have h2 := h.keep hps hws hts hms w2
  have cl2 := tl_claimsAt w2' (by rw [tl_busR]; decide) hb2 cl1
  have keep2 : ∀ {k : Nat} {x : EW}, (∀ r ∈ [claimsR, busR], k + 2 ≤ r.off ∨ r.stop ≤ k) →
      k + 2 ≤ 2 ^ 61 → EWAt s.mem (wd env.work k) x → EWAt s2.mem (wd env.work k) x :=
    fun hc hk hx ↦ tl_ewat w2' (fun r hr ↦ hc r (by simp at hr ⊢; tauto)) hk hb2
      (tl_ewat w1' (fun r hr ↦ hc r (by simp at hr ⊢; tauto)) hk hb1 hx)
  have hcb : ∀ k, 52000 ≤ k → (∀ r ∈ [claimsR, busR], k + 2 ≤ r.off ∨ r.stop ≤ k) := by
    intro k hk; rw [tl_busR, tl_claimsR]; simp only [List.mem_cons,
      List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Region.stop]; omega
  have zero2 := keep2 (hcb _ (by decide)) (by decide) v.hzero
  have one2 := keep2 (hcb _ (by decide)) (by decide) v.hone
  have fp02 : EWArr s2.mem (wd env.work fpPush) _ :=
    tl_ewarr w2' (n := 6) (by rw [tl_busR]; decide) (by decide) hb2 (by simp [Model.fingerprints])
      (tl_ewarr w1' (n := 6) (by rw [tl_claimsR]; decide) (by decide) hb1
        (by simp [Model.fingerprints]) v.hfp0)
  have fp12 : EWArr s2.mem (wd env.work fpPull) _ :=
    tl_ewarr w2' (n := 6) (by rw [tl_busR]; decide) (by decide) hb2 (by simp [Model.fingerprints])
      (tl_ewarr w1' (n := 6) (by rw [tl_claimsR]; decide) (by decide) hb1
        (by simp [Model.fingerprints]) v.hfp1)
  -- the push side
  refine wp_then (tl_side (side := 0) (by decide) h2 hps hws hts (by rfl) f2
    (fun t _ ↦ tl_forms0 t 0) zero2 one2 fp02 (by simp [Model.fingerprints])) fun s3 ⟨f3, t3, w3'⟩ ↦ ?_
  have hb3 : ∀ r ∈ tlSW 0, r.stop ≤ 2 ^ 61 := by simp only [tlSW]; tl_rg
  have w3 : Wrote env tlW s s3 := w2.trans (tl_widen w3' (tlSW_within (by decide)))
  have h3 := h.keep hps hws hts hms w3
  -- the pull side
  refine wp_then (tl_side (side := 1) (by decide) h3 hps hws hts (by rfl) f3
    (fun t _ ↦ by rw [tl_acc_other (by decide), tl_forms0])
    (tl_ewat w3' (by simp only [tlSW]; tl_rg) (by decide) hb3 zero2)
    (tl_ewat w3' (by simp only [tlSW]; tl_rg) (by decide) hb3 one2)
    (tl_ewarr w3' (n := 6) (by simp only [tlSW]; tl_rg) (by decide) hb3 (by simp [Model.fingerprints])
      fp12) (by simp [Model.fingerprints])) fun s4 ⟨f4, t4, w4'⟩ ↦ ?_
  have hb4 : ∀ r ∈ tlSW 1, r.stop ≤ 2 ^ 61 := by simp only [tlSW]; tl_rg
  have w4 : Wrote env tlW s s4 := w3.trans (tl_widen w4' (tlSW_within (by decide)))
  have h4 := h.keep hps hws hts hms w4
  -- the count side
  refine wp_then (tl_side (side := 2) (ffp := #[]) (by decide) h4 hps hws hts (by rfl) f4
    (fun t _ ↦ by rw [tl_acc_other (by decide), tl_acc_other (by decide), tl_forms0])
    (tl_ewat w4' (by simp only [tlSW]; tl_rg) (by decide) hb4
      (tl_ewat w3' (by simp only [tlSW]; tl_rg) (by decide) hb3 zero2))
    (tl_ewat w4' (by simp only [tlSW]; tl_rg) (by decide) hb4
      (tl_ewat w3' (by simp only [tlSW]; tl_rg) (by decide) hb3 one2))
    (fun i hi ↦ absurd hi (by simp)) (by rfl)) fun s5 ⟨f5, t5, w5'⟩ ↦ ?_
  have hb5 : ∀ r ∈ tlSW 2, r.stop ≤ 2 ^ 61 := by simp only [tlSW]; tl_rg
  have w5 : Wrote env tlW s s5 := w4.trans (tl_widen w5' (tlSW_within (by decide)))
  have h5 := h.keep hps hws hts hms w5
  -- the point and the totals
  set A0 := tlAcc forms0 0 layout weights beta point
    (fingerprints weights #[m0, m1] (point.extract 0 layout.logMemory)
      (point.extract 0 layout.logBytecode) share (gpow 0) 1 1) (trees.getD 0 0)
  set A1 := tlAcc A0.1 1 layout weights beta point
    (fingerprints weights #[m0, m1] (point.extract 0 layout.logMemory)
      (point.extract 0 layout.logBytecode) share (gpow (2 ^ layout.logBytecode - 1)) mf bf)
    (trees.getD 1 0)
  set A2 := tlAcc A1.1 2 layout weights beta point #[] (trees.getD 2 0)
  have t05 : EWAt s5.mem (wd env.work (totW 0)) A0.2 :=
    tl_ewat w5' (by simp only [tlSW]; tl_rg) (by decide) hb5
      (tl_ewat w4' (by simp only [tlSW]; tl_rg) (by decide) hb4 t3)
  have t15 : EWAt s5.mem (wd env.work (totW 1)) A1.2 :=
    tl_ewat w5' (by simp only [tlSW]; tl_rg) (by decide) hb5 t4
  have htot : EWArr s5.mem (totalsR.at env.work) #[A0.2, A1.2, A2.2] := by
    rw [tl_totalsAt]
    intro i hi
    simp only [List.size_toArray, List.length_cons, List.length_nil] at hi
    rw [wd_wd]
    interval_cases i
    · exact t05
    · exact t15
    · exact t5
  refine WP.blk_cons (WP.mono (busTail_spec h5.rdi h5.wp h5.hin
    (by rw [Region.at, pc_depthR_off]; exact h5.depth) hps
    (by rw [Region.at, pc_pointR_off]; exact h5.pt) htot rfl) ?_ fun _ h ↦ h)
  rintro s6 ⟨pt6, tot6, w6'⟩
  have hb6 : ∀ r ∈ [busTailR], r.stop ≤ 2 ^ 61 := by rw [tl_busTailR]; decide
  have f6 := tl_formsAt w6' (by rw [tl_busTailR]; decide) hb6 f5
  refine WP.blk_nil ⟨⟨f6.1, f6.2.1, f6.2.2, pt6, rfl, tot6⟩, ?_,
    w5.trans (tl_widen w6' (by rw [tl_busTailR]; decide))⟩
  have cl : ∀ ws (sa sb : QState), Wrote env ws sa sb → (∀ r ∈ ws, ∃ q ∈ tlW, Within r q) →
      (∀ r ∈ ws, 15569 + 12161 ≤ r.off ∨ r.stop ≤ 15569) →
      ClaimsAt sa.mem (claimsR.at env.work) (tlBus layout weights beta point trees #[m0, m1]
        mf bf share bp).claims →
      ClaimsAt sb.mem (claimsR.at env.work) (tlBus layout weights beta point trees #[m0, m1]
        mf bf share bp).claims := fun ws sa sb hw hin hc h ↦
    tl_claimsAt hw hc (fun r hr ↦ by
      obtain ⟨q, hq, h1, h2⟩ := hin r hr
      exact le_trans h2 (tl_stop q hq)) h
  refine cl _ _ _ w6' (by rw [tl_busTailR]; decide) (by rw [tl_busTailR]; decide) ?_
  refine cl _ _ _ w5' (tlSW_within (by decide)) (by simp only [tlSW]; tl_rg) ?_
  refine cl _ _ _ w4' (tlSW_within (by decide)) (by simp only [tlSW]; tl_rg) ?_
  exact cl _ _ _ w3' (tlSW_within (by decide)) (by simp only [tlSW]; tl_rg) cl2

end NativeVm.Code.P3
