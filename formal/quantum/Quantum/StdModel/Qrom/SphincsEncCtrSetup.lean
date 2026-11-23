module

public import Quantum.StdModel.Qrom.SphincsEncCtrDefs
public import Quantum.StdModel.Qrom.XmssEncSaltBudget

@[expose] public section

/-!
# EncTCR+C at leanSPHINCS B4: the live invariant after the setup

`encJu_pre`: every live run of B4's setup (`encRedPre`) against the challenger of `encTcrCtrIn`
ends in B4's live invariant (`EncJu`), the hypothesis `hpreU` of `encTcrCtrIn_probAvg_le`.

* The coins keep the transcript (`suLiftW_log`).
* The build (`suFold`, by `suAsk`): the secrets' digests are the sampled ones, the transcript
  gains evaluations only, and a live memory logs every other position's cell, read by the
  challenger, with a value truncating to its digest; a later position never changes the payload
  of an earlier one (`keyPayload_congr`, the order by rank).
* The targets (`suTargets`) are the keys in use on their messages; the challenger's answers only
  extend the log and the cells read (`suExt_liveAns`).
* The reveal answers `P`; no read of the setup is charged (`encRedPre_gc`, `suCnt`).
-/

open OracleComp OracleSpec
open HashSig hiding PublicKey
open Sphincs hiding HashDomain

namespace Quantum.StdModel.Qrom.SphEnc

open Quantum.StdModel Props Quantum.StdModel.Sphincs
open Quantum.Sphincs (Key)
open Quantum.Qrom.Sphincs (RawPos Pos slotInput)
open Quantum.StdModel.Qrom.EncTcr (Mem Gc uAns_log log_persist cntAfter Charged)
open Quantum.StdModel.Xmss (liveRedRun_bind_inv liveRedRun_pure_inv liveRedRun_queryInr_inv)

attribute [local irreducible] LiveRedRun LiveRun encTargets encCore encRedPre encRedSign
  encRedPost

/-! ## Extensions of the memory -/

/-- The memory `m'` extends `m`: every logged value kept, every cell the challenger read still
read. -/
def SuExt (m m' : Mem nB) : Prop :=
  (∀ x v, m.log x = some v → m'.log x = some v) ∧ ∀ x, m.ax x = true → m'.ax x = true

theorem suExt_refl (m : Mem nB) : SuExt m m :=
  ⟨fun _ _ h ↦ h, fun _ h ↦ h⟩

theorem SuExt.trans {m m' m'' : Mem nB} (h : SuExt m m') (h' : SuExt m' m'') : SuExt m m'' :=
  ⟨fun x v hv ↦ h'.1 x v (h.1 x v hv), fun x hx ↦ h'.2 x (h.2 x hx)⟩

/-- The cell of the input `l` was read by the challenger and logged with a value truncating to
`d`. -/
def SuLogged (l : HashInput) (d : Digest) (m : Mem nB) : Prop :=
  ∃ x o, Quantum.Qrom.encodeInput l = some x ∧ m.ax x = true ∧ m.log x = some o ∧
    truncateHash o = d

theorem SuLogged.ext {l : HashInput} {d : Digest} {m m' : Mem nB} (h : SuLogged l d m)
    (he : SuExt m m') : SuLogged l d m' := by
  obtain ⟨x, o, hx, ha, hl, ho⟩ := h
  exact ⟨x, o, hx, he.2 x ha, he.1 x o hl, ho⟩

/-- **A live read of the challenger** extends the memory, and logs the read cell as read. -/
theorem suExt_stepAns {z : Quantum.Qrom.HashDomain} {m m' : Mem nB} {v : HashOutput}
    (h : stepRd (EncTcr.rl nB) (EncTcr.upd encCtr EncTwIn nB .answer z) z (some m) v =
      some m') :
    SuExt m m' ∧ m'.ax z = true ∧ m'.log z = some v := by
  have hp := log_persist (fun m o ↦ uAns_log (e := encCtr) (G := EncTwIn) z m o) h
  obtain ⟨rfl, -⟩ := stepRd_some h
  refine ⟨⟨hp, fun x hx ↦ ?_⟩, ?_, ?_⟩
  · change Function.update m.ax z true x = true
    by_cases hxz : x = z
    · subst hxz
      exact Function.update_self ..
    · rw [Function.update_of_ne hxz]
      exact hx
  · change Function.update m.ax z true z = true
    exact Function.update_self ..
  · change Function.update m.log z (some v) z = some v
    exact Function.update_self ..

/-- **A live run of the challenger's answers** extends the memory, from a live one. -/
theorem suExt_liveAns {α : Type} {oa : OracleComp romWorld.Oracles α} {μ μ' : Option (Mem nB)}
    {a : α} (h : LiveRun (EncTcr.rl nB) (EncTcr.upd encCtr EncTwIn nB .answer) oa μ a μ') :
    ∀ m', μ' = some m' → ∃ m, μ = some m ∧ SuExt m m' :=
  liveRun_inv_all (fun ν ↦ ∀ m', ν = some m' → ∃ m, μ = some m ∧ SuExt m m')
    (fun _ ν _ hΦ m' hm' ↦ by
      rcases ν with _ | m₁
      · cases hm'
      obtain ⟨m, hm, hE⟩ := hΦ m₁ rfl
      exact ⟨m, hm, hE.trans (suExt_stepAns hm').1⟩) oa h
    (fun m' hm' ↦ ⟨m', hm', suExt_refl m'⟩)

/-! ## The coins and the charged reads -/

/-- **The coins keep the transcript.** -/
theorem suLiftW_log {α : Type} {_ : SampleableType α} (P : PublicParameter)
    {log log' : QueryLog EncCtrPorts} {μ μ' : Option (Mem nB)} {x : α}
    (h : LiveRedRun (EncTcr.rl nB) (EncTcr.upd encCtr EncTwIn nB)
      ((encTcrCtrIn romWorld encCtr slotColl EncTwIn).answer P)
      (liftW EncCtrPorts (Props.sample romWorld α)) log μ (x, log') μ') : log' = log := by
  have hna : Common.QueryCostAtMost (liftW EncCtrPorts (Props.sample romWorld α))
      (ansCost (R' := EncCtrPorts)) 0 := by
    rw [SphInst.ansCost_eq_portCost]
    exact queryCostAtMost_liftW_enc romWorld _ 0
  exact (liveRedRun_count _ _ _ _ (fun _ ↦ 0) (fun _ _ _ ↦ Nat.zero_le _) _ hna hna h).2

/-- **The setup makes no charged read.** -/
theorem suCnt (P : PublicParameter) {a : EncData × QueryLog EncCtrPorts} {μ : Option (Mem nB)}
    (h : LiveRedRun (EncTcr.rl nB) (EncTcr.upd encCtr EncTwIn nB)
      ((encTcrCtrIn romWorld encCtr slotColl EncTwIn).answer P) (encRedPre romWorld) []
      (some EncTcr.mem₀) a μ) :
    ∀ m, μ = some m → m.cnt.val = 0 := by
  refine liveRedRun_inv_cost (EncTcr.upd encCtr EncTwIn nB) (EncTcr.rl nB) _
    (gCostR (Gc encCtr EncTwIn)) (fun _ μ ↦ ∀ m, μ = some m → m.cnt.val = 0)
    (fun z _ μ v hz hΦ m' hm' ↦ ?_) (fun _ _ μ _ _ _ hΦ hrun' ↦ ?_) (encRedPre romWorld)
    encRedPre_gc h (by rintro m ⟨⟩; rfl)
  · rcases μ with _ | m
    · cases hm'
    have hz' : EncTcr.encTw encCtr EncTwIn z = none := by
      by_contra hne
      simp [gCostR, gCost, Gc, hne] at hz
    obtain ⟨rfl, -⟩ := stepRd_some hm'
    have hch : ¬ Charged encCtr EncTwIn nB m z := fun hc ↦ hc.1 hz'
    change (cntAfter encCtr EncTwIn nB m z).val = 0
    simp only [cntAfter, hch, ↓reduceIte]
    exact hΦ m rfl
  · exact liveRun_inv_all (fun μ ↦ ∀ m, μ = some m → m.cnt.val = 0) (fun _ μ _ hΦ' m' hm' ↦ by
      rcases μ with _ | m
      · cases hm'
      obtain ⟨rfl, -⟩ := stepRd_some hm'
      exact hΦ' m rfl) _ hrun' hΦ

/-! ## The build -/

theorem suSecDom {p : RawPos} (hk : KeyPart p) (hs : IsSecret p) : ∃ d, encSecDom p = some d := by
  cases p <;> first | exact ⟨_, rfl⟩ | exact (hk : False).elim | exact (hs : False).elim

/-- **A live run of one position's digest**: the secret, or an evaluation at its slot, its cell
logged as read by the challenger with a value truncating to the digest. -/
theorem suAsk (P : PublicParameter) (s : KeygenDomain → Digest) (p : Pos) (hk : KeyPart p.1)
    (t : RawPos → Digest) {log log₁ : QueryLog EncCtrPorts} {μ μ₁ : Option (Mem nB)}
    {d : Digest}
    (h : LiveRedRun (EncTcr.rl nB) (EncTcr.upd encCtr EncTwIn nB)
      ((encTcrCtrIn romWorld encCtr slotColl EncTwIn).answer P) (encAsk romWorld s p.1 t) log μ
      (d, log₁) μ₁) :
    (∃ T, (∀ e ∈ T, EncEvalOk e) ∧ log₁ = log ++ T) ∧
      (IsSecret p.1 → ∃ dd, encSecDom p.1 = some dd ∧ d = s dd) ∧
      ∀ m₁, μ₁ = some m₁ → ∃ m, μ = some m ∧ SuExt m m₁ ∧
        (¬IsSecret p.1 → SuLogged (keyInput P t p.1) d m₁) := by
  by_cases hs : IsSecret p.1
  · obtain ⟨dd, hdd⟩ := suSecDom hk hs
    have he : encAsk romWorld s p.1 t = pure (s dd) := by
      unfold encAsk
      simp only [hdd]
    rw [he] at h
    obtain ⟨h1, rfl⟩ := liveRedRun_pure_inv h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h1
    exact ⟨⟨[], fun e he ↦ by simp at he, (List.append_nil _).symm⟩, fun _ ↦ ⟨dd, hdd, rfl⟩,
      fun m₁ hm₁ ↦ ⟨m₁, hm₁, suExt_refl m₁, fun h ↦ absurd hs h⟩⟩
  · have he : encAsk romWorld s p.1 t =
        portQ romWorld EncCtrPorts (.eval (keySlot p.1) (keySlot p.1) (keyPayload p.1 t)) := by
      unfold encAsk
      simp only [encSecDom_none hs]
      rfl
    rw [he] at h
    obtain ⟨rfl, hrun⟩ := liveRedRun_queryInr_inv h
    refine ⟨⟨_, ?_, rfl⟩, fun h ↦ absurd h hs, fun m₁ hm₁ ↦ ?_⟩
    · intro e he
      rw [List.mem_singleton.mp he]
      refine ⟨rfl, rfl, fun t' ht' ↦ ?_⟩
      obtain rfl : keySlot p.1 = t' := Option.some.inj ht'
      exact not_isEncSlot_keySlot p.1
    · change LiveRun _ _
        (slotColl.eval romWorld (keySlot p.1) P (keySlot p.1) (keyPayload p.1 t)) _ _ _ at hrun
      rw [EncTcr.eval_eq, slotColl_layout P (slotInRange_keySlot p (encKeyPart_ne_hmsg hk)),
        Quantum.Qrom.hashQ_of_encodeInput_eq_some
          (Quantum.Qrom.Sphincs.encodeInput_slotInput _ _ _ _)] at hrun
      obtain ⟨v, μ₂, hv, hrun'⟩ := liveRun_query_bind hrun
      have hμ₂ := eq_stepRd_of_mem_support hv
      obtain ⟨rfl, rfl⟩ := liveRun_pure_inv hrun'
      subst hμ₂
      rcases μ with _ | m
      · cases hm₁
      obtain ⟨hE, hax, hlog⟩ := suExt_stepAns hm₁
      exact ⟨m, rfl, hE, fun _ ↦
        ⟨_, v, Quantum.Qrom.Sphincs.encodeInput_slotInput _ _ _ _, hax, hlog, rfl⟩⟩

/-- **A live run of the build over the positions `L`** (by nondecreasing rank, distinct): the
transcript gains evaluations; the positions off `L` keep their digests; the secrets of `L` get the
sampled ones; a live memory extends the start one and logs every other position's cell. -/
theorem suFold (P : PublicParameter) (s : KeygenDomain → Digest) :
    ∀ (L : List Pos), L.Pairwise (fun a b : Pos ↦ a.1.rank ≤ b.1.rank) → L.Nodup →
      (∀ p ∈ L, KeyPart p.1) → ∀ (t : RawPos → Digest) (log : QueryLog EncCtrPorts)
      (μ : Option (Mem nB)) (tf : RawPos → Digest) (log' : QueryLog EncCtrPorts)
      (μ' : Option (Mem nB)),
      LiveRedRun (EncTcr.rl nB) (EncTcr.upd encCtr EncTwIn nB)
        ((encTcrCtrIn romWorld encCtr slotColl EncTwIn).answer P)
        (L.foldlM (buildStep (encAsk romWorld s)) t) log μ (tf, log') μ' →
      (∃ T, (∀ e ∈ T, EncEvalOk e) ∧ log' = log ++ T) ∧ (∀ q : Pos, q ∉ L → tf q.1 = t q.1) ∧
        (∀ q ∈ L, IsSecret q.1 → ∃ d, encSecDom q.1 = some d ∧ tf q.1 = s d) ∧
        ∀ m', μ' = some m' → ∃ m, μ = some m ∧ SuExt m m' ∧
          ∀ q ∈ L, ¬IsSecret q.1 → SuLogged (keyInput P tf q.1) (tf q.1) m'
  | [], _, _, _, t, log, μ, tf, log', μ', h => by
    rw [List.foldlM_nil] at h
    obtain ⟨h1, rfl⟩ := liveRedRun_pure_inv h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h1
    exact ⟨⟨[], fun e he ↦ by simp at he, (List.append_nil _).symm⟩, fun _ _ ↦ rfl,
      fun q hq ↦ by simp at hq, fun m' hm' ↦ ⟨m', hm', suExt_refl m', fun q hq ↦ by simp at hq⟩⟩
  | p :: L, hP, hN, hK, t, log, μ, tf, log', μ', h => by
    rw [List.pairwise_cons] at hP
    rw [List.nodup_cons] at hN
    have hkp := hK p List.mem_cons_self
    rw [List.foldlM_cons] at h
    obtain ⟨t₁, log₁, μ₁, h1, h2⟩ := liveRedRun_bind_inv h
    unfold buildStep at h1
    obtain ⟨d, log₀, μ₀, h3, h4⟩ := liveRedRun_bind_inv h1
    obtain ⟨h5, rfl⟩ := liveRedRun_pure_inv h4
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h5
    obtain ⟨⟨T₁, hT₁, rfl⟩, hsec₁, hmem₁⟩ := suAsk P s p hkp t h3
    obtain ⟨⟨T₂, hT₂, rfl⟩, hout, hsec, hmem⟩ :=
      suFold P s L hP.2 hN.2 (fun q hq ↦ hK q (List.mem_cons_of_mem _ hq)) _ _ _ _ _ _ h2
    have hfp : tf p.1 = d := by
      rw [hout p hN.1, Function.update_self]
    have hlow : ∀ q : Pos, KeyPart q.1 → q.1.rank < p.1.rank → t q.1 = tf q.1 := by
      intro q _ hr
      have hq : q ∉ L := fun hq ↦ absurd (hP.1 q hq) (Nat.not_le.2 hr)
      have hqp : q.1 ≠ p.1 := fun e ↦ by
        rw [e] at hr
        exact lt_irrefl _ hr
      rw [hout q hq, Function.update_of_ne hqp]
    refine ⟨⟨T₁ ++ T₂, fun e he ↦ (List.mem_append.mp he).elim (hT₁ e) (hT₂ e),
      List.append_assoc _ _ _⟩, fun q hq ↦ ?_, fun q hq hs ↦ ?_, fun m' hm' ↦ ?_⟩
    · have hqp : q.1 ≠ p.1 := fun e ↦ hq (List.mem_cons.mpr (Or.inl (Subtype.ext e)))
      rw [hout q fun h ↦ hq (List.mem_cons_of_mem _ h), Function.update_of_ne hqp]
    · rcases List.mem_cons.mp hq with hqp | hq
      · subst q
        obtain ⟨dd, hdd, hd⟩ := hsec₁ hs
        exact ⟨dd, hdd, hfp.trans hd⟩
      · exact hsec q hq hs
    · obtain ⟨m₁, hm₁, hE, hlog⟩ := hmem m' hm'
      obtain ⟨m, hm, hE₀, hlog₀⟩ := hmem₁ m₁ hm₁
      refine ⟨m, hm, hE₀.trans hE, fun q hq hs ↦ ?_⟩
      rcases List.mem_cons.mp hq with hqp | hq
      · subst q
        have hin : keyInput P tf p.1 = keyInput P t p.1 := by
          unfold keyInput
          rw [keyPayload_congr p.1 fun r hk hr ↦ (hlow r hk hr).symm]
        rw [hin, hfp]
        exact (hlog₀ hs).ext hE
      · exact hlog q hq hs

/-! ## The targets -/

set_option linter.constructorNameAsVariable false in
/-- **A live run of the targets of the keys `Ks`**: the keys on their messages, logged; a live
memory extends the start one. -/
theorem suTargets (P : PublicParameter) (msg : Key → Digest) (Ks : List Key) :
    ∀ (log : QueryLog EncCtrPorts) (μ : Option (Mem nB)) (tg : List EncTgt)
      (log' : QueryLog EncCtrPorts) (μ' : Option (Mem nB)),
      LiveRedRun (EncTcr.rl nB) (EncTcr.upd encCtr EncTwIn nB)
        ((encTcrCtrIn romWorld encCtr slotColl EncTwIn).answer P) (encTargets romWorld msg Ks)
        log μ (tg, log') μ' →
      tg.map (fun x ↦ (x.1, x.2.1)) = Ks.map (fun K ↦ (K, msg K)) ∧
        log' = log ++ tg.map encEntry ∧ ∀ m', μ' = some m' → ∃ m, μ = some m ∧ SuExt m m' := by
  induction Ks with
  | nil =>
    intro log μ tg log' μ' h
    rw [encTargets] at h
    obtain ⟨h1, rfl⟩ := liveRedRun_pure_inv h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h1
    exact ⟨rfl, (List.append_nil _).symm, fun m' hm' ↦ ⟨m', hm', suExt_refl m'⟩⟩
  | cons K Ks ih =>
    intro log μ tg log' μ' h
    rw [encTargets] at h
    obtain ⟨a, log₁, μ₁, h1, h2⟩ := liveRedRun_bind_inv h
    obtain ⟨rest, log₂, μ₂, h3, h4⟩ := liveRedRun_bind_inv h2
    obtain ⟨h5, rfl⟩ := liveRedRun_pure_inv h4
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h5
    obtain ⟨rfl, hrun⟩ := liveRedRun_queryInr_inv h1
    obtain ⟨hmap, rfl, hmem⟩ := ih _ _ _ _ _ h3
    refine ⟨?_, List.append_assoc _ _ _, fun m' hm' ↦ ?_⟩
    · simp only [List.map_cons, hmap]
    · obtain ⟨m₁, hm₁, hE⟩ := hmem m' hm'
      obtain ⟨m, hm, hE₀⟩ := suExt_liveAns hrun m₁ hm₁
      exact ⟨m, hm, hE₀.trans hE⟩

/-! ## The setup -/

set_option linter.constructorNameAsVariable false in
/-- **B4's live invariant holds after every live run of its setup** (`hpreU` of
`encTcrCtrIn_probAvg_le`). -/
theorem encJu_pre (P : PublicParameter) (a : EncData × QueryLog EncCtrPorts)
    (μ : Option (Mem nB))
    (h : LiveRedRun (EncTcr.rl nB) (EncTcr.upd encCtr EncTwIn nB)
      ((encTcrCtrIn romWorld encCtr slotColl EncTwIn).answer P) (encRedPre romWorld) []
      (some EncTcr.mem₀) a μ) :
    EncJu P a.1 ((a.1, []), a.2) μ := by
  have hcnt := suCnt P h
  unfold encRedPre at h
  obtain ⟨s, log₁, μ₁, h1, h2⟩ := liveRedRun_bind_inv h
  obtain ⟨r, log₂, μ₂, h3, h4⟩ := liveRedRun_bind_inv h2
  obtain rfl := suLiftW_log P h1
  obtain rfl := suLiftW_log P h3
  unfold encCore at h4
  obtain ⟨tf, log₃, μ₃, h5, h6⟩ := liveRedRun_bind_inv h4
  obtain ⟨tg, log₄, μ₄, h7, h8⟩ := liveRedRun_bind_inv h6
  obtain ⟨P', log₅, μ₅, h9, h10⟩ := liveRedRun_bind_inv h8
  obtain ⟨ha, hμ⟩ := liveRedRun_pure_inv h10
  subst a
  subst hμ
  obtain ⟨rfl, hrev⟩ := liveRedRun_queryInr_inv h9
  change LiveRun _ _ (pure P) _ _ _ at hrev
  obtain ⟨hP, hμ'⟩ := liveRun_pure_inv hrev
  subst P'
  subst hμ'
  unfold buildDig at h5
  obtain ⟨⟨Tb, hTb, hlog₃⟩, -, hsec, hmem⟩ := suFold P s keyOrder pairwise_keyOrder
    tcr_nodup_keyOrder (fun p hp ↦ (mem_keyOrder p).1 hp) _ _ _ _ _ _ h5
  subst log₃
  obtain ⟨htg, rfl, hmemT⟩ := suTargets P _ encKeys _ _ _ _ _ h7
  unfold EncJu SecOk TgOk LogOk KeyLogged
  refine ⟨rfl, rfl, fun p hk hs ↦ hsec p ((mem_keyOrder p).2 hk) hs, htg,
    ⟨Tb, hTb, congrArg (fun L ↦ L ++ tg.map encEntry ++ [encRev P]) (List.nil_append Tb)⟩,
    fun m hm ↦ ⟨?_, hcnt m hm⟩⟩
  obtain ⟨m₃, hm₃, hE⟩ := hmemT m hm
  obtain ⟨-, -, -, hlog⟩ := hmem m₃ hm₃
  exact fun p hk hs ↦ (hlog p ((mem_keyOrder p).2 hk) hs).ext hE

end Quantum.StdModel.Qrom.SphEnc

end
