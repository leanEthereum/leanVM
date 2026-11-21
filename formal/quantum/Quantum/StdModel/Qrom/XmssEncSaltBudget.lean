module

public import Quantum.StdModel.Qrom.XmssEncSalt
public import Quantum.StdModel.Qrom.EncSaltAllowBound

@[expose] public section

/-!
# EncTCR$ at leanXMSS B2: the live budgets

The live hypotheses of `probAvg_encTcrSalt_le_allow` for B2 (`encRed`) against the refusing
adversary (`Qrom.Xmss.refuse`), which requests each leaf at most once (`okRefuse`).

* **The invariant** (`EncJu`): the handler's chain starts are the setup's; every bottom tweak sent
  to the challenger is a requested leaf (`EncBotOk`); every top tweak sent is cached at a bottom
  root that a live run of the honest bottom tree computed from a log the current one extends
  (`EncTopOk`).
* **The handler never re-grinds** on the live runs of a fresh request (`hσ_encSignG`): the
  bottom tweak is fresh, so the challenger answers it; at the top, the recomputed bottom root is
  the cached one (`LiveDet.liveRun_det`, the honest tree flips no coin), so the encoding is cached
  or the tweak is fresh. Its other reads are not encoding cells and the challenger's answers keep
  the read cells, so the budget measure `βS` does not grow. The handler is analysed over abstract
  honest programs (`encSignG`, `encSign_eq`): elaborating a hypothesis about a live run of the
  concrete tree makes `whnf` run the tree.
* `probAvg_encTcrSalt_encRed_le_budget`: `probAvg ≤ ((q + 4) √(gradeEta 2^128) + √TW)²`.
-/

open IPFunctor OracleComp OracleSpec HashSig HashSig.OverPermutation LeanXmss
open scoped ENNReal

namespace Quantum.StdModel.Xmss

open Quantum.StdModel Props Common
open Quantum.StdModel.Qrom (LiveRun LiveRedRun stepRd liveImpl Caller RecordsAt
  liveRun_none_mode liveRun_inv_all eq_stepRd_of_mem_support stepRd_some
  run_simulateQ_query_bind)
open Quantum.StdModel.Qrom.Tcr (Mem rl)
open Quantum.StdModel.Qrom.EncSalt (βS mem0 upd recordsAt_upd okRefuse nxtRefuse)
open Quantum.StdModel.Qrom.LiveDet (LogLe coinW)

/-! ## Live runs of a reduction's algorithm, step by step -/

section liveRed

variable {M : Type} {rlM : M → Quantum.Qrom.HashDomain → Option HashOutput}
  {updM : Caller → Quantum.Qrom.HashDomain → M → Option HashOutput → M} {Q' : Type}
  {R' : OracleSpec.{0, 0} Q'} {ans : (q' : Q') → OracleComp romWorld.Oracles (R'.Range q')}

/-- A live run of a sequence: a live run of the first step, then of the continuation. -/
theorem liveRedRun_bind_inv {α β : Type} {oa : OracleComp (romWorld.Oracles + R') α}
    {ob : α → OracleComp (romWorld.Oracles + R') β} {log : QueryLog R'} {μ : Option M}
    {r : β × QueryLog R'} {μ' : Option M}
    (h : LiveRedRun rlM updM ans (oa >>= ob) log μ r μ') :
    ∃ a log₁ μ₁, LiveRedRun rlM updM ans oa log μ (a, log₁) μ₁ ∧
      LiveRedRun rlM updM ans (ob a) log₁ μ₁ r μ' := by
  unfold LiveRedRun at h
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at h
  obtain ⟨⟨a, log₁, μ₁⟩, h1, h2⟩ := h
  exact ⟨a, log₁, μ₁, h1, h2⟩

/-- A live run of a value. -/
theorem liveRedRun_pure_inv {α : Type} {x : α} {log : QueryLog R'} {μ : Option M}
    {r : α × QueryLog R'} {μ' : Option M}
    (h : LiveRedRun rlM updM ans (pure x : OracleComp (romWorld.Oracles + R') α) log μ r μ') :
    r = (x, log) ∧ μ' = μ := by
  unfold LiveRedRun at h
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
    Prod.mk.injEq] at h
  exact ⟨Prod.ext h.1 h.2.1, h.2.2⟩

/-- A live run of a challenger query: the challenger's live run, logged. -/
theorem liveRedRun_queryInr_inv {q : Q'} {log log' : QueryLog R'} {μ μ' : Option M}
    {y : R'.Range q}
    (h : LiveRedRun rlM updM ans (liftM ((romWorld.Oracles + R').query (.inr q)) :
      OracleComp (romWorld.Oracles + R') (R'.Range q)) log μ (y, log') μ') :
    log' = log ++ [⟨q, y⟩] ∧ LiveRun rlM (updM .answer) (ans q) μ y μ' := by
  unfold LiveRedRun at h
  rw [simulateQ_spec_query] at h
  change (y, (log', μ')) ∈ support ((fun p ↦ (p.1, (log ++ [⟨q, p.1⟩], p.2))) <$>
    (simulateQ (liveImpl rlM (updM .answer)) (ans q)).run μ) at h
  rw [support_map] at h
  obtain ⟨⟨y', μ₂⟩, h3, he⟩ := h
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  exact ⟨rfl, h3⟩

/-- A live run of a world computation: the reduction's live run, the transcript kept. -/
theorem liveRedRun_liftL_inv {α : Type} (oa : OracleComp romWorld.Oracles α)
    {log log' : QueryLog R'} {μ μ' : Option M} {a : α}
    (h : LiveRedRun rlM updM ans (liftL (s₂ := R') oa) log μ (a, log') μ') :
    log' = log ∧ LiveRun rlM (updM .red) oa μ a μ' := by
  induction oa using OracleComp.inductionOn generalizing μ with
  | pure x =>
    obtain ⟨h1, h2⟩ := liveRedRun_pure_inv (x := x) h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h1
    subst h2
    refine ⟨rfl, ?_⟩
    unfold LiveRun
    simp
  | query_bind t k ih =>
    have h' : LiveRedRun rlM updM ans (liftM ((romWorld.Oracles + R').query (.inl t)) >>=
        fun u ↦ liftL (s₂ := R') (k u)) log μ (a, log') μ' := by
      unfold liftL at h
      rw [OracleComp.liftComp_bind, OracleComp.liftComp_query] at h
      simp only [OracleQuery.cont_query, OracleQuery.input_query, id_map] at h
      exact h
    obtain ⟨y, log₁, μ₁, h1, h2⟩ := liveRedRun_bind_inv h'
    unfold LiveRedRun at h1
    rw [simulateQ_spec_query] at h1
    change (y, (log₁, μ₁)) ∈ support ((fun p ↦ (p.1, (log, p.2))) <$>
      (liveImpl rlM (updM .red) t).run μ) at h1
    rw [support_map] at h1
    obtain ⟨⟨y', μ₂⟩, h3, he⟩ := h1
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    obtain ⟨hl, hk⟩ := ih y' h2
    refine ⟨hl, ?_⟩
    unfold LiveRun
    rw [run_simulateQ_query_bind, mem_support_bind_iff]
    exact ⟨(y', μ₂), h3, hk⟩

end liveRed

/-! ## Logs along live runs -/

section modeLe

/-- The log of the mode `μ'` extends that of `μ`, when `μ'` is alive. -/
def ModeLe (μ μ' : Option Mem) : Prop :=
  ∀ m', μ' = some m' → ∃ m, μ = some m ∧ LogLe rl m m'

theorem ModeLe.refl (μ : Option Mem) : ModeLe μ μ := fun m' h ↦ ⟨m', h, LogLe.refl m'⟩

theorem ModeLe.trans {μ μ' μ'' : Option Mem} (h : ModeLe μ μ') (h' : ModeLe μ' μ'') :
    ModeLe μ μ'' := fun m'' hm'' ↦ by
  obtain ⟨m', hm', hle'⟩ := h' m'' hm''
  obtain ⟨m, hm, hle⟩ := h m' hm'
  exact ⟨m, hm, hle.trans hle'⟩

theorem modeLe_liveRun {u : Quantum.Qrom.HashDomain → Mem → Option HashOutput → Mem}
    (hu : ∀ z, RecordsAt rl z (u z)) {α : Type} {oa : OracleComp romWorld.Oracles α}
    {μ : Option Mem} {a : α} {μ' : Option Mem} (h : LiveRun rl u oa μ a μ') : ModeLe μ μ' := by
  intro m' hm'
  rcases μ with _ | m
  · rw [liveRun_none_mode oa h] at hm'
    cases hm'
  · subst hm'
    exact ⟨m, rfl, Quantum.StdModel.Qrom.LiveDet.liveRun_logLe hu oa h⟩

theorem modeLe_red_step {i : romWorld.Oracles.Domain} {μ μ' : Option Mem}
    {y : romWorld.Oracles.Range i}
    (h : (y, μ') ∈ support ((liveImpl rl (upd xmssEnc .red) i).run μ)) : ModeLe μ μ' := by
  rcases i with n | z
  · change (y, μ') ∈ support ((fun b ↦ (b, μ)) <$>
      liftM (romWorld.Oracles.query (.inl n))) at h
    rw [support_map] at h
    obtain ⟨_, _, he⟩ := h
    rw [← (Prod.mk.inj he).2]
    exact ModeLe.refl μ
  · rw [eq_stepRd_of_mem_support h]
    intro m' hm'
    rcases μ with _ | m
    · simp [stepRd] at hm'
    · exact ⟨m, rfl, Quantum.StdModel.Qrom.LiveDet.logLe_stepRd
        (recordsAt_upd xmssEnc .red z) hm'⟩

/-- **The log grows along a live run of B2's algorithms.** -/
theorem modeLe_liveRedRun
    {ans : (q' : (Layer × KeyIndex) × Quantum.Qrom.Xmss.MsgBytes) →
      OracleComp romWorld.Oracles EncAns} {α : Type}
    (oa : OracleComp (romWorld.Oracles + EncSpec) α) {log : QueryLog EncSpec} {μ : Option Mem}
    {r : α × QueryLog EncSpec} {μ' : Option Mem}
    (h : LiveRedRun rl (upd xmssEnc) ans oa log μ r μ') : ModeLe μ μ' :=
  Quantum.StdModel.Qrom.EncSalt.liveRedRun_inv ans (fun _ μ'' ↦ ModeLe μ μ'')
    (fun _ _ _ _ _ hI h' ↦ hI.trans (modeLe_red_step h'))
    (fun _ _ _ _ _ hI h' ↦ hI.trans (modeLe_liveRun (recordsAt_upd xmssEnc .answer) h'))
    oa log μ r μ' (ModeLe.refl μ) h

end modeLe

/-! ## Costs of B2's honest work -/

section costs

/-- A slot input's hash weighs nothing under a weight free on the hash. -/
theorem cost_hashQ_slotInput_zero (w : romWorld.Oracles.Domain → ℕ) (hw : ∀ x, w (.inr x) = 0)
    (P : PublicParameter) {s : Quantum.Xmss.Slot} (d : Quantum.Qrom.Xmss.Payload s) :
    QueryCostAtMost (Quantum.Qrom.hashQ (Quantum.Qrom.Xmss.slotInput P s d)) w 0 := by
  rw [Quantum.Qrom.Xmss.hashQ_slotInput]
  exact (isWeightBound_query w _).mono (le_of_eq (hw _))

set_option maxRecDepth 20000 in
/-- The world's hash weighs nothing under a weight free on the hash. -/
theorem kindBound_zero (w : romWorld.Oracles.Domain → ℕ) (hw : ∀ x, w (.inr x) = 0) :
    KindBound romWorld.hash w ⟨0, 0, 0, 0⟩ where
  chain P l e s i v := by
    rw [romWorld_hash_eq]
    exact cost_hashQ_slotInput_zero w hw P (s := .chain l e s i) v
  leaf P l e ends := by
    rw [romWorld_hash_eq]
    exact cost_hashQ_slotInput_zero w hw P (s := .leaf l e) ends
  node P l k j c := by
    rw [romWorld_hash_eq]
    exact cost_hashQ_slotInput_zero w hw P (s := .node l k j) c
  msg P l e M ρ := by
    rw [romWorld_hash_eq]
    exact cost_hashQ_slotInput_zero w hw P (s := .msg l e) (M.mb, ρ)

/-- The world's hash flips no coin. -/
theorem kindBound_coinW : KindBound romWorld.hash coinW ⟨0, 0, 0, 0⟩ :=
  kindBound_zero coinW fun _ ↦ rfl

theorem treeNodeCost_hKinds_zero (x : ℕ) (k : ℕ) :
    treeNodeCost (hKinds ⟨0, 0, 0, x⟩) k = 0 := by
  simp only [treeNodeCost, keyLeafCost, hKinds, mul_zero, add_zero]

theorem signCost_hKinds_zero (x : ℕ) : signCost (hKinds ⟨0, 0, 0, x⟩) = 0 := by
  simp only [signCost, signLayerCost, treePathCost, treeNodeCost, keyLeafCost, hKinds, mul_zero,
    add_zero]

/-- **The honest tree flips no coin.** -/
theorem cost_treeNode_coinW (P : PublicParameter) (c : Starts)
    (enc : KeyIndex → LayerMsg → EncAns) (l : Layer) (k j : ℕ) :
    QueryCostAtMost (Gen.treeNode (hOps romWorld P c enc) l k j) coinW 0 :=
  (cost_treeNode (opsBound_hOps kindBound_coinW P c enc) l k j).mono
    (treeNodeCost_hKinds_zero 0 k).le

/-- The honest tree reads no encoding cell. -/
theorem cost_treeNode_costR (P : PublicParameter) (c : Starts)
    (enc : KeyIndex → LayerMsg → EncAns) (l : Layer) (k j : ℕ) :
    QueryCostAtMost (liftL (s₂ := EncSpec) (Gen.treeNode (hOps romWorld P c enc) l k j))
      (Quantum.StdModel.Qrom.EncSalt.costR xmssEnc) 0 :=
  ((cost_liftComp (slotCost msgSlots)
    (cost_treeNode (opsBound_hOps kindBound_msgSlots P c enc) l k j)).mono_weight
      costR_le_msgSlots).mono (treeNodeCost_hKinds_zero 1 k).le

/-- The honest signer reads no encoding cell. -/
theorem cost_sign_costR (P : PublicParameter) (c : Starts) (enc : KeyIndex → LayerMsg → EncAns)
    (idx : LeafIndex) (msg : Message) :
    QueryCostAtMost (liftL (s₂ := EncSpec) (Gen.sign (hOps romWorld P c enc) idx msg))
      (Quantum.StdModel.Qrom.EncSalt.costR xmssEnc) 0 :=
  ((cost_liftComp (slotCost msgSlots)
    (cost_sign (opsBound_hOps kindBound_msgSlots P c enc) idx msg)).mono_weight
      costR_le_msgSlots).mono (signCost_hKinds_zero 1).le

/-! ### B2's handler over abstract honest programs

On the concrete honest tree, elaborating a hypothesis about its live runs makes `whnf` run the
tree; the handler is therefore analysed over abstract programs `tn` (the bottom tree of a top key)
and `sg` (the signer), instantiated at the end (`encSign_eq`). -/

/-- B2's handler over the bottom-tree program `tn` and the signer `sg`. -/
noncomputable def encSignG (tn : Starts → KeyIndex → OracleComp romWorld.Oracles Digest)
    (sg : Starts → (KeyIndex → LayerMsg → EncAns) → LeafIndex → Message →
      OracleComp romWorld.Oracles (Option Signature))
    (P : PublicParameter) : HHandler romWorld SigningOracleSpec EncSpec EncSt :=
  fun s r ↦ do
  let root ← liftL (tn s.starts (keyIndexOnLayer r.leafIndex topLayer))
  let p1 ← encStep romWorld P s (keyIndexOnLayer r.leafIndex bottomLayer) (.inl r.message)
  let p2 ← encStep romWorld P p1.2 (keyIndexOnLayer r.leafIndex topLayer) (.inr root)
  let sig ← liftL (sg s.starts (pairEnc p1.1 p2.1) r.leafIndex r.message)
  pure (sig, p2.2.signed r sig)

/-- The honest bottom tree of a top key. -/
noncomputable def tnB (P : PublicParameter) (c : Starts) (e : KeyIndex) :
    OracleComp romWorld.Oracles Digest :=
  Gen.treeNode (hOps romWorld P c noEnc) bottomLayer layerHeight e.val

/-- The honest signer. -/
noncomputable def sgB (P : PublicParameter) (c : Starts) (enc : KeyIndex → LayerMsg → EncAns)
    (idx : LeafIndex) (msg : Message) : OracleComp romWorld.Oracles (Option Signature) :=
  Gen.sign (hOps romWorld P c enc) idx msg

/-- **B2's handler** over its honest programs. -/
theorem encSign_eq (P : PublicParameter) :
    encSign romWorld P = encSignG (tnB P) (sgB P) P :=
  rfl

theorem tnB_coinW (P : PublicParameter) (c : Starts) (e : KeyIndex) :
    QueryCostAtMost (tnB P c e) coinW 0 := by
  unfold tnB
  generalize layerHeight = k
  exact cost_treeNode_coinW P c noEnc bottomLayer k e.val

theorem tnB_costR (P : PublicParameter) (c : Starts) (e : KeyIndex) :
    QueryCostAtMost (liftL (s₂ := EncSpec) (tnB P c e))
      (Quantum.StdModel.Qrom.EncSalt.costR xmssEnc) 0 := by
  unfold tnB
  generalize layerHeight = k
  exact cost_treeNode_costR P c noEnc bottomLayer k e.val

theorem sgB_costR (P : PublicParameter) (c : Starts) (enc : KeyIndex → LayerMsg → EncAns)
    (idx : LeafIndex) (msg : Message) :
    QueryCostAtMost (liftL (s₂ := EncSpec) (sgB P c enc idx msg))
      (Quantum.StdModel.Qrom.EncSalt.costR xmssEnc) 0 := by
  unfold sgB
  exact cost_sign_costR P c enc idx msg

end costs

attribute [local irreducible] tnB sgB

/-! ## The budget measure along B2's live steps -/

section budget

open Quantum.StdModel.Qrom.EncSalt.Live (liveRedRun_βS_le)

/-- The challenger's answers keep the read cells and the slot. -/
theorem βS_uSel (z : Quantum.Qrom.HashDomain) (m : Mem) (o : Option HashOutput) :
    βS xmssEnc (Quantum.StdModel.Qrom.EncSalt.uSel xmssEnc z m o) = βS xmssEnc m :=
  rfl

/-- **The challenger's live runs keep the budget measure.** -/
theorem βS_liveRun_answer {α : Type} {oa : OracleComp romWorld.Oracles α} {μ : Option Mem}
    {a : α} {μ' : Option Mem} (h : LiveRun rl (upd xmssEnc .answer) oa μ a μ') :
    ∀ m m', μ = some m → μ' = some m' → βS xmssEnc m' ≤ βS xmssEnc m := by
  intro m m' hm hm'
  subst hm
  refine liveRun_inv_all (Φ := fun μ ↦ ∀ m'', μ = some m'' → βS xmssEnc m'' ≤ βS xmssEnc m)
    (fun z μ v hΦ m'' hm'' ↦ ?_) oa h (fun m'' h'' ↦ by cases h''; exact le_rfl) m' hm'
  rcases μ with _ | m0
  · simp [stepRd] at hm''
  · obtain ⟨rfl, -⟩ := stepRd_some hm''
    exact (le_of_eq (βS_uSel z m0 (some v))).trans (hΦ m0 rfl)

/-- The outcome of one of B2's encoding steps: a cache hit, or a cache miss recorded. -/
def StepRes (s : EncSt) (e : KeyIndex) (msg : LayerMsg) (p : EncAns × EncSt) : Prop :=
  (p.2 = s ∧ s.cache (e, msg) = some p.1) ∨ (p.2 = s.record e msg p.1 ∧ s.cache (e, msg) = none)

set_option linter.constructorNameAsVariable false in
/-- **A live encoding step**: a cache hit, or a cache miss recorded; without re-grinding (a hit,
or a fresh tweak), the budget measure does not grow. -/
theorem encStep_live (P : PublicParameter)
    {ans : (q' : (Layer × KeyIndex) × Quantum.Qrom.Xmss.MsgBytes) →
      OracleComp romWorld.Oracles EncAns} {s : EncSt} {e : KeyIndex} {msg : LayerMsg}
    {log : QueryLog EncSpec} {μ : Option Mem} {r : (EncAns × EncSt) × QueryLog EncSpec}
    {μ' : Option Mem}
    (h : LiveRedRun rl (upd xmssEnc) ans (encStep romWorld P s e msg) log μ r μ') :
    StepRes s e msg r.1 ∧ ((s.cache (e, msg)).isSome = true ∨
      (s.sent (msg.layer, e)).isNone = true →
        ∀ m m', μ = some m → μ' = some m' → βS xmssEnc m' ≤ βS xmssEnc m) := by
  unfold encStep at h
  split at h
  next v hc =>
    obtain ⟨rfl, rfl⟩ := liveRedRun_pure_inv h
    refine ⟨Or.inl ⟨rfl, hc⟩, fun _ m m' hm hm' ↦ ?_⟩
    rw [hm, Option.some.injEq] at hm'
    rw [hm']
  next hc =>
    by_cases hs : (s.sent (msg.layer, e)).isNone = true
    · simp only [hs, ↓reduceIte] at h
      obtain ⟨v, log₁, μ₁, h1, h2⟩ := liveRedRun_bind_inv h
      obtain ⟨rfl, rfl⟩ := liveRedRun_pure_inv h2
      exact ⟨Or.inr ⟨rfl, hc⟩, fun _ ↦ βS_liveRun_answer (liveRedRun_queryInr_inv h1).2⟩
    · simp only [hs, Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨v, log₁, μ₁, h1, h2⟩ := liveRedRun_bind_inv h
      obtain ⟨rfl, rfl⟩ := liveRedRun_pure_inv h2
      refine ⟨Or.inr ⟨rfl, hc⟩, fun hk ↦ ?_⟩
      rcases hk with hk | hk
      · rw [hc] at hk
        cases hk
      · exact absurd hk hs

end budget

/-! ## The invariant -/

section inv

variable (tn : Starts → KeyIndex → OracleComp romWorld.Oracles Digest)

/-- Every bottom tweak sent to the challenger is a requested leaf. -/
def EncBotOk (g : Finset LeafIndex) (s : EncSt) : Prop :=
  ∀ e, (s.sent (bottomLayer, e)).isSome = true → e ∈ g

/-- If the mode `μ` is alive, a live run of the bottom tree `tn c e` computed `root` from a log
that of `μ` extends. -/
def TreeLive (c : Starts) (e : KeyIndex) (root : Digest) (μ : Option Mem) : Prop :=
  ∀ m, μ = some m → ∃ m₁ m₁', LiveRun rl (upd xmssEnc .red) (tn c e) (some m₁) root
    (some m₁') ∧ LogLe rl m₁' m

/-- Every top tweak sent to the challenger is cached at a bottom root computed by a live run of
the bottom tree (`TreeLive`). -/
def EncTopOk (c : Starts) (s : EncSt) (μ : Option Mem) : Prop :=
  ∀ e mb v, s.sent (topLayer, e) = some (mb, v) → ∃ root, s.cache (e, .inr root) = some v ∧
    TreeLive tn c e root μ

/-- **B2's live invariant**: the setup's chain starts, the bottom tweaks among the requested
leaves `g`, the top tweaks cached at live bottom roots. -/
def EncJu (a : Starts × Digest) (g : Finset LeafIndex) (x : EncSt × QueryLog EncSpec)
    (μ : Option Mem) : Prop :=
  x.1.starts = a.1 ∧ EncBotOk g x.1 ∧ EncTopOk tn a.1 x.1 μ

variable {tn}

theorem keyIndexOnLayer_bottom (ℓ : LeafIndex) : keyIndexOnLayer ℓ bottomLayer = ℓ :=
  Fin.ext (by
    show ℓ.val / 2 ^ (layerHeight * 0) = ℓ.val
    rw [Nat.mul_zero, pow_zero, Nat.div_one])

theorem TreeLive.mono {c : Starts} {e : KeyIndex} {root : Digest} {μ μ' : Option Mem}
    (h : TreeLive tn c e root μ) (hm : ModeLe μ μ') : TreeLive tn c e root μ' := by
  intro m' hm'
  obtain ⟨m, hm0, hle⟩ := hm m' hm'
  obtain ⟨m₁, m₁', hrun, hle'⟩ := h m hm0
  exact ⟨m₁, m₁', hrun, hle'.trans hle⟩

theorem EncTopOk.mono {c : Starts} {s : EncSt} {μ μ' : Option Mem}
    (h : EncTopOk tn c s μ) (hm : ModeLe μ μ') : EncTopOk tn c s μ' := by
  intro e mb v hs
  obtain ⟨root, hc, hl⟩ := h e mb v hs
  exact ⟨root, hc, hl.mono hm⟩

theorem cache_record_of_some {s : EncSt} {e : KeyIndex} {msg : LayerMsg} {v : EncAns}
    (hc : s.cache (e, msg) = none) {k : KeyIndex × LayerMsg} {w : EncAns}
    (hk : s.cache k = some w) : (s.record e msg v).cache k = some w := by
  rw [EncSt.record_cache, Function.update_of_ne]
  · exact hk
  · rintro rfl
    rw [hc] at hk
    cases hk

theorem encBotOk_record {g g' : Finset LeafIndex} {s : EncSt} {e : KeyIndex} {msg : LayerMsg}
    {v : EncAns} (hB : EncBotOk g s) (hg : g ⊆ g') (hnew : msg.layer = bottomLayer → e ∈ g') :
    EncBotOk g' (s.record e msg v) := by
  intro e' he'
  by_cases hn : (s.sent (msg.layer, e)).isNone = true
  · rw [EncSt.record_sent_new s e msg v hn] at he'
    by_cases hk : (bottomLayer, e') = (msg.layer, e)
    · obtain ⟨h1, rfl⟩ := Prod.mk.inj hk
      exact hnew h1.symm
    · rw [Function.update_of_ne hk] at he'
      exact hg (hB e' he')
  · rw [EncSt.record_sent_old s e msg v hn] at he'
    exact hg (hB e' he')

theorem encTopOk_record {c : Starts} {s : EncSt} {μ : Option Mem} {e : KeyIndex}
    {msg : LayerMsg} {v : EncAns} (hT : EncTopOk tn c s μ) (hc : s.cache (e, msg) = none)
    (hnew : ∀ root, msg = .inr root → TreeLive tn c e root μ) :
    EncTopOk tn c (s.record e msg v) μ := by
  intro e' mb v' hs
  have hold : s.sent (topLayer, e') = some (mb, v') → ∃ root,
      (s.record e msg v).cache (e', .inr root) = some v' ∧ TreeLive tn c e' root μ :=
    fun hs' ↦ by
      obtain ⟨root, hc', hl⟩ := hT e' mb v' hs'
      exact ⟨root, cache_record_of_some hc hc', hl⟩
  by_cases hn : (s.sent (msg.layer, e)).isNone = true
  · rw [EncSt.record_sent_new s e msg v hn] at hs
    by_cases hk : (topLayer, e') = (msg.layer, e)
    · obtain ⟨h1, rfl⟩ := Prod.mk.inj hk
      rw [hk, Function.update_self, Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨-, rfl⟩ := hs
      rcases msg with M | root
      · exact absurd h1 topLayer_ne_bottomLayer
      · refine ⟨root, ?_, hnew root rfl⟩
        rw [EncSt.record_cache, Function.update_self]
    · rw [Function.update_of_ne hk] at hs
      exact hold hs
  · rw [EncSt.record_sent_old s e msg v hn] at hs
    exact hold hs

theorem StepRes.starts {s : EncSt} {e : KeyIndex} {msg : LayerMsg} {p : EncAns × EncSt}
    (h : StepRes s e msg p) : p.2.starts = s.starts := by
  rcases h with ⟨h, -⟩ | ⟨h, -⟩
  · rw [h]
  · rw [h]
    rfl

theorem StepRes.botOk {g g' : Finset LeafIndex} {s : EncSt} {e : KeyIndex} {msg : LayerMsg}
    {p : EncAns × EncSt} (h : StepRes s e msg p) (hB : EncBotOk g s) (hg : g ⊆ g')
    (hnew : msg.layer = bottomLayer → e ∈ g') : EncBotOk g' p.2 := by
  rcases h with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]
  · exact fun e' he' ↦ hg (hB e' he')
  · exact encBotOk_record hB hg hnew

theorem StepRes.topOk {c : Starts} {s : EncSt} {μ : Option Mem} {e : KeyIndex}
    {msg : LayerMsg} {p : EncAns × EncSt} (h : StepRes s e msg p) (hT : EncTopOk tn c s μ)
    (hnew : ∀ root, msg = .inr root → TreeLive tn c e root μ) : EncTopOk tn c p.2 μ := by
  rcases h with ⟨h, -⟩ | ⟨h, hc⟩ <;> rw [h]
  · exact hT
  · exact encTopOk_record hT hc hnew

/-- A live run of a reduction's algorithm ending alive started alive. -/
theorem some_of_liveRedRun
    {ans : (q' : (Layer × KeyIndex) × Quantum.Qrom.Xmss.MsgBytes) →
      OracleComp romWorld.Oracles EncAns} {α : Type}
    {oa : OracleComp (romWorld.Oracles + EncSpec) α} {log : QueryLog EncSpec} {μ : Option Mem}
    {r : α × QueryLog EncSpec} {μ' : Option Mem} {m' : Mem}
    (h : LiveRedRun rl (upd xmssEnc) ans oa log μ r μ') (hm' : μ' = some m') :
    ∃ m, μ = some m := by
  obtain ⟨m, hm, -⟩ := modeLe_liveRedRun oa h m' hm'
  exact ⟨m, hm⟩

end inv

/-! ## The handler's live step -/

section handler

open Quantum.StdModel.Qrom.EncSalt.Live (liveRedRun_βS_le)

set_option linter.constructorNameAsVariable false in
/-- **B2's handler on a fresh request keeps the invariant and the budget measure**, over a
bottom-tree program flipping no coin and programs reading no encoding cell. -/
theorem hσ_encSignG (tn : Starts → KeyIndex → OracleComp romWorld.Oracles Digest)
    (sg : Starts → (KeyIndex → LayerMsg → EncAns) → LeafIndex → Message →
      OracleComp romWorld.Oracles (Option Signature))
    (htn : ∀ c e, QueryCostAtMost (tn c e) coinW 0)
    (htnR : ∀ c e, QueryCostAtMost (liftL (s₂ := EncSpec) (tn c e))
      (Quantum.StdModel.Qrom.EncSalt.costR xmssEnc) 0)
    (hsgR : ∀ c enc idx msg, QueryCostAtMost (liftL (s₂ := EncSpec) (sg c enc idx msg))
      (Quantum.StdModel.Qrom.EncSalt.costR xmssEnc) 0)
    (P : PublicParameter) (a : Starts × Digest) (g : Finset LeafIndex)
    (st : EncSt) (log : QueryLog EncSpec) (μ : Option Mem) (r : SigningRequest)
    (hr : okRefuse g r) (hJ : EncJu tn a g (st, log) μ)
    (out : (Option Signature × EncSt) × QueryLog EncSpec) (μ' : Option Mem)
    (h : LiveRedRun rl (upd xmssEnc) ((encTcrSalt romWorld xmssEnc).answer P)
      (encSignG tn sg P st r) log μ out μ') :
    EncJu tn a (nxtRefuse g r) (out.1.2, out.2) μ' ∧
      ∀ m m', μ = some m → μ' = some m' → βS xmssEnc m' ≤ βS xmssEnc m := by
  obtain ⟨hst, hB, hT⟩ := hJ
  simp only [encSignG] at h
  obtain ⟨root, log1, μ1, h1, h⟩ := liveRedRun_bind_inv h
  have hTN := (liveRedRun_liftL_inv _ h1).2
  obtain ⟨p1, log2, μ2, h2, h⟩ := liveRedRun_bind_inv h
  obtain ⟨p2, log3, μ3, h3, h⟩ := liveRedRun_bind_inv h
  obtain ⟨sig, log4, μ4, h4, h⟩ := liveRedRun_bind_inv h
  obtain ⟨rfl, rfl⟩ := liveRedRun_pure_inv h
  have hm1 : ModeLe μ μ1 := modeLe_liveRun (recordsAt_upd xmssEnc .red) hTN
  have hm2 : ModeLe μ1 μ2 := modeLe_liveRedRun _ h2
  have hm3 : ModeLe μ2 μ3 := modeLe_liveRedRun _ h3
  have hm4 : ModeLe μ3 μ' := modeLe_liveRedRun _ h4
  rw [hst] at hTN
  obtain ⟨hs1, hβ1⟩ := encStep_live P h2
  obtain ⟨hs2, hβ2⟩ := encStep_live P h3
  have hleaf : keyIndexOnLayer r.leafIndex bottomLayer = r.leafIndex :=
    keyIndexOnLayer_bottom r.leafIndex
  -- The bottom tweak is fresh.
  have hbot : (st.sent (LayerMsg.layer (Sum.inl r.message),
      keyIndexOnLayer r.leafIndex bottomLayer)).isNone = true := by
    rcases hs : st.sent (bottomLayer, keyIndexOnLayer r.leafIndex bottomLayer) with _ | x
    · change (st.sent (bottomLayer, _)).isNone = true
      rw [hs]
      rfl
    · refine absurd ?_ hr
      rw [← hleaf]
      exact hB _ (by rw [hs]; rfl)
  -- The state after the bottom step.
  have hB1 : EncBotOk (nxtRefuse g r) p1.2 := hs1.botOk hB (Finset.subset_insert _ _)
    fun _ ↦ by rw [hleaf]; exact Finset.mem_insert_self _ _
  have hT1 : EncTopOk tn a.1 p1.2 μ := hs1.topOk hT fun _ h' ↦ by cases h'
  -- The top step does not re-grind on live runs.
  have hnog : ∀ m, μ = some m → ∀ m1, μ1 = some m1 →
      (p1.2.cache (keyIndexOnLayer r.leafIndex topLayer, .inr root)).isSome = true ∨
        (p1.2.sent (LayerMsg.layer (Sum.inr root),
          keyIndexOnLayer r.leafIndex topLayer)).isNone = true := by
    intro m hm m1 hm1'
    rcases hc : p1.2.cache (keyIndexOnLayer r.leafIndex topLayer, .inr root) with _ | w
    · right
      rcases hs : p1.2.sent (topLayer, keyIndexOnLayer r.leafIndex topLayer) with _ | ⟨mb, v⟩
      · change (p1.2.sent (topLayer, _)).isNone = true
        rw [hs]
        rfl
      · exfalso
        obtain ⟨root', hc', hl⟩ := hT1 _ mb v hs
        obtain ⟨m₁, m₁', hrun, hle⟩ := hl m hm
        rw [hm, hm1'] at hTN
        have heq : root' = root := Quantum.StdModel.Qrom.LiveDet.liveRun_det
          (recordsAt_upd xmssEnc .red) (recordsAt_upd xmssEnc .red) _ (htn _ _) hrun hTN hle
        rw [heq, hc] at hc'
        cases hc'
    · left
      rfl
  -- The state after the top step.
  have hT2 : EncTopOk tn a.1 p2.2 μ2 := hs2.topOk ((hT1.mono hm1).mono hm2)
    fun root' hroot m2 hm2' ↦ by
      cases hroot
      obtain ⟨m1, hm1', hle12⟩ := hm2 m2 hm2'
      obtain ⟨m0, hm0, -⟩ := hm1 m1 hm1'
      rw [hm0, hm1'] at hTN
      exact ⟨m0, m1, hTN, hle12⟩
  refine ⟨⟨?_, ?_, ?_⟩, fun m m' hm hm' ↦ ?_⟩
  · change p2.2.starts = a.1
    rw [hs2.starts, hs1.starts, hst]
  · exact hs2.botOk hB1 subset_rfl fun h' ↦ absurd h' topLayer_ne_bottomLayer
  · exact (hT2.mono hm3).mono hm4
  · obtain ⟨m3, hm3'⟩ := some_of_liveRedRun h4 hm'
    obtain ⟨m2, hm2'⟩ := some_of_liveRedRun h3 hm3'
    obtain ⟨m1, hm1'⟩ := some_of_liveRedRun h2 hm2'
    have b4 := liveRedRun_βS_le xmssEnc _ _ (hsgR _ _ _ _)
      (cost_liftL_zero _ _ fun _ ↦ rfl) h4 m3 m' hm3' hm'
    have b3 := hβ2 (hnog m hm m1 hm1') m2 m3 hm2' hm3'
    have b2 := hβ1 (Or.inr hbot) m1 m2 hm1' hm2'
    have b1 := liveRedRun_βS_le xmssEnc _ _ (htnR _ _)
      (cost_liftL_zero _ _ fun _ ↦ rfl) h1 m m1 hm hm1'
    omega

end handler

/-! ## The bound -/

open Quantum.StdModel.Qrom (rhoMem0 gradeEta)
open Quantum.StdModel.Qrom.EncSalt (dS saltProg)
open Quantum.Xmss.Hybrid (runtime2)

set_option linter.constructorNameAsVariable false in
open scoped Classical in
/-- **EncTCR$ at leanXMSS B2 against the refusing adversary**: for an adversary of `q` hash
calls, `probAvg ≤ ((q + 4) √(gradeEta 2^128) + √TW)²`, `TW` the total weight of the challenger's
trial reads. -/
theorem probAvg_encTcrSalt_encRed_le_budget (A : Quantum.Qrom.Xmss.Adversary) {q : ℕ}
    (hq : ∀ pk, IFreeM.IsChargeBound (A pk)
      (Quantum.Qrom.SufCma.cmdCharge Quantum.Qrom.SufCma.hashCharge) q) :
    romWorld.probAvg ((encTcrSalt romWorld xmssEnc).game
        (encRed romWorld (ofQrom (Quantum.Qrom.Xmss.refuse A)))) ≤
      (((q : ℝ≥0∞) + 4) * ENNReal.ofReal (gradeEta HashOutput (2 ^ 128)) ^ (2⁻¹ : ℝ) +
        (runtime2 HashOutput Quantum.Qrom.HashDomain mem0).totalWeight .instruments
          (dS xmssEnc) (saltProg xmssEnc (encPre romWorld)
            (fun P s0 ↦ ofQrom (Quantum.Qrom.Xmss.refuse A) ⟨s0.2, P⟩) (fun _ ↦ encSt0)
            (encSign romWorld) (encPost romWorld)) (rhoMem0 mem0) ^ (2⁻¹ : ℝ)) ^ 2 := by
  have h := Quantum.StdModel.Qrom.EncSalt.probAvg_encTcrSalt_le_allow xmssEnc xmssEnc_gSep
    xmssEnc_layout_injective xmssEnc_lengthLe (F := 2 ^ 128)
    (fun o ↦ by convert card_truncateHash_fiber_le_enc o using 3)
    (encPre romWorld) (fun P s0 ↦ ofQrom (Quantum.Qrom.Xmss.refuse A) ⟨s0.2, P⟩)
    (fun _ ↦ encSt0) (encSign romWorld) (encPost romWorld)
    (fun P a ↦ isChargeBound_ofQrom _ hashCharge _ (by
      rw [hashCharge_comp_qromPort]
      exact Quantum.Qrom.Xmss.isChargeBound_refuse (hq _)))
    okRefuse nxtRefuse ∅
    (fun P a ↦ Quantum.StdModel.Qrom.EncSalt.callsIn_ofQrom_refuse A ⟨a.2, P⟩) 0 2
    (fun P ↦ EncJu (tnB P))
    (fun P a μ' _ ↦ ⟨⟨rfl, fun _ h' ↦ (by cases h'), fun _ _ _ h' ↦ (by cases h')⟩,
      βS_encPre_live P (by assumption)⟩)
    (fun P a g st log μ qq hq' _ hJ r μ' _ ↦ hσ_encSignG (tnB P) (sgB P) (tnB_coinW P)
      (tnB_costR P) (sgB_costR P) P a g st log μ qq hq' hJ r μ' (by
        rwa [← encSign_eq]))
    (fun P a f g st log μ _ _ r μ' _ ↦ βS_encPost_live P a f st (by assumption))
  have h4 : ((0 + 2 + 2 : ℕ) : ℝ≥0∞) = 4 := by norm_num
  rw [h4] at h
  exact h

end Quantum.StdModel.Xmss

end
