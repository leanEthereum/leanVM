module

public import Quantum.StdModel.Qrom.EncSaltLogCost
public import Quantum.StdModel.Qrom.XmssEncSalt
public import Quantum.Qrom.Xmss.NoReuse

@[expose] public section

/-!
# EncTCR$ at leanXMSS B2: the challenger's trial reads

The log-aware bound on the total weight of the challenger's trial reads
(`EncSalt.LogCost.totalWeight_saltProg_rd_le`) at B2 (`encRed`) on `refuse A`.

* `EncSentJ`: B2's sent tweaks are those of the challenger's transcript, and every cached
  encoding has its tweak sent.
* `freshRdWP_encStep`, `freshRdWP_encSign`: B2's handler queries the challenger only at fresh
  tweaks, and reads no encoding cell outside the classes of the transcript's tweaks: its own
  grinding happens only at a tweak already sent, its honest work reads no encoding cell.
* `totalWeight_encRed_le`: `TW ≤ lam (q + 2) + c₀ (2 m)`.
-/

open IPFunctor OracleComp OracleSpec HashSig HashSig.OverPermutation LeanXmss
open scoped ENNReal

namespace Quantum.StdModel.Xmss

open Quantum.StdModel Props Common
open Quantum.Qrom.Xmss (MsgBytes)
open Quantum.StdModel.Qrom (rhoMem0 cntY)
open Quantum.StdModel.Qrom.Tcr (GCell Mem)
open Quantum.StdModel.Qrom.EncSalt (Yset Kset twOf twOf_nil twOf_append hitY costR costA
  queryCost_grind AnsBound dS saltProg mem0)
open Quantum.StdModel.Qrom.EncSalt.LogCost (FreshRdWP freshRdWP_bind freshRdWP_mono
  freshRdWP_query_bind hitY_Yset_le_costR totalWeight_saltProg_rd_le)
open Quantum.Xmss.Hybrid (runtime2)
open Quantum.Sponge (HwReg)

/-! ## Generic steps -/

/-- A query lifted to the left of a sum. -/
theorem liftComp_query_bind_inl {ι ι' : Type} {spec : OracleSpec.{0, 0} ι}
    {spec' : OracleSpec.{0, 0} ι'} {α : Type} (t : ι) (k : spec.Range t → OracleComp spec α) :
    liftComp (liftM (spec.query t) >>= k) (spec + spec') =
      liftM ((spec + spec').query (.inl t)) >>= fun u ↦ liftComp (k u) (spec + spec') := by
  rw [OracleComp.liftComp_bind, OracleComp.liftComp_query]
  simp only [OracleQuery.cont_query, OracleQuery.input_query, id_map]
  rfl

/-- A weaker postcondition. -/
theorem freshRdWP_imp (P : PublicParameter) {α : Type}
    {oa : OracleComp (romWorld.Oracles + EncSpec) α} {log : QueryLog EncSpec} {n : ℕ}
    {Post Post' : α → QueryLog EncSpec → ℕ → Prop}
    (h : ∀ a log' k, Post a log' k → Post' a log' k) (hf : FreshRdWP xmssEnc P oa log n Post) :
    FreshRdWP xmssEnc P oa log n Post' := by
  have h' := freshRdWP_mono xmssEnc P oa 0 (Post := Post) (Post' := Post') h log n hf
  rwa [Nat.add_zero] at h'

/-- **Sequencing through an intermediate postcondition.** -/
theorem freshRdWP_bind_of (P : PublicParameter) {α β : Type}
    {oa : OracleComp (romWorld.Oracles + EncSpec) α}
    {f : α → OracleComp (romWorld.Oracles + EncSpec) β} {log : QueryLog EncSpec} {n : ℕ}
    {Post : β → QueryLog EncSpec → ℕ → Prop} (I : α → QueryLog EncSpec → ℕ → Prop)
    (h1 : FreshRdWP xmssEnc P oa log n I)
    (h2 : ∀ a log' k, I a log' k → FreshRdWP xmssEnc P (f a) log' k Post) :
    FreshRdWP xmssEnc P (oa >>= f) log n Post :=
  (freshRdWP_bind xmssEnc P oa f Post log n).mpr (freshRdWP_imp P h2 h1)

/-- **A world computation, lifted**: it keeps the transcript, and spends at most its cost under
any weight above the hits of the encoding cells outside the transcript's classes. -/
theorem freshRdWP_liftL {α : Type} (P : PublicParameter) (oa : OracleComp romWorld.Oracles α)
    (w : (romWorld.Oracles + EncSpec).Domain → ℕ) (log : QueryLog EncSpec)
    {Post : α → QueryLog EncSpec → ℕ → Prop}
    (hw : ∀ i, hitY (Yset xmssEnc P (twOf log)) i ≤ w (.inl i)) (hP : ∀ a k, Post a log k) :
    ∀ m n, QueryCostAtMost (liftL (s₂ := EncSpec) oa) w m → m ≤ n →
      FreshRdWP xmssEnc P (liftL (s₂ := EncSpec) oa) log n Post := by
  unfold liftL
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro _ n _ _
    rw [OracleComp.liftComp_pure]
    exact hP a n
  | query_bind t k ih =>
    intro m n hc hmn
    rw [liftComp_query_bind_inl] at hc ⊢
    rw [isWeightBound_query_bind_iff] at hc
    have h1 := hw t
    have h2 := hc.1
    refine (freshRdWP_query_bind xmssEnc P _ _ log n Post).mpr ⟨by omega, fun u ↦ ?_⟩
    exact ih u (m - w (.inl t)) _ (hc.2 u) (by omega)

/-! ## B2's handler state -/

/-- **B2's sent tweaks**: a tweak is sent iff it is in the challenger's transcript, and every
cached encoding has its tweak sent. -/
def EncSentJ (s : EncSt) (log : QueryLog EncSpec) : Prop :=
  (∀ t, (s.sent t).isSome = true ↔ t ∈ twOf log) ∧
    ∀ e msg v, s.cache (e, msg) = some v → (s.sent (msg.layer, e)).isSome = true

theorem encSentJ_st0 (s0 : Starts × Digest) : EncSentJ (encSt0 s0) [] := by
  refine ⟨fun t ↦ ?_, fun _ _ _ h ↦ ?_⟩
  · rw [twOf_nil]
    simp [encSt0]
  · simp [encSt0] at h

theorem isSome_of_not_isNone {α : Type} {x : Option α} (h : ¬x.isNone = true) :
    x.isSome = true := by
  rcases x with _ | a
  · exact absurd rfl h
  · rfl

/-- A new tweak, sent with its answer. -/
theorem encSentJ_record_new (s : EncSt) (log : QueryLog EncSpec) (e : KeyIndex) (msg : LayerMsg)
    (v : EncAns) (h : (s.sent (msg.layer, e)).isNone = true) (hJ : EncSentJ s log) :
    EncSentJ (s.record e msg v) (log ++ [⟨((msg.layer, e), msg.mb), v⟩]) := by
  refine ⟨fun t ↦ ?_, fun e' msg' v' hc ↦ ?_⟩
  · rw [EncSt.record_sent_new s e msg v h, twOf_append, Set.mem_insert_iff]
    by_cases ht : t = (msg.layer, e)
    · subst ht
      simp
    · rw [Function.update_of_ne ht, hJ.1 t]
      simp [ht]
  · rw [EncSt.record_cache] at hc
    rw [EncSt.record_sent_new s e msg v h]
    by_cases hk : (e', msg') = (e, msg)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hk
      simp
    · rw [Function.update_of_ne hk] at hc
      have h3 := hJ.2 e' msg' v' hc
      by_cases ht : (msg'.layer, e') = (msg.layer, e)
      · rw [ht]
        simp
      · rw [Function.update_of_ne ht]
        exact h3

/-- An old tweak: the encoding cached, nothing sent. -/
theorem encSentJ_record_old (s : EncSt) (log : QueryLog EncSpec) (e : KeyIndex) (msg : LayerMsg)
    (v : EncAns) (h : ¬(s.sent (msg.layer, e)).isNone = true) (hJ : EncSentJ s log) :
    EncSentJ (s.record e msg v) log := by
  refine ⟨fun t ↦ ?_, fun e' msg' v' hc ↦ ?_⟩
  · rw [EncSt.record_sent_old s e msg v h]
    exact hJ.1 t
  · rw [EncSt.record_cache] at hc
    rw [EncSt.record_sent_old s e msg v h]
    by_cases hk : (e', msg') = (e, msg)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hk
      exact isSome_of_not_isNone h
    · rw [Function.update_of_ne hk] at hc
      exact hJ.2 e' msg' v' hc

/-! ## B2's algorithms -/

attribute [local irreducible] Gen.treeNode Gen.sign hOps

/-- **B2's setup** reads no encoding cell and starts the handler in `EncSentJ`. -/
theorem freshRdWP_encPre (P : PublicParameter) :
    FreshRdWP xmssEnc P (encPre romWorld P) [] 0 fun a log _ ↦ EncSentJ (encSt0 a) log := by
  have h := cost_encPre_costR P
  unfold encPre at h ⊢
  refine freshRdWP_liftL P _ (costR xmssEnc) [] (fun i ↦ hitY_Yset_le_costR xmssEnc P _ i)
    (fun a _ ↦ ?_) 0 0 h le_rfl
  exact encSentJ_st0 a

/-- **B2's output** reads at most two encoding cells. -/
theorem freshRdWP_encPost (P : PublicParameter) (s0 : Starts × Digest) (F : Forgery)
    (s : EncSt) (log : QueryLog EncSpec) :
    FreshRdWP xmssEnc P (encPost romWorld P s0 F s) log 2 fun _ _ _ ↦ True := by
  have h := cost_encPost_costR P s0 F s
  unfold encPost at h ⊢
  exact freshRdWP_liftL P _ (costR xmssEnc) log (fun i ↦ hitY_Yset_le_costR xmssEnc P _ i)
    (fun _ _ ↦ trivial) 2 2 h le_rfl

theorem treeNodeCost_msgSlots_eq_zero (k : ℕ) :
    treeNodeCost (hKinds (⟨0, 0, 0, 1⟩ : Kinds)) k = 0 := by
  simp only [treeNodeCost, keyLeafCost, hKinds, mul_zero, add_zero]

theorem signCost_msgSlots_eq_zero : signCost (hKinds (⟨0, 0, 0, 1⟩ : Kinds)) = 0 := by
  simp only [signCost, signLayerCost, treePathCost, treeNodeCost, keyLeafCost, hKinds, mul_zero,
    add_zero]

/-- **An encoding of B2** queries the challenger only at a fresh tweak, and grinds only at a
tweak already sent, reading only cells of its class. -/
theorem freshRdWP_encStep (P : PublicParameter) (s : EncSt) (e : KeyIndex) (msg : LayerMsg)
    (log : QueryLog EncSpec) (n : ℕ) (hJ : EncSentJ s log) :
    FreshRdWP xmssEnc P (encStep romWorld P s e msg) log n fun p log' _ ↦ EncSentJ p.2 log' := by
  unfold encStep
  split
  · exact hJ
  · dsimp only
    split
    · next h =>
      refine (freshRdWP_query_bind xmssEnc P _ _ log n _).mpr ⟨fun hm ↦ ?_, fun y ↦ ?_⟩
      · have h2 := (hJ.1 _).mpr hm
        rw [Option.isNone_iff_eq_none.mp h] at h2
        exact Bool.false_ne_true h2
      · exact encSentJ_record_new s log e msg y h hJ
    · next h =>
      have hmem : (msg.layer, e) ∈ twOf log := (hJ.1 _).mp (isSome_of_not_isNone h)
      refine freshRdWP_bind_of P (fun _ log' _ ↦ log' = log) ?_ fun v log' _ hl ↦ ?_
      · refine freshRdWP_liftL P _ (sumCost (hitY (Yset xmssEnc P (twOf log)))) log
          (fun _ ↦ le_rfl) (fun _ _ ↦ rfl) _ n (cost_liftComp _
            ((cost_sample romWorld (w := hitY (Yset xmssEnc P (twOf log))) (fun _ ↦ rfl)
              Randomizer).bind fun r0 ↦ queryCost_grind xmssEnc P (msg.layer, e) msg.mb r0 _
                (fun _ hy ↦ hy.2 _ hmem) xmssEnc.limit 0)) (Nat.zero_le _)
      · subst hl
        exact encSentJ_record_old s log' e msg v h hJ

/-- **B2's handler** queries the challenger only at fresh tweaks and reads no encoding cell
outside the classes of the transcript's tweaks. -/
theorem freshRdWP_encSign (P : PublicParameter) (s : EncSt) (r : SigningRequest)
    (log : QueryLog EncSpec) (n : ℕ) (hJ : EncSentJ s log) :
    FreshRdWP xmssEnc P (encSign romWorld P s r) log n fun p log' _ ↦ EncSentJ p.2 log' := by
  have hw : ∀ (log' : QueryLog EncSpec) i, hitY (Yset xmssEnc P (twOf log')) i ≤
      sumCost (slotCost msgSlots) (.inl i : (romWorld.Oracles + EncSpec).Domain) :=
    fun log' i ↦ (hitY_Yset_le_costR xmssEnc P (twOf log') i).trans (costR_le_msgSlots (.inl i))
  unfold encSign
  refine freshRdWP_bind_of P (fun _ log' _ ↦ log = log') ?_ fun root log1 k1 h1 ↦ ?_
  · refine freshRdWP_liftL P _ _ log (hw log) (fun _ _ ↦ rfl) _ n (cost_liftComp _
      (cost_treeNode (opsBound_hOps kindBound_msgSlots P s.starts noEnc) _ _ _)) ?_
    rw [treeNodeCost_msgSlots_eq_zero]
    exact Nat.zero_le _
  subst h1
  refine freshRdWP_bind_of P (fun p log' _ ↦ EncSentJ p.2 log')
    (freshRdWP_encStep P s _ _ log k1 hJ) fun p1 log2 k2 hJ1 ↦ ?_
  refine freshRdWP_bind_of P (fun p log' _ ↦ EncSentJ p.2 log')
    (freshRdWP_encStep P p1.2 _ _ log2 k2 hJ1) fun p2 log3 k3 hJ2 ↦ ?_
  refine freshRdWP_bind_of P (fun _ log' _ ↦ log3 = log') ?_ fun sig log4 k4 h4 ↦ ?_
  · refine freshRdWP_liftL P _ _ log3 (hw log3) (fun _ _ ↦ rfl) _ k3 (cost_liftComp _
      (cost_sign (opsBound_hOps kindBound_msgSlots P s.starts _) _ _)) ?_
    rw [signCost_msgSlots_eq_zero]
    exact Nat.zero_le _
  subst h4
  exact ⟨hJ2.1, hJ2.2⟩

/-- B2's encoding makes at most one challenger query. -/
theorem costA_encStep_le (P : PublicParameter) (s : EncSt) (e : KeyIndex) (msg : LayerMsg) :
    QueryCostAtMost (encStep romWorld P s e msg)
      (costA (Layer × KeyIndex) MsgBytes Randomizer Digest) 1 := by
  unfold encStep
  split
  · exact isWeightBound_pure _ _ _
  · dsimp only
    split
    · exact cost_bind_pure (isWeightBound_query _ _)
    · exact cost_bind_pure ((cost_liftL_zero _ _ fun _ ↦ rfl).mono (Nat.zero_le _))

/-- B2's handler makes at most two challenger queries. -/
theorem costA_encSign_le (P : PublicParameter) (s : EncSt) (r : SigningRequest) :
    QueryCostAtMost (encSign romWorld P s r)
      (costA (Layer × KeyIndex) MsgBytes Randomizer Digest) 2 := by
  unfold encSign
  exact ((cost_liftL_zero _ _ fun _ ↦ rfl).bind fun _ ↦ (costA_encStep_le P s _ _).bind
    fun p1 ↦ (costA_encStep_le P p1.2 _ _).bind fun _ ↦
      cost_bind_pure (cost_liftL_zero _ _ fun _ ↦ rfl)).mono (by norm_num)

/-- B2's setup makes no challenger query. -/
theorem costA_encPre (P : PublicParameter) :
    QueryCostAtMost (encPre romWorld P)
      (costA (Layer × KeyIndex) MsgBytes Randomizer Digest) 0 := by
  unfold encPre
  exact cost_liftL_zero _ _ fun _ ↦ rfl

/-- B2's output makes no challenger query. -/
theorem costA_encPost (P : PublicParameter) (s0 : Starts × Digest) (F : Forgery) (s : EncSt) :
    QueryCostAtMost (encPost romWorld P s0 F s)
      (costA (Layer × KeyIndex) MsgBytes Randomizer Digest) 0 := by
  unfold encPost
  exact cost_liftL_zero _ _ fun _ ↦ rfl

/-! ## The total weight -/

/-- The hash calls of `refuse A`, relabelled. -/
theorem encTW_isChargeBound_hash {A : Quantum.Qrom.Xmss.Adversary} {q : ℕ}
    (hq : ∀ pk, IFreeM.IsChargeBound (A pk)
      (Quantum.Qrom.SufCma.cmdCharge Quantum.Qrom.SufCma.hashCharge) q)
    (P : PublicParameter) (s0 : Starts × Digest) :
    IFreeM.IsChargeBound (ofQrom (Quantum.Qrom.Xmss.refuse A) ⟨s0.2, P⟩) (cmdCharge hashCharge)
      q :=
  isChargeBound_ofQrom (Quantum.Qrom.Xmss.refuse A) hashCharge ⟨s0.2, P⟩ (by
    rw [hashCharge_comp_qromPort]
    exact Quantum.Qrom.Xmss.isChargeBound_refuse (hq _))

/-- The signing requests of `refuse A`, relabelled. -/
theorem encTW_isChargeBound_call {A : Quantum.Qrom.Xmss.Adversary} {m : ℕ}
    (hm : ∀ pk, IFreeM.IsChargeBound (A pk)
      (Quantum.Qrom.SufCma.cmdCharge Quantum.Qrom.SufCma.signCharge) m)
    (P : PublicParameter) (s0 : Starts × Digest) :
    IFreeM.IsChargeBound (ofQrom (Quantum.Qrom.Xmss.refuse A) ⟨s0.2, P⟩) (cmdCharge callCharge)
      m :=
  isChargeBound_ofQrom (Quantum.Qrom.Xmss.refuse A) callCharge ⟨s0.2, P⟩ (by
    rw [callCharge_comp_qromPort]
    exact Quantum.Qrom.Xmss.isChargeBound_refuse (hm _))

attribute [local irreducible] encSign encPre encPost encStep in
/-- **The total weight of the challenger's trial reads in the EncTCR$ game played by B2 on
`refuse A`**: for `A` with `q` hash calls and `m` signing requests, per-answer weights `ℓ` with
`ℓ P q ≤ lam · (recorded cells of the class of q.1 at P) + c₀`,
`TW ≤ lam (q + 2) + c₀ (2 m)`. -/
theorem totalWeight_encRed_le (A : Quantum.Qrom.Xmss.Adversary) {q m : ℕ}
    (hq : ∀ pk, IFreeM.IsChargeBound (A pk)
      (Quantum.Qrom.SufCma.cmdCharge Quantum.Qrom.SufCma.hashCharge) q)
    (hm : ∀ pk, IFreeM.IsChargeBound (A pk)
      (Quantum.Qrom.SufCma.cmdCharge Quantum.Qrom.SufCma.signCharge) m)
    (ℓ : PublicParameter → (Layer × KeyIndex) × MsgBytes →
      HwReg HashOutput Quantum.Qrom.HashDomain Mem → ℝ)
    (hA : AnsBound xmssEnc ℓ) (lamR c₀R : ℝ) (hlam : 0 ≤ lamR) (hc₀ : 0 ≤ c₀R)
    (hℓ : ∀ P q s, ℓ P q s ≤ lamR * Quantum.StdModel.Qrom.cntY (Kset xmssEnc P q.1) s + c₀R) :
    (runtime2 HashOutput Quantum.Qrom.HashDomain mem0).totalWeight .instruments (dS xmssEnc)
        (saltProg xmssEnc (encPre romWorld)
          (fun P s0 ↦ ofQrom (Quantum.Qrom.Xmss.refuse A) ⟨s0.2, P⟩) (fun _ ↦ encSt0)
          (encSign romWorld) (encPost romWorld)) (rhoMem0 mem0) ≤
      ENNReal.ofReal lamR * (q + 2 : ℕ) + ENNReal.ofReal c₀R * (2 * m : ℕ) := by
  have h := totalWeight_saltProg_rd_le xmssEnc xmssEnc_gSep ℓ hA lamR c₀R hlam hc₀ hℓ
    (encPre romWorld) (fun P s0 ↦ ofQrom (Quantum.Qrom.Xmss.refuse A) ⟨s0.2, P⟩)
    (fun _ ↦ encSt0) (encSign romWorld) (encPost romWorld) (q := q) (kA := m)
    (encTW_isChargeBound_hash hq) (encTW_isChargeBound_call hm)
    (n₁ := 0) (m₁ := 0) (nσ := 0) (mσ := 2) (n₂ := 2) (m₂ := 0)
    costA_encPre costA_encSign_le costA_encPost (fun _ ↦ EncSentJ) freshRdWP_encPre
    (fun P s r log hJ ↦ freshRdWP_encSign P s r log 0 hJ)
    (fun P s0 F s log _ ↦ freshRdWP_encPost P s0 F s log)
  have e1 : (0 + q + m * 0 + 2 : ℕ) = q + 2 := by ring
  have e2 : (0 + m * 2 + 0 : ℕ) = 2 * m := by ring
  rw [e1, e2] at h
  exact h

end Quantum.StdModel.Xmss

end
