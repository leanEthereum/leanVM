module

public import Quantum.StdModel.Sphincs.PropsIn
public import Quantum.StdModel.Xmss.Reduction

@[expose] public section

/-!
# Theorem 1 with SM-TCR-C restricted to in-kind targets

At a tweak of the wrong kind (the leaf function at a slot other than a leaf, the node function at
a slot other than a node), the input of `xmssTcrC` is `P` followed by the message bytes, which does
not depend on the tweak. An arbitrary SM-TCR-C adversary can therefore submit `v` targets at
distinct such tweaks and win by a collision among its own targets (about `v² / 2^128`, no hash
call) or by a multi-target search (about `v q² / 2^128`): `smTcr W xmssTcrC xmssTcrD` is not hard
for arbitrary adversaries.

The restricted game is `Props.smTcrIn W xmssTcrC xmssTcrD TcrInKind`: every target in kind (the
leaf function at a leaf slot, the node function at a node slot of level `1..layerHeight`, index
below `2^32` by addressability). An in-kind target input is the honest input of its slot
(`xmssTcrC_layout_of_inKind`); it fixes the parameter and the tweak among all inputs of
`xmssTcrC` (`xmssTcrC_param_tweak_eq`), and at each function, parameter and tweak the input fixes
the message (`xmssTcrC_layout_injective`).

B4 (`tcrRed`) submits only in-kind targets (`tcrIn_of_allQ`), so its successes in the two games
are equal (`smTcrSucc_tcrRed_eq`), and Theorem 1 holds with the restricted game
(`xmss_suf_le_props_in`, `xmss_suf_le_props_in_keccak`).

EncTCR$ and CPRE need no restriction: the EncTCR$ tweak `(l, e)` always selects the slot
`.msg l e`, so the input determines the tweak; the CPRE tweaks are fixed by the challenger and its
evaluation collection is empty.
-/

open OracleComp OracleSpec HashSig HashSig.OverPermutation LeanXmss
open scoped ENNReal
open Quantum.Xmss (Slot)
open Quantum.Qrom.Xmss (Payload slotInput length_thInput_eq length_digestsPayload)

namespace Quantum.StdModel.Xmss

open Quantum.StdModel Props

/-! ## In-kind targets -/

/-- A target function at a slot of its own kind: the leaf at a leaf slot, the node at a node slot
of level `k + 1` with `k < layerHeight`. -/
def SlotInKind : TcrFn → Slot → Prop
  | .leaf, .leaf .. => True
  | .node, .node _ (k + 1) _ => k < layerHeight
  | _, _ => False

/-- **The SM-TCR-C target tweaks**: a slot of the target function's kind. -/
def TcrInKind (l : TcrFn) (t : XTw) : Prop :=
  SlotInKind l t.1

/-- **An in-kind target hashes the honest input of its slot.** -/
theorem xmssTcrC_layout_of_inKind (P : PublicParameter) {l : TcrFn} {t : XTw}
    (ht : TcrInKind l t) (m : TcrMsg l) : ∃ d, xmssTcrC.layout l P t m = slotInput P t.1 d := by
  obtain ⟨s, _⟩ := t
  change SlotInKind l s at ht
  cases l <;> cases s <;> first | exact False.elim ht | exact ⟨m, rfl⟩

/-- The honest input of an in-kind slot has `960` (leaf) or `64` (node) bytes. -/
theorem length_slotInput_inKind (P : PublicParameter) {l : TcrFn} {s : Slot}
    (hs : SlotInKind l s) (d : Payload s) :
    (slotInput P s d).length = 960 ∨ (slotInput P s d).length = 64 := by
  cases l <;> cases s <;> try exact False.elim hs
  · left
    rw [slotInput, length_thInput_eq, length_digestsPayload (n := chainCount) d]
    rfl
  · right
    rw [slotInput, length_thInput_eq]
    simp only [nodePayload, littleEndianBytes, List.length_append, List.length_ofFn]

/-- Every input of `xmssTcrC` starts with the bytes of its public parameter. -/
theorem xmssTcrC_layout_prefix (l : TcrFn) (P : PublicParameter) (t : XTw) (m : TcrMsg l) :
    ∃ rest, xmssTcrC.layout l P t m = littleEndianBytes 16 P ++ rest := by
  obtain ⟨s, -⟩ := t
  change ∃ rest, tcrLayout P l s m = _
  cases l <;> cases s <;> exact ⟨_, rfl⟩

/-- Inputs starting with the bytes of two public parameters agree on the parameter. -/
theorem xmss_param_eq_of_prefix {P P' : PublicParameter} {r r' : HashInput}
    (h : littleEndianBytes 16 P' ++ r' = littleEndianBytes 16 P ++ r) : P' = P :=
  Quantum.Xmss.littleEndianBytes_injective 16
    (List.append_inj h (by simp only [littleEndianBytes, List.length_ofFn])).1

/-- **SM-TCR-C separation at the in-kind tweaks, with the parameter**: an input of `xmssTcrC`
under any parameter equal to an in-kind target input has the same parameter and tweak. -/
theorem xmssTcrC_param_tweak_eq {l : TcrFn} {t : XTw} (ht : TcrInKind l t) (P : PublicParameter)
    (m : TcrMsg l) {l' : TcrFn} {P' : PublicParameter} {t' : XTw} {m' : TcrMsg l'}
    (h : xmssTcrC.layout l' P' t' m' = xmssTcrC.layout l P t m) : P' = P ∧ t' = t := by
  obtain ⟨r, hr⟩ := xmssTcrC_layout_prefix l P t m
  obtain ⟨r', hr'⟩ := xmssTcrC_layout_prefix l' P' t' m'
  have hP := xmss_param_eq_of_prefix (hr'.symm.trans (h.trans hr))
  refine ⟨hP, ?_⟩
  rw [hP] at h
  obtain ⟨d, hd⟩ := xmssTcrC_layout_of_inKind P ht m
  rcases tcrLayout_shape P l' t'.1 m' with ⟨d', hd'⟩ | hd'
  · exact Subtype.ext (congrArg Sigma.fst
      (xmss_slotInput_inj P t'.2 t.2 (hd'.symm.trans (h.trans hd))))
  · exfalso
    have hl := congrArg List.length (hd'.symm.trans (h.trans hd))
    rcases length_tcrJunk P l' m' with h1 | h1 <;>
      rcases length_slotInput_inKind P ht d with h2 | h2 <;> omega

/-- The bytes of a target message determine it. -/
theorem xmss_tcrBytes_injective (l : TcrFn) : Function.Injective (tcrBytes l) := by
  cases l with
  | leaf => exact fun _ _ h ↦ Quantum.Xmss.digestsPayload_injective h
  | node =>
    intro m m' h
    obtain ⟨h1, h2⟩ := Quantum.Xmss.nodePayload_injective h
    exact Prod.ext h1 h2

/-- **The SM-TCR-C target inputs determine their messages** at every function, parameter and
tweak. -/
theorem xmssTcrC_layout_injective (l : TcrFn) (P : PublicParameter) (t : XTw) :
    Function.Injective (xmssTcrC.layout l P t) := by
  intro m m' h
  obtain ⟨s, hs⟩ := t
  have junk : littleEndianBytes 16 P ++ tcrBytes l m = littleEndianBytes 16 P ++ tcrBytes l m' →
      m = m' := fun e ↦ xmss_tcrBytes_injective l (List.append_cancel_left e)
  cases l <;> cases s <;>
    first
    | exact junk h
    | exact eq_of_heq (Sigma.mk.inj (xmss_slotInput_inj P hs hs h)).2

/-! ## B4 submits in-kind targets -/

variable (W : OracleWorld)

/-- The SM-TCR-C experiment of the leanXMSS instance with the decision `J`. -/
noncomputable def tcrWithJudge
    (J : PublicParameter → QueryLog TcrPorts → TcrOut → OracleComp W.Oracles Bool) :
    Experiment W TcrPorts Unit TcrOut :=
  { smTcr W xmssTcrC xmssTcrD with judge := J }

theorem tcrWithJudge_answer
    (J : PublicParameter → QueryLog TcrPorts → TcrOut → OracleComp W.Oracles Bool) :
    (tcrWithJudge W J).answer = (smTcr W xmssTcrC xmssTcrD).answer :=
  rfl

theorem tcrWithJudge_judge
    (J : PublicParameter → QueryLog TcrPorts → TcrOut → OracleComp W.Oracles Bool) :
    (tcrWithJudge W J).judge = J :=
  rfl

/-- An honest target is in kind. -/
theorem tgtOK_inKind {o : Ops Id} {y : TcrOut × Digest} (hy : TgtOK o y) :
    TcrInKind y.1.1 y.1.2.1 := by
  rcases hy with ⟨l, e, rfl⟩ | ⟨l, k, j, h, rfl⟩
  · trivial
  · exact h.1

/-- **The targets of B4's transcript are in kind.** -/
theorem tcrIn_of_allQ (P : PublicParameter) {o : Ops Id} {T : QueryLog TcrPorts}
    (hT : AllQ o T) : TcrIn TcrInKind (T ++ [⟨.reveal, P⟩] : QueryLog TcrPorts) := by
  intro e he
  rw [tcrTargets_reveal] at he
  obtain ⟨a, ha, hae⟩ := mem_tcrTargets he
  exact tgtOK_inKind (entOK_target (hT.1 a ha) hae)

variable {W} in
/-- In a canonical run whose states keep `Inv`, which fixes the transcript to `L₀`, the
continuation may read the transcript as `L₀`. -/
theorem run₂_bind_kRunL_fix (Rt : QuantumRuntime W.spec) {Q Q' St : Type}
    {R : OracleSpec.{0, 0} Q} {R' : OracleSpec.{0, 0} Q'} (K : Kernel R (St × QueryLog R'))
    (Inv : St × QueryLog R' → Prop) (L₀ : QueryLog R') (hL : ∀ s, Inv s → s.2 = L₀)
    (hInv : ∀ s, Inv s → ∀ q, ∀ p ∈ support (K s q), Inv p.2) {A B C : QReg} {α β : Type}
    (x : QComp (advSpec W.spec R) A B α) (s : St) (hs : Inv (s, L₀))
    (k : (α × St) × QueryLog R' → QComp W.spec B C β) :
    Rt.run₂ .instruments ((kRunL W K x s L₀).bind k) =
      Rt.run₂ .instruments ((kRunL W K x s L₀).bind fun r ↦ k (r.1, L₀)) := by
  have h := run₂_map_kRunQ_sim Rt K K Inv id (fun s _ q ↦ by rw [Prod.map_id, id_map]; rfl)
    hInv x (s, L₀) hs (fun r ↦ ((r.1, r.2.1), L₀)) (fun r ↦ ((r.1, r.2.1), r.2.2))
    (fun a s hs ↦ by rw [hL s hs]; rfl)
  rw [kRunL_eq_map]
  refine (run₂_bind_congr h fun _ ↦ rfl).trans (congrArg _ ?_)
  simp only [QuantumComp₂.map_eq_bind_pure, QuantumComp₂.bind_assoc, QuantumComp₂.pure_bind]
  rfl

section Fixed

variable (tab : W.Tab) (A : SufAdversary W PublicKey SigningRequest (Option Signature) Forgery)

/-- After B4's setup, two decisions that agree on its transcript give the same probability. -/
theorem probAt_tcrRun_congr (P : PublicParameter) {c : Layer → KeyIndex → ChainIndex → Digest}
    {g : KeyIndex × LayerMsg → Randomizer} {root : Digest} {T : QueryLog TcrPorts}
    (hT : AllQ (idealOps (W.hashOf tab) P c g) T)
    (J₁ J₂ : PublicParameter → QueryLog TcrPorts → TcrOut → OracleComp W.Oracles Bool)
    (hJ : ∀ out, simulateQ (W.eager tab) (J₁ P (T ++ [⟨.reveal, P⟩]) out) =
      simulateQ (W.eager tab) (J₂ P (T ++ [⟨.reveal, P⟩]) out)) :
    W.probAt tab (QuantumComp₂.bind
      (kRunL W (hKernel tab ((smTcr W xmssTcrC xmssTcrD).answer P) (tcrSigner W))
        (A ⟨root, P⟩) (⟨c, g, P, root, T⟩, []) (T ++ [⟨.reveal, P⟩])) fun r ↦
      QuantumComp₂.bind (((simulateQ (logImpl tab ((smTcr W xmssTcrC xmssTcrD).answer P))
        (tcrPost W ⟨c, g, P, root, T⟩ r.1.1 r.1.2)).run r.2).toQuantumAt
          (QComp.coinImpl W.spec _)) fun r ↦
        (simulateQ (W.eager tab) (J₁ P r.2 r.1)).toQuantumAt (QComp.coinImpl W.spec _)) =
    W.probAt tab (QuantumComp₂.bind
      (kRunL W (hKernel tab ((smTcr W xmssTcrC xmssTcrD).answer P) (tcrSigner W))
        (A ⟨root, P⟩) (⟨c, g, P, root, T⟩, []) (T ++ [⟨.reveal, P⟩])) fun r ↦
      QuantumComp₂.bind (((simulateQ (logImpl tab ((smTcr W xmssTcrC xmssTcrD).answer P))
        (tcrPost W ⟨c, g, P, root, T⟩ r.1.1 r.1.2)).run r.2).toQuantumAt
          (QComp.coinImpl W.spec _)) fun r ↦
        (simulateQ (W.eager tab) (J₂ P r.2 r.1)).toQuantumAt (QComp.coinImpl W.spec _)) := by
  have hfix := run₂_bind_kRunL_fix (C := QReg.of Unit) (β := Bool) (W.runtime tab)
    (hKernel tab ((smTcr W xmssTcrC xmssTcrD).answer P) (tcrSigner W))
    (fun s ↦ s.1.1 = ⟨c, g, P, root, T⟩ ∧ s.2 = T ++ [⟨.reveal, P⟩]) (T ++ [⟨.reveal, P⟩])
    (fun _ hs ↦ hs.2) ?hInv (A ⟨root, P⟩) (⟨c, g, P, root, T⟩, []) ⟨rfl, rfl⟩
  case hInv =>
    rintro ⟨⟨d', sl⟩, L⟩ ⟨hd', hL⟩ q p hp
    dsimp only at hd' hL
    subst hd' hL
    rw [hKernel_tcrSigner W tab _ hT sl _ q, support_pure, Set.mem_singleton_iff] at hp
    subst hp
    exact ⟨rfl, rfl⟩
  refine probAt_eq_of_run₂ W tab ((hfix _).trans (Eq.trans ?_ (hfix _).symm))
  refine run₂_bind_congr rfl fun r ↦ ?_
  simp only [run_tcrPost, toQuantumAt_pure, QuantumComp₂.pure_bind]
  rw [hJ]

/-- **Two decisions that agree on B4's transcripts give B4 the same success.** -/
theorem succAt_tcrRed_congr (hW : W.CoinsFair)
    (J₁ J₂ : PublicParameter → QueryLog TcrPorts → TcrOut → OracleComp W.Oracles Bool)
    (hJ : ∀ (P : PublicParameter) (c : Layer → KeyIndex → ChainIndex → Digest)
      (g : KeyIndex × LayerMsg → Randomizer) (T : QueryLog TcrPorts),
      AllQ (idealOps (W.hashOf tab) P c g) T → ∀ out,
        simulateQ (W.eager tab) (J₁ P (T ++ [⟨.reveal, P⟩]) out) =
          simulateQ (W.eager tab) (J₂ P (T ++ [⟨.reveal, P⟩]) out)) :
    (tcrWithJudge W J₁).succAt tab (tcrRed W A) = (tcrWithJudge W J₂).succAt tab (tcrRed W A) := by
  have hS := fun J ↦ probAt_eq_of_run₂ W tab (run₂_game_slRed tab (tcrWithJudge W J)
    (fun _ ↦ tcrPre W) (fun _ d ↦ A ⟨d.root, d.P⟩) (fun _ d ↦ (d, [])) (fun _ ↦ tcrSigner W)
    (fun _ ↦ tcrPost W))
  refine (hS J₁).trans (Eq.trans ?_ (hS J₂).symm)
  simp only [slNormal, QuantumComp₂.bind_assoc, tcrWithJudge_answer, tcrWithJudge_judge]
  rw [probAt_bind_classicalOn W tab (classicalOn_coinImpl_toQuantumAt _ _),
    probAt_bind_classicalOn W tab (classicalOn_coinImpl_toQuantumAt _ _)]
  refine tsum_congr fun P ↦ congrArg (_ * ·) ?_
  obtain ⟨T₀, hQ, hpre⟩ := run_tcrPre W tab P hW
  rw [probAt_bind_classicalOn W tab (classicalOn_coinImpl_toQuantumAt _ _),
    probAt_bind_classicalOn W tab (classicalOn_coinImpl_toQuantumAt _ _), hpre]
  simp only [tsum_prEvent_bind_mul, tsum_prEvent_pure_mul]
  refine tsum_congr fun cg ↦ congrArg (_ * ·) ?_
  exact probAt_tcrRun_congr W tab A P (hQ cg) J₁ J₂ (hJ P cg.1 cg.2 (T₀ cg) (hQ cg))

/-- The restricted judge on a transcript with in-kind targets is the judge of `smTcr`. -/
theorem simulateQ_smTcrIn_judge (P : PublicParameter) {L : QueryLog TcrPorts}
    (hL : TcrIn TcrInKind L) (out : TcrOut) :
    simulateQ (W.eager tab) ((smTcr W xmssTcrC xmssTcrD).judge P L out) =
      simulateQ (W.eager tab) ((smTcrIn W xmssTcrC xmssTcrD TcrInKind).judge P L out) := by
  change _ = simulateQ (W.eager tab) ((smTcr W xmssTcrC xmssTcrD).judge P L out >>= fun b ↦
    pure (holds (TcrIn TcrInKind L) && b))
  rw [holds_eq_true.mpr hL]
  simp only [Bool.true_and, bind_pure]

/-- **B4 wins the restricted SM-TCR-C game exactly when it wins SM-TCR-C**: all its targets
are in kind. -/
theorem smTcrSucc_tcrRed_eq (hW : W.CoinsFair) :
    smTcrSucc W xmssTcrC xmssTcrD tab (tcrRed W A) =
      smTcrInSucc W xmssTcrC xmssTcrD TcrInKind tab (tcrRed W A) :=
  succAt_tcrRed_congr W tab A hW (smTcr W xmssTcrC xmssTcrD).judge
    (smTcrIn W xmssTcrC xmssTcrD TcrInKind).judge
    fun P _ _ _ hT out ↦ simulateQ_smTcrIn_judge W tab P (tcrIn_of_allQ P hT) out

end Fixed

/-! ## Theorem 1 with the restricted game -/

/-- **Theorem 1 at a fixed table** of a world with fair coins, with SM-TCR-C restricted to
in-kind targets. -/
theorem xmss_suf_le_props_in (W : OracleWorld) (hW : W.CoinsFair) (tab : W.Tab)
    (A : SufAdversary W PublicKey SigningRequest (Option Signature) Forgery) :
    (winProbAt W (xmssScheme W) tab A).toReal ≤
      xmssPrfAdv W tab (prfRed W A) +
        (encTcrSaltSucc W xmssEnc tab (encRed W A)).toReal +
        (cpreSucc W xmssChains noEval tab (cpreRed W A)).toReal +
        (smTcrInSucc W xmssTcrC xmssTcrD TcrInKind tab (tcrRed W A)).toReal := by
  rw [← smTcrSucc_tcrRed_eq W tab A hW]
  exact xmss_suf_le_props W hW tab A

/-- **Theorem 1 in the standard model** with SM-TCR-C restricted to in-kind targets. -/
theorem xmss_suf_le_props_in_keccak
    (A : SufAdversary keccakWorld PublicKey SigningRequest (Option Signature) Forgery) :
    (winProbAt keccakWorld (xmssScheme keccakWorld) () A).toReal ≤
      xmssPrfAdv keccakWorld () (prfRed keccakWorld A) +
        (encTcrSaltSucc keccakWorld xmssEnc () (encRed keccakWorld A)).toReal +
        (cpreSucc keccakWorld xmssChains noEval () (cpreRed keccakWorld A)).toReal +
        (smTcrInSucc keccakWorld xmssTcrC xmssTcrD TcrInKind () (tcrRed keccakWorld A)).toReal :=
  xmss_suf_le_props_in keccakWorld keccakWorld_coinsFair () A

end Quantum.StdModel.Xmss

end
