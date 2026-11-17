module

public import Quantum.StdModel.Qrom.Moded
public import Quantum.Qrom.Xmss.NoReuse

@[expose] public section

/-!
# Mixed games whose adversary only makes allowed classical calls

Moded's `modedP_mixGame` asks the reduction's handler to keep its invariant on every classical
call. Some handlers keep it only on the calls a well-behaved adversary makes (B2 re-grinds an
encoding on a reused leaf, which `refuse` never requests). The allowed calls are a property of
the adversary's program, threaded along the run by an index `g`.

* `CallsIn ok nxt g x`: along every path of `x`, each classical call `q` is allowed (`ok g q`),
  the index moving to `nxt g q`.
* `callsIn_refuseFrom`, `callsIn_ofQrom_refuse`: the requests of `refuseFrom F x` are of leaves
  outside `F` and those requested before (index `Finset LeafIndex`).
* `modedP_mixRun_allow`, `modedP_mixGame_allow`: Moded's `modedP_mixRun`, `modedP_mixGame` with
  the invariant indexed by `g` and the handler's step required only on allowed calls.
-/

open IPFunctor OracleComp OracleSpec
open scoped ENNReal

namespace Quantum.StdModel.Qrom.EncSalt

open Quantum QuantumRuntime Quantum.Qrom HashSig
open Quantum.Xmss.Assembly (ModedP modedP_bind modedP₂_bind modedP_map)

/-! ## Allowed classical calls -/

section callsIn

variable {spec : QuantumOracleSpec.{0, 0}} {Q : Type} {R : OracleSpec.{0, 0} Q}
  {X : QReg → Type} {G : Type}

/-- **Allowed classical calls**: along every path of the program, each classical call `q` is
allowed by the current index (`ok g q`), which moves to `nxt g q`; local operations and hash
calls keep it. -/
def CallsIn (ok : G → Q → Prop) (nxt : G → Q → G) :
    G → {A : QReg} →
      IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec spec R)) X A → Prop
  | _, _, .pure _ => True
  | g, _, .liftBind (.prim _) next => ∀ b, CallsIn ok nxt g (next b)
  | g, _, .liftBind (.query (.hash _) _ _) next => ∀ b, CallsIn ok nxt g (next b)
  | g, _, .liftBind (.query (.call q) _ _) next =>
      ok g q ∧ ∀ b, CallsIn ok nxt (nxt g q) (next b)

end callsIn

/-! ## The refusing adversary -/

section refuse

open LeanXmss

/-- The allowed requests of a refusing adversary: a leaf not requested before. -/
def okRefuse (F : Finset LeafIndex) (r : SigningRequest) : Prop := r.leafIndex ∉ F

/-- The requested leaves after the request `r`. -/
def nxtRefuse (F : Finset LeafIndex) (r : SigningRequest) : Finset LeafIndex :=
  insert r.leafIndex F

/-- **A refusing program only requests fresh leaves**: relabelled over `romWorld`,
`refuseFrom F x` requests no leaf of `F` and none twice. -/
theorem callsIn_refuseFrom {X : QReg → Type} {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0}
      (Quantum.Qrom.SufCma.advSpec SigningRequest (Option Signature))) X A)
    (F : Finset LeafIndex) :
    CallsIn (spec := romWorld.spec) okRefuse nxtRefuse F
      (IFreeM.mapLens qromLens (Quantum.Qrom.Xmss.refuseFrom F x)) := by
  induction x using IFreeM.inductionOn generalizing F with
  | pure _ _ => trivial
  | liftBind A c next ih =>
    rcases c with o | ⟨_ | r, E, ℓ⟩
    · exact fun b ↦ ih b F
    · exact fun b ↦ ih b F
    · by_cases h : r.leafIndex ∈ F
      · rw [Quantum.Qrom.Xmss.refuseFrom_sign_of_mem h]
        exact fun _ ↦ ih _ F
      · rw [Quantum.Qrom.Xmss.refuseFrom_sign_of_notMem h]
        exact ⟨h, fun b ↦ ih b _⟩

/-- **The refusing adversary only requests fresh leaves**, from no requested leaf. -/
theorem callsIn_ofQrom_refuse (A : Quantum.Qrom.Xmss.Adversary) (pk : PublicKey) :
    CallsIn (spec := romWorld.spec) okRefuse nxtRefuse ∅
      (ofQrom (Quantum.Qrom.Xmss.refuse A) pk) :=
  callsIn_refuseFrom (A pk) ∅

end refuse

/-! ## Mixed games with allowed calls -/

section live

variable {M : Type}

/-- **The reduction's call tree on one call keeps an invariant** if every live run of the
handler on that call ends in it. -/
theorem modedP_mixTrees_one (upd : Caller → HashDomain → M → Option HashOutput → M)
    (rl : M → HashDomain → Option HashOutput) {Q : Type} {R : OracleSpec.{0, 0} Q} {Q' : Type}
    {R' : OracleSpec.{0, 0} Q'} {St : Type}
    (ans : (q' : Q') → OracleComp romWorld.Oracles (R'.Range q')) (σ : HHandler romWorld R R' St)
    (Jo : St × QueryLog R' → Option M → Prop) (s : St × QueryLog R') (q : Q) (μ : Option M)
    (hσ : ∀ r μ', LiveRedRun rl upd ans (σ s.1 q) s.2 μ r μ' → Jo (r.1.2, r.2) μ')
    (E A : QReg) (ℓ : A ≃ (advSpec romWorld.spec R).In (.call q) × E) :
    ModedP okM (nxM upd rl) (fun p μ' ↦ Jo p.2.2.2 μ') μ (mixTrees ans σ s q E ℓ) := by
  refine modedP₂_bind (F := fun _ μ' ↦ μ' = μ)
    (F' := fun (r : R.Range q × (St × QueryLog R')) μ' ↦ Jo r.2 μ') _ _
    (Quantum.Xmss.Assembly.modedP_act (F := fun _ μ' ↦ μ' = μ) _ μ fun _ ↦ rfl) fun _ μ' hμ' ↦ ?_
  subst hμ'
  refine modedP_map (F := fun (r : R.Range q × (St × QueryLog R')) μ' ↦ Jo r.2 μ') _
    (modedP_mono (fun p μ'' h ↦ ?_) _ _
    (modedP_redImpl upd rl ans _ (σ s.1 q) s.2 μ'))
  exact hσ _ _ h

/-- **The adversary's run against call trees keeping an invariant on allowed calls**: as
`modedP_mixRun`, with the invariant indexed by `g` and the call trees keeping it only on calls
allowed by `g`, for a program making only allowed calls. -/
theorem modedP_mixRun_allow (upd : Caller → HashDomain → M → Option HashOutput → M)
    (rl : M → HashDomain → Option HashOutput) {Q : Type} {R : OracleSpec.{0, 0} Q} {St : Type}
    {X Y : QReg → Type} {G : Type} (ok : G → Q → Prop) (nxt : G → Q → G) (Tr : MixTrees R St)
    (leaf : ∀ u, X u → St → Y u) (J : G → St → Option M → Prop)
    (hTr : ∀ g s q (E A : QReg) (ℓ : A ≃ (advSpec romWorld.spec R).In (.call q) × E) μ, ok g q →
      J g s μ → ModedP okM (nxM upd rl) (fun p μ' ↦ J (nxt g q) p.2.2.2 μ') μ (Tr s q E ℓ))
    {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec romWorld.spec R)) X A)
    (g : G) (hx : CallsIn ok nxt g x) (s : St) (μ : Option M) (hs : J g s μ) :
    ModedP okM (nxM upd rl) (fun p μ' ↦ ∃ u y g' s', J g' s' μ' ∧ p = ⟨u, leaf u y s'⟩) μ
      (mixRun Tr leaf x s) := by
  induction x using IFreeM.inductionOn generalizing g s μ with
  | pure u y => exact ⟨u, y, g, s, hs, rfl⟩
  | liftBind A cmd next ih =>
    rcases cmd with o | ⟨p | q, E, ℓ⟩
    · exact ⟨trivial, fun b ↦ ih b g (hx b) s μ hs⟩
    · exact ⟨trivial, fun b ↦ ih b g (hx b) s μ hs⟩
    · refine modedP_bind (Tr s q E ℓ) _ (hTr g s q E A ℓ μ hx.1 hs) fun u l μ' hl ↦ ?_
      obtain ⟨rfl, v⟩ := l
      exact ih ⟨v.1⟩ (nxt g q) (hx.2 ⟨v.1⟩) v.2 μ' hl

/-- **The game of a straight-line reduction as a moded mixed program, with allowed calls**: as
`modedP_mixGame`, with the handler's invariant `J` also indexed by `g`, the handler's step
`hσ` required only on calls allowed by `g` (the index moving to `nxt g q`), for an adversary
making only allowed calls from `g₀`. -/
theorem modedP_mixGame_allow (upd : Caller → HashDomain → M → Option HashOutput → M)
    (rl : M → HashDomain → Option HashOutput) {Q : Type} {R : OracleSpec.{0, 0} Q} {Q' : Type}
    {R' : OracleSpec.{0, 0} Q'} {St Pub Out : Type} (E : Props.Experiment romWorld R' Pub Out)
    {S0 F : Type} (pre : Pub → OracleComp (romWorld.Oracles + R') S0)
    (adv : Pub → S0 → QComp (advSpec romWorld.spec R) (QReg.of Unit) (QReg.of Unit) F)
    (st0 : Pub → S0 → St) (σ : Pub → HHandler romWorld R R' St)
    (post : Pub → S0 → F → St → OracleComp (romWorld.Oracles + R') Out) (m₀ : M)
    {G : Type} (ok : G → Q → Prop) (nxt : G → Q → G) (g₀ : G)
    (hadv : ∀ s a, CallsIn ok nxt g₀ (adv (E.pub s) a))
    (I0 : E.State → Option M → Prop)
    (h0 : ∀ s μ, LiveRun rl (upd .setup) E.setup (some m₀) s μ → I0 s μ)
    (J : E.State → S0 → G → St × QueryLog R' → Option M → Prop)
    (hpre : ∀ s μ, I0 s μ → ∀ a μ', LiveRedRun rl upd (E.answer s) (pre (E.pub s)) [] μ a μ' →
      J s a.1 g₀ (st0 (E.pub s) a.1, a.2) μ')
    (hσ : ∀ s a g st log μ q, ok g q → J s a g (st, log) μ → ∀ r μ',
      LiveRedRun rl upd (E.answer s) (σ (E.pub s) st q) log μ r μ' →
        J s a (nxt g q) (r.1.2, r.2) μ')
    (Ipost : E.State → Out × QueryLog R' → Option M → Prop)
    (hpost : ∀ s a f g st log μ, J s a g (st, log) μ → ∀ r μ',
      LiveRedRun rl upd (E.answer s) (post (E.pub s) a f st) log μ r μ' → Ipost s r μ')
    (Win : Bool → Option M → Prop)
    (hjudge : ∀ s r μ, Ipost s r μ → ∀ b μ',
      LiveRun rl (upd .judge) (E.judge s r.2 r.1) μ b μ' → Win b μ') :
    ModedP okM (nxM upd rl) (fun p μ ↦ Win p.2.2 μ) (some m₀)
      (mixGame E pre adv st0 σ post) := by
  refine modedP₂_bind (F := I0) (F' := Win) _ _
    (modedP_mono (fun p μ h ↦ h0 _ _ h) _ _
      (modedP_toQuantumAt_mixImpl upd rl .setup _ E.setup (some m₀))) fun s μ hs ↦ ?_
  refine modedP₂_bind (F := Ipost s) (F' := Win) _ _ ?_
    fun r μ' hr ↦ modedP_mono (fun p μ'' h ↦ hjudge s r μ' hr _ μ'' h) _ _
      (modedP_toQuantumAt_mixImpl upd rl .judge _ (E.judge s r.2 r.1) μ')
  refine modedP₂_bind (F := fun a μ ↦ J s a.1 g₀ (st0 (E.pub s) a.1, a.2) μ) (F' := Ipost s) _ _
    (modedP_mono (fun p μ h ↦ hpre s _ hs _ _ h) _ _
      (modedP_redImpl upd rl (E.answer s) _ (pre (E.pub s)) [] μ)) fun a μ1 ha ↦ ?_
  refine modedP₂_bind (F := fun r μ ↦ ∃ g, J s a.1 g (r.1.2, r.2) μ) (F' := Ipost s) _ _ ?_
    fun r μ2 hr ↦ ?_
  · refine modedP_mono (fun p μ h ↦ ?_) _ _ (modedP_mixRun_allow upd rl ok nxt
      (mixTrees (E.answer s) (σ (E.pub s))) _ (J s a.1)
      (fun g st q E' A ℓ μ hq hst ↦ modedP_mixTrees_one upd rl (E.answer s) (σ (E.pub s))
        (J s a.1 (nxt g q)) st q μ (fun r μ' hr ↦ hσ s a.1 g st.1 st.2 μ q hq hst r μ' hr)
        E' A ℓ) (adv (E.pub s) a.1) g₀ (hadv s a.1) (st0 (E.pub s) a.1, a.2) μ1 ha)
    obtain ⟨u, y, g', s', hJ, rfl⟩ := h
    exact ⟨g', hJ⟩
  · obtain ⟨g, hr⟩ := hr
    exact modedP_mono (fun p μ h ↦ hpost s a.1 r.1.1 g r.1.2 r.2 μ2 hr _ _ h) _ _
      (modedP_redImpl upd rl (E.answer s) _ (post (E.pub s) a.1 r.1.1 r.1.2) r.2 μ2)

end live

end Quantum.StdModel.Qrom.EncSalt

end
