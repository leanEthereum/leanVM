module

public import Quantum.Xmss.Assembly.HTrial
public import Quantum.Sphincs.Assembly.PrefixRun
public import Quantum.Sphincs.Assembly.TrialsOff
public import Quantum.Sphincs.Assembly.GameTCalls
public import Quantum.Sphincs.Assembly.GameR
public import Quantum.Sphincs.Assembly.ReparamFull
public import Quantum.Sphincs.Assembly.MassSources

@[expose] public section

/-!
# The counter trials' hidden reads

leanSPHINCS's counterpart of leanXMSS's `Quantum.Xmss.Assembly.TrialSource`: the hidden mass of the
read ports of the template game (`readMass`), averaged over the padded tables through a
reparametrization masked by its good set, is the challenge prefix's term `htrial` (the WOTS+C
counter trials' reads) plus the verification's reads, the never-revealed coordinates' cells and
the mismatch of the charged coordinates.

* **The trial modes** (`trRdOk`, `trOkR`, `trOkT`, `trOkZ` for a trial predicate `T`; leanXMSS's
  `TMode`, `rdNx`, `nxR`, `ModedE`): every read of the challenge prefix (`prefixT`) is a counter
  trial's `k`-read at a trial block (TrialsOff's `TrialBlock`: one block
  `PK.seed ‖ ADRS_enc(K) ‖ m ‖ BE32(c)`, for every value `m`, so the hidden value `v (msgPos K)` the
  key signs needs no separate treatment) keeping the memory, then the `k'`-read at `π (x, a)` and
  the `h`-read at `π (x, a).2 + c` (`trFree_prefixT`).
* **Moving the trials' hidden mass onto their `k`-reads** (`trial_step_sph`,
  `totalWeight_prefixT_le_trialW_sph`): when no trial block is a hidden `k`-cell, the prefix's
  hidden read mass is at most leanXMSS's trial charge `trialW`.
* **The verification's reads** (`totalWeight_portMass_gameT_split_sph`, `sum_verifyMass_le_sph`):
  the masses of the game split at the verification; the verification's reads of hidden cells with
  sources (Masses' `Sources` on GameTCalls' `SlotInv`, weight `κ` per read) weigh
  `κ · 3 · verifyBlocks` per hidden value.
* **The masked read mass** (`uavg_mask_readMass_le_split_good_sph`): through an injective
  reparametrization `e` on a good set `G` of an arbitrary table type, with the game at a table equal
  to the game at the public data realized at hidden values agreeing off a charged set `B t`
  (depending on the table), the masked read mass is at most
  `τ + κ · 3 · verifyBlocks + N εK + N μ`: `τ` the trials' term on the good hidden values `TG`
  (HTrial's `sum_trialMass_le_sph`), `εK` the per-cell fraction of the never-revealed coordinates
  `K` over which extra hidden cells range, `μ` the named masked average of the record mass of the
  charged sets (Mismatch's `revW`), no bad fraction (the masked average pays it once, outside).
* **At the composed reparametrization** (`uavg_mask_readMass_le_sph_good`): the same at
  ReparamFull's `fullE` on `FullG S`, `B = chgB`, `N = clsCap`.
-/

open IPFunctor Matrix MeasureTheory
open scoped ENNReal ComplexOrder Kronecker

universe u v w

open Quantum.SufCma

open Quantum QuantumRuntime Quantum.Sponge Sphincs
open HashSig (Digest HashOutput Message)
open Quantum.Xmss (X Z blocks out256 keccakStateEquiv)
open Quantum.Xmss.Hybrid (LazyProg restrictTo Lazy lazy_const suppAt_empty Agree uavg uavg_mono
  uavg_add uavg_const_mul portMass readMass revW totalWeight_portMass_le_mismatch
  portMass_eq_diagMass totalWeight_diagMass_bind₂ hidSet diagMass setProj)
open Quantum.Xmss.Assembly (tmplSpec recHwSpec recSpec readLift readLens readLiftQ realizeT
  realizeT_bind₂ runtimeR RevealVals revealThen progThen liftRead tmplLens TMode rdNx nxR ModedE
  modedE_bind modedE₂_bind modedE_map modedE_cast totalWeight_le_moded_of_zero
  rdHU rdRoundU hashTrial kpot trialW sum_potential_kpot_free potential_zero
  potential_setProj potential_conj_kron disc₂_bind disc_readLift viewBy_runtimeR_of_disc Disc
  querySupportedOn_branch_bind lazy_run_realizeT invSupp Sources
  sum_totalWeight_portMass_runtimeR_le_inv totalWeight_portMass_mono
  totalWeight_portMass_union_le sum_totalWeight_portMass_le_count chg_readsProgram chg_map
  CellHardwired)

namespace Quantum.Sphincs.Assembly

/- Membership in the concrete FORS opening's sets is otherwise decided by evaluating them. -/
attribute [local irreducible] forsNeed forsSlots

/-! ## The modes of the counter trials -/

section modes

variable (π : Equiv.Perm (X × Z)) (T : X → Prop)

/-- **The reads a trial mode allows**, for the trial blocks `T`: a free read is a `k`-read at a
trial block keeping the memory; after the `k`-read at `x` with outcome `a` the `k'`-read at
`π (x, a)` keeping the memory; then the `h`-read at `z`. -/
def trRdOk {M' : Type} : TMode → HwRead X Z M' → Prop
  | .free, .readK x u => T x ∧ u = fun m _ ↦ m
  | .afK x a, .readK' y u => y = (π (x, a)).1 ∧ u = fun m _ ↦ m
  | .afK' z, .readH z' _ => z' = z
  | _, _ => False

/-- The calls the trial modes allow, on runtime 1's ports. -/
def trOkR {M : Type} : TMode → (hwReadSpec X Z M).Port → Prop
  | μ, .inl _ => μ = .free
  | μ, .inr c => trRdOk π T μ c

/-- The calls the trial modes allow, on the template's ports. -/
def trOkT {M : Type} : TMode → (SSpec M).Port → Prop
  | μ, .inl (.inl (.inr c)) => trRdOk π T μ c.1
  | μ, _ => μ = .free

/-- The trial mode after a call of the template. -/
def trNxT {M : Type} : TMode → (i : (SSpec M).Port) → (SSpec M).Result i → TMode
  | μ, .inl (.inl (.inr c)), r => rdNx π μ c.1 r
  | _, _, _ => .free

/-- The calls the trial modes allow, on runtime 2's ports with record ports. -/
def trOkZ {M : Type} : TMode → (recHwSpec X Z HPos M).Port → Prop
  | μ, .inl (.inl (.inr c)) => trRdOk π T μ c
  | μ, _ => μ = .free

/-- The trial mode after a call of runtime 2 with record ports. -/
def trNxZ {M : Type} : TMode → (i : (recHwSpec X Z HPos M).Port) →
    (recHwSpec X Z HPos M).Result i → TMode
  | μ, .inl (.inl (.inr c)), r => rdNx π μ c r
  | _, _, _ => .free

variable {M : Type} [Fintype M] [DecidableEq M]

variable {π T}

omit [Fintype M] [DecidableEq M] in
theorem trModed_readCall {μ : TMode} {c : HwRead X Z M} (h : trRdOk π T μ c) (B : QReg) :
    ModedE (L := LocalSig.instruments) (trOkR π T) (nxR π) (fun p ↦ rdNx π μ c p.2.2) μ
      (readCall c B) :=
  ⟨h, fun _ ↦ ⟨trivial, fun _ ↦ rfl⟩⟩

variable (π T) in
/-- A stateful program of runtime 1 that is moded from every state. -/
def TrSMod {B : QReg} {σ α : Type} (μ : TMode) (fin : α → TMode)
    (x : StateT σ (QComp (hwReadSpec X Z M) B B) α) : Prop :=
  ∀ s, ModedE (L := LocalSig.instruments) (trOkR π T) (nxR π) (fun p ↦ fin p.2.2.1) μ (x.run s)

section smod

variable {B : QReg} {σ α β : Type}

omit [Fintype M] [DecidableEq M] in
theorem trSMod_bind {x : StateT σ (QComp (hwReadSpec X Z M) B B) α}
    {k : α → StateT σ (QComp (hwReadSpec X Z M) B B) β} {μ : TMode} {f : α → TMode}
    {g : β → TMode} (hx : TrSMod π T μ f x) (hk : ∀ a, TrSMod π T (f a) g (k a)) :
    TrSMod π T μ g (x >>= k) := by
  intro s
  rw [StateT.run_bind]
  exact modedE₂_bind (fin := fun q : α × σ ↦ f q.1) (fin' := fun q : β × σ ↦ g q.1) _ _ (hx s)
    fun p ↦ hk p.1 p.2

omit [Fintype M] [DecidableEq M] in
theorem trSMod_pure (a : α) (f : α → TMode) :
    TrSMod π T (f a) f (pure a : StateT σ (QComp (hwReadSpec X Z M) B B) α) := by
  intro s
  rw [StateT.run_pure]
  rfl

omit [Fintype M] [DecidableEq M] in
theorem trSMod_map {x : StateT σ (QComp (hwReadSpec X Z M) B B) α} (g : α → β) {μ : TMode}
    {f : β → TMode} (hx : TrSMod π T μ (fun a ↦ f (g a)) x) : TrSMod π T μ f (g <$> x) := by
  intro s
  rw [StateT.run_map]
  exact modedE_map (f := fun q : β × σ ↦ f q.1) (fun p : α × σ ↦ (g p.1, p.2)) (hx s)

omit [Fintype M] [DecidableEq M] in
theorem trSMod_rdK {x : X} (hx : T x) :
    TrSMod π T .free (fun a ↦ .afK x a) (rdK (M := M) B x) :=
  fun s ↦ modedE₂_bind (fin := fun r : Option Z × M ↦ TMode.afK x (r.1.getD 0))
    (fin' := fun q : Z × List (SpongeRead X Z) ↦ TMode.afK x q.1) (readCall (.readK x keepMem) B)
    (fun r ↦ QuantumComp₂.pure (r.1.getD 0, s ++ [SpongeRead.k x (r.1.getD 0)]))
    (trModed_readCall (π := π) (T := T) (μ := .free) (c := .readK x keepMem) ⟨hx, rfl⟩ B)
    fun _ ↦ rfl

omit [Fintype M] [DecidableEq M] in
theorem trSMod_rdK' {x : X} {a : Z} {y : X} (hy : y = (π (x, a)).1) :
    TrSMod π T (.afK x a) (fun c ↦ .afK' ((π (x, a)).2 + c)) (rdK' (M := M) B y) :=
  fun s ↦ modedE₂_bind (fin := fun r : Option Z × M ↦ TMode.afK' ((π (x, a)).2 + r.1.getD 0))
    (fin' := fun q : Z × List (SpongeRead X Z) ↦ TMode.afK' ((π (x, a)).2 + q.1))
    (readCall (.readK' y keepMem) B)
    (fun r ↦ QuantumComp₂.pure (r.1.getD 0, s ++ [SpongeRead.k' y (r.1.getD 0)]))
    (trModed_readCall (π := π) (T := T) (μ := .afK x a) (c := .readK' y keepMem) ⟨hy, rfl⟩ B)
    fun _ ↦ rfl

omit [Fintype M] [DecidableEq M] in
theorem trSMod_rdHU {z z' : Z} (hz : z' = z) (u : M → Option X → M) :
    TrSMod π T (.afK' z) (fun _ ↦ .free) (rdHU M B z' u) :=
  fun s ↦ modedE₂_bind (fin := fun _ : Option X × M ↦ TMode.free)
    (fin' := fun _ : X × List (SpongeRead X Z) ↦ TMode.free) (readCall (.readH z' u) B)
    (fun r ↦ QuantumComp₂.pure (r.1.getD 0, s ++ [SpongeRead.h z' (r.1.getD 0)]))
    (trModed_readCall (π := π) (T := T) (μ := .afK' z) (c := .readH z' u) hz B) fun _ ↦ rfl

omit [Fintype M] [DecidableEq M] in
/-- **A trial's round of reads**, from a state with zero capacity and a trial block. -/
theorem trSMod_rdRoundU (u : X → X → M → Option X → M) (s : X × Z) (b : X) (hs : s.2 = 0)
    (hb : T (s.1 + b)) :
    TrSMod π T .free (fun _ ↦ .free) (rdRoundU M u π B s b) := by
  unfold rdRoundU
  refine trSMod_bind (trSMod_rdK hb) fun a ↦ ?_
  refine trSMod_bind (trSMod_rdK' (a := a) (by rw [hs, zero_add])) fun c ↦ ?_
  refine trSMod_bind (trSMod_rdHU (by rw [hs, zero_add]) _) fun w ↦ ?_
  exact trSMod_pure (f := fun _ ↦ TMode.free) _

omit [Fintype M] [DecidableEq M] in
/-- **A trial's hash** of a one-block input whose block is a trial block. -/
theorem trModed_hashTrial (u : X → X → M → Option X → M) (input : HashSig.HashInput) (b : X)
    (hb : blocks input = [b]) (hT : T b) :
    ModedE (L := LocalSig.instruments) (trOkR π T) (nxR π) (fun _ ↦ .free) .free
      (hashTrial M u π B input) := by
  have hfold : TrSMod π T (B := B) .free (fun _ ↦ .free)
      ((blocks input).foldlM (rdRoundU M u π B) (0, 0)) := by
    rw [hb]
    exact trSMod_bind (trSMod_rdRoundU u (0, 0) b rfl (by rw [zero_add]; exact hT))
      fun s' ↦ trSMod_pure (f := fun _ ↦ TMode.free) s'
  exact modedE_map (f := fun _ ↦ TMode.free) Prod.fst
    (trSMod_map (f := fun _ ↦ TMode.free) (out256 : X → HashOutput)
      (trSMod_map (f := fun _ ↦ TMode.free) (fun s : X × Z ↦ s.1) hfold) [])

omit [Fintype M] [DecidableEq M] in
/-- **The counter search** of key `K` on the value `m` is moded by the trial blocks. -/
theorem trModed_grindK (upd : TrialUpd M) (pub : Pub) (K : Key) (m : Digest) :
    ∀ n cnt, ModedE (L := LocalSig.instruments) (trOkR pub.perm TrialBlock) (nxR pub.perm)
      (fun _ ↦ .free) .free (grindK M upd pub B K m n cnt)
  | 0, _ => rfl
  | n + 1, cnt => by
    rw [grindK]
    have hb := blocks_encIn pub K m (BitVec.ofNat counterBits cnt)
    refine modedE₂_bind (fin := fun _ ↦ TMode.free) (fin' := fun _ ↦ TMode.free) _ _
      (trModed_hashTrial (upd K) _ _ hb ⟨pub.seed, K, m, _, hb⟩) fun out ↦ ?_
    split
    · rfl
    · exact trModed_grindK upd pub K m n (cnt + 1)

end smod

/-! ### Lifting the modes to the template and to runtime 2 -/

omit [Fintype M] [DecidableEq M] in
theorem trRdOk_liftRead {μ : TMode} {c : HwRead X Z M} (h : trRdOk π T μ c) :
    trRdOk π T μ (liftRead (S := HPos) c) := by
  rcases μ with _ | ⟨x, a⟩ | z <;> rcases c with ⟨z', u⟩ | ⟨x', u⟩ | ⟨y, u⟩
  all_goals first
    | exact h
    | exact ⟨h.1, by rw [h.2]⟩

omit [Fintype M] [DecidableEq M] in
/-- **Lifting runtime 1's moded programs to templates.** -/
theorem trModed_readLift {Ω : QReg → Type} {A : QReg} {fin : (Σ u, Ω u) → TMode}
    (y : QuantumComp LocalSig.instruments (hwReadSpec X Z M) Ω A) {μ : TMode}
    (hy : ModedE (trOkR π T) (nxR π) fin μ y) :
    ModedE (trOkT π T) (trNxT π) fin μ (readLift goodAll y) := by
  induction y using IFreeM.inductionOn generalizing μ with
  | pure _ a => exact hy
  | liftBind _ c next ih =>
    show ModedE _ _ _ μ (IFreeM.mapLens (readLens goodAll) (IFreeM.liftBind c next))
    rw [IFreeM.mapLens_liftBind]
    rcases c with o | ⟨i | c, E, ℓ⟩
    · exact ⟨trivial, fun b ↦ ih _ (hy.2 _)⟩
    · exact ⟨hy.1, fun b ↦ ih _ (hy.2 _)⟩
    · refine ⟨trRdOk_liftRead hy.1, fun b ↦ ?_⟩
      rcases c with ⟨z, u⟩ | ⟨x, u⟩ | ⟨y, u⟩ <;> rcases μ with _ | ⟨x', a⟩ | z' <;>
        exact ih _ (hy.2 (ULift.up (b.down.1, b.down.2.2)))

omit [Fintype M] [DecidableEq M] in
/-- A sponge program of runtime 1 is moded, free throughout. -/
theorem trModed_liftOrdinary {Ω : QReg → Type} {A : QReg}
    (y : QuantumComp LocalSig.instruments (spongeSpec X Z) Ω A) :
    ModedE (trOkR π T) (nxR π) (fun _ ↦ .free) .free
      (y.liftOrdinary (t := hwReadCmdSpec X Z M)) := by
  induction y using IFreeM.inductionOn with
  | pure _ a => rfl
  | liftBind _ c next ih =>
    show ModedE _ _ _ _ (IFreeM.mapLens QuantumComp.ordinaryLens (IFreeM.liftBind c next))
    rw [IFreeM.mapLens_liftBind]
    rcases c with o | ⟨i, E, ℓ⟩
    · exact ⟨trivial, fun b ↦ ih _⟩
    · exact ⟨rfl, fun b ↦ ih _⟩

omit [Fintype M] [DecidableEq M] in
/-- **Realizing keeps the modes.** -/
theorem trModed_realizeT (v : (s : HPos) → XD s) {L : LocalSig.{u, v}} {Ω : QReg → Type w}
    {A : QReg} {fin : (Σ u, Ω u) → TMode} (y : QuantumComp L (SSpec M) Ω A) {μ : TMode}
    (hy : ModedE (trOkT π T) (trNxT π) fin μ y) :
    ModedE (trOkZ π T) (trNxZ π) fin μ (realizeT v y) := by
  induction y using IFreeM.inductionOn generalizing μ with
  | pure _ a => exact hy
  | liftBind _ c next ih =>
    show ModedE _ _ _ μ (IFreeM.mapLens (tmplLens v) (IFreeM.liftBind c next))
    rw [IFreeM.mapLens_liftBind]
    rcases c with o | ⟨((i | c) | ⟨p, hp⟩) | T', E, ℓ⟩
    · exact ⟨trivial, fun b ↦ ih _ (hy.2 _)⟩
    · exact ⟨hy.1, fun b ↦ ih _ (hy.2 _)⟩
    · exact ⟨hy.1, fun b ↦ ih _ (hy.2 _)⟩
    · cases p <;> exact ⟨hy.1, fun b ↦ ih _ (hy.2 _)⟩
    · exact ⟨hy.1, fun b ↦ ih _ (hy.2 _)⟩

/-! ### The challenge prefix is moded -/

section trialPrefix

variable (π T) in
/-- A template moded from the free mode back to it. -/
abbrev TrFree {Ω : QReg → Type} {A : QReg} (y : QuantumComp LocalSig.instruments (SSpec M) Ω A) :
    Prop :=
  ModedE (trOkT π T) (trNxT π) (fun _ ↦ .free) .free y

omit [Fintype M] [DecidableEq M] in
theorem trFree_bind {A B B' : QReg} {α β : Type} (x : QComp (SSpec M) A B α)
    (g : α → QComp (SSpec M) B B' β) (hx : TrFree π T x) (hg : ∀ a, TrFree π T (g a)) :
    TrFree π T (x.bind g) :=
  modedE₂_bind (fin := fun _ ↦ TMode.free) (fin' := fun _ ↦ TMode.free) x g hx hg

omit [Fintype M] [DecidableEq M] in
theorem trFree_act {A B : QReg} {α : Type} (p : SubInstrument A B α) :
    TrFree π T (QComp.act (spec := SSpec M) p) :=
  ⟨trivial, fun _ ↦ rfl⟩

omit [Fintype M] [DecidableEq M] in
theorem trFree_revealThen {B B' : QReg} {α : Type} (T₀ : Finset HPos)
    (k : RevealVals XD T₀ × (Finset HPos × M) → QComp (SSpec M) B B' α)
    (hk : ∀ r, TrFree π T (k r)) : TrFree π T (revealThen goodAll T₀ k) :=
  ⟨rfl, fun b ↦ trFree_bind _ _ (trFree_act _) fun _ ↦ hk b.down⟩

omit [Fintype M] [DecidableEq M] in
theorem trFree_progThen {B B' : QReg} {α : Type} (p : LazyProg X Z HPos XD) (hp : goodAll p)
    (k : QComp (SSpec M) B B' α) (hk : TrFree π T k) : TrFree π T (progThen p hp k) :=
  ⟨rfl, fun _ ↦ trFree_bind _ _ (trFree_act _) fun _ ↦ hk⟩

omit [Fintype M] [DecidableEq M] in
theorem trFree_progPorts (B : QReg) (ps : List (LazyProg X Z HPos XD)) :
    TrFree π T (progPorts M B ps) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => exact trFree_progThen p trivial _ ih

omit [Fintype M] [DecidableEq M] in
theorem trFree_progSlots (pub : Pub) (B : QReg) (ss : List Slot) :
    TrFree π T (progSlots M pub B ss) := by
  induction ss with
  | nil => rfl
  | cons s ss ih => exact trFree_bind _ _ (trFree_progPorts B _) fun _ ↦ ih

omit [Fintype M] [DecidableEq M] in
theorem trFree_forsOpenT (pub : Pub) (B : QReg) (idx : Index)
    (lv : ForsTreeIndex → ForsLeafIndex) : TrFree π T (forsOpenT M pub B idx lv) := by
  unfold forsOpenT
  exact trFree_revealThen _ _ fun _ ↦ trFree_bind _ _ (trFree_progSlots pub B _) fun _ ↦ rfl

variable (upd : TrialUpd M)

omit [Fintype M] [DecidableEq M] in
/-- **A layer signature**: its counter search is moded by the trial blocks. -/
theorem trFree_signLayerT (pub : Pub) (B : QReg) (K : Key) :
    TrFree pub.perm TrialBlock (signLayerT M upd pub B K) := by
  unfold signLayerT
  refine trFree_revealThen _ _ fun r₀ ↦ trFree_bind _ _
    (trModed_readLift _ (trModed_grindK upd pub K _ _ _)) fun g ↦ ?_
  rcases g with _ | ⟨c, x⟩
  · rfl
  · exact trFree_revealThen _ _ fun r ↦ trFree_bind _ _ (trFree_progSlots pub B _) fun _ ↦ rfl

omit [Fintype M] [DecidableEq M] in
/-- **A signature** is moded, for every digest policy. -/
theorem trFree_signT (pol : DigestPolicy) (pub : Pub) (B : QReg) (msg : Message) :
    TrFree pub.perm TrialBlock (signT M upd pol pub B msg) := by
  unfold signT
  refine trFree_revealThen _ _ fun _ ↦ trFree_revealThen _ _ fun _ ↦ ?_
  refine trFree_bind _ _ (trFree_progPorts B _) fun _ ↦ ?_
  refine trFree_bind _ _ (trFree_forsOpenT pub B _ _) fun _ ↦ ?_
  refine trFree_bind _ _ (trFree_signLayerT upd pub B _) fun s₀ ↦ ?_
  rcases s₀ with _ | bottom
  · rfl
  · refine trFree_bind _ _ (trFree_signLayerT upd pub B _) fun s₁ ↦ ?_
    rcases s₁ with _ | middle
    · rfl
    · refine trFree_bind _ _ (trFree_signLayerT upd pub B _) fun s₂ ↦ ?_
      rcases s₂ with _ | top <;> rfl

omit [Fintype M] [DecidableEq M] in
/-- **The challenger** is moded, for every digest policy. -/
theorem trFree_challengeT (pol : DigestPolicy) (pub : Pub) (A : QReg)
    (cmd : QuantumComp.Cmd LocalSig.instruments.{0} sAdvSpec A) :
    ModedE (trOkT pub.perm TrialBlock) (trNxT pub.perm) (fun _ ↦ .free) .free
      (challengeT M upd pol pub A cmd) := by
  rcases cmd with o | ⟨q | msg, E, ℓ⟩
  · exact trModed_readLift _ (trModed_liftOrdinary _)
  · exact trModed_readLift _ (trModed_liftOrdinary _)
  · exact modedE_bind _ _ (trFree_bind _ _ (trFree_act _)
      fun _ ↦ trFree_signT upd pol pub _ msg) fun _ _ ↦ rfl

omit [Fintype M] [DecidableEq M] in
/-- Substituting moded trees that start and end free. -/
theorem trModed_substitute {spec : QuantumOracleSpec.{0, 0}}
    (σ : IPFunctor.CommandSubstitution (QuantumComp.toIPFunctor LocalSig.instruments spec)
      (QuantumComp.toIPFunctor LocalSig.instruments (SSpec M)))
    (hσ : ∀ A c, ModedE (trOkT π T) (trNxT π) (fun _ ↦ .free) .free (σ A c))
    {Ω : QReg → Type} {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments spec) Ω A) :
    ModedE (trOkT π T) (trNxT π) (fun _ ↦ .free) .free (x.substitute σ) := by
  induction x using IFreeM.inductionOn with
  | pure _ _ => rfl
  | liftBind s c next ih =>
    rw [IFreeM.substitute_liftBind]
    exact modedE_bind _ _ (hσ s c) fun u ans ↦ (modedE_cast ans.2 _ _).mpr (ih ans.1)

omit [Fintype M] [DecidableEq M] in
/-- **The challenge prefix is moded**: its reads are counter trials, for every digest policy. -/
theorem trFree_prefixT (pol : DigestPolicy) (pub : Pub) (A : SAdversary) :
    TrFree pub.perm TrialBlock (prefixT M upd pol pub A) := by
  unfold prefixT challengedT
  exact trFree_revealThen _ _ fun _ ↦ trFree_bind _ _
    (trModed_substitute _ (trFree_challengeT upd pol pub) _) fun _ ↦ rfl

end trialPrefix

end modes

/-! ## Moving the trials' hidden mass onto their `k`-reads -/

section trialW

variable {M : Type} [Fintype M] [DecidableEq M] {π : Equiv.Perm (X × Z)} {Hh : Set Z}
  {Hk' : Set X}

theorem portMass_readRec_read_sph (Hk : Set X) (c : HwRead X Z (Finset HPos × M))
    (σ : Matrix (Unit × HwReg X Z (Finset HPos × M)) (Unit × HwReg X Z (Finset HPos × M)) ℂ) :
    portMass (S := HPos) (M' := M) (fun i ↦ readRecPort M i = true) Hh Hk Hk'
      (.inl (.inl (.inr c))) σ = diagMass (hidSet Hh Hk Hk' (.inl (.inr c))) σ := by
  have hQ : readRecPort M (.inl (.inl (.inr c))) = true := rfl
  simp only [portMass, hQ, ↓reduceIte]
  exact congrFun (congrFun (Quantum.Xmss.Assembly.extWeight_hiddenMass_eq
    (t := recSpec HPos M) (M := Finset HPos × M) Hh Hk Hk') (.inl (.inl (.inr c)))) σ

theorem portMass_readRec_eq_zero_sph (Hk : Set X) {i : (recHwSpec X Z HPos M).Port}
    (hi : ∀ c, i ≠ .inl (.inl (.inr c)))
    (σ : Matrix ((recHwSpec X Z HPos M).In i × QReg.of (HwReg X Z (Finset HPos × M)))
      ((recHwSpec X Z HPos M).In i × QReg.of (HwReg X Z (Finset HPos × M))) ℂ) :
    portMass (fun i ↦ readRecPort M i = true) Hh Hk Hk' i σ = 0 := by
  rcases i with ((i | c) | c) | T
  · rfl
  · exact absurd rfl (hi c)
  · rfl
  · have hQ : readRecPort M (.inr T) = true := rfl
    simp only [portMass, hQ, ↓reduceIte]
    rw [congrFun (congrFun (Quantum.Xmss.Assembly.extWeight_hiddenMass_eq
      (t := recSpec HPos M) Hh Hk Hk') _) σ]
    exact Finset.sum_eq_zero fun a _ ↦ Set.indicator_of_notMem (Set.notMem_empty a) _

theorem step_readH_sph (Hk : Set X) (z : Z) (u : Finset HPos × M → Option X → Finset HPos × M)
    {σ : Matrix (Unit × HwReg X Z (Finset HPos × M)) (Unit × HwReg X Z (Finset HPos × M)) ℂ}
    (hσ : σ.PosSemidef) :
    portMass (fun i ↦ readRecPort M i = true) Hh Hk Hk' (.inl (.inl (.inr (.readH z u)))) σ +
        ∑' r : Option X × (Finset HPos × M), ∑ j, potential (kpot π Hh Hk' TMode.free j)
          (MatrixMap.conj (hwReadKraus (.readH z u) r) σ) ≤
      ∑ j, potential (kpot π Hh Hk' (.afK' z) j) σ + 0 := by
  rw [portMass_readRec_read_sph]
  simp only [sum_potential_kpot_free, tsum_zero, add_zero]
  rw [Fintype.sum_option]
  simp only [kpot, potential_zero, Finset.sum_const_zero, add_zero]
  rw [potential_setProj _ hσ]
  exact le_rfl

theorem step_readK_sph (Hk : Set X) (x : X) (hx : x ∉ Hk)
    (σ : Matrix (Unit × HwReg X Z (Finset HPos × M)) (Unit × HwReg X Z (Finset HPos × M)) ℂ) :
    portMass (fun i ↦ readRecPort M i = true) Hh Hk Hk'
        (.inl (.inl (.inr (.readK x (fun m _ ↦ m))))) σ +
        ∑' r : Option Z × (Finset HPos × M), ∑ j,
          potential (kpot π Hh Hk' (.afK x (r.1.getD 0)) j)
            (MatrixMap.conj (hwReadKraus (.readK x (fun m _ ↦ m)) r) σ) ≤
      ∑ j, potential (kpot π Hh Hk' TMode.free j) σ +
        trialW π Hh Hk' (S := HPos) (M := M) (.inl (.inl (.inr (.readK x (fun m _ ↦ m))))) σ := by
  have h0 : diagMass (hidSet Hh Hk Hk' (.inl (.inr (.readK x (fun m _ ↦ m)))) :
      Set (Unit × HwReg X Z (Finset HPos × M))) σ = 0 :=
    Finset.sum_eq_zero fun p _ ↦ Set.indicator_of_notMem (fun hp ↦ hx hp.1) _
  rw [portMass_readRec_read_sph, h0, zero_add, sum_potential_kpot_free, zero_add, tsum_fintype]
  exact le_rfl

theorem step_readK'_sph (Hk : Set X) (x : X) (a : Z)
    {σ : Matrix (Unit × HwReg X Z (Finset HPos × M)) (Unit × HwReg X Z (Finset HPos × M)) ℂ}
    (hσ : σ.PosSemidef) :
    portMass (fun i ↦ readRecPort M i = true) Hh Hk Hk'
        (.inl (.inl (.inr (.readK' (π (x, a)).1 (fun m _ ↦ m))))) σ +
        ∑' r : Option Z × (Finset HPos × M), ∑ j,
          potential (kpot π Hh Hk' (.afK' ((π (x, a)).2 + r.1.getD 0)) j)
            (MatrixMap.conj (hwReadKraus (.readK' (π (x, a)).1 (fun m _ ↦ m)) r) σ) ≤
      ∑ j, potential (kpot π Hh Hk' (.afK x a) j) σ + 0 := by
  rw [portMass_readRec_read_sph, Fintype.sum_option, tsum_fintype, add_zero]
  simp only [kpot]
  rw [potential_setProj _ hσ]
  refine add_le_add le_rfl (le_of_eq (Finset.sum_congr rfl fun r _ ↦ ?_))
  rw [Fintype.sum_option]
  simp only [potential_zero, Finset.sum_const_zero, add_zero]
  exact potential_conj_kron _ _ σ

/-- **The step condition of the trial modes**: in runtime 2 with record ports, the hidden mass of
every allowed call plus the potentials after it is at most the potentials before plus the trial
charge, when no trial block is a hidden `k`-cell. -/
theorem trial_step_sph (m₀ : Finset HPos × M) (T : X → Prop) (Hk : Set X)
    (hk : ∀ x, T x → x ∉ Hk) (μ : TMode) (i : (recHwSpec X Z HPos M).Port)
    (σ : Matrix ((recHwSpec X Z HPos M).In i × QReg.of (HwReg X Z (Finset HPos × M)))
      ((recHwSpec X Z HPos M).In i × QReg.of (HwReg X Z (Finset HPos × M))) ℂ)
    (hσ : σ.PosSemidef) (hok : trOkZ π T μ i) :
    portMass (fun i ↦ readRecPort M i = true) Hh Hk Hk' i σ +
        ∑' r, ∑ j, potential (kpot π Hh Hk' (trNxZ π μ i r) j)
          (((runtimeR m₀).step i).branch r σ) ≤
      ∑ j, potential (kpot π Hh Hk' μ j) σ + trialW π Hh Hk' i σ := by
  rcases i with ((i | c) | c) | T'
  · obtain rfl : μ = .free := hok
    rw [portMass_readRec_eq_zero_sph Hk (fun _ h ↦ by cases h), zero_add, sum_potential_kpot_free]
    exact (ENNReal.tsum_le_tsum fun r ↦ (sum_potential_kpot_free π Hh Hk' _).le).trans
      (by simp)
  · have hb : ∀ r, ((runtimeR m₀).step (.inl (.inl (.inr c)))).branch r σ =
        MatrixMap.conj (hwReadKraus c r) σ := fun r ↦
      LinearMap.congr_fun (spongeHardwiredRuntime_step_read (hwEmpty X Z) m₀ c r) σ
    simp only [hb]
    rcases c with ⟨z, u⟩ | ⟨x, u⟩ | ⟨y, u⟩ <;> rcases μ with _ | ⟨x₀, a⟩ | z₀
    all_goals try exact False.elim hok
    · obtain rfl : z = z₀ := hok
      exact step_readH_sph Hk z u hσ
    · obtain ⟨hT, rfl⟩ := hok
      exact step_readK_sph Hk x (hk x hT) σ
    · obtain ⟨rfl, rfl⟩ := hok
      exact step_readK'_sph Hk x₀ a hσ
  · obtain rfl : μ = .free := hok
    rw [portMass_readRec_eq_zero_sph Hk (fun _ h ↦ by simp at h), zero_add,
      sum_potential_kpot_free]
    exact (ENNReal.tsum_le_tsum fun r ↦ (sum_potential_kpot_free π Hh Hk' _).le).trans
      (by simp)
  · obtain rfl : μ = .free := hok
    rw [portMass_readRec_eq_zero_sph Hk (fun _ h ↦ by simp at h), zero_add,
      sum_potential_kpot_free]
    exact (ENNReal.tsum_le_tsum fun r ↦ (sum_potential_kpot_free π Hh Hk' _).le).trans
      (by simp)

variable (Hh Hk')

/-- **The trials' hidden mass moves onto their `k`-reads**: the hidden mass of the challenge
prefix's reads is at most the trial charge `trialW`, when no trial block is a hidden `k`-cell. -/
theorem totalWeight_prefixT_le_trialW_sph (upd : TrialUpd M) (pol : DigestPolicy)
    (m₀ : Finset HPos × M) (pub : Pub) (A : SAdversary) (v : (s : HPos) → XD s) (Hk : Set X)
    (hk : ∀ x, TrialBlock x → x ∉ Hk)
    {ρ : Matrix (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M)))
      (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M))) ℂ} (hρ : ρ.PosSemidef) :
    (runtimeR m₀).totalWeight LocalSig.Interp.instruments
        (portMass (fun i ↦ readRecPort M i = true) Hh Hk Hk')
        (realizeT v (prefixT M upd pol pub A)) ρ ≤
      (runtimeR m₀).totalWeight LocalSig.Interp.instruments (trialW pub.perm Hh Hk')
        (realizeT v (prefixT M upd pol pub A)) ρ :=
  totalWeight_le_moded_of_zero (runtimeR m₀) LocalSig.Interp.instruments
    (kpot pub.perm Hh Hk') _ _
    (fun μ i σ hσ hok ↦ trial_step_sph m₀ TrialBlock Hk hk μ i σ hσ hok)
    (realizeT v (prefixT M upd pol pub A)) .free (fun _ ↦ rfl)
    (trModed_realizeT v _ (trFree_prefixT upd pol pub A)) hρ

end trialW

/-! ## The verification's reads -/

section verify

variable {M : Type} [Fintype M] [DecidableEq M] {L : LocalSig.{u, v}} {Ω : QReg → Type w}

omit [Fintype M] [DecidableEq M] in
theorem invP_mono_sph {pub : Pub} {v : (s : HPos) → XD s} {C C' : Set (HwProg X Z)}
    (h : C ⊆ C') {r : HwReg X Z (Finset HPos × M)} (hr : InvP pub v C r) : InvP pub v C' r :=
  fun s hs q hq hl p hp ↦ (hr s hs q hq hl p hp).imp_right fun hc ↦ h hc

/-- **The pending invariant along a run** of a realized template keeping it (`HP`): every
branch of the run is supported on the invariant with the final pending set. -/
theorem querySupportedOn_run_hp_sph (m₀ : Finset HPos × M) (I : L.Interp) (pub : Pub)
    (v : (s : HPos) → XD s) {A : QReg} (y : QuantumComp L (SSpec M) Ω A) :
    ∀ C C', HP pub v y C C' → ∀ ρ : Matrix (A × (runtimeR m₀).D) (A × (runtimeR m₀).D) ℂ,
      QuerySupportedOn (fun m : A × (runtimeR m₀).D ↦ m.2) {s | InvP pub v C s} ρ →
      ∀ p : Σ u, Ω u, QuerySupportedOn (fun m : p.1 × (runtimeR m₀).D ↦ m.2)
        {s | InvP pub v C' s} (((runtimeR m₀).run I (realizeT v y)).branch p ρ) := by
  classical
  induction y using QuantumComp.inductionOn with
  | pure _ y =>
    intro C C' hy ρ hρ p
    show QuerySupportedOn _ _
      ((DSubInstrument.ret (fun p : Σ u, Ω u ↦ p.1 × (runtimeR m₀).D) ⟨_, y⟩).branch p ρ)
    by_cases hp : p = ⟨_, y⟩
    · subst hp
      rw [DSubInstrument.branch_ret_self]
      exact hρ.imp fun _ h ↦ invP_mono_sph hy h
    · rw [DSubInstrument.branch_ret_of_ne _ hp]
      exact querySupportedOn_zero _ _
  | primBind _ o k ih =>
    intro C C' hy ρ hρ p
    show QuerySupportedOn _ _
      ((((I o).frame _).bind fun b ↦ (runtimeR m₀).run I (realizeT v (k b))).branch p ρ)
    exact querySupportedOn_branch_bind ((I o).frame _)
      (fun b ↦ (runtimeR m₀).run I (realizeT v (k b))) p ρ fun b ↦ ih b C C' (hy.2 (ULift.up b))
      _ (QuerySupportedOn.amplify_snd (q := fun s ↦ s) hρ _) p
  | queryBind _ i E ℓ k ih =>
    intro C C' hy ρ hρ p
    rcases i with ((i | c) | ⟨p', hp⟩) | T
    · refine querySupportedOn_branch_bind ((runtimeR m₀).queryStep (.inl (.inl (.inl i))) E ℓ)
        (fun r ↦ (runtimeR m₀).run I (realizeT v (k r))) p ρ fun r ↦ ?_
      exact ih r C C' (hy.2 (ULift.up r)) _
        (Quantum.Xmss.Hybrid.querySupportedOn_queryStep (runtimeR m₀) (fun s ↦ s)
          (.inl (.inl (.inl i))) r (stepInv_sponge m₀ pub v i C r) E ℓ hρ) p
    · refine querySupportedOn_branch_bind ((runtimeR m₀).queryStep (.inl (.inl (.inr c.1))) E ℓ)
        (fun r ↦ (runtimeR m₀).run I (realizeT v (k r))) p ρ fun r ↦ ?_
      exact ih r C C' (hy.2 (ULift.up r)) _
        (Quantum.Xmss.Hybrid.querySupportedOn_queryStep (runtimeR m₀) (fun s ↦ s)
          (.inl (.inl (.inr c.1))) r (stepInv_read m₀ pub v c hy.1.2 C r) E ℓ hρ) p
    · cases p' with
      | programH T₀ c =>
        refine querySupportedOn_branch_bind ((runtimeR m₀).queryStep
          (.inl (.inr ((LazyProg.programH T₀ c).realize v))) E ℓ)
          (fun r ↦ (runtimeR m₀).run I (realizeT v (k r))) p ρ fun r ↦ ?_
        exact ih r _ C' (hy.2 (ULift.up r)) _
          (Quantum.Xmss.Hybrid.querySupportedOn_queryStep (runtimeR m₀) (fun s ↦ s)
            (.inl (.inr ((LazyProg.programH T₀ c).realize v))) r
            (stepInv_prog m₀ pub v _ C r) E ℓ hρ) p
      | programK T₀ c =>
        refine querySupportedOn_branch_bind ((runtimeR m₀).queryStep
          (.inl (.inr ((LazyProg.programK T₀ c).realize v))) E ℓ)
          (fun r ↦ (runtimeR m₀).run I (realizeT v (k r))) p ρ fun r ↦ ?_
        exact ih r _ C' (hy.2 (ULift.up r)) _
          (Quantum.Xmss.Hybrid.querySupportedOn_queryStep (runtimeR m₀) (fun s ↦ s)
            (.inl (.inr ((LazyProg.programK T₀ c).realize v))) r
            (stepInv_prog m₀ pub v _ C r) E ℓ hρ) p
      | programK' T₀ c =>
        refine querySupportedOn_branch_bind ((runtimeR m₀).queryStep
          (.inl (.inr ((LazyProg.programK' T₀ c).realize v))) E ℓ)
          (fun r ↦ (runtimeR m₀).run I (realizeT v (k r))) p ρ fun r ↦ ?_
        exact ih r _ C' (hy.2 (ULift.up r)) _
          (Quantum.Xmss.Hybrid.querySupportedOn_queryStep (runtimeR m₀) (fun s ↦ s)
            (.inl (.inr ((LazyProg.programK' T₀ c).realize v))) r
            (stepInv_prog m₀ pub v _ C r) E ℓ hρ) p
    · refine querySupportedOn_branch_bind ((runtimeR m₀).queryStep (.inr T) E ℓ)
        (fun m ↦ (runtimeR m₀).run I (realizeT v (k (restrictTo T v, m)))) p ρ fun m ↦ ?_
      exact ih (restrictTo T v, m) _ C' (hy.2 (ULift.up (restrictTo T v, m))) _
        (Quantum.Xmss.Hybrid.querySupportedOn_queryStep (runtimeR m₀) (fun s ↦ s) (.inr T) m
          (stepInv_rec m₀ pub v T C m) E ℓ hρ) p

variable (upd : TrialUpd M)

omit [Fintype M] [DecidableEq M] in
/-- The challenge prefix keeps the invariant, for a digest policy revealing no value position. -/
theorem hp_prefixT_sph {pol : DigestPolicy} (hpol : pol.ValFree) (pub : Pub)
    (v : (s : HPos) → XD s) (A : SAdversary) : HP pub v (prefixT M upd pol pub A) ∅ ∅ :=
  hp_revealThen pub v _ _ fun _ ↦ hp_mono pub v _
    (hp₂_bind pub v _ _ (hp_substitute pub v _ (hp_challengeT pub v upd hpol) _) fun _ ↦
      subset_rfl)
    (revealSet_rootPos pub v) subset_rfl

omit [Fintype M] [DecidableEq M] in
/-- The verification keeps the invariant. -/
theorem hp_verifyT_sph (pub : Pub) (v : (s : HPos) → XD s)
    (x : PublicKey × (Forgery × SignLog Message (Option Signature))) :
    HP pub v (verifyT M pub x) ∅ ∅ :=
  hp₂_bind pub v _ _ (hp_readLift pub v _) fun _ ↦ subset_rfl

omit [Fintype M] [DecidableEq M] in
/-- The verification programs nothing. -/
theorem disc_verifyT_sph (pub : Pub)
    (x : PublicKey × (Forgery × SignLog Message (Option Signature))) (T : Finset HPos) :
    Disc (verifyT M pub x) T :=
  disc₂_bind _ _ (disc_readLift _ _) fun _ _ _ ↦ trivial

omit [Fintype M] [DecidableEq M] in
/-- **The verification's read and record calls**: at most `3 · verifyBlocks`. -/
theorem chg_verifyT_sph (pub : Pub) (v : (s : HPos) → XD s)
    (x : PublicKey × (Forgery × SignLog Message (Option Signature))) :
    IFreeM.IsChargeBound (realizeT v (verifyT M pub x))
      (portCharge fun i ↦ if readRecPort M i = true then 1 else 0) (3 * verifyBlocks) := by
  have he : (fun i ↦ if readRecPort M i = true then 1 else 0) = rCharge M 0 1 0 1 := by
    funext i
    rcases i with ((i | c) | c) | T <;> rfl
  rw [he]
  refine isChargeBound_realizeT 0 1 0 1 v ?_
  have hv := chg_readsProgram (M := M) 0 1 pub.perm (QReg.of Unit) (verify_hashBlocks x.1 x.2.1)
  unfold verifyT
  exact IFreeM.IsChargeBound.mono (FreeM₂.isChargeBound_bind (n₂ := 0)
    (isChargeBound_readLift 0 1 0 1 (chg_map _ Prod.fst hv)) fun _ ↦ trivial)
    (by rw [Nat.add_zero, Nat.mul_one])

/-- **The port masses of the template game split at the verification**: those of the challenge
prefix, plus, for every return value of the prefix, those of the verification from the prefix's
branch at it. -/
theorem totalWeight_portMass_gameT_split_sph (Q : (recHwSpec X Z HPos M).Port → Prop)
    [DecidablePred Q] (pol : DigestPolicy) (m₀ : Finset HPos × M) (pub : Pub) (A : SAdversary)
    (v : (s : HPos) → XD s) (Hh : Set Z) (Hk Hk' : Set X)
    (ρ : Matrix (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M)))
      (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M))) ℂ) (hρ : ρ.PosSemidef) :
    (runtimeR m₀).totalWeight LocalSig.Interp.instruments (portMass Q Hh Hk Hk')
      (realizeT v (gameT M upd pol pub A)) ρ =
      (runtimeR m₀).totalWeight LocalSig.Interp.instruments (portMass Q Hh Hk Hk')
        (realizeT v (prefixT M upd pol pub A)) ρ +
      ∑' a, (runtimeR m₀).totalWeight LocalSig.Interp.instruments (portMass Q Hh Hk Hk')
        (realizeT v (verifyT M pub a))
        (((runtimeR m₀).run₂ LocalSig.Interp.instruments
          (realizeT v (prefixT M upd pol pub A))).branch a ρ) := by
  rw [gameT_eq_prefixT_bind, realizeT_bind₂, portMass_eq_diagMass]
  exact totalWeight_diagMass_bind₂ (runtimeR m₀) _ _ _ _ hρ

/-- **The verification's hidden masses** (Masses' `Sources` with weight `κ` on `SlotInv`, on the
verification run from the prefix's branches, which are lazy and on the invariant): summed over
the hidden values, the hidden masses at the read and record calls of the verification are at most
`κ` per verification read, `3 · verifyBlocks` of them. -/
theorem sum_verifyMass_le_sph {pol : DigestPolicy} (hpol : pol.ValFree) (pub : Pub)
    (A : SAdversary) (m₀ : Finset HPos × M)
    (ρ : Matrix (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M)))
      (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M))) ℂ) (hρ : ρ.PosSemidef)
    (hρ1 : ENNReal.ofReal ρ.trace.re ≤ 1)
    (hs : QuerySupportedOn (fun p : QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M)) ↦
      p.2.2.2.1) {∅} ρ)
    (Hhv : ((s : HPos) → XD s) → Set Z) (Hkv Hk'v : ((s : HPos) → XD s) → Set X) (κ : ℝ≥0∞)
    (src : Sources X Z HPos M HPos XD (fun r ↦ r.2.2.1) (SlotInv M pub) Hhv Hkv Hk'v κ) :
    ∑ v : (s : HPos) → XD s, ∑' a, (runtimeR m₀).totalWeight LocalSig.Interp.instruments
      (portMass (fun i ↦ readRecPort M i = true) (Hhv v) (Hkv v) (Hk'v v))
      (realizeT v (verifyT M pub a))
      (((runtimeR m₀).run₂ LocalSig.Interp.instruments
        (realizeT v (prefixT M upd pol pub A))).branch a ρ) ≤
      κ * (((3 * verifyBlocks : ℕ) : ℝ≥0∞) * Fintype.card ((s : HPos) → XD s)) := by
  set br : ((s : HPos) → XD s) → PublicKey × (Forgery × SignLog Message (Option Signature)) →
      Matrix (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M)))
        (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M))) ℂ := fun v a ↦
    ((runtimeR m₀).run₂ LocalSig.Interp.instruments
      (realizeT v (prefixT M upd pol pub A))).branch a ρ
  have hpos : ∀ v a, (br v a).PosSemidef := fun v a ↦
    ((runtimeR m₀).run₂ LocalSig.Interp.instruments
      (realizeT v (prefixT M upd pol pub A))).posSemidef_branch_apply a hρ
  have hlazy : ∀ a, Lazy (fun p : QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M)) ↦
      p.2.2.2.1) fun v ↦ br v a := fun a ↦
    lazy_run_realizeT LocalSig.Interp.instruments m₀ (prefixT M upd pol pub A) ∅
      (disc_prefixT M upd pol pub A ∅) (fun _ ↦ ρ) (lazy_const _ ρ) (fun _ ↦ suppAt_empty _ ρ)
      ⟨_, rfl, a⟩
  have hinv : ∀ a v, (runtimeR m₀).ForallQueries LocalSig.Interp.instruments
      (invSupp (runtimeR m₀) (fun i ↦ readRecPort M i = true) (SlotInv M pub v))
      (realizeT v (verifyT M pub a)) (br v a) := fun a v ↦
    forallQueries_of_hp (fun c ↦ readRecPort_prog c) m₀ _ pub v _ ∅ ∅ (hp_verifyT_sph pub v a) _
      (querySupportedOn_run_hp_sph m₀ _ pub v (prefixT M upd pol pub A) ∅ ∅
        (hp_prefixT_sph upd hpol pub v A) ρ
        (hs.imp fun _ ha ↦ invP_of_label_empty (Set.mem_singleton_iff.1 ha)) ⟨_, rfl, a⟩)
  have hper : ∀ a, ∑ v : (s : HPos) → XD s, (runtimeR m₀).totalWeight
      LocalSig.Interp.instruments
      (portMass (fun i ↦ readRecPort M i = true) (Hhv v) (Hkv v) (Hk'v v))
      (realizeT v (verifyT M pub a)) (br v a) ≤
      κ * (((3 * verifyBlocks : ℕ) : ℝ≥0∞) * ∑ v, ENNReal.ofReal (br v a).trace.re) := fun a ↦
    sum_totalWeight_portMass_runtimeR_le_inv LocalSig.Interp.instruments
      (fun i ↦ readRecPort M i = true) m₀ (fun r ↦ r.2.2.1)
      (fun v ↦ realizeT v (verifyT M pub a)) (fun v ↦ br v a) (fun v ↦ hpos v a)
      (fun j ↦ (viewBy_runtimeR_of_disc LocalSig.Interp.instruments m₀ (verifyT M pub a) ∅
        (disc_verifyT_sph pub a ∅) (fun v ↦ br v a) (hlazy a) (fun _ ↦ suppAt_empty _ _)
          j).viewByOn _)
      (fun v ↦ SlotInv M pub v) (hinv a) _ _ _ _ src fun v ↦ chg_verifyT_sph pub v a
  have htr : ∀ v, ∑' a, ENNReal.ofReal (br v a).trace.re ≤ 1 := fun v ↦
    (((runtimeR m₀).run₂ LocalSig.Interp.instruments
      (realizeT v (prefixT M upd pol pub A))).isCPTNIFamily.tsum_ofReal_trace_re_le hρ).trans hρ1
  rw [← Summable.tsum_finsetSum fun _ _ ↦ ENNReal.summable]
  calc ∑' a, ∑ v : (s : HPos) → XD s, (runtimeR m₀).totalWeight LocalSig.Interp.instruments
        (portMass (fun i ↦ readRecPort M i = true) (Hhv v) (Hkv v) (Hk'v v))
        (realizeT v (verifyT M pub a)) (br v a)
      ≤ ∑' a, κ * (((3 * verifyBlocks : ℕ) : ℝ≥0∞) * ∑ v, ENNReal.ofReal (br v a).trace.re) :=
        ENNReal.tsum_le_tsum hper
    _ = κ * (((3 * verifyBlocks : ℕ) : ℝ≥0∞) *
          ∑ v : (s : HPos) → XD s, ∑' a, ENNReal.ofReal (br v a).trace.re) := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left,
          Summable.tsum_finsetSum fun _ _ ↦ ENNReal.summable]
    _ ≤ κ * (((3 * verifyBlocks : ℕ) : ℝ≥0∞) * ∑ _v : (s : HPos) → XD s, (1 : ℝ≥0∞)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun v _ ↦ htr v) zero_le) zero_le
    _ = κ * (((3 * verifyBlocks : ℕ) : ℝ≥0∞) * Fintype.card ((s : HPos) → XD s)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

end verify

/-! ## The masked read mass through a reparametrization -/

section good

/-- **The masked average through an injection on a good set**, over an arbitrary finite type
(GradedMasked's `uavg_mask_le_of_injOn` without the product structure). -/
theorem uavg_mask_le_of_injOn_sph {Θ P V : Type*} [Fintype Θ] [Fintype P] [Fintype V]
    (e : Θ → P × V) (G : Θ → Prop) [DecidablePred G] (hinj : Set.InjOn e {t | G t})
    (hcard : Fintype.card P * Fintype.card V ≤ Fintype.card Θ)
    (f : Θ → ℝ≥0∞) (g : P → V → ℝ≥0∞) (hfg : ∀ t, G t → f t ≤ g (e t).1 (e t).2)
    (κ : ℝ≥0∞) (hg : ∀ p, ∑ v, g p v ≤ κ * Fintype.card V) :
    uavg (fun t ↦ if G t then f t else 0) ≤ κ := by
  classical
  set N : ℝ≥0∞ := (Fintype.card Θ : ℝ≥0∞)
  have hgood : ∑ t ∈ Finset.univ.filter G, g (e t).1 (e t).2 ≤ κ * N := by
    have himg : ∑ t ∈ Finset.univ.filter G, g (e t).1 (e t).2 =
        ∑ y ∈ (Finset.univ.filter G).image e, g y.1 y.2 := by
      refine (Finset.sum_image (f := fun y : P × V ↦ g y.1 y.2) ?_).symm
      intro a ha b hb h
      exact hinj (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).2
        (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).2 h
    calc ∑ t ∈ Finset.univ.filter G, g (e t).1 (e t).2
        ≤ ∑ y : P × V, g y.1 y.2 := by
          rw [himg]
          exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      _ = ∑ p, ∑ v, g p v := Fintype.sum_prod_type _
      _ ≤ ∑ _p : P, κ * Fintype.card V := Finset.sum_le_sum fun p _ ↦ hg p
      _ = κ * ((Fintype.card P : ℝ≥0∞) * Fintype.card V) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ring
      _ ≤ κ * N := mul_le_mul_of_nonneg_left (by rw [← Nat.cast_mul]; exact Nat.cast_le.mpr hcard)
          zero_le
  unfold uavg
  rw [← Finset.sum_filter]
  calc N⁻¹ * ∑ t ∈ Finset.univ.filter G, f t
      ≤ N⁻¹ * (κ * N) := mul_le_mul_of_nonneg_left ((Finset.sum_le_sum fun t ht ↦
          hfg t (Finset.mem_filter.mp ht).2).trans hgood) zero_le
    _ = κ * (N⁻¹ * N) := by ring
    _ ≤ κ := by
        by_cases h0 : N = 0
        · simp [h0]
        · rw [ENNReal.inv_mul_cancel h0 (ENNReal.natCast_ne_top _), mul_one]

/-- The arithmetic of the per-public-datum sum, over abstract quantities. -/
theorem split_good_arith (τ κ c N εK cK cV pre ver : ℝ≥0∞) (hpre : pre ≤ τ * cV)
    (hver : ver ≤ κ * (c * cV)) :
    cK * (pre + ver) + cV * (εK * N * cK) ≤ (τ + κ * c + N * εK) * (cV * cK) := by
  calc cK * (pre + ver) + cV * (εK * N * cK)
      ≤ cK * (τ * cV + κ * (c * cV)) + cV * (εK * N * cK) := by gcongr
    _ = (τ + κ * c + N * εK) * (cV * cK) := by ring

/-- A bound on a sum over a product from the iterated sum, over abstract types. -/
theorem sum_prod_le_of_sph {V K : Type*} [Fintype V] [Fintype K] (g : V × K → ℝ≥0∞)
    (c : ℝ≥0∞) (h : ∑ v, ∑ k, g (v, k) ≤ c * ((Fintype.card V : ℝ≥0∞) * Fintype.card K)) :
    ∑ w, g w ≤ c * Fintype.card (V × K) := by
  rw [Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul]
  exact h

variable {M : Type} [Fintype M] [DecidableEq M] (upd : TrialUpd M)

/-- The arithmetic of the per-public-datum sum with an extra term, over abstract quantities. -/
theorem split_good_arith_x (τ κ c N εK κX cK cV pre ver x : ℝ≥0∞) (hpre : pre ≤ τ * cV)
    (hver : ver ≤ κ * (c * cV)) (hx : x ≤ N * κX * cV) :
    cK * (pre + ver) + cV * (εK * N * cK) + cK * x ≤
      (τ + κ * c + N * εK + N * κX) * (cV * cK) := by
  calc cK * (pre + ver) + cV * (εK * N * cK) + cK * x
      ≤ cK * (τ * cV + κ * (c * cV)) + cV * (εK * N * cK) + cK * (N * κX * cV) := by gcongr
    _ = (τ + κ * c + N * εK + N * κX) * (cV * cK) := by ring

/-- A sum of three terms, over an abstract type. -/
theorem sum_three_eq_sph {V : Type*} [Fintype V] (c d : ℝ≥0∞) (a b x : V → ℝ≥0∞) :
    ∑ v, (c * (a v + b v) + d + c * x v) =
      c * (∑ v, a v + ∑ v, b v) + Fintype.card V * d + c * ∑ v, x v := by
  simp only [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_add]

/-- **The masked read mass through a reparametrization, with the trial term on good data.** Let
`e` be injective on the good set `G` of the tables `Θ`, into public data `P`, hidden values and
never-revealed coordinates `K`, with the read mass of the game at a table (public data `pubT t`,
hidden values `valT t`) at most that of the game at `pubP (e t).1` realized at `(e t).2.1` plus
`N r t` (`hmis`, the mismatch). Let the table's hidden cells lie in hidden cells `Hhv`, `Hkv`,
`Hk'v` of the public data and hidden values with sources (`src`, weight `κ`), in cells of the
never-revealed coordinates (at most `εK |K|` of them per cell) and in further cells `Hhx` of the
public data and hidden values whose read mass is `κX` per call (`hX`). Then the masked read mass is
at most the trials' term `τ` (asked on the good hidden values `TG`), `κ` per verification read,
`N εK`, `N κX` and `N` times the masked mismatch `μ`. -/
theorem uavg_mask_readMass_le_split_good_sph {pol : DigestPolicy} (hpol : pol.ValFree)
    (A : SAdversary) (m₀ : Finset HPos × M)
    (ρ : Matrix (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M)))
      (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M))) ℂ) (hρ : ρ.PosSemidef)
    (hρ1 : ENNReal.ofReal ρ.trace.re ≤ 1)
    (hs : QuerySupportedOn (fun p : QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M)) ↦
      p.2.2.2.1) {∅} ρ)
    {Θ P K : Type} [Fintype Θ] [Fintype P] [Fintype K]
    (pubT : Θ → Pub) (valT : Θ → (s : HPos) → XD s) (Hh : Θ → Set Z) (Hk Hk' : Θ → Set X)
    (e : Θ → P × (((s : HPos) → XD s) × K)) (G : Θ → Prop) [DecidablePred G]
    (hinj : Set.InjOn e {t | G t})
    (hcard : Fintype.card P * Fintype.card (((s : HPos) → XD s) × K) ≤ Fintype.card Θ)
    (pubP : P → Pub)
    (Hhv : P → ((s : HPos) → XD s) → Set Z) (Hkv Hk'v : P → ((s : HPos) → XD s) → Set X)
    (κ : ℝ≥0∞)
    (src : ∀ p, Sources X Z HPos M HPos XD (fun r ↦ r.2.2.1) (SlotInv M (pubP p)) (Hhv p) (Hkv p)
      (Hk'v p) κ)
    (Hhk : P → ((s : HPos) → XD s) × K → Set Z) (Hkk Hk'k : P → ((s : HPos) → XD s) × K → Set X)
    (Hhx : P → ((s : HPos) → XD s) → Set Z) (Hkx Hk'x : P → ((s : HPos) → XD s) → Set X)
    (hsub : ∀ t, G t →
      Hh t ⊆ Hhv (e t).1 (e t).2.1 ∪ Hhk (e t).1 (e t).2 ∪ Hhx (e t).1 (e t).2.1 ∧
      Hk t ⊆ Hkv (e t).1 (e t).2.1 ∪ Hkk (e t).1 (e t).2 ∪ Hkx (e t).1 (e t).2.1 ∧
      Hk' t ⊆ Hk'v (e t).1 (e t).2.1 ∪ Hk'k (e t).1 (e t).2 ∪ Hk'x (e t).1 (e t).2.1)
    (εK : ℝ≥0∞)
    (hcH : ∀ p v z, ∑ k, (Hhk p (v, k)).indicator (fun _ ↦ (1 : ℝ≥0∞)) z ≤
      εK * Fintype.card K)
    (hcK : ∀ p v y, ∑ k, (Hkk p (v, k)).indicator (fun _ ↦ (1 : ℝ≥0∞)) y ≤
      εK * Fintype.card K)
    (hcK' : ∀ p v y, ∑ k, (Hk'k p (v, k)).indicator (fun _ ↦ (1 : ℝ≥0∞)) y ≤
      εK * Fintype.card K)
    {N : ℕ} (hN : ∀ (pub : Pub) (v : (s : HPos) → XD s),
      IFreeM.IsChargeBound (realizeT v (gameT M upd pol pub A))
        (portCharge fun i ↦ if readRecPort M i = true then 1 else 0) N)
    (κX : ℝ≥0∞)
    (hX : ∀ p, ∑ v, (runtimeR m₀).totalWeight LocalSig.Interp.instruments
      (portMass (fun i ↦ readRecPort M i = true) (Hhx p v) (Hkx p v) (Hk'x p v))
      (realizeT v (gameT M upd pol (pubP p) A)) ρ ≤ N * κX * Fintype.card ((s : HPos) → XD s))
    (r : Θ → ℝ≥0∞)
    (hmis : ∀ t, G t → ∀ (Hh₀ : Set Z) (Hk₀ Hk'₀ : Set X),
      (runtimeR m₀).totalWeight LocalSig.Interp.instruments
          (portMass (fun i ↦ readRecPort M i = true) Hh₀ Hk₀ Hk'₀)
          (realizeT (valT t) (gameT M upd pol (pubT t) A)) ρ ≤
        (runtimeR m₀).totalWeight LocalSig.Interp.instruments
          (portMass (fun i ↦ readRecPort M i = true) Hh₀ Hk₀ Hk'₀)
          (realizeT (e t).2.1 (gameT M upd pol (pubP (e t).1) A)) ρ + N * r t)
    (μ : ℝ≥0∞) (hrev : uavg (fun t ↦ if G t then r t else 0) ≤ μ)
    (TG : P → ((s : HPos) → XD s) → Prop) [∀ p, DecidablePred (TG p)]
    (hTG : ∀ t, G t → TG (e t).1 (e t).2.1) (τ : ℝ≥0∞)
    (htrial : ∀ p, ∑ v : (s : HPos) → XD s, (if TG p v then (runtimeR m₀).totalWeight
      LocalSig.Interp.instruments
      (portMass (fun i ↦ readRecPort M i = true) (Hhv p v) (Hkv p v) (Hk'v p v))
      (realizeT v (prefixT M upd pol (pubP p) A)) ρ else 0) ≤
        τ * Fintype.card ((s : HPos) → XD s)) :
    uavg (fun t ↦ if G t then (runtimeR m₀).totalWeight LocalSig.Interp.instruments
      (readMass (Hh t) (Hk t) (Hk' t)) (realizeT (valT t) (gameT M upd pol (pubT t) A)) ρ
        else 0) ≤
      τ + κ * ((3 * verifyBlocks : ℕ) : ℝ≥0∞) + N * εK + N * κX + N * μ := by
  simp only [readMass_eq_portMass]
  set pre : P → ((s : HPos) → XD s) → ℝ≥0∞ := fun p v ↦ if TG p v then
    (runtimeR m₀).totalWeight LocalSig.Interp.instruments
      (portMass (fun i ↦ readRecPort M i = true) (Hhv p v) (Hkv p v) (Hk'v p v))
      (realizeT v (prefixT M upd pol (pubP p) A)) ρ else 0 with hpre
  set ver : P → ((s : HPos) → XD s) → ℝ≥0∞ := fun p v ↦ ∑' a, (runtimeR m₀).totalWeight
    LocalSig.Interp.instruments
    (portMass (fun i ↦ readRecPort M i = true) (Hhv p v) (Hkv p v) (Hk'v p v))
    (realizeT v (verifyT M (pubP p) a))
    (((runtimeR m₀).run₂ LocalSig.Interp.instruments
      (realizeT v (prefixT M upd pol (pubP p) A))).branch a ρ) with hver
  set ext : P → ((s : HPos) → XD s) × K → ℝ≥0∞ := fun p w ↦ (runtimeR m₀).totalWeight
    LocalSig.Interp.instruments
    (portMass (fun i ↦ readRecPort M i = true) (Hhk p w) (Hkk p w) (Hk'k p w))
    (realizeT w.1 (gameT M upd pol (pubP p) A)) ρ with hext
  set xt : P → ((s : HPos) → XD s) → ℝ≥0∞ := fun p v ↦ (runtimeR m₀).totalWeight
    LocalSig.Interp.instruments
    (portMass (fun i ↦ readRecPort M i = true) (Hhx p v) (Hkx p v) (Hk'x p v))
    (realizeT v (gameT M upd pol (pubP p) A)) ρ with hxt
  set g : P → ((s : HPos) → XD s) × K → ℝ≥0∞ := fun p w ↦
    pre p w.1 + ver p w.1 + ext p w + xt p w.1 with hg
  have hle : ∀ t, (if G t then (runtimeR m₀).totalWeight LocalSig.Interp.instruments
      (portMass (fun i ↦ readRecPort M i = true) (Hh t) (Hk t) (Hk' t))
      (realizeT (valT t) (gameT M upd pol (pubT t) A)) ρ else 0) ≤
      (if G t then g (e t).1 (e t).2 else 0) + (N : ℝ≥0∞) * (if G t then r t else 0) := by
    intro t
    by_cases ht : G t
    · obtain ⟨h1, h2, h3⟩ := hsub t ht
      simp only [ht, ↓reduceIte, hg, hpre, hver, hext, hxt, hTG t ht]
      refine (hmis t ht _ _ _).trans (add_le_add ?_ le_rfl)
      refine (totalWeight_portMass_mono _ _ m₀ h1 h2 h3 _ hρ).trans
        ((totalWeight_portMass_union_le _ _ m₀ _ _ _ _ _ _ _ hρ).trans (add_le_add
          ((totalWeight_portMass_union_le _ _ m₀ _ _ _ _ _ _ _ hρ).trans (add_le_add
            (le_of_eq ?_) le_rfl)) le_rfl))
      exact totalWeight_portMass_gameT_split_sph upd _ pol m₀ _ A _ _ _ _ ρ hρ
    · simp only [ht, ↓reduceIte, mul_zero, add_zero, le_refl]
  have hgsum : ∀ p, ∑ w, g p w ≤
      (τ + κ * ((3 * verifyBlocks : ℕ) : ℝ≥0∞) + N * εK + N * κX) *
        Fintype.card (((s : HPos) → XD s) × K) := by
    intro p
    have hK : ∀ v : (s : HPos) → XD s, ∑ k, ext p (v, k) ≤ εK * N * Fintype.card K := fun v ↦
      (sum_totalWeight_portMass_le_count LocalSig.Interp.instruments _ m₀ _ hρ
        (fun k ↦ Hhk p (v, k)) (fun k ↦ Hkk p (v, k)) (fun k ↦ Hk'k p (v, k)) εK (hcH p v)
        (hcK p v) (hcK' p v) (hN _ v)).trans
        (by calc (εK * Fintype.card K) * (N * ENNReal.ofReal ρ.trace.re)
              ≤ (εK * Fintype.card K) * (N * 1) := by gcongr
            _ = εK * N * Fintype.card K := by ring)
    have hv1 := sum_verifyMass_le_sph upd hpol (pubP p) A m₀ ρ hρ hρ1 hs (Hhv p) (Hkv p) (Hk'v p) κ
      (src p)
    refine sum_prod_le_of_sph (g p) _ ?_
    calc ∑ v, ∑ k, g p (v, k)
        ≤ ∑ v, ((Fintype.card K : ℝ≥0∞) * (pre p v + ver p v) + εK * N * Fintype.card K +
            (Fintype.card K : ℝ≥0∞) * xt p v) := by
          refine Finset.sum_le_sum fun v _ ↦ ?_
          simp only [hg]
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const,
            Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul]
          exact add_le_add (add_le_add le_rfl (hK v)) le_rfl
      _ = (Fintype.card K : ℝ≥0∞) * (∑ v, pre p v + ∑ v, ver p v) +
          Fintype.card ((s : HPos) → XD s) * (εK * N * Fintype.card K) +
          (Fintype.card K : ℝ≥0∞) * ∑ v, xt p v := sum_three_eq_sph _ _ _ _ _
      _ ≤ _ := split_good_arith_x τ κ _ N εK κX _ _ _ _ _ (htrial p) hv1 (hX p)
  calc uavg (fun t ↦ if G t then (runtimeR m₀).totalWeight LocalSig.Interp.instruments
        (portMass (fun i ↦ readRecPort M i = true) (Hh t) (Hk t) (Hk' t))
        (realizeT (valT t) (gameT M upd pol (pubT t) A)) ρ else 0)
      ≤ uavg (fun t ↦ (if G t then g (e t).1 (e t).2 else 0) +
          (N : ℝ≥0∞) * (if G t then r t else 0)) := uavg_mono hle
    _ = uavg (fun t ↦ if G t then g (e t).1 (e t).2 else 0) +
          (N : ℝ≥0∞) * uavg (fun t ↦ if G t then r t else 0) := by
        rw [uavg_add, uavg_const_mul]
    _ ≤ (τ + κ * ((3 * verifyBlocks : ℕ) : ℝ≥0∞) + N * εK + N * κX) + N * μ :=
        add_le_add (uavg_mask_le_of_injOn_sph e G hinj hcard (fun t ↦ g (e t).1 (e t).2) g
          (fun _ _ ↦ le_rfl) _ hgsum) (mul_le_mul_of_nonneg_left hrev zero_le)

end good

/-! ## At the composed reparametrization -/

section sph

/-- A count of a product's coordinates against the tables, across `Fintype` instances (over
abstract types: comparing the concrete instances unfolds them). -/
theorem le_card_mul_of_eq_inst {α β γ : Type*} (iα iα' : Fintype α) (iβ iβ' : Fintype β)
    (iγ iγ' : Fintype γ)
    (h : @Fintype.card α iα' * @Fintype.card β iβ' = @Fintype.card γ iγ') :
    @Fintype.card α iα * @Fintype.card β iβ ≤ @Fintype.card γ iγ := by
  rw [Subsingleton.elim iα iα', Subsingleton.elim iβ iβ', Subsingleton.elim iγ iγ']
  exact h.le

variable (A : SAdversary) {q : ℕ}
  (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) signatureLimit)
include hperm hsign

open scoped Classical in
/-- **The masked read mass at the composed reparametrization**
(`uavg_mask_readMass_le_split_good_sph` at ReparamFull's `fullE` on MassSources' `MassG S`, the
mismatch MassSources' `mass_le_chgRev`, `N = clsCap`): the trials' term `τ` on the good hidden
values `TG`, `κ` per verification read, `clsCap · εK` for the never-revealed coordinates' cells,
`clsCap · κX` for the further cells `Hhx` and `clsCap · chgRevAvg`. -/
theorem uavg_mask_readMass_le_sph_good (S : PP → ((s : HPos) → XD s) → Prop)
    (ρ : Matrix (QReg.of Unit × QReg.of (HwReg X Z (Mem HPos)))
      (QReg.of Unit × QReg.of (HwReg X Z (Mem HPos))) ℂ) (hρ : ρ.PosSemidef)
    (hρ1 : ENNReal.ofReal ρ.trace.re ≤ 1)
    (hs : QuerySupportedOn (fun p : QReg.of Unit × QReg.of (HwReg X Z (Mem HPos)) ↦
      p.2.2.2.1) {∅} ρ)
    (Hh : FT → Set Z) (Hk Hk' : FT → Set X)
    (Hhv : PP → ((s : HPos) → XD s) → Set Z) (Hkv Hk'v : PP → ((s : HPos) → XD s) → Set X)
    (κ : ℝ≥0∞)
    (src : ∀ p, Sources X Z HPos Selections HPos XD (fun r ↦ r.2.2.1)
      (SlotInv Selections (pubP p)) (Hhv p) (Hkv p) (Hk'v p) κ)
    (Hhk : PP → ((s : HPos) → XD s) × KK → Set Z)
    (Hkk Hk'k : PP → ((s : HPos) → XD s) × KK → Set X)
    (Hhx : PP → ((s : HPos) → XD s) → Set Z) (Hkx Hk'x : PP → ((s : HPos) → XD s) → Set X)
    (hsub : ∀ t, MassG S t →
      Hh t ⊆ Hhv (fullE t).1 (fullE t).2.1 ∪ Hhk (fullE t).1 (fullE t).2 ∪
        Hhx (fullE t).1 (fullE t).2.1 ∧
      Hk t ⊆ Hkv (fullE t).1 (fullE t).2.1 ∪ Hkk (fullE t).1 (fullE t).2 ∪
        Hkx (fullE t).1 (fullE t).2.1 ∧
      Hk' t ⊆ Hk'v (fullE t).1 (fullE t).2.1 ∪ Hk'k (fullE t).1 (fullE t).2 ∪
        Hk'x (fullE t).1 (fullE t).2.1)
    (εK : ℝ≥0∞)
    (hcH : ∀ p v z, ∑ k, (Hhk p (v, k)).indicator (fun _ ↦ (1 : ℝ≥0∞)) z ≤
      εK * Fintype.card KK)
    (hcK : ∀ p v y, ∑ k, (Hkk p (v, k)).indicator (fun _ ↦ (1 : ℝ≥0∞)) y ≤
      εK * Fintype.card KK)
    (hcK' : ∀ p v y, ∑ k, (Hk'k p (v, k)).indicator (fun _ ↦ (1 : ℝ≥0∞)) y ≤
      εK * Fintype.card KK)
    (κX : ℝ≥0∞)
    (hX : ∀ p, ∑ v, (runtimeR m0R).totalWeight LocalSig.Interp.instruments
      (readMass (Hhx p v) (Hkx p v) (Hk'x p v)) (gameR msgPol A (pubP p) v) ρ ≤
        clsCap * κX * Fintype.card ((s : HPos) → XD s))
    (TG : PP → ((s : HPos) → XD s) → Prop) [∀ p, DecidablePred (TG p)]
    (hTG : ∀ t, MassG S t → TG (fullE t).1 (fullE t).2.1) (τ : ℝ≥0∞)
    (htrial : ∀ p, ∑ v : (s : HPos) → XD s, (if TG p v then (runtimeR m0R).totalWeight
      LocalSig.Interp.instruments
      (portMass (fun i ↦ readRecPort Selections i = true) (Hhv p v) (Hkv p v) (Hk'v p v))
      (prefixR msgPol A (pubP p) v) ρ else 0) ≤ τ * Fintype.card ((s : HPos) → XD s)) :
    uavg (fun t ↦ if MassG S t then (runtimeR m0R).totalWeight LocalSig.Interp.instruments
      (readMass (Hh t) (Hk t) (Hk' t)) (gameR msgPol A (pubOf (tabOf t)) (valueAt (tabOf t))) ρ
        else 0) ≤
      τ + κ * ((3 * verifyBlocks : ℕ) : ℝ≥0∞) + clsCap * εK + clsCap * κX +
        clsCap * chgRevAvg A ρ S := by
  have hN := fun pub v ↦ hN_readRec cwUpd msgPol A hperm hsign pub v
  refine uavg_mask_readMass_le_split_good_sph (Θ := FT) (P := PP) (K := KK) cwUpd valFree_msgPol
    A m0R ρ hρ hρ1 hs
    (fun t ↦ pubOf (tabOf t)) (fun t ↦ valueAt (tabOf t)) Hh Hk Hk' fullE (MassG S)
    (fullE_spec (SrcS S) A).1 (le_card_mul_of_eq_inst _ _ _ _ _ _ card_coords) pubP
    Hhv Hkv Hk'v κ src Hhk Hkk Hk'k Hhx Hkx Hk'x hsub εK hcH hcK hcK' hN κX
    (fun p ↦ by
      have h := hX p
      simp only [readMass_eq_portMass] at h
      exact h) (chgRev A ρ)
    (fun t ht _ _ _ ↦ mass_le_chgRev _ A ρ hρ hs S hN t ht _ _ _) _ le_rfl TG hTG τ htrial

end sph

end Quantum.Sphincs.Assembly

end
