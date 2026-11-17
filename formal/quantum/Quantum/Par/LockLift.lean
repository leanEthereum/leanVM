module

public import Quantum.Par.LockstepRounds
public import Quantum.Sponge.Oracle.Hardwired.Runtime
public import VCVio.Quantum.Comp.TotalQueryBound

@[expose] public section

/-!
# Lifting sponge-level programs into the hardwired runtimes

The lockstep simulation (`Quantum.Par.LockstepRounds`) is a program over the sponge ports, single
or in rounds. The hardwired runtimes answer the sponge ports as the `.inl (.inl (.inl p))` ports of
`(hwSpec X Z M).sum t` (`t`: further ports, e.g. record ports).

* **Read runtimes** (`isReadRuntime_spongeHardwired`): the sponge ports of the hardwired oracles
  read their functions off the register in the basis of the compression `compressReg`.
* **Lifting** (`hwLens`, `hwParLens`): a program over the sponge ports, single or in rounds, runs
  against a hardwired runtime as against its sponge part `hwPart t R` (`run_mapLens_hwLens`,
  `run_mapLens_hwParLens`).
* **Programs with one path** (`IsThin`): their weights, then a continuation, are the
  continuation's from the path's leaf (`exists_totalWeight_bind_of_isThin`); the simulation and
  `lockRoundR` have one path.
* **Engine**: commandwise equal runs or weights of two substitutions, into the ports of `R` and
  of `R.par port`, give equal runs (`run_substitute_eq_par`) or weights
  (`totalWeight_substitute_bind_eq_par`).
* **Charges of `lockRoundR`** (`isChargeBound_lockRoundR`, `lockCharge_le_width`,
  `lockCharge_le_depth`).
-/

open IPFunctor Matrix
open scoped ENNReal Kronecker

universe u v

namespace Quantum.Par

open Quantum Quantum.Sponge QuantumRuntime

/-! ## The hardwired sponge oracles are read runtimes -/

section read

variable {X Z M : Type} [Fintype X] [DecidableEq X] [AddCommGroup X] [Fintype Z] [DecidableEq Z]
  [AddCommGroup Z] [Fintype M] [DecidableEq M]

/-- The compression of every database cell is unitary. -/
theorem compressReg_mem_unitaryGroup : compressReg X Z M ∈ unitaryGroup (HwReg X Z M) ℂ := by
  rw [mem_unitaryGroup_iff, star_eq_conjTranspose, conjTranspose_compressReg,
    compressReg_mul_self]

/-- The functions that the ports reading through `rH`, `rK`, `rK'` read off the basis state. -/
def readKeys (rH : HwReg X Z M → Z → X) (rK rK' : HwReg X Z M → X → Z) (s : HwReg X Z M) :
    SpongeKeys X Z :=
  (rH s, rK s, rK' s)

variable (X Z M) in
/-- The functions the hardwired sponge oracles read: the hardwired cells over the databases. -/
def hwKeys : HwReg X Z M → SpongeKeys X Z :=
  readKeys (fun s z ↦ (s.2.1.1 z).getD (s.1.1.lookup z))
    (fun s x ↦ (s.2.1.2.1 x).getD (s.1.2.1.lookup x))
    (fun s x ↦ (s.2.1.2.2 x).getD (s.1.2.2.lookup x))

/-- **The hardwired sponge oracles read their functions** in the basis of the compression. -/
theorem isReadRuntime_spongeHardwired (W₀ : Hw X Z) (m₀ : M) :
    IsReadRuntime ((spongeHardwired X Z W₀ m₀).toRuntime : QuantumRuntime (spongeSpec X Z))
      (compressReg X Z M) (hwKeys X Z M) := by
  intro p
  rw [(spongeHardwired X Z W₀ m₀).toRuntime_step_branch p (), conjTranspose_compressReg]
  cases p <;> rfl

end read

/-! ## The sponge part of a hardwired runtime -/

section part

variable {X Z M : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  (t : QuantumOracleSpec.{0, 0})

variable (X Z M) in
/-- The sponge ports of the hardwired runtime with the further ports `t`. -/
abbrev hwSpongePort : SpongePort → ((hwSpec X Z M).sum t).Port :=
  fun p ↦ .inl (.inl (.inl p))

/-- **The sponge part** of a runtime of the hardwired ports and `t`: its sponge ports on its
register. -/
def hwPart (R : QuantumRuntime ((hwSpec X Z M).sum t)) : QuantumRuntime (spongeSpec X Z) where
  D := R.D
  init := R.init
  step p := R.step (.inl (.inl (.inl p)))

variable (X Z M) in
/-- The sponge ports as the hardwired ports. -/
def hwLens {L : LocalSig.{u, v}} :
    IPFunctor.Lens (QuantumComp.toIPFunctor L (spongeSpec X Z))
      (QuantumComp.toIPFunctor L ((hwSpec X Z M).sum t)) where
  toFunA _
    | .prim o => .prim o
    | .query p E ℓ => .query (.inl (.inl (.inl p))) E ℓ
  toFunB _ c := by cases c <;> exact id
  src_eq _ c _ := by cases c <;> rfl

variable (X Z M) in
/-- The sponge ports, single or in rounds, as the hardwired ports. -/
def hwParLens {L : LocalSig.{u, v}} :
    IPFunctor.Lens (QuantumComp.toIPFunctor L (parSpec (spongeSpec X Z) id))
      (QuantumComp.toIPFunctor L (parSpec ((hwSpec X Z M).sum t) (hwSpongePort X Z M t))) where
  toFunA _
    | .prim o => .prim o
    | .query (.inl p) E ℓ => .query (.inl (.inl (.inl (.inl p)))) E ℓ
    | .query (.inr (.round w f)) E ℓ => .query (.inr (.round w f)) E ℓ
  toFunB _ c := by
    rcases c with o | ⟨p | ⟨w, f⟩, E, ℓ⟩
    · exact id
    · exact id
    · exact id
  src_eq _ c _ := by
    rcases c with o | ⟨p | ⟨w, f⟩, E, ℓ⟩ <;> rfl

variable (R : QuantumRuntime ((hwSpec X Z M).sum t)) {L : LocalSig.{u, v}} (I : L.Interp)
  {W : QReg → Type*} {A : QReg}

/-- A lifted program runs as against the sponge part. -/
theorem run_mapLens_hwLens (z : QuantumComp L (spongeSpec X Z) W A) :
    R.run I (IFreeM.mapLens (hwLens X Z M t) z) = (hwPart t R).run I z := by
  induction z using QuantumComp.inductionOn with
  | pure _ y => exact (R.run_pure I y).trans ((hwPart t R).run_pure I y).symm
  | primBind _ o k ih => exact congrArg (((I o).frame R.D).bind) (funext ih)
  | queryBind _ i E ℓ k ih =>
    exact congrArg (DSubInstrument.bind ((hwPart t R).queryStep i E ℓ)) (funext ih)

/-- The rounds of the sponge part are the rounds of the sponge ports. -/
theorem roundStep_hwPart {w : ℕ} (f : Fin w → SpongePort) :
    (hwPart t R).roundStep f = R.roundStep fun i ↦ hwSpongePort X Z M t (f i) := by
  induction w with
  | zero => rfl
  | succ w ih =>
    rw [roundStep_succ, roundStep_succ, ih]
    rfl

/-- A call with the step `s` on the register `D`, as `QuantumRuntime.queryStep`. -/
noncomputable def stepCall (D : QReg) {I O : QReg} {ρ : Type}
    (s : SubInstrument (I × D) (O × D) ρ) (E : QReg) {A : QReg} (ℓ : A ≃ I × E) :
    SubInstrument (A × D) ((O × E) × D) ρ :=
  (SubInstrument.relabel (queryEquivIn ℓ D)).bind fun _ ↦ (s.frame E).bind fun r ↦
    (SubInstrument.relabel (queryEquivOut O D E)).bind fun _ ↦ SubInstrument.pure r

omit [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] in
theorem queryStep_eq_stepCall {spec : QuantumOracleSpec.{0, 0}} (R' : QuantumRuntime spec)
    (i : spec.Port) (E : QReg) {A : QReg} (ℓ : A ≃ spec.In i × E) :
    R'.queryStep i E ℓ = stepCall R'.D (R'.step i) E ℓ :=
  rfl

/-- The step of a round of a parallel runtime. -/
theorem par_step_round {spec : QuantumOracleSpec.{0, 0}} {Q : Type} (port : Q → spec.Port)
    (R' : QuantumRuntime spec) {w : ℕ} (f : Fin w → Q) :
    (R'.par port).step (.inr (.round w f)) = R'.roundStep fun i ↦ port (f i) :=
  rfl

/-- The round calls of the sponge part are the round calls of the sponge ports. -/
theorem queryStep_par_hwPart_round {w : ℕ} (f : Fin w → SpongePort) (E : QReg) {A : QReg}
    (ℓ : A ≃ roundIn (spongeSpec X Z) f × E) :
    ((hwPart t R).par id).queryStep (.inr (.round w f)) E ℓ =
      (R.par (hwSpongePort X Z M t)).queryStep (.inr (.round w f)) E ℓ := by
  have h1 := par_step_round id (hwPart t R) f
  have h2 := roundStep_hwPart t R (fun i ↦ id (f i))
  have h3 := par_step_round (hwSpongePort X Z M t) R f
  have h := h1.trans (h2.trans h3.symm)
  exact (queryStep_eq_stepCall ((hwPart t R).par id) (.inr (.round w f)) E ℓ).trans
    ((congrArg (fun s ↦ stepCall R.D s E ℓ) h).trans
      (queryStep_eq_stepCall (R.par (hwSpongePort X Z M t)) (.inr (.round w f)) E ℓ).symm)

/-- **A lifted parallel program runs as against the sponge part**, rounds included. -/
theorem run_mapLens_hwParLens (y : QuantumComp L (parSpec (spongeSpec X Z) id) W A) :
    (R.par (hwSpongePort X Z M t)).run I (IFreeM.mapLens (hwParLens X Z M t) y) =
      ((hwPart t R).par id).run I y := by
  induction y using QuantumComp.inductionOn with
  | pure _ y => exact ((R.par _).run_pure I y).trans (((hwPart t R).par id).run_pure I y).symm
  | primBind _ o k ih => exact congrArg (((I o).frame R.D).bind) (funext ih)
  | queryBind _ i E ℓ k ih =>
    rcases i with p | ⟨w, f⟩
    · exact congrArg (DSubInstrument.bind (((hwPart t R).par id).queryStep (.inl p) E ℓ))
        (funext ih)
    · exact (congrArg (fun S ↦ DSubInstrument.bind S fun r ↦
        (R.par (hwSpongePort X Z M t)).run I (IFreeM.mapLens (hwParLens X Z M t) (k r)))
        (queryStep_par_hwPart_round t R f E ℓ).symm).trans
        (congrArg (DSubInstrument.bind (((hwPart t R).par id).queryStep (.inr (.round w f)) E ℓ))
          (funext ih))

/-- `run_mapLens_hwLens` for fixed final registers. -/
theorem run₂_mapLens_hwLens {B : QReg} {α : Type} (z : QuantumComp₂ L (spongeSpec X Z) A B α) :
    R.run₂ I (IFreeM.mapLens (hwLens X Z M t) z) = (hwPart t R).run₂ I z :=
  congrArg (fun P ↦ DSubInstrument.comap (QuantumComp₂.leafEquiv B α)
    (QuantumComp₂.leafEquiv B α).injective P) (run_mapLens_hwLens t R I z)

/-- `run_mapLens_hwParLens` for fixed final registers. -/
theorem run₂_mapLens_hwParLens {B : QReg} {α : Type}
    (y : QuantumComp₂ L (parSpec (spongeSpec X Z) id) A B α) :
    (R.par (hwSpongePort X Z M t)).run₂ I (IFreeM.mapLens (hwParLens X Z M t) y) =
      ((hwPart t R).par id).run₂ I y :=
  congrArg (fun P ↦ DSubInstrument.comap (QuantumComp₂.leafEquiv B α)
    (QuantumComp₂.leafEquiv B α).injective P) (run_mapLens_hwParLens t R I y)

end part

/-! ## Programs with one path -/

section thin

variable {L : LocalSig.{u, v}} {spec : QuantumOracleSpec.{0, 0}} {N : spec.Port → Prop}

/-- A command with one response; a call only at a port in `N`. -/
def ThinCmd (N : spec.Port → Prop) {A : QReg} : QuantumComp.Cmd L spec A → Prop
  | .prim o => Nonempty (L.Outcome o) ∧ Subsingleton (L.Outcome o)
  | .query i _ _ => N i ∧ Nonempty (spec.Result i) ∧ Subsingleton (spec.Result i)

open Classical in
/-- Charge `0` on the commands of `ThinCmd N`, `1` on the others. -/
noncomputable def thinCharge (N : spec.Port → Prop) (A : QReg) (c : QuantumComp.Cmd L spec A) :
    ℕ :=
  if ThinCmd N c then 0 else 1

/-- **A program with one path**, calling only the ports in `N`. -/
def IsThin (N : spec.Port → Prop) {X : QReg → Type} {A : QReg} (x : QuantumComp L spec X A) :
    Prop :=
  IFreeM.IsChargeBound x (thinCharge N) 0

theorem thinCharge_eq_zero {A : QReg} {c : QuantumComp.Cmd L spec A} (h : ThinCmd N c) :
    thinCharge N A c = 0 := by
  unfold thinCharge
  simp [h]

theorem thinCmd_of_thinCharge {A : QReg} {c : QuantumComp.Cmd L spec A}
    (h : thinCharge N A c ≤ 0) : ThinCmd N c := by
  unfold thinCharge at h
  split_ifs at h with hc
  · exact hc
  · omega

variable {X Y : QReg → Type} {A : QReg}

theorem isThin_pure (x : X A) : IsThin N (QuantumComp.pure x : QuantumComp L spec X A) :=
  trivial

theorem isThin_primBind (o : L.Op A) {k : (b : L.Outcome o) → QuantumComp L spec X (L.next o b)}
    (ho : Nonempty (L.Outcome o) ∧ Subsingleton (L.Outcome o)) (hk : ∀ b, IsThin N (k b)) :
    IsThin N (QuantumComp.primBind o k) :=
  ⟨(thinCharge_eq_zero (N := N) (c := .prim o) ho).le, fun b ↦ (hk b.down).mono (Nat.zero_le _)⟩

theorem isThin_queryBind (i : spec.Port) (E : QReg) (ℓ : A ≃ spec.In i × E)
    {k : spec.Result i → QuantumComp L spec X (QReg.of (spec.Out i × E))}
    (hi : N i ∧ Nonempty (spec.Result i) ∧ Subsingleton (spec.Result i))
    (hk : ∀ r, IsThin N (k r)) : IsThin N (QuantumComp.queryBind i E ℓ k) :=
  ⟨(thinCharge_eq_zero (N := N) (c := .query i E ℓ) hi).le,
    fun r ↦ (hk r.down).mono (Nat.zero_le _)⟩

theorem IsThin.bind {x : QuantumComp L spec X A} {k : ∀ u, X u → QuantumComp L spec Y u}
    (hx : IsThin N x) (hk : ∀ u y, IsThin N (k u y)) : IsThin N (x.bind k) :=
  IFreeM.isChargeBound_bind (n₁ := 0) (n₂ := 0) hx hk

theorem IsThin.bind₂ {B C : QReg} {α β : Type} {x : QuantumComp₂ L spec A B α}
    {k : α → QuantumComp₂ L spec B C β} (hx : IsThin N x) (hk : ∀ a, IsThin N (k a)) :
    IsThin N (x.bind k) :=
  FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) hx hk

theorem IsThin.map {B : QReg} {α β : Type} {x : QuantumComp₂ L spec A B α} (hx : IsThin N x)
    (g : α → β) : IsThin N (x.map g) :=
  isChargeBound_map hx g

/-- A charge bound holds for every smaller charge. -/
theorem isChargeBound_of_charge_le {P : IPFunctor.Endo QReg} {c c' : (A : QReg) → P.A A → ℕ}
    (hc : ∀ A a, c' A a ≤ c A a) {X : QReg → Type} {A : QReg} {x : IFreeM P X A} {n : ℕ}
    (h : IFreeM.IsChargeBound x c n) : IFreeM.IsChargeBound x c' n := by
  induction x using IFreeM.inductionOn generalizing n with
  | pure _ _ => trivial
  | liftBind A a next ih =>
    exact ⟨(hc A a).trans h.1, fun b ↦ IFreeM.IsChargeBound.mono (ih b (h.2 b))
      (Nat.sub_le_sub_left (hc A a) n)⟩

/-- The thin charges of two commands, when the first is thin only if the second is. -/
theorem thinCharge_le_of {L' : LocalSig.{u, v}} {spec' : QuantumOracleSpec.{0, 0}}
    {N' : spec'.Port → Prop} {c : QuantumComp.Cmd L spec A} {c' : QuantumComp.Cmd L' spec' A}
    (h : ThinCmd N c → ThinCmd N' c') : thinCharge N' A c' ≤ thinCharge N A c := by
  unfold thinCharge
  split_ifs with h₁ h₂ h₂
  · exact le_rfl
  · exact Nat.zero_le 1
  · exact absurd (h h₂) h₁
  · exact le_rfl

theorem isThin_act {B : QReg} {α : Type} (p : SubInstrument A B α)
    (hα : Nonempty α ∧ Subsingleton α) :
    IsThin N (QComp.act (spec := spec) p) :=
  isThin_primBind (L := LocalSig.instruments.{0}) _ hα fun _ ↦ isThin_pure _

theorem isThin_isoGate {B : QReg} (f : A → B) (hf : Function.Injective f) :
    IsThin N (isoGate.{0} (spec := spec) f hf) :=
  isThin_primBind (L := LocalSig.instruments.{0}) _ ⟨⟨PUnit.unit⟩, inferInstance⟩
    fun _ ↦ isThin_pure _

theorem isThin_coGate {B : QReg} (f : B → A) (hf : Function.Injective f) :
    IsThin N (coGate.{0} (spec := spec) f hf) :=
  isThin_primBind (L := LocalSig.instruments.{0}) _ ⟨⟨PUnit.unit⟩, inferInstance⟩
    fun _ ↦ isThin_pure _

/-- **The calls of a round, in order, form one path.** -/
theorem isThin_seqCalls : ∀ {w : ℕ} (f : Fin w → spec.Port)
    (_hf : ∀ i, N (f i) ∧ Nonempty (spec.Result (f i)) ∧ Subsingleton (spec.Result (f i)))
    (E : QReg) {A B : QReg} (ℓ : A ≃ roundIn spec f × E) (post : roundOut spec f × E ≃ B),
    IsThin N (seqCalls f E ℓ post)
  | 0, f, _, E, _, _, ℓ, post => by
    rw [seqCalls_zero]
    exact isThin_act _ ⟨⟨finZeroElim⟩, ⟨fun _ _ ↦ funext fun i ↦ i.elim0⟩⟩
  | w + 1, f, hf, E, _, _, ℓ, post => by
    rw [seqCalls_succ]
    exact isThin_queryBind (L := LocalSig.instruments.{0}) _ _ _ (hf 0) fun r ↦
      (isThin_seqCalls (fun i ↦ f i.succ) (fun i ↦ hf i.succ) _ _ _).map _

variable (R : QuantumRuntime spec) (I : L.Interp)
  {W : ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞}

/-- **The weight of a program with one path, then a continuation**, for a weight vanishing on
the ports the path calls: the weight of the continuation from the path's leaf. -/
theorem exists_totalWeight_bind_of_isThin (hW : ∀ i, N i → ∀ σ, W i σ = 0)
    (x : QuantumComp L spec X A) (hx : IsThin N x) :
    ∃ p : Σ u, X u, ∀ {Y : QReg → Type} (k : ∀ u, X u → QuantumComp L spec Y u)
      (ρ : Matrix (A × R.D) (A × R.D) ℂ),
      R.totalWeight I W (x.bind k) ρ = R.totalWeight I W (k p.1 p.2) ((R.run I x).branch p ρ) := by
  induction x using QuantumComp.inductionOn with
  | pure _ y =>
    refine ⟨⟨_, y⟩, fun k ρ ↦ ?_⟩
    rw [QuantumComp.pure_bind, run_pure, DSubInstrument.branch_ret_self, LinearMap.id_apply]
  | primBind _ o k' ih =>
    obtain ⟨⟨b₀⟩, hs⟩ := thinCmd_of_thinCharge (N := N) (c := .prim o) hx.1
    have h2 : IFreeM.IsChargeBound (k' b₀) (thinCharge (L := L) N)
        (0 - thinCharge N _ (.prim o)) := hx.2 (ULift.up b₀)
    obtain ⟨p, hp⟩ := ih b₀ (h2.mono (Nat.sub_le 0 _))
    refine ⟨p, fun k ρ ↦ ?_⟩
    rw [QuantumComp.primBind_bind, totalWeight_primBind, run_primBind,
      DSubInstrument.branch_bind_apply, tsum_eq_single b₀ fun b hb ↦ absurd (hs.elim b b₀) hb,
      tsum_eq_single b₀ fun b hb ↦ absurd (hs.elim b b₀) hb, hp]
  | queryBind _ i E ℓ k' ih =>
    obtain ⟨hN, ⟨r₀⟩, hs⟩ := thinCmd_of_thinCharge (N := N) (c := .query i E ℓ) hx.1
    have h2 : IFreeM.IsChargeBound (k' r₀) (thinCharge (L := L) N)
        (0 - thinCharge N _ (.query i E ℓ)) := hx.2 (ULift.up r₀)
    obtain ⟨p, hp⟩ := ih r₀ (h2.mono (Nat.sub_le 0 _))
    refine ⟨p, fun k ρ ↦ ?_⟩
    rw [QuantumComp.queryBind_bind, totalWeight_queryBind, hW i hN, zero_add, run_queryBind,
      DSubInstrument.branch_bind_apply, tsum_eq_single r₀ fun r hr ↦ absurd (hs.elim r r₀) hr,
      tsum_eq_single r₀ fun r hr ↦ absurd (hs.elim r r₀) hr, hp]

end thin

/-! ## Commandwise equal runs -/

section engine

variable {spec : QuantumOracleSpec.{0, 0}} {Q : Type} (port : Q → spec.Port)
  (R : QuantumRuntime spec) {P : IPFunctor.Endo QReg}
  (σ₁ : IPFunctor.CommandSubstitution P (QuantumComp.toIPFunctor LocalSig.instruments.{0} spec))
  (σ₂ : IPFunctor.CommandSubstitution P
    (QuantumComp.toIPFunctor LocalSig.instruments.{0} (parSpec spec port)))

/-- **Commandwise equal runs give equal runs**: a substitution into the ports of `R` and one into
its parallel ports, whose commands run alike against `R` and `R.par port`. -/
theorem run_substitute_eq_par
    (h : ∀ A a, R.run .instruments (σ₁ A a) = (R.par port).run .instruments (σ₂ A a))
    {X : QReg → Type} {A : QReg} (y : IFreeM P X A) :
    R.run .instruments (y.substitute σ₁) = (R.par port).run .instruments (y.substitute σ₂) := by
  induction y using IFreeM.inductionOn with
  | pure _ x => exact (R.run_pure _ x).trans ((R.par port).run_pure _ x).symm
  | liftBind A a next ih =>
    rw [IFreeM.substitute_liftBind, IFreeM.substitute_liftBind]
    refine (R.run_bind _ (σ₁ A a) _).trans (Eq.trans ?_ ((R.par port).run_bind _ (σ₂ A a) _).symm)
    rw [h A a]
    refine congrArg _ (funext fun p ↦ ?_)
    obtain ⟨u, b, e⟩ := p
    subst e
    exact ih b

variable (W : ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞)

/-- **Commandwise equal weights give equal weights**, for every continuation: the weights against
`R` and, on the single calls, against `R.par port`. -/
theorem totalWeight_substitute_bind_eq_par
    (h : ∀ A a {Y : QReg → Type}
      (k₁ : ∀ u, {b : P.B A a // P.src A a b = u} →
        QuantumComp LocalSig.instruments.{0} spec Y u)
      (k₂ : ∀ u, {b : P.B A a // P.src A a b = u} →
        QuantumComp LocalSig.instruments.{0} (parSpec spec port) Y u),
      (∀ u b ρ, R.totalWeight .instruments W (k₁ u b) ρ =
        (R.par port).totalWeight .instruments (parWeight port W) (k₂ u b) ρ) →
      ∀ ρ, R.totalWeight .instruments W ((σ₁ A a).bind k₁) ρ =
        (R.par port).totalWeight .instruments (parWeight port W) ((σ₂ A a).bind k₂) ρ)
    {X Y : QReg → Type} {A : QReg} (y : IFreeM P X A)
    (k₁ : ∀ u, X u → QuantumComp LocalSig.instruments.{0} spec Y u)
    (k₂ : ∀ u, X u → QuantumComp LocalSig.instruments.{0} (parSpec spec port) Y u)
    (hk : ∀ u x ρ, R.totalWeight .instruments W (k₁ u x) ρ =
      (R.par port).totalWeight .instruments (parWeight port W) (k₂ u x) ρ)
    (ρ : Matrix (A × R.D) (A × R.D) ℂ) :
    R.totalWeight .instruments W ((y.substitute σ₁).bind k₁) ρ =
      (R.par port).totalWeight .instruments (parWeight port W) ((y.substitute σ₂).bind k₂) ρ := by
  induction y using IFreeM.inductionOn with
  | pure _ x => exact hk _ x ρ
  | liftBind A a next ih =>
    refine (congrArg (fun z ↦ R.totalWeight .instruments W z ρ)
      (IFreeM.bind_assoc (σ₁ A a) _ k₁)).trans (Eq.trans ?_ (congrArg
        (fun z ↦ (R.par port).totalWeight .instruments (parWeight port W) z ρ)
        (IFreeM.bind_assoc (σ₂ A a) _ k₂)).symm)
    refine h A a _ _ (fun u b ρ' ↦ ?_) ρ
    obtain ⟨b, e⟩ := b
    subst e
    exact ih b ρ'

/-- A program over the ports of `R`, as a program over its parallel ports: the same weights, for
continuations of the same weights. -/
theorem totalWeight_bind_liftOrdinary_par {X Y : QReg → Type} {A : QReg}
    (x : QuantumComp LocalSig.instruments.{0} spec X A)
    (k₁ : ∀ u, X u → QuantumComp LocalSig.instruments.{0} spec Y u)
    (k₂ : ∀ u, X u → QuantumComp LocalSig.instruments.{0} (parSpec spec port) Y u)
    (hk : ∀ u x ρ, R.totalWeight .instruments W (k₁ u x) ρ =
      (R.par port).totalWeight .instruments (parWeight port W) (k₂ u x) ρ)
    (ρ : Matrix (A × R.D) (A × R.D) ℂ) :
    R.totalWeight .instruments W (x.bind k₁) ρ =
      (R.par port).totalWeight .instruments (parWeight port W)
        ((x.liftOrdinary (t := roundSpec spec port)).bind k₂) ρ := by
  induction x using QuantumComp.inductionOn with
  | pure _ y => exact hk _ y ρ
  | primBind _ o k ih =>
    exact (R.totalWeight_primBind .instruments o _ ρ).trans ((tsum_congr fun b ↦ ih b _).trans
      ((R.par port).totalWeight_primBind .instruments (w := parWeight port W) o _ ρ).symm)
  | queryBind _ i E ℓ k ih =>
    exact (R.totalWeight_queryBind .instruments i E ℓ _ ρ).trans
      ((congrArg (W i (callInput ℓ R.D ρ) + ·) (tsum_congr fun r ↦ ih r _)).trans
        ((R.par port).totalWeight_queryBind .instruments (w := parWeight port W) (.inl i) E ℓ _
          ρ).symm)

/-- A program over the ports of `R` runs as a program over its parallel ports, before
continuations with the same runs. -/
theorem run_bind_liftOrdinary_par {X Y : QReg → Type} {A : QReg}
    (x : QuantumComp LocalSig.instruments.{0} spec X A)
    (k₁ : ∀ u, X u → QuantumComp LocalSig.instruments.{0} spec Y u)
    (k₂ : ∀ u, X u → QuantumComp LocalSig.instruments.{0} (parSpec spec port) Y u)
    (hk : ∀ u x, R.run .instruments (k₁ u x) = (R.par port).run .instruments (k₂ u x)) :
    R.run .instruments (x.bind k₁) =
      (R.par port).run .instruments ((x.liftOrdinary (t := roundSpec spec port)).bind k₂) := by
  rw [QuantumRuntime.run_bind, QuantumRuntime.run_bind]
  exact congrArg₂ DSubInstrument.bind (R.run_liftOrdinary .instruments _ x).symm
    (funext fun p ↦ hk p.1 p.2)

/-- **Two one-valued fixed-register programs with the same branch**, each returning one leaf: the
same runs. -/
theorem run_bind_leaf_eq_par {A B : QReg} {α₁ α₂ : Type} [Unique α₁] [Unique α₂]
    {Y : QReg → Type} (g : ∀ u, B = u → Y u)
    (x₁ : QuantumComp₂ LocalSig.instruments.{0} spec A B α₁)
    (x₂ : QuantumComp₂ LocalSig.instruments.{0} (parSpec spec port) A B α₂)
    (h : (R.run₂ .instruments x₁).branch default =
      ((R.par port).run₂ .instruments x₂).branch default) :
    R.run .instruments (QuantumComp.bind x₁ fun u l ↦ QuantumComp.pure (g u l.1.symm)) =
      (R.par port).run .instruments
        (QuantumComp.bind x₂ fun u l ↦ QuantumComp.pure (g u l.1.symm)) := by
  refine (R.run_bind .instruments x₁ _).trans (Eq.trans ?_
    ((R.par port).run_bind .instruments x₂ _).symm)
  refine DSubInstrument.ext (funext fun q ↦ LinearMap.ext fun ρ ↦ ?_)
  refine (DSubInstrument.branch_bind_apply _ _ q ρ).trans (Eq.trans ?_
    (DSubInstrument.branch_bind_apply ((R.par port).run .instruments x₂)
      (fun p ↦ (R.par port).run .instruments (QuantumComp.pure (g p.1 p.2.1.symm))) q ρ).symm)
  rw [← (QuantumComp₂.leafEquiv B α₁).tsum_eq, ← (QuantumComp₂.leafEquiv B α₂).tsum_eq,
    tsum_fintype, tsum_fintype, Fintype.sum_unique, Fintype.sum_unique, run_pure, run_pure]
  exact congrArg (fun T ↦ (DSubInstrument.ret (fun p : Σ u, Y u ↦ p.1 × R.D)
    (⟨B, g B rfl⟩ : Σ u, Y u)).branch q (T ρ)) h

/-- Sequencing programs with the same runs, against `R` and `R.par port`. -/
theorem run_bind_eq_par {X Y : QReg → Type} {A : QReg}
    {x₁ : QuantumComp LocalSig.instruments.{0} spec X A}
    {x₂ : QuantumComp LocalSig.instruments.{0} (parSpec spec port) X A}
    {k₁ : ∀ u, X u → QuantumComp LocalSig.instruments.{0} spec Y u}
    {k₂ : ∀ u, X u → QuantumComp LocalSig.instruments.{0} (parSpec spec port) Y u}
    (hx : R.run .instruments x₁ = (R.par port).run .instruments x₂)
    (hk : ∀ u y, R.run .instruments (k₁ u y) = (R.par port).run .instruments (k₂ u y)) :
    R.run .instruments (x₁.bind k₁) = (R.par port).run .instruments (x₂.bind k₂) := by
  rw [QuantumRuntime.run_bind, QuantumRuntime.run_bind, hx]
  exact congrArg _ (funext fun p ↦ hk p.1 p.2)

/-- **The weights of two one-path, one-valued programs with the same branch**, each returning one
leaf, then continuations of the same weights. -/
theorem totalWeight_bind_leaf_eq_par {N₁ : spec.Port → Prop}
    {N₂ : (parSpec spec port).Port → Prop} (hW₁ : ∀ i, N₁ i → ∀ σ, W i σ = 0)
    (hW₂ : ∀ i, N₂ i → ∀ σ, parWeight port W i σ = 0) {A B : QReg} {α₁ α₂ : Type} [Unique α₁]
    [Unique α₂] {Y Y' : QReg → Type} (g : ∀ u, B = u → Y u)
    (x₁ : QuantumComp₂ LocalSig.instruments.{0} spec A B α₁)
    (x₂ : QuantumComp₂ LocalSig.instruments.{0} (parSpec spec port) A B α₂)
    (hx₁ : IsThin N₁ x₁) (hx₂ : IsThin N₂ x₂)
    (h : (R.run₂ .instruments x₁).branch default =
      ((R.par port).run₂ .instruments x₂).branch default)
    (k₁ : ∀ u, Y u → QuantumComp LocalSig.instruments.{0} spec Y' u)
    (k₂ : ∀ u, Y u → QuantumComp LocalSig.instruments.{0} (parSpec spec port) Y' u)
    (hk : ∀ u y ρ, R.totalWeight .instruments W (k₁ u y) ρ =
      (R.par port).totalWeight .instruments (parWeight port W) (k₂ u y) ρ)
    (ρ : Matrix (A × R.D) (A × R.D) ℂ) :
    R.totalWeight .instruments W
        ((QuantumComp.bind x₁ fun u l ↦ QuantumComp.pure (g u l.1.symm)).bind k₁) ρ =
      (R.par port).totalWeight .instruments (parWeight port W)
        ((QuantumComp.bind x₂ fun u l ↦ QuantumComp.pure (g u l.1.symm)).bind k₂) ρ := by
  obtain ⟨p₁, hp₁⟩ := exists_totalWeight_bind_of_isThin R .instruments hW₁ x₁ hx₁
  obtain ⟨p₂, hp₂⟩ := exists_totalWeight_bind_of_isThin (R.par port) .instruments hW₂ x₂ hx₂
  refine (congrArg (fun z ↦ R.totalWeight .instruments W z ρ)
    (QuantumComp.bind_assoc x₁ _ k₁)).trans ((hp₁ _ ρ).trans (Eq.trans ?_ ((hp₂ _ ρ).symm.trans
      (congrArg (fun z ↦ (R.par port).totalWeight .instruments (parWeight port W) z ρ)
        (QuantumComp.bind_assoc x₂ _ k₂)).symm)))
  obtain ⟨u₁, e₁, a₁⟩ := p₁
  obtain ⟨u₂, e₂, a₂⟩ := p₂
  subst e₁ e₂
  obtain rfl := Subsingleton.elim a₁ default
  obtain rfl := Subsingleton.elim a₂ default
  exact (congrArg (R.totalWeight .instruments W (k₁ _ (g _ rfl))) (LinearMap.congr_fun h ρ)).trans
    (hk _ _ _)

end engine

/-! ## The simulation and the lifted programs have one path -/

section spongeThin

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]

/-- A call of a sponge port has one result. -/
theorem thinCmd_sponge (j : SpongePort) :
    (fun _ : SpongePort ↦ True) j ∧ Nonempty ((spongeSpec X Z).Result j) ∧
      Subsingleton ((spongeSpec X Z).Result j) :=
  ⟨trivial, ⟨()⟩, inferInstanceAs (Subsingleton Unit)⟩

variable (F : QReg)

theorem isThin_stateGate (e : Equiv.Perm (X × Z)) :
    IsThin (fun _ ↦ True) (stateGate.{0} F e) :=
  isThin_isoGate _ _

theorem isThin_sigmaK : IsThin (fun _ ↦ True) (sigmaK.{0} (X := X) (Z := Z) F) :=
  isThin_queryBind (L := LocalSig.instruments.{0}) _ _ _ (thinCmd_sponge .k)
    fun _ ↦ isThin_pure _

theorem isThin_sigmaK' : IsThin (fun _ ↦ True) (sigmaK'.{0} (X := X) (Z := Z) F) :=
  isThin_queryBind (L := LocalSig.instruments.{0}) _ _ _ (thinCmd_sponge .k')
    fun _ ↦ isThin_pure _

theorem isThin_omegaH : IsThin (fun _ ↦ True) (omegaH.{0} (X := X) (Z := Z) F) :=
  IsThin.bind₂ (isThin_queryBind (L := LocalSig.instruments.{0}) _ _ _ (thinCmd_sponge .h)
    fun _ ↦ isThin_pure _) fun _ ↦ isThin_isoGate _ _

variable [AddCommGroup X] [AddCommGroup Z]

theorem isThin_evalPort (π : Equiv.Perm (X × Z)) (p : PermutationPort) :
    IsThin (fun _ ↦ True) (evalPort.{0} F π p) := by
  cases p
  · exact (isThin_sigmaK F).bind₂ fun _ ↦ (isThin_stateGate F π).bind₂ fun _ ↦
      (isThin_sigmaK' F).bind₂ fun _ ↦ isThin_omegaH F
  · exact ((isThin_stateGate F _).bind₂ fun _ ↦ (isThin_omegaH F).bind₂ fun _ ↦
      isThin_stateGate F _).bind₂ fun _ ↦ ((isThin_stateGate F _).bind₂ fun _ ↦
      (isThin_sigmaK' F).bind₂ fun _ ↦ isThin_stateGate F _).bind₂ fun _ ↦
      (isThin_stateGate F _).bind₂ fun _ ↦ (isThin_stateGate F _).bind₂ fun _ ↦
      (isThin_sigmaK F).bind₂ fun _ ↦ isThin_stateGate F _

theorem isThin_simTree (π : Equiv.Perm (X × Z)) (p : PermutationPort) (E : QReg) {A : QReg}
    (ℓ : A ≃ (qrpmSpec (X × Z)).In p × E) :
    IsThin (fun _ ↦ True) (simTree.{0} π p E ℓ) :=
  IsThin.bind (((isThin_isoGate _ _).bind₂ fun _ ↦ (isThin_evalPort _ π p).bind₂ fun _ ↦
    (isThin_isoGate _ _).bind₂ fun _ ↦ isThin_evalPort _ π _).bind₂ fun _ ↦ isThin_coGate _ _)
    fun _ _ ↦ isThin_pure _

/-- **The simulation of a program with one path has one path.** -/
theorem isThin_simulate {L : LocalSig.{u, 0}} (I : L.Interp) (π : Equiv.Perm (X × Z))
    {W : QReg → Type} {A : QReg} {x : QuantumComp L (qrpmSpec (X × Z)) W A}
    (hx : IsThin (fun _ ↦ True) x) : IsThin (fun _ ↦ True) (simulate I π x) := by
  refine IFreeM.IsChargeBound.substitute (simSubst I π) (fun s a ↦ ?_) hx
  rcases a with o | ⟨p, E, ℓ⟩
  · exact ⟨thinCharge_le_of id, fun _ ↦ trivial⟩
  · exact IFreeM.IsChargeBound.mono (isThin_simTree π p E ℓ) (Nat.zero_le _)

variable {M : Type} (t : QuantumOracleSpec.{0, 0})

variable (X Z M) in
/-- The sponge ports among the hardwired ports and `t`. -/
def HwPorts (i : ((hwSpec X Z M).sum t).Port) : Prop :=
  ∃ p, i = hwSpongePort X Z M t p

variable (X Z M) in
/-- The single calls and the rounds of the sponge ports. -/
def HwParPorts (i : (parSpec ((hwSpec X Z M).sum t) (hwSpongePort X Z M t)).Port) : Prop :=
  (∃ p, i = .inl (hwSpongePort X Z M t p)) ∨ ∃ w f, i = .inr (.round w f)

omit [AddCommGroup X] [AddCommGroup Z] in
/-- **A lifted program with one path has one path**, calling only sponge ports. -/
theorem isThin_mapLens_hwLens {L : LocalSig.{u, v}} {W : QReg → Type} {A : QReg}
    {z : QuantumComp L (spongeSpec X Z) W A} (hz : IsThin (fun _ ↦ True) z) :
    IsThin (HwPorts X Z M t) (IFreeM.mapLens (hwLens X Z M t) z) :=
  IFreeM.IsChargeBound.mapLens (c := thinCharge (HwPorts X Z M t)) (hwLens X Z M t)
    (isChargeBound_of_charge_le (fun _ a ↦ thinCharge_le_of (by
      rcases a with o | ⟨p, E, ℓ⟩
      · exact id
      · exact fun h ↦ ⟨⟨p, rfl⟩, h.2⟩)) hz)

omit [AddCommGroup X] [AddCommGroup Z] in
/-- **A lifted parallel program with one path has one path**, calling only sponge ports, single
or in rounds. -/
theorem isThin_mapLens_hwParLens {L : LocalSig.{u, v}} {W : QReg → Type} {A : QReg}
    {y : QuantumComp L (parSpec (spongeSpec X Z) id) W A} (hy : IsThin (fun _ ↦ True) y) :
    IsThin (HwParPorts X Z M t) (IFreeM.mapLens (hwParLens X Z M t) y) :=
  IFreeM.IsChargeBound.mapLens (c := thinCharge (HwParPorts X Z M t)) (hwParLens X Z M t)
    (isChargeBound_of_charge_le (fun _ a ↦ thinCharge_le_of (by
      rcases a with o | ⟨p | ⟨w, f⟩, E, ℓ⟩
      · exact id
      · exact fun h ↦ ⟨.inl ⟨p, rfl⟩, h.2⟩
      · exact fun h ↦ ⟨.inr ⟨w, f, rfl⟩, h.2⟩)) hy)

omit [AddCommGroup X] [AddCommGroup Z] in
/-- A weight vanishing on the sponge ports vanishes on their single calls and rounds. -/
theorem parWeight_eq_zero_of {D : Type} [Fintype D]
    {W : ∀ i, Matrix (((hwSpec X Z M).sum t).In i × D) (((hwSpec X Z M).sum t).In i × D) ℂ →
      ℝ≥0∞}
    (hW : ∀ p σ, W (hwSpongePort X Z M t p) σ = 0) :
    ∀ i, HwParPorts X Z M t i → ∀ σ, parWeight (hwSpongePort X Z M t) W i σ = 0 := by
  rintro i (⟨p, rfl⟩ | ⟨w, f, rfl⟩) σ
  · exact hW p σ
  · rfl

omit [AddCommGroup X] [AddCommGroup Z] in
theorem eq_zero_of_hwPorts {D : Type} [Fintype D]
    {W : ∀ i, Matrix (((hwSpec X Z M).sum t).In i × D) (((hwSpec X Z M).sum t).In i × D) ℂ →
      ℝ≥0∞}
    (hW : ∀ p σ, W (hwSpongePort X Z M t p) σ = 0) :
    ∀ i, HwPorts X Z M t i → ∀ σ, W i σ = 0 := by
  rintro i ⟨p, rfl⟩ σ
  exact hW p σ

end spongeThin

/-! ## Lenses and sequencing -/

section lens

variable {L : LocalSig.{u, v}} {spec spec' : QuantumOracleSpec.{0, 0}}
  (l : IPFunctor.Lens (QuantumComp.toIPFunctor L spec) (QuantumComp.toIPFunctor L spec'))

theorem mapLens_bindQ {X Y : QReg → Type} {A : QReg} (x : QuantumComp L spec X A)
    (k : ∀ u, X u → QuantumComp L spec Y u) :
    IFreeM.mapLens l (x.bind k) = (IFreeM.mapLens l x).bind fun u a ↦ IFreeM.mapLens l (k u a) := by
  have h := IFreeM.substitute_bind l.toSubstitution (x : IFreeM _ X A) k
  simp only [IFreeM.substitute_toSubstitution] at h
  exact h

theorem mapLens_bindQ₂ {A B C : QReg} {α β : Type} (x : QuantumComp₂ L spec A B α)
    (k : α → QuantumComp₂ L spec B C β) :
    IFreeM.mapLens l (x.bind k) =
      QuantumComp₂.bind (IFreeM.mapLens l x) fun a ↦ IFreeM.mapLens l (k a) := by
  refine (mapLens_bindQ l x _).trans ?_
  congr 1
  funext u p
  rcases p with ⟨rfl, a⟩
  rfl

theorem mapLens_map₂ {A B : QReg} {α β : Type} (x : QuantumComp₂ L spec A B α) (g : α → β) :
    IFreeM.mapLens l (x.map g) = QuantumComp₂.map g (IFreeM.mapLens l x) := by
  rw [QuantumComp₂.map_eq_bind_pure]
  exact (mapLens_bindQ₂ l x _).trans (QuantumComp₂.map_eq_bind_pure g _).symm

end lens

/-! ## The lockstep round with rounds: one path, and its charges -/

section lockR

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] {w : ℕ} {E : QReg}

theorem isThin_gateAll (g : Fin w → Equiv.Perm (SlotT X Z)) :
    IsThin (fun _ ↦ True) (gateAll (E := E) g) :=
  isThin_isoGate _ _

theorem isThin_subRound (p : SpongePort) (e : (X × Z) ≃ spongeIn X Z p) (P : Fin w → Prop)
    [DecidablePred P] : IsThin (fun _ ↦ True) (subRound (E := E) p e P) :=
  isThin_queryBind (L := LocalSig.instruments.{0}) _ _ _
    ⟨trivial, ⟨fun _ ↦ ()⟩, inferInstanceAs (Subsingleton (Fin _ → Unit))⟩
    fun _ ↦ isThin_isoGate _ _

variable (κ : (lockSpecR X Z).Port → ℕ)

/-- The charge of a round of port `p` on the slots in `P`. -/
def subCharge (p : SpongePort) (P : Fin w → Prop) [DecidablePred P] : ℕ :=
  κ (.inr (.round (Fintype.card {i // P i}) fun _ ↦ p))

/-- The charge of the lockstep round: its two rounds of `h` on all slots, and its four rounds of
`k` and four of `k'`, two on the forward and two on the inverse slots each. -/
def lockCharge (dir : Fin w → PermutationPort) : ℕ :=
  2 * subCharge κ .h (fun _ : Fin w ↦ True) + 2 * subCharge κ .k (fun i ↦ dir i = .forward) +
    2 * subCharge κ .k (fun i ↦ dir i = .inverse) +
    2 * subCharge κ .k' (fun i ↦ dir i = .forward) +
    2 * subCharge κ .k' (fun i ↦ dir i = .inverse)

theorem isChargeBound_gateAll (g : Fin w → Equiv.Perm (SlotT X Z)) :
    IFreeM.IsChargeBound (gateAll (E := E) g) (callCharge κ) 0 :=
  ⟨le_rfl, fun _ ↦ trivial⟩

theorem isChargeBound_subRound (p : SpongePort) (e : (X × Z) ≃ spongeIn X Z p)
    (P : Fin w → Prop) [DecidablePred P] :
    IFreeM.IsChargeBound (subRound (E := E) p e P) (callCharge κ) (subCharge κ p P) :=
  ⟨le_rfl, fun _ ↦ ⟨Nat.zero_le _, fun _ ↦ trivial⟩⟩

omit [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] in
theorem card_subtype_true [Fintype (Subtype fun _ : Fin w ↦ True)] :
    Fintype.card (Subtype fun _ : Fin w ↦ True) = w :=
  (Fintype.card_congr (Equiv.subtypeUnivEquiv fun _ ↦ trivial)).trans (Fintype.card_fin w)

omit [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] in
theorem card_forward_add_card_inverse (dir : Fin w → PermutationPort) :
    Fintype.card {i // dir i = .forward} + Fintype.card {i // dir i = .inverse} = w := by
  have h : Fintype.card {i // dir i = .inverse} = Fintype.card {i // ¬ dir i = .forward} :=
    Fintype.card_congr (Equiv.subtypeEquivRight fun i ↦ by cases dir i <;> simp)
  rw [h, Fintype.card_subtype_compl, Fintype.card_fin]
  have := Fintype.card_subtype_le (fun i : Fin w ↦ dir i = .forward)
  rw [Fintype.card_fin] at this
  omega

/-- **The width charges of the lockstep round**: `2 w` calls of each port. -/
theorem lockCharge_le_width {c : SpongePort → ℕ}
    (hκ : ∀ m p, κ (.inr (.round m fun _ ↦ p)) ≤ m * c p) (dir : Fin w → PermutationPort) :
    lockCharge κ dir ≤ (2 * c .h + 2 * c .k + 2 * c .k') * w := by
  have hle : ∀ (P : Fin w → Prop) [DecidablePred P] p,
      subCharge κ p P ≤ Fintype.card {i // P i} * c p := fun _ _ p ↦ hκ _ p
  have h1 := hle (fun _ ↦ True) .h
  rw [card_subtype_true] at h1
  have h2 := hle (fun i ↦ dir i = .forward) .k
  have h3 := hle (fun i ↦ dir i = .inverse) .k
  have h4 := hle (fun i ↦ dir i = .forward) .k'
  have h5 := hle (fun i ↦ dir i = .inverse) .k'
  have hFI := card_forward_add_card_inverse dir
  generalize Fintype.card {i // dir i = .forward} = a at h2 h4 hFI
  generalize Fintype.card {i // dir i = .inverse} = b at h3 h5 hFI
  have e : (2 * c .h + 2 * c .k + 2 * c .k') * w = 2 * (w * c .h) + 2 * (a * c .k) +
      2 * (b * c .k) + 2 * (a * c .k') + 2 * (b * c .k') := by
    rw [← hFI]
    ring
  unfold lockCharge
  omega

/-- **The depth charges of the lockstep round**: at most two rounds of `h` and four of each of `k`,
`k'`, none when the round is empty. -/
theorem lockCharge_le_depth {c : SpongePort → ℕ}
    (hκ : ∀ m p, κ (.inr (.round m fun _ ↦ p)) ≤ min 1 m * c p) (dir : Fin w → PermutationPort) :
    lockCharge κ dir ≤ (2 * c .h + 4 * c .k + 4 * c .k') * min 1 w := by
  have hle : ∀ (P : Fin w → Prop) [DecidablePred P] p, subCharge κ p P ≤ min 1 w * c p :=
    fun P _ p ↦ (hκ _ p).trans (Nat.mul_le_mul_right _ (min_le_min_left 1
      ((Fintype.card_subtype_le P).trans (Fintype.card_fin w).le)))
  have h1 := hle (fun _ ↦ True) .h
  have h2 := hle (fun i ↦ dir i = .forward) .k
  have h3 := hle (fun i ↦ dir i = .inverse) .k
  have h4 := hle (fun i ↦ dir i = .forward) .k'
  have h5 := hle (fun i ↦ dir i = .inverse) .k'
  unfold lockCharge
  calc _ ≤ 2 * (min 1 w * c .h) + 2 * (min 1 w * c .k) + 2 * (min 1 w * c .k) +
        2 * (min 1 w * c .k') + 2 * (min 1 w * c .k') := by omega
    _ = (2 * c .h + 4 * c .k + 4 * c .k') * min 1 w := by ring

variable [AddCommGroup X] [AddCommGroup Z]

/-- **The lockstep round has one path.** -/
theorem isThin_lockRoundR (π : Equiv.Perm (X × Z)) (dir : Fin w → PermutationPort) {A B : QReg}
    (ℓ : A ≃ roundIn (qrpmSpec (X × Z)) dir × E) (post : roundOut (qrpmSpec (X × Z)) dir × E ≃ B) :
    IsThin (fun _ ↦ True) (lockRoundR π dir ℓ post) := by
  unfold lockRoundR
  refine IsThin.bind₂ ?_ fun _ ↦ isThin_coGate _ _
  refine (isThin_isoGate _ _).bind₂ fun _ ↦ (isThin_subRound _ _ _).bind₂ fun _ ↦
    (isThin_gateAll _).bind₂ fun _ ↦ (isThin_subRound _ _ _).bind₂ fun _ ↦
    (isThin_subRound _ _ _).bind₂ fun _ ↦ (isThin_gateAll _).bind₂ fun _ ↦
    (isThin_subRound _ _ _).bind₂ fun _ ↦ (isThin_gateAll _).bind₂ fun _ ↦
    (isThin_subRound _ _ _).bind₂ fun _ ↦ (isThin_gateAll _).bind₂ fun _ ↦
    (isThin_subRound _ _ _).bind₂ fun _ ↦ (isThin_gateAll _).bind₂ fun _ ↦
    (isThin_subRound _ _ _).bind₂ fun _ ↦ (isThin_subRound _ _ _).bind₂ fun _ ↦
    (isThin_gateAll _).bind₂ fun _ ↦ (isThin_subRound _ _ _).bind₂ fun _ ↦
    (isThin_gateAll _).bind₂ fun _ ↦ (isThin_subRound _ _ _).bind₂ fun _ ↦ isThin_gateAll _

/-- **The charges of the lockstep round.** -/
theorem isChargeBound_lockRoundR (π : Equiv.Perm (X × Z)) (dir : Fin w → PermutationPort)
    {A B : QReg} (ℓ : A ≃ roundIn (qrpmSpec (X × Z)) dir × E)
    (post : roundOut (qrpmSpec (X × Z)) dir × E ≃ B) :
    IFreeM.IsChargeBound (lockRoundR π dir ℓ post) (callCharge κ) (lockCharge κ dir) := by
  unfold lockRoundR
  have h0 : ∀ {A' B' : QReg} (f : A' → B') (hf : Function.Injective f),
      IFreeM.IsChargeBound (isoGate.{0} (spec := lockSpecR X Z) f hf) (callCharge κ) 0 :=
    fun _ _ ↦ ⟨le_rfl, fun _ ↦ trivial⟩
  have h0' : ∀ {A' B' : QReg} (f : B' → A') (hf : Function.Injective f),
      IFreeM.IsChargeBound (coGate.{0} (spec := lockSpecR X Z) f hf) (callCharge κ) 0 :=
    fun _ _ ↦ ⟨le_rfl, fun _ ↦ trivial⟩
  refine IFreeM.IsChargeBound.mono (FreeM₂.isChargeBound_bind (n₁ := ?n) (n₂ := 0) ?hx
    fun _ ↦ h0' _ _) ?hle
  case hx =>
    exact FreeM₂.isChargeBound_bind (h0 _ _) fun _ ↦
      FreeM₂.isChargeBound_bind
        (isChargeBound_subRound κ .k (Equiv.refl _) (fun i ↦ dir i = .forward))
        fun _ ↦
      FreeM₂.isChargeBound_bind (isChargeBound_gateAll κ _) fun _ ↦
      FreeM₂.isChargeBound_bind
        (isChargeBound_subRound κ .k' (Equiv.refl _) (fun i ↦ dir i = .forward))
        fun _ ↦
      FreeM₂.isChargeBound_bind (isChargeBound_subRound κ .h (Equiv.prodComm X Z) (fun _ ↦ True))
        fun _ ↦
      FreeM₂.isChargeBound_bind (isChargeBound_gateAll κ _) fun _ ↦
      FreeM₂.isChargeBound_bind
        (isChargeBound_subRound κ .k' (Equiv.refl _) (fun i ↦ dir i = .inverse))
        fun _ ↦
      FreeM₂.isChargeBound_bind (isChargeBound_gateAll κ _) fun _ ↦
      FreeM₂.isChargeBound_bind
        (isChargeBound_subRound κ .k (Equiv.refl _) (fun i ↦ dir i = .inverse))
        fun _ ↦
      FreeM₂.isChargeBound_bind (isChargeBound_gateAll κ _) fun _ ↦
      FreeM₂.isChargeBound_bind
        (isChargeBound_subRound κ .k (Equiv.refl _) (fun i ↦ dir i = .inverse))
        fun _ ↦
      FreeM₂.isChargeBound_bind (isChargeBound_gateAll κ _) fun _ ↦
      FreeM₂.isChargeBound_bind
        (isChargeBound_subRound κ .k' (Equiv.refl _) (fun i ↦ dir i = .inverse))
        fun _ ↦
      FreeM₂.isChargeBound_bind (isChargeBound_subRound κ .h (Equiv.prodComm X Z) (fun _ ↦ True))
        fun _ ↦
      FreeM₂.isChargeBound_bind (isChargeBound_gateAll κ _) fun _ ↦
      FreeM₂.isChargeBound_bind
        (isChargeBound_subRound κ .k' (Equiv.refl _) (fun i ↦ dir i = .forward))
        fun _ ↦
      FreeM₂.isChargeBound_bind (isChargeBound_gateAll κ _) fun _ ↦
      FreeM₂.isChargeBound_bind
        (isChargeBound_subRound κ .k (Equiv.refl _) (fun i ↦ dir i = .forward))
        fun _ ↦
      isChargeBound_gateAll κ _
  case hle =>
    unfold lockCharge
    omega

end lockR

/-! ## Charges along lenses and minima -/

section charges

variable {X Z M : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  (t : QuantumOracleSpec.{0, 0})

variable (X Z M) in
/-- The ports of the sponge lockstep as the hardwired ports with rounds. -/
def hwParPort : (parSpec (spongeSpec X Z) id).Port →
    (parSpec ((hwSpec X Z M).sum t) (hwSpongePort X Z M t)).Port
  | .inl p => .inl (hwSpongePort X Z M t p)
  | .inr r => .inr r

/-- **Charges of a lifted parallel program**: the charges of its ports. -/
theorem isChargeBound_mapLens_hwParLens {L : LocalSig.{u, v}} {W : QReg → Type} {A : QReg}
    (κ : (parSpec ((hwSpec X Z M).sum t) (hwSpongePort X Z M t)).Port → ℕ)
    {y : QuantumComp L (parSpec (spongeSpec X Z) id) W A} {n : ℕ}
    (hy : IFreeM.IsChargeBound y (callCharge fun i ↦ κ (hwParPort X Z M t i)) n) :
    IFreeM.IsChargeBound (IFreeM.mapLens (hwParLens X Z M t) y) (callCharge κ) n :=
  IFreeM.IsChargeBound.mapLens (c := callCharge κ) (hwParLens X Z M t)
    (isChargeBound_of_charge_le (fun _ a ↦ by
      rcases a with o | ⟨p | ⟨w, f⟩, E, ℓ⟩ <;> exact le_rfl) hy)

omit [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] in
/-- **Two budgets give their minimum** for a charge below both charges. -/
theorem isChargeBound_min_of_le {P : IPFunctor.Endo QReg} {c c₁ c₂ : (A : QReg) → P.A A → ℕ}
    (hc : ∀ A a, c A a ≤ c₁ A a ∧ c A a ≤ c₂ A a) {Y : QReg → Type} {A : QReg}
    {x : IFreeM P Y A} {n₁ n₂ : ℕ} (h₁ : IFreeM.IsChargeBound x c₁ n₁)
    (h₂ : IFreeM.IsChargeBound x c₂ n₂) : IFreeM.IsChargeBound x c (min n₁ n₂) := by
  induction x using IFreeM.inductionOn generalizing n₁ n₂ with
  | pure _ _ => trivial
  | liftBind A a next ih =>
    obtain ⟨hc₁, hc₂⟩ := hc A a
    have e₁ := h₁.1
    have e₂ := h₂.1
    refine ⟨le_min (hc₁.trans e₁) (hc₂.trans e₂), fun b ↦ ?_⟩
    refine IFreeM.IsChargeBound.mono (ih b (h₁.2 b) (h₂.2 b)) ?_
    change min (n₁ - c₁ A a) (n₂ - c₂ A a) ≤ min n₁ n₂ - c A a
    omega

omit [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] in
/-- A budget of `0` for a charge holds for every charge vanishing where it vanishes. -/
theorem isChargeBound_zero_of {P : IPFunctor.Endo QReg} {c c' : (A : QReg) → P.A A → ℕ}
    (hc : ∀ A a, c A a = 0 → c' A a = 0) {Y : QReg → Type} {A : QReg} {x : IFreeM P Y A}
    (h : IFreeM.IsChargeBound x c 0) : IFreeM.IsChargeBound x c' 0 := by
  induction x using IFreeM.inductionOn with
  | pure _ _ => trivial
  | liftBind A a next ih =>
    have h0 : c A a = 0 := Nat.le_zero.mp h.1
    refine ⟨(hc A a h0).le, fun b ↦ ?_⟩
    have h2 : IFreeM.IsChargeBound (next b) c (0 - c A a) := h.2 b
    exact IFreeM.IsChargeBound.mono (ih b (h2.mono (Nat.zero_sub _).le)) (Nat.zero_le _)

end charges

/-! ## The engine for fixed final registers -/

section engine₂

variable {spec : QuantumOracleSpec.{0, 0}} {Q : Type} (port : Q → spec.Port)
  (R : QuantumRuntime spec) {A B C : QReg} {α β : Type}

theorem run_bind₂_eq_par {x₁ : QComp spec A B α} {x₂ : QComp (parSpec spec port) A B α}
    {k₁ : α → QComp spec B C β} {k₂ : α → QComp (parSpec spec port) B C β}
    (hx : R.run .instruments x₁ = (R.par port).run .instruments x₂)
    (hk : ∀ a, R.run .instruments (k₁ a) = (R.par port).run .instruments (k₂ a)) :
    R.run .instruments (x₁.bind k₁) = (R.par port).run .instruments (x₂.bind k₂) :=
  run_bind_eq_par port R hx fun u p ↦ by
    rcases p with ⟨rfl, a⟩
    exact hk a

theorem run_bind₂_liftOrdinary_par (x : QComp spec A B α) {k₁ : α → QComp spec B C β}
    {k₂ : α → QComp (parSpec spec port) B C β}
    (hk : ∀ a, R.run .instruments (k₁ a) = (R.par port).run .instruments (k₂ a)) :
    R.run .instruments (x.bind k₁) = (R.par port).run .instruments
      (QuantumComp₂.bind (QuantumComp.liftOrdinary (t := roundSpec spec port) x) k₂) :=
  run_bind_liftOrdinary_par port R x _ _ fun u p ↦ by
    rcases p with ⟨rfl, a⟩
    exact hk a

variable (W : ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞)

theorem totalWeight_bind₂_liftOrdinary_par (x : QComp spec A B α) {k₁ : α → QComp spec B C β}
    {k₂ : α → QComp (parSpec spec port) B C β}
    (hk : ∀ a ρ, R.totalWeight .instruments W (k₁ a) ρ =
      (R.par port).totalWeight .instruments (parWeight port W) (k₂ a) ρ)
    (ρ : Matrix (A × R.D) (A × R.D) ℂ) :
    R.totalWeight .instruments W (x.bind k₁) ρ = (R.par port).totalWeight .instruments
      (parWeight port W)
      (QuantumComp₂.bind (QuantumComp.liftOrdinary (t := roundSpec spec port) x) k₂) ρ :=
  totalWeight_bind_liftOrdinary_par port R W x _ _ (fun u p ρ' ↦ by
    rcases p with ⟨rfl, a⟩
    exact hk a ρ') ρ

/-- A program over the ports of `R`, as a program over its parallel ports: the same weights. -/
theorem totalWeight_liftOrdinary_par {X : QReg → Type}
    (x : QuantumComp LocalSig.instruments.{0} spec X A) (ρ : Matrix (A × R.D) (A × R.D) ℂ) :
    (R.par port).totalWeight .instruments (parWeight port W)
      (QuantumComp.liftOrdinary (t := roundSpec spec port) x) ρ =
        R.totalWeight .instruments W x ρ :=
  R.totalWeight_liftOrdinary .instruments _ W _ (fun _ _ ↦ rfl) x ρ

/-- Equal runs against `R` and `R.par port` observe the same distributions. -/
theorem evalDistMap_par_eq {X : QReg → Type} {x : QuantumComp LocalSig.instruments.{0} spec X A}
    {y : QuantumComp LocalSig.instruments.{0} (parSpec spec port) X A}
    (h : R.run .instruments x = (R.par port).run .instruments y) {γ : Type*} [MeasurableSpace γ]
    (ρ : SubState A) (f : (Σ u, X u) → γ) :
    R.evalDistMap .instruments x ρ f = (R.par port).evalDistMap .instruments y ρ f := by
  unfold QuantumRuntime.evalDistMap QuantumRuntime.jointPost
  rw [h]
  rfl

/-- Equal runs against `R` and `R.par port` have the same event weights. -/
theorem eventWeight_par_eq {X : QReg → Type} {x : QuantumComp LocalSig.instruments.{0} spec X A}
    {y : QuantumComp LocalSig.instruments.{0} (parSpec spec port) X A}
    (h : R.run .instruments x = (R.par port).run .instruments y) (P : Matrix R.D R.D ℂ)
    (ρ : Matrix (A × R.D) (A × R.D) ℂ) :
    R.eventWeight .instruments P x ρ = (R.par port).eventWeight .instruments P y ρ := by
  unfold QuantumRuntime.eventWeight
  rw [h]
  rfl

end engine₂

end Quantum.Par

end
