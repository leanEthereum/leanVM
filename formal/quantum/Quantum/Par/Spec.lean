module

public import VCVio.Quantum.Comp.Subsystem
public import VCVio.Quantum.Oracle.Emulated

@[expose] public section

/-!
# Parallel queries: rounds of calls on disjoint registers

A *round* of width `w` calls the ports `f 0, …, f (w-1)` of a signature at once, on the
components of the register `Π i, In (f i)`. Following the parallel-query model of Zalka and of
Chung, Fehr, Huang and Liao, its meaning is the `w` calls in order, with no other operation in
between: for a fixed function the calls are basis maps on disjoint registers and commute.

* `seqCalls f E ℓ post`: the program of the `w` calls on the components of the exposed
  register, the remainder `E` carried through every call, then one relabelling to `B`.
* `QuantumRuntime.roundStep R f`: the subinstrument of a round on `Π i, In (f i)` and the
  runtime register, the steps of the components framed one after the other.
* `run₂_seqCalls`: **exactness** of the round: running the `w` calls is the round step framed
  by the remainder.
* `parSpec spec port`: the signature with the single ports of `spec` and a round port for every
  tuple of ports named by `port : Q → spec.Port`; `QuantumRuntime.par R` answers rounds by
  `roundStep`.
* `parToSeq`: the substitution of each round by its calls; `run_substitute_parToSeq`: a
  parallel program against `R.par` runs as its serialization against `R`.
* `widthCharge port c`, `roundCharge port c`: the calls a command makes, counted by `c`, and
  whether it makes any; `isChargeBound_substitute_parToSeq` transports width budgets to the
  serialization, and `totalWeight_substitute_parToSeq` transports summed weights that vanish on
  the ports of rounds.
-/

open IPFunctor Quantum Quantum.SubInstrument
open scoped ENNReal ComplexOrder Kronecker

universe u v w w₁ u₁ v₁

namespace Quantum.Par

/-! ## Relabelling and framing -/

section frame

variable {S T U V : Type*} [Fintype S] [Fintype T] [Fintype U] [Fintype V] [DecidableEq S]
  [DecidableEq T] [DecidableEq U] [DecidableEq V] {α : Type*}

omit [DecidableEq V] in
/-- Relabelling twice before a continuation is relabelling along the composite. -/
theorem relabel_bind_relabel_bind (e : S ≃ T) (e' : T ≃ U) (k : Unit → SubInstrument U V α) :
    ((relabel e).bind fun _ ↦ (relabel e').bind k) = (relabel (e.trans e')).bind k := by
  rw [← SubInstrument.bind_assoc, relabel_bind_relabel]

variable {F G : Type*} [Fintype F] [Fintype G] [DecidableEq F] [DecidableEq G]

omit [Fintype S] [Fintype V] [DecidableEq S] [DecidableEq V] in
/-- Framing twice is framing once by the product, up to reassociation. -/
theorem frame_frame (p : SubInstrument T U α) :
    (p.frame F).frame G = (relabel (Equiv.prodAssoc T F G)).bind fun _ ↦
      (p.frame (F × G)).bind fun r ↦
        (relabel (Equiv.prodAssoc U F G).symm).bind fun _ ↦ SubInstrument.pure r :=
  DSubInstrument.ext <| funext fun r ↦ LinearMap.ext fun ρ ↦ by
    rw [DSubInstrument.branch_bind_unit, DSubInstrument.branch_bind_bind_unit_ret]
    ext x y
    simp only [LinearMap.comp_apply, relabel_branch_apply, DSubInstrument.branch_frame_apply,
      MatrixMap.amplify_amplify_apply, Matrix.submatrix_apply]
    rfl

end frame

/-! ## Rounds -/

variable (spec : QuantumOracleSpec.{u₁, v₁})

/-- The register of the inputs of a round: the input registers of its ports, side by side. -/
abbrev roundIn {w : ℕ} (f : Fin w → spec.Port) : QReg :=
  QReg.of (∀ i, spec.In (f i))

/-- The register of the outputs of a round. -/
abbrev roundOut {w : ℕ} (f : Fin w → spec.Port) : QReg :=
  QReg.of (∀ i, spec.Out (f i))

/-- The classical result of a round: the results of its calls. -/
abbrev RoundResult {w : ℕ} (f : Fin w → spec.Port) : Type v₁ :=
  ∀ i, spec.Result (f i)

variable {spec}

/-- A round of width zero leaves nothing to call. -/
def roundZeroEquiv (f : Fin 0 → spec.Port) : roundIn spec f ≃ roundOut spec f where
  toFun _ := finZeroElim
  invFun _ := finZeroElim
  left_inv _ := funext finZeroElim
  right_inv _ := funext finZeroElim

/-- Before the first call of a round: expose the input of `f 0`, the other inputs and the
remainder beside it. -/
def seqSplitIn {w : ℕ} (f : Fin (w + 1) → spec.Port) (E : QReg) {A : QReg}
    (ℓ : A ≃ roundIn spec f × E) :
    A ≃ spec.In (f 0) × QReg.of (roundIn spec (fun i ↦ f i.succ) × E) :=
  ℓ.trans (((Fin.consEquiv fun i ↦ (spec.In (f i) : Type)).symm.prodCongr
    (Equiv.refl E)).trans (Equiv.prodAssoc _ _ _))

/-- After the first call of a round: the other inputs, with the output of `f 0` moved into
the remainder. -/
def seqShift {w : ℕ} (f : Fin (w + 1) → spec.Port) (E : QReg) :
    QReg.of (spec.Out (f 0) × QReg.of (roundIn spec (fun i ↦ f i.succ) × E)) ≃
      roundIn spec (fun i ↦ f i.succ) × QReg.of (spec.Out (f 0) × E) :=
  (Equiv.prodAssoc _ _ _).symm.trans
    (((Equiv.prodComm _ _).prodCongr (Equiv.refl E)).trans (Equiv.prodAssoc _ _ _))

/-- At the end of a round: put the output of `f 0` back in front of the other outputs. -/
def seqPost {w : ℕ} (f : Fin (w + 1) → spec.Port) (E : QReg) {B : QReg}
    (post : roundOut spec f × E ≃ B) :
    roundOut spec (fun i ↦ f i.succ) × QReg.of (spec.Out (f 0) × E) ≃ B :=
  (Equiv.prodAssoc _ _ _).symm.trans (((Equiv.prodComm _ _).prodCongr (Equiv.refl E)).trans
    (((Fin.consEquiv fun i ↦ (spec.Out (f i) : Type)).prodCongr (Equiv.refl E)).trans post))

/-- **The calls of a round, in order.** Call `f 0`, …, `f (w-1)` on the components of the
register that `ℓ` exposes, the remainder `E` carried through every call, and relabel the outputs
and the remainder along `post` at the end. Returns the results of the calls. -/
noncomputable def seqCalls {w : ℕ} (f : Fin w → spec.Port) (E : QReg) {A B : QReg}
    (ℓ : A ≃ roundIn spec f × E) (post : roundOut spec f × E ≃ B) :
    QComp spec A B (RoundResult spec f) :=
  match w, f, ℓ, post with
  | 0, f, ℓ, post =>
    QComp.act ((relabel (ℓ.trans (((roundZeroEquiv f).prodCongr (Equiv.refl E)).trans
      post))).map fun _ ↦ (finZeroElim : RoundResult spec f))
  | _ + 1, f, ℓ, post =>
    QuantumComp₂.queryBind (f 0) (QReg.of (roundIn spec (fun i ↦ f i.succ) × E))
      (seqSplitIn f E ℓ) fun r ↦
        (seqCalls (fun i ↦ f i.succ) (QReg.of (spec.Out (f 0) × E)) (seqShift f E)
          (seqPost f E post)).map (Fin.cons r)

theorem seqCalls_zero (f : Fin 0 → spec.Port) (E : QReg) {A B : QReg}
    (ℓ : A ≃ roundIn spec f × E) (post : roundOut spec f × E ≃ B) :
    seqCalls f E ℓ post =
      QComp.act ((relabel (ℓ.trans (((roundZeroEquiv f).prodCongr (Equiv.refl E)).trans
        post))).map fun _ ↦ (finZeroElim : RoundResult spec f)) :=
  rfl

theorem seqCalls_succ {w : ℕ} (f : Fin (w + 1) → spec.Port) (E : QReg) {A B : QReg}
    (ℓ : A ≃ roundIn spec f × E) (post : roundOut spec f × E ≃ B) :
    seqCalls f E ℓ post =
      QuantumComp₂.queryBind (f 0) (QReg.of (roundIn spec (fun i ↦ f i.succ) × E))
        (seqSplitIn f E ℓ) fun r ↦
          (seqCalls (fun i ↦ f i.succ) (QReg.of (spec.Out (f 0) × E)) (seqShift f E)
            (seqPost f E post)).map (Fin.cons r) :=
  rfl

end Quantum.Par

namespace Quantum.QuantumRuntime

open Quantum.Par

variable {spec : QuantumOracleSpec.{u₁, v₁}} (R : QuantumRuntime spec)

/-- Before the step of `f 0` in a round step: its input and the runtime register, the other
inputs beside them. -/
def roundSplit {w : ℕ} (f : Fin (w + 1) → spec.Port) :
    roundIn spec f × R.D ≃ (spec.In (f 0) × R.D) × roundIn spec (fun i ↦ f i.succ) :=
  queryEquivIn (Fin.consEquiv fun i ↦ (spec.In (f i) : Type)).symm R.D

/-- After the step of `f 0`: the other inputs and the runtime register, the output of `f 0`
beside them. -/
def roundShift {w : ℕ} (f : Fin (w + 1) → spec.Port) :
    (spec.Out (f 0) × R.D) × roundIn spec (fun i ↦ f i.succ) ≃
      (roundIn spec (fun i ↦ f i.succ) × R.D) × spec.Out (f 0) :=
  (queryEquivOut (spec.Out (f 0)) R.D (roundIn spec (fun i ↦ f i.succ))).trans
    (queryEquivIn (Equiv.prodComm _ _) R.D)

/-- At the end of a round step: the outputs in order, beside the runtime register. -/
def roundJoin {w : ℕ} (f : Fin (w + 1) → spec.Port) :
    (roundOut spec (fun i ↦ f i.succ) × R.D) × spec.Out (f 0) ≃ roundOut spec f × R.D :=
  (queryEquivOut _ R.D (spec.Out (f 0))).trans
    ((((Equiv.prodComm _ _).trans (Fin.consEquiv fun i ↦ (spec.Out (f i) : Type))).prodCongr
      (Equiv.refl R.D)))

/-- **The step of a round**: the steps of `f 0`, …, `f (w-1)` in order, each on its own input
register and the runtime register, framed by the other components. -/
noncomputable def roundStep {w : ℕ} (f : Fin w → spec.Port) :
    SubInstrument (roundIn spec f × R.D) (roundOut spec f × R.D) (RoundResult spec f) :=
  match w, f with
  | 0, f => (relabel ((roundZeroEquiv f).prodCongr (Equiv.refl R.D))).map
      fun _ ↦ (finZeroElim : RoundResult spec f)
  | _ + 1, f =>
    (relabel (R.roundSplit f)).bind fun _ ↦
      ((R.step (f 0)).frame (roundIn spec (fun i ↦ f i.succ))).bind fun r ↦
        (relabel (R.roundShift f)).bind fun _ ↦
          ((roundStep (fun i ↦ f i.succ)).frame (spec.Out (f 0))).bind fun rs ↦
            (relabel (R.roundJoin f)).bind fun _ ↦
              SubInstrument.pure (Fin.cons (α := fun i ↦ spec.Result (f i)) r rs)

theorem roundStep_zero (f : Fin 0 → spec.Port) :
    R.roundStep f = (relabel ((roundZeroEquiv f).prodCongr (Equiv.refl R.D))).map
      fun _ ↦ (finZeroElim : RoundResult spec f) :=
  rfl

theorem roundStep_succ {w : ℕ} (f : Fin (w + 1) → spec.Port) :
    R.roundStep f =
      (relabel (R.roundSplit f)).bind fun _ ↦
        ((R.step (f 0)).frame (roundIn spec (fun i ↦ f i.succ))).bind fun r ↦
          (relabel (R.roundShift f)).bind fun _ ↦
            ((R.roundStep (fun i ↦ f i.succ)).frame (spec.Out (f 0))).bind fun rs ↦
              (relabel (R.roundJoin f)).bind fun _ ↦
                SubInstrument.pure (Fin.cons (α := fun i ↦ spec.Result (f i)) r rs) :=
  rfl

/-- **Exactness of a round.** Running the `w` calls of a round in order is the round step,
framed by the remainder `E`, between the relabellings of a call. -/
theorem run₂_seqCalls {w : ℕ} (f : Fin w → spec.Port) (E : QReg) {A B : QReg}
    (ℓ : A ≃ roundIn spec f × E) (post : roundOut spec f × E ≃ B) :
    R.run₂ .instruments (seqCalls f E ℓ post) =
      (relabel (queryEquivIn ℓ R.D)).bind fun _ ↦ ((R.roundStep f).frame E).bind fun rs ↦
        (relabel ((queryEquivOut (roundOut spec f) R.D E).trans
          (post.prodCongr (Equiv.refl R.D)))).bind fun _ ↦ SubInstrument.pure rs := by
  induction w generalizing E A B with
  | zero =>
    rw [seqCalls_zero, run₂_act, roundStep_zero]
    simp only [SubInstrument.map_eq_bind_pure, SubInstrument.frame_bind, frame_relabel,
      SubInstrument.frame_pure, SubInstrument.bind_assoc, SubInstrument.pure_bind,
      relabel_bind_relabel_bind]
    rfl
  | succ w ih =>
    rw [seqCalls_succ, run₂_queryBind, roundStep_succ]
    simp only [run₂_map, ih, queryStep, SubInstrument.map_eq_bind_pure, SubInstrument.frame_bind,
      frame_relabel, frame_frame, SubInstrument.frame_pure, SubInstrument.bind_assoc,
      SubInstrument.pure_bind, relabel_bind_relabel_bind]
    rfl

/-! ## Rounds of Kraus steps -/

/-- The Kraus operator of a round whose steps have the Kraus operators `K p r`: the relabellings
of `roundStep` around `K (f 0) (rs 0)` and the round of the other calls, each beside the identity
on the components it does not touch. -/
noncomputable def roundKraus
    (K : ∀ p, spec.Result p → Matrix (spec.Out p × R.D) (spec.In p × R.D) ℂ) :
    {w : ℕ} → (f : Fin w → spec.Port) → RoundResult spec f →
      Matrix (roundOut spec f × R.D) (roundIn spec f × R.D) ℂ
  | 0, f, _ => basisMatrix ((roundZeroEquiv f).prodCongr (Equiv.refl R.D))
  | _ + 1, f, rs =>
    basisMatrix (R.roundJoin f) *
      (roundKraus K (fun i ↦ f i.succ) (Fin.tail rs) ⊗ₖ (1 : Matrix (spec.Out (f 0))
        (spec.Out (f 0)) ℂ)) * basisMatrix (R.roundShift f) *
      (K (f 0) (rs 0) ⊗ₖ (1 : Matrix (roundIn spec (fun i ↦ f i.succ))
        (roundIn spec (fun i ↦ f i.succ)) ℂ)) * basisMatrix (R.roundSplit f)

/-- Relabelling, then returning a value other than `a`, has no branch at `a`. -/
private theorem branch_relabel_bind_pure_of_ne {S T : Type*} [Fintype S] [Fintype T]
    [DecidableEq S] [DecidableEq T] {α : Type*} (e : S ≃ T) {a b : α} (h : a ≠ b) :
    ((relabel e).bind fun _ ↦ SubInstrument.pure b).branch a = 0 := by
  rw [DSubInstrument.branch_bind_unit, SubInstrument.branch_pure_of_ne h, LinearMap.zero_comp]

/-- **A round of Kraus steps is a Kraus map**: if every step of `R` is the Kraus map of `K p r`
at the result `r`, the round step at the results `rs` is the Kraus map of `roundKraus`. -/
theorem branch_roundStep_of_conj
    (K : ∀ p, spec.Result p → Matrix (spec.Out p × R.D) (spec.In p × R.D) ℂ)
    (hK : ∀ p r, (R.step p).branch r = MatrixMap.conj (K p r)) {w : ℕ}
    (f : Fin w → spec.Port) (rs : RoundResult spec f) :
    (R.roundStep f).branch rs = MatrixMap.conj (R.roundKraus K f rs) := by
  induction w with
  | zero =>
    obtain rfl : rs = finZeroElim := funext fun i ↦ i.elim0
    rw [roundStep_zero, SubInstrument.map_eq_bind_pure, DSubInstrument.branch_bind_unit,
      SubInstrument.branch_pure_self, LinearMap.id_comp, branch_relabel]
    rfl
  | succ w ih =>
    have hz : ∀ r rs', (r ≠ rs 0 ∨ rs' ≠ Fin.tail rs) →
        ((relabel (R.roundJoin f)).bind fun _ ↦
          SubInstrument.pure (Fin.cons (α := fun i ↦ spec.Result (f i)) r rs')).branch rs = 0 := by
      intro r rs' h
      refine branch_relabel_bind_pure_of_ne _ fun he ↦ ?_
      rcases h with h | h
      · exact h ((Fin.cons_zero _ _).symm.trans (congrFun he 0).symm)
      · exact h ((Fin.tail_cons _ _).symm.trans (congrArg Fin.tail he).symm)
    refine LinearMap.ext fun ρ ↦ ?_
    rw [roundStep_succ, DSubInstrument.branch_bind_unit, LinearMap.comp_apply,
      DSubInstrument.branch_bind_apply, tsum_eq_single (rs 0) fun r hr ↦ ?_]
    · rw [DSubInstrument.branch_bind_unit, LinearMap.comp_apply,
        DSubInstrument.branch_bind_apply, tsum_eq_single (Fin.tail rs) fun rs' h ↦ ?_]
      · rw [Fin.cons_self_tail, DSubInstrument.branch_bind_unit, SubInstrument.branch_pure_self,
          LinearMap.id_comp, DSubInstrument.branch_frame_apply, DSubInstrument.branch_frame_apply,
          hK, ih, MatrixMap.amplify_conj, MatrixMap.amplify_conj, branch_relabel, branch_relabel,
          branch_relabel, roundKraus]
        simp only [MatrixMap.conj_apply, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      · rw [hz _ _ (.inr h), LinearMap.zero_apply]
    · simp only [DSubInstrument.branch_bind_unit, LinearMap.comp_apply,
        DSubInstrument.branch_bind_apply, fun rs' ↦ hz r rs' (.inl hr), LinearMap.zero_apply,
        tsum_zero]

end Quantum.QuantumRuntime

namespace Quantum.Par

variable {spec : QuantumOracleSpec.{u₁, v₁}}

/-! ## Budgets of the calls of a round -/

/-- A charge on ports as a charge on commands: a call of port `i` costs `c i`, a local
operation nothing. -/
def callCharge {L : LocalSig.{u, v}} (c : spec.Port → ℕ) (A : QReg) :
    QuantumComp.Cmd L spec A → ℕ
  | .prim _ => 0
  | .query i _ _ => c i

/-- Mapping the return value keeps every charge bound. -/
theorem isChargeBound_map {L : LocalSig.{u, v}} {A B : QReg} {α β : Type*}
    {c : (A : QReg) → QuantumComp.Cmd L spec A → ℕ} {x : QuantumComp₂ L spec A B α} {n : ℕ}
    (hx : IFreeM.IsChargeBound x c n) (g : α → β) : IFreeM.IsChargeBound (x.map g) c n := by
  rw [QuantumComp₂.map_eq_bind_pure]
  exact FreeM₂.isChargeBound_bind (n₂ := 0) hx fun _ ↦ trivial

/-- **The calls of a round cost the charges of their ports**: `k i` bounds the charge of a call
of `f i`, and local operations are free. -/
theorem isChargeBound_seqCalls {w : ℕ} {f : Fin w → spec.Port}
    {c : (A : QReg) → QuantumComp.Cmd LocalSig.instruments.{v₁} spec A → ℕ}
    (hprim : ∀ A o, c A (.prim o) = 0) {k : Fin w → ℕ}
    (hq : ∀ i A E ℓ, c A (.query (f i) E ℓ) ≤ k i) (E : QReg) {A B : QReg}
    (ℓ : A ≃ roundIn spec f × E) (post : roundOut spec f × E ≃ B) :
    IFreeM.IsChargeBound (seqCalls f E ℓ post) c (∑ i, k i) := by
  induction w generalizing E A B with
  | zero =>
    rw [seqCalls_zero]
    exact ⟨(hprim _ _).trans_le (Nat.zero_le _), fun _ ↦ trivial⟩
  | succ w ih =>
    rw [seqCalls_succ]
    refine ⟨(hq 0 _ _ _).trans (Fin.sum_univ_succ k ▸ Nat.le_add_right _ _), fun r ↦ ?_⟩
    refine isChargeBound_map (IFreeM.IsChargeBound.mono
      (ih (fun i A E ℓ ↦ hq i.succ A E ℓ) _ _ _) ?_) _
    rw [Fin.sum_univ_succ]
    exact Nat.le_sub_of_add_le ((Nat.add_comm _ _).trans_le
      (Nat.add_le_add_right (hq 0 A _ (seqSplitIn f E ℓ)) _))

/-! ## The parallel signature -/

/-- A round of calls of the ports named by `Q`: its width `w` and the port of each call. -/
inductive ParPort (Q : Type u₁) : Type u₁
  /-- The round of the calls `f 0, …, f (w-1)`. -/
  | round (w : ℕ) (f : Fin w → Q)

variable (spec) {Q : Type u₁} (port : Q → spec.Port)

/-- The round ports alone: a round of the ports named by `Q` acts on their registers side by
side and reports all their results. -/
@[reducible]
def roundSpec : QuantumOracleSpec.{u₁, v₁} where
  Port := ParPort Q
  In | .round _ f => roundIn spec fun i ↦ port (f i)
  Out | .round _ f => roundOut spec fun i ↦ port (f i)
  Result | .round _ f => RoundResult spec fun i ↦ port (f i)

/-- **The parallel signature**: the single ports of `spec` (on the left) and a round port for
every tuple of ports named by `Q` (on the right). -/
@[reducible]
def parSpec : QuantumOracleSpec.{u₁, v₁} :=
  spec.sum (roundSpec spec port)

variable {spec}

/-- The calls a command of the parallel signature makes, counted by `c`: a single call of `p`
costs `c p`, a round the sum over its calls. -/
def widthCharge (c : spec.Port → ℕ) : (parSpec spec port).Port → ℕ
  | .inl p => c p
  | .inr (.round _ f) => ∑ i, c (port (f i))

/-- Whether a command of the parallel signature makes a call charged by `c`: one for a single
charged call or a round with a charged call, zero otherwise. -/
def roundCharge (c : spec.Port → ℕ) (i : (parSpec spec port).Port) : ℕ :=
  if widthCharge port c i = 0 then 0 else 1

/-- A command's round count is at most its width. -/
theorem roundCharge_le_widthCharge (c : spec.Port → ℕ) (i : (parSpec spec port).Port) :
    roundCharge port c i ≤ widthCharge port c i := by
  unfold roundCharge
  split_ifs <;> omega

/-- **The parallel runtime**: single calls as in `R`, rounds by `QuantumRuntime.roundStep`. It
is `R` extended by the round ports, so `QuantumRuntime.run_liftOrdinary` applies. -/
noncomputable def _root_.Quantum.QuantumRuntime.par (R : QuantumRuntime spec) :
    QuantumRuntime (parSpec spec port) :=
  R.extend fun | .round _ f => R.roundStep fun i ↦ port (f i)

/-- **A round is its calls, in order**: local operations and single calls stay, a round
becomes `seqCalls`. -/
noncomputable def parToSeq :
    CommandSubstitution (QuantumComp.toIPFunctor LocalSig.instruments.{v₁} (parSpec spec port))
      (QuantumComp.toIPFunctor LocalSig.instruments.{v₁} spec)
  | _, .prim o => QuantumComp.primBind o fun b ↦ QuantumComp.pure ⟨ULift.up b, rfl⟩
  | _, .query (.inl p) E ℓ =>
      QuantumComp.queryBind (spec := spec) p E ℓ fun r ↦ QuantumComp.pure ⟨ULift.up r, rfl⟩
  | _, .query (.inr (.round _ f)) E ℓ =>
      QuantumComp.bind
        (seqCalls (fun i ↦ port (f i)) E (B := QReg.of (roundOut spec (fun i ↦ port (f i)) × E))
          ℓ (Equiv.refl _)) fun _ l ↦ QuantumComp.pure ⟨ULift.up l.2, l.1.symm⟩

/-- **Budgets of the serialization.** A parallel program within the width budget `n` for the
charge `c` makes calls of charge at most `n` once each round is replaced by its calls. -/
theorem isChargeBound_substitute_parToSeq (c : spec.Port → ℕ) {X : QReg → Type*} {A : QReg}
    {x : QuantumComp LocalSig.instruments.{v₁} (parSpec spec port) X A} {n : ℕ}
    (hx : IFreeM.IsChargeBound x (callCharge (widthCharge port c)) n) :
    IFreeM.IsChargeBound (IFreeM.substitute (parToSeq port) x) (callCharge c) n := by
  refine IFreeM.IsChargeBound.substitute (parToSeq port) (fun A cmd ↦ ?_) hx
  rcases cmd with o | ⟨p | ⟨w, f⟩, E, ℓ⟩
  · exact ⟨le_rfl, fun _ ↦ trivial⟩
  · exact ⟨le_rfl, fun _ ↦ trivial⟩
  · exact IFreeM.isChargeBound_bind (n₂ := 0)
      (isChargeBound_seqCalls (fun _ _ ↦ rfl) (fun _ _ _ _ ↦ le_rfl) E ℓ _) fun _ _ ↦ trivial

end Quantum.Par

namespace Quantum.QuantumRuntime

open Quantum.Par

variable {spec : QuantumOracleSpec.{u₁, v₁}} (R : QuantumRuntime spec) {Q : Type u₁}
  (port : Q → spec.Port)

/-- Sequencing after the run of a fixed-register program sees only its leaves on `B`. -/
theorem bind_run_eq_bind_run₂ {L : LocalSig.{u, v}} (I : L.Interp) {A B : QReg} {α : Type w}
    {Y : QReg → Type w₁} (x : QuantumComp₂ L spec A B α)
    (g : (p : Σ u, QuantumComp₂.Leaf B α u) →
      DSubInstrument (p.1 × R.D) (Σ u, Y u) fun q ↦ q.1 × R.D) :
    (R.run I x).bind g = DSubInstrument.bind (R.run₂ I x) fun a ↦ g ⟨B, rfl, a⟩ :=
  DSubInstrument.ext <| funext fun q ↦ LinearMap.ext fun ρ ↦ by
    rw [DSubInstrument.branch_bind_apply, DSubInstrument.branch_bind_apply,
      ← (QuantumComp₂.leafEquiv B α).tsum_eq]
    rfl

/-- The call of a round port of `R.par` is the run of its calls against `R`. -/
theorem queryStep_par_round {w : ℕ} (f : Fin w → Q) (E : QReg) {A : QReg}
    (ℓ : A ≃ roundIn spec (fun i ↦ port (f i)) × E) :
    (R.par port).queryStep (.inr (.round w f)) E ℓ =
      R.run₂ .instruments (seqCalls (fun i ↦ port (f i)) E
        (B := QReg.of (roundOut spec (fun i ↦ port (f i)) × E)) ℓ (Equiv.refl _)) := by
  rw [run₂_seqCalls]
  rfl

/-- Running a fixed-register program followed by a continuation on its leaves. -/
theorem run_bind_leaf {L : LocalSig.{u, v}} (I : L.Interp) {A B : QReg} {α : Type w}
    {Y : QReg → Type w₁} (x : QuantumComp₂ L spec A B α)
    (g : ∀ u, QuantumComp₂.Leaf B α u → QuantumComp L spec Y u) :
    R.run I (IFreeM.bind x g) =
      DSubInstrument.bind (R.run₂ I x) fun a ↦ R.run I (g B ⟨rfl, a⟩) :=
  (R.run_bind I x g).trans (R.bind_run_eq_bind_run₂ I x _)

/-- **Serialization is exact.** A parallel program run against `R.par` runs as the program
with each round replaced by its calls, run against `R`. -/
theorem run_substitute_parToSeq {X : QReg → Type w} {A : QReg}
    (x : QuantumComp LocalSig.instruments.{v₁} (parSpec spec port) X A) :
    R.run .instruments (IFreeM.substitute (parToSeq port) x) =
      (R.par port).run .instruments x := by
  induction x using QuantumComp.inductionOn with
  | pure _ y => exact (R.run_pure _ y).trans ((R.par port).run_pure _ y).symm
  | primBind _ o k ih =>
    exact congrArg (DSubInstrument.bind ((LocalSig.Interp.instruments o).frame R.D)) (funext ih)
  | queryBind _ i E ℓ k ih =>
    rcases i with p | ⟨w, f⟩
    · exact congrArg (DSubInstrument.bind (R.queryStep p E ℓ)) (funext ih)
    · exact (congrArg (R.run .instruments) (IFreeM.bind_assoc _ _ _)).trans
        ((R.run_bind_leaf _ _ _).trans
          ((congrArg (DSubInstrument.bind _) (funext ih)).trans
            (congrArg (fun p ↦ DSubInstrument.bind p fun r ↦ (R.par port).run .instruments (k r))
              (R.queryStep_par_round port f E ℓ).symm)))

/-! ## Weights of the serialization -/

section weight

variable {K : spec.Port → Type*} [∀ p, Fintype (K p)] {Φ : ∀ p, MatrixMap (spec.In p × R.D) (K p)}

/-- The calls of a round have no weight when the weight vanishes on their ports. -/
theorem totalWeight_seqCalls_eq_zero (hΦ : ∀ p, (Φ p).IsCP) {w : ℕ} (f : Fin w → spec.Port)
    (hf : ∀ i, Φ (f i) = 0) (E : QReg) {A B : QReg} (ℓ : A ≃ roundIn spec f × E)
    (post : roundOut spec f × E ≃ B) {ρ : Matrix (A × R.D) (A × R.D) ℂ} (hρ : ρ.PosSemidef) :
    R.totalWeight .instruments (fun p σ ↦ ENNReal.ofReal (Φ p σ).trace.re)
      (seqCalls f E ℓ post) ρ = 0 := by
  induction w generalizing E A B ρ with
  | zero =>
    exact (R.totalWeight_primBind _ _ _ ρ).trans
      (ENNReal.tsum_eq_zero.mpr fun _ ↦ R.totalWeight_pure _ _ _)
  | succ w ih =>
    refine (R.totalWeight_queryBind _ _ _ _ _ ρ).trans ?_
    rw [hf 0, LinearMap.zero_apply, Matrix.trace_zero, Complex.zero_re, ENNReal.ofReal_zero,
      zero_add]
    refine ENNReal.tsum_eq_zero.mpr fun r ↦ ?_
    have hb := (R.queryStep (f 0) _ (seqSplitIn f E ℓ)).posSemidef_branch_apply r hρ
    rw [QuantumComp₂.map_eq_bind_pure]
    refine (R.totalWeight_bind _ hΦ
      (seqCalls (fun i ↦ f i.succ) _ (seqShift f E) (seqPost f E post)) _ hb).trans ?_
    rw [ih _ (fun i ↦ hf i.succ) _ _ _ hb, zero_add]
    refine ENNReal.tsum_eq_zero.mpr fun ⟨u, h, a⟩ ↦ ?_
    subst h
    exact R.totalWeight_pure _ _ _

/-- The weight of the calls of a round followed by a continuation, when the weight vanishes on
the ports of the round: the weights of the continuations from the branches of the round. -/
theorem totalWeight_bind_seqCalls (hΦ : ∀ p, (Φ p).IsCP) {w : ℕ} (f : Fin w → spec.Port)
    (hf : ∀ i, Φ (f i) = 0) (E : QReg) {A B : QReg} (ℓ : A ≃ roundIn spec f × E)
    (post : roundOut spec f × E ≃ B) {X : QReg → Type w₁}
    (g : ∀ u, QuantumComp₂.Leaf B (RoundResult spec f) u →
      QuantumComp LocalSig.instruments.{v₁} spec X u)
    {ρ : Matrix (A × R.D) (A × R.D) ℂ} (hρ : ρ.PosSemidef) :
    R.totalWeight .instruments (fun p σ ↦ ENNReal.ofReal (Φ p σ).trace.re)
      (IFreeM.bind (seqCalls f E ℓ post) g) ρ =
      ∑' rs, R.totalWeight .instruments (fun p σ ↦ ENNReal.ofReal (Φ p σ).trace.re)
        (g B ⟨rfl, rs⟩) ((R.run₂ .instruments (seqCalls f E ℓ post)).branch rs ρ) := by
  refine (R.totalWeight_bind _ hΦ _ g hρ).trans ?_
  rw [R.totalWeight_seqCalls_eq_zero hΦ f hf E ℓ post hρ, zero_add]
  exact ((QuantumComp₂.leafEquiv B _).tsum_eq _).symm

/-- A weight on the calls of `spec` as a weight on the calls of the parallel signature: single
calls keep their weight, rounds have none. -/
def parWeight {D : Type*} (W : ∀ p, Matrix (spec.In p × D) (spec.In p × D) ℂ → ℝ≥0∞) :
    ∀ i, Matrix ((parSpec spec port).In i × D) ((parSpec spec port).In i × D) ℂ → ℝ≥0∞
  | .inl p => W p
  | .inr _ => fun _ ↦ 0

/-- **Weights of the serialization.** For a weight that vanishes on the ports of rounds, the
summed weight of the serialization is the summed weight of the parallel program on its single
calls. -/
theorem totalWeight_substitute_parToSeq (hΦ : ∀ p, (Φ p).IsCP) (hvan : ∀ q, Φ (port q) = 0)
    {X : QReg → Type w} {A : QReg}
    (x : QuantumComp LocalSig.instruments.{v₁} (parSpec spec port) X A)
    {ρ : Matrix (A × R.D) (A × R.D) ℂ} (hρ : ρ.PosSemidef) :
    R.totalWeight .instruments (fun p σ ↦ ENNReal.ofReal (Φ p σ).trace.re)
        (IFreeM.substitute (parToSeq port) x) ρ =
      (R.par port).totalWeight .instruments
        (parWeight port fun p σ ↦ ENNReal.ofReal (Φ p σ).trace.re) x ρ := by
  induction x using QuantumComp.inductionOn with
  | pure _ y => exact (R.totalWeight_pure _ y ρ).trans ((R.par port).totalWeight_pure _ y ρ).symm
  | primBind _ o k ih =>
    exact (R.totalWeight_primBind _ o (fun b ↦ IFreeM.substitute (parToSeq port) (k b)) ρ).trans
      ((tsum_congr fun b ↦ ih b
        (((LocalSig.Interp.instruments o).frame R.D).posSemidef_branch_apply b hρ)).trans
        ((R.par port).totalWeight_primBind _ o k ρ).symm)
  | queryBind _ i E ℓ k ih =>
    rcases i with p | ⟨w, f⟩
    · exact (R.totalWeight_queryBind _ p E ℓ (fun r ↦ IFreeM.substitute (parToSeq port) (k r))
        ρ).trans ((congrArg (_ + ·) (tsum_congr fun r ↦ ih r
          ((R.queryStep p E ℓ).posSemidef_branch_apply r hρ))).trans
          ((R.par port).totalWeight_queryBind _ (w := parWeight port fun p σ ↦
            ENNReal.ofReal (Φ p σ).trace.re) (.inl p) E ℓ k ρ).symm)
    · have hq := R.queryStep_par_round port f E ℓ
      have hb : ∀ r, ((R.par port).queryStep (.inr (.round w f)) E ℓ).branch r ρ =
          (R.run₂ .instruments (seqCalls (fun i ↦ port (f i)) E
            (B := QReg.of (roundOut spec (fun i ↦ port (f i)) × E)) ℓ (Equiv.refl _))).branch
              r ρ := fun r ↦ congrArg (fun S ↦ DSubInstrument.branch S r ρ) hq
      exact (congrArg (fun y ↦ R.totalWeight .instruments
          (fun p σ ↦ ENNReal.ofReal (Φ p σ).trace.re) y ρ) (IFreeM.bind_assoc _ _ _)).trans
        ((R.totalWeight_bind_seqCalls hΦ _ (fun i ↦ hvan (f i)) E ℓ _ _ hρ).trans
          ((tsum_congr fun r ↦ (ih r ((R.run₂ .instruments _).posSemidef_branch_apply r hρ)).trans
            (congrArg ((R.par port).totalWeight .instruments _ (k r)) (hb r).symm)).trans
            ((zero_add _).symm.trans
              ((R.par port).totalWeight_queryBind _ (w := parWeight port fun p σ ↦
                ENNReal.ofReal (Φ p σ).trace.re) (.inr (.round w f)) E ℓ k ρ).symm)))

end weight

end Quantum.QuantumRuntime
