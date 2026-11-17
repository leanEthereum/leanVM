module

public import Quantum.Sponge.Indifferentiability.FixCircuit
public import Quantum.Sponge.Indifferentiability.Pad

@[expose] public section

/-!
# The simulated sponge oracle as a circuit of calls of `H`

The sponge's random oracle `f' = simOracle sp conv pre x0 H Q` (`Pad.lean`) is implemented
exactly by calls of the random oracle `H : D → Y`, with the private `Q : M → X` hardwired as a
local basis map. A call `|m, y, e⟩ ↦ |m, y + f' m, e⟩` (`simOracleCall`):

* adds `privPart Q m` into `y` and prepares a fresh register `|preD m, 0⟩`, by one isometry;
* calls `H`, so the fresh register holds `H (preD m)`;
* adds `sp.symm (conv w, 0)` into `y` and negates `w`, by one local permutation;
* calls `H` again, which returns `w` to `0`, and removes the fresh register (`coGate`).

It costs two calls of `H`. One call does not suffice in general: `H` adds in `Y` (at Keccak,
addition modulo `2 ^ 256`) and the target adds in `X` (xor), and `conv` is not additive.

`convertSim I sp conv pre x0 Q x` substitutes `simOracleCall` for every call of a program `x`
over `qromSpec M X`. Against `H` it runs as `x` against `f'` (`run_convertSim`,
`evalDistMap_convertSim`), with at most `2 * q` calls of `H` if `x` makes `q`
(`isQueryBound_convertSim`, `isTotalQueryBound_convertSim`). At Keccak: `keccakSimCall`,
`convertKeccakSim`, against `additiveOracleRuntime (keccakSim H Q)`.
-/

open MeasureTheory IPFunctor

universe u v w

namespace Quantum.Sponge

open Quantum

/-! ## One call of the simulated oracle -/

section call

variable {D M X Y Yb R : Type} [Fintype D] [DecidableEq D] [Fintype M] [DecidableEq M]
  [Fintype X] [DecidableEq X] [AddCommGroup X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  [AddCommGroup Yb] [AddCommGroup R]

/-- The register of the response of a call of the oracle on `M × X`, beside its remainder. -/
abbrev padReg (M X : Type) [Fintype M] [DecidableEq M] [Fintype X] [DecidableEq X]
    (E : QReg) : QReg :=
  QReg.of ((qromSpec M X).Out () × E)

/-- A register `D × Y` for the calls of `H`, beside a remainder `F`. -/
abbrev hReg (D Y : Type) [Fintype D] [DecidableEq D] [Fintype Y] [DecidableEq Y]
    (F : QReg) : QReg :=
  QReg.of ((D × Y) × F)

variable (D) in
/-- One call of `H` on the fresh register. -/
noncomputable def padQuery (F : QReg) :
    QuantumComp₂ LocalSig.instruments.{v} (qromSpec D Y) (hReg D Y F) (hReg D Y F) Unit :=
  QuantumComp₂.query (L := LocalSig.instruments.{v}) (spec := qromSpec D Y) () F (Equiv.refl _)

variable (sp : X ≃+ Yb × R) (conv : Y ≃ Yb) (pre : M → Option D) (x0 : D) (Q : M → X)
  (E : QReg)

/-- The first isometry: `|m, y, e⟩ ↦ |preD m, 0⟩|m, y + privPart Q m, e⟩`. -/
def padIn {A : QReg} (ℓ : A ≃ (qromSpec M X).In () × E) (a : A) :
    (D × Y) × ((M × X) × E) :=
  ((preD pre x0 ((ℓ a).1 : M × X).1, 0),
    ((((ℓ a).1 : M × X).1, ((ℓ a).1 : M × X).2 + privPart sp pre Q ((ℓ a).1 : M × X).1),
      (ℓ a).2))

omit [Fintype D] [DecidableEq D] [Fintype Y] [DecidableEq Y] in
theorem padIn_injective {A : QReg} (ℓ : A ≃ (qromSpec M X).In () × E) :
    Function.Injective (padIn (Y := Y) sp pre x0 Q E ℓ) := by
  intro a b h
  have h2 := congrArg Prod.snd h
  simp only [padIn, Prod.mk.injEq] at h2
  obtain ⟨⟨hm, hy⟩, he⟩ := h2
  rw [hm, add_left_inj] at hy
  exact ℓ.injective (Prod.ext (Prod.ext hm hy) he)

/-- The middle permutation: `|d, w⟩|m, y, e⟩ ↦ |d, -w⟩|m, y + sp.symm (conv w, 0), e⟩`. -/
def padMid (F : Type) : (D × Y) × ((M × X) × F) ≃ (D × Y) × ((M × X) × F) where
  toFun q := ((q.1.1, -q.1.2), ((q.2.1.1, q.2.1.2 + sp.symm (conv q.1.2, 0)), q.2.2))
  invFun q := ((q.1.1, -q.1.2), ((q.2.1.1, q.2.1.2 - sp.symm (conv (-q.1.2), 0)), q.2.2))
  left_inv q := by simp
  right_inv q := by simp

/-- The fresh register `|preD m, 0⟩` beside the response, which `coGate` removes. -/
def padOut (F : Type) (r : (M × X) × F) : (D × Y) × ((M × X) × F) :=
  ((preD pre x0 r.1.1, 0), r)

omit [Fintype D] [DecidableEq D] [Fintype M] [DecidableEq M] [Fintype X] [DecidableEq X]
  [AddCommGroup X] [Fintype Y] [DecidableEq Y] in
theorem padOut_injective (F : Type) : Function.Injective (padOut pre x0 (X := X) (Y := Y) F) :=
  fun _ _ h ↦ congrArg Prod.snd h

/-- **One call of the simulated oracle** by two calls of `H`. -/
noncomputable def simOracleCall {A : QReg} (ℓ : A ≃ (qromSpec M X).In () × E) :
    QuantumComp₂ LocalSig.instruments.{v} (qromSpec D Y) A (padReg M X E) Unit :=
  ((isoGate (B := hReg D Y (padReg M X E)) (padIn sp pre x0 Q E ℓ)
    (padIn_injective sp pre x0 Q E ℓ)).bind fun _ ↦
    (padQuery D (padReg M X E)).bind fun _ ↦
      (isoGate (B := hReg D Y (padReg M X E)) (padMid sp conv E)
        (padMid sp conv E).injective).bind fun _ ↦
        padQuery D (padReg M X E)).bind fun _ ↦
    coGate (A := hReg D Y (padReg M X E)) (B := padReg M X E) (padOut pre x0 E)
      (padOut_injective pre x0 E)

variable {sp conv pre x0 Q E}

theorem runsAs_padQuery (H : D → Y) (F : QReg) :
    RunsAs (additiveOracleRuntime H) (padQuery.{v} D F)
      (Prod.map (Prod.map (oracleEquiv H) (id : F → F)) id) := by
  have hstep : ((additiveOracleRuntime H).step ()).branch () =
      MatrixMap.conj (basisMatrix (Prod.map (oracleEquiv H) (id : Unit → Unit))) :=
    branch_frame_oracleQuery H Unit
  refine RunsAs.congr (f := QuantumRuntime.queryEquivOut ((qromSpec D Y).In ())
    (additiveOracleRuntime H).D F ∘ Prod.map (Prod.map (oracleEquiv H) id) id ∘
      QuantumRuntime.queryEquivIn (Equiv.refl (hReg D Y F)) (additiveOracleRuntime H).D) ?_
    fun _ ↦ rfl
  rw [RunsAs, padQuery, QuantumRuntime.run₂_query, SubInstrument.bind,
    DSubInstrument.branch_bind_unit, SubInstrument.branch_pure_self, LinearMap.id_comp]
  exact branch_queryStep_of_basis _ _ hstep F _

/-- **The circuit runs as the call of the simulated oracle.** -/
theorem runsAs_simOracleCall (H : D → Y) {A : QReg} (ℓ : A ≃ (qromSpec M X).In () × E) :
    RunsAs (additiveOracleRuntime H) (simOracleCall.{v} sp conv pre x0 Q E ℓ)
      (qromCallMap (simOracle sp conv pre x0 H Q) ℓ) := by
  unfold simOracleCall
  refine ((runsAs_isoGate _ _).bind ((runsAs_padQuery H _).bind
    ((runsAs_isoGate _ _).bind (runsAs_padQuery H _)))).bind_coGate _ _ _ fun q ↦ ?_
  simp [Prod.map_apply', padIn, padMid, padOut, qromCallMap, simOracle, add_assoc]

/-- The circuit makes two calls of `H`. -/
theorem isQueryBound_simOracleCall {A : QReg} (ℓ : A ≃ (qromSpec M X).In () × E) :
    (simOracleCall.{v} sp conv pre x0 Q E ℓ).IsQueryBound fun _ ↦ 2 := by
  have hq : ∀ F, (padQuery.{v} D (Y := Y) F).IsQueryBound fun _ ↦ 1 := fun F ↦
    (QuantumComp₂.isQueryBound_query_iff _ _ _ _).mpr Nat.one_pos
  refine (QuantumComp₂.isQueryBound_bind (QuantumComp₂.isQueryBound_bind
    (isQueryBound_isoGate_spec _ _ 0) fun _ ↦ QuantumComp₂.isQueryBound_bind (hq _) fun _ ↦
      QuantumComp₂.isQueryBound_bind (isQueryBound_isoGate_spec _ _ 0) fun _ ↦ hq _)
    fun _ ↦ isQueryBound_coGate_spec _ _ 0).mono ?_
  intro i
  simp

end call

/-! ## Substitution -/

section subst

variable {D M X Y Yb R : Type} [Fintype D] [DecidableEq D] [Fintype M] [DecidableEq M]
  [Fintype X] [DecidableEq X] [AddCommGroup X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  [AddCommGroup Yb] [AddCommGroup R]
  {L : LocalSig.{u, v}} {W : QReg → Type w} (I : L.Interp)
  (sp : X ≃+ Yb × R) (conv : Y ≃ Yb) (pre : M → Option D) (x0 : D) (Q : M → X)

/-- The tree that replaces a call through `ℓ`: `simOracleCall`, ending at the call's response. -/
noncomputable def simOracleTree (E : QReg) {A : QReg} (ℓ : A ≃ (qromSpec M X).In () × E) :
    QuantumComp LocalSig.instruments.{v} (qromSpec D Y)
      (fun t ↦ Subtype fun _ : ULift.{v} Unit ↦ padReg M X E = t) A :=
  QuantumComp.bind (simOracleCall sp conv pre x0 Q E ℓ) fun _ l ↦
    QuantumComp.pure ⟨ULift.up (), l.1.symm⟩

/-- The substitution: a local operation becomes the instrument that `I` gives it, and a call
becomes `simOracleTree`. -/
noncomputable def convertSubst :
    CommandSubstitution (QuantumComp.toIPFunctor L (qromSpec M X))
      (QuantumComp.toIPFunctor LocalSig.instruments.{v} (qromSpec D Y))
  | _, .prim o => QuantumComp.primBind (L := LocalSig.instruments.{v})
      ⟨L.Outcome o, fun b ↦ L.next o b, I o⟩ fun b ↦ QuantumComp.pure ⟨ULift.up b, rfl⟩
  | _, .query () E ℓ => simOracleTree sp conv pre x0 Q E ℓ

/-- **The conversion of a program over the sponge's random oracle** into one over `H`: every
local operation becomes the instrument that `I` gives it, and every call becomes
`simOracleCall`. -/
noncomputable def convertSim {A : QReg} (x : QuantumComp L (qromSpec M X) W A) :
    QuantumComp LocalSig.instruments.{v} (qromSpec D Y) W A :=
  IFreeM.substitute (convertSubst I sp conv pre x0 Q) x

omit [AddCommGroup Y] in
/-- On a single-port signature, the budget of the port is the total budget. -/
theorem queryCharge_qromSpec {L' : LocalSig.{u, v}} :
    QuantumComp.queryCharge (L := L') (spec := qromSpec D Y) () = fun _ c ↦ c.queryCharge := by
  funext A c
  cases c with
  | prim o => rfl
  | query j E ℓ => simp [QuantumComp.queryCharge, QuantumComp.Cmd.queryCharge]

/-- **Query budget.** If every path of `x` makes at most `q` calls, every path of the conversion
makes at most `2 * q` calls of `H`. -/
theorem isQueryBound_convertSim {A : QReg}
    {x : QuantumComp L (qromSpec M X) W A} {q : ℕ} (hx : x.IsTotalQueryBound q) :
    (convertSim I sp conv pre x0 Q x).IsQueryBound fun _ ↦ 2 * q := by
  intro j
  refine IFreeM.IsChargeBound.substitute_mul (convertSubst I sp conv pre x0 Q) 2
    (fun B c ↦ ?_) hx
  cases c with
  | prim o =>
    exact (QuantumComp.isQueryBoundAt_primBind_iff (L := LocalSig.instruments.{v}) _ _ j _).mpr
      fun _ ↦ trivial
  | query p E ℓ =>
    cases p
    show (simOracleTree sp conv pre x0 Q E ℓ).IsQueryBoundAt j (2 + 0)
    exact QuantumComp.IsQueryBoundAt.bind (isQueryBound_simOracleCall ℓ j) fun _ _ ↦ trivial

/-- The conversion makes at most `2 * q` calls in total. -/
theorem isTotalQueryBound_convertSim {A : QReg}
    {x : QuantumComp L (qromSpec M X) W A} {q : ℕ} (hx : x.IsTotalQueryBound q) :
    (convertSim I sp conv pre x0 Q x).IsTotalQueryBound (2 * q) := by
  have h := isQueryBound_convertSim I sp conv pre x0 Q hx ()
  unfold QuantumComp.IsQueryBoundAt at h
  unfold QuantumComp.IsTotalQueryBound
  rwa [queryCharge_qromSpec] at h

theorem branch_run_simOracleTree_bind (Rt : QuantumRuntime (qromSpec D Y)) (E : QReg)
    {A : QReg} (ℓ : A ≃ (qromSpec M X).In () × E)
    (g : ∀ t, (Subtype fun _ : ULift.{v} Unit ↦ padReg M X E = t) →
      QuantumComp LocalSig.instruments.{v} (qromSpec D Y) W t) (q : Σ u, W u) :
    (Rt.run .instruments ((simOracleTree sp conv pre x0 Q E ℓ).bind g)).branch q =
      (Rt.run .instruments (g _ ⟨ULift.up (), rfl⟩)).branch q ∘ₗ
        (Rt.run₂ .instruments (simOracleCall.{v} sp conv pre x0 Q E ℓ)).branch () :=
  (congrArg (fun y ↦ (Rt.run .instruments y).branch q)
    (QuantumComp.bind_assoc (simOracleCall sp conv pre x0 Q E ℓ) _ g)).trans
    (branch_run_bind_unit Rt .instruments _ _ q)

/-- **The conversion runs as the simulated oracle.** Against `H`, the conversion of `x` runs to
the same dependent subinstrument as `x` against `simOracle sp conv pre x0 H Q`. -/
theorem run_convertSim (H : D → Y) {A : QReg}
    (x : QuantumComp L (qromSpec M X) W A) :
    (additiveOracleRuntime H).run .instruments (convertSim I sp conv pre x0 Q x) =
      (additiveOracleRuntime (simOracle sp conv pre x0 H Q)).run I x := by
  induction x using QuantumComp.inductionOn with
  | pure _ _ => rfl
  | primBind _ o k ih =>
    rw [QuantumRuntime.run_primBind]
    exact congrArg (((I o).frame _).bind) (funext ih)
  | queryBind _ p E ℓ k ih =>
    cases p
    refine DSubInstrument.ext (funext fun q ↦ ?_)
    refine (branch_run_simOracleTree_bind sp conv pre x0 Q _ E ℓ _ q).trans ?_
    have hs := runsAs_simOracleCall.{v} (sp := sp) (conv := conv) (pre := pre) (x0 := x0)
      (Q := Q) H ℓ
    rw [RunsAs] at hs
    rw [hs, QuantumRuntime.run_queryBind, DSubInstrument.branch_bind_unit,
      branch_queryStep_qromCallMap, ← ih ()]
    rfl

/-- The conversion is observed as the original program against the simulated oracle. -/
theorem evalDistMap_convertSim {β : Type*} [MeasurableSpace β] (H : D → Y) {A : QReg}
    (x : QuantumComp L (qromSpec M X) W A) (ρ : SubState A) (f : (Σ u, W u) → β) :
    (additiveOracleRuntime H).evalDistMap .instruments (convertSim I sp conv pre x0 Q x) ρ f =
      (additiveOracleRuntime (simOracle sp conv pre x0 H Q)).evalDistMap I x ρ f := by
  simp only [QuantumRuntime.evalDistMap, QuantumRuntime.jointPost, run_convertSim]
  rfl

/-- The conversion of a lossless program runs losslessly. -/
theorem lossless_run_convertSim (H : D → Y) {A : QReg}
    {x : QuantumComp L (qromSpec M X) W A} (hx : x.Lossless I) :
    ((additiveOracleRuntime H).run .instruments (convertSim I sp conv pre x0 Q x)).Lossless := by
  rw [run_convertSim]
  exact lossless_run_additiveOracleRuntime I hx _

end subst

/-! ## Keccak -/

section keccak

open HashSig Quantum.Qrom

variable {L : LocalSig.{u, v}} {W : QReg → Type w}

/-- **One call of the sponge's random oracle `keccakSim H Q`** by two calls of `H`, with `Q`
hardwired. -/
noncomputable def keccakSimCall (Q : Msg KeccakRate 9 → KeccakRate) (E : QReg) {A : QReg}
    (ℓ : A ≃ (qromSpec (Msg KeccakRate 9) KeccakRate).In () × E) :
    QuantumComp₂ LocalSig.instruments.{v} romSpec A (padReg (Msg KeccakRate 9) KeccakRate E)
      Unit :=
  simOracleCall rateSplit (Xmss.bitsEquiv 256) padPre 0 Q E ℓ

theorem runsAs_keccakSimCall (H : HashDomain → HashOutput) (Q : Msg KeccakRate 9 → KeccakRate)
    (E : QReg) {A : QReg} (ℓ : A ≃ (qromSpec (Msg KeccakRate 9) KeccakRate).In () × E) :
    RunsAs (additiveOracleRuntime H) (keccakSimCall.{v} Q E ℓ)
      (qromCallMap (keccakSim H Q) ℓ) :=
  runsAs_simOracleCall H ℓ

/-- **The conversion of a program over the sponge's random oracle** into one over `H`, given
`Q`. -/
noncomputable def convertKeccakSim (I : L.Interp) (Q : Msg KeccakRate 9 → KeccakRate)
    {A : QReg} (x : QuantumComp L (qromSpec (Msg KeccakRate 9) KeccakRate) W A) :
    QuantumComp LocalSig.instruments.{v} romSpec W A :=
  convertSim I rateSplit (Xmss.bitsEquiv 256) padPre 0 Q x

/-- **Against `H`, the conversion runs as the program against `keccakSim H Q`.** -/
theorem run_convertKeccakSim (I : L.Interp) (H : HashDomain → HashOutput)
    (Q : Msg KeccakRate 9 → KeccakRate) {A : QReg}
    (x : QuantumComp L (qromSpec (Msg KeccakRate 9) KeccakRate) W A) :
    (additiveOracleRuntime H).run .instruments (convertKeccakSim I Q x) =
      (additiveOracleRuntime (keccakSim H Q)).run I x :=
  run_convertSim I rateSplit (Xmss.bitsEquiv 256) padPre 0 Q H x

theorem evalDistMap_convertKeccakSim {β : Type*} [MeasurableSpace β] (I : L.Interp)
    (H : HashDomain → HashOutput) (Q : Msg KeccakRate 9 → KeccakRate) {A : QReg}
    (x : QuantumComp L (qromSpec (Msg KeccakRate 9) KeccakRate) W A) (ρ : SubState A)
    (f : (Σ u, W u) → β) :
    (additiveOracleRuntime H).evalDistMap .instruments (convertKeccakSim I Q x) ρ f =
      (additiveOracleRuntime (keccakSim H Q)).evalDistMap I x ρ f :=
  evalDistMap_convertSim I rateSplit (Xmss.bitsEquiv 256) padPre 0 Q H x ρ f

theorem isQueryBound_convertKeccakSim (I : L.Interp) (Q : Msg KeccakRate 9 → KeccakRate)
    {A : QReg} {x : QuantumComp L (qromSpec (Msg KeccakRate 9) KeccakRate) W A} {q : ℕ}
    (hx : x.IsTotalQueryBound q) :
    (convertKeccakSim I Q x).IsQueryBound fun _ ↦ 2 * q :=
  isQueryBound_convertSim I rateSplit (Xmss.bitsEquiv 256) padPre 0 Q hx

theorem isTotalQueryBound_convertKeccakSim (I : L.Interp) (Q : Msg KeccakRate 9 → KeccakRate)
    {A : QReg} {x : QuantumComp L (qromSpec (Msg KeccakRate 9) KeccakRate) W A} {q : ℕ}
    (hx : x.IsTotalQueryBound q) :
    (convertKeccakSim I Q x).IsTotalQueryBound (2 * q) :=
  isTotalQueryBound_convertSim I rateSplit (Xmss.bitsEquiv 256) padPre 0 Q hx

end keccak

end Quantum.Sponge

end
