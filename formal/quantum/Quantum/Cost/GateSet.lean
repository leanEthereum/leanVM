module

public import Quantum.Cost.Charge
public import VCVio.Quantum.Comp.Runtime
public import PolyFun.IPFunctor.Free.Substitution
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

/-!
# Gate sets, their interpretation, and calls from gates

A gate-set adversary is a program over a named signature `Γ.L` whose operations mean the
subinstruments `Γ.interp` and cost `Γ.gates` each. Interpreting the operations (`interpret`)
gives a program over the signature of instruments, the adversaries of the existing games, with
the same calls (`isChargeBound_interpret_iff`) and the same execution (`run_interpret`).

The cost model charges `Γ.gates o` per local operation and `k i` per call of port `i`
(`gateCharge Γ k`, an instance of `opCharge`). If every call of `i` costs at least `K` times its
port charge `p i`, a program within `N` gates makes calls of total port charge at most `N / K`
on every path (`calls_le_of_gates`); local gates only enter through being nonnegative, so this
holds for every gate set and every gate cost.

## Main definitions

* `GateSet`: named local operations, their meaning, and a gate count per operation.
* `interpret Γ`, `interpret₂ Γ`: each operation becomes the instrument it means.
* `opCharge δ k`, `portCharge p`, `gateCharge Γ k`: charges on commands.

## Main statements

* `run_interpret`, `lossless_interpret`, `isChargeBound_interpret_iff`: interpretation keeps
  the execution, losslessness and every port-charge bound.
* `calls_le_of_opCharge`, `calls_le_of_gates`: calls from a budget of the scaled cost.
* `le_closedForm`: a probability bounded by `bound q` and by `1` is within a closed form
  `((a q + b √q + c) / 2^64)²`, `1 ≤ a`, that holds for `q ≤ 2^64`, for every `q`.
-/

open IPFunctor
open scoped ENNReal

universe u v w u₁ v₁

namespace Quantum.Cost

/-- A gate set: named local operations, their meaning, and a gate count per operation. -/
structure GateSet where
  /-- The named local operations. -/
  L : LocalSig.{0, 0}
  /-- Their meaning, as dependent subinstruments. -/
  interp : L.Interp
  /-- The gate count of each operation. -/
  gates : ∀ ⦃A : QReg⦄, L.Op A → ℕ

variable {spec : QuantumOracleSpec.{u₁, v₁}} (Γ : GateSet) {X : QReg → Type w} {A : QReg}

/-! ## Interpretation -/

/-- Each local operation becomes the instrument it means; calls are unchanged. -/
noncomputable def interpretCmd :
    CommandSubstitution (QuantumComp.toIPFunctor Γ.L spec)
      (QuantumComp.toIPFunctor LocalSig.instruments.{0} spec)
  | _, .prim o => QuantumComp.primBind ⟨Γ.L.Outcome o, Γ.L.next o, Γ.interp o⟩ fun b ↦
      QuantumComp.pure ⟨ULift.up b, rfl⟩
  | _, .query i E ℓ => QuantumComp.queryBind i E ℓ fun r ↦ QuantumComp.pure ⟨ULift.up r, rfl⟩

/-- **The interpreted program**: each local operation replaced by the instrument it means. -/
noncomputable def interpret (x : QuantumComp Γ.L spec X A) :
    QuantumComp LocalSig.instruments.{0} spec X A :=
  IFreeM.substitute (interpretCmd Γ) x

/-- The interpreted fixed-register program, a program over instruments. -/
noncomputable def interpret₂ {B : QReg} {α : Type} (x : QuantumComp₂ Γ.L spec A B α) :
    QComp spec A B α :=
  interpret Γ x

theorem interpret_pure (x : X A) :
    interpret Γ (QuantumComp.pure (L := Γ.L) (spec := spec) x) = QuantumComp.pure x :=
  rfl

theorem interpret_primBind (o : Γ.L.Op A)
    (k : (b : Γ.L.Outcome o) → QuantumComp Γ.L spec X (Γ.L.next o b)) :
    interpret Γ (QuantumComp.primBind o k) =
      QuantumComp.primBind (L := LocalSig.instruments.{0})
        ⟨Γ.L.Outcome o, Γ.L.next o, Γ.interp o⟩ fun b ↦ interpret Γ (k b) :=
  rfl

theorem interpret_queryBind (i : spec.Port) (E : QReg) (ℓ : A ≃ spec.In i × E)
    (k : spec.Result i → QuantumComp Γ.L spec X (QReg.of (spec.Out i × E))) :
    interpret Γ (QuantumComp.queryBind i E ℓ k) =
      QuantumComp.queryBind i E ℓ fun r ↦ interpret Γ (k r) :=
  rfl

/-- **Fidelity**: running the interpreted program is running the gate program under
`Γ.interp`. -/
theorem run_interpret (R : QuantumRuntime spec) (x : QuantumComp Γ.L spec X A) :
    R.run LocalSig.Interp.instruments (interpret Γ x) = R.run Γ.interp x := by
  induction x using QuantumComp.inductionOn with
  | pure _ y => rw [interpret_pure, QuantumRuntime.run_pure, QuantumRuntime.run_pure]
  | primBind _ o k ih =>
    rw [interpret_primBind, QuantumRuntime.run_primBind, QuantumRuntime.run_primBind]
    exact congrArg _ (funext ih)
  | queryBind _ i E ℓ k ih =>
    rw [interpret_queryBind, QuantumRuntime.run_queryBind, QuantumRuntime.run_queryBind]
    exact congrArg _ (funext ih)

/-- Interpretation keeps losslessness. -/
theorem lossless_interpret {x : QuantumComp Γ.L spec X A} (hx : x.Lossless Γ.interp) :
    (interpret Γ x).Lossless LocalSig.Interp.instruments := by
  induction x using QuantumComp.inductionOn with
  | pure _ _ => trivial
  | primBind _ o k ih =>
    rw [QuantumComp.lossless_primBind_iff] at hx
    rw [interpret_primBind, QuantumComp.lossless_primBind_iff]
    exact ⟨hx.1, fun b ↦ ih b (hx.2 b)⟩
  | queryBind _ i E ℓ k ih =>
    rw [QuantumComp.lossless_queryBind_iff] at hx
    rw [interpret_queryBind, QuantumComp.lossless_queryBind_iff]
    exact fun r ↦ ih r (hx r)

/-! ## Charges -/

/-- A charge on commands: `δ o` per local operation `o`, `k i` per call of port `i`. -/
def opCharge {L : LocalSig.{u, v}} (δ : ∀ ⦃A : QReg⦄, L.Op A → ℕ) (k : spec.Port → ℕ)
    (A : QReg) : QuantumComp.Cmd L spec A → ℕ
  | .prim o => δ o
  | .query i _ _ => k i

/-- Port charges: a call of `i` costs `p i`, a local operation nothing. -/
abbrev portCharge {L : LocalSig.{u, v}} (p : spec.Port → ℕ) :
    (A : QReg) → QuantumComp.Cmd L spec A → ℕ :=
  opCharge (fun _ _ ↦ 0) p

/-- **The cost model**: `Γ.gates o` per local operation, `k i` per call of port `i`. -/
abbrev gateCharge (k : spec.Port → ℕ) : (A : QReg) → QuantumComp.Cmd Γ.L spec A → ℕ :=
  opCharge Γ.gates k

/-- **Interpretation keeps every port-charge bound**: the interpreted program has the same
calls, and one instrument per local operation. -/
theorem isChargeBound_interpret_iff (p : spec.Port → ℕ) (x : QuantumComp Γ.L spec X A)
    (n : ℕ) :
    IFreeM.IsChargeBound (interpret Γ x) (portCharge p) n ↔
      IFreeM.IsChargeBound x (portCharge p) n := by
  induction x using QuantumComp.inductionOn generalizing n with
  | pure _ _ => exact ⟨fun _ ↦ trivial, fun _ ↦ trivial⟩
  | primBind A' o k ih =>
    rw [interpret_primBind]
    exact (IFreeM.isChargeBound_liftBind_iff (P := QuantumComp.toIPFunctor _ spec)
      (c := portCharge p)
      (QuantumComp.Cmd.prim (L := LocalSig.instruments.{0}) (spec := spec) (A := A')
        ⟨Γ.L.Outcome o, Γ.L.next o, Γ.interp o⟩) _ n).trans
      ((and_congr Iff.rfl (forall_congr' fun (b : ULift.{v₁} (Γ.L.Outcome o)) ↦
        ih b.down _)).trans
        (IFreeM.isChargeBound_liftBind_iff (P := QuantumComp.toIPFunctor Γ.L spec)
          (c := portCharge p)
          (QuantumComp.Cmd.prim o) (QuantumComp.onDown k) n).symm)
  | queryBind A' i E ℓ k ih =>
    rw [interpret_queryBind]
    exact (IFreeM.isChargeBound_liftBind_iff (P := QuantumComp.toIPFunctor _ spec)
      (c := portCharge p)
      (QuantumComp.Cmd.query (L := LocalSig.instruments.{0}) (A := A') i E ℓ) _ n).trans
      ((and_congr Iff.rfl (forall_congr' fun (r : ULift.{0} (spec.Result i)) ↦
        ih r.down _)).trans
        (IFreeM.isChargeBound_liftBind_iff (P := QuantumComp.toIPFunctor Γ.L spec)
          (c := portCharge p)
          (QuantumComp.Cmd.query i E ℓ) (QuantumComp.onDown k) n).symm)

/-- **Calls from a scaled cost.** If each call of `i` costs at least `K · p i` under `opCharge δ
k`, a program within `N` makes calls of total `p`-charge at most `N / K` on every path, for
every charge `δ` of the local operations. -/
theorem calls_le_of_opCharge {L : LocalSig.{u, v}} {δ : ∀ ⦃A : QReg⦄, L.Op A → ℕ}
    {k p : spec.Port → ℕ} {K N : ℕ} (hK : 0 < K) (hp : ∀ i, K * p i ≤ k i)
    {x : QuantumComp L spec X A} (h : IFreeM.IsChargeBound x (opCharge δ k) N) :
    IFreeM.IsChargeBound x (portCharge p) (N / K) := by
  refine h.of_scaled_le hK fun _ c ↦ ?_
  cases c with
  | prim o => exact Nat.zero_le _
  | query i _ _ => exact hp i

/-- **Calls from gates**: if each call of `i` costs at least `GK · p i` gates, a program within
`G` gates makes calls of total `p`-charge at most `G / GK` on every path. -/
theorem calls_le_of_gates {gk p : spec.Port → ℕ} {GK G : ℕ} (hGK : 0 < GK)
    (hp : ∀ i, GK * p i ≤ gk i) {x : QuantumComp Γ.L spec X A}
    (h : IFreeM.IsChargeBound x (gateCharge Γ gk) G) :
    IFreeM.IsChargeBound x (portCharge p) (G / GK) :=
  calls_le_of_opCharge hGK hp h

/-! ## Closed forms at every budget -/

/-- **A closed form at every budget.** A probability `w ≤ 1` with `w ≤ bound q`, where
`bound q ≤ ((a q + b √q + c) / 2^64)²` for `q ≤ 2^64` and `1 ≤ a`, is within the closed form for
every `q`: above `2^64` it is at least `1`. -/
theorem le_closedForm {w : ℝ≥0∞} {bound : ℕ → ℝ≥0∞} {a b c : ℝ} {q : ℕ} (ha : 1 ≤ a)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hw1 : w ≤ 1) (hw : w ≤ bound q)
    (hcl : q ≤ 2 ^ 64 → bound q ≤ ENNReal.ofReal (((a * q + b * √(q : ℝ) + c) / 2 ^ 64) ^ 2)) :
    w ≤ ENNReal.ofReal (((a * q + b * √(q : ℝ) + c) / 2 ^ 64) ^ 2) := by
  by_cases hq : q ≤ 2 ^ 64
  · exact hw.trans (hcl hq)
  · refine hw1.trans (ENNReal.one_le_ofReal.2 (one_le_pow₀ ?_))
    have hq' : (2 : ℝ) ^ 64 ≤ q := by exact_mod_cast (not_le.mp hq).le
    have hbq : 0 ≤ b * √(q : ℝ) := mul_nonneg hb (Real.sqrt_nonneg _)
    rw [le_div_iff₀ (by positivity)]
    nlinarith

end Quantum.Cost

end
