module

public import Quantum.Sponge.Reads
public import Quantum.Sponge.Assembly.Prep

@[expose] public section

/-!
# The read log as a list of `SpongeRead`s

The log of `Quantum.Sponge.withReads` with the reads `spongeReadImpl` is a list of queries of
`spongeOSpec` with their answers; `toSpongeRead` reads each entry as a `SpongeRead`, and the
measured databases agree with the log exactly when they hold every read
(`agrees_iff_forall_heldBy`). `spongeEvalDistMap_withReads_le_heldBy` is
`spongeEvalDistMap_withReads_le` in these terms.
-/

open MeasureTheory OracleSpec OracleComp

namespace Quantum.Sponge

open Quantum

variable {X Z : Type}

/-- A log entry as a read with its answer. -/
def toSpongeRead : ((q : SpongeQuery X Z) × spongeOSpec X Z q) → SpongeRead X Z
  | ⟨.h z, a⟩ => .h z a
  | ⟨.k x, a⟩ => .k x a
  | ⟨.k' x, a⟩ => .k' x a

instance [DecidableEq X] [DecidableEq Z] (D : Dbs X Z) (e : SpongeRead X Z) :
    Decidable (e.HeldBy D) :=
  match e with
  | .h z a => inferInstanceAs (Decidable (D.h z = some a))
  | .k x a => inferInstanceAs (Decidable (D.k x = some a))
  | .k' x a => inferInstanceAs (Decidable (D.k' x = some a))

/-- The databases agree with a log exactly when they hold every read of it. -/
theorem agrees_iff_forall_heldBy (log : QueryLog (spongeOSpec X Z)) (D : DbReg X Z) :
    DbReg.Agrees log D ↔ ∀ e ∈ log.map toSpongeRead, e.HeldBy D.toDbs := by
  simp only [List.mem_map, DbReg.Agrees]
  constructor
  · rintro h _ ⟨⟨q, a⟩, he, rfl⟩
    have := h _ he
    cases q <;> exact this
  · intro h ⟨q, a⟩ he
    have := h _ ⟨_, he, rfl⟩
    cases q <;> exact this

variable [Fintype X] [DecidableEq X] [AddCommGroup X] [Nonempty X] [Fintype Z] [DecidableEq Z]
  [AddCommGroup Z] [Nonempty Z]

/-- **Classical reads of the sponge's compressed oracles are recorded**, with the log as a list of
`SpongeRead`s: every event `E` of the leaf, the result and the log has probability, with uniform
`(h, k, k')`, at most its probability jointly with the measured databases holding every read,
plus `2 (l_h / |X| + (l_k + l_k') / |Z|)`. -/
theorem spongeEvalDistMap_withReads_le_heldBy {W : QReg → Type} {A : QReg} {β : Type}
    (x : QuantumComp LocalSig.instruments.{0} (spongeSpec X Z) W A)
    (oa : (Σ u, W u) → OracleComp (spongeOSpec X Z) β) {lh lk lk' : ℕ}
    (hh : ∀ p, IsQueryBoundP (oa p) (fun q ↦ q.port = .h) lh)
    (hk : ∀ p, IsQueryBoundP (oa p) (fun q ↦ q.port = .k) lk)
    (hk' : ∀ p, IsQueryBoundP (oa p) (fun q ↦ q.port = .k') lk')
    (ρ : SubState A) (E : (Σ u, W u × β × QueryLog (spongeOSpec X Z)) → Prop)
    [DecidablePred E] :
    spongeEvalDistMap .instruments (withReads x (spongeReadImpl X Z) oa) ρ
        (fun _ q ↦ decide (E q)) {true} ≤
      jointLaw (spongeCompressedRuntime X Z) .instruments (withReads x (spongeReadImpl X Z) oa) ρ
          (fun q D ↦ decide (E q ∧ ∀ e ∈ q.2.2.2.map toSpongeRead, e.HeldBy D.toDbs)) {true} +
        ENNReal.ofReal (2 * (lh / Fintype.card X + (lk + lk') / Fintype.card Z)) := by
  have hf : (fun (q : Σ u, W u × β × QueryLog (spongeOSpec X Z)) (D : DbReg X Z) ↦
      decide (E q ∧ ∀ e ∈ q.2.2.2.map toSpongeRead, e.HeldBy D.toDbs)) =
      fun q D ↦ decide (E q ∧ DbReg.Agrees q.2.2.2 D) := by
    funext q D
    exact decide_eq_decide.mpr (and_congr_right' (agrees_iff_forall_heldBy _ _).symm)
  rw [hf]
  exact spongeEvalDistMap_withReads_le x oa hh hk hk' ρ E

end Quantum.Sponge

end
