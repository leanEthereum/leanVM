/-
  LeanVM.Protocol.EndToEnd.Front.FlockSetup

  The Flock phase of the leanISA instance as the specifications of the verifier program read it:
  the generic Flock argument's parameters on the instance's region, the statement a candidate is
  judged at, and the start of the argument's relations.
-/

module

public import LeanVM.Protocol.EndToEnd.Front.PubPhase
public import LeanVM.Protocol.EndToEnd.Front.FlockSkip
public import LeanVM.Protocol.EndToEnd.Front.FlockArk
public import LeanVM.Protocol.ToArkLib.Flock.Security
public import LeanVM.Protocol.FlockFields

/-!
# The Flock phase on the leanISA instance

The deployed Flock phase (`flockPhase`, `LeanVM.Protocol.Flock`) is the generic Flock argument
`Flock.flock` at `flockParams k` (`k = τ_BLAKE2S`, the region's `kBatch`) on the region `QFLOCK`
of the leanISA instance `leanIsaInstance F prog s`, with the region's R1CS `F.r1cs`, the bit tables
`FlockPhase.bits` and the side condition `FlockPhase.side` (the column claims received hold). Its
components' securities are the facts the program's specification uses (`FlockArk`).

A candidate `q` is judged at the *true statement* `flockStmt input (toI q)`: the public input,
with received claims all true of the candidate (`trueClaim`), so that the side condition holds
(`side_flockStmt`) and the program's own claims, carried as the conjunct `ColumnClaimsHold`, take
their place. The ArkLib argument's relations read the received claims only through the side
condition, so this is the statement whose doom the program's doom implies.

`not_pointRel_zero`: a candidate violating the Flock predicate is outside the argument's first
relation, by the fixed coordinates' `F_2`-independence (`fixedWeights_independent`), as in
`Flock.flockSecurity`.
-/

namespace LeanVM.Protocol.EndToEnd.Front

open LeanVM.Parameters LeanVM.Protocol.Flock CompPoly CMlPolynomialEval
open scoped ENNReal NNReal

@[expose] public section

section Setup

variable (F : FlockSpec) (prog : LeanVM.Semantics.Program) (s : LeanIsa.Sizes)

/-- The leanISA instance. -/
abbrev fI : M3Instance := leanIsaInstance F prog s

/-- Its Flock region, `QFLOCK` with `kBatch = τ_BLAKE2S`. -/
abbrev fR : FlockRegion (fI F prog s).toShape := LeanIsa.flockRegion prog s F

/-- The Flock argument's parameters on the region. -/
abbrev fP : Params E := flockParams (fR F prog s).kBatch

/-- The region's R1CS. -/
abbrev fC : BlockR1CS E ((fP F prog s).s + (fP F prog s).m) := (fR F prog s).r1cs

/-- The region's bit tables. -/
abbrev fz : (∀ i, TheOracle (fI F prog s) i) → Fin (2 ^ (fP F prog s).s) →
    CMlPolynomialEval E ((fP F prog s).m + (fP F prog s).κ) :=
  FlockPhase.bits (fR F prog s)

/-- The side condition: the received claims hold. -/
abbrev fside : (fI F prog s).Stmt × PubOut (fI F prog s) →
    (∀ i, TheOracle (fI F prog s) i) → Prop :=
  FlockPhase.side

/-- The true statement of a candidate: the public input and received claims true of it. -/
def flockStmt (input : LeanVM.Semantics.PublicInput) (q : Column (fI F prog s).μ) :
    (fI F prog s).Stmt × PubOut (fI F prog s) :=
  (input, ⟨Vector.replicate _ (trueClaim F prog s q)⟩)

/-- The side condition holds at the true statement. -/
theorem side_flockStmt (input : LeanVM.Semantics.PublicInput) (q : Column (fI F prog s).μ) :
    fside F prog s (flockStmt F prog s input q) (stackOracle F prog s q) := by
  intro c hc
  simp only [flockStmt, Vector.toList_replicate, List.mem_replicate] at hc
  rw [hc.2]
  rfl

/-- The Flock predicate is the region's batch of R1CS blocks on the stack's bit tables. -/
theorem aux_iff (q : Column (fI F prog s).μ) :
    (fI F prog s).aux q ↔
      BlockR1CS.BatchHolds (fC F prog s) (fP F prog s).cpos
        (fz F prog s (stackOracle F prog s q)) := by
  constructor
  · intro h
    exact h (fR F prog s) rfl
  · intro h r hr
    cases hr
    exact h

/-- **The argument's first relation needs the Flock predicate**: a candidate violating it is
outside `pointRel 0` at its true statement (the residuals vanish on the fixed coordinates only
if they vanish, by `fixedWeights_independent`). -/
theorem not_pointRel_zero (input : LeanVM.Semantics.PublicInput) (q : Column (fI F prog s).μ)
    (hq : ¬ (fI F prog s).aux q) :
    (((flockStmt F prog s input q, (#v[] : Vector E 0)), stackOracle F prog s q), ()) ∉
      pointRel (fP F prog s) (fC F prog s) (fz F prog s) (fside F prog s) 0 := by
  intro h
  apply hq
  rw [aux_iff]
  exact (Flock.batchHolds_iff _ _ _).mpr ⟨fun i u ↦
    eq_zero_of_restrictedZero_fixed (fP F prog s) (fun c hc hs ↦ fixedWeights_independent c hc hs)
      _ (isBool_errTable _ (fun i u ↦ bitTable_isBool _ i u) i) (h.2.1 i) u, h.2.2⟩

end Setup

end
end LeanVM.Protocol.EndToEnd.Front
