import Whir.PCSBCSChallengeOracleSource

/-! Atomic virtual-packet sampling on FIRST physical disclosure. All later
projections are cache hits, even after partial disclosure, abort or restoration.
Off-image observer and simulator RO requests remain ordinary memoized requests.
No ancestor warming multiplies the aggregate physical query cap. -/
set_option autoImplicit false
set_option maxRecDepth 100000
namespace Whir.PCSBCSChallengeOracle
open Concrete FiatShamirGame TypedOracleCompiler RawOracleCoupling

/-- Finite restriction of the literal key encoder. No raw keys are dropped:
keys not recognized as packet blocks occupy the garbage summand. -/
noncomputable def partitionOfInjection {Raw Packet : Type} {Block : Packet → Type}
    (encode : Sigma Block → Raw) (injective : Function.Injective encode) :
    Partition Raw Packet Block := by
  classical
  exact
    { encode := encode
      recognize := fun raw => if h : ∃ b, encode b = raw then some (Classical.choose h) else none
      recognize_encode := by
        intro b
        have hasPreimage : ∃ b', encode b' = encode b := ⟨b,rfl⟩
        rw [dite_eq_left hasPreimage]
        apply congrArg some
        exact injective (Classical.choose_spec (show ∃ b', encode b' = encode b from ⟨b,rfl⟩))
      encode_recognize := by
        intro raw b same
        split at same
        · rename_i h
          have eq := Option.some.inj same
          rw [← eq]
          exact Classical.choose_spec h
        · contradiction }

namespace Atomic
variable {Raw Packet : Type} {Block : Packet → Type}
  (part : Partition Raw Packet Block)

/-- Sampling the complete virtual packet is PRIVATE; the continuation receives
only the one requested 256-bit physical block, including its otherwise unused
bytes. A replay never re-enters this draw in the memoized interpreter. -/
def request (raw : Raw) : Sampling part.Key (part.Answer (D := Digest32)) Digest32 1 :=
  match h : part.recognize raw with
  | some b => .draw (.inl b.1) (fun full => .ret (full b.2))
  | none => .draw (.inr ⟨raw,h⟩) (fun answer => .ret answer)

theorem eval_request (table : (k : part.Key) → part.Answer (D := Digest32) k) (raw : Raw) :
    Sampling.eval table (request part raw) = part.join table raw := by
  unfold request Partition.join
  split
  · rename_i b hit
    simp only [Sampling.eval]
    split
    · rename_i b' hit'
      have same := Option.some.inj (hit.symm.trans hit')
      cases same
      rfl
    · rename_i missed
      have impossible := hit.symm.trans missed
      cases impossible
  · rename_i missed
    simp only [Sampling.eval]
    split
    · rename_i b hit
      have impossible := missed.symm.trans hit
      cases impossible
    · rfl

def program {R : Type} {n : Nat} : Sampling Raw (fun _ => Digest32) R n →
    Sampling part.Key (part.Answer (D := Digest32)) R n
  | .ret r => .ret r
  | .draw raw next => Sampling.pad (by omega)
      (Sampling.bind (request part raw) (fun answer => program (next answer)))

theorem eval_program {R : Type} {n : Nat}
    (table : (k : part.Key) → part.Answer (D := Digest32) k)
    (p : Sampling Raw (fun _ => Digest32) R n) :
    Sampling.eval table (program part p) = Sampling.eval (part.join table) p := by
  induction p with
  | ret r => rfl
  | draw raw next ih => simp [program, eval_request, Sampling.eval, ih]

open Classical in
/-- Exact game mapping for every adaptive program and payoff. The same outer
cache memoizes whole packets and arbitrary off-image observer requests. -/
theorem table_eq_atomic_packets [Fintype Raw] [Fintype Packet]
    [∀ p, Fintype (Block p)] [DecidableEq Packet]
    {R : Type} {n : Nat} (p : Sampling Raw (fun _ => Digest32) R n) (payoff : R → ℚ) :
    average (fun table : Raw → Digest32 => payoff (Sampling.eval table p)) =
      Sampling.expectation (fun result => payoff result.1)
        (RawOracleCoupling.memo (program part p) (fun _ => none)) := by
  classical
  rw [← RawOracleCoupling.empty_table_eq_memo]
  simp only [eval_program]
  have h := RawOracleCoupling.average_equiv part.tableEquiv
    (fun table => payoff (Sampling.eval (part.join table) p))
  simpa only [Partition.tableEquiv, Equiv.coe_fn_mk, Partition.join_split] using h

/-- Actual number of new virtual packets is at most the aggregate physical RO
request cap n. Sampling an entire packet does not charge a per-round n again. -/
theorem allocation_cap [DecidableEq Packet] [DecidableEq Raw]
    {R : Type} {n : Nat} (p : Sampling Raw (fun _ => Digest32) R n)
    {trace : List (Sigma (part.Answer (D := Digest32)))} {result : R × _}
    (run : Sampling.Runs (RawOracleCoupling.memo (program part p) (fun _ => none)) trace result) :
    trace.length ≤ n := run.length_le

end Atomic

/-- A finite family of actual source packets gives the literal injective encoder
required above. Distinct packet identifiers must name distinct prover histories;
this is an identity-of-keys condition, not an entropy or small-loss assumption. -/
theorem source_family_encode_injective {P : Type} {p : ParameterBounds.Profile}
    {Q : Nat} {iv : Digest32} {entry : FramedHistory}
    (coord : P → CausalProbability.Coordinate (ParameterBounds.config p))
    (packets : ∀ a, SourcePacket p Q iv entry (coord a))
    (unique : Function.Injective (fun a => (packets a).messages)) :
    Function.Injective (fun b : Sigma (fun a => Fin (blocks (PCSBCSRounds.rawWidth (coord a)))) =>
      (packets b.1).key b.2) := by
  intro a b same
  have facts := SourcePacket.distinct_history_keys (packets a.1) (packets b.1) a.2 b.2 same
  have identity := unique facts.1
  cases a with
  | mk a i =>
    cases b with
    | mk b j =>
      dsimp only at identity
      subst b
      exact congrArg (Sigma.mk a) (Fin.ext facts.2)

noncomputable def sourceFamilyPartition {P : Type} {p : ParameterBounds.Profile}
    {Q : Nat} {iv : Digest32} {entry : FramedHistory}
    (coord : P → CausalProbability.Coordinate (ParameterBounds.config p))
    (packets : ∀ a, SourcePacket p Q iv entry (coord a))
    (unique : Function.Injective (fun a => (packets a).messages)) :
    Partition (PublicCompressionCouplingMixed.Key Q) P
      (fun a => Fin (blocks (PCSBCSRounds.rawWidth (coord a)))) :=
  partitionOfInjection
    (fun b => .inr ((packets b.1).key b.2))
    (fun _ _ same => source_family_encode_injective coord packets unique (Sum.inr.inj same))

open Classical in
/-- Conditional first-disclosure kernel, with the ENTIRE past represented by
an arbitrary fixed shared cache. All continuation branches (including early
abort) receive projections only after the full packet has been allocated. -/
theorem first_disclosure_kernel {Packet : Type} [DecidableEq Packet]
    {Raw : Type} [DecidableEq Raw] {Block : Packet → Type}
    [∀ p, Fintype (Block p)] (part : Partition Raw Packet Block)
    {R : Type} {n : Nat} (packet : Packet)
    (cache : TypedFiatShamirGame.Cache part.Key (part.Answer (D := Digest32)))
    (fresh : cache (.inl packet) = none)
    (next : (Block packet → Digest32) → Sampling part.Key (part.Answer (D := Digest32)) R n)
    (payoff : R × TypedFiatShamirGame.Cache part.Key (part.Answer (D := Digest32)) → ℚ) :
    Sampling.expectation payoff (RawOracleCoupling.memo (.draw (.inl packet) next) cache) =
      average (fun full : Block packet → Digest32 =>
        Sampling.expectation payoff (RawOracleCoupling.memo (next full)
          (TypedFiatShamirGame.put cache (.inl packet) full))) := by
  classical
  simp only [RawOracleCoupling.memo, fresh, Sampling.expectation]

private theorem average_fintype {A : Type} (old new : Fintype A) (f : A → ℚ) :
    @average A old f = @average A new f := by
  cases Subsingleton.elim old new
  rfl

open Classical in
private theorem average_indicator_cast {A : Type} [Fintype A] (P : A → Prop) :
    ((average (fun a : A => if P a then (1:ℚ) else 0)) : ℝ) =
      SamplingProbability.probability P := by
  simp [average, SamplingProbability.probability, Finset.sum_boole, Fintype.card_subtype]

open Classical in
/-- Exact conditional uniform Raw distribution on the first disclosure of an
atomic source packet. A partially disclosed packet is already a cache hit and
is therefore ineligible for this theorem. The fixed cache may encode any past
public/primitive/Merkle observations and any earlier restored computations. -/
theorem first_disclosure_grouped_uniform {Packet : Type} [DecidableEq Packet]
    {RawKey : Type} [DecidableEq RawKey] {c : Protocol.Config}
    (coord : Packet → CausalProbability.Coordinate c)
    (part : Partition RawKey Packet (fun a => Fin (blocks (PCSBCSRounds.rawWidth (coord a)))))
    (packet : Packet)
    (cache : TypedFiatShamirGame.Cache part.Key (part.Answer (D := Digest32)))
    (fresh : cache (.inl packet) = none) (P : PCSBCSRounds.Raw (coord packet) → Prop) :
    ((Sampling.expectation
      (fun result : PCSBCSRounds.Raw (coord packet) ×
        TypedFiatShamirGame.Cache part.Key (part.Answer (D := Digest32)) =>
        if P result.1 then (1:ℚ) else 0)
      (RawOracleCoupling.memo
        (.draw (.inl packet) (fun full => .ret (n := 0) (grouped (coord packet) full))) cache)) : ℝ) =
      SamplingProbability.probability P := by
  simp only [RawOracleCoupling.memo, fresh, Sampling.expectation]
  rw [average_fintype _ (inferInstance : Fintype (Fin
    (blocks (PCSBCSRounds.rawWidth (coord packet))) → Digest32))
      (fun full => if P (grouped (coord packet) full) then (1:ℚ) else 0)]
  rw [average_indicator_cast, grouped_uniform]

open Classical in
/-- Pointwise lowering of the actual pinned ideal simulator and all its public
requests to the atomic challenge experiment. The finite mixed table contains
both independent simulator fallback seed answers and literal source RO answers.
The existing compiler charges at most Q draws under the SAME Counts Q cap. -/
theorem actual_ideal_eq_atomic_packets {Packet : Type} [Fintype Packet] [DecidableEq Packet]
    {Block : Packet → Type} [∀ p, Fintype (Block p)] {Q : Nat}
    (part : Partition (PublicCompressionCouplingMixed.Key Q) Packet Block)
    {R : Type} (iv : Digest32) (p : DuplexModeGame.Program R)
    (counted : DuplexModeGame.Counts Q p) (payoff : DuplexModeGame.View R → ℚ) :
    letI : DecidableEq (PublicCompressionCouplingMixed.Key Q) := Classical.decEq _
    letI := PublicCompressionCouplingMixed.mixedKeyFintype Q
    average (fun table : PublicCompressionCouplingMixed.Key Q → Digest32 =>
      payoff (DuplexModeGame.runIdeal (DuplexPublicSimulator.simulator Q)
        (fun k => table (.inr k)) iv
        ⟨(fun n => table (.inl n)),[]⟩ p Q (by rfl) counted).view) =
      Sampling.expectation (fun result => payoff result.1)
        (RawOracleCoupling.memo
          (Atomic.program part (PublicCompressionCouplingMixed.compile Q iv [] p Q (by rfl) counted))
          (fun _ => none)) := by
  classical
  let : DecidableEq (PublicCompressionCouplingMixed.Key Q) := Classical.decEq _
  let := PublicCompressionCouplingMixed.mixedKeyFintype Q
  have pointwise (table : PublicCompressionCouplingMixed.Key Q → Digest32) :=
    PublicCompressionCouplingMixed.compile_actual Q (fun n => table (.inl n))
      (fun k => table (.inr k)) iv [] p Q (by rfl) counted
  have oracle_identity (table : PublicCompressionCouplingMixed.Key Q → Digest32) :
      PublicCompressionCouplingMixed.oracle (fun n => table (.inl n)) (fun k => table (.inr k)) =
        table := by funext k; cases k <;> rfl
  simp only [oracle_identity] at pointwise
  simp_rw [← pointwise]
  exact Atomic.table_eq_atomic_packets part _ payoff

open Classical in
theorem actual_ideal_allocation_cap {Packet : Type} [DecidableEq Packet]
    {Block : Packet → Type} {Q : Nat}
    (part : Partition (PublicCompressionCouplingMixed.Key Q) Packet Block)
    {R : Type} (iv : Digest32) (p : DuplexModeGame.Program R)
    (counted : DuplexModeGame.Counts Q p) {trace result}
    (execution : Sampling.Runs
      (RawOracleCoupling.memo
        (Atomic.program part (PublicCompressionCouplingMixed.compile Q iv [] p Q (by rfl) counted))
        (fun _ => none)) trace result) : trace.length ≤ Q := execution.length_le

#print axioms first_disclosure_grouped_uniform
#print axioms actual_ideal_eq_atomic_packets
#print axioms actual_ideal_allocation_cap
#print axioms Atomic.table_eq_atomic_packets
#print axioms Atomic.allocation_cap
#print axioms source_family_encode_injective
end Whir.PCSBCSChallengeOracle
