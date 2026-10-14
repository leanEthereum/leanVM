import Whir.AnchoredFiatShamirSecurityROM
import Whir.AnchoredByteStreamPrepared

/-! Security ledger for the proved byte-stream ROM anchor plus independent
causal opening experiment. No unconditional native BLAKE2s bound is asserted;
the deployed verifier body and the primitive-to-ROM gap are separate obligations. -/
namespace Whir.AnchoredFiatShamirSecurityBudget
open Concrete Protocol CausalGame ParameterBounds CommitmentAnchor
open AnchoredFiatShamirSecurity AnchoredFiatShamirSecurityROM FiatShamirGame
open RawOracleCoupling.Concrete TypedOracleCompiler
open DuplexFraming DuplexModeGame
noncomputable local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- Actual derived composition: adaptive immutable-anchor ambiguity plus the
anchor-inclusive causal opening term, not a prospective native allocation cap. -/
def romLedger (attempts : Nat) : ℚ := (attempts : ℚ)/2^124 + (1 : ℚ)/2^73

theorem byte_stream_security_ledger {p : Profile} {Key : Type}
    [Fintype Key] [DecidableEq Key] (policy : Policy p Key) (n : Nat)
    (select : TableSelector policy n) (advertised : BlockOracle p Key → E)
    (opening : BlockOracle p Key → Array Claim) (strategy : BlockOracle p Key → Strategy)
    (opening_cap : ∀ table, (opening table).size+1 ≤ 2^64) :
    Soundness.uniformProb (Finset.univ.filter
      (TableFailure policy n select advertised opening strategy)) ≤ romLedger n :=
  block_table_unique_opening_probability policy n select advertised opening strategy opening_cap

/-- Resource charges use ceil(24*logN/32) distinct output blocks per attempt.
The numerical statement is attached to the actual proved experiment. -/
theorem byte_stream_security_numeric {p : Profile} {Key : Type}
    [Fintype Key] [DecidableEq Key] (policy : Policy p Key) (n Q : Nat)
    (blockBudget : n * AnchoredFiatShamirSecurityCodec.blockCount (config p).logN ≤ Q)
    (compression : Q ≤ 2^60)
    (select : TableSelector policy n) (advertised : BlockOracle p Key → E)
    (opening : BlockOracle p Key → Array Claim) (strategy : BlockOracle p Key → Strategy)
    (opening_cap : ∀ table, (opening table).size+1 ≤ 2^64) :
    Soundness.uniformProb (Finset.univ.filter
      (TableFailure policy n select advertised opening strategy)) ≤ (1 : ℚ)/2^63 := by
  exact (block_table_unique_opening_numeric policy n Q blockBudget compression select advertised
    opening strategy opening_cap).trans (by norm_num)

abbrev RawSelector {p : Profile} {Q : Nat} {iv : Digest32} {accept : FramedHistory → Bool}
    {R : Type} {n : Nat} (policy : AnchoredByteStreamPrepared.Policy p Q iv accept)
    (source : Sampling (RawKey Q) (fun _ => Digest32) R n) :=
  (table : RawKey Q → Digest32) → Option {e : Entry p (AnchoredByteStreamPrepared.PointPacket p Q iv accept) //
    e ∈ (AnchoredByteStreamPrepared.execution policy source table).1.2}

noncomputable def RawFailure {p : Profile} {Q : Nat} {iv : Digest32}
    {accept : FramedHistory → Bool} {R : Type} {n : Nat}
    (policy : AnchoredByteStreamPrepared.Policy p Q iv accept)
    (source : Sampling (RawKey Q) (fun _ => Digest32) R n)
    (select : RawSelector policy source) (advertised : (RawKey Q → Digest32) → E)
    (opening : (RawKey Q → Digest32) → Array Claim)
    (strategy : (RawKey Q → Digest32) → Strategy)
    (sample : (RawKey Q → Digest32) × Tape (config p)) : Prop :=
  match select sample.1 with
  | none => False
  | some e => openingFailure p (chosenCommitment e.val (advertised sample.1))
      (opening sample.1) (strategy sample.1) sample.2

/-- Actual adaptive raw-byte source grouping and immutable selection, followed
by the proved independent causal opening experiment. Every public raw oracle
answer may be inspected by the final selector, with no observer restriction. -/
theorem raw_security_ledger {p : Profile} {Q : Nat} {iv : Digest32}
    {accept : FramedHistory → Bool} {R : Type} {n : Nat}
    (policy : AnchoredByteStreamPrepared.Policy p Q iv accept)
    (source : Sampling (RawKey Q) (fun _ => Digest32) R n)
    (select : RawSelector policy source) (advertised : (RawKey Q → Digest32) → E)
    (opening : (RawKey Q → Digest32) → Array Claim)
    (strategy : (RawKey Q → Digest32) → Strategy)
    (opening_cap : ∀ table, (opening table).size+1 ≤ 2^64) :
    Soundness.uniformProb (Finset.univ.filter
      (RawFailure policy source select advertised opening strategy)) ≤ romLedger n := by
  classical
  apply RingMapBatching.conditional_error
    (fun table : RawKey Q → Digest32 =>
      Dirty (AnchoredByteStreamPrepared.execution policy source table).1.2)
    _ _ _ (by positivity)
    (AnchoredByteStreamPrepared.prepared_raw_table_ambiguity policy source)
  intro table clean
  cases chosen : select table with
  | none => simp [RawFailure, chosen, Soundness.uniformProb]
  | some e =>
    have sep : ¬ Ambiguous p e.val.commitment.lanes e.val.commitment.root
        e.val.commitment.point := fun bad => clean ⟨e.val,e.property,bad⟩
    simpa only [RawFailure, chosen] using
      (unique_opening_probability p (chosenCommitment e.val (advertised table))
        sep (opening table) (strategy table)).trans
        (production_interactive p _ (opening_cap table))

private theorem profile_blocks : ∀ p : Profile,
    1 ≤ AnchoredFiatShamirSecurityCodec.blockCount (config p).logN := by
  decide +kernel

theorem raw_security_numeric {p : Profile} {Q : Nat} {iv : Digest32}
    {accept : FramedHistory → Bool} {R : Type} {n : Nat}
    (policy : AnchoredByteStreamPrepared.Policy p Q iv accept)
    (source : Sampling (RawKey Q) (fun _ => Digest32) R n)
    (blockBudget : n * AnchoredFiatShamirSecurityCodec.blockCount (config p).logN ≤ Q)
    (compression : Q ≤ 2^60)
    (select : RawSelector policy source) (advertised : (RawKey Q → Digest32) → E)
    (opening : (RawKey Q → Digest32) → Array Claim)
    (strategy : (RawKey Q → Digest32) → Strategy)
    (opening_cap : ∀ table, (opening table).size+1 ≤ 2^64) :
    Soundness.uniformProb (Finset.univ.filter
      (RawFailure policy source select advertised opening strategy)) ≤ (1 : ℚ)/2^63 := by
  have attempts : n ≤ 2^60 := calc
    n = n*1 := by simp
    _ ≤ n*AnchoredFiatShamirSecurityCodec.blockCount (config p).logN :=
      Nat.mul_le_mul_left n (profile_blocks p)
    _ ≤ Q := blockBudget
    _ ≤ 2^60 := compression
  apply (raw_security_ledger policy source select advertised opening strategy opening_cap).trans
  unfold romLedger
  have h : (n : ℚ) ≤ 2^60 := by exact_mod_cast attempts
  have anchor := div_le_div_of_nonneg_right h (by positivity : (0 : ℚ) ≤ 2^124)
  calc
    _ ≤ (2^60 : ℚ)/2^124 + (1 : ℚ)/2^73 := add_le_add anchor le_rfl
    _ ≤ _ := by norm_num


/-- Chronology and counting alone still permit a root chosen after an answer.
The physical source integration must use its header decoder and frozen registry,
not infer pre-point preparation from the unrefined Source datatype. -/
def lateRoot {cap : Nat} (query : DuplexModeGame.Query) :
    WHIRSourceChronology.Source cap Unit :=
  .ask query (fun answer => .commit answer (.done ()))

theorem lateRoot_before {cap : Nat} (query : DuplexModeGame.Query) :
    WHIRSourceChronology.recover (lateRoot (cap := cap) query) [] =
      ⟨[],some query,none⟩ := rfl

theorem lateRoot_after {cap : Nat} (query : DuplexModeGame.Query) (answer : Digest32) :
    (WHIRSourceChronology.recover (lateRoot (cap := cap) query) [⟨query,answer⟩]).events =
      [.answer query answer,.commit answer] := rfl

theorem lateRoot_counted {cap : Nat} (query : DuplexModeGame.Query) :
    WHIRSourceChronology.Counts query.cost (lateRoot (cap := cap) query) := by
  simp [lateRoot, WHIRSourceChronology.Counts]

/- The byte codec and fresh raw history grouping concern actual 552 output
bytes. The opening term above is an independent causal opening tape, not the
native byte-stream body. Body challenge transport, accepted native arithmetic
and the BLAKE2s primitive gap are not proved by this ledger. Physical frame
absorption and all extra compression nodes must be charged by that composition. -/

end Whir.AnchoredFiatShamirSecurityBudget

#print axioms Whir.AnchoredFiatShamirSecurityBudget.byte_stream_security_ledger
#print axioms Whir.AnchoredFiatShamirSecurityBudget.byte_stream_security_numeric
#print axioms Whir.AnchoredFiatShamirSecurityBudget.lateRoot_counted
#print axioms Whir.AnchoredFiatShamirSecurityBudget.raw_security_ledger
#print axioms Whir.AnchoredFiatShamirSecurityBudget.raw_security_numeric
