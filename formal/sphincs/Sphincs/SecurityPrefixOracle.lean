import Sphincs.Statement
import Sphincs.RandomizedSupport
import Sphincs.SecurityTreeWitness
import Sphincs.SecuritySignatureWitness
import Sphincs.SecurityDomains
import Sphincs.Uniform
import SphincsBase.Proof.Chains.PartialChainEndpoint

/-!
An exact candidate-byte oracle split for one hidden WOTS prefix. Adapted from leanVM's
OtsPrefixOracle; the candidate has 64 chains and three hash steps per chain. Outside queries
and the unused high 128 output bits remain explicit, so erasure cannot silently discard
adversary-visible information.
-/

open OracleComp OracleSpec

namespace Sphincs.Security.Prefix
open Concrete

structure Segment where
  parameter : PublicParameter
  lay : Layer
  tree : TreeIndex
  leaf : LeafIndex
  chainIdx : ChainIndex
  digit : Digit

abbrev Query (segment : Segment) := Fin segment.digit.val × Digest
abbrev High := BitVec (hashOutputBits - digestBits)

def step (segment : Segment) (index : Fin segment.digit.val) : ChainStep :=
  ⟨index.val, by have := index.isLt; have := segment.digit.isLt; omega⟩

def input (segment : Segment) (query : Query segment) : HashInput :=
  tweakableHashInput segment.parameter
    (.chain segment.lay segment.tree segment.leaf segment.chainIdx (step segment query.1))
    (bytesLE 16 query.2)

theorem input_injective (segment : Segment) : Function.Injective (input segment) := by
  intro left right heq
  have hstep := (Chain.chain_input_address_injective segment.parameter segment.lay segment.tree
    segment.leaf left.2 right.2 heq).2
  have hpayload := (tweakableInput_injective heq).2.2
  exact Prod.ext (Fin.ext (congrArg (fun position : ChainStep => position.val) hstep))
    (bytesLE_injective hpayload)

noncomputable def parse (segment : Segment) (bytes : HashInput) : Option (Query segment) :=
  if h : ∃ query, input segment query = bytes then some h.choose else none

theorem parse_some_iff (segment : Segment) (bytes : HashInput) (query : Query segment) :
    parse segment bytes = some query ↔ bytes = input segment query := by
  unfold parse
  split
  · rename_i hex
    rw [Option.some.injEq]
    constructor
    · intro heq; rw [← heq]; exact hex.choose_spec.symm
    · intro heq; exact input_injective segment (hex.choose_spec.trans heq)
  · rename_i hnone
    constructor
    · intro h; cases h
    · intro heq; exact False.elim (hnone ⟨query, heq.symm⟩)

theorem parse_input (segment : Segment) (query : Query segment) :
    parse segment (input segment query) = some query := (parse_some_iff segment _ query).mpr rfl

noncomputable def combine (low : Digest) (high : High) : HashOutput :=
  (splitHashOutputEquiv digestBits (by decide)).symm (low, high)

theorem split_combine (low : Digest) (high : High) :
    splitHashOutput digestBits (combine low high) = (low, high) :=
  (splitHashOutputEquiv digestBits (by decide)).apply_symm_apply (low, high)

theorem truncate_combine (low : Digest) (high : High) : truncateHash (combine low high) = low :=
  congrArg Prod.fst (split_combine low high)

theorem combine_split (output : HashOutput) :
    combine (truncateHash output) (splitHashOutput digestBits output).2 = output :=
  (splitHashOutputEquiv digestBits (by decide)).symm_apply_apply output

noncomputable def answer (segment : Segment) (tables : Fin segment.digit.val → Digest → Digest)
    (high : Query segment → High) (outside : QueryImpl HashSpec Id) : QueryImpl HashSpec Id :=
  fun bytes => match parse segment bytes with
    | none => outside bytes
    | some query => combine (tables query.1 query.2) (high query)

def lows (segment : Segment) (f : QueryImpl HashSpec Id) : Fin segment.digit.val → Digest → Digest :=
  fun index value => truncateHash (f (input segment (index, value)))

def highs (segment : Segment) (f : QueryImpl HashSpec Id) : Query segment → High :=
  fun query => (splitHashOutput digestBits (f (input segment query))).2

/-- The exact byte-query oracle agrees outside this prefix, without asserting anything about
whether the public computation actually avoids it. -/
def Avoids (segment : Segment) {α : Type} (f : QueryImpl HashSpec Id)
    (oa : OracleComp HashSpec α) : Prop :=
  ∀ bytes ∈ queriedInputs f oa, parse segment bytes = none

end Sphincs.Security.Prefix
