import FORS.Statement
import FORS.Classification.Signature
import FORS.Scheme.Domains
import FORS.Base.Prelude

section

/-!
A hash output as its low 128 bits (the digest the scheme keeps) and its unused high bits
(`combine`, `split_combine`, `combine_split`), so a sampled output can be split without losing the
part the adversary sees. Adapted from leanVM's OtsPrefixOracle.
-/

open OracleComp OracleSpec

namespace FORS.Security.Prefix

variable [Params]
open Concrete

abbrev High := BitVec (hashOutputBits - digestBits)

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

end FORS.Security.Prefix

end

section

/-!
Chain addresses, secret tables indexed by them, the address of a selected prefix segment, and
secret tables whose selected coordinate is erased. Adapted from leanVM's OtsPrefixSecretSampling.
-/

open OracleComp OracleSpec

namespace FORS.Security.Prefix

variable [Params]
open UniformTableSplit

attribute [local instance] Classical.propDecidable

abbrev ChainAddress := Layer × TreeIndex × LeafIndex × ChainIndex
abbrev Secrets := ChainAddress → Digest

end FORS.Security.Prefix

end

section

/-!
The predicate that counts source hash calls and the fixed-function source world (`fixedHashWorld`:
fresh private draws and a supplied hash function).
-/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.Prefix

variable [Params]
set_option backward.isDefEq.respectTransparency false

/-- Source-side hash calls, excluding private uniform samples. -/
def SourceHash : OracleWorld.Domain → Prop
  | .inl _ => False
  | .inr _ => True

instance (input : OracleWorld.Domain) : Decidable (SourceHash input) := by
  cases input <;> unfold SourceHash <;> infer_instance

/-- Fresh private uniform sampling together with a supplied fixed hash function. -/
noncomputable def fixedHashWorld (outside : QueryImpl HashSpec Id) : QueryImpl OracleWorld PMF
  | .inl _sample => PMF.uniformOfFintype _
  | .inr bytes => PMF.pure (outside bytes)

end FORS.Security.Prefix

end

section

/-! The chain secrets derived from the seed, as a table indexed by chain addresses. -/

open OracleComp OracleSpec

namespace FORS.Security.Prefix

variable [Params]
open Concrete

def derivedSecrets (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (seed : MasterSeed) : Secrets :=
  fun (lay, tree, leaf, chain) =>
    evalWithAnswerFn f (Seeded.otsStart parameter lay tree leaf chain seed : OracleComp HashSpec Digest)

end FORS.Security.Prefix

end

section

/-! The first successful encoding of a counter search (`firstEncoding`), which is what the honest
one-time signer computes. -/

open OracleComp OracleSpec

namespace FORS.Security.Prefix

variable [Params]
open Concrete

attribute [local instance] Classical.propDecidable
attribute [local irreducible] encodingAttemptLimit Seeded.treePath Seeded.forsNode chainWalk

/-- The actual least successful encoding search; its counter remains a 32-bit value. -/
noncomputable def firstEncoding (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (message : HashInput) :
    Nat → Nat → Option (Counter × Encoding)
  | 0, _ => none
  | attempts + 1, counter =>
      match evalWithAnswerFn f (encode parameter lay tree leaf message (BitVec.ofNat counterBits counter) :
          OracleComp HashSpec (Option Encoding)) with
      | some word => some (BitVec.ofNat counterBits counter, word)
      | none => firstEncoding f parameter lay tree leaf message attempts (counter + 1)

theorem otsSignFrom_eq_firstEncoding (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (seed : MasterSeed) (message : HashInput)
    (attempts start : Nat) :
    evalWithAnswerFn f (Seeded.otsSignFrom parameter lay tree leaf seed message attempts start :
      OracleComp HashSpec (Option (Counter × (ChainIndex → Digest)))) =
    (firstEncoding f parameter lay tree leaf message attempts start).map (fun pair =>
      (pair.1, fun chain => evalWithAnswerFn f (chainWalk parameter lay tree leaf chain 0
        (pair.2 chain).val (derivedSecrets f parameter seed (lay, tree, leaf, chain)) :
        OracleComp HashSpec Digest))) := by
  induction attempts generalizing start with
  | zero => rfl
  | succ attempts ih =>
      cases hencode : evalWithAnswerFn f
          (encode parameter lay tree leaf message (BitVec.ofNat counterBits start) :
            OracleComp HashSpec (Option Encoding)) with
      | none =>
          simp only [Seeded.otsSignFrom, evalWithAnswerFn_bind, firstEncoding, hencode]
          exact ih (start + 1)
      | some word =>
          simp only [Seeded.otsSignFrom, evalWithAnswerFn_bind, firstEncoding, hencode,
            Completeness.eval_sequenceFin, Completeness.eval_otsSecrets, Completeness.otsSecret,
            evalWithAnswerFn_pure, Option.map_some, derivedSecrets]

end FORS.Security.Prefix

end

section

/-! Hash-only evaluation inside the private-sampling interpreter is deterministic. -/

open OracleComp OracleSpec

namespace FORS.Security.Prefix

variable [Params]
open Concrete
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] encodingAttemptLimit digestAttemptLimit Seeded.signLayer
  Seeded.forsOpen Seeded.forsKey sequenceFin chainWalk

/-- Hash-only evaluation inside the private-sampling interpreter is deterministic. -/
theorem fixedHashWorld_lift_hash (f : QueryImpl HashSpec Id) {α : Type}
    (computation : OracleComp HashSpec α) :
    simulateQ (fixedHashWorld f) (liftM computation : OracleComp OracleWorld α) =
      PMF.pure (evalWithAnswerFn f computation) := by
  have hlift : simulateQ (fixedHashWorld f) (liftM computation : OracleComp OracleWorld α) =
      simulateQ (fun bytes => PMF.pure (f bytes) : QueryImpl HashSpec PMF) computation :=
    QueryImpl.simulateQ_liftComp_right_eq_of_apply (fixedHashWorld f)
      (fun bytes => PMF.pure (f bytes)) (fun _ => rfl) computation
  rw [hlift]
  clear hlift
  induction computation using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, evalWithAnswerFn_pure]; rfl
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, evalWithAnswerFn_bind,
        show evalWithAnswerFn f (liftM (HashSpec.query input)) = f input from simulateQ_spec_query f input,
        ← PMF.monad_pure_eq_pure, pure_bind]
      exact ih (f input)


end FORS.Security.Prefix

end
