module

public import XmssSecurity.Proof.Bridge.Program
public import XmssSecurity.Proof.StatementLemmas

@[expose] public section

/-!
# The honest preparation

The model's key generation over a derivation table computes every chain, leaf and node of both
layers and every top signature. After it, the cache resolves each of these computations to the value
the model's secret key stores.
-/

open OracleComp OracleSpec

namespace XmssSecurity.Bridge

open Seeded DeterministicSigning

set_option backward.isDefEq.respectTransparency false

/-! ## The model key over a table -/

/-- The bottom chain starts: chain `i` of key `idx` is half `i mod 2` of derivation `(idx, i / 2)`. -/
def Derivations.secret (d : Derivations) : LeafIndex → ChainIndex → Digest :=
  fun index chain => hashHalf chain.val (d.bottom (index, chainPair chain))

def Derivations.topSecret (d : Derivations) : TopIndex → ChainIndex → Digest :=
  fun key chain => hashHalf chain.val (d.top (key, chainPair chain))

/-- The top randomizer base of key `b` signing root `r`. -/
def Derivations.topBase (d : Derivations) (key : TopIndex) (root : Digest) : Randomness :=
  truncateHash (d.topRnd (key, root))

/-- The model's key generation with the table's secrets and top bases. -/
def honestRun (d : Derivations) :
    OracleComp HashSpec (Digest × (TopIndex → Option (Randomness × Encoding))) :=
  Concrete.honestKeygen d.parameter d.secret d.topSecret fun key root => pure (d.topBase key root)

/-- The model key a logged run of `honestRun` gives. -/
noncomputable def modelSecretKey (d : Derivations)
    (result : (Digest × (TopIndex → Option (Randomness × Encoding))) × QueryLog HashSpec) :
    XmssSecurity.SecretKey :=
  Concrete.precomputedSecretKey d.parameter d.secret d.topSecret result.1.2 (hashCacheOfLog result.2)

def modelPublicKey (d : Derivations)
    (result : (Digest × (TopIndex → Option (Randomness × Encoding))) × QueryLog HashSpec) : PublicKey :=
  ⟨result.1.1, d.parameter⟩

/-! ## Tweakable computations -/

theorem onlyQueries_query {S : HashInput → Prop} {x : HashInput} (hx : S x) :
    OnlyQueries S (Concrete.oracleHash x : OracleComp HashSpec HashOutput) := by
  change OnlyQueries S (liftM (HashSpec.query x) : OracleComp HashSpec HashOutput)
  rw [← bind_pure (liftM (HashSpec.query x) : OracleComp HashSpec HashOutput)]
  exact .query x hx _ fun a => .pure a

theorem tweakableHash_tweakable (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    OnlyQueries Tweakable (Concrete.tweakableHash parameter domain payload : OracleComp HashSpec Digest) :=
  (onlyQueries_query ⟨parameter, domain, payload, rfl⟩).bind fun _ => .pure _

theorem chainWalk_tweakable (parameter : PublicParameter) (index : LeafIndex) (chain : ChainIndex)
    (start steps : Nat) (value : Digest) :
    OnlyQueries Tweakable (Concrete.chainWalk parameter index chain start steps value :
      OracleComp HashSpec Digest) := by
  induction steps with
  | zero => exact .pure _
  | succ steps ih =>
      rw [Concrete.chainWalk]
      refine ih.bind fun previous => ?_
      split
      · exact tweakableHash_tweakable _ _ _
      · exact .pure _

theorem topChainWalk_tweakable (parameter : PublicParameter) (key : TopIndex) (chain : ChainIndex)
    (start steps : Nat) (value : Digest) :
    OnlyQueries Tweakable (Concrete.topChainWalk parameter key chain start steps value :
      OracleComp HashSpec Digest) := by
  induction steps with
  | zero => exact .pure _
  | succ steps ih =>
      rw [Concrete.topChainWalk]
      refine ih.bind fun previous => ?_
      split
      · exact tweakableHash_tweakable _ _ _
      · exact .pure _

theorem treeNode_tweakable (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (levels : Nat) (node : MerkleNode) :
    OnlyQueries Tweakable (Concrete.treeNode parameter secret levels node : OracleComp HashSpec Digest) := by
  induction levels generalizing node with
  | zero =>
      rw [Concrete.treeNode_zero_eq]
      exact (OnlyQueries.sequenceFin fun chain => chainWalk_tweakable _ _ _ _ _ _).bind
        fun _ => tweakableHash_tweakable _ _ _
  | succ levels ih =>
      rw [Concrete.treeNode_succ_eq]
      refine (ih _).bind fun _ => (ih _).bind fun _ => ?_
      split
      · exact tweakableHash_tweakable _ _ _
      · exact .pure _

theorem topTreeNode_tweakable (parameter : PublicParameter) (topSecret : TopIndex → ChainIndex → Digest)
    (levels : Nat) (node : TopNode) :
    OnlyQueries Tweakable (Concrete.topTreeNode parameter topSecret levels node :
      OracleComp HashSpec Digest) := by
  induction levels generalizing node with
  | zero =>
      rw [Concrete.topTreeNode]
      exact (OnlyQueries.sequenceFin fun chain => topChainWalk_tweakable _ _ _ _ _ _).bind
        fun _ => tweakableHash_tweakable _ _ _
  | succ levels ih =>
      rw [Concrete.topTreeNode]
      refine (ih _).bind fun _ => (ih _).bind fun _ => ?_
      split
      · exact tweakableHash_tweakable _ _ _
      · exact .pure _

theorem topSignFrom_tweakable (parameter : PublicParameter) (key : TopIndex) (root : Digest)
    (base : Randomness) (attempts trial : Nat) :
    OnlyQueries Tweakable (Concrete.topSignFrom parameter key root base attempts trial :
      OracleComp HashSpec (Option (Randomness × Encoding))) := by
  induction attempts generalizing trial with
  | zero => exact .pure _
  | succ attempts ih =>
      rw [Concrete.topSignFrom]
      refine (tweakableHash_tweakable _ _ _).bind fun digest => ?_
      split
      · exact .pure _
      · exact ih _

theorem honestRun_tweakable (d : Derivations) : OnlyQueries Tweakable (honestRun d) := by
  unfold honestRun Concrete.honestKeygen
  exact (OnlyQueries.sequenceFin fun key => (treeNode_tweakable _ _ _ _).bind fun _ =>
    (OnlyQueries.pure _).bind fun _ => topSignFrom_tweakable _ _ _ _ _ _).bind fun _ =>
      (topTreeNode_tweakable _ _ _ _).bind fun _ => .pure _

/-! ## The prepared cache -/

/-- `cache` is the cache after the logged run of `honestRun d` with result `result` from the
programmed cache of `seed`. -/
structure Prepared (seed : MasterSeed) (d : Derivations)
    (result : (Digest × (TopIndex → Option (Randomness × Encoding))) × QueryLog HashSpec)
    (cache : QueryCache HashSpec) : Prop where
  resolves : Resolves cache (honestRun d) result.1
  prog_le : progCache seed d ≤ cache
  log_agree : ∀ x, Tweakable x → hashCacheOfLog result.2 x = cache x

theorem prepared_of_mem (seed : MasterSeed) (d : Derivations)
    (result : (Digest × (TopIndex → Option (Randomness × Encoding))) × QueryLog HashSpec)
    (cache : QueryCache HashSpec)
    (hmem : (result, cache) ∈ support
      ((simulateQ randomOracle (honestRun d).withQueryLog).run (progCache seed d))) :
    Prepared seed d result cache where
  resolves := by
    have h : (result.1, cache) ∈ support ((simulateQ randomOracle (honestRun d)).run (progCache seed d)) := by
      rw [← withQueryLog_run_forget, support_map]
      exact ⟨(result, cache), hmem, rfl⟩
    exact resolves_of_run _ _ _ h
  prog_le := by
    have h : (result.1, cache) ∈ support ((simulateQ randomOracle (honestRun d)).run (progCache seed d)) := by
      rw [← withQueryLog_run_forget, support_map]
      exact ⟨(result, cache), hmem, rfl⟩
    exact cache_le_of_run _ _ _ h
  log_agree := by
    intro x hx
    have hfinal := withQueryLog_finalCache _ _ _ hmem
    simp only at hfinal
    rw [hfinal, hashCacheOfLog]
    exact extendHashCacheWithLog_congr _ (progCache_tweakable hx).symm

namespace Prepared

variable {seed : MasterSeed} {d : Derivations}
  {result : (Digest × (TopIndex → Option (Randomness × Encoding))) × QueryLog HashSpec}
  {cache : QueryCache HashSpec}

/-- A tweakable computation the cache resolves replays from the log to the same value. -/
theorem replay_eq (h : Prepared seed d result cache) {α : Type} {c : OracleComp HashSpec α}
    (hc : OnlyQueries Tweakable c) {v : α} (hv : Resolves cache c v) :
    evalWithAnswerFn (Concrete.replayHash (hashCacheOfLog result.2)) c = v := by
  apply (Resolves.congr hv hc (fun x hx => h.log_agree x hx)).eval
  intro x a hx
  simp [Concrete.replayHash, hx]

end Prepared

end XmssSecurity.Bridge
