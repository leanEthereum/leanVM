import SphincsFors.SecurityPrefixFullSign

/-! Exact hash-call counts (`hashCalls`) of the honest seeded computations on a fixed answer
function: wrappers, chains, one-time keys, tree and FORS nodes, encodings, message digests and
signing attempts. -/

open OracleComp OracleSpec

namespace SphincsFors.Security.Prefix
open Concrete

attribute [local irreducible] encodingAttemptLimit digestAttemptLimit Seeded.treeNode
  Seeded.ftsNode Seeded.ftsKey Seeded.ftsOpen Seeded.treePath Seeded.signLayer chainWalk
  deriveKey derivePair
set_option backward.isDefEq.respectTransparency false

def hashCalls {α : Type} (f : QueryImpl HashSpec Id) (computation : OracleComp HashSpec α) : Nat :=
  (queriedInputs f computation).length

@[simp] theorem hashCalls_pure {α : Type} (f : QueryImpl HashSpec Id) (value : α) :
    hashCalls f (pure value) = 0 := rfl

theorem hashCalls_bind {α β : Type} (f : QueryImpl HashSpec Id)
    (computation : OracleComp HashSpec α) (next : α → OracleComp HashSpec β) :
    hashCalls f (computation >>= next) = hashCalls f computation +
      hashCalls f (next (evalWithAnswerFn f computation)) := by
  simp only [hashCalls, queriedInputs_bind, List.length_append]

@[simp] theorem hashCalls_oracleHash (f : QueryImpl HashSpec Id) (input : HashInput) :
    hashCalls f (oracleHash input : OracleComp HashSpec HashOutput) = 1 := rfl

@[simp] theorem hashCalls_tweakableHash (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    hashCalls f (tweakableHash parameter domain payload : OracleComp HashSpec Digest) = 1 := by
  simp only [hashCalls, queriedInputs_tweakableHash, List.length_singleton]

@[simp] theorem hashCalls_deriveKey (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (domain : KeygenDomain) (seed : MasterSeed) :
    hashCalls f (deriveKey parameter domain seed : OracleComp HashSpec Digest) = 1 := by
  simp only [deriveKey, hashCalls_bind, hashCalls_oracleHash, hashCalls_pure, Nat.add_zero]

/-- One hash of the seed gives the two values. -/
@[simp] theorem hashCalls_derivePair (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (domain : KeygenDomain) (seed : MasterSeed) :
    hashCalls f (derivePair parameter domain seed : OracleComp HashSpec (Digest × Digest)) = 1 := by
  simp only [derivePair, hashCalls_bind, hashCalls_oracleHash, hashCalls_pure, Nat.add_zero]

theorem hashCalls_sequenceFin {α : Type} {n : Nat} (f : QueryImpl HashSpec Id)
    (computation : Fin n → OracleComp HashSpec α) :
    hashCalls f (sequenceFin computation) = ∑ i, hashCalls f (computation i) := by
  induction n with
  | zero => simp [sequenceFin]
  | succ n ih =>
      simp only [sequenceFin, hashCalls_bind, hashCalls_pure, Nat.add_zero, ih,
        Fin.sum_univ_succ]

theorem hashCalls_chainWalk (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chain : ChainIndex)
    (start steps : Nat) (value : Digest) (hsteps : start + steps ≤ chainLength - 1) :
    hashCalls f (chainWalk parameter lay tree leaf chain start steps value : OracleComp HashSpec Digest) = steps := by
  induction steps generalizing start value with
  | zero => simp only [chainWalk, hashCalls_pure]
  | succ steps ih =>
      rw [chainWalk, hashCalls_bind, dite_eq_left (by omega), hashCalls_tweakableHash, ih _ _ (by omega)]

/-- A sum over the 64 chains, pair by pair. -/
theorem sum_chains_eq_sum_pairs (g : ChainIndex → Nat) :
    ∑ chain, g chain = ∑ pair : Fin (numChains / 2), (g (Seeded.evenChain pair) + g (Seeded.oddChain pair)) := by
  have h := Fintype.sum_equiv (finProdFinEquiv (m := 32) (n := 2))
    (fun x => g (finProdFinEquiv x)) g (fun _ => rfl)
  rw [Fintype.sum_prod_type] at h
  refine h.symm.trans (Fintype.sum_congr _ _ fun pair => ?_)
  rw [Fin.sum_univ_two]
  have heven : (finProdFinEquiv (pair, (0 : Fin 2)) : Fin (32 * 2)) = Seeded.evenChain pair :=
    Fin.ext (by simp [finProdFinEquiv, Seeded.evenChain])
  have hodd : (finProdFinEquiv (pair, (1 : Fin 2)) : Fin (32 * 2)) = Seeded.oddChain pair :=
    Fin.ext (by simp [finProdFinEquiv, Seeded.oddChain]; omega)
  rw [heven, hodd]

/-- The chain values of a one-time key take 32 hashes of the seed, two chain starts each, and the
chain steps. -/
theorem hashCalls_otsValues (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (seed : MasterSeed) (steps : ChainIndex → Nat)
    (hsteps : ∀ chain, steps chain ≤ chainLength - 1) :
    hashCalls f (Seeded.otsValues parameter lay tree leaf seed steps :
      OracleComp HashSpec (ChainIndex → Digest)) = numChains / 2 + ∑ chain, steps chain := by
  have walk (chain : ChainIndex) (value : Digest) :
      hashCalls f (chainWalk parameter lay tree leaf chain 0 (steps chain) value :
        OracleComp HashSpec Digest) = steps chain :=
    hashCalls_chainWalk f parameter lay tree leaf chain 0 (steps chain) value (by
      have := hsteps chain; omega)
  simp only [Seeded.otsValues, hashCalls_bind, hashCalls_sequenceFin, hashCalls_derivePair,
    hashCalls_pure, walk, Nat.add_zero]
  rw [sum_chains_eq_sum_pairs, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one]

/-- A one-time public key takes 32 hashes of the seed and 192 chain steps. -/
theorem hashCalls_oneTimePublicKey (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (seed : MasterSeed) :
    hashCalls f (Seeded.oneTimePublicKey parameter lay tree leaf seed :
      OracleComp HashSpec (ChainIndex → Digest)) = 224 := by
  rw [Seeded.oneTimePublicKey, hashCalls_otsValues f parameter lay tree leaf seed _ (fun _ => le_rfl)]
  decide

theorem hashCalls_treeNode (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (seed : MasterSeed) (level nodeIdx : Nat) :
    hashCalls f (Seeded.treeNode parameter lay tree seed level nodeIdx : OracleComp HashSpec Digest) =
      226 * 2 ^ level - 1 := by
  induction level generalizing nodeIdx with
  | zero => simp [Seeded.treeNode, hashCalls_bind, hashCalls_oneTimePublicKey, leafHash]
  | succ level ih =>
      simp only [Seeded.treeNode, hashCalls_bind, ih, hashCalls_tweakableHash]
      have hpos : 0 < 2 ^ level := Nat.two_pow_pos level
      rw [pow_succ]
      omega

/-- The hash calls of a FORS node over `2^level` leaves: a single leaf takes one hash of the seed
and its leaf hash; from level 1 on, each pair of leaves takes one hash of the seed. -/
def ftsNodeCost (level : Nat) : Nat := if level = 0 then 2 else 5 * 2 ^ (level - 1) - 1

theorem hashCalls_ftsNode (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (index : Index) (tree : FtsTree) (seed : MasterSeed) (level nodeIdx : Nat) :
    hashCalls f (Seeded.ftsNode parameter index tree seed level nodeIdx : OracleComp HashSpec Digest) =
      ftsNodeCost level := by
  induction level generalizing nodeIdx with
  | zero => simp [Seeded.ftsNode, hashCalls_bind, ftsLeafHash, ftsNodeCost]
  | succ level ih =>
      cases level with
      | zero =>
          simp [Seeded.ftsNode, hashCalls_bind, ftsLeafHash, ftsNodeCost]
      | succ level =>
          simp only [Seeded.ftsNode, hashCalls_bind, ih, hashCalls_tweakableHash]
          have hpos : 0 < 2 ^ level := Nat.two_pow_pos level
          simp only [ftsNodeCost, Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel]
          rw [pow_succ]
          omega

theorem hashCalls_encode (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (message : Digest) (counter : Counter) :
    hashCalls f (encode parameter lay tree leaf message counter : OracleComp HashSpec (Option Encoding)) = 1 := by
  simp only [encode, hashCalls_bind, hashCalls_tweakableHash, hashCalls_pure, Nat.add_zero]

variable [Params]

omit [Params] in
theorem hashCalls_sequenceLayers {α : Layer → Type} (f : QueryImpl HashSpec Id)
    (computation : (lay : Layer) → OracleComp HashSpec (Option (α lay))) :
    hashCalls f (sequenceLayers computation) = hashCalls f (computation topLayer) := by
  rw [sequenceLayers, hashCalls_bind]
  cases evalWithAnswerFn f (computation topLayer) <;> simp only [hashCalls_pure, Nat.add_zero]

omit [Params] in
theorem hashCalls_messageDigestCall (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (root : Digest) (message : Message) (randomness : Randomness) (call : Fin 2) :
    hashCalls f (messageDigestCall parameter root message randomness call : OracleComp HashSpec HashOutput) = 1 := rfl

omit [Params] in
theorem hashCalls_messageDigest (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (root : Digest) (message : Message) (randomness : Randomness) :
    hashCalls f (messageDigest parameter root message randomness : OracleComp HashSpec MessageDigest) = 2 := by
  simp only [messageDigest, hashCalls_bind, hashCalls_messageDigestCall, hashCalls_pure]

theorem hashCalls_signAttempt (f : QueryImpl HashSpec Id) (sk : Seeded.SecretKey)
    (message : Message) (randomness : Randomness) :
    hashCalls f (Seeded.signAttempt sk message randomness : OracleComp HashSpec (Option Index)) = 1 := by
  rw [Seeded.signAttempt, hashCalls_bind, hashCalls_messageDigestCall]
  split <;> rfl

end SphincsFors.Security.Prefix
