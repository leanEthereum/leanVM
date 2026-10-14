import LeanxmssProofs.Encoding
import LeanxmssProofs.Leaf
import LeanxmssProofs.Merkle

/-!
# The guest's `verify` is the specification's

For every public key, leaf index, message and signature, the guest's `verify` returns, without panicking:

- `Ok(())` exactly when the specification's `verify` accepts,
- `Err(InvalidEncoding)` exactly when the specification's encoding finds no digits,
- `Err(InvalidMerklePath)` otherwise.

The guest's values are the specification's through `Statement.lean`'s maps, which are bijections (`Words.lean`).
-/

open Aeneas Aeneas.Std Result WP
open EthCryptographySpecs.Xmss EthCryptographySpecs.Xmss.Constants

namespace leanxmss.Proofs

open Bytes Statement

/-- The specification's verdict as the guest's result: `Ok(())` if it accepts, else the guest's reason. -/
def specResult (pk : leanxmss.PublicKey) (leaf : Std.U32) (msg : Std.Array U64 4#usize) (sig : leanxmss.Signature) :
    core.result.Result Unit leanxmss.XmssVerifyError :=
  match wotsEncode (publicKey pk).publicParam (message msg) (signature sig).randomness (epoch leaf) with
  | none => .Err .InvalidEncoding
  | some _ =>
    if EthCryptographySpecs.Xmss.verify (publicKey pk) (message msg) (signature sig) (epoch leaf) then .Ok ()
    else .Err .InvalidMerklePath

theorem digest_inj {a b : Std.Array U64 2#usize} (h : Statement.digest a = Statement.digest b) : a = b :=
  bytes_inj rfl h

theorem arrayEq_ok (a b : Std.Array U64 2#usize) :
    core.array.equality.PartialEqArray.eq core.cmp.PartialEqU64 a b = ok (decide (a = b)) := by
  obtain ⟨la, ha⟩ : ∃ l, a.val = l := ⟨_, rfl⟩
  obtain ⟨lb, hb⟩ : ∃ l, b.val = l := ⟨_, rfl⟩
  have hla : la.length = 2 := by rw [← ha]; simp
  have hlb : lb.length = 2 := by rw [← hb]; simp
  match la, lb, hla, hlb with
  | [a0, a1], [b0, b1], _, _ =>
    have : (a = b) ↔ (a0 = b0 ∧ a1 = b1) := by
      rw [Std.Array.eq_iff, ha, hb]; simp
    simp [core.array.equality.PartialEqArray.eq, ha, hb, List.allM, this]
    have e0 : (a0.val = b0.val) ↔ a0 = b0 := ⟨UScalar.eq_of_val_eq, fun h => h ▸ rfl⟩
    have e1 : (a1.val = b1.val) ↔ a1 = b1 := ⟨UScalar.eq_of_val_eq, fun h => h ▸ rfl⟩
    by_cases h0 : a0 = b0 <;> by_cases h1 : a1 = b1 <;> simp [e0, e1, h0, h1] <;> rfl

/-- The guest's `verify` is the specification's, reasons included, and never panics. -/
theorem verify_spec (pk : leanxmss.PublicKey) (leaf : Std.U32) (msg : Std.Array U64 4#usize)
    (sig : leanxmss.Signature) :
    leanxmss.verify pk leaf msg sig = ok (specResult pk leaf msg sig) := by
  have he := encode_spec pk.public_param leaf msg sig.randomness
  unfold specResult
  simp only [publicKey, signature, epoch_eq_u32]
  split at he
  · rename_i hnone
    rw [hnone]
    simp [leanxmss.verify, he, core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  · rename_i x hx
    obtain ⟨d, hd, hget⟩ := he
    obtain ⟨chains, hchains, l, hl, hleaf⟩ := wots_leaf_spec pk.public_param leaf sig d x hget
    obtain ⟨r, hr, hroot⟩ := merkle_root_spec pk.public_param leaf l sig.merkle_proof
    simp only [signature] at hleaf
    simp only [EthCryptographySpecs.Xmss.verify, hx, signature, publicKey]
    rw [← hleaf, ← hroot]
    simp only [leanxmss.verify, hd, core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok,
      hchains, hl, hr, arrayEq_ok]
    by_cases h : r = pk.merkle_root
    · simp [h, hl, hr]
    · have : Statement.digest r ≠ Statement.digest pk.merkle_root := fun e => h (digest_inj e)
      simp [h, this, hl, hr]

/-- The guest accepts exactly the signatures the specification accepts. -/
theorem verify_ok_iff (pk : leanxmss.PublicKey) (leaf : Std.U32) (msg : Std.Array U64 4#usize)
    (sig : leanxmss.Signature) :
    leanxmss.verify pk leaf msg sig = ok (.Ok ()) ↔
      EthCryptographySpecs.Xmss.verify (publicKey pk) (message msg) (signature sig) (epoch leaf) = true := by
  rw [verify_spec]
  unfold specResult
  constructor
  · intro h
    have h := Result.ok_injective h
    split at h
    · cases h
    · split at h
      · assumption
      · cases h
  · intro h
    split
    · rename_i hnone
      simp [EthCryptographySpecs.Xmss.verify, hnone] at h
    · simp [h]

end leanxmss.Proofs
