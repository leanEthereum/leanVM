import LeanSphincsProofs.Common

/-!
# `hash.rs`: addresses and the tweakable hash

`th` is the truncated Keccak-256 of `PK.seed ‖ ADRS ‖ M` (`th_spec`, from `HasherSpec`), and the
address functions lay out the statement's `Address.toBytes` (`keyAdrs_spec`, `adrsWord_spec`,
`treeAdrs_spec`). The Rust library models they step through are in `Keccak256Proofs.Library`.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM Std.Do
open HashSig HashSig.OverPermutation Sphincs
open LeanVM.Semantics (KeccakState)
open LeanVM.Protocol.KeccakHash (digestBytes keccak256With)
open Keccak256Proofs

namespace LeanSphincsProofs

/-- **`u64::to_be_bytes` is the statement's `bigEndianBytes 8`.** -/
theorem bytes_u64_to_be_bytes (x : Std.U64) :
    bytes (Aeneas.Std.core.num.U64.to_be_bytes x).val = bigEndianBytes 8 x.bv := by
  have h : x.bv.toBEBytes = [x.bv.extractLsb' 56 8, x.bv.extractLsb' 48 8, x.bv.extractLsb' 40 8,
      x.bv.extractLsb' 32 8, x.bv.extractLsb' 24 8, x.bv.extractLsb' 16 8, x.bv.extractLsb' 8 8,
      x.bv.extractLsb' 0 8] := by
    simp [BitVec.toBEBytes, BitVec.toLEBytes]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> bv_bits
  simp only [Aeneas.Std.core.num.U64.to_be_bytes, Array.from_val, h, bytes, List.map_cons,
    List.map_nil, b8]
  rfl

/-! ## Addresses, as bytes -/

/-- `Adrs::word`: four bytes of the address set to a big-endian word. -/
@[spec]
theorem adrs_word_triple (a : lean_sphincs.hash.Adrs) (pos : Std.Usize) (v : Std.U32)
    (h : pos.val + 4 ≤ 32) :
    ⦃ ⌜ True ⌝ ⦄ lean_sphincs.hash.Adrs.word a pos v
    ⦃ ⇓ r => ⌜ r.val = a.val.setSlice! pos.val (Aeneas.Std.core.num.U32.to_be_bytes v).val ⌝ ⦄ := by
  hax_mvcgen [lean_sphincs.hash.Adrs.word, core.num.U32.to_be_bytes,
    rust_primitives.arithmetic.to_be_bytes_u32]
  case vc1.h => scalar_tac
  case vc2.he => scalar_tac
  case vc3.h =>
    rename_i e he r hr
    have ha : a.val.length = 32 := by simp
    show r.1.val.length = (Aeneas.Std.core.num.U32.to_be_bytes v).to_slice.val.length
    rw [hr.1]
    simp [List.slice]
    scalar_tac
  case vc4 =>
    rename_i e he r hr s a1 hs
    simp [a1, hr.2, hs]
  case vc5.h_fail => scalar_tac

@[simp] theorem bigEndianBytes_length (n : ℕ) (v : BitVec (8 * n)) :
    (bigEndianBytes n v).length = n := by
  simp [bigEndianBytes]

/-- `Adrs::word` on an address whose bytes are `p ‖ w ‖ q`, `w` the four at `pos`. -/
theorem adrs_word_bytes (a : lean_sphincs.hash.Adrs) (pos : Std.Usize) (v : Std.U32)
    (p w q : List UInt8) (hb : bytes a.val = p ++ w ++ q) (hp : p.length = pos.val)
    (hw : w.length = 4) :
    ∃ a', lean_sphincs.hash.Adrs.word a pos v = ok a' ∧
      bytes a'.val = p ++ bigEndianBytes 4 v.bv ++ q := by
  have hlen : (bytes a.val).length = 32 := by simp
  have hpos : pos.val + 4 ≤ 32 := by
    rw [hb] at hlen; simp at hlen; omega
  obtain ⟨a', ha', hv⟩ := exists_of_triple (adrs_word_triple a pos v hpos)
  refine ⟨a', ha', ?_⟩
  rw [hv, bytes_setSlice!, hb, bytes_u32_to_be_bytes, ← hp]
  exact setSlice!_mid p w q _ (by simp [hw])

/-- `Adrs::new`: the layer, four zero bytes, the tree, sixteen zero bytes. -/
theorem adrs_new_bytes (layer : Std.U32) (tree : Std.U64) :
    ∃ a, lean_sphincs.hash.Adrs.new layer tree = ok a ∧
      bytes a.val = bigEndianBytes 4 layer.bv ++ List.replicate 4 0 ++ bigEndianBytes 8 tree.bv ++
        List.replicate 16 0 := by
  have key : ⦃ ⌜ True ⌝ ⦄ lean_sphincs.hash.Adrs.new layer tree
      ⦃ ⇓ r => ⌜ r.val = ((List.replicate 32 0#u8).setSlice! 0
        (Aeneas.Std.core.num.U32.to_be_bytes layer).val).setSlice! 8
        (Aeneas.Std.core.num.U64.to_be_bytes tree).val ⌝ ⦄ := by
    hax_mvcgen [lean_sphincs.hash.Adrs.new, core.num.U32.to_be_bytes, core.num.U64.to_be_bytes,
      rust_primitives.arithmetic.to_be_bytes_u32, rust_primitives.arithmetic.to_be_bytes_u64]
    case vc2.h =>
      rename_i r0 h0 r hr
      show r.1.val.length = (Aeneas.Std.core.num.U32.to_be_bytes layer).to_slice.val.length
      rw [hr.1, h0]; simp
    case vc5.h =>
      rename_i r0 h0 r hr s out1 hs r' hr'
      show r'.1.val.length = (Aeneas.Std.core.num.U64.to_be_bytes tree).to_slice.val.length
      rw [hr'.1]; simp [List.slice, out1]
    case vc6 =>
      rename_i r0 h0 r hr s out1 hs r' hr' s' out2 hs'
      simp [out2, out1, hr'.2, hr.2, hs, hs', h0]
  obtain ⟨a, ha, hv⟩ := exists_of_triple key
  refine ⟨a, ha, ?_⟩
  rw [hv, bytes_setSlice!, bytes_setSlice!, bytes_u32_to_be_bytes, bytes_u64_to_be_bytes,
    bytes_replicate_zero]
  rw [show List.replicate 32 (0 : UInt8) = [] ++ List.replicate 4 0 ++ List.replicate 28 0 from rfl,
    setSlice!_mid' _ _ _ _ 0 rfl (by simp), List.nil_append,
    show List.replicate 28 (0 : UInt8) = List.replicate 4 0 ++ List.replicate 8 0 ++
      List.replicate 16 0 from rfl,
    ← List.append_assoc, ← List.append_assoc, setSlice!_mid' _ _ _ _ 8 (by simp) (by simp)]

/-- `Adrs::with_type` on an address whose first sixteen bytes are `p`: the type, then twelve zero
bytes. -/
theorem adrs_with_type_bytes (a : lean_sphincs.hash.Adrs) (t : Std.U32) (p q : List UInt8)
    (hb : bytes a.val = p ++ q) (hp : p.length = 16) :
    ∃ a', lean_sphincs.hash.Adrs.with_type a t = ok a' ∧
      bytes a'.val = p ++ bigEndianBytes 4 t.bv ++ List.replicate 12 0 := by
  have key : ⦃ ⌜ True ⌝ ⦄ lean_sphincs.hash.Adrs.with_type a t
      ⦃ ⇓ r => ⌜ r.val = (a.val.setSlice! 20 (List.replicate 12 0#u8)).setSlice! 16
        (Aeneas.Std.core.num.U32.to_be_bytes t).val ⌝ ⦄ := by
    hax_mvcgen [lean_sphincs.hash.Adrs.with_type]
    case vc2.success.success.success =>
      rename_i r hr s a1 hs r' hr'
      have hl : r.1.length = 12 := by
        show r.1.val.length = 12
        rw [hr.1]; simp
      rw [hr']
      simp [a1, hr.2, hs, hl]
    case vc3 => scalar_tac
  obtain ⟨a', ha', hv⟩ := exists_of_triple key
  refine ⟨a', ha', ?_⟩
  have hlen : (bytes a.val).length = 32 := by simp
  have hq : q.length = 16 := by rw [hb] at hlen; simp at hlen; omega
  rw [hv, bytes_setSlice!, bytes_setSlice!, bytes_u32_to_be_bytes, bytes_replicate_zero, hb]
  rw [show p ++ q = (p ++ q.take 4) ++ q.drop 4 ++ [] by simp,
    setSlice!_mid' _ _ _ _ 20 (by simp [hp, hq]) (by simp [hq]), List.append_nil,
    setSlice!_mid' _ _ _ _ 16 hp (by simp [hq])]

/-- A key's tree address with a type set: the layer, the tree, the type, and twelve zero bytes. -/
theorem tree_adrs_with_type_bytes (k : lean_sphincs.wots.OtsKey) (t : Std.U32) :
    ∃ a a', lean_sphincs.wots.OtsKey.tree_adrs k = ok a ∧
      lean_sphincs.hash.Adrs.with_type a t = ok a' ∧
      bytes a'.val = bigEndianBytes 4 (BitVec.ofNat 32 k.layer.val) ++ List.replicate 4 0 ++
        bigEndianBytes 8 (BitVec.ofNat 64 k.tree.val) ++ bigEndianBytes 4 t.bv ++
        List.replicate 12 0 := by
  obtain ⟨a, ha, hb⟩ := adrs_new_bytes (UScalar.cast .U32 k.layer) k.tree
  obtain ⟨a', ha', hb'⟩ := adrs_with_type_bytes a t _ _ hb (by simp)
  refine ⟨a, a', ?_, ha', ?_⟩
  · simp only [lean_sphincs.wots.OtsKey.tree_adrs, lift]
    exact (Aeneas.Std.bind_ok _ _).trans ha
  · rw [hb', show U32.bv (UScalar.cast .U32 k.layer) = _ from cast_u32_bv k.layer,
      ← u64_bv_eq_ofNat]

theorem toBytes_eq (A : Sphincs.Address) :
    A.toBytes = bigEndianBytes 4 A.layer ++ List.replicate 4 0 ++ bigEndianBytes 8 A.tree ++
      bigEndianBytes 4 (BitVec.ofNat 32 A.addressType.word) ++ bigEndianBytes 4 A.keyPair ++
      bigEndianBytes 4 A.chainOrTreeHeight ++ bigEndianBytes 4 A.hashOrTreeIndex := rfl

theorem bigEndianBytes_zero : bigEndianBytes 4 (BitVec.ofNat 32 0) = List.replicate 4 0 := by
  decide

/-- **`OtsKey::tree_adrs` then `with_type`.** -/
theorem treeAdrs_spec : TreeAdrsSpec := by
  intro k t T ht _
  obtain ⟨a, a', ha, ha', hb⟩ := tree_adrs_with_type_bytes k t
  refine ⟨a, a', ha, ha', ?_⟩
  rw [AdrsIs, hb, toBytes_eq, u32_bv_eq_ofNat t, ht]
  simp only [makeAddress, bigEndianBytes_zero, List.append_assoc]
  rfl

/-- **`OtsKey::adrs`.** -/
theorem keyAdrs_spec : KeyAdrsSpec := by
  intro k t T ht _
  obtain ⟨a, a', ha, ha', hb⟩ := tree_adrs_with_type_bytes k t
  obtain ⟨a'', ha'', hb''⟩ := adrs_word_bytes a' 20#usize k.leaf
    (bigEndianBytes 4 (BitVec.ofNat 32 k.layer.val) ++ List.replicate 4 0 ++
      bigEndianBytes 8 (BitVec.ofNat 64 k.tree.val) ++ bigEndianBytes 4 t.bv)
    (List.replicate 4 0) (List.replicate 8 0)
    (by rw [hb, List.append_assoc _ (List.replicate 4 0) (List.replicate 8 0)]; rfl)
    (by simp) (by simp)
  refine ⟨a'', ?_, ?_⟩
  · simp only [lean_sphincs.wots.OtsKey.adrs, ha]
    erw [Aeneas.Std.bind_ok, ha', Aeneas.Std.bind_ok]
    exact ha''
  · rw [AdrsIs, hb'', toBytes_eq, u32_bv_eq_ofNat t, ht, u32_bv_eq_ofNat k.leaf]
    simp only [makeAddress, bigEndianBytes_zero, List.append_assoc]
    rfl

/-- **`Adrs::with_chain`, `with_tree_height`, `with_hash`, `with_tree_index`.** -/
theorem adrsWord_spec : AdrsWordSpec := by
  intro a A v h
  rw [AdrsIs, toBytes_eq] at h
  have h5 := adrs_word_bytes a 24#usize v _ _ _ h (by simp) (by simp)
  have h6 := adrs_word_bytes a 28#usize v _ _ []
    (by rw [h, List.append_nil]) (by simp) (by simp)
  rw [List.append_nil] at h6
  exact ⟨h5, h5, h6, h6⟩

/-! ## The tweakable hash -/

/-- **`th`**: the truncated Keccak-256 of `PK.seed ‖ ADRS ‖ M`. -/
theorem th_spec {π : KeccakState → KeccakState} (H : HasherSpec π) : ThSpec π := by
  intro seed adrs m
  obtain ⟨h0, hn, ha0⟩ := H.new
  obtain ⟨h1, b1, hu1, ha1, hb1⟩ := H.update h0 [] seed.to_slice ha0
  obtain ⟨h2, b2, hu2, ha2, hb2⟩ := H.update h1 _ adrs.to_slice ha1
  obtain ⟨h3, b3, hu3, ha3, hb3⟩ := H.update h2 _ m ha2
  obtain ⟨d, hf, hd⟩ := H.finalize h3 _ ha3
  obtain ⟨r, hr, hrv⟩ := truncate_16 d
  refine ⟨r, ?_, ?_⟩
  · simp [lean_sphincs.hash.th, lean_sphincs.hash.hasher, keccak256.prefixed_hasher,
      lean_sphincs.hash.Adrs.as_bytes, core.array.Array.as_slice,
      rust_primitives.slice.array_as_slice, hn, hu1, hu2, hu3, hb1, hb2, hf, hr]
  · have hl : (hashBytes π ([] ++ bytes seed.to_slice.val ++ bytes adrs.to_slice.val ++
        bytes m.val)).length = 32 := digestBytes_length _
    have hs : seed.to_slice.val = seed.val := by simp
    have hA : (Array.to_slice adrs).val = adrs.val := by simp
    rw [List.nil_append, hs, hA] at hd hl
    have hbr : bytes r.val = (hashBytes π (bytes seed.val ++ bytes adrs.val ++ bytes m.val)).take 16 := by
      rw [hrv, ← hd]; simp [bytes, List.map_take]
    show BitVec.ofNat 128 (leNat (bytes r.val)) =
      truncateHash (BitVec.ofNat 256 (leNat (hashBytes π (bytes seed.val ++ bytes adrs.val ++ bytes m.val))))
    rw [hbr, leNat_take]
    apply BitVec.eq_of_toNat_eq
    simp [truncateHash, digestBits]

end LeanSphincsProofs
