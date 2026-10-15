import SphincsFors.Scheme

/-! Byte encoding and domain separation; adapted from leanVM b7a107256. -/
namespace SphincsFors
theorem bytesLE_injective {n : Nat} {x y : BitVec (8 * n)} (h : bytesLE n x = bytesLE n y) :
    x = y := by
  have hfun := List.ofFn_inj.mp h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hj : i / 8 < n := by omega
  have hbyte := congrFun hfun ⟨i / 8, hj⟩
  have hbits : (x.extractLsb' (8 * (i / 8)) 8) = (y.extractLsb' (8 * (i / 8)) 8) := by
    simpa using congrArg UInt8.toBitVec hbyte
  have hlsb := congrArg (fun b : BitVec 8 => b.getLsbD (i % 8)) hbits
  simp only [BitVec.getLsbD_extractLsb'] at hlsb
  have hmod : i % 8 < 8 := by omega
  have hsum : 8 * (i / 8) + i % 8 = i := by omega
  simpa [hmod, hsum] using hlsb

theorem bytesLE_length (n : Nat) (x : BitVec (8 * n)) : (bytesLE n x).length = n := by
  simp [bytesLE]

/-- A bit vector determines the natural it encodes, below the wrap. -/
theorem ofNat_inj_of_lt {w a b : Nat} (ha : a < 2 ^ w) (hb : b < 2 ^ w)
    (h : BitVec.ofNat w a = BitVec.ofNat w b) : a = b := by
  have htoNat := congrArg BitVec.toNat h
  rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at htoNat

/-- The 16 address bytes determine the type, the step and both fields. -/
theorem fieldBytes_injective {t1 t2 : TweakFields} (h : fieldBytes t1 = fieldBytes t2) : t1 = t2 := by
  obtain ⟨tag1, step1, hi1, lo1⟩ := t1
  obtain ⟨tag2, step2, hi2, lo2⟩ := t2
  simp only [fieldBytes] at h
  have h := List.append_cancel_right h
  obtain ⟨h, htag⟩ := List.append_inj' h (by simp [bytesLE_length])
  obtain ⟨hlo, hhi⟩ := List.append_inj' h (by simp [bytesLE_length])
  have h1 := tag1.isLt
  have h2 := tag2.isLt
  have h3 := step1.isLt
  have h4 := step2.isLt
  have htag := ofNat_inj_of_lt (by omega) (by omega) (bytesLE_injective htag)
  have ht : tag1 = tag2 := BitVec.eq_of_toNat_eq (by omega)
  have hs : step1 = step2 := BitVec.eq_of_toNat_eq (by omega)
  simp only [ht, hs, bytesLE_injective hhi, bytesLE_injective hlo]

/-- The layout test of `crates/sphincs/src/hash.rs`: type `10`, step `5`, `hi = 0x123456`,
`lo = 0x89abcdef`. -/
theorem fieldBytes_layout_example :
    fieldBytes (tweakFields 10 5 0x123456 0x89abcdef) =
      [0xef, 0xcd, 0xab, 0x89, 0x56, 0x34, 0x12, 0xaa, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide

theorem fieldBytes_length (fields : TweakFields) : (fieldBytes fields).length = 16 := by
  simp [fieldBytes, bytesLE_length]

/-- A digest call hashes 80 bytes, `P || A || m || rho`: the first 64-byte block ends with the
message and the second is the randomizer (`randomizer_and_digest_inputs` in
`crates/sphincs/src/scheme.rs`). -/
theorem messageDigestInput_length (parameter : PublicParameter) (root : Digest) (message : Message)
    (randomness : Randomness) (call : Fin 2) :
    (tweakableHashInput parameter (.message call)
      (Concrete.messageDigestPayload root message randomness)).length = 80 := by
  simp [tweakableHashInput, tweakBytes, fieldBytes_length, Concrete.messageDigestPayload,
    bytesLE_length]

/-- The scheme has one layer and one tree: these two arguments of a call are not serialized. -/
theorem layer_eq (lay lay' : Layer) : lay = lay' := by
  have h := lay.isLt
  have h' := lay'.isLt
  simp only [numLayers] at h h'
  exact Fin.ext (by omega)

theorem treeIndex_eq (tree tree' : TreeIndex) : tree = tree' := Subsingleton.elim _ _

end SphincsFors
