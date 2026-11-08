import FORS.Scheme.Lemmas

/-! Byte encoding and domain separation. -/
namespace FORS

variable [Params]
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

theorem bytesBE_length (n : Nat) (x : BitVec (8 * n)) : (bytesBE n x).length = n := by
  simp [bytesBE]

theorem bytesBE_injective {n : Nat} {x y : BitVec (8 * n)} (h : bytesBE n x = bytesBE n y) :
    x = y := by
  have hfun := List.ofFn_inj.mp h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hj : n - 1 - i / 8 < n := by omega
  have hbyte := congrFun hfun ⟨n - 1 - i / 8, hj⟩
  have hidx : n - 1 - (n - 1 - i / 8) = i / 8 := by omega
  simp only [hidx] at hbyte
  have hbits : (x.extractLsb' (8 * (i / 8)) 8) = (y.extractLsb' (8 * (i / 8)) 8) := by
    simpa using congrArg UInt8.toBitVec hbyte
  have hlsb := congrArg (fun b : BitVec 8 => b.getLsbD (i % 8)) hbits
  simp only [BitVec.getLsbD_extractLsb'] at hlsb
  have hmod : i % 8 < 8 := by omega
  have hsum : 8 * (i / 8) + i % 8 = i := by omega
  simpa [hmod, hsum] using hlsb

theorem flatMap_bytesLE_length (values : List Digest) :
    (values.flatMap (bytesLE 16)).length = 16 * values.length := by
  simp [List.length_flatMap, bytesLE_length]
  exact Nat.mul_comm _ _

theorem ofFn_flatMap_bytesLE_length {n : Nat} (values : Fin n → Digest) :
    ((List.ofFn values).flatMap (bytesLE 16)).length = 16 * n := by
  rw [flatMap_bytesLE_length, List.length_ofFn]

theorem nodePayload_length (left right : Digest) : (Concrete.nodePayload left right).length = 32 := by
  simp [Concrete.nodePayload, bytesLE_length]

theorem leafPayload_length (endpoints : ChainIndex → Digest) : (Concrete.leafPayload endpoints).length = 1024 := by
  rw [Concrete.leafPayload, ofFn_flatMap_bytesLE_length]
  rfl

theorem rootsPayload_length (roots : ForsKey) : (Concrete.rootsPayload roots).length = 16 * forsTrees := by
  rw [Concrete.rootsPayload, ofFn_flatMap_bytesLE_length]

theorem rootPayload_length (root : Digest) : (Concrete.rootPayload root).length = 16 :=
  bytesLE_length 16 root

theorem tweakableHashInput_length (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    (tweakableHashInput parameter domain payload).length = 48 + payload.length := by
  simp only [tweakableHashInput, tweakBytes, fieldBytes, List.length_append, bytesLE_length, bytesBE_length]

theorem keygenHashInput_length (parameter : PublicParameter) (domain : KeygenDomain) (seed : MasterSeed) :
    (keygenHashInput parameter domain seed).length = 80 := by
  simp only [keygenHashInput, fieldBytes, List.length_append, bytesLE_length, bytesBE_length]

/-- The 32 address bytes determine every word of the address. -/
theorem fieldBytes_injective {t1 t2 : TweakFields} (h : fieldBytes t1 = fieldBytes t2) : t1 = t2 := by
  obtain ⟨layer1, tree1, tag1, key1, height1, index1⟩ := t1
  obtain ⟨layer2, tree2, tag2, key2, height2, index2⟩ := t2
  simp only [fieldBytes] at h
  obtain ⟨h, hindex⟩ := List.append_inj' h (by simp [bytesBE_length])
  obtain ⟨h, hheight⟩ := List.append_inj' h (by simp [bytesBE_length])
  obtain ⟨h, hkey⟩ := List.append_inj' h (by simp [bytesBE_length])
  obtain ⟨h, htag⟩ := List.append_inj' h (by simp [bytesBE_length])
  obtain ⟨hlayer, htree⟩ := List.append_inj' h (by simp [bytesBE_length])
  simp only [bytesBE_injective hlayer, bytesBE_injective htree, bytesBE_injective htag,
    bytesBE_injective hkey, bytesBE_injective hheight, bytesBE_injective hindex]

end FORS
