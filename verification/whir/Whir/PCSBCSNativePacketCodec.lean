import Whir.PCSBCSNativePacketBridge
import Whir.WHIRRawReplay

/-! Full native GroupAnswer blocks are cast by their literal block count, and
then decoded by the same contiguous byte cursor as PCS grouped answers. This is
pointwise equality, not an equality of distributions or of output-cache words. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
namespace Whir.PCSBCSNativePacketCodec
open Concrete Protocol CausalProbability CausalGame FiatShamirGame PCSBCSRounds
open PCSBCSChallengeOracle PCSBCSNativePacketBridge

private theorem vectorBytes_slice (n : Nat) (v : Fin n → E) (i : Fin n) (j : Fin 24) :
    vectorBytes n v ⟨24*i.val+j.val, by omega⟩ = ByteCodec.encodeE (v i) j := by
  have hd : (24*i.val+j.val)/24 = i.val := by omega
  have hm : (24*i.val+j.val)%24 = j.val := by omega
  change ByteCodec.encodeE (v ⟨(24*i.val+j.val)/24, _⟩)
    ⟨(24*i.val+j.val)%24, _⟩ = _
  congr 2
  · exact Fin.ext hd

private theorem byte_at {n : Nat} (v : Fin n → Byte) (i : Nat) (hi : i < n) :
    (List.ofFn v)[i]! = v ⟨i,hi⟩ := by
  rw [getElem!_pos _ _ (by simpa using hi)]
  exact List.getElem_ofFn _
private theorem initial_map {c : Config} (x : Raw (.initial : Coordinate c)) (a : Fin 6) :
    rawVector .initial x a.succ.castSucc = x.1.2 a := by
  change Sum.elim (fun z : Fin 7 =>
    Sum.elim (fun _ : Fin 1 => x.1.1) x.1.2 (finSumFinEquiv.symm z))
    (fun _ : Fin 1 => x.2) (finSumFinEquiv.symm a.succ.castSucc) = _
  rw [finSumFinEquiv_symm_apply_castSucc]
  simp only [Sum.elim_inl]
  have h : a.succ = Fin.natAdd 1 a := Fin.ext (by simp [Nat.add_comm])
  rw [h, finSumFinEquiv_symm_apply_natAdd]
  rfl

private theorem query_chunk {c : Config} (i : Fin c.folds.size)
    (x : Raw (.query i)) (a : Fin (queryChunks c i.val)) :
    rawVector (.query i) x a.castSucc = x.1 a := by
  change Sum.elim x.1 (fun _ : Fin 1 => x.2) (finSumFinEquiv.symm a.castSucc) = _
  rw [finSumFinEquiv_symm_apply_castSucc]
  rfl

private theorem query_lambda {c : Config} (i : Fin c.folds.size) (x : Raw (.query i)) :
    rawVector (.query i) x (Fin.last _) = x.2 := by
  change Sum.elim x.1 (fun _ : Fin 1 => x.2) (finSumFinEquiv.symm (Fin.last _)) = _
  rw [finSumFinEquiv_symm_last]
  rfl


private theorem decodeSlice (n : Nat) (v : Fin n → E) (i : Fin n) :
    WHIRFiatShamir.scalarCodec (fun j =>
      (List.ofFn (vectorBytes n v))[24*i.val+j.val]!) = v i := by
  apply WHIRFiatShamir.scalarCodec.symm.injective
  rw [Equiv.symm_apply_apply]
  funext j
  rw [byte_at _ (24*i.val+j.val) (by have := i.isLt; have := j.isLt; omega)]
  exact vectorBytes_slice n v i j

/-- Stream decoding inverts the literal PCS byte representation. -/
theorem decodeBytes_vector {c : Config} (q : Coordinate c) (x : Raw q) :
    StackWHIRCodec.decodeBytes q
      (List.ofFn (vectorBytes (rawWidth q) (rawVector q x))) = x := by
  cases q with
  | initial =>
    simp only [StackWHIRCodec.decodeBytes, StackWHIRCodec.initialCodec,
      Equiv.prodCongr_apply, Prod.map, StackWHIRCodec.initialSlices, rawWidth, WHIRHistory.stackScalarCount]
    apply Prod.ext
    · apply Prod.ext
      · have h := decodeSlice 8 (rawVector (.initial : Coordinate c) x) 0
        rw [show rawVector (.initial : Coordinate c) x (0 : Fin 8) = x.1.1 from rfl] at h
        exact h
      · funext a
        have h := decodeSlice 8 (rawVector (.initial : Coordinate c) x) a.succ.castSucc
        rw [initial_map] at h
        exact h
    · have h := decodeSlice 8 (rawVector (.initial : Coordinate c) x) 7
      rw [show rawVector (.initial : Coordinate c) x (7 : Fin 8) = x.2 from rfl] at h
      exact h
  | fold i j =>
    simp only [StackWHIRCodec.decodeBytes, WHIRFiatShamir.codec, WHIRROM.slices,
      rawWidth, WHIRHistory.stackScalarCount, WHIRHistory.scalarCount]
    have h := decodeSlice 1 (rawVector (.fold i j) x) 0
    rw [show rawVector (.fold i j) x (0 : Fin 1) = x from rfl] at h
    exact h
  | ood i j =>
    simp only [StackWHIRCodec.decodeBytes, WHIRFiatShamir.codec, WHIRROM.slices,
      rawWidth, WHIRHistory.stackScalarCount, WHIRHistory.scalarCount]
    funext a
    exact decodeSlice _ x a
  | query i =>
    simp only [StackWHIRCodec.decodeBytes, WHIRFiatShamir.codec, WHIRROM.slices,
      Equiv.prodCongr_apply, rawWidth, WHIRHistory.stackScalarCount, WHIRHistory.scalarCount]
    apply Prod.ext
    · funext a
      have h := decodeSlice _ (rawVector (.query i) x) a.castSucc
      rw [query_chunk] at h
      exact h
    · have h := decodeSlice _ (rawVector (.query i) x) (Fin.last _)
      rw [query_lambda] at h
      exact h
  | tail j =>
    simp only [StackWHIRCodec.decodeBytes, WHIRFiatShamir.codec, WHIRROM.slices,
      rawWidth, WHIRHistory.stackScalarCount, WHIRHistory.scalarCount]
    have h := decodeSlice 1 (rawVector (.tail j) x) 0
    rw [show rawVector (.tail j) x (0 : Fin 1) = x from rfl] at h
    exact h

theorem blockCount_eq {c : Config} (q : Coordinate c) :
    StackWHIRCodec.outputBlocks q = blocks (rawWidth q) := by
  rw [StackWHIRCodec.outputBlocks_eq]
  simp only [blocks, rawWidth, Nat.mul_comm]

/-- A literal index cast retains every byte of every full output block. -/
def fullBlocksEquiv {c : Config} (q : Coordinate c) :
    (Fin (StackWHIRCodec.outputBlocks q) → Digest32) ≃
      (Fin (blocks (rawWidth q)) → Digest32) :=
  Equiv.arrowCongr (finCongr (blockCount_eq q)) (Equiv.refl Digest32)

/-- The byte-level codec bridge covers initial, fold, OOD, query and tail
without discarding the high query bits or the last block's unused suffix. -/
theorem blockDecode_eq_grouped {c : Config} (q : Coordinate c)
    (raw : Fin (StackWHIRCodec.outputBlocks q) → Digest32) :
    StackWHIRCodec.blockDecode q raw = grouped q (fullBlocksEquiv q raw) := by
  rw [StackWHIRCodec.blockDecode_eq_bytes]
  calc
    _ = StackWHIRCodec.decodeBytes q
        (List.ofFn (vectorBytes (rawWidth q)
          (rawVector q (grouped q (fullBlocksEquiv q raw))))) := by
      apply congrArg (StackWHIRCodec.decodeBytes q)
      apply congrArg List.ofFn
      funext j
      rw [grouped_payload_bytes]
      rfl
    _ = _ := decodeBytes_vector q _

variable (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack) (Q : Nat)

/-- Native grouped answers and PCS grouped answers differ only in their Fin
index proof. This equivalence, including its inverse, retains full blocks. -/
def nativeFullBlocksEquiv (packet : RawWHIRKeys.Packet ctx Q) :
    RawOracleCoupling.Concrete.GroupAnswer ctx Q (.inl packet) ≃
      (Fin (blocks (rawWidth (query ctx Q packet))) → Digest32) :=
  (WHIRRawReplay.packetEquiv ctx stack Q packet).trans
    (fullBlocksEquiv (query ctx Q packet))

theorem nativeFullBlocksEquiv_apply (packet : RawWHIRKeys.Packet ctx Q)
    (raw : RawOracleCoupling.Concrete.GroupAnswer ctx Q (.inl packet))
    (b : Fin (blocks (rawWidth (query ctx Q packet)))) :
    nativeFullBlocksEquiv ctx stack Q packet raw b =
      raw ⟨b.val, by
        rw [WHIRRawReplay.packet_blocks ctx stack Q packet, blockCount_eq]
        exact b.isLt⟩ := rfl

/-- Pointwise equality for the actual native full-block answer, not a scalar
cache or an equality-in-distribution substitute. -/
theorem decodePacket_eq_grouped (packet : RawWHIRKeys.Packet ctx Q)
    (raw : RawOracleCoupling.Concrete.GroupAnswer ctx Q (.inl packet)) :
    WHIRRawReplay.decodePacket ctx stack Q packet raw =
      grouped (query ctx Q packet) (nativeFullBlocksEquiv ctx stack Q packet raw) :=
  blockDecode_eq_grouped (query ctx Q packet) (WHIRRawReplay.packetEquiv ctx stack Q packet raw)

#print axioms blockDecode_eq_grouped
#print axioms decodePacket_eq_grouped

end Whir.PCSBCSNativePacketCodec
