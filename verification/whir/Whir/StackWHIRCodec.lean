import Whir.StackWHIRROM
import Whir.WHIRROM

/-! Exact packet decoding for the stacked alphabet. The first allocation is
192 contiguous bytes, or six independent 32-byte blocks, in gamma, map, lambda
order. Later vectors reuse the checked WHIR whole-block padding projection. -/
namespace Whir.StackWHIRCodec
open Concrete Protocol CausalGame CausalProbability ParameterBounds
open FiatShamirGame (Byte Digest32 Scalar24 average)
open WHIRFiatShamir (scalarCodec codec)
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

abbrev InitialBytes := (Scalar24 × (Fin 6 → Scalar24)) × Scalar24

def prependScalar (n : Nat) : (Scalar24 × (Fin n → Scalar24)) ≃ (Fin (n+1) → Scalar24) where
  toFun p := Fin.cases p.1 p.2
  invFun f := (f 0,fun i => f i.succ)
  left_inv p := by
    apply Prod.ext
    · rfl
    · funext i; rfl
  right_inv f := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl

/-- Gamma occupies slot zero, the six map draws slots one through six, and
lambda slot seven. No response boundary is inserted between these scalars. -/
def initialVector : InitialBytes ≃ (Fin 8 → Scalar24) :=
  (Equiv.prodCongr (prependScalar 6) (Equiv.refl Scalar24)).trans (WHIRROM.appendScalar 7)

def initialCodec : InitialBytes ≃ (RingPCSGame.Prefix × E) :=
  Equiv.prodCongr (Equiv.prodCongr scalarCodec (Equiv.piCongrRight (fun _ => scalarCodec))) scalarCodec

def initialPacked : InitialBytes ≃ (Fin 192 → Byte) :=
  initialVector.trans ((Equiv.curry (Fin 8) (Fin 24) Byte).symm.trans
    (Equiv.arrowCongr finProdFinEquiv (Equiv.refl Byte)))

/-- The actual first packet is bijective, with no padding or discarded bits. -/
def initialBlocks : (Fin 6 → Digest32) ≃ (RingPCSGame.Prefix × E) :=
  ((WHIRROM.blockBytes 6).trans initialPacked.symm).trans initialCodec

def initialSlices (bytes : List Byte) : InitialBytes :=
  ((fun j => bytes[j.val]!,fun i j => bytes[24*(i.val+1)+j.val]!),
    fun j => bytes[168+j.val]!)

private theorem byte_at {n : Nat} (bytes : Fin n → Byte) (i : Nat) (hi : i < n) :
    (List.ofFn bytes)[i]! = bytes ⟨i,hi⟩ := by
  rw [getElem!_pos _ _ (by simpa using hi)]
  exact List.getElem_ofFn _

theorem initialSlices_packed (bytes : Fin 192 → Byte) :
    initialSlices (List.ofFn bytes) = initialPacked.symm bytes := by
  apply Prod.ext
  · apply Prod.ext
    · funext j
      change (List.ofFn bytes)[j.val]! = bytes ⟨j.val,by omega⟩
      exact byte_at bytes j.val (by omega)
    · funext i j
      have h : 24*(i.val+1)+j.val < 192 := by omega
      change (List.ofFn bytes)[24*(i.val+1)+j.val]! = bytes ⟨j.val+24*(i.val+1),by omega⟩
      rw [byte_at bytes _ h]
      congr 1
      apply Fin.ext
      dsimp only
      omega
  · funext j
    have h : 168+j.val < 192 := by omega
    change (List.ofFn bytes)[168+j.val]! = bytes ⟨j.val+168,by omega⟩
    rw [byte_at bytes _ h]
    congr 1
    apply Fin.ext
    dsimp only
    omega

/-- Direct decoder of the actual contiguous output stream. -/
def decodeBytes {c : Config} (q : Coordinate c) (bytes : List Byte) : StackWHIRReplay.Sample q :=
  match q with
  | .initial => initialCodec (initialSlices bytes)
  | .fold i j => codec (.fold i j) (WHIRROM.slices (.fold i j) bytes)
  | .ood i j => codec (.ood i j) (WHIRROM.slices (.ood i j) bytes)
  | .query i => codec (.query i) (WHIRROM.slices (.query i) bytes)
  | .tail j => codec (.tail j) (WHIRROM.slices (.tail j) bytes)

def outputBlocks {c : Config} : Coordinate c → Nat
  | .initial => 6
  | q => WHIRROM.outputBlocks q

theorem outputBlocks_eq {c : Config} (q : Coordinate c) :
    outputBlocks q = (WHIRHistory.stackScalarCount q * 24 + 31) / 32 := by
  cases q with
  | initial => norm_num [outputBlocks,WHIRHistory.stackScalarCount]
  | fold i j => rfl
  | ood i j => rfl
  | query i => rfl
  | tail j => rfl

theorem payload_le_outputBlocks {c : Config} (q : Coordinate c) :
    WHIRHistory.stackScalarCount q * 24 ≤ outputBlocks q * 32 := by
  rw [outputBlocks_eq]
  omega

/-- Each packet is a vector of independently sampled full 32-byte blocks. The
initial packet has exactly six blocks; later partial final blocks are ignored. -/
def blockDecode {c : Config} (q : Coordinate c)
    (raw : Fin (outputBlocks q) → Digest32) : StackWHIRReplay.Sample q :=
  match q with
  | .initial => initialBlocks raw
  | .fold i j => WHIRROM.blockDecode (.fold i j) raw
  | .ood i j => WHIRROM.blockDecode (.ood i j) raw
  | .query i => WHIRROM.blockDecode (.query i) raw
  | .tail j => WHIRROM.blockDecode (.tail j) raw

/-- Packet decoding agrees byte-for-byte with the direct stream decoder. -/
theorem blockDecode_eq_bytes {c : Config} (q : Coordinate c)
    (raw : Fin (outputBlocks q) → Digest32) :
    blockDecode q raw = decodeBytes q (List.ofFn (fun i : Fin (WHIRHistory.stackScalarCount q * 24) =>
      WHIRROM.blockBytes (outputBlocks q) raw
        ⟨i.val,lt_of_lt_of_le i.isLt (payload_le_outputBlocks q)⟩)) := by
  cases q with
  | initial =>
    simp only [blockDecode,decodeBytes,outputBlocks,WHIRHistory.stackScalarCount,
      initialBlocks]
    rw [initialSlices_packed]
    apply congrArg initialCodec
    apply congrArg initialPacked.symm
    funext i
    rfl
  | fold i j =>
    simp only [blockDecode,decodeBytes,outputBlocks,WHIRHistory.stackScalarCount,WHIRROM.blockDecode,
      WHIRHistory.scalarCount]
    apply congrArg (codec (.fold i j))
    apply congrArg (WHIRROM.slices (.fold i j))
    apply congrArg List.ofFn
    funext k
    rfl
  | ood i j =>
    simp only [blockDecode,decodeBytes,outputBlocks,WHIRHistory.stackScalarCount,WHIRROM.blockDecode,
      WHIRHistory.scalarCount]
    apply congrArg (codec (.ood i j))
    apply congrArg (WHIRROM.slices (.ood i j))
    apply congrArg List.ofFn
    funext k
    rfl
  | query i =>
    simp only [blockDecode,decodeBytes,outputBlocks,WHIRHistory.stackScalarCount,WHIRROM.blockDecode,
      WHIRHistory.scalarCount]
    apply congrArg (codec (.query i))
    apply congrArg (WHIRROM.slices (.query i))
    apply congrArg List.ofFn
    funext k
    rfl
  | tail j =>
    simp only [blockDecode,decodeBytes,outputBlocks,WHIRHistory.stackScalarCount,WHIRROM.blockDecode,
      WHIRHistory.scalarCount]
    apply congrArg (codec (.tail j))
    apply congrArg (WHIRROM.slices (.tail j))
    apply congrArg List.ofFn
    funext k
    rfl

/-- Exact every-payoff distribution. The initial proof is a concrete bijection;
all later phases inherit the already checked independent-padding projection. -/
theorem block_average {c : Config} (q : Coordinate c) (f : StackWHIRReplay.Sample q → ℚ) :
    average (fun raw : Fin (outputBlocks q) → Digest32 => f (blockDecode q raw)) = average f := by
  cases q with
  | initial =>
    change average (fun raw : Fin 6 → Digest32 => f (initialBlocks raw)) = average f
    unfold average
    rw [Fintype.sum_equiv initialBlocks _ f (fun _ => rfl),Fintype.card_congr initialBlocks]
  | fold i j => exact WHIRROM.block_average (.fold i j) f
  | ood i j => exact WHIRROM.block_average (.ood i j) f
  | query i => exact WHIRROM.block_average (.query i) f
  | tail j => exact WHIRROM.block_average (.tail j) f

open Classical
/-- The concrete raw-packet sparse event uses the full stacked theorem, never
the standalone initial-E bound. -/
theorem key_block_sparse (p : Profile) (cap : Nat) (catalog : StackWHIRReplay.Catalog p cap)
    (roots : StackWHIRReplay.Roots) (key : StackWHIRReplay.Key p) :
    average (fun raw : Fin (outputBlocks (StackWHIRReplay.query p (key.statement,key.messages))) → Digest32 =>
      if StackWHIRROM.keyBad p cap catalog roots key
        (blockDecode (StackWHIRReplay.query p (key.statement,key.messages)) raw) then 1 else 0) ≤
      WHIRFiatShamir.stackEta p cap := by
  exact (block_average _ (fun x => if StackWHIRROM.keyBad p cap catalog roots key x then 1 else 0)).trans_le
    (StackWHIRROM.key_sparse p cap catalog roots key)

end Whir.StackWHIRCodec
