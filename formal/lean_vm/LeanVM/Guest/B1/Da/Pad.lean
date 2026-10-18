/-
  LeanVM.Guest.B1.Da.Pad

  The padding digests of LeanDA (`DA_PAD_CELL`, `DA_PAD_ROW`), computed by the kernel.
-/

module

public import LeanVM.Spec.Blake2s

/-!
# The padding digests

The zero cell's digest is BLAKE2s of 2048 zero bytes, and the zero row's is BLAKE2s of 64 copies of
the zero cell's digest. Each is checked by `decide +kernel`, eight compressions to a theorem at
the intermediate chaining values (`nfChain`, `absorb_step`), so that no one check holds the whole
computation.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash

@[expose] public section

/-- `k` non-final compressions of `absorb`. -/
def nfChain (h : Vector UInt32 8) (t : ℕ) : ℕ → List UInt8 → Vector UInt32 8
  | 0, _ => h
  | k + 1, data =>
      nfChain (compress h (blockWords (data.take 64)) (t + 64).toUInt64 0 0) (t + 64) k (data.drop 64)

theorem absorb_nfChain : ∀ (k : ℕ) (h : Vector UInt32 8) (t blocks : ℕ) (data : List UInt8),
    absorb h t (k + blocks) data = absorb (nfChain h t k data) (t + 64 * k) blocks (data.drop (64 * k))
  | 0, h, t, blocks, data => by simp [nfChain]
  | k + 1, h, t, blocks, data => by
    have e1 : t + 64 + 64 * k = t + 64 * (k + 1) := by ring
    have e2 : (data.drop 64).drop (64 * k) = data.drop (64 * (k + 1)) := by
      rw [List.drop_drop]; congr 1; ring
    rw [show k + 1 + blocks = (k + blocks) + 1 by omega, absorb, absorb_nfChain k, nfChain, e1, e2]

theorem absorb_step {h h' : Vector UInt32 8} {t k blocks : ℕ} {data rest : List UInt8}
    (hd : data.drop (64 * k) = rest) (hc : (nfChain h t k data).toList = h'.toList) :
    absorb h t (k + blocks) data = absorb h' (t + 64 * k) blocks rest := by
  rw [absorb_nfChain, Vector.toList_inj.mp hc, hd]

/-! ## The zero cell -/

def zc8 : Vector UInt32 8 :=
  #v[3406951921, 2786846549, 803207569, 2794252175, 273801315, 581563985, 4040587545, 137356329]
def zc16 : Vector UInt32 8 :=
  #v[1881059958, 3945110025, 3070114056, 4274235166, 3126016639, 2918274478, 3429877400, 3949620066]
def zc24 : Vector UInt32 8 :=
  #v[2367246506, 568093020, 1458743946, 2459541779, 1440050333, 4163901474, 1343017114, 310115709]

/-- The zero cell's digest. -/
def padCellD : Digest :=
  #v[328405102, 1003712108, 498679449, 4281136787, 1273881865, 4225404059, 3663672688, 3473285307]

theorem zc_8 : (nfChain paramIv 0 8 (List.replicate 2048 0)).toList = zc8.toList := by decide +kernel
theorem zc_16 : (nfChain zc8 512 8 (List.replicate 1536 0)).toList = zc16.toList := by decide +kernel
theorem zc_24 : (nfChain zc16 1024 8 (List.replicate 1024 0)).toList = zc24.toList := by decide +kernel
theorem zc_32 : (absorb zc24 1536 7 (List.replicate 512 0)).toList = padCellD.toList := by decide +kernel

/-- **The zero cell's digest** (`DA_PAD_CELL`): BLAKE2s of 2048 zero bytes. -/
theorem blake2s_zeros : blake2sBytes (List.replicate 2048 0) = padCellD := by
  rw [blake2sBytes, List.length_replicate]
  show absorb paramIv 0 (8 + 23) _ = _
  rw [absorb_step (List.drop_replicate ..) zc_8]
  show absorb zc8 512 (8 + 15) _ = _
  rw [absorb_step (List.drop_replicate ..) zc_16]
  show absorb zc16 1024 (8 + 7) _ = _
  rw [absorb_step (List.drop_replicate ..) zc_24]
  exact Vector.toList_inj.mp zc_32

/-! ## The zero row -/

/-- `n` copies of the zero cell's digest, as bytes. -/
def rowData (n : ℕ) : List UInt8 := (List.replicate n padCellD).flatMap digestBytes

def zr8 : Vector UInt32 8 :=
  #v[1842834807, 3028008286, 571439698, 2995762541, 140347509, 2934872702, 2298802263, 1972261099]
def zr16 : Vector UInt32 8 :=
  #v[2893789707, 2287994067, 1500112247, 930482079, 244456752, 682336978, 4066804476, 320097468]
def zr24 : Vector UInt32 8 :=
  #v[2018948279, 4255050020, 134233066, 1662995455, 3178604928, 1388420069, 3942887306, 3967099823]

/-- The zero row's digest. -/
def padRowD : Digest :=
  #v[448483255, 3690025497, 3906751961, 2883423376, 4098215269, 3529201093, 1606640541, 338389171]

theorem zr_8 : (nfChain paramIv 0 8 (rowData 64)).toList = zr8.toList := by decide +kernel
theorem zr_16 : (nfChain zr8 512 8 (rowData 48)).toList = zr16.toList := by decide +kernel
theorem zr_24 : (nfChain zr16 1024 8 (rowData 32)).toList = zr24.toList := by decide +kernel
theorem zr_32 : (absorb zr24 1536 7 (rowData 16)).toList = padRowD.toList := by decide +kernel

theorem rowData_drop {a b : ℕ} : (rowData (16 * a + b)).drop (64 * (8 * a)) = rowData b := by
  rw [rowData, List.replicate_add, List.flatMap_append, show 64 * (8 * a) = 512 * a by ring]
  have : ((List.replicate (16 * a) padCellD).flatMap digestBytes).length = 512 * a := by
    simp [List.length_flatMap, digestBytes, wordBytes]; ring
  rw [← this, List.drop_left]; rfl

theorem rowData_length (n : ℕ) : (rowData n).length = 32 * n := by
  simp [rowData, List.length_flatMap, digestBytes, wordBytes]; ring

/-- **The zero row's digest** (`DA_PAD_ROW`): BLAKE2s of 64 zero cell digests. -/
theorem blake2s_padRow : blake2sBytes (rowData 64) = padRowD := by
  rw [blake2sBytes, rowData_length]
  show absorb paramIv 0 (8 + 23) (rowData 64) = _
  rw [absorb_step (rowData_drop (a := 1) (b := 48) : (rowData 64).drop (64 * 8) = rowData 48) zr_8]
  show absorb zr8 512 (8 + 15) (rowData 48) = _
  rw [absorb_step (rowData_drop (a := 1) (b := 32) : (rowData 48).drop (64 * 8) = rowData 32) zr_16]
  show absorb zr16 1024 (8 + 7) (rowData 32) = _
  rw [absorb_step (rowData_drop (a := 1) (b := 16) : (rowData 32).drop (64 * 8) = rowData 16) zr_24]
  exact Vector.toList_inj.mp zr_32

end
end LeanVM.Guest.B1.Digest
