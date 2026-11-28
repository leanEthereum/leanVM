module

public import NativeRustc.Sphincs.SigMem
public import NativeRustc.Sphincs.ParseBytes

/-!
# The parsed signature from the raw signature's slices

`sigMem` of the signature parsed from the input words (`sigMem_eq`), in the pieces a parse
assembles it from: the FORS openings (`obytes c`: the path, then the secret), the paths
(`pbytes`), the randomizer, and the layers (`lbytes l`: the chain values, then the counter
little-endian), each a slice of the raw signature `sigBytes w` or a counter word. The raw
signature in the pieces x86-64's word loops write (`sigBytes_runs`).
-/

@[expose] public section

namespace NativeRustc.Sphincs.ParseMem

open LeanVM.Protocol.KeccakHash Native.Keccak

/-- FORS opening `c` in rustc's layout: its path, then its secret. -/
def obytes (w : Nat → UInt64) (c : Nat) : List UInt8 :=
  slice (sigBytes w) (32 + 176 * c) 160 ++ slice (sigBytes w) (16 + 176 * c) 16

/-- The three layers' paths. -/
def pbytes (w : Nat → UInt64) : List UInt8 :=
  slice (sigBytes w) 5268 128 ++ (slice (sigBytes w) 6424 128 ++ slice (sigBytes w) 7580 160)

/-- Layer `l` in rustc's layout: its chain values, then its counter little-endian. -/
def lbytes (w : Nat → UInt64) (l : Nat) : List UInt8 :=
  slice (sigBytes w) (sigLayerOff l + 4) 1024 ++ le32 (w (layerWordOff l)).toUInt32

theorem length_slice_sig (w : Nat → UInt64) {a n : Nat} (h : a + n ≤ 7740) :
    (slice (sigBytes w) a n).length = n :=
  length_slice (by rw [length_sigBytes]; exact h)

theorem length_obytes (w : Nat → UInt64) {c : Nat} (hc : c < 24) : (obytes w c).length = 176 := by
  rw [obytes, List.length_append, length_slice_sig w (by omega), length_slice_sig w (by omega)]

theorem length_openings (w : Nat → UInt64) : ∀ {c : Nat}, c ≤ 24 →
    ((List.range c).map (obytes w)).flatten.length = 176 * c
  | 0, _ => rfl
  | c + 1, h => by
    rw [List.range_succ, List.map_append, List.flatten_append, List.length_append,
      length_openings w (by omega)]
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil,
      length_obytes w (show c < 24 by omega)]
    omega

theorem length_pbytes (w : Nat → UInt64) : (pbytes w).length = 416 := by
  simp only [pbytes, List.length_append, length_slice_sig w (show 5268 + 128 ≤ 7740 by decide),
    length_slice_sig w (show 6424 + 128 ≤ 7740 by decide),
    length_slice_sig w (show 7580 + 160 ≤ 7740 by decide)]

theorem length_le32 (x : UInt32) : (le32 x).length = 4 := by simp [le32, be32]

theorem length_lbytes (w : Nat → UInt64) {l : Nat} (hl : l < 3) : (lbytes w l).length = 1028 := by
  rw [lbytes, List.length_append, length_le32, length_slice_sig w (by
    have := sigLayerOff_le hl; interval_cases l <;> decide)]

/-- **The parsed signature in rustc's layout**, from the raw signature's slices. -/
theorem sigMem_eq (w : Nat → UInt64) :
    sigMem (sigOf w) = ((List.range 24).map (obytes w)).flatten ++ (pbytes w ++
      (slice (sigBytes w) 0 16 ++ (lbytes w 0 ++ (lbytes w 1 ++ lbytes w 2)))) := by
  have hf : ((sigOf w).fors.map openingMem).flatten = ((List.range 24).map (obytes w)).flatten := by
    rw [SigMem.sig_fors, List.map_map]
    refine congrArg List.flatten (List.map_congr_left fun c _ ↦ ?_)
    simp only [Function.comp, openingMem, obytes]
    rw [flatten_slices]
  have hp : (sigOf w).paths.flatten = pbytes w := by
    simp only [SigMem.sig_paths, show List.range 3 = [0, 1, 2] from rfl, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, List.flatten_append, pbytes]
    rw [flatten_slices, flatten_slices, flatten_slices]
    rfl
  have hl : ∀ l, l < 3 → layerMem ⟨be32Of (slice (sigBytes w) (sigLayerOff l) 4),
      (List.range 64).map fun i ↦ slice (sigBytes w) (sigLayerOff l + 4 + 16 * i) 16⟩ =
      lbytes w l := fun l hl ↦ by
    rw [layerMem, lbytes, slice_counter w hl, be32Of_be32]
    simp only
    rw [flatten_slices]
  have hL : ((sigOf w).layers.map layerMem).flatten = lbytes w 0 ++ (lbytes w 1 ++ lbytes w 2) := by
    simp only [SigMem.sig_layers, show List.range 3 = [0, 1, 2] from rfl, List.map_cons,
      List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
    rw [hl 0 (by decide), hl 1 (by decide), hl 2 (by decide)]
  rw [sigMem, hf, hp, SigMem.sig_randomizer, hL]

/-- **The raw signature in x86-64's runs**: words `8 .. 537`, then per layer its counter
(big-endian) and its words. -/
theorem sigBytes_runs (w : Nat → UInt64) :
    sigBytes w = wb w 8 530 ++ (be32 (w 538).toUInt32 ++ (wb w 539 144 ++
      (be32 (w 683).toUInt32 ++ (wb w 684 144 ++ (be32 (w 828).toUInt32 ++ wb w 829 148))))) := by
  simp only [sigBytes, show List.range 3 = [0, 1, 2] from rfl, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.append_assoc]
  rfl

/-! ## Raw signature bytes directly -/

/-- FORS opening `c` in rustc's layout from raw signature bytes `sb`. -/
def obytesB (sb : List UInt8) (c : Nat) : List UInt8 :=
  slice sb (32 + 176 * c) 160 ++ slice sb (16 + 176 * c) 16

/-- The three layers' paths from raw signature bytes `sb`. -/
def pbytesB (sb : List UInt8) : List UInt8 :=
  slice sb 5268 128 ++ (slice sb 6424 128 ++ slice sb 7580 160)

/-- Layer `l` in rustc's layout from raw signature bytes `sb`: chain values then counter little-endian. -/
def lbytesB (sb : List UInt8) (l : Nat) : List UInt8 :=
  slice sb (sigLayerOff l + 4) 1024 ++ (slice sb (sigLayerOff l) 4).reverse

theorem length_obytesB {sb : List UInt8} (hsb : sb.length = 7740) {c : Nat} (hc : c < 24) :
    (obytesB sb c).length = 176 := by
  rw [obytesB, List.length_append, length_slice (by omega), length_slice (by omega)]

theorem length_openingsB {sb : List UInt8} (hsb : sb.length = 7740) : ∀ {c : Nat}, c ≤ 24 →
    ((List.range c).map (obytesB sb)).flatten.length = 176 * c
  | 0, _ => rfl
  | c + 1, h => by
    rw [List.range_succ, List.map_append, List.flatten_append, List.length_append,
      length_openingsB hsb (by omega)]
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil,
      length_obytesB hsb (show c < 24 by omega)]
    omega

theorem length_pbytesB {sb : List UInt8} (hsb : sb.length = 7740) : (pbytesB sb).length = 416 := by
  simp only [pbytesB, List.length_append, length_slice (show 5268 + 128 ≤ sb.length by omega),
    length_slice (show 6424 + 128 ≤ sb.length by omega),
    length_slice (show 7580 + 160 ≤ sb.length by omega)]

theorem length_lbytesB {sb : List UInt8} (hsb : sb.length = 7740) {l : Nat} (hl : l < 3) :
    (lbytesB sb l).length = 1028 := by
  have := sigLayerOff_le hl
  have hl0 : sigLayerOff l + 1028 ≤ 7740 := by interval_cases l <;> decide
  rw [lbytesB, List.length_append, List.length_reverse, length_slice (by omega), length_slice (by omega)]

/-- **The parsed signature in rustc's layout**, directly from raw 7740 signature bytes. -/
theorem sigMem_eq_bytes {sb : List UInt8} (hsb : sb.length = 7740) :
    sigMem (sigOfBytes sb) = ((List.range 24).map (obytesB sb)).flatten ++ (pbytesB sb ++
      (slice sb 0 16 ++ (lbytesB sb 0 ++ (lbytesB sb 1 ++ lbytesB sb 2)))) := by
  have hf : ((sigOfBytes sb).fors.map openingMem).flatten = ((List.range 24).map (obytesB sb)).flatten := by
    rw [SigMemBytes.sig_fors, List.map_map]
    refine congrArg List.flatten (List.map_congr_left fun c _ ↦ ?_)
    simp only [Function.comp, openingMem, obytesB]
    rw [flatten_slices]
  have hp : (sigOfBytes sb).paths.flatten = pbytesB sb := by
    simp only [SigMemBytes.sig_paths, show List.range 3 = [0, 1, 2] from rfl, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, List.flatten_append, pbytesB]
    rw [flatten_slices, flatten_slices, flatten_slices]
    rfl
  have hl : ∀ l, l < 3 → layerMem ⟨be32Of (slice sb (sigLayerOff l) 4),
      (List.range 64).map fun i ↦ slice sb (sigLayerOff l + 4 + 16 * i) 16⟩ =
      lbytesB sb l := fun l hl ↦ by
    have hle : sigLayerOff l + 4 ≤ sb.length := by rw [hsb]; interval_cases l <;> decide
    rw [layerMem, lbytesB, le32, le32_be32Of (slice sb (sigLayerOff l) 4) (length_slice hle)]
    simp only
    rw [flatten_slices]
  have hL : ((sigOfBytes sb).layers.map layerMem).flatten =
      lbytesB sb 0 ++ (lbytesB sb 1 ++ lbytesB sb 2) := by
    simp only [SigMemBytes.sig_layers, show List.range 3 = [0, 1, 2] from rfl, List.map_cons,
      List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
    rw [hl 0 (by decide), hl 1 (by decide), hl 2 (by decide)]
  rw [sigMem, hf, hp, SigMemBytes.sig_randomizer, hL]

end NativeRustc.Sphincs.ParseMem
