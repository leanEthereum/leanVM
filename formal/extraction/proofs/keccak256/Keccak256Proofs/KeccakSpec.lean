import Keccak256Proofs.Common
import Hash.Keccak.Equiv
import Hash.Keccak.API

/-!
# The statement's Keccak is hash-specs' Keccak

leanVM's statement of Keccak (`Statement/Keccak.lean`) against hash-specs' (`Hash.Keccak`), which
is proved equal to the FIPS 202 reference:

* `keccakF1600_eq_fast`: the permutation `LeanVM.Semantics.keccakF1600` is
  `Hash.Keccak.Fast.keccakF`, lane for lane;
* `keccak256_eq_hashSpecs`: `LeanVM.Protocol.KeccakHash.keccak256` is `Hash.keccak256` on every
  byte string;
* `keccak256_eq_reference`: hence it is the reference sponge `Hash.Keccak.Reference.keccak256` on
  the message's bits.

The helper lemmas are in `Keccak256Proofs.KeccakSpec`.
-/

open LeanVM.Semantics LeanVM.Parameters Hash.Keccak Hash

namespace Keccak256Proofs.KeccakSpec

theorem rot_eq (x : UInt64) (n : ℕ) (hn : n < 64) :
    Keccak.rot x n = UInt64.rotl x n.toUInt64 := by
  unfold Keccak.rot UInt64.rotl
  split
  · subst n
    change x = x <<< 0 ||| x >>> 0
    simp
  · congr 2
    interval_cases n <;> decide

theorem rot_rho (x : UInt64) (i : ℕ) (hi : i < 25) :
    Keccak.rot x (keccakRho.getD i 0) = UInt64.rotl x (Fast.rhoRotations.getD i 0) := by
  rw [rot_eq]
  · congr 1
    interval_cases i <;> decide
  · interval_cases i <;> decide

theorem lane_eq (a : KeccakState) (i : ℕ) : Keccak.lane a i = Fast.lane a.toArray i := rfl

theorem toArray_ofFn (f : Fin 25 → UInt64) (g : ℕ → UInt64) (h : ∀ i : Fin 25, f i = g i) :
    (Vector.ofFn f).toArray = Fast.tabulate 25 g := by
  apply Array.ext
  · simp [Fast.tabulate]
  · intro i h1 h2
    simp only [Vector.size_toArray] at h1
    simp [Fast.tabulate, h ⟨i, h1⟩]

theorem theta_eq (a : KeccakState) :
    (Vector.ofFn fun i : Fin 25 ↦
      Keccak.lane a i ^^^
        ((Vector.ofFn fun x : Fin 5 ↦ Keccak.lane a x ^^^ Keccak.lane a (x + 5) ^^^
          Keccak.lane a (x + 10) ^^^ Keccak.lane a (x + 15) ^^^ Keccak.lane a (x + 20)).toArray.getD
            ((i.val + 4) % 5) 0) ^^^
        Keccak.rot ((Vector.ofFn fun x : Fin 5 ↦ Keccak.lane a x ^^^ Keccak.lane a (x + 5) ^^^
          Keccak.lane a (x + 10) ^^^ Keccak.lane a (x + 15) ^^^ Keccak.lane a (x + 20)).toArray.getD
            ((i.val + 1) % 5) 0) 1).toArray = Fast.theta a.toArray := by
  unfold Fast.theta
  apply toArray_ofFn
  intro i
  have h5 : (i : ℕ) % 5 < 5 := Nat.mod_lt _ (by decide)
  have h4 : ((i : ℕ) + 4) % 5 < 5 := Nat.mod_lt _ (by decide)
  have h1 : ((i : ℕ) + 1) % 5 < 5 := Nat.mod_lt _ (by decide)
  have e4 : ((i : ℕ) % 5 + 4) % 5 = ((i : ℕ) + 4) % 5 := by omega
  have e1 : ((i : ℕ) % 5 + 1) % 5 = ((i : ℕ) + 1) % 5 := by omega
  simp only [Equiv.lane_tabulate _ _ _ h5, e4, e1, lane_eq, rot_eq _ 1 (by decide)]
  simp [Fast.lane, Fast.tabulate, h4, h1, UInt64.xor_assoc]

theorem rhoPi_eq (a : KeccakState) :
    ((List.range 25).foldl
      (fun b i ↦ b.setIfInBounds (keccakPi i) (Keccak.rot (Keccak.lane a i) (keccakRho.getD i 0)))
      (Vector.replicate 25 0)).toArray = Fast.pi (Fast.rho a.toArray) := by
  apply Array.ext
  · simp [Fast.pi, Fast.tabulate]
  · intro i h1 h2
    simp only [Vector.size_toArray] at h1
    have hj : (i % 5 + 3 * (i / 5)) % 5 + 5 * (i % 5) < 25 := by omega
    have hR : (Fast.pi (Fast.rho a.toArray))[i] =
        UInt64.rotl (Fast.lane a.toArray ((i % 5 + 3 * (i / 5)) % 5 + 5 * (i % 5)))
          (Fast.rhoRotations.getD ((i % 5 + 3 * (i / 5)) % 5 + 5 * (i % 5)) 0) := by
      simp only [Fast.pi, Fast.tabulate, List.getElem_toArray, List.getElem_map,
        List.getElem_range]
      rw [Fast.rho, Equiv.lane_tabulate _ _ _ hj]
    refine Eq.trans ?_ hR.symm
    interval_cases i <;>
      simp [List.range, List.range.loop, keccakPi, -List.getD_eq_getElem?_getD, rot_rho, lane_eq]

theorem chi_eq (b : KeccakState) :
    (Vector.ofFn fun i : Fin 25 ↦
      Keccak.lane b i ^^^ (~~~ Keccak.lane b (i.val - i.val % 5 + (i.val + 1) % 5) &&&
        Keccak.lane b (i.val - i.val % 5 + (i.val + 2) % 5))).toArray = Fast.chi b.toArray := by
  unfold Fast.chi
  apply toArray_ofFn
  intro i
  have e1 : (i : ℕ) - i % 5 + (i + 1) % 5 = (i % 5 + 1) % 5 + 5 * (i / 5) := by omega
  have e2 : (i : ℕ) - i % 5 + (i + 2) % 5 = (i % 5 + 2) % 5 + 5 * (i / 5) := by omega
  simp only [e1, e2, lane_eq]

theorem iota_eq (a : KeccakState) (ir : ℕ) :
    (a.setIfInBounds 0 (Keccak.lane a 0 ^^^ Fast.roundConstantWords.getD ir 0)).toArray =
      Fast.iota a.toArray ir := by
  apply Array.ext
  · simp [Fast.iota, Fast.tabulate]
  · intro i h1 h2
    simp only [Vector.size_toArray] at h1
    rcases i with _ | i <;> simp [Fast.iota, Fast.tabulate, lane_eq, Fast.lane, h1]

theorem round_eq (a : KeccakState) (ir : ℕ) :
    (Keccak.round a (Fast.roundConstantWords.getD ir 0)).toArray = Fast.round a.toArray ir := by
  unfold Keccak.round Fast.round
  simp only
  rw [iota_eq, chi_eq, rhoPi_eq, theta_eq]

theorem foldl_round (l : List ℕ) (a : KeccakState) :
    ((l.map fun ir ↦ Fast.roundConstantWords.getD ir 0).foldl Keccak.round a).toArray =
      l.foldl Fast.round a.toArray := by
  induction l generalizing a with
  | nil => rfl
  | cons ir l ih => rw [List.map_cons, List.foldl_cons, List.foldl_cons, ih, round_eq]

theorem keccakRC_eq :
    keccakRC = (List.range 24).map fun ir ↦ Fast.roundConstantWords.getD ir 0 := by
  decide

end Keccak256Proofs.KeccakSpec

namespace Keccak256Proofs

/-- (A) leanVM's Keccak-f[1600] is hash-specs' lane-level Keccak-f[1600]. -/
theorem keccakF1600_eq_fast (s : LeanVM.Semantics.KeccakState) :
    (LeanVM.Semantics.keccakF1600 s).toArray = Hash.Keccak.Fast.keccakF s.toArray := by
  rw [keccakF1600, KeccakSpec.keccakRC_eq, KeccakSpec.foldl_round, Fast.keccakF]

end Keccak256Proofs

namespace Keccak256Proofs.KeccakSpec

open LeanVM.Protocol LeanVM.Protocol.KeccakHash

/-- hash-specs' absorption of one block (`Fast.absorbBlock 136`), the block given as a list. -/
def absorbBlockL (a : Array UInt64) (block : List UInt8) : Array UInt64 :=
  Fast.keccakF <| Fast.tabulate 25 fun i ↦
    if i < 17 then Fast.lane a i ^^^ littleEndianLane block i else Fast.lane a i

/-- The statement's `absorbWith`, on arrays and over hash-specs' Keccak-f[1600]. -/
def absorbL : ℕ → Array UInt64 → List UInt8 → Array UInt64
  | 0, a, d => absorbBlockL a (padBlock d)
  | k + 1, a, d => absorbL k (absorbBlockL a (d.take 136)) (d.drop 136)

theorem absorbBlockWith_eq (s : KeccakState) (block : List UInt8) :
    (Id.run (absorbBlockWith (fun s ↦ pure (keccakF1600 s)) s block)).toArray =
      absorbBlockL s.toArray block := by
  unfold absorbBlockWith
  rw [Id.run_pure, keccakF1600_eq_fast, absorbBlockL]
  refine congrArg Fast.keccakF ?_
  apply toArray_ofFn
  intro i
  rfl

theorem absorbWith_eq (k : ℕ) (s : KeccakState) (d : List UInt8) :
    (Id.run (absorbWith (fun s ↦ pure (keccakF1600 s)) k s d)).toArray =
      absorbL k s.toArray d := by
  induction k generalizing s d with
  | zero => exact absorbBlockWith_eq s _
  | succ k ih =>
    change (Id.run (absorbWith (fun s ↦ pure (keccakF1600 s)) k
      (Id.run (absorbBlockWith (fun s ↦ pure (keccakF1600 s)) s (d.take 136))) (d.drop 136))).toArray = _
    rw [ih, absorbBlockWith_eq, absorbL]

theorem littleEndianLane_eq (l : List UInt8) (off i : ℕ) :
    littleEndianLane (l.drop off) i = ByteArray.getUInt64LE ⟨l.toArray⟩ (off + 8 * i) := by
  simp [littleEndianLane, List.range, List.range.loop, ByteArray.getUInt64LE, ByteArray.get!,
    Nat.add_assoc, show (default : UInt8) = 0 from rfl]

theorem littleEndianLane_append (b r : List UInt8) (i : ℕ) (hb : b.length = 136) (hi : i < 17) :
    littleEndianLane (b ++ r) i = littleEndianLane b i := by
  have h0 : (b ++ r)[8 * i]? = b[8 * i]? := List.getElem?_append_left (by omega)
  have h : ∀ k < 8, (b ++ r)[8 * i + k]? = b[8 * i + k]? :=
    fun k hk ↦ List.getElem?_append_left (by omega)
  simp [littleEndianLane, List.range, List.range.loop, h0, h]

theorem modify_append {α : Type} (l r : List α) (n k : ℕ) (f : α → α) (hn : n = l.length + k) :
    (l ++ r).modify n f = l ++ r.modify k f := by
  subst hn
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.cons_append, List.length_cons, show l.length + 1 + k = (l.length + k) + 1 by omega,
      List.modify_succ_cons, ih, List.cons_append]

theorem padBlock_eq (r : List UInt8) (h : r.length < 136) :
    padBlock r = r ++ (if r.length = 135 then [0x81]
      else 1 :: (List.replicate (134 - r.length) 0 ++ [0x80])) := by
  unfold padBlock rate padFirst padLast
  by_cases h5 : r.length = 135
  · rw [show List.replicate (136 - r.length) (0 : UInt8) = [0] by rw [h5]; rfl,
      modify_append r _ r.length 0 _ rfl, modify_append r _ (136 - 1) 0 _ (by omega), ite_eq_left h5]
    rfl
  · rw [show 136 - r.length = (134 - r.length) + 1 + 1 by omega, List.replicate_succ,
      List.replicate_succ', modify_append r _ r.length 0 _ rfl, List.modify_zero_cons,
      modify_append r _ (136 - 1) (134 - r.length + 1) _ (by omega), List.modify_succ_cons,
      modify_append _ [0] (134 - r.length) 0 _ (by simp), ite_eq_right h5]
    rfl

theorem pad_eq (d : List UInt8) :
    (Fast.pad 136 0x01 ⟨d.toArray⟩).data.toList = d ++ (if d.length % 136 = 135 then [0x81]
      else 1 :: (List.replicate (134 - d.length % 136) 0 ++ [0x80])) := by
  by_cases h : d.length % 136 = 135
  · simp [Fast.pad, ByteArray.size, h]
  · have h1 : ¬ 136 - d.length % 136 = 1 := by omega
    have h2 : 136 - d.length % 136 - 2 = 134 - d.length % 136 := by omega
    simp [Fast.pad, ByteArray.zeros, ByteArray.size, h, h1, h2]

theorem digest_eq (s : KeccakState) :
    digestBytes #v[Keccak.lane s 0, Keccak.lane s 1, Keccak.lane s 2, Keccak.lane s 3] =
      ((Fast.squeeze 136 s.toArray 1 ByteArray.empty).extract 0 32).data.toList := by
  simp [digestBytes, wordBytes, Fast.squeeze, Fast.rateBytes, List.range, List.range.loop,
    ByteArray.pushUInt64LE, lane_eq]

end Keccak256Proofs.KeccakSpec

namespace Keccak256Proofs.KeccakSpec
open LeanVM.Protocol LeanVM.Protocol.KeccakHash

theorem absorbBlock_eq (a : Array UInt64) (l : List UInt8) (off : ℕ) :
    Fast.absorbBlock 136 a ⟨l.toArray⟩ off = absorbBlockL a (l.drop off) := by
  unfold Fast.absorbBlock absorbBlockL
  simp only [littleEndianLane_eq]

theorem absorbBlockL_append (a : Array UInt64) (b r : List UInt8) (hb : b.length = 136) :
    absorbBlockL a (b ++ r) = absorbBlockL a b := by
  unfold absorbBlockL Fast.tabulate
  refine congrArg Fast.keccakF (congrArg List.toArray (List.map_congr_left fun i _ ↦ ?_))
  split
  · next hi => rw [littleEndianLane_append b r i hb hi]
  · rfl

/-- The padded message: `k` whole blocks of `d`, then the padded last block. -/
def padded (k : ℕ) (d : List UInt8) : List UInt8 := d.take (136 * k) ++ padBlock (d.drop (136 * k))

theorem padded_succ (k : ℕ) (d : List UInt8) :
    padded (k + 1) d = d.take 136 ++ padded k (d.drop 136) := by
  unfold padded
  rw [show 136 * (k + 1) = 136 + 136 * k by omega, List.take_add, List.drop_drop,
    List.append_assoc]

theorem absorbL_eq (k : ℕ) (a : Array UInt64) (d l : List UInt8) (off : ℕ)
    (hk : 136 * k ≤ d.length) (hl : l.drop off = padded k d) :
    absorbL k a d =
      (List.range (k + 1)).foldl (fun a i ↦ absorbBlockL a (l.drop (off + i * 136))) a := by
  induction k generalizing a d off with
  | zero =>
    simp only [absorbL, zero_add, List.range_one, List.foldl_cons, List.foldl_nil, zero_mul,
      add_zero, hl, padded, mul_zero, List.take_zero, List.drop_zero, List.nil_append]
  | succ k ih =>
    have hlen : (d.take 136).length = 136 := by rw [List.length_take]; omega
    rw [padded_succ] at hl
    have hl' : l.drop (off + 136) = padded k (d.drop 136) := by
      rw [← List.drop_drop, hl, List.drop_left' hlen]
    rw [absorbL, ih _ _ (off + 136) (by rw [List.length_drop]; omega) hl',
      List.range_succ_eq_map (n := k + 1), List.foldl_cons, List.foldl_map, zero_mul, add_zero,
      hl, absorbBlockL_append _ _ _ hlen]
    refine congrArg (fun f ↦ List.foldl f _ _) (funext fun a ↦ funext fun i ↦ ?_)
    rw [show off + 136 + i * 136 = off + (i + 1) * 136 by omega]

theorem keccak256_unfold (data : List UInt8) :
    keccak256 data =
      (let s := Id.run (absorbWith (fun s ↦ pure (keccakF1600 s)) (data.length / 136)
        (Vector.replicate 25 0) data)
      #v[Keccak.lane s 0, Keccak.lane s 1, Keccak.lane s 2, Keccak.lane s 3]) := rfl

theorem pad_toList (d : List UInt8) :
    (Fast.pad 136 0x01 ⟨d.toArray⟩).data.toList = padded (d.length / 136) d := by
  rw [pad_eq, padded, padBlock_eq _ (by rw [List.length_drop]; omega), List.length_drop,
    show d.length - 136 * (d.length / 136) = d.length % 136 by omega, ← List.append_assoc,
    List.take_append_drop]

theorem pad_size (d : List UInt8) :
    (Fast.pad 136 0x01 ⟨d.toArray⟩).size / 136 = d.length / 136 + 1 := by
  rw [Hash.size_eq_length, pad_eq, List.length_append]
  split <;> simp <;> omega

theorem sponge_eq (d : List UInt8) :
    Fast.sponge 136 0x01 ⟨d.toArray⟩ 32 =
      (Fast.squeeze 136 (absorbL (d.length / 136) (Array.replicate 25 0) d) 1
        ByteArray.empty).extract 0 32 := by
  have key : ∀ (a : Array UInt64) (i : ℕ),
      Fast.absorbBlock 136 a (Fast.pad 136 0x01 ⟨d.toArray⟩) (i * 136) =
        absorbBlockL a ((Fast.pad 136 0x01 ⟨d.toArray⟩).data.toList.drop (0 + i * 136)) := by
    intro a i
    rw [zero_add]
    exact absorbBlock_eq a (Fast.pad 136 0x01 ⟨d.toArray⟩).data.toList (i * 136)
  rw [absorbL_eq _ _ d (Fast.pad 136 0x01 ⟨d.toArray⟩).data.toList 0 (Nat.mul_div_le _ _)
    (by rw [List.drop_zero, pad_toList])]
  unfold Fast.sponge
  simp only [key, pad_size]
  rfl

end Keccak256Proofs.KeccakSpec

namespace Keccak256Proofs
open KeccakSpec

/-- (B) leanVM's Keccak-256 is hash-specs' Keccak-256 (Ethereum's), on every byte string. -/
theorem keccak256_eq_hashSpecs (data : List UInt8) :
    LeanVM.Protocol.KeccakHash.digestBytes (LeanVM.Protocol.KeccakHash.keccak256 data) =
      (Hash.keccak256 ⟨data.toArray⟩).data.toList := by
  rw [keccak256_unfold]
  simp only []
  rw [digest_eq, absorbWith_eq, Hash.keccak256, sponge_eq, Vector.toArray_replicate]

/-- (C) leanVM's Keccak-256 is the FIPS 202 sponge KECCAK[512], with the original Keccak
padding, on the message's bits. -/
theorem keccak256_eq_reference (data : List UInt8) :
    Hash.bytesToBitsLSB
        (LeanVM.Protocol.KeccakHash.digestBytes (LeanVM.Protocol.KeccakHash.keccak256 data)) =
      Hash.Keccak.Reference.keccak256 (Hash.bytesToBitsLSB data) := by
  rw [keccak256_eq_hashSpecs]
  exact Hash.Keccak.keccak256_eq ⟨data.toArray⟩

end Keccak256Proofs
