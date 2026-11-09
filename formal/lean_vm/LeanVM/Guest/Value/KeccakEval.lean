/-
  LeanVM.Guest.Value.KeccakEval

  Keccak-f[1600] and Keccak-256 on natural numbers, for kernel evaluation: every operation a
  `Nat` operation the kernel computes on literals, proved equal to the Spec's.
-/

module

public import Statement.Fast.Keccak
public import Mathlib.Data.List.Basic
public import LeanVM.Protocol.KeccakAbsorb

/-!
# Keccak by kernel evaluation

The guest bakes constants that are Keccak-f[1600] or Keccak-256 of fixed inputs (`AGG_SEED_*`,
`DA_PAD_*`, the Keccak table's padding row). Their equations are closed propositions, checked by
`decide +kernel`. The Spec's `keccakF` evaluates in the kernel through `UInt64`, `BitVec` and
`Vector` (lists walked by index), about 4 s and 1.2 GB per permutation; Keccak-256 of 2048 bytes
took 113 s and 24 GB. Here a lane is a natural number below `2^64` and a state a list of
`25`, the round has its lanes written out (`roundN`, as `Fast.Keccak.roundLanes`), and
every operation is one the kernel computes on literals by GMP (`Nat.xor`, `Nat.land`,
`Nat.lor`, the shifts, `%`, `-`).

* `keccakFN_toNats`: `keccakFN (toNats a) = toNats (keccakF a)`, and `toNats_inj`;
* `keccak256N_eq`: `toNats4 (keccak256 data) = keccak256N (data.map UInt8.toNat)`.

A constant is then checked as `keccakF a = b ↔ keccakFN (toNats a) = toNats b`
(`keccakF_eq_iff`), the right side by `decide +kernel`.
-/

namespace LeanVM.Guest.Value.KeccakEval

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash

@[expose] public section

/-! ## The round on natural numbers -/

/-- `rot` on a lane held as a natural number below `2^64`. -/
def rotN (x n : ℕ) : ℕ := if n = 0 then x else (x <<< n) % 2 ^ 64 ||| x >>> (64 - n)

/-- The complement of a lane below `2^64`. -/
def notN (x : ℕ) : ℕ := 18446744073709551615 - x

/-- `Fast.Keccak.roundLanes` on natural numbers: the state a list of `25` lanes. -/
def roundN : List ℕ → ℕ → List ℕ
  | [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19,
      a20, a21, a22, a23, a24], rc =>
    let c0 := a0 ^^^ a5 ^^^ a10 ^^^ a15 ^^^ a20
    let c1 := a1 ^^^ a6 ^^^ a11 ^^^ a16 ^^^ a21
    let c2 := a2 ^^^ a7 ^^^ a12 ^^^ a17 ^^^ a22
    let c3 := a3 ^^^ a8 ^^^ a13 ^^^ a18 ^^^ a23
    let c4 := a4 ^^^ a9 ^^^ a14 ^^^ a19 ^^^ a24
    let d0 := c4 ^^^ rotN c1 1
    let d1 := c0 ^^^ rotN c2 1
    let d2 := c1 ^^^ rotN c3 1
    let d3 := c2 ^^^ rotN c4 1
    let d4 := c3 ^^^ rotN c0 1
    let b0 := rotN (a0 ^^^ d0) 0
    let b1 := rotN (a6 ^^^ d1) 44
    let b2 := rotN (a12 ^^^ d2) 43
    let b3 := rotN (a18 ^^^ d3) 21
    let b4 := rotN (a24 ^^^ d4) 14
    let b5 := rotN (a3 ^^^ d3) 28
    let b6 := rotN (a9 ^^^ d4) 20
    let b7 := rotN (a10 ^^^ d0) 3
    let b8 := rotN (a16 ^^^ d1) 45
    let b9 := rotN (a22 ^^^ d2) 61
    let b10 := rotN (a1 ^^^ d1) 1
    let b11 := rotN (a7 ^^^ d2) 6
    let b12 := rotN (a13 ^^^ d3) 25
    let b13 := rotN (a19 ^^^ d4) 8
    let b14 := rotN (a20 ^^^ d0) 18
    let b15 := rotN (a4 ^^^ d4) 27
    let b16 := rotN (a5 ^^^ d0) 36
    let b17 := rotN (a11 ^^^ d1) 10
    let b18 := rotN (a17 ^^^ d2) 15
    let b19 := rotN (a23 ^^^ d3) 56
    let b20 := rotN (a2 ^^^ d2) 62
    let b21 := rotN (a8 ^^^ d3) 55
    let b22 := rotN (a14 ^^^ d4) 39
    let b23 := rotN (a15 ^^^ d0) 41
    let b24 := rotN (a21 ^^^ d1) 2
    [(b0 ^^^ (notN b1 &&& b2)) ^^^ rc,
      b1 ^^^ (notN b2 &&& b3),
      b2 ^^^ (notN b3 &&& b4),
      b3 ^^^ (notN b4 &&& b0),
      b4 ^^^ (notN b0 &&& b1),
      b5 ^^^ (notN b6 &&& b7),
      b6 ^^^ (notN b7 &&& b8),
      b7 ^^^ (notN b8 &&& b9),
      b8 ^^^ (notN b9 &&& b5),
      b9 ^^^ (notN b5 &&& b6),
      b10 ^^^ (notN b11 &&& b12),
      b11 ^^^ (notN b12 &&& b13),
      b12 ^^^ (notN b13 &&& b14),
      b13 ^^^ (notN b14 &&& b10),
      b14 ^^^ (notN b10 &&& b11),
      b15 ^^^ (notN b16 &&& b17),
      b16 ^^^ (notN b17 &&& b18),
      b17 ^^^ (notN b18 &&& b19),
      b18 ^^^ (notN b19 &&& b15),
      b19 ^^^ (notN b15 &&& b16),
      b20 ^^^ (notN b21 &&& b22),
      b21 ^^^ (notN b22 &&& b23),
      b22 ^^^ (notN b23 &&& b24),
      b23 ^^^ (notN b24 &&& b20),
      b24 ^^^ (notN b20 &&& b21)]
  | _, _ => []

/-- The round constants as natural numbers. -/
def keccakRCN : List ℕ := keccakRC.map UInt64.toNat

/-- Keccak-f[1600] on natural numbers. -/
def keccakFN (a : List ℕ) : List ℕ := keccakRCN.foldl roundN a

/-- A state's lanes as natural numbers. -/
def toNats (a : KeccakState) : List ℕ := a.toList.map UInt64.toNat

/-! ## The round is `Keccak.round` -/

theorem rotN_toNat (x : UInt64) {n : ℕ} (hn : n < 64) :
    (Keccak.rot x n).toNat = rotN x.toNat n := by
  unfold Keccak.rot rotN
  by_cases h0 : n = 0
  · simp [h0]
  · have h1 : n.toUInt64.toNat = n := by simp; omega
    have h2 : (64 - n).toUInt64.toNat = 64 - n := by simp; omega
    simp only [h0, ↓reduceIte, UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt64.toNat_shiftRight,
      h1, h2, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt (show 64 - n < 64 by omega)]

/-- **The round on natural numbers is `Keccak.round`.** -/
theorem roundN_toNats (a : KeccakState) (rc : UInt64) :
    roundN (toNats a) rc.toNat = toNats (Keccak.round a rc) := by
  rw [LeanVM.Fast.Keccak.round_eq_roundLanes]
  obtain ⟨⟨l⟩, hl⟩ := a
  rcases l with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | ⟨a7, _ | ⟨a8, _ |
    ⟨a9, _ | ⟨a10, _ | ⟨a11, _ | ⟨a12, _ | ⟨a13, _ | ⟨a14, _ | ⟨a15, _ | ⟨a16, _ | ⟨a17, _ | ⟨a18, _
    | ⟨a19, _ | ⟨a20, _ | ⟨a21, _ | ⟨a22, _ | ⟨a23, _ | ⟨a24, _ | ⟨_, _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals try (simp at hl; done)
  simp only [toNats, LeanVM.Fast.Keccak.roundLanes, Keccak.lane]
  simp [roundN, notN, UInt64.toNat_xor, UInt64.toNat_and, rotN_toNat]

/-! ## Keccak-f[1600] -/

/-- A fold of `UInt64` steps, read as natural numbers, is the fold of the steps they read as. -/
theorem foldl_toNat {β : Type} (f : UInt64 → β → UInt64) (g : ℕ → β → ℕ) :
    ∀ (l : List β), (∀ u b, b ∈ l → (f u b).toNat = g u.toNat b) →
      ∀ u, (l.foldl f u).toNat = l.foldl g u.toNat
  | [], _, _ => rfl
  | b :: l, h, u => by
    rw [List.foldl_cons, List.foldl_cons, foldl_toNat f g l
      (fun u b hb ↦ h u b (List.mem_cons_of_mem _ hb)), h u b List.mem_cons_self]

/-- **Keccak-f[1600] on natural numbers is `keccakF`.** -/
theorem keccakFN_toNats (a : KeccakState) : keccakFN (toNats a) = toNats (keccakF1600 a) := by
  unfold keccakFN keccakF1600 keccakRCN
  generalize keccakRC = rcs
  induction rcs generalizing a with
  | nil => rfl
  | cons rc rcs ih => rw [List.map_cons, List.foldl_cons, List.foldl_cons, roundN_toNats, ih]

theorem toNats_inj {a b : KeccakState} : toNats a = toNats b ↔ a = b := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ rfl⟩
  apply Vector.toList_inj.mp
  exact List.map_injective_iff.mpr (fun _ _ h ↦ UInt64.toNat_inj.mp h) h

/-- **A permutation's value, by evaluation**: `keccakF a = b` is the equation of the natural
numbers, which `decide +kernel` checks. -/
theorem keccakF_eq_iff (a b : KeccakState) : keccakF1600 a = b ↔ keccakFN (toNats a) = toNats b := by
  rw [keccakFN_toNats, toNats_inj]

/-! ## Keccak-256 -/

/-- `littleEndianLane` on bytes held as natural numbers. -/
def leLaneN (bytes : List ℕ) (i : ℕ) : ℕ :=
  (List.range 8).foldl (fun acc k ↦ acc ||| (bytes.getD (8 * i + k) 0 <<< (8 * k)) % 2 ^ 64) 0

/-- `absorbBlock` on natural numbers. -/
def absorbBlockN (state block : List ℕ) : List ℕ :=
  keccakFN (List.ofFn fun i : Fin 25 ↦
    if i.val < 17 then state.getD i 0 ^^^ leLaneN block i else state.getD i 0)

/-- `padBlock` on natural numbers. -/
def padBlockN (rest : List ℕ) : List ℕ :=
  ((rest ++ List.replicate (rate - rest.length) 0).modify rest.length (· ^^^ 1)).modify
    (rate - 1) (· ^^^ 128)

/-- `absorb` on natural numbers. -/
def absorbN : ℕ → List ℕ → List ℕ → List ℕ
  | 0, state, data => absorbBlockN state (padBlockN data)
  | blocks + 1, state, data => absorbN blocks (absorbBlockN state (data.take rate)) (data.drop rate)

/-- `keccak256` on natural numbers: the digest's four words. -/
def keccak256N (data : List ℕ) : List ℕ :=
  let state := absorbN (data.length / rate) (List.replicate 25 0) data
  [state.getD 0 0, state.getD 1 0, state.getD 2 0, state.getD 3 0]

theorem getD_toNats (a : KeccakState) (i : ℕ) : (toNats a).getD i 0 = (Keccak.lane a i).toNat := by
  have h : a.toArray[i]? = a.toList[i]? := by simp [Vector.toList]
  simp only [toNats, Keccak.lane, List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?,
    List.getElem?_map, h]
  rcases a.toList[i]? <;> rfl

theorem leLane_toNat (bytes : List UInt8) (i : ℕ) :
    (littleEndianLane bytes i).toNat = leLaneN (bytes.map UInt8.toNat) i := by
  unfold littleEndianLane leLaneN
  rw [foldl_toNat _ _ _ ?_]
  · rfl
  intro u k hk
  have hk : k < 8 := List.mem_range.mp hk
  have h8 : (8 * k).toUInt64.toNat = 8 * k := by simp; omega
  simp only [UInt64.toNat_or, UInt64.toNat_shiftLeft, h8,
    Nat.mod_eq_of_lt (show 8 * k < 64 by omega),
    UInt8.toNat_toUInt64, List.getD_eq_getElem?_getD, List.getElem?_map]
  congr 3
  rcases bytes[8 * i + k]? <;> rfl

theorem lane_fin (a : KeccakState) (i : Fin 25) : Keccak.lane a i.val = a[i] := by
  simp [Keccak.lane, Array.getD_eq_getD_getElem?]

theorem absorbBlock_toNats (state : KeccakState) (block : List UInt8) :
    toNats (absorbBlock state block) = absorbBlockN (toNats state) (block.map UInt8.toNat) := by
  rw [absorbBlock, absorbBlockN, ← keccakFN_toNats]
  refine congrArg keccakFN ?_
  simp only [toNats, Vector.toList_ofFn, List.map_ofFn]
  congr 1
  funext i
  simp only [Function.comp_apply, lane_fin]
  split <;> simp [UInt64.toNat_xor, leLane_toNat]

theorem map_modify {α β : Type} (f : α → β) (g : α → α) (g' : β → β) (h : ∀ a, f (g a) = g' (f a)) :
    ∀ (l : List α) (n : ℕ), (l.modify n g).map f = (l.map f).modify n g'
  | [], n => by simp
  | a :: l, 0 => by simp [h]
  | a :: l, n + 1 => by simp [map_modify f g g' h l n]

theorem padBlock_toNat (rest : List UInt8) :
    (padBlock rest).map UInt8.toNat = padBlockN (rest.map UInt8.toNat) := by
  unfold padBlock padBlockN
  rw [map_modify _ _ (· ^^^ 128) (fun a ↦ by rw [UInt8.toNat_xor]; rfl),
    map_modify _ _ (· ^^^ 1) (fun a ↦ by rw [UInt8.toNat_xor]; rfl)]
  simp

theorem absorb_toNats : ∀ (blocks : ℕ) (state : KeccakState) (data : List UInt8),
    toNats (absorb blocks state data) = absorbN blocks (toNats state) (data.map UInt8.toNat)
  | 0, state, data => by
    rw [absorb, absorbN, absorbBlock_toNats, padBlock_toNat]
  | blocks + 1, state, data => by
    rw [absorb, absorbN, absorb_toNats blocks, absorbBlock_toNats, List.map_take, List.map_drop]

/-- **Keccak-256 on natural numbers is `keccak256`.** -/
theorem keccak256N_eq (data : List UInt8) :
    (keccak256 data).toList.map UInt64.toNat = keccak256N (data.map UInt8.toNat) := by
  have hz : List.replicate 25 0 = toNats (Vector.replicate 25 0) := by decide
  rw [keccak256_eq_absorb, keccak256N, List.length_map, hz, ← absorb_toNats]
  simp only [getD_toNats]
  rfl

/-- **A digest's value, by evaluation**: `keccak256 data = d` is the equation of the natural
numbers, which `decide +kernel` checks. -/
theorem keccak256_eq_iff (data : List UInt8) (d : Digest) :
    keccak256 data = d ↔ keccak256N (data.map UInt8.toNat) = d.toList.map UInt64.toNat := by
  rw [← keccak256N_eq]
  refine ⟨fun h ↦ h ▸ rfl, fun h ↦ ?_⟩
  apply Vector.toList_inj.mp
  exact List.map_injective_iff.mpr (fun _ _ h ↦ UInt64.toNat_inj.mp h) h

end
end LeanVM.Guest.Value.KeccakEval
