module

public import LeanVMCircuits.BooleanOps
public import LeanVMCircuits.WordValues

@[expose] public section

namespace LeanVMCircuits.Words

variable {α β : Type} {n : ℕ}

def resize (m : ℕ) (fill : α) (bits : Vector α n) : Vector α m :=
  Vector.mapFinRange m fun i => filled bits fill i.val

theorem resize_map (f : α → β) (m : ℕ) (fill : α) (bits : Vector α n) :
    (resize m fill bits).map f = resize m (f fill) (bits.map f) := by
  apply Vector.ext
  intro i hi
  simp only [resize, Vector.getElem_map, Vector.getElem_mapFinRange, filled]
  split <;> simp

theorem resize_self (fill : α) (bits : Vector α n) : resize n fill bits = bits := by
  apply Vector.ext
  intro i hi
  simp [resize, filled, Vector.getElem_mapFinRange]

def leftTo (m amount : ℕ) (fill : α) (bits : Vector α n) : Vector α m :=
  Vector.mapFinRange m fun i => if amount ≤ i.val then filled bits fill (i.val - amount) else fill

theorem leftTo_zero (m : ℕ) (fill : α) (bits : Vector α n) :
    leftTo m 0 fill bits = resize m fill bits := by
  apply Vector.ext
  intro i hi
  simp [leftTo, resize, Vector.getElem_mapFinRange]

theorem leftTo_map (f : α → β) (m amount : ℕ) (fill : α) (bits : Vector α n) :
    (leftTo m amount fill bits).map f = leftTo m amount (f fill) (bits.map f) := by
  apply Vector.ext
  intro i hi
  simp only [leftTo, Vector.getElem_map, Vector.getElem_mapFinRange]
  by_cases h : amount ≤ i
  · simp only [h, if_pos, filled]
    split <;> simp
  · simp [h]

theorem leftTo_add (m k a b : ℕ) (fill : α) (bits : Vector α n) (hfits : n + b ≤ k) :
    leftTo m a fill (leftTo k b fill bits) = leftTo m (a + b) fill bits := by
  apply Vector.ext
  intro i hi
  simp only [leftTo, Vector.getElem_mapFinRange]
  by_cases ha : a ≤ i
  · by_cases hk : i - a < k
    · simp only [ha, if_pos, filled, hk, dif_pos, Vector.getElem_mapFinRange]
      by_cases hb : b ≤ i - a
      · have hab : a + b ≤ i := by omega
        simp [hb, hab, Nat.sub_sub]
      · have hab : ¬ a + b ≤ i := by omega
        simp [hb, hab]
    · have hn : ¬ i - (a + b) < n := by omega
      simp [ha, filled, hk, hn]
  · have hab : ¬ a + b ≤ i := by omega
    simp [ha, hab]

end LeanVMCircuits.Words

namespace LeanVMCircuits.Memory

def logWidth (low high : Bit) : ℕ := low.val + 2 * high.val

def LegalWidth (low high : Bit) : Prop := logWidth low high ∈ [0, 1, 2]

def offset (address : Vector Bit 64) : ℕ := Adder.value #v[address[0], address[1], address[2]]

def address (v1 imm : Vector Bit 64) : Vector Bit 64 :=
  Words.ofNat 64 ((Adder.value v1 + Adder.value imm) % 2 ^ 64)

def busParts {F : Type} [Zero F] (low high : F) (address : Vector F 64) : Vector F 64 :=
  Vector.mapFinRange 64 fun i =>
    if i.val = 0 then low
    else if i.val = 1 then high
    else if i.val = 2 then 0 else address[i]

theorem busParts_map {F G : Type} [Zero F] [Zero G] (f : F → G) (hzero : f 0 = 0)
    (low high : F) (address : Vector F 64) :
    (busParts low high address).map f = busParts (f low) (f high) (address.map f) := by
  apply Vector.ext
  intro i hi
  simp only [busParts, Vector.getElem_map, Vector.getElem_mapFinRange]
  by_cases h0 : i = 0 <;> by_cases h1 : i = 1 <;> by_cases h2 : i = 2 <;>
    simp [h0, h1, h2, hzero]

def bus (low high : Bit) (address : Vector Bit 64) : Vector Bit 64 :=
  busParts (address[0] * (low + high)) (address[1] * high) address

def load (low high signed : Bit) (address cell : Vector Bit 64) : Vector Bit 64 :=
  let shifted := Words.right (8 * offset address) 0 cell
  let width := 8 * 2 ^ logWidth low high
  Vector.mapFinRange 64 fun i =>
    if i.val < width then shifted[i]
    else if signed = 1 then Words.filled shifted 0 (width - 1) else 0

def store (low high : Bit) (address value cell : Vector Bit 64) : Vector Bit 64 :=
  let start := 8 * offset address
  let width := 8 * 2 ^ logWidth low high
  Vector.mapFinRange 64 fun i =>
    if start ≤ i.val ∧ i.val < start + width
    then Words.filled value 0 (i.val - start) else cell[i]

def Aligned (low high : Bit) (address : Vector Bit 64) : Prop :=
  offset address % 2 ^ logWidth low high = 0

end LeanVMCircuits.Memory
