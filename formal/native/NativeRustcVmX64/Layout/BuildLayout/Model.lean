module

public import NativeVm.Math.Layout
public import NativeRustcVmX64.Spec.Layout
public import NativeRustcVm.Arrays.ReadLemmas
public import NativeRustcVm.Transcript.Frame

/-!
# `build_layout` on x86-64: the model

The power-of-two test (`pow2_iff`); the row counts (`rowW`, `rowsOf`); the words the code stores
(`Ws`, `wsK`) and the model's layout from them (`layoutWAt_of`); the model's `buildLayout` is
`layoutF` exactly when the code's checks pass (`model_some`, `model_none`).
-/

namespace NativeRustcVmX64.Layout.BuildLayout

open NativeRustcX64 NativeVm.Model NativeRustcVm.Layout LeanVM.Protocol.Verifier
open NativeVm.Math.Layout NativeRustcVm.Transcript
open NativeRustcVm (WordAt WordsAt wordOf)

@[expose] public section

/-- The layout. -/
abbrev ll (m0 : MachineData) : BitVec 64 := reg m0 .rcx
/-- The row counts' address. -/
abbrev rp (m0 : MachineData) : BitVec 64 := reg m0 .rdx
/-- The row counts. -/
abbrev rowsOf (m0 : MachineData) : Array Nat := natsOf m0 (reg m0 .rdx) nTables
/-- Row count `t`, a word of the entry's memory. -/
abbrev rowW (m0 : MachineData) (t : Nat) : UInt64 := wordOf m0.dmem (off (rp m0) (8 * t))
/-- The memory's log-size. -/
abbrev lmN (m0 : MachineData) : Nat := (reg m0 .rsi).toNat
/-- The bytecode's length. -/
abbrev nN (m0 : MachineData) : Nat := (reg m0 .rdi).toNat

/-- The code's checks. -/
abbrev Chk (m0 : MachineData) : Prop :=
  5 ≤ bitLength (nN m0) ∧ 1 ≤ lmN m0 ∧ lmN m0 ≤ 30 ∧
    (∀ t < 6, (rowW m0 t).toNat ≤ 2 ^ 30) ∧ bitLength (nN m0) - 5 ≤ 30

/-- The length a power of two. -/
abbrev Pow2 (n : Nat) : Prop := 0 < n ∧ n &&& (n - 1) = 0

/-- The words `ws` (offset, value) from `b`. -/
def Ws (d : Mem 64) (b : BitVec 64) (ws : List (Nat × UInt64)) : Prop :=
  ∀ p ∈ ws, WordAt d (off b p.1) p.2

/-- A table's height word, from its row count. -/
abbrev hgt (rows : Array Nat) (t : Nat) : UInt64 := (bitLength (rows.getD t 0 - 1)).toUInt64

/-- The words `b9` to `b15` store. -/
abbrev wsK (lm lb : Nat) (rows : Array Nat) : List (Nat × UInt64) :=
  [(0, lm.toUInt64), (8, lb.toUInt64), (72, (rows.getD 0 0).toUInt64), (24, hgt rows 0),
   (80, (rows.getD 1 0).toUInt64), (32, hgt rows 1), (88, (rows.getD 2 0).toUInt64),
   (40, hgt rows 2), (96, (rows.getD 3 0).toUInt64), (48, hgt rows 3),
   (104, (rows.getD 4 0).toUInt64), (56, hgt rows 4), (112, (rows.getD 5 0).toUInt64),
   (64, (max (bitLength (rows.getD 5 0 - 1)) 9).toUInt64)]

end

public section

/-! ## The power-of-two test -/

theorem pow2_iff : ∀ n, 0 < n → (n &&& (n - 1) = 0 ↔ n - 1 < n ^^^ (n - 1))
  | n, hn => by
    have hX : n ^^^ (n - 1) = 2 * (n / 2 ^^^ (n - 1) / 2) + 1 := by
      have h1 : (n ^^^ (n - 1)) % 2 = 1 := by
        rw [Nat.xor_mod_two_eq_one]; omega
      have h2 := Nat.xor_div_two (a := n) (b := n - 1)
      omega
    have hA : n &&& (n - 1) = 2 * (n / 2 &&& (n - 1) / 2) := by
      have h1 : (n &&& (n - 1)) % 2 = 0 := by
        have := (Nat.and_mod_two_eq_one (a := n) (b := n - 1)).not
        omega
      have h2 := Nat.and_div_two (a := n) (b := n - 1)
      omega
    rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
    · have hm : 0 < m := by omega
      have ih := pow2_iff m hm
      rw [hA, hX, show 2 * m / 2 = m by omega, show (2 * m - 1) / 2 = m - 1 by omega]
      omega
    · rw [hA, hX, show (2 * m + 1) / 2 = m by omega, show (2 * m + 1 - 1) / 2 = m by omega,
        Nat.and_self, Nat.xor_self]
      omega
  termination_by n => n
  decreasing_by omega

/-- **`b0`'s test**: `x ^ (x - 1) ≤ x - 1`, the length not a power of two. -/
theorem pow2_test (x : BitVec 64) :
    (decide ((x ^^^ (x + BitVec.ofNat 64 18446744073709551615)).toNat <
        (x + BitVec.ofNat 64 18446744073709551615).toNat) ||
      decide ((x ^^^ (x + BitVec.ofNat 64 18446744073709551615)).toNat =
        (x + BitVec.ofNat 64 18446744073709551615).toNat)) = true ↔ ¬Pow2 x.toNat := by
  have hx := x.isLt
  have hm1 : (x + BitVec.ofNat 64 18446744073709551615).toNat = (x.toNat + (2 ^ 64 - 1)) % 2 ^ 64 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; rfl
  by_cases h0 : x.toNat = 0
  · have hs : (x + BitVec.ofNat 64 18446744073709551615).toNat = 2 ^ 64 - 1 := by rw [hm1]; omega
    have hxor : (x ^^^ (x + BitVec.ofNat 64 18446744073709551615)).toNat = 2 ^ 64 - 1 := by
      rw [BitVec.toNat_xor, hs, h0, Nat.zero_xor]
    rw [hxor, hs, h0]
    simp
  · have hs : (x + BitVec.ofNat 64 18446744073709551615).toNat = x.toNat - 1 := by rw [hm1]; omega
    have hp := pow2_iff x.toNat (by omega)
    rw [BitVec.toNat_xor, hs]
    simp only [Bool.or_eq_true, decide_eq_true_eq, Pow2]
    omega

theorem busBits_eq : busBits = 4 := rfl

theorem bitLength_pos {n : Nat} (h : 0 < n) : 1 ≤ bitLength n := by
  unfold bitLength; split <;> omega

theorem toNat_toUInt64 {x : Nat} (h : x < 2 ^ 64) : x.toUInt64.toNat = x := by
  rw [Nat.toUInt64, UInt64.toNat_ofNat', Nat.mod_eq_of_lt h]

theorem u64_eq {x : UInt64} {n : Nat} (h : x.toNat = n) : x = n.toUInt64 := by
  subst h; apply UInt64.toNat.inj; simp

theorem getElem_getD {xs : Array Nat} {t : Nat} (h : t < xs.size) : xs[t] = xs.getD t 0 := by
  simp [Array.getD, h]

/-! ## The rows -/

theorem rowsOf_size (m0 : MachineData) : (rowsOf m0).size = 6 := by
  simp [natsOf, nTables, NativeRustcVm.wordsOf]

theorem rows_getD (m0 : MachineData) {t : Nat} (ht : t < 6) :
    (rowsOf m0).getD t 0 = (rowW m0 t).toNat := by
  simp [natsOf, NativeRustcVm.wordsOf, Array.getD, nTables, ht]

theorem rows_all (m0 : MachineData) :
    (rowsOf m0).all (· ≤ 2 ^ 30) = true ↔ ∀ t < 6, (rowW m0 t).toNat ≤ 2 ^ 30 := by
  rw [Array.all_eq_true]
  constructor
  · intro h t ht
    have := h t (by rw [rowsOf_size]; exact ht)
    rw [getElem_getD (by rw [rowsOf_size]; exact ht), rows_getD m0 ht] at this
    simpa using this
  · intro h t ht
    rw [rowsOf_size] at ht
    rw [getElem_getD (by rw [rowsOf_size]; exact ht), rows_getD m0 ht]
    simpa using h t ht

theorem model_some {bc : Array UInt64} {m0 : MachineData} (hsz : nN m0 = bc.size)
    (hp2 : Pow2 (nN m0)) (hc : Chk m0) :
    buildLayout bc (lmN m0) (rowsOf m0) =
      some (layoutF bc (lmN m0) (bitLength (nN m0) - 5) (rowsOf m0)) := by
  obtain ⟨c1, c2, c3, c4, c5⟩ := hc
  rw [buildLayout_eq, ite_true_of ⟨by rw [← hsz]; exact hp2, by rw [busBits_eq, ← hsz]; omega, c2,
    c3, (rows_all m0).mpr c4, by rw [busBits_eq, ← hsz]; omega, rowsOf_size m0⟩, ← hsz, busBits_eq,
    show bitLength (nN m0) - 1 - 4 = bitLength (nN m0) - 5 by omega]

theorem model_none {bc : Array UInt64} {m0 : MachineData} (hsz : nN m0 = bc.size)
    (hc : ¬(Pow2 (nN m0) ∧ Chk m0)) : buildLayout bc (lmN m0) (rowsOf m0) = none := by
  rw [buildLayout_eq, ite_false_of]
  rintro ⟨c0, c1, c2, c3, c4, c5, -⟩
  rw [← hsz] at c0 c1 c5
  rw [busBits_eq] at c1 c5
  exact hc ⟨c0, by omega, c2, c3, (rows_all m0).mp c4, by omega⟩

/-! ## Words -/

theorem Ws.get {d : Mem 64} {b : BitVec 64} {ws : List (Nat × UInt64)} (h : Ws d b ws)
    {o : Nat} {v : UInt64} (hp : (o, v) ∈ ws) : WordAt d (off b o) v :=
  h (o, v) hp

theorem heights_le {rows : Array Nat} (hs : rows.size = 6) (hr : ∀ t < 6, rows.getD t 0 ≤ 2 ^ 30)
    {t : Nat} (ht : t < 6) : (heightsF rows).getD t 0 ≤ 30 := by
  rw [heightsF_getD hs ht]
  have := log2Ceil_le (hr t ht)
  unfold floorF
  split_ifs <;> omega

theorem hgt_eq {rows : Array Nat} (hrs : rows.size = 6) {t : Nat} (ht : t < 5) :
    hgt rows t = ((heightsF rows).getD t 0).toUInt64 := by
  rw [heightsF_getD hrs (by omega)]
  unfold floorF
  simp only [show ¬t = 5 by omega, ↓reduceIte, Nat.max_zero]
  rfl

theorem hgt5_eq {rows : Array Nat} (hrs : rows.size = 6) :
    (max (bitLength (rows.getD 5 0 - 1)) 9).toUInt64 = ((heightsF rows).getD 5 0).toUInt64 := by
  rw [heightsF_getD hrs (by omega)]
  rfl

/-- Numbers from words at `a + 8 t`. -/
theorem wordsAt_natWords {d : Mem 64} {a : BitVec 64} {xs : Array Nat}
    (h : ∀ t (ht : t < xs.size), WordAt d (off a (8 * t)) xs[t].toUInt64) :
    WordsAt d a (natWords xs) :=
  NativeRustcVm.wordsAt_iff.mpr fun i hi ↦ by
    simp only [natWords, List.length_map, Array.length_toList] at hi
    simpa [natWords] using h i hi

/-- **The heights in memory**, from the stored words. -/
theorem heights_words {d : Mem 64} {a : BitVec 64} {lm lb : Nat} {rows : Array Nat}
    (hrs : rows.size = 6) (hW : Ws d a (wsK lm lb rows)) :
    WordsAt d (off a 24) (natWords (heightsF rows)) := by
  refine wordsAt_natWords fun t ht ↦ ?_
  rw [heightsF_size hrs] at ht
  rw [off_off, show (heightsF rows)[t] = (heightsF rows).getD t 0 by
    simp [Array.getD, ht, heightsF_size hrs]]
  rcases (show t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 by omega)
    with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [← hgt_eq hrs (by omega)]; exact hW.get (by simp)
  · rw [← hgt_eq hrs (by omega)]; exact hW.get (by simp)
  · rw [← hgt_eq hrs (by omega)]; exact hW.get (by simp)
  · rw [← hgt_eq hrs (by omega)]; exact hW.get (by simp)
  · rw [← hgt_eq hrs (by omega)]; exact hW.get (by simp)
  · rw [← hgt5_eq hrs]; exact hW.get (by simp)

/-- **Numbers read back**: the words of `xs` at `a` are `xs`. -/
theorem natsOf_of_words {m : MachineData} {a : BitVec 64} {xs : Array Nat} {n : Nat}
    (h : WordsAt m.dmem a (natWords xs)) (hlt : ∀ x ∈ xs, x < 2 ^ 64) (hn : xs.size = n) :
    natsOf m a n = xs := by
  have hw := NativeRustcVm.wordsOf_of_wordsAt h
  have hl : (natWords xs).length = n := by simp [natWords, hn]
  rw [hl] at hw
  unfold natsOf
  rw [hw]
  apply Array.ext (by simp [natWords, hn]) fun i h1 h2 ↦ ?_
  simp only [natWords, List.getElem_toArray, List.getElem_map, Array.getElem_toList]
  exact toNat_toUInt64 (hlt _ (Array.getElem_mem _))

theorem heights_lt {rows : Array Nat} (hrs : rows.size = 6) (hr : ∀ t < 6, rows.getD t 0 ≤ 2 ^ 30) :
    ∀ x ∈ heightsF rows, x < 2 ^ 64 := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem hx
  have := heights_le hrs hr (t := i) (by rw [heightsF_size hrs] at hi; exact hi)
  simp [Array.getD, hi] at this
  omega

theorem cols_lt {lm lb : Nat} {rows : Array Nat} (hrs : rows.size = 6) (hlm : lm ≤ 30)
    (hlb : lb ≤ 30) (hr : ∀ t < 6, rows.getD t 0 ≤ 2 ^ 30) :
    ∀ x ∈ columnKappas lm lb (heightsF rows), x ≤ 36 := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem hx
  have hi' : i < 158 := by rw [columnKappas_size'] at hi; exact hi
  rw [getElem_getD hi, columnKappas_getD _ _ _ hi']
  exact kapF_le hlm hlb (fun t ht ↦ heights_le hrs hr ht) i

/-- **The layout** from the words `build_layout` stored. -/
theorem layoutWAt_of {d : Mem 64} {a : BitVec 64} {bc : Array UInt64} {lm lb : Nat}
    {rows : Array Nat} (hrs : rows.size = 6) (hlm : lm ≤ 30) (hlb : lb ≤ 30)
    (hr : ∀ t < 6, rows.getD t 0 ≤ 2 ^ 30) (hK : Ws d a (wsK lm lb rows))
    (hsl : (layoutF bc lm lb rows).stackLog < 2 ^ 64)
    (hs : WordAt d (off a 16) (layoutF bc lm lb rows).stackLog.toUInt64)
    (hpl : ∀ c (h : c < (layoutF bc lm lb rows).placements.size),
      PlacementWAt d (off a (120 + placementBytes * c)) (layoutF bc lm lb rows).placements[c]) :
    LayoutWAt d a (layoutF bc lm lb rows) := by
  obtain ⟨f1, f2, -, f4, f5, f6, -, -⟩ := layoutF_facts bc lm lb rows
  refine ⟨f1 ▸ hlm, ?_, f2 ▸ hlb, ?_, hsl, hs, by rw [f4]; exact heightsF_size hrs, ?_, ?_, ?_,
    by rw [f6]; rfl, hpl⟩
  · rw [f1, ← off_zero a]; exact hK.get (by simp)
  · rw [f2]; exact hK.get (by simp)
  · rw [f4]
    intro h hh
    obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem hh
    have hi' : i < 6 := by rw [heightsF_size hrs] at hi; exact hi
    rw [getElem_getD hi]
    exact heights_le hrs hr hi'
  · rw [f4]
    exact heights_words hrs hK
  · refine ⟨rows, hrs, fun x hx ↦ ?_, ?_, by rw [f4]; exact f5⟩
    · obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem hx
      rw [getElem_getD hi]
      exact hr i (by omega)
    · refine wordsAt_natWords fun t ht ↦ ?_
      rw [off_off, getElem_getD ht]
      rcases (show t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 by omega)
        with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hK.get (by simp)

end

end NativeRustcVmX64.Layout.BuildLayout
