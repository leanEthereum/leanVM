module

public import LeanVMCircuits.Rec.Rows
public import LeanVMCircuits.Blake2s.Export

@[expose] public section

/-!
A hash row's columns are BLAKE2s.

The `HASH` table's first 18 columns are the ports of the row's packed BLAKE2s witness: the counter, the finalization
word, the chaining value's four 64-bit words, the message's eight, then the result's four, each `K` element the word
whose coefficients are the port's bits. The witness's port bits are the Clean circuit's ports as `Hash::circuit`
binds them: 32-bit word `r` of `h`, `m` and the result is half `r % 2` of 64-bit port word `r / 2`, low half first.
When the witness satisfies the exported artifact, the output columns are RFC 7693's compression of the input columns.
-/

namespace LeanVMCircuits.Rec

open LeanVMCircuits.Blake2s Rfc7693

attribute [local irreducible] program

/-- The Clean circuit's ports from the 14 input port words, as `Hash::circuit` binds them. -/
def portsOf (P : Fin 14 → BitVec 64) : Compress.Input Bit :=
  { t := literal (P 0), f0 := literal ((P 1).setWidth 32),
    h := Vector.ofFn fun j => (literal (P ⟨2 + j.val / 64, by omega⟩) : Vector Bit 64)[j.val % 64]'(Nat.mod_lt _ (by norm_num)),
    m := Vector.ofFn fun j => (literal (P ⟨6 + j.val / 64, by omega⟩) : Vector Bit 64)[j.val % 64]'(Nat.mod_lt _ (by norm_num)) }

/-- The 256 output bits from the four output port words. -/
def resultOf (O : Fin 4 → BitVec 64) : Vector Bit 256 :=
  Vector.ofFn fun j => (literal (O ⟨j.val / 64, by omega⟩) : Vector Bit 64)[j.val % 64]'(Nat.mod_lt _ (by norm_num))

/-- Half `s` of a 64-bit word. -/
def half (w : BitVec 64) (s : ℕ) : BitVec 32 := (w >>> (32 * s)).setWidth 32

theorem words_ofFn {k : ℕ} (Q : Fin k → BitVec 64) (r : Fin (2 * k)) :
    (Compress.words (k := 2 * k) (Vector.ofFn fun j : Fin (32 * (2 * k)) =>
      (literal (Q ⟨j.val / 64, by omega⟩) : Vector Bit 64)[j.val % 64]'(Nat.mod_lt _ (by norm_num))))[r] =
      half (Q ⟨r.val / 2, by omega⟩) (r.val % 2) := by
  simp only [Compress.words, Fin.getElem_fin, Vector.getElem_ofFn]
  apply toWord_ext
  intro i hi
  simp only [Compress.chunk, Vector.getElem_ofFn, literal, half, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  have h1 : (32 * r.val + i) / 64 = r.val / 2 := by omega
  have h2 : (32 * r.val + i) % 64 = 32 * (r.val % 2) + i := by omega
  simp only [h1, h2, hi, decide_true, Bool.true_and]
  split <;> simp_all

/-- The chaining value's 32-bit words from the port words `2..6`. -/
def hWords (P : Fin 14 → BitVec 64) : Vector (BitVec 32) 8 := Vector.ofFn fun r => half (P ⟨2 + r.val / 2, by omega⟩) (r.val % 2)

/-- The message's 32-bit words from the port words `6..14`. -/
def mWords (P : Fin 14 → BitVec 64) : Vector (BitVec 32) 16 := Vector.ofFn fun r => half (P ⟨6 + r.val / 2, by omega⟩) (r.val % 2)

/-- A hash row's witness satisfying the exported artifact makes its output port words RFC 7693's compression of its
input port words, for both finalization words. -/
theorem hash_ports_compress (a : ℕ → Bit) (hholds : Compress.artifact.Holds a) (P : Fin 14 → BitVec 64)
    (O : Fin 4 → BitVec 64) (hin : Export.ports a = portsOf P) (hout : Export.result a = resultOf O) (f : Bool)
    (hf : (P 1).setWidth 32 = if f then BitVec.allOnes 32 else 0) (r : Fin 8) :
    half (O ⟨r.val / 2, by omega⟩) (r.val % 2) = (F (hWords P) (mWords P) (P 0) f)[r] := by
  have hs := Export.soundness a hholds f (by rw [hin, portsOf, toWord_literal]; exact hf)
  rw [hin, hout] at hs
  have hres : (Compress.words (k := 8) (resultOf O))[r] = _ := congrArg (·[r]) hs
  rw [← words_ofFn O r]
  have hh : Compress.words (k := 8) (portsOf P).h = hWords P := by
    apply Vector.ext
    intro i hi
    have := words_ofFn (fun j : Fin 4 => P ⟨2 + j.val, by omega⟩) ⟨i, hi⟩
    simp only [Fin.getElem_fin] at this
    simpa [hWords, portsOf] using this
  have hm : Compress.words (k := 16) (portsOf P).m = mWords P := by
    apply Vector.ext
    intro i hi
    have := words_ofFn (fun j : Fin 8 => P ⟨6 + j.val, by omega⟩) ⟨i, hi⟩
    simp only [Fin.getElem_fin] at this
    simpa [mWords, portsOf] using this
  rw [hh, hm, show (portsOf P).t = literal (P 0) from rfl, toWord_literal] at hres
  exact hres

/-- The port word a hash row's column holds: its coefficient word. -/
noncomputable def columnWord (row : ℕ → K) (c : ℕ) : BitVec 64 := BitVec.ofNat 64 (toWord (row c))

/-- A hash row: when its packed witness satisfies the exported artifact and the witness's ports are its columns' words,
its output columns are RFC 7693's compression of its chaining value and message columns, with its counter column,
for both finalization words. -/
theorem hash_row_compress (row : ℕ → K) (a : ℕ → Bit) (hholds : Compress.artifact.Holds a)
    (hin : Export.ports a = portsOf fun j => columnWord row j)
    (hout : Export.result a = resultOf fun k => columnWord row (hashO + k)) (f : Bool)
    (hf : (columnWord row hashF).setWidth 32 = if f then BitVec.allOnes 32 else 0) (r : Fin 8) :
    half (columnWord row (hashO + r.val / 2)) (r.val % 2) =
      (F (hWords fun j => columnWord row j) (mWords fun j => columnWord row j) (columnWord row hashT) f)[r] :=
  hash_ports_compress a hholds _ _ hin hout f hf r

end LeanVMCircuits.Rec
