import Rv64Verifier.Proofs.Runtime.Reserve
import Rv64Verifier.Proofs.Rodata

/-!
# Word arithmetic the multilinear proofs share

`negW n` is the word `-n`, a down-counter the compiled loops run up to zero (`negW_add`,
`negW_last`); `end_ptr` is the end pointer `a + 24 b` as compiled through a division by 24
(`mulhu` by `0xaaaaaaaaaaaaaaab`). `reserve_fast`: `Vec<E>::reserve` with room enough returns
at once, writing nothing (callers reserve on a `Vec` they just made with the capacity they need). Each is proved through `toNat`, with every `% 2^64` removed by
hand before `omega` (which is slow on them).
-/

namespace Rv64Verifier.MultilinearWords
open RiscvZkvm.Rv64

/-- The word `-n`. -/
def negW (n : Nat) : Word := 0 - BitVec.ofNat 64 n

theorem negW_toNat {n : Nat} (h0 : 0 < n) (h : n < 2 ^ 64) : (negW n).toNat = 2 ^ 64 - n := by
  simp only [negW, BitVec.toNat_sub, BitVec.toNat_ofNat, Sym.wordToNatLit]
  omega

theorem negW_add {m : Nat} (hm : 0 < m) (h : 24 * (m + 1) < 2 ^ 64) :
    negW (24 * (m + 1)) + 24 = negW (24 * m) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, negW_toNat (by omega) h, negW_toNat (by omega) (by omega)]
  simp only [Sym.wordToNatLit]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

theorem negW_add_ne {m : Nat} (hm : 0 < m) (h : 24 * (m + 1) < 2 ^ 64) :
    negW (24 * (m + 1)) + 24 ≠ 0 := by
  rw [negW_add hm h]
  intro h0
  have := congrArg BitVec.toNat h0
  rw [negW_toNat (by omega) (by omega)] at this
  simp only [Sym.wordToNatLit] at this
  omega

theorem negW_last : negW (24 * 1) + 24 = 0 := by decide

theorem neg_negW {n : Nat} (h : n < 2 ^ 64) : (0 - negW n).toNat = n := by
  have : (0 : Word) - negW n = BitVec.ofNat 64 n := by simp only [negW]; ring
  rw [this, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem mul_negW (x : Word) (h : 24 * x.toNat < 2 ^ 64) :
    x * 18446744073709551592 = negW (24 * x.toNat) := by
  have hc : (18446744073709551592 : Word) = 0 - 24 := by decide
  have hx : x * 24 = BitVec.ofNat 64 (24 * x.toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
    simp only [Sym.wordToNatLit]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mul_comm]
  rw [hc, negW, ← hx]
  ring

theorem toNat_and_f0 (x : Word) :
    (x &&& (18446744073709551600 : Word)).toNat = x.toNat - x.toNat % 16 := by
  have e : (18446744073709551600 : Word) = ~~~15#64 := by decide
  have h := congrArg BitVec.toNat (Runtime.and_not_add x 15#64)
  have h15 : (x &&& 15#64).toNat = x.toNat % 16 := by
    rw [BitVec.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod x.toNat 4
  rw [BitVec.toNat_add, h15] at h
  have := (x &&& ~~~15#64).isLt
  rw [e]
  omega

/-- `a + 24 b` through `(24 b - 24) / 24` by `mulhu`, as `index_mle` computes its end. -/
theorem end_ptr (a b : Word) (h1 : 1 ≤ b.toNat) (h2 : a.toNat + 24 * b.toNat < 2 ^ 64) :
    (rv64_mulhu (b * 16 + b * 8 - 24) (12297829382473034411 : Word) &&&
        (18446744073709551600 : Word)) + a +
      rv64_mulhu (b * 16 + b * 8 - 24) (12297829382473034411 : Word) >>> 4 * 8 + 24 =
    a + BitVec.ofNat 64 (24 * b.toNat) := by
  have hb : b * 16 + b * 8 - 24 = BitVec.ofNat 64 (24 * b.toNat - 24) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_mul,
      BitVec.toNat_ofNat]
    simp only [Sym.wordToNatLit]
    rw [Nat.mod_eq_of_lt (a := b.toNat * 16) (by omega),
      Nat.mod_eq_of_lt (a := b.toNat * 8) (by omega),
      Nat.mod_eq_of_lt (a := b.toNat * 16 + b.toNat * 8) (by omega),
      Nat.mod_eq_of_lt (a := 24 * b.toNat - 24) (by omega),
      show 2 ^ 64 - 24 + (b.toNat * 16 + b.toNat * 8) = 2 ^ 64 + (24 * b.toNat - 24) by omega,
      Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  have hM : rv64_mulhu (b * 16 + b * 8 - 24) (12297829382473034411 : Word) =
      BitVec.ofNat 64 (16 * (b.toNat - 1)) := by
    apply BitVec.eq_of_toNat_eq
    rw [Runtime.toNat_mulhu, hb, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (a := 24 * b.toNat - 24) (by omega),
      Nat.mod_eq_of_lt (a := 16 * (b.toNat - 1)) (by omega)]
    simp only [Sym.wordToNatLit]
    omega
  rw [hM]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, toNat_and_f0, BitVec.toNat_mul,
    BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := 16 * (b.toNat - 1)) (by omega),
    Nat.mod_eq_of_lt (a := 24 * b.toNat) (by omega), Nat.shiftRight_eq_div_pow]
  simp only [Sym.wordToNatLit]
  have : 16 * (b.toNat - 1) % 16 = 0 := by omega
  rw [this, Nat.sub_zero, show 16 * (b.toNat - 1) / 2 ^ 4 = b.toNat - 1 by omega,
    Nat.mod_eq_of_lt (a := (b.toNat - 1) * 8) (by omega),
    Nat.mod_eq_of_lt (a := 16 * (b.toNat - 1) + a.toNat) (by omega),
    Nat.mod_eq_of_lt (a := 16 * (b.toNat - 1) + a.toNat + (b.toNat - 1) * 8) (by omega),
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

/-- **`Vec<E>::reserve` with room enough** (`0x80008a10`): it returns, writing nothing. -/
theorem reserve_fast {u : MachineState} (hpc : u.pc = 0x80008a10)
    (hval : ValidMemRange (u.getReg .x10) 3)
    (hroom : (u.getMem (u.getReg .x10 + 16)).toNat + (u.getReg .x11).toNat ≤
      (u.getMem (u.getReg .x10)).toNat) :
    ∃ v, Reaches Image.code u v ∧ v.pc = returnAddress u ∧ Preserves u v ∧
      v.getReg .x10 = u.getReg .x10 ∧ ∀ a, v.getMem a = u.getMem a := by
  have hA : Runtime.Spec 0x80008a10 (Runtime.Reserve.resA 0x80008a10) :=
    Runtime.spec_of 8836 4 (by decide +kernel) (by decide +kernel) (by decide) (by decide)
  have hB : Runtime.Spec (0x80008a10 + 16) Runtime.Reserve.resB :=
    Runtime.spec_of 8840 1 (by decide +kernel) (by decide +kernel) (by decide) (by decide)
  have hb := ValidMemRange.bounds hval (by decide)
  obtain ⟨t₀, hr₀, h₀⟩ := hA.reaches hpc (by
    rv_eval []
    and_intros <;> valid_access hval [hb])
  have pc₀ := h₀.pc
  have k₀ := h₀.keeps (rs := [.x1, .x2, .x10, .x11] ++ Runtime.saved) rfl
  have hm₀ (a : Word) : t₀.getMem a = u.getMem a := h₀.frame a (by simp [Runtime.Reserve.resA])
  rv_eval [Runtime.Reserve.room] at pc₀
  have hroom' : (u.getMem (u.getReg .x10) - u.getMem (u.getReg .x10 + 16)).toNat =
      (u.getMem (u.getReg .x10)).toNat - (u.getMem (u.getReg .x10 + 16)).toNat := by
    rw [BitVec.toNat_sub]; omega
  rcases Runtime.eq_ite_cases pc₀ with ⟨hlt, -⟩ | ⟨-, pc₀⟩
  · simp only [BitVec.ult, decide_eq_true_eq, hroom'] at hlt
    omega
  obtain ⟨t, hr, h⟩ := hB.reaches pc₀ trivial
  have pc := h.pc
  rv_eval [k₀ .x1 (by decide)] at pc
  have k := h.keeps (rs := [.x2, .x10] ++ Runtime.saved) rfl
  refine ⟨t, hr₀.trans hr, pc.trans (returnAddress_eq u).symm, fun r hr' ↦ ?_,
    (k .x10 (by decide)).trans (k₀ .x10 (by decide)),
    fun a ↦ (h.frame a (by simp [Runtime.Reserve.resB])).trans (hm₀ a)⟩
  rw [k r (Runtime.mem_of_mem hr' _), k₀ r (Runtime.mem_of_mem hr' _)]

/-- Aligned doublewords inside the heap are valid. -/
theorem heap_valid_range {P : Word} {n : Nat} (ha : P.toNat % 8 = 0)
    (hlo : Runtime.heapStart ≤ P.toNat) (hhi : P.toNat + 8 * n ≤ Runtime.heapEnd) :
    ValidMemRange P n := by
  intro i hi
  apply validAccess_of_dword
  show Sym.validAccess 8 _ = true
  rw [Sym.validAccess_eight]
  simp only [Runtime.heapStart, Runtime.heapEnd] at hlo hhi
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 8 * i) (by omega),
    Nat.mod_eq_of_lt (by omega)]
  omega

/-- `.rodata` across a byte frame apart from it. -/
theorem rodataOk_of_byteFrame {s t : MachineState} {w : Word → Prop} (h : RodataOk s)
    (hf : Runtime.ByteFrame s t w) (hw : ∀ a, w a → ¬ Within a rodataBase rodataSize) :
    RodataOk t := by
  intro p hp
  have hin := within_of_mem_rodataWords hp
  rw [← h p hp]
  by_cases h8 : p.1.toNat % 8 = 0
  · exact hf.getMem fun i hi hwi ↦ hw _ hwi (by addr_omega [hin, hi, h8])
  · exact hf.unaligned _ h8

/-- A slice's suffix. -/
theorem eListAt_drop (s : MachineState) (p : Word) (n v : Nat) :
    (eListAt s p n).drop v = eListAt s (p + BitVec.ofNat 64 (24 * v)) (n - v) := by
  apply List.ext_getElem (by simp [eListAt_length])
  intro i h1 h2
  simp only [List.getElem_drop, eListAt_getElem]
  congr 1
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  congr 2
  ring

end Rv64Verifier.MultilinearWords
