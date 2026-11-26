/-
  Rv64mc.Proof.Bytecode.IsValidEncoding

  `is_valid_encoding_of_a_leanisa_program` keeps its contract (`Spec.Bytecode.IsValidEncoding.spec`), over any
  program holding its template, from the bounds check's panic (which does not return). The compiled checks are the
  Rust's in other terms: `n.is_power_of_two()` as `n - 1 < n ^ (n - 1)` (`pow2_iff`), the length's shape by two
  unsigned comparisons (`shape_iff`), and the opcode's one-hot test as a bit of `0x10016` then `8` and `32`
  (`machineOk`, equal to `Model.instructionOkRust` by `instr_eq`). `rv_auto` runs the entry to the loop's head
  (instruction 170); the loop over the instructions is `loop`, its invariant `Inv` the slots' pointers and every
  instruction before `j` valid. The zero tests of slots `7..15` are unrolled, so a path that passes them stops at
  instruction 434 (the target of the `KECCAK` arm's backward jump), from which it is stepped again to the back edge.
-/

import Rv64mc.Spec.Bytecode.IsValidEncoding
import Rv64mc.Spec.Runtime.Panic
import Rv64mc.Core.ReprLemmas
import Rv64mc.Gen.Tmpl.Verifier.Bytecode.IsValidEncodingOfALeanisaProgram
import Rv64mc.Tactic.Sym

namespace Rv64mc.Proof.Bytecode.IsValidEncoding

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Bytecode.IsValidEncoding
open Rv64mc.Gen.Verifier.Bytecode.IsValidEncodingOfALeanisaProgram (Link tmpl)

/-! ## Powers of two -/

theorem two_mul_xor (a c : Nat) (b d : Bool) :
    (2 * a + b.toNat) ^^^ (2 * c + d.toNat) = 2 * (a ^^^ c) + (bne b d).toNat := by
  have := Nat.xor_bit b a d c
  simp only [Nat.bit_val] at this
  rw [this]

theorem pow2_two_mul {u : Nat} : (2 * u).isPowerOfTwo ↔ u.isPowerOfTwo := by
  constructor
  · rintro ⟨k, hk⟩
    rcases k with _ | k
    · omega
    · exact ⟨k, by rw [Nat.pow_succ] at hk; omega⟩
  · rintro ⟨k, rfl⟩; exact ⟨k + 1, by rw [Nat.pow_succ, Nat.mul_comm]⟩

theorem pow2_odd {u : Nat} : (2 * u + 1).isPowerOfTwo ↔ u = 0 := by
  constructor
  · rintro ⟨k, hk⟩
    rcases k with _ | k
    · simp at hk; omega
    · rw [Nat.pow_succ] at hk; omega
  · rintro rfl; exact ⟨0, rfl⟩

/-- The power-of-two test `n - 1 < n ^ (n - 1)`, on numbers. -/
theorem xor_pred_iff : ∀ n : Nat, 0 < n → (n - 1 < n ^^^ (n - 1) ↔ n.isPowerOfTwo)
  | n, hn => by
    rcases Nat.even_or_odd' n with ⟨u, rfl | rfl⟩
    · have hu : 0 < u := by omega
      have h := two_mul_xor u (u - 1) false true
      simp only [Bool.toNat_false, Bool.toNat_true, add_zero] at h
      rw [show 2 * u - 1 = 2 * (u - 1) + 1 by omega, h, pow2_two_mul, ← xor_pred_iff u hu]
      rw [show (bne false true).toNat = 1 from rfl]
      omega
    · have h := two_mul_xor u u true false
      simp only [Bool.toNat_false, Bool.toNat_true, add_zero, Nat.xor_self, mul_zero] at h
      rw [Nat.add_sub_cancel, h, pow2_odd, show (bne true false).toNat = 1 from rfl]
      omega

/-- The machine's test of `n.is_power_of_two()`. -/
theorem pow2_iff {n : Nat} (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n + 18446744073709551615#64 < BitVec.ofNat 64 n ^^^ (BitVec.ofNat 64 n + 18446744073709551615#64)
      ↔ n.isPowerOfTwo := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · constructor
    · intro h; exact absurd h (by decide)
    · rintro ⟨k, hk⟩; have := Nat.one_le_two_pow (n := k); omega
  · have h1 : (BitVec.ofNat 64 n + 18446744073709551615#64).toNat = n - 1 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
    rw [BitVec.lt_def, BitVec.toNat_xor, h1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
    exact xor_pred_iff n hpos

theorem shr4 {L : Nat} (hL : L < 2 ^ 64) : BitVec.ofNat 64 L >>> 4 = BitVec.ofNat 64 (L / 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega

theorem and_ite (a b : Prop) [Decidable a] [Decidable b] :
    ((if a then (1 : BitVec 64) else 0) &&& (if b then 1 else 0)) = if a ∧ b then 1 else 0 := by
  by_cases ha : a <;> by_cases hb : b <;> simp only [ha, hb, ite_true, ite_false, and_true, and_false] <;> decide

/-- The machine's test of `len == n << 4 && n <= 1 << 30`. -/
theorem shape_iff {L : Nat} (hL : L < 2 ^ 64) :
    ¬ BinOp.ult.eval (BitVec.ofNat 64 L &&& 15#64) 1#64 &&& BinOp.ult.eval (BitVec.ofNat 64 L) 17179869200#64 = 0#64
      ↔ L % 16 = 0 ∧ L < 17179869200 := by
  have h15 : (BitVec.ofNat 64 L &&& 15#64).toNat = L % 16 := by
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hL]
    exact Nat.and_two_pow_sub_one_eq_mod L 4
  have hl : (BitVec.ofNat 64 L).toNat = L := by rw [BitVec.toNat_ofNat]; omega
  have e1 : (1#64).toNat = 1 := rfl
  have e2 : (17179869200#64).toNat = 17179869200 := rfl
  simp only [BinOp.eval, BitVec.ult_iff_lt, BitVec.lt_def, h15, hl, e1, e2]
  rw [and_ite]
  by_cases h : L % 16 < 1 ∧ L < 17179869200
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h)]; exact ⟨fun _ => ⟨by omega, h.2⟩, fun _ => by decide⟩
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h)]; exact ⟨fun h' => absurd rfl h', fun h' => absurd ⟨by omega, h'.2⟩ h⟩

/-- `validEncodingRust` as the machine tests it. -/
theorem valid_eq (ws : List Word) :
    Model.validEncodingRust ws =
      (decide ((ws.length / 16).isPowerOfTwo ∧ ws.length % 16 = 0 ∧ ws.length < 17179869200) &&
        (List.range (ws.length / 16)).all (Model.instructionOkRust ws (ws.length / 16))) := by
  have hs : ws.length >>> 4 = ws.length / 16 := Nat.shiftRight_eq_div_pow _ _
  have A : (ws.length / 16 != 0 && ws.length / 16 &&& (ws.length / 16 - 1) == 0) =
      decide (ws.length / 16).isPowerOfTwo := by
    rw [Bool.eq_iff_iff, decide_eq_true_eq, ← Nat.ne_zero_and_sub_one_eq_zero_iff_isPowerOfTwo]
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]
  have B : (ws.length == (ws.length / 16) <<< 4) = decide (ws.length % 16 = 0) := by
    rw [Bool.eq_iff_iff]
    simp only [beq_iff_eq, decide_eq_true_eq, Nat.shiftLeft_eq, show (2 : Nat) ^ 4 = 16 from rfl]
    omega
  have C : decide (ws.length / 16 ≤ 2 ^ 30) = decide (ws.length < 17179869200) := by
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq, show (2 : Nat) ^ 30 = 1073741824 from rfl]
    omega
  simp only [Model.validEncodingRust, hs, A, B, C, Bool.decide_and, Bool.and_assoc]

theorem find_op (w : Word) : (List.range 6).find? (fun op ↦ w == 1#64 <<< op) =
    if w = 1#64 then some 0 else if w = 2#64 then some 1 else if w = 4#64 then some 2 else
      if w = 8#64 then some 3 else if w = 16#64 then some 4 else if w = 32#64 then some 5 else none := by
  have e0 : 1#64 <<< 0 = 1#64 := by decide
  have e1 : 1#64 <<< 1 = 2#64 := by decide
  have e2 : 1#64 <<< 2 = 4#64 := by decide
  have e3 : 1#64 <<< 3 = 8#64 := by decide
  have e4 : 1#64 <<< 4 = 16#64 := by decide
  have e5 : 1#64 <<< 5 = 32#64 := by decide
  simp only [List.range_succ, List.range_zero, List.nil_append, List.cons_append, List.find?_cons,
    List.find?_nil, e0, e1, e2, e3, e4, e5]
  by_cases h1 : w = 1#64
  · subst h1; decide
  by_cases h2 : w = 2#64
  · subst h2; decide
  by_cases h4 : w = 4#64
  · subst h4; decide
  by_cases h8 : w = 8#64
  · subst h8; decide
  by_cases h16 : w = 16#64
  · subst h16; decide
  by_cases h32 : w = 32#64
  · subst h32; decide
  simp only [beq_false_of_ne h1, beq_false_of_ne h2, beq_false_of_ne h4, beq_false_of_ne h8,
    beq_false_of_ne h16, beq_false_of_ne h32, h1, h2, h4, h8, h16, h32, ite_false]

/-- One instruction's check, in the order and the terms the machine tests it: slots `0..3` zero, slot `3` at most
    `32`, the opcodes `1, 2, 4, 16` by a bit of `0x10016`, then `DEREF` (`8`) and `KECCAK` (`32`). -/
def machineOk (s : Nat → Word) : Bool :=
  (s 0 == 0#64) && (s 1 == 0#64) && (s 2 == 0#64) &&
    if s 3 ≤ 32#64 then
      if 65558#64 >>> (s 3 &&& 63#64).toNat &&& 1#64 = 0#64 then
        if s 3 = 8#64 then
          ((s 7 == 0#64 && decide (s 8 < 2#64)) || (s 7 == 1#64 && s 8 == 0#64)) && (s 9 == 0#64) &&
            (s 10 == 0#64) && (s 11 == 0#64) && (s 12 == 0#64) && (s 13 == 0#64) && (s 14 == 0#64) &&
            (s 15 == 0#64)
        else if s 3 = 32#64 then
          decide (s 12 < 2#64) && decide (s 13 < 2#64) &&
            ((s 14 == 0#64 && s 15 == 0#64) || (s 14 == 1#64 && decide (s 15 < 2#64)))
        else false
      else (s 7 == 0#64) && (s 8 == 0#64) && (s 9 == 0#64) && (s 10 == 0#64) && (s 11 == 0#64) &&
        (s 12 == 0#64) && (s 13 == 0#64) && (s 14 == 0#64) && (s 15 == 0#64)
    else false

theorem lt2 (x : Word) : decide (x < 2#64) = (x == 0#64 || x == 1#64) := by
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq, BitVec.lt_def, ← BitVec.toNat_inj]
  have : (2#64).toNat = 2 := rfl
  have : (1#64).toNat = 1 := rfl
  have : (0#64).toNat = 0 := rfl
  omega

theorem le1 (x : Word) : decide (x ≤ 1#64) = (x == 0#64 || x == 1#64) := by
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq, BitVec.le_def, ← BitVec.toNat_inj]
  have : (1#64).toNat = 1 := rfl
  have : (0#64).toNat = 0 := rfl
  omega

theorem deref_bool (a b c d : Bool) : (a && c || b && c || a && d) = (a && (c || d) || b && c) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

theorem keccak_bool (a b c d : Bool) : (a && c || b && c || b && d) = (a && c || b && (c || d)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

/-- **The machine's test is the instruction's check.** -/
theorem instr_eq (ws : List Word) (n pc : Nat) :
    Model.instructionOkRust ws n pc = machineOk (Model.slotRust ws n pc) := by
  unfold Model.instructionOkRust machineOk
  generalize Model.slotRust ws n pc = s
  simp only [find_op, lt2]
  by_cases h : s 3 ≤ 32#64
  · obtain ⟨k, hk, e⟩ : ∃ k, k ≤ 32 ∧ s 3 = BitVec.ofNat 64 k :=
      ⟨(s 3).toNat, by rw [BitVec.le_def] at h; exact h, by simp⟩
    rw [e]
    interval_cases k <;> simp [List.range', List.all_cons, List.range_succ, le1, Bool.and_assoc]
    · rw [deref_bool]
    · rw [keccak_bool]
  · have n : ∀ c : Word, c ≤ 32#64 → s 3 ≠ c := fun c hc e => h (e ▸ hc)
    simp only [n 1#64 (by decide), n 2#64 (by decide), n 4#64 (by decide), n 8#64 (by decide), n 16#64 (by decide),
      n 32#64 (by decide), h, ite_false, Bool.and_false]

/-! ## The verdicts -/

theorem ret_false {ws : List Word} {N j : Nat} (hLN : ws.length = 16 * N) (hj : j < N)
    (h : Model.instructionOkRust ws N j = false) :
    (0#64 = if Model.validEncodingRust ws = true then 1#64 else 0#64) := by
  have hN : ws.length / 16 = N := by omega
  have : Model.validEncodingRust ws = false := by
    rw [valid_eq, hN, Bool.and_eq_false_iff]
    exact Or.inr (List.all_eq_false.mpr ⟨j, List.mem_range.mpr hj, by rw [h]; decide⟩)
  rw [this]; rfl

theorem ret_false_of {ws : List Word} (h : ¬ ((ws.length / 16).isPowerOfTwo ∧ ws.length % 16 = 0 ∧
    ws.length < 17179869200)) : (0#64 = if Model.validEncodingRust ws = true then 1#64 else 0#64) := by
  have : Model.validEncodingRust ws = false := by
    rw [valid_eq, Bool.and_eq_false_iff]; exact Or.inl (decide_eq_false h)
  rw [this]; rfl

theorem ret_true {ws : List Word} {N : Nat} (hLN : ws.length = 16 * N) (hp : N.isPowerOfTwo)
    (hb : ws.length < 17179869200) (h : ∀ pc, pc < N → Model.instructionOkRust ws N pc = true) :
    (1#64 = if Model.validEncodingRust ws = true then 1#64 else 0#64) := by
  have hN : ws.length / 16 = N := by omega
  have : Model.validEncodingRust ws = true := by
    rw [valid_eq, hN, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
    exact ⟨⟨hp, by omega, hb⟩, fun pc hpc => h pc (List.mem_range.mp hpc)⟩
  rw [this]; rfl

/-! ## The words -/

/-- Slot `s`'s first word: `x + 8 s N`. -/
def slotBase (x : Word) (N s : Nat) : Word := x + BitVec.ofNat 64 (8 * (s * N))

/-- Slot `s` of instruction `j`, read through a frame that keeps the heap. -/
theorem load_slot {env : Env} {top : Word} {m M : MachineState} {x : Word} {ws : List Word} {N j : Nat} (s : Nat)
    (hf : env.Frame top Tactic.F m M) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) (hw : WordsAt m x ws)
    (hl : env.Live m x (8 * ws.length)) (hLN : ws.length = 16 * N) (hs : s < 16) (hj : j < N) :
    M.getMem (slotBase x N s + BitVec.ofNat 64 (8 * j)) = Model.slotRust ws N j s := by
  have hk : s * N + j < ws.length := by
    rw [hLN]; have := Nat.mul_le_mul_right N (show s + 1 ≤ 16 by omega); rw [Nat.succ_mul] at this; omega
  have h := ((hw.keep (Env.Frame.keeps_live hf hnx hl fun _ _ h => h)).2 (s * N + j) hk)
  rw [Model.slotRust, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some, ← h,
    slotBase, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_add]

theorem load_slot0 {env : Env} {top : Word} {m M : MachineState} {x : Word} {ws : List Word} {N j : Nat}
    (hf : env.Frame top Tactic.F m M) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) (hw : WordsAt m x ws)
    (hl : env.Live m x (8 * ws.length)) (hLN : ws.length = 16 * N) (hj : j < N) :
    M.getMem (x + BitVec.ofNat 64 (8 * j)) = Model.slotRust ws N j 0 := by
  have := load_slot 0 hf hnx hw hl hLN (by omega) hj
  simpa [slotBase] using this

/-- The loop's exit test. -/
theorem exit_iff {N j : Nat} (hN : 8 * N < 2 ^ 64) (hj : j < N) :
    BitVec.ofNat 64 (8 * N) = BitVec.ofNat 64 (8 * j) + 8#64 ↔ N = j + 1 := by
  rw [← BitVec.toNat_inj, BitVec.toNat_add]
  simp only [BitVec.toNat_ofNat]
  omega

theorem step_off (j : Nat) : BitVec.ofNat 64 (8 * j) + 8#64 = BitVec.ofNat 64 (8 * (j + 1)) := by
  rw [Nat.mul_succ, BitVec.ofNat_add]


/-! ## The loop -/

/-- The prologue's stores, with each pointer in its slot's form. -/
def stores (m : MachineState) (ret top : Word) (regs : Reg → Word) (L N : Nat) : MachineState :=
  (((((((((((((((((((m.setMem (top + 0xfffffffffffffff8#64) ret).setMem (top + 0xfffffffffffffff0#64)
    (regs .x8)).setMem (top + 0xffffffffffffffe8#64) (regs .x9)).setMem (top + 0xffffffffffffffe0#64)
    (regs .x18)).setMem (top + 0xffffffffffffffd8#64) (regs .x19)).setMem (top + 0xffffffffffffffd0#64)
    (regs .x20)).setMem (top + 0xffffffffffffffc8#64) (regs .x21)).setMem (top + 0xffffffffffffffc0#64)
    (regs .x22)).setMem (top + 0xffffffffffffffb8#64) (regs .x23)).setMem (top + 0xffffffffffffffb0#64)
    (regs .x24)).setMem (top + 0xffffffffffffffa8#64) (regs .x25)).setMem (top + 0xffffffffffffffa0#64)
    (regs .x26)).setMem (top + 0xffffffffffffff98#64) (regs .x27)).setMem (top + 0xffffffffffffff68#64)
    (BitVec.ofNat 64 L)).setMem (top + 0xffffffffffffff60#64) (BitVec.ofNat 64 L)).setMem
    (top + 0xffffffffffffff90#64) (slotBase (regs .x10) N 7)).setMem (top + 0xffffffffffffff88#64)
    (slotBase (regs .x10) N 8)).setMem (top + 0xffffffffffffff80#64) (slotBase (regs .x10) N 9)).setMem
    (top + 0xffffffffffffff78#64) (slotBase (regs .x10) N 10)).setMem (top + 0xffffffffffffff70#64)
    (slotBase (regs .x10) N 11)

/-- The loop's invariant at its head after `j` instructions, every one valid. -/
def Inv (env : Env) (ws : List Word) (N : Nat) (ret top : Word) (regs : Reg → Word) (m : MachineState) (j : Nat)
    (R : Reg → Word) (M : MachineState) : Prop :=
  R .x2 = top + 0xffffffffffffff60#64 ∧ R .x10 = regs .x10 ∧
    R .x20 = slotBase (regs .x10) N 1 ∧ R .x21 = slotBase (regs .x10) N 2 ∧ R .x22 = slotBase (regs .x10) N 3 ∧
    R .x1 = slotBase (regs .x10) N 12 ∧ R .x12 = slotBase (regs .x10) N 13 ∧
    R .x15 = slotBase (regs .x10) N 14 ∧ R .x27 = slotBase (regs .x10) N 15 ∧
    R .x25 = 65558#64 ∧ R .x29 = BitVec.ofNat 64 (8 * N) ∧ R .x30 = BitVec.ofNat 64 (8 * j) ∧
    env.Frame top Tactic.F m M ∧
    (∀ a, top + 0xffffffffffffff60#64 ≤ a → M.getMem a = (stores m ret top regs ws.length N).getMem a) ∧
    ∀ pc, pc < j → Model.instructionOkRust ws N pc = true

set_option hygiene false in
/-- The slots' loads as the model's slots, in every hypothesis. -/
local macro "slots_at_star" : tactic => `(tactic| (
  simp only [l0, ls 1 (by decide), ls 2 (by decide), ls 3 (by decide), ls 7 (by decide), ls 8 (by decide),
    ls 9 (by decide), ls 10 (by decide), ls 11 (by decide), ls 12 (by decide), ls 13 (by decide),
    ls 14 (by decide), ls 15 (by decide)] at *
  clear l0 ls))

set_option hygiene false in
/-- A path that returns `false`: the instruction it tested is not valid, by the branches it took. -/
local macro "close_bad" : tactic => `(tactic| (
  refine ret_false hLN hjN ?_
  clear hk hinv_13 hinv_14 hp hL hfail
  slots_at_star
  rw [instr_eq]
  simp_all [machineOk]))

set_option hygiene false in
/-- On a path that reaches the back edge, the instruction it tested is valid, by the branches it took. -/
local macro "have_ok" : tactic => `(tactic| (
  have hok : Model.instructionOkRust ws N j = true := by
    clear hk hinv_13 hinv_14 hp hL hfail
    slots_at_star
    rw [instr_eq]
    simp_all [machineOk]
  have hall : ∀ pc, pc < j + 1 → Model.instructionOkRust ws N pc = true := fun pc hpc => by
    rcases Nat.lt_succ_iff_lt_or_eq.mp hpc with h | h
    · exact hinv_15 pc h
    · rw [h]; exact hok))

set_option hygiene false in
/-- One pass of the body, from the head to the back edge or a return. -/
local macro "body" : tactic => `(tactic| (
  intro j R M hj hinv
  unfold Inv stores at hinv
  have hjN : j < N := by omega
  have l0 := load_slot0 hinv.2.2.2.2.2.2.2.2.2.2.2.2.1 hnx hw hl hLN hjN
  have ls := fun s hs => load_slot (j := j) s hinv.2.2.2.2.2.2.2.2.2.2.2.2.1 hnx hw hl hLN hs hjN
  rv_intro hinv
  rv_sym hp with [hL] using [hfail]
  all_goals try close_bad
  all_goals rv_sym hp with [hL] using [hfail]
  all_goals have_ok))

set_option maxHeartbeats 1000000 in
/-- **The loop**, from its head with `k + 1` instructions to go. -/
theorem loop (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (ws : List Word) (N : Nat)
    (hp : p[i]? = some (tmpl L)) (hL : L.WF p) (hfail : Spec.Runtime.NoReturn env p L.panicBoundsCheck.idx 0)
    {G : State rvIsa → Prop} {n : Nat} {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame}
    {regs : Reg → Word} {m : MachineState}
    (hk : ∀ r' m', Holds.post env (Post ws) (fun _ _ _ => False) ret top regs m r' m' →
      rvIsa.SafeN p sp1Ctx G n Q ⟨rest, r', m'⟩) (hsp16 : top.toNat % 16 = 0)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hst : env.Static m)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) (hw : WordsAt m (regs .x10) ws)
    (hl : env.Live m (regs .x10) (8 * ws.length)) (hLN : ws.length = 16 * N) (hpow : N.isPowerOfTwo)
    (hb : ws.length < 17179869200) :
    ∀ k j R M, j + k + 1 = N → Inv env ws N ret top regs m j R M →
      rvIsa.SafeN p sp1Ctx G n Q ⟨⟨i, 170, ret, top⟩ :: rest, R, M⟩ := by
  have h8N : 8 * N < 2 ^ 64 := by have := hw.1; omega
  intro k
  induction k with
  | zero =>
    body
    all_goals first
      | exact absurd ((exit_iff h8N hjN).2 (by omega)) hc
      | exact ret_true hLN hpow hb fun pc hpc => hall pc (by omega)
  | succ k ih =>
    body
    all_goals first
      | exact absurd ((exit_iff h8N hjN).1 hc) (by omega)
      | (apply ih (j + 1) _ _ (by omega)
         rv_close
         all_goals first | exact step_off j | exact hinv_14)

/-- The bounds the entry compares against the length, on a length of `16 n` words, `n ≥ 1`. -/
theorem two_lt {L N : Nat} (hL : L = 16 * N) (h0 : 0 < N) (h : L < 2 ^ 61) :
    BitVec.ofNat 64 N <<< 1 < BitVec.ofNat 64 L := by
  rw [BitVec.lt_def]; simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]; omega

theorem three_lt {L N : Nat} (hL : L = 16 * N) (h0 : 0 < N) (h : L < 2 ^ 61) :
    BitVec.ofNat 64 N <<< 1 + BitVec.ofNat 64 N < BitVec.ofNat 64 L := by
  have a1 : (BitVec.ofNat 64 N <<< 1).toNat = 2 * N := by
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]; omega
  have a2 : (BitVec.ofNat 64 N <<< 1 + BitVec.ofNat 64 N).toNat = 3 * N := by
    rw [BitVec.toNat_add, a1, BitVec.toNat_ofNat]; omega
  rw [BitVec.lt_def, a2, BitVec.toNat_ofNat]; omega

/-- A pointer the entry computes is its slot's. -/
local macro "addr_tac" : tactic => `(tactic| (
  unfold slotBase; apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_mul, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq]
  omega))

/-- **`is_valid_encoding_of_a_leanisa_program` keeps its contract.** -/
theorem ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    (hfail : Spec.Runtime.NoReturn env p L.panicBoundsCheck.idx 0) : spec env p i := by
  intro ws
  rv_auto hp with [hL] using [hfail]
  all_goals have hL64 : ws.length < 2 ^ 61 := by have := hpre_7.1; omega
  all_goals simp only [shr4 (show ws.length < 2 ^ 64 by omega)] at *
  · exact ret_false_of fun h => absurd ((pow2_iff (by omega)).2 h.1) (BitVec.not_lt.2 hc)
  · exact ret_false_of fun h => (shape_iff (by omega)).2 ⟨h.2.1, h.2.2⟩ hc
  all_goals have hpow := (pow2_iff (by omega)).1 hc_1
  all_goals obtain ⟨h16, hb⟩ := (shape_iff (by omega)).1 hc_2
  all_goals have hLN : ws.length = 16 * (ws.length / 16) := by omega
  all_goals have hN0 : 0 < ws.length / 16 := by obtain ⟨k, hk⟩ := hpow; have := Nat.one_le_two_pow (n := k); omega
  all_goals have h2 := two_lt hLN hN0 hL64
  all_goals have h3 := three_lt hLN hN0 hL64
  rotate_left
  · exact absurd h3 (BitVec.not_lt.2 hc)
  · exact absurd h2 (BitVec.not_lt.2 hc_3)
  · exact absurd h2 (BitVec.not_lt.2 hc_3)
  refine loop env p i L ws (ws.length / 16) hp hL hfail hk (by assumption) hpre_3 hpre_4 hpre_5 hpre_7 hpre_8 hLN hpow hb
    (ws.length / 16 - 1) 0 _ _ (by omega) ?_
  have e7 : regs .x10 - BitVec.ofNat 64 (ws.length / 16) <<< 3 + BitVec.ofNat 64 (ws.length / 16) <<< 6 =
      slotBase (regs .x10) (ws.length / 16) 7 := by addr_tac
  have e8 : regs .x10 + BitVec.ofNat 64 (ws.length / 16) <<< 6 = slotBase (regs .x10) (ws.length / 16) 8 := by
    addr_tac
  have e9 : regs .x10 + BitVec.ofNat 64 (ws.length / 16) <<< 3 + BitVec.ofNat 64 (ws.length / 16) <<< 6 =
      slotBase (regs .x10) (ws.length / 16) 9 := by addr_tac
  have e10 : regs .x10 + BitVec.ofNat 64 (ws.length / 16) <<< 4 + BitVec.ofNat 64 (ws.length / 16) <<< 6 =
      slotBase (regs .x10) (ws.length / 16) 10 := by addr_tac
  have e11 : regs .x10 + BitVec.ofNat 64 (ws.length / 16) * 88#64 = slotBase (regs .x10) (ws.length / 16) 11 := by
    addr_tac
  rv_close
  all_goals first
    | addr_tac
    | (apply BitVec.eq_of_toNat_eq
       simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
       omega)
    | (intro pc hpc; omega)
    | (intro a _; rw [e7, e8, e9, e10, e11]; rfl)

end Rv64mc.Proof.Bytecode.IsValidEncoding
