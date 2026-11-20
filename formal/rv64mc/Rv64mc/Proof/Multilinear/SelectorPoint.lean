/-
  Rv64mc.Proof.Multilinear.SelectorPoint

  `selector_point` keeps its contract (`Spec.Multilinear.SelectorPoint.spec`), over any program holding its
  template, from the contracts of `alloc`, `Vec::reserve` and `handle_error`. The code checks the byte count,
  allocates it (or takes the dangling pointer `8` for none), builds the header in its frame (`sp`: capacity, pointer,
  length `0`), reserves the length (which keeps the header: the capacity is the length), writes the bits into the
  block (`loop`, its memory `MemInv`), and copies the header to `sret` (`fin`).

  `rv_auto` steps up to `reserve`'s return (instruction 78, `stop`), where `after_of` turns the two paths into one
  `After` and `tail` goes on. What `rv_auto` leaves is memory it has no rule for: `reserve`'s `out` in the function's
  own stack (`frame_call_own`), the stores into the block (`frame_store_heap`, `mem_step`), the stores into `sret`,
  apart from the stack and the block (`owned_ne_stack`, `owned_ne_fresh`), and the loads past them.
-/

import Rv64mc.Spec.Multilinear.SelectorPoint
import Rv64mc.Spec.Runtime.Alloc
import Rv64mc.Spec.Runtime.VecReserve
import Rv64mc.Spec.Runtime.Panic
import Rv64mc.Proof.Layout.Out
import Rv64mc.Proof.Multilinear.Heap
import Rv64mc.Proof.Multilinear.SliceLoop
import Rv64mc.Gen.Tmpl.Verifier.Multilinear.SelectorPoint
import Rv64mc.Tactic.Sym

namespace Rv64mc.Proof.Multilinear.SelectorPoint

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters Rv64mc.Spec.Multilinear.SelectorPoint Rv64mc.Spec.Runtime
  Rv64mc.Proof.Multilinear Rv64mc.Proof.Layout
open Rv64mc.Gen.Verifier.Multilinear.SelectorPoint (Link tmpl)

/-! ## Bits -/

theorem shift_amt (k : Nat) : (BitVec.ofNat 64 k &&& 63#64).toNat = k % 64 := by
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, show (63#64).toNat = 2 ^ 6 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod_of_dvd _ (by norm_num)]

/-- Bit `k` of the selector as the code computes it: the limbs of `selectorPointRust`'s element `k`. -/
theorem bit_limbs (n : Word) (k : Nat) :
    Model.limbs (Model.bitE n k) = ((n >>> (BitVec.ofNat 64 k &&& 63#64).toNat) &&& 1#64, 0#64) := by
  rw [Model.bitE, Model.eNew, Model.limbs_ofK, BF64.toBitVec_ofBitVec, shift_amt]

theorem elem_limbs (n : Word) {len k : Nat} (hk : k < ((Model.selectorPointRust n len).map Model.limbs).length) :
    ((Model.selectorPointRust n len).map Model.limbs)[k] =
      ((n >>> (BitVec.ofNat 64 k &&& 63#64).toNat) &&& 1#64, 0#64) := by
  simp [Model.selectorPointRust, bit_limbs]

/-- The elements as the loop stores them. -/
theorem elist_of {M : MachineState} {q : Word} {xs : List (Word × Word)} (hb : q.toNat + 16 * xs.length < 2 ^ 64)
    (h : ∀ k (hk : k < xs.length), M.getMem (q + BitVec.ofNat 64 (16 * k)) = xs[k].1 ∧
      M.getMem (q + BitVec.ofNat 64 (16 * k) + 8#64) = xs[k].2) : EListAt M q xs :=
  ⟨by simpa using hb, fun k hk => by simpa [EAt] using h k hk⟩

/-! ## The stores into `sret` -/

theorem ne8 (a : Word) : a + 8#64 ≠ a := Tactic.add_ne (by decide)
theorem ne16 (a : Word) : a + 16#64 ≠ a := Tactic.add_ne (by decide)
theorem ne8_16 (a : Word) : a + 8#64 ≠ a + 16#64 := Tactic.add_ne_add (by decide)

/-- The stack bound gives the frame's slots as numbers. -/
theorem slots {top : Word} {S : Nat} (h : S + 64 ≤ top.toNat) :
    (top + 18446744073709551608#64).toNat = top.toNat - 8 ∧ (top + 18446744073709551600#64).toNat = top.toNat - 16 ∧
    (top + 18446744073709551592#64).toNat = top.toNat - 24 ∧ (top + 18446744073709551584#64).toNat = top.toNat - 32 ∧
    (top + 18446744073709551576#64).toNat = top.toNat - 40 ∧ (top + 18446744073709551568#64).toNat = top.toNat - 48 ∧
    (top + 18446744073709551560#64).toNat = top.toNat - 56 ∧ (top + 18446744073709551552#64).toNat = top.toNat - 64 :=
  ⟨slot_toNat (by decide) (by omega) (by decide), slot_toNat (by decide) (by omega) (by decide),
    slot_toNat (by decide) (by omega) (by decide), slot_toNat (by decide) (by omega) (by decide),
    slot_toNat (by decide) (by omega) (by decide), slot_toNat (by decide) (by omega) (by decide),
    slot_toNat (by decide) (by omega) (by decide), slot_toNat (by decide) (by omega) (by decide)⟩

/-- **The header copied to `sret`**, from a memory `M` that keeps the entry's frame, the saved registers, the
    header in the frame's slots (capacity at `sp`, pointer at `sp + 8`) and the elements at its pointer. -/
theorem fin {env : Env} {m M : MachineState} {top ret L : Word} {regs : Reg → Word} {xs : List (Word × Word)}
    (hown : env.Owned m top (regs .x10) Layouts.Vec.byteSize) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hlim : env.stackLimit.toNat + 64 ≤ top.toNat) (hF : env.Frame top Tactic.F m M) (hS : env.Static M)
    (h8 : M.getMem (top + 18446744073709551608#64) = ret) (h16 : M.getMem (top + 18446744073709551600#64) = regs .x8)
    (h24 : M.getMem (top + 18446744073709551592#64) = regs .x9)
    (h32 : M.getMem (top + 18446744073709551584#64) = regs .x18)
    (h40 : M.getMem (top + 18446744073709551576#64) = regs .x19)
    (hel : EListAt M (M.getMem (top + 18446744073709551560#64)) xs) (hL : L = BitVec.ofNat 64 xs.length)
    (hcap : xs.length ≤ (M.getMem (top + 18446744073709551552#64)).toNat)
    (hcl : (M.getMem (top + 18446744073709551552#64)).toNat < 2 ^ 63)
    (hfr : (M.getMem (top + 18446744073709551552#64)).toNat = 0 ∨ env.Fresh m M
      (M.getMem (top + 18446744073709551560#64)) (Layouts.E.byteSize * (M.getMem (top + 18446744073709551552#64)).toNat)) :
    let Mf := ((M.setMem (regs .x10) (M.getMem (top + 18446744073709551552#64))).setMem (regs .x10 + 8#64)
      (M.getMem (top + 18446744073709551560#64))).setMem (regs .x10 + 16#64) L
    Mf.getMem (top + 18446744073709551608#64) = ret ∧ Mf.getMem (top + 18446744073709551600#64) = regs .x8 ∧
      Mf.getMem (top + 18446744073709551592#64) = regs .x9 ∧
      Mf.getMem (top + 18446744073709551584#64) = regs .x18 ∧
      Mf.getMem (top + 18446744073709551576#64) = regs .x19 ∧
      env.Frame top (Spec.Whir.SretOut Layouts.Vec.byteSize regs m) m Mf ∧ env.Static Mf ∧
      ∃ ptr cap, VecAt EListAt Mf (regs .x10) ptr cap xs ∧
        (cap = 0 ∨ env.Fresh m Mf ptr (Layouts.E.byteSize * cap)) := by
  intro Mf
  have hl0 : env.stackLimit.toNat ≤ top.toNat := by omega
  have s0 := owned_slot0 hown hnx hl0 (by decide)
  have s8 := owned_slot (k := 8) hown hnx hl0 (by decide)
  have s16 := owned_slot (k := 16) hown hnx hl0 (by decide)
  obtain ⟨e8, e16, e24, e32, e40, -, -, -⟩ := slots hlim
  have hst : ∀ s : Word, env.stackLimit.toNat ≤ s.toNat → s.toNat < top.toNat → Mf.getMem s = M.getMem s :=
    fun s h1 h2 => by
      simp only [Mf]
      rw [MachineState.getMem_setMem_ne (owned_ne_stack hown hnx s16.1 h1 h2).symm,
        MachineState.getMem_setMem_ne (owned_ne_stack hown hnx s8.1 h1 h2).symm,
        MachineState.getMem_setMem_ne (owned_ne_stack hown hnx s0.1 h1 h2).symm]
  have hnf : env.next Mf = env.next M := by
    simp only [Mf, Env.next]
    rw [MachineState.getMem_setMem_ne (Ne.symm s16.2.1), MachineState.getMem_setMem_ne (Ne.symm s8.2.1),
      MachineState.getMem_setMem_ne (Ne.symm s0.2.1)]
  refine ⟨by rw [hst _ (by omega) (by omega), h8], by rw [hst _ (by omega) (by omega), h16],
    by rw [hst _ (by omega) (by omega), h24], by rw [hst _ (by omega) (by omega), h32],
    by rw [hst _ (by omega) (by omega), h40],
    frame_setMem_out (frame_setMem_out (frame_setMem_out (Tactic.frame_weaken hF) s0.1 s0.2.1) s8.1 s8.2.1)
      s16.1 s16.2.1,
    Env.static_setMem (Env.static_setMem (Env.static_setMem hS s0.2.2) s8.2.2) s16.2.2,
    M.getMem (top + 18446744073709551560#64), (M.getMem (top + 18446744073709551552#64)).toNat,
    ⟨?_, ?_, ?_, hcap, hcl, ?_⟩, ?_⟩
  · simp only [vecPtr, Layouts.Vec.ptr, Mf]
    rw [MachineState.getMem_setMem_ne (ne8_16 _), MachineState.getMem_setMem_eq]
  · simp only [vecCap, Layouts.Vec.cap, BitVec.add_zero, Mf, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rw [MachineState.getMem_setMem_ne (ne16 _).symm, MachineState.getMem_setMem_ne (ne8 _).symm,
      MachineState.getMem_setMem_eq]
  · simp only [vecLen, Layouts.Vec.len, Mf]
    rw [MachineState.getMem_setMem_eq, hL]
  · rcases hfr with h | h
    · have : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst this; exact ⟨by simpa using BitVec.isLt _, fun k hk => by simp at hk⟩
    · refine hel.keep fun b hb => ?_
      have := hel.1
      have hb' : b.toNat < env.heapEnd.toNat := by
        have := hb.2; have := h.2; have := hF.2.1; simp only [Layouts.E.byteSize] at *; omega
      have hb1 : (env.next m).toNat ≤ b.toNat := by have := hb.1; have := h.1; omega
      simp only [Mf]
      rw [MachineState.getMem_setMem_ne (owned_ne_fresh hown hl0 s16.1 hb1 hb').symm,
        MachineState.getMem_setMem_ne (owned_ne_fresh hown hl0 s8.1 hb1 hb').symm,
        MachineState.getMem_setMem_ne (owned_ne_fresh hown hl0 s0.1 hb1 hb').symm]
  · rcases hfr with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h.1, by rw [hnf]; exact h.2⟩

/-! ## The loop's memory -/

/-- The bit the loop stores for element `k`. -/
abbrev bit (sel : Word) (k : Nat) : Word := (sel >>> (BitVec.ofNat 64 k &&& 63#64).toNat) &&& 1#64

/-- The memory after `j` elements: the entry's frame, the static data, `NEXT` and the function's stack as after
    `reserve` (`M`), the first `j` elements at `q`. -/
def MemInv (env : Env) (m M : MachineState) (top q sel : Word) (j : Nat) (M' : MachineState) : Prop :=
  env.Frame top Tactic.F m M' ∧ env.Static M' ∧ env.next M' = env.next M ∧
    (∀ a : Word, env.stackLimit.toNat ≤ a.toNat → M'.getMem a = M.getMem a) ∧
    ∀ k, k < j → M'.getMem (q + BitVec.ofNat 64 (16 * k)) = bit sel k ∧
      M'.getMem (q + BitVec.ofNat 64 (16 * k) + 8#64) = 0#64

theorem memInv_zero {env : Env} {m M : MachineState} {top q sel : Word} (hF : env.Frame top Tactic.F m M)
    (hS : env.Static M) : MemInv env m M top q sel 0 M :=
  ⟨hF, hS, rfl, fun _ _ => rfl, fun _ hk => absurd hk (Nat.not_lt_zero _)⟩

/-- **One element stored.** -/
theorem mem_step {env : Env} {m M M' : MachineState} {top q sel : Word} {j len : Nat}
    (hlo : (env.next m).toNat ≤ q.toNat) (hhi : q.toNat + 16 * len ≤ (env.next M).toNat)
    (hnx : (env.next M).toNat ≤ env.heapEnd.toNat) (hj : j < len) (h : MemInv env m M top q sel j M') :
    MemInv env m M top q sel (j + 1) ((M'.setMem (q + BitVec.ofNat 64 (16 * j)) (bit sel j)).setMem
      (q + BitVec.ofNat 64 (16 * j) + 8#64) 0#64) := by
  obtain ⟨hF, hS, hn, hk, he⟩ := h
  have hlay := env.layout
  have hq : q.toNat + 16 * len < 2 ^ 64 := by have := env.heapEnd.isLt; omega
  have a1 : (q + BitVec.ofNat 64 (16 * j)).toNat = q.toNat + 16 * j := toNat_add_ofNat (by omega)
  have a2 : (q + BitVec.ofNat 64 (16 * j) + 8#64).toNat = q.toNat + 16 * j + 8 := by
    rw [toNat_add_ofNat (k := 8) (by omega), a1]
  have hn1 : env.next (M'.setMem (q + BitVec.ofNat 64 (16 * j)) (bit sel j)) = env.next M := by
    rw [next_store_heap (by omega), hn]
  refine ⟨frame_store_heap (frame_store_heap hF (by omega) (by rw [hn]; omega)) (by omega) (by rw [hn1]; omega),
    static_store_heap (static_store_heap hS (by omega)) (by omega),
    by rw [next_store_heap (by omega), hn1], fun a ha => ?_, fun k hk => ?_⟩
  · have hst : env.heapEnd.toNat < a.toNat := by omega
    rw [MachineState.getMem_setMem_ne (fun e => by rw [e] at hst; omega),
      MachineState.getMem_setMem_ne (fun e => by rw [e] at hst; omega), hk a ha]
  · have b1 : (q + BitVec.ofNat 64 (16 * k)).toNat = q.toNat + 16 * k := toNat_add_ofNat (by omega)
    have b2 : (q + BitVec.ofNat 64 (16 * k) + 8#64).toNat = q.toNat + 16 * k + 8 := by
      rw [toNat_add_ofNat (k := 8) (by omega), b1]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · have ne : ∀ x y : Word, x.toNat ≠ y.toNat → x ≠ y := fun x y h e => h (by rw [e])
      rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_ne (ne _ _ (by omega)),
        MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_ne (ne _ _ (by omega))]
      exact he k hk
    · exact ⟨by rw [MachineState.getMem_setMem_ne (ne8 _).symm, MachineState.getMem_setMem_eq],
        MachineState.getMem_setMem_eq⟩


/-! ## The loop -/

theorem cnt_step (j : Nat) : BitVec.ofNat 64 j + 1#64 = BitVec.ofNat 64 (j + 1) := by
  rw [BitVec.ofNat_add]

theorem cnt_iff {x : Word} {j : Nat} (hx : j + 1 < 2 ^ 64) : x = BitVec.ofNat 64 j + 1#64 ↔ x.toNat = j + 1 := by
  rw [cnt_step]
  constructor
  · intro h; subst h; simp; omega
  · intro h; apply BitVec.eq_of_toNat_eq; simp; omega

/-- What the function keeps from `reserve`'s return on: its frame from the entry, the saved registers, the header
    (capacity at `sp`, pointer at `sp + 8`, length `0` at `sp + 16`), the block. -/
def After (env : Env) (m : MachineState) (top ret : Word) (regs : Reg → Word) (M : MachineState) : Prop :=
  env.Frame top Tactic.F m M ∧ env.Static M ∧
    M.getMem (top + 18446744073709551608#64) = ret ∧ M.getMem (top + 18446744073709551600#64) = regs .x8 ∧
    M.getMem (top + 18446744073709551592#64) = regs .x9 ∧ M.getMem (top + 18446744073709551584#64) = regs .x18 ∧
    M.getMem (top + 18446744073709551576#64) = regs .x19 ∧ M.getMem (top + 18446744073709551568#64) = 0#64 ∧
    (regs .x12).toNat * 16 < 2 ^ 63 ∧
    ((regs .x12).toNat = 0 ∧ M.getMem (top + 18446744073709551552#64) = 0#64 ∨
      M.getMem (top + 18446744073709551552#64) = regs .x12 ∧
        env.Fresh m M (M.getMem (top + 18446744073709551560#64)) (16 * (regs .x12).toNat))

/-- The loop's invariant at its head after `j` elements. -/
def Inv (env : Env) (m M : MachineState) (top q : Word) (regs : Reg → Word) (j : Nat) (R : Reg → Word)
    (M' : MachineState) : Prop :=
  R .x2 = top + 18446744073709551552#64 ∧ R .x8 = regs .x12 ∧ R .x9 = regs .x10 ∧ R .x18 = regs .x11 ∧
    R .x10 = M.getMem (top + 18446744073709551568#64) + regs .x12 ∧ R .x11 = q + BitVec.ofNat 64 (16 * j) + 8#64 ∧
    R .x12 = BitVec.ofNat 64 j ∧ R .x20 = regs .x20 ∧ R .x21 = regs .x21 ∧ R .x22 = regs .x22 ∧
    R .x23 = regs .x23 ∧ R .x24 = regs .x24 ∧ R .x25 = regs .x25 ∧ R .x26 = regs .x26 ∧ R .x27 = regs .x27 ∧
    MemInv env m M top q (regs .x11) j M'

/-- The header copied to `sret` after the last element: `fin`'s facts from the loop's. -/
theorem exit_fin {env : Env} {m M M' : MachineState} {top ret q : Word} {regs : Reg → Word} {j : Nat}
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) (hlim : env.stackLimit.toNat + 64 ≤ top.toNat)
    (hown : env.Owned m top (regs .x10) Layouts.Vec.byteSize) (hA : After env m top ret regs M)
    (hq : q = M.getMem (top + 18446744073709551560#64)) (hj : j + 1 = (regs .x12).toNat)
    (hm : MemInv env m M top q (regs .x11) j M') :
    let M'' := (M'.setMem (q + BitVec.ofNat 64 (16 * j)) (bit (regs .x11) j)).setMem
      (q + BitVec.ofNat 64 (16 * j) + 8#64) 0#64
    let Mf := ((M''.setMem (regs .x10) (M''.getMem (top + 18446744073709551552#64))).setMem (regs .x10 + 8#64)
      (M''.getMem (top + 18446744073709551560#64))).setMem (regs .x10 + 16#64)
      (M.getMem (top + 18446744073709551568#64) + regs .x12)
    Mf.getMem (top + 18446744073709551608#64) = ret ∧ Mf.getMem (top + 18446744073709551600#64) = regs .x8 ∧
      Mf.getMem (top + 18446744073709551592#64) = regs .x9 ∧
      Mf.getMem (top + 18446744073709551584#64) = regs .x18 ∧
      Mf.getMem (top + 18446744073709551576#64) = regs .x19 ∧
      env.Frame top (Spec.Whir.SretOut Layouts.Vec.byteSize regs m) m Mf ∧ env.Static Mf ∧
      ∃ ptr cap, VecAt EListAt Mf (regs .x10) ptr cap
          ((Model.selectorPointRust (regs .x11) (regs .x12).toNat).map Model.limbs) ∧
        (cap = 0 ∨ env.Fresh m Mf ptr (Layouts.E.byteSize * cap)) := by
  intro M'' Mf
  obtain ⟨hF, hS, a8, a16, a24, a32, a40, a48, hb, hc⟩ := hA
  obtain ⟨e8, e16, e24, e32, e40, e48, e56, e64⟩ := slots hlim
  have hc' : M.getMem (top + 18446744073709551552#64) = regs .x12 ∧
      env.Fresh m M (M.getMem (top + 18446744073709551560#64)) (16 * (regs .x12).toNat) := by
    rcases hc with h | h
    · omega
    · exact h
  have mi := mem_step (len := (regs .x12).toNat) (by rw [hq]; exact hc'.2.1) (by rw [hq]; exact hc'.2.2) hF.2.1
    (by omega) hm
  have hk : ∀ s : Word, env.stackLimit.toNat ≤ s.toNat → M''.getMem s = M.getMem s := mi.2.2.2.1
  have hlen : (regs .x12).toNat < 2 ^ 63 := by omega
  refine fin hown hnx hlim mi.1 mi.2.1 (by rw [hk _ (by omega), a8]) (by rw [hk _ (by omega), a16])
    (by rw [hk _ (by omega), a24]) (by rw [hk _ (by omega), a32]) (by rw [hk _ (by omega), a40]) ?_
    (by rw [a48, BitVec.zero_add]; simp [Model.selectorPointRust]) (by rw [hk _ (by omega), hc'.1]; simp [Model.selectorPointRust])
    (by rw [hk _ (by omega), hc'.1]; exact hlen)
    (Or.inr (by
      rw [hk _ (by omega), hk _ (by omega), hc'.1]
      exact ⟨hc'.2.1, by rw [mi.2.2.1]; exact hc'.2.2⟩))
  rw [hk _ (by omega), ← hq]
  have hq2 := hc'.2.2
  rw [← hq] at hq2
  refine elist_of (by simp [Model.selectorPointRust]; have := env.heapEnd.isLt; have := hF.2.1; omega)
    fun k hk' => ?_
  rw [elem_limbs]
  simp only [List.length_map, Model.selectorPointRust, List.length_range] at hk'
  exact mi.2.2.2.2 k (by omega)

/-- **The loop**, from its head with `k + 1` elements to go; its last pass copies the header to `sret`. -/
theorem loop (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    {need : Nat} (hn : 64 ≤ need)
    {G : State rvIsa → Prop} {n : Nat} {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame}
    {regs : Reg → Word} {m M : MachineState} {q : Word}
    (hk : ∀ r' m', Holds.post env (Post env) (Spec.Whir.SretOut Layouts.Vec.byteSize) ret top regs m r' m' →
      rvIsa.SafeN p sp1Ctx G n Q ⟨rest, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hown : env.Owned m top (regs .x10) Layouts.Vec.byteSize) (hA : After env m top ret regs M)
    (hq : q = M.getMem (top + 18446744073709551560#64)) :
    ∀ k j R M', j + k + 1 = (regs .x12).toNat → Inv env m M top q regs j R M' →
      rvIsa.SafeN p sp1Ctx G n Q ⟨⟨i, 94, ret, top⟩ :: rest, R, M'⟩ := by
  have hlim : env.stackLimit.toNat + 64 ≤ top.toNat := by omega
  intro k
  induction k with
  | zero =>
    intro j R M' hj hinv
    rv_intro hinv
    rv_sym hp
    · exact absurd ((cnt_iff (by have := (regs .x12).isLt; omega)).2 (by omega)) hc
    all_goals
      have fn := exit_fin hnx hlim hown hA hq (by omega) ⟨hinv_16, hinv_17, hinv_18, hinv_19, hinv_20⟩
    · exact fn.1
    · exact fn.2.1
    · exact fn.2.2.1
    · exact fn.2.2.2.1
    · exact fn.2.2.2.2.1
    · exact fn.2.2.2.2.2.1
    · exact fn.2.2.2.2.2.2.1
    · exact fn.2.2.2.2.2.2.2
  | succ k ih =>
    intro j R M' hj hinv
    rv_intro hinv
    rv_sym hp
    · obtain ⟨hF, -, -, -, -, -, -, -, -, hc'⟩ := hA
      have h' : M.getMem (top + 18446744073709551552#64) = regs .x12 ∧
          env.Fresh m M (M.getMem (top + 18446744073709551560#64)) (16 * (regs .x12).toNat) := by
        rcases hc' with h | h
        · omega
        · exact h
      have mi := mem_step (len := (regs .x12).toNat) (by rw [hq]; exact h'.2.1) (by rw [hq]; exact h'.2.2)
        hF.2.1 (by omega) ⟨hinv_16, hinv_17, hinv_18, hinv_19, hinv_20⟩
      apply ih (j + 1) _ _ (by omega)
      rv_close
      all_goals first
        | exact step_ptr _ _
        | exact cnt_step j
        | exact mi.1
        | exact mi.2.1
        | exact mi.2.2.1
        | exact mi.2.2.2.1
        | exact mi.2.2.2.2
    all_goals exact absurd ((cnt_iff (by have := (regs .x12).isLt; omega)).1 hc) (by omega)


/-! ## From `reserve`'s return -/

/-- The registers and memory at `reserve`'s return. -/
def TailInv (env : Env) (m : MachineState) (top ret : Word) (regs : Reg → Word) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551552#64 ∧ R .x8 = regs .x12 ∧ R .x9 = regs .x10 ∧ R .x18 = regs .x11 ∧
    R .x20 = regs .x20 ∧ R .x21 = regs .x21 ∧ R .x22 = regs .x22 ∧ R .x23 = regs .x23 ∧ R .x24 = regs .x24 ∧
    R .x25 = regs .x25 ∧ R .x26 = regs .x26 ∧ R .x27 = regs .x27 ∧ After env m top ret regs M

/-- **The rest of the function** from `reserve`'s return: the loop, or the empty header copied. -/
theorem tail (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    {need : Nat} (hn : 64 ≤ need)
    {G : State rvIsa → Prop} {n : Nat} {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame}
    {regs : Reg → Word} {m : MachineState}
    (hk : ∀ r' m', Holds.post env (Post env) (Spec.Whir.SretOut Layouts.Vec.byteSize) ret top regs m r' m' →
      rvIsa.SafeN p sp1Ctx G n Q ⟨rest, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hown : env.Owned m top (regs .x10) Layouts.Vec.byteSize) :
    ∀ R M, TailInv env m top ret regs R M → rvIsa.SafeN p sp1Ctx G n Q ⟨⟨i, 78, ret, top⟩ :: rest, R, M⟩ := by
  have hlim : env.stackLimit.toNat + 64 ≤ top.toNat := by omega
  intro R M hinv
  have hA : After env m top ret regs M := hinv.2.2.2.2.2.2.2.2.2.2.2.2
  rv_intro hinv
  rv_sym hp
  all_goals obtain ⟨hF, hS, a8, a16, a24, a32, a40, a48, hb, hc'⟩ := hA
  rotate_right
  · -- the loop
    have hq : M.getMem (top + 18446744073709551568#64) <<< 4 + M.getMem (top + 18446744073709551560#64) =
        M.getMem (top + 18446744073709551560#64) := by rw [a48]; simp
    have hl : 0 < (regs .x12).toNat := by
      have : regs .x12 ≠ 0#64 := hc
      rw [Ne, ← BitVec.toNat_inj] at this; simp at this; omega
    refine loop env p i L hp hn hk hstk hnx hown ⟨hF, hS, a8, a16, a24, a32, a40, a48, hb, hc'⟩ hq
      ((regs .x12).toNat - 1) 0 _ _ (by omega) ?_
    rv_close
    all_goals first
      | exact start_ptr _
      | exact (memInv_zero (q := _) (sel := regs .x11) hF hS).2.2.2.2
  all_goals
    have hx0 : (regs .x12).toNat = 0 := by rw [hc]; rfl
    have hcap0 : (M.getMem (top + 18446744073709551552#64)).toNat = 0 := by
      rcases hc' with h | h
      · rw [h.2]; rfl
      · rw [h.1, hx0]
    have fn := fin (M := M) (L := M.getMem (top + 18446744073709551568#64))
      (xs := (Model.selectorPointRust (regs .x11) (regs .x12).toNat).map Model.limbs) hown hnx hlim hF hS
      a8 a16 a24 a32 a40 (by rw [hx0]; exact ⟨by simpa [Model.selectorPointRust] using BitVec.isLt _, fun k hk => by simp [Model.selectorPointRust] at hk⟩) (by rw [a48, hx0]; rfl)
      (by simp [hx0, Model.selectorPointRust]) (by omega) (Or.inl hcap0)
  · exact fn.1
  · exact fn.2.1
  · exact fn.2.2.1
  · exact fn.2.2.2.1
  · exact fn.2.2.2.2.1
  · exact fn.2.2.2.2.2.1
  · exact fn.2.2.2.2.2.2.1
  · exact fn.2.2.2.2.2.2.2

/-! ## Up to `reserve`'s return -/

theorem ovf {x : Word}
    (h : BinOp.ult.eval 0#64 (x >>> 60) ||| BinOp.ult.eval 9223372036854775800#64 (x <<< 4) = 0#64) :
    (x <<< 4).toNat = 16 * x.toNat ∧ 16 * x.toNat < 2 ^ 63 := by
  by_cases h1 : BitVec.ult 0#64 (x >>> 60) <;> by_cases h2 : BitVec.ult 9223372036854775800#64 (x <<< 4) <;>
    simp [BinOp.eval, h1, h2] at h
  simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.not_lt] at h1 h2
  have := x.isLt
  have hx : x.toNat < 2 ^ 60 := by simp at h1; omega
  have e : (x.toNat * 2 ^ 4) % 2 ^ 64 = 16 * x.toNat := by rw [Nat.mod_eq_of_lt (by omega)]; omega
  rw [e] at h2
  refine ⟨by rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, e], by simp at h2; omega⟩

theorem at64_8 (t : Word) : t + 18446744073709551552#64 + BitVec.ofNat 64 8 = t + 18446744073709551560#64 := by
  rw [BitVec.add_assoc]; rfl
theorem at64_16 (t : Word) : t + 18446744073709551552#64 + BitVec.ofNat 64 16 = t + 18446744073709551568#64 := by
  rw [BitVec.add_assoc]; rfl

/-- `reserve`'s `out` is in the header. -/
theorem grow_in {R : Reg → Word} {M : MachineState} {v b : Word} (hx : R .x10 = v) (hv : v.toNat + 24 < 2 ^ 64)
    (h : GrowOut R M b) : InRange v 24 b := by
  unfold GrowOut rvCapAt rvPtrAt at h
  simp only [Layouts.RawVecInner.cap, Layouts.RawVecInner.ptr] at h
  rw [hx] at h
  rcases h with h | h <;> subst h <;> unfold InRange <;> rw [toNat_add_ofNat (by simp; omega)] <;> omega

/-- **`After` from the header the code stores** (capacity `c`, pointer `q`) over a memory `N` that keeps the
    entry's frame and the saved registers, and `reserve`'s contract. -/
theorem after_of {env : Env} {m N m3 : MachineState} {top ret c q : Word} {regs : Reg → Word} {out : Word → Prop}
    (hlim : env.stackLimit.toNat + 64 ≤ top.toNat) (hF : env.Frame top Tactic.F m N)
    (s8 : N.getMem (top + 18446744073709551608#64) = ret) (s16 : N.getMem (top + 18446744073709551600#64) = regs .x8)
    (s24 : N.getMem (top + 18446744073709551592#64) = regs .x9)
    (s32 : N.getMem (top + 18446744073709551584#64) = regs .x18)
    (s40 : N.getMem (top + 18446744073709551576#64) = regs .x19)
    (h3 : env.Frame (top + 18446744073709551552#64) out
      (((N.setMem (top + 18446744073709551552#64) c).setMem (top + 18446744073709551560#64) q).setMem
        (top + 18446744073709551568#64) 0#64) m3)
    (ho : ∀ b, out b → InRange (top + 18446744073709551552#64) 24 b) (hS3 : env.Static m3)
    (hl3 : vecLen m3 (top + 18446744073709551552#64) = vecLen
      (((N.setMem (top + 18446744073709551552#64) c).setMem (top + 18446744073709551560#64) q).setMem
        (top + 18446744073709551568#64) 0#64) (top + 18446744073709551552#64))
    (hk3 : (regs .x12).toNat ≤ (vecCap
      (((N.setMem (top + 18446744073709551552#64) c).setMem (top + 18446744073709551560#64) q).setMem
        (top + 18446744073709551568#64) 0#64) (top + 18446744073709551552#64)).toNat - (vecLen
      (((N.setMem (top + 18446744073709551552#64) c).setMem (top + 18446744073709551560#64) q).setMem
        (top + 18446744073709551568#64) 0#64) (top + 18446744073709551552#64)).toNat →
      vecCap m3 (top + 18446744073709551552#64) = vecCap
        (((N.setMem (top + 18446744073709551552#64) c).setMem (top + 18446744073709551560#64) q).setMem
          (top + 18446744073709551568#64) 0#64) (top + 18446744073709551552#64) ∧
      vecPtr m3 (top + 18446744073709551552#64) = vecPtr
        (((N.setMem (top + 18446744073709551552#64) c).setMem (top + 18446744073709551560#64) q).setMem
          (top + 18446744073709551568#64) 0#64) (top + 18446744073709551552#64))
    (hb : (regs .x12).toNat * 16 < 2 ^ 63)
    (hc : (regs .x12).toNat = 0 ∧ c = 0#64 ∨ c = regs .x12 ∧ env.Fresh m N q (16 * (regs .x12).toNat)) :
    After env m top ret regs m3 := by
  obtain ⟨e8, e16, e24, e32, e40, e48, e56, e64⟩ := slots hlim
  have r64 : (((N.setMem (top + 18446744073709551552#64) c).setMem (top + 18446744073709551560#64) q).setMem
      (top + 18446744073709551568#64) 0#64).getMem (top + 18446744073709551552#64) = c := by
    rw [MachineState.getMem_setMem_ne (Tactic.add_ne_add (by decide)),
      MachineState.getMem_setMem_ne (Tactic.add_ne_add (by decide)), MachineState.getMem_setMem_eq]
  have r56 : (((N.setMem (top + 18446744073709551552#64) c).setMem (top + 18446744073709551560#64) q).setMem
      (top + 18446744073709551568#64) 0#64).getMem (top + 18446744073709551560#64) = q := by
    rw [MachineState.getMem_setMem_ne (Tactic.add_ne_add (by decide)), MachineState.getMem_setMem_eq]
  simp only [vecCap, vecPtr, vecLen, Layouts.Vec.cap, Layouts.Vec.ptr, Layouts.Vec.len, BitVec.add_zero,
    at64_8, at64_16, MachineState.getMem_setMem_eq, r64, r56] at hl3 hk3
  have hcap : (regs .x12).toNat ≤ c.toNat := by
    rcases hc with h | h
    · omega
    · rw [h.1]
  obtain ⟨hk64, hk56⟩ := hk3 (by simpa using hcap)
  have hin : ∀ b, InRange (top + 18446744073709551552#64) 24 b →
      env.stackLimit.toNat ≤ b.toNat ∧ b.toNat < top.toNat := fun b hb => by unfold InRange at hb; omega
  have f2 : env.Frame top Tactic.F m
      (((N.setMem (top + 18446744073709551552#64) c).setMem (top + 18446744073709551560#64) q).setMem
        (top + 18446744073709551568#64) 0#64) :=
    Tactic.frame_store (Tactic.frame_store (Tactic.frame_store hF (by omega) (by omega)) (by omega) (by omega))
      (by omega) (by omega)
  have f3 := frame_call_own f2 h3 (by omega) fun b hb => hin b (ho b hb)
  have k : ∀ a : Word, top.toNat - 40 ≤ a.toNat → a.toNat < top.toNat → m3.getMem a = N.getMem a :=
    fun a ha1 ha2 => by
      have hn1 : ∀ c : Word, c.toNat < top.toNat - 40 → a ≠ c := fun c hc he => by rw [he] at ha1; omega
      rw [h3.getMem_above (by omega) (by omega) fun hb => by have := ho a hb; unfold InRange at this; omega,
        MachineState.getMem_setMem_ne (hn1 _ (by omega)), MachineState.getMem_setMem_ne (hn1 _ (by omega)),
        MachineState.getMem_setMem_ne (hn1 _ (by omega))]
  refine ⟨f3, hS3, by rw [k _ (by omega) (by omega), s8], by rw [k _ (by omega) (by omega), s16],
    by rw [k _ (by omega) (by omega), s24], by rw [k _ (by omega) (by omega), s32],
    by rw [k _ (by omega) (by omega), s40], hl3, hb, ?_⟩
  rw [hk64, hk56]
  rcases hc with h | h
  · exact Or.inl h
  · refine Or.inr ⟨h.1, h.2.1, ?_⟩
    have := h.2.2; have := f2.1; have := h3.1
    have hn : env.next (((N.setMem (top + 18446744073709551552#64) c).setMem (top + 18446744073709551560#64)
        q).setMem (top + 18446744073709551568#64) 0#64) = env.next N := by
      rw [Env.next_setMem_stack (by omega), Env.next_setMem_stack (by omega), Env.next_setMem_stack (by omega)]
    rw [hn] at this; omega

theorem hdr_reads (N : MachineState) (t c q : Word) :
    (((N.setMem (t + 18446744073709551552#64) c).setMem (t + 18446744073709551560#64) q).setMem
        (t + 18446744073709551568#64) 0#64).getMem (t + 18446744073709551552#64) = c ∧
    (((N.setMem (t + 18446744073709551552#64) c).setMem (t + 18446744073709551560#64) q).setMem
        (t + 18446744073709551568#64) 0#64).getMem (t + 18446744073709551560#64) = q ∧
    (((N.setMem (t + 18446744073709551552#64) c).setMem (t + 18446744073709551560#64) q).setMem
        (t + 18446744073709551568#64) 0#64).getMem (t + 18446744073709551568#64) = 0#64 := by
  refine ⟨?_, ?_, MachineState.getMem_setMem_eq⟩
  · rw [MachineState.getMem_setMem_ne (Tactic.add_ne_add (by decide)),
      MachineState.getMem_setMem_ne (Tactic.add_ne_add (by decide)), MachineState.getMem_setMem_eq]
  · rw [MachineState.getMem_setMem_ne (Tactic.add_ne_add (by decide)), MachineState.getMem_setMem_eq]

/-- The prologue's stores, read back; their frame and `NEXT`. -/
theorem prologue {env : Env} {m : MachineState} {top ret : Word} {regs : Reg → Word}
    (hlim : env.stackLimit.toNat + 64 ≤ top.toNat) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) :
    let M0 := ((((m.setMem (top + 18446744073709551608#64) ret).setMem (top + 18446744073709551600#64)
      (regs .x8)).setMem (top + 18446744073709551592#64) (regs .x9)).setMem (top + 18446744073709551584#64)
      (regs .x18)).setMem (top + 18446744073709551576#64) (regs .x19)
    env.Frame top Tactic.F m M0 ∧ env.next M0 = env.next m ∧
      M0.getMem (top + 18446744073709551608#64) = ret ∧ M0.getMem (top + 18446744073709551600#64) = regs .x8 ∧
      M0.getMem (top + 18446744073709551592#64) = regs .x9 ∧ M0.getMem (top + 18446744073709551584#64) = regs .x18 ∧
      M0.getMem (top + 18446744073709551576#64) = regs .x19 := by
  intro M0
  obtain ⟨e8, e16, e24, e32, e40, -, -, -⟩ := slots hlim
  refine ⟨Tactic.frame_store (Tactic.frame_store (Tactic.frame_store (Tactic.frame_store (Tactic.frame_store
      (Tactic.frame_refl hnx) (by omega) (by omega)) (by omega) (by omega)) (by omega) (by omega)) (by omega)
      (by omega)) (by omega) (by omega), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [M0]
    rw [Env.next_setMem_stack (by omega), Env.next_setMem_stack (by omega), Env.next_setMem_stack (by omega),
      Env.next_setMem_stack (by omega), Env.next_setMem_stack (by omega)]
  all_goals simp only [M0]; repeat rw [MachineState.getMem_setMem_ne (Tactic.add_ne_add (by decide))]
  all_goals rw [MachineState.getMem_setMem_eq]

/-- **`selector_point` keeps its contract.** -/
theorem ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needA needR needH : Nat} (hnA : 64 + needA ≤ need) (hnR : 64 + needR ≤ need) (hnH : 64 + needH ≤ need)
    (hal : AllocSpec env p L.alloc.idx needA)
    (hres : ReserveSpec env 8 16 p L.reserve.idx needR)
    (hhe : NoReturn env p L.handleError.idx needH) : spec env p i need := by
  rv_auto hp stop [78] with [hL] using [hal, hres, hhe]
  all_goals have hlim : env.stackLimit.toNat + 64 ≤ top.toNat := by omega
  all_goals obtain ⟨e8, e16, e24, e32, e40, e48, e56, e64⟩ := slots hlim
  all_goals have hov := ovf hc_1
  all_goals obtain ⟨hF0, hn0, p8, p16, p24, p32, p40⟩ := prologue (ret := ret) (regs := regs) hlim hpre_5
  all_goals have hown : env.Owned m top (regs .x10) Layouts.Vec.byteSize :=
    ⟨by rw [hpre_2] at hpre_6; exact hpre_6, hpre_7⟩
  -- no bytes: the dangling buffer
  · exact Or.inr (by omega)
  · simp only [Layouts.Vec.byteSize]; have := top.isLt; omega
  · exact Or.inr (by omega)
  · simp only [Layouts.RawVecInner.byteSize]; have := top.isLt; omega
  · decide
  · decide
  · decide
  · left; simp only [rvCapAt, Layouts.RawVecInner.cap, BitVec.add_zero]; rw [(hdr_reads _ _ _ _).1, hc]; rfl
  · simp only [rvCapAt, Layouts.RawVecInner.cap, BitVec.add_zero]; rw [(hdr_reads _ _ _ _).1, hc]; decide
  · simp only [vecLen, Layouts.Vec.len]; rw [at64_16, (hdr_reads _ _ _ _).2.2]; simp
  · refine tail env p i L hp (by omega) hk hpre_3 hpre_5 hown _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, after_of hlim hF0 p8 p16 p24 p32 p40 hret1_14 (fun b h => grow_in rfl (by omega) h) hret1_15
      hret1_16 hret1_17 (by omega) (Or.inl ⟨?_, hc⟩)⟩
    have := hov.1; rw [hc] at this; simp at this; omega
  -- a block from `alloc`
  · rw [hov.1]; omega
  · exact Or.inr (by omega)
  · simp only [Layouts.Vec.byteSize]; have := top.isLt; omega
  · exact Or.inr (by omega)
  · simp only [Layouts.RawVecInner.byteSize]; have := top.isLt; omega
  · decide
  · decide
  · decide
  · right
    simp only [rvCapAt, rvPtrAt, Layouts.RawVecInner.cap, Layouts.RawVecInner.ptr, BitVec.add_zero, at64_8]
    rw [(hdr_reads _ _ _ _).1, (hdr_reads _ _ _ _).2.1]
    unfold Env.Live
    rw [Env.next_setMem_stack (by omega), Env.next_setMem_stack (by omega), Env.next_setMem_stack (by omega)]
    rw [hov.1] at hret2_18; omega
  · simp only [rvCapAt, Layouts.RawVecInner.cap, BitVec.add_zero]; rw [(hdr_reads _ _ _ _).1]; omega
  · simp only [vecLen, Layouts.Vec.len]; rw [at64_16, (hdr_reads _ _ _ _).2.2]; simp
  · have hF2 := Tactic.frame_call hF0 hret2_14 (by omega)
    have k2 : ∀ a : Word, top.toNat - 64 ≤ a.toNat → m2.getMem a = _ := fun a ha =>
      keep2_1 a (by rw [BitVec.le_def]; omega)
    refine tail env p i L hp (by omega) hk hpre_3 hpre_5 hown _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, after_of hlim hF2 (by rw [k2 _ (by omega), p8]) (by rw [k2 _ (by omega), p16])
      (by rw [k2 _ (by omega), p24]) (by rw [k2 _ (by omega), p32]) (by rw [k2 _ (by omega), p40]) hret3_14
      (fun b h => grow_in rfl (by omega) h) hret3_15 hret3_16 hret3_17 (by omega)
      (Or.inr ⟨rfl, by rw [hn0] at hret2_16; exact hret2_16, by rw [hov.1] at hret2_18; omega⟩)⟩

end Rv64mc.Proof.Multilinear.SelectorPoint
