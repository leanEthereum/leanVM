import Rv64Verifier.Proofs.Walk.Limbs
import Rv64Verifier.Proofs.Runtime.Contracts

/-!
# `walk`: `table_rows` and the rate

From `0x800011b8`: the bounds traps of `announced[1..7]` and `announced[7]` (the length is at least
`8` past them), `table_rows` allocated (`alloc(8, 48)`) and filled with the low limbs of
`announced[1..7]`, `log_memory = announced[0].c0` in `s9`, then the rate check
`log_inverse_rate - 1 <ᵤ 4` (`Err` at `0x800012b8`). At `0x80001238` (`Rows`) the code runs what is
left of `walk` past the rate's `TM.require` (`afterRate`).
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-! ## The announced sizes' parts -/

def lmOf (A : List E) : Word := ((A.getD 0 0).limb 0).toBitVec

def rowsOf (A : List E) : List Word :=
  ((A.drop 1).take LayoutMirror.nTablesRust).map fun value ↦ (value.limb 0).toBitVec

def rateOf (A : List E) : Word := ((A.getD (1 + LayoutMirror.nTablesRust) 0).limb 0).toBitVec

/-- `walk` past the rate's check. -/
def afterRate (s : MachineState) (A : List E) : TM SummaryRust :=
  ((TM.ofOption (LayoutMirror.buildLayoutRust
      (BitVec.ofNat 64 (Proofs.Bytecode.readBytecode s (s.getReg .x11)).len) (lmOf A) (rowsOf A)) >>=
    fun layout ↦ TM.require (Pcs.minStackedLog ≤ layout.stackLog ∧
      layout.stackLog ≤ Pcs.maxStackedLog) >>= fun _ ↦ pure (layout, rowsOf A, rateOf A)) >>=
    bodyRest (Proofs.Bytecode.readBytecode s (s.getReg .x11)) (bytesAt s (s.getReg .x12) 32)) >>=
    finishRust

theorem afterHigh_eq (s : MachineState) (A : List E) :
    afterHigh s A = TM.require (1#64 ≤ rateOf A ∧ rateOf A ≤ 4#64) >>= fun _ ↦ afterRate s A := by
  simp only [afterHigh, afterRate, announcedTail, bind_assoc]
  rfl

theorem limb0_eAt (u : MachineState) (a : Word) : ((eAt u a).limb 0).toBitVec = u.getMem a := rfl

theorem eListAt_getD {u : MachineState} {P : Word} {n i : Nat} (hi : i < n) :
    (eListAt u P n).getD i 0 = eAt u (P + BitVec.ofNat 64 (24 * i)) := by
  rw [List.getD_eq_getElem _ _ (by rw [eListAt_length]; exact hi), eListAt_getElem]

theorem lmOf_eList {u : MachineState} {P : Word} {n : Nat} (h : 0 < n) :
    lmOf (eListAt u P n) = u.getMem P := by
  rw [lmOf, eListAt_getD h, limb0_eAt]
  simp

theorem rateOf_eList {u : MachineState} {P : Word} {n : Nat} (h : 8 ≤ n) :
    rateOf (eListAt u P n) = u.getMem (P + 168) := by
  rw [rateOf, eListAt_getD (by unfold LayoutMirror.nTablesRust; omega), limb0_eAt]
  rfl

theorem rowsOf_eList {u : MachineState} {P : Word} {n : Nat} (h : 7 ≤ n) :
    rowsOf (eListAt u P n) = [u.getMem (P + 24), u.getMem (P + 48), u.getMem (P + 72),
      u.getMem (P + 96), u.getMem (P + 120), u.getMem (P + 144)] := by
  apply List.ext_getElem
  · simp only [rowsOf, List.length_map, List.length_take, List.length_drop, eListAt_length,
      LayoutMirror.nTablesRust, List.length_cons, List.length_nil]
    omega
  · intro i h1 h2
    simp only [List.length_cons, List.length_nil] at h2
    simp only [rowsOf, List.getElem_map, List.getElem_take, List.getElem_drop, eListAt_getElem,
      limb0_eAt]
    interval_cases i <;> rfl

theorem rate_iff (r : Word) : (r - 1).toNat < (4 : Word).toNat ↔ 1#64 ≤ r ∧ r ≤ 4#64 := by
  have h1 : (1 : Word).toNat = 1 := rfl
  have h1' : (1#64).toNat = 1 := rfl
  have h4 : (4 : Word).toNat = 4 := rfl
  have h4' : (4#64).toNat = 4 := rfl
  have := r.isLt
  rw [BitVec.toNat_sub, h1, h4, BitVec.le_def, BitVec.le_def, h1', h4']
  omega

/-! ## Allocations keep the transcript -/

/-- What an allocation writes: `NEXT` and the heap it allocates. -/
def HeapW (u v : MachineState) (a : Word) : Prop := Within a nextAddr 8 ∨ Fresh u v a

theorem HeapW.loc {s u v : MachineState} {a : Word} (h : HeapW u v a) : Loc s u v a :=
  h.elim (fun h ↦ Or.inr (Or.inl h)) fun h ↦ Or.inr (Or.inr h)

theorem TranscriptAt.heap {s u v : MachineState} (hpre : WalkPre s) (h : Inv s u)
    (hptr : u.getMem (tp s) = s.getReg .x13) (hv : HeapOk v) (fr : DFrame u v (HeapW u v))
    {T : TState} (hT : TranscriptAt u (tp s) T) : TranscriptAt v (tp s) T := by
  obtain ⟨hb1, hb2, -, -⟩ := bounds hpre
  have hx := hpre.stack.next
  have ha := hpre.stack.above
  rw [stackLo_eq, stack_eq] at hx
  rw [stackLo_eq] at ha
  have hh := hv.hi
  have stk : ∀ lo : Word, ∀ n : Nat, (s.getReg .x2 - 11392).toNat ≤ lo.toNat →
      lo.toNat + n ≤ (s.getReg .x2).toNat → Misses (HeapW u v) lo n := by
    intro lo n h1 h2 y hy hw
    simp only [HeapW, Fresh, heapNext, heapEnd] at hw hh ha
    rcases hw with hw | ⟨-, hw⟩
    · addr_omega [hx, hy, hw, h1, h2, hb1]
    · addr_omega [ha, hy, hw, h1, hh, hb1]
  have mono (a : Word) (n : Nat) (hm : Misses (Loc s u v) a n) : Misses (HeapW u v) a n :=
    fun y hy hw ↦ hm y hy hw.loc
  obtain ⟨e0, e1, e2⟩ := proofVals hpre h hptr
  have hP := hpre.proof
  refine fr.transcriptAt hT (tok hpre h hptr) (stk _ _ (by rw [tp]; addr_omega [hb1])
    (by rw [tp]; addr_omega [hb1])) ?_ ?_ (stk _ _ (by rw [tp]; addr_omega [hb1])
    (by rw [tp]; addr_omega [hb1]))
  · rw [e0]; exact mono _ _ (h.missLoc hv hpre.proofRO (by addr_omega [hP]))
  · rw [e1, e2]
    refine mono _ _ (h.missLoc hv hpre.streamRO ?_)
    rcases hpre.stream with h0 | h0
    · rw [h0]; have := (vecPtr s (s.getReg .x13)).isLt; omega
    · addr_omega [h0]

/-! ## The stage -/

/-- At `0x80001238`: `table_rows` filled at `s2`, the row counts also in registers,
`log_memory` in `s9`, the rate in `s0`, checked, and the code runs `afterRate`. -/
structure Rows (OI : MachineState → Word → List (List Opening) → Prop) (s u : MachineState)
    (A : List E) : Prop where
  inv : Inv s u
  regs : Regs s u
  proofPtr : u.getMem (tp s) = s.getReg .x13
  checked : byteAt u (tp s + 360) = 1
  x26 : u.getReg .x26 = s.getReg .x2 - 512
  x8 : u.getReg .x8 = rateOf A
  x25 : u.getReg .x25 = lmOf A
  rowRegs : [u.getReg .x16, u.getReg .x17, u.getReg .x13, u.getReg .x14, u.getReg .x11,
    u.getReg .x12] = rowsOf A
  buf : (u.getReg .x18).toNat % 8 = 0 ∧ 0x20000000 ≤ (u.getReg .x18).toNat ∧
    (u.getReg .x18).toNat + 48 ≤ heapNext u
  rows : [u.getMem (u.getReg .x18), u.getMem (u.getReg .x18 + 8), u.getMem (u.getReg .x18 + 16),
    u.getMem (u.getReg .x18 + 24), u.getMem (u.getReg .x18 + 32), u.getMem (u.getReg .x18 + 40)] =
    rowsOf A
  rate : 1#64 ≤ rateOf A ∧ rateOf A ≤ 4#64
  tracks : Tracks OI s u (afterRate s A)

/-- A doubleword of the frame misses what an allocation writes. -/
theorem HeapW.frame {s u v : MachineState} (hpre : WalkPre s) (hv : HeapOk v)
    (fr : DFrame u v (HeapW u v)) {x : Word}
    (hy : (s.getReg .x2 - 2656).toNat ≤ x.toNat ∧ x.toNat + 8 ≤ (s.getReg .x2).toNat) :
    v.getMem x = u.getMem x := by
  obtain ⟨hb1, hb2, -, -⟩ := bounds hpre
  have hx := hpre.stack.next
  have ha := hpre.stack.above
  rw [stackLo_eq, stack_eq] at hx
  rw [stackLo_eq] at ha
  have hh := hv.hi
  refine fr x fun i hi hw ↦ ?_
  simp only [HeapW, Fresh, heapNext, heapEnd] at hw hh ha
  rcases hw with hw | ⟨-, hw⟩
  · addr_omega [hx, hy, hw, hi, hb1]
  · addr_omega [ha, hy, hw, hi, hh, hb1]

/-- At `0x800011cc`: past the bounds traps, at least seven scalars. -/
theorem lenChecks {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {P : Word} {n : Nat} (hpc : u.pc = 0x800011b8) (h : High OI s u A P n) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = 0x800011cc ∧ 7 ≤ n ∧ (∀ a, t.getMem a = u.getMem a) ∧
      ∀ r ∈ keepRegs, t.getReg r = u.getReg r) ∨ Dead Image.code t) := by
  have hn : n < 2 ^ 64 := by rcases h.buf.2 with h0 | h0 <;> omega
  have x9 : (u.getReg .x9).toNat = n := by rw [h.x9, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b800011b8_spec hpc (by rv_eval [])
  by_cases hz : u.getReg .x9 = 0
  · obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b800011bc_spec (b800011b8_pc_not_taken h₁ hz)
      (by rv_eval [])
    exact ⟨u₂, hr₁.trans hr₂, Or.inr (trapAt (b800011bc_pc h₂))⟩
  obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b800011c0_spec (b800011b8_pc_taken h₁ hz)
    (by rv_eval [])
  have x9' : u₁.getReg .x9 = u.getReg .x9 := b800011b8_keeps h₁ .x9 (by decide)
  have h6w : (6 : Word).toNat = 6 := rfl
  by_cases h6 : (6 : Word).toNat < (u₁.getReg .x9).toNat
  · refine ⟨u₂, hr₁.trans hr₂, Or.inl ⟨b800011c0_pc_taken h₂ h6, by rw [x9', x9, h6w] at h6; omega,
      fun a ↦ (b800011c0_mem_same h₂ a).trans (b800011b8_mem_same h₁ a), fun r hr ↦ ?_⟩⟩
    rw [b800011c0_keeps h₂ r (mem_of_mem hr _), b800011b8_keeps h₁ r (mem_of_mem hr _)]
  · obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b800011c8_spec
      (b800011c0_pc_not_taken h₂ (Nat.le_of_not_lt h6)) (by rv_eval [])
    exact ⟨u₃, hr₁.trans (hr₂.trans hr₃), Or.inr (trapAt (b800011c8_pc h₃))⟩

/-- At `0x80001228`: `table_rows` at `Q` filled, the rate still in memory at `P + 168`. -/
structure Filled (OI : MachineState → Word → List (List Opening) → Prop) (s u : MachineState)
    (A : List E) (P Q : Word) : Prop where
  inv : Inv s u
  regs : Regs s u
  proofPtr : u.getMem (tp s) = s.getReg .x13
  checked : byteAt u (tp s + 360) = 1
  x26 : u.getReg .x26 = s.getReg .x2 - 512
  x8 : u.getReg .x8 = P
  x18 : u.getReg .x18 = Q
  x25 : u.getReg .x25 = lmOf A
  rowRegs : [u.getReg .x16, u.getReg .x17, u.getReg .x13, u.getReg .x14, u.getReg .x11,
    u.getReg .x12] = rowsOf A
  buf : Q.toNat % 8 = 0 ∧ 0x20000000 ≤ Q.toNat ∧ Q.toNat + 48 ≤ heapNext u
  rows : [u.getMem Q, u.getMem (Q + 8), u.getMem (Q + 16), u.getMem (Q + 24), u.getMem (Q + 32),
    u.getMem (Q + 40)] = rowsOf A
  rateMem : u.getMem (P + 168) = rateOf A
  rateOk : Mapped P 176 ∧ P.toNat % 8 = 0
  tracks : Tracks OI s u (afterHigh s A)

set_option maxRecDepth 8192 in
/-- `table_rows = alloc(8, 48)`, filled with `announced[1..7].c0`. -/
theorem fillRows (hAS : AllocSpec) {OI : MachineState → Word → List (List Opening) → Prop}
    {s u v : MachineState} {A : List E} {P : Word} {n : Nat} (hpre : WalkPre s)
    (h : High OI s u A P n) (hpc : v.pc = 0x800011cc) (h7 : 7 ≤ n)
    (hm : ∀ a, v.getMem a = u.getMem a) (hr : ∀ r ∈ keepRegs, v.getReg r = u.getReg r) :
    ∃ t, Reaches Image.code v t ∧ ((t.pc = 0x80001228 ∧ ∃ Q, Filled OI s t A P Q) ∨
      Dead Image.code t) := by
  obtain ⟨hb1, -, hb3, -⟩ := bounds hpre
  have Iv : Inv s v := h.inv.same hm (hr .x2 (by decide))
  have hn : heapNext v = heapNext u := by simp only [heapNext, hm]
  have hhv := Iv.heap
  obtain ⟨hP8, hPb⟩ := h.buf
  have hbe := h.below
  have hP : 0x20000000 ≤ P.toNat ∧ P.toNat + 24 * n ≤ heapNext v := by
    rw [hn]; omega
  have hhi := hhv.hi
  simp only [heapEnd] at hhi
  have hPm : P.toNat + 24 * n ≤ 0x78000000 := by omega
  have hmP : Mapped P (24 * n) := Or.inl ⟨by omega, by omega⟩
  have x8v : v.getReg .x8 = P := by rw [hr .x8 (by decide), h.x8]
  have x9v : (v.getReg .x9).toNat = n := by
    rw [hr .x9 (by decide), h.x9, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  obtain ⟨v₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b800011cc_spec hpc (by
    rv_eval [x8v]
    exact Mapped.valid8 hmP (by omega) (by omega) hP8)
  have m₃ := b800011cc_mem_same h₃
  have k₃ := b800011cc_keeps h₃
  have hn₃ : heapNext v₃ = heapNext v := by simp only [heapNext, m₃]
  have pre₃ : AllocPre v₃ := ⟨⟨by rw [hn₃]; exact hhv.lo, by rw [hn₃]; exact hhv.hi⟩, by rw [b800011cc_x10 h₃]; decide⟩
  obtain ⟨v₄, hr₄, ⟨hpc₄, hp₄, post₄⟩ | hd⟩ := hAS.call (Reaches.refl v₃) (b800011cc_pc h₃) pre₃
  swap
  · exact ⟨v₄, hr₃.trans hr₄, Or.inr hd⟩
  have hal := post₄.aligned
  have hab := post₄.above
  have hnx := post₄.next
  have hh₄ := post₄.heap.hi
  rw [b800011cc_x10 h₃] at hal
  rw [b800011cc_x11 h₃] at hnx
  simp only [heapEnd] at hh₄
  have e8 : (8 : Word).toNat = 8 := rfl
  have e48 : (48 : Word).toNat = 48 := rfl
  rw [e8] at hal
  rw [e48] at hnx
  rw [hn₃] at hab
  set Q := v₄.getReg .x10 with hQ
  have hQb : 0x20000000 ≤ Q.toNat ∧ Q.toNat + 48 ≤ 0x78000000 := by
    have := hhv.lo; simp only [heapStart] at this; omega
  have hmQ : Mapped Q 48 := Or.inl ⟨by omega, by omega⟩
  obtain ⟨v₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b800011e0_spec (by
    rw [hpc₄, returnAddress_eq, b800011cc_x1 h₃]; decide) (by rv_eval [])
  have m₅ := b800011e0_mem_same h₅
  have k₅ := b800011e0_keeps h₅
  have pc₅ := b800011e0_pc_taken h₅ (by
    intro he; have := congrArg BitVec.toNat he; rw [← hQ] at this
    have h0 : (0 : Word).toNat = 0 := rfl
    omega)
  have x8₅ : v₅.getReg .x8 = P := by
    rw [k₅ .x8 (by decide), hp₄.reg .x8, k₃ .x8 (by decide), x8v]
  have x10₅ : v₅.getReg .x10 = Q := k₅ .x10 (by decide)
  have x9₅ : v₅.getReg .x9 = v.getReg .x9 := by
    rw [k₅ .x9 (by decide), hp₄.reg .x9, k₃ .x9 (by decide)]
  have hnA : nextAddr.toNat = 2684358448 := rfl
  have mem₅ : ∀ x, x ≠ nextAddr → v₅.getMem x = u.getMem x := fun x hx ↦ by
    rw [m₅, post₄.mem x hx, m₃, hm]
  have hPx : ∀ k : Word, k.toNat ≤ 168 → (P + k).toNat = P.toNat + k.toNat := fun k hk ↦ by
    rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  obtain ⟨v₆, hr₆, h₆⟩ := Sym.BlockSpec.reaches b800011e8_spec pc₅ (by
    rv_eval [x8₅, x10₅]
    and_intros
    all_goals first
      | exact Mapped.valid8 hmQ (by addr_omega [hQb]) (by addr_omega [hQb]) (by addr_omega [hal, hQb])
      | exact Mapped.valid8 hmP (by addr_omega [hP, hPm]) (by addr_omega [hP, hPm, h7])
          (by addr_omega [hP8, hP, hPm])
      | addr_omega [hP, hab, hal, h7, hQb])
  by_cases h7' : v₅.getReg .x9 = (7 : Word)
  · obtain ⟨v₇, hr₇, h₇⟩ := Sym.BlockSpec.reaches b80001224_spec (b800011e8_pc_not_taken h₆ h7')
      (by rv_eval [])
    exact ⟨v₇, hr₃.trans (hr₄.trans (hr₅.trans (hr₆.trans hr₇))), Or.inr (trapAt (b80001224_pc h₇))⟩
  have pc₆ := b800011e8_pc_taken h₆ h7'
  have h8 : 8 ≤ n := by
    rw [x9₅] at h7'
    have h7w : (7 : Word).toNat = 7 := rfl
    have : n ≠ 7 := fun he ↦ h7' (BitVec.eq_of_toNat_eq (by rw [x9v, he, h7w]))
    omega
  have m₆ : MemFrame v₅ v₆ Q 48 := by rw [← x10₅]; exact b800011e8_frame h₆ (by rw [x10₅]; omega)
  have k₆ := b800011e8_keeps h₆
  have hnext : v₆.getMem nextAddr = v₄.getMem nextAddr := by
    rw [m₆ _ (by simp only [Within]; rw [hnA]; omega), m₅]
  have hn₆ : heapNext v₆ = Q.toNat + 48 := by simp only [heapNext, hnext]; exact hnx
  have heap₆ : HeapOk v₆ := ⟨by simp only [heapStart]; omega, by simp only [heapEnd]; omega⟩
  have fr : DFrame v v₆ (HeapW v v₆) := fun a ha ↦ by
    have h0 := ha 0 (by decide)
    rw [add_ofNat_zero] at h0
    simp only [HeapW, Fresh, not_or, not_and, not_lt] at h0
    obtain ⟨hn0, hf⟩ := h0
    have hQa : ¬ Within a Q 48 := by
      simp only [Within]; intro hw; have := hf (by omega); omega
    have hna : a ≠ nextAddr := fun he ↦ hn0 (by rw [he]; simp only [Within]; omega)
    rw [m₆ a hQa, m₅, post₄.mem a hna, m₃]
  have sp₆ : v₆.getReg .x2 = v.getReg .x2 := by
    rw [k₆ .x2 (by decide), k₅ .x2 (by decide), hp₄.reg .x2, k₃ .x2 (by decide)]
  have I₆ : Inv s v₆ := Iv.loc hpre (fr.mono fun _ h ↦ h.loc) heap₆ (by omega) sp₆
  have keep (x : Word) (hy : (s.getReg .x2 - 2656).toNat ≤ x.toNat ∧
      x.toNat + 8 ≤ (s.getReg .x2).toNat) : v₆.getMem x = u.getMem x := by
    rw [HeapW.frame hpre heap₆ fr hy, hm]
  have ptr₆ : v₆.getMem (tp s) = s.getReg .x13 := by
    rw [keep _ (by rw [tp]; constructor <;> addr_omega [hb1])]; exact h.proofPtr
  have hA := h.elems
  have hrows := rowsOf_eList (u := u) (P := P) h7
  rw [hA] at hrows
  have rd : ∀ k : Word, k.toNat ≤ 144 → v₅.getMem (P + k) = u.getMem (P + k) := fun k hk ↦
    mem₅ _ fun he ↦ by
      have := congrArg BitVec.toNat he
      rw [hPx k (by omega), hnA] at this
      omega
  refine ⟨v₆, hr₃.trans (hr₄.trans (hr₅.trans hr₆)), Or.inl ⟨pc₆, Q, {
    inv := I₆
    regs := h.regs.keep fun r hr' ↦ by
      rw [k₆ r (mem_of_mem hr' _), k₅ r (mem_of_mem hr' _), hp₄.reg r (mem_six hr'),
        k₃ r (mem_of_mem hr' _), hr r (mem_of_mem hr' _)]
    proofPtr := ptr₆
    checked := by
      have ha : (tp s + 360).toNat % 8 = 0 := by rw [tp]; addr_omega [hb1, hb3]
      rw [byteAt_congr ha (keep _ (by rw [tp]; constructor <;> addr_omega [hb1]))]
      exact h.checked
    x26 := by
      rw [k₆ .x26 (by decide), k₅ .x26 (by decide), hp₄.reg .x26, k₃ .x26 (by decide),
        hr .x26 (by decide), h.x26]
    x8 := by rw [k₆ .x8 (by decide), x8₅]
    x18 := by rw [b800011e8_x18 h₆, x10₅]
    x25 := by
      rw [k₆ .x25 (by decide), k₅ .x25 (by decide), hp₄.reg .x25, b800011cc_x25 h₃, x8v, hm, ← hA,
        lmOf_eList (by omega)]
    rowRegs := by
      rw [hrows, b800011e8_x16 h₆, b800011e8_x17 h₆, b800011e8_x13 h₆, b800011e8_x14 h₆,
        b800011e8_x11 h₆, b800011e8_x12 h₆, x8₅, rd 24 (by decide), rd 48 (by decide),
        rd 72 (by decide), rd 96 (by decide), rd 120 (by decide), rd 144 (by decide)]
    buf := ⟨hal, by omega, by omega⟩
    rows := by
      have q0 : v₆.getMem Q = v₅.getMem (v₅.getReg .x8 + 24) := by
        rw [← b800011e8_m_x10_0 h₆, x10₅]
      have q8 : v₆.getMem (Q + 8) = v₅.getMem (v₅.getReg .x8 + 48) := by
        rw [← b800011e8_m_x10_8 h₆, x10₅]
      have q16 : v₆.getMem (Q + 16) = v₅.getMem (v₅.getReg .x8 + 72) := by
        rw [← b800011e8_m_x10_16 h₆, x10₅]
      have q24 : v₆.getMem (Q + 24) = v₅.getMem (v₅.getReg .x8 + 96) := by
        rw [← b800011e8_m_x10_24 h₆, x10₅]
      have q32 : v₆.getMem (Q + 32) = v₅.getMem (v₅.getReg .x8 + 120) := by
        rw [← b800011e8_m_x10_32 h₆, x10₅]
      have q40 : v₆.getMem (Q + 40) = v₅.getMem (v₅.getReg .x8 + 144) := by
        rw [← b800011e8_m_x10_40 h₆, x10₅]
      rw [hrows, q0, q8, q16, q24, q32, q40, x8₅, rd 24 (by decide), rd 48 (by decide),
        rd 72 (by decide), rd 96 (by decide), rd 120 (by decide), rd 144 (by decide)]
    rateMem := by
      have hQ168 : ¬ Within (P + 168) Q 48 := by
        simp only [Within]; rw [hPx 168 (by decide)]; have : (168 : Word).toNat = 168 := rfl; omega
      rw [m₆ _ hQ168, mem₅ _ (fun he ↦ by
        have := congrArg BitVec.toNat he
        rw [hPx 168 (by decide), hnA] at this
        have : (168 : Word).toNat = 168 := rfl
        omega), ← hA, rateOf_eList (by omega)]
    rateOk := ⟨Or.inl ⟨by omega, by omega⟩, hP8⟩
    tracks := (h.tracks.keep fun T hT ↦ TranscriptAt.same hpre h.inv h.proofPtr hm hT).keep
      fun T hT ↦ TranscriptAt.heap hpre Iv (by rw [hm]; exact h.proofPtr) heap₆ fr hT }⟩⟩

/-- The rate check: `log_inverse_rate - 1 <ᵤ 4`, else `Err` 25. -/
theorem rateCheck {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {P Q : Word} (hpre : WalkPre s) (hpc : u.pc = 0x80001228)
    (h : Filled OI s u A P Q) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = 0x80001238 ∧ Rows OI s t A) ∨ Done OI s t) := by
  obtain ⟨hmP, hP8⟩ := h.rateOk
  obtain ⟨t, hr, h₁⟩ := Sym.BlockSpec.reaches b80001228_spec hpc (by
    rv_eval [h.x8]
    exact Mapped.valid8 hmP (by addr_omega [hmP]) (by addr_omega [hmP]) (by addr_omega [hP8, hmP]))
  have m₁ := b80001228_mem_same h₁
  have k₁ := b80001228_keeps h₁
  have It : Inv s t := h.inv.same m₁ (k₁ .x2 (by decide))
  have rate : u.getMem (u.getReg .x8 + 168) = rateOf A := by rw [h.x8, h.rateMem]
  by_cases hc : (4 : Word).toNat ≤ (u.getMem (u.getReg .x8 + 168) - 1).toNat
  · obtain ⟨t', hr', hd⟩ := err12b8 (OI := OI) hpre It
      (by rw [k₁ .x23 (by decide), h.regs.x23]) (b80001228_pc_taken h₁ hc)
    exact ⟨t', hr.trans hr', Or.inr hd⟩
  have hc' := Nat.lt_of_not_le hc
  rw [rate] at hc'
  have hrate := (rate_iff _).mp hc'
  have rg (r : Reg) (hr : r ∈ [Reg.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x9, .x11, .x12, .x13, .x14,
      .x16, .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30,
      .x31] := by decide) : t.getReg r = u.getReg r := k₁ r (mem_of_mem hr _)
  refine ⟨t, hr, Or.inl ⟨b80001228_pc_not_taken h₁ (Nat.lt_of_not_le hc), {
    inv := It
    regs := h.regs.keep fun r hr' ↦ k₁ r (mem_of_mem hr' _)
    proofPtr := by rw [m₁]; exact h.proofPtr
    checked := by
      obtain ⟨hb1, -, hb3, -⟩ := bounds hpre
      have ha : (tp s + 360).toNat % 8 = 0 := by rw [tp]; addr_omega [hb1, hb3]
      rw [byteAt_congr ha (m₁ _)]
      exact h.checked
    x26 := by rw [rg .x26, h.x26]
    x8 := by rw [b80001228_x8 h₁, rate]
    x25 := by rw [rg .x25, h.x25]
    rowRegs := by rw [rg .x16, rg .x17, rg .x13, rg .x14, rg .x11, rg .x12, h.rowRegs]
    buf := by rw [rg .x18, h.x18]; simp only [heapNext, m₁]; exact h.buf
    rows := by simp only [m₁, rg .x18, h.x18]; exact h.rows
    rate := hrate
    tracks := by
      have tr := h.tracks.keep fun T hT ↦ TranscriptAt.same hpre h.inv h.proofPtr m₁ hT
      rw [afterHigh_eq] at tr
      exact tr.require hrate }⟩⟩

/-- **From `0x800011b8` to the layout's head** (`0x80001238`), or `Err`, or a dead end. -/
theorem rowsStage (hAS : AllocSpec) {OI : MachineState → Word → List (List Opening) → Prop}
    {s u : MachineState} {A : List E} {P : Word} {n : Nat} (hpre : WalkPre s)
    (hpc : u.pc = 0x800011b8) (h : High OI s u A P n) :
    ∃ t, Reaches Image.code u t ∧
      ((t.pc = 0x80001238 ∧ Rows OI s t A) ∨ Done OI s t ∨ Dead Image.code t) := by
  obtain ⟨v, hr₁, ⟨pc₁, h7, hm, hrg⟩ | hd⟩ := lenChecks hpc h
  · obtain ⟨w, hr₂, ⟨pc₂, Q, hf⟩ | hd⟩ := fillRows hAS hpre h pc₁ h7 hm hrg
    · obtain ⟨t, hr₃, ht⟩ := rateCheck hpre pc₂ hf
      exact ⟨t, hr₁.trans (hr₂.trans hr₃), ht.imp id Or.inl⟩
    · exact ⟨w, hr₁.trans hr₂, Or.inr (Or.inr hd)⟩
  · exact ⟨v, hr₁, Or.inr (Or.inr hd)⟩

end Rv64Verifier.Proofs.Walk
