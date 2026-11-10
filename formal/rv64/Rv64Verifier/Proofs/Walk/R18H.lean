import Rv64Verifier.Proofs.Walk.R18G

/-!
# `walk` R18, the table claims: the outer loop's blocks

`TabR18`: table `k`'s values' count, pointer and column base loaded (`0x80003858`). `outerHead`:
from the outer head to the exit (`ExitR18`, at `0x80003a48`, every table done) or to
`0x80003910` (no room: `grow_amortized`) or `0x80003878`. `tab3878`: an empty table goes to
`0x8000383c`, else `0x8000387c`. `tab387c`: to the inner head. `endStep`: from `0x8000383c` to
the next table's head or the exit.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Verifier Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript
  Rv64Verifier.Blocks.F4 Rv64Verifier.Bus
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- At `0x80003a48`, every table's claims appended, `L` claims in all. -/
structure ExitR18 (OI : MachineState → Word → List (List Opening) → Prop)
    (s u₀ w t u : MachineState) (layout : LayoutMirror.LayoutRust) (rows : List (BitVec 64))
    (lir : BitVec 64) (bus : BusResultRust) (evs : List (List E × List E)) (P C L : Word) : Prop
    extends CoreR18 OI s u₀ w t u layout rows lir bus evs P C L.toNat
      (bus.claims ++ tableClaimsRust evs) where
  pc : u.pc = 0x80003a48
  x24 : u.getReg .x24 = s.getReg .x2 - 512
  x25 : u.getReg .x25 = L
  lenSlot : u.getMem (s.getReg .x2 - 1616) = L

/-- Table `k`'s values loaded: their count in `s4`, their pointer in `s8`, the column base in
`s10`. -/
structure TabR18 (OI : MachineState → Word → List (List Opening) → Prop)
    (s u₀ w t u : MachineState) (layout : LayoutMirror.LayoutRust) (rows : List (BitVec 64))
    (lir : BitVec 64) (bus : BusResultRust) (evs : List (List E × List E)) (k : Nat)
    (P C L : Word) : Prop extends CoreR18 OI s u₀ w t u layout rows lir bus evs P C L.toNat
      (bus.claims ++ tableClaimsRust (evs.take k)) where
  hk : k < 6 ∧ k < evs.length
  x8 : u.getReg .x8 = 6
  x9 : u.getReg .x9 = 0xffffffffffffffff
  x18 : u.getReg .x18 = BitVec.ofNat 64 k
  x19 : u.getReg .x19 = s.getReg .x2 - 896
  x21 : u.getReg .x21 = s.getReg .x2 - 1312
  x22 : u.getReg .x22 = vecPtr t (s.getReg .x2 - 928) + 48 * vecLen t (s.getReg .x2 - 928)
  x23 : u.getReg .x23 = vecPtr t (s.getReg .x2 - 928) + BitVec.ofNat 64 (48 * k)
  x20 : u.getReg .x20 = BitVec.ofNat 64 (evs.getD k ([], [])).2.length
  x24 : u.getReg .x24 = vecPtr t (vecPtr t (s.getReg .x2 - 928) + BitVec.ofNat 64 (48 * k + 24))
  x25 : u.getReg .x25 = L
  x26 : u.getReg .x26 = BitVec.ofNat 64 (LayoutMirror.globalColumnBasesRust.getD k 0)
  lenSlot : u.getMem (s.getReg .x2 - 1616) = L

section Outer
variable {OI : MachineState → Word → List (List Opening) → Prop} {s u₀ w t u : MachineState}
  {layout : LayoutMirror.LayoutRust} {rows : List (BitVec 64)} {lir : BitVec 64}
  {bus : BusResultRust} {evs : List (List E × List E)} {k : Nat} {P C L : Word}

theorem CoreR18.n_lt {M : Nat} {cl : List ColumnClaim}
    (H : CoreR18 OI s u₀ w t u layout rows lir bus evs P C M cl) : C.toNat < 2 ^ 32 := by
  have b := H.buf.2.1
  have hh := H.rest.inv.heap.hi
  simp only [heapEnd] at hh
  omega

/-- Through a block that writes no memory and keeps the registers `TabR18` names. -/
theorem TabR18.same (hpre : WalkPre s) (T : TabR18 OI s u₀ w t u layout rows lir bus evs k P C L)
    {v : MachineState} (hm : ∀ a, v.getMem a = u.getMem a)
    (hr : ∀ r ∈ ([.x2, .x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26] : List Reg),
      v.getReg r = u.getReg r) : TabR18 OI s u₀ w t v layout rows lir bus evs k P C L where
  toCoreR18 := T.toCoreR18.stepW hpre (StepW.same T.rest.inv.heap hm (hr .x2 (by decide))
    (fun _ ↦ False) False) (fun _ h ↦ h.elim) (fun _ h ↦ h.elim)
  hk := T.hk
  x8 := by rw [hr .x8 (by decide), T.x8]
  x9 := by rw [hr .x9 (by decide), T.x9]
  x18 := by rw [hr .x18 (by decide), T.x18]
  x19 := by rw [hr .x19 (by decide), T.x19]
  x21 := by rw [hr .x21 (by decide), T.x21]
  x22 := by rw [hr .x22 (by decide), T.x22]
  x23 := by rw [hr .x23 (by decide), T.x23]
  x20 := by rw [hr .x20 (by decide), T.x20]
  x24 := by rw [hr .x24 (by decide), T.x24]
  x25 := by rw [hr .x25 (by decide), T.x25]
  x26 := by rw [hr .x26 (by decide), T.x26]
  lenSlot := by rw [hm, T.lenSlot]

set_option maxHeartbeats 800000 in
/-- The outer head: every table done, or table `k`'s values loaded. -/
theorem outerHead (hpre : WalkPre s) (H : LoopR18 OI s u₀ w t u layout rows lir bus evs k P C L)
    (hk6 : k < 6) :
    ∃ v, Reaches Image.code u v ∧ (ExitR18 OI s u₀ w t v layout rows lir bus evs P C L ∨
      (TabR18 OI s u₀ w t v layout rows lir bus evs k P C L ∧ v.pc = 0x80003910 ∧
        C.toNat - L.toNat < (evs.getD k ([], [])).2.length) ∨
      (TabR18 OI s u₀ w t v layout rows lir bus evs k P C L ∧ v.pc = 0x80003878 ∧
        (evs.getD k ([], [])).2.length ≤ C.toNat - L.toNat)) := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  have sp := H.rest.inv.sp
  have hh := H.rest.inv.heap.hi
  have htm := H.tmono
  have hwm := H.wmono
  have hsm := H.smono
  have hs0 := hpre.heap.lo
  simp only [heapEnd, heapStart] at hh hs0
  obtain ⟨Pa, Pl, Pf⟩ := rowsAt_facts H.rowsAt
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80003854_spec H.pc (by rv_eval [])
  have m₁ := b80003854_mem_same h₁
  have k₁ := b80003854_keeps h₁
  have C₁ := H.toCoreR18.stepW hpre (StepW.same H.rest.inv.heap m₁ (k₁ .x2 (by decide))
    (fun _ ↦ False) False) (fun _ h ↦ h.elim) (fun _ h ↦ h.elim)
  rcases Nat.lt_or_ge k evs.length with hkl | hkl
  swap
  · have hke : k = evs.length := le_antisymm H.hk.2 hkl
    have pc₁ := b80003854_pc_taken h₁ (by
      rw [H.x23, H.x22]
      have : vecLen t (s.getReg .x2 - 928) = BitVec.ofNat 64 k := by
        apply BitVec.eq_of_toNat_eq
        rw [Pl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hke.symm
      rw [this]; bv_omega)
    rw [tableClaims_take_done evs k (Or.inl hke)] at C₁
    have ls : u₁.getMem (s.getReg .x2 - 1616) = L := by rw [m₁]; exact H.lenSlot
    exact ⟨u₁, hr₁, Or.inl ⟨C₁, pc₁, by rw [k₁ .x24 (by decide), H.x24],
      by rw [k₁ .x25 (by decide), H.x25], ls⟩⟩
  rcases Pf with h0 | ⟨p1, p2⟩
  · omega
  have e48 : (48 * vecLen t (s.getReg .x2 - 928) : Word).toNat = 48 * evs.length := by
    rw [BitVec.toNat_mul, Pl, show (48 : Word).toNat = 48 from rfl, Nat.mod_eq_of_lt (by omega)]
  have pc₁ := b80003854_pc_not_taken h₁ (by
    rw [H.x23, H.x22]; intro he; have := congrArg BitVec.toNat he
    addr_omega [this, e48, p2, Pl, hkl, htm, hh])
  have pk := H.rowsAt.pairs k hkl
  obtain ⟨Va, Vl, Vb⟩ := newVecE_facts pk.2
  have hgd : evs.getD k ([], []) = evs[k] := List.getD_eq_getElem _ _ hkl
  have x2₁ : u₁.getReg .x2 = s.getReg .x2 - 2656 := by rw [k₁ .x2 (by decide), sp]
  have x18₁ : u₁.getReg .x18 = BitVec.ofNat 64 k := by rw [k₁ .x18 (by decide), H.x18]
  have x19₁ : u₁.getReg .x19 = s.getReg .x2 - 896 := by rw [k₁ .x19 (by decide), H.x19]
  have x23₁ : u₁.getReg .x23 = vecPtr t (s.getReg .x2 - 928) + BitVec.ofNat 64 (48 * k) := by
    rw [k₁ .x23 (by decide), H.x23]
  have x25₁ : u₁.getReg .x25 = L := by rw [k₁ .x25 (by decide), H.x25]
  obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80003858_spec pc₁ (by
    rv_eval [x2₁, x18₁, x19₁, x23₁]
    and_intros <;> first
      | valid_access hval [hb1, hb3, hk6]
      | (refine heapValid ?_ ?_ ?_ <;> addr_omega [p1, p2, Pa, hkl, htm, hh, hwm, hsm, hs0]))
  have m₂ := b80003858_mem_same h₂
  have k₂ := b80003858_keeps h₂
  have g (c : Nat) (hc : c ≤ 40) : u₁.getMem (vecPtr t (s.getReg .x2 - 928) +
      BitVec.ofNat 64 (48 * k) + BitVec.ofNat 64 c) = t.getMem (vecPtr t (s.getReg .x2 - 928) +
      BitVec.ofNat 64 (48 * k) + BitVec.ofNat 64 c) := by
    rw [m₁]; exact H.evKept _ (by addr_omega [p1, p2, hkl, hc, htm, hh])
      (by addr_omega [p1, p2, hkl, hc, htm, hh])
  have hn64 : (evs.getD k ([], [])).2.length < 2 ^ 64 := by
    have h := (vecLen t (vecPtr t (s.getReg .x2 - 928) + BitVec.ofNat 64 (48 * k + 24))).isLt
    rw [Vl, ← hgd] at h; exact h
  have e40 : u₁.getMem (u₁.getReg .x23 + 40) = BitVec.ofNat 64 (evs.getD k ([], [])).2.length := by
    rw [x23₁, show (40 : Word) = BitVec.ofNat 64 40 from rfl, g 40 (by omega),
      show vecPtr t (s.getReg .x2 - 928) + BitVec.ofNat 64 (48 * k) + BitVec.ofNat 64 40 =
        vecPtr t (s.getReg .x2 - 928) + BitVec.ofNat 64 (48 * k + 24) + 16 by bv_omega]
    apply BitVec.eq_of_toNat_eq
    show (vecLen t _).toNat = _
    rw [Vl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64, hgd]
  have eC : u₁.getMem (u₁.getReg .x2 + 1024) - u₁.getReg .x25 = C - L := by
    rw [x25₁, x2₁, show s.getReg .x2 - 2656 + 1024 = s.getReg .x2 - 1632 by bv_omega, m₁, H.capSlot]
  have hLC := H.len
  have T : TabR18 OI s u₀ w t u₂ layout rows lir bus evs k P C L := {
    toCoreR18 := C₁.stepW hpre (StepW.same C₁.rest.inv.heap m₂ (k₂ .x2 (by decide))
      (fun _ ↦ False) False) (fun _ h ↦ h.elim) (fun _ h ↦ h.elim)
    hk := ⟨hk6, hkl⟩
    x8 := by rw [k₂ .x8 (by decide), k₁ .x8 (by decide), H.x8]
    x9 := by rw [k₂ .x9 (by decide), k₁ .x9 (by decide), H.x9]
    x18 := by rw [k₂ .x18 (by decide), x18₁]
    x19 := by rw [k₂ .x19 (by decide), x19₁]
    x21 := by rw [k₂ .x21 (by decide), k₁ .x21 (by decide), H.x21]
    x22 := by rw [k₂ .x22 (by decide), k₁ .x22 (by decide), H.x22]
    x23 := by rw [k₂ .x23 (by decide), x23₁]
    x20 := by rw [b80003858_x20 h₂, e40]
    x24 := by
      rw [b80003858_x24 h₂, x23₁, show (32 : Word) = BitVec.ofNat 64 32 from rfl, g 32 (by omega),
        show vecPtr t (s.getReg .x2 - 928) + BitVec.ofNat 64 (48 * k) + BitVec.ofNat 64 32 =
          vecPtr t (s.getReg .x2 - 928) + BitVec.ofNat 64 (48 * k + 24) + 8 by bv_omega]
      rfl
    x25 := by rw [k₂ .x25 (by decide), x25₁]
    x26 := by
      rw [b80003858_x26 h₂, x19₁, x18₁, m₁,
        show s.getReg .x2 - 896 + BitVec.ofNat 64 k * 8 =
          s.getReg .x2 - 896 + BitVec.ofNat 64 (8 * k) by bv_omega]
      exact H.bases k hk6
    lenSlot := by rw [m₂, m₁]; exact H.lenSlot }
  by_cases hc : C.toNat - L.toNat < (evs.getD k ([], [])).2.length
  · refine ⟨u₂, hr₁.trans hr₂, Or.inr (Or.inl ⟨T, b80003858_pc_taken h₂ ?_, hc⟩)⟩
    rw [eC, e40]; addr_omega [hLC, hc, hn64]
  · refine ⟨u₂, hr₁.trans hr₂, Or.inr (Or.inr ⟨T, b80003858_pc_not_taken h₂ ?_, by omega⟩)⟩
    rw [eC, e40]; addr_omega [hLC, hc, hn64]

end Outer

end Rv64Verifier.Proofs.Walk
