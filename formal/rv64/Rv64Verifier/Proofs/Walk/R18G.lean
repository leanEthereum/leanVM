import Rv64Verifier.Proofs.Walk.R18F

/-!
# `walk` R18, the table claims: the inner loop

`innerStep`: one value's claim, from the inner loop's head to the next value's or, after table
`k`'s last value, to `0x8000383c` (`EndR18`). `innerLoop`: from the head to `EndR18`.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Verifier Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript
  Rv64Verifier.Blocks.F4 Rv64Verifier.Bus
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- At `0x8000383c`, table `k`'s claims appended, `L` claims in all. -/
structure EndR18 (OI : MachineState → Word → List (List Opening) → Prop)
    (s u₀ w t u : MachineState) (layout : LayoutMirror.LayoutRust) (rows : List (BitVec 64))
    (lir : BitVec 64) (bus : BusResultRust) (evs : List (List E × List E)) (k : Nat)
    (P C L : Word) : Prop extends CoreR18 OI s u₀ w t u layout rows lir bus evs P C L.toNat
      (bus.claims ++ tableClaimsRust (evs.take (k + 1))) where
  pc : u.pc = 0x8000383c
  hk : k < 6 ∧ k < evs.length
  x8 : u.getReg .x8 = 6
  x9 : u.getReg .x9 = 0xffffffffffffffff
  x18 : u.getReg .x18 = BitVec.ofNat 64 k
  x19 : u.getReg .x19 = s.getReg .x2 - 896
  x21 : u.getReg .x21 = s.getReg .x2 - 1312
  x22 : u.getReg .x22 = vecPtr t (s.getReg .x2 - 928) + 48 * vecLen t (s.getReg .x2 - 928)
  x23 : u.getReg .x23 = vecPtr t (s.getReg .x2 - 928) + BitVec.ofNat 64 (48 * k)
  x25 : u.getReg .x25 = L

section Inner
variable {OI : MachineState → Word → List (List Opening) → Prop} {s u₀ w t u : MachineState}
  {layout : LayoutMirror.LayoutRust} {rows : List (BitVec 64)} {lir : BitVec 64}
  {bus : BusResultRust} {evs : List (List E × List E)} {k j : Nat} {P C L : Word}

/-- One value's claim. -/
theorem innerStep (hCl : CloneSpecE) (hpre : WalkPre s)
    (H : InnerR18 OI s u₀ w t u layout rows lir bus evs k j P C L) :
    ∃ v, Reaches Image.code u v ∧
      ((j + 1 < (evs.getD k ([], [])).2.length ∧
        InnerR18 OI s u₀ w t v layout rows lir bus evs k (j + 1) P C L) ∨
      EndR18 OI s u₀ w t v layout rows lir bus evs k P C
        (L + BitVec.ofNat 64 (evs.getD k ([], [])).2.length) ∨ Dead Image.code v) := by
  obtain ⟨v, hr, ⟨hpc, hreg, Cv, hel, hfr, hal, hls⟩ | hd⟩ := innerClone hCl hpre H
  swap
  · exact ⟨v, hr, Or.inr (Or.inr hd)⟩
  obtain ⟨v₂, hr₂, C₂, hls₂, hregs, x20, x24, x26, x27, pT, pN⟩ :=
    innerStore hpre H hpc hreg Cv hel hfr hal hls
  have hj := H.hj
  have hroom := H.room
  have hn64 : (evs.getD k ([], [])).2.length < 2 ^ 63 := by
    have b := H.buf.2.1
    have hh := H.rest.inv.heap.hi
    simp only [heapEnd] at hh
    omega
  have R (r : Reg) (hr : r ∈ ([.x8, .x9, .x18, .x19, .x21, .x22, .x23, .x25] : List Reg)) :
      v₂.getReg r = u.getReg r := hregs r hr
  by_cases hlast : j + 1 < (evs.getD k ([], [])).2.length
  · refine ⟨v₂, hr.trans hr₂, Or.inl ⟨hlast, {
      toCoreR18 := C₂
      pc := pT (by rw [H.x20]; intro h0; have := congrArg BitVec.toNat h0; addr_omega [this, hn64, hlast])
      hk := H.hk
      hj := hlast
      room := hroom
      x8 := by rw [R .x8 (by decide), H.x8]
      x9 := by rw [R .x9 (by decide), H.x9]
      x18 := by rw [R .x18 (by decide), H.x18]
      x19 := by rw [R .x19 (by decide), H.x19]
      x21 := by rw [R .x21 (by decide), H.x21]
      x22 := by rw [R .x22 (by decide), H.x22]
      x23 := by rw [R .x23 (by decide), H.x23]
      x20 := by rw [x20, H.x20]; addr_omega [hn64, hlast]
      x24 := by rw [x24, H.x24]; bv_omega
      x25 := by rw [R .x25 (by decide), H.x25]
      x26 := by rw [x26, H.x26]; bv_omega
      x27 := by rw [x27, H.x27]; bv_omega
      lenSlot := hls₂ }⟩⟩
  · have hend : j + 1 = (evs.getD k ([], [])).2.length := by omega
    have pc₂ := pN (by rw [H.x20]; addr_omega [hn64, hend])
    obtain ⟨v₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000390c_spec pc₂ (by rv_eval [])
    have m₃ := b8000390c_mem_same h₃
    have k₃ := b8000390c_keeps h₃
    have C₃ := C₂.stepW hpre (StepW.same C₂.rest.inv.heap m₃ (k₃ .x2 (by decide)) (fun _ ↦ False)
      False) (fun _ h ↦ h.elim) (fun _ h ↦ h.elim)
    have hL : L.toNat + (j + 1) = (L + BitVec.ofNat 64 (evs.getD k ([], [])).2.length).toNat := by
      have := C.isLt; addr_omega [hend, hroom, this]
    have hl : bus.claims ++ tableClaimsRust (evs.take k) ++ (tableClaimsOf evs k).take (j + 1) =
        bus.claims ++ tableClaimsRust (evs.take (k + 1)) := by
      rw [hend, ← tableClaimsOf_length, List.take_length,
        tableClaims_succ evs k H.hk.1 H.hk.2, List.append_assoc]
    rw [hL, hl] at C₃
    have R₃ (r : Reg) (hr : r ∈ ([.x8, .x9, .x18, .x19, .x21, .x22, .x23, .x25] : List Reg)) :
        v₃.getReg r = u.getReg r := by
      have hr' := hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rw [← R r hr]
      rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact k₃ _ (by decide)
    exact ⟨v₃, hr.trans (hr₂.trans hr₃), Or.inr (Or.inl {
      toCoreR18 := C₃
      pc := b8000390c_pc h₃
      hk := H.hk
      x8 := by rw [R₃ .x8 (by decide), H.x8]
      x9 := by rw [R₃ .x9 (by decide), H.x9]
      x18 := by rw [R₃ .x18 (by decide), H.x18]
      x19 := by rw [R₃ .x19 (by decide), H.x19]
      x21 := by rw [R₃ .x21 (by decide), H.x21]
      x22 := by rw [R₃ .x22 (by decide), H.x22]
      x23 := by rw [R₃ .x23 (by decide), H.x23]
      x25 := by rw [R₃ .x25 (by decide), H.x25] })⟩

/-- The inner loop, from value `j` to `0x8000383c`. -/
theorem innerLoop (hCl : CloneSpecE) (hpre : WalkPre s) :
    ∀ m j u, (evs.getD k ([], [])).2.length - j = m →
      InnerR18 OI s u₀ w t u layout rows lir bus evs k j P C L →
      ∃ v, Reaches Image.code u v ∧
        (EndR18 OI s u₀ w t v layout rows lir bus evs k P C
          (L + BitVec.ofNat 64 (evs.getD k ([], [])).2.length) ∨ Dead Image.code v) := by
  intro m
  induction m with
  | zero => intro j u hm H; have := H.hj; omega
  | succ m ih =>
    intro j u hm H
    obtain ⟨v, hr, ⟨hl, H'⟩ | hE | hd⟩ := innerStep hCl hpre H
    · obtain ⟨v', hr', h'⟩ := ih (j + 1) v (by omega) H'
      exact ⟨v', hr.trans hr', h'⟩
    · exact ⟨v, hr, Or.inl hE⟩
    · exact ⟨v, hr, Or.inr hd⟩

end Inner

end Rv64Verifier.Proofs.Walk
