import Rv64Verifier.Proofs.Runtime.Contracts
import Rv64Verifier.Blocks.F40
import Rv64Verifier.Blocks.F41

/-!
# Drop glue

`drop_glue::<Vec<Vec<Form>>>` at `0x8000c0dc` is a `ret` (the allocator frees nothing).
`drop_glue::<Layout>` at `0x8000c0e0` (`Blocks/F41.lean`) calls it on two fields of each 80-byte
element of the `Layout`'s first `Vec` and on three more fields, the last a tail call: `0x8000c0e0`
saves `ra`, `s0`..`s2` in a 32-byte frame and branches on an empty `Vec`; `0x8000c100` sets `s1`
to the first element's field at `+64` and `s2` to the end; the loop is `0x8000c118` (call),
`0x8000c128` (call), `0x8000c138` (advance by 80); `0x8000c140` and `0x8000c150` call, and
`0x8000c160` restores and jumps to the callee with the caller's `ra`.
-/

namespace Rv64Verifier.Runtime.Drop
open RiscvZkvm.Rv64 Rv64Verifier.Blocks.F40 Rv64Verifier.Blocks.F41
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- **`drop_glue::<Vec<Vec<Form>>>` meets its contract.** -/
theorem drop_nop_spec : DropNopSpec := by
  intro s hpc _
  obtain ⟨t, hr, h⟩ := Sym.BlockSpec.reaches b8000c0dc_spec hpc trivial
  exact ⟨t, hr, Or.inl ⟨(b8000c0dc_pc h).trans (returnAddress_eq s).symm,
    fun r hr' ↦ b8000c0dc_keeps h r (mem_of_mem hr' _), b8000c0dc_mem_same h⟩⟩

/-- The callee-saved registers the function never touches. -/
def untouched : List Reg := [.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27]

/-- Inside the frame, memory as after the prologue (`t₁`). -/
structure Inv (s t₁ u : MachineState) : Prop where
  sp : u.getReg .x2 = s.getReg .x2 - 32
  self : u.getReg .x8 = s.getReg .x10
  kept : ∀ r ∈ untouched, u.getReg r = s.getReg r
  mem : ∀ a, u.getMem a = t₁.getMem a

/-- At the loop head, before element `k`. -/
structure LoopInv (s t₁ u : MachineState) (k : Nat) : Prop extends Inv s t₁ u where
  pc : u.pc = 0x8000c118
  lt : k < (vecLen s (s.getReg .x10)).toNat
  x9 : u.getReg .x9 = vecPtr s (s.getReg .x10) + BitVec.ofNat 64 (80 * k) + 64
  x18 : u.getReg .x18 =
    vecPtr s (s.getReg .x10) + BitVec.ofNat 64 (80 * (vecLen s (s.getReg .x10)).toNat) + 64

theorem Inv.of_call {s t₁ u v : MachineState} (h : Inv s t₁ u) (hp : Preserves u v)
    (hm : ∀ a, v.getMem a = u.getMem a) : Inv s t₁ v where
  sp := (hp.reg .x2).trans h.sp
  self := (hp.reg .x8).trans h.self
  kept := fun r hr ↦ (hp r (mem_of_mem hr _)).trans (h.kept r hr)
  mem := fun a ↦ (hm a).trans (h.mem a)

theorem Inv.of_block {s t₁ u v : MachineState} (h : Inv s t₁ u) (hm : ∀ a, v.getMem a = u.getMem a)
    {l : List Reg} (hk : ∀ r ∈ l, v.getReg r = u.getReg r)
    (hl : ∀ r ∈ [Reg.x2, .x8] ++ untouched, r ∈ l := by decide) : Inv s t₁ v where
  sp := (hk _ (hl _ (by decide))).trans h.sp
  self := (hk _ (hl _ (by decide))).trans h.self
  kept := fun r hr ↦ (hk r (hl r (by simp [hr]))).trans (h.kept r hr)
  mem := fun a ↦ (hm a).trans (h.mem a)

theorem _root_.Rv64Verifier.Runtime.DropLayoutPre.bounds {s : MachineState} (h : DropLayoutPre s) :
    0x40 ≤ (s.getReg .x2).toNat ∧ (s.getReg .x2).toNat ≤ 0xc0000008 ∧
      (s.getReg .x2).toNat % 16 = 0 ∧ 0x20 ≤ (s.getReg .x10).toNat ∧
      (s.getReg .x10).toNat % 8 = 0 ∧ (s.getReg .x10).toNat + 96 ≤ 0xc0000008 := by
  have := h.stack.bounds (by decide) (by decide)
  have ho := ValidMemRange.bounds h.self (by decide)
  simp only [dropLayoutStack] at this
  omega

/-- The loop is over: at `0x8000c140`, or at a dead end. -/
def Done (s t₁ u : MachineState) : Prop :=
  (u.pc = 0x8000c140 ∧ Inv s t₁ u) ∨ Dead Image.code u

/-- One element: two calls, advance. -/
theorem body (hD : DropNopSpec) {s t₁ : MachineState} (hpre : DropLayoutPre s)
    (u : MachineState) (hu : ∃ k, LoopInv s t₁ u k) :
    (∃ v, Reaches Image.code u v ∧ Done s t₁ v) ∨
      (∃ v, Reaches Image.code u v ∧ (∃ k, LoopInv s t₁ v k) ∧
        (v.getReg .x18).toNat - (v.getReg .x9).toNat <
          (u.getReg .x18).toNat - (u.getReg .x9).toNat) := by
  obtain ⟨k, hk⟩ := hu
  have hlt := hk.lt
  have hE := ValidMemRange.bounds hpre.elems (by omega)
  obtain ⟨p, hp⟩ : ∃ p, p = vecPtr s (s.getReg .x10) + BitVec.ofNat 64 (80 * k) := ⟨_, rfl⟩
  have hx9 : u.getReg .x9 = p + 64 := by rw [hk.x9, hp]
  have hval (j : Nat) (hj : j < 10) : Sym.validAccess 8 (p + BitVec.ofNat 64 (8 * j)) = true :=
    ValidMemRange.access hpre.elems (by addr_omega [hp, hE, hlt, hj])
      (by addr_omega [hp, hE, hlt, hj]) (by addr_omega [hp, hE, hlt, hj])
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000c118_spec hk.pc (by
    rv_eval [hx9]
    exact ⟨hval 5 (by decide), hval 4 (by decide)⟩)
  have k₁ := b8000c118_keeps h₁
  obtain ⟨u₂, hr₂, ⟨hpc₂, hp₂, hm₂⟩ | hdead⟩ := hD.call hr₁ (b8000c118_pc h₁) trivial
  swap
  · exact Or.inl ⟨u₂, hr₂, Or.inr hdead⟩
  have i₂ := (hk.toInv.of_block (b8000c118_mem_same h₁) k₁).of_call hp₂ hm₂
  have hx9₂ : u₂.getReg .x9 = p + 64 := by rw [hp₂.reg .x9, k₁ .x9 (by decide), hx9]
  obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000c128_spec
    (by rw [hpc₂, returnAddress_eq, b8000c118_x1 h₁]; decide) (by
      rv_eval [hx9₂]
      exact ⟨hval 8 (by decide), hval 7 (by decide)⟩)
  have k₃ := b8000c128_keeps h₃
  obtain ⟨u₄, hr₄, ⟨hpc₄, hp₄, hm₄⟩ | hdead⟩ := hD.call hr₃ (b8000c128_pc h₃) trivial
  swap
  · exact Or.inl ⟨u₄, hr₂.trans hr₄, Or.inr hdead⟩
  have i₄ := (i₂.of_block (b8000c128_mem_same h₃) k₃).of_call hp₄ hm₄
  obtain ⟨u₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b8000c138_spec
    (by rw [hpc₄, returnAddress_eq, b8000c128_x1 h₃]; decide) trivial
  have k₅ := b8000c138_keeps h₅
  have i₅ := i₄.of_block (b8000c138_mem_same h₅) k₅
  have hx9₄ : u₄.getReg .x9 = p + 64 := by rw [hp₄.reg .x9, k₃ .x9 (by decide), hx9₂]
  have hx18₄ : u₄.getReg .x18 = u.getReg .x18 := by
    rw [hp₄.reg .x18, k₃ .x18 (by decide), hp₂.reg .x18, k₁ .x18 (by decide)]
  have hx18 := hk.x18
  have hreach := hr₂.trans (hr₄.trans hr₅)
  by_cases hlast : k + 1 = (vecLen s (s.getReg .x10)).toNat
  · refine Or.inl ⟨u₅, hreach, Or.inl ⟨b8000c138_pc_not_taken h₅ ?_, i₅⟩⟩
    rw [hx9₄, hx18₄, hx18, hp]
    addr_omega [hlast, hE]
  · have hk1 : k + 1 < (vecLen s (s.getReg .x10)).toNat := by omega
    refine Or.inr ⟨u₅, hreach, ⟨k + 1, { toInv := i₅, pc := ?_, lt := hk1, x9 := ?_, x18 := ?_ }⟩, ?_⟩
    · exact b8000c138_pc_taken h₅ (by rw [hx9₄, hx18₄, hx18, hp]; addr_omega [hk1, hE])
    · rw [b8000c138_x9 h₅, hx9₄, hp]; addr_omega [hk1, hE]
    · rw [k₅ .x18 (by decide), hx18₄, hx18]
    · rw [b8000c138_x9 h₅, k₅ .x18 (by decide), hx9₄, hx18₄, hx18, hx9, hp]
      addr_omega [hk1, hE]

/-- The last three calls, the third a tail call, with the caller's `ra`. -/
theorem exit (hD : DropNopSpec) {s t₁ u : MachineState} (hpre : DropLayoutPre s)
    (hpc : u.pc = 0x8000c140) (h : Inv s t₁ u)
    (hsl : t₁.getMem (s.getReg .x2 - 8) = s.getReg .x1 ∧ t₁.getMem (s.getReg .x2 - 16) = s.getReg .x8 ∧
      t₁.getMem (s.getReg .x2 - 24) = s.getReg .x9 ∧ t₁.getMem (s.getReg .x2 - 32) = s.getReg .x18) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = returnAddress s ∧ Preserves s t ∧
      ∀ a, t.getMem a = t₁.getMem a) ∨ Dead Image.code t) := by
  have hb := hpre.bounds
  have hv (j : Nat) (hj : j < 12) : Sym.validAccess 8 (s.getReg .x10 + BitVec.ofNat 64 (8 * j)) = true :=
    hpre.self j hj
  obtain ⟨sl1, sl2, sl3, sl4⟩ := hsl
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000c140_spec hpc (by
    rv_eval [h.self]
    exact ⟨hv 5 (by decide), hv 4 (by decide)⟩)
  have k₁ := b8000c140_keeps h₁
  obtain ⟨u₂, hr₂, ⟨hpc₂, hp₂, hm₂⟩ | hdead⟩ := hD.call hr₁ (b8000c140_pc h₁) trivial
  swap
  · exact ⟨u₂, hr₂, Or.inr hdead⟩
  have i₂ := (h.of_block (b8000c140_mem_same h₁) k₁).of_call hp₂ hm₂
  obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000c150_spec
    (by rw [hpc₂, returnAddress_eq, b8000c140_x1 h₁]; decide) (by
      rv_eval [i₂.self]
      exact ⟨hv 8 (by decide), hv 7 (by decide)⟩)
  have k₃ := b8000c150_keeps h₃
  obtain ⟨u₄, hr₄, ⟨hpc₄, hp₄, hm₄⟩ | hdead⟩ := hD.call hr₃ (b8000c150_pc h₃) trivial
  swap
  · exact ⟨u₄, hr₂.trans hr₄, Or.inr hdead⟩
  have i₄ := (i₂.of_block (b8000c150_mem_same h₃) k₃).of_call hp₄ hm₄
  obtain ⟨u₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b8000c160_spec
    (by rw [hpc₄, returnAddress_eq, b8000c150_x1 h₃]; decide) (by
      rv_eval [i₄.sp, i₄.self]
      and_intros
      · valid_access hpre.stack.valid [hb]
      · valid_access hpre.stack.valid [hb]
      · valid_access hpre.stack.valid [hb]
      · valid_access hpre.stack.valid [hb]
      · exact hv 11 (by decide)
      · exact hv 10 (by decide))
  have k₅ := b8000c160_keeps h₅
  have x1 := b8000c160_x1 h₅
  have x2 := b8000c160_x2 h₅
  have x8 := b8000c160_x8 h₅
  have x9 := b8000c160_x9 h₅
  have x18 := b8000c160_x18 h₅
  rv_eval [i₄.sp, i₄.mem, sl1, sl2, sl3, sl4] at x1 x2 x8 x9 x18
  obtain ⟨t, hr, ⟨hpc', hp', hm'⟩ | hdead⟩ := hD.call hr₅ (b8000c160_pc h₅) trivial
  swap
  · exact ⟨t, hr₂.trans (hr₄.trans hr), Or.inr hdead⟩
  refine ⟨t, hr₂.trans (hr₄.trans hr), Or.inl ⟨by rw [hpc', returnAddress, returnAddress, x1], ?_,
    fun a ↦ (hm' a).trans ((b8000c160_mem_same h₅ a).trans (i₄.mem a))⟩⟩
  refine preserves_of ((hp'.reg .x2).trans x2) ((hp'.reg .x8).trans x8) ((hp'.reg .x9).trans x9)
    ((hp'.reg .x18).trans x18) ?_ fun r hr' ↦ ?_
  · rw [hp'.reg .x19, k₅ .x19 (by decide), i₄.kept .x19 (by decide)]
  · rw [hp' r (mem_of_mem hr' _), k₅ r (mem_of_mem hr' _), i₄.kept r (mem_of_mem hr' _)]

/-- **`drop_glue::<Layout>` meets its contract**, given the no-op drop's. -/
theorem drop_layout_spec (hD : DropNopSpec) : DropLayoutSpec := by
  intro s hpc hpre
  have hb := hpre.bounds
  have hs := hpre.selfStack
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000c0e0_spec hpc (by
    rv_eval []
    and_intros <;> first
      | addr_omega [hb, hs]
      | exact hpre.self 2 (by decide)
      | valid_access hpre.stack.valid [hb])
  have k₁ := b8000c0e0_keeps h₁
  have hm₁ := b8000c0e0_frame h₁ (by addr_omega [hb])
  have hframe : MemFrame s t₁ (stackLo s dropLayoutStack) dropLayoutStack :=
    hm₁.mono fun a ha ↦ by addr_omega [ha, hb]
  have hself (j : Nat) (hj : j < 12) : t₁.getMem (s.getReg .x10 + BitVec.ofNat 64 (8 * j)) =
      s.getMem (s.getReg .x10 + BitVec.ofNat 64 (8 * j)) :=
    hm₁ _ (by addr_omega [hb, hs, hj])
  have i₁ : Inv s t₁ t₁ := ⟨b8000c0e0_x2 h₁, b8000c0e0_x8 h₁,
    fun r hr ↦ k₁ r (mem_of_mem hr _), fun _ ↦ rfl⟩
  have hsl := And.intro (b8000c0e0_m_x2_n8 h₁) (And.intro (b8000c0e0_m_x2_n16 h₁)
    (And.intro (b8000c0e0_m_x2_n24 h₁) (b8000c0e0_m_x2_n32 h₁)))
  have finish (u : MachineState) (hu : Reaches Image.code s u) (hd : Done s t₁ u) :
      ∃ t, Reaches Image.code s t ∧ ((t.pc = returnAddress s ∧ Preserves s t ∧
        MemFrame s t (stackLo s dropLayoutStack) dropLayoutStack) ∨ Dead Image.code t) := by
    rcases hd with ⟨hpc', hi⟩ | hdead
    · obtain ⟨t, hr, ⟨hpc'', hp, hm⟩ | hdead⟩ := exit hD hpre hpc' hi hsl
      · exact ⟨t, hu.trans hr, Or.inl ⟨hpc'', hp, fun a ha ↦ (hm a).trans (hframe a ha)⟩⟩
      · exact ⟨t, hu.trans hr, Or.inr hdead⟩
    · exact ⟨u, hu, Or.inr hdead⟩
  have hlen : t₁.getReg .x10 = vecLen s (s.getReg .x10) := b8000c0e0_x10 h₁
  by_cases h0 : vecLen s (s.getReg .x10) = 0
  · exact finish t₁ hr₁ (Or.inl ⟨b8000c0e0_pc_taken h₁ h0, i₁⟩)
  have hE := ValidMemRange.bounds hpre.elems (by
    have : (vecLen s (s.getReg .x10)).toNat ≠ 0 := fun h' ↦ h0 (BitVec.eq_of_toNat_eq h')
    omega)
  obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000c100_spec (b8000c0e0_pc_not_taken h₁ h0) (by
    rv_eval [b8000c0e0_x8 h₁]
    exact hpre.self 1 (by decide))
  have k₂ := b8000c100_keeps h₂
  have i₂ := i₁.of_block (b8000c100_mem_same h₂) k₂
  have hptr : t₁.getMem (s.getReg .x10 + 8) = vecPtr s (s.getReg .x10) := hself 1 (by decide)
  have hl : (vecLen s (s.getReg .x10)).toNat ≠ 0 := fun h' ↦ h0 (BitVec.eq_of_toNat_eq h')
  have hloop : LoopInv s t₁ t₂ 0 := {
    toInv := i₂
    pc := b8000c100_pc h₂
    lt := Nat.pos_of_ne_zero hl
    x9 := by rw [b8000c100_x9 h₂, b8000c0e0_x8 h₁, hptr]; addr_omega [hE]
    x18 := by
      rw [b8000c100_x18 h₂, b8000c0e0_x8 h₁, hlen, hptr]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat,
        show (64 : Word).toNat = 64 from rfl, show (16 : Word).toNat = 16 from rfl]
      have : (vecLen s (s.getReg .x10)).toNat * 80 < 2 ^ 64 := by omega
      omega }
  obtain ⟨u, hu, hd⟩ := Reaches.loop (fun u ↦ ∃ k, LoopInv s t₁ u k)
    (fun u ↦ (u.getReg .x18).toNat - (u.getReg .x9).toNat) (Done s t₁) (body hD hpre) t₂
    ⟨0, hloop⟩
  exact finish u (hr₁.trans (hr₂.trans hu)) hd

end Rv64Verifier.Runtime.Drop
