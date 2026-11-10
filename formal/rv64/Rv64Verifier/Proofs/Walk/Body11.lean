import Rv64Verifier.Proofs.Walk.Head11

/-!
# `walk`: one table of `kappas` (R11)

`kapCheck` reads the `i`-th table's opcode (bounded twice), its height `h` and its width `w`.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Compile Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Layout Rv64Verifier.Model.LayoutMirror
  Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- `kappas`' buffer. -/
@[rv_addr] def kapBuf (s u : MachineState) (x : Word) : Prop :=
  Within x (vecPtr u (s.getReg .x2 - 1344)) (8 * (vecCap u (s.getReg .x2 - 1344)).toNat)

theorem KapVec.bounds {s u : MachineState} {lo2 : Nat} {ks : List Nat} (h : KapVec s u lo2 ks)
    (hk : ks ≠ []) : (vecPtr u (s.getReg .x2 - 1344)).toNat % 8 = 0 ∧
      heapStart ≤ (vecPtr u (s.getReg .x2 - 1344)).toNat ∧
      (vecPtr u (s.getReg .x2 - 1344)).toNat + 8 * (vecCap u (s.getReg .x2 - 1344)).toNat ≤
        heapNext u ∧ ks.length ≤ (vecCap u (s.getReg .x2 - 1344)).toNat := by
  have hr := h.ok.raw
  have hl := h.ok.len
  have hn := h.len
  have : ks.length ≠ 0 := fun h0 ↦ hk (List.eq_nil_of_length_eq_zero h0)
  simp only [RawVecOk, Buf] at hr
  rcases hr.2 with h0 | h0
  · omega
  · exact ⟨hr.1, h0.1, by omega, by omega⟩

/-- A frame missing `kappas`' header and buffer keeps it. -/
theorem KapVec.keep {s u v : MachineState} {lo2 : Nat} {ks : List Nat} (h : KapVec s u lo2 ks)
    (hk : ks ≠ []) {w : Word → Prop} (fr : Layout.DFrame u v w)
    (hh : ∀ x, Within x (s.getReg .x2 - 1344) 24 → ¬ w x) (hb : ∀ x, kapBuf s u x → ¬ w x)
    (hs : (s.getReg .x2 - 1344).toNat + 24 ≤ 2 ^ 64) (hhi : heapNext u ≤ heapEnd)
    (mono : heapNext u ≤ heapNext v) : KapVec s v lo2 ks := by
  obtain ⟨b1, b2, b3, b4⟩ := h.bounds hk
  simp only [heapEnd] at hhi
  have g (o : Nat) (ho : o + 8 ≤ 24) : v.getMem (s.getReg .x2 - 1344 + BitVec.ofNat 64 o) =
      u.getMem (s.getReg .x2 - 1344 + BitVec.ofNat 64 o) :=
    fr.getMem_of (fun x hx ↦ hh x (by addr_omega [hx, ho, hs])) (by addr_omega [ho, hs])
  have hc : vecCap v (s.getReg .x2 - 1344) = vecCap u (s.getReg .x2 - 1344) := by
    simpa [vecCap] using g 0 (by decide)
  have hp : vecPtr v (s.getReg .x2 - 1344) = vecPtr u (s.getReg .x2 - 1344) := g 8 (by decide)
  have hl : vecLen v (s.getReg .x2 - 1344) = vecLen u (s.getReg .x2 - 1344) := g 16 (by decide)
  have hraw := h.ok.raw
  refine ⟨⟨?_, ?_⟩, by rw [hp]; exact h.fresh, by rw [hl]; exact h.len, fun j hj ↦ ?_⟩
  · simp only [RawVecOk, Buf, hc, hp] at hraw ⊢
    exact ⟨hraw.1, hraw.2.imp id fun h' ↦ ⟨h'.1, by omega⟩⟩
  · rw [hc, hl]; exact h.ok.len
  · rw [hp, ← h.vals j hj]
    have hL := h.len
    simp only [heapStart] at b2
    exact fr.getMem_of (fun x hx ↦ hb x (by simp only [kapBuf, Within] at hx ⊢; addr_omega [hx, hj, b2, b3, b4, hhi]))
      (by addr_omega [hj, b2, b3, b4, hhi])

theorem kapPre_ne (A : List E) (k : Nat) {i : Nat} (hi : i ≤ 6) : kapPre A k i ≠ [] := fun h0 ↦ by
  have := kapPre_length A k i hi
  rw [h0, List.length_nil, kapLen] at this
  omega

set_option maxRecDepth 8192 in
/-- The `i`-th table's opcode, bounded, its height `h` (`s5`) and width `w` (`s8`); the branch on
`h = 0`. -/
theorem kapCheck {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q B : Word} {lo lo2 i : Nat} (hpre : WalkPre s)
    (hpc : u.pc = 0x800030c8) (h : Kap11 OI s u A k R Q B lo lo2 i) :
    ∃ t, Reaches Image.code u t ∧
      t.pc = (if (hts A).getD i 0 = 0 then 0x80003180 else 0x80003100) ∧
      (∀ a, t.getMem a = u.getMem a) ∧
      (∀ r ∈ ([.x2, .x8, .x9, .x19, .x20, .x22, .x27] : List Reg), t.getReg r = u.getReg r) ∧
      t.getReg .x10 = s.getReg .x2 - 928 ∧ t.getReg .x21 = BitVec.ofNat 64 ((hts A).getD i 0) ∧
      t.getReg .x24 = BitVec.ofNat 64 (tableWidthsRust.getD i 0) := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have H := h.keep.at11.base
  have sp : u.getReg .x2 = s.getReg .x2 - 2656 := H.inv.sp
  have hi := h.lt
  have hB := H.bufB
  have hQ := H.bufQ
  have hl := H.loLe
  have hhu := H.inv.heap.hi
  have hs0 := hpre.heap.lo
  have hmo := H.inv.mono
  simp only [heapEnd, heapStart] at hhu hs0
  obtain ⟨-, -, -, -, sQ, -⟩ := H.slots
  have ro := H.inv.rodata hpre
  have op := opAt H h.keep.at11.op5 hi
  have e72 : u.getReg .x27 + u.getReg .x8 + 72 = B + BitVec.ofNat 64 (80 * i) + 72 := by
    rw [h.x27, h.x8]
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b800030c8_spec hpc (by
    rv_eval [e72]
    simp only [Sym.validAccess_eight]
    addr_omega [hB, hl, hhu, hi, hs0, hmo])
  have x10₁ : u₁.getReg .x10 = BitVec.ofNat 64 i := by rw [b800030c8_x10 h₁, e72, op]
  have hiN : (BitVec.ofNat 64 i).toNat = i := by rw [BitVec.toNat_ofNat]; omega
  have pc₁ := b800030c8_pc_taken h₁ (by rw [e72, op, hiN, h.x22]; simp; omega)
  have m₁ := b800030c8_mem_same h₁
  have k₁ := b800030c8_keeps h₁
  obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b800030d8_spec pc₁ (by rv_eval [])
  have pc₂ := b800030d8_pc_taken h₂ (by rw [x10₁, hiN, k₁ .x9 (by decide), h.x9]; simp; omega)
  have m₂ := b800030d8_mem_same h₂
  have k₂ := b800030d8_keeps h₂
  have sp₂ : u₂.getReg .x2 = s.getReg .x2 - 2656 := by
    rw [k₂ .x2 (by decide), k₁ .x2 (by decide)]; exact sp
  have x10₂ : u₂.getReg .x10 = BitVec.ofNat 64 i := by rw [k₂ .x10 (by decide)]; exact x10₁
  have x19₂ : u₂.getReg .x19 = 0xa0000460 := by
    rw [k₂ .x19 (by decide), k₁ .x19 (by decide)]; exact h.x19
  have mQ' : u₂.getMem (s.getReg .x2 - 2464) = Q := by rw [m₂, m₁]; exact sQ
  have mQ : u₂.getMem (u₂.getReg .x2 + 192) = Q := by rw [sp₂]; rv_eval [mQ']
  have hgt : u₂.getMem (u₂.getMem (u₂.getReg .x2 + (192 : Word)) + (u₂.getReg .x10 * (8 : Word))) =
      BitVec.ofNat 64 ((hts A).getD i 0) := by
    rw [mQ, x10₂, m₂, m₁, mul8 hi]; exact H.heights i hi
  obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b800030e0_spec pc₂ (by
    rv_eval [sp₂, mQ', x10₂, x19₂, mul8 hi]
    simp only [Sym.validAccess_eight]
    and_intros <;> addr_omega [hb1, hb2, hb3, hQ, hl, hhu, hi, hs0, hmo])
  have m₃ := b800030e0_mem_same h₃
  have k₃ := b800030e0_keeps h₃
  have hh : (hts A).getD i 0 ≤ 32 := heightsLe H.ok i
  have hz : BitVec.ofNat 64 ((hts A).getD i 0) = 0 ↔ (hts A).getD i 0 = 0 := by
    constructor
    · intro he
      have := congrArg BitVec.toNat he
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
      exact this
    · intro he; rw [he]; rfl
  refine ⟨u₃, hr₁.trans (hr₂.trans hr₃), ?_, fun a ↦ by rw [m₃, m₂, m₁], fun r hr ↦ ?_, ?_, ?_, ?_⟩
  · split_ifs with h0
    · exact b800030e0_pc_taken h₃ (by rw [hgt]; exact hz.mpr h0)
    · exact b800030e0_pc_not_taken h₃ (by rw [hgt]; exact fun he ↦ h0 (hz.mp he))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [k₃ _ (by decide), k₂ _ (by decide), k₁ _ (by decide)]
  · rw [b800030e0_x10 h₃, sp₂]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  · rw [b800030e0_x21 h₃]; exact hgt
  · rw [b800030e0_x24 h₃, x19₂, x10₂, mul8 hi, m₂, m₁]
    rw [show BitVec.ofNat 64 (8 * i) = BitVec.ofNat 64 i * 8 from (mul8 hi).symm]
    exact widthRod ro hi

end Rv64Verifier.Proofs.Walk
