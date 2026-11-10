import Rv64Verifier.Proofs.Walk.Try11

/-!
# `walk`: the `i`-th table's `vec![h; w]` (R11)

At `0x800031a4` (`Tmp11 .. i T`) the buffer `T`, above `kappas`' buffer, holds `w` words `h`.
`kapTmpB` builds it for `h = 0` (`try_allocate_in` zeroed).
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Compile Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Layout Rv64Verifier.Model.LayoutMirror
  Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- At `0x800031a4`: the `i`-th table's `vec![h; w]` in `T`. -/
structure Tmp11 (OI : MachineState → Word → List (List Opening) → Prop) (s u : MachineState)
    (A : List E) (k : Nat) (R Q B : Word) (lo lo2 i : Nat) (T : Word) : Prop where
  keep : Keep11 OI s u A k R Q B lo lo2
  kv : KapVec s u lo2 (kapPre A k i)
  lt : i < 6
  x8 : u.getReg .x8 = BitVec.ofNat 64 (80 * i)
  x9 : u.getReg .x9 = 6
  x19 : u.getReg .x19 = 0xa0000460
  x20 : u.getReg .x20 = 480
  x22 : u.getReg .x22 = 6
  x27 : u.getReg .x27 = B
  x24 : u.getReg .x24 = BitVec.ofNat 64 (tableWidthsRust.getD i 0)
  x25 : u.getReg .x25 = T
  tal : T.toNat % 8 = 0
  tlo : (vecPtr u (s.getReg .x2 - 1344)).toNat + 8 * (vecCap u (s.getReg .x2 - 1344)).toNat ≤
    T.toNat
  thi : T.toNat + 8 * tableWidthsRust.getD i 0 ≤ heapNext u
  tvals : ∀ j < tableWidthsRust.getD i 0,
    u.getMem (T + BitVec.ofNat 64 (8 * j)) = BitVec.ofNat 64 ((hts A).getD i 0)

theorem Keep11.same {OI : MachineState → Word → List (List Opening) → Prop} {s u v : MachineState}
    {A : List E} {k : Nat} {R Q B : Word} {lo lo2 : Nat} (hpre : WalkPre s)
    (h : Keep11 OI s u A k R Q B lo lo2) (hm : ∀ a, v.getMem a = u.getMem a)
    (sp : v.getReg .x2 = u.getReg .x2) : Keep11 OI s v A k R Q B lo lo2 := by
  have hn : heapNext v = heapNext u := by simp only [heapNext, hm]
  exact h.keep hpre (w := fun _ ↦ False) (Layout.DFrame.of_same hm _) (fun _ h ↦ h.elim)
    ⟨hn ▸ h.at11.base.inv.heap.lo, hn ▸ h.at11.base.inv.heap.hi⟩ hn.ge sp

theorem KapVec.same {s u v : MachineState} {lo2 : Nat} {ks : List Nat} (hpre : WalkPre s)
    (h : KapVec s u lo2 ks) (hk : ks ≠ []) (hhi : heapNext u ≤ heapEnd)
    (hm : ∀ a, v.getMem a = u.getMem a) : KapVec s v lo2 ks := by
  obtain ⟨hb1, -, -, -⟩ := Walk.bounds hpre
  have hn : heapNext v = heapNext u := by simp only [heapNext, hm]
  exact h.keep hk (w := fun _ ↦ False) (Layout.DFrame.of_same hm _) (fun _ _ h ↦ h)
    (fun _ _ h ↦ h) (by addr_omega [hb1]) hhi hn.ge

/-- An aligned doubleword of `n` zero bytes is zero. -/
theorem getMem_zero_of_bytes {t : MachineState} {a : Word} {N k : Nat}
    (h : bytesAt t a N = List.replicate N 0) (ha : a.toNat % 8 = 0) (hk : k % 8 = 0)
    (hkN : k + 8 ≤ N) : t.getMem (a + BitVec.ofNat 64 k) = 0 := by
  refine eq_of_extractByte fun i hi ↦ ?_
  have hal : (a + BitVec.ofNat 64 k).toNat % 8 = 0 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  rw [← byteAt_add hal hi, Layout.add_ofNat_add]
  have e := List.getElem_of_eq h (by rw [bytesAt_length]; omega : k + i < (bytesAt t a N).length)
  rw [bytesAt_getElem, List.getElem_replicate] at e
  rw [e]
  simp [extractByte]

end Rv64Verifier.Proofs.Walk

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Compile Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Layout Rv64Verifier.Model.LayoutMirror
  Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

set_option maxRecDepth 8192 in
/-- `h = 0`: `vec![0; w]` by a zeroed allocation. -/
theorem kapTmpB (hTA : TryAllocZeroedSpec) {OI : MachineState → Word → List (List Opening) → Prop}
    {s u c : MachineState} {A : List E} {k : Nat} {R Q B : Word} {lo lo2 i : Nat}
    (hpre : WalkPre s) (h : Kap11 OI s u A k R Q B lo lo2 i) (hc : c.pc = 0x80003180)
    (mc : ∀ a, c.getMem a = u.getMem a)
    (kc : ∀ r ∈ ([.x2, .x8, .x9, .x19, .x20, .x22, .x27] : List Reg), c.getReg r = u.getReg r)
    (x10 : c.getReg .x10 = s.getReg .x2 - 928)
    (x24 : c.getReg .x24 = BitVec.ofNat 64 (tableWidthsRust.getD i 0))
    (h0 : (hts A).getD i 0 = 0) :
    ∃ t, Reaches Image.code c t ∧ (Dead Image.code t ∨
      (t.pc = 0x800031a4 ∧ ∃ T, Tmp11 OI s t A k R Q B lo lo2 i T)) := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have hi := h.lt
  have hk := kapPre_ne A k (le_of_lt hi)
  have hw := width_pos hi
  have hhi := h.keep.at11.base.inv.heap.hi
  have spc : c.getReg .x2 = s.getReg .x2 - 2656 := by
    rw [kc .x2 (by decide)]; exact h.keep.at11.base.inv.sp
  obtain ⟨c₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80003180_spec hc (by rv_eval [])
  have m₁ (a : Word) : c₁.getMem a = u.getMem a := by rw [b80003180_mem_same h₁, mc]
  have k₁ := b80003180_keeps h₁
  have K₁ := h.keep.same hpre m₁ (by rw [k₁ .x2 (by decide), kc .x2 (by decide)])
  have kv₁ := h.kv.same hpre hk hhi m₁
  obtain ⟨t, hr, hd | ⟨hpct, hp, K', kv', hP, hC, hok⟩⟩ := tryCall hTA hpre hk K₁ kv₁
    (b80003180_pc h₁) (by rw [k₁ .x10 (by decide)]; exact x10) hw.2
    (by rw [b80003180_x11 h₁]; exact x24) (b80003180_x13 h₁) (b80003180_x14 h₁) (by omega)
  · exact ⟨t, hr₁.trans hr, Or.inl hd⟩
  have pct : t.pc = 0x80003198 := by rw [hpct, returnAddress_eq, b80003180_x1 h₁]; decide
  have spt : t.getReg .x2 = s.getReg .x2 - 2656 := by
    rw [hp .x2 (by decide), k₁ .x2 (by decide)]; exact spc
  obtain ⟨t₁, hrt₁, ht₁⟩ := Sym.BlockSpec.reaches b80003198_spec pct (by
    rv_eval [spt]; simp only [Sym.validAccess_eight]; addr_omega [hb1, hb2, hb3])
  have e1728 : t.getReg .x2 + 1728 = s.getReg .x2 - 928 := by
    rw [spt]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  by_cases hz : t.getMem (s.getReg .x2 - 928) = 0
  swap
  · exact ⟨t₁, hr₁.trans (hr.trans hrt₁), Or.inl (trapAt (b80003198_pc_taken ht₁ (by rw [e1728]; exact hz)))⟩
  have pc₁ := b80003198_pc_not_taken ht₁ (by rw [e1728]; exact hz)
  obtain ⟨o8, o1, o2, o3, oz⟩ := hok hz
  obtain ⟨t₂, hrt₂, ht₂⟩ := Sym.BlockSpec.reaches b800031a0_spec pc₁ (by
    rv_eval [spt, b80003198_keeps ht₁ .x2 (by decide)]
    simp only [Sym.validAccess_eight]; addr_omega [hb1, hb2, hb3])
  have mt₂ (a : Word) : t₂.getMem a = t.getMem a := by
    rw [b800031a0_mem_same ht₂, b80003198_mem_same ht₁]
  have kt₂ (r : Reg) (hr : r ∈ ([.x2, .x8, .x9, .x19, .x20, .x22, .x24, .x27] : List Reg)) :
      t₂.getReg r = c.getReg r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [b800031a0_keeps ht₂ _ (by decide), b80003198_keeps ht₁ _ (by decide), hp _ (by decide),
        k₁ _ (by decide)]
  have hn₂ : heapNext t₂ = heapNext t := by simp only [heapNext, mt₂]
  set T := t.getMem (s.getReg .x2 - 912) with hT
  have ht := K'.at11.base.inv.heap.hi
  refine ⟨t₂, hr₁.trans (hr.trans (hrt₁.trans hrt₂)), Or.inr ⟨b800031a0_pc ht₂, T, {
    keep := K'.same hpre mt₂ (by rw [kt₂ .x2 (by decide), hp .x2 (by decide), k₁ .x2 (by decide)])
    kv := kv'.same hpre hk ht mt₂
    lt := hi
    x8 := by rw [kt₂ .x8 (by decide), kc .x8 (by decide)]; exact h.x8
    x9 := by rw [kt₂ .x9 (by decide), kc .x9 (by decide)]; exact h.x9
    x19 := by rw [kt₂ .x19 (by decide), kc .x19 (by decide)]; exact h.x19
    x20 := by rw [kt₂ .x20 (by decide), kc .x20 (by decide)]; exact h.x20
    x22 := by rw [kt₂ .x22 (by decide), kc .x22 (by decide)]; exact h.x22
    x27 := by rw [kt₂ .x27 (by decide), kc .x27 (by decide)]; exact h.x27
    x24 := by rw [kt₂ .x24 (by decide)]; exact x24
    x25 := by
      rw [b800031a0_x25 ht₂, b80003198_keeps ht₁ .x2 (by decide), spt]
      rv_eval [b80003198_mem_same ht₁]
      exact hT.symm
    tal := o1
    tlo := by
      have e1 : vecPtr t₂ (s.getReg .x2 - 1344) = vecPtr c₁ (s.getReg .x2 - 1344) := by
        simp only [vecPtr, mt₂]; exact hP
      have e2 : vecCap t₂ (s.getReg .x2 - 1344) = vecCap c₁ (s.getReg .x2 - 1344) := by
        simp only [vecCap, mt₂]; exact hC
      rw [e1, e2]; exact o2
    thi := by rw [hn₂]; exact o3
    tvals := fun j hj ↦ by
      rw [mt₂, h0]
      exact getMem_zero_of_bytes (oz (by rw [b80003180_x12 h₁]; decide)) o1 (by omega) (by omega) }⟩⟩

end Rv64Verifier.Proofs.Walk
