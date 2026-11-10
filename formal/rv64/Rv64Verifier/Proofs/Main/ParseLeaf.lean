import Rv64Verifier.Proofs.Main.ParseSib

/-!
# A path's leaf

`0x80000cdc` copies the leaf's `l` words from the input (from word `kl`) to the buffer at `L`, a
word at a time (`leaf_body`, `leaf_loop`).
-/

namespace Rv64Verifier.Proofs.Main
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile Rv64Verifier.Runtime
  Rv64Verifier.Proofs.Bytecode Rv64Verifier.Proofs.End Rv64Verifier.Blocks.F3

/-- The leaf's copy at `e` (`0x80000cdc`, or `0x80000cf0` when done), `d` of its `l` words
copied; `t₀` where it started. -/
structure LfS (u₀ : MachineState) (words : List Word) (L : Word) (l kl : Nat) (t₀ : MachineState)
    (e : Word) (t : MachineState) (d : Nat) : Prop where
  pg : PG u₀ t
  pc : t.pc = e
  le : d ≤ l
  regs : ∀ r ∈ calleeSaved, t.getReg r = t₀.getReg r
  x10 : t.getReg .x10 = t₀.getReg .x10
  x11 : t.getReg .x11 = L + BitVec.ofNat 64 (8 * l)
  x12 : t.getReg .x12 = inputBase + BitVec.ofNat 64 (8 * (kl + d))
  x13 : t.getReg .x13 = L + BitVec.ofNat 64 (8 * d)
  room : kl + l ≤ words.length
  val : t.readWords L d = (words.drop kl).take d
  frame : BFrame t₀ t (Within · L (8 * l))
  buf : L.toNat % 8 = 0 ∧ heapNext u₀ ≤ L.toNat ∧ L.toNat + 8 * l ≤ heapNext t₀
  heap : heapNext t = heapNext t₀

theorem readWords_snoc {t t' : MachineState} {L : Word} {d : Nat}
    (hf : MemFrame t t' (L + BitVec.ofNat 64 (8 * d)) 8) (hL : L.toNat + 8 * (d + 1) ≤ 2 ^ 64) :
    t'.readWords L (d + 1) = t.readWords L d ++ [t'.getMem (L + BitVec.ofNat 64 (8 * d))] := by
  rw [readWords_eq_map, readWords_eq_map, List.range_succ, List.map_append]
  congr 1
  apply List.map_congr_left
  intro i hi
  simp only [List.mem_range] at hi
  exact hf _ (by addr_omega [hi, hL])

theorem take_drop_succ {words : List Word} {kl d : Nat} (h : kl + d < words.length) :
    (words.drop kl).take (d + 1) = (words.drop kl).take d ++ [words[kl + d]] := by
  rw [List.take_add_one, List.getElem?_drop, List.getElem?_eq_getElem h]
  rfl

section
variable {s u₀ t : MachineState} {words : List Word}

/-- One word. -/
theorem leaf_body (h0 : ParseA s words u₀) {L : Word} {l kl d : Nat} {t₀ : MachineState}
    (hs : LfS u₀ words L l kl t₀ 0x80000cdc t d) (hd : d < l) :
    ∃ v, Reaches Image.code t v ∧
      ((d + 1 < l ∧ LfS u₀ words L l kl t₀ 0x80000cdc v (d + 1)) ∨
      (d + 1 = l ∧ LfS u₀ words L l kl t₀ 0x80000cf0 v (d + 1))) := by
  have hg := hs.pg
  have hsp := hg.sp
  have hfit := h0.inv.fits
  simp only [inputWords] at hfit
  have hib : inputBase.toNat = 0x10000000 := rfl
  have hhi := hg.heap.hi
  obtain ⟨hL8, hL0, hLl⟩ := hs.buf
  rw [← hs.heap] at hLl
  have hlo0 := h0.inv.heap.lo
  simp only [heapStart, heapNext, heapEnd] at hlo0 hhi hL0 hLl
  have hroom := hs.room
  have hin := input_mapped (words := words) (by simp only [inputWords]; exact hfit)
  have hLm : Mapped L (8 * l) := by simp only [Mapped]; omega
  obtain ⟨t₁, r₁, h₁⟩ := Sym.BlockSpec.reaches b80000cdc_spec hs.pc (by
    rv_eval [hs.x12, hs.x13]
    and_intros <;> first
      | valid_in hLm [hL8, hd, hLl, hhi]
      | valid_in hin [hib, hroom, hfit, hd])
  have k₁ := b80000cdc_keeps h₁
  have hfr := b80000cdc_frame h₁ (by rw [hs.x13]; addr_omega [hd, hLl, hhi])
  rw [hs.x13] at hfr
  have hsp₁ : t₁.getReg .x2 = msp := by rw [k₁ .x2 (by decide), hsp]
  have hg₁ : PG u₀ t₁ := hg.heapWrite hfr (by addr_omega [hL8, hd, hLl, hhi]) (by decide)
    (by addr_omega [hL0, hd, hLl, hhi]) (by simp only [heapNext]; addr_omega [hd, hLl, hhi])
    hsp₁
  have hw : t₁.getMem (L + BitVec.ofNat 64 (8 * d)) = words[kl + d] := by
    have e := b80000cdc_m_x13_0 h₁
    rw [hs.x13, hs.x12] at e
    rw [e, hg.word h0 (j := kl + d) (by omega) rfl]
  have hnx : heapNext t₁ = heapNext t := by
    simp only [heapNext]; rw [hfr _ (by addr_omega [hd, hLl, hhi])]
  have hS : ∀ e, t₁.pc = e → LfS u₀ words L l kl t₀ e t₁ (d + 1) := fun e he ↦
    { pg := hg₁
      pc := he
      le := by omega
      regs := fun r hr ↦ by rw [k₁ r (mem_of_calleeSaved hr _), hs.regs r hr]
      x10 := by rw [k₁ .x10 (by decide), hs.x10]
      x11 := by rw [k₁ .x11 (by decide), hs.x11]
      x12 := by rw [b80000cdc_x12 h₁, hs.x12]; addr_omega [hib, hroom, hfit, hd]
      x13 := by rw [b80000cdc_x13 h₁, hs.x13]; addr_omega [hd, hLl, hhi]
      room := hroom
      val := by
        rw [readWords_snoc hfr (by omega), hs.val, hw, take_drop_succ (by omega)]
      frame := hs.frame.trans (BFrame.of_memFrame hfr (by addr_omega [hL8, hd, hLl, hhi])
        (by decide)) fun a ha ↦ by addr_omega [ha, hd, hLl, hhi]
      buf := hs.buf
      heap := by rw [hnx, hs.heap] }
  by_cases he : d + 1 = l
  · exact ⟨t₁, r₁, Or.inr ⟨he, hS _ (b80000cdc_pc_not_taken h₁ (by
      rw [hs.x13, hs.x11]; addr_omega [hd, he, hLl, hhi]))⟩⟩
  · exact ⟨t₁, r₁, Or.inl ⟨by omega, hS _ (b80000cdc_pc_taken h₁ (by
      rw [hs.x13, hs.x11]; addr_omega [hd, he, hLl, hhi]))⟩⟩

/-- The leaf's copy. -/
theorem leaf_loop (h0 : ParseA s words u₀) {L : Word} {l kl : Nat} {t₀ : MachineState}
    (hs : LfS u₀ words L l kl t₀ 0x80000cdc t 0) (hl : 0 < l) :
    ∃ v, Reaches Image.code t v ∧ LfS u₀ words L l kl t₀ 0x80000cf0 v l := by
  refine Reaches.loop (fun t ↦ ∃ d, d < l ∧ LfS u₀ words L l kl t₀ 0x80000cdc t d)
    (fun t ↦ l - ((t.getReg .x13).toNat - L.toNat) / 8) _ ?_ t ⟨0, hl, hs⟩
  rintro t ⟨d, hd, hsd⟩
  obtain ⟨v, hv, ⟨hl', hsv⟩ | ⟨he, hsv⟩⟩ := leaf_body h0 hsd hd
  · refine Or.inr ⟨v, hv, ⟨d + 1, hl', hsv⟩, ?_⟩
    have b := hsd.buf.2.2
    have hhi := hsd.pg.heap.hi
    rw [← hsd.heap] at b
    simp only [heapNext, heapEnd] at b hhi
    have e1 : (v.getReg .x13).toNat = L.toNat + 8 * (d + 1) := by
      rw [hsv.x13]; addr_omega [b, hhi, hl']
    have e0 : (t.getReg .x13).toNat = L.toNat + 8 * d := by
      rw [hsd.x13]; addr_omega [b, hhi, hd]
    rw [e0, e1]
    omega
  · exact Or.inl ⟨v, hv, he ▸ hsv⟩

end

end Rv64Verifier.Proofs.Main
