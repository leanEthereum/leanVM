import Rv64Verifier.Proofs.Pcs.ExtendScanLoop

/-!
# `Vec<StackClaim>::extend_desugared`: the push's `selector_point`

From `Push` at `0x80009cdc`: the iterator's position written, `selector_point(F + 80, index >>
variables, stack_log - variables)`, to `AfterSel` at `0x80009d08`.
-/

namespace Rv64Verifier.Proofs.Pcs.Extend
open RiscvZkvm.Rv64 Rv64Verifier.Runtime Rv64Verifier.Transcript Rv64Verifier.Pcs
  Rv64Verifier.PcsContracts Rv64Verifier.Model.Pcs Rv64Verifier.Blocks.F37
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem hK : extendStack = 464 := rfl

theorem sbounds {s : MachineState} (h : Walk.ExtendPreE s) :
    0xa0000f38 + 464 ≤ (s.getReg .x2).toNat ∧ (s.getReg .x2).toNat ≤ 0xc0000008 ∧
      (s.getReg .x2).toNat % 16 = 0 := by
  have hm := h.stack.mapped (by decide) (by decide)
  have hn := h.stack.next
  have hr := h.stack.rodata
  have ha := h.stack.aligned
  rw [hK] at hm hn hr
  refine ⟨?_, ?_, ha⟩ <;> addr_omega [hm, hn, hr]

/-- What the push writes before its `grow_amortized`. -/
def CallW (s u : MachineState) (nx x : Word) : Prop :=
  Within x (s.getReg .x11) 8 ∨ Within x (stackLo s extendStack) (extendStack - 104) ∨
    Within x nextAddr 8 ∨ (heapNext u ≤ x.toNat ∧ x.toNat < nx.toNat)

/-- Claim `k`'s placement's `variables` and `index`. -/
def varsAt (s : MachineState) (k : Nat) : Nat := (s.getMem (plAt s k + 8)).toNat
def idxAt (s : MachineState) (k : Nat) : Word := s.getMem (plAt s k + 16)

/-- At `0x80009d08`, `selector_point` returned. -/
structure AfterSel (s u t : MachineState) (k : Nat) : Prop where
  pc : t.pc = 0x80009d08
  sp : t.getReg .x2 = s.getReg .x2 - 240
  keep : ∀ r ∈ [Reg.x8, .x9, .x19, .x20, .x21, .x22, .x23, .x24], t.getReg r = u.getReg r
  x18 : t.getReg .x18 = clAt s k
  x25 : t.getReg .x25 = clAt s (k + 1)
  x26 : t.getReg .x26 = s.getMem (clAt s k + 8)
  x27 : t.getReg .x27 = s.getMem (clAt s k + 16)
  heap : HeapOk t
  mono : heapNext u ≤ heapNext t
  fr : DFrame u t (CallW s u (t.getMem nextAddr))
  sel : vecEs t (s.getReg .x2 - 160) =
    Model.selectorPointRust (idxAt s k >>> (varsAt s k % 64)) (stackLogAt s - varsAt s k)
  selLen : (vecLen t (s.getReg .x2 - 160)).toNat = stackLogAt s - varsAt s k
  selBuf : NewBuf u t (vecPtr t (s.getReg .x2 - 160)) (24 * (vecLen t (s.getReg .x2 - 160)).toNat) 8

theorem vars_le {s : MachineState} {k : Nat} (hpre : Walk.ExtendPreE s) (hcol : colAt s k < placementsLen s)
    (hbit : s.getMem (plAt s k) &&& 1 ≠ 0) : varsAt s k ≤ stackLogAt s := by
  have hmem : placementAt s (plAt s k) ∈ placementsAt s (placementsPtr s) (placementsLen s) :=
    List.mem_map.mpr ⟨colAt s k, List.mem_range.mpr hcol, rfl⟩
  exact hpre.within _ hmem ⟨varsAt s k, idxAt s k⟩ (by simp only [placementAt, hbit, ite_false]; rfl)

theorem sel_step (hS : MultilinearContracts.SelectorSpec) {s u : MachineState} {k : Nat} (hpre : Walk.ExtendPreE s)
    (hp : Push s u k) : ∃ t, Reaches Image.code u t ∧ (Dead Image.code t ∨ AfterSel s u t k) := by
  have hI := hp.inv
  have hk := hp.lt
  have hcol := hp.col
  have hf := facts hpre (by omega)
  have hCb := Region.bounds hf.claims
  have hLb := Region.bounds hf.layout
  have hPR := pl_region hpre hcol
  have hPb := Region.bounds hPR
  have hIt := hpre.iter
  have hItb := Region.bounds hIt.region
  have hItf := hIt.free
  simp only [Outside] at hItf
  have hb := sbounds hpre
  have hst := hpre.stack
  have hsp : u.getReg .x2 = s.getReg .x2 - 240 := hI.p.sp
  have rP8 : u.getMem (plAt s k + 8) = s.getMem (plAt s k + 8) :=
    hI.read hpre.placements hpre.placementsOff (by simp only [plAt]; addr_omega [hPb, hcol])
      (by simp only [plAt]; addr_omega [hPb, hcol])
  have rP16 : u.getMem (plAt s k + 16) = s.getMem (plAt s k + 16) :=
    hI.read hpre.placements hpre.placementsOff (by simp only [plAt]; addr_omega [hPb, hcol])
      (by simp only [plAt]; addr_omega [hPb, hcol])
  have rC8 : u.getMem (clAt s k + 8) = s.getMem (clAt s k + 8) :=
    hI.read hpre.claims hpre.claimsOff (by addr_omega [hCb, hk]) (by addr_omega [hCb, hk])
  have rC16 : u.getMem (clAt s k + 16) = s.getMem (clAt s k + 16) :=
    hI.read hpre.claims hpre.claimsOff (by addr_omega [hCb, hk]) (by addr_omega [hCb, hk])
  have rL := rd_layout hpre hf hI (o := 184) (by decide)
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80009cdc_spec hp.pc (by
    rv_eval [hp.x18, hI.x8, hI.x20, hp.x13]
    and_intros <;> first
      | exact Region.valid hIt.region (by addr_omega [hItb]) (by addr_omega [hItb])
          (by addr_omega [hItb])
      | exact Region.valid hf.claims (by addr_omega [hCb, hk]) (by addr_omega [hCb, hk])
          (by addr_omega [hCb, hk])
      | exact Region.valid hf.layout (by addr_omega [hLb]) (by addr_omega [hLb])
          (by addr_omega [hLb])
      | exact Region.valid hPR (by simp only [plAt]; addr_omega [hPb, hcol])
          (by simp only [plAt]; addr_omega [hPb, hcol]) (by simp only [plAt]; addr_omega [hPb, hcol]))
  have k₁ := b80009cdc_keeps h₁
  have hf₁ := DFrame.of_memFrame (b80009cdc_frame h₁ (by rw [hI.x8]; addr_omega [hItb]))
  rw [hI.x8] at hf₁
  have hn₁ : t₁.getMem nextAddr = u.getMem nextAddr :=
    hf₁.word (fun x hx hw ↦ by addr_omega [hx, hw, hItf.2]) (by decide)
  have hsp₁ : t₁.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 240 := (k₁ .x2 (by decide)).trans hsp
  have hheap₁ : HeapOk t₁ := by
    have := hI.p.heap hpre.heap
    exact ⟨by simp only [heapNext, hn₁]; exact this.lo, by simp only [heapNext, hn₁]; exact this.hi⟩
  have x10₁ : t₁.getReg .x10 = s.getReg .x2 - 160 := by
    rw [b80009cdc_x10 h₁, hsp]; addr_omega [hb]
  have x11₁ := h₁.reg .x11 rfl
  have x12₁ := b80009cdc_x12 h₁
  rv_eval [] at x11₁
  rw [hp.x13, rP16, rP8] at x11₁
  rw [hI.x20, hp.x13, rL, rP8] at x12₁
  have hle := vars_le hpre hcol hp.bit
  have x12n : (t₁.getReg .x12).toNat = stackLogAt s - varsAt s k := by
    rw [x12₁, BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact hle)]; rfl
  have hsl : stackLo t₁ MultilinearContracts.selectorStack = s.getReg .x2 - 352 := by
    simp only [stackLo, hsp₁]; addr_omega [hb]
  have hpreS : MultilinearContracts.SelectorPre t₁ := {
    heap := hheap₁
    out := by
      rw [x10₁]
      exact ValidMemRange.sub hst.valid (by rw [hK]; addr_omega [hb]) (by rw [hK]; addr_omega [hb])
        (by rw [hK]; addr_omega [hb])
    stack := hst.sub 240 hsp₁ (by decide) (by decide) (by decide) (by decide) (by decide)
    outFree := by rw [x10₁]; simp only [Outside]; exact ⟨Or.inr (by addr_omega [hb]), by addr_omega [hb]⟩
    outStack := by rw [x10₁, hsl]; addr_omega [hb] }
  obtain ⟨t₂, hr₂, ⟨hpc₂, hpres₂, hpost₂⟩ | hdead⟩ := hS.call hr₁ (b80009cdc_pc h₁) hpreS
  swap
  · exact ⟨t₂, hr₂, Or.inl hdead⟩
  have kp (r : Reg) (hr : r ∈ calleeSaved) : t₂.getReg r = t₁.getReg r := hpres₂ r hr
  have hlen := hpost₂.len
  have hel := hpost₂.elems
  rw [x10₁] at hlen hel
  have hfr₂ := DFrame.of_byteFrame hpost₂.frame
  rw [x10₁, hsl] at hfr₂
  have hn₂ := hpost₂.heap.hi
  have hmono : heapNext u ≤ heapNext t₂ := by
    have := hpost₂.mono; simp only [heapNext, hn₁] at this ⊢; exact this
  refine ⟨t₂, hr₂, Or.inr ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hpost₂.heap, hmono, ?_, ?_, ?_, ?_⟩⟩
  · rw [hpc₂, returnAddress_eq, b80009cdc_x1 h₁]; decide
  · rw [kp .x2 (by decide), hsp₁]; rfl
  · intro r hr
    rw [kp r ((by decide : [Reg.x8, .x9, .x19, .x20, .x21, .x22, .x23, .x24] ⊆ calleeSaved) hr)]
    exact keeps_sub k₁ (by decide) r hr
  · rw [kp .x18 (by decide), k₁ .x18 (by decide), hp.x18]
  · rw [kp .x25 (by decide), k₁ .x25 (by decide), hp.x25]
  · rw [kp .x26 (by decide), b80009cdc_x26 h₁, hp.x18, rC8]
  · rw [kp .x27 (by decide), b80009cdc_x27 h₁, hp.x18, rC16]
  · have hnx : (t₂.getMem nextAddr).toNat = heapNext t₂ := rfl
    refine (hf₁.mono (w' := CallW s u (t₂.getMem nextAddr)) fun a ha ↦ Or.inl ha).trans hfr₂
      fun a ha ↦ ?_
    rcases ha with ha | ha | ha | ha
    · exact Or.inr (Or.inl (by rw [hK]; addr_omega [ha, hb]))
    · exact Or.inr (Or.inl (by rw [hK]; addr_omega [ha, hb]))
    · exact Or.inr (Or.inr (Or.inl ha))
    · simp only [Fresh, heapNext, hn₁] at ha
      exact Or.inr (Or.inr (Or.inr ⟨ha.1, by rw [hnx]; exact ha.2⟩))
  · rw [hel, x11₁, x12n]; rfl
  · rw [hlen, x12n]
  · have := hpost₂.fresh
    rw [x10₁] at this
    rw [hlen]
    simp only [NewBuf, heapNext, hn₁] at this ⊢
    exact this

end Rv64Verifier.Proofs.Pcs.Extend
