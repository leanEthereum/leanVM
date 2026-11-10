import Rv64Verifier.Proofs.Bus.VbbTail37

/-!
# `verify_bus_balance`'s side loop: the tables' selectors' loop

The loop at `0x8000767c`, as the framework's (`selIter`) with the buffer in `s4` and the count at
`S - 1296` (`SelI2`, `selIter2`, `selLoop2`).
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F26
  Rv64Verifier.MultilinearContracts
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- At `0x8000767c` with `k` of `cnt` selectors stored from `P`. -/
structure SelI2 (s z h u₁ u : MachineState) (L P pp pl : Word) (point : List E)
    (cnt k : Nat) : Prop where
  cur : Cur s z h u
  fr : DFrame u₁ u fun a ↦ SelW s h u a ∨ Within a (s.getReg .x2 - 1296) 8
  regs : ∀ r ∈ ([.x2, .x8, .x18, .x22, .x24, .x25, .x26] : List Reg), u.getReg r = u₁.getReg r
  x9 : u.getReg .x9 = h.getMem (L + 8) + BitVec.ofNat 64 (16 * k + 8)
  x23 : u.getReg .x23 = h.getMem (L + 8) + BitVec.ofNat 64 (16 * cnt + 8)
  x19 : u.getReg .x19 = P + BitVec.ofNat 64 (24 * k)
  x20 : u.getReg .x20 = P
  x21 : u.getReg .x21 = pl
  x27 : u.getReg .x27 = pp
  buf : P.toNat % 8 = 0 ∧ heapNext h ≤ P.toNat ∧ P.toNat + 24 * cnt ≤ heapNext u
  vals : eListAt u P k = ((placementsAt h L).take k).map (·.eqAbove point)
  m48 : u.getMem (s.getReg .x2 - 1296) = BitVec.ofNat 64 cnt

set_option maxRecDepth 8192 in
/-- One iteration of the tables' selectors loop. -/
theorem selIter2 (hEA : EqAboveSpec) {s z h u₁ u : MachineState} {L P pp pl : Word}
    {point : List E} {cnt k : Nat} (hpre : BusBalancePre s) (hsz : heapNext s ≤ heapNext z)
    (Ih : Inv s h) (hzh : heapNext z ≤ heapNext h) (PA : PointAt z h pp pl point)
    (hcnt : (h.getMem (L + 16)).toNat = cnt)
    (hF : LowBuf (h.getMem (L + 8)) (16 * cnt) (heapNext z))
    (S : SelI2 s z h u₁ u L P pp pl point cnt k) (hk : k < cnt) (hpc : u.pc = 0x8000767c) :
    ∃ w, Reaches Image.code u w ∧ (Dead Image.code w ∨ SelI2 s z h u₁ w L P pp pl point cnt (k + 1) ∧
      ((k + 1 < cnt ∧ w.pc = 0x8000767c) ∨ (k + 1 = cnt ∧ w.pc = 0x800076bc))) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  have hab := hpre.stack.above
  have hnx := hpre.stack.next
  rw [stackLo_eq] at hab hnx
  have Iu := S.cur.inv
  have spv : u.getReg .x2 = s.getReg .x2 - 1344 := Iu.sp
  have hhu := S.cur.step.mono
  have huE := Iu.heap.hi
  obtain ⟨F8, hFb⟩ := hF
  have hFl : heapStart ≤ (h.getMem (L + 8)).toNat ∧ (h.getMem (L + 8)).toNat + 16 * cnt ≤ heapNext z := by
    rcases hFb with h0 | h0
    · omega
    · exact h0
  obtain ⟨P8, hPh, hPu⟩ := S.buf
  have hvF : ValidMemRange (h.getMem (L + 8)) (2 * cnt) :=
    heapRange F8 hFl.1 (by simp only [heapNext, heapEnd] at hFl hzh hhu huE ⊢; omega)
  have hvP : ValidMemRange P (3 * cnt) :=
    heapRange P8 (le_trans Ih.heap.lo (le_trans (le_refl _) hPh))
      (by simp only [heapNext, heapEnd] at hPu huE ⊢; omega)
  simp only [heapNext, heapEnd, heapStart] at hFl hzh hhu huE hPh hPu hab
  have x9 := S.x9
  have x23 := S.x23
  have x19 := S.x19
  generalize hFg : h.getMem (L + 8) = F at hFl hvF F8 x9 x23
  -- `0x8000767c`
  obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000767c_spec hpc (by
    rv_eval [x9]
    and_intros <;> valid_access hvF [hFl, hk, hzh, hhu, huE])
  have m₂ := b8000767c_mem_same h₂
  have k₂ := b8000767c_keeps h₂
  have hn₂ : heapNext u₂ = heapNext u := by simp only [heapNext, m₂]
  have C₂ : Cur s z h u₂ := S.cur.next hpre hsz (A := fun _ ↦ False)
    (StepS.same m₂ Iu.heap (k₂ .x2 (by decide))) fun _ h ↦ h.elim
  have e9 : u.getReg .x9 - 8 = F + BitVec.ofNat 64 (16 * k) := by
    rw [x9]; apply BitVec.eq_of_toNat_eq; addr_omega [hFl, hk, hzh, hhu, huE]
  have e9' : u.getReg .x9 = F + BitVec.ofNat 64 (16 * k) + 8 := by
    rw [x9]; apply BitVec.eq_of_toNat_eq; addr_omega [hFl, hk, hzh, hhu, huE]
  have rdF (j : Nat) (hj : j + 8 ≤ 16) : u.getMem (F + BitVec.ofNat 64 (16 * k) + BitVec.ofNat 64 j) =
      h.getMem (F + BitVec.ofNat 64 (16 * k) + BitVec.ofNat 64 j) :=
    S.cur.low hpre Ih (by simp only [heapNext]; omega) (by simp only [heapStart]; addr_omega [hFl, hk, hj])
      (by simp only [heapNext]; addr_omega [hFl, hk, hj])
  have x11₂ : u₂.getReg .x11 = h.getMem (F + BitVec.ofNat 64 (16 * k)) := by
    rw [b8000767c_x11 h₂, e9]; simpa using rdF 0 (by omega)
  have x12₂ : u₂.getReg .x12 = h.getMem (F + BitVec.ofNat 64 (16 * k) + 8) := by
    rw [b8000767c_x12 h₂, e9']; exact rdF 8 (by omega)
  have x13₂ : u₂.getReg .x13 = pp := by rw [b8000767c_x13 h₂, S.x27]
  have x14₂ : u₂.getReg .x14 = pl := by rw [b8000767c_x14 h₂, S.x21]
  have pl8 := PA.p8
  have plb := PA.lo
  have plh := PA.hi
  -- `eq_above`
  obtain ⟨v, hrv, ⟨hpcv, hpv, Cv, frv, hmv, hEv⟩ | hd⟩ := eqAboveC hEA hpre hsz C₂ (Reaches.refl _)
    (b8000767c_pc h₂) (by rw [b8000767c_x10 h₂, spv]; rv_eval [])
    (by rw [x13₂]; exact pl8)
    (by rw [x13₂, x14₂]; exact plb)
    (by rw [x13₂, x14₂]; simp only [heapNext] at hn₂ plh ⊢; omega)
  swap
  · exact ⟨v, hr₂.trans hrv, Or.inl hd⟩
  rw [x11₂, x12₂, x13₂, x14₂, (PA.at hpre C₂ Ih (by simp only [heapNext]; omega))] at hEv
  have Iv := Cv.inv
  have spv' : v.getReg .x2 = s.getReg .x2 - 1344 := Iv.sp
  have x19v : v.getReg .x19 = P + BitVec.ofNat 64 (24 * k) := by
    rw [hpv.reg .x19, k₂ .x19 (by decide), x19]
  have hvE := Iv.heap.hi
  simp only [heapNext, heapEnd] at hmv hvE hn₂
  -- `0x80007698`
  obtain ⟨w, hrw, hw⟩ := Sym.BlockSpec.reaches b80007698_spec
    (by rw [hpcv, returnAddress_eq, b8000767c_x1 h₂]; decide) (by
      rv_eval [spv', x19v]
      and_intros <;> first
        | valid_access hval [hb1]
        | valid_access hvP [hPh, hPu, hk]
        | addr_omega [hb1, hPh, hPu, hk, hab, huE, hmv, hn₂, hhu, hzh])
  have kw := b80007698_keeps hw
  have hPk : (P + BitVec.ofNat 64 (24 * k)).toNat = P.toNat + 24 * k := by
    addr_omega [hPu, huE, hk]
  have frw : DFrame v w (Within · (P + BitVec.ofNat 64 (24 * k)) 24) := by
    have := DFrame.of_memFrame (b80007698_frame hw (by rw [x19v]; addr_omega [hPu, huE, hk]))
    rw [x19v] at this; exact this
  have stw : StepS s v w (Within · (P + BitVec.ofNat 64 (24 * k)) 24) :=
    StepS.ofDFrame Iv.heap frw (fun _ h ↦ h) (fun i hi hw' ↦ by addr_omega [hw', hi, hPu, huE, hnx, hk])
      (kw .x2 (by decide))
  have hnw : heapNext w = heapNext v := by
    simp only [heapNext]; exact congrArg BitVec.toNat (frw nextAddr fun i hi hw' ↦ by
      addr_omega [hw', hi, hPu, huE, hnx, hk])
  have Cw : Cur s z h w := Cv.next hpre hsz stw fun a ha ↦ Or.inr ⟨by
      simp only [heapNext] at hzh hhu hPh ⊢; addr_omega [ha, hPk, hzh, hhu, hPh],
    by simp only [heapNext] at hnw hmv hn₂ ⊢; addr_omega [ha, hPk, hPu, hk, hnw, hmv, hn₂]⟩
  have r (x : Reg) (h2 : x ∈ ([.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x15, .x16, .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31] : List Reg))
      (hc : x ∈ calleeSaved)
      (hw2 : x ∈ ([.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x11, .x12, .x13, .x14, .x15, .x16, .x17, .x18, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31] : List Reg)) :
      w.getReg x = u.getReg x := by
    rw [kw x hw2, hpv.reg x hc, k₂ x h2]
  -- the iteration's frame
  have frIt : DFrame u w (SelW s h w) := by
    refine ((DFrame.of_same m₂ _).trans (frv.mono fun a ha ↦ ?_) fun _ h ↦ h).trans
      (frw.mono fun a ha ↦ ?_) fun _ h ↦ h
    · rcases ha with ha | ha | ha | ⟨a1, a2⟩
      · exact Or.inl ha
      · exact Or.inr (Or.inr (Or.inl ha))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by
          simp only [heapNext] at hn₂ hhu a1 ⊢; omega, by simp only [heapNext] at hnw a2 ⊢; omega⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by
          simp only [heapNext] at hhu hPh ⊢; addr_omega [ha, hPk, hhu, hPh],
          by simp only [heapNext] at hnw hmv hn₂ ⊢; addr_omega [ha, hPk, hPu, hk, hnw, hmv, hn₂]⟩)))
  have frAll : DFrame u₁ w fun a ↦ SelW s h w a ∨ Within a (s.getReg .x2 - 1296) 8 := by
    refine (S.fr.mono fun a ha ↦ ?_).trans frIt fun a ha ↦ Or.inl ha
    rcases ha with ha | ha
    · refine Or.inl ?_
      rcases ha with ha | ha | ha | ha | ⟨a1, a2⟩
      · exact Or.inl ha
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr (Or.inl ha))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨a1, by
          simp only [heapNext] at hnw hmv hn₂ a2 ⊢; omega⟩)))
    · exact Or.inr ha
  -- the elements
  have keepP (x : Word) (h1 : P.toNat ≤ x.toNat) (h2 : x.toNat + 8 ≤ P.toNat + 24 * k) :
      w.getMem x = u.getMem x := by
    rw [frw x fun i hi hw' ↦ by addr_omega [hw', hi, hPk, h1, h2, hPu, huE, hk],
      frv x fun i hi hw' ↦ by
        rcases hw' with hw' | hw' | hw' | ⟨a1, a2⟩
        · addr_omega [hw', hi, h1, h2, hPu, huE, hb1, hk]
        · addr_omega [hw', hi, h1, h2, hPu, huE, hb1, hab, hk]
        · addr_omega [hw', hi, h1, h2, hPu, huE, hnx, hk]
        · simp only [heapNext] at a1 hn₂; addr_omega [a1, hi, h1, h2, hPu, huE, hn₂, hk], m₂]
  have hold : eListAt w P k = eListAt u P k := eListAt_congr fun j hj ↦ by
    have w0 := keepP (P + BitVec.ofNat 64 (24 * j)) (by addr_omega [hPu, huE, hk, hj])
      (by addr_omega [hPu, huE, hk, hj])
    have w8 := keepP (P + BitVec.ofNat 64 (24 * j) + 8) (by addr_omega [hPu, huE, hk, hj])
      (by addr_omega [hPu, huE, hk, hj])
    have w16 := keepP (P + BitVec.ofNat 64 (24 * j) + 16) (by addr_omega [hPu, huE, hk, hj])
      (by addr_omega [hPu, huE, hk, hj])
    exact eAt_congr w0 w8 w16
  have hnew : eAt w (P + BitVec.ofNat 64 (24 * k)) = eAt v (s.getReg .x2 - 248) := by
    have e0 := b80007698_m_x19_0 hw
    have e8 := b80007698_m_x19_8 hw
    have e16 := b80007698_m_x19_16 hw
    rw [x19v, spv'] at e0 e8 e16
    rv_eval [] at e0 e8 e16
    refine eAt_congr e0 (e8.trans ?_) (e16.trans ?_) <;>
      exact congrArg v.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
  have hkL : k < (vecLen h L).toNat := by simp only [vecLen]; omega
  refine ⟨w, hr₂.trans (hrv.trans hrw), Or.inr ⟨⟨Cw, frAll, fun x hx ↦ ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ⟨P8, hPh, by simp only [heapNext] at hnw hmv hn₂ ⊢; omega⟩, ?_, ?_⟩, ?_⟩⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact (r _ (by decide) (by decide) (by decide)).trans (S.regs _ (by decide))
  · rw [b80007698_x9 hw, hpv.reg .x9, k₂ .x9 (by decide), x9, hFg]
    apply BitVec.eq_of_toNat_eq; addr_omega [hFl, hk, hzh, hhu, huE]
  · rw [r .x23 (by decide) (by decide) (by decide), S.x23]
  · rw [b80007698_x19 hw, x19v]; apply BitVec.eq_of_toNat_eq; addr_omega [hPu, huE, hk]
  · rw [r .x20 (by decide) (by decide) (by decide), S.x20]
  · rw [r .x21 (by decide) (by decide) (by decide), S.x21]
  · rw [r .x27 (by decide) (by decide) (by decide), S.x27]
  · rw [eListAt_succ, hold, S.vals, hnew, hEv, placementsAt_take_succ hkL, List.map_append]
    simp only [vecPtr, hFg, List.map_cons, List.map_nil]
  · rw [frIt _ fun i hi hw' ↦ by
      rcases hw' with hw' | hw' | hw' | hw' | ⟨a1, a2⟩
      · addr_omega [hw', hi, hb1]
      · addr_omega [hw', hi, hb1]
      · addr_omega [hw', hi, hb1]
      · addr_omega [hw', hi, hb1]
      · simp only [heapNext] at a2 hnw; addr_omega [a2, hi, hb1, hnw, hvE, hab]]
    exact S.m48
  · have x9v : v.getReg .x9 = F + BitVec.ofNat 64 (16 * k + 8) := by
      rw [hpv.reg .x9, k₂ .x9 (by decide), x9]
    have x23v : v.getReg .x23 = F + BitVec.ofNat 64 (16 * cnt + 8) := by
      rw [hpv.reg .x23, k₂ .x23 (by decide), x23]
    rcases Nat.lt_or_ge (k + 1) cnt with hlt | hge
    · refine Or.inl ⟨hlt, b80007698_pc_taken hw ?_⟩
      rw [x9v, x23v]; intro he
      have := congrArg BitVec.toNat he
      addr_omega [this, hFl, hk, hlt, hzh, hhu, huE]
    · refine Or.inr ⟨by omega, b80007698_pc_not_taken hw ?_⟩
      rw [x9v, x23v]; apply BitVec.eq_of_toNat_eq
      addr_omega [hFl, hk, hge, hzh, hhu, huE]

/-- The loop, from `k` of `cnt` to the last. -/
theorem selLoop2 (hEA : EqAboveSpec) {s z h u₁ : MachineState} {L P pp pl : Word}
    {point : List E} {cnt : Nat} (hpre : BusBalancePre s) (hsz : heapNext s ≤ heapNext z)
    (Ih : Inv s h) (hzh : heapNext z ≤ heapNext h) (PA : PointAt z h pp pl point)
    (hcnt : (h.getMem (L + 16)).toNat = cnt)
    (hF : LowBuf (h.getMem (L + 8)) (16 * cnt) (heapNext z)) :
    ∀ m k u, cnt = k + m + 1 → SelI2 s z h u₁ u L P pp pl point cnt k → u.pc = 0x8000767c →
      ∃ w, Reaches Image.code u w ∧ (Dead Image.code w ∨
        SelI2 s z h u₁ w L P pp pl point cnt cnt ∧ w.pc = 0x800076bc) := by
  intro m
  induction m with
  | zero =>
    intro k u hm S hpc
    obtain ⟨w, hr, hd | ⟨S', ⟨hlt, -⟩ | ⟨heq, hpc'⟩⟩⟩ :=
      selIter2 hEA hpre hsz Ih hzh PA hcnt hF S (by omega) hpc
    · exact ⟨w, hr, Or.inl hd⟩
    · omega
    · exact ⟨w, hr, Or.inr ⟨heq ▸ S', hpc'⟩⟩
  | succ m ih =>
    intro k u hm S hpc
    obtain ⟨w, hr, hd | ⟨S', ⟨-, hpc'⟩ | ⟨heq, -⟩⟩⟩ :=
      selIter2 hEA hpre hsz Ih hzh PA hcnt hF S (by omega) hpc
    · exact ⟨w, hr, Or.inl hd⟩
    · obtain ⟨x, hx, hd⟩ := ih (k + 1) w (by omega) S' hpc'
      exact ⟨x, hr.trans hx, hd⟩
    · omega

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
