import Rv64Verifier.Proofs.Bus.VbbTail49

/-!
# `verify_bus_balance`'s side loop: the block's form, from the head

From `0x80007984` (`Hd`) to `0x80007a08`: the coordinates' count's test, the loop's bounds at
`0x8000798c`, the loop (`coLoop`); the block's form at `S - 296` is `blockFormRust` of block `k`
(`Bf`, `coStage`).
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F26
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- At `0x80007a08`: block `k`'s form at `S - 296`, from `Hd` at `t₄`. -/
structure Bf (s z h t₀ t₄ t : MachineState) (i : Nat)
    (sd : List BusBlock × BusLayoutRust × List E × List E × E) (k : Nat) : Prop where
  cur : Cur s z h t
  fr : DFrame t₄ t (CoW s t₀ t)
  mono : heapNext t₄ ≤ heapNext t
  regs : ∀ r ∈ ([.x2, .x8, .x20, .x21, .x22, .x24, .x25, .x27] : List Reg),
    t.getReg r = t₄.getReg r
  ok : Layout.FormOk t (s.getReg .x2 - 296)
  fbuf : ∀ x, Layout.formBuf t (s.getReg .x2 - 296) x → heapNext t₀ ≤ x.toNat ∧ x.toNat < heapNext t
  form : (Layout.formOf t (s.getReg .x2 - 296)).toSpec =
    blockFormRust (blockAt s (blkAddr s i k)) sd.2.2.2.1 sd.2.2.2.2
  len : 1 ≤ (vecLen t (s.getReg .x2 - 296)).toNat

set_option maxRecDepth 8192 in
theorem coStage (hAS : Layout.AddScaledSpec) {s z h e t₀ t₄ : MachineState} {i : Nat}
    {sd : List BusBlock × BusLayoutRust × List E × List E × E} {point : List E} {P : Word}
    {n : Nat} {forms : List (List Form)} {tot : List E} {k : Nat}
    (hpre : BusBalancePre s) (hsz : heapNext s ≤ heapNext z) (Ih : Inv s h)
    (hzh : heapNext z ≤ heapNext h) (En : Entry s z h e i sd point P n)
    (B : Blk s z h e t₀ i sd point P n forms tot k)
    (hk : k < min sd.2.1.tables.length sd.1.length) (H : Hd s z h e t₀ t₄ i sd point P n k)
    (hpc : t₄.pc = 0x80007984) :
    ∃ t, Reaches Image.code t₄ t ∧ (Dead Image.code t ∨ (t.pc = 0x80007a08 ∧ Bf s z h t₀ t₄ t i sd k)) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  have C₄ := H.cur
  have I₄ := C₄.inv
  have sp₄ : t₄.getReg .x2 = s.getReg .x2 - 1344 := I₄.sp
  have hzt : heapNext z ≤ heapNext t₀ := le_trans hzh B.cur.step.mono
  -- the block, read only
  have hro0 := En.bro.blocks
  have hlen : (vecLen s (blkVec s i)).toNat = sd.1.length := by
    rw [← En.blocks, blocksAt, List.length_map, List.length_range]
  rw [hlen] at hro0
  have hkB : k < sd.1.length := lt_of_lt_of_le hk (min_le_right _ _)
  have hvB : ValidMemRange (vecPtr s (blkVec s i)) (6 * sd.1.length) :=
    Bus.RO.range (n := 6 * sd.1.length) (by rw [show 8 * (6 * sd.1.length) = 48 * sd.1.length by omega]; exact hro0)
  have hBb := hro0.bound
  have hro : FormRowsRO s busBalanceStack [(s.getReg .x10, 120)] (s.getReg .x12) (blkAddr s i k) 1 :=
    En.bro.coordinates k (by rw [hlen]; exact hkB)
  have hroF := hro.forms 0 (by omega)
  simp only [Nat.mul_zero, add_ofNat_zero] at hroF
  have hFb := hroF.bound
  have hc : (vecLen s (blkAddr s i k)).toNat < 2 ^ 60 := by
    rcases hroF.region with h0 | h0
    · omega
    · simp only [Region, Mapped] at h0; omega
  have rdB (q : Nat) (hq : q + 8 ≤ 48) : t₄.getMem (blkAddr s i k + BitVec.ofNat 64 q) =
      s.getMem (blkAddr s i k + BitVec.ofNat 64 q) :=
    I₄.word hro0 (by simp only [blkAddr]; addr_omega [hBb, hkB, hq])
      (by simp only [blkAddr]; addr_omega [hBb, hkB, hq])
  have x27₄ := H.x27
  -- the slots the loop reads
  have slotE (j : Nat) (hj : 8 ≤ j) (hj2 : j ≤ 1344) (h1 : j ≤ 1104 ∨ 1144 ≤ j)
      (h2 : j ≤ 104 ∨ 304 ≤ j) :
      t₄.getMem (s.getReg .x2 - BitVec.ofNat 64 j) = e.getMem (s.getReg .x2 - BitVec.ofNat 64 j) :=
    (H.fr _ (ItW.slot hpre C₄.inv.heap hj hj2 (blkW_miss hpre hj hj2 h1 h2))).trans
      (B.slots j hj hj2 (blkW_miss hpre hj hj2 h1 h2))
  -- `0x80007984`
  obtain ⟨t₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b80007984_spec hpc (by
    rv_eval [x27₄]; simp only [blkAddr]; valid_access hvB [hBb, hkB])
  have m₅ := b80007984_mem_same h₅
  have k₅ := b80007984_keeps h₅
  have C₅ : Cur s z h t₅ := C₄.next hpre hsz (A := fun _ ↦ False)
    (StepS.same m₅ I₄.heap (k₅ .x2 (by decide))) fun _ h ↦ h.elim
  have hn₅ : heapNext t₅ = heapNext t₄ := by simp only [heapNext, m₅]
  have eC : t₄.getMem (t₄.getReg .x27 + 16) = vecLen s (blkAddr s i k) := by
    rw [x27₄]; exact rdB 16 (by omega)
  have hcs : (blockAt s (blkAddr s i k)).coordinates.length = (vecLen s (blkAddr s i k)).toNat := by
    simp [blockAt, formVecAt]
  -- the form at `t₄`, kept through `t₅`
  have ok₅ : Layout.FormOk t₅ (s.getReg .x2 - 296) :=
    (Layout.formOf_frame (toLayoutFrame (DFrame.of_same m₅ (fun _ ↦ False))) H.ok
      (fun _ _ h ↦ h) (fun _ _ h ↦ h) (by addr_omega [hb1]) I₄.heap (by rw [hn₅])).2
  have fo₅ : Layout.formOf t₅ (s.getReg .x2 - 296) = Layout.formOf t₄ (s.getReg .x2 - 296) :=
    (Layout.formOf_frame (toLayoutFrame (DFrame.of_same m₅ (fun _ ↦ False))) H.ok
      (fun _ _ h ↦ h) (fun _ _ h ↦ h) (by addr_omega [hb1]) I₄.heap (by rw [hn₅])).1
  have fb₅ : ∀ x, Layout.formBuf t₅ (s.getReg .x2 - 296) x →
      heapNext t₀ ≤ x.toNat ∧ x.toNat < heapNext t₅ := by
    intro x hx
    simp only [Layout.formBuf, vecPtr, vecCap, m₅] at hx
    rw [hn₅]; exact H.fbuf x hx
  have len₅ : 1 ≤ (vecLen t₅ (s.getReg .x2 - 296)).toNat := by
    have := congrArg (fun f ↦ f.terms.length) (fo₅.trans H.form)
    simp only [Layout.formOf, Layout.termsOf_length, LayoutMirror.constantRust,
      LayoutMirror.FormRust.term, List.length_singleton] at this
    omega
  have form₅ : (Layout.formOf t₅ (s.getReg .x2 - 296)).toSpec = Form.const sd.2.2.2.2 := by
    rw [fo₅, H.form]; rfl
  by_cases hc0 : vecLen s (blkAddr s i k) = 0
  · have pc₅ := b80007984_pc_taken h₅ (by rw [eC, hc0])
    refine ⟨t₅, hr₅, Or.inr ⟨pc₅, C₅, (DFrame.of_same m₅ (fun _ ↦ False)).mono fun _ ha ↦ ha.elim,
      le_of_eq hn₅.symm, fun r hr ↦ k₅ r (mem_of_mem hr _), ok₅, fb₅, ?_, len₅⟩⟩
    rw [form₅]
    have : (blockAt s (blkAddr s i k)).coordinates = [] :=
      List.eq_nil_of_length_eq_zero (by rw [hcs, hc0]; rfl)
    simp [blockFormRust, this]
  have pc₅ := b80007984_pc_not_taken h₅ (by rw [eC]; exact hc0)
  have hc1 : 1 ≤ (vecLen s (blkAddr s i k)).toNat := by
    rcases Nat.eq_zero_or_pos (vecLen s (blkAddr s i k)).toNat with h0 | h0
    · exact absurd (BitVec.eq_of_toNat_eq h0) hc0
    · exact h0
  have sp₅ : t₅.getReg .x2 = s.getReg .x2 - 1344 := C₅.inv.sp
  have x10₅ : t₅.getReg .x10 = vecLen s (blkAddr s i k) := by rw [b80007984_x10 h₅, eC]
  have x27₅ : t₅.getReg .x27 = blkAddr s i k := by rw [k₅ .x27 (by decide), x27₄]
  -- `0x8000798c`
  obtain ⟨t₆, hr₆, h₆⟩ := Sym.BlockSpec.reaches b8000798c_spec pc₅ (by
    rv_eval [sp₅, x27₅]
    and_intros <;> first
      | valid_access hval [hb1]
      | (simp only [blkAddr]; valid_access hvB [hBb, hkB]))
  have m₆ := b8000798c_mem_same h₆
  have k₆ := b8000798c_keeps h₆
  have C₆ : Cur s z h t₆ := C₅.next hpre hsz (A := fun _ ↦ False)
    (StepS.same m₆ C₅.inv.heap (k₆ .x2 (by decide))) fun _ h ↦ h.elim
  have hn₆ : heapNext t₆ = heapNext t₅ := by simp only [heapNext, m₆]
  have e96 : t₅.getMem (t₅.getReg .x2 + 96) = e.getMem (s.getReg .x2 - 1248) := by
    rw [sp₅]; rv_eval []; rw [m₅]
    exact slotE 1248 (by omega) (by omega) (by omega) (by omega)
  have x9₆ : t₆.getReg .x9 = coBound (e.getMem (s.getReg .x2 - 1248)) (vecLen s (blkAddr s i k)).toNat := by
    rw [b8000798c_x9' h₆, e96, x10₅, bound_eq hc1 hc]
  have x10₆ : t₆.getReg .x10 = vecPtr s (blkAddr s i k) + 16 := by
    rw [b8000798c_x10 h₆, x27₅, m₅]; congr 1; exact rdB 8 (by omega)
  have x13₆ : t₆.getReg .x13 = e.getMem (s.getReg .x2 - 1264) := by
    rw [b8000798c_x13 h₆, sp₅]; rv_eval []; rw [m₅]
    exact slotE 1264 (by omega) (by omega) (by omega) (by omega)
  have x18₆ : t₆.getReg .x18 = e.getMem (s.getReg .x2 - 1248) + 1 := by
    rw [b8000798c_x18 h₆, sp₅]; rv_eval []; rw [m₅]
    exact (slotE 1272 (by omega) (by omega) (by omega) (by omega)).trans En.w1272
  have hn₀₄ := H.mono
  have htv : heapNext t₀ ≤ heapNext t₆ := by rw [hn₆, hn₅]; exact hn₀₄
  have fr₆ := (Layout.formOf_frame (toLayoutFrame (DFrame.of_same m₆ (fun _ ↦ False))) ok₅
      (fun _ _ h ↦ h) (fun _ _ h ↦ h) (by addr_omega [hb1]) C₅.inv.heap (by rw [hn₆]))
  have S0 : CoI s z h t₀ t₆ t₆ i sd k 0 := by
    refine ⟨C₆, DFrame.refl _ _, le_refl _, fun _ _ ↦ rfl, by simp, by simp, by simp, fr₆.2,
      fun x hx ↦ ?_, ?_, ?_⟩
    · simp only [Layout.formBuf, vecPtr, vecCap, m₆] at hx
      rw [hn₆]; exact fb₅ x hx
    · rw [fr₆.1, form₅]; rfl
    · simp only [vecLen, m₆]; exact len₅
  obtain ⟨t, hrt, hd | ⟨S, hpct⟩⟩ := coLoop hAS hpre hsz hzt htv Ih hzh En hro x10₆ x13₆ x18₆ x9₆ hc
    ((vecLen s (blkAddr s i k)).toNat - 1) 0 t₆ (by omega) S0 (Nat.zero_le _) (b8000798c_pc h₆)
  · exact ⟨t, hr₅.trans (hr₆.trans hrt), Or.inl hd⟩
  refine ⟨t, hr₅.trans (hr₆.trans hrt), Or.inr ⟨hpct, S.cur, ((DFrame.of_same m₅ _).trans
    (DFrame.of_same m₆ _) fun _ h ↦ h).trans S.fr fun _ h ↦ h, ?_, fun r hr ↦ ?_, S.ok, S.fbuf, ?_,
    S.len⟩⟩
  · have := S.mono; rw [hn₆, hn₅] at this; exact this
  · rw [S.regs r (mem_of_mem hr _), k₆ r (mem_of_mem hr _), k₅ r (mem_of_mem hr _)]
  · rw [S.form, ← hcs, coFold_all]

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
