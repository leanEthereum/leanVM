import Rv64Verifier.Proofs.Walk.R17A
import Rv64Verifier.Proofs.Bus.TsStart

/-!
# `walk` R17, `powers` and `dot`

`powers(xi, n_constraints + 3)` into `S - 1872`, its length checked, the split at
`n_constraints`, `dot(form_powers, bus.totals)` into `S - 1704` (`target`), to `0x8000375c`.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Compile Rv64Verifier.Runtime Rv64Verifier.Model
  Rv64Verifier.Transcript Rv64Verifier.Blocks.F4 Rv64Verifier.MultilinearContracts
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- The frame bytes R17 writes up to `table_sumcheck`'s arguments. -/
def W17b (s : MachineState) (a : Word) : Prop :=
  W17a s a ∨ Within a (s.getReg .x2 - 1872) 24 ∨ Within a (s.getReg .x2 - 1704) 24

theorem W17b_ok {s u₀ v : MachineState} (hpre : WalkPre s) (h : Rest s u₀ v) {a : Word}
    (ha : W17b s a) : InF s a ∧ ¬ KeepR s u₀ a := by
  rcases ha with ha | ha | ha
  · exact W17a_ok hpre h ha
  · exact range_ok hpre h (c := 1872) (k := 1872) (n := 24) rfl (by omega) (by omega) ha
  · exact range_ok hpre h (c := 1704) (k := 1704) (n := 24) rfl (by omega) (by omega) ha

/-- At `0x8000375c`: `xi`'s powers at `PP`, `target` at `S - 1704`. -/
structure PreArgs (s u₀ v : MachineState) (bus : BusResultRust) (PP : Word) : Prop where
  rest : Rest s u₀ v
  st : StepW s u₀ v (W17b s) True
  x9 : v.getReg .x9 = s.getReg .x2 - 1704
  x18 : v.getReg .x18 = PP
  x20 : v.getReg .x20 = 3
  x24 : v.getReg .x24 = 2
  x26 : v.getReg .x26 = PP + 48
  x22 : v.getReg .x22 = u₀.getMem (s.getReg .x2 - 864)
  regs : ∀ r ∈ ([.x19, .x21, .x25, .x27] : List Reg), v.getReg r = u₀.getReg r
  m184 : v.getMem (s.getReg .x2 - 2472) = u₀.getMem (s.getReg .x2 - 920)
  m56 : v.getMem (s.getReg .x2 - 2600) = u₀.getMem (s.getReg .x2 - 840)
  m64 : v.getMem (s.getReg .x2 - 2592) = u₀.getMem (s.getReg .x2 - 848)
  m160 : v.getMem (s.getReg .x2 - 2496) = u₀.getMem (s.getReg .x2 - 872)
  pp : NewBuf u₀ v PP 120 8
  powers : eListAt v PP 5 = LeanVM.Protocol.Verifier.powers (eAt v (s.getReg .x2 - 152)) 5
  target : eAt v (s.getReg .x2 - 1704) = dotRust (eListAt v (PP + 48) 3) bus.totals
  sample : ∀ T, TranscriptAt u₀ (tp s) T → ∃ T', TM.sample.run T =
    some (eAt v (s.getReg .x2 - 152), T') ∧ TranscriptAt v (tp s) T'

set_option maxRecDepth 8192 in
theorem r17b (hP : PowersSpec) (hDt : DotSpec) {OI : MachineState → Word → List (List Opening) → Prop}
    {s u₀ u : MachineState} {layout : LayoutMirror.LayoutRust} {rows : List (BitVec 64)}
    {lir : BitVec 64} {bus : BusResultRust} (hpre : WalkPre s)
    (h : AtR17 OI s u₀ layout rows lir bus) (hpc : u.pc = 0x80007dfc) (P : PrePowers s u₀ u) :
    ∃ v, Reaches Image.code u v ∧
      ((v.pc = 0x8000375c ∧ ∃ PP, PreArgs s u₀ v bus PP) ∨ Dead Image.code v) := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  have I := P.rest.inv
  have R₀' := Rest.of h.inv
  have sp := I.sp
  -- `powers`
  have pre₁ : PowersPre u := {
    heap := I.heap
    out := by rw [P.x10]; valid_sub hval [hb1]
    base := by rw [P.x11]; valid_sub hval [hb1]
    stack := hpre.stack.sub 2656 sp (by rw [stack_eq]; decide) (by decide) (by decide)
      (by decide) (by decide)
    outFree := by rw [P.x10]; exact (fr_ok hpre I (c := 1872) (k := 1872) (n := 24) (m := 0) rfl (by omega) (by omega)
      (by omega)).1
    outStack := by rw [P.x10]; exact (fr_ok hpre I (c := 1872) (k := 1872) (n := 24) rfl (by omega) (by omega)
      (by decide)).2.1
    outRodata := by rw [P.x10]; exact (fr_ok hpre I (c := 1872) (k := 1872) (n := 24) (m := 0) rfl (by omega) (by omega)
      (by omega)).2.2
    baseFree := by rw [P.x11]; exact (fr_ok hpre I (c := 152) (k := 152) (n := 24) (m := 0) rfl (by omega) (by omega)
      (by omega)).1
    baseStack := by rw [P.x11]; exact (fr_ok hpre I (c := 152) (k := 152) (n := 24) rfl (by omega) (by omega)
      (by decide)).2.1
    baseOut := by rw [P.x11, P.x10]; addr_omega [hb1]
    rodata := I.rodata hpre }
  obtain ⟨v₁, hr₁, ⟨hpc₁, hp₁, post₁⟩ | hd⟩ := hP.call (Reaches.refl u) hpc pre₁
  swap
  · exact ⟨v₁, hr₁, Or.inr hd⟩
  have fr₁ := post₁.frame
  have st₁ : StepW s u v₁ (fun a ↦ Within a (s.getReg .x2 - 1872) 24) False :=
    StepW.ofCall hpre I (m := powersStack) (by decide)
      (fun a ha ↦ fr₁ a fun i hi hw ↦ ha i hi (by simpa only [PowersW, P.x10] using hw))
      post₁.heap post₁.mono (hp₁ .x2 (by decide))
  have R₁ := P.rest.stepW hpre (fun a ha ↦ range_ok hpre P.rest (c := 1872) (k := 1872) (n := 24) rfl (by omega)
    (by omega) ha) st₁
  have sp₁ : v₁.getReg .x2 = s.getReg .x2 - 2656 := R₁.inv.sp
  have e1872 : u.getReg .x10 = s.getReg .x2 - 1872 := P.x10
  have hlen₁ : vecLen v₁ (s.getReg .x2 - 1872) = 5 := by rw [← e1872, post₁.len, P.x12]
  have hel₁ := post₁.elems
  rw [e1872, P.x11, P.x12] at hel₁
  have hfr₁ := post₁.fresh
  rw [e1872, P.x12, show 24 * (5 : Word).toNat = 120 from rfl] at hfr₁
  generalize hPPd : vecPtr v₁ (s.getReg .x2 - 1872) = PP at hfr₁
  have hPPr : Region PP (8 * 15) := NewBuf.region hfr₁ I.heap post₁.heap (by decide)
  have hPPb := hfr₁
  simp only [NewBuf] at hPPb
  have hPPn : PP.toNat + 120 ≤ heapNext v₁ := by
    rcases hPPb.2 with h0 | h0
    · exact absurd h0 (by decide)
    · exact h0.2
  -- the length check, the split
  obtain ⟨w₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000371c_spec
    (by rw [hpc₁, returnAddress_eq, P.x1]; decide) (by
      rv_eval [sp₁]; valid_access hval [hb1])
  have m₂ := b8000371c_mem_same h₂
  have e800 : v₁.getReg .x2 + 800 = s.getReg .x2 - 1872 + 16 := by
    rw [sp₁]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have e792 : v₁.getReg .x2 + 792 = s.getReg .x2 - 1872 + 8 := by
    rw [sp₁]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have x24₁ : v₁.getReg .x24 = 2 := by rw [hp₁ .x24 (by decide), P.x24]
  have hpc₂ := b8000371c_pc_not_taken h₂ (by
    rw [x24₁, e800, show v₁.getMem (s.getReg .x2 - 1872 + 16) = 5 from hlen₁]; decide)
  have k₂ := b8000371c_keeps h₂
  obtain ⟨w₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80003724_spec hpc₂ (by
      rv_eval [k₂ .x2 (by decide), sp₁]; valid_access hval [hb1])
  have m₃ := b80003724_mem_same h₃
  have k₃ := b80003724_keeps h₃
  have mm (a : Word) : w₃.getMem a = v₁.getMem a := by rw [m₃, m₂]
  have I₃ : Inv s w₃ := R₁.inv.same mm ((k₃ .x2 (by decide)).trans (k₂ .x2 (by decide)))
  have sp₃ : w₃.getReg .x2 = s.getReg .x2 - 2656 := I₃.sp
  have x10₃ : w₃.getReg .x10 = s.getReg .x2 - 1704 := by
    rw [b80003724_x10 h₃, k₂ .x2 (by decide), sp₁]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have x11₃ : w₃.getReg .x11 = PP + 48 := by
    rw [b80003724_x11 h₃, k₂ .x2 (by decide), e792, m₂, k₂ .x24 (by decide), x24₁, ← hPPd, vecPtr]
    rfl
  have x12₃ : w₃.getReg .x12 = 3 := by
    rw [b80003724_x12 h₃, b8000371c_x10 h₂, k₂ .x24 (by decide), x24₁, e800,
      show v₁.getMem (s.getReg .x2 - 1872 + 16) = 5 from hlen₁]; rfl
  have x13₃ : w₃.getReg .x13 = u₀.getMem (s.getReg .x2 - 824) := by
    rw [b80003724_x13 h₃, k₂ .x23 (by decide), hp₁ .x23 (by decide), P.x23]
  have x14₃ : w₃.getReg .x14 = u₀.getMem (s.getReg .x2 - 816) := by
    rw [b80003724_x14 h₃, k₂ .x8 (by decide), hp₁ .x8 (by decide), P.x8]
  -- the totals
  have TOT := (h.busAt).totals
  rw [show s.getReg .x2 - 928 + 96 = s.getReg .x2 - 832 by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]] at TOT
  have eTp : vecPtr u₀ (s.getReg .x2 - 832) = u₀.getMem (s.getReg .x2 - 824) := by
    rw [vecPtr]; congr 1; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have eTl : vecLen u₀ (s.getReg .x2 - 832) = u₀.getMem (s.getReg .x2 - 816) := by
    rw [vecLen]; congr 1; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have hTb := TOT.buf
  have hTl := TOT.vec.len
  have hTe := TOT.elems
  rw [eTp] at hTb
  rw [eTl] at hTl
  rw [vecEs, eTp, eTl] at hTe
  simp only [NewBuf] at hTb
  generalize u₀.getMem (s.getReg .x2 - 824) = TP' at hTb hTe x13₃
  generalize u₀.getMem (s.getReg .x2 - 816) = TL at hTl hTe x14₃
  have hTn : TL.toNat = 0 ∨ TP'.toNat % 8 = 0 ∧ heapNext s ≤ TP'.toNat ∧
      TP'.toNat + 24 * TL.toNat ≤ heapNext u₀ := by
    rcases hTb.2 with h0 | h0
    · left; have := Nat.mul_le_mul_right 24 hTl; omega
    · right; have := Nat.mul_le_mul_right 24 hTl; exact ⟨hTb.1, h0.1, by omega⟩
  -- `dot`
  have hab := hpre.stack.above
  rw [stackLo_eq] at hab
  have hhv := post₁.heap.hi
  have m₀₁ := P.rest.mono
  have m₁ := post₁.mono
  have hsl := stackLo_callee I₃ dotStack
  have hro := hpre.stack.rodata
  rw [stackLo_eq, stack_eq] at hro
  have hrs : rodataStart.toNat = 2684354560 := rfl
  have hrb : rodataBase.toNat = 2684354560 := rfl
  simp only [heapEnd, heapNext] at hab hhv m₀₁ m₁ hPPn hTn
  have pre₂ : DotPre w₃ := {
    ret := by rw [x10₃]; valid_sub hval [hb1]
    left := by
      rw [x11₃, x12₃]
      exact ValidMemRange.sub (Bus.TableSumcheck.region_range hPPr) (by addr_omega [hPPr])
        (by addr_omega [hPPr]) (by addr_omega [hPPr])
    right := by
      rw [x13₃, x14₃]
      rcases hTn with h0 | ⟨ha, h1, h2⟩
      · rw [h0]; intro i hi; omega
      · have := hpre.heap.lo
        simp only [heapNext, heapStart] at this h1 h2
        refine Bus.TableSumcheck.region_range ⟨Or.inl ⟨by omega, by omega⟩, ha⟩
    stack := calleeStack hpre I₃ (by decide) (by decide)
    retLeft := by rw [x10₃, x11₃, x12₃]; addr_omega [hb1, hab, hPPn, hhv, m₀₁, m₁]
    retRight := by
      rw [x10₃, x13₃, x14₃]
      rcases hTn with h0 | ⟨-, -, h2⟩
      · rw [h0]; simp [Apart]
      · addr_omega [hb1, hab, h2, hhv, m₀₁, m₁]
    retStack := by rw [x10₃]; exact (fr_ok hpre I₃ (c := 1704) (k := 1704) (n := 24) rfl
      (by omega) (by omega) (by decide)).2.1
    leftStack := by rw [x11₃, x12₃, hsl]; addr_omega [hb1, hab, hPPn, hhv, m₀₁, m₁]
    rightStack := by
      rw [x13₃, x14₃, hsl]
      rcases hTn with h0 | ⟨-, -, h2⟩
      · rw [h0]; simp [Apart]
      · addr_omega [hb1, hab, h2, hhv, m₀₁, m₁]
    rodata := I₃.rodata hpre
    retRodata := by rw [x10₃]; exact (fr_ok hpre I₃ (c := 1704) (k := 1704) (n := 24) (m := 0) rfl
      (by omega) (by omega) (by omega)).2.2
    stackRodata := by rw [hsl]; addr_omega [hro, hrs, hrb, hb1] }
  obtain ⟨v₂, hr₄, ⟨hpc₄, hp₄, post₂⟩ | hd⟩ := hDt.call (hr₂.trans hr₃) (b80003724_pc h₃) pre₂
  swap
  · exact ⟨v₂, hr₁.trans hr₄, Or.inr hd⟩
  have hx := hpre.stack.next
  rw [stackLo_eq, stack_eq] at hx
  have fr₂ : ∀ a, ¬ Within a (s.getReg .x2 - 1704) 24 → ¬ Within a (stackLo w₃ dotStack) dotStack →
      v₂.getMem a = w₃.getMem a := by rw [← x10₃]; exact post₂.frame
  have hn₂ : heapNext v₂ = heapNext w₃ := by
    simp only [heapNext]
    rw [fr₂ _ (by addr_omega [hb1, hx]) (by rw [hsl]; addr_omega [hb1, hx])]
  have st₂ : StepW s w₃ v₂ (Within · (s.getReg .x2 - 1704) 24) False :=
    ⟨fun a ha ↦ fr₂ a (fun hw ↦ ha 0 (by decide) (Or.inl (by rw [add_ofNat_zero]; exact hw)))
      (fun hw ↦ ha 0 (by decide) (Or.inr (Or.inl (by
        rw [add_ofNat_zero]; rw [hsl] at hw; addr_omega [hw, hb1])))),
      ⟨hn₂ ▸ I₃.heap.lo, hn₂ ▸ I₃.heap.hi⟩, hn₂.ge, hp₄ .x2 (by decide)⟩
  have R₃ : Rest s u₀ w₃ := R₁.same mm ((k₃ .x2 (by decide)).trans (k₂ .x2 (by decide)))
  have R₄ := R₃.stepW hpre (fun a ha ↦ range_ok hpre R₃ (c := 1704) (k := 1704) (n := 24) rfl
    (by omega) (by omega) ha) st₂
  have sm₁₃ : StepW s v₁ w₃ (fun _ ↦ False) False :=
    StepW.same post₁.heap mm ((k₃ .x2 (by decide)).trans (k₂ .x2 (by decide))) _ _
  have stB := (st₁.trans sm₁₃).trans st₂
  have fB : ∀ a, ((Within a (s.getReg .x2 - 1872) 24 ∨ False) ∨ Within a (s.getReg .x2 - 1704) 24) →
      InF s a := fun a ha ↦ by
    rcases ha with (ha | ha) | ha
    · exact (range_ok hpre R₁ (c := 1872) (k := 1872) (n := 24) rfl (by omega) (by omega) ha).1
    · exact ha.elim
    · exact (range_ok hpre R₁ (c := 1704) (k := 1704) (n := 24) rfl (by omega) (by omega) ha).1
  have gB (k : Nat) (hk : 2400 ≤ k ∧ k ≤ 2656) : v₂.getMem (s.getReg .x2 - BitVec.ofNat 64 k) =
      u.getMem (s.getReg .x2 - BitVec.ofNat 64 k) :=
    stB.getF hpre (by addr_omega [hb1, hk]) (fun i hi hw ↦ by
        rcases hw with (hw | hw) | hw
        · addr_omega [hw, hi, hb1, hk]
        · exact hw
        · addr_omega [hw, hi, hb1, hk])
      fun hf ↦ ((hf.elim (fun h' ↦ h'.elim id id) id)).elim
  have hl3 : (vecLen v₁ (s.getReg .x2 - 1872)).toNat = 5 := by rw [hlen₁]; rfl
  have hTL : TL.toNat = 3 := by
    have := post₂.len; rw [x12₃, x14₃] at this; rw [← this]; rfl
  have fW' : ∀ a, W17a s a → InF s a := fun a ha ↦ (W17a_ok hpre R₀' ha).1
  have hTn' : TP'.toNat + 72 ≤ heapNext u₀ := by
    rcases hTn with h0 | ⟨-, -, h2⟩
    · omega
    · rw [hTL] at h2; exact h2
  have e152 : eAt v₂ (s.getReg .x2 - 152) = eAt u (s.getReg .x2 - 152) :=
    stB.eAtF hpre (by addr_omega [hb1]) (fun i hi hw ↦ by
        rcases hw with (hw | hw) | hw
        · addr_omega [hw, hi, hb1]
        · exact hw
        · addr_omega [hw, hi, hb1])
      fun hf ↦ ((hf.elim (fun h' ↦ h'.elim id id) id)).elim
  have etp : tp s = s.getReg .x2 - BitVec.ofNat 64 2448 := rfl
  have ptrR {v : MachineState} (R : Rest s u₀ v) : v.getMem (tp s) = s.getReg .x13 := by
    rw [etp, R.get (keep_slot hpre (by omega)), ← etp]; exact h.proofPtr
  have tpW : ∀ {k : Nat}, (k = 1872 ∨ k = 1704) → ∀ a, Within a (s.getReg .x2 - BitVec.ofNat 64 k) 24 →
      InF s a ∧ ¬ Within a (tp s) 368 := by
    intro k hk a ha
    refine ⟨?_, ?_⟩
    · simp only [InF]; rcases hk with rfl | rfl <;> constructor <;> addr_omega [ha, hb1]
    · rw [tp]; rcases hk with rfl | rfl <;> addr_omega [ha, hb1]
  refine ⟨v₂, hr₁.trans hr₄, Or.inl ⟨by rw [hpc₄, returnAddress_eq, b80003724_x1 h₃]; decide, PP, {
    rest := R₄
    st := (P.st.trans stB).weaken (fun a ha ↦ by
        rcases ha with ha | ((ha | ha) | ha)
        · exact Or.inl ha
        · exact Or.inr (Or.inl ha)
        · exact ha.elim
        · exact Or.inr (Or.inr ha)) fun _ ↦ trivial
    x9 := by
      rw [hp₄ .x9 (by decide), b80003724_x9 h₃, k₂ .x2 (by decide), sp₁]
      apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
    x18 := by
      rw [hp₄ .x18 (by decide), b80003724_x18 h₃, k₂ .x2 (by decide), e792, m₂, ← hPPd]; rfl
    x20 := by rw [hp₄ .x20 (by decide), b80003724_x20 h₃, ← b80003724_x12 h₃, x12₃]
    x24 := by rw [hp₄ .x24 (by decide), k₃ .x24 (by decide), k₂ .x24 (by decide), x24₁]
    x26 := by rw [hp₄ .x26 (by decide), b80003724_x26 h₃, ← b80003724_x11 h₃, x11₃]
    x22 := by
      rw [hp₄ .x22 (by decide), k₃ .x22 (by decide), k₂ .x22 (by decide), hp₁ .x22 (by decide), P.x22]
    regs := fun r hr ↦ by
      have hr' := P.regs r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;>
      rw [hp₄ _ (by decide), k₃ _ (by decide), k₂ _ (by decide), hp₁ _ (by decide), hr']
    m184 := by rw [show (2472 : Word) = BitVec.ofNat 64 2472 from rfl, gB 2472 (by omega)]; exact P.m184
    m56 := by rw [show (2600 : Word) = BitVec.ofNat 64 2600 from rfl, gB 2600 (by omega)]; exact P.m56
    m64 := by rw [show (2592 : Word) = BitVec.ofNat 64 2592 from rfl, gB 2592 (by omega)]; exact P.m64
    m160 := by rw [show (2496 : Word) = BitVec.ofNat 64 2496 from rfl, gB 2496 (by omega)]; exact P.m160
    pp := by
      have a1 := P.rest.mono
      have a2 : heapNext v₁ ≤ heapNext v₂ := by rw [hn₂]; simp only [heapNext, mm]; exact le_refl _
      simp only [NewBuf] at hPPb ⊢
      refine ⟨hPPb.1, Or.inr ⟨?_, ?_⟩⟩ <;> rcases hPPb.2 with h0 | h0 <;> omega
    powers := by
      have e1 : eListAt v₁ PP 5 = LeanVM.Protocol.Verifier.powers (eAt u (s.getReg .x2 - 152)) 5 := by
        have := hel₁; rw [vecEs, hPPd, hl3] at this; exact this
      rw [(sm₁₃.trans st₂).eListH hpre (fun a ha ↦ by
          rcases ha with ha | ha
          · exact ha.elim
          · exact (tpW (Or.inr rfl) a ha).1) (by simp only [heapNext]; omega), e1, e152]
    target := by
      have hv := post₂.value
      rw [x10₃, x11₃, x12₃, x13₃] at hv
      rw [hv, st₂.eListH hpre (fun a ha ↦ (tpW (Or.inr rfl) a ha).1)
        (by simp only [heapNext]; rw [mm]; addr_omega [hPPn])]
      congr 1
      rw [show ((3 : Word)).toNat = 3 from rfl, (P.st.trans (st₁.trans sm₁₃)).eListH hpre
        (fun a ha ↦ by
          rcases ha with ha | ha | ha
          · exact fW' a ha
          · exact (tpW (Or.inl rfl) a ha).1
          · exact ha.elim) (by omega), ← hTL]
      exact hTe
    sample := fun T hT ↦ by
      obtain ⟨T', e, hT'⟩ := P.sample T hT
      refine ⟨T', by rw [e, e152], ?_⟩
      exact st₂.transcript hpre I₃ (ptrR R₃) (fun a ha ↦ tpW (Or.inr rfl) a ha)
        (TranscriptAt.same hpre R₁.inv (ptrR R₁) mm
          (st₁.transcript hpre I (ptrR P.rest) (fun a ha ↦ tpW (Or.inl rfl) a ha) hT')) }⟩⟩

end Rv64Verifier.Proofs.Walk
