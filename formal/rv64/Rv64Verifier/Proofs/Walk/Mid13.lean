import Rv64Verifier.Proofs.Walk.So13

/-!
# `walk`: `offsets` and `placements`' buffers (R13)

`ofAlloc`: from `0x800032c4` (`So13`), `vec![0; 165]` for `offsets` (`OF`), to the scatter loop
(`Sf13`). `plAlloc`: from its end at `0x80003334`, the bound on `kappas`' length, `stack_log`,
`q_keccak`'s index (`offsets[5]`) and `try_allocate_in(165)` for `placements` (`PL`), to the
placements' loop (`Sp13`).
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Compile Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Layout Rv64Verifier.Model.LayoutMirror
  Rv64Verifier.Blocks.F4 Rv64Verifier.MultilinearContracts
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- At the scatter loop's start, `offsets` zero. -/
structure Sf13 (OI : MachineState → Word → List (List Opening) → Prop) (s u : MachineState)
    (A : List E) (k : Nat) (R Q B : Word) (lo lo2 lo3 : Nat) (G SO OF : Word) : Prop where
  base : Base12 OI s u A k R Q B lo lo2 lo3
  gal : G.toNat % 8 = 0
  glo : lo3 ≤ G.toNat
  ghi : G.toNat + 808 ≤ SO.toNat
  gvals : ∀ i < 101, u.getMem (G + BitVec.ofNat 64 (8 * i)) = BitVec.ofNat 64 ((blk 165).getD i 0)
  soal : SO.toNat % 8 = 0
  sohi : SO.toNat + 808 ≤ OF.toNat
  sovals : ∀ i < 101, u.getMem (SO + BitVec.ofNat 64 (8 * i)) = (sol (kapPre A k 6)).getD i 0
  ofal : OF.toNat % 8 = 0
  ofhi : OF.toNat + 8 * 165 ≤ heapNext u
  sc : Sc13 u u G SO OF (sol (kapPre A k 6)) 0
  x8 : (u.getReg .x8).toNat = (stackOffsetsRust (bkl (kapPre A k 6))).2
  x20 : u.getReg .x20 = OF
  x24 : u.getReg .x24 = 165
  x18 : u.getReg .x18 = BitVec.ofNat 64 ((hts A).getD 5 0)
  x23 : u.getReg .x23 = BitVec.ofNat 64 (k - 4)
  x26 : u.getReg .x26 = BitVec.ofNat 64 ((hts A).getD 5 0 + 6)

theorem scat_zero (sol : List Word) {c : Nat} (hc : c < 165) : (scat sol 0).getD c 0 = 0 := by
  show (List.replicate 165 0#64).getD c 0 = 0
  rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  simp [hc]

set_option maxRecDepth 8192 in
/-- `offsets = vec![0; 165]`, to the scatter loop. -/
theorem ofAlloc (hTA : TryAllocZeroedSpec) {OI : MachineState → Word → List (List Opening) → Prop}
    {s u : MachineState} {A : List E} {k : Nat} {R Q B : Word} {lo lo2 lo3 : Nat} {G SO : Word}
    (hpre : WalkPre s) (hpc : u.pc = 0x800032c4) (h : So13 OI s u A k R Q B lo lo2 lo3 G SO) :
    ∃ t, Reaches Image.code u t ∧ (Dead Image.code t ∨
      (t.pc = 0x80003304 ∧ ∃ OF, Sf13 OI s t A k R Q B lo lo2 lo3 G SO OF)) := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have Bs := h.base
  have I := Bs.k11.at11.base.inv
  have sp : u.getReg .x2 = s.getReg .x2 - 2656 := I.sp
  have gl := h.glo
  have gh := h.ghi
  have sh := h.sohi
  have hl3 := Bs.lo3le
  obtain ⟨c1, c2, c3, -⟩ := Bs.kv.bounds (kapPre_ne A k (le_refl 6))
  have kb := Bs.kbelow
  simp only [heapStart] at c2
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b800032c4_spec hpc (by
    rv_eval [sp]; simp only [Sym.validAccess_eight]; and_intros <;> addr_omega [hb1, hb2, hb3])
  have m₁ := b800032c4_mem_same h₁
  have k₁ := b800032c4_keeps h₁
  have B₁ := Bs.same hpre m₁ (k₁ .x2 (by decide))
  have I₁ := B₁.k11.at11.base.inv
  have hn₁ : heapNext u₁ = heapNext u := by simp only [heapNext, m₁]
  have e1736 : s.getReg .x2 - 2656 + 1736 = s.getReg .x2 - 920 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have e1744 : s.getReg .x2 - 2656 + 1744 = s.getReg .x2 - 912 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have e1752 : s.getReg .x2 - 2656 + 1752 = s.getReg .x2 - 904 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have x10₁ : u₁.getReg .x10 = s.getReg .x2 - 928 := by
    rw [b800032c4_x10 h₁, sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have x11₁ : u₁.getReg .x11 = 165 := by rw [b800032c4_x11 h₁]; exact h.x24
  have hab := hpre.stack.above
  have hx := hpre.stack.next
  rw [stackLo_eq] at hab hx
  rw [stack_eq] at hx
  simp only [heapEnd] at hab
  have pre : TryAllocPre .x13 .x14 u₁ := {
    heap := I₁.heap
    out := by
      rw [x10₁]; exact validMemRange_of (by addr_omega [hb1, hb3]) (Or.inr ⟨by addr_omega [hb1],
        by addr_omega [hb1, hb2]⟩)
    align := by rw [b800032c4_x13 h₁]; decide
    size := by rw [b800032c4_x14 h₁]; decide
    stack := stk10 hpre I₁ (by decide) (by decide)
    outFree := by
      rw [x10₁]; exact ⟨Or.inr (by addr_omega [hab, hb1]), by simp only [Apart]; addr_omega [hx, hb1]⟩
    outStack := by rw [x10₁, stackLo_callee I₁]; simp only [Apart]; addr_omega [hb1] }
  obtain ⟨t, hr, ⟨hpct, hp, post, hzero⟩ | hd⟩ := hTA u₁ (b800032c4_pc h₁) pre
  swap
  · exact ⟨t, hr₁.trans hr, Or.inl hd⟩
  have fr := post.frame.dframe
  rw [x10₁] at fr
  have ok := post.ok
  rw [x10₁, x11₁, b800032c4_x13 h₁, b800032c4_x14 h₁] at ok
  rw [x10₁, x11₁, b800032c4_x14 h₁, b800032c4_x12 h₁] at hzero
  have hht := post.heap.hi
  have hhc := I₁.heap.hi
  have hmono := post.mono
  simp only [heapEnd] at hht hhc
  have Bt := B₁.keep hpre fr (fun a ha ↦ by
      rcases ha with ha | ha | ha | ha
      · exact Or.inl (by simp only [Within] at ha ⊢; omega)
      · rw [stackLo_callee I₁] at ha
        exact Or.inr (Or.inl (by simp only [Within, tryAllocStack] at ha ⊢; addr_omega [ha, hb1]))
      · exact Or.inr (Or.inr (Or.inl ha))
      · simp only [Fresh] at ha; exact Or.inr (Or.inr (Or.inr ⟨by rw [hn₁] at ha; omega, ha.2⟩)))
    post.heap hmono (hp .x2 (by decide))
  have keepH : ∀ p : Word, ∀ n, lo3 ≤ p.toNat → p.toNat + n ≤ heapNext u → ∀ i, 8 * i + 8 ≤ n →
      t.getMem (p + BitVec.ofNat 64 (8 * i)) = u.getMem (p + BitVec.ofNat 64 (8 * i)) :=
    fun p n hp1 hp2 i hi ↦ by
      rw [fr.getMem_of (fun x hx hw ↦ by
          simp only [Within] at hx
          rcases hw with h2 | h2 | h2 | h2
          · simp only [Within] at h2; addr_omega [hx, h2, hb1, hhc, hn₁, hp1, hp2, hi, c2, c3, kb]
          · rw [stackLo_callee I₁] at h2; simp only [Within, tryAllocStack] at h2
            addr_omega [hx, h2, hb1, hhc, hn₁, hp1, hp2, hi, c2, c3, kb]
          · simp only [Within, nextAddr] at h2; addr_omega [hx, h2, hhc, hn₁, hp1, hp2, hi, c2, c3, kb]
          · simp only [Fresh] at h2; addr_omega [hx, h2, hn₁, hp1, hp2, hi])
        (by addr_omega [hhc, hn₁, hp1, hp2, hi, c2, c3, kb]), m₁]
  have pct : t.pc = 0x800032ec := by rw [hpct, returnAddress_eq, b800032c4_x1 h₁]; decide
  have spt : t.getReg .x2 = s.getReg .x2 - 2656 := by
    rw [hp .x2 (by decide), k₁ .x2 (by decide)]; exact sp
  obtain ⟨t₁, hrt₁, ht₁⟩ := Sym.BlockSpec.reaches b800032ec_spec pct (by
    rv_eval [spt]; simp only [Sym.validAccess_eight]; addr_omega [hb1, hb2, hb3])
  have e1728 : s.getReg .x2 - 2656 + 1728 = s.getReg .x2 - 928 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  by_cases hz : t.getMem (s.getReg .x2 - 928) = 0
  swap
  · exact ⟨t₁, hr₁.trans (hr.trans hrt₁),
      Or.inl (trapAt (b800032ec_pc_taken ht₁ (by rw [spt, e1728]; exact hz)))⟩
  have pc₁ := b800032ec_pc_not_taken ht₁ (by rw [spt, e1728]; exact hz)
  obtain ⟨-, o2⟩ := ok hz
  have z := hzero (by decide) hz
  have e1320 : (165 : Word).toNat * (8 : Word).toNat = 1320 := rfl
  rw [e1320] at o2 z
  obtain ⟨OF, hOFd⟩ : ∃ OF, t.getMem (s.getReg .x2 - 928 + 16) = OF := ⟨_, rfl⟩
  rw [hOFd] at o2 z
  simp only [NewBuf] at o2
  obtain ⟨of1, of2⟩ := o2
  have of3 : heapNext u ≤ OF.toNat ∧ OF.toNat + 1320 ≤ heapNext t := by
    rcases of2 with h0 | h0
    · omega
    · rw [hn₁] at h0; exact h0
  have mt₁ := b800032ec_mem_same ht₁
  have kt₁ := b800032ec_keeps ht₁
  have spt₁ : t₁.getReg .x2 = s.getReg .x2 - 2656 := by rw [kt₁ .x2 (by decide)]; exact spt
  obtain ⟨t₂, hrt₂, ht₂⟩ := Sym.BlockSpec.reaches b800032f4_spec pc₁ (by
    rv_eval [spt₁]; simp only [Sym.validAccess_eight]; addr_omega [hb1, hb2, hb3])
  have x25t₁ : t₁.getReg .x25 = 101 := by
    rw [kt₁ .x25 (by decide), hp .x25 (by decide), k₁ .x25 (by decide)]; exact h.x25
  have pc₂ := b800032f4_pc_not_taken ht₂ (by rw [x25t₁]; decide)
  have mt₂ := b800032f4_mem_same ht₂
  have kt₂ := b800032f4_keeps ht₂
  obtain ⟨t₃, hrt₃, ht₃⟩ := Sym.BlockSpec.reaches b800032fc_spec pc₂ (by rv_eval [])
  have mt₃ := b800032fc_mem_same ht₃
  have kt₃ := b800032fc_keeps ht₃
  have m₃ (a : Word) : t₃.getMem a = t.getMem a := by rw [mt₃, mt₂, mt₁]
  have hn₃ : heapNext t₃ = heapNext t := by simp only [heapNext, m₃]
  have rg (r : Reg) (hr : r ∈ ([.x2, .x8, .x9, .x18, .x19, .x23, .x24, .x26] : List Reg)) :
      t₃.getReg r = u₁.getReg r := by
    rw [kt₃ r (by revert r hr; decide), kt₂ r (by revert r hr; decide),
      kt₁ r (by revert r hr; decide), hp r (by revert r hr; decide)]
  have rg' (r : Reg) (hr : r ∈ ([.x9, .x18, .x23, .x24, .x26] : List Reg)) :
      t₃.getReg r = u.getReg r := by
    rw [rg r (by revert r hr; decide), k₁ r (by revert r hr; decide)]
  have x20₃ : t₃.getReg .x20 = OF := by
    rw [kt₃ .x20 (by decide), b800032f4_x20 ht₂, spt₁, e1744, mt₁]
    rw [show s.getReg .x2 - 912 = s.getReg .x2 - 928 + 16 by
      apply BitVec.eq_of_toNat_eq; addr_omega [hb1]]
    exact hOFd
  have x21₁ : u₁.getReg .x21 = 101 := by rw [b800032c4_x21 h₁, sp, e1744]; exact h.hd16
  have x10₃ : t₃.getReg .x10 = BitVec.ofNat 64 (808 - 8 * 0) := by
    rw [b800032fc_x10 ht₃, kt₂ .x21 (by decide), kt₁ .x21 (by decide), hp .x21 (by decide), x21₁]
    rfl
  have x25₃ : t₃.getReg .x25 = BitVec.ofNat 64 (808 - 8 * 0) := by
    rw [b800032fc_x25 ht₃, kt₂ .x25 (by decide), x25t₁]; rfl
  have soL : lo3 ≤ SO.toNat := by omega
  refine ⟨t₃, hr₁.trans (hr.trans (hrt₁.trans (hrt₂.trans hrt₃))), Or.inr ⟨b800032fc_pc ht₃, OF, {
    base := Bt.same hpre m₃ (by rw [rg .x2 (by decide), hp .x2 (by decide)])
    gal := h.gal
    glo := gl
    ghi := gh
    gvals := fun i hi ↦ by rw [m₃, keepH G 808 gl (by omega) i (by omega)]; exact h.gvals i hi
    soal := h.soal
    sohi := by omega
    sovals := fun i hi ↦ by rw [m₃, keepH SO 808 soL sh i (by omega)]; exact h.sovals i hi
    ofal := of1
    ofhi := by rw [hn₃]; exact of3.2
    sc := {
      pc := b800032fc_pc ht₃
      lt := by decide
      x9 := by rw [rg' .x9 (by decide), h.x9]; simp
      x19 := by
        rw [rg .x19 (by decide), b800032c4_x19 h₁, sp, e1736, h.hd8]; simp
      x10 := x10₃
      x25 := x25₃
      regs := fun _ _ ↦ rfl
      fr := Layout.DFrame.refl _ _
      vals := fun c hc ↦ by
        rw [scat_zero _ hc, m₃]
        exact getMem_zero_of_bytes z of1 (by omega) (by omega) }
    x8 := by rw [rg .x8 (by decide), b800032c4_x8 h₁, sp, e1752]; exact h.hd24
    x20 := x20₃
    x24 := by rw [rg' .x24 (by decide)]; exact h.x24
    x18 := by rw [rg' .x18 (by decide)]; exact h.x18
    x23 := by rw [rg' .x23 (by decide)]; exact h.x23
    x26 := by rw [rg' .x26 (by decide)]; exact h.x26 }⟩⟩

theorem sol_length (K : List Nat) : (sol K).length = 101 := by
  rw [stackOffsetsRust_length, bkl_length]

theorem scat_ofl (K : List Nat) : scat (sol K) 101 = ofl K := by
  rw [scat_full (sol_length K)]; rfl

/-- At the placements' loop's start. -/
structure Sp13 (OI : MachineState → Word → List (List Opening) → Prop) (s u : MachineState)
    (A : List E) (k : Nat) (R Q B : Word) (lo lo2 lo3 : Nat) (OF PL : Word) : Prop where
  base : Base12 OI s u A k R Q B lo lo2 lo3
  ofal : OF.toNat % 8 = 0
  oflo : lo3 ≤ OF.toNat
  ofpl : OF.toNat + 8 * 165 ≤ PL.toNat
  ov : ∀ c < 165, u.getMem (OF + BitVec.ofNat 64 (8 * c)) = (ofl (kapPre A k 6)).getD c 0
  plal : PL.toNat % 8 = 0
  plhi : PL.toNat + 24 * 165 ≤ heapNext u
  pl0 : Pl13 u u PL OF (vecPtr u (s.getReg .x2 - 1344)) (kapPre A k 6) 0
  x8 : max 15 (u.getReg .x8).toNat = max 15 (stackOffsetsRust (bkl (kapPre A k 6))).2
  x9 : (u.getReg .x9).toNat = max 15 (u.getReg .x8).toNat
  x11 : u.getReg .x11 = 73
  x12 : u.getReg .x12 = 86
  x14 : u.getReg .x14 = 25
  x27 : u.getReg .x27 = 24
  x19 : u.getReg .x19 = (ofl (kapPre A k 6)).getD 5 0
  x21 : u.getReg .x21 = PL
  x22 : u.getReg .x22 = 165
  x24 : u.getReg .x24 = 165
  x18 : u.getReg .x18 = BitVec.ofNat 64 ((hts A).getD 5 0)
  x23 : u.getReg .x23 = BitVec.ofNat 64 (k - 4)
  x26 : u.getReg .x26 = BitVec.ofNat 64 ((hts A).getD 5 0 + 6)

set_option maxRecDepth 8192 in
/-- The scatter loop, `stack_log`, `q_keccak`'s index, `placements`' buffer. -/
theorem plAlloc (hTA : TryAllocZeroedSpec) {OI : MachineState → Word → List (List Opening) → Prop}
    {s u : MachineState} {A : List E} {k : Nat} {R Q B : Word} {lo lo2 lo3 : Nat} {G SO OF : Word}
    (hpre : WalkPre s) (h : Sf13 OI s u A k R Q B lo lo2 lo3 G SO OF) :
    ∃ t, Reaches Image.code u t ∧ (Dead Image.code t ∨
      (t.pc = 0x80003394 ∧ ∃ PL, Sp13 OI s t A k R Q B lo lo2 lo3 OF PL)) := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have Bs := h.base
  have I := Bs.k11.at11.base.inv
  have sp : u.getReg .x2 = s.getReg .x2 - 2656 := I.sp
  have gl := h.glo
  have gh := h.ghi
  have sh := h.sohi
  have oh := h.ofhi
  have hl3 := Bs.lo3le
  have hhu := I.heap.hi
  simp only [heapEnd] at hhu
  obtain ⟨c1, c2, c3, -⟩ := Bs.kv.bounds (kapPre_ne A k (le_refl 6))
  have kb := Bs.kbelow
  simp only [heapStart] at c2
  obtain ⟨t₀, hr₀, pc₀, rg₀, fr₀, vals₀⟩ := scLoop h.gal h.soal h.ofal (by omega) gh sh (by omega)
    (sol_length _) h.x24 h.x20 h.gvals h.sovals _ 0 u rfl h.sc
  rw [scat_ofl] at vals₀
  have hn₀ : heapNext t₀ = heapNext u := by
    simp only [heapNext]
    exact congrArg BitVec.toNat (fr₀ nextAddr (fun y hy hw ↦ by
      simp only [Within, nextAddr] at hy hw; addr_omega [hy, hw, oh, hhu]) (by decide))
  have hv₀ : HeapOk t₀ := ⟨hn₀ ▸ I.heap.lo, hn₀ ▸ I.heap.hi⟩
  have B₀ := Bs.keep hpre fr₀ (fun a ha ↦ by
      simp only [Within] at ha
      exact Or.inr (Or.inr (Or.inr ⟨by omega, by rw [hn₀]; omega⟩))) hv₀ hn₀.ge
    (rg₀ .x2 (by decide))
  have sp₀ : t₀.getReg .x2 = s.getReg .x2 - 2656 := by rw [rg₀ .x2 (by decide)]; exact sp
  -- `kappas.len() >= 6`, `stack_log`
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80003334_spec pc₀ (by rv_eval [])
  have pc₁ := b80003334_pc_not_taken h₁ (by rw [rg₀ .x24 (by decide), h.x24]; decide)
  have m₁ := b80003334_mem_same h₁
  have k₁ := b80003334_keeps h₁
  obtain ⟨w, hrw, pcw, mw, rgw, x9w⟩ : ∃ w, Reaches Image.code t₁ w ∧ w.pc = 0x8000334c ∧
      (∀ a, w.getMem a = t₁.getMem a) ∧
      (∀ r ∈ ([.x2, .x8, .x18, .x20, .x21, .x22, .x23, .x24, .x26] : List Reg),
        w.getReg r = t₁.getReg r) ∧
      (w.getReg .x9).toNat = max 15 (t₁.getReg .x8).toNat := by
    obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000333c_spec pc₁ (by rv_eval [])
    have k₂ := b8000333c_keeps h₂
    have h15 : (15 : Word).toNat = 15 := rfl
    by_cases hg : 15 < (t₁.getReg .x8).toNat
    · exact ⟨t₂, hr₂, b8000333c_pc_taken h₂ (by rw [h15]; exact hg), b8000333c_mem_same h₂,
        fun r hr ↦ k₂ r (by revert r hr; decide), by rw [b8000333c_x9 h₂]; omega⟩
    · obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80003348_spec
        (b8000333c_pc_not_taken h₂ (by rw [h15]; omega)) (by rv_eval [])
      exact ⟨t₃, hr₂.trans hr₃, b80003348_pc h₃, fun a ↦ by
        rw [b80003348_mem_same h₃, b8000333c_mem_same h₂],
        fun r hr ↦ by rw [b80003348_keeps h₃ r (by revert r hr; decide), k₂ r (by revert r hr; decide)],
        by rw [b80003348_x9 h₃]; show 15 = _; omega⟩
  have mw₀ (a : Word) : w.getMem a = t₀.getMem a := by rw [mw, m₁]
  have rgw₀ (r : Reg) (hr : r ∈ ([.x2, .x8, .x18, .x20, .x21, .x22, .x23, .x24, .x26] : List Reg)) :
      w.getReg r = u.getReg r := by
    rw [rgw r hr, k₁ r (by revert r hr; decide), rg₀ r (by revert r hr; decide)]
  have spw : w.getReg .x2 = s.getReg .x2 - 2656 := by rw [rgw₀ .x2 (by decide)]; exact sp
  have x20w : w.getReg .x20 = OF := by rw [rgw₀ .x20 (by decide)]; exact h.x20
  have Bw := B₀.same hpre mw₀ (by rw [spw, sp₀])
  have Iw := Bw.k11.at11.base.inv
  have hnw : heapNext w = heapNext u := by simp only [heapNext, mw₀]; exact hn₀
  obtain ⟨u₁, hr₄, h₄⟩ := Sym.BlockSpec.reaches b8000334c_spec pcw (by
    rv_eval [spw, x20w]; simp only [Sym.validAccess_eight]
    and_intros <;> addr_omega [hb1, hb2, hb3, h.ofal, oh, hhu, gl, gh, sh, c2, c3, kb, hl3])
  have m₄ (a : Word) : u₁.getMem a = w.getMem a := b8000334c_mem_same h₄ a
  have k₄ := b8000334c_keeps h₄
  have B₄ := Bw.same hpre m₄ (k₄ .x2 (by decide))
  have I₄ := B₄.k11.at11.base.inv
  have hn₄ : heapNext u₁ = heapNext u := by simp only [heapNext, m₄]; exact hnw
  have x19₄ : u₁.getReg .x19 = (ofl (kapPre A k 6)).getD 5 0 := by
    rw [b8000334c_x19 h₄, x20w, mw₀]; exact vals₀ 5 (by decide)
  have e1320 : s.getReg .x2 - 2656 + 1320 = s.getReg .x2 - 1344 + 8 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have x25₄ : u₁.getReg .x25 = vecPtr u₁ (s.getReg .x2 - 1344) := by
    rw [b8000334c_x25 h₄, spw, e1320]; simp only [vecPtr, m₄]
  have x10₄ : u₁.getReg .x10 = s.getReg .x2 - 928 := by
    rw [b8000334c_x10 h₄, spw]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have x11₄ : u₁.getReg .x11 = 165 := by
    rw [b8000334c_x11 h₄, rgw₀ .x24 (by decide)]; exact h.x24
  have hab := hpre.stack.above
  have hx := hpre.stack.next
  rw [stackLo_eq] at hab hx
  rw [stack_eq] at hx
  simp only [heapEnd] at hab
  have pre : TryAllocPre .x13 .x14 u₁ := {
    heap := I₄.heap
    out := by
      rw [x10₄]; exact validMemRange_of (by addr_omega [hb1, hb3]) (Or.inr ⟨by addr_omega [hb1],
        by addr_omega [hb1, hb2]⟩)
    align := by rw [b8000334c_x13 h₄]; decide
    size := by rw [b8000334c_x14 h₄]; decide
    stack := stk10 hpre I₄ (by decide) (by decide)
    outFree := by
      rw [x10₄]; exact ⟨Or.inr (by addr_omega [hab, hb1]), by simp only [Apart]; addr_omega [hx, hb1]⟩
    outStack := by rw [x10₄, stackLo_callee I₄]; simp only [Apart]; addr_omega [hb1] }
  obtain ⟨t, hr, ⟨hpct, hp, post, -⟩ | hd⟩ := hTA u₁ (b8000334c_pc h₄) pre
  swap
  · exact ⟨t, hr₀.trans (hr₁.trans (hrw.trans (hr₄.trans hr))), Or.inl hd⟩
  have fr := post.frame.dframe
  rw [x10₄] at fr
  have ok := post.ok
  rw [x10₄, x11₄, b8000334c_x13 h₄, b8000334c_x14 h₄] at ok
  have hht := post.heap.hi
  have hmono := post.mono
  simp only [heapEnd] at hht
  have Bt := B₄.keep hpre fr (fun a ha ↦ by
      rcases ha with ha | ha | ha | ha
      · exact Or.inl (by simp only [Within] at ha ⊢; omega)
      · rw [stackLo_callee I₄] at ha
        exact Or.inr (Or.inl (by simp only [Within, tryAllocStack] at ha ⊢; addr_omega [ha, hb1]))
      · exact Or.inr (Or.inr (Or.inl ha))
      · simp only [Fresh] at ha; exact Or.inr (Or.inr (Or.inr ⟨by rw [hn₄] at ha; omega, ha.2⟩)))
    post.heap hmono (hp .x2 (by decide))
  have ovt : ∀ c < 165, t.getMem (OF + BitVec.ofNat 64 (8 * c)) = (ofl (kapPre A k 6)).getD c 0 :=
    fun c hc ↦ by
      rw [fr.getMem_of (fun x hx hw ↦ by
          simp only [Within] at hx
          rcases hw with h2 | h2 | h2 | h2
          · simp only [Within] at h2; addr_omega [hx, h2, hb1, hhu, oh, hc, h.ofal]
          · rw [stackLo_callee I₄] at h2; simp only [Within, tryAllocStack] at h2
            addr_omega [hx, h2, hb1, hhu, oh, hc]
          · simp only [Within, nextAddr] at h2; addr_omega [hx, h2, hhu, oh, hc]
          · simp only [Fresh] at h2; addr_omega [hx, h2, hn₄, oh, hc])
        (by addr_omega [hhu, oh, hc]), m₄, mw₀]
      exact vals₀ c hc
  have pct : t.pc = 0x80003374 := by rw [hpct, returnAddress_eq, b8000334c_x1 h₄]; decide
  have spt : t.getReg .x2 = s.getReg .x2 - 2656 := by
    rw [hp .x2 (by decide), k₄ .x2 (by decide)]; exact spw
  obtain ⟨t₁, hrt₁, ht₁⟩ := Sym.BlockSpec.reaches b80003374_spec pct (by
    rv_eval [spt]; simp only [Sym.validAccess_eight]; addr_omega [hb1, hb2, hb3])
  have e1728 : s.getReg .x2 - 2656 + 1728 = s.getReg .x2 - 928 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  by_cases hz : t.getMem (s.getReg .x2 - 928) = 0
  swap
  · exact ⟨t₁, hr₀.trans (hr₁.trans (hrw.trans (hr₄.trans (hr.trans hrt₁)))),
      Or.inl (trapAt (b80003374_pc_taken ht₁ (by rw [spt, e1728]; exact hz)))⟩
  have pc₅ := b80003374_pc_not_taken ht₁ (by rw [spt, e1728]; exact hz)
  obtain ⟨o1, o2⟩ := ok hz
  have e3960 : (165 : Word).toNat * (24 : Word).toNat = 3960 := rfl
  rw [e3960] at o2
  obtain ⟨PL, hPLd⟩ : ∃ PL, t.getMem (s.getReg .x2 - 928 + 16) = PL := ⟨_, rfl⟩
  rw [hPLd] at o2
  simp only [NewBuf] at o2
  obtain ⟨pl1, pl2⟩ := o2
  have pl3 : heapNext u ≤ PL.toNat ∧ PL.toNat + 3960 ≤ heapNext t := by
    rcases pl2 with h0 | h0
    · omega
    · rw [hn₄] at h0; exact h0
  have mt₁ := b80003374_mem_same ht₁
  have kt₁ := b80003374_keeps ht₁
  have spt₁ : t₁.getReg .x2 = s.getReg .x2 - 2656 := by rw [kt₁ .x2 (by decide)]; exact spt
  obtain ⟨t₂, hrt₂, ht₂⟩ := Sym.BlockSpec.reaches b8000337c_spec pc₅ (by
    rv_eval [spt₁]; simp only [Sym.validAccess_eight]; and_intros <;> addr_omega [hb1, hb2, hb3])
  have mt₂ := b8000337c_mem_same ht₂
  have kt₂ := b8000337c_keeps ht₂
  have m₂ (a : Word) : t₂.getMem a = t.getMem a := by rw [mt₂, mt₁]
  have hn₂ : heapNext t₂ = heapNext t := by simp only [heapNext, m₂]
  have e1736 : s.getReg .x2 - 2656 + 1736 = s.getReg .x2 - 928 + 8 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have e1744 : s.getReg .x2 - 2656 + 1744 = s.getReg .x2 - 928 + 16 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have rg (r : Reg) (hr : r ∈ ([.x2, .x8, .x9, .x18, .x19, .x20, .x23, .x24, .x25, .x26, .x27] :
      List Reg)) : t₂.getReg r = u₁.getReg r := by
    rw [kt₂ r (by revert r hr; decide), kt₁ r (by revert r hr; decide), hp r (by revert r hr; decide)]
  have rgu (r : Reg) (hr : r ∈ ([.x8, .x18, .x20, .x23, .x24, .x26] : List Reg)) :
      t₂.getReg r = u.getReg r := by
    rw [rg r (by revert r hr; decide), k₄ r (by revert r hr; decide), rgw₀ r (by revert r hr; decide)]
  have hPk : vecPtr t₂ (s.getReg .x2 - 1344) = vecPtr u₁ (s.getReg .x2 - 1344) := by
    simp only [vecPtr, m₂]
    exact fr.getMem_of (fun x hx hw ↦ by
        simp only [Within] at hx
        rcases hw with h2 | h2 | h2 | h2
        · simp only [Within] at h2; addr_omega [hx, h2, hb1]
        · rw [stackLo_callee I₄] at h2; simp only [Within, tryAllocStack] at h2; addr_omega [hx, h2, hb1]
        · simp only [Within, nextAddr] at h2; addr_omega [hx, h2, hb1]
        · simp only [Fresh] at h2; addr_omega [hx, h2, hb1, hht])
      (by addr_omega [hb1])
  have x8u : (u.getReg .x8).toNat = (stackOffsetsRust (bkl (kapPre A k 6))).2 := h.x8
  refine ⟨t₂, hr₀.trans (hr₁.trans (hrw.trans (hr₄.trans (hr.trans (hrt₁.trans hrt₂))))),
    Or.inr ⟨b8000337c_pc ht₂, PL, {
      base := Bt.same hpre m₂ (by rw [rg .x2 (by decide), hp .x2 (by decide)])
      ofal := h.ofal
      oflo := by omega
      ofpl := by omega
      ov := fun c hc ↦ by rw [m₂]; exact ovt c hc
      plal := pl1
      plhi := by rw [hn₂]; exact pl3.2
      pl0 := {
        pc := b8000337c_pc ht₂
        lt := by decide
        x10 := by rw [kt₂ .x10 (by decide), b80003374_x10 ht₁, spt, e1728, hz]; rfl
        x13 := by rw [b8000337c_x13 ht₂, spt₁, e1744, mt₁, hPLd]; simp
        x20 := by rw [rgu .x20 (by decide), h.x20]; simp
        x25 := by rw [rg .x25 (by decide), x25₄, hPk]; simp
        regs := fun _ _ ↦ rfl
        fr := Layout.DFrame.refl _ _
        vals := fun i hi ↦ absurd hi (Nat.not_lt_zero _) }
      x8 := by rw [rgu .x8 (by decide), x8u]
      x9 := by
        rw [rg .x9 (by decide), k₄ .x9 (by decide), x9w, rg .x8 (by decide), k₄ .x8 (by decide),
          rgw .x8 (by decide)]
      x11 := b8000337c_x11 ht₂
      x12 := b8000337c_x12 ht₂
      x14 := b8000337c_x14 ht₂
      x27 := by rw [rg .x27 (by decide), b8000334c_x27 h₄]
      x19 := by rw [rg .x19 (by decide)]; exact x19₄
      x21 := by rw [b8000337c_x21 ht₂, spt₁, e1744, mt₁, hPLd]
      x22 := by rw [b8000337c_x22 ht₂, spt₁, e1736, mt₁]; exact o1
      x24 := by rw [rgu .x24 (by decide)]; exact h.x24
      x18 := by rw [rgu .x18 (by decide)]; exact h.x18
      x23 := by rw [rgu .x23 (by decide)]; exact h.x23
      x26 := by rw [rgu .x26 (by decide)]; exact h.x26 }⟩⟩

end Rv64Verifier.Proofs.Walk
