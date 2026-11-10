import Rv64Verifier.Proofs.Multilinear.MleEvalInv

/-!
# `multilinear_eval`: the entry, the error path, the exit, the prologue and the outer loop's head

`entry` saves the registers; `err` takes a size mismatch to `Err`; `finish` writes the tag at
`0x8000d5e4`, restores and returns; `prologue` runs from the entry through the copy of the table to
the outer loop (`OInv`, `k = 0`) or, for an empty point, to the end (`Last`); `outer_head` from the
outer loop's head through `Scaler::new` to the inner loop (`IInv`, `i = 0`).
-/

namespace Rv64Verifier.Proofs.Multilinear.MleEval
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Contracts
  Rv64Verifier.Runtime Rv64Verifier.MultilinearContracts Rv64Verifier.MultilinearWords
  Rv64Verifier.Blocks.F56 Rv64Verifier.Proofs.Multilinear.ScalerFill
  Rv64Verifier.Proofs.Multilinear.EqKernelWin Rv64Verifier.Proofs.Multilinear.MleEvalWin
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- The size check, as compiled: `n < 64` and `L = 1 << n`. -/
theorem ok_cond (a b : Word) :
    ((((if a.ult 64 = true then (1 : Word) else 0) &&&
      if (b ^^^ 1 * BitVec.ofNat 64 (2 ^ (a.toNat % 64))).ult 1 = true then 1 else 0) == 0) = true) ↔
      ¬ (a.toNat < 64 ∧ b.toNat = 2 ^ a.toNat) := by
  have e1 (x : Word) : (1 : Word) * x = x := by
    rw [show (1 : Word) = 1#64 from rfl, BitVec.one_mul]
  have z (x : Word) : (0 : Word) &&& x = 0 := BitVec.zero_and
  rw [e1]
  by_cases ha : a.toNat < 64
  · have h1 : a.ult 64 = true := by simp only [BitVec.ult, decide_eq_true_eq]; exact ha
    have hp : 2 ^ a.toNat < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) ha
    rw [h1, Nat.mod_eq_of_lt ha]
    by_cases hb : b = BitVec.ofNat 64 (2 ^ a.toNat)
    · have hv : b.toNat = 2 ^ a.toNat := by rw [hb, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp]
      have hx : (b ^^^ BitVec.ofNat 64 (2 ^ a.toNat)).ult 1 = true := by
        rw [hb, BitVec.xor_self]; decide
      rw [hx]
      simp only [hv, ha, and_self, not_true_eq_false, iff_false]
      decide
    · have hv : b.toNat ≠ 2 ^ a.toNat := fun h ↦ hb (BitVec.eq_of_toNat_eq (by
        rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp]))
      have hx : (b ^^^ BitVec.ofNat 64 (2 ^ a.toNat)).ult 1 = false := by
        rw [BitVec.ult, decide_eq_false_iff_not]
        intro h0
        apply hb
        have hz : b ^^^ BitVec.ofNat 64 (2 ^ a.toNat) = 0 := BitVec.eq_of_toNat_eq (by
          simp only [Sym.wordToNatLit] at h0 ⊢; omega)
        have hbb : b = b ^^^ BitVec.ofNat 64 (2 ^ a.toNat) ^^^ BitVec.ofNat 64 (2 ^ a.toNat) := by
          rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
        rw [hbb, hz, Sym.zero_xor_lit]
      rw [hx]
      simp only [hv, and_false, not_false_eq_true, iff_true]
      decide
  · have h1 : a.ult 64 = false := by
      simp only [BitVec.ult, decide_eq_false_iff_not]; exact ha
    rw [h1]
    simp only [ha, false_and, not_false_eq_true, iff_true, Bool.false_eq_true, ↓reduceIte, z]
    decide

/-- The entry block: the registers saved, the sizes checked. -/
theorem entry {s : MachineState} (hpc : s.pc = 0x8000d28c) (hpre : MleEvalPre s) :
    ∃ t, Reaches Image.code s t ∧ b8000d28c.Holds s t ∧ Inv s t (s.getMem nextAddr) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hnx8 := hst.next
  obtain ⟨t, hr, h⟩ := Sym.BlockSpec.reaches b8000d28c_spec hpc (by
    rv_eval []
    and_intros <;> valid_access hst.valid [hb])
  have hm := b8000d28c_frame h (by addr_omega [hb])
  refine ⟨t, hr, h, {
    sp := b8000d28c_x2 h
    slots := by
      simp only [slots, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
        and_true]
      rv_eval []
      exact ⟨b8000d28c_m_x2_n8 h, b8000d28c_m_x2_n16 h, b8000d28c_m_x2_n24 h,
        b8000d28c_m_x2_n32 h, b8000d28c_m_x2_n40 h, b8000d28c_m_x2_n48 h,
        b8000d28c_m_x2_n56 h, b8000d28c_m_x2_n64 h, b8000d28c_m_x2_n72 h,
        b8000d28c_m_x2_n80 h, b8000d28c_m_x2_n88 h, b8000d28c_m_x2_n96 h,
        b8000d28c_m_x2_n104 h⟩
    dw := fun a ha _ ↦ hm a fun hw ↦ ha (Or.inr (Or.inl (by addr_omega [hw, hb])))
    next := hm _ (by addr_omega [hb, hnx8])
    mono := Nat.le_refl _
    fits := hpre.heap.hi }⟩

/-- The exit: the tag to the result, the registers restored. -/
theorem finish {s u : MachineState} {nx : Word} (hpre : MleEvalPre s) (h : Inv s u nx)
    (hpc : u.pc = 0x8000d5e4) (h8 : u.getReg .x8 = s.getReg .x10)
    (hval : match Model.multilinearEvalRust (mle s) (pt s) with
      | some v => u.getReg .x12 = 0 ∧ eAt u (s.getReg .x10 + 8) = v
      | none => u.getReg .x12 = 1) :
    ∃ t, Reaches Image.code u t ∧ t.pc = returnAddress s ∧ Preserves s t ∧ MleEvalPost s t := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hos := hpre.outStack
  have hof := hpre.outFree
  simp only [Outside] at hof
  have hsp := h.sp
  have sl := h.slots
  simp only [slots, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
    and_true] at sl
  rv_eval [] at sl
  obtain ⟨sl1, sl2, sl3, sl4, sl5, sl6, sl7, sl8, sl9, sl10, sl11, sl12, sl13⟩ := sl
  obtain ⟨t, hr, ht⟩ := Sym.BlockSpec.reaches b8000d5e4_spec hpc (by
    rv_eval [hsp, h8]
    and_intros <;> first
      | valid_access hst.valid [hb]
      | valid_access (outValid hpre) [hb]
      | addr_omega [hb, hos])
  have k := b8000d5e4_keeps ht
  have hfr := b8000d5e4_frame ht (by rw [h8]; addr_omega [hb])
  rw [h8] at hfr
  have m0 := b8000d5e4_m_x8_0 ht
  rw [h8] at m0
  have pc := b8000d5e4_pc ht
  have x2 := b8000d5e4_x2 ht
  have x8 := b8000d5e4_x8 ht
  have x9 := b8000d5e4_x9 ht
  have x18 := b8000d5e4_x18 ht
  have x19 := b8000d5e4_x19 ht
  have x20 := b8000d5e4_x20 ht
  have x21 := b8000d5e4_x21 ht
  have x22 := b8000d5e4_x22 ht
  have x23 := b8000d5e4_x23 ht
  have x24 := b8000d5e4_x24 ht
  have x25 := b8000d5e4_x25 ht
  have x26 := b8000d5e4_x26 ht
  have x27 := b8000d5e4_x27 ht
  rv_eval [hsp, sl1, sl2, sl3, sl4, sl5, sl6, sl7, sl8, sl9, sl10, sl11, sl12, sl13]
    at pc x2 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
  have hnt : t.getMem nextAddr = nx := (hfr _ (by addr_omega [hb, hof.2])).trans h.next
  have hn : heapNext t = nx.toNat := by simp only [heapNext, hnt]
  have hlo := hpre.heap.lo
  have hmono := h.mono
  have e8 : eAt t (s.getReg .x10 + 8) = eAt u (s.getReg .x10 + 8) :=
    hfr.eAt (by addr_omega [hb]) (by addr_omega [hb])
  refine ⟨t, hr, pc.trans (returnAddress_eq s).symm,
    preserves_of x2 x8 x9 x18 x19 fun r hr' ↦ ?_, {
      heap := ⟨by rw [hn]; simp only [heapNext] at hlo hmono ⊢; omega, by rw [hn]; exact h.fits⟩
      mono := by rw [hn]; exact hmono
      value := ?_
      frame := fun a ha ↦ ?_ }⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact x20
    · exact x21
    · exact x22
    · exact x23
    · exact x24
    · exact x25
    · exact x26
    · exact x27
  · simp only [mle, pt, ll, nn] at hval
    split
    · rename_i v hv
      rw [hv] at hval
      exact ⟨m0.trans hval.1, e8.trans hval.2⟩
    · rename_i hv
      rw [hv] at hval
      exact m0.trans hval
  · have hsub (b : Word) (hb' : PW s nx b) : Within b (s.getReg .x10) 32 ∨
        Within b (stackLo s mleEvalStack) mleEvalStack ∨ Within b nextAddr 8 ∨ Fresh s t b := by
      simp only [PW, LW] at hb'
      rcases hb' with hw | hw | hw | hw
      · exact Or.inl hw
      · exact Or.inr (Or.inl hw)
      · exact Or.inr (Or.inr (Or.inl hw))
      · exact Or.inr (Or.inr (Or.inr (by simp only [Fresh, hn]; exact hw)))
    have ha0 := ha 0 (by decide)
    simp only [BitVec.add_zero] at ha0
    rw [hfr a fun hw ↦ ha0 (Or.inl (by addr_omega [hw]))]
    exact h.dw a (fun hw ↦ ha0 (hsub a hw)) (Or.inr fun i hi hw ↦ ha i hi (hsub _ hw))

/-- **A size mismatch**: `Err`, tag `1`. -/
theorem err {s : MachineState} (hpc : s.pc = 0x8000d28c) (hpre : MleEvalPre s) (hs : ¬ Sized s) :
    ∃ t, Reaches Image.code s t ∧ t.pc = returnAddress s ∧ Preserves s t ∧ MleEvalPost s t := by
  have hb := bounds hpre
  have hos := hpre.outStack
  have hof := hpre.outFree
  simp only [Outside] at hof
  obtain ⟨t₁, hr₁, h₁, inv₁⟩ := entry hpc hpre
  have hpc₁ : t₁.pc = 0x8000d5b4 := h₁.pc_eq (by
    rv_eval []
    exact ite_eq_left_of_eq_true _ _ (eq_true ((ok_cond _ _).mpr fun h ↦ hs ⟨h.1, h.2⟩)))
  have hx8 : t₁.getReg .x8 = s.getReg .x10 := b8000d28c_x8 h₁
  obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000d5b4_spec hpc₁ (by
    rv_eval [hx8]; valid_access (outValid hpre) [hb])
  have k₂ := b8000d5b4_keeps h₂
  have hm₂ := b8000d5b4_frame h₂ (by rw [hx8]; addr_omega [hb])
  rw [hx8] at hm₂
  have inv₂ := inv₁.step hpre (DwFrame.of_mem hm₂) (fun a ha ↦ Or.inl (by addr_omega [ha, hb]))
    (fun a ha ↦ by addr_omega [ha, hb, hos]) ((hm₂ _ (by addr_omega [hb, hof.2])).trans inv₁.next)
    (Nat.le_refl _) inv₁.fits (k₂ .x2 (by decide))
  obtain ⟨t, hr, ht⟩ := finish hpre inv₂ (b8000d5b4_pc h₂) ((k₂ .x8 (by decide)).trans hx8) (by
    have hn : Model.multilinearEvalRust (mle s) (pt s) = none := by
      rw [Model.multilinearEvalRust, ite_eq_right_iff.mpr]
      · intro hc
        exact absurd (Model.multilinearEvalRust_eq _ _ hc) (by
          intro _
          exact hs ⟨by have := hc.1; rwa [pt, eListAt_length] at this,
            by have := hc.2; rwa [pt, mle, eListAt_length, eListAt_length] at this⟩)
    rw [hn]
    exact (k₂ .x12 (by decide)).trans (b8000d28c_x12 h₁))
  exact ⟨t, hr₁.trans (hr₂.trans hr), ht⟩

theorem ofNat_toNat_eq {x : Word} {n : Nat} (h : x.toNat = n) : x = BitVec.ofNat 64 n := by
  subst h; simp

/-- From the entry with the sizes right, through the copy, to the outer loop, or to the end for an
empty point. -/
theorem prologue (hT : TryAllocZeroedSpec) (hR : ReserveFastSpec 0x80008a10)
    (hC : MemcpySpec 0x800126e4) {s : MachineState} (hpc : s.pc = 0x8000d28c)
    (hpre : MleEvalPre s) (hs : Sized s) :
    ∃ u, Reaches Image.code s u ∧ ((∃ P nx, OInv s u P nx 0) ∨ (∃ P nx, Last s u P nx) ∨
      Dead Image.code u) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hab := hst.above
  have hnx8 := hst.next
  have hro := hst.rodata
  have hheap := hpre.heap
  have hlo := hheap.lo
  have hLpos : 0 < (s.getReg .x12).toNat := by
    have := hs.len; simp only [ll] at this; rw [this]; exact Nat.two_pow_pos _
  have hmr := hpre.mle.resolve_left (by omega)
  have hmf := hpre.mleFree.resolve_left (by omega)
  have hms := hpre.mleStack
  have hmo := hpre.mleOut
  have hm1 := hmr.1
  obtain ⟨t₁, hr₁, h₁, inv₁⟩ := entry hpc hpre
  have hpc₁ : t₁.pc = 0x8000d2f0 := h₁.pc_eq (by
    rv_eval []
    exact ite_eq_right_of_eq_false _ _ (eq_false fun hc ↦ (ok_cond _ _).mp hc ⟨hs.lt, hs.len⟩))
  have k₁ := b8000d28c_keeps h₁
  have hsp₁ : t₁.getReg .x2 = s.getReg .x2 - 208 := b8000d28c_x2 h₁
  -- `0x8000d2f0`: `try_allocate_in(S - 128, L, 0, 8, 24)`
  obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000d2f0_spec hpc₁ (by rv_eval [])
  have k₂ := b8000d2f0_keeps h₂
  have inv₂ := inv₁.same hpre (b8000d2f0_mem_same h₂) (k₂ .x2 (by decide))
  have hsp₂ : t₂.getReg .x2 = s.getReg .x2 - 208 := (k₂ .x2 (by decide)).trans hsp₁
  have hx10₂ : t₂.getReg .x10 = s.getReg .x2 - 128 := by rw [b8000d2f0_x10 h₂, hsp₁]; rv_eval []
  have hx11₂ : t₂.getReg .x11 = s.getReg .x12 := by rw [b8000d2f0_x11 h₂, b8000d28c_x19 h₁]
  have hn₂ : heapNext t₂ = heapNext s := by simp only [heapNext, inv₂.next]
  have hsl : stackLo t₂ tryAllocStack = s.getReg .x2 - 256 := by
    simp only [stackLo, tryAllocStack, hsp₂, Sym.sub_sub_lit]; rfl
  have hpre₂ : TryAllocPre .x13 .x14 t₂ := {
    heap := ⟨hn₂ ▸ hheap.lo, hn₂ ▸ hheap.hi⟩
    out := by rw [hx10₂]; valid_sub hst.valid [hb]
    align := by rw [b8000d2f0_x13 h₂]; decide
    size := by rw [b8000d2f0_x14 h₂]; decide
    stack := ⟨⟨by rw [hsl]; valid_sub hst.valid [hb], by rw [hsp₂]; addr_omega [hb]⟩,
      by rw [hsl]; addr_omega [hab, hb], by rw [hsl]; addr_omega [hnx8, hb],
      by rw [hsl]; addr_omega [hro, hb]⟩
    outFree := by
      rw [hx10₂]
      simp only [Outside]
      exact ⟨Or.inr (by addr_omega [hab, hb]), by addr_omega [hnx8, hb]⟩
    outStack := by rw [hx10₂, hsl]; addr_omega [hb] }
  obtain ⟨t₃, hr₃, ⟨hpc₃, hpres₃, hpost₃, -⟩ | hdead⟩ := hT.call hr₂ (b8000d2f0_pc h₂) hpre₂
  swap
  · exact ⟨t₃, hr₁.trans hr₃, Or.inr (Or.inr hdead)⟩
  have hfr₃ := hpost₃.frame
  rw [hx10₂, hsl] at hfr₃
  have hfit₃ := hpost₃.heap.hi
  have inv₃ : Inv s t₃ (t₃.getMem nextAddr) := inv₂.step hpre (DwFrame.of_byte hfr₃)
    (fun a ha ↦ by
      rcases ha with ha | ha | ha | ha
      · exact Or.inr (Or.inl (by addr_omega [ha, hb]))
      · exact Or.inr (Or.inl (by addr_omega [ha, hb]))
      · exact Or.inr (Or.inr (Or.inl ha))
      · simp only [Fresh, hn₂] at ha
        exact Or.inr (Or.inr (Or.inr ha)))
    (fun a ha ↦ by
      rcases ha with ha | ha | ha | ha
      · addr_omega [ha, hb]
      · addr_omega [ha, hb]
      · addr_omega [ha, hb, hnx8]
      · simp only [Fresh] at ha; addr_omega [ha, hb, hab, hfit₃])
    rfl (by rw [← heapNext, ← heapNext, ← hn₂]; exact hpost₃.mono) hfit₃ (hpres₃.reg .x2)
  have hsp₃ : t₃.getReg .x2 = s.getReg .x2 - 208 := (hpres₃.reg .x2).trans hsp₂
  -- `0x8000d310`: trap on `Err`
  obtain ⟨t₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b8000d310_spec
    (by rw [hpc₃, returnAddress_eq, b8000d2f0_x1 h₂]; decide) (by
      rv_eval [hsp₃]; valid_access hst.valid [hb])
  rcases eq_or_ne (t₃.getMem (s.getReg .x2 - 128)) 0 with htag | htag
  swap
  · refine ⟨t₄, hr₁.trans (hr₃.trans hr₄), Or.inr (Or.inr (dead_of_fetch ?_))⟩
    rw [b8000d310_pc_taken h₄ (by rv_eval [hsp₃]; exact htag)]
    exact Option.isNone_iff_eq_none.mp (by decide +kernel)
  have k₄ := b8000d310_keeps h₄
  have hm34 (a : Word) : t₄.getMem a = t₃.getMem a := b8000d310_mem_same h₄ a
  have inv₄ := inv₃.same hpre hm34 (k₄ .x2 (by decide))
  obtain ⟨hcap, hbuf⟩ := hpost₃.ok (by rw [hx10₂]; exact htag)
  rw [hx10₂, hx11₂] at hcap hbuf
  rw [b8000d2f0_x14 h₂, b8000d2f0_x13 h₂] at hbuf
  rv_eval [] at hcap hbuf
  obtain ⟨P, hP⟩ : ∃ P, P = t₃.getMem (s.getReg .x2 - 112) := ⟨_, rfl⟩
  rw [← hP] at hbuf
  simp only [NewBuf, hn₂] at hbuf
  have hPa : P.toNat % 8 = 0 := hbuf.1
  have hPr : heapNext s ≤ P.toNat ∧ P.toNat + (s.getReg .x12).toNat * 24 ≤ heapNext t₃ := by
    rcases hbuf.2 with h | h
    · omega
    · exact h
  -- `0x8000d318`: the `Vec` at `S - 128`, the result's address at `S - 208`
  have hsp₄ : t₄.getReg .x2 = s.getReg .x2 - 208 := (k₄ .x2 (by decide)).trans hsp₃
  obtain ⟨t₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b8000d318_spec
    (b8000d310_pc_not_taken h₄ (by rv_eval [hsp₃]; exact htag)) (by
      rv_eval [hsp₄]; and_intros <;> valid_access hst.valid [hb])
  have k₅ := b8000d318_keeps h₅
  have hm₅ := b8000d318_frame h₅ (by rw [hsp₄]; addr_omega [hb])
  rw [hsp₄] at hm₅
  have inv₅ := inv₄.step hpre (DwFrame.of_mem hm₅)
    (fun a ha ↦ Or.inr (Or.inl (by addr_omega [ha, hb]))) (fun a ha ↦ by addr_omega [ha, hb])
    ((hm₅ _ (by addr_omega [hb, hnx8])).trans inv₄.next) (Nat.le_refl _) inv₄.fits
    (k₅ .x2 (by decide))
  have hsp₅ : t₅.getReg .x2 = s.getReg .x2 - 208 := (k₅ .x2 (by decide)).trans hsp₄
  have c80 := b8000d318_m_x2_80 h₅
  have c88 := b8000d318_m_x2_88 h₅
  have c96 := b8000d318_m_x2_96 h₅
  have c0 := b8000d318_m_x2_0 h₅
  rw [hsp₄] at c80 c88 c96 c0
  rv_eval [hm34] at c80 c88 c96
  have hx8₄ : t₄.getReg .x8 = s.getReg .x10 := by
    rw [k₄ .x8 (by decide), hpres₃.reg .x8, k₂ .x8 (by decide), b8000d28c_x8 h₁]
  rw [hx8₄] at c0
  rw [hcap] at c80
  rw [← hP] at c88
  -- `reserve`, with room enough
  have hx10₅ : t₅.getReg .x10 = s.getReg .x2 - 128 := by rw [b8000d318_x10 h₅, hsp₄]; rv_eval []
  have hx19₄ : t₄.getReg .x19 = s.getReg .x12 := by
    rw [k₄ .x19 (by decide), hpres₃.reg .x19, k₂ .x19 (by decide), b8000d28c_x19 h₁]
  have hx11₅ : t₅.getReg .x11 = s.getReg .x12 := by rw [b8000d318_x11 h₅, hx19₄]
  obtain ⟨t₆, hr₆, ⟨hpc₆, hpres₆, -, hm₆⟩ | hdead⟩ := hR.call hr₅ (b8000d318_pc h₅)
    ⟨by rw [hx10₅]; valid_sub hst.valid [hb], by
      simp only [vecLen, vecCap]
      rw [hx10₅, hx11₅, show s.getReg .x2 - 128 + 16 = s.getReg .x2 - 112 by rv_eval [], c80, c96]
      simp⟩
  swap
  · exact ⟨t₆, hr₁.trans (hr₃.trans (hr₄.trans hr₆)), Or.inr (Or.inr hdead)⟩
  have hsp₆ : t₆.getReg .x2 = s.getReg .x2 - 208 := (hpres₆.reg .x2).trans hsp₅
  have inv₆ := inv₅.same hpre hm₆ (hpres₆.reg .x2)
  -- `0x8000d340`: `memcpy(P, mle, 24 L)`
  obtain ⟨t₇, hr₇, h₇⟩ := Sym.BlockSpec.reaches b8000d340_spec
    (by rw [hpc₆, returnAddress_eq, b8000d318_x1 h₅]; decide) (by
      rv_eval [hsp₆]; and_intros <;> valid_access hst.valid [hb])
  have k₇ := b8000d340_keeps h₇
  have hm76 (a : Word) : t₇.getMem a = t₆.getMem a := b8000d340_mem_same h₇ a
  have inv₇ := inv₆.same hpre hm76 (k₇ .x2 (by decide))
  have hsp₇ : t₇.getReg .x2 = s.getReg .x2 - 208 := (k₇ .x2 (by decide)).trans hsp₆
  have hd₇ : t₇.getReg .x10 = P := by
    rw [b8000d340_x10 h₇, hsp₆]; rv_eval [hm₆, c88, c96]
  have hs₇ : t₇.getReg .x11 = s.getReg .x11 := by
    rw [b8000d340_x11 h₇, hpres₆.reg .x20, k₅ .x20 (by decide), k₄ .x20 (by decide),
      hpres₃.reg .x20, b8000d2f0_x20 h₂, k₁ .x11 (by decide)]
  have hx19₆ : t₆.getReg .x19 = s.getReg .x12 := by
    rw [hpres₆.reg .x19, k₅ .x19 (by decide), hx19₄]
  have hn₇ : (t₇.getReg .x12).toNat = 24 * (s.getReg .x12).toNat := by
    rw [b8000d340_x12 h₇, hx19₆]; addr_omega [hPr, hfit₃]
  have hP₇ : t₇.getReg .x21 = P := by rw [b8000d340_x21 h₇, hsp₆]; rv_eval [hm₆, c88]
  have hpre₇ : MemcpyPre t₇ := {
    dst := by rw [hd₇, hn₇]; addr_omega [hPr, hfit₃, hlo]
    src := by rw [hs₇, hn₇]; exact hm1
    apart := by rw [hd₇, hs₇, hn₇]; addr_omega [hPr, hfit₃, hmf.1]
    stack := ⟨by
        refine ValidMemRange.sub hst.valid ?_ ?_ ?_ <;> simp only [stackLo] <;> rw [hsp₇] <;>
          addr_omega [hb],
      by rw [hsp₇]; addr_omega [hb]⟩
    dstStack := by
      rw [hd₇, hn₇]; simp only [stackLo]; rw [hsp₇]; addr_omega [hPr, hfit₃, hb, hab]
    srcStack := by rw [hs₇, hn₇]; simp only [stackLo]; rw [hsp₇]; addr_omega [hms, hb] }
  obtain ⟨t₈, hr₈, ⟨hpc₈, hpres₈, hcpy⟩ | hdead⟩ := hC.call hr₇ (b8000d340_pc h₇) hpre₇
  swap
  · exact ⟨t₈, hr₁.trans (hr₃.trans (hr₄.trans (hr₆.trans hr₈))), Or.inr (Or.inr hdead)⟩
  have hfr₈ := hcpy.frame
  rw [hd₇, hn₇] at hfr₈
  simp only [stackLo, hsp₇] at hfr₈
  have inv₈ := inv₇.step hpre (DwFrame.of_byte hfr₈) (fun a ha ↦ by
      rcases ha with ha | ha
      · exact Or.inr (Or.inr (Or.inr ⟨by addr_omega [ha, hPr], by addr_omega [ha, hPr]⟩))
      · exact Or.inr (Or.inl (by addr_omega [ha, hb])))
    (fun a ha ↦ by rcases ha with ha | ha <;> addr_omega [ha, hb, hab, hPr, hfit₃])
    ((hfr₈.getMem fun i hi ha ↦ by
        rcases ha with ha | ha
        · addr_omega [ha, hi, hPr, hfit₃]
        · addr_omega [ha, hi, hb, hnx8]).trans inv₇.next)
    (Nat.le_refl _) inv₇.fits (hpres₈.reg .x2)
  have hby := hcpy.bytes
  rw [hd₇, hs₇, hn₇] at hby
  have hel₈ : eListAt t₈ P (ll s) = mle s := by
    rw [ll, eListAt_eq_of_bytesAt hby hPa hmr.2]
    exact inv₇.slice hpre hmf hms hmo (by addr_omega [hm1])
  have res₈ : Res s t₈ P (t₃.getMem nextAddr) := {
    inv := inv₈
    outp := by
      rw [hfr₈.getMem fun i hi ha ↦ by
        rcases ha with ha | ha
        · addr_omega [ha, hi, hPr, hfit₃, hb, hab]
        · addr_omega [ha, hi, hb], hm76, hm₆]
      exact c0
    align := hPa
    lo := hPr.1
    top := by simp only [ll]; have := hPr.2; simp only [heapNext] at this; omega }
  have hsp₈ : t₈.getReg .x2 = s.getReg .x2 - 208 := (hpres₈.reg .x2).trans hsp₇
  -- `0x8000d370`: the length, and an empty point
  obtain ⟨t₉, hr₉, h₉⟩ := Sym.BlockSpec.reaches b8000d370_spec
    (by rw [hpc₈, returnAddress_eq, b8000d340_x1 h₇]; decide) (by rv_eval [])
  have k₉ := b8000d370_keeps h₉
  have hm₉ := b8000d370_mem_same h₉
  have res₉ := res₈.same hpre hm₉ (k₉ .x2 (by decide))
  have hx8₉ : t₉.getReg .x8 = s.getReg .x12 := by
    rw [b8000d370_x8 h₉, hpres₈.reg .x8, b8000d340_x8 h₇, hsp₆, hpres₈.reg .x19,
      k₇ .x19 (by decide), hx19₆]
    rv_eval [hm₆, c96]
    exact BitVec.zero_add _
  have hx18₈ : t₈.getReg .x18 = s.getReg .x14 := by
    rw [hpres₈.reg .x18, k₇ .x18 (by decide), hpres₆.reg .x18,
      k₅ .x18 (by decide), k₄ .x18 (by decide), hpres₃.reg .x18, k₂ .x18 (by decide),
      b8000d28c_x18 h₁]
  have hx21₉ : t₉.getReg .x21 = P := by rw [k₉ .x21 (by decide), hpres₈.reg .x21, hP₇]
  have hL : s.getReg .x12 = BitVec.ofNat 64 (2 ^ nn s) := ofNat_toNat_eq hs.len
  by_cases hn0 : s.getReg .x14 = 0
  · have hn0' : nn s = 0 := by simp only [nn, hn0]; rfl
    obtain ⟨t₁₀, hr₁₀, h₁₀⟩ := Sym.BlockSpec.reaches b8000d5bc_spec
      (b8000d370_pc_taken h₉ (by rw [hx18₈]; exact hn0)) (by rv_eval [])
    have hm₁₀ := b8000d5bc_mem_same h₁₀
    refine ⟨t₁₀, hr₁.trans (hr₃.trans (hr₄.trans (hr₆.trans (hr₈.trans (hr₉.trans hr₁₀))))),
      Or.inr (Or.inl ⟨P, t₃.getMem nextAddr, {
        toRes := res₉.same hpre hm₁₀ (b8000d5bc_keeps h₁₀ .x2 (by decide))
        pc := b8000d5bc_pc h₁₀
        x19 := by
          rw [b8000d5bc_x19 h₁₀, hx8₉, hL, hn0']
          decide
        x21 := (b8000d5bc_keeps h₁₀ .x21 (by decide)).trans hx21₉
        val := ?_ }⟩)⟩
    have h0 : cur s (nn s) = mle s := by rw [hn0']; simp [cur]
    rw [h0, ← hel₈, EqKernel.eListAt_getD' _ _ (by simp only [ll]; omega)]
    simp only [Nat.mul_zero, BitVec.add_zero]
    unfold eAt
    rw [hm₁₀, hm₁₀, hm₁₀, hm₉, hm₉, hm₉]
  -- `0x8000d378`: the constants
  have hnpos : 0 < nn s := by
    rcases Nat.eq_zero_or_pos (nn s) with h | h
    · exact absurd (BitVec.eq_of_toNat_eq (by simpa [nn] using h)) hn0
    · exact h
  have hx9₉ : t₉.getReg .x9 = s.getReg .x13 := by
    rw [k₉ .x9 (by decide), hpres₈.reg .x9, k₇ .x9 (by decide), hpres₆.reg .x9,
      k₅ .x9 (by decide), k₄ .x9 (by decide), hpres₃.reg .x9, k₂ .x9 (by decide),
      b8000d28c_x9 h₁]
  have hsp₉ : t₉.getReg .x2 = s.getReg .x2 - 208 := (k₉ .x2 (by decide)).trans hsp₈
  obtain ⟨t₁₀, hr₁₀, h₁₀⟩ := Sym.BlockSpec.reaches b8000d378_spec
    (b8000d370_pc_not_taken h₉ (by rw [hx18₈]; exact hn0)) (by
      rv_eval [hsp₉]; valid_access hst.valid [hb])
  have k₁₀ := b8000d378_keeps h₁₀
  have hm₁₀ := b8000d378_frame h₁₀ (by rw [hsp₉]; addr_omega [hb])
  rw [hsp₉] at hm₁₀
  rv_eval [] at hm₁₀
  have hpb := ValidMemRange.bounds (pointValid hpre hnpos) (by omega)
  have mstop := b8000d378_m_x2_8 h₁₀
  rw [hsp₉, hx9₉, k₉ .x18 (by decide), hx18₈] at mstop
  rv_eval [] at mstop
  have res₁₀ := res₉.step hpre (DwFrame.of_mem hm₁₀) (fun a ha ↦ Or.inl (by addr_omega [ha, hb]))
    (fun a ha ↦ ⟨by addr_omega [ha, hb], by addr_omega [ha, hb]⟩)
    ((hm₁₀ _ (by addr_omega [hb, hnx8])).trans res₉.inv.next) (Nat.le_refl _) res₉.inv.fits
    (k₁₀ .x2 (by decide))
  refine ⟨t₁₀, hr₁.trans (hr₃.trans (hr₄.trans (hr₆.trans (hr₈.trans (hr₉.trans hr₁₀))))),
    Or.inl ⟨P, t₃.getMem nextAddr, {
      toRes := res₁₀
      x20 := b8000d378_x20 h₁₀
      x21 := (k₁₀ .x21 (by decide)).trans hx21₉
      x22 := b8000d378_x22 h₁₀
      x24 := b8000d378_x24 h₁₀
      stop := by rw [mstop]; simp only [nn] at hpb ⊢; addr_omega [hpb]
      pc := b8000d378_pc h₁₀
      lt := hnpos
      x11 := by rw [b8000d378_x11 h₁₀, hx9₉]; simp
      x8 := by rw [k₁₀ .x8 (by decide), hx8₉, hL, Nat.sub_zero]
      buf := ?_ }⟩⟩
  have hc0 : cur s 0 = mle s := by simp [cur]
  rw [Nat.sub_zero, hc0, ← hel₈, ← hs.len]
  exact (EqKernel.eListAt_frame hm₁₀ (by simp only [ll]; addr_omega [hPr, hfit₃, hb, hab])
    (by simp only [ll]; addr_omega [hPr, hfit₃])).trans (EqKernel.eListAt_same hm₉ P (ll s))

theorem outer_head (hS : ScalerSpec) {s : MachineState} (hpre : MleEvalPre s) (hs : Sized s)
    {P nx : Word} {k : Nat} {u : MachineState} (hu : OInv s u P nx k) :
    ∃ v, Reaches Image.code u v ∧ ((∃ T nx', IInv s v P T nx' k 0) ∨ Dead Image.code v) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hab := hst.above
  have hnx8 := hst.next
  have hro := hst.rodata
  have hlo := hpre.heap.lo
  have hk := hu.lt
  have hsp := hu.inv.sp
  have hpb := ValidMemRange.bounds (pointValid hpre (by omega)) (by omega)
  have hfit := hu.inv.fits
  have hmono := hu.inv.mono
  have htop := hu.top
  have hPlo := hu.lo
  have hlen := hs.len
  obtain ⟨hPN, hn27⟩ := hu.small hs
  simp only [heapEnd] at hPN
  have hm := Nat.two_pow_pos (nn s - k - 1)
  have hpk : 2 ^ (nn s - k) ≤ 2 ^ nn s := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hh64 : 2 ^ (nn s - k - 1) < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  -- `0x8000d3b8`: `Scaler::new(S - 160, &point[k], len / 2)`
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000d3b8_spec hu.pc (by
    rv_eval [hsp]; valid_access hst.valid [hb])
  have k₁ := b8000d3b8_keeps h₁
  have hm₁ := b8000d3b8_frame h₁ (by rw [hsp]; addr_omega [hb])
  rw [hsp] at hm₁
  rv_eval [] at hm₁
  have m192 := b8000d3b8_m_x2_16 h₁
  rw [hsp, hu.x11] at m192
  rv_eval [] at m192
  have hhalf : u.getReg .x8 >>> 1 = BitVec.ofNat 64 (2 ^ (nn s - k - 1)) := by
    rw [hu.x8]; exact shr1 (by omega) (by omega)
  have hx12₁ : u₁.getReg .x12 = BitVec.ofNat 64 (2 ^ (nn s - k - 1)) :=
    (b8000d3b8_x12 h₁).trans hhalf
  have hx19₁ : u₁.getReg .x19 = BitVec.ofNat 64 (2 ^ (nn s - k - 1)) :=
    (b8000d3b8_x19 h₁).trans hhalf
  have hx10₁ : u₁.getReg .x10 = s.getReg .x2 - 160 := by rw [b8000d3b8_x10 h₁, hsp]; rv_eval []
  have hx11₁ : u₁.getReg .x11 = s.getReg .x13 + BitVec.ofNat 64 (24 * k) :=
    (k₁ .x11 (by decide)).trans hu.x11
  have hsp₁ : u₁.getReg .x2 = s.getReg .x2 - 208 := (k₁ .x2 (by decide)).trans hsp
  have mid₁ := hu.toMid.step hpre (DwFrame.of_mem hm₁) (fun a ha ↦ Or.inl (by addr_omega [ha, hb]))
    (fun a ha ↦ ⟨by addr_omega [ha, hb], by addr_omega [ha, hb]⟩)
    ((hm₁ _ (by addr_omega [hb, hnx8])).trans hu.inv.next) (Nat.le_refl _) hfit
    fun r hr ↦ k₁ r (mem_of_mem hr _)
  have hbuf₁ : eListAt u₁ P (2 ^ (nn s - k)) = eListAt u P (2 ^ (nn s - k)) :=
    EqKernel.eListAt_frame hm₁ (by addr_omega [hPN, hPlo, hlo, hb, hab, hpk]) (by omega)
  have hsl : stackLo u₁ scalerStack = s.getReg .x2 - 432 := by
    simp only [stackLo, scalerStack, fromElemStack, tryAllocStack, hsp₁, Sym.sub_sub_lit]; rfl
  have hpf := hpre.pointFree.resolve_left (by simp only [nn] at hk; omega)
  simp only [Outside] at hpf
  have hn₁ : heapNext u₁ = nx.toNat := by simp only [heapNext, mid₁.inv.next]
  have hn₁' : (u₁.getMem nextAddr).toNat = nx.toNat := hn₁
  have hpre₁ : ScalerPre u₁ := {
    heap := ⟨by rw [hn₁]; simp only [heapNext] at hlo hmono; omega, by rw [hn₁]; exact hfit⟩
    out := by rw [hx10₁]; valid_sub hst.valid [hb]
    r := by rw [hx11₁]; valid_sub (pointValid hpre (by omega)) [hpb, hk]
    stack := ⟨⟨by rw [hsl]; valid_sub hst.valid [hb], by rw [hsp₁]; addr_omega [hb]⟩,
      by rw [hsl]; addr_omega [hab, hb], by rw [hsl]; addr_omega [hnx8, hb],
      by rw [hsl]; addr_omega [hro, hb]⟩
    outFree := by
      rw [hx10₁]
      simp only [Outside]
      exact ⟨Or.inr (by addr_omega [hab, hb]), by addr_omega [hnx8, hb]⟩
    outStack := by rw [hx10₁, hsl]; addr_omega [hb]
    rFree := by
      rw [hx11₁]
      simp only [Outside, hn₁]
      refine ⟨?_, by addr_omega [hpf.2, hk, hpb]⟩
      rcases hpf.1 with h | h
      · exact Or.inl (by addr_omega [h, hk, hpb, hmono])
      · exact Or.inr (by addr_omega [h, hk, hpb])
    rStack := by rw [hx11₁, hsl]; addr_omega [hpre.pointStack, hk, hpb, hb]
    rOut := by rw [hx11₁, hx10₁]; addr_omega [hpre.pointStack, hk, hpb, hb]
    rodata := mid₁.inv.rodataOk hpre }
  obtain ⟨w, hr₂, ⟨hpc₂, hpres₂, hpost₂⟩ | hdead⟩ := hS.call hr₁ (b8000d3b8_pc h₁) hpre₁
  swap
  · exact ⟨w, hr₂, Or.inr hdead⟩
  have hfr₂ := hpost₂.frame
  rw [hx10₁, hsl] at hfr₂
  have hfit₂ := hpost₂.heap.hi
  have hmono₂ := hpost₂.mono
  rw [hn₁] at hmono₂
  simp only [heapNext] at hfit₂ hmono₂
  have hsu : (s.getMem nextAddr).toNat ≤ nx.toNat := hmono
  have hX2 (a : Word) (ha : Within a (s.getReg .x2 - 160) 32 ∨
      Within a (s.getReg .x2 - 432) scalerStack ∨ Within a nextAddr 8 ∨ Fresh u₁ w a) :
      LW s (w.getMem nextAddr) a := by
    simp only [LW]
    rcases ha with ha | ha | ha | ha
    · exact Or.inl (by addr_omega [ha, hb])
    · exact Or.inl (by addr_omega [ha, hb])
    · exact Or.inr (Or.inl ha)
    · simp only [Fresh, heapNext] at ha
      exact Or.inr (Or.inr ⟨by simp only [heapNext]; omega, ha.2⟩)
  have miss2 (a : Word) (h1 : (s.getReg .x2).toNat - 208 ≤ a.toNat)
      (h2 : a.toNat < (s.getReg .x2).toNat - 160) : ¬ (Within a (s.getReg .x2 - 160) 32 ∨
        Within a (s.getReg .x2 - 432) scalerStack ∨ Within a nextAddr 8 ∨ Fresh u₁ w a) := by
    rintro (ha | ha | ha | ha)
    · addr_omega [ha, hb, h1, h2]
    · addr_omega [ha, hb, h1, h2]
    · addr_omega [ha, hb, h1, h2, hnx8]
    · simp only [Fresh, heapNext] at ha; addr_omega [ha, hb, h1, h2, hab, hfit₂]
  have hdw₂ := DwFrame.of_byte hfr₂
  have mid₂ := mid₁.step hpre hdw₂ hX2 (fun a ha ↦ by
      rcases ha with ha | ha | ha | ha
      · exact ⟨by addr_omega [ha, hb], by addr_omega [ha, hb]⟩
      · exact ⟨by addr_omega [ha, hb], by addr_omega [ha, hb]⟩
      · exact ⟨by addr_omega [ha, hb, hnx8], by addr_omega [ha, hb, hnx8]⟩
      · simp only [Fresh, heapNext] at ha
        exact ⟨by addr_omega [ha, hb, hab, hfit₂], by addr_omega [ha, hb, hab, hfit₂]⟩)
    rfl hmono₂ hfit₂ fun r hr ↦ hpres₂ r (by unfold calleeSaved; exact mem_of_mem hr _)
  have m192₂ : w.getMem (s.getReg .x2 - 192) = s.getReg .x13 + BitVec.ofNat 64 (24 * k) := by
    rw [EqKernel.DwFrame.keep hdw₂ fun i hi ↦
      miss2 _ (by addr_omega [hi, hb]) (by addr_omega [hi, hb])]
    exact m192
  have hbuf₂ : eListAt w P (2 ^ (nn s - k)) = eListAt u P (2 ^ (nn s - k)) := by
    rw [EqKernel.eListAt_dw hdw₂ (fun a ha hx ↦ by
        rcases hx with hx | hx | hx | hx
        · addr_omega [ha, hx, hb, hab, hPN, hpk]
        · addr_omega [ha, hx, hb, hab, hPN, hpk]
        · addr_omega [ha, hx, hPN, hpk]
        · simp only [Fresh, heapNext] at hx; addr_omega [ha, hx, htop, hn₁', hpk, hlen])
      (by omega), hbuf₁]
  have hsp₂ : w.getReg .x2 = s.getReg .x2 - 208 := (hpres₂.reg .x2).trans hsp₁
  have hx19₂ : w.getReg .x19 = BitVec.ofNat 64 (2 ^ (nn s - k - 1)) :=
    (hpres₂.reg .x19).trans hx19₁
  have hx8₂ : w.getReg .x8 = BitVec.ofNat 64 (2 ^ (nn s - k)) := by
    rw [hpres₂.reg .x8, k₁ .x8 (by decide), hu.x8]
  -- `0x8000d3d0`, `0x8000d3d4`: the inner loop's set-up
  obtain ⟨w₁, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000d3d0_spec
    (by rw [hpc₂, returnAddress_eq, b8000d3b8_x1 h₁]; decide) (by rv_eval [])
  have hne : BitVec.ofNat 64 (2 ^ (nn s - k - 1)) ≠ 0 := by
    intro h0
    have := congrArg BitVec.toNat h0
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hh64] at this
    simp only [Sym.wordToNatLit] at this
    omega
  have k₃ := b8000d3d0_keeps h₃
  have hm₃ := b8000d3d0_mem_same h₃
  have hsp₃ : w₁.getReg .x2 = s.getReg .x2 - 208 := (k₃ .x2 (by decide)).trans hsp₂
  obtain ⟨w₂, hr₄, h₄⟩ := Sym.BlockSpec.reaches b8000d3d4_spec
    (b8000d3d0_pc_not_taken h₃ (by rw [hx19₂]; exact hne)) (by
      rv_eval [hsp₃]; and_intros <;> valid_access hst.valid [hb])
  have k₄ := b8000d3d4_keeps h₄
  have hm₄ := b8000d3d4_mem_same h₄
  have hmw (a : Word) : w₂.getMem a = w.getMem a := (hm₄ a).trans (hm₃ a)
  have hreg (r : Reg) (hr : r ∈ midRegs) : w₂.getReg r = w.getReg r :=
    (k₄ r (mem_of_mem hr _)).trans (k₃ r (mem_of_mem hr _))
  have hr_eq : eAt u₁ (u₁.getReg .x11) = (pt s).getD k 0 := by
    rw [hx11₁, ← EqKernel.eListAt_getD' u₁ (s.getReg .x13) hk, mid₁.inv.point hpre (by omega)]
  have htag : w₂.getReg .x28 = w.getMem (s.getReg .x2 - 160) := by
    rw [b8000d3d4_x28 h₄, hsp₃, hm₃]; rv_eval []
  refine ⟨w₂, hr₂.trans (hr₃.trans hr₄), Or.inl ⟨w.getMem (s.getReg .x2 - 144), w.getMem nextAddr,
    { toMid := mid₂.same hpre hmw hreg
      pc := b8000d3d4_pc h₄
      lt := hk
      ilt := hm
      m192 := (hmw _).trans m192₂
      x19 := (k₄ .x19 (by decide)).trans ((k₃ .x19 (by decide)).trans hx19₂)
      x9 := by rw [b8000d3d4_x9 h₄, k₃ .x8 (by decide), hx8₂]; exact shr1' (by omega) (by omega)
      x23 := (b8000d3d4_x23 h₄).trans rfl
      sc := {
        x26 := by rw [b8000d3d4_x26 h₄, hsp₃, hm₃]; rv_eval []
        plain := fun hne ↦ by
          by_cases hl : (u₁.getReg .x12).toNat < 256
          · obtain ⟨-, he⟩ := hpost₂.plain hl
            rw [hx10₁] at he
            rv_eval [] at he
            rw [← hr_eq, ← he]
            unfold eAt
            rw [hmw, hmw, hmw]
          · have h0 := (hpost₂.table (by omega)).1
            rw [hx10₁] at h0
            exact absurd (htag.trans h0) hne
        table := fun he ↦ by
          by_cases hl : (u₁.getReg .x12).toNat < 256
          · have := (hpost₂.plain hl).1
            rw [hx10₁, ← htag, he] at this
            exact absurd this (by decide)
          obtain ⟨-, hvok, hvlen, hvmap, hvnew⟩ := hpost₂.table (by omega)
          rw [hx10₁] at hvok hvlen hvmap hvnew
          simp only [vecLen, vecPtr, vecEs] at hvlen hvmap hvnew
          rv_eval [] at hvlen hvmap hvnew
          simp only [NewBuf, hn₁] at hvnew
          rw [hvlen] at hvmap
          have hT := hvnew.2
          simp only [heapNext] at hT
          refine ⟨by rw [b8000d3d4_x27 h₄, hsp₃, hm₃]; rv_eval [hvlen], ⟨hvnew.1,
            by simp only [heapStart, heapNext] at hlo hmono ⊢; omega,
            by simp only [tabBytes]; omega⟩, by simp only [ll] at htop ⊢; omega,
            by simp only [tabBytes]; omega, ?_⟩
          rw [tab_same hmw, ScalerNew.tab_eq_map, show (2112 : Word).toNat = 2112 from rfl] at *
          rw [hvmap, hr_eq] }
      buf := (EqKernel.eListAt_same hmw P _).trans (hbuf₂.trans hu.buf) }⟩⟩

end Rv64Verifier.Proofs.Multilinear.MleEval
