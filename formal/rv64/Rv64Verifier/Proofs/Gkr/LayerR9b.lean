import Rv64Verifier.Proofs.Gkr.LayerR9

/-!
# `keccak::verify_layer`: the three scalars

`keccak.rs:136` at `0x8000f750..0x8000f780`: the local point and its value kept in registers,
`next_scalars(3)` into `f + 960` (`r9_ns`), its `Err` returned through `0x8000fa0c`.
-/

namespace Rv64Verifier.Gkr.Layer
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Model.Gkr Rv64Verifier.Transcript Rv64Verifier.Contracts
  Rv64Verifier.Gkr Rv64Verifier.Blocks.F74
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

attribute [local rv_addr] vecPtr vecLen vecCap

/-- A transcript callee's frame, its result in the scratch slots, is one of `W9`. -/
theorem w9_tframe {s u v : MachineState} (hpre : VerifyLayerPre s) (B : Base s u) {n k K : Nat}
    (hx10 : u.getReg .x10 = s.getReg .x2 - BitVec.ofNat 64 K) (hx11 : u.getReg .x11 = s.getReg .x11)
    (hscr : ∀ a, Within a (s.getReg .x2 - BitVec.ofNat 64 K) n → Scr9 s a) (hk : k ≤ sumcheckStack)
    (F : TFrame n k u v) : DFrame u v (W9 s u v) := by
  have hb := bounds hpre
  unfold TFrame at F
  rw [hx10, hx11] at F
  simp only [stackLo, B.x2] at F
  refine F.mono fun a h ↦ ?_
  rcases h with h | h | h | h | h
  · exact Or.inl (hscr a h)
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inl (by addr_omega [h, hb, hk]))
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

/-- The scratch slot `f + 960` (`f + 1712 - 752`). -/
theorem scr_752 {s : MachineState} (hpre : VerifyLayerPre s) {n : Nat} (hn : n ≤ 48) (a : Word)
    (h : Within a (s.getReg .x2 - BitVec.ofNat 64 752) n) : Scr9 s a := by
  have hb := bounds hpre
  exact Or.inr (Or.inr (Or.inr (Or.inr (by addr_omega [h, hb, hn]))))

/-- `0x8000fa0c`: `next_scalars`' `Err` (its payload in `s8` and `s3`) into the result, then
return. -/
theorem err_fa0c {s u : MachineState} (hpre : VerifyLayerPre s) (B : Base s u)
    (hpc : u.pc = 0x8000fa0c) (hout : u.getMem (s.getReg .x2 - 1664) = s.getReg .x10)
    (hf : Fails s) : ∃ t, Reaches Image.code u t ∧ Ret s t := by
  have hb := bounds hpre
  have ho := hpre.out
  have hos := hpre.outStack
  have hof := hpre.outFree
  obtain ⟨w, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000fa0c_spec hpc (by
    rv_eval [B.x2, hout]
    and_intros <;> first
      | valid_access hpre.stack.valid [hb]
      | (refine Region.valid ho ?_ ?_ ?_ <;> addr_omega [ho]))
  have m0 := b8000fa0c_m2 h₁
  rw [B.x2] at m0
  rv_eval [hout] at m0
  have f₁ : MemFrame u w (s.getReg .x10) 24 := h₁.memFrame (by
    rv_eval [B.x2, hout]; and_intros <;> addr_omega [ho])
  have x2w : w.getReg .x2 = s.getReg .x2 - 1712 := (b8000fa0c_keeps h₁ .x2 (by decide)).trans B.x2
  have hN : w.getMem nextAddr = u.getMem nextAddr := f₁ _ (by addr_omega [ho, hof])
  have Bw : Base s w := B.next hpre x2w
    ⟨by simp only [heapNext, hN]; exact B.heap.lo, by simp only [heapNext, hN]; exact B.heap.hi⟩
    (by simp only [heapNext, hN]; exact le_refl _) (DFrame.of_memFrame f₁) fun a ha ↦
      ⟨Or.inl (by addr_omega [ha]), by unfold verifyLayerStack at hb hos; addr_omega [ha, hos, hb]⟩
  obtain ⟨t, hr₂, pc, pres, same⟩ := exit hpre (b8000fa0c_pc h₁) Bw.x2 Bw.saved
  exact ⟨t, hr₁.trans hr₂, pc, pres, post_err Bw m0 hf same⟩

/-- The local point, the value and the three scalars, at `0x8000f780`. -/
structure S10 (s v : MachineState) (ip : Word) (c : E) (point : List E) (scale : E)
    (lp : List E) (lv : E) (t : List E) : Prop where
  pc : v.pc = 0x8000f780
  base : Base s v
  k8 : K8 s v ip c point scale
  x20 : v.getReg .x20 = s.getReg .x11
  x26 : v.getReg .x26 = 16
  lvL : limbs lv = (v.getReg .x8, v.getReg .x23, v.getReg .x21)
  x9 : (v.getReg .x9).toNat = lp.length
  lpB : NewBuf s v (v.getReg .x22) (24 * lp.length) 8
  lpE : eListAt v (v.getReg .x22) lp.length = lp
  tl : t.length = 3
  tB : NewBuf s v (v.getReg .x24) (24 * (v.getReg .x19).toNat) 8
  tE : eListAt v (v.getReg .x24) (v.getReg .x19).toNat = t
  rest : Rest s v (TM.require (check2 (claimAt s (lClaim s)).weights
    (sumE (instanceWeightsRust c)) scale lv lp t) >>= fun _ ↦
      stage7 (instanceWeightsRust c) point (eqKernelRust (lp.take 6)) (eqKernelRust (lp.drop 6)) t)

theorem eListAt_congr {u v : MachineState} (h : ∀ a, v.getMem a = u.getMem a) (p : Word) (n : Nat) :
    eListAt v p n = eListAt u p n := by
  simp only [Rv64Verifier.eListAt, Rv64Verifier.eAt, h]

set_option maxHeartbeats 16000000 in
/-- `0x8000f750`: the value into `s0`, `s7`, `s5`, `next_scalars(3)` into `f + 960`; its `Err`
returned (`0x8000fa0c`). -/
theorem r9_ns (hNS : NextScalarsSpec) {s v : MachineState} {ip : Word} {c : E}
    {point lp : List E} {scale lv : E} (hpre : VerifyLayerPre s)
    (S : S9 s v ip c point scale lp lv) :
    ∃ u, Reaches Image.code v u ∧ ((∃ t, S10 s u ip c point scale lp lv t) ∨ Ret s u ∨
      Dead Image.code u) := by
  have hb := bounds hpre
  have B := S.base
  unfold verifyLayerStack at hb
  -- the local point
  have hl := S.lpV.vec.len
  have hbuf := S.lpV.buf
  have hel := S.lpV.elems
  simp only [vecPtr, vecLen, vecCap, vecEs] at hl hbuf hel
  rv_eval [] at hl hbuf hel
  rw [← S.x9] at hl hel
  rw [← S.x22] at hbuf hel
  have hlen : (v.getReg .x9).toNat = lp.length := by rw [← hel, eListAt_length]
  have lpB : NewBuf s v (v.getReg .x22) (24 * lp.length) 8 := newBuf_len hbuf (by omega)
  rw [hlen] at hel
  -- `0x8000f750`
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000f750_spec S.pc (by
    rv_eval [B.x2]; and_intros <;> valid_access hpre.stack.valid [hb])
  have k₁ := b8000f750_keeps h₁
  have hm₁ := b8000f750_mem_same h₁
  have x2₁ : t₁.getReg .x2 = s.getReg .x2 - 1712 := (k₁ .x2 (by decide)).trans B.x2
  have B₁ : Base s t₁ := B.same x2₁ hm₁
  have x10₁ : t₁.getReg .x10 = s.getReg .x2 - 752 := by rw [b8000f750_x10 h₁, B.x2]; rv_eval []
  have x11₁ : t₁.getReg .x11 = s.getReg .x11 := by rw [b8000f750_x11 h₁, S.x20]
  have x12₁ := b8000f750_x12 h₁
  have lvL₁ : limbs lv = (t₁.getReg .x8, t₁.getReg .x23, t₁.getReg .x21) := by
    rw [← S.lvE, limbs_eAt, b8000f750_x8 h₁, b8000f750_x23 h₁, b8000f750_x21 h₁, B.x2]
    rv_eval []
  have hN₁ : heapNext t₁ = heapNext v := by simp only [heapNext, hm₁]
  have K₁ : K8 s t₁ ip c point scale := S.k8.keep hpre B.heap B₁.heap (le_of_eq hN₁.symm)
    (DFrame.of_same hm₁ _)
  have R₀ : Rest s t₁ (TM.nextScalars 3 >>= fun t ↦ TM.require (check2
      (claimAt s (lClaim s)).weights (sumE (instanceWeightsRust c)) scale lv lp t) >>= fun _ ↦
        stage7 (instanceWeightsRust c) point (eqKernelRust (lp.take 6))
          (eqKernelRust (lp.drop 6)) t) :=
    S.rest.keep fun T hT ↦ transcriptAt_congr hm₁ hT
  -- `next_scalars(3)`
  have hns : NextScalarsPre t₁ :=
    B₁.tpre hpre 752 x10₁ x11₁ (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨t₂, hr₂, ⟨hpc₂, hp₂, NP⟩ | hd⟩ := hNS.call hr₁ (b8000f750_pc h₁) hns
  swap
  · exact ⟨_, hr₂, Or.inr (Or.inr hd)⟩
  have x2₂ : t₂.getReg .x2 = s.getReg .x2 - 1712 := (hp₂.reg .x2).trans x2₁
  have B₂ : Base s t₂ := B₁.next hpre x2₂ NP.heap NP.mono NP.frame fun a ha ↦
    tframe_lw hpre B₁ 752 x10₁ x11₁ (by decide) (by decide) (by decide) NP.heap a ha
  have F₂ : DFrame t₁ t₂ (W9 s t₁ t₂) :=
    w9_tframe hpre B₁ x10₁ x11₁ (scr_752 hpre (by decide)) (by decide) NP.frame
  have K₂ : K8 s t₂ ip c point scale := K₁.keep hpre B₁.heap NP.heap NP.mono F₂
  have lpB₁ : NewBuf s t₁ (v.getReg .x22) (24 * lp.length) 8 := newBuf_mono lpB (le_of_eq hN₁.symm)
  have lpE₂ : eListAt t₂ (v.getReg .x22) lp.length = lp := by
    rw [w9_eList hpre B₁.heap F₂ lpB₁ (le_refl _), eListAt_congr hm₁, hel]
  have hv (T : TState) (hT : TranscriptAt t₁ (s.getReg .x11) T) :
      match (TM.nextScalars 3).run T with
      | some (xs, T') => vecCap t₂ (s.getReg .x2 - 752) ≠ errNiche ∧
          NewVecE t₁ t₂ (s.getReg .x2 - 752) xs ∧ TranscriptAt t₂ (s.getReg .x11) T'
      | none => vecCap t₂ (s.getReg .x2 - 752) = errNiche := by
    have h := NP.value T (by rw [x11₁]; exact hT)
    rw [x10₁, x11₁, x12₁] at h
    exact h
  -- `0x8000f770`: `Err` or the scalars
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000f770_spec
    (by rw [hpc₂, returnAddress_eq, b8000f750_x1 h₁]; decide) (by
      rv_eval [x2₂]; and_intros <;> valid_access hpre.stack.valid [hb])
  have k₃ := b8000f770_keeps h₃
  have hm₃ := b8000f770_mem_same h₃
  have x2₃ : t₃.getReg .x2 = s.getReg .x2 - 1712 := (k₃ .x2 (by decide)).trans x2₂
  have B₃ : Base s t₃ := B₂.same x2₃ hm₃
  have hN₃ : heapNext t₃ = heapNext t₂ := by simp only [heapNext, hm₃]
  have K₃ : K8 s t₃ ip c point scale := K₂.keep hpre NP.heap B₃.heap (le_of_eq hN₃.symm)
    (DFrame.of_same hm₃ _)
  have x18₂ : t₂.getReg .x18 = errNiche := by
    rw [hp₂.reg .x18, k₁ .x18 (by decide), S.x18]
  have cap₂ : t₂.getMem (t₂.getReg .x2 + 960) = t₂.getMem (s.getReg .x2 - 752) := by
    rw [x2₂]; rv_eval []
  by_cases herr : t₂.getMem (s.getReg .x2 - 752) = errNiche
  · have hf : Fails s := R₀.fail fun T hT ↦ by
      have e := hv T hT
      generalize (TM.nextScalars 3).run T = o at e ⊢
      rcases o with _ | ⟨xs, T'⟩
      · rfl
      · exact absurd herr e.1
    obtain ⟨t, hr, ht⟩ := err_fa0c hpre B₃
      (b8000f770_pc_taken h₃ (by rw [cap₂, x18₂]; exact herr)) (by rw [hm₃]; exact K₂.out) hf
    exact ⟨t, hr₂.trans (hr₃.trans hr), Or.inr (Or.inl ht)⟩
  obtain ⟨T₀, hT₀⟩ := Open.exists_T t₁ (s.getReg .x11)
  have h₀ := hv T₀ hT₀
  generalize hx : (TM.nextScalars 3).run T₀ = o at h₀
  rcases o with _ | ⟨t, T₀'⟩
  · exact absurd h₀ herr
  obtain ⟨-, htV, -⟩ := h₀
  have tl : t.length = 3 := nextScalars_length hx
  have tV : NewVecE s t₂ (s.getReg .x2 - 752) t := Open.newVecE_mono htV B₁.mono
  have tl2 := tV.vec.len
  have tb := tV.buf
  have te := tV.elems
  simp only [vecPtr, vecLen, vecCap, vecEs] at tl2 tb te
  rv_eval [] at tl2 tb te
  have x24₃ : t₃.getReg .x24 = t₂.getMem (s.getReg .x2 - 744) := by
    rw [b8000f770_x24 h₃, x2₂]; rv_eval []
  have x19₃ : t₃.getReg .x19 = t₂.getMem (s.getReg .x2 - 736) := by
    rw [b8000f770_x19 h₃, x2₂]; rv_eval []
  refine ⟨t₃, hr₂.trans hr₃, Or.inl ⟨t, {
    pc := b8000f770_pc_not_taken h₃ (by rw [cap₂, x18₂]; exact herr)
    base := B₃
    k8 := K₃
    x20 := by rw [k₃ .x20 (by decide), hp₂.reg .x20, k₁ .x20 (by decide), S.x20]
    x26 := by rw [k₃ .x26 (by decide), hp₂.reg .x26, k₁ .x26 (by decide), S.x26]
    lvL := by
      rw [lvL₁, k₃ .x8 (by decide), k₃ .x23 (by decide), k₃ .x21 (by decide), hp₂.reg .x8,
        hp₂.reg .x23, hp₂.reg .x21]
    x9 := by rw [k₃ .x9 (by decide), hp₂.reg .x9, k₁ .x9 (by decide)]; exact hlen
    lpB := by
      rw [k₃ .x22 (by decide), hp₂.reg .x22, k₁ .x22 (by decide)]
      exact newBuf_mono lpB (by rw [hN₃, ← hN₁]; exact NP.mono)
    lpE := by
      rw [k₃ .x22 (by decide), hp₂.reg .x22, k₁ .x22 (by decide), eListAt_congr hm₃]; exact lpE₂
    tl := tl
    tB := by
      rw [x24₃, x19₃]
      exact newBuf_mono (newBuf_len tb (by omega)) (le_of_eq hN₃.symm)
    tE := by rw [x24₃, x19₃, eListAt_congr hm₃]; exact te
    rest := R₀.step (x := t) fun T hT ↦ by
      have h := hv T hT
      generalize (TM.nextScalars 3).run T = o at h ⊢
      rcases o with _ | ⟨xs, T'⟩
      · exact absurd h herr
      obtain ⟨-, hxs, hT'⟩ := h
      have e1 : xs = t := hxs.elems.symm.trans htV.elems
      subst e1
      exact ⟨T', rfl, transcriptAt_congr hm₃ hT'⟩ }⟩⟩

end Rv64Verifier.Gkr.Layer
