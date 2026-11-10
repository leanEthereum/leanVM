import Rv64Verifier.Proofs.Gkr.LayerR9b

/-!
# `keccak::verify_layer`: the local point's two kernels

`keccak.rs:137-138` at `0x8000f780..0x8000f7e0`: at least six coordinates (else a trap),
`eq_kernel(local[..6])` into `f + 144` (`r9_ek1`), `eq_kernel(local[6..])` into `f + 168`, their
lengths and pointers and `&t[2]` into the slots the second check reads (`r9_ek2`).
-/

namespace Rv64Verifier.Gkr.Layer
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Model.Gkr Rv64Verifier.Transcript Rv64Verifier.Contracts
  Rv64Verifier.Gkr Rv64Verifier.Blocks.F74
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

attribute [local rv_addr] vecPtr vecLen vecCap

theorem elist_take (u : MachineState) (p : Word) {k n : Nat} (h : k ≤ n) :
    (eListAt u p n).take k = eListAt u p k := by
  apply List.ext_getElem (by simp [eListAt_length, h])
  intro i h1 h2
  simp only [List.getElem_take, eListAt_getElem]

/-- `eq_kernel`'s frame, its result in the scratch slots, is one of `W9`. -/
theorem w9_cframe {s u v : MachineState} (hpre : VerifyLayerPre s) (B : Base s u) {n k : Nat}
    (K : Nat) (hscr : ∀ a, Within a (s.getReg .x2 - BitVec.ofNat 64 K) n → Scr9 s a)
    (hk : k ≤ sumcheckStack)
    (F : DFrame u v fun a ↦ Within a (s.getReg .x2 - BitVec.ofNat 64 K) n ∨
      Within a (stackLo u k) k ∨ Within a nextAddr 8 ∨ Fresh u v a) : DFrame u v (W9 s u v) := by
  have hb := bounds hpre
  simp only [stackLo, B.x2] at F
  refine F.mono fun a h ↦ ?_
  rcases h with h | h | h | h
  · exact Or.inl (hscr a h)
  · exact Or.inr (Or.inl (by addr_omega [h, hb, hk]))
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

/-- A `Vec` whose header a frame keeps, its buffer allocated since the entry. -/
theorem newVecE_keep {s w v : MachineState} (hpre : VerifyLayerPre s) (hH : HeapOk w)
    (hN : heapNext w ≤ heapNext v) (F : DFrame w v (W9 s w v)) {a : Word} {xs : List E}
    (h0 : v.getMem a = w.getMem a) (h1 : v.getMem (a + 8) = w.getMem (a + 8))
    (h2 : v.getMem (a + 16) = w.getMem (a + 16)) (hv : NewVecE s w a xs) : NewVecE s v a xs := by
  obtain ⟨⟨hr, hl⟩, hbuf, he⟩ := hv
  have p0 : vecCap v a = vecCap w a := h0
  have p1 : vecPtr v a = vecPtr w a := h1
  have p2 : vecLen v a = vecLen w a := h2
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · simp only [RawVecOk, Buf, p0, p1] at hr ⊢
    exact ⟨hr.1, hr.2.imp_right fun h ↦ ⟨h.1, h.2.trans hN⟩⟩
  · rw [p0, p2]; exact hl
  · rw [p0, p1]; exact newBuf_mono hbuf hN
  · rw [← he]
    simp only [vecEs, p1, p2]
    exact w9_eList hpre hH F hbuf (by omega)

/-- After the first kernel, at `0x8000f79c`. -/
structure S11 (s v : MachineState) (ip : Word) (c : E) (point : List E) (scale : E)
    (lp : List E) (lv : E) (t : List E) : Prop where
  pc : v.pc = 0x8000f79c
  base : Base s v
  k8 : K8 s v ip c point scale
  x20 : v.getReg .x20 = s.getReg .x11
  x26 : v.getReg .x26 = 16
  lvL : limbs lv = (v.getReg .x8, v.getReg .x23, v.getReg .x21)
  x9 : (v.getReg .x9).toNat = lp.length
  h6 : 6 ≤ lp.length
  lpB : NewBuf s v (v.getReg .x22) (24 * lp.length) 8
  lpE : eListAt v (v.getReg .x22) lp.length = lp
  tl : t.length = 3
  tB : NewBuf s v (v.getReg .x24) (24 * (v.getReg .x19).toNat) 8
  tE : eListAt v (v.getReg .x24) (v.getReg .x19).toNat = t
  ezV : NewVecE s v (s.getReg .x2 - 1568) (eqKernelRust (lp.take 6))
  rest : Rest s v (TM.require (check2 (claimAt s (lClaim s)).weights
    (sumE (instanceWeightsRust c)) scale lv lp t) >>= fun _ ↦
      stage7 (instanceWeightsRust c) point (eqKernelRust (lp.take 6)) (eqKernelRust (lp.drop 6)) t)

set_option maxHeartbeats 16000000 in
/-- `0x8000f780`: at least six coordinates, else a trap; `eq_kernel(local[..6])` into
`f + 144`. -/
theorem r9_ek1 (hEK : EqKernelSpec) {s v : MachineState} {ip : Word} {c : E}
    {point lp t : List E} {scale lv : E} (hpre : VerifyLayerPre s)
    (S : S10 s v ip c point scale lp lv t) :
    ∃ u, Reaches Image.code v u ∧ (S11 s u ip c point scale lp lv t ∨ Dead Image.code u) := by
  have hb := bounds hpre
  have B := S.base
  have hnx := hpre.stack.next
  have hab := hpre.stack.above
  have hsm := hpre.stack.mapped (by decide) (by decide)
  have hrs := hpre.stack.rodata
  have hlo := hpre.heap.lo
  simp only [stackLo] at hnx hab hrs
  unfold verifyLayerStack at hb hnx hab hsm hrs
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000f780_spec S.pc trivial
  have k₁ := b8000f780_keeps h₁
  have hm₁ := b8000f780_mem_same h₁
  have h5w : ((5 : Word)).toNat = 5 := rfl
  by_cases h5 : (v.getReg .x9).toNat ≤ 5
  · exact ⟨t₁, hr₁, Or.inr (dead_of_fetch (by
      rw [b8000f780_pc_taken h₁ (by rw [h5w]; exact h5)]; exact trap))⟩
  have h6 : 6 ≤ lp.length := by rw [← S.x9]; omega
  have x2₁ : t₁.getReg .x2 = s.getReg .x2 - 1712 := (k₁ .x2 (by decide)).trans B.x2
  obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000f788_spec
    (b8000f780_pc_not_taken h₁ (by rw [h5w]; omega)) trivial
  have k₂ := b8000f788_keeps h₂
  have hm₂ := b8000f788_mem_same h₂
  have x2₂ : t₂.getReg .x2 = s.getReg .x2 - 1712 := (k₂ .x2 (by decide)).trans x2₁
  have hm12 (a : Word) : t₂.getMem a = v.getMem a := by rw [hm₂, hm₁]
  have B₂ : Base s t₂ := B.same x2₂ hm12
  have x10₂ : t₂.getReg .x10 = s.getReg .x2 - 1568 := by rw [b8000f788_x10 h₂, x2₁]; rv_eval []
  have x11₂ : t₂.getReg .x11 = v.getReg .x22 := by rw [b8000f788_x11 h₂, k₁ .x22 (by decide)]
  have x12₂ : (t₂.getReg .x12).toNat = 6 := by rw [b8000f788_x12 h₂]; rfl
  have hN₂ : heapNext t₂ = heapNext v := by simp only [heapNext, hm12]
  have hHv := B.heap.hi
  obtain ⟨la, lr⟩ := S.lpB
  have lr' : heapNext s ≤ (v.getReg .x22).toNat ∧
      (v.getReg .x22).toNat + 24 * lp.length ≤ heapNext v := by
    rcases lr with h | h
    · omega
    · exact h
  have hek : EqKernelPre t₂ := {
    heap := B₂.heap
    out := by rw [x10₂]; addr_omega [hb, hsm]
    point := by rw [x12₂, x11₂]; right; addr_omega [la, lr', h6, hHv, hlo]
    stack := hpre.stack.sub 1712 x2₂ (by unfold verifyLayerStack; decide) (by decide) (by decide)
      (by decide) (by decide)
    outFree := by rw [x10₂]; refine ⟨Or.inr ?_, ?_⟩ <;> addr_omega [hb, hab, hnx]
    pointFree := by
      rw [x12₂, x11₂]; right; refine ⟨Or.inl ?_, ?_⟩ <;> addr_omega [lr', h6, hN₂, hHv]
    outStack := by rw [x10₂]; simp only [stackLo, x2₂]; addr_omega [hb]
    pointStack := by
      rw [x12₂, x11₂]; simp only [stackLo, x2₂]; addr_omega [lr', h6, hHv, hab, hb]
    pointOut := by rw [x12₂, x11₂, x10₂]; addr_omega [lr', h6, hHv, hab, hb]
    rodata := B₂.rodata hpre
    outRodata := by rw [x10₂]; addr_omega [hrs, hb] }
  obtain ⟨e₁, hr₃, ⟨hpc₃, hp₃, EP⟩ | hd⟩ := hEK.call (hr₁.trans hr₂) (b8000f788_pc h₂) hek
  swap
  · exact ⟨_, hr₃, Or.inr hd⟩
  have G₃ := EP.frame
  have V₃ := EP.value
  rw [x10₂] at G₃ V₃
  rw [x11₂, x12₂] at V₃
  have x2e : e₁.getReg .x2 = s.getReg .x2 - 1712 := (hp₃.reg .x2).trans x2₂
  have B₃ : Base s e₁ := B₂.next hpre x2e EP.heap EP.mono G₃ fun a ha ↦
    cframe_lw hpre B₂ 1568 (by decide) (by decide) (by decide) EP.heap rfl a ha
  have F₃ : DFrame t₂ e₁ (W9 s t₂ e₁) := w9_cframe hpre B₂ 1568
    (fun a h ↦ Or.inr (Or.inr (Or.inl (by addr_omega [h, hb])))) (by decide) G₃
  have F₃b : DFrame t₂ e₁ (BodyW s t₂ e₁) := G₃.mono fun a ha ↦
    cframe_body hpre B₂ 1568 (by decide) (by decide) (by decide) (le_refl _) (le_refl _) rfl a ha
  have K₃ : K8 s e₁ ip c point scale :=
    (S.k8.keep hpre B.heap B₂.heap (le_of_eq hN₂.symm) (DFrame.of_same hm12 _)).keep hpre B₂.heap
      EP.heap EP.mono F₃
  have lpB₂ : NewBuf s t₂ (v.getReg .x22) (24 * lp.length) 8 :=
    newBuf_mono S.lpB (le_of_eq hN₂.symm)
  have tB₂ : NewBuf s t₂ (v.getReg .x24) (24 * (v.getReg .x19).toNat) 8 :=
    newBuf_mono S.tB (le_of_eq hN₂.symm)
  have hmono : heapNext t₂ ≤ heapNext e₁ := EP.mono
  have e6 : eListAt t₂ (v.getReg .x22) 6 = lp.take 6 := by
    rw [eListAt_congr hm12, ← elist_take _ _ h6, S.lpE]
  rw [e6] at V₃
  refine ⟨e₁, hr₃, Or.inl {
    pc := by rw [hpc₃, returnAddress_eq, b8000f788_x1 h₂]; decide
    base := B₃
    k8 := K₃
    x20 := by rw [hp₃.reg .x20, k₂ .x20 (by decide), k₁ .x20 (by decide), S.x20]
    x26 := by rw [hp₃.reg .x26, k₂ .x26 (by decide), k₁ .x26 (by decide), S.x26]
    lvL := by
      rw [S.lvL, hp₃.reg .x8, k₂ .x8 (by decide), k₁ .x8 (by decide), hp₃.reg .x23,
        k₂ .x23 (by decide), k₁ .x23 (by decide), hp₃.reg .x21, k₂ .x21 (by decide),
        k₁ .x21 (by decide)]
    x9 := by rw [hp₃.reg .x9, k₂ .x9 (by decide), k₁ .x9 (by decide)]; exact S.x9
    h6 := h6
    lpB := by
      rw [hp₃.reg .x22, k₂ .x22 (by decide), k₁ .x22 (by decide)]; exact newBuf_mono lpB₂ hmono
    lpE := by
      rw [hp₃.reg .x22, k₂ .x22 (by decide), k₁ .x22 (by decide),
        w9_eList hpre B₂.heap F₃ lpB₂ (le_refl _), eListAt_congr hm12]
      exact S.lpE
    tl := S.tl
    tB := by
      rw [hp₃.reg .x24, k₂ .x24 (by decide), k₁ .x24 (by decide), hp₃.reg .x19,
        k₂ .x19 (by decide), k₁ .x19 (by decide)]
      exact newBuf_mono tB₂ hmono
    tE := by
      rw [hp₃.reg .x24, k₂ .x24 (by decide), k₁ .x24 (by decide), hp₃.reg .x19,
        k₂ .x19 (by decide), k₁ .x19 (by decide), w9_eList hpre B₂.heap F₃ tB₂ (le_refl _),
        eListAt_congr hm12]
      exact S.tE
    ezV := Open.newVecE_mono V₃ B₂.mono
    rest := (S.rest.keep fun T hT ↦ transcriptAt_congr hm12 hT).body hpre B₂ B₃ F₃b }⟩

/-- A `Vec`'s buffer and elements by its pointer and length. -/
theorem newVecE_parts {s u : MachineState} {a : Word} {xs : List E} (h : NewVecE s u a xs) :
    NewBuf s u (u.getMem (a + 8)) (24 * (u.getMem (a + 16)).toNat) 8 ∧
      eListAt u (u.getMem (a + 8)) (u.getMem (a + 16)).toNat = xs := by
  have hl := h.vec.len
  simp only [vecLen, vecCap] at hl
  exact ⟨newBuf_len h.buf (by simp only [vecCap]; omega), h.elems⟩

/-- The two kernels in place, at `0x8000f7e0`. -/
structure J10 (s v : MachineState) (ip : Word) (c : E) (point : List E) (scale : E)
    (lp : List E) (lv : E) (t : List E) : Prop where
  pc : v.pc = 0x8000f7e0
  base : Base s v
  k8 : K8 s v ip c point scale
  x20 : v.getReg .x20 = s.getReg .x11
  x26 : v.getReg .x26 = 16
  lvL : limbs lv = (v.getReg .x8, v.getReg .x23, v.getReg .x21)
  tl : t.length = 3
  tB : NewBuf s v (v.getReg .x24) (24 * (v.getReg .x19).toNat) 8
  tE : eListAt v (v.getReg .x24) (v.getReg .x19).toNat = t
  t2 : v.getMem (s.getReg .x2 - 1680) = v.getReg .x24 + 48
  ezB : NewBuf s v (v.getMem (s.getReg .x2 - 1632)) (24 * (v.getMem (s.getReg .x2 - 1640)).toNat) 8
  ezE : eListAt v (v.getMem (s.getReg .x2 - 1632)) (v.getMem (s.getReg .x2 - 1640)).toNat =
    eqKernelRust (lp.take 6)
  x25 : v.getReg .x25 = v.getMem (s.getReg .x2 - 1600)
  x18 : v.getReg .x18 = v.getMem (s.getReg .x2 - 1624)
  elB : NewBuf s v (v.getMem (s.getReg .x2 - 1600)) (24 * (v.getMem (s.getReg .x2 - 1624)).toNat) 8
  elE : eListAt v (v.getMem (s.getReg .x2 - 1600)) (v.getMem (s.getReg .x2 - 1624)).toNat =
    eqKernelRust (lp.drop 6)
  rest : Rest s v (TM.require (check2 (claimAt s (lClaim s)).weights
    (sumE (instanceWeightsRust c)) scale lv lp t) >>= fun _ ↦
      stage7 (instanceWeightsRust c) point (eqKernelRust (lp.take 6)) (eqKernelRust (lp.drop 6)) t)

set_option maxHeartbeats 16000000 in
/-- `0x8000f79c`: `eq_kernel(local[6..])` into `f + 168`; `0x8000f7b0`: the kernels' lengths and
pointers and `&t[2]` into the slots, and the transcript checked. -/
theorem r9_ek2 (hEK : EqKernelSpec) {s v : MachineState} {ip : Word} {c : E}
    {point lp t : List E} {scale lv : E} (hpre : VerifyLayerPre s)
    (S : S11 s v ip c point scale lp lv t) :
    ∃ u, Reaches Image.code v u ∧ (J10 s u ip c point scale lp lv t ∨ Dead Image.code u) := by
  have hb := bounds hpre
  have B := S.base
  have hnx := hpre.stack.next
  have hab := hpre.stack.above
  have hsm := hpre.stack.mapped (by decide) (by decide)
  have hrs := hpre.stack.rodata
  have hlo := hpre.heap.lo
  have hS := hpre.self.self
  have hss := hpre.selfStack
  simp only [stackLo] at hnx hab hrs hss
  unfold verifyLayerStack at hb hnx hab hsm hrs hss
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000f79c_spec S.pc trivial
  have k₁ := b8000f79c_keeps h₁
  have hm₁ := b8000f79c_mem_same h₁
  have x2₁ : t₁.getReg .x2 = s.getReg .x2 - 1712 := (k₁ .x2 (by decide)).trans B.x2
  have B₁ : Base s t₁ := B.same x2₁ hm₁
  have hN₁ : heapNext t₁ = heapNext v := by simp only [heapNext, hm₁]
  have x10₁ : t₁.getReg .x10 = s.getReg .x2 - 1544 := by rw [b8000f79c_x10 h₁, B.x2]; rv_eval []
  have x11₁ : t₁.getReg .x11 = v.getReg .x22 + 144 := b8000f79c_x11 h₁
  have h6 := S.h6
  have x12₁ : (t₁.getReg .x12).toNat = lp.length - 6 := by
    have := (v.getReg .x9).isLt
    rw [S.x9] at this
    rw [b8000f79c_x12 h₁, BitVec.toNat_sub, show (6 : Word).toNat = 6 from rfl, S.x9]
    omega
  obtain ⟨la, lr⟩ := S.lpB
  have lr' : heapNext s ≤ (v.getReg .x22).toNat ∧
      (v.getReg .x22).toNat + 24 * lp.length ≤ heapNext v := by
    rcases lr with h | h
    · omega
    · exact h
  have hHv := B.heap.hi
  have hek : EqKernelPre t₁ := {
    heap := B₁.heap
    out := by rw [x10₁]; addr_omega [hb, hsm]
    point := by
      rw [x12₁, x11₁]
      by_cases h0 : lp.length - 6 = 0
      · left; exact h0
      · right; addr_omega [la, lr', h6, h0, hHv, hlo]
    stack := hpre.stack.sub 1712 x2₁ (by unfold verifyLayerStack; decide) (by decide) (by decide)
      (by decide) (by decide)
    outFree := by rw [x10₁]; refine ⟨Or.inr ?_, ?_⟩ <;> addr_omega [hb, hab, hnx]
    pointFree := by
      rw [x12₁, x11₁]
      by_cases h0 : lp.length - 6 = 0
      · left; exact h0
      · right; refine ⟨Or.inl ?_, ?_⟩ <;> addr_omega [lr', h6, h0, hN₁, hHv]
    outStack := by rw [x10₁]; simp only [stackLo, x2₁]; addr_omega [hb]
    pointStack := by
      rw [x12₁, x11₁]; simp only [stackLo, x2₁]; addr_omega [lr', h6, hHv, hab, hb]
    pointOut := by rw [x12₁, x11₁, x10₁]; addr_omega [lr', h6, hHv, hab, hb]
    rodata := B₁.rodata hpre
    outRodata := by rw [x10₁]; addr_omega [hrs, hb] }
  obtain ⟨e₂, hr₂, ⟨hpc₂, hp₂, EP⟩ | hd⟩ := hEK.call hr₁ (b8000f79c_pc h₁) hek
  swap
  · exact ⟨_, hr₂, Or.inr hd⟩
  have G₂ := EP.frame
  have V₂ := EP.value
  rw [x10₁] at G₂ V₂
  rw [x11₁, x12₁] at V₂
  have x2₂ : e₂.getReg .x2 = s.getReg .x2 - 1712 := (hp₂.reg .x2).trans x2₁
  have B₂ : Base s e₂ := B₁.next hpre x2₂ EP.heap EP.mono G₂ fun a ha ↦
    cframe_lw hpre B₁ 1544 (by decide) (by decide) (by decide) EP.heap rfl a ha
  have F₂ : DFrame t₁ e₂ (W9 s t₁ e₂) := w9_cframe hpre B₁ 1544
    (fun a h ↦ Or.inr (Or.inr (Or.inl (by addr_omega [h, hb])))) (by decide) G₂
  have F₂b : DFrame t₁ e₂ (BodyW s t₁ e₂) := G₂.mono fun a ha ↦
    cframe_body hpre B₁ 1544 (by decide) (by decide) (by decide) (le_refl _) (le_refl _) rfl a ha
  have hmono : heapNext t₁ ≤ heapNext e₂ := EP.mono
  have hH2 := EP.heap.hi
  have K₂ : K8 s e₂ ip c point scale :=
    (S.k8.keep hpre B.heap B₁.heap (le_of_eq hN₁.symm) (DFrame.of_same hm₁ _)).keep hpre B₁.heap
      EP.heap hmono F₂
  have edrop : eListAt t₁ (v.getReg .x22 + 144) (lp.length - 6) = lp.drop 6 := by
    have e := Open.eListAt_drop v (v.getReg .x22) lp.length 6
    rw [S.lpE] at e
    rw [e, eListAt_congr hm₁, show (144 : Word) = BitVec.ofNat 64 (24 * 6) from rfl]
  rw [edrop] at V₂
  simp only [stackLo, x2₁] at G₂
  have kG (y : Word) (h1 : (s.getReg .x2).toNat - 1712 ≤ y.toNat)
      (h2 : y.toNat + 8 ≤ (s.getReg .x2).toNat - 1544 ∨
        (s.getReg .x2).toNat - 1520 ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2).toNat - 104) :
      e₂.getMem y = t₁.getMem y :=
    G₂ y fun i hi hw ↦ by
      simp only [Fresh] at hw
      rcases hw with hw | hw | hw | hw <;> addr_omega [hw, hi, h1, h2, hb, hnx, hab, hH2]
  have ezV₂ : NewVecE s e₂ (s.getReg .x2 - 1568) (eqKernelRust (lp.take 6)) :=
    newVecE_keep hpre B₁.heap hmono F₂ (kG _ (by addr_omega [hb]) (Or.inl (by addr_omega [hb])))
      (kG _ (by addr_omega [hb]) (Or.inl (by addr_omega [hb])))
      (kG _ (by addr_omega [hb]) (Or.inl (by addr_omega [hb]))) (newVecE_congr hm₁ S.ezV)
  have elV₂ : NewVecE s e₂ (s.getReg .x2 - 1544) (eqKernelRust (lp.drop 6)) :=
    Open.newVecE_mono V₂ B₁.mono
  obtain ⟨zb, ze⟩ := newVecE_parts ezV₂
  obtain ⟨lb, lE⟩ := newVecE_parts elV₂
  rv_eval [] at zb ze lb lE
  -- `0x8000f7b0`: the slots, the transcript checked
  have x20₂ : e₂.getReg .x20 = s.getReg .x11 := by rw [hp₂.reg .x20, k₁ .x20 (by decide), S.x20]
  have hck : extractByte (s.getMem (s.getReg .x11 + 360)) 0 ≠ 0 := by
    have h := hpre.checked
    simp only [Checked] at h
    rwa [← Transcript.add_ofNat_zero (s.getReg .x11 + 360),
      Runtime.byteAt_add (by addr_omega [hS]) (by decide)] at h
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000f7b0_spec
    (by rw [hpc₂, returnAddress_eq, b8000f79c_x1 h₁]; decide) (by
      rv_eval [x2₂, x20₂]
      and_intros <;> first
        | valid_access hpre.stack.valid [hb]
        | addr_omega [hb, hss, hS]
        | exact Mapped.valid hS.1 (i := 360) (by decide))
  have pc₃ : t₃.pc = 0x8000f7e0 := Sym.Expect.Holds.pc_eq h₃ (by
    rv_eval [x20₂, byte_test hpre B₂]
    exact ite_eq_right_of_eq_false _ _ (eq_false fun h ↦ hck (by
      have := congrArg BitVec.toNat (beq_iff_eq.mp h)
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.truncate_eq_setWidth] at this
      rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (BitVec.isLt _) (by decide))] at this
      simpa using this)))
  have k₃ := b8000f7b0_keeps h₃
  have f₃ := b8000f7b0_frame h₃ (by rw [x2₂]; addr_omega [hb])
  rw [x2₂] at f₃
  rv_eval [] at f₃
  have x2₃ : t₃.getReg .x2 = s.getReg .x2 - 1712 := (k₃ .x2 (by decide)).trans x2₂
  have B₃ : Base s t₃ := B₂.slots hpre x2₃ f₃ (by addr_omega [hb]) (by addr_omega [hb])
  have F₃ : DFrame e₂ t₃ (W9 s e₂ t₃) := dframe_of_writes h₃ (by
    rv_eval [x2₂]; and_intros <;> exact Or.inl (by addr_omega [hb]))
  have F₃b : DFrame e₂ t₃ (BodyW s e₂ t₃) := (DFrame.of_memFrame f₃).mono fun a h ↦
    slots_body hpre (by addr_omega [hb]) (by addr_omega [hb]) h
  have hN₃ : heapNext t₃ = heapNext e₂ := by
    simp only [heapNext]; rw [f₃ _ (by addr_omega [hb, hnx])]
  have m88 := b8000f7b0_m_x2_88 h₃
  have m112 := b8000f7b0_m_x2_112 h₃
  have m32 := b8000f7b0_m_x2_32 h₃
  have m72 := b8000f7b0_m_x2_72 h₃
  have m80 := b8000f7b0_m_x2_80 h₃
  have x18₃ := b8000f7b0_x18 h₃
  have x25₃ := b8000f7b0_x25 h₃
  rw [x2₂] at m88 m112 m72 m80 x18₃ x25₃
  rw [x2₂] at m32
  rv_eval [] at m88 m112 m32 m72 m80 x18₃ x25₃
  have tB₁ : NewBuf s t₁ (v.getReg .x24) (24 * (v.getReg .x19).toNat) 8 :=
    newBuf_mono S.tB (le_of_eq hN₁.symm)
  have tB₂ : NewBuf s e₂ (v.getReg .x24) (24 * (v.getReg .x19).toNat) 8 := newBuf_mono tB₁ hmono
  have r24 : t₃.getReg .x24 = v.getReg .x24 := by
    rw [k₃ .x24 (by decide), hp₂.reg .x24, k₁ .x24 (by decide)]
  have r19 : t₃.getReg .x19 = v.getReg .x19 := by
    rw [k₃ .x19 (by decide), hp₂.reg .x19, k₁ .x19 (by decide)]
  refine ⟨t₃, hr₂.trans hr₃, Or.inl {
    pc := pc₃
    base := B₃
    k8 := K₂.keep hpre EP.heap B₃.heap (le_of_eq hN₃.symm) F₃
    x20 := by rw [k₃ .x20 (by decide), x20₂]
    x26 := by rw [k₃ .x26 (by decide), hp₂.reg .x26, k₁ .x26 (by decide), S.x26]
    lvL := by
      rw [S.lvL, k₃ .x8 (by decide), hp₂.reg .x8, k₁ .x8 (by decide), k₃ .x23 (by decide),
        hp₂.reg .x23, k₁ .x23 (by decide), k₃ .x21 (by decide), hp₂.reg .x21,
        k₁ .x21 (by decide)]
    tl := S.tl
    tB := by rw [r24, r19]; exact newBuf_mono tB₂ (le_of_eq hN₃.symm)
    tE := by
      rw [r24, r19, w9_eList hpre EP.heap F₃ tB₂ (le_refl _),
        w9_eList hpre B₁.heap F₂ tB₁ (le_refl _), eListAt_congr hm₁]
      exact S.tE
    t2 := by rw [m32, r24, hp₂.reg .x24, k₁ .x24 (by decide)]
    ezB := by rw [m80, m72]; exact newBuf_mono zb (le_of_eq hN₃.symm)
    ezE := by rw [m80, m72, w9_eList hpre EP.heap F₃ zb (le_refl _)]; exact ze
    x25 := by rw [x25₃, m112]
    x18 := by rw [x18₃, m88]
    elB := by rw [m112, m88]; exact newBuf_mono lb (le_of_eq hN₃.symm)
    elE := by rw [m112, m88, w9_eList hpre EP.heap F₃ lb (le_refl _)]; exact lE
    rest := ((S.rest.keep fun T hT ↦ transcriptAt_congr hm₁ hT).body hpre B₁ B₂ F₂b).body hpre
      B₂ B₃ F₃b }⟩

end Rv64Verifier.Gkr.Layer
