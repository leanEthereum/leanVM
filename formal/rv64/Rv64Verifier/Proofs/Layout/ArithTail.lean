import Rv64Verifier.Proofs.Layout.ArithCols

/-!
# `flushes_arith`: from the result to the return

`0x80005bc8` `memcpy`s the result's three forms to `sp' + 80`; `0x80005bd8` calls `prod(sp' + 320,
fp, o_c, 0)` and `0x80005bf0` `memory(sp' + 8, sp' + 320, cnt_c, sp' + 80)`; `0x80005c08` copies the
`Flushes` to `a0`, restores and returns.
-/

namespace Rv64Verifier.Layout.Arith
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.FieldContracts
  Rv64Verifier.Blocks.F19 Rv64Verifier.Model.LayoutMirror
open Rv64Verifier.Layout.Limb (Held)

/-- A `Vec<Vec<Form>>` whose header was copied from `a'` to `a`, its deep footprint untouched, is
the same `Vec`. -/
theorem formVecsOf_move {s t : MachineState} {w : Word → Prop} (h : DFrame s t w) {a a' : Word}
    (hok : FormVecsOk s a') (h0 : t.getMem a = s.getMem a')
    (h8 : t.getMem (a + 8) = s.getMem (a' + 8))
    (h16 : t.getMem (a + 16) = s.getMem (a' + 16)) (hd : ∀ x, formVecsDeep s a' x → ¬ w x)
    (hheap : HeapOk s) (hmono : heapNext s ≤ heapNext t) :
    formVecsOf t a = formVecsOf s a' ∧ FormVecsOk t a ∧ formVecsDeep t a = formVecsDeep s a' ∧
      formVecsBuf t a = formVecsBuf s a' := by
  have hcp : vecCap t a = vecCap s a' := h0
  have hptr : vecPtr t a = vecPtr s a' := h8
  have hln : vecLen t a = vecLen s a' := h16
  have hb := vecBuf_bounds hok.vec (by decide)
  have hlen := hok.vec.len
  have hhi := hheap.hi
  have hslot (i : Nat) (hi : i < (vecLen s a').toNat) (k : Nat) (hk : k + 8 ≤ 24) :
      t.getMem (vecPtr s a' + BitVec.ofNat 64 (24 * i) + BitVec.ofNat 64 k) =
        s.getMem (vecPtr s a' + BitVec.ofNat 64 (24 * i) + BitVec.ofNat 64 k) := by
    rcases hb.2 with h0 | h0
    · omega
    · exact h.getMem_of (fun x hx ↦ hd x (Or.inl (by
        simp only [formVecsBuf]; addr_omega [hx, h0, hi, hlen, hk, hhi])))
        (by addr_omega [h0, hi, hlen, hk, hhi])
  have hel (i : Nat) (hi : i < (vecLen s a').toNat) :=
    formVecOf_moved h (e := vecPtr s a' + BitVec.ofNat 64 (24 * i))
      (e' := vecPtr s a' + BitVec.ofNat 64 (24 * i))
      (by simpa using hslot i hi 0 (by decide)) (hslot i hi 8 (by decide))
      (hslot i hi 16 (by decide)) (hok.elems i hi) (fun x hx ↦ hd x (Or.inr ⟨i, hi, hx⟩))
      hheap hmono
  have hbuf : formVecsBuf t a = formVecsBuf s a' := by
    funext x; simp only [formVecsBuf, hptr, hcp]
  refine ⟨?_, ⟨⟨?_, ?_⟩, fun i hi ↦ ?_, fun i hi x hx ↦ ?_⟩, ?_, hbuf⟩
  · simp only [formVecsOf, hptr, hln]
    exact List.map_congr_left fun i hm ↦ (hel i (List.mem_range.mp hm)).1
  · have hraw := hok.vec.raw
    simp only [RawVecOk, Buf, hptr, hcp] at hraw ⊢
    exact ⟨hraw.1, hraw.2.imp id fun h' ↦ ⟨h'.1, Nat.le_trans h'.2 hmono⟩⟩
  · rw [hcp, hln]; exact hlen
  · rw [hln] at hi; rw [hptr]; exact (hel i hi).2.1
  · rw [hln] at hi; rw [hptr, (hel i hi).2.2] at hx; rw [hbuf]; exact hok.sep i hi x hx
  · funext x
    apply propext
    simp only [formVecsDeep, hbuf, hptr, hln]
    refine or_congr Iff.rfl (exists_congr fun i ↦
      ⟨fun ⟨hi, hx⟩ ↦ ⟨hi, ?_⟩, fun ⟨hi, hx⟩ ↦ ⟨hi, ?_⟩⟩)
    · rwa [(hel i hi).2.2] at hx
    · rwa [(hel i hi).2.2]

/-- A `Flushes` whose header was copied from `a'` to `a`, its deep footprint untouched and apart
from `a`'s header, is the same `Flushes`. -/
theorem flushesOf_move {s t : MachineState} {w : Word → Prop} (h : DFrame s t w) {a a' : Word}
    (hok : FlushesOk s a') (g0 : t.getMem a = s.getMem a')
    (g8 : t.getMem (a + 8) = s.getMem (a' + 8))
    (g16 : t.getMem (a + 16) = s.getMem (a' + 16)) (g24 : t.getMem (a + 24) = s.getMem (a' + 24))
    (g32 : t.getMem (a + 24 + 8) = s.getMem (a' + 24 + 8))
    (g40 : t.getMem (a + 24 + 16) = s.getMem (a' + 24 + 16))
    (hd : ∀ x, flushesDeep s a' x → ¬ w x) (hh : ∀ x, Within x a 48 → ¬ flushesDeep s a' x)
    (hheap : HeapOk s) (hmono : heapNext s ≤ heapNext t) :
    flushesOf t a = flushesOf s a' ∧ FlushesOk t a ∧ flushesDeep t a = flushesDeep s a' := by
  have h1 := formVecsOf_move h hok.push g0 g8 g16 (fun x hx ↦ hd x (Or.inl hx)) hheap hmono
  have h2 := formVecsOf_move h hok.pull g24 g32 g40 (fun x hx ↦ hd x (Or.inr hx)) hheap hmono
  have hdeep : flushesDeep t a = flushesDeep s a' := by
    funext x; simp only [flushesDeep, h1.2.2.1, h2.2.2.1]
  refine ⟨by simp only [flushesOf, h1.1, h2.1], ⟨h1.2.1, h2.2.1, ?_, ?_, ?_⟩, hdeep⟩
  · rw [h1.2.2.2, h2.2.2.1]; exact hok.pushPull
  · rw [h2.2.2.2, h1.2.2.1]; exact hok.pullPush
  · rw [hdeep]; exact hh

/-- At the `memcpy` of the result: its three forms from `src`, held from `L` on. -/
structure AtTail (s u : MachineState) (src : Word) (L : Nat) (f0 f1 f2 : FormRust) : Prop
    extends Inv s u where
  pc : u.pc = 0x80005bc8
  x11 : u.getReg .x11 = src
  srcAt : src = s.getReg .x2 - 136 ∨ src = s.getReg .x2 - 328
  hL : L ≤ heapNext u
  fl : FHeld s u (flCols (s.getReg .x11).toNat) L
  r0 : Held u src f0 L (heapNext u)
  r1 : Held u (src + 24) f1 L (heapNext u)
  r2 : Held u (src + 48) f2 L (heapNext u)

/-- The `memcpy` to `sp' + 80`, and `prod(sp' + 320, fp, o_c, 0)`. -/
structure AtMemory (s u : MachineState) (L : Nat) (f0 f1 f2 : FormRust) : Prop extends Inv s u where
  pc : u.pc = 0x800051b0
  x1 : u.getReg .x1 = 0x80005c08
  x10 : u.getReg .x10 = s.getReg .x2 - 472
  x11 : u.getReg .x11 = s.getReg .x2 - 160
  x12 : u.getReg .x12 = 13
  x13 : u.getReg .x13 = s.getReg .x2 - 400
  fl : FHeld s u (flCols (s.getReg .x11).toNat) L
  hL : L ≤ heapNext u
  addr : Held u (s.getReg .x2 - 160) (prodRust 1 4 0) L (heapNext u)
  v0 : Held u (s.getReg .x2 - 400) f0 L (heapNext u)
  v1 : Held u (s.getReg .x2 - 376) f1 L (heapNext u)
  v2 : Held u (s.getReg .x2 - 352) f2 L (heapNext u)

theorem toMemory (hM : MemcpySpec 0x800126e4) (hP : ProdSpec) {s u0 u : MachineState} {src : Word}
    {L : Nat} {f0 f1 f2 : FormRust} (hpre : FlushesArithPre s) (hr : Reaches Image.code u0 u)
    (A : AtTail s u src L f0 f1 f2) :
    ∃ v, Reaches Image.code u0 v ∧ (AtMemory s v L f0 f1 f2 ∨ Dead Image.code v) := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have hhi := stack_high hpre
  have c := A.toInv
  have x2 := c.x2
  have hs := A.srcAt
  have hsrc : (s.getReg .x2).toNat - 328 ≤ src.toNat ∧ src.toNat + 72 ≤ (s.getReg .x2).toNat - 64 ∧
      src.toNat % 8 = 0 := by rcases hs with h | h <;> rw [h] <;> addr_omega [hsb]
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80005bc8_spec A.pc trivial
  have k₁ := b80005bc8_keeps h₁
  have hm₁ := b80005bc8_mem_same h₁
  have c₁ := c.same hpre hm₁ fun r hr ↦ k₁ r (mem_of_mem hr _)
  have hn₁ : heapNext t₁ = heapNext u := by simp only [heapNext, hm₁]
  have x10₁ : t₁.getReg .x10 = s.getReg .x2 - 400 := by rw [b80005bc8_x10 h₁, x2]; rv_eval []
  have x11₁ : t₁.getReg .x11 = src := by rw [k₁ .x11 (by decide), A.x11]
  have x12₁ := b80005bc8_x12 h₁
  have x2₁ := c₁.x2
  have hmc : MemcpyPre t₁ := {
    dst := by rw [x10₁, x12₁]; addr_omega [hsb, hhi]
    src := by rw [x11₁, x12₁]; addr_omega [hsb, hhi, hsrc]
    apart := by rw [x10₁, x11₁, x12₁]; addr_omega [hsb, hsrc]
    stack := (hpre.stack.inner (k := 480) x2₁ (by decide) (by decide) (by decide) (by decide)
      (by decide)).toStackOk
    dstStack := by rw [x10₁, x12₁]; simp only [stackLo, memcpyStack]; rw [x2₁]; addr_omega [hsb]
    srcStack := by
      rw [x11₁, x12₁]; simp only [stackLo, memcpyStack]; rw [x2₁]; addr_omega [hsb, hsrc] }
  obtain ⟨m, hr₂, ⟨hpc₂, hpres₂, hmp⟩ | hdead⟩ := hM.call (hr.trans hr₁) (b80005bc8_pc h₁) hmc
  swap
  · exact ⟨m, hr₂, Or.inr hdead⟩
  have hmf := hmp.frame.dframe
  have hb := hmp.bytes
  rw [x10₁, x11₁, x12₁] at hb
  rw [x10₁, x12₁, show stackLo t₁ memcpyStack = s.getReg .x2 - 496 by
    simp only [stackLo, x2₁, memcpyStack]; rv_eval []] at hmf
  have hn₂ : heapNext m = heapNext t₁ := by
    simp only [heapNext]
    rw [hmf.getMem_of (fun x hx h ↦ by rcases h with h | h <;> addr_omega [hx, h, hsb, hnx])
      (by decide)]
  have hhu := c₁.heap.hi
  have hL := A.hL
  have hW : ∀ x, (Within x (s.getReg .x2 - 400) (BitVec.toNat (72 : Word)) ∨
      Within x (s.getReg .x2 - 496) memcpyStack) → L ≤ x.toNat → heapNext u ≤ x.toNat :=
    fun x h _ ↦ by
      simp only [memcpyStack] at h; rcases h with h | h <;> addr_omega [h, hsb, hab, hhu, hn₁]
  have c₂ := c₁.step hpre hmf (fun x h ↦ Or.inl (by rcases h with h | h <;> addr_omega [h, hsb]))
    ⟨hn₂ ▸ c₁.heap.lo, hn₂ ▸ c₁.heap.hi⟩ hn₂.ge (keepRegs_of hpres₂)
  have h8a : (s.getReg .x2 - 400).toNat % 8 = 0 := by addr_omega [hsb]
  have g (k : Nat) (hk : k % 8 = 0) (hkN : k + 8 ≤ 72) (a b : Word)
      (ha : a = s.getReg .x2 - 400 + BitVec.ofNat 64 k)
      (hb' : b = src + BitVec.ofNat 64 k) : m.getMem a = t₁.getMem b := by
    subst ha hb'
    exact getMem_eq_of_bytesAt hb h8a hsrc.2.2 hk hkN
  have r0 := A.r0.same c.heap hm₁ (by addr_omega [hsrc])
  have r1 := A.r1.same c.heap hm₁ (by addr_omega [hsrc])
  have r2 := A.r2.same c.heap hm₁ (by addr_omega [hsrc])
  have v0 := moveHeld (e := s.getReg .x2 - 400) r0 hmf c₁.heap hn₂.ge hW
    (g 0 (by decide) (by decide) _ _ (by addr_omega [hsb]) (by addr_omega [hsrc]))
    (g 8 (by decide) (by decide) _ _ (by addr_omega [hsb]) (by addr_omega [hsrc]))
    (g 16 (by decide) (by decide) _ _ (by addr_omega [hsb]) (by addr_omega [hsrc]))
  have v1 := moveHeld (e := s.getReg .x2 - 376) r1 hmf c₁.heap hn₂.ge hW
    (g 24 (by decide) (by decide) _ _ (by addr_omega [hsb]) (by addr_omega [hsrc]))
    (g 32 (by decide) (by decide) _ _ (by addr_omega [hsb]) (by addr_omega [hsrc]))
    (g 40 (by decide) (by decide) _ _ (by addr_omega [hsb]) (by addr_omega [hsrc]))
  have v2 := moveHeld (e := s.getReg .x2 - 352) r2 hmf c₁.heap hn₂.ge hW
    (g 48 (by decide) (by decide) _ _ (by addr_omega [hsb]) (by addr_omega [hsrc]))
    (g 56 (by decide) (by decide) _ _ (by addr_omega [hsb]) (by addr_omega [hsrc]))
    (g 64 (by decide) (by decide) _ _ (by addr_omega [hsb]) (by addr_omega [hsrc]))
  have f₂ := (A.fl.keep (DFrame.of_same hm₁ fun _ ↦ False) c.heap hn₁.ge (fun _ h ↦ h.elim)
    (fun _ _ h ↦ h) (by addr_omega [hsb])).keep hmf c₁.heap hn₂.ge
    (fun x h _ ↦ by
      simp only [memcpyStack] at h; rcases h with h | h <;> addr_omega [h, hsb, hab, hhu, hL, hn₁])
    (fun x hx h ↦ by
      simp only [memcpyStack] at h; rcases h with h | h <;> addr_omega [hx, h, hsb])
    (by addr_omega [hsb])
  -- `prod(sp' + 320, fp, o_c, 0)`
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80005bd8_spec
    (by rw [hpc₂, returnAddress_eq, b80005bc8_x1 h₁]; decide) trivial
  have k₃ := b80005bd8_keeps h₃
  have hm₃ := b80005bd8_mem_same h₃
  have c₃ := c₂.same hpre hm₃ fun r hr ↦ k₃ r (mem_of_mem hr _)
  have K₃ := sameKeeps hpre c₂ hm₃
  have hn₃ : heapNext t₃ = heapNext m := by simp only [heapNext, hm₃]
  obtain ⟨t₄, hr₄, ⟨hpc₄, hp₄, c₄, hn₄, b₄, K₄⟩ | hd⟩ := prodCall hP hpre c₃ (hr₂.trans hr₃)
    (b80005bd8_pc h₃) (o := s.getReg .x2 - 160) (by rw [b80005bd8_x10 h₃, c₂.x2]; rv_eval [])
    (Or.inl (by addr_omega [hsb])) (by addr_omega [hsb]) (Nat.le_refl _)
    (Or.inl (by addr_omega [hsb, hab]))
  swap
  · exact ⟨t₄, hr₄, Or.inr hd⟩
  rw [b80005bd8_x11 h₃, b80005bd8_x12 h₃, b80005bd8_x13 h₃] at b₄
  have kv (e : Word) (f : FormRust) (b : Held m e f L (heapNext m)) (he₁ : Loc s e)
      (he₂ : Apart e 24 (s.getReg .x2 - 160) 24) : Held t₄ e f L (heapNext t₄) :=
    heldMono (K₄.1 _ _ _ _ (K₃.1 _ _ _ _ b (by omega) (Or.inl he₁) (Or.inr (Or.inl rfl)))
      (by omega) (Or.inl he₁) he₂) (Nat.le_refl _) (by omega)
  have f₄ := (K₄.2 _ _ (K₃.2 _ _ f₂ (by omega)) (by omega))
  -- the arguments of `memory`
  obtain ⟨t₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b80005bf0_spec
    (by rw [hpc₄, returnAddress_eq, b80005bd8_x1 h₃]; decide) trivial
  have k₅ := b80005bf0_keeps h₅
  have hm₅ := b80005bf0_mem_same h₅
  have c₅ := c₄.same hpre hm₅ fun r hr ↦ k₅ r (mem_of_mem hr _)
  have K₅ := sameKeeps hpre c₄ hm₅
  have hn₅ : heapNext t₅ = heapNext t₄ := by simp only [heapNext, hm₅]
  have kw (e : Word) (f : FormRust) (l : Nat) (b : Held t₄ e f l (heapNext t₄)) (hl : L ≤ l)
      (he₁ : Loc s e) : Held t₅ e f L (heapNext t₅) :=
    heldMono (K₅.1 _ _ _ _ b (by omega) (Or.inl he₁) (Or.inr (Or.inl rfl))) hl (by omega)
  have kmv (e : Word) (f : FormRust) (b : Held m e f L (heapNext u)) (he₁ : Loc s e)
      (he₂ : Apart e 24 (s.getReg .x2 - 160) 24) : Held t₅ e f L (heapNext t₅) :=
    kw e f L (kv e f (heldMono b (Nat.le_refl _) (by omega)) he₁ he₂) (Nat.le_refl _) he₁
  refine ⟨t₅, hr₄.trans hr₅, Or.inl {
    toInv := c₅
    pc := b80005bf0_pc h₅
    x1 := b80005bf0_x1 h₅
    x10 := by rw [b80005bf0_x10 h₅, c₄.x2]; rv_eval []
    x11 := by rw [b80005bf0_x11 h₅, c₄.x2]; rv_eval []
    x12 := b80005bf0_x12 h₅
    x13 := by rw [b80005bf0_x13 h₅, c₄.x2]; rv_eval []
    fl := K₅.2 _ _ f₄ (by omega)
    hL := by omega
    addr := kw _ _ _ b₄ (by omega) (by addr_omega [hsb])
    v0 := kmv _ _ v0 (by addr_omega [hsb]) (by addr_omega [hsb])
    v1 := kmv _ _ v1 (by addr_omega [hsb]) (by addr_omega [hsb])
    v2 := kmv _ _ v2 (by addr_omega [hsb]) (by addr_omega [hsb]) }⟩

end Rv64Verifier.Layout.Arith
