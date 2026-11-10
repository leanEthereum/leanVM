import Rv64Verifier.Proofs.Layout.CloneLemmas
import Rv64Verifier.Blocks.F89

/-!
# `<[&[Form]; 3]>::concat`, at `0x80011cb0`

```rust
fn concat(slices: &[&[Form]; 3]) -> Vec<Form> {
    let mut result = Vec::with_capacity(slices.iter().map(|s| s.len()).sum());
    for s in slices { result.extend_from_slice(s) }
    result
}
```

compiled (`Blocks/F89.lean`): `0x80011cb0` makes an 80-byte frame (`sp'` = the entry's `sp - 80`),
saves `ra`, `s0`..`s4`, and calls `try_allocate_in(sp' + 8, l₀ + l₁ + l₂, 0, 8, 24)`; `0x80011d00`
traps on an error; `0x80011d08` makes the `Vec` at `sp' + 8` (the capacity, the buffer, length 0)
and calls `spec_extend` with the first slice, `0x80011d3c` and `0x80011d5c` with the others;
`0x80011d7c` copies the `Vec` to `a0`, restores and returns.
-/

namespace Rv64Verifier.Layout.Concat
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Blocks.F89
  Rv64Verifier.Model.LayoutMirror
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- The `Vec` at `sp - 72` holding `pre`; memory changed only on the stack, `NEXT` and what is
allocated, the saved registers kept. -/
structure VInv (s t₁ e : MachineState) (pre : List FormRust) : Prop where
  heap : HeapOk e
  mono : heapNext s ≤ heapNext e
  ok : FormVecOk e (s.getReg .x2 - 72)
  value : formVecOf e (s.getReg .x2 - 72) = pre
  fresh : ∀ x, formVecDeep e (s.getReg .x2 - 72) x → Fresh s e x
  saved : ∀ a : Word, (s.getReg .x2).toNat - 48 ≤ a.toNat → a.toNat + 8 ≤ (s.getReg .x2).toNat →
    e.getMem a = t₁.getMem a
  frame : DFrame s e fun x ↦ Within x (s.getReg .x2 - 352) 352 ∨ Within x nextAddr 8 ∨ Fresh s e x

theorem _root_.Rv64Verifier.Layout.ConcatPre.bounds {s : MachineState} (hpre : ConcatPre s) :
    0x78000000 + 352 ≤ (s.getReg .x2).toNat ∧ (s.getReg .x2).toNat ≤ 0xc0000008 ∧
      (s.getReg .x2).toNat % 16 = 0 ∧ (s.getReg .x10).toNat % 8 = 0 ∧
      (s.getReg .x10).toNat + 24 ≤ 0xc0000008 ∧ (s.getReg .x11).toNat % 8 = 0 ∧
      (s.getReg .x11).toNat + 48 ≤ 0xc0000008 := by
  have := hpre.stack.bounds (by decide) (by decide)
  have ha := hpre.stack.above
  have ho := ValidMemRange.bounds hpre.out (by decide)
  have hs := ValidMemRange.bounds hpre.slices (by decide)
  simp only [concatStack, specExtendStack, reserveStack, stackLo, heapEnd] at this ha
  rw [this.2.2.2] at ha
  omega

/-- What a frame of the stack, `NEXT` and the heap allocated since the entry misses: the slices
array and the slices' forms. -/
theorem untouched {s e : MachineState} (hpre : ConcatPre s) (he : heapNext e ≤ heapEnd) {x : Word}
    (hx : Within x (s.getReg .x11) 48 ∨ ∃ i < 3,
      Within x (slicePtr s (s.getReg .x11) i) (24 * sliceLen s (s.getReg .x11) i) ∨
      formsDeep s (slicePtr s (s.getReg .x11) i) (sliceLen s (s.getReg .x11) i) x) :
    ¬ (Within x (s.getReg .x2 - 352) 352 ∨ Within x nextAddr 8 ∨ Fresh s e x) := by
  have hb := hpre.bounds
  have hab := hpre.stack.above
  have hshi := hpre.heap.hi
  have hsf := hpre.slicesFree
  have hss := hpre.slicesStack
  simp only [concatStack, specExtendStack, reserveStack, stackLo, heapEnd] at hab hss
  simp only [Outside, heapNext, heapEnd] at hsf hshi he
  rcases hx with hx | ⟨i, hi, hx | hx⟩
  · intro h
    rcases h with h | h | h
    · addr_omega [hx, h, hss, hb]
    · addr_omega [hx, h, hsf.2]
    · simp only [Fresh, heapNext] at h; addr_omega [hx, h, hsf.1, he]
  · have hf := hpre.srcFree i hi
    have hst := hpre.srcStack i hi
    simp only [concatStack, specExtendStack, reserveStack, stackLo] at hst
    simp only [Outside, heapNext, heapEnd] at hf
    intro h
    rcases h with h | h | h
    · addr_omega [hx, h, hst, hb]
    · addr_omega [hx, h, hf.2]
    · simp only [Fresh, heapNext] at h; addr_omega [hx, h, hf.1, he]
  · obtain ⟨j, hj, hxj⟩ := hx
    have hbl := formBuf_below (hpre.srcOk i hi j hj) hxj
    simp only [heapNext, heapStart] at hbl
    intro h
    rcases h with h | h | h
    · addr_omega [hbl, h, hb, hab, hshi]
    · addr_omega [hbl, h, hshi]
    · simp only [Fresh, heapNext] at h; omega

/-- A slices-array word, unchanged. -/
theorem slice_word {s e : MachineState} {t₁ : MachineState} {pre : List FormRust}
    (hpre : ConcatPre s) (hv : VInv s t₁ e pre) {o : Nat} (ho' : o + 8 ≤ 48) :
    e.getMem (s.getReg .x11 + BitVec.ofNat 64 o) = s.getMem (s.getReg .x11 + BitVec.ofNat 64 o) := by
  have hb := hpre.bounds
  have hhi := hv.heap.hi
  exact hv.frame.getMem_of (fun x hx ↦ untouched hpre hhi (Or.inl (by addr_omega [hx, hb, ho'])))
    (by addr_omega [hb, ho'])

/-- One call to `spec_extend`, with slice `i`. -/
theorem extendStep (hS : SpecExtendSpec) {s t₁ e : MachineState} {pre : List FormRust} {i : Nat}
    (hpre : ConcatPre s) (hi : i < 3) (hv : VInv s t₁ e pre) (hpc : e.pc = 0x80011db8)
    (hsp : e.getReg .x2 = s.getReg .x2 - 80) (h10 : e.getReg .x10 = s.getReg .x2 - 72)
    (h11 : e.getReg .x11 = slicePtr s (s.getReg .x11) i)
    (h12 : e.getReg .x12 = slicePtr s (s.getReg .x11) i +
      BitVec.ofNat 64 (24 * sliceLen s (s.getReg .x11) i)) :
    ∃ e', Reaches Image.code e e' ∧ ((e'.pc = returnAddress e ∧ Preserves e e' ∧
      VInv s t₁ e' (pre ++ formsAt s (slicePtr s (s.getReg .x11) i) (sliceLen s (s.getReg .x11) i)))
      ∨ Dead Image.code e') := by
  have hb := hpre.bounds
  have hst := hpre.stack
  have hnx := hst.next
  have hab := hst.above
  simp only [concatStack, specExtendStack, reserveStack, stackLo, heapEnd, Nat.reduceAdd] at hnx hab
  have hhi := hv.heap.hi
  have hhi' := hhi
  simp only [heapNext, heapEnd] at hhi'
  obtain ⟨p, hp⟩ : ∃ p, p = slicePtr s (s.getReg .x11) i := ⟨_, rfl⟩
  obtain ⟨l, hl⟩ : ∃ l, l = sliceLen s (s.getReg .x11) i := ⟨_, rfl⟩
  rw [← hp] at h11 h12 ⊢
  rw [← hl] at h12 ⊢
  have hsrc := hpre.src i hi
  have hok := hpre.srcOk i hi
  have hsf := hpre.srcFree i hi
  have hss := hpre.srcStack i hi
  rw [← hp, ← hl] at hsrc hok hsf hss
  simp only [concatStack, specExtendStack, reserveStack, stackLo, Nat.reduceAdd] at hss
  have hpb : p.toNat + 24 * l ≤ 0xc0000008 ∨ l = 0 := by
    rcases Nat.eq_zero_or_pos l with h | h
    · exact Or.inr h
    · have := ValidMemRange.bounds hsrc (by omega); omega
  have hpl : p.toNat + 24 * l < 2 ^ 64 := by have := p.isLt; omega
  have hd : (e.getReg .x12).toNat - (e.getReg .x11).toNat = 24 * l := by
    rw [h11, h12]; addr_omega [hpl]
  have hcnt : ((e.getReg .x12).toNat - (e.getReg .x11).toNat) / 24 = l := by rw [hd]; omega
  -- the slice at `e`
  have hun : ∀ x, (Within x p (24 * l) ∨ formsDeep s p l x) →
      ¬ (Within x (s.getReg .x2 - 352) 352 ∨ Within x nextAddr 8 ∨ Fresh s e x) := fun x hx ↦
    untouched hpre hhi (Or.inr ⟨i, hi, by rw [← hp, ← hl]; exact hx⟩)
  have hfa := formsAt_frame hv.frame hok (fun x hx ↦ hun x (Or.inl hx)) (fun x hx ↦ hun x (Or.inr hx))
    (by omega) hpre.heap hv.mono
  have hfd := formsDeep_frame hv.frame (fun x hx ↦ hun x (Or.inl hx)) (by omega)
  have hxs : ∀ x, formVecDeep e (s.getReg .x2 - 72) x → x.toNat < heapNext e := fun x hx ↦
    (hv.fresh x hx).2
  have hse : SpecExtendPre e := {
    heap := hv.heap
    stack := hst.inner (k := 80) hsp (by decide) (by decide) (by decide) (by decide) (by decide)
    self := by rw [h10]; valid_sub hst.valid [hb]
    ok := by rw [h10]; exact hv.ok
    bounds := by rw [h11, h12]; addr_omega [hpl]
    whole := by rw [hd]; omega
    src := by rw [hd, h11, show 24 * l / 8 = 3 * l by omega]; exact hsrc
    srcOk := by rw [hcnt, h11]; exact hfa.2
    selfFree := by
      rw [h10]; simp only [Outside, heapEnd]
      exact ⟨Or.inr (by addr_omega [hb, hab]), by addr_omega [hb, hnx]⟩
    srcFree := by
      rw [hd, h11]; simp only [Outside] at hsf ⊢
      exact ⟨hsf.1.imp_left fun h ↦ Nat.le_trans h hv.mono, hsf.2⟩
    selfStack := by rw [h10]; addr_omega [hb, hsp]
    srcStack := by rw [hd, h11]; addr_omega [hss, hb, hsp]
    apart := by
      rw [hcnt, hd, h11, h10, hfd]
      intro x hx h
      refine hun x hx ?_
      rcases h with h | h
      · exact Or.inl (by addr_omega [h, hb])
      · exact Or.inr (Or.inr (hv.fresh x (Or.inl h)))
    header := by
      rw [h10]
      intro x hx hd'
      have := hxs x hd'
      simp only [heapNext] at this
      addr_omega [hx, this, hhi', hb, hab] }
  obtain ⟨e', hr, ⟨hpc', hpres, hpost⟩ | hdead⟩ := hS.call (Reaches.refl e) hpc hse
  swap
  · exact ⟨e', hr, Or.inr hdead⟩
  refine ⟨e', hr, Or.inl ⟨hpc', hpres, ?_⟩⟩
  have hval := hpost.value
  have hok' := hpost.ok
  have hdeep := hpost.deep
  have hfr := hpost.frame
  rw [h10] at hval hok' hdeep hfr
  rw [hcnt, h11, hfa.1, hv.value] at hval
  rw [show stackLo e specExtendStack = s.getReg .x2 - 352 by
    simp only [stackLo, hsp, specExtendStack, reserveStack]; rv_eval [Nat.reduceAdd]] at hfr
  have hm' := hpost.mono
  exact {
    heap := hpost.heap
    mono := hv.mono.trans hm'
    ok := hok'
    value := hval
    fresh := fun x hx ↦ by
      rcases hdeep x hx with h | h
      · have := hv.fresh x h; simp only [Fresh] at this ⊢; omega
      · simp only [Fresh] at h ⊢; have := hv.mono; omega
    saved := fun a h1 h2 ↦ by
      rw [hfr.getMem_of (a := a) (fun x hx h ↦ by
        rcases h with h | h | h | h | h
        · addr_omega [hx, h, h1, h2, hb]
        · have := hxs x (Or.inl h); simp only [heapNext] at this
          addr_omega [hx, this, hhi', h1, h2, hb]
        · addr_omega [hx, h, h1, h2, hb]
        · addr_omega [hx, h, h1, h2, hb, hnx]
        · simp only [Fresh, heapNext] at h
          have := hpost.heap.hi; simp only [heapNext, heapEnd] at this
          addr_omega [hx, h, h1, h2, hb, this]) (by addr_omega [h2, hb])]
      exact hv.saved a h1 h2
    frame := (hv.frame.union hfr).mono fun x h ↦ by
      rcases h with (h | h | h) | (h | h | h | h | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨h.1, Nat.lt_of_lt_of_le h.2 hm'⟩)
      · exact Or.inl (by addr_omega [h, hb])
      · exact Or.inr (Or.inr ⟨(hv.fresh x (Or.inl h)).1,
          Nat.lt_of_lt_of_le (hv.fresh x (Or.inl h)).2 hm'⟩)
      · exact Or.inl (by addr_omega [h, hb])
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨Nat.le_trans hv.mono h.1, h.2⟩) }

/-- A step that writes nothing keeps the invariant. -/
theorem VInv.same {s t₁ e e' : MachineState} {pre : List FormRust} (hv : VInv s t₁ e pre)
    (h : ∀ a, e'.getMem a = e.getMem a) : VInv s t₁ e' pre := by
  have hn : heapNext e' = heapNext e := by simp only [heapNext, h]
  have hf := formVecOf_move (DFrame.of_same h fun _ ↦ False) hv.ok (h _) (h _) (h _)
    (fun _ _ h ↦ h) hv.heap hn.ge
  exact {
    heap := ⟨hn ▸ hv.heap.lo, hn ▸ hv.heap.hi⟩
    mono := hn ▸ hv.mono
    ok := hf.2.1
    value := hf.1.trans hv.value
    fresh := fun x hx ↦ by rw [hf.2.2] at hx; simpa only [Fresh, hn] using hv.fresh x hx
    saved := fun a h1 h2 ↦ (h a).trans (hv.saved a h1 h2)
    frame := (hv.frame.union (DFrame.of_same h fun _ ↦ False)).mono fun x hx ↦ by
      rcases hx with (hx | hx | hx) | hx
      · exact Or.inl hx
      · exact Or.inr (Or.inl hx)
      · exact Or.inr (Or.inr (by simpa only [Fresh, hn] using hx))
      · exact hx.elim }

theorem trap : Image.code.fetch 0x80011db4 = none :=
  Option.isNone_iff_eq_none.mp (by decide +kernel)

theorem mul24 (x : Word) : x * 16 + x * 8 = BitVec.ofNat 64 (24 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  simp only [show (16 : Word).toNat = 16 from rfl, show (8 : Word).toNat = 8 from rfl]
  omega

/-- **`<[&[Form]; 3]>::concat` meets its contract**, given `try_allocate_in`'s and
`spec_extend`'s. -/
theorem concat_spec (hT : TryAllocZeroedSpec) (hS : SpecExtendSpec) : ConcatSpec := by
  intro s hpc hpre
  have hb := hpre.bounds
  have hst := hpre.stack
  have hnx := hst.next
  have hab := hst.above
  have hss := hpre.slicesStack
  have hos := hpre.outStack
  have hof := hpre.outFree
  simp only [concatStack, specExtendStack, reserveStack, stackLo, heapEnd,
    Nat.reduceAdd] at hnx hab hss hos
  simp only [Outside, heapNext, heapEnd] at hof
  -- the prologue and `try_allocate_in`
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80011cb0_spec hpc (by
    rv_eval []
    and_intros <;> first
      | valid_access hst.valid [hb]
      | valid_access hpre.slices [hb]
      | addr_omega [hb, hss])
  have k₁ := b80011cb0_keeps h₁
  have hm₁ := b80011cb0_frame h₁ (by addr_omega [hb])
  have x2₁ := b80011cb0_x2 h₁
  have x10₁ := b80011cb0_x10 h₁
  have hn₁ : t₁.getMem nextAddr = s.getMem nextAddr := hm₁ _ (by addr_omega [hnx, hb])
  have hnext₁ : heapNext t₁ = heapNext s := by simp only [heapNext, hn₁]
  have hta : TryAllocPre .x13 .x14 t₁ := {
    heap := ⟨hnext₁ ▸ hpre.heap.lo, hnext₁ ▸ hpre.heap.hi⟩
    out := by rw [x10₁]; valid_sub hst.valid [hb]
    align := by rw [b80011cb0_x13 h₁]; decide
    size := by rw [b80011cb0_x14 h₁]; decide
    stack := hst.inner (k := 80) x2₁ (by decide) (by decide) (by decide) (by decide) (by decide)
    outFree := by
      rw [x10₁]; simp only [Outside, heapEnd]
      exact ⟨Or.inr (by addr_omega [hb, hab]), by addr_omega [hb, hnx]⟩
    outStack := by rw [x10₁]; addr_omega [hb, x2₁] }
  obtain ⟨w, hr₂, ⟨hpc₂, hpres₂, hpost, -⟩ | hdead⟩ := hT.call hr₁ (b80011cb0_pc h₁) hta
  swap
  · exact ⟨w, hr₂, Or.inr hdead⟩
  have hwf := hpost.frame.dframe
  rw [x10₁, show stackLo t₁ tryAllocStack = s.getReg .x2 - 128 by
    simp only [stackLo, x2₁, tryAllocStack]; rv_eval []] at hwf
  have x2₂ : w.getReg .x2 = s.getReg .x2 - 80 := (hpres₂.reg .x2).trans x2₁
  obtain ⟨w₂, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80011d00_spec
    (by rw [hpc₂, returnAddress_eq, b80011cb0_x1 h₁]; decide) (by
      rv_eval [x2₂]
      valid_access hst.valid [hb])
  by_cases htag : w.getMem (s.getReg .x2 - 72) = 0
  swap
  · exact ⟨w₂, hr₂.trans hr₃, Or.inr (dead_of_fetch (by
      rw [b80011d00_pc_taken h₃ (by rw [x2₂]; rv_eval []; exact htag)]; exact trap))⟩
  have hok₂ := hpost.ok
  rw [x10₁] at hok₂
  obtain ⟨hcap₂, hnew₂⟩ := hok₂ htag
  rw [b80011cb0_x14 h₁, b80011cb0_x13 h₁] at hnew₂
  have k₃ := b80011d00_keeps h₃
  have hm₃ := b80011d00_mem_same h₃
  have x2w₂ : w₂.getReg .x2 = s.getReg .x2 - 80 := (k₃ .x2 (by decide)).trans x2₂
  have hreg (q : Reg) (hq : q ∈ [Reg.x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26,
      .x27]) : w₂.getReg q = t₁.getReg q := by
    rw [k₃ q (mem_of_mem hq _), hpres₂ q (mem_of_mem hq _)]
  have x9w₂ : w₂.getReg .x9 = s.getReg .x11 := by rw [hreg .x9 (by decide), b80011cb0_x9 h₁]
  obtain ⟨e₀, hr₄, h₄⟩ := Sym.BlockSpec.reaches b80011d08_spec
    (b80011d00_pc_not_taken h₃ (by rw [x2₂]; rv_eval []; exact htag)) (by
      rv_eval [x2w₂, x9w₂]
      and_intros <;> first
        | valid_access hst.valid [hb]
        | valid_access hpre.slices [hb])
  have k₄ := b80011d08_keeps h₄
  have hm₄ := b80011d08_frame h₄ (by rw [x2w₂]; addr_omega [hb])
  rw [x2w₂, show s.getReg .x2 - 80 + 8 = s.getReg .x2 - 72 by rv_eval []] at hm₄
  have c₀ := b80011d08_m_x2_8 h₄
  have p₀ := b80011d08_m_x2_16 h₄
  have l₀ := b80011d08_m_x2_24 h₄
  rw [x2w₂] at c₀ p₀ l₀
  rv_eval [] at c₀ p₀ l₀
  rw [hm₃] at c₀ p₀
  rw [show s.getReg .x2 - 72 + 8 = s.getReg .x2 - 64 by rv_eval []] at hcap₂
  rw [show s.getReg .x2 - 72 + 16 = s.getReg .x2 - 56 by rv_eval []] at hnew₂
  rw [hcap₂, b80011cb0_x11 h₁] at c₀
  obtain ⟨ptr, hptr⟩ : ∃ p, p = w.getMem (s.getReg .x2 - 56) := ⟨_, rfl⟩
  rw [← hptr] at p₀ hnew₂
  have hcap0 : vecCap e₀ (s.getReg .x2 - 72) =
      s.getMem (s.getReg .x11 + 40) + (s.getMem (s.getReg .x11 + 24) + s.getMem (s.getReg .x11 + 8)) :=
    c₀
  have hptr0 : vecPtr e₀ (s.getReg .x2 - 72) = ptr := by
    simp only [vecPtr]; rw [show s.getReg .x2 - 72 + 8 = s.getReg .x2 - 64 by rv_eval []]; exact p₀
  have hlen0 : vecLen e₀ (s.getReg .x2 - 72) = 0 := by
    simp only [vecLen]; rw [show s.getReg .x2 - 72 + 16 = s.getReg .x2 - 56 by rv_eval []]; exact l₀
  have hn₄ : heapNext e₀ = heapNext w := by
    simp only [heapNext]; rw [hm₄ _ (by addr_omega [hb, hnx]), hm₃]
  have hnb := hnew₂
  simp only [NewBuf] at hnb
  rw [b80011cb0_x11 h₁, show (24 : Word).toNat = 24 from rfl] at hnb
  have hwhi := hpost.heap.hi
  have hfr₀ : DFrame s e₀ fun x ↦ Within x (s.getReg .x2 - 352) 352 ∨ Within x nextAddr 8 ∨
      Fresh s e₀ x :=
    (((hm₁.dframe.union hwf).union (DFrame.of_same hm₃ fun _ ↦ False)).union hm₄.dframe).mono
      fun x h ↦ by
        rcases h with (((h | h | h | h | h) | h) | h)
        · exact Or.inl (by addr_omega [h, hb])
        · exact Or.inl (by addr_omega [h, hb])
        · exact Or.inl (by addr_omega [h, hb])
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (by simpa only [Fresh, hnext₁, hn₄] using h))
        · exact h.elim
        · exact Or.inl (by addr_omega [h, hb])
  have inv₀ : VInv s t₁ e₀ [] := {
    heap := ⟨hn₄ ▸ hpost.heap.lo, hn₄ ▸ hpost.heap.hi⟩
    mono := by rw [hn₄, ← hnext₁]; exact hpost.mono
    ok := ⟨⟨by
        simp only [RawVecOk, Buf, hptr0, hcap0, hn₄]
        refine ⟨hnb.1, hnb.2.imp id fun h' ↦ ⟨?_, h'.2⟩⟩
        have := hpre.heap.lo; rw [← hnext₁] at this; omega,
      by rw [hlen0]; simp⟩, fun i hi ↦ by rw [hlen0] at hi; simp at hi,
      fun x ⟨i, hi, _⟩ ↦ by rw [hlen0] at hi; simp at hi⟩
    value := by simp only [formVecOf, formsAt, hlen0]; rfl
    fresh := fun x hx ↦ by
      rcases hx with hx | ⟨i, hi, _⟩
      · simp only [formVecBuf, hptr0, hcap0, Within] at hx
        simp only [Fresh, ← hnext₁, hn₄]
        rcases hnb.2 with h0 | h0
        · rw [Nat.mul_eq_zero] at h0; omega
        · omega
      · rw [hlen0] at hi; simp at hi
    saved := fun a h1 h2 ↦ by
      rw [hm₄ a (by addr_omega [h1, h2, hb]), hm₃]
      refine hwf.getMem_of (fun x hx h ↦ ?_) (by addr_omega [h2, hb])
      simp only [heapNext, heapEnd] at hwhi
      rcases h with h | h | h | h
      · addr_omega [hx, h, h1, h2, hb]
      · addr_omega [hx, h, h1, h2, hb]
      · addr_omega [hx, h, h1, h2, hb, hnx]
      · simp only [Fresh, heapNext] at h; addr_omega [hx, h, h1, h2, hb, hwhi, hab]
    frame := hfr₀ }
  -- the slices' words, read at any later state
  have hsw {e : MachineState} {pre : List FormRust} (hv : VInv s t₁ e pre) (o : Nat) (ho : o + 8 ≤ 48) :
      e.getMem (s.getReg .x11 + BitVec.ofNat 64 o) = s.getMem (s.getReg .x11 + BitVec.ofNat 64 o) :=
    slice_word hpre hv ho
  have hw₂a : w₂.getMem (s.getReg .x11) = s.getMem (s.getReg .x11) := by
    rw [← hm₄ _ (by addr_omega [hb, hss])]
    simpa using hsw inv₀ 0 (by decide)
  have x20w₂ : w₂.getReg .x20 = s.getMem (s.getReg .x11 + 8) := by
    rw [hreg .x20 (by decide), b80011cb0_x20 h₁]
  -- the first slice
  obtain ⟨e₀', hr₅, ⟨hpc₅, hpres₅, inv₀'⟩ | hdead⟩ := extendStep hS hpre (i := 0) (by decide) inv₀
    (b80011d08_pc h₄) ((k₄ .x2 (by decide)).trans x2w₂)
    (by rw [b80011d08_x10 h₄, x2w₂]; rv_eval [])
    (by rw [b80011d08_x11 h₄, x9w₂, hw₂a]; simp [slicePtr])
    (by
      rw [b80011d08_x12 h₄, x9w₂, hw₂a, x20w₂, mul24]
      simp only [slicePtr, sliceLen, Nat.mul_zero, Nat.zero_add, BitVec.add_zero]
      rfl)
  swap
  · exact ⟨e₀', hr₂.trans (hr₃.trans (hr₄.trans hr₅)), Or.inr hdead⟩
  have hreg₀ (q : Reg) (hq : q ∈ [Reg.x8, .x9, .x18, .x19, .x21, .x22, .x23, .x24, .x25, .x26,
      .x27]) : e₀'.getReg q = t₁.getReg q := by
    rw [hpres₅ q (mem_of_mem hq _), k₄ q (mem_of_mem hq _), hreg q (mem_of_mem hq _)]
  have x2₅ : e₀'.getReg .x2 = s.getReg .x2 - 80 := by
    rw [hpres₅.reg .x2, k₄ .x2 (by decide), x2w₂]
  have x9₅ : e₀'.getReg .x9 = s.getReg .x11 := by rw [hreg₀ .x9 (by decide), b80011cb0_x9 h₁]
  -- the second slice
  obtain ⟨e₁, hr₆, h₆⟩ := Sym.BlockSpec.reaches b80011d3c_spec
    (by rw [hpc₅, returnAddress_eq, b80011d08_x1 h₄]; decide) (by
      rv_eval [x9₅]
      valid_access hpre.slices [hb])
  have k₆ := b80011d3c_keeps h₆
  have inv₁ := inv₀'.same (b80011d3c_mem_same h₆)
  have hs16 : e₀'.getMem (s.getReg .x11 + 16) = s.getMem (s.getReg .x11 + 16) := by
    simpa using hsw inv₀' 16 (by decide)
  obtain ⟨e₁', hr₇, ⟨hpc₇, hpres₇, inv₁'⟩ | hdead⟩ := extendStep hS hpre (i := 1) (by decide) inv₁
    (b80011d3c_pc h₆) ((k₆ .x2 (by decide)).trans x2₅)
    (by rw [b80011d3c_x10 h₆, x2₅]; rv_eval [])
    (by rw [b80011d3c_x11 h₆, x9₅, hs16]; rfl)
    (by
      rw [b80011d3c_x12 h₆, x9₅, hs16, hreg₀ .x19 (by decide), b80011cb0_x19 h₁, mul24]
      rfl)
  swap
  · exact ⟨e₁', hr₂.trans (hr₃.trans (hr₄.trans (hr₅.trans (hr₆.trans hr₇)))), Or.inr hdead⟩
  have hreg₁ (q : Reg) (hq : q ∈ [Reg.x8, .x9, .x18, .x20, .x21, .x22, .x23, .x24, .x25, .x26,
      .x27]) : e₁'.getReg q = e₀'.getReg q := by
    rw [hpres₇ q (mem_of_mem hq _), k₆ q (mem_of_mem hq _)]
  have x2₇ : e₁'.getReg .x2 = s.getReg .x2 - 80 := by
    rw [hpres₇.reg .x2, k₆ .x2 (by decide), x2₅]
  have x9₇ : e₁'.getReg .x9 = s.getReg .x11 := by rw [hreg₁ .x9 (by decide), x9₅]
  -- the third slice
  obtain ⟨e₂, hr₈, h₈⟩ := Sym.BlockSpec.reaches b80011d5c_spec
    (by rw [hpc₇, returnAddress_eq, b80011d3c_x1 h₆]; decide) (by
      rv_eval [x9₇]
      valid_access hpre.slices [hb])
  have k₈ := b80011d5c_keeps h₈
  have inv₂ := inv₁'.same (b80011d5c_mem_same h₈)
  have hs32 : e₁'.getMem (s.getReg .x11 + 32) = s.getMem (s.getReg .x11 + 32) := by
    simpa using hsw inv₁' 32 (by decide)
  obtain ⟨e₂', hr₉, ⟨hpc₉, hpres₉, inv₂'⟩ | hdead⟩ := extendStep hS hpre (i := 2) (by decide) inv₂
    (b80011d5c_pc h₈) ((k₈ .x2 (by decide)).trans x2₇)
    (by rw [b80011d5c_x10 h₈, x2₇]; rv_eval [])
    (by rw [b80011d5c_x11 h₈, x9₇, hs32]; rfl)
    (by
      rw [b80011d5c_x12 h₈, x9₇, hs32, hreg₁ .x18 (by decide), hreg₀ .x18 (by decide),
        b80011cb0_x18 h₁, mul24]
      rfl)
  swap
  · exact ⟨e₂', hr₂.trans (hr₃.trans (hr₄.trans (hr₅.trans (hr₆.trans (hr₇.trans (hr₈.trans
      hr₉)))))), Or.inr hdead⟩
  -- the epilogue
  have hreg₉ (q : Reg) (hq : q ∈ [Reg.x8, .x9, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26,
      .x27]) : e₂'.getReg q = e₁'.getReg q := by
    rw [hpres₉ q (mem_of_mem hq _), k₈ q (mem_of_mem hq _)]
  have x2₉ : e₂'.getReg .x2 = s.getReg .x2 - 80 := by
    rw [hpres₉.reg .x2, k₈ .x2 (by decide), x2₇]
  have x8₉ : e₂'.getReg .x8 = s.getReg .x10 := by
    rw [hreg₉ .x8 (by decide), hreg₁ .x8 (by decide), hreg₀ .x8 (by decide), b80011cb0_x8 h₁]
  have hob := ValidMemRange.bounds hpre.out (by decide)
  obtain ⟨t, hr₁₀, h₁₀⟩ := Sym.BlockSpec.reaches b80011d7c_spec
    (by rw [hpc₉, returnAddress_eq, b80011d5c_x1 h₈]; decide) (by
      rv_eval [x2₉, x8₉]
      and_intros <;> first
        | valid_access hst.valid [hb]
        | valid_access hpre.out [hb]
        | addr_omega [hb, hos])
  have k₁₀ := b80011d7c_keeps h₁₀
  have hmf := b80011d7c_frame h₁₀ (by rw [x8₉]; addr_omega [hb])
  rw [x8₉] at hmf
  have o0 := b80011d7c_m_x8_0 h₁₀
  have o8 := b80011d7c_m_x8_8 h₁₀
  have o16 := b80011d7c_m_x8_16 h₁₀
  rw [x8₉, x2₉] at o0 o8 o16
  rv_eval [] at o0 o8 o16
  have hsv (a : Word) (h1 : (s.getReg .x2).toNat - 48 ≤ a.toNat)
      (h2 : a.toNat + 8 ≤ (s.getReg .x2).toNat) : e₂'.getMem a = t₁.getMem a := inv₂'.saved a h1 h2
  have pc := b80011d7c_pc h₁₀
  have r₁ := b80011d7c_x1 h₁₀
  have r₂ := b80011d7c_x2 h₁₀
  have r₈ := b80011d7c_x8 h₁₀
  have r₉ := b80011d7c_x9 h₁₀
  have r₁₈ := b80011d7c_x18 h₁₀
  have r₁₉ := b80011d7c_x19 h₁₀
  have r₂₀ := b80011d7c_x20 h₁₀
  rw [x2₉] at pc r₁ r₂ r₈ r₉ r₁₈ r₁₉ r₂₀
  rv_eval [] at pc r₁ r₂ r₈ r₉ r₁₈ r₁₉ r₂₀
  rw [hsv _ (by addr_omega [hb]) (by addr_omega [hb]), b80011cb0_m_x2_n8 h₁] at pc r₁
  rw [hsv _ (by addr_omega [hb]) (by addr_omega [hb]), b80011cb0_m_x2_n16 h₁] at r₈
  rw [hsv _ (by addr_omega [hb]) (by addr_omega [hb]), b80011cb0_m_x2_n24 h₁] at r₉
  rw [hsv _ (by addr_omega [hb]) (by addr_omega [hb]), b80011cb0_m_x2_n32 h₁] at r₁₈
  rw [hsv _ (by addr_omega [hb]) (by addr_omega [hb]), b80011cb0_m_x2_n40 h₁] at r₁₉
  rw [hsv _ (by addr_omega [hb]) (by addr_omega [hb]), b80011cb0_m_x2_n48 h₁] at r₂₀
  have hdo : ∀ x, formVecDeep e₂' (s.getReg .x2 - 72) x → ¬ Within x (s.getReg .x10) 24 := by
    intro x hx h
    have := inv₂'.fresh x hx
    have hhi := inv₂'.heap.hi
    simp only [Fresh, heapNext, heapEnd] at this hhi
    addr_omega [this, h, hof, hhi]
  have hnt : heapNext t = heapNext e₂' := by
    simp only [heapNext]; rw [hmf _ (by addr_omega [hof.2, hob])]
  have hf := formVecOf_move hmf.dframe inv₂'.ok o0
    (by rw [show s.getReg .x2 - 72 + 8 = s.getReg .x2 - 64 by rv_eval []]; exact o8)
    (by rw [show s.getReg .x2 - 72 + 16 = s.getReg .x2 - 56 by rv_eval []]; exact o16)
    hdo inv₂'.heap hnt.ge
  refine ⟨t, hr₂.trans (hr₃.trans (hr₄.trans (hr₅.trans (hr₆.trans (hr₇.trans (hr₈.trans
    (hr₉.trans hr₁₀))))))), Or.inl ⟨pc.trans (returnAddress_eq s).symm,
    preserves_of r₂ r₈ r₉ r₁₈ r₁₉ fun q hq ↦ ?_, ⟨⟨hnt ▸ inv₂'.heap.lo, hnt ▸ inv₂'.heap.hi⟩,
      hnt ▸ inv₂'.mono, hf.2.1, fun x hx ↦ ?_, ?_⟩, ?_⟩⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact r₂₀
    all_goals
      rw [k₁₀ _ (by decide), hreg₉ _ (by decide), hreg₁ _ (by decide), hreg₀ _ (by decide),
        k₁ _ (by decide)]
  · rw [hf.2.2] at hx
    simpa only [Fresh, hnt] using inv₂'.fresh x hx
  · refine (inv₂'.frame.union hmf.dframe).mono fun x h ↦ ?_
    rcases h with (h | h | h) | h
    · exact Or.inr (Or.inl (by addr_omega [h, hb]))
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (by simpa only [Fresh, hnt] using h)))
    · exact Or.inl h
  · rw [hf.1, inv₂'.value, List.nil_append]

end Rv64Verifier.Layout.Concat
