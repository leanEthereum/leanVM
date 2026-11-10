import Rv64Verifier.Proofs.Multilinear.Contracts
import Rv64Verifier.Proofs.Multilinear.ScalerFill
import Rv64Verifier.Proofs.Runtime.Inv

/-!
# `Scaler::new`

```rust
fn new(r: E, uses: usize) -> Self {
    if uses >= 256 { Self::Table(Scaled::new(r)) } else { Self::Plain(r) }
}
```

compiled at `0x80008a58` (`Blocks/F33.lean`), `Scaled::new` inlined, with `S` the entry's `sp`:
`0x80008a58` saves `ra`, `s0`..`s9` in a 112-byte frame (`s0` = the result, `s1` = `r`) and
branches on `uses`; `0x80008bf4` writes `Plain(r)`; otherwise `0x80008a98` calls
`from_elem(S - 112, &ZERO, 2112)` (`ZERO` in `.rodata` at `0xa0000068`), `0x80008ab4` checks the
length, `0x80008ac0` loads `r` and the loop bounds (the end through a division by 704, its
reciprocal in `.rodata`), the fill runs (`ScalerFill.lean`), `0x80008bd4` writes `Table(vec)`;
`0x80008c10` writes the tag, restores and returns.
-/

namespace Rv64Verifier.Proofs.Multilinear.ScalerNew
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.MultilinearContracts
  Rv64Verifier.MultilinearWords Rv64Verifier.Model Rv64Verifier.Blocks.F33
  Rv64Verifier.Proofs.Multilinear.ScalerFill
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

def slots : List (Nat × Reg) := [(8, .x1), (16, .x8), (24, .x9), (32, .x18), (40, .x19),
  (48, .x20), (56, .x21), (64, .x22), (72, .x23), (80, .x24), (88, .x25)]

def kept : List Reg := [.x26, .x27]

/-- What the function writes besides its saved registers: the result, and the stack below
them. -/
@[rv_addr] def W (s : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x10) 32 ∨ Within a (stackLo s scalerStack) 136

abbrev Inv (s u : MachineState) (nx : Word) : Prop := FnInv s u 112 slots kept (W s) nx

theorem bounds {s : MachineState} (h : ScalerPre s) :
    0x780000e0 ≤ (s.getReg .x2).toNat ∧ (s.getReg .x2).toNat ≤ 0xc0000008 ∧
      (s.getReg .x2).toNat % 16 = 0 ∧ (s.getReg .x10).toNat % 8 = 0 ∧
      (s.getReg .x10).toNat + 32 ≤ 0xc0000008 := by
  have := h.stack.bounds (by decide) (by decide)
  have ha := h.stack.above
  have ho := ValidMemRange.bounds h.out (by decide)
  simp only [scalerStack, fromElemStack, tryAllocStack, stackLo, heapEnd] at this ha
  rw [this.2.2.2] at ha
  omega

theorem stack112 {s : MachineState} (h : ScalerPre s) : RtStack s 112 := by
  have hb := bounds h
  have hst := h.stack
  have hn := hst.next
  have hro := hst.rodata
  refine ⟨⟨?_, hst.aligned⟩, by addr_omega [hb], by addr_omega [hb, hn], by addr_omega [hb, hro]⟩
  exact ValidMemRange.sub hst.valid (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb])

theorem Inv.step {s u v : MachineState} {nx nx' : Word} {X : Word → Prop}
    (hpre : ScalerPre s) (h : Inv s u nx) (hX : ByteFrame u v X)
    (hXsub : ∀ a, X a → W s a ∨ Within a nextAddr 8 ∨ (heapNext s ≤ a.toNat ∧ a.toNat < nx'.toNat))
    (hnx : v.getMem nextAddr = nx') (hle : nx.toNat ≤ nx'.toNat) (hend : nx'.toNat ≤ heapEnd)
    (hr : ∀ r ∈ Reg.x2 :: kept, v.getReg r = u.getReg r) : Inv s v nx' := by
  have hb := bounds hpre
  have hs := hpre.outStack
  exact FnInv.step (m := 88) h (stack112 hpre) (by decide) (by decide) (by decide)
    (fun a ha ha' ↦ by simp only [W] at ha; addr_omega [ha, ha', hs, hb]) hX hXsub hnx hle hend
    (hr _ (by decide)) fun r hr' ↦ hr r (List.mem_cons_of_mem _ hr')

theorem Inv.same {s u v : MachineState} {nx : Word} (hpre : ScalerPre s) (h : Inv s u nx)
    (hm : ∀ a, v.getMem a = u.getMem a) {l : List Reg} (hk : ∀ r ∈ l, v.getReg r = u.getReg r)
    (hl : ∀ r ∈ Reg.x2 :: kept, r ∈ l := by decide) : Inv s v nx :=
  h.step hpre (ByteFrame.of_same hm fun _ ↦ False) (fun _ h ↦ h.elim) ((hm _).trans h.next)
    (Nat.le_refl _) h.fits fun r hr ↦ hk r (hl r hr)

/-- The tag to the result, the registers restored, return; then the contract's heap and frame. -/
theorem exit {s u : MachineState} {nx : Word} (hpre : ScalerPre s) (hpc : u.pc = 0x80008c10)
    (h : Inv s u nx) (hout : u.getReg .x8 = s.getReg .x10) :
    ∃ t, Reaches Image.code u t ∧ t.pc = returnAddress s ∧ Preserves s t ∧
      t.getMem (s.getReg .x10) = u.getReg .x10 ∧ MemFrame u t (s.getReg .x10) 8 ∧
      HeapOk t ∧ heapNext s ≤ heapNext t ∧ heapNext t = nx.toNat ∧
      ByteFrame s t (fun a ↦ Within a (s.getReg .x10) 32 ∨
        Within a (stackLo s scalerStack) scalerStack ∨ Within a nextAddr 8 ∨ Fresh s t a) := by
  have hb := bounds hpre
  have hs := hpre.outStack
  have hof := hpre.outFree
  simp only [Outside] at hof
  have hsp := h.sp
  have sl := h.slots
  simp only [slots, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
    and_true] at sl
  rv_eval [] at hsp sl
  obtain ⟨sl1, sl2, sl3, sl4, sl5, sl6, sl7, sl8, sl9, sl10, sl11⟩ := sl
  obtain ⟨t, hr, ht⟩ := Sym.BlockSpec.reaches b80008c10_spec hpc (by
    rv_eval [hsp, hout]
    and_intros <;> first
      | addr_omega [hb, hs]
      | valid_access hpre.stack.valid [hb]
      | valid_access hpre.out [hb])
  have k := b80008c10_keeps ht
  have hm := b80008c10_frame ht (by rw [hout]; addr_omega [hb])
  rw [hout] at hm
  have pc := b80008c10_pc ht
  have x2 := b80008c10_x2 ht
  have x8 := b80008c10_x8 ht
  have x9 := b80008c10_x9 ht
  have x18 := b80008c10_x18 ht
  have x19 := b80008c10_x19 ht
  have x20 := b80008c10_x20 ht
  have x21 := b80008c10_x21 ht
  have x22 := b80008c10_x22 ht
  have x23 := b80008c10_x23 ht
  have x24 := b80008c10_x24 ht
  have x25 := b80008c10_x25 ht
  have m := b80008c10_m_x8_0 ht
  rv_eval [hsp, sl1, sl2, sl3, sl4, sl5, sl6, sl7, sl8, sl9, sl10, sl11, hout]
    at pc x2 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 m
  have hu := ht.unaligned (by rv_eval [hout]; addr_omega [hb])
  have bf := ByteFrame.of_memFrame hm (by addr_omega [hb]) (by decide) hu
  have hnt : t.getMem nextAddr = nx := (hm _ (by addr_omega [hof.2, hb])).trans h.next
  have hn : heapNext t = nx.toNat := by simp only [heapNext, hnt]
  have hfr := h.frame bf (fun a ha ↦ Or.inl (by addr_omega [ha, hb])) hnt
  have hlo := hpre.heap.lo
  refine ⟨t, hr, pc.trans (returnAddress_eq s).symm,
    preserves_of x2 x8 x9 x18 x19 fun r hr' ↦ ?_, m, hm,
    ⟨by have := h.mono; omega, by have := h.fits; omega⟩, by have := h.mono; omega, hn,
    hfr.mono fun a ha ↦ ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact x20
    · exact x21
    · exact x22
    · exact x23
    · exact x24
    · exact x25
    all_goals exact (k _ (by decide)).trans (h.kept _ (by decide))
  · rcases ha with ha | ha | ha | ha
    · rcases ha with ha | ha
      · exact Or.inl ha
      · exact Or.inr (Or.inl (by addr_omega [ha, hb]))
    · exact Or.inr (Or.inl (by addr_omega [ha, hb]))
    · exact Or.inr (Or.inr (Or.inl ha))
    · exact Or.inr (Or.inr (Or.inr ha))

theorem zero_valid : ValidMemRange (0xa0000068 : Word) 3 := by
  intro i hi
  interval_cases i <;> decide

theorem end_eq (P : Word) : P + (rv64_mulhu 2112 (0x2e8ba2e8ba2e8ba3 : Word) >>> 7 * 16384 +
    rv64_mulhu 2112 (0x2e8ba2e8ba2e8ba3 : Word) >>> 7 * 512) = P + BitVec.ofNat 64 tabBytes := by
  congr 1

theorem tab_eq_map (u : MachineState) (P : Word) :
    tab u P = (eListAt u P 2112).map limbs := by
  simp only [tab, eListAt, List.map_map]
  rfl

/-- After the prologue. -/
structure Pro (s t₁ : MachineState) : Prop where
  inv : Inv s t₁ (s.getMem nextAddr)
  x8 : t₁.getReg .x8 = s.getReg .x10
  x9 : t₁.getReg .x9 = s.getReg .x11
  x12 : t₁.getReg .x12 = s.getReg .x12
  sp : t₁.getReg .x2 = s.getReg .x2 - 112
  mem : MemFrame s t₁ (s.getReg .x2 - 88) 88
  small : (s.getReg .x12).toNat < 256 → t₁.pc = 0x80008bf4
  big : ¬ (s.getReg .x12).toNat < 256 → t₁.pc = 0x80008a98

theorem prologue {s : MachineState} (hpc : s.pc = 0x80008a58) (hpre : ScalerPre s) :
    ∃ t₁, Reaches Image.code s t₁ ∧ Pro s t₁ := by
  have hb := bounds hpre
  have hst := hpre.stack
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80008a58_spec hpc (by
    rv_eval []
    and_intros <;> valid_access hst.valid [hb])
  have k₁ := b80008a58_keeps h₁
  have hm₁ := b80008a58_frame h₁ (by addr_omega [hb])
  exact ⟨t₁, hr₁, {
    inv := FnInv.init hpre.heap (stack112 hpre)
      (by rw [b80008a58_x2 h₁]; rfl)
      (by
        simp only [slots, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
          and_true]
        rv_eval []
        exact ⟨b80008a58_m_x2_n8 h₁, b80008a58_m_x2_n16 h₁, b80008a58_m_x2_n24 h₁,
          b80008a58_m_x2_n32 h₁, b80008a58_m_x2_n40 h₁, b80008a58_m_x2_n48 h₁,
          b80008a58_m_x2_n56 h₁, b80008a58_m_x2_n64 h₁, b80008a58_m_x2_n72 h₁,
          b80008a58_m_x2_n80 h₁, b80008a58_m_x2_n88 h₁⟩)
      (fun r hr ↦ k₁ r (mem_of_mem hr _))
      (hm₁.mono fun a ha ↦ by addr_omega [ha, hb])
      (h₁.unaligned (by rv_eval []; and_intros <;> addr_omega [hb])) (by decide)
    x8 := b80008a58_x8 h₁
    x9 := b80008a58_x9 h₁
    x12 := k₁ .x12 (by decide)
    sp := b80008a58_x2 h₁
    mem := hm₁
    small := fun h ↦ b80008a58_pc_taken h₁ (by show _ ≤ 255; omega)
    big := fun h ↦ b80008a58_pc_not_taken h₁ (by show 255 < _; omega) }⟩

/-- `r` is never written. -/
theorem r_keep {s u : MachineState} {nx : Word} (hpre : ScalerPre s) (h : Inv s u nx) (c : Nat)
    (hc : c = 0 ∨ c = 8 ∨ c = 16) :
    u.getMem (s.getReg .x11 + BitVec.ofNat 64 c) = s.getMem (s.getReg .x11 + BitVec.ofNat 64 c) := by
  have hb := bounds hpre
  have hR := ValidMemRange.bounds hpre.r (by decide)
  have hrf := hpre.rFree
  simp only [Outside] at hrf
  have hrs := hpre.rStack
  have hro' := hpre.rOut
  have hfit := h.fits
  refine h.mem.getMem fun i hi hw ↦ ?_
  rcases hw with (hw | hw) | hw | hw | hw
  · addr_omega [hw, hi, hc, hR, hro']
  · addr_omega [hw, hi, hc, hR, hrs, hb]
  · addr_omega [hw, hi, hc, hR, hrs, hb]
  · addr_omega [hw, hi, hc, hR, hrf.2]
  · addr_omega [hw, hi, hc, hR, hrf.1, hfit]

theorem r_eAt {s u : MachineState} {nx : Word} (hpre : ScalerPre s) (h : Inv s u nx) :
    u.getMem (s.getReg .x11) = s.getMem (s.getReg .x11) ∧
      u.getMem (s.getReg .x11 + 8) = s.getMem (s.getReg .x11 + 8) ∧
      u.getMem (s.getReg .x11 + 16) = s.getMem (s.getReg .x11 + 16) := by
  have e0 := r_keep hpre h 0 (Or.inl rfl)
  have e1 := r_keep hpre h 8 (Or.inr (Or.inl rfl))
  have e2 := r_keep hpre h 16 (Or.inr (Or.inr rfl))
  rv_eval [] at e0 e1 e2
  exact ⟨e0, e1, e2⟩

/-- `Plain(r)`. -/
theorem plain {s t₁ : MachineState} (hpre : ScalerPre s) (hr₁ : Reaches Image.code s t₁)
    (hp : Pro s t₁) (hsmall : (s.getReg .x12).toNat < 256) :
    ∃ t, Reaches Image.code s t ∧
      ((t.pc = returnAddress s ∧ Preserves s t ∧ ScalerPost s t) ∨ Dead Image.code t) := by
  have hb := bounds hpre
  have hof := hpre.outFree
  simp only [Outside] at hof
  have hR := ValidMemRange.bounds hpre.r (by decide)
  obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80008bf4_spec (hp.small hsmall) (by
      rv_eval [hp.x8, hp.x9]
      and_intros <;> first | valid_access hpre.out [hb] | valid_access hpre.r [hR])
  have k₂ := b80008bf4_keeps h₂
  have hm₂ := b80008bf4_frame h₂ (by rw [hp.x8]; addr_omega [hb])
  rw [hp.x8] at hm₂
  have p₀ := b80008bf4_m_x8_8 h₂
  have p₁ := b80008bf4_m_x8_16 h₂
  have p₂ := b80008bf4_m_x8_24 h₂
  rw [hp.x8, hp.x9] at p₀ p₁ p₂
  have inv₂ := hp.inv.step hpre (ByteFrame.of_memFrame hm₂ (by addr_omega [hb]) (by decide)
      (h₂.unaligned (by rv_eval [hp.x8]; and_intros <;> addr_omega [hb])))
    (fun a ha ↦ Or.inl (Or.inl (by addr_omega [ha, hb])))
    ((hm₂ _ (by addr_omega [hof.2, hb])).trans hp.inv.next) (Nat.le_refl _) hp.inv.fits
    fun r hr ↦ k₂ r (mem_of_mem hr _)
  obtain ⟨t, hr, hpct, hpres, htag, hmt, hheapt, hmono, -, hframe⟩ :=
    exit hpre (b80008bf4_pc h₂) inv₂ (by rw [k₂ .x8 (by decide), hp.x8])
  obtain ⟨e0, e1, e2⟩ := r_eAt hpre hp.inv
  refine ⟨t, hr₁.trans (hr₂.trans hr), Or.inl ⟨hpct, hpres, {
    heap := hheapt
    mono := hmono
    plain := fun _ ↦ ⟨by rw [htag, b80008bf4_x10 h₂], ?_⟩
    table := fun h ↦ absurd h (by omega)
    frame := hframe }⟩⟩
  unfold eAt
  rw [hmt _ (by addr_omega [hb]), hmt (s.getReg .x10 + 8 + 8) (by addr_omega [hb]),
    hmt (s.getReg .x10 + 8 + 16) (by addr_omega [hb])]
  rv_eval [p₀, p₁, p₂, e0, e1, e2]

/-- Before the fill: the `Vec` of `2112` zeros at `S - 112`, `r` and the bounds loaded. -/
structure Mid (s t₅ : MachineState) (P : Word) : Prop where
  inv : Inv s t₅ (t₅.getMem nextAddr)
  limb : LimbInv t₅ t₅ t₅ P (limbs (eAt s (s.getReg .x11))) 0
  x12 : t₅.getReg .x12 = 1
  x14 : t₅.getReg .x14 = 6
  x16 : t₅.getReg .x16 = P + BitVec.ofNat 64 tabBytes
  x17 : t₅.getReg .x17 = 16896
  x8 : t₅.getReg .x8 = s.getReg .x10
  buf : BufP P
  fresh : heapNext s ≤ P.toNat
  top : P.toNat + tabBytes ≤ (t₅.getMem nextAddr).toNat
  vec : VecOk t₅ (s.getReg .x2 - 112) 24 8
  ptr : vecPtr t₅ (s.getReg .x2 - 112) = P
  len : vecLen t₅ (s.getReg .x2 - 112) = 2112

theorem alloc {s t₁ : MachineState} (hF : FromElemSpec) (hpre : ScalerPre s)
    (hr₁ : Reaches Image.code s t₁) (hp : Pro s t₁) (hbig : ¬ (s.getReg .x12).toNat < 256) :
    ∃ t₅, Reaches Image.code s t₅ ∧ ((∃ P, Mid s t₅ P) ∨ Dead Image.code t₅) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hab := hst.above
  have hnx8 := hst.next
  have hro := hst.rodata
  have hheap := hpre.heap
  have hR := ValidMemRange.bounds hpre.r (by decide)
  obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80008a98_spec (hp.big hbig) trivial
  have k₂ := b80008a98_keeps h₂
  have inv₂ := hp.inv.same hpre (b80008a98_mem_same h₂) k₂
  have hsp₂ : t₂.getReg .x2 = s.getReg .x2 - 112 := (k₂ .x2 (by decide)).trans hp.sp
  have hn₂ : heapNext t₂ = heapNext s := by simp only [heapNext, inv₂.next]
  have hsl : stackLo t₂ fromElemStack = stackLo s scalerStack := by
    simp only [stackLo, fromElemStack, scalerStack, tryAllocStack, hsp₂]
    rw [Sym.sub_sub_lit]; rfl
  have hrod₂ : RodataOk t₂ := hpre.rodata.frame
    (fun a ha ↦ (b80008a98_mem_same h₂ a).trans (hp.mem a ha)) (by addr_omega [hb, hro])
  have hpre₂ : FromElemPre t₂ := {
    heap := ⟨hn₂ ▸ hheap.lo, hn₂ ▸ hheap.hi⟩
    out := by rw [b80008a98_x10 h₂, hp.sp]; valid_sub hst.valid [hb]
    elem := by rw [b80008a98_x11 h₂]; exact zero_valid
    stack := ⟨⟨by rw [hsl]; valid_sub hst.valid [hb], by rw [hsp₂]; addr_omega [hb]⟩,
      by rw [hsl]; exact hab, by rw [hsl]; addr_omega [hnx8, hb], by rw [hsl]; addr_omega [hro, hb]⟩
    outFree := by
      rw [b80008a98_x10 h₂, hp.sp]
      simp only [Outside]
      exact ⟨Or.inr (by addr_omega [hab, hb]), by addr_omega [hnx8, hb]⟩
    outStack := by rw [b80008a98_x10 h₂, hp.sp, hsl]; addr_omega [hb]
    elemFree := by
      rw [b80008a98_x11 h₂]
      simp only [Outside]
      exact ⟨Or.inr (by addr_omega []), by addr_omega []⟩
    elemStack := by rw [b80008a98_x11 h₂, hsl]; addr_omega [hro, hb]
    elemOut := by rw [b80008a98_x11 h₂, b80008a98_x10 h₂, hp.sp]; addr_omega [hro, hb] }
  obtain ⟨t₃, hr₃, ⟨hpc₃, hpres₃, hpost₃⟩ | hdead⟩ := hF.call hr₂ (b80008a98_pc h₂) hpre₂
  swap
  · exact ⟨t₃, hr₁.trans hr₃, Or.inr hdead⟩
  have hfr₃ := hpost₃.frame
  rw [b80008a98_x10 h₂, hp.sp, hsl] at hfr₃
  have inv₃ : Inv s t₃ (t₃.getMem nextAddr) := inv₂.step hpre hfr₃ (fun a ha ↦ by
      rcases ha with ha | ha | ha | ha
      · exact Or.inl (Or.inr (by addr_omega [ha, hb]))
      · exact Or.inl (Or.inr (by addr_omega [ha, hb]))
      · exact Or.inr (Or.inl ha)
      · simp only [Fresh, hn₂] at ha
        exact Or.inr (Or.inr ha))
    rfl (by rw [← heapNext, ← heapNext, ← hn₂]; exact hpost₃.mono) hpost₃.heap.hi
    fun r hr ↦ hpres₃ r (by unfold calleeSaved; exact mem_of_mem hr _)
  have hsp₃ : t₃.getReg .x2 = s.getReg .x2 - 112 := (hpres₃.reg .x2).trans hsp₂
  have hvec := hpost₃.vec
  have hlen₃ := hpost₃.len
  have hel₃ := hpost₃.elems
  have hfresh := hpost₃.fresh
  rw [b80008a98_x10 h₂, hp.sp] at hvec hlen₃ hel₃ hfresh
  rw [b80008a98_x12 h₂] at hlen₃ hel₃ hfresh
  rw [b80008a98_x11 h₂] at hel₃
  obtain ⟨P, hP⟩ : ∃ P, P = vecPtr t₃ (s.getReg .x2 - 112) := ⟨_, rfl⟩
  rw [← hP] at hfresh
  have hzero : eAt t₂ 0xa0000068 = 0 := by
    apply eAt_eq_of_limbs
    rv_eval [hrod₂.word (a := 0xa0000068) (v := 0), hrod₂.word (a := 0xa0000070) (v := 0),
      hrod₂.word (a := 0xa0000078) (v := 0)]
    rfl
  rw [hzero] at hel₃
  have hfit₃ := hpost₃.heap.hi
  simp only [NewBuf, hn₂, Sym.wordToNatLit] at hfresh
  have hPr : heapNext s ≤ P.toNat ∧ P.toNat + 24 * 2112 ≤ heapNext t₃ := by
    rcases hfresh.2 with h0 | h0
    · omega
    · exact h0
  have hBuf : BufP P := by
    have := hheap.lo
    exact ⟨hfresh.1, by simp only [heapStart] at this; omega, by simp only [tabBytes]; omega⟩
  obtain ⟨t₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b80008ab4_spec
    (by rw [hpc₃, returnAddress_eq, b80008a98_x1 h₂]; decide) (by
      rv_eval [hsp₃]
      valid_access hst.valid [hb])
  have k₄ := b80008ab4_keeps h₄
  have hm₄ := b80008ab4_mem_same h₄
  have hl₃ : t₃.getMem (s.getReg .x2 - 96) = 2112 := by
    rw [← hlen₃, vecLen]; rv_eval []
  obtain ⟨t₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b80008ac0_spec
    (b80008ab4_pc_not_taken h₄ (by rv_eval [hsp₃, hl₃]; decide)) (by
      rv_eval [k₄ .x2 (by decide), hsp₃, k₄ .x9 (by decide), hpres₃.reg .x9,
        k₂ .x9 (by decide), hp.x9]
      and_intros <;> first | valid_access hst.valid [hb] | valid_access hpre.r [hR])
  have k₅ := b80008ac0_keeps h₅
  have hm₅ := b80008ac0_mem_same h₅
  have inv₅ := (inv₃.same hpre hm₄ k₄).same hpre hm₅ k₅
  have hx9₄ : t₄.getReg .x9 = s.getReg .x11 := by
    rw [k₄ .x9 (by decide), hpres₃.reg .x9, k₂ .x9 (by decide), hp.x9]
  have hsp₄ : t₄.getReg .x2 = s.getReg .x2 - 112 := (k₄ .x2 (by decide)).trans hsp₃
  obtain ⟨e0, e1, e2⟩ := r_eAt hpre inv₃
  have hptr : t₃.getMem (s.getReg .x2 - 104) = P := by rw [hP, vecPtr]; rv_eval []
  have hrod₃ : RodataOk t₃ := rodataOk_of_byteFrame hrod₂ hfr₃ fun a hw ↦ by
    rcases hw with hw | hw | hw | hw
    · addr_omega [hw, hb, hro]
    · addr_omega [hw, hb, hro]
    · addr_omega [hw]
    · simp only [Fresh] at hw; addr_omega [hw, hfit₃]
  have hm54 (a : Word) : t₅.getMem a = t₃.getMem a := (hm₅ a).trans (hm₄ a)
  refine ⟨t₅, hr₁.trans (hr₃.trans (hr₄.trans hr₅)), Or.inl ⟨P, {
    inv := by have := inv₅; rwa [← hm54 nextAddr] at this
    limb := {
      ctx := ⟨fun _ _ ↦ rfl, MemFrame.refl _ _ _, fun _ _ ↦ rfl⟩
      pc := b80008ac0_pc h₅
      keep := fun _ _ ↦ rfl
      lt := by decide
      x10 := by rw [b80008ac0_x10 h₅, hsp₄, hm₄]; rv_eval [hptr]; simp
      x15 := by rw [b80008ac0_x15 h₅, hsp₄, hm₄]; rv_eval [hptr]; simp
      st := by
        rw [List.range_zero, List.foldl_nil, Prod.mk.injEq]
        refine ⟨?_, ?_⟩
        · have h53 : tab t₅ P = tab t₃ P := by simp only [tab, eAt, hm54]
          have hE : eListAt t₃ P 2112 = List.replicate 2112 0 := by
            have h := hel₃
            rw [vecEs, ← hP, hlen₃, show (2112 : Word).toNat = 2112 from rfl] at h
            exact h
          rw [h53, tab_eq_map, hE, List.map_replicate, show (3 * 11) <<< 6 = 2112 from rfl,
            limbs_zero]
        · simp only [monoOf, b80008ac0_x13 h₅, b80008ac0_x7 h₅, b80008ac0_x11 h₅, hx9₄, hm₄, e0,
            e1, e2, limbs_eAt] }
    x12 := b80008ac0_x12 h₅
    x14 := b80008ac0_x14 h₅
    x16 := by
      rw [h₅.reg .x16 rfl]
      rv_eval [hsp₄, hm₄, hptr, b80008ab4_x15 h₄, hsp₃, hl₃,
        hrod₃.word (a := 0xa0000010) (v := 0x2e8ba2e8ba2e8ba3)]
      exact end_eq P
    x17 := b80008ac0_x17 h₅
    x8 := by rw [k₅ .x8 (by decide), k₄ .x8 (by decide), hpres₃.reg .x8, k₂ .x8 (by decide), hp.x8]
    buf := hBuf
    fresh := hPr.1
    top := by rw [hm54]; have := hPr.2; simp only [heapNext, tabBytes] at this ⊢; omega
    vec := ⟨by
        have h := hvec.raw
        simp only [RawVecOk, Buf, vecCap, vecPtr, heapNext] at h ⊢
        simp only [hm54]
        exact h,
      by have h := hvec.len; simp only [vecLen, vecCap] at h ⊢; simp only [hm54]; exact h⟩
    ptr := by rw [vecPtr, hm54, ← vecPtr, ← hP]
    len := by rw [vecLen, hm54, ← vecLen, hlen₃] }⟩⟩

/-- The fill, `Table(vec)`, the epilogue. -/
theorem fill_exit {s t₅ : MachineState} {P : Word} (hpre : ScalerPre s)
    (hr₅ : Reaches Image.code s t₅) (hbig : ¬ (s.getReg .x12).toNat < 256) (hm : Mid s t₅ P) :
    ∃ t, Reaches Image.code s t ∧
      ((t.pc = returnAddress s ∧ Preserves s t ∧ ScalerPost s t) ∨ Dead Image.code t) := by
  have hb := bounds hpre
  have hos := hpre.outStack
  have hof := hpre.outFree
  simp only [Outside] at hof
  have hP := hm.buf
  have h1 := hP.hi
  have h2 := hP.lo
  have hPa := hP.align
  have htop := hm.top
  have hlo := hm.fresh
  have hsp₅ : t₅.getReg .x2 = s.getReg .x2 - 112 := by have := hm.inv.sp; rv_eval [] at this; exact this
  obtain ⟨v, hr₆, hpc₆, hctx, hkeep, htab⟩ := limb_loop hP hm.x12 hm.x14 hm.x17 hm.x16 hm.limb
  have inv₆ : Inv s v (t₅.getMem nextAddr) := hm.inv.step hpre
    (ByteFrame.of_memFrame hctx.mem hPa (by decide) hctx.una)
    (fun a ha ↦ Or.inr (Or.inr ⟨by addr_omega [ha, hlo], by addr_omega [ha, htop]⟩))
    (hctx.mem _ (by addr_omega [h1])) (Nat.le_refl _) hm.inv.fits
    fun r hr ↦ hctx.regs r (Runtime.mem_of_mem hr _)
  have hv8 : v.getReg .x8 = s.getReg .x10 := by rw [hctx.regs .x8 (by decide), hm.x8]
  have hv2 : v.getReg .x2 = s.getReg .x2 - 112 := by rw [hctx.regs .x2 (by decide), hsp₅]
  have hvt (a : Word) (ha : ¬ Within a P tabBytes) : v.getMem a = t₅.getMem a := hctx.mem a ha
  obtain ⟨w, hr₇, h₇⟩ := Sym.BlockSpec.reaches b80008bd4_spec hpc₆ (by
    rv_eval [hv8, hv2]
    and_intros <;> first | valid_access hpre.out [hb] | valid_access hpre.stack.valid [hb])
  have k₇ := b80008bd4_keeps h₇
  have hm₇ := b80008bd4_frame h₇ (by rw [hv8]; addr_omega [hb])
  rw [hv8] at hm₇
  have c₀ := b80008bd4_m_x8_8 h₇
  have c₁ := b80008bd4_m_x8_16 h₇
  have c₂ := b80008bd4_m_x8_24 h₇
  rv_eval [hv8, hv2] at c₀ c₁ c₂
  have inv₇ := inv₆.step hpre (ByteFrame.of_memFrame hm₇ (by addr_omega [hb]) (by decide)
      (h₇.unaligned (by rv_eval [hv8]; and_intros <;> addr_omega [hb])))
    (fun a ha ↦ Or.inl (Or.inl (by addr_omega [ha, hb])))
    ((hm₇ _ (by addr_omega [hof.2, hb])).trans inv₆.next) (Nat.le_refl _) inv₆.fits
    fun r hr ↦ k₇ r (mem_of_mem hr _)
  obtain ⟨t, hr, hpct, hpres, htag, hmt, hheapt, hmono, hnt, hframe⟩ :=
    exit hpre (b80008bd4_pc h₇) inv₇ (by rw [k₇ .x8 (by decide), hv8])
  have hS (o : Word) (ho : o = 0 ∨ o = 8 ∨ o = 16) :
      v.getMem (s.getReg .x2 - 112 + o) = t₅.getMem (s.getReg .x2 - 112 + o) :=
    hvt _ (by rcases ho with rfl | rfl | rfl <;> addr_omega [h1, hb, hm.inv.fits])
  have s0 := hS 0 (Or.inl rfl)
  have s1 := hS 8 (Or.inr (Or.inl rfl))
  have s2 := hS 16 (Or.inr (Or.inr rfl))
  rv_eval [] at s0 s1 s2
  have hcap : vecCap t (s.getReg .x10 + 8) = vecCap t₅ (s.getReg .x2 - 112) := by
    rw [vecCap, hmt _ (by addr_omega [hb]), c₀, s0, vecCap]
  have hptr : vecPtr t (s.getReg .x10 + 8) = P := by
    rw [vecPtr, hmt _ (by addr_omega [hb]), ← hm.ptr, vecPtr]; rv_eval [c₁, s1]
  have hlen : vecLen t (s.getReg .x10 + 8) = 2112 := by
    rw [vecLen, hmt _ (by addr_omega [hb]), ← hm.len, vecLen]; rv_eval [c₂, s2]
  have htw : tab t P = tab v P := by
    unfold tab eAt
    apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    have hw (a : Word) (ha1 : P.toNat ≤ a.toNat) (ha2 : a.toNat < P.toNat + tabBytes) :
        t.getMem a = v.getMem a :=
      (hmt a (by addr_omega [ha1, ha2, hof.1, h1, hlo, hb])).trans
        (hm₇ a (by addr_omega [ha1, ha2, hof.1, h1, hlo, hb]))
    rw [hw _ (by addr_omega [hi, h1]) (by addr_omega [hi, h1]),
      hw (P + BitVec.ofNat 64 (24 * i) + 8) (by addr_omega [hi, h1]) (by addr_omega [hi, h1]),
      hw (P + BitVec.ofNat 64 (24 * i) + 16) (by addr_omega [hi, h1]) (by addr_omega [hi, h1])]
  have hn₅ : heapNext t = (t₅.getMem nextAddr).toNat := hnt
  refine ⟨t, hr₅.trans (hr₆.trans (hr₇.trans hr)), Or.inl ⟨hpct, hpres, {
    heap := hheapt
    mono := hmono
    plain := fun h ↦ absurd h hbig
    table := fun _ ↦ ⟨by rw [htag, b80008bd4_x10 h₇], ⟨?_, ?_⟩, hlen, ?_, ?_⟩
    frame := hframe }⟩⟩
  · have h := hm.vec.raw
    simp only [RawVecOk, Buf] at h ⊢
    rw [hcap, hptr]
    rw [hm.ptr] at h
    refine ⟨h.1, ?_⟩
    rcases h.2 with h0 | h0
    · exact Or.inl h0
    · exact Or.inr ⟨h0.1, by rw [hn₅]; have := h0.2; simp only [heapNext] at this; omega⟩
  · rw [hcap, hlen, ← hm.len]; exact hm.vec.len
  · rw [vecEs, hptr, hlen, show (2112 : Word).toNat = 2112 from rfl, ← tab_eq_map, htw, htab]
  · simp only [NewBuf, hptr]
    exact ⟨hPa, Or.inr ⟨hlo, by rw [hn₅]; simp only [tabBytes] at htop; omega⟩⟩

/-- **`Scaler::new` meets its contract**, given `from_elem`'s. -/
theorem scaler_new_spec (hF : FromElemSpec) : ScalerSpec := by
  intro s hpc hpre
  obtain ⟨t₁, hr₁, hp⟩ := prologue hpc hpre
  by_cases hsmall : (s.getReg .x12).toNat < 256
  · exact plain hpre hr₁ hp hsmall
  obtain ⟨t₅, hr₅, ⟨P, hm⟩ | hdead⟩ := alloc hF hpre hr₁ hp hsmall
  swap
  · exact ⟨t₅, hr₅, Or.inr hdead⟩
  exact fill_exit hpre hr₅ hsmall hm

end Rv64Verifier.Proofs.Multilinear.ScalerNew
