import Rv64Verifier.Proofs.Bus.VbbContracts
import Rv64Verifier.Proofs.Multilinear.StackOffsets
import Rv64Verifier.Proofs.Runtime.Wrap
import Rv64Verifier.Blocks.F82
import Rv64Verifier.Blocks.F94

/-!
# `bus_layout`, at `0x80010acc`: the frame

```rust
fn bus_layout(framework_log_rows: &[usize], blocks: &[BusBlock]) -> BusLayout {
    let sizes: Vec<usize> = framework_log_rows.iter().copied()
        .chain(blocks.iter().map(|block| block.log_rows)).collect();
    let (offsets, depth) = stack_offsets(&sizes);
    let mut framework: Vec<Placement> = sizes.iter().zip(offsets)
        .map(|(&variables, index)| Placement { variables, index }).collect();
    let tables = framework.split_off(framework_log_rows.len());
    BusLayout { depth, framework, tables }
}
```

compiled (`Blocks/F82.lean`), with `S` the entry's `sp`, `n` rows and `m` blocks: `0x80010acc` saves
`ra`, `s0`..`s7` in a 112-byte frame and calls `try_allocate_in(S - 104, m + n, 0, 8, 8)`; the
`Vec` it gives is `reserve`d for `m + n` more (a call that returns at once), the rows `memcpy`d in
(`0x80010b64`, unless `n = 0`) and each block's `log_rows` copied after them (the loop at
`0x80010ba4`). `stack_offsets` then writes its `Vec` and depth at `S - 104`; a second buffer of
`16 (m + n)` bytes takes the pairs (the loop at `0x80010c18`), a third the last `m` of them
(`memcpy` at `0x80010c68`), and `0x80010c88` writes the result. `0x80010cd0` traps.

`memcpy` of no bytes (`memcpy_zero`) asks nothing of its pointers: the last copy may get the
dangling pointer of an empty buffer.
-/

namespace Rv64Verifier.Layout.BusLayout
open RiscvZkvm.Rv64 Rv64Verifier.Runtime Rv64Verifier.Sym Rv64Verifier.Bus
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- `memcpy` of no bytes returns at once, writing nothing. -/
def MemcpyZeroSpec : Prop := FunSpec Image.code 0x800126e4 (fun s ↦ s.getReg .x12 = 0)
  fun s t ↦ t.getReg .x10 = s.getReg .x10 ∧ ∀ a, t.getMem a = s.getMem a

theorem memcpy_zero : MemcpyZeroSpec := by
  refine Wrap.wrap (target := 0x80011ff8) (spec_of 18873 2 (by decide +kernel) (by decide +kernel) (by decide) (by decide))
    ?_ (fun s c hag hp ↦ by rw [hag.reg .x12 (by decide)]; exact hp)
    fun s c t hag ⟨h1, h2⟩ ↦ ⟨h1.trans (hag.reg .x10 (by decide)), fun a ↦ (h2 a).trans (hag.mem a)⟩
  intro s hpc h0
  obtain ⟨u₁, hr₁, h₁⟩ := BlockSpec.reaches Blocks.F94.b80011ff8_spec hpc (by rv_eval [])
  have k₁ := Blocks.F94.b80011ff8_keeps h₁
  obtain ⟨u₂, hr₂, h₂⟩ := BlockSpec.reaches Blocks.F94.b8001212c_spec
    (Blocks.F94.b80011ff8_pc_taken h₁ (by rw [h0]; decide)) (by rv_eval [])
  have k₂ := Blocks.F94.b8001212c_keeps h₂
  obtain ⟨u₃, hr₃, h₃⟩ := BlockSpec.reaches Blocks.F94.b80012138_spec
    (Blocks.F94.b8001212c_pc_not_taken h₂ (by
      rw [k₁ .x12 (by decide), h0]; simp)) (by rv_eval [])
  have k₃ := Blocks.F94.b80012138_keeps h₃
  obtain ⟨t, hr₄, h₄⟩ := BlockSpec.reaches Blocks.F94.b80012180_spec (Blocks.F94.b80012138_pc h₃)
    (by rv_eval [])
  have k₄ := Blocks.F94.b80012180_keeps h₄
  have hreg (r : Reg) (hr : r ∈ [Reg.x1, .x8, .x9, .x10, .x18, .x19, .x20, .x21, .x22, .x23, .x24,
      .x25, .x26, .x27]) : t.getReg r = s.getReg r := by
    rw [k₄ r (by revert hr; revert r; decide), k₃ r (by revert hr; revert r; decide),
      k₂ r (by revert hr; revert r; decide), k₁ r (by revert hr; revert r; decide)]
  have hx2 : t.getReg .x2 = s.getReg .x2 := by
    rw [Blocks.F94.b80012180_x2 h₄, k₃ .x2 (by decide), k₂ .x2 (by decide),
      Blocks.F94.b80011ff8_x2 h₁, BitVec.sub_add_cancel]
  refine ⟨t, hr₁.trans (hr₂.trans (hr₃.trans hr₄)), Or.inl ⟨?_, ?_, hreg .x10 (by decide), fun a ↦ ?_⟩⟩
  · rw [Blocks.F94.b80012180_pc h₄, k₃ .x1 (by decide), k₂ .x1 (by decide), k₁ .x1 (by decide),
      returnAddress_eq]
  · exact preserves_of hx2 (hreg _ (by decide)) (hreg _ (by decide)) (hreg _ (by decide))
      (hreg _ (by decide)) fun r hr ↦ hreg r (by revert hr; revert r; decide)
  · rw [Blocks.F94.b80012180_mem_same h₄, Blocks.F94.b80012138_mem_same h₃,
      Blocks.F94.b8001212c_mem_same h₂, Blocks.F94.b80011ff8_mem_same h₁]

/-! ## The frame -/

def slots : List (Nat × Reg) :=
  [(8, .x1), (16, .x8), (24, .x9), (32, .x18), (40, .x19), (48, .x20), (56, .x21), (64, .x22),
    (72, .x23)]

def kept : List Reg := [.x24, .x25, .x26, .x27]

/-- What the function writes besides its saved registers: the result, and the stack below them. -/
@[rv_addr] def W (s : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x10) 56 ∨ Within a (stackLo s busLayoutStack) 200

abbrev Inv (s u : MachineState) (nx : Word) : Prop := FnInv s u 112 slots kept (W s) nx

theorem bounds {s : MachineState} (h : BusLayoutPre s) :
    0xa0000110 ≤ (s.getReg .x2).toNat ∧ (s.getReg .x2).toNat ≤ 0xc0000008 ∧
      (s.getReg .x2).toNat % 16 = 0 ∧
      (stackLo s busLayoutStack).toNat = (s.getReg .x2).toNat - 272 := by
  have hm := h.stack.mapped (by decide) (by decide)
  have ha := h.stack.aligned
  simp only [busLayoutStack, reserveStack, Nat.reduceAdd] at hm ⊢
  omega

theorem stack112 {s : MachineState} (h : BusLayoutPre s) : RtStack s 112 := by
  have hb := bounds h
  have hst := h.stack
  have hn := hst.next
  have hro := hst.rodata
  have hab := hst.above
  refine ⟨⟨?_, hst.aligned⟩, by addr_omega [hb, hab], by addr_omega [hb, hn],
    by addr_omega [hb, hro]⟩
  exact ValidMemRange.sub hst.valid (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb])

theorem Inv.step {s u v : MachineState} {nx nx' : Word} {X : Word → Prop}
    (hpre : BusLayoutPre s) (h : Inv s u nx) (hX : ByteFrame u v X)
    (hXsub : ∀ a, X a → W s a ∨ Within a nextAddr 8 ∨ (heapNext s ≤ a.toNat ∧ a.toNat < nx'.toNat))
    (hnx : v.getMem nextAddr = nx') (hle : nx.toNat ≤ nx'.toNat) (hend : nx'.toNat ≤ heapEnd)
    (hr : ∀ r ∈ Reg.x2 :: kept, v.getReg r = u.getReg r) :
    Inv s v nx' := by
  have hb := bounds hpre
  have hs := hpre.outStack
  exact FnInv.step (m := 72) h (stack112 hpre) (by decide) (by decide) (by decide)
    (fun a ha ha' ↦ by
      simp only [W] at ha
      rcases ha with ha | ha <;> addr_omega [ha, ha', hs, hb])
    hX hXsub hnx hle hend (hr _ (by decide)) fun r hr' ↦ hr r (List.mem_cons_of_mem _ hr')

theorem Inv.same {s u v : MachineState} {nx : Word} (hpre : BusLayoutPre s) (h : Inv s u nx)
    (hm : ∀ a, v.getMem a = u.getMem a) {l : List Reg} (hk : ∀ r ∈ l, v.getReg r = u.getReg r)
    (hl : ∀ r ∈ Reg.x2 :: kept, r ∈ l := by decide) : Inv s v nx :=
  h.step hpre (ByteFrame.of_same hm fun _ ↦ False) (fun _ h ↦ h.elim) ((hm _).trans h.next)
    (Nat.le_refl _) h.fits fun r hr ↦ hk r (hl r hr)

/-- A step that writes only below the saved registers. -/
theorem Inv.frame {s u v : MachineState} {nx : Word} (hpre : BusLayoutPre s) (h : Inv s u nx)
    {lo : Word} {k : Nat} (hm : MemFrame u v lo k) (hlo : lo.toNat % 8 = 0) (hk : k % 8 = 0)
    (hu : ∀ a, a.toNat % 8 ≠ 0 → v.getMem a = u.getMem a)
    (hin : ∀ a, Within a lo k → W s a ∨ (heapNext s ≤ a.toNat ∧ a.toNat < nx.toNat))
    {l : List Reg} (hkr : ∀ r ∈ l, v.getReg r = u.getReg r)
    (hl : ∀ r ∈ Reg.x2 :: kept, r ∈ l := by decide) : Inv s v nx := by
  have hnx := h.next
  have hb := bounds hpre
  have hst := hpre.stack
  have hn8 := hst.next
  refine h.step hpre (ByteFrame.of_memFrame hm hlo hk hu) (fun a ha ↦ ?_) ?_ (Nat.le_refl _) h.fits
    fun r hr ↦ hkr r (hl r hr)
  · rcases hin a ha with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inr h')
  · rw [hm _ fun hw ↦ ?_, hnx]
    rcases hin _ hw with h' | h'
    · simp only [W] at h'
      have ho := hpre.outFree.2
      rcases h' with h' | h' <;> addr_omega [h', ho, hn8, hb]
    · have hfit := h.fits
      simp only [heapNext] at h'
      addr_omega [h', hfit]

theorem Inv.saved {s u : MachineState} {nx : Word} (h : Inv s u nx) :
    u.getReg .x2 = s.getReg .x2 - 112 ∧ u.getMem (s.getReg .x2 - 8) = s.getReg .x1 ∧
      u.getMem (s.getReg .x2 - 16) = s.getReg .x8 ∧ u.getMem (s.getReg .x2 - 24) = s.getReg .x9 ∧
      u.getMem (s.getReg .x2 - 32) = s.getReg .x18 ∧ u.getMem (s.getReg .x2 - 40) = s.getReg .x19 ∧
      u.getMem (s.getReg .x2 - 48) = s.getReg .x20 ∧ u.getMem (s.getReg .x2 - 56) = s.getReg .x21 ∧
      u.getMem (s.getReg .x2 - 64) = s.getReg .x22 ∧ u.getMem (s.getReg .x2 - 72) = s.getReg .x23 := by
  have hsp := h.sp
  have sl := h.slots
  simp only [slots, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
    and_true] at sl
  rv_eval [] at hsp sl
  exact ⟨hsp, sl⟩

/-- What `bus_layout` reads is unchanged. -/
theorem Inv.read {s u : MachineState} {nx : Word} (hpre : BusLayoutPre s) (h : Inv s u nx)
    {a p : Word} {k : Nat} (hr : LayoutRead s (s.getReg .x10) a k) (h1 : a.toNat ≤ p.toNat)
    (h2 : p.toNat + 8 ≤ a.toNat + k) : u.getMem p = s.getMem p := by
  have hb := bounds hpre
  have hf := hr.free
  have hs := hr.stack
  have ho := hr.out
  have hfit := h.fits
  have hk : a.toNat + k ≤ 0xc0000000 := by
    rcases hr.region with h0 | h0
    · omega
    · simp only [Transcript.Region, Mapped] at h0; omega
  simp only [Outside] at hf
  refine h.mem.getMem fun i hi hw ↦ ?_
  simp only [W] at hw
  rcases hw with (hw | hw) | hw | hw | hw <;> addr_omega [hw, hi, h1, h2, hf, hs, ho, hb, hfit, hk]

/-! ## The sizes -/

/-- The `i`-th size: a row, or a block's `log_rows`. -/
def srcWord (s : MachineState) (i : Nat) : Word :=
  if i < (s.getReg .x12).toNat then s.getMem (s.getReg .x11 + BitVec.ofNat 64 (8 * i))
  else s.getMem (s.getReg .x13 + BitVec.ofNat 64 (48 * (i - (s.getReg .x12).toNat)) + 24)

theorem sizes_eq (s : MachineState) :
    ((List.range ((s.getReg .x12).toNat + (s.getReg .x14).toNat)).map fun i ↦ (srcWord s i).toNat) =
      natsAt s (s.getReg .x11) (s.getReg .x12).toNat ++
        (blocksFrom s (s.getReg .x13) (s.getReg .x14).toNat).map (·.logRows) := by
  rw [List.range_add, List.map_append, List.map_map]
  congr 1
  · simp only [natsAt, readWords_eq_map, List.map_map]
    exact List.map_congr_left fun i hi ↦ by
      simp only [Function.comp, srcWord, List.mem_range.mp hi, ↓reduceIte]
  · simp only [blocksFrom, List.map_map]
    exact List.map_congr_left fun i _ ↦ by
      have hn : ¬ (s.getReg .x12).toNat + i < (s.getReg .x12).toNat := by omega
      simp only [Function.comp, srcWord, hn, ↓reduceIte, Nat.add_sub_cancel_left, blockAt]

end Rv64Verifier.Layout.BusLayout
