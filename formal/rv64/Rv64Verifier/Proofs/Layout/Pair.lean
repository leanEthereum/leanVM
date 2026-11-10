import Rv64Verifier.Proofs.Layout.ContractsVec
import Rv64Verifier.Proofs.Layout.PairRoom
import Rv64Verifier.Blocks.F87

/-!
# `Flushes::pair`, at `0x80011b98`

```rust
fn pair(&mut self, push: Vec<Form>, pull: Vec<Form>) {
    self.push.push(push);
    self.pull.push(pull);
}
```

compiled (`Blocks/F87.lean`): `0x80011b98` saves `ra`, `s0`..`s4` in a 48-byte frame and branches
on `push` being full, `0x80011bcc` then calling `grow_one(&self.push)`; `0x80011bd8` writes `push`'s
header into the slot after the last and the length, and branches on `pull` being full,
`0x80011c18` then calling `grow_one(&self.pull)`; `0x80011c24` writes `pull`'s header into its slot
and the length, restores and returns. Each side's room is `PairRoom.lean`'s `room`.
-/

namespace Rv64Verifier.Layout.Pair
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Blocks.F87
  Rv64Verifier.Model.LayoutMirror
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem slot_eq (p x : Word) : p + (x * 16 + x * 8) = p + BitVec.ofNat 64 (24 * x.toNat) := by
  congr 1
  apply BitVec.eq_of_toNat_eq
  have h16 : (16 : Word).toNat = 16 := rfl
  have h8 : (8 : Word).toNat = 8 := rfl
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, h16, h8]
  omega

/-- Everything a sound `Vec<Vec<Form>>` reaches is in the heap below `NEXT`. -/
theorem formVecsDeep_below {s : MachineState} {a x : Word} (h : FormVecsOk s a)
    (hx : formVecsDeep s a x) : heapStart ≤ x.toNat ∧ x.toNat < heapNext s := by
  rcases hx with hx | ⟨i, hi, hx⟩
  · have hraw := h.vec.raw
    simp only [RawVecOk, Buf] at hraw
    simp only [formVecsBuf, Within] at hx
    rcases hraw.2 with h0 | h0 <;> omega
  · exact (h.elems i hi).deep_below hx

set_option maxHeartbeats 4000000 in
/-- **`Flushes::pair` meets its contract**, given `grow_one`'s. -/
theorem pair_spec (hG : GrowOneFreshSpec 0x80011c78 24 8) : PairSpec := by
  intro s hpc hpre
  have hsb := hpre.stack.bounds (by decide) (by decide)
  have hab := hpre.stack.above
  have hnx := hpre.stack.next
  have hsf := hpre.selfFree
  have hss := hpre.selfStack
  have hselfb := ValidMemRange.bounds hpre.self (by decide)
  have hok := hpre.ok
  have hheap := hpre.heap
  simp only [pairStack, growOneStack, Nat.reduceAdd] at hsb hab hnx hss
  -- the frame
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80011b98_spec hpc (by
    rv_eval []
    and_intros <;> first
      | valid_access hpre.stack.valid [hsb]
      | valid_access hpre.self [hselfb]
      | addr_omega [hsb, hss, hselfb])
  have k₁ := b80011b98_keeps h₁
  have hm₁ := b80011b98_frame h₁ (by addr_omega [hsb])
  have hs₁ (y : Word) (hy : Apart y 8 (stackLo s 208) 208) (hw : y.toNat + 8 ≤ 2 ^ 64) :
      t₁.getMem y = s.getMem y := hm₁ y (by addr_omega [hy, hw, hsb])
  have x2₁ : t₁.getReg .x2 = s.getReg .x2 - 48 := b80011b98_x2 h₁
  have hhd (k : Nat) (hk : k + 8 ≤ 48) :
      t₁.getMem (s.getReg .x10 + BitVec.ofNat 64 k) = s.getMem (s.getReg .x10 + BitVec.ofNat 64 k) :=
    hs₁ _ (by addr_omega [hss, hselfb, hk]) (by addr_omega [hselfb, hk])
  have hn₁ : t₁.getMem nextAddr = s.getMem nextAddr := hs₁ _ (by addr_omega [hnx]) (by decide)
  have hnext₁ : heapNext t₁ = heapNext s := by simp only [heapNext, hn₁]
  have hheap₁ : HeapOk t₁ := ⟨hnext₁ ▸ hheap.lo, hnext₁ ▸ hheap.hi⟩
  have hcap₁ : vecCap t₁ (s.getReg .x10) = vecCap s (s.getReg .x10) := by
    simpa [vecCap] using hhd 0 (by decide)
  have hptr₁ : vecPtr t₁ (s.getReg .x10) = vecPtr s (s.getReg .x10) := hhd 8 (by decide)
  have hlen₁ : vecLen t₁ (s.getReg .x10) = vecLen s (s.getReg .x10) := hhd 16 (by decide)
  have hvec₁ : VecOk t₁ (s.getReg .x10) 24 8 := by
    have := hok.push.vec
    exact ⟨by simp only [RawVecOk, Buf, hptr₁, hcap₁, hnext₁]; exact this.raw,
      by rw [hlen₁, hcap₁]; exact this.len⟩
  have hst₁ : RtStack t₁ growOneStack := hpre.stack.inner (k := 48) x2₁ (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have hlo₁ : stackLo t₁ growOneStack = s.getReg .x2 - 208 := by
    simp only [stackLo, x2₁, growOneStack]; rv_eval []
  -- room on `push`
  obtain ⟨u₁, hru₁, ⟨hpcu₁, hregu₁, hroom₁⟩ | hdead⟩ : ∃ u, Reaches Image.code t₁ u ∧
      ((u.pc = 0x80011bd8 ∧ (∀ r ∈ calleeSaved, u.getReg r = t₁.getReg r) ∧
        Room t₁ u (s.getReg .x10)) ∨ Dead Image.code u) := by
    by_cases hfull : vecLen t₁ (s.getReg .x10) = vecCap t₁ (s.getReg .x10)
    · refine room hG hvec₁ hheap₁ (ValidMemRange.sub hpre.self (by addr_omega [hselfb])
        (by addr_omega [hselfb]) (by addr_omega [hselfb])) hst₁
        (by simp only [Outside, hnext₁] at hsf ⊢; exact ⟨by omega, by addr_omega [hsf.2, hselfb]⟩)
        (by rw [hlo₁]; addr_omega [hss, hselfb, hsb]) hfull ?_ (by decide)
      obtain ⟨z, hrz, hz⟩ := Sym.BlockSpec.reaches b80011bcc_spec
        (b80011b98_pc_not_taken h₁ (by have := hfull; rw [hlen₁, hcap₁] at this; exact this)) trivial
      have kz := b80011bcc_keeps hz
      exact ⟨z, hrz, b80011bcc_pc hz, by rw [b80011bcc_x10 hz, b80011b98_x8 h₁],
        b80011bcc_x1 hz, fun r hr ↦ kz r (mem_of_mem hr _), b80011bcc_mem_same hz⟩
    · exact ⟨t₁, Reaches.refl _, Or.inl ⟨b80011b98_pc_taken h₁ (by
        have := hfull; rw [hlen₁, hcap₁] at this; exact this), fun _ _ ↦ rfl,
        Room.refl hheap₁ hvec₁ hfull⟩⟩
  swap
  · exact ⟨u₁, hr₁.trans hru₁, Or.inr hdead⟩
  -- `push`'s header into the slot, and the length
  have hpush := hok.push
  have hpull := hok.pull
  have hgb := ValidMemRange.bounds hpre.push (by decide)
  have hhb := ValidMemRange.bounds hpre.pull (by decide)
  have hgf := hpre.pushFree
  have hhf := hpre.pullFree
  have hgs := hpre.pushStack
  have hhs := hpre.pullStack
  simp only [pairStack, growOneStack, Nat.reduceAdd] at hgs hhs
  have hapart := hpre.apart
  have r₂ : u₁.getReg .x2 = s.getReg .x2 - 48 := (hregu₁ .x2 (by decide)).trans x2₁
  have r₈ : u₁.getReg .x8 = s.getReg .x10 := (hregu₁ .x8 (by decide)).trans (b80011b98_x8 h₁)
  have r₉ : u₁.getReg .x9 = s.getReg .x12 := (hregu₁ .x9 (by decide)).trans (b80011b98_x9 h₁)
  have r₁₈ : u₁.getReg .x18 = s.getReg .x11 := (hregu₁ .x18 (by decide)).trans (b80011b98_x18 h₁)
  have r₁₉ : u₁.getReg .x19 = vecLen s (s.getReg .x10) := (hregu₁ .x19 (by decide)).trans
    (b80011b98_x19 h₁)
  have hnu₁ := hroom₁.heap.hi
  have hroomu₁ := hroom₁.room
  have hrawu₁ := hroom₁.raw
  have hmono₁ := hroom₁.mono
  rw [hlen₁] at hroomu₁
  simp only [RawVecOk, Buf] at hrawu₁
  obtain ⟨hP₁al, hP₁b⟩ : (vecPtr u₁ (s.getReg .x10)).toNat % 8 = 0 ∧
      heapStart ≤ (vecPtr u₁ (s.getReg .x10)).toNat ∧
      (vecPtr u₁ (s.getReg .x10)).toNat + 24 * (vecCap u₁ (s.getReg .x10)).toNat ≤ heapNext u₁ := by
    refine ⟨hrawu₁.1, ?_⟩
    rcases hrawu₁.2 with h0 | h0
    · exfalso; rw [Nat.mul_eq_zero] at h0; omega
    · omega
  simp only [heapNext, heapStart, heapEnd] at hP₁b hnu₁ hmono₁
  -- what `u₁` holds where `s` did: the frame wrote `push`'s first 16 bytes, the stack, `NEXT` and
  -- the heap from `NEXT` on
  have hfu₁ : DFrame s u₁ fun y ↦ Within y (s.getReg .x10) 16 ∨ Within y (stackLo s 208) 208 ∨
      Within y nextAddr 8 ∨ Fresh s u₁ y :=
    (hm₁.dframe.union hroom₁.frame).mono fun y hy ↦ by
      rcases hy with hy | hy | hy | hy | hy
      · exact Or.inr (Or.inl (by addr_omega [hy, hsb]))
      · exact Or.inl hy
      · rw [hlo₁] at hy; exact Or.inr (Or.inl (by addr_omega [hy, hsb]))
      · exact Or.inr (Or.inr (Or.inl hy))
      · exact Or.inr (Or.inr (Or.inr (by simpa only [Fresh, hnext₁] using hy)))
  have hku₁ (y : Word) (h1 : ¬ Within y (s.getReg .x10) 16 ∧ Apart y 8 (s.getReg .x10) 16)
      (h2 : Apart y 8 (stackLo s 208) 208) (h3 : Apart y 8 nextAddr 8)
      (h4 : y.toNat + 8 ≤ heapNext s ∨ heapEnd ≤ y.toNat) (hw : y.toNat + 8 ≤ 2 ^ 64) :
      u₁.getMem y = s.getMem y :=
    hfu₁.getMem_of (fun z hz hzw ↦ by
      have hhi₁ := hroom₁.heap.hi
      rcases hzw with hzw | hzw | hzw | hzw
      · addr_omega [hz, hzw, h1.2]
      · addr_omega [hz, hzw, h2]
      · addr_omega [hz, hzw, h3]
      · simp only [Fresh, heapNext, heapEnd] at hzw h4 hhi₁; addr_omega [hz, hzw, h4, hhi₁]) hw
  have hlenb := hok.push.vec.len
  simp only [vecPtr, vecCap, vecLen] at hP₁al hP₁b hroomu₁ hlenb r₁₉
  have hbuf₁ : ValidMemRange (u₁.getMem (s.getReg .x10 + 8))
      (3 * (u₁.getMem (s.getReg .x10)).toNat) :=
    validMemRange_of hP₁al (Or.inl ⟨by omega, by omega⟩)
  have hsep₁ : Apart (s.getReg .x10) 48 (u₁.getMem (s.getReg .x10 + 8))
      (24 * (u₁.getMem (s.getReg .x10)).toNat) := by
    rcases hroom₁.ptr with ⟨hp, hc⟩ | hp
    · have hp' : u₁.getMem (s.getReg .x10 + 8) = vecPtr s (s.getReg .x10) := hp.trans hptr₁
      have hc' : u₁.getMem (s.getReg .x10) = vecCap s (s.getReg .x10) := hc.trans hcap₁
      rw [hp', hc']
      exact apart_of_forall fun x hx hb ↦ hok.header x hx (Or.inl (Or.inl hb))
    · simp only [vecPtr, heapNext] at hp
      have := hsf.1
      simp only [heapNext, heapEnd] at this hn₁
      rw [hn₁] at hp
      simp only [Apart]
      omega
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80011bd8_spec hpcu₁ (by
    rv_eval [r₂, r₈, r₉, r₁₈, r₁₉]
    simp only [slot_eq]
    and_intros <;> first
      | valid_access hpre.self [hselfb]
      | valid_access hpre.push [hgb]
      | valid_access hbuf₁ [hP₁al, hP₁b, hroomu₁, hnu₁]
      | addr_omega [hsep₁, hP₁al, hP₁b, hroomu₁, hnu₁, hselfb])
  have k₃ := b80011bd8_keeps h₃
  have hf₃ : DFrame u₁ t₃ fun y ↦ Within y (u₁.getMem (s.getReg .x10 + 8) +
      BitVec.ofNat 64 (24 * (s.getMem (s.getReg .x10 + 16)).toNat)) 24 ∨
        Within y (s.getReg .x10 + 16) 8 :=
    (h₃.byteFrame (by
      rv_eval [r₈, r₁₉]
      simp only [slot_eq]
      and_intros <;> first
        | (intro i hi; exact Or.inl (by addr_omega [hi, hP₁al, hP₁b, hroomu₁, hnu₁]))
        | (intro i hi; exact Or.inr (by addr_omega [hi, hselfb]))
        | addr_omega [hP₁al, hP₁b, hroomu₁, hnu₁, hselfb])).dframe
  have hmid (y : Word) (h1 : Apart y 8 (u₁.getMem (s.getReg .x10 + 8) +
      BitVec.ofNat 64 (24 * (s.getMem (s.getReg .x10 + 16)).toNat)) 24)
      (h2 : Apart y 8 (s.getReg .x10 + 16) 8) (hw : y.toNat + 8 ≤ 2 ^ 64) :
      t₃.getMem y = u₁.getMem y :=
    hf₃.getMem_of (fun z hz hzw ↦ by
      rcases hzw with hzw | hzw
      · addr_omega [hz, hzw, h1]
      · addr_omega [hz, hzw, h2]) hw
  -- `pull`'s header is still `s`'s
  have hpullw (k : Nat) (hk1 : 24 ≤ k) (hk2 : k + 8 ≤ 48) :
      t₃.getMem (s.getReg .x10 + BitVec.ofNat 64 k) = s.getMem (s.getReg .x10 + BitVec.ofNat 64 k) := by
    rw [hmid _ (by addr_omega [hsep₁, hselfb, hk1, hk2, hroomu₁, hP₁b, hnu₁])
      (by addr_omega [hselfb, hk1, hk2]) (by addr_omega [hselfb, hk2])]
    refine hku₁ _ ⟨by addr_omega [hselfb, hk1, hk2], by addr_omega [hselfb, hk1, hk2]⟩
      (by addr_omega [hss, hselfb, hk1, hk2]) (by have := hsf.2; addr_omega [this, hselfb, hk1, hk2])
      ?_ (by addr_omega [hselfb, hk2])
    have := hsf.1
    simp only [heapNext] at this ⊢
    rcases this with h0 | h0
    · left; addr_omega [h0, hselfb, hk1, hk2]
    · right; addr_omega [h0, hselfb, hk1, hk2]
  have hn₃ : t₃.getMem nextAddr = u₁.getMem nextAddr :=
    hmid _ (by addr_omega [hP₁b, hroomu₁, hnu₁]) (by have := hsf.2; addr_omega [this, hselfb])
      (by decide)
  have hnext₃ : heapNext t₃ = heapNext u₁ := by simp only [heapNext, hn₃]
  have hheap₃ : HeapOk t₃ := ⟨hnext₃ ▸ hroom₁.heap.lo, hnext₃ ▸ hroom₁.heap.hi⟩
  have hv₃ : vecCap t₃ (s.getReg .x10 + 24) = vecCap s (s.getReg .x10 + 24) := by
    simpa [vecCap] using hpullw 24 (by decide) (by decide)
  have hq₃ : vecPtr t₃ (s.getReg .x10 + 24) = vecPtr s (s.getReg .x10 + 24) := by
    simpa [vecPtr, BitVec.add_assoc] using hpullw 32 (by decide) (by decide)
  have hl₃ : vecLen t₃ (s.getReg .x10 + 24) = vecLen s (s.getReg .x10 + 24) := by
    simpa [vecLen, BitVec.add_assoc] using hpullw 40 (by decide) (by decide)
  have hmono₃ : heapNext s ≤ heapNext t₃ := by
    rw [hnext₃]; have := hroom₁.mono; rw [hnext₁] at this; exact this
  have hvec₃ : VecOk t₃ (s.getReg .x10 + 24) 24 8 := by
    have := hok.pull.vec
    refine ⟨?_, by rw [hl₃, hv₃]; exact this.len⟩
    have hr := this.raw
    simp only [RawVecOk, Buf, hq₃, hv₃] at hr ⊢
    exact ⟨hr.1, hr.2.imp id fun h' ↦ ⟨h'.1, Nat.le_trans h'.2 hmono₃⟩⟩
  have x2₃ : t₃.getReg .x2 = s.getReg .x2 - 48 := (k₃ .x2 (by decide)).trans r₂
  have hst₃ : RtStack t₃ growOneStack := hpre.stack.inner (k := 48) x2₃ (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have hlo₃ : stackLo t₃ growOneStack = s.getReg .x2 - 208 := by
    simp only [stackLo, x2₃, growOneStack]; rv_eval []
  have hpc₃ := b80011bd8_pc_taken h₃
  have hpc₃' := b80011bd8_pc_not_taken h₃
  rw [r₈] at hpc₃ hpc₃'
  have e40 : u₁.getMem (s.getReg .x10 + 40) = vecLen t₃ (s.getReg .x10 + 24) := by
    simp only [vecLen, BitVec.add_assoc]
    exact (hmid _ (by addr_omega [hsep₁, hselfb, hroomu₁, hP₁b, hnu₁]) (by addr_omega [hselfb])
      (by addr_omega [hselfb])).symm
  have e24 : u₁.getMem (s.getReg .x10 + 24) = vecCap t₃ (s.getReg .x10 + 24) := by
    simp only [vecCap]
    exact (hmid _ (by addr_omega [hsep₁, hselfb, hroomu₁, hP₁b, hnu₁]) (by addr_omega [hselfb])
      (by addr_omega [hselfb])).symm
  rw [e40, e24] at hpc₃ hpc₃'
  -- room on `pull`
  obtain ⟨u₂, hru₂, ⟨hpcu₂, hregu₂, hroom₂⟩ | hdead⟩ : ∃ u, Reaches Image.code t₃ u ∧
      ((u.pc = 0x80011c24 ∧ (∀ r ∈ calleeSaved, u.getReg r = t₃.getReg r) ∧
        Room t₃ u (s.getReg .x10 + 24)) ∨ Dead Image.code u) := by
    by_cases hfull : vecLen t₃ (s.getReg .x10 + 24) = vecCap t₃ (s.getReg .x10 + 24)
    · refine room hG hvec₃ hheap₃ (ValidMemRange.sub hpre.self (by addr_omega [hselfb])
        (by addr_omega [hselfb]) (by addr_omega [hselfb])) hst₃ ?_
        (by rw [hlo₃]; addr_omega [hss, hselfb, hsb]) hfull ?_ (by decide)
      · have := hsf.1
        have h2 := hsf.2
        simp only [Outside, heapNext] at this hmono₃ ⊢
        refine ⟨?_, by addr_omega [h2, hselfb]⟩
        rcases this with h0 | h0
        · left; addr_omega [h0, hselfb, hmono₃]
        · right; addr_omega [h0, hselfb]
      obtain ⟨z, hrz, hz⟩ := Sym.BlockSpec.reaches b80011c18_spec (hpc₃' hfull) trivial
      have kz := b80011c18_keeps hz
      exact ⟨z, hrz, b80011c18_pc hz, by rw [b80011c18_x10 hz, k₃ .x8 (by decide), r₈],
        b80011c18_x1 hz, fun r hr ↦ kz r (mem_of_mem hr _), b80011c18_mem_same hz⟩
    · exact ⟨t₃, Reaches.refl _, Or.inl ⟨hpc₃ hfull, fun _ _ ↦ rfl,
        Room.refl hheap₃ hvec₃ hfull⟩⟩
  swap
  · exact ⟨u₂, hr₁.trans (hru₁.trans (hr₃.trans hru₂)), Or.inr hdead⟩
  -- `pull`'s header into its slot, the length, and return
  have q₂ : u₂.getReg .x2 = s.getReg .x2 - 48 := (hregu₂ .x2 (by decide)).trans x2₃
  have q₈ : u₂.getReg .x8 = s.getReg .x10 := by
    rw [hregu₂ .x8 (by decide), k₃ .x8 (by decide), r₈]
  have q₉ : u₂.getReg .x9 = s.getReg .x12 := by
    rw [hregu₂ .x9 (by decide), k₃ .x9 (by decide), r₉]
  have q₂₀ : u₂.getReg .x20 = vecLen s (s.getReg .x10 + 24) := by
    rw [hregu₂ .x20 (by decide), b80011bd8_x20 h₃, r₈, e40, hl₃]
  have hnu₂ := hroom₂.heap.hi
  have hroomu₂ := hroom₂.room
  have hrawu₂ := hroom₂.raw
  rw [hl₃] at hroomu₂
  simp only [RawVecOk, Buf] at hrawu₂
  obtain ⟨hQ₂al, hQ₂b⟩ : (vecPtr u₂ (s.getReg .x10 + 24)).toNat % 8 = 0 ∧
      heapStart ≤ (vecPtr u₂ (s.getReg .x10 + 24)).toNat ∧
      (vecPtr u₂ (s.getReg .x10 + 24)).toNat + 24 * (vecCap u₂ (s.getReg .x10 + 24)).toNat ≤
        heapNext u₂ := by
    refine ⟨hrawu₂.1, ?_⟩
    rcases hrawu₂.2 with h0 | h0
    · exfalso; rw [Nat.mul_eq_zero] at h0; omega
    · omega
  have hQ : vecPtr u₂ (s.getReg .x10 + 24) = u₂.getMem (s.getReg .x10 + 32) := by
    simp only [vecPtr]; rv_eval []
  have hC : vecCap u₂ (s.getReg .x10 + 24) = u₂.getMem (s.getReg .x10 + 24) := rfl
  have hM : vecLen s (s.getReg .x10 + 24) = s.getMem (s.getReg .x10 + 40) := by
    simp only [vecLen]; rv_eval []
  rw [hQ] at hQ₂al
  rw [hQ, hC] at hQ₂b
  rw [hC, hM] at hroomu₂
  rw [hM] at q₂₀
  simp only [heapNext, heapStart, heapEnd] at hQ₂b hnu₂
  have hbuf₂ : ValidMemRange (u₂.getMem (s.getReg .x10 + 32))
      (3 * (u₂.getMem (s.getReg .x10 + 24)).toNat) :=
    validMemRange_of hQ₂al (Or.inl ⟨by omega, by omega⟩)
  have hsep₂ : Apart (s.getReg .x10) 48 (u₂.getMem (s.getReg .x10 + 32))
      (24 * (u₂.getMem (s.getReg .x10 + 24)).toNat) := by
    rcases hroom₂.ptr with ⟨hp, hc⟩ | hp
    · rw [← hQ, ← hC, hp, hc, hq₃, hv₃]
      exact apart_of_forall fun x hx hb ↦ hok.header x hx (Or.inr (Or.inl hb))
    · rw [hQ] at hp
      have := hsf.1
      simp only [heapNext, heapEnd] at this hp hmono₃
      simp only [Apart]
      omega
  obtain ⟨t₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b80011c24_spec hpcu₂ (by
    rv_eval [q₂, q₈, q₉, q₂₀]
    simp only [slot_eq]
    and_intros <;> first
      | valid_access hpre.stack.valid [hsb]
      | valid_access hpre.self [hselfb]
      | valid_access hpre.pull [hhb]
      | valid_access hbuf₂ [hQ₂al, hQ₂b, hroomu₂, hnu₂]
      | addr_omega [hsep₂, hQ₂al, hQ₂b, hroomu₂, hnu₂, hselfb, hsb, hab, hss, hhs])
  have k₅ := b80011c24_keeps h₅
  have hf₅ : DFrame u₂ t₅ fun y ↦ Within y (u₂.getMem (s.getReg .x10 + 32) +
      BitVec.ofNat 64 (24 * (s.getMem (s.getReg .x10 + 40)).toNat)) 24 ∨
        Within y (s.getReg .x10 + 40) 8 :=
    (h₅.byteFrame (by
      rv_eval [q₈, q₂₀]
      simp only [slot_eq]
      and_intros <;> first
        | (intro i hi; exact Or.inl (by addr_omega [hi, hQ₂al, hQ₂b, hroomu₂, hnu₂]))
        | (intro i hi; exact Or.inr (by addr_omega [hi, hselfb]))
        | addr_omega [hQ₂al, hQ₂b, hroomu₂, hnu₂, hselfb])).dframe
  -- the frame's slots, from the entry to `u₂`
  have hsaved (k : Nat) (hk1 : 8 ≤ k) (hk2 : k ≤ 48) :
      u₂.getMem (s.getReg .x2 - BitVec.ofNat 64 k) = t₁.getMem (s.getReg .x2 - BitVec.ofNat 64 k) := by
    have hhi₂ := hroom₂.heap.hi
    have hhi₁ := hroom₁.heap.hi
    simp only [heapNext, heapEnd] at hhi₂ hhi₁
    have e1 := hroom₂.frame.getMem_of (a := s.getReg .x2 - BitVec.ofNat 64 k) (fun z hz hzw ↦ by
      rw [hlo₃] at hzw
      rcases hzw with hzw | hzw | hzw | hzw
      · addr_omega [hz, hzw, hss, hselfb, hk1, hk2, hsb]
      · addr_omega [hz, hzw, hk1, hk2, hsb]
      · addr_omega [hz, hzw, hnx, hk1, hk2, hsb]
      · simp only [Fresh, heapNext] at hzw; addr_omega [hz, hzw, hab, hhi₂, hk1, hk2, hsb])
      (by addr_omega [hk1, hk2, hsb])
    have e2 := hmid (s.getReg .x2 - BitVec.ofNat 64 k)
      (by addr_omega [hP₁b, hroomu₁, hnu₁, hab, hk1, hk2, hsb])
      (by addr_omega [hss, hselfb, hk1, hk2, hsb]) (by addr_omega [hk1, hk2, hsb])
    have e3 := hroom₁.frame.getMem_of (a := s.getReg .x2 - BitVec.ofNat 64 k) (fun z hz hzw ↦ by
      rw [hlo₁] at hzw
      rcases hzw with hzw | hzw | hzw | hzw
      · addr_omega [hz, hzw, hss, hselfb, hk1, hk2, hsb]
      · addr_omega [hz, hzw, hk1, hk2, hsb]
      · addr_omega [hz, hzw, hnx, hk1, hk2, hsb]
      · simp only [Fresh, heapNext] at hzw; addr_omega [hz, hzw, hab, hhi₁, hk1, hk2, hsb])
      (by addr_omega [hk1, hk2, hsb])
    rw [e1, e2, e3]
  have pc₅ := b80011c24_pc h₅
  have r₅₁ := b80011c24_x1 h₅
  have r₅₂ := b80011c24_x2 h₅
  have r₅₈ := b80011c24_x8 h₅
  have r₅₉ := b80011c24_x9 h₅
  have r₅₁₈ := b80011c24_x18 h₅
  have r₅₁₉ := b80011c24_x19 h₅
  have r₅₂₀ := b80011c24_x20 h₅
  rw [q₂] at pc₅ r₅₁ r₅₂ r₅₈ r₅₉ r₅₁₈ r₅₁₉ r₅₂₀
  rv_eval [] at pc₅ r₅₁ r₅₂ r₅₈ r₅₉ r₅₁₈ r₅₁₉ r₅₂₀
  have sv₈ := hsaved 8 (by decide) (by decide)
  have sv₁₆ := hsaved 16 (by decide) (by decide)
  have sv₂₄ := hsaved 24 (by decide) (by decide)
  have sv₃₂ := hsaved 32 (by decide) (by decide)
  have sv₄₀ := hsaved 40 (by decide) (by decide)
  have sv₄₈ := hsaved 48 (by decide) (by decide)
  rv_eval [] at sv₈ sv₁₆ sv₂₄ sv₃₂ sv₄₀ sv₄₈
  rw [sv₈, b80011b98_m_x2_n8 h₁] at pc₅
  rw [sv₁₆, b80011b98_m_x2_n16 h₁] at r₅₈
  rw [sv₂₄, b80011b98_m_x2_n24 h₁] at r₅₉
  rw [sv₃₂, b80011b98_m_x2_n32 h₁] at r₅₁₈
  rw [sv₄₀, b80011b98_m_x2_n40 h₁] at r₅₁₉
  rw [sv₄₈, b80011b98_m_x2_n48 h₁] at r₅₂₀
  have hk (r : Reg) (hr : r ∈ [Reg.x21, .x22, .x23, .x24, .x25, .x26, .x27]) :
      t₅.getReg r = s.getReg r := by
    rw [k₅ r (mem_of_mem hr _), hregu₂ r (mem_of_mem hr _), k₃ r (mem_of_mem hr _),
      hregu₁ r (mem_of_mem hr _), k₁ r (mem_of_mem hr _)]
  refine ⟨t₅, hr₁.trans (hru₁.trans (hr₃.trans (hru₂.trans hr₅))),
    Or.inl ⟨pc₅.trans (returnAddress_eq s).symm, preserves_of r₅₂ r₅₈ r₅₉ r₅₁₈ r₅₁₉ ?_, ?_⟩⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | hr
    · exact r₅₂₀
    · exact hk r (by simp only [List.mem_cons, List.not_mem_nil, or_false]; tauto)
  -- the heap
  have hhi₂ := hroom₂.heap.hi
  have hmono₂ := hroom₂.mono
  simp only [heapNext, heapEnd] at hhi₂ hmono₂ hmono₃ hnext₃
  have hn₅ : t₅.getMem nextAddr = u₂.getMem nextAddr :=
    hf₅.getMem_of (fun z hz hzw ↦ by
      rcases hzw with hzw | hzw
      · addr_omega [hz, hzw, hQ₂b, hroomu₂, hnu₂]
      · have := hsf.2; addr_omega [hz, hzw, this, hselfb]) (by decide)
  have hnext₅ : heapNext t₅ = heapNext u₂ := by simp only [heapNext, hn₅]
  -- the old buffers, and the new ones: each the old one or fresh
  have hPold := vecBuf_bounds hok.push.vec (by decide)
  have hQold := vecBuf_bounds hok.pull.vec (by decide)
  have hpushLen := hok.push.vec.len
  have hpullLen := hok.pull.vec.len
  simp only [vecPtr, vecCap, heapNext, heapStart, BitVec.add_assoc] at hPold hQold
  simp only [vecCap, vecLen, BitVec.add_assoc] at hpushLen hpullLen
  rv_eval [] at hPold hQold hpushLen hpullLen
  have hP₁c : (u₁.getMem (s.getReg .x10 + 8) = s.getMem (s.getReg .x10 + 8) ∧
      u₁.getMem (s.getReg .x10) = s.getMem (s.getReg .x10)) ∨
      (s.getMem nextAddr).toNat ≤ (u₁.getMem (s.getReg .x10 + 8)).toNat := by
    rcases hroom₁.ptr with ⟨hp, hc⟩ | hp
    · exact Or.inl ⟨hp.trans hptr₁, hc.trans hcap₁⟩
    · right; simp only [heapNext, vecPtr, hn₁] at hp; exact hp
  have hQ₂c : (u₂.getMem (s.getReg .x10 + 32) = s.getMem (s.getReg .x10 + 32) ∧
      u₂.getMem (s.getReg .x10 + 24) = s.getMem (s.getReg .x10 + 24)) ∨
      (u₁.getMem nextAddr).toNat ≤ (u₂.getMem (s.getReg .x10 + 32)).toNat := by
    rcases hroom₂.ptr with ⟨hp, hc⟩ | hp
    · left
      rw [← hQ, ← hC, hp, hc, hq₃, hv₃]
      simp only [vecPtr, vecCap]
      rv_eval []
    · right; rw [hQ] at hp; simp only [heapNext] at hp; rw [hn₃] at hp; exact hp
  have hm01 : (s.getMem nextAddr).toNat ≤ (u₁.getMem nextAddr).toNat := by
    rw [← hn₁]; exact hmono₁
  have hPQ : Apart (u₁.getMem (s.getReg .x10 + 8)) (24 * (u₁.getMem (s.getReg .x10)).toNat)
      (u₂.getMem (s.getReg .x10 + 32)) (24 * (u₂.getMem (s.getReg .x10 + 24)).toNat) := by
    rcases hP₁c with ⟨hp, hc⟩ | hp <;> rcases hQ₂c with ⟨hq, hd⟩ | hq
    · rw [hp, hc, hq, hd]
      refine apart_of_forall fun x hx hy ↦ hok.pushPull x ?_ (Or.inl ?_)
      · simp only [formVecsBuf, vecPtr, vecCap]; exact hx
      · simp only [formVecsBuf, vecPtr, vecCap]; rv_eval []; exact hy
    · rw [hp, hc]; simp only [Apart]; rcases hPold.2 with h0 | h0 <;> omega
    · rw [hq, hd]; simp only [Apart]; rcases hQold.2 with h0 | h0 <;> omega
    · simp only [Apart]; omega
  -- what `t₅` holds where `u₁` did, and where `s` did
  have hU (y : Word) (h1 : Apart y 8 (u₁.getMem (s.getReg .x10 + 8) +
      BitVec.ofNat 64 (24 * (s.getMem (s.getReg .x10 + 16)).toNat)) 24)
      (h2 : Apart y 8 (s.getReg .x10 + 16) 8) (h3 : Apart y 8 (s.getReg .x10 + 24) 24)
      (h4 : Apart y 8 (s.getReg .x2 - 208) 208) (h5 : Apart y 8 nextAddr 8)
      (h6 : y.toNat + 8 ≤ (u₁.getMem nextAddr).toNat ∨ heapEnd ≤ y.toNat)
      (h7 : Apart y 8 (u₂.getMem (s.getReg .x10 + 32) +
        BitVec.ofNat 64 (24 * (s.getMem (s.getReg .x10 + 40)).toNat)) 24)
      (hw : y.toNat + 8 ≤ 2 ^ 64) : t₅.getMem y = u₁.getMem y := by
    rw [hf₅.getMem_of (fun z hz hzw ↦ by
        rcases hzw with hzw | hzw
        · addr_omega [hz, hzw, h7, hselfb]
        · addr_omega [hz, hzw, h3, hselfb]) hw,
      hroom₂.frame.getMem_of (fun z hz hzw ↦ by
        rw [hlo₃] at hzw
        rcases hzw with hzw | hzw | hzw | hzw
        · addr_omega [hz, hzw, h3, hselfb]
        · addr_omega [hz, hzw, h4, hsb]
        · addr_omega [hz, hzw, h5]
        · simp only [Fresh, heapNext, heapEnd] at hzw h6
          rw [hn₃] at hzw
          addr_omega [hz, hzw, h6, hhi₂]) hw,
      hmid y h1 h2 hw]
  -- the lengths and buffers in `t₅`
  have hLlt := hroomu₁
  have hMlt := hroomu₂
  have hpL : t₃.getMem (s.getReg .x10 + 16) = s.getMem (s.getReg .x10 + 16) + 1 := by
    have := b80011bd8_m_x8_16 h₃; rw [r₈, r₁₉] at this; exact this
  have hpL₅ : t₅.getMem (s.getReg .x10 + 16) = s.getMem (s.getReg .x10 + 16) + 1 := by
    rw [hf₅.getMem_of (fun z hz hzw ↦ by
        rcases hzw with hzw | hzw
        · addr_omega [hz, hzw, hsep₂, hselfb, hQ₂b, hroomu₂, hnu₂]
        · addr_omega [hz, hzw, hselfb]) (by addr_omega [hselfb]),
      hroom₂.frame.getMem_of (fun z hz hzw ↦ by
        rw [hlo₃] at hzw
        rcases hzw with hzw | hzw | hzw | hzw
        · addr_omega [hz, hzw, hselfb]
        · addr_omega [hz, hzw, hss, hselfb, hsb]
        · have := hsf.2; addr_omega [hz, hzw, this, hselfb]
        · have := hsf.1
          simp only [Fresh, heapNext, heapEnd] at hzw this
          rw [hn₃] at hzw
          rcases this with h0 | h0 <;> addr_omega [hz, hzw, h0, hselfb, hm01, hhi₂])
        (by addr_omega [hselfb]), hpL]
  have hhdr (k : Nat) (hk : k = 0 ∨ k = 8) :
      t₅.getMem (s.getReg .x10 + BitVec.ofNat 64 k) = u₁.getMem (s.getReg .x10 + BitVec.ofNat 64 k) := by
    have := hsf.1
    simp only [heapNext, heapEnd] at this
    exact hU _ (by addr_omega [hsep₁, hselfb, hk, hP₁b, hroomu₁, hnu₁])
      (by addr_omega [hselfb, hk]) (by addr_omega [hselfb, hk]) (by addr_omega [hss, hselfb, hk, hsb])
      (by have := hsf.2; addr_omega [this, hselfb, hk])
      (by rcases this with h0 | h0
          · left; addr_omega [h0, hselfb, hk, hm01]
          · right; addr_omega [h0, hselfb, hk])
      (by addr_omega [hsep₂, hselfb, hk, hQ₂b, hroomu₂, hnu₂]) (by addr_omega [hselfb, hk])
  have hP₅ : vecPtr t₅ (s.getReg .x10) = u₁.getMem (s.getReg .x10 + 8) := hhdr 8 (Or.inr rfl)
  have hC₅ : vecCap t₅ (s.getReg .x10) = u₁.getMem (s.getReg .x10) := by
    have := hhdr 0 (Or.inl rfl); simpa [vecCap] using this
  have hpM₅ : t₅.getMem (s.getReg .x10 + 40) = s.getMem (s.getReg .x10 + 40) + 1 := by
    have := b80011c24_m_x8_40 h₅; rw [q₈, q₂₀] at this; exact this
  have hQ₅ : t₅.getMem (s.getReg .x10 + 32) = u₂.getMem (s.getReg .x10 + 32) :=
    hf₅.getMem_of (fun z hz hzw ↦ by
      rcases hzw with hzw | hzw
      · addr_omega [hz, hzw, hsep₂, hselfb, hQ₂b, hroomu₂, hnu₂]
      · addr_omega [hz, hzw, hselfb]) (by addr_omega [hselfb])
  have hD₅ : t₅.getMem (s.getReg .x10 + 24) = u₂.getMem (s.getReg .x10 + 24) :=
    hf₅.getMem_of (fun z hz hzw ↦ by
      rcases hzw with hzw | hzw
      · addr_omega [hz, hzw, hsep₂, hselfb, hQ₂b, hroomu₂, hnu₂]
      · addr_omega [hz, hzw, hselfb]) (by addr_omega [hselfb])
  -- the global frame
  have hm3 : (s.getMem nextAddr).toNat ≤ (u₂.getMem nextAddr).toNat := by
    have := hroom₂.mono; simp only [heapNext] at this; rw [hn₃] at this; omega
  have hW : DFrame s t₅ fun y ↦ Within y (s.getReg .x10) 48 ∨ Within y (s.getReg .x2 - 208) 208 ∨
      Within y nextAddr 8 ∨ Fresh s t₅ y ∨
      Within y (u₁.getMem (s.getReg .x10 + 8) +
        BitVec.ofNat 64 (24 * (s.getMem (s.getReg .x10 + 16)).toNat)) 24 ∨
      Within y (u₂.getMem (s.getReg .x10 + 32) +
        BitVec.ofNat 64 (24 * (s.getMem (s.getReg .x10 + 40)).toNat)) 24 :=
    (((hfu₁.union hf₃).union hroom₂.frame).union hf₅).mono fun y hy ↦ by
      have hf5 : (heapNext t₅) = (u₂.getMem nextAddr).toNat := by rw [hnext₅]; rfl
      rcases hy with (((hy | hy | hy | hy) | hy | hy) | hy | hy | hy | hy) | hy | hy
      · exact Or.inl (by addr_omega [hy, hselfb])
      · exact Or.inr (Or.inl (by addr_omega [hy, hsb]))
      · exact Or.inr (Or.inr (Or.inl hy))
      · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
        simp only [Fresh, heapNext] at hy ⊢; rw [hn₅]
        have := hroom₂.mono; simp only [heapNext] at this; rw [hn₃] at this; omega
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hy))))
      · exact Or.inl (by addr_omega [hy, hselfb])
      · exact Or.inl (by addr_omega [hy, hselfb])
      · rw [hlo₃] at hy; exact Or.inr (Or.inl (by addr_omega [hy, hsb]))
      · exact Or.inr (Or.inr (Or.inl hy))
      · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
        simp only [Fresh, heapNext] at hy ⊢; rw [hn₃] at hy; rw [hn₅]; omega
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hy))))
      · exact Or.inl (by addr_omega [hy, hselfb])
  have hbufQ₅ : ∀ x, formVecsBuf t₅ (s.getReg .x10 + 24) x ↔
      Within x (u₂.getMem (s.getReg .x10 + 32)) (24 * (u₂.getMem (s.getReg .x10 + 24)).toNat) := by
    intro x
    simp only [formVecsBuf, vecPtr, vecCap]
    rw [show s.getReg .x10 + 24 + 8 = s.getReg .x10 + 32 by rv_eval [], hQ₅, hD₅]
  -- an address of the heap below `s`'s `NEXT` in none of `s`'s buffers nor its header is in none of
  -- what the call writes, nor in `t₅`'s buffers
  have hgood (x : Word) (hb : heapStart ≤ x.toNat ∧ x.toNat < heapNext s)
      (hh : ¬ Within x (s.getReg .x10) 48) (hp : ¬ formVecsBuf s (s.getReg .x10) x)
      (hq : ¬ formVecsBuf s (s.getReg .x10 + 24) x) :
      ¬ (Within x (s.getReg .x10) 48 ∨ Within x (s.getReg .x2 - 208) 208 ∨
        Within x nextAddr 8 ∨ Fresh s t₅ x ∨
        Within x (u₁.getMem (s.getReg .x10 + 8) +
          BitVec.ofNat 64 (24 * (s.getMem (s.getReg .x10 + 16)).toNat)) 24 ∨
        Within x (u₂.getMem (s.getReg .x10 + 32) +
          BitVec.ofNat 64 (24 * (s.getMem (s.getReg .x10 + 40)).toNat)) 24) ∧ ¬ formVecsBuf t₅ (s.getReg .x10) x ∧
        ¬ formVecsBuf t₅ (s.getReg .x10 + 24) x := by
    simp only [heapNext, heapStart] at hb
    have inP : ¬ Within x (u₁.getMem (s.getReg .x10 + 8)) (24 * (u₁.getMem (s.getReg .x10)).toNat) := by
      intro hx
      rcases hP₁c with ⟨hp', hc'⟩ | hp'
      · apply hp; simp only [formVecsBuf, vecPtr, vecCap]; rw [← hp', ← hc']; exact hx
      · simp only [Within] at hx; omega
    have inQ : ¬ Within x (u₂.getMem (s.getReg .x10 + 32))
        (24 * (u₂.getMem (s.getReg .x10 + 24)).toNat) := by
      intro hx
      rcases hQ₂c with ⟨hq', hd'⟩ | hq'
      · apply hq; simp only [formVecsBuf, vecPtr, vecCap]
        rw [show s.getReg .x10 + 24 + 8 = s.getReg .x10 + 32 by rv_eval [], ← hq', ← hd']; exact hx
      · simp only [Within] at hx; omega
    refine ⟨fun hx ↦ ?_, fun hx ↦ inP (by simpa only [formVecsBuf, hP₅, hC₅] using hx),
      fun hx ↦ inQ ((hbufQ₅ x).mp hx)⟩
    have hhs := hheap.hi
    simp only [heapNext, heapEnd] at hhs
    rcases hx with hx | hx | hx | hx | hx | hx
    · exact hh hx
    · addr_omega [hx, hb, hab, hsb, hhs]
    · addr_omega [hx, hb, hhs]
    · simp only [Fresh, heapNext] at hx; omega
    · exact inP (by addr_omega [hx, hLlt, hP₁b, hnu₁])
    · exact inQ (by addr_omega [hx, hMlt, hQ₂b, hnu₂])
  have hga : Apart (s.getReg .x11) 24 (s.getReg .x10) 48 :=
    apart_of_forall fun x hx hy ↦ hapart x (Or.inl hx) (Or.inl hy)
  have hha : Apart (s.getReg .x12) 24 (s.getReg .x10) 48 :=
    apart_of_forall fun x hx hy ↦ hapart x (Or.inr (Or.inr (Or.inl hx))) (Or.inl hy)
  have hQa : Apart (s.getReg .x10) 48 (s.getMem (s.getReg .x10 + 32))
      (24 * (s.getMem (s.getReg .x10 + 24)).toNat) := by
    refine apart_of_forall fun x hx hy ↦ hok.header x hx (Or.inr (Or.inl ?_))
    simp only [formVecsBuf, vecPtr, vecCap]; rv_eval []; exact hy
  have hPQold : Apart (u₁.getMem (s.getReg .x10 + 8)) (24 * (u₁.getMem (s.getReg .x10)).toNat)
      (s.getMem (s.getReg .x10 + 32)) (24 * (s.getMem (s.getReg .x10 + 24)).toNat) := by
    rcases hP₁c with ⟨hp, hc⟩ | hp
    · rw [hp, hc]
      refine apart_of_forall fun x hx hy ↦ hok.pushPull x ?_ (Or.inl ?_)
      · simp only [formVecsBuf, vecPtr, vecCap]; exact hx
      · simp only [formVecsBuf, vecPtr, vecCap]; rv_eval []; exact hy
    · simp only [Apart]; rcases hQold.2 with h0 | h0 <;> omega
  have hP₁h : Apart (s.getReg .x12) 24 (u₁.getMem (s.getReg .x10 + 8))
      (24 * (u₁.getMem (s.getReg .x10)).toNat) := by
    rcases hP₁c with ⟨hp, hc⟩ | hp
    · rw [hp, hc]
      refine apart_of_forall fun x hx hy ↦ hapart x (Or.inr (Or.inr (Or.inl hx))) (Or.inr (Or.inl ?_))
      simp only [formVecsBuf, vecPtr, vecCap]; exact hy
    · have := hhf.1
      simp only [heapNext, heapEnd] at this
      simp only [Apart]
      rcases this with h0 | h0 <;> omega
  have hhs' := hheap.hi
  simp only [heapNext, heapEnd] at hhs'
  -- `push`
  have hLn : (s.getMem (s.getReg .x10 + 16) + 1).toNat = (s.getMem (s.getReg .x10 + 16)).toNat + 1 := by
    rw [BitVec.toNat_add, show (1 : Word).toNat = 1 from rfl]; omega
  have hPush := formVecsOf_push hW (v := s.getReg .x10) (g := s.getReg .x11) hok.push hpre.pushOk
    (by simp only [vecLen]; rw [hpL₅, hLn])
    (by rw [hC₅]; simp only [vecLen]; omega)
    (by simp only [RawVecOk, Buf, hP₅, hC₅, heapNext, hn₅]
        exact ⟨hP₁al, Or.inr ⟨hP₁b.1, by omega⟩⟩)
    (by
      intro i hi k hk
      simp only [vecLen] at hi
      have hj : 24 * i + 8 * k + 8 ≤ 24 * (vecLen t₁ (s.getReg .x10)).toNat := by
        rw [hlen₁]; simp only [vecLen]; omega
      rw [hP₅, hU _ (by addr_omega [hi, hk, hLlt, hP₁b, hnu₁])
          (by addr_omega [hsep₁, hi, hk, hLlt, hP₁b, hnu₁, hselfb])
          (by addr_omega [hsep₁, hi, hk, hLlt, hP₁b, hnu₁, hselfb])
          (by addr_omega [hi, hk, hLlt, hP₁b, hnu₁, hab, hsb])
          (by addr_omega [hi, hk, hLlt, hP₁b, hnu₁])
          (Or.inl (by addr_omega [hi, hk, hLlt, hP₁b, hnu₁]))
          (by addr_omega [hPQ, hi, hk, hLlt, hP₁b, hnu₁, hMlt, hQ₂b, hnu₂])
          (by addr_omega [hi, hk, hLlt, hP₁b, hnu₁]),
        BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.add_assoc, ← BitVec.ofNat_add]
      have hc := hroom₁.copy (24 * i + 8 * k) (by omega) (by omega)
      simp only [vecPtr] at hc
      rw [hc]
      have hi' : i < (s.getMem (s.getReg .x10)).toNat := by omega
      have hp' : t₁.getMem (s.getReg .x10 + 8) = s.getMem (s.getReg .x10 + 8) := hptr₁
      rw [hp']
      exact hs₁ _ (by rcases hPold.2 with h0 | h0
                      · omega
                      · addr_omega [h0, hi', hk, hab, hsb, hhs'])
        (by rcases hPold.2 with h0 | h0
            · omega
            · addr_omega [h0, hi', hk, hhs']))
    (by
      intro k hk
      simp only [vecLen]
      rw [hP₅]
      have hT : t₅.getMem (u₁.getMem (s.getReg .x10 + 8) +
          BitVec.ofNat 64 (24 * (s.getMem (s.getReg .x10 + 16)).toNat) + BitVec.ofNat 64 (8 * k)) =
          t₃.getMem (u₁.getMem (s.getReg .x10 + 8) +
          BitVec.ofNat 64 (24 * (s.getMem (s.getReg .x10 + 16)).toNat) + BitVec.ofNat 64 (8 * k)) := by
        rw [hf₅.getMem_of (fun z hz hzw ↦ by
            rcases hzw with hzw | hzw
            · addr_omega [hz, hzw, hPQ, hk, hLlt, hP₁b, hnu₁, hMlt, hQ₂b, hnu₂]
            · addr_omega [hz, hzw, hsep₁, hk, hLlt, hP₁b, hnu₁, hselfb])
            (by addr_omega [hk, hLlt, hP₁b, hnu₁]),
          hroom₂.frame.getMem_of (fun z hz hzw ↦ by
            rw [hlo₃] at hzw
            rcases hzw with hzw | hzw | hzw | hzw
            · addr_omega [hz, hzw, hsep₁, hk, hLlt, hP₁b, hnu₁, hselfb]
            · addr_omega [hz, hzw, hk, hLlt, hP₁b, hnu₁, hab, hsb]
            · addr_omega [hz, hzw, hk, hLlt, hP₁b, hnu₁]
            · simp only [Fresh, heapNext] at hzw
              rw [hn₃] at hzw
              addr_omega [hz, hzw, hk, hLlt, hP₁b, hnu₁]) (by addr_omega [hk, hLlt, hP₁b, hnu₁])]
      have hg (j : Word) (hj : j.toNat < 24) (hj8 : j.toNat % 8 = 0) :
          u₁.getMem (s.getReg .x11 + j) = s.getMem (s.getReg .x11 + j) := by
        have := hgf.1
        simp only [heapNext, heapEnd] at this
        exact hku₁ _ ⟨by addr_omega [hga, hgb, hj, hj8], by addr_omega [hga, hgb, hj, hj8]⟩
          (by addr_omega [hgs, hgb, hj, hj8, hsb]) (by have := hgf.2; addr_omega [this, hgb, hj, hj8])
          (by rcases this with h0 | h0
              · left; simp only [heapNext]; addr_omega [h0, hgb, hj, hj8]
              · right; simp only [heapEnd]; addr_omega [h0, hgb, hj, hj8])
          (by addr_omega [hgb, hj, hj8])
      have m3 := b80011bd8_m3 h₃
      have m2 := b80011bd8_m2 h₃
      have m1 := b80011bd8_m1 h₃
      rw [r₈, r₁₈, r₁₉, slot_eq] at m3 m2 m1
      rw [hT]
      obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by omega
      · simpa using m3.trans (by simpa using hg 0 (by decide) (by decide))
      · exact m2.trans (hg 8 (by decide) (by decide))
      · exact m1.trans (hg 16 (by decide) (by decide)))
    (fun i hi x hx ↦ by
      have hb := (hok.push.elems i hi).deep_below hx
      have := hgood x hb (fun h ↦ hok.header x h (Or.inl (Or.inr ⟨i, hi, hx⟩)))
        (hok.push.sep i hi x hx) (fun h ↦ hok.pullPush x h (Or.inr ⟨i, hi, hx⟩))
      exact ⟨this.1, this.2.1⟩)
    (fun x hx ↦ by
      have hb := hpre.pushOk.deep_below hx
      have ha := hapart x (Or.inr (Or.inl hx))
      simp only [flushesBuf, not_or] at ha
      have := hgood x hb ha.1 ha.2.1 ha.2.2
      exact ⟨this.1, this.2.1⟩)
    hheap (by rw [hnext₅]; exact hm3)
  -- `pull`
  have hMn : (s.getMem (s.getReg .x10 + 40) + 1).toNat = (s.getMem (s.getReg .x10 + 40)).toNat + 1 := by
    rw [BitVec.toNat_add, show (1 : Word).toNat = 1 from rfl]; omega
  have hl40 : vecLen t₅ (s.getReg .x10 + 24) = t₅.getMem (s.getReg .x10 + 40) := by
    simp only [vecLen]; rv_eval []
  have hp32 : vecPtr t₅ (s.getReg .x10 + 24) = u₂.getMem (s.getReg .x10 + 32) := by
    simp only [vecPtr]; rw [show s.getReg .x10 + 24 + 8 = s.getReg .x10 + 32 by rv_eval [], hQ₅]
  have hc24 : vecCap t₅ (s.getReg .x10 + 24) = u₂.getMem (s.getReg .x10 + 24) := hD₅
  have hQs : vecPtr s (s.getReg .x10 + 24) = s.getMem (s.getReg .x10 + 32) := by
    simp only [vecPtr]; rv_eval []
  have hPull := formVecsOf_push hW (v := s.getReg .x10 + 24) (g := s.getReg .x12) hok.pull
    hpre.pullOk (by rw [hl40, hpM₅, hM, hMn]) (by rw [hc24, hM]; omega)
    (by simp only [RawVecOk, Buf, hp32, hc24, heapNext, hn₅]
        exact ⟨hQ₂al, Or.inr ⟨hQ₂b.1, by omega⟩⟩)
    (by
      intro i hi k hk
      rw [hM] at hi
      have hiD : i < (s.getMem (s.getReg .x10 + 24)).toNat := by omega
      rw [hp32, hf₅.getMem_of (fun z hz hzw ↦ by
          rcases hzw with hzw | hzw
          · addr_omega [hz, hzw, hi, hk, hMlt, hQ₂b, hnu₂]
          · addr_omega [hz, hzw, hsep₂, hi, hk, hMlt, hQ₂b, hnu₂, hselfb])
          (by addr_omega [hi, hk, hMlt, hQ₂b, hnu₂]),
        BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.add_assoc, ← BitVec.ofNat_add, ← hQ]
      have hc := hroom₂.copy (24 * i + 8 * k) (by omega) (by rw [hl₃, hM]; omega)
      rw [hc, hq₃, hQs]
      rw [hmid _ (by addr_omega [hPQold, hiD, hk, hLlt, hP₁b, hnu₁, hQold, hhs'])
          (by addr_omega [hQa, hiD, hk, hselfb, hQold, hhs'])
          (by addr_omega [hiD, hk, hQold, hhs'])]
      exact hku₁ _ ⟨by addr_omega [hQa, hiD, hk, hselfb, hQold, hhs'],
          by addr_omega [hQa, hiD, hk, hselfb, hQold, hhs']⟩
        (by addr_omega [hiD, hk, hQold, hhs', hab, hsb])
        (by addr_omega [hiD, hk, hQold, hhs'])
        (Or.inl (by simp only [heapNext]; rcases hQold.2 with h0 | h0
                    · omega
                    · addr_omega [h0, hiD, hk]))
        (by addr_omega [hiD, hk, hQold, hhs']))
    (by
      intro k hk
      rw [hp32, hM]
      have hh (j : Word) (hj : j.toNat < 24) (hj8 : j.toNat % 8 = 0) :
          u₂.getMem (s.getReg .x12 + j) = s.getMem (s.getReg .x12 + j) := by
        have := hhf.1
        simp only [heapNext, heapEnd] at this
        rw [hroom₂.frame.getMem_of (fun z hz hzw ↦ by
            rw [hlo₃] at hzw
            rcases hzw with hzw | hzw | hzw | hzw
            · addr_omega [hz, hzw, hha, hhb, hj, hj8, hselfb]
            · addr_omega [hz, hzw, hhs, hhb, hj, hj8, hsb]
            · have := hhf.2; addr_omega [hz, hzw, this, hhb, hj, hj8]
            · simp only [Fresh, heapNext] at hzw
              rw [hn₃] at hzw
              rcases this with h0 | h0 <;> addr_omega [hz, hzw, h0, hhb, hj, hj8, hm01, hhi₂])
            (by addr_omega [hhb, hj, hj8]),
          hmid _ (by addr_omega [hP₁h, hhb, hj, hj8, hLlt, hP₁b, hnu₁])
            (by addr_omega [hha, hhb, hj, hj8, hselfb]) (by addr_omega [hhb, hj, hj8])]
        exact hku₁ _ ⟨by addr_omega [hha, hhb, hj, hj8], by addr_omega [hha, hhb, hj, hj8]⟩
          (by addr_omega [hhs, hhb, hj, hj8, hsb]) (by have := hhf.2; addr_omega [this, hhb, hj, hj8])
          (by rcases this with h0 | h0
              · left; simp only [heapNext]; addr_omega [h0, hhb, hj, hj8]
              · right; simp only [heapEnd]; addr_omega [h0, hhb, hj, hj8])
          (by addr_omega [hhb, hj, hj8])
      have m3 := b80011c24_m3 h₅
      have m2 := b80011c24_m2 h₅
      have m1 := b80011c24_m1 h₅
      rw [q₈, q₉, q₂₀, slot_eq] at m3 m2 m1
      obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by omega
      · simpa using m3.trans (by simpa using hh 0 (by decide) (by decide))
      · exact m2.trans (hh 8 (by decide) (by decide))
      · exact m1.trans (hh 16 (by decide) (by decide)))
    (fun i hi x hx ↦ by
      have hb := (hok.pull.elems i hi).deep_below hx
      have := hgood x hb (fun h ↦ hok.header x h (Or.inr (Or.inr ⟨i, hi, hx⟩)))
        (fun h ↦ hok.pushPull x h (Or.inr ⟨i, hi, hx⟩)) (hok.pull.sep i hi x hx)
      exact ⟨this.1, this.2.2⟩)
    (fun x hx ↦ by
      have hb := hpre.pullOk.deep_below hx
      have ha := hapart x (Or.inr (Or.inr (Or.inr hx)))
      simp only [flushesBuf, not_or] at ha
      have := hgood x hb ha.1 ha.2.1 ha.2.2
      exact ⟨this.1, this.2.2⟩)
    hheap (by rw [hnext₅]; exact hm3)
  -- each new buffer is the old one or fresh
  have hm5 : (u₁.getMem nextAddr).toNat ≤ (t₅.getMem nextAddr).toNat := by
    rw [hn₅, ← hn₃]; exact hmono₂
  have regP (x : Word) (hx : formVecsBuf t₅ (s.getReg .x10) x) :
      formVecsBuf s (s.getReg .x10) x ∨ Fresh s t₅ x := by
    simp only [formVecsBuf, hP₅, hC₅] at hx
    rcases hP₁c with ⟨hp, hc⟩ | hp
    · left; simp only [formVecsBuf, vecPtr, vecCap]; rw [← hp, ← hc]; exact hx
    · right; simp only [Fresh, heapNext]; simp only [Within] at hx; omega
  have regQ (x : Word) (hx : formVecsBuf t₅ (s.getReg .x10 + 24) x) :
      formVecsBuf s (s.getReg .x10 + 24) x ∨ Fresh s t₅ x := by
    rw [hbufQ₅] at hx
    rcases hQ₂c with ⟨hq, hd⟩ | hq
    · left; simp only [formVecsBuf, vecPtr, vecCap]
      rw [show s.getReg .x10 + 24 + 8 = s.getReg .x10 + 32 by rv_eval [], ← hq, ← hd]; exact hx
    · right; simp only [Fresh, heapNext]; simp only [Within] at hx; rw [hn₅]; omega
  have frP (x : Word) (hx : Fresh s t₅ x) : ¬ (formVecsDeep s (s.getReg .x10) x ∨
      formVecsDeep s (s.getReg .x10 + 24) x ∨ formVecDeep s (s.getReg .x11) x ∨
      formVecDeep s (s.getReg .x12) x) := by
    simp only [Fresh] at hx
    rintro (h' | h' | h' | h')
    · have := formVecsDeep_below hok.push h'; omega
    · have := formVecsDeep_below hok.pull h'; omega
    · have := hpre.pushOk.deep_below h'; omega
    · have := hpre.pullOk.deep_below h'; omega
  have hbP (x : Word) (hx : formVecsBuf t₅ (s.getReg .x10) x) : ¬ Within x (s.getReg .x10) 48 := by
    simp only [formVecsBuf, hP₅, hC₅] at hx
    intro h'; addr_omega [hx, h', hsep₁]
  have hbQ (x : Word) (hx : formVecsBuf t₅ (s.getReg .x10 + 24) x) :
      ¬ Within x (s.getReg .x10) 48 := by
    rw [hbufQ₅] at hx
    intro h'; addr_omega [hx, h', hsep₂]
  refine ⟨⟨hnext₅ ▸ hroom₂.heap.lo, hnext₅ ▸ hroom₂.heap.hi⟩, by rw [hnext₅]; exact hm3, ?_,
    ⟨hPush.2.1, hPull.2.1, ?_, ?_, ?_⟩, ?_, ?_⟩
  · simp only [flushesOf, FlushesRust.pair, hPush.1, hPull.1]
  · intro x hx hd
    rcases hPull.2.2 x hd with hb | hb | hb
    · simp only [formVecsBuf, hP₅, hC₅] at hx
      rw [hbufQ₅] at hb
      addr_omega [hx, hb, hPQ]
    · rcases regP x hx with h' | h'
      · exact hok.pushPull x h' hb
      · exact frP x h' (Or.inr (Or.inl hb))
    · rcases regP x hx with h' | h'
      · exact hapart x (Or.inr (Or.inr (Or.inr hb))) (Or.inr (Or.inl h'))
      · exact frP x h' (Or.inr (Or.inr (Or.inr hb)))
  · intro x hx hd
    rcases hPush.2.2 x hd with hb | hb | hb
    · simp only [formVecsBuf, hP₅, hC₅] at hb
      rw [hbufQ₅] at hx
      addr_omega [hx, hb, hPQ]
    · rcases regQ x hx with h' | h'
      · exact hok.pullPush x h' hb
      · exact frP x h' (Or.inl hb)
    · rcases regQ x hx with h' | h'
      · exact hapart x (Or.inr (Or.inl hb)) (Or.inr (Or.inr h'))
      · exact frP x h' (Or.inr (Or.inr (Or.inl hb)))
  · intro x hx hd
    rcases hd with hd | hd
    · rcases hPush.2.2 x hd with hb | hb | hb
      · exact hbP x hb hx
      · exact hok.header x hx (Or.inl hb)
      · exact hapart x (Or.inr (Or.inl hb)) (Or.inl hx)
    · rcases hPull.2.2 x hd with hb | hb | hb
      · exact hbQ x hb hx
      · exact hok.header x hx (Or.inr hb)
      · exact hapart x (Or.inr (Or.inr (Or.inr hb))) (Or.inl hx)
  · intro x hd
    rcases hd with hd | hd
    · rcases hPush.2.2 x hd with hb | hb | hb
      · rcases regP x hb with h' | h'
        · exact Or.inl (Or.inl (Or.inl h'))
        · exact Or.inr (Or.inr (Or.inr h'))
      · exact Or.inl (Or.inl hb)
      · exact Or.inr (Or.inl hb)
    · rcases hPull.2.2 x hd with hb | hb | hb
      · rcases regQ x hb with h' | h'
        · exact Or.inl (Or.inr (Or.inl h'))
        · exact Or.inr (Or.inr (Or.inr h'))
      · exact Or.inl (Or.inr hb)
      · exact Or.inr (Or.inr (Or.inl hb))
  · refine hW.mono fun y hy ↦ ?_
    rcases hy with hy | hy | hy | hy | hy | hy
    · exact Or.inl hy
    · exact Or.inr (Or.inr (Or.inl (by
        simp only [stackLo, pairStack, growOneStack, Nat.reduceAdd]; addr_omega [hy, hsb])))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hy)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr hy)))
    · rcases regP y (by simp only [formVecsBuf, hP₅, hC₅]; addr_omega [hy, hLlt, hP₁b, hnu₁])
        with h' | h'
      · exact Or.inr (Or.inl (Or.inl h'))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h')))
    · rcases regQ y (by rw [hbufQ₅]; addr_omega [hy, hMlt, hQ₂b, hnu₂]) with h' | h'
      · exact Or.inr (Or.inl (Or.inr h'))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h')))

end Rv64Verifier.Layout.Pair
