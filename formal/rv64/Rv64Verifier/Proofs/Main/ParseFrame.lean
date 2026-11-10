import Rv64Verifier.Proofs.Main.ParseBase
import Rv64Verifier.Proofs.Main.Return

/-!
# What `ParseRest` keeps

`Wf B`: what `ParseRest` writes, `main`'s scratch slots, its callees' stacks, `NEXT` and the heap
from `B` on. `PG u₀ t`: from `ParseA`'s `u₀` to `t`, memory changed only there (`B = NEXT` at
`u₀`); then `main`'s frame, its input, the `Bytecode` and the public input are as at `u₀`
(`PG.minv`, `PG.bc`, `PG.bufs`, `PG.pi`).

`PathIn` and `PhaseIn`: a `MerklePath` or a `Vec<MerklePath>` holding a given value, its buffers in
`[lo, hi)`; writes that miss its header and `[lo, hi)` keep it (`PathIn.frame`, `PhaseIn.frame`).
-/

namespace Rv64Verifier.Proofs.Main
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile Rv64Verifier.Runtime
  Rv64Verifier.Proofs.Bytecode Rv64Verifier.Proofs.End

/-! ## Frames of bytes -/

/-- `t`'s bytes outside `w` are `s`'s. -/
def BFrame (s t : MachineState) (w : Word → Prop) : Prop := ∀ a, ¬ w a → byteAt t a = byteAt s a

section
variable {s t u : MachineState} {w w' : Word → Prop}

theorem BFrame.refl (s : MachineState) (w : Word → Prop) : BFrame s s w := fun _ _ ↦ rfl

theorem BFrame.mono (h : BFrame s t w) (hw : ∀ a, w a → w' a) : BFrame s t w' :=
  fun a ha ↦ h a fun h' ↦ ha (hw a h')

theorem BFrame.trans (h₁ : BFrame s t w) (h₂ : BFrame t u w') (hw : ∀ a, w' a → w a) :
    BFrame s u w :=
  fun a ha ↦ (h₂ a fun h' ↦ ha (hw a h')).trans (h₁ a ha)

theorem BFrame.of_same (hm : ∀ a, t.getMem a = s.getMem a) (w : Word → Prop) : BFrame s t w :=
  fun a _ ↦ by rw [byteAt_eq, byteAt_eq, hm]

theorem BFrame.getMem (h : BFrame s t w) {a : Word} (h8 : a.toNat % 8 = 0)
    (ha : ∀ i < 8, ¬ w (a + BitVec.ofNat 64 i)) : t.getMem a = s.getMem a :=
  getMem_eq_of_bytes h8 h8 fun i hi ↦ h _ (ha i hi)

theorem BFrame.bytesAt (h : BFrame s t w) {p : Word} {n : Nat}
    (hp : ∀ i < n, ¬ w (p + BitVec.ofNat 64 i)) : bytesAt t p n = bytesAt s p n :=
  bytesAt_eq_iff.mpr fun i hi ↦ h _ (hp i hi)

/-- A frame of doublewords whose range holds every byte of each doubleword it touches. -/
theorem BFrame.of_dwords (h : ∀ a, ¬ w a → t.getMem a = s.getMem a)
    (hw : ∀ a, w (a &&& ~~~7#64) → w a) : BFrame s t w :=
  fun a ha ↦ by rw [byteAt_eq, byteAt_eq, h _ fun h' ↦ ha (hw a h')]

theorem BFrame.of_memFrame {lo : Word} {n : Nat} (h : MemFrame s t lo n) (hlo : lo.toNat % 8 = 0)
    (hn : n % 8 = 0) : BFrame s t (Within · lo n) :=
  BFrame.of_dwords h fun _ ha ↦ within_of_alignDown hlo hn ha

end

/-! ## What `ParseRest` writes -/

/-- `main`'s scratch slots, its callees' stacks, `NEXT` and the heap from `B` on. -/
def Wf (B : Nat) (a : Word) : Prop :=
  Within a (msp + 24) 80 ∨ Within a (msp + 272) 80 ∨ Within a (msp - 4096) 4096 ∨
    Within a nextAddr 8 ∨ (B ≤ a.toNat ∧ a.toNat < heapEnd)

theorem Wf.mono {B B' : Nat} (h : B ≤ B') {a : Word} (ha : Wf B' a) : Wf B a := by
  rcases ha with ha | ha | ha | ha | ha
  · exact Or.inl ha
  · exact Or.inr (Or.inl ha)
  · exact Or.inr (Or.inr (Or.inl ha))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨le_trans h ha.1, ha.2⟩)))

theorem Wf.heap {B : Nat} {a : Word} (h1 : B ≤ a.toNat) (h2 : a.toNat < heapEnd) : Wf B a :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, h2⟩)))

theorem Wf.slot {B : Nat} {a : Word} (h : Within a (msp + 24) 80) : Wf B a := Or.inl h

theorem Wf.out {B : Nat} {a : Word} (h : Within a (msp + 272) 80) : Wf B a := Or.inr (Or.inl h)

theorem Wf.stack {B : Nat} {a : Word} (h : Within a (msp - 4096) 4096) : Wf B a :=
  Or.inr (Or.inr (Or.inl h))

theorem Wf.next {B : Nat} {a : Word} (h : Within a nextAddr 8) : Wf B a :=
  Or.inr (Or.inr (Or.inr (Or.inl h)))

/-- What a call of `try_allocate_in` from `main` writes. -/
theorem Wf.tryAlloc {t v : MachineState} (hsp : t.getReg .x2 = msp) (hv : HeapOk v) {a : Word}
    (h : Within a (msp + 320) 24 ∨ Within a (stackLo t tryAllocStack) tryAllocStack ∨
      Within a nextAddr 8 ∨ Fresh t v a) : Wf (heapNext t) a := by
  have := hv.hi
  rcases h with h | h | h | h
  · exact Wf.out (by addr_omega [h])
  · simp only [stackLo, hsp, tryAllocStack] at h; exact Wf.stack (by addr_omega [h])
  · exact Wf.next h
  · have h2 := h.2
    exact Wf.heap h.1 (by simp only [heapEnd] at this ⊢; omega)

/-- From `u₀` on: `sp` is `msp`, the heap in shape and grown, memory changed only in `Wf`;
`NEXT` where `u₀` left it, or 8-aligned. -/
structure PG (u₀ t : MachineState) : Prop where
  sp : t.getReg .x2 = msp
  heap : HeapOk t
  mono : heapNext u₀ ≤ heapNext t
  frame : BFrame u₀ t (Wf (heapNext u₀))
  al : heapNext t = heapNext u₀ ∨ heapNext t % 8 = 0

theorem PG.step {u₀ t t' : MachineState} {W : Word → Prop} (h : PG u₀ t) (hf : BFrame t t' W)
    (hW : ∀ a, W a → Wf (heapNext u₀) a) (hsp : t'.getReg .x2 = msp) (hheap : HeapOk t')
    (hmono : heapNext t ≤ heapNext t') (hal : heapNext t' = heapNext t ∨ heapNext t' % 8 = 0) :
    PG u₀ t' :=
  ⟨hsp, hheap, le_trans h.mono hmono, h.frame.trans hf hW,
    hal.elim (fun e ↦ e ▸ h.al) Or.inr⟩

/-- A step that changes no memory. -/
theorem PG.same {u₀ t t' : MachineState} (h : PG u₀ t) (hm : ∀ a, t'.getMem a = t.getMem a)
    (hsp : t'.getReg .x2 = msp) : PG u₀ t' := by
  have hn : heapNext t' = heapNext t := by simp only [heapNext, hm]
  exact h.step (BFrame.of_same hm (fun _ ↦ False)) (fun _ h ↦ h.elim) hsp
    ⟨by rw [hn]; exact h.heap.lo, by rw [hn]; exact h.heap.hi⟩ (le_of_eq hn.symm) (Or.inl hn)

theorem not_kept_wf {words : List Word} (hf : words.length ≤ inputWords) {B : Nat}
    (hB : heapStart ≤ B) {a : Word} (h : Wf B a) : ¬ Kept words a := by
  intro hk
  simp only [Kept, inputBase_eq] at hk
  simp only [inputWords] at hf
  simp only [heapStart] at hB
  rcases h with h | h | h | h | h <;> rcases hk with hk | hk | hk <;>
    addr_omega [h, hk, hf, hB]

section
variable {s u₀ t : MachineState} {words : List Word}

theorem PG.minv (h0 : ParseA s words u₀) (h : PG u₀ t) : MInv s words t where
  fits := h0.inv.fits
  sp := h.sp
  slots := by
    intro p hp
    rw [← h0.inv.slots p hp]
    obtain ⟨h1, h2, h8⟩ := slot_bounds hp
    exact h.frame.getMem (by addr_omega [h1, h2, h8]) fun i hi hw ↦
      not_kept_wf h0.inv.fits h0.inv.heap.lo hw (Or.inl (by addr_omega [h1, h2, hi]))
  input := by
    intro i hi
    rw [← h0.inv.input i hi]
    have hf := h0.inv.fits
    simp only [inputWords] at hf
    have hib : inputBase.toNat = 0x10000000 := rfl
    exact h.frame.getMem (by addr_omega [hib, hi, hf]) fun j hj hw ↦
      not_kept_wf h0.inv.fits h0.inv.heap.lo hw (Or.inr (Or.inl (by addr_omega [hi, hj, hf, hib])))
  heap := h.heap
  rodata := by
    intro p hp
    have hw' := within_of_mem_rodataWords hp
    have h8 : p.1.toNat % 8 = 0 := by
      simpa using List.all_eq_true.mp rodataWords_aligned' p hp
    rw [h.frame.getMem h8 fun i hi hw ↦ not_kept_wf h0.inv.fits h0.inv.heap.lo hw
      (Or.inr (Or.inr (by addr_omega [hw', h8, hi])))]
    exact h0.inv.rodata p hp

theorem PG.keepB (h0 : ParseA s words u₀) (h : PG u₀ t) {a : Word}
    (ha : (heapStart ≤ a.toNat ∧ a.toNat < heapNext u₀) ∨
      ((msp + 104).toNat ≤ a.toNat ∧ a.toNat < (msp + 272).toNat)) :
    byteAt t a = byteAt u₀ a := by
  have hhi := h0.inv.heap.hi
  simp only [heapStart, heapNext] at ha hhi
  refine h.frame _ fun hw ↦ ?_
  simp only [heapEnd] at hhi
  rcases hw with hw | hw | hw | hw | ⟨hw1, hw2⟩
  · rcases ha with ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩ <;> addr_omega [hw, ha1, ha2, hhi]
  · rcases ha with ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩ <;> addr_omega [hw, ha1, ha2, hhi]
  · rcases ha with ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩ <;> addr_omega [hw, ha1, ha2, hhi]
  · rcases ha with ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩ <;> addr_omega [hw, ha1, ha2, hhi]
  · simp only [heapNext, heapEnd] at hw1 hw2
    rcases ha with ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩ <;> addr_omega [hw1, hw2, ha1, ha2, hhi]

/-- A doubleword below `NEXT` at `u₀`, or of the `Bytecode` and the public input. -/
theorem PG.keep (h0 : ParseA s words u₀) (h : PG u₀ t) {a : Word} (h8 : a.toNat % 8 = 0)
    (ha : (heapStart ≤ a.toNat ∧ a.toNat + 8 ≤ heapNext u₀) ∨
      ((msp + 104).toNat ≤ a.toNat ∧ a.toNat + 8 ≤ (msp + 272).toNat)) :
    t.getMem a = u₀.getMem a := by
  have hhi := h0.inv.heap.hi
  simp only [heapStart, heapNext, heapEnd] at ha hhi
  refine getMem_eq_of_bytes h8 h8 fun i hi ↦ h.keepB h0 ?_
  simp only [heapStart, heapNext]
  rcases ha with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left; constructor <;> addr_omega [h1, h2, hi, hhi]
  · right; constructor <;> addr_omega [h1, h2, hi, hhi]

theorem PG.pi (h0 : ParseA s words u₀) (h : PG u₀ t) :
    bytesAt t (msp + 240) 32 = bytesAt u₀ (msp + 240) 32 :=
  bytesAt_eq_iff.mpr fun i hi ↦ h.keepB h0 (Or.inr (by addr_omega [hi]))

theorem blocksAt_keep {u t : MachineState} {p : Word} {n : Nat} (hp8 : p.toNat % 8 = 0)
    (hk : ∀ a : Word, a.toNat % 8 = 0 → p.toNat ≤ a.toNat → a.toNat + 8 ≤ p.toNat + 24 * n →
      t.getMem a = u.getMem a)
    (hp : p.toNat + 24 * n < 2 ^ 64) : blocksAt t p n = blocksAt u p n := by
  unfold blocksAt
  apply List.map_congr_left
  intro i hi
  simp only [List.mem_range] at hi
  rw [hk _ (by addr_omega [hp, hi, hp8]) (by addr_omega [hp, hi]) (by addr_omega [hp, hi]),
    hk (p + BitVec.ofNat 64 (24 * i) + 8) (by addr_omega [hp, hi, hp8]) (by addr_omega [hp, hi])
      (by addr_omega [hp, hi]),
    hk (p + BitVec.ofNat 64 (24 * i) + 16) (by addr_omega [hp, hi, hp8]) (by addr_omega [hp, hi])
      (by addr_omega [hp, hi])]

theorem wordsAt_keep {u t : MachineState} {p : Word} {n : Nat} (hp8 : p.toNat % 8 = 0)
    (hk : ∀ a : Word, a.toNat % 8 = 0 → p.toNat ≤ a.toNat → a.toNat + 8 ≤ p.toNat + 16 * n →
      t.getMem a = u.getMem a)
    (hp : p.toNat + 16 * n < 2 ^ 64) : wordsAt t p n = wordsAt u p n := by
  unfold wordsAt
  apply List.map_congr_left
  intro i hi
  simp only [List.mem_range] at hi
  rw [hk _ (by addr_omega [hp, hi, hp8]) (by addr_omega [hp, hi]) (by addr_omega [hp, hi]),
    hk (p + BitVec.ofNat 64 (16 * i) + 8) (by addr_omega [hp, hi, hp8]) (by addr_omega [hp, hi])
      (by addr_omega [hp, hi])]

theorem halvesAt_keep {u t : MachineState} {p : Word} {n : Nat} (hal : p.toNat % 2 = 0)
    (hk : ∀ a : Word, p.toNat ≤ a.toNat → a.toNat < p.toNat + 2 * n → byteAt t a = byteAt u a)
    (hp : p.toNat + 2 * n < 2 ^ 64) : halvesAt t p n = halvesAt u p n := by
  unfold halvesAt
  apply List.map_congr_left
  intro i hi
  simp only [List.mem_range] at hi
  exact getHalfword_eq_of_bytes (by addr_omega [hp, hi, hal])
    (hk _ (by addr_omega [hp, hi]) (by addr_omega [hp, hi]))
    (hk _ (by addr_omega [hp, hi]) (by addr_omega [hp, hi]))

theorem msp_128 : (msp + 104 + 24 : Word) = msp + 128 := by decide
theorem msp_152 : (msp + 104 + 48 : Word) = msp + 152 := by decide
theorem msp_176 : (msp + 104 + 72 : Word) = msp + 176 := by decide

theorem PG.bc (h0 : ParseA s words u₀) (h : PG u₀ t) :
    readBytecode t (msp + 104) = readBytecode u₀ (msp + 104) := by
  have hb := h0.bufs
  have hhi := h0.inv.heap.hi
  have hb₀ := hb.blocks
  have hb₁ := hb.words
  have hb₂ := hb.positions
  have hb₃ := hb.bytes
  simp only [Buf, heapStart, heapNext] at hb₀ hb₁ hb₂ hb₃
  simp only [heapNext, heapEnd] at hhi
  have K : ∀ c : Nat, c % 8 = 0 → 104 ≤ c → c + 8 ≤ 272 →
      t.getMem (msp + BitVec.ofNat 64 c) = u₀.getMem (msp + BitVec.ofNat 64 c) :=
    fun c hc h1 h2 ↦ h.keep h0 (by addr_omega [h1, h2, hc]) (Or.inr (by addr_omega [h1, h2]))
  have hp : ∀ c : Nat, c % 8 = 0 → 104 ≤ c → c + 8 ≤ 272 →
      t.getMem (msp + BitVec.ofNat 64 c) = u₀.getMem (msp + BitVec.ofNat 64 c) := K
  have v0p : vecPtr t (msp + 104) = vecPtr u₀ (msp + 104) := hp 112 (by decide) (by decide) (by decide)
  have v0l : vecLen t (msp + 104) = vecLen u₀ (msp + 104) := hp 120 (by decide) (by decide) (by decide)
  have v1p : vecPtr t (msp + 104 + 24) = vecPtr u₀ (msp + 104 + 24) := hp 136 (by decide) (by decide) (by decide)
  have v1l : vecLen t (msp + 104 + 24) = vecLen u₀ (msp + 104 + 24) := hp 144 (by decide) (by decide) (by decide)
  have v2p : vecPtr t (msp + 104 + 48) = vecPtr u₀ (msp + 104 + 48) := hp 160 (by decide) (by decide) (by decide)
  have v2l : vecLen t (msp + 104 + 48) = vecLen u₀ (msp + 104 + 48) := hp 168 (by decide) (by decide) (by decide)
  have v3p : vecPtr t (msp + 104 + 72) = vecPtr u₀ (msp + 104 + 72) := hp 184 (by decide) (by decide) (by decide)
  have v3l : vecLen t (msp + 104 + 72) = vecLen u₀ (msp + 104 + 72) := hp 192 (by decide) (by decide) (by decide)
  have vlen : t.getMem (msp + 104 + 96) = u₀.getMem (msp + 104 + 96) := hp 200 (by decide) (by decide) (by decide)
  have hiv : bytesAt t (msp + 104 + 104) 32 = bytesAt u₀ (msp + 104 + 104) 32 :=
    bytesAt_eq_iff.mpr fun i hi ↦ h.keepB h0 (Or.inr (by addr_omega [hi]))
  have heap_dw : ∀ (p : Word) (n : Nat), (n = 0 ∨ heapStart ≤ p.toNat ∧ p.toNat + n ≤ heapNext u₀) →
      ∀ a : Word, a.toNat % 8 = 0 → p.toNat ≤ a.toNat → a.toNat + 8 ≤ p.toNat + n →
        t.getMem a = u₀.getMem a := by
    intro p n hpn a h8 h1 h2
    rcases hpn with rfl | hpn
    · omega
    · exact h.keep h0 h8 (Or.inl ⟨by omega, by omega⟩)
  have heap_b : ∀ (p : Word) (n : Nat), (n = 0 ∨ heapStart ≤ p.toNat ∧ p.toNat + n ≤ heapNext u₀) →
      ∀ a : Word, p.toNat ≤ a.toNat → a.toNat < p.toNat + n → byteAt t a = byteAt u₀ a := by
    intro p n hpn a h1 h2
    rcases hpn with rfl | hpn
    · omega
    · exact h.keepB h0 (Or.inl ⟨by omega, by omega⟩)
  have lt0 : ∀ (p : Word) (n : Nat), (n = 0 ∨ heapStart ≤ p.toNat ∧ p.toNat + n ≤ heapNext u₀) →
      n = 0 ∨ p.toNat + n < 2 ^ 64 := by
    intro p n hpn
    rcases hpn with h' | h'
    · exact Or.inl h'
    · right; simp only [heapNext] at h'; omega
  unfold readBytecode
  rw [vlen, hiv, v0p, v0l, v1p, v1l, v2p, v2l, v3p, v3l]
  simp only [msp_128, msp_152, msp_176]
  congr 1
  · rcases lt0 _ _ hb₀.2 with h' | h'
    · rw [Nat.mul_eq_zero.mp h' |>.resolve_left (by decide)]
      rfl
    · exact blocksAt_keep hb₀.1 (heap_dw _ _ hb₀.2) h'
  · rcases lt0 _ _ hb₁.2 with h' | h'
    · rw [Nat.mul_eq_zero.mp h' |>.resolve_left (by decide)]
      rfl
    · exact wordsAt_keep hb₁.1 (heap_dw _ _ hb₁.2) h'
  · rcases lt0 _ _ hb₂.2 with h' | h'
    · rw [Nat.mul_eq_zero.mp h' |>.resolve_left (by decide)]
      rfl
    · exact halvesAt_keep hb₂.1 (heap_b _ _ hb₂.2) h'
  · rcases lt0 _ _ hb₃.2 with h' | h'
    · rw [Nat.mul_eq_zero.mp h' |>.resolve_left (by decide)]
      rfl
    · exact halvesAt_keep hb₃.1 (heap_b _ _ hb₃.2) h'

theorem PG.bufs (h0 : ParseA s words u₀) (h : PG u₀ t) : BcBufs t := by
  have hb := h0.bufs
  have hm := h.mono
  have K : ∀ c : Nat, c % 8 = 0 → 104 ≤ c → c + 8 ≤ 272 →
      t.getMem (msp + BitVec.ofNat 64 c) = u₀.getMem (msp + BitVec.ofNat 64 c) :=
    fun c hc h1 h2 ↦ h.keep h0 (by addr_omega [h1, h2, hc]) (Or.inr (by addr_omega [h1, h2]))
  have p0 : vecPtr t (msp + 104) = vecPtr u₀ (msp + 104) := K 112 (by decide) (by decide) (by decide)
  have l0 : vecLen t (msp + 104) = vecLen u₀ (msp + 104) := K 120 (by decide) (by decide) (by decide)
  have p1 : vecPtr t (msp + 128) = vecPtr u₀ (msp + 128) := K 136 (by decide) (by decide) (by decide)
  have l1 : vecLen t (msp + 128) = vecLen u₀ (msp + 128) := K 144 (by decide) (by decide) (by decide)
  have p2 : vecPtr t (msp + 152) = vecPtr u₀ (msp + 152) := K 160 (by decide) (by decide) (by decide)
  have l2 : vecLen t (msp + 152) = vecLen u₀ (msp + 152) := K 168 (by decide) (by decide) (by decide)
  have p3 : vecPtr t (msp + 176) = vecPtr u₀ (msp + 176) := K 184 (by decide) (by decide) (by decide)
  have l3 : vecLen t (msp + 176) = vecLen u₀ (msp + 176) := K 192 (by decide) (by decide) (by decide)
  have b₀ := hb.blocks
  have b₁ := hb.words
  have b₂ := hb.positions
  have b₃ := hb.bytes
  simp only [Buf] at b₀ b₁ b₂ b₃
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> try simp only [Buf]
  · rw [p0, l0]; exact ⟨b₀.1, b₀.2.imp_right fun h' ↦ ⟨h'.1, le_trans h'.2 hm⟩⟩
  · rw [p1, l1]; exact ⟨b₁.1, b₁.2.imp_right fun h' ↦ ⟨h'.1, le_trans h'.2 hm⟩⟩
  · rw [p2, l2]; exact ⟨b₂.1, b₂.2.imp_right fun h' ↦ ⟨h'.1, le_trans h'.2 hm⟩⟩
  · rw [p3, l3]; exact ⟨b₃.1, b₃.2.imp_right fun h' ↦ ⟨h'.1, le_trans h'.2 hm⟩⟩
  · rw [p0]; exact le_trans hb.blocksLe hm
  · rw [p1]; exact le_trans hb.wordsLe hm
  · rw [p2]; exact le_trans hb.positionsLe hm
  · rw [p3]; exact le_trans hb.bytesLe hm

end

end Rv64Verifier.Proofs.Main
