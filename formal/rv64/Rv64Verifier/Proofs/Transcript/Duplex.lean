import Rv64Verifier.Proofs.Transcript.Sponge
import Rv64Verifier.Proofs.Transcript.Keccak
import Rv64Verifier.Proofs.Transcript.Contracts
import Rv64Verifier.Blocks.F27

/-!
# `Sponge::duplex`

```rust
fn duplex(&mut self) {
    let mut input = self.state;
    input[..16].fill(0);
    for (i, &(value, tag)) in self.pending[..self.n_pending].iter().enumerate() {
        input[4 * i..4 * i + 4].copy_from_slice(&[value.c0, value.c1, value.c2, tag]);
    }
    keccak_f(&mut input);
    self.state = input;
    self.n_pending = 0;
}
```

compiled at `0x80007cd8` (`Blocks/F27.lean`): a 224-byte frame, `input` at its bottom (`sp - 224`
for the entry's `sp`); `memcpy` of the state into it, `memset` of its first 128 bytes; a trap if
`n_pending ≥ 5`; then one block per waiting scalar, each copying its four doublewords (`0x80007d28`,
`0x80007d50`, `0x80007d78`, `0x80007da0`), leaving the chain after `n_pending` of them; `keccak_f`;
`memcpy` back; `n_pending = 0`; return.

The proof follows the blocks; between the `memset` and `keccak_f`, `Mid s u k` says the buffer
holds the first `k` scalars' doublewords, zeros up to lane `16`, and the capacity
(`stateAt_eq_duplexInput`), and every write so far lies in the stack (`frame`).
-/

namespace Rv64Verifier.Transcript.Duplex
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F27
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- The callee-saved registers the function never touches. -/
def keptRegs : List Reg := [.x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27]

theorem mem_keptRegs {r : Reg} (h : r ∈ keptRegs) (l : List Reg) (hl : ∀ r ∈ keptRegs, r ∈ l := by decide) :
    r ∈ l :=
  hl r h

/-- `sp` and the stack as numbers. -/
theorem bounds {s : MachineState} (h : DuplexPre s) :
    0xa0000000 + duplexStack ≤ (s.getReg .x2).toNat ∧ (s.getReg .x2).toNat ≤ 0xc0000000 ∧
      (s.getReg .x2).toNat % 16 = 0 ∧
      (stackLo s duplexStack).toNat = (s.getReg .x2).toNat - duplexStack := by
  have hm := h.stack.mapped (by decide) (by decide)
  have hb := h.stack.bounds (by decide) (by decide)
  omega

/-- The input buffer's lane `j`, `k` scalars copied. -/
def lane (s : MachineState) (k j : Nat) : Word :=
  if j < 4 * k then s.getMem (s.getReg .x10 + BitVec.ofNat 64 (8 * j))
  else if j < 16 then 0 else s.getMem (s.getReg .x10 + 128 + BitVec.ofNat 64 (8 * j))

/-- Between the `memset` and `keccak_f`: `k` scalars copied, every write in the stack. -/
structure Mid (s u : MachineState) (k : Nat) : Prop where
  x2 : u.getReg .x2 = s.getReg .x2 - 224
  x8 : u.getReg .x8 = s.getReg .x10
  x9 : u.getReg .x9 = s.getReg .x10 + 128
  kept : ∀ r ∈ keptRegs, u.getReg r = s.getReg r
  ra : u.getMem (s.getReg .x2 - 8) = s.getReg .x1
  s0 : u.getMem (s.getReg .x2 - 16) = s.getReg .x8
  s1 : u.getMem (s.getReg .x2 - 24) = s.getReg .x9
  frame : DFrame s u (Within · (stackLo s duplexStack) duplexStack)
  buf : ∀ j < 25, u.getMem (s.getReg .x2 - 224 + BitVec.ofNat 64 (8 * j)) = lane s k j

/-- What lies in the sponge is what the entry's memory holds there. -/
theorem keep_sponge {s u : MachineState} (hpre : DuplexPre s)
    (hu : DFrame s u (Within · (stackLo s duplexStack) duplexStack)) {x : Word}
    (h1 : (s.getReg .x10).toNat ≤ x.toNat) (h2 : x.toNat + 8 ≤ (s.getReg .x10).toNat + 336) :
    u.getMem x = s.getMem x := by
  have hs := hpre.sponge
  have hss := hpre.spongeStack
  exact hu x fun i hi h ↦ by addr_omega [h, hi, h1, h2, hs, hss]

/-- One copy block: scalar `k`'s four doublewords at `sp - 224 + 32 k`. -/
theorem Mid.copy {s u u' : MachineState} {k : Nat} (hpre : DuplexPre s) (h : Mid s u k)
    (hk : k < 4)
    (hm : ∀ m < 4, u'.getMem (s.getReg .x2 - 224 + BitVec.ofNat 64 (32 * k + 8 * m)) =
      u.getMem (s.getReg .x10 + BitVec.ofNat 64 (32 * k + 8 * m)))
    (hf : MemFrame u u' (s.getReg .x2 - 224 + BitVec.ofNat 64 (32 * k)) 32)
    (hr : ∀ r ∈ [Reg.x2, .x8, .x9] ++ keptRegs, u'.getReg r = u.getReg r) : Mid s u' (k + 1) := by
  have hb := bounds hpre
  have hs := hpre.sponge
  have hfr : DFrame s u' (Within · (stackLo s duplexStack) duplexStack) :=
    h.frame.trans ((DFrame.of_memFrame hf).mono fun a ha ↦ by addr_omega [ha, hb, hk])
      fun _ h ↦ h
  have old (x : Word) (hx : ¬ Within x (s.getReg .x2 - 224 + BitVec.ofNat 64 (32 * k)) 32) :
      u'.getMem x = u.getMem x := hf x hx
  refine ⟨(hr _ (by decide)).trans h.x2, (hr _ (by decide)).trans h.x8,
    (hr _ (by decide)).trans h.x9,
    fun r hr' ↦ (hr r (by simp [hr'])).trans (h.kept r hr'),
    (old _ (by addr_omega [hb, hk])).trans h.ra, (old _ (by addr_omega [hb, hk])).trans h.s0,
    (old _ (by addr_omega [hb, hk])).trans h.s1, hfr, fun j hj ↦ ?_⟩
  by_cases hin : 4 * k ≤ j ∧ j < 4 * k + 4
  · have hj' : 8 * j = 32 * k + 8 * (j - 4 * k) := by omega
    rw [hj', hm _ (by omega), keep_sponge hpre h.frame (by addr_omega [hs, hin, hk])
      (by addr_omega [hs, hin, hj, hk]), ← hj']
    simp only [lane, show j < 4 * (k + 1) by omega, ↓reduceIte]
  · rw [old _ (by addr_omega [hb, hin, hj, hk]), h.buf j hj]
    by_cases hlt : j < 4 * k
    · simp only [lane, hlt, show j < 4 * (k + 1) by omega, ↓reduceIte]
    · simp only [lane, hlt, show ¬ j < 4 * (k + 1) by omega, ↓reduceIte]

/-- A step that writes no memory and keeps the registers `Mid` names. -/
theorem Mid.same {s u u' : MachineState} {k : Nat} (h : Mid s u k)
    (hm : ∀ a, u'.getMem a = u.getMem a)
    (hr : ∀ r ∈ [Reg.x2, .x8, .x9] ++ keptRegs, u'.getReg r = u.getReg r) : Mid s u' k :=
  ⟨(hr _ (by decide)).trans h.x2, (hr _ (by decide)).trans h.x8,
    (hr _ (by decide)).trans h.x9,
    fun r hr' ↦ (hr r (by simp [hr'])).trans (h.kept r hr'), (hm _).trans h.ra, (hm _).trans h.s0,
    (hm _).trans h.s1, h.frame.trans (DFrame.of_same hm _) fun _ h ↦ h,
    fun j hj ↦ (hm _).trans (h.buf j hj)⟩

/-- The `n` bytes from `a` held `0`. -/
theorem getMem_zero_of_bytesAt {t : MachineState} {a : Word} {N k : Nat} {z : BitVec 8}
    (hz : z = 0) (h : bytesAt t a N = List.replicate N z) (ha : a.toNat % 8 = 0) (hk : k % 8 = 0)
    (hkN : k + 8 ≤ N) : t.getMem (a + BitVec.ofNat 64 k) = 0 := by
  subst hz
  refine eq_of_extractByte fun i hi ↦ ?_
  have hal : (a + BitVec.ofNat 64 k).toNat % 8 = 0 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  rw [← byteAt_add hal hi, add_ofNat_add]
  have e := List.getElem_of_eq h (by rw [bytesAt_length]; omega : k + i < (bytesAt t a N).length)
  rw [bytesAt_getElem, List.getElem_replicate] at e
  rw [e]
  simp [extractByte]

theorem trap : Image.code.fetch 0x80007df8 = none :=
  Option.isNone_iff_eq_none.mp (by decide +kernel)

/-- The frame, `memcpy` of the state, `memset` of the rate, the check `n_pending < 5`. -/
theorem prologue (hMC : MemcpySpec 0x800126e4) (hMS : MemsetSpec 0x800126f4) {s : MachineState}
    (hpc : s.pc = 0x80007cd8) (hpre : DuplexPre s) :
    ∃ u, Reaches Image.code s u ∧ ((u.pc = 0x80007d24 ∧ Mid s u 0 ∧
      u.getReg .x10 = s.getMem (s.getReg .x10 + 328) ∧
      (s.getMem (s.getReg .x10 + 328)).toNat < 5) ∨ Dead Image.code u) := by
  have hb := bounds hpre
  have hs := hpre.sponge
  have hss := hpre.spongeStack
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80007cd8_spec hpc (by
    rv_eval []
    and_intros <;> valid_access hpre.stack.valid [hb])
  have k₁ := b80007cd8_keeps h₁
  have x1₁ := b80007cd8_x1 h₁
  have x2₁ := b80007cd8_x2 h₁
  have x8₁ := b80007cd8_x8 h₁
  have x9₁ := b80007cd8_x9 h₁
  have x10₁ := b80007cd8_x10 h₁
  have x11₁ := b80007cd8_x11 h₁
  have x12₁ := b80007cd8_x12 h₁
  have ra₁ := b80007cd8_m_x2_n8 h₁
  have s0₁ := b80007cd8_m_x2_n16 h₁
  have s1₁ := b80007cd8_m_x2_n24 h₁
  have F₁ : DFrame s t₁ (Within · (stackLo s duplexStack) duplexStack) :=
    (DFrame.of_memFrame (b80007cd8_frame h₁ (by addr_omega [hb]))).mono fun a ha ↦ by
      addr_omega [ha, hb]
  have h200 : (200 : Word).toNat = 200 := rfl
  -- `memcpy(input, state, 200)`
  have hmc : MemcpyPre t₁ := {
    dst := by rw [x10₁, x12₁]; addr_omega [hb]
    src := by rw [x11₁, x12₁]; addr_omega [hs]
    apart := by rw [x10₁, x11₁, x12₁]; addr_omega [hb, hs, hss]
    stack := ⟨by simp only [stackLo, x2₁]; valid_sub hpre.stack.valid [hb],
      by rw [x2₁]; addr_omega [hb]⟩
    dstStack := by rw [x10₁, x12₁]; simp only [stackLo, x2₁]; addr_omega [hb]
    srcStack := by rw [x11₁, x12₁]; simp only [stackLo, x2₁]; addr_omega [hb, hs, hss] }
  obtain ⟨t₂, hr₂, ⟨hpc₂, hpres₂, hpost₂⟩ | hdead⟩ := hMC.call hr₁ (b80007cd8_pc h₁) hmc
  swap
  · exact ⟨_, hr₂, Or.inr hdead⟩
  have by₂ := hpost₂.bytes
  rw [x10₁, x11₁, x12₁, h200] at by₂
  have G₂ : DFrame t₁ t₂ (Within · (stackLo s duplexStack) (duplexStack - 24)) :=
    (DFrame.of_byteFrame hpost₂.frame).mono fun a ha ↦ by
      rw [x10₁, x12₁, h200] at ha
      simp only [stackLo, x2₁] at ha
      rcases ha with ha | ha <;> addr_omega [ha, hb]
  have buf₂ (j : Nat) (hj : j < 25) : t₂.getMem (s.getReg .x2 - 224 + BitVec.ofNat 64 (8 * j)) =
      s.getMem (s.getReg .x10 + 128 + BitVec.ofNat 64 (8 * j)) := by
    rw [getMem_eq_of_bytesAt by₂ (by addr_omega [hb]) (by addr_omega [hs]) (by omega) (by omega)]
    exact keep_sponge hpre F₁ (by addr_omega [hs, hj]) (by addr_omega [hs, hj])
  have x2₂ : t₂.getReg .x2 = s.getReg .x2 - 224 := (hpres₂.reg .x2).trans x2₁
  -- `memset(input, 0, 128)`
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80007d04_spec
    (by rw [hpc₂, returnAddress_eq, x1₁]; decide) trivial
  have k₃ := b80007d04_keeps h₃
  have x10₃ : t₃.getReg .x10 = s.getReg .x2 - 224 := (b80007d04_x10 h₃).trans x2₂
  have x11₃ := b80007d04_x11 h₃
  have x12₃ := b80007d04_x12 h₃
  have h128 : (128 : Word).toNat = 128 := rfl
  obtain ⟨t₄, hr₄, ⟨hpc₄, hpres₄, hpost₄⟩ | hdead⟩ := hMS.call (hr₂.trans hr₃) (b80007d04_pc h₃)
    (show MemsetPre t₃ by simp only [MemsetPre]; rw [x10₃, x12₃, h128]; addr_omega [hb])
  swap
  · exact ⟨_, hr₄, Or.inr hdead⟩
  have by₄ := hpost₄.bytes
  rw [x10₃, x11₃, x12₃, h128] at by₄
  have G₄ : DFrame t₁ t₄ (Within · (stackLo s duplexStack) (duplexStack - 24)) :=
    (G₂.trans (DFrame.of_same (b80007d04_mem_same h₃) _) fun _ h ↦ h).trans
      (DFrame.of_byteFrame hpost₄.frame) fun a ha ↦ by
        rw [x10₃, x12₃, h128] at ha
        addr_omega [ha, hb]
  have F₄ : DFrame s t₄ (Within · (stackLo s duplexStack) duplexStack) :=
    F₁.trans G₄ fun a ha ↦ by addr_omega [ha, hb]
  have buf₄ (j : Nat) (hj : j < 25) :
      t₄.getMem (s.getReg .x2 - 224 + BitVec.ofNat 64 (8 * j)) = lane s 0 j := by
    by_cases h16 : j < 16
    · rw [getMem_zero_of_bytesAt (by rfl) by₄ (by addr_omega [hb]) (by omega) (by omega)]
      simp only [lane, Nat.mul_zero, Nat.not_lt_zero, h16, ↓reduceIte]
    · rw [DFrame.of_byteFrame hpost₄.frame _ fun i hi ha ↦ by
          rw [x10₃, x12₃, h128] at ha
          addr_omega [ha, hi, hb, hj, h16],
        b80007d04_mem_same h₃, buf₂ j hj]
      simp only [lane, Nat.mul_zero, Nat.not_lt_zero, h16, ↓reduceIte]
  have x8₄ : t₄.getReg .x8 = s.getReg .x10 := by
    rw [hpres₄.reg .x8, k₃ .x8 (by decide), hpres₂.reg .x8, x8₁]
  have slot (x : Word) (h1 : (s.getReg .x2).toNat - 24 ≤ x.toNat) (h2 : x.toNat + 8 ≤ (s.getReg .x2).toNat) :
      t₄.getMem x = t₁.getMem x :=
    G₄ x fun i hi h ↦ by addr_omega [h, hi, h1, h2, hb]
  -- `n_pending ≥ 5` traps
  obtain ⟨t₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b80007d18_spec
    (by rw [hpc₄, returnAddress_eq, b80007d04_x1 h₃]; decide) (by
      rv_eval [x8₄]
      refine Region.valid hs ?_ ?_ ?_ <;> addr_omega [hs])
  have k₅ := b80007d18_keeps h₅
  have hn : t₄.getMem (t₄.getReg .x8 + 328) = s.getMem (s.getReg .x10 + 328) := by
    rw [x8₄]; exact keep_sponge hpre F₄ (by addr_omega [hs]) (by addr_omega [hs])
  by_cases h5 : 5 ≤ (s.getMem (s.getReg .x10 + 328)).toNat
  · refine ⟨t₅, (hr₄.trans hr₅), Or.inr (dead_of_fetch ?_)⟩
    rw [b80007d18_pc_taken h₅ (by rw [hn]; exact h5)]
    exact trap
  refine ⟨t₅, hr₄.trans hr₅, Or.inl ⟨b80007d18_pc_not_taken h₅ (by rw [hn, show (5 : Word).toNat = 5 from rfl]; omega), ?_,
    by rw [b80007d18_x10 h₅, hn], by omega⟩⟩
  have hm₅ := b80007d18_mem_same h₅
  exact {
    x2 := by rw [k₅ .x2 (by decide), hpres₄.reg .x2, k₃ .x2 (by decide), x2₂]
    x8 := by rw [k₅ .x8 (by decide), x8₄]
    x9 := by rw [k₅ .x9 (by decide), hpres₄.reg .x9, k₃ .x9 (by decide), hpres₂.reg .x9, x9₁]
    kept := fun r hr ↦ by
      rw [k₅ r (mem_of_mem hr _), hpres₄ r (mem_of_mem hr _), k₃ r (mem_of_mem hr _),
        hpres₂ r (mem_of_mem hr _), k₁ r (mem_of_mem hr _)]
    ra := by rw [hm₅, slot _ (by addr_omega [hb]) (by addr_omega [hb]), ra₁]
    s0 := by rw [hm₅, slot _ (by addr_omega [hb]) (by addr_omega [hb]), s0₁]
    s1 := by rw [hm₅, slot _ (by addr_omega [hb]) (by addr_omega [hb]), s1₁]
    frame := F₄.trans (DFrame.of_same hm₅ _) fun _ h ↦ h
    buf := fun j hj ↦ (hm₅ _).trans (buf₄ j hj) }

theorem word_eq_of_toNat {w : Word} {n : Nat} (h : w.toNat = n) (hn : n < 2 ^ 64) :
    w = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq; rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

/-- The copy blocks: after `n_pending` of them, at `keccak_f`'s call. -/
theorem copies {s u : MachineState} (hpre : DuplexPre s) (hpc : u.pc = 0x80007d24) (h : Mid s u 0)
    (hx : u.getReg .x10 = s.getMem (s.getReg .x10 + 328))
    (hn : (s.getMem (s.getReg .x10 + 328)).toNat < 5) :
    ∃ v, Reaches Image.code u v ∧ v.pc = 0x80007dc0 ∧
      Mid s v (s.getMem (s.getReg .x10 + 328)).toNat := by
  have hb := bounds hpre
  have hs := hpre.sponge
  generalize hN : (s.getMem (s.getReg .x10 + 328)).toNat = n at hn
  have hw : s.getMem (s.getReg .x10 + 328) = BitVec.ofNat 64 n := word_eq_of_toNat hN (by omega)
  rw [hw] at hx
  have obl (v : MachineState) (k : Nat) (hv : Mid s v k) (o : Word) (ho : o.toNat + 8 ≤ 200)
      (ho8 : o.toNat % 8 = 0) :
      Sym.validAccess 8 (v.getReg .x8 + o) = true ∧ Sym.validAccess 8 (v.getReg .x2 + o) = true := by
    rw [hv.x8, hv.x2]
    exact ⟨Region.valid hs (by addr_omega [hs, ho]) (by addr_omega [hs, ho]) (by addr_omega [hs, ho, ho8]),
      by valid_access hpre.stack.valid [hb, ho, ho8]⟩
  obtain ⟨u₀, hr₀, h₀⟩ := Sym.BlockSpec.reaches b80007d24_spec hpc trivial
  have M₀ := h.same (b80007d24_mem_same h₀) fun r hr ↦ b80007d24_keeps h₀ r (mem_of_mem hr _)
  have x0 : u₀.getReg .x10 = BitVec.ofNat 64 n := (b80007d24_keeps h₀ .x10 (by decide)).trans hx
  by_cases e0 : n = 0
  · subst e0
    exact ⟨u₀, hr₀, b80007d24_pc_taken h₀ (by rw [hx]; rfl), M₀⟩
  have p₀ := b80007d24_pc_not_taken h₀ (by rw [hx]; exact fun h ↦ e0 (by
    have := congrArg BitVec.toNat h; rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this))
  -- scalar 0
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80007d28_spec p₀ (by
    have o0 := obl u₀ 0 M₀ 0 (by decide) (by decide)
    have o1 := obl u₀ 0 M₀ 8 (by decide) (by decide)
    have o2 := obl u₀ 0 M₀ 16 (by decide) (by decide)
    have o3 := obl u₀ 0 M₀ 24 (by decide) (by decide)
    rw [Sym.add_zero_lit, Sym.add_zero_lit] at o0
    rv_eval []
    exact ⟨o3.2, o2.2, o1.2, o0.2, o3.1, o2.1, o1.1, o0.1⟩)
  have M₁ : Mid s u₁ 1 := M₀.copy hpre (by decide)
    (fun m hm ↦ by
      have e0 := b80007d28_m_x2_0 h₁
      have e1 := b80007d28_m_x2_8 h₁
      have e2 := b80007d28_m_x2_16 h₁
      have e3 := b80007d28_m_x2_24 h₁
      rw [M₀.x2, M₀.x8] at e0 e1 e2 e3
      interval_cases m
      · simpa only [Nat.mul_zero, Nat.add_zero, add_ofNat_zero] using e0
      · exact e1
      · exact e2
      · exact e3)
    (by
      have f := b80007d28_frame h₁ (by rw [M₀.x2]; addr_omega [hb])
      rw [M₀.x2] at f
      simpa only [Nat.mul_zero, add_ofNat_zero] using f)
    fun r hr ↦ b80007d28_keeps h₁ r (mem_of_mem hr _)
  have x1 : u₁.getReg .x10 = BitVec.ofNat 64 n := (b80007d28_keeps h₁ .x10 (by decide)).trans x0
  by_cases e1 : n = 1
  · subst e1
    exact ⟨u₁, hr₀.trans hr₁, b80007d28_pc_taken h₁ (by rw [x0]; rfl), M₁⟩
  have p₁ := b80007d28_pc_not_taken h₁ (by
    rw [x0]; exact fun h ↦ e1 (by
      have := congrArg BitVec.toNat h; rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this))
  -- scalar 1
  obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80007d50_spec p₁ (by
    have o0 := obl u₁ 1 M₁ 32 (by decide) (by decide)
    have o1 := obl u₁ 1 M₁ 40 (by decide) (by decide)
    have o2 := obl u₁ 1 M₁ 48 (by decide) (by decide)
    have o3 := obl u₁ 1 M₁ 56 (by decide) (by decide)
    rv_eval []
    exact ⟨o3.2, o2.2, o1.2, o0.2, o3.1, o2.1, o1.1, o0.1⟩)
  have M₂ : Mid s u₂ 2 := M₁.copy hpre (by decide)
    (fun m hm ↦ by
      have e0 := b80007d50_m_x2_32 h₂
      have e1 := b80007d50_m_x2_40 h₂
      have e2 := b80007d50_m_x2_48 h₂
      have e3 := b80007d50_m_x2_56 h₂
      rw [M₁.x2, M₁.x8] at e0 e1 e2 e3
      interval_cases m
      · exact e0
      · exact e1
      · exact e2
      · exact e3)
    (by
      have f := b80007d50_frame h₂ (by rw [M₁.x2]; addr_omega [hb])
      rw [M₁.x2] at f
      exact f)
    fun r hr ↦ b80007d50_keeps h₂ r (mem_of_mem hr _)
  have x2 : u₂.getReg .x10 = BitVec.ofNat 64 n := (b80007d50_keeps h₂ .x10 (by decide)).trans x1
  by_cases e2 : n = 2
  · subst e2
    exact ⟨u₂, (hr₀.trans hr₁).trans hr₂,
      b80007d50_pc_taken h₂ (by rw [x1]; rfl), M₂⟩
  have p₂ := b80007d50_pc_not_taken h₂ (by
    rw [x1]; exact fun h ↦ e2 (by
      have := congrArg BitVec.toNat h; rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this))
  -- scalar 2
  obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80007d78_spec p₂ (by
    have o0 := obl u₂ 2 M₂ 64 (by decide) (by decide)
    have o1 := obl u₂ 2 M₂ 72 (by decide) (by decide)
    have o2 := obl u₂ 2 M₂ 80 (by decide) (by decide)
    have o3 := obl u₂ 2 M₂ 88 (by decide) (by decide)
    rv_eval []
    exact ⟨o3.2, o2.2, o1.2, o0.2, o3.1, o2.1, o1.1, o0.1⟩)
  have M₃ : Mid s u₃ 3 := M₂.copy hpre (by decide)
    (fun m hm ↦ by
      have e0 := b80007d78_m_x2_64 h₃
      have e1 := b80007d78_m_x2_72 h₃
      have e2 := b80007d78_m_x2_80 h₃
      have e3 := b80007d78_m_x2_88 h₃
      rw [M₂.x2, M₂.x8] at e0 e1 e2 e3
      interval_cases m
      · exact e0
      · exact e1
      · exact e2
      · exact e3)
    (by
      have f := b80007d78_frame h₃ (by rw [M₂.x2]; addr_omega [hb])
      rw [M₂.x2] at f
      exact f)
    fun r hr ↦ b80007d78_keeps h₃ r (mem_of_mem hr _)
  by_cases e3 : n = 3
  · subst e3
    exact ⟨u₃, ((hr₀.trans hr₁).trans hr₂).trans hr₃,
      b80007d78_pc_taken h₃ (by rw [x2]; rfl), M₃⟩
  have p₃ := b80007d78_pc_not_taken h₃ (by
    rw [x2]; exact fun h ↦ e3 (by
      have := congrArg BitVec.toNat h; rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this))
  -- scalar 3
  obtain ⟨u₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b80007da0_spec p₃ (by
    have o0 := obl u₃ 3 M₃ 96 (by decide) (by decide)
    have o1 := obl u₃ 3 M₃ 104 (by decide) (by decide)
    have o2 := obl u₃ 3 M₃ 112 (by decide) (by decide)
    have o3 := obl u₃ 3 M₃ 120 (by decide) (by decide)
    rv_eval []
    exact ⟨o3.2, o2.2, o1.2, o0.2, o3.1, o2.1, o1.1, o0.1⟩)
  have M₄ : Mid s u₄ 4 := M₃.copy hpre (by decide)
    (fun m hm ↦ by
      have e0 := b80007da0_m_x2_96 h₄
      have e1 := b80007da0_m_x2_104 h₄
      have e2 := b80007da0_m_x2_112 h₄
      have e3 := b80007da0_m_x2_120 h₄
      rw [M₃.x2, M₃.x8] at e0 e1 e2 e3
      interval_cases m
      · exact e0
      · exact e1
      · exact e2
      · exact e3)
    (by
      have f := b80007da0_frame h₄ (by rw [M₃.x2]; addr_omega [hb])
      rw [M₃.x2] at f
      exact f)
    fun r hr ↦ b80007da0_keeps h₄ r (mem_of_mem hr _)
  have e4 : n = 4 := by omega
  subst e4
  exact ⟨u₄, (((hr₀.trans hr₁).trans hr₂).trans hr₃).trans hr₄, b80007da0_pc h₄, M₄⟩

/-- `keccak_f` on the buffer, `memcpy` back, `n_pending = 0`, return. -/
theorem epilogue (hMC : MemcpySpec 0x800126e4) (hK : Contracts.KeccakFSpec) {s v : MachineState}
    (hpre : DuplexPre s) (hpc : v.pc = 0x80007dc0) (h : Mid s v (nPending s (s.getReg .x10)))
    (hn : nPending s (s.getReg .x10) ≤ 4) :
    ∃ t, Reaches Image.code v t ∧
      ((t.pc = returnAddress s ∧ Preserves s t ∧ DuplexPost s t) ∨ Dead Image.code t) := by
  have hb := bounds hpre
  have hs := hpre.sponge
  have hss := hpre.spongeStack
  have hro := hpre.stack.rodata
  have h200 : (200 : Word).toNat = 200 := rfl
  -- `keccak_f(input)`
  obtain ⟨w₀, hr₀, h₀⟩ := Sym.BlockSpec.reaches b80007dc0_spec hpc trivial
  have k₀ := b80007dc0_keeps h₀
  have x10₀ : w₀.getReg .x10 = s.getReg .x2 - 224 := (b80007dc0_x10 h₀).trans h.x2
  have x2₀ : w₀.getReg .x2 = s.getReg .x2 - 224 := (k₀ .x2 (by decide)).trans h.x2
  have hm₀ := b80007dc0_mem_same h₀
  have F₀ : DFrame s w₀ (Within · (stackLo s duplexStack) duplexStack) :=
    h.frame.trans (DFrame.of_same hm₀ _) fun _ h ↦ h
  have hrod₀ : RodataOk w₀ :=
    hpre.rodata.dframe F₀ fun a ha hw ↦ by addr_omega [ha, hw, hro, hb]
  have hkp : Contracts.KeccakFPre w₀ := {
    state := by rw [x10₀]; valid_sub hpre.stack.valid [hb]
    stack := ⟨by simp only [stackLo, x2₀]; valid_sub hpre.stack.valid [hb],
      by rw [x2₀]; addr_omega [hb]⟩
    stateStack := by rw [x10₀]; simp only [stackLo, x2₀]; addr_omega [hb]
    tables := keccakTables_of_rodata hrod₀
    tablesState := by rw [x10₀]; addr_omega [hb, hro]
    tablesStack := by simp only [stackLo, x2₀]; addr_omega [hb, hro] }
  obtain ⟨w₁, hr₁, ⟨hpc₁, hpres₁, hpost₁⟩ | hdead⟩ := hK.call hr₀ (b80007dc0_pc h₀) hkp
  swap
  · exact ⟨_, hr₁, Or.inr hdead⟩
  have val₁ : stateAt w₁ (s.getReg .x2 - 224) =
      keccakF1600 (duplexInput (spongeAt s (s.getReg .x10))) := by
    have e := stateAt_keccakF hpost₁.value
    rw [x10₀] at e
    rw [e, stateAt_congr (t' := v) (y := s.getReg .x2 - 224) (fun j _ ↦ hm₀ _),
      stateAt_eq_duplexInput hn (fun j hj ↦ h.buf j hj)]
  have G₁ : DFrame w₀ w₁ (Within · (stackLo s duplexStack) (duplexStack - 24)) :=
    (DFrame.of_two hpost₁.frame).mono fun a ha ↦ by
      rw [x10₀] at ha
      simp only [stackLo, x2₀] at ha
      rcases ha with ha | ha <;> addr_omega [ha, hb]
  -- `memcpy(state, input, 200)`
  obtain ⟨w₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80007dcc_spec
    (by rw [hpc₁, returnAddress_eq, b80007dc0_x1 h₀]; decide) trivial
  have k₂ := b80007dcc_keeps h₂
  have x2₁ : w₁.getReg .x2 = s.getReg .x2 - 224 := (hpres₁.reg .x2).trans x2₀
  have x10₂ : w₂.getReg .x10 = s.getReg .x10 + 128 := by
    rw [b80007dcc_x10 h₂, hpres₁.reg .x9, k₀ .x9 (by decide), h.x9]
  have x11₂ : w₂.getReg .x11 = s.getReg .x2 - 224 := (b80007dcc_x11 h₂).trans x2₁
  have x12₂ := b80007dcc_x12 h₂
  have x2₂ : w₂.getReg .x2 = s.getReg .x2 - 224 := (k₂ .x2 (by decide)).trans x2₁
  have hm₂ := b80007dcc_mem_same h₂
  have hmc : MemcpyPre w₂ := {
    dst := by rw [x10₂, x12₂]; addr_omega [hs]
    src := by rw [x11₂, x12₂]; addr_omega [hb]
    apart := by rw [x10₂, x11₂, x12₂]; addr_omega [hb, hs, hss]
    stack := ⟨by simp only [stackLo, x2₂]; valid_sub hpre.stack.valid [hb],
      by rw [x2₂]; addr_omega [hb]⟩
    dstStack := by rw [x10₂, x12₂]; simp only [stackLo, x2₂]; addr_omega [hb, hs, hss]
    srcStack := by rw [x11₂, x12₂]; simp only [stackLo, x2₂]; addr_omega [hb] }
  obtain ⟨w₃, hr₃, ⟨hpc₃, hpres₃, hpost₃⟩ | hdead⟩ :=
    hMC.call (hr₁.trans hr₂) (b80007dcc_pc h₂) hmc
  swap
  · exact ⟨_, hr₃, Or.inr hdead⟩
  have by₃ := hpost₃.bytes
  rw [x10₂, x11₂, x12₂, h200] at by₃
  have H₁ : DFrame v w₁ (fun x ↦ Within x (s.getReg .x10) 336 ∨
      Within x (stackLo s duplexStack) (duplexStack - 24)) :=
    (DFrame.of_same hm₀ _).trans G₁ fun _ h ↦ Or.inr h
  have H₂ : DFrame v w₂ (fun x ↦ Within x (s.getReg .x10) 336 ∨
      Within x (stackLo s duplexStack) (duplexStack - 24)) :=
    H₁.trans (DFrame.of_same hm₂ _) fun _ h ↦ h
  have H : DFrame v w₃ (fun x ↦ Within x (s.getReg .x10) 336 ∨
      Within x (stackLo s duplexStack) (duplexStack - 24)) :=
    H₂.trans (DFrame.of_byteFrame hpost₃.frame) fun x hx ↦ by
      rw [x10₂, x12₂, h200] at hx
      simp only [stackLo, x2₂] at hx
      rcases hx with hx | hx
      · exact Or.inl (by addr_omega [hx, hs])
      · exact Or.inr (by addr_omega [hx, hb])
  have slot (x : Word) (h1 : (s.getReg .x2).toNat - 24 ≤ x.toNat)
      (h2 : x.toNat + 8 ≤ (s.getReg .x2).toNat) : w₃.getMem x = v.getMem x :=
    H x fun i hi hx ↦ by rcases hx with hx | hx <;> addr_omega [hx, hi, h1, h2, hb, hss, hs]
  -- `n_pending = 0`, return
  have x2₃ : w₃.getReg .x2 = s.getReg .x2 - 224 := (hpres₃.reg .x2).trans x2₂
  have x8₃ : w₃.getReg .x8 = s.getReg .x10 := by
    rw [hpres₃.reg .x8, k₂ .x8 (by decide), hpres₁.reg .x8, k₀ .x8 (by decide), h.x8]
  obtain ⟨t, hr₄, h₄⟩ := Sym.BlockSpec.reaches b80007de0_spec
    (by rw [hpc₃, returnAddress_eq, b80007dcc_x1 h₂]; decide) (by
      rv_eval [x2₃, x8₃]
      and_intros <;> first
        | addr_omega [hb, hs, hss]
        | valid_access hpre.stack.valid [hb]
        | (refine Region.valid hs ?_ ?_ ?_ <;> addr_omega [hs]))
  have k₄ := b80007de0_keeps h₄
  have pc₄ := b80007de0_pc h₄
  have x2₄ := b80007de0_x2 h₄
  have x8₄ := b80007de0_x8 h₄
  have x9₄ := b80007de0_x9 h₄
  have m₄ := b80007de0_m_x8_328 h₄
  have f₄ := b80007de0_frame h₄ (by rw [x8₃]; addr_omega [hs])
  rv_eval [x2₃] at pc₄ x2₄ x8₄ x9₄
  rw [x8₃] at m₄ f₄
  have hk : ∀ r ∈ keptRegs, t.getReg r = s.getReg r := fun r hr ↦ by
    rw [k₄ r (mem_of_mem hr _), hpres₃ r (mem_of_mem hr _), k₂ r (mem_of_mem hr _),
      hpres₁ r (mem_of_mem hr _), k₀ r (mem_of_mem hr _), h.kept r hr]
  refine ⟨t, hr₃.trans hr₄, Or.inl ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [pc₄, slot _ (by addr_omega [hb]) (by addr_omega [hb]), h.ra, returnAddress_eq]
  · exact preserves_of x2₄
      (by rw [x8₄, slot _ (by addr_omega [hb]) (by addr_omega [hb]), h.s0])
      (by rw [x9₄, slot _ (by addr_omega [hb]) (by addr_omega [hb]), h.s1])
      (hk _ (by decide)) (hk _ (by decide)) fun r hr ↦ hk r (mem_of_mem hr _)
  · rw [spongeAt_of_empty m₄]
    show (⟨stateAt t _, []⟩ : Sponge) =
      ⟨keccakF1600 (duplexInput (spongeAt s (s.getReg .x10))), []⟩
    rw [← val₁, stateAt_congr (t' := w₂) (y := s.getReg .x2 - 224) fun j hj ↦ ?_]
    · rw [stateAt_congr (t' := w₁) (y := s.getReg .x2 - 224) fun j _ ↦ hm₂ _]
    rw [f₄ _ (by addr_omega [hs, hj]),
      getMem_eq_of_bytesAt by₃ (by addr_omega [hs]) (by addr_omega [hb]) (by omega) (by omega)]
  · have Hs : DFrame s w₃ (fun x ↦ Within x (s.getReg .x10) 336 ∨
        Within x (stackLo s duplexStack) duplexStack) :=
      (h.frame.mono fun _ hx ↦ Or.inr hx).trans H fun x hx ↦ by
        rcases hx with hx | hx
        · exact Or.inl hx
        · exact Or.inr (by addr_omega [hx, hb])
    exact Hs.trans (DFrame.of_memFrame f₄) fun x hx ↦ Or.inl (by addr_omega [hx, hs])

/-- **`Sponge::duplex` meets its contract**, given `memcpy`'s, `memset`'s and `keccak_f`'s. -/
theorem duplex_spec (hMC : MemcpySpec 0x800126e4) (hMS : MemsetSpec 0x800126f4)
    (hK : Contracts.KeccakFSpec) : DuplexSpec := by
  intro s hpc hpre
  obtain ⟨u, hsu, ⟨hpcu, hu, hx, hn⟩ | hd⟩ := prologue hMC hMS hpc hpre
  · obtain ⟨v, huv, hpcv, hv⟩ := copies hpre hpcu hu hx hn
    have e : nPending s (s.getReg .x10) = (s.getMem (s.getReg .x10 + 328)).toNat := by
      unfold nPending; omega
    obtain ⟨t, hvt, ht⟩ := epilogue hMC hK hpre hpcv (e ▸ hv) (by unfold nPending; omega)
    exact ⟨t, hsu.trans (huv.trans hvt), ht⟩
  · exact ⟨u, hsu, Or.inr hd⟩

end Rv64Verifier.Transcript.Duplex
