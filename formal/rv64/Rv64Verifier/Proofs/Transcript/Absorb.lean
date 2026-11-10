import Rv64Verifier.Proofs.Transcript.Sponge
import Rv64Verifier.Proofs.Transcript.Contracts
import Rv64Verifier.Blocks.F48

/-!
# `Sponge::absorb`

```rust
fn absorb(&mut self, value: E, tag: u64) {
    if self.n_pending == RATE_SCALARS {
        self.duplex();
    }
    self.pending[self.n_pending] = (value, tag);
    self.n_pending += 1;
}
```

compiled at `0x8000c808` (`Blocks/F48.lean`), `value` by reference in `a1`: a 32-byte frame saving
`ra`, `s0`..`s2`; `n_pending = 4` calls `duplex` (`0x8000c834`) and reloads it (`0x8000c840`);
`0x8000c844` traps if `n_pending > 3`; `0x8000c84c` writes the scalar and its tag at
`32 n_pending`, increments `n_pending`, and returns (`tail`, `spongeAt_push`).
-/

namespace Rv64Verifier.Transcript.Absorb
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F48
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- The callee-saved registers the function never touches. -/
def keptRegs : List Reg := [.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27]

theorem bounds {s : MachineState} (h : AbsorbPre s) :
    0xa0000000 + absorbStack ≤ (s.getReg .x2).toNat ∧ (s.getReg .x2).toNat ≤ 0xc0000000 ∧
      (s.getReg .x2).toNat % 16 = 0 ∧
      (stackLo s absorbStack).toNat = (s.getReg .x2).toNat - absorbStack := by
  have hm := h.stack.mapped (by decide) (by decide)
  have hb := h.stack.bounds (by decide) (by decide)
  omega

theorem trap : Image.code.fetch 0x8000c894 = none :=
  Option.isNone_iff_eq_none.mp (by decide +kernel)

theorem mul32 (w : Word) : w * 32 = BitVec.ofNat 64 (32 * w.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_mul, BitVec.toNat_ofNat, show (32 : Word).toNat = 32 from rfl]
  omega

/-- From `0x8000c844`: the check `n_pending ≤ 3`, the push, the return. -/
theorem tail {s u : MachineState} (hpre : AbsorbPre s) (hpc : u.pc = 0x8000c844)
    (x2 : u.getReg .x2 = s.getReg .x2 - 32) (x8 : u.getReg .x8 = s.getReg .x10)
    (x9 : u.getReg .x9 = s.getReg .x12) (x18 : u.getReg .x18 = s.getReg .x11)
    (x10 : u.getReg .x10 = u.getMem (s.getReg .x10 + 328))
    (kept : ∀ r ∈ keptRegs, u.getReg r = s.getReg r)
    (ra : u.getMem (s.getReg .x2 - 8) = s.getReg .x1)
    (s0 : u.getMem (s.getReg .x2 - 16) = s.getReg .x8)
    (s1 : u.getMem (s.getReg .x2 - 24) = s.getReg .x9)
    (s2 : u.getMem (s.getReg .x2 - 32) = s.getReg .x18)
    (val : eAt u (s.getReg .x11) = eAt s (s.getReg .x11)) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = returnAddress s ∧ Preserves s t ∧
      (u.getMem (s.getReg .x10 + 328)).toNat ≤ 3 ∧
      spongeAt t (s.getReg .x10) = { spongeAt u (s.getReg .x10) with
        pending := (spongeAt u (s.getReg .x10)).pending ++
          [(eAt s (s.getReg .x11), (s.getReg .x12).toNat)] } ∧
      DFrame u t (Within · (s.getReg .x10) 336)) ∨ Dead Image.code t) := by
  have hb := bounds hpre
  have hs := hpre.sponge
  have hv := hpre.value
  have hss := hpre.spongeStack
  have hvs := hpre.valueStack
  have hvsp := hpre.valueSponge
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000c844_spec hpc trivial
  have k₁ := b8000c844_keeps h₁
  have hm₁ := b8000c844_mem_same h₁
  generalize hN : u.getMem (s.getReg .x10 + 328) = w at x10
  by_cases h3 : 3 < w.toNat
  · exact ⟨u₁, hr₁, Or.inr (dead_of_fetch (by
      rw [b8000c844_pc_taken h₁ (by rw [x10]; exact h3)]; exact trap))⟩
  have p₁ := b8000c844_pc_not_taken h₁ (by rw [x10, show (3 : Word).toNat = 3 from rfl]; omega)
  have y2 : u₁.getReg .x2 = s.getReg .x2 - 32 := (k₁ .x2 (by decide)).trans x2
  have y8 : u₁.getReg .x8 = s.getReg .x10 := (k₁ .x8 (by decide)).trans x8
  have y9 : u₁.getReg .x9 = s.getReg .x12 := (k₁ .x9 (by decide)).trans x9
  have y10 : u₁.getReg .x10 = w := (k₁ .x10 (by decide)).trans x10
  have y18 : u₁.getReg .x18 = s.getReg .x11 := (k₁ .x18 (by decide)).trans x18
  obtain ⟨t, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000c84c_spec p₁ (by
    rv_eval [y2, y8, y10, y18]
    and_intros <;> first
      | addr_omega [hb, hs, hss, hvs, hvsp, h3]
      | valid_access hpre.stack.valid [hb]
      | (refine Region.valid hs ?_ ?_ ?_ <;> addr_omega [hs, h3])
      | (refine Region.valid hv ?_ ?_ ?_ <;> addr_omega [hv]))
  have k₂ := b8000c84c_keeps h₂
  have pc₂ := b8000c84c_pc h₂
  have x2₂ := b8000c84c_x2 h₂
  have x8₂ := b8000c84c_x8 h₂
  have x9₂ := b8000c84c_x9 h₂
  have x18₂ := b8000c84c_x18 h₂
  have mc := b8000c84c_m_x8_328 h₂
  have m1 := b8000c84c_m1 h₂
  have m2 := b8000c84c_m2 h₂
  have m3 := b8000c84c_m3 h₂
  have m4 := b8000c84c_m4 h₂
  rv_eval [y2] at pc₂ x2₂ x8₂ x9₂ x18₂
  rw [y8] at mc
  rw [y8, y10, mul32] at m1 m2 m3 m4
  rw [y9] at m1
  rw [y18] at m2 m3 m4
  simp only [hm₁] at pc₂ x8₂ x9₂ x18₂ mc
  rw [hN] at mc
  have hw : w.toNat ≤ 3 := by omega
  -- the writes lie in the sponge
  have fr (y : Word) (hy : ¬ Within y (s.getReg .x10) 336) : t.getMem y = u₁.getMem y :=
    h₂.frame y (by
      rv_eval [y8, y10, mul32]
      and_intros <;> addr_omega [hy, hs, hw])
  have fr' (y : Word) (h1 : (s.getReg .x10).toNat ≤ y.toNat)
      (h2 : y.toNat + 8 ≤ (s.getReg .x10).toNat + 32 * w.toNat ∨
        ((s.getReg .x10).toNat + 128 ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x10).toNat + 328)) :
      t.getMem y = u₁.getMem y :=
    h₂.frame y (by
      rv_eval [y8, y10, mul32]
      and_intros <;> rcases h2 with h2 | h2 <;> addr_omega [h1, h2, hs, hw])
  have hk : ∀ r ∈ keptRegs, t.getReg r = s.getReg r := fun r hr ↦ by
    rw [k₂ r (mem_of_mem hr _), k₁ r (mem_of_mem hr _), kept r hr]
  have hsu : spongeAt u₁ (s.getReg .x10) = spongeAt u (s.getReg .x10) :=
    spongeAt_congr (by addr_omega [hs]) fun x _ _ ↦ hm₁ x
  refine ⟨t, hr₁.trans hr₂, Or.inl ⟨?_, ?_, hw, ?_, ?_⟩⟩
  · rw [pc₂, ra, returnAddress_eq]
  · exact preserves_of x2₂ (by rw [x8₂, s0]) (by rw [x9₂, s1]) (by rw [x18₂, s2])
      (hk _ (by decide)) fun r hr ↦ hk r (mem_of_mem hr _)
  · rw [← hsu]
    refine spongeAt_push (by addr_omega [hs]) (by rw [hm₁, hN]; omega)
      (by rw [mc, hm₁, hN]; addr_omega [hw]) ?_ ?_ ?_
    · rw [hm₁, hN]
      have e : eAt t (s.getReg .x10 + BitVec.ofNat 64 (32 * w.toNat)) =
          eAt u₁ (s.getReg .x11) := by
        unfold Rv64Verifier.eAt; rw [m2, m3, m4]
      rw [e, (DFrame.of_same hm₁ fun _ ↦ False).eAt fun _ _ h ↦ h, val]
    · rw [hm₁, hN, ← add_ofNat_add]
      exact congrArg BitVec.toNat m1
    · intro y h1 h2; rw [hm₁, hN] at h2; exact fr' y h1 h2
  · exact (DFrame.of_same hm₁ _).trans (fun y hy ↦ fr y (by
      simpa only [add_ofNat_zero] using hy 0 (by decide))) fun _ h ↦ h

theorem pending_length (s : MachineState) (a : Word) :
    (spongeAt s a).pending.length = nPending s a := pendingAt_length _ _ _

/-- **`Sponge::absorb` meets its contract**, given `duplex`'s. -/
theorem absorb_spec (hD : DuplexSpec) : AbsorbSpec := by
  intro s hpc hpre
  have hb := bounds hpre
  have hs := hpre.sponge
  have hv := hpre.value
  have hss := hpre.spongeStack
  have hvs := hpre.valueStack
  have hvsp := hpre.valueSponge
  have hro := hpre.stack.rodata
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000c808_spec hpc (by
    rv_eval []
    and_intros <;> first
      | addr_omega [hb, hs, hss]
      | valid_access hpre.stack.valid [hb]
      | (refine Region.valid hs ?_ ?_ ?_ <;> addr_omega [hs]))
  have k₁ := b8000c808_keeps h₁
  have x2₁ := b8000c808_x2 h₁
  have x8₁ := b8000c808_x8 h₁
  have x9₁ := b8000c808_x9 h₁
  have x10₁ := b8000c808_x10 h₁
  have x18₁ := b8000c808_x18 h₁
  have sl₀ := b8000c808_m_x2_n32 h₁
  have sl₁ := b8000c808_m_x2_n24 h₁
  have sl₂ := b8000c808_m_x2_n16 h₁
  have sl₃ := b8000c808_m_x2_n8 h₁
  have f₁ := b8000c808_frame h₁ (by addr_omega [hb])
  have F₁ : DFrame s t₁ (Within · (stackLo s absorbStack) absorbStack) :=
    (DFrame.of_memFrame f₁).mono fun a ha ↦ by addr_omega [ha, hb]
  have keepS (x : Word) (h1 : (s.getReg .x10).toNat ≤ x.toNat)
      (h2 : x.toNat + 8 ≤ (s.getReg .x10).toNat + 336) : t₁.getMem x = s.getMem x :=
    f₁ x (by addr_omega [h1, h2, hss, hb, hs])
  have hsp₁ : spongeAt t₁ (s.getReg .x10) = spongeAt s (s.getReg .x10) :=
    spongeAt_congr (by addr_omega [hs]) keepS
  have val₁ : eAt t₁ (s.getReg .x11) = eAt s (s.getReg .x11) :=
    F₁.eAt fun i hi h ↦ by addr_omega [h, hi, hvs, hb, hv]
  have hn₁ : t₁.getMem (s.getReg .x10 + 328) = s.getMem (s.getReg .x10 + 328) :=
    keepS _ (by addr_omega [hs]) (by addr_omega [hs])
  have hk₁ : ∀ r ∈ keptRegs, t₁.getReg r = s.getReg r := fun r hr ↦ k₁ r (mem_of_mem hr _)
  by_cases h4 : s.getMem (s.getReg .x10 + 328) = 4
  · -- a full queue: `duplex` first
    obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000c834_spec
      (b8000c808_pc_not_taken h₁ h4) trivial
    have k₂ := b8000c834_keeps h₂
    have hm₂ := b8000c834_mem_same h₂
    have x10₂ : t₂.getReg .x10 = s.getReg .x10 := (b8000c834_x10 h₂).trans x8₁
    have x2₂ : t₂.getReg .x2 = s.getReg .x2 - 32 := (k₂ .x2 (by decide)).trans x2₁
    have F₂ : DFrame s t₂ (Within · (stackLo s absorbStack) absorbStack) :=
      F₁.trans (DFrame.of_same hm₂ _) fun _ h ↦ h
    have hdp : DuplexPre t₂ := {
      sponge := by rw [x10₂]; exact hs
      stack := hpre.stack.sub 32 x2₂ (by simp only [absorbStack]; omega) (by decide)
        (by decide) (by decide) (by decide)
      spongeStack := by rw [x10₂]; simp only [stackLo, x2₂]; addr_omega [hb, hss]
      rodata := hpre.rodata.dframe F₂ fun a ha hw ↦ by addr_omega [ha, hw, hro, hb]
      spongeRodata := by rw [x10₂]; exact hpre.spongeRodata }
    obtain ⟨t₃, hr₃, ⟨hpc₃, hpres₃, hpost₃⟩ | hd⟩ := hD.call (hr₁.trans hr₂) (b8000c834_pc h₂) hdp
    swap
    · exact ⟨_, hr₃, Or.inr hd⟩
    have val₃ := hpost₃.value
    rw [x10₂] at val₃
    have G₃ : DFrame t₂ t₃ (fun a ↦ Within a (s.getReg .x10) 336 ∨
        Within a (stackLo s absorbStack) (absorbStack - 32)) :=
      hpost₃.frame.mono fun a ha ↦ by
        rw [x10₂] at ha
        simp only [stackLo, x2₂] at ha
        rcases ha with ha | ha
        · exact Or.inl ha
        · exact Or.inr (by addr_omega [ha, hb])
    have x8₃ : t₃.getReg .x8 = s.getReg .x10 := by
      rw [hpres₃.reg .x8, k₂ .x8 (by decide), x8₁]
    obtain ⟨u, hr₄, h₄⟩ := Sym.BlockSpec.reaches b8000c840_spec
      (by rw [hpc₃, returnAddress_eq, b8000c834_x1 h₂]; decide) (by
        rv_eval [x8₃]
        refine Region.valid hs ?_ ?_ ?_ <;> addr_omega [hs])
    have k₄ := b8000c840_keeps h₄
    have hm₄ := b8000c840_mem_same h₄
    have slot (x : Word) (h1 : (s.getReg .x2).toNat - 32 ≤ x.toNat)
        (h2 : x.toNat + 8 ≤ (s.getReg .x2).toNat) : u.getMem x = t₁.getMem x := by
      rw [hm₄, G₃ x fun i hi h ↦ by rcases h with h | h <;> addr_omega [h, hi, h1, h2, hb, hss, hs],
        hm₂]
    have reg (r : Reg) (hr : r ∈ calleeSaved) : u.getReg r = t₁.getReg r := by
      rw [k₄ r (mem_of_mem hr _), hpres₃ r hr, k₂ r (mem_of_mem hr _)]
    obtain ⟨t, hr₅, ⟨hpc, hpres, hle, hval, hfr⟩ | hd⟩ := tail hpre (b8000c840_pc h₄)
      (by rw [reg .x2 (by decide), x2₁]) (by rw [reg .x8 (by decide), x8₁])
      (by rw [reg .x9 (by decide), x9₁]) (by rw [reg .x18 (by decide), x18₁])
      (by rw [b8000c840_x10 h₄, x8₃, hm₄])
      (fun r hr ↦ by rw [reg r (mem_of_mem hr _), hk₁ r hr])
      (by rw [slot _ (by addr_omega [hb]) (by addr_omega [hb]), sl₃])
      (by rw [slot _ (by addr_omega [hb]) (by addr_omega [hb]), sl₂])
      (by rw [slot _ (by addr_omega [hb]) (by addr_omega [hb]), sl₁])
      (by rw [slot _ (by addr_omega [hb]) (by addr_omega [hb]), sl₀])
      (by
        rw [← val₁, (DFrame.of_same hm₄ fun _ ↦ False).eAt fun _ _ h ↦ h,
          G₃.eAt fun i hi h ↦ by rcases h with h | h <;> addr_omega [h, hi, hvs, hvsp, hb, hv],
          (DFrame.of_same hm₂ fun _ ↦ False).eAt fun _ _ h ↦ h])
    · refine ⟨t, (hr₃.trans hr₄).trans hr₅, Or.inl ⟨hpc, hpres, ⟨?_, ?_⟩⟩⟩
      · have hu : spongeAt u (s.getReg .x10) = spongeAt t₃ (s.getReg .x10) :=
          spongeAt_congr (by addr_omega [hs]) fun x _ _ ↦ hm₄ x
        have h2s : spongeAt t₂ (s.getReg .x10) = spongeAt s (s.getReg .x10) := by
          rw [← hsp₁]; exact spongeAt_congr (by addr_omega [hs]) fun x _ _ ↦ hm₂ x
        rw [hval, hu, val₃, h2s, spAbsorb_eq, pending_length,
          show nPending s (s.getReg .x10) = 4 by unfold nPending; rw [h4]; rfl]
        rfl
      · have H : DFrame s u (fun a ↦ Within a (s.getReg .x10) 336 ∨
            Within a (stackLo s absorbStack) absorbStack) :=
          (((F₂.mono fun _ h ↦ Or.inr h).trans G₃ fun a h ↦ by
            rcases h with h | h
            · exact Or.inl h
            · exact Or.inr (by addr_omega [h, hb])).trans (DFrame.of_same hm₄ _) fun _ h ↦ h)
        exact H.trans hfr fun _ h ↦ Or.inl h
    · exact ⟨t, (hr₃.trans hr₄).trans hr₅, Or.inr hd⟩
  · -- room in the queue
    obtain ⟨t, hr₅, ⟨hpc, hpres, hle, hval, hfr⟩ | hd⟩ := tail hpre (b8000c808_pc_taken h₁ h4)
      x2₁ x8₁ x9₁ x18₁ (by rw [x10₁, hn₁]) hk₁
      (by rw [sl₃]) (by rw [sl₂]) (by rw [sl₁]) (by rw [sl₀]) val₁
    · refine ⟨t, hr₁.trans hr₅, Or.inl ⟨hpc, hpres, ⟨?_, ?_⟩⟩⟩
      · rw [hval, hsp₁, spAbsorb_eq, pending_length]
        have : nPending s (s.getReg .x10) ≠ 4 := by
          rw [hn₁] at hle; unfold nPending; omega
        simp only [this, ↓reduceIte]
      · exact ((F₁.mono fun _ h ↦ Or.inr h).trans hfr fun _ h ↦ Or.inl h)
    · exact ⟨t, hr₁.trans hr₅, Or.inr hd⟩

end Rv64Verifier.Transcript.Absorb
