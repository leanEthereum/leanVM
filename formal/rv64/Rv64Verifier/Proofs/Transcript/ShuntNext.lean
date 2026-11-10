import Rv64Verifier.Proofs.Transcript.Frames
import Rv64Verifier.Proofs.Transcript.Contracts
import Rv64Verifier.Blocks.F91

/-!
# `GenericShunt<Map<Range<usize>, next_scalars::{closure}>, Result<!, _>>::next`

The iterator `next_scalars` collects: past the end, `None`; otherwise `start += 1` and
`next_scalar`, its `Ok` value as `Some`, its error into the residual and `None`.

Compiled at `0x80011ef4` (`Blocks/F91.lean`): a 64-byte frame saving `ra`, `s0`, `s1`; the range
check; `0x80011f14` advances `start` and calls `next_scalar` into `sp + 8` (the frame's `sp`);
`0x80011f34` tests its tag; `0x80011f60` copies the value out (`Some`), `0x80011f48` the error into
the residual; `0x80011f58` is `None` past the end; `0x80011f70` writes the tag and returns
(`exit`).
-/

namespace Rv64Verifier.Transcript.ShuntNext
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Model
  Rv64Verifier.Transcript Rv64Verifier.Blocks.F91
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

attribute [local rv_addr] vecPtr vecLen shuntP shuntR shuntStart shuntEnd

/-- The callee-saved registers the function never touches. -/
def keptRegs : List Reg := [.x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27]

theorem bounds {s : MachineState} (h : ShuntNextPre s) :
    0xa0000000 + shuntNextStack ≤ (s.getReg .x2).toNat ∧ (s.getReg .x2).toNat ≤ 0xc0000000 ∧
      (s.getReg .x2).toNat % 16 = 0 ∧
      (stackLo s shuntNextStack).toNat = (s.getReg .x2).toNat - shuntNextStack := by
  have hm := h.stack.mapped (by decide) (by decide)
  have hb := h.stack.bounds (by decide) (by decide)
  omega

/-- Inside the frame: `s0` = the result, the saved registers in place. -/
structure Inside (s v : MachineState) : Prop where
  x2 : v.getReg .x2 = s.getReg .x2 - 64
  x8 : v.getReg .x8 = s.getReg .x10
  kept : ∀ r ∈ keptRegs, v.getReg r = s.getReg r
  ra : v.getMem (s.getReg .x2 - 8) = s.getReg .x1
  s0 : v.getMem (s.getReg .x2 - 16) = s.getReg .x8
  s1 : v.getMem (s.getReg .x2 - 24) = s.getReg .x9

/-- `0x80011f70`: the tag, the saved registers back, return. -/
theorem exit {s v : MachineState} (hpre : ShuntNextPre s) (hpc : v.pc = 0x80011f70)
    (h : Inside s v) :
    ∃ t, Reaches Image.code v t ∧ t.pc = returnAddress s ∧ Preserves s t ∧
      t.getMem (s.getReg .x10) = v.getReg .x10 ∧ MemFrame v t (s.getReg .x10) 8 := by
  have hb := bounds hpre
  have ho := hpre.out
  have hos := hpre.outStack
  obtain ⟨t, hr, h₁⟩ := Sym.BlockSpec.reaches b80011f70_spec hpc (by
    rv_eval [h.x2, h.x8]
    and_intros <;> first
      | addr_omega [hb, ho, hos]
      | valid_access hpre.stack.valid [hb]
      | (refine Region.valid ho ?_ ?_ ?_ <;> addr_omega [ho]))
  have k := b80011f70_keeps h₁
  have pc := b80011f70_pc h₁
  have y2 := b80011f70_x2 h₁
  have y8 := b80011f70_x8 h₁
  have y9 := b80011f70_x9 h₁
  have m0 := b80011f70_m_x8_0 h₁
  have f := b80011f70_frame h₁ (by rw [h.x8]; addr_omega [ho])
  rv_eval [h.x2] at pc y2 y8 y9
  rw [h.x8] at m0 f
  refine ⟨t, hr, by rw [pc, h.ra, returnAddress_eq], ?_, m0, f⟩
  exact preserves_of y2 (by rw [y8, h.s0]) (by rw [y9, h.s1]) (by rw [k .x18 (by decide),
    h.kept .x18 (by decide)]) (by rw [k .x19 (by decide), h.kept .x19 (by decide)])
    fun r hr ↦ by rw [k r (mem_of_mem hr _), h.kept r (mem_of_mem hr _)]

theorem ProofApart.mono {s : MachineState} {p lo lo' : Word} {n n' : Nat} (h : ProofApart s p lo n)
    (h1 : lo.toNat ≤ lo'.toNat) (h2 : lo'.toNat + n' ≤ lo.toNat + n) : ProofApart s p lo' n' := by
  obtain ⟨ha, hb⟩ := h
  exact ⟨by addr_omega [ha, h1, h2], by addr_omega [hb, h1, h2]⟩

/-- What the shunt writes. -/
def W (s : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x10) 32 ∨ Within a (s.getReg .x11 + 8) 8 ∨ Within a (shuntR s) 16 ∨
    Within a (shuntP s + 8) 344 ∨ Within a (stackLo s shuntNextStack) shuntNextStack

set_option maxHeartbeats 1000000 in
/-- **`GenericShunt::next` meets its contract**, given `next_scalar`'s. -/
theorem shunt_next_spec (hN : NextScalarSpec) : ShuntNextSpec := by
  intro s hpc hpre
  have hb := bounds hpre
  have hself := hpre.self
  have hS := hself.self
  have hP := hself.proof
  have ho := hpre.out
  have hsh := hpre.shunt
  have hR := hpre.residual
  have hro := hpre.stack.rodata
  have hos := hpre.outStack
  have hshs := hpre.shuntStack
  have hrs := hpre.residualStack
  have hss := hpre.selfStack
  have hps := hpre.proofStack
  have hpsh := hpre.proofShunt
  have hpo := hpre.proofOut
  have hpr := hpre.proofResidual
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80011ef4_spec hpc (by
    rv_eval []
    and_intros <;> first
      | addr_omega [hb, hsh, hshs]
      | valid_access hpre.stack.valid [hb]
      | (refine Region.valid hsh ?_ ?_ ?_ <;> addr_omega [hsh]))
  have k₁ := b80011ef4_keeps h₁
  have f₁ := b80011ef4_frame h₁ (by addr_omega [hb])
  have I₁ : Inside s t₁ := ⟨b80011ef4_x2 h₁, b80011ef4_x8 h₁,
    fun r hr ↦ k₁ r (mem_of_mem hr _), b80011ef4_m_x2_n8 h₁, b80011ef4_m_x2_n16 h₁,
    b80011ef4_m_x2_n24 h₁⟩
  have F₁ : DFrame s t₁ (W s) :=
    (DFrame.of_memFrame f₁).mono fun a ha ↦ by
      simp only [W]; exact Or.inr (Or.inr (Or.inr (Or.inr (by addr_omega [ha, hb]))))
  have miss (lo : Word) (n : Nat) (h0 : Apart lo n (s.getReg .x10) 32)
      (h1 : Apart lo n (s.getReg .x11 + 8) 8) (h2 : Apart lo n (s.getMem (s.getReg .x11 + 24)) 16)
      (h3 : Apart lo n (s.getMem (s.getReg .x11) + 8) 344)
      (h4 : Apart lo n (stackLo s shuntNextStack) shuntNextStack) (hn : lo.toNat + n ≤ 2 ^ 64) :
      Misses (W s) lo n := fun y hy hw ↦ by
    simp only [W, shuntP, shuntR] at hw
    rcases hw with hw | hw | hw | hw | hw <;> addr_omega [hy, hw, h0, h1, h2, h3, h4, hn]
  have mP : Misses (W s) (s.getMem (s.getReg .x11)) 8 :=
    miss _ _ (by addr_omega [hpre.outSelf]) (by addr_omega [hpre.shuntSelf, hsh])
      (by addr_omega [hpre.residualSelf]) (by addr_omega [hS]) (by addr_omega [hss])
      (by addr_omega [hS])
  have mQ : Misses (W s) (proofAt s (s.getMem (s.getReg .x11))) 48 :=
    miss _ _ (by addr_omega [hpo]) (by addr_omega [hpsh, hsh]) (by addr_omega [hpr])
      (by addr_omega [hself.apart]) (by addr_omega [hps]) (by addr_omega [hP])
  have mB : Misses (W s) (streamPtr s (s.getMem (s.getReg .x11)))
      (24 * streamLen s (s.getMem (s.getReg .x11))) := by
    rcases hself.stream with h0 | hB
    · intro y hy
      have : streamLen s (s.getMem (s.getReg .x11)) = 0 := h0
      simp only [Within] at hy; omega
    · exact miss _ _ (by addr_omega [hpo]) (by addr_omega [hpsh, hsh]) (by addr_omega [hpr])
        (by addr_omega [hself.apart]) (by addr_omega [hps]) (by addr_omega [hB])
  by_cases hlt : (s.getMem (s.getReg .x11 + 8)).toNat < (s.getMem (s.getReg .x11 + 16)).toNat
  swap
  · -- past the end
    obtain ⟨v, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80011f58_spec
      (b80011ef4_pc_taken h₁ (by omega)) trivial
    have k₂ := b80011f58_keeps h₂
    have hm₂ := b80011f58_mem_same h₂
    obtain ⟨t, hr₃, pc, pres, m0, f⟩ := exit hpre (b80011f58_pc h₂)
      ⟨by rw [k₂ .x2 (by decide), I₁.x2], by rw [k₂ .x8 (by decide), I₁.x8],
        fun r hr ↦ by rw [k₂ r (mem_of_mem hr _), I₁.kept r hr], by rw [hm₂, I₁.ra],
        by rw [hm₂, I₁.s0], by rw [hm₂, I₁.s1]⟩
    have F' : DFrame s t (fun a ↦ Within a (s.getReg .x2 - 24) 24 ∨ Within a (s.getReg .x10) 8) :=
      (((DFrame.of_memFrame f₁).mono fun _ h ↦ Or.inl h).trans (DFrame.of_same hm₂ _)
        fun _ h ↦ h).trans (DFrame.of_memFrame f) fun _ h ↦ Or.inr h
    have F : DFrame s t (W s) := F'.mono fun a ha ↦ by
      simp only [W]
      rcases ha with ha | ha
      · exact Or.inr (Or.inr (Or.inr (Or.inr (by addr_omega [ha, hb]))))
      · exact Or.inl (by addr_omega [ha, ho])
    have miss' (lo : Word) (n : Nat) (h0 : Apart lo n (s.getReg .x10) 8)
        (h4 : Apart lo n (stackLo s shuntNextStack) shuntNextStack) (hn : lo.toNat + n ≤ 2 ^ 64) :
        Misses (fun a ↦ Within a (s.getReg .x2 - 24) 24 ∨ Within a (s.getReg .x10) 8) lo n :=
      fun y hy hw ↦ by rcases hw with hw | hw <;> addr_omega [hy, hw, h0, h4, hn, hb]
    have mB' : Misses (fun a ↦ Within a (s.getReg .x2 - 24) 24 ∨ Within a (s.getReg .x10) 8)
        (streamPtr s (s.getMem (s.getReg .x11))) (24 * streamLen s (s.getMem (s.getReg .x11))) := by
      rcases hself.stream with h0 | hB
      · intro y hy
        have : streamLen s (s.getMem (s.getReg .x11)) = 0 := h0
        simp only [Within] at hy; omega
      · exact miss' _ _ (by addr_omega [hpo]) (by addr_omega [hps]) (by addr_omega [hB])
    refine ⟨t, (hr₁.trans hr₂).trans hr₃, Or.inl ⟨pc, pres, fun T hT ↦ ?_, F⟩⟩
    simp only [shuntP, shuntStart, shuntEnd, hlt, ↓reduceIte]
    refine ⟨by rw [m0, b80011f58_x10 h₂], F' _ (fun i hi hw ↦ by
      rcases hw with hw | hw <;> addr_omega [hw, hi, hpre.outShunt, hsh, hshs, hb, ho]), ?_⟩
    exact F'.transcriptAt hT hself (miss' _ _ (by addr_omega [hpre.outSelf]) (by addr_omega [hss])
        (by addr_omega [hS]))
      (miss' _ _ (by addr_omega [hpo]) (by addr_omega [hps]) (by addr_omega [hP])) mB'
      (miss' _ _ (by addr_omega [hpre.outSelf, hS]) (by addr_omega [hss, hS]) (by addr_omega [hS]))
  -- `start += 1`, `next_scalar(sp + 8, transcript)`
  have x11₁ : t₁.getReg .x11 = s.getReg .x11 := k₁ .x11 (by decide)
  obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80011f14_spec (b80011ef4_pc_not_taken h₁ hlt) (by
    rv_eval [x11₁]
    and_intros <;> (refine Region.valid hsh ?_ ?_ ?_ <;> addr_omega [hsh]))
  have k₂ := b80011f14_keeps h₂
  have f₂ := b80011f14_frame h₂ (by simp only [x11₁]; addr_omega [hsh])
  simp only [x11₁] at f₂
  have mt₁ (y : Word) (h1 : (s.getReg .x11).toNat ≤ y.toNat) (h2 : y.toNat + 8 ≤ (s.getReg .x11).toNat + 32) :
      t₁.getMem y = s.getMem y := f₁ y (by addr_omega [h1, h2, hshs, hb, hsh])
  have x9₂ : t₂.getReg .x9 = s.getMem (s.getReg .x11 + 24) := by
    rw [b80011f14_x9 h₂, x11₁, mt₁ _ (by addr_omega [hsh]) (by addr_omega [hsh])]
  have x10₂ : t₂.getReg .x10 = s.getReg .x2 - 64 + 8 := by rw [b80011f14_x10 h₂, I₁.x2]
  have x11₂ : t₂.getReg .x11 = s.getMem (s.getReg .x11) := by
    rw [b80011f14_x11 h₂, x11₁, mt₁ _ (by addr_omega [hsh]) (by addr_omega [hsh])]
  have x2₂ : t₂.getReg .x2 = s.getReg .x2 - 64 := by rw [k₂ .x2 (by decide), I₁.x2]
  have st₂ : t₂.getMem (s.getReg .x11 + 8) = s.getMem (s.getReg .x11 + 8) + 1 := by
    rw [← x11₁, b80011f14_m_x11_8 h₂, b80011ef4_x13 h₁, x11₁]
  have F₂ : DFrame s t₂ (fun a ↦ Within a (s.getReg .x2 - 24) 24 ∨ Within a (s.getReg .x11 + 8) 8) :=
    ((DFrame.of_memFrame f₁).mono fun _ h ↦ Or.inl h).trans (DFrame.of_memFrame f₂)
      fun _ h ↦ Or.inr h
  have miss₂ (lo : Word) (n : Nat) (h1 : Apart lo n (s.getReg .x11) 32)
      (h4 : Apart lo n (stackLo s shuntNextStack) shuntNextStack) (hn : lo.toNat + n ≤ 2 ^ 64) :
      Misses (fun a ↦ Within a (s.getReg .x2 - 24) 24 ∨ Within a (s.getReg .x11 + 8) 8) lo n :=
    fun y hy hw ↦ by rcases hw with hw | hw <;> addr_omega [hy, hw, h1, h4, hn, hb, hsh]
  have mP₂ := miss₂ (s.getMem (s.getReg .x11)) 8 (by addr_omega [hpre.shuntSelf]) (by addr_omega [hss]) (by addr_omega [hS])
  have mQ₂ := miss₂ (proofAt s (s.getMem (s.getReg .x11))) 48 (by addr_omega [hpsh]) (by addr_omega [hps]) (by addr_omega [hP])
  have hok₂ : TranscriptOk t₂ (s.getMem (s.getReg .x11)) := F₂.transcriptOk hself mP₂ mQ₂
  have hS8 : (s.getMem (s.getReg .x11)).toNat + 8 ≤ 2 ^ 64 := by addr_omega [hS]
  have hP48 : (proofAt s (s.getMem (s.getReg .x11))).toNat + 48 ≤ 2 ^ 64 := by addr_omega [hP]
  have hsm := hpre.stack.mapped (by decide) (by decide)
  have hnp : NextScalarPre t₂ := {
    out := by rw [x10₂]; addr_omega [hsm, hb]
    self := by rw [x11₂]; exact hok₂
    stack := hpre.stack.sub 64 x2₂ (by simp only [shuntNextStack]; omega) (by decide)
      (by decide) (by decide) (by decide)
    outStack := by rw [x10₂]; simp only [stackLo, x2₂]; addr_omega [hb]
    selfStack := by rw [x11₂]; simp only [stackLo, x2₂]; addr_omega [hb, hss]
    outSelf := by rw [x10₂, x11₂]; addr_omega [hb, hss]
    proofStack := by
      rw [x11₂]
      refine F₂.proofApart mP₂ hS8 mQ₂ hP48 (ProofApart.mono hps ?_ ?_) <;> simp only [stackLo, x2₂] <;>
        addr_omega [hb]
    proofOut := by
      rw [x11₂, x10₂]
      refine F₂.proofApart mP₂ hS8 mQ₂ hP48 (ProofApart.mono hps ?_ ?_) <;> addr_omega [hb]
    rodata := hpre.rodata.dframe F₂ fun a ha hw ↦ by
      rcases hw with hw | hw <;> addr_omega [ha, hw, hro, hb, hpre.shuntRodata, hsh]
    outRodata := by rw [x10₂]; addr_omega [hro, hb]
    selfRodata := by rw [x11₂]; exact hpre.selfRodata }
  obtain ⟨w, hr₃, ⟨hpc₃, hpres₃, hpost₃⟩ | hd⟩ := hN.call (hr₁.trans hr₂) (b80011f14_pc h₂) hnp
  swap
  · exact ⟨_, hr₃, Or.inr hd⟩
  have hv := hpost₃.value
  have G₃ := hpost₃.frame
  rw [x10₂, x11₂] at hv G₃
  simp only [stackLo, x2₂] at G₃
  have x2w : w.getReg .x2 = s.getReg .x2 - 64 := by rw [hpres₃.reg .x2, x2₂]
  have Fw : DFrame s w (W s) := (F₂.mono fun a h ↦ by
      simp only [W]
      rcases h with h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inr (by addr_omega [h, hb]))))
      · exact Or.inr (Or.inl h)).trans G₃ fun a h ↦ by
      simp only [W]
      rcases h with h | h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inr (by addr_omega [h, hb]))))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (by addr_omega [h, hb]))))
  have slotw (y : Word) (h1 : (s.getReg .x2).toNat - 24 ≤ y.toNat)
      (h2 : y.toNat + 8 ≤ (s.getReg .x2).toNat) : w.getMem y = t₁.getMem y := by
    rw [G₃ y fun i hi h ↦ by rcases h with h | h | h <;> addr_omega [h, hi, h1, h2, hb, hss, hS],
      f₂ y (by addr_omega [h1, h2, hb, hshs, hsh])]
  have startw : w.getMem (s.getReg .x11 + 8) = s.getMem (s.getReg .x11 + 8) + 1 := by
    rw [G₃ _ fun i hi h ↦ by
      rcases h with h | h | h <;> addr_omega [h, hi, hb, hshs, hsh, hpre.shuntSelf, hS], st₂]
  obtain ⟨v₁, hr₄, h₄⟩ := Sym.BlockSpec.reaches b80011f34_spec
    (by rw [hpc₃, returnAddress_eq, b80011f14_x1 h₂]; decide) (by
      rv_eval [x2w]
      and_intros <;> valid_access hpre.stack.valid [hb])
  have k₄ := b80011f34_keeps h₄
  have hm₄ := b80011f34_mem_same h₄
  have x11₄ := b80011f34_x11 h₄
  have x12₄ := b80011f34_x12 h₄
  rw [x2w] at x11₄ x12₄
  have Iv : Inside s v₁ := ⟨by rw [k₄ .x2 (by decide), x2w],
    by rw [k₄ .x8 (by decide), hpres₃.reg .x8, k₂ .x8 (by decide), I₁.x8],
    fun r hr ↦ by rw [k₄ r (mem_of_mem hr _), hpres₃ r (mem_of_mem hr _),
      k₂ r (mem_of_mem hr _), I₁.kept r hr],
    by rw [hm₄, slotw _ (by addr_omega [hb]) (by addr_omega [hb]), I₁.ra],
    by rw [hm₄, slotw _ (by addr_omega [hb]) (by addr_omega [hb]), I₁.s0],
    by rw [hm₄, slotw _ (by addr_omega [hb]) (by addr_omega [hb]), I₁.s1]⟩
  have mB₂ : Misses (fun a ↦ Within a (s.getReg .x2 - 24) 24 ∨ Within a (s.getReg .x11 + 8) 8)
      (streamPtr s (s.getMem (s.getReg .x11))) (24 * streamLen s (s.getMem (s.getReg .x11))) := by
    rcases hself.stream with h0 | hB
    · intro y hy
      have : streamLen s (s.getMem (s.getReg .x11)) = 0 := h0
      simp only [Within] at hy; omega
    · exact miss₂ _ _ (by addr_omega [hpsh]) (by addr_omega [hps]) (by addr_omega [hB])
  have mM₂ := miss₂ (s.getMem (s.getReg .x11) + 8) 352 (by addr_omega [hpre.shuntSelf, hS])
    (by addr_omega [hss, hS]) (by addr_omega [hS])
  have a16 : s.getReg .x2 - 64 + 8 + 8 = s.getReg .x2 - 64 + 16 := by rw [BitVec.add_assoc]; rfl
  by_cases htag : w.getMem (s.getReg .x2 - 64 + 8) = 1
  · -- `Err`: into the residual
    have x9v : v₁.getReg .x9 = s.getMem (s.getReg .x11 + 24) := by
      rw [k₄ .x9 (by decide), hpres₃.reg .x9, x9₂]
    obtain ⟨v₂, hr₅, h₅⟩ := Sym.BlockSpec.reaches b80011f48_spec
      (b80011f34_pc_not_taken h₄ (by rw [x2w]; exact htag)) (by
        rv_eval [x9v]
        and_intros <;> (refine Region.valid hR ?_ ?_ ?_ <;> addr_omega [hR]))
    have k₅ := b80011f48_keeps h₅
    have m0 := b80011f48_m_x9_0 h₅
    have f₅ := b80011f48_frame h₅ (by rw [x9v]; addr_omega [hR])
    rw [x9v, x12₄] at m0
    rw [x9v] at f₅
    have kp (y : Word) (hy : ¬ Within y (s.getMem (s.getReg .x11 + 24)) 16) :
        v₂.getMem y = v₁.getMem y := f₅ y hy
    obtain ⟨t, hr₆, pc, pres, m0', f⟩ := exit hpre (b80011f48_pc h₅)
      ⟨by rw [k₅ .x2 (by decide), Iv.x2], by rw [k₅ .x8 (by decide), Iv.x8],
        fun r hr ↦ by rw [k₅ r (mem_of_mem hr _), Iv.kept r hr],
        by rw [kp _ (by addr_omega [hR, hrs, hb]), Iv.ra],
        by rw [kp _ (by addr_omega [hR, hrs, hb]), Iv.s0],
        by rw [kp _ (by addr_omega [hR, hrs, hb]), Iv.s1]⟩
    have F : DFrame s t (W s) :=
      (((Fw.trans (DFrame.of_same hm₄ _) fun _ h ↦ h).trans (DFrame.of_memFrame f₅) fun a h ↦ by
        simp only [W]; exact Or.inr (Or.inr (Or.inl h))).trans (DFrame.of_memFrame f) fun a h ↦ by
        simp only [W]; exact Or.inl (by addr_omega [h, ho]))
    refine ⟨t, ((hr₃.trans hr₄).trans hr₅).trans hr₆, Or.inl ⟨pc, pres, fun T hT ↦ ?_, F⟩⟩
    simp only [shuntP, shuntStart, shuntEnd, shuntR, hlt, ↓reduceIte]
    refine ⟨by
      rw [f _ (by addr_omega [hpre.outShunt, ho, hsh]), kp _ (by addr_omega [hpre.shuntResidual, hR, hsh]),
        hm₄, startw], ?_⟩
    have hv' := hv T (F₂.transcriptAt hT hself mP₂ mQ₂ mB₂ mM₂)
    generalize TM.nextScalar.run T = o at hv' ⊢
    rcases o with _ | ⟨x, T'⟩
    · refine ⟨by rw [m0', b80011f48_x10 h₅], ?_⟩
      rw [f _ (by addr_omega [hpre.outResidual, ho, hR]), m0, ← a16]
      exact hv'.2
    · exact absurd (hv'.1.symm.trans htag) (by decide)
  · -- `Ok`: the value out
    obtain ⟨v₂, hr₅, h₅⟩ := Sym.BlockSpec.reaches b80011f60_spec
      (b80011f34_pc_taken h₄ (by rw [x2w]; exact htag)) (by
        rv_eval [Iv.x8, Iv.x2]
        and_intros <;> first
          | valid_access hpre.stack.valid [hb]
          | (refine Region.valid ho ?_ ?_ ?_ <;> addr_omega [ho]))
    have k₅ := b80011f60_keeps h₅
    have m8 := b80011f60_m_x8_8 h₅
    have m16 := b80011f60_m_x8_16 h₅
    have m24 := b80011f60_m_x8_24 h₅
    have f₅ := b80011f60_frame h₅ (by rw [Iv.x8]; addr_omega [ho])
    rw [Iv.x8, x12₄] at m8
    rw [Iv.x8, x11₄] at m16
    rw [Iv.x8, Iv.x2, hm₄] at m24
    rw [Iv.x8] at f₅
    have kp (y : Word) (hy : ¬ Within y (s.getReg .x10 + 8) 24) : v₂.getMem y = v₁.getMem y :=
      f₅ y hy
    obtain ⟨t, hr₆, pc, pres, m0', f⟩ := exit hpre (b80011f60_pc h₅)
      ⟨by rw [k₅ .x2 (by decide), Iv.x2], by rw [k₅ .x8 (by decide), Iv.x8],
        fun r hr ↦ by rw [k₅ r (mem_of_mem hr _), Iv.kept r hr],
        by rw [kp _ (by addr_omega [ho, hos, hb]), Iv.ra],
        by rw [kp _ (by addr_omega [ho, hos, hb]), Iv.s0],
        by rw [kp _ (by addr_omega [ho, hos, hb]), Iv.s1]⟩
    have Fwt : DFrame w t (Within · (s.getReg .x10) 32) :=
      (((DFrame.of_same hm₄ _).trans (DFrame.of_memFrame f₅) fun a h ↦ by addr_omega [h, ho]).trans
        (DFrame.of_memFrame f) fun a h ↦ by addr_omega [h, ho])
    have F : DFrame s t (W s) :=
      Fw.trans Fwt fun a h ↦ by simp only [W]; exact Or.inl h
    refine ⟨t, ((hr₃.trans hr₄).trans hr₅).trans hr₆, Or.inl ⟨pc, pres, fun T hT ↦ ?_, F⟩⟩
    simp only [shuntP, shuntStart, shuntEnd, shuntR, hlt, ↓reduceIte]
    refine ⟨by rw [Fwt _ fun i hi h ↦ by addr_omega [h, hi, hpre.outShunt, ho, hsh], startw], ?_⟩
    have hv' := hv T (F₂.transcriptAt hT hself mP₂ mQ₂ mB₂ mM₂)
    generalize TM.nextScalar.run T = o at hv' ⊢
    rcases o with _ | ⟨x, T'⟩
    · exact absurd hv'.1 htag
    · obtain ⟨-, hx, hT'⟩ := hv'
      have o16 : s.getReg .x10 + 8 + 8 = s.getReg .x10 + 16 := by rw [BitVec.add_assoc]; rfl
      have o24 : s.getReg .x10 + 8 + 16 = s.getReg .x10 + 24 := by rw [BitVec.add_assoc]; rfl
      refine ⟨by rw [m0', k₅ .x10 (by decide), b80011f34_x10 h₄], ?_, ?_⟩
      · rw [← hx]
        unfold Rv64Verifier.eAt
        have b24 : s.getReg .x2 - 64 + 16 + 8 = s.getReg .x2 - 64 + 24 := by
          rw [BitVec.add_assoc]; rfl
        have b32 : s.getReg .x2 - 64 + 16 + 16 = s.getReg .x2 - 64 + 32 := by
          rw [BitVec.add_assoc]; rfl
        rw [o16, o24, a16, b24, b32, f _ (by addr_omega [ho]), f _ (by addr_omega [ho]),
          f _ (by addr_omega [ho]), m8, m16, m24]
      · have hokw := G₃.transcriptOk hok₂
          (fun y hy h ↦ by rcases h with h | h | h <;> addr_omega [hy, h, hb, hss, hS])
          (fun y hy h ↦ by
            obtain ⟨e0, -, -⟩ := F₂.stream' mP₂ hS8 mQ₂ hP48
            rw [e0] at hy
            rcases h with h | h | h <;> addr_omega [hy, h, hb, hps, hself.apart, hP])
        obtain ⟨e0, e1, e2⟩ := Fw.stream' mP hS8 mQ hP48
        have mo (lo : Word) (n : Nat) (h0 : Apart lo n (s.getReg .x10) 32)
            (hn : lo.toNat + n ≤ 2 ^ 64) : Misses (Within · (s.getReg .x10) 32) lo n :=
          fun y hy h ↦ by addr_omega [hy, h, h0, hn]
        refine Fwt.transcriptAt hT' hokw (mo _ _ (by addr_omega [hpre.outSelf]) hS8)
          (by rw [e0]; exact mo _ _ (by addr_omega [hpo]) hP48) ?_
          (mo _ _ (by addr_omega [hpre.outSelf, hS]) (by addr_omega [hS]))
        rw [e1, e2]
        rcases hself.stream with h0 | hB
        · intro y hy
          have : streamLen s (s.getMem (s.getReg .x11)) = 0 := h0
          simp only [Within] at hy; omega
        · exact mo _ _ (by addr_omega [hpo]) (by addr_omega [hB])

end Rv64Verifier.Transcript.ShuntNext
