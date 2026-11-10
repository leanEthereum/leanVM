import Rv64Verifier.Proofs.Pcs.VsoFold
import Rv64Verifier.Proofs.Pcs.VsoCalls

/-!
# `verify_stacked_opening`'s level loop: a fold round's challenge

`0x8000a1e8` calls `duplex`; `0x8000a1fc` copies the challenge's lanes to `S - 128` and compares
the folds' length with their capacity.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- After round `j`'s challenge `c` (at `S - 128`): at `0x8000a228` with room in `folds`, or at
`0x8000a21c` to grow it. -/
structure Smp (s : MachineState) (x : LCtx) (h u : MachineState) (ℓ : ℕ)
    (Wl : Model.Pcs.WhirLocals) (j : ℕ) (lf q : List E) (c : E) : Prop
    extends RB s x h u ℓ Wl (Wl.folds ++ lf) lf q where
  pc : (u.pc = 0x8000a228 ∧ Wl.folds.length + j < (vecCap u (s.getReg .x2 - 688)).toNat) ∨
    (u.pc = 0x8000a21c ∧ Wl.folds.length + j = (vecCap u (s.getReg .x2 - 688)).toNat)
  x8 : u.getReg .x8 = BitVec.ofNat 64 (Wl.folds.length + j)
  x19 : u.getReg .x19 = vecPtr u (s.getReg .x2 - 640)
  x20 : u.getReg .x20 = BitVec.ofNat 64 (24 * j)
  x21 : u.getReg .x21 = BitVec.ofNat 64 j
  x24 : u.getReg .x24 = BitVec.ofNat 64 Wl.folds.length
  jlt : j < fcOf s ℓ
  lfl : lf.length = j
  chal : eAt u (s.getReg .x2 - 128) = c
  value : Runs s u ℓ (Model.Pcs.roundK Wl lf q (fcOf s ℓ - (j + 1)) (AFk s x ℓ) c)

theorem rnd_sample (hD : DuplexSpec) {s : MachineState} {x : LCtx} {h u : MachineState} {ℓ : ℕ}
    {Wl : Model.Pcs.WhirLocals} {j : ℕ} {lf q : List E} (hpre : VsoPre s)
    (hr : Rnd s x h u ℓ Wl j lf q) :
    ∃ v, Reaches Image.code u v ∧ (Dead Image.code v ∨ ∃ c, Smp s x h v ℓ Wl j lf q c) := by
  have hb := bounds hpre
  have hst := hpre.stack
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hI := hpre.self
  have hS := Region.bounds hI.ok.self
  have hIs := hI.stack
  rw [stackLo_vso, vso_stack] at hIs
  have hf := hr.head.facts
  have hB := hr.bufs
  have hsp := hr.sp
  have inv := FW.inv hpre hr.head hr.fr hr.heap hr.mono (hsp.trans hr.head.sp.symm)
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000a1e8_spec hr.pc trivial
  have k₁ := b8000a1e8_keeps h₁
  have hm₁ := b8000a1e8_mem_same h₁
  have inv₁ : InvR s t₁ (t₁.getMem nextAddr) := by
    rw [hm₁]; exact Inv.same' inv hm₁ (k₁ .x2 (by decide))
  obtain ⟨t₂, hr₂, hv₂⟩ := callDuplex hD hpre inv₁ (b8000a1e8_pc h₁)
    (by rw [b8000a1e8_x10 h₁, hr.x25])
  rcases hv₂ with hd | ⟨hpc₂, hpres₂, X₂, hsp₂⟩
  · exact ⟨t₂, hr₁.trans hr₂, Or.inl hd⟩
  have sp₂ : t₂.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := by
    rw [hpres₂ .x2 (by decide), k₁ .x2 (by decide), hsp]
  have x27₂ : t₂.getReg .x27 = s.getReg .x10 := by
    rw [hpres₂ .x27 (by decide), k₁ .x27 (by decide), hr.x27]
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000a1fc_spec
    (by rw [hpc₂, returnAddress_eq, b8000a1e8_x1 h₁]; decide) (by
      rv_eval [sp₂, x27₂]
      and_intros <;> first
        | valid_access hst.valid [hb]
        | exact Region.valid hI.ok.self (by addr_omega [hS]) (by addr_omega [hS]) (by addr_omega [hS]))
  have k₃ := b8000a1fc_keeps h₃
  have X₃ : DFrame t₂ t₃ fun a ↦ Within a (s.getReg .x2 - 128) 24 := by
    have := DFrame.of_memFrame (b8000a1fc_frame h₃ (by rw [sp₂]; addr_omega [hb]))
    rw [sp₂] at this
    exact this.mono fun a ha ↦ by addr_omega [ha, hb]
  have X : DFrame u t₃ fun a ↦ Within a (s.getReg .x10 + 8) 336 ∨
      Within a (s.getReg .x2 - 1920) 880 ∨ Within a (s.getReg .x2 - 128) 24 :=
    ((DFrame.of_same hm₁ _).trans X₂ fun a ha ↦ by
      rcases ha with ha | ha
      · exact Or.inl ha
      · exact Or.inr (Or.inl ha)).trans X₃ fun a ha ↦ Or.inr (Or.inr ha)
  have hfree := hI.free
  simp only [Outside] at hfree
  have hhu := hr.heap.hi
  have hLs := hf.hs
  have nx : t₃.getMem nextAddr = u.getMem nextAddr := X _ fun i hi hw ↦ by
    rcases hw with hw | hw | hw
    · addr_omega [hw, hi, hfree.2, hS]
    · addr_omega [hw, hi, hb, hnx]
    · addr_omega [hw, hi, hb, hnx]
  have hn : heapNext t₃ = heapNext u := by simp only [heapNext, nx]
  have hRB := RB.carry hpre hr.toRB X (fun a ha ↦ by
      rcases ha with ha | ha | ha
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          (by simp only [W]; addr_omega [ha, hS])))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb]))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb]))))))
    (fun a ha ↦ by
      refine ⟨fun hs ↦ ?_, fun hs ↦ ?_⟩
      · simp only [RSlots] at hs
        rcases ha with ha | ha | ha <;> rcases hs with hs | hs | hs | hs | hs <;>
          addr_omega [ha, hs, hb, hIs, hS]
      · simp only [RBufs] at hs
        rcases ha with ha | ha | ha
        · rcases hfree.1 with h0 | h0
          · rcases hs with hs | hs | hs
            · rcases hB.F with h1 | h1
              · simp only [Within] at hs; omega
              · addr_omega [ha, hs, h0, h1.1, hLs]
            · rcases hB.LF with h1 | h1
              · simp only [Within] at hs; omega
              · addr_omega [ha, hs, h0, h1.1, hLs]
            · rcases hB.Q with h1 | h1
              · simp only [Within] at hs; omega
              · addr_omega [ha, hs, h0, h1.1, hLs]
          · rcases hs with hs | hs | hs
            · rcases hB.F with h1 | h1
              · simp only [Within] at hs; omega
              · addr_omega [ha, hs, h0, h1.2, hhu, hS]
            · rcases hB.LF with h1 | h1
              · simp only [Within] at hs; omega
              · addr_omega [ha, hs, h0, h1.2, hhu, hS]
            · rcases hB.Q with h1 | h1
              · simp only [Within] at hs; omega
              · addr_omega [ha, hs, h0, h1.2, hhu, hS]
        · rcases hs with hs | hs | hs
          · rcases hB.F with h1 | h1
            · simp only [Within] at hs; omega
            · addr_omega [ha, hs, hb, h1.2, hhu]
          · rcases hB.LF with h1 | h1
            · simp only [Within] at hs; omega
            · addr_omega [ha, hs, hb, h1.2, hhu]
          · rcases hB.Q with h1 | h1
            · simp only [Within] at hs; omega
            · addr_omega [ha, hs, hb, h1.2, hhu]
        · rcases hs with hs | hs | hs
          · rcases hB.F with h1 | h1
            · simp only [Within] at hs; omega
            · addr_omega [ha, hs, hb, h1.2, hhu]
          · rcases hB.LF with h1 | h1
            · simp only [Within] at hs; omega
            · addr_omega [ha, hs, hb, h1.2, hhu]
          · rcases hB.Q with h1 | h1
            · simp only [Within] at hs; omega
            · addr_omega [ha, hs, hb, h1.2, hhu])
    ⟨by rw [hn]; exact hr.heap.lo, by rw [hn]; exact hhu⟩ (by rw [hn])
    (fun r hr' ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        rw [k₃ _ (by decide), hpres₂ _ (by decide), k₁ _ (by decide)])
  have hrst := hpre.root.stack
  rw [stackLo_vso, vso_stack] at hrst
  have hrsp := hpre.rootSponge
  have inv₂ : InvR s t₂ (t₂.getMem nextAddr) := by
    have nx₂ : t₂.getMem nextAddr = t₁.getMem nextAddr := X₂ _ fun i hi hw ↦ by
      rcases hw with hw | hw
      · addr_omega [hw, hi, hfree.2, hS]
      · addr_omega [hw, hi, hb, hnx]
    refine Inv.step' hpre inv₁ X₂ (fun a ha ↦ ?_) (fun a ha ↦ ?_) rfl (by rw [nx₂])
      (by rw [nx₂]; exact inv₁.fits) (hpres₂ .x2 (by decide))
    · rcases ha with ha | ha
      · exact Or.inl (Or.inl (by simp only [W]; addr_omega [ha, hS]))
      · exact Or.inr (Or.inl (in_stack hpre (by addr_omega [ha, hb])))
    · rcases ha with ha | ha
      · addr_omega [ha, hIs, hS, hb]
      · addr_omega [ha, hb]
  have hval : Runs s t₃ ℓ (Model.Pcs.roundK Wl lf q (fcOf s ℓ - (j + 1)) (AFk s x ℓ)
      (eAt t₃ (s.getReg .x2 - 128))) := by
    have hv := hr.value
    rw [show fcOf s ℓ - j = fcOf s ℓ - (j + 1) + 1 by have := hr.jlt; omega,
      Model.Pcs.loopN_fold_succ] at hv
    refine hv.step (digest_keep X (root_bound hpre) fun y hy hw ↦ ?_) fun T hT ↦ ?_
    · rcases hw with hw | hw | hw
      · addr_omega [hy, hw, hrsp]
      · addr_omega [hy, hw, hrst, hb]
      · addr_omega [hy, hw, hrst, hb]
    · have hT₁ : TranscriptAt t₁ (s.getReg .x10) T :=
        tr_keep hpre inv hT (DFrame.of_same hm₁ (fun _ ↦ False)) (fun _ h ↦ h.elim)
      have hT₂ := tr_duplex hpre inv₁ hT₁ X₂ hsp₂
      have hT₃ := tr_keep hpre inv₂ hT₂ X₃ (fun a ha ↦ Or.inl (by addr_omega [ha, hb]))
      have hc : (spSqueeze T.sponge).1 = eAt t₃ (s.getReg .x2 - 128) := by
        have hsq : (spSqueeze T.sponge).1 = Compile.challengeOf (spDuplex T.sponge).state := rfl
        rw [hsq, ← hT₁.sponge, ← hsp₂]
        show Compile.challengeOf (stateAt t₂ (s.getReg .x10 + 8 + 128)) = _
        rw [Samples.challengeOf_stateAt]
        have m0 := b8000a1fc_m_x2_912 h₃
        have m1 := b8000a1fc_m_x2_920 h₃
        have m2 := b8000a1fc_m_x2_928 h₃
        rw [sp₂, x27₂] at m0 m1 m2
        rv_eval [] at m0 m1 m2
        unfold eAt
        rv_eval [m0, m1, m2]
      refine ⟨{ T with sponge := spDuplex T.sponge }, ?_, hT₃, rfl, rfl, rfl⟩
      rw [run_bind_of (show (Model.TM.sample).run T =
        some ((spSqueeze T.sponge).1, { T with sponge := spDuplex T.sponge }) from rfl), hc]
  -- the folds' header, kept
  have kh (y : Word) (h1 : (s.getReg .x2 - 688).toNat ≤ y.toNat)
      (h2 : y.toNat + 8 ≤ (s.getReg .x2 - 616).toNat) : t₃.getMem y = u.getMem y :=
    X y fun i hi hw ↦ by
      rcases hw with hw | hw | hw
      · addr_omega [hw, hi, h1, h2, hIs, hS, hb]
      · addr_omega [hw, hi, h1, h2, hb]
      · addr_omega [hw, hi, h1, h2, hb]
  have hFl : (vecLen u (s.getReg .x2 - 688)).toNat = Wl.folds.length + j := by
    have := congrArg List.length hr.F.2.1
    rw [vecEs, eListAt_length, List.length_append, hr.lfl] at this; exact this
  have hFc : vecCap t₃ (s.getReg .x2 - 688) = vecCap u (s.getReg .x2 - 688) :=
    kh _ (by addr_omega [hb]) (by addr_omega [hb])
  have hLp : vecPtr t₃ (s.getReg .x2 - 640) = vecPtr u (s.getReg .x2 - 640) :=
    kh _ (by addr_omega [hb]) (by addr_omega [hb])
  have hlc := hr.F.1.len
  have hsm := vec_small hr.F.1 hr.heap
  have x8₂ : t₂.getReg .x8 = BitVec.ofNat 64 (Wl.folds.length + j) := by
    rw [hpres₂ .x8 (by decide), b8000a1e8_x8 h₁, hr.x6, hr.x21, BitVec.ofNat_add]
  have hcap₂ : t₂.getMem (t₂.getReg .x2 + 352) = vecCap u (s.getReg .x2 - 688) := by
    rw [← hFc, sp₂]
    have : t₃.getMem (s.getReg .x2 - 688) = t₂.getMem (s.getReg .x2 - 688) :=
      X₃ _ fun i hi hw ↦ by addr_omega [hw, hi, hb]
    simp only [vecCap]; rw [this]; rv_eval []
  refine ⟨t₃, hr₁.trans (hr₂.trans hr₃), Or.inr ⟨eAt t₃ (s.getReg .x2 - 128), {
    toRB := hRB
    pc := by
      by_cases he : Wl.folds.length + j = (vecCap t₃ (s.getReg .x2 - 688)).toNat
      · exact Or.inr ⟨b8000a1fc_pc_not_taken h₃ (by
          rw [x8₂, hcap₂, ← hFc]; addr_omega [he, hsm, hlc, hFl]), he⟩
      · exact Or.inl ⟨b8000a1fc_pc_taken h₃ (by
          rw [x8₂, hcap₂, ← hFc]; intro he'; exact he (by addr_omega [he', hsm, hlc, hFl])),
          by rw [hFc] at he ⊢; omega⟩
    x8 := by rw [k₃ .x8 (by decide), x8₂]
    x19 := by rw [k₃ .x19 (by decide), hpres₂ .x19 (by decide), k₁ .x19 (by decide), hr.x19, hLp]
    x20 := by rw [k₃ .x20 (by decide), hpres₂ .x20 (by decide), k₁ .x20 (by decide), hr.x20]
    x21 := by rw [k₃ .x21 (by decide), hpres₂ .x21 (by decide), k₁ .x21 (by decide), hr.x21]
    x24 := by rw [k₃ .x24 (by decide), hpres₂ .x24 (by decide), b8000a1e8_x24 h₁, hr.x6]
    jlt := hr.jlt
    lfl := hr.lfl
    chal := rfl
    value := hval }⟩⟩

end Rv64Verifier.Proofs.Pcs.Vso
