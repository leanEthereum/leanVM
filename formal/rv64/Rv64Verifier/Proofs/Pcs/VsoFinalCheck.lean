import Rv64Verifier.Proofs.Pcs.VsoFinalEnd

/-!
# `verify_stacked_opening`'s final level: the terminal check, run

`check`: from `TC` (`0x8000bfe8`) to `Ok` or an `Err`. What it writes from `TC`'s state `u` on is
`YW`: the frame below the saved registers, the callees' stacks, `NEXT` and the heap allocated.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- What the tail writes from `u` on, `NEXT` below `hi`. -/
@[rv_addr] def YW (s u : MachineState) (hi : ℕ) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 2464) 2360 ∨ Within a nextAddr 8 ∨ (heapNext u ≤ a.toNat ∧ a.toNat < hi)

theorem YW.inv {s u v : MachineState} {hi : ℕ} (hpre : VsoPre s)
    (h : InvR s u (u.getMem nextAddr)) (hX : DFrame u v (YW s u hi))
    (hle : heapNext u ≤ heapNext v) (hhi : hi ≤ heapNext v) (hend : heapNext v ≤ heapEnd)
    (hsp : v.getReg .x2 = u.getReg .x2) : InvR s v (v.getMem nextAddr) := by
  have hb := bounds hpre
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hab := hpre.stack.above
  rw [stackLo_vso] at hab
  have hm := h.mono
  refine Inv.step' hpre h hX (fun a ha ↦ ?_) (fun a ha ↦ ?_) rfl hle hend hsp
  · rcases ha with ha | ha | ha
    · exact Or.inr (Or.inl (in_stack hpre (by addr_omega [ha, hb])))
    · exact Or.inr (Or.inr (Or.inl ha))
    · exact Or.inr (Or.inr (Or.inr ⟨Nat.le_trans hm ha.1, Nat.lt_of_lt_of_le ha.2 hhi⟩))
  · rcases ha with ha | ha | ha
    · addr_omega [ha, hb]
    · addr_omega [ha, hb, hnx]
    · simp only [heapEnd] at hend hab; addr_omega [ha.2, hhi, hend, hab, hb]

theorem YW.ns {s u : MachineState} {hi : ℕ} (hpre : VsoPre s) (h : InvR s u (u.getMem nextAddr))
    (hend : hi ≤ heapEnd) {a : Word} (ha : YW s u hi a) : NS s a := by
  have hb := bounds hpre
  rcases ha with ha | ha | ha
  · exact Or.inl (by addr_omega [ha, hb])
  · exact Or.inr (Or.inl ha)
  · exact Or.inr (Or.inr (Or.inl ⟨Nat.le_trans h.mono ha.1, by omega⟩))

theorem c048_x10 {s t : MachineState} (h : b8000c048.Holds s t) :
    t.getReg .x10 = ((if BitVec.ult 0 (((s.getMem (s.getReg .x2 + 576) ^^^
      s.getMem (s.getReg .x2 + 136)) ||| (s.getMem (s.getReg .x2 + 584) ^^^
      s.getMem (s.getReg .x2 + 120))) ||| (s.getMem (s.getReg .x2 + 592) ^^^
      s.getMem (s.getReg .x2 + 176))) then (1 : Word) else 0) - 1) ||| 18 :=
  h.reg_eq .x10 rfl (by rv_eval []; rfl)

theorem eAt_limbs (u : MachineState) (B : Word) (k : ℕ) (_hk : k + 16 < 2 ^ 64) :
    eAt u (B + BitVec.ofNat 64 k) = E.ofLimbs (BF64.ofBitVec (u.getMem (B + BitVec.ofNat 64 k)))
      (BF64.ofBitVec (u.getMem (B + BitVec.ofNat 64 (k + 8))))
      (BF64.ofBitVec (u.getMem (B + BitVec.ofNat 64 (k + 16)))) := by
  unfold Rv64Verifier.eAt
  rw [BitVec.add_assoc, BitVec.add_assoc, show BitVec.ofNat 64 k + 8 = BitVec.ofNat 64 (k + 8) by
    rw [BitVec.ofNat_add]; rfl, show BitVec.ofNat 64 k + 16 = BitVec.ofNat 64 (k + 16) by
    rw [BitVec.ofNat_add]; rfl]

/-- **The terminal check**: to `Ok` when the mirror's check holds, or an `Err`. -/
theorem check (hMle : MultilinearContracts.MleEvalSpec) (hM : MulSpec)
    {OA : MachineState → Word → Model.TState → Prop} {s u : MachineState} {ml : ℕ}
    {residual tf : List E} {w rt : E} (hpre : VsoPre s) (h : TC OA s u ml residual tf w rt) :
    ∃ v, Reaches Image.code u v ∧ (FailR s v ∨ OkR OA s v) := by
  have hb := bounds hpre
  have hst := hpre.stack
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hsp : u.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := h.inv.sp
  have hu := h.heap
  have hus : heapNext s ≤ heapNext u := h.inv.mono
  have hhu := hu.hi
  have hab := hst.above
  rw [stackLo_vso] at hab
  generalize hB : u.getReg .x2 = B at hsp
  -- the residual's value
  have htl : tf.length = ml := by rw [← h.tail.1, eListAt_length]
  obtain ⟨rv, hmle⟩ : ∃ rv, Model.multilinearEvalRust residual tf = some rv :=
    ⟨_, Model.multilinearEvalRust_eq _ _ ⟨by rw [htl]; exact h.ml64, by rw [h.rlen, htl]⟩⟩
  -- `0x8000bfe8`
  obtain ⟨t₁, r₁, h₁⟩ := Sym.BlockSpec.reaches b8000bfe8_spec h.pc (by
    rv_eval [hB, hsp]; and_intros <;> valid_access hst.valid [hb])
  have m₁ := b8000bfe8_mem_same h₁
  have k₁ := b8000bfe8_keeps h₁
  have sp₁ : t₁.getReg .x2 = B := by rw [k₁ .x2 (by decide), hB]
  have inv₁ : InvR s t₁ (t₁.getMem nextAddr) := by
    rw [m₁]; exact Inv.same' h.inv m₁ (k₁ .x2 (by decide))
  have hn₁ : heapNext t₁ = heapNext u := by simp only [heapNext, m₁]
  have hl₁ (p : Word) (n : ℕ) : eListAt t₁ p n = eListAt u p n := by
    simp only [Rv64Verifier.eListAt, Rv64Verifier.eAt, m₁]
  have a72 : B + 72 = s.getReg .x2 - 968 := by rw [hsp]; addr_omega [hb]
  have a80 : B + 80 = s.getReg .x2 - 960 := by rw [hsp]; addr_omega [hb]
  have hres := h.res
  have htail := h.tail
  rw [← hB] at a72 a80
  have hx11 : t₁.getReg .x11 = u.getMem (s.getReg .x2 - 968) := by rw [b8000bfe8_x11 h₁, a72]
  have hx12 : t₁.getReg .x12 = u.getMem (s.getReg .x2 - 960) := by rw [b8000bfe8_x12 h₁, a80]
  have hx14 : (t₁.getReg .x14).toNat = ml := by
    rw [b8000bfe8_x14 h₁, h.x19, BitVec.toNat_ofNat]; have := h.ml64; omega
  -- `multilinear_eval`
  obtain ⟨t₂, r₂, h₂⟩ := callMle hMle (o := B + 656) hpre inv₁ ⟨by rw [hn₁]; exact hu.lo,
      by rw [hn₁]; exact hhu⟩ (b8000bfe8_pc h₁) (by rw [b8000bfe8_x10 h₁, hB]) hx11 hx12
    (b8000bfe8_x13 h₁) rfl (by rw [hsp]; addr_omega [hb])
    (by
      rw [hn₁]
      rcases hres.2.2 with h0 | h0
      · exact Or.inl h0
      · exact Or.inr ⟨Nat.le_trans hpre.heap.lo h0.1, h0.2⟩) hres.2.1
    (by
      rw [hn₁, hx14]
      rcases htail.2.2 with h0 | h0
      · exact Or.inl h0
      · exact Or.inr ⟨Nat.le_trans hpre.heap.lo h0.1, h0.2⟩)
    htail.2.1
    (by rw [hl₁, hl₁, hx14, htail.1, hres.1]; exact hmle)
  rcases h₂ with hd | ⟨hpc₂, hpres₂, hheap₂, hmono₂, X₂, tag₂, val₂⟩
  · exact ⟨t₂, r₁.trans r₂, Or.inl (Or.inl hd)⟩
  have sp₂ : t₂.getReg .x2 = B := by rw [hpres₂ .x2 (by decide), sp₁]
  have hhi₂ := hheap₂.hi
  -- `0x8000c004`: no `Err`
  obtain ⟨t₃, r₃, h₃⟩ := Sym.BlockSpec.reaches b8000c004_spec
    (by rw [hpc₂, returnAddress_eq, b8000bfe8_x1 h₁]; decide) (by
      rv_eval [sp₂, hsp]; and_intros <;> valid_access hst.valid [hb])
  have pc₃ := b8000c004_pc_not_taken h₃ (by rw [sp₂]; exact tag₂)
  have F₃ : DFrame t₂ t₃ fun a ↦ Within a (B + 144) 8 ∨ Within a (B + 232) 8 :=
    (holds_dframe h₃).mono fun a ⟨k, hk, hw⟩ ↦ by
      simp only [b8000c004, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl <;> rv_eval [sp₂] at hw
      all_goals first
        | exact Or.inl (by addr_omega [hw, hb, hsp])
        | exact Or.inr (by addr_omega [hw, hb, hsp])
  have k₃ := b8000c004_keeps h₃
  have sp₃ : t₃.getReg .x2 = B := by rw [k₃ .x2 (by decide), sp₂]
  -- `0x8000c01c`: the value to `B + 656`, `mul`
  obtain ⟨t₄, r₄, h₄⟩ := Sym.BlockSpec.reaches b8000c01c_spec pc₃ (by
      rv_eval [sp₃, hsp]; and_intros <;> valid_access hst.valid [hb])
  have F₄ := DFrame.of_memFrame (b8000c01c_frame h₄ (by rw [sp₃, hsp]; addr_omega [hb]))
  have k₄ := b8000c01c_keeps h₄
  have sp₄ : t₄.getReg .x2 = B := by rw [k₄ .x2 (by decide), sp₃]
  rw [sp₃] at F₄
  -- the frame so far
  have Y₄ : DFrame u t₄ (YW s u (heapNext t₂)) := by
    refine DFrame.trans (DFrame.trans (DFrame.trans (DFrame.of_same m₁ _) X₂ ?_) F₃ ?_) F₄ ?_
    · intro a ha
      rcases ha with ha | ha | ha | ha
      · exact Or.inl (by rw [hsp] at ha; addr_omega [ha, hb])
      · exact Or.inl (by addr_omega [ha, hb])
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr ⟨by rw [← hn₁]; exact ha.1, ha.2⟩)
    · intro a ha; rcases ha with ha | ha <;> exact Or.inl (by rw [hsp] at ha; addr_omega [ha, hb])
    · intro a ha; exact Or.inl (by rw [hsp] at ha; addr_omega [ha, hb])
  have nx₄ : t₄.getMem nextAddr = t₂.getMem nextAddr := by
    rw [F₄ _ fun i hi hw ↦ by rw [hsp] at hw; addr_omega [hw, hi, hb, hnx],
      F₃ _ fun i hi hw ↦ by rcases hw with hw | hw <;> (rw [hsp] at hw; addr_omega [hw, hi, hb, hnx])]
  have hn₄ : heapNext t₄ = heapNext t₂ := by simp only [heapNext, nx₄]
  have inv₄ : InvR s t₄ (t₄.getMem nextAddr) := YW.inv hpre h.inv Y₄
    (by rw [hn₄, ← hn₁]; exact hmono₂) (by rw [hn₄]) (by rw [hn₄]; exact hhi₂) (by rw [sp₄, hB])
  -- the value and the weight at `mul`
  have v₄ : eAt t₄ (B + 656) = rv := by
    rw [← val₂, show B + 656 + 8 = B + BitVec.ofNat 64 664 from by rw [BitVec.add_assoc]; rfl,
      eAt_limbs t₂ B 664 (by decide), show B + 656 = B + BitVec.ofNat 64 656 from rfl,
      eAt_limbs t₄ B 656 (by decide)]
    have e1 := b8000c01c_m_x2_656 h₄
    have e2 := b8000c01c_m_x2_664 h₄
    have e3 := b8000c01c_m_x2_672 h₄
    have e4 := b8000c004_m_x2_144 h₃
    have e5 := b8000c004_m_x2_232 h₃
    have e6 : t₃.getMem (B + 680) = t₂.getMem (B + 680) :=
      F₃ _ fun i hi hw ↦ by rcases hw with hw | hw <;> (rw [hsp] at hw; addr_omega [hw, hi, hb])
    rw [sp₃] at e1 e2 e3
    rw [sp₂] at e4 e5
    simp only [Nat.reduceAdd]
    rw [show B + BitVec.ofNat 64 656 = B + 656 from rfl, show B + BitVec.ofNat 64 664 = B + 664 from rfl,
      show B + BitVec.ofNat 64 672 = B + 672 from rfl, show B + BitVec.ofNat 64 680 = B + 680 from rfl,
      e1, e2, e3, e4, e5, e6]
  have w₄ : eAt t₄ (B + 856) = w := by
    have e₁ : eAt t₁ (B + 856) = eAt u (B + 856) := by simp only [Rv64Verifier.eAt, m₁]
    rw [F₄.eAt fun i hi hw ↦ by rw [hsp] at hw; addr_omega [hw, hi, hb],
      F₃.eAt fun i hi hw ↦ by rcases hw with hw | hw <;> (rw [hsp] at hw; addr_omega [hw, hi, hb]),
      X₂.eAt fun i hi hw ↦ by
        rcases hw with hw | hw | hw | hw
        · rw [hsp] at hw; addr_omega [hw, hi, hb]
        · addr_omega [hw, hi, hb, hsp]
        · addr_omega [hw, hi, hb, hnx, hsp]
        · simp only [Fresh, heapEnd] at hw hhi₂ hab; addr_omega [hw.1, hw.2, hi, hb, hab, hhi₂, hsp],
      e₁, ← h.wt, show B + 856 = s.getReg .x2 - 184 by rw [hsp]; addr_omega [hb]]
  obtain ⟨t₅, r₅, h₅⟩ := callMul hM (o := B + 576) (a := B + 856) (b := B + 656) hpre inv₄
    (b8000c01c_pc h₄) (by rw [b8000c01c_x10 h₄, sp₃]) (by rw [b8000c01c_x11 h₄, sp₃])
    (by rw [b8000c01c_x12 h₄, sp₃]) (by rw [hsp]; addr_omega [hb]) (by rw [hsp]; addr_omega [hb])
    (by rw [hsp]; addr_omega [hb]) (by rw [hsp]; addr_omega [hb]) (by rw [hsp]; addr_omega [hb])
  rcases h₅ with hd | ⟨hpc₅, hpres₅, X₅, val₅⟩
  · exact ⟨t₅, r₁.trans (r₂.trans (r₃.trans (r₄.trans r₅))), Or.inl (Or.inl hd)⟩
  have sp₅ : t₅.getReg .x2 = B := by rw [hpres₅ .x2 (by decide), sp₄]
  rw [w₄, v₄] at val₅
  have Y₅ : DFrame u t₅ (YW s u (heapNext t₂)) := DFrame.trans Y₄ X₅ fun a ha ↦ by
    rcases ha with ha | ha <;> exact Or.inl (by (try rw [hsp] at ha); addr_omega [ha, hb])
  -- `0x8000c048`, `0x8000c080`, `0x8000c084`
  obtain ⟨t₆, r₆, h₆⟩ := Sym.BlockSpec.reaches b8000c048_spec
    (by rw [hpc₅, returnAddress_eq, b8000c01c_x1 h₄]; decide) (by
      rv_eval [sp₅, hsp]; and_intros <;> valid_access hst.valid [hb])
  have x10₆ := c048_x10 h₆
  have m₆ := b8000c048_mem_same h₆
  have sp₆ : t₆.getReg .x2 = B := by rw [b8000c048_keeps h₆ .x2 (by decide), sp₅]
  obtain ⟨t₇, r₇, h₇⟩ := Sym.BlockSpec.reaches b8000c080_spec (b8000c048_pc h₆) (by
      rv_eval [sp₆, hsp]; valid_access hst.valid [hb])
  have F₇ := DFrame.of_memFrame (b8000c080_frame h₇ (by rw [sp₆, hsp]; addr_omega [hb]))
  have sp₇ : t₇.getReg .x2 = B := by rw [b8000c080_keeps h₇ .x2 (by decide), sp₆]
  obtain ⟨t₈, r₈, h₈⟩ := Sym.BlockSpec.reaches b8000c084_spec (b8000c080_pc h₇) (by
      rv_eval [sp₇, hsp]; and_intros <;> valid_access hst.valid [hb])
  have x1₈ : t₈.getReg .x1 = t₆.getReg .x10 := by
    rw [b8000c084_x1 h₈, sp₇, ← sp₆, b8000c080_m_x2_144 h₇]
  have m₈ := b8000c084_mem_same h₈
  have sp₈ : t₈.getReg .x2 = B := by rw [b8000c084_keeps h₈ .x2 (by decide), sp₇]
  rw [sp₆] at F₇
  have Y₈ : DFrame u t₈ (YW s u (heapNext t₂)) :=
    DFrame.trans (DFrame.trans (DFrame.trans Y₅ (DFrame.of_same m₆ fun _ ↦ False) fun _ h ↦ False.elim h)
      F₇ fun a ha ↦ Or.inl (by rw [hsp] at ha; addr_omega [ha, hb]))
      (DFrame.of_same m₈ fun _ ↦ False) fun _ h ↦ False.elim h
  have nx₈ : t₈.getMem nextAddr = t₂.getMem nextAddr := by
    rw [m₈, F₇ _ fun i hi hw ↦ by rw [hsp] at hw; addr_omega [hw, hi, hb, hnx], m₆,
      X₅ _ fun i hi hw ↦ by rcases hw with hw | hw <;> (try rw [hsp] at hw); all_goals addr_omega [hw, hi, hb, hnx],
      nx₄]
  have hn₈ : heapNext t₈ = heapNext t₂ := by simp only [heapNext, nx₈]
  have inv₈ : InvR s t₈ (t₈.getMem nextAddr) := YW.inv hpre h.inv Y₈
    (by rw [hn₈, ← hn₁]; exact hmono₂) (by rw [hn₈]) (by rw [hn₈]; exact hhi₂) (by rw [sp₈, hB])
  have hr₈ : Reaches Image.code u t₈ :=
    r₁.trans (r₂.trans (r₃.trans (r₄.trans (r₅.trans (r₆.trans (r₇.trans r₈))))))
  by_cases hok : t₆.getReg .x10 = okTag
  swap
  · obtain ⟨v, rv', hv⟩ := fail844 inv₈ (b8000c084_pc h₈) (by rw [x1₈]; exact hok)
    exact ⟨v, hr₈.trans rv', Or.inl hv⟩
  obtain ⟨v, rv', pcv, x10v, invv, memv⟩ := ok844 inv₈ (b8000c084_pc h₈) (by rw [x1₈]; exact hok)
  -- the product is the running target
  rw [x10₆, sp₅] at hok
  obtain ⟨l0, l1, l2⟩ := cmp_ok hok
  have keep (k : ℕ) (hk : k = 120 ∨ k = 136 ∨ k = 176) :
      t₅.getMem (B + BitVec.ofNat 64 k) = u.getMem (B + BitVec.ofNat 64 k) := by
    have hk' : k ≤ 176 := by omega
    rw [X₅ _ fun i hi hw ↦ by rcases hw with hw | hw <;> (try rw [hsp] at hw); all_goals addr_omega [hw, hi, hb, hsp, hk', hk],
      F₄ _ fun i hi hw ↦ by rw [hsp] at hw; addr_omega [hw, hi, hb, hsp, hk', hk],
      F₃ _ fun i hi hw ↦ by rcases hw with hw | hw <;> (rw [hsp] at hw; rcases hk with rfl | rfl | rfl <;> addr_omega [hw, hi, hb, hsp]),
      X₂ _ fun i hi hw ↦ by
        rcases hw with hw | hw | hw | hw
        · rw [hsp] at hw; addr_omega [hw, hi, hb, hk', hk]
        · addr_omega [hw, hi, hb, hsp, hk', hk]
        · addr_omega [hw, hi, hb, hnx, hsp, hk', hk]
        · simp only [Fresh, heapEnd] at hw hhi₂ hab; addr_omega [hw.1, hw.2, hi, hb, hab, hhi₂, hsp, hk', hk],
      m₁]
  have hwr : w * rv = rt := by
    rw [← val₅, show B + 576 = B + BitVec.ofNat 64 576 from rfl, eAt_limbs t₅ B 576 (by decide),
      ← h.trg]
    simp only [Nat.reduceAdd]
    rw [show B + BitVec.ofNat 64 576 = B + 576 from rfl, show B + BitVec.ofNat 64 584 = B + 584 from rfl,
      show B + BitVec.ofNat 64 592 = B + 592 from rfl, l0, l1, l2,
      show B + 136 = B + BitVec.ofNat 64 136 from rfl, show B + 120 = B + BitVec.ofNat 64 120 from rfl,
      show B + 176 = B + BitVec.ofNat 64 176 from rfl, keep 136 (by decide), keep 120 (by decide),
      keep 176 (by decide), show B + BitVec.ofNat 64 136 = s.getReg .x2 - 904 by rw [hsp]; addr_omega [hb],
      show B + BitVec.ofNat 64 120 = s.getReg .x2 - 920 by rw [hsp]; addr_omega [hb],
      show B + BitVec.ofNat 64 176 = s.getReg .x2 - 864 by rw [hsp]; addr_omega [hb]]
  refine ⟨v, hr₈.trans rv', Or.inr ⟨pcv, x10v, ⟨_, invv⟩, fun T hT hO hr ↦ ?_⟩⟩
  obtain ⟨T', e, hT'⟩ := h.value T hT hO hr
  refine ⟨T', ?_, tr_congr (tr_keep hpre h.inv hT' Y₈ fun a ha ↦ YW.ns hpre h.inv hhi₂ ha) memv⟩
  rw [e]
  simp only [terminalCheckM, hmle, Model.TM.ofOption, Model.TM.require, bind, StateT.bind,
    pure, StateT.pure, StateT.run]
  exact ite_eq_left_of_eq_true _ _ (eq_true hwr)

end Rv64Verifier.Proofs.Pcs.Vso
