import Rv64Verifier.Proofs.Pcs.VsoFoldGrowL

/-!
# `verify_stacked_opening`'s level loop: the challenge pushed to `level_folds`, the quadratic at it

`0x8000a270` stores the challenge after `level_folds` and their new length, and calls
`poly_eval(S - 464, quadratic, S - 128)`, which returns at `0x8000a2ac`.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- At `0x8000a2ac`: the challenge `c` pushed to both, the quadratic at it in `S - 464`. -/
structure PL (s : MachineState) (x : LCtx) (h u : MachineState) (ℓ : ℕ)
    (Wl : Model.Pcs.WhirLocals) (j : ℕ) (lf q : List E) (c : E) : Prop
    extends RB s x h u ℓ Wl (Wl.folds ++ lf ++ [c]) (lf ++ [c]) q where
  pc : u.pc = 0x8000a2ac
  x19 : u.getReg .x19 = vecPtr u (s.getReg .x2 - 640)
  x20 : u.getReg .x20 = BitVec.ofNat 64 (24 * j)
  x21 : u.getReg .x21 = BitVec.ofNat 64 (j + 1)
  x24 : u.getReg .x24 = BitVec.ofNat 64 Wl.folds.length
  jlt : j < fcOf s ℓ
  lfl : lf.length = j
  pe : eAt u (s.getReg .x2 - 464) = Model.polyEvalRust q c
  value : Runs s u ℓ (Model.Pcs.roundK Wl lf q (fcOf s ℓ - (j + 1)) (AFk s x ℓ) c)

theorem pushLF (hPE : PolyEvalSpec) {s : MachineState} {x : LCtx} {h u : MachineState} {ℓ : ℕ}
    {Wl : Model.Pcs.WhirLocals} {j : ℕ} {lf q : List E} {c : E}
    (hpre : VsoPre s) (hs : PF s x h u ℓ Wl j lf q c) (hpc : u.pc = 0x8000a270)
    (hroom : j < (vecCap u (s.getReg .x2 - 640)).toNat) :
    ∃ v, Reaches Image.code u v ∧ (Dead Image.code v ∨ PL s x h v ℓ Wl j lf q c) := by
  have hb := bounds hpre
  have hst := hpre.stack
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hsp := hs.sp
  have hB := hs.bufs
  have hf := hs.head.facts
  have hhu := hs.heap.hi
  have hsm := vec_small hs.LF.1 hs.heap
  have hL8 := hs.LF.1.raw.1
  obtain ⟨hLl, hLh⟩ : x.L ≤ (vecPtr u (s.getReg .x2 - 640)).toNat ∧
      (vecPtr u (s.getReg .x2 - 640)).toNat + (vecCap u (s.getReg .x2 - 640)).toNat * 24 ≤
        heapNext u := by
    rcases hB.LF with h0 | h0
    · omega
    · exact h0
  have hLs := hf.hs
  have hhs := hpre.heap.lo
  have hLr : Region (vecPtr u (s.getReg .x2 - 640)) ((vecCap u (s.getReg .x2 - 640)).toNat * 24) :=
    heap_region (by simp only [heapStart, heapNext] at hhs hLs hLl ⊢; omega) (by omega) hL8
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000a270_spec hpc (by
    rv_eval [hsp, hs.x19, hs.x20]
    and_intros <;> first
      | valid_access hst.valid [hb]
      | exact Region.valid hLr (by addr_omega [hroom, hsm, hLh, hhu])
          (by addr_omega [hroom, hsm, hLh, hhu]) (by addr_omega [hroom, hsm, hLh, hhu, hL8])
      | addr_omega [hb, hroom, hsm, hLh, hhu])
  have k₁ := b8000a270_keeps h₁
  have hjl : lf.length = j := hs.lfl
  have m1 := b8000a270_m1 h₁
  have m2 := b8000a270_m2 h₁
  have m3 := b8000a270_m3 h₁
  rw [hs.x19, hs.x20, ← hjl] at m1 m2 m3
  have X : DFrame u t₁ fun a ↦ Within a (s.getReg .x2 - 624) 8 ∨
      Within a (vecPtr u (s.getReg .x2 - 640) + BitVec.ofNat 64 (24 * lf.length)) 24 :=
    (holds_dframe h₁).mono fun a ⟨k, hk, hw⟩ ↦ by
      simp only [b8000a270, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl <;> rv_eval [hsp, hs.x19, hs.x20] at hw
      all_goals first
        | exact Or.inl (by addr_omega [hw, hb])
        | exact Or.inr (by rw [hjl]; addr_omega [hw, hroom, hsm, hLh, hhu])
  have hFB := hB.F
  have hap := hs.ap
  have nx : t₁.getMem nextAddr = u.getMem nextAddr := X _ fun i hi hw ↦ by
    rcases hw with hw | hw
    · addr_omega [hw, hi, hb, hnx]
    · rw [hjl] at hw; addr_omega [hw, hi, hroom, hsm, hLh, hhu, hnx]
  have hn₁ : heapNext t₁ = heapNext u := by simp only [heapNext, nx]
  have hl : t₁.getMem (s.getReg .x2 - 640 + 16) = BitVec.ofNat 64 (lf.length + 1) := by
    have m416 := b8000a270_m_x2_416 h₁
    rw [hsp, hs.x21] at m416
    rw [show s.getReg .x2 - 640 + 16 = s.getReg .x2 - BitVec.ofNat 64 1040 + 416 by
      addr_omega [hb], m416, hjl]
    addr_omega [hroom, hsm]
  have hc : eAt t₁ (vecPtr u (s.getReg .x2 - 640) + BitVec.ofNat 64 (24 * lf.length)) = c := by
    rw [← hs.chal]
    unfold eAt
    rw [m1, m2, m3, hsp]
    rv_eval []
  have hLp := vecE_push hs.LF.1 hs.LF.2.1 X (fun a ha ↦ by
      rcases ha with ha | ha
      · exact Or.inl (by addr_omega [ha, hb])
      · exact Or.inr ha) (by rw [hjl]; exact hroom) hl hc (by addr_omega [hb]) (by addr_omega [hb])
    hs.heap (by rw [hn₁])
  have hFk := vecE_keep X hs.F.1 (fun a ha ↦ by
      refine ⟨fun hw ↦ ?_, fun hw ↦ ?_⟩
      · rcases ha with ha | ha
        · addr_omega [ha, hw, hb]
        · rw [hjl] at ha; addr_omega [ha, hw, hb, hroom, hsm, hLh, hhu]
      · rcases ha with ha | ha
        · rcases hFB with h0 | h0
          · simp only [Within] at hw; omega
          · addr_omega [ha, hw, hb, h0.2, hhu]
        · rw [hjl] at ha; addr_omega [ha, hw, hap.1, hroom, hsm, hLh, hhu])
    (by addr_omega [hb]) (by rw [hn₁]) hs.heap
  have hRB := RB.carry2 (fl' := Wl.folds ++ lf ++ [c]) (lfs' := lf ++ [c]) hpre hs.toRB X
    (fun a ha ↦ by
      rcases ha with ha | ha
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb])))))
      · rw [hjl] at ha
        refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨?_, ?_⟩)))))))
        · rcases hs.LF.2.2.2 with h0 | h0
          · omega
          · addr_omega [ha, h0.1, hroom, hsm, hLh, hhu]
        · rw [nx]; addr_omega [ha, hroom, hsm, hLh, hhu])
    (fun a ha ↦ by
      refine ⟨fun hw ↦ ?_, fun hw ↦ ?_⟩
      · rcases ha with ha | ha
        · rcases hw with hw | hw | hw <;> addr_omega [ha, hw, hb]
        · rw [hjl] at ha
          rcases hw with hw | hw | hw <;> addr_omega [ha, hw, hb, hroom, hsm, hLh, hhu]
      · rcases ha with ha | ha
        · rcases hB.Q with h0 | h0
          · simp only [Within] at hw; omega
          · addr_omega [ha, hw, hb, h0.2, hhu]
        · rw [hjl] at ha; addr_omega [ha, hw, hap.2.2, hroom, hsm, hLh, hhu])
    ⟨by rw [hn₁]; exact hs.heap.lo, by rw [hn₁]; exact hhu⟩ (by rw [hn₁])
    (fun r hr' ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact k₁ _ (by decide))
    ⟨hFk.1, by rw [hFk.2.1]; exact hs.F.2.1, by
      rw [hFk.2.2.1, hFk.2.2.2.1]
      rcases hs.F.2.2 with h0 | h0
      · exact Or.inl h0
      · exact Or.inr (NewBuf.grow h0 (by rw [hn₁]))⟩
    ⟨hLp.1, hLp.2.1, by
      rw [hLp.2.2.1, hLp.2.2.2]; exact NewBuf.grow hs.LF.2.2 (by rw [hn₁])⟩
    (by rw [hFk.2.2.1, hFk.2.2.2.1, hLp.2.2.1, hLp.2.2.2]; exact hap)
  have hrst := hpre.root.stack
  rw [stackLo_vso, vso_stack] at hrst
  have hrf := hpre.root.free
  simp only [Outside] at hrf
  have inv := FW.inv hpre hs.head hs.fr hs.heap hs.mono (hsp.trans hs.head.sp.symm)
  have v₁ := hs.value.keep hpre inv X (fun a ha ↦ by
        rcases ha with ha | ha
        · exact Or.inl (by addr_omega [ha, hb])
        · rw [hjl] at ha
          exact Or.inr (Or.inr (Or.inl ⟨by
            have := hf.hs; addr_omega [ha, hLl, this, hroom, hsm, hLh, hhu],
            by addr_omega [ha, hroom, hsm, hLh, hhu]⟩)))
      fun y hy hw ↦ by
        rcases hw with hw | hw
        · addr_omega [hy, hw, hrst, hb]
        · rw [hjl] at hw
          rcases hrf.1 with h0 | h0
          · have := hf.hs; addr_omega [hy, hw, h0, hLl, this, hroom, hsm, hLh, hhu]
          · addr_omega [hy, hw, h0, hroom, hsm, hLh, hhu]
  have c₁ : eAt t₁ (s.getReg .x2 - 128) = c := by
    rw [← hs.chal]
    exact X.eAt' (fun y hy hw ↦ by
      rcases hw with hw | hw
      · addr_omega [hy, hw, hb]
      · rw [hjl] at hw; addr_omega [hy, hw, hb, hroom, hsm, hLh, hhu]) (by addr_omega [hb])
  have sp₁ : t₁.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := hRB.sp
  have inv₁ := FW.inv hpre hs.head hRB.fr hRB.heap hRB.mono (sp₁.trans hs.head.sp.symm)
  have hQB := hRB.bufs.Q
  have hq₁ := hRB.Q
  have hhs' := hRB.heap.hi
  obtain ⟨t₂, hr₂, hv₂⟩ := callPolyEval (o := s.getReg .x2 - 464) (c := s.getReg .x2 - 128) hPE hpre inv₁
    (b8000a270_pc h₁) (by rw [b8000a270_x10 h₁, hsp]; addr_omega [hb]) (b8000a270_x11 h₁) (b8000a270_x12 h₁)
    (by rw [b8000a270_x13 h₁, hsp]; addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb])
    (by addr_omega [hb]) (by
      rw [← k₁ .x22 (by decide), ← k₁ .x23 (by decide)]
      rcases hQB with h0 | h0
      · exact Or.inl h0
      · exact Or.inr ⟨by simp only [heapStart, heapNext] at hhs hLs h0 ⊢; omega, by
          have := hhs'; simp only [heapEnd] at this ⊢; omega⟩)
    (by rw [← k₁ .x22 (by decide)]; exact hq₁.2.1)
  rcases hv₂ with hd | ⟨hpc₂, hpres₂, X₂, hpe⟩
  · exact ⟨t₂, hr₁.trans hr₂, Or.inl hd⟩
  have hreg (r : Reg) (hr : r ∈ calleeSaved) : t₂.getReg r = t₁.getReg r := hpres₂ r hr
  have hRB₂ := RB.carry hpre hRB X₂ (fun a ha ↦ by
      rcases ha with ha | ha
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb])))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))))
    (fun a ha ↦ by
      have hB₁ := hRB.bufs
      refine ⟨fun hw ↦ ?_, fun hw ↦ ?_⟩
      · simp only [RSlots] at hw
        rcases ha with ha | ha <;> rcases hw with hw | hw | hw | hw | hw <;> addr_omega [ha, hw, hb]
      · simp only [RBufs] at hw
        rcases hw with hw | hw | hw
        · rcases hB₁.F with h0 | h0
          · simp only [Within] at hw; omega
          · rcases ha with ha | ha <;> addr_omega [ha, hw, hb, h0.2, hhs']
        · rcases hB₁.LF with h0 | h0
          · simp only [Within] at hw; omega
          · rcases ha with ha | ha <;> addr_omega [ha, hw, hb, h0.2, hhs']
        · rcases hB₁.Q with h0 | h0
          · simp only [Within] at hw; omega
          · rcases ha with ha | ha <;> addr_omega [ha, hw, hb, h0.2, hhs'])
    (by
      have nx₂ : t₂.getMem nextAddr = t₁.getMem nextAddr := X₂ _ fun i hi hw ↦ by
        rcases hw with hw | hw <;> addr_omega [hw, hi, hb, hnx]
      exact ⟨by simp only [heapNext, nx₂]; exact hRB.heap.lo,
        by simp only [heapNext, nx₂]; exact hRB.heap.hi⟩)
    (by
      have nx₂ : t₂.getMem nextAddr = t₁.getMem nextAddr := X₂ _ fun i hi hw ↦ by
        rcases hw with hw | hw <;> addr_omega [hw, hi, hb, hnx]
      simp only [heapNext, nx₂]; exact Nat.le_refl _)
    (fun r hr' ↦ hreg r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide))
  refine ⟨t₂, hr₁.trans hr₂, Or.inr {
    toRB := hRB₂
    pc := by rw [hpc₂, returnAddress_eq, b8000a270_x1 h₁]; decide
    x19 := by
      have e : vecPtr t₂ (s.getReg .x2 - 640) = vecPtr t₁ (s.getReg .x2 - 640) :=
        X₂ _ fun i hi hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hi, hb]
      rw [hreg .x19 (by decide), k₁ .x19 (by decide), hs.x19, e, hLp.2.2.1]
    x20 := by rw [hreg .x20 (by decide), k₁ .x20 (by decide), hs.x20]
    x21 := by rw [hreg .x21 (by decide), b8000a270_x21 h₁, hs.x21, BitVec.ofNat_add]; rfl
    x24 := by rw [hreg .x24 (by decide), k₁ .x24 (by decide), hs.x24]
    jlt := hs.jlt
    lfl := hs.lfl
    pe := by
      rw [hpe, c₁, ← hq₁.1, k₁ .x22 (by decide), k₁ .x23 (by decide)]
    value := v₁.keep hpre inv₁ X₂ (fun a ha ↦ by
        rcases ha with ha | ha <;> exact Or.inl (by addr_omega [ha, hb]))
      fun y hy hw ↦ by rcases hw with hw | hw <;> addr_omega [hy, hw, hrst, hb] }⟩

end Rv64Verifier.Proofs.Pcs.Vso
