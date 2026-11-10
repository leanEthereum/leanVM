import Rv64Verifier.Proofs.Bus.VbbGkrBase

/-!
# `verify_bus_balance`: the GKR loop from its iterations

The loop's entry (`0x80006614`: `count`'s third limb and `push`'s pointer saved, the registers
set), its exit (`0x80006c7c`: the saved words reloaded, `point`'s capacity not `-1`), and the loop
by induction on the layers left, from one iteration (`Iter`).
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F26
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem NewVecR.same {s u v : MachineState} {c p l : Word} {xs : List E}
    (h : NewVecR s u c p l xs) (hm : ∀ a, v.getMem a = u.getMem a) : NewVecR s v c p l xs := by
  have hn : heapNext v = heapNext u := by simp only [heapNext, hm]
  refine ⟨h.le, ?_, ?_⟩
  · have := h.buf
    simp only [NewBuf] at this ⊢
    rw [hn]
    exact this
  · rw [← h.elems]
    exact eListAt_congr fun i _ ↦ eAt_congr (hm _) (hm _) (hm _)

/-- From `0x80006614` to the loop's head. -/
theorem gkrEntry {bev : MachineState → Word → List E → Option E} {s u : MachineState} {k : Start}
    {sh cnt : E} (hpre : BusBalancePre s) (h : AfterStart bev s u k sh cnt)
    (F : Fence s u (vecPtr u (s.getReg .x2 - 176))) (hpc : u.pc = 0x80006614) :
    ∃ v, Reaches Image.code u v ∧ v.pc = 0x8000669c ∧
      Loop bev s v k cnt (vecPtr u (s.getReg .x2 - 176)) 0 (pushDepth s) ⟨[sh, sh, cnt], []⟩ := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  have sp := h.inv.sp
  obtain ⟨v, hr, h₁⟩ := Sym.BlockSpec.reaches b80006614_spec hpc (by
    rv_eval [sp]
    and_intros <;> valid_access hval [hb1])
  have k₁ := b80006614_keeps h₁
  have fr : DFrame u v fun a ↦ Within a (s.getReg .x2 - 1272) 8 ∨
      Within a (s.getReg .x2 - 1256) 8 := fun a ha ↦
    h₁.frame a (by
      rv_eval [sp]
      and_intros <;> intro he <;> exact ha 0 (by decide) (by
        rw [add_ofNat_zero, he]; addr_omega [hb1]))
  have st : StepR s u v fun a ↦ Within a (s.getReg .x2 - 1272) 8 ∨
      Within a (s.getReg .x2 - 1256) 8 :=
    StepR.ofDFrame h.inv.heap fr (fun _ h ↦ h) (fun i hi hw ↦ by
      rcases hw with hw | hw <;> addr_omega [hw, hi, hb1]) (k₁ .x2 (by decide))
  have fA : FrameW s fun a ↦ Within a (s.getReg .x2 - 1272) 8 ∨
      Within a (s.getReg .x2 - 1256) 8 := fun a ha ↦ by
    rcases ha with ha | ha <;> addr_omega [ha, hb1]
  have I := h.inv.afterR hpre fA st
  obtain ⟨-, -, hP3⟩ := h.values.heap3 rfl h.inv.heap
  have stV : StepR s u v (FreeV s (vecPtr u (s.getReg .x2 - 176))) := st.weaken fun a ha ↦ by
    rcases ha with ha | ha
    · exact Or.inl (Or.inr (Or.inl (by addr_omega [ha, hb1])))
    · exact Or.inl (Or.inr (Or.inr (Or.inl ha)))
  obtain ⟨K, F'⟩ := h.kept.stepV hpre F h.inv.heap hP3 stV
  have miss (j n : Nat) (hj : j ≤ 1248) (hj2 : n ≤ j) : ∀ y, Within y (s.getReg .x2 - BitVec.ofNat 64 j) n →
      ¬ (Within y (s.getReg .x2 - 1272) 8 ∨ Within y (s.getReg .x2 - 1256) 8) := fun y hy hw ↦ by
    rcases hw with hw | hw <;> addr_omega [hy, hw, hb1, hj, hj2]
  have m72 := b80006614_m_x2_72 h₁
  have m88 := b80006614_m_x2_88 h₁
  rw [sp, show s.getReg .x2 - 1344 + 72 = s.getReg .x2 - 1272 by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]] at m72
  rw [sp, show s.getReg .x2 - 1344 + 88 = s.getReg .x2 - 1256 by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]] at m88
  refine ⟨v, hr, b80006614_pc h₁, {
    inv := I
    kept := K
    fence := F'
    x9 := b80006614_x9 h₁
    x19 := (k₁ .x19 (by decide)).trans h.x19
    x20 := (k₁ .x20 (by decide)).trans h.x20
    x22 := (k₁ .x22 (by decide)).trans h.x22
    x24 := b80006614_x24 h₁
    x25 := by rw [k₁ .x25 (by decide)]; exact h.x25
    cnt2 := by rw [m88]; exact h.cntEq
    pushPtr := by rw [m72]; exact h.x24
    ptr := by
      show v.getMem (s.getReg .x2 - 176 + 8) = u.getMem (s.getReg .x2 - 176 + 8)
      rw [show s.getReg .x2 - 176 + 8 = s.getReg .x2 - BitVec.ofNat 64 168 by
        apply BitVec.eq_of_toNat_eq; addr_omega [hb1]]
      exact st.word hpre (miss 168 8 (by omega) (by omega)) (Or.inl (by addr_omega [hb1]))
    point := by
      rw [b80006614_x27 h₁, b80006614_x21 h₁]
      exact ⟨Nat.le_refl _, ⟨by decide, Or.inl rfl⟩, rfl⟩
    values := h.values.keepR hpre st fA (by addr_omega [hb1]) (miss 176 24 (by omega) (by omega))
    len := rfl
    tracks := h.tracks.keep fun T hT ↦ h.inv.transcript hpre I.heap
      (fr.mono fun a ha ↦ by rcases ha with ha | ha <;> exact Or.inl (by addr_omega [ha, hb1])) hT }⟩

/-- From the exit's test, `0x80006c7c`, to `0x80006b60`. -/
theorem gkrExit {bev : MachineState → Word → List E → Option E} {s u : MachineState} {k : Start}
    {cnt : E} {P : Word} {st : GkrState} (hpre : BusBalancePre s)
    (h : Loop bev s u k cnt P (u.getMem (s.getReg .x2 - 248)) 0 st) (hpc : u.pc = 0x80006c7c) :
    ∃ v, Reaches Image.code u v ∧ v.pc = 0x80006b60 ∧ AfterGkr bev s v k cnt st := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  have sp := h.inv.sp
  obtain ⟨v, hr, h₁⟩ := Sym.BlockSpec.reaches b80006c7c_spec hpc (by
    rv_eval [sp]
    and_intros <;> valid_access hval [hb1])
  have k₁ := b80006c7c_keeps h₁
  have m₁ := b80006c7c_mem_same h₁
  have sp₁ := k₁ .x2 (by decide)
  have hc : u.getMem (s.getReg .x2 - 248) ≠ 0xffffffffffffffff := by
    intro he
    have hb := h.point.buf
    have hh := h.inv.heap.hi
    rw [he] at hb
    simp only [NewBuf, heapNext, heapEnd] at hb hh
    rcases hb.2 with h0 | ⟨-, b2⟩
    · exact absurd h0 (by decide)
    · have : (0xffffffffffffffff : Word).toNat = 2 ^ 64 - 1 := rfl
      omega
  have hpc₁ := b80006c7c_pc_taken h₁ (by rw [sp]; rw [show s.getReg .x2 - 1344 + 1096 = s.getReg .x2 - 248 by
        apply BitVec.eq_of_toNat_eq; addr_omega [hb1]]; exact hc)
  have st : ∀ {A : Word → Prop}, StepR s u v A := StepR.same m₁ h.inv.heap sp₁
  refine ⟨v, hr, hpc₁, {
    inv := h.inv.same m₁ sp₁
    kept := h.kept.step hpre st
    x18 := by rw [b80006c7c_x18 h₁, sp, show s.getReg .x2 - 1344 + 32 = s.getReg .x2 - 1312 by
        apply BitVec.eq_of_toNat_eq; addr_omega [hb1]]; exact h.kept.out
    x20 := (k₁ .x20 (by decide)).trans h.x20
    x19 := by
      rw [k₁ .x19 (by decide), h.x19, ← h.ptr]
      exact (m₁ _).symm
    x24 := by rw [b80006c7c_x24 h₁, sp, show s.getReg .x2 - 1344 + 72 = s.getReg .x2 - 1272 by
        apply BitVec.eq_of_toNat_eq; addr_omega [hb1]]; exact h.pushPtr
    x11 := by rw [b80006c7c_x11 h₁, sp, show s.getReg .x2 - 1344 + 120 = s.getReg .x2 - 1224 by
        apply BitVec.eq_of_toNat_eq; addr_omega [hb1]]; exact h.kept.count0
    x12 := by rw [b80006c7c_x12 h₁, sp, show s.getReg .x2 - 1344 + 112 = s.getReg .x2 - 1232 by
        apply BitVec.eq_of_toNat_eq; addr_omega [hb1]]; exact h.kept.count1
    cntEq := by rw [b80006c7c_x13 h₁, sp, show s.getReg .x2 - 1344 + 88 = s.getReg .x2 - 1256 by
        apply BitVec.eq_of_toNat_eq; addr_omega [hb1]]; exact h.cnt2
    point := by
      rw [b80006c7c_x22 h₁, sp, show s.getReg .x2 - 1344 + 1096 = s.getReg .x2 - 248 by
        apply BitVec.eq_of_toNat_eq; addr_omega [hb1], k₁ .x27 (by decide), k₁ .x21 (by decide)]
      exact h.point.same m₁
    values := h.values.keepR hpre (st (A := fun _ ↦ False)) (fun _ h ↦ False.elim h)
      (by addr_omega [hb1]) fun _ _ h ↦ h
    tracks := by
      have := h.tracks
      rw [gkrLoopM_zero, pure_bind] at this
      exact this.keep fun T hT ↦ TranscriptAt.same hpre h.inv m₁ hT }⟩

/-- The loop, from its head with `n` layers left. -/
theorem gkrLoop {bev : MachineState → Word → List E → Option E} (hI : Iter bev)
    {s : MachineState} {k : Start} {cnt : E} {P : Word} (hpre : BusBalancePre s) :
    ∀ n u c st, Loop bev s u k cnt P c n st → u.pc = 0x8000669c → 0 < n →
      ∃ v, Reaches Image.code u v ∧ (Done bev s v ∨ Dead Image.code v ∨
        ∃ state, v.pc = 0x80006b60 ∧ AfterGkr bev s v k cnt state) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro u c st h hpc hn
    obtain ⟨v, hr, hd | hd | ⟨st', L, hpc'⟩⟩ := hI s u k cnt P c n st hpre h hpc hn
    · exact ⟨v, hr, Or.inl hd⟩
    · exact ⟨v, hr, Or.inr (Or.inl hd)⟩
    by_cases h0 : n - stepOf n = 0
    · simp only [h0, ↓reduceIte] at hpc'
      rw [h0] at L
      obtain ⟨w, hrw, hpcw, A⟩ := gkrExit hpre L hpc'
      exact ⟨w, hr.trans hrw, Or.inr (Or.inr ⟨st', hpcw, A⟩)⟩
    · simp only [h0, ↓reduceIte] at hpc'
      have hlt : n - stepOf n < n := by unfold stepOf; split <;> omega
      obtain ⟨w, hrw, hw⟩ := ih _ hlt v _ st' L hpc' (by omega)
      exact ⟨w, hr.trans hrw, hw⟩

/-- **The GKR loop's stage**, from one iteration. -/
theorem gkrStage (bev : MachineState → Word → List E → Option E) (hI : Iter bev) :
    GkrStage bev := by
  intro s u k sh cnt hpre h hpc
  obtain ⟨v, hr, hpcv, L⟩ := gkrEntry hpre h h.fence hpc
  have hpos : 0 < pushDepth s := by
    rcases h.branch with ⟨h1, -⟩ | ⟨-, h2⟩
    · rw [hpc] at h1; exact absurd h1 (by decide)
    · exact h2
  obtain ⟨w, hrw, hw⟩ := gkrLoop hI hpre _ v _ _ L hpcv hpos
  exact ⟨w, hr.trans hrw, hw⟩

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
