import Rv64Verifier.Proofs.Bus.VbbGkrBase

/-!
# `verify_bus_balance`: what an iteration of the GKR loop keeps

`Ctx`: the loop's invariant without the registers and the layer's objects: `Inv`, `Kept`, the
fence, `count`'s third limb and `push`'s pointer saved, `values`' capacity (at least three, so the
pushes never grow it) and buffer. A step writing the frame's scratch (`Scratch`: `Free` but those
words and `values`' capacity and pointer) keeps it (`Ctx.step`), and so does a push into `values`
(`Ctx.stepV`).
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript

/-- `Free` but `S - 1272`, `S - 1256` and `values`' capacity and pointer. -/
def Scratch (s : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 1344) 32 ∨ Within a (s.getReg .x2 - 1304) 32 ∨
    Within a (s.getReg .x2 - 1216) 16 ∨ Within a (s.getReg .x2 - 1144) 8 ∨
    Within a (s.getReg .x2 - 1128) 48 ∨ Within a (s.getReg .x2 - 864) 688 ∨
    Within a (s.getReg .x2 - 160) 56

theorem Scratch.free {s : MachineState} (hpre : BusBalancePre s) {a : Word} (h : Scratch s a) :
    Free s a := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  rcases h with h | h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (by addr_omega [h, hb1]))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by addr_omega [h, hb1]))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by addr_omega [h, hb1]))))))

theorem Scratch.frameW {s : MachineState} (hpre : BusBalancePre s) : FrameW s (Scratch s) :=
  fun a ha ↦ Free.frameW hpre a (ha.free hpre)

/-- The words at `S - j`, `j` from `n` down, miss `Scratch`. -/
theorem Scratch.miss {s : MachineState} (hpre : BusBalancePre s) {j n : Nat} (hj : n ≤ j)
    (hj2 : j ≤ 1344)
    (h : ∀ i, j - n < i → i ≤ j → (1312 < i ∧ i ≤ 1344 → False) ∧ (1272 < i ∧ i ≤ 1304 → False) ∧
      (1200 < i ∧ i ≤ 1216 → False) ∧ (1136 < i ∧ i ≤ 1144 → False) ∧
      (1080 < i ∧ i ≤ 1128 → False) ∧ (176 < i ∧ i ≤ 864 → False) ∧ (104 < i ∧ i ≤ 160 → False)) :
    ∀ y, Within y (s.getReg .x2 - BitVec.ofNat 64 j) n → ¬ Scratch s y := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  intro y hy hf
  have hyn : (s.getReg .x2).toNat - j ≤ y.toNat ∧ y.toNat < (s.getReg .x2).toNat - j + n := by
    addr_omega [hy, hb1, hj, hj2]
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := h ((s.getReg .x2).toNat - y.toNat) (by omega)
    (by omega)
  rcases hf with hf | hf | hf | hf | hf | hf | hf
  · exact c1 (by addr_omega [hf, hb1, hyn])
  · exact c2 (by addr_omega [hf, hb1, hyn])
  · exact c3 (by addr_omega [hf, hb1, hyn])
  · exact c4 (by addr_omega [hf, hb1, hyn])
  · exact c5 (by addr_omega [hf, hb1, hyn])
  · exact c6 (by addr_omega [hf, hb1, hyn])
  · exact c7 (by addr_omega [hf, hb1, hyn])

/-- What every step of an iteration keeps. -/
structure Ctx (s u : MachineState) (k : Start) (cnt : E) (P : Word) : Prop where
  inv : Inv s u
  kept : Kept s u k
  fence : Fence s u P
  cnt2 : cnt = eOf3 k.count0 k.count1 (u.getMem (s.getReg .x2 - 1256))
  pushPtr : u.getMem (s.getReg .x2 - 1272) = vecPtr s (s.getReg .x11 + 24)
  cap : 3 ≤ (vecCap u (s.getReg .x2 - 176)).toNat
  ptr : vecPtr u (s.getReg .x2 - 176) = P
  heapP : heapNext s ≤ P.toNat ∧ P.toNat + 72 ≤ heapNext u ∧ P.toNat + 72 ≤ heapEnd

theorem Loop.ctx {bev : MachineState → Word → List E → Option E} {s u : MachineState}
    {k : Start} {cnt : E} {P c : Word} {n : ℕ} {st : GkrState}
    (h : Loop bev s u k cnt P c n st) : Ctx s u k cnt P := by
  refine ⟨h.inv, h.kept, h.fence, h.cnt2, h.pushPtr, ?_, h.ptr, h.heapP⟩
  have hl := h.values.vec.len
  have h3 : (vecLen u (s.getReg .x2 - 176)).toNat = 3 := by
    rw [← h.len, ← h.values.elems, vecEs, eListAt_length]
  omega

section Ctx
variable {s v w : MachineState} {k : Start} {cnt : E} {P : Word}

/-- The words `Ctx` reads outside `Kept`. -/
theorem Ctx.words (hpre : BusBalancePre s) {A : Word → Prop} (st : StepR s v w A)
    (hA : ∀ y, (Within y (s.getReg .x2 - 1272) 8 ∨ Within y (s.getReg .x2 - 1256) 8 ∨
      Within y (s.getReg .x2 - 176) 16) → ¬ A y) :
    w.getMem (s.getReg .x2 - 1272) = v.getMem (s.getReg .x2 - 1272) ∧
      w.getMem (s.getReg .x2 - 1256) = v.getMem (s.getReg .x2 - 1256) ∧
      vecCap w (s.getReg .x2 - 176) = vecCap v (s.getReg .x2 - 176) ∧
      vecPtr w (s.getReg .x2 - 176) = vecPtr v (s.getReg .x2 - 176) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  refine ⟨st.word hpre (fun y hy ↦ hA y (Or.inl hy)) (Or.inl (by addr_omega [hb1])),
    st.word hpre (fun y hy ↦ hA y (Or.inr (Or.inl hy))) (Or.inl (by addr_omega [hb1])),
    st.word hpre (fun y hy ↦ hA y (Or.inr (Or.inr (by addr_omega [hy, hb1]))))
      (Or.inl (by addr_omega [hb1])),
    st.word hpre (fun y hy ↦ hA y (Or.inr (Or.inr (by addr_omega [hy, hb1]))))
      (Or.inl (by addr_omega [hb1]))⟩

theorem Ctx.step (hpre : BusBalancePre s) (c : Ctx s v k cnt P) (st : StepR s v w (Scratch s)) :
    Ctx s w k cnt P := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  obtain ⟨K, F⟩ := c.kept.stepV hpre c.fence c.inv.heap c.heapP.2.2
    (st.weaken fun a ha ↦ Or.inl (ha.free hpre))
  obtain ⟨e1, e2, e3, e4⟩ := Ctx.words hpre st fun y hy hs ↦ by
    rcases hy with hy | hy | hy
    · exact Scratch.miss hpre (j := 1272) (n := 8) (by omega) (by omega)
        (by intro i h1 h2; omega) y hy hs
    · exact Scratch.miss hpre (j := 1256) (n := 8) (by omega) (by omega)
        (by intro i h1 h2; omega) y hy hs
    · exact Scratch.miss hpre (j := 176) (n := 16) (by omega) (by omega)
        (by intro i h1 h2; omega) y hy hs
  have hm := st.mono
  have hP := c.heapP
  exact ⟨c.inv.afterR hpre (Scratch.frameW hpre) st, K, F, by rw [e2]; exact c.cnt2,
    by rw [e1]; exact c.pushPtr, by rw [e3]; exact c.cap, by rw [e4]; exact c.ptr,
    ⟨c.heapP.1, by omega, c.heapP.2.2⟩⟩

theorem Ctx.stepV (hpre : BusBalancePre s) (c : Ctx s v k cnt P)
    (st : StepR s v w fun a ↦ Scratch s a ∨ Within a P 72) : Ctx s w k cnt P := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hP := c.heapP
  have stV : StepR s v w (FreeV s P) := st.weaken fun a ha ↦ ha.imp_left (Scratch.free hpre)
  obtain ⟨K, F⟩ := c.kept.stepV hpre c.fence c.inv.heap hP.2.2 stV
  obtain ⟨e1, e2, e3, e4⟩ := Ctx.words hpre st fun y hy hs ↦ by
    simp only [heapEnd] at hP
    rcases hs with hs | hs
    · rcases hy with hy | hy | hy
      · exact Scratch.miss hpre (j := 1272) (n := 8) (by omega) (by omega)
          (by intro i h1 h2; omega) y hy hs
      · exact Scratch.miss hpre (j := 1256) (n := 8) (by omega) (by omega)
          (by intro i h1 h2; omega) y hy hs
      · exact Scratch.miss hpre (j := 176) (n := 16) (by omega) (by omega)
          (by intro i h1 h2; omega) y hy hs
    · rcases hy with hy | hy | hy <;> addr_omega [hy, hs, hb1, hP]
  have hm := st.mono
  exact ⟨c.inv.afterV hpre stV hP.1 hP.2.1, K, F, by rw [e2]; exact c.cnt2,
    by rw [e1]; exact c.pushPtr, by rw [e3]; exact c.cap, by rw [e4]; exact c.ptr,
    ⟨hP.1, by omega, hP.2.2⟩⟩

end Ctx

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
