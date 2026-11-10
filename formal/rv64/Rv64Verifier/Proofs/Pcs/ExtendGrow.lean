import Rv64Verifier.Proofs.Pcs.ExtendConcat

/-!
# `Vec<StackClaim>::extend_desugared`: room for the claim

From `Mid` at `0x80009d34`: the value to `F + 32`, and `grow_amortized` when the `Vec` is full,
to `Room` at `0x80009bf8`; a grown `Vec`'s buffer is a new one holding the old claims' words.
-/

namespace Rv64Verifier.Proofs.Pcs.Extend
open RiscvZkvm.Rv64 Rv64Verifier.Runtime Rv64Verifier.Transcript Rv64Verifier.Pcs
  Rv64Verifier.PcsContracts Rv64Verifier.Model.Pcs Rv64Verifier.Blocks.F37 LeanVM.Parameters
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem CallW.step {s u : MachineState} {nx x : Word} (h : CallW s u nx x) : StepW s u nx x := by
  rcases h with h | h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

theorem StepW.mono {s u : MachineState} {nx nx' x : Word} (h : StepW s u nx x)
    (hle : nx.toNat ≤ nx'.toNat) : StepW s u nx' x := by
  rcases h with h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h.1, by omega⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

/-- A new `Vec<E>` across a frame that misses it and its buffer. -/
theorem NewVecE.frame {u v w : MachineState} {a : Word} {xs : List E} (h : NewVecE u v a xs)
    {X : Word → Prop} (hf : DFrame v w X) (hn : heapNext v ≤ heapNext w)
    (hs : ∀ x, Within x a 24 → ¬ X x) (ha : a.toNat + 24 ≤ 2 ^ 64)
    (hbuf : ∀ x, Within x (vecPtr v a) ((vecCap v a).toNat * 24) → ¬ X x) : NewVecE u w a xs := by
  have w0 : w.getMem a = v.getMem a := hf.word (fun x hx ↦ hs x (by addr_omega [hx, ha])) (by omega)
  have w8 : w.getMem (a + 8) = v.getMem (a + 8) :=
    hf.word (fun x hx ↦ hs x (by addr_omega [hx, ha])) (by addr_omega [ha])
  have w16 : w.getMem (a + 16) = v.getMem (a + 16) :=
    hf.word (fun x hx ↦ hs x (by addr_omega [hx, ha])) (by addr_omega [ha])
  have hP : vecPtr w a = vecPtr v a := w8
  have hL : vecLen w a = vecLen v a := w16
  have hC : vecCap w a = vecCap v a := w0
  have hv := h.vec
  have hb := h.buf
  refine ⟨⟨?_, by rw [hL, hC]; exact hv.len⟩, ?_, ?_⟩
  · have := hv.raw
    simp only [RawVecOk, Buf, hP, hC] at this ⊢
    omega
  · simp only [NewBuf, hP, hC] at hb ⊢
    omega
  · rw [← h.elems, vecEs, vecEs, hP, hL]
    have hl := hv.len
    rcases hb with ⟨-, hb0 | ⟨hb1, hb2⟩⟩
    · have : (vecLen v a).toNat = 0 := by omega
      rw [this]; rfl
    · have hlt : heapNext v < 2 ^ 64 := (v.getMem nextAddr).isLt
      exact hf.eList (fun x hx ↦ hbuf x (by addr_omega [hx, hl])) (Or.inr (by omega))

end Rv64Verifier.Proofs.Pcs.Extend
