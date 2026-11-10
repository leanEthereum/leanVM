import Rv64Verifier.Proofs.Pcs.VsoGlueBase

/-!
# `verify_stacked_opening`'s final level: one glued claim, its head

The loop's invariant at `0x8000bb58` is `GLI`: claim `j` next, the weight so far `acc` at
`S - 184`, the end of the claims at `S - 880`. A claim's value `val` reaches `0x8000baf8` as `GV`.
`0x8000bb58` loads the scalar into `S - 232` and the fold start, a trap past the point's end;
`0x8000bb7c` keeps the claim at `S - 872`, the point's suffix at `S - 848` and its length in `s10`,
and branches on the weight's kind.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-! ## Buffers -/

/-- Bytes of a buffer all in `[L, H)`: the buffer is. -/
theorem bufBound {p : Word} {n L H : ℕ} (hH : H ≤ heapEnd)
    (hf : ∀ y, Within y p n → L ≤ y.toNat ∧ y.toNat < H) :
    n = 0 ∨ L ≤ p.toNat ∧ p.toNat + n ≤ H := by
  by_cases hn : n = 0
  · exact Or.inl hn
  right
  have h1 := hf p ⟨Nat.le_refl _, by omega⟩
  have hp := p.isLt
  simp only [heapEnd] at hH
  by_cases hw : p.toNat + n - 1 < 2 ^ 64
  · have h2 := hf (BitVec.ofNat 64 (p.toNat + n - 1)) ⟨by rw [BitVec.toNat_ofNat]; omega,
      by rw [BitVec.toNat_ofNat]; omega⟩
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw] at h2
    omega
  · have h2 := hf (BitVec.ofNat 64 (2 ^ 64 - 1)) ⟨by rw [BitVec.toNat_ofNat]; omega,
      by rw [BitVec.toNat_ofNat]; omega⟩
    rw [BitVec.toNat_ofNat] at h2
    omega

section
variable {OA : MachineState → Word → Model.TState → Prop} {s : MachineState} {x : LCtx}
  {u v : MachineState} {Wl : Model.Pcs.WhirLocals} {residual : List E}

/-- Words of the heap allocated between the entry and `u`, the tail keeps. -/
theorem TI.readWords (hpre : VsoPre s) (h : TI OA s x u v Wl residual) {p : Word} {n : ℕ}
    (hn : n = 0 ∨ heapNext s ≤ p.toNat ∧ p.toNat + 8 * n ≤ heapNext u) :
    v.readWords p n = u.readWords p n := by
  have hhu := h.fin.heap.hi
  simp only [heapEnd] at hhu
  rcases hn with h0 | h0
  · subst h0; rfl
  · exact readWords_congr fun i hi ↦ h.keepHeap hpre (by addr_omega [h0.1, h0.2, hi, hhu])
      (by addr_omega [h0.1, h0.2, hi, hhu])

/-- The glued claims' buffer, in the heap from the mark on. -/
theorem VsoFinalIn.gbuf (h : VsoFinalIn OA s x u Wl residual) :
    (vecPtr u (s.getReg .x2 - 664)).toNat % 8 = 0 ∧
      (vecLen u (s.getReg .x2 - 664)).toNat ≤ (vecCap u (s.getReg .x2 - 664)).toNat ∧
      ((vecCap u (s.getReg .x2 - 664)).toNat = 0 ∨ x.L ≤ (vecPtr u (s.getReg .x2 - 664)).toNat ∧
        (vecPtr u (s.getReg .x2 - 664)).toNat + 88 * (vecCap u (s.getReg .x2 - 664)).toNat ≤
          heapNext u) := by
  obtain ⟨hv, -, hlo⟩ := h.glued
  have hr := hv.raw
  simp only [RawVecOk, Buf] at hr
  refine ⟨hr.1, hv.len, ?_⟩
  rcases hlo with h0 | h0
  · left; rw [h0]; rfl
  · rcases hr.2 with h1 | h1
    · left; omega
    · right; exact ⟨h0, by omega⟩

/-- Claim `j`'s address: in the heap from the mark on, its 88 bytes below `u`'s `NEXT`. -/
theorem VsoFinalIn.claimAt (h : VsoFinalIn OA s x u Wl residual) {j : ℕ}
    (hj : j < (vecLen u (s.getReg .x2 - 664)).toNat) :
    (gAddr u s j).toNat = (vecPtr u (s.getReg .x2 - 664)).toNat + 88 * j ∧
      x.L ≤ (gAddr u s j).toNat ∧ (gAddr u s j).toNat + 88 ≤ heapNext u ∧
      (gAddr u s j).toNat % 8 = 0 := by
  obtain ⟨h8, hl, hb⟩ := h.gbuf
  have hhu := h.heap.hi
  simp only [heapEnd] at hhu
  rcases hb with h0 | h0
  · omega
  have e : (gAddr u s j).toNat = (vecPtr u (s.getReg .x2 - 664)).toNat + 88 * j := by
    simp only [gAddr]; rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  refine ⟨e, by omega, by omega, by omega⟩

/-- Claim `j`, as the mirror has it. -/
theorem VsoFinalIn.claim_get (h : VsoFinalIn OA s x u Wl residual) {j : ℕ}
    (hj : j < (vecLen u (s.getReg .x2 - 664)).toNat) :
    ∃ hj' : j < Wl.glued.length, Wl.glued[j] = gluedAt u (gAddr u s j) := by
  have he := h.glued.2.1
  have hl : Wl.glued.length = (vecLen u (s.getReg .x2 - 664)).toNat := by
    rw [← he]; simp [gluedListAt]
  refine ⟨by omega, ?_⟩
  simp only [← he, gluedListAt, gAddr, List.getElem_map, List.getElem_range]

theorem VsoFinalIn.glen (h : VsoFinalIn OA s x u Wl residual) :
    Wl.glued.length = (vecLen u (s.getReg .x2 - 664)).toNat := by
  rw [← h.glued.2.1]; simp [gluedListAt]

/-- The first `j + 1` claims. -/
theorem VsoFinalIn.take_succ (h : VsoFinalIn OA s x u Wl residual) {j : ℕ}
    (hj : j < (vecLen u (s.getReg .x2 - 664)).toNat) :
    Wl.glued.take (j + 1) = Wl.glued.take j ++ [gluedAt u (gAddr u s j)] := by
  obtain ⟨hj', e⟩ := h.claim_get hj
  rw [← e, List.take_add_one, List.getElem?_eq_getElem hj']
  rfl

end

/-- One more claim, folded. -/
theorem gluedFold_snoc (l : List Model.Pcs.GluedClaimRust) (c : Model.Pcs.GluedClaimRust)
    (point : List E) (w0 : E) : gluedFold (l ++ [c]) point w0 = (gluedFold l point w0).bind
      fun acc ↦ (do
        let x ← Model.Pcs.sliceFrom c.foldStart point
        let value ← c.weight.evaluate x
        pure (acc + c.scalar * value)) := by
  simp only [gluedFold, List.foldlM_append, List.foldlM_cons, List.foldlM_nil, bind_pure]
  rfl

/-! ## The loop's states -/

/-- At `0x8000bb58`, claim `j` next: the weight so far `acc` at `S - 184`. -/
structure GLI (OA : MachineState → Word → Model.TState → Prop) (s : MachineState) (x : LCtx)
    (u v w : MachineState) (Wl : Model.Pcs.WhirLocals) (residual tf : List E) (rt w0 : E)
    (j : ℕ) (acc : E) : Prop where
  tb : TB OA s x u v Wl residual tf rt w0
  gs : GS s v w
  pc : w.pc = 0x8000bb58
  jlt : j < (vecLen u (s.getReg .x2 - 664)).toNat
  x8 : w.getReg .x8 = gAddr u s j
  m880 : w.getMem (s.getReg .x2 - 880) =
    vecPtr u (s.getReg .x2 - 664) + vecLen u (s.getReg .x2 - 664) * 88
  fold : gluedFold (Wl.glued.take j) (Wl.folds ++ tf) w0 = some acc
  wt : eAt w (s.getReg .x2 - 184) = acc

/-- At `0x8000baf8`, claim `j` (at `a`)'s value `val` in `x23`, `x25`, `x24`; the claim at
`S - 872`, its scalar at `S - 232`. -/
structure GV (OA : MachineState → Word → Model.TState → Prop) (s : MachineState) (x : LCtx)
    (u v w : MachineState) (Wl : Model.Pcs.WhirLocals) (residual tf : List E) (rt w0 : E)
    (j : ℕ) (a : Word) (acc val : E) : Prop where
  tb : TB OA s x u v Wl residual tf rt w0
  gs : GS s v w
  pc : w.pc = 0x8000baf8
  jlt : j < (vecLen u (s.getReg .x2 - 664)).toNat
  addr : gAddr u s j = a
  m880 : w.getMem (s.getReg .x2 - 880) =
    vecPtr u (s.getReg .x2 - 664) + vecLen u (s.getReg .x2 - 664) * 88
  m872 : w.getMem (s.getReg .x2 - 872) = a
  fold : gluedFold (Wl.glued.take j) (Wl.folds ++ tf) w0 = some acc
  wt : eAt w (s.getReg .x2 - 184) = acc
  scalar : eAt w (s.getReg .x2 - 232) = eAt u (a + 56)
  value : E.ofLimbs (BF64.ofBitVec (w.getReg .x23)) (BF64.ofBitVec (w.getReg .x25))
    (BF64.ofBitVec (w.getReg .x24)) = val
  eval : ∃ xs, Model.Pcs.sliceFrom (gluedAt u a).foldStart (Wl.folds ++ tf) = some xs ∧
    (gluedAt u a).weight.evaluate xs = some val

end Rv64Verifier.Proofs.Pcs.Vso
