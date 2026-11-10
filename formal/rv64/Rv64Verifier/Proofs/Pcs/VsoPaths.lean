import Rv64Verifier.Proofs.Pcs.VsoPathTail

/-!
# `verify_stacked_opening`'s Merkle checks: the path loop

A phase's `n` paths from `P`, 56 bytes apart, `E = P + 56 n` past the last: `path_step` takes path
`j` from `0x8000ab38` to `0x8000ab2c`, which goes on to path `j + 1` at `0x8000ab38` or, after the
last, to `0x8000b0d0`, every path's root checked (`paths_loop`).
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- **A path.** -/
theorem path_step (hT : TryAllocZeroedSpec) (hRF : ReserveFastSpec 0x8000c898)
    (hM : Runtime.MemcpySpec 0x800126e4) (hK : KeccakHashSpec) (hC : MemcmpSpec)
    {s u0 u : MachineState} {p E R : Word} (hpre : VsoPre s) (hp : PathOk s u0 p)
    (hR : RootOk s u0 R) (hin : PathIn s u0 p E u) :
    ∃ w, Reaches Image.code u w ∧ (Dead Image.code w ∨ PathOut s u0 p E R u w) := by
  obtain ⟨w1, r1, hd | ⟨B, ha⟩⟩ := allocLeaf hT hRF hpre hp hin
  · exact ⟨w1, r1, Or.inl hd⟩
  obtain ⟨w2, r2, hd | hh⟩ := copyHash hM hK hpre hp hin ha
  · exact ⟨w2, r1.trans r2, Or.inl hd⟩
  obtain ⟨w3, r3, hv⟩ := pathTail hM hK hC hpre hp hR hin hh
  exact ⟨w3, r1.trans (r2.trans r3), hv⟩

/-- What the path loop did since `u0`. -/
structure PathsFr (s u0 w : MachineState) : Prop where
  sp : w.getReg .x2 = s.getReg .x2 - 1040
  fr : DFrame u0 w (PW s (heapNext u0) (heapNext w))
  heap : HeapOk w
  mono : heapNext u0 ≤ heapNext w

theorem addr56 (P : Word) (j : ℕ) :
    P + BitVec.ofNat 64 (56 * j) + 56 = P + BitVec.ofNat 64 (56 * (j + 1)) := by
  rw [BitVec.add_assoc, show (56 : Word) = BitVec.ofNat 64 56 from rfl, ← BitVec.ofNat_add,
    show 56 * j + 56 = 56 * (j + 1) by ring]

/-- **The path loop**, from path `j` on. -/
theorem paths_loop (hT : TryAllocZeroedSpec) (hRF : ReserveFastSpec 0x8000c898)
    (hM : Runtime.MemcpySpec 0x800126e4) (hK : KeccakHashSpec) (hC : MemcmpSpec)
    {s u0 : MachineState} {P R : Word} {n : ℕ} (hpre : VsoPre s)
    (hPn : P.toNat + 56 * n < 2 ^ 64)
    (hps : ∀ j < n, PathOk s u0 (P + BitVec.ofNat 64 (56 * j))) (hR : RootOk s u0 R) :
    ∀ k j u, n - j = k → j < n →
      PathIn s u0 (P + BitVec.ofNat 64 (56 * j)) (P + BitVec.ofNat 64 (56 * n)) u →
      (∀ r ∈ [Reg.x9, .x26], u.getReg r = u0.getReg r) →
      ∃ w, Reaches Image.code u w ∧ (Dead Image.code w ∨ (PathsFr s u0 w ∧
        (w.pc = 0x8000b8d4 ∨ (w.pc = 0x8000b0d0 ∧
          (∀ r ∈ [Reg.x9, .x26], w.getReg r = u0.getReg r) ∧
          w.getReg .x23 = w.getMem (s.getReg .x2 - 808) ∧
          ∀ i, j ≤ i → i < n → PathRoot u0 (P + BitVec.ofNat 64 (56 * i)) R))))
  | 0, j, _, hk, hj, _, _ => absurd hj (by omega)
  | k + 1, j, u, hk, hj, hin, hr => by
    obtain ⟨w, r1, hd | ho⟩ := path_step hT hRF hM hK hC hpre (hps j hj) hR hin
    · exact ⟨w, r1, Or.inl hd⟩
    have frw : DFrame u0 w (PW s (heapNext u0) (heapNext w)) :=
      (hin.fr.mono fun a h ↦ h.mono (Nat.le_refl _) ho.mono).trans ho.fr
        fun a h ↦ h.mono hin.mono (Nat.le_refl _)
    have hmw : heapNext u0 ≤ heapNext w := hin.mono.trans ho.mono
    rcases ho.next with hpc | ⟨hpc, x22, x25, regs, root⟩
    · exact ⟨w, r1, Or.inr ⟨⟨ho.sp, frw, ho.heap, hmw⟩, Or.inl hpc⟩⟩
    obtain ⟨t, r2, h2⟩ := Sym.BlockSpec.reaches b8000ab2c_spec hpc trivial
    have k2 := b8000ab2c_keeps h2
    have m2 := b8000ab2c_mem_same h2
    have hnt : heapNext t = heapNext w := by simp only [heapNext, m2]
    have frt : DFrame u0 t (PW s (heapNext u0) (heapNext t)) := by
      rw [hnt]; exact frw.trans (DFrame.of_same m2 _) fun _ h ↦ h
    have hft : PathsFr s u0 t := ⟨by rw [k2 .x2 (by decide), ho.sp], frt,
      ⟨by rw [hnt]; exact ho.heap.lo, by rw [hnt]; exact ho.heap.hi⟩, by rw [hnt]; exact hmw⟩
    have rt : ∀ r ∈ [Reg.x9, .x26], t.getReg r = u0.getReg r := fun r hm' ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm'
      rcases hm' with rfl | rfl <;> rw [k2 _ (by decide), regs _ (by simp), hr _ (by simp)]
    have hnext : P + BitVec.ofNat 64 (56 * j) + 56 = P + BitVec.ofNat 64 (56 * (j + 1)) :=
      addr56 P j
    have x23t : t.getReg .x23 = t.getMem (s.getReg .x2 - 808) := by
      rw [k2 .x23 (by decide), ho.x23, m2]
    by_cases hlast : j + 1 = n
    · refine ⟨t, r1.trans r2, Or.inr ⟨hft, Or.inr ⟨b8000ab2c_pc_taken h2 (by
        rw [x22, x25, hnext, hlast]), rt, x23t, fun i hi1 hi2 ↦ ?_⟩⟩⟩
      rw [show i = j by omega]
      exact root
    · have hne : P + BitVec.ofNat 64 (56 * (j + 1)) ≠ P + BitVec.ofNat 64 (56 * n) :=
        ne_of_toNat_lt (by rw [toNat_add_ofNat (by omega), toNat_add_ofNat (by omega)]; omega)
      have pc2 := b8000ab2c_pc_not_taken h2 (by rw [x22, x25, hnext]; exact hne)
      have hin' : PathIn s u0 (P + BitVec.ofNat 64 (56 * (j + 1))) (P + BitVec.ofNat 64 (56 * n)) t :=
        { pc := pc2
          sp := hft.sp
          x22 := by rw [b8000ab2c_x22 h2, x22, hnext]
          x5 := by rw [b8000ab2c_x5 h2, x25]
          fr := frt
          heap := hft.heap
          mono := hft.mono
          rodata := hin.rodata.dframe
            (ho.fr.trans (DFrame.of_same m2 (PW s (heapNext u) (heapNext w))) fun _ h ↦ h)
            (PW.rodata (lo := heapNext u) (hi := heapNext w) hpre ho.heap.hi)
          x23 := x23t }
      obtain ⟨v, r3, hv⟩ := paths_loop hT hRF hM hK hC hpre hPn hps hR k (j + 1) t (by omega)
        (by omega) hin' rt
      refine ⟨v, r1.trans (r2.trans r3), ?_⟩
      rcases hv with hd | ⟨hfv, hv⟩
      · exact Or.inl hd
      rcases hv with hpc' | ⟨hpc', rv, x23v, roots⟩
      · exact Or.inr ⟨hfv, Or.inl hpc'⟩
      refine Or.inr ⟨hfv, Or.inr ⟨hpc', rv, x23v, fun i hi1 hi2 ↦ ?_⟩⟩
      rcases Nat.lt_or_ge j i with h | h
      · exact roots i h hi2
      · rw [show i = j by omega]
        exact root

end Rv64Verifier.Proofs.Pcs.Vso
