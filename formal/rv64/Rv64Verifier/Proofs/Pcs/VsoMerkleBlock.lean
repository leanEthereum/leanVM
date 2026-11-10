import Rv64Verifier.Proofs.Pcs.VsoMerkleKeep

/-!
# `verify_stacked_opening`'s Merkle checks: what they need, and the scans

`MerkleIn` is what the level's earlier steps establish at `0x8000aa14`: the front's inputs, the
function's invariant, the root's pointer at `S - 840`, the queries (`s10` of them, from
`[S - 824]`) and, if a phase is left, the phase `PhaseOk`. `MerkleOut` is the state at
`0x8000b0dc`: the paths and their count in `s6`/`s4`, what the checks wrote (`MW`), the spills,
and the phase's shape, leaf indices and roots as `merkleRust` checks them. `merkle_err` takes an
`Err` to the function's exit with the invariant; `merkle_scans` runs the front and both scans.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- The `Vec` at `a` of `k`-byte elements: empty, or a `Clear` region. -/
def BufOk (s u : MachineState) (a : Word) (k : ℕ) : Prop :=
  (vecLen u a).toNat = 0 ∨ Region (vecPtr u a) (k * (vecLen u a).toNat) ∧
    Clear s (heapNext u) (vecPtr u a) (k * (vecLen u a).toNat)

/-- The phase with header `H`: the header, the paths, the leaves and the siblings `Clear`. -/
structure PhaseOk (s u : MachineState) (H : Word) : Prop where
  hdr : Clear s (heapNext u) H 24
  paths : BufOk s u H 56
  leaves : ∀ j < (vecLen u H).toNat, BufOk s u (vecPtr u H + BitVec.ofNat 64 (56 * j)) 8
  sibs : ∀ j < (vecLen u H).toNat, SibOk s u (vecPtr u H + BitVec.ofNat 64 (56 * j) + 24)

/-- The leaf's width, `lanes` at level `0` and `3 lanes` deeper. -/
def widthW (ℓ fc : ℕ) : Word := (if ℓ = 0 then 1 else 3 : Word) <<< (fc % 64)

/-- **At `0x8000aa14`**, what the Merkle checks need. -/
structure MerkleIn (s u : MachineState) (ℓ fc : ℕ) : Prop where
  front : FrontIn s u ℓ fc
  hℓ : ℓ < 2 ^ 64
  hfc : fc < 2 ^ 64
  inv : InvR s u (u.getMem nextAddr)
  root : u.getMem (s.getReg .x2 - 840) = s.getReg .x11
  queries : (u.getReg .x26).toNat = 0 ∨
    Region (u.getMem (s.getReg .x2 - 824)) (8 * (u.getReg .x26).toNat) ∧
      Clear s (heapNext u) (u.getMem (s.getReg .x2 - 824)) (8 * (u.getReg .x26).toNat)
  phase : (u.getMem (s.getReg .x10 + 352)).toNat < (u.getMem (u.getMem (s.getReg .x10) + 40)).toNat →
    PhaseOk s u (phaseH s u)
  /-- The running quadratic's length, in `s7` as at `S - 808`. -/
  x23 : u.getReg .x23 = u.getMem (s.getReg .x2 - 808)

/-- **At `0x8000b0dc`**, after the Merkle checks from `u`. -/
structure MerkleOut (s u w : MachineState) (ℓ fc : ℕ) : Prop where
  pc : w.pc = 0x8000b0dc
  sp : w.getReg .x2 = s.getReg .x2 - 1040
  inv : InvR s w (w.getMem nextAddr)
  fr : DFrame u w (MW s (heapNext u) (heapNext w))
  mono : heapNext u ≤ heapNext w
  regs : ∀ r ∈ [Reg.x9, .x26], w.getReg r = u.getReg r
  x20 : w.getReg .x20 = vecLen u (phaseH s u)
  x22 : w.getReg .x22 = vecPtr u (phaseH s u)
  hdr : (u.getMem (s.getReg .x10 + 352)).toNat < (u.getMem (u.getMem (s.getReg .x10) + 40)).toNat
  off : w.getMem (s.getReg .x10 + 352) = u.getMem (s.getReg .x10 + 352) + 1
  s16 : w.getMem (s.getReg .x2 - 1008) = BitVec.ofNat 64 ℓ + 1
  s19 : w.getMem (s.getReg .x2 - 1000) = u.getReg .x19
  s18 : w.getMem (s.getReg .x2 - 992) = u.getReg .x18
  s25 : w.getMem (s.getReg .x2 - 984) = u.getReg .x25
  s24 : w.getMem (s.getReg .x2 - 976) = u.getReg .x24
  count : vecLen u (phaseH s u) = u.getReg .x26
  scanned : Scanned u (vecPtr u (phaseH s u)) (u.getMem (s.getReg .x2 - 824)) (u.getReg .x26).toNat
    (widthW ℓ fc) (u.getReg .x8)
  roots : ∀ i < (u.getReg .x26).toNat,
    PathRoot u (vecPtr u (phaseH s u) + BitVec.ofNat 64 (56 * i)) (s.getReg .x11)
  /-- `s7` as `S - 808` was at the checks' start. -/
  x23 : w.getReg .x23 = u.getMem (s.getReg .x2 - 808)

/-- **An `Err` of the Merkle checks**: the function's exit, the invariant kept. -/
theorem merkle_err {s u v : MachineState} (hpre : VsoPre s) (hinv : InvR s u (u.getMem nextAddr))
    (hu : u.getReg .x2 = s.getReg .x2 - 1040) (hsp : v.getReg .x2 = s.getReg .x2 - 1040)
    (hpc : v.pc = 0x8000b830 ∨ v.pc = 0x8000b83c ∨ v.pc = 0x8000b860 ∨ v.pc = 0x8000b8d4)
    (fr : DFrame u v (MW s (heapNext u) (heapNext v))) (heap : HeapOk v)
    (mono : heapNext u ≤ heapNext v) : ∃ w, Reaches Image.code v w ∧ FailR s w := by
  have hv := MW.inv hpre hinv fr heap mono (hsp.trans hu.symm)
  obtain ⟨w, r, pc, ne, sp, m⟩ := errTail hpre hsp hpc
  exact ⟨w, r, Or.inr ⟨pc, ne, _, Inv.same' hv m sp⟩⟩

/-- The scans' checks, from the front's end `t`, hold of `u`. -/
theorem Scanned.keep {s u t : MachineState} {P Q : Word} {n : ℕ} {lw sc : Word} (hpre : VsoPre s)
    (hu : HeapOk u) (hf : DFrame u t (MY s))
    (hp : n = 0 ∨ Region P (56 * n) ∧ Clear s (heapNext u) P (56 * n))
    (hq : n = 0 ∨ Region Q (8 * n) ∧ Clear s (heapNext u) Q (8 * n)) (h : Scanned t P Q n lw sc) :
    Scanned u P Q n lw sc := by
  intro i hi
  obtain ⟨e1, e2, e3⟩ := h i hi
  rcases hp with h0 | ⟨hR, hC⟩
  · omega
  rcases hq with h0 | ⟨hQR, hQC⟩
  · omega
  have hRb := Region.bounds hR
  have hQb := Region.bounds hQR
  have hF := MY.toMW hf (heapNext u) (heapNext u)
  have k (x : Word) (h1 : P.toNat + 56 * i ≤ x.toNat) (h2 : x.toNat + 8 ≤ P.toNat + 56 * i + 56) :
      t.getMem x = u.getMem x :=
    hC.keep hpre hF hu.hi (by omega) (by omega) (by
      have : 56 * i + 56 ≤ 56 * n := by omega
      omega)
  refine ⟨?_, ?_, ?_⟩
  · rw [← k _ (by addr_omega [hRb, hi]) (by addr_omega [hRb, hi])]; exact e1
  · rw [← k _ (by addr_omega [hRb, hi]) (by addr_omega [hRb, hi])]; exact e2
  · rw [← k _ (by addr_omega [hRb, hi]) (by addr_omega [hRb, hi]),
      ← hQC.keep hpre hF hu.hi (by omega) (by addr_omega [hQb, hi]) (by addr_omega [hQb, hi])]
    exact e3

/-- The scans' end at `0x8000aad8`, from the front's end `t`. -/
structure Scans (s u t v : MachineState) (ℓ fc : ℕ) : Prop where
  front : Front s u t ℓ fc
  pc : v.pc = 0x8000aad8
  mem : ∀ a, v.getMem a = t.getMem a
  regs : ∀ r ∈ KS2, v.getReg r = t.getReg r
  count : vecLen u (phaseH s u) = u.getReg .x26
  scanned : Scanned u (vecPtr u (phaseH s u)) (u.getMem (s.getReg .x2 - 824)) (u.getReg .x26).toNat
    (widthW ℓ fc) (u.getReg .x8)

/-- **The front and both scans**: an `Err`, or the scans' end. -/
theorem merkle_scans {s u : MachineState} {ℓ fc : ℕ} (hpre : VsoPre s) (hm : MerkleIn s u ℓ fc) :
    ∃ v, Reaches Image.code u v ∧ (FailR s v ∨ ∃ t, Scans s u t v ℓ fc) := by
  have hb := bounds hpre
  have hT := Region.bounds hpre.self.ok.self
  have hIs := hpre.self.stack
  rw [stackLo_vso, vso_stack] at hIs
  have hu := hm.inv.heap hpre.heap
  obtain ⟨t, r1, ht⟩ := front hpre hm.front hm.hℓ hm.hfc
  rcases ht with ⟨pc, sp, m⟩ | hF
  · have hn : heapNext t = heapNext u := by simp only [heapNext, m]
    obtain ⟨w, r2, hw⟩ := merkle_err hpre hm.inv hm.front.sp sp (Or.inr (Or.inr (Or.inl pc)))
      (DFrame.of_same m _) ⟨hn ▸ hu.lo, hn ▸ hu.hi⟩ (le_of_eq hn.symm)
    exact ⟨w, r1.trans r2, Or.inl hw⟩
  have hP := hm.phase hF.hdr
  have frT : DFrame u t (MY s) := hF.fr.mono fun _ h ↦ Or.inl h
  have hnT := MY.next hpre frT
  have hQ : t.getMem (s.getReg .x2 - 824) = u.getMem (s.getReg .x2 - 824) :=
    hF.fr _ fun i hi hw ↦ by addr_omega [hw, hi, hb, hIs, hT]
  have hpath : (vecLen u (phaseH s u)).toNat = 0 ∨
      Region (vecPtr u (phaseH s u)) (56 * (vecLen u (phaseH s u)).toNat) ∧
        Clear s (heapNext u) (vecPtr u (phaseH s u)) (56 * (vecLen u (phaseH s u)).toNat) := hP.paths
  have hPn : (vecPtr u (phaseH s u)).toNat + 56 * (vecLen u (phaseH s u)).toNat < 2 ^ 64 := by
    rcases hpath with h0 | ⟨hR, -⟩
    · rw [h0]; exact (vecPtr u (phaseH s u)).isLt
    · have := Region.bounds hR; omega
  have hv : ∀ j < (vecLen u (phaseH s u)).toNat,
      Region (vecPtr u (phaseH s u) + BitVec.ofNat 64 (56 * j)) 56 := by
    intro j hj
    rcases hpath with h0 | ⟨hR, -⟩
    · omega
    exact region_sub hR (56 * j) 56 (by omega) (by omega)
  have x26 : t.getReg .x26 = u.getReg .x26 := hF.regs .x26 (by decide)
  obtain ⟨v, r2, m2, k2, hv2⟩ := scans (N := vecLen u (phaseH s u)) hpre hF.pc hF.sp (hQ.trans rfl)
    hPn hv (by rw [x26]; exact hm.queries.imp id fun h ↦ h.1) hF.x10 hF.x11 hF.x13 hF.x14 hF.x22
  have frV : DFrame u v (MY s) := frT.trans (DFrame.of_same m2 _) fun _ h ↦ h
  have hnV := MY.next hpre frV
  rcases hv2 with pc | pc | ⟨pc, hN, hS⟩
  · obtain ⟨w, r3, hw⟩ := merkle_err hpre hm.inv hm.front.sp (by rw [k2 .x2 (by decide), hF.sp])
      (Or.inl pc) (MY.toMW frV _ _) ⟨hnV ▸ hu.lo, hnV ▸ hu.hi⟩ (le_of_eq hnV.symm)
    exact ⟨w, r1.trans (r2.trans r3), Or.inl hw⟩
  · obtain ⟨w, r3, hw⟩ := merkle_err hpre hm.inv hm.front.sp (by rw [k2 .x2 (by decide), hF.sp])
      (Or.inr (Or.inl pc)) (MY.toMW frV _ _) ⟨hnV ▸ hu.lo, hnV ▸ hu.hi⟩ (le_of_eq hnV.symm)
    exact ⟨w, r1.trans (r2.trans r3), Or.inl hw⟩
  have hcount : vecLen u (phaseH s u) = u.getReg .x26 := hN.trans x26
  refine ⟨v, r1.trans r2, Or.inr ⟨t, hF, pc, m2, k2, hcount, ?_⟩⟩
  have hS' := Scanned.keep hpre hu frT (by exact hpath) (by rw [hcount]; exact hm.queries) hS
  rw [hF.x12, hF.regs .x8 (by decide), hcount] at hS'
  exact hS'

end Rv64Verifier.Proofs.Pcs.Vso
