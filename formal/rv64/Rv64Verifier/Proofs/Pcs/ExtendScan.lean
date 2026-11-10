import Rv64Verifier.Proofs.Pcs.ExtendInv

/-!
# `Vec<StackClaim>::extend_desugared`: the scan

From the loop's head (`0x80009c64`, `Head`) to the next claim to push (`0x80009cdc`, `Push`) or
the end (`0x80009d7c`, `Exit`): `0x80009c64` and `0x80009c70` test the claim at `s9`, the loop at
`0x80009ca4` the ones after it, a claim out of the placements' bounds trapping at `0x80009d78`.
-/

namespace Rv64Verifier.Proofs.Pcs.Extend
open RiscvZkvm.Rv64 Rv64Verifier.Runtime Rv64Verifier.Transcript Rv64Verifier.Pcs
  Rv64Verifier.PcsContracts Rv64Verifier.Model.Pcs Rv64Verifier.Blocks.F37
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- Claim `k`'s address, its column. -/
@[rv_addr] def clAt (s : MachineState) (k : Nat) : Word := itCur s + BitVec.ofNat 64 (56 * k)
def colAt (s : MachineState) (k : Nat) : Nat := (s.getMem (clAt s k + 24)).toNat
/-- Its placement's address. -/
def plAt (s : MachineState) (k : Nat) : Word := placementsPtr s + BitVec.ofNat 64 (24 * colAt s k)

/-- At the loop's head, claim `j` next. -/
structure Head (s u : MachineState) (j : Nat) : Prop where
  inv : Inv s u j
  pc : u.pc = 0x80009c64
  x25 : u.getReg .x25 = clAt s j
  lt : j < itCount s

/-- At `0x80009cdc`, claim `k` to push. -/
structure Push (s u : MachineState) (k : Nat) : Prop where
  inv : Inv s u k
  pc : u.pc = 0x80009cdc
  x18 : u.getReg .x18 = clAt s k
  x25 : u.getReg .x25 = clAt s (k + 1)
  x13 : u.getReg .x13 = plAt s k
  col : colAt s k < placementsLen s
  bit : s.getMem (plAt s k) &&& 1 ≠ 0
  lt : k < itCount s

/-- At `0x80009d7c`, every claim done. -/
structure Exit (s u : MachineState) : Prop where
  inv : Inv s u (itCount s)
  pc : u.pc = 0x80009d7c

/-- In the loop after claim `j`, at `0x80009ca4`, claim `j` next. -/
structure Skip (s u : MachineState) (j : Nat) : Prop where
  inv : Inv s u j
  pc : u.pc = 0x80009ca4
  x12 : u.getReg .x12 = clAt s j
  x10 : u.getReg .x10 = s.getMem (itLayout s + 112)
  x11 : u.getReg .x11 = placementsPtr s
  lt : j < itCount s

theorem htrap : Image.code.fetch 0x80009d78 = none :=
  Option.isNone_iff_eq_none.mp (by decide +kernel)

/-- An `Inv` across a block that writes nothing and keeps the loop's registers. -/
theorem Inv.congr {s u v : MachineState} {j : Nat} (h : Inv s u j)
    (hm : ∀ a, v.getMem a = u.getMem a) (hsp : v.getReg .x2 = u.getReg .x2)
    (hr : ∀ r ∈ [Reg.x8, .x9, .x19, .x20, .x21, .x22, .x23, .x24], v.getReg r = u.getReg r) :
    Inv s v j := by
  have hn : heapNext v = heapNext u := by simp only [heapNext, hm]
  have hP : vecPtr v (s.getReg .x10) = vecPtr u (s.getReg .x10) := hm _
  have hL : vecLen v (s.getReg .x10) = vecLen u (s.getReg .x10) := hm _
  have hC : vecCap v (s.getReg .x10) = vecCap u (s.getReg .x10) := hm _
  have hsl : spareLo v (s.getReg .x10) = spareLo u (s.getReg .x10) := by
    simp only [spareLo, hP, hL]
  have hsn : spareLen v (s.getReg .x10) = spareLen u (s.getReg .x10) := by
    simp only [spareLen, hC, hL]
  have hS (a : Word) (n : Nat) (ha : Safe s u a n) : Safe s v a n := by
    simp only [Safe, hn, hsl, hsn]; exact ha
  have hcl (i : Nat) (hi : i < (vecLen u (s.getReg .x10)).toNat) :=
    claim_move (u := u) (v := v) (P := Safe s u) (Q := Safe s v) (fun _ _ ↦ hm _) (h.safe i hi)
      (fun _ _ _ ↦ (DFrame.of_same hm fun _ ↦ False).eListAt fun _ _ h ↦ h) hS
      (hS _ _ (h.safe i hi).1)
  refine ⟨?_, (hr .x8 (by simp)).trans h.x8, (hr .x9 (by simp)).trans h.x9,
    (hr .x19 (by simp)).trans h.x19, (hr .x20 (by simp)).trans h.x20,
    (hr .x21 (by simp)).trans h.x21, (hr .x22 (by simp)).trans h.x22,
    (hr .x23 (by simp)).trans h.x23, (hr .x24 (by simp)).trans h.x24, ?_, ?_, ?_, ?_, h.le, ?_, ?_⟩
  · rw [hm]; exact h.p.same hm hsp fun r hr ↦ by simp at hr
  · exact ⟨by simp only [RawVecOk, Buf, hP, hC, hn]; exact h.vec.raw,
      by rw [hL, hC]; exact h.vec.len⟩
  · exact h.buf.imp (fun e ↦ by rw [hL, hC]; exact e)
      fun e ↦ by simp only [NewBuf, hP, hC, hn]; exact e
  · intro i hi
    rw [hL] at hi
    rw [hP]
    exact (hcl i hi).2
  · rw [← h.value, stackClaimsAt, stackClaimsAt, hP, hL]
    exact claimsAt_congr fun i hi ↦ (hcl i hi).1
  · intro i hi k hk
    rw [hP, hm]
    exact h.words i hi k hk
  · intro i h1 h2
    rw [hL] at h2
    exact heapBuf_move (hm _) (hm _) (le_of_eq hn.symm) (by rw [hP]; exact h.added i h1 h2)

/-- Claim `j` skipped. -/
theorem Inv.skip {s u : MachineState} {j : Nat} (h : Inv s u j) (hj : j < itCount s)
    (hn : onStackS s (columnClaimAt s (clAt s j)) = none) : Inv s u (j + 1) :=
  { h with
    value := by
      simp only [clAt] at hn
      rw [h.value, columnClaimsAt_succ, List.filterMap_append, List.filterMap_cons_none hn,
        List.filterMap_nil, List.append_nil]
    le := hj }

/-! ## Reads -/

/-- The bounds the scan needs. -/
structure Facts (s : MachineState) : Prop where
  claims : Region (itCur s) (56 * itCount s)
  layout : Region (itLayout s) 192
  stop : (itEnd s).toNat = (itCur s).toNat + 56 * itCount s

theorem facts {s : MachineState} (hpre : Walk.ExtendPreE s) (hc : 0 < itCount s) : Facts s := by
  refine ⟨hpre.claims.region.resolve_left (by omega), hpre.layout.region.resolve_left (by decide), ?_⟩
  have := hpre.bounds
  simp only [itCount] at hc ⊢
  omega

theorem clAt_end {s : MachineState} (hf : Facts s) {m : Nat} (hm : m ≤ itCount s) :
    clAt s m = itEnd s ↔ m = itCount s := by
  have hb := Region.bounds hf.claims
  have he := hf.stop
  constructor
  · intro h
    addr_omega [h, hb, he, hm]
  · intro h
    addr_omega [h, hb, he, hm]

theorem rd_col {s u : MachineState} {j k : Nat} (hpre : Walk.ExtendPreE s) (hf : Facts s) (h : Inv s u j)
    (hk : k < itCount s) : u.getMem (clAt s k + 24) = s.getMem (clAt s k + 24) := by
  have hb := Region.bounds hf.claims
  exact h.read hpre.claims hpre.claimsOff (by addr_omega [hb, hk]) (by addr_omega [hb, hk])

theorem rd_layout {s u : MachineState} {j : Nat} (hpre : Walk.ExtendPreE s) (hf : Facts s)
    (h : Inv s u j) {o : Word} (ho : o.toNat + 8 ≤ 192) :
    u.getMem (itLayout s + o) = s.getMem (itLayout s + o) := by
  have hb := Region.bounds hf.layout
  exact h.read hpre.layout hpre.layoutOff (by addr_omega [hb, ho]) (by addr_omega [hb, ho])

theorem pl_region {s : MachineState} (hpre : Walk.ExtendPreE s) {k : Nat}
    (hk : colAt s k < placementsLen s) : Region (placementsPtr s) (24 * placementsLen s) :=
  hpre.placements.region.resolve_left (by omega)

theorem rd_pl {s u : MachineState} {j k : Nat} (hpre : Walk.ExtendPreE s) (h : Inv s u j)
    (hk : colAt s k < placementsLen s) : u.getMem (plAt s k) = s.getMem (plAt s k) := by
  have hb := Region.bounds (pl_region hpre hk)
  exact h.read hpre.placements hpre.placementsOff (by simp only [plAt]; addr_omega [hb, hk])
    (by simp only [plAt]; addr_omega [hb, hk])

/-- The machine's placement address, `ptr + (c << 4) + (c << 3)`. -/
theorem pl_eq {s : MachineState} (k : Nat) :
    placementsPtr s + (s.getMem (clAt s k + 24) * 16 + s.getMem (clAt s k + 24) * 8) = plAt s k := by
  rw [mul24]; rfl

end Rv64Verifier.Proofs.Pcs.Extend
