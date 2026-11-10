import Rv64Verifier.Proofs.Pcs.ExtendStoreInv

/-!
# `Vec<StackClaim>::extend_desugared`: the claims after a push

The old claims kept (or moved by `grow_amortized`), the new one claim `k`'s `on_stack`, and
`store_inv`.
-/

namespace Rv64Verifier.Proofs.Pcs.Extend
open RiscvZkvm.Rv64 Rv64Verifier.Runtime Rv64Verifier.Transcript Rv64Verifier.Pcs
  Rv64Verifier.PcsContracts Rv64Verifier.Model.Pcs LeanVM.Parameters

theorem SCtx.heapT {s u w t : MachineState} {k : Nat} (c : SCtx s u w t k) :
    heapNext u ≤ heapNext t := by
  rw [show heapNext t = heapNext w by simp only [heapNext, c.nx]]; exact c.hr.mono

theorem SCtx.old {s u w t : MachineState} {k : Nat} (hpre : ExtendPre s) (c : SCtx s u w t k)
    {i : Nat} (hi : i < (vecLen u (s.getReg .x10)).toNat) :
    stackClaimAt t (vecPtr w (s.getReg .x10) + BitVec.ofNat 64 (88 * i)) =
        stackClaimAt u (vecPtr u (s.getReg .x10) + BitVec.ofNat 64 (88 * i)) ∧
      ClaimRegions (Safe s t) t (vecPtr w (s.getReg .x10) + BitVec.ofNat 64 (88 * i)) := by
  have hI := c.hp.inv
  have hX := c.frame hpre
  have hnt : (t.getMem nextAddr).toNat ≤ heapEnd := by rw [c.nx]; exact c.hr.heap.hi
  have hsafe := hI.safe i hi
  have hroom := c.hr.room
  have hAb := Region.bounds hpre.self.region
  have hAf := hpre.self.free
  simp only [Outside] at hAf
  have hwh := c.hr.heap.hi
  have v1 := c.v1
  have v2 := c.v2
  refine claim_move (fun j hj ↦ ?_) hsafe (fun a m hm ↦ hX.eList (fun x hx ↦ hm.miss hnt x hx) (by
      rcases hm.bound with h | h
      · left; omega
      · right; omega)) (fun a n h ↦ h.next c.heapT c.spare) (c.slot hpre hi.le)
  have hwt : t.getMem (vecPtr w (s.getReg .x10) + BitVec.ofNat 64 (88 * i) + BitVec.ofNat 64 (8 * j)) =
      w.getMem (vecPtr w (s.getReg .x10) + BitVec.ofNat 64 (88 * i) + BitVec.ofNat 64 (8 * j)) :=
    c.hs.fr.word (fun x hx hw ↦ by
      rcases hw with hw | hw
      · rcases hAf.1 with h | h <;> addr_omega [hx, hw, h, v1, v2, hroom, hi, hj, hwh, hAb]
      · simp only [eNew] at hw; addr_omega [hx, hw, v1, v2, hroom, hi, hj])
      (by addr_omega [v1, v2, hroom, hi, hj])
  rw [hwt]
  rcases c.hr.moved with ⟨hP, hC⟩ | ⟨-, hmv⟩
  · rw [hP]
    have hsb : (vecPtr u (s.getReg .x10) + BitVec.ofNat 64 (88 * i)).toNat + 88 ≤ 0xc0000000 := by
      rcases hsafe.1.bound with h | h
      · omega
      · exact h
    exact c.hr.fr.word (fun x hx ↦ hsafe.1.miss hwh x (by addr_omega [hx, hsb, hj]))
      (by addr_omega [hsb, hj])
  · exact hmv i hi j hj

theorem SCtx.new {s u w t : MachineState} {k : Nat} (hpre : ExtendPre s) (c : SCtx s u w t k) :
    stackClaimAt t (eNew s u w) = ⟨.eq (stackPt s k), eAt s (clAt s k + 32)⟩ ∧
      ClaimRegions (Safe s t) t (eNew s u w) := by
  have hroom := c.hr.room
  have hb := c.hb
  have hAb := Region.bounds hpre.self.region
  have hAf := hpre.self.free
  simp only [Outside] at hAf
  have hIf := hpre.iter.free
  simp only [Outside] at hIf
  have hIb := Region.bounds hpre.iter.region
  have hlo := hpre.heap.lo
  simp only [heapStart] at hlo
  have hwh := c.hr.heap.hi
  have hu' : heapNext s ≤ heapNext u := c.hp.inv.p.mono
  have hnt : heapNext t = heapNext w := by simp only [heapNext, c.nx]
  have v1 := c.v1
  have v2 := c.v2
  have hpa := c.hr.ptApart
  have hpb := c.hr.pt.buf
  have hpl := c.hr.pt.vec.len
  simp only [NewBuf] at hpb
  have n1 : eNew s u w + 8 + 8 = eNew s u w + 16 := add_lit _ _ _ _ rfl
  have n2 : eNew s u w + 8 + 16 = eNew s u w + 24 := add_lit _ _ _ _ rfl
  have hP8 : vecPtr t (eNew s u w + 8) = vecPtr w (s.getReg .x2 - 184) := by
    unfold vecPtr; rw [n1, c.hs.p16]
  have hL8 : vecLen t (eNew s u w + 8) = vecLen w (s.getReg .x2 - 184) := by
    unfold vecLen; rw [n2, c.hs.p24]
  have hv : vecEs t (eNew s u w + 8) = stackPt s k := by
    rw [← c.hr.pt.elems]
    unfold vecEs
    rw [hP8, hL8]
    rcases hpb with ⟨-, h0 | ⟨h1, h2⟩⟩
    · have : (vecLen w (s.getReg .x2 - 184)).toNat = 0 := by omega
      rw [this]; rfl
    · exact c.hs.fr.eList (fun x hx hw ↦ by
        rcases hw with hw | hw
        · rcases hAf.1 with h | h <;> addr_omega [hx, hw, h, h1, h2, hpl, hu', hwh, hAb]
        · simp only [eNew] at hw
          simp only [Apart] at hpa
          addr_omega [hx, hw, hpa, hpl, hroom, h1, h2, v1, v2]) (Or.inr (by addr_omega [h2, hpl, hwh]))
  have hval : eAt t (eNew s u w + 64) = eAt s (clAt s k + 32) := by
    rw [← c.hr.val]
    unfold eAt
    rw [c.hs.v64, add_lit _ 64 8 72 rfl, c.hs.v72, add_lit _ 64 16 80 rfl, c.hs.v80]
  constructor
  · simp only [stackClaimAt, stackWeightAt, c.hs.tag, ↓reduceIte, hv, hval]
  · refine ⟨c.slot hpre (Nat.le_refl _), ?_⟩
    simp only [c.hs.tag, ↓reduceIte]
    rw [hP8, hL8]
    rcases hpb with ⟨hal, h0 | ⟨h1, h2⟩⟩
    · left; omega
    · by_cases hz : (vecLen w (s.getReg .x2 - 184)).toNat = 0
      · left; omega
      right
      refine ⟨heap_region (by omega) (by simp only [heapEnd] at hwh ⊢; omega) hal, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
      · rcases hAf.1 with h | h <;> addr_omega [h, h1, h2, hpl, hu', hwh, hAb]
      · rcases hIf.1 with h | h <;> addr_omega [h, h1, h2, hpl, hu', hwh, hIb]
      · rw [hK]; addr_omega [h1, h2, hpl, hwh, hb]
      · addr_omega [h1, h2, hpl, hwh]
      · left; rw [hnt]; omega
      · simp only [Apart] at hpa
        simp only [spareLo, spareLen, c.pT, c.cT, c.lT]
        addr_omega [hpa, hpl, hroom, h1, h2, v1, v2]

/-- **After a push, the invariant for the next claim.** -/
theorem store_inv {s u w t : MachineState} {k : Nat} (hpre : ExtendPre s) (c : SCtx s u w t k) :
    Inv s t (k + 1) := by
  have hI := c.hp.inv
  have hnt : heapNext t = heapNext w := by simp only [heapNext, c.nx]
  have hwh := c.hr.heap.hi
  have hroom := c.hr.room
  have hlo := hpre.heap.lo
  have v1 := c.v1
  have hle : (u.getMem nextAddr).toNat ≤ (t.getMem nextAddr).toNat := c.heapT
  have hend : (t.getMem nextAddr).toNat ≤ heapEnd := by rw [c.nx]; exact hwh
  have hsp : t.getReg .x2 = u.getReg .x2 := by
    rw [c.hs.keep .x2 (by decide), c.hr.sp, hI.p.sp]; rfl
  have kr (r : Reg) (hr : r ∈ [Reg.x8, .x9, .x19, .x20, .x21, .x22, .x23, .x24]) :
      t.getReg r = u.getReg r :=
    (c.hs.keep r ((by decide : [Reg.x8, .x9, .x19, .x20, .x21, .x22, .x23, .x24] ⊆
      [Reg.x2, .x8, .x9, .x19, .x20, .x21, .x22, .x23, .x24, .x25]) hr)).trans (c.hr.keep r hr)
  have hos : onStackS s (columnClaimAt s (itCur s + BitVec.ofNat 64 (56 * k))) =
      some ⟨.eq (stackPt s k), eAt s (clAt s k + 32)⟩ := onStack_some s c.hp.col c.hp.bit
  refine ⟨hI.p.step 104 (by decide) (by have := c.hb; omega) (c.frame hpre)
      (fun a h ↦ stepW_wr hI hle h) (fun a h ↦ stepW_slot hpre hI hend h) rfl hle hend hsp
      (fun r hr ↦ by simp at hr),
    (kr .x8 (by decide)).trans hI.x8, (kr .x9 (by decide)).trans hI.x9,
    (kr .x19 (by decide)).trans hI.x19, (kr .x20 (by decide)).trans hI.x20,
    (kr .x21 (by decide)).trans hI.x21, (kr .x22 (by decide)).trans hI.x22,
    (kr .x23 (by decide)).trans hI.x23, (kr .x24 (by decide)).trans hI.x24,
    ⟨?_, by rw [c.lT, c.cT]; omega⟩, Or.inr ?_, ?_, ?_, c.hp.lt⟩
  · simp only [RawVecOk, Buf, c.pT, c.cT, hnt]
    exact ⟨c.v3, Or.inr ⟨by omega, c.v2⟩⟩
  · simp only [NewBuf, c.pT, c.cT, hnt]
    exact ⟨c.v3, Or.inr ⟨c.v1, c.v2⟩⟩
  · intro i hi
    rw [c.lT] at hi
    rw [c.pT]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact (c.old hpre hi).2
    · exact (c.new hpre).2
  · rw [stackClaimsAt, c.pT, c.lT, claimsAt_succ, claimsAt_congr fun i hi ↦ (c.old hpre hi).1,
      show stackClaimAt t (vecPtr w (s.getReg .x10) +
        BitVec.ofNat 64 (88 * (vecLen u (s.getReg .x10)).toNat)) = _ from (c.new hpre).1,
      show claimsAt u (vecPtr u (s.getReg .x10)) (vecLen u (s.getReg .x10)).toNat =
        stackClaimsAt u (s.getReg .x10) from rfl, hI.value, columnClaimsAt_succ,
      List.filterMap_append, List.filterMap_cons_some hos, List.filterMap_nil, List.append_assoc]

end Rv64Verifier.Proofs.Pcs.Extend
