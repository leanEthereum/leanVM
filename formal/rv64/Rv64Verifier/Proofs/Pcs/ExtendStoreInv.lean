import Rv64Verifier.Proofs.Pcs.ExtendStoreBlk

/-!
# `Vec<StackClaim>::extend_desugared`: the invariant after a push

`store_inv`: after the store, claim `k` is on the `Vec`, `Inv` holds for `k + 1`.
-/

namespace Rv64Verifier.Proofs.Pcs.Extend
open RiscvZkvm.Rv64 Rv64Verifier.Runtime Rv64Verifier.Transcript Rv64Verifier.Pcs
  Rv64Verifier.PcsContracts Rv64Verifier.Model.Pcs LeanVM.Parameters

/-- The store's context: the bounds every part of `store_inv` uses. -/
structure SCtx (s u w t : MachineState) (k : Nat) : Prop where
  hp : Push s u k
  hr : Room s u w k
  hs : Stored s u w t k
  hb : 0xa0000f38 + 464 ≤ (s.getReg .x2).toNat ∧ (s.getReg .x2).toNat ≤ 0xc0000008 ∧
    (s.getReg .x2).toNat % 16 = 0
  v1 : heapNext s ≤ (vecPtr w (s.getReg .x10)).toNat
  v2 : (vecPtr w (s.getReg .x10)).toNat + (vecCap w (s.getReg .x10)).toNat * 88 ≤ heapNext w
  v3 : (vecPtr w (s.getReg .x10)).toNat % 8 = 0
  nx : t.getMem nextAddr = w.getMem nextAddr
  pT : vecPtr t (s.getReg .x10) = vecPtr w (s.getReg .x10)
  cT : vecCap t (s.getReg .x10) = vecCap w (s.getReg .x10)
  lT : (vecLen t (s.getReg .x10)).toNat = (vecLen u (s.getReg .x10)).toNat + 1

theorem sctx {s u w t : MachineState} {k : Nat} (hpre : Walk.ExtendPreE s) (hp : Push s u k)
    (hr : Room s u w k) (hs : Stored s u w t k) : SCtx s u w t k := by
  have hb := sbounds hpre
  have hAb := Region.bounds hpre.self.region
  have hAf := hpre.self.free
  simp only [Outside] at hAf
  have hu' : heapNext s ≤ heapNext u := hp.inv.p.mono
  have hm := hr.mono
  have hwh := hr.heap.hi
  have hroom := hr.room
  obtain ⟨hv1, hv2, hv3⟩ := vbuf hp hr
  have heB : heapNext s ≤ (eNew s u w).toNat ∧ (eNew s u w).toNat + 88 ≤ heapNext w := by
    simp only [eNew]; constructor <;> addr_omega [hv1, hv2, hroom]
  have miss (a : Word) (ha : a.toNat + 8 ≤ (s.getReg .x10).toNat + 16 ∨ (s.getReg .x10).toNat + 24 ≤ a.toNat)
      (h2 : a.toNat + 8 ≤ heapNext s ∨ heapNext w ≤ a.toNat) (h3 : a.toNat + 8 ≤ 2 ^ 64) :
      t.getMem a = w.getMem a :=
    hs.fr.word (fun x hx hw ↦ by
      rcases hw with hw | hw
      · addr_omega [hx, hw, ha, hAb, h3]
      · addr_omega [hx, hw, h2, heB, h3]) h3
  have hlt : (vecLen u (s.getReg .x10)).toNat + 1 < 2 ^ 64 := by
    have := (w.getMem nextAddr).isLt
    simp only [heapNext] at hv2; omega
  refine ⟨hp, hr, hs, hb, hv1, hv2, hv3, miss _ (by addr_omega [hwh, hAf.2]) (by addr_omega [hwh]) (by decide),
    miss _ (by addr_omega [hAb]) (by rcases hAf.1 with h | h <;> addr_omega [h, hAb, hwh]) (by addr_omega [hAb]),
    miss _ (by addr_omega [hAb]) (by rcases hAf.1 with h | h <;> addr_omega [h, hAb, hwh]) (by addr_omega [hAb]), ?_⟩
  have := hs.len
  rw [this, BitVec.toNat_add, Nat.mod_eq_of_lt (by exact hlt)]
  rfl

theorem SCtx.frame {s u w t : MachineState} {k : Nat} (hpre : Walk.ExtendPreE s) (c : SCtx s u w t k) :
    DFrame u t (StepW s u (t.getMem nextAddr)) := by
  have hroom := c.hr.room
  have hAb := Region.bounds hpre.self.region
  have hv2 := c.v2
  refine (c.hr.fr.mono fun a h ↦ h.mono (by rw [c.nx])).trans c.hs.fr fun a h ↦ ?_
  rcases h with h | h
  · exact Or.inl (by addr_omega [h, hAb])
  · rcases c.hr.moved with ⟨hP, hC⟩ | ⟨hn, -⟩
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))
      rw [hP, hC] at hv2; rw [hC] at hroom
      simp only [eNew, hP] at h
      addr_omega [h, hroom, hv2]
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
      simp only [NewBuf] at hn
      simp only [eNew] at h
      rw [c.nx]
      constructor <;> addr_omega [h, hn, hroom, hv2]

theorem SCtx.slot {s u w t : MachineState} {k : Nat} (hpre : Walk.ExtendPreE s) (c : SCtx s u w t k)
    {i : Nat} (hi : i ≤ (vecLen u (s.getReg .x10)).toNat) :
    Safe s t (vecPtr w (s.getReg .x10) + BitVec.ofNat 64 (88 * i)) 88 := by
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
  have hnt : heapNext t = heapNext w := by simp only [heapNext, c.nx]
  have v1 := c.v1
  have v2 := c.v2
  have v3 := c.v3
  right
  refine ⟨heap_region (by addr_omega [v1, v2, hlo, hroom, hi])
      (by simp only [heapEnd] at hwh ⊢; addr_omega [v1, v2, hwh, hroom, hi])
      (by addr_omega [v1, v2, v3, hroom, hi]), ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rcases hAf.1 with h | h <;> addr_omega [h, v1, v2, hroom, hi, hwh, hAb]
  · rcases hIf.1 with h | h <;> addr_omega [h, v1, v2, hroom, hi, hwh, hIb]
  · rw [hK]; addr_omega [v1, v2, hroom, hi, hwh, hb]
  · addr_omega [v1, v2, hroom, hi, hwh]
  · left; rw [hnt]; addr_omega [v1, v2, hroom, hi]
  · simp only [spareLo, spareLen, c.pT, c.cT, c.lT]; addr_omega [v1, v2, hroom, hi]

theorem SCtx.spare {s u w t : MachineState} {k : Nat} (c : SCtx s u w t k) :
    spareLen t (s.getReg .x10) = 0 ∨
      ((spareLo u (s.getReg .x10)).toNat ≤ (spareLo t (s.getReg .x10)).toNat ∧
        (spareLo t (s.getReg .x10)).toNat + spareLen t (s.getReg .x10) ≤
          (spareLo u (s.getReg .x10)).toNat + spareLen u (s.getReg .x10)) ∨
      (heapNext u ≤ (spareLo t (s.getReg .x10)).toNat ∧
        (spareLo t (s.getReg .x10)).toNat + spareLen t (s.getReg .x10) ≤ heapEnd) := by
  have hroom := c.hr.room
  have hwh := c.hr.heap.hi
  have hv2 := c.v2
  rcases c.hr.moved with ⟨hP, hC⟩ | ⟨hn, -⟩
  · right; left
    rw [hP, hC] at hv2; rw [hC] at hroom
    simp only [spareLo, spareLen, c.pT, c.cT, c.lT, hP, hC]
    constructor <;> addr_omega [hv2, hroom]
  · right; right
    simp only [NewBuf] at hn
    simp only [spareLo, spareLen, c.pT, c.cT, c.lT]
    constructor <;> addr_omega [hn, hv2, hroom, hwh]

end Rv64Verifier.Proofs.Pcs.Extend
