import Rv64Verifier.Proofs.Pcs.VsoQOuter

/-!
# `verify_stacked_opening`'s level loop: grinding and the queries, whole

From `0x8000a790` to `0x8000a9d8`: the grinding (`grind`), the queries' setup (`qsetup`) and
`sample_queries` (`qloop`). The mirror is `TM.grind 17`, then `sampleQueriesRust` at the level's
block length.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- At `0x8000a9d8`, the level's positions `qs` drawn, from `u` at `0x8000a790` on. -/
structure QOut (s u v : MachineState) (d : ℕ) (qs : List Word) : Prop where
  pc : v.pc = 0x8000a9d8
  sp : v.getReg .x2 = s.getReg .x2 - 1040
  inv : InvR s v (v.getMem nextAddr)
  fr : DFrame u v fun a ↦ GW s a ∨ QW s u v a
  mono : heapNext u ≤ heapNext v
  x1 : v.getReg .x1 = vecPtr v (s.getReg .x2 - 464)
  x8 : v.getReg .x8 = BitVec.ofNat 64 d
  x9 : v.getReg .x9 = u.getReg .x9
  x19 : v.getReg .x19 = vecCap v (s.getReg .x2 - 464)
  x20 : v.getReg .x20 = s.getReg .x10
  /-- The running quadratic's length, in `s7` as at `S - 808`. -/
  x23 : v.getReg .x23 = v.getMem (s.getReg .x2 - 808)
  x26 : v.getReg .x26 = BitVec.ofNat 64 qs.length
  vec : QVec s u v qs.length qs

theorem QVec.rebase {s u w v : MachineState} {cnt : ℕ} {r : List Word}
    (hn : heapNext w = heapNext u) (h : QVec s w v cnt r) : QVec s u v cnt r :=
  ⟨h.cap, h.len, by have := h.buf; simp only [NewBuf] at this ⊢; rw [← hn]; exact this, h.elems,
    h.le, by rw [← hn]; exact h.hw, by rw [← hn]; exact h.hs⟩

theorem QDone.rebase {s u w v : MachineState} {d : ℕ} {qs : List Word}
    (hg : DFrame u w (GW s)) (hn : heapNext w = heapNext u) (h9 : w.getReg .x9 = u.getReg .x9)
    (h : QDone s w v d qs) : QOut s u v d qs where
  pc := h.pc
  sp := h.sp
  inv := h.inv
  fr := (hg.mono fun _ ha ↦ Or.inl ha).trans h.fr fun a ha ↦ by
    rcases ha with ha | ha | ha | ha | ha | ha | ha
    · exact Or.inr (Or.inl ha)
    · exact Or.inr (Or.inr (Or.inl ha))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))))
    · simp only [Fresh] at ha
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by rw [← hn]; exact ha.1,
        ha.2⟩))))))
  mono := by rw [← hn]; exact h.mono
  x1 := h.x1
  x8 := h.x8
  x9 := h.x9.trans h9
  x19 := h.x19
  x20 := h.x20
  x23 := h.x23
  x26 := h.x26
  vec := h.vec.rebase hn

/-- **The grinding and the queries**, from `0x8000a790` to `0x8000a9d8`, or an `Err`. -/
theorem queries (hD : DuplexSpec) (hA : AbsorbSpec) (hTA : TryAllocZeroedSpec)
    {s u : MachineState} {QP QL : Word} {ℓ ml rt : ℕ} {T : Model.TState} (hpre : VsoPre s)
    (hc : Cfg s QP QL)
    (hconf : Model.Pcs.deriveConfigRust (s.getReg .x12).toNat (s.getReg .x13).toNat =
      some (cfgOf s))
    (hinv : InvR s u (u.getMem nextAddr)) (hpc : u.pc = 0x8000a790) (hlt : ℓ < K0 s + 2)
    (hmr : ml + rt < 64)
    (h184 : u.getMem (s.getReg .x2 - 856) = BitVec.ofNat 64 ℓ)
    (h240 : u.getMem (s.getReg .x2 - 800) = QL)
    (h192 : u.getMem (s.getReg .x2 - 848) = QP)
    (h208 : u.getMem (s.getReg .x2 - 832) = BitVec.ofNat 64 (8 * ℓ))
    (h168 : u.getMem (s.getReg .x2 - 872) = BitVec.ofNat 64 ml)
    (h216 : u.getMem (s.getReg .x2 - 824) = BitVec.ofNat 64 rt)
    (h224 : u.getMem (s.getReg .x2 - 816) = s.getReg .x10)
    (h248 : u.getMem (s.getReg .x2 - 792) = s.getReg .x10 + 8)
    (hT : TranscriptAt u (s.getReg .x10) T) :
    ∃ v, Reaches Image.code u v ∧ (FailR s v ∨ ∃ cnt qs T',
      (cfgOf s).queries[ℓ]? = some cnt ∧ qs.length = cnt ∧ 0 < ml + rt ∧
      QOut s u v (ml + rt) qs ∧
      (∀ k : List Word → Model.TM Unit,
        (Model.TM.grind Model.Pcs.queryGrindingBitsRust >>= fun _ ↦
          Model.Pcs.sampleQueriesRust (1#64 <<< ((ml + rt) % 64)) cnt >>= k).run T = (k qs).run T') ∧
      TranscriptAt v (s.getReg .x10) T' ∧ T'.proof = T.proof ∧ T'.roots = T.roots ∧
      T'.openingOffset = T.openingOffset ∧
      v.getMem (s.getReg .x2 - 968) = u.getReg .x1 ∧ v.getMem (s.getReg .x2 - 960) = u.getReg .x31) := by
  have hb := bounds hpre
  have hI := hpre.self
  have hS := Region.bounds hI.ok.self
  have hIs := hI.stack
  rw [stackLo_vso, vso_stack] at hIs
  obtain ⟨w, hr₁, hv₁⟩ := grind hD hA hpre hinv hpc h224 h248 hT
  rcases hv₁ with hf | hg
  · exact ⟨w, hr₁, Or.inl hf⟩
  obtain ⟨T₁, hgr, hT₁, p₁, r₁, o₁⟩ := hg.tr
  have kw (o : ℕ) (ho : o = 856 ∨ o = 800 ∨ o = 848 ∨ o = 832 ∨ o = 872 ∨ o = 824 ∨ o = 816 ∨
      o = 792 ∨ o = 808) : w.getMem (s.getReg .x2 - BitVec.ofNat 64 o) =
        u.getMem (s.getReg .x2 - BitVec.ofNat 64 o) :=
    hg.fr _ fun i hi hw ↦ by
      rcases hw with hw | hw | hw | hw
      · simp only [W] at hw
        rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          addr_omega [hw, hi, hS, hIs, hb]
      · rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> addr_omega [hw, hi, hb]
      · rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> addr_omega [hw, hi, hb]
      · rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> addr_omega [hw, hi, hb]
  have hn : heapNext w = heapNext u := by simp only [heapNext, hg.nx]
  have h9 : w.getReg .x9 = u.getReg .x9 := hg.regs .x9 (by decide)
  obtain ⟨hnx, -⟩ := sfacts hpre
  have spill {v : MachineState} (hfr : DFrame w v (QW s w v)) (hhi : heapNext v ≤ heapEnd) :
      v.getMem (s.getReg .x2 - 968) = u.getReg .x1 ∧
        v.getMem (s.getReg .x2 - 960) = u.getReg .x31 := by
    have k (o : ℕ) (ho : o = 968 ∨ o = 960) : v.getMem (s.getReg .x2 - BitVec.ofNat 64 o) =
        w.getMem (s.getReg .x2 - BitVec.ofNat 64 o) :=
      hfr _ fun i hi hx ↦ by
        rcases hx with hx | hx | hx | hx | hx | hx | hx
        · simp only [W] at hx; rcases ho with rfl | rfl <;> addr_omega [hx, hi, hS, hIs, hb]
        · rcases ho with rfl | rfl <;> addr_omega [hx, hi, hb]
        · rcases ho with rfl | rfl <;> addr_omega [hx, hi, hb]
        · rcases ho with rfl | rfl <;> addr_omega [hx, hi, hb]
        · rcases ho with rfl | rfl <;> addr_omega [hx, hi, hb]
        · rcases ho with rfl | rfl <;> addr_omega [hx, hi, hb, hnx]
        · simp only [Fresh] at hx; rcases ho with rfl | rfl <;> addr_omega [hx.2, hi, hb, hhi]
    exact ⟨(k 968 (Or.inl rfl)).trans hg.s72, (k 960 (Or.inr rfl)).trans hg.s80⟩
  have hbl : Model.log2StrictRust (1#64 <<< ((ml + rt) % 64)) = some (ml + rt) :=
    Model.Pcs.log2StrictRust_one_shiftLeft hmr
  obtain ⟨v, hr₂, hv₂⟩ := qsetup hTA hpre hc hconf hg.inv hg.pc hg.sp hlt hmr
    ((kw 856 (by decide)).trans h184) ((kw 800 (by decide)).trans h240)
    ((kw 848 (by decide)).trans h192) ((kw 832 (by decide)).trans h208)
    ((kw 872 (by decide)).trans h168) ((kw 824 (by decide)).trans h216) hg.x20
    (hg.x23.trans (kw 808 (by decide)).symm)
  rcases hv₂ with hd | ⟨cnt, hcnt, hpos, htr, ⟨h0, hq⟩ | hq⟩
  · exact ⟨v, hr₁.trans hr₂, Or.inl (Or.inl hd)⟩
  · subst h0
    refine ⟨v, hr₁.trans hr₂, Or.inr ⟨0, [], T₁, hcnt, rfl, hpos, hq.rebase hg.fr hn h9,
      fun k ↦ ?_, htr _ hT₁, p₁, r₁, o₁, spill hq.fr (hq.inv.heap hpre.heap).hi⟩⟩
    rw [run_bind_of hgr]
    simp only [Model.Pcs.sampleQueriesRust, hbl, Model.TM.ofOption, pure_bind,
      Model.Pcs.sampleQueriesLoop]
  obtain ⟨v', hr₃, hv₃⟩ := qloop hD hpre ((kw 816 (by decide)).trans h224)
    ((kw 792 (by decide)).trans h248) _ [] v T₁ cnt rfl (by simp) hq (htr _ hT₁)
  rcases hv₃ with hd | ⟨qs, T', hd, hql, hrun, hT', p, ro, o⟩
  · exact ⟨v', hr₁.trans (hr₂.trans hr₃), Or.inl (Or.inl hd)⟩
  refine ⟨v', hr₁.trans (hr₂.trans hr₃), Or.inr ⟨cnt, qs, T', hcnt, hql, hpos,
    hd.rebase hg.fr hn h9, fun k ↦ ?_, hT', p.trans p₁, ro.trans r₁, o.trans o₁,
    spill hd.fr (hd.inv.heap hpre.heap).hi⟩⟩
  rw [run_bind_of hgr]
  simp only [Model.Pcs.sampleQueriesRust, hbl, Model.TM.ofOption, pure_bind]
  exact run_bind_of hrun

end Rv64Verifier.Proofs.Pcs.Vso
