import Rv64Verifier.Proofs.Pcs.VsoFoldGrow

/-!
# `verify_stacked_opening`'s level loop: the challenge pushed to `folds`

`0x8000a228` stores the challenge after the folds and their new length, and compares the rounds
done with `level_folds`' capacity.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- The challenge `c` pushed to `folds`: at `0x8000a270` with room in `level_folds`, or at
`0x8000a260` to grow it. -/
structure PF (s : MachineState) (x : LCtx) (h u : MachineState) (ℓ : ℕ)
    (Wl : Model.Pcs.WhirLocals) (j : ℕ) (lf q : List E) (c : E) : Prop
    extends RB s x h u ℓ Wl (Wl.folds ++ lf ++ [c]) lf q where
  pc : (u.pc = 0x8000a270 ∧ j < (vecCap u (s.getReg .x2 - 640)).toNat) ∨
    (u.pc = 0x8000a260 ∧ j = (vecCap u (s.getReg .x2 - 640)).toNat)
  x19 : u.getReg .x19 = vecPtr u (s.getReg .x2 - 640)
  x20 : u.getReg .x20 = BitVec.ofNat 64 (24 * j)
  x21 : u.getReg .x21 = BitVec.ofNat 64 j
  x24 : u.getReg .x24 = BitVec.ofNat 64 Wl.folds.length
  jlt : j < fcOf s ℓ
  lfl : lf.length = j
  chal : eAt u (s.getReg .x2 - 128) = c
  value : Runs s u ℓ (Model.Pcs.roundK Wl lf q (fcOf s ℓ - (j + 1)) (AFk s x ℓ) c)

theorem pushF {s : MachineState} {x : LCtx} {h u : MachineState} {ℓ : ℕ}
    {Wl : Model.Pcs.WhirLocals} {j : ℕ} {lf q : List E} {c : E}
    (hpre : VsoPre s) (hs : Smp s x h u ℓ Wl j lf q c) (hpc : u.pc = 0x8000a228)
    (hroom : Wl.folds.length + j < (vecCap u (s.getReg .x2 - 688)).toNat) :
    ∃ v, Reaches Image.code u v ∧ PF s x h v ℓ Wl j lf q c := by
  have hb := bounds hpre
  have hst := hpre.stack
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hsp := hs.sp
  have hB := hs.bufs
  have hf := hs.head.facts
  have hhu := hs.heap.hi
  have hsm := vec_small hs.F.1 hs.heap
  have hF8 := hs.F.1.raw.1
  have hFb : (s.getReg .x2 - 688 + 8).toNat = (s.getReg .x2 - 680).toNat := by addr_omega [hb]
  obtain ⟨hFl, hFh⟩ : x.L ≤ (vecPtr u (s.getReg .x2 - 688)).toNat ∧
      (vecPtr u (s.getReg .x2 - 688)).toNat + (vecCap u (s.getReg .x2 - 688)).toNat * 24 ≤
        heapNext u := by
    rcases hB.F with h0 | h0
    · omega
    · exact h0
  have hLs := hf.hs
  have hhs := hpre.heap.lo
  have hFr : Region (vecPtr u (s.getReg .x2 - 688)) ((vecCap u (s.getReg .x2 - 688)).toNat * 24) :=
    heap_region (by simp only [heapStart, heapNext] at hhs hLs hFl ⊢; omega) (by omega) hF8
  have hFP : u.getMem (s.getReg .x2 - 680) = vecPtr u (s.getReg .x2 - 688) := by
    simp only [vecPtr]; rv_eval []
  have hL0 := hs.x24
  obtain ⟨t, hr, ht⟩ := Sym.BlockSpec.reaches b8000a228_spec hpc (by
    rv_eval [hsp, hs.x18, hs.x20, hFP]
    and_intros <;> first
      | valid_access hst.valid [hb]
      | exact Region.valid hFr (by addr_omega [hroom, hsm, hFh, hhu])
          (by addr_omega [hroom, hsm, hFh, hhu]) (by addr_omega [hroom, hsm, hFh, hhu, hF8])
      | addr_omega [hb, hroom, hsm, hFh, hhu])
  have k := b8000a228_keeps ht
  have hn : (Wl.folds ++ lf).length = Wl.folds.length + j := by
    rw [List.length_append, hs.lfl]
  have hbase : u.getMem (s.getReg .x2 - BitVec.ofNat 64 1040 + 360) +
      (BitVec.ofNat 64 (24 * Wl.folds.length) + u.getReg .x20) =
      vecPtr u (s.getReg .x2 - 688) + BitVec.ofNat 64 (24 * (Wl.folds ++ lf).length) := by
    rw [hs.x20, hn, show u.getMem (s.getReg .x2 - BitVec.ofNat 64 1040 + 360) =
      vecPtr u (s.getReg .x2 - 688) by simp only [vecPtr]; congr 1; addr_omega [hb]]
    addr_omega [hroom, hsm, hFh, hhu]
  have m1 := b8000a228_m1 ht
  have m2 := b8000a228_m2 ht
  have m3 := b8000a228_m3 ht
  rw [hsp, hs.x18] at m1 m2 m3
  rw [hbase] at m1 m2 m3
  have X : DFrame u t fun a ↦ Within a (s.getReg .x2 - 672) 8 ∨
      Within a (vecPtr u (s.getReg .x2 - 688) +
        BitVec.ofNat 64 (24 * (Wl.folds ++ lf).length)) 24 :=
    (holds_dframe ht).mono fun a ⟨k, hk, hw⟩ ↦ by
      simp only [b8000a228, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl <;> rv_eval [hsp, hs.x18, hs.x20, hFP] at hw
      all_goals first
        | exact Or.inl (by addr_omega [hw, hb])
        | exact Or.inr (by rw [hn]; addr_omega [hw, hroom, hsm, hFh, hhu])
  have nx : t.getMem nextAddr = u.getMem nextAddr := X _ fun i hi hw ↦ by
    rcases hw with hw | hw
    · addr_omega [hw, hi, hb, hnx]
    · rw [hn] at hw; addr_omega [hw, hi, hroom, hsm, hFh, hhu, hnx]
  have hn' : heapNext t = heapNext u := by simp only [heapNext, nx]
  have hl : t.getMem (s.getReg .x2 - 688 + 16) =
      BitVec.ofNat 64 ((Wl.folds ++ lf).length + 1) := by
    have m368 := b8000a228_m_x2_368 ht
    rw [hsp] at m368
    rw [show s.getReg .x2 - 688 + 16 = s.getReg .x2 - BitVec.ofNat 64 1040 + 368 by
        addr_omega [hb], m368,
      show u.getMem (s.getReg .x2 - BitVec.ofNat 64 1040 + 248) =
        u.getMem (s.getReg .x2 - 792) by congr 1; addr_omega [hb],
      hs.m248, hs.x21, hn]
    addr_omega [hroom, hsm]
  have hc : eAt t (vecPtr u (s.getReg .x2 - 688) +
      BitVec.ofNat 64 (24 * (Wl.folds ++ lf).length)) = c := by
    rw [← hs.chal]
    unfold eAt
    rw [m1, m2, m3]
    rv_eval []
  have hFpu := vecE_push hs.F.1 hs.F.2.1 X (fun a ha ↦ by
      rcases ha with ha | ha
      · exact Or.inl (by addr_omega [ha, hb])
      · exact Or.inr ha) (by rw [hn]; exact hroom) hl hc (by addr_omega [hb]) (by addr_omega [hb])
    hs.heap (by rw [hn'])
  have hap := hs.ap
  have hLB := hB.LF
  have hLk := vecE_keep X hs.LF.1 (fun a ha ↦ by
      refine ⟨fun hw ↦ ?_, fun hw ↦ ?_⟩
      · rcases ha with ha | ha
        · addr_omega [ha, hw, hb]
        · rw [hn] at ha; addr_omega [ha, hw, hb, hroom, hsm, hFh, hhu]
      · rcases ha with ha | ha
        · rcases hLB with h0 | h0
          · simp only [Within] at hw; omega
          · addr_omega [ha, hw, hb, h0.2, hhu]
        · rw [hn] at ha; addr_omega [ha, hw, hap.1, hroom, hsm, hFh, hhu])
    (by addr_omega [hb]) (by rw [hn']) hs.heap
  have hRB := RB.carry2 (fl' := Wl.folds ++ lf ++ [c]) (lfs' := lf) hpre hs.toRB X (fun a ha ↦ by
      rcases ha with ha | ha
      · exact Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb]))))
      · rw [hn] at ha
        rcases hs.F.2.2 with ⟨e1, e2⟩ | h0
        · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))))))
          rw [← e1, ← e2]; addr_omega [ha, hroom, hsm, hFh, hhu]
        · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨?_, ?_⟩)))))))
          · have := h0.2; rcases this with h1 | h1
            · omega
            · addr_omega [ha, h1.1, hroom, hsm, hFh, hhu]
          · rw [nx]; addr_omega [ha, hroom, hsm, hFh, hhu])
    (fun a ha ↦ by
      refine ⟨fun hw ↦ ?_, fun hw ↦ ?_⟩
      · rcases ha with ha | ha
        · rcases hw with hw | hw | hw <;> addr_omega [ha, hw, hb]
        · rw [hn] at ha; rcases hw with hw | hw | hw <;> addr_omega [ha, hw, hb, hroom, hsm, hFh, hhu]
      · rcases ha with ha | ha
        · rcases hB.Q with h0 | h0
          · simp only [Within] at hw; omega
          · addr_omega [ha, hw, hb, h0.2, hhu]
        · rw [hn] at ha; addr_omega [ha, hw, hap.2.1, hroom, hsm, hFh, hhu])
    ⟨by rw [hn']; exact hs.heap.lo, by rw [hn']; exact hhu⟩ (by rw [hn'])
    (fun r hr' ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact k _ (by decide))
    ⟨hFpu.1, hFpu.2.1, by
      rw [hFpu.2.2.1, hFpu.2.2.2]
      rcases hs.F.2.2 with h0 | h0
      · exact Or.inl h0
      · exact Or.inr (NewBuf.grow h0 (by rw [hn']))⟩
    ⟨hLk.1, by rw [hLk.2.1]; exact hs.LF.2.1, by
      rw [hLk.2.2.1, hLk.2.2.2.1]; exact NewBuf.grow hs.LF.2.2 (by rw [hn'])⟩
    (by rw [hFpu.2.2.1, hFpu.2.2.2, hLk.2.2.1, hLk.2.2.2.1]; exact hap)
  have hLl : (vecLen u (s.getReg .x2 - 640)).toNat = j := by
    have := congrArg List.length hs.LF.2.1
    rw [vecEs, eListAt_length, hs.lfl] at this; exact this
  have hLc := hs.LF.1.len
  have hLs := vec_small hs.LF.1 hs.heap
  have hcap4 : u.getMem (u.getReg .x2 + 400) = vecCap t (s.getReg .x2 - 640) := by
    rw [hLk.2.2.2.1, hsp]; simp only [vecCap]; rv_eval []
  have hrst := hpre.root.stack
  rw [stackLo_vso, vso_stack] at hrst
  have hrf := hpre.root.free
  simp only [Outside] at hrf
  refine ⟨t, hr, {
    toRB := hRB
    pc := by
      by_cases he : j = (vecCap t (s.getReg .x2 - 640)).toNat
      · exact Or.inr ⟨b8000a228_pc_not_taken ht (by
          rw [hcap4, hs.x21]; rw [hLk.2.2.2.1] at he ⊢; addr_omega [he, hLs, hLl, hLc]), he⟩
      · refine Or.inl ⟨b8000a228_pc_taken ht (by
          rw [hcap4, hs.x21]; intro he'; rw [hLk.2.2.2.1] at he he'
          exact he (by addr_omega [he', hLs, hLl, hLc])), ?_⟩
        rw [hLk.2.2.2.1] at he ⊢; omega
    x19 := by rw [k .x19 (by decide), hs.x19, hLk.2.2.1]
    x20 := by rw [k .x20 (by decide), hs.x20]
    x21 := by rw [k .x21 (by decide), hs.x21]
    x24 := by rw [k .x24 (by decide), hs.x24]
    jlt := hs.jlt
    lfl := hs.lfl
    chal := by
      rw [← hs.chal]
      exact X.eAt' (fun y hy hw ↦ by
        rcases hw with hw | hw
        · addr_omega [hy, hw, hb]
        · rw [hn] at hw; addr_omega [hy, hw, hb, hroom, hsm, hFh, hhu]) (by addr_omega [hb])
    value := hs.value.keep hpre (FW.inv hpre hs.head hs.fr hs.heap hs.mono
        (hsp.trans hs.head.sp.symm)) X (fun a ha ↦ by
        rcases ha with ha | ha
        · exact Or.inl (by addr_omega [ha, hb])
        · rw [hn] at ha
          exact Or.inr (Or.inr (Or.inl ⟨by
            have := hf.hs; addr_omega [ha, hFl, this, hroom, hsm, hFh, hhu],
            by addr_omega [ha, hroom, hsm, hFh, hhu]⟩)))
      fun y hy hw ↦ by
        rcases hw with hw | hw
        · addr_omega [hy, hw, hrst, hb]
        · rw [hn] at hw
          rcases hrf.1 with h0 | h0
          · have := hf.hs; addr_omega [hy, hw, h0, hFl, this, hroom, hsm, hFh, hhu]
          · addr_omega [hy, hw, h0, hroom, hsm, hFh, hhu] }⟩

end Rv64Verifier.Proofs.Pcs.Vso
