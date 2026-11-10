import Rv64Verifier.Proofs.Walk.R18C

/-!
# `walk` R18, the table claims: one claim stored

`CoreR18.store`: writing claim `M` into the buffer's spare room keeps the loop's facts, `M + 1`
claims. The write is in the heap `walk` allocated, apart from what `KeepR` holds, the evaluations,
the earlier claims, their points and the transcript (`claimAt_keep`, `transcript_heapW`).
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Verifier Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript
  Rv64Verifier.Bus

/-- A claim apart from a 56-byte write, its point empty or apart from it too, is kept. -/
theorem claimAt_keep {u v : MachineState} {X x : Word}
    (hf : ∀ y : Word, (∀ i < 8, ¬ Within (y + BitVec.ofNat 64 i) X 56) → v.getMem y = u.getMem y)
    (hX : X.toNat + 56 ≤ 2 ^ 64) (hx : Apart x 56 X 56) (hxw : x.toNat + 56 ≤ 2 ^ 64)
    (hp : (vecLen u x).toNat = 0 ∨ (Apart (vecPtr u x) (24 * (vecLen u x).toNat) X 56 ∧
      (vecPtr u x).toNat + 24 * (vecLen u x).toNat ≤ 2 ^ 64)) :
    claimAt v x = claimAt u x := by
  have g (c : Nat) (hc : c ≤ 48) (y : Word) (hy : y = x + BitVec.ofNat 64 c) :
      v.getMem y = u.getMem y := by
    subst hy
    exact hf _ fun i hi hw ↦ by simp only [Within, Apart] at hw hx; addr_omega [hw, hx, hxw, hc, hi, hX]
  have el : vecLen v x = vecLen u x := g 16 (by omega) _ rfl
  have ep : vecPtr v x = vecPtr u x := g 8 (by omega) _ rfl
  simp only [claimAt, vecEs, ep, el, g 24 (by omega) (x + 24) rfl]
  congr 1
  · rcases hp with h0 | ⟨hp, hpw⟩
    · simp [h0, eListAt]
    · have hy (i : Nat) (hi : i < (vecLen u x).toNat) (c : Nat) (hc : c ≤ 16) (y : Word)
          (hy : y = vecPtr u x + BitVec.ofNat 64 (24 * i) + BitVec.ofNat 64 c) :
          v.getMem y = u.getMem y := by
        subst hy
        exact hf _ fun j hj hw ↦ by
          simp only [Within, Apart] at hw hp; addr_omega [hw, hp, hpw, hi, hc, hj, hX]
      exact Bus.eListAt_congr fun i hi ↦ eAt_congr (hy i hi 0 (by omega) _ (by rw [add_ofNat_zero]))
        (hy i hi 8 (by omega) _ rfl) (hy i hi 16 (by omega) _ rfl)
  · exact eAt_congr (g 32 (by omega) _ rfl) (g 40 (by omega) _ (by bv_omega))
      (g 48 (by omega) _ (by bv_omega))

/-- A write into heap `walk` allocated keeps what the transcript stands for. -/
theorem transcript_heapW {s v w : MachineState} (hpre : WalkPre s) (h : Inv s v)
    (hptr : v.getMem (tp s) = s.getReg .x13) {X : Word} {n : Nat}
    (fr : DFrame v w (Within · X n)) (h1 : heapNext s ≤ X.toNat) (h2 : X.toNat + n ≤ heapNext v)
    {T : TState} (hT : TranscriptAt v (tp s) T) : TranscriptAt w (tp s) T := by
  obtain ⟨hb1, hb2, -, -⟩ := bounds hpre
  have hab := hpre.stack.above
  rw [stackLo_eq] at hab
  have hh := h.heap.hi
  simp only [heapEnd] at hab hh
  obtain ⟨e0, e1, e2⟩ := proofVals hpre h hptr
  have hP := hpre.proof
  have ro : ∀ {a : Word} {m : Nat}, ReadOnly s a m → a.toNat + m ≤ 2 ^ 64 →
      Misses (Within · X n) a m := by
    intro a m hr hm y hy hw
    obtain ⟨⟨hf, -⟩, -, -, -⟩ := hr
    simp only [heapEnd] at hf
    simp only [Within] at hy hw
    rcases hf with hf | hf <;> omega
  have tpw : ∀ y, Within y (tp s) 368 → ¬ Within y X n := by
    intro y hy hw
    rw [tp] at hy
    simp only [Within] at hy hw
    addr_omega [hy, hw, hh, hab, hb1, h2]
  refine fr.transcriptAt hT (tok hpre h hptr) (fun y hy ↦ tpw y (by
      rw [tp] at hy ⊢; addr_omega [hy, hb1])) ?_ ?_ (fun y hy ↦ tpw y (by
      rw [tp] at hy ⊢; addr_omega [hy, hb1]))
  · rw [e0]; exact ro hpre.proofRO (by addr_omega [hP])
  · rw [e1, e2]
    refine ro hpre.streamRO ?_
    rcases hpre.stream with h0 | h0
    · rw [h0]; have := (vecPtr s (s.getReg .x13)).isLt; omega
    · addr_omega [h0]

section Store
variable {OI : MachineState → Word → List (List Opening) → Prop} {s u₀ w t u v : MachineState}
  {layout : LayoutMirror.LayoutRust} {rows : List (BitVec 64)} {lir : BitVec 64}
  {bus : BusResultRust} {evs : List (List E × List E)} {P C : Word} {M : Nat}
  {cl : List ColumnClaim}

/-- Claim `M` written into the buffer's spare room. -/
theorem CoreR18.store (hpre : WalkPre s)
    (H : CoreR18 OI s u₀ w t u layout rows lir bus evs P C M cl) (hM : M < C.toNat)
    (fr : DFrame u v (Within · (P + BitVec.ofNat 64 (56 * M)) 56))
    (sp : v.getReg .x2 = u.getReg .x2) {c : ColumnClaim}
    (hc : claimAt v (P + BitVec.ofNat 64 (56 * M)) = c)
    (hpt : ((vecLen v (P + BitVec.ofNat 64 (56 * M))).toNat = 0 ∨
        Old s v (vecPtr v (P + BitVec.ofNat 64 (56 * M)))
          (24 * (vecLen v (P + BitVec.ofNat 64 (56 * M))).toNat)) ∧
      Apart (vecPtr v (P + BitVec.ofNat 64 (56 * M)))
        (24 * (vecLen v (P + BitVec.ofNat 64 (56 * M))).toNat) P (56 * C.toNat)) :
    CoreR18 OI s u₀ w t v layout rows lir bus evs P C (M + 1) (cl ++ [c]) := by
  obtain ⟨hb1, hb2, -, -⟩ := bounds hpre
  have hab := hpre.stack.above
  rw [stackLo_eq] at hab
  have hh := H.rest.inv.heap.hi
  simp only [heapEnd] at hab hh
  have hN : heapNext u ≤ 2 ^ 63 := by omega
  obtain ⟨bal, bhi, blo, bcase⟩ := H.buf
  have hW : P.toNat + 56 * M + 56 ≤ 2013265920 := by omega
  have hX : (P + BitVec.ofNat 64 (56 * M)).toNat = P.toNat + 56 * M := by addr_omega [bhi, hM, hN]
  have hs0 : heapNext s ≤ P.toNat := by omega
  -- what the write misses
  have kp : ∀ y : Word, y.toNat + 8 ≤ P.toNat + 56 * M ∨ P.toNat + 56 * M + 56 ≤ y.toNat →
      y.toNat + 8 ≤ 2 ^ 64 → v.getMem y = u.getMem y := fun y hy hw ↦
    fr y fun i hi h' ↦ by simp only [Within] at h'; rw [hX] at h'; addr_omega [hy, hw, hi, h']
  have kS : ∀ k : Nat, 8 ≤ k → k ≤ 11392 →
      v.getMem (s.getReg .x2 - BitVec.ofNat 64 k) = u.getMem (s.getReg .x2 - BitVec.ofNat 64 k) :=
    fun k h1 h2 ↦ kp _ (Or.inr (by addr_omega [hb1, h1, h2, hab, hW])) (by addr_omega [hb1, h1, h2])
  have hn : heapNext v = heapNext u := by
    simp only [heapNext]
    exact congrArg BitVec.toNat (kp nextAddr (Or.inr (by
      have : nextAddr.toNat = 2684358448 := rfl
      omega)) (by decide))
  have m₀ := H.rest.mono
  have hm := H.umono
  have hw := H.wmono
  have htm := H.tmono
  have heap : HeapOk v := ⟨hn ▸ H.rest.inv.heap.lo, hn ▸ H.rest.inv.heap.hi⟩
  refine {
    rest := ⟨H.rest.inv.step hpre fr (fun a ha ↦ by
        simp only [Within] at ha
        rw [hX] at ha
        refine ⟨Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)), ?_⟩
        simp only [Within]; addr_omega [ha, hb1, hab, hW]) heap (by omega) sp,
      by omega, H.rest.keep.trans fr fun a ha hK ↦ by
        simp only [Within] at ha
        rw [hX] at ha
        simp only [KeepR] at hK
        rcases hK with (hK | hK | hK | hK | hK | hK) | ⟨k1, k2, k3⟩
        all_goals first
          | (simp only [Within] at hK; addr_omega [ha, hK, hb1, hab, hW])
          | (rcases bcase with ⟨rfl, rfl, -⟩ | bc
             · exact k3 ⟨by omega, by omega⟩
             · omega)⟩
    smono := H.smono
    wmono := hw
    umono := hm
    tmono := by omega
    evKept := fun x h1 h2 ↦ by
      rw [kp x (by rcases bcase with ⟨-, -, bc⟩ | bc <;> omega) (by omega)]
      exact H.evKept x h1 h2
    rowsAt := H.rowsAt
    bases := fun i hi ↦ by
      have e : s.getReg .x2 - 896 + BitVec.ofNat 64 (8 * i) =
          s.getReg .x2 - BitVec.ofNat 64 (896 - 8 * i) := by
        apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hi]
      rw [e, kS _ (by omega) (by omega), ← e]
      exact H.bases i hi
    capSlot := by rw [show (1632 : Word) = BitVec.ofNat 64 1632 from rfl, kS _ (by omega) (by omega)]; exact H.capSlot
    ptrSlot := by rw [show (1624 : Word) = BitVec.ofNat 64 1624 from rfl, kS _ (by omega) (by omega)]; exact H.ptrSlot
    ptr184 := by rw [show (2472 : Word) = BitVec.ofNat 64 2472 from rfl, kS _ (by omega) (by omega)]; exact H.ptr184
    evPtr := by rw [show (2616 : Word) = BitVec.ofNat 64 2616 from rfl, kS _ (by omega) (by omega)]; exact H.evPtr
    evLen := by rw [show (2608 : Word) = BitVec.ofNat 64 2608 from rfl, kS _ (by omega) (by omega)]; exact H.evLen
    proofPtr := by
      have etp : tp s = s.getReg .x2 - BitVec.ofNat 64 2448 := rfl
      rw [etp, kS _ (by omega) (by omega), ← etp]; exact H.proofPtr
    len := hM
    buf := ⟨bal, by omega, blo, bcase⟩
    claims := by
      rw [← hc, ← H.claims]
      simp only [claimsIn, List.range_succ, List.map_append, List.map_cons, List.map_nil]
      congr 1
      refine List.map_congr_left fun i hi ↦ ?_
      simp only [List.mem_range] at hi
      have hp := H.points i hi
      simp only [Old, Apart] at hp
      refine claimAt_keep (fun y hy ↦ fr y hy) (by omega)
        (by simp only [Apart]; rw [hX]; addr_omega [hi, bhi, hN]) (by addr_omega [hi, bhi, hN, hM]) ?_
      rcases hp with ⟨h0 | ⟨p1, p2, -⟩, ha⟩
      · exact Or.inl h0
      · refine Or.inr ⟨?_, by omega⟩
        simp only [Apart]; rw [hX]
        rcases ha with ha | ha | ha | ha <;> omega
    points := fun i hi ↦ by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · have e1 : vecPtr v (P + BitVec.ofNat 64 (56 * i)) = vecPtr u (P + BitVec.ofNat 64 (56 * i)) :=
          kp _ (Or.inl (by addr_omega [hi, bhi, hN, hM])) (by addr_omega [hi, bhi, hN, hM])
        have e2 : vecLen v (P + BitVec.ofNat 64 (56 * i)) = vecLen u (P + BitVec.ofNat 64 (56 * i)) :=
          kp _ (Or.inl (by addr_omega [hi, bhi, hN, hM])) (by addr_omega [hi, bhi, hN, hM])
        rw [e1, e2]
        exact ⟨(H.points i hi).1.imp_right fun h ↦ h.mono (by omega), (H.points i hi).2⟩
      · exact hpt
    tracks := H.tracks.keep fun T hT ↦ transcript_heapW hpre H.rest.inv H.proofPtr fr
      (by rw [hX]; omega) (by rw [hX]; omega) hT }

end Store

end Rv64Verifier.Proofs.Walk
