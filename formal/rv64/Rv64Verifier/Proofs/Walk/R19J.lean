import Rv64Verifier.Proofs.Walk.R19I

/-!
# `walk` R19, the public input's claims: `grow_one` with the new buffer's place
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Verifier Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript
  Rv64Verifier.Bus

section Grow
variable {OI : MachineState → Word → List (List Opening) → Prop} {s u₀ w t u : MachineState}
  {layout : LayoutMirror.LayoutRust} {lir : BitVec 64} {evs : List (List E × List E)}
  {P C : Word} {M : Nat} {cl : List ColumnClaim} {K : TM SummaryRust}

set_option maxHeartbeats 1600000 in
/-- `CoreT.growOne`, the new buffer allocated after the call. -/
theorem CoreT.growOneF (hG : GrowOneFreshSpec 0x8000c0a4 56 8) (hpre : WalkPre s)
    (H : CoreT OI s u₀ w t u layout lir evs P C M cl K) (hfull : M = C.toNat)
    {u' : MachineState} (hr : Reaches Image.code u' u) (hpc : u.pc = 0x8000c0a4)
    (h10 : u.getReg .x10 = s.getReg .x2 - 1632) :
    ∃ v, Reaches Image.code u' v ∧ ((v.pc = returnAddress u ∧ Preserves u v ∧
      StepW s u v (Within · (s.getReg .x2 - 1632) 16) False ∧
      ∃ P' C', CoreT OI s u₀ w t v layout lir evs P' C' M cl K ∧ M < C'.toNat ∧
        heapNext u ≤ P'.toNat) ∨
      Dead Image.code v) := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  have I := H.rest.inv
  have hLC := H.len
  have hC := H.n_lt
  have hh := I.heap.hi
  have hs0 := hpre.heap.lo
  have htm := H.tmono
  have hwm := H.wmono
  have hum := H.umono
  have hsm := H.smono
  simp only [heapEnd, heapStart] at hh hs0
  obtain ⟨bal, bhi, blo, -⟩ := H.buf
  have eP : vecPtr u (s.getReg .x2 - 1632) = P := by
    simp only [vecPtr]; rw [show s.getReg .x2 - 1632 + 8 = s.getReg .x2 - 1624 by bv_omega]
    exact H.ptrSlot
  have eC : vecCap u (s.getReg .x2 - 1632) = C := by
    simp only [vecCap]; exact H.capSlot
  have hgs : growOneStack ≤ 8736 := by decide
  have pre : GrowOnePre 56 8 u := {
    heap := I.heap
    self := by rw [h10]; valid_sub hval [hb1, hb3]
    raw := by
      rw [h10]
      simp only [RawVecOk, Buf]
      rw [eP, eC]
      refine ⟨bal, ?_⟩
      rcases blo with h0 | h0
      · left; simp [h0]
      · right; exact ⟨by simp only [heapStart]; omega, by omega⟩
    stack := hpre.stack.sub 2656 I.sp (by rw [stack_eq]; decide) (by decide) (by decide)
      (by decide) (by decide)
    selfFree := by
      rw [h10]
      exact (fr_ok hpre I (c := 1632) (k := 1632) (n := 16) (m := 0) rfl (by omega) (by omega)
        (by omega)).1
    selfStack := by
      rw [h10]
      exact (fr_ok hpre I (c := 1632) (k := 1632) (n := 16) rfl (by omega) (by omega) hgs).2.1 }
  obtain ⟨v, hrv, ⟨hpcv, hp, post, fs⟩ | hd⟩ := hG.call hr hpc pre
  swap
  · exact ⟨v, hrv, Or.inr hd⟩
  have okC := post.cap
  have okB := post.bytes
  have fr := post.frame
  rw [h10] at okC okB fr fs
  rw [eC, eP] at okB
  rw [eC] at okC
  have W1ok : ∀ a, Within a (s.getReg .x2 - 1632) 16 → InF s a ∧ ¬ KeepR s u₀ a := fun a ha ↦
    range_ok hpre H.rest (c := 1632) (k := 1632) (n := 16) rfl (by omega) (by omega) ha
  have st : StepW s u v (Within · (s.getReg .x2 - 1632) 16) False :=
    StepW.ofCall hpre I hgs (DFrame.of_byteFrame fr) post.heap post.mono (hp .x2 (by decide))
  have gu : ∀ x : Word, x.toNat + 8 ≤ heapNext u → v.getMem x = u.getMem x := fun x hx ↦
    st.getH hpre (fun a ha ↦ (W1ok a ha).1) hx
  have gF (c : Nat) (hc : 112 ≤ c ∧ c ≤ 2648) (hw : c ≤ 1616 ∨ 1640 ≤ c) :
      v.getMem (s.getReg .x2 - BitVec.ofNat 64 c) = u.getMem (s.getReg .x2 - BitVec.ofNat 64 c) :=
    st.getF hpre (by addr_omega [hb1, hc]) (fun i hi hw' ↦ by
      simp only [Within] at hw'
      rcases hw with hw | hw <;> addr_omega [hw', hw, hi, hb1, hc])
      (fun hf ↦ hf.elim)
  obtain ⟨P', hP'⟩ : ∃ P', vecPtr v (s.getReg .x2 - 1632) = P' := ⟨_, rfl⟩
  obtain ⟨C', hC'⟩ : ∃ C', vecCap v (s.getReg .x2 - 1632) = C' := ⟨_, rfl⟩
  rw [hC'] at okC
  rw [hP'] at okB
  rw [hP', hC'] at fs
  simp only [NewBuf] at fs
  rcases fs with ⟨fa, f0 | ⟨f1, f2⟩⟩
  · omega
  have hm := st.mono
  have hdr (i : Nat) (hi : i < M) (c : Nat) (hc48 : c ≤ 48) (h8 : c % 8 = 0) :
      v.getMem (P' + BitVec.ofNat 64 (56 * i) + BitVec.ofNat 64 c) =
        u.getMem (P + BitVec.ofNat 64 (56 * i) + BitVec.ofNat 64 c) := by
    rw [show P' + BitVec.ofNat 64 (56 * i) + BitVec.ofNat 64 c = P' + BitVec.ofNat 64 (56 * i + c)
        by bv_omega,
      show P + BitVec.ofNat 64 (56 * i) + BitVec.ofNat 64 c = P + BitVec.ofNat 64 (56 * i + c)
        by bv_omega,
      getMem_eq_of_bytesAt okB fa bal (by omega) (by omega)]
  have ePv : v.getMem (s.getReg .x2 - 1624) = P' := by
    rw [← hP']; simp only [vecPtr]; congr 1; bv_omega
  refine ⟨v, hrv, Or.inl ⟨hpcv, hp, st, P', C', {
    rest := H.rest.stepW hpre W1ok st
    smono := hsm
    wmono := hwm
    umono := hum
    tmono := by omega
    evKept := fun x h1 h2 ↦ (gu x (by omega)).trans (H.evKept x h1 h2)
    rowsAt := H.rowsAt
    capSlot := by rw [← hC']; rfl
    ptrSlot := ePv
    proofPtr := by
      have etp : tp s = s.getReg .x2 - BitVec.ofNat 64 2448 := rfl
      rw [etp, gF 2448 (by omega) (by omega), ← etp]; exact H.proofPtr
    evPtr := by
      rw [show (2616 : Word) = BitVec.ofNat 64 2616 from rfl, gF 2616 (by omega) (by omega)]
      exact H.evPtr
    evLen := by
      rw [show (2608 : Word) = BitVec.ofNat 64 2608 from rfl, gF 2608 (by omega) (by omega)]
      exact H.evLen
    len := by omega
    buf := ⟨fa, by omega, Or.inr (by omega), Or.inr (by omega)⟩
    claims := by
      rw [← H.claims]
      simp only [claimsIn]
      refine List.map_congr_left fun i hi ↦ ?_
      simp only [List.mem_range] at hi
      refine claimAt_move (fun c hc h8 ↦ hdr i hi c hc h8) ?_
      rcases (H.points i hi).1 with h0 | hp'
      · exact Or.inl h0
      · simp only [Old] at hp'
        exact Or.inr fun j hj c hc ↦ gu _ (by addr_omega [hp'.2.1, hj, hc, hh])
    points := fun i hi ↦ by
      have e8 : vecPtr v (P' + BitVec.ofNat 64 (56 * i)) = vecPtr u (P + BitVec.ofNat 64 (56 * i)) :=
        hdr i hi 8 (by omega) (by omega)
      have e16 : vecLen v (P' + BitVec.ofNat 64 (56 * i)) = vecLen u (P + BitVec.ofNat 64 (56 * i)) :=
        hdr i hi 16 (by omega) (by omega)
      rw [e8, e16]
      refine ⟨(H.points i hi).1.imp_right fun h ↦ h.mono (by omega), ?_⟩
      simp only [Apart]
      rcases (H.points i hi).1 with h0 | hp'
      · left; omega
      · simp only [Old] at hp'; right; right; left; omega
    tracks := H.tracks.keep fun _ hT ↦ st.transcript hpre I H.proofPtr (fun a ha ↦ ⟨(W1ok a ha).1,
      by rw [tp]; simp only [Within] at ha ⊢; addr_omega [ha, hb1]⟩) hT }, by omega, f1⟩⟩

end Grow

end Rv64Verifier.Proofs.Walk
