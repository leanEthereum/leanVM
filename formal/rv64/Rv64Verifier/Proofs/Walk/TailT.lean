import Rv64Verifier.Proofs.Walk.R18K
import Rv64Verifier.Proofs.Walk.TailStages

/-!
# `walk` from R19 on: the claims and the stages

`CoreT`: `CoreR18` with any computation left (`K`) and no column bases: the claims `Vec` at
`S - 1632` (capacity `C`, buffer `P`) holding `cl`, `M` of them, the evaluations as
`table_sumcheck` left them. `CoreT.stepW` (a step writing frame bytes apart from its slots),
`CoreT.store` (claim `M` written into the spare room), `CoreT.bind` (a stage of the mirror run).

The stages' entries: `AtR20` (`0x80003eb0`, the public input's claims appended), `AtR22`
(`0x80004144`, `verify_stacked_opening` returned `Ok`). From `verify_stacked_opening` on the root
at `S - 1800` is overwritten: `RestN` keeps the rest of `KeepR`, `TracksN` tracks the mirror
without the roots.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Verifier Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript
  Rv64Verifier.Bus

/-- The claims loop's facts, any computation `K` left. -/
structure CoreT (OI : MachineState → Word → List (List Opening) → Prop)
    (s u₀ w t u : MachineState) (layout : LayoutMirror.LayoutRust) (lir : BitVec 64)
    (evs : List (List E × List E)) (P C : Word) (M : Nat) (cl : List ColumnClaim)
    (K : TM SummaryRust) : Prop where
  rest : Rest s u₀ u
  smono : heapNext s ≤ heapNext u₀
  wmono : heapNext u₀ ≤ heapNext w
  umono : heapNext u₀ ≤ heapNext t
  tmono : heapNext t ≤ heapNext u
  evKept : ∀ x : Word, heapNext w ≤ x.toNat → x.toNat + 8 ≤ heapNext t → u.getMem x = t.getMem x
  rowsAt : RowsAt w t (s.getReg .x2 - 928) evs
  capSlot : u.getMem (s.getReg .x2 - 1632) = C
  ptrSlot : u.getMem (s.getReg .x2 - 1624) = P
  proofPtr : u.getMem (tp s) = s.getReg .x13
  evPtr : u.getMem (s.getReg .x2 - 2616) = vecPtr t (s.getReg .x2 - 928)
  evLen : u.getMem (s.getReg .x2 - 2608) = vecLen t (s.getReg .x2 - 928)
  len : M ≤ C.toNat
  buf : P.toNat % 8 = 0 ∧ P.toNat + 56 * C.toNat ≤ heapNext u ∧
    (C.toNat = 0 ∨ heapNext s ≤ P.toNat) ∧
    ((P = vecPtr u₀ (s.getReg .x2 - 928) ∧ C = vecCap u₀ (s.getReg .x2 - 928) ∧
      P.toNat + 56 * C.toNat ≤ heapNext u₀) ∨ heapNext t ≤ P.toNat)
  claims : claimsIn u P M = cl
  points : ∀ i < M, ((vecLen u (P + BitVec.ofNat 64 (56 * i))).toNat = 0 ∨
      Old s u (vecPtr u (P + BitVec.ofNat 64 (56 * i)))
        (24 * (vecLen u (P + BitVec.ofNat 64 (56 * i))).toNat)) ∧
    Apart (vecPtr u (P + BitVec.ofNat 64 (56 * i)))
      (24 * (vecLen u (P + BitVec.ofNat 64 (56 * i))).toNat) P (56 * C.toNat)
  tracks : TracksR OI s u
    (PcsContracts.digestAt u₀ (s.getReg .x2 - 1800), stackShape layout.stackLog lir.toNat) K

section Core
variable {OI : MachineState → Word → List (List Opening) → Prop} {s u₀ w t u v : MachineState}
  {layout : LayoutMirror.LayoutRust} {rows : List (BitVec 64)} {lir : BitVec 64}
  {bus : BusResultRust} {evs : List (List E × List E)} {P C : Word} {M : Nat}
  {cl : List ColumnClaim} {K : TM SummaryRust}

theorem CoreR18.toT (H : CoreR18 OI s u₀ w t u layout rows lir bus evs P C M cl) :
    CoreT OI s u₀ w t u layout lir evs P C M cl
      (afterTables (bytesAt s (s.getReg .x12) 32) layout rows lir bus evs) :=
  ⟨H.rest, H.smono, H.wmono, H.umono, H.tmono, H.evKept, H.rowsAt, H.capSlot, H.ptrSlot,
    H.proofPtr, H.evPtr, H.evLen, H.len, H.buf, H.claims, H.points, H.tracks⟩

theorem CoreT.n_lt (H : CoreT OI s u₀ w t u layout lir evs P C M cl K) : C.toNat < 2 ^ 32 := by
  have b := H.buf.2.1
  have hh := H.rest.inv.heap.hi
  simp only [heapEnd] at hh
  omega

/-- The claims list renamed. -/
theorem CoreT.congr {cl' : List ColumnClaim} {K' : TM SummaryRust}
    (H : CoreT OI s u₀ w t u layout lir evs P C M cl K) (e : cl = cl') (eK : K = K') :
    CoreT OI s u₀ w t u layout lir evs P C M cl' K' := by
  subst e eK; exact H

/-- A step writing frame bytes apart from the claims' slots, and maybe the sponge, keeps it, the
code then running `K'`. -/
theorem CoreT.step (hpre : WalkPre s)
    (H : CoreT OI s u₀ w t u layout lir evs P C M cl K) {W : Word → Prop} {Tw : Prop}
    (st : StepW s u v W Tw)
    (hW : ∀ a, W a → InF s a ∧ ¬ KeepR s u₀ a ∧ ¬ Within a (tp s) 368)
    (hs : ∀ a, W a → ¬ Within a (s.getReg .x2 - 1632) 16 ∧ ¬ Within a (s.getReg .x2 - 2616) 16)
    {K' : TM SummaryRust}
    (htr : TracksR OI s v
      (PcsContracts.digestAt u₀ (s.getReg .x2 - 1800), stackShape layout.stackLog lir.toNat) K') :
    CoreT OI s u₀ w t v layout lir evs P C M cl K' := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have fW : ∀ a, W a → InF s a := fun a ha ↦ (hW a ha).1
  have hm := st.mono
  have htm := H.tmono
  have hh := H.rest.inv.heap.hi
  have hN : heapNext u ≤ 2 ^ 63 := by simp only [heapNext, heapEnd] at hh ⊢; omega
  have gH : ∀ x : Word, x.toNat + 8 ≤ heapNext u → v.getMem x = u.getMem x :=
    fun x hx ↦ st.getH hpre fW hx
  have gF (k : Nat) (hk : 112 ≤ k ∧ k ≤ 2648) (hk' : k ≤ 2088 ∨ 2448 ≤ k)
      (hw : ∀ i < 8, ¬ W (s.getReg .x2 - BitVec.ofNat 64 k + BitVec.ofNat 64 i)) :
      v.getMem (s.getReg .x2 - BitVec.ofNat 64 k) = u.getMem (s.getReg .x2 - BitVec.ofNat 64 k) :=
    st.getF hpre (by addr_omega [hb1, hk]) hw fun _ ↦ by
      rw [tp]; simp only [Apart]; rcases hk' with hk' | hk' <;> addr_omega [hb1, hk, hk']
  have hdr (i : Nat) (hi : i < M) (c : Nat) (hc : c ≤ 48) :
      (P + BitVec.ofNat 64 (56 * i) + BitVec.ofNat 64 c).toNat + 8 ≤ heapNext u := by
    have b1 := H.buf.2.1; have b2 := H.len; addr_omega [hi, hc, hN, b1, b2]
  have pv (i : Nat) (hi : i < M) :
      vecPtr v (P + BitVec.ofNat 64 (56 * i)) = vecPtr u (P + BitVec.ofNat 64 (56 * i)) ∧
      vecLen v (P + BitVec.ofNat 64 (56 * i)) = vecLen u (P + BitVec.ofNat 64 (56 * i)) :=
    ⟨gH _ (hdr i hi 8 (by omega)), gH _ (hdr i hi 16 (by omega))⟩
  refine {
    rest := H.rest.stepW hpre (fun a ha ↦ ⟨(hW a ha).1, (hW a ha).2.1⟩) st
    smono := H.smono
    wmono := H.wmono
    umono := H.umono
    tmono := by omega
    evKept := fun x h1 h2 ↦ (gH x (by omega)).trans (H.evKept x h1 h2)
    rowsAt := H.rowsAt
    capSlot := by
      rw [show (1632 : Word) = BitVec.ofNat 64 1632 from rfl, gF 1632 (by omega) (by omega) fun j hj hw ↦
        (hs _ hw).1 (by simp only [Within]; addr_omega [hb1, hj])]
      exact H.capSlot
    ptrSlot := by
      rw [show (1624 : Word) = BitVec.ofNat 64 1624 from rfl, gF 1624 (by omega) (by omega) fun j hj hw ↦
        (hs _ hw).1 (by simp only [Within]; addr_omega [hb1, hj])]
      exact H.ptrSlot
    proofPtr := by
      have etp : tp s = s.getReg .x2 - BitVec.ofNat 64 2448 := rfl
      rw [etp, gF 2448 (by omega) (by omega) fun j hj hw ↦ (hW _ hw).2.2 (by
        rw [tp]; simp only [Within]; addr_omega [hb1, hj]), ← etp]
      exact H.proofPtr
    evPtr := by
      rw [show (2616 : Word) = BitVec.ofNat 64 2616 from rfl, gF 2616 (by omega) (by omega) fun j hj hw ↦
        (hs _ hw).2 (by simp only [Within]; addr_omega [hb1, hj])]
      exact H.evPtr
    evLen := by
      rw [show (2608 : Word) = BitVec.ofNat 64 2608 from rfl, gF 2608 (by omega) (by omega) fun j hj hw ↦
        (hs _ hw).2 (by simp only [Within]; addr_omega [hb1, hj])]
      exact H.evLen
    len := H.len
    buf := ⟨H.buf.1, by have := H.buf.2.1; omega, H.buf.2.2⟩
    claims := by
      rw [← H.claims]
      simp only [claimsIn]
      refine List.map_congr_left fun i hi ↦ ?_
      simp only [List.mem_range] at hi
      have hp := (H.points i hi).1
      simp only [Old] at hp
      have b1 := H.buf.2.1
      have b2 := H.len
      exact claimAt_congr' gH hN (by addr_omega [hi, hN, b1, b2]) (hp.imp_right fun h ↦ h.2.1)
    points := fun i hi ↦ by
      obtain ⟨e1, e2⟩ := pv i hi
      rw [e1, e2]
      exact ⟨(H.points i hi).1.imp_right fun h ↦ h.mono (by omega), (H.points i hi).2⟩
    tracks := htr }

/-- A step writing frame bytes apart from the claims' slots keeps it. -/
theorem CoreT.stepW (hpre : WalkPre s)
    (H : CoreT OI s u₀ w t u layout lir evs P C M cl K) {W : Word → Prop}
    (st : StepW s u v W False)
    (hW : ∀ a, W a → InF s a ∧ ¬ KeepR s u₀ a ∧ ¬ Within a (tp s) 368)
    (hs : ∀ a, W a → ¬ Within a (s.getReg .x2 - 1632) 16 ∧ ¬ Within a (s.getReg .x2 - 2616) 16) :
    CoreT OI s u₀ w t v layout lir evs P C M cl K :=
  H.step hpre st hW hs (H.tracks.keep fun _ hT ↦ st.transcript hpre H.rest.inv H.proofPtr
    (fun a ha ↦ ⟨(hW a ha).1, (hW a ha).2.2⟩) hT)

/-- Through a block that writes no memory. -/
theorem CoreT.same (hpre : WalkPre s) (H : CoreT OI s u₀ w t u layout lir evs P C M cl K)
    (hm : ∀ a, v.getMem a = u.getMem a) (sp : v.getReg .x2 = u.getReg .x2) :
    CoreT OI s u₀ w t v layout lir evs P C M cl K :=
  H.stepW hpre (StepW.same H.rest.inv.heap hm sp (fun _ ↦ False) False) (fun _ h ↦ h.elim)
    (fun _ h ↦ h.elim)

/-- Claim `M` written into the buffer's spare room. -/
theorem CoreT.store (hpre : WalkPre s)
    (H : CoreT OI s u₀ w t u layout lir evs P C M cl K) (hM : M < C.toNat)
    (fr : DFrame u v (Within · (P + BitVec.ofNat 64 (56 * M)) 56))
    (sp : v.getReg .x2 = u.getReg .x2) {c : ColumnClaim}
    (hc : claimAt v (P + BitVec.ofNat 64 (56 * M)) = c)
    (hpt : ((vecLen v (P + BitVec.ofNat 64 (56 * M))).toNat = 0 ∨
        Old s v (vecPtr v (P + BitVec.ofNat 64 (56 * M)))
          (24 * (vecLen v (P + BitVec.ofNat 64 (56 * M))).toNat)) ∧
      Apart (vecPtr v (P + BitVec.ofNat 64 (56 * M)))
        (24 * (vecLen v (P + BitVec.ofNat 64 (56 * M))).toNat) P (56 * C.toNat)) :
    CoreT OI s u₀ w t v layout lir evs P C (M + 1) (cl ++ [c]) K := by
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
    capSlot := by rw [show (1632 : Word) = BitVec.ofNat 64 1632 from rfl, kS _ (by omega) (by omega)]; exact H.capSlot
    ptrSlot := by rw [show (1624 : Word) = BitVec.ofNat 64 1624 from rfl, kS _ (by omega) (by omega)]; exact H.ptrSlot
    proofPtr := by
      have etp : tp s = s.getReg .x2 - BitVec.ofNat 64 2448 := rfl
      rw [etp, kS _ (by omega) (by omega), ← etp]; exact H.proofPtr
    evPtr := by rw [show (2616 : Word) = BitVec.ofNat 64 2616 from rfl, kS _ (by omega) (by omega)]; exact H.evPtr
    evLen := by rw [show (2608 : Word) = BitVec.ofNat 64 2608 from rfl, kS _ (by omega) (by omega)]; exact H.evLen
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

end Core

/-! ## Past `verify_stacked_opening` -/

/-- `KeepR` but the root, which `verify_stacked_opening` overwrites. -/
@[rv_addr] def KeepN (s u₀ : MachineState) (a : Word) : Prop :=
  KeepR s u₀ a ∧ ¬ Within a (s.getReg .x2 - 1800) 32

/-- `Rest`, the root aside. -/
structure RestN (s u₀ u : MachineState) : Prop where
  inv : Inv s u
  mono : heapNext u₀ ≤ heapNext u
  keep : DFrame u₀ u fun a ↦ ¬ KeepN s u₀ a

theorem Rest.toN {s u₀ u : MachineState} (h : Rest s u₀ u) : RestN s u₀ u :=
  ⟨h.inv, h.mono, h.keep.mono fun _ ha hK ↦ ha hK.1⟩

theorem RestN.get {s u₀ u : MachineState} (h : RestN s u₀ u) {x : Word}
    (hx : ∀ i < 8, KeepN s u₀ (x + BitVec.ofNat 64 i)) : u.getMem x = u₀.getMem x :=
  h.keep x fun i hi h' ↦ h' (hx i hi)

theorem RestN.same {s u₀ v w : MachineState} (h : RestN s u₀ v)
    (hm : ∀ a, w.getMem a = v.getMem a) (sp : w.getReg .x2 = v.getReg .x2) : RestN s u₀ w := by
  have hn : heapNext w = heapNext v := by simp only [heapNext, hm]
  exact ⟨h.inv.same hm sp, hn ▸ h.mono, h.keep.trans (DFrame.of_same hm _) fun _ h ↦ h⟩

/-- The code runs `C` from a transcript holding the proof, whatever the roots. -/
def TracksN (OI : MachineState → Word → List (List Opening) → Prop) (s u : MachineState)
    (C : TM SummaryRust) : Prop :=
  ∀ proof, ProofIn OI s (s.getReg .x13) proof → ∃ T, T.proof = proof ∧
    TranscriptAt u (tp s) T ∧ (prog s).run (initT s proof) = C.run T

theorem TracksR.toN {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {r : Digest × ℕ × ℕ} {C : TM SummaryRust} (h : TracksR OI s u r C) : TracksN OI s u C :=
  fun proof hp ↦ by
    obtain ⟨T, e, -, hT, hr⟩ := h proof hp
    exact ⟨T, e, hT, hr⟩

theorem TracksN.done {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {d : SummaryRust} (h : TracksN OI s u (pure d)) :
    ∀ proof, ProofIn OI s (s.getReg .x13) proof →
      ∃ summary, verifyExecutionRust (Proofs.Bytecode.readBytecode s (s.getReg .x11))
        (bytesAt s (s.getReg .x12) 32) proof = some summary := fun proof hp ↦ by
  obtain ⟨T, -, -, hr⟩ := h proof hp
  refine ⟨d, ?_⟩
  show ((prog s).run (initT s proof)).map (·.1) = some d
  rw [hr]
  rfl

/-! ## The stages' entries -/

/-- At `0x80003eb0`: the public input's claims `pub` appended, `L` claims in all (`L` also in
`s9`, `s10 + 1`), the length slot stale; `s7` the result's address, `s8` = `sp + 2144`. -/
structure AtR20 (OI : MachineState → Word → List (List Opening) → Prop)
    (s u₀ w t u : MachineState) (layout : LayoutMirror.LayoutRust) (rows : List (BitVec 64))
    (lir : BitVec 64) (bus : BusResultRust) (evs : List (List E × List E)) (P C L : Word)
    (pub : List ColumnClaim) : Prop
    extends CoreT OI s u₀ w t u layout lir evs P C L.toNat (bus.claims ++ tableClaimsRust evs ++ pub)
      (keccakPhaseRust layout evs >>=
        afterKeccak layout rows lir bus (bus.claims ++ tableClaimsRust evs ++ pub)) where
  pc : u.pc = 0x80003eb0
  x23 : u.getReg .x23 = s.getReg .x10
  x24 : u.getReg .x24 = s.getReg .x2 - 512
  x25 : u.getReg .x25 = L
  x26 : u.getReg .x26 + 1 = L

/-- At `0x80004144`, `verify_stacked_opening` returned `Ok`: what is left is `finish` on
`summary`; `s7` the result's address, `s8` = `sp + 2144`. -/
structure AtR22 (OI : MachineState → Word → List (List Opening) → Prop)
    (s u₀ u : MachineState) (summary : SummaryRust) : Prop where
  pc : u.pc = 0x80004144
  rest : RestN s u₀ u
  proofPtr : u.getMem (tp s) = s.getReg .x13
  x23 : u.getReg .x23 = s.getReg .x10
  x24 : u.getReg .x24 = s.getReg .x2 - 512
  tracks : TracksN OI s u (finishRust summary)

/-- At `0x800041cc`, an `Err` past `verify_stacked_opening`: the block writes `errNiche` to the
result and the error at its `a0`. -/
structure Err41cc (s u₀ u : MachineState) : Prop where
  pc : u.pc = 0x800041cc
  rest : RestN s u₀ u
  x23 : u.getReg .x23 = s.getReg .x10
  x10 : u.getReg .x10 = 8 ∨ u.getReg .x10 = 16

end Rv64Verifier.Proofs.Walk
