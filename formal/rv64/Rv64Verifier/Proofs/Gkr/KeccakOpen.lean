import Rv64Verifier.Proofs.Gkr.KeccakLoop

/-!
# `keccak::verify_keccak`: calls to `open`, `memcpy` of a row, `mul` on the frame's slots

`open_call` is a call to `open` with the claim at `f + 200` or `f + 296` and the value at
`f + 176` or `f + 5120`, its result at `f + 1952`; `memcpy_row` copies a 64-element row between two
slots; `mul_slots` multiplies two slots into a third.
-/

namespace Rv64Verifier.Gkr.Keccak
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Model.Gkr Rv64Verifier.Transcript Rv64Verifier.Contracts
  Rv64Verifier.Gkr Rv64Verifier.Blocks.F35
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

attribute [local rv_addr] vecPtr vecLen vecCap

theorem open_call (hO : OpenSpec) {s u : MachineState} {J V F C : Nat} {cl : KeccakClaim}
    {g : List E × List E × E → TM KeccakOpenings} (hpre : VerifyKeccakPre s) (B : Base s u)
    (hpc : u.pc = 0x80010184) (hJV : (J = 5048 ∧ V = 5072) ∨ (J = 4952 ∧ V = 128))
    (hc : ClaimOut s u (s.getReg .x2 - BitVec.ofNat 64 J) cl) (hl : Lens cl)
    (hx10 : u.getReg .x10 = s.getReg .x2 - 3296) (hx11 : u.getReg .x11 = s.getReg .x11)
    (hx12 : u.getReg .x12 = s.getReg .x12) (hx13 : u.getReg .x13 = 12)
    (hx14 : u.getReg .x14 = s.getReg .x2 - BitVec.ofNat 64 J)
    (hx15 : u.getReg .x15 = BitVec.ofNat 64 F) (hx16 : u.getReg .x16 = BitVec.ofNat 64 C)
    (hFC : F + C ≤ 2) (hx17 : u.getReg .x17 = s.getReg .x2 - BitVec.ofNat 64 V)
    (hR : Rest s u (openRust ⟨(s.getReg .x12).toNat, 12⟩ cl F C
      (eAt u (s.getReg .x2 - BitVec.ofNat 64 V)) >>= g)) :
    ∃ t, Reaches Image.code u t ∧ (Dead Image.code t ∨ (t.pc = returnAddress u ∧ Preserves u t ∧
      Base s t ∧ heapNext u ≤ heapNext t ∧ DFrame u t (SW s u t [(3296, 1584), (V, 24)] true) ∧
      ((t.getMem (s.getReg .x2 - 3296) = errNiche ∧ Fails s) ∨
        (t.getMem (s.getReg .x2 - 3296) ≠ errNiche ∧ ∃ slot row v,
          NewVecE s t (s.getReg .x2 - 3296) slot ∧ eListAt t (s.getReg .x2 - 3272) 64 = row ∧
          eAt t (s.getReg .x2 - 1736) = v ∧ Rest s t (g (slot, row, v)))))) := by
  have hb := bounds hpre
  have hsm := hpre.stack.mapped (by decide) (by decide)
  have hab := hpre.stack.above
  have hnx := hpre.stack.next
  have hrs := hpre.stack.rodata
  have hS := hpre.self.self
  have hss := hpre.selfStack
  have tp : TPre 1584 openStack u := B.tpre hpre 3296 hx10 hx11 (by decide) (by decide)
    (by decide) (le_refl _) (by decide)
  obtain ⟨p1, p2, p3, p4⟩ := vec_facts hpre B hc.point hl.2.1
  obtain ⟨w1, w2, w3, w4⟩ := vec_facts hpre B hc.weights hl.2.2
  obtain ⟨-, r2, -⟩ := readsKW hpre B.heap
  obtain ⟨r1, -, -⟩ := readsKW hpre B.heap
  have hS8 : (s.getReg .x11).toNat + 8 ≤ 2 ^ 64 := by addr_omega [hS]
  have hP48 : (proofAt s (s.getReg .x11)).toNat + 48 ≤ 2 ^ 64 := by addr_omega [hpre.self.proof]
  unfold verifyKeccakStack at hb hsm hab hnx hss hrs
  have st : heapEnd ≤ (stackLo u openStack).toNat := by
    simp only [stackLo, B.x2]; addr_omega [hb, hab]
  have ot : heapEnd ≤ (u.getReg .x10).toNat := by rw [hx10]; addr_omega [hb, hab]
  have vt : heapEnd ≤ (s.getReg .x2 - BitVec.ofNat 64 V).toNat := by
    rcases hJV with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> addr_omega [hb, hab]
  have ec : oClaim u = s.getReg .x2 - BitVec.ofNat 64 J := hx14
  have ev : oValue u = s.getReg .x2 - BitVec.ofNat 64 V := hx17
  have eo : oOut u = s.getReg .x2 - 3296 := hx10
  have ep : oP u = s.getReg .x11 := hx11
  have hpv : ProofApart u (oP u) (oValue u) 24 := by
    rw [ep, ev]
    refine B.frame.proofApart r1 hS8 r2 hP48 (Open.ProofApart.mono' hpre.proofStack ?_ ?_) <;>
      rcases hJV with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> unfold verifyKeccakStack <;> addr_omega [hb]
  have hop : OpenPre u := { tp with
    depth := hx13
    firstCount := by rw [hx15, hx16, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
    claim := by rw [ec]; rcases hJV with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> addr_omega [hb, hsm]
    point := by rw [ec]; exact p1
    weights := by rw [ec]; exact w1
    value := by rw [ev]; rcases hJV with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> addr_omega [hb, hsm]
    claimFree := by
      rw [ec]; rcases hJV with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> refine ⟨Or.inr ?_, ?_⟩ <;>
        addr_omega [hb, hab, hnx]
    pointFree := by rw [ec]; exact p2
    weightsFree := by rw [ec]; exact w2
    valueFree := by
      rw [ev]; rcases hJV with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> refine ⟨Or.inr ?_, ?_⟩ <;>
        addr_omega [hb, hab, hnx]
    claimStack := by
      rw [ec]; simp only [stackLo, B.x2]; rcases hJV with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> addr_omega [hb]
    pointStack := by rw [ec]; exact p3 _ _ st
    weightsStack := by rw [ec]; exact w3 _ _ st
    valueStack := by
      rw [ev]; simp only [stackLo, B.x2]; rcases hJV with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> addr_omega [hb]
    claimOut := by rw [ec, eo]; rcases hJV with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> addr_omega [hb]
    pointOut := by rw [ec]; exact p3 _ _ ot
    weightsOut := by rw [ec]; exact w3 _ _ ot
    valueOut := by rw [ev, eo]; rcases hJV with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> addr_omega [hb]
    claimSelf := by rw [ec, ep]; rcases hJV with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> addr_omega [hb, hss, hS]
    pointSelf := by rw [ec, ep]; exact p4
    weightsSelf := by rw [ec, ep]; exact w4
    valueSelf := by rw [ev, ep]; rcases hJV with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> addr_omega [hb, hss, hS]
    claimValue := by rw [ec, ev]; rcases hJV with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> addr_omega [hb]
    pointValue := by rw [ec, ev]; exact p3 _ _ vt
    weightsValue := by rw [ec, ev]; exact w3 _ _ vt
    proofValue := hpv
    valueRodata := by rw [ev]; rcases hJV with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> addr_omega [hb, hrs] }
  obtain ⟨t, hr, ⟨hpc', hpres, hpost⟩ | hd⟩ := hO u hpc hop
  swap
  · exact ⟨t, hr, Or.inl hd⟩
  have x2t : t.getReg .x2 = s.getReg .x2 - 5248 := (hpres.reg .x2).trans B.x2
  have hok : SlotsOk [(3296, 1584), (V, 24)] = true := by
    rcases hJV with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> decide
  have FR : DFrame u t (SW s u t [(3296, 1584), (V, 24)] true) := hpost.frame.mono fun a ha ↦ by
    simp only [OpenW] at ha
    rcases ha with h | h | h | h | h | h
    · rw [eo] at h; exact Or.inl ⟨(3296, 1584), by simp, h⟩
    · rw [ev] at h; exact Or.inl ⟨(V, 24), by simp, h⟩
    · rw [ep] at h; exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, h⟩)))
    · exact Or.inr (Or.inl (stk_sw hpre B.x2 (le_refl _) h))
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  have Bt := B.step hpre x2t hpost.heap hpost.mono hok FR
  have hcl : claimAt u (oClaim u) = cl := by rw [ec]; exact ClaimOut.claimAt hc
  have hsh : shapeOf u = ⟨(s.getReg .x12).toNat, 12⟩ := by rw [Open.shapeOf_eq hx13, hx12]
  have hF : (u.getReg .x15).toNat = F := by rw [hx15, BitVec.toNat_ofNat]; omega
  have hC : (u.getReg .x16).toNat = C := by rw [hx16, BitVec.toNat_ofNat]; omega
  have e24 : s.getReg .x2 - 3296 + 24 = s.getReg .x2 - 3272 :=
    BitVec.eq_of_toNat_eq (by addr_omega [hb])
  have e1560 : s.getReg .x2 - 3296 + 1560 = s.getReg .x2 - 1736 :=
    BitVec.eq_of_toNat_eq (by addr_omega [hb])
  have hv (T : TState) (hT : TranscriptAt u (s.getReg .x11) T) :
      match (openRust ⟨(s.getReg .x12).toNat, 12⟩ cl F C
          (eAt u (s.getReg .x2 - BitVec.ofNat 64 V))).run T with
      | some ((slot, row, v), T') => vecCap t (s.getReg .x2 - 3296) ≠ errNiche ∧
          NewVecE u t (s.getReg .x2 - 3296) slot ∧ eListAt t (s.getReg .x2 - 3272) 64 = row ∧
          eAt t (s.getReg .x2 - 1736) = v ∧ TranscriptAt t (s.getReg .x11) T'
      | none => vecCap t (s.getReg .x2 - 3296) = errNiche := by
    have h := hpost.value T (by rw [ep]; exact hT)
    rw [hsh, hcl, hF, hC, ev, eo, ep, e24, e1560] at h
    exact h
  refine ⟨t, hr, Or.inr ⟨hpc', hpres, Bt, hpost.mono, FR, ?_⟩⟩
  by_cases hcap : t.getMem (s.getReg .x2 - 3296) = errNiche
  · refine Or.inl ⟨hcap, hR.fail fun T hT ↦ ?_⟩
    have h := hv T hT
    generalize (openRust ⟨(s.getReg .x12).toNat, 12⟩ cl F C
      (eAt u (s.getReg .x2 - BitVec.ofNat 64 V))).run T = o at h ⊢
    rcases o with _ | ⟨⟨slot, row, v⟩, T'⟩
    · rfl
    · exact absurd hcap h.1
  · refine Or.inr ⟨hcap, ?_⟩
    obtain ⟨T₀, hT₀⟩ := Open.exists_T u (s.getReg .x11)
    have h₀ := hv T₀ hT₀
    generalize (openRust ⟨(s.getReg .x12).toNat, 12⟩ cl F C
      (eAt u (s.getReg .x2 - BitVec.ofNat 64 V))).run T₀ = o at h₀
    rcases o with _ | ⟨⟨slot, row, v⟩, T₀'⟩
    · exact absurd h₀ hcap
    obtain ⟨-, hs₀, hrow₀, hv₀, -⟩ := h₀
    refine ⟨slot, row, v, Open.newVecE_mono hs₀ B.mono, hrow₀, hv₀, hR.step fun T hT ↦ ?_⟩
    have h := hv T hT
    generalize (openRust ⟨(s.getReg .x12).toNat, 12⟩ cl F C
      (eAt u (s.getReg .x2 - BitVec.ofNat 64 V))).run T = o at h
    rcases o with _ | ⟨⟨slot₁, row₁, v₁⟩, T₁⟩
    · exact absurd h hcap
    obtain ⟨-, hs₁, hrow₁, hv₁, hT₁⟩ := h
    have e1 : slot₁ = slot := hs₁.elems.symm.trans hs₀.elems
    subst e1
    subst hrow₁
    subst hv₁
    refine ⟨T₁, ?_, hT₁⟩
    rw [hrow₀, hv₀]

/-- `memcpy(f + 5248 - D, f + 5248 - S, 1536)`: a 64-element row. -/
theorem memcpy_row (hMC : Runtime.MemcpySpec 0x800126e4) {s w : MachineState}
    (hpre : VerifyKeccakPre s) (B : Base s w) (hpc : w.pc = 0x800126e4) {D S : Nat}
    (hD : 1640 ≤ D ∧ D ≤ 5248 ∧ D % 8 = 0) (hS : 1536 ≤ S ∧ S ≤ 5248 ∧ S % 8 = 0)
    (hDS : D + 1536 ≤ S ∨ S + 1536 ≤ D)
    (hx10 : w.getReg .x10 = s.getReg .x2 - BitVec.ofNat 64 D)
    (hx11 : w.getReg .x11 = s.getReg .x2 - BitVec.ofNat 64 S) (hx12 : w.getReg .x12 = 1536) :
    ∃ w', Reaches Image.code w w' ∧ (Dead Image.code w' ∨ (w'.pc = returnAddress w ∧
      Preserves w w' ∧ DFrame w w' (SW s w w' [(D, 1536)] false) ∧ heapNext w' = heapNext w ∧
      eListAt w' (s.getReg .x2 - BitVec.ofNat 64 D) 64 =
        eListAt w (s.getReg .x2 - BitVec.ofNat 64 S) 64)) := by
  have hb := bounds hpre
  have hsm := hpre.stack.mapped (by decide) (by decide)
  have hnx := hpre.stack.next
  unfold verifyKeccakStack at hb hsm hnx
  obtain ⟨hD1, hD2, hD3⟩ := hD
  obtain ⟨hS1, hS2, hS3⟩ := hS
  have hn : (w.getReg .x12).toNat = 1536 := by rw [hx12]; rfl
  have hmc : Runtime.MemcpyPre w := {
    dst := by rw [hx10, hn]; addr_omega [hb, hsm, hD1, hD2]
    src := by rw [hx11, hn]; addr_omega [hb, hsm, hS1, hS2]
    apart := by rw [hx10, hx11, hn]; addr_omega [hb, hD2, hS2, hDS]
    stack := (hpre.stack.sub 5248 B.x2 (by unfold verifyKeccakStack; decide) (by decide)
      (by decide) (by decide) (by decide)).toStackOk
    dstStack := by rw [hx10, hn]; simp only [stackLo, B.x2]; addr_omega [hb, hD1, hD2]
    srcStack := by rw [hx11, hn]; simp only [stackLo, B.x2]; addr_omega [hb, hS1, hS2] }
  obtain ⟨w', hr, ⟨hpc', hpres, hpost⟩ | hd⟩ := hMC w hpc hmc
  swap
  · exact ⟨w', hr, Or.inl hd⟩
  have bytes := hpost.bytes
  rw [hx10, hx11, hn] at bytes
  have hN0 : w'.getMem nextAddr = w.getMem nextAddr :=
    DFrame.of_byteFrame hpost.frame _ fun i hi h ↦ by
      rw [hx10, hn] at h
      simp only [stackLo, B.x2] at h
      rcases h with h | h <;> addr_omega [h, hi, hb, hnx, hD1, hD2]
  refine ⟨w', hr, Or.inr ⟨hpc', hpres, (DFrame.of_byteFrame hpost.frame).mono fun a ha ↦ ?_,
    by simp only [heapNext, hN0],
    eListAt_eq_of_bytesAt (by rw [show 24 * 64 = 1536 from rfl]; exact bytes)
      (by addr_omega [hb, hD2, hD3]) (by addr_omega [hb, hS2, hS3])⟩⟩
  rw [hx10, hn] at ha
  rcases ha with h | h
  · exact Or.inl ⟨(D, 1536), List.mem_singleton_self _, h⟩
  · exact Or.inr (Or.inl (stk_sw hpre B.x2 (k := memcpyStack) (by decide) h))

/-- `mul(f + 5248 - Ko, f + 5248 - Kl, f + 5248 - Kr)`. -/
theorem mul_slots (hM : MulSpec) {s u : MachineState} (hpre : VerifyKeccakPre s) (B : Base s u)
    (hpc : u.pc = 0x80008c48) {Ko Kl Kr : Nat} (hKo : 128 ≤ Ko ∧ Ko ≤ 5248 ∧ Ko % 8 = 0)
    (hKl : 24 ≤ Kl ∧ Kl ≤ 5248 ∧ Kl % 8 = 0) (hKr : 24 ≤ Kr ∧ Kr ≤ 5248 ∧ Kr % 8 = 0)
    (hol : Ko + 24 ≤ Kl ∨ Kl + 24 ≤ Ko) (hor : Ko + 24 ≤ Kr ∨ Kr + 24 ≤ Ko)
    (hx10 : u.getReg .x10 = s.getReg .x2 - BitVec.ofNat 64 Ko)
    (hx11 : u.getReg .x11 = s.getReg .x2 - BitVec.ofNat 64 Kl)
    (hx12 : u.getReg .x12 = s.getReg .x2 - BitVec.ofNat 64 Kr) :
    ∃ t, Reaches Image.code u t ∧ (Dead Image.code t ∨ (t.pc = returnAddress u ∧
      Preserves u t ∧ Base s t ∧ heapNext t = heapNext u ∧
      DFrame u t (SW s u t [(Ko, 24)] false) ∧
      eAt t (s.getReg .x2 - BitVec.ofNat 64 Ko) =
        eAt u (s.getReg .x2 - BitVec.ofNat 64 Kl) * eAt u (s.getReg .x2 - BitVec.ofNat 64 Kr))) := by
  have hb := bounds hpre
  have hnx := hpre.stack.next
  obtain ⟨hKo1, hKo2, hKo3⟩ := hKo
  obtain ⟨hKl1, hKl2, hKl3⟩ := hKl
  obtain ⟨hKr1, hKr2, hKr3⟩ := hKr
  have hmp : MulPre u := mul_pre hpre B.x2 (B.rodata hpre) Ko hx10 (by omega) hKo2 hKo3
    (by rw [hx11]; exact slot_vmr hpre (by omega) hKl2 hKl3)
    (by rw [hx11]; unfold verifyKeccakStack at hb; addr_omega [hb, hKl1, hKl2])
    (by rw [hx10, hx11]; unfold verifyKeccakStack at hb; addr_omega [hb, hKo2, hKl2, hol])
    (by rw [hx12]; exact slot_vmr hpre (by omega) hKr2 hKr3)
    (by rw [hx12]; unfold verifyKeccakStack at hb; addr_omega [hb, hKr1, hKr2])
    (by rw [hx10, hx12]; unfold verifyKeccakStack at hb; addr_omega [hb, hKo2, hKr2, hor])
  obtain ⟨t, hr, ⟨hpc', hpres, hpost⟩ | hd⟩ := hM u hpc hmp
  swap
  · exact ⟨t, hr, Or.inl hd⟩
  have x2t : t.getReg .x2 = s.getReg .x2 - 5248 := (hpres.reg .x2).trans B.x2
  unfold verifyKeccakStack at hb hnx
  have F : DFrame u t (SW s u t [(Ko, 24)] false) := (mul_frame B.x2 hpost).mono fun a h ↦ by
    rcases h with h | h
    · exact Or.inl (out_sw (K := Ko) (n := 24) hx10 h)
    · exact Or.inr (Or.inl (by unfold verifyKeccakStack; addr_omega [h, hb]))
  have hN : heapNext t = heapNext u := by
    simp only [heapNext]
    rw [hpost.frame _ (by rw [hx10]; addr_omega [hb, hnx, hKo1, hKo2])
      (by simp only [stackLo, B.x2, mulStack]; addr_omega [hb, hnx])]
  have hok : SlotsOk [(Ko, 24)] = true := by
    simp only [SlotsOk, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
      decide_eq_true_eq]
    omega
  refine ⟨t, hr, Or.inr ⟨hpc', hpres,
    B.step hpre x2t ⟨by rw [hN]; exact B.heap.lo, by rw [hN]; exact B.heap.hi⟩ (le_of_eq hN.symm)
      hok F, hN, F, ?_⟩⟩
  have hv := hpost.value
  rw [hx10, hx11, hx12] at hv
  exact hv

end Rv64Verifier.Gkr.Keccak
