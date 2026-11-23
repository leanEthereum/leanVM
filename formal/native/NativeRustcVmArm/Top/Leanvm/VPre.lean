module

public import NativeRustcVmArm.Top.Leanvm.Calls3

/-!
# `leanvm_verify`: `verify`'s precondition

Before `bl verify`, with the frame's body, the public input at the frame's byte 8, the `Decoded`
at its byte 40 naming the decoded area, which holds the decoded proof, and `verify`'s arguments in
X0 to X4: `verify`'s precondition holds (`vPre`).
-/

namespace NativeRustcVmArm.Top.Leanvm

open NativeRustcArm NativeRustcArm.Sym NativeVm
open NativeRustcVm (WordAt WordsAt Region)
open NativeRustcVm.Top (workAreaBytes entryRegions ApartFrom Aligned)
open NativeRustcVm.Transcript (DecArea DecFieldsAt DecodedAt)
open NativeVm.Model (EW OpeningW)

/-- The decoded area of the wire's `L` bytes. -/
@[expose] public def decArea (a : NativeVm.Entry.Areas) (L : Nat) : DecArea :=
  ⟨a.decoded.toBitVec, decodedWords L, L⟩

public section

/-- The read-only data stays at its labels while only the verifier's areas change. -/
theorem rodata_R2 [Labels] {a : NativeVm.Entry.Areas} {bytes : List UInt8} {bytecode : List UInt64}
    {pub : Vector UInt64 4} {m0 st : MachineData}
    (hpre : LeanvmVerifyPre a bytes bytecode pub m0)
    (hs : SameOutside m0.dmem st.dmem (R2 a bytes.length m0))
    (hsp : st.regs.SP.toBitVec = frameOf m0) : RodataAt st verifyStack := by
  have g := geo_of hpre
  obtain ⟨-, hrod, -, -, -, hapR⟩ := hpre
  have hs' := g.s
  have hF := g.F
  have hS := leanvmVerifyStack_eq
  have hsb : (stackBelow m0 leanvmVerifyStack).toNat = m0.regs.SP.toBitVec.toNat - 19344 := g.sb
  have hV : verifyStack = 19216 := rfl
  have hsbV : (stackBelow st verifyStack).toNat = m0.regs.SP.toBitVec.toNat - 19344 := by
    show (st.regs.SP.toBitVec - BitVec.ofNat 64 verifyStack).toNat = _
    rw [hsp, hV, toNat_subAddr (by rw [hF]; omega), hF]; omega
  have hdp := decodedWords_pos bytes.length
  have hwle := workAreaBytes_le bytecode.length
  refine rodataAt_keep hrod hs (fun p hp t ↦ ?_) (by rw [hsb, hsbV])
    (by rw [hsb, hsbV, hS, hV]; omega)
  have hst := hrod.apart t
  unfold NativeRustcVm.Apart at hst
  rw [hsb, hS] at hst
  rcases hp with hp | hp | hp
  · unfold InStack at hp; rw [hS] at hp; omega
  · have h := hapR ⟨a.decoded.toBitVec, 8 * decodedWords bytes.length⟩ (by simp [entryRegions])
      (by show 0 < 8 * decodedWords bytes.length; omega) t
    unfold NativeRustcVm.Apart at h
    rw [inRange_nat g.decN] at hp
    simp only at h; omega
  · have h := hapR ⟨a.work.toBitVec, 8 * NativeVm.Entry.workWords bytecode.length⟩ (by simp [entryRegions])
      (by show 0 < 8 * NativeVm.Entry.workWords bytecode.length
          have : workAreaBytes = 495552 := rfl
          omega) t
    unfold NativeRustcVm.Apart at h
    rw [inRange_nat g.workN] at hp
    simp only at h; omega

/-- **`verify`'s precondition.** -/
theorem vPre [Labels] {a : NativeVm.Entry.Areas} {bytes : List UInt8} {bytecode : List UInt64}
    {pub : Vector UInt64 4} {m0 st : MachineData} {stream : Array EW}
    {openings : Array (Array OpeningW)}
    (hpre : LeanvmVerifyPre a bytes bytecode pub m0)
    (hB : Body m0 128 slots (R2 a bytes.length m0) st)
    (hdecF : DecFieldsAt st.dmem (frameOf m0 + BitVec.ofNat 64 40) (decArea a bytes.length))
    (hdec : DecodedAt st.dmem (decArea a bytes.length) stream openings)
    (hx0 : 0 < bytecode.length → st.regs.X0 = a.bytecode)
    (hx1 : st.regs.X1 = bytecode.length.toUInt64)
    (hx2 : st.regs.X2.toBitVec = frameOf m0 + BitVec.ofNat 64 8)
    (hx3 : st.regs.X3.toBitVec = frameOf m0 + BitVec.ofNat 64 40)
    (hx4 : st.regs.X4 = a.work) : VerifyPre (decArea a bytes.length) stream openings st := by
  have g := geo_of hpre
  have hrodK := rodata_R2 hpre hB.same hB.sp
  obtain ⟨⟨-, -, hmap⟩, hrod, hin, -, -, hapR⟩ := hpre
  have hs := g.s
  have hF := g.F
  have hS := leanvmVerifyStack_eq
  have hsl := m0.regs.SP.toBitVec.isLt
  have hsb : (m0.regs.SP.toBitVec - BitVec.ofNat 64 leanvmVerifyStack).toNat =
      m0.regs.SP.toBitVec.toNat - 19344 := g.sb
  have hV : verifyStack = 19216 := rfl
  have hsp : st.regs.SP.toBitVec = frameOf m0 := hB.sp
  have hsbV : (stackBelow st verifyStack).toNat = m0.regs.SP.toBitVec.toNat - 19344 := by
    show (st.regs.SP.toBitVec - BitVec.ofNat 64 verifyStack).toNat = _
    rw [hsp, hV, toNat_subAddr (by rw [hF]; omega), hF]; omega
  have hn32 := hin.bcSmall
  have hX1 : st.regs.X1.toNat = bytecode.length := by rw [hx1]; exact natToU64 (by omega)
  have hdp := decodedWords_pos bytes.length
  have hwle := workAreaBytes_le bytecode.length
  have hwa : workAreaBytes = 495552 := rfl
  have gd := g.dec
  have gdN := g.decN
  have gw := g.work
  have gwN := g.workN
  have gdw := g.decWork
  have ed : a.decoded.toBitVec.toNat = a.decoded.toNat := rfl
  have ew : a.work.toBitVec.toNat = a.work.toNat := rfl
  have eb : a.bytecode.toBitVec.toNat = a.bytecode.toNat := rfl
  have hF8 : (frameOf m0 + BitVec.ofNat 64 8).toNat = m0.regs.SP.toBitVec.toNat - 120 := by
    rw [toNat_addr (by rw [hF]; omega), hF]; omega
  have hF40 : (frameOf m0 + BitVec.ofNat 64 40).toNat = m0.regs.SP.toBitVec.toNat - 88 := by
    rw [toNat_addr (by rw [hF]; omega), hF]; omega
  have hFm : Mapped st.dmem (frameOf m0) 128 :=
    Mapped.kept (Mapped.within hmap (by rw [hsb]; omega) (by rw [hsb, hF]; omega)
      (by rw [hsb, hF]; omega)) hB.kept
  have hdM : Mapped st.dmem a.decoded.toBitVec (8 * decodedWords bytes.length) :=
    Mapped.kept (NativeRustcVm.mapped_of_wordView hin.decSome) hB.kept
  have hwM : Mapped st.dmem a.work.toBitVec (8 * NativeVm.Entry.workWords bytecode.length) :=
    Mapped.kept (NativeRustcVm.mapped_of_wordView hin.workSome) hB.kept
  -- The frame's bytes apart from the read-only data.
  have hFR : ∀ (o n : Nat), o + n ≤ 128 → RodataApart (frameOf m0 + BitVec.ofNat 64 o) n :=
    fun o n hon t ↦ by
      have := hrod.apart t
      unfold NativeRustcVm.Apart at this ⊢
      rw [show (stackBelow m0 leanvmVerifyStack).toNat = m0.regs.SP.toBitVec.toNat - 19344
        from hsb, hS] at this
      rw [toNat_addr (by rw [hF]; omega), hF]
      omega
  refine ⟨⟨?_, ?_, ?_⟩, hrodK, by rw [hX1]; omega,
    (by show DecFieldsAt _ st.regs.X3.toBitVec _; rw [hx3]; exact hdecF),
    hdec, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨hdM, gdN⟩, ⟨?_, ?_⟩, ?_, ?_,
    fun hn ↦ ⟨?_, ?_⟩⟩
  · show st.regs.SP.toBitVec.toNat % 16 = 0
    rw [hsp, hF]; have := g.al; omega
  · show verifyStack ≤ st.regs.SP.toBitVec.toNat
    rw [hsp, hF, hV]; omega
  · show Mapped st.dmem (st.regs.SP.toBitVec - BitVec.ofNat 64 verifyStack) verifyStack
    refine Mapped.kept (Mapped.within hmap (by rw [hsb]; omega) ?_ ?_) hB.kept
    · rw [hsb, hsp, hV, toNat_subAddr (by rw [hF]; omega), hF]; omega
    · rw [hsb, hsp, hV, toNat_subAddr (by rw [hF]; omega), hF]; omega
  · show Mapped st.dmem st.regs.X0.toBitVec (8 * st.regs.X1.toNat)
    rw [hX1]
    by_cases h0 : bytecode.length = 0
    · rw [h0]; exact fun i hi ↦ absurd hi (Nat.not_lt_zero _)
    · rw [hx0 (by omega)]
      exact Mapped.kept (NativeRustcVm.WordsAt.mapped
        (NativeRustcVm.wordsAt_of_wordView hin.bcWords)) hB.kept
  · show st.regs.X0.toBitVec.toNat + 8 * st.regs.X1.toNat ≤ 2 ^ 64
    rw [hX1]
    by_cases h0 : bytecode.length = 0
    · rw [h0]; have := st.regs.X0.toBitVec.isLt; omega
    · rw [hx0 (by omega)]; exact g.bcN
  · show Mapped st.dmem st.regs.X2.toBitVec 32
    rw [hx2]; exact Mapped.within hFm (by rw [hF]; omega) (by rw [hF8, hF]; omega)
      (by rw [hF8, hF]; omega)
  · show st.regs.X2.toBitVec.toNat + 32 ≤ 2 ^ 64
    rw [hx2, hF8]; omega
  · show Mapped st.dmem st.regs.X3.toBitVec 24
    rw [hx3]; exact Mapped.within hFm (by rw [hF]; omega) (by rw [hF40, hF]; omega)
      (by rw [hF40, hF]; omega)
  · show st.regs.X3.toBitVec.toNat + 24 ≤ 2 ^ 64
    rw [hx3, hF40]; omega
  · show Mapped st.dmem st.regs.X4.toBitVec workAreaBytes
    rw [hx4]; exact NativeRustcVm.Mapped.mono hwM (by omega)
  · show st.regs.X4.toBitVec.toNat + workAreaBytes ≤ 2 ^ 64
    rw [hx4]; exact gwN
  · show NativeRustcVm.Disjoint [⟨stackBelow st verifyStack, verifyStack⟩,
      ⟨st.regs.X2.toBitVec, 32⟩, ⟨st.regs.X3.toBitVec, 24⟩,
      ⟨a.decoded.toBitVec, 8 * decodedWords bytes.length⟩, ⟨st.regs.X4.toBitVec, workAreaBytes⟩]
    rw [hx2, hx3, hx4]
    refine disjoint_five ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> dsimp only [NativeRustcVm.Apart] <;>
      omega
  · intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · show RodataApart st.regs.X2.toBitVec 32
      rw [hx2]; exact hFR 8 32 (by omega)
    · show RodataApart st.regs.X3.toBitVec 24
      rw [hx3]; exact hFR 40 24 (by omega)
    · exact fun t ↦ hapR ⟨a.decoded.toBitVec, 8 * decodedWords bytes.length⟩
        (by simp [entryRegions]) (by show 0 < 8 * decodedWords bytes.length; omega) t
    · show RodataApart st.regs.X4.toBitVec workAreaBytes
      rw [hx4]
      intro t
      have h := hapR ⟨a.work.toBitVec, 8 * NativeVm.Entry.workWords bytecode.length⟩ (by simp [entryRegions])
        (by show 0 < 8 * NativeVm.Entry.workWords bytecode.length; omega) t
      unfold NativeRustcVm.Apart at h ⊢
      simp only at h
      omega
  · have hn' : 0 < bytecode.length := by rw [← hX1]; exact hn
    have gb := g.bc hn'
    have gbd := g.bcDec
    have gbw := g.bcWork
    show NativeRustcVm.Disjoint [⟨stackBelow st verifyStack, verifyStack⟩,
      ⟨st.regs.X0.toBitVec, 8 * st.regs.X1.toNat⟩,
      ⟨a.decoded.toBitVec, 8 * decodedWords bytes.length⟩, ⟨st.regs.X4.toBitVec, workAreaBytes⟩]
    rw [hx0 hn', hX1, hx4]
    refine disjoint_four ?_ ?_ ?_ ?_ ?_ ?_ <;> dsimp only [NativeRustcVm.Apart] <;> omega
  · have hn' : 0 < bytecode.length := by rw [← hX1]; exact hn
    show RodataApart st.regs.X0.toBitVec (8 * st.regs.X1.toNat)
    rw [hx0 hn', hX1]
    exact fun t ↦ hapR ⟨a.bytecode.toBitVec, 8 * bytecode.length⟩ (by simp [entryRegions])
      (by show 0 < 8 * bytecode.length; omega) t

end

end NativeRustcVmArm.Top.Leanvm
