module

public import NativeRustcVmX64.Top.Leanvm.Checks
public import NativeRustcVmX64.Code.Vm.Decode.Names

/-!
# `leanvm_verify`: the call to `decode` (x86-64)

`decodeCall`: at `decode`'s call (after `b10` or `b14`, the frame's RSP at offset `0`), the
arguments in RDI to R8 (the wire, `L`, the decoded area, `decodedWords L`, the working area) meet
`decode`'s precondition; after it, `AD`: the frame, the changes in the stack and the two areas, the
callee-saved registers, the public input in the frame; and the verdict of `decodeM` in AL with the
decoded proof in the area.
-/

namespace NativeRustcVmX64.Top.Leanvm

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.LeanvmVerify NativeRustcVmX64.Transcript
open NativeRustcVmX64.Top NativeVm NativeVm.Wire NativeRustcVm.Wire NativeRustcVm.Transcript
open NativeRustcVm.Top (workAreaBytes usedRegions ApartFrom Aligned)
open NativeVm.Transcript (wd)

/-- What `leanvm_verify` may change: its stack, the decoded and the working areas. -/
@[expose] public def Out (m0 : MachineData) (a : NativeVm.Entry.Areas) (L : Nat) (q : BitVec 64) : Prop :=
  NativeRustcVm.InRange (stackBelow m0 18816) 18816 q ∨
    NativeRustcVm.InRange a.decoded.toBitVec (8 * decodedWords L) q ∨
    NativeRustcVm.InRange a.work.toBitVec workAreaBytes q

/-- After `decode`: the frame; the changes; the callee-saved registers; the public input in the
frame. -/
public structure AD [Labels] (a : NativeVm.Entry.Areas) (bytes : List UInt8) (bytecode : List UInt64)
    (pub : Vector UInt64 4) (m0 d : MachineData) : Prop where
  frame : Frame m0 112 slots 8 d
  same : NativeRustcVm.SameOutside m0.dmem d.dmem (Out m0 a bytes.length)
  rbx : reg d .rbx = BitVec.ofNat 64 bytes.length
  rbp : reg d .rbp = a.bytecode.toBitVec
  r12 : reg d .r12 = a.decoded.toBitVec
  r13 : reg d .r13 = a.work.toBitVec
  r14 : reg d .r14 = BitVec.ofNat 64 bytecode.length
  r15 : reg d .r15 = BitVec.ofNat 64 (decodedWords bytes.length)
  pubw : NativeRustcVm.WordsAt d.dmem (off (stackBelow m0 112) 8) pub.toList

public section

/-- The wire's bytes at its address. -/
theorem wireBytes {d : DataMem} {a : NativeVm.Entry.Areas} {bytes : List UInt8} {bytecode : List UInt64}
    {pub : Vector UInt64 4} {ctx : UInt64}
    (hin : NativeVm.Entry.CheckedEntryPre d ctx a bytes bytecode pub) :
    NativeRustcVm.BytesAt d a.wire.toBitVec bytes := hin.wire

theorem rc_len : (NativeRustcVm.Data.Item.bytes .keccakRC).length = 192 := by
  rw [NativeRustcVm.Data.Item.bytes, NativeRustcVm.length_wordsBytes, keccakRC_eq]; rfl

variable [Host] {k : Nat}

/-- **The call to `decode`.** -/
theorem decodeCall (hdec : Spec (Labels.label NativeRustcVmX64.Vm.Decode.entryLabel) DecodePre DecodePost)
    {a : NativeVm.Entry.Areas} {bytes : List UInt8} {bytecode : List UInt64} {pub : Vector UInt64 4}
    {m0 : MachineData} (hpre : LeanvmVerifyPre a bytes bytecode pub m0) {st : MachineState}
    {next : Int64} {env : NativeRustcX64.Sym.Env} (hpc : PcOk env (.call NativeRustcVmX64.Vm.Decode.entryLabel) next st)
    (hf : Frame m0 112 slots 0 st.data)
    (hs : NativeRustcVm.SameOutside m0.dmem st.data.dmem
      (NativeRustcVm.InRange (stackBelow m0 112) 112))
    {bp : BitVec 64} (hrdi : reg st.data .rdi = bp)
    (hbp : bytes.length = 0 ∧ bp = 1#64 ∨ 0 < bytes.length ∧ bp = a.wire.toBitVec)
    (hrsi : (reg st.data .rsi).toNat = bytes.length) (hrdx : reg st.data .rdx = a.decoded.toBitVec)
    (hrcx : (reg st.data .rcx).toNat = decodedWords bytes.length)
    (hr8 : reg st.data .r8 = a.work.toBitVec)
    (hrbx : reg st.data .rbx = BitVec.ofNat 64 bytes.length)
    (hrbp : reg st.data .rbp = a.bytecode.toBitVec) (hr12 : reg st.data .r12 = a.decoded.toBitVec)
    (hr13 : reg st.data .r13 = a.work.toBitVec)
    (hr14 : reg st.data .r14 = BitVec.ofNat 64 bytecode.length)
    (hr15 : reg st.data .r15 = BitVec.ofNat 64 (decodedWords bytes.length))
    (hpub : NativeRustcVm.WordsAt st.data.dmem (off (stackBelow m0 112) 8) pub.toList) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = next ∧ AD a bytes bytecode pub m0 st'.data ∧
      match decodeM bytes with
      | some r => boolRet st'.data = 1 ∧ DecodedAt st'.data.dmem
          ⟨a.decoded.toBitVec, decodedWords bytes.length, bytes.length⟩ (streamW r.1) (openingsW r.2)
      | none => boolRet st'.data = 0) st := by
  have g := geo_of hpre
  obtain ⟨hst, hrod, hin, -, -, hapR, hgot⟩ := hpre
  have hS := leanvmVerifyStack_eq
  have hR := g.R
  have h8 := g.e8
  have hBn := g.F
  have hn : leanvmVerifyStack ≤ (rspOf m0).toNat := hst.1
  have hfnw := frame_noWrap (F := 112) hst (by decide)
  have hsp : rspOf st.data = stackBelow m0 112 := by rw [hf.sp, off_zero]
  have hL := hin.L32
  have hwa := workAreaBytes_le
  have hdp := decodedWords_pos bytes.length
  have hwb : NativeRustcVm.Wire.workBytes ≤ workAreaBytes := by decide
  have gdec := g.dec
  have gdecN := g.decN
  have gwork := g.work
  have gworkN := g.workN
  have gdw := g.decWork
  have hrc := hrod.rcAt
  have hrcN := hrc.2.1
  have hrcA := hrc.2.2
  unfold NativeRustcVm.Apart at hrcA
  unfold NativeRustcVm.NoWrap at hrcN
  rw [hS, lsb_eq] at hrcA
  -- the read-only data and the areas
  have rcApart : ∀ (x : UInt64) (sz : Nat),
      (⟨x.toBitVec, sz⟩ : NativeRustcVm.Region) ∈
        usedRegions (ctxOf m0) a bytes.length bytecode.length →
      0 < sz → x.toNat + sz ≤ rcAddr.toNat ∨ rcAddr.toNat + 192 ≤ x.toNat := fun x sz hr hp ↦ by
    have h := hapR _ hr hp .keccakRC
    unfold NativeRustcVm.Apart at h
    rw [rc_len] at h
    exact h
  have rcD := rcApart a.decoded (8 * decodedWords bytes.length) (by simp [usedRegions]) (by omega)
  have rcW := rcApart a.work (8 * NativeVm.Entry.workWords) (by simp [usedRegions])
    (by unfold workAreaBytes NativeRustcVm.Top.workAreaWords at hwa; omega)
  have hstk : (stackBelow st.data 1296).toNat = lsb m0 + 17408 := by
    rw [stackBelow_callee hsp (by show 112 + 1296 ≤ (rspOf m0).toNat; omega),
      stackBelow_toNat (m := m0) (n := 112 + 1296) (by omega), hR]
    omega
  have hdM : NativeRustcVm.Mapped m0.dmem a.decoded.toBitVec (8 * decodedWords bytes.length) :=
    NativeRustcVm.mapped_of_wordView hin.decSome
  have hwM : NativeRustcVm.Mapped m0.dmem a.work.toBitVec workAreaBytes :=
    NativeRustcVm.Mapped.mono (NativeRustcVm.mapped_of_wordView hin.workSome) hwa
  have hwireM : NativeRustcVm.Mapped m0.dmem a.wire.toBitVec bytes.length :=
    (wireBytes hin).mapped
  have hwN : a.wire.toNat + bytes.length ≤ 2 ^ 64 := by
    have := g.wireN; omega
  -- the frame's changes are in the stack
  have hfr : ∀ q, NativeRustcVm.InRange (stackBelow m0 112) 112 q →
      lsb m0 + 18704 ≤ q.toNat ∧ q.toNat < lsb m0 + 18816 := fun q h ↦ by
    rw [inR (by unfold NativeRustcVm.NoWrap; omega), hBn] at h
    omega
  have hrcK : ∀ i < 192, st.data.dmem.get? (rcAddr + BitVec.ofNat 64 i) =
      m0.dmem.get? (rcAddr + BitVec.ofNat 64 i) :=
    rc_keep hs fun q hq h ↦ by
      have := hfr q hq
      rw [inR (by unfold NativeRustcVm.NoWrap; omega)] at h
      omega
  -- `decode`'s precondition
  have hpre' : DecodePre st.data := by
    unfold DecodePre
    simp only [hrdi, hrsi, hrdx, hrcx, hr8]
    refine ⟨stackOk_callee hst hf.kept hsp (by show 112 + 1296 ≤ _; omega),
      RcAt.callee hrc hrcK hsp hn (by show 112 + 1296 ≤ _; omega), hL, le_refl _, ?_,
      ⟨Mapped.keeps hdM hf.kept, gdecN⟩,
      ⟨Mapped.keeps (NativeRustcVm.Mapped.mono hwM hwb) hf.kept, by
        show a.work.toBitVec.toNat + NativeRustcVm.Wire.workBytes ≤ 2 ^ 64; simp; omega⟩,
      ?_, (fun hL0 ↦ ?_), ?_⟩
    · rcases hbp with ⟨h0, rfl⟩ | ⟨h0, rfl⟩
      · rw [h0]
        exact ⟨fun i hi ↦ absurd hi (Nat.not_lt_zero _), by unfold NativeRustcVm.NoWrap; simp⟩
      · exact ⟨Mapped.keeps hwireM hf.kept, by show a.wire.toBitVec.toNat + _ ≤ _; simp; omega⟩
    · simp only [NativeRustcVm.disjoint_cons_iff, List.forall_mem_cons, List.mem_nil_iff,
        false_implies, implies_true, NativeRustcVm.disjoint_nil, and_true, NativeRustcVm.Apart,
        stackR, rcR, show decodeStack = 1296 from rfl, hstk, UInt64.toNat_toBitVec]
      refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;> omega
    · rcases hbp with ⟨h0, -⟩ | ⟨-, rfl⟩
      · omega
      have gw := g.wire hL0
      have gwd := g.wireDec (by omega)
      have gww := g.wireWork (by omega)
      have rcWi := rcApart a.wire (bytes.length) (by simp [usedRegions])
        (by omega)
      simp only [NativeRustcVm.disjoint_cons_iff, List.forall_mem_cons, List.mem_nil_iff,
        false_implies, implies_true, NativeRustcVm.disjoint_nil, and_true, NativeRustcVm.Apart,
        stackR, rcR, show decodeStack = 1296 from rfl, hstk, UInt64.toNat_toBitVec]
      refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;> omega
    · apply NativeRustcVmX64.GotAt.callee hgot
      · apply NativeRustcVmX64.GotAt.unchanged_stack hgot hst
        intro q hq
        exact hs q fun h => hq (by
          have hh := hfr q h
          change NativeRustcVm.InRange (stackBelow m0 leanvmVerifyStack) leanvmVerifyStack q
          rw [hS, inR (by unfold NativeRustcVm.NoWrap; rw [lsb_eq]; omega), lsb_eq]
          omega)
      · rw [hS, lsb_eq, show decodeStack = 1296 from rfl, hstk]
        omega
      · rw [hS, lsb_eq, show decodeStack = 1296 from rfl, hstk]
        omega
      · intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl
        · exact ⟨(rcAddr, 192), by simp [rc_mem_rodataAreas], Nat.le_refl _, Nat.le_refl _⟩
        · exact ⟨(a.decoded.toBitVec, 8 * decodedWords bytes.length),
            by simp [usedRegions], Nat.le_refl _, Nat.le_refl _⟩
        · refine ⟨(a.work.toBitVec, 8 * NativeVm.Entry.workWords),
            by simp [usedRegions], Nat.le_refl _, ?_⟩
          dsimp only
          omega
  refine call_then hpc hdec hpre' fun st' hpc' hrsp' hpost ↦ ?_
  obtain ⟨hres, hs', hsv'⟩ := hpost
  simp only [hrdi, hrsi, hrdx, hrcx, hr8] at hres hs'
  -- what `decode` changes
  have hR' : ∀ q, NativeRustcVm.InAny [⟨a.decoded.toBitVec, 8 * decodedWords bytes.length⟩,
      ⟨a.work.toBitVec, NativeRustcVm.Wire.workBytes⟩, frameR st.data decodeStack] q →
      (lsb m0 ≤ q.toNat ∧ q.toNat < lsb m0 + 18704) ∨
        NativeRustcVm.InRange a.decoded.toBitVec (8 * decodedWords bytes.length) q ∨
        NativeRustcVm.InRange a.work.toBitVec workAreaBytes q := by
    intro q h
    rcases inAny3 h with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (inRange_mono h hwb))
    · left
      change NativeRustcVm.InRange (stackBelow st.data decodeStack) decodeStack q at h
      rw [show decodeStack = 1296 from rfl] at h
      rw [inR (by unfold NativeRustcVm.NoWrap; rw [hstk]; omega), hstk] at h
      omega
  have hnotF : ∀ q, (NativeRustcVm.InRange a.decoded.toBitVec (8 * decodedWords bytes.length) q ∨
      NativeRustcVm.InRange a.work.toBitVec workAreaBytes q) →
      q.toNat < lsb m0 ∨ lsb m0 + 18824 ≤ q.toNat := by
    rintro q (h | h)
    · rw [inR (by unfold NativeRustcVm.NoWrap; simp; omega)] at h
      simp only [UInt64.toNat_toBitVec] at h
      omega
    · rw [inR (by unfold NativeRustcVm.NoWrap; simp; omega)] at h
      simp only [UInt64.toNat_toBitVec] at h
      omega
  have hf' : Frame m0 112 slots 8 st'.data := by
    refine Frame.call_low hf hsv' hrsp' hs' (L := 8) (fun q h ↦ ?_) (fun p hp ↦ by
      have := slots_ge p hp; omega) (by decide) hfnw slots_le
    rw [hBn]
    rcases hR' q h with h | h
    · left; omega
    · rcases hnotF q h with h | h
      · left; omega
      · right; omega
  refine .done _ ⟨hpc', ⟨hf', fun q hq ↦ ?_, (hsv'.1 .rbx rfl).trans hrbx,
    (hsv'.1 .rbp rfl).trans hrbp, (hsv'.1 .r12 rfl).trans hr12, (hsv'.1 .r13 rfl).trans hr13,
    (hsv'.1 .r14 rfl).trans hr14, (hsv'.1 .r15 rfl).trans hr15, ?_⟩, ?_⟩
  · -- the changes
    have hq' : ¬ (lsb m0 ≤ q.toNat ∧ q.toNat < lsb m0 + 18816) := fun h ↦ hq (Or.inl (by
      rw [inR (by unfold NativeRustcVm.NoWrap; rw [lsb_eq]; omega), lsb_eq]; exact h))
    rw [hs' q fun h ↦ by
      rcases hR' q h with h | h | h
      · exact hq' ⟨by omega, by omega⟩
      · exact hq (Or.inr (Or.inl h))
      · exact hq (Or.inr (Or.inr h))]
    exact hs q fun h ↦ hq' (by have := hfr q h; omega)
  · -- the public input
    refine keep_off hpub hs' fun j h1 h2 h ↦ ?_
    rw [NativeRustcVm.length_wordsBytes, Vector.length_toList] at h2
    have hq : (off (stackBelow m0 112) j).toNat = lsb m0 + 18704 + j := by
      rw [toNat_off (by omega), hBn]
    rcases hR' _ h with h | h
    · omega
    · have := hnotF _ h; omega
  · -- the verdict
    have hB : NativeRustcVm.BytesAt st.data.dmem bp bytes := by
      rcases hbp with ⟨h0, -⟩ | ⟨h0, rfl⟩
      · rw [List.length_eq_zero_iff.mp h0]; exact NativeRustcVm.BytesAt.nil _ _
      · refine (wireBytes hin).of_sameOutside hs fun i hi h ↦ ?_
        have := hfr _ h
        have gw := g.wire h0
        rw [NativeRustcVm.toNat_add_ofNat (by simp; omega)] at this
        simp only [UInt64.toNat_toBitVec] at this
        omega
    have h := hres bytes rfl hB
    exact h

end

end NativeRustcVmX64.Top.Leanvm
