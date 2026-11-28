module

public import NativeRustcVmX64.Wire.Frame
public import NativeRustcVmX64.Spec.Wire
public import NativeRustcVm.Wire.ReaderFacts
public import NativeRustcVm.Transcript.Update
import NativeVm.Wire.Read
public import NativeRustcVmX64.Code.Vm.ReaderLe.Names

/-!
# Memory kept, by numbers (x86-64)

The proofs of `phase_m` and `decode` describe what a step changes by the numbers of its bytes'
addresses (`q.toNat` in an interval), so that one `omega` decides that a word, a reader, a part of
the decoded area survive it (`bytesAt_keep`, `wordAt_keep`, `reader_keep`, `agree_keep`); the
bytes of a frame and of the regions as numbers (`frame_toNat`, `iv_of_inRange`). A call of
`Reader::le` for four bytes from a frame (`le4_call`), its outcome in the model's `rdU32`
(`Read4`).
-/

namespace NativeRustcVmX64.Wire.PhaseM

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmX64.Transcript (Frame Slots stackOk_callee Frame.call_slots)
open NativeRustcVm.Transcript (off off_zero off_off toNat_off)

@[expose] public section

/-- The outcome of a read of four bytes at `c`: the tag in RAX, the value in RDX. -/
def Read4 (r bp : BitVec 64) (B : List UInt8) (c : Nat) (m : MachineData) : Prop :=
  match rdU32 B c with
  | some (v, c') => reg m .rax = 1 ∧ (reg m .rdx).toNat = v ∧ ReaderAt m.dmem r bp B c'
  | none => reg m .rax = 0

end

public section

/-- Bytes whose addresses a change misses are kept. -/
theorem bytesAt_keep {d d' : Mem 64} {a : BitVec 64} {bs : List UInt8} {R : BitVec 64 → Prop}
    (h : NativeRustcVm.BytesAt d a bs) (hs : NativeRustcVm.SameOutside d d' R)
    (hnw : a.toNat + bs.length ≤ 2 ^ 64)
    (hR : ∀ q, R q → q.toNat < a.toNat ∨ a.toNat + bs.length ≤ q.toNat) :
    NativeRustcVm.BytesAt d' a bs :=
  h.of_sameOutside hs fun i hi hq ↦ by
    have := hR _ hq
    rw [NativeRustcVm.toNat_add_ofNat (by omega)] at this
    omega

theorem wordAt_keep {d d' : Mem 64} {a : BitVec 64} {w : UInt64} {R : BitVec 64 → Prop}
    (h : NativeRustcVm.WordAt d a w) (hs : NativeRustcVm.SameOutside d d' R)
    (hnw : a.toNat + 8 ≤ 2 ^ 64) (hR : ∀ q, R q → q.toNat < a.toNat ∨ a.toNat + 8 ≤ q.toNat) :
    NativeRustcVm.WordAt d' a w :=
  bytesAt_keep (bs := NativeRustcVm.wordBytes w) h hs (by rw [NativeRustcVm.length_wordBytes]; exact hnw)
    (by rw [NativeRustcVm.length_wordBytes]; exact hR)

theorem wordsAt_keep {d d' : Mem 64} {a : BitVec 64} {ws : List UInt64} {R : BitVec 64 → Prop}
    (h : NativeRustcVm.WordsAt d a ws) (hs : NativeRustcVm.SameOutside d d' R)
    (hnw : a.toNat + 8 * ws.length ≤ 2 ^ 64)
    (hR : ∀ q, R q → q.toNat < a.toNat ∨ a.toNat + 8 * ws.length ≤ q.toNat) :
    NativeRustcVm.WordsAt d' a ws :=
  bytesAt_keep (bs := ws.flatMap NativeRustcVm.wordBytes) h hs
    (by rw [NativeRustcVm.length_wordsBytes]; exact hnw)
    (by rw [NativeRustcVm.length_wordsBytes]; exact hR)

theorem ewAt_keep {d d' : Mem 64} {a : BitVec 64} {x : NativeVm.Model.EW} {R : BitVec 64 → Prop}
    (h : NativeRustcVm.EWAt d a x) (hs : NativeRustcVm.SameOutside d d' R)
    (hnw : a.toNat + 16 ≤ 2 ^ 64) (hR : ∀ q, R q → q.toNat < a.toNat ∨ a.toNat + 16 ≤ q.toNat) :
    NativeRustcVm.EWAt d' a x :=
  bytesAt_keep (bs := NativeRustcVm.ewBytes x) h hs
    (by rw [NativeRustcVm.length_ewBytes]; exact hnw) (by rw [NativeRustcVm.length_ewBytes]; exact hR)

/-- **A reader kept** by a change missing it and its bytes. -/
theorem reader_keep {d d' : Mem 64} {r bp : BitVec 64} {B : List UInt8} {c : Nat}
    {R : BitVec 64 → Prop} (h : ReaderAt d r bp B c) (hs : NativeRustcVm.SameOutside d d' R)
    (hr : ∀ q, R q → q.toNat < r.toNat ∨ r.toNat + 24 ≤ q.toNat)
    (hb : ∀ q, R q → q.toNat < bp.toNat ∨ bp.toNat + B.length ≤ q.toNat) :
    ReaderAt d' r bp B c := by
  have hrn : r.toNat + 24 ≤ 2 ^ 64 := h.ok.2
  have hbn : bp.toNat + B.length ≤ 2 ^ 64 := h.noWrap
  refine h.frame hs (fun i hi hq ↦ ?_) (fun i hi hq ↦ ?_)
  · have := hr _ hq
    rw [NativeRustcVm.toNat_add_ofNat (by omega)] at this
    omega
  · have := hb _ hq
    rw [NativeRustcVm.toNat_add_ofNat (by omega)] at this
    omega

/-- An area agrees after a change missing it. -/
theorem agree_keep {d d' : Mem 64} {a : BitVec 64} {n : Nat} {R : BitVec 64 → Prop}
    (hs : NativeRustcVm.SameOutside d d' R) (hnw : a.toNat + n ≤ 2 ^ 64)
    (hR : ∀ q, R q → q.toNat < a.toNat ∨ a.toNat + n ≤ q.toNat) :
    NativeRustcVm.Transcript.Agree d d' a n (fun _ ↦ False) := by
  intro j hj _
  refine hs _ fun hq ↦ ?_
  have := hR _ hq
  rw [toNat_off (by omega)] at this
  omega

/-- A byte in a range that does not wrap, as a number. -/
theorem iv_of_inRange {a q : BitVec 64} {n : Nat} (hnw : a.toNat + n ≤ 2 ^ 64)
    (h : NativeRustcVm.InRange a n q) : a.toNat ≤ q.toNat ∧ q.toNat < a.toNat + n :=
  (NativeRustcVm.inRange_iff hnw).mp h

/-- Byte `j` of a frame of `F` bytes and the return address, as a number. -/
theorem frame_toNat {m0 : MachineData} {F j : Nat} (hF : F ≤ (rspOf m0).toNat)
    (h8 : (rspOf m0).toNat + 8 ≤ 2 ^ 64) (hj : j < F + 8) :
    (off (stackBelow m0 F) j).toNat = (rspOf m0).toNat - F + j := by
  rw [toNat_off (by rw [stackBelow_toNat hF]; omega), stackBelow_toNat hF]

theorem stackBelow_toNat' {m : MachineData} {n : Nat} (h : n ≤ (rspOf m).toNat) :
    (stackBelow m n).toNat = (rspOf m).toNat - n :=
  stackBelow_toNat h

/-- The callee's stack below a frame, as numbers. -/
theorem callee_toNat {m0 d : MachineData} {F n : Nat} (hsp : rspOf d = stackBelow m0 F)
    (hF : F + n ≤ (rspOf m0).toNat) :
    (stackBelow d n).toNat = (rspOf m0).toNat - F - n ∧ (rspOf d).toNat = (rspOf m0).toNat - F := by
  have h1 : (rspOf d).toNat = (rspOf m0).toNat - F := by
    rw [hsp, stackBelow_toNat (by omega)]
  exact ⟨by rw [stackBelow_toNat (by omega), h1], h1⟩

/-- A word's value, as a number below `2 ^ 64`. -/
theorem toNat_toUInt64 {n : Nat} (h : n < 2 ^ 64) : n.toUInt64.toNat = n :=
  NativeRustcVm.Wire.toNat_toUInt64_of_lt h

/-- A 4-byte read of `Reader::le` is `rdU32`'s. -/
theorem rdLe_four (B : List UInt8) (c : Nat) :
    rdLe B c 4 = (rdU32 B c).map fun p ↦ (p.1.toUInt64, p.2) := by
  unfold rdLe rdU32
  split <;> rfl

theorem rdU32_lt {B : List UInt8} {c v c' : Nat} (h : rdU32 B c = some (v, c')) : v < 2 ^ 32 := by
  unfold rdU32 at h
  split at h
  · cases h
    have := leNat_lt B c 4
    simpa using this
  · cases h

theorem rdU32_c {B : List UInt8} {c v c' : Nat} (h : rdU32 B c = some (v, c')) : c' = c + 4 := by
  unfold rdU32 at h
  split at h
  · cases h; rfl
  · cases h

theorem read4_cases {r bp : BitVec 64} {B : List UInt8} {c : Nat} {m : MachineData}
    (h : Read4 r bp B c m) :
    (rdU32 B c = none ∧ reg m .rax = 0) ∨
      ∃ v, rdU32 B c = some (v, c + 4) ∧ reg m .rax = 1 ∧ (reg m .rdx).toNat = v ∧
        v < 2 ^ 32 ∧ ReaderAt m.dmem r bp B (c + 4) := by
  unfold Read4 at h
  rcases h1 : rdU32 B c with _ | ⟨v, c'⟩
  · rw [h1] at h; exact .inl ⟨rfl, h⟩
  · rw [h1] at h
    have := rdU32_c h1
    subst this
    exact .inr ⟨v, rfl, h.1, h.2.1, rdU32_lt h1, h.2.2⟩
variable [Host]


/-- **A call of `Reader::le` for four bytes** from a frame of `F` bytes (its slots from `lo` on),
with the reader at `r` apart from the call's return address and its cursor apart from the slots
and the return address. -/
theorem le4_call (hle : Spec (Labels.label NativeRustcVmX64.Vm.ReaderLe.entryLabel) ReaderLePre ReaderLePost)
    {m0 : MachineData} {F N lo : Nat} {slots : Slots} (hst : StackOk m0 N) (hFN : F ≤ N)
    (hlo : lo ≤ F) (hsl : ∀ p ∈ slots, lo ≤ p.1 ∧ p.1 + 8 ≤ F) {st : MachineState} {next : Int64}
    {R : MachineState → Prop} (hf : Frame m0 F slots 0 st.data) {r bp : BitVec 64}
    {B : List UInt8} {c : Nat} (hR : ReaderAt st.data.dmem r bp B c) (hrdi : reg st.data .rdi = r)
    (hrsi : (reg st.data .rsi).toNat = 4)
    (hap : (rspOf m0).toNat - F + 8 ≤ r.toNat ∨ r.toNat + 24 ≤ (rspOf m0).toNat - F)
    (hcur : r.toNat + 24 ≤ (rspOf m0).toNat - F + lo ∨ (rspOf m0).toNat + 8 ≤ r.toNat + 16)
    (hpc : st.pc = Labels.label NativeRustcVmX64.Vm.ReaderLe.entryLabel ∧ retOf st.data = next)
    (cont : ∀ m2, Frame m0 F slots 8 m2 →
      (∀ x, calleeSaved x = true → reg m2 x = reg st.data x) →
      NativeRustcVm.SameOutside st.data.dmem m2.dmem (NativeRustcVm.InRange (off r 16) 8) →
      Read4 r bp B c m2 → Eventually (step1 Host.exe) R ⟨m2, next⟩) :
    Eventually (step1 Host.exe) R st := by
  have hN := hst.1
  have h8 := hst.2.1
  have hsp : rspOf st.data = stackBelow m0 F := by rw [hf.sp, off_zero]
  have hrn : r.toNat + 24 ≤ 2 ^ 64 := hR.ok.2
  obtain ⟨hcs, hcsp⟩ := callee_toNat (n := 0) hsp (by omega)
  have hP : ReaderLePre st.data := by
    refine ⟨stackOk_callee hst hf.kept hsp (by unfold readerLeStack; omega), .inl hrsi, bp, B, c,
      by rw [hrdi]; exact hR, ?_⟩
    rw [hrdi]
    refine List.pairwise_pair.mpr ?_
    show NativeRustcVm.Apart (stackBelow st.data readerLeStack) (readerLeStack + 8) r 24
    unfold NativeRustcVm.Apart readerLeStack
    rw [hcs]
    omega
  refine Eventually.bind (Spec.apply hle hpc.1 hP) fun st' ⟨hpc', hrsp', hres, hs, hsv⟩ ↦ ?_
  rw [hpc.2] at hpc'
  rw [hrdi] at hres hs
  have hc16 : (off r 16).toNat = r.toNat + 16 := toNat_off (by omega)
  have hnot : ∀ j, lo ≤ j → j < F + 8 →
      ¬ NativeRustcVm.InRange (off r 16) 8 (off (stackBelow m0 F) j) := fun j hj hj' hq ↦ by
    have := iv_of_inRange (by rw [hc16]; omega) hq
    rw [frame_toNat (by omega) h8 hj', hc16] at this
    omega
  have hf' : Frame m0 F slots 8 st'.data :=
    Frame.call_slots hf hsv hrsp' hs
      (fun p hp i hi ↦ hnot _ (by have := hsl p hp; omega) (by have := hsl p hp; omega))
      (fun j hj ↦ hnot _ (by omega) (by omega))
  obtain ⟨m2, pc2⟩ := st'
  simp only at hpc'
  subst hpc'
  refine cont m2 hf' (fun x hx ↦ hsv.1 x hx) hs ?_
  have := hres bp B c hR
  rw [hrsi, rdLe_four] at this
  unfold Read4
  rcases h : rdU32 B c with _ | ⟨v, c'⟩
  · rw [h] at this; exact this
  · rw [h] at this
    obtain ⟨h0, h1, h2⟩ := this
    refine ⟨h0, ?_, h2⟩
    rw [h1]
    exact toNat_toUInt64 (by have := rdU32_lt h; omega)

end

end NativeRustcVmX64.Wire.PhaseM
