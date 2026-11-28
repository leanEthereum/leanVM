module

public import NativeRustcVmX64.Wire.ReaderLe
public import NativeRustcVmX64.Transcript.Frame
public import NativeRustcVmX64.Code.Vm.ReaderLe.Names

/-!
# Frames of the functions that read (x86-64)

A function reading through the reader at `r` keeps its frame (`Transcript.Frame`: its pushes and
locals, `F` bytes below the entry's RSP, and the return address) at the top of its `N` bytes of
stack, and writes the reader's cursor and its outputs `W`. `RGeo`: the stack (with the return
address), the reader and its bytes apart, `W` apart from all three. Then: the reader survives a
change of the frame and the outputs (`reader_frame`); a call of `Reader::le` for eight bytes from
the frame (`le_call`), its outcome `ReadRes`.
-/

namespace NativeRustcVmX64.Wire

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmX64.Transcript (Frame Slots apart_callee apart_frame stackOk_callee
  inRange_mono)
open NativeRustcVm.Transcript (off_zero)

@[expose] public section

/-- The outcome of a read of eight bytes at `c`: the tag in RAX, the word in RDX. -/
def ReadRes (r bp : BitVec 64) (B : List UInt8) (c : Nat) (m : MachineData) : Prop :=
  match rdLe B c 8 with
  | some (v, c') => reg m .rax = 1 ∧ reg m .rdx = v.toBitVec ∧ ReaderAt m.dmem r bp B c'
  | none => reg m .rax = 0

/-- The places of a reading function: its `N` bytes of stack and the return address, the reader
at `r` and its `L` bytes at `bp` apart, the outputs `W` apart from the three. -/
structure RGeo (m0 : MachineData) (N : Nat) (r bp : BitVec 64) (L : Nat) (W : BitVec 64 → Prop) :
    Prop where
  st : StackOk m0 N
  rNw : NativeRustcVm.NoWrap r 24
  bpNw : NativeRustcVm.NoWrap bp L
  sr : NativeRustcVm.Apart r 24 (stackBelow m0 N) (N + 8)
  sb : NativeRustcVm.Apart bp L (stackBelow m0 N) (N + 8)
  rb : NativeRustcVm.Apart r 24 bp L
  wS : ∀ q, W q → ¬NativeRustcVm.InRange (stackBelow m0 N) (N + 8) q
  wR : ∀ q, W q → ¬NativeRustcVm.InRange r 24 q
  wB : ∀ q, W q → ¬NativeRustcVm.InRange bp L q

end

public section

variable {m0 : MachineData} {N F : Nat} {r bp : BitVec 64} {L : Nat} {W : BitVec 64 → Prop}

theorem not_inRange_of_apart' {a b q : BitVec 64} {n n' : Nat}
    (hap : NativeRustcVm.Apart a n b n') (hna : NativeRustcVm.NoWrap a n)
    (hnb : NativeRustcVm.NoWrap b n') (ha : NativeRustcVm.InRange a n q)
    (hb : NativeRustcVm.InRange b n' q) : False :=
  hap.not_inRange hna hnb ha hb

/-- The frame is in the stack. -/
theorem inRange_frame (hst : StackOk m0 N) (hF : F ≤ N) {q : BitVec 64}
    (h : NativeRustcVm.InRange (stackBelow m0 F) (F + 8) q) :
    NativeRustcVm.InRange (stackBelow m0 N) (N + 8) q := by
  have hn := hst.1
  have h8 := hst.2.1
  have h1 := NativeRustcVmX64.stackBelow_toNat (m := m0) (n := F) (by omega)
  have h2 := NativeRustcVmX64.stackBelow_toNat (m := m0) (n := N) hn
  rw [NativeRustcVm.inRange_iff (by unfold NativeRustcVm.NoWrap; rw [h1]; omega), h1] at h
  rw [NativeRustcVm.inRange_iff (by unfold NativeRustcVm.NoWrap; rw [h2]; omega), h2]
  omega

/-- The outputs and the cursor miss the frame. -/
theorem RGeo.not_frame (g : RGeo m0 N r bp L W) (hF : F ≤ N) {q : BitVec 64}
    (h : NativeRustcVm.InRange (r + BitVec.ofNat 64 16) 8 q ∨ W q) :
    ¬NativeRustcVm.InRange (stackBelow m0 F) (F + 8) q := fun hq ↦ by
  have hq := inRange_frame g.st hF hq
  have hS := NativeRustcVmX64.noWrap_stackBelow g.st
  rcases h with h | h
  · have hr := g.rNw
    unfold NativeRustcVm.NoWrap at hr
    refine not_inRange_of_apart' g.sr g.rNw hS ?_ hq
    exact NativeRustcVm.InRange.of_sub (o := 16) (m := 8) h g.rNw (by omega)
  · exact g.wS q h hq

/-- **A reader survives** a change of the stack and the outputs, its cursor aside. -/
theorem RGeo.reader_frame (g : RGeo m0 N r bp L W) {d d' : DataMem} {B : List UInt8} {c : Nat}
    (hL : B.length = L) (hR : ReaderAt d r bp B c)
    (hs : NativeRustcVm.SameOutside d d' fun q ↦
      NativeRustcVm.InRange (stackBelow m0 N) (N + 8) q ∨ W q) :
    ReaderAt d' r bp B c := by
  subst hL
  have hS := NativeRustcVmX64.noWrap_stackBelow g.st
  refine hR.frame hs (fun i hi hq ↦ ?_) (fun i hi hq ↦ ?_)
  · have hin : NativeRustcVm.InRange r 24 (r + BitVec.ofNat 64 i) :=
      NativeRustcVm.inRange_add hi (by have := g.rNw; unfold NativeRustcVm.NoWrap at this; omega)
    rcases hq with h | h
    · exact not_inRange_of_apart' g.sr g.rNw hS hin h
    · exact g.wR _ h hin
  · have hin : NativeRustcVm.InRange bp B.length (bp + BitVec.ofNat 64 i) :=
      NativeRustcVm.inRange_add hi (by have := g.bpNw; unfold NativeRustcVm.NoWrap at this; omega)
    rcases hq with h | h
    · exact not_inRange_of_apart' g.sb g.bpNw hS hin h
    · exact g.wB _ h hin

theorem readRes_cases {B : List UInt8} {c : Nat} {m : MachineData} (h : ReadRes r bp B c m) :
    (reg m .rax = 0 ∧ ¬c + 8 ≤ B.length) ∨
      (reg m .rax = 1 ∧ reg m .rdx = (leAt B c 8).toBitVec ∧ ReaderAt m.dmem r bp B (c + 8) ∧
        c + 8 ≤ B.length) := by
  unfold ReadRes rdLe at h
  by_cases hc : c + 8 ≤ B.length
  · simp only [hc, ↓reduceIte] at h
    exact .inr ⟨h.1, h.2.1, h.2.2, hc⟩
  · simp only [hc, ↓reduceIte] at h
    exact .inl ⟨h, hc⟩

variable [Host]

/-- **A call of `Reader::le` for eight bytes** from a reading function's frame, RSP at its base:
back at the return address in the frame (RSP at offset `8`), the callee-saved registers kept, the
cursor word changed at most, the read's outcome. -/
theorem le_call (hle : Spec (Labels.label NativeRustcVmX64.Vm.ReaderLe.entryLabel) ReaderLePre ReaderLePost)
    {slots : Slots} {B : List UInt8} {c : Nat} (g : RGeo m0 N r bp B.length W) (hFN : F ≤ N)
    (hsl : ∀ p ∈ slots, p.1 + 8 ≤ F) {st : MachineState} {next : Int64}
    {R : MachineState → Prop} (hfr : Frame m0 F slots 0 st.data)
    (hR : ReaderAt st.data.dmem r bp B c) (hrdi : reg st.data .rdi = r)
    (hrsi : (reg st.data .rsi).toNat = 8)
    (hpc : st.pc = Labels.label NativeRustcVmX64.Vm.ReaderLe.entryLabel ∧ retOf st.data = next)
    (cont : ∀ m2, Frame m0 F slots 8 m2 →
      (∀ x, calleeSaved x = true → reg m2 x = reg st.data x) →
      NativeRustcVm.SameOutside st.data.dmem m2.dmem
        (NativeRustcVm.InRange (r + BitVec.ofNat 64 16) 8) →
      ReadRes r bp B c m2 → Eventually (step1 Host.exe) R ⟨m2, next⟩) :
    Eventually (step1 Host.exe) R st := by
  have hN := g.st.1
  have hsp : rspOf st.data = stackBelow m0 F := by rw [hfr.sp, off_zero]
  have hP : ReaderLePre st.data := by
    refine ⟨stackOk_callee g.st hfr.kept hsp (by unfold readerLeStack; omega), .inr hrsi, bp, B, c,
      by rw [hrdi]; exact hR, ?_⟩
    rw [hrdi]
    have := apart_callee g.sr hsp hN (n' := readerLeStack) (by unfold readerLeStack; omega)
    exact List.pairwise_pair.mpr (by
      unfold NativeRustcVm.Apart at this ⊢; dsimp only [stackR]; omega)
  refine Eventually.bind (Spec.apply hle hpc.1 hP) fun st' ⟨hpc', hrsp', hres, hs, hsv⟩ ↦ ?_
  rw [hpc.2] at hpc'
  rw [hrdi] at hres hs
  have hfr' : Frame m0 F slots 8 st'.data :=
    Frame.call hfr hsv hrsp' hs (fun q hq ↦ g.not_frame hFN (.inl hq))
      (NativeRustcVmX64.Transcript.frame_noWrap g.st hFN) hsl
  obtain ⟨m2, pc2⟩ := st'
  simp only at hpc'
  subst hpc'
  refine cont m2 hfr' (fun x hx ↦ hsv.1 x hx) hs ?_
  have := hres bp B c hR
  rw [hrsi] at this
  exact this

end

end NativeRustcVmX64.Wire
