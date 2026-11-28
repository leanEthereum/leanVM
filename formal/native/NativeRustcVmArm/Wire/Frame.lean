module

public import NativeRustcVmArm.Code.Vm.ReaderLe.Names
public import NativeRustcVmArm.Wire.ReaderLe
public import NativeRustcVmArm.Ring.Frame

/-!
# Frames of the functions that read

A function reading through the reader at `r` keeps its frame in the `F` bytes below SP, uses `N`
bytes of stack (`Ring.Fr`), and writes the reader's cursor and its outputs `W` (`outs`). `RGeo`:
the stack, the reader and its bytes apart, `W` apart from all three. Then: the reader survives what
the frame allows (`reader_frame`), its cursor changes aside; a call of `Reader::le` from the frame
(`le_call`), its outcome `ReadRes`.
-/

namespace NativeRustcVmArm.Wire

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmArm.Ring (Fr base)

@[expose] public section

/-- What a reading function writes besides its frame: the reader's cursor and the outputs `W`. -/
def outs (r : BitVec 64) (W : BitVec 64 → Prop) (q : BitVec 64) : Prop :=
  InRange (r + BitVec.ofNat 64 16) 8 q ∨ W q

/-- The outcome of a read of eight bytes at `c`. -/
def ReadRes (r bp : BitVec 64) (B : List UInt8) (c : Nat) (m : MachineData) : Prop :=
  match rdLe B c 8 with
  | some (v, c') => m.regs.X0 = 1 ∧ m.regs.X1 = v ∧ ReaderAt m.dmem r bp B c'
  | none => m.regs.X0 = 0

/-- The places of a reading function: the `N` bytes of stack, the reader at `r` and its `L` bytes
at `bp` apart, the outputs `W` apart from the three. -/
structure RGeo (m0 : MachineData) (N : Nat) (r bp : BitVec 64) (L : Nat) (W : BitVec 64 → Prop) :
    Prop where
  st : StackOk m0 N
  rNw : NoWrap r 24
  bpNw : NoWrap bp L
  sr : Apart (base m0 N) N r 24
  sb : Apart (base m0 N) N bp L
  rb : Apart r 24 bp L
  wS : ∀ q, W q → ¬InRange (base m0 N) N q
  wR : ∀ q, W q → ¬InRange r 24 q
  wB : ∀ q, W q → ¬InRange bp L q

end

public section

section
variable {m0 : MachineData} {N F : Nat} {r bp : BitVec 64} {L : Nat} {W : BitVec 64 → Prop}

theorem inRange_base (g : RGeo m0 N r bp L W) (hF : F ≤ N) {q : BitVec 64}
    (h : InRange (base m0 F) F q) : InRange (base m0 N) N q := by
  have hN := g.st.2.1
  rw [Sym.inRange_iff (Ring.base_noWrap (by omega)), Ring.base_toNat (by omega)] at h
  rw [Sym.inRange_iff (Ring.base_noWrap hN), Ring.base_toNat hN]
  omega

/-- The outputs miss the frame. -/
theorem RGeo.not_frame (g : RGeo m0 N r bp L W) (hF : F ≤ N) {q : BitVec 64} (h : outs r W q) :
    ¬InRange (base m0 F) F q := fun hq ↦ by
  have hq := inRange_base g hF hq
  have hb := Ring.base_noWrap (m0 := m0) (F := N) g.st.2.1
  rcases h with h | h
  · exact NativeRustcVm.Apart.not_inRange g.sr.symm g.rNw hb
      (NativeRustcVm.InRange.of_sub (o := 16) (m := 8) h g.rNw (by omega)) hq
  · exact g.wS q h hq

/-- **A reader survives** a change of the frame and the outputs, its cursor aside. -/
theorem RGeo.reader_frame (g : RGeo m0 N r bp L W) {d d' : DataMem} {B : List UInt8} {c : Nat}
    (hL : B.length = L) (hR : ReaderAt d r bp B c)
    (hs : SameOutside d d' fun q ↦ InRange (base m0 N) N q ∨ W q) : ReaderAt d' r bp B c := by
  subst hL
  have hb := Ring.base_noWrap (m0 := m0) (F := N) g.st.2.1
  refine hR.frame hs (fun i hi hq ↦ ?_) (fun i hi hq ↦ ?_)
  · have hin : InRange r 24 (r + BitVec.ofNat 64 i) :=
      NativeRustcVm.inRange_add hi (by have := g.rNw; unfold NoWrap at this; omega)
    rcases hq with h | h
    · exact NativeRustcVm.Apart.not_inRange g.sr.symm g.rNw hb hin h
    · exact g.wR _ h hin
  · have hin : InRange bp B.length (bp + BitVec.ofNat 64 i) :=
      NativeRustcVm.inRange_add hi (by have := g.bpNw; unfold NoWrap at this; omega)
    rcases hq with h | h
    · exact NativeRustcVm.Apart.not_inRange g.sb.symm g.bpNw hb hin h
    · exact g.wB _ h hin

/-- The places of a reading function with one output range. -/
theorem RGeo.of_apart {m0 : MachineData} {N : Nat} {r bp out : BitVec 64} {L no : Nat}
    (hst : StackOk m0 N) (hrNw : NoWrap r 24) (hbpNw : NoWrap bp L) (hoNw : NoWrap out no)
    (sr : Apart (base m0 N) N r 24) (sb : Apart (base m0 N) N bp L) (so : Apart (base m0 N) N out no)
    (rb : Apart r 24 bp L) (ro : Apart r 24 out no) (bo : Apart bp L out no) :
    RGeo m0 N r bp L (InRange out no) :=
  have hb := Ring.base_noWrap (m0 := m0) (F := N) hst.2.1
  ⟨hst, hrNw, hbpNw, sr, sb, rb,
    fun _ h ↦ NativeRustcVm.Apart.not_inRange so.symm hoNw hb h,
    fun _ h ↦ NativeRustcVm.Apart.not_inRange ro.symm hoNw hrNw h,
    fun _ h ↦ NativeRustcVm.Apart.not_inRange bo.symm hoNw hbpNw h⟩

theorem readRes_cases {B : List UInt8} {c : Nat} {m : MachineData} (h : ReadRes r bp B c m) :
    (m.regs.X0 = 0 ∧ ¬c + 8 ≤ B.length) ∨
      (m.regs.X0 = 1 ∧ m.regs.X1 = leAt B c 8 ∧ ReaderAt m.dmem r bp B (c + 8) ∧ c + 8 ≤ B.length) := by
  unfold ReadRes rdLe at h
  by_cases hc : c + 8 ≤ B.length
  · simp only [hc, ↓reduceIte] at h
    exact .inr ⟨h.1, h.2.1, h.2.2, hc⟩
  · simp only [hc, ↓reduceIte] at h
    exact .inl ⟨h, hc⟩

end

variable [Host]

/-- **A call of `Reader::le` for eight bytes** from a state of a reading function's frame. -/
theorem le_call (hle : Spec (Labels.label NativeRustcVmArm.Vm.ReaderLe.entryLabel) ReaderLePre ReaderLePost)
    {m0 : MachineData} {F N : Nat} {slots : List (Nat × XReg)} {keep : List XReg}
    {r bp : BitVec 64} {B : List UInt8} {W : BitVec 64 → Prop} {c : Nat}
    (g : RGeo m0 N r bp B.length W) (hF : F % 16 = 0) (hFN : F ≤ N)
    (hkeep : ∀ x ∈ keep, calleeSaved x = true) (hsl : ∀ p ∈ slots, p.1 + 8 ≤ F)
    {st : MachineState} {next : Int64} {R : MachineState → Prop}
    (hfr : Fr m0 F N slots keep (outs r W) st.data) (hR : ReaderAt st.data.dmem r bp B c)
    (hx0 : st.data.regs.X0.toBitVec = r) (hx1 : st.data.regs.X1.toNat = 8)
    (hpc : st.pc = Labels.label NativeRustcVmArm.Vm.ReaderLe.entryLabel ∧ retOf st.data = next)
    (cont : ∀ m2, Fr m0 F N slots keep (outs r W) m2 →
      (∀ x, calleeSaved x = true → m2.regs.getXReg x = st.data.regs.getXReg x) →
      SameOutside st.data.dmem m2.dmem (InRange (r + BitVec.ofNat 64 16) 8) →
      ReadRes r bp B c m2 → Eventually (step1 Host.exe) R ⟨m2, next⟩) :
    Eventually (step1 Host.exe) R st := by
  have hN := g.st.2.1
  have hP : ReaderLePre st.data :=
    ⟨hfr.stackOk g.st hF (by unfold readerLeStack; omega), .inr hx1, bp, B, c, by rw [hx0]; exact hR⟩
  refine Fr.leaf (N' := readerLeStack) hfr hN (by unfold readerLeStack; omega) hkeep hsl
    (fun q hq ↦ g.not_frame hFN hq)
    (Spec.carry hle fun m ↦ m.regs.X0.toBitVec = r)
    (fun m m' ⟨⟨_, hs, hsv⟩, h0⟩ ↦ ⟨?_, hsv⟩) hpc ⟨hP, hx0⟩ ?_
  · exact NativeRustcVm.SameOutside.mono hs fun q hq ↦ .inr (.inl (by rw [← h0]; exact hq))
  · intro m2 hfr2 ⟨hq, h0⟩ hcs
    refine cont m2 hfr2 hcs (by rw [← h0]; exact hq.2.1) ?_
    have := hq.1 bp B c (by rw [hx0]; exact hR)
    rw [hx1, hx0] at this
    exact this

end

end NativeRustcVmArm.Wire
