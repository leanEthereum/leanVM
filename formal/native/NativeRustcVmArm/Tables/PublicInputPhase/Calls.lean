module

public import NativeRustcVmArm.Code.Vm.MultilinearEvalByOfMultilinearEval.Names
public import NativeRustcVmArm.Code.Vm.PushClaim.Names
public import NativeRustcVmArm.Tables.PublicInputPhase.Facts
public import NativeRustcVmArm.Tables.Common

/-!
# `public_input_phase`: its calls and its point

The model's run (`run_eq`): one challenge, the two claims at the point `pt` (the challenge, then
zeros). `multilinear_eval_by` on the two elements at offset `496` of the frame and the challenge at
`528` (`mle_call`); `push_claim` with the point at the frame's base (`push_call`); the point's
words in the frame (`ptWords`) are its elements (`ewsAt_pt`).
-/

namespace NativeRustcVmArm.Tables.PublicInputPhase

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Ring NativeVm.Model
open NativeRustcVm.Layout (claimsBytes ClaimsWAt claimCap pointCap)
open LeanVM.Protocol.Verifier (memory0 memory1)

@[expose] public section

/-- The point's words: the challenge, then `60` zeros. -/
def ptWords (ch : EW) : List (Nat × UInt64) :=
  (0, ch.c0) :: (8, ch.c1) :: (List.range 60).map fun j ↦ (16 + 8 * j, 0)

/-- The point's `62` words, zero. -/
def zeroWords : List (Nat × UInt64) := (List.range 62).map fun j ↦ (8 * j, 0)

/-- The point: the challenge, then `n - 1` zeros. -/
def pt (ch : EW) (n : Nat) : Array EW := #[ch] ++ Array.replicate (n - 1) 0

end

public section

/-- **The model's run**: the challenge, the two claims at the point `pt`. -/
theorem run_eq (L : LayoutW) (pub : Vector UInt64 4) (s : TState) :
    (publicInputPhase L pub).run s = some (#[
      ⟨memory0, pt s.sponge.squeeze.1 (L.placement memory0).variableCount,
        multilinearEval #[EW.ofK pub[0], EW.ofK pub[2]] #[s.sponge.squeeze.1]⟩,
      ⟨memory1, pt s.sponge.squeeze.1 (L.placement memory0).variableCount,
        multilinearEval #[EW.ofK pub[1], EW.ofK pub[3]] #[s.sponge.squeeze.1]⟩],
      { s with sponge := s.sponge.squeeze.2 }) := by
  simp [publicInputPhase, sampleChallenge, pt]

theorem size_pt (ch : EW) (n : Nat) : (pt ch n).size = 1 + (n - 1) := by
  simp [pt]

/-- **The point's words** are its elements. -/
theorem ewsAt_pt {d : DataMem} {b : BitVec 64} {ch : EW} (h : Bus.FrameWords d b (ptWords ch))
    {n : Nat} (hn : n ≤ 31) : NativeRustcVm.EWsAt d b (pt ch n).toList := by
  refine Bus.ewsAt_of_words _ fun i hi ↦ ?_
  have hl : (pt ch n).toList.length = 1 + (n - 1) := by simp [pt]; omega
  rw [hl] at hi
  rcases i with _ | i
  · have hx : (pt ch n).toList[0] = ch := by simp [pt]
    rw [hx]
    exact ⟨h (0, ch.c0) (by simp [ptWords]), h (8, ch.c1) (by simp [ptWords])⟩
  · have hx : (pt ch n).toList[i + 1] = 0 := by simp [pt]
    rw [hx]
    refine ⟨?_, ?_⟩
    · have := h (16 + 8 * (2 * i), 0) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_map.mpr ⟨2 * i, List.mem_range.mpr (by omega), rfl⟩)))
      rwa [show 16 + 8 * (2 * i) = 16 * (i + 1) by omega] at this
    · have := h (16 + 8 * (2 * i + 1), 0) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_map.mpr ⟨2 * i + 1, List.mem_range.mpr (by omega), rfl⟩)))
      rwa [show 16 + 8 * (2 * i + 1) = 16 * (i + 1) + 8 by omega] at this

/-- The point's elements in the frame: the slice `push_claim` reads. -/
theorem ewsOf_pt {d : DataMem} {b : BitVec 64} {ch : EW} (h : Bus.FrameWords d b (ptWords ch))
    {n : Nat} (h1 : 1 ≤ n) (hn : n ≤ 31) : (NativeRustcVm.ewsOf d b n).toArray = pt ch n := by
  have e := NativeRustcVm.ewsOf_of_ewsAt (ewsAt_pt h hn)
  have hl : (pt ch n).toList.length = n := by simp [pt]; omega
  rw [hl] at e
  rw [e]

/-- Each of the point's words is at a multiple of `8` below `496`. -/
theorem ptWords_off (ch : EW) : ∀ p ∈ ptWords ch, ∃ j < 62, p.1 = 8 * j := by
  intro p hp
  simp only [ptWords, List.mem_cons, List.mem_map, List.mem_range] at hp
  rcases hp with rfl | rfl | ⟨j, hj, rfl⟩
  · exact ⟨0, by omega, rfl⟩
  · exact ⟨1, by omega, rfl⟩
  · exact ⟨j + 2, by omega, by simp only; omega⟩

/-- Two elements from their four words. -/
theorem ewsAt_two {d : DataMem} {b : BitVec 64} {o : Nat} {x0 x1 y0 y1 : UInt64}
    (h0 : NativeRustcVm.WordAt d (b + BitVec.ofNat 64 o) x0)
    (h1 : NativeRustcVm.WordAt d (b + BitVec.ofNat 64 (o + 8)) x1)
    (h2 : NativeRustcVm.WordAt d (b + BitVec.ofNat 64 (o + 16)) y0)
    (h3 : NativeRustcVm.WordAt d (b + BitVec.ofNat 64 (o + 24)) y1) :
    NativeRustcVm.EWsAt d (b + BitVec.ofNat 64 o) [⟨x0, x1⟩, ⟨y0, y1⟩] := by
  refine Bus.ewsAt_of_words _ fun i hi ↦ ?_
  rw [NativeRustcVm.addr_add_add, NativeRustcVm.addr_add_add]
  match i, hi with
  | 0, _ => exact ⟨h0, h1⟩
  | 1, _ => exact ⟨h2, h3⟩

/-- One element from its two words. -/
theorem ewsAt_one {d : DataMem} {b : BitVec 64} {o : Nat} {x0 x1 : UInt64}
    (h0 : NativeRustcVm.WordAt d (b + BitVec.ofNat 64 o) x0)
    (h1 : NativeRustcVm.WordAt d (b + BitVec.ofNat 64 (o + 8)) x1) :
    NativeRustcVm.EWsAt d (b + BitVec.ofNat 64 o) [⟨x0, x1⟩] := by
  refine Bus.ewsAt_of_words _ fun i hi ↦ ?_
  rw [NativeRustcVm.addr_add_add, NativeRustcVm.addr_add_add]
  match i, hi with
  | 0, _ => exact ⟨h0, h1⟩

theorem le_squeeze : 608 + squeezeStack ≤ publicInputPhaseStack := by decide
theorem le_mle : 608 + mleStack ≤ publicInputPhaseStack := by decide
theorem le_push : 608 + pushClaimStack ≤ publicInputPhaseStack := by decide
theorem le_place : 608 + layoutWPlacementStack ≤ publicInputPhaseStack := by decide
theorem le_N : 608 ≤ publicInputPhaseStack := by decide

section
variable [Host]

/-- **`multilinear_eval_by`** on the two elements at offset `496` of the frame, the point the one
at `528`. -/
theorem mle_call
    (hmle : Spec (Labels.label NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.entryLabel) MleOfMultilinearEvalPre
      MleOfMultilinearEvalPost)
    {m1 : MachineData} (hS1 : StackOk m1 publicInputPhaseStack) {st : MachineState}
    {next : Int64} {R : MachineState → Prop}
    (hfr : Fr m1 608 publicInputPhaseStack slots keep (fun _ ↦ False) st.data)
    (hpc : st.pc = Labels.label NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.entryLabel ∧ retOf st.data = next)
    (h0 : st.data.regs.X0.toBitVec = BitVec.ofNat 64 2)
    (h2 : st.data.regs.X2.toBitVec = BitVec.ofNat 64 2)
    (h4 : st.data.regs.X4.toBitVec = BitVec.ofNat 64 1)
    (h1 : st.data.regs.X1.toBitVec = base m1 608 + BitVec.ofNat 64 496)
    (h3 : st.data.regs.X3.toBitVec = base m1 608 + BitVec.ofNat 64 528) {x y ch : EW}
    (hxy : NativeRustcVm.EWsAt st.data.dmem (base m1 608 + BitVec.ofNat 64 496) [x, y])
    (hch : NativeRustcVm.EWsAt st.data.dmem (base m1 608 + BitVec.ofNat 64 528) [ch])
    (cont : ∀ m2, Fr m1 608 publicInputPhaseStack slots keep (fun _ ↦ False) m2 →
      ewRet m2 = multilinearEval #[x, y] #[ch] →
      (∀ r, calleeSaved r = true → m2.regs.getXReg r = st.data.regs.getXReg r) →
      SameOutside st.data.dmem m2.dmem
        (fun q ↦ InRange (stackBelow st.data mleStack) mleStack q ∨ False) →
      Eventually (step1 Host.exe) R ⟨m2, next⟩) :
    Eventually (step1 Host.exe) R st := by
  have hle := le_mle
  have hN := hS1.2.1
  have hn2 : st.data.regs.X2.toNat = 2 := by
    show st.data.regs.X2.toBitVec.toNat = 2; rw [h2]; rfl
  have hn4 : st.data.regs.X4.toNat = 1 := by
    show st.data.regs.X4.toBitVec.toNat = 1; rw [h4]; rfl
  have hl1 := Bus.local_ok (o := 496) (n := 32) hS1 hle (by omega) hfr.kept hfr.sp
  have hl3 := Bus.local_ok (o := 528) (n := 16) hS1 hle (by omega) hfr.kept hfr.sp
  have hpre : MleOfMultilinearEvalPre st.data := by
    refine ⟨hfr.stackOk hS1 rfl hle, ?_, by rw [hn4]; omega, ?_, ?_⟩
    · apply UInt64.toBitVec_inj.mp; rw [h0, h2]
    · unfold SliceOk; rw [h1, hn2]; exact hl1
    · unfold SliceOk; rw [h3, hn4]; exact hl3
  refine Fr.leaf hfr hN hle keep_callee slots_le (fun _ h ↦ h.elim) hmle
    (fun m m' hq ↦ ⟨Bus.changes_zero hq.2.1, hq.2.2⟩) hpc hpre fun m2 hfr2 hq hcs ↦ ?_
  refine cont m2 hfr2 ?_ hcs (Bus.changes_zero hq.2.1)
  rw [hq.1]
  unfold slice
  have e1 : NativeRustcVm.ewsOf st.data.dmem (base m1 608 + BitVec.ofNat 64 496) 2 = [x, y] :=
    NativeRustcVm.ewsOf_of_ewsAt hxy
  have e3 : NativeRustcVm.ewsOf st.data.dmem (base m1 608 + BitVec.ofNat 64 528) 1 = [ch] :=
    NativeRustcVm.ewsOf_of_ewsAt hch
  rw [h1, hn2, h3, hn4, e1, e3]

/-- **`push_claim`** of a column at the point of `n` elements at the frame's base, on the claims
at `cA`. -/
theorem push_call
    (hpush : ∀ cs, Spec (Labels.label NativeRustcVmArm.Vm.PushClaim.entryLabel) (PushClaimPre cs) (PushClaimPost cs))
    {m1 : MachineData} (hS1 : StackOk m1 publicInputPhaseStack) {cA : BitVec 64}
    (hcR : Readable m1 cA claimsBytes) (hcO : OffStack m1 cA claimsBytes publicInputPhaseStack)
    {st : MachineState} {next : Int64} {R : MachineState → Prop}
    (hfr : Fr m1 608 publicInputPhaseStack slots keep (fun _ ↦ False) st.data)
    (hpc : st.pc = Labels.label NativeRustcVmArm.Vm.PushClaim.entryLabel ∧ retOf st.data = next)
    (h0 : st.data.regs.X0.toBitVec = cA) (h2 : st.data.regs.X2.toBitVec = base m1 608) {n : Nat}
    (h3 : st.data.regs.X3.toNat = n) (hn : n ≤ 31) {cs : Array ColumnClaimW}
    (hcs : ClaimsWAt st.data.dmem cA cs)
    (cont : ∀ m2, Fr m1 608 publicInputPhaseStack slots keep (fun q ↦ InRange cA claimsBytes q) m2 →
      PushClaimPost cs st.data m2 →
      (∀ r, calleeSaved r = true → m2.regs.getXReg r = st.data.regs.getXReg r) →
      Eventually (step1 Host.exe) R ⟨m2, next⟩) :
    Eventually (step1 Host.exe) R st := by
  have hle := le_push
  have hN := hS1.2.1
  have hap : Apart cA claimsBytes (base m1 608) 608 := apart_frame hN le_N hcO
  have hfrO : ∀ q, InRange cA claimsBytes q → ¬InRange (base m1 608) 608 q := fun q hq ↦
    NativeRustcVm.Apart.not_inRange hap hcR.2 (base_noWrap (by have := le_N; omega)) hq
  have hlp := Bus.local_ok (o := 0) (n := 16 * n) hS1 hle (by omega) hfr.kept hfr.sp
  rw [NativeRustcVm.addr_add_zero] at hlp
  refine Bus.Gkr.Fr.callSpec (Bus.Fr.mono hfr fun _ h ↦ h.elim) hN hle keep_callee slots_le
    hfrO (hpush cs) hpc ?_ (fun m' hq ↦ ⟨?_, hq.2.2⟩) cont
  · refine ⟨hfr.stackOk hS1 rfl hle, by rw [h0]; exact hcs, ?_, ?_, ?_, ?_⟩
    · rw [h0]; exact Bus.Fr.readable hfr hcR
    · rw [h0]; exact Bus.Fr.offStack hfr hS1 hcO hle
    · unfold SliceOk; rw [h2, h3]; exact hlp
    · rw [h0, h2, h3]
      exact NativeRustcVm.Apart.mono_right hap (Nat.le_refl _) (by omega)
  · refine NativeRustcVm.SameOutside.mono hq.2.1 fun q hq' ↦ ?_
    rcases hq' with hq' | hq'
    · exact .inr (by rw [h0] at hq'; exact hq')
    · exact .inl hq'

end

end

end NativeRustcVmArm.Tables.PublicInputPhase
