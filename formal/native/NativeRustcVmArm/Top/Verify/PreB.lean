module

public import NativeRustcVmArm.Top.Verify.Init

/-!
# `verify`: `verify_execution`'s precondition

After `b1`, the frame's body, the arguments in X0 to X4 and the `TState` representing the first
state give `verify_execution`'s precondition (`vePre`); the areas' apartness as numbers
(`disjA`, `disjB`).
-/

namespace NativeRustcVmArm.Top.Verify

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.Verify NativeVm.Model
open NativeRustcVm.Transcript
open NativeRustcVm (WordAt WordsAt Region wordsOf wordOf)
open NativeRustcVm.Top (workAreaBytes)

public section

/-- `verify_execution`'s areas apart. -/
theorem disjA {S la : Nat} {sb t pub w aw : BitVec 64} (hsb : sb.toNat = S - 19216)
    (ht : t.toNat = S - 824) (hs : 19216 ≤ S)
    (ga : aw.toNat + la ≤ S - 19216 ∨ S ≤ aw.toNat)
    (gp : pub.toNat + 32 ≤ S - 19216 ∨ S ≤ pub.toNat)
    (gw : w.toNat + 495552 ≤ S - 19216 ∨ S ≤ w.toNat)
    (hpa : NativeRustcVm.Apart pub 32 aw la) (hpw : NativeRustcVm.Apart pub 32 w 495552)
    (haw : NativeRustcVm.Apart aw la w 495552) :
    NativeRustcVm.Disjoint [⟨sb, 18384⟩, ⟨t, 760⟩, ⟨aw, la⟩, ⟨pub, 32⟩, ⟨w, 495552⟩] := by
  unfold NativeRustcVm.Apart at hpa hpw haw
  refine disjoint_five ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> dsimp only [NativeRustcVm.Apart] <;> omega

/-- `verify_execution`'s areas apart from a nonempty bytecode. -/
theorem disjB {S la N : Nat} {sb t bc w aw : BitVec 64} (hsb : sb.toNat = S - 19216)
    (ht : t.toNat = S - 824) (hs : 19216 ≤ S)
    (ga : aw.toNat + la ≤ S - 19216 ∨ S ≤ aw.toNat)
    (gb : bc.toNat + N ≤ S - 19216 ∨ S ≤ bc.toNat)
    (gw : w.toNat + 495552 ≤ S - 19216 ∨ S ≤ w.toNat)
    (hba : NativeRustcVm.Apart bc N aw la) (hbw : NativeRustcVm.Apart bc N w 495552)
    (haw : NativeRustcVm.Apart aw la w 495552) :
    NativeRustcVm.Disjoint [⟨sb, 18384⟩, ⟨bc, N⟩, ⟨t, 760⟩, ⟨aw, la⟩, ⟨w, 495552⟩] := by
  unfold NativeRustcVm.Apart at hba hbw haw
  refine disjoint_five ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> dsimp only [NativeRustcVm.Apart] <;> omega

/-- `VerifyPre`'s areas pairwise apart (those `Geo` does not give). -/
theorem apart_of [Labels] {a : DecArea} {stream : Array EW} {openings : Array (Array OpeningW)}
    {m0 : MachineData} (hpre : VerifyPre a stream openings m0) :
    NativeRustcVm.Apart m0.regs.X2.toBitVec 32 a.words (8 * a.len) ∧
      NativeRustcVm.Apart m0.regs.X2.toBitVec 32 m0.regs.X4.toBitVec workAreaBytes ∧
      NativeRustcVm.Apart a.words (8 * a.len) m0.regs.X4.toBitVec workAreaBytes ∧
      (0 < m0.regs.X1.toNat →
        NativeRustcVm.Apart m0.regs.X0.toBitVec (8 * m0.regs.X1.toNat) a.words (8 * a.len) ∧
        NativeRustcVm.Apart m0.regs.X0.toBitVec (8 * m0.regs.X1.toNat) m0.regs.X4.toBitVec
          workAreaBytes) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hdis, -, hbcD⟩ := hpre
  simp only [NativeRustcVm.Disjoint, List.pairwise_cons, List.mem_cons, List.mem_nil_iff,
    or_false, forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true, DecArea.region] at hdis
  refine ⟨hdis.2.1.2.1, hdis.2.1.2.2, hdis.2.2.2.1, fun hn ↦ ?_⟩
  have h := (hbcD hn).1
  simp only [NativeRustcVm.Disjoint, List.pairwise_cons, List.mem_cons, List.mem_nil_iff,
    or_false, forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true, DecArea.region] at h
  exact ⟨h.2.1.1, h.2.1.2⟩

/-- **`verify_execution`'s precondition** after `b1`. -/
theorem vePre [Labels] {a : DecArea} {stream : Array EW} {openings : Array (Array OpeningW)}
    {m0 st1 : MachineData} {s : TState} (hpre : VerifyPre a stream openings m0)
    (hB1 : Body m0 832 slots (InStack m0 verifyStack) st1)
    (hX0 : st1.regs.X0.toBitVec = tOf m0) (hX1 : st1.regs.X1 = m0.regs.X0)
    (hX2 : st1.regs.X2 = m0.regs.X1) (hX3 : st1.regs.X3 = m0.regs.X2)
    (hX4 : st1.regs.X4 = m0.regs.X4) (hts : TStateAt st1.dmem (tOf m0) a s)
    (hroots : s.roots.size = 0) : VerifyExecutionPre a s st1 := by
  have g := geo_of hpre
  obtain ⟨hpa, hpw, haw, hbcA⟩ := apart_of hpre
  obtain ⟨⟨-, -, hmap⟩, hrod, -, -, -, ⟨hbcM, -⟩, ⟨hpubM, -⟩, -, -, ⟨hwM, -⟩, -, hapR, hbcR⟩ :=
    hpre
  have hs := g.s
  have hF := g.F
  have hT := g.T
  have hsb0 := g.sb
  have hS := verifyStack_eq
  have hsl := m0.regs.SP.toBitVec.isLt
  have hVE : verifyExecutionStack = 18384 := rfl
  have e1 : m0.regs.X1.toNat = m0.regs.X1.toBitVec.toNat := rfl
  have hsp1 : st1.regs.SP.toBitVec = frameOf m0 := hB1.sp
  have hsbV : (stackBelow st1 verifyExecutionStack).toNat =
      m0.regs.SP.toBitVec.toNat - 19216 := by
    show (st1.regs.SP.toBitVec - BitVec.ofNat 64 verifyExecutionStack).toNat = _
    rw [hsp1, hVE, toNat_subAddr (by rw [hF]; omega), hF]; omega
  refine ⟨⟨?_, ?_, ?_⟩, rodataAt_body hrod hB1 (by omega) hsp1 (by rw [hS]; decide),
    ?_, ?_, hroots, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, fun hn ↦ ⟨?_, ?_⟩⟩
  · show st1.regs.SP.toBitVec.toNat % 16 = 0
    rw [hsp1, hF]; have := g.al; omega
  · show verifyExecutionStack ≤ st1.regs.SP.toBitVec.toNat
    rw [hsp1, hF, hVE]; omega
  · show Mapped st1.dmem (st1.regs.SP.toBitVec - BitVec.ofNat 64 verifyExecutionStack) _
    refine Mapped.kept (Mapped.within hmap (by rw [hsb0]; omega) ?_ ?_) hB1.kept
    · rw [hsb0, hsp1, hVE, toNat_subAddr (by rw [hF]; omega), hF]; omega
    · rw [hsb0, hsp1, hVE, toNat_subAddr (by rw [hF]; omega), hF]; omega
  · show 9 + 8 * st1.regs.X2.toNat < 2 ^ 32
    rw [hX2]; exact g.n32
  · show TStateAt st1.dmem st1.regs.X0.toBitVec a _
    rw [hX0]; exact hts
  · show Mapped st1.dmem st1.regs.X1.toBitVec (8 * st1.regs.X2.toNat)
    rw [hX1, hX2]; exact Mapped.kept hbcM hB1.kept
  · show st1.regs.X1.toBitVec.toNat + 8 * st1.regs.X2.toNat ≤ 2 ^ 64
    rw [hX1, hX2]; exact g.bcN
  · show Mapped st1.dmem st1.regs.X3.toBitVec 32
    rw [hX3]; exact Mapped.kept hpubM hB1.kept
  · show st1.regs.X3.toBitVec.toNat + 32 ≤ 2 ^ 64
    rw [hX3]; exact g.pubN
  · show Mapped st1.dmem st1.regs.X4.toBitVec workAreaBytes
    rw [hX4]; exact Mapped.kept hwM hB1.kept
  · show st1.regs.X4.toBitVec.toNat + workAreaBytes ≤ 2 ^ 64
    rw [hX4]; exact g.workN
  · show NativeRustcVm.Disjoint [⟨stackBelow st1 verifyExecutionStack, verifyExecutionStack⟩,
      ⟨st1.regs.X0.toBitVec, tstateBytes⟩, ⟨a.words, 8 * a.len⟩, ⟨st1.regs.X3.toBitVec, 32⟩,
      ⟨st1.regs.X4.toBitVec, workAreaBytes⟩]
    rw [hX0, hX3, hX4]
    exact disjA hsbV hT hs g.area g.pub g.work hpa hpw haw
  · intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · show RodataApart st1.regs.X0.toBitVec tstateBytes
      rw [hX0]
      intro it
      have := hrod.apart it
      unfold NativeRustcVm.Apart at this ⊢
      rw [show (stackBelow m0 verifyStack).toNat = m0.regs.SP.toBitVec.toNat - 19216
        from hsb0] at this
      unfold tstateBytes; omega
    · exact hapR a.region (by simp)
    · show RodataApart st1.regs.X3.toBitVec 32
      rw [hX3]; exact hapR ⟨_, 32⟩ (by simp)
    · show RodataApart st1.regs.X4.toBitVec workAreaBytes
      rw [hX4]; exact hapR ⟨_, workAreaBytes⟩ (by simp)
  · have hn' : 0 < m0.regs.X1.toNat := by rw [← hX2]; exact hn
    obtain ⟨hba, hbw⟩ := hbcA hn'
    show NativeRustcVm.Disjoint [⟨stackBelow st1 verifyExecutionStack, verifyExecutionStack⟩,
      ⟨st1.regs.X1.toBitVec, 8 * st1.regs.X2.toNat⟩, ⟨st1.regs.X0.toBitVec, tstateBytes⟩,
      ⟨a.words, 8 * a.len⟩, ⟨st1.regs.X4.toBitVec, workAreaBytes⟩]
    rw [hX0, hX1, hX2, hX4]
    have gb := g.bc (by rw [← e1]; exact hn')
    rw [← e1] at gb
    exact disjB hsbV hT hs g.area gb g.work hba hbw haw
  · show RodataApart st1.regs.X1.toBitVec (8 * st1.regs.X2.toNat)
    rw [hX1, hX2]
    exact (hbcR (by rw [← hX2]; exact hn)).2

end

end NativeRustcVmArm.Top.Verify
