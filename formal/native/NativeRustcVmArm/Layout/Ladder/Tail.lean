module

public import NativeRustcVmArm.Layout.Ladder.Exec
public import NativeRustcVmArm.Layout.Ladder.Table

/-!
# `ladder`'s store (`b15`)

At `b15` the registers hold the result's words (`R15`): the count, each level's fold, rate and
query count. `b15` stores them in order, run from `endS` (region 0 the result): the result is
`Whir.ladder μ r` (`tail`).
-/

namespace NativeRustcVmArm.Layout.Ladder

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.Ladder
open LeanVM.Parameters NativeRustcVm.Layout
open NativeRustcVm (WordAt WordsAt addr_add_add addr_add_zero)
open NativeRustcVm.Transcript (off)

public section

theorem toUInt64_toNat (x : UInt64) : x.toNat.toUInt64 = x := by
  apply UInt64.toNat.inj; simp

theorem wordAt_conv {d : Mem 64} {a : BitVec 64} {x : UInt64} {n : Nat} (h : WordAt d a x)
    (hx : x.toNat = n) : WordAt d a n.toUInt64 := by
  rw [← hx, toUInt64_toNat]; exact h

theorem ptr_zero_eval [Labels] (env : Env) (r : Nat) : (Sym.ptr r 0).eval env = env.base r := by
  simp [Sym.eval]

/-- Three words from `o + j`. -/
theorem words3 {d : Mem 64} {o : BitVec 64} {j : Nat} {a b c : UInt64}
    (ha : WordAt d (o + BitVec.ofNat 64 j) a) (hb : WordAt d (o + BitVec.ofNat 64 (j + 8)) b)
    (hc : WordAt d (o + BitVec.ofNat 64 (j + 8 + 8)) c) :
    WordsAt d (o + BitVec.ofNat 64 j) [a, b, c] := by
  rw [NativeRustcVm.wordsAt_cons_iff, NativeRustcVm.wordsAt_cons_iff,
    NativeRustcVm.wordsAt_singleton_iff, addr_add_add, addr_add_add]
  exact ⟨ha, hb, hc⟩

/-- **The registers at `b15`**, for the entry `m` (`μ` in X1, `r` in X2): memory and the frame as
at the entry, the count, and each level's words (those past the third for the levels there are). -/
structure R15 (m st : MachineData) : Prop where
  dmem : st.dmem = m.dmem
  saved : Saved m st
  x0 : st.regs.X0 = m.regs.X0
  x30 : st.regs.X30 = m.regs.X30
  x2 : st.regs.X2 = m.regs.X2
  x13 : st.regs.X13.toNat = nOf m.regs.X1.toNat
  x1 : st.regs.X1.toNat = m.regs.X2.toNat + 3
  x17 : st.regs.X17.toNat = m.regs.X2.toNat + 6
  x18 : st.regs.X18.toNat = qAt m.regs.X1.toNat m.regs.X2.toNat 0
  x16 : st.regs.X16.toNat = qAt m.regs.X1.toNat m.regs.X2.toNat 1
  x15 : st.regs.X15.toNat = qAt m.regs.X1.toNat m.regs.X2.toNat 2
  l3 : 3 < nOf m.regs.X1.toNat → st.regs.X12.toNat = 4 ∧ st.regs.X8.toNat = m.regs.X2.toNat + 9 ∧
    st.regs.X3.toNat = qAt m.regs.X1.toNat m.regs.X2.toNat 3
  l4 : 4 < nOf m.regs.X1.toNat → st.regs.X14.toNat = 4 ∧ st.regs.X9.toNat = m.regs.X2.toNat + 12 ∧
    st.regs.X4.toNat = qAt m.regs.X1.toNat m.regs.X2.toNat 4
  l5 : 5 < nOf m.regs.X1.toNat → st.regs.X11.toNat = 4 ∧ st.regs.X10.toNat = m.regs.X2.toNat + 15 ∧
    st.regs.X5.toNat = qAt m.regs.X1.toNat m.regs.X2.toNat 5

variable [Host] {k : Nat}

/-- **`b15`**: the result stored, the return. -/
theorem tail (hp : Placed code k) {m : MachineData}
    (hO : Readable m m.regs.X0.toBitVec ladderBytes)
    (hadm : Whir.Admissible m.regs.X1.toNat m.regs.X2.toNat) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.Ladder.b15Offset)) (hR : R15 m st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = retOf m ∧ LadderPost m st'.data) st := by
  set o := m.regs.X0.toBitVec with ho
  set μ := m.regs.X1.toNat with hμ
  set r := m.regs.X2.toNat with hr
  let env := Env.ofMachine st.data [(o, 160)]
  have hwf : env.WF := Env.wf_of
    ⟨⟨show Mapped st.data.dmem o 160 by rw [hR.dmem]; exact hO.1, hO.2⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hm : Match env endS st.data :=
    match_ofMachine ⟨rfl, nofun, trivial⟩ rfl
      ⟨show _ = (Sym.ptr 0 0).eval env by
        rw [ptr_zero_eval]; exact congrArg UInt64.toBitVec hR.x0, trivial⟩ trivial trivial trivial
  have hx30 : env.regs .X30 = m.regs.X30.toBitVec := congrArg UInt64.toBitVec hR.x30
  refine exec_at (infix_of b15_in_code (by simp [b15]) hp) run_b15 hwf hpc hm
    fun st' hm' hpc' ↦ .done _ ⟨?_, ?_, ?_, ?_⟩
  · simp only [PcOk] at hpc'
    exact hpc'.trans (retOf_of_x30 hm' rfl hx30)
  · -- The words.
    have hn := nOf_le μ
    have w0 := Layout.Match.wordAt_write hm' (r := 0) (o := 0) (v := .lit 1) rfl (by decide)
      (by decide)
    have w152 := Layout.Match.wordAt_write hm' (r := 0) (o := 152) (v := .reg .X13) rfl
      (by decide) (by decide)
    rw [addr_add_zero] at w0
    rw [ladder_eq hadm]
    refine ⟨w0, by rw [length_ladderW]; exact hn.2, ?_, ?_⟩
    · rw [length_ladderW]; exact wordAt_conv w152 hR.x13
    · intro i hi
      rw [length_ladderW] at hi
      simp only [ladderW, List.getElem_map, List.getElem_range]
      have hb := admissible_iff.mp hadm
      refine ⟨show foldAt i < 2 ^ 64 by unfold foldAt; split <;> omega,
        show r + 3 * i < 2 ^ 64 by omega,
        show qAt μ r i < 2 ^ 64 from lt_of_le_of_lt (qAt_le _ _ _) (by decide), ?_⟩
      rw [show off (off o 8) (NativeRustcVm.Whir.levelBytes * i) =
        o + BitVec.ofNat 64 (8 + 24 * i) from addr_add_add _ _ _]
      have hi6 : i < 6 := by omega
      interval_cases i
      · refine words3 (wordAt_conv (Layout.Match.wordAt_write hm' (r := 0) (o := 8) (v := .lit 6)
          rfl (by decide) (by decide)) rfl) (wordAt_conv (Layout.Match.wordAt_write hm' (r := 0)
          (o := 16) (v := .reg .X2) rfl (by decide) (by decide)) ?_) (wordAt_conv
          (Layout.Match.wordAt_write hm' (r := 0) (o := 24) (v := .reg .X18) rfl (by decide)
          (by decide)) hR.x18)
        show (st.data.regs.X2).toNat = r + 3 * 0
        rw [hR.x2]; rfl
      · exact words3 (wordAt_conv (Layout.Match.wordAt_write hm' (r := 0) (o := 32) (v := .lit 4)
          rfl (by decide) (by decide)) rfl) (wordAt_conv (Layout.Match.wordAt_write hm' (r := 0)
          (o := 40) (v := .reg .X1) rfl (by decide) (by decide)) hR.x1) (wordAt_conv
          (Layout.Match.wordAt_write hm' (r := 0) (o := 48) (v := .reg .X16) rfl (by decide)
          (by decide)) hR.x16)
      · exact words3 (wordAt_conv (Layout.Match.wordAt_write hm' (r := 0) (o := 56) (v := .lit 4)
          rfl (by decide) (by decide)) rfl) (wordAt_conv (Layout.Match.wordAt_write hm' (r := 0)
          (o := 64) (v := .reg .X17) rfl (by decide) (by decide)) hR.x17) (wordAt_conv
          (Layout.Match.wordAt_write hm' (r := 0) (o := 72) (v := .reg .X15) rfl (by decide)
          (by decide)) hR.x15)
      · obtain ⟨h12, h8, h3⟩ := hR.l3 hi
        exact words3 (wordAt_conv (Layout.Match.wordAt_write hm' (r := 0) (o := 80)
          (v := .reg .X12) rfl (by decide) (by decide)) h12) (wordAt_conv
          (Layout.Match.wordAt_write hm' (r := 0) (o := 88) (v := .reg .X8) rfl (by decide)
          (by decide)) h8) (wordAt_conv (Layout.Match.wordAt_write hm' (r := 0) (o := 96)
          (v := .reg .X3) rfl (by decide) (by decide)) h3)
      · obtain ⟨h14, h9, h4⟩ := hR.l4 hi
        exact words3 (wordAt_conv (Layout.Match.wordAt_write hm' (r := 0) (o := 104)
          (v := .reg .X14) rfl (by decide) (by decide)) h14) (wordAt_conv
          (Layout.Match.wordAt_write hm' (r := 0) (o := 112) (v := .reg .X9) rfl (by decide)
          (by decide)) h9) (wordAt_conv (Layout.Match.wordAt_write hm' (r := 0) (o := 120)
          (v := .reg .X4) rfl (by decide) (by decide)) h4)
      · obtain ⟨h11, h10, h5⟩ := hR.l5 hi
        exact words3 (wordAt_conv (Layout.Match.wordAt_write hm' (r := 0) (o := 128)
          (v := .reg .X11) rfl (by decide) (by decide)) h11) (wordAt_conv
          (Layout.Match.wordAt_write hm' (r := 0) (o := 136) (v := .reg .X10) rfl (by decide)
          (by decide)) h10) (wordAt_conv (Layout.Match.wordAt_write hm' (r := 0) (o := 144)
          (v := .reg .X5) rfl (by decide) (by decide)) h5)
  · -- Only the result changed.
    have hs := Layout.Match.sameOutside_regions hm' hwf (by decide)
    intro p hp'
    refine (hs p fun ⟨e, he, h⟩ ↦ hp' ?_).trans (congrArg (·.get? p) hR.dmem)
    obtain rfl : e = (o, 160) := List.mem_singleton.mp he
    exact .inl h
  · exact hR.saved.trans (Match.saved hm hm' hwf rfl (by decide))

end

end NativeRustcVmArm.Layout.Ladder
