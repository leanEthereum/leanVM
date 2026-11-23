module

public import NativeRustcVmArm.Sumcheck.OpenPhase.Exec
public import NativeRustcVmArm.Sumcheck.Loop
public import NativeRustcVm.Sumcheck.OpenPhase

/-!
# `open_phase`: the frame and the exits

The 176-byte frame (`FrO`, `Ring.Fr`, no outputs before the exit): the phase's openings' address
at `0`, `8 w` at `8`, `climb`'s output at `16`, `hash_words`' at `48`, the saved registers from
`80` (`slotsO`). The inputs (the phase, the root, the positions) are apart from the stack, so
kept (`FrO.keep`); a callee from the frame gets its stack and the round constants
(`FrO.stackOk`, `FrO.rcAt`). `exit_fail` (`b22`, `b23`): `None` at the output; `exit_rows`
(`b21`, `b23`): the rows.
-/

namespace NativeRustcVmArm.Sumcheck.OpenPhase

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.OpenPhase
open NativeRustcVmArm.Ring NativeRustcVm.Transcript NativeVm.Model NativeRustcVm.Sumcheck
open LeanVM.Protocol LeanVM.Protocol.Compile NativeVm

@[expose] public section

/-- The saved registers' slots. -/
def slotsO : List (Nat × XReg) :=
  [(80, .X29), (88, .X30), (96, .X28), (104, .X27), (112, .X26), (120, .X25), (128, .X24),
    (136, .X23), (144, .X22), (152, .X21), (160, .X20), (168, .X19)]

/-- The output, the root, the positions, the phase: X0, X1, X4, X6 at the entry. -/
abbrev outO (m0 : MachineData) : BitVec 64 := m0.regs.X0.toBitVec
abbrev rootO (m0 : MachineData) : BitVec 64 := m0.regs.X1.toBitVec
abbrev posO (m0 : MachineData) : BitVec 64 := m0.regs.X4.toBitVec
abbrev phO (m0 : MachineData) : BitVec 64 := m0.regs.X6.toBitVec

/-- The frame. -/
abbrev FrO [Labels] (m0 m : MachineData) : Prop :=
  Fr m0 176 openPhaseStack slotsO [] (fun _ ↦ False) m

end

public section

theorem openPhaseStack_eq : openPhaseStack = 1088 := by decide

section
variable [Labels] {P : Array OpeningW} {R : Digest} {Q : Array UInt64} {m0 m : MachineData}

theorem hN (hpre : OpenPhasePre P R Q m0) : openPhaseStack ≤ m0.regs.SP.toNat := hpre.1.2.1

theorem stack_noWrap (hpre : OpenPhasePre P R Q m0) :
    NoWrap (stackBelow m0 openPhaseStack) openPhaseStack := Bus.stack_noWrap hpre.1

/-- **An input kept**: bytes apart from the stack. -/
theorem keep (hpre : OpenPhasePre P R Q m0) (hf : FrO m0 m) {x : BitVec 64} {n : Nat}
    (hnw : NoWrap x n) (hap : Apart x n (stackBelow m0 openPhaseStack) openPhaseStack)
    {bs : List UInt8} (hle : bs.length ≤ n) (h : NativeRustcVm.BytesAt m0.dmem x bs) :
    NativeRustcVm.BytesAt m.dmem x bs :=
  NativeRustcVm.BytesAt.of_sameOutside h hf.same fun i hi hq ↦ hq.elim
    (fun hs ↦ NativeRustcVm.Apart.not_inRange hap hnw (stack_noWrap hpre)
      (by unfold NoWrap at hnw; exact NativeRustcVm.inRange_add (by omega) (by omega)) hs)
    id

/-- A callee's stack below the frame. -/
theorem stackOk (hpre : OpenPhasePre P R Q m0) (hf : FrO m0 m) {N' : Nat}
    (hle : 176 + N' ≤ openPhaseStack) : StackOk m N' :=
  hf.stackOk hpre.1 (by decide) hle

/-- A callee's round constants. -/
theorem rcAt (hpre : OpenPhasePre P R Q m0) (hf : FrO m0 m) {N' : Nat}
    (hle : 176 + N' ≤ openPhaseStack) : RcAt m N' :=
  RcAt.sub hpre.2.1 hf.sp hle (hN hpre) fun p hp ↦ hf.same p fun h ↦ h.elim
    (fun hs ↦ NativeRustcVm.Apart.not_inRange hpre.2.1.2.2 hpre.2.1.2.1 (stack_noWrap hpre) hp hs)
    id

/-- A local of the frame, apart from the round constants. -/
theorem local_rc (hpre : OpenPhasePre P R Q m0) {o n : Nat} (hon : o + n ≤ 176) :
    Apart (base m0 176 + BitVec.ofNat 64 o) n rcAddr 192 := by
  have hap := apart_frame (F := 176) (hN hpre) (by decide) hpre.2.1.2.2
  have hb := base_toNat (m0 := m0) (F := 176) (le_trans (by decide) (hN hpre))
  have hl := m0.regs.SP.toNat_lt
  have h1088 := hN hpre
  rw [openPhaseStack_eq] at h1088
  unfold Apart at hap ⊢
  rw [NativeRustcVm.toNat_add_ofNat (by omega)]
  omega

end

variable [Host] {P : Array OpeningW} {R : Digest} {Q : Array UInt64} {m0 : MachineData} {k : Nat}

/-- **The exits' common part**: from the frame, `ds` (`b21` or `b22`) from `outS`, then `b23`. -/
theorem exit_of (hp : Placed code k) (hpre : OpenPhasePre P R Q m0) {m : MachineData}
    (hf : FrO m0 m) (hx19 : m.regs.getXReg .X19 = m0.regs.X0) {ds : List Directive} {j : Nat}
    {S1 S2 : SState} {x : Exit} (hk : ds.IsInfixAt Host.prog j) (hx1 : exec ds outS = some (S1, x))
    (hpc1 : ∀ st, PcOk (Env.ofMachine m [(base m0 176, 176), (outO m0, 32)]) x
      (Host.addrOf (j + ds.length)) st → st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.OpenPhase.b23Offset))
    (hx2 : exec b23 S1 = some (S2, .ret))
    (hok : exitOk S2 176 slotsO [] = true) (hW : ∀ w ∈ S2.mem, w.r = 1 ∧ w.off + w.n ≤ 32)
    (hout : ∀ st : MachineState,
      Match (Env.ofMachine m [(base m0 176, 176), (outO m0, 32)]) S2 st.data →
      OptRowsAt st.data.dmem (outO m0) (off (phO m0) 24) (openPhase R m0.regs.X2.toNat
        m0.regs.X3.toNat Q P)) :
    Eventually (step1 Host.exe)
      (fun st ↦ st.pc = retOf m0 ∧ OpenPhasePost P R Q m0 st.data) ⟨m, Host.addrOf j⟩ := by
  have hS := hpre.1
  have hk23 : b23.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.OpenPhase.b23Offset) := b23_in_code.trans hp.1 (by simp [b23])
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hmo, hnwo, -, -, -, haso, -⟩ := hpre
  have hwf : (Env.ofMachine m [(base m0 176, 176), (outO m0, 32)]).WF :=
    Bus.wf_frame2 hS (by decide) hf.kept ⟨hmo, hnwo⟩ haso
  have hm : Match (Env.ofMachine m [(base m0 176, 176), (outO m0, 32)]) outS m := by
    have := Bus.match_frame2 (r := .X19) (n := 32) hS (by decide) (by decide) hf.sp
    rwa [hx19] at this
  refine exec_then hk hx1 hwf hm fun st1 hm1 hpc1' ↦ ?_
  refine exec_at hk23 hx2 hwf (hpc1 st1 hpc1') hm1 fun st hm' hpc ↦ Eventually.done _ ?_
  obtain ⟨hret, hsv⟩ := Fr.exit hf hm' hwf hok
  have hwr : ∀ q, Written (Env.ofMachine m [(base m0 176, 176), (outO m0, 32)]) S2 q →
      InRange (outO m0) 32 q := fun q hq ↦ Written.inRange (r := 1) rfl hnwo hW hq
  have hs := hm'.sameOutside hwf
  refine ⟨hpc.trans hret, hout st hm', ?_, hsv⟩
  refine NativeRustcVm.SameOutside.mono (NativeRustcVm.SameOutside.trans hf.same hs)
    fun q hq ↦ ?_
  rcases hq with (hq | hq) | hq
  · exact .inr hq
  · exact hq.elim
  · exact .inl (hwr q hq)

/-- **`b22`, `b23`**: a rejection, `None` at the output. -/
theorem exit_fail (hp : Placed code k) (hpre : OpenPhasePre P R Q m0) {m : MachineData}
    (hf : FrO m0 m) (hx19 : m.regs.getXReg .X19 = m0.regs.X0)
    (hr : openPhase R m0.regs.X2.toNat m0.regs.X3.toNat Q P = none) :
    Eventually (step1 Host.exe)
      (fun st ↦ st.pc = retOf m0 ∧ OpenPhasePost P R Q m0 st.data)
      ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.OpenPhase.b22Offset)⟩ := by
  have hk22 : b22.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.OpenPhase.b22Offset) := b22_in_code.trans hp.1 (by simp [b22])
  refine exit_of hp hpre hf hx19 hk22 run_b22 (fun st h ↦ h)
    (by rw [← after_eq run_b22]; exact run_b23b) (by decide) (by decide) fun st hm' ↦ ?_
  rw [hr]
  have w0 := NativeRustcVmArm.Sumcheck.Match.wordAt_write hm' (r := 1) (o := 0) rfl (by decide)
    (v := .lit 0) (by decide +kernel)
  rw [NativeRustcVm.addr_add_zero] at w0
  exact w0

/-- **`b21`, `b23`**: the rows at the output, reading the openings at `phase + 24`. -/
theorem exit_rows (hp : Placed code k) (hpre : OpenPhasePre P R Q m0) {m : MachineData}
    (hf : FrO m0 m) (hx19 : m.regs.getXReg .X19 = m0.regs.X0) {w : Nat}
    (hw : w ≤ wireMaxLeafWords) (hsz : P.size ≤ wireMaxQueries)
    (h0 : NativeRustcVm.WordAt m.dmem (base m0 176 + BitVec.ofNat 64 0)
      (UInt64.ofBitVec (off (phO m0) 24)))
    (h23 : m.regs.getXReg .X23 = P.size.toUInt64) (h21 : m.regs.getXReg .X21 = w.toUInt64)
    (hleaf : ∀ j (hj : j < P.size), P[j].leaf.size = w ∧
      NativeRustcVm.WordsAt m.dmem (off (off (phO m0) 24) (8 * (1 + j * openingWords)))
        P[j].leaf.toList)
    (hr : openPhase R m0.regs.X2.toNat m0.regs.X3.toNat Q P = some (P.map (·.leaf))) :
    Eventually (step1 Host.exe)
      (fun st ↦ st.pc = retOf m0 ∧ OpenPhasePost P R Q m0 st.data)
      ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.OpenPhase.b21Offset)⟩ := by
  have hk21 : b21.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.OpenPhase.b21Offset) := b21_in_code.trans hp.1 (by simp [b21])
  obtain ⟨-, -, -, -, -, -, -, hnwp, -, -, hmo, hnwo, -, -, -, haso, hop, -⟩ := id hpre
  have hpw : phaseWords = 49411 := rfl
  have how : openingWords = 193 := rfl
  have hmq : wireMaxQueries = 256 := rfl
  have hml : wireMaxLeafWords = 64 := rfl
  unfold NoWrap at hnwp hnwo
  rw [hpw] at hnwp hop
  have hnwp' : (phO m0).toNat + 8 * 49411 ≤ 2 ^ 64 := hnwp
  have hnwo' : (outO m0).toNat + 32 ≤ 2 ^ 64 := hnwo
  have hsz' : P.size ≤ 256 := hsz
  have hw' : w ≤ 64 := hw
  refine exit_of hp hpre hf hx19 hk21 run_b21 (fun st h ↦ h.trans (hp.label (j := NativeRustcVmArm.Vm.OpenPhase.b23Offset) NativeRustcVmArm.Vm.OpenPhase.label_19_at))
    (by rw [← after_eq run_b21]; exact run_b23a) (by decide) (by decide) fun st hm' ↦ ?_
  rw [hr]
  have hb0 : (Env.ofMachine m [(base m0 176, 176), (outO m0, 32)]).base 0 = base m0 176 := rfl
  have hwr : ∀ q, Written (Env.ofMachine m [(base m0 176, 176), (outO m0, 32)])
      (after b23 (after b21 outS)) q → InRange (outO m0) 32 q := fun q hq ↦
    Written.inRange (r := 1) rfl hnwo (by rw [after_eq run_b23a]; decide +kernel) hq
  have hs : SameOutside m.dmem st.data.dmem (InRange (outO m0) 32) :=
    NativeRustcVm.SameOutside.mono (hm'.sameOutside (Bus.wf_frame2 hpre.1 (by decide) hf.kept
      ⟨hmo, hnwo⟩ haso))
      (fun q hq ↦ hwr q (by rw [after_eq run_b23a]; exact hq))
  have w0 := NativeRustcVmArm.Sumcheck.Match.wordAt_write hm' (r := 1) (o := 0) rfl (by decide)
    (v := .load 0 0 8) (by decide +kernel)
  have w8 := NativeRustcVmArm.Sumcheck.Match.wordAt_write hm' (r := 1) (o := 8) rfl (by decide)
    (v := .lit 49408) (by decide +kernel)
  have w16 := NativeRustcVmArm.Sumcheck.Match.wordAt_write hm' (r := 1) (o := 16) rfl
    (by decide) (v := .reg .X23) (by decide +kernel)
  have w24 := NativeRustcVmArm.Sumcheck.Match.wordAt_write hm' (r := 1) (o := 24) rfl
    (by decide) (v := .reg .X21) (by decide +kernel)
  have hpz : off (phO m0) 24 ≠ 0 := fun h ↦ by
    have := congrArg BitVec.toNat h
    rw [off, NativeRustcVm.toNat_add_ofNat (by omega)] at this
    simp at this
  refine ⟨hpz, by simpa using hsz, w, hw, ?_, fun j hj ↦ ?_⟩
  · rw [NativeRustcVm.wordsAt_cons_iff, NativeRustcVm.wordsAt_cons_iff,
      NativeRustcVm.wordsAt_cons_iff, NativeRustcVm.wordsAt_singleton_iff,
      NativeRustcVm.addr_add_add, NativeRustcVm.addr_add_add]
    rw [NativeRustcVm.addr_add_zero] at w0
    refine ⟨?_, w8, ?_, ?_⟩
    · convert w0 using 1
      rw [show (Sym.load 0 0 8).eval (Env.ofMachine m [(base m0 176, 176), (outO m0, 32)]) =
        Env.load _ 0 0 8 from rfl, load_word (by rw [hb0]; exact h0)]
    · convert w16 using 1
      simp only [Array.size_map]
      exact ((congrArg UInt64.ofBitVec (show (Sym.reg .X23).eval _ =
        (m.regs.getXReg .X23).toBitVec from rfl)).trans (by rw [h23])).symm
    · convert w24 using 1
      exact ((congrArg UInt64.ofBitVec (show (Sym.reg .X21).eval _ =
        (m.regs.getXReg .X21).toBitVec from rfl)).trans (by rw [h21])).symm
  · simp only [Array.size_map] at hj
    obtain ⟨hl, hws⟩ := hleaf j hj
    simp only [Array.getElem_map]
    refine ⟨hl, NativeRustcVm.BytesAt.of_sameOutside hws hs fun i hi hq ↦ ?_⟩
    rw [NativeRustcVm.length_wordsBytes, Array.length_toList, hl] at hi
    have e : (off (off (phO m0) 24) (8 * (1 + j * openingWords)) + BitVec.ofNat 64 i).toNat =
        (phO m0).toNat + (24 + 8 * (1 + j * openingWords) + i) := by
      rw [off_off, off, NativeRustcVm.addr_add_add,
        NativeRustcVm.toNat_add_ofNat (by rw [how]; omega)]
    rw [Sym.inRange_iff hnwo, e] at hq
    unfold Apart at hop
    have hop' : (outO m0).toNat + 32 ≤ (phO m0).toNat ∨
        (phO m0).toNat + 8 * 49411 ≤ (outO m0).toNat := hop
    rw [how] at e hq
    simp only [outO, phO] at hq hop' hnwp'
    omega

end

end NativeRustcVmArm.Sumcheck.OpenPhase
