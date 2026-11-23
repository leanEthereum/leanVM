module

public import NativeRustcVmX64.Wire.Decode.Stream
public import NativeRustcVmX64.Code.Vm.Decode.Names
public import NativeRustcVmX64.Code.Vm.ReaderLe.Names
public import NativeRustcVmX64.Code.Vm.ReaderWords.Names

/-!
# `decode`: the phase count stored (x86-64)

`room_run`: from the room's check (`At7`, `b7`: the stream's end is always within the area's
words), the phase count stored at word `streamEnd L` and the loop's registers (`b8`: R13 below
phase `0`'s words, R14 `b8`'s quotient, at least `9`), to the loop's head. `stream_run`: from
`Reader::words`' call to the head.
-/

namespace NativeRustcVmX64.Wire.Decode

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVm.Wire NativeVm NativeVm.Wire
open NativeRustcVmX64.Vm.Decode
open NativeRustcVmX64.Transcript (Frame frameEnv frame_wf frame_mapped frame_noWrap Frame.of_block
  after after_eq eval_ptr0 wordAt_write mapped_off)
open NativeRustcVm.Transcript (off off_zero off_off toNat_off Mapped.keeps)
open NativeRustcVmX64.Wire.PhaseM (wordAt_keep wordsAt_keep reader_keep iv_of_inRange)
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

public section

variable {m0 : MachineData} [Host] {k : Nat}

/-- **The phase count stored**, from the room's check to the loop's head. -/
theorem room_run (hp : Placed code k) (G : Geo m0) {n : Nat} {ws : List K} {p : Nat}
    {st : MachineState} (h : At7 m0 k n ws p st) :
    Eventually (step1 Host.exe) (fun st' ↦ Head m0 k n ws p 0 [] (8 + 16 * n) st') st := by
  obtain ⟨hpc6', hb6, h1, hw, hv5, hp8, hfit, hwsl, hpos, hcnt6, hws6, hR6, hp6, h13, h14⟩ := h
  have hst := G.st
  have hsp := G.sp
  have htop := G.top
  have hlen := G.len
  rw [decodedWords_eq] at hlen
  have hdn := G.dNw
  have hwn := G.wNw
  have hbn := G.bNw
  have hsD := G.sD
  have hsB := G.sB (by omega)
  have hbD := G.bD (by omega)
  have hS := stackBelow_toNat (m := m0) (n := 80) (by omega)
  have hr := G.fr (j := 8) (by omega)
  have hr' : (rdA m0).toNat = SP0 m0 - 72 := by rw [hr]; omega
  -- `b7`: the stream's end against the area's words (always within).
  refine fblk hp G b7_in_code (by simp [b7]) exit_b7 nofun ok_b7.1 (ok_b7.2.2 .rbx (by simp))
    (ok_b7.2.2 .r15 (by simp)) hpc6' hb6
    fun s7 hb7 hd7 hm7 hpc7 ↦ ?_
  have rk7 : ∀ x ∈ [Reg64.rdx, .rbx, .r12, .r13, .r14, .r15], reg s7.data x = reg st.data x :=
    fun x hx ↦ hm7.regs x _ (ok_b7.2.2 x hx)
  have h15 : reg st.data .r15 = reg m0 .rsi := hb6.r15
  have hax7 : (reg s7.data .rax).toNat = streamEnd (LN m0) := by
    rw [show reg s7.data .rax = _ from hm7.regs .rax _ ok_b7.2.1]
    simp only [Sym.eval, Env.ofMachine_regs]
    rw [show st.data.regs.get64 .r15 = reg m0 .rsi from h15]
    exact se_eval _
  have h14_6 : reg st.data .r14 = reg m0 .rcx := h14
  have h13_6 : reg st.data .r13 = DEC m0 := h13
  have hse := streamEnd_eq (LN m0)
  have hpc7' : s7.pc = if (SBool.cmp .ult .W64 (.bin .or .W64 (.bin .shr .W64 (.reg .r15) (.lit 3))
      (.lit 1)) (.reg .r14)).not.eval (frameEnv m0 st.data 80 []) = true
      then Labels.label NativeRustcVmX64.Vm.Decode.label_9 else Host.addrOf (k + NativeRustcVmX64.Vm.Decode.b7Offset + b7.length) := hpc7
  rw [b7_eval, show (frameEnv m0 st.data 80 []).regs .r15 = reg m0 .rsi from h15,
    show (frameEnv m0 st.data 80 []).regs .r14 = reg m0 .rcx from h14_6,
    decide_eq_true (show streamEnd (LN m0) < LEN m0 by omega)] at hpc7'
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc7'
  -- `b8`: the phase count stored, the loop's registers.
  have hseL : 8 * streamEnd (LN m0) + 8 ≤ 8 * LEN m0 := by omega
  have hpw := G.wd (i := streamEnd (LN m0)) (by omega)
  have hwf8 := frame_wf (m0 := m0) (d := s7.data) (F := 80)
    (rest := [(wd m0 (streamEnd (LN m0)), 8)]) (vars := fun _ ↦ 0) (ret := 0)
    ⟨Mapped.keeps (frame_mapped hst (by omega)) hb7.fr.kept, frame_noWrap hst (by omega)⟩
    (fun x hx ↦ by
      rw [List.mem_singleton] at hx; subst hx
      have hdm : NativeRustcVm.Mapped m0.dmem (DEC m0) (8 * LEN m0) := G.dOk.1
      exact ⟨mapped_off (Mapped.keeps hdm hb7.fr.kept) hseL,
        show (wd m0 (streamEnd (LN m0))).toNat + 8 ≤ 2 ^ 64 by omega⟩)
    (List.pairwise_pair.mpr (by
      show NativeRustcVm.Apart (stackBelow m0 80) (80 + 8) (wd m0 (streamEnd (LN m0))) 8
      unfold NativeRustcVm.Apart; rw [hS, hpw]; omega))
  have hm8 : Match (frameEnv m0 s7.data 80 [(wd m0 (streamEnd (LN m0)), 8)]) pcS s7.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hb7.fr.rsp_eval, trivial⟩ trivial trivial
      ⟨by
        show BinOp.apply .add .W64 (reg s7.data .r13) (BinOp.apply .mul .W64 (reg s7.data .rax)
          (BitVec.ofNat 64 8)) = wd m0 (streamEnd (LN m0)) + BitVec.ofInt 64 0
        rw [NativeRustcVmX64.Transcript.ofInt_zero64, BitVec.add_zero, rk7 .r13 (by simp), h13_6]
        exact pc_addr G hax7 (by omega), trivial⟩
  refine exec_at (infix_of b8_in_code (by simp [b8]) hp) exit_b8 hwf8 nofun
    (hpc7'.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.Decode.b7_next)) hm8 fun s8 hm8' hpc8 ↦ ?_
  obtain ⟨hmid8, hmem8, hpw8, hr12_8, hr13_8, hr14_8, hrbp8, hk8⟩ := ok_b8
  have hf8 : Frame m0 80 slots 8 s8.data := Frame.of_block hb7.fr hwf8 hm8' hmid8 slots_le
  have hs8 : NativeRustcVm.SameOutside s7.data.dmem s8.data.dmem (fun q ↦
      (wd m0 (streamEnd (LN m0))).toNat ≤ q.toNat ∧
        q.toNat < (wd m0 (streamEnd (LN m0))).toNat + 8) := fun q hq ↦
    hm8'.get?_mem0 hwf8 fun ⟨w, hw', b, sz, hb, h1', h2'⟩ ↦ hq (by
      rw [hmem8] at hw'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw'
      subst hw'
      dsimp only at h1' h2'
      simp only [Env.ofMachine_regions, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      exact ⟨by omega, by omega⟩)
  have hdx7 : (reg s7.data .rdx).toNat = p := by rw [rk7 .rdx (by simp)]; exact hp6
  have hpc8w : NativeRustcVm.WordAt s8.data.dmem (wd m0 (streamEnd (LN m0))) p.toUInt64 := by
    have := wordAt_write hm8' (r := 1) (o := 0) (b := wd m0 (streamEnd (LN m0))) (sz := 8) rfl
      (by omega) hpw8
    simp only [Sym.eval, Env.ofMachine_regs, off_zero] at this
    rw [show s7.data.regs.get64 .rdx = reg s7.data .rdx from rfl, ofBitVec_eq_toUInt64,
      hdx7] at this
    exact this
  have hs78 : NativeRustcVm.SameOutside st.data.dmem s8.data.dmem (fun q ↦
      (wd m0 (streamEnd (LN m0))).toNat ≤ q.toNat ∧
        q.toNat < (wd m0 (streamEnd (LN m0))).toNat + 8) := by rw [← hd7]; exact hs8
  have hw1 : (wd m0 1).toNat = (DEC m0).toNat + 8 := G.wd (by omega)
  have hw0 : (wd m0 0).toNat = (DEC m0).toNat := by rw [G.wd (by omega)]; rfl
  refine .done _ ⟨?_, ⟨hf8, ?_, ?_, ?_⟩, hpos, ?_, by omega, Nat.zero_le _, rfl,
    ⟨by unfold maxStream; omega, hwsl, ?_, ?_, hpc8w, fun j hj ↦ absurd hj (by simp)⟩, ?_, ?_,
    ?_, ?_, ?_⟩
  · rw [hpc8, Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.Decode.b8_next
  · refine (hb7.chg.trans hs8).mono fun q hq ↦ ?_
    rcases hq with hq | hq
    · exact hq
    · rw [hpw] at hq; exact .inr (.inl (by omega))
  · rw [show reg s8.data .rbx = _ from hm8'.regs .rbx _ (hk8 .rbx (by simp))]; exact hb7.rbx
  · rw [show reg s8.data .r15 = _ from hm8'.regs .r15 _ (hk8 .r15 (by simp))]; exact hb7.r15
  · simp only [decodeM_eq, h1, hw, afterStream, hv5,
      show ¬ wireMaxPhases < p by unfold wireMaxPhases; omega, ↓reduceIte, Nat.sub_zero]
  · -- the count
    refine wordAt_keep hcnt6 hs78 (by rw [hw0]; omega) fun q hq ↦ ?_
    rw [hw0]; rw [hpw] at hq; omega
  · -- the words
    refine wordsAt_keep hws6 hs78 (by rw [hw1, List.length_map, hwsl]; omega) fun q hq ↦ ?_
    rw [hw1, List.length_map, hwsl]
    rw [hpw] at hq
    omega
  · -- the reader
    refine reader_keep (hR6) hs78 (fun q hq ↦ by rw [hr']; rw [hpw] at hq; omega)
      (fun q hq ↦ by rw [length_Bs]; rw [hpw] at hq; omega)
  · rw [show reg s8.data .r12 = _ from hm8'.regs .r12 _ hr12_8]; exact hdx7
  · rw [show reg s8.data .rbp = _ from hm8'.regs .rbp _ hrbp8]; rfl
  · rw [show reg s8.data .r13 = _ from hm8'.regs .r13 _ hr13_8]
    simp only [Sym.eval, Env.ofMachine_regs]
    rw [show s7.data.regs.get64 .r13 = DEC m0 by rw [← h13_6]; exact rk7 .r13 (by simp),
      r13_eq _ _ _ hax7, phaseBase_eq]
    rw [show 2 * (LN m0 / 16) + 2 + 0 * 49411 = streamEnd (LN m0) + 1 by rw [hse]]
  · rw [show reg s8.data .r14 = _ from hm8'.regs .r14 _ hr14_8]
    refine quot_ge _ ?_
    show (reg s7.data .rax).toNat + 1 + 395288 ≤ (reg s7.data .r14).toNat
    rw [hax7, rk7 .r14 (by simp), h14_6]
    omega

/-- **The stream and the phase count**, from `Reader::words`' call to the loop's head. -/
theorem stream_run (hp : Placed code k) (G : Geo m0)
    (hle : Spec (Labels.label NativeRustcVmX64.Vm.ReaderLe.entryLabel) ReaderLePre ReaderLePost)
    (hrw : Spec (Labels.label NativeRustcVmX64.Vm.ReaderWords.entryLabel) ReaderWordsPre ReaderWordsPost) {n : Nat}
    {st : MachineState} (h : At3 m0 k n st) :
    Eventually (step1 Host.exe) (fun st' ↦ Post m0 st' ∨
      ∃ ws p, Head m0 k n ws p 0 [] (8 + 16 * n) st') st := by
  refine Eventually.bind (words_run hp G hrw h) fun s1 h1 ↦ ?_
  rcases h1 with h1 | ⟨ws, h1⟩
  · exact .done _ (.inl h1)
  refine Eventually.bind (count_run hp G hle h1) fun s2 h2 ↦ ?_
  rcases h2 with h2 | ⟨p, h2⟩
  · exact .done _ (.inl h2)
  exact Eventually.mono (room_run hp G h2) fun _ h ↦ .inr ⟨ws, p, h⟩

end

end NativeRustcVmX64.Wire.Decode
