module

public import NativeRustcVmX64.Sumcheck.Climb.Frame
public import NativeRustcVmX64.Code.Vm.HashPair.Names

/-!
# A level of `climb` up to `hash_pair` (x86-64)

From the loop head (`Inv`), `b6` checks the level against the path's slice (never past it, the
height at most `32`), `b7` copies the sibling into the frame and tests the position's low bit;
`b3` (even: the accumulator left) or `b8`, `b11` (odd: right) set `hash_pair`'s arguments and `b4`
calls it (`call_level`): after it, its output is the next accumulator (`head_spec`, `Called`).
-/

namespace NativeRustcVmX64.Sumcheck.Climb

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.Climb NativeRustcVmX64.Transcript
open NativeVm.Model LeanVM.Protocol NativeRustcVm.Sumcheck NativeRustcVm.Transcript

public section

variable {N : Digest} {P : Array Digest} {m0 : MachineData}

section
variable [Labels]

/-- The level's sibling: its words, apart from `climb`'s stack. -/
theorem sib_at (hpre : ClimbPre N P m0) {l : Nat} (hl : l < P.size) {d : Mem 64}
    (hs : NativeRustcVm.SameOutside m0.dmem d
      (NativeRustcVm.InRange (stackBelow m0 climbStack) climbStack)) :
    NativeRustcVm.WordsAt d (off (reg m0 .rcx) (32 * l)) P[l].toList ∧
      NativeRustcVm.NoWrap (off (reg m0 .rcx) (32 * l)) 32 ∧
      NativeRustcVm.Apart (off (reg m0 .rcx) (32 * l)) 32 (stackBelow m0 climbStack)
        (climbStack + 8) := by
  obtain ⟨hst, -, -, hsz, -, hpw, -, hpnw, -, -, -, hpap, -, -⟩ := hpre
  have hnw : (reg m0 .rcx).toNat + 32 * (reg m0 .r8).toNat ≤ 2 ^ 64 := hpnw
  have ho : (off (reg m0 .rcx) (32 * l)).toNat = (reg m0 .rcx).toNat + 32 * l :=
    toNat_off (by omega)
  have hnw' : NativeRustcVm.NoWrap (off (reg m0 .rcx) (32 * l)) 32 := by
    unfold NativeRustcVm.NoWrap; rw [ho]; omega
  have hap : NativeRustcVm.Apart (off (reg m0 .rcx) (32 * l)) 32 (stackBelow m0 climbStack)
      (climbStack + 8) := by
    unfold NativeRustcX64.Apart at hpap; unfold NativeRustcVm.Apart; rw [ho]; omega
  refine ⟨?_, hnw', hap⟩
  have hl4 : (P[l].toList.flatMap NativeRustcVm.wordBytes).length = 32 := by
    rw [NativeRustcVm.length_wordsBytes]; simp
  refine NativeRustcVm.BytesAt.of_sameOutside_apart (wordsAt_path hpw hl) hs
    (by rw [hl4]; unfold NativeRustcVm.Apart at hap ⊢; omega)
    (by rw [hl4]; exact hnw') (stack_noWrap hst)

end

variable [Host] {k : Nat}

/-- The head's environment: the frame, the level's sibling; `hash_pair` returns to `b5`. -/
abbrev headEnv (m0 m : MachineData) (l k : Nat) : Env :=
  frameEnv m0 m 160 [(off (reg m0 .rcx) (32 * l), 32)] (fun _ ↦ 0)
    (Host.addrOf (k + NativeRustcVmX64.Vm.Climb.b4Offset + b4.length)).toBitVec

/-- **The call**: from a level's state at `call hash_pair` (`CallOk`, `hash_pair`'s arguments at
`a`, `b` of the frame, the accumulator's and the sibling's offsets), its return, with its output
`hashPair L R`. -/
theorem call_level (hhp : Spec (Labels.label NativeRustcVmX64.Vm.HashPair.entryLabel) HashPairPre HashPairPost)
    (hpre : ClimbPre N P m0) {l : Nat} {m : MachineData} (hinv : Inv m0 N P l m) {S : SState}
    (hS : CallOk S) {a b : Nat} (ha : S.reg .rsi = some (.ptr 0 a))
    (hb : S.reg .rdx = some (.ptr 0 b)) {L R : Digest}
    (hab : (a = 8 ∧ b = 40 ∧ L = (climbTo N (q0 m0) P l).1 ∧ R = P[l]'hinv.lt) ∨
      (a = 40 ∧ b = 8 ∧ L = P[l]'hinv.lt ∧ R = (climbTo N (q0 m0) P l).1))
    (hwf : (headEnv m0 m l k).WF) {st : MachineState} (hm : Match (headEnv m0 m l k) S st.data)
    (hpc : PcOk (headEnv m0 m l k) (.call NativeRustcVmX64.Vm.HashPair.entryLabel)
      (Host.addrOf (k + NativeRustcVmX64.Vm.Climb.b4Offset + b4.length)) st) :
    Eventually (step1 Host.exe)
      (fun st' ↦ st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.Climb.b5Offset) ∧ Called m0 m (hashPair L R) st'.data) st := by
  have g := Geo.of_pre hpre
  have hst := hpre.1
  have hrc := hpre.2.1
  have hl := hinv.lt
  obtain ⟨hsib, -, -⟩ := sib_at hpre hl hinv.st.same
  obtain ⟨hmid, hrdi, hsw, hws, hr12, hr13, hr14, hr15, hrbp, hrbx⟩ := hS
  have hin := writesIn_of_mid hmid
  have hf : Frame m0 160 slots 0 st.data := Frame.of_block hinv.st.frame hwf hm hmid slots_le
  have hsp : rspOf st.data = fa m0 := by rw [hf.sp, off_zero]
  -- The frame's words at the call.
  have hacc : NativeRustcVm.WordsAt st.data.dmem (off (fa m0) 8)
      (climbTo N (q0 m0) P l).1.toList :=
    keep_frame (bs := ((climbTo N (q0 m0) P l).1.toList.flatMap NativeRustcVm.wordBytes)) hwf hm
      hin (by rw [NativeRustcVm.length_wordsBytes]; simp)
      (fun w hw _ ↦ by
        rw [NativeRustcVm.length_wordsBytes]; simp only [Vector.length_toList]
        rcases (hws w hw).2 with h | h <;> omega)
      hinv.st.acc
  have hsib' : NativeRustcVm.WordsAt st.data.dmem (off (fa m0) 40) (P[l]'hl).toList :=
    wordsAt_written hm (r := 0) rfl (by omega) hsw fun i hi ↦
      load_ofMachine (o := 8 * i) rfl (wordsAt_iff.mp hsib i (by simpa using hi))
  have hout : NativeRustcVm.WordAt st.data.dmem (off (fa m0) 72) (.ofBitVec (reg m0 .rdi)) :=
    keep_frame hwf hm hin (by simp [NativeRustcVm.length_wordBytes])
      (fun w hw _ ↦ by
        simp only [NativeRustcVm.length_wordBytes]
        rcases (hws w hw).2 with h | h <;> omega)
      hinv.st.out
  have hsame : NativeRustcVm.SameOutside m0.dmem st.data.dmem
      (NativeRustcVm.InRange (stackBelow m0 climbStack) climbStack) :=
    SameOutside.mono (hinv.st.same.trans (sameOutside_low hwf hm (r := 0) rfl (hi := 160)
      (by omega) fun w hw ↦ ⟨(hws w hw).1, by rcases (hws w hw).2 with h | h <;> omega⟩))
      fun q hq ↦ by rcases hq with hq | hq; exact hq; exact g.inRange_stack hq
  have hregs : ∀ r, calleeSaved r = true → reg st.data r = reg m r := by
    intro r hr
    cases r <;> simp only [calleeSaved, Bool.false_eq_true] at hr
    · exact (hm.regs .rbx _ hrbx).trans ((eval_ptr0 40).trans hinv.rbx.symm)
    · exact (hm.regs .rbp _ hrbp).trans ((eval_ptr0 8).trans hinv.rbp.symm)
    · exact hm.regs .r12 _ hr12
    · exact hm.regs .r13 _ hr13
    · exact hm.regs .r14 _ hr14
    · exact hm.regs .r15 _ hr15
  -- `hash_pair`'s arguments.
  have hdi : reg st.data .rdi = off (fa m0) 80 := (hm.regs .rdi _ hrdi).trans (eval_ptr0 80)
  have hsi : reg st.data .rsi = off (fa m0) a := (hm.regs .rsi _ ha).trans (eval_ptr0 a)
  have hdx : reg st.data .rdx = off (fa m0) b := (hm.regs .rdx _ hb).trans (eval_ptr0 b)
  have hab' : (a = 8 ∨ a = 40) ∧ (b = 8 ∨ b = 40) := by
    rcases hab with ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩ <;> omega
  have hfm : NativeRustcVm.Mapped st.data.dmem (fa m0) 168 :=
    Mapped.keeps (frame_mapped hst (F := 160) (by rw [climbStack_eq]; omega)) hf.kept
  have hn' : 160 + hashPairStack ≤ climbStack := by rw [climbStack_eq, hashPairStack_eq]
  have hrcap : NativeRustcVm.Apart rcAddr 192 (stackBelow m0 climbStack) (climbStack + 8) :=
    hrc.2.2
  have hpre' : HashPairPre st.data := by
    unfold HashPairPre
    rw [hdi, hsi, hdx]
    refine ⟨stackOk_callee hst hf.kept hsp hn',
      RcAt.callee hrc (rc_keep hsame fun q hq h ↦ ?_) hsp hst.1 hn',
      mapped_off hfm (by omega), g.noWrap (by omega) (by omega),
      mapped_off hfm (by omega), g.noWrap (by omega) (by omega),
      mapped_off hfm (by omega), g.noWrap (by omega) (by omega),
      g.apart_callee hsp (by omega) (by omega), g.apart_callee hsp (by omega) (by omega),
      g.apart_callee hsp (by omega) (by omega),
      Apart.symm' (g.apart_of_stack hrcap (o := 80) (k := 32) (by omega) (by omega)), ?_⟩
    · exact not_inRange_of_apart hrcap hrc.2.1 (noWrap_stackBelow hst) h
        (inRange_mono hq (Nat.le_succ_of_le (by omega)))
    · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hg⟩ := hpre
      refine hg.transport (fun l hl i hi ↦ hsame _ ?_)
        (fun l hl ↦ apart_callee (hg.1 l hl).2.2.1 hsp hst.1 hn') ?_
      · exact not_inRange_of_apart (hg.1 l hl).2.2.1 (hg.1 l hl).2.1
          (noWrap_stackBelow hst) (inRange_off_self hi (by decide)) ∘
          (fun hq ↦ inRange_mono hq (by omega))
      · intro l hl x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · exact g.apart_of_stack (hg.1 l hl).2.2.1 (by omega) (by omega)
        · exact (hg.1 l hl).2.2.2 _ (by simp)
  refine call_then hpc hhp hpre' fun st' hpc' hrsp' ⟨hpost, hso, hsv⟩ ↦ ?_
  rw [hdi] at hpost hso
  rw [hsi, hdx] at hpost
  have hR : ∀ j, 8 ≤ j ∧ j < 80 ∨ 112 ≤ j ∧ j < 168 →
      ¬ (NativeRustcVm.InRange (off (fa m0) 80) 32 (off (fa m0) j) ∨
        NativeRustcVm.InRange (stackBelow st.data hashPairStack) hashPairStack (off (fa m0) j)) :=
    fun j hj ↦ g.notR hsp hj
  have hf' : Frame m0 160 slots 8 st'.data :=
    Frame.call_slots hf hsv hrsp' hso
      (fun p hp i hi ↦ hR _ (by have := slots_le p hp; have := slots_ge p hp; omega))
      (fun j hj ↦ hR _ (by omega))
  refine .done _ ⟨hpc'.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.Climb.b4_next), ⟨hf', ?_, ?_, ?_, ?_⟩⟩
  · rcases hab with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · exact hpost _ _ hacc hsib'
    · exact hpost _ _ hsib' hacc
  · refine NativeRustcVm.BytesAt.of_sameOutside hout hso fun i hi ↦ ?_
    rw [off_add]
    simp only [NativeRustcVm.length_wordBytes] at hi
    exact hR _ (by omega)
  · refine SameOutside.mono (hsame.trans hso) fun q hq ↦ ?_
    rcases hq with hq | hq | hq
    · exact hq
    · exact g.out_in hq
    · exact g.callee_in hsp hq
  · intro r hr
    exact (hsv.1 r hr).trans (hregs r hr)

end

end NativeRustcVmX64.Sumcheck.Climb
