module

public import NativeRustcVmX64.Sumcheck.OpenPhase.Start
public import NativeRustcVmX64.Code.Vm.Climb.Names
public import NativeRustcVmX64.Code.Vm.Keccak256WordsOfHashWords.Names

/-!
# `open_phase`: a climb's leaf hash and path (x86-64)

From the loop head `NativeRustcVmX64.Vm.OpenPhase.label_7` (`CInv`), `b13` (the count against `256`, never there) and
`b14` call `keccak256_words` with `hash_words`' closure on opening `j`'s leaf words: at `b15`, the
hash at the frame's `96` (`Hashed`, `hash_spec`). `b15` calls `climb` on it with opening `j`'s
leaf index and path: at `b16`, the path's top at the frame's `64` (`Climbed`, `path_spec`).
-/

namespace NativeRustcVmX64.Sumcheck.OpenPhase

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.OpenPhase NativeRustcVmX64.Transcript
open NativeRustcVmX64.Sumcheck NativeVm NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVm.Sumcheck LeanVM.Protocol LeanVM.Protocol.Compile

@[expose] public section

/-- At `b15`: opening `j`'s leaf hashed at the frame's `96`, RBX its address. -/
structure Hashed (m0 : MachineData) (P : Array OpeningW) (Q : Array UInt64) (R : Digest)
    (h w j : Nat) (m : MachineData) : Prop where
  inv : CInv m0 P Q R h w j m
  hash : NativeRustcVm.WordsAt m.dmem (off (fa m0) 96) (hashWords (P[j]'inv.lt).leaf).toList
  rbx : reg m .rbx = off (fa m0) 96

/-- At `b16`: opening `j`'s path climbed from its hashed leaf, at the frame's `64`. -/
structure Climbed (m0 : MachineData) (P : Array OpeningW) (Q : Array UInt64) (R : Digest)
    (h w j : Nat) (m : MachineData) : Prop where
  inv : CInv m0 P Q R h w j m
  top : NativeRustcVm.WordsAt m.dmem (off (fa m0) 64)
    (climb (hashWords (P[j]'inv.lt).leaf) (P[j]'inv.lt).leafIndex (P[j]'inv.lt).path).toList

end

public section

variable {m0 m : MachineData} {P : Array OpeningW} {Q : Array UInt64} {R : Digest} {h w j : Nat}

/-- `8 w` as `b14` computes it. -/
theorem eightW_eval [Labels] (env : Env) (hw : (env.regs .r14).toNat ≤ 64) :
    (eightW.eval env).toNat = 8 * (env.regs .r14).toNat := by
  simp only [eightW, Sym.eval, BinOp.apply, low_W64, ext_W64, BitVec.toNat_mul,
    BitVec.toNat_ofNat]
  have := (env.regs .r14).isLt
  omega

/-! ## The phase's bytes -/

section
variable [Labels]

theorem ph_toNat (hpre : OpenPhasePre P R Q m0) {o : Nat} (ho : o < 8 * phaseWords) :
    (off (phO m0) o).toNat = (phO m0).toNat + o := by
  have h : (phO m0).toNat + 8 * phaseWords ≤ 2 ^ 64 := hpre.2.2.2.2.2.2.2.2.1
  exact toNat_off (by omega)

theorem ph_noWrap (hpre : OpenPhasePre P R Q m0) {o n : Nat} (ho : o < 8 * phaseWords)
    (hon : o + n ≤ 8 * phaseWords) : NativeRustcVm.NoWrap (off (phO m0) o) n := by
  have h : (phO m0).toNat + 8 * phaseWords ≤ 2 ^ 64 := hpre.2.2.2.2.2.2.2.2.1
  unfold NativeRustcVm.NoWrap
  rw [ph_toNat hpre ho]
  omega

theorem ph_mapped (hpre : OpenPhasePre P R Q m0) (hk : Kept m0.dmem m.dmem) {o n : Nat}
    (hon : o + n ≤ 8 * phaseWords) : NativeRustcVm.Mapped m.dmem (off (phO m0) o) n :=
  mapped_off (Mapped.keeps hpre.2.2.2.2.2.2.2.1 hk) hon

theorem ph_apart (hpre : OpenPhasePre P R Q m0) {o n : Nat} (ho : o < 8 * phaseWords)
    (hon : o + n ≤ 8 * phaseWords) :
    NativeRustcVm.Apart (off (phO m0) o) n (stackBelow m0 openPhaseStack) (openPhaseStack + 8) := by
  have h : (phO m0).toNat + 8 * phaseWords ≤ (stackBelow m0 openPhaseStack).toNat ∨
      (stackBelow m0 openPhaseStack).toNat + (openPhaseStack + 8) ≤ (phO m0).toNat :=
    hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold NativeRustcVm.Apart
  rw [ph_toNat hpre ho]
  omega

end

variable [Host] {k : Nat}

/-- **A climb's leaf hash**: from `NativeRustcVmX64.Vm.OpenPhase.label_7`, `b15` with opening `j`'s leaf hashed. -/
theorem hash_spec (hp : Placed code k)
    (hkh : Spec (Labels.label NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.entryLabel) Keccak256WordsHashPre
      Keccak256WordsHashPost)
    (hpre : OpenPhasePre P R Q m0) (hph : PhaseHW m0.dmem (phO m0) P h w)
    (hi : CInv m0 P Q R h w j m) :
    Eventually (step1 Host.exe)
      (fun st ↦ st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.OpenPhase.b15Offset) ∧ Hashed m0 P Q R h w j st.data)
      ⟨m, Host.addrOf (k + NativeRustcVmX64.Vm.OpenPhase.b13Offset)⟩ := by
  have hst := hpre.1
  have hlt := hi.lt
  have hsz : P.size ≤ 256 := hph.2.2.1
  have hw64 : w ≤ 64 := hph.2.1
  have how : openingWords = 193 := rfl
  have hpw : phaseWords = 49411 := rfl
  have ho := hph.2.2.2.2.2.2 j hlt
  -- `b13`: the count is below `256`.
  obtain ⟨hmid13, hmem13, hk13⟩ := ok_b13
  refine frTest hst hi.fr (infix_of b13_in_code (by simp [b13]) hp) exit_b13 nofun hmid13 hmem13
    hk13 fun st1 hf1 hd1 hkr1 hm1 hpc1 ↦ ?_
  have hc13 : c13.eval (frameEnv m0 m 176 [] (fun _ ↦ 0) 0) = false := by
    simp only [c13, SBool.eval, Sym.eval, CmpOp.apply, low_W64, Env.ofMachine_regs]
    rw [beq_eq_false_iff_ne]
    intro e
    have := congrArg BitVec.toNat e
    rw [show (m.regs.get64 .r12).toNat = j from hi.r12] at this
    simp at this
    omega
  simp only [PcOk, hc13, Bool.false_eq_true, ↓reduceIte] at hpc1
  have hi1 := hi.keep hf1 (fun r hr ↦ hkr1 r (by rcases hr with h | h | h | h | h <;> subst h <;>
    decide) rfl) (fun j _ _ ↦ by rw [hd1])
  obtain ⟨d1, pc1⟩ := st1
  have hpc1' : pc1 = Host.addrOf (k + NativeRustcVmX64.Vm.OpenPhase.b14Offset) := hpc1.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.OpenPhase.b13_next)
  subst hpc1'
  -- `b14`: the call's arguments.
  have hwf := wf0 hst hi1.fr (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.OpenPhase.b14Offset + b14.length)).toBitVec)
  refine exec_then (infix_of b14_in_code (by simp [b14]) hp) exit_b14 hwf (fun _ _ ↦ rfl)
    (match_ofMachine ⟨rfl, trivial⟩ ⟨hi1.fr.frame.rsp_eval, trivial⟩ trivial trivial trivial)
    fun st2 hm2 hpc2 ↦ ?_
  obtain ⟨hmid2, hW2, hdi2, hbx2, hsi2, hdx2, hcx2, hr82, hkb2⟩ := ok_b14
  have hf2 : FrO m0 0 st2.data :=
    FrO.block hst hi1.fr hwf hm2 hmid2 fun w hw ↦ ⟨(hW2 w hw).1, by have := (hW2 w hw).2; omega⟩
  have hl2 : LowKept m0 d1 st2.data :=
    lowKept_block hwf hm2 (writesIn_of_mid hmid2) fun w hw _ ↦ by have := (hW2 w hw).2; omega
  have hsp2 : rspOf st2.data = fa m0 := by rw [hf2.frame.sp, off_zero]
  have hk2 : ∀ r, r ≠ .rsp → [Reg64.rbx, .rcx, .rdx, .rsi, .rdi, .r8].contains r = false →
      reg st2.data r = reg d1 r := fun r h1 h2 ↦ KeepBut.regs hkb2 hm2 h1 h2
  have h14 : reg d1 .r14 = w.toUInt64.toBitVec := hi1.r14
  have hwn : (w.toUInt64.toBitVec).toNat = w := toUInt64_toNat (by omega)
  have hdi : reg st2.data .rdi = off (fa m0) 96 := (hm2.regs .rdi _ hdi2).trans (eval_ptr0 96)
  have hbx : reg st2.data .rbx = off (fa m0) 96 := (hm2.regs .rbx _ hbx2).trans (eval_ptr0 96)
  have hsi : reg st2.data .rsi = w.toUInt64.toBitVec := (hm2.regs .rsi _ hsi2).trans h14
  have hr8 : reg st2.data .r8 = w.toUInt64.toBitVec := (hm2.regs .r8 _ hr82).trans h14
  have hdx : (reg st2.data .rdx).toNat = 8 * w := by
    rw [show reg st2.data .rdx = _ from hm2.regs .rdx _ hdx2, eightW_eval _ (by
      show (reg d1 .r14).toNat ≤ 64; rw [h14, hwn]; omega)]
    show 8 * (reg d1 .r14).toNat = _
    rw [h14, hwn]
  have hc0 : 32 + 1544 * j < 8 * phaseWords := by rw [hpw]; omega
  have hcn : 32 + 1544 * j + 8 * w ≤ 8 * phaseWords := by rw [hpw]; omega
  have hcx : reg st2.data .rcx = off (phO m0) (32 + 1544 * j) := by
    rw [show reg st2.data .rcx = _ from hm2.regs .rcx _ hcx2]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
    rw [show d1.regs.get64 .r15 = off (phO m0) (544 + 1544 * j) from hi1.r15]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, ph_toNat hpre (by rw [hpw]; omega), ph_toNat hpre hc0]
    simp only [BitVec.toNat_ofNat, show (2 : Nat) ^ Width.W64.bits = 2 ^ 64 from rfl]
    have hnw : (phO m0).toNat + 8 * phaseWords ≤ 2 ^ 64 := hpre.2.2.2.2.2.2.2.2.1
    omega
  have hkpre : Keccak256WordsHashPre st2.data := by
    simp only [Keccak256WordsHashPre]
    rw [hdi, hsi, hr8, hcx, hwn]
    refine ⟨stackOk_callee hst hf2.frame.kept hsp2 (by decide), rcAt_callee hst hpre.2.1 hf2
      (by decide), rfl, hdx, ph_mapped hpre hf2.frame.kept hcn, ph_noWrap hpre hc0 hcn,
      mapped_off (Mapped.keeps (frame_mapped hst (by decide)) hf2.frame.kept) (by omega),
      fa_noWrap' hst (by omega) (by omega), fun _ ↦ ?_,
      fa_apart_callee hst hsp2 (by decide) (by omega) (by omega), fa_rc hpre.2.1 hst (by omega)
        (by omega), ?_⟩
    · exact apart_callee' hst hsp2 (by decide) (ph_apart hpre hc0 hcn)
    · apply hf2.gotAt hpre (by decide)
      intro l hl x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact got_frame hpre hl (by omega)
      · exact ((got_of hpre).1 l hl).2.2.2 _ (by simp)
  have hleaf : NativeRustcVm.WordsAt st2.data.dmem (off (phO m0) (32 + 1544 * j))
      (P[j]'hlt).leaf.toList := by
    have := ho.2.2.2.2.1
    rw [off_off, show 8 * (3 + j * openingWords) + 8 = 32 + 1544 * j by rw [how]; omega] at this
    exact ph_keep hpre hf2.same hc0
      (by rw [NativeRustcVm.length_wordsBytes, Array.length_toList, ho.1]; omega) this
  refine call_then hpc2 hkh hkpre fun st3 hpc3 hrsp3 ⟨hpost, hs3, hsv3⟩ ↦ ?_
  rw [hdi, hcx, hr8, hwn] at hpost
  rw [hdi] at hs3
  obtain ⟨hf3, hk3⟩ := FrO.call hst hf2 hsv3 hrsp3 (by decide) (o := 96) (by omega) hs3
  have hh := hpost (P[j]'hlt).leaf.toList (by rw [Array.length_toList, ho.1]) hleaf
  refine .done _ ⟨hpc3.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.OpenPhase.b14_next),
    ⟨hi1.keep hf3 (fun r hr ↦ ?_) (hl2.trans (lowKept_call (o := 96) (by omega) hk3)), ?_, ?_⟩⟩
  · exact (hsv3.1 r (by rcases hr with h | h | h | h | h <;> subst h <;> rfl)).trans
      (hk2 r (by rcases hr with h | h | h | h | h <;> subst h <;> decide)
        (by rcases hr with h | h | h | h | h <;> subst h <;> rfl))
  · simpa only [Array.toArray_toList] using hh
  · exact (hsv3.1 .rbx rfl).trans hbx

/-- **A climb's path**: from `b15`, `b16` with opening `j`'s path climbed. -/
theorem path_spec (hp : Placed code k)
    (hcl : ∀ N P, Spec (Labels.label NativeRustcVmX64.Vm.Climb.entryLabel) (ClimbPre N P) (ClimbPost N P))
    (hpre : OpenPhasePre P R Q m0) (hph : PhaseHW m0.dmem (phO m0) P h w)
    (hi : Hashed m0 P Q R h w j m) :
    Eventually (step1 Host.exe)
      (fun st ↦ st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.OpenPhase.b16Offset) ∧ Climbed m0 P Q R h w j st.data)
      ⟨m, Host.addrOf (k + NativeRustcVmX64.Vm.OpenPhase.b15Offset)⟩ := by
  have hst := hpre.1
  have hc := hi.inv
  have hlt := hc.lt
  have ho := hph.2.2.2.2.2.2 j hlt
  have how : openingWords = 193 := rfl
  have hpw : phaseWords = 49411 := rfl
  have hmh : wireMaxHeight = 32 := rfl
  have hml : wireMaxLeafWords = 64 := rfl
  have hsz : P.size ≤ 256 := hph.2.2.1
  have hh32 : h ≤ 32 := hph.1
  -- `b15`: the call's arguments, from the frame and opening `j`'s leaf index.
  have hc24 : 24 + 1544 * j < 8 * phaseWords := by rw [hpw]; omega
  have hidx : NativeRustcVm.WordAt m.dmem (off (phO m0) (24 + 1544 * j)) (P[j]'hlt).leafIndex := by
    have := ho.2.2.2.1
    rw [show 8 * (3 + j * openingWords) = 24 + 1544 * j by rw [how]; omega] at this
    exact ph_word hpre hc.fr.same (by rw [hpw]; omega) this
  have hwf := wf1 hst hc.fr (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.OpenPhase.b15Offset + b15.length)).toBitVec)
    (ph_mapped hpre hc.fr.frame.kept (o := 24 + 1544 * j) (n := 8) (by rw [hpw]; omega))
    (ph_noWrap hpre hc24 (by rw [hpw]; omega)) (ph_apart hpre hc24 (by rw [hpw]; omega))
  have hal : (Sym.reg .r15).eval (frameEnv m0 m 176 [(off (phO m0) (24 + 1544 * j), 8)]
      (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.OpenPhase.b15Offset + b15.length)).toBitVec) =
      (frameEnv m0 m 176 [(off (phO m0) (24 + 1544 * j), 8)] (fun _ ↦ 0)
        (Host.addrOf (k + NativeRustcVmX64.Vm.OpenPhase.b15Offset + b15.length)).toBitVec).base 1 + BitVec.ofInt 64 520 := by
    show reg m .r15 = off (phO m0) (24 + 1544 * j) + BitVec.ofInt 64 520
    rw [hc.r15, show BitVec.ofInt 64 520 = BitVec.ofNat 64 520 from rfl, off_add]
    congr 1
    omega
  refine exec_then (infix_of b15_in_code (by simp [b15]) hp) exit_b15 hwf (fun _ _ ↦ rfl)
    (match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hc.fr.frame.rsp_eval, trivial⟩ trivial trivial
      ⟨hal, trivial⟩) fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hmid1, hW1, hdi1, hsi1, hdx1, hcx1, hr81, hkb1⟩ := ok_b15
  have hf1 : FrO m0 0 st1.data :=
    FrO.block hst hc.fr hwf hm1 hmid1 fun w hw ↦ ⟨(hW1 w hw).1, by have := (hW1 w hw).2; omega⟩
  have hin1 := writesIn_of_mid hmid1
  have hl1 : LowKept m0 m st1.data :=
    lowKept_block hwf hm1 hin1 fun w hw _ ↦ by have := (hW1 w hw).2; omega
  have hsp1 : rspOf st1.data = fa m0 := by rw [hf1.frame.sp, off_zero]
  have hk1 : ∀ r, r ≠ .rsp → [Reg64.rcx, .rdx, .rsi, .rdi, .r8].contains r = false →
      reg st1.data r = reg m r := fun r h1 h2 ↦ KeepBut.regs hkb1 hm1 h1 h2
  have hdi : reg st1.data .rdi = off (fa m0) 64 := (hm1.regs .rdi _ hdi1).trans (eval_ptr0 64)
  have hsi : reg st1.data .rsi = off (fa m0) 96 := (hm1.regs .rsi _ hsi1).trans hi.rbx
  have hdx : reg st1.data .rdx = (P[j]'hlt).leafIndex.toBitVec :=
    (hm1.regs .rdx _ hdx1).trans (load_ofMachine (o := 0) rfl (by rw [off_zero]; exact hidx))
  have hcx : reg st1.data .rcx = off (phO m0) (544 + 1544 * j) :=
    (hm1.regs .rcx _ hcx1).trans hc.r15
  have hr8 : (reg st1.data .r8).toNat = h := by
    rw [show reg st1.data .r8 = _ from hm1.regs .r8 _ hr81]
    show ((frameEnv m0 m 176 [(off (phO m0) (24 + 1544 * j), 8)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.OpenPhase.b15Offset + b15.length)).toBitVec).load 0 56 8).toNat = h
    rw [load_ofMachine (o := 56) rfl hc.w56, toUInt64_toNat (by omega)]
  have hpl : (pathWords (P[j]'hlt).path).length = 4 * h := by
    have hl : ∀ xs : List Digest, (xs.flatMap (·.toList)).length = 4 * xs.length := by
      intro xs
      induction xs with
      | nil => simp
      | cons x xs ih =>
        simp only [List.flatMap_cons, List.length_append, Vector.length_toList, ih,
          List.length_cons]
        omega
    unfold pathWords
    rw [hl, Array.length_toList, ho.2.1]
  have hc544 : 544 + 1544 * j < 8 * phaseWords := by rw [hpw]; omega
  have hcn : 544 + 1544 * j + 32 * h ≤ 8 * phaseWords := by rw [hpw]; omega
  have hpath : NativeRustcVm.WordsAt st1.data.dmem (off (phO m0) (544 + 1544 * j))
      (pathWords (P[j]'hlt).path) := by
    have := ho.2.2.2.2.2
    rw [off_off, show 8 * (3 + j * openingWords) + 8 * (1 + wireMaxLeafWords) =
      544 + 1544 * j by rw [how, hml]; omega] at this
    exact ph_keep hpre hf1.same hc544 (by rw [NativeRustcVm.length_wordsBytes, hpl]; omega) this
  have hnode : NativeRustcVm.WordsAt st1.data.dmem (off (fa m0) 96)
      (hashWords (P[j]'hlt).leaf).toList :=
    keep_frame hwf hm1 hin1 (by rw [NativeRustcVm.length_wordsBytes]; simp)
      (fun w hw _ ↦ .inl (by have := (hW1 w hw).2; omega)) hi.hash
  have hclpre : ClimbPre (hashWords (P[j]'hlt).leaf) (P[j]'hlt).path st1.data := by
    simp only [ClimbPre]
    rw [hdi, hsi, hcx, hr8]
    refine ⟨stackOk_callee hst hf1.frame.kept hsp1 (by decide), rcAt_callee hst hpre.2.1 hf1
      (by decide), by rw [hmh]; exact hh32, ho.2.1, hnode, hpath,
      fa_noWrap' hst (by omega) (by omega), ph_noWrap hpre hc544 hcn,
      mapped_off (Mapped.keeps (frame_mapped hst (by decide)) hf1.frame.kept) (by omega),
      fa_noWrap' hst (by omega) (by omega),
      fa_apart_callee hst hsp1 (by decide) (by omega) (by omega),
      apart_callee' hst hsp1 (by decide) (ph_apart hpre hc544 hcn),
      fa_apart_callee hst hsp1 (by decide) (by omega) (by omega),
      fa_rc hpre.2.1 hst (by omega) (by omega), ?_⟩
    apply hf1.gotAt hpre (by decide)
    intro l hl x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact got_frame hpre hl (by omega)
    · have ha := ((got_of hpre).1 l hl).2.2.2 (phO m0, 8 * phaseWords) (by simp)
      change (gotAddr l).toNat + 8 ≤ (phO m0).toNat ∨
        (phO m0).toNat + 8 * phaseWords ≤ (gotAddr l).toNat at ha
      change (gotAddr l).toNat + 8 ≤ (off (phO m0) (544 + 1544 * j)).toNat ∨
        (off (phO m0) (544 + 1544 * j)).toNat + 32 * h ≤ (gotAddr l).toNat
      rw [ph_toNat hpre hc544]
      omega
    · exact got_frame hpre hl (by omega)
    · exact ((got_of hpre).1 l hl).2.2.2 _ (by simp)
  refine call_then hpc1 (hcl _ _) hclpre fun st2 hpc2 hrsp2 ⟨hpost, hs2, hsv2⟩ ↦ ?_
  rw [hdi, hdx] at hpost
  rw [hdi] at hs2
  obtain ⟨hf2, hk2⟩ := FrO.call hst hf1 hsv2 hrsp2 (by decide) (o := 64) (by omega) hs2
  refine .done _ ⟨hpc2.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.OpenPhase.b15_next),
    ⟨hc.keep hf2 (fun r hr ↦ ?_) (hl1.trans (lowKept_call (o := 64) (by omega) hk2)), hpost⟩⟩
  exact (hsv2.1 r (by rcases hr with h | h | h | h | h <;> subst h <;> rfl)).trans
    (hk1 r (by rcases hr with h | h | h | h | h <;> subst h <;> decide)
      (by rcases hr with h | h | h | h | h <;> subst h <;> rfl))

end

end NativeRustcVmX64.Sumcheck.OpenPhase
