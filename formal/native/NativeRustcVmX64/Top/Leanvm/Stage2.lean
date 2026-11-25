module

public import NativeRustcVmX64.Top.Leanvm.Exit
public import NativeRustcVmX64.Code.Vm.Decode.Names

/-!
# `leanvm_verify`: the decoder (x86-64)

`stage2`: from `C1`, `b8` tests `L`: when zero, `b14` stores the public input and calls `decode`
with a dangling pointer (`1`) and `b15` returns `0` when it refuses; else `b9` tests the wire's
address (nonzero, `Aligned`), `b10` stores the public input and calls `decode` on the wire, and
`b11` returns `0` (`b12`) when it refuses. Either way, when the decoder accepts, the machine
reaches `NativeRustcVmX64.Vm.LeanvmVerify.label_16` in `AD`.
-/

namespace NativeRustcVmX64.Top.Leanvm

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.LeanvmVerify NativeRustcVmX64.Transcript
open NativeRustcVmX64.Top NativeVm NativeVm.Wire NativeRustcVm.Wire NativeRustcVm.Transcript
open NativeRustcVm.Top (workAreaBytes usedRegions ApartFrom Aligned)

public section

variable [Labels] in
/-- A register a block keeps. -/
theorem keep_of_all {env : NativeRustcX64.Sym.Env} {S : SState} {d : MachineData} (hm : Match env S d)
    {rs : List Reg64} (h : rs.all (fun r ↦ S.reg r == some (.reg r)) = true) {r : Reg64}
    (hr : r ∈ rs) : reg d r = env.regs r :=
  hm.regs r (.reg r) (by simpa using List.all_eq_true.mp h r hr)

/-- The registers the check blocks keep. -/
abbrev kept11 : List Reg64 := [.rax, .rbp, .r8, .rsi, .rdx, .rcx, .r12, .r13, .rbx, .r14, .r15]

variable [Labels] in
/-- `C1` through a block without writes keeping its registers. -/
theorem C1.block {a : NativeVm.Entry.Areas} {bytes : List UInt8} {bytecode : List UInt64}
    {pub : Vector UInt64 4} {m0 d d' : MachineData} {S : SState} (hC : C1 a bytes bytecode pub m0 d)
    (hwf : (frameEnv m0 d 112 [] (fun _ ↦ 0) 0).WF)
    (hm : Match (frameEnv m0 d 112 [] (fun _ ↦ 0) 0) S d') (hmid : MidOk 112 8 slots S = true)
    (hmem : S.mem = []) (hk : kept11.all (fun r ↦ S.reg r == some (.reg r)) = true) :
    C1 a bytes bytecode pub m0 d' :=
  ⟨Frame.of_block hC.frame hwf hm hmid slots_le, by rw [hm.dmem_eq hwf hmem]; exact hC.same,
    (keep_of_all hm hk (by simp)).trans hC.rax, (keep_of_all hm hk (by simp)).trans hC.rbx,
    (keep_of_all hm hk (by simp)).trans hC.rbp, (keep_of_all hm hk (by simp)).trans hC.r8,
    (keep_of_all hm hk (by simp)).trans hC.rsi, (keep_of_all hm hk (by simp)).trans hC.rdx,
    (keep_of_all hm hk (by simp)).trans hC.rcx, (keep_of_all hm hk (by simp)).trans hC.r12,
    (keep_of_all hm hk (by simp)).trans hC.r13, (keep_of_all hm hk (by simp)).trans hC.r14,
    (keep_of_all hm hk (by simp)).trans hC.r15⟩

variable [Labels] in
/-- The public input a block stored at the frame's bytes 8 to 39. -/
theorem pub_stored {m0 d d' : MachineData} {S : SState} {pub : Vector UInt64 4} {ret : BitVec 64}
    (hm : Match (frameEnv m0 d 112 [] (fun _ ↦ 0) ret) S d')
    (h0 : ∀ j < 8, findWrite 0 (8 + j) S.mem = some (.reg .r8, j))
    (h1 : ∀ j < 8, findWrite 0 (16 + j) S.mem = some (.reg .rsi, j))
    (h2 : ∀ j < 8, findWrite 0 (24 + j) S.mem = some (.reg .rdx, j))
    (h3 : ∀ j < 8, findWrite 0 (32 + j) S.mem = some (.reg .rcx, j))
    (e0 : reg d .r8 = pub[0].toBitVec) (e1 : reg d .rsi = pub[1].toBitVec)
    (e2 : reg d .rdx = pub[2].toBitVec) (e3 : reg d .rcx = pub[3].toBitVec) :
    NativeRustcVm.WordsAt d'.dmem (off (stackBelow m0 112) 8) pub.toList := by
  have w : ∀ (o : Nat) (r : Reg64) (v : UInt64), o + 8 ≤ 120 →
      (∀ j < 8, findWrite 0 (o + j) S.mem = some (.reg r, j)) → reg d r = v.toBitVec →
      NativeRustcVm.WordAt d'.dmem (off (stackBelow m0 112) o) v := fun o r v ho hw hr ↦ by
    have := wordAt_write (r := 0) (b := stackBelow m0 112) (sz := 120) hm rfl ho hw
    rwa [show (Sym.reg r).eval (frameEnv m0 d 112 [] (fun _ ↦ 0) ret) = reg d r from rfl, hr,
      UInt64.ofBitVec_toBitVec] at this
  refine wordsAt_iff.mpr fun i hi ↦ ?_
  have hi4 : i < 4 := by simpa using hi
  rw [off_off]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
  · exact w 8 .r8 _ (by decide) h0 (by simpa using e0)
  · exact w 16 .rsi _ (by decide) h1 (by simpa using e1)
  · exact w 24 .rdx _ (by decide) h2 (by simpa using e2)
  · exact w 32 .rcx _ (by decide) h3 (by simpa using e3)

/-- The stage's end: refused (RAX `0`, returned) or accepted at `NativeRustcVmX64.Vm.LeanvmVerify.label_16`. -/
@[expose] def Stage2End [Host] (a : NativeVm.Entry.Areas) (bytes : List UInt8) (bytecode : List UInt64)
    (pub : Vector UInt64 4) (m0 : MachineData) (k : Nat) (st : MachineState) : Prop :=
  (decodeM bytes = none ∧ st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧
    reg st.data .rax = 0#64 ∧ NativeRustcVm.SameOutside m0.dmem st.data.dmem (Out m0 a bytes.length) ∧
    Saved m0 st.data) ∨
  (∃ r, decodeM bytes = some r ∧ st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.LeanvmVerify.b16Offset) ∧ AD a bytes bytecode pub m0 st.data ∧
    DecodedAt st.data.dmem ⟨a.decoded.toBitVec, decodedWords bytes.length, bytes.length⟩
      (streamW r.1) (openingsW r.2))

variable [Host] {k : Nat}

/-- **The decoder.** -/
theorem stage2 (hp : Placed code k) (hdec : Spec (Labels.label NativeRustcVmX64.Vm.Decode.entryLabel) DecodePre DecodePost)
    {a : NativeVm.Entry.Areas} {bytes : List UInt8} {bytecode : List UInt64} {pub : Vector UInt64 4}
    {m0 : MachineData} (hpre : LeanvmVerifyPre a bytes bytecode pub m0) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.LeanvmVerify.b8Offset)) (hC : C1 a bytes bytecode pub m0 st.data) :
    Eventually (step1 Host.exe) (Stage2End a bytes bytecode pub m0 k) st := by
  have g := geo_of hpre
  have hpre' := hpre
  obtain ⟨hst, -, hin, hal, -, -⟩ := hpre'
  have hfnw := frame_noWrap (F := 112) hst (by decide)
  have hFm : ∀ d : MachineData, Kept m0.dmem d.dmem →
      NativeRustcVm.Mapped d.dmem (stackBelow m0 112) (112 + 8) :=
    fun d hk ↦ Mapped.keeps (frame_mapped hst (by decide)) hk
  have hL := hin.L32
  have hdw : decodedWords bytes.length < 2 ^ 64 := by have := g.decN; omega
  -- the frame's environment
  have envOk : ∀ (d : MachineData) {ret : BitVec 64}, Frame m0 112 slots 8 d →
      (frameEnv m0 d 112 [] (fun _ ↦ 0) ret).WF ∧
        Match (frameEnv m0 d 112 [] (fun _ ↦ 0) ret) bodyS d :=
    fun d _ hf ↦ ⟨frame_wf ⟨hFm _ hf.kept, hfnw⟩ (by simp) (List.pairwise_singleton _ _),
      match_ofMachine ⟨rfl, trivial⟩ ⟨hf.rsp_eval, trivial⟩ trivial trivial trivial⟩
  -- `AD` through a block without writes keeping the callee-saved registers
  have adBlock : ∀ {d d' : MachineData} {S : SState}, AD a bytes bytecode pub m0 d →
      Match (frameEnv m0 d 112 [] (fun _ ↦ 0) 0) S d' → MidOk 112 8 slots S = true → S.mem = [] →
      [Reg64.rbp, .r12, .r13, .rbx, .r14, .r15].all (fun r ↦ S.reg r == some (.reg r)) = true →
      AD a bytes bytecode pub m0 d' ∧ d'.dmem = d.dmem := by
    intro d d' S hA hm hmid hmem hk
    have hwf := (envOk d (ret := 0) hA.frame).1
    have hd := hm.dmem_eq hwf hmem
    exact ⟨⟨Frame.of_block hA.frame hwf hm hmid slots_le, by rw [hd]; exact hA.same,
      (keep_of_all hm hk (by simp)).trans hA.rbx, (keep_of_all hm hk (by simp)).trans hA.rbp,
      (keep_of_all hm hk (by simp)).trans hA.r12, (keep_of_all hm hk (by simp)).trans hA.r13,
      (keep_of_all hm hk (by simp)).trans hA.r14, (keep_of_all hm hk (by simp)).trans hA.r15,
      by rw [hd]; exact hA.pubw⟩, hd⟩
  have hk6 : ∀ {S : SState}, kept11.all (fun r ↦ S.reg r == some (.reg r)) = true →
      [Reg64.rbp, .r12, .r13, .rbx, .r14, .r15].all (fun r ↦ S.reg r == some (.reg r)) = true := by
    intro S h
    simp only [kept11, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h ⊢
    tauto
  -- `b8`: `L` tested.
  obtain ⟨hwf8, hm8⟩ := envOk _ (ret := 0) hC.frame
  refine exec_at (infix_of b8_in_code (by simp [b8]) hp) run_b8 hwf8 nofun hpc hm8
    fun st9 hm9 hpc9 ↦ ?_
  obtain ⟨hmid9, hmem9, hk9⟩ := after_eq run_b8 ▸ ok_b8
  have hC9 := C1.block hC hwf8 hm9 hmid9 hmem9 hk9
  simp only [PcOk] at hpc9
  rw [cond_zero _ hC.rbx] at hpc9
  rcases Nat.eq_zero_or_pos bytes.length with hL0 | hL0
  · -- `L = 0`: `b14`, `decode` on a dangling pointer, `b15`.
    rw [hL0] at hpc9
    simp only [show (BitVec.ofNat 64 0 == 0) = true from rfl, ↓reduceIte] at hpc9
    obtain ⟨hwf14, hm14⟩ := envOk _ (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.LeanvmVerify.b14Offset + b14.length)).toBitVec) hC9.frame
    refine exec_at (infix_of b14_in_code (by simp [b14]) hp) run_b14 hwf14 (fun _ _ ↦ rfl)
      (hpc9.trans (lbl_15 hp)) hm14 fun st15 hm15 hpc15 ↦ ?_
    obtain ⟨hmid15, hw15, h0, h1, h2, h3, hrdi, hrsi, hrdx, hrcx, hr8, hk15⟩ :=
      after_eq run_b14 ▸ ok_b14
    have hf15 : Frame m0 112 slots 0 st15.data := Frame.of_block hC9.frame hwf14 hm15 hmid15 slots_le
    have hs15 : NativeRustcVm.SameOutside m0.dmem st15.data.dmem
        (NativeRustcVm.InRange (stackBelow m0 112) 112) := by
      have := sameOutside_low hwf14 hm15 (r := 0) rfl (by decide) hw15
      intro q hq
      rw [this q fun h ↦ hq (inRange_mono h (by decide))]
      exact hC9.same q hq
    refine Eventually.bind (decodeCall hdec hpre hpc15 hf15 hs15 (hm15.regs .rdi _ hrdi)
      (Or.inl ⟨hL0, rfl⟩) (by rw [show reg st15.data .rsi = _ from hm15.regs .rsi _ hrsi, hL0]; rfl)
      ((hm15.regs .rdx _ hrdx).trans hC9.r12)
      (by rw [show reg st15.data .rcx = _ from (hm15.regs .rcx _ hrcx).trans hC9.r15, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hdw])
      ((hm15.regs .r8 _ hr8).trans hC9.r13)
      ((keep_of_all hm15 hk15 (by simp)).trans hC9.rbx)
      ((keep_of_all hm15 hk15 (by simp)).trans hC9.rbp)
      ((keep_of_all hm15 hk15 (by simp)).trans hC9.r12)
      ((keep_of_all hm15 hk15 (by simp)).trans hC9.r13)
      ((keep_of_all hm15 hk15 (by simp)).trans hC9.r14)
      ((keep_of_all hm15 hk15 (by simp)).trans hC9.r15)
      (pub_stored hm15 h0 h1 h2 h3 hC9.r8 hC9.rsi hC9.rdx hC9.rcx)) fun st16 ⟨hpc16, hA16, hres⟩ ↦ ?_
    obtain ⟨hwf16, hm16⟩ := envOk _ (ret := 0) hA16.frame
    refine exec_at (infix_of b15_in_code (by simp [b15]) hp) run_b15 hwf16 nofun
      (hpc16.trans (by rw [show k + NativeRustcVmX64.Vm.LeanvmVerify.b14Offset + b14.length = k + NativeRustcVmX64.Vm.LeanvmVerify.b15Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.LeanvmVerify.b14_next]])) hm16
      fun st17 hm17 hpc17 ↦ ?_
    obtain ⟨hmid17, hmem17, hrax17, hk17⟩ := after_eq run_b15 ▸ ok_b15
    obtain ⟨hA17, hd17⟩ := adBlock hA16 hm17 hmid17 hmem17 hk17
    simp only [PcOk] at hpc17
    have hc : (SBool.cmp .eq .W8 (.bin .and .W8 (.un .trunc .W32 (.reg .rax))
        (.un .trunc .W32 (.reg .rax))) (.lit 0)).eval (frameEnv m0 st16.data 112 [] (fun _ ↦ 0) 0) =
        decide (boolRet st16.data = 0) := by
      simp only [SBool.eval, Sym.eval]
      rw [testAl_eq, trunc32_mod]
      rfl
    rw [hc] at hpc17
    revert hres
    cases hdm : decodeM bytes with
    | none =>
      intro hres
      simp only [hres, decide_true, ↓reduceIte] at hpc17
      refine Eventually.mono (exit13 hp hst (hpc17.trans (lbl_18 hp)) hA17.frame)
        fun s ⟨h1, h2, h3, h4, h5⟩ ↦ Or.inl ⟨hdm, h1, h2, h3.trans (hm17.regs .rax _ hrax17), ?_, h5⟩
      rw [h4]; exact hA17.same
    | some r =>
      rintro ⟨hb, hD⟩
      simp only [hb, show ((1 : Nat) = 0) = False from by decide, decide_false,
        Bool.false_eq_true, ↓reduceIte] at hpc17
      exact .done _ (Or.inr ⟨r, hdm, hpc17.trans (by rw [show k + NativeRustcVmX64.Vm.LeanvmVerify.b15Offset + b15.length = k + NativeRustcVmX64.Vm.LeanvmVerify.b16Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.LeanvmVerify.b15_next]]),
        hA17, by rw [hd17]; exact hD⟩)
  · -- `L > 0`: `b9` (the wire nonzero), `b10`, `decode` on the wire, `b11`.
    have hne : (BitVec.ofNat 64 bytes.length == 0) = false := by
      rw [show (0 : BitVec 64) = BitVec.ofNat 64 0 from rfl,
        ofNat_beq (X := bytes.length) (k := 0) (by omega) (by decide)]
      simpa using (show bytes.length ≠ 0 by omega)
    simp only [hne, Bool.false_eq_true, ↓reduceIte] at hpc9
    obtain ⟨hwf10, hm10⟩ := envOk _ (ret := 0) hC9.frame
    refine exec_at (infix_of b9_in_code (by simp [b9]) hp) run_b9 hwf10 nofun
      (hpc9.trans (by rw [show k + NativeRustcVmX64.Vm.LeanvmVerify.b8Offset + b8.length = k + NativeRustcVmX64.Vm.LeanvmVerify.b9Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.LeanvmVerify.b8_next]])) hm10 fun st11 hm11 hpc11 ↦ ?_
    obtain ⟨hmid11, hmem11, hk11⟩ := after_eq run_b9 ▸ ok_b9
    have hC11 := C1.block hC9 hwf10 hm11 hmid11 hmem11 hk11
    simp only [PcOk] at hpc11
    rw [cond_zero _ hC9.rax] at hpc11
    have hw0 : (a.wire.toBitVec == 0) = false := by
      rw [Bool.eq_false_iff]
      intro h
      exact hal.wire hL0 (UInt64.toBitVec_inj.mp (by simpa using h))
    simp only [hw0, Bool.false_eq_true, ↓reduceIte] at hpc11
    obtain ⟨hwf12, hm12⟩ := envOk _ (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.LeanvmVerify.b10Offset + b10.length)).toBitVec) hC11.frame
    refine exec_at (infix_of b10_in_code (by simp [b10]) hp) run_b10 hwf12 (fun _ _ ↦ rfl)
      (hpc11.trans (by rw [show k + NativeRustcVmX64.Vm.LeanvmVerify.b9Offset + b9.length = k + NativeRustcVmX64.Vm.LeanvmVerify.b10Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.LeanvmVerify.b9_next]])) hm12
      fun st13 hm13 hpc13 ↦ ?_
    obtain ⟨hmid13, hw13, h0, h1, h2, h3, hrdi, hrsi, hrdx, hrcx, hr8, hk13⟩ :=
      after_eq run_b10 ▸ ok_b10
    have hf13 : Frame m0 112 slots 0 st13.data := Frame.of_block hC11.frame hwf12 hm13 hmid13 slots_le
    have hs13 : NativeRustcVm.SameOutside m0.dmem st13.data.dmem
        (NativeRustcVm.InRange (stackBelow m0 112) 112) := by
      have := sameOutside_low hwf12 hm13 (r := 0) rfl (by decide) hw13
      intro q hq
      rw [this q fun h ↦ hq (inRange_mono h (by decide))]
      exact hC11.same q hq
    refine Eventually.bind (decodeCall hdec hpre hpc13 hf13 hs13
      ((hm13.regs .rdi _ hrdi).trans hC11.rax) (Or.inr ⟨hL0, rfl⟩)
      (by rw [show reg st13.data .rsi = _ from (hm13.regs .rsi _ hrsi).trans hC11.rbx,
        BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega)])
      ((hm13.regs .rdx _ hrdx).trans hC11.r12)
      (by rw [show reg st13.data .rcx = _ from (hm13.regs .rcx _ hrcx).trans hC11.r15, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hdw])
      ((hm13.regs .r8 _ hr8).trans hC11.r13)
      ((keep_of_all hm13 hk13 (by simp)).trans hC11.rbx)
      ((keep_of_all hm13 hk13 (by simp)).trans hC11.rbp)
      ((keep_of_all hm13 hk13 (by simp)).trans hC11.r12)
      ((keep_of_all hm13 hk13 (by simp)).trans hC11.r13)
      ((keep_of_all hm13 hk13 (by simp)).trans hC11.r14)
      ((keep_of_all hm13 hk13 (by simp)).trans hC11.r15)
      (pub_stored hm13 h0 h1 h2 h3 hC11.r8 hC11.rsi hC11.rdx hC11.rcx))
      fun st14 ⟨hpc14, hA14, hres⟩ ↦ ?_
    obtain ⟨hwf14, hm14⟩ := envOk _ (ret := 0) hA14.frame
    refine exec_at (infix_of b11_in_code (by simp [b11]) hp) run_b11 hwf14 nofun
      (hpc14.trans (by rw [show k + NativeRustcVmX64.Vm.LeanvmVerify.b10Offset + b10.length = k + NativeRustcVmX64.Vm.LeanvmVerify.b11Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.LeanvmVerify.b10_next]])) hm14
      fun st15 hm15 hpc15 ↦ ?_
    obtain ⟨hmid15, hmem15, hk15⟩ := after_eq run_b11 ▸ ok_b11
    obtain ⟨hA15, hd15⟩ := adBlock hA14 hm15 hmid15 hmem15 (hk6 hk15)
    simp only [PcOk] at hpc15
    have hc : (SBool.cmp .eq .W8 (.bin .and .W8 (.reg .rax) (.reg .rax)) (.lit 0)).not.eval
        (frameEnv m0 st14.data 112 [] (fun _ ↦ 0) 0) = !decide (boolRet st14.data = 0) := by
      simp only [SBool.eval, Sym.eval]
      rw [testAl_eq]
      rfl
    rw [hc] at hpc15
    revert hres
    cases hdm : decodeM bytes with
    | none =>
      intro hres
      simp only [hres, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc15
      refine Eventually.mono (exit12 hp hst (hpc15.trans (by
          rw [show k + NativeRustcVmX64.Vm.LeanvmVerify.b11Offset + b11.length = k + NativeRustcVmX64.Vm.LeanvmVerify.b12Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.LeanvmVerify.b11_next]])) hA15.frame)
        fun s ⟨h1, h2, h3, h4, h5⟩ ↦ Or.inl ⟨hdm, h1, h2, h3, ?_, h5⟩
      rw [h4]; exact hA15.same
    | some r =>
      rintro ⟨hb, hD⟩
      simp only [hb, show ((1 : Nat) = 0) = False from by decide, decide_false, Bool.not_false,
        ↓reduceIte] at hpc15
      exact .done _ (Or.inr ⟨r, hdm, hpc15.trans (lbl_16 hp), hA15, by rw [hd15]; exact hD⟩)

end

end NativeRustcVmX64.Top.Leanvm
