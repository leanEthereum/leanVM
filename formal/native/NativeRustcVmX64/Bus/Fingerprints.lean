module

public import NativeRustcVmX64.Bus.Fingerprints.Exec
public import NativeRustcVmX64.Bus.Common
public import NativeRustcVmX64.Code.Vm.Dot.Names
public import NativeRustcVmX64.Code.Vm.Fingerprints.Names
public import NativeRustcVmX64.Code.Vm.IndexMleFrom.Names
public import NativeRustcVmX64.Code.Vm.Kpow.Names

/-!
# `fingerprints` on x86-64

`b0` pushes the callee-saved registers, keeps the arguments in them (R9 in the frame), and calls
`kpow(0)`; then three fingerprints, each a `dot` of the first weights with an array the function
builds in its frame (`b1` at offset `32`, `b3` at `128` with `memory`, `b6` at `80`), around
`kpow(2)` and `index_mle_from`; `b7` adds the share to the third and writes the three at `out`
(`fingerprints_spec`). The stack arguments are region 1 of the blocks reading them.
-/

namespace NativeRustcVmX64.Bus.Fingerprints

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.Fingerprints
open NativeRustcVmX64.Transcript NativeVm.Model NativeRustcVm.Transcript NativeRustcVmX64.Bus
open NativeRustcVm (ewsOf wordOf ewOf)

public section

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 256 := by decide

theorem ewsOf_take (d : DataMem) (a : BitVec 64) {k n : Nat} (h : k ≤ n) :
    (ewsOf d a n).take k = ewsOf d a k := by
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  simp

theorem extract_ewsOf (d : DataMem) (a : BitVec 64) {k n : Nat} (h : k ≤ n) :
    (ewsOf d a n).toArray.extract 0 k = (ewsOf d a k).toArray := by
  apply Array.ext'
  simp [ewsOf_take d a h]

theorem stack_eq : fingerprintsStack = 464 := by decide

/-- The first `k` of `n` readable elements apart from the stack, as a slice. -/
theorem sliceOk_prefix {m : MachineData} {a : BitVec 64} {n k s : Nat} (h : EWsOk m a n s)
    (hk : k ≤ n) (hk64 : k < 2 ^ 64) : SliceOk m a (BitVec.ofNat 64 k) s := by
  have hkn : (BitVec.ofNat 64 k).toNat = k := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hk64
  unfold SliceOk
  rw [hkn]
  refine ⟨⟨NativeRustcVm.Mapped.mono h.1.1 (by omega),
    NativeRustcVm.NoWrap.mono h.1.2 (by omega)⟩, ?_⟩
  have h' : NativeRustcVm.Apart a (16 * n) (stackBelow m s) (s + 8) := h.2
  show NativeRustcVm.Apart _ _ _ _
  unfold NativeRustcVm.Apart at h' ⊢
  omega

/-- A slice of three elements of the frame. -/
theorem slice_three {m : MachineData} {a : BitVec 64} {x y z : EW}
    (h : NativeRustcVm.EWsAt m.dmem a [x, y, z]) : slice m a (BitVec.ofNat 64 3) = #[x, y, z] :=
  slice_of_ewsAt h rfl

/-- A slice of five elements of the frame. -/
theorem slice_five {m : MachineData} {a : BitVec 64} {x y z u v : EW}
    (h : NativeRustcVm.EWsAt m.dmem a [x, y, z, u, v]) :
    slice m a (BitVec.ofNat 64 5) = #[x, y, z, u, v] :=
  slice_of_ewsAt h rfl

theorem slice_weights (d : MachineData) (a : BitVec 64) (n : Nat) (h : n < 2 ^ 64) :
    slice d a (BitVec.ofNat 64 n) = (ewsOf d.dmem a n).toArray := by
  unfold slice
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem xor_apply (a b : BitVec 64) : BinOp.xor.apply .W64 a b = a ^^^ b := by
  simp only [BinOp.apply, low_W64, ext_W64]

variable [Host] {k : Nat}

/-- **`fingerprints`' contract.** -/
theorem fingerprints_spec (hp : Placed code k)
    (hkpow : Spec (Labels.label NativeRustcVmX64.Vm.Kpow.entryLabel) KpowPre KpowPost)
    (hdot : Spec (Labels.label NativeRustcVmX64.Vm.Dot.entryLabel) DotPre DotPost)
    (himf : Spec (Labels.label NativeRustcVmX64.Vm.IndexMleFrom.entryLabel) IndexMleFromPre IndexMleFromPost) :
    Spec (Labels.label NativeRustcVmX64.Vm.Fingerprints.entryLabel) FingerprintsPre FingerprintsPost := by
  rintro m0 ⟨hst, hargs, hW, hM, hML, hBL, hOR, hOS⟩
  have hF : 256 ≤ fingerprintsStack := by rw [stack_eq]; omega
  have hlk : 256 + kpowStack ≤ fingerprintsStack := by decide
  have hld : 256 + dotStack ≤ fingerprintsStack := by decide
  have hli : 256 + indexMleFromStack ≤ fingerprintsStack := by decide
  have hW3 : SliceOk m0 (reg m0 .rsi) (BitVec.ofNat 64 3) fingerprintsStack :=
    sliceOk_prefix hW (by omega) (by omega)
  have hW5 : SliceOk m0 (reg m0 .rsi) (BitVec.ofNat 64 5) fingerprintsStack :=
    sliceOk_prefix hW (by omega) (by omega)
  have AL : ∀ (d : MachineData), NativeRustcVm.SameOutside m0.dmem d.dmem
      (NativeRustcVm.InRange (stackBelow m0 fingerprintsStack) fingerprintsStack) →
      ∀ (i : Nat), i < 8 → ∀ (ret : BitVec 64),
        (frameEnv m0 d 256 [(rspOf m0 + 8#64, 8 * 8)] (fun _ ↦ 0) ret).load 1 (8 * i) 8 =
          stackArg m0 i :=
    fun _ hs _ hi _ ↦ load_arg hst hargs hs hi
  have ALI : ∀ (d : MachineData) (ret : BitVec 64), AllOf (fun p ↦ p.1.eval
      (frameEnv m0 d 256 [(rspOf m0 + 8#64, 8 * 8)] (fun _ ↦ 0) ret) =
        (frameEnv m0 d 256 [(rspOf m0 + 8#64, 8 * 8)] (fun _ ↦ 0) ret).base p.2.1 +
          BitVec.ofInt 64 p.2.2) argAliases := fun _ _ ↦
    ⟨alias_arg 0, alias_arg 1, alias_arg 2, alias_arg 3, alias_arg 4, alias_arg 5, alias_arg 6,
      alias_arg 7, trivial⟩
  -- `b0`: the prologue, the arguments kept, `kpow(0)`.
  have hwf0 := wf_args (d := m0) hst hF (fun _ h ↦ h) hargs (by decide) (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.Fingerprints.b0Offset + b0.length)).toBitVec)
  unfold NativeRustcVmX64.Vm.Fingerprints.entryLabel
  rw [hp.label NativeRustcVmX64.Vm.Fingerprints.entry_at]
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_b0 hwf0 (fun _ _ ↦ rfl)
    (match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨match_rsp, trivial⟩ trivial trivial (ALI m0 _))
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hpro1, hw1, hwr1, hbx1, h14_1, h12_1, h13_1, h15_1, hbp1, hdi1⟩ :=
    after_eq run_b0 ▸ ok_b0
  have hb1 : Body m0 256 fingerprintsStack slots 0 st1.data :=
    Body.of_prologue hst hF hwf0 hm1 hpro1 hw1 slots_le (by decide)
  have e1bx : reg st1.data .rbx = reg m0 .rdi := hm1.regs .rbx _ hbx1
  have e1_14 : reg st1.data .r14 = reg m0 .rsi := hm1.regs .r14 _ h14_1
  have e1_12 : reg st1.data .r12 = reg m0 .rdx := hm1.regs .r12 _ h12_1
  have e1_13 : reg st1.data .r13 = reg m0 .rcx := hm1.regs .r13 _ h13_1
  have e1_15 : reg st1.data .r15 = reg m0 .r8 := hm1.regs .r15 _ h15_1
  have e1bp : reg st1.data .rbp = stackArg m0 3 :=
    (hm1.regs .rbp _ hbp1).trans (AL m0 (fun _ _ ↦ rfl) 3 (by decide) _)
  have e1di : reg st1.data .rdi = 0#64 := hm1.regs .rdi _ hdi1
  have FW1 : FrameWords m0 256 st1.data.dmem [(24, UInt64.ofBitVec (reg m0 .r9))] := by
    intro p hp
    rw [List.mem_singleton] at hp
    subst hp
    exact wordAt_write_eq hm1 (b := stackBelow m0 256) rfl (by omega) (.reg .r9)
      (hwr1.find (by simp)) rfl
  refine call_then hpc1 hkpow (hb1.stackOk hst hlk) fun st2 hpc2 hrsp2 ⟨hk2, hs2, hsv2⟩ ↦ ?_
  have hc2 : Changes st1.data st2.data kpowStack 0 0 :=
    NativeRustcVm.Transcript.SameOutside.mono hs2 fun _ h ↦ Or.inr h
  have hb2 := Body.call hst hF hb1 hlk hsv2 hrsp2 hc2 slots_le
  have FW2 := FrameWords.call hst hb1 hlk hc2 (by simp) FW1
  have e2ax : reg st2.data .rax = (gpowK 0).toBitVec := by rw [hk2, e1di]; rfl
  have e2bp : reg st2.data .rbp = stackArg m0 3 := (hsv2.1 .rbp rfl).trans e1bp
  -- `b1`: `[1, pc, gpow 0]` at offset `32`, `dot` with the first three weights.
  have hwf2 := wf_args (d := st2.data) hst hF hb2.fr.kept hargs (by decide) (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.Fingerprints.b1Offset + b1.length)).toBitVec)
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) run_b1 hwf2 (fun _ _ ↦ rfl)
    (hpc2.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.Fingerprints.b0_next))
    (match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hb2.fr.rsp_eval, trivial⟩ trivial trivial (ALI _ _))
    fun st3 hm3 hpc3 ↦ ?_
  obtain ⟨hmid3, hw3, hwr3, hbd3, hk3, hdi3, hsi3, hdx3, hcx3⟩ := after_eq run_b1 ▸ ok_b1
  have hb3 := Body.of_block hst hF hb2 hwf2 hm3 hmid3 hw3 slots_le
  have FW3 := FrameWords.block hwf2 hm3 (writesIn_of_mid hmid3) (by simp)
    (fun p hp w hw _ ↦ by
      rw [List.mem_singleton] at hp; subst hp; rcases hbd3 w hw with h | h <;> omega) FW2
  have hA1 : NativeRustcVm.EWsAt st3.data.dmem (off (stackBelow m0 256) 32)
      [sepStateW, EW.ofK (UInt64.ofBitVec (stackArg m0 3)), gpow 0] := by
    refine ewsAt_words fun i hi ↦ ?_
    match i, hi with
    | 0, _ =>
      exact ⟨wordAt_write_eq hm3 (b := stackBelow m0 256) rfl (by omega) (.lit 1)
          (hwr3.find (by simp)) rfl,
        wordAt_write_eq hm3 (b := stackBelow m0 256) rfl (by omega) (.lit 0)
          (hwr3.find (by simp)) rfl⟩
    | 1, _ =>
      exact ⟨wordAt_write_eq hm3 (b := stackBelow m0 256) rfl (by omega) (.reg .rbp)
          (hwr3.find (by simp)) e2bp,
        wordAt_write_eq hm3 (b := stackBelow m0 256) rfl (by omega) (.lit 0)
          (hwr3.find (by simp)) rfl⟩
    | 2, _ =>
      exact ⟨wordAt_write_eq hm3 (b := stackBelow m0 256) rfl (by omega) (.reg .rax)
          (hwr3.find (by simp)) e2ax,
        wordAt_write_eq hm3 (b := stackBelow m0 256) rfl (by omega) (.lit 0)
          (hwr3.find (by simp)) rfl⟩
  have e3di : reg st3.data .rdi = reg m0 .rsi :=
    (hm3.regs .rdi _ hdi3).trans ((hsv2.1 .r14 rfl).trans e1_14)
  have e3si : reg st3.data .rsi = BitVec.ofNat 64 3 := hm3.regs .rsi _ hsi3
  have e3dx : reg st3.data .rdx = off (stackBelow m0 256) 32 :=
    (hm3.regs .rdx _ hdx3).trans (eval_ptr0 32)
  have e3cx : reg st3.data .rcx = BitVec.ofNat 64 3 := hm3.regs .rcx _ hcx3
  have hpre3 : DotPre st3.data := by
    refine ⟨hb3.stackOk hst hld, ?_, ?_⟩
    · rw [e3di, e3si]; exact hb3.sliceOk hst hld hW3
    · rw [e3dx, e3cx]; exact local_sliceOk hst hb3 hld (by omega) (by omega)
  refine call_then hpc3 hdot hpre3 fun st4 hpc4 hrsp4 ⟨hd4, hc4, hsv4⟩ ↦ ?_
  have hdot1 : ewRet st4.data = dot (ewsOf m0.dmem (reg m0 .rsi) 3).toArray
      #[sepStateW, EW.ofK (UInt64.ofBitVec (stackArg m0 3)), gpow 0] := by
    rw [hd4, e3di, e3si, e3dx, e3cx, hb3.slice_eq hst hW3, slice_three hA1,
      slice_weights _ _ 3 (by decide)]
  have hb4 := Body.call hst hF hb3 hld hsv4 hrsp4 hc4 slots_le
  have FW4 := FrameWords.call hst hb3 hld hc4 (by simp) FW3
  -- `b2`: the first fingerprint's limb `0` at offset `16`, `index_mle_from(memory_low)`.
  have hwf4 := wf_args (d := st4.data) hst hF hb4.fr.kept hargs (by decide) (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.Fingerprints.b2Offset + b2.length)).toBitVec)
  refine exec_at (infix_of b2_in_code (by simp [b2]) hp) run_b2 hwf4 (fun _ _ ↦ rfl)
    (hpc4.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.Fingerprints.b1_next))
    (match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hb4.fr.rsp_eval, trivial⟩ trivial trivial (ALI _ _))
    fun st5 hm5 hpc5 ↦ ?_
  obtain ⟨hmid5, hw5, hwr5, hbd5, hk5, hbp5, hdi5, hsi5⟩ := after_eq run_b2 ▸ ok_b2
  have hb5 := Body.of_block hst hF hb4 hwf4 hm5 hmid5 hw5 slots_le
  have FW5 : FrameWords m0 256 st5.data.dmem
      [(16, UInt64.ofBitVec (reg st4.data .rax)), (24, UInt64.ofBitVec (reg m0 .r9))] := by
    have FW5' := FrameWords.block hwf4 hm5 (writesIn_of_mid hmid5) (by simp)
      (fun p hp w hw _ ↦ by
        rw [List.mem_singleton] at hp; subst hp; rcases hbd5 w hw with h | h <;> omega) FW4
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact wordAt_write_eq hm5 (b := stackBelow m0 256) rfl (by omega) (.reg .rax)
        (hwr5.find (by simp)) rfl
    · exact FW5' p hp
  have e5bp : reg st5.data .rbp = reg st4.data .rdx := hm5.regs .rbp _ hbp5
  have e4_13 : reg st4.data .r13 = reg m0 .rcx :=
    (hsv4.1 .r13 rfl).trans ((hk3.reg' hm3 (by simp)).trans ((hsv2.1 .r13 rfl).trans e1_13))
  have e4_15 : reg st4.data .r15 = reg m0 .r8 :=
    (hsv4.1 .r15 rfl).trans ((hk3.reg' hm3 (by simp)).trans ((hsv2.1 .r15 rfl).trans e1_15))
  have e4_12 : reg st4.data .r12 = reg m0 .rdx :=
    (hsv4.1 .r12 rfl).trans ((hk3.reg' hm3 (by simp)).trans ((hsv2.1 .r12 rfl).trans e1_12))
  have e4_14 : reg st4.data .r14 = reg m0 .rsi :=
    (hsv4.1 .r14 rfl).trans ((hk3.reg' hm3 (by simp)).trans ((hsv2.1 .r14 rfl).trans e1_14))
  have e4bx : reg st4.data .rbx = reg m0 .rdi :=
    (hsv4.1 .rbx rfl).trans ((hk3.reg' hm3 (by simp)).trans ((hsv2.1 .rbx rfl).trans e1bx))
  have e5di : reg st5.data .rdi = reg m0 .rcx := (hm5.regs .rdi _ hdi5).trans e4_13
  have e5si : reg st5.data .rsi = reg m0 .r8 := (hm5.regs .rsi _ hsi5).trans e4_15
  have hpre5 : IndexMleFromPre st5.data := by
    refine ⟨hb5.stackOk hst hli, ?_⟩
    rw [e5di, e5si]; exact hb5.sliceOk hst hli hML
  refine call_then hpc5 himf hpre5 fun st6 hpc6 hrsp6 ⟨hi6, hc6, hsv6⟩ ↦ ?_
  have himl : ewRet st6.data = indexMleFrom gen (slice m0 (reg m0 .rcx) (reg m0 .r8)) := by
    rw [hi6, e5di, e5si, hb5.slice_eq hst hML]
  have hb6 := Body.call hst hF hb5 hli hsv6 hrsp6 hc6 slots_le
  have FW6 := FrameWords.call hst hb5 hli hc6 (by simp) FW5
  have e6_12 : reg st6.data .r12 = reg m0 .rdx :=
    (hsv6.1 .r12 rfl).trans ((hk5.reg' hm5 (by simp)).trans e4_12)
  -- `b3`: `memory`'s two elements loaded, `[g, index_mle(memory_low), memory_count, memory]` at
  -- offset `128`, `dot` with the first five weights.
  have hwf6 := wf1 (d := st6.data) hst hF hb6.fr.kept (a := reg m0 .rdx) (n := 32) hM.1 hM.2
    (vars := fun _ ↦ 0) (ret := 0)
  refine exec_at (infix_of ((infix_take b3 4).trans b3_in_code (by simp [b3])) (by simp [b3]) hp)
    run_b3a hwf6 nofun (hpc6.trans (congrArg Host.addrOf (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.Fingerprints.b2_next)))
    (match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hb6.fr.rsp_eval, known_ptr rfl e6_12, trivial⟩ trivial
      trivial trivial)
    fun st7 hm7 hpc7 ↦ ?_
  obtain ⟨hmid7, hmem7, hk7, hcx7, hsi7, hdi7, h8_7⟩ := after_eq run_b3a ▸ ok_b3a
  have hb7 := Body.of_block hst hF hb6 hwf6 hm7 hmid7 (by rw [hmem7]; nofun) slots_le
  have hd7 : st7.data.dmem = st6.data.dmem := hm7.dmem_eq hwf6 hmem7
  have FW7 : FrameWords m0 256 st7.data.dmem
      [(16, UInt64.ofBitVec (reg st4.data .rax)), (24, UInt64.ofBitVec (reg m0 .r9))] := by
    rw [hd7]; exact FW6
  -- `memory` as the loaded words.
  have hmem : ewsOf m0.dmem (reg m0 .rdx) 2 =
      [ewArg (reg st7.data .rcx) (reg st7.data .rsi), ewArg (reg st7.data .rdi) (reg st7.data .r8)] := by
    have hkeep : ewsOf st6.data.dmem (reg m0 .rdx) 2 = ewsOf m0.dmem (reg m0 .rdx) 2 :=
      NativeRustcVm.ewsOf_congr fun _ hi ↦ get_keep hst hb6.same hM.2 hM.1.2 hi
    rw [← hkeep, show reg st7.data .rcx = _ from hm7.regs .rcx _ hcx7,
      show reg st7.data .rsi = _ from hm7.regs .rsi _ hsi7,
      show reg st7.data .rdi = _ from hm7.regs .rdi _ hdi7,
      show reg st7.data .r8 = _ from hm7.regs .r8 _ h8_7]
    have hbase : (frameEnv m0 st6.data 256 [(reg m0 .rdx, 32)] (fun _ ↦ 0) 0).base 1 =
        reg m0 .rdx := rfl
    have hmem0 : (frameEnv m0 st6.data 256 [(reg m0 .rdx, 32)] (fun _ ↦ 0) 0).mem0 =
        st6.data.dmem := rfl
    have e0 := NativeRustcVmX64.Arrays.ewOf_loads
      (frameEnv m0 st6.data 256 [(reg m0 .rdx, 32)] (fun _ ↦ 0) 0) 1 0
    have e1 := NativeRustcVmX64.Arrays.ewOf_loads
      (frameEnv m0 st6.data 256 [(reg m0 .rdx, 32)] (fun _ ↦ 0) 0) 1 16
    rw [hbase, hmem0] at e0 e1
    show [ewOf st6.data.dmem (reg m0 .rdx + BitVec.ofNat 64 (16 * 0)),
      ewOf st6.data.dmem (reg m0 .rdx + BitVec.ofNat 64 (16 * 1))] = _
    rw [e0, e1]
    rfl
  -- `b3`'s rest.
  have hb7' : Body m0 256 fingerprintsStack slots 8 st7.data := hb7
  have hwf7 := wf_args (d := st7.data) hst hF hb7.fr.kept hargs (by decide) (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + (33 + 4) + (b3.drop 4).length)).toBitVec)
  refine exec_at (infix_of ((infix_drop b3 4).trans b3_in_code (by simp [b3])) (by simp [b3]) hp)
    run_b3b hwf7 (fun _ _ ↦ rfl)
    (hpc7.trans (congrArg Host.addrOf (by have : (b3.take 4).length = 4 := rfl; omega)))
    (match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hb7'.fr.rsp_eval, trivial⟩ trivial trivial (ALI _ _))
    fun st8 hm8 hpc8 ↦ ?_
  obtain ⟨hmid8, hw8, hwr8, hbd8, hk8, hdi8, hsi8, hdx8, hcx8⟩ := after_eq run_b3b ▸ ok_b3b
  have hb8 := Body.of_block hst hF hb7' hwf7 hm8 hmid8 hw8 slots_le
  have FW8 := FrameWords.block hwf7 hm8 (writesIn_of_mid hmid8) (by simp)
    (fun p hp w hw _ ↦ by
      rcases List.mem_cons.mp hp with rfl | hp
      · rcases hbd8 w hw with h | h <;> omega
      · rw [List.mem_singleton] at hp; subst hp; rcases hbd8 w hw with h | h <;> omega) FW7
  have e6ax : reg st7.data .rax = reg st6.data .rax := hk7.reg' hm7 (by simp)
  have e6dx : reg st7.data .rdx = reg st6.data .rdx := hk7.reg' hm7 (by simp)
  have hA2 : NativeRustcVm.EWsAt st8.data.dmem (off (stackBelow m0 256) 128)
      [sepMemW, ewRet st6.data, ewArg (stackArg m0 4) (stackArg m0 5),
        ewArg (reg st7.data .rcx) (reg st7.data .rsi),
        ewArg (reg st7.data .rdi) (reg st7.data .r8)] := by
    have hs7 := hb7'.same
    refine ewsAt_words fun i hi ↦ ?_
    match i, hi with
    | 0, _ =>
      exact ⟨wordAt_write_eq hm8 (b := stackBelow m0 256) rfl (by omega) (.lit 2)
          (hwr8.find (by simp)) rfl,
        wordAt_write_eq hm8 (b := stackBelow m0 256) rfl (by omega) (.lit 0)
          (hwr8.find (by simp)) rfl⟩
    | 1, _ =>
      exact ⟨wordAt_write_eq hm8 (b := stackBelow m0 256) rfl (by omega) (.reg .rax)
          (hwr8.find (by simp)) e6ax,
        wordAt_write_eq hm8 (b := stackBelow m0 256) rfl (by omega) (.reg .rdx)
          (hwr8.find (by simp)) e6dx⟩
    | 2, _ =>
      exact ⟨wordAt_write_eq hm8 (b := stackBelow m0 256) rfl (by omega) (.load 1 32 8)
          (hwr8.find (by simp)) (AL st7.data hs7 4 (by decide) _),
        wordAt_write_eq hm8 (b := stackBelow m0 256) rfl (by omega) (.load 1 40 8)
          (hwr8.find (by simp)) (AL st7.data hs7 5 (by decide) _)⟩
    | 3, _ =>
      exact ⟨wordAt_write_eq hm8 (b := stackBelow m0 256) rfl (by omega) (.reg .rcx)
          (hwr8.find (by simp)) rfl,
        wordAt_write_eq hm8 (b := stackBelow m0 256) rfl (by omega) (.reg .rsi)
          (hwr8.find (by simp)) rfl⟩
    | 4, _ =>
      exact ⟨wordAt_write_eq hm8 (b := stackBelow m0 256) rfl (by omega) (.reg .rdi)
          (hwr8.find (by simp)) rfl,
        wordAt_write_eq hm8 (b := stackBelow m0 256) rfl (by omega) (.reg .r8)
          (hwr8.find (by simp)) rfl⟩
  have e7_14 : reg st7.data .r14 = reg m0 .rsi :=
    (hk7.reg' hm7 (by simp)).trans ((hsv6.1 .r14 rfl).trans
      ((hk5.reg' hm5 (by simp)).trans e4_14))
  have e8di : reg st8.data .rdi = reg m0 .rsi := (hm8.regs .rdi _ hdi8).trans e7_14
  have e8si : reg st8.data .rsi = BitVec.ofNat 64 5 := hm8.regs .rsi _ hsi8
  have e8dx : reg st8.data .rdx = off (stackBelow m0 256) 128 :=
    (hm8.regs .rdx _ hdx8).trans (eval_ptr0 128)
  have e8cx : reg st8.data .rcx = BitVec.ofNat 64 5 := hm8.regs .rcx _ hcx8
  have hpre8 : DotPre st8.data := by
    refine ⟨hb8.stackOk hst hld, ?_, ?_⟩
    · rw [e8di, e8si]; exact hb8.sliceOk hst hld hW5
    · rw [e8dx, e8cx]; exact local_sliceOk hst hb8 hld (by omega) (by omega)
  refine call_then hpc8 hdot hpre8 fun st9 hpc9 hrsp9 ⟨hd9, hc9, hsv9⟩ ↦ ?_
  have hdot2 : ewRet st9.data = dot (ewsOf m0.dmem (reg m0 .rsi) 5).toArray
      (#[sepMemW, indexMleFrom gen (slice m0 (reg m0 .rcx) (reg m0 .r8)),
        ewArg (stackArg m0 4) (stackArg m0 5)] ++ (ewsOf m0.dmem (reg m0 .rdx) 2).toArray) := by
    rw [hd9, e8di, e8si, e8dx, e8cx, hb8.slice_eq hst hW5, slice_five hA2,
      slice_weights _ _ 5 (by decide), himl, hmem]
    rfl
  have hb9 := Body.call hst hF hb8 hld hsv9 hrsp9 hc9 slots_le
  have FW9 := FrameWords.call hst hb8 hld hc9 (by simp) FW8
  -- `b4`: the second fingerprint in R15, R12; `kpow(2)`.
  have hwf9 := wf_args (d := st9.data) hst hF hb9.fr.kept hargs (by decide) (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.Fingerprints.b4Offset + b4.length)).toBitVec)
  refine exec_at (infix_of b4_in_code (by simp [b4]) hp) run_b4 hwf9 (fun _ _ ↦ rfl)
    (hpc9.trans (congrArg Host.addrOf (by have hn := NativeRustcVmX64.Vm.Fingerprints.b3_next; have hl := NativeRustcVmX64.Vm.Fingerprints.b3_length; simp only [NativeRustcVmX64.Vm.Fingerprints.b3Length] at hl; simp only [List.length_drop]; omega)))
    (match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hb9.fr.rsp_eval, trivial⟩ trivial trivial (ALI _ _))
    fun st10 hm10 hpc10 ↦ ?_
  obtain ⟨hmid10, hw10, hk10, h15_10, h12_10, hdi10⟩ := after_eq run_b4 ▸ ok_b4
  have hb10 := Body.of_block hst hF hb9 hwf9 hm10 hmid10 (fun w hw ↦ (hw10 w hw).1) slots_le
  have FW10 := FrameWords.block hwf9 hm10 (writesIn_of_mid hmid10) (by simp)
    (fun p hp w hw _ ↦ by
      have h1 := (hw10 w hw).2
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> left <;> dsimp only <;> omega) FW9
  have e10_15 : reg st10.data .r15 = reg st9.data .rax := hm10.regs .r15 _ h15_10
  have e10_12 : reg st10.data .r12 = reg st9.data .rdx := hm10.regs .r12 _ h12_10
  have e10di : reg st10.data .rdi = BitVec.ofNat 64 2 := hm10.regs .rdi _ hdi10
  refine call_then hpc10 hkpow (hb10.stackOk hst hlk)
    fun st11 hpc11 hrsp11 ⟨hk11, hs11, hsv11⟩ ↦ ?_
  have hc11 : Changes st10.data st11.data kpowStack 0 0 :=
    NativeRustcVm.Transcript.SameOutside.mono hs11 fun _ h ↦ Or.inr h
  have hb11 := Body.call hst hF hb10 hlk hsv11 hrsp11 hc11 slots_le
  have FW11 := FrameWords.call hst hb10 hlk hc11 (by simp) FW10
  have e11ax : reg st11.data .rax = (gpowK 2).toBitVec := by rw [hk11, e10di]; rfl
  -- `b5`: `kpow(2)` in R13, `index_mle_from(bytecode_low)`.
  have hwf11 := wf_args (d := st11.data) hst hF hb11.fr.kept hargs (by decide) (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.Fingerprints.b5Offset + b5.length)).toBitVec)
  refine exec_at (infix_of b5_in_code (by simp [b5]) hp) run_b5 hwf11 (fun _ _ ↦ rfl)
    (hpc11.trans (congrArg Host.addrOf (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.Fingerprints.b4_next)))
    (match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hb11.fr.rsp_eval, trivial⟩ trivial trivial (ALI _ _))
    fun st12 hm12 hpc12 ↦ ?_
  obtain ⟨hmid12, hw12, hk12, h13_12, hdi12, hsi12⟩ := after_eq run_b5 ▸ ok_b5
  have hb12 := Body.of_block hst hF hb11 hwf11 hm12 hmid12 (fun w hw ↦ (hw12 w hw).1) slots_le
  have FW12 := FrameWords.block hwf11 hm12 (writesIn_of_mid hmid12) (by simp)
    (fun p hp w hw _ ↦ by
      have h1 := (hw12 w hw).2
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> left <;> dsimp only <;> omega) FW11
  have e12_13 : reg st12.data .r13 = reg st11.data .rax := hm12.regs .r13 _ h13_12
  have e12di : reg st12.data .rdi = reg m0 .r9 :=
    (hm12.regs .rdi _ hdi12).trans
      (load_frameWord FW11 (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  have e12si : reg st12.data .rsi = stackArg m0 0 :=
    (hm12.regs .rsi _ hsi12).trans (AL st11.data hb11.same 0 (by decide) _)
  have hpre12 : IndexMleFromPre st12.data := by
    refine ⟨hb12.stackOk hst hli, ?_⟩
    rw [e12di, e12si]; exact hb12.sliceOk hst hli hBL
  refine call_then hpc12 himf hpre12 fun st13 hpc13 hrsp13 ⟨hi13, hc13, hsv13⟩ ↦ ?_
  have himl2 : ewRet st13.data = indexMleFrom gen (slice m0 (reg m0 .r9) (stackArg m0 0)) := by
    rw [hi13, e12di, e12si, hb12.slice_eq hst hBL]
  have hb13 := Body.call hst hF hb12 hli hsv13 hrsp13 hc13 slots_le
  have FW13 := FrameWords.call hst hb12 hli hc13 (by simp) FW12
  -- `b6`: `[g², index_mle(bytecode_low), bytecode_count]` at offset `80`, `dot`.
  have hwf13 := wf_args (d := st13.data) hst hF hb13.fr.kept hargs (by decide) (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.Fingerprints.b6Offset + b6.length)).toBitVec)
  refine exec_at (infix_of b6_in_code (by simp [b6]) hp) run_b6 hwf13 (fun _ _ ↦ rfl)
    (hpc13.trans (congrArg Host.addrOf (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.Fingerprints.b5_next)))
    (match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hb13.fr.rsp_eval, trivial⟩ trivial trivial (ALI _ _))
    fun st14 hm14 hpc14 ↦ ?_
  obtain ⟨hmid14, hw14, hwr14, hbd14, hk14, hdi14, hsi14, hdx14, hcx14⟩ := after_eq run_b6 ▸ ok_b6
  have hb14 := Body.of_block hst hF hb13 hwf13 hm14 hmid14 hw14 slots_le
  have FW14 := FrameWords.block hwf13 hm14 (writesIn_of_mid hmid14) (by simp)
    (fun p hp w hw _ ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> rcases hbd14 w hw with h | h <;> dsimp only <;> omega) FW13
  have e13_13 : reg st13.data .r13 = (gpowK 2).toBitVec :=
    (hsv13.1 .r13 rfl).trans (e12_13.trans e11ax)
  have hA3 : NativeRustcVm.EWsAt st14.data.dmem (off (stackBelow m0 256) 80)
      [sepBytecodeW, ewRet st13.data, ewArg (stackArg m0 6) (stackArg m0 7)] := by
    have hs13 := hb13.same
    refine ewsAt_words fun i hi ↦ ?_
    match i, hi with
    | 0, _ =>
      exact ⟨wordAt_write_eq hm14 (b := stackBelow m0 256) rfl (by omega) (.reg .r13)
          (hwr14.find (by simp)) e13_13,
        wordAt_write_eq hm14 (b := stackBelow m0 256) rfl (by omega) (.lit 0)
          (hwr14.find (by simp)) rfl⟩
    | 1, _ =>
      exact ⟨wordAt_write_eq hm14 (b := stackBelow m0 256) rfl (by omega) (.reg .rax)
          (hwr14.find (by simp)) rfl,
        wordAt_write_eq hm14 (b := stackBelow m0 256) rfl (by omega) (.reg .rdx)
          (hwr14.find (by simp)) rfl⟩
    | 2, _ =>
      exact ⟨wordAt_write_eq hm14 (b := stackBelow m0 256) rfl (by omega) (.load 1 48 8)
          (hwr14.find (by simp)) (AL st13.data hs13 6 (by decide) _),
        wordAt_write_eq hm14 (b := stackBelow m0 256) rfl (by omega) (.load 1 56 8)
          (hwr14.find (by simp)) (AL st13.data hs13 7 (by decide) _)⟩
  have e13_14 : reg st13.data .r14 = reg m0 .rsi :=
    (hsv13.1 .r14 rfl).trans ((hk12.reg' hm12 (by simp)).trans ((hsv11.1 .r14 rfl).trans
      ((hk10.reg' hm10 (by simp)).trans ((hsv9.1 .r14 rfl).trans
        ((hk8.reg' hm8 (by simp)).trans e7_14)))))
  have e14di : reg st14.data .rdi = reg m0 .rsi := (hm14.regs .rdi _ hdi14).trans e13_14
  have e14si : reg st14.data .rsi = BitVec.ofNat 64 3 := hm14.regs .rsi _ hsi14
  have e14dx : reg st14.data .rdx = off (stackBelow m0 256) 80 :=
    (hm14.regs .rdx _ hdx14).trans (eval_ptr0 80)
  have e14cx : reg st14.data .rcx = BitVec.ofNat 64 3 := hm14.regs .rcx _ hcx14
  have hpre14 : DotPre st14.data := by
    refine ⟨hb14.stackOk hst hld, ?_, ?_⟩
    · rw [e14di, e14si]; exact hb14.sliceOk hst hld hW3
    · rw [e14dx, e14cx]; exact local_sliceOk hst hb14 hld (by omega) (by omega)
  refine call_then hpc14 hdot hpre14 fun st15 hpc15 hrsp15 ⟨hd15, hc15, hsv15⟩ ↦ ?_
  have hdot3 : ewRet st15.data = dot (ewsOf m0.dmem (reg m0 .rsi) 3).toArray
      #[sepBytecodeW, indexMleFrom gen (slice m0 (reg m0 .r9) (stackArg m0 0)),
        ewArg (stackArg m0 6) (stackArg m0 7)] := by
    rw [hd15, e14di, e14si, e14dx, e14cx, hb14.slice_eq hst hW3, slice_three hA3,
      slice_weights _ _ 3 (by decide), himl2]
  have hb15 := Body.call hst hF hb14 hld hsv15 hrsp15 hc15 slots_le
  have FW15 := FrameWords.call hst hb14 hld hc15 (by simp) FW14
  -- `b7`: the share added to the third; the three at `out`; the epilogue.
  have hwf15 := wf_args (d := st15.data) hst hF hb15.fr.kept hargs (by decide) (vars := fun _ ↦ 0)
    (ret := 0)
  refine exec_at (infix_of ((infix_take b7 2).trans b7_in_code (by simp [b7])) (by simp [b7]) hp)
    run_b7a hwf15 nofun
    (hpc15.trans (congrArg Host.addrOf (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.Fingerprints.b6_next)))
    (match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hb15.fr.rsp_eval, trivial⟩ trivial trivial (ALI _ _))
    fun st16 hm16 hpc16 ↦ ?_
  obtain ⟨hmid16, hmem16, hk16, hax16, hdx16⟩ := after_eq run_b7a ▸ ok_b7a
  have hb16 := Body.of_block hst hF hb15 hwf15 hm16 hmid16 (by rw [hmem16]; nofun) slots_le
  have hd16 : st16.data.dmem = st15.data.dmem := hm16.dmem_eq hwf15 hmem16
  have e16ax : reg st16.data .rax = reg st15.data .rax ^^^ stackArg m0 1 := by
    rw [show reg st16.data .rax = _ from hm16.regs .rax _ hax16]
    simp only [Sym.eval, xor_apply, Env.ofMachine_regs]
    rw [AL st15.data hb15.same 1 (by decide) _]
  have e16dx : reg st16.data .rdx = reg st15.data .rdx ^^^ stackArg m0 2 := by
    rw [show reg st16.data .rdx = _ from hm16.regs .rdx _ hdx16]
    simp only [Sym.eval, xor_apply, Env.ofMachine_regs]
    rw [AL st15.data hb15.same 2 (by decide) _]
  -- The registers holding the first two fingerprints and `out`.
  have K : ∀ r ∈ [Reg64.rbx, .rbp, .r12, .r15], reg st16.data r = reg st10.data r := by
    intro r hr
    have hcs : calleeSaved r = true := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> rfl
    have hr6 : r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl <;> simp
    have hr5 : r ∈ [Reg64.rbx, .rbp, .r12, .r14, .r15] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl <;> simp
    exact (hk16.reg' hm16 hr6).trans ((hsv15.1 r hcs).trans ((hk14.reg' hm14 hr6).trans
      ((hsv13.1 r hcs).trans ((hk12.reg' hm12 hr5).trans (hsv11.1 r hcs)))))
  have e9bp : reg st10.data .rbp = reg st4.data .rdx :=
    (hk10.reg' hm10 (by simp)).trans ((hsv9.1 .rbp rfl).trans ((hk8.reg' hm8 (by simp)).trans
      ((hk7.reg' hm7 (by simp)).trans ((hsv6.1 .rbp rfl).trans e5bp))))
  have e10bx : reg st10.data .rbx = reg m0 .rdi :=
    (hk10.reg' hm10 (by simp)).trans ((hsv9.1 .rbx rfl).trans ((hk8.reg' hm8 (by simp)).trans
      ((hk7.reg' hm7 (by simp)).trans ((hsv6.1 .rbx rfl).trans
        ((hk5.reg' hm5 (by simp)).trans e4bx)))))
  have FW16 : FrameWords m0 256 st16.data.dmem
      [(16, UInt64.ofBitVec (reg st4.data .rax)), (24, UInt64.ofBitVec (reg m0 .r9))] := by
    rw [hd16]; exact FW15
  have hwf16 := wf1 (d := st16.data) hst hF hb16.fr.kept hOR hOS (vars := fun _ ↦ 0) (ret := 0)
  have hbx16 : reg st16.data .rbx = reg m0 .rdi := (K .rbx (by simp)).trans e10bx
  refine exec_at (infix_of ((infix_drop b7 2).trans b7_in_code (by simp [b7])) (by simp [b7]) hp)
    run_b7b hwf16 nofun (hpc16.trans (congrArg Host.addrOf (by
      have : (b7.take 2).length = 2 := rfl; omega)))
    (match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hb16.fr.rsp_eval, known_ptr rfl hbx16, trivial⟩
      trivial trivial trivial)
    fun st17 hm17 hpc17 ↦ ?_
  obtain ⟨hepi, hw17, hwr17⟩ := after_eq run_b7b ▸ ok_b7b
  obtain ⟨hsv17, hrsp17⟩ := Frame.epilogue hb16.fr hwf16 hm17 hepi
  have hso17 : NativeRustcVm.SameOutside st16.data.dmem st17.data.dmem
      (NativeRustcVm.InRange (reg m0 .rdi) 48) :=
    sameOutside_region hwf16 hm17 (r := 1) rfl fun w hw ↦ ⟨(hw17 w hw).1, Nat.zero_le _,
      (hw17 w hw).2⟩
  have hOut : NativeRustcVm.EWsAt st17.data.dmem (off (reg m0 .rdi) 0)
      [ewRet st4.data, ewRet st9.data, ewRet st15.data + ewArg (stackArg m0 1) (stackArg m0 2)] := by
    refine ewsAt_words fun i hi ↦ ?_
    match i, hi with
    | 0, _ =>
      exact ⟨wordAt_write_eq hm17 (b := reg m0 .rdi) rfl (by omega) (.load 0 16 8)
          (hwr17.find (by simp)) (load_frameWord FW16 List.mem_cons_self),
        wordAt_write_eq hm17 (b := reg m0 .rdi) rfl (by omega) (.reg .rbp)
          (hwr17.find (by simp)) ((K .rbp (by simp)).trans e9bp)⟩
    | 1, _ =>
      exact ⟨wordAt_write_eq hm17 (b := reg m0 .rdi) rfl (by omega) (.reg .r15)
          (hwr17.find (by simp)) ((K .r15 (by simp)).trans e10_15),
        wordAt_write_eq hm17 (b := reg m0 .rdi) rfl (by omega) (.reg .r12)
          (hwr17.find (by simp)) ((K .r12 (by simp)).trans e10_12)⟩
    | 2, _ =>
      exact ⟨wordAt_write_eq hm17 (b := reg m0 .rdi) rfl (by omega) (.reg .rax)
          (hwr17.find (by simp)) e16ax,
        wordAt_write_eq hm17 (b := reg m0 .rdi) rfl (by omega) (.reg .rdx)
          (hwr17.find (by simp)) e16dx⟩
  simp only [PcOk] at hpc17
  refine .done _ ⟨by rw [hpc17]; exact hb16.fr.load_ret hst hF, hrsp17, ?_, ?_, hsv17⟩
  · have hfp : fingerprints (ewsOf m0.dmem (reg m0 .rsi) 5).toArray
        (ewsOf m0.dmem (reg m0 .rdx) 2).toArray (slice m0 (reg m0 .rcx) (reg m0 .r8))
        (slice m0 (reg m0 .r9) (stackArg m0 0)) (ewArg (stackArg m0 1) (stackArg m0 2))
        (EW.ofK (.ofBitVec (stackArg m0 3))) (ewArg (stackArg m0 4) (stackArg m0 5))
        (ewArg (stackArg m0 6) (stackArg m0 7)) =
        #[ewRet st4.data, ewRet st9.data,
          ewRet st15.data + ewArg (stackArg m0 1) (stackArg m0 2)] := by
      rw [hdot1, hdot2, hdot3]
      simp only [fingerprints, extract_ewsOf _ _ (show 3 ≤ 5 by omega),
        extract_ewsOf _ _ (Nat.le_refl 5), indexMle]
    show NativeRustcVm.EWsAt st17.data.dmem (reg m0 .rdi)
      (fingerprints (ewsOf m0.dmem (reg m0 .rsi) 5).toArray
        (ewsOf m0.dmem (reg m0 .rdx) 2).toArray (slice m0 (reg m0 .rcx) (reg m0 .r8))
        (slice m0 (reg m0 .r9) (stackArg m0 0)) (ewArg (stackArg m0 1) (stackArg m0 2))
        (EW.ofK (.ofBitVec (stackArg m0 3))) (ewArg (stackArg m0 4) (stackArg m0 5))
        (ewArg (stackArg m0 6) (stackArg m0 7))).toList
    rw [hfp, ← off_zero (reg m0 .rdi)]
    exact hOut
  · intro q hq
    simp only [not_or] at hq
    exact (hso17 q hq.1).trans (hb16.same q hq.2)

end

end NativeRustcVmX64.Bus.Fingerprints
