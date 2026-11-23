module

public import NativeRustcVmX64.Whir.InducedWeight.Fin
public import NativeRustcVmX64.Code.Vm.Memcpy.Names
public import NativeRustcVmX64.Code.Vm.SubspaceTable.Names

/-!
# `induced_weight`'s entry (x86-64)

`entry_a`: `b0a` pushes the callee-saved registers and opens the 1112-byte frame, `b0b` spills the
queries' and the weights' pointers and calls `subspace_table(μ)` into the frame at 104; `b1` checks
its tag: for `μ > 30` (`None`) `none_fin`. `entry_b`: `b2` spills the output and copies the table's
pairs to 624 (`memcpy`), `b3` stores the table's count at 616 and takes the queries' count (the
smaller of the queries' and the weights'): none goes to `zero_fin`, else `b4` spills the table's
slice and the count, loads the point and enters the queries' loop (`OInv m0 0`).
-/

namespace NativeRustcVmX64.Whir.InducedWeight

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.InducedWeight NativeVm.Model
open NativeRustcVm.Whir NativeRustcVmX64.Whir.Leaf
open NativeRustcVm (Region InAny WordAt WordsAt wordOf)
open NativeRustcVmX64.Field (midS frameS frameEnv frame_wf match_frame)
open NativeRustcVmX64.Arrays (stackOk_mono load8_eq wordAt_of_write eval_reg eval_lit eval_load
  eval_test eval_min wf_two apart_symm keepsRegs freeRegs)

public section

/-- **A block writing the frame below its slots** keeps a body. -/
theorem fr_write [Labels] {m0 st st' : MachineData} {env : Env} {S₀ S₁ : SState}
    (hS : StackOk m0 inducedWeightStack) (hfr : Fr m0 st) (hm₀ : Match env S₀ st)
    (hm : Match env S₁ st') (hwf : env.WF) (hd : st.dmem = env.mem0)
    (hk : keepsRegs S₀ S₁ (.rsp :: freeRegs slots) = true) {sz : Nat}
    (hr : env.regions[0]? = some (fbOf m0, sz)) (hsz : 1120 ≤ sz)
    (hall : ∀ w ∈ S₁.mem, w.r = 0 ∧ w.off + w.n ≤ 1120) : Fr m0 st' := by
  obtain ⟨-, -, hfe⟩ := frame_ok hS stack_le.1
  have h1 := hS.1
  have h2 := hS.2.1
  exact hfr.of_write hm₀ hm hwf hd hk (r := 0) hr hsz hall
    (fun p h ↦ .inr (inRange_frame hS stack_le.1 (by omega) h))
    (fun q hq i hi ↦ by
      rw [addr_add]
      exact Arrays.not_inRange_above (by have := slots_ok q hq; omega)
        (by rw [fbOf, hfe]; have := slots_ok q hq; have := stack_le.1; omega))

/-- A frame range is an input of a callee using `N` bytes of stack below the frame. -/
theorem whirIn_fr {m0 d : MachineData} {N : Nat} (hS : StackOk m0 inducedWeightStack)
    (hk : Kept m0.dmem d.dmem) (hsp : rspOf d = fbOf m0) (hle : 1168 + N ≤ inducedWeightStack)
    {o n : Nat} (h8 : 8 ≤ o) (hon : o + n ≤ 1168) : WhirIn d (fbOf m0 + BitVec.ofNat 64 o) n N := by
  obtain ⟨hfmap, hfnw, hfe⟩ := frame_ok hS stack_le.1
  have h1 := hS.1
  have h2 := hS.2.1
  have hfb : (fbOf m0).toNat = (rspOf m0).toNat - 1168 := hfe
  have hfo : (fbOf m0 + BitVec.ofNat 64 o).toNat = (rspOf m0).toNat - 1168 + o :=
    fb_toNat hS stack_le.1 (by omega)
  have hd : (rspOf d).toNat = (rspOf m0).toNat - 1168 := by rw [hsp]; exact hfb
  refine ⟨Readable.keep (Readable.sub (m := m0) ⟨hfmap, hfnw⟩ (by omega)) hk, ?_⟩
  unfold OffStack Apart
  rw [Arrays.stackBelow_toNat (m := d) (n := N) (by omega), hd, hfo]
  omega

/-- `memcpy`'s copy: a prefix of the source's bytes. -/
theorem bytesAt_copy {d d' : DataMem} {a a' : BitVec 64} {n : Nat} {bs : List UInt8}
    (hc : NativeRustcVm.BytesAt d a (bytesOf d' a' n)) (hb : NativeRustcVm.BytesAt d' a' bs)
    (hle : bs.length ≤ n) : NativeRustcVm.BytesAt d a bs := by
  intro i hi
  rw [hc i (by simp [NativeRustcX64.bytesOf]; omega)]
  have := hb i hi
  simp only [NativeRustcX64.bytesOf, List.getElem_map, List.getElem_range]
  rw [show (d'.get? (a' + BitVec.ofNat 64 i)) = some bs[i] from this]
  rfl

/-- Five words from their addresses. -/
theorem words5 {d : DataMem} {a : BitVec 64} {o : Nat} {w0 w1 w2 w3 w4 : UInt64}
    (h0 : WordAt d (a + BitVec.ofNat 64 o) w0) (h1 : WordAt d (a + BitVec.ofNat 64 (o + 8)) w1)
    (h2 : WordAt d (a + BitVec.ofNat 64 (o + 16)) w2)
    (h3 : WordAt d (a + BitVec.ofNat 64 (o + 24)) w3)
    (h4 : WordAt d (a + BitVec.ofNat 64 (o + 32)) w4) :
    WordsAt d (a + BitVec.ofNat 64 o) [w0, w1, w2, w3, w4] := by
  refine NativeRustcVm.wordsAt_cons_iff.mpr ⟨h0, ?_⟩
  rw [addr_add]
  refine NativeRustcVm.wordsAt_cons_iff.mpr ⟨h1, ?_⟩
  rw [addr_add, show o + 8 + 8 = o + 16 by omega]
  refine NativeRustcVm.wordsAt_cons_iff.mpr ⟨h2, ?_⟩
  rw [addr_add, show o + 16 + 8 = o + 24 by omega]
  refine NativeRustcVm.wordsAt_cons_iff.mpr ⟨h3, ?_⟩
  rw [addr_add, show o + 24 + 8 = o + 32 by omega]
  exact NativeRustcVm.wordsAt_singleton_iff.mpr h4

/-- The argument words on the stack: readable, above the frame. -/
theorem args_ok {m0 : MachineData} (hS : StackOk m0 inducedWeightStack) (h : ArgsOk m0 2) :
    Readable m0 (rspOf m0 + 8#64) 16 ∧
      Apart (stackBelow m0 1168) (1168 + 8) (rspOf m0 + 8#64) 16 ∧
      (rspOf m0 + 8#64).toNat = (rspOf m0).toNat + 8 := by
  have h1 := hS.1
  have h2 := h.2
  have hF := stack_le.1
  have ht : (rspOf m0 + 8#64).toNat = (rspOf m0).toNat + 8 := by
    rw [BitVec.toNat_add, show (8#64).toNat = 8 from rfl]
    omega
  refine ⟨⟨h.1, by unfold NoWrap; rw [ht]; omega⟩, ?_, ht⟩
  unfold Apart
  rw [ht, Arrays.stackBelow_toNat (m := m0) (n := 1168) (by omega)]
  omega

theorem fb_args0 (m0 : MachineData) :
    stackBelow m0 1168 + BitVec.ofInt 64 1176 = rspOf m0 + 8#64 + BitVec.ofInt 64 0 := by
  rw [show (1176 : Int) = ((1168 + 8 : Nat) : Int) from rfl, Field.frame_rsp,
    show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]

theorem fb_args8 (m0 : MachineData) :
    stackBelow m0 1168 + BitVec.ofInt 64 1184 = rspOf m0 + 8#64 + BitVec.ofInt 64 8 := by
  rw [show (1184 : Int) = ((1168 + 16 : Nat) : Int) from rfl, Field.frame_rsp,
    show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl, BitVec.add_assoc, ← BitVec.ofNat_add]

/-- **An argument word loaded** in a body that wrote no output. -/
theorem arg_load [Labels] {m0 st : MachineData} {env : Env} (hS : StackOk m0 inducedWeightStack)
    (hargs : ArgsOk m0 2) (hfr : Fr m0 st) (hb : env.base 1 = rspOf m0 + 8#64)
    (hmem : env.mem0 = st.dmem) {i : Nat} (hi : i < 2) :
    env.load 1 (8 * i) 8 = stackArg m0 i := by
  obtain ⟨-, -, ht⟩ := args_ok hS hargs
  have h1 := hS.1
  have h2 := hS.2.1
  have h3 := hargs.2
  rw [load8_eq, hb, hmem]
  unfold stackArg
  rw [addr_add]
  refine congrArg UInt64.toBitVec (NativeRustcVm.wordOf_congr fun j hj ↦ ?_)
  rw [addr_add]
  refine hfr.get?_eq fun h ↦ h.elim (fun ⟨_, hr, _⟩ ↦ absurd hr List.not_mem_nil) fun h ↦ ?_
  have hnw := stack_noWrap hS
  unfold NoWrap at hnw
  rw [Sym.inRange_iff (by omega), Arrays.stackBelow_toNat h1,
    toNat_add_ofNat _ _ (by omega)] at h
  omega

theorem ult32 {n : Nat} (h : n < 32) : (BitVec.ofNat 64 n).ult (BitVec.ofNat 64 32) = true := by
  rw [ult_ofNat (by decide), Arrays.toNat_ofNat_lt (by omega)]
  simp [h]

/-- `cmpq $32, %r14` with R14 below 32: the `ite`s it selects. -/
theorem ite32 [Labels] {env : Env} {n : Nat} (h : env.regs .r14 = BitVec.ofNat 64 n) (hn : n < 32)
    (a b : Sym) :
    (Sym.ite (.not (.cmp .ult .W64 (.reg .r14) (.lit 32))) a b).eval env = b.eval env ∧
      (Sym.ite (.cmp .ult .W64 (.reg .r14) (.lit 32)) a b).eval env = a.eval env := by
  have hc : CmpOp.apply .ult .W64 (env.regs .r14) (BitVec.ofNat 64 32) = true := by
    simp only [CmpOp.apply, low_W64, h]
    exact ult32 hn
  refine ⟨?_, ?_⟩
  · show (if (!(CmpOp.apply .ult .W64 (env.regs .r14) (BitVec.ofNat 64 32))) = true then a.eval env
      else b.eval env) = b.eval env
    rw [hc]; rfl
  · show (if (CmpOp.apply .ult .W64 (env.regs .r14) (BitVec.ofNat 64 32)) = true then a.eval env
      else b.eval env) = a.eval env
    rw [hc]; rfl

/-- **At `b2`**: the queries' and the weights' pointers spilled, `subspace_table`'s table (`μ ≤
30`) in the frame at 104. -/
structure AtB2 (m0 st : MachineData) : Prop where
  fr : Fr m0 st
  w56 : WordAt st.dmem (fbOf m0 + BitVec.ofNat 64 56) (.ofBitVec (reg m0 .rdx))
  w64 : WordAt st.dmem (fbOf m0 + BitVec.ofNat 64 64) (.ofBitVec (reg m0 .r8))
  tbw : WordAt st.dmem (fbOf m0 + BitVec.ofNat 64 112) (tbOf m0).size.toUInt64
  pairs : PairsAt st.dmem (fbOf m0 + BitVec.ofNat 64 120) (tbOf m0).toList
  tlen : (tbOf m0).size ≤ 31
  r14 : reg st .r14 = reg m0 .rdi
  rbx : reg st .rbx = reg m0 .rcx
  r15 : reg st .r15 = reg m0 .r9
  mu : muOf m0 ≤ stackCap

variable [Host] {k : Nat}

theorem hb0 (hp : Placed code k) : b0a.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.InducedWeight.b0Offset) ∧
    b0b.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.InducedWeight.b0Offset + b0a.length) := by
  have h := b0_in_code.trans hp.1 (by simp [b0])
  rw [← List.take_append_drop 8 b0] at h
  exact h.append
theorem hb1 (hp : Placed code k) : b1.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.InducedWeight.b1Offset) :=
  b1_in_code.trans hp.1 (by simp [b1])
theorem hb2 (hp : Placed code k) : b2.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.InducedWeight.b2Offset) :=
  b2_in_code.trans hp.1 (by simp [b2])
theorem hb3 (hp : Placed code k) : b3.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.InducedWeight.b3Offset) :=
  b3_in_code.trans hp.1 (by simp [b3])
theorem hb4 (hp : Placed code k) : b4.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.InducedWeight.b4Offset) :=
  b4_in_code.trans hp.1 (by simp [b4])

/-- **From the entry to `b2`**, or `None` for `μ > 30`. -/
theorem entry_a (hp : Placed code k)
    (htab : Spec (Labels.label NativeRustcVmX64.Vm.SubspaceTable.entryLabel) SubspaceTablePre SubspaceTablePost)
    {m0 : MachineData} (hpre : InducedWeightPre m0)
    (cont : ∀ st : MachineState, st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.InducedWeight.b2Offset) → AtB2 m0 st.data →
      Eventually (step1 Host.exe) (Post m0) st) :
    Eventually (step1 Host.exe) (Post m0) ⟨m0, Host.addrOf (k + NativeRustcVmX64.Vm.InducedWeight.b0Offset)⟩ := by
  have hpre' := hpre
  obtain ⟨hS, -, -, -, -, -, -⟩ := hpre'
  obtain ⟨hF, hle_t, -, -, -, -⟩ := stack_le
  have hsl := slots_ok
  -- `b0a`: the prologue
  have hwf0 := frame_wf (m := m0) (vars := fun _ ↦ 0) (ret := 0) (stackOk_mono hS hF)
    fun _ h ↦ h
  refine exec_then (hb0 hp).1 run_b0a hwf0 (by intro l h; cases h) match_frame
    fun st1 hm1 hpc1 ↦ ?_
  simp only [PcOk, show b0a.length = 8 from rfl] at hpc1
  obtain ⟨hw0, hregs0, hmem0, hsp0, hargs0⟩ := after_eq run_b0a ▸ b0a_entry
  have hfr1 : Fr m0 st1.data := Frame.of_entry hS hF hm1 hsp0 hw0 hregs0 hmem0
  have harg : ∀ r ∈ [Reg64.rdi, .rsi, .rdx, .rcx, .r8, .r9], reg st1.data r = reg m0 r :=
    fun r hr ↦ hm1.regs r (.reg r) (hargs0 r hr)
  -- `b0b`: the spills, `subspace_table`
  have hwf2 := hfr1.wf (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.InducedWeight.b1Offset)).toBitVec) hS hF
  refine exec_at (hb0 hp).2 run_b0b hwf2 (fun _ _ ↦ rfl) hpc1 hfr1.mid_match
    fun st2 hm2 hpc2 ↦ ?_
  obtain ⟨hk2, hsig2, hv56, hv64⟩ := after_eq run_b0b ▸ b0b_call
  have hrsp2 := rsp_call hm2 rfl
  have hkept2 : Kept m0.dmem st2.data.dmem := fun p h ↦ hm2.kept hwf2 p (hfr1.kept p h)
  have hrdi2 : reg st2.data .rdi = fbOf m0 + BitVec.ofNat 64 104 := hm2.regs .rdi _ rfl
  have hrsi2 : reg st2.data .rsi = reg m0 .rsi :=
    (hm2.regs .rsi _ rfl).trans (harg .rsi (by simp))
  have hr14 : reg st2.data .r14 = reg m0 .rdi :=
    (hm2.regs .r14 _ rfl).trans (harg .rdi (by simp))
  have hrbx : reg st2.data .rbx = reg m0 .rcx :=
    (hm2.regs .rbx _ rfl).trans (harg .rcx (by simp))
  have hr15 : reg st2.data .r15 = reg m0 .r9 :=
    (hm2.regs .r15 _ rfl).trans (harg .r9 (by simp))
  have w56 : WordAt st2.data.dmem (fbOf m0 + BitVec.ofNat 64 56) (.ofBitVec (reg m0 .rdx)) := by
    have := wordAt_of_write hm2 (r := 0) (o := 56) rfl (by decide) (v := .reg .rdx) hv56
    rwa [eval_reg, Env.ofMachine_regs,
      show st1.data.regs.get64 .rdx = _ from harg .rdx (by simp)] at this
  have w64 : WordAt st2.data.dmem (fbOf m0 + BitVec.ofNat 64 64) (.ofBitVec (reg m0 .r8)) := by
    have := wordAt_of_write hm2 (r := 0) (o := 64) rfl (by decide) (v := .reg .r8) hv64
    rwa [eval_reg, Env.ofMachine_regs,
      show st1.data.regs.get64 .r8 = _ from harg .r8 (by simp)] at this
  have hgot := hpre.2.2.2.2.2.2.2
  have hP1 : SubspaceTablePre st2.data :=
    ⟨stackOk_callee hS hkept2 hrsp2 hle_t, by
      rw [hrdi2]; exact whirIn_fr hS hkept2 hrsp2 hle_t (by omega) (by decide), by
      apply hfr1.got_after hS hle_t hgot hwf2 hm2 (hw_of hsig2 (by decide)) hrsp2
      intro a ha
      simp only [List.mem_singleton] at ha
      subst a
      dsimp only [Prod.fst, Prod.snd]
      rw [hrdi2, show fbOf m0 = stackBelow m0 1168 from rfl,
        fb_toNat hS hF (j := 104) (by omega)]
      have hb := (frame_ok hS hF).2.2
      rw [hb]
      unfold tableBytes rootCap
      omega⟩
  refine Frame.call htab hfr1 hS hle_t (L := 1120) (by omega) hsl out_nil hwf2 hfr1.mid_match
    hm2 hpc2 hk2 rfl (hw_of hsig2 (by decide)) hP1
    (fun m' ⟨_, hch, hsv⟩ ↦ ⟨hsv, fun p hp ↦ hch p fun h ↦ hp (h.elim (fun ⟨r, hr, hin⟩ ↦ by
        rw [List.mem_singleton] at hr
        subst hr
        have h' : InRange (reg st2.data .rdi) (8 + tableBytes) p := hin
        rw [hrdi2] at h'
        exact .inr (.inl (inRange_low_of hS hF (c := 104) (n := 8 + tableBytes) (by omega)
          (by decide) h'))) (fun h ↦ .inr (.inr h)))⟩)
    fun st3 hpc3 hfr3 ⟨hval, hch3, hsv3⟩ ↦ ?_
  have hpc3' : st3.pc = Host.addrOf (k + NativeRustcVmX64.Vm.InducedWeight.b1Offset) := hpc3
  rw [hrdi2] at hch3
  rw [hrdi2, hrsi2] at hval
  have k3 := fkeep_call hS hrsp2 hle_t (c := 104) (n := 8 + tableBytes) hch3 (by decide)
    (by omega) (lo := 56) (hi := 72) (by omega) (.inl (by omega))
  -- `b1`: the tag
  have hwf3 := hfr3.wf (vars := fun _ ↦ 0) (ret := 0) hS hF
  refine exec_at (hb1 hp) run_b1 hwf3 (by intro l h; cases h) hpc3' hfr3.mid_match
    fun st4 hm4 hpc4 ↦ ?_
  have hfr4 := hfr3.of_block hfr3.mid_match hm4 hwf3 rfl (after_eq run_b1 ▸ b1_keeps)
  have hd4 : st4.data.dmem = st3.data.dmem := hm4.dmem_eq hwf3 rfl
  have e4 : ∀ r ∈ [Reg64.rbx, .r14, .r15], reg st4.data r = reg st2.data r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      exact (Match.reg_eq hfr3.mid_match hm4 rfl rfl).trans (hsv3.1 _ rfl)
  simp only [PcOk] at hpc4
  obtain ⟨hT4, hF4⟩ := Arrays.pc_cond hpc4
  by_cases hmu : (reg m0 .rsi).toNat ≤ stackCap
  swap
  · simp only [hmu, ↓reduceIte] at hval
    have hc : (SBool.not (.cmp .eq .W32 (.load 0 104 4) (.lit 1))).eval
        (frameEnv m0 st3.data 1168 (fun _ ↦ 0) 0) = true := by
      show (!CmpOp.apply .eq .W32 ((frameEnv m0 st3.data 1168 (fun _ ↦ 0) 0).load 0 104 4)
        (BitVec.ofNat 64 1)) = true
      rw [load4_of_tag (env := frameEnv m0 st3.data 1168 (fun _ ↦ 0) 0) (r := 0) (.inl rfl) hval]
      rfl
    exact none_fin hp hpre hmu ((hT4 hc).trans (hp.label NativeRustcVmX64.Vm.InducedWeight.label_3_at)) hfr4
      ((e4 .r14 (by simp)).trans hr14)
  simp only [hmu, ↓reduceIte] at hval
  obtain ⟨htag, htb⟩ := hval
  have hc : (SBool.not (.cmp .eq .W32 (.load 0 104 4) (.lit 1))).eval
      (frameEnv m0 st3.data 1168 (fun _ ↦ 0) 0) = false := by
    show (!CmpOp.apply .eq .W32 ((frameEnv m0 st3.data 1168 (fun _ ↦ 0) 0).load 0 104 4)
      (BitVec.ofNat 64 1)) = false
    rw [load4_of_tag (env := frameEnv m0 st3.data 1168 (fun _ ↦ 0) 0) (r := 0) (.inr rfl) htag]
    rfl
  have hpc4' : st4.pc = Host.addrOf (k + NativeRustcVmX64.Vm.InducedWeight.b2Offset) := hF4 (by rw [hc]; exact Bool.false_ne_true)
  have htb' : BufPairsAt st3.data.dmem (fbOf m0 + BitVec.ofNat 64 112) rootCap
      (tbOf m0).toList := by
    have := htb
    rwa [NativeRustcVm.Transcript.off, addr_add] at this
  have hts : (tbOf m0).size ≤ 31 := by
    have := htb'.1
    rwa [Array.length_toList] at this
  have htw : WordAt st3.data.dmem (fbOf m0 + BitVec.ofNat 64 112) (tbOf m0).size.toUInt64 := by
    have := htb'.2.1
    rwa [Array.length_toList] at this
  have hpairs : PairsAt st3.data.dmem (fbOf m0 + BitVec.ofNat 64 120) (tbOf m0).toList := by
    have := htb'.2.2
    rwa [NativeRustcVm.Transcript.off, addr_add] at this
  refine cont st4 hpc4' ⟨hfr4, ?_, ?_, hd4 ▸ htw, hd4 ▸ hpairs, hts, ?_, ?_, ?_, hmu⟩
  · rw [hd4]; exact word_keep w56 k3 (by omega) (by omega)
  · rw [hd4]; exact word_keep w64 k3 (by omega) (by omega)
  · exact (e4 .r14 (by simp)).trans hr14
  · exact (e4 .rbx (by simp)).trans hrbx
  · exact (e4 .r15 (by simp)).trans hr15

/-- **From `b2`**: the table's copy, the count; the queries' loop, or the sum `0`. -/
theorem entry_b (hp : Placed code k)
    (hmemcpy : Spec (Labels.label NativeRustcVmX64.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    {m0 : MachineData} (hpre : InducedWeightPre m0) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.InducedWeight.b2Offset)) (hA : AtB2 m0 st.data)
    (cont : ∀ st : MachineState, st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.InducedWeight.b7Offset) → OInv m0 0 st.data →
      Eventually (step1 Host.exe) (Post m0) st) :
    Eventually (step1 Host.exe) (Post m0) st := by
  have hpre' := hpre
  obtain ⟨hS, hargs, -, -, -, -, -⟩ := hpre'
  obtain ⟨hF, -, -, -, -, hle_0⟩ := stack_le
  have hsl := slots_ok
  have hS1 := hS.1
  have hS2 := hS.2.1
  obtain ⟨hfmap, hfnw, hfe⟩ := frame_ok hS hF
  have hfb : (fbOf m0).toNat = (rspOf m0).toNat - 1168 := hfe
  have hts := hA.tlen
  have hfr := hA.fr
  -- `b2`: the output spilled, `memcpy`
  have hgot := hpre.2.2.2.2.2.2.2
  have hgot0 := hgot.areas (areas' := []) (by simp)
  have hwf5 := hfr.got_wf (l := "memcpy") (vars := fun _ => 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.InducedWeight.b3Offset)).toBitVec)
    hS hF hgot (by simp)
  have hm5start := hfr.got_match (l := "memcpy") (vars := fun _ => 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.InducedWeight.b3Offset)).toBitVec)
    (fun i hi => hfr.got_byte hS hgot0 (by simp) (by intro r hr; cases hr) (by simp) hi)
  refine exec_at (hb2 hp) run_b2 hwf5 (fun _ _ ↦ rfl) hpc hm5start fun st5 hm5 hpc5 ↦ ?_
  obtain ⟨hk5, hsig5, hv24⟩ := after_eq run_b2 ▸ b2_call
  have hrsp5 := rsp_call hm5 rfl
  have hkept5 : Kept m0.dmem st5.data.dmem := fun p h ↦ hm5.kept hwf5 p (hfr.kept p h)
  have hrdi5 : reg st5.data .rdi = fbOf m0 + BitVec.ofNat 64 624 :=
    (hm5.regs .rdi (.ptr 0 624) rfl).trans rfl
  have hrsi5 : reg st5.data .rsi = fbOf m0 + BitVec.ofNat 64 120 :=
    (hm5.regs .rsi (.ptr 0 120) rfl).trans rfl
  have hrdx5 : (reg st5.data .rdx).toNat = 496 := by
    rw [show reg st5.data .rdx = _ from hm5.regs .rdx _ rfl]; rfl
  have hr12 : reg st5.data .r12 = fbOf m0 + BitVec.ofNat 64 624 :=
    (hm5.regs .r12 (.ptr 0 624) rfl).trans rfl
  have hr14 : reg st5.data .r14 = BitVec.ofNat 64 (tbOf m0).size := by
    refine (hm5.regs .r14 _ rfl).trans ?_
    rw [eval_load, load8_eq]
    exact congrArg UInt64.toBitVec (NativeRustcVm.wordOf_of_wordAt hA.tbw)
  have k5 := fkeep_block hm5 hwf5 (m0 := m0) rfl (lo := 32) (hi := 1176) (by omega)
    (hall_of hsig5 (by decide))
  have w24 : WordAt st5.data.dmem (fbOf m0 + BitVec.ofNat 64 24) (.ofBitVec (reg m0 .rdi)) := by
    have := wordAt_of_write hm5 (r := 0) (o := 24) rfl (by decide) (v := .reg .r14) hv24
    rwa [eval_reg, gotEnv_regs, hA.r14] at this
  have h624 : (fbOf m0 + BitVec.ofNat 64 624).toNat = (rspOf m0).toNat - 1168 + 624 :=
    fb_toNat hS hF (by omega)
  have h120 : (fbOf m0 + BitVec.ofNat 64 120).toNat = (rspOf m0).toNat - 1168 + 120 :=
    fb_toNat hS hF (by omega)
  have hP5 : MemcpyPre st5.data := by
    unfold MemcpyPre
    simp only [hrdi5, hrsi5, hrdx5]
    have ha := whirIn_fr hS hkept5 hrsp5 (N := 0) hle_0 (o := 624) (n := 496) (by omega)
      (by omega)
    have hb := whirIn_fr hS hkept5 hrsp5 (N := 0) hle_0 (o := 120) (n := 496) (by omega)
      (by omega)
    refine ⟨stackOk_callee hS hkept5 hrsp5 hle_0, ha.1.1, hb.1.1, ha.1.2, hb.1.2, ?_, ?_⟩
    · unfold Apart; rw [h624, h120]; omega
    · unfold Apart; rw [h624, hrsp5, show (stackBelow m0 1168).toNat = _ from hfb]; omega
  refine Frame.call hmemcpy hfr hS (N := 0) hle_0 (L := 1120) (by omega) hsl out_nil hwf5
    hm5start hm5 hpc5 hk5 rfl (hw_of hsig5 (by decide)) hP5
    (fun m' ⟨_, _, hso, hsv⟩ ↦ ⟨hsv, fun p hp ↦ hso p fun h ↦ hp (.inr (.inl (by
      simp only [hrdi5, hrdx5] at h
      exact inRange_low_of hS hF (c := 624) (n := 496) (by omega) (by omega) h)))⟩)
    fun st6 hpc6 hfr6 ⟨_, hcopy, hso6, hsv6⟩ ↦ ?_
  have hpc6' : st6.pc = Host.addrOf (k + NativeRustcVmX64.Vm.InducedWeight.b3Offset) := hpc6
  simp only [hrdi5, hrsi5, hrdx5] at hcopy hso6
  have k6 := fkeep_range hS (c := 624) (n := 496) hso6 (by omega) (by omega) (lo := 0)
    (hi := 624) (by omega) (.inl le_rfl)
  have e6 : ∀ r ∈ [Reg64.rbx, .r12, .r14, .r15], reg st6.data r = reg st5.data r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hsv6.1 _ rfl
  have e5 : ∀ r ∈ [Reg64.rbx, .r15], reg st5.data r = reg st.data r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Match.reg_eq hm5start hm5 rfl rfl
  have hpairs6 : PairsAt st6.data.dmem (fbOf m0 + BitVec.ofNat 64 624) (tbOf m0).toList := by
    have hp5 : PairsAt st5.data.dmem (fbOf m0 + BitVec.ofNat 64 120) (tbOf m0).toList := by
      have hp0 := hA.pairs
      unfold PairsAt NativeRustcVm.WordsAt at hp0 ⊢
      refine bytes_keep hp0 k5 (by omega) ?_
      rw [pairs_len, Array.length_toList]
      omega
    unfold PairsAt NativeRustcVm.WordsAt at hp5 ⊢
    exact bytesAt_copy hcopy hp5 (by rw [pairs_len, Array.length_toList]; omega)
  -- `b3`: the table's count, the queries' count
  have hwf7 := hfr6.wf (vars := fun _ ↦ 0) (ret := 0) hS hF
  refine exec_at (hb3 hp) run_b3 hwf7 (by intro l h; cases h) hpc6' hfr6.mid_match
    fun st7 hm7 hpc7 ↦ ?_
  obtain ⟨hk7, hsig7, hv616⟩ := after_eq run_b3 ▸ b3_write
  have hfr7 := fr_write hS hfr6 hfr6.mid_match hm7 hwf7 rfl hk7 rfl (by omega)
    (hw_of hsig7 (by decide))
  have k7a := fkeep_block hm7 hwf7 (m0 := m0) rfl (lo := 0) (hi := 616) (by omega)
    (hall_of hsig7 (by decide))
  have k7b := fkeep_block hm7 hwf7 (m0 := m0) rfl (lo := 624) (hi := 1176) (by omega)
    (hall_of hsig7 (by decide))
  have hr14_6 : reg st6.data .r14 = BitVec.ofNat 64 (tbOf m0).size :=
    (e6 .r14 (by simp)).trans hr14
  have hr15_6 : reg st6.data .r15 = reg m0 .r9 :=
    (e6 .r15 (by simp)).trans ((e5 .r15 (by simp)).trans hA.r15)
  have hrbx6 : reg st6.data .rbx = reg m0 .rcx :=
    (e6 .rbx (by simp)).trans ((e5 .rbx (by simp)).trans hA.rbx)
  have w616 : WordAt st7.data.dmem (fbOf m0 + BitVec.ofNat 64 616) (tbOf m0).size.toUInt64 := by
    have := wordAt_of_write hm7 (r := 0) (o := 616) rfl (by decide) (v := .reg .r14) hv616
    rwa [eval_reg, Env.ofMachine_regs, show st6.data.regs.get64 .r14 = _ from hr14_6] at this
  have hc64 : cntOf m0 < 2 ^ 64 := by
    unfold cntOf; have := (reg m0 .r9).isLt; omega
  have hmin : (Sym.ite (.cmp .ult .W64 (.reg .rbx) (.reg .r15)) (.reg .rbx) (.reg .r15)).eval
      (frameEnv m0 st6.data 1168 (fun _ ↦ 0) 0) = BitVec.ofNat 64 (cntOf m0) := by
    rw [eval_min, Env.ofMachine_regs, Env.ofMachine_regs,
      show st6.data.regs.get64 .r15 = _ from hr15_6, show st6.data.regs.get64 .rbx = _ from hrbx6]
    rfl
  have hr15_7 : reg st7.data .r15 = BitVec.ofNat 64 (cntOf m0) :=
    (hm7.regs .r15 _ rfl).trans hmin
  have e7 : ∀ r ∈ [Reg64.r12, .r14], reg st7.data r = reg st6.data r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Match.reg_eq hfr6.mid_match hm7 rfl rfl
  have w24_7 : WordAt st7.data.dmem (fbOf m0 + BitVec.ofNat 64 24) (.ofBitVec (reg m0 .rdi)) :=
    word_keep (word_keep w24 k6 (by omega) (by omega)) k7a (by omega) (by omega)
  simp only [PcOk] at hpc7
  rw [eval_test, hmin, ofNat_beq hc64 (by decide)] at hpc7
  obtain ⟨hT7, hF7⟩ := Arrays.pc_cond hpc7
  by_cases hc0 : cntOf m0 = 0
  · exact zero_fin hp hpre hA.mu hc0 ((hT7 (by rw [decide_eq_true_eq]; exact hc0)).trans
      (hp.label NativeRustcVmX64.Vm.InducedWeight.label_2_at)) hfr7 w24_7
  have hpc7' : st7.pc = Host.addrOf (k + NativeRustcVmX64.Vm.InducedWeight.b4Offset) := hF7 (by rw [decide_eq_true_eq]; exact hc0)
  -- `b4`: the table's slice, the count, the point
  obtain ⟨hard, hap, -⟩ := args_ok hS hargs
  have hwf8 : (Env.ofMachine st7.data [(stackBelow m0 1168, 1168 + 8), (rspOf m0 + 8#64, 16)]).WF :=
    wf_two (stackOk_mono hS hF) hfr7.kept (Readable.keep hard hfr7.kept) hap
  have hm8 : Match (Env.ofMachine st7.data [(stackBelow m0 1168, 1168 + 8), (rspOf m0 + 8#64, 16)])
      a4S st7.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hfr7.rsp, trivial⟩ trivial trivial
      ⟨fb_args0 m0, trivial⟩
  refine exec_at (hb4 hp) run_b4 hwf8 (by intro l h; cases h) hpc7' hm8 fun st8 hm8' hpc8 ↦ ?_
  obtain ⟨hk8, hsig8, hv40, hv48, hv32⟩ := after_eq run_b4 ▸ b4_write
  have hfr8 := fr_write hS hfr7 hm8 hm8' hwf8 rfl hk8 rfl (by omega) (hw_of hsig8 (by decide))
  have k8a := fkeep_block hm8' hwf8 (m0 := m0) rfl (lo := 0) (hi := 32) (by omega)
    (hall_of hsig8 (by decide))
  have k8b := fkeep_block hm8' hwf8 (m0 := m0) rfl (lo := 56) (hi := 1176) (by omega)
    (hall_of hsig8 (by decide))
  have hr14_7 : (Env.ofMachine st7.data [(stackBelow m0 1168, 1168 + 8), (rspOf m0 + 8#64, 16)]).regs
      .r14 = BitVec.ofNat 64 (tbOf m0).size :=
    (e7 .r14 (by simp)).trans hr14_6
  obtain ⟨hi1, hi2⟩ := ite32 hr14_7 (by omega) (.lit 0) (.reg .r14)
  obtain ⟨-, hi3⟩ := ite32 hr14_7 (by omega) (.reg .r12) (.lit 8)
  have w40 : WordAt st8.data.dmem (fbOf m0 + BitVec.ofNat 64 40) (tbOf m0).size.toUInt64 := by
    have := wordAt_of_write hm8' (r := 0) (o := 40) rfl (by decide) hv40
    rwa [hi1, eval_reg, hr14_7] at this
  have w48 : WordAt st8.data.dmem (fbOf m0 + BitVec.ofNat 64 48) (cntOf m0).toUInt64 := by
    have := wordAt_of_write hm8' (r := 0) (o := 48) rfl (by decide) (v := .reg .r15) hv48
    rwa [eval_reg, Env.ofMachine_regs, show st7.data.regs.get64 .r15 = _ from hr15_7] at this
  have w32 : WordAt st8.data.dmem (fbOf m0 + BitVec.ofNat 64 32)
      (.ofBitVec (fbOf m0 + BitVec.ofNat 64 624)) := by
    have := wordAt_of_write hm8' (r := 0) (o := 32) rfl (by decide) hv32
    rwa [hi3, eval_reg, Env.ofMachine_regs,
      show st7.data.regs.get64 .r12 = _ from (e7 .r12 (by simp)).trans
        ((e6 .r12 (by simp)).trans hr12)] at this
  have hkA : FKeep m0 st.data.dmem st8.data.dmem 56 72 :=
    ((((k5.mono (by omega) (by omega)).trans (k6.mono (by omega) (by omega))).trans
      (k7a.mono (by omega) (by omega))).trans (k8b.mono le_rfl (by omega)))
  simp only [PcOk] at hpc8
  refine cont st8 (hpc8.trans (hp.label NativeRustcVmX64.Vm.InducedWeight.label_6_at)) ⟨hfr8, ⟨?_, ?_, ?_⟩, by omega, hA.mu,
    (hm8'.regs .rsi _ rfl).trans rfl, ?_, ?_, ?_, ?_⟩
  · exact word_keep w24_7 k8a (by omega) (by omega)
  · exact words5 w32 w40 w48 (word_keep hA.w56 hkA (by omega) (by omega))
      (word_keep hA.w64 hkA (by omega) (by omega))
  · refine ⟨by rw [Array.length_toList]; exact hts, ?_, ?_⟩
    · rw [Array.length_toList]
      exact word_keep w616 k8b (by omega) (by omega)
    · unfold PairsAt NativeRustcVm.WordsAt at hpairs6
      unfold PairsAt NativeRustcVm.Transcript.off NativeRustcVm.WordsAt
      rw [addr_add]
      refine bytes_keep (bytes_keep hpairs6 (k7b.mono le_rfl le_rfl) le_rfl ?_) k8b (by omega) ?_
      · rw [pairs_len, Array.length_toList]; omega
      · rw [pairs_len, Array.length_toList]; omega
  · rw [totOf_zero]; exact (hm8'.regs .rcx _ rfl).trans rfl
  · rw [totOf_zero]; exact (hm8'.regs .rax _ rfl).trans rfl
  · exact (hm8'.regs .rdx _ rfl).trans (hi1.trans hr14_7)
  · refine (hm8'.regs .r14 _ rfl).trans ?_
    rw [eval_load]
    exact arg_load (i := 0) hS hargs hfr7 rfl rfl (by omega)

end

end NativeRustcVmX64.Whir.InducedWeight
