module

public import NativeRustcVmX64.Bus.GkrLayers.Exec
public import NativeRustcVmX64.Bus.GkrCommon
public import NativeRustcVmX64.Bus.GkrModel
public import NativeRustcVmX64.Code.Vm.GkrLayers.Names
public import NativeRustcVmX64.Code.Vm.GkrStep.Names
public import NativeRustcX64.Got

/-!
# `gkr_layers` on x86-64

`b0` pushes R15, R14, R12, RBX and RAX (the 48-byte frame: the slots from `16`), sets BL = `1` and
leaves at once when `depth = 0` (`NativeRustcVmX64.Vm.GkrLayers.label_11`, `exit_spec`); else `b1` keeps the `TState` in
R15, the `GkrStateW` in R14, the levels left `n` in R12 and goes to `NativeRustcVmX64.Vm.GkrLayers.label_4` (`Mid n`,
`iter_spec`): one level left, the tail call `gkr_step(t, 1, true, s)` (`b12`, `tail_spec`); `n`
odd, a step of one level (`b8`) and `n - 1` left (`b10`); `n` even, a step of two (`b3`, `last`
when none are left after it) and `n - 2` left (`b5`, or the exit when none are). A failed step
leaves with BL = `0` (`NativeRustcVmX64.Vm.GkrLayers.label_10`, `fail_spec`). `gkrLayers_spec`.
-/

namespace NativeRustcVmX64.Bus.GkrLayers

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.GkrLayers
open NativeRustcVmX64.Transcript NativeRustcVmX64.Sumcheck NativeRustcVmX64.Bus.Gkr
open NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Bus

@[expose] public section

/-- The outputs: the `TState` (RDI) and the `GkrStateW` (RDX). -/
def outs (m0 : MachineData) (q : BitVec 64) : Prop :=
  NativeRustcVm.InRange (reg m0 .rdi) tstateBytes q ∨
    NativeRustcVm.InRange (reg m0 .rdx) gkrStateBytes q

/-- **At `NativeRustcVmX64.Vm.GkrLayers.label_4`**, `n` levels left: the frame, the `TState` (R15) and the `GkrStateW`
(R14) where the walk is, BL = `1`. -/
structure Mid [Labels] (a : DecArea) (s0 : TState) (g0 : GkrStateW) (m0 : MachineData) (n : Nat)
    (d : MachineData) : Prop where
  fr : Fr m0 48 gkrLayersStack slots (outs m0) 8 d
  r12 : (reg d .r12).toNat = n
  r14 : reg d .r14 = reg m0 .rdx
  r15 : reg d .r15 = reg m0 .rdi
  rbx : (reg d .rbx).toNat % 256 = 1
  st : ∃ g s, (gkrLayers (reg m0 .rsi).toNat g0).run s0 = (gkrLayers n g).run s ∧
    TStateAt d.dmem (reg m0 .rdi) a s ∧ GkrStateWAt d.dmem (reg m0 .rdx) g ∧
    g.point.size + n ≤ busPointCap

end

public section

theorem N_eq : gkrLayersStack = 48 + gkrStepStack := rfl
theorem N_ge : 48 ≤ gkrLayersStack := Nat.le_add_right _ _
theorem le_step : 48 - 0 + gkrStepStack ≤ gkrLayersStack := Nat.le_refl _
theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 48 := by decide
theorem slots_cs : ∀ p ∈ slots, calleeSaved p.2 = true := by decide
theorem slots_call : ∀ p ∈ slots, 0 ≤ p.1 ∧ 8 + 0 ≤ p.1 ∧ p.1 + 8 ≤ 48 := by decide

/-! ## Arithmetic -/

theorem eq64_lit (x : BitVec 64) (v : Nat) (hv : v < 2 ^ 64) :
    CmpOp.apply .eq .W64 x (BitVec.ofNat 64 v) = decide (x.toNat = v) := by
  simp only [CmpOp.apply, low_W64]
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← BitVec.toNat_inj, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hv]

theorem test64 (x : BitVec 64) :
    CmpOp.apply .eq .W64 (BinOp.apply .and .W64 x x) (BitVec.ofNat 64 0) = decide (x.toNat = 0) := by
  simp only [BinOp.apply, low_W64, ext_W64, BitVec.and_self]
  exact eq64_lit x 0 (by decide)

theorem and1 (x : BitVec 64) :
    CmpOp.apply .eq .W8 (BinOp.apply .and .W8 x (BitVec.ofNat 64 1)) (BitVec.ofNat 64 0) =
      decide (x.toNat % 2 = 0) := by
  simp only [CmpOp.apply, BinOp.apply, low, ext, Width.bits]
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← BitVec.toNat_inj]
  simp only [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.reducePow,
    Nat.reduceMod]
  rw [Nat.and_one_is_mod]
  omega

theorem sub1 (x : BitVec 64) (h : 1 ≤ x.toNat) :
    (BinOp.apply .sub .W64 x (BitVec.ofNat 64 1)).toNat = x.toNat - 1 := by
  simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := x.isLt
  omega

theorem add_m2 (x : BitVec 64) (h : 2 ≤ x.toNat) :
    (BinOp.apply .add .W64 (BitVec.ofNat 64 18446744073709551614) x).toNat = x.toNat - 2 := by
  simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_add, BitVec.toNat_ofNat]
  have := x.isLt
  omega

theorem merge01 (b : Bool) :
    (BinOp.apply .merge .W8 (BitVec.ofNat 64 0)
      (if b then BitVec.ofNat 64 1 else BitVec.ofNat 64 0)).toNat = if b then 1 else 0 := by
  cases b <;> rfl

theorem decide_ite (b : Bool) : decide ((if b then 1 else 0 : Nat) = 1) = b := by
  cases b <;> rfl

/-- A register a block set to a register's value. -/
theorem reg_of [Labels] {d d' : MachineData} {rs : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    {ret : BitVec 64} {S : SState} {r r' : Reg64} (hm : Match (Env.ofMachine d rs vars ret) S d')
    (h : S.reg r = some (.reg r')) : reg d' r = reg d r' :=
  hm.regs _ _ h

/-- A register a block set to a value. -/
theorem reg_val [Labels] {d d' : MachineData} {rs : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    {ret : BitVec 64} {S : SState} {r : Reg64} {v : Sym} (hm : Match (Env.ofMachine d rs vars ret) S d')
    (h : S.reg r = some v) : reg d' r = v.eval (Env.ofMachine d rs vars ret) :=
  hm.regs _ _ h

section
variable [Labels] {a : DecArea} {s0 : TState} {g0 : GkrStateW} {m0 : MachineData}

theorem pre_gk (h : GkrLayersPre a s0 g0 m0) :
    OutOk m0 (reg m0 .rdi) a (reg m0 .rdx) gkrStateBytes gkrLayersStack := h.2.2.2.2.2.1

theorem pre_got (h : GkrLayersPre a s0 g0 m0) :
    GotAt m0 gkrLayersStack [(reg m0 .rdi, tstateBytes), (a.words, 8 * a.len),
      (reg m0 .rdx, gkrStateBytes), (rcAddr, 192)] ["memcpy"] := h.2.2.2.2.2.2.2

theorem got_pass (h : GkrLayersPre a s0 g0 m0) {d : MachineData} {F : Nat}
    (hs : NativeRustcVm.SameOutside m0.dmem d.dmem
      (fun q => NativeRustcVm.InRange (stackBelow m0 gkrLayersStack) gkrLayersStack q ∨ outs m0 q))
    (hsp : rspOf d = stackBelow m0 F) (hn : F + gkrStepStack ≤ gkrLayersStack) :
    GotAt d gkrStepStack [(reg m0 .rdi, tstateBytes), (a.words, 8 * a.len),
      (reg m0 .rdx, gkrStateBytes), (rcAddr, 192)] ["memcpy"] := by
  refine got_callee (pre_got h) ?_ hsp h.1.1 hn (fun l hl => ((pre_got h).1 l hl).2.2.2)
  refine got_keep (pre_got h) h.1
    (writes := [(reg m0 .rdi, tstateBytes), (reg m0 .rdx, gkrStateBytes)])
    (by intro b hb; simp only [List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl <;> simp)
    (by
      intro b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · exact h.2.2.1.footprint.1.2
      · exact (pre_gk h).2.1)
    (NativeRustcVm.SameOutside.mono hs ?_)
  intro q hq
  rcases hq with hq | hq | hq
  · exact .inr hq
  · exact .inl ⟨(reg m0 .rdi, tstateBytes), by simp, hq⟩
  · exact .inl ⟨(reg m0 .rdx, gkrStateBytes), by simp, hq⟩

/-- The entry's context. -/
theorem ctx (h : GkrLayersPre a s0 g0 m0) : Ctx m0 (reg m0 .rdi) a gkrLayersStack 48 :=
  ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.1.footprint, N_ge⟩

/-- The entry's context, without a frame (the tail call). -/
theorem ctx0 (h : GkrLayersPre a s0 g0 m0) : Ctx m0 (reg m0 .rdi) a gkrLayersStack 0 :=
  ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.1.footprint, Nat.zero_le _⟩

theorem outs_not_rc (h : GkrLayersPre a s0 g0 m0) :
    ∀ q, outs m0 q → ¬ NativeRustcVm.InRange rcAddr 192 q := by
  intro q hq
  have c := ctx h
  rcases hq with hq | hq
  · exact c.not_rc_tstate hq
  · exact c.out_not_rc (pre_gk h) hq

theorem outs_not_frame (h : GkrLayersPre a s0 g0 m0) :
    ∀ q, outs m0 q → ¬ NativeRustcVm.InRange (stackBelow m0 48) (48 + 8) q := by
  intro q hq
  have c := ctx h
  rcases hq with hq | hq
  · exact not_inRange_of_apart (apart_frame c.tok.1 c.spN N_ge) c.fp.1.2 c.noWrap_frame hq
  · exact not_inRange_of_apart (apart_frame (pre_gk h).2.2.2.2.1 c.spN N_ge) (pre_gk h).2.1
      c.noWrap_frame hq

theorem wf0 (h : GkrLayersPre a s0 g0 m0) {d : MachineData} (hk : Kept m0.dmem d.dmem)
    (ret : BitVec 64) : (frameEnv m0 d 48 [] (fun _ ↦ 0) ret).WF := by
  have c := ctx h
  exact frame_wf ⟨c.mapped_frame hk, c.noWrap_frame⟩ (by simp) (List.pairwise_singleton _ _)

omit [Labels] in
theorem match_head [Labels] {d : MachineData} (fr : Fr m0 48 gkrLayersStack slots (outs m0) 8 d)
    (ret : BitVec 64) : Match (frameEnv m0 d 48 [] (fun _ ↦ 0) ret) headS d :=
  match_ofMachine ⟨rfl, trivial⟩ ⟨fr.frame.rsp_eval, trivial⟩ trivial trivial trivial

/-- The `TState` and the `GkrStateW` kept where the memory changed in the frame only. -/
theorem keep_ts_gs (h : GkrLayersPre a s0 g0 m0) {d d' : Mem 64} (hk : Kept d d')
    (hs : NativeRustcVm.SameOutside d d' (NativeRustcVm.InRange (stackBelow m0 48) 48))
    {s : TState} {g : GkrStateW} (hts : TStateAt d (reg m0 .rdi) a s)
    (hgs : GkrStateWAt d (reg m0 .rdx) g) :
    TStateAt d' (reg m0 .rdi) a s ∧ GkrStateWAt d' (reg m0 .rdx) g := by
  have c := ctx h
  exact ⟨hts.frame hk (fun q hq ↦ c.stack_not_t (c.inRange_frame hq)) hs,
    gkrStateWAt_keep hgs hs fun q hq hp ↦ c.out_not_stack (pre_gk h) hp (c.inRange_frame hq)⟩

/-- `Mid` after a block of the body without writes keeping R12, R14, R15, RBX. -/
theorem Mid.block (h : GkrLayersPre a s0 g0 m0) {n : Nat} {d d' : MachineData} {ret : BitVec 64}
    {S : SState} (mid : Mid a s0 g0 m0 n d)
    (hm : Match (frameEnv m0 d 48 [] (fun _ ↦ 0) ret) S d') (hok : BodyOk 8 S = true)
    (hmem : S.mem = []) (hk : Keeps S [.rbx, .r12, .r14, .r15] = true) : Mid a s0 g0 m0 n d' := by
  have hwf := wf0 h mid.fr.frame.kept ret
  simp only [BodyOk, Bool.and_eq_true] at hok
  have fr' := (mid.fr.block0 h.1 N_ge hwf hm hok.1 slots_le (by simp [hmem])).1
  have hd : d'.dmem = d.dmem := hm.dmem_eq hwf hmem
  simp only [Keeps, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    beq_iff_eq] at hk
  obtain ⟨g, s, hrun, hts, hgs, hsz⟩ := mid.st
  refine ⟨fr', ?_, (hm.regs _ _ hk.2.2.1).trans mid.r14, (hm.regs _ _ hk.2.2.2).trans mid.r15,
    ?_, g, s, hrun, by rw [hd]; exact hts, by rw [hd]; exact hgs, hsz⟩
  · rw [show reg d' .r12 = reg d .r12 from hm.regs _ _ hk.2.1]; exact mid.r12
  · rw [show reg d' .rbx = reg d .rbx from hm.regs _ _ hk.1]; exact mid.rbx

end

section
variable [Host] {a : DecArea} {s0 : TState} {g0 : GkrStateW} {m0 : MachineData} {k : Nat}

/-- What `gkr_layers` reaches. -/
abbrev Goal (a : DecArea) (s0 : TState) (g0 : GkrStateW) (m0 : MachineData) (st : MachineState) :
    Prop :=
  st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧ GkrLayersPost a s0 g0 m0 st.data

/-- **The exit** (`NativeRustcVmX64.Vm.GkrLayers.label_11`, `b14`): AL = BL. -/
theorem exit_spec (hp : Placed code k) (h : GkrLayersPre a s0 g0 m0) {d : MachineData}
    (fr : Fr m0 48 gkrLayersStack slots (outs m0) 8 d)
    (hbx : (reg d .rbx).toNat % 256 =
      (okWord ((gkrLayers (reg m0 .rsi).toNat g0).run s0).isSome).toNat)
    (hok : ∀ g' s', (gkrLayers (reg m0 .rsi).toNat g0).run s0 = some (g', s') →
      TStateAt d.dmem (reg m0 .rdi) a s' ∧ GkrStateWAt d.dmem (reg m0 .rdx) g') :
    Eventually (step1 Host.exe) (Goal a s0 g0 m0) ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.GkrLayers.b14Offset)⟩ := by
  have hwf := wf0 h fr.frame.kept 0
  obtain ⟨hepi, hmem, hrax⟩ := ok_b14
  refine fr.exit h.1 N_ge (infix_of b14_in_code (by simp [b14]) hp) exit_b14 hwf rfl
    (match_head fr 0) hepi (fun q hw ↦ ?_)
    fun st hm hpc hrsp hsame _ hsv ↦ .done _ ⟨hpc, hrsp, ?_, ?_, ?_, hsv⟩
  · obtain ⟨w, hw, -⟩ := hw
    rw [hmem] at hw
    cases hw
  · show (reg st.data .rax).toNat % 256 = _
    rw [reg_val hm hrax]
    show (UnOp.apply .trunc .W32 (reg d .rbx)).toNat % 256 = _
    rw [trunc32_mod, hbx]
  · intro g' s' he
    rw [hm.dmem_eq hwf hmem]
    exact hok g' s' he
  · exact NativeRustcVm.SameOutside.mono hsame fun q hq ↦ by
      rcases hq with hq | hq | hq
      · exact .inr (.inr hq)
      · exact .inl hq
      · exact .inr (.inl hq)

/-- **A failed step** (`NativeRustcVmX64.Vm.GkrLayers.label_10`, `b13`): BL = `0`, then the exit. -/
theorem fail_spec (hp : Placed code k) (h : GkrLayersPre a s0 g0 m0) {d : MachineData}
    (fr : Fr m0 48 gkrLayersStack slots (outs m0) 8 d)
    (hr : (gkrLayers (reg m0 .rsi).toNat g0).run s0 = none) :
    Eventually (step1 Host.exe) (Goal a s0 g0 m0) ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.GkrLayers.b13Offset)⟩ := by
  have hwf := wf0 h fr.frame.kept 0
  obtain ⟨hok, hmem, hbx⟩ := ok_b13
  simp only [BodyOk, Bool.and_eq_true] at hok
  refine exec_then (infix_of b13_in_code (by simp [b13]) hp) exit_b13 hwf nofun
    (match_head fr 0) fun st hm hpc ↦ ?_
  have fr' := (fr.block0 h.1 N_ge hwf hm hok.1 slots_le (by simp [hmem])).1
  simp only [PcOk] at hpc
  refine at_pc (hpc.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.GkrLayers.b13_next))
    (exit_spec hp h fr' ?_ fun g' s' he ↦ by rw [hr] at he; cases he)
  rw [hr, show reg st.data .rbx = BitVec.ofNat 64 0 from hm.regs _ _ hbx]
  rfl

/-- **One level left** (`NativeRustcVmX64.Vm.GkrLayers.label_8`, `b12`): the tail call `gkr_step(t, 1, true, s)`. -/
theorem tail_spec (hp : Placed code k) (h : GkrLayersPre a s0 g0 m0)
    (hstep : ∀ s g, Spec (Labels.label NativeRustcVmX64.Vm.GkrStep.entryLabel) (GkrStepPre a s g) (GkrStepPost a s g))
    {d : MachineData} (mid : Mid a s0 g0 m0 1 d) :
    Eventually (step1 Host.exe) (Goal a s0 g0 m0) ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.GkrLayers.b12Offset)⟩ := by
  have hwf := wf0 h mid.fr.frame.kept 0
  have c0 := ctx0 h
  obtain ⟨hl, hko, hsp, hmem, hdi, hsi, hdx, hcx⟩ := ok_b12
  refine exec_then (infix_of b12_in_code (by simp [b12]) hp) exit_b12 hwf nofun
    (match_head mid.fr 0) fun st hm hpc ↦ ?_
  simp only [PcOk] at hpc
  obtain ⟨hsv, hrsp⟩ := Frame.tail mid.fr.frame hwf hm hl hko hsp
  have hd : st.data.dmem = d.dmem := hm.dmem_eq hwf hmem
  have hret : retOf st.data = retOf m0 := retOf_of mid.fr.frame hd hrsp
  obtain ⟨g, s, hrun, hts, hgs, hsz⟩ := mid.st
  have hsame0 : NativeRustcVm.SameOutside m0.dmem st.data.dmem
      (fun q ↦ NativeRustcVm.InRange (stackBelow m0 gkrLayersStack) gkrLayersStack q ∨ outs m0 q) := by
    rw [hd]; exact mid.fr.same
  have hat : At m0 0 st.data :=
    ⟨by rw [hrsp]; simp [stackBelow], hsv.2,
      rc_keep hsame0 fun q hq ↦ hq.elim (fun hq ↦ c0.not_rc_stack hq) (outs_not_rc h q)⟩
  have hle : 0 + gkrStepStack ≤ gkrLayersStack := by rw [N_eq]; omega
  have edi : reg st.data .rdi = reg m0 .rdi := (hm.regs _ _ hdi).trans mid.r15
  have ecx : reg st.data .rcx = reg m0 .rdx := (hm.regs _ _ hcx).trans mid.r14
  have esi : (reg st.data .rsi).toNat = 1 := by rw [reg_val hm hsi]; rfl
  have edx : (reg st.data .rdx).toNat = 1 := by rw [reg_val hm hdx]; rfl
  have hpre : GkrStepPre a s g st.data := by
    unfold GkrStepPre GkrOk
    rw [edi, ecx, esi, edx]
    exact ⟨c0.stackOk hat hle, c0.rcAt hat hle, by rw [hd]; exact hts, c0.tstateOk hat hle,
      .inl rfl, Nat.le_refl _, by omega, c0.outOk hat hle (pre_gk h),
      by rw [hd]; exact hgs, got_pass h hsame0 hat.sp hle⟩
  refine Eventually.mono (Spec.apply (hstep s g) hpc hpre) fun st' ⟨hpc', hrsp', hq⟩ ↦ ?_
  obtain ⟨hal, hok, hso, hsv'⟩ := hq
  rw [esi, edx] at hal hok
  rw [edi, ecx] at hok hso
  have e1 : (gkrStep 1 (decide (1 = 1)) g).run s = (gkrLayers (reg m0 .rsi).toNat g0).run s0 := by
    rw [hrun, gkrLayers_one]; rfl
  rw [e1] at hal hok
  refine ⟨hpc'.trans hret, by rw [hrsp', hrsp], hal, hok, ?_, hsv.trans hsv'⟩
  refine NativeRustcVm.SameOutside.mono (hsame0.trans hso) fun q hq ↦ ?_
  rcases hq with (hq | hq | hq) | hq | hq | hq
  · exact .inr (.inr hq)
  · exact .inl hq
  · exact .inr (.inl hq)
  · exact .inl hq
  · exact .inr (.inl hq)
  · exact .inr (.inr (c0.inRange_callee hat hle hq).1)

/-- **A call of `gkr_step(t, j, last, s)`** from the frame. -/
theorem step_call (h : GkrLayersPre a s0 g0 m0)
    (hstep : ∀ s g, Spec (Labels.label NativeRustcVmX64.Vm.GkrStep.entryLabel) (GkrStepPre a s g) (GkrStepPost a s g))
    {st : MachineState} {next : Int64} {R : MachineState → Prop}
    (fr : Fr m0 48 gkrLayersStack slots (outs m0) 0 st.data)
    (hpc : st.pc = Labels.label NativeRustcVmX64.Vm.GkrStep.entryLabel ∧ retOf st.data = next)
    (hdi : reg st.data .rdi = reg m0 .rdi) (hcx : reg st.data .rcx = reg m0 .rdx) {j : Nat}
    (hsi : (reg st.data .rsi).toNat = j) (hj : j = 1 ∨ j = 2) {last : Bool}
    (hdx : (reg st.data .rdx).toNat = if last then 1 else 0) {g : GkrStateW} {s : TState}
    (hsz : g.point.size + j ≤ busPointCap) (hts : TStateAt st.data.dmem (reg m0 .rdi) a s)
    (hgs : GkrStateWAt st.data.dmem (reg m0 .rdx) g)
    (cont : ∀ m2 : MachineData, Fr m0 48 gkrLayersStack slots (outs m0) 8 m2 →
      OkAl m2 ((gkrStep j last g).run s).isSome →
      (∀ g' s', (gkrStep j last g).run s = some (g', s') →
        TStateAt m2.dmem (reg m0 .rdi) a s' ∧ GkrStateWAt m2.dmem (reg m0 .rdx) g') →
      (∀ r, calleeSaved r = true → m2.regs.get64 r = st.data.regs.get64 r) →
      Eventually (step1 Host.exe) R ⟨m2, next⟩) :
    Eventually (step1 Host.exe) R st := by
  have c := ctx h
  have hat : At m0 48 st.data := fr.at_ c (by omega) (outs_not_rc h)
  refine fr.call (c := 0) (Nc := gkrStepStack) (lo := 8) (len := 0) (X := outs m0)
    h.1 N_ge (by omega) le_step slots_call (by omega) (outs_not_frame h) (fun q hq ↦ .inl hq)
    (hstep s g) hpc ?_ (fun m' hq ↦ ⟨?_, hq.2.2.2⟩) fun m2 fr2 hq _ hcs ↦ ?_
  · unfold GkrStepPre GkrOk
    rw [hdi, hcx, hsi, hdx]
    exact ⟨c.stackOk hat le_step, c.rcAt hat le_step, hts, c.tstateOk hat le_step, hj,
      by split <;> omega, hsz, c.outOk hat le_step (pre_gk h), hgs,
      got_pass h fr.same hat.sp le_step⟩
  · have := hq.2.2.1
    rw [hdi, hcx] at this
    exact NativeRustcVm.SameOutside.mono this fun q hq ↦ by
      rcases hq with hq | hq | hq
      · exact .inr (.inl hq)
      · exact .inr (.inr hq)
      · exact .inl hq
  · obtain ⟨hal, hok, -, -⟩ := hq
    rw [hsi, hdx, decide_ite] at hal hok
    rw [hdi, hcx] at hok
    exact cont m2 fr2 hal hok hcs

/-- The walk's state after a step: `n'` levels left of the state the step reached. -/
def After (a : DecArea) (s0 : TState) (g0 : GkrStateW) (m0 : MachineData) (n' : Nat)
    (d : MachineData) : Prop :=
  ∃ g s, (gkrLayers (reg m0 .rsi).toNat g0).run s0 = (gkrLayers n' g).run s ∧
    TStateAt d.dmem (reg m0 .rdi) a s ∧ GkrStateWAt d.dmem (reg m0 .rdx) g ∧
    g.point.size + n' ≤ busPointCap

/-- **A step's result tested** (`b4`, `b9`: `test %al, %al`): a failure leaves with `0`, else
the walk goes on, `n'` levels left. -/
theorem tested (hp : Placed code k) (h : GkrLayersPre a s0 g0 m0) {ds : List Directive}
    {j : Nat} {S' : SState} (hk : ds.IsInfixAt Host.prog j)
    (hx : exec ds headS = some (S', .cond cAl NativeRustcVmX64.Vm.GkrLayers.label_10))
    (hok : BodyOk 8 S' = true) (hmem : S'.mem = []) (hkp : Keeps S' [.rbx, .r12, .r14, .r15] = true)
    {d : MachineData} (fr : Fr m0 48 gkrLayersStack slots (outs m0) 8 d)
    {r : Option (GkrStateW × TState)} (hal : OkAl d r.isSome)
    (hres : ∀ g' s', r = some (g', s') → TStateAt d.dmem (reg m0 .rdi) a s' ∧
      GkrStateWAt d.dmem (reg m0 .rdx) g')
    {n' : Nat} (hrun : (gkrLayers (reg m0 .rsi).toNat g0).run s0 =
      r.bind fun p ↦ (gkrLayers n' p.1).run p.2)
    (hsz : ∀ g' s', r = some (g', s') → g'.point.size + n' ≤ busPointCap)
    {R : MachineState → Prop} (hR : ∀ st, Goal a s0 g0 m0 st → R st)
    (cont : ∀ st : MachineState, st.pc = Host.addrOf (j + ds.length) →
      Fr m0 48 gkrLayersStack slots (outs m0) 8 st.data →
      (∀ q ∈ [Reg64.rbx, .r12, .r14, .r15], reg st.data q = reg d q) →
      After a s0 g0 m0 n' st.data → Eventually (step1 Host.exe) R st) :
    Eventually (step1 Host.exe) R ⟨d, Host.addrOf j⟩ := by
  have hwf := wf0 h fr.frame.kept 0
  refine exec_then hk hx hwf nofun (match_head fr 0) fun st hm hpc ↦ ?_
  simp only [BodyOk, Bool.and_eq_true] at hok
  have fr' := (fr.block0 h.1 N_ge hwf hm hok.1 slots_le (by simp [hmem])).1
  have hd : st.data.dmem = d.dmem := hm.dmem_eq hwf hmem
  simp only [Keeps, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    beq_iff_eq] at hkp
  have hc : SBool.eval (frameEnv m0 d 48 [] (fun _ ↦ 0) 0) cAl = !r.isSome := testAl_okAl hal
  simp only [PcOk, hc] at hpc
  cases hr : r with
  | none =>
    simp only [hr, Option.isSome_none, Bool.not_false, ↓reduceIte] at hpc
    exact at_pc (hpc.trans (hp.label NativeRustcVmX64.Vm.GkrLayers.label_10_at))
      (Eventually.mono (fail_spec hp h fr' (by rw [hrun, hr]; rfl)) hR)
  | some p =>
    obtain ⟨g', s'⟩ := p
    simp only [hr, Option.isSome_some, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc
    obtain ⟨hts, hgs⟩ := hres g' s' hr
    refine cont st hpc fr' (fun q hq ↦ ?_) ⟨g', s', by rw [hrun, hr]; rfl, by rw [hd]; exact hts,
      by rw [hd]; exact hgs, hsz g' s' hr⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact hm.regs _ _ hkp.1
    · exact hm.regs _ _ hkp.2.1
    · exact hm.regs _ _ hkp.2.2.1
    · exact hm.regs _ _ hkp.2.2.2

/-- A call block (`b3`, `b8`) from `Mid n`: the frame at offset `0`, the `TState` and the
`GkrStateW` kept. -/
theorem call_block (h : GkrLayersPre a s0 g0 m0) {n : Nat} {d : MachineData}
    (mid : Mid a s0 g0 m0 n d) {S' : SState} {ret : BitVec 64} {d' : MachineData}
    (hm : Match (frameEnv m0 d 48 [] (fun _ ↦ 0) ret) S' d') (hok : BodyOk 0 S' = true) :
    Fr m0 48 gkrLayersStack slots (outs m0) 0 d' ∧
      ∃ g s, (gkrLayers (reg m0 .rsi).toNat g0).run s0 = (gkrLayers n g).run s ∧
        TStateAt d'.dmem (reg m0 .rdi) a s ∧ GkrStateWAt d'.dmem (reg m0 .rdx) g ∧
        g.point.size + n ≤ busPointCap := by
  have hwf := wf0 h mid.fr.frame.kept ret
  simp only [BodyOk, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hok
  obtain ⟨fr', hs⟩ := mid.fr.block0 h.1 N_ge hwf hm hok.1 slots_le fun w hw ↦ (hok.2 w hw).1
  obtain ⟨g, s, hrun, hts, hgs, hsz⟩ := mid.st
  obtain ⟨hts', hgs'⟩ := keep_ts_gs h (hm.kept hwf) hs hts hgs
  exact ⟨fr', g, s, hrun, hts', hgs', hsz⟩

/-- **An odd number `n ≥ 3` of levels left** (`b8` to `b10`): a step of one level, `n - 1`
left. -/
theorem odd_spec (hp : Placed code k) (h : GkrLayersPre a s0 g0 m0)
    (hstep : ∀ s g, Spec (Labels.label NativeRustcVmX64.Vm.GkrStep.entryLabel) (GkrStepPre a s g) (GkrStepPost a s g))
    {n : Nat} (hn : n % 2 = 1) (hn1 : n ≠ 1) {d : MachineData} (mid : Mid a s0 g0 m0 n d) :
    Eventually (step1 Host.exe) (fun st ↦ Goal a s0 g0 m0 st ∨
      (st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.GkrLayers.b6Offset) ∧ Mid a s0 g0 m0 (n - 1) st.data))
      ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.GkrLayers.b8Offset)⟩ := by
  have hwf := wf0 h mid.fr.frame.kept (Host.addrOf (k + NativeRustcVmX64.Vm.GkrLayers.b8Offset + b8.length)).toBitVec
  obtain ⟨hok, hdi, hsi, hdx, hcx, hkp⟩ := ok_b8
  refine exec_then (infix_of b8_in_code (by simp [b8]) hp) exit_b8 hwf (fun _ _ ↦ rfl)
    (match_head mid.fr _) fun st hm hpc ↦ ?_
  obtain ⟨fr1, g, s, hrun, hts, hgs, hsz⟩ := call_block h mid hm hok
  simp only [Keeps, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    beq_iff_eq] at hkp
  obtain ⟨m', hn'⟩ : ∃ m', n = m' + 2 := ⟨n - 2, by omega⟩
  subst hn'
  have hm' : m' % 2 = 1 := by omega
  refine step_call h hstep fr1 hpc ((hm.regs _ _ hdi).trans mid.r15)
    ((hm.regs _ _ hcx).trans mid.r14) (j := 1)
    (by rw [reg_val hm hsi]; rfl) (.inl rfl) (last := false)
    (by rw [reg_val hm hdx]; rfl) (by omega) hts hgs
    fun m2 fr2 hal hres hcs ↦ ?_
  have e12 : reg m2 .r12 = reg d .r12 := (hcs .r12 rfl).trans (hm.regs _ _ hkp.2.1)
  have e14 : reg m2 .r14 = reg d .r14 := (hcs .r14 rfl).trans (hm.regs _ _ hkp.2.2.1)
  have e15 : reg m2 .r15 = reg d .r15 := (hcs .r15 rfl).trans (hm.regs _ _ hkp.2.2.2)
  have ebx : reg m2 .rbx = reg d .rbx := (hcs .rbx rfl).trans (hm.regs _ _ hkp.1)
  obtain ⟨hok9, hmem9, hk9⟩ := ok_b9
  refine tested hp h (infix_of b9_in_code (by simp [b9]) hp) exit_b9 hok9 hmem9
    hk9 fr2 hal hres (n' := m' + 1) (by rw [hrun, gkrLayers_odd hm'])
    (fun g' s' he ↦ by have := (gkrStep_size (by omega) he).1; omega) (fun _ h ↦ .inl h)
    fun st9 hpc9 fr9 hr9 haft ↦ ?_
  -- `b10`: one level less.
  have hwf10 := wf0 h fr9.frame.kept 0
  obtain ⟨hok10, hmem10, h1210, hk10⟩ := ok_b10
  simp only [BodyOk, Bool.and_eq_true] at hok10
  refine exec_at (infix_of b10_in_code (by simp [b10]) hp) exit_b10 hwf10 nofun
    (hpc9.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.GkrLayers.b9_next)) (match_head fr9 0) fun st10 hm10 hpc10 ↦ ?_
  have fr10 := (fr9.block0 h.1 N_ge hwf10 hm10 hok10.1 slots_le (by simp [hmem10])).1
  have hd10 : st10.data.dmem = st9.data.dmem := hm10.dmem_eq hwf10 hmem10
  simp only [Keeps, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    beq_iff_eq] at hk10
  have r12' : (reg st9.data .r12).toNat = m' + 2 := by
    rw [hr9 .r12 (by simp), e12]; exact mid.r12
  have e1210 : (reg st10.data .r12).toNat = m' + 1 := by
    rw [reg_val hm10 h1210]
    show (BinOp.apply .sub .W64 (reg st9.data .r12) (BitVec.ofNat 64 1)).toNat = _
    rw [sub1 _ (by omega), r12']
    omega
  have hc : SBool.eval (frameEnv m0 st9.data 48 [] (fun _ ↦ 0) 0)
      (SBool.cmp .eq .W64 (.bin .and .W64 subOne subOne) (.lit 0)).not = true := by
    show (!CmpOp.apply .eq .W64 (BinOp.apply .and .W64
      (BinOp.apply .sub .W64 (reg st9.data .r12) (BitVec.ofNat 64 1))
      (BinOp.apply .sub .W64 (reg st9.data .r12) (BitVec.ofNat 64 1))) (BitVec.ofNat 64 0)) = true
    rw [test64, sub1 _ (by omega), r12']
    simp
  simp only [PcOk, hc, ↓reduceIte] at hpc10
  obtain ⟨g', s', hrun', hts', hgs', hsz'⟩ := haft
  refine .done _ (.inr ⟨hpc10.trans (hp.label NativeRustcVmX64.Vm.GkrLayers.label_4_at),
    ⟨fr10, by rw [e1210]; omega, ?_, ?_, ?_, g', s', hrun', by rw [hd10]; exact hts',
      by rw [hd10]; exact hgs', hsz'⟩⟩)
  · rw [reg_of hm10 hk10.2.1, hr9 .r14 (by simp), e14]
    exact mid.r14
  · rw [reg_of hm10 hk10.2.2, hr9 .r15 (by simp), e15]
    exact mid.r15
  · rw [reg_of hm10 hk10.1, hr9 .rbx (by simp), ebx]
    exact mid.rbx

/-- **An even number `n ≥ 2` of levels left** (`b3` to `b5`): a step of two levels, `last` when
none are left after it, `n - 2` left. -/
theorem even_spec (hp : Placed code k) (h : GkrLayersPre a s0 g0 m0)
    (hstep : ∀ s g, Spec (Labels.label NativeRustcVmX64.Vm.GkrStep.entryLabel) (GkrStepPre a s g) (GkrStepPost a s g))
    {n : Nat} (hn : n % 2 = 0) (hn0 : n ≠ 0) {d : MachineData} (mid : Mid a s0 g0 m0 n d) :
    Eventually (step1 Host.exe) (fun st ↦ Goal a s0 g0 m0 st ∨
      (st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.GkrLayers.b6Offset) ∧ n - 2 ≠ 0 ∧ Mid a s0 g0 m0 (n - 2) st.data))
      ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.GkrLayers.b3Offset)⟩ := by
  have hwf := wf0 h mid.fr.frame.kept (Host.addrOf (k + NativeRustcVmX64.Vm.GkrLayers.b3Offset + b3.length)).toBitVec
  obtain ⟨hok, hdi, hsi, hdx, hcx, h12, hkp⟩ := ok_b3
  refine exec_then (infix_of b3_in_code (by simp [b3]) hp) exit_b3 hwf (fun _ _ ↦ rfl)
    (match_head mid.fr _) fun st hm hpc ↦ ?_
  obtain ⟨fr1, g, s, hrun, hts, hgs, hsz⟩ := call_block h mid hm hok
  simp only [Keeps, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    beq_iff_eq] at hkp
  obtain ⟨m', hn'⟩ : ∃ m', n = m' + 2 := ⟨n - 2, by omega⟩
  subst hn'
  have hm' : m' % 2 = 0 := by omega
  have r12d := mid.r12
  have e12 : (reg st.data .r12).toNat = m' := by
    rw [reg_val hm h12]
    show (BinOp.apply .add .W64 (BitVec.ofNat 64 18446744073709551614) (reg d .r12)).toNat = _
    rw [add_m2 _ (by omega), r12d]
    rfl
  have edx : (reg st.data .rdx).toNat = if decide (m' = 0) then 1 else 0 := by
    rw [reg_val hm hdx]
    show (BinOp.apply .merge .W8 (BitVec.ofNat 64 0)
      (if CmpOp.apply .eq .W64 (BinOp.apply .add .W64 (BitVec.ofNat 64 18446744073709551614)
        (reg d .r12)) (BitVec.ofNat 64 0) then BitVec.ofNat 64 1 else BitVec.ofNat 64 0)).toNat = _
    rw [eq64_lit _ 0 (by decide), add_m2 _ (by omega), r12d, merge01]
    simp
  refine step_call h hstep fr1 hpc ((hm.regs _ _ hdi).trans mid.r15)
    ((hm.regs _ _ hcx).trans mid.r14) (j := 2)
    (by rw [reg_val hm hsi]; rfl) (.inr rfl) edx (by omega) hts hgs
    fun m2 fr2 hal hres hcs ↦ ?_
  have e12' : reg m2 .r12 = reg st.data .r12 := hcs .r12 rfl
  have e14 : reg m2 .r14 = reg d .r14 := (hcs .r14 rfl).trans (hm.regs _ _ hkp.2.1)
  have e15 : reg m2 .r15 = reg d .r15 := (hcs .r15 rfl).trans (hm.regs _ _ hkp.2.2)
  have ebx : reg m2 .rbx = reg d .rbx := (hcs .rbx rfl).trans (hm.regs _ _ hkp.1)
  obtain ⟨hok4, hmem4, hk4⟩ := ok_b4
  refine tested hp h (infix_of b4_in_code (by simp [b4]) hp) exit_b4 hok4 hmem4
    hk4 fr2 hal hres (n' := m') (by rw [hrun, gkrLayers_even hm'])
    (fun g' s' he ↦ by have := (gkrStep_size (by omega) he).1; omega) (fun _ h ↦ .inl h)
    fun st4 hpc4 fr4 hr4 haft ↦ ?_
  -- `b5`: none left?
  have hwf5 := wf0 h fr4.frame.kept 0
  obtain ⟨hok5, hmem5, hk5⟩ := ok_b5
  simp only [BodyOk, Bool.and_eq_true] at hok5
  refine exec_at (infix_of b5_in_code (by simp [b5]) hp) exit_b5 hwf5 nofun
    (hpc4.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.GkrLayers.b4_next)) (match_head fr4 0) fun st5 hm5 hpc5 ↦ ?_
  have fr5 := (fr4.block0 h.1 N_ge hwf5 hm5 hok5.1 slots_le (by simp [hmem5])).1
  have hd5 : st5.data.dmem = st4.data.dmem := hm5.dmem_eq hwf5 hmem5
  simp only [Keeps, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    beq_iff_eq] at hk5
  have r12' : (reg st4.data .r12).toNat = m' := by rw [hr4 .r12 (by simp), e12', e12]
  have hc : SBool.eval (frameEnv m0 st4.data 48 [] (fun _ ↦ 0) 0)
      (.cmp .eq .W64 (.bin .and .W64 (.reg .r12) (.reg .r12)) (.lit 0)) = decide (m' = 0) := by
    show CmpOp.apply .eq .W64 (BinOp.apply .and .W64 (reg st4.data .r12) (reg st4.data .r12))
      (BitVec.ofNat 64 0) = _
    rw [test64, r12']
  simp only [PcOk, hc] at hpc5
  obtain ⟨g', s', hrun', hts', hgs', hsz'⟩ := haft
  by_cases h0 : m' = 0
  · subst h0
    simp only [decide_true, ↓reduceIte] at hpc5
    rw [gkrLayers_zero] at hrun'
    refine at_pc (hpc5.trans (hp.label NativeRustcVmX64.Vm.GkrLayers.label_11_at)) (Eventually.mono
      (exit_spec hp h fr5 ?_ fun g2 s2 he ↦ ?_) fun _ h ↦ .inl h)
    · rw [hrun', reg_of hm5 hk5.1, hr4 .rbx (by simp), ebx]
      exact mid.rbx
    · rw [hrun'] at he
      cases he
      rw [hd5]
      exact ⟨hts', hgs'⟩
  · simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc5
    refine .done _ (.inr ⟨hpc5.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.GkrLayers.b5_next), by omega,
      ⟨fr5, by rw [reg_of hm5 hk5.2.1, r12']; omega, ?_, ?_, ?_,
        g', s', by simpa using hrun', by rw [hd5]; exact hts', by rw [hd5]; exact hgs',
        by simpa using hsz'⟩⟩)
    · rw [reg_of hm5 hk5.2.2.1, hr4 .r14 (by simp), e14]
      exact mid.r14
    · rw [reg_of hm5 hk5.2.2.2, hr4 .r15 (by simp), e15]
      exact mid.r15
    · rw [reg_of hm5 hk5.1, hr4 .rbx (by simp), ebx]
      exact mid.rbx

/-- **At `NativeRustcVmX64.Vm.GkrLayers.label_4`** (`b6`, `b7`), `n ≥ 1` levels left: the tail call, an odd or an even
step. -/
theorem iter_spec (hp : Placed code k) (h : GkrLayersPre a s0 g0 m0)
    (hstep : ∀ s g, Spec (Labels.label NativeRustcVmX64.Vm.GkrStep.entryLabel) (GkrStepPre a s g) (GkrStepPost a s g))
    {n : Nat} (hn : 1 ≤ n) {d : MachineData} (mid : Mid a s0 g0 m0 n d) :
    Eventually (step1 Host.exe) (fun st ↦ Goal a s0 g0 m0 st ∨
      ∃ n' < n, 1 ≤ n' ∧ st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.GkrLayers.b6Offset) ∧ Mid a s0 g0 m0 n' st.data)
      ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.GkrLayers.b6Offset)⟩ := by
  have hwf := wf0 h mid.fr.frame.kept 0
  obtain ⟨hok6, hmem6, hk6⟩ := ok_b6
  refine exec_then (infix_of b6_in_code (by simp [b6]) hp) exit_b6 hwf nofun
    (match_head mid.fr 0) fun st6 hm6 hpc6 ↦ ?_
  have mid6 := mid.block h hm6 hok6 hmem6 hk6
  have hc6 : SBool.eval (frameEnv m0 d 48 [] (fun _ ↦ 0) 0)
      (.cmp .eq .W64 (.reg .r12) (.lit 1)) = decide (n = 1) := by
    show CmpOp.apply .eq .W64 (reg d .r12) (BitVec.ofNat 64 1) = _
    rw [eq64_lit _ 1 (by decide), mid.r12]
  simp only [PcOk, hc6] at hpc6
  by_cases h1 : n = 1
  · subst h1
    simp only [decide_true, ↓reduceIte] at hpc6
    exact at_pc (hpc6.trans (hp.label NativeRustcVmX64.Vm.GkrLayers.label_8_at))
      (Eventually.mono (tail_spec hp h hstep mid6) fun _ h ↦ .inl h)
  simp only [h1, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc6
  have hwf7 := wf0 h mid6.fr.frame.kept 0
  obtain ⟨hok7, hmem7, hk7⟩ := ok_b7
  refine exec_at (infix_of b7_in_code (by simp [b7]) hp) exit_b7 hwf7 nofun
    (hpc6.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.GkrLayers.b6_next)) (match_head mid6.fr 0)
    fun st7 hm7 hpc7 ↦ ?_
  have mid7 := mid6.block h hm7 hok7 hmem7 hk7
  have hc7 : SBool.eval (frameEnv m0 st6.data 48 [] (fun _ ↦ 0) 0)
      (.cmp .eq .W8 (.bin .and .W8 (.reg .r12) (.lit 1)) (.lit 0)) = decide (n % 2 = 0) := by
    show CmpOp.apply .eq .W8 (BinOp.apply .and .W8 (reg st6.data .r12) (BitVec.ofNat 64 1))
      (BitVec.ofNat 64 0) = _
    rw [and1, mid6.r12]
  simp only [PcOk, hc7] at hpc7
  by_cases he : n % 2 = 0
  · simp only [he, decide_true, ↓reduceIte] at hpc7
    refine at_pc (hpc7.trans (hp.label NativeRustcVmX64.Vm.GkrLayers.label_2_at))
      (Eventually.mono (even_spec hp h hstep he (by omega) mid7) fun st hs ↦ ?_)
    rcases hs with hs | ⟨hpc, hne, hmid⟩
    · exact .inl hs
    · exact .inr ⟨n - 2, by omega, by omega, hpc, hmid⟩
  · simp only [he, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc7
    refine at_pc (hpc7.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.GkrLayers.b7_next))
      (Eventually.mono (odd_spec hp h hstep (by omega) h1 mid7) fun st hs ↦ ?_)
    rcases hs with hs | ⟨hpc, hmid⟩
    · exact .inl hs
    · exact .inr ⟨n - 1, by omega, by omega, hpc, hmid⟩

/-- **`gkr_layers`'s contract.** -/
theorem gkrLayers_spec (hp : Placed code k)
    (hstep : ∀ s g, Spec (Labels.label NativeRustcVmX64.Vm.GkrStep.entryLabel) (GkrStepPre a s g) (GkrStepPost a s g)) :
    Spec (Labels.label NativeRustcVmX64.Vm.GkrLayers.entryLabel) (GkrLayersPre a s0 g0) (GkrLayersPost a s0 g0) := by
  intro m0 h
  have hS := h.1
  unfold NativeRustcVmX64.Vm.GkrLayers.entryLabel
  rw [hp.label NativeRustcVmX64.Vm.GkrLayers.entry_at]
  have hwf0 := wf0 h (d := m0) (fun _ h ↦ h) 0
  obtain ⟨hpro, hw0, hbx0, hk0⟩ := ok_b0
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) exit_b0 hwf0 nofun
    (match_ofMachine ⟨rfl, trivial⟩ ⟨match_rsp, trivial⟩ trivial trivial trivial)
    fun st1 hm1 hpc1 ↦ ?_
  have hw0' : ∀ w ∈ (after b0 entryS).mem, w.r = 0 := fun w hw ↦ (hw0 w hw).1
  have fr1 : Fr m0 48 gkrLayersStack slots (outs m0) 8 st1.data :=
    Fr.of_prologue hS N_ge hwf0 hm1 hpro slots_le slots_cs hw0'
  have hs1 : NativeRustcVm.SameOutside m0.dmem st1.data.dmem
      (NativeRustcVm.InRange (stackBelow m0 48) 48) :=
    fun q hq ↦ hm1.get?_mem0 hwf0 fun hw ↦ hq (written_fb hS N_ge (fun w hw ↦ ⟨hw0' w hw,
      belowRet_spec (belowRet_of_pro hpro) w hw (hw0' w hw)⟩) hw)
  obtain ⟨hts1, hgs1⟩ := keep_ts_gs h (hm1.kept hwf0) hs1 h.2.2.1 h.2.2.2.2.2.2.1
  have hbx1 : (reg st1.data .rbx).toNat % 256 = 1 := by
    rw [reg_val hm1 hbx0]; exact merge_one_mod _
  simp only [Keeps, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    beq_iff_eq] at hk0
  have hc : SBool.eval (frameEnv m0 m0 48 [] (fun _ ↦ 0) 0)
      (.cmp .eq .W64 (.bin .and .W64 (.reg .rsi) (.reg .rsi)) (.lit 0)) =
        decide ((reg m0 .rsi).toNat = 0) := by
    show CmpOp.apply .eq .W64 (BinOp.apply .and .W64 (reg m0 .rsi) (reg m0 .rsi))
      (BitVec.ofNat 64 0) = _
    rw [test64]
  simp only [PcOk, hc] at hpc1
  by_cases h0 : (reg m0 .rsi).toNat = 0
  · simp only [h0, decide_true, ↓reduceIte] at hpc1
    have hr : (gkrLayers (reg m0 .rsi).toNat g0).run s0 = some (g0, s0) := by
      rw [h0]; exact gkrLayers_zero g0 s0
    refine at_pc (hpc1.trans (hp.label NativeRustcVmX64.Vm.GkrLayers.label_11_at)) (Eventually.mono
      (exit_spec hp h fr1 (by rw [hbx1, hr]; rfl) fun g' s' he ↦ ?_) fun _ h ↦
        ⟨h.1, h.2.1, h.2.2⟩)
    rw [hr] at he
    cases he
    exact ⟨hts1, hgs1⟩
  simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc1
  -- `b1`: the `TState`, `depth`, the `GkrStateW`.
  have hwf1 := wf0 h fr1.frame.kept 0
  obtain ⟨hok1, hmem1, h121, h141, h151, hk1⟩ := ok_b1
  simp only [BodyOk, Bool.and_eq_true] at hok1
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) exit_b1 hwf1 nofun
    (hpc1.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.GkrLayers.b0_next)) (match_head fr1 0) fun st2 hm2 hpc2 ↦ ?_
  have fr2 := (fr1.block0 hS N_ge hwf1 hm2 hok1.1 slots_le (by simp [hmem1])).1
  have hd2 : st2.data.dmem = st1.data.dmem := hm2.dmem_eq hwf1 hmem1
  simp only [Keeps, List.all_cons, List.all_nil, Bool.and_true, beq_iff_eq] at hk1
  have mid : Mid a s0 g0 m0 (reg m0 .rsi).toNat st2.data :=
    ⟨fr2, by rw [reg_of hm2 h121,
        reg_of hm1 hk0.1],
      (hm2.regs _ _ h141).trans (hm1.regs _ _ hk0.2.1),
      (hm2.regs _ _ h151).trans (hm1.regs _ _ hk0.2.2),
      by rw [reg_of hm2 hk1]; exact hbx1,
      g0, s0, rfl, by rw [hd2]; exact hts1, by rw [hd2]; exact hgs1, h.2.2.2.2.1⟩
  simp only [PcOk] at hpc2
  refine at_pc (hpc2.trans (hp.label NativeRustcVmX64.Vm.GkrLayers.label_4_at)) ?_
  refine loop (I := fun n st ↦ 1 ≤ n ∧ st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.GkrLayers.b6Offset) ∧ Mid a s0 g0 m0 n st.data)
    (fun n st ⟨hn, hpc, hmid⟩ ↦ at_pc hpc (Eventually.mono (iter_spec hp h hstep hn hmid)
      fun st' hs ↦ hs.elim (fun h ↦ .inl ⟨h.1, h.2.1, h.2.2⟩)
        fun ⟨n', hlt, h1, hpc', hmid'⟩ ↦ .inr ⟨n', hlt, h1, hpc', hmid'⟩))
    (n := (reg m0 .rsi).toNat) ⟨by omega, rfl, mid⟩

end

end

end NativeRustcVmX64.Bus.GkrLayers
