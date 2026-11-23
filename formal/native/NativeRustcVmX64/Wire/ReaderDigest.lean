module

public import NativeRustcVmX64.Wire.ReaderDigest.Exec
public import NativeRustcVmX64.Wire.Frame
public import NativeRustcVmX64.Code.Vm.ReaderDigest.Names
public import NativeRustcVmX64.Code.Vm.ReaderLe.Names

/-!
# `Reader::digest` meets its contract (x86-64)

`readerDigest_spec`: four calls of `Reader::le` for eight bytes (`le_call`), from the prologue
(`b0`) and the call blocks `b2`, `b4`, `b6` (`call_step`), each word kept in a callee-saved
register; after each, the tag's test (`b1`, `tag_step`, the same block four times): a failed read
leaves the reads past the bytes (`rdDigest_none`), the tag `0` stored (`b9`, `b10`, `fail_fin`);
four good reads store the words and the tag `1` (`b8`, `b10`, `ok_fin`).
-/

namespace NativeRustcVmX64.Wire.ReaderDigest

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmX64.Vm.ReaderDigest
open NativeRustcVmX64.Transcript (Frame frameEnv frame_wf frame_mapped frame_noWrap match_rsp
  Frame.of_prologue Frame.of_block Frame.epilogue Frame.load_ret sameOutside_low
  sameOutside_region wordAt_write after after_eq exec_after known_ptr inRange_mono apart_frame MidOk)
open NativeRustcVm.Transcript (Mapped.keeps off_zero off_off)

@[expose] public section

/-- What a run changes of the entry's memory: the frame, the reader's cursor. -/
def Chg (m0 : MachineData) (r : BitVec 64) (d : MachineData) : Prop :=
  NativeRustcVm.SameOutside m0.dmem d.dmem fun q ↦
    NativeRustcVm.InRange (stackBelow m0 48) 48 q ∨ NativeRustcVm.InRange (r + BitVec.ofNat 64 16) 8 q

/-- What `Reader::digest` reaches. -/
abbrev Post (m0 : MachineData) (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧ ReaderDigestPost m0 st.data

end

public section

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 48 := by decide

theorem stack_eq : readerDigestStack = 48 := rfl

theorem rdDigest_none {B : List UInt8} {c i : Nat} (hi : i < 4) (h : ¬c + 8 * i + 8 ≤ B.length) :
    rdDigest B c = none := by
  unfold rdDigest
  simp only [show ¬c + 32 ≤ B.length by omega, ↓reduceIte]

theorem rdDigest_some {B : List UInt8} {c : Nat} (h : c + 32 ≤ B.length) :
    rdDigest B c =
      some (#v[leAt B c 8, leAt B (c + 8) 8, leAt B (c + 16) 8, leAt B (c + 24) 8], c + 32) := by
  unfold rdDigest
  simp only [h, ↓reduceIte]

theorem chg_trans {m0 d d' : MachineData} {r : BitVec 64} (h : Chg m0 r d)
    (h' : NativeRustcVm.SameOutside d.dmem d'.dmem fun q ↦
      NativeRustcVm.InRange (stackBelow m0 48) 48 q ∨
        NativeRustcVm.InRange (r + BitVec.ofNat 64 16) 8 q) : Chg m0 r d' :=
  fun q hq ↦ (h' q hq).trans (h q hq)

/-- The places of `Reader::digest`, from its precondition. -/
theorem geo {m0 : MachineData} {bp : BitVec 64} {B : List UInt8} {c : Nat}
    (hst : StackOk m0 readerDigestStack) (hout : NativeRustcVm.Region.Ok m0.dmem ⟨reg m0 .rdi, 40⟩)
    (hR : ReaderAt m0.dmem (reg m0 .rsi) bp B c)
    (hd : NativeRustcVm.Disjoint [stackR m0 readerDigestStack, ⟨reg m0 .rsi, 24⟩,
      ⟨bp, B.length⟩, ⟨reg m0 .rdi, 40⟩]) :
    RGeo m0 48 (reg m0 .rsi) bp B.length (NativeRustcVm.InRange (reg m0 .rdi) 40) ∧
      NativeRustcVm.Apart (reg m0 .rdi) 40 (stackBelow m0 48) (48 + 8) := by
  simp only [NativeRustcVm.Disjoint, List.pairwise_cons, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq, stackR, stack_eq] at hd
  obtain ⟨⟨h1, h2, h3⟩, ⟨h4, h5⟩, h6, -⟩ := hd
  have hS := NativeRustcVmX64.noWrap_stackBelow hst
  have hoS : NativeRustcVm.Apart (reg m0 .rdi) 40 (stackBelow m0 48) (48 + 8) := by
    unfold NativeRustcVm.Apart at h3 ⊢; omega
  refine ⟨⟨hst, hR.ok.2, hR.noWrap, by unfold NativeRustcVm.Apart at h1 ⊢; omega,
    by unfold NativeRustcVm.Apart at h2 ⊢; omega, h4, fun q hq ↦ ?_, fun q hq ↦ ?_,
    fun q hq ↦ ?_⟩, hoS⟩
  · exact hoS.not_inRange hout.2 hS hq
  · exact (show NativeRustcVm.Apart (reg m0 .rdi) 40 (reg m0 .rsi) 24 by
      unfold NativeRustcVm.Apart at h5 ⊢; omega).not_inRange hout.2 hR.ok.2 hq
  · exact (show NativeRustcVm.Apart (reg m0 .rdi) 40 bp B.length by
      unfold NativeRustcVm.Apart at h6 ⊢; omega).not_inRange hout.2 hR.noWrap hq

theorem ite_no {α : Type} {p : Prop} [Decidable p] {a b : α} (h : ¬p) :
    (if p then a else b) = b := by simp [h]

theorem ite_yes {α : Type} {p : Prop} [Decidable p] {a b : α} (h : p) :
    (if p then a else b) = a := by simp [h]

/-- RAX against `1`, the tag's test. -/
theorem beq_one (x : BitVec 64) : (x == BitVec.ofNat 64 1) = decide (x = 1) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  rfl

variable [Host] {k : Nat}

/-- **The tag's test** (`b1`, at `j`): on to `j + 2` if RAX is `1`, else to `NativeRustcVmX64.Vm.ReaderDigest.label_8`. -/
theorem tag_step (hp : Placed code k) {j : Nat} (hj : b1.IsInfixAt code j) {m0 : MachineData}
    (hst : StackOk m0 readerDigestStack) {st : MachineState} (hpc : st.pc = Host.addrOf (k + j))
    (hf : Frame m0 48 slots 8 st.data) {R : MachineState → Prop}
    (cont : ∀ st', Frame m0 48 slots 8 st'.data → st'.data.dmem = st.data.dmem →
      (∀ x, reg st'.data x = reg st.data x) →
      st'.pc = (if reg st.data .rax = 1 then Host.addrOf (k + j + 2) else Host.addrOf (k + NativeRustcVmX64.Vm.ReaderDigest.b9Offset)) →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  obtain ⟨hmid, hregs, hmem, hsome⟩ := ok_b1
  have hwf := frame_wf (m0 := m0) (d := st.data) (F := 48) (rest := []) (vars := fun _ ↦ 0)
    (ret := 0) ⟨Mapped.keeps (frame_mapped hst (by decide)) hf.kept, frame_noWrap hst (by decide)⟩
    (by simp) (List.pairwise_singleton _ _)
  have hm : Match (frameEnv m0 st.data 48 []) midS st.data :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨hf.rsp_eval, trivial⟩ trivial trivial trivial
  refine exec_at (infix_of hj (by simp [b1]) hp) exit_b1 hwf nofun hpc hm fun st' hm' hpc' ↦
    cont st' (Frame.of_block hf hwf hm' hmid slots_le) (hm'.dmem_eq hwf hmem) (fun x ↦ ?_) ?_
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hsome x)
    exact Match.reg_eq hm hm' hv (by rw [SState.reg, hregs]; exact hv)
  · simp only [PcOk, SBool.eval, Sym.eval, CmpOp.apply, low_W64, beq_one] at hpc'
    rw [hp.label NativeRustcVmX64.Vm.ReaderDigest.label_8_at, NativeRustcVmX64.Vm.ReaderDigest.b1_length] at hpc'
    change st'.pc = (if (!decide (reg st.data .rax = 1)) = true then Host.addrOf (k + NativeRustcVmX64.Vm.ReaderDigest.b9Offset)
      else Host.addrOf (k + j + 2)) at hpc'
    by_cases h : reg st.data .rax = 1
    · simp only [h, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc' ⊢
      exact hpc'
    · simp only [h, decide_false, Bool.not_false, ↓reduceIte] at hpc' ⊢
      exact hpc'

/-- **A call block** (`b2`, `b4`, `b6`, at `j`): RDX kept in `x`, then `Reader::le`. -/
theorem call_step (hp : Placed code k)
    (hle : Spec (Labels.label NativeRustcVmX64.Vm.ReaderLe.entryLabel) ReaderLePre ReaderLePost) {m0 : MachineData}
    {r bp out : BitVec 64} {B : List UInt8} {c : Nat}
    (g : RGeo m0 48 r bp B.length (NativeRustcVm.InRange out 40)) {bj : List Directive} {j : Nat}
    (hb : bj.IsInfixAt code j) (hne : bj ≠ []) {x : Reg64} (hx : calleeSaved x = true)
    (hrun : exec bj midS = some (after bj midS,
      .call NativeRustcVmX64.Vm.ReaderLe.entryLabel))
    (hok : CallOk (after bj midS) x = true) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + j)) (hf : Frame m0 48 slots 8 st.data)
    (hr14 : reg st.data .r14 = r) (hR : ReaderAt st.data.dmem r bp B c) {R : MachineState → Prop}
    (cont : ∀ m2, Frame m0 48 slots 8 m2 → reg m2 x = reg st.data .rdx →
      (∀ y ∈ [Reg64.rbx, .r12, .r13, .r14, .r15], y ≠ x → reg m2 y = reg st.data y) →
      NativeRustcVm.SameOutside st.data.dmem m2.dmem (fun q ↦
        NativeRustcVm.InRange (stackBelow m0 48) 48 q ∨
          NativeRustcVm.InRange (r + BitVec.ofNat 64 16) 8 q) →
      ReadRes r bp B c m2 → Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (k + j + bj.length)⟩) :
    Eventually (step1 Host.exe) R st := by
  simp only [CallOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨hmid, hws⟩, hrdi⟩, hrsi⟩, hrx⟩, hkeep⟩ := hok
  have hst : StackOk m0 48 := g.st
  have hwf := frame_wf (m0 := m0) (d := st.data) (F := 48) (rest := []) (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + j + bj.length)).toBitVec)
    ⟨Mapped.keeps (frame_mapped hst (by decide)) hf.kept, frame_noWrap hst (by decide)⟩
    (by simp) (List.pairwise_singleton _ _)
  have hm : Match (frameEnv m0 st.data 48 [] (fun _ ↦ 0)
      (Host.addrOf (k + j + bj.length)).toBitVec) midS st.data :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨hf.rsp_eval, trivial⟩ trivial trivial trivial
  refine exec_at (infix_of hb hne hp) hrun hwf (fun _ _ ↦ rfl) hpc hm fun st1 hm1 hpc1 ↦ ?_
  have hf1 : Frame m0 48 slots 0 st1.data := Frame.of_block hf hwf hm1 hmid slots_le
  have hs1 : NativeRustcVm.SameOutside st.data.dmem st1.data.dmem
      (NativeRustcVm.InRange (stackBelow m0 48) 8) :=
    sameOutside_low hwf hm1 (r := 0) rfl (by decide) hws
  have hR1 : ReaderAt st1.data.dmem r bp B c :=
    g.reader_frame rfl hR fun q hq ↦ hs1 q fun h ↦ hq (.inl (inRange_mono h (by omega)))
  have hrdi1 : reg st1.data .rdi = r := (hm1.regs .rdi _ hrdi).trans hr14
  have hrsi1 : (reg st1.data .rsi).toNat = 8 := by
    rw [show reg st1.data .rsi = _ from hm1.regs .rsi _ hrsi]
    rfl
  refine le_call hle g (F := 48) le_rfl slots_le hf1 hR1 hrdi1 hrsi1 hpc1
    fun m2 hf2 hcs hs2 hrr ↦ cont m2 hf2 ?_ ?_ ?_ hrr
  · exact (hcs x hx).trans (hm1.regs x _ hrx)
  · intro y hy hyx
    have hcy : calleeSaved y = true := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl <;> rfl
    exact (hcs y hcy).trans (hm1.regs y _ (hkeep y (List.mem_filter.mpr ⟨hy, by
      cases h : (y == x)
      · simp only [bne, h, Bool.not_false]
      · exact absurd (Reg64.eq_of_beq h) hyx⟩)))
  · intro q hq
    simp only [not_or] at hq
    rw [hs2 q hq.2]
    exact hs1 q fun h ↦ hq.1 (inRange_mono h (by omega))

/-- **A failed read** (`b9`, `b10`): the tag `0` stored, the epilogue. -/
theorem fail_fin (hp : Placed code k) {m0 : MachineData} {bp : BitVec 64} {B : List UInt8}
    {c : Nat} (hst : StackOk m0 readerDigestStack)
    (hR : ReaderAt m0.dmem (reg m0 .rsi) bp B c)
    (hout : NativeRustcVm.Region.Ok m0.dmem ⟨reg m0 .rdi, 40⟩)
    (hoS : NativeRustcVm.Apart (reg m0 .rdi) 40 (stackBelow m0 48) (48 + 8))
    (hnone : rdDigest B c = none) {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.ReaderDigest.b9Offset))
    (hf : Frame m0 48 slots 8 st.data) (hrbx : reg st.data .rbx = reg m0 .rdi)
    (hchg : Chg m0 (reg m0 .rsi) st.data) :
    Eventually (step1 Host.exe) (Post m0) st := by
  set out := reg m0 .rdi
  have hwf := frame_wf (m0 := m0) (d := st.data) (F := 48) (rest := [(out, 40)])
    (vars := fun _ ↦ 0) (ret := 0)
    ⟨Mapped.keeps (frame_mapped hst (by decide)) hf.kept, frame_noWrap hst (by decide)⟩
    (by
      intro y hy
      rw [List.mem_singleton] at hy
      subst hy
      exact ⟨Mapped.keeps hout.1 hf.kept, hout.2⟩)
    (List.pairwise_pair.mpr (by unfold NativeRustcVm.Apart at hoS ⊢; dsimp only; omega))
  have hm : Match (frameEnv m0 st.data 48 [(out, 40)]) outS st.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hf.rsp_eval, known_ptr rfl hrbx, trivial⟩ trivial
      trivial trivial
  refine exec_at (infix_of b9_in_code (by simp [b9]) hp) run_b9 hwf nofun hpc hm
    fun st1 hm1 hpc1 ↦ ?_
  refine exec_at (infix_of b10_in_code (by simp [b10]) hp) (exec_after run_b9 run_b10n) hwf
    nofun (hpc1.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.ReaderDigest.b9_next)) hm1 fun st2 hm2 hpc2 ↦ ?_
  obtain ⟨hepi, hw0, hws⟩ := after_eq run_b10n ▸ ok_b10n
  obtain ⟨hsv, hrsp⟩ := Frame.epilogue hf hwf hm2 hepi
  have ht := wordAt_write hm2 (r := 1) (o := 0) (b := out) (sz := 40) rfl (by decide)
    (fun i hi ↦ by rw [Nat.zero_add]; exact hw0 i hi)
  rw [off_zero] at ht
  have hs := sameOutside_region hwf hm2 (r := 1) rfl hws
  simp only [PcOk] at hpc2
  refine .done _ ⟨by rw [hpc2]; exact hf.load_ret hst (by decide), hrsp, ?_, ?_, hsv⟩
  · intro bp' B' c' hR'
    obtain ⟨rfl, rfl, rfl⟩ := hR.unique hR'
    rw [hnone]
    exact ht
  · intro q hq
    simp only [NativeRustcVm.InAny, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
      exists_eq_left, frameR, stack_eq, NativeRustcVm.Region.Holds, curRegion] at hq
    simp only [not_or] at hq
    rw [hs q hq.1]
    exact hchg q fun h ↦ h.elim hq.2.2 hq.2.1

/-- **Four good reads** (`b8`, `b10`): the words and the tag `1` stored, the epilogue. -/
theorem ok_fin (hp : Placed code k) {m0 : MachineData} {bp : BitVec 64} {B : List UInt8}
    {c : Nat} (hst : StackOk m0 readerDigestStack)
    (hR : ReaderAt m0.dmem (reg m0 .rsi) bp B c)
    (hout : NativeRustcVm.Region.Ok m0.dmem ⟨reg m0 .rdi, 40⟩)
    (hoS : NativeRustcVm.Apart (reg m0 .rdi) 40 (stackBelow m0 48) (48 + 8))
    (hfit : c + 32 ≤ B.length) {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.ReaderDigest.b8Offset))
    (hf : Frame m0 48 slots 8 st.data) (hrbx : reg st.data .rbx = reg m0 .rdi)
    (h12 : reg st.data .r12 = (leAt B c 8).toBitVec)
    (h13 : reg st.data .r13 = (leAt B (c + 8) 8).toBitVec)
    (h15 : reg st.data .r15 = (leAt B (c + 16) 8).toBitVec)
    (hdx : reg st.data .rdx = (leAt B (c + 24) 8).toBitVec)
    (hR' : ReaderAt st.data.dmem (reg m0 .rsi) bp B (c + 32))
    (hreader : ∀ q, NativeRustcVm.InRange (reg m0 .rdi) 40 q →
      ¬ NativeRustcVm.InRange (reg m0 .rsi) 24 q ∧ ¬ NativeRustcVm.InRange bp B.length q)
    (hchg : Chg m0 (reg m0 .rsi) st.data) :
    Eventually (step1 Host.exe) (Post m0) st := by
  set out := reg m0 .rdi
  have hwf := frame_wf (m0 := m0) (d := st.data) (F := 48) (rest := [(out, 40)])
    (vars := fun _ ↦ 0) (ret := 0)
    ⟨Mapped.keeps (frame_mapped hst (by decide)) hf.kept, frame_noWrap hst (by decide)⟩
    (by
      intro y hy
      rw [List.mem_singleton] at hy
      subst hy
      exact ⟨Mapped.keeps hout.1 hf.kept, hout.2⟩)
    (List.pairwise_pair.mpr (by unfold NativeRustcVm.Apart at hoS ⊢; dsimp only; omega))
  have hm : Match (frameEnv m0 st.data 48 [(out, 40)]) outS st.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hf.rsp_eval, known_ptr rfl hrbx, trivial⟩ trivial
      trivial trivial
  refine exec_at (infix_of b8_in_code (by simp [b8]) hp) run_b8 hwf nofun hpc hm
    fun st1 hm1 hpc1 ↦ ?_
  simp only [PcOk] at hpc1
  refine exec_at (infix_of b10_in_code (by simp [b10]) hp) (exec_after run_b8 run_b10s) hwf
    nofun (hpc1.trans (hp.label NativeRustcVmX64.Vm.ReaderDigest.label_9_at)) hm1 fun st2 hm2 hpc2 ↦ ?_
  obtain ⟨hepi, hw0, hw8, hw16, hw24, hw32, hws⟩ := after_eq run_b10s ▸ ok_b10s
  obtain ⟨hsv, hrsp⟩ := Frame.epilogue hf hwf hm2 hepi
  have w0 := wordAt_write hm2 (r := 1) (o := 0) (b := out) (sz := 40) rfl (by decide)
    (fun i hi ↦ by rw [Nat.zero_add]; exact hw0 i hi)
  have w8 := wordAt_write hm2 (r := 1) (o := 8) (b := out) (sz := 40) rfl (by decide) hw8
  have w16 := wordAt_write hm2 (r := 1) (o := 16) (b := out) (sz := 40) rfl (by decide) hw16
  have w24 := wordAt_write hm2 (r := 1) (o := 24) (b := out) (sz := 40) rfl (by decide) hw24
  have w32 := wordAt_write hm2 (r := 1) (o := 32) (b := out) (sz := 40) rfl (by decide) hw32
  rw [off_zero] at w0
  have e : ∀ {v : UInt64} {x : Reg64}, reg st.data x = v.toBitVec →
      UInt64.ofBitVec ((Sym.reg x).eval (frameEnv m0 st.data 48 [(out, 40)])) = v :=
    fun h ↦ by show UInt64.ofBitVec (reg st.data _) = _; rw [h]
  rw [e h12] at w8
  rw [e h13] at w16
  rw [e h15] at w24
  rw [e hdx] at w32
  have hs := sameOutside_region hwf hm2 (r := 1) rfl hws
  simp only [PcOk] at hpc2
  refine .done _ ⟨by rw [hpc2]; exact hf.load_ret hst (by decide), hrsp, ?_, ?_, hsv⟩
  · intro bp' B' c' hR''
    obtain ⟨rfl, rfl, rfl⟩ := hR.unique hR''
    rw [rdDigest_some hfit]
    refine ⟨w0, ?_, hR'.frame hs (fun i hi h ↦ (hreader _ h).1 (NativeRustcVm.inRange_add hi
      (by have := hR'.ok.2; unfold NativeRustcVm.NoWrap at this; omega)))
      (fun i hi h ↦ (hreader _ h).2 (NativeRustcVm.inRange_add hi
      (by have := hR'.noWrap; unfold NativeRustcVm.NoWrap at this; omega)))⟩
    show NativeRustcVm.WordsAt _ _ [_, _, _, _]
    refine NativeRustcVm.Transcript.wordsAt_cons.mpr ⟨w8, ?_⟩
    rw [off_off]
    refine NativeRustcVm.Transcript.wordsAt_cons.mpr ⟨w16, ?_⟩
    rw [off_off]
    refine NativeRustcVm.Transcript.wordsAt_cons.mpr ⟨w24, ?_⟩
    rw [off_off]
    exact NativeRustcVm.Transcript.wordsAt_cons.mpr ⟨w32, NativeRustcVm.Transcript.wordsAt_nil _ _⟩
  · intro q hq
    simp only [NativeRustcVm.InAny, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
      exists_eq_left, frameR, stack_eq, NativeRustcVm.Region.Holds, curRegion] at hq
    simp only [not_or] at hq
    rw [hs q hq.1]
    exact hchg q fun h ↦ h.elim hq.2.2 hq.2.1

/-- **`Reader::digest` meets its contract.** -/
theorem readerDigest_spec (hp : Placed code k)
    (hle : Spec (Labels.label NativeRustcVmX64.Vm.ReaderLe.entryLabel) ReaderLePre ReaderLePost) :
    Spec (Labels.label NativeRustcVmX64.Vm.ReaderDigest.entryLabel) ReaderDigestPre ReaderDigestPost := by
  intro m0 ⟨hst, hout, bp, B, c, hR, hd⟩
  obtain ⟨g, hoS⟩ := geo hst hout hR hd
  have hreader : ∀ q, NativeRustcVm.InRange (reg m0 .rdi) 40 q →
      ¬ NativeRustcVm.InRange (reg m0 .rsi) 24 q ∧ ¬ NativeRustcVm.InRange bp B.length q :=
    fun q h ↦ ⟨g.wR q h, g.wB q h⟩
  rw [show Labels.label NativeRustcVmX64.Vm.ReaderDigest.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.ReaderDigest.b0Offset) from hp.label NativeRustcVmX64.Vm.ReaderDigest.entry_at]
  -- `b0`: the prologue, the first read.
  have hwf0 := frame_wf (m0 := m0) (d := m0) (F := 48) (rest := []) (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.ReaderDigest.b0Offset + b0.length)).toBitVec)
    ⟨frame_mapped hst (by decide), frame_noWrap hst (by decide)⟩ (by simp)
    (List.pairwise_singleton _ _)
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_b0 hwf0 (fun _ _ ↦ rfl)
    (match_ofMachine ⟨rfl, trivial⟩ ⟨match_rsp, trivial⟩ trivial trivial trivial)
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hpro, hws1, hx7, hx6, hx14, hx3⟩ := after_eq run_b0 ▸ ok_b0
  have hf1 : Frame m0 48 slots 0 st1.data :=
    Frame.of_prologue Frame.entry hwf0 hm1 hpro slots_le (by decide)
  have hs1 : NativeRustcVm.SameOutside m0.dmem st1.data.dmem
      (NativeRustcVm.InRange (stackBelow m0 48) 48) :=
    sameOutside_low hwf0 hm1 (r := 0) rfl (by decide) hws1
  have hR1 := g.reader_frame rfl hR fun q hq ↦ hs1 q fun h ↦ hq (.inl (inRange_mono h (by omega)))
  have hrdi1 : reg st1.data .rdi = reg m0 .rsi := hm1.regs .rdi _ hx7
  have hrsi1 : (reg st1.data .rsi).toNat = 8 := by
    rw [show reg st1.data .rsi = _ from hm1.regs .rsi _ hx6]; rfl
  have h14 : reg st1.data .r14 = reg m0 .rsi := hm1.regs .r14 _ hx14
  have h3 : reg st1.data .rbx = reg m0 .rdi := hm1.regs .rbx _ hx3
  have hc1 : Chg m0 (reg m0 .rsi) st1.data := fun q hq ↦ hs1 q fun h ↦ hq (.inl h)
  refine le_call hle g (F := 48) le_rfl slots_le hf1 hR1 hrdi1 hrsi1 hpc1
    fun m2 hf2 hcs2 hs2 hrr2 ↦ ?_
  have hc2 : Chg m0 (reg m0 .rsi) m2 := chg_trans hc1 fun q hq ↦ hs2 q fun h ↦ hq (.inr h)
  have h14₂ : reg m2 .r14 = reg m0 .rsi := (hcs2 .r14 rfl).trans h14
  have h3₂ : reg m2 .rbx = reg m0 .rdi := (hcs2 .rbx rfl).trans h3
  -- The first tag.
  refine tag_step hp (j := NativeRustcVmX64.Vm.ReaderDigest.b1Offset) b1_in_code hst (st := ⟨m2, _⟩) rfl hf2
    fun st3 hf3 hd3 hr3 hpc3 ↦ ?_
  dsimp only at hd3 hr3 hpc3
  have hc3 : Chg m0 (reg m0 .rsi) st3.data := fun q hq ↦ by rw [hd3]; exact hc2 q hq
  rcases readRes_cases hrr2 with ⟨h0, hc⟩ | ⟨h1, hv1, hR2, hc⟩
  · rw [ite_no (by rw [h0]; decide)] at hpc3
    exact fail_fin hp hst hR hout hoS (rdDigest_none (i := 0) (by decide) (by omega)) hpc3 hf3
      ((hr3 .rbx).trans h3₂) hc3
  rw [ite_yes h1] at hpc3
  -- The second read.
  refine call_step hp hle g b2_in_code (by simp [b2]) (x := .r12) rfl run_b2 ok_b2 hpc3 hf3
    ((hr3 .r14).trans h14₂) (by rw [hd3]; exact hR2) fun m4 hf4 hx4 hk4 hs4 hrr4 ↦ ?_
  have hc4 : Chg m0 (reg m0 .rsi) m4 := chg_trans hc3 hs4
  have h12₄ : reg m4 .r12 = (leAt B c 8).toBitVec := by rw [hx4, hr3, hv1]
  have h14₄ : reg m4 .r14 = reg m0 .rsi := by rw [hk4 .r14 (by simp) (by decide), hr3, h14₂]
  have h3₄ : reg m4 .rbx = reg m0 .rdi := by rw [hk4 .rbx (by simp) (by decide), hr3, h3₂]
  refine tag_step hp (j := NativeRustcVmX64.Vm.ReaderDigest.b3Offset) (b3_eq ▸ b3_in_code) hst (st := ⟨m4, _⟩) rfl hf4
    fun st5 hf5 hd5 hr5 hpc5 ↦ ?_
  dsimp only at hd5 hr5 hpc5
  have hc5 : Chg m0 (reg m0 .rsi) st5.data := fun q hq ↦ by rw [hd5]; exact hc4 q hq
  rcases readRes_cases hrr4 with ⟨h0, hc'⟩ | ⟨h1, hv2, hR4, hc'⟩
  · rw [ite_no (by rw [h0]; decide)] at hpc5
    exact fail_fin hp hst hR hout hoS (rdDigest_none (i := 1) (by decide) (by omega)) hpc5 hf5
      ((hr5 .rbx).trans h3₄) hc5
  rw [ite_yes h1] at hpc5
  -- The third read.
  refine call_step hp hle g b4_in_code (by simp [b4]) (x := .r13) rfl run_b4 ok_b4 hpc5 hf5
    ((hr5 .r14).trans h14₄) (by rw [hd5]; exact hR4) fun m6 hf6 hx6 hk6 hs6 hrr6 ↦ ?_
  have hc6 : Chg m0 (reg m0 .rsi) m6 := chg_trans hc5 hs6
  have h12₆ : reg m6 .r12 = (leAt B c 8).toBitVec := by
    rw [hk6 .r12 (by simp) (by decide), hr5, h12₄]
  have h13₆ : reg m6 .r13 = (leAt B (c + 8) 8).toBitVec := by rw [hx6, hr5, hv2]
  have h14₆ : reg m6 .r14 = reg m0 .rsi := by rw [hk6 .r14 (by simp) (by decide), hr5, h14₄]
  have h3₆ : reg m6 .rbx = reg m0 .rdi := by rw [hk6 .rbx (by simp) (by decide), hr5, h3₄]
  refine tag_step hp (j := NativeRustcVmX64.Vm.ReaderDigest.b5Offset) (b5_eq ▸ b5_in_code) hst (st := ⟨m6, _⟩) rfl hf6
    fun st7 hf7 hd7 hr7 hpc7 ↦ ?_
  dsimp only at hd7 hr7 hpc7
  have hc7 : Chg m0 (reg m0 .rsi) st7.data := fun q hq ↦ by rw [hd7]; exact hc6 q hq
  rcases readRes_cases hrr6 with ⟨h0, hc''⟩ | ⟨h1, hv3, hR6, hc''⟩
  · rw [ite_no (by rw [h0]; decide)] at hpc7
    exact fail_fin hp hst hR hout hoS (rdDigest_none (i := 2) (by decide) (by omega)) hpc7 hf7
      ((hr7 .rbx).trans h3₆) hc7
  rw [ite_yes h1] at hpc7
  -- The fourth read.
  refine call_step hp hle g b6_in_code (by simp [b6]) (x := .r15) rfl run_b6 ok_b6 hpc7 hf7
    ((hr7 .r14).trans h14₆) (by rw [hd7]; exact hR6) fun m8 hf8 hx8 hk8 hs8 hrr8 ↦ ?_
  have hc8 : Chg m0 (reg m0 .rsi) m8 := chg_trans hc7 hs8
  have h12₈ : reg m8 .r12 = (leAt B c 8).toBitVec := by
    rw [hk8 .r12 (by simp) (by decide), hr7, h12₆]
  have h13₈ : reg m8 .r13 = (leAt B (c + 8) 8).toBitVec := by
    rw [hk8 .r13 (by simp) (by decide), hr7, h13₆]
  have h15₈ : reg m8 .r15 = (leAt B (c + 16) 8).toBitVec := by rw [hx8, hr7, hv3]
  have h3₈ : reg m8 .rbx = reg m0 .rdi := by rw [hk8 .rbx (by simp) (by decide), hr7, h3₆]
  refine tag_step hp (j := NativeRustcVmX64.Vm.ReaderDigest.b7Offset) (b7_eq ▸ b7_in_code) hst (st := ⟨m8, _⟩) rfl hf8
    fun st9 hf9 hd9 hr9 hpc9 ↦ ?_
  dsimp only at hd9 hr9 hpc9
  have hc9 : Chg m0 (reg m0 .rsi) st9.data := fun q hq ↦ by rw [hd9]; exact hc8 q hq
  rcases readRes_cases hrr8 with ⟨h0, hc'''⟩ | ⟨h1, hv4, hR8, hc'''⟩
  · rw [ite_no (by rw [h0]; decide)] at hpc9
    exact fail_fin hp hst hR hout hoS (rdDigest_none (i := 3) (by decide) (by omega)) hpc9 hf9
      ((hr9 .rbx).trans h3₈) hc9
  rw [ite_yes h1] at hpc9
  exact ok_fin hp hst hR hout hoS (by omega) hpc9 hf9 ((hr9 .rbx).trans h3₈)
    ((hr9 .r12).trans h12₈) ((hr9 .r13).trans h13₈) ((hr9 .r15).trans h15₈)
    ((hr9 .rdx).trans hv4) (by rw [hd9, show c + 32 = c + 8 + 8 + 8 + 8 by omega]; exact hR8)
    hreader hc9

end

end NativeRustcVmX64.Wire.ReaderDigest
