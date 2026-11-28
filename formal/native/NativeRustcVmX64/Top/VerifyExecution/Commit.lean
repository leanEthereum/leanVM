module

public import NativeRustcVmX64.Top.VerifyExecution.Bus
public import NativeRustcVmX64.Code.Vm.CommitStack.Names
public import NativeRustcVmX64.Code.Vm.KeccakPhase.Names
public import NativeRustcVmX64.Code.Vm.PublicInputPhase.Names
public import NativeRustcVmX64.Code.Vm.ReadOod.Names
public import NativeRustcVmX64.Code.Vm.RingSwitch.Names
public import NativeRustcVmX64.Code.Vm.TableColumnClaims.Names
public import NativeRustcVmX64.Code.Vm.TablePhase.Names
public import NativeRustcVmX64.Code.Vm.VerifyBusBalance.Names
public import NativeRustcVmX64.Code.Vm.VerifyStackedOpening.Names

/-!
# `verify_execution`: the stack's commitment and the out-of-domain sample (x86-64)

`b2` keeps the rate in R15 and the stack's log-size (the layout's word at byte `16`) in RBP and
calls `commit_stack`; `b3` returns `0` when it failed. `b4` calls `read_ood` into the working
area's bytes from `3912` (kept in RBP); `b5` returns `0` when it failed, else the bus (`callOod`,
`callCommit`).
-/

namespace NativeRustcVmX64.Top.VerifyExecution

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.VerifyExecution NativeRustcVmX64.Transcript
open NativeRustcVmX64.Top NativeRustcVm.Transcript NativeVm.Model
open NativeRustcVm.Top (workAreaBytes walkCommit walkOod run_bind_eq commitStack_roots)
open NativeRustcVm.Layout (LayoutWAt OodAt)
open LeanVM.Protocol.Verifier (memory0)

public section

variable [Host] {k : Nat}

/-- **The out-of-domain sample**, from `b4`: the function returns the walk's rest. -/
theorem callOod (hp : Placed code k)
    (hro : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.ReadOod.entryLabel) (ReadOodPre a s) (ReadOodPost a s))
    (hbb : ∀ a s L, Spec (Labels.label NativeRustcVmX64.Vm.VerifyBusBalance.entryLabel) (VerifyBusBalancePre a s L)
      (VerifyBusBalancePost a s L))
    (htp : ∀ a s layout bus, Spec (Labels.label NativeRustcVmX64.Vm.TablePhase.entryLabel) (TablePhasePre a s layout bus)
      (TablePhasePost a s layout bus))
    (htc : ∀ evals cs, Spec (Labels.label NativeRustcVmX64.Vm.TableColumnClaims.entryLabel) (TableColumnClaimsPre evals cs)
      (TableColumnClaimsPost evals cs))
    (hpi : ∀ a s layout pub cs, Spec (Labels.label NativeRustcVmX64.Vm.PublicInputPhase.entryLabel)
      (PublicInputPhasePre a s layout pub cs) (PublicInputPhasePost a s layout pub cs))
    (hkp : ∀ a s cs layout evals, Spec (Labels.label NativeRustcVmX64.Vm.KeccakPhase.entryLabel)
      (KeccakPhasePre a s cs layout evals) (KeccakPhasePost a s cs layout evals))
    (hrs : ∀ a s point, Spec (Labels.label NativeRustcVmX64.Vm.RingSwitch.entryLabel) (RingSwitchPre a s)
      (RingSwitchPost a s point))
    (hvso : ∀ a s layout target coefficients point slices cs z value,
      Spec (Labels.label NativeRustcVmX64.Vm.VerifyStackedOpening.entryLabel)
        (VerifyStackedOpeningPre a s layout target coefficients point slices cs z value)
        (VerifyStackedOpeningPost a s layout target coefficients point cs z value))
    {a : DecArea} {m0 : MachineData} (g : Geo a m0) {st : MachineState} (h : At m0 st.data)
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyExecution.b4Offset)) {rate : Nat} (h15 : (reg st.data .r15).toNat = rate)
    (h12 : reg st.data .r12 = reg m0 .rsi) (h13 : reg st.data .r13 = reg m0 .rdx)
    {L : LayoutW} (hbp : (reg st.data .rbp).toNat = L.stackLog)
    (h40 : NativeRustcVm.WordAt st.data.dmem (off (stackBelow m0 96) 40)
      (UInt64.ofBitVec (reg m0 .rcx)))
    {P : Vector UInt64 4} (hP : NativeRustcVm.WordsAt m0.dmem (reg m0 .rcx) P.toList)
    {s : TState} (hts : TStateAt st.data.dmem (reg m0 .rdi) a s) (hroots : s.roots.size ≤ 2)
    (hL : LayoutWAt st.data.dmem (reg m0 .r8) L) (hsl : L.stackLog ≤ 30)
    (hvc : (L.placement memory0).variableCount ≤ 31) (hBn : L.bytecode.size = (reg m0 .rdx).toNat)
    (hB : NativeRustcVm.WordsAt m0.dmem (reg m0 .rsi) L.bytecode.toList) :
    Eventually (step1 Host.exe) (Done a m0 ((walkOod P L rate).run s)) st := by
  have hR := g.R
  have h8 := g.e8
  have hF := g.F
  have hwN := g.wN
  have hN : readOodStack = 688 := rfl
  obtain ⟨hwf, hm⟩ := h.env g (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyExecution.b4Offset + b4.length)).toBitVec)
  refine exec_at (infix_of b4_in_code (by simp [b4]) hp) run_b4 hwf (fun _ _ ↦ rfl) hpc hm
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hmid, hw1, hrdi, hrsi, hrdx, hrbp, hk⟩ := after_eq run_b4 ▸ ok_b4
  have hC : AtCall m0 st1.data := h.toCall g hwf hm1 hmid (by decide) hw1
  have hs1 : NativeRustcVm.SameOutside st.data.dmem st1.data.dmem
      (NativeRustcVm.InRange (stackBelow m0 96) 40) :=
    sameOutside_low hwf hm1 (r := 0) rfl (by decide) hw1
  have hs1' : ∀ q, NativeRustcVm.InRange (stackBelow m0 96) 40 q →
      vsb m0 + 17792 ≤ q.toNat ∧ q.toNat < vsb m0 + 17832 := fun q hq ↦ by
    rw [inR (by unfold NativeRustcVm.NoWrap; omega), hF] at hq
    omega
  have kr : ∀ r ∈ [Reg64.rbx, .r12, .r13, .r14, .r15], reg st1.data r = reg st.data r :=
    fun r hr ↦ hm1.regs r (.reg r) (by simpa using List.all_eq_true.mp hk r hr)
  have eadd : (Sym.bin .add .W64 (.reg .rbx) (.lit 3912)).eval (frameEnv m0 st.data 96 []
      (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyExecution.b4Offset + b4.length)).toBitVec) = off (reg m0 .r8) 3912 := by
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]
    exact congrArg (· + BitVec.ofNat 64 3912) h.rbx
  have eRdi : reg st1.data .rdi = reg m0 .rdi := (hm1.regs .rdi _ hrdi).trans h.r14
  have eRsi : (reg st1.data .rsi).toNat = L.stackLog := by
    rw [show reg st1.data .rsi = _ from hm1.regs .rsi _ hrsi]; exact hbp
  have eRdx : reg st1.data .rdx = off (reg m0 .r8) 3912 := (hm1.regs .rdx _ hrdx).trans eadd
  have eRbp : reg st1.data .rbp = off (reg m0 .r8) 3912 := (hm1.regs .rbp _ hrbp).trans eadd
  have hts1 : TStateAt st1.data.dmem (reg m0 .rdi) a s :=
    hts.frame (fun p hp ↦ hm1.kept hwf p hp) (fun q hq ↦ by
      have := hs1' q hq
      have := g.aS
      have := g.tS
      refine ⟨fun hi ↦ ?_, fun hi ↦ ?_⟩
      · have := (inR g.tN).mp hi; omega
      · have := (inR g.aN).mp hi; omega) hs1
  have hc : (32 : Nat) ≤ 96 := by decide
  have hN' : 688 ≤ 17792 + 32 := by decide
  have hpre : ReadOodPre a s st1.data := by
    unfold ReadOodPre
    simp only [eRdi, eRdx]
    rw [hN]
    refine ⟨hC.stackOk g hc hN', hC.rcAt g hc hN', hts1, hC.tstateOk g hc hN',
      by rw [eRsi]; exact hsl, hC.outOk g hc (o := 3912) (n := 504) (by omega) (by omega) hN', ?_⟩
    apply GotAt.symbols (symbols := ["memcpy", "memset"]) (hs := by decide)
    apply hC.got g hc hN'
    intro l hl
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨g.gotT hl, g.gotA hl, g.gotW hl (by omega) (by decide), g.gotRc hl⟩
  refine call_then hpc1 (hro a s) hpre fun st2 hpc2 hrsp2 hpost ↦ ?_
  obtain ⟨hok, hres, hch, hsv⟩ := hpost
  simp only [eRdi, eRdx, eRsi, hN, show NativeRustcVm.Layout.eqClaimBytes = 504 from rfl]
    at hok hres hch
  have hR2 : ∀ q, (NativeRustcVm.InRange (off (reg m0 .r8) 3912) 504 q ∨
      NativeRustcVm.InRange (reg m0 .rdi) tstateBytes q ∨
      NativeRustcVm.InRange (stackBelow st1.data 688) 688 q) →
      (vsb m0 ≤ q.toNat ∧ q.toNat < vsb m0 + 17824) ∨
      ((reg m0 .rdi).toNat ≤ q.toNat ∧ q.toNat < (reg m0 .rdi).toNat + 760) ∨
      ((reg m0 .r8).toNat + 3912 ≤ q.toNat ∧ q.toNat < (reg m0 .r8).toNat + 4416) := by
    rintro q (hq | hq | hq)
    · have := g.inW (o := 3912) (n := 504) (by omega) (by omega) hq; omega
    · exact Or.inr (Or.inl (g.inT hq))
    · have := hC.inS g hc hN' hq; left; omega
  have h2 : At m0 st2.data := hC.ret g ((kr .rbx (by simp)).trans h.rbx)
    ((kr .r14 (by simp)).trans h.r14) hsv hrsp2 hch fun q hq ↦ by
      rcases hR2 q hq with hq | hq | hq
      · exact Or.inl hq
      · exact Or.inr (Or.inl hq)
      · exact Or.inr (Or.inr ⟨by omega, by omega⟩)
  have hsA := NativeRustcVm.Transcript.SameOutside.trans hs1 hch
  have hRA : ∀ q, (NativeRustcVm.InRange (stackBelow m0 96) 40 q ∨
      (NativeRustcVm.InRange (off (reg m0 .r8) 3912) 504 q ∨
        NativeRustcVm.InRange (reg m0 .rdi) tstateBytes q ∨
        NativeRustcVm.InRange (stackBelow st1.data 688) 688 q)) →
      (vsb m0 ≤ q.toNat ∧ q.toNat < vsb m0 + 17832) ∨
      ((reg m0 .rdi).toNat ≤ q.toNat ∧ q.toNat < (reg m0 .rdi).toNat + 760) ∨
      ((reg m0 .r8).toNat + 3912 ≤ q.toNat ∧ q.toNat < (reg m0 .r8).toNat + 4416) := by
    rintro q (hq | hq)
    · have := hs1' q hq; left; omega
    · rcases hR2 q hq with h' | h' | h'
      · left; omega
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr h')
  have hsC : NativeRustcVm.Layout.Same st.data.dmem st2.data.dmem (off (reg m0 .r8) 0) 3912 :=
    g.same hsA (by omega) (by omega) fun q hq ↦ by
      have := g.wS
      have := g.tw
      rcases hRA q hq with h' | h' | h' <;> omega
  have h40' : NativeRustcVm.WordAt st2.data.dmem (off (stackBelow m0 96) 40)
      (UInt64.ofBitVec (reg m0 .rcx)) :=
    keep40 g hsA (fun q hq ↦ by
      rcases hRA q hq with h' | h' | h'
      · left; omega
      · right; right; left; exact h'
      · right; right; right; omega) h40
  -- `b5`: the test
  rw [walkOod, run_bind_eq]
  generalize hr : (readOod L.stackLog).run s = r at hok hres
  refine branch hp g b5_in_code (by simp [b5]) (by rw [after_eq run_b5]; exact run_b5)
    (ok_test b5 (by simp)) h2 (hpc2.trans (by rw [show k + NativeRustcVmX64.Vm.VerifyExecution.b4Offset + b4.length = k + NativeRustcVmX64.Vm.VerifyExecution.b5Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyExecution.b4_next]]))
    hok (fun hb ↦ by cases r with | none => rfl | some _ => cases hb)
    fun st3 hb h3 hd3 hk3 hpc3 ↦ ?_
  obtain ⟨⟨ood, s'⟩, rfl⟩ := Option.isSome_iff_exists.mp hb
  obtain ⟨hood, hts'⟩ := hres _ _ rfl
  have hroots' : s'.roots = s.roots := (NativeVm.Math.readOod_roots L.stackLog).keeps _ _ _ hr
  have k12 : reg st3.data .r12 = reg st1.data .r12 := (hk3 .r12 (by simp)).trans (hsv.1 .r12 rfl)
  have k13 : reg st3.data .r13 = reg st1.data .r13 := (hk3 .r13 (by simp)).trans (hsv.1 .r13 rfl)
  have k15 : reg st3.data .r15 = reg st1.data .r15 := (hk3 .r15 (by simp)).trans (hsv.1 .r15 rfl)
  have kbp : reg st3.data .rbp = reg st1.data .rbp := (hk3 .rbp (by simp)).trans (hsv.1 .rbp rfl)
  have hL3 : LayoutWAt st3.data.dmem (off (reg m0 .r8) 0) L := by
    rw [hd3]
    exact NativeRustcVm.Tables.LayoutWAt.of_same (by rw [off_zero]; exact hL) hsC
  rw [off_zero] at hL3
  exact callBus hp hbb htp htc hpi hkp hrs hvso g h3
    (hpc3.trans (by rw [show k + NativeRustcVmX64.Vm.VerifyExecution.b5Offset + b5.length = k + NativeRustcVmX64.Vm.VerifyExecution.b6Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyExecution.b5_next]])) (rate := rate)
    (by rw [k15, kr _ (by simp)]; exact h15) (by rw [k12, kr _ (by simp)]; exact h12)
    (by rw [k13, kr _ (by simp)]; exact h13) (by rw [kbp]; exact eRbp)
    (by rw [hd3]; exact h40') hP (by rw [hd3]; exact hts') (by rw [hroots']; exact hroots) hL3 hvc
    hBn hB (by rw [hd3]; exact hood)

/-- **The stack's commitment**, from `b2`: the function returns the walk's rest. -/
theorem callCommit (hp : Placed code k)
    (hcs : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.CommitStack.entryLabel) (CommitStackPre a s) (CommitStackPost a s))
    (hro : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.ReadOod.entryLabel) (ReadOodPre a s) (ReadOodPost a s))
    (hbb : ∀ a s L, Spec (Labels.label NativeRustcVmX64.Vm.VerifyBusBalance.entryLabel) (VerifyBusBalancePre a s L)
      (VerifyBusBalancePost a s L))
    (htp : ∀ a s layout bus, Spec (Labels.label NativeRustcVmX64.Vm.TablePhase.entryLabel) (TablePhasePre a s layout bus)
      (TablePhasePost a s layout bus))
    (htc : ∀ evals cs, Spec (Labels.label NativeRustcVmX64.Vm.TableColumnClaims.entryLabel) (TableColumnClaimsPre evals cs)
      (TableColumnClaimsPost evals cs))
    (hpi : ∀ a s layout pub cs, Spec (Labels.label NativeRustcVmX64.Vm.PublicInputPhase.entryLabel)
      (PublicInputPhasePre a s layout pub cs) (PublicInputPhasePost a s layout pub cs))
    (hkp : ∀ a s cs layout evals, Spec (Labels.label NativeRustcVmX64.Vm.KeccakPhase.entryLabel)
      (KeccakPhasePre a s cs layout evals) (KeccakPhasePost a s cs layout evals))
    (hrs : ∀ a s point, Spec (Labels.label NativeRustcVmX64.Vm.RingSwitch.entryLabel) (RingSwitchPre a s)
      (RingSwitchPost a s point))
    (hvso : ∀ a s layout target coefficients point slices cs z value,
      Spec (Labels.label NativeRustcVmX64.Vm.VerifyStackedOpening.entryLabel)
        (VerifyStackedOpeningPre a s layout target coefficients point slices cs z value)
        (VerifyStackedOpeningPost a s layout target coefficients point cs z value))
    {a : DecArea} {m0 : MachineData} (g : Geo a m0) {st : MachineState} (h : At m0 st.data)
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyExecution.b2Offset)) {rate : Nat} (hrdx : (reg st.data .rdx).toNat = rate)
    (h12 : reg st.data .r12 = reg m0 .rsi) (h13 : reg st.data .r13 = reg m0 .rdx)
    (h40 : NativeRustcVm.WordAt st.data.dmem (off (stackBelow m0 96) 40)
      (UInt64.ofBitVec (reg m0 .rcx)))
    {P : Vector UInt64 4} (hP : NativeRustcVm.WordsAt m0.dmem (reg m0 .rcx) P.toList)
    {s : TState} (hts : TStateAt st.data.dmem (reg m0 .rdi) a s) (hroots : s.roots.size = 0)
    {L : LayoutW} (hL : LayoutWAt st.data.dmem (reg m0 .r8) L) (hsl : L.stackLog ≤ 30)
    (hvc : (L.placement memory0).variableCount ≤ 31) (hBn : L.bytecode.size = (reg m0 .rdx).toNat)
    (hB : NativeRustcVm.WordsAt m0.dmem (reg m0 .rsi) L.bytecode.toList) :
    Eventually (step1 Host.exe) (Done a m0 ((walkCommit P L rate).run s)) st := by
  have hR := g.R
  have h8 := g.e8
  have hF := g.F
  have hwN := g.wN
  have hN : commitStackStack = 704 := rfl
  have hwf := frame_wf (m0 := m0) (d := st.data) (F := 96) (rest := [(reg m0 .r8, 72)])
    (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyExecution.b2Offset + b2.length)).toBitVec)
    ⟨Mapped.keeps g.fmapped h.frame.kept, g.fnw⟩
    (fun x hx ↦ by
      rw [List.mem_singleton] at hx; subst hx
      exact ⟨Mapped.keeps (NativeRustcVm.Mapped.mono g.mW (show 72 ≤ 495552 by decide))
        h.frame.kept, by show (reg m0 .r8).toNat + 72 ≤ 2 ^ 64; omega⟩)
    (List.pairwise_pair.mpr (by
      unfold NativeRustcVm.Apart; dsimp only; rw [hF]; have := g.wS; omega))
  have hm : Match (frameEnv m0 st.data 96 [(reg m0 .r8, 72)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyExecution.b2Offset + b2.length)).toBitVec) workS st.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨h.frame.rsp_eval, known_ptr rfl h.rbx, trivial⟩ trivial
      trivial trivial
  refine exec_at (infix_of b2_in_code (by simp [b2]) hp) run_b2 hwf (fun _ _ ↦ rfl) hpc hm
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hmid, hw1, hrdi, hrsi, hrdx', hr15, hrbp, hrbx, hk⟩ := after_eq run_b2 ▸ ok_b2
  have hs1 : NativeRustcVm.SameOutside st.data.dmem st1.data.dmem
      (NativeRustcVm.InRange (stackBelow m0 96) 40) :=
    sameOutside_low hwf hm1 (r := 0) rfl (by decide) hw1
  have hs1' : ∀ q, NativeRustcVm.InRange (stackBelow m0 96) 40 q →
      vsb m0 + 17792 ≤ q.toNat ∧ q.toNat < vsb m0 + 17832 := fun q hq ↦ by
    rw [inR (by unfold NativeRustcVm.NoWrap; omega), hF] at hq
    omega
  have hC : AtCall m0 st1.data := ⟨Frame.of_block h.frame hwf hm1 hmid slots_le, fun q hq ↦ by
    rw [hs1 q fun hq' ↦ hq (wr_s g (by have := hs1' q hq'; omega))]
    exact h.same q hq⟩
  have kr : ∀ r ∈ [Reg64.r12, .r13, .r14], reg st1.data r = reg st.data r :=
    fun r hr ↦ hm1.regs r (.reg r) (by simpa using List.all_eq_true.mp hk r hr)
  have hsw : NativeRustcVm.WordAt st.data.dmem (off (reg m0 .r8) 16) L.stackLog.toUInt64 :=
    hL.stack_log
  have eload : (Sym.load 1 16 8).eval (frameEnv m0 st.data 96 [(reg m0 .r8, 72)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyExecution.b2Offset + b2.length)).toBitVec) = L.stackLog.toUInt64.toBitVec :=
    load_ofMachine (r := 1) (b := reg m0 .r8) (n := 72) rfl hsw
  have hslN : L.stackLog.toUInt64.toNat = L.stackLog := by
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  have eRdi : reg st1.data .rdi = reg m0 .rdi := (hm1.regs .rdi _ hrdi).trans h.r14
  have eRsi : (reg st1.data .rsi).toNat = L.stackLog := by
    rw [show reg st1.data .rsi = _ from (hm1.regs .rsi _ hrsi).trans eload]; exact hslN
  have eRdx : (reg st1.data .rdx).toNat = rate := by
    rw [show reg st1.data .rdx = _ from hm1.regs .rdx _ hrdx']; exact hrdx
  have eR15 : (reg st1.data .r15).toNat = rate := by
    rw [show reg st1.data .r15 = _ from hm1.regs .r15 _ hr15]; exact hrdx
  have eRbp : (reg st1.data .rbp).toNat = L.stackLog := by
    rw [show reg st1.data .rbp = _ from (hm1.regs .rbp _ hrbp).trans eload]; exact hslN
  have eRbx : reg st1.data .rbx = reg m0 .r8 := (hm1.regs .rbx _ hrbx).trans (eval_ptr rfl)
  have hts1 : TStateAt st1.data.dmem (reg m0 .rdi) a s :=
    hts.frame (fun p hp ↦ hm1.kept hwf p hp) (fun q hq ↦ by
      have := hs1' q hq
      have := g.aS
      have := g.tS
      refine ⟨fun hi ↦ ?_, fun hi ↦ ?_⟩
      · have := (inR g.tN).mp hi; omega
      · have := (inR g.aN).mp hi; omega) hs1
  have hc : (32 : Nat) ≤ 96 := by decide
  have hN' : 704 ≤ 17792 + 32 := by decide
  have hRo := hC.rodataAt g hc hN'
  have hpre : CommitStackPre a s st1.data := by
    unfold CommitStackPre
    simp only [eRdi]
    rw [hN]
    refine ⟨hC.stackOk g hc hN', hRo.rcAt, hRo, hts1, hC.tstateOk g hc hN',
      by rw [hroots]; decide, ?_⟩
    apply GotAt.symbols (symbols := ["memcpy", "memset"]) (hs := by decide)
    apply hC.got g hc hN'
    intro l hl
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨g.gotT hl, g.gotA hl, g.gotRc hl⟩
  refine call_then hpc1 (hcs a s) hpre fun st2 hpc2 hrsp2 hpost ↦ ?_
  obtain ⟨hok, hnext, hch, hsv⟩ := hpost
  simp only [eRdi, eRsi, eRdx, hN] at hok hnext hch
  have hR2 : ∀ q, (NativeRustcVm.InRange (reg m0 .rdi) tstateBytes q ∨
      NativeRustcVm.InRange (stackBelow st1.data 704) 704 q) →
      (vsb m0 ≤ q.toNat ∧ q.toNat < vsb m0 + 17824) ∨
      ((reg m0 .rdi).toNat ≤ q.toNat ∧ q.toNat < (reg m0 .rdi).toNat + 760) := by
    rintro q (hq | hq)
    · exact Or.inr (g.inT hq)
    · have := hC.inS g hc hN' hq; left; omega
  have h2 : At m0 st2.data := hC.ret g eRbx ((kr .r14 (by simp)).trans h.r14) hsv hrsp2 hch
    fun q hq ↦ by
      rcases hR2 q hq with hq | hq
      · exact Or.inl hq
      · exact Or.inr (Or.inl hq)
  have hsA := NativeRustcVm.Transcript.SameOutside.trans hs1 hch
  have hRA : ∀ q, (NativeRustcVm.InRange (stackBelow m0 96) 40 q ∨
      (NativeRustcVm.InRange (reg m0 .rdi) tstateBytes q ∨
        NativeRustcVm.InRange (stackBelow st1.data 704) 704 q)) →
      (vsb m0 ≤ q.toNat ∧ q.toNat < vsb m0 + 17832) ∨
      ((reg m0 .rdi).toNat ≤ q.toNat ∧ q.toNat < (reg m0 .rdi).toNat + 760) := by
    rintro q (hq | hq)
    · have := hs1' q hq; left; omega
    · rcases hR2 q hq with h' | h'
      · left; omega
      · exact Or.inr h'
  have hsC : NativeRustcVm.Layout.Same st.data.dmem st2.data.dmem (off (reg m0 .r8) 0) 3912 :=
    g.same hsA (by omega) (by omega) fun q hq ↦ by
      have := g.wS
      have := g.tw
      rcases hRA q hq with h' | h' <;> omega
  have h40' : NativeRustcVm.WordAt st2.data.dmem (off (stackBelow m0 96) 40)
      (UInt64.ofBitVec (reg m0 .rcx)) :=
    keep40 g hsA (fun q hq ↦ by
      rcases hRA q hq with h' | h'
      · left; omega
      · right; right; left; exact h') h40
  -- `b3`: the test
  rw [walkCommit, run_bind_eq]
  generalize hr : (commitStack L.stackLog rate).run s = r at hok hnext
  refine branch hp g b3_in_code (by simp [b3]) (by rw [after_eq run_b3]; exact run_b3)
    (ok_test b3 (by simp)) h2 (hpc2.trans (by rw [show k + NativeRustcVmX64.Vm.VerifyExecution.b2Offset + b2.length = k + NativeRustcVmX64.Vm.VerifyExecution.b3Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyExecution.b2_next]]))
    hok (fun hb ↦ by cases r with | none => rfl | some _ => cases hb)
    fun st3 hb h3 hd3 hk3 hpc3 ↦ ?_
  obtain ⟨⟨u, s'⟩, rfl⟩ := Option.isSome_iff_exists.mp hb
  have hts' := hnext _ _ rfl
  have hroots' : s'.roots.size ≤ s.roots.size + 1 :=
    (commitStack_roots L.stackLog rate).grows _ _ _ hr
  have k12 : reg st3.data .r12 = reg st1.data .r12 := (hk3 .r12 (by simp)).trans (hsv.1 .r12 rfl)
  have k13 : reg st3.data .r13 = reg st1.data .r13 := (hk3 .r13 (by simp)).trans (hsv.1 .r13 rfl)
  have k15 : reg st3.data .r15 = reg st1.data .r15 := (hk3 .r15 (by simp)).trans (hsv.1 .r15 rfl)
  have kbp : reg st3.data .rbp = reg st1.data .rbp := (hk3 .rbp (by simp)).trans (hsv.1 .rbp rfl)
  have hL3 : LayoutWAt st3.data.dmem (off (reg m0 .r8) 0) L := by
    rw [hd3]
    exact NativeRustcVm.Tables.LayoutWAt.of_same (by rw [off_zero]; exact hL) hsC
  rw [off_zero] at hL3
  exact callOod hp hro hbb htp htc hpi hkp hrs hvso g h3
    (hpc3.trans (by rw [show k + NativeRustcVmX64.Vm.VerifyExecution.b3Offset + b3.length = k + NativeRustcVmX64.Vm.VerifyExecution.b4Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyExecution.b3_next]])) (rate := rate)
    (by rw [k15]; exact eR15) (by rw [k12, kr _ (by simp)]; exact h12)
    (by rw [k13, kr _ (by simp)]; exact h13) (by rw [kbp]; exact eRbp)
    (by rw [hd3]; exact h40') hP (by rw [hd3]; exact hts') (show s'.roots.size ≤ 2 by omega) hL3 hsl hvc hBn hB

end

end NativeRustcVmX64.Top.VerifyExecution
