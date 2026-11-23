module

public import NativeRustcVmX64.Top.VerifyExecution.Claims
public import NativeRustcVmX64.Code.Vm.KeccakPhase.Names
public import NativeRustcVmX64.Code.Vm.PublicInputPhase.Names
public import NativeRustcVmX64.Code.Vm.RingSwitch.Names
public import NativeRustcVmX64.Code.Vm.TableColumnClaims.Names
public import NativeRustcVmX64.Code.Vm.TablePhase.Names
public import NativeRustcVmX64.Code.Vm.VerifyStackedOpening.Names

/-!
# `verify_execution`: the tables (x86-64)

`b8` calls `table_phase` on the layout, the bus's result and the tables' evaluations' entries
(kept in R12); `b9` returns `0` when it failed, else the tables' column claims (`callTables`).
-/

namespace NativeRustcVmX64.Top.VerifyExecution

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.VerifyExecution NativeRustcVmX64.Transcript
open NativeRustcVmX64.Top NativeRustcVm.Transcript NativeVm.Model
open NativeRustcVm.Top (workAreaBytes walkTables run_bind_eq)
open NativeRustcVm.Layout (LayoutWAt ClaimsWAt OodAt claimCap)
open NativeRustcVm.Tables (TableEvalsAt)
open NativeRustcVm.Bus (BusWAt)
open LeanVM.Protocol.Verifier (memory0)

public section

variable [Host] {k : Nat}

/-- **The tables**, from `b8`: the function returns the walk's rest. -/
theorem callTables (hp : Placed code k)
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
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyExecution.b8Offset)) {rate : Nat} (h15 : (reg st.data .r15).toNat = rate)
    (h12 : reg st.data .r12 = off (reg m0 .r8) 4416)
    (h13 : reg st.data .r13 = off (reg m0 .r8) 123992)
    (hbp : reg st.data .rbp = off (reg m0 .r8) 3912)
    (h40 : NativeRustcVm.WordAt st.data.dmem (off (stackBelow m0 96) 40)
      (UInt64.ofBitVec (reg m0 .rcx)))
    {P : Vector UInt64 4} (hP : NativeRustcVm.WordsAt m0.dmem (reg m0 .rcx) P.toList)
    {s : TState} (hts : TStateAt st.data.dmem (reg m0 .rdi) a s) (hroots : s.roots.size ≤ 2)
    {L : LayoutW} (hL : LayoutWAt st.data.dmem (reg m0 .r8) L)
    (hvc : (L.placement memory0).variableCount ≤ 31) {bus : BusResultW}
    (hbus : BusWAt st.data.dmem (off (reg m0 .r8) 4416) bus)
    (hcl : ClaimsWAt st.data.dmem (off (reg m0 .r8) 123992) bus.claims)
    (hcs : bus.claims.size = 4)
    {ood : StackClaimW} (hood : OodAt st.data.dmem (off (reg m0 .r8) 3912) ood) :
    Eventually (step1 Host.exe) (Done a m0 ((walkTables P L rate ood bus).run s)) st := by
  have hR := g.R
  have h8 := g.e8
  have hF := g.F
  have hwN := g.wN
  have hN : tablePhaseStack = 1872 := rfl
  obtain ⟨hwf, hm⟩ := h.env g (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyExecution.b8Offset + b8.length)).toBitVec)
  refine exec_at (infix_of b8_in_code (by simp [b8]) hp) run_b8 hwf (fun _ _ ↦ rfl) hpc hm
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hmid, hw1, hrdi, hrsi, hrdx, hrcx, hr12, hk⟩ := after_eq run_b8 ▸ ok_b8
  have hC : AtCall m0 st1.data := h.toCall g hwf hm1 hmid (by decide) hw1
  have hs1 : NativeRustcVm.SameOutside st.data.dmem st1.data.dmem
      (NativeRustcVm.InRange (stackBelow m0 96) 40) :=
    sameOutside_low hwf hm1 (r := 0) rfl (by decide) hw1
  have hs1' : ∀ q, NativeRustcVm.InRange (stackBelow m0 96) 40 q →
      vsb m0 + 17792 ≤ q.toNat ∧ q.toNat < vsb m0 + 17832 := fun q hq ↦ by
    rw [inR (by unfold NativeRustcVm.NoWrap; omega), hF] at hq
    omega
  have kr : ∀ r ∈ [Reg64.rbx, .r13, .r14, .r15, .rbp], reg st1.data r = reg st.data r :=
    fun r hr ↦ hm1.regs r (.reg r) (by simpa using List.all_eq_true.mp hk r hr)
  have eadd : (Sym.bin .add .W64 (.reg .rbx) (.lit 112184)).eval (frameEnv m0 st.data 96 []
      (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyExecution.b8Offset + b8.length)).toBitVec) = off (reg m0 .r8) 112184 := by
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]
    exact congrArg (· + BitVec.ofNat 64 112184) h.rbx
  have eRdi : reg st1.data .rdi = reg m0 .rdi := (hm1.regs .rdi _ hrdi).trans h.r14
  have eRsi : reg st1.data .rsi = off (reg m0 .r8) 0 := by
    rw [off_zero]; exact (hm1.regs .rsi _ hrsi).trans h.rbx
  have eRdx : reg st1.data .rdx = off (reg m0 .r8) 4416 := (hm1.regs .rdx _ hrdx).trans h12
  have eRcx : reg st1.data .rcx = off (reg m0 .r8) 112184 := (hm1.regs .rcx _ hrcx).trans eadd
  have eR12 : reg st1.data .r12 = off (reg m0 .r8) 112184 := (hm1.regs .r12 _ hr12).trans eadd
  have hsW : ∀ {o n : Nat}, o < 495552 → o + n ≤ 495552 →
      NativeRustcVm.Layout.Same st.data.dmem st1.data.dmem (off (reg m0 .r8) o) n := fun ho hn ↦
    g.same hs1 ho hn fun q hq ↦ by have := hs1' q hq; have := g.wS; omega
  have hts1 : TStateAt st1.data.dmem (reg m0 .rdi) a s :=
    hts.frame (fun p hp ↦ hm1.kept hwf p hp) (fun q hq ↦ by
      have := hs1' q hq
      have := g.aS
      have := g.tS
      refine ⟨fun hi ↦ ?_, fun hi ↦ ?_⟩
      · have := (inR g.tN).mp hi; omega
      · have := (inR g.aN).mp hi; omega) hs1
  have hL1 : LayoutWAt st1.data.dmem (off (reg m0 .r8) 0) L :=
    NativeRustcVm.Tables.LayoutWAt.of_same (by rw [off_zero]; exact hL)
      (hsW (o := 0) (n := 3912) (by omega) (by omega))
  have hbus1 := NativeRustcVm.Tables.BusWAt.of_same hbus (hsW (n := 107768) (by omega) (by omega))
  have hc : (32 : Nat) ≤ 96 := by decide
  have hN' : 1872 ≤ 17792 + 32 := by decide
  have hws : ∀ {o n : Nat}, o + n ≤ 112184 →
      ∀ w ∈ [(⟨reg m0 .rdi, tstateBytes⟩ : NativeRustcVm.Region),
        ⟨off (reg m0 .r8) 112184, NativeRustcVm.Tables.tableEvalsBytes⟩],
      NativeRustcVm.Apart (off (reg m0 .r8) o) n w.addr w.size :=
    fun hn ↦ by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨g.apartWT (by omega) (by omega),
        g.apartW (o' := 112184) (n' := 11808) (by omega) (by omega) (by omega)⟩
  have hRd := hC.rodataAt g hc hN'
  have hpre : TablePhasePre a s L bus st1.data := by
    unfold TablePhasePre TablesAt
    simp only [eRdi, eRsi, eRdx, eRcx]
    rw [hN]
    refine ⟨hC.stackOk g hc hN', hRd.rcAt, hRd, hts1, hC.tstateOk g hc hN',
      hC.outOk g hc (o := 112184) (n := 11808) (by omega) (by omega) hN', g.rt,
      g.wRod (o := 112184) (n := 11808) (by omega) (by omega),
      ⟨hC.readable g (o := 0) (n := 3912) (by omega) (by omega),
        hC.offStack g hc (o := 0) (n := 3912) (by omega) (by omega) hN', hws (n := 3912) (by omega)⟩, hL1,
      ⟨hC.readable g (o := 4416) (n := 107768) (by omega) (by omega),
        hC.offStack g hc (o := 4416) (n := 107768) (by omega) (by omega) hN', hws (n := 107768) (by omega)⟩,
      hbus1, ?_⟩
    apply GotAt.symbols (symbols := ["memcpy", "memset"]) (hs := by decide)
    apply hC.got g hc hN'
    intro l hl
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨g.gotT hl, g.gotA hl, g.gotW hl (by omega) (by decide),
      g.gotW hl (by omega) (by decide), g.gotW hl (by omega) (by decide),
      g.gotRc hl, g.gotRod hl .tables⟩
  refine call_then hpc1 (htp a s L bus) hpre fun st2 hpc2 hrsp2 hpost ↦ ?_
  obtain ⟨hok, hres, hnext, hch, hsv⟩ := hpost
  simp only [eRdi, eRcx, hN, show NativeRustcVm.Tables.tableEvalsBytes = 11808 from rfl]
    at hres hnext hch
  have hR2 : ∀ q, (NativeRustcVm.InRange (reg m0 .rdi) tstateBytes q ∨
      NativeRustcVm.InRange (off (reg m0 .r8) 112184) 11808 q ∨
      NativeRustcVm.InRange (stackBelow st1.data 1872) 1872 q) →
      (vsb m0 ≤ q.toNat ∧ q.toNat < vsb m0 + 17824) ∨
      ((reg m0 .rdi).toNat ≤ q.toNat ∧ q.toNat < (reg m0 .rdi).toNat + 760) ∨
      ((reg m0 .r8).toNat + 112184 ≤ q.toNat ∧ q.toNat < (reg m0 .r8).toNat + 123992) := by
    rintro q (hq | hq | hq)
    · exact Or.inr (Or.inl (g.inT hq))
    · have := g.inW (o := 112184) (n := 11808) (by omega) (by omega) hq; omega
    · have := hC.inS g hc hN' hq; left; omega
  have h2 : At m0 st2.data := hC.ret g ((kr .rbx (by simp)).trans h.rbx)
    ((kr .r14 (by simp)).trans h.r14) hsv hrsp2 hch fun q hq ↦ by
      rcases hR2 q hq with hq | hq | hq
      · exact Or.inl hq
      · exact Or.inr (Or.inl hq)
      · exact Or.inr (Or.inr ⟨by omega, by omega⟩)
  have hsA := NativeRustcVm.Transcript.SameOutside.trans hs1 hch
  have hRA : ∀ q, (NativeRustcVm.InRange (stackBelow m0 96) 40 q ∨
      (NativeRustcVm.InRange (reg m0 .rdi) tstateBytes q ∨
        NativeRustcVm.InRange (off (reg m0 .r8) 112184) 11808 q ∨
        NativeRustcVm.InRange (stackBelow st1.data 1872) 1872 q)) →
      (vsb m0 ≤ q.toNat ∧ q.toNat < vsb m0 + 17832) ∨
      ((reg m0 .rdi).toNat ≤ q.toNat ∧ q.toNat < (reg m0 .rdi).toNat + 760) ∨
      ((reg m0 .r8).toNat + 112184 ≤ q.toNat ∧ q.toNat < (reg m0 .r8).toNat + 123992) := by
    rintro q (hq | hq)
    · have := hs1' q hq; left; omega
    · rcases hR2 q hq with h' | h' | h'
      · left; omega
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr h')
  have hsC : ∀ {o n : Nat}, o < 495552 → o + n ≤ 495552 → (o + n ≤ 112184 ∨ 123992 ≤ o) →
      NativeRustcVm.Layout.Same st.data.dmem st2.data.dmem (off (reg m0 .r8) o) n :=
    fun ho hn hlh ↦ g.same hsA ho hn fun q hq ↦ by
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
  -- `b9`: the test
  rw [walkTables, run_bind_eq]
  generalize hr : (tablePhase L bus).run s = r at hok hres hnext
  refine branch hp g b9_in_code (by simp [b9]) (by rw [after_eq run_b9]; exact run_b9)
    (ok_test b9 (by simp)) h2 (hpc2.trans (by rw [show k + NativeRustcVmX64.Vm.VerifyExecution.b8Offset + b8.length = k + NativeRustcVmX64.Vm.VerifyExecution.b9Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyExecution.b8_next]]))
    hok (fun hb ↦ by cases r with | none => rfl | some _ => cases hb)
    fun st3 hb h3 hd3 hk3 hpc3 ↦ ?_
  obtain ⟨⟨ev, s'⟩, rfl⟩ := Option.isSome_iff_exists.mp hb
  have hev := hres _ _ rfl
  have hts' := hnext _ _ rfl
  have hsh := NativeRustcVm.Top.tablePhase_shape hL.heights_size hbus.forms_size hr
  have hroots' : s'.roots = s.roots := (NativeVm.Math.tablePhase_roots L bus).keeps _ _ _ hr
  have k12 : reg st3.data .r12 = reg st1.data .r12 := (hk3 .r12 (by simp)).trans (hsv.1 .r12 rfl)
  have k13 : reg st3.data .r13 = reg st1.data .r13 := (hk3 .r13 (by simp)).trans (hsv.1 .r13 rfl)
  have k15 : reg st3.data .r15 = reg st1.data .r15 := (hk3 .r15 (by simp)).trans (hsv.1 .r15 rfl)
  have kbp : reg st3.data .rbp = reg st1.data .rbp := (hk3 .rbp (by simp)).trans (hsv.1 .rbp rfl)
  have hL3 : LayoutWAt st3.data.dmem (off (reg m0 .r8) 0) L := by
    rw [hd3]
    exact NativeRustcVm.Tables.LayoutWAt.of_same (by rw [off_zero]; exact hL)
      (hsC (o := 0) (n := 3912) (by omega) (by omega) (by omega))
  rw [off_zero] at hL3
  have hcl3 : ClaimsWAt st3.data.dmem (off (reg m0 .r8) 123992) bus.claims := by
    rw [hd3]
    exact NativeRustcVm.Tables.ClaimsWAt.of_same hcl (hsC (n := 97288) (by omega) (by omega) (by omega))
  have hood3 : OodAt st3.data.dmem (off (reg m0 .r8) 3912) ood := by
    rw [hd3]
    exact NativeRustcVm.Top.OodAt.of_same hood (hsC (n := 504) (by omega) (by omega) (by omega))
  exact callClaims hp htc hpi hkp hrs hvso g h3
    (hpc3.trans (by rw [show k + NativeRustcVmX64.Vm.VerifyExecution.b9Offset + b9.length = k + NativeRustcVmX64.Vm.VerifyExecution.b10Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyExecution.b9_next]])) (rate := rate)
    (by rw [k15, kr _ (by simp)]; exact h15) (by rw [k12]; exact eR12)
    (by rw [k13, kr _ (by simp)]; exact h13) (by rw [kbp, kr _ (by simp)]; exact hbp)
    (by rw [hd3]; exact h40') hP (by rw [hd3]; exact hts') (by rw [hroots']; exact hroots) hL3 hvc
    (by rw [hd3]; exact hev) hsh hcl3 hcs hood3

end

end NativeRustcVmX64.Top.VerifyExecution
