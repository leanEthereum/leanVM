module

public import NativeRustcVmX64.Top.VerifyExecution.Tables
public import NativeRustcVmX64.Code.Vm.KeccakPhase.Names
public import NativeRustcVmX64.Code.Vm.PublicInputPhase.Names
public import NativeRustcVmX64.Code.Vm.RingSwitch.Names
public import NativeRustcVmX64.Code.Vm.TableColumnClaims.Names
public import NativeRustcVmX64.Code.Vm.TablePhase.Names
public import NativeRustcVmX64.Code.Vm.VerifyBusBalance.Names
public import NativeRustcVmX64.Code.Vm.VerifyStackedOpening.Names

/-!
# `verify_execution`: the bus (x86-64)

`b6` calls `verify_bus_balance` on the layout, the bytecode (R12, R13), the bus's result and the
column claims (kept in R12, R13); `b7` returns `0` when it failed, else the tables (`callBus`).
-/

namespace NativeRustcVmX64.Top.VerifyExecution

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.VerifyExecution NativeRustcVmX64.Transcript
open NativeRustcVmX64.Top NativeRustcVm.Transcript NativeVm.Model
open NativeRustcVm.Top (workAreaBytes walkBus run_bind_eq)
open NativeRustcVm.Layout (LayoutWAt ClaimsWAt OodAt claimCap)
open LeanVM.Protocol.Verifier (memory0)

public section

section
variable [Labels] {a : DecArea} {m0 d : MachineData}

/-- The bytecode's words stay. -/
theorem AtCall.bc (h : AtCall m0 d) (g : Geo a m0) {bcw : List UInt64}
    (hl : bcw.length = (reg m0 .rdx).toNat) (hw : NativeRustcVm.WordsAt m0.dmem (reg m0 .rsi) bcw) :
    NativeRustcVm.WordsAt d.dmem (reg m0 .rsi) bcw := by
  rcases Nat.eq_zero_or_pos (reg m0 .rdx).toNat with hn | hn
  · rw [List.eq_nil_of_length_eq_zero (hl.trans hn)]
    exact NativeRustcVm.wordsAt_nil _ _
  · refine hw.of_sameOutside h.same fun i hi hq ↦ ?_
    rw [NativeRustcVm.length_wordsBytes, hl] at hi
    have := g.bN
    have := g.bt hn
    have := g.bw hn
    have := g.bS hn
    have e : (reg m0 .rsi + BitVec.ofNat 64 i).toNat = (reg m0 .rsi).toNat + i :=
      NativeRustcVm.toNat_add_ofNat (by omega)
    rcases g.writable hq with h' | h' | h' <;> omega

end

variable [Host] {k : Nat}

/-- **The bus**, from `b6`: the function returns the walk's rest. -/
theorem callBus (hp : Placed code k)
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
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyExecution.b6Offset)) {rate : Nat} (h15 : (reg st.data .r15).toNat = rate)
    (h12 : reg st.data .r12 = reg m0 .rsi) (h13 : reg st.data .r13 = reg m0 .rdx)
    (hbp : reg st.data .rbp = off (reg m0 .r8) 3912)
    (h40 : NativeRustcVm.WordAt st.data.dmem (off (stackBelow m0 96) 40)
      (UInt64.ofBitVec (reg m0 .rcx)))
    {P : Vector UInt64 4} (hP : NativeRustcVm.WordsAt m0.dmem (reg m0 .rcx) P.toList)
    {s : TState} (hts : TStateAt st.data.dmem (reg m0 .rdi) a s) (hroots : s.roots.size ≤ 2)
    {L : LayoutW} (hL : LayoutWAt st.data.dmem (reg m0 .r8) L)
    (hvc : (L.placement memory0).variableCount ≤ 31) (hBn : L.bytecode.size = (reg m0 .rdx).toNat)
    (hB : NativeRustcVm.WordsAt m0.dmem (reg m0 .rsi) L.bytecode.toList)
    {ood : StackClaimW} (hood : OodAt st.data.dmem (off (reg m0 .r8) 3912) ood) :
    Eventually (step1 Host.exe) (Done a m0 ((walkBus P L rate ood).run s)) st := by
  have hR := g.R
  have h8 := g.e8
  have hF := g.F
  have hwN := g.wN
  have hN : verifyBusBalanceStack = 17824 := rfl
  obtain ⟨hwf, hm⟩ := h.env g (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyExecution.b6Offset + b6.length)).toBitVec)
  refine exec_at (infix_of b6_in_code (by simp [b6]) hp) run_b6 hwf (fun _ _ ↦ rfl) hpc hm
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hmid, hw1, hrdi, hrsi, hrdx, hrcx, hr8, hr9, hr12, hr13, hk⟩ := after_eq run_b6 ▸ ok_b6
  have hC : AtCall m0 st1.data := h.toCall g hwf hm1 hmid (by decide) hw1
  have hs1 : NativeRustcVm.SameOutside st.data.dmem st1.data.dmem
      (NativeRustcVm.InRange (stackBelow m0 96) 40) :=
    sameOutside_low hwf hm1 (r := 0) rfl (by decide) hw1
  have hs1' : ∀ q, NativeRustcVm.InRange (stackBelow m0 96) 40 q →
      vsb m0 + 17792 ≤ q.toNat ∧ q.toNat < vsb m0 + 17832 := fun q hq ↦ by
    rw [inR (by unfold NativeRustcVm.NoWrap; omega), hF] at hq
    omega
  have kr : ∀ r ∈ [Reg64.rbx, .r14, .r15, .rbp], reg st1.data r = reg st.data r :=
    fun r hr ↦ hm1.regs r (.reg r) (by simpa using List.all_eq_true.mp hk r hr)
  have eadd : ∀ c : Nat, (Sym.bin .add .W64 (.reg .rbx) (.lit c)).eval (frameEnv m0 st.data 96 []
      (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyExecution.b6Offset + b6.length)).toBitVec) = off (reg m0 .r8) c := fun c ↦ by
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]
    exact congrArg (· + BitVec.ofNat 64 c) h.rbx
  have eRdi : reg st1.data .rdi = reg m0 .rdi := (hm1.regs .rdi _ hrdi).trans h.r14
  have eRsi : reg st1.data .rsi = off (reg m0 .r8) 0 := by
    rw [off_zero]; exact (hm1.regs .rsi _ hrsi).trans h.rbx
  have eRdx : reg st1.data .rdx = reg m0 .rsi := (hm1.regs .rdx _ hrdx).trans h12
  have eRcx : reg st1.data .rcx = reg m0 .rdx := (hm1.regs .rcx _ hrcx).trans h13
  have eR8 : reg st1.data .r8 = off (reg m0 .r8) 4416 := (hm1.regs .r8 _ hr8).trans (eadd _)
  have eR9 : reg st1.data .r9 = off (reg m0 .r8) 123992 := (hm1.regs .r9 _ hr9).trans (eadd _)
  have eR12 : reg st1.data .r12 = off (reg m0 .r8) 4416 := (hm1.regs .r12 _ hr12).trans (eadd _)
  have eR13 : reg st1.data .r13 = off (reg m0 .r8) 123992 := (hm1.regs .r13 _ hr13).trans (eadd _)
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
  have hc : (32 : Nat) ≤ 96 := by decide
  have hN' : 17824 ≤ 17792 + 32 := by decide
  have hRd := hC.rodataAt g hc hN'
  have hsb := hC.sb g hc hN'
  have hpre : VerifyBusBalancePre a s L st1.data := by
    unfold VerifyBusBalancePre InOk
    simp only [eRdi, eRsi, eRdx, eRcx, eR8, eR9]
    rw [hN]
    have hbt := g.bt
    have hbw := g.bw
    have hbS := g.bS
    have hwS := g.wS
    refine ⟨hC.stackOk g hc hN', hRd.rcAt, hRd, hts1, hC.tstateOk g hc hN', hL1,
      ⟨hC.readable g (o := 0) (n := 3912) (by omega) (by omega),
        hC.offStack g hc (o := 0) (n := 3912) (by omega) (by omega) hN'⟩,
      g.apartWT (o := 0) (n := 3912) (by omega) (by omega), hBn,
      hC.bc g (by rw [Array.length_toList, hBn]) hB,
      ⟨Mapped.keeps g.mB hC.frame.kept, g.bN⟩, fun hn ↦ ?_,
      hC.outOk g hc (o := 4416) (n := 107768) (by omega) (by omega) hN',
      g.wRod (o := 4416) (n := 107768) (by omega) (by omega),
      g.apartW (o := 4416) (n := 107768) (o' := 0) (n' := 3912) (by omega) (by omega) (by omega),
      fun hn ↦ ?_,
      hC.outOk g hc (o := 123992) (n := 97288) (by omega) (by omega) hN',
      g.wRod (o := 123992) (n := 97288) (by omega) (by omega),
      g.apartW (o := 123992) (n := 97288) (o' := 0) (n' := 3912) (by omega) (by omega) (by omega),
      fun hn ↦ ?_,
      g.apartW (o := 4416) (n := 107768) (o' := 123992) (n' := 97288) (by omega) (by omega)
        (by omega), g.rt, fun hn ↦ ?_, ?_⟩
    · have := hbS hn
      show _ ∨ _
      rw [hsb]; omega
    · have := hbw hn
      show NativeRustcVm.Apart (off (reg m0 .r8) 4416) 107768 _ _
      unfold NativeRustcVm.Apart; rw [g.wo (by decide)]; omega
    · have := hbw hn
      show NativeRustcVm.Apart (off (reg m0 .r8) 123992) 97288 _ _
      unfold NativeRustcVm.Apart; rw [g.wo (by decide)]; omega
    · have := hbt hn
      show NativeRustcVm.Apart _ _ (reg m0 .rdi) 760
      unfold NativeRustcVm.Apart; omega
    · apply hC.got g hc hN'
      intro l hl
      simp only [List.append_assoc]
      intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
        · exact g.gotT hl
        · exact g.gotA hl
        · exact g.gotW hl (by omega) (by dsimp only; decide)
        · exact g.gotW hl (by omega) (by dsimp only; decide)
        · exact g.gotW hl (by omega) (by dsimp only; decide)
        · exact g.gotRc hl
      · rcases List.mem_append.mp hr with hr | hr
        · by_cases hn : (reg m0 .rdx).toNat = 0
          · simp only [hn, ↓reduceIte, List.mem_nil_iff] at hr
          · simp only [hn, ↓reduceIte, List.mem_cons, List.mem_nil_iff, or_false] at hr
            subst r
            exact g.gotB hl hn
        · obtain ⟨t, _, rfl⟩ := List.mem_map.mp hr
          exact g.gotRod hl t
  refine call_then hpc1 (hbb a s L) hpre fun st2 hpc2 hrsp2 hpost ↦ ?_
  obtain ⟨hok, hres, hch, hsv⟩ := hpost
  simp only [eRdi, eR8, eR9, hN, show NativeRustcVm.Bus.busBytes = 107768 from rfl,
    show NativeRustcVm.Layout.claimsBytes = 97288 from rfl] at hres hch
  have hR2 : ∀ q, (NativeRustcVm.InRange (reg m0 .rdi) tstateBytes q ∨
      NativeRustcVm.InRange (off (reg m0 .r8) 4416) 107768 q ∨
      NativeRustcVm.InRange (off (reg m0 .r8) 123992) 97288 q ∨
      NativeRustcVm.InRange (stackBelow st1.data 17824) 17824 q) →
      (vsb m0 ≤ q.toNat ∧ q.toNat < vsb m0 + 17824) ∨
      ((reg m0 .rdi).toNat ≤ q.toNat ∧ q.toNat < (reg m0 .rdi).toNat + 760) ∨
      ((reg m0 .r8).toNat + 4416 ≤ q.toNat ∧ q.toNat < (reg m0 .r8).toNat + 221280) := by
    rintro q (hq | hq | hq | hq)
    · exact Or.inr (Or.inl (g.inT hq))
    · have := g.inW (o := 4416) (n := 107768) (by omega) (by omega) hq; omega
    · have := g.inW (o := 123992) (n := 97288) (by omega) (by omega) hq; omega
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
        NativeRustcVm.InRange (off (reg m0 .r8) 4416) 107768 q ∨
        NativeRustcVm.InRange (off (reg m0 .r8) 123992) 97288 q ∨
        NativeRustcVm.InRange (stackBelow st1.data 17824) 17824 q)) →
      (vsb m0 ≤ q.toNat ∧ q.toNat < vsb m0 + 17832) ∨
      ((reg m0 .rdi).toNat ≤ q.toNat ∧ q.toNat < (reg m0 .rdi).toNat + 760) ∨
      ((reg m0 .r8).toNat + 4416 ≤ q.toNat ∧ q.toNat < (reg m0 .r8).toNat + 221280) := by
    rintro q (hq | hq)
    · have := hs1' q hq; left; omega
    · rcases hR2 q hq with h' | h' | h'
      · left; omega
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr h')
  have hsC : ∀ {o n : Nat}, o < 495552 → o + n ≤ 4416 →
      NativeRustcVm.Layout.Same st.data.dmem st2.data.dmem (off (reg m0 .r8) o) n :=
    fun ho hn ↦ g.same hsA ho (by omega) fun q hq ↦ by
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
  -- `b7`: the test
  rw [walkBus, run_bind_eq]
  generalize hr : (verifyBusBalance L).run s = r at hok hres
  refine branch hp g b7_in_code (by simp [b7]) (by rw [after_eq run_b7]; exact run_b7)
    (ok_test b7 (by simp)) h2 (hpc2.trans (by rw [show k + NativeRustcVmX64.Vm.VerifyExecution.b6Offset + b6.length = k + NativeRustcVmX64.Vm.VerifyExecution.b7Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyExecution.b6_next]]))
    hok (fun hb ↦ by cases r with | none => rfl | some _ => cases hb)
    fun st3 hb h3 hd3 hk3 hpc3 ↦ ?_
  obtain ⟨⟨bus, s'⟩, rfl⟩ := Option.isSome_iff_exists.mp hb
  obtain ⟨hts', hbus, hcl⟩ := hres _ _ rfl
  have hcs := (NativeRustcVm.Top.verifyBusBalance_claims L).gives _ _ _ hr
  have hroots' : s'.roots = s.roots := (NativeVm.Math.verifyBusBalance_roots L).keeps _ _ _ hr
  have k12 : reg st3.data .r12 = reg st1.data .r12 := (hk3 .r12 (by simp)).trans (hsv.1 .r12 rfl)
  have k13 : reg st3.data .r13 = reg st1.data .r13 := (hk3 .r13 (by simp)).trans (hsv.1 .r13 rfl)
  have k15 : reg st3.data .r15 = reg st1.data .r15 := (hk3 .r15 (by simp)).trans (hsv.1 .r15 rfl)
  have kbp : reg st3.data .rbp = reg st1.data .rbp := (hk3 .rbp (by simp)).trans (hsv.1 .rbp rfl)
  have hL3 : LayoutWAt st3.data.dmem (off (reg m0 .r8) 0) L := by
    rw [hd3]
    exact NativeRustcVm.Tables.LayoutWAt.of_same (by rw [off_zero]; exact hL)
      (hsC (o := 0) (n := 3912) (by omega) (by omega))
  rw [off_zero] at hL3
  have hood3 : OodAt st3.data.dmem (off (reg m0 .r8) 3912) ood := by
    rw [hd3]
    exact NativeRustcVm.Top.OodAt.of_same hood (hsC (n := 504) (by omega) (by omega))
  exact callTables hp htp htc hpi hkp hrs hvso g h3
    (hpc3.trans (by rw [show k + NativeRustcVmX64.Vm.VerifyExecution.b7Offset + b7.length = k + NativeRustcVmX64.Vm.VerifyExecution.b8Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyExecution.b7_next]])) (rate := rate)
    (by rw [k15, kr _ (by simp)]; exact h15) (by rw [k12]; exact eR12) (by rw [k13]; exact eR13)
    (by rw [kbp, kr _ (by simp)]; exact hbp)
    (by rw [hd3]; exact h40') hP (by rw [hd3]; exact hts') (by rw [hroots']; exact hroots) hL3 hvc
    (by rw [hd3]; exact hbus) (by rw [hd3]; exact hcl) hcs hood3

end

end NativeRustcVmX64.Top.VerifyExecution
