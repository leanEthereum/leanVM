module

public import NativeRustcVmX64.Top.VerifyExecution.Public
public import NativeRustcVmX64.Code.Vm.KeccakPhase.Names
public import NativeRustcVmX64.Code.Vm.PublicInputPhase.Names
public import NativeRustcVmX64.Code.Vm.RingSwitch.Names
public import NativeRustcVmX64.Code.Vm.TableColumnClaims.Names
public import NativeRustcVmX64.Code.Vm.VerifyStackedOpening.Names

/-!
# `verify_execution`: the tables' column claims (x86-64)

`b10` calls `table_column_claims` on the tables' evaluations and the column claims; `b11` returns
`0` when they overflow, else the public input (`callClaims`).
-/

namespace NativeRustcVmX64.Top.VerifyExecution

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.VerifyExecution NativeRustcVmX64.Transcript
open NativeRustcVmX64.Top NativeRustcVm.Transcript NativeVm.Model
open NativeRustcVm.Top (workAreaBytes walkPublic)
open NativeRustcVm.Layout (LayoutWAt ClaimsWAt OodAt claimCap)
open NativeRustcVm.Tables (TableEvalsAt)
open LeanVM.Protocol.Verifier (opKeccak keccakOut memory0)

public section

variable [Host] {k : Nat}

/-- **The tables' column claims**, from `b10`: the function returns the walk's rest. -/
theorem callClaims (hp : Placed code k)
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
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyExecution.b10Offset)) {rate : Nat} (h15 : (reg st.data .r15).toNat = rate)
    (h12 : reg st.data .r12 = off (reg m0 .r8) 112184)
    (h13 : reg st.data .r13 = off (reg m0 .r8) 123992)
    (hbp : reg st.data .rbp = off (reg m0 .r8) 3912)
    (h40 : NativeRustcVm.WordAt st.data.dmem (off (stackBelow m0 96) 40)
      (UInt64.ofBitVec (reg m0 .rcx)))
    {P : Vector UInt64 4} (hP : NativeRustcVm.WordsAt m0.dmem (reg m0 .rcx) P.toList)
    {s : TState} (hts : TStateAt st.data.dmem (reg m0 .rdi) a s) (hroots : s.roots.size ≤ 2)
    {L : LayoutW} (hL : LayoutWAt st.data.dmem (reg m0 .r8) L)
    (hvc : (L.placement memory0).variableCount ≤ 31)
    {ev : Array (Array EW × Array EW)} (hev : TableEvalsAt st.data.dmem (off (reg m0 .r8) 112184) ev)
    (hsh : ev.size = 6 ∧ ∀ t < 6, (ev.getD t (#[], #[])).2.size = NativeVm.Math.Tables.widths.getD t 0 ∧
      (ev.getD t (#[], #[])).1.size = L.tableLogHeights.getD t 0)
    {cs : Array ColumnClaimW} (hcl : ClaimsWAt st.data.dmem (off (reg m0 .r8) 123992) cs)
    (hcs : cs.size = 4)
    {ood : StackClaimW} (hood : OodAt st.data.dmem (off (reg m0 .r8) 3912) ood) :
    Eventually (step1 Host.exe)
      (Done a m0 ((walkPublic P L rate ood (cs ++ tableColumnClaims ev) ev).run s)) st := by
  have hR := g.R
  have h8 := g.e8
  have hF := g.F
  have hwN := g.wN
  have hN : tableColumnClaimsStack = 120 := rfl
  have hsz := NativeRustcVm.Top.tableColumnClaims_size hsh.1 fun t ht ↦ (hsh.2 t ht).1
  have hfits : cs.size + (tableColumnClaims ev).size ≤ claimCap := by
    rw [hcs, hsz]; decide
  obtain ⟨hwf, hm⟩ := h.env g (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyExecution.b10Offset + b10.length)).toBitVec)
  refine exec_at (infix_of b10_in_code (by simp [b10]) hp) run_b10 hwf (fun _ _ ↦ rfl) hpc hm
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hmid, hw1, hrdi, hrsi, hk⟩ := after_eq run_b10 ▸ ok_b10
  have hC : AtCall m0 st1.data := h.toCall g hwf hm1 hmid (by decide) hw1
  have hs1 : NativeRustcVm.SameOutside st.data.dmem st1.data.dmem
      (NativeRustcVm.InRange (stackBelow m0 96) 40) :=
    sameOutside_low hwf hm1 (r := 0) rfl (by decide) hw1
  have hs1' : ∀ q, NativeRustcVm.InRange (stackBelow m0 96) 40 q →
      vsb m0 + 17792 ≤ q.toNat ∧ q.toNat < vsb m0 + 17832 := fun q hq ↦ by
    rw [inR (by unfold NativeRustcVm.NoWrap; omega), hF] at hq
    omega
  have kr : ∀ r ∈ [Reg64.rbx, .r12, .r13, .r14, .r15, .rbp], reg st1.data r = reg st.data r :=
    fun r hr ↦ hm1.regs r (.reg r) (by simpa using List.all_eq_true.mp hk r hr)
  have eRdi : reg st1.data .rdi = off (reg m0 .r8) 112184 := (hm1.regs .rdi _ hrdi).trans h12
  have eRsi : reg st1.data .rsi = off (reg m0 .r8) 123992 := (hm1.regs .rsi _ hrsi).trans h13
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
  have hev1 := NativeRustcVm.Top.TableEvalsAt.of_same hev (hsW (n := 11808) (by omega) (by omega))
  have hcl1 := NativeRustcVm.Tables.ClaimsWAt.of_same hcl (hsW (n := 97288) (by omega) (by omega))
  have hc : (32 : Nat) ≤ 96 := by decide
  have hN' : 120 ≤ 17792 + 32 := by decide
  have hpre : TableColumnClaimsPre ev cs st1.data := by
    unfold TableColumnClaimsPre
    simp only [eRdi, eRsi]
    rw [hN]
    refine ⟨hC.stackOk g hc hN', ⟨hC.readable g (o := 112184) (n := 11808) (by omega) (by omega),
      hC.offStack g hc (o := 112184) (n := 11808) (by omega) (by omega) hN', ?_⟩, hev1,
      hC.readable g (o := 123992) (n := 97288) (by omega) (by omega),
      hC.offStack g hc (o := 123992) (n := 97288) (by omega) (by omega) hN', hcl1⟩
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
    exact g.apartW (o := 112184) (n := 11808) (o' := 123992) (n' := 97288) (by omega) (by omega)
      (by omega)
  refine call_then hpc1 (htc ev cs) hpre fun st2 hpc2 hrsp2 hpost ↦ ?_
  obtain ⟨hok, hres, hch, hsv⟩ := hpost
  unfold Changes at hch
  simp only [eRsi, hN, show NativeRustcVm.Layout.claimsBytes = 97288 from rfl] at hres hch
  have hR2 : ∀ q, (NativeRustcVm.InRange (off (reg m0 .r8) 123992) 97288 q ∨
      NativeRustcVm.InRange (stackBelow st1.data 120) 120 q) →
      (vsb m0 ≤ q.toNat ∧ q.toNat < vsb m0 + 17824) ∨
      ((reg m0 .r8).toNat + 123992 ≤ q.toNat ∧ q.toNat < (reg m0 .r8).toNat + 221280) := by
    rintro q (hq | hq)
    · have := g.inW (o := 123992) (n := 97288) (by omega) (by omega) hq; omega
    · have := hC.inS g hc hN' hq; left; omega
  have h2 : At m0 st2.data := hC.ret g ((kr .rbx (by simp)).trans h.rbx)
    ((kr .r14 (by simp)).trans h.r14) hsv hrsp2 hch fun q hq ↦ by
      rcases hR2 q hq with hq | hq
      · exact Or.inl hq
      · exact Or.inr (Or.inr ⟨by omega, by omega⟩)
  have hsA := NativeRustcVm.Transcript.SameOutside.trans hs1 hch
  have hRA : ∀ q, (NativeRustcVm.InRange (stackBelow m0 96) 40 q ∨
      (NativeRustcVm.InRange (off (reg m0 .r8) 123992) 97288 q ∨
        NativeRustcVm.InRange (stackBelow st1.data 120) 120 q)) →
      (vsb m0 ≤ q.toNat ∧ q.toNat < vsb m0 + 17832) ∨
      ((reg m0 .r8).toNat + 123992 ≤ q.toNat ∧ q.toNat < (reg m0 .r8).toNat + 221280) := by
    rintro q (hq | hq)
    · have := hs1' q hq; left; omega
    · rcases hR2 q hq with h' | h'
      · left; omega
      · exact Or.inr h'
  have hsC : ∀ {o n : Nat}, o < 495552 → o + n ≤ 495552 → (o + n ≤ 123992 ∨ 221280 ≤ o) →
      NativeRustcVm.Layout.Same st.data.dmem st2.data.dmem (off (reg m0 .r8) o) n :=
    fun ho hn hlh ↦ g.same hsA ho hn fun q hq ↦ by
      have := g.wS
      rcases hRA q hq with h' | h' <;> omega
  have hts2 : TStateAt st2.data.dmem (reg m0 .rdi) a s :=
    hts1.frame (fun p hp ↦ hsv.2 p hp) (fun q hq ↦ by
      have := g.aS
      have := g.tS
      have := g.tw
      have := g.aw
      have hq' := hR2 q hq
      refine ⟨fun hi ↦ ?_, fun hi ↦ ?_⟩
      · have := (inR g.tN).mp hi; omega
      · have := (inR g.aN).mp hi; omega) hch
  have h40' : NativeRustcVm.WordAt st2.data.dmem (off (stackBelow m0 96) 40)
      (UInt64.ofBitVec (reg m0 .rcx)) :=
    keep40 g hsA (fun q hq ↦ by
      rcases hRA q hq with h' | h'
      · left; omega
      · right; right; right; omega) h40
  -- `b11`: the test
  refine branch hp g b11_in_code (by simp [b11]) (by rw [after_eq run_b11]; exact run_b11)
    (ok_test b11 (by simp)) h2 (hpc2.trans (by rw [show k + NativeRustcVmX64.Vm.VerifyExecution.b10Offset + b10.length = k + NativeRustcVmX64.Vm.VerifyExecution.b11Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyExecution.b10_next]]))
    hok (fun hb ↦ absurd hb (by simp [hfits])) fun st3 _ h3 hd3 hk3 hpc3 ↦ ?_
  have k12 : reg st3.data .r12 = reg st1.data .r12 := (hk3 .r12 (by simp)).trans (hsv.1 .r12 rfl)
  have k13 : reg st3.data .r13 = reg st1.data .r13 := (hk3 .r13 (by simp)).trans (hsv.1 .r13 rfl)
  have k15 : reg st3.data .r15 = reg st1.data .r15 := (hk3 .r15 (by simp)).trans (hsv.1 .r15 rfl)
  have kbp : reg st3.data .rbp = reg st1.data .rbp := (hk3 .rbp (by simp)).trans (hsv.1 .rbp rfl)
  have hL3 : LayoutWAt st3.data.dmem (off (reg m0 .r8) 0) L := by
    rw [hd3]
    exact NativeRustcVm.Tables.LayoutWAt.of_same (by rw [off_zero]; exact hL)
      (hsC (o := 0) (n := 3912) (by omega) (by omega) (by omega))
  rw [off_zero] at hL3
  have hev3 : TableEvalsAt st3.data.dmem (off (reg m0 .r8) 112184) ev := by
    rw [hd3]
    exact NativeRustcVm.Top.TableEvalsAt.of_same hev (hsC (n := 11808) (by omega) (by omega) (by omega))
  have hood3 : OodAt st3.data.dmem (off (reg m0 .r8) 3912) ood := by
    rw [hd3]
    exact NativeRustcVm.Top.OodAt.of_same hood (hsC (n := 504) (by omega) (by omega) (by omega))
  have hk5 := hsh.2 5 (by omega)
  exact callPublic hp hpi hkp hrs hvso g h3
    (hpc3.trans (by rw [show k + NativeRustcVmX64.Vm.VerifyExecution.b11Offset + b11.length = k + NativeRustcVmX64.Vm.VerifyExecution.b12Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyExecution.b11_next]])) (rate := rate)
    (by rw [k15, kr _ (by simp)]; exact h15) (by rw [k12, kr _ (by simp)]; exact h12)
    (by rw [k13, kr _ (by simp)]; exact h13) (by rw [kbp, kr _ (by simp)]; exact hbp)
    (by rw [hd3]; exact h40') hP (by rw [hd3]; exact hts2) hroots hL3 hvc hev3 hk5.2
    (by show keccakOut ≤ (ev.getD 5 (#[], #[])).2.size
        rw [hk5.1]; exact (Nat.le_add_right _ _).trans NativeRustcVm.Top.keccakOut_le)
    (by rw [hd3]; exact hres hfits) (by rw [Array.size_append, hcs, hsz]; decide) hood3

end

end NativeRustcVmX64.Top.VerifyExecution
