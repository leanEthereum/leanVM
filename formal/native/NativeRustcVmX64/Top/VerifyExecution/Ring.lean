module

public import NativeRustcVmX64.Top.VerifyExecution.Vso
public import NativeRustcVmX64.Code.Vm.RingSwitch.Names
public import NativeRustcVmX64.Code.Vm.VerifyStackedOpening.Names

/-!
# `verify_execution`: ring switching (x86-64)

`b16` calls `ring_switch` on the Keccak output's slices into the working area's bytes from
`222888`; `b17` returns `0` when it failed, else the stacked opening (`callRing`).
-/

namespace NativeRustcVmX64.Top.VerifyExecution

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.VerifyExecution NativeRustcVmX64.Transcript
open NativeRustcVmX64.Top NativeRustcVm.Transcript NativeVm.Model
open NativeRustcVm.Top (workAreaBytes walkRing run_bind_eq ringSwitch_point)
open NativeRustcVm.Layout (LayoutWAt ClaimsWAt OodAt EqClaimAt)
open NativeRustcVm.Ring (RingWAt)
open NativeRustcVm.KeccakGkr (KeccakOutAt)

public section

section
variable [Labels] {a : DecArea} {m0 : MachineData}

/-- A working-area address `rbx + c` a block computed. -/
theorem eval_addW {d : MachineData} {ret : BitVec 64} (hrbx : reg d .rbx = reg m0 .r8) (c : Nat) :
    (Sym.bin .add .W64 (.reg .rbx) (.lit c)).eval (frameEnv m0 d 96 [] (fun _ ↦ 0) ret) =
      off (reg m0 .r8) c := by
  simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
  rw [show d.regs.get64 .rbx = reg m0 .r8 from hrbx]

/-- A change below the callee's stack top or in the given working-area range: the bytes from `o`
of the working area outside it stay the same. -/
theorem Geo.sameCall (g : Geo a m0) {d d' : DataMem} {R : BitVec 64 → Prop}
    (hs : NativeRustcVm.SameOutside d d' R) {o n lo hi : Nat} (ho : o < 495552)
    (hn : o + n ≤ 495552) (hlh : o + n ≤ lo ∨ hi ≤ o)
    (hR : ∀ q, R q → (vsb m0 ≤ q.toNat ∧ q.toNat < vsb m0 + 17824) ∨
      ((reg m0 .rdi).toNat ≤ q.toNat ∧ q.toNat < (reg m0 .rdi).toNat + 760) ∨
      ((reg m0 .r8).toNat + lo ≤ q.toNat ∧ q.toNat < (reg m0 .r8).toNat + hi)) :
    NativeRustcVm.Layout.Same d d' (off (reg m0 .r8) o) n :=
  g.same hs ho hn fun q hq ↦ by
    have := g.wS
    have := g.tw
    rcases hR q hq with h | h | h <;> omega

end

variable [Host] {k : Nat}

/-- **Ring switching**, from `b16`: the function returns the walk's rest. -/
theorem callRing (hp : Placed code k)
    (hrs : ∀ a s point, Spec (Labels.label NativeRustcVmX64.Vm.RingSwitch.entryLabel) (RingSwitchPre a s)
      (RingSwitchPost a s point))
    (hvso : ∀ a s layout target coefficients point slices cs z value,
      Spec (Labels.label NativeRustcVmX64.Vm.VerifyStackedOpening.entryLabel)
        (VerifyStackedOpeningPre a s layout target coefficients point slices cs z value)
        (VerifyStackedOpeningPost a s layout target coefficients point cs z value))
    {a : DecArea} {m0 : MachineData} (g : Geo a m0) {st : MachineState} (h : At m0 st.data)
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyExecution.b16Offset)) {rate : Nat} (h15 : (reg st.data .r15).toNat = rate)
    (h13 : reg st.data .r13 = off (reg m0 .r8) 123992)
    (hbp : reg st.data .rbp = off (reg m0 .r8) 3912)
    (h40 : NativeRustcVm.WordAt st.data.dmem (off (stackBelow m0 96) 40)
      (UInt64.ofBitVec (off (reg m0 .r8) 221280)))
    {s : TState} (hts : TStateAt st.data.dmem (reg m0 .rdi) a s) (hroots : s.roots.size ≤ 2)
    {L : LayoutW} (hL : LayoutWAt st.data.dmem (reg m0 .r8) L) {kp ks : Array EW}
    (hko : KeccakOutAt st.data.dmem (off (reg m0 .r8) 221280) kp ks) {cs : Array ColumnClaimW}
    (hcl : ClaimsWAt st.data.dmem (off (reg m0 .r8) 123992) cs) {ood : StackClaimW}
    (hood : OodAt st.data.dmem (off (reg m0 .r8) 3912) ood) :
    Eventually (step1 Host.exe) (Done a m0 ((walkRing L rate ood cs kp ks).run s)) st := by
  have hR := g.R
  have h8 := g.e8
  have hF := g.F
  have hwN := g.wN
  have hN : ringSwitchStack = 3008 := rfl
  obtain ⟨hwf, hm⟩ := h.env g (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyExecution.b16Offset + b16.length)).toBitVec)
  refine exec_at (infix_of b16_in_code (by simp [b16]) hp) run_b16 hwf (fun _ _ ↦ rfl) hpc hm
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hmid, hw1, hrdi, hrsi, hrdx, hr12, hk⟩ := after_eq run_b16 ▸ ok_b16
  have hC : AtCall m0 st1.data := h.toCall g hwf hm1 hmid (by decide) hw1
  have kr : ∀ r ∈ [Reg64.rbx, .r13, .r14, .r15, .rbp], reg st1.data r = reg st.data r :=
    fun r hr ↦ hm1.regs r (.reg r) (by simpa using List.all_eq_true.mp hk r hr)
  have hs1 : NativeRustcVm.SameOutside st.data.dmem st1.data.dmem
      (NativeRustcVm.InRange (stackBelow m0 96) 40) :=
    sameOutside_low hwf hm1 (r := 0) rfl (by decide) hw1
  have hs1' : ∀ q, NativeRustcVm.InRange (stackBelow m0 96) 40 q →
      vsb m0 + 17792 ≤ q.toNat ∧ q.toNat < vsb m0 + 17832 := fun q hq ↦ by
    rw [inR (by unfold NativeRustcVm.NoWrap; omega), hF] at hq
    omega
  have eRdi : reg st1.data .rdi = reg m0 .rdi := (hm1.regs .rdi _ hrdi).trans h.r14
  have eRsi : reg st1.data .rsi = off (reg m0 .r8) 221864 :=
    (hm1.regs .rsi _ hrsi).trans (eval_addW h.rbx 221864)
  have eRdx : reg st1.data .rdx = off (reg m0 .r8) 222888 :=
    (hm1.regs .rdx _ hrdx).trans (eval_addW h.rbx 222888)
  have eR12 : reg st1.data .r12 = off (reg m0 .r8) 222888 :=
    (hm1.regs .r12 _ hr12).trans (eval_addW h.rbx 222888)
  -- the memory the block keeps
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
  have hko1 := NativeRustcVm.Top.KeccakOutAt.of_same hko (hsW (by omega) (by decide))
  obtain ⟨hkp, hks, hksE⟩ := hko1
  have hslE : NativeRustcVm.EWsAt st1.data.dmem (off (reg m0 .r8) 221864) ks.toList := by
    have e : off (off (reg m0 .r8) 221280) NativeRustcVm.KeccakGkr.slicesOff =
        off (reg m0 .r8) 221864 := off_off _ _ _
    rw [← e]; exact hksE
  have harr : arr st1.data (reg st1.data .rsi) NativeRustcVm.Ring.coeffCount = ks := by
    unfold arr
    rw [eRsi, show NativeRustcVm.Ring.coeffCount = ks.toList.length by simp [hks]; rfl,
      NativeRustcVm.ewsOf_of_ewsAt hslE]
  -- the precondition
  have hc : (32 : Nat) ≤ 96 := by decide
  have hN' : 3008 ≤ 17792 + 32 := by decide
  have hpre : RingSwitchPre a s st1.data := by
    unfold RingSwitchPre ArrOk
    simp only [eRdi, eRsi, eRdx, hN, show NativeRustcVm.Ring.ringWBytes = 1040 from rfl,
      show NativeRustcVm.Ring.coeffCount = 64 from rfl]
    refine ⟨hC.stackOk g hc hN', hC.rcAt g hc hN', hts1, hC.tstateOk g hc hN',
      hC.outOk g hc (o := 222888) (n := 1040) (by omega) (by omega) hN',
      ⟨hC.readable g (o := 221864) (n := 1024) (by omega) (by omega),
        hC.offStack g hc (o := 221864) (n := 1024) (by omega) (by omega) hN'⟩,
      g.apartWT (o := 221864) (n := 1024) (by omega) (by omega),
      g.apartW (o := 221864) (n := 1024) (o' := 222888) (n' := 1040) (by omega) (by omega)
        (by omega), ?_⟩
    apply GotAt.symbols (symbols := ["memcpy", "memset"]) (hs := by decide)
    apply hC.got g hc hN'
    intro l hl
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨g.gotT hl, g.gotA hl, g.gotW hl (by omega) (by decide),
      g.gotW hl (by omega) (by decide), g.gotRc hl⟩
  refine call_then hpc1 (hrs a s kp) hpre fun st2 hpc2 hrsp2 hpost ↦ ?_
  obtain ⟨hok, hres, hch, hsv⟩ := hpost
  rw [harr] at hok hres
  simp only [eRdi, eRdx, hN, show NativeRustcVm.Ring.ringWBytes = 1040 from rfl] at hres hch
  have hR2 : ∀ q, (NativeRustcVm.InRange (off (reg m0 .r8) 222888) 1040 q ∨
      NativeRustcVm.InRange (reg m0 .rdi) tstateBytes q ∨
      NativeRustcVm.InRange (stackBelow st1.data 3008) 3008 q) →
      (vsb m0 ≤ q.toNat ∧ q.toNat < vsb m0 + 17824) ∨
      ((reg m0 .rdi).toNat ≤ q.toNat ∧ q.toNat < (reg m0 .rdi).toNat + 760) ∨
      ((reg m0 .r8).toNat + 222888 ≤ q.toNat ∧ q.toNat < (reg m0 .r8).toNat + 223928) := by
    rintro q (hq | hq | hq)
    · have := g.inW (o := 222888) (n := 1040) (by omega) (by omega) hq; omega
    · exact Or.inr (Or.inl (g.inT hq))
    · have := hC.inS g hc hN' hq; left; omega
  have h2 : At m0 st2.data := hC.ret g ((kr .rbx (by simp)).trans h.rbx)
    ((kr .r14 (by simp)).trans h.r14) hsv hrsp2 hch fun q hq ↦ by
      rcases hR2 q hq with hq | hq | hq
      · exact Or.inl hq
      · exact Or.inr (Or.inl hq)
      · exact Or.inr (Or.inr ⟨by omega, by omega⟩)
  -- what the block and the call keep
  have hsA := NativeRustcVm.Transcript.SameOutside.trans hs1 hch
  have hRA : ∀ q, (NativeRustcVm.InRange (stackBelow m0 96) 40 q ∨
      (NativeRustcVm.InRange (off (reg m0 .r8) 222888) 1040 q ∨
        NativeRustcVm.InRange (reg m0 .rdi) tstateBytes q ∨
        NativeRustcVm.InRange (stackBelow st1.data 3008) 3008 q)) →
      (vsb m0 ≤ q.toNat ∧ q.toNat < vsb m0 + 17832) ∨
      ((reg m0 .rdi).toNat ≤ q.toNat ∧ q.toNat < (reg m0 .rdi).toNat + 760) ∨
      ((reg m0 .r8).toNat + 222888 ≤ q.toNat ∧ q.toNat < (reg m0 .r8).toNat + 223928) := by
    rintro q (hq | hq)
    · have := hs1' q hq; left; omega
    · rcases hR2 q hq with h' | h' | h'
      · left; omega
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr h')
  have hsC : ∀ {o n : Nat}, o < 495552 → o + n ≤ 495552 → (o + n ≤ 222888 ∨ 223928 ≤ o) →
      NativeRustcVm.Layout.Same st.data.dmem st2.data.dmem (off (reg m0 .r8) o) n :=
    fun ho hn hlh ↦ g.same hsA ho hn fun q hq ↦ by
      have := g.wS
      have := g.tw
      rcases hRA q hq with h' | h' | h' <;> omega
  have h40' : NativeRustcVm.WordAt st2.data.dmem (off (stackBelow m0 96) 40)
      (UInt64.ofBitVec (off (reg m0 .r8) 221280)) :=
    keep_off h40 hsA fun j h1 h2 hq ↦ by
      rw [NativeRustcVm.length_wordBytes] at h2
      have hq' : (off (stackBelow m0 96) j).toNat = vsb m0 + 17792 + j := by
        rw [toNat_off (by omega), hF]
      have := g.wS
      have := g.tS
      rcases hRA _ hq with h' | h' | h' <;> omega
  -- `b17`: the test
  rw [walkRing, run_bind_eq]
  generalize hr : (ringSwitch kp ks).run s = r at hok hres
  refine branch hp g b17_in_code (by simp [b17]) (by rw [after_eq run_b17]; exact run_b17)
    (ok_test b17 (by simp)) h2 (hpc2.trans (by rw [show k + NativeRustcVmX64.Vm.VerifyExecution.b16Offset + b16.length = k + NativeRustcVmX64.Vm.VerifyExecution.b17Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyExecution.b16_next]]))
    hok (fun hb ↦ by cases r with | none => rfl | some _ => cases hb)
    fun st3 hb h3 hd3 hk3 hpc3 ↦ ?_
  obtain ⟨⟨⟨target, rp, coeffs⟩, s'⟩, rfl⟩ := Option.isSome_iff_exists.mp hb
  obtain ⟨hring, hts'⟩ := hres _ _ rfl
  have hrp : rp = kp := (ringSwitch_point kp ks).gives _ _ _ hr
  have hroots' : s'.roots = s.roots := (NativeRustcVm.Top.ringSwitch_roots kp ks).keeps _ _ _ hr
  subst rp
  have k12 : reg st3.data .r12 = reg st1.data .r12 := (hk3 .r12 (by simp)).trans (hsv.1 .r12 rfl)
  have k13 : reg st3.data .r13 = reg st1.data .r13 := (hk3 .r13 (by simp)).trans (hsv.1 .r13 rfl)
  have k15 : reg st3.data .r15 = reg st1.data .r15 := (hk3 .r15 (by simp)).trans (hsv.1 .r15 rfl)
  have kbp : reg st3.data .rbp = reg st1.data .rbp := (hk3 .rbp (by simp)).trans (hsv.1 .rbp rfl)
  have hL3 : LayoutWAt st3.data.dmem (off (reg m0 .r8) 0) L := by
    rw [hd3]
    exact NativeRustcVm.Tables.LayoutWAt.of_same (by rw [off_zero]; exact hL)
      (hsC (o := 0) (n := 3912) (by omega) (by omega) (by omega))
  rw [off_zero] at hL3
  have hko3 : KeccakOutAt st3.data.dmem (off (reg m0 .r8) 221280) kp ks := by
    rw [hd3]; exact NativeRustcVm.Top.KeccakOutAt.of_same hko (hsC (n := 1608) (by omega) (by omega) (by omega))
  have hcl3 : ClaimsWAt st3.data.dmem (off (reg m0 .r8) 123992) cs := by
    rw [hd3]; exact NativeRustcVm.Tables.ClaimsWAt.of_same hcl (hsC (n := 97288) (by omega) (by omega) (by omega))
  have hood3 : OodAt st3.data.dmem (off (reg m0 .r8) 3912) ood := by
    rw [hd3]; exact NativeRustcVm.Top.OodAt.of_same hood (hsC (n := 504) (by omega) (by omega) (by omega))
  exact callVso hp hvso g h3 (hpc3.trans (by rw [show k + NativeRustcVmX64.Vm.VerifyExecution.b17Offset + b17.length = k + NativeRustcVmX64.Vm.VerifyExecution.b18Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyExecution.b17_next]]))
    (by rw [k15, kr _ (by simp)]; exact h15) (by rw [k12]; exact eR12)
    (by rw [k13, kr _ (by simp)]; exact h13) (by rw [kbp, kr _ (by simp)]; exact hbp)
    (by rw [hd3]; exact h40') (by rw [hd3]; exact hts') (by rw [hroots']; exact hroots) hL3
    (by rw [hd3]; exact hring) hko3 hcl3 hood3

end

end NativeRustcVmX64.Top.VerifyExecution
