module

public import NativeRustcVmX64.Top.VerifyExecution.Flow
public import NativeRustcVmX64.Code.Vm.VerifyStackedOpening.Names

/-!
# `verify_execution`: the stacked opening (x86-64)

`b18` pushes `verify_stacked_opening`'s three argument words (the out-of-domain claim, the scales'
buffer, the `WhirW`, all in the working area) and calls it on the layout, the rate, the ring
switch's output, the Keccak output (its address read back from the frame) and the column claims;
its result is the walk's, which `b19` and the epilogue return (`callVso`).
-/

namespace NativeRustcVmX64.Top.VerifyExecution

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.VerifyExecution NativeRustcVmX64.Transcript
open NativeRustcVmX64.Top NativeRustcVm.Transcript NativeVm.Model
open NativeRustcVm.Top (workAreaBytes)
open NativeRustcVm.Layout (LayoutWAt ClaimsWAt OodAt EqClaimAt)
open NativeRustcVm.Ring (RingWAt)
open NativeRustcVm.KeccakGkr (KeccakOutAt)

public section

variable [Host] {k : Nat}

/-- **The stacked opening**, from `b18`: the function returns its result. -/
theorem callVso (hp : Placed code k)
    (hvso : ∀ a s layout target coefficients point slices cs z value,
      Spec (Labels.label NativeRustcVmX64.Vm.VerifyStackedOpening.entryLabel)
        (VerifyStackedOpeningPre a s layout target coefficients point slices cs z value)
        (VerifyStackedOpeningPost a s layout target coefficients point cs z value))
    {a : DecArea} {m0 : MachineData} (g : Geo a m0) {st : MachineState} (h : At m0 st.data)
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyExecution.b18Offset)) {rate : Nat} (h15 : (reg st.data .r15).toNat = rate)
    (h12 : reg st.data .r12 = off (reg m0 .r8) 222888)
    (h13 : reg st.data .r13 = off (reg m0 .r8) 123992)
    (hbp : reg st.data .rbp = off (reg m0 .r8) 3912)
    (h40 : NativeRustcVm.WordAt st.data.dmem (off (stackBelow m0 96) 40)
      (UInt64.ofBitVec (off (reg m0 .r8) 221280)))
    {s : TState} (hts : TStateAt st.data.dmem (reg m0 .rdi) a s) (hroots : s.roots.size ≤ 2)
    {L : LayoutW} (hL : LayoutWAt st.data.dmem (reg m0 .r8) L) {target : EW} {coeffs : Array EW}
    (hring : RingWAt st.data.dmem (off (reg m0 .r8) 222888) target coeffs) {kp ks : Array EW}
    (hko : KeccakOutAt st.data.dmem (off (reg m0 .r8) 221280) kp ks) {cs : Array ColumnClaimW}
    (hcl : ClaimsWAt st.data.dmem (off (reg m0 .r8) 123992) cs) {ood : StackClaimW}
    (hood : OodAt st.data.dmem (off (reg m0 .r8) 3912) ood) :
    Eventually (step1 Host.exe) (Done a m0 ((verifyStackedOpening L.stackLog rate
      (#[ringSwitchClaim L target kp coeffs] ++ cs.filterMap (·.onStack L) ++ #[ood])).run s)) st := by
  have hR := g.R
  have h8 := g.e8
  have hF := g.F
  have hwN := g.wN
  have hwS := g.wS
  have htw := g.tw
  have htS := g.tS
  have hN : verifyStackedOpeningStack = 11936 := rfl
  obtain ⟨hwf, hm⟩ := h.env g (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyExecution.b18Offset + b18.length)).toBitVec)
  refine exec_at (infix_of b18_in_code (by simp [b18]) hp) run_b18 hwf (fun _ _ ↦ rfl) hpc hm
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hmid, hw1, hw8, hw16, hw24, hrdi, hrsi, hrdx, hrcx, hr8, hr9, hk⟩ :=
    after_eq run_b18 ▸ ok_b18
  have hf1 : Frame m0 96 slots 0 st1.data := Frame.of_block h.frame hwf hm1 hmid slots_le
  have hs1 : NativeRustcVm.SameOutside st.data.dmem st1.data.dmem
      (NativeRustcVm.InRange (stackBelow m0 96) 32) :=
    sameOutside_low hwf hm1 (r := 0) rfl (by decide) hw1
  have hs1' : ∀ q, NativeRustcVm.InRange (stackBelow m0 96) 32 q →
      vsb m0 + 17792 ≤ q.toNat ∧ q.toNat < vsb m0 + 17824 := fun q hq ↦ by
    rw [inR (by unfold NativeRustcVm.NoWrap; omega), hF] at hq
    omega
  have hC : AtCall m0 st1.data 0 := ⟨hf1, fun q hq ↦ by
    rw [hs1 q fun h' ↦ hq (wr_s g (by have := hs1' q h'; omega))]
    exact h.same q hq⟩
  have hsp1 : rspOf st1.data = stackBelow m0 96 := hC.sp g (by decide)
  -- the registers and the argument words
  have kr : ∀ r ∈ [Reg64.rbx, .r12, .r13, .r14, .r15, .rbp], reg st1.data r = reg st.data r :=
    fun r hr ↦ hm1.regs r (.reg r) (by simpa using List.all_eq_true.mp hk r hr)
  have eRdi : reg st1.data .rdi = reg m0 .rdi := (hm1.regs .rdi _ hrdi).trans h.r14
  have eRsi : reg st1.data .rsi = off (reg m0 .r8) 0 := by rw [off_zero]; exact (hm1.regs .rsi _ hrsi).trans h.rbx
  have eRdx : (reg st1.data .rdx).toNat = rate := by
    rw [show reg st1.data .rdx = _ from hm1.regs .rdx _ hrdx]; exact h15
  have eRcx : reg st1.data .rcx = off (reg m0 .r8) 222888 := (hm1.regs .rcx _ hrcx).trans h12
  have eR8 : reg st1.data .r8 = off (reg m0 .r8) 221280 := by
    rw [show reg st1.data .r8 = _ from hm1.regs .r8 _ hr8]
    exact load_ofMachine (r := 0) (b := stackBelow m0 96) (n := 104) rfl h40
  have eR9 : reg st1.data .r9 = off (reg m0 .r8) 123992 := (hm1.regs .r9 _ hr9).trans h13
  have warg : ∀ (o : Nat) (v : Sym) (x : BitVec 64), o + 8 ≤ 32 →
      (∀ j < 8, findWrite 0 (o + j) (after b18 bodyS).mem = some (v, j)) →
      v.eval (frameEnv m0 st.data 96 [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyExecution.b18Offset + b18.length)).toBitVec) = x →
      NativeRustcVm.WordAt st1.data.dmem (off (stackBelow m0 96) o) (UInt64.ofBitVec x) :=
    fun o v x ho hv hx ↦ by
      have := wordAt_write (r := 0) (b := stackBelow m0 96) (sz := 104) hm1 rfl (by omega) hv
      rwa [hx] at this
  have sarg : ∀ (i : Nat) (x : BitVec 64), i < 3 →
      NativeRustcVm.WordAt st1.data.dmem (off (stackBelow m0 96) (8 + 8 * i)) (UInt64.ofBitVec x) →
      NativeRustcVmX64.stackArg st1.data i = x := fun i x _ hx ↦ by
    unfold NativeRustcVmX64.stackArg
    rw [hsp1, NativeRustcVm.wordOf_of_wordAt hx]
  have ea0 : NativeRustcVmX64.stackArg st1.data 0 = off (reg m0 .r8) 3912 :=
    sarg 0 _ (by decide) (warg 8 (.reg .rbp) _ (by decide) (after_eq run_b18 ▸ hw8) hbp)
  have ea1 : NativeRustcVmX64.stackArg st1.data 1 = off (reg m0 .r8) 223928 :=
    sarg 1 _ (by decide) (warg 16 _ _ (by decide) (after_eq run_b18 ▸ hw16) (by
      simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
      rw [show st.data.regs.get64 .rbx = reg m0 .r8 from h.rbx]))
  have ea2 : NativeRustcVmX64.stackArg st1.data 2 = off (reg m0 .r8) 226528 :=
    sarg 2 _ (by decide) (warg 24 _ _ (by decide) (after_eq run_b18 ▸ hw24) (by
      simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
      rw [show st.data.regs.get64 .rbx = reg m0 .r8 from h.rbx]))
  -- the memory the store keeps
  have hsW : ∀ {o n : Nat}, o < 495552 → o + n ≤ 495552 →
      NativeRustcVm.Layout.Same st.data.dmem st1.data.dmem (off (reg m0 .r8) o) n := fun ho hn ↦
    g.same hs1 ho hn fun q hq ↦ by have := hs1' q hq; omega
  have hts1 : TStateAt st1.data.dmem (reg m0 .rdi) a s :=
    hts.frame (fun p hp ↦ hm1.kept hwf p hp) (fun q hq ↦ by
      have := hs1' q hq
      have := g.aS
      refine ⟨fun hi ↦ ?_, fun hi ↦ ?_⟩
      · have := (inR g.tN).mp hi; omega
      · have := (inR g.aN).mp hi; omega) hs1
  have hL1 : LayoutWAt st1.data.dmem (off (reg m0 .r8) 0) L :=
    NativeRustcVm.Tables.LayoutWAt.of_same (by rw [off_zero]; exact hL)
      (hsW (o := 0) (n := 3912) (by omega) (by omega))
  have hring1 := NativeRustcVm.Top.RingWAt.of_same hring (hsW (by omega) (by decide))
  have hko1 := NativeRustcVm.Top.KeccakOutAt.of_same hko (hsW (by omega) (by decide))
  have hcl1 := NativeRustcVm.Tables.ClaimsWAt.of_same hcl (hsW (by omega) (by decide))
  obtain ⟨z, hz, hood1⟩ := NativeRustcVm.Top.OodAt.of_same hood (hsW (by omega) (by decide))
  -- the precondition
  have hc : (0 : Nat) ≤ 96 := by decide
  have hN' : 11936 ≤ 17792 + 0 := by decide
  have hsb := hC.sb g hc hN'
  have hin : ∀ {o n : Nat}, o < 495552 → o + n ≤ 223928 →
      WhirIn st1.data (off (reg m0 .r8) o) n verifyStackedOpeningStack ∧
      NativeRustcVm.Apart (off (reg m0 .r8) o) n (reg m0 .rdi) tstateBytes ∧
      NativeRustcVm.Apart (off (reg m0 .r8) o) n (off (reg m0 .r8) 226528) 63200 ∧
      NativeRustcVm.Apart (off (reg m0 .r8) o) n (off (reg m0 .r8) 223928) 2600 :=
    fun {o n} ho hn ↦ ⟨⟨hC.readable g ho (by omega), by rw [hN]; exact hC.offStack g hc ho (by omega) hN'⟩,
      g.apartWT ho (by omega), g.apartW ho (by omega) (by left; omega),
      g.apartW ho (by omega) (by left; omega)⟩
  have ap : ∀ {o n o' n' : Nat}, o < 495552 → o' < 495552 → o + n ≤ o' ∨ o' + n' ≤ o →
      NativeRustcVm.Apart (off (reg m0 .r8) o) n (off (reg m0 .r8) o') n' := fun ho ho' hle ↦ g.apartW ho ho' hle
  have hA8 : ∀ {o n : Nat}, o < 495552 → o + n ≤ 495552 →
      NativeRustcVm.Apart (rspOf st1.data + 8#64) 24 (off (reg m0 .r8) o) n := fun {o n} ho hn ↦ by
    rw [hsp1]
    unfold NativeRustcVm.Apart
    rw [show stackBelow m0 96 + 8#64 = off (stackBelow m0 96) 8 from rfl,
      toNat_off (by omega), hF, g.wo ho]
    omega
  have hpre : VerifyStackedOpeningPre a s L target coeffs kp ks cs z ood.value st1.data := by
    unfold VerifyStackedOpeningPre vsoInputs NativeRustcVm.Whir.BasisAddrs.regions WhirT
    simp only [eRdi, eRsi, eRcx, eR8, eR9, ea0, ea1, ea2, List.tail_cons, List.mem_cons,
      List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq, List.pairwise_cons,
      List.Pairwise.nil, and_true, show NativeRustcVm.Whir.whirBytes = 63200 from rfl,
      show NativeRustcVm.Whir.scalesBytes = 2600 from rfl,
      show NativeRustcVm.Layout.layoutBytes = 3912 from rfl,
      show NativeRustcVm.Ring.ringWBytes = 1040 from rfl,
      show NativeRustcVm.KeccakGkr.outBytes = 1608 from rfl,
      show NativeRustcVm.Layout.claimsBytes = 97288 from rfl,
      show NativeRustcVm.Layout.eqClaimBytes = 504 from rfl]
    rw [hN]
    refine ⟨⟨hC.stackOk g hc hN', hC.rcAt g hc hN', hC.rodataAt g hc hN', hC.tstateOk g hc hN',
      g.rt⟩, ⟨by rw [hsp1]; exact mapped_off (Mapped.keeps g.fmapped hf1.kept) (by decide),
        by rw [hsp1, hF]; omega⟩, hts1, hroots, hL1, hring1, hko1, hcl1, hood1, ?_,
      hA8 (o := 223928) (n := 2600) (by omega) (by omega),
      hA8 (o := 226528) (n := 63200) (by omega) (by omega),
      ⟨hC.outOk g hc (o := 226528) (n := 63200) (by omega) (by omega) hN',
        g.wRod (by omega) (by omega)⟩,
      ⟨hC.outOk g hc (o := 223928) (n := 2600) (by omega) (by omega) hN',
        g.wRod (by omega) (by omega)⟩,
      ap (o := 226528) (n := 63200) (o' := 223928) (n' := 2600) (by omega) (by omega) (by omega),
      ⟨hin (o := 0) (n := 3912) (by omega) (by omega), hin (o := 222888) (n := 1040) (by omega) (by omega),
        hin (o := 221280) (n := 1608) (by omega) (by omega),
        hin (o := 123992) (n := 97288) (by omega) (by omega),
        hin (o := 3912) (n := 504) (by omega) (by omega)⟩,
      ⟨⟨ap (o := 0) (n := 3912) (o' := 222888) (n' := 1040) (by omega) (by omega) (by omega),
        ap (o := 0) (n := 3912) (o' := 221280) (n' := 1608) (by omega) (by omega) (by omega),
        ap (o := 0) (n := 3912) (o' := 123992) (n' := 97288) (by omega) (by omega) (by omega),
        ap (o := 0) (n := 3912) (o' := 3912) (n' := 504) (by omega) (by omega) (by omega)⟩,
      ⟨ap (o := 222888) (n := 1040) (o' := 221280) (n' := 1608) (by omega) (by omega) (by omega),
        ap (o := 222888) (n := 1040) (o' := 123992) (n' := 97288) (by omega) (by omega) (by omega),
        ap (o := 222888) (n := 1040) (o' := 3912) (n' := 504) (by omega) (by omega) (by omega)⟩,
      ⟨ap (o := 221280) (n := 1608) (o' := 123992) (n' := 97288) (by omega) (by omega) (by omega),
        ap (o := 221280) (n := 1608) (o' := 3912) (n' := 504) (by omega) (by omega) (by omega)⟩,
      ap (o := 123992) (n := 97288) (o' := 3912) (n' := 504) (by omega) (by omega) (by omega),
      (fun _ h ↦ h.elim)⟩, ?_⟩
    · rw [hsp1]
      show _ ∨ _
      unfold tstateBytes
      rw [show stackBelow m0 96 + 8#64 = off (stackBelow m0 96) 8 from rfl, toNat_off (by omega), hF]
      omega
    · apply hC.got g hc hN'
      intro l hl
      simp only [List.append_assoc]
      intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact g.gotT hl
        · exact g.gotA hl
        · exact g.gotW hl (by omega) (by dsimp only; decide)
        · exact g.gotW hl (by omega) (by dsimp only; decide)
      · rcases List.mem_append.mp hr with hr | hr
        · simp only [List.map_cons, List.map_nil, List.mem_cons, List.mem_nil_iff, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl <;>
            exact g.gotW hl (by omega) (by dsimp only; decide)
        · exact g.gotRodata hl r hr
  refine call_then hpc1 (hvso a s L target coeffs kp ks cs z ood.value) hpre
    fun st2 hpc2 hrsp2 hpost ↦ ?_
  obtain ⟨hok, hnext, hch, hsv⟩ := hpost
  have hcl' : NativeRustcVm.Whir.stackClaims L target kp coeffs cs z ood.value =
      #[ringSwitchClaim L target kp coeffs] ++ cs.filterMap (·.onStack L) ++ #[ood] := by
    obtain ⟨w', v⟩ := ood
    cases hz
    rfl
  simp only [eRdi, eRdx, ea1, ea2, hcl', show NativeRustcVm.Whir.whirBytes = 63200 from rfl,
    show NativeRustcVm.Whir.scalesBytes = 2600 from rfl] at hok hnext hch
  -- the changes
  have hR2 : ∀ q, (NativeRustcVm.InAny [⟨off (reg m0 .r8) 226528, 63200⟩,
      ⟨off (reg m0 .r8) 223928, 2600⟩, ⟨reg m0 .rdi, tstateBytes⟩] q ∨
      NativeRustcVm.InRange (stackBelow st1.data verifyStackedOpeningStack)
        verifyStackedOpeningStack q) →
      (vsb m0 ≤ q.toNat ∧ q.toNat < vsb m0 + 17792) ∨
      ((reg m0 .rdi).toNat ≤ q.toNat ∧ q.toNat < (reg m0 .rdi).toNat + 760) ∨
      ((reg m0 .r8).toNat ≤ q.toNat ∧ q.toNat < (reg m0 .r8).toNat + 495552) := by
    rintro q (hq | hq)
    · rcases inAny3 hq with hq | hq | hq
      · have := g.inW (o := 226528) (n := 63200) (by omega) (by omega) hq; omega
      · have := g.inW (o := 223928) (n := 2600) (by omega) (by omega) hq; omega
      · exact Or.inr (Or.inl (g.inT hq))
    · rw [hN] at hq
      have := hC.inS g hc hN' hq
      left; omega
  have hf2 : Frame m0 96 slots 8 st2.data := by
    refine Frame.call_low hf1 hsv hrsp2 hch (L := 8) (fun q hq ↦ ?_)
      (fun p hp ↦ by have := slots_ge p hp; omega) (by decide) g.fnw slots_le
    rw [hF]
    rcases hR2 q hq with hq | hq | hq <;> omega
  -- `b19`, `b21`.
  have hwf2 := frame_wf (m0 := m0) (d := st2.data) (F := 96) (rest := []) (vars := fun _ ↦ 0)
    (ret := 0) ⟨Mapped.keeps g.fmapped hf2.kept, g.fnw⟩ (by simp) (List.pairwise_singleton _ _)
  refine exec_at (infix_of b19_in_code (by simp [b19]) hp) run_b19 hwf2 nofun
    (hpc2.trans (by rw [show k + NativeRustcVmX64.Vm.VerifyExecution.b18Offset + b18.length = k + NativeRustcVmX64.Vm.VerifyExecution.b19Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyExecution.b18_next]]))
    (match_ofMachine ⟨rfl, trivial⟩ ⟨hf2.rsp_eval, trivial⟩ trivial trivial trivial)
    fun st3 hm3 hpc3 ↦ ?_
  obtain ⟨hmid3, hmem3, hrax3⟩ := after_eq run_b19 ▸ ok_b19
  have hf3 : Frame m0 96 slots 48 st3.data := Frame.of_block hf2 hwf2 hm3 hmid3 slots_le
  have hd3 : st3.data.dmem = st2.data.dmem := hm3.dmem_eq hwf2 hmem3
  simp only [PcOk] at hpc3
  refine Eventually.mono (exit21 hp g (hpc3.trans (lbl_11 hp)) hf3)
    fun s' ⟨h1, h2, h3, h4, h5⟩ ↦ ⟨h1, h2, ?_, ?_, fun q hq ↦ ?_, h5⟩
  · unfold OkAl boolRet at hok ⊢
    rw [h3, show reg st3.data .rax = _ from hm3.regs .rax _ hrax3]
    exact hok
  · rw [h4, hd3]; exact hnext
  · rw [h4, hd3, hch q fun h' ↦ hq (by
      rcases hR2 q h' with h' | h' | h'
      · exact wr_s g ⟨h'.1, by omega⟩
      · exact wr_t ((inR g.tN).mpr h')
      · exact wr_w g h')]
    exact hC.same q hq

end

end NativeRustcVmX64.Top.VerifyExecution
