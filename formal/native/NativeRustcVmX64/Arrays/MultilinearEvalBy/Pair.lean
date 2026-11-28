module

public import NativeRustcVmX64.Arrays.MultilinearEvalBy.Steps
public import NativeRustcVmX64.Code.Vm.EWMul.Names

/-!
# `multilinear_eval_by`: an entry pairs, for both instances (x86-64)

`pair_step`: at level `k` an entry `a` waits. The loads (`a`, from `pairS`) clear `full[k]`
(`pendOf_clear`) and load `pending[k]` and `point[k]`; `EW::mul` gives `a·(1 + r)` (stored at
`fb + 64`) and `v·r`; their sum (`b13`, from `midS`) is carried to level `k + 1`: back at the inner
loop's head, or, at level `|point|`, the result (a jump to the epilogue).
-/

namespace NativeRustcVmX64.Arrays.MleFrame

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Field
open NativeRustcVm (wordOf ewOf ewsOf)
open NativeRustcVm.Mle (setP stream cont)

@[expose] public section

/-- The pairing's loads: `full[k]` cleared, `pending[k]` in RDI, RSI, `1 + point[k]` in RDX, RCX,
`point[k]` in `plo`, `phi`, RSP and the loop's registers kept. -/
abbrev PairOk (R : Regs) (S : SState) : Prop :=
  S.mem = [⟨1, 0, 1, .lit 0⟩] ∧ S.reg .rdi = some (.load 2 0 8) ∧
    S.reg .rsi = some (.load 2 8 8) ∧ S.reg .rdx = some (.bin .xor .W64 (.load 3 0 8) (.lit 1)) ∧
    S.reg .rcx = some (.load 3 8 8) ∧ S.reg R.plo = some (.load 3 0 8) ∧
    S.reg R.phi = some (.load 3 8 8) ∧
    keepsRegs (pairS R.rf R.ri) S [.rsp, R.rf, R.ri, R.vlo, R.vhi] = true

/-- The first call: the arguments and the loop's registers kept, the return address pushed. -/
abbrev Call1Ok (R : Regs) (S : SState) : Prop :=
  keepsRegs (midS 1216) S [.rdi, .rsi, .rdx, .rcx, R.rf, R.ri, R.vlo, R.vhi, R.plo, R.phi] = true ∧
    S.reg .rsp = some (.ptr 0 0) ∧ ∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ 8

/-- The second call: the product stored at `64`, `v` and `point[k]` the arguments. -/
abbrev Call2Ok (R : Regs) (S : SState) : Prop :=
  S.reg .rdi = some (.reg R.vlo) ∧ S.reg .rsi = some (.reg R.vhi) ∧
    S.reg .rdx = some (.reg R.plo) ∧ S.reg .rcx = some (.reg R.phi) ∧
    keepsRegs (midS 1216) S [R.rf, R.ri] = true ∧ S.reg .rsp = some (.ptr 0 0) ∧
    (∀ w ∈ S.mem, w.r = 0 ∧ (w.off + w.n ≤ 8 ∨ (64 ≤ w.off ∧ w.off + w.n ≤ 80))) ∧
    (∀ i < 8, findWrite 0 (64 + i) S.mem = some (.reg .rax, i)) ∧
    (∀ i < 8, findWrite 0 (72 + i) S.mem = some (.reg .rdx, i))

/-- The sum, the next level. -/
abbrev SumOk (R : Regs) (S : SState) : Prop :=
  S.mem = [] ∧ S.reg .rsp = some (.ptr 0 8) ∧
    S.reg R.vlo = some (.bin .xor .W64 (.reg .rax) (.load 0 64 8)) ∧
    S.reg R.vhi = some (.bin .xor .W64 (.reg .rdx) (.load 0 72 8)) ∧
    S.reg R.ri = some (.bin .add .W64 (.lit 16) (.reg R.ri)) ∧
    S.reg R.rf = some (.bin .add .W64 (.reg R.rf) (.lit 1))

end

public section

/-- **Frame bytes a block keeps**: those at `L` or above, where it writes only below `L`. -/
theorem frame_keep [Labels] {m0 st st' : MachineData} {vars : Nat → BitVec 64} {ret : BitVec 64}
    {S : SState} (hS : StackOk m0 mleStack) (hwf : (frameEnv m0 st 1216 vars ret).WF)
    (hm : Match (frameEnv m0 st 1216 vars ret) S st') {L : Nat}
    (hw : ∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ L) {j : Nat} (hj : L ≤ j) (hj' : j < 1224) :
    st'.dmem.get? (fbOf m0 + BitVec.ofNat 64 j) = st.dmem.get? (fbOf m0 + BitVec.ofNat 64 j) :=
  hm.get?_mem0 hwf fun h ↦ by
    have h1 := written_region0 rfl hwf (show L ≤ 1216 + 8 by omega) hw h
    have ef : (stackBelow m0 1216).toNat = (rspOf m0).toNat - 1216 ∧ 1360 ≤ (rspOf m0).toNat ∧
      (rspOf m0).toNat + 8 ≤ 2 ^ 64 := fb_toNat hS
    have e2 : (stackBelow m0 1216 + BitVec.ofNat 64 j).toNat = (stackBelow m0 1216).toNat + j :=
      fb_add_toNat hS hj'
    rw [Sym.inRange_iff (by omega), e2] at h1
    omega

variable [Host]

/-- **An entry waits at level `kk`**: paired with `v`, carried to level `kk + 1`. -/
theorem pair_step (R : Regs) (hR : R.Saved)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) {es : List EW} {m0 : MachineData}
    (hS : StackOk m0 mleStack) (hP : SliceOk m0 (reg m0 .rcx) (reg m0 .r8) mleStack)
    {a c1 c2 d e : List Directive} {k1 kI kEnd : Nat} {Sa Sc1 Sc2 Sd Se : SState}
    {lI lE : Label}
    (hka : a.IsInfixAt Host.prog k1) (hxa : exec a (pairS R.rf R.ri) = some (Sa, .fall))
    (hca : PairOk R Sa)
    (hkc1 : c1.IsInfixAt Host.prog (k1 + a.length))
    (hxc1 : exec c1 (midS 1216) = some (Sc1, .call NativeRustcVmX64.Vm.EWMul.entryLabel)) (hcc1 : Call1Ok R Sc1)
    (hkc2 : c2.IsInfixAt Host.prog (k1 + a.length + c1.length))
    (hxc2 : exec c2 (midS 1216) = some (Sc2, .call NativeRustcVmX64.Vm.EWMul.entryLabel)) (hcc2 : Call2Ok R Sc2)
    (hkd : d.IsInfixAt Host.prog (k1 + a.length + c1.length + c2.length))
    (hxd : exec d (midS 1216) = some (Sd,
      .cond (.not (.cmp .eq .W64 (.load 0 48 8) (.bin .add .W64 (.lit 16) (.reg R.ri)))) lI))
    (hcd : SumOk R Sd) (hlI : Labels.label lI = Host.addrOf kI)
    (hke : e.IsInfixAt Host.prog (k1 + a.length + c1.length + c2.length + d.length))
    (hxe : exec e regsS = some (Se, .jump lE)) (hce : JumpOk R Se)
    (hlE : Labels.label lE = Host.addrOf kEnd)
    {i kk : Nat} {s : MachineState} (hpc : s.pc = Host.addrOf k1) (hI : Inner es R m0 i kk s.data)
    (hsome : pendOf s.data.dmem (fbOf m0) kk =
      some (ewOf s.data.dmem (fbOf m0 + BitVec.ofNat 64 (144 + 16 * kk)))) :
    Eventually (step1 Host.exe) (fun s' ↦ (s'.pc = Host.addrOf kEnd ∧ AtEnd es R m0 s'.data) ∨
      (s'.pc = Host.addrOf kI ∧ Inner es R m0 i (kk + 1) s'.data)) s := by
  obtain ⟨hrf, hri, hvlo, hvhi, hplo, hphi⟩ := hR
  have hk64 : kk < 64 := by have := hI.hk; have := hI.lt; omega
  have hkm : kk < (reg m0 .r8).toNat := hI.hk
  have ef := fb_toNat hS
  have h1360 : 1216 + ewMulStack ≤ mleStack := by decide
  have h1216 : 1216 ≤ mleStack := by decide
  have hfb0 : (stackBelow m0 1216).toNat = (rspOf m0).toNat - 1216 := (fb_toNat hS).1
  have hmm : mm m0 = (reg m0 .r8).toNat := rfl
  have hsl8 : ∀ p ∈ mleSlots, 8 ≤ p.1 ∧ p.1 + 8 ≤ 1216 := fun p hp ↦
    ⟨by have := (mleSlots_ok p hp).1; omega, (mleSlots_ok p hp).2⟩
  have hsl80 : ∀ p ∈ mleSlots, 80 ≤ p.1 ∧ p.1 + 8 ≤ 1216 := fun p hp ↦
    ⟨by have := (mleSlots_ok p hp).1; omega, (mleSlots_ok p hp).2⟩
  have hfree : keepsRegs (midS 1216) Sc1 (freeRegs mleSlots) = true := by
    rw [freeRegs_mleSlots]; rfl
  have hfree2 : keepsRegs (midS 1216) Sc2 (freeRegs mleSlots) = true := by
    rw [freeRegs_mleSlots]; rfl
  obtain ⟨hmem, hrdi, hrsi, hrdx, hrcx, hrplo, hrphi, hka'⟩ := hca
  -- the loads
  have h0 := frame_piece hS hI.fr.body.kept (o := 0) (n := 80) (by omega)
  rw [add_ofNat_zero] at h0
  have h1 := frame_piece hS hI.fr.body.kept (o := 80 + kk) (n := 1) (by omega)
  have h2 := frame_piece hS hI.fr.body.kept (o := 144 + 16 * kk) (n := 16) (by omega)
  have h3 := elem_mapped hP.1 hI.fr.body.kept hkm
  have a01 := frame_apart hS (o := 0) (n := 80) (o' := 80 + kk) (n' := 1) (by omega) (by omega)
    (by omega)
  have a02 := frame_apart hS (o := 0) (n := 80) (o' := 144 + 16 * kk) (n' := 16) (by omega)
    (by omega) (by omega)
  have a12 := frame_apart hS (o := 80 + kk) (n := 1) (o' := 144 + 16 * kk) (n' := 16) (by omega)
    (by omega) (by omega)
  rw [add_ofNat_zero] at a01 a02
  have a03 := piece_offStack hS hP.2 hP.1.2 (j := 16 * kk) (w := 16) (o := 0) (n := 80)
    (by omega) (by omega) (by omega) (by omega)
  have a13 := piece_offStack hS hP.2 hP.1.2 (j := 16 * kk) (w := 16) (o := 80 + kk) (n := 1)
    (by omega) (by omega) (by omega) (by omega)
  have a23 := piece_offStack hS hP.2 hP.1.2 (j := 16 * kk) (w := 16) (o := 144 + 16 * kk)
    (n := 16) (by omega) (by omega) (by omega) (by omega)
  rw [add_ofNat_zero] at a03
  have hwf := wf4 (st := s.data) h0 h1 h2 h3 a01 a02 (apart_symm a03) a12 (apart_symm a13)
    (apart_symm a23)
  have hm : Match (Env.ofMachine s.data [(fbOf m0, 80), (fbOf m0 + BitVec.ofNat 64 (80 + kk), 1),
      (fbOf m0 + BitVec.ofNat 64 (144 + 16 * kk), 16),
      (reg m0 .rcx + BitVec.ofNat 64 (16 * kk), 16)]) (pairS R.rf R.ri) s.data :=
    match_ofMachine ⟨rfl, rfl, rfl, rfl, trivial⟩ ⟨hI.fr.body.rsp,
      hI.rf.trans (eval_ptr0 rfl).symm, trivial⟩ trivial trivial ⟨by
        dsimp only
        rw [eval_add]
        show fbOf m0 + BitVec.ofInt 64 8 + reg s.data R.ri = _
        rw [hI.ri]
        exact pend_alias _ _, by
        dsimp only
        rw [eval_add, eval_load,
          val_load (env := Env.ofMachine s.data [(fbOf m0, 80),
            (fbOf m0 + BitVec.ofNat 64 (80 + kk), 1), (fbOf m0 + BitVec.ofNat 64 (144 + 16 * kk), 16),
            (reg m0 .rcx + BitVec.ofNat 64 (16 * kk), 16)]) (r := 0) hI.fr.args (o := 56)
            (v := reg m0 .rcx) (by simp [argVals])]
        show reg m0 .rcx + reg s.data R.ri = _
        rw [hI.ri, ofInt_0, BitVec.add_zero]
        rfl, trivial⟩
  refine exec_at hka hxa hwf (by intro l h; cases h) hpc hm fun s2 hm2 hpc2 ↦ ?_
  have hpc2' : s2.pc = Host.addrOf (k1 + a.length) := hpc2
  have hnw2 : ∀ j, j < 1224 → j ≠ 80 + kk →
      s2.data.dmem.get? (fbOf m0 + BitVec.ofNat 64 j) =
        s.data.dmem.get? (fbOf m0 + BitVec.ofNat 64 j) := by
    intro j hj h1'
    refine hm2.get?_mem0 hwf fun hw ↦ ?_
    obtain ⟨w, hw', b, sz, hb, hlo, hhi⟩ := written_bounds hw
    rw [hmem] at hw'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw'
    subst hw'
    simp only [Env.ofMachine_regions, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    simp only at hlo hhi
    have e1 := fb_add_toNat hS (o := 80 + kk) (by omega)
    have e2 := fb_add_toNat hS (o := j) hj
    omega
  have hflag : s2.data.dmem.get? (fbOf m0 + BitVec.ofNat 64 (80 + kk)) = some 0 := by
    have := hm2.mem 1 (fbOf m0 + BitVec.ofNat 64 (80 + kk)) 1 rfl 0 (by decide)
    rw [add_ofNat_zero] at this
    rw [this, hmem]
    simp [memByte, findWrite, Sym.eval, byteOf]
  have bd2 : Body m0 1216 mleStack mleSlots 0 0 s2.data :=
    body_of_local hI.fr.body hS hm2 hwf rfl (regs_eq_of hm hm2 hka' .rsp (by simp)) fun p hp ↦ by
      obtain ⟨w, hw', b, sz, hb, hlo, hhi⟩ := written_bounds hp
      rw [hmem] at hw'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw'
      subst hw'
      simp only [Env.ofMachine_regions, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      simp only at hlo hhi
      have e1 := fb_add_toNat hS (o := 80 + kk) (by omega)
      exact frame_addr hS (lo := 16) (hi := 1168) (by omega) (by omega) (by omega)
  have hP2 : pendOf s2.data.dmem (fbOf m0) = setP (pendOf s.data.dmem (fbOf m0)) kk none :=
    pendOf_clear hk64 hflag fun j _ hj h1' ↦ hnw2 j (by omega) h1'
  have he2 := regs_eq_of hm hm2 hka'
  -- the loaded values
  have hA : ewArg (reg s2.data .rdi) (reg s2.data .rsi) =
      ewOf s.data.dmem (fbOf m0 + BitVec.ofNat 64 (144 + 16 * kk)) := by
    have h := ew_of_loads (off := 0) (lo := .rdi) (hi := .rsi) hm2 hrdi hrsi
    rw [add_ofNat_zero] at h
    exact h
  have hpt : ewOf s.data.dmem (reg m0 .rcx + BitVec.ofNat 64 (16 * kk)) =
      (pts m0)[kk]'(by simp [pts]; exact hkm) :=
    elem_of_apart hI.fr.body.same hS hP.1.2 hP.2 (apart_zero _ _) noWrap_zero hkm
  have hRr : ewArg (reg s2.data R.plo) (reg s2.data R.phi) = (pts m0)[kk]'(by simp [pts]; exact hkm) := by
    have h := ew_of_loads (off := 0) (lo := R.plo) (hi := R.phi) hm2 hrplo hrphi
    rw [add_ofNat_zero] at h
    exact h.trans hpt
  have hR1 : ewArg (reg s2.data .rdx) (reg s2.data .rcx) =
      1 + (pts m0)[kk]'(by simp [pts]; exact hkm) := by
    rw [← hRr]
    show ewArg (s2.data.regs.get64 .rdx) (s2.data.regs.get64 .rcx) =
      1 + ewArg (s2.data.regs.get64 R.plo) (s2.data.regs.get64 R.phi)
    rw [hm2.regs .rdx _ hrdx, hm2.regs .rcx _ hrcx, hm2.regs R.plo _ hrplo, hm2.regs R.phi _ hrphi,
      eval_xor, eval_lit]
    exact one_add_ewArg _ _
  -- the first call
  have hwf3 := bd2.wf (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k1 + a.length + c1.length)).toBitVec) hS h1216
  refine exec_at hkc1 hxc1 hwf3 (fun _ _ ↦ rfl) hpc2' bd2.mid_match fun s3 hm3 hpc3 ↦ ?_
  obtain ⟨hk3, hsp3, hw3⟩ := hcc1
  have he3 := regs_eq_of bd2.mid_match hm3 hk3
  refine Body.call_mul (rs := []) (L := 8) hmul bd2 hS h1360 (by omega) hsl8 hwf3 bd2.mid_match
    hm3 hpc3 hfree hsp3 hw3 fun s4 hpc4 bd4 hprod4 hsv4 _ hfr4 ↦ ?_
  have hprod4' : ewRet s4.data = ewOf s.data.dmem (fbOf m0 + BitVec.ofNat 64 (144 + 16 * kk)) *
      (1 + (pts m0)[kk]'(by simp [pts]; exact hkm)) := by
    rw [hprod4, he3 .rdi (by simp), he3 .rsi (by simp), he3 .rdx (by simp), he3 .rcx (by simp),
      hA, hR1]
    rfl
  have k4 : ∀ r, calleeSaved r = true → r ∈ [R.rf, R.ri, R.vlo, R.vhi, R.plo, R.phi] →
      reg s4.data r = reg s2.data r := fun r hc hr ↦
    (hsv4 r hc).trans (he3 r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)))))
  have hf4 : ∀ j, 8 ≤ j → j < 1224 → s4.data.dmem.get? (fbOf m0 + BitVec.ofNat 64 j) =
      s2.data.dmem.get? (fbOf m0 + BitVec.ofNat 64 j) := fun j h1' h2' ↦
    (hfr4 j (by omega)).trans (frame_keep hS hwf3 hm3 hw3 h1' h2')
  -- the second call
  have hwf5 := bd4.wf (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k1 + a.length + c1.length + c2.length)).toBitVec) hS h1216
  refine exec_at hkc2 hxc2 hwf5 (fun _ _ ↦ rfl) hpc4 bd4.mid_match fun s5 hm5 hpc5 ↦ ?_
  obtain ⟨h5di, h5si, h5dx, h5cx, hk5, hsp5, hw5, hw64, hw72⟩ := hcc2
  have hw5' : ∀ w ∈ Sc2.mem, w.r = 0 ∧ w.off + w.n ≤ 80 := fun w hw ↦
    ⟨(hw5 w hw).1, by rcases (hw5 w hw).2 with h | h <;> omega⟩
  have hv64 : ValsAt s5.data.dmem (fbOf m0) [(64, reg s4.data .rax)] :=
    val_of_write hm5 (r := 0) rfl (by omega) hw64
  have hv72 : ValsAt s5.data.dmem (fbOf m0) [(72, reg s4.data .rdx)] :=
    val_of_write hm5 (r := 0) rfl (by omega) hw72
  have he5 := regs_eq_of bd4.mid_match hm5 hk5
  have hf5 : ∀ j, 8 ≤ j → j < 1224 → (j < 64 ∨ 80 ≤ j) →
      s5.data.dmem.get? (fbOf m0 + BitVec.ofNat 64 j) =
        s4.data.dmem.get? (fbOf m0 + BitVec.ofNat 64 j) := fun j h1' h2' h3' ↦
    hm5.get?_mem0 hwf5 fun h ↦ by
      obtain ⟨w, hw', b, sz, hb, hlo, hhi⟩ := written_bounds h
      obtain ⟨hr0, hw''⟩ := hw5 w hw'
      rw [hr0] at hb
      simp only [Env.ofMachine_regions, List.getElem?_cons_zero, Option.some.injEq,
        Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      have e2 := fb_add_toNat hS (o := j) h2'
      omega
  refine Body.call_mul (rs := []) (L := 80) hmul bd4 hS h1360 (by omega) hsl80 hwf5 bd4.mid_match
    hm5 hpc5 hfree2 hsp5 hw5' fun s6 hpc6 bd6 hprod6 hsv6 _ hfr6 ↦ ?_
  have hprod6' : ewRet s6.data = ewArg (reg s.data R.vlo) (reg s.data R.vhi) *
      (pts m0)[kk]'(by simp [pts]; exact hkm) := by
    have e1 : reg s5.data .rdi = reg s4.data R.vlo := hm5.regs .rdi _ h5di
    have e2 : reg s5.data .rsi = reg s4.data R.vhi := hm5.regs .rsi _ h5si
    have e3 : reg s5.data .rdx = reg s4.data R.plo := hm5.regs .rdx _ h5dx
    have e4 : reg s5.data .rcx = reg s4.data R.phi := hm5.regs .rcx _ h5cx
    rw [hprod6, e1, e2, e3, e4, k4 R.vlo hvlo (by simp), k4 R.vhi hvhi (by simp),
      k4 R.plo hplo (by simp), k4 R.phi hphi (by simp), hRr, he2 R.vlo (by simp),
      he2 R.vhi (by simp)]
    rfl
  have hf6 : ∀ j, 8 ≤ j → j < 1224 → (j < 64 ∨ 80 ≤ j) →
      s6.data.dmem.get? (fbOf m0 + BitVec.ofNat 64 j) =
        s2.data.dmem.get? (fbOf m0 + BitVec.ofNat 64 j) := fun j h1' h2' h3' ↦
    (hfr6 j (by omega)).trans ((hf5 j h1' h2' h3').trans (hf4 j h1' h2'))
  have hv6 : ValsAt s6.data.dmem (fbOf m0) [(64, reg s4.data .rax), (72, reg s4.data .rdx)] := by
    rw [vals_cons]
    refine ⟨?_, vals_congr hv72 fun p hp j hj ↦ hfr6 _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; subst hp; dsimp only; omega)⟩
    have := vals_congr hv64 fun p hp j hj ↦ hfr6 _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; subst hp; dsimp only; omega)
    rw [vals_cons] at this
    exact this.1
  have hri6 : reg s6.data R.ri = BitVec.ofNat 64 (16 * kk) := by
    rw [hsv6 R.ri hri, he5 R.ri (by simp), k4 R.ri hri (by simp), he2 R.ri (by simp)]
    exact hI.ri
  have hrf6 : reg s6.data R.rf = fbOf m0 + BitVec.ofNat 64 (80 + kk) := by
    rw [hsv6 R.rf hrf, he5 R.rf (by simp), k4 R.rf hrf (by simp), he2 R.rf (by simp)]
    exact hI.rf
  -- the sum, the next level
  have hwf7 := bd6.wf (vars := fun _ ↦ 0) (ret := 0) hS h1216
  refine exec_at hkd hxd hwf7 (by intro l h; cases h) hpc6 bd6.mid_match fun s7 hm7 hpc7 ↦ ?_
  obtain ⟨hmem7, hsp7, h7lo, h7hi, h7ri, h7rf⟩ := hcd
  have hd7 : s7.data.dmem = s6.data.dmem := hm7.dmem_eq hwf7 hmem7
  have bd7 := body_of_local bd6 hS hm7 hwf7 rfl
    (Match.reg_eq bd6.mid_match hm7 (show (midS 1216).reg .rsp = some (.ptr 0 8) from rfl) hsp7)
    (fun p hp ↦ absurd hp (not_written_nil hmem7 p))
  have hE7 : ∀ j, 8 ≤ j → j < 1224 → (j < 64 ∨ 80 ≤ j) →
      s7.data.dmem.get? (fbOf m0 + BitVec.ofNat 64 j) =
        s.data.dmem.get? (fbOf m0 + BitVec.ofNat 64 j) ∨ j = 80 + kk := fun j h1' h2' h3' ↦ by
    by_cases hj : j = 80 + kk
    · exact .inr hj
    · exact .inl (by rw [hd7, hf6 j h1' h2' h3', hnw2 j h2' hj])
  have hargs7 : ValsAt s7.data.dmem (fbOf m0) (argVals m0) :=
    args_congr hI.fr.args fun j h1' h2' ↦ (hE7 j (by omega) (by omega) (by omega)).resolve_right
      (by omega)
  have hP7 : pendOf s7.data.dmem (fbOf m0) = setP (pendOf s.data.dmem (fbOf m0)) kk none := by
    rw [← hP2]
    exact pendOf_congr fun j h1' h2' ↦ by rw [hd7, hf6 j (by omega) (by omega) (by omega)]
  have hv7 : ewArg (reg s7.data R.vlo) (reg s7.data R.vhi) =
      ewOf s.data.dmem (fbOf m0 + BitVec.ofNat 64 (144 + 16 * kk)) *
          (1 + (pts m0)[kk]'(by simp [pts]; exact hkm)) +
        ewArg (reg s.data R.vlo) (reg s.data R.vhi) * (pts m0)[kk]'(by simp [pts]; exact hkm) := by
    show ewArg (s7.data.regs.get64 R.vlo) (s7.data.regs.get64 R.vhi) = _
    rw [hm7.regs R.vlo _ h7lo, hm7.regs R.vhi _ h7hi, eval_xor, eval_xor, eval_reg, eval_reg,
      eval_load, eval_load,
      val_load (env := frameEnv m0 s6.data 1216) (r := 0) hv6 (o := 64) (v := reg s4.data .rax)
        (by simp),
      val_load (env := frameEnv m0 s6.data 1216) (r := 0) hv6 (o := 72) (v := reg s4.data .rdx)
        (by simp), Env.ofMachine_regs,
      Env.ofMachine_regs, ewArg_xor]
    show ewRet s6.data + ewRet s4.data = _
    rw [hprod6', hprod4', ew_add_comm]
  have hkP : kk < (pts m0).length := by simp only [pts, NativeRustcVm.length_ewsOf]; exact hkm
  have hval7 : cont (pts m0) (es.drop (i + 1)) (pendOf s7.data.dmem (fbOf m0)) (kk + 1)
      (ewArg (reg s7.data R.vlo) (reg s7.data R.vhi)) = stream (pts m0) es fun _ ↦ none := by
    rw [hP7, hv7, ← hI.val, NativeRustcVm.Mle.cont_some _ _ hkP hsome]
  -- the test `kk + 1 = |point|`
  simp only [PcOk] at hpc7
  have hargs6 : ValsAt s6.data.dmem (fbOf m0) (argVals m0) := by rw [← hd7]; exact hargs7
  rw [eval_not, eval_cmp_eq, eval_load, eval_add, eval_lit, eval_reg, Env.ofMachine_regs,
    val_load (env := frameEnv m0 s6.data 1216) (r := 0) hargs6 (o := 48)
      (v := BitVec.ofNat 64 (16 * mm m0)) (by simp [argVals]),
    show s6.data.regs.get64 R.ri = BitVec.ofNat 64 (16 * kk) from hri6, ofNat_16_add,
    ofNat_beq (by have := hI.lt; omega) (by omega)] at hpc7
  obtain ⟨hT, hF⟩ := pc_cond hpc7
  by_cases hlast : 16 * mm m0 = 16 * (kk + 1)
  · refine Eventually.mono (jump_end R hS hke hxe hce hlE (hF (by simp [hlast])) ⟨bd7, ?_⟩)
      fun _ h ↦ Or.inl h
    have hlen : (pts m0).length ≤ kk + 1 := by
      rw [NativeRustcVm.length_ewsOf]; omega
    rw [NativeRustcVm.Mle.cont_top _ hlen] at hval7
    exact hval7
  · refine .done _ (Or.inr ⟨(hT (by simp [hlast])).trans hlI, ⟨bd7, hargs7, ?_⟩, hI.hi,
      by have := hI.hk; omega, hI.lt, ?_, ?_, ?_, hval7⟩)
    · refine flagsOk_clear hI.fr.flags ?_ fun j h1' h2' h3' ↦
        (hE7 j (by omega) (by omega) (by omega)).resolve_right h3'
      rw [hd7, hf6 _ (by omega) (by omega) (by omega)]
      exact hflag
    · exact wi_congr hI.wi fun j h1' h2' ↦ (hE7 j (by omega) (by omega) (by omega)).resolve_right
        (by omega)
    · show s7.data.regs.get64 R.rf = _
      rw [hm7.regs R.rf _ h7rf, eval_add, eval_reg, eval_lit, Env.ofMachine_regs,
        show s6.data.regs.get64 R.rf = _ from hrf6, addr_add, Nat.add_assoc]
    · show s7.data.regs.get64 R.ri = _
      rw [hm7.regs R.ri _ h7ri, eval_add, eval_reg, eval_lit, Env.ofMachine_regs,
        show s6.data.regs.get64 R.ri = _ from hri6, ofNat_16_add]

end

end NativeRustcVmX64.Arrays.MleFrame
