module

public import NativeRustcVmX64.Arrays.MultilinearEvalBy.Pair
public import NativeRustcVmX64.Code.Vm.EWMul.Names

/-!
# `multilinear_eval_by`: the loops, for both instances (x86-64)

`enter_step`: the inner loop's set-up (the next index stored, `full[0]`'s address, level `0`)
enters the inner loop with entry `i`. `inner_turn`: a turn of the inner loop (`test_step`, then
`push_step` or `pair_step`). `loops`: from the outer loop's head with nothing streamed, the
epilogue with the streamed value, from the instance's outer step (loading entry `i`) and the
turns.
-/

namespace NativeRustcVmX64.Arrays.MleFrame

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Field
open NativeRustcVm (wordOf ewOf ewsOf)
open NativeRustcVm.Mle (setP stream cont)

@[expose] public section

/-- The inner loop's set-up: `i + 1` stored at `16` (`i` in `rix`), `full[0]`'s address, `16·0`,
the value `ulo`, `uhi`, RSP kept. -/
abbrev EnterOk (R : Regs) (rix : Reg64) (ulo uhi : Sym) (S : SState) : Prop :=
  S.mem = [⟨0, 16, 8, .bin .add .W64 (.reg rix) (.lit 1)⟩] ∧ S.reg R.rf = some (.ptr 0 80) ∧
    S.reg R.ri = some (.lit 0) ∧ S.reg R.vlo = some ulo ∧ S.reg R.vhi = some uhi ∧
    S.reg .rsp = some (.ptr 0 8)

end

public section

theorem ofInt_80 : BitVec.ofInt 64 80 = BitVec.ofNat 64 (80 + 0) := by decide

variable [Host]

/-- **The inner loop's set-up**: entry `i` (`ulo`, `uhi`) at level `0`. -/
theorem enter_step (R : Regs) {es : List EW} {m0 : MachineData} (hS : StackOk m0 mleStack)
    {rix : Reg64} {ulo uhi : Sym} {ds : List Directive} {kB : Nat} {S : SState}
    (hk : ds.IsInfixAt Host.prog kB) (hx : exec ds (midS 1216) = some (S, .fall))
    (hc : EnterOk R rix ulo uhi S) {i : Nat} {s : MachineState} (hpc : s.pc = Host.addrOf kB)
    (hO : Outer es m0 i s.data) (hlen : i < es.length)
    (hix : reg s.data rix = BitVec.ofNat 64 i)
    (hv : ewArg (ulo.eval (frameEnv m0 s.data 1216)) (uhi.eval (frameEnv m0 s.data 1216)) = es[i]) :
    Eventually (step1 Host.exe)
      (fun s' ↦ s'.pc = Host.addrOf (kB + ds.length) ∧ Inner es R m0 i 0 s'.data) s := by
  obtain ⟨hmem, hrf, hri, hlo, hhi, hsp⟩ := hc
  have h1216 : 1216 ≤ mleStack := by decide
  have hwf := hO.fr.body.wf (vars := fun _ ↦ 0) (ret := 0) hS h1216
  refine exec_at hk hx hwf (by intro l h; cases h) hpc hO.fr.body.mid_match fun s2 hm2 hpc2 ↦ ?_
  have hw : ∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ 24 := by
    rw [hmem]; intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw; subst hw
    exact ⟨rfl, Nat.le_refl _⟩
  have hnw : ∀ j, 24 ≤ j → j < 1224 → s2.data.dmem.get? (fbOf m0 + BitVec.ofNat 64 j) =
      s.data.dmem.get? (fbOf m0 + BitVec.ofNat 64 j) := fun j h1 h2 ↦
    frame_keep hS hwf hm2 hw h1 h2
  have bd2 := body_of_local hO.fr.body hS hm2 hwf rfl
    (Match.reg_eq hO.fr.body.mid_match hm2 (show (midS 1216).reg .rsp = some (.ptr 0 8) from rfl)
      hsp)
    fun p hp ↦ by
      obtain ⟨w, hw', b, sz, hb, hlo', hhi'⟩ := written_bounds hp
      rw [hmem] at hw'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw'
      subst hw'
      simp only [Env.ofMachine_regions, List.getElem?_cons_zero, Option.some.injEq,
        Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      simp only at hlo' hhi'
      have : (stackBelow m0 1216).toNat = (rspOf m0).toNat - 1216 := (fb_toNat hS).1
      have := fb_toNat hS
      exact frame_addr hS (lo := 16) (hi := 1168) (by omega) (by omega) (by omega)
  have hwi : ValsAt s2.data.dmem (fbOf m0) [(16, BitVec.ofNat 64 (i + 1))] := by
    have h := val_of_write hm2 (r := 0) (o := 16) rfl (by omega) fun j hj ↦ by
      rw [hmem]; exact findWrite_head hj
    rw [eval_add, eval_reg, eval_lit, Env.ofMachine_regs] at h
    rw [show s.data.regs.get64 rix = BitVec.ofNat 64 i from hix, ← BitVec.ofNat_add] at h
    exact h
  have hkP : (0 : Nat) < (pts m0).length := by
    simp only [pts, NativeRustcVm.length_ewsOf]; exact hO.pos
  refine .done _ ⟨hpc2, ⟨bd2, args_congr hO.fr.args fun j h1 h2 ↦ hnw j h1 (by omega),
    flagsOk_congr hO.fr.flags fun j h1 h2 ↦ hnw j (by omega) (by omega)⟩, hO.hi, hO.pos, hO.lt,
    hwi, ?_, ?_, ?_⟩
  · show s2.data.regs.get64 R.rf = _
    rw [hm2.regs R.rf _ hrf]
    show stackBelow m0 1216 + BitVec.ofInt 64 80 = _
    rw [ofInt_80]
  · show s2.data.regs.get64 R.ri = _
    rw [hm2.regs R.ri _ hri]
    rfl
  · have hP : pendOf s2.data.dmem (fbOf m0) = pendOf s.data.dmem (fbOf m0) :=
      pendOf_congr fun j h1 h2 ↦ hnw j (by omega) (by omega)
    rw [hP, ← hO.val, List.drop_eq_getElem_cons hlen, NativeRustcVm.Mle.stream_cons]
    show cont _ _ _ _ (ewArg (s2.data.regs.get64 R.vlo) (s2.data.regs.get64 R.vhi)) = _
    rw [hm2.regs R.vlo _ hlo, hm2.regs R.vhi _ hhi, hv]

/-- **A turn of the inner loop**: `full[k]`'s test, then the value waits (`push_step`) or pairs
(`pair_step`). -/
theorem inner_turn (R : Regs) (hR : R.Saved)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) {es : List EW} {m0 : MachineData}
    (hS : StackOk m0 mleStack) (h02 : reg m0 .rdi = reg m0 .rdx) (hes : es.length = nn m0)
    (hP : SliceOk m0 (reg m0 .rcx) (reg m0 .r8) mleStack)
    {t p a c1 c2 d e e' : List Directive} {kI kP kO k1 kE kE' kEnd : Nat}
    {St Sp Sa Sc1 Sc2 Sd Se Se' : SState} {lP lO lI lE : Label}
    -- the test
    (hkt : t.IsInfixAt Host.prog kI)
    (hxt : exec t (flagS R.rf) = some (St, .cond (.cmp .eq .W8 (.load 0 0 1) (.lit 0)) lP))
    (hct : TestOk R St) (hlP : Labels.label lP = Host.addrOf kP)
    -- the push
    (hkp : p.IsInfixAt Host.prog kP)
    (hxp : exec p (pushS R.rf R.ri) =
      some (Sp, .cond (.not (.cmp .eq .W64 (.load 0 16 8) (.load 0 32 8))) lO))
    (hcp : PushOk R Sp) (hlO : Labels.label lO = Host.addrOf kO)
    (hke' : e'.IsInfixAt Host.prog kE') (hde' : kP + p.length = kE')
    (hxe' : exec e' regsS = some (Se', .jump lE)) (hce' : JumpOk R Se')
    -- the pairing
    (hk1 : kI + t.length = k1)
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
    (hke : e.IsInfixAt Host.prog kE) (hdE : k1 + a.length + c1.length + c2.length + d.length = kE)
    (hxe : exec e regsS = some (Se, .jump lE)) (hce : JumpOk R Se)
    (hlE : Labels.label lE = Host.addrOf kEnd)
    {i kk : Nat} {s : MachineState} (hpc : s.pc = Host.addrOf kI) (hI : Inner es R m0 i kk s.data) :
    Eventually (step1 Host.exe) (fun s' ↦ (s'.pc = Host.addrOf kEnd ∧ AtEnd es R m0 s'.data) ∨
      (s'.pc = Host.addrOf kO ∧ Outer es m0 (i + 1) s'.data) ∨
      (s'.pc = Host.addrOf kI ∧ Inner es R m0 i (kk + 1) s'.data)) s := by
  subst hk1 hdE
  refine test_step R hS hkt hxt hct hlP hpc hI (fun s' hpc' hI' hn ↦ ?_) fun s' hpc' hI' hs ↦ ?_
  · refine Eventually.mono (push_step R hS h02 hes hkp hxp hcp hlO hke' hde' hxe' hce' hlE hpc' hI'
      hn) fun _ h ↦ ?_
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · refine Eventually.mono (pair_step R hR hmul hS hP hka hxa hca hkc1 hxc1 hcc1 hkc2 hxc2 hcc2 hkd
      hxd hcd hlI hke hxe hce hlE hpc' hI' hs) fun _ h ↦ ?_
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)

/-- **The loops**: from the outer loop's head with nothing streamed, the epilogue with the
streamed value. -/
theorem loops (R : Regs) {es : List EW} {m0 : MachineData} {kO kI kEnd : Nat}
    (outer : ∀ i (s : MachineState), s.pc = Host.addrOf kO → Outer es m0 i s.data →
      Eventually (step1 Host.exe) (fun s' ↦ s'.pc = Host.addrOf kI ∧ Inner es R m0 i 0 s'.data) s)
    (turn : ∀ i kk (s : MachineState), s.pc = Host.addrOf kI → Inner es R m0 i kk s.data →
      Eventually (step1 Host.exe) (fun s' ↦ (s'.pc = Host.addrOf kEnd ∧ AtEnd es R m0 s'.data) ∨
        (s'.pc = Host.addrOf kO ∧ Outer es m0 (i + 1) s'.data) ∨
        (s'.pc = Host.addrOf kI ∧ Inner es R m0 i (kk + 1) s'.data)) s)
    {s : MachineState} (hpc : s.pc = Host.addrOf kO) (hO : Outer es m0 0 s.data) :
    Eventually (step1 Host.exe) (fun s' ↦ s'.pc = Host.addrOf kEnd ∧ AtEnd es R m0 s'.data) s := by
  refine Sym.loop (fun n s ↦ s.pc = Host.addrOf kO ∧ ∃ i, nn m0 - i = n ∧ Outer es m0 i s.data)
    (fun n s ⟨hpc, i, hn, hO⟩ ↦ ?_) ⟨hpc, 0, rfl, hO⟩
  refine Eventually.bind (outer i s hpc hO) fun s1 ⟨hpc1, hI⟩ ↦ ?_
  refine Eventually.mono (innerLoop R (Q := fun s' ↦ (s'.pc = Host.addrOf kEnd ∧
      AtEnd es R m0 s'.data) ∨ (s'.pc = Host.addrOf kO ∧ Outer es m0 (i + 1) s'.data))
    (fun kk s hpc hI ↦ Eventually.mono (turn i kk s hpc hI) fun s' h ↦ by
      rcases h with h | h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr h) hpc1 hI) fun s' h ↦ ?_
  rcases h with h | ⟨hpc', hO'⟩
  · exact Or.inl h
  · exact Or.inr ⟨nn m0 - (i + 1), by have := hO.hi; omega, hpc', i + 1, rfl, hO'⟩

end

end NativeRustcVmX64.Arrays.MleFrame
