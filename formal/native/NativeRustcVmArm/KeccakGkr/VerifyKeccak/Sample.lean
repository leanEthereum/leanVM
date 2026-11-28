module

public import NativeRustcVmArm.Code.Vm.TStateReadScalar.Names
public import NativeRustcVmArm.Code.Vm.TStateSampleChallenges.Names
public import NativeRustcVmArm.Code.Vm.VerifyKeccak.Names
public import NativeRustcVmArm.KeccakGkr.VerifyKeccak.Fin

/-!
# `verify_keccak`: the grind's branch, the challenges, the committed outputs' value

`b2`: on the grind's `None`, the epilogue with X0 `0`; `b3`, `b4`: the segment challenge into the
frame at 96, the five lane challenges at 112; `b5`: `read_scalar` into the frame's `Option<EW>` at
960; `b6`: on `None`, the failure exit.
-/

namespace NativeRustcVmArm.KeccakGkr.VerifyKeccak

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVmArm.Ring
open NativeRustcVm.Transcript NativeRustcVmArm.Vm.VerifyKeccak

public section

variable [Host] {k : Nat} {a : DecArea} {s : TState} {cs : Array ColumnClaimW}
  {inst output : Array EW} {m0 : MachineData}

/-- The block's writes are in the frame below the slots: as numbers. -/
theorem block_same (hn : Nums a inst m0) {m st : MachineData} {S : SState}
    (hm : Match (envM m0 m) S st) (hwf : (envM m0 m).WF)
    (hw : S.mem.all (fun w ↦ w.r == 0 && decide (w.off + w.n ≤ 3264)) = true) :
    SameOutside m.dmem st.dmem (fun q ↦
      m0.regs.SP.toNat - 3360 ≤ q.toNat ∧ q.toNat < m0.regs.SP.toNat - 3360 + 3264) :=
  written_nat hn hm hwf hw

/-- The `TState` and the claims past a block writing the frame. -/
theorem out_block (hn : Nums a inst m0) {m st : MachineData} {S : SState} {s' : TState}
    (hm : Match (envM m0 m) S st) (hwf : (envM m0 m).WF)
    (hw : S.mem.all (fun w ↦ w.r == 0 && decide (w.off + w.n ≤ 3264)) = true)
    (hts : TStateAt m.dmem (tA m0) a s')
    (hcl : NativeRustcVm.Layout.ClaimsWAt m.dmem (clA m0) cs) :
    TStateAt st.dmem (tA m0) a s' ∧ NativeRustcVm.Layout.ClaimsWAt st.dmem (clA m0) cs := by
  have hd := block_same hn hm hwf hw
  have := hn.tS; have := hn.wS; have := hn.cS; have := hn.hN
  exact ⟨ts_keep hn hts (hm.kept hwf) hd fun q hq ↦ ⟨by omega, by omega⟩,
    cls_keep hn hcl hd fun q hq ↦ by omega⟩

/-- **The grind's branch** (`b2`). -/
theorem stepGrind (hp : Placed code k) (hn : Nums a inst m0) {m : MachineData} (hmid : Mid m0 m)
    {b : Bool} (hx0 : m.regs.X0 = okWord b) (hfail : b = false → run0 s inst output m0 = none)
    (cont : b = true → ∀ m', Mid m0 m' → m'.dmem = m.dmem →
      (∀ r, calleeSaved r = true → m'.regs.getXReg r = m.regs.getXReg r) →
      Eventually (step1 Host.exe) (Goal a s cs inst output m0) ⟨m', Host.addrOf (k + NativeRustcVmArm.Vm.VerifyKeccak.b3Offset)⟩) :
    Eventually (step1 Host.exe) (Goal a s cs inst output m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyKeccak.b2Offset)⟩ := by
  refine blockStep hn (b2_in_code.trans hp.1 (by simp [b2])) run_b2 hmid.fr rfl rfl
    fun st hm1 hfr1 hd hpc ↦ ?_
  obtain ⟨d, pc⟩ := st
  simp only [PcOk] at hpc
  cases b
  · have hc : SBool.eval (envM m0 m) (.cmp .eq .W32 (.un .trunc .W32 (.reg .X0))
      (.lit 0)) = true := by
      sym_simp; simp only [Env.ofMachine_regs, gx0, hx0]; decide
    simp only [hc, ↓reduceIte] at hpc
    rw [show Labels.label NativeRustcVmArm.Vm.VerifyKeccak.label_32 = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyKeccak.b73Offset) from
      hp.label (j := NativeRustcVmArm.Vm.VerifyKeccak.b73Offset) NativeRustcVmArm.Vm.VerifyKeccak.label_32_at] at hpc
    subst hpc
    refine goal_exit hp hn hfr1 ?_ fun _ _ _ _ hr ↦ by rw [hfail rfl] at hr; cases hr
    rw [hfail rfl]
    exact reg_of hm1 (r := .X0) (v := .lit 0) rfl rfl
  · have hc : SBool.eval (envM m0 m) (.cmp .eq .W32 (.un .trunc .W32 (.reg .X0))
      (.lit 0)) = false := by
      sym_simp; simp only [Env.ofMachine_regs, gx0, hx0]; decide
    simp only [hc, Bool.false_eq_true, ↓reduceIte] at hpc
    rw [show k + NativeRustcVmArm.Vm.VerifyKeccak.b2Offset + b2.length = k + NativeRustcVmArm.Vm.VerifyKeccak.b3Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyKeccak.b2_next]] at hpc
    subst hpc
    have hwf := envM_wf hn hmid.fr
    exact cont rfl d ⟨hfr1, hmid.regs.block (matchM hn hmid.fr) hm1 (by decide),
      by rw [hd]; exact hmid.pk⟩ hd (cs_block (matchM hn hmid.fr) hm1 (by decide))

end

end NativeRustcVmArm.KeccakGkr.VerifyKeccak

namespace NativeRustcVmArm.KeccakGkr.VerifyKeccak

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVmArm.Ring
open NativeRustcVm.Transcript NativeRustcVmArm.Vm.VerifyKeccak

public section

variable [Host] {k : Nat} {a : DecArea} {s : TState} {cs : Array ColumnClaimW}
  {inst output : Array EW} {m0 : MachineData}

/-- What a transcript call with an output in the frame keeps: memory but the output, the `TState`
and the stack below the frame. -/
@[expose] def TKeep (m0 : MachineData) (o n : Nat) (d d' : Mem 64) : Prop :=
  SameOutside d d' (fun q ↦
    (m0.regs.SP.toNat - 3360 + o ≤ q.toNat ∧ q.toNat < m0.regs.SP.toNat - 3360 + o + n) ∨
      ((tA m0).toNat ≤ q.toNat ∧ q.toNat < (tA m0).toNat + 760) ∨
      (m0.regs.SP.toNat - 7008 ≤ q.toNat ∧ q.toNat < m0.regs.SP.toNat - 3360))

/-- **`sample_challenges(t, frame + o, n)`**, after a block writing only the output. -/
theorem scStep (h : P0 a s cs inst output m0) (hn : Nums a inst m0)
    (hsc : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.TStateSampleChallenges.entryLabel) (SampleChallengesPre a s)
      (SampleChallengesPost a s))
    {ds : List Directive} {i : Nat} {S' : SState} {o n : Nat} {s1 : TState} {m : MachineData}
    {R : MachineState → Prop}
    (hk : ds.IsInfixAt Host.prog i)
    (hrun : exec ds midS = some (S', .call NativeRustcVmArm.Vm.TStateSampleChallenges.entryLabel))
    (hmid : Mid m0 m) (hts : TStateAt m.dmem (tA m0) a s1)
    (hcl : NativeRustcVm.Layout.ClaimsWAt m.dmem (clA m0) cs)
    (hsp : S'.sp = .ptr 0 0)
    (hw : S'.mem.all (fun w ↦ w.r == 0 &&
      [(o, o + 16 * n)].any (fun p ↦ decide (p.1 ≤ w.off) && decide (w.off + w.n ≤ p.2))) = true)
    (hrk : regsL.all (fun r ↦ (midS.reg r).isSome && S'.reg r == midS.reg r) = true)
    (hck : csL.all (fun r ↦ (midS.reg r).isSome && S'.reg r == midS.reg r) = true)
    (hx0 : S'.reg .X0 = some (.reg .X20)) (hx1 : S'.reg .X1 = some (.ptr 0 (o : Int)))
    (hx2 : S'.reg .X2 = some (.lit n)) (ho : 96 ≤ o) (hon : o + 16 * n ≤ 3264) (hn64 : n < 2 ^ 64)
    (cont : ∀ m2 xs s2, (sampleChallenges n).run s1 = some (xs, s2) → Mid m0 m2 →
      TStateAt m2.dmem (tA m0) a s2 → NativeRustcVm.Layout.ClaimsWAt m2.dmem (clA m0) cs →
      NativeRustcVm.EWsAt m2.dmem (loc m0 o) xs.toList → TKeep m0 o (16 * n) m.dmem m2.dmem →
      (∀ r, calleeSaved r = true → m2.regs.getXReg r = m.regs.getXReg r) →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (i + ds.length)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf i⟩ := by
  have hwf := envM_wf hn hmid.fr
  have hN := hn.hN
  have hscs : sampleChallengesStack = 464 := rfl
  refine callStep hn hk hrun hmid.fr (matchM hn hmid.fr) hwf hsp
    (writeOk_ranges (by simp [hon]) hw)
    (N' := sampleChallengesStack) (lo := o) (n := 16 * n) (by decide) hon (hsc a s1)
    (fun st hm1 hfr1 ↦ ?_) (fun st m' hm1 hfr1 hq ↦ ?_) fun st m2 hm1 hfr1 hq hfr2 hcs ↦ ?_
  all_goals
    have hb := written_in hn hm1 hwf hw
    have e0 : st.regs.X0 = m0.regs.X0 :=
      (reg_of hm1 (r := .X0) (v := .reg .X20) hx0 rfl).trans hmid.regs.x20
    have e1 : st.regs.X1.toBitVec = loc m0 o := reg_loc hm1 hx1
    have e2 : st.regs.X2.toNat = n := by
      rw [← UInt64.toNat_toBitVec, show st.regs.X2 = st.regs.getXReg .X2 from rfl,
        hm1.regs .X2 _ hx2]
      simp only [Sym.eval, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hn64
    have := hn.tS; have := hn.wS; have := hn.cS; have := hn.txc; have := hn.c_w
    have hts1 : TStateAt st.dmem (tA m0) a s1 :=
      ts_keep hn hts (hm1.kept hwf) hb fun q ⟨p, hp, hq⟩ ↦ by
        simp only [List.mem_singleton] at hp; subst hp; constructor <;> omega
  · refine ⟨stackOk_of hn hfr1 (by decide), rcAt_of h hn hfr1 (by decide), ?_, ?_, ?_⟩
    · show TStateAt _ st.regs.X0.toBitVec a s1
      rw [e0]; exact hts1
    · show TStateOk _ st.regs.X0.toBitVec a _
      rw [e0]; exact tok_of hn hfr1 (by decide)
    · show OutOk _ st.regs.X0.toBitVec a st.regs.X1.toBitVec (16 * st.regs.X2.toNat) _
      rw [e0, e1, e2]; exact outOk_loc hn hfr1 (by decide) hon
  · obtain ⟨-, hs, hsv⟩ := hq
    refine ⟨NativeRustcVm.SameOutside.mono hs fun q hq ↦ ?_, hsv⟩
    rw [e1, e2] at hq
    rcases hq with hq | hq | hq
    · exact .inr (.inl hq)
    · exact .inr (.inr (.inl (by rw [e0] at hq; exact hq)))
    · exact .inl hq
  · obtain ⟨⟨xs, s2, hr, hxs, hts2⟩, hs, hsv⟩ := hq
    rw [e0, e1, e2] at *
    have hR : ∀ q, (InRange (loc m0 o) (16 * n) q ∨ InRange (tA m0) tstateBytes q ∨
        InRange (stackBelow st sampleChallengesStack) sampleChallengesStack q) → _ :=
      fun q hq ↦ tR_nat hn hfr1 (by omega) (by decide) hq
    have hmid1 : Mid m0 st :=
      ⟨hfr1, hmid.regs.block (matchM hn hmid.fr) hm1 hrk, word_keep hmid.pk hb
        (by rw [loc_toNat hn.hN (by omega)]; have := m0.regs.SP.toNat_lt; omega)
        (by rw [loc_toNat hn.hN (by omega)]; intro q ⟨p, hp, hq⟩
            simp only [List.mem_singleton] at hp; subst hp; omega)⟩
    refine cont m2 xs s2 hr (Mid.call hn hmid1 hfr2 hcs hs fun q hq ↦ ?_) hts2 ?_ hxs ?_
      (fun r hr ↦ (hcs r hr).trans (cs_block (matchM hn hmid.fr) hm1 hck r hr))
    · rcases hR q hq with h1 | h1 | h1 <;> omega
    · refine cls_keep hn (cls_keep hn hcl hb fun q ⟨p, hp, hq⟩ ↦ ?_) hs fun q hq ↦ ?_
      · simp only [List.mem_singleton] at hp; subst hp; omega
      · rcases hR q hq with h1 | h1 | h1 <;> omega
    · intro q hq
      rw [hs q fun h1 ↦ hq ?_, hb q fun ⟨p, hp, h2⟩ ↦ hq ?_]
      · simp only [List.mem_singleton] at hp; subst hp; exact .inl ⟨by omega, by omega⟩
      · rcases hR q h1 with h1 | h1 | h1
        · exact .inl h1
        · exact .inr (.inl h1)
        · exact .inr (.inr ⟨by omega, h1.2⟩)

/-- **`read_scalar(frame + o, t)`**, after a block without writes. -/
theorem rsStep (h : P0 a s cs inst output m0) (hn : Nums a inst m0)
    (hrs : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.TStateReadScalar.entryLabel) (ReadScalarPre a s) (ReadScalarPost a s))
    {ds : List Directive} {i : Nat} {S' : SState} {o : Nat} {s1 : TState} {m : MachineData}
    {cs' : Array ColumnClaimW} {R : MachineState → Prop}
    (hk : ds.IsInfixAt Host.prog i)
    (hrun : exec ds midS = some (S', .call NativeRustcVmArm.Vm.TStateReadScalar.entryLabel))
    (hmid : Mid m0 m) (hts : TStateAt m.dmem (tA m0) a s1)
    (hcl : NativeRustcVm.Layout.ClaimsWAt m.dmem (clA m0) cs')
    (hsp : S'.sp = .ptr 0 0) (hmem : S'.mem = [])
    (hrk : regsL.all (fun r ↦ (midS.reg r).isSome && S'.reg r == midS.reg r) = true)
    (hx0 : S'.reg .X0 = some (.ptr 0 (o : Int))) (hx1 : S'.reg .X1 = some (.reg .X20))
    (ho : 96 ≤ o) (hon : o + 24 ≤ 3264)
    (cont : ∀ st m2 : MachineData, Match (envM m0 m) S' st →
      OptEWAt m2.dmem (loc m0 o) ((readScalar.run s1).map (·.1)) →
      NextAt m2.dmem (tA m0) a (readScalar.run s1) → Mid m0 m2 →
      NativeRustcVm.Layout.ClaimsWAt m2.dmem (clA m0) cs' → TKeep m0 o 24 m.dmem m2.dmem →
      (∀ r, calleeSaved r = true → m2.regs.getXReg r = st.regs.getXReg r) →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (i + ds.length)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf i⟩ := by
  have hwf := envM_wf hn hmid.fr
  have hN := hn.hN
  refine callStep hn hk hrun hmid.fr (matchM hn hmid.fr) hwf hsp
    (by rw [hmem]; intro w hw; cases hw)
    (N' := readScalarStack) (lo := o) (n := 24) (by decide) hon (hrs a s1)
    (fun st hm1 hfr1 ↦ ?_) (fun st m' hm1 hfr1 hq ↦ ?_) fun st m2 hm1 hfr1 hq hfr2 hcs ↦ ?_
  all_goals
    have hd : st.dmem = m.dmem := hm1.dmem_eq hwf hmem
    have e1 : st.regs.X1 = m0.regs.X0 :=
      (reg_of hm1 (r := .X1) (v := .reg .X20) hx1 rfl).trans hmid.regs.x20
    have e0 : st.regs.X0.toBitVec = loc m0 o := reg_loc hm1 hx0
  · refine ⟨stackOk_of hn hfr1 (by decide), rcAt_of h hn hfr1 (by decide), ?_, ?_, ?_⟩
    · show TStateAt _ st.regs.X1.toBitVec a s1
      rw [e1, hd]; exact hts
    · show TStateOk _ st.regs.X1.toBitVec a _
      rw [e1]; exact tok_of hn hfr1 (by decide)
    · show OutOk _ st.regs.X1.toBitVec a st.regs.X0.toBitVec 24 _
      rw [e0, e1]; exact outOk_loc hn hfr1 (by decide) hon
  · obtain ⟨-, -, hs, hsv⟩ := hq
    refine ⟨NativeRustcVm.SameOutside.mono hs fun q hq ↦ ?_, hsv⟩
    rw [e0, e1] at hq
    rcases hq with hq | hq | hq
    · exact .inr (.inl hq)
    · exact .inr (.inr (.inl hq))
    · exact .inl hq
  · obtain ⟨hv, hnx, hs, hsv⟩ := hq
    rw [e0] at hv
    rw [e1] at hnx
    rw [e0, e1] at hs
    have hR : ∀ q, (InRange (loc m0 o) 24 q ∨ InRange (tA m0) tstateBytes q ∨
        InRange (stackBelow st readScalarStack) readScalarStack q) → _ :=
      fun q hq ↦ tR_nat hn hfr1 (by omega) (by decide) hq
    have := hn.tS; have := hn.wS; have := hn.cS; have := hn.txc; have := hn.c_w
    have hrss : readScalarStack = 544 := rfl
    have hmid1 : Mid m0 st :=
      ⟨hfr1, hmid.regs.block (matchM hn hmid.fr) hm1 hrk, by rw [hd]; exact hmid.pk⟩
    refine cont st m2 hm1 hv hnx (Mid.call hn hmid1 hfr2 hcs hs fun q hq ↦ ?_) ?_ ?_ hcs
    · rcases hR q hq with h1 | h1 | h1 <;> omega
    · rw [hd] at hs
      refine cls_keep hn hcl hs fun q hq ↦ ?_
      rcases hR q hq with h1 | h1 | h1 <;> omega
    · intro q hq
      rw [hd] at hs
      refine hs q fun h1 ↦ hq ?_
      rcases hR q h1 with h1 | h1 | h1
      · exact .inl h1
      · exact .inr (.inl h1)
      · exact .inr (.inr ⟨by omega, h1.2⟩)

end

end NativeRustcVmArm.KeccakGkr.VerifyKeccak
