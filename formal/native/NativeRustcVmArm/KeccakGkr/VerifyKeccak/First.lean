module

public import NativeRustcVmArm.Code.Vm.FirstClaim.Names
public import NativeRustcVmArm.KeccakGkr.VerifyKeccak.Areas

/-!
# `verify_keccak`: the first claim

`b7`: `first_claim` into the frame's `Option<KeccakClaimW>` at 960, its bit weights into the
scratch's first; `b8`: its tag (always `Some`). At `b9` (`AtF`): the claim at 968.
-/

namespace NativeRustcVmArm.KeccakGkr.VerifyKeccak

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVmArm.Ring
open NativeRustcVm.Transcript NativeRustcVmArm.Vm.VerifyKeccak
open NativeRustcVm.KeccakGkr (ClaimAt WeightsAt scratchBytes)
open NativeRustcVm (Region)

@[expose] public section

/-- **After the first claim** (`b9`). -/
structure AtF [Labels] (a : DecArea) (s : TState) (cs : Array ColumnClaimW) (inst output : Array EW)
    (m0 m : MachineData) (s4 : TState) (first : KeccakClaimW) (c : EW) : Prop where
  mid : Mid m0 m
  x28 : (m.regs.getXReg .X28).toBitVec = loc m0 960
  x29 : m.regs.getXReg .X29 = c.c1
  w72 : NativeRustcVm.WordAt m.dmem (loc m0 72) m0.regs.X7
  w80 : NativeRustcVm.WordAt m.dmem (loc m0 80) c.c0
  ts : TStateAt m.dmem (tA m0) a s4
  cls : NativeRustcVm.Layout.ClaimsWAt m.dmem (clA m0) cs
  claim : ClaimAt m.dmem (loc m0 968) first
  wts : WeightsAt m.dmem (scA m0) first
  hfirst : first.point.size = inst.size - 4 + 1
  run : run0 s inst output m0 = (afterCommitted m0.regs.X1.toNat inst first c).run s4

end

public section

variable [Host] {k : Nat} {a : DecArea} {s : TState} {cs : Array ColumnClaimW}
  {inst output seg lp : Array EW} {m0 : MachineData}

/-- **The first claim** (`b7`, `b8`). -/
theorem stepFirst (hp : Placed code k) (h : P0 a s cs inst output m0) (hn : Nums a inst m0)
    (hfc : Spec (Labels.label NativeRustcVmArm.Vm.FirstClaim.entryLabel)
      (FirstClaimPre inst seg lp output) (FirstClaimPost inst seg lp output))
    {m : MachineData} {s4 : TState} {c : EW}
    (hc : AtC a s cs inst output m0 m s4 seg lp c)
    (cont : ∀ m', AtF a s cs inst output m0 m' s4
        (keccakFirstClaim inst seg lp output c) c →
      Eventually (step1 Host.exe) (Goal a s cs inst output m0) ⟨m', Host.addrOf (k + NativeRustcVmArm.Vm.VerifyKeccak.b9Offset)⟩) :
    Eventually (step1 Host.exe) (Goal a s cs inst output m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyKeccak.b7Offset)⟩ := by
  have hwf := envM_wf hn hc.mid.fr
  have hN := hn.hN
  have hSP := m0.regs.SP.toNat_lt
  have hfcs : firstClaimStack = 2112 := rfl
  have e0 := hc.cv.2
  rw [show off (loc m0 960) 8 = loc m0 968 from loc_add m0 960 8] at e0
  have ec := load_ew (env := envM m0 m) (r := 0) (o := 968) e0
  refine callStep hn (b7_in_code.trans hp.1 (by simp [b7])) run_b7 hc.mid.fr (matchM hn hc.mid.fr)
    hwf rfl (writeOk_low (by decide)) (N' := firstClaimStack) (lo := 960) (n := 776)
    (by decide) (by decide) hfc (fun st hm1 hfr1 ↦ ?_) (fun st m' hm1 hfr1 hq ↦ ?_)
    fun st m2 hm1 hfr1 hq hfr2 hcs ↦ ?_
  all_goals
    have hb := written_in hn hm1 hwf (L := [(0, 8), (72, 88)]) (by decide)
    have e0 : st.regs.X0.toBitVec = loc m0 960 := reg_loc hm1 (r := .X0) (o := 960) rfl
    have e3 : st.regs.X3.toBitVec = loc m0 96 := reg_loc hm1 (r := .X3) (o := 96) rfl
    have e4 : st.regs.X4.toBitVec = loc m0 112 := reg_loc hm1 (r := .X4) (o := 112) rfl
    have e1 : st.regs.X1 = m0.regs.X2 :=
      (reg_of hm1 (r := .X1) (v := .reg .X24) rfl rfl).trans hc.mid.regs.x24
    have e2 : st.regs.X2 = m0.regs.X3 := (reg_of hm1 (r := .X2)
        (v := .reg .X28) rfl rfl).trans hc.x28
    have e5 : st.regs.X5 = m0.regs.X4 := (reg_of hm1 (r := .X5)
        (v := .reg .X19) rfl rfl).trans hc.x19
    have e6 : st.regs.X6 = c.c0 := reg_of hm1 (r := .X6) (v := .load 0 968 8) rfl ec.1
    have e7 : st.regs.X7 = c.c1 := reg_of hm1 (r := .X7) (v := .load 0 976 8) rfl ec.2
    have hsp : st.regs.SP.toBitVec = fb m0 := hfr1.sp
    have hw0 : firstWeights st = scA m0 := by
      have := Sumcheck.Match.wordAt_write hm1 (r := 0) (o := 0) (v := .reg .X22) rfl (by decide)
        (by decide)
      unfold firstWeights
      rw [hsp, show fb m0 = fb m0 + BitVec.ofNat 64 0 by simp,
        NativeRustcVm.wordOf_of_wordAt this]
      simp only [Sym.eval, Env.ofMachine_regs, hc.mid.regs.x22]; rfl
  · have hfb : st.regs.SP.toBitVec = loc m0 0 := by rw [hsp]; simp
    refine ⟨stackOk_of hn hfr1 (by decide), by rw [e2]; exact h.n3, h.n30, ?_, hc.segSz, ?_,
      hc.lpSz, ?_, h.o25, ?_, ?_⟩
    · rw [e1]
      show NativeRustcVm.EWsAt st.dmem (ipA m0) inst.toList
      exact bytes_m0 hn hfr1 h.insts (by rw [ews16, Array.length_toList]; exact hn.iW)
        (by rw [ews16, Array.length_toList]; exact hn.iS) fun q hq ↦ by
          rw [ews16, Array.length_toList]
          have := hn.t_i; have := hn.s_i; have := hn.c_i; have := hn.o_i
          rcases outs_nat hn hq with _ | _ | _ | _ <;> omega
    · rw [e3]
      refine ews_keep hc.segv hb
          (by rw [Array.length_toList, hc.segSz, loc_toNat hn.hN (by omega)]; omega)
        fun q ⟨p, hp, hq⟩ ↦ ?_
      rw [Array.length_toList, hc.segSz, loc_toNat hn.hN (by omega)]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> omega
    · rw [e4]
      refine ews_keep hc.lpv hb
          (by rw [Array.length_toList, hc.lpSz, loc_toNat hn.hN (by omega)]; omega)
        fun q ⟨p, hp, hq⟩ ↦ ?_
      rw [Array.length_toList, hc.lpSz, loc_toNat hn.hN (by omega)]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> omega
    · rw [e5]
      show NativeRustcVm.EWsAt st.dmem (opA m0) output.toList
      exact bytes_m0 hn hfr1 h.outv (by rw [ews16, Array.length_toList, h.o25]; exact hn.pW)
        (by rw [ews16, Array.length_toList, h.o25]; exact hn.pS) fun q hq ↦ by
          rw [ews16, Array.length_toList, h.o25]
          have := hn.t_p; have := hn.s_p; have := hn.c_p; have := hn.o_p
          rcases outs_nat hn hq with _ | _ | _ | _ <;> omega
    · show Areas st firstClaimStack [⟨st.regs.X0.toBitVec, 8 + NativeRustcVm.KeccakGkr.claimBytes⟩,
        ⟨firstWeights st, NativeRustcVm.KeccakGkr.weightsBytes⟩]
        [ewsRegion st.regs.X1.toBitVec inst.size, ewsRegion st.regs.X3.toBitVec 1,
          ewsRegion st.regs.X4.toBitVec 5, ewsRegion st.regs.X5.toBitVec 25,
          ⟨st.regs.SP.toBitVec, 8⟩]
      rw [e0, e1, e3, e4, e5, hw0, hfb]
      show Areas st firstClaimStack [⟨loc m0 960, _⟩, ⟨scA m0, _⟩]
        [ewsRegion (ipA m0) inst.size, _, _, ewsRegion (opA m0) 25, _]
      areas_split
      all_goals first
        | exact (ok_loc hn hfr1 (by decide)).1
        | exact (ok_loc hn hfr1 (by decide)).2
        | exact (ok_of (ok_sc h) hn.sW hfr1 (by decide)).1
        | exact (ok_of (ok_sc h) hn.sW hfr1 (by decide)).2
        | exact (ok_of (ok_ip h) hn.iW hfr1 le_rfl).1
        | exact (ok_of (ok_ip h) hn.iW hfr1 le_rfl).2
        | exact (ok_of (ok_op h) hn.pW hfr1 le_rfl).1
        | exact (ok_of (ok_op h) hn.pW hfr1 le_rfl).2
        | (try rw [hfcs]); apart_auto hn hfr1
  · obtain ⟨-, -, -, hs, hsv⟩ := hq
    refine ⟨NativeRustcVm.SameOutside.mono hs fun q ⟨r, hr, hq⟩ ↦ ?_, hsv⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl hq
    · rw [e0] at hq; exact .inr (.inl hq)
    · rw [hw0] at hq
      exact .inr (.inr (.inr (.inl (by
        simp only [NativeRustcVm.Region.Holds, NativeRustcVm.InRange,
          NativeRustcVm.KeccakGkr.weightsBytes] at hq
        show (q - scA m0).toNat < 205824; omega))))
  · obtain ⟨hw1, hcl, hwt, hs, hsv⟩ := hq
    rw [e6, e7, show ({ c0 := c.c0, c1 := c.c1 } : EW) = c from rfl] at hcl hwt
    rw [e0] at hw1 hcl
    rw [hw0] at hwt
    rw [show off (loc m0 960) 8 = loc m0 968 from loc_add m0 960 8] at hcl
    have hfs := first_point_size inst seg lp output c hc.segSz
    have hrun := hc.run
    generalize keccakFirstClaim inst seg lp output c = fc at hcl hwt hfs hrun cont ⊢
    have := hn.hN; have := hn.tS; have := hn.wS; have := hn.cS; have := hn.sS; have := hn.txc
    have := hn.txs; have := hn.sxc; have := hn.t_w; have := hn.c_w; have := hn.s_w
    have hR : ∀ q, NativeRustcVm.InAny (stackRegion st firstClaimStack ::
        [⟨st.regs.X0.toBitVec, 8 + NativeRustcVm.KeccakGkr.claimBytes⟩,
          ⟨firstWeights st, NativeRustcVm.KeccakGkr.weightsBytes⟩]) q →
        (m0.regs.SP.toNat - 3360 - 2112 ≤ q.toNat ∧ q.toNat < m0.regs.SP.toNat - 3360) ∨
        (m0.regs.SP.toNat - 3360 + 960 ≤ q.toNat ∧ q.toNat < m0.regs.SP.toNat - 3360 + 1736) ∨
        ((scA m0).toNat ≤ q.toNat ∧ q.toNat < (scA m0).toNat + 25600) := by
      rintro q ⟨r, hr, hq⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · have := stk_nat hn hfr1 (by decide) hq
        rw [hfcs] at this
        exact .inl ⟨by omega, by omega⟩
      · rw [e0] at hq
        simp only [NativeRustcVm.Region.Holds, NativeRustcVm.KeccakGkr.claimBytes] at hq
        have := loc_nat hn (by omega) hq
        exact .inr (.inl ⟨by omega, by omega⟩)
      · rw [hw0] at hq
        simp only [NativeRustcVm.Region.Holds, NativeRustcVm.KeccakGkr.weightsBytes] at hq
        have := inR_nat (by have := hn.sW; omega) hq
        exact .inr (.inr ⟨by omega, by omega⟩)
    have hst : Mid m0 st :=
      ⟨hfr1, hc.mid.regs.block (matchM hn hc.mid.fr) hm1 (by decide), word_keep hc.mid.pk hb
        (by rw [loc_toNat hn.hN (by omega)]; omega)
        (by rw [loc_toNat hn.hN (by omega)]; intro q ⟨p, hp, hq⟩
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
            rcases hp with rfl | rfl <;> omega)⟩
    have hmid2 : Mid m0 m2 := Mid.call hn hst hfr2 hcs hs fun q hq ↦ by
      rcases hR q hq with h1 | h1 | h1 <;> omega
    have hw72 : NativeRustcVm.WordAt st.dmem (loc m0 72) m0.regs.X7 := by
      have := Sumcheck.Match.wordAt_write hm1 (r := 0) (o := 72) (v := .reg .X29) rfl (by decide)
        (by decide)
      simp only [Sym.eval, Env.ofMachine_regs, hc.x29] at this; exact this
    have hw80 : NativeRustcVm.WordAt st.dmem (loc m0 80) c.c0 := by
      have := Sumcheck.Match.wordAt_write hm1 (r := 0) (o := 80) (v := .load 0 968 8) rfl
        (by decide) (by decide)
      simp only [Sym.eval, ec.1] at this; exact this
    have hts : TStateAt st.dmem (tA m0) a s4 :=
      ts_keep hn hc.ts (hm1.kept hwf) hb fun q ⟨p, hp, hq⟩ ↦ by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl <;> constructor <;> omega
    have hcls : NativeRustcVm.Layout.ClaimsWAt st.dmem (clA m0) cs :=
      cls_keep hn hc.cls hb fun q ⟨p, hp, hq⟩ ↦ by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl <;> omega
    have hopt : OptEWAt m2.dmem (loc m0 960) (some fc.value) :=
      ⟨hw1, by rw [show off (loc m0 960) 8 = loc m0 968 from loc_add m0 960 8]; exact hcl.1⟩
    refine failBranch (b := true) hp hn (b8_in_code.trans hp.1 (by simp [b8])) run_b8 hmid2 rfl rfl
      (by decide) (by decide) (cond4 (o := 960) (r := some fc.value) hopt) (fun hf ↦ nomatch hf)
          fun _ m9 hmid9 hd9 hcs9 ↦ ?_
    refine cont m9 ⟨hmid9, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfs, hrun⟩
    · rw [hcs9 .X28 rfl, hcs .X28 rfl]; exact reg_loc hm1 (r := .X28) (o := 960) rfl
    · rw [hcs9 .X29 rfl, hcs .X29 rfl]; exact reg_of hm1 (r := .X29) (v := .load 0 976 8) rfl ec.2
    · rw [hd9]; exact word_keep hw72 hs (by rw [loc_toNat hn.hN (by omega)]; omega) fun q hq ↦ by
        rw [loc_toNat hn.hN (by omega)]; rcases hR q hq with h1 | h1 | h1 <;> omega
    · rw [hd9]; exact word_keep hw80 hs (by rw [loc_toNat hn.hN (by omega)]; omega) fun q hq ↦ by
        rw [loc_toNat hn.hN (by omega)]; rcases hR q hq with h1 | h1 | h1 <;> omega
    · rw [hd9]; exact ts_keep hn hts hsv.2.2 hs fun q hq ↦ by
        rcases hR q hq with h1 | h1 | h1 <;> constructor <;> omega
    · rw [hd9]; exact cls_keep hn hcls hs fun q hq ↦ by rcases hR q hq with h1 | h1 | h1 <;> omega
    · rw [hd9]; exact hcl
    · rw [hd9]; exact hwt

end

end NativeRustcVmArm.KeccakGkr.VerifyKeccak
