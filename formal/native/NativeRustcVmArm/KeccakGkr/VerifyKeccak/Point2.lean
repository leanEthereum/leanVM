module

public import NativeRustcVmArm.Code.Vm.BufEW36Extend.Names
public import NativeRustcVmArm.Code.Vm.PushClaim.Names
public import NativeRustcVmArm.KeccakGkr.VerifyKeccak.Point1

/-!
# `verify_keccak`: the output point, the slot, the column claim

`b51`: the buffer at 2592 extended by the slot point; `b52`: its verdict; `b53`:
`push_claim(claims, QKECCAK, point, word)`; `b54`: its verdict. At `b55`: `AtS`.
-/

namespace NativeRustcVmArm.KeccakGkr.VerifyKeccak

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVmArm.Ring
open NativeRustcVm.Transcript NativeRustcVmArm.Vm.VerifyKeccak
open NativeRustcVm.KeccakGkr (ClaimAt WeightsAt)
open LeanVM.Protocol.Verifier (qkeccak)

public section

variable [Host] {k : Nat} {a : DecArea} {s : TState} {cs : Array ColumnClaimW}
  {inst output : Array EW} {m0 : MachineData}

/-- **The slot and the column claim** (`b51` to `b54`). -/
theorem stepPoint2 (hp : Placed code k) (h : P0 a s cs inst output m0) (hn : Nums a inst m0)
    (hext : Spec (Labels.label NativeRustcVmArm.Vm.BufEW36Extend.entryLabel) (BufEWExtendPre 36) (BufEWExtendPost 36))
    (hpc : ∀ cs, Spec (Labels.label NativeRustcVmArm.Vm.PushClaim.entryLabel) (PushClaimPre cs) (PushClaimPost cs))
    {m : MachineData} {s1 : TState} {cj : KeccakClaimW} {sl : Array EW} {w : EW}
    (hw : AtP a s cs inst output m0 m s1 cj sl w)
    (cont : ∀ m', AtS a s cs inst output m0 m' s1 cj (outsOf inst sl w) →
      Eventually (step1 Host.exe) (Goal a s cs inst output m0) ⟨m', Host.addrOf (k + NativeRustcVmArm.Vm.VerifyKeccak.b55Offset)⟩) :
    Eventually (step1 Host.exe) (Goal a s cs inst output m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyKeccak.b51Offset)⟩ := by
  have hN := hn.hN
  have hSP := m0.regs.SP.toNat_lt
  have n30 := h.n30
  have hwf := envM_wf hn hw.mid.fr
  have l2592 := loc_toNat (m0 := m0) hn.hN (o := 2592) (by decide)
  have l2496 := loc_toNat (m0 := m0) hn.hN (o := 2496) (by decide)
  have hlen : (inst.extract 0 4 ++ inst.extract 4 inst.size).toList.length = inst.size := by
    rw [inst_split, Array.length_toList]
  -- `b51`
  refine extC hn hext (b51_in_code.trans hp.1 (by simp [b51])) run_b51 hw.mid rfl
    (Lb := []) (L := (inst.extract 0 4 ++ inst.extract 4 inst.size).toList) (xs := sl.toList)
    (A := loc m0 2496) (by decide) (by decide) (by decide) (by decide) rfl
    (fun st hm1 hfr1 ↦ ?_) (by rw [hlen, Array.length_toList, hw.slsz]; omega)
    fun st m2 hm1 hmid2 hbuf2 hx2 hb2 hc2 hk2 hcs2 ↦ ?_
  · have hd : st.dmem = m.dmem := hm1.dmem_eq hwf rfl
    refine ⟨reg_loc hm1 (r := .X1) (o := 2496) rfl, ?_, by rw [hd]; exact hw.buf,
      by rw [hd]; exact hw.slot, ⟨frame_mapped' hn hfr1 (by simp [hw.slsz]),
        loc_noWrap hn (by simp [hw.slsz])⟩, ?_⟩
    · rw [show st.regs.X2 = (6 : UInt64) from reg_of hm1 (r := .X2) (v := .lit 6) rfl rfl,
        Array.length_toList, hw.slsz]; rfl
    · unfold Apart; rw [l2592, l2496]; simp only [Array.length_toList, hw.slsz]; omega
  have x19 : (m2.regs.getXReg .X19).toBitVec = loc m0 2592 := by
    rw [hcs2 .X19 rfl, Match.reg_eq (matchM hn hw.mid.fr) hm1 (r := .X19) rfl rfl]; exact hw.x19
  have x28 : m2.regs.getXReg .X28 = w.c0 := by
    rw [hcs2 .X28 rfl, Match.reg_eq (matchM hn hw.mid.fr) hm1 (r := .X28) rfl rfl]; exact hw.x28
  rw [show k + NativeRustcVmArm.Vm.VerifyKeccak.b51Offset + b51.length = k + NativeRustcVmArm.Vm.VerifyKeccak.b52Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyKeccak.b51_next]]
  refine failBranch hp hn (b52_in_code.trans hp.1 (by simp [b52])) run_b52 hmid2 rfl rfl
    (by decide) (by decide) (b := true)
    (condW0 (by rw [Env.ofMachine_regs, gx0, hx2]; rfl)) (fun hf ↦ nomatch hf)
    fun _ m3 hmid3 hd3 hcs3 ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.VerifyKeccak.b52Offset + b52.length = k + NativeRustcVmArm.Vm.VerifyKeccak.b53Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyKeccak.b52_next]]
  have hb2' : Chg m0 [(2592, 3176)] [] m.dmem m3.dmem := by
    rw [hd3]; exact (hb2.trans hc2).mono (fun p hp ↦ by simpa using hp) (fun o ho ↦ by simp at ho)
  have hk3 : Kept m.dmem m3.dmem := by rw [hd3]; exact hk2
  have hbuf3 : NativeRustcVm.BufEWAt m3.dmem (loc m0 2592) 36
      (inst.extract 0 4 ++ inst.extract 4 inst.size ++ sl).toList := by
    rw [hd3, Array.toList_append]; exact hbuf2
  have hcnt : (inst.extract 0 4 ++ inst.extract 4 inst.size ++ sl).size = inst.size + 6 := by
    rw [Array.size_append, inst_split, hw.slsz]
  -- `b53`
  have hwf3 := envM_wf hn hmid3.fr
  have hl : (Sym.load 0 2592 8).eval (envM m0 m3) = (inst.size + 6).toUInt64.toBitVec := by
    have := Sumcheck.load_word (env := envM m0 m3) (r := 0) (off := 2592) hbuf3.2.1
    show (envM m0 m3).load 0 2592 8 = _
    rw [this, Array.length_toList, hcnt]
  have hlt : ((Sym.load 0 2592 8).eval (envM m0 m3)).toNat < 37 := by
    rw [hl, u64_toNat (by omega)]; omega
  refine callC hn (b53_in_code.trans hp.1 (by simp [b53])) run_b53 hmid3.fr (matchM hn hmid3.fr)
    hwf3 rfl (Lb := []) (L := []) (O := [(2, 0, 97288)]) (lo := 0) (n := 0) (by decide)
    (by decide) (by decide) (by decide) (by decide) (hpc cs) (fun st hm1 hfr1 ↦ ?_)
    (fun st m' hm1 hfr1 hq ↦ ?_) fun st m4 hm1 hfr1 hq hfr4 hcs4 hb4 hc4 hk4 ↦ ?_
  all_goals
    have hd : st.dmem = m3.dmem := hm1.dmem_eq hwf3 rfl
    have e0 : st.regs.X0 = m0.regs.X6 :=
      (reg_of hm1 (r := .X0) (v := .reg .X23) rfl rfl).trans hmid3.regs.x23
    have e2 : st.regs.X2.toBitVec = loc m0 2600 := by
      rw [show st.regs.X2 = st.regs.getXReg .X2 from rfl, hm1.regs .X2 _ rfl,
        eval_ite_lt (by decide) hlt, eval_add_reg (p := loc m0 2592)
            (by rw [hcs3 .X19 rfl]; exact x19)]
      exact loc_add m0 2592 8
    have e3 : st.regs.X3.toNat = inst.size + 6 := by
      rw [← UInt64.toNat_toBitVec, show st.regs.X3 = st.regs.getXReg .X3 from rfl,
        hm1.regs .X3 _ rfl, eval_ite_lt (by decide) hlt, hl, u64_toNat (by omega)]
    have hpt : NativeRustcVm.EWsAt st.dmem (loc m0 2600)
        (inst.extract 0 4 ++ inst.extract 4 inst.size ++ sl).toList := by
      have := hbuf3.2.2; rw [show loc m0 2592 + 8#64 = loc m0 2600 from loc_add m0 2592 8] at this
      rw [hd]; exact this
  · have hpcs : pushClaimStack = 48 := rfl
    have e97 : NativeRustcVm.Layout.claimsBytes = 97288 := rfl
    have hcS : m0.regs.X6.toBitVec.toNat + 97288 ≤ m0.regs.SP.toNat - 7008 ∨
        m0.regs.SP.toNat ≤ m0.regs.X6.toBitVec.toNat := hn.cS
    refine ⟨stackOk_of hn hfr1 (by decide), ?_, ?_, ?_, ?_, ?_⟩
    · rw [e0, hd]; exact hb2'.cls hn (by decide) (by decide) (by decide) hw.cls
    · rw [e0]; exact ok_of (ok_cl h) hn.cW hfr1 le_rfl
    · rw [e0]; unfold OffStack Apart; rw [sb_toNat hn.hN hfr1 (by decide)]
      obtain h1 | h1 := hcS <;> omega
    · refine ⟨?_, ?_⟩
      · rw [e2, e3]; exact ⟨frame_mapped' hn hfr1 (by omega), loc_noWrap hn (by omega)⟩
      · rw [e2, e3]; unfold OffStack Apart
        rw [sb_toNat hn.hN hfr1 (by decide), loc_toNat hn.hN (by omega)]; omega
    · rw [e0, e2, e3]; unfold Apart; rw [loc_toNat hn.hN (by omega)]
      obtain h1 | h1 := hcS <;> omega
  · obtain ⟨-, hs, hsv⟩ := hq
    refine ⟨NativeRustcVm.SameOutside.mono hs fun q hq ↦ ?_, hsv⟩
    rcases hq with hq | hq
    · rw [e0] at hq
      exact ws_ob0 hn (i := 2) (n := 97288) (by decide) (by decide) (by decide) (by decide) hq
    · exact ws_stk hn hfr1 (by decide) hq
  · obtain ⟨hpost, -, -⟩ := hq
    rw [e3] at hpost
    have hcap : cs.size < NativeRustcVm.Layout.claimCap ∧ inst.size + 6 ≤
        NativeRustcVm.Layout.pointCap := ⟨h.ncs, by unfold NativeRustcVm.Layout.pointCap; omega⟩
    simp only [hcap, and_self, ↓reduceIte] at hpost
    obtain ⟨hx4, hcl4⟩ := hpost
    have hsl : slice st st.regs.X2 st.regs.X3 =
        inst.extract 0 4 ++ inst.extract 4 inst.size ++ sl := by
      unfold slice
      rw [e2, e3, ← hcnt, ← Array.length_toList, NativeRustcVm.ewsOf_of_ewsAt hpt,
        Array.toArray_toList]
    have e1 : st.regs.X1.toNat = qkeccak := by
      rw [show st.regs.X1 = (4 : UInt64) from reg_of hm1 (r := .X1) (v := .lit 4) rfl rfl]; rfl
    have e45 : ewArg st.regs.X4 st.regs.X5 = w := by
      have e4 : st.regs.X4 = w.c0 := by
        rw [show st.regs.X4 = m3.regs.getXReg .X28 from
          reg_of hm1 (r := .X4) (v := .reg .X28) rfl rfl, hcs3 .X28 rfl, x28]
      have e5 : st.regs.X5 = w.c1 := reg_of hm1 (r := .X5) (v := .load 0 80 8) rfl
        (Sumcheck.load_word (hb2'.word hn (by decide) (by decide) (by decide) hw.w80))
      rw [e4, e5]; rfl
    rw [hsl, e1, e45, e0] at hcl4
    have hT : Chg m0 [(2592, 3176)] [(2, 0, 97288)] m.dmem m4.dmem :=
      (hb2'.trans (hb4.trans hc4)).mono (fun p hp ↦ by simpa using hp)
        (fun o ho ↦ by simpa using ho)
    have hk : Kept m.dmem m4.dmem := kept_tr hk3 hk4
    have hmid4 : Mid m0 m4 := Mid.chg hn hmid3 hfr4
      (regs_kept (matchM hn hmid3.fr) hm1 (by decide) hcs4) (hb4.trans hc4) (by decide)
      (by decide)
    rw [show k + NativeRustcVmArm.Vm.VerifyKeccak.b53Offset + b53.length = k + NativeRustcVmArm.Vm.VerifyKeccak.b54Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyKeccak.b53_next]]
    refine failBranch hp hn (b54_in_code.trans hp.1 (by simp [b54])) run_b54 hmid4 rfl rfl
      (by decide) (by decide) (b := true)
      (condW0 (by rw [Env.ofMachine_regs, gx0, hx4]; rfl)) (fun hf ↦ nomatch hf)
      fun _ m5 hmid5 hd5 hcs5 ↦ ?_
    rw [show k + NativeRustcVmArm.Vm.VerifyKeccak.b54Offset + b54.length = k + NativeRustcVmArm.Vm.VerifyKeccak.b55Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyKeccak.b54_next]]
    refine cont m5 ⟨hmid5, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hw.psz, hw.run⟩ <;> rw [hd5]
    · exact hT.word hn (by decide) (by decide) (by decide) hw.w40
    · exact hT.word hn (by decide) (by decide) (by decide) hw.w64
    · exact hT.word hn (by decide) (by decide) (by decide) hw.w72
    · exact hT.ts hn hk (by decide) (by decide) (by decide) hw.ts
    · exact hcl4
    · exact hT.claim hn (by decide) (by decide) (by decide) hw.claim
    · exact hT.wts hn (by decide) (by decide) (by decide) (by decide) hw.wts

end

end NativeRustcVmArm.KeccakGkr.VerifyKeccak
