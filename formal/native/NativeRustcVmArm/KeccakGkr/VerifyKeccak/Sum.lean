module

public import NativeRustcVmArm.Code.Vm.SumcheckOfSumcheckPlain.Names
public import NativeRustcVmArm.KeccakGkr.VerifyKeccak.Point2

/-!
# `verify_keccak`: the sumcheck over the pack's instances

`b55`: `sumcheck_plain(claim.value, 3, low)` into the frame's `Option<EW>` at 3240, the four
challenges at 3176; `b56`: its tag. At `b57` (`AtU`).
-/

namespace NativeRustcVmArm.KeccakGkr.VerifyKeccak

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVmArm.Ring
open NativeRustcVm.Transcript NativeRustcVmArm.Vm.VerifyKeccak
open NativeRustcVm.KeccakGkr (ClaimAt WeightsAt)

@[expose] public section

/-- **After the sumcheck** (`b57`). -/
structure AtU [Labels] (a : DecArea) (s : TState) (cs : Array ColumnClaimW)
    (inst output : Array EW) (m0 m : MachineData) (s' : TState) (cj : KeccakClaimW)
    (outs : Array ColumnClaimW) (low : Array EW) (v : EW) : Prop where
  mid : Mid m0 m
  w40 : NativeRustcVm.WordAt m.dmem (loc m0 40) (UInt64.ofBitVec (loc m0 1248))
  w64 : NativeRustcVm.WordAt m.dmem (loc m0 64) (UInt64.ofBitVec (scA m0 + BitVec.ofNat 64 140288))
  w72 : NativeRustcVm.WordAt m.dmem (loc m0 72) m0.regs.X7
  ts : TStateAt m.dmem (tA m0) a s'
  cls : NativeRustcVm.Layout.ClaimsWAt m.dmem (clA m0) (cs ++ outs)
  claim : ClaimAt m.dmem (loc m0 960) cj
  wts : WeightsAt m.dmem (scA m0 + BitVec.ofNat 64 25600) cj
  psz : cj.point.size = inst.size - 4 + 1
  lowsz : low.size = 4
  lowv : NativeRustcVm.EWsAt m.dmem (loc m0 3176) low.toList
  val : OptEWAt m.dmem (loc m0 3240) (some v)
  run : run0 s inst output m0 = (afterSum m0.regs.X1.toNat cj outs low v).run s'

end

public section

variable [Host] {k : Nat} {a : DecArea} {s : TState} {cs : Array ColumnClaimW}
  {inst output : Array EW} {m0 : MachineData}

/-- **The sumcheck** (`b55`, `b56`). -/
theorem stepSum (hp : Placed code k) (h : P0 a s cs inst output m0) (hn : Nums a inst m0)
    (hsp : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.SumcheckOfSumcheckPlain.entryLabel) (SumcheckPlainPre a s)
      (SumcheckPlainPost a s))
    {m : MachineData} {s1 : TState} {cj : KeccakClaimW} {outs : Array ColumnClaimW}
    (hw : AtS a s cs inst output m0 m s1 cj outs)
    (cont : ∀ m' s' low v, AtU a s cs inst output m0 m' s' cj outs low v →
      Eventually (step1 Host.exe) (Goal a s cs inst output m0) ⟨m', Host.addrOf (k + NativeRustcVmArm.Vm.VerifyKeccak.b57Offset)⟩) :
    Eventually (step1 Host.exe) (Goal a s cs inst output m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyKeccak.b55Offset)⟩ := by
  have hwf := envM_wf hn hw.mid.fr
  have hN := hn.hN
  have ec := load_ew (env := envM m0 m) (r := 0) (o := 960) hw.claim.1
  refine callC hn (b55_in_code.trans hp.1 (by simp [b55])) run_b55 hw.mid.fr
    (matchM hn hw.mid.fr) hwf rfl (Lb := [(3176, 3240)]) (L := [(3240, 3264), (3176, 3240)])
    (O := [(0, 0, 760)]) (lo := 3176) (n := 88) (by decide) (by decide) (by decide)
    (by decide) (by decide) (hsp a s1) (fun st hm1 hfr1 ↦ ?_) (fun st m' hm1 hfr1 hq ↦ ?_)
    fun st m2 hm1 hfr1 hq hfr2 hcs hb hc hkt ↦ ?_
  all_goals
    have hb0 : Chg m0 [(3176, 3240)] [] m.dmem st.dmem := Chg.block hn hm1 hwf (by decide)
    have e0 : st.regs.X0.toBitVec = loc m0 3240 := reg_loc hm1 (r := .X0) (o := 3240) rfl
    have e1 : st.regs.X1 = m0.regs.X0 :=
      (reg_of hm1 (r := .X1) (v := .reg .X20) rfl rfl).trans hw.mid.regs.x20
    have e5 : st.regs.X5.toBitVec = loc m0 3176 := reg_loc hm1 (r := .X5) (o := 3176) rfl
    have e4 : st.regs.X4.toNat = 3 := by
      rw [show st.regs.X4 = (3 : UInt64) from reg_of hm1 (r := .X4) (v := .lit 3) rfl rfl]; rfl
    have e6 : st.regs.X6.toNat = 4 := by
      rw [show st.regs.X6 = (4 : UInt64) from reg_of hm1 (r := .X6) (v := .lit 4) rfl rfl]; rfl
  · refine ⟨stackOk_of hn hfr1 (by decide), rcAt_of h hn hfr1 (by decide), ?_, ?_, ?_, ?_, ?_,
      ?_, ?_⟩
    · rw [e1]; exact hb0.ts hn (hm1.kept hwf) (by decide) (by decide) (by decide) hw.ts
    · rw [e1]; exact tok_of hn hfr1 (by decide)
    · rw [e4]; decide
    · rw [e4]; decide
    · rw [e0, e1]; exact outOk_loc hn hfr1 (by decide) (by decide)
    · rw [e5, e1, e6]; exact outOk_loc hn hfr1 (by decide) (by decide)
    · rw [e0, e5, e6]; unfold Apart
      rw [loc_toNat hn.hN (by decide), loc_toNat hn.hN (by decide)]; omega
  · obtain ⟨-, hs, hsv⟩ := hq
    refine ⟨NativeRustcVm.SameOutside.mono hs fun q hq ↦ ?_, hsv⟩
    rw [e0, e5, e1, e6] at hq
    rcases hq with hq | hq | hq | hq
    · exact ws_loc hn (o := 3240) (n := 24) (by decide) (by decide) hq
    · exact ws_loc hn (o := 3176) (n := 64) (by decide) (by decide) hq
    · exact ws_ob0 hn (i := 0) (n := 760) (by decide) (by decide) (by decide) (by decide) hq
    · exact ws_stk hn hfr1 (by decide) hq
  · obtain ⟨⟨hout, hsl, hnx⟩, -, -⟩ := hq
    have e23 : (⟨st.regs.X2, st.regs.X3⟩ : EW) = cj.value := by
      rw [show st.regs.X2 = cj.value.c0 from reg_of hm1 (r := .X2) (v := .load 0 960 8) rfl ec.1,
        show st.regs.X3 = cj.value.c1 from reg_of hm1 (r := .X3) (v := .load 0 968 8) rfl ec.2]
    rw [e0, e23, e4, e6] at hout
    rw [e5, e23, e4, e6] at hsl
    rw [e1, e23, e4, e6] at hnx
    have hT := hb.trans hc
    have hmid2 : Mid m0 m2 := Mid.chg hn hw.mid hfr2
      (regs_kept (matchM hn hw.mid.fr) hm1 (by decide) hcs) hT (by decide) (by decide)
    rw [show k + NativeRustcVmArm.Vm.VerifyKeccak.b55Offset + b55.length = k + NativeRustcVmArm.Vm.VerifyKeccak.b56Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyKeccak.b55_next]]
    refine failBranch hp hn (b56_in_code.trans hp.1 (by simp [b56])) run_b56 hmid2 rfl rfl
      (by decide) (by decide)
      (b := ((sumcheckPlain cj.value 3 4).run s1 |>.map (·.1.2)).isSome)
      (cond8 (o := 3240) (r := (sumcheckPlain cj.value 3 4).run s1 |>.map (·.1.2)) hout)
      (fun hf ↦ ?_) fun ht m3 hmid3 hd3 hcs3 ↦ ?_
    · cases hr : (sumcheckPlain cj.value 3 4).run s1 with
      | none => rw [hw.run, restSum_none hr]
      | some _ => rw [hr] at hf; cases hf
    · obtain ⟨⟨⟨low, v⟩, s2⟩, hr⟩ : ∃ q, (sumcheckPlain cj.value 3 4).run s1 = some q := by
        cases hq : (sumcheckPlain cj.value 3 4).run s1 with
        | none => rw [hq] at ht; cases ht
        | some q => exact ⟨q, rfl⟩
      rw [hr] at hout
      have hlow : low.size = 4 := by
        have h1 := hr
        rw [← NativeRustcVm.Sumcheck.sumcheckFn_none] at h1
        exact Bus.Gkr.sumcheckFn_size _ _ _ _ h1
      rw [show k + NativeRustcVmArm.Vm.VerifyKeccak.b56Offset + b56.length = k + NativeRustcVmArm.Vm.VerifyKeccak.b57Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyKeccak.b56_next]]
      refine cont m3 s2 low v ⟨hmid3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hw.psz, hlow, ?_, ?_,
        by rw [hw.run, restSum_some hr]⟩ <;> rw [hd3]
      · exact hT.word hn (by decide) (by decide) (by decide) hw.w40
      · exact hT.word hn (by decide) (by decide) (by decide) hw.w64
      · exact hT.word hn (by decide) (by decide) (by decide) hw.w72
      · exact hnx (low, v) s2 hr
      · exact hT.cls hn (by decide) (by decide) (by decide) hw.cls
      · exact hT.claim hn (by decide) (by decide) (by decide) hw.claim
      · exact hT.wts hn (by decide) (by decide) (by decide) (by decide) hw.wts
      · exact hsl low v s2 hr
      · exact hout

end

end NativeRustcVmArm.KeccakGkr.VerifyKeccak
