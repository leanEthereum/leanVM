module

public import NativeRustcVmArm.Code.Vm.TStateReadScalars.Names
public import NativeRustcVmArm.KeccakGkr.VerifyKeccak.Open2
public import NativeRustcVm.Sumcheck.RoundPoly

/-!
# `verify_keccak`: the slices

`b59`: the second opening's value into X22, X21; `read_scalars(t, out.slices, 64)`; `b60`: its
verdict. At `b61` (`AtY`): the slices at the `KeccakOutW`'s.
-/

namespace NativeRustcVmArm.KeccakGkr.VerifyKeccak

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVmArm.Ring
open NativeRustcVm.Transcript NativeRustcVmArm.Vm.VerifyKeccak
open NativeRustcVm.KeccakGkr (ClaimAt WeightsAt)

@[expose] public section

/-- **After the slices** (`b61`). -/
structure AtY [Labels] (a : DecArea) (s : TState) (cs : Array ColumnClaimW)
    (inst output : Array EW) (m0 m : MachineData) (s' s3 : TState) (cj : KeccakClaimW)
    (outs : Array ColumnClaimW) (low sl ws : Array EW) (v : EW) (xs : Array EW) : Prop where
  fr : VFr m0 m
  x21 : m.regs.getXReg .X21 = v.c1
  x22 : m.regs.getXReg .X22 = v.c0
  x23 : (m.regs.getXReg .X23).toBitVec = loc m0 1248
  x24 : (m.regs.getXReg .X24).toNat = cj.point.size
  w64 : NativeRustcVm.WordAt m.dmem (loc m0 64) (UInt64.ofBitVec (scA m0 + BitVec.ofNat 64 140288))
  w72 : NativeRustcVm.WordAt m.dmem (loc m0 72) m0.regs.X7
  pk : NativeRustcVm.WordAt m.dmem (loc m0 88) (packW m0)
  ts : TStateAt m.dmem (tA m0) a s3
  cls : NativeRustcVm.Layout.ClaimsWAt m.dmem (clA m0) (cs ++ outs)
  claim : ClaimAt m.dmem (loc m0 960) cj
  psz : cj.point.size = inst.size - 4 + 1
  lowsz : low.size = 4
  lowv : NativeRustcVm.EWsAt m.dmem (loc m0 3176) low.toList
  slsz : sl.size = 6
  slot : NativeRustcVm.EWsAt m.dmem (loc m0 2496) sl.toList
  wsz : ws.size = 64
  rows : NativeRustcVm.EWsAt m.dmem (scA m0 + BitVec.ofNat 64 140288) ws.toList
  xsz : xs.size = 64
  slices : NativeRustcVm.EWsAt m.dmem (oA m0 + BitVec.ofNat 64 584) xs.toList
  rs : (readScalars 64).run s' = some (xs, s3)
  run : run0 s inst output m0 = (afterOpen2 m0.regs.X1.toNat cj outs low sl ws v).run s'

/-- The registers `b60` keeps. -/
def f1L : List XReg := [.X21, .X22, .X23, .X24]

end

public section

variable [Host] {k : Nat} {a : DecArea} {s : TState} {cs : Array ColumnClaimW}
  {inst output : Array EW} {m0 : MachineData}

/-- **The slices** (`b59`, `b60`). -/
theorem stepFin1 (hp : Placed code k) (h : P0 a s cs inst output m0) (hn : Nums a inst m0)
    (hrss : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.TStateReadScalars.entryLabel) (ReadScalarsPre a s)
      (ReadScalarsPost a s))
    {m : MachineData} {s1 : TState} {cj : KeccakClaimW} {outs : Array ColumnClaimW}
    {low sl ws : Array EW} {v : EW} (hv : AtV a s cs inst output m0 m s1 cj outs low sl ws v)
    (cont : ∀ m' s3 xs, AtY a s cs inst output m0 m' s1 s3 cj outs low sl ws v xs →
      Eventually (step1 Host.exe) (Goal a s cs inst output m0) ⟨m', Host.addrOf (k + NativeRustcVmArm.Vm.VerifyKeccak.b61Offset)⟩) :
    Eventually (step1 Host.exe) (Goal a s cs inst output m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyKeccak.b59Offset)⟩ := by
  have hwf := envM_wf hn hv.fr
  have hN := hn.hN
  have ev := hv.val.2
  rw [show off (loc m0 3240) 8 = loc m0 3248 from loc_add m0 3240 8] at ev
  have ec := load_ew (env := envM m0 m) (r := 0) (o := 3248) ev
  have h7 : (envM m0 m).load 0 72 8 = oA m0 := Sumcheck.load_word hv.w72
  have hrsS : readScalarsStack = 608 := rfl
  refine callC hn (b59_in_code.trans hp.1 (by simp [b59])) run_b59 hv.fr (matchM hn hv.fr) hwf rfl
    (Lb := []) (L := []) (O := [(3, 584, 1608), (0, 0, 760)]) (lo := 0) (n := 0) (by decide)
    (by decide) (by decide) (by decide) (by decide) (hrss a s1) (fun st hm1 hfr1 ↦ ?_)
    (fun st m' hm1 hfr1 hq ↦ ?_) fun st m2 hm1 hfr1 hq hfr2 hcs hb hc hkt ↦ ?_
  all_goals
    have hd : st.dmem = m.dmem := hm1.dmem_eq hwf rfl
    have e0 : st.regs.X0 = m0.regs.X0 := (reg_of hm1 (r := .X0)
        (v := .reg .X20) rfl rfl).trans hv.x20
    have e1 : st.regs.X1.toBitVec = oA m0 + BitVec.ofNat 64 584 := by
      rw [show st.regs.X1 = st.regs.getXReg .X1 from rfl, hm1.regs .X1 _ rfl]
      simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, h7]
    have e2 : st.regs.X2.toNat = 64 := by
      rw [show st.regs.X2 = (64 : UInt64) from reg_of hm1 (r := .X2) (v := .lit 64) rfl rfl]; rfl
  · refine ⟨stackOk_of hn hfr1 (by decide), rcAt_of h hn hfr1 (by decide), ?_, ?_, ?_⟩
    · rw [e0, hd]; exact hv.ts
    · rw [e0]; exact tok_of hn hfr1 (by decide)
    · rw [e0, e1, e2]
      have hoN := oN hn (o := 584) (by decide)
      have htxo : m0.regs.X0.toBitVec.toNat + 760 ≤ (oA m0).toNat ∨
          (oA m0).toNat + 1608 ≤ m0.regs.X0.toBitVec.toNat := hn.txo
      refine ⟨mapped_of (ok_out h) hfr1 (by decide), ?_, ?_, ?_, ?_, ?_⟩ <;>
        (try unfold NoWrap) <;> (try unfold Apart) <;> (try rw [sb_toNat hn.hN hfr1
            (by decide)]) <;> rw [hoN]
      · have := hn.oW; omega
      · obtain h1 | h1 := htxo <;> simp only [tstateBytes] <;> omega
      · obtain h1 | h1 := hn.o_w <;> omega
      · obtain h1 | h1 := hn.oS <;> omega
      · obtain h1 | h1 := hn.o_rc <;> omega
  · obtain ⟨-, -, -, hs, hsv⟩ := hq
    refine ⟨NativeRustcVm.SameOutside.mono hs fun q hq ↦ ?_, hsv⟩
    rw [e1, e2, e0] at hq
    rcases hq with hq | hq | hq
    · exact ws_ob hn (i := 3) (o := 584) (n := 1024) (by decide) (by decide) (by decide)
        (by decide) hq
    · exact ws_ob0 hn (i := 0) (n := 760) (by decide) (by decide) (by decide) (by decide) hq
    · exact ws_stk hn hfr1 (by decide) hq
  · obtain ⟨hx, hxs, hnx, -, -⟩ := hq
    rw [e2] at hx hxs hnx
    rw [e1] at hxs
    rw [e0] at hnx
    have hT := hb.trans hc
    have hk : ∀ r ∈ f1L, m2.regs.getXReg r = st.regs.getXReg r := fun r hr ↦ hcs r (by
      simp only [f1L, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> rfl)
    have x21 : m2.regs.getXReg .X21 = v.c1 := by
      rw [hk .X21 (by simp [f1L])]; exact reg_of hm1 (r := .X21) (v := .load 0 3256 8) rfl ec.2
    have x22 : m2.regs.getXReg .X22 = v.c0 := by
      rw [hk .X22 (by simp [f1L])]; exact reg_of hm1 (r := .X22) (v := .load 0 3248 8) rfl ec.1
    have x23 : (m2.regs.getXReg .X23).toBitVec = loc m0 1248 := by
      rw [hk .X23 (by simp [f1L]), Match.reg_eq (matchM hn hv.fr) hm1 (r := .X23) rfl rfl]
      exact hv.x23
    have x24 : (m2.regs.getXReg .X24).toNat = cj.point.size := by
      rw [hk .X24 (by simp [f1L]), Match.reg_eq (matchM hn hv.fr) hm1 (r := .X24) rfl rfl]
      exact hv.x24
    rw [show k + NativeRustcVmArm.Vm.VerifyKeccak.b59Offset + b59.length = k + NativeRustcVmArm.Vm.VerifyKeccak.b60Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyKeccak.b59_next]]
    refine failBranchF hp hn (b60_in_code.trans hp.1 (by simp [b60])) run_b60 hfr2 rfl rfl
      (L := f1L) (by decide) (b := ((readScalars 64).run s1).isSome)
      (condX0 (by rw [Env.ofMachine_regs, gx0, hx])) (fun hf ↦ ?_) fun ht m3 hfr3 hd3 hk3 ↦ ?_
    · cases hr : (readScalars 64).run s1 with
      | none => rw [hv.run, afterOpen2_none hr]
      | some _ => rw [hr] at hf; cases hf
    · obtain ⟨⟨xs, s3⟩, hr⟩ : ∃ q, (readScalars 64).run s1 = some q := by
        cases hq : (readScalars 64).run s1 with
        | none => rw [hq] at ht; cases ht
        | some q => exact ⟨q, rfl⟩
      have hxsz : xs.size = 64 := NativeRustcVm.Sumcheck.readScalars_size hr
      rw [show k + NativeRustcVmArm.Vm.VerifyKeccak.b60Offset + b60.length = k + NativeRustcVmArm.Vm.VerifyKeccak.b61Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyKeccak.b60_next]]
      refine cont m3 s3 xs ⟨hfr3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hv.psz, hv.lowsz, ?_,
        hv.slsz, ?_, hv.wsz, ?_, hxsz, ?_, hr, hv.run⟩
      · rw [hk3 .X21 (by simp [f1L])]; exact x21
      · rw [hk3 .X22 (by simp [f1L])]; exact x22
      · rw [hk3 .X23 (by simp [f1L])]; exact x23
      · rw [hk3 .X24 (by simp [f1L])]; exact x24
      all_goals rw [hd3]
      · exact hT.word hn (by decide) (by decide) (by decide) hv.w64
      · exact hT.word hn (by decide) (by decide) (by decide) hv.w72
      · exact hT.word hn (by decide) (by decide) (by decide) hv.pk
      · exact hnx xs s3 hr
      · exact hT.cls hn (by decide) (by decide) (by decide) hv.cls
      · exact hT.claim hn (by decide) (by decide) (by decide) hv.claim
      · exact hT.ews hn (by decide) (o := 3176) (k := 64) (by decide) (by decide)
          (by simp [Array.length_toList, hv.lowsz]) hv.lowv
      · exact hT.ews hn (by decide) (o := 2496) (k := 96) (by decide) (by decide)
          (by simp [Array.length_toList, hv.slsz]) hv.slot
      · exact hT.ewsOut hn (by decide) (by decide) (i := 1) (o := 140288) (k := 1024)
          (by decide) (by decide) (by decide) (by decide)
          (by simp [Array.length_toList, hv.wsz]) hv.rows
      · exact hxs xs s3 hr

end

end NativeRustcVmArm.KeccakGkr.VerifyKeccak
