module

public import NativeRustcVmArm.Code.Vm.KeccakOpen.Names
public import NativeRustcVmArm.KeccakGkr.VerifyKeccak.Sum

/-!
# `verify_keccak`: the opening of the inputs

`b57`: the claim's point (address and size) into X23, X24; `keccak_open(frame + 3240, t,
logSteps, point, scratch.weights, 0, 2, value, frame + 2496, scratch.rows)`; `b58`: its tag. At
`b59`: `AtV`.
-/

namespace NativeRustcVmArm.KeccakGkr.VerifyKeccak

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVmArm.Ring
open NativeRustcVm.Transcript NativeRustcVmArm.Vm.VerifyKeccak
open NativeRustcVm.KeccakGkr (ClaimAt WeightsAt)

public section

variable [Host] {k : Nat} {a : DecArea} {s : TState} {cs : Array ColumnClaimW}
  {inst output : Array EW} {m0 : MachineData}

/-- The registers `b58` keeps. -/
@[expose] def o2L : List XReg := [.X20, .X23, .X24]

/-- **The second opening** (`b57`, `b58`). -/
theorem stepOpen2 (hp : Placed code k) (h : P0 a s cs inst output m0) (hn : Nums a inst m0)
    (hko : ∀ a s c, Spec (Labels.label NativeRustcVmArm.Vm.KeccakOpen.entryLabel) (KeccakOpenPre a s c)
      (KeccakOpenPost a s c))
    {m : MachineData} {s1 : TState} {cj : KeccakClaimW} {outs : Array ColumnClaimW}
    {low : Array EW} {v : EW} (hu : AtU a s cs inst output m0 m s1 cj outs low v)
    (cont : ∀ m' s' sl ws v', AtV a s cs inst output m0 m' s' cj outs low sl ws v' →
      Eventually (step1 Host.exe) (Goal a s cs inst output m0) ⟨m', Host.addrOf (k + NativeRustcVmArm.Vm.VerifyKeccak.b59Offset)⟩) :
    Eventually (step1 Host.exe) (Goal a s cs inst output m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyKeccak.b57Offset)⟩ := by
  have hwf := envM_wf hn hu.mid.fr
  have hN := hn.hN
  have n30 := h.n30
  have hpsz := hu.psz
  have h22 : (m.regs.getXReg .X22).toBitVec = scA m0 := congrArg UInt64.toBitVec hu.mid.regs.x22
  have ev := hu.val.2
  rw [show off (loc m0 3240) 8 = loc m0 3248 from loc_add m0 3240 8] at ev
  have ec := load_ew (env := envM m0 m) (r := 0) (o := 3248) ev
  have hpw := hu.claim.2.2.2.1
  rw [show NativeRustcVm.KeccakGkr.off (loc m0 960) NativeRustcVm.KeccakGkr.pointOff =
    loc m0 1240 from loc_add m0 960 280] at hpw
  have hpe := hu.claim.2.2.2.2
  rw [show NativeRustcVm.KeccakGkr.off (loc m0 960) NativeRustcVm.KeccakGkr.pointOff + 8#64 =
    loc m0 1248 from (congrArg (· + 8#64) (loc_add m0 960 280)).trans (loc_add m0 1240 8)] at hpe
  have l1240 : (Sym.load 0 1240 8).eval (envM m0 m) =
      cj.point.toList.length.toUInt64.toBitVec := Sumcheck.load_word hpw
  have hlt : ((Sym.load 0 1240 8).eval (envM m0 m)).toNat < 31 := by
    rw [l1240, u64_toNat (by simp; omega)]; simp; omega
  have e3v : (Sym.ite (.cmp .ult .W64 (.load 0 1240 8) (.lit 31)) (.load 0 40 8) (.lit 8)).eval
      (envM m0 m) = loc m0 1248 := by
    rw [eval_ite_lt (by decide) hlt]; exact Sumcheck.load_word hu.w40
  have e4v : ((Sym.ite (.cmp .ult .W64 (.load 0 1240 8) (.lit 31)) (.load 0 1240 8)
      (.lit 0)).eval (envM m0 m)).toNat = cj.point.size := by
    rw [eval_ite_lt (by decide) hlt, l1240, u64_toNat (by simp; omega), Array.length_toList]
  refine callC hn (b57_in_code.trans hp.1 (by simp [b57])) run_b57 hu.mid.fr
    (matchM hn hu.mid.fr) hwf rfl (Lb := [(0, 32)]) (L := [(3240, 3264), (2496, 2592)])
    (O := [(0, 0, 760), (1, 140288, 205824)]) (lo := 2496) (n := 768) (by decide) (by decide)
    (by decide) (by decide) (by decide) (hko a s1 cj) (fun st hm1 hfr1 ↦ ?_)
    (fun st m' hm1 hfr1 hq ↦ ?_) fun st m2 hm1 hfr1 hq hfr2 hcs hb hc hkt ↦ ?_
  all_goals
    have hb0 : Chg m0 [(0, 32)] [] m.dmem st.dmem := Chg.block hn hm1 hwf (by decide)
    have e0 : st.regs.X0.toBitVec = loc m0 3240 := reg_loc hm1 (r := .X0) (o := 3240) rfl
    have e1 : st.regs.X1 = m0.regs.X0 :=
      (reg_of hm1 (r := .X1) (v := .reg .X20) rfl rfl).trans hu.mid.regs.x20
    have e2 : st.regs.X2 = m0.regs.X1 :=
      (reg_of hm1 (r := .X2) (v := .reg .X21) rfl rfl).trans hu.mid.regs.x21
    have e3 : st.regs.X3.toBitVec = loc m0 1248 := by
      rw [show st.regs.X3 = st.regs.getXReg .X3 from rfl, hm1.regs .X3 _ rfl]; exact e3v
    have e4 : st.regs.X4.toNat = cj.point.size := by
      rw [← UInt64.toNat_toBitVec, show st.regs.X4 = st.regs.getXReg .X4 from rfl,
        hm1.regs .X4 _ rfl]; exact e4v
    have e5 : st.regs.X5.toBitVec = scA m0 + BitVec.ofNat 64 25600 :=
      reg_add hm1 (x := .X5) (y := .X22) rfl h22
    have e6 : st.regs.X6.toNat = 0 := by
      rw [show st.regs.X6 = (0 : UInt64) from reg_of hm1 (r := .X6) (v := .lit 0) rfl rfl]; rfl
    have e7 : st.regs.X7.toNat = 2 := by
      rw [show st.regs.X7 = (2 : UInt64) from reg_of hm1 (r := .X7) (v := .lit 2) rfl rfl]; rfl
    have hsp : st.regs.SP.toBitVec = fb m0 := hfr1.sp
    have hval : openValue st = v := openValue_eq hsp
      (wordOf_loc hm1 (o := 0) (v := .load 0 3248 8) (by decide) (by decide) ec.1)
      (wordOf_loc hm1 (o := 8) (v := .load 0 3256 8) (by decide) (by decide) ec.2)
    have hslot : openSlot st = loc m0 2496 := openSlot_eq hsp
      (wordOf_loc hm1 (o := 16) (v := .ptr 0 2496) (by decide) (by decide) eval_ptr0)
    have hrows : openRows st = scA m0 + BitVec.ofNat 64 140288 := openRows_eq hsp
      (wordOf_loc hm1 (o := 24) (v := .load 0 64 8) (by decide) (by decide)
        (Sumcheck.load_word hu.w64))
  · have hfb : st.regs.SP.toBitVec = loc m0 0 := by rw [hsp]; simp
    refine ⟨stackOk_of hn hfr1 (by decide), rcAt_of h hn hfr1 (by decide), ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_⟩
    · rw [e1]; exact hb0.ts hn (hm1.kept hwf) (by decide) (by decide) (by decide) hu.ts
    · rw [e4]
    · rw [e3]
      exact hb0.ews hn (by decide) (o := 1248) (k := 480) (by decide) (by decide)
        (by rw [Array.length_toList]; omega) hpe
    · rw [e5]; exact hb0.wts hn (by decide) (by decide) (by decide) (by decide) hu.wts
    · have := h.n1
      unfold SegmentsFit; rw [e2]; omega
    · rw [e7]; decide
    · rw [e6, e7]; decide
    · rw [e0, e1, e3, e5, hslot, hrows, hfb]
      show Areas st keccakOpenStack [⟨loc m0 3240, 24⟩, ⟨tA m0, _⟩, _, _]
        [a.region, ewsRegion (loc m0 1248) cj.point.size, _, rcRegion, ⟨loc m0 0, 32⟩]
      simp only [ewsRegion, NativeVm.Math.Keccak.qkeccakSlotBits_eq]
      exact open_areas h hn hfr1 (by decide) (by decide) (by omega) (by decide) rfl
  · obtain ⟨-, -, hs, hsv⟩ := hq
    refine ⟨NativeRustcVm.SameOutside.mono hs fun q ⟨r, hr, hq⟩ ↦ ?_, hsv⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ws_stk hn hfr1 (by decide) hq
    · rw [e0] at hq
      exact ws_loc hn (o := 3240) (n := 24) (by decide) (by decide) hq
    · rw [e1] at hq
      exact ws_ob0 hn (i := 0) (n := 760) (by decide) (by decide) (by decide) (by decide) hq
    · rw [hslot] at hq
      simp only [ewsRegion, NativeVm.Math.Keccak.qkeccakSlotBits_eq] at hq
      exact ws_loc hn (o := 2496) (n := 96) (by decide) (by decide) hq
    · rw [hrows] at hq
      exact ws_ob hn (i := 1) (o := 140288) (n := 65536) (by decide) (by decide) (by decide)
        (by decide) hq
  · obtain ⟨hout, hsome, -, -⟩ := hq
    rw [e0, e2, e6, e7, hval] at hout
    rw [e2, e6, e7, hval, hslot, hrows, e1] at hsome
    have hT := hb.trans hc
    have hk : ∀ r ∈ o2L, m2.regs.getXReg r = st.regs.getXReg r := fun r hr ↦ hcs r (by
      simp only [o2L, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> rfl)
    have x20 : m2.regs.getXReg .X20 = m0.regs.X0 := by
      rw [hk .X20 (by simp [o2L]), Match.reg_eq (matchM hn hu.mid.fr) hm1 (r := .X20) rfl rfl]
      exact hu.mid.regs.x20
    have x23 : (m2.regs.getXReg .X23).toBitVec = loc m0 1248 := by
      rw [hk .X23 (by simp [o2L]), hm1.regs .X23 _ rfl]; exact e3v
    have x24 : (m2.regs.getXReg .X24).toNat = cj.point.size := by
      rw [hk .X24 (by simp [o2L]), ← UInt64.toNat_toBitVec, hm1.regs .X24 _ rfl]; exact e4v
    rw [show k + NativeRustcVmArm.Vm.VerifyKeccak.b57Offset + b57.length = k + NativeRustcVmArm.Vm.VerifyKeccak.b58Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyKeccak.b57_next]]
    refine failBranchF hp hn (b58_in_code.trans hp.1 (by simp [b58])) run_b58 hfr2 rfl rfl
      (L := o2L) (by decide)
      (b := ((keccakOpen m0.regs.X1.toNat cj 0 2 v).run s1 |>.map (·.1.2.2)).isSome)
      (cond4 (o := 3240) (r := (keccakOpen m0.regs.X1.toNat cj 0 2 v).run s1 |>.map (·.1.2.2))
        hout) (fun hf ↦ ?_) fun ht m3 hfr3 hd3 hk3 ↦ ?_
    · cases hr : (keccakOpen m0.regs.X1.toNat cj 0 2 v).run s1 with
      | none => rw [hu.run, afterSum_none hr]
      | some _ => rw [hr] at hf; cases hf
    · obtain ⟨⟨⟨sl, ws, v'⟩, s2⟩, hr⟩ :
          ∃ q, (keccakOpen m0.regs.X1.toNat cj 0 2 v).run s1 = some q := by
        cases hq : (keccakOpen m0.regs.X1.toNat cj 0 2 v).run s1 with
        | none => rw [hq] at ht; cases ht
        | some q => exact ⟨q, rfl⟩
      obtain ⟨hslv, hrowv, hts'⟩ := hsome sl ws v' s2 hr
      rw [hr] at hout
      obtain ⟨hsl6, hws64⟩ := open_weights_size hr
      rw [show k + NativeRustcVmArm.Vm.VerifyKeccak.b58Offset + b58.length = k + NativeRustcVmArm.Vm.VerifyKeccak.b59Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyKeccak.b58_next]]
      refine cont m3 s2 sl ws v' ⟨hfr3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hpsz, hu.lowsz, ?_,
        hsl6, ?_, hws64, ?_, ?_, by rw [hu.run, afterSum_some hr]⟩
      · rw [hk3 .X20 (by simp [o2L])]; exact x20
      · rw [hk3 .X23 (by simp [o2L])]; exact x23
      · rw [hk3 .X24 (by simp [o2L])]; exact x24
      all_goals rw [hd3]
      · exact hT.word hn (by decide) (by decide) (by decide) hu.w64
      · exact hT.word hn (by decide) (by decide) (by decide) hu.w72
      · exact hT.word hn (by decide) (by decide) (by decide) hu.mid.pk
      · exact hts'
      · exact hT.cls hn (by decide) (by decide) (by decide) hu.cls
      · exact hT.claim hn (by decide) (by decide) (by decide) hu.claim
      · exact hT.ews hn (by decide) (o := 3176) (k := 64) (by decide) (by decide)
          (by simp [Array.length_toList, hu.lowsz]) hu.lowv
      · exact hslv
      · exact hrowv
      · exact hout

end

end NativeRustcVmArm.KeccakGkr.VerifyKeccak
