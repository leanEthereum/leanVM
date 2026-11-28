module

public import NativeRustcVmArm.Code.Vm.KeccakOpen.Names
public import NativeRustcVmArm.KeccakGkr.VerifyKeccak.OAreas

/-!
# `verify_keccak`: the opening of the committed outputs

`b40`: `keccak_open(frame + 2592, t, logSteps, first.point, scratch.first_weights, 1, 1,
committed, frame + 2496, scratch.rows)`; `b41`: its tag. At `b42` (`AtO`): the slot point at
2496, the rows at the scratch's `rows`, the value's `Option<EW>` at 2592.
-/

namespace NativeRustcVmArm.KeccakGkr.VerifyKeccak

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVmArm.Ring
open NativeRustcVm.Transcript NativeRustcVmArm.Vm.VerifyKeccak
open NativeRustcVm.KeccakGkr (ClaimAt WeightsAt)
open LeanVM.Protocol.Verifier (keccakDepth)

@[expose] public section

/-- **After the first opening** (`b42`). -/
structure AtO [Labels] (a : DecArea) (s : TState) (cs : Array ColumnClaimW)
    (inst output : Array EW) (m0 m : MachineData) (s' : TState) (cj : KeccakClaimW)
    (sl ws : Array EW) (v : EW) : Prop where
  mid : Mid m0 m
  x28 : (m.regs.getXReg .X28).toBitVec = scA m0 + BitVec.ofNat 64 139264
  w40 : NativeRustcVm.WordAt m.dmem (loc m0 40) (UInt64.ofBitVec (loc m0 1248))
  w64 : NativeRustcVm.WordAt m.dmem (loc m0 64) (UInt64.ofBitVec (scA m0 + BitVec.ofNat 64 140288))
  w72 : NativeRustcVm.WordAt m.dmem (loc m0 72) m0.regs.X7
  ts : TStateAt m.dmem (tA m0) a s'
  cls : NativeRustcVm.Layout.ClaimsWAt m.dmem (clA m0) cs
  claim : ClaimAt m.dmem (loc m0 960) cj
  wts : WeightsAt m.dmem (scA m0 + BitVec.ofNat 64 25600) cj
  psz : cj.point.size = inst.size - 4 + 1
  slsz : sl.size = 6
  slot : NativeRustcVm.EWsAt m.dmem (loc m0 2496) sl.toList
  wsz : ws.size = 64
  rows : NativeRustcVm.EWsAt m.dmem (scA m0 + BitVec.ofNat 64 140288) ws.toList
  val : OptEWAt m.dmem (loc m0 2592) (some v)
  run : run0 s inst output m0 = (afterOpen1 m0.regs.X1.toNat inst cj sl ws v).run s'

end

public section

variable [Host] {k : Nat} {a : DecArea} {s : TState} {cs : Array ColumnClaimW}
  {inst output : Array EW} {m0 : MachineData}

omit [Host] in
theorem run_layers_end [Labels] {m : MachineData} {sj : TState} {cj first : KeccakClaimW} {c : EW}
    (hl : AtL a s cs inst output m0 m 12 sj cj first c) :
    run0 s inst output m0 = (restOpen m0.regs.X1.toNat inst first c cj).run sj := by
  rw [hl.run, show (12 : Nat) = keccakDepth from rfl, layersFrom_end, pure_bind]

/-- **The first opening** (`b40`, `b41`). -/
theorem stepOpen1 (hp : Placed code k) (h : P0 a s cs inst output m0) (hn : Nums a inst m0)
    (hko : ∀ a s c, Spec (Labels.label NativeRustcVmArm.Vm.KeccakOpen.entryLabel) (KeccakOpenPre a s c)
      (KeccakOpenPost a s c))
    {m : MachineData} {sj : TState} {cj first : KeccakClaimW} {c : EW}
    (hl : AtL a s cs inst output m0 m 12 sj cj first c)
    (cont : ∀ m' s' sl ws v, AtO a s cs inst output m0 m' s' cj sl ws v →
      Eventually (step1 Host.exe) (Goal a s cs inst output m0) ⟨m', Host.addrOf (k + NativeRustcVmArm.Vm.VerifyKeccak.b42Offset)⟩) :
    Eventually (step1 Host.exe) (Goal a s cs inst output m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyKeccak.b40Offset)⟩ := by
  have hwf := envM_wf hn hl.sl.mid.fr
  have hN := hn.hN
  have hSP := m0.regs.SP.toNat_lt
  have hfsz := hl.sl.fsz
  have h22 : (m.regs.getXReg .X22).toBitVec = scA m0 := congrArg UInt64.toBitVec hl.sl.mid.regs.x22
  refine callC hn (b40_in_code.trans hp.1 (by simp [b40])) run_b40 hl.sl.mid.fr
    (matchM hn hl.sl.mid.fr) hwf rfl (Lb := [(0, 32), (40, 48), (64, 72), (2496, 2592)])
    (L := [(2496, 2592), (2592, 2616)]) (O := [(0, 0, 760), (1, 140288, 205824)])
    (lo := 2496) (n := 120) (by decide) (by decide) (by decide) (by decide) (by decide)
    (hko a sj first) (fun st hm1 hfr1 ↦ ?_) (fun st m' hm1 hfr1 hq ↦ ?_)
    fun st m2 hm1 hfr1 hq hfr2 hcs hb hc hkt ↦ ?_
  all_goals
    have hb0 : Chg m0 [(0, 32), (40, 48), (64, 72), (2496, 2592)] [] m.dmem st.dmem :=
      Chg.block hn hm1 hwf (by decide)
    have e0 : st.regs.X0.toBitVec = loc m0 2592 := reg_loc hm1 (r := .X0) (o := 2592) rfl
    have e1 : st.regs.X1 = m0.regs.X0 :=
      (reg_of hm1 (r := .X1) (v := .reg .X20) rfl rfl).trans hl.sl.mid.regs.x20
    have e2 : st.regs.X2 = m0.regs.X1 :=
      (reg_of hm1 (r := .X2) (v := .reg .X21) rfl rfl).trans hl.sl.mid.regs.x21
    have e5 : st.regs.X5 = m0.regs.X5 :=
      (reg_of hm1 (r := .X5) (v := .reg .X22) rfl rfl).trans hl.sl.mid.regs.x22
    have l64 : (Sym.load 0 64 8).eval (envM m0 m) = first.point.size.toUInt64.toBitVec :=
      Sumcheck.load_word hl.sl.w64
    have e3 : st.regs.X3.toBitVec = loc m0 480 := by
      rw [show st.regs.X3 = st.regs.getXReg .X3 from rfl, hm1.regs .X3 _ rfl,
        eval_ite_lt (by decide) (by rw [l64, u64_toNat (by omega)]; omega)]
      exact Sumcheck.load_word hl.sl.w48
    have e4 : st.regs.X4.toNat = first.point.size := by
      rw [← UInt64.toNat_toBitVec, show st.regs.X4 = st.regs.getXReg .X4 from rfl,
        hm1.regs .X4 _ rfl, eval_ite_lt (by decide) (by rw [l64, u64_toNat (by omega)]; omega),
        l64, u64_toNat (by omega)]
    have e6 : st.regs.X6.toNat = 1 := by
      rw [show st.regs.X6 = st.regs.getXReg .X6 from rfl, reg_of hm1 (r := .X6) (v := .lit 1)
        rfl (w := 1) rfl]; rfl
    have e7 : st.regs.X7.toNat = 1 := by
      rw [show st.regs.X7 = st.regs.getXReg .X7 from rfl, reg_of hm1 (r := .X7) (v := .lit 1)
        rfl (w := 1) rfl]; rfl
    have hsp : st.regs.SP.toBitVec = fb m0 := hfr1.sp
    have hval : openValue st = c := openValue_eq hsp
      (wordOf_loc hm1 (o := 0) (v := .load 0 80 8) (by decide) (by decide)
        (Sumcheck.load_word hl.sl.w80))
      (wordOf_loc hm1 (o := 8) (v := .load 0 56 8) (by decide) (by decide)
        (Sumcheck.load_word hl.sl.w56))
    have hslot : openSlot st = loc m0 2496 := openSlot_eq hsp
      (wordOf_loc hm1 (o := 16) (v := .ptr 0 2496) (by decide) (by decide) eval_ptr0)
    have hrows : openRows st = scA m0 + BitVec.ofNat 64 140288 := openRows_eq hsp
      (wordOf_loc hm1 (o := 24) (v := .bin .add .W64 (.reg .X22) (.lit 140288)) (by decide)
        (by decide) (eval_add_reg h22))
  · have hfb : st.regs.SP.toBitVec = loc m0 0 := by rw [hsp]; simp
    refine ⟨stackOk_of hn hfr1 (by decide), rcAt_of h hn hfr1 (by decide), ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_⟩
    · rw [e1]; exact hb0.ts hn (hm1.kept hwf) (by decide) (by decide) (by decide) hl.ts
    · rw [e4]
    · rw [e3]
      exact hb0.ews hn (by decide) (o := 480) (k := 480) (by decide) (by decide)
        (by rw [Array.length_toList]; omega) hl.sl.fpt
    · have := hb0.wts hn (by decide) (by decide) (o := 0) (by decide) (by decide) hl.sl.fw
      rw [NativeRustcVm.addr_add_zero] at this
      rw [e5]; exact this
    · have := h.n1; have := hl.hfirst
      unfold SegmentsFit; rw [e2]; omega
    · rw [e7]
    · rw [e6, e7]; decide
    · rw [e0, e1, e3, e5, hslot, hrows, hfb]
      show Areas st keccakOpenStack [⟨loc m0 2592, 24⟩, ⟨tA m0, _⟩, _, _]
        [a.region, ewsRegion (loc m0 480) first.point.size, ⟨scA m0, _⟩, rcRegion, ⟨loc m0 0, 32⟩]
      simp only [ewsRegion, NativeVm.Math.Keccak.qkeccakSlotBits_eq]
      exact open_areas h hn hfr1 (by decide) (by decide) (by omega) (by decide)
        (NativeRustcVm.addr_add_zero _).symm
  · obtain ⟨-, -, hs, hsv⟩ := hq
    refine ⟨NativeRustcVm.SameOutside.mono hs fun q ⟨r, hr, hq⟩ ↦ ?_, hsv⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ws_stk hn hfr1 (by decide) hq
    · rw [e0] at hq
      exact ws_loc hn (o := 2592) (n := 24) (by decide) (by decide) hq
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
    have hregs : ∀ r ∈ regsL, m2.regs.getXReg r = m.regs.getXReg r :=
      regs_kept (matchM hn hl.sl.mid.fr) hm1 (by decide) hcs
    have hmid2 : Mid m0 m2 := Mid.chg hn hl.sl.mid hfr2 hregs (hb.trans hc) (by decide) (by decide)
    have hT := hb.trans hc
    have w40 : NativeRustcVm.WordAt st.dmem (loc m0 40) (UInt64.ofBitVec (loc m0 1248)) := by
      have := Sumcheck.Match.wordAt_write hm1 (r := 0) (o := 40) (v := .reg .X19) rfl (by decide)
        (by decide)
      simp only [Sym.eval, Env.ofMachine_regs, hl.sl.x19] at this; exact this
    have w64 : NativeRustcVm.WordAt st.dmem (loc m0 64)
        (UInt64.ofBitVec (scA m0 + BitVec.ofNat 64 140288)) := by
      have := Sumcheck.Match.wordAt_write hm1 (r := 0) (o := 64)
        (v := .bin .add .W64 (.reg .X22) (.lit 140288)) rfl (by decide) (by decide)
      rw [eval_add_reg h22] at this; exact this
    have x28 : (m2.regs.getXReg .X28).toBitVec = scA m0 + BitVec.ofNat 64 139264 := by
      rw [hcs .X28 rfl]; exact reg_add hm1 (x := .X28) (y := .X22) rfl h22
    refine failBranch hp hn (b41_in_code.trans hp.1 (by simp [b41])) run_b41 hmid2 rfl rfl
      (by decide) (by decide)
      (b := ((keccakOpen m0.regs.X1.toNat first 1 1 c).run sj |>.map (·.1.2.2)).isSome)
      (cond8 (o := 2592) (r := (keccakOpen m0.regs.X1.toNat first 1 1 c).run sj |>.map (·.1.2.2))
        hout) (fun hf ↦ ?_) fun ht m3 hmid3 hd3 hcs3 ↦ ?_
    · cases hr : (keccakOpen m0.regs.X1.toNat first 1 1 c).run sj with
      | none => rw [run_layers_end hl, restOpen_none hr]
      | some _ => rw [hr] at hf; cases hf
    · obtain ⟨⟨⟨sl, ws, v⟩, s'⟩, hr⟩ :
          ∃ q, (keccakOpen m0.regs.X1.toNat first 1 1 c).run sj = some q := by
        cases hq : (keccakOpen m0.regs.X1.toNat first 1 1 c).run sj with
        | none => rw [hq] at ht; cases ht
        | some q => exact ⟨q, rfl⟩
      obtain ⟨hslv, hrowv, hts'⟩ := hsome sl ws v s' hr
      rw [hr] at hout
      obtain ⟨hsl6, hws64⟩ := open_weights_size hr
      rw [show k + NativeRustcVmArm.Vm.VerifyKeccak.b40Offset + b40.length + b41.length = k + NativeRustcVmArm.Vm.VerifyKeccak.b42Offset from by
        rw [← b41_next, ← b40_next]
        simp only [Nat.add_assoc]]
      refine cont m3 s' sl ws v ⟨hmid3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hl.psz.trans hl.hfirst,
        hsl6, ?_, hws64, ?_, ?_, ?_⟩
      · rw [hcs3 .X28 rfl]; exact x28
      · rw [hd3]; exact hc.word hn (by decide) (by decide) (by decide) w40
      · rw [hd3]; exact hc.word hn (by decide) (by decide) (by decide) w64
      · rw [hd3]; exact hT.word hn (by decide) (by decide) (by decide) hl.sl.w72
      · rw [hd3]; exact hts'
      · rw [hd3]; exact hT.cls hn (by decide) (by decide) (by decide) hl.sl.cls
      · rw [hd3]; exact hT.claim hn (by decide) (o := 960) (by decide) (by decide) hl.claim
      · rw [hd3]
        exact hT.wts hn (by decide) (by decide) (o := 25600) (by decide) (by decide) hl.wts
      · rw [hd3]; exact hslv
      · rw [hd3]; exact hrowv
      · rw [hd3]; exact hout
      · rw [run_layers_end hl, restOpen_some hr]

end

end NativeRustcVmArm.KeccakGkr.VerifyKeccak
