module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.KeccakGkr.VerifyKeccak.Read1

/-!
# `verify_keccak`: the committed outputs' check

`b44` (from `rowS`, region 1 the scratch from byte `139264`): `EW::mul(rows[0][0], word)`, the
word's limbs into X28 and the frame's word at 80; `b45`, `b46`: the product against the opening's
value, limb by limb. At `b47`: `AtW`.
-/

namespace NativeRustcVmArm.KeccakGkr.VerifyKeccak

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVmArm.Ring
open NativeRustcVm.Transcript NativeRustcVmArm.Vm.VerifyKeccak
open NativeRustcVm.KeccakGkr (ClaimAt WeightsAt)

public section

/-- The registers the checks keep. -/
@[expose] def chkL : List XReg :=
  [.X0, .X1, .X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29]

variable [Host] {k : Nat} {a : DecArea} {s : TState} {cs : Array ColumnClaimW}
  {inst output : Array EW} {m0 : MachineData}

/-- The environment of `b44`: the frame and the scratch from byte `139264`. -/
abbrev envR (m0 m : MachineData) : Env :=
  Env.ofMachine m [(fb m0, 3360), (scA m0 + BitVec.ofNat 64 139264, 1040)]

omit [Host] in
theorem envR_wf [Labels] (h : P0 a s cs inst output m0) (hn : Nums a inst m0) {m : MachineData}
    (hfr : VFr m0 m) : (envR m0 m).WF := by
  have hN := hn.hN
  have hSP := m0.regs.SP.toNat_lt
  have e1 := scN hn (o := 139264) (by decide)
  have hfm : Mapped m.dmem (fb m0) 3360 :=
    fun i hi ↦ hfr.kept _ (frame_mapped hn.stk (by decide) i hi)
  refine Env.wf_of ⟨⟨hfm, base_noWrap (by omega)⟩, ⟨mapped_of (ok_sc h) hfr (o := 139264)
      (k := 1040) (by decide), by
    unfold NoWrap; rw [e1]; have := hn.sW; omega⟩, trivial⟩
    (List.Pairwise.cons (fun e he ↦ by
      simp only [List.mem_singleton] at he; subst he
      unfold Apart; simp only; rw [fb_toNat hn.hN, e1]
      obtain h1 | h1 := hn.sS <;> omega) (List.pairwise_singleton _ _))

omit [Host] in
theorem matchR [Labels] {m : MachineData} (hfr : VFr m0 m) (hn : Nums a inst m0)
    (hx : (m.regs.getXReg .X28).toBitVec = scA m0 + BitVec.ofNat 64 139264) :
    Match (envR m0 m) rowS m :=
  match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hn.stk (by decide) (by decide),
      ⟨rfl, ⟨fun h ↦ absurd h (by decide), trivial⟩⟩⟩
    (by rw [hfr.sp]; simp [Sym.eval])
    ⟨by
      show (m.regs.getXReg .X28).toBitVec = scA m0 + BitVec.ofNat 64 139264 + BitVec.ofInt 64 0
      rw [show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero, hx], trivial⟩
    trivial trivial trivial

/-- **The committed outputs' check** (`b44` to `b46`). -/
theorem stepWord (hp : Placed code k) (h : P0 a s cs inst output m0) (hn : Nums a inst m0)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {m : MachineData} {s1 : TState} {cj : KeccakClaimW} {sl ws : Array EW} {v w : EW}
    (hr : AtR a s cs inst output m0 m s1 cj sl ws v w)
    (cont : ∀ m', AtW a s cs inst output m0 m' s1 cj sl w →
      Eventually (step1 Host.exe) (Goal a s cs inst output m0) ⟨m', Host.addrOf (k + NativeRustcVmArm.Vm.VerifyKeccak.b47Offset)⟩) :
    Eventually (step1 Host.exe) (Goal a s cs inst output m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyKeccak.b44Offset)⟩ := by
  have hwf := envR_wf h hn hr.mid.fr
  have hm0 := matchR hr.mid.fr hn hr.x28
  have ew := hr.word.2
  rw [show off (loc m0 2592) 8 = loc m0 2600 from loc_add m0 2592 8] at ew
  have ec := load_ew (env := envR m0 m) (r := 0) (o := 2600) ew
  have er := ewsAt_getD hr.rows (i := 0) (by rw [hr.wsz]; decide)
  rw [show scA m0 + BitVec.ofNat 64 140288 + BitVec.ofNat 64 (16 * 0) =
    scA m0 + BitVec.ofNat 64 139264 + BitVec.ofNat 64 1024 by
      rw [NativeRustcVm.addr_add_add, NativeRustcVm.addr_add_add]] at er
  have ex := load_ew (env := envR m0 m) (r := 1) (o := 1024) er
  refine callC hn (b44_in_code.trans hp.1 (by simp [b44])) run_b44 hr.mid.fr hm0 hwf rfl
    (Lb := [(80, 88)]) (L := []) (O := []) (lo := 0) (n := 0) (by decide) (by decide) (by decide)
    (by decide) (by decide) hmul (fun st hm1 hfr1 ↦ stackOk_of hn hfr1 (by decide))
    (fun st m' hm1 hfr1 hq ↦ ?_) fun st m2 hm1 hfr1 hq hfr2 hcs hb hc hkt ↦ ?_
  · obtain ⟨-, -, hs, hsv⟩ := hq
    exact ⟨NativeRustcVm.SameOutside.mono hs fun q hq ↦ ws_stk hn hfr1 (by decide) hq, hsv⟩
  obtain ⟨hx0, hx1, -, -⟩ := hq
  have e0 : st.regs.X0 = (ws.getD 0 0).c0 := reg_of hm1 (r := .X0) (v := .load 1 1024 8) rfl ex.1
  have e1 : st.regs.X1 = (ws.getD 0 0).c1 := reg_of hm1 (r := .X1) (v := .load 1 1032 8) rfl ex.2
  have e2 : st.regs.X2 = w.c0 := reg_of hm1 (r := .X2) (v := .load 0 2600 8) rfl ec.1
  have e3 : st.regs.X3 = w.c1 := reg_of hm1 (r := .X3) (v := .load 0 2608 8) rfl ec.2
  rw [e0, e1, e2, e3] at hx0 hx1
  have hprod : (EW.mul ⟨(ws.getD 0 0).c0, (ws.getD 0 0).c1⟩ ⟨w.c0, w.c1⟩) = ws.getD 0 0 * w := rfl
  rw [hprod] at hx0 hx1
  have hregs : ∀ r ∈ regsL, m2.regs.getXReg r = m.regs.getXReg r :=
    regs_kept hm0 hm1 (by decide) hcs
  have hT := hb.trans hc
  have hmid2 : Mid m0 m2 := Mid.chg hn hr.mid hfr2 hregs hT (by decide) (by decide)
  have x29 : m2.regs.getXReg .X29 = v.c0 := by
    rw [hcs .X29 rfl, Match.reg_eq hm0 hm1 (r := .X29) rfl rfl]; exact hr.x29
  have x19 : m2.regs.getXReg .X19 = v.c1 := by
    rw [hcs .X19 rfl, Match.reg_eq hm0 hm1 (r := .X19) rfl rfl]; exact hr.x19
  have x28 : m2.regs.getXReg .X28 = w.c0 := by
    rw [hcs .X28 rfl]; exact reg_of hm1 (r := .X28) (v := .load 0 2600 8) rfl ec.1
  have w80 : NativeRustcVm.WordAt st.dmem (loc m0 80) w.c1 := by
    have := Sumcheck.Match.wordAt_write hm1 (r := 0) (o := 80) (v := .load 0 2608 8) rfl
      (by decide) (by decide)
    simp only [Sym.eval, ec.2] at this; exact this
  rw [show k + NativeRustcVmArm.Vm.VerifyKeccak.b44Offset + b44.length = k + NativeRustcVmArm.Vm.VerifyKeccak.b45Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyKeccak.b44_next]]
  -- `b45`
  refine failBranchF hp hn (b45_in_code.trans hp.1 (by simp [b45])) run_b45 hfr2 rfl rfl
    (L := chkL) (by decide) (b := ((ws.getD 0 0 * w).c0 == v.c0))
    (by rw [condNe, Env.ofMachine_regs, Env.ofMachine_regs, bv_beq, x29, gx0, hx0])
    (fun hf ↦ by rw [hr.run, afterWord_false (ew_beq_c0 (by simpa using hf))])
    fun ht0 m3 hfr3 hd3 hk3 ↦ ?_
  have g : ∀ r ∈ chkL, m3.regs.getXReg r = m2.regs.getXReg r := hk3
  simp only [chkL, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at g
  obtain ⟨g0, g1, g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, g29⟩ := g
  rw [show k + NativeRustcVmArm.Vm.VerifyKeccak.b45Offset + b45.length = k + NativeRustcVmArm.Vm.VerifyKeccak.b46Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyKeccak.b45_next]]
  -- `b46`
  refine failBranchF hp hn (b46_in_code.trans hp.1 (by simp [b46])) run_b46 hfr3 rfl rfl
    (L := chkL) (by decide) (b := ((ws.getD 0 0 * w).c1 == v.c1))
    (by rw [condNe, Env.ofMachine_regs, Env.ofMachine_regs, bv_beq, g1, g19, x19, gx1, hx1])
    (fun hf ↦ by rw [hr.run, afterWord_false (ew_beq_c1 (by simpa using hf))])
    fun ht1 m4 hfr4 hd4 hk4 ↦ ?_
  have g' : ∀ r ∈ chkL, m4.regs.getXReg r = m3.regs.getXReg r := hk4
  simp only [chkL, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at g'
  obtain ⟨-, -, -, h20, h21, h22, h23, h24, h25, h26, h27, h28, -⟩ := g'
  have hd : m4.dmem = m2.dmem := hd4.trans hd3
  rw [show k + NativeRustcVmArm.Vm.VerifyKeccak.b46Offset + b46.length = k + NativeRustcVmArm.Vm.VerifyKeccak.b47Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyKeccak.b46_next]]
  refine cont m4 ⟨Mid.of_dmem hmid2 hfr4 hd fun r hr' ↦ ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hr.psz, hr.slsz, ?_, ?_⟩
  · simp only [regsL, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h20.trans g20
    · exact h21.trans g21
    · exact h22.trans g22
    · exact h23.trans g23
    · exact h24.trans g24
    · exact h25.trans g25
    · exact h26.trans g26
    · exact h27.trans g27
  · rw [h28, g28]; exact x28
  · rw [hd]; exact hc.word hn (by decide) (by decide) (by decide) w80
  · rw [hd]; exact hT.word hn (by decide) (by decide) (by decide) hr.w40
  · rw [hd]; exact hT.word hn (by decide) (by decide) (by decide) hr.w64
  · rw [hd]; exact hT.word hn (by decide) (by decide) (by decide) hr.w72
  · rw [hd]; exact hT.ts hn hkt (by decide) (by decide) (by decide) hr.ts
  · rw [hd]; exact hT.cls hn (by decide) (by decide) (by decide) hr.cls
  · rw [hd]; exact hT.claim hn (by decide) (by decide) (by decide) hr.claim
  · rw [hd]; exact hT.wts hn (by decide) (by decide) (by decide) (by decide) hr.wts
  · rw [hd]
    exact hT.ews hn (by decide) (o := 2496) (k := 96) (by decide) (by decide)
      (by simp [Array.length_toList, hr.slsz]) hr.slot
  · rw [hr.run, afterWord_true (ew_beq_true (by simpa using ht0) (by simpa using ht1))]

end

end NativeRustcVmArm.KeccakGkr.VerifyKeccak
