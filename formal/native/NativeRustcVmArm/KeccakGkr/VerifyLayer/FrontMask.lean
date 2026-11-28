module

public import NativeRustcVmArm.Code.Vm.VerifyLayer.Names
public import NativeRustcVmArm.KeccakGkr.VerifyLayer.FrontA
public import NativeRustcVmArm.KeccakGkr.VerifyLayer.WeightsA

/-!
# `verify_layer`'s front: the instance weights' masked sum

At `.LVerifyLayer_4` (`b6`, `k + NativeRustcVmArm.Vm.VerifyLayer.b6Offset`) with bit `j` of the projection (`MaskIn`): the sum of the
claim's instance weights whose `RMFE_PROJECT` mask has bit `j` set, two entries a turn (`b9`,
`b10`, `PairI`, `pair_loop`), then the odd one left (`b12`, `b13`, `one_run`); at
`.LVerifyLayer_3` (`b4`, `k + NativeRustcVmArm.Vm.VerifyLayer.b4Offset`) it is in X0, X1 (`masked_run`).
-/

namespace NativeRustcVmArm.KeccakGkr.VerifyLayer

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Ring NativeVm.Model
open NativeRustcVmArm.Vm.VerifyLayer
open NativeRustcVm.Transcript (tstateBytes TStateAt DecArea)
open NativeRustcVm.KeccakGkr (ClaimAt WeightsAt claimBytes)
open NativeRustcVmArm.Bus.Gkr (Fr.runBlock at_pc)

@[expose] public section

/-- The registers the projection's loops keep. -/
abbrev regsL : List XReg := [.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29]

/-- **At the masked sum of bit `j`** (`b6`). -/
structure MaskIn [Labels] (m0 : MachineData) (c : KeccakClaimW) (j : Nat) (st : MachineData) :
    Prop where
  fb : FB m0 st
  lt : j < 47
  x25 : st.regs.X25.toNat = c.mu.size
  x23 : st.regs.X23.toNat = 2 * (c.mu.size / 2)
  x20 : st.regs.X20.toNat = j
  x24 : st.regs.X24.toBitVec = projectAddr
  x26 : st.regs.X26.toBitVec = projectAddr + BitVec.ofNat 64 8
  x19 : st.regs.X19.toBitVec = cA m0 + BitVec.ofNat 64 32
  x27 : st.regs.X27.toNat = 1
  f144 : NativeRustcVm.WordAt st.dmem (loc m0 144) (UInt64.ofBitVec (cA m0 + BitVec.ofNat 64 24))

/-- **The pair loop's head** (`b10`), `i` pairs summed. -/
structure PairI [Labels] (m0 : MachineData) (c : KeccakClaimW) (j i : Nat) (st0 st : MachineData) :
    Prop where
  fb : FB m0 st
  dm : st.dmem = st0.dmem
  keep : Bus.KeepRegs regsL st0 st
  x8 : st.regs.X8.toNat = 2 ^ j
  x15 : st.regs.X15.toNat = 2 * (c.mu.size / 2) - 2 * i
  x14 : st.regs.X14.toBitVec = projectAddr + BitVec.ofNat 64 (8 + 16 * i)
  x13 : st.regs.X13.toBitVec = cA m0 + BitVec.ofNat 64 (40 + 32 * i)
  ev : (⟨st.regs.X9, st.regs.X11⟩ : EW) = xs (fun l ↦ muSel c.mu j (2 * l)) i
  od : (⟨st.regs.X10, st.regs.X12⟩ : EW) = xs (fun l ↦ muSel c.mu j (2 * l + 1)) i
  lt : i < c.mu.size / 2

end

public section

theorem and30 : ∀ n < 32, n &&& 30 = 2 * (n / 2) := by decide

theorem muSel_eq (mu : Array EW) (j l : Nat) (x0 x1 : UInt64)
    (h0 : x0 = (mu.getD l 0).c0) (h1 : x1 = (mu.getD l 0).c1) :
    (⟨if testBitW (rmfeProjectW.getD l 0) j then x0 else 0,
      if testBitW (rmfeProjectW.getD l 0) j then x1 else 0⟩ : EW) = muSel mu j l := by
  unfold muSel sel
  subst h0 h1
  cases testBitW (rmfeProjectW.getD l 0) j <;> rfl

theorem bv_of_toNat {x : BitVec 64} {n : Nat} (h : x.toNat = n) : x = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (h ▸ x.isLt)]

/-- The two regions of a block reading a mask and an entry, as numbers. -/
theorem wf_two [Labels] {m0 : MachineData} {m : MachineData} (pg : PGeo m0) (g : Geo m0)
    (hk : Kept m0.dmem m.dmem) {o n o' n' : Nat} (hn : 0 < n) (hn' : 0 < n') (hon : o + n ≤ 128)
    (hon' : o' + n' ≤ 768) :
    (Env.ofMachine m [(projectAddr + BitVec.ofNat 64 o, n),
      (cA m0 + BitVec.ofNat 64 o', n')]).WF := by
  have := pg.pn; have := pg.pc; have := g.hc
  have e1 : (projectAddr + BitVec.ofNat 64 o).toNat = projectAddr.toNat + o :=
    NativeRustcVm.toNat_add_ofNat (by omega)
  have e2 : (cA m0 + BitVec.ofNat 64 o').toNat = (cA m0).toNat + o' :=
    NativeRustcVm.toNat_add_ofNat (by omega)
  refine Env.wf_of ⟨⟨mapped_sub hk pg.pm hon, by unfold NoWrap; rw [e1]; omega⟩,
    ⟨mapped_sub hk pg.cm hon', by unfold NoWrap; rw [e2]; omega⟩, trivial⟩ ?_
  refine List.Pairwise.cons ?_ (List.pairwise_singleton _ _)
  simp only [List.mem_singleton, forall_eq]
  unfold Apart
  rw [e1, e2]
  omega

variable [Host] {k : Nat} {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData}

theorem label2 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.VerifyLayer.label_2 = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyLayer.b3Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.VerifyLayer.b3Offset) NativeRustcVmArm.Vm.VerifyLayer.label_2_at

theorem label3 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.VerifyLayer.label_3 = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyLayer.b4Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.VerifyLayer.b4Offset) NativeRustcVmArm.Vm.VerifyLayer.label_3_at

theorem label7 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.VerifyLayer.label_7 = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyLayer.b9Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.VerifyLayer.b9Offset) NativeRustcVmArm.Vm.VerifyLayer.label_7_at

theorem label8 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.VerifyLayer.label_8 = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyLayer.b10Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.VerifyLayer.b10Offset) NativeRustcVmArm.Vm.VerifyLayer.label_8_at

theorem label10 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.VerifyLayer.label_10 = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyLayer.b12Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.VerifyLayer.b12Offset) NativeRustcVmArm.Vm.VerifyLayer.label_10_at

/-- **The odd entry left** (`b12`, `b13`, `b14`): from `.LVerifyLayer_10` with `n - 1` entries
summed to `.LVerifyLayer_3` with all `n`. -/
theorem one_run (hp : Placed code k) (h : VerifyLayerPre a s c m0) {j : Nat} (hj : j < 47)
    {st0 : MachineData} {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyLayer.b12Offset))
    (hb : FB m0 st.data) (hdm : st.data.dmem = st0.dmem) (hk : Bus.KeepRegs regsL st0 st.data)
    (hn : 1 ≤ c.mu.size) (h25 : st0.regs.X25.toNat = c.mu.size)
    (h24 : st0.regs.X24.toBitVec = projectAddr)
    (h19 : st0.regs.X19.toBitVec = cA m0 + BitVec.ofNat 64 32)
    (h11 : st.data.regs.X11.toNat = c.mu.size - 1) (h8 : st.data.regs.X8.toNat = 2 ^ j)
    (h01 : (⟨st.data.regs.X0, st.data.regs.X1⟩ : EW) = xs (muSel c.mu j) (c.mu.size - 1))
    {R : MachineState → Prop}
    (cont : ∀ st' : MachineState, st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyLayer.b4Offset) → FB m0 st'.data →
      st'.data.dmem = st0.dmem → Bus.KeepRegs regsL st0 st'.data →
      (⟨st'.data.regs.X0, st'.data.regs.X1⟩ : EW) = xs (muSel c.mu j) c.mu.size →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have hS := pre_stack h
  have g := geo_of h
  have pg := pgeo_of h
  have hmu := (mu_len (claimAt_fb h hb)).2
  -- `b12`: the addresses of the last mask and entry.
  refine at_pc hpc (Fr.runBlock hS N_ge rfl hb (blk hp b12_in_code (by simp [b12])) e12 rfl rfl
    (by decide) (by decide) fun st1 hb1 hd1 hm1 hpc1 ↦ ?_)
  simp only [PcOk] at hpc1
  rw [show k + NativeRustcVmArm.Vm.VerifyLayer.b12Offset + b12.length = k + NativeRustcVmArm.Vm.VerifyLayer.b13Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyLayer.b12_next]] at hpc1
  have k1 : Bus.KeepRegs (regsL ++ [.X0, .X1, .X8]) st.data st1.data :=
    Bus.KeepRegs.of_block hm1 rfl
  have r24 : (st.data.regs.getXReg .X24).toBitVec = projectAddr := by
    rw [kg hk .X24]; exact h24
  have r19 : (st.data.regs.getXReg .X19).toBitVec = cA m0 + BitVec.ofNat 64 32 := by
    rw [kg hk .X19]; exact h19
  have r25 : (st.data.regs.getXReg .X25).toNat = c.mu.size := by rw [kg hk .X25]; exact h25
  have e9 : (st1.data.regs.getXReg .X9).toBitVec =
      projectAddr + BitVec.ofNat 64 (8 * (c.mu.size - 1)) := by
    rw [hm1.regs .X9 _ rfl, addShl (regB .X24 r24) (regN .X11 h11)]
    exact addr_eq (by norm_num)
  have e10 : (st1.data.regs.getXReg .X10).toBitVec =
      cA m0 + BitVec.ofNat 64 (24 + 16 * (c.mu.size - 1)) + BitVec.ofInt 64 8 := by
    rw [hm1.regs .X10 _ rfl, addShl (regB .X19 r19) (regN .X11 h11),
      show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl, NativeRustcVm.addr_add_add,
      NativeRustcVm.addr_add_add]
    exact addr_eq (by norm_num; omega)
  have e11 : (st1.data.regs.getXReg .X11).toNat = 1 := by
    show (st1.data.regs.getXReg .X11).toBitVec.toNat = 1
    rw [hm1.regs .X11 _ rfl, subSym (regN .X25 r25) (regN .X11 h11) (by omega)]
    omega
  -- `b13`: the last entry, if its mask has bit `j`.
  have hwf := wf_two pg g hb1.kept (o := 8 * (c.mu.size - 1)) (n := 8)
    (o' := 24 + 16 * (c.mu.size - 1)) (n' := 16) (by omega) (by omega) (by omega) (by omega)
  have hm2 : Match (Env.ofMachine st1.data
      [(projectAddr + BitVec.ofNat 64 (8 * (c.mu.size - 1)), 8),
        (cA m0 + BitVec.ofNat 64 (24 + 16 * (c.mu.size - 1)), 16)]) oneS st1.data :=
    match_ofMachine ⟨rfl, nofun, rfl, nofun, trivial⟩ rfl
      ⟨by
        beta_reduce
        rw [ev_ptr, e9, show BitVec.ofInt 64 0 = BitVec.ofNat 64 0 from rfl,
          NativeRustcVm.addr_add_zero]
        rfl,
        by beta_reduce; rw [ev_ptr, e10]; rfl, trivial⟩ trivial trivial trivial
  refine fb_run hb1 (blk hp b13_in_code (by simp [b13])) e13 hwf rfl hpc1 hm2 rfl rfl
    fun st2 hb2 hd2 hm2' hpc2 ↦ ?_
  have hc1 := claimAt_fb h hb1
  have hmw : NativeRustcVm.WordAt st1.data.dmem
      (projectAddr + BitVec.ofNat 64 (8 * (c.mu.size - 1)) + BitVec.ofNat 64 0)
      (rmfeProjectW.getD (c.mu.size - 1) 0) := by
    rw [NativeRustcVm.addr_add_zero]; exact mask_word (proj_fb h hb1) (by omega)
  have hmu0 : NativeRustcVm.WordAt st1.data.dmem
      (cA m0 + BitVec.ofNat 64 (24 + 16 * (c.mu.size - 1)) + BitVec.ofNat 64 0)
      (c.mu.getD (c.mu.size - 1) 0).c0 := by
    rw [NativeRustcVm.addr_add_zero]; exact (mu_word hc1 (by omega)).1
  have hmu1 : NativeRustcVm.WordAt st1.data.dmem
      (cA m0 + BitVec.ofNat 64 (24 + 16 * (c.mu.size - 1)) + BitVec.ofNat 64 8)
      (c.mu.getD (c.mu.size - 1) 0).c1 := by
    rw [NativeRustcVm.addr_add_add]; exact (mu_word hc1 (by omega)).2
  have r8 : (st1.data.regs.getXReg .X8).toNat = 2 ^ j := by rw [kg k1 .X8]; exact h8
  have e0 := reg_val (r := .X0) hm2' rfl (eorSym (ev_regU _ _ _)
    (selSym (by omega) (ld0 hmw) (regN .X8 r8) (ld1 hmu0)))
  have e1 := reg_val (r := .X1) hm2' rfl (eorSym (ev_regU _ _ _)
    (selSym (by omega) (ld0 hmw) (regN .X8 r8) (ld1 hmu1)))
  have hc13 : (SBool.not (SBool.cmp .eq .W64 (.reg .X11) (.lit 1))).eval (Env.ofMachine st1.data
      [(projectAddr + BitVec.ofNat 64 (8 * (c.mu.size - 1)), 8),
        (cA m0 + BitVec.ofNat 64 (24 + 16 * (c.mu.size - 1)), 16)]) = false := by
    rw [sb_not, sb_cmp, eq_apply, regN .X11 e11, ev_lit, BitVec.toNat_ofNat]
    rfl
  have hpc2' := pc_false hpc2 hc13
  rw [show k + NativeRustcVmArm.Vm.VerifyLayer.b13Offset + b13.length = k + NativeRustcVmArm.Vm.VerifyLayer.b14Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyLayer.b13_next]] at hpc2'
  have k2 : Bus.KeepRegs regsL st1.data st2.data := Bus.KeepRegs.of_block hm2' rfl
  -- `b14`: back to `.LVerifyLayer_3`.
  refine at_pc hpc2' (Fr.runBlock hS N_ge rfl hb2 (blk hp b14_in_code (by simp [b14])) e14 rfl rfl
    (by decide) (by decide) fun st3 hb3 hd3 hm3 hpc3 ↦ ?_)
  simp only [PcOk] at hpc3
  have k3 : Bus.KeepRegs (regsL ++ [.X0, .X1]) st2.data st3.data := Bus.KeepRegs.of_block hm3 rfl
  refine cont st3 (hpc3.trans (label3 hp)) hb3 (by rw [hd3, hd2, hd1, hdm]) ?_ ?_
  · have k1' : Bus.KeepRegs regsL st.data st1.data := fun r hr ↦ k1 r (List.mem_append_left _ hr)
    have k3' : Bus.KeepRegs regsL st2.data st3.data := fun r hr ↦ k3 r (List.mem_append_left _ hr)
    exact hk.trans (k1'.trans (k2.trans k3'))
  · show (⟨st3.data.regs.getXReg .X0, st3.data.regs.getXReg .X1⟩ : EW) = _
    rw [kg k3 .X0, kg k3 .X1, e0, e1, kg k1 .X0, kg k1 .X1,
      show c.mu.size = c.mu.size - 1 + 1 by omega, xs_succ, Nat.add_sub_cancel, ← h01,
      ← muSel_eq c.mu j (c.mu.size - 1) _ _ rfl rfl]
    rfl

/-- **The pair loop**, `i` pairs summed, to `b11` with all of them. -/
theorem pair_loop (hp : Placed code k) (h : VerifyLayerPre a s c m0) {j : Nat} (hj : j < 47)
    {st0 : MachineData} {R : MachineState → Prop}
    (cont : ∀ st' : MachineState, st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyLayer.b11Offset) → FB m0 st'.data →
      st'.data.dmem = st0.dmem → Bus.KeepRegs regsL st0 st'.data →
      st'.data.regs.X8.toNat = 2 ^ j →
      (⟨st'.data.regs.X9, st'.data.regs.X11⟩ : EW) =
        xs (fun l ↦ muSel c.mu j (2 * l)) (c.mu.size / 2) →
      (⟨st'.data.regs.X10, st'.data.regs.X12⟩ : EW) =
        xs (fun l ↦ muSel c.mu j (2 * l + 1)) (c.mu.size / 2) →
      Eventually (step1 Host.exe) R st') :
    ∀ r i (st : MachineState), c.mu.size / 2 - i = r → st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyLayer.b10Offset) →
      PairI m0 c j i st0 st.data → Eventually (step1 Host.exe) R st := by
  have g := geo_of h
  have pg := pgeo_of h
  intro r
  induction r with
  | zero => intro i st hr _ hi; have := hi.lt; omega
  | succ r ih =>
    intro i st hr hpc hi
    have hmu := (mu_len (claimAt_fb h hi.fb)).2
    have hlt := hi.lt
    have hwf := wf_two pg g hi.fb.kept (o := 16 * i) (n := 16) (o' := 24 + 32 * i) (n' := 32)
      (by omega) (by omega) (by omega) (by omega)
    have hm : Match (Env.ofMachine st.data [(projectAddr + BitVec.ofNat 64 (16 * i), 16),
        (cA m0 + BitVec.ofNat 64 (24 + 32 * i), 32)]) pairS st.data :=
      match_ofMachine ⟨rfl, nofun, rfl, nofun, trivial⟩ rfl
        ⟨by
          beta_reduce
          rw [ev_ptr]
          show st.data.regs.X14.toBitVec =
            projectAddr + BitVec.ofNat 64 (16 * i) + BitVec.ofInt 64 8
          rw [hi.x14, show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl,
            NativeRustcVm.addr_add_add]
          exact addr_eq (by omega),
        by
          beta_reduce
          rw [ev_ptr]
          show st.data.regs.X13.toBitVec =
            cA m0 + BitVec.ofNat 64 (24 + 32 * i) + BitVec.ofInt 64 16
          rw [hi.x13, show BitVec.ofInt 64 16 = BitVec.ofNat 64 16 from rfl,
            NativeRustcVm.addr_add_add]
          exact addr_eq (by omega), trivial⟩ trivial trivial trivial
    refine fb_run hi.fb (blk hp b10_in_code (by simp [b10])) e10 hwf rfl hpc hm rfl rfl
      fun st1 hb1 hd1 hm1 hpc1 ↦ ?_
    have hc := claimAt_fb h hi.fb
    have pw := proj_fb h hi.fb
    have lA : NativeRustcVm.WordAt st.data.dmem
        (projectAddr + BitVec.ofNat 64 (16 * i) + BitVec.ofNat 64 0)
        (rmfeProjectW.getD (2 * i) 0) := by
      rw [NativeRustcVm.addr_add_add, show 16 * i + 0 = 8 * (2 * i) by omega]
      exact mask_word pw (by omega)
    have lB : NativeRustcVm.WordAt st.data.dmem
        (projectAddr + BitVec.ofNat 64 (16 * i) + BitVec.ofNat 64 8)
        (rmfeProjectW.getD (2 * i + 1) 0) := by
      rw [NativeRustcVm.addr_add_add, show 16 * i + 8 = 8 * (2 * i + 1) by omega]
      exact mask_word pw (by omega)
    have u0 : NativeRustcVm.WordAt st.data.dmem
        (cA m0 + BitVec.ofNat 64 (24 + 32 * i) + BitVec.ofNat 64 0)
        (c.mu.getD (2 * i) 0).c0 := by
      rw [NativeRustcVm.addr_add_add, show 24 + 32 * i + 0 = 24 + 16 * (2 * i) by omega]
      exact (mu_word hc (by omega)).1
    have u8 : NativeRustcVm.WordAt st.data.dmem
        (cA m0 + BitVec.ofNat 64 (24 + 32 * i) + BitVec.ofNat 64 8)
        (c.mu.getD (2 * i) 0).c1 := by
      rw [NativeRustcVm.addr_add_add, show 24 + 32 * i + 8 = 24 + 16 * (2 * i) + 8 by omega]
      exact (mu_word hc (by omega)).2
    have u16 : NativeRustcVm.WordAt st.data.dmem
        (cA m0 + BitVec.ofNat 64 (24 + 32 * i) + BitVec.ofNat 64 16)
        (c.mu.getD (2 * i + 1) 0).c0 := by
      rw [NativeRustcVm.addr_add_add, show 24 + 32 * i + 16 = 24 + 16 * (2 * i + 1) by omega]
      exact (mu_word hc (by omega)).1
    have u24 : NativeRustcVm.WordAt st.data.dmem
        (cA m0 + BitVec.ofNat 64 (24 + 32 * i) + BitVec.ofNat 64 24)
        (c.mu.getD (2 * i + 1) 0).c1 := by
      rw [NativeRustcVm.addr_add_add,
        show 24 + 32 * i + 24 = 24 + 16 * (2 * i + 1) + 8 by omega]
      exact (mu_word hc (by omega)).2
    have r8 : (st.data.regs.getXReg .X8).toNat = 2 ^ j := hi.x8
    have e9 := reg_val (r := .X9) hm1 rfl (eorSym (ev_regU _ _ _)
      (selSym (by omega) (ld0 lA) (regN .X8 r8) (ld1 u0)))
    have e11 := reg_val (r := .X11) hm1 rfl (eorSym (ev_regU _ _ _)
      (selSym (by omega) (ld0 lA) (regN .X8 r8) (ld1 u8)))
    have e10 := reg_val (r := .X10) hm1 rfl (eorSym (ev_regU _ _ _)
      (selSym (by omega) (ld0 lB) (regN .X8 r8) (ld1 u16)))
    have e12 := reg_val (r := .X12) hm1 rfl (eorSym (ev_regU _ _ _)
      (selSym (by omega) (ld0 lB) (regN .X8 r8) (ld1 u24)))
    have e15 : (st1.data.regs.getXReg .X15).toNat = 2 * (c.mu.size / 2) - 2 * (i + 1) := by
      show (st1.data.regs.getXReg .X15).toBitVec.toNat = _
      rw [hm1.regs .X15 _ rfl, subSym (regN .X15 hi.x15) (litN 2) (by omega)]
      omega
    have k1 : Bus.KeepRegs (regsL ++ [.X8]) st.data st1.data := Bus.KeepRegs.of_block hm1 rfl
    have hev : (⟨st1.data.regs.X9, st1.data.regs.X11⟩ : EW) =
        xs (fun l ↦ muSel c.mu j (2 * l)) (i + 1) := by
      show (⟨st1.data.regs.getXReg .X9, st1.data.regs.getXReg .X11⟩ : EW) = _
      rw [e9, e11, xs_succ, ← hi.ev, ← muSel_eq c.mu j (2 * i) _ _ rfl rfl]
      rfl
    have hod : (⟨st1.data.regs.X10, st1.data.regs.X12⟩ : EW) =
        xs (fun l ↦ muSel c.mu j (2 * l + 1)) (i + 1) := by
      show (⟨st1.data.regs.getXReg .X10, st1.data.regs.getXReg .X12⟩ : EW) = _
      rw [e10, e12, xs_succ, ← hi.od, ← muSel_eq c.mu j (2 * i + 1) _ _ rfl rfl]
      rfl
    have hkeep : Bus.KeepRegs regsL st0 st1.data :=
      hi.keep.trans fun r hr ↦ k1 r (List.mem_append_left _ hr)
    have h8 : st1.data.regs.X8.toNat = 2 ^ j := by
      show (st1.data.regs.getXReg .X8).toNat = _
      rw [kg k1 .X8]; exact hi.x8
    have hdm : st1.data.dmem = st0.dmem := hd1.trans hi.dm
    have hc10 : (SBool.not (SBool.cmp .eq .W64 (.reg .X15) (.lit 2))).eval (Env.ofMachine
        st.data [(projectAddr + BitVec.ofNat 64 (16 * i), 16),
          (cA m0 + BitVec.ofNat 64 (24 + 32 * i), 32)]) = decide (i + 1 < c.mu.size / 2) := by
      rw [sb_not, sb_cmp, eq_apply, regN .X15 hi.x15, litN 2]
      by_cases hl : i + 1 < c.mu.size / 2
      · rw [decide_eq_true hl, decide_eq_false (by omega)]; rfl
      · rw [decide_eq_false hl, decide_eq_true (by omega)]; rfl
    by_cases hl : i + 1 < c.mu.size / 2
    · refine ih (i + 1) st1 (by omega)
        ((pc_true hpc1 (by rw [hc10, decide_eq_true hl])).trans (label8 hp))
        ⟨hb1, hdm, hkeep, h8, e15, ?_, ?_, hev, hod, hl⟩
      · show (st1.data.regs.getXReg .X14).toBitVec = _
        rw [hm1.regs .X14 _ rfl, ev_ptr]
        show projectAddr + BitVec.ofNat 64 (16 * i) + BitVec.ofInt 64 24 = _
        rw [show BitVec.ofInt 64 24 = BitVec.ofNat 64 24 from rfl, NativeRustcVm.addr_add_add]
        exact addr_eq (by omega)
      · show (st1.data.regs.getXReg .X13).toBitVec = _
        rw [hm1.regs .X13 _ rfl, ev_ptr]
        show cA m0 + BitVec.ofNat 64 (24 + 32 * i) + BitVec.ofInt 64 48 = _
        rw [show BitVec.ofInt 64 48 = BitVec.ofNat 64 48 from rfl, NativeRustcVm.addr_add_add]
        exact addr_eq (by omega)
    · have hpc1' := pc_false hpc1 (by rw [hc10, decide_eq_false hl])
      rw [show k + NativeRustcVmArm.Vm.VerifyLayer.b10Offset + b10.length = k + NativeRustcVmArm.Vm.VerifyLayer.b11Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyLayer.b10_next]] at hpc1'
      have hp2 : i + 1 = c.mu.size / 2 := by omega
      rw [hp2] at hev hod
      exact cont st1 hpc1' hb1 hdm hkeep h8 hev hod

/-- **The masked sum of bit `j`**: from `b6` to `.LVerifyLayer_3` with it in X0, X1. -/
theorem masked_run (hp : Placed code k) (h : VerifyLayerPre a s c m0) {j : Nat}
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyLayer.b6Offset)) (hi : MaskIn m0 c j st.data)
    {R : MachineState → Prop}
    (cont : ∀ st' : MachineState, st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyLayer.b4Offset) → FB m0 st'.data →
      st'.data.dmem = st.data.dmem → Bus.KeepRegs regsL st.data st'.data →
      (⟨st'.data.regs.X0, st'.data.regs.X1⟩ : EW) = maskedOf c.mu j →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have hS := pre_stack h
  have hmu := (mu_len (claimAt_fb h hi.fb)).2
  have hj := hi.lt
  rw [masked_eq c.mu j hmu] at cont
  -- `b6`: no entries?
  refine at_pc hpc (Fr.runBlock hS N_ge rfl hi.fb (blk hp b6_in_code (by simp [b6])) e6 rfl rfl
    (by decide) (by decide) fun st1 hb1 hd1 hm1 hpc1 ↦ ?_)
  have k1 : Bus.KeepRegs (regsL ++ [.X0, .X1]) st.data st1.data := Bus.KeepRegs.of_block hm1 rfl
  have hk1 : Bus.KeepRegs regsL st.data st1.data := fun r hr ↦ k1 r (List.mem_append_left _ hr)
  have hc6 : (SBool.cmp .eq .W64 (.reg .X25) (.lit 0)).eval
      (Env.ofMachine st.data [(base m0 2032, 2032)]) = decide (c.mu.size = 0) := by
    rw [sb_cmp, eq_apply, regN .X25 hi.x25, litN 0]
  by_cases hn0 : c.mu.size = 0
  · -- `b3`: the sum is `0`.
    have hpc1' := (pc_true hpc1 (by rw [hc6, decide_eq_true hn0])).trans (label2 hp)
    refine at_pc hpc1' (Fr.runBlock hS N_ge rfl hb1 (blk hp b3_in_code (by simp [b3])) e3 rfl rfl
      (by decide) (by decide) fun st2 hb2 hd2 hm2 hpc2 ↦ ?_)
    simp only [PcOk] at hpc2
    rw [show k + NativeRustcVmArm.Vm.VerifyLayer.b3Offset + b3.length = k + NativeRustcVmArm.Vm.VerifyLayer.b4Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyLayer.b3_next]] at hpc2
    have k2 : Bus.KeepRegs regsL st1.data st2.data := Bus.KeepRegs.of_block hm2 rfl
    refine cont st2 hpc2 hb2 (hd2.trans hd1) (hk1.trans k2) ?_
    rw [hn0, xs_zero]
    show (⟨st2.data.regs.getXReg .X0, st2.data.regs.getXReg .X1⟩ : EW) = ⟨0, 0⟩
    rw [reg_val hm2 rfl (x := 0) (by rw [ev_lit]; rfl),
      reg_val hm2 rfl (x := 0) (by rw [ev_lit]; rfl)]
  have hpc1' := pc_false hpc1 (by rw [hc6, decide_eq_false hn0])
  rw [show k + NativeRustcVmArm.Vm.VerifyLayer.b6Offset + b6.length = k + NativeRustcVmArm.Vm.VerifyLayer.b7Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyLayer.b6_next]] at hpc1'
  -- `b7`: the bit; one entry?
  refine at_pc hpc1' (Fr.runBlock hS N_ge rfl hb1 (blk hp b7_in_code (by simp [b7])) e7 rfl rfl
    (by decide) (by decide) fun st2 hb2 hd2 hm2 hpc2 ↦ ?_)
  have k2 : Bus.KeepRegs regsL st1.data st2.data := Bus.KeepRegs.of_block hm2 rfl
  have hk2 := hk1.trans k2
  have r27n : (st1.data.regs.getXReg .X27).toNat = 1 :=
    (congrArg UInt64.toNat (kg hk1 .X27)).trans hi.x27
  have r27 : (st1.data.regs.getXReg .X27).toBitVec = BitVec.ofNat 64 1 := bv_of_toNat r27n
  have r20 : (st1.data.regs.getXReg .X20).toNat = j :=
    (congrArg UInt64.toNat (kg hk1 .X20)).trans hi.x20
  have r25 : (st1.data.regs.getXReg .X25).toNat = c.mu.size :=
    (congrArg UInt64.toNat (kg hk1 .X25)).trans hi.x25
  have r20' : ((Sym.reg .X20).eval (Env.ofMachine st1.data [(base m0 2032, 2032)])).toNat = j :=
    regN .X20 r20
  have x8v : st2.data.regs.X8.toNat = 2 ^ j := by
    show (st2.data.regs.getXReg .X8).toBitVec.toNat = _
    rw [hm2.regs .X8 _ rfl, ev_bin, regB .X27 r27, lslv_one (by rw [r20']; omega), r20']
  have hc7 : (SBool.not (SBool.cmp .eq .W64 (.reg .X25) (.lit 1))).eval
      (Env.ofMachine st1.data [(base m0 2032, 2032)]) = !decide (c.mu.size = 1) := by
    rw [sb_not, sb_cmp, eq_apply, regN .X25 r25, litN 1]
  by_cases hn1 : c.mu.size = 1
  · -- `b8`: nothing summed yet, then the one entry.
    have hpc2' := pc_false hpc2 (by rw [hc7, decide_eq_true hn1]; rfl)
    rw [show k + NativeRustcVmArm.Vm.VerifyLayer.b7Offset + b7.length = k + NativeRustcVmArm.Vm.VerifyLayer.b8Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyLayer.b7_next]] at hpc2'
    refine at_pc hpc2' (Fr.runBlock hS N_ge rfl hb2 (blk hp b8_in_code (by simp [b8])) e8 rfl rfl
      (by decide) (by decide) fun st3 hb3 hd3 hm3 hpc3 ↦ ?_)
    simp only [PcOk] at hpc3
    have k3 : Bus.KeepRegs (regsL ++ [.X8]) st2.data st3.data := Bus.KeepRegs.of_block hm3 rfl
    refine one_run hp h hj (hpc3.trans (label10 hp)) hb3 (hd3.trans (hd2.trans hd1))
      (hk2.trans fun r hr ↦ k3 r (List.mem_append_left _ hr)) (by omega) hi.x25 hi.x24 hi.x19
      ?_ ?_ ?_ cont
    · show (st3.data.regs.getXReg .X11).toBitVec.toNat = _
      rw [NativeRustcVmArm.Bus.Gkr.reg_lit hm3 rfl, hn1]; rfl
    · show (st3.data.regs.getXReg .X8).toNat = _
      rw [kg k3 .X8]; exact x8v
    · rw [hn1, xs_zero]
      show (⟨st3.data.regs.getXReg .X0, st3.data.regs.getXReg .X1⟩ : EW) = ⟨0, 0⟩
      rw [reg_val hm3 rfl (x := 0) (by rw [ev_lit]; rfl),
        reg_val hm3 rfl (x := 0) (by rw [ev_lit]; rfl)]
  have hpc2' := (pc_true hpc2 (by rw [hc7, decide_eq_false hn1]; rfl)).trans (label7 hp)
  -- `b9`: the pair loop's registers.
  refine at_pc hpc2' (Fr.runBlock hS N_ge rfl hb2 (blk hp b9_in_code (by simp [b9])) e9 rfl rfl
    (by decide) (by decide) fun st3 hb3 hd3 hm3 hpc3 ↦ ?_)
  simp only [PcOk] at hpc3
  rw [show k + NativeRustcVmArm.Vm.VerifyLayer.b9Offset + b9.length = k + NativeRustcVmArm.Vm.VerifyLayer.b10Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyLayer.b9_next]] at hpc3
  have k3 : Bus.KeepRegs (regsL ++ [.X8]) st2.data st3.data := Bus.KeepRegs.of_block hm3 rfl
  have hk3 : Bus.KeepRegs regsL st.data st3.data :=
    hk2.trans fun r hr ↦ k3 r (List.mem_append_left _ hr)
  have h144 : NativeRustcVm.WordAt st2.data.dmem (base m0 2032 + BitVec.ofNat 64 144)
      (UInt64.ofBitVec (cA m0 + BitVec.ofNat 64 24)) := by rw [hd2, hd1]; exact hi.f144
  have r25 : (st2.data.regs.getXReg .X25).toNat = c.mu.size := by
    rw [kg hk2 .X25]; exact hi.x25
  have hpair : PairI m0 c j 0 st.data st3.data := by
    refine ⟨hb3, hd3.trans (hd2.trans hd1), hk3, ?_, ?_, ?_, ?_, ?_, ?_, by omega⟩
    · show (st3.data.regs.getXReg .X8).toNat = _
      rw [kg k3 .X8]; exact x8v
    · show (st3.data.regs.getXReg .X15).toBitVec.toNat = _
      rw [hm3.regs .X15 _ rfl, ev_bin, ev_regU, ev_lit, and_apply, BitVec.toNat_and,
        BitVec.toNat_ofNat]
      show (st2.data.regs.getXReg .X25).toNat &&& 30 % 2 ^ 64 = _
      rw [r25, and30 _ (by omega)]
      rfl
    · show (st3.data.regs.getXReg .X14).toBitVec = _
      rw [hm3.regs .X14 _ rfl, ev_regU, kg hk2 .X26]; exact hi.x26
    · show (st3.data.regs.getXReg .X13).toBitVec = _
      rw [hm3.regs .X13 _ rfl, ev_bin, ev_load, fw_load rfl h144, ev_lit, add_apply,
        UInt64.toBitVec_ofBitVec, NativeRustcVm.addr_add_add]
    · show (⟨st3.data.regs.getXReg .X9, st3.data.regs.getXReg .X11⟩ : EW) = 0
      rw [reg_val hm3 rfl (x := 0) (by rw [ev_lit]; rfl),
        reg_val hm3 rfl (x := 0) (by rw [ev_lit]; rfl)]; rfl
    · show (⟨st3.data.regs.getXReg .X10, st3.data.regs.getXReg .X12⟩ : EW) = 0
      rw [reg_val hm3 rfl (x := 0) (by rw [ev_lit]; rfl),
        reg_val hm3 rfl (x := 0) (by rw [ev_lit]; rfl)]; rfl
  refine pair_loop hp h hj (st0 := st.data) ?_ _ 0 st3 rfl hpc3 hpair
  intro st4 hpc4 hb4 hd4 hk4 h8 hev hod
  -- `b11`: the two halves; an odd entry left?
  refine at_pc hpc4 (Fr.runBlock hS N_ge rfl hb4 (blk hp b11_in_code (by simp [b11])) e11 rfl rfl
    (by decide) (by decide) fun st5 hb5 hd5 hm5 hpc5 ↦ ?_)
  have k5 : Bus.KeepRegs (regsL ++ [.X8]) st4.data st5.data := Bus.KeepRegs.of_block hm5 rfl
  have hk5 : Bus.KeepRegs regsL st.data st5.data :=
    hk4.trans fun r hr ↦ k5 r (List.mem_append_left _ hr)
  have h01 : (⟨st5.data.regs.X0, st5.data.regs.X1⟩ : EW) =
      xs (muSel c.mu j) (2 * (c.mu.size / 2)) := by
    show (⟨st5.data.regs.getXReg .X0, st5.data.regs.getXReg .X1⟩ : EW) = _
    rw [reg_val hm5 rfl (eorSym (ev_regU _ _ _) (ev_regU _ _ _)),
      reg_val hm5 rfl (eorSym (ev_regU _ _ _) (ev_regU _ _ _)), xs_split2, ← hev, ← hod]
    show (⟨st4.data.regs.X10 ^^^ st4.data.regs.X9, st4.data.regs.X12 ^^^ st4.data.regs.X11⟩ :
      EW) = ⟨st4.data.regs.X9 ^^^ st4.data.regs.X10, st4.data.regs.X11 ^^^ st4.data.regs.X12⟩
    rw [UInt64.xor_comm st4.data.regs.X10, UInt64.xor_comm st4.data.regs.X12]
  have r25' : (st4.data.regs.getXReg .X25).toNat = c.mu.size := by
    rw [kg hk4 .X25]; exact hi.x25
  have r23' : (st4.data.regs.getXReg .X23).toNat = 2 * (c.mu.size / 2) := by
    rw [kg hk4 .X23]; exact hi.x23
  have hc11 : (SBool.cmp .eq .W64 (.reg .X25) (.reg .X23)).eval
      (Env.ofMachine st4.data [(base m0 2032, 2032)]) = decide (c.mu.size % 2 = 0) := by
    rw [sb_cmp, eq_apply, regN .X25 r25', regN .X23 r23']
    by_cases he : c.mu.size % 2 = 0
    · rw [decide_eq_true he, decide_eq_true (by omega)]
    · rw [decide_eq_false he, decide_eq_false (by omega)]
  by_cases he : c.mu.size % 2 = 0
  · have hpc5' := (pc_true hpc5 (by rw [hc11, decide_eq_true he])).trans (label3 hp)
    refine cont st5 hpc5' hb5 (hd5.trans hd4) hk5 ?_
    rw [h01, show 2 * (c.mu.size / 2) = c.mu.size by omega]
  · have hpc5' := pc_false hpc5 (by rw [hc11, decide_eq_false he])
    rw [show k + NativeRustcVmArm.Vm.VerifyLayer.b11Offset + b11.length = k + NativeRustcVmArm.Vm.VerifyLayer.b12Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyLayer.b11_next]] at hpc5'
    refine one_run hp h hj hpc5' hb5 (hd5.trans hd4) hk5 (by omega) hi.x25 hi.x24 hi.x19 ?_ ?_ ?_
      cont
    · show (st5.data.regs.getXReg .X11).toBitVec.toNat = _
      rw [hm5.regs .X11 _ rfl, ev_bin, ev_regU, ev_lit, and_apply, BitVec.toNat_and,
        BitVec.toNat_ofNat]
      show (st4.data.regs.getXReg .X25).toNat &&& 30 % 2 ^ 64 = _
      rw [r25', and30 _ (by omega)]
      show 2 * (c.mu.size / 2) = _
      omega
    · show (st5.data.regs.getXReg .X8).toNat = _
      rw [kg k5 .X8]; exact h8
    · rw [h01, show 2 * (c.mu.size / 2) = c.mu.size - 1 by omega]

end

end NativeRustcVmArm.KeccakGkr.VerifyLayer
