module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Tables.TableWeights.Steps

/-!
# `table_weights`: a turn of the loop, the loop

`b3` multiplies weight 0 (`first_step`); `b4` to `b8` the others (`mults`); `b9` moves to the next
coordinate or leaves the loop (`last_step`). A turn (`turn_step`) and the loop (`loop_spec`): from
the loop head with `c` coordinates done to the exit with all done.
-/

namespace NativeRustcVmArm.Tables.TableWeights

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Tables
open NativeRustcVmArm.Vm.TableWeights
open NativeRustcVm (wordOf ewOf)

public section

variable {m0 : MachineData}

theorem Frm.toX {m : MachineData} (hf : Frm m0 m) : FrmX m0 m := by
  refine ⟨hf.sp, fun p hp => hf.slots p ?_, hf.same, hf.kept⟩
  simp only [xslots, List.mem_cons, List.not_mem_nil, or_false] at hp
  simp only [kslots, List.mem_cons, List.not_mem_nil, or_false]
  rcases hp with h | h | h | h | h | h | h | h | h | h | h | h | h <;> simp [h]

theorem keepB_b9 : (∀ i < 5, (lo i).after (after b9 midS) = some (lo i).sym ∧
      (hi i).after (after b9 midS) = some (hi i).sym) ∧
    ∀ p ∈ koffs, loadSym (after b9 midS).mem 0 p 8 = .load 0 p 8 := by
  rw [after_eq run_b9]
  exact ⟨by decide, by decide⟩

theorem ptr_add (x : BitVec 64) (a b : Nat) :
    x + BitVec.ofNat 64 a + BitVec.ofNat 64 b = x + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

/-- `b9`'s test: the point's cursor at its end exactly when the coordinate was the last. -/
theorem end_iff {x n0 : BitVec 64} {c : Nat} (hc : c < n0.toNat) (hnw : x.toNat + 16 * n0.toNat ≤ 2 ^ 64) :
    (x + BitVec.ofNat 64 (16 * (c + 1)) == x + n0 <<< 4) = decide (c + 1 = n0.toNat) := by
  have key : ∀ a b : BitVec 64, x + a = x + b ↔ a = b := fun a b =>
    ⟨fun h => by
      have := congrArg (· - x) h
      simpa only [BitVec.add_comm x, BitVec.add_sub_cancel] using this, fun h => h ▸ rfl⟩
  have hiff : x + BitVec.ofNat 64 (16 * (c + 1)) = x + n0 <<< 4 ↔ c + 1 = n0.toNat := by
    rw [key, BitVec.toNat_eq, BitVec.toNat_ofNat, BitVec.toNat_shiftLeft]
    omega
  by_cases h : c + 1 = n0.toNat
  · rw [decide_eq_true h]
    exact beq_iff_eq.mpr (hiff.mpr h)
  · rw [decide_eq_false h]
    exact beq_false_of_ne fun e => h (hiff.mp e)

variable [Host] {k : Nat}

/-- **The first multiplication** of coordinate `c`. -/
theorem first_step (hp : Placed code k) (hc : Ctx m0)
    (hmul : Spec (label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost) {c : Nat} {m : MachineData}
    (h3 : Pre3 m0 c m) :
    Eventually (step1 Host.exe) (fun st => st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.TableWeights.b4Offset) ∧ Mid m0 c 0 st.data)
      ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.TableWeights.b3Offset)⟩ := by
  have hx := hc.ptc h3.lt
  have hwf := hc.wf_in h3.frm hx
  have hcn : c < 2 ^ 64 := Nat.lt_of_lt_of_le h3.lt (UInt64.toNat_lt _).le
  have hm : Match (Env.ofMachine m [(fb m0, 240), (rg m0 .X4 + BitVec.ofNat 64 (16 * c), 16)])
      headS m :=
    match_frame (rs := [(_, 16)]) (srs := [(16, false)]) (known := [(.X27, .ptr 1 0)])
      (aliases := []) hc.geo h3.frm ⟨rfl, fun h => absurd h (by decide), trivial⟩
      ⟨by simp [Sym.eval]; exact h3.x27, trivial⟩ trivial
  have kb := keepB_b3
  rw [after_eq run_b3] at kb
  refine exec_then (hb3 hp) run_b3 hwf hm fun st hm' hpc => ?_
  refine call_mul hwf rfl (h3.frm.frameOk hc.geo) hm' hpc rfl rfl (v0 := (lo 0).sym)
    (v1 := (hi 0).sym) (v2 := fac2 0 (.load 1 0 8)) (v3 := fac3 0) rfl rfl rfl rfl hmul
    fun st' hpc' hx0 hx1 hsv hsp hwd hsame hkept => .done _
      ⟨hpc'.trans (addr_eq (by rw [Nat.add_assoc, NativeRustcVmArm.Vm.TableWeights.b3_next])), ?_⟩
  have hreg : ∀ r ∈ [XReg.X22, .X23, .X24, .X25, .X26], rg st'.data r = rg m r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hsv _ (.reg _) rfl rfl
  have h29 : (Sym.load 1 0 8).eval (Env.ofMachine m [(fb m0, 240),
      (rg m0 .X4 + BitVec.ofNat 64 (16 * c), 16)]) = (ch m0 c).c0.toBitVec := by
    show (Env.ofMachine m _).load 1 0 8 = _
    rw [hc.load_in h3.frm hx (by omega), ch_c0 h3.lt]
  have hprod : mulOf (Env.ofMachine m [(fb m0, 240), (rg m0 .X4 + BitVec.ofNat 64 (16 * c), 16)])
      (lo 0).sym (hi 0).sym (fac2 0 (.load 1 0 8)) (fac3 0) = (W m0 (c + 1)).getD 0 0 := by
    rw [mulOf, weight_of (h3.w 0 (by omega)), factor_of hcn (by omega) h3.frm h3.x22 h3.x25
      h3.x26 h29 h3.x24, W_succ h3.lt (by omega)]
  refine ⟨h3.lt, frm_after h3.frm hsp hwd (by rw [koffs_eq]; exact kb.slots) hsame hkept,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun i hi hi0 => ?_⟩
  · rw [hreg .X22 (by simp)]; exact h3.x22
  · rw [hreg .X23 (by simp)]; exact h3.x23
  · rw [show rg st'.data .X27 = _ from hsv .X27 (.ptr 1 16) rfl rfl]
    simp only [Sym.eval, Env.base_ofMachine_eq, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.map_some, Option.getD_some]
    rw [show (16 : Int) = ((16 : Nat) : Int) from rfl, add_ofNat_ofInt, Nat.mul_succ]
  · rw [show rg st'.data .X29 = _ from hsv .X29 _ rfl rfl]; exact h29
  · rw [hreg .X24 (by simp)]; exact h3.x24
  · rw [hreg .X25 (by simp)]; exact h3.x25
  · rw [hreg .X26 (by simp)]; exact h3.x26
  · show st'.data.regs.X0.toBitVec = _
    rw [hx0, hprod]
  · show st'.data.regs.X1.toBitVec = _
    rw [hx1, hprod]
  · simp only [Nat.not_lt_zero, ↓reduceIte]
    obtain ⟨hl, hh⟩ := kb.keep i hi
    exact ⟨by rw [Pl.val_after hsv hwd lo_ok hl, Pl.sym_eval]; exact (h3.w i hi).1,
      by rw [Pl.val_after hsv hwd hi_ok hh, Pl.sym_eval]; exact (h3.w i hi).2⟩

/-- **The multiplications** of coordinate `c`. -/
theorem mults (hp : Placed code k) (hc : Ctx m0)
    (hmul : Spec (label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost) {c : Nat} {m : MachineData}
    (h3 : Pre3 m0 c m) :
    Eventually (step1 Host.exe) (fun st => st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.TableWeights.b9Offset) ∧ Mid m0 c 5 st.data)
      ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.TableWeights.b3Offset)⟩ := by
  refine Eventually.bind (first_step hp hc hmul h3) fun ⟨d1, pc1⟩ ⟨e1, h1⟩ => ?_
  cases e1
  refine Eventually.bind (mid_step (j := 1) (by omega) (by omega) (hb4 hp) run_b4
    (after_eq run_b4 ▸ mb4) hmul hc.geo h1) fun ⟨d2, pc2⟩ ⟨e2, h2⟩ => ?_
  rw [NativeRustcVmArm.Vm.TableWeights.b4_length, NativeRustcVmArm.Vm.TableWeights.b4Length] at e2; cases e2
  refine Eventually.bind (mid_step (j := 2) (by omega) (by omega) (hb5 hp) run_b5
    (after_eq run_b5 ▸ mb5) hmul hc.geo h2) fun ⟨d3, pc3⟩ ⟨e3, h3⟩ => ?_
  rw [NativeRustcVmArm.Vm.TableWeights.b5_length, NativeRustcVmArm.Vm.TableWeights.b5Length] at e3; cases e3
  refine Eventually.bind (mid_step (j := 3) (by omega) (by omega) (hb6 hp) run_b6
    (after_eq run_b6 ▸ mb6) hmul hc.geo h3) fun ⟨d4, pc4⟩ ⟨e4, h4⟩ => ?_
  rw [NativeRustcVmArm.Vm.TableWeights.b6_length, NativeRustcVmArm.Vm.TableWeights.b6Length] at e4; cases e4
  refine Eventually.bind (mid_step (j := 4) (by omega) (by omega) (hb7 hp) run_b7
    (after_eq run_b7 ▸ mb7) hmul hc.geo h4) fun ⟨d5, pc5⟩ ⟨e5, h5⟩ => ?_
  rw [NativeRustcVmArm.Vm.TableWeights.b7_length, NativeRustcVmArm.Vm.TableWeights.b7Length] at e5; cases e5
  exact Eventually.mono (mid_step (j := 5) (by omega) (by omega) (hb8 hp) run_b8
    (after_eq run_b8 ▸ mb8) hmul hc.geo h5) fun st ⟨e, h⟩ => ⟨by rw [e, Nat.add_assoc, NativeRustcVmArm.Vm.TableWeights.b8_next], h⟩

/-- **`b9`**: the next coordinate, or the exit. -/
theorem last_step (hp : Placed code k) (hc : Ctx m0) {c : Nat} {m : MachineData}
    (hmid : Mid m0 c 5 m) :
    Eventually (step1 Host.exe)
      (fun st => (st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.TableWeights.b10Offset) ∧ It m0 (c + 1) st.data) ∨
        (st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.TableWeights.b13Offset) ∧ Fin m0 st.data))
      ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.TableWeights.b9Offset)⟩ := by
  have hf := hmid.frm
  have hwf : (Env.ofMachine m [(fb m0, 240)]).WF :=
    Env.wf_of ⟨⟨hf.frameOk hc.geo |>.mapped, hc.geo.hi⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hm : Match (Env.ofMachine m [(fb m0, 240)]) midS m :=
    match_frame (rs := []) (srs := []) (known := []) (aliases := []) hc.geo hf trivial trivial
      trivial
  obtain ⟨kw, ks⟩ := keepB_b9
  rw [after_eq run_b9] at kw ks
  refine exec_then (hb9 hp) run_b9 hwf hm fun st hm' hpc => ?_
  have hf' : Frm m0 st.data := frm_of_match hc.geo hf hwf hm' rfl rfl ks
  have h64 : fw m0 m 64 = rg m0 .X4 + rg m0 .X5 <<< 4 :=
    hf.slots (64, _) (by simp [kslots])
  have hw : ∀ j < 5, WAt m0 st.data j ((W m0 (c + 1)).getD j 0) := fun j hj => by
    have := hmid.w j (by omega) (by omega)
    simp only [hj, ↓reduceIte] at this
    obtain ⟨hl, hh⟩ := kw j hj
    exact ⟨by rw [Pl.val_keep hwf hm' lo_ok hl, Pl.sym_eval]; exact this.1,
      by rw [Pl.val_keep hwf hm' hi_ok hh, Pl.sym_eval]; exact this.2⟩
  have hx0 : rg st.data .X0 = ((W m0 (c + 1)).getD 5 0).c0.toBitVec := by
    rw [rg_keep hm' (r := .X0) rfl]; exact hmid.x0
  have hx9 : rg st.data .X9 = ((W m0 (c + 1)).getD 5 0).c1.toBitVec := by
    rw [show rg st.data .X9 = _ from hm'.regs .X9 (.reg .X1) rfl]; exact hmid.x1
  simp only [PcOk, SBool.eval, CmpOp.apply, Sym.eval, low_W64, Env.ofMachine_regs, load_fw,
    h64] at hpc
  rw [show (m.regs.getXReg .X27).toBitVec = _ from hmid.x27,
    end_iff (x := rg m0 .X4) (n0 := rg m0 .X5) hmid.lt hc.pt.1.2] at hpc
  by_cases hend : c + 1 = n m0
  · rw [decide_eq_true (show c + 1 = (rg m0 .X5).toNat from hend)] at hpc
    simp only [↓reduceIte, lbl_7 hp] at hpc
    refine .done _ (Or.inr ⟨hpc, hf'.toX, ?_, ?_, ?_⟩)
    · rw [← hend]; exact hw
    · rw [← hend]; exact hx0
    · rw [← hend]; exact hx9
  · rw [decide_eq_false (show ¬c + 1 = (rg m0 .X5).toNat from hend)] at hpc
    simp only [Bool.false_eq_true, ↓reduceIte] at hpc
    refine .done _ (Or.inl ⟨hpc.trans (addr_eq (by rw [Nat.add_assoc, NativeRustcVmArm.Vm.TableWeights.b9_next])),
      ⟨by have := hmid.lt; unfold n at hend this ⊢; omega, hf', ?_, ?_, ?_, hw, hx0, hx9⟩⟩)
    · rw [show rg st.data .X22 = _ from hm'.regs .X22 _ rfl]
      simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
      rw [show (m.regs.getXReg .X22).toBitVec = _ from hmid.x22, BitVec.ofNat_add]
    · rw [show rg st.data .X23 = _ from hm'.regs .X23 _ rfl]
      simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
      rw [show (m.regs.getXReg .X23).toBitVec = _ from hmid.x23, ptr_add, Nat.mul_succ,
        Nat.add_assoc]
    · rw [rg_keep hm' (r := .X27) rfl]; exact hmid.x27

/-- **A turn of the loop.** -/
theorem turn_step (hp : Placed code k) (hc : Ctx m0)
    (hmul : Spec (label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost) {c : Nat} {m : MachineData}
    (hit : It m0 c m) :
    Eventually (step1 Host.exe)
      (fun st => (st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.TableWeights.b10Offset) ∧ It m0 (c + 1) st.data) ∨
        (st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.TableWeights.b13Offset) ∧ Fin m0 st.data))
      ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.TableWeights.b10Offset)⟩ := by
  refine Eventually.bind (head_step hp hc hit) fun ⟨d1, pc1⟩ ⟨e1, h1⟩ => ?_
  cases e1
  refine Eventually.bind (mults hp hc hmul h1) fun ⟨d2, pc2⟩ ⟨e2, h2⟩ => ?_
  cases e2
  exact last_step hp hc h2

/-- **The loop**: from the loop head with `c` coordinates done, the exit. -/
theorem loop_spec (hp : Placed code k) (hc : Ctx m0)
    (hmul : Spec (label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost) {c : Nat} {m : MachineData}
    (hit : It m0 c m) :
    Eventually (step1 Host.exe) (fun st => st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.TableWeights.b13Offset) ∧ Fin m0 st.data)
      ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.TableWeights.b10Offset)⟩ := by
  refine Sym.loop (fun r st => st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.TableWeights.b10Offset) ∧ ∃ c, n m0 - c = r ∧
      It m0 c st.data) (fun r st ⟨hpc, c, hr, hi⟩ => ?_) ⟨rfl, c, rfl, hit⟩
  obtain ⟨d, pc⟩ := st
  simp only at hpc
  subst hpc
  refine Eventually.mono (turn_step hp hc hmul hi) fun st h => ?_
  rcases h with ⟨hpc, hi'⟩ | h
  · exact Or.inr ⟨n m0 - (c + 1), by have := hi.lt; omega, hpc, c + 1, rfl, hi'⟩
  · exact Or.inl h

end

end NativeRustcVmArm.Tables.TableWeights
