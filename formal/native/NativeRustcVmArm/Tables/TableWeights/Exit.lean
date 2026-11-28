module

public import NativeRustcVmArm.Tables.TableWeights.Turn
public import NativeRustcArm.Hasher.Bytes

/-!
# `table_weights`: the exit

`b13` (`.LTableWeights_7`) writes the six weights to `out`, restores the callee-saved registers
and SP and returns (`exit_step`): `table_weights`'s postcondition.
-/

namespace NativeRustcVmArm.Tables.TableWeights

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Tables
open NativeRustcVmArm.Vm.TableWeights
open NativeRustcVm (wordOf ewOf)

public section

variable {m0 : MachineData}

/-- Where `b13` writes weight `i`'s limbs: its places, weight 5 from X0, X9. -/
def outLo (i : Nat) : Sym := if i < 5 then (lo i).sym else .reg .X0
/-- Weight `i`'s high limb as `b13` writes it. -/
def outHi (i : Nat) : Sym := if i < 5 then (hi i).sym else .reg .X9

/-- The saved registers' frame words. -/
def savedOffs : List (XReg × Nat) :=
  [(.X19, 232), (.X20, 224), (.X21, 216), (.X22, 208), (.X23, 200), (.X24, 192), (.X25, 184),
    (.X26, 176), (.X27, 168), (.X28, 160), (.X29, 144)]

theorem exitB : (∀ i < 6, ∀ t < 8, findWrite 1 (16 * i + t) (after b13 lastS).mem = some (outLo i, t) ∧
      findWrite 1 (16 * i + 8 + t) (after b13 lastS).mem = some (outHi i, t)) ∧
    (after b13 lastS).mem.all (fun w ↦ (w.r == 0 && decide (w.off + w.n ≤ 240)) ||
      (w.r == 1 && decide (w.off + w.n ≤ 96))) = true ∧
    (∀ p ∈ savedOffs, (after b13 lastS).reg p.1 = some (.load 0 p.2 8)) ∧
    (after b13 lastS).reg .X30 = some (.load 0 152 8) ∧ (after b13 lastS).sp = .ptr 0 240 := by
  rw [after_eq run_b13]
  exact ⟨by decide, rfl, by decide, rfl, rfl⟩

theorem calleeSaved_mem {r : XReg} (h : calleeSaved r = true) : ∃ o, (r, o) ∈ savedOffs := by
  cases r <;> simp [calleeSaved] at h <;> simp [savedOffs]

theorem savedOffs_xslots {r : XReg} {o : Nat} (h : (r, o) ∈ savedOffs) :
    (o, rg m0 r) ∈ xslots m0 := by
  simp only [savedOffs, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [xslots]

theorem W_size (c : Nat) : (W m0 c).size = 6 := by rw [W, size_twPrefix, size_H]

variable [Host] {k : Nat}

/-- **The exit.** -/
theorem exit_step (hp : Placed code k) (hc : Ctx m0) {m : MachineData} (hfin : Fin m0 m) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = retOf m0 ∧ TableWeightsPost m0 st.data) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.TableWeights.b13Offset)⟩ := by
  have hf := hfin.frm
  have hout : In m0 (rg m0 .X0) 96 := hc.out
  have hfm : FrameOk m.dmem (fb m0) 240 :=
    ⟨hc.geo.al, hc.geo.lo, hc.geo.hi, fun i hi => hf.kept _ (hc.geo.map i hi)⟩
  have hx0 : fw m0 m 8 = rg m0 .X0 := hf.slots (8, _) (by simp [xslots])
  have hwf : (Env.ofMachine m [(fb m0, 240), (rg m0 .X0, 96)]).WF :=
    Env.wf_of ⟨⟨hfm.mapped, hc.geo.hi⟩, ⟨fun i hi => hf.kept _ (hout.1.1 i hi), hout.1.2⟩, trivial⟩
      (List.pairwise_pair.mpr (hout.apart_frame hc.stk))
  have hm : Match (Env.ofMachine m [(fb m0, 240), (rg m0 .X0, 96)]) lastS m :=
    match_ofMachine ⟨rfl, fun _ => hc.geo.al, rfl, fun h => absurd h (by decide), trivial⟩
      (by rw [hf.sp]; simp [Sym.eval]) trivial trivial trivial
      ⟨by
        show (Env.ofMachine m ((fb m0, 240) :: [(rg m0 .X0, 96)])).load 0 8 8 = _
        rw [load_fw, hx0]
        simp, trivial⟩
  obtain ⟨hw, hwr, hsv, h30, hsp⟩ := exitB
  rw [after_eq run_b13] at hw hwr hsv h30 hsp
  refine exec_then (hb13 hp) run_b13 hwf hm fun st hm' hpc => .done _ ⟨?_, ?_, ?_, ?_⟩
  · -- the return address
    have e30 : st.data.regs.X30.toBitVec = m0.regs.X30.toBitVec := by
      rw [show st.data.regs.X30.toBitVec = _ from hm'.regs .X30 _ h30]
      show (Env.ofMachine m ((fb m0, 240) :: [(rg m0 .X0, 96)])).load 0 152 8 = _
      rw [load_fw]
      exact hf.slots (152, rg m0 .X30) (by simp [xslots])
    rw [show st.pc = retOf st.data from hpc]
    simp only [retOf, e30]
  · -- the weights at `out`
    show NativeRustcVm.EWsAt _ _ (tableWeights (H m0) (E m0) (P m0)).toList
    rw [tableWeights_eq, size_P]
    show NativeRustcVm.EWsAt _ _ (W m0 (n m0)).toList
    rw [NativeRustcVm.ewsAt_iff]
    intro i hi
    have hi6 : i < 6 := by simpa [W_size] using hi
    have hget : (W m0 (n m0)).toList[i] = (W m0 (n m0)).getD i 0 := by
      simp [Array.getD, W_size, hi6]
    have wordAt : ∀ (o : Nat) (v : Sym), o + 8 ≤ 96 →
        (∀ t < 8, findWrite 1 (o + t) (after b13 lastS).mem = some (v, t)) →
        NativeRustcVm.WordAt st.data.dmem (rg m0 .X0 + BitVec.ofNat 64 o)
          (UInt64.ofBitVec (v.eval (Env.ofMachine m [(fb m0, 240), (rg m0 .X0, 96)]))) := by
      intro o v ho hv
      rw [after_eq run_b13] at hv
      have := hm'.bytesAt_write (r := 1) (b := rg m0 .X0) (sz := 96) rfl ho hv
      rwa [← Hasher.wordBytes_ofBitVec] at this
    have exitB' := exitB.1
    rw [hget, NativeRustcVm.ewAt_iff, NativeRustcVm.addr_add_add]
    have env_eq : ∀ (j : Nat) (hj : j < 6),
        UInt64.ofBitVec ((outLo j).eval (Env.ofMachine m [(fb m0, 240), (rg m0 .X0, 96)])) =
          ((W m0 (n m0)).getD j 0).c0 ∧
        UInt64.ofBitVec ((outHi j).eval (Env.ofMachine m [(fb m0, 240), (rg m0 .X0, 96)])) =
          ((W m0 (n m0)).getD j 0).c1 := by
      intro j hj
      by_cases h5 : j < 5
      · refine ⟨?_, ?_⟩
        · simp only [outLo, h5, ↓reduceIte]
          rw [Pl.sym_eval, (hfin.w j h5).1]
        · simp only [outHi, h5, ↓reduceIte]
          rw [Pl.sym_eval, (hfin.w j h5).2]
      · obtain rfl : j = 5 := by omega
        simp only [outLo, outHi, show ¬(5 < 5) by decide, ↓reduceIte]
        rw [show (Sym.reg .X0).eval (Env.ofMachine m [(fb m0, 240), (rg m0 .X0, 96)]) = rg m .X0
          from rfl, show (Sym.reg .X9).eval (Env.ofMachine m [(fb m0, 240), (rg m0 .X0, 96)]) =
          rg m .X9 from rfl, hfin.x0, hfin.x9]
        exact ⟨rfl, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← (env_eq i hi6).1]
      exact wordAt (16 * i) (outLo i) (by omega) fun t ht => (exitB' i hi6 t ht).1
    · rw [← (env_eq i hi6).2]
      exact wordAt (16 * i + 8) (outHi i) (by omega) fun t ht => (exitB' i hi6 t ht).2
  · -- memory changed only at `out` and in the stack
    intro p hp
    rw [hm'.sameOutside hwf p fun ⟨w, hwm, b, sz, hb, h1, h2⟩ => hp ?_]
    · refine hf.same p fun h => hp (Or.inr ?_)
      rwa [stackArea_eq] at h
    have hw' := List.all_eq_true.mp hwr w hwm
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hw'
    rcases hw' with ⟨h0, hle⟩ | ⟨h1', hle⟩
    · rw [h0] at hb
      cases hb
      right
      rw [← stackArea_eq]
      have := hc.geo.lo
      have := hc.geo.hi
      have hlo : (fb m0 - BitVec.ofNat 64 ewMulStack).toNat = (fb m0).toNat - ewMulStack :=
        NativeRustcVm.toNat_sub_ofNat hc.geo.lo
      unfold StackArea
      rw [inRange_iff (by omega), hlo]
      omega
    · rw [h1'] at hb
      cases hb
      left
      show InRange (rg m0 .X0) 96 p
      rw [inRange_iff hout.1.2]
      omega
  · -- the registers kept
    refine ⟨fun r hr => ?_, ?_, fun p h => hm'.kept hwf p (hf.kept p h)⟩
    · obtain ⟨o, ho⟩ := calleeSaved_mem hr
      apply UInt64.toBitVec_inj.mp
      have h1 := hm'.regs r (.load 0 o 8) (hsv _ ho)
      have h2 : fw m0 m o = rg m0 r := hf.slots (o, rg m0 r) (savedOffs_xslots ho)
      rw [h1]
      show (Env.ofMachine m ((fb m0, 240) :: [(rg m0 .X0, 96)])).load 0 o 8 = rg m0 r
      rw [load_fw, h2]
    · apply UInt64.toBitVec_inj.mp
      rw [hm'.sp, hsp]
      simp only [Sym.eval, Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
        Option.getD_some, fb]
      rw [show (240 : Int) = ((240 : Nat) : Int) from rfl, BitVec.ofInt_natCast,
        BitVec.sub_add_cancel]

end

end NativeRustcVmArm.Tables.TableWeights
