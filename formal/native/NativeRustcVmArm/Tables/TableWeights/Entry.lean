module

public import NativeRustcVmArm.Tables.TableWeights.Exit

/-!
# `table_weights`: the entry

`b0` saves the callee-saved registers, `out` and `|equality_point|` in the frame and tests the
point's length. `b1` (a non-empty point) stores the heights and the point's end in the frame, sets
the six weights to `1` and enters the loop (`It 0`); `b12` (an empty point) sets the weights to `1`
and falls into the exit (`Fin`). Both from the environment of the entry state (`env0`: the frame,
the heights), what the blocks leave (`EntryBlock`), `entry_step`.
-/

namespace NativeRustcVmArm.Tables.TableWeights

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Tables
open NativeRustcVmArm.Vm.TableWeights
open NativeRustcVm (wordOf)

@[expose] public section

/-- The environment of the entry state: the frame, region 0; the heights, region 1. -/
abbrev env0 (m0 : MachineData) : Env := Env.ofMachine m0 [(fb m0, 240), (rg m0 .X1, 48)]

/-- The frame words both entry paths store: `out` and the saved registers. -/
def xsyms : List (Nat × Sym) :=
  [(8, .reg .X0), (144, .reg .X29), (152, .reg .X30), (160, .reg .X28), (168, .reg .X27),
    (176, .reg .X26), (184, .reg .X25), (192, .reg .X24), (200, .reg .X23),
    (208, .reg .X22), (216, .reg .X21), (224, .reg .X20), (232, .reg .X19)]

/-- The frame words `b0` then `b1` store: the loop's kept words. -/
def ksyms : List (Nat × Sym) :=
  [(8, .reg .X0), (72, .reg .X3),
    (64, .bin .add .W64 (.reg .X4) (.un (.shift .LSL 4) .W64 (.reg .X5))),
    (56, .load 1 0 8), (48, .load 1 8 8), (40, .load 1 16 8), (32, .load 1 24 8),
    (24, .load 1 32 8), (16, .load 1 40 8),
    (144, .reg .X29), (152, .reg .X30), (160, .reg .X28), (168, .reg .X27),
    (176, .reg .X26), (184, .reg .X25), (192, .reg .X24), (200, .reg .X23),
    (208, .reg .X22), (216, .reg .X21), (224, .reg .X20), (232, .reg .X19)]

/-- What the entry blocks leave: SP the frame's base, writes only in the frame, the words `L`,
the six weights `1`. -/
structure EntryBlock (L : List (Nat × Sym)) (S : SState) : Prop where
  sp : S.sp = .ptr 0 0
  writes : FrameWrites S 240
  slots : ∀ p ∈ L, loadSym S.mem 0 p.1 8 = p.2
  le : ∀ p ∈ L, p.1 + 8 ≤ 240
  ones : ∀ i < 5, (lo i).after S = some (.lit 1) ∧ (hi i).after S = some (.lit 0)
  x0 : S.reg .X0 = some (.lit 1)
  x9 : S.reg .X9 = some (.lit 0)

end

public section

variable {m0 : MachineData}

theorem entryB_b1 : EntryBlock ksyms (after b1 (after b0 entryS)) ∧
    (after b1 (after b0 entryS)).reg .X22 = some (.lit 0) ∧
    (after b1 (after b0 entryS)).reg .X23 = some (.bin .add .W64 (.reg .X2) (.lit 8)) ∧
    (after b1 (after b0 entryS)).reg .X27 = some (.reg .X4) := by
  rw [after_eq run_b1]
  exact ⟨⟨rfl, rfl, by decide, by decide, by decide, rfl, rfl⟩, rfl, rfl, rfl⟩

theorem entryB_b12 : EntryBlock xsyms (after b12 (after b0 entryS)) := by
  rw [after_eq run_b12]
  exact ⟨rfl, rfl, by decide, by decide, by decide, rfl, rfl⟩

section
variable [Labels]

theorem ksyms_eval :
    ksyms.map (fun p ↦ (p.1, p.2.eval (env0 m0))) = kslots m0 := by
  have hw : ∀ j, (env0 m0).load 1 (8 * j) 8 = hword m0 j := fun j => by rw [load8]; rfl
  have h64 : (Sym.bin .add .W64 (.reg .X4) (.un (.shift .LSL 4) .W64 (.reg .X5))).eval (env0 m0) =
      rg m0 .X4 + rg m0 .X5 <<< 4 := by
    simp only [Sym.eval, BinOp.apply, UnOp.apply, low_W64, ext_W64, shiftW, Env.ofMachine_regs]
  simp only [ksyms, kslots, List.map_cons, List.map_nil, h64]
  rw [← hw 0, ← hw 1, ← hw 2, ← hw 3, ← hw 4, ← hw 5]
  rfl

theorem xsyms_eval :
    xsyms.map (fun p ↦ (p.1, p.2.eval (env0 m0))) = xslots m0 := rfl

omit [Labels] in
/-- The entry's environment: well formed. -/
theorem wf0 (hc : Ctx m0) : (env0 m0).WF :=
  Env.wf_of ⟨⟨(FrameOk.mapped ⟨hc.geo.al, hc.geo.lo, hc.geo.hi, hc.geo.map⟩), hc.geo.hi⟩,
    ⟨hc.hts.1.1, hc.hts.1.2⟩, trivial⟩
    (List.pairwise_pair.mpr (hc.hts.apart_frame hc.stk))

/-- The entry state in its environment. -/
theorem match0 (hc : Ctx m0) : Match (env0 m0) entryS m0 :=
  match_ofMachine ⟨rfl, fun _ => hc.geo.al, rfl, fun h => absurd h (by decide), trivial⟩
    (by
      simp only [Sym.eval, Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
        Option.getD_some, fb]
      rw [show (240 : Int) = ((240 : Nat) : Int) from rfl, BitVec.ofInt_natCast,
        BitVec.sub_add_cancel])
    ⟨by simp [Sym.eval], trivial⟩ trivial trivial trivial

/-- The frame words an entry block leaves. -/
theorem fw_entry {L : List (Nat × Sym)} {S : SState} {st : MachineData} (hc : Ctx m0)
    (hm : Match (env0 m0) S st) (hb : EntryBlock L S) :
    ∀ p ∈ L.map (fun p ↦ (p.1, p.2.eval (env0 m0))), fw m0 st p.1 = p.2 := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  rw [fw, match_wordOf hm (wf0 hc) (r := 0) (b := fb m0) (sz := 240) rfl (hb.le q hq),
    hb.slots q hq]

/-- The memory an entry block leaves. -/
theorem same_entry {S : SState} {st : MachineData} (hc : Ctx m0)
    (hm : Match (env0 m0) S st) (hw : FrameWrites S 240) :
    SameOutside m0.dmem st.dmem (StackArea (fb m0) ewMulStack 240) := fun p hp =>
  hm.sameOutside (wf0 hc) p fun h => hp (written_frame hc.geo hw h)

/-- The weights an entry block sets. -/
theorem w_entry {L : List (Nat × Sym)} {S : SState} {st : MachineData} (hc : Ctx m0)
    (hm : Match (env0 m0) S st) (hb : EntryBlock L S) (c : Nat) (hc0 : c = 0) :
    (∀ j < 5, WAt m0 st j ((W m0 c).getD j 0)) ∧
      rg st .X0 = ((W m0 c).getD 5 0).c0.toBitVec ∧
      rg st .X9 = ((W m0 c).getD 5 0).c1.toBitVec := by
  subst hc0
  have h1 : ∀ j < 6, (W m0 0).getD j 0 = 1 := fun j hj => by
    rw [W, twPrefix_zero]
    simp [Array.getD, size_H, hj]
  refine ⟨fun j hj => ?_, ?_, ?_⟩
  · obtain ⟨hl, hh⟩ := hb.ones j hj
    rw [h1 j (by omega)]
    exact ⟨Pl.val_keep (wf0 hc) hm lo_ok hl, Pl.val_keep (wf0 hc) hm hi_ok hh⟩
  · rw [h1 5 (by omega)]
    exact hm.regs .X0 _ hb.x0
  · rw [h1 5 (by omega)]
    exact hm.regs .X9 _ hb.x9

end

variable [Host] {k : Nat}

/-- **The entry**: the loop head with no coordinate done, or (an empty point) the exit. -/
theorem entry_step (hp : Placed code k) (hc : Ctx m0) :
    Eventually (step1 Host.exe)
      (fun st => (st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.TableWeights.b10Offset) ∧ It m0 0 st.data) ∨
        (st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.TableWeights.b13Offset) ∧ Fin m0 st.data))
      ⟨m0, Host.addrOf (k + NativeRustcVmArm.Vm.TableWeights.b0Offset)⟩ := by
  refine exec_then (hb0 hp) run_b0 (wf0 hc) (match0 hc) fun st1 hm1 hpc1 => ?_
  have hm1' : Match (env0 m0) (after b0 entryS) st1.data := by rw [after_eq run_b0]; exact hm1
  simp only [PcOk, SBool.eval, CmpOp.apply, Sym.eval, low_W64, Env.ofMachine_regs] at hpc1
  by_cases hn : n m0 = 0
  · -- an empty point: `b12`, the exit
    have h5 : (m0.regs.getXReg .X5).toBitVec = BitVec.ofNat 64 0 := by
      apply BitVec.eq_of_toNat_eq
      show n m0 = (BitVec.ofNat 64 0).toNat
      rw [hn]; rfl
    simp only [h5, beq_self_eq_true, ↓reduceIte, lbl_6 hp] at hpc1
    refine exec_at (hb12 hp) run_b12 (wf0 hc) hpc1 hm1' fun st2 hm2 hpc2 => .done _
      (Or.inr ⟨hpc2.trans (addr_eq (by rw [Nat.add_assoc, NativeRustcVmArm.Vm.TableWeights.b12_next])), ?_⟩)
    have hm2' : Match (env0 m0) (after b12 (after b0 entryS)) st2.data := by
      rw [after_eq run_b12]; exact hm2
    have hb := entryB_b12
    obtain ⟨hw, hx0, hx9⟩ := w_entry hc hm2' hb (n m0) hn
    refine ⟨⟨?_, ?_, same_entry hc hm2' hb.writes, hm2'.kept (wf0 hc)⟩, hw, hx0, hx9⟩
    · rw [hm2'.sp, hb.sp]; simp [Sym.eval]
    · rw [← xsyms_eval]; exact fw_entry hc hm2' hb
  · -- `b1`, the loop head
    have h5 : ¬(m0.regs.getXReg .X5).toBitVec = BitVec.ofNat 64 0 := fun h => hn (by
      have := congrArg BitVec.toNat h
      exact this)
    simp only [beq_false_of_ne h5, Bool.false_eq_true, ↓reduceIte] at hpc1
    refine exec_at (hb1 hp) run_b1 (wf0 hc) (hpc1.trans (addr_eq (by rw [Nat.add_assoc, NativeRustcVmArm.Vm.TableWeights.b0_next]))) hm1'
      fun st2 hm2 hpc2 => .done _ (Or.inl ⟨by rw [hpc2, lbl_4 hp], ?_⟩)
    have hm2' : Match (env0 m0) (after b1 (after b0 entryS)) st2.data := by
      rw [after_eq run_b1]; exact hm2
    obtain ⟨hb, h22, h23, h27⟩ := entryB_b1
    obtain ⟨hw, hx0, hx9⟩ := w_entry hc hm2' hb 0 rfl
    refine ⟨by omega, ⟨?_, ?_, same_entry hc hm2' hb.writes, hm2'.kept (wf0 hc)⟩, ?_, ?_, ?_,
      hw, hx0, hx9⟩
    · rw [hm2'.sp, hb.sp]; simp [Sym.eval]
    · rw [← ksyms_eval]; exact fw_entry hc hm2' hb
    · rw [show rg st2.data .X22 = _ from hm2'.regs .X22 _ h22]; rfl
    · rw [show rg st2.data .X23 = _ from hm2'.regs .X23 _ h23]
      simp [Sym.eval, BinOp.apply]
    · rw [show rg st2.data .X27 = _ from hm2'.regs .X27 _ h27]
      simp [Sym.eval]

end

end NativeRustcVmArm.Tables.TableWeights
