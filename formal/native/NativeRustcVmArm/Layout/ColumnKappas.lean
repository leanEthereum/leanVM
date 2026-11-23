module

public import NativeRustcVmArm.Code.Vm.ColumnKappas.Names
public import NativeRustcVmArm.Layout.ColumnKappas.Exec
public import NativeRustcVmArm.Layout.Body
public import NativeVm.Math.Layout

/-!
# `column_kappas` on AArch64

**`columnKappas_spec`**: rustc's `column_kappas(out, log_memory, log_bytecode, heights)`, placed
anywhere in the program, meets `ColumnKappasPre`/`ColumnKappasPost`. Its one block stores column
`c`'s log-size from its source `srcOf c` (`colSym`), which is the model's `columnKappas`
(`NativeVm.Math.Layout.columnKappas_getD`, `kapF`).
-/

namespace NativeRustcVmArm.Layout.ColumnKappas

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.ColumnKappas NativeVm.Model
open NativeVm.Math.Layout (kapF columnKappas_getD columnKappas_size')
open NativeRustcVm (wordOf wordsOf WordAt WordsAt)

public section

/-- A source's value: the memory's and the bytecode's log-sizes, `q_keccak`'s, a table's. -/
def srcNat (lm lb : Nat) (hs : Array Nat) : Nat → Nat
  | 0 => lm
  | 1 => lb
  | 2 => hs.getD 5 0 + 6
  | s => hs.getD (s - 3) 0

theorem kapF_eq (lm lb : Nat) (hs : Array Nat) (c : Nat) :
    kapF lm lb hs c = srcNat lm lb hs (srcOf c) := by
  unfold kapF srcOf
  split_ifs <;> rfl

theorem srcOf_le (c : Nat) : srcOf c ≤ 8 := by
  unfold srcOf
  split_ifs <;> decide

variable [Host] {k : Nat}

theorem lbl_entry (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.ColumnKappas.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.ColumnKappas.b0Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.ColumnKappas.entryOffset) NativeRustcVmArm.Vm.ColumnKappas.entry_at

/-- **`column_kappas` meets its contract.** -/
theorem columnKappas_spec (hp : Placed code k) :
    Spec (Labels.label NativeRustcVmArm.Vm.ColumnKappas.entryLabel) ColumnKappasPre ColumnKappasPost := by
  rintro m ⟨hro, hrh, hap, hq⟩
  rw [lbl_entry hp]
  let env := Env.ofMachine m [(m.regs.X0.toBitVec, kappasBytes), (m.regs.X3.toBitVec, 48)]
  have hwf : env.WF := Env.wf_of ⟨hro, hrh, trivial⟩ (List.pairwise_pair.mpr hap)
  have hm : Match env entryS m :=
    match_ofMachine ⟨rfl, nofun, rfl, nofun, trivial⟩ rfl
      ⟨by show _ = m.regs.X0.toBitVec + BitVec.ofInt 64 0; rw [ofInt_zero, BitVec.add_zero]; rfl,
       by show _ = m.regs.X3.toBitVec + BitVec.ofInt 64 0; rw [ofInt_zero, BitVec.add_zero]; rfl,
       trivial⟩ trivial trivial trivial
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_b0 hwf hm fun st hm' hpc ↦ ?_
  obtain ⟨hv, hw, hk⟩ := after_eq run_b0 ▸ b0_facts
  have hx30 : env.regs .X30 = m.regs.X30.toBitVec := rfl
  refine .done _ ⟨?_, ?_, ?_, Match.saved hm hm' hwf rfl hk⟩
  · simp only [PcOk] at hpc
    exact hpc.trans (retOf_of_x30 hm' rfl hx30)
  · let hs := natsOf m m.regs.X3 nTables
    have hhs : ∀ t < 6, hs.getD t 0 = (env.load 1 (8 * t) 8).toNat := by
      intro t ht
      rw [show hs = natsOf m m.regs.X3 6 from rfl, natsOf_getD m _ ht, Arrays.load8_eq]
      rfl
    have hval : ∀ s ≤ 8, UInt64.ofBitVec ((colSym s).eval env) =
        (srcNat m.regs.X1.toNat m.regs.X2.toNat hs s).toUInt64 := by
      intro s hs8
      apply UInt64.toNat_inj.mp
      rw [Nat.toUInt64, UInt64.toNat_ofNat']
      match s, hs8 with
      | 0, _ => simp [colSym, srcNat, Sym.eval, env]; rfl
      | 1, _ => simp [colSym, srcNat, Sym.eval, env]; rfl
      | 2, _ =>
        have h5 := hhs 5 (by decide)
        have hq' : hs.getD 5 0 + 6 < 2 ^ 64 := hq
        simp only [colSym, srcNat, Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64]
        rw [UInt64.toNat_ofBitVec, BitVec.toNat_add, BitVec.toNat_ofNat, ← h5]
      | 3, _ =>
        simp only [colSym, srcNat, Sym.eval, hhs 0 (by decide), UInt64.toNat_ofBitVec]
        exact (Nat.mod_eq_of_lt (BitVec.isLt _)).symm
      | 4, _ =>
        simp only [colSym, srcNat, Sym.eval, hhs 1 (by decide), UInt64.toNat_ofBitVec]
        exact (Nat.mod_eq_of_lt (BitVec.isLt _)).symm
      | 5, _ =>
        simp only [colSym, srcNat, Sym.eval, hhs 2 (by decide), UInt64.toNat_ofBitVec]
        exact (Nat.mod_eq_of_lt (BitVec.isLt _)).symm
      | 6, _ =>
        simp only [colSym, srcNat, Sym.eval, hhs 3 (by decide), UInt64.toNat_ofBitVec]
        exact (Nat.mod_eq_of_lt (BitVec.isLt _)).symm
      | 7, _ =>
        simp only [colSym, srcNat, Sym.eval, hhs 4 (by decide), UInt64.toNat_ofBitVec]
        exact (Nat.mod_eq_of_lt (BitVec.isLt _)).symm
      | 8, _ =>
        simp only [colSym, srcNat, Sym.eval, hhs 5 (by decide), UInt64.toNat_ofBitVec]
        exact (Nat.mod_eq_of_lt (BitVec.isLt _)).symm
    unfold natWords
    rw [NativeRustcVm.wordsAt_iff]
    intro c hc
    have hc' : c < 158 := by simpa [columnKappas_size'] using hc
    have := Match.wordAt_write hm' (r := 0) (o := 8 * c) rfl
      (by show 8 * c + 8 ≤ 1264; omega) (hv c hc')
    rw [hval _ (srcOf_le c), ← kapF_eq, ← columnKappas_getD _ _ _ hc'] at this
    have hc2 : c < (columnKappas m.regs.X1.toNat m.regs.X2.toNat hs).size := by
      rw [columnKappas_size']; exact hc'
    simp only [Array.getD, hc2, dite_true] at this
    simpa using this
  · exact fun p hp' ↦ same_of_region hm' hwf (r := 0) rfl hw p fun h ↦ hp' (Or.inl h)

end

end NativeRustcVmArm.Layout.ColumnKappas
