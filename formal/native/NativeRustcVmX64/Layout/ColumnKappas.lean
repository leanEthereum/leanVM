module

public import NativeRustcVmX64.Layout.ColumnKappas.Exec
public import NativeVm.Math.Layout
public import NativeRustcVmX64.Code.Vm.ColumnKappas.Names

/-!
# `column_kappas` on x86-64

**`columnKappas_spec`**: rustc's `column_kappas(out, log_memory, log_bytecode, heights)`, placed
anywhere in the program, meets `ColumnKappasPre`/`ColumnKappasPost`. Its one block pushes RBX,
stores column `c`'s log-size from its source `srcOf c` (`colSym`), which is the model's
`columnKappas` (`NativeVm.Math.Layout.columnKappas_getD`, `kapF`), pops RBX and returns
(`leaf_run`).
-/

namespace NativeRustcVmX64.Layout.ColumnKappas

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.ColumnKappas NativeVm.Model
open NativeVm.Math.Layout (kapF columnKappas_getD columnKappas_size')
open NativeRustcVm (wordOf wordsOf WordAt WordsAt)
open NativeRustcVmX64.Transcript (after after_eq frameEnv infix_of)

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

/-- **`column_kappas` meets its contract.** -/
theorem columnKappas_spec (hp : Placed code k) :
    Spec (Labels.label NativeRustcVmX64.Vm.ColumnKappas.entryLabel) ColumnKappasPre ColumnKappasPost := by
  rintro m ⟨hst, hro, hoo, hrh, hoh, hap, hq⟩
  rw [show Labels.label NativeRustcVmX64.Vm.ColumnKappas.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.ColumnKappas.b0Offset) from hp.label NativeRustcVmX64.Vm.ColumnKappas.entry_at]
  let rest : List (BitVec 64 × Nat) := [(reg m .rdi, kappasBytes), (reg m .rcx, 48)]
  let env := frameEnv m m 8 rest
  have hrest : ∀ x ∈ rest, NativeRustcVm.Mapped m.dmem x.1 x.2 ∧ NativeRustcVm.NoWrap x.1 x.2 := by
    intro x hx
    simp only [rest, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact hro
    · exact hrh
  have hapl : ((stackBelow m 8, 8 + 8) :: rest).Pairwise
      fun x y ↦ NativeRustcVm.Apart x.1 x.2 y.1 y.2 :=
    Transcript.pairwise3 (Transcript.Apart.symm' hoo) (Transcript.Apart.symm' hoh) hap
  have hwf := Transcript.frame_wf (m0 := m) (d := m) (F := 8) (rest := rest)
    (vars := fun _ ↦ 0) (ret := 0)
    ⟨Transcript.frame_mapped hst le_rfl, Transcript.frame_noWrap hst le_rfl⟩ hrest hapl
  have hm : Match env entryS m :=
    match_ofMachine ⟨rfl, rfl, rfl, trivial⟩
      ⟨Transcript.match_rsp, Transcript.known_ptr rfl rfl, Transcript.known_ptr rfl rfl, trivial⟩
      trivial trivial trivial
  refine leaf_run (st := ⟨m, _⟩) (infix_of b0_in_code (by simp [b0]) hp) run_b0
    (after_eq run_b0 ▸ b0_facts).2.2 hst le_rfl rfl Transcript.Frame.entry hrest hapl hm
    (Q := fun d ↦ WordsAt d.dmem (reg m .rdi) (natWords (columnKappas (reg m .rsi).toNat
      (reg m .rdx).toNat (natsOf m (reg m .rcx) nTables))) ∧
      SameOutside m.dmem d.dmem (fun p ↦ InRange (reg m .rdi) kappasBytes p ∨
        InRange (stackBelow m columnKappasStack) columnKappasStack p))
    (fun d hm' ↦ ?_) |>.mono fun s ⟨h1, h2, ⟨h3, h4⟩, h5⟩ ↦ ⟨h1, h2, h3, h4, h5⟩
  obtain ⟨hv, hw, -⟩ := after_eq run_b0 ▸ b0_facts
  refine ⟨?_, fun p hp' ↦ ?_⟩
  · let hs := natsOf m (reg m .rcx) nTables
    have hhs : ∀ t < 6, hs.getD t 0 = (env.load 2 (8 * t) 8).toNat := by
      intro t ht
      rw [show hs = natsOf m (reg m .rcx) 6 from rfl, natsOf_getD m _ ht, Arrays.load8_eq]
      rfl
    have hval : ∀ s ≤ 8, UInt64.ofBitVec ((colSym s).eval env) =
        (srcNat (reg m .rsi).toNat (reg m .rdx).toNat hs s).toUInt64 := by
      intro s hs8
      apply UInt64.toNat_inj.mp
      rw [Nat.toUInt64, UInt64.toNat_ofNat']
      match s, hs8 with
      | 0, _ =>
        simp only [colSym, srcNat, Sym.eval, env, Env.ofMachine_regs, UInt64.toNat_ofBitVec]
        exact (Nat.mod_eq_of_lt (BitVec.isLt _)).symm
      | 1, _ =>
        simp only [colSym, srcNat, Sym.eval, env, Env.ofMachine_regs, UInt64.toNat_ofBitVec]
        exact (Nat.mod_eq_of_lt (BitVec.isLt _)).symm
      | 2, _ =>
        have h5 := hhs 5 (by decide)
        have hq' : hs.getD 5 0 + 6 < 2 ^ 64 := hq
        simp only [colSym, srcNat, Sym.eval, BinOp.apply, low_W64, ext_W64]
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
    have := Arrays.wordAt_of_write hm' (r := 1) (o := 8 * c) rfl
      (by show 8 * c + 8 ≤ 1264; omega) (hv c hc')
    rw [hval _ (srcOf_le c), ← kapF_eq, ← columnKappas_getD _ _ _ hc'] at this
    have hc2 : c < (columnKappas (reg m .rsi).toNat (reg m .rdx).toNat hs).size := by
      rw [columnKappas_size']; exact hc'
    simp only [Array.getD, hc2, dite_true] at this
    simpa using this
  · refine hm'.get?_mem0 hwf fun hW ↦ hp' ?_
    obtain ⟨e, he, hin⟩ := written_in hwf (rs := [(0, 8), (1, 1264)])
      (by
        intro e he
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl
        · exact ⟨16, rfl, by decide⟩
        · exact ⟨1264, rfl, le_rfl⟩) hw hW
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact Or.inr hin
    · exact Or.inl hin

end

end NativeRustcVmX64.Layout.ColumnKappas
