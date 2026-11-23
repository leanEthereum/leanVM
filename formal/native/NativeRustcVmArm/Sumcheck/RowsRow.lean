module

public import NativeRustcVmArm.Code.Vm.RowsRow.Names
public import NativeRustcVmArm.Sumcheck.RowsRow.Exec
public import NativeRustcVmArm.Sumcheck.Common
public import NativeRustcVmArm.Spec.Sumcheck

/-!
# `Rows::row`

One block: the slice from word `start = 193 j + 1` of the openings, `width` words, when it fits
in them (no carry, `start + width ≤ len`), else the empty slice. For `j` below the count of rows
`RowsAt` describes it fits: the row's words.
-/

namespace NativeRustcVmArm.Sumcheck.RowsRow

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.RowsRow
open NativeVm LeanVM.Protocol.Compile NativeRustcVm.Sumcheck NativeRustcVm.Transcript

public section

variable [Host] {k : Nat}

/-- **`Rows::row`'s contract.** -/
theorem rowsRow_spec (hp : Placed code k) (p : BitVec 64) (rows : Array (Array UInt64)) :
    Spec (Labels.label NativeRustcVmArm.Vm.RowsRow.entryLabel) (RowsRowPre p rows) (RowsRowPost p rows) := by
  intro m ⟨⟨hp0, hsz, w, hw, hhdr, hrow⟩, hnw⟩
  have hentry : Labels.label NativeRustcVmArm.Vm.RowsRow.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.RowsRow.b0Offset) := hp.label (j := NativeRustcVmArm.Vm.RowsRow.entryOffset) NativeRustcVmArm.Vm.RowsRow.entry_at
  rw [hentry]
  have hk : b0.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.RowsRow.b0Offset) := b0_in_code.trans hp.1 (by simp [b0])
  let env := Env.ofMachine m [(m.regs.X0.toBitVec, 32)]
  have hmap : Mapped m.dmem m.regs.X0.toBitVec 32 := by
    have := NativeRustcVm.WordsAt.mapped hhdr
    exact this
  have hwf : env.WF := Env.wf_of ⟨⟨hmap, hnw⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hm : Match env entryS m :=
    match_ofMachine ⟨rfl, by simp, trivial⟩ rfl ⟨by simp [Sym.eval]; rfl, trivial⟩ trivial
      trivial trivial
  have hb : env.base 0 = m.regs.X0.toBitVec := rfl
  have hw0 : env.load 0 0 8 = p := by
    have := hhdr.getElem (i := 0) (by simp)
    rw [load_word (by rw [hb]; exact this)]; rfl
  have hw1 : env.load 0 8 8 = BitVec.ofNat 64 openingsWords := by
    have := hhdr.getElem (i := 1) (by simp)
    rw [load_word (by rw [hb]; exact this)]; rfl
  have hw3 : env.load 0 24 8 = BitVec.ofNat 64 w := by
    have := hhdr.getElem (i := 3) (by simp)
    rw [load_word (by rw [hb]; exact this)]; rfl
  refine exec_then hk run_b0 hwf hm fun st hm' hpc ↦ ?_
  have h0 := hm'.regs .X0 _ rfl
  have h1 := hm'.regs .X1 _ rfl
  sym_simp at h0 h1
  have hJ : env.regs XReg.X1 * 193#64 + 1#64 = BitVec.ofNat 64 (193 * m.regs.X1.toNat + 1) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, env, Env.ofMachine_regs]
    show (m.regs.X1.toNat * 193 % 2 ^ 64 + 1) % 2 ^ 64 = (193 * m.regs.X1.toNat + 1) % 2 ^ 64
    omega
  have hS : BitVec.ofNat 64 w + BitVec.ofNat 64 (193 * m.regs.X1.toNat + 1) =
      BitVec.ofNat 64 (w + (193 * m.regs.X1.toNat + 1)) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [hw1, hw3, hJ, hS] at h0 h1
  rw [hw0] at h0
  have hx30 : retOf st.data = retOf m := by
    have := hm'.regs .X30 _ rfl
    simp only [Sym.eval, env, Env.ofMachine_regs] at this
    simp only [retOf]
    rw [show st.data.regs.X30 = m.regs.X30 from UInt64.toBitVec_inj.mp this]
  refine Eventually.done _ ⟨hpc.trans hx30, fun hj ↦ ?_, Match.dmem_eq hm' hwf rfl,
    Match.saved hm hm' hwf rfl (by decide)⟩
  obtain ⟨hlen, hrj⟩ := hrow _ hj
  have hq : wireMaxQueries = 256 := rfl
  have hl : wireMaxLeafWords = 64 := rfl
  have ho : openingWords = 193 := rfl
  have hos : openingsWords = 49408 := rfl
  have hA : w + (193 * m.regs.X1.toNat + 1) < openingsWords := by
    rw [hos]; have := m.regs.X1.toNat_lt; omega
  have hult : (BitVec.ofNat 64 (w + (193 * m.regs.X1.toNat + 1))).ult
      (BitVec.ofNat 64 openingsWords) = true := by
    rw [BitVec.ult, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
    exact decide_eq_true hA
  have hun : (BitVec.ofNat 64 (w + (193 * m.regs.X1.toNat + 1))).unsigned =
      (BitVec.ofNat 64 w).unsigned + (BitVec.ofNat 64 (193 * m.regs.X1.toNat + 1)).unsigned := by
    simp only [BitVec.unsigned, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    push_cast; rfl
  have hz : (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 0#64)) ==
      BitVec.setWidth 32 0#64) = true := by decide
  simp only [hult, hun, Bool.true_or, bne_self_eq_false, Bool.not_false, ↓reduceIte, hz,
    Bool.not_true, Bool.false_eq_true] at h0 h1
  have hx1 : st.data.regs.X1.toBitVec = BitVec.ofNat 64 w := h1
  have hx0 : st.data.regs.X0.toBitVec = off p (8 * (1 + m.regs.X1.toNat * openingWords)) := by
    refine (show st.data.regs.X0.toBitVec = _ from h0).trans ?_
    rw [off]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, ho,
      show MemWidth.W64.bits = 64 from rfl]
    omega
  refine ⟨?_, hx0, ?_⟩
  · rw [← UInt64.toNat_toBitVec, hx1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hlen]
  · rw [hx0, Match.dmem_eq hm' hwf rfl]
    exact hrj
end

end NativeRustcVmArm.Sumcheck.RowsRow
