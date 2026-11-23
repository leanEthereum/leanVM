module

public import NativeRustcVmArm.Wire.RdRows.Mem

/-!
# `rd_rows`' return and the zeros before a row (rows of `rw > 0` words)

The return (`b2`, `ret_spec`) with the result `X23`. For `rw > 0` (`RegA`: the registers of the
loop over the leaves), the zeros before row `i` (`ZA`): four at a time (`b8`, `VecA`), then one at
a time (`b10`, `SclA`), up to the call reading the row (`CallA`).
-/

namespace NativeRustcVmArm.Wire.RdRows

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt InAny Region)
open NativeRustcVmArm.Vm.RdRows
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

@[expose] public section

/-- The registers the loop over the leaves keeps (`rw > 0`). -/
def regsA : List XReg := [.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X27, .X28, .X29]

/-- **The loop over the leaves at leaf `i`** (`rw > 0`): the leaf, the widths, the reader, the
result so far, the end, the zeros' counts and the frame's word. -/
structure RegA (m0 : MachineData) (i : Nat) (rows : List (List K)) (s : MachineData) : Prop where
  fr : Frm m0 s
  x19 : (s.regs.getXReg .X19).toBitVec = leaf m0 i
  x20 : s.regs.getXReg .X20 = m0.regs.X2
  x21 : (s.regs.getXReg .X21).toBitVec = rdr m0
  x22 : s.regs.getXReg .X22 = m0.regs.X3
  x23 : (s.regs.getXReg .X23).toNat = flag rows
  x24 : (s.regs.getXReg .X24).toBitVec = leaf m0 (nr m0)
  x25 : 0 < zc m0 → (s.regs.getXReg .X25).toNat = zc m0 - 1
  x27 : (s.regs.getXReg .X27).toBitVec = leaf m0 i + BitVec.ofNat 64 16
  x28 : (s.regs.getXReg .X28).toNat = 8 * zc m0
  x29 : 0 < zc m0 → (s.regs.getXReg .X29).toNat = 8 * q4 (zc m0)
  q : 0 < zc m0 → WordAt s.dmem (base m0 112 + BitVec.ofNat 64 8) (q4 (zc m0)).toUInt64
  lt : i < nr m0
  rw0 : 0 < rw m0

/-- **Zeros before row `i`**: `t` of them written. -/
structure ZA (m0 : MachineData) (bp : BitVec 64) (B : List UInt8) (c i t : Nat)
    (rows : List (List K)) (ci : Nat) (s : MachineData) : Prop where
  reg : RegA m0 i rows s
  kept : Kept m0 bp B c i rows ci s.dmem
  x26 : (s.regs.getXReg .X26).toBitVec = leaf m0 i + BitVec.ofNat 64 (8 * zc m0)
  zs : WordsAt s.dmem (leaf m0 i) (List.replicate t 0)
  le : t ≤ zc m0

end

public section

variable {m0 : MachineData} {bp : BitVec 64} {B : List UInt8} {c : Nat}

theorem RegA.keep {i : Nat} {rows : List (List K)} {s s' : MachineData} (h : RegA m0 i rows s)
    (hfr : Frm m0 s') (hr : ∀ r ∈ regsA, s'.regs.getXReg r = s.regs.getXReg r)
    (hq : 0 < zc m0 → WordAt s'.dmem (base m0 112 + BitVec.ofNat 64 8) (q4 (zc m0)).toUInt64) :
    RegA m0 i rows s' where
  fr := hfr
  x19 := by rw [hr .X19 (by simp [regsA])]; exact h.x19
  x20 := by rw [hr .X20 (by simp [regsA])]; exact h.x20
  x21 := by rw [hr .X21 (by simp [regsA])]; exact h.x21
  x22 := by rw [hr .X22 (by simp [regsA])]; exact h.x22
  x23 := by rw [hr .X23 (by simp [regsA])]; exact h.x23
  x24 := by rw [hr .X24 (by simp [regsA])]; exact h.x24
  x25 := by rw [hr .X25 (by simp [regsA])]; exact h.x25
  x27 := by rw [hr .X27 (by simp [regsA])]; exact h.x27
  x28 := by rw [hr .X28 (by simp [regsA])]; exact h.x28
  x29 := by rw [hr .X29 (by simp [regsA])]; exact h.x29
  q := hq
  lt := h.lt
  rw0 := h.rw0

/-- Registers a block keeps as their atoms. -/
theorem regs_keep [Labels] {env : Env} {S S' : SState} {s s' : MachineData} (hm : Match env S s)
    (hm' : Match env S' s') {rs : List XReg}
    (h : ∀ r ∈ rs, S.reg r = some (.reg r) ∧ S'.reg r = some (.reg r)) :
    ∀ r ∈ rs, s'.regs.getXReg r = s.regs.getXReg r := fun r hr ↦
  Match.reg_eq hm hm' (h r hr).1 (h r hr).2

theorem trunc_small {x : BitVec 64} (h : x.toNat < 2 ^ 32) : UnOp.apply .trunc .W32 x = x :=
  Sym.ext_low_W32 h

theorem flag_le (rows : List (List K)) : flag rows ≤ 1 := by
  unfold flag; split <;> omega

theorem x0_flag {x : UInt64} {rows : List (List K)} (h : x.toNat = flag rows) :
    x = if ∀ y ∈ rows, y.getD 0 0 = 0 then 1 else 0 := by
  apply UInt64.toNat_inj.mp
  rw [h]
  unfold flag
  split <;> rfl

variable [Host] {k : Nat}

/-- **The return** (`b2`) with the result in `X23`. -/
theorem ret_spec (hp : Placed code k) (G : Geo m0 bp B)
    (hR : ReaderAt m0.dmem (rdr m0) bp B c) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.RdRows.b2Offset)) (hfr : Frm m0 st.data)
    (hres : match rdRows B (rw m0) (nr m0) c with
      | some (rows, c') => (st.data.regs.getXReg .X23).toNat = flag rows ∧
          LeavesAt st.data.dmem (lv m0) (rows.map fun x ↦ paddedLeaf x (lw m0)) ∧
          ReaderAt st.data.dmem (rdr m0) bp B c'
      | none => (st.data.regs.getXReg .X23).toNat = 2) :
    Eventually (step1 Host.exe) (Post m0) st := by
  have hst := G.g.st
  have hwf := frEnv_wf hst hfr
  have hm := frEnv_match hst hfr
  refine exec_at (infix_of b2_in_code (by simp [b2]) hp) run_b2 hwf hpc hm fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hret, hsv⟩ := hfr.exit hm1 hwf (by decide)
  have hd : st1.data.dmem = st.data.dmem := hm1.dmem_eq hwf rfl
  have hx0 : st1.data.regs.X0.toBitVec = (st.data.regs.getXReg .X23).toBitVec := by
    have h := hm1.regs .X0 _ rfl
    simp only [Sym.eval, Env.ofMachine_regs] at h
    rw [trunc_small] at h
    · exact h
    · split at hres
      · have := flag_le ‹List (List K)›
        rw [UInt64.toNat_toBitVec]; omega
      · rw [UInt64.toNat_toBitVec]; omega
  have hx0' : st1.data.regs.X0 = st.data.regs.getXReg .X23 := UInt64.toBitVec_inj.mp hx0
  refine .done _ ⟨by simp only [PcOk] at hpc1; rw [hpc1, hret], fun bp' B' c' hR' ↦ ?_, ?_, hsv⟩
  · obtain ⟨rfl, rfl, rfl⟩ := hR.unique hR'
    split at hres
    · rename_i rows c1 he
      rw [he]
      exact ⟨x0_flag (by rw [hx0']; exact hres.1), by rw [hd]; exact hres.2.1,
        by rw [hd]; exact hres.2.2⟩
    · rename_i he
      rw [he]
      apply UInt64.toNat_inj.mp
      rw [hx0']; exact hres
  · intro p hp
    rw [hd]
    refine hfr.same p ?_
    rintro (h | h | h)
    · exact hp ⟨stackR m0 rdRowsStack, by simp, h⟩
    · exact hp ⟨curRegion (rdr m0), by simp, h⟩
    · exact hp ⟨_, List.mem_cons_self, h⟩

end

end NativeRustcVmArm.Wire.RdRows
