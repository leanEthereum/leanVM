module

public import NativeRustcVmX64.Field.Frame
public import NativeRustcVmX64.Spec.Field

/-!
# The frame's environment, and functions without calls (x86-64)

`frameEnv m0 m F`: the environment of the machine state `m` with region 0 the `F` bytes below the
entry `m0`'s RSP and the return address at RSP (`frame_wf`); `frameS F` describes the entry
(`match_frame`). Its offset `F` holds the return address (`load_ret`).

`leaf_done`: a function without calls whose blocks, run from `frameS F` in the entry's frame
environment, end in `ret` with RSP at the offset `F + 8`, the callee-saved registers kept and
writes only below offset `F`, meets the frame part of its contract: back at the return address,
RSP 8 above, nothing changed outside the `F` bytes below RSP, `Saved`.
-/

namespace NativeRustcVmX64.Field

open NativeRustcX64 NativeRustcX64.Sym

@[expose] public section

/-- The environment of `m` with region 0 the `F` bytes below `m0`'s RSP and the return address. -/
abbrev frameEnv (m0 m : MachineData) (F : Nat) (vars : Nat → BitVec 64 := fun _ ↦ 0)
    (ret : BitVec 64 := 0) : Env :=
  Env.ofMachine m [(stackBelow m0 F, F + 8)] vars ret

end

public section

variable {m0 m : MachineData} {F : Nat}

theorem stackBelow_toNat' (h : F ≤ (rspOf m0).toNat) :
    (stackBelow m0 F).toNat = (rspOf m0).toNat - F :=
  toNat_sub_of_le _ _ (by rw [BitVec.toNat_ofNat]; have := (rspOf m0).isLt; omega) |>.trans
    (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := (rspOf m0).isLt; omega)])

theorem frame_noWrap (h : StackOk m0 F) : (stackBelow m0 F).toNat + (F + 8) ≤ 2 ^ 64 := by
  rw [stackBelow_toNat' h.1]
  have := h.1
  have := h.2.1
  omega

theorem frame_wf {vars : Nat → BitVec 64} {ret : BitVec 64} (h : StackOk m0 F)
    (hk : Kept m0.dmem m.dmem) : (frameEnv m0 m F vars ret).WF :=
  Env.wf_of ⟨⟨fun i hi ↦ hk _ (h.2.2 i hi), frame_noWrap h⟩, trivial⟩
    (List.pairwise_singleton _ _)

theorem frame_base {vars : Nat → BitVec 64} {ret : BitVec 64} :
    (frameEnv m0 m F vars ret).base 0 = stackBelow m0 F := rfl

/-- `F` above the frame's base is RSP. -/
theorem frame_add (F j : Nat) :
    stackBelow m0 F + BitVec.ofNat 64 (F + j) = rspOf m0 + BitVec.ofNat 64 j := by
  rw [stackBelow, BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]

theorem frame_rsp (F o : Nat) :
    stackBelow m0 F + BitVec.ofInt 64 ((F + o : Nat) : Int) = rspOf m0 + BitVec.ofNat 64 o := by
  rw [BitVec.ofInt_natCast, frame_add]

/-- The entry's state in its frame environment. -/
theorem match_frame [Labels] {vars : Nat → BitVec 64} {ret : BitVec 64} :
    Match (frameEnv m0 m0 F vars ret) (frameS F) m0 :=
  match_ofMachine ⟨rfl, trivial⟩
    ⟨show rspOf m0 = stackBelow m0 F + BitVec.ofInt 64 (F : Int) by
        rw [show ((F : Nat) : Int) = ((F + 0 : Nat) : Int) from rfl, frame_rsp F 0]
        simp, trivial⟩
    trivial trivial trivial

/-- **The return address**: the frame's offset `F`, while `m` keeps the entry's 8 bytes at RSP. -/
theorem load_ret {vars : Nat → BitVec 64} {ret : BitVec 64} (h : StackOk m0 F)
    (hsame : ∀ j < 8, m.dmem.get? (rspOf m0 + BitVec.ofNat 64 j) =
      m0.dmem.get? (rspOf m0 + BitVec.ofNat 64 j)) :
    Int64.ofBitVec ((frameEnv m0 m F vars ret).load 0 F 8) = retOf m0 := by
  have hget : ∀ j < 8, m0.dmem.get? (rspOf m0 + BitVec.ofNat 64 j) =
      some ((m0.dmem.get? (rspOf m0 + BitVec.ofNat 64 j)).getD 0) := fun j hj ↦ by
    have := h.2.2 (F + j) (by omega)
    rw [show rspOf m0 - BitVec.ofNat 64 F = stackBelow m0 F from rfl, frame_add] at this
    revert this
    cases m0.dmem.get? (rspOf m0 + BitVec.ofNat 64 j) <;> simp
  rw [retOf, loadInt_of_get? _ _ 8 _ hget, Option.getD_some]
  unfold Env.load
  congr 3
  apply List.map_congr_left
  intro j hj
  rw [List.mem_range] at hj
  rw [frame_base, Env.ofMachine_mem0, frame_add, hsame j hj]

/-- Memory outside the frame's first `n` bytes, after writes only there. -/
theorem frame_outside [Labels] {vars : Nat → BitVec 64} {ret : BitVec 64} {S : SState}
    {m' : MachineData} (h : StackOk m0 F) (hk : Kept m0.dmem m.dmem)
    (hm : Match (frameEnv m0 m F vars ret) S m') {n : Nat} (hn : n ≤ F + 8)
    (hw : ∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ n) :
    SameOutside m.dmem m'.dmem (InRange (stackBelow m0 F) n) := by
  intro p hp
  refine hm.get?_mem0 (frame_wf h hk) fun ⟨w, hwm, b, sz, hbs, h1, h2⟩ ↦ hp ?_
  obtain ⟨hr, hn'⟩ := hw w hwm
  rw [hr] at hbs
  cases hbs
  have := frame_noWrap h
  rw [inRange_iff (by omega)]
  omega

variable [Host]

/-- **A function without calls**, at its `ret`. -/
theorem leaf_done {vars : Nat → BitVec 64} {ret : BitVec 64} {next : Int64} (h : StackOk m0 F) {S : SState}
    {st : MachineState} (hm : Match (frameEnv m0 m0 F vars ret) S st.data)
    (hpc : PcOk (frameEnv m0 m0 F vars ret) (.ret (.load 0 F 8)) next st)
    (hsp : S.reg .rsp = some (.ptr 0 ((F + 8 : Nat) : Int)))
    (hkeep : keeps (frameS F) S = true) (hw : ∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ F) :
    st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧
      SameOutside m0.dmem st.data.dmem (InRange (stackBelow m0 F) F) ∧ Saved m0 st.data := by
  have hwf := frame_wf (m := m0) (vars := vars) (ret := ret) h fun _ h ↦ h
  have hso := frame_outside h (fun _ h ↦ h) hm (Nat.le_add_right F 8) hw
  refine ⟨?_, ?_, hso, Match.saved match_frame hm hwf rfl hkeep⟩
  · simp only [PcOk] at hpc
    rw [hpc]
    exact load_ret h fun _ _ ↦ rfl
  · show st.data.regs.get64 .rsp = _
    rw [hm.regs .rsp _ hsp]
    exact frame_rsp F 8

end

end NativeRustcVmX64.Field
