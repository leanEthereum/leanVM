module

public import NativeRustcVmArm.Tables.TableWeights.Facts

/-!
# `table_weights`: reading a block's results

After a frame block (environment `Env.ofMachine m ((fb m0, 240) :: rs)`, final state `S'`) and its call
of `EW::mul` (`frame_mul`), a callee-saved register is the value of its symbolic value
(`rg_after`), a frame word the value of its symbolic load (`fw_after`); the frame's kept words
and the base keep (`frm_after`). The machine's facts the proofs need of the entry state
(`Geo`: the frame's base aligned, the stack area mapped and not wrapping).
-/

namespace NativeRustcVmArm.Tables.TableWeights

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Tables
open NativeRustcVm (wordOf)

public section

variable {m0 : MachineData}

/-- The frame's geometry at the entry. -/
structure Geo (m0 : MachineData) : Prop where
  al : (fb m0).toNat % 16 = 0
  lo : ewMulStack ≤ (fb m0).toNat
  hi : (fb m0).toNat + 240 ≤ 2 ^ 64
  map : Mapped m0.dmem (fb m0 - BitVec.ofNat 64 ewMulStack) (ewMulStack + 240)

theorem fb_toNat (hstk : StackOk m0 tableWeightsStack) : (fb m0).toNat = m0.regs.SP.toNat - 240 := by
  have := hstk.2.1
  unfold tableWeightsStack at this
  rw [fb, NativeRustcVm.toNat_sub_ofNat (by rw [UInt64.toNat_toBitVec]; omega),
    UInt64.toNat_toBitVec]

/-- The frame's base minus `EW::mul`'s stack is the entry's stack bottom. -/
theorem fb_sub (m0 : MachineData) :
    fb m0 - BitVec.ofNat 64 ewMulStack = stackBelow m0 tableWeightsStack := by
  rw [fb, stackBelow, tableWeightsStack, BitVec.sub_sub, ← BitVec.ofNat_add]

theorem geo_of (hstk : StackOk m0 tableWeightsStack) : Geo m0 := by
  have hf := fb_toNat hstk
  obtain ⟨hal, hle, hmap⟩ := hstk
  unfold tableWeightsStack ewMulStack at hle
  have := m0.regs.SP.toNat_lt
  refine ⟨by rw [hf]; omega, by rw [hf]; unfold ewMulStack; omega, by rw [hf]; omega, ?_⟩
  rw [fb_sub]
  exact hmap

variable [Labels]

/-- A callee-saved register after a block and a call. -/
theorem rg_after {st : MachineData} {S' : SState} {env : Env}
    (hsv : ∀ r v, calleeSaved r = true → S'.reg r = some v →
      (st.regs.getXReg r).toBitVec = v.eval env)
    {r : XReg} {v : Sym} (hr : calleeSaved r = true) (h : S'.reg r = some v) :
    rg st r = v.eval env :=
  hsv r v hr h

/-- A frame word after a block and a call. -/
theorem fw_after {st : MachineData} {S' : SState} {env : Env}
    (hwd : ∀ o, o + 8 ≤ 240 → (wordOf st.dmem (fb m0 + BitVec.ofNat 64 o)).toBitVec =
      (loadSym S'.mem 0 o 8).eval env)
    {o : Nat} {v : Sym} (ho : o + 8 ≤ 240) (h : loadSym S'.mem 0 o 8 = v) :
    fw m0 st o = v.eval env := by
  rw [fw, hwd o ho, h]

/-- **The frame's invariant after a block and a call** that kept the frame's kept words. -/
theorem frm_after {m st : MachineData} {rs : List (BitVec 64 × Nat)} {S' : SState}
    (hf : Frm m0 m)
    (hsp : st.regs.SP.toBitVec = fb m0)
    (hwd : ∀ o, o + 8 ≤ 240 → (wordOf st.dmem (fb m0 + BitVec.ofNat 64 o)).toBitVec =
      (loadSym S'.mem 0 o 8).eval (Env.ofMachine m ((fb m0, 240) :: rs)))
    (hk : ∀ p ∈ (kslots m0).map Prod.fst, loadSym S'.mem 0 p 8 = .load 0 p 8)
    (hsame : SameOutside m.dmem st.dmem (StackArea (fb m0) ewMulStack 240))
    (hkept : Kept m.dmem st.dmem) : Frm m0 st where
  sp := hsp
  slots p hp := by
    have hmem := List.mem_map_of_mem (f := Prod.fst) hp
    have ho : p.1 + 8 ≤ 240 := by
      simp only [kslots, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
        or_false] at hmem
      omega
    rw [fw_after hwd ho (hk _ hmem)]
    show (Env.ofMachine m ((fb m0, 240) :: rs)).load 0 p.1 8 = _
    rw [load_fw]
    exact hf.slots p hp
  same p hp := by rw [hsame p hp]; exact hf.same p hp
  kept p h := hkept p (hf.kept p h)

end

end NativeRustcVmArm.Tables.TableWeights
