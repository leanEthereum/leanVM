module

public import NativeRustcVmArm.KeccakGkr.KeccakPhase.Basic

/-!
# `keccak_phase`: what its steps share

- The frame's environment and match between the blocks (`wfF`, `matchF`), a register a block set
  (`reg_of`).
- What the code keeps of the entry's memory until `verify_keccak` (`same_m0`: a range apart from
  the stack, with the frame's outputs none).
- The zeros the prologue stores (`zeros`) and the output lanes after `memcpy` (`lanes_at`).
-/

namespace NativeRustcVmArm.KeccakGkr.KeccakPhase

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVmArm.Ring
open NativeRustcVm.Transcript
open NativeRustcVm (Region InAny)
open LeanVM.Protocol.Verifier (keccakOut)
open NativeRustcVm.Layout (Same)

public section

/-- A register a block set to `v`. -/
theorem reg_of [Labels] {env : Env} {S : SState} {m : MachineData} (hm : Match env S m) {r : XReg}
    {v : Sym} (h : S.reg r = some v) {w : UInt64} (hv : v.eval env = w.toBitVec) :
    m.regs.getXReg r = w :=
  UInt64.toBitVec_inj.mp ((hm.regs r v h).trans hv)

theorem keep_cs : ∀ r ∈ keep, calleeSaved r = true := by decide

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 480 := by decide

/-- A frame with no outputs is one with any. -/
theorem Fr.weaken {m0 m : MachineData} {outs' : BitVec 64 → Prop}
    (h : Fr m0 480 keccakPhaseStack slots keep (fun _ ↦ False) m) :
    Fr m0 480 keccakPhaseStack slots keep outs' m where
  sp := h.sp
  keep := h.keep
  slots := h.slots
  same := NativeRustcVm.SameOutside.mono h.same fun _ hq ↦ hq.elim .inl False.elim
  kept := h.kept

section
variable [Labels] {a : DecArea} {m0 m : MachineData} {outs' : BitVec 64 → Prop}

theorem fb_toNat (hn : Nums a m0) : (fb m0).toNat = m0.regs.SP.toNat - 480 :=
  base_toNat (by have := hn.hN; omega)

theorem frame_ok (hn : Nums a m0) (hS : StackOk m0 keccakPhaseStack) :
    Mapped m0.dmem (fb m0) 480 ∧ NoWrap (fb m0) 480 :=
  ⟨frame_mapped hS (by rw [stack_eq]; decide), base_noWrap (by have := hn.hN; omega)⟩

/-- The environment of the frame. -/
theorem wfF (hn : Nums a m0) (hS : StackOk m0 keccakPhaseStack)
    (hfr : Fr m0 480 keccakPhaseStack slots keep outs' m) :
    (Env.ofMachine m [(fb m0, 480)]).WF :=
  Env.wf_of ⟨⟨Mapped.kept' (frame_ok hn hS).1 hfr.kept, (frame_ok hn hS).2⟩, trivial⟩
    (List.pairwise_singleton _ _)

/-- The frame from SP. -/
theorem matchF (_hn : Nums a m0) (hS : StackOk m0 keccakPhaseStack)
    (hfr : Fr m0 480 keccakPhaseStack slots keep outs' m) :
    Match (Env.ofMachine m [(fb m0, 480)]) midS m :=
  match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hS (by rw [stack_eq]; decide) (by decide), trivial⟩
    (by rw [hfr.sp]; simp [Sym.eval]) trivial trivial trivial trivial

/-- **A range apart from the stack** is as at the entry while the frame has no outputs. -/
theorem same_m0 (hn : Nums a m0) (hfr : Fr m0 480 keccakPhaseStack slots keep (fun _ ↦ False) m)
    {A : BitVec 64} {n : Nat} (hW : A.toNat + n ≤ 2 ^ 64)
    (hA : A.toNat + n ≤ m0.regs.SP.toNat - 7488 ∨ m0.regs.SP.toNat ≤ A.toNat) :
    Same m0.dmem m.dmem A n := by
  refine NativeRustcVm.Layout.Same.of_sameOutside hfr.same fun j hj hq ↦ ?_
  rcases hq with hq | hq
  · have hN := hn.hN
    have hSP := m0.regs.SP.toNat_lt
    have hbN : (base m0 keccakPhaseStack).toNat = m0.regs.SP.toNat - 7488 := by
      rw [stack_eq]; exact base_toNat hN
    rw [Sym.inRange_iff (by rw [hbN, stack_eq]; omega), hbN, stack_eq,
      NativeRustcVm.toNat_add_ofNat (by omega)] at hq
    omega
  · exact hq

end

/-! ## The output lanes -/

/-- **The zeros the prologue stores**: words `0` to `49` of region 0. -/
theorem zeros [Labels] {env : Env} {S : SState} {m : MachineData} (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 480))
    (hz : ∀ i < 50, ∀ j < 8, findWrite 0 (8 * i + j) S.mem = some (.lit 0, j)) :
    ∀ i < 50, NativeRustcVm.WordAt m.dmem (b + BitVec.ofNat 64 (8 * i)) 0 := by
  intro i hi
  have := Sumcheck.Match.wordAt_write hm hb (r := 0) (o := 8 * i) (v := .lit 0) (by omega)
    fun j hj ↦ hz i hi j hj
  have e : UInt64.ofBitVec ((Sym.lit 0).eval env) = 0 := by
    simp only [Sym.eval]; rfl
  rw [e] at this
  exact this

theorem keccakOut_eq : keccakOut = 40 := by decide +kernel

theorem lanes_size (values : Array EW) : (lanes values).size = 25 := by simp [lanes]

theorem lanes_getElem (values : Array EW) {i : Nat} (hi : i < (lanes values).size) :
    (lanes values)[i] = values.getD (40 + i) 0 := by
  simp [lanes, keccakOut_eq]

/-- **The output lanes** after `memcpy` copied the `p` present ones over the zeros. -/
theorem lanes_at {d d' : DataMem} {fb0 vb : BitVec 64} {values : Array EW}
    (hfb : fb0.toNat + 480 ≤ 2 ^ 64)
    (hz : ∀ i < 50, NativeRustcVm.WordAt d (fb0 + BitVec.ofNat 64 (8 * i)) 0)
    (hv : NativeRustcVm.EWsAt d vb values.toList) (h40 : 40 ≤ values.size)
    (hc : NativeRustcVm.BytesAt d' fb0
      (NativeRustcArm.bytesOf d (vb + BitVec.ofNat 64 640) (16 * min (values.size - 40) 25)))
    (hs : SameOutside d d' (InRange fb0 (16 * min (values.size - 40) 25))) :
    NativeRustcVm.EWsAt d' fb0 (lanes values).toList := by
  refine NativeRustcVm.ewsAt_iff.mpr fun i hi ↦ ?_
  have hi' : i < 25 := by simpa [lanes_size] using hi
  rw [Array.getElem_toList, lanes_getElem]
  by_cases hp : i < min (values.size - 40) 25
  · have hlt : 40 + i < values.size := by omega
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt, Option.getD_some]
    have h1 := hv.getElem (i := 40 + i) (by simpa using hlt)
    rw [Array.getElem_toList] at h1
    have h1' : NativeRustcVm.BytesAt d (vb + BitVec.ofNat 64 640 + BitVec.ofNat 64 (16 * i))
        (NativeRustcVm.ewBytes values[40 + i]) := by
      rw [NativeRustcVm.addr_add_add, show 640 + 16 * i = 16 * (40 + i) by omega]; exact h1
    exact bytes_copy (o := 16 * i) h1' hc (by rw [NativeRustcVm.length_ewBytes]; omega)
  · have hge : values.size ≤ 40 + i := by omega
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hge, Option.getD_none]
    have h0 : NativeRustcVm.EWAt d (fb0 + BitVec.ofNat 64 (16 * i)) 0 := by
      refine NativeRustcVm.ewAt_iff.mpr ⟨?_, ?_⟩
      · have := hz (2 * i) (by omega)
        rwa [show 8 * (2 * i) = 16 * i by omega] at this
      · have := hz (2 * i + 1) (by omega)
        rw [NativeRustcVm.addr_add_add, show 16 * i + 8 = 8 * (2 * i + 1) by omega]
        exact this
    refine NativeRustcVm.Layout.EWAt.of_same h0 (n := 16) ?_ le_rfl
    refine NativeRustcVm.Layout.Same.of_sameOutside hs fun j hj hq ↦ ?_
    rw [NativeRustcVm.addr_add_add, Sym.inRange_iff (by omega),
      NativeRustcVm.toNat_add_ofNat (by omega)] at hq
    omega

end

end NativeRustcVmArm.KeccakGkr.KeccakPhase
