module

public import NativeRustcVmX64.KeccakGkr.VerifyKeccak.Keep
public import NativeRustcVmX64.Transcript.Frame
public import NativeVm.Equiv.KeccakRmfe
public import NativeRustcVmX64.Got

/-!
# `verify_keccak`'s calls: their preconditions' common parts (x86-64)

`CallAt m0 wr oc mc`: the machine at a call, RSP at the frame's offset `oc`, memory the entry's
but in the stack and the written regions `wr`. From it a callee's stack (`CallAt.rc`, the
read-only tables `CallAt.pj`, `CallAt.rh`), the `TState`'s footprint (`CallAt.tok`), outputs in
the frame (`CallAt.outF`) or in a region (`CallAt.outR`), and the elements the function reads
(`inst`, the output lanes) as at the entry.
-/

namespace NativeRustcVmX64.KeccakGkr.VerifyKeccak

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.KeccakGkr.SeqZ NativeVm.Model
open NativeRustcVmX64.Ring (outsOf)
open NativeRustcVm.Transcript (DecArea TStateAt tstateBytes)
open NativeRustcVm.KeccakGkr (off)

@[expose] public section

/-- **At a call**, RSP at the frame's offset `oc`. -/
structure CallAt [Labels] (m0 : MachineData) (wr : Nat → Bool) (oc : Nat) (mc : MachineData) :
    Prop where
  sp : rspOf mc = stackBelow m0 (3344 - oc)
  oc8 : oc + 8 ≤ 3344
  kept : Kept m0.dmem mc.dmem
  same : SameOutside m0.dmem mc.dmem
    (fun q ↦ InRange (stackBelow m0 verifyKeccakStack) verifyKeccakStack q ∨ outsOf (rsOf m0) wr q)

end

public section

theorem rc_len : (LeanVM.Parameters.keccakRC.flatMap NativeRustcVm.wordBytes).length = 192 := by
  rw [NativeRustcVm.length_wordsBytes]; rfl

theorem pj_len : (rmfeProjectW.toList.flatMap NativeRustcVm.wordBytes).length = 128 := by
  rw [NativeRustcVm.length_wordsBytes]
  simp [rmfeProjectW, NativeVm.Equiv.rmfeProject_length]

theorem rh_len [Labels] : rhoBytes.length = 100 := by decide

theorem Sep.symm {x n y k : Nat} (h : Sep x n y k) : Sep y k x n := by unfold Sep at *; omega

variable [Labels] {m0 mc : MachineData} {a : DecArea} {inst : Array EW} {wr : Nat → Bool}
  {oc : Nat}

theorem CallAt.rsp (c : Ctx a inst m0) (h : CallAt m0 wr oc mc) :
    (rspOf mc).toNat = (rspOf m0).toNat - 3344 + oc := by
  have := h.oc8
  rw [h.sp, stackBelow_toNat (by have := c.sp; have := vk_eq; omega)]
  have := c.sp; have := vk_eq
  omega

theorem CallAt.sb (c : Ctx a inst m0) (h : CallAt m0 wr oc mc) {N : Nat}
    (hN : 3344 - oc + N ≤ verifyKeccakStack) :
    (stackBelow mc N).toNat = (rspOf m0).toNat - 3344 + oc - N := by
  have hr := h.rsp c
  have := h.oc8
  have := c.sp
  rw [stackBelow_toNat (by rw [hr]; omega), hr]

/-- Bytes apart from the stack and every region stay the entry's at a call. -/
theorem CallAt.ro (c : Ctx a inst m0) (h : CallAt m0 wr oc mc) {A : BitVec 64} {n : Nat}
    (hA : A.toNat + n ≤ 2 ^ 64)
    (hst : Sep A.toNat n (stackBelow m0 verifyKeccakStack).toNat (verifyKeccakStack + 8))
    (h1 : Sep A.toNat n (reg m0 .rdi).toNat 760) (h2 : Sep A.toNat n (reg m0 .r9).toNat 205824)
    (h3 : Sep A.toNat n (keccakClaims m0).toNat 97288)
    (h4 : Sep A.toNat n (keccakOutArg m0).toNat 1608) :
    NativeRustcVm.Layout.Same m0.dmem mc.dmem A n :=
  same_ro c h.same hA hst (fun _ ↦ h1) (fun _ ↦ h2) (fun _ ↦ h3) (fun _ ↦ h4)

/-- A call preserves the sole loader slot used by the GKR verifier. -/
theorem CallAt.got (c : Ctx a inst m0) (h : CallAt m0 wr oc mc) {N : Nat}
    (hN : 3344 - oc + N ≤ verifyKeccakStack) {areas : List (BitVec 64 × Nat)}
    (hcover : ∀ p ∈ areas,
      ∃ b ∈ (stackBelow m0 verifyKeccakStack, verifyKeccakStack + 8) ::
        [(reg m0 .rdi, 760), (reg m0 .r9, 205824), (keccakClaims m0, 97288),
          (keccakOutArg m0, 1608), (a.region.addr, a.region.size),
          (reg m0 .rdx, 16 * inst.size), (reg m0 .r8, 400), (rcAddr, 192),
          (projectAddr, 128), (rhoAddr, 100), (rspOf m0 + 8#64, 16)],
        b.1.toNat ≤ p.1.toNat ∧ p.1.toNat + p.2 ≤ b.1.toNat + b.2) :
    GotAt mc N areas ["memcpy"] := by
  apply NativeRustcVmX64.GotAt.callee c.got _ _ _ hcover
  · intro l hl i hi
    have hg := c.got.1 l hl
    exact h.ro c hg.2.1 hg.2.2.1
      (hg.2.2.2 (reg m0 .rdi, 760) (by simp)) (hg.2.2.2 (reg m0 .r9, 205824) (by simp))
      (hg.2.2.2 (keccakClaims m0, 97288) (by simp))
      (hg.2.2.2 (keccakOutArg m0, 1608) (by simp)) i hi
  · rw [c.K, h.sb c hN]
    have := c.sp; have := h.oc8; omega
  · rw [c.K, h.sb c hN]
    have := c.sp; have := h.oc8; have := vk_eq; omega

/-- **The round constants** for a callee using `N` bytes of stack. -/
theorem CallAt.rc (c : Ctx a inst m0) (h : CallAt m0 wr oc mc)
    (hrc : RcAt m0 verifyKeccakStack) {N : Nat} (hN : 3344 - oc + N ≤ verifyKeccakStack) :
    RcAt mc N :=
  NativeRustcVmX64.Transcript.RcAt.callee hrc (fun i hi ↦ CallAt.ro c h c.rcW c.rcS c.trc.symm c.src.symm c.crc.symm
    c.orc.symm i hi) h.sp c.sp hN

theorem CallAt.pj (c : Ctx a inst m0) (h : CallAt m0 wr oc mc) (hpj : ProjectAt m0) :
    ProjectAt mc :=
  NativeRustcVm.Layout.BytesAt.of_same hpj (CallAt.ro c h c.pjW c.pjS c.tpj.symm c.spj.symm
    c.cpj.symm c.opj.symm) (by rw [pj_len])

theorem CallAt.rh (c : Ctx a inst m0) (h : CallAt m0 wr oc mc) (hrh : RhoAt m0) : RhoAt mc :=
  NativeRustcVm.Layout.BytesAt.of_same hrh (CallAt.ro c h c.rhW c.rhS c.trh.symm c.srh.symm
    c.crh.symm c.orh.symm) (by rw [rh_len])

/-- `inst`'s elements at a call. -/
theorem CallAt.instAt (c : Ctx a inst m0) (h : CallAt m0 wr oc mc)
    (hi : NativeRustcVm.EWsAt m0.dmem (reg m0 .rdx) inst.toList) :
    NativeRustcVm.EWsAt mc.dmem (reg m0 .rdx) inst.toList :=
  NativeRustcVm.Tables.EWsAt.of_same hi (CallAt.ro c h c.iW c.iS c.ti.symm c.si.symm c.ci.symm
    c.oi.symm) (by simp)

/-- The output lanes at a call. -/
theorem CallAt.lanes (c : Ctx a inst m0) (h : CallAt m0 wr oc mc) {output : Array EW}
    (hs : output.size = 25) (ho : NativeRustcVm.EWsAt m0.dmem (reg m0 .r8) output.toList) :
    NativeRustcVm.EWsAt mc.dmem (reg m0 .r8) output.toList :=
  NativeRustcVm.Tables.EWsAt.of_same ho (CallAt.ro c h c.pW c.pS c.tp.symm c.spp.symm c.cp.symm
    c.op.symm) (by simp [hs])

/-- **The `TState`'s footprint** for a callee using `N` bytes of stack. -/
theorem CallAt.tok (c : Ctx a inst m0) (h : CallAt m0 wr oc mc) {N : Nat}
    (hN : 3344 - oc + N ≤ verifyKeccakStack) :
    NativeRustcVmX64.TStateOk mc (reg m0 .rdi) a N := by
  have hb := h.sb c hN
  have hK := c.K
  have := c.sp
  have := h.oc8
  have := vk_eq
  have h1 := c.tS
  have h2 := c.wS
  have h3 := c.trc
  unfold Sep at h1 h2 h3
  refine ⟨?_, ?_, ?_⟩ <;> simp only [NativeRustcX64.Apart, tstateBytes] <;> omega

/-- The regions are mapped. -/
theorem ob_mapped (h : LayZ m0 3344 3368 verifyKeccakStack (rsOf m0)) {i : Nat} (h1 : 1 ≤ i)
    (h4 : i ≤ 4) : NativeRustcVm.Mapped m0.dmem (ob m0 i) (rsz i) := by
  have harr := h.arr
  simp only [rsOf, AllOf] at harr
  rcases (by omega : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl
  · exact harr.1.1
  · exact harr.2.1.1
  · exact harr.2.2.1.1
  · exact harr.2.2.2.1.1

/-- **An output in the frame** at offset `o` (above the callee's stack). -/
theorem CallAt.outF (c : Ctx a inst m0) (h : CallAt m0 wr oc mc)
    (hl : LayZ m0 3344 3368 verifyKeccakStack (rsOf m0)) {N o n : Nat}
    (hN : 3344 - oc + N ≤ verifyKeccakStack) (ho : oc + 8 ≤ o) (hon : o + n ≤ 3344) :
    NativeRustcVmX64.OutOk mc (reg m0 .rdi) a (off (fb m0) o) n N := by
  have hb := h.sb c hN
  have hK := c.K
  have := c.sp
  have := c.top
  have := vk_eq
  have e := off_fb c (o := o) (by omega)
  have hS1 := ob_S c (i := 1) (by omega) (by omega)
  have h2 := c.wS
  have h3 := c.rcS
  simp only [ob, rsz] at hS1
  unfold Sep at h2 h3
  refine ⟨NativeRustcVmX64.Transcript.mapped_off (NativeRustcVm.Transcript.Mapped.keeps hl.map h.kept)
    (by omega), ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [NativeRustcX64.NoWrap, NativeRustcX64.Apart, tstateBytes] <;> rw [e] <;> omega

/-- **An output in region `i`** (the scratch or the `KeccakOutW`) at offset `o`. -/
theorem CallAt.outR (c : Ctx a inst m0) (h : CallAt m0 wr oc mc)
    (hl : LayZ m0 3344 3368 verifyKeccakStack (rsOf m0)) {N i o n : Nat}
    (hN : 3344 - oc + N ≤ verifyKeccakStack) (h1 : 2 ≤ i) (h4 : i ≤ 4) (hon : o + n ≤ rsz i)
    (hn : 0 < n) :
    NativeRustcVmX64.OutOk mc (reg m0 .rdi) a (off (ob m0 i) o) n N := by
  have hb := h.sb c hN
  have hK := c.K
  have := c.sp
  have := c.top
  have := vk_eq
  have hw := ob_W c (i := i) (by omega) h4
  have e : (off (ob m0 i) o).toNat = (ob m0 i).toNat + o := toNat_add_ofNat _ _ (by omega)
  have hS := ob_S c (i := i) (by omega) h4
  have hs1 : Sep (ob m0 i).toNat (rsz i) (reg m0 .rdi).toNat 760 :=
    ob_sep c (i := i) (j := 1) (by omega) h4 (by omega) (by omega) (by omega)
  have hw' := ob_w c (i := i) (by omega) h4
  have hoc := h.oc8
  have hrc : Sep (ob m0 i).toNat (rsz i) rcAddr.toNat 192 := by
    rcases (by omega : i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl
    · exact c.src
    · exact c.crc
    · exact c.orc
  unfold Sep at hs1 hw' hrc
  refine ⟨NativeRustcVmX64.Transcript.mapped_off (NativeRustcVm.Transcript.Mapped.keeps
    (ob_mapped hl (by omega) h4) h.kept) hon, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [NativeRustcX64.NoWrap, NativeRustcX64.Apart, tstateBytes] <;> rw [e] <;> omega

end

end NativeRustcVmX64.KeccakGkr.VerifyKeccak
