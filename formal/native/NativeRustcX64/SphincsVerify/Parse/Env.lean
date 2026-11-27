module

public import NativeRustcX64.SphincsVerify.Parse.Glue
public import NativeRustcX64.SphincsVerify.Parse.State

/-!
# The parse's environments (x86-64)

Regions 0..3 are always `r.frameRegs` (frame, slots below, memcpy GOT, memset GOT), with an
optional region 4 for an external read-only input buffer:
- `regsPk`: the 32-byte public key (`pkPtr`) at `b0` (`wfPk`);
- `regsSig`: the 7740-byte raw signature (`sigPtr`) (`wfSig`, `match_sig`);
- `regsOpen c`: the 176-byte FORS opening `c` (`sigPtr + 16 + 176 c`) at `b1` (`wfOpen`,
  `match_open`);
- `wfSigTurn`: 32 bytes of `sigPtr` and 32 bytes of the frame for the chain-value copy loops.
-/

namespace NativeRustcX64.SphincsVerifyProof.Parse

open NativeRustc NativeRustc.Sphincs NativeRustcX64.Sym LeanVM.Protocol.KeccakHash

@[expose] public section

/-- The frame's regions and the 32-byte public key. -/
abbrev regsPk (r : Run) [Labels] : List (BitVec 64 × Nat) :=
  r.frameRegs ++ [(r.pkPtr, 32)]

/-- The frame's regions and the 7740-byte raw signature. -/
abbrev regsSig (r : Run) [Labels] : List (BitVec 64 × Nat) :=
  r.frameRegs ++ [(r.sigPtr, 7740)]

/-- The frame's regions and FORS opening `c` (176 bytes of the raw signature). -/
abbrev regsOpen (r : Run) [Labels] (c : Nat) : List (BitVec 64 × Nat) :=
  r.frameRegs ++ [(r.sigPtr + BitVec.ofNat 64 (16 + 176 * c), 176)]

/-- Environment with `regions` where regions 2, 3, 4 (GOT slots and external input) are read-only. -/
abbrev envExt (m : MachineData) (regions : List (BitVec 64 × Nat))
    (vars : Nat → BitVec 64 := fun _ ↦ 0) (ret : BitVec 64 := 0) : Env :=
  { Env.ofMachine m regions vars ret with roRegions := [2, 3, 4] }

/-- The writes are in region 0 below the return address, or in region 1. -/
def entryWrites (S : SState) : Bool :=
  S.mem.all fun w ↦ (w.r == 0 && decide (w.off + w.n ≤ 21624)) || (w.r == 1 && decide (w.off + w.n ≤ 16))

end

public section

theorem bytesAt_sub {d : DataMem} {a : BitVec 64} {bs : List UInt8} (h : BytesAt d a bs) {k n : Nat}
    (hk : k + n ≤ bs.length) : BytesAt d (a + BitVec.ofNat 64 k) (slice bs k n) := by
  intro i hi
  have hl : (slice bs k n).length = n := by simp [slice]; omega
  rw [addr_add, h (k + i) (by omega)]
  simp [slice]

variable (r : Run) [Labels]

/-- A slice of the raw signature at `r.sigPtr + k`. -/
theorem sig_slice (hpre : r.Pre) {d : DataMem} (hS : SameOutside r.m0.dmem d r.StackArea)
    {k n : Nat} (hk : k + n ≤ 7740) :
    BytesAt d (r.sigPtr + BitVec.ofNat 64 k) (slice r.sigB k n) :=
  bytesAt_sub (r.sig_at hpre hS) (by rw [r.hsig]; exact hk)

/-- Helper: appending a 5th external read-only region apart from the stack to `frameRegs` is WF
with regions 2, 3, 4 read-only (no GOT-vs-input disjointness required). -/
private theorem wf_frame_ext (hpre : r.Pre) {m : MachineData} (hk : Kept r.m0.dmem m.dmem)
    {p : BitVec 64} {len : Nat}
    (hmap : Mapped m.dmem p len) (hnw : NoWrap p len)
    (hA : Apart p len (stackBelow r.m0 sphincsStack) (sphincsStack + 8))
    (vars : Nat → BitVec 64) (ret : BitVec 64) :
    (envExt m (r.frameRegs ++ [(p, len)]) vars ret).WFRo := by
  have hw := r.frame_wf hpre hk vars ret
  have hb := r.base_toNat hpre
  have hbl := r.below_toNat hpre
  have hlo : (r.base - 16#64).toNat = r.base.toNat - 16 := toNat_sub_ofNat (by omega)
  have h0 : Mapped m.dmem r.base frameRegion ∧ NoWrap r.base frameRegion :=
    ⟨hw.mapped 0 r.base frameRegion rfl, hw.noWrap 0 r.base frameRegion rfl⟩
  have h1 : Mapped m.dmem (r.base - 16#64) 16 ∧ NoWrap (r.base - 16#64) 16 :=
    ⟨hw.mapped 1 (r.base - 16#64) 16 rfl, hw.noWrap 1 (r.base - 16#64) 16 rfl⟩
  have h2 : Mapped m.dmem (gotAddr "memcpy") 8 ∧ NoWrap (gotAddr "memcpy") 8 :=
    ⟨hw.mapped 2 (gotAddr "memcpy") 8 rfl, hw.noWrap 2 (gotAddr "memcpy") 8 rfl⟩
  have h3 : Mapped m.dmem (gotAddr "memset") 8 ∧ NoWrap (gotAddr "memset") 8 :=
    ⟨hw.mapped 3 (gotAddr "memset") 8 rfl, hw.noWrap 3 (gotAddr "memset") 8 rfl⟩
  refine Sym.Env.wf_of_ro ⟨h0, h1, h2, h3, ⟨hmap, hnw⟩, trivial⟩ ?_
  simp only [Apart, Run.sphincsStack_eq] at hA hbl
  intro i j b b' n n' hro hne hi hj
  have hi5 : i < 5 := by
    have := (List.getElem?_eq_some_iff.mp hi).1
    simpa [envExt, Run.frameRegs] using this
  have hj5 : j < 5 := by
    have := (List.getElem?_eq_some_iff.mp hj).1
    simpa [envExt, Run.frameRegs] using this
  have hi2 : i < 2 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hro
    omega
  interval_cases i <;> interval_cases j
  · exact absurd rfl hne
  · simp only [Run.frameRegs] at hi hj; cases hi; cases hj
    exact hw.disjoint 0 1 _ _ _ _ (by decide) rfl rfl
  · simp only [Run.frameRegs] at hi hj; cases hi; cases hj
    exact (r.got_apart_frame hpre (by simp)).symm
  · simp only [Run.frameRegs] at hi hj; cases hi; cases hj
    exact (r.got_apart_frame hpre (by simp)).symm
  · simp only [Run.frameRegs] at hi hj; cases hi; cases hj
    show Apart r.base frameRegion p len
    unfold Apart; rw [Run.frameRegion_eq]; omega
  · simp only [Run.frameRegs] at hi hj; cases hi; cases hj
    exact (hw.disjoint 0 1 _ _ _ _ (by decide) rfl rfl).symm
  · exact absurd rfl hne
  · simp only [Run.frameRegs] at hi hj; cases hi; cases hj
    exact (r.got_apart_below hpre (by simp)).symm
  · simp only [Run.frameRegs] at hi hj; cases hi; cases hj
    exact (r.got_apart_below hpre (by simp)).symm
  · simp only [Run.frameRegs] at hi hj; cases hi; cases hj
    show Apart (r.base - 16#64) 16 p len
    unfold Apart; omega

/-- **The frame's regions and the public key** are a well-formed environment (at `b0`). -/
theorem wfPk (hpre : r.Pre) (vars : Nat → BitVec 64) (ret : BitVec 64) :
    (envExt r.m0 (regsPk r) vars ret).WFRo := by
  obtain ⟨hpk, hnw, hA⟩ := r.pk_pre hpre
  have hmap : Mapped r.m0.dmem r.pkPtr 32 := fun i hi ↦ by
    rw [hpk i (by rw [r.hpk]; exact hi)]; rfl
  exact wf_frame_ext r hpre (fun _ h ↦ h) hmap hnw hA vars ret

/-- **The frame's regions and the raw signature** are a well-formed environment. -/
theorem wfSig (hpre : r.Pre) {m : MachineData} (hk : Kept r.m0.dmem m.dmem)
    (hS : SameOutside r.m0.dmem m.dmem r.StackArea) (vars : Nat → BitVec 64) (ret : BitVec 64) :
    (envExt m (regsSig r) vars ret).WFRo := by
  obtain ⟨_, hnw, hA⟩ := r.sig_pre hpre
  have hmap : Mapped m.dmem r.sigPtr 7740 := fun i hi ↦ by
    rw [r.sig_at hpre hS i (by rw [r.hsig]; exact hi)]; rfl
  exact wf_frame_ext r hpre hk hmap hnw hA vars ret

/-- **The frame's regions and FORS opening `c`** are a well-formed environment (at `b1`). -/
theorem wfOpen (hpre : r.Pre) {m : MachineData} (hk : Kept r.m0.dmem m.dmem)
    (hS : SameOutside r.m0.dmem m.dmem r.StackArea) {c : Nat} (hc : c < 24)
    (vars : Nat → BitVec 64) (ret : BitVec 64) :
    (envExt m (regsOpen r c) vars ret).WFRo := by
  obtain ⟨_, hnw, hA⟩ := r.sig_pre hpre
  have hoff : (r.sigPtr + BitVec.ofNat 64 (16 + 176 * c)).toNat = r.sigPtr.toNat + (16 + 176 * c) :=
    Sym.toNat_add_ofNat _ _ (by unfold NoWrap at hnw; omega)
  have hmap : Mapped m.dmem (r.sigPtr + BitVec.ofNat 64 (16 + 176 * c)) 176 := fun i hi ↦ by
    rw [addr_add, r.sig_at hpre hS _ (by rw [r.hsig]; omega)]; rfl
  have hnw' : NoWrap (r.sigPtr + BitVec.ofNat 64 (16 + 176 * c)) 176 := by
    unfold NoWrap at hnw ⊢; omega
  have hA' : Apart (r.sigPtr + BitVec.ofNat 64 (16 + 176 * c)) 176
      (stackBelow r.m0 sphincsStack) (sphincsStack + 8) := by
    unfold Apart at hA ⊢; omega
  exact wf_frame_ext r hpre hk hmap hnw' hA' vars ret

/-- **A 32-byte slice of `sigPtr` and a 32-byte slice of the frame** are a well-formed environment. -/
theorem wfSigTurn (hpre : r.Pre) {m : MachineData} (hk : Kept r.m0.dmem m.dmem)
    (hS : SameOutside r.m0.dmem m.dmem r.StackArea) {off d : Nat}
    (hoff : off + 32 ≤ 7740) (hd : d + 32 ≤ 21624)
    (vars : Nat → BitVec 64) (ret : BitVec 64) :
    (Env.ofMachine m [(r.sigPtr + BitVec.ofNat 64 off, 32), (r.off d, 32)] vars ret).WF := by
  obtain ⟨_, hnw, hA⟩ := r.sig_pre hpre
  have hbl := r.below_toNat hpre
  have hb := r.base_toNat hpre
  have ho := r.off_toNat hpre (a := d) (by omega)
  have hs : (r.sigPtr + BitVec.ofNat 64 off).toNat = r.sigPtr.toNat + off :=
    Sym.toNat_add_ofNat _ _ (by unfold NoWrap at hnw; omega)
  have hmap : Mapped m.dmem (r.sigPtr + BitVec.ofNat 64 off) 32 := fun i hi ↦ by
    rw [addr_add, r.sig_at hpre hS _ (by rw [r.hsig]; omega)]; rfl
  refine Sym.Env.wf_of ⟨⟨hmap, by dsimp only; unfold NoWrap at hnw ⊢; omega⟩,
    r.frame_mapped hpre hk hd, trivial⟩ (List.pairwise_pair.mpr ?_)
  show Apart _ 32 _ 32
  simp only [Apart, Run.sphincsStack_eq] at hA hbl ⊢
  omega

/-- Match `fSig k` in a frame state with `RBX = r.sigPtr`. -/
theorem match_sig (hpre : r.Pre) {m : MachineData} (hF : r.Frame m) (hrbx : Run.RegIs m .rbx r.sigPtr)
    {vars : Nat → BitVec 64} {ret : BitVec 64} {k : List (Reg64 × Sym)}
    (hk : AllOf (fun p ↦ m.regs.get64 p.1 = p.2.eval (envExt m (regsSig r) vars ret)) k) :
    Match (envExt m (regsSig r) vars ret) (fSig k) m := by
  apply Match.withKnownBytes
  · apply Match.withKnownBytes
    · apply match_ofMachine_ro
      · exact ⟨rfl, rfl, rfl, rfl, rfl, trivial⟩
      · refine ⟨by show rspOf m = r.base + BitVec.ofInt 64 0; simpa only [BitVec.ofInt_ofNat, BitVec.add_zero] using hF.1,
          by show m.regs.get64 .rbx = r.sigPtr + BitVec.ofInt 64 0; simp only [BitVec.ofInt_ofNat, BitVec.add_zero]; exact hrbx,
          hk⟩
      · exact trivial
      · exact trivial
      · refine ⟨r.alias8, ?_, ?_, ?_, trivial⟩
        · change r.base + BitVec.ofInt 64 (-16) = (r.base - 16#64) + BitVec.ofInt 64 0
          rw [show BitVec.ofInt 64 (-16) = -16#64 by decide, show BitVec.ofInt 64 0 = 0#64 by decide]
          bv_omega
        · simp [Sym.eval, Env.base, regsSig, Run.frameRegs, gotAddr]
        · simp [Sym.eval, Env.base, regsSig, Run.frameRegs, gotAddr]
    · intro i hi
      simpa [Sym.eval, Env.base, regsSig, Run.frameRegs] using
        r.got_byte hpre hF.2.2.1 (by simp : "memcpy" ∈ _) hi
  · intro i hi
    simpa [Sym.eval, Env.base, regsSig, Run.frameRegs] using
      r.got_byte hpre hF.2.2.1 (by simp : "memset" ∈ _) hi

/-- **The places a block's writes cover**, in an environment whose regions 0 and 1 are the
frame's: in the stack area (`entryWrites`). -/
theorem written_stack (hpre : r.Pre) {env : Env}
    (h0 : env.regions[0]? = some (r.base, 21632))
    (h1 : env.regions[1]? = some (r.base - 16#64, 16)) {S : SState} (hw : entryWrites S = true) :
    ∀ p, Sym.Written env S p → r.StackArea p := by
  have hb := r.base_toNat hpre
  rintro p ⟨w, hwm, b, sz, hr, h1', h2⟩
  simp only [entryWrites, List.all_eq_true, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at hw
  rw [r.stackArea_iff hpre]
  rcases hw w hwm with ⟨hw0, hwn⟩ | ⟨hw1, hwn⟩
  · rw [hw0] at hr
    simp only [h0, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    omega
  · rw [hw1] at hr
    simp only [h1, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    have hlo : (r.base - 16#64).toNat = r.base.toNat - 16 := toNat_sub_ofNat (by omega)
    omega

theorem written_frame (hpre : r.Pre) {env : Env}
    (h0 : env.regions[0]? = some (r.base, 21632))
    (h1 : env.regions[1]? = some (r.base - 16#64, 16)) {S : SState} (hw : Run.frameWrites S = true) :
    ∀ p, Sym.Written env S p →
      r.StackArea p ∧ ¬InRange (r.off 21576) 48 p := by
  have hb := r.base_toNat hpre
  rintro p ⟨w, hwm, b, sz, hr, h1', h2⟩
  simp only [Run.frameWrites, List.all_eq_true, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at hw
  have hs := r.off_toNat hpre (a := 21576) (by decide)
  rw [r.stackArea_iff hpre, Sym.inRange_iff (by rw [hs]; omega), hs]
  rcases hw w hwm with ⟨hw0, hwn⟩ | ⟨hw1, hwn⟩
  · rw [hw0] at hr
    simp only [h0, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    omega
  · rw [hw1] at hr
    simp only [h1, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    have hlo : (r.base - 16#64).toNat = r.base.toNat - 16 := toNat_sub_ofNat (by omega)
    omega

/-- **The frame's invariant after a block** of an environment whose regions 0 and 1 are the
frame's, its writes there off the saved registers, RSP the base. -/
theorem frame_of_block (hpre : r.Pre) {m m' : MachineData} (hF : r.Frame m)
    {env : Env}
    (h0 : env.regions[0]? = some (r.base, 21632)) (h1 : env.regions[1]? = some (r.base - 16#64, 16))
    {S : SState} (hm : Match env S m')
    (hwf : env.WFRo) (hsp : S.reg .rsp = some (.ptr 0 0))
    (hw : Run.frameWrites S = true) (hmem : env.mem0 = m.dmem := by rfl) : r.Frame m' :=
  Run.Frame.of_change hF.2.1 hF.2.2.1 hF.2.2.2
    (by rw [rspOf, hm.regs .rsp _ hsp]; simp [Sym.eval, Env.base, h0])
    (hmem ▸ hm.sameOutside_ro hwf) (written_frame r hpre h0 h1 hw) (hmem ▸ hm.kept_ro hwf)

/-- **At a call after a block** of an environment whose regions 0 and 1 are the frame's. -/
theorem atCall_of_block (hpre : r.Pre) {m m' : MachineData} (hF : r.Frame m)
    {env : Env}
    (h0 : env.regions[0]? = some (r.base, 21632)) (h1 : env.regions[1]? = some (r.base - 16#64, 16))
    {S : SState} (hm : Match env S m')
    (hwf : env.WFRo) (hsp : S.reg .rsp = some (.ptr 0 (-8)))
    (hw : Run.frameWrites S = true) (hmem : env.mem0 = m.dmem := by rfl) : r.AtCall m' := by
  have hF' := Run.Frame.of_change hF.2.1 hF.2.2.1 hF.2.2.2 (m' := { m' with regs := m.regs }) hF.1
    (hmem ▸ hm.sameOutside_ro hwf) (written_frame r hpre h0 h1 hw) (hmem ▸ hm.kept_ro hwf)
  refine ⟨?_, hF'.2.1, hF'.2.2.1, hF'.2.2.2⟩
  rw [rspOf, hm.regs .rsp _ hsp]
  simp only [Sym.eval, Env.base, h0, Option.map_some, Option.getD_some]
  rw [show BitVec.ofInt 64 (-8) = -8#64 by decide]
  bv_omega

end

end NativeRustcX64.SphincsVerifyProof.Parse
