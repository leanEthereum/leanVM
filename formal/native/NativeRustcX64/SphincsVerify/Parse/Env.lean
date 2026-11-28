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

/-- Helper: appending a 5th external read-only region apart from stack and GOT to `frameRegs` is WF. -/
private theorem wf_frame_ext (hpre : r.Pre) {m : MachineData} (hk : Kept r.m0.dmem m.dmem)
    {p : BitVec 64} {len : Nat}
    (hmap : Mapped m.dmem p len) (hnw : NoWrap p len)
    (hA : Apart p len (stackBelow r.m0 sphincsStack) (sphincsStack + 8))
    (hg1 : Apart (gotAddr "memcpy") 8 p len) (hg2 : Apart (gotAddr "memset") 8 p len)
    (vars : Nat → BitVec 64) (ret : BitVec 64) :
    (Env.ofMachine m (r.frameRegs ++ [(p, len)]) vars ret).WF := by
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
  refine Sym.Env.wf_of ⟨h0, h1, h2, h3, ⟨hmap, hnw⟩, trivial⟩ ?_
  simp only [Apart, Run.sphincsStack_eq] at hA hbl
  dsimp only [Run.frameRegs, List.cons_append, List.nil_append]
  refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (List.pairwise_singleton _ _))))
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact hw.disjoint 0 1 _ _ _ _ (by decide) rfl rfl
    · exact (r.got_apart_frame hpre (by simp)).symm
    · exact (r.got_apart_frame hpre (by simp)).symm
    · show Apart r.base frameRegion p len
      unfold Apart; rw [Run.frameRegion_eq]; omega
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    · exact (r.got_apart_below hpre (by simp)).symm
    · exact (r.got_apart_below hpre (by simp)).symm
    · show Apart (r.base - 16#64) 16 p len
      unfold Apart; omega
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact hw.disjoint 2 3 _ _ _ _ (by decide) rfl rfl
    · exact hg1
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    exact hg2

/-- **The frame's regions and the public key** are a well-formed environment (at `b0`). -/
theorem wfPk (hpre : r.Pre) (vars : Nat → BitVec 64) (ret : BitVec 64) :
    (Env.ofMachine r.m0 (regsPk r) vars ret).WF := by
  obtain ⟨hpk, hnw, hA⟩ := r.pk_pre hpre
  have hmap : Mapped r.m0.dmem r.pkPtr 32 := fun i hi ↦ by
    rw [hpk i (by rw [r.hpk]; exact hi)]; rfl
  exact wf_frame_ext r hpre (fun _ h ↦ h) hmap hnw hA
    (r.got_apart_pk hpre (by simp)) (r.got_apart_pk hpre (by simp)) vars ret

/-- **The frame's regions and the raw signature** are a well-formed environment. -/
theorem wfSig (hpre : r.Pre) {m : MachineData} (hk : Kept r.m0.dmem m.dmem)
    (hS : SameOutside r.m0.dmem m.dmem r.StackArea) (vars : Nat → BitVec 64) (ret : BitVec 64) :
    (Env.ofMachine m (regsSig r) vars ret).WF := by
  obtain ⟨_, hnw, hA⟩ := r.sig_pre hpre
  have hmap : Mapped m.dmem r.sigPtr 7740 := fun i hi ↦ by
    rw [r.sig_at hpre hS i (by rw [r.hsig]; exact hi)]; rfl
  exact wf_frame_ext r hpre hk hmap hnw hA
    (r.got_apart_sig hpre (by simp)) (r.got_apart_sig hpre (by simp)) vars ret

/-- **The frame's regions and FORS opening `c`** are a well-formed environment (at `b1`). -/
theorem wfOpen (hpre : r.Pre) {m : MachineData} (hk : Kept r.m0.dmem m.dmem)
    (hS : SameOutside r.m0.dmem m.dmem r.StackArea) {c : Nat} (hc : c < 24)
    (vars : Nat → BitVec 64) (ret : BitVec 64) :
    (Env.ofMachine m (regsOpen r c) vars ret).WF := by
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
  have hg : ∀ l ∈ ["memcpy", "memset"], Apart (gotAddr l) 8
      (r.sigPtr + BitVec.ofNat 64 (16 + 176 * c)) 176 := fun l hl ↦ by
    have h := r.got_apart_sig hpre hl
    unfold Apart at h ⊢; omega
  exact wf_frame_ext r hpre hk hmap hnw' hA' (hg "memcpy" (by simp)) (hg "memset" (by simp)) vars ret

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
    (hk : AllOf (fun p ↦ m.regs.get64 p.1 = p.2.eval (Env.ofMachine m (regsSig r) vars ret)) k) :
    Match (Env.ofMachine m (regsSig r) vars ret) (fSig k) m := by
  apply Match.withKnownBytes
  · apply Match.withKnownBytes
    · apply match_ofMachine
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
theorem written_stack (hpre : r.Pre) {m : MachineData} {regions : List (BitVec 64 × Nat)}
    {vars : Nat → BitVec 64} {ret : BitVec 64} (h0 : regions[0]? = some (r.base, 21632))
    (h1 : regions[1]? = some (r.base - 16#64, 16)) {S : SState} (hw : entryWrites S = true) :
    ∀ p, Sym.Written (Env.ofMachine m regions vars ret) S p → r.StackArea p := by
  have hb := r.base_toNat hpre
  rintro p ⟨w, hwm, b, sz, hr, h1', h2⟩
  simp only [entryWrites, List.all_eq_true, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at hw
  rw [r.stackArea_iff hpre]
  rcases hw w hwm with ⟨hw0, hwn⟩ | ⟨hw1, hwn⟩
  · rw [hw0] at hr
    simp only [Env.ofMachine_regions, h0, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    omega
  · rw [hw1] at hr
    simp only [Env.ofMachine_regions, h1, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    have hlo : (r.base - 16#64).toNat = r.base.toNat - 16 := toNat_sub_ofNat (by omega)
    omega

theorem written_frame (hpre : r.Pre) {m : MachineData} {regions : List (BitVec 64 × Nat)}
    {vars : Nat → BitVec 64} {ret : BitVec 64} (h0 : regions[0]? = some (r.base, 21632))
    (h1 : regions[1]? = some (r.base - 16#64, 16)) {S : SState} (hw : Run.frameWrites S = true) :
    ∀ p, Sym.Written (Env.ofMachine m regions vars ret) S p →
      r.StackArea p ∧ ¬InRange (r.off 21576) 48 p := by
  have hb := r.base_toNat hpre
  rintro p ⟨w, hwm, b, sz, hr, h1', h2⟩
  simp only [Run.frameWrites, List.all_eq_true, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at hw
  have hs := r.off_toNat hpre (a := 21576) (by decide)
  rw [r.stackArea_iff hpre, Sym.inRange_iff (by rw [hs]; omega), hs]
  rcases hw w hwm with ⟨hw0, hwn⟩ | ⟨hw1, hwn⟩
  · rw [hw0] at hr
    simp only [Env.ofMachine_regions, h0, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    omega
  · rw [hw1] at hr
    simp only [Env.ofMachine_regions, h1, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    have hlo : (r.base - 16#64).toNat = r.base.toNat - 16 := toNat_sub_ofNat (by omega)
    omega

/-- **The frame's invariant after a block** of an environment whose regions 0 and 1 are the
frame's, its writes there off the saved registers, RSP the base. -/
theorem frame_of_block (hpre : r.Pre) {m m' : MachineData} (hF : r.Frame m)
    {regions : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} {ret : BitVec 64}
    (h0 : regions[0]? = some (r.base, 21632)) (h1 : regions[1]? = some (r.base - 16#64, 16))
    {S : SState} (hm : Match (Env.ofMachine m regions vars ret) S m')
    (hwf : (Env.ofMachine m regions vars ret).WF) (hsp : S.reg .rsp = some (.ptr 0 0))
    (hw : Run.frameWrites S = true) : r.Frame m' :=
  Run.Frame.of_change hF.2.1 hF.2.2.1 hF.2.2.2
    (by rw [rspOf, hm.regs .rsp _ hsp]; simp [Sym.eval, Env.base, h0])
    (hm.sameOutside hwf) (written_frame r hpre h0 h1 hw) (hm.kept hwf)

/-- **At a call after a block** of an environment whose regions 0 and 1 are the frame's. -/
theorem atCall_of_block (hpre : r.Pre) {m m' : MachineData} (hF : r.Frame m)
    {regions : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} {ret : BitVec 64}
    (h0 : regions[0]? = some (r.base, 21632)) (h1 : regions[1]? = some (r.base - 16#64, 16))
    {S : SState} (hm : Match (Env.ofMachine m regions vars ret) S m')
    (hwf : (Env.ofMachine m regions vars ret).WF) (hsp : S.reg .rsp = some (.ptr 0 (-8)))
    (hw : Run.frameWrites S = true) : r.AtCall m' := by
  have hF' := Run.Frame.of_change hF.2.1 hF.2.2.1 hF.2.2.2 (m' := { m' with regs := m.regs }) hF.1
    (hm.sameOutside hwf) (written_frame r hpre h0 h1 hw) (hm.kept hwf)
  refine ⟨?_, hF'.2.1, hF'.2.2.1, hF'.2.2.2⟩
  rw [rspOf, hm.regs .rsp _ hsp, eval_ptr h0]
  rw [show BitVec.ofInt 64 (-8) = -8#64 by decide]
  bv_omega

end

end NativeRustcX64.SphincsVerifyProof.Parse
