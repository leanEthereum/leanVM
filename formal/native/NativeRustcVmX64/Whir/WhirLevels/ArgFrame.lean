module

public import NativeRustcVmX64.Transcript.Frame

/-!
# A frame whose region also holds the stack arguments (x86-64)

`NativeRustcVmX64.Transcript.Frame`'s region 0 is the `F` bytes below the entry's RSP and the
return address (`F + 8` bytes). `next_level`, `final_level` and `whir_levels` read their seventh
argument word above the return address (`F + 8(%rsp)` in their bodies), so their blocks run in
`argEnv`, region 0 `A` bytes longer: the frame, the return address, `A` bytes of arguments.
`Frame` (RSP, slots, return address, callee-saved registers, mapped bytes) is the same predicate;
its prologue, block and epilogue rules are restated for `argEnv` (`Frame.of_prologueA`,
`Frame.of_blockA`, `Frame.epilogueA`, `Frame.load_retA`), and the arguments' words are what the
environment loads where they are kept (`load_argA`).
-/

namespace NativeRustcVmX64.Whir.Levels

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVm.Transcript NativeRustcVmX64.Transcript

@[expose] public section

/-- A block's environment: region 0 the frame, the return address and `A` bytes of stack
arguments, then `rest`. -/
abbrev argEnv (m0 d : MachineData) (F A : Nat) (rest : List (BitVec 64 × Nat))
    (vars : Nat → BitVec 64 := fun _ ↦ 0) (ret : BitVec 64 := 0) : Env :=
  Env.ofMachine d ((stackBelow m0 F, F + 8 + A) :: rest) vars ret

end

public section

variable {m0 d d' : MachineData} {F A n : Nat} {slots : Slots}

theorem argEnv_wf {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} {ret : BitVec 64}
    (hok : NativeRustcVm.Mapped d.dmem (stackBelow m0 F) (F + 8 + A) ∧
      NativeRustcVm.NoWrap (stackBelow m0 F) (F + 8 + A))
    (hrest : ∀ x ∈ rest, NativeRustcVm.Mapped d.dmem x.1 x.2 ∧ NativeRustcVm.NoWrap x.1 x.2)
    (hap : ((stackBelow m0 F, F + 8 + A) :: rest).Pairwise
      fun x y ↦ NativeRustcVm.Apart x.1 x.2 y.1 y.2) :
    (argEnv m0 d F A rest vars ret).WF where
  noWrap r b k hb := by
    cases r with
    | zero => cases hb; exact hok.2
    | succ r => exact (hrest _ (List.mem_of_getElem? hb)).2
  mapped r b k hb := by
    cases r with
    | zero => cases hb; exact hok.1
    | succ r => exact (hrest _ (List.mem_of_getElem? hb)).1
  disjoint r r' b b' k k' hne hb hb' := by
    have := List.pairwise_iff_getElem.mp hap
    simp only [Env.ofMachine_regions] at hb hb'
    obtain ⟨hr, hbr⟩ := List.getElem?_eq_some_iff.mp hb
    obtain ⟨hr', hbr'⟩ := List.getElem?_eq_some_iff.mp hb'
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have := this r r' hr hr' h
      rw [hbr, hbr'] at this
      unfold NativeRustcVm.Apart at this
      exact this
    · have := this r' r hr' hr h
      rw [hbr, hbr'] at this
      unfold NativeRustcVm.Apart at this
      dsimp only at this
      omega

theorem eval_ptr0A [Labels] {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    {ret : BitVec 64} (o : Nat) : (Sym.ptr 0 (o : Int)).eval (argEnv m0 d F A rest vars ret) =
      off (stackBelow m0 F) o := by
  show (argEnv m0 d F A rest vars ret).base 0 + BitVec.ofInt 64 (o : Int) = _
  rw [BitVec.ofInt_natCast]
  rfl

/-- RSP at the entry, as region 0's offset `F`. -/
theorem match_rspA [Labels] {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    {ret : BitVec 64} :
    m0.regs.get64 .rsp = (Sym.ptr 0 (F : Int)).eval (argEnv m0 d F A rest vars ret) := by
  rw [eval_ptr0A, off_frame_F]
  rfl

/-- RSP in a frame, as region 0's offset `o`. -/
theorem Frame.rsp_evalA [Labels] {o : Nat} {rest : List (BitVec 64 × Nat)}
    {vars : Nat → BitVec 64} {ret : BitVec 64} (hf : Frame m0 F slots o d) :
    d.regs.get64 .rsp = (Sym.ptr 0 (o : Int)).eval (argEnv m0 d F A rest vars ret) := by
  rw [eval_ptr0A]
  exact hf.sp

/-- A byte of region 0 no write of a block covers. -/
theorem not_written0A [Labels] {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    {ret : BitVec 64} {S : SState} (hwf : (argEnv m0 d F A rest vars ret).WF)
    (hm : Match (argEnv m0 d F A rest vars ret) S d') (hin : writesIn S = true) {j : Nat}
    (hj : j < F + 8 + A) (hmiss : ∀ w ∈ S.mem, w.r = 0 → w.off + w.n ≤ j ∨ j < w.off) :
    ¬ Written (argEnv m0 d F A rest vars ret) S (off (stackBelow m0 F) j) := by
  rintro ⟨w, hw, b, sz, hb, h1, h2⟩
  have hnw0 := hwf.noWrap 0 (stackBelow m0 F) (F + 8 + A) rfl
  have hq : (off (stackBelow m0 F) j).toNat = (stackBelow m0 F).toNat + j := toNat_off (by omega)
  rw [hq] at h1 h2
  by_cases hr : w.r = 0
  · rw [hr] at hb
    cases hb
    rcases hmiss w hw hr with h | h <;> omega
  · unfold writesIn at hin
    rw [List.all_eq_true] at hin
    have hw' := hin w hw
    obtain ⟨sz', hS'⟩ : ∃ sz', S.regions[w.r]? = some sz' := by
      revert hw'
      cases S.regions[w.r]? with
      | none => simp
      | some x => exact fun _ ↦ ⟨x, rfl⟩
    rw [hS'] at hw'
    simp only [decide_eq_true_eq] at hw'
    obtain ⟨b', hb'⟩ := hm.regions _ _ hS'
    rw [hb] at hb'
    cases hb'
    have := hwf.disjoint 0 w.r _ _ _ _ (Ne.symm hr) rfl hb
    omega

/-- **The prologue** establishes the frame (`Frame.of_prologue` in `argEnv`). -/
theorem Frame.of_prologueA [Labels] {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    {ret : BitVec 64} {S : SState} {o o' : Nat} (hf : Frame m0 F [] o d)
    (hwf : (argEnv m0 d F A rest vars ret).WF)
    (hm : Match (argEnv m0 d F A rest vars ret) S d') (hS : ProOk F o' slots S = true)
    (hle : ∀ p ∈ slots, p.1 + 8 ≤ F) (hcs : ∀ p ∈ slots, calleeSaved p.2 = true) :
    Frame m0 F slots o' d' := by
  simp only [ProOk, Bool.and_eq_true, beq_iff_eq] at hS
  obtain ⟨⟨⟨⟨hw, hk⟩, hbr⟩, hin⟩, hsp⟩ := hS
  refine ⟨?_, fun p hp ↦ ?_, fun j hj ↦ ?_, kept_trans hf.kept (hm.kept hwf), fun r hr hs ↦ ?_⟩
  · show d'.regs.get64 .rsp = _
    rw [hm.regs .rsp _ hsp, eval_ptr0A]
  · unfold slotsWritten at hw
    rw [List.all_eq_true] at hw
    have hp' := hw p hp
    rw [List.all_eq_true] at hp'
    have := wordAt_write hm (r := 0) (o := p.1) rfl (by have := hle p hp; omega) (v := .reg p.2)
      fun t ht ↦ by
        have := hp' t (List.mem_range.mpr ht)
        simpa using this
    rwa [show (Sym.reg p.2).eval (argEnv m0 d F A rest vars ret) = reg m0 p.2 from
      hf.regs p.2 (hcs p hp) rfl] at this
  · rw [hm.get?_mem0 hwf (not_written0A hwf hm hin (by omega) fun w hw hr ↦ ?_)]
    · exact hf.ret j hj
    · have := belowRet_spec hbr w hw hr
      omega
  · exact (hm.regs r _ (keepsOthers_spec hk hr hs)).trans (hf.regs r hr rfl)

/-- **A block** keeps the frame (`Frame.of_block` in `argEnv`). -/
theorem Frame.of_blockA [Labels] {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    {ret : BitVec 64} {S : SState} {o o' : Nat} (hf : Frame m0 F slots o d)
    (hwf : (argEnv m0 d F A rest vars ret).WF)
    (hm : Match (argEnv m0 d F A rest vars ret) S d') (hS : MidOk F o' slots S = true)
    (hle : ∀ p ∈ slots, p.1 + 8 ≤ F) : Frame m0 F slots o' d' := by
  simp only [MidOk, Bool.and_eq_true, beq_iff_eq] at hS
  obtain ⟨⟨⟨⟨hu, hbr⟩, hin⟩, hk⟩, hsp⟩ := hS
  refine ⟨?_, fun p hp ↦ ?_, fun j hj ↦ ?_, kept_trans hf.kept (hm.kept hwf), fun r hr hs ↦ ?_⟩
  · show d'.regs.get64 .rsp = _
    rw [hm.regs .rsp _ hsp, eval_ptr0A]
  · refine bytesAt_congr (hf.slot p hp) fun i hi ↦ ?_
    have hi' : i < 8 := by simpa [LeanVM.Protocol.KeccakHash.wordBytes] using hi
    rw [off_add]
    refine (hm.get?_mem0 hwf (not_written0A hwf hm hin (by have := hle p hp; omega)
      fun w hw hr ↦ ?_))
    have := slotsUntouched_spec hu w hw hr p hp
    omega
  · rw [hm.get?_mem0 hwf (not_written0A hwf hm hin (by omega) fun w hw hr ↦ ?_)]
    · exact hf.ret j hj
    · have := belowRet_spec hbr w hw hr
      omega
  · have := hm.regs r _ (keepsOthers_spec hk hr hs)
    rw [Sym.eval, Env.ofMachine_regs] at this
    exact this.trans (hf.regs r hr hs)

/-- The return address, loaded from region 0 (`Frame.load_ret` in `argEnv`). -/
theorem Frame.load_retA {o : Nat} {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    {ret : BitVec 64} (hf : Frame m0 F slots o d) (h : StackOk m0 n) (hF : F ≤ n) :
    Int64.ofBitVec ((argEnv m0 d F A rest vars ret).load 0 F 8) = retOf m0 := by
  have := hf.load_ret (rest := rest) (vars := vars) (ret := ret) h hF
  exact this

/-- **The epilogue** restores the registers (`Frame.epilogue` in `argEnv`). -/
theorem Frame.epilogueA [Labels] {o : Nat} {rest : List (BitVec 64 × Nat)}
    {vars : Nat → BitVec 64} {ret : BitVec 64} {S : SState} (hf : Frame m0 F slots o d)
    (hwf : (argEnv m0 d F A rest vars ret).WF)
    (hm : Match (argEnv m0 d F A rest vars ret) S d') (hS : EpiOk F slots S = true) :
    Saved m0 d' ∧ rspOf d' = rspOf m0 + 8#64 := by
  simp only [EpiOk, Bool.and_eq_true, beq_iff_eq] at hS
  obtain ⟨⟨hl, hk⟩, hsp⟩ := hS
  have hslot : ∀ p ∈ slots, reg d' p.2 = reg m0 p.2 := by
    intro p hp
    unfold slotsLoaded at hl
    rw [List.all_eq_true] at hl
    have := hm.regs p.2 _ (by simpa using hl p hp)
    rw [Sym.eval, load_ofMachine (o := p.1) rfl (hf.slot p hp)] at this
    exact this
  refine ⟨⟨fun r hr ↦ ?_, kept_trans hf.kept (hm.kept hwf)⟩, ?_⟩
  · cases hs : slots.any (·.2 == r)
    · have := hm.regs r _ (keepsOthers_spec hk hr hs)
      rw [Sym.eval, Env.ofMachine_regs] at this
      exact this.trans (hf.regs r hr hs)
    · obtain ⟨p, hp, hpr⟩ := List.any_eq_true.mp hs
      rw [← Reg64.eq_of_beq hpr]
      exact hslot p hp
  · show d'.regs.get64 .rsp = _
    rw [hm.regs .rsp _ hsp, eval_ptr0A, frame_add]

/-- **A stack argument's word**, kept in `d`, is what `argEnv` loads at `F + 8 + 8 i`. -/
theorem load_argA {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} {ret : BitVec 64}
    {i : Nat} {v : UInt64}
    (h : NativeRustcVm.WordAt d.dmem (rspOf m0 + BitVec.ofNat 64 (8 + 8 * i)) v) :
    (argEnv m0 d F A rest vars ret).load 0 (F + 8 + 8 * i) 8 = v.toBitVec := by
  refine (Env.load_of_bytesAt (NativeRustcVm.length_wordBytes v) ?_).trans
    (ofInt_ofBytes_wordBytes v)
  rw [show (argEnv m0 d F A rest vars ret).base 0 + BitVec.ofNat 64 (F + 8 + 8 * i) =
      off (stackBelow m0 F) (F + (8 + 8 * i)) by rw [Nat.add_assoc]; rfl, frame_add]
  exact h

end

end NativeRustcVmX64.Whir.Levels
