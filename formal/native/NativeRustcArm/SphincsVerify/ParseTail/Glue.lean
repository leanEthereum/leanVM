module

public import NativeRustcArm.Code.Common.Memcpy.Names
public import NativeRustcArm.Code.Common.Memset.Names

public import NativeRustcArm.SphincsVerify.Parse.Glue
public import NativeRustcArm.SphincsVerify.Rev

/-!
# The parse's tail: what its blocks share

The tail (`b7 .. b35`) runs each straight block from `fs known`: region 0 the frame (`21616`),
region 1 the raw signature buffer (`r.sigPtr`, `7740`), SP region 0's base, X29 the saved
registers' address (`21520`), the `known` registers. A block ending in `bl memcpy`
(`block_memcpy`), `bl memset` (`block_memset`) or falling through (`block_fall`) is the block's
summary then, for a call, the callee's contract between frame offsets. The copy loops (`b9`,
`b17`, `b25`) copy 16 bytes a turn between a 16-byte frame region and a 16-byte raw-signature
region rebased each turn (`loopS`, `copy_turn`).
-/

namespace NativeRustcArm.SphincsVerifyProof.ParseTail

open NativeRustc NativeRustc.Sphincs NativeRustcArm.Sym NativeRustcArm.SphincsVerifyProof.Parse
  LeanVM.Protocol.KeccakHash

@[expose] public section

/-- A straight block's start: region 0 the frame, region 1 the raw signature, SP region 0's base,
X29 the saved registers', `known`. -/
def fs (known : List (XReg × Sym)) : SState :=
  init [(21616, true), (7740, false)] (.ptr 0 0) ((.X29, .ptr 0 21520) :: known)

/-- A copy loop's turn: region 0 the 16 destination bytes at `D + X8`, region 1 the 16 source
bytes at `X9 + X8`. -/
def loopS (D : XReg) : SState :=
  init [(16, false), (16, false)] .sp [] [] []
    [(.bin .add .W64 (.reg D) (.reg .X8), 0, 0), (.bin .add .W64 (.reg .X9) (.reg .X8), 1, 0)]

/-- The parse tail's environment: region 0 the frame, region 1 the raw signature buffer. -/
abbrev envSig (r : Run) (m : MachineData) (vars : Nat → BitVec 64 := fun _ ↦ 0) : Env :=
  Env.ofMachine m [(r.base, 21616), (r.sigPtr, 7740)] vars

end

public section

section
variable (r : Run) [Labels]

theorem ptr_eval (m : MachineData) (vars : Nat → BitVec 64) (a : Nat) :
    (Sym.ptr 0 a).eval (envSig r m vars) = r.off a := by
  show r.base + BitVec.ofInt 64 (a : Int) = r.base + BitVec.ofNat 64 a
  rw [BitVec.ofInt_natCast]

theorem ptr1_eval (m : MachineData) (vars : Nat → BitVec 64) (a : Nat) :
    (Sym.ptr 1 a).eval (envSig r m vars) = r.sigPtr + BitVec.ofNat 64 a := by
  show r.sigPtr + BitVec.ofInt 64 (a : Int) = r.sigPtr + BitVec.ofNat 64 a
  rw [BitVec.ofInt_natCast]

theorem envSig_wf (hpre : r.Pre) {m : MachineData} (hF : r.Frame m) (vars : Nat → BitVec 64) :
    (envSig r m vars).WF := by
  have hf := r.frame_mapped hpre hF (a := 0) (n := 21616) (by decide)
  rw [Run.off_zero] at hf
  have hA := r.apart_off_ext hpre (a := 0) (n := 21616) (by decide) (r.pre_sig hpre).2.2
  rw [Run.off_zero] at hA
  exact Env.wf_of ⟨hf, r.sig_mapped hpre hF, trivial⟩ (List.pairwise_pair.mpr hA)

/-- The frame's invariant after a block run in `envSig`. -/
theorem frame_of_match_sig (hpre : r.Pre) {m m' : MachineData} (hF : r.Frame m)
    {vars : Nat → BitVec 64} {S : SState} (hm : Match (envSig r m vars) S m')
    (hwf : (envSig r m vars).WF) (hsp : S.sp = .ptr 0 0) (hx29 : S.reg .X29 = some (.ptr 0 21520))
    (hw : Run.frameWrites S = true) : r.Frame m' := by
  have hb := r.base_toNat hpre
  have := r.m0.regs.SP.toNat_lt
  refine hF.of_block ?_ ?_ (hm.sameOutside hwf) ?_ (hm.kept hwf)
  · rw [hm.sp, hsp]
    show r.base + BitVec.ofInt 64 0 = r.base
    simp
  · rw [hm.regs .X29 _ hx29]
    rfl
  · rintro p ⟨w, hwm, b, sz, hr, h1, h2⟩
    simp only [Run.frameWrites, List.all_eq_true, Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq] at hw
    obtain ⟨hw0, hwn⟩ := hw w hwm
    rw [hw0] at hr
    cases hr
    exact r.inRange_off hpre (a := 0) (n := 21520) (by decide) (by
      rw [Run.off_zero, Sym.inRange_iff (by omega)]
      omega)

/-- Frame bytes not written by a block in `envSig` (which only writes in region 0) are kept. -/
theorem bytesAt_kept_sig (hpre : r.Pre) {m m' : MachineData} {vars : Nat → BitVec 64}
    {S : SState} (hm : Match (envSig r m vars) S m') (hwf : (envSig r m vars).WF)
    (hfw : Run.frameWrites S = true) {o : Nat}
    {bs : List UInt8} (ho : o + bs.length ≤ 21616) (h : BytesAt m.dmem (r.off o) bs)
    (hn : Run.noWriteIn S o bs.length = true) : BytesAt m'.dmem (r.off o) bs := by
  have hb := r.base_toNat hpre
  have := r.m0.regs.SP.toNat_lt
  have hoff := r.off_toNat hpre (a := o) (by omega)
  refine bytesAt_of_sameOutside h (hm.sameOutside hwf) fun i hi ⟨w, hwm, b, sz, hr, h1, h2⟩ ↦ ?_
  simp only [Run.frameWrites, List.all_eq_true, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at hfw
  have hw0 := (hfw w hwm).1
  simp only [Run.noWriteIn, List.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq,
    decide_eq_true_eq] at hn
  have hw := hn w hwm
  rw [hw0] at hr hw
  cases hr
  rw [Sym.toNat_add_ofNat _ _ (by omega), hoff] at h1 h2
  omega

/-- `envSig` and `fs known` describe a state of the frame whose `known` registers are their values. -/
theorem match_fs (hpre : r.Pre) {m : MachineData} (hF : r.Frame m) {known : List (XReg × Sym)}
    (hkn : AllOf (fun p ↦ (m.regs.getXReg p.1).toBitVec = p.2.eval (envSig r m)) known) :
    Match (envSig r m) (fs known) m :=
  match_ofMachine ⟨rfl, fun _ ↦ r.base_aligned hpre, ⟨rfl, fun h ↦ absurd h Bool.false_ne_true, trivial⟩⟩
    (by show m.regs.SP.toBitVec = r.base + BitVec.ofInt 64 0; simp [hF.1])
    ⟨hF.2.1.trans (ptr_eval r m (fun _ ↦ 0) 21520).symm, hkn⟩ trivial trivial trivial

end

section
variable (r : Run) [ElfHost]

/-- **A straight block ending in `bl memcpy`** between frame offsets: the block's summary, then
`memcpy`'s contract; `cont` from the return address. -/
theorem block_memcpy (hp : PlacedIn Sphincs.SphincsVerify.code r.sec r.k) (hc : Callees) (hpre : r.Pre)
    {ds : List Directive} {j : Nat} (hk : ds.IsInfixAt Sphincs.SphincsVerify.code j)
    {known : List (XReg × Sym)} {S' : SState} (hx : exec ds (fs known) = some (S', .call NativeRustcArm.Common.Memcpy.entryLabel))
    (hw : Run.frameWrites S' = true) (hsp : S'.sp = .ptr 0 0) (h29 : S'.reg .X29 = some (.ptr 0 21520))
    {a b n : Nat} (h0 : S'.reg .X0 = some (.ptr 0 a)) (h1 : S'.reg .X1 = some (.ptr 0 b))
    (h2 : S'.reg .X2 = some (.lit n)) (hn : n < 2 ^ 64) (ha : a + n ≤ 21520) (hb : b + n ≤ 21616)
    (hab : a + n ≤ b ∨ b + n ≤ a) {m : MachineData} (hF : r.Frame m)
    (hkn : AllOf (fun p ↦ (m.regs.getXReg p.1).toBitVec = p.2.eval (envSig r m)) known)
    {R : MachineState → Prop}
    (cont : ∀ (m' : MachineData) (st' : MachineState), Match (envSig r m) S' m' →
      st'.pc = r.pc (j + ds.length) → r.Frame st'.data → Saved m' st'.data →
      BytesAt st'.data.dmem (r.off a) (bytesOf m'.dmem (r.off b) n) →
      SameOutside m'.dmem st'.data.dmem (InRange (r.off a) n) →
      Eventually (elfStep1 ElfHost.exe) R st') :
    Eventually (elfStep1 ElfHost.exe) R ⟨m, r.pc j⟩ := by
  have hk' : ds.IsInfixAt (ElfHost.sectionProg r.sec) (r.k + j) := hk.trans hp.1 (by
    rintro rfl; cases hx)
  have hwf := envSig_wf r hpre hF (fun _ ↦ 0)
  refine exec_then_elf hk' hx hwf (match_fs r hpre hF hkn) fun st hm' hpc ↦ ?_
  have hF' := frame_of_match_sig r hpre hF hm' hwf hsp h29 hw
  have hx0 : (st.data.regs.getXReg .X0).toBitVec = r.off a := by
    rw [hm'.regs .X0 _ h0, ptr_eval]
  have hx1 : (st.data.regs.getXReg .X1).toBitVec = r.off b := by
    rw [hm'.regs .X1 _ h1, ptr_eval]
  have hx2 : (st.data.regs.getXReg .X2).toNat = n := by
    show (st.data.regs.getXReg .X2).toBitVec.toNat = n
    rw [hm'.regs .X2 _ h2]
    simp only [Sym.eval, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt hn
  refine memcpy_frame r hpre hc hpc hF' hx0 hx1 hx2 ha hb hab fun st' hpc' hF'' hS hb' hout ↦ ?_
  exact cont st.data st' hm' (by rw [hpc', Run.pc, Nat.add_assoc]) hF'' hS hb' hout

/-- **A straight block ending in `bl memset`** of frame offsets. -/
theorem block_memset (hp : PlacedIn Sphincs.SphincsVerify.code r.sec r.k) (hc : Callees) (hpre : r.Pre)
    {ds : List Directive} {j : Nat} (hk : ds.IsInfixAt Sphincs.SphincsVerify.code j)
    {known : List (XReg × Sym)} {S' : SState} (hx : exec ds (fs known) = some (S', .call NativeRustcArm.Common.Memset.entryLabel))
    (hw : Run.frameWrites S' = true) (hsp : S'.sp = .ptr 0 0) (h29 : S'.reg .X29 = some (.ptr 0 21520))
    {a n : Nat} (h0 : S'.reg .X0 = some (.ptr 0 a)) (h2 : S'.reg .X2 = some (.lit n))
    (hn : n < 2 ^ 64) (ha : a + n ≤ 21520) {m : MachineData} (hF : r.Frame m)
    (hkn : AllOf (fun p ↦ (m.regs.getXReg p.1).toBitVec = p.2.eval (envSig r m)) known)
    {R : MachineState → Prop}
    (cont : ∀ (m' : MachineData) (st' : MachineState), Match (envSig r m) S' m' →
      st'.pc = r.pc (j + ds.length) → r.Frame st'.data → Saved m' st'.data →
      SameOutside m'.dmem st'.data.dmem (InRange (r.off a) n) →
      Eventually (elfStep1 ElfHost.exe) R st') :
    Eventually (elfStep1 ElfHost.exe) R ⟨m, r.pc j⟩ := by
  have hk' : ds.IsInfixAt (ElfHost.sectionProg r.sec) (r.k + j) := hk.trans hp.1 (by
    rintro rfl; cases hx)
  have hwf := envSig_wf r hpre hF (fun _ ↦ 0)
  refine exec_then_elf hk' hx hwf (match_fs r hpre hF hkn) fun st hm' hpc ↦ ?_
  have hF' := frame_of_match_sig r hpre hF hm' hwf hsp h29 hw
  have hx0 : (st.data.regs.getXReg .X0).toBitVec = r.off a := by
    rw [hm'.regs .X0 _ h0, ptr_eval]
  have hx2 : (st.data.regs.getXReg .X2).toNat = n := by
    show (st.data.regs.getXReg .X2).toBitVec.toNat = n
    rw [hm'.regs .X2 _ h2]
    simp only [Sym.eval, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt hn
  refine memset_frame r hpre hc hpc hF' hx0 hx2 ha fun st' hpc' hF'' hS hout ↦ ?_
  exact cont st.data st' hm' (by rw [hpc', Run.pc, Nat.add_assoc]) hF'' hS hout

/-- **A straight block falling through.** -/
theorem block_fall (hp : PlacedIn Sphincs.SphincsVerify.code r.sec r.k) (hpre : r.Pre)
    {ds : List Directive} {j : Nat} (hk : ds.IsInfixAt Sphincs.SphincsVerify.code j)
    {known : List (XReg × Sym)} {S' : SState} (hne : ds ≠ [])
    (hx : exec ds (fs known) = some (S', .fall))
    (hw : Run.frameWrites S' = true) (hsp : S'.sp = .ptr 0 0) (h29 : S'.reg .X29 = some (.ptr 0 21520))
    {m : MachineData} (hF : r.Frame m)
    (hkn : AllOf (fun p ↦ (m.regs.getXReg p.1).toBitVec = p.2.eval (envSig r m)) known)
    {R : MachineState → Prop}
    (cont : ∀ st' : MachineState, Match (envSig r m) S' st'.data → st'.pc = r.pc (j + ds.length) →
      r.Frame st'.data → Eventually (elfStep1 ElfHost.exe) R st') :
    Eventually (elfStep1 ElfHost.exe) R ⟨m, r.pc j⟩ := by
  have hk' : ds.IsInfixAt (ElfHost.sectionProg r.sec) (r.k + j) := hk.trans hp.1 hne
  have hwf := envSig_wf r hpre hF (fun _ ↦ 0)
  refine exec_then_elf hk' hx hwf (match_fs r hpre hF hkn) fun st hm' hpc ↦ ?_
  exact cont st hm' (by rw [show st.pc = _ from hpc, Run.pc, Nat.add_assoc])
    (frame_of_match_sig r hpre hF hm' hwf hsp h29 hw)

end

end

end NativeRustcArm.SphincsVerifyProof.ParseTail
