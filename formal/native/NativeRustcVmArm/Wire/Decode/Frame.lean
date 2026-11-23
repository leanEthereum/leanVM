module

public import NativeRustcVmArm.Code.Vm.ReaderLe.Names
public import NativeRustcVmArm.Wire.Decode.Basic

/-!
# `decode`'s frame

The places from the precondition (`geo_of`), the frame's environment (`frEnv_wf`,
`frEnv_match`), the outputs apart from the frame (`Geo.notFrame`), the reader kept by a change
apart from it (`Geo.reader_keep`), a call of `Reader::le` for four bytes (`le4_call`), and the
way out with `None` (`exit15`, `exit14`).
-/

namespace NativeRustcVmArm.Wire.Decode

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Wire NativeVm NativeVm.Wire
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt InAny Region)
open NativeRustcVmArm.Vm.Decode
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

public section

variable {m0 : MachineData} {B : List UInt8}

/-- **The places** from the precondition and the wire's bytes. -/
theorem geo_of [Labels] (h : DecodePre m0) (hl : B.length = Ln m0)
    (hb : BytesAt m0.dmem (bpA m0) B) : Geo m0 B := by
  obtain ⟨hst, hrc, hL, hdw, hbOk, hdOk, hwOk, hd1, hd2⟩ := h
  simp only [NativeRustcVm.Disjoint, List.pairwise_cons, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true] at hd1 hd2
  obtain ⟨⟨h1, h2, h3⟩, ⟨h4, h5⟩, h6⟩ := hd1
  exact ⟨hst, hrc, hl, hb, hL, hdw, hbOk.2, hdOk, hwOk, h1, h2, h3, h4, h5, h6.1,
    fun hp ↦ (hd2 hp).1.2.1, fun hp ↦ (hd2 hp).2.1.1, fun hp ↦ (hd2 hp).2.2.1.1,
    fun hp ↦ (hd2 hp).2.2.1.2⟩

theorem base_aligned (hst : StackOk m0 1280) : (base m0 96).toNat % 16 = 0 := by
  rw [Ring.base_toNat (by have := hst.2.1; omega)]; have := hst.1; omega

theorem frEnv_wf (hst : StackOk m0 1280) {m : MachineData} (hfr : Frm m0 m) :
    (frEnv m0 m).WF :=
  Env.wf_of ⟨⟨fun j hj ↦ hfr.kept _ (Ring.frame_mapped hst (by omega) j hj),
    Ring.base_noWrap (by have := hst.2.1; omega)⟩, trivial⟩ (List.pairwise_singleton _ _)

theorem frEnv_match [Labels] (hst : StackOk m0 1280) {m : MachineData} (hfr : Frm m0 m) :
    Match (frEnv m0 m) frS m :=
  match_ofMachine ⟨rfl, fun _ ↦ base_aligned hst, trivial⟩ (by rw [hfr.sp]; simp [Sym.eval])
    trivial trivial trivial trivial

section
variable [Labels]

theorem Geo.sp (G : Geo m0 B) : 1280 ≤ m0.regs.SP.toNat := G.st.2.1

theorem Geo.base_toNat (G : Geo m0 B) {F : Nat} (hF : F ≤ 1280) :
    (base m0 F).toNat = m0.regs.SP.toNat - F := Ring.base_toNat (by have := G.sp; omega)

theorem Geo.rdr_toNat (G : Geo m0 B) : (rdr m0).toNat = m0.regs.SP.toNat - 88 := by
  have hb := G.base_toNat (F := 96) (by omega)
  have hsp := G.sp
  have hSP := m0.regs.SP.toNat_lt
  rw [NativeRustcVm.toNat_add_ofNat (by omega), hb]
  omega

theorem Geo.dNw (G : Geo m0 B) : (decA m0).toNat + 8 * lenW m0 ≤ 2 ^ 64 := G.dOk.2
theorem Geo.wNw (G : Geo m0 B) : (wk m0).toNat + workBytes ≤ 2 ^ 64 := G.wOk.2

theorem Geo.rdr_base (G : Geo m0 B) :
    (rdr m0).toNat = (base m0 1280).toNat + 1192 ∧ (base m0 1280).toNat + 1280 < 2 ^ 64 := by
  have := G.rdr_toNat
  have := G.base_toNat (F := 1280) le_rfl
  have := G.sp
  have := m0.regs.SP.toNat_lt
  omega

/-- **The outputs miss the frame.** -/
theorem Geo.notFrame (G : Geo m0 B) : ∀ q, W m0 q → ¬InRange (base m0 96) 96 q := by
  intro q hq hin
  have hb := G.base_toNat (F := 96) (by omega)
  have hb' := G.base_toNat (F := 1280) le_rfl
  have hsp := G.sp
  have hSP := m0.regs.SP.toNat_lt
  rw [Sym.inRange_iff (by omega), hb] at hin
  have hsD := G.sD
  have hsW := G.sW
  unfold NativeRustcVm.Apart at hsD hsW
  rcases hq with h | h
  · rw [Sym.inRange_iff G.dNw] at h; omega
  · rw [Sym.inRange_iff G.wNw] at h; omega

/-- **The reader kept** by a change of memory that misses it and the wire's bytes. -/
theorem Geo.reader_keep (G : Geo m0 B) {d d' : Mem 64} {c : Nat}
    (h : ReaderAt d (rdr m0) (bpA m0) B c) {R : BitVec 64 → Prop} (hs : SameOutside d d' R)
    (hR : ∀ q, R q → (q.toNat < m0.regs.SP.toNat - 88 ∨ m0.regs.SP.toNat - 64 ≤ q.toNat) ∧
      (0 < Ln m0 → q.toNat < (bpA m0).toNat ∨ (bpA m0).toNat + Ln m0 ≤ q.toNat)) :
    ReaderAt d' (rdr m0) (bpA m0) B c := by
  have hr := G.rdr_toNat
  have hsp := G.sp
  have hSP := m0.regs.SP.toNat_lt
  have hbn := G.bNw
  unfold NoWrap at hbn
  refine h.frame hs (fun i hi hq ↦ ?_) (fun i hi hq ↦ ?_)
  · have := (hR _ hq).1
    rw [NativeRustcVm.toNat_add_ofNat (by omega), hr] at this
    omega
  · have := (hR _ hq).2 (by rw [G.len] at hi; omega)
    rw [G.len] at hi
    rw [NativeRustcVm.toNat_add_ofNat (by omega)] at this
    omega

/-- The reader is kept by a change in the outputs. -/
theorem Geo.notReader (G : Geo m0 B) {q : BitVec 64} (hq : W m0 q) :
    (q.toNat < m0.regs.SP.toNat - 88 ∨ m0.regs.SP.toNat - 64 ≤ q.toNat) ∧
      (0 < Ln m0 → q.toNat < (bpA m0).toNat ∨ (bpA m0).toNat + Ln m0 ≤ q.toNat) := by
  have hb' := G.base_toNat (F := 1280) le_rfl
  have hsp := G.sp
  have hsD := G.sD
  have hsW := G.sW
  unfold NativeRustcVm.Apart at hsD hsW
  refine ⟨?_, fun hl ↦ ?_⟩
  · rcases hq with h | h
    · rw [Sym.inRange_iff G.dNw] at h; omega
    · rw [Sym.inRange_iff G.wNw] at h; omega
  · have hbD := G.bD hl
    have hbW := G.bW hl
    unfold NativeRustcVm.Apart at hbD hbW
    rcases hq with h | h
    · rw [Sym.inRange_iff G.dNw] at h; omega
    · rw [Sym.inRange_iff G.wNw] at h; omega

omit [Labels] in
/-- The reader's cursor is the frame's byte 24. -/
theorem cur_eq (m0 : MachineData) :
    NativeRustcVm.Transcript.off (rdr m0) 16 = base m0 96 + BitVec.ofNat 64 24 :=
  NativeRustcVm.addr_add_add _ _ _

/-- A callee's stack below the frame is the function's. -/
theorem stack_sub (G : Geo m0 B) {m : MachineData} (hfr : Frm m0 m) {N' : Nat}
    (hN' : 96 + N' ≤ 1280) {q : BitVec 64} (h : InRange (stackBelow m N') N' q) :
    InRange (base m0 1280) 1280 q := by
  have hN := G.sp
  have hSP := m0.regs.SP.toNat_lt
  rw [Ring.stackBelow_eq hfr.sp (by omega)] at h
  have hb1 := Ring.base_toNat (m0 := m0) (F := 96 + N') (by omega)
  have hb2 := Ring.base_toNat (m0 := m0) (F := 1280) hN
  rw [Sym.inRange_iff (by rw [hb1]; omega), hb1] at h
  rw [Sym.inRange_iff (by rw [hb2]; omega), hb2]
  omega

end

/-- The final memory: the entry's but in the stack and the outputs. -/
theorem same_res {m : MachineData} (h : Frm m0 m) :
    SameOutside m0.dmem m.dmem
      (InAny [⟨decA m0, 8 * lenW m0⟩, ⟨wk m0, workBytes⟩, stackR m0 decodeStack]) :=
  NativeRustcVm.SameOutside.mono h.same fun q hq ↦ by
    rcases hq with h | h | h
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), h⟩
    · exact ⟨_, List.mem_cons_self, h⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h⟩

variable [Host]

/-- **A call of `Reader::le` for four bytes** from a state of the frame. -/
theorem le4_call (hle : Spec (Labels.label NativeRustcVmArm.Vm.ReaderLe.entryLabel) ReaderLePre ReaderLePost)
    (G : Geo m0 B) {c : Nat} {st : MachineState} {next : Int64} {R : MachineState → Prop}
    (hfr : Frm m0 st.data) (hR : ReaderAt st.data.dmem (rdr m0) (bpA m0) B c)
    (hx0 : st.data.regs.X0.toBitVec = rdr m0) (hx1 : st.data.regs.X1.toNat = 4)
    (hpc : st.pc = Labels.label NativeRustcVmArm.Vm.ReaderLe.entryLabel ∧ retOf st.data = next)
    (cont : ∀ m2, Frm m0 m2 →
      (∀ x, calleeSaved x = true → m2.regs.getXReg x = st.data.regs.getXReg x) →
      SameOutside st.data.dmem m2.dmem (InRange (base m0 96 + BitVec.ofNat 64 24) 8) →
      Read4 (rdr m0) (bpA m0) B c m2 → Eventually (step1 Host.exe) R ⟨m2, next⟩) :
    Eventually (step1 Host.exe) R st := by
  have hN := G.sp
  have hP : ReaderLePre st.data :=
    ⟨hfr.stackOk G.st (by decide) (by unfold readerLeStack; omega), .inl hx1, bpA m0, B, c,
      by rw [hx0]; exact hR⟩
  refine Fr.leafIn (N' := readerLeStack) (lo := 24) (n := 8) hfr hN
    (by unfold readerLeStack; omega) (by omega) (by decide) (by decide) G.notFrame
    (Spec.carry hle fun m ↦ m.regs.X0.toBitVec = rdr m0)
    hpc ⟨hP, hx0⟩ (fun m' ⟨⟨_, hs, hsv⟩, h0⟩ ↦ ⟨?_, hsv⟩) ?_
  · refine NativeRustcVm.SameOutside.mono hs fun q hq ↦ .inr (.inl ?_)
    have : InRange (NativeRustcVm.Transcript.off (rdr m0) 16) 8 q := by
      rw [← hx0]; exact hq
    rwa [cur_eq] at this
  · intro m2 hfr2 ⟨hq, h0⟩ hcs
    have hs := hq.2.1
    refine cont m2 hfr2 hcs (fun q hq' ↦ hs q fun h ↦ hq' ?_) ?_
    · have : InRange (NativeRustcVm.Transcript.off (rdr m0) 16) 8 q := by
        rw [← hx0]; exact h
      rwa [cur_eq] at this
    have := hq.1 (bpA m0) B c (by rw [hx0]; exact hR)
    rw [hx1, hx0, rdLe_four] at this
    unfold Read4
    rcases h : rdU32 B c with _ | ⟨v, c'⟩
    · rw [h] at this; exact this
    · rw [h] at this
      obtain ⟨h0, h1, h2⟩ := this
      refine ⟨h0, ?_, h2⟩
      rw [h1]
      exact toNat_toUInt64_of_lt (by have := rdU32_lt h; omega)

variable {k : Nat}

/-- **The epilogue** (`b15`) with `X0` the result. -/
theorem exit15 (hp : Placed code k) (G : Geo m0 B) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.Decode.b15Offset)) (hfr : Frm m0 st.data)
    (hres : match decodeM B with
      | some r => st.data.regs.X0 = 1 ∧ NativeRustcVm.Transcript.DecodedAt st.data.dmem (area m0)
          (streamW r.1) (openingsW r.2)
      | none => st.data.regs.X0 = 0) :
    Eventually (step1 Host.exe) (Res m0 B) st := by
  have hwf := frEnv_wf G.st hfr
  have hm := frEnv_match G.st hfr
  refine exec_at (infix_of b15_in_code (by simp [b15]) hp) run_b15 hwf hpc hm fun s hm' hpc' ↦ ?_
  rw [← after_eq run_b15] at hm'
  obtain ⟨hret, hsv⟩ := Fr.exit hfr hm' hwf (by decide +kernel)
  have hd : s.data.dmem = st.data.dmem := hm'.dmem_eq hwf (by decide)
  have h0 : s.data.regs.X0 = st.data.regs.X0 := Match.reg_eq hm hm' (r := .X0) rfl (by decide)
  refine .done _ ⟨by simp only [PcOk] at hpc'; rw [hpc', hret], ?_, by
    rw [hd]; exact same_res hfr, hsv⟩
  rw [h0, hd]
  exact hres

/-- **`None`** from `b14`. -/
theorem exit14 (hp : Placed code k) (G : Geo m0 B) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.Decode.b14Offset)) (hfr : Frm m0 st.data) (hn : decodeM B = none) :
    Eventually (step1 Host.exe) (Res m0 B) st := by
  have hwf := frEnv_wf G.st hfr
  have hm := frEnv_match G.st hfr
  refine exec_at (infix_of b14_in_code (by simp [b14]) hp) run_b14 hwf hpc hm fun s hm' hpc' ↦ ?_
  have hfr' : Frm m0 s.data := Fr.ofBlock hfr hm hm' hwf rfl rfl rfl
    fun x hx ↦ by
      refine ⟨.reg x, ?_⟩
      simp only [keep, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩
  refine exit15 hp G (hpc'.trans (congrArg Host.addrOf rfl)) hfr' ?_
  rw [hn]
  apply UInt64.toBitVec_inj.mp
  rw [show s.data.regs.X0 = s.data.regs.getXReg .X0 from rfl, hm'.regs .X0 _ rfl]
  rfl

end

end NativeRustcVmArm.Wire.Decode
