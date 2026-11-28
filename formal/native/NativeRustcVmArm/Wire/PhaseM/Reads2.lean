module

public import NativeRustcVmArm.Code.Vm.PhaseM.Names
public import NativeRustcVmArm.Code.Vm.ReaderLe.Names
public import NativeRustcVmArm.Wire.PhaseM.Reads

/-!
# `phase_m`: the count, and the three sizes

`first_run`: the prologue and the query count (`b0`, `b1`, at most 256), to the queries' loop
(`b2`, `b3`) or, with none, past it. `rest_run`: the height, the leaf width (to the frame's byte
56) and the row width (`b7` to `b14`), to the sort's head. `reads_run`: both, with the queries'
loop between.
-/

namespace NativeRustcVmArm.Wire.PhaseM

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt InAny Region)
open NativeRustcVmArm.Vm.PhaseM
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

@[expose] public section

/-- The count's check: the read failed, or the count is past 256. -/
def c1 : SBool := .cmp .eq .W32 (.bin .and .W32 (.reg .X0) (.un .trunc .W32
  (.ite (.not (.cmp .ult .W64 (.reg .X1) (.lit 257))) (.lit 0) (.lit 1)))) (.lit 0)

end

public section

theorem c1_eval [Labels] {env : Sym.Env} :
    c1.eval env = CmpOp.apply .eq .W32 (BinOp.apply .and .W32 (env.regs .X0) (UnOp.apply .trunc .W32
      (if (env.regs .X1).toNat < 257 then 1#64 else 0#64))) 0#64 := by
  have hu : CmpOp.apply .ult .W64 (Sym.eval env (.reg .X1)) (Sym.eval env (.lit 257)) =
      decide ((env.regs .X1).toNat < 257) := by
    simp only [Sym.eval]; rw [ult_apply]; rfl
  show CmpOp.apply .eq .W32 (BinOp.apply .and .W32 (env.regs .X0) (UnOp.apply .trunc .W32
      (if (SBool.not (SBool.cmp .ult .W64 (.reg .X1) (.lit 257))).eval env then 0#64 else 1#64)))
      0#64 = _
  simp only [SBool.eval]
  by_cases hc : (env.regs .X1).toNat < 257 <;> simp [hu, hc]

theorem c1_zero [Labels] {env : Sym.Env} (h : env.regs .X0 = 0) : c1.eval env = true := by
  rw [c1_eval, h]
  split <;> decide

theorem c1_one [Labels] {env : Sym.Env} (h : env.regs .X0 = 1) :
    c1.eval env = decide (257 ≤ (env.regs .X1).toNat) := by
  rw [c1_eval, h]
  by_cases hc : (env.regs .X1).toNat < 257
  · simp only [hc, ↓reduceIte]; rw [decide_eq_false (by omega)]; decide
  · simp only [hc, ↓reduceIte]; rw [decide_eq_true (by omega)]; decide

theorem tbz_zero [Labels] {env : Sym.Env} (h : env.regs .X0 = 0) :
    (SBool.bit .W32 (.reg .X0) 0).not.eval env = true := by
  simp only [SBool.eval, Sym.eval, h]; rfl

theorem tbz_one [Labels] {env : Sym.Env} (h : env.regs .X0 = 1) :
    (SBool.bit .W32 (.reg .X0) 0).not.eval env = false := by
  simp only [SBool.eval, Sym.eval, h]; rfl

theorem lsl3 {x : BitVec 64} (h : 8 * x.toNat < 2 ^ 64) :
    (UnOp.apply (.ubfm 61 60) .W64 x).toNat = 8 * x.toNat := by
  rw [ubfm_lsl3, BitVec.toNat_shiftLeft]
  simp only [Nat.shiftLeft_eq]
  omega

theorem cmp_eq_lit [Labels] {env : Sym.Env} {r : XReg} {n v : Nat} (hn : n < 2 ^ 64)
    (h : (env.regs r).toNat = v) :
    (SBool.cmp .eq .W64 (.reg r) (.lit n)).eval env = decide (v = n) := by
  simp only [SBool.eval, Sym.eval]
  rw [eq_lit _ n hn, h]

theorem x0_bv {m : MachineData} {v : UInt64} (h : m.regs.X0 = v) :
    (m.regs.getXReg .X0).toBitVec = v.toBitVec := by
  rw [show m.regs.getXReg .X0 = m.regs.X0 from rfl, h]

variable {m0 : MachineData} {bp : BitVec 64} {B : List UInt8} {c : Nat}

theorem frame_sub (hst : StackOk m0 1184) {o n : Nat} (hon : o + n ≤ 192) {q : BitVec 64}
    (h : InRange (base m0 192 + BitVec.ofNat 64 o) n q) : InRange (base m0 1184) 1184 q := by
  rw [← Ring.base_add (F := 192) (N := 1184) (by omega) hst.2.1, NativeRustcVm.addr_add_add] at h
  exact NativeRustcVm.InRange.of_sub h (Ring.base_noWrap hst.2.1) (by omega)

/-- A frame word kept by a write elsewhere in the frame. -/
theorem FW.frame (hst : StackOk m0 1184) {d d' : Mem 64} {o' n' : Nat}
    (hs : SameOutside d d' (InRange (base m0 192 + BitVec.ofNat 64 o') n')) {o : Nat} {v : UInt64}
    (hon : o' + n' ≤ 192) (ho : o + 8 ≤ 192) (hd : o + 8 ≤ o' ∨ o' + n' ≤ o) (h : FW m0 d o v) :
    FW m0 d' o v := by
  have hb := Ring.base_toNat (m0 := m0) (F := 192) (by have := hst.2.1; omega)
  have hSP := m0.regs.SP.toNat_lt
  have := hst.2.1
  refine h.keep hs fun i hi hq ↦ ?_
  by_cases hn : n' = 0
  · subst hn; unfold InRange at hq; omega
  rw [Sym.inRange_iff (by rw [NativeRustcVm.toNat_add_ofNat (by rw [hb]; omega), hb]; omega),
    NativeRustcVm.toNat_add_ofNat (by rw [hb]; omega), hb, NativeRustcVm.addr_add_add,
    NativeRustcVm.toNat_add_ofNat (by rw [hb]; omega), hb] at hq
  omega

/-- A frame word kept by a call of `Reader::le`. -/
theorem FW.cur [Labels] (G : Geo m0 bp B) {d d' : Mem 64}
    (hs : SameOutside d d' (InRange (rdr m0 + BitVec.ofNat 64 16) 8)) {o : Nat} {v : UInt64}
    (ho : o + 8 ≤ 192) (h : FW m0 d o v) : FW m0 d' o v := by
  refine h.keep hs fun i hi hq ↦ G.rgeo.not_frame (F := 192) (by omega) (.inl hq) ?_
  have hb := Ring.base_toNat (m0 := m0) (F := 192) (by have := G.sp; omega)
  have hSP := m0.regs.SP.toNat_lt
  have := G.sp
  rw [Sym.inRange_iff (by rw [hb]; omega), hb, NativeRustcVm.addr_add_add,
    NativeRustcVm.toNat_add_ofNat (by rw [hb]; omega), hb]
  omega

/-- Working-area words kept by a write in the frame. -/
theorem keep_frame [Labels] (G : Geo m0 bp B) {d d' : Mem 64} {o' n' : Nat}
    (hs : SameOutside d d' (InRange (base m0 192 + BitVec.ofNat 64 o') n')) (hon : o' + n' ≤ 192)
    {o : Nat} {bs : List UInt8} (ho : o + bs.length ≤ workBytes) (h : BytesAt d (wa m0 o) bs) :
    BytesAt d' (wa m0 o) bs :=
  G.keep_wa (L := []) hs ho h (fun q hq ↦ .inl (frame_sub G.st hon hq)) (by simp)

/-- The reader kept by a write in the frame. -/
theorem reader_fr [Labels] (G : Geo m0 bp B) {d d' : Mem 64} {o' n' : Nat}
    (hs : SameOutside d d' (InRange (base m0 192 + BitVec.ofNat 64 o') n')) (hon : o' + n' ≤ 192)
    {c : Nat} (h : ReaderAt d (rdr m0) bp B c) : ReaderAt d' (rdr m0) bp B c :=
  G.rgeo.reader_frame rfl h (NativeRustcVm.SameOutside.mono hs fun _ hq ↦
    .inl (frame_sub G.st hon hq))

variable [Host] {k : Nat}

/-- **The prologue and the count.** -/
theorem first_run (hp : Placed code k) (G : Geo m0 bp B)
    (hle : Spec (Labels.label NativeRustcVmArm.Vm.ReaderLe.entryLabel) ReaderLePre ReaderLePost)
    (hR0 : ReaderAt m0.dmem (rdr m0) bp B c) :
    Eventually (step1 Host.exe) (fun st ↦ AtNone m0 B c k st ∨
      (∃ count, AtQ m0 bp B c k count 0 st) ∨ ∃ count qs c2, At30 m0 bp B c k count qs c2 st)
      ⟨m0, Host.addrOf (k + NativeRustcVmArm.Vm.PhaseM.b0Offset)⟩ := by
  have hst := G.st
  have hN := hst.2.1
  let env0 := Env.ofMachine m0 [(base m0 192, 192)]
  have hwf0 : env0.WF := Env.wf_of ⟨⟨Ring.frame_mapped hst (by omega),
    Ring.base_noWrap (by omega)⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hm0 : Match env0 entryS m0 := match_ofMachine ⟨rfl, fun _ ↦ base_aligned hst, trivial⟩
    (by simp only [Sym.eval, Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
          Option.getD_some]
        rw [show BitVec.ofInt 64 192 = BitVec.ofNat 64 192 from rfl]
        exact Ring.base_add_eq.symm)
    trivial trivial trivial trivial
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_b0 hwf0 hm0 fun s1 hm1 hpc1 ↦ ?_
  rw [← after_eq run_b0] at hm1
  have hfr1 : Frm m0 s1.data :=
    Fr.ofPrologue hN (by omega) hm1 hwf0 (by decide) (by decide +kernel) (by decide)
      (by decide +kernel) (by simp)
  have hs1 := Match.sameOutside_in hm1 hwf0 (r0 := 0) (o := 0) (n := 192) rfl (by omega)
    (by decide +kernel)
  have hR1 : ReaderAt s1.data.dmem (rdr m0) bp B c := reader_fr G hs1 (by omega) hR0
  have hb1 : Base m0 s1.data := ⟨hfr1, hm1.regs .X19 (.reg .X2) (by decide),
    hm1.regs .X20 (.reg .X1) (by decide), hm1.regs .X22 (.reg .X0) (by decide)⟩
  have hx0 : s1.data.regs.X0.toBitVec = rdr m0 := hm1.regs .X0 (.reg .X0) (by decide)
  have hx1 : s1.data.regs.X1.toNat = 4 := by
    show (s1.data.regs.getXReg .X1).toBitVec.toNat = 4
    rw [hm1.regs .X1 (.lit 4) (by decide)]; rfl
  refine le4_call hle G hfr1 hR1 hx0 hx1 hpc1 fun m2 hfr2 hcs hs2 hrd2 ↦ ?_
  have hb2 := hb1.call hfr2 hcs
  -- `b1`
  refine blk hp b1_in_code (by simp [b1]) run_b1 rfl rfl hst hfr2 rfl fun s3 hfr3 hd3 hm3 hpc3 ↦ ?_
  have hm2 := frEnv_match hst hfr2
  have r3 := regs_of hm2 hm3 (rs := [.X0, .X1, .X19, .X20, .X21, .X22]) (by decide)
  have hb3 : Base m0 s3.data := hb2.of_regs hfr3 fun x hx ↦ r3 x (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp)
  simp only [PcOk] at hpc3
  rcases read4_cases hrd2 with ⟨hn, h0⟩ | ⟨count, hv, h0, hx1', hrd3⟩
  · have hc := c1_zero (env := frEnv m0 m2) (by simp only [Env.ofMachine_regs]; rw [x0_bv h0]; rfl)
    unfold c1 at hc
    rw [hc] at hpc3
    refine .done _ (.inl ⟨hpc3.trans (hp.label (j := NativeRustcVmArm.Vm.PhaseM.b18Offset) NativeRustcVmArm.Vm.PhaseM.label_12_at), hb3, ?_⟩)
    rw [phaseM_eq, hn]
  have hc := c1_one (env := frEnv m0 m2) (by simp only [Env.ofMachine_regs]; rw [x0_bv h0]; rfl)
  unfold c1 at hc
  rw [hc] at hpc3
  have hx1b : (m2.regs.getXReg .X1).toBitVec.toNat = count := hx1'
  simp only [Env.ofMachine_regs, hx1b] at hpc3
  by_cases hbig : 257 ≤ count
  · simp only [hbig, decide_true, ↓reduceIte] at hpc3
    refine .done _ (.inl ⟨hpc3.trans (hp.label (j := NativeRustcVmArm.Vm.PhaseM.b18Offset) NativeRustcVmArm.Vm.PhaseM.label_12_at), hb3, ?_⟩)
    rw [phaseM_eq, hv]
    simp only [show wireMaxQueries < count by unfold wireMaxQueries; omega, ↓reduceIte]
  simp only [hbig, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc3
  -- `b2`
  refine blk hp b2_in_code (by simp [b2]) run_b2 rfl rfl hst hfr3 hpc3
    fun s4 hfr4 hd4 hm4 hpc4 ↦ ?_
  have hm3' := frEnv_match hst hfr3
  have r4 := regs_of hm3' hm4 (rs := [.X1, .X19, .X20, .X22]) (by decide)
  have hb4 : Base m0 s4.data := hb3.of_regs hfr4 fun x hx ↦ r4 x (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp)
  have x1_3 : (s3.data.regs.getXReg .X1).toBitVec.toNat = count := by
    rw [r3 .X1 (by simp)]; exact hx1b
  have x21 : (s4.data.regs.getXReg .X21).toNat = count := by
    show (s4.data.regs.getXReg .X21).toBitVec.toNat = _
    rw [hm4.regs .X21 _ rfl]; exact x1_3
  have x27 : (s4.data.regs.getXReg .X27).toNat = 8 * count := by
    show (s4.data.regs.getXReg .X27).toBitVec.toNat = _
    rw [hm4.regs .X27 _ rfl]
    simp only [Sym.eval, Env.ofMachine_regs]
    rw [lsl3 (by rw [x1_3]; omega), x1_3]
  have hrd4 : ReaderAt s4.data.dmem (rdr m0) bp B (c + 4) := by rw [hd4, hd3]; exact hrd3
  have hcnt : count ≤ 256 := by omega
  simp only [PcOk, cmp_eq_lit (env := frEnv m0 s3.data) (r := .X1) (n := 0) (by decide) x1_3]
    at hpc4
  by_cases hz : count = 0
  · simp only [hz, decide_true, ↓reduceIte] at hpc4
    subst hz
    refine .done _ (.inr (.inr ⟨0, [], c + 4, hpc4.trans (hp.label (j := NativeRustcVmArm.Vm.PhaseM.b7Offset) NativeRustcVmArm.Vm.PhaseM.label_5_at), hb4, x21, x27,
      hv, hcnt, rfl, NativeRustcVm.wordsAt_nil _ _, hrd4⟩))
  simp only [hz, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc4
  -- `b3`
  refine blk hp b3_in_code (by simp [b3]) run_b3 rfl rfl hst hfr4 hpc4
    fun s5 hfr5 hd5 hm5 hpc5 ↦ ?_
  have hm4' := frEnv_match hst hfr4
  have r5 := regs_of hm4' hm5 (rs := [.X19, .X20, .X21, .X22, .X27]) (by decide)
  refine .done _ (.inr (.inl ⟨count, ⟨hpc5, hb4.of_regs hfr5 fun x hx ↦ r5 x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> simp),
    by rw [r5 .X21 (by simp)]; exact x21, by rw [r5 .X27 (by simp)]; exact x27, ?_, ?_, hv, hcnt,
    by omega, [], rfl, NativeRustcVm.wordsAt_nil _ _, by rw [hd5]; simpa using hrd4⟩⟩))
  · show (s5.data.regs.getXReg .X23).toBitVec.toNat = _
    rw [hm5.regs .X23 _ rfl]
    simp only [Sym.eval, Env.ofMachine_regs]
    exact x27
  · rw [hm5.regs .X24 _ rfl]
    simp only [Sym.eval, Env.ofMachine_regs]
    rw [hb4.x19]
    simp

/-- A call of `Reader::le` for four bytes, from a block `b` (`frS`, no writes) ending in it with
X0 the reader and X1 four. -/
theorem call4 (hp : Placed code k) (G : Geo m0 bp B)
    (hle : Spec (Labels.label NativeRustcVmArm.Vm.ReaderLe.entryLabel) ReaderLePre ReaderLePost) {b : List Directive}
    {j : Nat} (hb : b.IsInfixAt code j) (hne : b ≠ []) {S' : SState}
    (hx : exec b frS = some (S', .call NativeRustcVmArm.Vm.ReaderLe.entryLabel)) (hmem : S'.mem = []) (hsp : S'.sp = .ptr 0 0)
    (h0 : S'.reg .X0 = some (.reg .X22)) (h1 : S'.reg .X1 = some (.lit 4))
    (h19 : S'.reg .X19 = some (.reg .X19)) (h20 : S'.reg .X20 = some (.reg .X20))
    (h22 : S'.reg .X22 = some (.reg .X22))
    {c' : Nat} {st : MachineState} {R : MachineState → Prop} (hb0 : Base m0 st.data)
    (hpc : st.pc = Host.addrOf (k + j)) (hR : ReaderAt st.data.dmem (rdr m0) bp B c')
    (cont : ∀ m2 : MachineData, Base m0 m2 →
      (∀ x, calleeSaved x = true → ∀ v, S'.reg x = some v →
        (m2.regs.getXReg x).toBitVec = v.eval (frEnv m0 st.data)) →
      SameOutside st.data.dmem m2.dmem (InRange (rdr m0 + BitVec.ofNat 64 16) 8) →
      Read4 (rdr m0) bp B c' m2 →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (k + j + b.length)⟩) :
    Eventually (step1 Host.exe) R st := by
  refine blk hp hb hne hx hmem hsp G.st hb0.fr hpc fun s1 hfr1 hd1 hm1 hpc1 ↦ ?_
  have hm := frEnv_match G.st hb0.fr
  have hb1 : Base m0 s1.data := hb0.of_regs hfr1 fun x hx ↦ by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact Match.reg_eq hm hm1 rfl h19
    · exact Match.reg_eq hm hm1 rfl h20
    · exact Match.reg_eq hm hm1 rfl h22
  have hx0 : s1.data.regs.X0.toBitVec = rdr m0 := (hm1.regs .X0 _ h0).trans hb0.x22
  have hx1 : s1.data.regs.X1.toNat = 4 := by
    show (s1.data.regs.getXReg .X1).toBitVec.toNat = 4
    rw [hm1.regs .X1 _ h1]; rfl
  refine le4_call hle G hb1.fr (by rw [hd1]; exact hR) hx0 hx1 hpc1 fun m2 hfr2 hcs hs2 hrd2 ↦ ?_
  refine cont m2 (hb1.call hfr2 hcs) (fun x hx v hv ↦ by rw [hcs x hx]; exact hm1.regs x v hv)
    (by rw [← hd1]; exact hs2) hrd2

/-- The flag test `tbz w0, #0` after a read (`b`, `frS`, nothing changed). -/
theorem tbz_step (hp : Placed code k) (G : Geo m0 bp B) {b : List Directive} {j : Nat}
    (hb : b.IsInfixAt code j) (hne : b ≠ [])
    (hx : exec b frS = some (frS, .cond (SBool.bit .W32 (.reg .X0) 0).not NativeRustcVmArm.Vm.PhaseM.label_12))
    {st : MachineState} {R : MachineState → Prop} (hb0 : Base m0 st.data)
    (hpc : st.pc = Host.addrOf (k + j)) {v : UInt64} (h0 : st.data.regs.X0 = v)
    (hv : v = 0 ∨ v = 1)
    (cont : ∀ st', Base m0 st'.data → st'.data.dmem = st.data.dmem →
      (∀ x, st'.data.regs.getXReg x = st.data.regs.getXReg x) →
      st'.pc = (if v = 0 then Host.addrOf (k + NativeRustcVmArm.Vm.PhaseM.b18Offset) else Host.addrOf (k + j + b.length)) →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  refine blk hp hb hne hx rfl rfl G.st hb0.fr hpc fun s1 hfr1 hd1 hm1 hpc1 ↦ ?_
  have hm := frEnv_match G.st hb0.fr
  have r1 : ∀ x, s1.data.regs.getXReg x = st.data.regs.getXReg x := fun x ↦
    Match.reg_eq (v := .reg x) hm hm1 (by cases x <;> rfl) (by cases x <;> rfl)
  refine cont s1 (hb0.of_regs hfr1 fun x _ ↦ r1 x) hd1 r1 ?_
  simp only [PcOk] at hpc1
  rw [hpc1]
  rcases hv with rfl | rfl
  · rw [tbz_zero (by simp only [Env.ofMachine_regs]; rw [x0_bv h0]; rfl)]
    simp only [↓reduceIte]
    exact hp.label (j := NativeRustcVmArm.Vm.PhaseM.b18Offset) NativeRustcVmArm.Vm.PhaseM.label_12_at
  · rw [tbz_one (by simp only [Env.ofMachine_regs]; rw [x0_bv h0]; rfl)]
    simp

/-- **The three sizes**: the height, the leaf width, the row width. -/
theorem rest_run (hp : Placed code k) (G : Geo m0 bp B)
    (hle : Spec (Labels.label NativeRustcVmArm.Vm.ReaderLe.entryLabel) ReaderLePre ReaderLePost) {count : Nat}
    {qs : List Nat} {c2 : Nat} {st : MachineState} (h : At30 m0 bp B c k count qs c2 st) :
    Eventually (step1 Host.exe) (fun st' ↦ AtNone m0 B c k st' ∨
      ∃ height lw rw c5, SortSt m0 bp B c k count qs height lw rw c5 0 st') st := by
  obtain ⟨hpc, hb, x21, x27, h1, hcnt, hqs, hqW, hrd⟩ := h
  have hst := G.st
  have hpm := pm_eq_of h1 hcnt hqs
  obtain ⟨hql, hc2⟩ := rdU32s_len B count (c + 4) hqs
  have hqlt := NativeRustcVm.Wire.rdU32s_lt B count (c + 4) hqs
  have hqb : 8 * qs.length ≤ workBytes := by rw [hql, workBytes_eq]; omega
  -- the height
  refine call4 hp G hle b7_in_code (by simp [b7]) run_b7 rfl rfl rfl rfl rfl rfl rfl hb hpc hrd
    fun m2 hb2 hk2 hs2 hrd2 ↦ ?_
  have e21 : (m2.regs.getXReg .X21).toBitVec = (st.data.regs.getXReg .X21).toBitVec :=
    hk2 .X21 rfl _ rfl
  have e27 : (m2.regs.getXReg .X27).toBitVec = (st.data.regs.getXReg .X27).toBitVec :=
    hk2 .X27 rfl _ rfl
  have hqW2 : WordsAt m2.dmem (wa m0 0) (qs.map Nat.toUInt64) :=
    G.keep_wa (L := []) hs2 (by rw [NativeRustcVm.length_wordsBytes, List.length_map]; omega)
      hqW (fun q hq ↦ .inr (.inl hq)) (by simp)
  rcases read4_cases hrd2 with ⟨hn, h0⟩ | ⟨height, hv3, h0, hx1, hrd3⟩
  · refine tbz_step hp G b8_in_code (by simp [b8]) (by rw [run_b8]; rfl) hb2 rfl h0 (.inl rfl)
      fun s hbs _ _ hpcs ↦ .done _ (.inl ⟨by simpa using hpcs, hbs, by rw [hpm, hn]⟩)
  refine tbz_step hp G b8_in_code (by simp [b8]) (by rw [run_b8]; rfl) hb2 rfl h0 (.inr rfl)
    fun s3 hb3 hd3 hr3 hpc3 ↦ ?_
  simp only [show (1 : UInt64) ≠ 0 by decide, ↓reduceIte] at hpc3
  -- the leaf width
  refine call4 hp G hle b9_in_code (by simp [b9]) run_b9 rfl rfl rfl rfl rfl rfl rfl hb3 hpc3
    (by rw [hd3]; exact hrd3) fun m4 hb4 hk4 hs4 hrd4 ↦ ?_
  have e24 : (m4.regs.getXReg .X24).toNat = height := by
    show (m4.regs.getXReg .X24).toBitVec.toNat = _
    rw [hk4 .X24 rfl _ rfl]
    show (s3.data.regs.getXReg .X1).toBitVec.toNat = _
    rw [hr3]; exact hx1
  have hqW4 : WordsAt m4.dmem (wa m0 0) (qs.map Nat.toUInt64) :=
    G.keep_wa (L := []) hs4 (by rw [NativeRustcVm.length_wordsBytes, List.length_map]; omega)
      (by rw [hd3]; exact hqW2) (fun q hq ↦ .inr (.inl hq)) (by simp)
  -- `b10`: the check, the leaf width to the frame
  refine blkW hp b10_in_code (by simp [b10]) run_b10 (by decide) rfl hst hb4.fr rfl
    fun s5 hfr5 hs5 hm5 hpc5 ↦ ?_
  have hm4 := frEnv_match hst hb4.fr
  have r5 : ∀ x ∈ [XReg.X0, .X19, .X20, .X21, .X22, .X24, .X27],
      s5.data.regs.getXReg x = m4.regs.getXReg x :=
    regs_of hm4 hm5 (by decide)
  have hb5 : Base m0 s5.data := hb4.of_regs hfr5 fun x hx ↦ r5 x (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
    rcases hx with rfl | rfl | rfl <;> simp)
  rcases read4_cases hrd4 with ⟨hn, h0⟩ | ⟨lw, hv4, h0, hx1', hrd5⟩
  · have hc : (SBool.cmp .eq .W64 (.reg .X0) (.lit 1)).not.eval (frEnv m0 m4) = true := by
      rw [SBool.eval, cmp_eq_lit (v := 0) (by decide)
        (by simp only [Env.ofMachine_regs]; rw [x0_bv h0]; rfl)]
      rfl
    simp only [PcOk, hc, ↓reduceIte] at hpc5
    refine .done _ (.inl ⟨hpc5.trans (hp.label (j := NativeRustcVmArm.Vm.PhaseM.b18Offset) NativeRustcVmArm.Vm.PhaseM.label_12_at), hb5, ?_⟩)
    rw [hpm, hv3]
    simp only [hn]
  have hc : (SBool.cmp .eq .W64 (.reg .X0) (.lit 1)).not.eval (frEnv m0 m4) = false := by
    rw [SBool.eval, cmp_eq_lit (v := 1) (by decide)
      (by simp only [Env.ofMachine_regs]; rw [x0_bv h0]; rfl)]
    rfl
  simp only [PcOk, hc, Bool.false_eq_true, ↓reduceIte] at hpc5
  have f56 : FW m0 s5.data.dmem 56 lw.toUInt64 := by
    have := hm5.bytesAt_write (r := 0) (o := 56) (n := 8) (b := base m0 192) (sz := 192) rfl
      (by omega) (v := .reg .X1) (by decide)
    have hw := wordAt_reg this
    simp only [Sym.eval, Env.ofMachine_regs] at hw
    rwa [ofBitVec_eq (show (m4.regs.getXReg .X1).toBitVec.toNat = lw from hx1')] at hw
  have hd5 : s5.data.dmem = s5.data.dmem := rfl
  have hqW5 : WordsAt s5.data.dmem (wa m0 0) (qs.map Nat.toUInt64) :=
    keep_frame G hs5 (by omega)
      (by rw [NativeRustcVm.length_wordsBytes, List.length_map]; omega) hqW4
  have hrd5' : ReaderAt s5.data.dmem (rdr m0) bp B (c2 + 4 + 4) := reader_fr G hs5 (by omega) hrd5
  -- the row width
  refine call4 hp G hle b11_in_code (by simp [b11]) run_b11 rfl rfl rfl rfl rfl rfl rfl hb5 hpc5
    hrd5' fun m6 hb6 hk6 hs6 hrd6 ↦ ?_
  have f56' : FW m0 m6.dmem 56 lw.toUInt64 := FW.cur G hs6 (by omega) f56
  have hqW6 : WordsAt m6.dmem (wa m0 0) (qs.map Nat.toUInt64) :=
    G.keep_wa (L := []) hs6 (by rw [NativeRustcVm.length_wordsBytes, List.length_map]; omega)
      hqW5 (fun q hq ↦ .inr (.inl hq)) (by simp)
  have e21' : (m6.regs.getXReg .X21).toNat = count := by
    show (m6.regs.getXReg .X21).toBitVec.toNat = _
    rw [hk6 .X21 rfl _ rfl]
    show (s5.data.regs.getXReg .X21).toBitVec.toNat = _
    rw [r5 .X21 (by simp), hk4 .X21 rfl _ rfl]
    show (s3.data.regs.getXReg .X21).toBitVec.toNat = _
    rw [hr3, e21]; exact x21
  have e27' : (m6.regs.getXReg .X27).toNat = 8 * count := by
    show (m6.regs.getXReg .X27).toBitVec.toNat = _
    rw [hk6 .X27 rfl _ rfl]
    show (s5.data.regs.getXReg .X27).toBitVec.toNat = _
    rw [r5 .X27 (by simp), hk4 .X27 rfl _ rfl]
    show (s3.data.regs.getXReg .X27).toBitVec.toNat = _
    rw [hr3, e27]; exact x27
  have e24' : (m6.regs.getXReg .X24).toNat = height := by
    show (m6.regs.getXReg .X24).toBitVec.toNat = _
    rw [hk6 .X24 rfl _ rfl]
    show (s5.data.regs.getXReg .X24).toBitVec.toNat = _
    rw [r5 .X24 (by simp)]; exact e24
  -- `b12`: no query
  refine blk hp b12_in_code (by simp [b12]) run_b12 rfl rfl hst hb6.fr rfl
    fun s7 hfr7 hd7 hm7 hpc7 ↦ ?_
  have hm6 := frEnv_match hst hb6.fr
  have r7 : ∀ x, s7.data.regs.getXReg x = m6.regs.getXReg x := fun x ↦
    Match.reg_eq (v := .reg x) hm6 hm7 (by cases x <;> rfl) (by cases x <;> rfl)
  have hb7 : Base m0 s7.data := hb6.of_regs hfr7 fun x _ ↦ r7 x
  simp only [PcOk, cmp_eq_lit (env := frEnv m0 m6) (r := .X21) (n := 0) (by decide) e21'] at hpc7
  by_cases hz : count = 0
  · simp only [hz, decide_true, ↓reduceIte] at hpc7
    refine .done _ (.inl ⟨hpc7.trans (hp.label (j := NativeRustcVmArm.Vm.PhaseM.b18Offset) NativeRustcVmArm.Vm.PhaseM.label_12_at), hb7, ?_⟩)
    have : qs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    simp only [hpm, hv3, hv4]
    split
    · rfl
    · exact tail_nil _ _ _ _ _
  simp only [hz, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc7
  -- `b13`: the read's flag
  have hx07 : s7.data.regs.X0 = m6.regs.X0 := r7 .X0
  rcases read4_cases hrd6 with ⟨hn, h0⟩ | ⟨rw, hv5, h0, hx1'', hrd8⟩
  · refine tbz_step hp G b13_in_code (by simp [b13]) (by rw [run_b13]; rfl) hb7 hpc7
      (hx07.trans h0) (.inl rfl) fun s hbs _ _ hpcs ↦ .done _ (.inl ⟨by simpa using hpcs, hbs, ?_⟩)
    simp only [hpm, hv3, hv4, hn]
  refine tbz_step hp G b13_in_code (by simp [b13]) (by rw [run_b13]; rfl) hb7 hpc7
    (hx07.trans h0) (.inr rfl) fun s8 hb8 hd8 hr8 hpc8 ↦ ?_
  simp only [show (1 : UInt64) ≠ 0 by decide, ↓reduceIte] at hpc8
  -- `b14`
  refine blkW hp b14_in_code (by simp [b14]) run_b14 (by decide) rfl hst hb8.fr hpc8
    fun s9 hfr9 hs9 hm9 hpc9 ↦ ?_
  have hm8 := frEnv_match hst hb8.fr
  have r9 : ∀ x ∈ [XReg.X19, .X20, .X21, .X22, .X24, .X27], s9.data.regs.getXReg x =
      s8.data.regs.getXReg x := regs_of hm8 hm9 (by decide)
  have hb9 : Base m0 s9.data := hb8.of_regs hfr9 fun x hx ↦ r9 x (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
    rcases hx with rfl | rfl | rfl <;> simp)
  have hreg : ∀ x, (s8.data.regs.getXReg x) = m6.regs.getXReg x := fun x ↦ (hr8 x).trans (r7 x)
  have hd9 : s8.data.dmem = m6.dmem := hd8.trans hd7
  refine .done _ (.inr ⟨height, lw, rw, c2 + 4 + 4 + 4,
    ⟨by simp only [PcOk] at hpc9; exact hpc9, hb9, ?_, hql, by omega, hcnt, hqlt, rdU32_lt hv3,
      rdU32_lt hv4, rdU32_lt hv5, ?_, ?_, ?_, ?_, ?_, ?_, by omega, ?_, ?_, ?_, ?_, ?_⟩⟩)
  · simp only [hpm, hv3, hv4, hv5]
  · rw [r9 .X21 (by simp), hreg]; exact e21'
  · rw [r9 .X24 (by simp), hreg]; exact e24'
  · rw [r9 .X27 (by simp), hreg]; exact e27'
  · show (s9.data.regs.getXReg .X28).toBitVec.toNat = _
    rw [hm9.regs .X28 _ rfl]
    show (s8.data.regs.getXReg .X1).toBitVec.toNat = _
    rw [hreg]; exact hx1''
  · show (s9.data.regs.getXReg .X23).toBitVec.toNat = _
    rw [hm9.regs .X23 _ rfl]; rfl
  · show (s9.data.regs.getXReg .X26).toBitVec.toNat = _
    rw [hm9.regs .X26 _ rfl]; rfl
  · exact FW.frame hst (Match.sameOutside_in hm9 (frEnv_wf hst hb8.fr) (r0 := 0) (o := 48)
      (n := 8) rfl (by omega) (by decide)) (by omega) (by omega) (.inr (by omega))
      (show FW m0 s8.data.dmem 56 _ by rw [hd9]; exact f56')
  · have := hm9.bytesAt_write (r := 0) (o := 48) (n := 8) (b := base m0 192) (sz := 192) rfl
      (by omega) (v := .bin .add .W64 (.reg .X19) (.lit 2048)) (by decide)
    have hw := wordAt_reg this
    simp only [Sym.eval, Env.ofMachine_regs] at hw
    rw [hb8.x19, add_lit] at hw
    exact hw
  · exact keep_frame G hs9 (by omega)
      (by rw [NativeRustcVm.length_wordsBytes, List.length_map]; omega)
      (by rw [hd9]; exact hqW6)
  · exact NativeRustcVm.wordsAt_nil _ _
  · exact reader_fr G hs9 (by omega) (by rw [hd9]; exact hrd8)

end

end NativeRustcVmArm.Wire.PhaseM
