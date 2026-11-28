module

public import NativeRustcVmArm.Code.Vm.ReaderWords.Names
public import NativeRustcVmArm.Wire.RdRows.Call

/-!
# `rd_rows`' rows of `rw > 0` words

`Reader::words` reads row `i` after its zeros (`b11`); `None` (`b12`, `b1`, `none_spec`), or the
row's first word checked and the next leaf (`b13`): the loop's head again or the return (`b14`):
`callA_step`; the loop over the leaves (`loopA`).
-/

namespace NativeRustcVmArm.Wire.RdRows

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt InAny Region)
open NativeRustcVmArm.Vm.RdRows
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

public section

variable [Host] {k : Nat} {m0 : MachineData} {bp : BitVec 64} {B : List UInt8} {c : Nat}

/-- **`None`** (`b1`, then the return): a row could not be read. -/
theorem none_spec (hp : Placed code k) (G : Geo m0 bp B) (hR : ReaderAt m0.dmem (rdr m0) bp B c)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.RdRows.b1Offset)) (hfr : Frm m0 st.data)
    (hnone : rdRows B (rw m0) (nr m0) c = none) : Eventually (step1 Host.exe) (Post m0) st := by
  have hst := G.g.st
  have hwf := frEnv_wf hst hfr
  have hm := frEnv_match hst hfr
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) run_b1 hwf hpc hm fun s1 hm1 hpc1 ↦ ?_
  have hfr1 : Frm m0 s1.data := Fr.ofBlock hfr hm hm1 hwf rfl rfl rfl
    fun x hx ↦ absurd hx (by simp)
  simp only [PcOk] at hpc1
  refine ret_spec hp G hR (hpc1.trans (congrArg Host.addrOf rfl)) hfr1 ?_
  rw [hnone]
  show (s1.data.regs.getXReg .X23).toBitVec.toNat = 2
  rw [hm1.regs .X23 _ rfl]
  rfl

omit [Host] in
theorem saved_regs : ∀ r ∈ (.X26 :: regsA), calleeSaved r = true := by decide

/-- **Row `i`**, read after its zeros (`b11` to `b14`). -/
theorem callA_step (hp : Placed code k) (G : Geo m0 bp B) (hR : ReaderAt m0.dmem (rdr m0) bp B c)
    (hw : Spec (Labels.label NativeRustcVmArm.Vm.ReaderWords.entryLabel) ReaderWordsPre ReaderWordsPost) {i : Nat}
    {rows : List (List K)} {ci : Nat} {st : MachineState} (hI : CallA k m0 bp B c i rows ci st) :
    Eventually (step1 Host.exe) (fun st' ↦ Post m0 st' ∨
      ∃ rows' ci', HeadA k m0 bp B c (i + 1) rows' ci' st') st := by
  have hst := G.g.st
  have hi := hI.z.reg.lt
  have hrw := hI.z.reg.rw0
  have hlw := G.lw64
  have hrl := G.rwlw
  have hzc : zc m0 = lw m0 - rw m0 := rfl
  have ho : 8 * zc m0 + 8 * rw m0 ≤ 512 := by omega
  have hwf := frEnv_wf hst hI.z.reg.fr
  have hm := frEnv_match hst hI.z.reg.fr
  refine exec_at (infix_of b11_in_code (by simp [b11]) hp) run_b11 hwf hI.pc hm fun s1 hm1 hpc1 ↦ ?_
  have hd1 : s1.data.dmem = st.data.dmem := hm1.dmem_eq hwf rfl
  have hfr1 : Frm m0 s1.data := Fr.ofBlock hI.z.reg.fr hm hm1 hwf rfl rfl rfl
    fun x hx ↦ absurd hx (by simp)
  have hr1 := regs_keep hm hm1 (rs := .X26 :: regsA) (by decide)
  have hx0 : s1.data.regs.X0.toBitVec = rdr m0 := by
    rw [show s1.data.regs.X0 = s1.data.regs.getXReg .X0 from rfl, hm1.regs .X0 _ rfl]
    exact hI.z.reg.x21
  have hx1 : s1.data.regs.X1.toBitVec = leaf m0 i + BitVec.ofNat 64 (8 * zc m0) := by
    rw [show s1.data.regs.X1 = s1.data.regs.getXReg .X1 from rfl, hm1.regs .X1 _ rfl]
    simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
    rw [hI.z.reg.x19]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [UInt64.toNat_toBitVec, hI.z.reg.x28, BitVec.toNat_ofNat]
    omega
  have hx2 : s1.data.regs.X2 = m0.regs.X3 := by
    apply UInt64.toBitVec_inj.mp
    rw [show s1.data.regs.X2 = s1.data.regs.getXReg .X2 from rfl, hm1.regs .X2 _ rfl]
    simp only [Sym.eval, Env.ofMachine_regs]
    rw [hI.z.reg.x22]
  have hP := G.words_pre hi ho hfr1 hx0 hx1 (by rw [hx2]) (by rw [hd1]; exact hI.z.kept.hrd)
  refine Fr.leaf (N' := readerWordsStack) hfr1 hst.2.1 (by decide) (by simp) (by decide)
    (fun q hq ↦ G.g.not_frame (by omega) hq)
    (Spec.carry hw fun m ↦ m.regs.X0.toBitVec = rdr m0 ∧
      m.regs.X1.toBitVec = leaf m0 i + BitVec.ofNat 64 (8 * zc m0) ∧ m.regs.X2 = m0.regs.X3)
    (fun m m' ⟨⟨_, hs, hsv⟩, h0, h1, h2⟩ ↦ ⟨?_, hsv⟩) hpc1 ⟨hP, hx0, hx1, hx2⟩ ?_
  · refine NativeRustcVm.SameOutside.mono hs fun q ⟨r, hr, h⟩ ↦ ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · refine .inr (.inr ?_)
      have h' : InRange m.regs.X1.toBitVec (8 * m.regs.X2.toNat) q := h
      rw [h1, h2] at h'
      exact (G.chunk_apart hi ho (by omega) h').1
    · exact .inr (.inl (by have h' : InRange (m.regs.X0.toBitVec + 16#64) 8 q := h; rwa [h0] at h'))
    · exact .inl h
  intro m2 hfr2 ⟨hpost, _⟩ hcs
  obtain ⟨hres, hs2, -⟩ := hpost
  simp only [hx0, hx1, hx2] at hres
  have hres' := hres bp B ci (by rw [hd1]; exact hI.z.kept.hrd)
  have hs2' : SameOutside s1.data.dmem m2.dmem (InAny [⟨leaf m0 i + BitVec.ofNat 64 (8 * zc m0),
      8 * rw m0⟩, curRegion (rdr m0), stackR s1.data readerWordsStack]) := by
    have := hs2
    simp only [hx0, hx1, hx2] at this
    exact this
  have hsame := G.call_same hfr1 hs2'
  have h2r : ∀ r ∈ (.X26 :: regsA), m2.regs.getXReg r = st.data.regs.getXReg r :=
    fun r hr ↦ (hcs r (saved_regs r hr)).trans (hr1 r hr)
  -- `b12`: the read's outcome
  have hwf2 := frEnv_wf hst hfr2
  have hm2 := frEnv_match hst hfr2
  refine exec_at (infix_of b12_in_code (by simp [b12]) hp) run_b12 hwf2
    (by rw [Nat.add_assoc, b11_next]) hm2 fun s2 hm2' hpc2 ↦ ?_
  have hd2 : s2.data.dmem = m2.dmem := hm2'.dmem_eq hwf2 rfl
  have hfr3 : Frm m0 s2.data := Fr.ofBlock hfr2 hm2 hm2' hwf2 rfl rfl rfl
    fun x hx ↦ absurd hx (by simp)
  have h3r : ∀ r ∈ (.X26 :: regsA), s2.data.regs.getXReg r = st.data.regs.getXReg r :=
    fun r hr ↦ (regs_keep hm2 hm2' (rs := .X26 :: regsA) (by decide) r hr).trans (h2r r hr)
  cases hrd : rdWords B (rw m0) ci with
  | none =>
    rw [hrd] at hres'
    have hc : (SBool.cmp .eq .W32 (.reg .X0) (.lit 0)).eval (frEnv m0 m2) = true := by
      simp only [SBool.eval, Sym.eval, CmpOp.apply, Env.ofMachine_regs,
        show m2.regs.getXReg .X0 = m2.regs.X0 from rfl, hres']
      decide
    simp only [PcOk, hc, ↓reduceIte, hp.label (j := NativeRustcVmArm.Vm.RdRows.b1Offset) NativeRustcVmArm.Vm.RdRows.label_1_at] at hpc2
    exact Eventually.mono (none_spec hp G hR hpc2 hfr3 (rdRows_none hI.z.kept.hrows hrd hi))
      fun _ h ↦ .inl h
  | some p =>
    obtain ⟨ws, c'⟩ := p
    rw [hrd] at hres'
    obtain ⟨h0', hws, hR2⟩ := hres'
    have hc : (SBool.cmp .eq .W32 (.reg .X0) (.lit 0)).eval (frEnv m0 m2) = false := by
      simp only [SBool.eval, Sym.eval, CmpOp.apply, Env.ofMachine_regs,
        show m2.regs.getXReg .X0 = m2.regs.X0 from rfl, h0']
      decide
    simp only [PcOk, hc, Bool.false_eq_true, ↓reduceIte, NativeRustcVmArm.Vm.RdRows.b12_length, NativeRustcVmArm.Vm.RdRows.b12Length] at hpc2
    have hwl := rdWords_length hrd
    obtain ⟨hrl', hrw'⟩ := rdRows_length (B := B) _ _ hI.z.kept.hrows
    -- the leaves, the reader, the frame's word after the call
    have hlvs : LeavesAt s2.data.dmem (lv m0) ((rows ++ [ws]).map fun x ↦ paddedLeaf x (lw m0)) := by
      rw [List.map_append, List.map_singleton, hd2]
      refine leaves_snoc (G.call_leaves hi ho hsame (by simpa using hrl') (fun x hx ↦ ?_)
        (by rw [hd1]; exact hI.z.kept.hlvs)) ?_
      · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
        simp only [paddedLeaf, List.length_append, List.length_replicate, hrw' y hy]
        omega
      · rw [map_lane_paddedLeaf, hwl, List.length_map, hrl', NativeRustcVm.wordsAt_append_iff,
          List.length_replicate]
        exact ⟨G.call_zeros hi ho (le_refl _) hsame (by rw [hd1]; exact hI.z.zs), hws⟩
    have hq2 : 0 < zc m0 →
        WordAt s2.data.dmem (base m0 112 + BitVec.ofNat 64 8) (q4 (zc m0)).toUInt64 := fun h ↦ by
      rw [hd2]
      exact G.call_frame hi ho (by omega) hsame (by omega) (by rw [hd1]; exact hI.z.reg.q h)
    have hR3 : ReaderAt s2.data.dmem (rdr m0) bp B c' := by rw [hd2]; exact hR2
    -- `b13`: the row's first word, the next leaf
    have hw0 : WordAt s2.data.dmem (leaf m0 i + BitVec.ofNat 64 (8 * zc m0)) (ws[0]'(by omega)).lane := by
      have := hws.getElem (i := 0) (by simp; omega)
      rw [Nat.mul_zero, NativeRustcVm.addr_add_zero, List.getElem_map] at this
      rw [hd2]; exact this
    have hwf3 := G.chunk_wf hi (o := 8 * zc m0) (sz := 8) (by omega) (by omega) hfr3
    have hm3 : Match (chEnv m0 s2.data (leaf m0 i + BitVec.ofNat 64 (8 * zc m0)) 8) rowS s2.data :=
      chunk_match G hfr3 rfl (by
        show (s2.data.regs.getXReg .X26).toBitVec = _ + BitVec.ofInt 64 0
        rw [h3r .X26 (by simp), hI.z.x26, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero])
    refine exec_at (infix_of b13_in_code (by simp [b13]) hp) run_b13 hwf3 hpc2 hm3
      fun s3 hm3' hpc3 ↦ ?_
    have hd3 : s3.data.dmem = s2.data.dmem := hm3'.dmem_eq hwf3 rfl
    have hfr4 : Frm m0 s3.data := Fr.ofBlock hfr3 hm3 hm3' hwf3 rfl rfl rfl
      fun x hx ↦ absurd hx (by simp)
    have h4r := regs_keep hm3 hm3' (rs := [.X20, .X21, .X22, .X24, .X25, .X28, .X29]) (by decide)
    have hld : (chEnv m0 s2.data (leaf m0 i + BitVec.ofNat 64 (8 * zc m0)) 8).load 1 0 8 =
        (ws[0]'(by omega)).lane.toBitVec :=
      load_word (by rw [Env.base_ofMachine _ _ _ (b := leaf m0 i + BitVec.ofNat 64 (8 * zc m0))
        (n := 8) rfl, NativeRustcVm.addr_add_zero]; exact hw0)
    have hkept : Kept m0 bp B c (i + 1) (rows ++ [ws]) c' s3.data.dmem :=
      ⟨by rw [rdRows_succ hI.z.kept.hrows, hrd]; rfl, by rw [hd3]; exact hR3,
        by rw [hd3]; exact hlvs⟩
    have h23 : (s3.data.regs.getXReg .X23).toNat = flag (rows ++ [ws]) := by
      show (s3.data.regs.getXReg .X23).toBitVec.toNat = _
      rw [hm3'.regs .X23 _ rfl]
      have hx23 : (s2.data.regs.getXReg .X23).toNat = flag rows := by
        rw [h3r .X23 (by simp [regsA])]; exact hI.z.reg.x23
      simp only [Sym.eval, SBool.eval, eq_apply, hld, Env.ofMachine_regs]
      rw [flag_snoc, show ws.getD 0 0 = ws[0]'(by omega) by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]]
      by_cases hz : (ws[0]'(by omega)) = 0
      · have hl0 : (ws[0]'(by omega)).lane = 0 := lane_eq_zero.mpr hz
        rw [hl0]
        simp only [eq_true hz, ite_true]
        simp only [UInt64.toNat_toBitVec, UInt64.toNat_zero, BitVec.toNat_ofNat, decide_true,
          ↓reduceIte]
        rw [trunc_small (by rw [UInt64.toNat_toBitVec, hx23]; have := flag_le rows; omega),
          UInt64.toNat_toBitVec, hx23]
      · have hl0 : (ws[0]'(by omega)).lane ≠ 0 := fun h ↦ hz (lane_eq_zero.mp h)
        simp only [eq_false hz, ite_false]
        have : (ws[0]'(by omega)).lane.toNat ≠ (BitVec.ofNat 64 0).toNat := by
          intro h; apply hl0; apply UInt64.toNat_inj.mp; simpa using h
        simp only [UInt64.toNat_toBitVec, this, decide_false, Bool.false_eq_true, ↓reduceIte]
        rfl
    have hn := G.lvNw
    have e19 : (s2.data.regs.getXReg .X19).toBitVec + BitVec.ofNat 64 512 = leaf m0 (i + 1) := by
      rw [h3r .X19 (by simp [regsA]), hI.z.reg.x19, NativeRustcVm.addr_add_add]
      congr 2
    have e24 : (s2.data.regs.getXReg .X24).toBitVec = leaf m0 (nr m0) := by
      rw [h3r .X24 (by simp [regsA])]; exact hI.z.reg.x24
    have hc3 : (SBool.cmp .eq .W64 (.bin .add .W64 (.reg .X19) (.lit 512)) (.reg .X24)).not.eval
        (chEnv m0 s2.data (leaf m0 i + BitVec.ofNat 64 (8 * zc m0)) 8) =
        decide (i + 1 ≠ nr m0) := by
      simp only [SBool.eval, eq_apply, Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64,
        Env.ofMachine_regs, e19, e24]
      have h2 : (leaf m0 (nr m0)).toNat = (lv m0).toNat + 512 * nr m0 ∨
          ((leaf m0 (nr m0)).toNat = 0 ∧ (lv m0).toNat + 512 * nr m0 = 2 ^ 64) :=
        NativeRustcVm.toNat_add_ofNat_le hn
      have key : (leaf m0 (i + 1)).toNat = (leaf m0 (nr m0)).toNat ↔ i + 1 = nr m0 := by
        constructor
        · intro h
          by_contra hne
          have hlt : i + 1 < nr m0 := by omega
          have h1 : (leaf m0 (i + 1)).toNat = (lv m0).toNat + 512 * (i + 1) :=
            NativeRustcVm.toNat_add_ofNat (by omega)
          rw [h1] at h
          rcases h2 with h2 | ⟨h2, -⟩ <;> omega
        · intro h; rw [h]
      simp only [key]
      by_cases h : i + 1 = nr m0 <;> simp [h]
    simp only [PcOk, hc3] at hpc3
    have hx19 : (s3.data.regs.getXReg .X19).toBitVec = leaf m0 (i + 1) := by
      rw [hm3'.regs .X19 _ rfl]
      simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
      exact e19
    by_cases hend : i + 1 = nr m0
    · -- the last leaf: `b14`, the return
      simp only [hend, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
        at hpc3
      have hwf4 := frEnv_wf hst hfr4
      have hm4 := frEnv_match hst hfr4
      refine exec_at (infix_of b14_in_code (by simp [b14]) hp) run_b14 hwf4
        (hpc3.trans (congrArg Host.addrOf rfl)) hm4 fun s4 hm4' hpc4 ↦ ?_
      have hd4 : s4.data.dmem = s3.data.dmem := hm4'.dmem_eq hwf4 rfl
      have hfr5 : Frm m0 s4.data := Fr.ofBlock hfr4 hm4 hm4' hwf4 rfl rfl rfl
        fun x hx ↦ absurd hx (by simp)
      simp only [PcOk, hp.label (j := NativeRustcVmArm.Vm.RdRows.b2Offset) NativeRustcVmArm.Vm.RdRows.label_2_at] at hpc4
      refine Eventually.mono (ret_spec hp G hR hpc4 hfr5 ?_) fun _ h ↦ .inl h
      rw [← hend, hkept.hrows]
      refine ⟨?_, by rw [hd4]; exact hkept.hlvs, by rw [hd4]; exact hkept.hrd⟩
      rw [Match.reg_eq hm4 hm4' (v := .reg .X23) rfl rfl]
      exact h23
    simp only [ne_eq, hend, not_false_eq_true, decide_true, ↓reduceIte, hp.label (j := NativeRustcVmArm.Vm.RdRows.b5Offset) NativeRustcVmArm.Vm.RdRows.label_5_at]
      at hpc3
    have hs4 : ∀ r ∈ [XReg.X20, .X21, .X22, .X24, .X25, .X28, .X29],
        s3.data.regs.getXReg r = st.data.regs.getXReg r := fun r hr ↦ by
      rw [h4r r hr]
      exact h3r r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [regsA])
    refine .done _ (.inr ⟨rows ++ [ws], c', hpc3, ⟨hfr4, hx19, ?_, ?_, ?_, h23, ?_, ?_, ?_, ?_, ?_,
      fun h ↦ by rw [hd3]; exact hq2 h, by omega, hrw⟩, hkept⟩)
    · rw [hs4 .X20 (by simp)]; exact hI.z.reg.x20
    · rw [hs4 .X21 (by simp)]; exact hI.z.reg.x21
    · rw [hs4 .X22 (by simp)]; exact hI.z.reg.x22
    · rw [hs4 .X24 (by simp)]; exact hI.z.reg.x24
    · rw [hs4 .X25 (by simp)]; exact hI.z.reg.x25
    · rw [hm3'.regs .X27 _ rfl]
      simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
      rw [h3r .X27 (by simp [regsA]), hI.z.reg.x27, NativeRustcVm.addr_add_add,
        NativeRustcVm.addr_add_add, NativeRustcVm.addr_add_add]
      congr 2
    · rw [hs4 .X28 (by simp)]; exact hI.z.reg.x28
    · rw [hs4 .X29 (by simp)]; exact hI.z.reg.x29

/-- **The loop over the leaves** (`rw > 0`), from leaf `i`. -/
theorem loopA (hp : Placed code k) (G : Geo m0 bp B) (hR : ReaderAt m0.dmem (rdr m0) bp B c)
    (hw : Spec (Labels.label NativeRustcVmArm.Vm.ReaderWords.entryLabel) ReaderWordsPre ReaderWordsPost) {i : Nat}
    {rows : List (List K)} {ci : Nat} {st : MachineState} (hI : HeadA k m0 bp B c i rows ci st) :
    Eventually (step1 Host.exe) (Post m0) st := by
  refine Sym.loop (fun n st ↦ ∃ i rows ci, n = nr m0 - i ∧ HeadA k m0 bp B c i rows ci st)
    (fun n st ⟨i, rows, ci, hn, hI⟩ ↦ ?_) ⟨i, rows, ci, rfl, hI⟩
  refine Eventually.bind (fill_spec hp G hI) fun st' hC ↦ ?_
  refine Eventually.mono (callA_step hp G hR hw hC) fun st'' h ↦ ?_
  rcases h with h | ⟨rows', ci', h⟩
  · exact .inl h
  · exact .inr ⟨_, by have := hI.reg.lt; omega, i + 1, rows', ci', rfl, h⟩

end

end NativeRustcVmArm.Wire.RdRows
