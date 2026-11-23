module

public import NativeRustcVmArm.Code.Vm.ReaderWords.Names
public import NativeRustcVmArm.Wire.RdRows.ZeroB
public import NativeRustcVmArm.Wire.RdRows.RowA

/-!
# `rd_rows`' leaves without a row (`rw = 0`)

`Reader::words` reads no word after the leaf's zeros (`b22`); `None` (`b23`, `b1`), or the next
leaf (`b24`): the loop's head again or `Some` with every row empty (`b25`): `callB_step`; the loop
over the leaves (`loopB`).
-/

namespace NativeRustcVmArm.Wire.RdRows

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt InAny Region)
open NativeRustcVmArm.Vm.RdRows
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

public section

variable [Host] {k : Nat} {m0 : MachineData} {bp : BitVec 64} {B : List UInt8} {c : Nat}

omit [Host] in
theorem flag_empty {rows : List (List K)} (h : ∀ x ∈ rows, x.length = 0) : flag rows = 1 := by
  unfold flag
  simp only [eq_true (fun x hx ↦ by rw [List.length_eq_zero_iff.mp (h x hx)]; rfl :
    ∀ x ∈ rows, x.getD 0 0 = 0), ite_true]

omit [Host] in
theorem saved_regsB : ∀ r ∈ (.X8 :: regsB), r ≠ .X8 → calleeSaved r = true := by decide

/-- **Leaf `i`**, no row read after its zeros (`b22` to `b25`). -/
theorem callB_step (hp : Placed code k) (G : Geo m0 bp B) (hR : ReaderAt m0.dmem (rdr m0) bp B c)
    (hw : Spec (Labels.label NativeRustcVmArm.Vm.ReaderWords.entryLabel) ReaderWordsPre ReaderWordsPost) {i : Nat}
    {rows : List (List K)} {ci : Nat} {st : MachineState} (hI : CallB k m0 bp B c i rows ci st) :
    Eventually (step1 Host.exe) (fun st' ↦ Post m0 st' ∨
      ∃ rows' ci', HeadB k m0 bp B c (i + 1) rows' ci' st') st := by
  have hst := G.g.st
  have hi := hI.z.reg.lt
  have hrw := hI.z.reg.rw0
  have hlw := G.lw64
  have ho : 8 * lw m0 + 0 ≤ 512 := by omega
  have hwf := frEnv_wf hst hI.z.reg.fr
  have hm := frEnv_match hst hI.z.reg.fr
  refine exec_at (infix_of b22_in_code (by simp [b22]) hp) run_b22 hwf hI.pc hm fun s1 hm1 hpc1 ↦ ?_
  have hd1 : s1.data.dmem = st.data.dmem := hm1.dmem_eq hwf rfl
  have hfr1 : Frm m0 s1.data := Fr.ofBlock hI.z.reg.fr hm hm1 hwf rfl rfl rfl
    fun x hx ↦ absurd hx (by simp)
  have hr1 := regs_keep hm hm1 (rs := regsB) (by decide)
  have hx0 : s1.data.regs.X0.toBitVec = rdr m0 := by
    rw [show s1.data.regs.X0 = s1.data.regs.getXReg .X0 from rfl, hm1.regs .X0 _ rfl]
    exact hI.z.reg.x21
  have hx1 : s1.data.regs.X1.toBitVec = leaf m0 i + BitVec.ofNat 64 (8 * lw m0) := by
    rw [show s1.data.regs.X1 = s1.data.regs.getXReg .X1 from rfl, hm1.regs .X1 _ rfl]
    simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
    rw [hI.z.reg.x19]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [UInt64.toNat_toBitVec, hI.z.reg.x22, BitVec.toNat_ofNat]
    omega
  have hx2 : s1.data.regs.X2.toNat = 0 := by
    rw [show s1.data.regs.X2 = s1.data.regs.getXReg .X2 from rfl, ← UInt64.toNat_toBitVec,
      hm1.regs .X2 _ rfl]
    rfl
  have hP := G.words_pre hi ho hfr1 hx0 hx1 (by rw [hx2]) (by rw [hd1]; exact hI.z.kept.hrd)
  refine Fr.leaf (N' := readerWordsStack) hfr1 hst.2.1 (by decide) (by simp) (by decide)
    (fun q hq ↦ G.g.not_frame (by omega) hq)
    (Spec.carry hw fun m ↦ m.regs.X0.toBitVec = rdr m0 ∧
      m.regs.X1.toBitVec = leaf m0 i + BitVec.ofNat 64 (8 * lw m0) ∧ m.regs.X2.toNat = 0)
    (fun m m' ⟨⟨_, hs, hsv⟩, h0, h1, h2⟩ ↦ ⟨?_, hsv⟩) hpc1 ⟨hP, hx0, hx1, hx2⟩ ?_
  · refine NativeRustcVm.SameOutside.mono hs fun q ⟨r, hr, h⟩ ↦ ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact absurd h (by
        show ¬InRange m.regs.X1.toBitVec (8 * m.regs.X2.toNat) q
        rw [h2]; unfold InRange; omega)
    · exact .inr (.inl (by have h' : InRange (m.regs.X0.toBitVec + 16#64) 8 q := h; rwa [h0] at h'))
    · exact .inl h
  intro m2 hfr2 ⟨hpost, _⟩ hcs
  obtain ⟨hres, hs2, -⟩ := hpost
  simp only [hx0, hx1, hx2] at hres hs2
  have hres' := hres bp B ci (by rw [hd1]; exact hI.z.kept.hrd)
  have hsame := G.call_same (sz := 8 * 0) hfr1 hs2
  have h2r : ∀ r ∈ regsB, m2.regs.getXReg r = st.data.regs.getXReg r :=
    fun r hr ↦ (hcs r (saved_regsB r (List.mem_cons_of_mem _ hr) (by
      intro h; subst h; simp [regsB] at hr))).trans (hr1 r hr)
  have hci : ci ≤ B.length := hI.z.kept.hrd.c_le
  have hrd : rdWords B 0 ci = some ([], ci) := by simp [rdWords, hci]
  rw [hrd] at hres'
  obtain ⟨h0', -, hR2⟩ := hres'
  -- `b23`
  have hwf2 := frEnv_wf hst hfr2
  have hm2 := frEnv_match hst hfr2
  refine exec_at (infix_of b23_in_code (by simp [b23]) hp) run_b23 hwf2
    (by simp only [Nat.add_assoc, NativeRustcVmArm.Vm.RdRows.b22_next]) hm2 fun s2 hm2' hpc2 ↦ ?_
  have hd2 : s2.data.dmem = m2.dmem := hm2'.dmem_eq hwf2 rfl
  have hfr3 : Frm m0 s2.data := Fr.ofBlock hfr2 hm2 hm2' hwf2 rfl rfl rfl
    fun x hx ↦ absurd hx (by simp)
  have h3r : ∀ r ∈ regsB, s2.data.regs.getXReg r = st.data.regs.getXReg r :=
    fun r hr ↦ (regs_keep hm2 hm2' (rs := regsB) (by decide) r hr).trans (h2r r hr)
  have hc : (SBool.cmp .eq .W32 (.reg .X0) (.lit 0)).eval (frEnv m0 m2) = false := by
    simp only [SBool.eval, Sym.eval, CmpOp.apply, Env.ofMachine_regs,
      show m2.regs.getXReg .X0 = m2.regs.X0 from rfl, h0']
    decide
  simp only [PcOk, hc, Bool.false_eq_true, ↓reduceIte, Nat.add_assoc,
    NativeRustcVmArm.Vm.RdRows.b23_next] at hpc2
  obtain ⟨hrl', hrw'⟩ := rdRows_length (B := B) _ _ hI.z.kept.hrows
  have hlvs : LeavesAt s2.data.dmem (lv m0) ((rows ++ [[]]).map fun x ↦ paddedLeaf x (lw m0)) := by
    rw [List.map_append, List.map_singleton, hd2]
    refine leaves_snoc (G.call_leaves hi ho hsame (by simpa using hrl') (fun x hx ↦ ?_)
      (by rw [hd1]; exact hI.z.kept.hlvs)) ?_
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      simp only [paddedLeaf, List.length_append, List.length_replicate, hrw' y hy]
      omega
    · rw [map_lane_paddedLeaf, List.length_map, hrl', List.length_nil, Nat.sub_zero,
        List.map_nil, List.append_nil]
      exact G.call_zeros hi ho (le_refl _) hsame (by rw [hd1]; exact hI.z.zs)
  have hkept : Kept m0 bp B c (i + 1) (rows ++ [[]]) ci s2.data.dmem :=
    ⟨by rw [rdRows_succ hI.z.kept.hrows, hrw, hrd]; rfl, by rw [hd2]; exact hR2, hlvs⟩
  -- `b24`
  have hwf3 := frEnv_wf hst hfr3
  have hm3 := frEnv_match hst hfr3
  refine exec_at (infix_of b24_in_code (by simp [b24]) hp) run_b24 hwf3 hpc2 hm3
    fun s3 hm3' hpc3 ↦ ?_
  have hd3 : s3.data.dmem = s2.data.dmem := hm3'.dmem_eq hwf3 rfl
  have hfr4 : Frm m0 s3.data := Fr.ofBlock hfr3 hm3 hm3' hwf3 rfl rfl rfl
    fun x hx ↦ absurd hx (by simp)
  have h4r := regs_keep hm3 hm3' (rs := [.X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27])
    (by decide)
  have hn := G.lvNw
  have e19 : (s2.data.regs.getXReg .X19).toBitVec + BitVec.ofNat 64 512 = leaf m0 (i + 1) := by
    rw [h3r .X19 (by simp [regsB]), hI.z.reg.x19, NativeRustcVm.addr_add_add]
    congr 2
  have e24 : (s2.data.regs.getXReg .X24).toBitVec = leaf m0 (nr m0) := by
    rw [h3r .X24 (by simp [regsB])]; exact hI.z.reg.x24
  have hc3 : (SBool.cmp .eq .W64 (.bin .add .W64 (.reg .X19) (.lit 512)) (.reg .X24)).not.eval
      (frEnv m0 s2.data) = decide (i + 1 ≠ nr m0) := by
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
  by_cases hend : i + 1 = nr m0
  · -- the last leaf: `b25`, the return
    simp only [hend, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
      at hpc3
    have hwf4 := frEnv_wf hst hfr4
    have hm4 := frEnv_match hst hfr4
    refine exec_at (infix_of b25_in_code (by simp [b25]) hp) run_b25 hwf4
      (hpc3.trans (congrArg Host.addrOf rfl)) hm4 fun s4 hm4' hpc4 ↦ ?_
    have hd4 : s4.data.dmem = s3.data.dmem := hm4'.dmem_eq hwf4 rfl
    have hfr5 : Frm m0 s4.data := Fr.ofBlock hfr4 hm4 hm4' hwf4 rfl rfl rfl
      fun x hx ↦ absurd hx (by simp)
    simp only [PcOk, hp.label (j := NativeRustcVmArm.Vm.RdRows.b2Offset) NativeRustcVmArm.Vm.RdRows.label_2_at] at hpc4
    refine Eventually.mono (ret_spec hp G hR hpc4 hfr5 ?_) fun _ h ↦ .inl h
    rw [← hend, hkept.hrows]
    refine ⟨?_, by rw [hd4, hd3]; exact hkept.hlvs, by rw [hd4, hd3]; exact hkept.hrd⟩
    rw [flag_empty fun x hx ↦ ?_]
    · show (s4.data.regs.getXReg .X23).toBitVec.toNat = 1
      rw [hm4'.regs .X23 _ rfl]
      rfl
    · rcases List.mem_append.mp hx with hx | hx
      · rw [hrw' x hx, hrw]
      · rw [List.mem_singleton.mp hx]; rfl
  simp only [ne_eq, hend, not_false_eq_true, decide_true, ↓reduceIte, hp.label (j := NativeRustcVmArm.Vm.RdRows.b16Offset) NativeRustcVmArm.Vm.RdRows.label_14_at]
    at hpc3
  have hs4 : ∀ r ∈ [XReg.X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27],
      s3.data.regs.getXReg r = st.data.regs.getXReg r := fun r hr ↦ by
    rw [h4r r hr]
    exact h3r r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [regsB])
  have hx19 : (s3.data.regs.getXReg .X19).toBitVec = leaf m0 (i + 1) := by
    rw [hm3'.regs .X19 _ rfl]
    simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
    exact e19
  refine .done _ (.inr ⟨rows ++ [[]], ci, hpc3, ⟨hfr4, hx19, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    by omega, hrw⟩, by rw [hd3]; exact hkept⟩)
  · rw [hs4 .X20 (by simp)]; exact hI.z.reg.x20
  · rw [hs4 .X21 (by simp)]; exact hI.z.reg.x21
  · rw [hs4 .X22 (by simp)]; exact hI.z.reg.x22
  · rw [hs4 .X23 (by simp)]; exact hI.z.reg.x23
  · rw [hs4 .X24 (by simp)]; exact hI.z.reg.x24
  · rw [hs4 .X25 (by simp)]; exact hI.z.reg.x25
  · rw [hs4 .X26 (by simp)]; exact hI.z.reg.x26
  · rw [hs4 .X27 (by simp)]; exact hI.z.reg.x27
  · rw [hm3'.regs .X28 _ rfl]
    simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
    rw [h3r .X28 (by simp [regsB]), hI.z.reg.x28, NativeRustcVm.addr_add_add,
      NativeRustcVm.addr_add_add, NativeRustcVm.addr_add_add]
    congr 2

/-- **The loop over the leaves** (`rw = 0`), from leaf `i`. -/
theorem loopB (hp : Placed code k) (G : Geo m0 bp B) (hR : ReaderAt m0.dmem (rdr m0) bp B c)
    (hw : Spec (Labels.label NativeRustcVmArm.Vm.ReaderWords.entryLabel) ReaderWordsPre ReaderWordsPost) {i : Nat}
    {rows : List (List K)} {ci : Nat} {st : MachineState} (hI : HeadB k m0 bp B c i rows ci st) :
    Eventually (step1 Host.exe) (Post m0) st := by
  refine Sym.loop (fun n st ↦ ∃ i rows ci, n = nr m0 - i ∧ HeadB k m0 bp B c i rows ci st)
    (fun n st ⟨i, rows, ci, hn, hI⟩ ↦ ?_) ⟨i, rows, ci, rfl, hI⟩
  refine Eventually.bind (fillB_spec hp G hI) fun st' hC ↦ ?_
  refine Eventually.mono (callB_step hp G hR hw hC) fun st'' h ↦ ?_
  rcases h with h | ⟨rows', ci', h⟩
  · exact .inl h
  · exact .inr ⟨_, by have := hI.reg.lt; omega, i + 1, rows', ci', rfl, h⟩

end

end NativeRustcVmArm.Wire.RdRows
