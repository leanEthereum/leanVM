module

public import NativeRustcVmArm.Code.Vm.InsD.Names
public import NativeRustcVmArm.Wire.PhaseM.Reads2

/-!
# `phase_m`: the distinct positions

`sort_run`: from the sort's head (`SortSt … 0`), each query inserted by `ins_d` into the positions
at the working area's byte 2048 (`b15`, `b16`), then the count's check (`b17`, at least one
position, at most 256), to the checks of the sizes (`Chk`).
-/

namespace NativeRustcVmArm.Wire.PhaseM

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt InAny Region)
open NativeRustcVmArm.Vm.PhaseM
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

@[expose] public section

/-- **At the size checks** (`b20`): the distinct positions `ps` at the working area's byte 2048. -/
structure Chk [Host] (m0 : MachineData) (bp : BitVec 64) (B : List UInt8) (c k : Nat)
    (count : Nat) (qs : List Nat) (height lw rw c5 : Nat) (st : MachineState) : Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.PhaseM.b20Offset)
  base : Base m0 st.data
  model : phaseM B c = tail B qs height lw rw c5
  len : qs.length = count
  cnt0 : 0 < count
  cnt : count ≤ 256
  qlt : ∀ q ∈ qs, q < 2 ^ 32
  hlt : height < 2 ^ 32
  lwlt : lw < 2 ^ 32
  rwlt : rw < 2 ^ 32
  ps0 : 0 < (sortD qs).length
  ps256 : (sortD qs).length ≤ 256
  x21 : (st.data.regs.getXReg .X21).toNat = count
  x24 : (st.data.regs.getXReg .X24).toNat = height
  x28 : (st.data.regs.getXReg .X28).toNat = rw
  x26 : (st.data.regs.getXReg .X26).toNat = (sortD qs).length
  f56 : FW m0 st.data.dmem 56 lw.toUInt64
  f48 : FW m0 st.data.dmem 48 (UInt64.ofBitVec (wa m0 2048))
  qsW : WordsAt st.data.dmem (wa m0 0) (qs.map Nat.toUInt64)
  psW : WordsAt st.data.dmem (wa m0 2048) ((sortD qs).map Nat.toUInt64)
  rd : ReaderAt st.data.dmem (rdr m0) bp B c5

end

public section

theorem memExtE0 (i : Nat) :
    UnOp.apply (.memExtend ⟨.UXTX, .E0⟩) .W64 (BitVec.ofNat 64 i) = BitVec.ofNat 64 i := by
  apply BitVec.eq_of_toNat_eq
  simp [UnOp.apply, BitVec.apply_mem_extend, BitVec.unsigned]
  omega

theorem sortD_lt {qs : List Nat} (h : ∀ q ∈ qs, q < 2 ^ 32) : ∀ y ∈ sortD qs, y < 2 ^ 32 :=
  fun y hy ↦ h y (mem_sortD hy)

theorem sortD_ne {qs : List Nat} (h : qs ≠ []) : sortD qs ≠ [] := by
  obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil qs h
  intro he
  have := ((sortD_aux qs [] List.Pairwise.nil).2 q).2 (.inl hq)
  rw [show qs.foldl insD [] = sortD qs from rfl, he] at this
  simp at this

theorem length_sortD_take (qs : List Nat) (i : Nat) : (sortD (qs.take i)).length ≤ i := by
  have := length_sortD (qs.take i)
  simp only [List.length_take] at this
  omega

theorem addC_apply (n : BitVec 64) :
    CmpOp.apply .addC .W64 (BinOp.apply .sub .W64 n (BitVec.ofNat 64 257)) (BitVec.ofNat 64 256) =
      decide (1 ≤ n.toNat ∧ n.toNat ≤ 256) := by
  simp only [CmpOp.apply, BinOp.apply, Sym.low_W64, Sym.ext_W64, BitVec.unsigned]
  have hn := n.isLt
  have h1 : (n - BitVec.ofNat 64 257).toNat = (n.toNat + (2 ^ 64 - 257)) % 2 ^ 64 := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have h2 : (n - BitVec.ofNat 64 257 + BitVec.ofNat 64 256).toNat =
      ((n - BitVec.ofNat 64 257).toNat + 256) % 2 ^ 64 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  have h3 : (BitVec.ofNat 64 256).toNat = 256 := rfl
  rw [h2, h3, h1, Bool.eq_iff_iff, bne_iff_ne, decide_eq_true_iff, ne_eq]
  constructor
  · intro h; omega
  · intro h; omega

variable {m0 : MachineData} {bp : BitVec 64} {B : List UInt8} {c : Nat} [Host] {k : Nat}

/-- **The sort.** -/
theorem sort_run (hp : Placed code k) (G : Geo m0 bp B)
    (hins : Spec (Labels.label NativeRustcVmArm.Vm.InsD.entryLabel) InsDPre InsDPost) {count : Nat} {qs : List Nat}
    {height lw rw c5 : Nat} {st : MachineState}
    (h : SortSt m0 bp B c k count qs height lw rw c5 0 st) :
    Eventually (step1 Host.exe) (fun st' ↦ AtNone m0 B c k st' ∨
      Chk m0 bp B c k count qs height lw rw c5 st') st := by
  have hst := G.st
  refine Sym.loop (tr := step1 Host.exe)
    (fun n st ↦ ∃ i, n = count - i ∧ SortSt m0 bp B c k count qs height lw rw c5 i st)
    (fun _ st ⟨i, hn, h⟩ ↦ ?_) ⟨0, rfl, h⟩
  obtain ⟨hpc, hb, hmod, hql, hc0, hcnt, hqlt, hhl, hlwl, hrwl, x21, x24, x27, x28, x23, x26, hi,
    f56, f48, hqW, hpW, hrd⟩ := h
  have hqi : i < qs.length := by omega
  have hps : (sortD (qs.take i)).length ≤ i := length_sortD_take qs i
  -- `b15`: query `i`, `ins_d`
  have hon : 8 * i + 8 ≤ workBytes := by rw [workBytes_eq]; omega
  have hwf := G.al_wf (o := 8 * i) (n := 8) hon (by omega) hb.fr
  have hmA := G.al_match (o := 8 * i) (n := 8) (a := qAddr) (k := 0) hb.fr (by
    simp only [qAddr, Sym.eval, Env.ofMachine_regs]
    rw [hb.x19]
    have : (st.data.regs.getXReg .X23).toBitVec = BitVec.ofNat 64 (8 * i) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      exact x23
    rw [this, memExtE0, add_lit]
    simp)
  refine exec_at (infix_of b15_in_code (by simp [b15]) hp) run_b15 hwf hpc hmA
    fun s1 hm1 hpc1 ↦ ?_
  have hd1 : s1.data.dmem = st.data.dmem := hm1.dmem_eq hwf rfl
  have hfr1 : Frm m0 s1.data := Fr.ofBlock hb.fr hmA hm1 hwf rfl rfl rfl
    fun x hx ↦ absurd hx (by simp)
  have r1 : ∀ x ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X27, .X28], s1.data.regs.getXReg x =
      st.data.regs.getXReg x := regs_of hmA hm1 (by decide)
  have hb1 : Base m0 s1.data := hb.of_regs hfr1 fun x hx ↦ r1 x (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
    rcases hx with rfl | rfl | rfl <;> simp)
  have hq : (s1.data.regs.getXReg .X2).toBitVec = (qs[i].toUInt64).toBitVec := by
    rw [hm1.regs .X2 _ rfl]
    show (alEnv m0 st.data (wa m0 (8 * i)) 8).load 1 0 8 = _
    apply load_word
    rw [Env.ofMachine_mem0, Env.base_ofMachine _ _ _ rfl, NativeRustcVm.addr_add_zero]
    have := NativeRustcVm.WordsAt.getElem hqW (i := i) (by simp; omega)
    simpa [wa, NativeRustcVm.addr_add_add] using this
  have hpre : InsDPre s1.data := by
    refine ⟨hfr1.stackOk hst (by decide) (by unfold insDStack; omega), ?_, ?_⟩
    · show (s1.data.regs.getXReg .X1).toBitVec.toNat < 256
      rw [hm1.regs .X1 _ rfl]
      show (st.data.regs.getXReg .X26).toBitVec.toNat < 256
      have : (st.data.regs.getXReg .X26).toBitVec.toNat = _ := x26
      omega
    · show Region.Ok s1.data.dmem ⟨(s1.data.regs.getXReg .X0).toBitVec, 2048⟩
      rw [hm1.regs .X0 _ rfl]
      simp only [Sym.eval, Env.ofMachine_regs]
      rw [hb.x19, add_lit]
      exact G.wa_ok (o := 2048) (n := 2048) (by rw [workBytes_eq]; omega) hfr1.kept
  have hx0 : (s1.data.regs.getXReg .X0).toBitVec = wa m0 2048 := by
    rw [hm1.regs .X0 _ rfl]
    simp only [Sym.eval, Env.ofMachine_regs]
    rw [hb.x19, add_lit]
  have hx1 : (s1.data.regs.getXReg .X1).toNat = (sortD (qs.take i)).length := by
    show (s1.data.regs.getXReg .X1).toBitVec.toNat = _
    rw [hm1.regs .X1 _ rfl]; exact x26
  simp only [PcOk] at hpc1
  have hin : ∀ q, InRange (wa m0 2048) 2048 q → InRange (wk m0) workBytes q := fun q hq ↦
    NativeRustcVm.InRange.of_sub hq G.wOk.2 (by rw [workBytes_eq]; omega)
  have hQ : ∀ m', InsDPost s1.data m' → SameOutside s1.data.dmem m'.dmem (fun q ↦
      InRange (stackBelow s1.data insDStack) insDStack q ∨ outs (rdr m0) (W m0) q) ∧
      Saved s1.data m' := by
    rintro m' ⟨-, hs, hsv⟩
    refine ⟨NativeRustcVm.SameOutside.mono hs fun q hq ↦ .inr (.inr (.inr (hin q ?_))), hsv⟩
    rw [show s1.data.regs.X0.toBitVec = wa m0 2048 from hx0] at hq
    exact hq
  refine Fr.leafAt (N' := insDStack) hfr1 hst.2.1 (by unfold insDStack; omega) (by simp)
    (by decide) (fun q hq ↦ G.rgeo.not_frame (by omega) hq) hins hpc1 hpre hQ
    fun m2 hfr2 hq2 hcs ↦ ?_
  obtain ⟨hpost, hs2, -⟩ := hq2
  have hpost' := hpost (sortD (qs.take i)) hx1.symm
    (fun y hy ↦ by have := sortD_lt (fun q hq ↦ hqlt q (List.mem_of_mem_take hq)) y hy; omega)
    (by rw [show s1.data.regs.X0.toBitVec = wa m0 2048 from hx0, hd1]; exact hpW)
  rw [show s1.data.regs.X2.toNat = qs[i] by
    have := congrArg BitVec.toNat hq
    simp only [UInt64.toNat_toBitVec] at this
    rw [toNat_toUInt64_of_lt (by have := hqlt _ (List.getElem_mem hqi); omega)] at this
    exact this, ← sortD_take_succ qs hqi] at hpost'
  obtain ⟨hn2, hpW2⟩ := hpost'
  rw [show s1.data.regs.X0.toBitVec = wa m0 2048 from hx0] at hpW2 hs2
  have hb2 : Base m0 m2 := hb1.call hfr2 hcs
  -- `b16`
  refine blk hp b16_in_code (by simp [b16]) run_b16 rfl rfl hst hfr2 rfl
    fun s3 hfr3 hd3 hm3 hpc3 ↦ ?_
  have hm2 := frEnv_match hst hfr2
  have r3 : ∀ x ∈ [XReg.X19, .X20, .X21, .X22, .X24, .X27, .X28], s3.data.regs.getXReg x =
      m2.regs.getXReg x := regs_of hm2 hm3 (by decide)
  have hb3 : Base m0 s3.data := hb2.of_regs hfr3 fun x hx ↦ r3 x (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
    rcases hx with rfl | rfl | rfl <;> simp)
  have rr : ∀ x ∈ [XReg.X21, .X24, .X27, .X28], (s3.data.regs.getXReg x) = st.data.regs.getXReg x :=
    fun x hx ↦ by
      rw [r3 x (by simp at hx ⊢; rcases hx with rfl | rfl | rfl | rfl <;> simp),
        hcs x (by simp at hx; rcases hx with rfl | rfl | rfl | rfl <;> rfl),
        r1 x (by simp at hx ⊢; rcases hx with rfl | rfl | rfl | rfl <;> simp)]
  have x23' : (s3.data.regs.getXReg .X23).toNat = 8 * (i + 1) := by
    show (s3.data.regs.getXReg .X23).toBitVec.toNat = _
    rw [hm3.regs .X23 _ rfl]
    simp only [Sym.eval, Env.ofMachine_regs]
    rw [hcs .X23 rfl, r1 .X23 (by simp), add_lit, BitVec.toNat_add, BitVec.toNat_ofNat]
    have : (st.data.regs.getXReg .X23).toBitVec.toNat = 8 * i := x23
    rw [this]; omega
  have x26' : (s3.data.regs.getXReg .X26).toNat = (sortD (qs.take (i + 1))).length := by
    show (s3.data.regs.getXReg .X26).toBitVec.toNat = _
    rw [hm3.regs .X26 _ rfl]; exact hn2
  have hs12 : SameOutside st.data.dmem m2.dmem (InRange (wa m0 2048) 2048) := by
    rw [← hd1]; exact hs2
  have f56' : FW m0 s3.data.dmem 56 lw.toUInt64 := by
    rw [hd3]; exact f56.keep hs12 fun j hj hq ↦ G.rgeo.not_frame (F := 192) (by omega)
      (.inr (.inr (NativeRustcVm.InRange.of_sub hq G.wOk.2 (by rw [workBytes_eq]; omega)))) (by
        have hb0 := Ring.base_toNat (m0 := m0) (F := 192) (by have := hst.2.1; omega)
        have := hst.2.1; have := m0.regs.SP.toNat_lt
        rw [Sym.inRange_iff (by rw [hb0]; omega), hb0, NativeRustcVm.addr_add_add,
          NativeRustcVm.toNat_add_ofNat (by rw [hb0]; omega), hb0]; omega)
  have f48' : FW m0 s3.data.dmem 48 (UInt64.ofBitVec (wa m0 2048)) := by
    rw [hd3]; exact f48.keep hs12 fun j hj hq ↦ G.rgeo.not_frame (F := 192) (by omega)
      (.inr (.inr (NativeRustcVm.InRange.of_sub hq G.wOk.2 (by rw [workBytes_eq]; omega)))) (by
        have hb0 := Ring.base_toNat (m0 := m0) (F := 192) (by have := hst.2.1; omega)
        have := hst.2.1; have := m0.regs.SP.toNat_lt
        rw [Sym.inRange_iff (by rw [hb0]; omega), hb0, NativeRustcVm.addr_add_add,
          NativeRustcVm.toNat_add_ofNat (by rw [hb0]; omega), hb0]; omega)
  have hqW' : WordsAt s3.data.dmem (wa m0 0) (qs.map Nat.toUInt64) := by
    rw [hd3]
    exact G.keep_wa (L := [(2048, 2048)]) hs12
      (by rw [NativeRustcVm.length_wordsBytes, List.length_map, hql, workBytes_eq]; omega) hqW
      (fun q hq ↦ .inr (.inr (.inr ⟨_, List.mem_singleton_self _, hq⟩)))
      (by
        intro p hp
        simp only [List.mem_singleton] at hp
        subst hp
        rw [NativeRustcVm.length_wordsBytes, List.length_map, hql, workBytes_eq]
        omega)
  have hrd' : ReaderAt s3.data.dmem (rdr m0) bp B c5 := by
    rw [hd3]
    exact G.rgeo.reader_frame rfl hrd (NativeRustcVm.SameOutside.mono hs12 fun q hq ↦
      .inr (.inr (NativeRustcVm.InRange.of_sub hq G.wOk.2 (by rw [workBytes_eq]; omega))))
  have hcond : (SBool.cmp .eq .W64 (.reg .X27) (.bin .add .W64 (.reg .X23) (.lit 8))).not.eval
      (frEnv m0 m2) = !decide (i + 1 = count) := by
    simp only [SBool.eval, Sym.eval, Env.ofMachine_regs]
    rw [eq_apply, hcs .X27 rfl, hcs .X23 rfl, r1 .X27 (by simp), r1 .X23 (by simp), add_lit,
      BitVec.toNat_add, BitVec.toNat_ofNat]
    have e27 : (st.data.regs.getXReg .X27).toBitVec.toNat = 8 * count := x27
    have e23 : (st.data.regs.getXReg .X23).toBitVec.toNat = 8 * i := x23
    rw [e27, e23]
    by_cases hh : i + 1 = count
    · rw [decide_eq_true (by omega), decide_eq_true hh]
    · rw [decide_eq_false (by omega), decide_eq_false hh]
  simp only [PcOk, hcond] at hpc3
  by_cases hlast : i + 1 = count
  · -- `b17`
    simp only [hlast, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc3
    have htk : qs.take (i + 1) = qs := List.take_of_length_le (by omega)
    rw [htk] at x26' hpW2
    have hps0 : 0 < (sortD qs).length :=
      List.length_pos_iff.mpr (sortD_ne (List.ne_nil_of_length_pos (by omega)))
    have hps256 : (sortD qs).length ≤ 256 := by have := length_sortD qs; omega
    refine blk hp b17_in_code (by simp [b17]) run_b17 rfl rfl hst hb3.fr hpc3
      fun s4 hfr4 hd4 hm4 hpc4 ↦ .done _ (.inl (.inr ?_))
    have hm3' := frEnv_match hst hb3.fr
    have r4 : ∀ x ∈ [XReg.X19, .X20, .X21, .X22, .X24, .X26, .X28], s4.data.regs.getXReg x =
        s3.data.regs.getXReg x := regs_of hm3' hm4 (by decide)
    have hc : (SBool.cmp .addC .W64 (.bin .sub .W64 (.reg .X26) (.lit 257)) (.lit 256)).eval
        (frEnv m0 s3.data) = true := by
      simp only [SBool.eval, Sym.eval, Env.ofMachine_regs]
      rw [addC_apply, show (s3.data.regs.getXReg .X26).toBitVec.toNat = _ from x26']
      simp only [decide_eq_true_eq]; omega
    simp only [PcOk, hc, ↓reduceIte] at hpc4
    refine ⟨hpc4.trans (hp.label (j := NativeRustcVmArm.Vm.PhaseM.b20Offset) NativeRustcVmArm.Vm.PhaseM.label_14_at), hb3.of_regs hfr4 fun x hx ↦ r4 x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl | rfl <;> simp), hmod, hql, hc0, hcnt, hqlt, hhl, hlwl, hrwl,
      hps0, hps256, ?_, ?_, ?_, ?_, by rw [hd4]; exact f56', by rw [hd4]; exact f48',
      by rw [hd4]; exact hqW', by rw [hd4, hd3]; exact hpW2, by rw [hd4]; exact hrd'⟩
    · rw [r4 .X21 (by simp), rr .X21 (by simp)]; exact x21
    · rw [r4 .X24 (by simp), rr .X24 (by simp)]; exact x24
    · rw [r4 .X28 (by simp), rr .X28 (by simp)]; exact x28
    · rw [r4 .X26 (by simp)]; exact x26'
  · simp only [hlast, decide_false, Bool.not_false, ↓reduceIte] at hpc3
    refine .done _ (.inr ⟨count - (i + 1), by omega, i + 1, rfl, ⟨hpc3.trans
      (hp.label (j := NativeRustcVmArm.Vm.PhaseM.b15Offset) NativeRustcVmArm.Vm.PhaseM.label_10_at), hb3, hmod, hql, hc0, hcnt, hqlt, hhl, hlwl, hrwl, ?_, ?_, ?_, ?_,
      x23', x26', by omega, f56', f48', hqW', by rw [hd3]; exact hpW2, hrd'⟩⟩)
    · rw [rr .X21 (by simp)]; exact x21
    · rw [rr .X24 (by simp)]; exact x24
    · rw [rr .X27 (by simp)]; exact x27
    · rw [rr .X28 (by simp)]; exact x28

end

end NativeRustcVmArm.Wire.PhaseM
