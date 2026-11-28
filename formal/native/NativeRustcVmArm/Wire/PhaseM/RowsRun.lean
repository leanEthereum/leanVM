module

public import NativeRustcVmArm.Code.Vm.RdRows.Names
public import NativeRustcVmArm.Wire.PhaseM.Checks2

/-!
# `phase_m`: the rows

`rows_run`: from `rd_rows`' call (`b24`, the leaves' address to the frame's byte 40), `rd_rows`'
contract reads the rows into the leaves; the rows' check (`b25`) to `None`, or to the hashing of
the leaves (`Rows`).
-/

namespace NativeRustcVmArm.Wire.PhaseM

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt InAny Region)
open NativeRustcVmArm.Vm.PhaseM
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.KeccakHash

public section

theorem disjoint4 {a b c d : Region}
    (hab : NativeRustcVm.Apart a.addr a.size b.addr b.size)
    (hac : NativeRustcVm.Apart a.addr a.size c.addr c.size)
    (had : NativeRustcVm.Apart a.addr a.size d.addr d.size)
    (hbc : NativeRustcVm.Apart b.addr b.size c.addr c.size)
    (hbd : NativeRustcVm.Apart b.addr b.size d.addr d.size)
    (hcd : NativeRustcVm.Apart c.addr c.size d.addr d.size) :
    NativeRustcVm.Disjoint [a, b, c, d] := by
  simp only [NativeRustcVm.Disjoint, List.pairwise_cons, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true, IsEmpty.forall_iff,
    implies_true]
  exact ⟨⟨hab, hac, had⟩, ⟨hbc, hbd⟩, hcd⟩

variable {m0 : MachineData} {bp : BitVec 64} {B : List UInt8} {c : Nat}

/-- A callee's stack is the function's. -/
theorem stack_sub {m : MachineData} (hst : StackOk m0 1184) (hfr : Frm m0 m) {N' : Nat}
    (hN' : 192 + N' ≤ 1184) {q : BitVec 64} (h : InRange (stackBelow m N') N' q) :
    InRange (base m0 1184) 1184 q := by
  have hN := hst.2.1
  have hSP := m0.regs.SP.toNat_lt
  rw [Ring.stackBelow_eq hfr.sp (by omega)] at h
  have hb1 := Ring.base_toNat (m0 := m0) (F := 192 + N') (by omega)
  have hb2 := Ring.base_toNat (m0 := m0) (F := 1184) hN
  rw [Sym.inRange_iff (by rw [hb1]; omega), hb1] at h
  rw [Sym.inRange_iff (by rw [hb2]; omega), hb2]
  omega

variable [Host] {k : Nat}

/-- **The rows.** -/
theorem rows_run (hp : Placed code k) (G : Geo m0 bp B)
    (hrows : Spec (Labels.label NativeRustcVmArm.Vm.RdRows.entryLabel) RdRowsPre RdRowsPost) {count : Nat} {qs : List Nat}
    {height lw rw c5 : Nat} {st : MachineState}
    (h : Chk m0 bp B c k count qs height lw rw c5 ⟨st.data, Host.addrOf (k + NativeRustcVmArm.Vm.PhaseM.b20Offset)⟩)
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.PhaseM.b24Offset)) (h32 : height ≤ 32) (h64 : lw ≤ 64) (hrl : rw ≤ lw)
    (hlast : (sortD qs).getLastD 0 < 2 ^ height) :
    Eventually (step1 Host.exe) (fun st' ↦ AtNone m0 B c k st' ∨
      ∃ rows c6, Rows m0 bp B c k count qs height lw rows c6 st') st := by
  obtain ⟨-, hb, hmod, hql, hc0, hcnt, hqlt, hhl, hlwl, hrwl, hps0, hps256, x21, x24, x28, x26,
    f56, f48, hqW, hpW, hrd⟩ := h
  have hst := G.st
  set n := (sortD qs).length with hn
  have hne : sortD qs ≠ [] := List.ne_nil_of_length_pos hps0
  rw [tail_ok ⟨h32, h64, hrl, hne, hlast⟩] at hmod
  have hqb : ((qs.map Nat.toUInt64).flatMap NativeRustcVm.wordBytes).length ≤ 2048 := by
    rw [NativeRustcVm.length_wordsBytes, List.length_map, hql]; omega
  have hpb : (((sortD qs).map Nat.toUInt64).flatMap NativeRustcVm.wordBytes).length ≤ 2048 := by
    rw [NativeRustcVm.length_wordsBytes, List.length_map]; omega
  -- `b24`
  refine blkW hp b24_in_code (by simp [b24]) run_b24 (by decide) rfl hst hb.fr hpc
    fun s1 hfr1 _ hm1 hpc1 ↦ ?_
  have hm := frEnv_match hst hb.fr
  have hwf := frEnv_wf hst hb.fr
  have hs1 := Match.sameOutside_in hm1 hwf (r0 := 0) (o := 40) (n := 8) rfl (by omega) (by decide)
  have r1 : ∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X24, .X26, .X28], s1.data.regs.getXReg r =
      st.data.regs.getXReg r := regs_of hm hm1 (by decide)
  have hb1 : Base m0 s1.data := hb.of_regs hfr1 fun r hr ↦ r1 r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl <;> simp)
  have hx4 : (s1.data.regs.getXReg .X4).toBitVec = wa m0 352512 := by
    rw [hm1.regs .X4 _ rfl]
    simp only [Sym.eval, Env.ofMachine_regs]
    rw [hb.x19, add_lit]
  have f40 : FW m0 s1.data.dmem 40 (UInt64.ofBitVec (wa m0 352512)) := by
    have := hm1.bytesAt_write (r := 0) (o := 40) (n := 8) (b := base m0 192) (sz := 192) rfl
      (by omega) (v := .bin .add .W64 (.reg .X19) (.lit 352512)) (by decide)
    have hw := wordAt_reg this
    simp only [Sym.eval, Env.ofMachine_regs] at hw
    rwa [hb.x19, add_lit] at hw
  have f56' : FW m0 s1.data.dmem 56 lw.toUInt64 :=
    FW.frame hst hs1 (by omega) (by omega) (.inr (by omega)) f56
  have f48' : FW m0 s1.data.dmem 48 (UInt64.ofBitVec (wa m0 2048)) :=
    FW.frame hst hs1 (by omega) (by omega) (.inr (by omega)) f48
  have hqW1 : WordsAt s1.data.dmem (wa m0 0) (qs.map Nat.toUInt64) :=
    keep_frame G hs1 (by omega) (by rw [workBytes_eq]; omega) hqW
  have hpW1 : WordsAt s1.data.dmem (wa m0 2048) ((sortD qs).map Nat.toUInt64) :=
    keep_frame G hs1 (by omega) (by rw [workBytes_eq]; omega) hpW
  have hrd1 : ReaderAt s1.data.dmem (rdr m0) bp B c5 := reader_fr G hs1 (by omega) hrd
  -- the call
  have hNs : 192 + rdRowsStack ≤ 1184 := by unfold rdRowsStack readerWordsStack readerLeStack; omega
  have hx0 : s1.data.regs.X0.toBitVec = rdr m0 := by
    rw [show s1.data.regs.X0.toBitVec = (s1.data.regs.getXReg .X0).toBitVec from rfl,
      hm1.regs .X0 _ rfl]
    exact hb.x22
  have hx1 : s1.data.regs.X1.toNat = n := by
    show (s1.data.regs.getXReg .X1).toBitVec.toNat = _
    rw [hm1.regs .X1 _ rfl]; exact x26
  have hx2 : s1.data.regs.X2.toNat = lw := by
    show (s1.data.regs.getXReg .X2).toBitVec.toNat = _
    rw [hm1.regs .X2 _ rfl]
    show ((frEnv m0 st.data).load 0 56 8).toNat = lw
    rw [load_fw f56]
    exact toNat_toUInt64_of_lt (by omega)
  have hx3 : s1.data.regs.X3.toNat = rw := by
    show (s1.data.regs.getXReg .X3).toBitVec.toNat = _
    rw [hm1.regs .X3 _ rfl]; exact x28
  have hx4' : s1.data.regs.X4.toBitVec = wa m0 352512 := hx4
  have hon : 352512 + 512 * n ≤ workBytes := by rw [workBytes_eq]; omega
  have hpre : RdRowsPre s1.data := by
    refine ⟨hfr1.stackOk hst (by decide) hNs, by omega, by omega, by omega, by omega, ?_, bp, B, c5,
      by rw [hx0]; exact hrd1, ?_⟩
    · rw [hx4', hx1]; exact G.wa_ok hon hfr1.kept
    · rw [hx0, hx4', hx1]
      exact disjoint4 (hfr1.apart G.sp G.sR.symm hNs).symm (hfr1.apart G.sp G.sB.symm hNs).symm
        (hfr1.apart G.sp (G.wa_apart hon (by omega) G.sW.symm) hNs).symm G.rB
        (G.wa_apart hon (by omega) G.rW.symm).symm (G.wa_apart hon (by omega) G.bW.symm).symm
  simp only [PcOk] at hpc1
  have hQ : ∀ m', RdRowsPost s1.data m' → SameOutside s1.data.dmem m'.dmem (fun q ↦
      InRange (stackBelow s1.data rdRowsStack) rdRowsStack q ∨ outs (rdr m0) (W m0) q) ∧
      Saved s1.data m' := by
    rintro m' ⟨-, hs, hsv⟩
    refine ⟨NativeRustcVm.SameOutside.mono hs fun q ⟨R, hR, hq⟩ ↦ ?_, hsv⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl
    · rw [hx4', hx1] at hq
      exact .inr (.inr (.inr (NativeRustcVm.InRange.of_sub hq G.wOk.2 hon)))
    · rw [hx0] at hq; exact .inr (.inl hq)
    · exact .inl hq
  refine Fr.leafAt (N' := rdRowsStack) hfr1 hst.2.1 hNs (by simp) (by decide)
    (fun q hq ↦ G.rgeo.not_frame (by omega) hq) hrows hpc1 hpre hQ fun m2 hfr2 hq2 hcs ↦ ?_
  have hsc : SameOutside s1.data.dmem m2.dmem fun q ↦ InRange (stackBelow s1.data rdRowsStack)
      rdRowsStack q ∨ InRange (base m0 192 + BitVec.ofNat 64 0) 0 q ∨ outs (rdr m0) (W m0) q :=
    NativeRustcVm.SameOutside.mono (hQ m2 hq2).1 fun q hq ↦ hq.elim .inl (.inr ∘ .inr)
  obtain ⟨hpost, hs2, -⟩ := hq2
  have hpost' := hpost bp B c5 (by rw [hx0]; exact hrd1)
  rw [hx1, hx3, hx2, hx4', hx0] at hpost'
  have hs2' : SameOutside s1.data.dmem m2.dmem fun q ↦ InRange (base m0 1184) 1184 q ∨
      InRange (rdr m0 + BitVec.ofNat 64 16) 8 q ∨ InRange (outA m0) phaseBytes q ∨
      ∃ p ∈ [(352512, 512 * n)], InRange (wa m0 p.1) p.2 q :=
    NativeRustcVm.SameOutside.mono hs2 fun q ⟨R, hR, hq⟩ ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
      rcases hR with rfl | rfl | rfl
      · rw [hx4', hx1] at hq; exact .inr (.inr (.inr ⟨_, List.mem_singleton_self _, hq⟩))
      · rw [hx0] at hq; exact .inr (.inl hq)
      · exact .inl (stack_sub hst hfr1 hNs hq)
  have hb2 : Base m0 m2 := hb1.call hfr2 hcs
  -- `b25`
  refine blk hp b25_in_code (by simp [b25]) run_b25 rfl rfl hst hfr2 rfl
    fun s3 hfr3 hd3 hm3 hpc3 ↦ ?_
  have hm2 := frEnv_match hst hfr2
  have r3 : ∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X24, .X26, .X28], s3.data.regs.getXReg r =
      m2.regs.getXReg r := regs_of hm2 hm3 (by decide)
  have hb3 : Base m0 s3.data := hb2.of_regs hfr3 fun r hr ↦ r3 r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl <;> simp)
  have e28 : (m2.regs.getXReg .X28).toBitVec.toNat = rw := by
    rw [hcs .X28 rfl, r1 .X28 (by simp)]; exact x28
  simp only [PcOk] at hpc3
  rcases hrr : rdRows B rw n c5 with _ | ⟨rows, c6⟩
  · rw [hrr] at hpost'
    have hc := rows_cond (frEnv m0 m2) (x0 := 2) (by
      simp only [Env.ofMachine_regs]; rw [x0_bv hpost']; rfl) (.inr (.inr rfl))
    rw [hc] at hpc3
    simp only [true_or, decide_true, ↓reduceIte] at hpc3
    exact .done _ (.inl ⟨hpc3.trans (hp.label (j := NativeRustcVmArm.Vm.PhaseM.b18Offset) NativeRustcVmArm.Vm.PhaseM.label_12_at), hb3, by rw [hmod, ← hn, hrr]⟩)
  rw [hrr] at hpost'
  obtain ⟨hflag, hlv, hrd2⟩ := hpost'
  have hmod' : phaseM B c = if 0 < rw ∧ ∀ r ∈ rows, r.getD 0 0 = 0 then none
      else climbFin B qs height lw rows c6 := by
    rw [hmod, ← hn, hrr]
  have hfv : m2.regs.X0 = 0 ∨ m2.regs.X0 = 1 := by
    rw [hflag]; split <;> simp
  have hc := rows_cond (frEnv m0 m2) (x0 := m2.regs.X0.toBitVec) rfl (by
    rcases hfv with h | h <;> rw [h] <;> simp)
  rw [hc] at hpc3
  obtain ⟨hlen, hrw⟩ := rdRows_length (B := B) rw n hrr
  by_cases hz : 0 < rw ∧ ∀ r ∈ rows, r.getD 0 0 = 0
  · have : decide (m2.regs.X0.toBitVec = 2 ∨ ((frEnv m0 m2).regs .X28).toNat ≠ 0 ∧
        m2.regs.X0.toBitVec = 1) = true := by
      rw [decide_eq_true_iff]
      right
      refine ⟨by simp only [Env.ofMachine_regs]; omega, ?_⟩
      rw [hflag]
      split
      · rfl
      · next hn' => exact absurd hz.2 hn'
    simp only [this, ↓reduceIte] at hpc3
    refine .done _ (.inl ⟨hpc3.trans (hp.label (j := NativeRustcVmArm.Vm.PhaseM.b18Offset) NativeRustcVmArm.Vm.PhaseM.label_12_at), hb3, ?_⟩)
    rw [hmod']
    split
    · rfl
    · contradiction
  have : decide (m2.regs.X0.toBitVec = 2 ∨ ((frEnv m0 m2).regs .X28).toNat ≠ 0 ∧
      m2.regs.X0.toBitVec = 1) = false := by
    rw [decide_eq_false_iff_not]
    rintro (h2 | ⟨h28, h1⟩)
    · rcases hfv with h | h <;> rw [h] at h2 <;> exact absurd h2 (by decide)
    · simp only [Env.ofMachine_regs] at h28
      apply hz
      refine ⟨by omega, ?_⟩
      by_contra hn'
      rw [hflag] at h1
      split at h1
      · next hy => exact hn' hy
      · exact absurd h1 (by decide)
  simp only [this, Bool.false_eq_true, ↓reduceIte] at hpc3
  have hd23 : s3.data.dmem = m2.dmem := hd3
  have rr : ∀ r ∈ [XReg.X21, .X24, .X26], s3.data.regs.getXReg r = st.data.regs.getXReg r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      rw [r3 _ (by simp), hcs _ rfl, r1 _ (by simp)]
  refine .done _ (.inr ⟨rows, c6, hpc3.trans (congrArg _ rfl), hb3, by
    rw [hmod']
    split
    · contradiction
    · rfl, hql,
    hc0, hcnt, hqlt, h32, h64, hps0, hps256, hlen, fun r hr ↦ by rw [hrw r hr]; exact hrl,
    by rw [rr .X21 (by simp)]; exact x21, by rw [rr .X24 (by simp)]; exact x24,
    by rw [rr .X26 (by simp)]; exact x26, ?_, ?_, ?_, ?_, ?_, ?_, by rw [hd23]; exact hrd2⟩)
  · rw [hd23]; exact FW.call G hfr1 hNs hsc (by omega) (.inr (by omega)) (by omega) f56'
  · rw [hd23]; exact FW.call G hfr1 hNs hsc (by omega) (.inr (by omega)) (by omega) f48'
  · rw [hd23]; exact FW.call G hfr1 hNs hsc (by omega) (.inr (by omega)) (by omega) f40
  · rw [hd23]
    exact G.keep_wa hs2' (by rw [workBytes_eq]; omega) hqW1 (fun q hq ↦ hq) (by
        intro p hp; simp only [List.mem_singleton] at hp; subst hp
        refine ⟨hon, .inr ?_⟩; omega)
  · rw [hd23]
    exact G.keep_wa hs2' (by rw [workBytes_eq]; omega) hpW1 (fun q hq ↦ hq) (by
        intro p hp; simp only [List.mem_singleton] at hp; subst hp
        refine ⟨hon, .inr ?_⟩; omega)
  · rw [hd23]; exact hlv

end

end NativeRustcVmArm.Wire.PhaseM
