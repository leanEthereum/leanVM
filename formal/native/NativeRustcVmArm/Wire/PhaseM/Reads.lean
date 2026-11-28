module

public import NativeRustcVmArm.Code.Vm.ReaderLe.Names
public import NativeRustcVmArm.Wire.PhaseM.Steps

/-!
# `phase_m`: the six reads

From the entry: the prologue and the query count (`b0`, `b1`), the queries into the working area
(`b2` to `b6`, `qloop`), the height, the leaf width (kept at the frame's byte 56) and the row
width (`b7` to `b14`), to the head of the sort (`SortSt`, the model's phase now `tail` of what was
read) or to `None`.
-/

namespace NativeRustcVmArm.Wire.PhaseM

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt InAny Region)
open NativeRustcVmArm.Vm.PhaseM
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

@[expose] public section

/-- **At the sort's head**, query `i`: the reads done, the queries at the working area's start,
the distinct positions of the first `i` at its byte 2048. -/
structure SortSt [Host] (m0 : MachineData) (bp : BitVec 64) (B : List UInt8) (c k : Nat)
    (count : Nat) (qs : List Nat) (height lw rw c5 i : Nat) (st : MachineState) : Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.PhaseM.b15Offset)
  base : Base m0 st.data
  model : phaseM B c = tail B qs height lw rw c5
  len : qs.length = count
  cnt0 : 0 < count
  cnt : count ≤ 256
  qlt : ∀ q ∈ qs, q < 2 ^ 32
  hlt : height < 2 ^ 32
  lwlt : lw < 2 ^ 32
  rwlt : rw < 2 ^ 32
  x21 : (st.data.regs.getXReg .X21).toNat = count
  x24 : (st.data.regs.getXReg .X24).toNat = height
  x27 : (st.data.regs.getXReg .X27).toNat = 8 * count
  x28 : (st.data.regs.getXReg .X28).toNat = rw
  x23 : (st.data.regs.getXReg .X23).toNat = 8 * i
  x26 : (st.data.regs.getXReg .X26).toNat = (sortD (qs.take i)).length
  ilt : i < count
  f56 : FW m0 st.data.dmem 56 lw.toUInt64
  f48 : FW m0 st.data.dmem 48 (UInt64.ofBitVec (wa m0 2048))
  qsW : WordsAt st.data.dmem (wa m0 0) (qs.map Nat.toUInt64)
  psW : WordsAt st.data.dmem (wa m0 2048) ((sortD (qs.take i)).map Nat.toUInt64)
  rd : ReaderAt st.data.dmem (rdr m0) bp B c5

/-- After the queries. -/
structure At30 [Host] (m0 : MachineData) (bp : BitVec 64) (B : List UInt8) (c k : Nat)
    (count : Nat) (qs : List Nat) (c2 : Nat) (st : MachineState) : Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.PhaseM.b7Offset)
  base : Base m0 st.data
  x21 : (st.data.regs.getXReg .X21).toNat = count
  x27 : (st.data.regs.getXReg .X27).toNat = 8 * count
  h1 : rdU32 B c = some (count, c + 4)
  cnt : count ≤ 256
  hqs : rdU32s B count (c + 4) = some (qs, c2)
  qsW : WordsAt st.data.dmem (wa m0 0) (qs.map Nat.toUInt64)
  rd : ReaderAt st.data.dmem (rdr m0) bp B c2

/-- The queries' loop, query `i`. -/
structure AtQ [Host] (m0 : MachineData) (bp : BitVec 64) (B : List UInt8) (c k : Nat)
    (count i : Nat) (st : MachineState) : Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.PhaseM.b4Offset)
  base : Base m0 st.data
  x21 : (st.data.regs.getXReg .X21).toNat = count
  x27 : (st.data.regs.getXReg .X27).toNat = 8 * count
  x23 : (st.data.regs.getXReg .X23).toNat = 8 * (count - i)
  x24 : (st.data.regs.getXReg .X24).toBitVec = wa m0 (8 * i)
  h1 : rdU32 B c = some (count, c + 4)
  cnt : count ≤ 256
  ilt : i < count
  qs : ∃ qs, rdU32s B i (c + 4) = some (qs, c + 4 + 4 * i) ∧
    WordsAt st.data.dmem (wa m0 0) (qs.map Nat.toUInt64) ∧
    ReaderAt st.data.dmem (rdr m0) bp B (c + 4 + 4 * i)

end

public section

theorem rdU32_c {B : List UInt8} {c v c' : Nat} (h : rdU32 B c = some (v, c')) : c' = c + 4 := by
  unfold rdU32 at h
  split at h
  · cases h; rfl
  · cases h

theorem read4_cases {r bp : BitVec 64} {B : List UInt8} {c : Nat} {m : MachineData}
    (h : Read4 r bp B c m) :
    (rdU32 B c = none ∧ m.regs.X0 = 0) ∨
      ∃ v, rdU32 B c = some (v, c + 4) ∧ m.regs.X0 = 1 ∧ m.regs.X1.toNat = v ∧
        ReaderAt m.dmem r bp B (c + 4) := by
  unfold Read4 at h
  rcases h1 : rdU32 B c with _ | ⟨v, c'⟩
  · rw [h1] at h; exact .inl ⟨rfl, h⟩
  · rw [h1] at h
    have := rdU32_c h1
    subst this
    exact .inr ⟨v, rfl, h⟩

theorem bit0_zero : (Sym.low .W32 (0 : UInt64).toBitVec).getLsbD 0 = false := by decide
theorem bit0_one : (Sym.low .W32 (1 : UInt64).toBitVec).getLsbD 0 = true := by decide

theorem eq_lit (x : BitVec 64) (n : Nat) (hn : n < 2 ^ 64) :
    CmpOp.apply .eq .W64 x (BitVec.ofNat 64 n) = decide (x.toNat = n) := by
  rw [eq_apply, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

theorem wordsAt_snoc {d : Mem 64} {a : BitVec 64} {ws : List UInt64} {v : UInt64}
    (h : WordsAt d a ws) (hv : WordAt d (a + BitVec.ofNat 64 (8 * ws.length)) v) :
    WordsAt d a (ws ++ [v]) :=
  NativeRustcVm.wordsAt_append_iff.mpr ⟨h, NativeRustcVm.wordsAt_singleton_iff.mpr hv⟩

/-- A register's word, as the executor writes it. -/
theorem wordAt_reg {d : Mem 64} {a x : BitVec 64}
    (h : BytesAt d a ((List.range 8).map (byteOf x))) : WordAt d a (UInt64.ofBitVec x) := by
  rw [byteOf_range] at h; exact h

theorem ofBitVec_eq {x : BitVec 64} {n : Nat} (h : x.toNat = n) :
    UInt64.ofBitVec x = n.toUInt64 := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_ofBitVec, h, toNat_toUInt64_of_lt (by have := x.isLt; omega)]

theorem sub_lit {x : BitVec 64} {n : Nat} (h : n ≤ x.toNat) :
    (BinOp.apply .sub .W64 x (BitVec.ofNat 64 n)).toNat = x.toNat - n := by
  simp only [BinOp.apply, Sym.low_W64, Sym.ext_W64, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := x.isLt
  rw [Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega)]
  omega

theorem add_lit (x : BitVec 64) (n : Nat) :
    BinOp.apply .add .W64 x (BitVec.ofNat 64 n) = x + BitVec.ofNat 64 n := by
  simp [BinOp.apply]

variable {m0 : MachineData} {bp : BitVec 64} {B : List UInt8} {c : Nat} [Host] {k : Nat}

/-- **The queries' loop.** -/
theorem qloop (hp : Placed code k) (G : Geo m0 bp B)
    (hle : Spec (Labels.label NativeRustcVmArm.Vm.ReaderLe.entryLabel) ReaderLePre ReaderLePost) {count i : Nat}
    {st : MachineState} (h : AtQ m0 bp B c k count i st) :
    Eventually (step1 Host.exe) (fun st' ↦ AtNone m0 B c k st' ∨
      ∃ qs c2, At30 m0 bp B c k count qs c2 st') st := by
  refine Sym.loop (tr := step1 Host.exe)
    (fun n st ↦ ∃ i, n = count - i ∧ AtQ m0 bp B c k count i st)
    (fun _ st ⟨i, hn, h⟩ ↦ ?_) ⟨i, rfl, h⟩
  obtain ⟨hpc, hb, x21, x27, x23, x24, h1, hcnt, hi, qs, hqs, hqW, hrd⟩ := h
  have hst := G.st
  have hm := frEnv_match hst hb.fr
  -- `b4`: the call
  refine blk hp b4_in_code (by simp [b4]) run_b4 rfl rfl hst hb.fr hpc fun s1 hfr1 hd1 hm1 hpc1 ↦ ?_
  have r1 := regs_of hm hm1 (rs := [.X19, .X20, .X21, .X22, .X23, .X24, .X27]) (by decide)
  have hb1 : Base m0 s1.data := hb.of_regs hfr1 fun x hx ↦ r1 x (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp)
  have hx0 : s1.data.regs.X0.toBitVec = rdr m0 := (hm1.regs .X0 _ rfl).trans hb.x22
  have hx1 : s1.data.regs.X1.toNat = 4 := by
    show (s1.data.regs.getXReg .X1).toBitVec.toNat = 4
    rw [hm1.regs .X1 _ rfl]; rfl
  refine le4_call hle G hb1.fr (by rw [hd1]; exact hrd) hx0 hx1 hpc1 fun m2 hfr2 hcs hs2 hrd2 ↦ ?_
  have hb2 := hb1.call hfr2 hcs
  have e21 := hcs .X21 rfl; have e23 := hcs .X23 rfl; have e24 := hcs .X24 rfl
  have e27 := hcs .X27 rfl
  -- `b5`: the read's flag
  refine blk hp b5_in_code (by simp [b5]) run_b5 rfl rfl hst hfr2 rfl fun s3 hfr3 hd3 hm3 hpc3 ↦ ?_
  have hm2 := frEnv_match hst hfr2
  have r3 := regs_of hm2 hm3 (rs := [.X0, .X1, .X19, .X20, .X21, .X22, .X23, .X24, .X27])
    (by decide)
  simp only [PcOk] at hpc3
  rcases read4_cases hrd2 with ⟨hn, h0⟩ | ⟨v, hv, h0, hx1', hrd3⟩
  · -- no query: `None`
    have hcz : (SBool.bit .W32 (.reg .X0) 0).not.eval (frEnv m0 m2) = true := by
      simp only [SBool.eval, Sym.eval, Env.ofMachine_regs]
      rw [show m2.regs.getXReg .X0 = m2.regs.X0 from rfl, h0, bit0_zero]; rfl
    simp only [hcz, ↓reduceIte] at hpc3
    rw [hp.label (j := NativeRustcVmArm.Vm.PhaseM.b18Offset) NativeRustcVmArm.Vm.PhaseM.label_12_at] at hpc3
    refine .done _ (.inl (.inl ⟨hpc3, hb2.of_regs hfr3 fun x hx ↦ r3 x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> simp), ?_⟩))
    rw [phaseM_eq, h1]
    simp only [show ¬ wireMaxQueries < count from by unfold wireMaxQueries; omega, ↓reduceIte]
    have hc := (rdU32s_len B i (c + 4) hqs).2
    rw [show count = i + 1 + (count - i - 1) by omega, rdU32s_none B i (c + 4) _ hqs
      (by rw [show c + 4 + 4 * i = c + 4 + 4 * i from rfl]; exact hn)]
  have hcz : (SBool.bit .W32 (.reg .X0) 0).not.eval (frEnv m0 m2) = false := by
    simp only [SBool.eval, Sym.eval, Env.ofMachine_regs]
    rw [show m2.regs.getXReg .X0 = m2.regs.X0 from rfl, h0, bit0_one]; rfl
  simp only [hcz, Bool.false_eq_true, ↓reduceIte] at hpc3
  -- `b6`: the store
  have hon : 8 * i + 8 ≤ workBytes := by rw [workBytes_eq]; omega
  have hwf := G.al_wf (o := 8 * i) (n := 8) hon (by omega) hfr3
  have x24' : (s3.data.regs.getXReg .X24).toBitVec = wa m0 (8 * i) := by
    rw [r3 .X24 (by simp), e24, r1 .X24 (by simp)]; exact x24
  have hmA := G.al_match (o := 8 * i) (n := 8) (a := .reg .X24) (k := 0) hfr3
    (by simp only [Sym.eval, Env.ofMachine_regs]; rw [x24']; simp)
  refine exec_at (infix_of b6_in_code (by simp [b6]) hp) run_b6 hwf hpc3 hmA
    fun s4 hm4 hpc4 ↦ ?_
  have r4 := regs_of hmA hm4 (rs := [.X19, .X20, .X21, .X22, .X27]) (by decide)
  have hfr4 : Frm m0 s4.data := Fr.ofBlockW hfr3 hmA hm4 hwf rfl rfl
    (fun x hx ↦ absurd hx (by simp)) rfl (by omega) hst.2.1 (by decide) fun w hw ↦ by
      simp only [List.mem_singleton] at hw
      subst hw
      right
      refine ⟨by decide, fun b sz hb ↦ ?_⟩
      simp only [Env.ofMachine_regions, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      refine ⟨by decide, fun j hj ↦ .inr (.inr ?_)⟩
      rw [NativeRustcVm.addr_add_add]
      have := G.wNw
      exact NativeRustcVm.inRange_add (by omega) (by omega)
  have hb4 : Base m0 s4.data := hb2.of_regs hfr4 fun x hx ↦ by
    have hx' : x = .X19 ∨ x = .X20 ∨ x = .X22 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; exact hx
    rw [r4 x (by rcases hx' with rfl | rfl | rfl <;> simp),
      r3 x (by rcases hx' with rfl | rfl | rfl <;> simp)]
  have hs4 := Match.sameOutside_in hm4 hwf (r0 := 1) (o := 0) (n := 8) rfl (by omega)
    (by decide)
  rw [NativeRustcVm.addr_add_zero] at hs4
  have hd4 : s3.data.dmem = m2.dmem := hd3
  have hqW4 : WordsAt s4.data.dmem (wa m0 0) ((qs ++ [v]).map Nat.toUInt64) := by
    rw [List.map_append]
    have hlen := (rdU32s_len B i (c + 4) hqs).1
    refine wordsAt_snoc ?_ ?_
    · have hqW2 : WordsAt m2.dmem (wa m0 0) (qs.map Nat.toUInt64) :=
        G.keep_wa (L := []) hs2
          (by rw [NativeRustcVm.length_wordsBytes, List.length_map, hlen, workBytes_eq]; omega)
          (by rw [hd1]; exact hqW) (fun q hq ↦ .inr (.inl hq)) (by simp)
      rw [← hd4] at hqW2
      exact G.keep_wa (L := [(8 * i, 8)]) hs4
        (by rw [NativeRustcVm.length_wordsBytes, List.length_map, hlen, workBytes_eq]; omega) hqW2
        (fun q hq ↦ .inr (.inr (.inr ⟨_, List.mem_singleton_self _, hq⟩)))
        (by
          intro p hp
          simp only [List.mem_singleton] at hp
          subst hp
          rw [NativeRustcVm.length_wordsBytes, List.length_map, hlen, workBytes_eq]
          omega)
    · have hw := hm4.bytesAt_write (r := 1) (o := 0) (n := 8) (b := wa m0 (8 * i)) (sz := 8) rfl
        (by omega) (v := .reg .X1) (by decide)
      rw [NativeRustcVm.addr_add_zero] at hw
      have := wordAt_reg hw
      simp only [Sym.eval, Env.ofMachine_regs] at this
      rw [show (s3.data.regs.getXReg .X1).toBitVec = m2.regs.X1.toBitVec from
        (r3 .X1 (by simp)).symm ▸ rfl, ofBitVec_eq hx1'] at this
      simp only [List.length_map, hlen, NativeRustcVm.addr_add_add, Nat.zero_add]
      exact this
  have hrd4 : ReaderAt s4.data.dmem (rdr m0) bp B (c + 4 + 4 * (i + 1)) := by
    have := hrd3
    rw [← hd4] at this
    rw [show c + 4 + 4 * (i + 1) = c + 4 + 4 * i + 4 by omega]
    refine G.rgeo.reader_frame rfl this (NativeRustcVm.SameOutside.mono hs4 fun q hq ↦ .inr ?_)
    · right
      have := G.wNw
      exact NativeRustcVm.InRange.of_sub hq G.wOk.2 (by omega)
  have hqs' : rdU32s B (i + 1) (c + 4) = some (qs ++ [v], c + 4 + 4 * (i + 1)) := by
    rw [show c + 4 + 4 * (i + 1) = c + 4 + 4 * i + 4 by omega]
    exact rdU32s_snoc B i (c + 4) hqs hv
  have x23v : (s3.data.regs.getXReg .X23).toNat = 8 * (count - i) := by
    rw [r3 .X23 (by simp), e23, r1 .X23 (by simp)]; exact x23
  have hcond : (SBool.cmp .eq .W64 (.reg .X23) (.lit 8)).not.eval
      (alEnv m0 s3.data (wa m0 (8 * i)) 8) = !decide (i + 1 = count) := by
    simp only [SBool.eval, Sym.eval, Env.ofMachine_regs]
    rw [eq_lit _ 8 (by decide), show (s3.data.regs.getXReg .X23).toBitVec.toNat = _ from x23v]
    by_cases hh : i + 1 = count
    · simp only [hh, decide_true]; rw [decide_eq_true (by omega)]
    · simp only [hh, decide_false]; rw [decide_eq_false (by omega)]
  simp only [PcOk, hcond] at hpc4
  by_cases hlast : i + 1 = count
  · simp only [hlast, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc4
    refine .done _ (.inl (.inr ⟨qs ++ [v], c + 4 + 4 * (i + 1),
      ⟨?_, hb4, ?_, ?_, h1, hcnt, ?_, hqW4, hrd4⟩⟩))
    · rw [hpc4]; rfl
    · rw [r4 .X21 (by simp), r3 .X21 (by simp), e21, r1 .X21 (by simp)]; exact x21
    · rw [r4 .X27 (by simp), r3 .X27 (by simp), e27, r1 .X27 (by simp)]; exact x27
    · rw [← hlast]; exact hqs'
  · simp only [hlast, decide_false, Bool.not_false, ↓reduceIte] at hpc4
    refine .done _ (.inr ⟨count - (i + 1), by omega, i + 1, rfl, ⟨?_, hb4, ?_, ?_, ?_, ?_, h1, hcnt,
      by omega, qs ++ [v], hqs', hqW4, hrd4⟩⟩)
    · rw [hpc4]; exact hp.label (j := NativeRustcVmArm.Vm.PhaseM.b4Offset) NativeRustcVmArm.Vm.PhaseM.label_3_at
    · rw [r4 .X21 (by simp), r3 .X21 (by simp), e21, r1 .X21 (by simp)]; exact x21
    · rw [r4 .X27 (by simp), r3 .X27 (by simp), e27, r1 .X27 (by simp)]; exact x27
    · show (s4.data.regs.getXReg .X23).toBitVec.toNat = _
      rw [hm4.regs .X23 _ rfl]
      simp only [Sym.eval, Env.ofMachine_regs]
      have x23b : (s3.data.regs.getXReg .X23).toBitVec.toNat = 8 * (count - i) := x23v
      rw [sub_lit (by rw [x23b]; omega), x23b]
      omega
    · rw [hm4.regs .X24 _ rfl]
      simp only [Sym.eval, Env.ofMachine_regs]
      rw [x24', add_lit, NativeRustcVm.addr_add_add]
      congr 2

end

end NativeRustcVmArm.Wire.PhaseM
