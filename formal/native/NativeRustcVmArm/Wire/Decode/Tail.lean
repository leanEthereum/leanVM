module

public import NativeRustcVmArm.Code.Vm.PhaseM.Names
public import NativeRustcVmArm.Code.Vm.ReaderLe.Names
public import NativeRustcVmArm.Wire.Decode.Head

/-!
# `decode` from the stream's count to the phases

From `Mid` (`b5`): the stream's count stored at the decoded area's word `0` and the phase count
read (`Reader::le`), its bound (`b6`), the stream's end in the area (`b7`), the phase count
stored there and the loop's set-up (`b8`): the loop (`loop_spec`) from no phase read.
-/

namespace NativeRustcVmArm.Wire.Decode

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Wire NativeVm NativeVm.Wire
open NativeVm.Model
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt InAny Region)
open NativeRustcVmArm.Vm.Decode
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

@[expose] public section

/-- **At the stream's end** (`b7`): the phase count `p` read, at most eight, to the cursor `cs`;
the stream's count and words stored. -/
structure At7 [Host] (k0 : Nat) (m0 : MachineData) (B : List UInt8) (n : Nat) (ws : List K)
    (c1 p cs : Nat) (st : MachineState) : Prop where
  pc : st.pc = Host.addrOf (k0 + NativeRustcVmArm.Vm.Decode.b7Offset)
  fr : Frm m0 st.data
  x1 : (st.data.regs.getXReg .X1).toNat = p
  x19 : st.data.regs.getXReg .X19 = m0.regs.X4
  x20 : st.data.regs.getXReg .X20 = m0.regs.X1
  x21 : st.data.regs.getXReg .X21 = m0.regs.X2
  x22 : st.data.regs.getXReg .X22 = m0.regs.X3
  p_le : p ≤ wireMaxPhases
  r3 : rdU32 B c1 = some (p, cs)
  rd : ReaderAt st.data.dmem (rdr m0) (bpA m0) B cs
  cnt : WordAt st.data.dmem (dw m0 0) n.toUInt64
  words : WordsAt st.data.dmem (dw m0 1) (ws.map K.lane)

/-- **At the phase count's store** (`b8`): the stream's end in X8. -/
structure At8 [Host] (k0 : Nat) (m0 : MachineData) (B : List UInt8) (n : Nat) (ws : List K)
    (c1 p cs : Nat) (st : MachineState) : Prop where
  pc : st.pc = Host.addrOf (k0 + NativeRustcVmArm.Vm.Decode.b8Offset)
  fr : Frm m0 st.data
  x1 : (st.data.regs.getXReg .X1).toNat = p
  x8 : (st.data.regs.getXReg .X8).toBitVec.toNat = streamEnd (Ln m0)
  x19 : st.data.regs.getXReg .X19 = m0.regs.X4
  x20 : st.data.regs.getXReg .X20 = m0.regs.X1
  x21 : st.data.regs.getXReg .X21 = m0.regs.X2
  x22 : st.data.regs.getXReg .X22 = m0.regs.X3
  p_le : p ≤ wireMaxPhases
  r3 : rdU32 B c1 = some (p, cs)
  rd : ReaderAt st.data.dmem (rdr m0) (bpA m0) B cs
  cnt : WordAt st.data.dmem (dw m0 0) n.toUInt64
  words : WordsAt st.data.dmem (dw m0 1) (ws.map K.lane)

end

public section

variable {m0 : MachineData} {B : List UInt8}

theorem and_zero_cmp (y : BitVec 64) :
    CmpOp.apply .eq .W32 (BinOp.apply .and .W32 (0 : UInt64).toBitVec y) (BitVec.ofNat 64 0) =
      true := by
  simp only [CmpOp.apply, BinOp.apply, Sym.low_ext]
  simp

theorem dec_eq {n : Nat} {ws : List K} {c1 p cs : Nat} (h1 : rdU32 B 0 = some (n, 4))
    (h2 : rdWords B (2 * n) 4 = some (ws, c1)) (h3 : rdU32 B c1 = some (p, cs))
    (hp : p ≤ wireMaxPhases) :
    decodeM B = match phasesM B p cs with
      | none => none
      | some (ps, c) => if c ≠ B.length then none else some (streamOf n ws, ps) := by
  rw [decodeM_eq', h1]
  dsimp only
  rw [h2]
  dsimp only
  rw [h3]
  dsimp only
  split
  · omega
  · rfl

theorem decode_none_3 {n : Nat} {ws : List K} {c1 : Nat} (h1 : rdU32 B 0 = some (n, 4))
    (h2 : rdWords B (2 * n) 4 = some (ws, c1)) (h3 : rdU32 B c1 = none) : decodeM B = none := by
  rw [decodeM_eq', h1]
  dsimp only
  rw [h2]
  dsimp only
  rw [h3]

theorem decode_none_4 {n : Nat} {ws : List K} {c1 p cs : Nat} (h1 : rdU32 B 0 = some (n, 4))
    (h2 : rdWords B (2 * n) 4 = some (ws, c1)) (h3 : rdU32 B c1 = some (p, cs))
    (hp : wireMaxPhases < p) : decodeM B = none := by
  rw [decodeM_eq', h1]
  dsimp only
  rw [h2]
  dsimp only
  rw [h3]
  dsimp only
  split
  · rfl
  · omega

theorem shl3 (x : BitVec 64) :
    UnOp.apply (.shift .LSL 3) .W64 x = BitVec.ofNat 64 (8 * x.toNat) := by
  simp only [UnOp.apply, Sym.low_W64, Sym.ext_W64, shiftW]
  apply BitVec.eq_of_toNat_eq
  have e : MemWidth.W64.bits = 64 := rfl
  simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat, e]
  omega

/-- The first phase's address less the phase's bytes, as `b8` computes it. -/
theorem x21_eq (d : BitVec 64) (se : Nat) :
    BinOp.apply .sub .W64 (BinOp.apply .sub .W64 (BinOp.apply .add .W64 d
      (UnOp.apply (.shift .LSL 3) .W64 (BitVec.ofNat 64 se))) (BitVec.ofNat 64 393216))
      (BitVec.ofNat 64 2064) + BitVec.ofNat 64 phaseBytes = d + BitVec.ofNat 64 (8 * (se + 1)) := by
  rw [shl3]
  simp only [BinOp.apply, Sym.low_W64, Sym.ext_W64, phaseBytes_eq]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

section
variable [Labels]

theorem Geo.dw_wf (G : Geo m0 B) {m : MachineData} (hfr : Frm m0 m) {i : Nat}
    (hi : i < lenW m0) : (dwEnv m0 m i).WF := by
  have hst := G.st
  have hd := G.dw_toNat hi
  have hD := G.dNw
  have hbt := G.base_toNat (F := 96) (by omega)
  have hb' := G.base_toNat (F := 1280) le_rfl
  have hsp := G.sp
  have sD := G.sD
  unfold NativeRustcVm.Apart at sD
  refine Env.wf_of ⟨⟨fun j hj ↦ hfr.kept _ (Ring.frame_mapped hst (by omega) j hj),
    Ring.base_noWrap (by omega)⟩, ⟨fun j hj ↦ ?_, ?_⟩, trivial⟩ (List.pairwise_pair.mpr ?_)
  · rw [NativeRustcVm.addr_add_add]
    exact hfr.kept _ (G.dOk.1 _ (by show 8 * i + j < 8 * lenW m0; omega))
  · show (dw m0 i).toNat + 8 ≤ 2 ^ 64
    omega
  · show (base m0 96).toNat + 96 ≤ (dw m0 i).toNat ∨ (dw m0 i).toNat + 8 ≤ (base m0 96).toNat
    omega

theorem Geo.dw_match (G : Geo m0 B) {m : MachineData} (hfr : Frm m0 m) {i : Nat}
    {a : Sym} (ha : a.eval (dwEnv m0 m i) = dw m0 i + BitVec.ofInt 64 0) :
    Match (dwEnv m0 m i) (init [(96, true), (8, false)] (.ptr 0 0) [] [] [] [(a, 1, 0)]) m :=
  match_ofMachine ⟨rfl, fun _ ↦ base_aligned G.st, rfl, fun h ↦ absurd h (by decide), trivial⟩
    (by rw [hfr.sp]; simp [Sym.eval]) trivial trivial trivial ⟨ha, trivial⟩

/-- A word of the decoded area is in the outputs. -/
theorem Geo.w_dw (G : Geo m0 B) {i : Nat} (hi : i < lenW m0) {j : Nat} (hj : j < 8) :
    W m0 (dw m0 i + BitVec.ofNat 64 j) := by
  left
  have hd := G.dw_toNat hi
  have hD := G.dNw
  rw [Sym.inRange_iff hD, NativeRustcVm.toNat_add_ofNat (by omega), hd]
  omega

/-- A change in a word of the decoded area keeps the reader. -/
theorem Geo.reader_dw (G : Geo m0 B) {i : Nat} (hi : i < lenW m0) {d d' : Mem 64} {c : Nat}
    (h : ReaderAt d (rdr m0) (bpA m0) B c) (hs : SameOutside d d' (InRange (dw m0 i) 8)) :
    ReaderAt d' (rdr m0) (bpA m0) B c := by
  refine G.reader_keep h hs fun q hq ↦ G.notReader (.inl ?_)
  exact NativeRustcVm.InRange.of_sub (o := 8 * i) hq G.dNw (by omega)

end

variable [Host] {k0 : Nat}

/-- **From the stream's count to the phase count's bound.** -/
theorem tail_a (hp : Placed code k0) (G : Geo m0 B)
    (hle : Spec (Labels.label NativeRustcVmArm.Vm.ReaderLe.entryLabel) ReaderLePre ReaderLePost) {n : Nat} {ws : List K}
    {c1 : Nat} {st : MachineState} (hM : Mid k0 m0 B n ws c1 st) :
    Eventually (step1 Host.exe) (fun s ↦ Res m0 B s ∨ ∃ p cs, At7 k0 m0 B n ws c1 p cs s) st := by
  obtain ⟨hpc, hfr, x19, x20, x21, x22, x23, h1, h2, hR, hws⟩ := hM
  have hst := G.st
  have hdLe := G.dLe
  have hlen := G.len
  have hL := G.l32
  have hdN := G.dNw
  have hl : 0 < Ln m0 := by have := (rdU32_c h1).2; omega
  obtain ⟨hlt, hnS⟩ := words_lt h2 (len := lenW m0) (by rw [hlen]; exact hdLe)
  rw [hlen] at hnS
  obtain ⟨-, hc1, hwsE⟩ := rdWords_c h2
  have hwsl : ws.length = 2 * n := by rw [hwsE]; simp
  have hdg := decodedWords_ge (Ln m0)
  rw [phaseWords_eq] at hdg
  have hse : 1 + 2 * n ≤ streamEnd (Ln m0) := by unfold streamEnd; omega
  have l8 := NativeRustcVm.length_wordBytes
  have lw : ((ws.map K.lane).flatMap NativeRustcVm.wordBytes).length = 8 * (2 * n) := by
    rw [NativeRustcVm.length_wordsBytes, List.length_map, hwsl]
  -- `b5`: the stream's count stored, `Reader::le`'s call
  have hwf := G.dw_wf hfr (i := 0) (by omega)
  have hm := G.dw_match hfr (i := 0) (a := .reg .X21) (by
    simp only [Sym.eval, Env.ofMachine_regs, x21, BitVec.ofInt_ofNat, NativeRustcVm.addr_add_zero]
    show _ = decA m0 + BitVec.ofNat 64 (8 * 0)
    rw [Nat.mul_zero, NativeRustcVm.addr_add_zero])
  refine exec_at (infix_of b5_in_code (by simp [b5]) hp) run_b5 hwf hpc hm fun s1 hm1 hpc1 ↦ ?_
  have hfr1 : Frm m0 s1.data := Fr.ofBlockW hfr hm hm1 hwf rfl rfl (keepOk (by decide)) rfl
    (by omega) G.sp (by decide) (by
      intro w hw
      simp only [List.mem_singleton] at hw
      subst hw
      refine .inr ⟨by decide, fun b sz hb ↦ ?_⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
      exact ⟨by decide, fun j hj ↦ G.w_dw (by omega) hj⟩)
  have hs1 := Match.sameOutside_in hm1 hwf (r0 := 1) (o := 0) (n := 8) rfl (by omega) (by decide)
  rw [NativeRustcVm.addr_add_zero] at hs1
  have hcnt : WordAt s1.data.dmem (dw m0 0) n.toUInt64 := by
    have w := wordAt_reg (hm1.bytesAt_write (r := 1) (o := 0) (n := 8) (b := dw m0 0) (sz := 8)
      rfl (by omega) (v := .reg .X23) (by decide))
    rw [NativeRustcVm.addr_add_zero] at w
    have e : UInt64.ofBitVec ((Sym.reg .X23).eval (dwEnv m0 st.data 0)) = n.toUInt64 := by
      apply UInt64.toNat_inj.mp
      rw [toNat_toUInt64_of_lt (by omega)]
      exact x23
    rwa [e] at w
  have hR1 := G.reader_dw (i := 0) (by omega) hR hs1
  have hws1 : WordsAt s1.data.dmem (dw m0 1) (ws.map K.lane) :=
    G.keepB (lo := 0) (nb := 8) hs1 (fun q hq ↦ .inr hq) (by omega) hws (by rw [lw]; omega)
      (.inl (by omega))
  have k1 : ∀ x ∈ [XReg.X19, .X20, .X21, .X22], s1.data.regs.getXReg x =
      st.data.regs.getXReg x := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> exact Match.reg_eq hm hm1 rfl rfl
  have hx0 : s1.data.regs.X0.toBitVec = rdr m0 := by
    rw [show s1.data.regs.X0 = s1.data.regs.getXReg .X0 from rfl, hm1.regs .X0 _ rfl]
    simp only [Sym.eval, Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
      Option.getD_some, ofInt8]
  have hx1 : s1.data.regs.X1.toNat = 4 := by
    show (s1.data.regs.getXReg .X1).toBitVec.toNat = 4
    rw [hm1.regs .X1 _ rfl]
    rfl
  simp only [PcOk] at hpc1
  refine le4_call hle G hfr1 hR1 hx0 hx1 hpc1 fun m2 hfr2 hcs2 hs2 hr2 ↦ ?_
  have hR2' : ∀ q, InRange (base m0 96 + BitVec.ofNat 64 24) 8 q →
      Out m0 q ∨ InRange (dw m0 0) 0 q := fun q hq ↦ .inl (G.out_frame (by omega) hq)
  have hcnt2 : WordAt m2.dmem (dw m0 0) n.toUInt64 :=
    G.keepB (lo := 0) (nb := 0) hs2 hR2' (by omega) hcnt (by rw [l8]; omega) (.inl (by omega))
  have hws2 : WordsAt m2.dmem (dw m0 1) (ws.map K.lane) :=
    G.keepB (lo := 0) (nb := 0) hs2 hR2' (by omega) hws1 (by rw [lw]; omega) (.inl (by omega))
  have c19 : m2.regs.getXReg .X19 = m0.regs.X4 := by rw [hcs2 .X19 rfl, k1 .X19 (by simp), x19]
  have c20 : m2.regs.getXReg .X20 = m0.regs.X1 := by rw [hcs2 .X20 rfl, k1 .X20 (by simp), x20]
  have c21 : m2.regs.getXReg .X21 = m0.regs.X2 := by rw [hcs2 .X21 rfl, k1 .X21 (by simp), x21]
  have c22 : m2.regs.getXReg .X22 = m0.regs.X3 := by rw [hcs2 .X22 rfl, k1 .X22 (by simp), x22]
  -- `b6`: the phase count's bound
  have hwf2 := frEnv_wf hst hfr2
  have hm2 := frEnv_match hst hfr2
  refine exec_at (infix_of b6_in_code (by simp [b6]) hp) run_b6 hwf2 (congrArg Host.addrOf rfl)
    hm2 fun s3 hm3 hpc3 ↦ ?_
  have hfr3 : Frm m0 s3.data := Fr.ofBlock hfr2 hm2 hm3 hwf2 rfl rfl rfl (keepOk (by decide))
  have hd3 : s3.data.dmem = m2.dmem := hm3.dmem_eq hwf2 rfl
  simp only [PcOk] at hpc3
  unfold Read4 at hr2
  rcases h3 : rdU32 B c1 with _ | ⟨p, cs⟩
  · rw [h3] at hr2
    have hc : (SBool.cmp .eq .W32 (.bin .and .W32 (.reg .X0) (.un .trunc .W32
        (.ite (.not (.cmp .ult .W64 (.reg .X1) (.lit 9))) (.lit 0) (.lit 1)))) (.lit 0)).eval
        (frEnv m0 m2) = true := by
      simp only [SBool.eval, Sym.eval, Env.ofMachine_regs]
      rw [show m2.regs.getXReg .X0 = 0 from hr2]
      exact and_zero_cmp _
    simp only [hc, ↓reduceIte, hp.label (j := NativeRustcVmArm.Vm.Decode.b14Offset) NativeRustcVmArm.Vm.Decode.label_9_at] at hpc3
    exact Eventually.mono (exit14 hp G hpc3 hfr3 (decode_none_3 h1 h2 h3)) fun _ h ↦ .inl h
  rw [h3] at hr2
  obtain ⟨h0, hpv, hR3⟩ := hr2
  have hc : (SBool.cmp .eq .W32 (.bin .and .W32 (.reg .X0) (.un .trunc .W32
      (.ite (.not (.cmp .ult .W64 (.reg .X1) (.lit 9))) (.lit 0) (.lit 1)))) (.lit 0)).eval
      (frEnv m0 m2) = decide (9 ≤ p) := by
    simp only [SBool.eval, Sym.eval, Env.ofMachine_regs, ult_apply]
    rw [show m2.regs.getXReg .X0 = 1 from h0]
    have hp' : (m2.regs.getXReg .X1).toBitVec.toNat = p := hpv
    rw [hp']
    by_cases h9 : p < 9
    · rw [decide_eq_true (by simpa using h9), decide_eq_false (by omega)]
      rfl
    · rw [decide_eq_false (by simpa using h9), decide_eq_true (by omega)]
      rfl
  rw [hc] at hpc3
  by_cases h9 : 9 ≤ p
  · simp only [h9, decide_true, ↓reduceIte, hp.label (j := NativeRustcVmArm.Vm.Decode.b14Offset) NativeRustcVmArm.Vm.Decode.label_9_at] at hpc3
    exact Eventually.mono (exit14 hp G hpc3 hfr3 (decode_none_4 h1 h2 h3
      (by unfold wireMaxPhases; omega))) fun _ h ↦ .inl h
  simp only [h9, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc3
  have hp8 : p ≤ wireMaxPhases := by unfold wireMaxPhases; omega
  have k3 : ∀ x ∈ [XReg.X1, .X19, .X20, .X21, .X22], s3.data.regs.getXReg x =
      m2.regs.getXReg x := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> exact Match.reg_eq hm2 hm3 rfl rfl
  refine .done _ (.inr ⟨p, cs, hpc3.trans (congrArg Host.addrOf rfl), hfr3, ?_, ?_, ?_, ?_, ?_,
    hp8, h3, by rw [hd3]; exact hR3, by rw [hd3]; exact hcnt2, by rw [hd3]; exact hws2⟩)
  · rw [k3 .X1 (by simp)]; exact hpv
  · rw [k3 .X19 (by simp), c19]
  · rw [k3 .X20 (by simp), c20]
  · rw [k3 .X21 (by simp), c21]
  · rw [k3 .X22 (by simp), c22]

/-- **The stream's end** (`b7`). -/
theorem tail_b (hp : Placed code k0) (G : Geo m0 B) {n : Nat} {ws : List K}
    {c1 p cs : Nat} (h1 : rdU32 B 0 = some (n, 4)) (h2 : rdWords B (2 * n) 4 = some (ws, c1))
    {s3 : MachineState} (hA : At7 k0 m0 B n ws c1 p cs s3) :
    Eventually (step1 Host.exe) (At8 k0 m0 B n ws c1 p cs) s3 := by
  obtain ⟨hpc3, hfr3, hpv, a19, a20, a21, a22, hp8, h3, hR3, hcnt3, hws3⟩ := hA
  have hst := G.st
  have hdLe := G.dLe
  have hlen := G.len
  have hL := G.l32
  have hdN := G.dNw
  have hl : 0 < Ln m0 := by have := (rdU32_c h1).2; omega
  obtain ⟨hlt, hnS⟩ := words_lt h2 (len := lenW m0) (by rw [hlen]; exact hdLe)
  rw [hlen] at hnS
  obtain ⟨-, hc1, hwsE⟩ := rdWords_c h2
  have hwsl : ws.length = 2 * n := by rw [hwsE]; simp
  have hdg := decodedWords_ge (Ln m0)
  rw [phaseWords_eq] at hdg
  have hse : 1 + 2 * n ≤ streamEnd (Ln m0) := by unfold streamEnd; omega
  have l8 := NativeRustcVm.length_wordBytes
  have lw : ((ws.map K.lane).flatMap NativeRustcVm.wordBytes).length = 8 * (2 * n) := by
    rw [NativeRustcVm.length_wordsBytes, List.length_map, hwsl]
  have hm3' := frEnv_match hst hfr3
  -- `b7`: the stream's end
  have hwf3 := frEnv_wf hst hfr3
  refine exec_at (infix_of b7_in_code (by simp [b7]) hp) run_b7 hwf3
    (hpc3.trans (congrArg Host.addrOf rfl)) hm3' fun s4 hm4 hpc4 ↦ ?_
  have hfr4 : Frm m0 s4.data := Fr.ofBlock hfr3 hm3' hm4 hwf3 rfl rfl rfl (keepOk (by decide))
  have hd4 : s4.data.dmem = s3.data.dmem := hm4.dmem_eq hwf3 rfl
  simp only [PcOk] at hpc4
  have hseE : (BinOp.apply .orr .W64 (UnOp.apply (.ubfm 3 63) .W64
      (s3.data.regs.getXReg .X20).toBitVec) (BitVec.ofNat 64 1)).toNat = streamEnd (Ln m0) := by
    rw [streamEnd_eval, a20]
    rfl
  have hc4 : (SBool.cmp .ult .W64 (.bin .orr .W64 (.un (.ubfm 3 63) .W64 (.reg .X20)) (.lit 1))
      (.reg .X22)).not.eval (frEnv m0 s3.data) = false := by
    simp only [SBool.eval, Sym.eval, Env.ofMachine_regs, ult_apply, hseE, a22]
    simp only [Bool.not_eq_false', decide_eq_true_eq]
    show streamEnd (Ln m0) < lenW m0
    omega
  simp only [hc4, Bool.false_eq_true, ↓reduceIte] at hpc4
  have k4 : ∀ x ∈ [XReg.X1, .X19, .X20, .X21, .X22], s4.data.regs.getXReg x =
      s3.data.regs.getXReg x := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> exact Match.reg_eq hm3' hm4 rfl rfl
  have x8 : (s4.data.regs.getXReg .X8).toBitVec.toNat = streamEnd (Ln m0) := by
    rw [hm4.regs .X8 _ rfl]
    exact hseE
  refine .done _ ⟨hpc4.trans (congrArg Host.addrOf rfl), hfr4, by rw [k4 .X1 (by simp)]; exact hpv,
    x8, by rw [k4 .X19 (by simp), a19], by rw [k4 .X20 (by simp), a20],
    by rw [k4 .X21 (by simp), a21], by rw [k4 .X22 (by simp), a22], hp8, h3,
    by rw [hd4]; exact hR3, by rw [hd4]; exact hcnt3, by rw [hd4]; exact hws3⟩

private theorem slots_after {env : Env} {m : MachineData}
    (hm : Match env (after b8 pcS) m)
    (h : (env.regs .X8).toNat + 1 + 8 * phaseWords ≤ (env.regs .X22).toNat) :
    9 ≤ (m.regs.getXReg .X22).toBitVec.toNat := by
  simp only [after, run_b8] at hm
  rw [hm.regs .X22 _ rfl]
  simpa only [Sym.eval] using (slots_ge h)

/-- **From the phase count's store to the phases** (`b8`, the loop). -/
theorem tail_c (hp : Placed code k0) (G : Geo m0 B)
    (hpm : Spec (Labels.label NativeRustcVmArm.Vm.PhaseM.entryLabel) PhaseMPre PhaseMPost) {n : Nat} {ws : List K}
    {c1 p cs : Nat} (h1 : rdU32 B 0 = some (n, 4)) (h2 : rdWords B (2 * n) 4 = some (ws, c1))
    {s4 : MachineState} (hA : At8 k0 m0 B n ws c1 p cs s4) :
    Eventually (step1 Host.exe) (Res m0 B) s4 := by
  obtain ⟨hpc4, hfr4, hpv, x8, a19, a20, a21, a22, hp8, h3, hR4, hcnt4, hws4⟩ := hA
  have hst := G.st
  have hdLe := G.dLe
  have hlen := G.len
  have hL := G.l32
  have hdN := G.dNw
  have hl : 0 < Ln m0 := by have := (rdU32_c h1).2; omega
  obtain ⟨hlt, hnS⟩ := words_lt h2 (len := lenW m0) (by rw [hlen]; exact hdLe)
  rw [hlen] at hnS
  obtain ⟨-, hc1, hwsE⟩ := rdWords_c h2
  have hwsl : ws.length = 2 * n := by rw [hwsE]; simp
  have hdg := decodedWords_ge (Ln m0)
  rw [phaseWords_eq] at hdg
  have hse : 1 + 2 * n ≤ streamEnd (Ln m0) := by unfold streamEnd; omega
  have l8 := NativeRustcVm.length_wordBytes
  have lw : ((ws.map K.lane).flatMap NativeRustcVm.wordBytes).length = 8 * (2 * n) := by
    rw [NativeRustcVm.length_wordsBytes, List.length_map, hwsl]
  -- `b8`: the phase count stored, the loop's set-up
  set se := streamEnd (Ln m0) with hseD
  have hse8 : 8 * se < 2 ^ 64 := by omega
  have hwf5 := G.dw_wf hfr4 (i := se) (by omega)
  have hm5 := G.dw_match hfr4 (i := se) (a := pcAddr) (by
    simp only [pcAddr, Sym.eval, Env.ofMachine_regs, BitVec.ofInt_ofNat,
      NativeRustcVm.addr_add_zero]
    rw [shl3, x8, a21]
    simp [BinOp.apply])
  refine exec_at (infix_of b8_in_code (by simp [b8]) hp) run_b8 hwf5
    (hpc4.trans (congrArg Host.addrOf rfl)) hm5 fun s6 hm6 hpc6 ↦ ?_
  have hfr6 : Frm m0 s6.data := Fr.ofBlockW hfr4 hm5 hm6 hwf5 rfl rfl (keepOk (by decide)) rfl
    (by omega) G.sp (by decide) (by
      intro w hw
      simp only [List.mem_singleton] at hw
      subst hw
      refine .inr ⟨by decide, fun b sz hb ↦ ?_⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
      exact ⟨by decide, fun j hj ↦ G.w_dw (by omega) hj⟩)
  have hs6 := Match.sameOutside_in hm6 hwf5 (r0 := 1) (o := 0) (n := 8) rfl (by omega) (by decide)
  rw [NativeRustcVm.addr_add_zero] at hs6
  have hpc6' : WordAt s6.data.dmem (dw m0 se) p.toUInt64 := by
    have w := wordAt_reg (hm6.bytesAt_write (r := 1) (o := 0) (n := 8) (b := dw m0 se) (sz := 8)
      rfl (by omega) (v := .reg .X1) (by decide))
    rw [NativeRustcVm.addr_add_zero] at w
    have e : UInt64.ofBitVec ((Sym.reg .X1).eval (dwEnv m0 s4.data se)) = p.toUInt64 := by
      apply UInt64.toNat_inj.mp
      rw [toNat_toUInt64_of_lt (by have : p ≤ 8 := hp8; omega)]
      exact hpv
    rwa [e] at w
  have hR6 : ReaderAt s6.data.dmem (rdr m0) (bpA m0) B cs :=
    G.reader_dw (i := se) (by omega) hR4 hs6
  have hcnt6 : WordAt s6.data.dmem (dw m0 0) n.toUInt64 :=
    G.keepB (lo := se) (nb := 8) hs6 (fun q hq ↦ .inr hq) (by omega) hcnt4
      (by rw [l8]; omega) (.inr (by rw [l8]; omega))
  have hws6 : WordsAt s6.data.dmem (dw m0 1) (ws.map K.lane) :=
    G.keepB (lo := se) (nb := 8) hs6 (fun q hq ↦ .inr hq) (by omega) hws4
      (by rw [lw]; omega) (.inr (by rw [lw]; omega))
  simp only [PcOk] at hpc6
  have F : Fix m0 B n ws p cs := ⟨hwsl, hnS, hp8, hl, dec_eq h1 h2 h3 hp8⟩
  have v8 : (s4.data.regs.getXReg .X8).toBitVec = BitVec.ofNat 64 se := by
    apply BitVec.eq_of_toNat_eq; rw [x8, BitVec.toNat_ofNat]; omega
  have v21 : (s4.data.regs.getXReg .X21).toBitVec = decA m0 := by rw [a21]
  refine loop_spec hp G F hpm (k := 0) ⟨hpc6.trans (congrArg Host.addrOf rfl), hfr6, ?_, ?_, ?_,
    ?_, ?_, ?_, ⟨[], cs, rfl, hR6, ⟨hcnt6, hws6, hpc6', fun j hj ↦ absurd hj (by simp)⟩⟩⟩
  · rw [Match.reg_eq hm5 hm6 rfl rfl, a19]
  · rw [Match.reg_eq hm5 hm6 rfl rfl, a20]
  · rw [hm6.regs .X21 _ rfl]
    simp only [Sym.eval, Env.ofMachine_regs, v8, v21]
    rw [x21_eq]
    show _ = decA m0 + BitVec.ofNat 64 (8 * (streamEnd (Ln m0) + 1 + 0 * phaseWords))
    rw [Nat.zero_mul, Nat.add_zero]
  · simp only [Nat.add_zero]
    apply slots_after (env := dwEnv m0 s4.data se)
    · simpa only [after, run_b8] using hm6
    · change (s4.data.regs.getXReg .X8).toBitVec.toNat + 1 + 8 * phaseWords ≤
        (s4.data.regs.getXReg .X22).toBitVec.toNat
      rw [x8, a22, phaseWords_eq]
      change streamEnd (Ln m0) + 1 + 8 * 49411 ≤ lenW m0
      omega
  · show (s6.data.regs.getXReg .X23).toBitVec.toNat + 0 = p
    rw [hm6.regs .X23 _ rfl]
    exact hpv
  · show (s6.data.regs.getXReg .X24).toBitVec.toNat = phaseBytes
    rw [hm6.regs .X24 _ rfl]
    rfl




/-- **From the stream's count to the phases.** -/
theorem tail_spec (hp : Placed code k0) (G : Geo m0 B)
    (hle : Spec (Labels.label NativeRustcVmArm.Vm.ReaderLe.entryLabel) ReaderLePre ReaderLePost)
    (hpm : Spec (Labels.label NativeRustcVmArm.Vm.PhaseM.entryLabel) PhaseMPre PhaseMPost) {n : Nat} {ws : List K}
    {c1 : Nat} {st : MachineState} (hM : Mid k0 m0 B n ws c1 st) :
    Eventually (step1 Host.exe) (Res m0 B) st :=
  Eventually.bind (tail_a hp G hle hM) fun _ h ↦ h.elim (.done _) fun ⟨_, _, hA⟩ ↦
    Eventually.bind (tail_b hp G hM.r1 hM.r2 hA) fun _ hB ↦ tail_c hp G hpm hM.r1 hM.r2 hB

end

end NativeRustcVmArm.Wire.Decode
