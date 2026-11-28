module

public import NativeRustcArm.WotsLeaf.Codeword.Tests

/-!
# The codeword's digits

From `AtB8` at `b8` (directive 97): `b8` (the loop's registers, `out` saved at 0), the digits' loop
(`digits_loop`), `b10` (digits 56 and 57, the values' address at 8, `hi >> 16` at 20): the chain
loop's state for chain 0 at `b14` (directive 184).
-/

namespace NativeRustcArm.WotsLeafProof

open NativeRustc NativeRustc.Xmss NativeRustcArm.Sym NativeRustcArm.Xmss.WotsLeaf Codeword
open LeanVM.Protocol.KeccakHash

public section


theorem regIs_u64 {m : MachineData} {x : XReg} {v : UInt64} (h : Run.RegIs m x v.toBitVec) :
    m.regs.getXReg x = v := UInt64.toBitVec_inj.mp h

variable [NativeRustcArm.Host]

/-- `b8`, then the loop's first turn's state. -/
theorem b8_step (r : Run) (hp : Placed Xmss.WotsLeaf.code r.k) (hpre : r.Pre) (m : MachineData)
    (hA : r.AtB8 m) {R : MachineState → Prop}
    (k : ∀ m', r.AtDigits 0 m' → Eventually (step1 NativeRustcArm.Host.exe) R ⟨m', r.pc NativeRustcArm.Xmss.WotsLeaf.b9Offset⟩) :
    Eventually (step1 NativeRustcArm.Host.exe) R ⟨m, r.pc NativeRustcArm.Xmss.WotsLeaf.b8Offset⟩ := by
  obtain ⟨hK, h52, hcw, h8, h9, h19, h20, h22⟩ := hA
  refine frameStep r hp hpre b8_in_code (List.cons_ne_nil _ _) run_b8 (by decide) rfl hK trivial
    fun st hm hK' hkb hpc ↦ pc_at (by simpa [PcOk, NativeRustcArm.Xmss.WotsLeaf.b8_next] using hpc) (k st.data ?_)
  have hb := r.base_toNat hpre
  have := r.m0.regs.SP.toNat_lt
  have hout : BytesAt st.data.dmem (r.off 0) (wordBytes r.m0.regs.X0) := by
    have := frame_covers hm (o := 0) (n := 8) (by decide) (v := .reg .X19) (by decide)
    rwa [bytes_reg, regIs_u64 (v := r.m0.regs.X0) h19] at this
  refine ⟨⟨hK'.1, allOf_append hK'.2 ⟨⟨length_wordBytes _, by norm_num, hout⟩, trivial⟩⟩,
    fun _ h ↦ absurd h (by simp [Run.digitsPre]), regIs_reg hm rfl h8, regIs_reg hm rfl h9, ?_, ?_,
    ?_, regIs_reg hm rfl h19, regIs_reg hm rfl h20, regIs_reg hm rfl h22⟩
  · unfold Run.RegIs at *
    rw [hm.regs .X10 _ rfl]
    show UnOp.apply (.ubfm 63 62) .W64 ((m.regs.getXReg .X8).toBitVec) = _
    rw [h8, lsl1]
  · unfold Run.RegIs
    rw [hm.regs .X11 _ rfl]
    show BinOp.apply .orr .W64 (r.base + BitVec.ofInt 64 380) (BitVec.ofNat 64 1) = r.base + _
    simp only [BinOp.apply, Sym.low_W64, Sym.ext_W64]
    rw [orr_380 (r.base_aligned hpre) (by omega)]
  · have := regIs_lit hm (y := .X12) (c := 6) rfl
    simpa using this

/-- `b10`, from the loop's end: the chain loop's state for chain 0. -/
theorem b10_step (r : Run) (hp : Placed Xmss.WotsLeaf.code r.k) (hpre : r.Pre) (m : MachineData)
    (hA : r.AtDigits 14 m) (h52 : r.hiW.toNat < 2 ^ 52) :
    Eventually (step1 NativeRustcArm.Host.exe)
      (fun st ↦ st.pc = r.pc NativeRustcArm.Xmss.WotsLeaf.b14Offset ∧ r.AtChain (digits r.dNum) 0 [] st.data) ⟨m, r.pc NativeRustcArm.Xmss.WotsLeaf.b10Offset⟩ := by
  obtain ⟨hK, hD, h8, h9, h10, h11, h12, h19, h20, h22⟩ := hA
  refine frameStep r hp hpre b10_in_code (List.cons_ne_nil _ _) run_b10 (by decide) rfl hK trivial
    fun st hm hK' hkb hpc ↦ .done _ ⟨?_, ?_⟩
  · rw [show st.pc = _ from hpc]
    exact Run.label_of_block r hp b14_in_code rfl
  have s8 : BytesAt st.data.dmem (r.off 8) (wordBytes r.m0.regs.X7) := by
    have := frame_covers hm (o := 8) (n := 8) (by decide) (v := .reg .X22) (by decide)
    rwa [bytes_reg, regIs_u64 (v := r.m0.regs.X7) h22] at this
  have s20 : BytesAt st.data.dmem (r.off 20) (u32Bytes (r.hi >>> 16)) := by
    have := frame_covers hm (o := 20) (n := 4) (by decide)
      (v := .un (.ubfm 16 31) .W32 (.load 0 28 4)) (by decide)
    rwa [bytes_hi16 (Env.load_of_bytesAt rfl hK.2.2.1.2.2)] at this
  have d56 : BytesAt st.data.dmem (r.off 436) [UInt8.ofNat (r.dNum >>> (2 * 56) &&& 3)] := by
    have := frame_covers hm (o := 436) (n := 1) (by decide)
      (v := .un (.ubfm 48 49) .W64 (.reg .X8)) (by decide)
    have e : (List.range 1).map (byteOf ((Sym.un (.ubfm 48 49) .W64 (.reg .X8)).eval (r.env m))) =
        [byteOf (UnOp.apply (.ubfm 48 49) .W64 (m.regs.getXReg .X8).toBitVec) 0] := rfl
    rwa [e, show (m.regs.getXReg .X8).toBitVec = r.hiW from h8, byte_ubfm48 r.lo] at this
  have d57 : BytesAt st.data.dmem (r.off 437) [UInt8.ofNat (r.dNum >>> (2 * 57) &&& 3)] := by
    have := frame_covers hm (o := 437) (n := 1) (by decide)
      (v := .un (.ubfm 50 63) .W64 (.reg .X8)) (by decide)
    have e : (List.range 1).map (byteOf ((Sym.un (.ubfm 50 63) .W64 (.reg .X8)).eval (r.env m))) =
        [byteOf (UnOp.apply (.ubfm 50 63) .W64 (m.regs.getXReg .X8).toBitVec) 0] := rfl
    rwa [e, show (m.regs.getXReg .X8).toBitVec = r.hiW from h8, byte_ubfm50 r.lo r.hiW h52] at this
  have hD' : BytesAt st.data.dmem (r.off 380) (digits r.dNum) := by
    rw [← digitsPre_58, digitsPre_56_2]
    have hD56 : BytesAt m.dmem (r.off 380) (r.digitsPre 56) := hD
    refine BytesAt.append (hkb 380 _ (by rw [length_digitsPre]; omega)
      (by rw [length_digitsPre]; decide) hD56) ?_
    rw [length_digitsPre, r.off_add]
    refine BytesAt.append (bs := [_]) d56 ?_
    rw [List.length_singleton, r.off_add]
    exact d57
  refine ⟨by omega, rfl, ⟨hK'.1, ⟨length_wordBytes _, by norm_num, hK'.2.2.2.2.1.2.2⟩,
    ⟨length_wordBytes _, by norm_num, s8⟩, ⟨rfl, by norm_num, s20⟩, hK'.2.1, hK'.2.2.1,
    ⟨by simp [digits], by norm_num, hD'⟩, ⟨rfl, by norm_num, fun _ h ↦ absurd h (by simp)⟩, trivial⟩,
    regIs_lit hm rfl, regIs_ptr hm rfl, regIs_lit hm rfl, regIs_ptr hm rfl, regIs_ptr hm rfl,
    regIs_reg hm rfl h20, regIs_reg hm rfl h22⟩

/-- **Region 2, the codeword**: from `AtCheck` at `b6`, no codeword and the return, or the
codeword's digits and the chain loop's state for chain 0 at `b14` (directive 184). -/
theorem codeword_region : RegionSpec Run.AtCheck NativeRustcArm.Xmss.WotsLeaf.b6Offset fun r st ↦
    (r.result = none ∧ r.Done st) ∨
      (codeword r.digest16 = some (digits r.dNum) ∧ st.pc = r.pc NativeRustcArm.Xmss.WotsLeaf.b14Offset ∧
        r.AtChain (digits r.dNum) 0 [] st.data) := by
  intro r hp hc hpre m hA
  refine NativeRustcArm.Eventually.bind (tests_region r hp hc hpre m hA) fun st h ↦ ?_
  rcases h with h | ⟨hpc, hB⟩
  · exact .done _ (.inl h)
  refine pc_at hpc (b8_step r hp hpre st.data hB fun m' hD ↦ ?_)
  refine NativeRustcArm.Eventually.bind (digits_loop r hp hpre 14 0 rfl (by decide) m' hD)
    fun st' ⟨hpc', hD'⟩ ↦ pc_at hpc' ?_
  exact NativeRustcArm.Eventually.mono (b10_step r hp hpre st'.data hD' hB.2.1) fun st'' h ↦
    .inr ⟨codeword_some r hB.2.2.1, h⟩

end

end NativeRustcArm.WotsLeafProof
