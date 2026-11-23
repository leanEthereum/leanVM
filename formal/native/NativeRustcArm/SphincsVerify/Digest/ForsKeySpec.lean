module

public import NativeRustcArm.Rodata.Names

public import NativeRustcArm.SphincsVerify.Digest.ForsKey

/-!
# Region 4, the FORS key: `b100` and `ForsKeySpec`

`b100` (directive 1288) stores `signed`, the FORS key's 16 bytes, at `27792`, the layer loop's
spill `base + 26769` at `0`, and sets the loop's registers: `AtLayer 0 r.forsPk` at `b101`
(directive 1306, `forsKey2_spec`). `forsKey_spec` composes the region.
-/

namespace NativeRustcArm.SphincsVerifyProof.Digest

open NativeRustc NativeRustc.Sphincs NativeRustc.Keccak NativeRustcArm.Sym
  LeanVM.Protocol.KeccakHash Native.Keccak

public section

/-- `orr x23, x19, #0x1`: the 16-byte aligned frame's byte `26768`, plus one. -/
theorem orr_one_eval [Labels] {r : Run} (hpre : r.Pre) (m : MachineData) :
    (Sym.bin .orr .W64 (.ptr 0 26768) (.lit 1)).eval (r.env m) = r.off 26769 := by
  have e : (Sym.ptr 0 26768).eval (r.env m) = r.off 26768 := eval_ptr0 m _ 26768
  show BinOp.apply .orr .W64 ((Sym.ptr 0 26768).eval (r.env m)) (BitVec.ofNat 64 1) = _
  rw [e]
  simp only [BinOp.apply, low_W64, ext_W64]
  show r.off 26768 ||| BitVec.ofNat 64 1 = r.off 26769
  have hb := r.base_aligned hpre
  have h1 := r.off_toNat hpre (a := 26768) (by decide)
  have h2 := r.off_toNat hpre (a := 26769) (by decide)
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or, h1, h2, show (BitVec.ofNat 64 1).toNat = 1 from rfl, Nat.or_comm,
    lor_eq_add (n := 1) (by decide) (by omega)]
  omega

variable [NativeRustcArm.Host]

/-- **`signed`, the layer loop's registers** (`b100`). -/
theorem forsKey2_spec (r : Run) (hp : Placed Sphincs.SphincsVerify.code r.k) (hpre : r.Pre)
    {m : MachineData} (hA : FK1 r m) :
    Eventually (step1 NativeRustcArm.Host.exe) (fun st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b101Offset ∧ r.AtLayer 0 r.forsPk st.data)
      ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b100Offset⟩ := by
  obtain ⟨hK, h22, h19, h20, h384, hD⟩ := hA
  obtain ⟨hF, ⟨hpk, hsig, h376⟩, h392⟩ := hK
  have hwf := r.frame_wf hpre hF (fun _ ↦ 0)
  have hm := Run.frame_match r hpre ⟨hF, ⟨hpk, hsig, h376⟩, h392⟩
    (knownOK_ptr h19 (knownOK_ptr h20 (knownOK_nil m)))
  refine Run.fallStep r hp Sphincs.SphincsVerify.b100_in_code rfl (List.cons_ne_nil _ _) hwf
    run_b100 hm fun m₁ hm₁ ↦ .done _ ⟨rfl, ?_⟩
  have hw := NativeRustc.length_wordBytes
  have hk : ∀ o (bs : List UInt8), o + bs.length ≤ 29376 → Run.noWriteIn _ o bs.length = true →
      BytesAt m.dmem (r.off o) bs → BytesAt m₁.dmem (r.off o) bs :=
    fun _ _ ho hn h ↦ r.bytesAt_kept hpre hm₁ hwf ho h hn
  have hpl := length_pkBytes r.w
  have hsl := r.length_sigMem
  have hP : BytesAt m.dmem (r.off 16400) r.forsPk := by
    have := bytesAt_drop_take hD 0 16 (by rw [NativeRustc.Sphincs.length_hashBytes]; omega)
    rwa [Run.off_add, List.drop_zero, ← forsPk_eq] at this
  refine ⟨by decide, length_forsPk r, Run.Frame.of_match r hpre hF hm₁ hwf rfl rfl rfl,
    ⟨hk 8208 _ (by omega) (by rw [hpl]; rfl) hpk, hk 8244 _ (by omega) (by rw [hsl]; rfl) hsig,
      hk 376 _ (by rw [hw]; omega) (by rw [hw]; rfl) h376⟩,
    regIs_lit hm₁ (y := .X10) (c := 0) rfl, ?_, ?_, (regIs_lit hm₁ (y := .X12) (c := 4656) rfl :),
    (regIs_lit hm₁ (y := .X13) (c := 8) rfl :), regIs_keep hm₁ rfl h22,
    (regIs_lit hm₁ (y := .X14) (c := 117440512) rfl :), regIs_ptr hm₁ (y := .X20) (o := 21648) rfl,
    (regIs_lit hm₁ (y := .X26) (c := 136) rfl :), regIs_ptr hm₁ (y := .X21) (o := 26968) rfl, ?_,
    regIs_ptr hm₁ (y := .X25) (o := 16600) rfl, ?_, ?_, hk 384 _ (by rw [hw]; omega) (by rw [hw]; rfl) h384⟩
  · unfold Run.RegIs
    rw [hm₁.regs .X8 (.label NativeRustcArm.layerHeightsLabel) rfl]
    rfl
  · unfold Run.RegIs
    rw [hm₁.regs .X11 (.load 0 392 8) rfl]
    show (r.env m).load 0 392 8 = _
    have h392' : BytesAt (r.env m).mem0 ((r.env m).base 0 + BitVec.ofNat 64 392)
        (wordBytes (r.addr 12900)) := h392
    rw [Env.load_of_bytesAt (hw _) h392', ofInt_ofBytes_wordBytes]
    rfl
  · unfold Run.RegIs
    rw [hm₁.regs .X23 _ rfl, orr_one_eval hpre m]
  · have hP' : BytesAt (r.env m).mem0 ((r.env m).base 0 + BitVec.ofNat 64 16400) r.forsPk := hP
    exact copy hm₁ (r := 0) (r' := 0) (sz := 29376) (o := 27792) (o' := 16400) (n := 16) rfl (by decide) rfl
      (length_forsPk r) hP'
  · have := hm₁.bytesAt_write (r := 0) (o := 0) (n := 8) (b := r.base) (sz := 29376) rfl
      (by decide) (v := .bin .orr .W64 (.ptr 0 26768) (.lit 1)) (by decide)
    rw [bytes_word, orr_one_eval hpre m] at this
    exact this

end

end NativeRustcArm.SphincsVerifyProof.Digest

namespace NativeRustcArm.SphincsVerifyProof

open Digest

public section

/-- **Region 4, the FORS key.** -/
theorem forsKey_spec [NativeRustcArm.Host] : ForsKeySpec := by
  intro r hp hc hpre m hA
  exact Run.stage r (forsKey0_spec r hp hc hpre hA) fun m₁ h₁ ↦
    Run.stage r (forsKey1_spec r hp hc hpre h₁) fun m₂ h₂ ↦ forsKey2_spec r hp hpre h₂

end

end NativeRustcArm.SphincsVerifyProof
