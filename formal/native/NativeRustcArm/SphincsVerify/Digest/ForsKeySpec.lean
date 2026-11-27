module

public import NativeRustcArm.Rodata.Names

public import NativeRustcArm.SphincsVerify.Digest.ForsKey

/-!
# Region 4, the FORS key: `b91` and `ForsKeySpec`

`b91` stores `signed`, the FORS key's 16 bytes, at `20032`, the layer loop's
spill `base + 19009` at `8`, and sets the loop's registers: `AtLayer 0 r.forsPk` at `b92`
(`forsKey2_spec`). `forsKey_spec` composes the region.
-/

namespace NativeRustcArm.SphincsVerifyProof.Digest

open NativeRustc NativeRustc.Sphincs NativeRustc.Keccak NativeRustcArm.Sym
  LeanVM.Protocol.KeccakHash Native.Keccak

public section

/-- `orr x24, x19, #0x1`: the 16-byte aligned frame's byte `19008`, plus one. -/
theorem orr_one_eval [Labels] {r : Run} (hpre : r.Pre) (m : MachineData) :
    (Sym.bin .orr .W64 (.ptr 0 19008) (.lit 1)).eval (r.env m) = r.off 19009 := by
  have e : (Sym.ptr 0 19008).eval (r.env m) = r.off 19008 := eval_ptr0 m _ 19008
  show BinOp.apply .orr .W64 ((Sym.ptr 0 19008).eval (r.env m)) (BitVec.ofNat 64 1) = _
  rw [e]
  simp only [BinOp.apply, low_W64, ext_W64]
  show r.off 19008 ||| BitVec.ofNat 64 1 = r.off 19009
  have hb := r.base_aligned hpre
  have h1 := r.off_toNat hpre (a := 19008) (by decide)
  have h2 := r.off_toNat hpre (a := 19009) (by decide)
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or, h1, h2, show (BitVec.ofNat 64 1).toNat = 1 from rfl, Nat.or_comm,
    lor_eq_add (n := 1) (by decide) (by omega)]
  omega

variable [ElfHost]

/-- **`signed`, the layer loop's registers** (`b91`). -/
theorem forsKey2_spec (r : Run) (hp : PlacedIn Sphincs.SphincsVerify.code r.sec r.k) (hpre : r.Pre)
    {m : MachineData} (hA : FK1 r m) :
    Eventually (elfStep1 ElfHost.exe) (fun st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b92Offset ∧ r.AtLayer 0 r.forsPk st.data)
      ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b91Offset⟩ := by
  obtain ⟨hK, h23, h19, h20, h27, h400, hD⟩ := hA
  obtain ⟨hF, ⟨hpk, hsig, h392⟩, h408⟩ := hK
  have hwf := r.frame_wf hpre hF (fun _ ↦ 0)
  have hm := Run.frame_match r hpre ⟨hF, ⟨hpk, hsig, h392⟩, h408⟩
    (knownOK_ptr h19 (knownOK_ptr h20 (knownOK_nil m)))
  refine Run.fallStep r hp Sphincs.SphincsVerify.b91_in_code rfl (List.cons_ne_nil _ _) hwf
    run_b91 hm fun m₁ hm₁ ↦ .done _ ⟨rfl, ?_⟩
  have hw := NativeRustc.length_wordBytes
  have hk : ∀ o (bs : List UInt8), o + bs.length ≤ 21616 → Run.noWriteIn _ o bs.length = true →
      BytesAt m.dmem (r.off o) bs → BytesAt m₁.dmem (r.off o) bs :=
    fun _ _ ho hn h ↦ r.bytesAt_kept hpre hm₁ hwf ho h hn
  have hpl := r.hpk
  have hsl := r.length_sigMem
  have hP : BytesAt m.dmem (r.off 8640) r.forsPk := by
    have := bytesAt_drop_take hD 0 16 (by rw [NativeRustc.Sphincs.length_hashBytes]; omega)
    rwa [Run.off_add, List.drop_zero, ← forsPk_eq] at this
  refine ⟨by decide, length_forsPk r, Run.Frame.of_match r hpre hF hm₁ hwf rfl rfl rfl,
    ⟨hk 448 _ (by omega) (by rw [hpl]; rfl) hpk, hk 484 _ (by omega) (by rw [hsl]; rfl) hsig,
      hk 392 _ (by rw [hw]; omega) (by rw [hw]; rfl) h392⟩,
    regIs_lit hm₁ (y := .X10) (c := 0) rfl, ?_, (regIs_lit hm₁ (y := .X11) (c := 4656) rfl :),
    (regIs_lit hm₁ (y := .X12) (c := 8) rfl :), regIs_keep hm₁ rfl h23,
    (regIs_lit hm₁ (y := .X13) (c := 117440512) rfl :), regIs_ptr hm₁ (y := .X22) (o := 15936) rfl,
    (regIs_lit hm₁ (y := .X19) (c := 136) rfl :), regIs_ptr hm₁ (y := .X21) (o := 19208) rfl, ?_,
    regIs_ptr hm₁ (y := .X25) (o := 8840) rfl, regIs_keep hm₁ rfl h27, ?_, ?_,
    hk 400 _ (by rw [hw]; omega) (by rw [hw]; rfl) h400,
    hk 408 _ (by rw [hw]; omega) (by rw [hw]; rfl) h408⟩
  · unfold Run.RegIs
    rw [hm₁.regs .X8 (.label NativeRustcArm.layerHeightsLabel) rfl]
    rfl
  · unfold Run.RegIs
    rw [hm₁.regs .X24 _ rfl, orr_one_eval hpre m]
  · have hP' : BytesAt (r.env m).mem0 ((r.env m).base 0 + BitVec.ofNat 64 8640) r.forsPk := hP
    exact copy hm₁ (r := 0) (r' := 0) (sz := 21616) (o := 20032) (o' := 8640) (n := 16) rfl (by decide) rfl
      (length_forsPk r) hP'
  · have := hm₁.bytesAt_write (r := 0) (o := 8) (n := 8) (b := r.base) (sz := 21616) rfl
      (by decide) (v := .bin .orr .W64 (.ptr 0 19008) (.lit 1)) (by decide)
    rw [bytes_word, orr_one_eval hpre m] at this
    exact this

end

end NativeRustcArm.SphincsVerifyProof.Digest

namespace NativeRustcArm.SphincsVerifyProof

open Digest

public section

/-- **Region 4, the FORS key.** -/
theorem forsKey_spec [ElfHost] : ForsKeySpec := by
  intro r hp hc hpre m hA
  exact Run.stage r (forsKey0_spec r hp hc hpre hA) fun m₁ h₁ ↦
    Run.stage r (forsKey1_spec r hp hc hpre h₁) fun m₂ h₂ ↦ forsKey2_spec r hp hpre h₂

end

end NativeRustcArm.SphincsVerifyProof
