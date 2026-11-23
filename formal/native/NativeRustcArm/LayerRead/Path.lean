module

public import NativeRustcArm.Code.Common.Memcpy.Names

public import NativeRustcArm.LayerRead.Mid
public import NativeRustcArm.LayerRead.PathExec
public import NativeRustcArm.LayerRead.Head
import Std.Tactic.BVDecide

/-!
# `LayerSignature::read`: the sixteen path nodes

The remaining slice has at least 256 bytes after the chain values. Clearing
its low four bits therefore cannot make it any of the smaller lengths
checked by the unrolled path. The final block advances both descriptor words.
-/

namespace NativeRustcArm.Xmss.LayerRead

open NativeRustcArm.Sym NativeRustcArm

set_option Elab.async false

/-- The environment at block 5. -/
def envP (m₀ m : MachineData) : Env :=
  Env.ofMachine m [(frame m₀, 1936), (cur m₀, 16), (sig m₀, 1200)]

theorem ls_false [Labels] {env : Env} {v : Nat}
    (hx : env.regs .X24 = BitVec.ofNat 64 v) (h : 15 < v) (hv : v < 2 ^ 64) :
    (SBool.or (SBool.cmp .ult .W64 (.reg .X24) (.lit 15))
      (SBool.cmp .eq .W64 (.reg .X24) (.lit 15))).eval env = false := by
  simp [SBool.eval, CmpOp.apply, Sym.eval, low_W64, hx, BitVec.ult, BitVec.toNat_eq]
  omega

theorem mask_div (x : BitVec 64) :
    (x &&& BitVec.ofNat 64 18446744073709551600).toNat / 16 = x.toNat / 16 := by
  have h : (x &&& BitVec.ofNat 64 18446744073709551600) >>> 4 = x >>> 4 := by
    bv_decide
  have := congrArg BitVec.toNat h
  simpa [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] using this

theorem mask_ne [Labels] {env : Env} {v n : Nat} {r : XReg}
    (hx : env.regs r = BitVec.ofNat 64 v) (hv : v < 2 ^ 64) (hn : n < 256)
    (h : 256 ≤ v) :
    (SBool.cmp .eq .W64 (.bin .and .W64 (.reg r) (.lit 18446744073709551600)) (.lit n)).eval env = false := by
  simp only [SBool.eval, CmpOp.apply, Sym.eval, BinOp.apply, low_W64, ext_W64, hx,
    beq_eq_false_iff_ne]
  intro heq
  have hd := mask_div (BitVec.ofNat 64 v)
  rw [heq] at hd
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv,
    Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega)] at hd
  omega

section
variable {m₀ m : MachineData}

theorem envP_wf (P : Pre m₀) (C : Common m₀ m) : (envP m₀ m).WF := by
  exact Env.wf_of ⟨⟨P.frameMapped.kept C.kept, P.frameNW⟩, ⟨P.curMapped.kept C.kept, P.curNW⟩,
    ⟨P.sigMapped.kept C.kept, P.sigNW⟩, trivial⟩
    (pairwise3 P.curF.symm P.sigF.symm P.curSig)

theorem match_envP [Labels] (P : Pre m₀) (h : MidAt m₀ m) : Match (envP m₀ m) stP0 m := by
  have C := h.common
  unfold envP stP0
  apply match_ofMachine
  · exact And.intro rfl (And.intro (fun _ => P.frame16) (And.intro rfl (And.intro (by simp)
      (And.intro rfl (And.intro (by simp) trivial)))))
  · rw [C.sp]
    simp [Sym.eval]
  · exact ⟨C.x20.trans (by simp [Sym.eval]), trivial⟩
  · exact trivial
  · exact trivial
  · refine ⟨?_, trivial⟩
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs, C.x21, h.x23,
      Env.base_ofMachine_eq]
    simp

end

/-- The machine state at the `memcpy` of the path. -/
theorem pathCall [Labels] {m₀ m m' : MachineData} (P : Pre m₀) (h : MidAt m₀ m)
    (hm : Match (envP m₀ m) stP17 m') : PathCall m₀ m' := by
  have C := h.common
  have hwf := envP_wf P C
  have hs : Saved m m' := Match.saved (match_envP P h) hm hwf rfl stP17_keeps
  have hr0 : (envP m₀ m).regions[0]? = some (frame m₀, 1936) := rfl
  have hfr : ∀ {o : Nat} {bs : List UInt8}, o + bs.length ≤ 1936 →
      firstOverlap 0 o bs.length stP17.mem = none →
      BytesAt m.dmem (frame m₀ + BitVec.ofNat 64 o) bs →
      BytesAt m'.dmem (frame m₀ + BitVec.ofNat 64 o) bs :=
    fun hle hc h0 => hm.bytesAt_keep hr0 hle hc h0
  refine ⟨common_of_saved C hs ?_ (fun j hj hj3 => hfr (by rw [length_regBytes]; omega)
      (by rw [length_regBytes]; exact stP17_save j hj) (C.save j hj hj3)),
    ?_, ?_, ?_, ?_, ?_,
    bytesAt_add_zero (hfr (by rw [length_chainBytes P]; omega)
      (by rw [length_chainBytes P]; exact stP17_chain) (by simpa using h.chain)), ?_⟩
  · refine (C.same.trans (hm.sameOutside_in hwf stP17_writes)).mono fun p hp => ?_
    rcases hp with hp | ⟨r, hr, b, sz, hb, hin⟩
    · exact hp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · cases hb
        exact Or.inl hin
      · cases hb
        exact Or.inr hin
  · exact (hm.regs .X0 (.reg .X19) stP17_regs.1).trans C.x19
  · exact (hm.regs .X1 (.ptr 0 928) stP17_regs.2.1).trans (by simp [Sym.eval, envP])
  · exact hm.regs .X2 (.lit 256) stP17_regs.2.2
  · have := bytesAt_add_zero (hm.bytesAt_write (r := 1) (o := 0) (n := 8) rfl (by omega)
      stP17_cursorData)
    simpa [Sym.eval, BinOp.apply, envP, h.common.x21, h.x23, addr_add_addr, regBytes] using this
  · have := hm.bytesAt_write (r := 1) (o := 8) (n := 8) rfl (by omega) stP17_cursorLength
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs, envP, h.x22] at this
    rw [ofNat_sub _ _ (by have := P.remaining; omega)] at this
    change BytesAt m'.dmem (cur m₀ + BitVec.ofNat 64 8)
      (regBytes (BitVec.ofNat 64 (remaining m₀ - 1200)))
    simpa only [show remaining m₀ - 928 - 272 = remaining m₀ - 1200 by omega, regBytes] using this
  · refine bytesAt_flatten 16 (fun j hj => P.pathSlot_length hj) fun j hj => ?_
    rw [addr_add_addr]
    refine bytesAt_slice (by omega) fun t ht => ?_
    rw [addr_add_addr]
    have hg := hm.get?_load (r := 0) hr0 (by omega) (stP17_path j hj t ht) (by omega) (le_refl 8)
    rw [hg, show 944 + 16 * j + 8 * (t / 8) + t % 8 = 944 + 16 * j + t by omega]
    simp only [Env.base_ofMachine_eq, envP, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.map_some, Option.getD_some, Env.ofMachine_mem0]
    rw [C.same _ (P.sig_not_scratch (by omega))]
    rfl

/-- The path reaches its output copy with an advanced slice descriptor. -/
public theorem path [Host] {k : Nat} (hp : Placed code k) {m₀ : MachineData} (P : Pre m₀)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcArm.Xmss.LayerRead.b5Offset)) (h : MidAt m₀ st.data)
    {R : MachineState → Prop}
    (cont : ∀ st' : MachineState, st'.pc = Labels.label NativeRustcArm.Common.Memcpy.entryLabel → retOf st'.data = Host.addrOf (k + NativeRustcArm.Xmss.LayerRead.b22Offset) →
      PathCall m₀ st'.data → Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have hwf := envP_wf P h.common
  have hn := P.remaining
  have hn' := remaining_lt m₀
  have hx22 : (envP m₀ st.data).regs .X22 = BitVec.ofNat 64 (remaining m₀ - 928) := h.x22
  have hx24 : (envP m₀ st.data).regs .X24 = BitVec.ofNat 64 (remaining m₀ - 944) := h.x24
  refine cond_step (b5_in_code.trans hp.1 (List.cons_ne_nil _ _)) b5_execP hwf hpc
    (match_envP P h) (ls_false hx24 (by omega) (by omega)) fun s1 hpc1 hm1 => ?_
  refine cond_step (b6_in_code.trans hp.1 (List.cons_ne_nil _ _)) b6_execP hwf
    (hpc1.trans rfl) hm1 (mask_ne hx24 (by omega) (by decide) (by omega)) fun s2 hpc2 hm2 => ?_
  refine cond_step (b7_in_code.trans hp.1 (List.cons_ne_nil _ _)) b7_execP hwf
    (hpc2.trans rfl) hm2 (mask_ne hx24 (by omega) (by decide) (by omega)) fun s3 hpc3 hm3 => ?_
  refine cond_step (b8_in_code.trans hp.1 (List.cons_ne_nil _ _)) b8_execP hwf
    (hpc3.trans rfl) hm3 (mask_ne hx24 (by omega) (by decide) (by omega)) fun s4 hpc4 hm4 => ?_
  refine cond_step (b9_in_code.trans hp.1 (List.cons_ne_nil _ _)) b9_execP hwf
    (hpc4.trans rfl) hm4 (mask_ne hx24 (by omega) (by decide) (by omega)) fun s5 hpc5 hm5 => ?_
  refine cond_step (b10_in_code.trans hp.1 (List.cons_ne_nil _ _)) b10_execP hwf
    (hpc5.trans rfl) hm5 (mask_ne hx24 (by omega) (by decide) (by omega)) fun s6 hpc6 hm6 => ?_
  refine cond_step (b11_in_code.trans hp.1 (List.cons_ne_nil _ _)) b11_execP hwf
    (hpc6.trans rfl) hm6 (mask_ne hx24 (by omega) (by decide) (by omega)) fun s7 hpc7 hm7 => ?_
  refine cond_step (b12_in_code.trans hp.1 (List.cons_ne_nil _ _)) b12_execP hwf
    (hpc7.trans rfl) hm7 (mask_ne hx24 (by omega) (by decide) (by omega)) fun s8 hpc8 hm8 => ?_
  refine cond_step (b13_in_code.trans hp.1 (List.cons_ne_nil _ _)) b13_execP hwf
    (hpc8.trans rfl) hm8 (mask_ne hx22 (by omega) (by decide) (by omega)) fun s9 hpc9 hm9 => ?_
  refine cond_step (b14_in_code.trans hp.1 (List.cons_ne_nil _ _)) b14_execP hwf
    (hpc9.trans rfl) hm9 (mask_ne hx24 (by omega) (by decide) (by omega)) fun s10 hpc10 hm10 => ?_
  refine cond_step (b15_in_code.trans hp.1 (List.cons_ne_nil _ _)) b15_execP hwf
    (hpc10.trans rfl) hm10 (mask_ne hx24 (by omega) (by decide) (by omega)) fun s11 hpc11 hm11 => ?_
  refine cond_step (b16_in_code.trans hp.1 (List.cons_ne_nil _ _)) b16_execP hwf
    (hpc11.trans rfl) hm11 (mask_ne hx24 (by omega) (by decide) (by omega)) fun s12 hpc12 hm12 => ?_
  refine cond_step (b17_in_code.trans hp.1 (List.cons_ne_nil _ _)) b17_execP hwf
    (hpc12.trans rfl) hm12 (mask_ne hx24 (by omega) (by decide) (by omega)) fun s13 hpc13 hm13 => ?_
  refine cond_step (b18_in_code.trans hp.1 (List.cons_ne_nil _ _)) b18_execP hwf
    (hpc13.trans rfl) hm13 (mask_ne hx24 (by omega) (by decide) (by omega)) fun s14 hpc14 hm14 => ?_
  refine cond_step (b19_in_code.trans hp.1 (List.cons_ne_nil _ _)) b19_execP hwf
    (hpc14.trans rfl) hm14 (mask_ne hx24 (by omega) (by decide) (by omega)) fun s15 hpc15 hm15 => ?_
  refine cond_step (b20_in_code.trans hp.1 (List.cons_ne_nil _ _)) b20_execP hwf
    (hpc15.trans rfl) hm15 (mask_ne hx24 (by omega) (by decide) (by omega)) fun s16 hpc16 hm16 => ?_
  refine call_step (b21_in_code.trans hp.1 (List.cons_ne_nil _ _)) b21_execP hwf
    (hpc16.trans rfl) hm16 fun s hpc' hm => cont s (hpc'.1) (hpc'.2.trans rfl) ?_
  exact pathCall P h hm

end NativeRustcArm.Xmss.LayerRead
