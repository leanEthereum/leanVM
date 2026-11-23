module

public import NativeRustcArm.Code.Common.Memset.Names

public import NativeRustcArm.XmssVerify.Head

/-!
# `xmss_verify`: from the entry to the loop copying the signature's words

`head`: blocks 0 and 1 and the `memset` between them (`NativeRustcArm.XmssVerify.Head`), to
`LoopAt` before the loop's first turn.
-/

namespace NativeRustcArm.Xmss.XmssVerify

open NativeRustcArm.Sym NativeRustcArm LeanVM.Protocol.KeccakHash

set_option Elab.async false

variable [Host] {w : Nat → UInt64} {m₀ : MachineData}

theorem match_st0 (P : Pre w m₀) : Match (Env.ofMachine m₀ (regs0 m₀)) st0 m₀ := by
  unfold st0
  apply match_ofMachine
  · exact And.intro rfl (And.intro (fun _ => frame16 P) (And.intro rfl
      (And.intro (by simp) trivial)))
  · simp only [Sym.eval, Env.base_ofMachine_eq, regs0, List.getElem?_cons_zero, Option.map_some,
      Option.getD_some]
    exact (sp_eq m₀).symm
  · refine ⟨?_, trivial⟩
    simp only [Sym.eval, Env.base_ofMachine_eq, regs0, List.getElem?_cons_succ,
      List.getElem?_cons_zero, Option.map_some, Option.getD_some]
    exact (inp_eq m₀).symm
  · exact trivial
  · exact trivial
  · exact trivial

/-- Common after block 0. -/
theorem common_b0 (P : Pre w m₀) {m : MachineData}
    (hm : Match (Env.ofMachine m₀ (regs0 m₀)) st0' m) : Common m₀ m := by
  have hwf := regs0_wf P (Kept.refl m₀.dmem)
  obtain ⟨-, -, -, -, -, h29, hsp, hw⟩ := st0'_facts
  refine ⟨?_, ?_, fun j hj => ?_, ?_, ?_⟩
  · rw [hm.sp, hsp]
    simp [Sym.eval, regs0]
  · rw [hm.regs .X29 _ h29]
    simp only [Sym.eval, Env.base_ofMachine_eq, regs0, List.getElem?_cons_zero, Option.map_some,
      Option.getD_some]
    rw [BitVec.ofInt_ofNat, ad_add]
  · have := hm.bytesAt_write (r := 0) rfl (by omega) (st0'_save j hj)
    rw [show fb + 5776 + 8 * j = fb + (5776 + 8 * j) by omega, ← ad_add]
    exact this
  · refine (hm.sameOutside_in hwf hw).mono fun p ⟨r, hr, b, sz, hb, hin⟩ => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    simp only [Env.ofMachine_regions, regs0, List.getElem?_cons_zero, Option.some.injEq,
      Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    exact P.inRange_lo (by fbo) hin
  · exact hm.kept hwf

omit [Host] in
theorem base1_regs0 {m : MachineData} (t : Nat) :
    (Env.ofMachine m (regs0 m₀)).base 1 + BitVec.ofNat 64 t = inp m₀ + BitVec.ofNat 64 t := rfl

/-- **The prologue**: from the entry to the loop copying the signature's words. -/
public theorem head {k : Nat} (hp : Placed code k)
    (hmemset : Spec (label NativeRustcArm.Common.Memset.entryLabel) MemsetPre MemsetPost) (P : Pre w m₀)
    {R : MachineState → Prop}
    (cont : ∀ st : MachineState, st.pc = Host.addrOf (k + NativeRustcArm.Xmss.XmssVerify.b2Offset) → LoopAt w m₀ st.data 0 →
      Eventually (step1 Host.exe) R st) :
    Eventually (step1 Host.exe) R ⟨m₀, Host.addrOf k⟩ := by
  have hwf := regs0_wf P (Kept.refl m₀.dmem)
  refine call_step (b0_in_code.trans hp.1 (List.cons_ne_nil _ _)) b0_exec hwf rfl (match_st0 P)
    fun st₁ hpc₁ hm₁ => ?_
  change Match _ st0' st₁.data at hm₁
  have C₁ := common_b0 P hm₁
  obtain ⟨h0, -, h2, h19, h20, -, -, -⟩ := st0'_facts
  have hx0 : st₁.data.regs.X0.toBitVec = ad m₀ (fb + 48) := by
    show (st₁.data.regs.getXReg .X0).toBitVec = _
    rw [hm₁.regs .X0 _ h0]
    simp only [Sym.eval, Env.base_ofMachine_eq, regs0, List.getElem?_cons_zero, Option.map_some,
      Option.getD_some, BitVec.ofInt_ofNat, ad_add]
  have hx2 : st₁.data.regs.X2.toNat = 2400 := by
    show st₁.data.regs.X2.toBitVec.toNat = 2400
    erw [hm₁.regs .X2 _ h2]
    rfl
  refine call_then hpc₁ hmemset (memsetPre P C₁ hx0 hx2 (by fbo)) fun st₂ hpc₂ hpost => ?_
  obtain ⟨-, -, hsame, hs⟩ := hpost
  rw [hx0, hx2] at hsame
  have C₂ : Common m₀ st₂.data := C₁.call hs hsame (fun p hp => P.inRange_lo (by fbo) hp)
    fun x hx hx' => P.not_inRange_ad (by fbo) hx' (by omega)
  have hwf₂ := regs0_wf P C₂.kept
  have hm₂ : Match (Env.ofMachine st₂.data (regs0 m₀)) st1 st₂.data := by
    unfold st1
    apply match_ofMachine
    · exact And.intro rfl (And.intro (fun _ => frame16 P) (And.intro rfl
        (And.intro (by simp) trivial)))
    · rw [C₂.sp]
      simp [Sym.eval, regs0]
    · refine ⟨?_, ?_, ?_, ?_, trivial⟩
      · show (st₂.data.regs.getXReg .X20).toBitVec = _
        rw [hs.1 .X20 rfl, hm₁.regs .X20 _ h20]
        rfl
      · show (st₂.data.regs.getXReg .X19).toBitVec = _
        rw [hs.1 .X19 rfl, hm₁.regs .X19 _ h19]
        rfl
      · show (st₂.data.regs.getXReg .X21).toBitVec = _
        rw [hs.1 .X21 rfl, hm₁.regs .X21 _ st0'_x21]
        rfl
      · show (st₂.data.regs.getXReg .X22).toBitVec = _
        rw [hs.1 .X22 rfl, hm₁.regs .X22 _ st0'_x22]
        rfl
    · exact trivial
    · exact trivial
    · exact trivial
  refine fall_step (b1_in_code.trans hp.1 (List.cons_ne_nil _ _)) b1_exec hwf₂ (hpc₂.trans rfl) hm₂
    fun st₃ hpc₃ hm₃ => cont st₃ (hpc₃.trans rfl) ?_
  change Match _ st1' st₃.data at hm₃
  obtain ⟨h8, h9, h10, h11, h12, h24, h23, h19', h20', h29, hsp, hw, hsave⟩ := st1'_facts
  have hword : ∀ {r : XReg} {i : Nat}, i < 309 → st1'.reg r = some (.load 1 (8 * i) 8) →
      st₃.data.regs.getXReg r = w i := fun hi h =>
    UInt64.toBitVec_inj.mp ((hm₃.regs _ _ h).trans
      (load_word P C₂.same hi (base1_regs0 (8 * _))))
  refine ⟨Common.block P C₂ hwf₂ hm₂ hm₃ (by rw [hsp]; rfl) rfl h29 hw hsave, ?_, ?_, ?_,
    hword (i := 0) (by omega) h8, hword (i := 1) (by omega) h9, hword (i := 2) (by omega) h10,
    hword (i := 3) (by omega) h11, hword (i := 8) (by omega) h24, ?_, fun k hk => ?_, ?_,
    fun k hk => absurd hk (by omega), ?_, ?_, ?_⟩
  · rw [hm₃.regs .X19 _ h19']
    simp only [Sym.eval, Env.base_ofMachine_eq, regs0, List.getElem?_cons_zero, Option.map_some,
      Option.getD_some, BitVec.ofInt_ofNat, ad_add]
  · rw [hm₃.regs .X20 _ h20']
    exact inp_eq m₀
  · rw [hm₃.regs .X12 _ h12]
    simp [Sym.eval, Env.base_ofMachine_eq, regs0, ad_add]
  · have := hm₃.regs .X23 _ h23
    simp only [Sym.eval, UnOp.apply, low_W32, ext_W32,
      load_word P C₂.same (i := 8) (by omega) (base1_regs0 (8 * 8))] at this
    show (st₃.data.regs.getXReg .X23).toBitVec.toNat = _
    rw [this]
    simp only [BitVec.toNat_setWidth]
    have : (w 8).toNat = (w 8).toBitVec.toNat := rfl
    omega
  · have := copy_word P hm₃ (rd := 0) (od := 8 + 8 * k) rfl (by omega) (i := 4 + k) (by omega)
      (rs := 1) (os := 8 * (4 + k)) (fun t _ => base1_regs0 _) C₂.same (st1'_msg k hk)
    rw [ad_add] at this
    rwa [show fb + 8 + 8 * k = fb + (8 + 8 * k) by omega]
  · intro t ht
    simp only [List.length_take, NativeRustc.length_wordBytes] at ht
    have hg := hm₃.get?_load (r := 0) rfl (by omega) (st1'_li t (by omega)) (by omega) (le_refl 8)
    rw [ad_add, show fb + (44 + t) = fb + 44 + t by omega, base1_regs0, ← addr_add_addr,
      Env.ofMachine_mem0, P.words_at C₂.same (i := 8) (by omega) t (by rw [NativeRustc.length_wordBytes]; omega)] at hg
    rw [ad_add, hg]
    simp
  · rw [hm₃.regs .X21 _ st1'_x21]
    simp only [Sym.eval, Env.base_ofMachine_eq, regs0, List.getElem?_cons_zero, Option.map_some,
      Option.getD_some, BitVec.ofInt_ofNat, ad_add]
  · rw [hm₃.regs .X13 _ st1'_x13]
    rfl
  · exact hm₃.regs .X14 _ st1'_x14

end NativeRustcArm.Xmss.XmssVerify
