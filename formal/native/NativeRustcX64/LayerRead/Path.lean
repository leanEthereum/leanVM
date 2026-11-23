module

public import NativeRustcX64.Code.Common.Memcpy.Names

public import NativeRustcX64.LayerRead.Mid
public import NativeRustcX64.LayerRead.PathExec
public import NativeRustcX64.LayerRead.Head

/-! # The authentication path and final slice-cursor update -/

namespace NativeRustcX64.Xmss.LayerRead

open NativeRustcX64.Sym

set_option Elab.async false

@[expose] public def envP [Labels] (m₀ m : MachineData) (ret : BitVec 64) : Env :=
  Env.ofMachine m [(base m₀, 1944), (cur m₀, 16), (sig m₀, 1200), (gotAddr "memcpy", 8)]
    (fun _ => 0) ret

theorem mask_bound (x : BitVec 64) (h : 256 ≤ x.toNat) :
    256 ≤ (x &&& BitVec.ofInt 64 (-16)).toNat := by
  obtain ⟨i, hi, hx⟩ := Nat.exists_ge_and_testBit_of_ge_two_pow (n := 8) h
  have hp := Nat.ge_two_pow_of_testBit hx
  have hi64 : i < 64 := by
    by_contra hn
    have hl := x.isLt
    have hh : 2 ^ 64 ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hm : ∀ j < 64, 8 ≤ j → Nat.testBit (2 ^ 64 - 16) j = true := by decide +kernel
  have hy : ((x &&& BitVec.ofInt 64 (-16)).toNat).testBit i = true := by
    rw [BitVec.toNat_and, Nat.testBit_and, hx]
    change (true && Nat.testBit (2 ^ 64 - 16) i) = true
    rw [hm i hi64 hi]
    rfl
  exact (Nat.pow_le_pow_right (by decide) hi).trans (Nat.ge_two_pow_of_testBit hy)

theorem small_false [Labels] {env : Env} {v : Nat} (hx : env.regs .rbp = BitVec.ofNat 64 v)
    (h : 256 ≤ v) (hv : v < 2 ^ 64) :
    (SBool.or (SBool.cmp .ult .W64 (.reg .rbp) (.lit 15))
      (SBool.cmp .eq .W64 (.reg .rbp) (.lit 15))).eval env = false := by
  simp only [SBool.eval, CmpOp.apply, Sym.eval, low_W64, hx]
  simp [BitVec.ult, BitVec.toNat_eq]
  omega

theorem masked_false [Labels] {env : Env} {r : Reg64} {v N : Nat}
    (hx : env.regs r = BitVec.ofNat 64 v) (h : 256 ≤ v) (hv : v < 2 ^ 64) (hN : N < 256) :
    (SBool.cmp .eq .W64 (.bin .and .W64 (.reg r) (.lit (2 ^ 64 - 16))) (.lit N)).eval env = false := by
  have hb := mask_bound (BitVec.ofNat 64 v)
    (by simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv] using h)
  change 256 ≤ (BitVec.ofNat 64 v &&& BitVec.ofNat 64 (2 ^ 64 - 16)).toNat at hb
  simp only [SBool.eval, CmpOp.apply, Sym.eval, BinOp.apply, low_W64, ext_W64]
  rw [hx]
  simp only [beq_eq_false_iff_ne]
  intro heq
  have he := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_ofNat] at he
  change (BitVec.ofNat 64 v &&& BitVec.ofNat 64 (2 ^ 64 - 16)).toNat = N % 2 ^ 64 at he
  omega

section
variable [Labels] {m₀ m : MachineData} {ret : BitVec 64}

theorem envP_wf (P : Pre m₀) (G : ParserGot m₀) (C : Common m₀ m) :
    (envP m₀ m ret).WF := by
  have hg := G.1 "memcpy" (by simp)
  exact Env.wf_of ⟨⟨P.stackMapped.kept C.kept, P.baseNW⟩, ⟨P.curMapped.kept C.kept, P.curNW⟩,
    ⟨P.sigMapped.kept C.kept, P.sigNW⟩,
    ⟨(G.mapped (by simp)).kept C.kept, hg.2.1⟩, trivial⟩
    (pairwise4 P.curF.symm P.sigF.symm hg.2.2.1.symm P.curSig
      (hg.2.2.2 (cur m₀, 16) (by simp)).symm
      (hg.2.2.2 (sig m₀, 1200) (by simp)).symm)

theorem match_envP (P : Pre m₀) (G : ParserGot m₀) (h : MidAt m₀ m) :
    Match (envP m₀ m ret) stP0 m := by
  have C := h.common
  unfold envP stP0
  apply Match.withKnownBytes
  · apply match_ofMachine
    · exact ⟨rfl, rfl, rfl, rfl, trivial⟩
    · exact ⟨C.rsp.trans (by simp [Sym.eval]), h.r14.trans (by simp [Sym.eval]),
        h.r13.trans (by simp [Sym.eval, Env.base]), h.r15.trans (by simp [Sym.eval, Env.base]),
        trivial⟩
    · exact trivial
    · exact trivial
    · exact ⟨by simp [Sym.eval, Env.base, gotAddr], trivial⟩
  · intro i hi
    simpa [Sym.eval, Env.base] using P.got_byte G (C.same.mono fun _ => Or.inl) hi

end

theorem pathCall [Labels] {m₀ m m' : MachineData} {ret : BitVec 64} (P : Pre m₀)
    (G : ParserGot m₀) (h : MidAt m₀ m)
    (hm : Match (envP m₀ m ret) stP17 m') : PathCall m₀ m' := by
  have C := h.common
  have hwf := envP_wf (ret := ret) P G C
  have hr0 : (envP m₀ m ret).regions[0]? = some (base m₀, 1944) := rfl
  have hfr : ∀ {o : Nat} {bs : List UInt8}, o + bs.length ≤ 1944 →
      firstOverlap 0 o bs.length stP17.mem = none →
      BytesAt m.dmem (base m₀ + BitVec.ofNat 64 o) bs →
      BytesAt m'.dmem (base m₀ + BitVec.ofNat 64 o) bs :=
    fun hle hc h0 => hm.bytesAt_keep hr0 hle hc h0
  obtain ⟨hdi, hsi, hdx, hsp, h14, hbx⟩ := stP17_regs
  have hout : (envP m₀ m ret).load 0 24 8 = out m₀ := by
    rw [Env.load_of_bytesAt (length_regBytes _) (by simpa [envP] using C.output), ofBytes_regBytes]
  have hsame : SameOutside m.dmem m'.dmem
      (fun p => InRange (base m₀) 288 p ∨ InRange (cur m₀) 16 p) :=
    (hm.sameOutside_below hwf stP17_writes).mono fun p ⟨rb, hrb, b, sz, hb, hin⟩ => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hrb
      rcases hrb with rfl | rfl
      · cases hb
        exact Or.inl hin
      · cases hb
        exact Or.inr hin
  refine ⟨⟨(hm.regs .rsp _ hsp).trans (by simp [Sym.eval, envP]),
    (C.same.trans hsame).mono fun p hp => ?_, C.kept.trans (hm.kept hwf),
    fun j hj => hfr (by rw [length_regBytes]; omega)
      (by rw [length_regBytes]; exact stP17_save j hj) (C.save j hj),
    hfr (by rw [length_regBytes]; omega) (by rw [length_regBytes]; exact stP17_output) C.output⟩,
    (hm.regs .r14 _ h14).trans hout, (hm.regs .rdi _ hdi).trans hout,
    (hm.regs .rsi _ hsi).trans (by simp [Sym.eval, envP]), hm.regs .rdx _ hdx, ?_, ?_,
    hfr (by rw [length_regBytes]; omega) (by rw [length_regBytes]; exact stP17_input) h.input,
    hfr (by rw [length_chainBytes P]; omega) (by rw [length_chainBytes P]; exact stP17_chain)
      h.chain, ?_, hm.regs .rbx _ hbx⟩
  · rcases hp with hp | hp | hp
    · exact hp
    · exact P.stack_scratch (o := 0) (s := 288) (by omega) (by simpa using hp)
    · exact Or.inr hp
  · simpa only [regBytes, Sym.eval, Env.base, envP, Env.ofMachine_regions, List.getElem?_cons_succ,
      List.getElem?_cons_zero, Option.map_some, Option.getD_some, BitVec.ofInt_ofNat] using bytesAt_add_zero
      (hm.bytesAt_write (r := 1) (o := 0) (n := 8) rfl (by omega) stP17_cursor)
  · have hl := hm.bytesAt_write (r := 1) (o := 8) (n := 8) rfl (by omega) stP17_length
    have he : (Sym.bin .add .W64 (.lit (2 ^ 64 - 288))
        (.bin .add .W64 (.lit (2 ^ 64 - 16)) (.reg .rbx))).eval (envP m₀ m ret) =
        BitVec.ofNat 64 (remaining m₀ - 1200) := by
      simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, envP, Env.ofMachine_regs,
        show m.regs.get64 .rbx = _ from h.rbx]
      change BitVec.ofInt 64 (-288) + (BitVec.ofInt 64 (-16) +
        BitVec.ofNat 64 (remaining m₀ - 896)) = _
      rw [← BitVec.add_assoc,
        show BitVec.ofInt 64 (-288) + BitVec.ofInt 64 (-16) = BitVec.ofInt 64 (-304) from rfl,
        BitVec.add_comm]
      have heq : remaining m₀ - 896 - 304 = remaining m₀ - 1200 := by omega
      have hs : BitVec.ofNat 64 (remaining m₀ - 896) + BitVec.ofInt 64 (-304) =
          BitVec.ofNat 64 (remaining m₀ - 896 - 304) :=
        sub_nat (remaining m₀ - 896) 304 (by have := P.enough; omega)
      rwa [heq] at hs
    rw [he] at hl
    exact hl
  · refine bytesAt_flatten 16 (fun j hj => P.pathSlot_length hj) fun j hj => ?_
    rw [addr_add_addr]
    refine bytesAt_slice (by omega) fun t ht => ?_
    rw [addr_add_addr]
    have hg := hm.get?_load (r := 0) hr0 (by omega) (stP17_path (16 * j + t) (by omega))
      (by omega) (le_refl 8)
    rw [show 32 + (16 * j + t) = 32 + 16 * j + t by omega] at hg
    rw [hg, show 944 + 8 * ((16 * j + t) / 8) + (16 * j + t) % 8 = 944 + 16 * j + t by omega]
    simp only [Env.base_ofMachine_eq, envP, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.map_some, Option.getD_some, Env.ofMachine_mem0]
    rw [C.same _ (P.sig_not_scratch (by omega))]
    rfl

theorem pathLast [Host] {k : Nat} (hp : Placed code k) {m₀ m : MachineData} (P : Pre m₀)
    (G : ParserGot m₀) (h : MidAt m₀ m) {st : MachineState}
    (hpc8 : st.pc = Host.addrOf (k + b13Offset + b13.length))
    (hm8 : Match (envP m₀ m (Host.addrOf (k + b23Offset)).toBitVec) stP8 st.data)
    {R : MachineState → Prop}
    (cont : ∀ st' : MachineState, st'.pc = Labels.label NativeRustcX64.Common.Memcpy.entryLabel →
      retOf st'.data = Host.addrOf (k + b23Offset) → PathCall m₀ st'.data →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have hwf := envP_wf (ret := (Host.addrOf (k + b23Offset)).toBitVec) P G h.common
  have hn := P.enough
  have hlt := P.lengthLt
  have hx : (envP m₀ m (Host.addrOf (k + b23Offset)).toBitVec).regs .rbp =
      BitVec.ofNat 64 (remaining m₀ - 944) := h.rbp
  have hy : (envP m₀ m (Host.addrOf (k + b23Offset)).toBitVec).regs .r12 =
      BitVec.ofNat 64 (remaining m₀ - 928) := h.r12
  refine cond_step (b14_in_code.trans hp.1 (List.cons_ne_nil _ _)) b14_execP hwf
    (hpc8.trans rfl) hm8 (masked_false hy (by omega) (by omega) (by decide)) fun s9 hpc9 hm9 => ?_
  refine cond_step (b15_in_code.trans hp.1 (List.cons_ne_nil _ _)) b15_execP hwf
    (hpc9.trans rfl) hm9 (masked_false hx (by omega) (by omega) (by decide)) fun s10 hpc10 hm10 => ?_
  refine cond_step (b16_in_code.trans hp.1 (List.cons_ne_nil _ _)) b16_execP hwf
    (hpc10.trans rfl) hm10 (masked_false hx (by omega) (by omega) (by decide)) fun s11 hpc11 hm11 => ?_
  refine cond_step (b17_in_code.trans hp.1 (List.cons_ne_nil _ _)) b17_execP hwf
    (hpc11.trans rfl) hm11 (masked_false hx (by omega) (by omega) (by decide)) fun s12 hpc12 hm12 => ?_
  refine cond_step (b18_in_code.trans hp.1 (List.cons_ne_nil _ _)) b18_execP hwf
    (hpc12.trans rfl) hm12 (masked_false hx (by omega) (by omega) (by decide)) fun s13 hpc13 hm13 => ?_
  refine cond_step (b19_in_code.trans hp.1 (List.cons_ne_nil _ _)) b19_execP hwf
    (hpc13.trans rfl) hm13 (masked_false hx (by omega) (by omega) (by decide)) fun s14 hpc14 hm14 => ?_
  refine cond_step (b20_in_code.trans hp.1 (List.cons_ne_nil _ _)) b20_execP hwf
    (hpc14.trans rfl) hm14 (masked_false hx (by omega) (by omega) (by decide)) fun s15 hpc15 hm15 => ?_
  refine cond_step (b21_in_code.trans hp.1 (List.cons_ne_nil _ _)) b21_execP hwf
    (hpc15.trans rfl) hm15 (masked_false hx (by omega) (by omega) (by decide)) fun s16 hpc16 hm16 => ?_
  refine call_step (b22_in_code.trans hp.1 (List.cons_ne_nil _ _)) b22_execP hwf rfl
    (hpc16.trans rfl) hm16 fun s hpc' hm => cont s hpc'.1 (hpc'.2.trans rfl) ?_
  exact pathCall P G h hm

public theorem path [Host] {k : Nat} (hp : Placed code k) {m₀ : MachineData} (P : Pre m₀)
    (G : ParserGot m₀) {st : MachineState} (hpc : st.pc = Host.addrOf (k + b6Offset))
    (h : MidAt m₀ st.data) {R : MachineState → Prop}
    (cont : ∀ st' : MachineState, st'.pc = Labels.label NativeRustcX64.Common.Memcpy.entryLabel →
      retOf st'.data = Host.addrOf (k + b23Offset) → PathCall m₀ st'.data →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have hwf := envP_wf (ret := (Host.addrOf (k + b23Offset)).toBitVec) P G h.common
  have hn := P.enough
  have hlt := P.lengthLt
  have hx : (envP m₀ st.data (Host.addrOf (k + b23Offset)).toBitVec).regs .rbp =
      BitVec.ofNat 64 (remaining m₀ - 944) := h.rbp
  refine cond_step (b6_in_code.trans hp.1 (List.cons_ne_nil _ _)) b6_execP hwf hpc
    (match_envP P G h) (small_false hx (by omega) (by omega)) fun s1 hpc1 hm1 => ?_
  refine cond_step (b7_in_code.trans hp.1 (List.cons_ne_nil _ _)) b7_execP hwf
    (hpc1.trans rfl) hm1 (masked_false hx (by omega) (by omega) (by decide)) fun s2 hpc2 hm2 => ?_
  refine cond_step (b8_in_code.trans hp.1 (List.cons_ne_nil _ _)) b8_execP hwf
    (hpc2.trans rfl) hm2 (masked_false hx (by omega) (by omega) (by decide)) fun s3 hpc3 hm3 => ?_
  refine cond_step (b9_in_code.trans hp.1 (List.cons_ne_nil _ _)) b9_execP hwf
    (hpc3.trans rfl) hm3 (masked_false hx (by omega) (by omega) (by decide)) fun s4 hpc4 hm4 => ?_
  refine cond_step (b10_in_code.trans hp.1 (List.cons_ne_nil _ _)) b10_execP hwf
    (hpc4.trans rfl) hm4 (masked_false hx (by omega) (by omega) (by decide)) fun s5 hpc5 hm5 => ?_
  refine cond_step (b11_in_code.trans hp.1 (List.cons_ne_nil _ _)) b11_execP hwf
    (hpc5.trans rfl) hm5 (masked_false hx (by omega) (by omega) (by decide)) fun s6 hpc6 hm6 => ?_
  refine cond_step (b12_in_code.trans hp.1 (List.cons_ne_nil _ _)) b12_execP hwf
    (hpc6.trans rfl) hm6 (masked_false hx (by omega) (by omega) (by decide)) fun s7 hpc7 hm7 => ?_
  refine cond_step (b13_in_code.trans hp.1 (List.cons_ne_nil _ _)) b13_execP hwf
    (hpc7.trans rfl) hm7 (masked_false hx (by omega) (by omega) (by decide)) fun s8 hpc8 hm8 => ?_
  exact pathLast hp P G h hpc8 hm8 cont

end NativeRustcX64.Xmss.LayerRead
