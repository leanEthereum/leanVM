module

public import NativeRustcX64.LayerRead.Head
meta import NativeRustcX64.LayerRead.Inv
meta import NativeRustcX64.Code.Xmss.LayerRead

/-! # Reading the 58 chain values, two per iteration -/

namespace NativeRustcX64.Xmss.LayerRead

open NativeRustcX64.Sym

set_option Elab.async false

@[expose] public def stL : SState := init [16, 48, 32] [(.r14, .ptr 0 0)] [] []
  [(.bin .add .W64 (.reg .r11) (.reg .rcx), (1, 0)),
    (.bin .add .W64 (.reg .rsi) (.reg .rcx), (2, 0)),
    (.bin .add .W64 (.lit 16) (.bin .add .W64 (.reg .r11) (.reg .rcx)), (1, 16))]

sym_block b2_execL := exec b2 stL
@[expose] public def stL1 : SState := ((exec b2 stL).getD (stL, .fall)).1
sym_block b3_execL := exec b3 stL1
@[expose] public def stL2 : SState := ((exec b3 stL1).getD (stL1, .fall)).1
sym_block b4_execL := exec b4 stL2
@[expose] public def stL3 : SState := ((exec b4 stL2).getD (stL2, .fall)).1

theorem stL3_chain : ∀ t < 32,
    findWrite 2 (0 + t) stL3.mem = some (.load 1 (16 + 8 * (t / 8)) 8, t % 8) := by
  decide +kernel
theorem stL3_writes : writesBelow stL3 [(0, 16), (2, 32)] = true := by decide +kernel
theorem stL3_keeps : ∀ r ∈ [Reg64.r11, .rax, .rsi, .rsp],
    stL3.reg r = some (.reg r) := by decide +kernel
theorem stL3_regs :
    stL3.reg .r14 = some (.ptr 0 0) ∧
    stL3.reg .r12 = some (.bin .add .W64 (.lit (2 ^ 64 - 32)) (.reg .r12)) ∧
    stL3.reg .rbx = some (.reg .r12) ∧
    stL3.reg .rbp = some (.bin .add .W64 (.reg .r12) (.lit (2 ^ 64 - 48))) ∧
    stL3.reg .r13 = some (.bin .add .W64 (.lit 16) (.bin .add .W64 (.reg .r11) (.reg .rcx))) ∧
    stL3.reg .r15 = some (.bin .add .W64 (.lit 48) (.bin .add .W64 (.reg .r11) (.reg .rcx))) ∧
    stL3.reg .rdi = some (.bin .add .W64 (.lit 2) (.reg .rdi)) ∧
    stL3.reg .rcx = some (.bin .add .W64 (.lit 32) (.reg .rcx)) ∧
    stL3.reg .rdx = some (.bin .add .W64 (.lit (2 ^ 64 - 2)) (.reg .rdx)) := by decide +kernel

@[expose] public def envL (m₀ m : MachineData) (i : Nat) : Env :=
  Env.ofMachine m [(cur m₀, 16), (sig m₀ + BitVec.ofNat 64 (32 * i), 48),
    (base m₀ + BitVec.ofNat 64 (32 + 32 * i), 32)]

section
variable {m₀ m : MachineData} {i : Nat}

theorem envL_wf (P : Pre m₀) (hi : i < 29) (C : Common m₀ m) : (envL m₀ m i).WF :=
  Env.wf_of ⟨⟨P.curMapped.kept C.kept, P.curNW⟩,
    ⟨(P.sigMapped.sub (by omega)).kept C.kept, NoWrap.sub P.sigNW (by omega)⟩,
    ⟨(P.stackMapped.sub (by omega)).kept C.kept, P.baseNW.sub (by omega)⟩, trivial⟩
    (pairwise3 (P.curSig.sub_right P.sigNW (by omega) (by omega))
      (P.curF.sub_right P.baseNW (by omega) (by omega))
      ((P.sigF.sub_left P.sigNW (by omega) (by omega)).sub_right P.baseNW (by omega) (by omega)))

theorem match_envL [Labels] (h : LoopAt m₀ m i) : Match (envL m₀ m i) stL m := by
  unfold envL stL
  apply match_ofMachine
  · exact ⟨rfl, rfl, rfl, trivial⟩
  · exact ⟨h.r14.trans (by simp [Sym.eval, Env.base]), trivial⟩
  · exact trivial
  · exact trivial
  · refine ⟨?_, ?_, ?_, trivial⟩
    · simp [Sym.eval, BinOp.apply, low_W64, ext_W64, h.r11, h.rcx, Env.base]
    · simp [Sym.eval, BinOp.apply, low_W64, ext_W64, h.rsi, h.rcx, Env.base, addr_add_addr]
    · simp [Sym.eval, BinOp.apply, low_W64, ext_W64, h.r11, h.rcx, Env.base,
        add_comm]

theorem envL_outside (P : Pre m₀) (hi : i < 29) {o : Nat}
    (ho : o < 32 + 32 * i ∨ 64 + 32 * i ≤ o) (ho' : o < 1944) :
    (envL m₀ m i).Outside (base m₀ + BitVec.ofNat 64 o) :=
  Env.outside_of_apart ⟨P.curF.sub_right P.baseNW (by omega) (by omega),
    (P.sigF.sub_left P.sigNW (by omega) (by omega)).sub_right P.baseNW (by omega) (by omega),
    apart_offsets P.baseNW (by omega) (by omega) (by omega) (by omega) (by omega), trivial⟩

theorem keep_stackL [Labels] (P : Pre m₀) (hi : i < 29) {S : SState} {m' : MachineData}
    (hm : Match (envL m₀ m i) S m') {o : Nat} {bs : List UInt8}
    (ho : o + bs.length ≤ 32 + 32 * i ∨ 64 + 32 * i ≤ o) (ho' : o + bs.length ≤ 1944)
    (h : BytesAt m.dmem (base m₀ + BitVec.ofNat 64 o) bs) :
    BytesAt m'.dmem (base m₀ + BitVec.ofNat 64 o) bs :=
  hm.bytesAt_outside (fun t ht => by
    rw [addr_add_addr]
    exact envL_outside P hi (by omega) (by omega)) h

end

structure AfterTurn (m₀ m : MachineData) (i : Nat) : Prop where
  common : Common m₀ m
  r14 : reg m .r14 = cur m₀
  r11 : reg m .r11 = sig m₀
  r12 : reg m .r12 = BitVec.ofNat 64 (remaining m₀ - 32 * (i + 1))
  rax : reg m .rax = BitVec.ofNat 64 ((remaining m₀ - 16) / 16)
  rdx : reg m .rdx = BitVec.ofNat 64 ((remaining m₀ - 16) / 16 - 2 * (i + 1))
  rdi : reg m .rdi = BitVec.ofNat 64 (2 * (i + 1))
  rcx : reg m .rcx = BitVec.ofNat 64 (32 * (i + 1))
  rsi : reg m .rsi = base m₀ + 32#64
  rbx : reg m .rbx = BitVec.ofNat 64 (remaining m₀ - 32 * i)
  rbp : reg m .rbp = BitVec.ofNat 64 (remaining m₀ - (48 + 32 * i))
  r13 : reg m .r13 = sig m₀ + BitVec.ofNat 64 (16 + 32 * i)
  r15 : reg m .r15 = sig m₀ + BitVec.ofNat 64 (48 + 32 * i)
  chain : ∀ j < 2 * (i + 1),
    BytesAt m.dmem (base m₀ + BitVec.ofNat 64 (32 + 16 * j)) (chainSlot m₀ j)

theorem afterTurn [Labels] {m₀ m m' : MachineData} {i : Nat} (P : Pre m₀)
    (h : LoopAt m₀ m i) (hm : Match (envL m₀ m i) stL3 m') : AfterTurn m₀ m' i := by
  have C := h.common
  have hi := h.lt
  have hwf := envL_wf P hi C
  have hn := P.enough
  have hreg : ∀ r ∈ [Reg64.r11, .rax, .rsi, .rsp], reg m' r = reg m r :=
    fun r hr => hm.regs r _ (stL3_keeps r hr)
  obtain ⟨h14, h12, hbx, hbp, h13, h15, hdi, hcx, hdx⟩ := stL3_regs
  refine ⟨⟨(hreg .rsp (by simp)).trans C.rsp, ?_, C.kept.trans (hm.kept hwf),
    fun j hj => keep_stackL P hi hm (by simp [length_regBytes]; omega)
      (by simp [length_regBytes]; omega) (C.save j hj),
    keep_stackL (o := 24) P hi hm (by simp [length_regBytes])
      (by simp [length_regBytes]) C.output⟩,
    (hm.regs .r14 _ h14).trans (by simp [Sym.eval, Env.base, envL]),
    (hreg .r11 (by simp)).trans h.r11, ?_, (hreg .rax (by simp)).trans h.rax,
    ?_, ?_, ?_, (hreg .rsi (by simp)).trans h.rsi, (hm.regs .rbx _ hbx).trans h.r12,
    ?_, ?_, ?_, ?_⟩
  · refine (C.same.trans (hm.sameOutside_below hwf stL3_writes)).mono fun p hp => ?_
    rcases hp with hp | ⟨rb, hrb, b, sz, hb, hin⟩
    · exact hp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hrb
      rcases hrb with rfl | rfl
      · cases hb
        exact Or.inr hin
      · cases hb
        exact P.stack_scratch (by omega) hin
  · change m'.regs.get64 .r12 = _
    rw [hm.regs .r12 _ h12]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, envL, Env.ofMachine_regs,
      show m.regs.get64 .r12 = _ from h.r12]
    change BitVec.ofInt 64 (-32) + BitVec.ofNat 64 (remaining m₀ - 32 * i) = _
    rw [BitVec.add_comm]
    have he : remaining m₀ - 32 * i - 32 = remaining m₀ - 32 * (i + 1) := by omega
    have hs : BitVec.ofNat 64 (remaining m₀ - 32 * i) + BitVec.ofInt 64 (-32) =
        BitVec.ofNat 64 (remaining m₀ - 32 * i - 32) :=
      sub_nat (remaining m₀ - 32 * i) 32 (by omega)
    rwa [he] at hs
  · change m'.regs.get64 .rdx = _
    rw [hm.regs .rdx _ hdx]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, envL, Env.ofMachine_regs,
      show m.regs.get64 .rdx = _ from h.rdx]
    change BitVec.ofInt 64 (-2) + BitVec.ofNat 64 ((remaining m₀ - 16) / 16 - 2 * i) = _
    rw [BitVec.add_comm]
    have he : (remaining m₀ - 16) / 16 - 2 * i - 2 =
        (remaining m₀ - 16) / 16 - 2 * (i + 1) := by omega
    have hs : BitVec.ofNat 64 ((remaining m₀ - 16) / 16 - 2 * i) + BitVec.ofInt 64 (-2) =
        BitVec.ofNat 64 ((remaining m₀ - 16) / 16 - 2 * i - 2) :=
      sub_nat ((remaining m₀ - 16) / 16 - 2 * i) 2 (by omega)
    rwa [he] at hs
  · change m'.regs.get64 .rdi = _
    rw [hm.regs .rdi _ hdi]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, envL, Env.ofMachine_regs,
      show m.regs.get64 .rdi = _ from h.rdi]
    rw [← BitVec.ofNat_add]
    congr 1
    omega
  · change m'.regs.get64 .rcx = _
    rw [hm.regs .rcx _ hcx]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, envL, Env.ofMachine_regs,
      show m.regs.get64 .rcx = _ from h.rcx]
    rw [← BitVec.ofNat_add]
    congr 1
    omega
  · change m'.regs.get64 .rbp = _
    rw [hm.regs .rbp _ hbp]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, envL, Env.ofMachine_regs,
      show m.regs.get64 .r12 = _ from h.r12]
    change BitVec.ofNat 64 (remaining m₀ - 32 * i) + BitVec.ofInt 64 (-48) = _
    have he : remaining m₀ - 32 * i - 48 = remaining m₀ - (48 + 32 * i) := by omega
    have hs : BitVec.ofNat 64 (remaining m₀ - 32 * i) + BitVec.ofInt 64 (-48) =
        BitVec.ofNat 64 (remaining m₀ - 32 * i - 48) :=
      sub_nat (remaining m₀ - 32 * i) 48 (by omega)
    rwa [he] at hs
  · change m'.regs.get64 .r13 = _
    rw [hm.regs .r13 _ h13]
    simp [Sym.eval, BinOp.apply, low_W64, ext_W64, envL, h.r11, h.rcx,
      add_comm, BitVec.ofNat_add, BitVec.add_assoc]
  · change m'.regs.get64 .r15 = _
    rw [hm.regs .r15 _ h15]
    simp [Sym.eval, BinOp.apply, low_W64, ext_W64, envL, h.r11, h.rcx,
      add_comm, BitVec.ofNat_add, BitVec.add_assoc]
    rw [← BitVec.add_assoc, BitVec.add_comm 48#64, BitVec.add_assoc]
  · intro j hj
    by_cases hji : j < 2 * i
    · exact keep_stackL P hi hm (by rw [P.chainSlot_length (by omega)]; omega)
        (by rw [P.chainSlot_length (by omega)]; omega) (h.chain j hji)
    · obtain ⟨u, hu, rfl⟩ : ∃ u < 2, j = 2 * i + u := ⟨j - 2 * i, by omega, by omega⟩
      refine bytesAt_slice (by omega) fun t ht => ?_
      have hg := hm.get?_load (r := 2) rfl (by omega) (stL3_chain (16 * u + t) (by omega))
        (by omega) (le_refl 8)
      simp only [Nat.zero_add] at hg
      rw [addr_add_addr, show 32 + 16 * (2 * i + u) + t = 32 + 32 * i + (16 * u + t) by omega,
        ← addr_add_addr, hg,
        show 16 + 8 * ((16 * u + t) / 8) + (16 * u + t) % 8 = 16 + (16 * u + t) by omega]
      simp only [Env.base, envL, Env.ofMachine_regions, List.getElem?_cons_succ,
        List.getElem?_cons_zero, Option.map_some, Option.getD_some, Env.ofMachine_mem0,
        addr_add_addr]
      rw [show 32 * i + (16 + (16 * u + t)) = 16 + 16 * (2 * i + u) + t by omega,
        C.same _ (P.sig_not_scratch (by omega))]
      rfl

theorem turn [Host] {k : Nat} (hp : Placed code k) {m₀ : MachineData} (P : Pre m₀) {i : Nat}
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + b2Offset)) (h : LoopAt m₀ st.data i) :
    Eventually (step1 Host.exe) (fun st' => (st'.pc = Host.addrOf (k + b5Offset) ∧ LoopDone m₀ st'.data) ∨
      (i + 1 < 29 ∧ st'.pc = Host.addrOf (k + b2Offset) ∧ LoopAt m₀ st'.data (i + 1))) st := by
  have hi := h.lt
  have hn := P.enough
  have hlt := P.lengthLt
  have hwf := envL_wf P hi h.common
  have h2 : (SBool.cmp .eq .W64 (.bin .and .W64 (.reg .rdx) (.reg .rdx)) (.lit 0)).eval
      (envL m₀ st.data i) = false := by
    simp only [SBool.eval, CmpOp.apply, Sym.eval, BinOp.apply, low_W64, ext_W64,
      envL, Env.ofMachine_regs, h.rdx, BitVec.and_self]
    simp [BitVec.toNat_eq]
    omega
  refine cond_step (b2_in_code.trans hp.1 (List.cons_ne_nil _ _)) b2_execL hwf hpc (match_envL h)
    h2 fun st₁ hpc₁ hm₁ => ?_
  have h3 : (SBool.cmp .eq .W64 (.bin .add .W64 (.reg .rdi) (.lit 1))
      (.reg .rax)).eval (envL m₀ st.data i) = false := by
    simp only [SBool.eval, CmpOp.apply, Sym.eval, BinOp.apply, low_W64, ext_W64,
      envL, Env.ofMachine_regs, h.rdi, h.rax]
    simp [BitVec.toNat_eq, ← BitVec.ofNat_add]
    omega
  refine cond_step (b3_in_code.trans hp.1 (List.cons_ne_nil _ _)) b3_execL hwf hpc₁ hm₁ h3
    fun st₂ hpc₂ hm₂ => ?_
  refine exec_at (b4_in_code.trans hp.1 (List.cons_ne_nil _ _)) b4_execL hwf
    (fun _ h => nomatch h) hpc₂ hm₂ fun st₃ hm₃ hpc₃ => ?_
  have hm : Match (envL m₀ st.data i) stL3 st₃.data := by unfold stL3; rw [b4_execL]; exact hm₃
  have A := afterTurn P h hm
  refine .done _ ?_
  have hc : (SBool.not (SBool.cmp .eq .W64 (.bin .add .W64 (.lit 2) (.reg .rdi)) (.lit 58))).eval
      (envL m₀ st.data i) = decide (i + 1 < 29) := by
    simp only [SBool.eval, CmpOp.apply, Sym.eval, BinOp.apply, low_W64, ext_W64,
      envL, Env.ofMachine_regs, h.rdi]
    by_cases hnext : i + 1 < 29
    · simp only [hnext, decide_true, Bool.not_eq_true']
      simp [BitVec.toNat_eq, ← BitVec.ofNat_add]
      omega
    · simp only [hnext, decide_false, Bool.not_eq_false']
      simp [BitVec.toNat_eq, ← BitVec.ofNat_add]
      omega
  simp only [PcOk, hc] at hpc₃
  by_cases hnext : i + 1 < 29
  · simp only [hnext, decide_true, ite_true] at hpc₃
    exact Or.inr ⟨hnext, hpc₃.trans (hp.label label_2_at),
      ⟨A.common, hnext, A.r14, A.r11, A.r12, A.rax, A.rdx, A.rdi, A.rcx, A.rsi, A.chain⟩⟩
  · simp only [hnext, decide_false, Bool.false_eq_true, ite_false] at hpc₃
    have hi' : i = 28 := by omega
    subst hi'
    exact Or.inl ⟨hpc₃,
      ⟨A.common, A.r14, A.r11, A.r12, A.r13, A.r15, A.rbx, A.rbp, A.rsi, A.chain⟩⟩

public theorem loop [Host] {k : Nat} (hp : Placed code k) {m₀ : MachineData} (P : Pre m₀)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + b2Offset)) (h : LoopAt m₀ st.data 0) :
    Eventually (step1 Host.exe) (fun st' => st'.pc = Host.addrOf (k + b5Offset) ∧ LoopDone m₀ st'.data)
      st :=
  Sym.loop (I := fun n s => ∃ i, i + n = 29 ∧ 0 < n ∧ s.pc = Host.addrOf (k + b2Offset) ∧
      LoopAt m₀ s.data i)
    (fun n s ⟨i, hn, hn0, hpc, h⟩ => NativeRustcX64.Eventually.mono (turn hp P hpc h)
      fun s' h' => by
      rcases h' with h' | ⟨hlt, hpc', h'⟩
      · exact Or.inl h'
      · exact Or.inr ⟨n - 1, by omega, i + 1, by omega, by omega, hpc', h'⟩)
    (n := 29) ⟨0, rfl, by decide, hpc, h⟩

end NativeRustcX64.Xmss.LayerRead
