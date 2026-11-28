module

public import NativeRustcArm.LayerRead.Head
meta import NativeRustcArm.Code.Xmss.LayerRead

/-!
# `LayerSignature::read`: the 58 chain values

Each iteration copies the next 16-byte chain value, advances the descriptor,
and decreases its remaining length. The loop counter is independent of the
slice length, whose lower bound discharges every panic branch.
-/

namespace NativeRustcArm.Xmss.LayerRead

open NativeRustcArm.Sym NativeRustcArm

set_option Elab.async false

/-- The symbolic state at the loop's head. -/
def stL : SState := init [(16, false), (32, false), (16, false)] .sp [(.X20, .ptr 0 0)]
  (aliases := [(.bin .add .W64 (.reg .X21) (.reg .X23), (1, 0)),
    (.bin .add .W64 (.reg .X9) (.reg .X23), (2, 0))])

sym_block b2_execL := exec b2 stL

/-- The symbolic state after block 2. -/
def stL1 : SState := ((exec b2 stL).getD (stL, .fall)).1

sym_block b3_execL := exec b3 stL1

/-- The symbolic state after block 3. -/
def stL2 : SState := ((exec b3 stL1).getD (stL, .fall)).1

theorem stL2_chain : ∀ t < 16,
    findWrite 2 (0 + t) stL2.mem = some (.load 1 (16 + 8 * (t / 8)) 8, t % 8) := by
  decide +kernel

theorem stL2_writes : writesIn stL2 [0, 2] = true := by decide +kernel

/-- The environment of turn `i`. -/
def envL (m₀ m : MachineData) (i : Nat) : Env :=
  Env.ofMachine m [(cur m₀, 16), (sig m₀ + BitVec.ofNat 64 (16 * i), 32),
    (frame m₀ + BitVec.ofNat 64 (928 + 16 * i), 16)]

section
variable {m₀ m : MachineData} {i : Nat}

theorem envL_wf (P : Pre m₀) (hi : i < 58) (C : Common m₀ m) : (envL m₀ m i).WF := by
  exact Env.wf_of ⟨⟨P.curMapped.kept C.kept, P.curNW⟩,
    ⟨(P.sigMapped.sub (by omega)).kept C.kept, NoWrap.sub P.sigNW (by omega)⟩,
    ⟨(P.frameMapped.sub (by unfold layerReadStack; omega)).kept C.kept,
      P.frameNW.sub (by unfold layerReadStack; omega)⟩, trivial⟩
    (pairwise3 (P.curSig.sub_right P.sigNW (by omega) (by omega))
      (P.curF.sub_right P.frameNW (by unfold layerReadStack; omega) (by omega))
      ((P.sigF.sub_left P.sigNW (by omega) (by omega)).sub_right P.frameNW
        (by unfold layerReadStack; omega) (by omega)))

theorem match_envL [Labels] (h : LoopAt m₀ m i) : Match (envL m₀ m i) stL m := by
  unfold envL stL
  apply match_ofMachine
  · exact And.intro rfl (And.intro (by simp) (And.intro rfl (And.intro (by simp)
      (And.intro rfl (And.intro (by simp) trivial)))))
  · rfl
  · exact ⟨h.common.x20.trans (by simp [Sym.eval, Env.base]), trivial⟩
  · exact trivial
  · exact trivial
  · refine ⟨?_, ?_, trivial⟩
    · simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs, h.common.x21, h.x23]
      simp [Env.base, Env.ofMachine_regions]
    · simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs, h.x9, h.x23]
      simp only [Env.base, Env.ofMachine_regions]
      rw [addr_add_addr]
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.map_some, Option.getD_some]
      rw [show (BitVec.ofInt 64 (0 : Int)) = BitVec.ofNat 64 0 from rfl, addr_add_addr]
      congr 2

/-- A byte of the frame outside turn `i`'s slot is outside the turn's regions. -/
theorem envL_outside (P : Pre m₀) (hi : i < 58) {o : Nat} (ho : o < 928 + 16 * i ∨ 944 + 16 * i ≤ o)
    (ho' : o < 1936) : (envL m₀ m i).Outside (frame m₀ + BitVec.ofNat 64 o) := by
  exact Env.outside_of_apart ⟨P.curF.sub_right P.frameNW (by unfold layerReadStack; omega) (by omega),
    (P.sigF.sub_left P.sigNW (by omega) (by omega)).sub_right P.frameNW
      (by unfold layerReadStack; omega) (by omega),
    apart_offsets P.frameNW (by omega) (by unfold layerReadStack; omega)
      (by unfold layerReadStack; omega) (by omega) (by omega), trivial⟩

/-- Bytes of the frame outside turn `i`'s slot are kept. -/
theorem keep_frameL [Labels] (P : Pre m₀) (hi : i < 58) {S : SState} {m' : MachineData}
    (hm : Match (envL m₀ m i) S m') {o : Nat} {bs : List UInt8}
    (ho : o + bs.length ≤ 928 + 16 * i ∨ 944 + 16 * i ≤ o) (ho' : o + bs.length ≤ 1936)
    (h : BytesAt m.dmem (frame m₀ + BitVec.ofNat 64 o) bs) :
    BytesAt m'.dmem (frame m₀ + BitVec.ofNat 64 o) bs :=
  hm.bytesAt_outside (fun t ht => by
    rw [addr_add_addr]
    exact envL_outside P hi (by omega) (by omega)) h

end

/-- What a turn leaves: the head's facts for the next value. -/
structure AfterTurn (m₀ m : MachineData) (i : Nat) : Prop where
  common : Common m₀ m
  x8 : (m.regs.getXReg .X8).toBitVec = BitVec.ofNat 64 ((remaining m₀ - 16) / 16 - (i + 1))
  x9 : (m.regs.getXReg .X9).toBitVec = frame m₀ + BitVec.ofNat 64 928
  x22 : (m.regs.getXReg .X22).toBitVec = BitVec.ofNat 64 (remaining m₀ - 16 * (i + 1))
  x23 : (m.regs.getXReg .X23).toBitVec = BitVec.ofNat 64 (16 * (i + 1))
  x24 : (m.regs.getXReg .X24).toBitVec = BitVec.ofNat 64 (remaining m₀ - (32 + 16 * i))
  chain : ∀ j < i + 1, BytesAt m.dmem (frame m₀ + BitVec.ofNat 64 (928 + 16 * j)) (chainSlot m₀ j)

theorem ofNat_add_lit (x c : Nat) :
    BitVec.ofNat 64 x + BitVec.ofNat 64 c = BitVec.ofNat 64 (x + c) := (BitVec.ofNat_add x c).symm

/-- The machine state after a turn. -/
theorem afterTurn [Labels] {m₀ m m' : MachineData} {i : Nat} (P : Pre m₀) (hi : i < 58)
    (h : LoopAt m₀ m i) (hm : Match (envL m₀ m i) stL2 m') : AfterTurn m₀ m' i := by
  have C := h.common
  have hwf := envL_wf P hi C
  have hn := P.remaining
  have hreg : ∀ r, stL2.reg r = some (.reg r) →
      (m'.regs.getXReg r).toBitVec = (m.regs.getXReg r).toBitVec := fun r hr => hm.regs r _ hr
  refine ⟨⟨(hreg .X19 (by decide +kernel)).trans C.x19,
    (hm.regs .X20 (.ptr 0 0) (by decide +kernel)).trans (by simp [Sym.eval, Env.base, envL, cur]),
    (hreg .X21 (by decide +kernel)).trans C.x21,
    fun r hr => ?_, (hreg .X29 (by decide +kernel)).trans C.x29,
    hm.sp.trans ((congrArg (Sym.eval _) (show stL2.sp = .sp by decide +kernel)).trans C.sp),
    ?_, C.kept.trans (hm.kept hwf),
    fun j hj hj3 => keep_frameL P hi hm (by simp [length_regBytes]; omega)
      (by simp [length_regBytes]; omega) (C.save j hj hj3)⟩,
    ?_, (hreg .X9 (by decide +kernel)).trans h.x9, ?_, ?_, ?_, ?_⟩
  · have hr' := C.keep r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [← hr']
    rcases hr with rfl | rfl | rfl | rfl <;>
      exact UInt64.toBitVec_inj.mp (hreg _ (by decide +kernel))
  · refine (C.same.trans (hm.sameOutside_in hwf stL2_writes)).mono fun p hp => ?_
    rcases hp with hp | ⟨r, hr, b, sz, hb, hin⟩
    · exact hp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · simp only [envL, Env.ofMachine_regions] at hb
        cases hb
        exact Or.inr hin
      · simp only [envL, Env.ofMachine_regions] at hb
        cases hb
        exact Or.inl (inRange_sub P.frameNW (by unfold layerReadStack; omega) hin)
  · rw [hm.regs .X8 (.bin .sub .W64 (.reg .X8) (.lit 1)) (by decide +kernel)]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs, envL, h.x8]
    rw [ofNat_sub _ _ (by omega)]
    rw [Nat.sub_sub]
  · rw [hm.regs .X22 (.bin .sub .W64 (.reg .X22) (.lit 16)) (by decide +kernel)]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs, envL, h.x22]
    rw [ofNat_sub _ _ (by omega)]
    rw [Nat.sub_sub, show 16 * i + 16 = 16 * (i + 1) by omega]
  · rw [hm.regs .X23 (.bin .add .W64 (.reg .X23) (.lit 16)) (by decide +kernel)]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs, envL, h.x23, ofNat_add_lit]
    rw [show 16 * i + 16 = 16 * (i + 1) by omega]
  · rw [hm.regs .X24 (.bin .sub .W64 (.reg .X22) (.lit 32)) (by decide +kernel)]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs, envL, h.x22]
    rw [ofNat_sub _ _ (by omega)]
    rw [Nat.sub_sub, show 16 * i + 32 = 32 + 16 * i by omega]
  · intro j hj
    by_cases hji : j < i
    · have hl : (chainSlot m₀ j).length = 16 := by
        simp [chainSlot, NativeRustc.slice, LayerReadPre.bytes, length_bytesOf]
        omega
      exact keep_frameL P hi hm (by rw [hl]; omega) (by rw [hl]; omega) (h.chain j hji)
    · have hji' : j = i := by omega
      subst hji'
      refine bytesAt_slice (by omega) fun t ht => ?_
      have hg := hm.get?_load (r := 2) rfl (by omega) (stL2_chain t ht) (by omega) (le_refl 8)
      simp only [Nat.zero_add] at hg
      rw [hg, show 16 + 8 * (t / 8) + t % 8 = 16 + t by omega]
      simp only [Env.base, envL, Env.ofMachine_regions, List.getElem?_cons_succ,
        List.getElem?_cons_zero, Option.map_some, Option.getD_some, Env.ofMachine_mem0,
        addr_add_addr]
      rw [C.same _ (P.sig_not_scratch (by omega))]
      simp only [sig, Nat.add_assoc, Nat.add_comm]

end NativeRustcArm.Xmss.LayerRead

namespace NativeRustcArm.Xmss.LayerRead

open NativeRustcArm.Sym NativeRustcArm

/-- **A turn of the loop**: from the head before value `i`, the head before value `i + 1`, or the
loop's end after the last value. -/
theorem turn [Host] {k : Nat} (hp : Placed code k) {m₀ : MachineData} (P : Pre m₀) {i : Nat}
    (hi : i < 58) {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcArm.Xmss.LayerRead.b2Offset))
    (h : LoopAt m₀ st.data i) :
    Eventually (step1 Host.exe) (fun st' => (st'.pc = Host.addrOf (k + NativeRustcArm.Xmss.LayerRead.b4Offset) ∧ LoopDone m₀ st'.data) ∨
      (i + 1 < 58 ∧ st'.pc = Host.addrOf (k + NativeRustcArm.Xmss.LayerRead.b2Offset) ∧ LoopAt m₀ st'.data (i + 1))) st := by
  have hwf := envL_wf P hi h.common
  have hn := P.remaining
  refine exec_at (b2_in_code.trans hp.1 (List.cons_ne_nil _ _)) b2_execL hwf hpc (match_envL h)
    fun st₁ hm₁ hpc₁ => ?_
  have hnb : (SBool.cmp .eq .W64 (.reg .X8) (.lit 0)).eval
      (envL m₀ st.data i) = false := by
    have := remaining_lt m₀
    simp only [SBool.eval, CmpOp.apply, Sym.eval, low_W64, Env.ofMachine_regs, envL, h.x8]
    simp [BitVec.toNat_eq]
    omega
  simp only [PcOk, hnb, Bool.false_eq_true, ite_false] at hpc₁
  have hm₁' : Match (envL m₀ st.data i) stL1 st₁.data := by unfold stL1; rw [b2_execL]; exact hm₁
  refine exec_at (b3_in_code.trans hp.1 (List.cons_ne_nil _ _)) b3_execL hwf hpc₁ hm₁'
    fun st₂ hm₂ hpc₂ => ?_
  have hm : Match (envL m₀ st.data i) stL2 st₂.data := by unfold stL2; rw [b3_execL]; exact hm₂
  have A := afterTurn P hi h hm
  refine .done _ ?_
  have hc : (SBool.not (SBool.cmp .eq .W64 (.bin .add .W64 (.reg .X23) (.lit 16)) (.lit 928))).eval
      (envL m₀ st.data i) = decide (i + 1 < 58) := by
    simp only [SBool.eval, CmpOp.apply, Sym.eval, BinOp.apply, low_W64, ext_W64,
      Env.ofMachine_regs, envL, h.x23, ofNat_add_lit]
    by_cases hlt : i + 1 < 58
    · simp only [hlt, decide_true, Bool.not_eq_true']
      simp [BitVec.toNat_eq]
      omega
    · simp only [hlt, decide_false, Bool.not_eq_false']
      simp [BitVec.toNat_eq]
      omega
  simp only [PcOk, hc] at hpc₂
  by_cases hlt : i + 1 < 58
  · simp only [hlt, decide_true, ite_true] at hpc₂
    exact Or.inr ⟨hlt, hpc₂.trans (hp.label NativeRustcArm.Xmss.LayerRead.label_2_at),
      ⟨A.common, A.x8, A.x9, A.x22, A.x23, A.chain⟩⟩
  · simp only [hlt, decide_false, Bool.false_eq_true, ite_false] at hpc₂
    have hi' : i = 57 := by omega
    subst hi'
    exact Or.inl ⟨hpc₂, ⟨A.common, A.x22, A.x23, A.x24, A.chain⟩⟩

/-- **The loop over the chain values**: from its head before value `0` to its end. -/
public theorem loop [Host] {k : Nat} (hp : Placed code k) {m₀ : MachineData} (P : Pre m₀)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcArm.Xmss.LayerRead.b2Offset)) (h : LoopAt m₀ st.data 0) :
    Eventually (step1 Host.exe) (fun st' => st'.pc = Host.addrOf (k + NativeRustcArm.Xmss.LayerRead.b4Offset) ∧ LoopDone m₀ st'.data)
      st :=
  Sym.loop (I := fun n s => ∃ i, i + n = 58 ∧ 0 < n ∧ s.pc = Host.addrOf (k + NativeRustcArm.Xmss.LayerRead.b2Offset) ∧
      LoopAt m₀ s.data i)
    (fun n s ⟨i, hn, hn0, hpc, h⟩ => NativeRustcArm.Eventually.mono (turn hp P (by omega) hpc h)
      fun s' h' => by
      rcases h' with h' | ⟨hlt, hpc', h'⟩
      · exact Or.inl h'
      · exact Or.inr ⟨n - 1, by omega, i + 1, by omega, by omega, hpc', h'⟩)
    (n := 58) ⟨0, rfl, by decide, hpc, h⟩

end NativeRustcArm.Xmss.LayerRead
