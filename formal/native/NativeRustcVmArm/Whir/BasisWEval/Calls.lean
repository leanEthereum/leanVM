module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Whir.BasisWEval.Entry

/-!
# `BasisW::eval`: the loop's invariants, the callees' arguments

`Keep`: the frame and the registers every later block reads (the point X21, the `BasisW` X22, the
layout X23). `Acc W`: the running sum (X24, X25) is `dot scales W`, X28 points at scale `|W|`
(clamped to the scales' end, X29). `Loop i` at `.LBasisWEval_7` (`b10`) before column claim `i`
(X20 16 bytes into it, X19 the bytes left); `AtB9 i` at `.LBasisWEval_6` (`b9`) after it; `End`
at `.LBasisWEval_14` (`b19`) after all.

The callees' arguments: inputs readable and apart from a callee's stack (`In.argOk`), the frame's
`Option<EW>` at `sp + 24` (`frame_out`), slices reading as at the entry (`slice_of`).
-/

namespace NativeRustcVmArm.Whir.BasisWEval

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model LeanVM.Parameters
open NativeRustcVmArm.Ring NativeRustcVm.Whir NativeRustcVm.Layout NativeRustcVm.Ring
open NativeRustcVm.KeccakGkr NativeRustcVmArm.Vm.BasisWEval
open LeanVM.Protocol.Verifier (qkeccak Placement)

@[expose] public section

/-- The frame and the registers the later blocks read. -/
structure Keep (m0 : MachineData) (ba : BasisAddrs) (st : MachineData) : Prop where
  fr : Fr1 m0 st
  x21 : st.regs.X21 = m0.regs.X2
  x22 : st.regs.X22 = m0.regs.X1
  x23 : st.regs.X23 = UInt64.ofBitVec ba.layout

/-- The running sum over the weights `W`, the next scale's address. -/
structure Acc (ba : BasisAddrs) (b : BasisW) (W : Array EW) (st : MachineData) : Prop where
  x24 : st.regs.X24 = (dot b.scales W).c0
  x25 : st.regs.X25 = (dot b.scales W).c1
  x28 : st.regs.X28.toBitVec = ba.scales + BitVec.ofNat 64 (16 * min W.size ba.count)
  x29 : st.regs.X29.toBitVec = ba.scales + BitVec.ofNat 64 (16 * ba.count)

/-- **Before column claim `i`** (`b10`). -/
structure Loop (m0 : MachineData) (ba : BasisAddrs) (b : BasisW) (v : Vals) (i : Nat)
    (st : MachineData) : Prop where
  keep : Keep m0 ba st
  acc : Acc ba b (ws v (xpt m0) i) st
  ilt : i < v.cs.size
  x19 : st.regs.X19.toNat = 608 * (v.cs.size - i)
  x20 : st.regs.X20.toBitVec = ba.claims + BitVec.ofNat 64 (24 + 608 * i)

/-- **After column claim `i`** (`b9`). -/
structure AtB9 (m0 : MachineData) (ba : BasisAddrs) (b : BasisW) (v : Vals) (i : Nat)
    (st : MachineData) : Prop where
  keep : Keep m0 ba st
  acc : Acc ba b (ws v (xpt m0) (i + 1)) st
  ilt : i < v.cs.size
  x19 : st.regs.X19.toNat = 608 * (v.cs.size - i)
  x20 : st.regs.X20.toBitVec = ba.claims + BitVec.ofNat 64 (24 + 608 * i)

/-- **After the column claims** (`b19`). -/
structure End (m0 : MachineData) (ba : BasisAddrs) (b : BasisW) (v : Vals) (st : MachineData) :
    Prop where
  keep : Keep m0 ba st
  acc : Acc ba b (ws v (xpt m0) v.cs.size) st

end

public section

theorem _root_.NativeRustcVmArm.Ring.Fr.addSlot {m0 st : MachineData} {F N : Nat}
    {sl : List (Nat × XReg)} {keep : List XReg} {outs : BitVec 64 → Prop}
    (h : Fr m0 F N sl keep outs st) {o : Nat} {r : XReg}
    (hw : NativeRustcVm.WordAt st.dmem (base m0 F + BitVec.ofNat 64 o) (m0.regs.getXReg r)) :
    Fr m0 F N ((o, r) :: sl) keep outs st where
  sp := h.sp
  keep := h.keep
  slots p hp := by
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hw
    · exact h.slots p hp
  same := h.same
  kept := h.kept

/-! ## The weights -/

theorem dot_push_c (sc W : Array EW) (w : EW) :
    (dot sc (W.push w)).c0 = (EW.mul (sAt sc W.size) w).c0 ^^^ (dot sc W).c0 ∧
      (dot sc (W.push w)).c1 = (EW.mul (sAt sc W.size) w).c1 ^^^ (dot sc W).c1 := by
  rw [dot_push]
  exact ⟨UInt64.xor_comm _ _, UInt64.xor_comm _ _⟩

theorem dot_single (sc : Array EW) (w : EW) : dot sc #[w] = EW.mul (sAt sc 0) w := by
  rw [show #[w] = (#[] : Array EW).push w from rfl, dot_push, dot_empty]
  exact ew_zero_add _

theorem ws_size (v : Vals) (x : Array EW) (i : Nat) :
    (ws v x i).size = 1 + (colWs v.L x v.cs i).length := by
  simp [ws, Nat.add_comm]

theorem ws_succ (v : Vals) (x : Array EW) {i : Nat} (hi : i < v.cs.size) :
    ws v x (i + 1) = match (v.L.placements[v.cs[i].column]?).getD none with
      | none => ws v x i
      | some pl => (ws v x i).push (eqEval (stackPoint pl v.cs[i].point v.L.stackLog) x) := by
  unfold ws
  rw [colWs_succ _ _ _ hi]
  cases (v.L.placements[v.cs[i].column]?).getD none <;> simp

theorem ws_zero (v : Vals) (x : Array EW) : ws v x 0 = #[ringW v x] := by
  simp [ws, colWs_zero]

/-! ## The layout -/

theorem placement_lt {d : Mem 64} {a : BitVec 64} {L : LayoutW} (h : LayoutWAt d a L) (c : Nat) :
    (L.placement c).variableCount < 2 ^ 64 ∧ (L.placement c).index < 2 ^ 64 := by
  unfold LayoutW.placement
  cases hc : L.placements[c]? with
  | none => exact ⟨by decide, by decide⟩
  | some o =>
    cases o with
    | none => exact ⟨by decide, by decide⟩
    | some p =>
      obtain ⟨hc', he⟩ := Array.getElem?_eq_some_iff.mp hc
      have := h.placements c hc'
      rw [he] at this
      exact ⟨this.2.1, this.2.2.1⟩

theorem placementArg_eq {m : MachineData} {p : Placement} (hp : p.variableCount < 2 ^ 64 ∧
    p.index < 2 ^ 64) (h1 : m.regs.X1 = p.variableCount.toUInt64)
    (h2 : m.regs.X2 = p.index.toUInt64) : placementArg m = p := by
  unfold placementArg
  rw [h1, h2, natCast_toUInt64_toNat hp.1, natCast_toUInt64_toNat hp.2]

/-! ## Scales -/

theorem shl4 (c : Nat) : (BitVec.ofNat 64 c) <<< 4 = BitVec.ofNat 64 (16 * c) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.mod_mul_mod]
  congr 1
  omega

theorem scale_beq {s : BitVec 64} {c j : Nat} (hnw : NoWrap s (16 * c))
    (hpos : 0 < s.toNat ∨ s.toNat + 16 * c < 2 ^ 64) :
    ((s + BitVec.ofNat 64 (16 * min j c)) == (s + BitVec.ofNat 64 (16 * c))) =
      decide (c ≤ j) := by
  rw [bv_beq_toNat]
  unfold NoWrap at hnw
  have e1 := NativeRustcVm.toNat_add_ofNat_le (a := s) (i := 16 * min j c) (by omega)
  have e2 := NativeRustcVm.toNat_add_ofNat_le (a := s) (i := 16 * c) (by omega)
  by_cases hc : c ≤ j
  · simp only [hc, decide_true, decide_eq_true_eq]
    rw [Nat.min_eq_right hc]
  · simp only [hc, decide_false, decide_eq_false_iff_not]
    omega

variable {m0 : MachineData} {ba : BasisAddrs} {b : BasisW} {v : Vals}

theorem In.scalesPos (h : In m0 ba b v) :
    0 < ba.scales.toNat ∨ ba.scales.toNat + 16 * ba.count < 2 ^ 64 := by
  have hN := h.hN
  have hs := h.scales.2
  have e := base_toNat (m0 := m0) (F := basisWEvalStack) hN
  have := m0.regs.SP.toNat_lt
  have h0 : 0 < basisWEvalStack := by unfold basisWEvalStack; omega
  unfold OffStack Apart at hs
  rw [show stackBelow m0 basisWEvalStack = base m0 basisWEvalStack from rfl, e] at hs
  omega

/-- The scales' pointer against their end: equal once `j` scales are taken. -/
theorem In.scale_beq (h : In m0 ba b v) (j : Nat) :
    ((ba.scales + BitVec.ofNat 64 (16 * min j ba.count)) ==
      (ba.scales + BitVec.ofNat 64 (16 * ba.count))) = decide (ba.count ≤ j) :=
  BasisWEval.scale_beq h.scales.1.2 h.scalesPos

theorem sAt_ge {sc : Array EW} {j : Nat} (hj : sc.size ≤ j) : sAt sc j = 0 := by
  rw [sAt, Array.getElem?_eq_none hj]; rfl

theorem sAt_lt {sc : Array EW} {j : Nat} (hj : j < sc.size) : sAt sc j = sc[j] := by
  rw [sAt, Array.getElem?_eq_getElem hj, Option.getD_some]

section
variable {sl : List (Nat × XReg)} {st : MachineData}

/-- Scale `j` in a state of the frame. -/
theorem In.scaleAt (h : In m0 ba b v) (hf : Fr m0 144 basisWEvalStack sl [] (fun _ ↦ False) st)
    {j : Nat} (hj : j < ba.count) :
    NativeRustcVm.WordAt st.dmem (ba.scales + BitVec.ofNat 64 (16 * j) + BitVec.ofNat 64 0)
        (sAt b.scales j).c0 ∧
      NativeRustcVm.WordAt st.dmem (ba.scales + BitVec.ofNat 64 (16 * j) + BitVec.ofNat 64 8)
        (sAt b.scales j).c1 := by
  have hsz := h.pre.2.1.scales_size
  have hj' : j < b.scales.toList.length := by simp; omega
  have he := NativeRustcVm.ewAt_iff.mp ((h.scalesAt hf).getElem hj')
  rw [sAt_lt (by omega)]
  exact ⟨by simpa using he.1, by simpa using he.2⟩

/-- Scale `j`'s 16 bytes: an input area. -/
theorem In.scaleIn (h : In m0 ba b v) {j : Nat} (hj : j < ba.count) :
    WhirIn m0 (ba.scales + BitVec.ofNat 64 (16 * j)) 16 basisWEvalStack :=
  WhirIn.sub h.scales (by omega)

/-! ## The callees' arguments -/

/-- An input: readable, apart from a callee's stack. -/
theorem In.argOk (h : In m0 ba b v) (hf : Fr m0 144 basisWEvalStack sl [] (fun _ ↦ False) st)
    {a : BitVec 64} {n : Nat} (ha : WhirIn m0 a n basisWEvalStack) {N' : Nat}
    (hle : 144 + N' ≤ basisWEvalStack) : Readable st a n ∧ OffStack st a n N' :=
  ⟨mapped_of hf ha, hf.apart h.hN ha.2 hle⟩

/-- The frame's `Option<EW>` at `sp + 24`. -/
theorem frame_out (h : In m0 ba b v) (hf : Fr m0 144 basisWEvalStack sl [] (fun _ ↦ False) st)
    {N' : Nat} (hle : 144 + N' ≤ basisWEvalStack) :
    Readable st (base m0 144 + BitVec.ofNat 64 24) 24 ∧
      OffStack st (base m0 144 + BitVec.ofNat 64 24) 24 N' := by
  have hN := h.hN
  obtain ⟨hmap, hnw⟩ := frame_of h hf
  have e1 := base_toNat (m0 := m0) (F := 144) (by omega)
  have := m0.regs.SP.toNat_lt
  refine ⟨⟨fun i hi ↦ by rw [NativeRustcVm.addr_add_add]; exact hmap _ (by omega),
    NativeRustcVm.NoWrap.sub hnw (by omega)⟩, ?_⟩
  unfold OffStack Apart
  rw [stackBelow_eq hf.sp (by omega), base_toNat (by omega),
    NativeRustcVm.toNat_add_ofNat (by omega), e1]
  omega

/-- The elements of an input read as at the entry. -/
theorem slice_of (h : In m0 ba b v) (hf : Fr m0 144 basisWEvalStack sl [] (fun _ ↦ False) st)
    {a : BitVec 64} {n N : Nat} (ha : WhirIn m0 a N basisWEvalStack) (hn : 16 * n ≤ N) :
    NativeRustcVm.ewsOf st.dmem a n = NativeRustcVm.ewsOf m0.dmem a n :=
  NativeRustcVm.ewsOf_congr fun i hi ↦ same_of h.hN hf ha i (by omega)

/-- The point, as at the entry. -/
theorem In.xpt_eq (h : In m0 ba b v) (hf : Fr m0 144 basisWEvalStack sl [] (fun _ ↦ False) st)
    {a n : UInt64} (ha : a = m0.regs.X2) (hn : n = m0.regs.X3) : slice st a n = xpt m0 := by
  subst ha hn
  unfold slice xpt slice
  rw [slice_of h hf h.point le_rfl]

theorem WhirIn.mono {m : MachineData} {a : BitVec 64} {N n S : Nat} (h : WhirIn m a N S)
    (hle : n ≤ N) : WhirIn m a n S :=
  ⟨⟨NativeRustcVm.Mapped.mono h.1.1 hle, NativeRustcVm.NoWrap.mono h.1.2 hle⟩,
    NativeRustcVm.Apart.mono h.2 (Nat.le_refl _) (by omega) (Nat.le_refl _) (Nat.le_refl _)⟩

/-- A count below its cap, as the executor compares it. -/
theorem count_ult {n N : Nat} (h : n ≤ N) (hN : N + 1 < 2 ^ 64) :
    (n.toUInt64.toBitVec).ult (BitVec.ofNat 64 (N + 1)) = true := by
  rw [toBitVec_ult_ofNat hN, natCast_toUInt64_toNat (by omega)]
  simp
  omega

/-- The frame's environment for `frameS`. -/
theorem frame_env [Labels] (h : In m0 ba b v)
    (hf : Fr m0 144 basisWEvalStack sl [] (fun _ ↦ False) st) :
    (Env.ofMachine st [(base m0 144, 144)]).WF ∧
      Match (Env.ofMachine st [(base m0 144, 144)]) frameS st := by
  obtain ⟨hmap, hnw⟩ := frame_of h hf
  refine ⟨Env.wf_of ⟨⟨hmap, hnw⟩, trivial⟩ (List.pairwise_singleton _ _),
    match_ofMachine ⟨rfl, fun _ ↦ Ring.frame_aligned h.stackOk stack_le.2.2.2.2.2 rfl, trivial⟩
      (by rw [hf.sp]; simp [Sym.eval]) trivial trivial trivial trivial⟩

/-- **`EW::mul`** from a state of the frame. -/
theorem mul_call [Host] (h : In m0 ba b v) (hsl : ∀ p ∈ sl, p.1 + 8 ≤ 144)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost) {st : MachineState} {next : Int64}
    (hf : Fr m0 144 basisWEvalStack sl [] (fun _ ↦ False) st.data)
    (hpc : st.pc = Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel ∧ retOf st.data = next) {R : MachineState → Prop}
    (cont : ∀ m2, Fr m0 144 basisWEvalStack sl [] (fun _ ↦ False) m2 →
      m2.regs.X0 = (EW.mul ⟨st.data.regs.X0, st.data.regs.X1⟩
        ⟨st.data.regs.X2, st.data.regs.X3⟩).c0 →
      m2.regs.X1 = (EW.mul ⟨st.data.regs.X0, st.data.regs.X1⟩
        ⟨st.data.regs.X2, st.data.regs.X3⟩).c1 →
      (∀ r, calleeSaved r = true → m2.regs.getXReg r = st.data.regs.getXReg r) →
      Eventually (step1 Host.exe) R ⟨m2, next⟩) :
    Eventually (step1 Host.exe) R st :=
  Fr.leaf hf h.hN stack_le.1 (fun _ h ↦ absurd h (by simp)) hsl (fun _ h ↦ h.elim) hmul
    (fun _ _ hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.2.1 fun _ h ↦ .inl h, hq.2.2.2⟩) hpc
    (hf.stackOk h.stackOk (by decide) stack_le.1)
    fun m2 hf2 hq hcs ↦ cont m2 hf2 hq.1 hq.2.1 hcs

end

end

end NativeRustcVmArm.Whir.BasisWEval
