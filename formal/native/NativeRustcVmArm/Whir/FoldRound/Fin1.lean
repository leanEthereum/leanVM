module

public import NativeRustcVmArm.Whir.FoldRound.Muls2

/-!
# `fold_round`: the push's environment, the folded claim

`pushEnv m0 st c`: the frame, the state's head, the `α`s' slot `c`, the output; well formed
(`push_wf`), `pushS` matching it with `c` in X8 (`push_match`). `foldW_claim`: the folded claim as
the sum of the products.
-/

namespace NativeRustcVmArm.Whir.FoldRound

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir NativeRustcVmArm.Vm.FoldRound

public section

section
variable [Labels]

/-- The frame, the state's head, the `α`s' slot `c`, the output. -/
abbrev pushEnv (m0 st : MachineData) (c : Nat) : Env :=
  Env.ofMachine st [(base m0 208, 208), (pA m0, 24), (off (pA m0) (24 + 16 * c), 16), (oA m0, 40)]

end

theorem shl4 (c : Nat) : BitVec.ofNat 64 c <<< 4 = BitVec.ofNat 64 (16 * c) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [Nat.mod_mul_mod, Nat.mul_comm]

theorem neg24 : BitVec.ofInt 64 (-24) = -(24#64) := by decide

theorem slot_alias (p : BitVec 64) (c : Nat) :
    p + BitVec.ofNat 64 c <<< 4 = p + BitVec.ofNat 64 (24 + 16 * c) + BitVec.ofInt 64 (-24) := by
  rw [shl4, neg24, BitVec.ofNat_add, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 24),
    BitVec.add_assoc, ← BitVec.sub_eq_add_neg, show BitVec.ofNat 64 24 = 24#64 from rfl,
    BitVec.sub_self, BitVec.add_zero]

/-- **The folded claim**, as the code sums the products. -/
theorem foldW_claim (w : WhirStateW) (s5 : TState) (u0 v c0 c1 : EW) :
    (foldW w u0 v c0 c1 (alA s5) (beA s5)).claim =
      ⟨u0.c0 ^^^ (p1 w s5 u0).c0 ^^^ (p3 s5 v).c0 ^^^ (p4 s5 c0).c0 ^^^ (p6 s5 c0 c1).c0,
        u0.c1 ^^^ (p1 w s5 u0).c1 ^^^ (p3 s5 v).c1 ^^^ (p4 s5 c0).c1 ^^^ (p6 s5 c0 c1).c1⟩ := by
  have e1 : alA s5 * (u0 + w.claim) = p1 w s5 u0 := by
    show EW.mul _ ⟨u0.c0 ^^^ w.claim.c0, u0.c1 ^^^ w.claim.c1⟩ = _
    rw [UInt64.xor_comm u0.c0, UInt64.xor_comm u0.c1]; rfl
  have e6 : alA s5 * beA s5 * (c0 + c1) = p6 s5 c0 c1 := by
    show EW.mul _ ⟨c0.c0 ^^^ c1.c0, c0.c1 ^^^ c1.c1⟩ = _
    rw [UInt64.xor_comm c0.c0, UInt64.xor_comm c0.c1]; rfl
  simp only [foldW]
  rw [e1, e6]
  rfl

variable [Host] {a : DecArea} {s0 : TState} {w : WhirStateW} {m0 : MachineData}

/-- The geometry of the push's areas. -/
theorem push_geo (h : FoldRoundPre a s0 w m0) :
    (pA m0).toNat + stateBytes ≤ 2 ^ 64 ∧ (oA m0).toNat + 40 ≤ 2 ^ 64 ∧
      ((pA m0).toNat + stateBytes ≤ m0.regs.SP.toNat - foldRoundStack ∨
        m0.regs.SP.toNat ≤ (pA m0).toNat) ∧
      ((oA m0).toNat + 40 ≤ m0.regs.SP.toNat - foldRoundStack ∨
        m0.regs.SP.toNat ≤ (oA m0).toNat) ∧
      ((oA m0).toNat + 40 ≤ (pA m0).toNat ∨ (pA m0).toNat + stateBytes ≤ (oA m0).toNat) ∧
      foldRoundStack ≤ m0.regs.SP.toNat := by
  have hN := pre_hN h
  have hpo : OutOk m0 (tA m0) a (pA m0) stateBytes foldRoundStack := h.2.2.2.2.1.1
  have hoo : OutOk m0 (tA m0) a (oA m0) 40 foldRoundStack := h.2.2.2.2.2.1.1
  have hap : Apart (oA m0) 40 (pA m0) stateBytes := h.2.2.2.2.2.2
  have hsb : (stackBelow m0 foldRoundStack).toNat = m0.regs.SP.toNat - foldRoundStack :=
    base_toNat hN
  have h1 := hpo.2.2.2.2.1
  have h2 := hoo.2.2.2.2.1
  unfold Apart at h1 h2 hap
  rw [hsb] at h1 h2
  have : (stackBelow m0 foldRoundStack).toNat + foldRoundStack = m0.regs.SP.toNat := by omega
  exact ⟨hpo.2.1, hoo.2.1, by omega, by omega, hap, hN⟩

theorem push_wf (h : FoldRoundPre a s0 w m0) {st : MachineData} (hf : FFr m0 st) {c : Nat}
    (hc : c < 30) : (pushEnv m0 st c).WF := by
  obtain ⟨g1, g2, g3, g4, g5, hN⟩ := push_geo h
  have hpo : OutOk m0 (tA m0) a (pA m0) stateBytes foldRoundStack := h.2.2.2.2.1.1
  have hoo : OutOk m0 (tA m0) a (oA m0) 40 foldRoundStack := h.2.2.2.2.2.1.1
  have hS : stateBytes = 61152 := rfl
  have hNv : foldRoundStack = 800 := rfl
  have hbF := base_toNat (m0 := m0) (F := 208) (by omega)
  have hsl : (off (pA m0) (24 + 16 * c)).toNat = (pA m0).toNat + (24 + 16 * c) :=
    NativeRustcVm.toNat_add_ofNat (by omega)
  refine Env.wf_of ⟨⟨frame_mapped' h hf, base_noWrap (by omega)⟩,
    ⟨fun i hi ↦ hf.kept _ (hpo.1 i (by omega)), by show (pA m0).toNat + 24 ≤ _; omega⟩,
    ⟨fun i hi ↦ ?_, by show (off (pA m0) (24 + 16 * c)).toNat + 16 ≤ _; omega⟩,
    ⟨fun i hi ↦ hf.kept _ (hoo.1 i hi), by show (oA m0).toNat + 40 ≤ _; omega⟩, trivial⟩ ?_
  · have := hf.kept _ (hpo.1 (24 + 16 * c + i) (by omega))
    rwa [← NativeRustcVm.addr_add_add] at this
  · refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (List.Pairwise.cons ?_
      (List.pairwise_singleton _ _)))
    all_goals
      intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    · rcases he with rfl | rfl | rfl
      · show (base m0 208).toNat + 208 ≤ (pA m0).toNat ∨ (pA m0).toNat + 24 ≤ (base m0 208).toNat
        omega
      · show (base m0 208).toNat + 208 ≤ (off (pA m0) (24 + 16 * c)).toNat ∨
          (off (pA m0) (24 + 16 * c)).toNat + 16 ≤ (base m0 208).toNat
        omega
      · show (base m0 208).toNat + 208 ≤ (oA m0).toNat ∨ (oA m0).toNat + 40 ≤ (base m0 208).toNat
        omega
    · rcases he with rfl | rfl
      · show (pA m0).toNat + 24 ≤ (off (pA m0) (24 + 16 * c)).toNat ∨ _
        omega
      · show (pA m0).toNat + 24 ≤ (oA m0).toNat ∨ (oA m0).toNat + 40 ≤ (pA m0).toNat
        omega
    · subst he
      show (off (pA m0) (24 + 16 * c)).toNat + 16 ≤ (oA m0).toNat ∨
        (oA m0).toNat + 40 ≤ (off (pA m0) (24 + 16 * c)).toNat
      omega

theorem push_match (h : FoldRoundPre a s0 w m0) {st : MachineData} (hf : FFr m0 st) {c : Nat}
    (h19 : st.regs.X19 = m0.regs.X0) (h20 : st.regs.X20 = m0.regs.X2)
    (h8 : st.regs.X8 = c.toUInt64) : Match (pushEnv m0 st c) pushS st := by
  refine match_ofMachine ⟨rfl, fun _ ↦ frame_aligned h.1.1 (by rw [stack_eq]; decide) rfl, rfl,
    fun h ↦ absurd h (by decide), rfl, fun h ↦ absurd h (by decide), rfl,
    fun h ↦ absurd h (by decide), trivial⟩ (by rw [hf.sp]; simp [Sym.eval])
    ⟨?_, ?_, trivial⟩ trivial trivial ⟨?_, trivial⟩
  · show (st.regs.getXReg .X20).toBitVec = _
    simp only [Sym.eval, Env.base_ofMachine_eq, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.map_some, Option.getD_some, BitVec.ofInt_ofNat, BitVec.add_zero]
    exact congrArg UInt64.toBitVec h20
  · show (st.regs.getXReg .X19).toBitVec = _
    simp only [Sym.eval, Env.base_ofMachine_eq, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.map_some, Option.getD_some, BitVec.ofInt_ofNat, BitVec.add_zero]
    exact congrArg UInt64.toBitVec h19
  · simp only [slotSym, Sym.eval, BinOp.apply, UnOp.apply, low_W64, ext_W64, shiftW,
      Env.base_ofMachine_eq, Env.ofMachine_regs, List.getElem?_cons_succ,
      List.getElem?_cons_zero, Option.map_some, Option.getD_some, BitVec.ofInt_ofNat,
      BitVec.add_zero]
    rw [show (st.regs.getXReg .X8).toBitVec = BitVec.ofNat 64 c by
      rw [show st.regs.getXReg .X8 = c.toUInt64 from h8]; rfl]
    exact slot_alias _ c

end

end NativeRustcVmArm.Whir.FoldRound
