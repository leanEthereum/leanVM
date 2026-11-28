module

public import NativeRustcVmArm.Code.Vm.HashPair.Names
public import NativeRustcVmArm.Code.Vm.ReaderDigest.Names
public import NativeRustcVmArm.Wire.ClimbLevel.CarryRun

/-!
# `climb_level`'s scan for a sibling

`b7`: past the last node, the sibling read (`carry_spec`); else `b8` compares node `j`'s key with
node `i`'s (`scanS`, `scanSelfS` when `j = i`): the sibling found (`found_spec`) or the next
node (`scan_step`); the scan to its end (`scan_spec`).
-/

namespace NativeRustcVmArm.Wire.ClimbLevel

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt InAny Region)
open NativeRustcVmArm.Vm.ClimbLevel
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

public section

variable {m0 : MachineData} {bp : BitVec 64} {B : List UInt8} {c : Nat} {ns : List (Nat × Digest)}

/-- **`Cur` kept** by a block without writes. -/
theorem Cur.keep {i : Nat} {sl : List (Nat × Digest × Bool)} {ci : Nat} {m m' : MachineData}
    (h : Cur m0 bp B c ns i sl ci m) (hfr : Frm m0 m') (hd : m'.dmem = m.dmem)
    (hr : ∀ r ∈ [XReg.X19, .X20, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
      m'.regs.getXReg r = m.regs.getXReg r) :
    Cur m0 bp B c ns i sl ci m' :=
  ⟨hfr, h.fx.keep fun r h ↦ hr r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
      rcases h with rfl | rfl | rfl | rfl | rfl <;> simp),
    by rw [hd]; exact h.dn, h.lt, by rw [hr .X19 (by simp)]; exact h.x19,
    by rw [hr .X20 (by simp)]; exact h.x20, by rw [hr .X23 (by simp)]; exact h.x23,
    by rw [hr .X24 (by simp)]; exact h.x24, by rw [hr .X26 (by simp)]; exact h.x26⟩

theorem ofInt_neg40 : (BitVec.ofInt 64 (-40)).toNat = 2 ^ 64 - 40 := by
  rw [BitVec.toNat_ofInt]; rfl

/-- `x + 40 = a`: `x` is `a` less 40. -/
theorem sub40 {x a : BitVec 64} (h : x + BitVec.ofNat 64 40 = a) : x = a + BitVec.ofInt 64 (-40) := by
  subst h
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_add, ofInt_neg40, BitVec.toNat_ofNat]
  have := x.isLt
  omega

theorem add40_cancel (a : BitVec 64) :
    a + BitVec.ofInt 64 (-40) + BitVec.ofNat 64 40 = a := by
  have h : BitVec.ofInt 64 (-40) + BitVec.ofNat 64 40 = 0#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, ofInt_neg40]
    rfl
  rw [BitVec.add_assoc, h, BitVec.add_zero]

/-- A node's key word. -/
theorem key_word [Labels] (G : Geo m0 bp B) (hns : NodesAt m0.dmem (nodes m0) ns)
    (hlen : ns.length = cnt m0) {m : MachineData} (hfr : Frm m0 m) {j : Nat} (hj : j < ns.length) :
    ns[j].1 < 2 ^ 64 ∧ WordAt m.dmem (nd m0 j + BitVec.ofNat 64 0) ns[j].1.toUInt64 := by
  have h := G.nodes_frm hlen hns hfr j hj
  rw [NativeRustcVm.addr_add_zero]
  exact ⟨h.1, h.2.1⟩

variable [Host] {k : Nat}

omit [Host] in
theorem saved10' : ∀ r ∈ [XReg.X19, .X20, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
    calleeSaved r = true := by decide

/-- **A step of the scan**: the sibling read or found (`Post` or the head after node `i`), or the
scan at node `j + 1`. -/
theorem scan_step (hp : Placed code k) (G : Geo m0 bp B)
    (hh : Spec (Labels.label NativeRustcVmArm.Vm.HashPair.entryLabel) HashPairPre HashPairPost)
    (hd : Spec (Labels.label NativeRustcVmArm.Vm.ReaderDigest.entryLabel) ReaderDigestPre ReaderDigestPost)
    (hR : ReaderAt m0.dmem (rdr m0) bp B c)
    (hns : NodesAt m0.dmem (nodes m0) ns) (hlen : ns.length = cnt m0) {i : Nat}
    {sl : List (Nat × Digest × Bool)} {ci j : Nat} {st : MachineState}
    (hS : Scan m0 bp B c ns k i sl ci j st) :
    Eventually (step1 Host.exe) (fun st' ↦ (Post m0 st' ∨
      ∃ sl' ci', Head m0 bp B c ns k (i + 1) sl' ci' st') ∨ Scan m0 bp B c ns k i sl ci (j + 1) st')
      st := by
  have hC := hS.cur
  have hn := G.n256
  have hsp := G.sp
  have h224 := stack224
  have hlt := hC.lt
  have hi : i < ns.length := by omega
  have hwf := G.frEnv_wf hC.fr
  have hm := G.frEnv_match hC.fr
  refine exec_at (infix_of b7_in_code (by simp [b7]) hp) run_b7 hwf hS.pc hm fun st1 hm1 hpc1 ↦ ?_
  have hfr1 : Frm m0 st1.data := Fr.ofBlock hC.fr hm hm1 hwf rfl rfl rfl
    fun x hx ↦ absurd hx (by simp)
  have hr1 : ∀ r ∈ [XReg.X19, .X20, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
      st1.data.regs.getXReg r = st.data.regs.getXReg r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact Match.reg_eq hm hm1 rfl rfl
  have hC1 := hC.keep hfr1 (hm1.dmem_eq hwf rfl) hr1
  have hx9 := hS.x9
  have hc : (SBool.cmp .eq .W64 (.reg .X9) (.lit 0)).eval (frEnv m0 st.data) =
      decide (j = cnt m0) := by
    simp only [SBool.eval, eq_apply, Sym.eval, Env.ofMachine_regs, UInt64.toNat_toBitVec, hx9,
      BitVec.toNat_ofNat]
    have := hS.le
    by_cases h : j = cnt m0
    · simp only [h, Nat.sub_self, Nat.mul_zero, Nat.zero_mod, decide_true]
    · rw [decide_eq_false (by omega), decide_eq_false h]
  simp only [PcOk, hc] at hpc1
  by_cases hend : j = cnt m0
  · simp only [hend, decide_true, ↓reduceIte, hp.label (j := NativeRustcVmArm.Vm.ClimbLevel.b11Offset) NativeRustcVmArm.Vm.ClimbLevel.label_9_at] at hpc1
    refine Eventually.mono (carry_spec hp G hh hd hR hns hlen hpc1 hC1 hi ?_) fun _ h ↦ .inl h
    rw [hlen, ← hend]
    exact hS.miss
  simp only [hend, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc1
  have hj : j < cnt m0 := by have := hS.le; omega
  have hjl : j < ns.length := by omega
  have hx8 : (st1.data.regs.getXReg .X8).toBitVec = nd m0 j + BitVec.ofInt 64 (-40) := by
    rw [Match.reg_eq hm hm1 (r := .X8) rfl rfl]
    exact sub40 hS.x8
  have := G.ndNw; have := G.nS
  have hnd0 := G.nd0 hj
  have hni := G.nd0 hlt
  obtain ⟨hkj, wj⟩ := key_word G hns hlen hfr1 hjl
  obtain ⟨hki, wi⟩ := key_word G hns hlen hfr1 hi
  -- after `b8`: node `j`'s key compared
  have post : ∀ st2 : MachineState, (st2.pc = Host.addrOf (k + NativeRustcVmArm.Vm.ClimbLevel.b9Offset) ∧ ns[j].1 = ns[i].1 ^^^ 1) ∨
      (st2.pc = Host.addrOf (k + NativeRustcVmArm.Vm.ClimbLevel.b7Offset) ∧ ns[j].1 ≠ ns[i].1 ^^^ 1) → Frm m0 st2.data →
      st2.data.dmem = st1.data.dmem →
      (∀ r ∈ [XReg.X19, .X20, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
        st2.data.regs.getXReg r = st1.data.regs.getXReg r) →
      (st2.data.regs.getXReg .X8).toBitVec = nd m0 j →
      (st2.data.regs.getXReg .X9).toNat = 40 * (cnt m0 - (j + 1)) →
      (st2.data.regs.getXReg .X21).toNat = ns[i].1 →
      Eventually (step1 Host.exe) (fun st' ↦ (Post m0 st' ∨
        ∃ sl' ci', Head m0 bp B c ns k (i + 1) sl' ci' st') ∨
        Scan m0 bp B c ns k i sl ci (j + 1) st') st2 := by
    intro st2 hpc2 hfr2 hd2 hr2 h8 h9 h21
    have hC2 := hC1.keep hfr2 hd2 hr2
    rcases hpc2 with ⟨hpc2', hne⟩ | ⟨hpc2', hne⟩
    · exact Eventually.mono (found_spec hp G hh hns hlen hpc2' hC2 hj h8 hi hjl hne hS.miss h21)
        fun _ h ↦ .inl (.inr h)
    · refine .done _ (.inr ⟨hpc2', hC2, by omega, ?_, h9, ?_⟩)
      · rw [h8, NativeRustcVm.addr_add_add, show 40 * j + 40 = 40 * (j + 1) by omega]
      · intro j' hj' hj1 hi1
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj') with h | rfl
        · exact hS.miss j' h hj1 hi1
        · exact hne
  by_cases hji : j = i
  · subst hji
    have hwf2 : (Env.ofMachine st1.data [(base m0 224, 224), (nd m0 j, 40)]).WF :=
      G.env2_wf hfr1 (G.ndMap' hj (le_refl _)) (by rw [hnd0]; omega)
        (by rw [hnd0]; unfold climbLevelStack at *; omega)
    have hm2 : Match (Env.ofMachine st1.data [(base m0 224, 224), (nd m0 j, 40)]) scanSelfS
        st1.data :=
      match_ofMachine ⟨rfl, fun _ ↦ G.aligned, rfl, nofun, trivial⟩
        (by rw [hfr1.sp]; simp [Sym.eval]) trivial trivial trivial
        ⟨hx8, by
          show (st1.data.regs.getXReg .X24).toBitVec = nd m0 j + BitVec.ofInt 64 0
          rw [hC1.x24, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero], trivial⟩
    refine exec_at (infix_of b8_in_code (by simp [b8]) hp) run_b8s hwf2 hpc1 hm2
      fun st2 hm2' hpc2 ↦ ?_
    have hfr2 : Frm m0 st2.data := Fr.ofBlock hfr1 hm2 hm2' hwf2 rfl rfl rfl
      fun x hx ↦ absurd hx (by simp)
    have hl : (Env.ofMachine st1.data [(base m0 224, 224), (nd m0 j, 40)]).load 1 0 8 =
        ns[j].1.toUInt64.toBitVec := load_of rfl wj
    have hc2 : (SBool.cmp .eq .W64 (.bin .eor .W64 (.load 1 0 8) (.load 1 0 8)) (.lit 1)).not.eval
        (Env.ofMachine st1.data [(base m0 224, 224), (nd m0 j, 40)]) = true := by
      simp only [SBool.eval, eq_apply, Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, hl,
        BitVec.xor_self]
      decide
    simp only [PcOk, hc2, ↓reduceIte, hp.label (j := NativeRustcVmArm.Vm.ClimbLevel.b7Offset) NativeRustcVmArm.Vm.ClimbLevel.label_6_at] at hpc2
    have hne : ns[j].1 ≠ ns[j].1 ^^^ 1 := by
      intro h
      have := (xor_eq_one_iff ns[j].1 ns[j].1).mpr h
      rw [Nat.xor_self] at this
      exact absurd this (by decide)
    refine post st2 (.inr ⟨hpc2, hne⟩) hfr2 (hm2'.dmem_eq hwf2 rfl) (fun r hr ↦ ?_) ?_ ?_ ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact Match.reg_eq hm2 hm2' rfl rfl
    · rw [hm2'.regs .X8 _ rfl]
      simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs, hx8]
      exact add40_cancel _
    · show (st2.data.regs.getXReg .X9).toBitVec.toNat = _
      rw [hm2'.regs .X9 _ rfl]
      simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs,
        BitVec.toNat_sub, BitVec.toNat_ofNat]
      rw [show (st1.data.regs.getXReg .X9).toBitVec.toNat = 40 * (cnt m0 - j) from by
        rw [Match.reg_eq hm hm1 (r := .X9) rfl rfl]; exact hx9]
      omega
    · show (st2.data.regs.getXReg .X21).toBitVec.toNat = _
      rw [hm2'.regs .X21 _ rfl]
      simp only [Sym.eval]
      rw [hl, UInt64.toNat_toBitVec, toNat_toUInt64_of_lt hkj]
  · have hwf2 : (Env.ofMachine st1.data [(base m0 224, 224), (nd m0 j, 40), (nd m0 i, 8)]).WF :=
      G.env3_wf hfr1 (G.ndMap' hj (le_refl _)) (by rw [hnd0]; omega)
        (by rw [hnd0]; unfold climbLevelStack at *; omega)
        (G.ndMap' hlt (by omega)) (by rw [hni]; omega)
        (by rw [hni]; unfold climbLevelStack at *; omega)
        (by rw [hnd0, hni]; omega)
    have hm2 : Match (Env.ofMachine st1.data [(base m0 224, 224), (nd m0 j, 40), (nd m0 i, 8)])
        scanS st1.data :=
      match_ofMachine ⟨rfl, fun _ ↦ G.aligned, rfl, nofun, rfl, nofun, trivial⟩
        (by rw [hfr1.sp]; simp [Sym.eval]) trivial trivial trivial
        ⟨hx8, by
          show (st1.data.regs.getXReg .X24).toBitVec = nd m0 i + BitVec.ofInt 64 0
          rw [hC1.x24, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero], trivial⟩
    refine exec_at (infix_of b8_in_code (by simp [b8]) hp) run_b8 hwf2 hpc1 hm2
      fun st2 hm2' hpc2 ↦ ?_
    have hfr2 : Frm m0 st2.data := Fr.ofBlock hfr1 hm2 hm2' hwf2 rfl rfl rfl
      fun x hx ↦ absurd hx (by simp)
    have hlj : (Env.ofMachine st1.data [(base m0 224, 224), (nd m0 j, 40), (nd m0 i, 8)]).load
        1 0 8 = ns[j].1.toUInt64.toBitVec := load_of rfl wj
    have hli : (Env.ofMachine st1.data [(base m0 224, 224), (nd m0 j, 40), (nd m0 i, 8)]).load
        2 0 8 = ns[i].1.toUInt64.toBitVec := load_of rfl wi
    have hc2 : (SBool.cmp .eq .W64 (.bin .eor .W64 (.load 2 0 8) (.load 1 0 8)) (.lit 1)).not.eval
        (Env.ofMachine st1.data [(base m0 224, 224), (nd m0 j, 40), (nd m0 i, 8)]) =
        decide (ns[j].1 ≠ ns[i].1 ^^^ 1) := by
      simp only [SBool.eval, eq_apply, Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, hlj, hli,
        xor_toNat, toNat_toUInt64_of_lt hkj, toNat_toUInt64_of_lt hki,
        BitVec.toNat_ofNat]
      rw [show (1 : Nat) % 2 ^ 64 = 1 from rfl]
      by_cases h : ns[j].1 = ns[i].1 ^^^ 1
      · rw [decide_eq_true ((xor_eq_one_iff _ _).mpr h), decide_eq_false (not_not.mpr h)]; rfl
      · rw [decide_eq_false (fun h' ↦ h ((xor_eq_one_iff _ _).mp h')), decide_eq_true h]; rfl
    simp only [PcOk, hc2] at hpc2
    refine post st2 ?_ hfr2 (hm2'.dmem_eq hwf2 rfl) (fun r hr ↦ ?_) ?_ ?_ ?_
    · by_cases h : ns[j].1 ≠ ns[i].1 ^^^ 1
      · simp only [decide_eq_true h, ↓reduceIte, hp.label (j := NativeRustcVmArm.Vm.ClimbLevel.b7Offset) NativeRustcVmArm.Vm.ClimbLevel.label_6_at] at hpc2
        exact .inr ⟨hpc2, h⟩
      · simp only [decide_eq_false h, Bool.false_eq_true, ↓reduceIte] at hpc2
        exact .inl ⟨hpc2.trans (congrArg Host.addrOf rfl), not_not.mp h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact Match.reg_eq hm2 hm2' rfl rfl
    · rw [hm2'.regs .X8 _ rfl]
      simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs, hx8]
      exact add40_cancel _
    · show (st2.data.regs.getXReg .X9).toBitVec.toNat = _
      rw [hm2'.regs .X9 _ rfl]
      simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs,
        BitVec.toNat_sub, BitVec.toNat_ofNat]
      rw [show (st1.data.regs.getXReg .X9).toBitVec.toNat = 40 * (cnt m0 - j) from by
        rw [Match.reg_eq hm hm1 (r := .X9) rfl rfl]; exact hx9]
      omega
    · show (st2.data.regs.getXReg .X21).toBitVec.toNat = _
      rw [hm2'.regs .X21 _ rfl]
      simp only [Sym.eval]
      rw [hli, UInt64.toNat_toBitVec, toNat_toUInt64_of_lt hki]

end

end NativeRustcVmArm.Wire.ClimbLevel
