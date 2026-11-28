module

public import NativeRustcVmArm.Code.Vm.ClimbLevel.Names
public import NativeRustcVmArm.Code.Vm.HashPair.Names
public import NativeRustcVmArm.Code.Vm.ReaderDigest.Names
public import NativeRustcVmArm.Wire.ClimbLevel.Loop
public import NativeRustcVmArm.Wire.Find

/-!
# `climb_level` meets its contract

`climbLevel_spec`: the prologue (`b0`, the reader and the parents' address saved at SP+8 and
SP+16); no node (`b17`, then `Some 0`), or the set-up (`b1`) and the loop over the nodes
(`loop_spec`). The nodes are the words in memory (`exists_nodesAt`), the only ones there
(`NodesAt.unique`).
-/

namespace NativeRustcVmArm.Wire.ClimbLevel

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt InAny Region)
open NativeRustcVmArm.Vm.ClimbLevel
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

public section

/-- **Mapped memory holds nodes.** -/
theorem exists_nodesAt {d : Mem 64} {a : BitVec 64} :
    ∀ n : Nat, NativeRustcVm.Mapped d a (40 * n) → ∃ ns : List (Nat × Digest),
      ns.length = n ∧ NodesAt d a ns
  | 0, _ => ⟨[], rfl, fun _ h ↦ absurd h (Nat.not_lt_zero _)⟩
  | n + 1, h => by
    obtain ⟨h1, h2⟩ := (NativeRustcVm.mapped_append_iff (n := 40 * n) (m := 40)).mp
      (by rwa [Nat.mul_succ] at h)
    obtain ⟨ns, hl, hns⟩ := exists_nodesAt n h1
    obtain ⟨L, hL, hw⟩ := exists_wordsAt (d := d) 5 _ h2
    match L, hL, hw with
    | [w0, w1, w2, w3, w4], _, hw =>
      refine ⟨ns ++ [(w0.toNat, #v[w1, w2, w3, w4])], by simp [hl], NodesAt.append_one hns ?_⟩
      rw [hl]
      have g := fun (i : Nat) (hi : i < 5) ↦ hw.getElem (i := i) (by simpa using hi)
      refine nodeAt_iff.mpr ⟨UInt64.toNat_lt _, ?_, g 1 (by omega), g 2 (by omega),
        g 3 (by omega), g 4 (by omega)⟩
      have := g 0 (by omega)
      rw [Nat.mul_zero, NativeRustcVm.addr_add_zero] at this
      simpa using this

variable [Host] {k : Nat} {m0 : MachineData} {bp : BitVec 64} {B : List UInt8} {c : Nat}
  {ns : List (Nat × Digest)}

/-- **From the entry.** -/
theorem entry_spec (hp : Placed code k) (G : Geo m0 bp B)
    (hh : Spec (Labels.label NativeRustcVmArm.Vm.HashPair.entryLabel) HashPairPre HashPairPost)
    (hd : Spec (Labels.label NativeRustcVmArm.Vm.ReaderDigest.entryLabel) ReaderDigestPre ReaderDigestPost)
    (hR : ReaderAt m0.dmem (rdr m0) bp B c)
    (hns : NodesAt m0.dmem (nodes m0) ns) (hlen : ns.length = cnt m0) :
    Eventually (step1 Host.exe) (Post m0) ⟨m0, Host.addrOf (k + NativeRustcVmArm.Vm.ClimbLevel.b0Offset)⟩ := by
  have hst := G.g.st
  have hN := hst.2.1
  have hn := G.n256
  have h224 := stack224
  let env0 := Env.ofMachine m0 [(base m0 224, 224)]
  have hb := Ring.base_noWrap (m0 := m0) (F := 224) (by omega)
  have hwf0 : env0.WF :=
    Env.wf_of ⟨⟨Ring.frame_mapped hst (by decide), hb⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hm0 : Match env0 entryS m0 := match_ofMachine ⟨rfl, fun _ ↦ G.aligned, trivial⟩
    (by simp only [Sym.eval, Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
          Option.getD_some]
        rw [show BitVec.ofInt 64 224 = BitVec.ofNat 64 224 from rfl]
        exact Ring.base_add_eq.symm)
    trivial trivial trivial trivial
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_b0 hwf0 hm0 fun s1 hm1 hpc1 ↦ ?_
  rw [← after_eq run_b0] at hm1
  have hfr1 : Frm m0 s1.data :=
    Fr.ofPrologue hN (by omega) hm1 hwf0 (by decide) (by decide +kernel) (by decide)
      (by decide +kernel) (by simp)
  have hs1 := Match.sameOutside_in hm1 hwf0 (r0 := 0) (o := 0) (n := 224) rfl (by omega)
    (by decide +kernel)
  rw [NativeRustcVm.addr_add_zero] at hs1
  have hR1 : ReaderAt s1.data.dmem (rdr m0) bp B c :=
    G.g.reader_frame rfl hR (NativeRustcVm.SameOutside.mono hs1 fun _ h ↦
      .inl (G.inStack (by rw [G.bF]; omega) (by rw [G.bF]; omega) h))
  rw [after_eq run_b0] at hm1
  have ha : ∀ x ∈ [XReg.X1, .X2, .X3], s1.data.regs.getXReg x = m0.regs.getXReg x := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> exact Match.reg_eq hm0 hm1 rfl rfl
  have hdn : Done m0 bp B c ns 0 [] c s1.data.dmem :=
    ⟨by simp [sibsM], hR1, fun _ h ↦ absurd h (by simp), fun _ h ↦ absurd h (by simp [parentsOf])⟩
  have hc : (SBool.cmp .eq .W64 (.reg .X2) (.lit 0)).eval env0 = decide (cnt m0 = 0) := by
    simp only [SBool.eval, eq_apply]
    rfl
  simp only [PcOk, hc] at hpc1
  by_cases h0 : cnt m0 = 0
  · simp only [h0, decide_true, ↓reduceIte, hp.label (j := NativeRustcVmArm.Vm.ClimbLevel.b17Offset) NativeRustcVmArm.Vm.ClimbLevel.label_13_at] at hpc1
    have hwf2 := G.frEnv_wf hfr1
    have hm2 := G.frEnv_match hfr1
    refine exec_at (infix_of b17_in_code (by simp [b17]) hp) run_b17 hwf2 hpc1 hm2
      fun s2 hm2' hpc2 ↦ ?_
    have hfr2 : Frm m0 s2.data := Fr.ofBlock hfr1 hm2 hm2' hwf2 rfl rfl rfl
      fun x hx ↦ absurd hx (by simp)
    simp only [PcOk] at hpc2
    refine ok_spec hp G hR hns hlen (sl := []) (ci := c) (hpc2.trans (congrArg Host.addrOf rfl))
      hfr2 (by rw [hm2'.dmem_eq hwf2 rfl, h0]; exact hdn) ?_
    show (s2.data.regs.getXReg .X19).toBitVec.toNat = _
    rw [hm2'.regs .X19 _ rfl]
    simp [parentsOf, Sym.eval]
  simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc1
  have hwf2 := G.frEnv_wf hfr1
  have hm2 := G.frEnv_match hfr1
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) run_b1 hwf2
    (hpc1.trans (congrArg Host.addrOf rfl)) hm2 fun s2 hm2' hpc2 ↦ ?_
  have hfr2 : Frm m0 s2.data := Fr.ofBlock hfr1 hm2 hm2' hwf2 rfl rfl rfl
    fun x hx ↦ absurd hx (by simp)
  have hd2 : s2.data.dmem = s1.data.dmem := hm2'.dmem_eq hwf2 rfl
  simp only [PcOk, hp.label (j := NativeRustcVmArm.Vm.ClimbLevel.b6Offset) NativeRustcVmArm.Vm.ClimbLevel.label_5_at] at hpc2
  have hnw := G.ndNw
  have h40 : (UnOp.apply (.ubfm 61 60) .W64 (BinOp.apply .add .W64
      (s1.data.regs.getXReg .X2).toBitVec
      (UnOp.apply (.shift .LSL 2) .W64 (s1.data.regs.getXReg .X2).toBitVec))).toNat =
      40 * cnt m0 := by
    rw [Find.times40 (by rw [ha .X2 (by simp)]; show 40 * cnt m0 < 2 ^ 64; omega),
      ha .X2 (by simp)]
    rfl
  have h1 : (s1.data.regs.getXReg .X1).toBitVec = nodes m0 := by rw [ha .X1 (by simp)]; rfl
  have hfx : Fix m0 s2.data := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hm2'.regs .X22 _ rfl]
      show (s1.data.regs.getXReg .X3).toBitVec = _
      rw [ha .X3 (by simp)]; rfl
    · show (s2.data.regs.getXReg .X25).toBitVec.toNat = _
      rw [hm2'.regs .X25 _ rfl]
      exact h40
    · rw [hm2'.regs .X27 _ rfl]
      rfl
    · have h40' : UnOp.apply (.ubfm 61 60) .W64 (BinOp.apply .add .W64
          (s1.data.regs.getXReg .X2).toBitVec
          (UnOp.apply (.shift .LSL 2) .W64 (s1.data.regs.getXReg .X2).toBitVec)) =
          BitVec.ofNat 64 (40 * cnt m0) := by
        apply BitVec.eq_of_toNat_eq
        rw [h40, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      rw [hm2'.regs .X28 _ rfl]
      simp only [Sym.eval, Env.ofMachine_regs]
      rw [h40', h1]
      simp only [BinOp.apply, Sym.low_W64, Sym.ext_W64]
    · rw [hm2'.regs .X29 _ rfl]
      simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs, h1]
      exact BitVec.sub_add_cancel _ _
  refine Eventually.bind (b6_spec hp G hh hd hR hns hlen (i := 0) (sl := []) (ci := c) hpc2 hfr2
    hfx (by rw [hd2]; exact hdn) (by omega) ?_ ?_ ?_) fun st' h ↦ ?_
  · show (s2.data.regs.getXReg .X19).toBitVec.toNat = _
    rw [hm2'.regs .X19 _ rfl]
    simp [parentsOf, Sym.eval]
  · show (s2.data.regs.getXReg .X20).toBitVec.toNat = _
    rw [hm2'.regs .X20 _ rfl]
    rfl
  · rw [hm2'.regs .X23 _ rfl]
    show (s1.data.regs.getXReg .X1).toBitVec = nodes m0 + BitVec.ofNat 64 (40 * 0)
    rw [h1, Nat.mul_zero, NativeRustcVm.addr_add_zero]
  · rcases h with h | ⟨sl', ci', h⟩
    · exact .done _ h
    · exact loop_spec hp G hh hd hR hns hlen h

/-- **`climb_level` meets its contract.** -/
theorem climbLevel_spec (hp : Placed code k)
    (hh : Spec (Labels.label NativeRustcVmArm.Vm.HashPair.entryLabel) HashPairPre HashPairPost)
    (hd : Spec (Labels.label NativeRustcVmArm.Vm.ReaderDigest.entryLabel) ReaderDigestPre ReaderDigestPost) :
    Spec (Labels.label NativeRustcVmArm.Vm.ClimbLevel.entryLabel) ClimbLevelPre ClimbLevelPost := by
  intro m0 hpre
  obtain ⟨-, -, -, ⟨hnm, -⟩, -, -, bp, B, c, hR, -⟩ := id hpre
  obtain ⟨ns, hlen, hns⟩ := exists_nodesAt (d := m0.dmem) (a := nodes m0) (cnt m0) hnm
  rw [hp.label (j := NativeRustcVmArm.Vm.ClimbLevel.entryOffset) NativeRustcVmArm.Vm.ClimbLevel.entry_at]
  exact entry_spec hp (geo_of hpre hR) hh hd hR hns hlen

end

end NativeRustcVmArm.Wire.ClimbLevel
