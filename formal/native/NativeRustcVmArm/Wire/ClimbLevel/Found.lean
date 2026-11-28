module

public import NativeRustcVmArm.Code.Vm.HashPair.Names
public import NativeRustcVmArm.Wire.ClimbLevel.Sib

/-!
# `climb_level`'s sibling found among the nodes

`b9`: node `j`, of key node `i`'s `^^^ 1`, its digest node `i`'s sibling (and at SP+64); an odd
key has no parent (the loop's head, `Mid.head`), an even key's parent hashed (`b10`, then
`hash14_spec`): `found_spec`.
-/

namespace NativeRustcVmArm.Wire.ClimbLevel

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt InAny Region)
open NativeRustcVmArm.Vm.ClimbLevel
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

public section

variable [Host] {k : Nat} {m0 : MachineData} {bp : BitVec 64} {B : List UInt8} {c : Nat}
  {ns : List (Nat × Digest)}

/-- **No parent**: the loop's head after node `i`. -/
theorem Mid.head {i : Nat} {sl : List (Nat × Digest × Bool)} {ci : Nat} {q : Nat × Digest × Bool}
    {st : MachineState} (h : Mid m0 bp B c ns i sl ci q st.data) (hi : i < ns.length)
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.ClimbLevel.b5Offset)) (hpar : parentOf ns[i] q = []) :
    Head m0 bp B c ns k (i + 1) (sl ++ [q]) ci st := by
  have htl : (ns.take i).length = sl.length := by rw [List.length_take, h.hl]; omega
  have hp : parentsOf (ns.take (i + 1)) (sl ++ [q]) = parentsOf (ns.take i) sl := by
    rw [take_succ_eq hi, parentsOf_snoc htl, hpar, List.append_nil]
  exact ⟨hpc, h.fr, h.fx, ⟨h.hs, h.rd, h.sb, by rw [hp]; exact h.nx⟩, h.lt, by rw [hp]; exact h.x19,
    h.x20, h.x23⟩

theorem sibAddr_eval {m : MachineData} {rs : List (BitVec 64 × Nat)} {i : Nat} (hi : i < 256)
    (h26 : (m.regs.getXReg .X26).toNat = i) (h22 : (m.regs.getXReg .X22).toBitVec = sibs m0)
    (hnw : (sibs m0).toNat + 10240 ≤ 2 ^ 64) :
    sibAddr.eval (Env.ofMachine m rs) = sb m0 i := by
  simp only [sibAddr, Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs, h22]
  apply BitVec.eq_of_toNat_eq
  rw [toNat_off (by omega)]
  have e64 : (2 : Nat) ^ MemWidth.W64.bits = 2 ^ 64 := rfl
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, UInt64.toNat_toBitVec, h26,
    e64, show (40 : Nat) % 2 ^ 64 = 40 from rfl]
  have e3 : (sibs m0).toNat = m0.regs.X3.toNat := rfl
  omega

/-- **The sibling found** (`b9`): node `j` of key node `i`'s `^^^ 1`, the first. -/
theorem found_spec (hp : Placed code k) (G : Geo m0 bp B)
    (hh : Spec (Labels.label NativeRustcVmArm.Vm.HashPair.entryLabel) HashPairPre HashPairPost)
    (hns : NodesAt m0.dmem (nodes m0) ns) (hlen : ns.length = cnt m0) {i j : Nat}
    {sl : List (Nat × Digest × Bool)} {ci : Nat} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.ClimbLevel.b9Offset)) (hC : Cur m0 bp B c ns i sl ci st.data)
    (hj : j < cnt m0) (hx8 : (st.data.regs.getXReg .X8).toBitVec = nd m0 j)
    (hi : i < ns.length) (hjl : j < ns.length) (hk : ns[j].1 = ns[i].1 ^^^ 1)
    (hmiss : Miss ns i j) (h21 : (st.data.regs.getXReg .X21).toNat = ns[i].1) :
    Eventually (step1 Host.exe) (fun st' ↦ ∃ sl' ci', Head m0 bp B c ns k (i + 1) sl' ci' st') st := by
  have hn := G.n256
  have hlt := hC.lt
  have hsp := G.sp
  have h224 := stack224
  have hi256 : i < 256 := by omega
  have := G.ndNw; have := G.sbNw; have := G.nS; have := G.sS; have := G.nSb
  have hnd0 := G.nd0 hj
  have hsb0 := G.sb0 hi256
  have hwf : (Env.ofMachine st.data [(base m0 224, 224), (nd m0 j, 40), (sb m0 i, 40)]).WF :=
    G.env3_wf hC.fr (G.ndMap' hj (le_refl _)) (by rw [hnd0]; omega) (by rw [hnd0]; omega)
      (G.sbMap' hi256) (by rw [hsb0]; omega) (by rw [hsb0]; omega) (by rw [hnd0, hsb0]; omega)
  have hm : Match (Env.ofMachine st.data [(base m0 224, 224), (nd m0 j, 40), (sb m0 i, 40)])
      foundS st.data :=
    match_ofMachine ⟨rfl, fun _ ↦ G.aligned, rfl, nofun, rfl, nofun, trivial⟩
      (by rw [hC.fr.sp]; simp [Sym.eval]) trivial trivial trivial
      ⟨by
        show (st.data.regs.getXReg .X8).toBitVec = nd m0 j + BitVec.ofInt 64 0
        rw [hx8, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero],
      by
        show sibAddr.eval _ = sb m0 i + BitVec.ofInt 64 0
        rw [sibAddr_eval hi256 hC.x26 hC.fx.x22 G.sbNw, show BitVec.ofInt 64 0 = 0#64 from rfl,
          BitVec.add_zero], trivial⟩
  refine exec_at (infix_of b9_in_code (by simp [b9]) hp) run_b9 hwf hpc hm fun st1 hm1 hpc1 ↦ ?_
  have hfr1 : Frm m0 st1.data := G.frm_block hC.fr hm hm1 hwf rfl rfl rfl (r1 := 2) (by decide)
    rfl (fun t ht ↦ G.sb_outs hi256 ht) (by decide)
  have hS := G.block_same (ls := i) (lp := 256) hm1 hwf rfl (r1 := 2) rfl
    (fun t ht ↦ ⟨G.sb_keep hi256 ht 256, G.sb_cur hi256 ht⟩) (by decide)
  have hk1 := NativeRustcVm.SameOutside.mono hS fun _ h ↦ h.1
  have hr : ∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
      st1.data.regs.getXReg r = st.data.regs.getXReg r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact Match.reg_eq hm hm1 rfl rfl
  -- node `j`'s words
  have hnj := nodeAt_iff.mp (G.nodes_frm hlen hns hC.fr j hjl)
  obtain ⟨-, -, w1, w2, w3, w4⟩ := hnj
  have hkey : ns[i].1 < 2 ^ 64 := by rw [← h21]; exact UInt64.toNat_lt _
  have e21 : UInt64.ofBitVec (st.data.regs.getXReg .X21).toBitVec = ns[i].1.toUInt64 :=
    UInt64.toNat_inj.mp (by rw [UInt64.toNat_ofBitVec, UInt64.toNat_toBitVec, h21,
      toNat_toUInt64_of_lt hkey])
  have hsl : sl.length = i := by
    rw [sibsM_length B ns _ c hC.dn.hs, List.length_take]; omega
  let q : Nat × Digest × Bool := (ns[i].1, ns[j].2, true)
  have hnode : NodeAt st1.data.dmem (sb m0 i) (q.1, q.2.1) :=
    node_write hm1 (r := 2) (v0 := .reg .X21) (v1 := .load 1 8 8) (v2 := .load 1 16 8)
      (v3 := .load 1 24 8) (v4 := .load 1 32 8) rfl (by decide) (by decide) (by decide)
      (by decide) (by decide) hkey e21
      (by simp only [Sym.eval]; rw [load_of rfl w1])
      (by simp only [Sym.eval]; rw [load_of rfl w2])
      (by simp only [Sym.eval]; rw [load_of rfl w3])
      (by simp only [Sym.eval]; rw [load_of rfl w4])
  have hdg : WordsAt st1.data.dmem (base m0 224 + BitVec.ofNat 64 64) q.2.1.toList :=
    digest_write hm1 (r := 0) (o := 64) (sz := 224) (v1 := .load 1 8 8) (v2 := .load 1 16 8)
      (v3 := .load 1 24 8) (v4 := .load 1 32 8) rfl (by omega) (by decide) (by decide)
      (by decide) (by decide)
      (by simp only [Sym.eval]; rw [load_of rfl w1])
      (by simp only [Sym.eval]; rw [load_of rfl w2])
      (by simp only [Sym.eval]; rw [load_of rfl w3])
      (by simp only [Sym.eval]; rw [load_of rfl w4])
  have hM : Mid m0 bp B c ns i sl ci q st1.data := by
    refine ⟨hfr1, hC.fx.keep fun r h ↦ hr r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
        rcases h with rfl | rfl | rfl | rfl | rfl <;> simp), hlt,
      sibsM_step hC.dn.hs hi (sibStep_found hi hjl hk hmiss),
      G.keep_reader (by omega) (by omega) hS (fun _ h ↦ h) hC.dn.rd, ?_,
      G.keep_nxt (by omega) (by omega) hk1
        (by have := parentsOf_length_le (ns.take i) sl; have := List.length_take_le i ns; omega)
        hC.dn.nx,
      hsl, fun _ ↦ rfl, hdg, by rw [hr .X19 (by simp)]; exact hC.x19,
      by rw [hr .X20 (by simp)]; exact hC.x20, by rw [hr .X21 (by simp)]; exact h21,
      by rw [hr .X23 (by simp)]; exact hC.x23, by rw [hr .X24 (by simp)]; exact hC.x24⟩
    rw [List.map_append, List.map_singleton]
    refine NodesAt.append_one (G.keep_sibs (by omega) (by omega) hk1 (by simp [hsl]) hC.dn.sb) ?_
    rw [List.length_map, hsl]
    exact hnode
  have hc : (SBool.bit .W32 (.reg .X21) 0).eval
      (Env.ofMachine st.data [(base m0 224, 224), (nd m0 j, 40), (sb m0 i, 40)]) =
      decide (ns[i].1 % 2 = 1) := by
    simp only [SBool.eval, Sym.eval, Env.ofMachine_regs]
    rw [bit0_low, UInt64.toNat_toBitVec, h21]
  simp only [PcOk, hc] at hpc1
  by_cases hodd : ns[i].1 % 2 = 1
  · simp only [hodd, decide_true, ↓reduceIte, hp.label (j := NativeRustcVmArm.Vm.ClimbLevel.b5Offset) NativeRustcVmArm.Vm.ClimbLevel.label_4_at] at hpc1
    exact .done _ ⟨_, _, hM.head hi hpc1 (parent_none hodd rfl)⟩
  · simp only [hodd, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc1
    have hwf2 := G.frEnv_wf hfr1
    have hm2 := G.frEnv_match hfr1
    refine exec_at (infix_of b10_in_code (by simp [b10]) hp) run_b10 hwf2
      (hpc1.trans (congrArg Host.addrOf rfl)) hm2 fun st2 hm2' hpc2 ↦ ?_
    have hfr2 : Frm m0 st2.data := Fr.ofBlock hfr1 hm2 hm2' hwf2 rfl rfl rfl
      fun x hx ↦ absurd hx (by simp)
    have hM2 := hM.keep hfr2 (hm2'.dmem_eq hwf2 rfl) fun r hr ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact Match.reg_eq hm2 hm2' rfl rfl
    simp only [PcOk, hp.label (j := NativeRustcVmArm.Vm.ClimbLevel.b14Offset) NativeRustcVmArm.Vm.ClimbLevel.label_11_at] at hpc2
    exact Eventually.mono (hash14_spec hp G hh hns hlen hpc2 hM2 hi (parent_even (by omega)))
      fun _ h ↦ ⟨_, _, h⟩

end

end NativeRustcVmArm.Wire.ClimbLevel
