module

public import NativeRustcVmArm.Code.Vm.HashPair.Names
public import NativeRustcVmArm.Wire.ClimbLevel.Hash

/-!
# `climb_level`'s parents

After node `i`'s sibling (`Mid`): `hash_pair` of node `i`'s digest and its sibling's, in order
(`b14`, `hash14_spec`) or the sibling's first (`b2`, `hash2_spec`); the hash at SP+96
(`Hashed`); the count checked (`b15`, `b3`), the parent stored.
-/

namespace NativeRustcVmArm.Wire.ClimbLevel

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt InAny Region)
open NativeRustcVmArm.Vm.ClimbLevel
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

@[expose] public section

variable (m0 : MachineData) (bp : BitVec 64) (B : List UInt8) (c : Nat) (ns : List (Nat × Digest))

/-- Node `i`'s parent hashed: `H` at SP+96. -/
structure Hashed (i : Nat) (sl : List (Nat × Digest × Bool)) (ci : Nat) (q : Nat × Digest × Bool)
    (H : Digest) (m : MachineData) : Prop where
  fr : Frm m0 m
  fx : Fix m0 m
  lt : i < cnt m0
  hi : i < ns.length
  hs : sibsM B ns (ns.take (i + 1)) c = some (sl ++ [q], ci)
  rd : ReaderAt m.dmem (rdr m0) bp B ci
  sb : NodesAt m.dmem (sibs m0) ((sl ++ [q]).map fun s ↦ (s.1, s.2.1))
  nx : NodesAt m.dmem (nxt m0) (parentsOf (ns.take i) sl)
  hl : sl.length = i
  hH : WordsAt m.dmem (base m0 224 + BitVec.ofNat 64 96) H.toList
  x19 : (m.regs.getXReg .X19).toNat = (parentsOf (ns.take i) sl).length
  x20 : (m.regs.getXReg .X20).toNat = i + 1
  x21 : (m.regs.getXReg .X21).toNat = q.1
  x23 : (m.regs.getXReg .X23).toBitVec = nd m0 (i + 1)

end

public section

variable {m0 : MachineData} {bp : BitVec 64} {B : List UInt8} {c : Nat} {ns : List (Nat × Digest)}

/-- **Hashed**, kept by a block without writes. -/
theorem Hashed.keep {i : Nat} {sl : List (Nat × Digest × Bool)} {ci : Nat}
    {q : Nat × Digest × Bool} {H : Digest} {m m' : MachineData}
    (h : Hashed m0 bp B c ns i sl ci q H m) (hfr : Frm m0 m') (hd : m'.dmem = m.dmem)
    (hr : ∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X25, .X27, .X28, .X29],
      m'.regs.getXReg r = m.regs.getXReg r) :
    Hashed m0 bp B c ns i sl ci q H m' :=
  ⟨hfr, h.fx.keep fun r h ↦ hr r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
      rcases h with rfl | rfl | rfl | rfl | rfl <;> simp),
    h.lt, h.hi, h.hs, by rw [hd]; exact h.rd, by rw [hd]; exact h.sb, by rw [hd]; exact h.nx, h.hl,
    by rw [hd]; exact h.hH, by rw [hr .X19 (by simp)]; exact h.x19,
    by rw [hr .X20 (by simp)]; exact h.x20, by rw [hr .X21 (by simp)]; exact h.x21,
    by rw [hr .X23 (by simp)]; exact h.x23⟩

/-- **Hashed**, after the call from the sibling's state. -/
theorem Hashed.of_call [Labels] (G : Geo m0 bp B) {i : Nat} {sl : List (Nat × Digest × Bool)}
    {ci : Nat} {q : Nat × Digest × Bool} {H : Digest} {m m2 : MachineData}
    (hM : Mid m0 bp B c ns i sl ci q m) (hi : i < ns.length) (hfr2 : Frm m0 m2)
    (hH : WordsAt m2.dmem (base m0 224 + BitVec.ofNat 64 96) H.toList)
    (hs : SameOutside m.dmem m2.dmem (fun a ↦ Keep m0 256 256 a ∧
      ¬InRange (rdr m0 + BitVec.ofNat 64 16) 8 a))
    (hr : ∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X25, .X27, .X28, .X29],
      m2.regs.getXReg r = m.regs.getXReg r) :
    Hashed m0 bp B c ns i sl ci q H m2 := by
  have hk := NativeRustcVm.SameOutside.mono hs fun _ h ↦ h.1
  have hpl := parentsOf_length_le (ns.take i) sl
  have htl := List.length_take_le i ns
  have hn := G.n256
  have hlt := hM.lt
  exact ⟨hfr2, hM.fx.keep fun r h ↦ hr r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
      rcases h with rfl | rfl | rfl | rfl | rfl <;> simp),
    hM.lt, hi, hM.hs, G.keep_reader (by omega) (by omega) hs (fun _ h ↦ h) hM.rd,
    G.keep_sibs (by omega) (by omega) hk (by simp [hM.hl]; omega) hM.sb,
    G.keep_nxt (by omega) (by omega) hk (by omega) hM.nx, hM.hl, hH,
    by rw [hr .X19 (by simp)]; exact hM.x19, by rw [hr .X20 (by simp)]; exact hM.x20,
    by rw [hr .X21 (by simp)]; exact hM.x21, by rw [hr .X23 (by simp)]; exact hM.x23⟩

variable [Host] {k : Nat}

/-- **The count checked** (`b15`), then the parent stored. -/
theorem b15_spec (hp : Placed code k) (G : Geo m0 bp B) {i : Nat}
    {sl : List (Nat × Digest × Bool)} {ci : Nat} {q : Nat × Digest × Bool} {H : Digest}
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.ClimbLevel.b15Offset))
    (h : Hashed m0 bp B c ns i sl ci q H st.data) (hkey : q.1 = (ns[i]'h.hi).1)
    (hpar : parentOf (ns[i]'h.hi) q = [((ns[i]'h.hi).1 >>> 1, H)]) :
    Eventually (step1 Host.exe) (Head m0 bp B c ns k (i + 1) (sl ++ [q]) ci) st := by
  have hwf := G.frEnv_wf h.fr
  have hm := G.frEnv_match h.fr
  refine exec_at (infix_of b15_in_code (by simp [b15]) hp) run_b15 hwf hpc hm fun st1 hm1 hpc1 ↦ ?_
  have hd1 : st1.data.dmem = st.data.dmem := hm1.dmem_eq hwf rfl
  have hfr1 : Frm m0 st1.data := Fr.ofBlock h.fr hm hm1 hwf rfl rfl rfl
    fun x hx ↦ absurd hx (by simp)
  have hr : ∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X25, .X27, .X28, .X29],
      st1.data.regs.getXReg r = st.data.regs.getXReg r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact Match.reg_eq hm hm1 rfl rfl
  have hc : (SBool.cmp .ult .W64 (.reg .X19) (.lit 256)).eval (frEnv m0 st.data) = true := by
    simp only [SBool.eval, ult_apply, Sym.eval, Env.ofMachine_regs, decide_eq_true_eq]
    rw [UInt64.toNat_toBitVec, h.x19, BitVec.toNat_ofNat]
    exact parents_lt (by have := h.lt; have := G.n256; omega)
  simp only [PcOk, hc, ↓reduceIte, hp.label (j := NativeRustcVmArm.Vm.ClimbLevel.b4Offset) NativeRustcVmArm.Vm.ClimbLevel.label_3_at] at hpc1
  have h' := h.keep hfr1 hd1 hr
  exact store_spec hp G hpc1 h'.fr h'.fx h'.lt h'.hi h'.hs h'.rd h'.sb h'.nx h'.hl h'.hH hpar
    h'.x19 h'.x20 (by rw [h'.x21, hkey]) h'.x23

/-- **The count checked** (`b3`), then the parent stored. -/
theorem b3_spec (hp : Placed code k) (G : Geo m0 bp B) {i : Nat}
    {sl : List (Nat × Digest × Bool)} {ci : Nat} {q : Nat × Digest × Bool} {H : Digest}
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.ClimbLevel.b3Offset))
    (h : Hashed m0 bp B c ns i sl ci q H st.data) (hkey : q.1 = (ns[i]'h.hi).1)
    (hpar : parentOf (ns[i]'h.hi) q = [((ns[i]'h.hi).1 >>> 1, H)]) :
    Eventually (step1 Host.exe) (Head m0 bp B c ns k (i + 1) (sl ++ [q]) ci) st := by
  have hwf := G.frEnv_wf h.fr
  have hm := G.frEnv_match h.fr
  refine exec_at (infix_of b3_in_code (by simp [b3]) hp) run_b3 hwf hpc hm fun st1 hm1 hpc1 ↦ ?_
  have hd1 : st1.data.dmem = st.data.dmem := hm1.dmem_eq hwf rfl
  have hfr1 : Frm m0 st1.data := Fr.ofBlock h.fr hm hm1 hwf rfl rfl rfl
    fun x hx ↦ absurd hx (by simp)
  have hr : ∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X25, .X27, .X28, .X29],
      st1.data.regs.getXReg r = st.data.regs.getXReg r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact Match.reg_eq hm hm1 rfl rfl
  have hc : (SBool.cmp .ult .W64 (.reg .X19) (.lit 256)).not.eval (frEnv m0 st.data) = false := by
    simp only [SBool.eval, ult_apply, Sym.eval, Env.ofMachine_regs, Bool.not_eq_false',
      decide_eq_true_eq]
    rw [UInt64.toNat_toBitVec, h.x19, BitVec.toNat_ofNat]
    exact parents_lt (by have := h.lt; have := G.n256; omega)
  simp only [PcOk, hc, Bool.false_eq_true, ↓reduceIte] at hpc1
  have h' := h.keep hfr1 hd1 hr
  exact store_spec hp G (hpc1.trans (congrArg Host.addrOf rfl)) h'.fr h'.fx h'.lt h'.hi h'.hs
    h'.rd h'.sb h'.nx h'.hl h'.hH hpar h'.x19 h'.x20 (by rw [h'.x21, hkey]) h'.x23

omit [Host] in
theorem saved_regs : ∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X25, .X27, .X28, .X29],
    calleeSaved r = true := by decide

/-- **Node `i` first** (`b14`, `hash_pair`, `b15`): an even key, or its sibling carried. -/
theorem hash14_spec (hp : Placed code k) (G : Geo m0 bp B)
    (hh : Spec (Labels.label NativeRustcVmArm.Vm.HashPair.entryLabel) HashPairPre HashPairPost)
    (hns : NodesAt m0.dmem (nodes m0) ns) (hlen : ns.length = cnt m0) {i : Nat}
    {sl : List (Nat × Digest × Bool)} {ci : Nat} {q : Nat × Digest × Bool} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.ClimbLevel.b14Offset)) (hM : Mid m0 bp B c ns i sl ci q st.data)
    (hi : i < ns.length)
    (hpar : parentOf ns[i] q = [(ns[i].1 >>> 1, NativeVm.Model.hashPair ns[i].2 q.2.1)]) :
    Eventually (step1 Host.exe) (Head m0 bp B c ns k (i + 1) (sl ++ [q]) ci) st := by
  have hwf := G.frEnv_wf hM.fr
  have hm := G.frEnv_match hM.fr
  refine exec_at (infix_of b14_in_code (by simp [b14]) hp) run_b14 hwf hpc hm fun st1 hm1 hpc1 ↦ ?_
  have hd1 : st1.data.dmem = st.data.dmem := hm1.dmem_eq hwf rfl
  have hfr1 : Frm m0 st1.data := Fr.ofBlock hM.fr hm hm1 hwf rfl rfl rfl
    fun x hx ↦ absurd hx (by simp)
  have hr1 : ∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X25, .X27, .X28, .X29],
      st1.data.regs.getXReg r = st.data.regs.getXReg r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact Match.reg_eq hm hm1 rfl rfl
  have hx0 : st1.data.regs.X0.toBitVec = base m0 224 + BitVec.ofNat 64 96 := hm1.regs .X0 _ rfl
  have hx1 : st1.data.regs.X1.toBitVec = nd m0 i + BitVec.ofNat 64 8 := by
    rw [show st1.data.regs.X1 = st1.data.regs.getXReg .X1 from rfl, hm1.regs .X1 _ rfl]
    simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
    rw [hM.x24]
  have hx2 : st1.data.regs.X2.toBitVec = base m0 224 + BitVec.ofNat 64 64 := hm1.regs .X2 _ rfl
  have hnd := (G.nodes_frm hlen hns hfr1 i hi).2.2
  refine hash_call G hh hfr1 hpc1 hx0 hx1 hx2 (G.hashArg_node hfr1 hM.lt)
    (G.hashArg_frame hfr1 (by omega)) (L := ns[i].2) (Rd := q.2.1) hnd
    (by rw [hd1]; exact hM.dg) fun m2 hfr2 hH hs2 hcs ↦ ?_
  have hr2 : ∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X25, .X27, .X28, .X29],
      m2.regs.getXReg r = st.data.regs.getXReg r := fun r hr ↦
    (hcs r (saved_regs r hr)).trans (hr1 r hr)
  exact b15_spec hp G (show Host.addrOf (k + NativeRustcVmArm.Vm.ClimbLevel.b14Offset + b14.length) = Host.addrOf (k + NativeRustcVmArm.Vm.ClimbLevel.b15Offset) from
    congrArg Host.addrOf rfl) (Hashed.of_call G hM hi hfr2 hH (by rw [← hd1]; exact hs2) hr2)
    (hM.key hi) hpar

/-- **The sibling first** (`b2`, `hash_pair`, `b3`): an odd key, its sibling read. -/
theorem hash2_spec (hp : Placed code k) (G : Geo m0 bp B)
    (hh : Spec (Labels.label NativeRustcVmArm.Vm.HashPair.entryLabel) HashPairPre HashPairPost)
    (hns : NodesAt m0.dmem (nodes m0) ns) (hlen : ns.length = cnt m0) {i : Nat}
    {sl : List (Nat × Digest × Bool)} {ci : Nat} {q : Nat × Digest × Bool} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.ClimbLevel.b2Offset)) (hM : Mid m0 bp B c ns i sl ci q st.data)
    (hi : i < ns.length)
    (hpar : parentOf ns[i] q = [(ns[i].1 >>> 1, NativeVm.Model.hashPair q.2.1 ns[i].2)]) :
    Eventually (step1 Host.exe) (Head m0 bp B c ns k (i + 1) (sl ++ [q]) ci) st := by
  have hwf := G.frEnv_wf hM.fr
  have hm := G.frEnv_match hM.fr
  refine exec_at (infix_of b2_in_code (by simp [b2]) hp) run_b2 hwf hpc hm fun st1 hm1 hpc1 ↦ ?_
  have hd1 : st1.data.dmem = st.data.dmem := hm1.dmem_eq hwf rfl
  have hfr1 : Frm m0 st1.data := Fr.ofBlock hM.fr hm hm1 hwf rfl rfl rfl
    fun x hx ↦ absurd hx (by simp)
  have hr1 : ∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X25, .X27, .X28, .X29],
      st1.data.regs.getXReg r = st.data.regs.getXReg r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact Match.reg_eq hm hm1 rfl rfl
  have hx0 : st1.data.regs.X0.toBitVec = base m0 224 + BitVec.ofNat 64 96 := hm1.regs .X0 _ rfl
  have hx1 : st1.data.regs.X1.toBitVec = base m0 224 + BitVec.ofNat 64 64 := hm1.regs .X1 _ rfl
  have hx2 : st1.data.regs.X2.toBitVec = nd m0 i + BitVec.ofNat 64 8 := by
    rw [show st1.data.regs.X2 = st1.data.regs.getXReg .X2 from rfl, hm1.regs .X2 _ rfl]
    simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
    rw [hM.x24]
  have hnd := (G.nodes_frm hlen hns hfr1 i hi).2.2
  refine hash_call G hh hfr1 hpc1 hx0 hx1 hx2 (G.hashArg_frame hfr1 (by omega))
    (G.hashArg_node hfr1 hM.lt) (L := q.2.1) (Rd := ns[i].2) (by rw [hd1]; exact hM.dg) hnd
    fun m2 hfr2 hH hs2 hcs ↦ ?_
  have hr2 : ∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X25, .X27, .X28, .X29],
      m2.regs.getXReg r = st.data.regs.getXReg r := fun r hr ↦
    (hcs r (saved_regs r hr)).trans (hr1 r hr)
  exact b3_spec hp G (show Host.addrOf (k + NativeRustcVmArm.Vm.ClimbLevel.b2Offset + b2.length) = Host.addrOf (k + NativeRustcVmArm.Vm.ClimbLevel.b3Offset) from
    congrArg Host.addrOf rfl) (Hashed.of_call G hM hi hfr2 hH (by rw [← hd1]; exact hs2) hr2)
    (hM.key hi) hpar

end

end NativeRustcVmArm.Wire.ClimbLevel
