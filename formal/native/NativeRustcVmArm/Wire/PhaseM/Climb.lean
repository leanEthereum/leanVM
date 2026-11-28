module

public import NativeRustcVmArm.Wire.PhaseM.HashRun

/-!
# `phase_m`: the climb's states

`ClimbSt l`: at level `l`'s head (`b31`), the levels read so far `acc`, the level's nodes `ns` at
the working area's byte `4096 + 10240 (l % 2)`, the rest of the climb in the model (`climb_acc`).
`Pre36`: at `write_openings`' call (`b36`), every level read. `climb_entry`: from `Climb0`, the
climb's set-up (`b29`, `b30`) to level 0, or with height zero to `Pre36`.
-/

namespace NativeRustcVmArm.Wire.PhaseM

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt InAny Region)
open NativeRustcVmArm.Vm.PhaseM
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.KeccakHash

@[expose] public section

/-- The siblings' levels' base and their counts' base. -/
abbrev sibA (m0 : MachineData) : BitVec 64 := wa m0 24832
abbrev cntA (m0 : MachineData) : BitVec 64 := wa m0 24576

/-- **At level `l`'s head** (`b31`). -/
structure ClimbSt [Host] (m0 : MachineData) (bp : BitVec 64) (B : List UInt8) (c k count : Nat)
    (qs : List Nat) (height lw : Nat) (rows : List (List K)) (c6 l : Nat)
    (acc : List (List (Nat × Digest))) (ns : List (Nat × Digest)) (cl : Nat) (st : MachineState) :
    Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.PhaseM.b31Offset)
  base : Base m0 st.data
  mid : Mid m0 B c count qs height lw rows c6 st.data.dmem
  accl : acc.length = l
  model : climbM B height (nodes0 qs lw rows) c6 =
    (climbM B (height - l) ns cl).map fun q ↦ (acc ++ q.1, q.2)
  ll : l < height
  nsl : ns.length ≤ 256
  sibs : SibsAt st.data.dmem (sibA m0) (cntA m0) acc
  nodes : NodesAt st.data.dmem (wa m0 (4096 + 10240 * (l % 2))) ns
  rd : ReaderAt st.data.dmem (rdr m0) bp B cl
  f24 : FW m0 st.data.dmem 24 (UInt64.ofBitVec (sibA m0))
  x21 : (st.data.regs.getXReg .X21).toNat = count
  x24 : (st.data.regs.getXReg .X24).toNat = height
  x26 : (st.data.regs.getXReg .X26).toNat = (sortD qs).length
  x25 : (st.data.regs.getXReg .X25).toNat = l
  x23 : (st.data.regs.getXReg .X23).toBitVec = wa m0 (24576 + 8 * l)
  x27 : (st.data.regs.getXReg .X27).toBitVec = wa m0 14336
  x28 : (st.data.regs.getXReg .X28).toNat = ns.length
  x29 : (st.data.regs.getXReg .X29).toBitVec = wa m0 (24832 + 10240 * l)

/-- **At `write_openings`' call** (`b36`), every level read. -/
structure Pre36 [Host] (m0 : MachineData) (bp : BitVec 64) (B : List UInt8) (c k count : Nat)
    (qs : List Nat) (height lw : Nat) (rows : List (List K)) (c6 : Nat)
    (sl : List (List (Nat × Digest))) (cf : Nat) (st : MachineState) : Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.PhaseM.b36Offset)
  base : Base m0 st.data
  mid : Mid m0 B c count qs height lw rows c6 st.data.dmem
  model : climbM B height (nodes0 qs lw rows) c6 = some (sl, cf)
  sll : sl.length = height
  sibs : SibsAt st.data.dmem (sibA m0) (cntA m0) sl
  rd : ReaderAt st.data.dmem (rdr m0) bp B cf
  x21 : (st.data.regs.getXReg .X21).toNat = count
  x24 : (st.data.regs.getXReg .X24).toNat = height
  x26 : (st.data.regs.getXReg .X26).toNat = (sortD qs).length
  x5 : (st.data.regs.getXReg .X5).toNat = lw
  x8 : (st.data.regs.getXReg .X8).toBitVec = cntA m0
  x29 : (st.data.regs.getXReg .X29).toBitVec = sibA m0

end

public section

theorem climbM_zero (B : List UInt8) (ns : List (Nat × Digest)) (c : Nat) :
    climbM B 0 ns c = some ([], c) := rfl

theorem climbFin_some {B : List UInt8} {qs : List Nat} {height lw : Nat} {rows : List (List K)}
    {c6 : Nat} {sl : List (List (Nat × Digest))} {cf : Nat}
    (h : climbM B height (nodes0 qs lw rows) c6 = some (sl, cf)) :
    climbFin B qs height lw rows c6 =
      some (⟨height, lw, qs.map (openingAt (sortD qs) (leavesOf lw rows) sl height)⟩, cf) := by
  unfold climbFin; rw [h]

theorem climbFin_none {B : List UInt8} {qs : List Nat} {height lw : Nat} {rows : List (List K)}
    {c6 : Nat} (h : climbM B height (nodes0 qs lw rows) c6 = none) :
    climbFin B qs height lw rows c6 = none := by
  unfold climbFin; rw [h]

variable {m0 : MachineData} {bp : BitVec 64} {B : List UInt8} {c : Nat} [Host] {k : Nat}

/-- **The climb's set-up.** -/
theorem climb_entry (hp : Placed code k) (G : Geo m0 bp B) {count : Nat} {qs : List Nat}
    {height lw : Nat} {rows : List (List K)} {c6 : Nat} {st : MachineState}
    (h : Climb0 m0 bp B c k count qs height lw rows c6 st) :
    Eventually (step1 Host.exe) (fun st' ↦
      (∃ sl cf, Pre36 m0 bp B c k count qs height lw rows c6 sl cf st') ∨
      ClimbSt m0 bp B c k count qs height lw rows c6 0 [] (nodes0 qs lw rows) c6 st') st := by
  obtain ⟨hpc, hb, hM, hrd, x21, x26, x5, hnd⟩ := h
  have hst := G.st
  -- `b29`
  refine blk hp b29_in_code (by simp [b29]) run_b29 rfl rfl hst hb.fr hpc
    fun s1 hfr1 hd1 hm1 hpc1 ↦ ?_
  have hm := frEnv_match hst hb.fr
  have r1 : ∀ r ∈ [XReg.X5, .X19, .X20, .X21, .X22, .X26], s1.data.regs.getXReg r =
      st.data.regs.getXReg r := regs_of hm hm1 (by decide)
  have hb1 : Base m0 s1.data := hb.of_regs hfr1 fun r hr ↦ r1 r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl <;> simp)
  have e32 : (frEnv m0 st.data).load 0 32 8 = height.toUInt64.toBitVec := load_fw hM.f32
  have hh : height.toUInt64.toBitVec.toNat = height := by
    rw [UInt64.toNat_toBitVec, toNat_toUInt64_of_lt (by have := hM.h32; omega)]
  have x24 : (s1.data.regs.getXReg .X24).toNat = height := by
    show (s1.data.regs.getXReg .X24).toBitVec.toNat = _
    rw [hm1.regs .X24 _ rfl]; show ((frEnv m0 st.data).load 0 32 8).toNat = _
    rw [e32, hh]
  have x29 : (s1.data.regs.getXReg .X29).toBitVec = sibA m0 := by
    rw [hm1.regs .X29 _ rfl]; simp only [Sym.eval, Env.ofMachine_regs]; rw [hb.x19, add_lit]
  have hc : (SBool.cmp .eq .W64 (.load 0 32 8) (.lit 0)).eval (frEnv m0 st.data) =
      decide (height = 0) := by
    simp only [SBool.eval, Sym.eval]; rw [eq_lit _ 0 (by decide), e32, hh]
  simp only [PcOk, hc] at hpc1
  by_cases h0 : height = 0
  · simp only [h0, decide_true, ↓reduceIte] at hpc1
    subst h0
    refine .done _ (.inl ⟨[], c6, ⟨hpc1.trans (hp.label (j := NativeRustcVmArm.Vm.PhaseM.b36Offset) NativeRustcVmArm.Vm.PhaseM.label_27_at), hb1, by rw [hd1]; exact hM,
      rfl, rfl, fun j hj ↦ absurd hj (by simp), by rw [hd1]; exact hrd,
      by rw [r1 .X21 (by simp)]; exact x21, x24, by rw [r1 .X26 (by simp)]; exact x26,
      by rw [r1 .X5 (by simp)]; exact x5, ?_, x29⟩⟩)
    rw [hm1.regs .X8 _ rfl]; simp only [Sym.eval, Env.ofMachine_regs]; rw [hb.x19, add_lit]
  simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc1
  -- `b30`
  refine blkW hp b30_in_code (by simp [b30]) run_b30 (by decide) rfl hst hb1.fr hpc1
    fun s2 hfr2 hs2 hm2 hpc2 ↦ .done _ (.inr ?_)
  have hm' := frEnv_match hst hb1.fr
  have hwf := frEnv_wf hst hb1.fr
  have r2 : ∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X24, .X26, .X29], s2.data.regs.getXReg r =
      s1.data.regs.getXReg r := regs_of hm' hm2 (by decide)
  have hb2 : Base m0 s2.data := hb1.of_regs hfr2 fun r hr ↦ r2 r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl <;> simp)
  have hs2' := Match.sameOutside_in hm2 hwf (r0 := 0) (o := 24) (n := 8) rfl (by omega)
    (by decide)
  have hd : s1.data.dmem = st.data.dmem := hd1
  have hsC : SameOutside st.data.dmem s2.data.dmem (Chg m0 []) := by
    rw [← hd]; exact NativeRustcVm.SameOutside.mono hs2' fun q hq ↦ frame_chg hst (by omega) hq
  have fwf : ∀ {f : Nat} {v : UInt64}, f + 8 ≤ 192 → (f + 8 ≤ 24 ∨ 32 ≤ f) →
      FW m0 st.data.dmem f v → FW m0 s2.data.dmem f v := fun hf hd' h ↦ by
    rw [← hd] at h; exact FW.frame hst hs2' (by omega) hf hd' h
  have hl := hM.rlen
  have hn := hM.ps256
  refine ⟨by simp only [PcOk] at hpc2; exact hpc2, hb2,
    hM.keep G hsC (by simp) (fwf (by omega) (.inr (by omega)) hM.f56)
      (fwf (by omega) (.inr (by omega)) hM.f48) (fwf (by omega) (.inr (by omega)) hM.f40)
      (fwf (by omega) (.inr (by omega)) hM.f32), rfl, by simp, by omega, by simp [hl]; omega,
    fun j hj ↦ absurd hj (by simp), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact nodes_keep hnd hsC fun j hj ↦ by
      rw [length_nodes0 hl] at hj
      exact G.not_chg (L := []) (o := 4096) (n := 40 * (sortD qs).length)
        (by rw [workBytes_eq]; omega) (by simp) j hj
  · exact reader_fr G hs2' (by omega) (show ReaderAt s1.data.dmem _ _ _ _ by rw [hd]; exact hrd)
  · have := hm2.bytesAt_write (r := 0) (o := 24) (n := 8) (b := base m0 192) (sz := 192) rfl
      (by omega) (v := .reg .X29) (by decide)
    have hw := wordAt_reg this
    simp only [Sym.eval, Env.ofMachine_regs] at hw
    rwa [x29] at hw
  · rw [r2 .X21 (by simp), r1 .X21 (by simp)]; exact x21
  · rw [r2 .X24 (by simp)]; exact x24
  · rw [r2 .X26 (by simp), r1 .X26 (by simp)]; exact x26
  · show (s2.data.regs.getXReg .X25).toBitVec.toNat = _
    rw [hm2.regs .X25 _ rfl]; rfl
  · rw [hm2.regs .X23 _ rfl]; simp only [Sym.eval, Env.ofMachine_regs]; rw [hb1.x19, add_lit]
  · rw [hm2.regs .X27 _ rfl]; simp only [Sym.eval, Env.ofMachine_regs]; rw [hb1.x19, add_lit]
  · show (s2.data.regs.getXReg .X28).toBitVec.toNat = _
    rw [hm2.regs .X28 _ rfl]
    show (s1.data.regs.getXReg .X26).toBitVec.toNat = _
    rw [r1 .X26 (by simp), length_nodes0 hl]; exact x26
  · rw [r2 .X29 (by simp), x29]

end

end NativeRustcVmArm.Wire.PhaseM
