module

public import NativeRustcVmArm.Code.Vm.RingClaimWeight.Names
public import NativeRustcVmArm.Whir.BasisWEval.Calls

/-!
# `BasisW::eval`: the ring-switched claim

From `.LBasisWEval_3` (`At4`): `b4` calls `ring_claim_weight` on the placement of `QKECCAK`, the
Keccak output's point (at most 36 coordinates) and the ring switch's coefficients, its
`Option<EW>` at `sp + 24` (`ring_call`); always `Some`, so `b5` falls into `b6`, which saves the
output's address at `sp + 8` and multiplies the weight by the first scale (`mul_call`).
-/

namespace NativeRustcVmArm.Whir.BasisWEval

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model LeanVM.Parameters
open NativeRustcVmArm.Ring NativeRustcVm.Whir NativeRustcVm.Layout NativeRustcVm.Ring
open NativeRustcVm.KeccakGkr NativeRustcVmArm.Vm.BasisWEval
open LeanVM.Protocol.Verifier (qkeccak Placement)

public section

variable {m0 : MachineData} {ba : BasisAddrs} {b : BasisW} {v : Vals} [Host] {k : Nat}

/-- **The ring-switched claim's weight**, from `.LBasisWEval_3` to `b5`: `Some` of it at
`sp + 24`, the rest as `At4`. -/
theorem ring_call (hp : Placed code k) (h : In m0 ba b v)
    (hrcw : Spec (Labels.label NativeRustcVmArm.Vm.RingClaimWeight.entryLabel) RingClaimWeightPre RingClaimWeightPost)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.BasisWEval.b4Offset)) (ha : At4 m0 ba b v st.data)
    {R : MachineState → Prop}
    (cont : ∀ st' : MachineState, st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.BasisWEval.b5Offset) →
      NativeRustcVm.Transcript.OptEWAt st'.data.dmem (base m0 144 + BitVec.ofNat 64 24)
        (some (ringW v (xpt m0))) →
      Fr0 m0 st'.data →
      (∀ r, calleeSaved r = true → st'.data.regs.getXReg r = st.data.regs.getXReg r) →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have hS := h.stackOk
  have hN := h.hN
  obtain ⟨hs1, hs2, hs3, hs4, hs5, hs6⟩ := stack_le
  have hf := ha.fr
  let p := m0.regs.X1.toBitVec
  let env := Env.ofMachine st.data [(base m0 144, 144), (p, 56), (ba.keccak, 8)]
  have hkin := h.keccakIn
  have hK := NativeRustcVm.Layout.BufEWAt.of_same h.keccak.1 (same_of hN hf hkin) (by decide)
  have hlen : v.kp.toList.length ≤ 36 := hK.1
  have hfa := frame_apart h h.basis
  have hk8 : WhirIn m0 ba.keccak 8 basisWEvalStack := WhirIn.mono hkin (by decide)
  have hfk := frame_apart h hk8
  have hbk : Apart m0.regs.X1.toBitVec 56 ba.keccak 8 :=
    NativeRustcVm.Apart.mono h.aparts.1 (Nat.le_refl _) (by unfold basisBytes; omega)
      (Nat.le_refl _) (by unfold outBytes; omega)
  obtain ⟨hfmap, hfnw⟩ := frame_of h hf
  have hwf : env.WF := by
    refine Env.wf_of ⟨⟨hfmap, hfnw⟩, mapped_of hf h.basis, mapped_of hf hk8, trivial⟩ ?_
    refine List.pairwise_cons.mpr ⟨fun r hr ↦ ?_, List.pairwise_pair.mpr hbk⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hfa.symm
    · exact hfk.symm
  have wk : NativeRustcVm.WordAt st.data.dmem (p + BitVec.ofNat 64 32)
      (UInt64.ofBitVec ba.keccak) := h.word hf 4 (by decide)
  have wr : NativeRustcVm.WordAt st.data.dmem (p + BitVec.ofNat 64 24)
      (UInt64.ofBitVec ba.ring) := h.word hf 3 (by decide)
  have hm : Match env ringS st.data := by
    refine match_ofMachine ⟨rfl, fun _ ↦ Ring.frame_aligned hS hs6 rfl, rfl,
        fun h ↦ absurd h (by decide), rfl, fun h ↦ absurd h (by decide), trivial⟩
      (by rw [hf.sp]; simp [Sym.eval]) ⟨?_, trivial⟩ trivial trivial ⟨?_, trivial⟩
    · show st.data.regs.X22.toBitVec = _
      rw [ha.x22]; simp [Sym.eval]; rfl
    · simp only [Sym.eval]
      rw [Ring.load_word (env := env) (r := 1) (off := 32) wk]
      simp
  refine exec_at (inf hp b4_in_code (by simp [b4])) run_b4 hwf hpc hm fun st4 hm4 hpc4 ↦ ?_
  simp only [PcOk] at hpc4
  have hf4 : Fr0 m0 st4.data :=
    Fr.ofBlock hf hm hm4 hwf rfl rfl rfl (fun _ h ↦ absurd h (by simp))
  -- the loads
  have l2 : env.load 2 0 8 = v.kp.toList.length.toUInt64.toBitVec :=
    Ring.load_word (by show NativeRustcVm.WordAt st.data.dmem (ba.keccak + BitVec.ofNat 64 0) _
                       rw [NativeRustcVm.addr_add_zero]; exact hK.2.1)
  have l32 : env.load 1 32 8 = ba.keccak := Ring.load_word (env := env) (r := 1) (off := 32) wk
  have l24 : env.load 1 24 8 = ba.ring := Ring.load_word (env := env) (r := 1) (off := 24) wr
  have l16 : env.load 0 16 8 = m0.regs.X3.toBitVec :=
    Ring.load_word (env := env) (r := 0) (off := 16) (hf.slots (16, .X3) (by simp [slots0]))
  have hx0 : st4.data.regs.X0.toBitVec = base m0 144 + BitVec.ofNat 64 24 := by
    refine (hm4.regs .X0 _ rfl).trans ?_
    simp [Sym.eval]; rfl
  have hx1 : st4.data.regs.X1 = (v.L.placement qkeccak).variableCount.toUInt64 :=
    (reg_of hm4 (r := .X1) (v := .reg .X2) rfl rfl).trans ha.x2
  have hx2 : st4.data.regs.X2 = (v.L.placement qkeccak).index.toUInt64 :=
    (reg_of hm4 (r := .X2) (v := .reg .X6) rfl rfl).trans ha.x6
  have hx3 : st4.data.regs.X3 = UInt64.ofBitVec (ba.keccak + BitVec.ofNat 64 8) := reg_eq <| by
    refine (hm4.regs .X3 _ rfl).trans ?_
    sym_simp
    rw [l2, l32, count_ult hlen (by decide)]
    simp only [↓reduceIte]
  have hx4 : st4.data.regs.X4 = v.kp.toList.length.toUInt64 := reg_eq <| by
    refine (hm4.regs .X4 _ rfl).trans ?_
    sym_simp
    rw [l2, count_ult hlen (by decide)]
    simp only [↓reduceIte]
    rfl
  have hx5 : st4.data.regs.X5 = UInt64.ofBitVec (ba.ring + BitVec.ofNat 64 16) := reg_eq <| by
    refine (hm4.regs .X5 _ rfl).trans ?_
    sym_simp
    rw [l24]
  have hx6 : st4.data.regs.X6 = m0.regs.X2 :=
    (reg_of hm4 (r := .X6) (v := .reg .X21) rfl rfl).trans ha.x21
  have hx7 : st4.data.regs.X7 = m0.regs.X3 := reg_eq <| by
    refine (hm4.regs .X7 _ rfl).trans ?_
    simp only [Sym.eval]
    rw [l16]
  have hlen' : v.kp.toList.length.toUInt64.toNat = v.kp.toList.length :=
    natCast_toUInt64_toNat (by omega)
  have hpre : RingClaimWeightPre st4.data := by
    refine ⟨hf4.stackOk hS (by decide) hs2, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hx4, hlen']; exact hlen
    · rw [hx7]; exact h.pre.2.2.2.1
    · unfold SliceOk
      rw [hx3, hx4, hlen']
      exact h.argOk hf4 (WhirIn.sub hkin (by unfold outBytes; omega)) hs2
    · rw [hx5]
      exact h.argOk hf4 (WhirIn.sub h.ringIn (by unfold ringWBytes; omega)) hs2
    · rw [hx6, hx7]; exact h.argOk hf4 h.point hs2
    · show Readable _ _ _ ∧ OffStack _ _ _ _
      rw [hx0]; exact frame_out h hf4 hs2
  have hk4 : ∀ r, calleeSaved r = true → st4.data.regs.getXReg r = st.data.regs.getXReg r := by
    intro r hr
    cases r <;> simp [calleeSaved] at hr <;> first
      | exact reg_of hm4 rfl rfl
      | exact reg_of hm4 (r := .X22) (v := .ptr 1 0) rfl (by
          show _ = st.data.regs.X22.toBitVec
          rw [ha.x22]; simp [Sym.eval]; rfl)
  refine Fr.leafIn hf4 hN hs2 (lo := 24) (n := 24) (by decide) (fun _ h ↦ absurd h (by simp))
    (by decide) (fun _ h ↦ h.elim) hrcw hpc4 hpre (fun m' hq ↦ ⟨?_, hq.2.2⟩)
    fun m5 hf5 hq5 hcs5 ↦ ?_
  · refine NativeRustcVm.SameOutside.mono hq.2.1 fun q hq ↦ ?_
    rcases hq with hq | hq
    · rw [hx0] at hq; exact .inr (.inl hq)
    · exact .inl hq
  · refine cont _ (by rw [show k + NativeRustcVmArm.Vm.BasisWEval.b4Offset + b4.length = k + NativeRustcVmArm.Vm.BasisWEval.b5Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.BasisWEval.b4_next]]) ?_ hf5
      fun r hr ↦ (hcs5 r hr).trans (hk4 r hr)
    have e1 : placementArg st4.data = v.L.placement qkeccak :=
      placementArg_eq (placement_lt h.layout qkeccak) hx1 hx2
    have e2 : slice st4.data st4.data.regs.X3 st4.data.regs.X4 = v.kp := by
      unfold slice
      rw [hx3, hx4, UInt64.toBitVec_ofBitVec, hlen',
        slice_of h hf4 (WhirIn.sub hkin (o := 8) (by unfold outBytes; omega)) le_rfl,
        NativeRustcVm.ewsOf_of_ewsAt h.keccak.1.2.2, Array.toArray_toList]
    have e3 : arr st4.data st4.data.regs.X5 coeffCount = v.coeffs := by
      unfold arr
      have hcl : v.coeffs.toList.length = 64 := by simpa [coeffCount] using h.ring.2.1
      rw [hx5, UInt64.toBitVec_ofBitVec, show coeffCount = v.coeffs.toList.length by
          rw [hcl]; rfl,
        slice_of h hf4 (WhirIn.sub h.ringIn (o := 16) (by
          rw [hcl]; unfold ringWBytes coeffCount; omega)) le_rfl,
        NativeRustcVm.ewsOf_of_ewsAt h.ring.2.2, Array.toArray_toList]
    have h1 := hq5.1
    rw [hx0, e1, e2, e3, h.xpt_eq hf4 hx6 hx7] at h1
    exact h1

end

end NativeRustcVmArm.Whir.BasisWEval
