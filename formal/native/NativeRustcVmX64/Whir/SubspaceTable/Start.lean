module

public import NativeRustcVmX64.Whir.SubspaceTable.Outer
public import NativeRustcVmX64.Code.Vm.Kinv.Names

/-!
# `subspace_table`: the table's first pair (x86-64)

`first`: from the layer (`Init μ`, `b11`), `b11` zeroes the table's words and calls `kinv(1)`;
`b12` stores the pair `(1, kinv 1)` and, `μ = 0`, goes to the copy (`Done`, `b21`); else `b13`
spills `μ` and `8μ` and enters the turns (`OInv 0`, `b14`).
-/

namespace NativeRustcVmX64.Whir.SubspaceTable

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.SubspaceTable NativeVm.Model
open NativeRustcVm.Whir NativeRustcVmX64.Whir.Leaf
open NativeRustcVm (Region WordAt WordsAt wordOf)
open NativeRustcVmX64.Field (midS frameS frameEnv frame_wf match_frame)
open NativeRustcVmX64.Arrays (stackOk_mono load8_eq load_word wordAt_of_write eval_reg eval_lit
  eval_load eval_add eval_test apart_symm not_inRange_of_apart written_region0)

public section

/-- `8μ` as `b13` computes it. -/
theorem mu8_eval (x : BitVec 64) :
    x * BitVec.ofNat 64 8 = BitVec.ofNat 64 (8 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]
  omega

theorem pairWords_one (a b : UInt64) : pairWords [(a, b)] = [a, b] := by simp [pairWords]

/-- The first pair's words. -/
theorem pairs_zero {d : DataMem} {a : BitVec 64} {mu : Nat}
    (h0 : WordAt d a 1) (h1 : WordAt d (a + BitVec.ofNat 64 8) (kinv 1)) :
    PairsAt d a (tableAt mu 0) := by
  unfold PairsAt
  rw [tableAt_zero, rootPair, pairWords_one, NativeRustcVm.wordsAt_cons_iff, NativeRustcVm.wordsAt_singleton_iff]
  exact ⟨h0, h1⟩

variable [Host] {k : Nat}

theorem hb11 (hp : Placed code k) : b11.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.SubspaceTable.b11Offset) :=
  b11_in_code.trans hp.1 (by simp [b11])
theorem hb12 (hp : Placed code k) : b12.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.SubspaceTable.b12Offset) :=
  b12_in_code.trans hp.1 (by simp [b12])
theorem hb13 (hp : Placed code k) : b13.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.SubspaceTable.b13Offset) :=
  b13_in_code.trans hp.1 (by simp [b13])

/-- **The table's first pair** (`b11` to `b13`): at the turns' head (`OInv 0`) or, `μ = 0`, at
the copy. -/
theorem first (hp : Placed code k) (hkinv : Spec (Labels.label NativeRustcVmX64.Vm.Kinv.entryLabel) KinvPre KinvPost)
    {m0 : MachineData} (hpre : SubspaceTablePre m0) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceTable.b11Offset)) (hI : Init m0 (muOf m0) st.data) :
    Eventually (step1 Host.exe) (fun s ↦ (s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceTable.b14Offset) ∧ OInv m0 0 s.data) ∨
      (s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceTable.b21Offset) ∧ Done m0 s.data)) st := by
  have hpre' := hpre
  obtain ⟨hS, hout, _⟩ := hpre'
  obtain ⟨hF, hlek, -, -⟩ := stack_le
  obtain ⟨hfmap, hfnw, hfe⟩ := frame_ok hS hF
  have hS1 := hS.1
  have hS2 := hS.2.1
  have hsl := slots_ok
  have hfr := hI.fr
  have hmu := hI.hmu
  have hmu64 : muOf m0 < 2 ^ 64 := (reg m0 .rsi).isLt
  have hmuv : reg m0 .rsi = BitVec.ofNat 64 (muOf m0) := reg_ofNat _
  have hlw : ∀ w : UInt64, (NativeRustcVm.wordBytes w).length = 8 := NativeRustcVm.length_wordBytes
  have hil : ((initL (muOf m0)).flatMap NativeRustcVm.wordBytes).length = 248 := by
    rw [NativeRustcVm.length_wordsBytes, initL_length]
  -- `b11`: the table's words zeroed, `kinv(1)`
  have hwf := hfr.wf (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceTable.b12Offset)).toBitVec) hS hF
  refine exec_at (hb11 hp) run_b11 hwf (fun _ _ ↦ rfl) hpc hfr.mid_match fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨⟨hk1, hsp1, hw1⟩, hw1'⟩ := after_eq run_b11 ▸ b11_call
  have hrsp1 := rsp_call hm1 hsp1
  refine Frame.call hkinv hfr hS hlek (L := 552) (by decide)
    (fun p hp' ↦ ⟨by have := (hsl p hp').1; omega, (hsl p hp').2⟩) (out_one hout) hwf
    hfr.mid_match hm1 hpc1 hk1 hsp1 hw1
    (stackOk_callee hS (fun p h ↦ hm1.kept hwf p (hfr.kept p h)) hrsp1 hlek)
    (fun m' ⟨_, hso, hsv⟩ ↦ ⟨hsv, fun p hp ↦ hso p fun h ↦ hp (.inr (.inr h))⟩)
    fun st2 hpc2 hfr2 ⟨hax2, hso2, hsv2⟩ ↦ ?_
  have k2 : ∀ {o : Nat} {bs : List UInt8}, o + bs.length ≤ 856 →
      (∀ n off : Nat, (off + n ≤ 8 ∨ (48 ≤ off ∧ off + n ≤ 56) ∨ 72 ≤ off) → off + n ≤ 552 →
        off + n ≤ o ∨ o + bs.length ≤ off) →
      NativeRustcVm.BytesAt st.data.dmem (fbOf m0 + BitVec.ofNat 64 o) bs →
      NativeRustcVm.BytesAt st2.data.dmem (fbOf m0 + BitVec.ofNat 64 o) bs :=
    fun hl hap h ↦ bytesAt_callee hS hrsp1 hlek hso2 hl (bytesAt_block hm1 hwf rfl hl
      (fun w hw ↦ ⟨(hw1 w hw).1, hap w.n w.off (hw1' w hw) (hw1 w hw).2⟩) h)
  have hout2 : OutAt m0 st2.data := k2 (by rw [hlw]; omega) (fun n off h1 h2 ↦ by
    rw [hlw]; omega) hI.out
  have hlay2 : WordsAt st2.data.dmem (fbOf m0 + BitVec.ofNat 64 552) (initL (muOf m0)) :=
    k2 (by rw [hil]; omega) (fun n off _ h2 ↦ .inl h2) hI.layer
  have hinv : reg st2.data .rax = (kinv 1).toBitVec := by
    rw [hax2, show reg st1.data .rdi = BitVec.ofNat 64 1 from hm1.regs .rdi _ rfl]
    rfl
  have e2 : ∀ R ∈ [Reg64.r14], reg st2.data R = reg st.data R := by
    intro R hR
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    subst hR
    exact (hsv2.1 _ rfl).trans (Match.reg_eq hfr.mid_match hm1 rfl rfl)
  have hr12 : reg st2.data .r12 = BitVec.ofNat 64 1 :=
    (hsv2.1 .r12 rfl).trans (show reg st1.data .r12 = BitVec.ofNat 64 1 from hm1.regs .r12 _ rfl)
  -- `b12`: the pair `(1, kinv 1)`
  have hpc2' : st2.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceTable.b12Offset) := hpc2
  have hwf3 := hfr2.wf (vars := fun _ ↦ 0) (ret := 0) hS hF
  refine exec_at (hb12 hp) run_b12 hwf3 (by intro l h; cases h) hpc2' hfr2.mid_match
    fun st3 hm3 hpc3 ↦ ?_
  obtain ⟨⟨hk3, hw3⟩, hw3', hv56, hv64⟩ := after_eq run_b12 ▸ b12_write
  have hfr3 : Fr m0 st3.data := hfr2.of_write hfr2.mid_match hm3 hwf3 rfl hk3 (r := 0) rfl
    (len := 72) (by omega) hw3 (fun p h ↦ .inr (inRange_frame hS hF (by omega) h))
    (fun q hq i hi ↦ by
      rw [addr_add]
      exact Arrays.not_inRange_above (by have := hsl q hq; omega)
        (by rw [hfe]; have := hsl q hq; omega))
  have k3 : ∀ {o : Nat} {bs : List UInt8}, (o + bs.length ≤ 56 ∨ 72 ≤ o) → o + bs.length ≤ 856 →
      NativeRustcVm.BytesAt st2.data.dmem (fbOf m0 + BitVec.ofNat 64 o) bs →
      NativeRustcVm.BytesAt st3.data.dmem (fbOf m0 + BitVec.ofNat 64 o) bs :=
    fun hap hl h ↦ bytesAt_block hm3 hwf3 rfl hl
      (fun w hw ↦ ⟨(hw3 w hw).1, by have := (hw3' w hw); have := (hw3 w hw).2; omega⟩) h
  have htab3 : PairsAt st3.data.dmem (fbOf m0 + BitVec.ofNat 64 56) (tableAt (muOf m0) 0) := by
    have h56 := wordAt_of_write hm3 (r := 0) (o := 56) rfl (by decide) hv56
    rw [eval_lit] at h56
    refine pairs_zero h56 ?_
    have := wordAt_of_write hm3 (r := 0) (o := 64) rfl (by decide) hv64
    rw [eval_reg, Env.ofMachine_regs, show st2.data.regs.get64 .rax = _ from hinv,
      UInt64.ofBitVec_toBitVec] at this
    rw [addr_add]
    exact this
  have hout3 : OutAt m0 st3.data := k3 (.inl (by rw [hlw]; omega)) (by rw [hlw]; omega) hout2
  have hlay3 : WordsAt st3.data.dmem (fbOf m0 + BitVec.ofNat 64 552) (initL (muOf m0)) :=
    k3 (.inr (by omega)) (by rw [hil]; omega) hlay2
  have hr14_2 : reg st2.data .r14 = BitVec.ofNat 64 (muOf m0) :=
    (e2 .r14 (by simp)).trans (hI.r14.trans hmuv)
  have e3 : ∀ R ∈ [Reg64.r12, .r14], reg st3.data R = reg st2.data R := by
    intro R hR
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl <;> exact Match.reg_eq hfr2.mid_match hm3 rfl rfl
  simp only [PcOk] at hpc3
  rw [eval_test, eval_reg, Env.ofMachine_regs, show st2.data.regs.get64 .r14 = _ from hr14_2,
    ofNat_beq hmu64 (by decide)] at hpc3
  obtain ⟨hT3, hF3⟩ := Arrays.pc_cond hpc3
  by_cases h0 : muOf m0 = 0
  · refine .done _ (.inr ⟨(hT3 (by rw [decide_eq_true_eq]; exact h0)).trans
      (hp.label NativeRustcVmX64.Vm.SubspaceTable.label_18_at), ⟨hfr3, hout3, by omega, ?_, ?_⟩⟩)
    · rw [h0]; rw [h0] at htab3; exact htab3
    · rw [h0]; exact (e3 .r12 (by simp)).trans hr12
  -- `b13`: `μ`, `8μ` spilled, the turns' registers
  have hpc3' : st3.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceTable.b13Offset) := hF3 (by rw [decide_eq_true_eq]; exact h0)
  have hwf4 := hfr3.wf (vars := fun _ ↦ 0) (ret := 0) hS hF
  refine exec_at (hb13 hp) run_b13 hwf4 (by intro l h; cases h) hpc3' hfr3.mid_match
    fun st4 hm4 hpc4 ↦ ?_
  obtain ⟨⟨hk4, hw4⟩, hw4', hv16, hv24⟩ := after_eq run_b13 ▸ b13_write
  have hfr4 : Fr m0 st4.data := hfr3.of_write hfr3.mid_match hm4 hwf4 rfl hk4 (r := 0) rfl
    (len := 32) (by omega) hw4 (fun p h ↦ .inr (inRange_frame hS hF (by omega) h))
    (fun q hq i hi ↦ by
      rw [addr_add]
      exact Arrays.not_inRange_above (by have := hsl q hq; omega)
        (by rw [hfe]; have := hsl q hq; omega))
  have k4 : ∀ {o : Nat} {bs : List UInt8}, (o + bs.length ≤ 16 ∨ 32 ≤ o) → o + bs.length ≤ 856 →
      NativeRustcVm.BytesAt st3.data.dmem (fbOf m0 + BitVec.ofNat 64 o) bs →
      NativeRustcVm.BytesAt st4.data.dmem (fbOf m0 + BitVec.ofNat 64 o) bs :=
    fun hap hl h ↦ bytesAt_block hm4 hwf4 rfl hl
      (fun w hw ↦ ⟨(hw4 w hw).1, by have := (hw4' w hw); have := (hw4 w hw).2; omega⟩) h
  have hr14_3 : reg st3.data .r14 = reg m0 .rsi :=
    (e3 .r14 (by simp)).trans ((e2 .r14 (by simp)).trans hI.r14)
  have hmu4 : WordAt st4.data.dmem (fbOf m0 + BitVec.ofNat 64 16) (.ofBitVec (reg m0 .rsi)) := by
    have := wordAt_of_write hm4 (r := 0) (o := 16) rfl (by decide) hv16
    rwa [eval_reg, Env.ofMachine_regs, show st3.data.regs.get64 .r14 = _ from hr14_3] at this
  have hmu8 : WordAt st4.data.dmem (fbOf m0 + BitVec.ofNat 64 24) (.ofNat (8 * muOf m0)) := by
    have := wordAt_of_write hm4 (r := 0) (o := 24) rfl (by decide) hv24
    simp only [mu8S, Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs] at this
    rw [show st3.data.regs.get64 .r14 = _ from hr14_3, mu8_eval] at this
    exact wordAt_ofNat this
  have hpl := pairWords_len (tableAt (muOf m0) 0)
  rw [tableAt_len' (by omega)] at hpl
  have hlay4 : WordsAt st4.data.dmem (fbOf m0 + BitVec.ofNat 64 552) (layerAt (muOf m0) 0) := by
    rw [layerAt, ← initL_take (by omega)]
    exact NativeRustcVm.WordsAt.take (k4 (.inr (by omega)) (by rw [hil]; omega) hlay3) _
  have hpc4' : st4.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceTable.b14Offset) := hpc4
  refine .done _ (.inl ⟨hpc4', ⟨hfr4, k4 (.inl (by rw [hlw])) (by rw [hlw]; omega) hout3,
    hmu4, hmu8, hmu⟩, by omega, hlay4, k4 (.inr (by omega)) (by rw [hpl]; omega) htab3,
    ?_, ?_, ?_, ?_, ?_⟩)
  · exact (hm4.regs .rbx _ rfl).trans (ptr0_eval 552)
  · exact (hm4.regs .r12 _ rfl).trans rfl
  · exact (hm4.regs .r13 _ rfl).trans rfl
  · exact (Match.reg_eq (r := .r14) hfr3.mid_match hm4 rfl rfl).trans hr14_3
  · exact (hm4.regs .r15 _ rfl).trans rfl

end

end NativeRustcVmX64.Whir.SubspaceTable
