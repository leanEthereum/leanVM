module

public import NativeRustcVmX64.Whir.SubspaceTable.Inner

/-!
# `subspace_table`'s turns' head (x86-64)

`head`: the turns' head (`OInv t`, `b14`) spills the turn and the table's length, and enters the
layer loop (`IInv t 0`). The end of a turn is `Push.push`, the loops `SubspaceTable.turns`.
-/

namespace NativeRustcVmX64.Whir.SubspaceTable

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.SubspaceTable NativeVm.Model
open NativeRustcVm.Whir NativeRustcVmX64.Whir.Leaf
open NativeRustcVm (Region WordAt WordsAt wordOf)
open NativeRustcVmX64.Field (midS frameS frameEnv frame_wf match_frame)
open NativeRustcVmX64.Arrays (stackOk_mono load8_eq load_word wordAt_of_write eval_reg eval_lit
  eval_load eval_add eval_cmp_eq eval_not eval_xor eval_min eval_shl_lit apart_symm
  not_inRange_of_apart written_region0)

public section

theorem wordAt_ofNat {d : DataMem} {a : BitVec 64} {n : Nat}
    (h : WordAt d a (UInt64.ofBitVec (BitVec.ofNat 64 n))) : WordAt d a (.ofNat n) := h

variable [Host] {k : Nat}


theorem hb14 (hp : Placed code k) : b14.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.SubspaceTable.b14Offset) :=
  b14_in_code.trans hp.1 (by simp [b14])
theorem hb18 (hp : Placed code k) : b18a.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.SubspaceTable.b18Offset) ∧
    b18b.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.SubspaceTable.b18Offset + b18a.length) := by
  have h := b18_in_code.trans hp.1 (by simp [b18])
  rw [← List.take_append_drop 2 b18] at h
  exact h.append
theorem hb19 (hp : Placed code k) : b19.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.SubspaceTable.b19Offset) :=
  b19_in_code.trans hp.1 (by simp [b19])
theorem hb20 (hp : Placed code k) : b20.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.SubspaceTable.b20Offset) :=
  b20_in_code.trans hp.1 (by simp [b20])

/-- **The turns' head** (`b14`). -/
theorem head (hp : Placed code k) {m0 : MachineData} (hpre : SubspaceTablePre m0) {t : Nat}
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceTable.b14Offset)) (hI : OInv m0 t st.data) :
    Eventually (step1 Host.exe) (fun s ↦ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceTable.b15Offset) ∧ IInv m0 t 0 s.data) st := by
  obtain ⟨hS, hout, _⟩ := hpre
  obtain ⟨hF, -, -, -⟩ := stack_le
  obtain ⟨hfmap, hfnw, hfe⟩ := frame_ok hS hF
  have hsl := slots_ok
  have hfr := hI.tn.fr
  have hmu := hI.tn.hmu
  have ht := hI.ht
  have hlw : ∀ w : UInt64, (NativeRustcVm.wordBytes w).length = 8 := NativeRustcVm.length_wordBytes
  have hll := layer_len m0 t
  have hlb : ((layerAt (muOf m0) t).flatMap NativeRustcVm.wordBytes).length = 8 * muOf m0 := by
    rw [NativeRustcVm.length_wordsBytes, hll]
  have hpl := pairWords_len (tableAt (muOf m0) t)
  rw [tableAt_len' (by omega)] at hpl
  have hwf := hfr.wf (vars := fun _ ↦ 0) (ret := 0) hS hF
  refine exec_at (hb14 hp) run_b14 hwf (by intro l h; cases h) hpc hfr.mid_match
    fun st1 hm1 hpc1 ↦ .done _ ⟨hpc1, ?_⟩
  obtain ⟨⟨hk1, hw1⟩, hw1', hv40, hv32⟩ := after_eq run_b14 ▸ b14_write
  have hfr1 : Fr m0 st1.data := hfr.of_write hfr.mid_match hm1 hwf rfl hk1 (r := 0) rfl
    (len := 48) (by omega) hw1 (fun p h ↦ .inr (inRange_frame hS hF (by omega) h))
    (fun q hq i hi ↦ by
      rw [addr_add]
      exact Arrays.not_inRange_above (by have := hsl q hq; omega)
        (by rw [hfe]; have := hsl q hq; omega))
  have kk : ∀ {o : Nat} {bs : List UInt8}, (o + bs.length ≤ 32 ∨ 48 ≤ o) → o + bs.length ≤ 856 →
      NativeRustcVm.BytesAt st.data.dmem (fbOf m0 + BitVec.ofNat 64 o) bs →
      NativeRustcVm.BytesAt st1.data.dmem (fbOf m0 + BitVec.ofNat 64 o) bs :=
    fun hap hl h ↦ bytesAt_block hm1 hwf rfl hl
      (fun w hw ↦ ⟨(hw1 w hw).1, by have := (hw1' w hw); have := (hw1 w hw).2; omega⟩) h
  have hl24 : (frameEnv m0 st.data 848 (fun _ ↦ 0) 0).load 0 24 8 = BitVec.ofNat 64 (8 * muOf m0) :=
    load_word (show WordAt st.data.dmem (stackBelow m0 848 + BitVec.ofNat 64 24) _ from hI.tn.mu8)
  have hmin : (Sym.ite (.cmp .ult .W64 (.reg .r14) (.reg .r13)) (.reg .r14) (.reg .r13)).eval
      (frameEnv m0 st.data 848 (fun _ ↦ 0) 0) = BitVec.ofNat 64 t := by
    rw [eval_min, Env.ofMachine_regs, Env.ofMachine_regs]
    show BitVec.ofNat 64 (min (reg st.data .r13).toNat (reg st.data .r14).toNat) = _
    rw [hI.r13, hI.r14, toNat_ofNat_lt (by omega)]
    congr 1
    unfold muOf at ht
    omega
  refine ⟨⟨hfr1, kk (.inl (by rw [hlw]; omega)) (by rw [hlw]; omega) hI.tn.out,
    kk (.inl (by rw [hlw]; omega)) (by rw [hlw]; omega) hI.tn.mu,
    kk (.inl (by rw [hlw])) (by rw [hlw]; omega) hI.tn.mu8, hmu⟩, by omega, ?_, ?_, ?_,
    kk (.inr (by omega)) (by rw [hpl]; omega) hI.table, ?_, ?_, ?_, ?_⟩
  · have := wordAt_of_write hm1 (r := 0) (o := 40) rfl (by decide) (v := .reg .r13) hv40
    rw [eval_reg, Env.ofMachine_regs, show st.data.regs.get64 .r13 = _ from hI.r13] at this
    exact wordAt_ofNat this
  · have := wordAt_of_write hm1 (r := 0) (o := 32) rfl (by decide) (v := .reg .r12) hv32
    rw [eval_reg, Env.ofMachine_regs, show st.data.regs.get64 .r12 = _ from hI.r12] at this
    exact wordAt_ofNat this
  · rw [Nat.add_zero, innerL_start (by rw [hll]; omega)]
    exact kk (.inr (by omega)) (by rw [hlb]; omega) hI.layer
  · exact (Match.reg_eq (r := .rbx) hfr.mid_match hm1 rfl rfl).trans hI.rbx
  · refine (hm1.regs .rbp _ rfl).trans ?_
    show BinOp.apply .sub .W64 (Env.load _ 0 24 8)
      ((Sym.bin .shl .W64 _ (.lit 3)).eval _) = _
    rw [sub64, hl24, eval_shl_lit _ (by decide), hmin]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    omega
  · exact (hm1.regs .r14 _ rfl).trans rfl
  · exact (Match.reg_eq (r := .r15) hfr.mid_match hm1 rfl rfl).trans hI.r15

end

end NativeRustcVmX64.Whir.SubspaceTable
