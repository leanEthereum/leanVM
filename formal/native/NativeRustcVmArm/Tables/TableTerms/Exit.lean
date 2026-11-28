module

public import NativeRustcVmArm.Tables.TableTerms.Blocks

/-!
# `table_terms`: the exits

`b16` (`.LTableTerms_7`) restores the registers and returns (`exit16`). `b15` (`.LTableTerms_6`)
writes `None` at `out` (`exit_none`: the model's run fails). `b14` writes `Some` of the running
sum at `out` (`exit_some`: after the sixth table).
-/

namespace NativeRustcVmArm.Tables.TableTerms

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Ring NativeRustcVm.Transcript
open NativeVm.Model NativeRustcVm.Tables NativeRustcVm.Layout NativeRustcVmArm.Vm.TableTerms
open NativeRustcVm (wordOf ewsOf)
open NativeRustcVmArm.Bus (after)

public section

variable [Host] {k : Nat} {a : DecArea} {s : TState} {heights : Array Nat}
  {forms : Array (Array FormW)} {m0 : MachineData}

/-- **The epilogue** (`b16`): the registers restored, `ret`; the memory the block's. -/
theorem exit16 (hp : Placed code k) (h : TableTermsPre a s heights forms m0) {m : MachineData}
    (hfr : Fr m0 288 N slots [] (outs m0) m)
    (hpost : ∀ m' : MachineData, m'.dmem = m.dmem →
      OptEWAt m'.dmem m0.regs.X0.toBitVec ((R heights forms m0 s).map (·.1.1)) ∧
      (∀ x s', R heights forms m0 s = some (x, s') → TableEvalsAt m'.dmem (ev m0) x.2) ∧
      NextAt m'.dmem m0.regs.X1.toBitVec a (R heights forms m0 s)) :
    Eventually (step1 Host.exe) (Goal a s heights forms m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.TableTerms.b16Offset)⟩ := by
  have hS := Pre.stack h
  have hwf := wf0 hS hfr.kept
  refine exec_then (hb16 hp) run_b16 hwf (match0 hS hfr.sp) fun st hm hpc ↦ ?_
  have hm' : Match (E0 m0 m) (after b16 sF) st.data := by rw [Bus.after_eq run_b16]; exact hm
  obtain ⟨hok, hmem⟩ := ok_b16
  obtain ⟨hret, hsv⟩ := hfr.exit hm' hwf hok
  have hd : st.data.dmem = m.dmem := hm'.dmem_eq hwf hmem
  obtain ⟨p1, p2, p3⟩ := hpost st.data hd
  refine .done _ ⟨by simp only [PcOk] at hpc; rw [hpc, hret], p1, p2, p3, ?_, hsv⟩
  rw [hd]
  exact NativeRustcVm.SameOutside.mono hfr.same fun q hq ↦ hq.elim (fun h ↦ .inr (.inr (.inr h)))
    fun h ↦ h.elim .inl fun h ↦ h.elim (.inr ∘ .inl) (.inr ∘ .inr ∘ .inl)

/-- `out` as region 1 of a block's environment. -/
theorem out_env (h : TableTermsPre a s heights forms m0) {m : MachineData}
    (hfr : Fr m0 288 N slots [] (outs m0) m) (hw : FW m0 m (cws m0)) :
    (E1 m0 m m0.regs.X0.toBitVec 24).WF ∧
      Match (E1 m0 m m0.regs.X0.toBitVec 24) outS m := by
  have hS := Pre.stack h
  have ho := Pre.out h
  refine ⟨wf1 hS hfr.kept ⟨ho.1, ho.2.1⟩ ho.2.2.2.2.1, match1 hS hfr.sp ?_⟩
  rw [ld0, hw (16, rg m0 .X0) (by simp [cws])]
  exact (BitVec.add_zero _).symm

/-- **A failed run** (`b15`): `None` at `out`. -/
theorem exit_none (hp : Placed code k) (h : TableTermsPre a s heights forms m0) {m : MachineData}
    (hfr : Fr m0 288 N slots [] (outs m0) m) (hw : FW m0 m (cws m0))
    (hr : R heights forms m0 s = none) :
    Eventually (step1 Host.exe) (Goal a s heights forms m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.TableTerms.b15Offset)⟩ := by
  have hS := Pre.stack h
  obtain ⟨hwf, hm⟩ := out_env h hfr hw
  refine exec_then (hb15 hp) run_b15 hwf hm fun st hm1 hpc ↦ ?_
  have hm1' : Match (E1 m0 m m0.regs.X0.toBitVec 24) (after b15 outS) st.data := by
    rw [Bus.after_eq run_b15]; exact hm1
  obtain ⟨hsp, hW, -, h0⟩ := ok_b15
  have hfr1 := fr_block hfr (spN h) hm hm1' hwf hsp rfl (hout_one fun _ hi ↦ out_outs hi) hW
  have hw0 : NativeRustcVm.WordAt st.data.dmem m0.regs.X0.toBitVec 0 := by
    have := wordAt_of_load hm1' hwf (r := 1) (o := 0) rfl (by omega) h0
    rw [NativeRustcVm.addr_add_zero] at this
    exact this
  simp only [PcOk] at hpc
  refine Bus.Gkr.at_pc (hpc.trans (addr_eq (by rw [Nat.add_assoc, NativeRustcVmArm.Vm.TableTerms.b15_next])))
    (exit16 hp h hfr1 fun m' hd ↦ ⟨?_, fun x s' h' ↦ (by rw [hr] at h'; cases h'),
      fun x s' h' ↦ (by rw [hr] at h'; cases h')⟩)
  rw [hr, hd]
  exact hw0

/-- **After the sixth table** (`b14`): `Some` of the running sum at `out`. -/
theorem exit_some (hp : Placed code k) (h : TableTermsPre a s heights forms m0)
    (hh : heights.size = 6) (hf : forms.size = 6) {acc : Acc} {si : TState} {m : MachineData}
    (H : Head a s heights forms m0 6 acc si m) :
    Eventually (step1 Host.exe) (Goal a s heights forms m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.TableTerms.b14Offset)⟩ := by
  have hcw : FW m0 m (cws m0) := fun p hp ↦ H.fw p (List.mem_append_left _ hp)
  obtain ⟨hwf, hm⟩ := out_env h H.fr hcw
  refine exec_then (hb14 hp) run_b14 hwf hm fun st hm1 hpc ↦ ?_
  have hm1' : Match (E1 m0 m m0.regs.X0.toBitVec 24) (after b14 outS) st.data := by
    rw [Bus.after_eq run_b14]; exact hm1
  obtain ⟨hsp, hW, -, hin, l0, l8, l16⟩ := ok_b14
  have hfr1 := fr_block H.fr (spN h) hm hm1' hwf hsp rfl (hout_one fun _ hi ↦ out_outs hi) hW
  have ho := Pre.out h
  have hwr : ∀ q, Written (E1 m0 m m0.regs.X0.toBitVec 24) (after b14 outS) q →
      InRange m0.regs.X0.toBitVec 24 q :=
    fun q hq ↦ Bus.Written.inRange (r := 1) rfl ho.2.1 hin hq
  have hrun : R heights forms m0 s = some ((acc.2.1, acc.2.2), si) := by
    rw [R, run_full hh hf, H.run]; rfl
  simp only [PcOk] at hpc
  refine Bus.Gkr.at_pc (hpc.trans (lbl_7 hp)) (exit16 hp h hfr1 fun m' hd ↦ ?_)
  rw [hrun, hd]
  refine ⟨⟨?_, ?_⟩, fun x s' h' ↦ ?_, fun x s' h' ↦ ?_⟩
  · have := wordAt_of_load hm1' hwf (r := 1) (o := 0) rfl (by omega) l0
    rw [NativeRustcVm.addr_add_zero] at this
    exact this
  · rw [NativeRustcVm.ewAt_iff]
    have e8 := wordAt_of_load hm1' hwf (r := 1) (o := 8) rfl (by omega) l8
    have e16 := wordAt_of_load hm1' hwf (r := 1) (o := 16) rfl (by omega) l16
    rw [show m0.regs.X0.toBitVec + BitVec.ofNat 64 16 =
      m0.regs.X0.toBitVec + BitVec.ofNat 64 8 + 8#64 from (NativeRustcVm.addr_add_add _ 8 8).symm]
      at e16
    refine ⟨?_, ?_⟩
    · have hx : UInt64.ofBitVec ((Sym.reg .X22).eval (E1 m0 m m0.regs.X0.toBitVec 24)) =
          acc.2.1.c0 := H.x22
      rw [hx] at e8; exact e8
    · have hx : UInt64.ofBitVec ((Sym.reg .X23).eval (E1 m0 m m0.regs.X0.toBitVec 24)) =
          acc.2.1.c1 := H.x23
      rw [hx] at e16; exact e16
  · cases h'
    refine ⟨by rw [H.osz]; rfl, fun j hj ↦ ?_⟩
    refine TableEvalAt.of_same (H.evs j hj) (Same.of_sameOutside (hm1'.sameOutside hwf)
      fun i hi hq ↦ ?_)
    have hj6 : j < 6 := by rw [H.osz] at hj; exact hj
    exact NativeRustcVm.Apart.not_inRange (Pre.out_ev h) ho.2.1 (ev_noWrap h) (hwr _ hq)
      (evi_in h hj6 (NativeRustcVm.inRange_add hi (by norm_num)))
  · cases h'
    exact H.ts.frame (hm1'.kept hwf) (fun q hq ↦ out_not_ts (Pre.ts h) ho q (hwr q hq))
      (hm1'.sameOutside hwf)

end

end NativeRustcVmArm.Tables.TableTerms
