module

public import NativeRustcVmX64.Whir.FoldRound.Basic

/-!
# `fold_round` on x86-64: the exits and the reads' checks

`exit21`: from a body state, RBX the output, RAX the tag `v`, `b21` writes the tag and returns;
the postcondition from what the round left (`Res`). `none20`: the `None` exit (`b20` clears RAX,
`b21`). `readCheck`: `read_scalar` into the frame's words `8` to `32`, then the tag's test: on
`None` the `None` exit, on `Some x` a body state with `x` at the frame's words `16`, `24`.
-/

namespace NativeRustcVmX64.Whir.FoldRound

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Whir
open NativeRustcVmX64.Vm.FoldRound
open NativeRustcVmX64.Transcript (Frame frameEnv MidOk)
open NativeRustcVmX64.Whir.SampleQueries (wr0 miss wrote kept wrote_spec kept_spec wr0_spec
  miss_spec midOk_writesIn)
open NativeRustcVm (WordAt EWAt EWsAt)

public section

/-- No writes. -/
theorem no_written [Labels] {env : Env} {S : SState} (h : S.mem = []) {q : BitVec 64} :
    ¬ Written env S q := fun ⟨_, hw, _⟩ ↦ by rw [h] at hw; cases hw

variable [Host] {k : Nat} {a : DecArea} {s0 : TState} {w : WhirStateW} {m0 : MachineData}

/-- **`b21`**: the tag `v` in RAX written to the output, the return. -/
theorem exit21 (hp : Placed code k) (h : FoldRoundPre a s0 w m0) {d : MachineData}
    (hw : Fr m0 d) (hbx : reg d .rbx = oA m0) {v : UInt64} (hax : reg d .rax = v.toBitVec)
    {Q : Mem 64 → Prop}
    (hQ : ∀ d' : Mem 64, Kept d.dmem d' → SameOutside d.dmem d' (InRange (oA m0) 8) → Q d')
    (hfin : ∀ d' : Mem 64, WordAt d' (oA m0) v → Q d' → Res a s0 w m0 d') :
    Eventually (step1 Host.exe) (Goal a s0 w m0) ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.FoldRound.b21Offset)⟩ := by
  have c := ctx h
  have ho := pre_o h
  have hon : (oA m0).toNat + 40 ≤ 2 ^ 64 := ho.2.1
  have hap : NativeRustcVm.Apart (fb m0) (176 + 8) (oA m0) 8 :=
    Transcript.Apart.sub (Transcript.Apart.symm' (Transcript.apart_frame ho.2.2.2.2.1 c.hN F_le))
      le_rfl (by omega)
  have hwf : (frameEnv m0 d 176 [(oA m0, 8)] (fun _ ↦ 0) 0).WF := by
    refine Transcript.frame_wf ⟨Mapped.keeps (Transcript.frame_mapped c.stack F_le) hw.fr.kept,
      c.fnw⟩ (fun x hx ↦ ?_) (List.pairwise_pair.mpr hap)
    rw [List.mem_singleton] at hx
    subst hx
    exact ⟨Mapped.keeps (fun i hi ↦ ho.1 i (by omega)) hw.fr.kept,
      show (oA m0).toNat + 8 ≤ 2 ^ 64 by omega⟩
  have hm : Match (frameEnv m0 d 176 [(oA m0, 8)] (fun _ ↦ 0) 0) tagS d :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hw.fr.rsp_eval, Transcript.known_ptr rfl hbx, trivial⟩
      trivial trivial trivial
  refine exec_then (inf hp b21_in_code (by simp [b21])) run_b21 hwf (by intro l h; cases h) hm
    fun st1 hm1 hpc1 ↦ .done _ ?_
  obtain ⟨he, hwr, hwt⟩ := after_eq run_b21 ▸ ok_b21
  obtain ⟨hsv, hrsp⟩ := Frame.epilogue hw.fr hwf hm1 he
  have hs1 : SameOutside d.dmem st1.data.dmem (InRange (oA m0) 8) :=
    Transcript.sameOutside_low hwf hm1 (r := 1) rfl le_rfl (wrR_spec hwr)
  have hword : WordAt st1.data.dmem (oA m0) v := by
    have := Transcript.wordAt_write hm1 (r := 1) (o := 0) rfl (by omega) (wrote_spec hwt)
    rwa [off_zero, show (Sym.reg .rax).eval (frameEnv m0 d 176 [(oA m0, 8)] (fun _ ↦ 0) 0) =
      v.toBitVec from hax, UInt64.ofBitVec_toBitVec] at this
  refine ⟨?_, hrsp, hfin _ hword (hQ _ (hm1.kept hwf) hs1), changes hw.same hs1, hsv⟩
  simp only [PcOk] at hpc1
  rw [hpc1]
  exact hw.fr.load_ret c.stack F_le

/-- **The `None` exit**: `b20`, `b21`. -/
theorem none20 (hp : Placed code k) (h : FoldRoundPre a s0 w m0) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FoldRound.b20Offset)) (hw : Fr m0 st.data) (hbx : reg st.data .rbx = oA m0)
    (hnone : (foldRound w).run s0 = none) :
    Eventually (step1 Host.exe) (Goal a s0 w m0) st := by
  have c := ctx h
  have hwf := c.wf0 (vars := fun _ ↦ 0) (ret := 0) hw.fr.kept
  refine exec_at (inf hp b20_in_code (by simp [b20])) run_b20 hwf (by intro l h; cases h) hpc
    hw.mid fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hmid, hmem, hax, hk⟩ := after_eq run_b20 ▸ ok_b20
  have hw1 := WFr.block c hw hwf hm1 hmid slots_le fun q hq ↦ absurd hq (no_written hmem)
  simp only [PcOk] at hpc1
  obtain ⟨d1, pc1⟩ := st1
  simp only at hpc1 hw1 hm1
  subst hpc1
  refine exit21 hp h hw1 ((hm1.regs .rbx _ (kept_spec hk (by simp [cs]))).trans hbx)
    (v := 0) (hm1.regs .rax _ hax) (Q := fun _ ↦ True) (fun _ _ _ ↦ trivial) fun d' hw' _ ↦ ?_
  simp only [Res, hnone]
  exact hw'

end

end NativeRustcVmX64.Whir.FoldRound
