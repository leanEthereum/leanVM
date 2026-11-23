module

public import NativeRustcVmX64.KeccakGkr.VerifyLayer.Back.WeightsMul

/-! # Storing one layer weight and advancing the loop -/

namespace NativeRustcVmX64.KeccakGkr.VerifyLayer

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Vm.VerifyLayer
open NativeRustcVm.Transcript (DecArea off)
open LeanVM.Protocol.Verifier

public section

theorem written_region {env : Env} {S : SState} {r n : Nat} {p : BitVec 64}
    (hwf : env.WF) (hp : env.regions[r]? = some (p, n))
    (h : S.mem.all (fun w ↦ w.r == r && decide (w.off + w.n ≤ n)) = true)
    {q : BitVec 64} (hq : Written env S q) : InRange p n q := by
  obtain ⟨w, hw, p', n', he, h1, h2⟩ := hq
  have hh := List.all_eq_true.mp h w hw
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hh
  rw [hh.1, hp] at he
  cases he
  rw [Sym.inRange_iff (hwf.noWrap r p n hp)]
  omega

variable [Host] {m0 : MachineData} {a : DecArea} {s s6 : TState} {c : KeccakClaimW}
  {ch b : EW} {pt lp t : Array EW} {j k : Nat}

theorem weights_store (hp : Placed code k) (hpre : VerifyLayerPre a s c m0)
    (hpt : pt.size ≤ 30) (hlp : lp.size = 11) (hj : j < 1600)
    {d : MachineData} (h : WMul m0 a c ch b pt lp t s6 j d) {R : MachineState → Prop}
    (more : ∀ d', WHead m0 a c ch b pt lp t s6 (j + 1) d' →
      Eventually (step1 Host.exe) R ⟨d', Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b74Offset)⟩)
    (done : ∀ d', Body m0 (wFront m0) 24 d' → WMem m0 a c ch b pt lp t s6 1600 d'.dmem →
      reg d' .r15 = sA m0 → Eventually (step1 Host.exe) R ⟨d', Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b79Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b73Offset)⟩ := by
  have g := geo_of hpre
  have hwf := wfScratch hpre h.body (p := 51200 + 16 * j) (n := 16) (by omega) (by omega) (ret := 0)
  have hw80 := h.mem.fw (80, .ofBitVec (sA m0)) (by apply List.mem_append_left; fw_mem)
  have halias : a71b.eval (envB m0 d [(sA m0 + BitVec.ofNat 64 (51200 + 16 * j), 16)]
      (fun _ ↦ 0) 0) = sA m0 + BitVec.ofNat 64 (51200 + 16 * j) + BitVec.ofInt 64 (-51200) := by
    simp only [a71b, Sym.eval]
    rw [fload8 hw80, add64]
    change sA m0 + reg d .rbx = _
    rw [h.rbx]
    bv_omega
  have hm : Match (envB m0 d [(sA m0 + BitVec.ofNat 64 (51200 + 16 * j), 16)]
      (fun _ ↦ 0) 0) (fr 24 [16] [] [] [(a71b, 1, -51200)]) d :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨h.body.rsp, trivial⟩ trivial trivial ⟨halias, trivial⟩
  refine Body.blk (o' := 24) g h.body hwf (blk hp b73_in_code (by simp [b73])) e73 nofun hm
    (by decide +kernel) ?_ fun st hm' hpc hb _ ↦ ?_
  · intro w hw hr p n he q h1 h2
    exact scr_wFront hpre (by omega) (by omega)
      (written_region hwf (r := 1) rfl (by decide +kernel) ⟨w, hw, p, n, he, h1, h2⟩)
  have hsame : SameOutside d.dmem st.data.dmem
      (InRange (sA m0 + BitVec.ofNat 64 (51200 + 16 * j)) 16) :=
    NativeRustcVm.SameOutside.mono (hm'.sameOutside hwf)
      (fun _ hq ↦ written_region hwf (r := 1) rfl (by decide +kernel) hq)
  have hf := frSame_blk (o := 24) (n := 1944) hwf hm' (by decide +kernel) (by decide)
    (by decide +kernel)
  have ht := h.mem.ts.frame (hm'.kept hwf)
    (fun _ hq ↦ scr_not_t hpre (by omega) hq) hsame
  have heq : NativeRustcVm.EWsAt st.data.dmem (sA m0 + BitVec.ofNat 64 107520)
      (eqKernel lp).toList := by
    apply NativeRustcVm.BytesAt.of_sameOutside h.mem.eq hsame
    intro i hi hq
    rw [NativeRustcVm.length_ewsBytes, eqK_len hlp] at hi
    have hn := g.hs
    have he : (sA m0 + BitVec.ofNat 64 107520 + BitVec.ofNat 64 i).toNat =
        (sA m0).toNat + 107520 + i := by
      rw [NativeRustcVm.addr_add_add, g.sa (by omega)]
      omega
    rw [Sym.inRange_iff (by rw [g.sa (by omega)]; omega), g.sa (by omega), he] at hq
    omega
  have hvalue : ewArg
      (BinOp.apply .xor .W64 (reg d .rax) ((eqKernel lp).getD j 0).c0.toBitVec)
      (BinOp.apply .xor .W64 (reg d .rdx) ((eqKernel lp).getD j 0).c1.toBitVec) =
      lwF (eqKernel lp) b j := by
    rw [NativeRustcVmX64.Arrays.xor_eval, NativeRustcVmX64.Arrays.xor_eval,
      NativeRustcVmX64.Arrays.ewArg_xor, h.value, ewArg_ew, ew_add_comm']
    rfl
  have hw0 : NativeRustcVm.WordAt st.data.dmem
      (off (sA m0 + BitVec.ofNat 64 (51200 + 16 * j)) 0) (lwF (eqKernel lp) b j).c0 := by
    apply NativeRustcVmX64.Sumcheck.wordAt_written hm' (r := 1)
      (v := .bin .xor .W64 (.reg .rax) (.load 0 48 8)) rfl (by decide)
      (by decide +kernel)
    simp only [Sym.eval]
    rw [fload8 h.w48]
    exact ewArg_c0 hvalue
  have hw8 : NativeRustcVm.WordAt st.data.dmem
      (off (sA m0 + BitVec.ofNat 64 (51200 + 16 * j)) 8) (lwF (eqKernel lp) b j).c1 := by
    apply NativeRustcVmX64.Sumcheck.wordAt_written hm' (r := 1)
      (v := .bin .xor .W64 (.reg .rdx) (.load 0 32 8)) rfl (by decide)
      (by decide +kernel)
    simp only [Sym.eval]
    rw [fload8 h.w32]
    exact ewArg_c1 hvalue
  have hnew : NativeRustcVm.EWAt st.data.dmem
      (sA m0 + BitVec.ofNat 64 (51200 + 16 * j)) (lwF (eqKernel lp) b j) := by
    rw [NativeRustcVm.ewAt_iff]
    exact ⟨by simpa only [NativeRustcVm.Transcript.off_zero] using hw0, hw8⟩
  have hmem : WMem m0 a c ch b pt lp t s6 (j + 1) st.data.dmem := by
    refine ⟨ht, FWs.keepR
      (os := [24, 40, 56, 64, 80, 88, 96, 120, 128, 224, 72, 104, 112, 184, 192, 200])
      rfl hf (by decide +kernel) h.mem.fw,
      (hf.sub (o' := 1704) (n' := 264) (by decide) (by decide)).buf h.mem.mu,
      (hf.sub (o' := 1224) (n' := 480) (by decide) (by decide)).ews h.mem.pt
        (by rw [Array.length_toList]; omega), heq, ?_⟩
    intro i hi
    by_cases hij : i = j
    · subst hij; exact hnew
    · apply NativeRustcVm.BytesAt.of_sameOutside (h.mem.lw i (by omega)) hsame
      intro z hz hq
      change z < 16 at hz
      have hn := g.hs
      have he : (sA m0 + BitVec.ofNat 64 (51200 + 16 * i) + BitVec.ofNat 64 z).toNat =
          (sA m0).toNat + 51200 + 16 * i + z := by
        rw [NativeRustcVm.addr_add_add, g.sa (by omega)]
        omega
      rw [Sym.inRange_iff (by rw [g.sa (by omega)]; omega), g.sa (by omega), he] at hq
      omega
  have h15 : reg st.data .r15 = sA m0 := (hm'.regs .r15 _ rfl).trans (fload8 hw80)
  have h13 : reg st.data .r13 = BitVec.ofNat 64 288230376151711742 := hm'.regs .r13 _ rfl
  have hbp : reg st.data .rbp = BitVec.ofNat 64 (j + 1) := by
    rw [show reg st.data .rbp = _ from hm'.regs .rbp _ rfl]
    change BinOp.apply .add .W64 (reg d .rbp) 1#64 = _
    rw [add64, h.rbp]
    bv_omega
  have hbx : reg st.data .rbx = BitVec.ofNat 64 (16 * (j + 1)) := by
    rw [show reg st.data .rbx = _ from hm'.regs .rbx _ rfl]
    change BinOp.apply .add .W64 16#64 (reg d .rbx) = _
    rw [add64, h.rbx]
    bv_omega
  have hc : (SBool.cmp .eq .W64 (.bin .add .W64 (.lit 16) (.reg .rbx)) (.lit 25600)).eval
      (envB m0 d [(sA m0 + BitVec.ofNat 64 (51200 + 16 * j), 16)] (fun _ ↦ 0) 0) =
      decide (j + 1 = 1600) := by
    simp only [SBool.eval, Sym.eval]
    change CmpOp.apply .eq .W64 (BinOp.apply .add .W64 16#64 (reg d .rbx)) 25600#64 = _
    rw [add64, h.rbx, eq64, Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    bv_omega
  simp only [PcOk] at hpc
  rw [hc] at hpc
  by_cases he : j + 1 = 1600
  · simp only [he, decide_true, ↓reduceIte] at hpc
    rw [lbl hp b79_in_code rfl] at hpc
    exact at_pc hpc (done st.data hb (he ▸ hmem) h15)
  · simp only [decide_eq_false he, Bool.false_eq_true, ↓reduceIte] at hpc
    exact at_pc hpc (more st.data ⟨hb, hmem, by omega, hbp, hbx, h15, h13⟩)

end

end NativeRustcVmX64.KeccakGkr.VerifyLayer
