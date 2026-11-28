module

public import NativeRustcVmX64.KeccakGkr.KeccakOpen.FoldStoreBase
public import NativeRustcVmX64.Code.Vm.KeccakOpen

namespace NativeRustcVmX64.KeccakGkr.KeccakOpen

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Vm.KeccakOpen
open NativeRustcVm.Transcript (off off_zero off_off off_add DecArea)

public section

variable [Host] {k : Nat} {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData}

theorem store_run (hp : Placed code k) (h : PreOk a s c m0)
    {cx : Cx} (ha : cx.a = a) {n : Nat} (hn : n < 4096)
    {b : List Directive} {kb : Nat} (hin : b.IsInfixAt code kb) (hne : b ≠ [])
    {S0 S : SState} {x : Exit} (hex : exec b S0 = some (S, x))
    (hcall : ∀ l, x ≠ .call l)
    {lo0 lo1 ib : Reg64} {nib : Sym} {keep : List Reg64}
    (hok : sOk lo0 lo1 ib nib keep S = true)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + kb))
    (hm : Mid cx m0 8 st.data) (hmatch : Match (storeEnv m0 st.data n) S0 st.data)
    {prod lo : EW} (hp0 : reg st.data .rax = prod.c0.toBitVec)
    (hp1 : reg st.data .rdx = prod.c1.toBitVec)
    (hl0 : reg st.data lo0 = lo.c0.toBitVec) (hl1 : reg st.data lo1 = lo.c1.toBitVec)
    {R : MachineState → Prop}
    (cont : ∀ st' : MachineState,
      PcOk (storeEnv m0 st.data n) x (Host.addrOf (k + kb + b.length)) st' →
      Match (storeEnv m0 st.data n) S st'.data → Mid cx m0 8 st'.data →
      NativeRustcVm.EWAt st'.data.dmem (off (rwA m0) (16 * n)) (prod + lo) →
      NativeRustcVm.SameOutside st.data.dmem st'.data.dmem
        (NativeRustcVm.InRange (off (rwA m0) (16 * n)) 16) →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  simp only [sOk, Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨⟨hmid, hmem⟩, _⟩, _⟩ := hok
  have hwf := store_wf h hm.fr.kept hn
  refine exec_at (infix_of hin hne hp) hex hwf (fun l hl ↦ False.elim (hcall l hl))
    hpc hmatch fun st' hm' hpc' ↦ ?_
  have hf := Frame.of_block hm.fr hwf hm' hmid slots_le'
  have hs : NativeRustcVm.SameOutside st.data.dmem st'.data.dmem
      (NativeRustcVm.InRange (off (rwA m0) (16 * n)) 16) :=
    sameOutside_low hwf hm' (r := 1) (N := 16) (hi := 16) rfl (by decide) (by
      intro w hw
      rw [hmem] at hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> exact ⟨rfl, by dsimp only; decide⟩)
  have hm2 := Mid.keep h hm hf (hm'.kept hwf) hs (fun _ hq ↦ store_safe h hn hq) ha
  have hword0 := wordAt_write hm' (r := 1) (o := 0)
    (v := .bin .xor .W64 (.reg .rax) (.reg lo0)) rfl (by decide) (by
      intro i hi
      rw [hmem]
      simp [findWrite, hi, Nat.not_le.mpr hi])
  have hword1 := wordAt_write hm' (r := 1) (o := 8)
    (v := .bin .xor .W64 (.reg .rdx) (.reg lo1)) rfl (by decide) (by
      intro i hi
      rw [hmem]
      simp only [findWrite, show 8 ≤ 8 + i by omega, show 8 + i < 8 + 8 by omega,
        and_self, ↓reduceIte, Nat.add_sub_cancel_left])
  have hew : NativeRustcVm.EWAt st'.data.dmem (off (rwA m0) (16 * n)) (prod + lo) := by
    apply NativeRustcVm.ewAt_iff.mpr
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64] at hword0 hword1
    change NativeRustcVm.WordAt _ _ (UInt64.ofBitVec (reg st.data .rax ^^^ reg st.data lo0)) at hword0
    change NativeRustcVm.WordAt _ _ (UInt64.ofBitVec (reg st.data .rdx ^^^ reg st.data lo1)) at hword1
    rw [hp0, hl0, ← UInt64.toBitVec_xor, UInt64.ofBitVec_toBitVec] at hword0
    rw [hp1, hl1, ← UInt64.toBitVec_xor, UInt64.ofBitVec_toBitVec] at hword1
    rw [show (prod + lo).c0 = prod.c0 ^^^ lo.c0 from rfl,
      show (prod + lo).c1 = prod.c1 ^^^ lo.c1 from rfl]
    exact ⟨by simpa only [off_zero] using hword0, hword1⟩
  exact cont st' hpc' hm' hm2 hew hs

end

end NativeRustcVmX64.KeccakGkr.KeccakOpen
