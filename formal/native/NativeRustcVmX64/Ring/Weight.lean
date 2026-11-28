module

public import NativeRustcVmX64.Ring.Weight.Sum
public import NativeRustcVmX64.Ring.Weight.Copy
public import NativeRustcVmX64.Ring.Weight.Outer
public import NativeRustcVmX64.Ring.Weight.Empty
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.RingWeight.Names

/-!
# `ring_weight` on x86-64

**`ringWeight_spec`**: rustc's `ring_weight(out, r, r', coefficients)`, placed anywhere in the
program, given `EW::mul`'s contract, stores `some (ringWeight r r' coefficients)` at `out`. The
prologue (`b0`) zeroes the powers and branches on `|r|`: with `r` empty the total is the
coefficients' sum (`b3` to `b5`, `sumPath`); else `r` is copied into the powers (`b1`, `b2`, `b6`
to `b9`, `copyAll`), `b10` branches on `|r'|`, and each of the 64 coefficients' products is added
to the total, the powers squared after it, with `r'` not empty (`b11` to `b19`, `outPath`) or
empty (`b20` to `b24`, `emptyPath`); the epilogue (`b25`, `exitW`) stores `some` total.
-/

namespace NativeRustcVmX64.Ring.Weight

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring NativeVm.Model NativeRustcVm.Ring
open NativeRustcVmX64.Vm.RingWeight

public section

variable {m0 : MachineData} [Host] {k : Nat}

/-- **`r` copied, `|r| ≥ 1`**: `b10` branches on `|r'|`, `b11` or `b20` start the turns. -/
theorem turns (hp : Placed code k) (h : RingWeightPre m0)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) (hR0 : 0 < nR m0)
    {st : MachineState} (hA : At m0 k NativeRustcVmX64.Vm.RingWeight.b10Offset [] noWr (tD sz0 []) (V0 m0) (CopyI m0 (nR m0)) st) :
    Eventually (step1 Host.exe) (Goal m0) st := by
  have hR : nR m0 ≤ 36 := h.2.1
  obtain ⟨hok, hmiss⟩ := f_b10
  refine (jcond hp (lay0 h.1) b10_in_code (by simp [b10]) (next := 144) rfl
    (by exact hp.label NativeRustcVmX64.Vm.RingWeight.label_9_at) hok (vals' := V0 m0) (I' := CopyI m0 (nR m0))
    (b := decide (nQ m0 = 0)) (fun _ _ _ ↦ cv_test _ _ rfl)
    (fun _ _ _ _ ↦ by
      wv
      · exact ev_end15 _ rfl rfl
      · exact ev_min16 _ rfl rfl)
    rfl rfl rfl (fun _ _ ↦ noAl rfl) rfl
    (fun m m' hB hI hm ↦ slotsAt_keep h.1 ((lay0 h.1).wf hB.kept) hm hR hI hmiss) hA).bind
    fun st h1 ↦ ?_
  by_cases hQ : nQ m0 = 0
  · rw [if_dt hQ] at h1
    obtain ⟨hok20, hmiss20⟩ := f_b20
    refine (jfall hp (lay0 h.1) b20_in_code (by simp [b20]) (next := 196) rfl hok20
      (vals' := vv m0 0 0 (Tot m0 0) 0) (I' := PowI m0 0) (fun _ _ _ _ ↦ by wv <;> rfl)
      rfl rfl rfl (fun _ _ ↦ noAl rfl) rfl
      (fun m m' hB hI hm ↦ (slotsAt_keep h.1 ((lay0 h.1).wf hB.kept) hm hR hI hmiss20).congr
        fun l hl ↦ (Pw_zero hl).symm) h1).bind fun st h2 ↦ ?_
    exact emptyPath hp h hmul hQ hR0 h2
  · rw [if_df hQ] at h1
    obtain ⟨hok11, hmiss11⟩ := f_b11
    refine (jfall hp (lay0 h.1) b11_in_code (by simp [b11]) (next := 149) rfl hok11
      (vals' := vv m0 0 0 (Tot m0 0) 0) (I' := PowI m0 0) (fun _ _ _ _ ↦ by
        wv
        · rfl
        · exact ev_shl4' _ rfl (show min (nR m0) (nQ m0) ≤ 36 by omega)
        · rfl)
      rfl rfl rfl (fun _ _ ↦ noAl rfl) rfl
      (fun m m' hB hI hm ↦ (slotsAt_keep h.1 ((lay0 h.1).wf hB.kept) hm hR hI hmiss11).congr
        fun l hl ↦ (Pw_zero hl).symm) h1).bind fun st h2 ↦ ?_
    exact outPath hp h hmul (by omega) hR0 h2

/-- **`ring_weight` meets its contract.** -/
theorem ringWeight_spec (hp : Placed code k)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) :
    Spec (Labels.label NativeRustcVmX64.Vm.RingWeight.entryLabel) RingWeightPre RingWeightPost := by
  intro m0 h
  rw [show Labels.label NativeRustcVmX64.Vm.RingWeight.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.RingWeight.b0Offset) from hp.label NativeRustcVmX64.Vm.RingWeight.entry_at]
  have hA : At m0 k NativeRustcVmX64.Vm.RingWeight.b0Offset [] noWr t0 (V0 m0) (fun m ↦ m = m0) ⟨m0, Host.addrOf (k + NativeRustcVmX64.Vm.RingWeight.b0Offset)⟩ :=
    ⟨rfl, start rfl fun ret ↦ ⟨((Field.frame_rsp 672 0).trans (BitVec.add_zero _)).symm, trivial⟩,
      rfl⟩
  refine (jcond hp (lay0 h.1) b0_in_code (by simp [b0]) (next := 83) rfl
    (by exact hp.label NativeRustcVmX64.Vm.RingWeight.label_1_at) f_b0 (vals' := V0 m0) (I' := fun _ ↦ True)
    (b := decide (nR m0 = 0)) (fun m _ hm ↦ by subst hm; exact cv_test _ _ rfl)
    (fun m _ hm ret ↦ by subst hm; wv) rfl rfl rfl (fun _ _ ↦ noAl rfl) rfl
    (fun _ _ _ _ _ ↦ trivial) hA).bind fun st h1 ↦ ?_
  by_cases h0 : nR m0 = 0
  · rw [if_dt h0] at h1
    exact sumPath hp h h0 h1
  · rw [if_df h0] at h1
    exact (copyAll hp h h0 h1).bind fun st h2 ↦ turns hp h hmul (by omega) h2

end

end NativeRustcVmX64.Ring.Weight
