module

public import NativeRustcVmX64.Ring.Weight.Sq
public import NativeRustcVmX64.Ring.Weight.Exit
public import NativeRustcVmX64.Ring.Weight.Facts
public import NativeRustcVmX64.Ring.Weight.Sw
public import NativeRustcVmX64.Code.Vm.EWMul.Names

/-!
# `ring_weight`: the coefficients' loop, `r'` empty (x86-64)

Turn `n` (`EmpH n`, before `b21`): `b21` loads the coefficient (the window `rsK n`), which is
the product (`prodOf_nil`); the powers squared (`sqLoop2`); `b24` adds the coefficient to the
total and steps, after the last falls through to the epilogue (`emptyLoop`, `emptyPath`).
-/

namespace NativeRustcVmX64.Ring.Weight

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring NativeVm.Model NativeRustcVm.Ring
open NativeRustcVmX64.Vm.RingWeight
open NativeRustcVmX64.Transcript (after)

@[expose] public section

/-- Before `b21`, turn `n`. -/
abbrev EmpH [Host] (m0 : MachineData) (k n : Nat) : MachineState → Prop :=
  At m0 k NativeRustcVmX64.Vm.RingWeight.b21Offset [] noWr (tO2 sz0 []) (vv m0 0 n (Tot m0 n) 0) (PowI m0 n)

end

public section

variable {m0 : MachineData}

theorem qL_nil (hQ : nQ m0 = 0) : qL m0 = #[] := by
  rw [← Array.size_eq_zero_iff, size_qL, hQ]

variable [Host] {k : Nat}

/-- **Turn `n`** (`r'` empty). -/
theorem emptyTurn (hp : Placed code k) (h : RingWeightPre m0)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) {n : Nat} (hn : n < 64)
    (hQ : nQ m0 = 0) (hR0 : 0 < nR m0) {st : MachineState} (hA : EmpH m0 k n st) :
    Eventually (step1 Host.exe) (fun st ↦ (n + 1 < 64 ∧ EmpH m0 k (n + 1) st) ∨
      (n + 1 = 64 ∧ At m0 k NativeRustcVmX64.Vm.RingWeight.b25Offset [] noWr (tO2 sz0 []) (vv m0 0 64 (Tot m0 64) 0) (PowI m0 64) st))
      st := by
  have hR : nR m0 ≤ 36 := h.2.1
  have hA := hA.sw sw_out.2.2.2.1 (rs' := rsK m0 n) (wr' := noWr) rfl
    (fun _ _ ↦ oneAl rfl (ev_kal _ rfl rfl rfl)) outs_noWr
  obtain ⟨hok, hmiss⟩ := f_b21
  have hl := layK h hn
  refine (jfall hp hl b21_in_code (by simp [b21]) (next := 202) rfl hok
    (vals' := vv m0 0 n (Tot m0 n) (ce m0 n)) (I' := SqI m0 n 0) (fun m hB _ ret ↦ by
      wv
      · exact win_c0 h.1 h.2.2.2.2.1.1 h.2.2.2.2.1.2 hB (i := n) (by omega)
          (by simp only [coeffCount]; omega)
      · exact win_c1 h.1 h.2.2.2.2.1.1 h.2.2.2.2.1.2 hB (i := n) (by omega)
          (by simp only [coeffCount]; omega))
    rfl rfl rfl (fun _ _ ↦ noAl rfl) rfl
    (fun m m' hB hI hm ↦ (slotsAt_keep h.1 (hl.wf hB.kept) hm hR hI hmiss).congr
      fun l _ ↦ sqF_zero.symm) hA).bind fun st h1 ↦ ?_
  have h1 := h1.sw sw_out.2.2.2.2.1 (rs' := []) (wr' := noWr) rfl (fun _ _ ↦ noAl rfl) outs_noWr
  refine (sqLoop2 hp h hmul (nR m0 - 1) 0 (by omega) h1).bind fun st h2 ↦ ?_
  obtain ⟨hok24, hmiss24⟩ := f_b24 (nR m0) (by omega)
  refine (jcond hp (lay0 h.1) b24_in_code (by simp [b24]) (next := 219) rfl
    (by exact hp.label NativeRustcVmX64.Vm.RingWeight.label_10_at) hok24 (vals' := vv m0 0 (n + 1) (Tot m0 (n + 1)) 0)
    (I' := PowI m0 (n + 1)) (fun _ _ _ ↦ cv_ne (x := 16 * (n + 1)) _ (ev_k16 _ rfl) (by omega)
      (by decide))
    (fun _ _ _ _ ↦ by
      wv
      · rw [ev_t20, Tot_succ hn, qL_nil hQ, prodOf_nil]; exact tot_c0
      · rw [ev_t21, Tot_succ hn, qL_nil hQ, prodOf_nil]; exact tot_c1
      · exact ev_k16 _ rfl)
    rfl rfl rfl (fun _ _ ↦ noAl rfl) rfl
    (fun m m' hB hI hm ↦ (slotsAt_keep h.1 ((lay0 h.1).wf hB.kept) hm hR hI hmiss24).congr
      fun l hl ↦ sqF_done hn hl) h2).mono fun st h3 ↦ ?_
  by_cases hl : n + 1 < 64
  · rw [if_dt (by omega)] at h3
    exact .inl ⟨hl, h3⟩
  · rw [if_df (by omega)] at h3
    obtain rfl : n = 63 := by omega
    exact .inr ⟨rfl, h3⟩

/-- **The coefficients' loop** (`r'` empty), from turn `n`. -/
theorem emptyLoop (hp : Placed code k) (h : RingWeightPre m0)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) (hQ : nQ m0 = 0)
    (hR0 : 0 < nR m0) :
    ∀ r n, n + r + 1 = 64 → ∀ {st : MachineState}, EmpH m0 k n st →
      Eventually (step1 Host.exe)
        (At m0 k NativeRustcVmX64.Vm.RingWeight.b25Offset [] noWr (tO2 sz0 []) (vv m0 0 64 (Tot m0 64) 0) (PowI m0 64)) st := by
  intro r
  induction r with
  | zero =>
    intro n hn st hA
    refine (emptyTurn hp h hmul (by omega) hQ hR0 hA).mono fun st' h' ↦ ?_
    rcases h' with ⟨hlt, -⟩ | ⟨-, h'⟩
    · omega
    · exact h'
  | succ r ih =>
    intro n hn st hA
    refine (emptyTurn hp h hmul (by omega) hQ hR0 hA).bind fun st' h' ↦ ?_
    rcases h' with ⟨-, h'⟩ | ⟨he, -⟩
    · exact ih (n + 1) (by omega) h'
    · omega

/-- **`ring_weight` with `r'` empty**, from the first turn. -/
theorem emptyPath (hp : Placed code k) (h : RingWeightPre m0)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) (hQ : nQ m0 = 0)
    (hR0 : 0 < nR m0) {st : MachineState} (hA : EmpH m0 k 0 st) :
    Eventually (step1 Host.exe) (Goal m0) st :=
  (emptyLoop hp h hmul hQ hR0 63 0 rfl hA).bind fun st h1 ↦
    exitW hp h (fun i hi ↦ by interval_cases i <;> simp only [vv]) rfl rfl Tot_done
      (h1.sw sw_out.2.2.2.2.2 (rs' := rsO m0) (wr' := oWr) rfl (fun _ _ ↦ oneAl rfl (al0 _))
        outs_noWr)

end

end NativeRustcVmX64.Ring.Weight
