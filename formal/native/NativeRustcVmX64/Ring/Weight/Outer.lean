module

public import NativeRustcVmX64.Ring.Weight.Prod
public import NativeRustcVmX64.Ring.Weight.Sq
public import NativeRustcVmX64.Ring.Weight.Exit
public import NativeRustcVmX64.Code.Vm.EWMul.Names

/-!
# `ring_weight`: the coefficients' loop, `r'` not empty (x86-64)

Turn `n` (`OutH n`: before `b12`, the total and the powers `accW`'s after `n` coefficients):
`b12` loads the coefficient (the window `rsK n`), the product (`prodLoop`), `b15` spills it, the
powers squared (`sqLoop`), `b18` adds the product to the total and steps to the next coefficient;
after the last, `b19` jumps to the epilogue (`outLoop`, `outPath`).
-/

namespace NativeRustcVmX64.Ring.Weight

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring NativeVm.Model NativeRustcVm.Ring
open NativeRustcVmX64.Vm.RingWeight
open NativeRustcVmX64.Transcript (after)

@[expose] public section

/-- Before `b12`, turn `n`. -/
abbrev OutH [Host] (m0 : MachineData) (k n : Nat) : MachineState → Prop :=
  At m0 k NativeRustcVmX64.Vm.RingWeight.b12Offset [] noWr (tO sz0 []) (vv m0 0 n (Tot m0 n) 0) (PowI m0 n)

end

public section

variable {m0 : MachineData}

/-- Coefficient `n`'s window's alias. -/
theorem kOk [Labels] {n : Nat} {x : EW} {t s : EW} {m : MachineData} {ret : BitVec 64} :
    AliasesOk (tO (sz1 16) kAl) (envS m0 m 672 (rsK m0 n) (vv m0 x n t s) ret) :=
  oneAl rfl (ev_kal _ rfl rfl rfl)

variable [Host] {k : Nat}

/-- **Coefficient `n` loaded** (`b12`): the product's first factor. -/
theorem outLoad (hp : Placed code k) (h : RingWeightPre m0) {n : Nat} (hn : n < 64)
    {st : MachineState} (hA : OutH m0 k n st) :
    Eventually (step1 Host.exe) (At m0 k NativeRustcVmX64.Vm.RingWeight.b13Offset (rsQ m0 (16 * 0 + 16)) noWr
      (tP (sz1 (16 * 0 + 16)) qAl 0) (vv m0 (pp m0 n 0) n (Tot m0 n) 0) (PowI m0 n)) st := by
  have hR : nR m0 ≤ 36 := h.2.1
  have hA := hA.sw sw_out.1 (rs' := rsK m0 n) (wr' := noWr) rfl (fun _ _ ↦ kOk) outs_noWr
  obtain ⟨hok, hmiss⟩ := f_b12
  have hl := layK h hn
  refine (jfall hp hl b12_in_code (by simp [b12]) (next := 155) rfl hok
    (vals' := vv m0 (pp m0 n 0) n (Tot m0 n) 0) (I' := PowI m0 n) (fun m hB _ ret ↦ by
      wv
      · exact win_c0 h.1 h.2.2.2.2.1.1 h.2.2.2.2.1.2 hB (i := n) (by omega)
          (by simp only [coeffCount]; omega)
      · exact win_c1 h.1 h.2.2.2.2.1.1 h.2.2.2.2.1.2 hB (i := n) (by omega)
          (by simp only [coeffCount]; omega))
    rfl rfl rfl (fun _ _ ↦ noAl rfl) rfl
    (fun m m' hB hI hm ↦ slotsAt_keep h.1 (hl.wf hB.kept) hm hR hI hmiss) hA).mono
    fun st h' ↦ h'.sw sw_out.2.1 (rs' := rsQ m0 (16 * 0 + 16)) (wr' := noWr) rfl
      (fun _ _ ↦ oneAl rfl (al0 _)) outs_noWr

/-- **Turn `n`** (`r'` not empty). -/
theorem outTurn (hp : Placed code k) (h : RingWeightPre m0)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) {n : Nat} (hn : n < 64)
    (hQ : 0 < nQ m0) (hR0 : 0 < nR m0) {st : MachineState} (hA : OutH m0 k n st) :
    Eventually (step1 Host.exe) (fun st ↦ (n + 1 < 64 ∧ OutH m0 k (n + 1) st) ∨
      (n + 1 = 64 ∧ At m0 k NativeRustcVmX64.Vm.RingWeight.b19Offset [] noWr (tO sz0 []) (vv m0 0 64 (Tot m0 64) 0) (PowI m0 64) st))
      st := by
  have hR : nR m0 ≤ 36 := h.2.1
  have e : mn m0 = min (nR m0) (nQ m0) := rfl
  refine (outLoad hp h hn hA).bind fun st h1 ↦ ?_
  refine (prodLoop hp h hmul (mn m0 - 1) 0 (by omega) h1).bind fun st h2 ↦ ?_
  obtain ⟨hok15, hmiss15⟩ := f_b15 (mn m0) (by omega)
  refine (jfall hp (lay0 h.1) b15_in_code (by simp [b15]) (next := 172) rfl hok15
    (vals' := vv m0 0 n (Tot m0 n) (pp m0 n (mn m0))) (I' := SqI m0 n 0) (fun _ _ _ _ ↦ by wv)
    rfl rfl rfl (fun _ _ ↦ noAl rfl) rfl
    (fun m m' hB hI hm ↦ (slotsAt_keep h.1 ((lay0 h.1).wf hB.kept) hm hR hI hmiss15).congr
      fun l _ ↦ sqF_zero.symm) h2).bind fun st h3 ↦ ?_
  refine (sqLoop hp h hmul (nR m0 - 1) 0 (by omega) h3).bind fun st h4 ↦ ?_
  obtain ⟨hok18, hmiss18⟩ := f_b18 (nR m0) (by omega)
  refine (jcond hp (lay0 h.1) b18_in_code (by simp [b18]) (next := 190) rfl
    (by exact hp.label NativeRustcVmX64.Vm.RingWeight.label_17_at) hok18 (vals' := vv m0 0 (n + 1) (Tot m0 (n + 1)) 0)
    (I' := PowI m0 (n + 1)) (fun _ _ _ ↦ cv_ne (x := 16 * (n + 1)) _ (ev_k16 _ rfl) (by omega)
      (by decide))
    (fun _ _ _ _ ↦ by
      wv
      · exact ev_k16 _ rfl
      · rw [ev_t20, Tot_succ hn, ← pp_done]; exact tot_c0
      · rw [ev_t21, Tot_succ hn, ← pp_done]; exact tot_c1)
    rfl rfl rfl (fun _ _ ↦ noAl rfl) rfl
    (fun m m' hB hI hm ↦ (slotsAt_keep h.1 ((lay0 h.1).wf hB.kept) hm hR hI hmiss18).congr
      fun l hl ↦ sqF_done hn hl) h4).mono fun st h5 ↦ ?_
  by_cases hl : n + 1 < 64
  · rw [if_dt (by omega)] at h5
    exact .inl ⟨hl, h5⟩
  · rw [if_df (by omega)] at h5
    obtain rfl : n = 63 := by omega
    exact .inr ⟨rfl, h5⟩

/-- **The coefficients' loop** (`r'` not empty), from turn `n`. -/
theorem outLoop (hp : Placed code k) (h : RingWeightPre m0)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) (hQ : 0 < nQ m0)
    (hR0 : 0 < nR m0) :
    ∀ r n, n + r + 1 = 64 → ∀ {st : MachineState}, OutH m0 k n st →
      Eventually (step1 Host.exe)
        (At m0 k NativeRustcVmX64.Vm.RingWeight.b19Offset [] noWr (tO sz0 []) (vv m0 0 64 (Tot m0 64) 0) (PowI m0 64)) st := by
  intro r
  induction r with
  | zero =>
    intro n hn st hA
    refine (outTurn hp h hmul (by omega) hQ hR0 hA).mono fun st' h' ↦ ?_
    rcases h' with ⟨hlt, -⟩ | ⟨-, h'⟩
    · omega
    · exact h'
  | succ r ih =>
    intro n hn st hA
    refine (outTurn hp h hmul (by omega) hQ hR0 hA).bind fun st' h' ↦ ?_
    rcases h' with ⟨-, h'⟩ | ⟨he, -⟩
    · exact ih (n + 1) (by omega) h'
    · omega

/-- **`ring_weight` with `r'` not empty**, from the first turn. -/
theorem outPath (hp : Placed code k) (h : RingWeightPre m0)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) (hQ : 0 < nQ m0)
    (hR0 : 0 < nR m0) {st : MachineState} (hA : OutH m0 k 0 st) :
    Eventually (step1 Host.exe) (Goal m0) st := by
  refine (outLoop hp h hmul hQ hR0 63 0 rfl hA).bind fun st h1 ↦ ?_
  obtain hok := f_b19
  refine (jjump hp (lay0 h.1) b19_in_code (by simp [b19]) (by exact hp.label NativeRustcVmX64.Vm.RingWeight.label_13_at) hok
    (vals' := vv m0 0 64 (Tot m0 64) 0) (I' := fun _ ↦ True) (fun _ _ _ _ ↦ by wv) rfl rfl rfl
    (fun _ _ ↦ noAl rfl) rfl (fun _ _ _ _ _ ↦ trivial) h1).bind fun st h2 ↦ ?_
  exact exitW hp h (fun i hi ↦ by interval_cases i <;> simp only [vv]) rfl rfl Tot_done
    (h2.sw sw_out.2.2.1 (rs' := rsO m0) (wr' := oWr) rfl (fun _ _ ↦ oneAl rfl (al0 _)) outs_noWr)

end

end NativeRustcVmX64.Ring.Weight
