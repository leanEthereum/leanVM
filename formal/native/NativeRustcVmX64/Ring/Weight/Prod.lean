module

public import NativeRustcVmX64.Ring.Weight.Turn
public import NativeRustcVmX64.Ring.Weight.FactsB
public import NativeRustcVmX64.Ring.Weight.Sw
public import NativeRustcVmX64.Code.Vm.EWMul.Names

/-!
# `ring_weight`: a turn's product (x86-64)

Factor `i` (`b13`, `EW::mul` of the product so far and `1 + P_i + r'_i`, `r'` the window `rsQ`;
`b14` the next factor): `prodTurn`, `prodLoop`, the product `pp n |min(r, r')|` before `b15`.
-/

namespace NativeRustcVmX64.Ring.Weight

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring NativeVm.Model NativeRustcVm.Ring
open NativeRustcVmX64.Vm.RingWeight
open NativeRustcVmX64.Transcript (after)

public section

variable {m0 : MachineData} [Host] {k : Nat}

/-- **Factor `i` of turn `n`'s product.** -/
theorem prodTurn (hp : Placed code k) (h : RingWeightPre m0)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) {n i : Nat} (hi : i < mn m0)
    {st : MachineState}
    (hA : At m0 k NativeRustcVmX64.Vm.RingWeight.b13Offset (rsQ m0 (16 * i + 16)) noWr (tP (sz1 (16 * i + 16)) qAl i)
      (vv m0 (pp m0 n i) n (Tot m0 n) 0) (PowI m0 n) st) :
    Eventually (step1 Host.exe) (fun st ↦
      (i + 1 < mn m0 ∧ At m0 k NativeRustcVmX64.Vm.RingWeight.b13Offset (rsQ m0 (16 * (i + 1) + 16)) noWr
        (tP (sz1 (16 * (i + 1) + 16)) qAl (i + 1)) (vv m0 (pp m0 n (i + 1)) n (Tot m0 n) 0)
        (PowI m0 n) st) ∨
      (i + 1 = mn m0 ∧ At m0 k NativeRustcVmX64.Vm.RingWeight.b15Offset [] noWr (tP sz0 [] (i + 1))
        (vv m0 (pp m0 n (i + 1)) n (Tot m0 n) 0) (PowI m0 n) st)) st := by
  have hn : nR m0 ≤ 36 := h.2.1
  have e : mn m0 = min (nR m0) (nQ m0) := rfl
  have eQ : nQ m0 = (reg m0 .r8).toNat := rfl
  obtain ⟨hok, r_di, r_si, r_dx, r_cx, hmiss⟩ := f_b13 i (by omega)
  have hl := layQ h (n := 16 * i + 16) (by omega)
  refine Eventually.bind (mstep hp hmul hl b13_in_code (by simp [b13]) (next := 165) rfl hok
    (vals' := vv m0 (pp m0 n (i + 1)) n (Tot m0 n) 0) (I' := PowI m0 n) (fun _ _ _ _ ↦ by wv)
    rfl rfl (fun m hB hI mc ret hm ↦ ?_) rfl rfl rfl (fun _ _ ↦ oneAl rfl (al0 _)) rfl
    (fun m mc m' hB hI ⟨ret, hm⟩ hsp hq ↦ slots_callee h.1 hsp hq hn
      (slotsAt_keep h.1 (hl.wf hB.kept) hm hn hI hmiss)) hA) fun st h1 ↦ ?_
  · have q0 : (envS m0 m 672 (rsQ m0 (16 * i + 16)) (vv m0 (pp m0 n i) n (Tot m0 n) 0) ret).load
        1 (16 * i) 8 = c0 (qe m0 i) :=
      win_c0 h.1 h.2.2.2.1.1 h.2.2.2.1.2 hB (i := i) (by omega) (by omega)
    have q1 : (envS m0 m 672 (rsQ m0 (16 * i + 16)) (vv m0 (pp m0 n i) n (Tot m0 n) 0) ret).load
        1 (16 * i + 8) 8 = c1 (qe m0 i) :=
      win_c1 h.1 h.2.2.2.1.1 h.2.2.2.1.2 hB (i := i) (by omega) (by omega)
    have hr := mulRes_of (fun r v hv ↦ hm.regs r v hv) r_di r_si r_dx r_cx
      (x := pp m0 n i) (y := 1 + Pw m0 n i + qe m0 i) rfl rfl
      (by rw [ev_fA, slot_c0 hI (by omega), q0]; exact (fac_c0 _ _).symm)
      (by rw [ev_fB, slot_c1 hI (by omega), q1]; exact (fac_c1 _ _).symm)
    rw [hr, pp_succ hi]
    exact ⟨rfl, rfl⟩
  obtain ⟨hok14, hmiss14⟩ := f_b14 i (by omega)
  refine Eventually.bind (jcond hp hl b14_in_code (by simp [b14]) (next := 168) rfl
    (by exact hp.label NativeRustcVmX64.Vm.RingWeight.label_18_at) hok14 (vals' := vv m0 (pp m0 n (i + 1)) n (Tot m0 n) 0)
    (I' := PowI m0 n) (fun _ _ _ ↦ cv_ne (x := 16 * mn m0) _ rfl (by omega) (by omega))
    (fun _ _ _ _ ↦ by wv) rfl rfl rfl (fun _ _ ↦ oneAl rfl (al0 _)) rfl
    (fun m m' hB hI hm ↦ slotsAt_keep h.1 (hl.wf hB.kept) hm hn hI hmiss14) h1) fun st h2 ↦ ?_
  by_cases hlast : i + 1 = mn m0
  · rw [if_df (by omega)] at h2
    exact .done _ (.inr ⟨hlast, h2.sw (sw_prod i (by omega)).2 (rs' := []) (wr' := noWr) rfl
      (fun _ _ ↦ noAl rfl) outs_noWr⟩)
  · rw [if_dt (by omega)] at h2
    exact .done _ (.inl ⟨by omega, h2.sw (sw_prod i (by omega)).1
      (rs' := rsQ m0 (16 * (i + 1) + 16)) (wr' := noWr) rfl (fun _ _ ↦ oneAl rfl (al0 _))
      outs_noWr⟩)

/-- **Turn `n`'s product**, from factor `i`. -/
theorem prodLoop (hp : Placed code k) (h : RingWeightPre m0)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) {n : Nat} :
    ∀ r i, i + r + 1 = mn m0 → ∀ {st : MachineState},
      At m0 k NativeRustcVmX64.Vm.RingWeight.b13Offset (rsQ m0 (16 * i + 16)) noWr (tP (sz1 (16 * i + 16)) qAl i)
        (vv m0 (pp m0 n i) n (Tot m0 n) 0) (PowI m0 n) st →
      Eventually (step1 Host.exe) (At m0 k NativeRustcVmX64.Vm.RingWeight.b15Offset [] noWr (tP sz0 [] (mn m0))
        (vv m0 (pp m0 n (mn m0)) n (Tot m0 n) 0) (PowI m0 n)) st := by
  intro r
  induction r with
  | zero =>
    intro i hi st hA
    refine (prodTurn hp h hmul (by omega) hA).mono fun st' h' ↦ ?_
    rcases h' with ⟨hlt, -⟩ | ⟨he, h'⟩
    · omega
    · rwa [he] at h'
  | succ r ih =>
    intro i hi st hA
    refine (prodTurn hp h hmul (by omega) hA).bind fun st' h' ↦ ?_
    rcases h' with ⟨-, h'⟩ | ⟨he, -⟩
    · exact ih (i + 1) (by omega) h'
    · omega

end

end NativeRustcVmX64.Ring.Weight
