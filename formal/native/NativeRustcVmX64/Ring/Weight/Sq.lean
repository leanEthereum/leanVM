module

public import NativeRustcVmX64.Ring.Weight.Turn
public import NativeRustcVmX64.Ring.Weight.FactsC
public import NativeRustcVmX64.Code.Vm.EWMul.Names

/-!
# `ring_weight`: a turn's powers squared (x86-64)

Power `j` squared by `EW::mul` and stored back: with `r'` not empty `b16`, `b17` (`sqTurn`,
`sqLoop`), with `r'` empty `b22`, `b23` (`sqTurn2`, `sqLoop2`). The other values (`vals`'s
coefficient, total, spill) are kept.
-/

namespace NativeRustcVmX64.Ring.Weight

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring NativeVm.Model NativeRustcVm.Ring
open NativeRustcVmX64.Vm.RingWeight
open NativeRustcVmX64.Transcript (after)

public section

variable {m0 : MachineData}

/-- Power `j` squared and stored: the powers below `j + 1` done. -/
theorem sq_store [Labels] (h : RingWeightPre m0) {rs : List (BitVec 64 × Nat)}
    {vals : Nat → BitVec 64} {m m' : MachineData} {S : SState} {n j : Nat}
    (hwf : (envS m0 m 672 rs vals 0).WF) (hm : Match (envS m0 m 672 rs vals 0) S m')
    (hj : j < nR m0) (hI : SqI m0 n j m)
    (h6 : vals 6 = c0 (Pw m0 n j * Pw m0 n j)) (h7 : vals 7 = c1 (Pw m0 n j * Pw m0 n j))
    (hs : storeOk S (48 + 16 * j) (.var 6) (.var 7) = true)
    (h1 : missR 48 (48 + 16 * j) S = true) (h2 : missR (64 + 16 * j) 624 S = true) :
    SqI m0 n (j + 1) m' := by
  have hn : nR m0 ≤ 36 := h.2.1
  intro l hl
  by_cases hlj : l = j
  · subst hlj
    have := slot_new hm (by omega) hs
    rwa [show (Sym.var 6).eval (envS m0 m 672 rs vals 0) = vals 6 from rfl,
      show (Sym.var 7).eval (envS m0 m 672 rs vals 0) = vals 7 from rfl, h6, h7, ew_eta,
      ← sqF_new] at this
  · rw [sqF_succ hlj]
    exact slots_keep h.1 hwf hm (lo := j) (hi := j + 1) hn (by omega) hI h1
      (by rwa [show 48 + 16 * (j + 1) = 64 + 16 * j by omega]) l hl (by omega)

variable [Host] {k : Nat}

/-- **Power `j` squared** (`r'` not empty). -/
theorem sqTurn (hp : Placed code k) (h : RingWeightPre m0)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) {n j c : Nat} {t s : EW}
    (hj : j < nR m0) {st : MachineState}
    (hA : At m0 k NativeRustcVmX64.Vm.RingWeight.b16Offset [] noWr (tS sz0 j) (vv m0 0 c t s) (SqI m0 n j) st) :
    Eventually (step1 Host.exe) (At m0 k (if decide (j + 1 ≠ nR m0) then 172 else 183) [] noWr
      (tS sz0 (j + 1)) (vv m0 0 c t s) (SqI m0 n (j + 1))) st := by
  have hn : nR m0 ≤ 36 := h.2.1
  obtain ⟨hok, r_di, r_si, r_dx, r_cx, hmiss⟩ := f_b16 j (by omega)
  refine Eventually.bind (mstep hp hmul (lay0 h.1) b16_in_code (by simp [b16]) (next := 178) rfl
    hok (vals' := vv m0 (Pw m0 n j * Pw m0 n j) c t s) (I' := SqI m0 n j) (fun _ _ _ _ ↦ by wv)
    rfl rfl (fun m hB hI mc ret hm ↦ ?_) rfl rfl rfl (fun _ _ ↦ noAl rfl) rfl
    (fun m mc m' hB hI ⟨ret, hm⟩ hsp hq ↦ slots_callee h.1 hsp hq hn
      (slotsAt_keep h.1 ((lay0 h.1).wf hB.kept) hm hn hI hmiss)) hA) fun st h1 ↦ ?_
  · have e0 := slot_c0 (rs := []) (vals := vv m0 0 c t s) (ret := ret) hI hj
    have e1 := slot_c1 (rs := []) (vals := vv m0 0 c t s) (ret := ret) hI hj
    rw [sqF_self] at e0 e1
    have hr := mulRes_of (fun r v hv ↦ hm.regs r v hv) r_di r_si r_dx r_cx
      (x := Pw m0 n j) (y := Pw m0 n j) e0 e1 e0 e1
    rw [hr]
    exact ⟨rfl, rfl⟩
  obtain ⟨hok17, hs, hm0, hm1⟩ := f_b17 j (by omega)
  exact jcond hp (lay0 h.1) b17_in_code (by simp [b17]) (next := 183) rfl
    (by exact hp.label NativeRustcVmX64.Vm.RingWeight.label_20_at) hok17 (vals' := vv m0 0 c t s) (I' := SqI m0 n (j + 1))
    (fun _ _ _ ↦ cv_slot _ rfl rfl (by omega) hn) (fun _ _ _ _ ↦ by wv) rfl rfl rfl
    (fun _ _ ↦ noAl rfl) rfl
    (fun m m' hB hI hm ↦ sq_store h ((lay0 h.1).wf hB.kept) hm hj hI rfl rfl hs hm0 hm1) h1

/-- **The powers squared** (`r'` not empty), from power `j`. -/
theorem sqLoop (hp : Placed code k) (h : RingWeightPre m0)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) {n c : Nat} {t s : EW} :
    ∀ r j, j + r + 1 = nR m0 → ∀ {st : MachineState},
      At m0 k NativeRustcVmX64.Vm.RingWeight.b16Offset [] noWr (tS sz0 j) (vv m0 0 c t s) (SqI m0 n j) st →
      Eventually (step1 Host.exe) (At m0 k NativeRustcVmX64.Vm.RingWeight.b18Offset [] noWr (tS sz0 (nR m0)) (vv m0 0 c t s)
        (SqI m0 n (nR m0))) st := by
  intro r
  induction r with
  | zero =>
    intro j hj st hA
    have h' := sqTurn hp h hmul (by omega) hA
    rwa [if_df (by omega), show j + 1 = nR m0 by omega] at h'
  | succ r ih =>
    intro j hj st hA
    refine (sqTurn hp h hmul (by omega) hA).bind fun st' h' ↦ ?_
    rw [if_dt (by omega)] at h'
    exact ih (j + 1) (by omega) h'

/-- **Power `j` squared** (`r'` empty). -/
theorem sqTurn2 (hp : Placed code k) (h : RingWeightPre m0)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) {n j c : Nat} {t s : EW}
    (hj : j < nR m0) {st : MachineState}
    (hA : At m0 k NativeRustcVmX64.Vm.RingWeight.b22Offset [] noWr (tS2 sz0 j) (vv m0 0 c t s) (SqI m0 n j) st) :
    Eventually (step1 Host.exe) (At m0 k (if decide (j + 1 ≠ nR m0) then 202 else 213) [] noWr
      (tS2 sz0 (j + 1)) (vv m0 0 c t s) (SqI m0 n (j + 1))) st := by
  have hn : nR m0 ≤ 36 := h.2.1
  obtain ⟨hok, r_di, r_si, r_dx, r_cx, hmiss⟩ := f_b22 j (by omega)
  refine Eventually.bind (mstep hp hmul (lay0 h.1) b22_in_code (by simp [b22]) (next := 208) rfl
    hok (vals' := vv m0 (Pw m0 n j * Pw m0 n j) c t s) (I' := SqI m0 n j) (fun _ _ _ _ ↦ by wv)
    rfl rfl (fun m hB hI mc ret hm ↦ ?_) rfl rfl rfl (fun _ _ ↦ noAl rfl) rfl
    (fun m mc m' hB hI ⟨ret, hm⟩ hsp hq ↦ slots_callee h.1 hsp hq hn
      (slotsAt_keep h.1 ((lay0 h.1).wf hB.kept) hm hn hI hmiss)) hA) fun st h1 ↦ ?_
  · have e0 := slot_c0 (rs := []) (vals := vv m0 0 c t s) (ret := ret) hI hj
    have e1 := slot_c1 (rs := []) (vals := vv m0 0 c t s) (ret := ret) hI hj
    rw [sqF_self] at e0 e1
    have hr := mulRes_of (fun r v hv ↦ hm.regs r v hv) r_di r_si r_dx r_cx
      (x := Pw m0 n j) (y := Pw m0 n j) e0 e1 e0 e1
    rw [hr]
    exact ⟨rfl, rfl⟩
  obtain ⟨hok23, hs, hm0, hm1⟩ := f_b23 j (by omega)
  exact jcond hp (lay0 h.1) b23_in_code (by simp [b23]) (next := 213) rfl
    (by exact hp.label NativeRustcVmX64.Vm.RingWeight.label_11_at) hok23 (vals' := vv m0 0 c t s) (I' := SqI m0 n (j + 1))
    (fun _ _ _ ↦ cv_slot _ rfl rfl (by omega) hn) (fun _ _ _ _ ↦ by wv) rfl rfl rfl
    (fun _ _ ↦ noAl rfl) rfl
    (fun m m' hB hI hm ↦ sq_store h ((lay0 h.1).wf hB.kept) hm hj hI rfl rfl hs hm0 hm1) h1

/-- **The powers squared** (`r'` empty), from power `j`. -/
theorem sqLoop2 (hp : Placed code k) (h : RingWeightPre m0)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) {n c : Nat} {t s : EW} :
    ∀ r j, j + r + 1 = nR m0 → ∀ {st : MachineState},
      At m0 k NativeRustcVmX64.Vm.RingWeight.b22Offset [] noWr (tS2 sz0 j) (vv m0 0 c t s) (SqI m0 n j) st →
      Eventually (step1 Host.exe) (At m0 k NativeRustcVmX64.Vm.RingWeight.b24Offset [] noWr (tS2 sz0 (nR m0)) (vv m0 0 c t s)
        (SqI m0 n (nR m0))) st := by
  intro r
  induction r with
  | zero =>
    intro j hj st hA
    have h' := sqTurn2 hp h hmul (by omega) hA
    rwa [if_df (by omega), show j + 1 = nR m0 by omega] at h'
  | succ r ih =>
    intro j hj st hA
    refine (sqTurn2 hp h hmul (by omega) hA).bind fun st' h' ↦ ?_
    rw [if_dt (by omega)] at h'
    exact ih (j + 1) (by omega) h'

end

end NativeRustcVmX64.Ring.Weight
