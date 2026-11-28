module

public import NativeRustcVmX64.Ring.Weight.Vals
public import NativeRustcVmX64.Ring.Weight.Facts
public import NativeRustcVmX64.Ring.Weight.FactsA
public import NativeRustcVmX64.Ring.Weight.Sw

/-!
# `ring_weight`: `r` copied into the powers (x86-64)

`b6` sets up the pairs' copy, `b7` copies `r`'s elements `2 t`, `2 t + 1` into powers `2 t`,
`2 t + 1` (`r` the window `rsR`, `copyTurn`, `copyLoop`), `b8` tests `|r|`'s parity, `b9` copies
the last element (`copyLast`; reached from `b2` directly when `|r| = 1`). Then the powers hold `r`
(`CopyI m0 |r|`) before `b10`.
-/

namespace NativeRustcVmX64.Ring.Weight

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring NativeVm.Model NativeRustcVm.Ring
open NativeRustcVmX64.Vm.RingWeight
open NativeRustcVmX64.Transcript (after)

@[expose] public section

/-- `r`'s first `n` bytes. -/
abbrev rsR (m0 : MachineData) (n : Nat) : List (BitVec 64 × Nat) :=
  [(reg m0 .rsi + BitVec.ofNat 64 0, n)]

/-- The values outside the loops. -/
abbrev V0 (m0 : MachineData) : Nat → BitVec 64 := vv m0 0 0 0 0

/-- The powers hold `r`'s first `c` elements. -/
abbrev CopyI (m0 : MachineData) (c : Nat) (d : MachineData) : Prop := SlotsAt m0 d (re m0) c

end

public section

variable {m0 : MachineData}

theorem layR (h : RingWeightPre m0) {n : Nat} (hn : n ≤ 16 * nR m0) : Lay m0 672 NW (rsR m0 n) :=
  lay1 h.1 h.2.2.1.1 h.2.2.1.2 (by show 0 + n ≤ 16 * nR m0; omega)

theorem copyI_zero {d : MachineData} : CopyI m0 0 d := fun _ hl ↦ absurd hl (Nat.not_lt_zero _)

/-- **Element `i` of `r` stored as power `i`**, from the window `rsR n`. -/
theorem copy_new [Labels] (h : RingWeightPre m0) {T S : SState} {m m' : MachineData} {n i : Nat}
    (hB : Bnd m0 672 NW (rsR m0 n) noWr T (V0 m0) m)
    (hm : Match (envS m0 m 672 (rsR m0 n) (V0 m0) 0) S m') (hi : i < nR m0) (hn : i < 36)
    (hs : storeOk S (48 + 16 * i) (.load 1 (16 * i) 8) (.load 1 (16 * i + 8) 8) = true) :
    NativeRustcVm.EWAt m'.dmem (slotA m0 i) (re m0 i) := by
  have e : nR m0 = (reg m0 .rdx).toNat := rfl
  have := slot_new hm hn hs
  rwa [win_c0 h.1 h.2.2.1.1 h.2.2.1.2 hB (i := i) (by omega) (by omega),
    win_c1 h.1 h.2.2.1.1 h.2.2.1.2 hB (i := i) (by omega) (by omega), ew_eta] at this

variable [Host] {k : Nat}

/-- **A turn of the pairs' copy.** -/
theorem copyTurn (hp : Placed code k) (h : RingWeightPre m0) {t : Nat}
    (ht : 2 * t + 2 ≤ nR m0) {st : MachineState}
    (hA : At m0 k NativeRustcVmX64.Vm.RingWeight.b7Offset (rsR m0 (32 * t + 32)) noWr (tC (sz1 (32 * t + 32)) rAl t) (V0 m0)
      (CopyI m0 (2 * t)) st) :
    Eventually (step1 Host.exe) (At m0 k (if decide (nR m0 / 2 * 2 ≠ 2 * t + 2) then 115 else 128)
      (rsR m0 (32 * t + 32)) noWr (tC (sz1 (32 * t + 32)) rAl (t + 1)) (V0 m0)
      (CopyI m0 (2 * t + 2))) st := by
  have hn : nR m0 ≤ 36 := h.2.1
  have e : nR m0 = (reg m0 .rdx).toNat := rfl
  obtain ⟨hok, hs0, hs1, hm0, hm1⟩ := f_b7 t (by omega)
  have hl := layR h (n := 32 * t + 32) (by omega)
  refine jcond hp hl b7_in_code (by simp [b7]) rfl (by exact hp.label NativeRustcVmX64.Vm.RingWeight.label_15_at) hok
    (fun _ _ _ ↦ cv_ne _ rfl (by omega) (by omega)) (fun _ _ _ _ ↦ by wv) rfl rfl rfl
    (fun _ _ ↦ oneAl rfl (al0 _)) rfl (fun m m' hB hI hm ↦ ?_) hA
  have hwf := hl.wf hB.kept (vals := V0 m0) (ret := 0)
  intro l hl'
  by_cases h1 : l < 2 * t
  · exact slots_keep h.1 hwf hm (lo := 2 * t) (hi := 2 * t + 2) (by omega) (by omega) hI
      (by rwa [show 48 + 16 * (2 * t) = 48 + 32 * t by omega]) (by
        rwa [show 48 + 16 * (2 * t + 2) = 80 + 32 * t by omega]) l h1 (.inl (by omega))
  · by_cases h2 : l = 2 * t
    · subst h2
      exact copy_new h hB hm (by omega) (by omega) (by
        rw [show 48 + 16 * (2 * t) = 48 + 32 * t by omega, show 16 * (2 * t) = 32 * t by omega]
        exact hs0)
    · obtain rfl : l = 2 * t + 1 := by omega
      exact copy_new h hB hm (by omega) (by omega) (by
        rw [show 48 + 16 * (2 * t + 1) = 64 + 32 * t by omega,
          show 16 * (2 * t + 1) = 32 * t + 16 by omega]
        exact hs1)

/-- **The pairs' copy**, from turn `t`. -/
theorem copyLoop (hp : Placed code k) (h : RingWeightPre m0) (h2 : 2 ≤ nR m0) :
    ∀ n t, t + n + 1 = nR m0 / 2 → ∀ {st : MachineState},
      At m0 k NativeRustcVmX64.Vm.RingWeight.b7Offset (rsR m0 (32 * t + 32)) noWr (tC (sz1 (32 * t + 32)) rAl t) (V0 m0)
        (CopyI m0 (2 * t)) st →
      Eventually (step1 Host.exe) (At m0 k NativeRustcVmX64.Vm.RingWeight.b8Offset (rsR m0 (32 * (nR m0 / 2))) noWr
        (tC (sz1 (32 * (nR m0 / 2))) rAl (nR m0 / 2)) (V0 m0) (CopyI m0 (2 * (nR m0 / 2)))) st := by
  have hn : nR m0 ≤ 36 := h.2.1
  have e : nR m0 = (reg m0 .rdx).toNat := rfl
  intro n
  induction n with
  | zero =>
    intro t ht st hA
    have h' := copyTurn hp h (t := t) (by omega) hA
    rw [if_df (by omega), show 32 * t + 32 = 32 * (nR m0 / 2) by omega,
      show t + 1 = nR m0 / 2 by omega, show 2 * t + 2 = 2 * (nR m0 / 2) by omega] at h'
    exact h'
  | succ n ih =>
    intro t ht st hA
    refine Eventually.bind (copyTurn hp h (by omega) hA) fun st' h' ↦ ?_
    rw [if_dt (by omega)] at h'
    have h'' := h'.sw (sw_b7 t (by omega)) (rs' := rsR m0 (32 * (t + 1) + 32)) (wr' := noWr) rfl
      (fun _ _ ↦ oneAl rfl (al0 _)) outs_noWr
    exact ih (t + 1) (by omega) (by rwa [show 2 * (t + 1) = 2 * t + 2 by omega])

/-- **The last element's copy** (`b9`), element `c`. -/
theorem copyLast (hp : Placed code k) (h : RingWeightPre m0) {c : Nat} (hc : c + 1 = nR m0)
    {st : MachineState}
    (hA : At m0 k NativeRustcVmX64.Vm.RingWeight.b9Offset (rsR m0 (16 * c + 16)) noWr (tL (sz1 (16 * c + 16)) rAl c) (V0 m0)
      (CopyI m0 c) st) :
    Eventually (step1 Host.exe) (At m0 k NativeRustcVmX64.Vm.RingWeight.b10Offset [] noWr (tD sz0 []) (V0 m0) (CopyI m0 (nR m0))) st := by
  have hn : nR m0 ≤ 36 := h.2.1
  have e : nR m0 = (reg m0 .rdx).toNat := rfl
  obtain ⟨hok, hs, hm0, hm1⟩ := f_b9 c (by omega)
  have hl := layR h (n := 16 * c + 16) (by omega)
  refine Eventually.bind (jfall hp hl b9_in_code (by simp [b9]) rfl hok (I' := CopyI m0 (nR m0)) (vals' := V0 m0)
    (fun _ _ _ _ ↦ by wv) rfl rfl rfl (fun _ _ ↦ noAl rfl) rfl (fun m m' hB hI hm ↦ ?_) hA)
    fun st h' ↦ .done _ (h'.sw (sw_b9 c (by omega)) (rs' := []) (wr' := noWr) rfl
      (fun _ _ ↦ noAl rfl) outs_noWr)
  have hwf := hl.wf hB.kept (vals := V0 m0) (ret := 0)
  intro l hl'
  by_cases h1 : l < c
  · exact slots_keep h.1 hwf hm (lo := c) (hi := c + 1) (by omega) (by omega) hI hm0
      (by rwa [show 48 + 16 * (c + 1) = 64 + 16 * c by omega]) l h1 (.inl h1)
  · obtain rfl : l = c := by omega
    exact copy_new h hB hm (by omega) (by omega) hs

/-- **The parity test** (`b8`) after the pairs, and the last element if `|r|` is odd. -/
theorem copyEnd (hp : Placed code k) (h : RingWeightPre m0) {st : MachineState}
    (hA : At m0 k NativeRustcVmX64.Vm.RingWeight.b8Offset (rsR m0 (32 * (nR m0 / 2))) noWr (tC (sz1 (32 * (nR m0 / 2))) rAl (nR m0 / 2))
      (V0 m0) (CopyI m0 (2 * (nR m0 / 2))) st) :
    Eventually (step1 Host.exe) (At m0 k NativeRustcVmX64.Vm.RingWeight.b10Offset [] noWr (tD sz0 []) (V0 m0) (CopyI m0 (nR m0))) st := by
  have hn : nR m0 ≤ 36 := h.2.1
  have e : nR m0 = (reg m0 .rdx).toNat := rfl
  obtain ⟨hok, hmiss⟩ := f_b8 (nR m0 / 2) (by omega)
  have hl := layR h (n := 32 * (nR m0 / 2)) (by omega)
  refine Eventually.bind (jcond hp hl b8_in_code (by simp [b8]) rfl (by exact hp.label NativeRustcVmX64.Vm.RingWeight.label_7_at)
    hok (vals' := V0 m0) (I' := CopyI m0 (2 * (nR m0 / 2))) (fun _ _ _ ↦ cv_odd (x := reg m0 .rdx) _ rfl (by omega)) (fun _ _ _ _ ↦ by wv) rfl rfl rfl
    (fun _ _ ↦ oneAl rfl (al0 _)) rfl
    (fun m m' hB hI hm ↦ slotsAt_keep h.1 (hl.wf hB.kept) hm (by omega) hI hmiss) hA)
    fun st h' ↦ ?_
  by_cases hev : nR m0 % 2 = 0
  · rw [if_dt hev] at h'
    have h'' := h'.sw (sw_b8 (nR m0 / 2) (by omega)).1 (rs' := []) (wr' := noWr) rfl
      (fun _ _ ↦ noAl rfl) outs_noWr
    rw [show 2 * (nR m0 / 2) = nR m0 by omega] at h''
    exact .done _ h''
  · rw [if_df hev] at h'
    have h'' := h'.sw (sw_b8 (nR m0 / 2) (by omega)).2
      (rs' := rsR m0 (16 * (2 * (nR m0 / 2)) + 16)) (wr' := noWr) rfl
      (fun _ _ ↦ oneAl rfl (al0 _)) outs_noWr
    exact copyLast hp h (by omega) h''

/-- **`r` copied**, from `b1` (`|r| ≥ 1`). -/
theorem copyAll (hp : Placed code k) (h : RingWeightPre m0) (h0 : nR m0 ≠ 0) {I : MachineData → Prop}
    {st : MachineState} (hA : At m0 k NativeRustcVmX64.Vm.RingWeight.b1Offset [] noWr (tA sz0 []) (V0 m0) I st) :
    Eventually (step1 Host.exe) (At m0 k NativeRustcVmX64.Vm.RingWeight.b10Offset [] noWr (tD sz0 []) (V0 m0) (CopyI m0 (nR m0))) st := by
  have hn : nR m0 ≤ 36 := h.2.1
  have e : nR m0 = (reg m0 .rdx).toNat := rfl
  obtain ⟨hok1, -⟩ := f_b1
  refine Eventually.bind (jcond hp (lay0 h.1) b1_in_code (by simp [b1]) (next := 89) rfl
    (by exact hp.label NativeRustcVmX64.Vm.RingWeight.label_14_at) hok1 (b := decide (nR m0 ≠ 1)) (I' := fun _ ↦ True) (vals' := V0 m0)
    (fun _ _ _ ↦ cv_ne (x := nR m0) _ (ofNat_toNat' _).symm (by omega) (by decide))
    (fun _ _ _ _ ↦ by wv; exact ev_shl4 _ rfl hn) rfl rfl rfl (fun _ _ ↦ noAl rfl) rfl
    (fun _ _ _ _ _ ↦ trivial) hA) fun st h1 ↦ ?_
  by_cases hr1 : nR m0 = 1
  · rw [if_df (by omega)] at h1
    obtain ⟨hok2, -⟩ := f_b2
    refine Eventually.bind (jjump hp (lay0 h.1) b2_in_code (by simp [b2])
      (by exact hp.label NativeRustcVmX64.Vm.RingWeight.label_6_at) hok2 (I' := CopyI m0 0) (vals' := V0 m0) (fun _ _ _ _ ↦ by wv) rfl rfl rfl
      (fun _ _ ↦ noAl rfl) rfl (fun _ _ _ _ _ ↦ copyI_zero) h1) fun st h2 ↦ ?_
    have h3 := h2.sw sw_one (rs' := rsR m0 (16 * 0 + 16)) (wr' := noWr) rfl
      (fun _ _ ↦ oneAl rfl (al0 _)) outs_noWr
    exact copyLast hp h (by omega) h3
  · rw [if_dt (by omega)] at h1
    obtain ⟨hok6, -⟩ := f_b6
    refine Eventually.bind (jfall hp (lay0 h.1) b6_in_code (by simp [b6]) (next := 115) rfl hok6
      (I' := CopyI m0 (2 * 0)) (vals' := V0 m0) (fun _ _ _ _ ↦ by wv; exact ev_and25 _ rfl hn) rfl rfl rfl
      (fun _ _ ↦ noAl rfl) rfl (fun _ _ _ _ _ ↦ copyI_zero) h1) fun st h2 ↦ ?_
    have h3 := h2.sw sw_b6 (rs' := rsR m0 (32 * 0 + 32)) (wr' := noWr) rfl
      (fun _ _ ↦ oneAl rfl (al0 _)) outs_noWr
    exact (copyLoop hp h (by omega) (nR m0 / 2 - 1) 0 (by omega) h3).bind fun st h4 ↦
      copyEnd hp h h4

end

end NativeRustcVmX64.Ring.Weight
