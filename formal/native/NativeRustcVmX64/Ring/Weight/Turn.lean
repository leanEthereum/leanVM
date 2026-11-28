module

public import NativeRustcVmX64.Ring.Weight.Vals

/-!
# `ring_weight`: a coefficient's turn, what both loops share (x86-64)

Turn `n` (coefficient `n`) starts with the total `Tot n` and the powers `Pw n` (`PowI n`: the
model's `accW` after `n` coefficients); its product's first `i` factors `pp n i`; while squaring,
the powers below `j` squared (`SqI n j`). The windows: the coefficient (`rsK n`), `r'` (`rsQ`).
-/

namespace NativeRustcVmX64.Ring.Weight

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring NativeVm.Model NativeRustcVm.Ring

@[expose] public section

/-- `r'`'s first `n` bytes. -/
abbrev rsQ (m0 : MachineData) (n : Nat) : List (BitVec 64 × Nat) :=
  [(reg m0 .rcx + BitVec.ofNat 64 0, n)]

/-- Coefficient `n`. -/
abbrev rsK (m0 : MachineData) (n : Nat) : List (BitVec 64 × Nat) :=
  [(reg m0 .r9 + BitVec.ofNat 64 (16 * n), 16)]

/-- The total before coefficient `n`. -/
abbrev Tot (m0 : MachineData) (n : Nat) : EW := (A m0 n).1

/-- Power `l` before coefficient `n`. -/
abbrev Pw (m0 : MachineData) (n l : Nat) : EW := (A m0 n).2.getD l 0

/-- The powers before coefficient `n`. -/
abbrev PowI (m0 : MachineData) (n : Nat) (d : MachineData) : Prop := SlotsAt m0 d (Pw m0 n) (nR m0)

/-- Power `l` while squaring the powers of turn `n`, those below `j` done. -/
abbrev SqF (m0 : MachineData) (n j l : Nat) : EW :=
  if l < j then Pw m0 n l * Pw m0 n l else Pw m0 n l

abbrev SqI (m0 : MachineData) (n j : Nat) (d : MachineData) : Prop :=
  SlotsAt m0 d (SqF m0 n j) (nR m0)

/-- Turn `n`'s product's first `i` factors. -/
abbrev pp (m0 : MachineData) (n i : Nat) : EW := prodPart (A m0 n).2 (qL m0) (ce m0 n) i

end

public section

variable {m0 : MachineData}

theorem layQ (h : RingWeightPre m0) {n : Nat} (hn : n ≤ 16 * nQ m0) : Lay m0 672 NW (rsQ m0 n) :=
  lay1 h.1 h.2.2.2.1.1 h.2.2.2.1.2 (by show 0 + n ≤ 16 * nQ m0; omega)

theorem layK (h : RingWeightPre m0) {n : Nat} (hn : n < 64) : Lay m0 672 NW (rsK m0 n) :=
  lay1 h.1 h.2.2.2.2.1.1 h.2.2.2.2.1.2 (by show 16 * n + 16 ≤ 16 * 64; omega)

theorem size_A {n : Nat} : (A m0 n).2.size = nR m0 := by rw [size_accW, size_rL]

theorem A_succ {n : Nat} (hn : n < 64) : A m0 (n + 1) = wStep (qL m0) (A m0 n) (ce m0 n) := by
  unfold A
  rw [accW_succ (by rw [size_cL]; exact hn), getElem_getD (by rw [size_cL]; exact hn), cL_getD hn]

theorem Tot_succ {n : Nat} (hn : n < 64) :
    Tot m0 (n + 1) = Tot m0 n + prodOf (A m0 n).2 (qL m0) (ce m0 n) := by
  unfold Tot
  rw [A_succ hn]
  rfl

theorem Pw_succ {n l : Nat} (hn : n < 64) (hl : l < nR m0) :
    Pw m0 (n + 1) l = Pw m0 n l * Pw m0 n l := by
  unfold Pw
  rw [A_succ hn]
  exact getD_map_sq (by rw [size_A]; exact hl)

theorem Pw_zero {l : Nat} (hl : l < nR m0) : Pw m0 0 l = re m0 l := rL_getD hl

theorem SlotsAt.congr {d : MachineData} {f g : Nat → EW} {c : Nat} (h : SlotsAt m0 d f c)
    (he : ∀ l < c, f l = g l) : SlotsAt m0 d g c := fun l hl ↦ he l hl ▸ h l hl

theorem sqF_zero {n l : Nat} : SqF m0 n 0 l = Pw m0 n l := ite_eq_right (Nat.not_lt_zero l)

theorem sqF_self {n j : Nat} : SqF m0 n j j = Pw m0 n j := ite_eq_right (Nat.lt_irrefl j)

theorem sqF_succ {n j l : Nat} (hl : l ≠ j) : SqF m0 n (j + 1) l = SqF m0 n j l := by
  unfold SqF
  by_cases h1 : l < j
  · rw [ite_eq_left h1, ite_eq_left (by omega)]
  · rw [ite_eq_right h1, ite_eq_right (by omega)]

theorem sqF_new {n j : Nat} : SqF m0 n (j + 1) j = Pw m0 n j * Pw m0 n j := ite_eq_left (Nat.lt_succ_self j)

theorem sqF_done {n l : Nat} (hn : n < 64) (hl : l < nR m0) : SqF m0 n (nR m0) l = Pw m0 (n + 1) l := by
  rw [Pw_succ hn hl]
  exact ite_eq_left hl

theorem pp_succ {n i : Nat} (hi : i < mn m0) :
    pp m0 n (i + 1) = pp m0 n i * (1 + Pw m0 n i + qe m0 i) := by
  have e : mn m0 = min (nR m0) (nQ m0) := rfl
  unfold pp
  rw [prodPart_succ (by rw [size_A]; omega) (by rw [size_qL]; omega),
    getElem_getD (by rw [size_A]; omega), getElem_getD (by rw [size_qL]; omega),
    qL_getD (by omega)]

theorem pp_done {n : Nat} : pp m0 n (mn m0) = prodOf (A m0 n).2 (qL m0) (ce m0 n) := by
  unfold pp
  rw [prodOf_eq, size_A, size_qL]

/-- The total plus the product, as `b18`, `b24` compute it. -/
theorem tot_c0 {t s : EW} : c0 t ^^^ c0 s = c0 (t + s) := rfl
theorem tot_c1 {t s : EW} : c1 t ^^^ c1 s = c1 (t + s) := rfl

theorem Tot_done : Tot m0 64 = ringWeight (rL m0) (qL m0) (cL m0) := by
  rw [ringWeight_eq, size_cL]

end

end NativeRustcVmX64.Ring.Weight
