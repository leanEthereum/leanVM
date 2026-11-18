/-
  LeanVM.Guest.CoreMode.CorePtr

  Runs whose bounds are entry cells' exponents, and runs of pointers: a mode signature's facts and
  the heap signature's at the slots' words.
-/

module

public import LeanVM.Guest.CoreMode.CoreSlot

/-!
# Exponent bounds and pointer runs

A mode run's bound is a constant or the exponent of a frame cell's word (`Mode.Idx.ex`); a heap run's
a constant or the exponent of a slot's word (`CIdx.val`). `idxX` translates the bounds of the cells
`2 + b` with no offset, `rngX` a run (`rngC` with exponent bounds). At a frame whose cells hold the
slots' words, `RW` of the mode run is its heap run written (`rw_slotX`) and back, given the bounds'
exponents (`slot_rwX`).

A mode pointer run (`preP`, `postP`: `PW`) is a heap pointer run (`prePR`, `postPR`: its cells' words
read on the reference `img.read`, `PtrSigSet`) at the same run: `pw_slotX` one way, in a memory
agreeing with the reference; `slot_pwX` the other, the run's cells written and the memory within the
reference's `2 ^ κ` cells, so that each pointer cell's word is the reference's.
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Prover.Exec (St Fine refMem maxCells Mem gpow_inj Mem.get_of_written Agree refRd_img)
open LeanVM.Guest.Mode (Names written_mono MonoVal BsVal BaseVal IdxVal HW RW PW PtrW)

@[expose] public section

variable {κ : ℕ}

/-! ## Bounds -/

theorem idxX_spec {i : Mode.Idx} {ci : CIdx} (h : idxX i = some ci) :
    (∃ n, i = .num n ∧ n < 2 ^ 62 ∧ ci = .num n) ∨ ∃ o, i = .ex (.fr o) 0 ∧ 2 ≤ o ∧ ci = .val (o - 2) := by
  cases i with
  | num n =>
    simp only [idxX, Bool.cond_eq_ite, decide_eq_true_eq] at h
    split_ifs at h with hn
    cases h
    exact .inl ⟨n, rfl, hn, rfl⟩
  | ex b c =>
    cases b with
    | fr o =>
      simp only [idxX, Bool.cond_eq_ite, Bool.and_eq_true, decide_eq_true_eq, Nat.beq_eq] at h
      split_ifs at h with hn
      cases h
      obtain ⟨h2, rfl⟩ := hn
      exact .inr ⟨o, rfl, h2, rfl⟩
    | hp q d => simp [idxX] at h

theorem rngX_spec {r : Mode.Rng} {q : CRun} (h : rngX r = some q) :
    ∃ lo hi c, idxX r.lo = some lo ∧ idxX r.hi = some hi ∧ monoC r.q = some c ∧
      q = ⟨⟨c.bases, c.off + r.d⟩, r.S, lo, hi⟩ := by
  unfold rngX at h
  split at h
  · rename_i lo hi c h1 h2 h3
    cases h
    exact ⟨lo, hi, c, h1, h2, h3, rfl⟩
  · cases h

theorem slotEq_app {s : St} {ws : List E} {a b : List (Mode.Base × ℕ)} (h : SlotEq s ws (a ++ b)) :
    SlotEq s ws a ∧ SlotEq s ws b :=
  ⟨fun x hx ↦ h x (List.mem_append_left _ hx), fun x hx ↦ h x (List.mem_append_right _ hx)⟩

theorem slotGet_app {s : St} {ws : List E} {a b : List (Mode.Base × ℕ)} (h : SlotGet s ws (a ++ b)) :
    SlotGet s ws a ∧ SlotGet s ws b :=
  ⟨fun x hx ↦ h x (List.mem_append_left _ hx), fun x hx ↦ h x (List.mem_append_right _ hx)⟩

/-- **A bound's value is its heap index's exponent** (where its cell holds its slot's word). -/
theorem idxVal_rep {s : St} {ws : List E} {i : Mode.Idx} {ci : CIdx} (hi : idxX i = some ci)
    (hc : SlotEq s ws (idxB i)) {x : ℕ} (h : IdxVal s i x) : rep ((idxC ci).valW (slotW ws)) = some x := by
  rcases idxX_spec hi with ⟨n, rfl, hn, rfl⟩ | ⟨o, rfl, h2, rfl⟩
  · simp only [IdxVal] at h
    subst h
    exact rep_const (by rw [capE_eq]; exact hn)
  · obtain ⟨v, e, hv, rfl, he, rfl⟩ := h
    obtain ⟨o', ho', -, hget⟩ := hc _ List.mem_cons_self
    simp only [Mode.Base.fr.injEq] at ho'
    subst ho'
    simp only [BaseVal] at hv
    rw [idxC, valW_baseC, ← hget _ hv]
    exact rep_of (by rw [capE_eq]; exact he)

/-- **A heap index's exponent is its bound's value** (where its cell holds its slot's word). -/
theorem rep_idxVal {s : St} {ws : List E} {i : Mode.Idx} {ci : CIdx} (hi : idxX i = some ci)
    (hc : SlotGet s ws (idxB i)) {x : ℕ} (h : rep ((idxC ci).valW (slotW ws)) = some x) : IdxVal s i x := by
  rcases idxX_spec hi with ⟨n, rfl, hn, rfl⟩ | ⟨o, rfl, h2, rfl⟩
  · rw [idxC, rep_const (by rw [capE_eq]; exact hn), Option.some.injEq] at h
    exact h.symm
  · obtain ⟨o', ho', -, hget⟩ := hc _ List.mem_cons_self
    simp only [Mode.Base.fr.injEq] at ho'
    subst ho'
    rw [idxC, valW_baseC] at h
    obtain ⟨hx, hw⟩ := rep_spec h
    exact ⟨_, x, hget, hw, by rw [capE_eq] at hx; exact hx, rfl⟩

/-- A constant bound's heap index has its exponent. -/
theorem rngX_rep_lo {r : Mode.Rng} {q : CRun} (h : rngX r = some q) (hb : idxB r.lo = []) (w : ℕ → E) :
    ∃ y, rep ((idxC q.lo).valW w) = some y := by
  obtain ⟨lo, hi, c, hlo, -, -, rfl⟩ := rngX_spec h
  rcases idxX_spec hlo with ⟨n, hn', hn, rfl⟩ | ⟨o, ho, -, -⟩
  · exact ⟨n, rep_const (by rw [capE_eq]; exact hn)⟩
  · rw [ho] at hb; simp [idxB] at hb

theorem rngX_rep_hi {r : Mode.Rng} {q : CRun} (h : rngX r = some q) (hb : idxB r.hi = []) (w : ℕ → E) :
    ∃ y, rep ((idxC q.hi).valW w) = some y := by
  obtain ⟨lo, hi, c, -, hhi, -, rfl⟩ := rngX_spec h
  rcases idxX_spec hhi with ⟨n, hn', hn, rfl⟩ | ⟨o, ho, -, -⟩
  · exact ⟨n, rep_const (by rw [capE_eq]; exact hn)⟩
  · rw [ho] at hb; simp [idxB] at hb

/-! ## Runs -/

theorem runSet_iff {w : ℕ → E} {q : CRun} {x : K} :
    q.Set w x ↔ ∃ ylo yhi j, rep ((idxC q.lo).valW w) = some ylo ∧ rep ((idxC q.hi).valW w) = some yhi ∧
      ylo ≤ j ∧ j < yhi ∧ x = (q.base.valW w * ofK (addressOfIndex (q.stride * j))).limb 0 := Iff.rfl

theorem run_cell {w : ℕ → E} (c : CCell) (S j d : ℕ) :
    (c.valW w * ofK (g ^ (S * j + d))) =
      ((⟨c.bases, c.off + d⟩ : CCell).valW w * ofK (addressOfIndex (S * j))) := by
  rw [valW_shiftc]
  simp only [addressOfIndex, pow_add, ofK_mul']
  ring

/-- **A run written is its heap run's cells written**, its bounds' cells holding their slots' words. -/
theorem rw_slotX {s : St} {ws : List E} {r : Mode.Rng} {q : CRun} (hr : rngX r = some q)
    (hc : SlotEq s ws (rngM r).bs) (h : RW s r) : ∀ x, q.Set (slotW ws) x → WrK s.mem x := by
  obtain ⟨lo, hi, c, hlo, hhi, hmc, rfl⟩ := rngX_spec hr
  obtain ⟨hc1, hc3⟩ := slotEq_app hc
  obtain ⟨hcq, hc2⟩ := slotEq_app hc1
  intro x hx
  obtain ⟨ylo, yhi, j, h1, h2, h3, h4, rfl⟩ := runSet_iff.mp hx
  obtain ⟨vq, xlo, xhi, hv, hil, hih, hall⟩ := h
  rw [idxVal_rep hlo hc2 hil, Option.some.injEq] at h1
  rw [idxVal_rep hhi hc3 hih, Option.some.injEq] at h2
  subst h1 h2
  obtain ⟨y, hy, hw⟩ := hall j h3 h4
  rw [monoVal_slot hmc hcq hv, run_cell] at hy
  exact wrk_names hy hw

/-- **A heap run written is its run written**, its bounds having exponents. -/
theorem slot_rwX {s : St} {ws : List E} {r : Mode.Rng} {q : CRun} (hr : rngX r = some q)
    (hc : SlotGet s ws (rngM r).bs) (hlo : ∃ y, rep ((idxC q.lo).valW (slotW ws)) = some y)
    (hhi : ∃ y, rep ((idxC q.hi).valW (slotW ws)) = some y)
    (h : ∀ x, q.Set (slotW ws) x → WrK s.mem x) : RW s r := by
  obtain ⟨lo, hi, c, hlo', hhi', hmc, rfl⟩ := rngX_spec hr
  obtain ⟨hc1, hc3⟩ := slotGet_app hc
  obtain ⟨hcq, hc2⟩ := slotGet_app hc1
  obtain ⟨ylo, hylo⟩ := hlo
  obtain ⟨yhi, hyhi⟩ := hhi
  refine ⟨_, ylo, yhi, monoVal_slot' hmc hcq, rep_idxVal hlo' hc2 hylo, rep_idxVal hhi' hc3 hyhi,
    fun j h1 h2 ↦ ?_⟩
  have hx := h _ (runSet_iff.mpr ⟨ylo, yhi, j, hylo, hyhi, h1, h2, rfl⟩)
  rw [run_cell]
  exact names_wrk hx

/-! ## Pointer runs -/

/-- The reference's word at a cell below `2 ^ κ`. -/
theorem read_refMem {img : MemoryImage κ} (hκ : κ ≤ 28) {x : ℕ} (hx : x < 2 ^ κ) :
    img.read (g ^ x) = some (refMem img x) := by
  have := MemoryImage.read_gpow (by omega) img ⟨x, hx⟩
  simp only [addressOfIndex] at this
  rw [this, refMem, dite_eq_left hx]

/-- **A pointer run is its heap pointer run** (its cells' words read on the reference), in a memory
agreeing with the reference. -/
theorem pw_slotX {img : MemoryImage κ} (hκ : κ ≤ 28) {s : St} (ha : Agree s.mem (refMem img)) {ws : List E}
    {r : Mode.Rng} {os : List ℕ} {q : CRun} (hr : rngX r = some q) (hc : SlotEq s ws (rngM r).bs)
    (h : PW s r os) : ∀ x, (∃ a, q.Set (slotW ws) a ∧ PtrSet img.read a os x) → WrK s.mem x := by
  obtain ⟨lo, hi, c, hlo, hhi, hmc, rfl⟩ := rngX_spec hr
  obtain ⟨hc1, hc3⟩ := slotEq_app hc
  obtain ⟨hcq, hc2⟩ := slotEq_app hc1
  rintro x ⟨a, ha', w', hw', o, ho, rfl⟩
  obtain ⟨ylo, yhi, j, h1, h2, h3, h4, rfl⟩ := runSet_iff.mp ha'
  obtain ⟨vq, xlo, xhi, hv, hil, hih, hall⟩ := h
  rw [idxVal_rep hlo hc2 hil, Option.some.injEq] at h1
  rw [idxVal_rep hhi hc3 hih, Option.some.injEq] at h2
  subst h1 h2
  obtain ⟨x', hx', p, hp, hpw⟩ := hall j h3 h4
  rw [monoVal_slot hmc hcq hv, run_cell] at hx'
  rw [hx'.1] at hw'
  have hrm := (refRd_img hκ img x' w' (by have := hx'.2; unfold maxCells at this; omega) hw').2
  have hpv : p = w' := by rw [← hrm]; exact (ha.get _ _ hp).symm
  subst hpv
  obtain ⟨y, hy, hyw⟩ := hpw o ho
  refine ⟨y, ?_, hy.2, hyw⟩
  rw [← hy.1, limb0_mul_ofK]

/-- **A heap pointer run is its pointer run**: the run's cells written, the memory within the
reference's `2 ^ κ` cells, agreeing with it, the bounds having exponents. -/
theorem slot_pwX {img : MemoryImage κ} (hκ : κ ≤ 28) {s : St} (ha : Agree s.mem (refMem img))
    (hu : s.mem.used ≤ 2 ^ κ) {ws : List E} {r : Mode.Rng} {os : List ℕ} {q : CRun} (hr : rngX r = some q)
    (hc : SlotGet s ws (rngM r).bs) (hlo : ∃ y, rep ((idxC q.lo).valW (slotW ws)) = some y)
    (hhi : ∃ y, rep ((idxC q.hi).valW (slotW ws)) = some y)
    (hcells : ∀ x, q.Set (slotW ws) x → WrK s.mem x)
    (h : ∀ x, (∃ a, q.Set (slotW ws) a ∧ PtrSet img.read a os x) → WrK s.mem x) : PW s r os := by
  obtain ⟨lo, hi, c, hlo', hhi', hmc, rfl⟩ := rngX_spec hr
  obtain ⟨hc1, hc3⟩ := slotGet_app hc
  obtain ⟨hcq, hc2⟩ := slotGet_app hc1
  obtain ⟨ylo, hylo⟩ := hlo
  obtain ⟨yhi, hyhi⟩ := hhi
  refine ⟨_, ylo, yhi, monoVal_slot' hmc hcq, rep_idxVal hlo' hc2 hylo, rep_idxVal hhi' hc3 hyhi,
    fun j h1 h2 ↦ ?_⟩
  have hset := runSet_iff.mpr ⟨ylo, yhi, j, hylo, hyhi, h1, h2, rfl⟩
  obtain ⟨x', hx', hw⟩ := names_wrk (hcells _ hset)
  obtain ⟨p, hp⟩ := Mem.get_of_written hw
  have hlt : x' < 2 ^ κ := lt_of_lt_of_le (ha.wf.get_lt hp) hu
  have hpv : p = refMem img x' := (ha.get _ _ hp).symm
  rw [run_cell]
  refine ⟨x', hx', p, hp, fun o ho ↦ ?_⟩
  have hrd : img.read (((⟨c.bases, c.off + r.d⟩ : CCell).valW (slotW ws) *
      ofK (addressOfIndex (r.S * j))).limb 0) = some p := by
    rw [hx'.1, hpv]
    exact read_refMem hκ hlt
  obtain ⟨y, hy1, hy2, hyw⟩ := h (p.limb 0 * addressOfIndex o) ⟨_, hset, p, hrd, o, ho, rfl⟩
  refine ⟨y, ⟨?_, hy2⟩, hyw⟩
  rw [limb0_mul_ofK]
  exact hy1

end

end LeanVM.Guest.CoreMode
