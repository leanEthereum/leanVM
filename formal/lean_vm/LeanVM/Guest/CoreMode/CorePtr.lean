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

theorem idxC_idxO (b c : ℕ) : idxC (idxO b c) = ⟨[(b, 1)], c⟩ := by
  cases c <;> rfl

theorem valW_idxO (w : ℕ → E) (b c : ℕ) :
    (idxC (idxO b c)).valW w = w b * ofK (addressOfIndex c) := by
  rw [idxC_idxO]
  simp [CCell.valW, prodW]

/-- **A heap index has an exponent** at the slots' words `w`, at least its constant offset. -/
def IdxEx (w : ℕ → E) (i : CIdx) : Prop := ∃ y, rep ((idxC i).valW w) = some y ∧ (idxC i).off ≤ y

theorem idxEx_num (w : ℕ → E) {n : ℕ} (hn : n < 2 ^ 62) : IdxEx w (.num n) :=
  ⟨n, rep_const (by rw [capE_eq]; exact hn), le_refl _⟩

theorem idxEx_val {w : ℕ → E} {b : ℕ} {e : ℕ} (he : e < 2 ^ 62) (hw : w b = ofK (g ^ e)) : IdxEx w (.val b) :=
  ⟨e, by rw [idxC, valW_baseC, hw]; exact rep_of (by rw [capE_eq]; exact he), Nat.zero_le _⟩

/-- `g^e · g^c` read as its exponent `e + c`. -/
theorem idxEx_idxO {w : ℕ → E} {b c e : ℕ} (he : e + c < 2 ^ 62) (hw : w b = ofK (g ^ e)) : IdxEx w (idxO b c) := by
  refine ⟨e + c, ?_, by rw [idxC_idxO]; exact Nat.le_add_left _ _⟩
  rw [valW_idxO, hw, show ofK (g ^ e) * ofK (addressOfIndex c) = ofK (addressOfIndex (e + c)) by
    rw [addressOfIndex, addressOfIndex, pow_add, ofK_mul]]
  exact rep_of (by rw [capE_eq]; exact he)

theorem idxX_spec {i : Mode.Idx} {ci : CIdx} (h : idxX i = some ci) :
    (∃ n, i = .num n ∧ n < 2 ^ 62 ∧ ci = .num n) ∨
      ∃ o c, i = .ex (.fr o) c ∧ 2 ≤ o ∧ c < 2 ^ 28 ∧ ci = idxO (o - 2) c := by
  cases i with
  | num n =>
    simp only [idxX, Bool.cond_eq_ite, decide_eq_true_eq] at h
    split_ifs at h with hn
    cases h
    exact .inl ⟨n, rfl, hn, rfl⟩
  | ex b c =>
    cases b with
    | fr o =>
      simp only [idxX, Bool.cond_eq_ite, Bool.and_eq_true, decide_eq_true_eq] at h
      split_ifs at h with hn
      cases h
      exact .inr ⟨o, c, rfl, hn.1, hn.2, rfl⟩
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

/-- **A bound's value is its heap index's exponent, if it has one** (where its cell holds its slot's word): the
bound `e + c` of the word `g^e`, `e < 2^62`, `c < 2^28`, and the exponent below `2^62` of `g^(e + c)`. -/
theorem idxVal_rep {s : St} {ws : List E} {i : Mode.Idx} {ci : CIdx} (hi : idxX i = some ci)
    (hc : SlotEq s ws (idxB i)) {x : ℕ} (h : IdxVal s i x) {y : ℕ}
    (hy : rep ((idxC ci).valW (slotW ws)) = some y) : y = x := by
  rcases idxX_spec hi with ⟨n, rfl, hn, rfl⟩ | ⟨o, c, rfl, h2, hc28, rfl⟩
  · simp only [IdxVal] at h
    subst h
    rw [idxC, rep_const (by rw [capE_eq]; exact hn), Option.some.injEq] at hy
    exact hy.symm
  · obtain ⟨v, e, hv, rfl, he, rfl⟩ := h
    obtain ⟨o', ho', -, hget⟩ := hc _ List.mem_cons_self
    simp only [Mode.Base.fr.injEq] at ho'
    subst ho'
    simp only [BaseVal] at hv
    rw [valW_idxO, ← hget _ hv] at hy
    obtain ⟨hy1, hy2⟩ := rep_spec hy
    rw [capE_eq] at hy1
    refine gpow_inj_lt (by omega) (by omega) ?_
    rw [← hy2, addressOfIndex, addressOfIndex, pow_add, ofK_mul]

/-- **A heap index's exponent, at least its offset, is its bound's value** (where its cell holds its slot's word). -/
theorem rep_idxVal {s : St} {ws : List E} {i : Mode.Idx} {ci : CIdx} (hi : idxX i = some ci)
    (hc : SlotGet s ws (idxB i)) {x : ℕ} (h : rep ((idxC ci).valW (slotW ws)) = some x) (hx : (idxC ci).off ≤ x) :
    IdxVal s i x := by
  rcases idxX_spec hi with ⟨n, rfl, hn, rfl⟩ | ⟨o, c, rfl, h2, hc28, rfl⟩
  · rw [idxC, rep_const (by rw [capE_eq]; exact hn), Option.some.injEq] at h
    exact h.symm
  · obtain ⟨o', ho', -, hget⟩ := hc _ List.mem_cons_self
    simp only [Mode.Base.fr.injEq] at ho'
    subst ho'
    rw [idxC_idxO] at hx
    change c ≤ x at hx
    rw [valW_idxO] at h
    obtain ⟨hx1, hw⟩ := rep_spec h
    rw [capE_eq] at hx1
    have hw' : slotW ws (o - 2) = ofK (g ^ (x - c)) := by
      have hne : ofK (addressOfIndex c) ≠ 0 := Mode.ofK_gpow_ne_zero c
      refine mul_right_cancel₀ hne ?_
      rw [hw, addressOfIndex, addressOfIndex, ← ofK_mul, ← pow_add, Nat.sub_add_cancel hx]
    exact ⟨_, x - c, hget, hw', by omega, by omega⟩

/-! ## Runs -/

theorem runSet_iff {w : ℕ → E} {q : CRun} {x : K} :
    q.Set w x ↔ ∃ ylo yhi j, rep ((idxC q.lo).valW w) = some ylo ∧ rep ((idxC q.hi).valW w) = some yhi ∧
      ylo ≤ j ∧ j < yhi ∧ x = (q.base.valW w * ofK (addressOfIndex (q.stride * j))).limb 0 := Iff.rfl

theorem run_cell {w : ℕ → E} (c : CCell) (S j d : ℕ) :
    (c.valW w * ofK (g ^ (S * j + d))) =
      ((⟨c.bases, c.off + d⟩ : CCell).valW w * ofK (addressOfIndex (S * j))) := by
  rw [valW_shiftc]
  simp only [addressOfIndex, pow_add, ofK_mul]
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
  have e1 := idxVal_rep hlo hc2 hil h1
  have e2 := idxVal_rep hhi hc3 hih h2
  subst e1 e2
  obtain ⟨y, hy, hw⟩ := hall j h3 h4
  rw [monoVal_slot hmc hcq hv, run_cell] at hy
  exact wrk_names hy hw

/-- **A heap run written is its run written**, its bounds having exponents. -/
theorem slot_rwX {s : St} {ws : List E} {r : Mode.Rng} {q : CRun} (hr : rngX r = some q)
    (hc : SlotGet s ws (rngM r).bs) (hlo : IdxEx (slotW ws) q.lo) (hhi : IdxEx (slotW ws) q.hi)
    (h : ∀ x, q.Set (slotW ws) x → WrK s.mem x) : RW s r := by
  obtain ⟨lo, hi, c, hlo', hhi', hmc, rfl⟩ := rngX_spec hr
  obtain ⟨hc1, hc3⟩ := slotGet_app hc
  obtain ⟨hcq, hc2⟩ := slotGet_app hc1
  obtain ⟨ylo, hylo, hylo'⟩ := hlo
  obtain ⟨yhi, hyhi, hyhi'⟩ := hhi
  refine ⟨_, ylo, yhi, monoVal_slot' hmc hcq, rep_idxVal hlo' hc2 hylo hylo', rep_idxVal hhi' hc3 hyhi hyhi',
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
  have e1 := idxVal_rep hlo hc2 hil h1
  have e2 := idxVal_rep hhi hc3 hih h2
  subst e1 e2
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
    (hc : SlotGet s ws (rngM r).bs) (hlo : IdxEx (slotW ws) q.lo) (hhi : IdxEx (slotW ws) q.hi)
    (hcells : ∀ x, q.Set (slotW ws) x → WrK s.mem x)
    (h : ∀ x, (∃ a, q.Set (slotW ws) a ∧ PtrSet img.read a os x) → WrK s.mem x) : PW s r os := by
  obtain ⟨lo, hi, c, hlo', hhi', hmc, rfl⟩ := rngX_spec hr
  obtain ⟨hc1, hc3⟩ := slotGet_app hc
  obtain ⟨hcq, hc2⟩ := slotGet_app hc1
  obtain ⟨ylo, hylo, hylo'⟩ := hlo
  obtain ⟨yhi, hyhi, hyhi'⟩ := hhi
  refine ⟨_, ylo, yhi, monoVal_slot' hmc hcq, rep_idxVal hlo' hc2 hylo hylo', rep_idxVal hhi' hc3 hyhi hyhi',
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

/-! ## Pointer bases -/

theorem hp_val {s : St} {q d k : ℕ} {v : E} (h : MonoVal s ⟨0, k, [(.hp q d, 1)]⟩ v) :
    ∃ p x u, s.mem.get (s.fp + q) = some p ∧ Names (p * ofK (g ^ d)) x ∧ s.mem.get x = some u ∧
      v = u * ofK (g ^ k) := by
  obtain ⟨w, ⟨u, w', ⟨p, x, hp, hx, hu⟩, hw', rfl⟩, rfl⟩ := h
  simp only [BsVal] at hw'
  subst hw'
  refine ⟨p, x, u, hp, hx, hu, ?_⟩
  simp only [pow_zero, one_mul, pow_one, mul_one]
  ring

/-- **A pointer-based product written is its pointer fact's cell written** (the pointer's word read on
the reference), in a memory agreeing with the reference, its frame cell holding the slot's word. -/
theorem hw_hp {img : MemoryImage κ} (hκ : κ ≤ 28) {s : St} (ha : Agree s.mem (refMem img)) {ws : List E}
    {q d k : ℕ} (_hq : 2 ≤ q) (hc : SlotEq s ws [(.fr q, 1)]) (h : HW s ⟨0, k, [(.hp q d, 1)]⟩) {w : E}
    (hr : img.read ((⟨[(q - 2, 1)], d⟩ : CCell).addrW (slotW ws)) = some w) :
    WrK s.mem (w.limb 0 * addressOfIndex k) := by
  obtain ⟨v, y, hv, hy, hw⟩ := h
  obtain ⟨p, x, u, hp, hx, hu, rfl⟩ := hp_val hv
  obtain ⟨o, ho, -, hget⟩ := hc _ List.mem_cons_self
  simp only [Mode.Base.fr.injEq] at ho
  subst ho
  have hpw : p = slotW ws (q - 2) := hget p hp
  have hadr : (⟨[(q - 2, 1)], d⟩ : CCell).addrW (slotW ws) = g ^ x := by
    rw [← hx.1, hpw]
    simp [CCell.addrW, CCell.valW, prodW, addressOfIndex, limb0_mul_ofK]
  rw [hadr] at hr
  have hrm := (refRd_img hκ img x w (by have := hx.2; unfold maxCells at this; omega) hr).2
  have huw : u = w := by rw [← hrm]; exact (ha.get _ _ hu).symm
  subst huw
  refine ⟨y, ?_, hy.2, hw⟩
  rw [← hy.1, limb0_mul_ofK]

/-- **A pointer fact's cells written make its pointer-based product written**: the pointer cell written,
the memory within the reference's `2 ^ κ` cells, agreeing with it. -/
theorem hp_hw {img : MemoryImage κ} (hκ : κ ≤ 28) {s : St} (ha : Agree s.mem (refMem img))
    (hu : s.mem.used ≤ 2 ^ κ) {ws : List E} {q d k : ℕ} (_hq : 2 ≤ q) (hc : SlotGet s ws [(.fr q, 1)])
    (hcell : WrK s.mem ((⟨[(q - 2, 1)], d⟩ : CCell).addrW (slotW ws)))
    (h : ∀ w, img.read ((⟨[(q - 2, 1)], d⟩ : CCell).addrW (slotW ws)) = some w →
      WrK s.mem (w.limb 0 * addressOfIndex k)) : HW s ⟨0, k, [(.hp q d, 1)]⟩ := by
  obtain ⟨o, ho, -, hget⟩ := hc _ List.mem_cons_self
  simp only [Mode.Base.fr.injEq] at ho
  subst ho
  obtain ⟨x, hx, hxlt, hxw⟩ := hcell
  obtain ⟨u, hgu⟩ := Mem.get_of_written hxw
  have hlt : x < 2 ^ κ := lt_of_lt_of_le (ha.wf.get_lt hgu) hu
  have hux : u = refMem img x := (ha.get _ _ hgu).symm
  have hrd : img.read ((⟨[(q - 2, 1)], d⟩ : CCell).addrW (slotW ws)) = some u := by
    rw [hx, hux]; exact read_refMem hκ hlt
  obtain ⟨y, hy, hylt, hyw⟩ := h u hrd
  have hnx : Names (slotW ws (q - 2) * ofK (g ^ d)) x := by
    refine ⟨?_, hxlt⟩
    rw [← hx]
    simp [CCell.addrW, CCell.valW, prodW, addressOfIndex, limb0_mul_ofK]
  refine ⟨u * ofK (g ^ k), y, ⟨u, ⟨u, 1, ⟨_, x, hget, hnx, hgu⟩, rfl, by simp⟩, by simp [mul_comm]⟩, ⟨?_, hylt⟩, hyw⟩
  rw [limb0_mul_ofK]
  exact hy

theorem hpOf_spec {m : Mode.Mono} {q d : ℕ} (h : hpOf m = some (q, d)) : m = ⟨0, m.k, [(.hp q d, 1)]⟩ := by
  obtain ⟨fp, k, bs⟩ := m
  unfold hpOf at h
  split at h
  · rename_i q' d' h1 h2
    cases h
    simp only at h1 h2
    subst h1 h2
    rfl
  · cases h

theorem monoS_fr {G : Mode.Sig} {n : ℕ} {ent : Bool} {q : ℕ} (h : hpSlot G n ent q = true) :
    monoS G n ent ⟨0, 0, [(.fr q, 1)]⟩ = true := by
  simpa [monoS, hpSlot] using h


/-! ## Runs over one pointer base -/

theorem bsVal_hpSplit {s : St} : ∀ {bs : List (Mode.Base × ℕ)} {q d : ℕ} {rest : List (Mode.Base × ℕ)},
    hpSplit bs = some ((q, d), rest) → ∀ {v : E}, BsVal s bs v →
      ∃ u w, BaseVal s (.hp q d) u ∧ BsVal s rest w ∧ v = u * w
  | [], _, _, _, h, _, _ => by simp [hpSplit] at h
  | (.hp q' d', e) :: bs, q, d, rest, h, v, hv => by
    simp only [hpSplit, Bool.cond_eq_ite, Bool.and_eq_true, Nat.beq_eq] at h
    split_ifs at h with hc
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    obtain ⟨u, w, hu, hw, rfl⟩ := hv
    rw [hc.1]
    exact ⟨u, w, hu, hw, by simp⟩
  | (.fr o, e) :: bs, q, d, rest, h, v, hv => by
    simp only [hpSplit, Option.map_eq_some_iff] at h
    obtain ⟨⟨p1, p2⟩, hp, he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨a, b, ha, hb, rfl⟩ := hv
    obtain ⟨u, w, hu, hw, rfl⟩ := bsVal_hpSplit hp hb
    exact ⟨u, a ^ e * w, hu, ⟨a, w, ha, hw, rfl⟩, by ring⟩

/-- **A run over one pointer base written is its run at the cell's word written** (`rngQ`; the word read on the
reference), in a memory agreeing with the reference, its frame cells holding their slots' words. -/
theorem rw_slotQ {img : MemoryImage κ} (hκ : κ ≤ 28) {s : St} (ha : Agree s.mem (refMem img)) {ws : List E}
    {r : Mode.Rng} {c : CCell} {q : CRun} (hr : rngQ r = some (c, q))
    (hc : ∀ q' d bs, hpSplit r.q.bs = some ((q', d), bs) →
      SlotEq s ws ((.fr q', 1) :: (bs ++ idxB r.lo ++ idxB r.hi)))
    (h : RW s r) : ∀ x, (∃ w, img.read (c.addrW (slotW ws)) = some w ∧
      RunSetB (slotW ws) w q.base q.stride (idxC q.lo) (idxC q.hi) x) → WrK s.mem x := by
  unfold rngQ at hr
  split at hr
  · rename_i q' d bs hsp
    simp only [Bool.cond_eq_ite, decide_eq_true_eq] at hr
    split_ifs at hr with h2
    obtain ⟨q0, hq0, he⟩ := Option.map_eq_some_iff.mp hr
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have hsl := hc q' d bs hsp
    obtain ⟨lo, hi, c0, hlo, hhi, hmc, rfl⟩ := rngX_spec hq0
    rintro x ⟨w, hw, ylo, yhi, j, h1, h2', h3, h4, rfl⟩
    obtain ⟨vq, xlo, xhi, hv, hil, hih, hall⟩ := h
    have hsl' : SlotEq s ws (bs ++ idxB r.lo ++ idxB r.hi) := fun b hb ↦ hsl b (List.mem_cons_of_mem _ hb)
    obtain ⟨hc1, hc3⟩ := slotEq_app hsl'
    obtain ⟨hcq, hc2⟩ := slotEq_app hc1
    have e1 := idxVal_rep hlo hc2 hil h1
    have e2 := idxVal_rep hhi hc3 hih h2'
    subst e1 e2
    obtain ⟨y, hy, hyw⟩ := hall j h3 h4
    obtain ⟨w0, hbs, rfl⟩ := hv
    obtain ⟨u, wr, hu, hwr, rfl⟩ := bsVal_hpSplit hsp hbs
    obtain ⟨p, x0, hp, hx0, hu'⟩ := hu
    obtain ⟨o, ho, -, hget⟩ := hsl _ List.mem_cons_self
    simp only [Mode.Base.fr.injEq] at ho
    subst ho
    have hpw : p = slotW ws (q' - 2) := hget p hp
    have hadr : (⟨[(q' - 2, 1)], d⟩ : CCell).addrW (slotW ws) = g ^ x0 := by
      rw [← hx0.1, hpw]
      simp [CCell.addrW, CCell.valW, prodW, addressOfIndex, limb0_mul_ofK]
    rw [hadr] at hw
    have hrm := (refRd_img hκ img x0 w (by have := hx0.2; unfold maxCells at this; omega) hw).2
    have huw : u = w := by rw [← hrm]; exact (ha.get _ _ hu').symm
    subst huw
    have hmv : MonoVal s ⟨r.q.fp, r.q.k, bs⟩ (ofK (g ^ s.fp) ^ r.q.fp * ofK (g ^ r.q.k) * wr) := ⟨wr, hwr, rfl⟩
    have hrest := monoVal_slot hmc hcq hmv
    refine wrk_names (x := y) ?_ hyw
    have : ofK (g ^ s.fp) ^ r.q.fp * ofK (g ^ r.q.k) * (u * wr) * ofK (g ^ (r.S * j + r.d)) =
        u * ((ofK (g ^ s.fp) ^ r.q.fp * ofK (g ^ r.q.k) * wr) * ofK (g ^ (r.S * j + r.d))) := by ring
    rw [this, hrest, run_cell, ← mul_assoc] at hy
    exact hy
  · cases hr

/-- **A pointer fact a guaranteed run over one pointer base gives is written** (`hpRunIn`): its offsets' cells past
the word at its cell (read on the reference), in a memory agreeing with the reference. -/
theorem hpRun_wr {img : MemoryImage κ} (hκ : κ ≤ 28) {s : St} (ha : Agree s.mem (refMem img)) {ws : List E}
    {G : Mode.Sig} {n : ℕ} {p : CCell × List ℕ} (hp : hpRunIn G n p = true)
    (hR : ∀ r ∈ G.postR, RW s r) (hSE : ∀ {m0 : Mode.Mono}, monoS G n false m0 = true → SlotEq s ws m0.bs)
    {w : E} (hw : img.read (p.1.addrW (slotW ws)) = some w) {o : ℕ} (ho : o ∈ p.2) :
    WrK s.mem (w.limb 0 * addressOfIndex o) := by
  obtain ⟨r, hr, hrr⟩ := List.any_eq_true.mp hp
  cases hq : hpRunOf r with
  | none => simp [hq] at hrr
  | some x =>
    obtain ⟨q, d, lo, hi⟩ := x
    obtain ⟨hrq, hlo, hhi⟩ := hpRunOf_spec hq
    simp only [hq, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, List.mem_range, Nat.beq_eq] at hrr
    obtain ⟨⟨hsl, hpb⟩, hos⟩ := hrr
    obtain ⟨t, ht, rfl⟩ := hos o ho
    rw [CCell.beq_eq hpb] at hw
    obtain ⟨vq, xlo, xhi, hv, hil, hih, hall⟩ := hR _ hr
    rw [hlo] at hil
    rw [hhi] at hih
    simp only [IdxVal] at hil hih
    subst xlo xhi
    obtain ⟨y, hy, hyw⟩ := hall (lo + t) (by omega) (by omega)
    rw [hrq] at hv
    obtain ⟨pp, x, u, hpp, hx, hu, rfl⟩ := hp_val hv
    obtain ⟨o', ho', -, hget⟩ := hSE (monoS_fr hsl) _ List.mem_cons_self
    simp only [Mode.Base.fr.injEq] at ho'
    subst ho'
    have hpw : pp = slotW ws (q - 2) := hget pp hpp
    have hadr : (⟨[(q - 2, 1)], d⟩ : CCell).addrW (slotW ws) = g ^ x := by
      rw [← hx.1, hpw]
      simp [CCell.addrW, CCell.valW, prodW, addressOfIndex, limb0_mul_ofK]
    rw [hadr] at hw
    have hrm := (refRd_img hκ img x w (by have := hx.2; unfold maxCells at this; omega) hw).2
    have huw : u = w := by rw [← hrm]; exact (ha.get _ _ hu).symm
    subst huw
    refine ⟨y, ?_, hy.2, hyw⟩
    rw [← hy.1, limb0_mul_ofK, limb0_mul_ofK]
    simp only [addressOfIndex, pow_add, mul_assoc]
    ring

end

end LeanVM.Guest.CoreMode
