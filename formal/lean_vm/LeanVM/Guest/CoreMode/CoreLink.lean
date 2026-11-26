/-
  LeanVM.Guest.CoreMode.CoreLink

  A mode signature's bases through the caller's frame (`.hp 1 d`) at an honest frame: the caller's
  cell `d` linked to a slot (`CFun.gl`, `GlF`), a run over them written is its heap run written.
-/

module

public import LeanVM.Guest.CoreMode.CorePtr

/-!
# The caller's cells, linked to slots

A mode signature may name a word of its caller's frame: the base `.hp 1 d`, cell `d` of the frame
header cell `1` names. The core route links such a cell to a slot (`CFun.gl`: cell `d` holds slot
`b`'s word times `g^k`, `GlF` at the honest frames), and translates the base to slot `b` (`baseOfL`,
`k = 0`) and a bound on it to the exponent of `ws[b]·g^k` (`idxL`). At a frame agreeing with the
reference whose parameter cells hold their slots' words and whose caller's linked cells hold theirs
(`slotEqL_of`), a run written is its heap run written (`rw_slotL`).
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Prover.Exec (St Fine refMem maxCells Mem gpow_inj Mem.get_of_written Agree refRd_img)
open LeanVM.Guest.Mode (Names written_mono MonoVal BsVal BaseVal IdxVal HW RW names_shift)

@[expose] public section

variable {κ : ℕ}

theorem names_uniqL {u : E} {x y : ℕ} (hx : Names u x) (hy : Names u y) : x = y :=
  gpow_inj (by have := hx.2; unfold maxCells at this; omega)
    (by have := hy.2; unfold maxCells at this; omega) (hx.1.symm.trans hy.1)

theorem lookup_memL {α β : Type} [BEq α] [LawfulBEq α] {a : α} {b : β} :
    ∀ {l : List (α × β)}, l.lookup a = some b → (a, b) ∈ l
  | [], h => by simp at h
  | (a', b') :: l, h => by
    simp only [List.lookup] at h
    split at h
    · rename_i hab
      cases h
      rw [beq_iff_eq] at hab
      subst hab
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (lookup_memL h)

/-- **The word a base holds**, its slot's: a frame cell `2 + b`'s slot `b`'s, a linked caller's cell's slot
`b`'s times `g^k`. -/
def BaseL (gl : List (ℕ × ℕ × ℕ)) (gp : List ((ℕ × ℕ) × ℕ)) (ws : List E) : Mode.Base → Option E
  | .fr o => if 2 ≤ o then some (slotW ws (o - 2)) else none
  | .hp q d => if q = 1 then (gl.lookup d).map fun p ↦ slotW ws p.1 * ofK (g ^ p.2) else
    (gp.lookup (q, d)).map (slotW ws)

/-- **The bases hold their slots' words** where they have one. -/
def SlotEqL (gl : List (ℕ × ℕ × ℕ)) (gp : List ((ℕ × ℕ) × ℕ)) (s : St) (ws : List E) (bs : List (Mode.Base × ℕ)) :
    Prop :=
  ∀ b ∈ bs, ∃ w, BaseL gl gp ws b.1 = some w ∧ ∀ u, BaseVal s b.1 u → u = w

variable {gp : List ((ℕ × ℕ) × ℕ)}

theorem slotEqL_app {gl : List (ℕ × ℕ × ℕ)} {s : St} {ws : List E} {a b : List (Mode.Base × ℕ)}
    (h : SlotEqL gl gp s ws (a ++ b)) : SlotEqL gl gp s ws a ∧ SlotEqL gl gp s ws b :=
  ⟨fun x hx ↦ h x (List.mem_append_left _ hx), fun x hx ↦ h x (List.mem_append_right _ hx)⟩

theorem baseOfL_spec {gl : List (ℕ × ℕ × ℕ)} {ws : List E} {b : Mode.Base} {e k e' : ℕ}
    (h : baseOfL gl gp (b, e) = some (k, e')) : e' = e ∧ BaseL gl gp ws b = some (slotW ws k) := by
  cases b with
  | fr o =>
    simp only [baseOfL] at h
    split_ifs at h with h2
    cases h
    exact ⟨rfl, by simp [BaseL, h2]⟩
  | hp q d =>
    simp only [baseOfL] at h
    split_ifs at h with h1
    · split at h
      · rename_i b0 hl
        cases h
        refine ⟨rfl, ?_⟩
        simp [BaseL, h1, hl]
      · cases h
    · obtain ⟨b0, hl, h⟩ := Option.map_eq_some_iff.mp h
      cases h
      exact ⟨rfl, by simp [BaseL, h1, hl]⟩

theorem bsVal_slotL {gl : List (ℕ × ℕ × ℕ)} {s : St} {ws : List E} : ∀ (bs : List (Mode.Base × ℕ)) (cb : List (ℕ × ℕ)),
    bs.mapM (baseOfL gl gp) = some cb → SlotEqL gl gp s ws bs → ∀ w, BsVal s bs w → w = prodW (slotW ws) cb
  | [], cb, h, _, w, hw => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    simpa [BsVal, prodW] using hw
  | (b, e) :: bs, cb, h, hc, w, hw => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨⟨k, e'⟩, hx, xs, hxs, rfl⟩ := h
    obtain ⟨rfl, hb⟩ := baseOfL_spec (ws := ws) hx
    obtain ⟨w0, hw0, hu0⟩ := hc (b, _) List.mem_cons_self
    rw [hb, Option.some.injEq] at hw0
    subst hw0
    obtain ⟨u, w', hu, hw', rfl⟩ := hw
    rw [hu0 u hu, bsVal_slotL bs xs hxs (fun b hb ↦ hc b (List.mem_cons_of_mem _ hb)) w' hw']
    rfl

theorem monoF_specL {gl : List (ℕ × ℕ × ℕ)} {m : Mode.Mono} {c : CCell} (h : monoF (baseOfL gl gp) m = some c) :
    m.fp = 0 ∧ ∃ cb, m.bs.mapM (baseOfL gl gp) = some cb ∧ c = ⟨cb, m.k⟩ := by
  unfold monoF at h
  split_ifs at h with h0
  obtain ⟨cb, hcb, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨h0, cb, hcb, rfl⟩

theorem monoVal_slotL {gl : List (ℕ × ℕ × ℕ)} {s : St} {ws : List E} {m : Mode.Mono} {c : CCell}
    (hm : monoF (baseOfL gl gp) m = some c) (hc : SlotEqL gl gp s ws m.bs) {v : E} (h : MonoVal s m v) :
    v = c.valW (slotW ws) := by
  obtain ⟨h0, cb, hcb, rfl⟩ := monoF_specL hm
  obtain ⟨w, hw, rfl⟩ := h
  rw [bsVal_slotL m.bs cb hcb hc w hw, h0]
  simp only [pow_zero, one_mul, CCell.valW]
  ring

/-- **A bound's value is its heap index's exponent, if it has one**, the caller's cells linked. -/
theorem idxVal_repL {gl : List (ℕ × ℕ × ℕ)} {s : St} {ws : List E} {i : Mode.Idx} {ci : CIdx}
    (hi : idxL gl i = some ci) (hc : SlotEqL gl gp s ws (idxB i)) {x : ℕ} (h : IdxVal s i x) {y : ℕ}
    (hy : rep ((idxC ci).valW (slotW ws)) = some y) : y = x := by
  -- the base's word, a power of `g`
  have hbase : ∀ b, IdxVal s (.ex b 0) x → (∃ w, BaseL gl gp ws b = some w ∧ ∀ u, BaseVal s b u → u = w) →
      ∃ w, BaseL gl gp ws b = some w ∧ rep w = some x := by
    rintro b ⟨v, e, hv, hve, he, rfl⟩ ⟨w, hw, hu⟩
    refine ⟨w, hw, ?_⟩
    rw [← hu v hv, hve]
    exact rep_of (by rw [capE_eq]; exact he)
  suffices hs : rep ((idxC ci).valW (slotW ws)) = some x by
    rw [hs, Option.some.injEq] at hy
    exact hy.symm
  cases i with
  | num n =>
    simp only [idxL, idxX, Bool.cond_eq_ite, decide_eq_true_eq] at hi
    split_ifs at hi with hn
    cases hi
    simp only [IdxVal] at h
    subst h
    exact rep_const (by rw [capE_eq]; exact hn)
  | ex b c =>
    cases b with
    | fr o =>
      simp only [idxL, idxX, Bool.cond_eq_ite, Bool.and_eq_true, decide_eq_true_eq] at hi
      split_ifs at hi with hn
      cases hi
      obtain ⟨v, e, hv, rfl, he, rfl⟩ := h
      obtain ⟨w, hw, hu⟩ := hc _ List.mem_cons_self
      simp only [BaseL, hn.1, ite_true, Option.some.injEq] at hw
      subst hw
      have hy' := hy
      rw [valW_idxO, ← hu _ hv] at hy'
      obtain ⟨hy1, hy2⟩ := rep_spec hy'
      rw [capE_eq] at hy1
      have hyx : y = e + c := gpow_inj_lt (by omega) (by omega) (by
        rw [← hy2, addressOfIndex, addressOfIndex, pow_add, ofK_mul'])
      rw [← hyx]
      exact hy
    | hp q d =>
      simp only [idxL] at hi
      split_ifs at hi with hn
      obtain ⟨rfl, rfl⟩ := hn
      obtain ⟨⟨b, k⟩, hl, rfl⟩ := Option.map_eq_some_iff.mp hi
      obtain ⟨w, hw, hr⟩ := hbase _ h (hc _ List.mem_cons_self)
      simp only [BaseL, ite_true, hl, Option.map_some, Option.some.injEq] at hw
      subst hw
      cases k with
      | zero =>
        simpa [idxC, valW_baseC] using hr
      | succ k =>
        simpa [idxC, CCell.valW, prodW, addressOfIndex] using hr

theorem rngL_spec {gl : List (ℕ × ℕ × ℕ)} {r : Mode.Rng} {q : CRun} (h : rngL gl gp r = some q) :
    ∃ lo hi c, idxL gl r.lo = some lo ∧ idxL gl r.hi = some hi ∧ monoF (baseOfL gl gp) r.q = some c ∧
      q = ⟨⟨c.bases, c.off + r.d⟩, r.S, lo, hi⟩ := by
  unfold rngL at h
  split at h
  · rename_i lo hi c h1 h2 h3
    cases h
    exact ⟨lo, hi, c, h1, h2, h3, rfl⟩
  · cases h

/-- **A run written is its heap run's cells written**, the caller's cells linked. -/
theorem rw_slotL {gl : List (ℕ × ℕ × ℕ)} {s : St} {ws : List E} {r : Mode.Rng} {q : CRun} (hr : rngL gl gp r = some q)
    (hc : SlotEqL gl gp s ws (rngM r).bs) (h : RW s r) : ∀ x, q.Set (slotW ws) x → WrK s.mem x := by
  obtain ⟨lo, hi, c, hlo, hhi, hmc, rfl⟩ := rngL_spec hr
  obtain ⟨hc1, hc3⟩ := slotEqL_app hc
  obtain ⟨hcq, hc2⟩ := slotEqL_app hc1
  intro x hx
  obtain ⟨ylo, yhi, j, h1, h2, h3, h4, rfl⟩ := runSet_iff.mp hx
  obtain ⟨vq, xlo, xhi, hv, hil, hih, hall⟩ := h
  have e1 := idxVal_repL hlo hc2 hil h1
  have e2 := idxVal_repL hhi hc3 hih h2
  subst e1 e2
  obtain ⟨y, hy, hw⟩ := hall j h3 h4
  rw [monoVal_slotL hmc hcq hv, run_cell] at hy
  exact wrk_names hy hw

/-- **The own parameter words at frame `fp`** of the reference (`gp`, `gpOf`): base `.hp q d` at slot `b`, the word at
cell `d` past the word `p` of frame cell `q` being slot `b`'s. -/
def GpF (img : MemoryImage κ) (gp : List ((ℕ × ℕ) × ℕ)) (fp : ℕ) (ws : List E) : Prop :=
  ∀ q d b, gp.lookup (q, d) = some b → ∃ p, Rd img fp q = some p ∧
    ∀ x, Names (p * ofK (g ^ d)) x → slotW ws b = refMem img x

/-- **At a frame agreeing with the reference**, whose cells `2 + b` hold slot `b`'s word for `b < n`, whose
caller's linked cells hold theirs (`GlF`) and whose own parameter words theirs (`GpF`), bases the frame knows
(`baseS`): `SlotEqL`. -/
theorem slotEqL_of {img : MemoryImage κ} (hκ : κ ≤ 28) {s : St} (ha : Agree s.mem (refMem img))
    (hfp : s.fp < maxCells) {ws : List E} {n : ℕ} (hws : ∀ b < n, Rd img s.fp (2 + b) = some (slotW ws b))
    {gl : List (ℕ × ℕ × ℕ)} (hgl : GlF img gl s.fp ws) (hgp : GpF img gp s.fp ws) {bs : List (Mode.Base × ℕ)}
    (hall : bs.all (baseS gl gp n ·.1) = true) : SlotEqL gl gp s ws bs := by
  intro b hb
  have h := List.all_eq_true.mp hall b hb
  rcases hb1 : b.1 with o | ⟨q, d⟩
  · rw [hb1] at h
    simp only [baseS, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨h2, hn⟩, h28⟩ := h
    refine ⟨slotW ws (o - 2), by simp [BaseL, h2], fun u hu ↦ rd_getA hκ ha hfp h28 ?_ hu⟩
    have := hws (o - 2) hn
    rwa [show 2 + (o - 2) = o by omega] at this
  · rw [hb1] at h
    by_cases hq : q = 1
    · subst hq
      have h' : (!Nat.beq d 0 && (gl.lookup d).isSome) = true := h
      rw [Bool.and_eq_true] at h'
      obtain ⟨hd0, h'⟩ := h'
      obtain ⟨⟨bb, k⟩, hl⟩ := Option.isSome_iff_exists.mp h'
      have hd0' : d ≠ 0 := fun h0 ↦ by simp [h0] at hd0
      obtain ⟨a, ha1, had, hM⟩ := hgl d bb k (lookup_memL hl)
      simp only [LinkW, hd0', ↓reduceIte] at hM
      refine ⟨slotW ws bb * ofK (g ^ k), by simp [BaseL, hl], fun u hu ↦ ?_⟩
      obtain ⟨p, x, hp, hx, hu⟩ := hu
      have hp' : p = ofK (g ^ a) := rd_getA hκ ha hfp (by norm_num) ha1 hp
      subst hp'
      have hx' : x = a + d := names_uniqL hx (names_shift (by simp) had)
      subst hx'
      rw [← hM]
      exact (ha.get _ _ hu).symm
    · have hqb : Nat.beq q 1 = false := by cases h1 : Nat.beq q 1 <;> simp_all [Nat.beq_eq]
      simp only [baseS, hqb, Bool.cond_false, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨h28, h⟩ := h
      obtain ⟨bb, hl⟩ := Option.isSome_iff_exists.mp h
      obtain ⟨p0, hrd, hM⟩ := hgp q d bb hl
      refine ⟨slotW ws bb, by simp [BaseL, hq, hl], fun u hu ↦ ?_⟩
      obtain ⟨p, x, hp, hx, hu⟩ := hu
      have hp' : p = p0 := rd_getA hκ ha hfp h28 hrd hp
      subst hp'
      rw [hM x hx]
      exact (ha.get _ _ hu).symm

/-- **A one-point run at a product written** (`ptLIs`): its cell written. -/
theorem rw_ptL {gl : List (ℕ × ℕ × ℕ)} {s : St} {ws : List E} {m : Mode.Mono} {q : CRun}
    (hq : ptLIs gl gp m q = true) (hc : SlotEqL gl gp s ws m.bs) (h : Mode.HW s m) :
    ∀ x, q.Set (slotW ws) x → WrK s.mem x := by
  unfold ptLIs at hq
  split at hq
  · rename_i c hmc
    obtain rfl := of_decide_eq_true hq
    intro x hx
    obtain ⟨ylo, yhi, j, h1, h2, h3, h4, rfl⟩ := runSet_iff.mp hx
    have e1 : ylo = 0 := by
      have := rep_const (w := slotW ws) (n := 0) (by rw [capE_eq]; norm_num)
      simp only [idxC] at h1
      rw [this, Option.some.injEq] at h1; exact h1.symm
    have e2 : yhi = 1 := by
      have := rep_const (w := slotW ws) (n := 1) (by rw [capE_eq]; norm_num)
      simp only [idxC] at h2
      rw [this, Option.some.injEq] at h2; exact h2.symm
    subst e1 e2
    obtain rfl : j = 0 := by omega
    obtain ⟨v, x, hv, hx, hw⟩ := h
    rw [monoVal_slotL hmc hc hv] at hx
    simpa [addressOfIndex] using wrk_names hx hw
  · cases hq

/-! ## A callee's caller cells, from the caller -/

/-- **Each base has its slot's word** (`BaseL`, the caller's cells linked, the words at arguments' cells `gp`). -/
def SlotGetL (gl : List (ℕ × ℕ × ℕ)) (gp : List ((ℕ × ℕ) × ℕ)) (s : St) (ws : List E) (bs : List (Mode.Base × ℕ)) :
    Prop :=
  ∀ b ∈ bs, ∃ w, BaseL gl gp ws b.1 = some w ∧ BaseVal s b.1 w

theorem bsVal_slotL' {gl : List (ℕ × ℕ × ℕ)} {s : St} {ws : List E} :
    ∀ (bs : List (Mode.Base × ℕ)) (cb : List (ℕ × ℕ)), bs.mapM (baseOfL gl gp) = some cb → SlotGetL gl gp s ws bs →
      BsVal s bs (prodW (slotW ws) cb)
  | [], cb, h, _ => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    simp [BsVal, prodW]
  | (b, e) :: bs, cb, h, hc => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨⟨k, e'⟩, hx, xs, hxs, rfl⟩ := h
    obtain ⟨rfl, hb⟩ := baseOfL_spec (ws := ws) hx
    obtain ⟨w0, hw0, hv0⟩ := hc (b, _) List.mem_cons_self
    rw [hb, Option.some.injEq] at hw0
    subst hw0
    exact ⟨_, _, hv0, bsVal_slotL' bs xs hxs (fun b hb ↦ hc b (List.mem_cons_of_mem _ hb)), rfl⟩

theorem monoVal_slotL' {gl : List (ℕ × ℕ × ℕ)} {s : St} {ws : List E} {m : Mode.Mono} {c : CCell}
    (hm : monoF (baseOfL gl gp) m = some c) (hc : SlotGetL gl gp s ws m.bs) : MonoVal s m (c.valW (slotW ws)) := by
  obtain ⟨h0, cb, hcb, rfl⟩ := monoF_specL hm
  refine ⟨_, bsVal_slotL' m.bs cb hcb hc, ?_⟩
  rw [h0]
  simp only [pow_zero, one_mul, CCell.valW, addressOfIndex]
  ring

/-- **A run of constant bounds, the caller's cells linked: its heap run's cells written, it is written.** -/
theorem slot_rwL {gl : List (ℕ × ℕ × ℕ)} {s : St} {ws : List E} {r : Mode.Rng} {q : CRun}
    (hr : rngL gl gp r = some q) (hn : numB r = true) (hc : SlotGetL gl gp s ws r.q.bs)
    (h : ∀ x, q.Set (slotW ws) x → WrK s.mem x) : RW s r := by
  obtain ⟨lo, hi, c, hlo, hhi, hmc, rfl⟩ := rngL_spec hr
  unfold numB at hn
  split at hn
  · rename_i a b ha hb
    rw [ha] at hlo
    rw [hb] at hhi
    simp only [idxL, idxX, Bool.cond_eq_ite, decide_eq_true_eq] at hlo hhi
    split_ifs at hlo with ha'
    split_ifs at hhi with hb'
    cases hlo
    cases hhi
    refine ⟨_, a, b, monoVal_slotL' hmc hc, by rw [ha]; rfl, by rw [hb]; rfl, fun j h1 h2 ↦ ?_⟩
    have hx := h _ ((runSet_const (q := ⟨⟨c.bases, c.off + r.d⟩, r.S, .num a, .num b⟩) rfl rfl ha' hb').mpr
      ⟨j, h1, h2, rfl⟩)
    obtain ⟨y, hy, hw⟩ := names_wrk hx
    refine ⟨y, ?_, hw⟩
    rwa [run_cell]
  · cases hn

/-- **A one-point run at a product, the caller's cells linked** (`ptLIs`): its heap run's cell written, the product is
written. -/
theorem slot_hwL {gl : List (ℕ × ℕ × ℕ)} {s : St} {ws : List E} {m : Mode.Mono} {q : CRun}
    (hq : ptLIs gl gp m q = true) (hc : SlotGetL gl gp s ws m.bs) (h : ∀ x, q.Set (slotW ws) x → WrK s.mem x) :
    Mode.HW s m := by
  unfold ptLIs at hq
  split at hq
  · rename_i c hmc
    obtain rfl := of_decide_eq_true hq
    have hx := h _ ((runSet_const (q := ⟨c, 1, .num 0, .num 1⟩) rfl rfl (by norm_num) (by norm_num)).mpr
      ⟨0, le_rfl, by norm_num, rfl⟩)
    obtain ⟨y, hy, hw⟩ := names_wrk hx
    refine ⟨_, y, monoVal_slotL' hmc hc, ?_, hw⟩
    simpa [addressOfIndex] using hy
  · cases hq

end

end LeanVM.Guest.CoreMode
