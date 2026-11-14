/-
  LeanVM.Guest.Backend.Sound.Atoms

  Placement of an atom is sound: the instructions it emits, or the pool it reads, give the atom's
  relation under the valuation by places.
-/

module

public import LeanVM.Guest.Backend.Sound.Flush

/-!
# An atom's instructions give its relation

`placeAtom_spec`: every success of `placeAtom a` emits straight-line instructions whose meaning,
with the pools of the scope, gives `a.Holds` under the final valuation by places `valP Γ.L fp F`.
One case an atom:

* a result taken from a pool (`const`, `add`, `mul`, `load` under `Kind.pooled`) is placed in the
  pooled cell, which holds the same relation on the same operand cells (`PoolOK`), or in a fresh
  cell the instruction writes;
* a `mul` of addresses keeps their shifts in the product's place (`Loc.shifted`);
* a copy the trace says is dropped is one between two values of one cell (checked);
* `assert_in_k` is a `JUMP` on the pooled zero, which checks its target cells and falls through;
* `KECCAK` reads and writes the runs its cells are checked to be;
* `addr` is the frame pointer's cell shifted to the run's first cell, the run's cells checked
  consecutive, so the words read through it are the run's.
-/

namespace LeanVM.Guest.Backend

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

variable {κ : ℕ} {Γ : Site κ} {fp : K} {F : Std.HashMap V Loc} {ctx : Ctx}

theorem isLazy_spec (v : V) (kind : Kind) : Spec Γ fp F ctx (isLazy v kind) (fun _ => True) := by
  intro st
  unfold isLazy
  straight

/-- A `JUMP` on a cell holding zero checks its target cells and falls through. -/
theorem emitJumpZero_spec {H : Prop} {st : St} {oc od of : ℕ} (hz : H → wd Γ.L fp oc = 0) :
    SpecAt (Γ := Γ) (fp := fp) (F := F) H ctx st (emitOp (.jump oc od of))
      (fun _ => IsInK (wd Γ.L fp od) ∧ IsInK (wd Γ.L fp of)) :=
  wp_bind.mpr (wp_modifyGet.mpr (wp_modify.mpr
    (Emits.jumpZero (fun h _ => hz h) rfl rfl ⟨rfl, rfl⟩ rfl)))

theorem char2 (a : E) : a + a = 0 := CharTwo.add_self_eq_zero a

variable {st : St}

theorem place_const (d : V) (c : E) :
    SpecAt (Γ := Γ) (fp := fp) (F := F) True ctx st (placeAtom (.const d c))
      (fun _ => (Atom.const d c).Holds Γ.L.read (valP Γ.L fp F)) := by
  unfold placeAtom
  dsimp only
  refine SpecAt.modify_bind quiet ?_
  refine SpecAt.bindTT (SpecAt.lastT (isLazy_spec _ _)) fun b _ => ?_
  split
  · refine SpecAt.lastH (pooled_spec
      (fun o => wd Γ.L fp o = Guest.word (limbsOf c).1 (limbsOf c).2) (fun _ => rfl)
      (fun sc o hp ho => hp.consts _ o ho) (fun o pc h => holds_set_const h)
      (fun sc o hp ho => hp.insertConst ho)) fun _ _ ⟨o, ho, hd⟩ => ?_
    show valP Γ.L fp F d = c
    rw [hd, ho, word_limbsOf]
  · refine SpecAt.call (cellAt_spec d) fun o _ => ?_
    refine SpecAt.call (emitOp_spec rfl) fun _ _ => ?_
    refine SpecAt.get_bind ?_
    have fin : F[d]? = some (.cell o) → (∃ pc, Holds Γ.L pc fp
        (Γ.R (.set o (.const (limbsOf c).1 (limbsOf c).2)))) → valP Γ.L fp F d = c :=
      fun hd hs => by rw [valP_of_cell hd, holds_set_const hs.choose_spec, word_limbsOf]
    split
    · exact SpecAt.learn rfl rfl ⟨rfl, rfl⟩
        (fun h hp => hp.insertConstIfNew (holds_set_const h.2.choose_spec))
        (fun h => fin h.1.2 h.2)
    · exact SpecAt.pure fun h _ _ => fin h.1.2 h.2

theorem place_add (d a b : V) :
    SpecAt (Γ := Γ) (fp := fp) (F := F) True ctx st (placeAtom (.add d a b))
      (fun _ => (Atom.add d a b).Holds Γ.L.read (valP Γ.L fp F)) := by
  unfold placeAtom
  dsimp only
  refine SpecAt.call (cellOf_spec a) fun la _ => ?_
  refine SpecAt.call (cellOf_spec b) fun lb _ => ?_
  refine SpecAt.bindTT (SpecAt.lastT (isLazy_spec _ _)) fun _ _ => ?_
  split
  · refine SpecAt.lastH (pooled_spec
      (fun o => wd Γ.L fp o = wd Γ.L fp la + wd Γ.L fp lb) (fun _ => rfl)
      (fun sc o hp ho => (hp.xors _ o ho).trans (wd_sorted_add la lb))
      (fun o pc h => holds_xor h)
      (fun sc o hp ho => hp.insertXor (ho.trans (wd_sorted_add la lb).symm)))
      fun _ h ⟨o, ho, hd⟩ => ?_
    show valP Γ.L fp F d = valP Γ.L fp F a + valP Γ.L fp F b
    rw [hd, ho, h.1.2, h.2]
  · refine SpecAt.call (cellAt_spec d) fun o _ => ?_
    exact SpecAt.lastH (emitOp_spec rfl) fun _ h hx => by
      show valP Γ.L fp F d = valP Γ.L fp F a + valP Γ.L fp F b
      rw [valP_of_cell h.2, holds_xor hx.choose_spec, h.1.1.2, h.1.2]

theorem place_mul (d a b : V) :
    SpecAt (Γ := Γ) (fp := fp) (F := F) True ctx st (placeAtom (.mul d a b))
      (fun _ => (Atom.mul d a b).Holds Γ.L.read (valP Γ.L fp F)) := by
  unfold placeAtom
  dsimp only
  refine SpecAt.bindTT (SpecAt.lastT (isLazy_spec _ _)) fun _ _ => ?_
  split
  · refine SpecAt.call (factor_spec a) fun ra _ => ?_
    refine SpecAt.call (factor_spec b) fun rb _ => ?_
    refine SpecAt.call (pooledCell_spec
      (fun o => wd Γ.L fp o = wd Γ.L fp ra.1 * wd Γ.L fp rb.1) (fun _ => rfl)
      (fun sc o hp ho => (hp.muls _ o ho).trans (wd_sorted_mul ra.1 rb.1))
      (fun o pc h => holds_mul h)
      (fun sc o hp ho => hp.insertMul (ho.trans (wd_sorted_mul ra.1 rb.1).symm)))
      fun o _ => ?_
    refine SpecAt.lastH (bindTo_spec d _) fun _ h hd => ?_
    show valP Γ.L fp F d = valP Γ.L fp F a * valP Γ.L fp F b
    rw [hd, h.1.1.2, h.1.2]
    have ho := h.2
    split
    · next he =>
      have he' : ra.2 + rb.2 = 0 := by simpa using he
      have ha : ra.2 = 0 := by omega
      have hb : rb.2 = 0 := by omega
      rw [ha, hb, addressOfIndex, pow_zero, ofK_one, mul_one, mul_one]
      exact ho
    · show wd Γ.L fp o * ofK (addressOfIndex (ra.2 + rb.2)) = _
      rw [ho, ← ofK_gpow_add]
      ring
  · refine SpecAt.call (cellOf_spec a) fun la _ => ?_
    refine SpecAt.call (cellOf_spec b) fun lb _ => ?_
    refine SpecAt.call (cellAt_spec d) fun o _ => ?_
    exact SpecAt.lastH (emitOp_spec rfl) fun _ h hx => by
      show valP Γ.L fp F d = valP Γ.L fp F a * valP Γ.L fp F b
      rw [valP_of_cell h.2, holds_mul hx.choose_spec, h.1.1.2, h.1.2]

theorem place_copy (d s : V) :
    SpecAt (Γ := Γ) (fp := fp) (F := F) True ctx st (placeAtom (.copy d s))
      (fun _ => (Atom.copy d s).Holds Γ.L.read (valP Γ.L fp F)) := by
  unfold placeAtom
  dsimp only
  refine SpecAt.call (cellOf_spec s) fun ls _ => ?_
  refine SpecAt.get_bind ?_
  split
  · refine SpecAt.call (cellAt_spec d) fun ld _ => ?_
    split
    · exact SpecAt.fail_bind
    · next hne =>
      exact SpecAt.pure fun h _ _ => by
        have hl : ld = ls := by simpa using hne
        show valP Γ.L fp F d = valP Γ.L fp F s
        rw [valP_of_cell h.2, hl, h.1.2]
  · refine SpecAt.call oneCell_spec fun one _ => ?_
    refine SpecAt.call (cellAt_spec d) fun ld _ => ?_
    exact SpecAt.lastH (emitOp_spec rfl) fun _ h hx => by
      show valP Γ.L fp F d = valP Γ.L fp F s
      rw [valP_of_cell h.2, holds_mul hx.choose_spec, h.1.2, mul_one, h.1.1.2]

theorem place_load (d p : V) (off : ℕ) :
    SpecAt (Γ := Γ) (fp := fp) (F := F) True ctx st (placeAtom (.load d p off))
      (fun _ => (Atom.load d p off).Holds Γ.L.read (valP Γ.L fp F)) := by
  unfold placeAtom
  dsimp only
  refine SpecAt.bindTT (SpecAt.lastT (isLazy_spec _ _)) fun _ _ => ?_
  split
  · refine SpecAt.call (pointer_spec p off) fun r _ => ?_
    obtain ⟨ptr, o2⟩ := r
    dsimp only
    refine SpecAt.lastH (pooled_spec (fun o => IsInK (wd Γ.L fp ptr) ∧
        Γ.L.read ((wd Γ.L fp ptr).limb 0 * addressOfIndex o2) = some (wd Γ.L fp o))
      (fun _ => rfl) (fun sc o hp ho => hp.loads (ptr, o2) o ho) (fun o pc h => holds_deref h)
      (fun sc o hp ho => hp.insertLoad (k := (ptr, o2)) ho)) fun _ h ⟨o, ho, hd⟩ => ?_
    show LoadHolds Γ.L.read (valP Γ.L fp F p) off (valP Γ.L fp F d)
    obtain ⟨hK, he⟩ := h.2 ho.1
    exact ⟨hK, by rw [he, hd]; exact ho.2⟩
  · refine SpecAt.call (cellOf_spec d) fun o _ => ?_
    refine SpecAt.call (pointer_spec p off) fun r _ => ?_
    obtain ⟨ptr, o2⟩ := r
    dsimp only
    refine SpecAt.lastH (emitDeref_spec ptr o2 o) fun _ h hx => ?_
    show LoadHolds Γ.L.read (valP Γ.L fp F p) off (valP Γ.L fp F d)
    obtain ⟨hK, he⟩ := h.2 hx.1
    exact ⟨hK, by rw [he, ← h.1.2]; exact hx.2⟩

theorem place_assertEq (a b : V) :
    SpecAt (Γ := Γ) (fp := fp) (F := F) True ctx st (placeAtom (.assertEq a b))
      (fun _ => (Atom.assertEq a b).Holds Γ.L.read (valP Γ.L fp F)) := by
  unfold placeAtom
  dsimp only
  refine SpecAt.call (cellOf_spec a) fun la _ => ?_
  refine SpecAt.call (cellOf_spec b) fun lb _ => ?_
  refine SpecAt.call oneCell_spec fun one _ => ?_
  exact SpecAt.lastH (emitOp_spec rfl) fun _ h hx => by
    show valP Γ.L fp F a + valP Γ.L fp F b = 0
    have := holds_mul hx.choose_spec
    rw [h.2, mul_one, h.1.1.2, h.1.2] at this
    rw [this]
    exact char2 _

theorem place_assertNe (x inv p : V) :
    SpecAt (Γ := Γ) (fp := fp) (F := F) True ctx st (placeAtom (.assertNe x inv p))
      (fun _ => (Atom.assertNe x inv p).Holds Γ.L.read (valP Γ.L fp F)) := by
  unfold placeAtom
  dsimp only
  refine SpecAt.call (cellOf_spec x) fun lx _ => ?_
  refine SpecAt.call (cellOf_spec inv) fun li _ => ?_
  refine SpecAt.call (cellAt_spec p) fun lp _ => ?_
  refine SpecAt.call (emitOp_spec rfl) fun _ _ => ?_
  exact SpecAt.lastH (emitOp_spec rfl) fun _ h hs => by
    show valP Γ.L fp F p = valP Γ.L fp F x * valP Γ.L fp F inv ∧ valP Γ.L fp F p = 1
    obtain ⟨⟨⟨⟨-, h1⟩, h2⟩, h3⟩, h4⟩ := h
    rw [valP_of_cell h3]
    exact ⟨by rw [holds_mul h4.choose_spec, h1, h2],
      (holds_set_const hs.choose_spec).trans word_one⟩

theorem place_rangeCheck (x y t1 t2 k : V) :
    SpecAt (Γ := Γ) (fp := fp) (F := F) True ctx st (placeAtom (.rangeCheck x y t1 t2 k))
      (fun _ => (Atom.rangeCheck x y t1 t2 k).Holds Γ.L.read (valP Γ.L fp F)) := by
  unfold placeAtom
  dsimp only
  refine SpecAt.call (cellOf_spec k) fun lk _ => ?_
  refine SpecAt.call (cellOf_spec x) fun lx _ => ?_
  refine SpecAt.call (cellAt_spec y) fun ly _ => ?_
  refine SpecAt.call (cellAt_spec t1) fun l1 _ => ?_
  refine SpecAt.call (emitDeref_spec lx 0 l1) fun _ _ => ?_
  refine SpecAt.call (emitOp_spec rfl) fun _ _ => ?_
  refine SpecAt.call (cellAt_spec t2) fun l2 _ => ?_
  exact SpecAt.lastH (emitDeref_spec ly 0 l2) fun _ h h8 => by
    obtain ⟨⟨⟨⟨⟨⟨⟨-, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
    show LoadHolds Γ.L.read (valP Γ.L fp F x) 0 (valP Γ.L fp F t1) ∧
      valP Γ.L fp F k = valP Γ.L fp F x * valP Γ.L fp F y ∧
      LoadHolds Γ.L.read (valP Γ.L fp F y) 0 (valP Γ.L fp F t2)
    rw [← h1, ← h2, valP_of_cell h3, valP_of_cell h4, valP_of_cell h7]
    exact ⟨h5, holds_mul h6.choose_spec, h8⟩

theorem place_assertInK (a b : V) :
    SpecAt (Γ := Γ) (fp := fp) (F := F) True ctx st (placeAtom (.assertInK a b))
      (fun _ => (Atom.assertInK a b).Holds Γ.L.read (valP Γ.L fp F)) := by
  unfold placeAtom
  dsimp only
  refine SpecAt.call (cellOf_spec a) fun la _ => ?_
  refine SpecAt.call (cellOf_spec b) fun lb _ => ?_
  refine SpecAt.call zeroCell_spec fun z _ => ?_
  exact (emitJumpZero_spec (fun h => h.2)).mono fun _ h hj => by
    show IsInK (valP Γ.L fp F a) ∧ IsInK (valP Γ.L fp F b)
    rw [← h.1.1.2, ← h.1.2]
    exact hj

theorem place_hint (h : Hint) :
    SpecAt (Γ := Γ) (fp := fp) (F := F) True ctx st (placeAtom (.hint h))
      (fun _ => (Atom.hint h).Holds Γ.L.read (valP Γ.L fp F)) := by
  unfold placeAtom
  exact SpecAt.lastT (placeHint_spec h)

theorem place_touch (t p : V) :
    SpecAt (Γ := Γ) (fp := fp) (F := F) True ctx st (placeAtom (.touch t p))
      (fun _ => (Atom.touch t p).Holds Γ.L.read (valP Γ.L fp F)) := by
  unfold placeAtom
  dsimp only
  refine SpecAt.call (cellOf_spec p) fun lp _ => ?_
  refine SpecAt.call (cellAt_spec t) fun lt _ => ?_
  exact SpecAt.lastH (emitDeref_spec lp 0 lt) fun _ h hx => by
    show LoadHolds Γ.L.read (valP Γ.L fp F p) 0 (valP Γ.L fp F t)
    rw [← h.1.2, valP_of_cell h.2]
    exact hx

/-! ## Runs of cells -/

theorem all_zipIdx : ∀ {cs : List ℕ} {base n : ℕ},
    ((cs.zipIdx n).all fun (c, k) => c == base + k) = true →
      ∀ k (hk : k < cs.length), cs[k] = base + (n + k)
  | [], _, _, _, _, hk => absurd hk (Nat.not_lt_zero _)
  | c :: cs, base, n, h, k, hk => by
      rw [List.zipIdx_cons, List.all_cons, Bool.and_eq_true] at h
      cases k with
      | zero => simpa using h.1
      | succ k =>
          have := all_zipIdx h.2 k (Nat.lt_of_succ_lt_succ hk)
          simp only [List.getElem_cons_succ, this]
          omega

/-- Cells checked consecutive from `base` are `base`, `base + 1`, …. -/
theorem consecutiveFrom_getElem {base : ℕ} {cs : List ℕ} (h : consecutiveFrom base cs = true)
    (k : ℕ) (hk : k < cs.length) : cs[k] = base + k := by
  have := all_zipIdx (n := 0) h k hk
  simpa using this

theorem forall₂_getElem {α β : Type} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) :
    l₁.length = l₂.length ∧ ∀ k (h1 : k < l₁.length) (h2 : k < l₂.length), R l₁[k] l₂[k] := by
  induction h with
  | nil => exact ⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | cons hr _ ih =>
      refine ⟨by simp [ih.1], fun k h1 h2 => ?_⟩
      cases k with
      | zero => exact hr
      | succ k => exact ih.2 k (Nat.lt_of_succ_lt_succ h1) (Nat.lt_of_succ_lt_succ h2)

/-! ## `addr` -/

/-- A pointer worth `fp · g^base` is the address of a run whose cells are consecutive from
`base`: a word read through it is the run's. -/
theorem frameAddr_holds {p : V} {run : List V} {cells : List Cell} {base : ℕ}
    (hp : valP Γ.L fp F p = ofK fp * ofK (addressOfIndex base))
    (hrun : List.Forall₂ (fun v n => F[v]? = some (.cell n)) run cells)
    (hcons : consecutiveFrom base cells = true) :
    (Atom.frameAddr p run).Holds Γ.L.read (valP Γ.L fp F) := by
  obtain ⟨hlen, hget⟩ := forall₂_getElem hrun
  have hp' : valP Γ.L fp F p = ofK (fp * addressOfIndex base) := by rw [hp, ofK_mul]
  refine ⟨by rw [hp']; exact isInK_ofK _, fun k hk w hr => ?_⟩
  have hk' : k < cells.length := hlen ▸ hk
  rw [valP_of_cell (hget k hk hk'), consecutiveFrom_getElem hcons k hk']
  rw [hp'] at hr
  have he : (ofK (fp * addressOfIndex base)).limb 0 * addressOfIndex k =
      fp * addressOfIndex (base + k) := by
    simp [addressOfIndex, pow_add, mul_assoc]
  rw [he] at hr
  exact (wd_of_read hr).symm

/-! ## `KECCAK` -/

theorem getD_map_wd {L : MemoryImage κ} (cs : List Cell) {i : ℕ} (hi : i < cs.length) :
    (cs.map (wd L fp)).getD i 0 = wd L fp (cs.getD i 0) := by
  simp [List.getD_eq_getElem?_getD, hi]

/-- The cells a `KECCAK` reads are the thirteen of its operand, the runs from `tail` and `cap`
checked consecutive. -/
theorem keccakInOff_cells {cs : List Cell} (h13 : cs.length = 13)
    (ht : consecutiveFrom (cs.getD 4 0) ((cs.drop 4).take 4) = true)
    (hc : consecutiveFrom (cs.getD 9 0) ((cs.drop 9).take 4) = true) (i : ℕ) (hi : i < 13) :
    keccakInOff (cs.getD 0 0) (cs.getD 1 0) (cs.getD 2 0) (cs.getD 3 0) (cs.getD 4 0)
      (cs.getD 8 0) (cs.getD 9 0) i = cs.getD i 0 := by
  have hT : ∀ j < 4, cs.getD (4 + j) 0 = cs.getD 4 0 + j := fun j hj => by
    have := consecutiveFrom_getElem ht j (by simp [h13]; omega)
    simpa [List.getD_eq_getElem?_getD, h13, hj, show 4 + j < 13 by omega] using this
  have hC : ∀ j < 4, cs.getD (9 + j) 0 = cs.getD 9 0 + j := fun j hj => by
    have := consecutiveFrom_getElem hc j (by simp [h13]; omega)
    simpa [List.getD_eq_getElem?_getD, h13, hj, show 9 + j < 13 by omega] using this
  unfold keccakInOff
  by_cases h0 : i = 0
  · simp [h0]
  by_cases h1 : i = 1
  · simp [h1]
  by_cases h2 : i = 2
  · simp [h2]
  by_cases h3 : i = 3
  · simp [h3]
  by_cases h8 : i < 8
  · simp only [h0, h1, h2, h3, h8, ↓reduceIte]
    rw [← hT (i - 4) (by omega)]
    congr 1
    omega
  by_cases h8' : i = 8
  · simp [h8']
  simp only [h0, h1, h2, h3, h8, h8', ↓reduceIte]
  rw [← hC (i - 9) (by omega)]
  congr 1
  omega

/-- A `KECCAK` on the cells of the atom's values gives the atom's relation. -/
theorem keccak_holds {ins outs : List V} {cs los : List Cell} {out pc : ℕ} {inOdd outOdd : Bool}
    (hins : List.Forall₂ (fun v n => wd Γ.L fp n = valP Γ.L fp F v) ins cs)
    (houts : List.Forall₂ (fun v n => F[v]? = some (.cell n)) outs los)
    (h13 : cs.length = 13)
    (ht : consecutiveFrom (cs.getD 4 0) ((cs.drop 4).take 4) = true)
    (hc : consecutiveFrom (cs.getD 9 0) ((cs.drop 9).take 4) = true)
    (ho : consecutiveFrom out los = true)
    (hl : los.length = 1 ∨ los.length = 2 ∨ los.length = 13)
    (hk : Holds Γ.L pc fp (.keccak (cs.getD 0 0) (cs.getD 1 0) (cs.getD 2 0) (cs.getD 3 0)
      (cs.getD 4 0) (cs.getD 8 0) (cs.getD 9 0) out inOdd outOdd
      (if los.length == 1 then .one else if los.length == 2 then .two else .all))) :
    (Atom.keccak ins outs inOdd outOdd).Holds Γ.L.read (valP Γ.L fp F) := by
  obtain ⟨input, output, hin, hout, hrel⟩ := hk
  have hilen := (forall₂_getElem hins).1
  obtain ⟨holen, hoget⟩ := forall₂_getElem houts
  have hcount : los.length = (if los.length == 1 then KeccakOutputCells.one
      else if los.length == 2 then .two else .all).cellCount := by
    rcases hl with h | h | h <;> simp [h, KeccakOutputCells.cellCount]
  have hinput : input = cells13 (ins.map (valP Γ.L fp F)) := by
    funext c
    have h := wd_of_read (hin c)
    rw [keccakInOff_cells h13 ht hc c.val c.isLt] at h
    rw [cells13, ← forall₂_cells hins, getD_map_wd cs (by rw [h13]; exact c.isLt)]
    exact h.symm
  refine ⟨by rw [hilen, h13], _, by rw [holen]; exact hcount, fun c hcc => ?_⟩
  rw [← hinput, ← hrel c hcc]
  have hcl : c.val < los.length := by rw [hcount]; exact hcc
  have hco : c.val < outs.length := by rw [holen]; exact hcl
  rw [cells13, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hco,
    Option.map_some, Option.getD_some, valP_of_cell (hoget c.val hco hcl),
    consecutiveFrom_getElem ho c.val hcl]
  exact wd_of_read (hout c hcc)

theorem place_keccak (ins outs : List V) (inOdd outOdd : Bool) :
    SpecAt (Γ := Γ) (fp := fp) (F := F) True ctx st (placeAtom (.keccak ins outs inOdd outOdd))
      (fun _ => (Atom.keccak ins outs inOdd outOdd).Holds Γ.L.read (valP Γ.L fp F)) := by
  unfold placeAtom
  dsimp only
  refine SpecAt.call (mapM_spec cellOf_spec ins) fun cs _ => ?_
  refine SpecAt.call (mapM_spec cellAt_spec outs) fun los _ => ?_
  split
  · next out hout =>
    refine SpecAt.guard fun hc => ?_
    simp only [Bool.not_eq_true, Bool.not_eq_false', Bool.and_eq_true, Bool.or_eq_true,
      beq_iff_eq] at hc
    exact SpecAt.lastH (emitOp_spec rfl) fun _ h hk =>
      keccak_holds h.1.2 h.2 hc.1.1.1.1 hc.1.1.1.2 hc.1.1.2 hc.1.2 (or_assoc.mp hc.2) hk.choose_spec
  · exact SpecAt.fail

section

variable (hmain : ctx.isMain = true → fp = 1)

include hmain in
/-- The cell `isSelfFp` accepts holds the frame pointer. -/
theorem isSelfFp_spec (n : Cell) :
    Spec Γ fp F ctx (isSelfFp n) (fun b => b = true → wd Γ.L fp n = ofK fp) := by
  intro st
  unfold isSelfFp
  refine SpecAt.read_bind ?_
  by_cases hm : ctx.isMain = true
  · simp only [hm, ↓reduceIte]
    refine SpecAt.get_bind (SpecAt.withPool ?_)
    exact SpecAt.pure fun h _ _ hb => by
      rw [h.2.consts (1, 0) n (eq_of_beq hb), word_one, hmain hm]
      exact ofK_one.symm
  · simp only [hm, Bool.false_eq_true, ↓reduceIte]
    refine SpecAt.get_bind (SpecAt.withPool ?_)
    exact SpecAt.pure fun h _ _ hb => h.2.selfFp n (eq_of_beq hb)

include hmain in
theorem place_frameAddr (p : V) (run : List V) :
    SpecAt (Γ := Γ) (fp := fp) (F := F) True ctx st (placeAtom (.frameAddr p run))
      (fun _ => (Atom.frameAddr p run).Holds Γ.L.read (valP Γ.L fp F)) := by
  unfold placeAtom
  dsimp only
  refine SpecAt.bindTT (SpecAt.lastT (isLazy_spec _ _)) fun _ _ => ?_
  split
  · split
    · next r0 hr0 =>
      refine SpecAt.call (cellAt_spec r0) fun base _ => ?_
      refine SpecAt.call (mapM_spec cellAt_spec run) fun cells _ => ?_
      refine SpecAt.guard fun hc => ?_
      refine SpecAt.call (selfFp_spec hmain) fun sf _ => ?_
      exact SpecAt.lastH (bindTo_spec p _) fun _ h hb =>
        frameAddr_holds (by rw [hb]; show wd Γ.L fp sf * _ = _; rw [h.2]) h.1.2
          (by simpa using hc)
    · exact SpecAt.fail
  · refine SpecAt.get_bind ?_
    split
    · next c exp hsh =>
      refine SpecAt.get_bind (SpecAt.withSub ?_)
      split
      · next n e hn =>
        refine SpecAt.call (isSelfFp_spec hmain n) fun b _ => ?_
        refine SpecAt.guard fun hb => ?_
        refine SpecAt.call (mapM_spec cellAt_spec run) fun cells _ => ?_
        refine SpecAt.guard fun hc => ?_
        refine SpecAt.call (materialize_spec n (e + exp)) fun o _ => ?_
        exact SpecAt.lastH (bindTo_spec p _) fun _ h hb' =>
          frameAddr_holds (by
            rw [hb']
            show wd Γ.L fp o = _
            rw [h.2, h.1.1.2 (by simpa using hb)]) h.1.2 (by simpa using hc)
      · exact SpecAt.fail
    · exact SpecAt.fail

include hmain in
/-- **Placement of an atom is sound**: its instructions, with the pools, give its relation under
the valuation by places. -/
theorem placeAtom_spec (a : Atom) :
    Spec Γ fp F ctx (placeAtom a) (fun _ => a.Holds Γ.L.read (valP Γ.L fp F)) := by
  intro st
  cases a with
  | const d c => exact place_const d c
  | add d a b => exact place_add d a b
  | mul d a b => exact place_mul d a b
  | copy d s => exact place_copy d s
  | load d p off => exact place_load d p off
  | assertEq a b => exact place_assertEq a b
  | assertNe x inv p => exact place_assertNe x inv p
  | rangeCheck x y t1 t2 k => exact place_rangeCheck x y t1 t2 k
  | assertInK a b => exact place_assertInK a b
  | keccak ins outs inOdd outOdd => exact place_keccak ins outs inOdd outOdd
  | frameAddr p run => exact place_frameAddr hmain p run
  | hint h => exact place_hint h
  | touch t p => exact place_touch t p

end

end
end LeanVM.Guest.Backend
