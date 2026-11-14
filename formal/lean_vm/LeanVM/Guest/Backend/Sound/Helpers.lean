/-
  LeanVM.Guest.Backend.Sound.Helpers

  What each helper of the placement walk guarantees: the cell it returns holds the word meant.
-/

module

public import LeanVM.Guest.Backend.Sound.Walk
public import LeanVM.Guest.Backend.Sound.Spec

/-!
# The helpers of the placement walk

One specification (`Spec`) a helper of `Place`: every success emits straight-line instructions
only, keeps the pools true (`PoolOK`), and returns a cell whose word is the one the caller wants.

* `constCell k` returns a cell holding the word of `k`; `mulCell a b` one holding the product;
  `selfFp` one holding the frame pointer; `materialize c exp` one holding `fp[c] · g^exp`;
* `cellOf v`, `cellAt v` return a cell holding `v`'s word under the final places; `factor`,
  `pointer` the cell and the shift a `DEREF` folds into its immediate;
* a pool hit emits nothing and is justified by `PoolOK`; a miss emits the instruction and the
  pool learns it (`PoolOK.insert*`).
-/

namespace LeanVM.Guest.Backend

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

variable {κ : ℕ} {Γ : Site κ} {fp : K} {F : Std.HashMap V Loc} {ctx : Ctx} {α : Type}

/-! ## Pools learn -/

section Pool

variable {L : MemoryImage κ} {sc : Scope}

theorem PoolOK.insertConst (h : PoolOK L fp sc) {k : ℕ × ℕ} {o : Cell}
    (ho : wd L fp o = Guest.word k.1 k.2) :
    PoolOK L fp { sc with consts := sc.consts.insert k o } := by
  refine { h with consts := fun k' o' hk => ?_ }
  rw [Std.TreeMap.get?_eq_getElem?, Std.TreeMap.getElem?_insert] at hk
  split at hk
  · next heq =>
    cases hk
    rw [← cmp2_eq_iff.mp heq]
    exact ho
  · exact h.consts k' o' hk

theorem PoolOK.insertConstIfNew (h : PoolOK L fp sc) {k : ℕ × ℕ} {o : Cell}
    (ho : wd L fp o = Guest.word k.1 k.2) :
    PoolOK L fp { sc with consts := sc.consts.insertIfNew k o } := by
  refine { h with consts := fun k' o' hk => ?_ }
  rw [Std.TreeMap.get?_eq_getElem?, Std.TreeMap.getElem?_insertIfNew] at hk
  split at hk
  · next heq =>
    cases hk
    rw [← cmp2_eq_iff.mp heq.1]
    exact ho
  · exact h.consts k' o' hk

theorem PoolOK.insertXor (h : PoolOK L fp sc) {k : ℕ × ℕ} {o : Cell}
    (ho : wd L fp o = wd L fp k.1 + wd L fp k.2) :
    PoolOK L fp { sc with xors := sc.xors.insert k o } := by
  refine { h with xors := fun k' o' hk => ?_ }
  rw [Std.TreeMap.get?_eq_getElem?, Std.TreeMap.getElem?_insert] at hk
  split at hk
  · next heq =>
    cases hk
    rw [← cmp2_eq_iff.mp heq]
    exact ho
  · exact h.xors k' o' hk

theorem PoolOK.insertMul (h : PoolOK L fp sc) {k : ℕ × ℕ} {o : Cell}
    (ho : wd L fp o = wd L fp k.1 * wd L fp k.2) :
    PoolOK L fp { sc with muls := sc.muls.insert k o } := by
  refine { h with muls := fun k' o' hk => ?_ }
  rw [Std.TreeMap.get?_eq_getElem?, Std.TreeMap.getElem?_insert] at hk
  split at hk
  · next heq =>
    cases hk
    rw [← cmp2_eq_iff.mp heq]
    exact ho
  · exact h.muls k' o' hk

theorem PoolOK.insertLoad (h : PoolOK L fp sc) {k : ℕ × ℕ} {o : Cell}
    (ho : IsInK (wd L fp k.1) ∧
      L.read ((wd L fp k.1).limb 0 * addressOfIndex k.2) = some (wd L fp o)) :
    PoolOK L fp { sc with loads := sc.loads.insertIfNew k o } := by
  refine { h with loads := fun k' o' hk => ?_ }
  rw [Std.TreeMap.get?_eq_getElem?, Std.TreeMap.getElem?_insertIfNew] at hk
  split at hk
  · next heq =>
    cases hk
    rw [← cmp2_eq_iff.mp heq.1]
    exact ho
  · exact h.loads k' o' hk

theorem PoolOK.insertMats (h : PoolOK L fp sc) {c : ℕ} {l : List (ℕ × Cell)}
    (hl : ∀ p ∈ l, wd L fp p.2 = wd L fp c * ofK (addressOfIndex p.1)) :
    PoolOK L fp { sc with mats := sc.mats.insert c l } := by
  refine { h with mats := fun c' l' hk => ?_ }
  rw [Std.TreeMap.get?_eq_getElem?, Std.TreeMap.getElem?_insert] at hk
  split at hk
  · next heq =>
    cases hk
    rw [← Std.LawfulEqCmp.compare_eq_iff_eq.mp heq]
    exact hl
  · exact h.mats c' l' hk

theorem PoolOK.setSelfFp (h : PoolOK L fp sc) {o : Cell} (ho : wd L fp o = ofK fp) :
    PoolOK L fp { sc with selfFp := some o } :=
  { h with selfFp := fun o' ho' => by cases ho'; exact ho }

theorem wd_sorted_mul (a b : ℕ) :
    wd L fp (sorted a b).1 * wd L fp (sorted a b).2 = wd L fp a * wd L fp b := by
  unfold sorted
  rcases Nat.le_total a b with h | h
  · rw [Nat.min_eq_left h, Nat.max_eq_right h]
  · rw [Nat.min_eq_right h, Nat.max_eq_left h, mul_comm]

theorem wd_sorted_add (a b : ℕ) :
    wd L fp (sorted a b).1 + wd L fp (sorted a b).2 = wd L fp a + wd L fp b := by
  unfold sorted
  rcases Nat.le_total a b with h | h
  · rw [Nat.min_eq_left h, Nat.max_eq_right h]
  · rw [Nat.min_eq_right h, Nat.max_eq_left h, add_comm]

end Pool

/-! ## Primitives -/

/-- The state changes in nothing a proof reads. -/
macro "quiet" : term => `(Emits.frame rfl rfl ⟨rfl, rfl⟩ fun _ _ h => h)

theorem fresh_spec : Spec Γ fp F ctx fresh (fun _ => True) :=
  fun _ => SpecAt.modifyGet quiet

theorem pushHint_spec (h : LHint) : Spec Γ fp F ctx (pushHint h) (fun _ => True) :=
  fun _ => SpecAt.modify quiet

theorem takeHints_spec : Spec Γ fp F ctx takeHints (fun _ => True) :=
  fun _ => SpecAt.modifyGet quiet

theorem advance_spec : Spec Γ fp F ctx advance (fun _ => True) :=
  fun _ => SpecAt.modify quiet

theorem endStmt_spec : Spec Γ fp F ctx endStmt (fun _ => True) :=
  fun _ => SpecAt.modify quiet

/-- One straight-line instruction: it holds. -/
theorem emitOp_spec {o : LOp} (hj : o.isJump = false) :
    Spec Γ fp F ctx (emitOp o) (fun _ => ∃ pc, Holds Γ.L pc fp (Γ.R o)) :=
  fun _ => wp_bind.mpr (wp_modifyGet.mpr (wp_modify.mpr (Emits.op hj rfl rfl ⟨rfl, rfl⟩ rfl)))

/-- A value is placed once. -/
theorem bindTo_spec (v : V) (l : Loc) :
    Spec Γ fp F ctx (bindTo v l) (fun _ => valP Γ.L fp F v = locVal Γ.L fp l) := by
  intro st
  unfold bindTo
  refine SpecAt.get_bind (SpecAt.guard fun hc => ?_)
  exact SpecAt.modify (Emits.place (by simpa using hc) rfl rfl ⟨rfl, rfl⟩ rfl)

/-- The cell of a value held in one is its final place. -/
theorem cellAt_spec (v : V) : Spec Γ fp F ctx (cellAt v) (fun n => F[v]? = some (.cell n)) := by
  intro st
  unfold cellAt
  refine SpecAt.get_bind ?_
  split
  · next n hn => exact SpecAt.pure fun _ hF _ => hF v _ hn
  · exact SpecAt.fail

theorem valP_of_cell {L : MemoryImage κ} {v : V} {n : Cell} (h : F[v]? = some (.cell n)) :
    valP L fp F v = wd L fp n := by
  rw [valP, h]
  rfl

/-- A pooled constant's cell holds the constant. -/
theorem constCell_spec (k : ℕ × ℕ) :
    Spec Γ fp F ctx (constCell k) (fun o => wd Γ.L fp o = Guest.word k.1 k.2) := by
  intro st
  unfold constCell
  refine SpecAt.get_bind ?_
  split
  · next o ho => exact SpecAt.pure fun _ _ hp => hp.consts k o ho
  · refine SpecAt.call fresh_spec fun o _ => ?_
    refine SpecAt.call (emitOp_spec rfl) fun _ st2 => ?_
    refine SpecAt.modify_bind (Emits.frame rfl rfl ⟨rfl, rfl⟩ fun h _ hp =>
      hp.insertConst (holds_set_const h.2.choose_spec)) ?_
    exact SpecAt.pure fun h _ _ => holds_set_const h.1.2.choose_spec

theorem oneCell_spec : Spec Γ fp F ctx oneCell (fun o => wd Γ.L fp o = 1) :=
  fun st => (constCell_spec (1, 0) st).mono fun _ _ h => h.trans word_one

theorem zeroCell_spec : Spec Γ fp F ctx zeroCell (fun o => wd Γ.L fp o = 0) :=
  fun st => (constCell_spec (0, 0) st).mono fun _ _ h => h.trans word_zero

/-- A pooled product's cell holds the product. -/
theorem mulCell_spec (a b : Cell) :
    Spec Γ fp F ctx (mulCell a b) (fun o => wd Γ.L fp o = wd Γ.L fp a * wd Γ.L fp b) := by
  intro st
  unfold mulCell
  refine SpecAt.get_bind ?_
  split
  · next o ho => exact SpecAt.pure fun _ _ hp => (hp.muls _ o ho).trans (wd_sorted_mul a b)
  · refine SpecAt.call fresh_spec fun o _ => ?_
    refine SpecAt.call (emitOp_spec rfl) fun _ _ => ?_
    refine SpecAt.modify_bind (Emits.frame rfl rfl ⟨rfl, rfl⟩ fun h _ hp =>
      hp.insertMul ((holds_mul h.2.choose_spec).trans (wd_sorted_mul a b).symm)) ?_
    exact SpecAt.pure fun h _ _ => holds_mul h.1.2.choose_spec

/-- A `DEREF` of a cell reads through its pointer, and the scope remembers the load. -/
theorem emitDeref_spec (ptr off dst : ℕ) :
    Spec Γ fp F ctx (emitDeref ptr off dst) (fun _ => IsInK (wd Γ.L fp ptr) ∧
      Γ.L.read ((wd Γ.L fp ptr).limb 0 * addressOfIndex off) = some (wd Γ.L fp dst)) := by
  intro st
  unfold emitDeref
  refine SpecAt.call (emitOp_spec rfl) fun _ st' => SpecAt.modify ?_
  have e : Emits Γ fp F (True ∧ ∃ pc, Holds Γ.L pc fp (Γ.R (.deref ptr off dst .cell))) st'
      { st' with scope.loads := st'.scope.loads.insertIfNew (ptr, off) dst } True :=
    Emits.frame rfl rfl ⟨rfl, rfl⟩ fun h _ hp =>
      hp.insertLoad (k := (ptr, off)) (holds_deref h.2.choose_spec)
  exact e.imp fun h _ _ _ => holds_deref h.2.choose_spec

/-- The cell `selfFp` returns holds the frame pointer; `main`'s frame is at `1`. -/
theorem selfFp_spec (hmain : ctx.isMain = true → fp = 1) :
    Spec Γ fp F ctx selfFp (fun o => wd Γ.L fp o = ofK fp) := by
  intro st
  unfold selfFp
  refine SpecAt.read_bind ?_
  by_cases hm : ctx.isMain = true
  · simp only [hm, ↓reduceIte]
    exact (oneCell_spec st).mono fun _ _ h => by rw [h, hmain hm]; exact ofK_one.symm
  · simp only [hm, Bool.false_eq_true, ↓reduceIte]
    refine SpecAt.get_bind ?_
    split
    · next o ho => exact SpecAt.pure fun _ _ hp => hp.selfFp o ho
    · refine SpecAt.call fresh_spec fun q _ => ?_
      refine SpecAt.call (pushHint_spec _) fun _ _ => ?_
      refine SpecAt.call (emitOp_spec rfl) fun _ _ => ?_
      refine SpecAt.call fresh_spec fun o _ => ?_
      refine SpecAt.call (emitOp_spec rfl) fun _ _ => ?_
      have key : ∀ {pc pc' : ℕ}, Holds Γ.L pc fp (Γ.R (.deref q 0 0 .fp)) →
          Holds Γ.L pc' fp (Γ.R (.deref q 0 o .cell)) → wd Γ.L fp o = ofK fp := fun h3 h5 =>
        Option.some.inj ((holds_deref h5).2.symm.trans (holds_deref_fp h3).2)
      refine SpecAt.modify_bind (Emits.frame rfl rfl ⟨rfl, rfl⟩ fun h _ hp =>
        hp.setSelfFp (key h.1.1.2.choose_spec h.2.choose_spec)) ?_
      exact SpecAt.pure fun h _ _ => key h.1.1.1.2.choose_spec h.1.2.choose_spec

/-- A fold that keeps its best candidate returns the initial one or a member that passed. -/
theorem foldl_pick {β : Type} (f : Option β → β → Option β) (G : β → Prop)
    (hf : ∀ best a, f best a = best ∨ (f best a = some a ∧ G a)) :
    ∀ (l : List β) (init : Option β) (r : β), l.foldl f init = some r →
      init = some r ∨ (r ∈ l ∧ G r)
  | [], _, _, h => Or.inl h
  | a :: l, init, r, h => by
      rw [List.foldl_cons] at h
      rcases foldl_pick f G hf l (f init a) r h with h' | ⟨hm, hg⟩
      · rcases hf init a with he | ⟨he, hg⟩
        · exact Or.inl (he ▸ h')
        · rw [he] at h'
          cases h'
          exact Or.inr ⟨List.mem_cons_self, hg⟩
      · exact Or.inr ⟨List.mem_cons_of_mem _ hm, hg⟩

theorem matStart_spec {sc : Scope} {c : Cell} {exp : ℕ} {mats : List (ℕ × Cell)} {src : Cell}
    {dist : ℕ} (h : matStart sc c exp mats = (src, dist)) :
    ∃ e, e + dist = exp ∧ ((e, src) = (0, c) ∨ (e, src) ∈ mats) := by
  unfold matStart at h
  split at h
  · next e src' hstart =>
    cases h
    unfold matPick at hstart
    split at hstart
    · cases hstart
    · have := foldl_pick _ (fun x : ℕ × Cell => x.1 < exp) (fun best x => by
        split
        · next hc =>
          right
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
          exact ⟨rfl, hc.1.1⟩
        · left; rfl) _ _ _ hstart
      rcases this with h0 | ⟨hm, hlt⟩
      · cases h0
      · exact ⟨e, by dsimp only at hlt; omega, by simpa using hm⟩
  · cases h
    exact ⟨0, by omega, Or.inl rfl⟩

/-- **`materialize c exp` returns a cell holding `fp[c] · g^exp`.** -/
theorem materialize_spec (c : Cell) (exp : ℕ) :
    Spec Γ fp F ctx (materialize c exp)
      (fun o => wd Γ.L fp o = wd Γ.L fp c * ofK (addressOfIndex exp)) := by
  intro st
  unfold materialize
  dsimp only
  split
  · next h0 =>
    exact SpecAt.pure fun _ _ _ => by rw [h0, addressOfIndex, pow_zero, ofK_one, mul_one]
  · refine SpecAt.guard fun hlt => ?_
    refine SpecAt.get_bind (SpecAt.withPool ?_)
    have hmats : PoolOK Γ.L fp st.scope → ∀ p ∈ (st.scope.mats.get? c).getD [],
        wd Γ.L fp p.2 = wd Γ.L fp c * ofK (addressOfIndex p.1) := by
      intro hp p hpm
      cases hg : st.scope.mats.get? c with
      | none => rw [hg] at hpm; simp at hpm
      | some l => rw [hg] at hpm; exact hp.mats c l hg p hpm
    split
    · next e o hfind =>
      refine SpecAt.pure fun h _ _ => ?_
      have he : e = exp := by simpa using List.find?_some hfind
      rw [← he]
      exact hmats h.2 (e, o) (List.mem_of_find?_eq_some hfind)
    · generalize hpair : matStart st.scope c exp ((st.scope.mats.get? c).getD []) = pr
      obtain ⟨src, dist⟩ := pr
      dsimp only
      obtain ⟨e, he, hsrc⟩ := matStart_spec hpair
      refine SpecAt.call (constCell_spec _) fun k _ => ?_
      refine SpecAt.call (mulCell_spec src k) fun o _ => ?_
      have key : PoolOK Γ.L fp st.scope → wd Γ.L fp k = Guest.word (gpowLimbs dist).1
          (gpowLimbs dist).2 → wd Γ.L fp o = wd Γ.L fp src * wd Γ.L fp k →
          wd Γ.L fp o = wd Γ.L fp c * ofK (addressOfIndex exp) := by
        intro hp hk ho
        have hsrc' : wd Γ.L fp src = wd Γ.L fp c * ofK (addressOfIndex e) := by
          rcases hsrc with h0 | hm
          · cases h0
            rw [addressOfIndex, pow_zero, ofK_one, mul_one]
          · exact hmats hp (e, src) hm
        rw [ho, hk, word_gpow (by omega), hsrc', mul_assoc, ofK_gpow_add, he]
      refine SpecAt.modify_bind (Emits.frame rfl rfl ⟨rfl, rfl⟩ fun h _ hp =>
        hp.insertMats fun p hp' => ?_) ?_
      · rcases List.mem_append.mp hp' with hm | hm
        · exact hmats h.1.1.2 p hm
        · obtain rfl := List.mem_singleton.mp hm
          exact key h.1.1.2 h.1.2 h.2
      · exact SpecAt.pure fun h _ _ => key h.1.1.1.2 h.1.1.2 h.1.2

/-- **The cell of a value an instruction reads holds the value.** -/
theorem cellOf_spec (v : V) :
    Spec Γ fp F ctx (cellOf v) (fun n => wd Γ.L fp n = valP Γ.L fp F v) := by
  intro st
  unfold cellOf
  refine SpecAt.get_bind (SpecAt.withSub ?_)
  split
  · next n hn => exact SpecAt.pure fun h _ _ => (valP_of_sub h.2 hn).symm
  · next n e hn =>
    exact SpecAt.last (materialize_spec n e) fun o h ho => ho.trans (valP_of_sub h.2 hn).symm
  · exact SpecAt.fail

/-- A value as a factor: the cell's word times `g^shift` is the value. -/
theorem factor_spec (v : V) :
    Spec Γ fp F ctx (factor v)
      (fun r => valP Γ.L fp F v = wd Γ.L fp r.1 * ofK (addressOfIndex r.2)) := by
  intro st
  unfold factor
  refine SpecAt.get_bind (SpecAt.withSub ?_)
  have one : ∀ x : E, x = x * ofK (addressOfIndex 0) := fun x => by
    rw [addressOfIndex, pow_zero, ofK_one, mul_one]
  split
  · next n e hn =>
    split
    · refine SpecAt.call (materialize_spec n e) fun o _ => ?_
      exact SpecAt.pure fun h _ _ => by
        rw [valP_of_sub h.1.2 hn, ← one]
        exact h.2.symm
    · exact SpecAt.pure fun h _ _ => valP_of_sub h.2 hn
  · refine SpecAt.call (cellOf_spec v) fun n _ => ?_
    exact SpecAt.pure fun h _ _ => by rw [← one]; exact h.2.symm

/-- The pointer cell and offset of a `DEREF` through `p · g^off`: the same address. -/
theorem pointer_spec (p : V) (off : ℕ) :
    Spec Γ fp F ctx (pointer p off) (fun r => IsInK (wd Γ.L fp r.1) →
      IsInK (valP Γ.L fp F p) ∧ (valP Γ.L fp F p).limb 0 * addressOfIndex off =
        (wd Γ.L fp r.1).limb 0 * addressOfIndex r.2) := by
  intro st
  unfold pointer
  refine SpecAt.call (factor_spec p) fun r _ => ?_
  obtain ⟨n, e⟩ := r
  dsimp only
  refine SpecAt.guard fun _ => ?_
  exact SpecAt.pure fun h _ _ hK => by
    rw [h.2]
    refine ⟨isInK_mul hK (isInK_ofK _), ?_⟩
    rw [limb_mul_ofK hK, mul_assoc, addressOfIndex, addressOfIndex, addressOfIndex, ← pow_add]

/-- A pooled result: the pool's cell, justified by the pool, or a fresh one the instruction
writes and the pool learns. -/
theorem pooledCell_spec {find : Scope → Option Cell} {learn : Cell → Scope → Scope}
    {mk : Cell → LOp} (R : Cell → Prop) (hj : ∀ o, (mk o).isJump = false)
    (hfind : ∀ sc o, PoolOK Γ.L fp sc → find sc = some o → R o)
    (hmk : ∀ o pc, Holds Γ.L pc fp (Γ.R (mk o)) → R o)
    (hlearn : ∀ sc o, PoolOK Γ.L fp sc → R o → PoolOK Γ.L fp (learn o sc)) :
    Spec Γ fp F ctx (pooledCell find learn mk) R := by
  intro st
  unfold pooledCell
  refine SpecAt.get_bind ?_
  split
  · next o ho => exact SpecAt.pure fun _ _ hp => hfind _ o hp ho
  · refine SpecAt.call fresh_spec fun o _ => ?_
    refine SpecAt.call (emitOp_spec (hj o)) fun _ _ => ?_
    refine SpecAt.modify_bind (Emits.frame rfl rfl ⟨rfl, rfl⟩ fun h _ hp =>
      hlearn _ o hp (hmk o _ h.2.choose_spec)) ?_
    exact SpecAt.pure fun h _ _ => hmk o _ h.1.2.choose_spec

/-- A value placed in a pooled result's cell. -/
theorem pooled_spec {d : V} {find : Scope → Option Cell} {learn : Cell → Scope → Scope}
    {mk : Cell → LOp} (R : Cell → Prop) (hj : ∀ o, (mk o).isJump = false)
    (hfind : ∀ sc o, PoolOK Γ.L fp sc → find sc = some o → R o)
    (hmk : ∀ o pc, Holds Γ.L pc fp (Γ.R (mk o)) → R o)
    (hlearn : ∀ sc o, PoolOK Γ.L fp sc → R o → PoolOK Γ.L fp (learn o sc)) :
    Spec Γ fp F ctx (pooled d find learn mk)
      (fun _ => ∃ o, R o ∧ valP Γ.L fp F d = wd Γ.L fp o) := by
  intro st
  unfold pooled
  refine SpecAt.call (pooledCell_spec R hj hfind hmk hlearn) fun o _ => ?_
  exact SpecAt.last (bindTo_spec d (.cell o)) fun _ h hb => ⟨o, h.2, hb⟩

/-! ## Lists -/

theorem mapM_spec {β γ : Type} {f : β → P γ} {R : β → γ → Prop}
    (hf : ∀ b, Spec Γ fp F ctx (f b) (R b)) :
    ∀ l : List β, Spec Γ fp F ctx (l.mapM f) (fun rs => List.Forall₂ R l rs)
  | [] => fun st => by
      rw [List.mapM_nil]
      exact SpecAt.pure fun _ _ _ => List.Forall₂.nil
  | b :: l => fun st => by
      rw [List.mapM_cons]
      refine SpecAt.call (hf b) fun c _ => ?_
      refine SpecAt.call (mapM_spec hf l) fun cs _ => ?_
      exact SpecAt.pure fun h _ _ => List.Forall₂.cons h.1.2 h.2

theorem forM_spec {β : Type} {f : β → P PUnit} {R : β → Prop}
    (hf : ∀ b, Spec Γ fp F ctx (f b) (fun _ => R b)) :
    ∀ l : List β, Spec Γ fp F ctx (l.forM f) (fun _ => ∀ b ∈ l, R b)
  | [] => fun st => by
      show SpecAt True ctx st (pure PUnit.unit) _
      exact SpecAt.pure fun _ _ _ _ hb => nomatch hb
  | b :: l => fun st => by
      show SpecAt True ctx st (f b >>= fun _ => l.forM f) _
      refine SpecAt.call (hf b) fun _ _ => ?_
      exact SpecAt.last (forM_spec hf l) fun _ h hl b' hb' => by
        rcases List.mem_cons.mp hb' with rfl | hm
        · exact h.2
        · exact hl b' hm

/-- The cells of a run hold its values, in order. -/
theorem forall₂_cells {L : MemoryImage κ} {vs : List V} {cs : List Cell}
    (h : List.Forall₂ (fun v n => wd L fp n = valP L fp F v) vs cs) :
    cs.map (wd L fp) = vs.map (valP L fp F) := by
  induction h with
  | nil => rfl
  | cons h _ ih => simp [h, ih]

theorem bindRun_spec (vs : List V) (base : Cell) :
    Spec Γ fp F ctx (bindRun vs base) (fun _ => True) := fun _ =>
  SpecAt.lastT (forM_spec (fun _ => bindTo_spec _ _) _)

theorem takeRun_spec (vs : List V) : Spec Γ fp F ctx (takeRun vs) (fun _ => True) := by
  intro st
  unfold takeRun
  refine SpecAt.get_bind (SpecAt.bindT (bindRun_spec vs _ st) fun _ _ => ?_)
  exact SpecAt.modify quiet

end
end LeanVM.Guest.Backend
