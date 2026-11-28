/-
  LeanVM.Guest.B1.Link.IndexSide

  B1 for `index_side` (pointer widths `19` to `24`): `index_mle`, `eq(ζ, r)`, its shift, `below`.
-/

module

public import LeanVM.Guest.B1.Link.Suffixes

/-!
# `index_side`

`index_side(r, zeta, below, w)` (G) calls `index_mle(r, w)`, folds `(eqzr, shz, carry)` over
`(zeta[k], r[k])`, `k < w` (`sideStep`), then writes `below[k] = Π_{k ≤ i < w} (1 + r_i)` with
`one_plus_suffixes`' loop (`ops_run` at offset `16 w`). Its specialization `index_side__L{w}` is
`isBody w`: block `k` from value `16 k + 2` (`isBlk`), the first with the fold's start folded in.
`index_mle`'s meaning is a hypothesis (`IndexMleSound`): `index_mle` is unchanged since the bus
era, and B1's restoration of the unchanged functions proves it.
-/

namespace LeanVM.Guest.B1.Link

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Protocol.Verifier

@[expose] public section

/-- `index_mle__L{w}`, `19 ≤ w ≤ 24`. -/
def imNames : List String := ["index_mle__L19", "index_mle__L20", "index_mle__L21", "index_mle__L22", "index_mle__L23", "index_mle__L24"]

/-- `index_mle__L{w}(zeta)` is `indexMle` of the `w` words at `zeta` (the bus era's
`index_mle_Spec`, at the widths the link reads). -/
def IndexMleSound (P : Program) : Prop :=
  ∀ w, 19 ≤ w → w ≤ 24 → ∀ (rd : Reader) (zeta v : E), P.Rel rd (imNames.getD (w - 19) "") [zeta] [v] →
    ∃ zs : List E, zs.length = w ∧ ReadsAt rd zeta zs ∧ v = indexMle zs

/-- **`index_side(r, zeta, below, w)`**: the `w` words `rs` at `r` and `zs` at `zeta`;
`below[k] = belowE rs k` for `k ≤ w`; it returns `indexMle rs` and `sideFold zs rs`'s
`eq(ζ, r)` and shift. -/
def MeaningIndexSide (w : ℕ) (rd : Reader) : List E → List E → Prop
  | [r, zeta, below], rets => ∃ rs zs : List E, rs.length = w ∧ zs.length = w ∧
      ReadsAt rd r rs ∧ ReadsAt rd zeta zs ∧ (∀ k ≤ w, LoadHolds rd below k (belowE rs k)) ∧
      rets = [indexMle rs, (sideFold zs rs).1, (sideFold zs rs).2.1]
  | _, _ => False

/-- The specializations' names, `index_side__L{w}`, `19 ≤ w ≤ 24`. -/
def isNames : List String := ["index_side__L19", "index_side__L20", "index_side__L21", "index_side__L22", "index_side__L23", "index_side__L24"]

/-- `index_side__L{w}`'s core IR implies its meaning. -/
def index_side_SoundP (P : Program) : Prop :=
  ∀ w, 19 ≤ w → w ≤ 24 → ∀ (rd : Reader) (args rets : List E),
    P.Rel rd (isNames.getD (w - 19) "") args rets → MeaningIndexSide w rd args rets

/-! ## Runs of loads -/

theorem readsAt_unique {rd : Reader} {p : E} {l1 l2 : List E} (h1 : ReadsAt rd p l1)
    (h2 : ReadsAt rd p l2) (hl : l1.length = l2.length) : l1 = l2 :=
  List.ext_getElem hl fun k hk1 hk2 ↦ loadHolds_unique (h1 k hk1) (h2 k hk2)

theorem readsAt_range_map {rd : Reader} {p : E} {f : ℕ → E} {n : ℕ}
    (h : ∀ k < n, LoadHolds rd p k (f k)) : ReadsAt rd p ((List.range n).map f) := by
  intro k hk
  simp only [List.length_map, List.length_range] at hk
  simpa using h k hk

theorem zip_range_map {α β : Type} (g : ℕ → α) (h : ℕ → β) (n : ℕ) :
    ((List.range n).map g).zip ((List.range n).map h) = (List.range n).map fun i ↦ (g i, h i) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.range_succ, List.zip_append, ih]

/-! ## The template -/

/-- The fold's values after block `k`: `x = r[k]`, `z = zeta[k]`, `eqzr`, `shz`, `carry`. -/
def isX (k : ℕ) : ℕ := if k = 0 then 4 else 16 * k + 2

def isZ (k : ℕ) : ℕ := if k = 0 then 5 else 16 * k + 3

def isEq (k : ℕ) : ℕ := if k = 0 then 8 else 16 * k + 17

def isSh (k : ℕ) : ℕ := if k = 0 then 14 else 16 * k + 12

def isCa (k : ℕ) : ℕ := if k = 0 then 17 else 16 * k + 16

/-- Block `k` of the fold. -/
def isBlk (k : ℕ) : List Stmt :=
  if k = 0 then
    [.atom (.load (.n 4) (.n 0) 0), .atom (.load (.n 5) (.n 1) 0), .atom (.const (.n 6) (word 1 0)),
      .atom (.add (.n 7) (.n 6) (.n 5)), .atom (.add (.n 8) (.n 7) (.n 4)),
      .atom (.const (.n 9) (word 0 0)), .atom (.mul (.n 10) (.n 9) (.n 8)),
      .atom (.const (.n 11) (word 1 0)), .atom (.add (.n 12) (.n 11) (.n 4)),
      .atom (.mul (.n 13) (.n 12) (.n 5)), .atom (.add (.n 14) (.n 10) (.n 13)),
      .atom (.const (.n 15) (word 1 0)), .atom (.add (.n 16) (.n 15) (.n 5)),
      .atom (.mul (.n 17) (.n 4) (.n 16))]
  else
    let b := 16 * k + 2
    [.atom (.load (.n b) (.n 0) k), .atom (.load (.n (b + 1)) (.n 1) k),
      .atom (.const (.n (b + 2)) (word 1 0)), .atom (.add (.n (b + 3)) (.n (b + 2)) (.n (b + 1))),
      .atom (.add (.n (b + 4)) (.n (b + 3)) (.n b)),
      .atom (.mul (.n (b + 5)) (.n (isSh (k - 1))) (.n (b + 4))),
      .atom (.const (.n (b + 6)) (word 1 0)), .atom (.add (.n (b + 7)) (.n (b + 6)) (.n b)),
      .atom (.mul (.n (b + 8)) (.n (isCa (k - 1))) (.n (b + 7))),
      .atom (.mul (.n (b + 9)) (.n (b + 8)) (.n (b + 1))),
      .atom (.add (.n (b + 10)) (.n (b + 5)) (.n (b + 9))),
      .atom (.mul (.n (b + 11)) (.n (isCa (k - 1))) (.n b)),
      .atom (.const (.n (b + 12)) (word 1 0)), .atom (.add (.n (b + 13)) (.n (b + 12)) (.n (b + 1))),
      .atom (.mul (.n (b + 14)) (.n (b + 11)) (.n (b + 13))),
      .atom (.mul (.n (b + 15)) (.n (isEq (k - 1))) (.n (b + 4)))]

/-- The expansion of `index_side__L{w}`, `w ≥ 1`. -/
def isBody (w : ℕ) : List Stmt :=
  [.call (imNames.getD (w - 19) "") [.n 0] [.n 3]] ++ ((List.range w).map isBlk).flatten ++
    opsLoop (16 * w) 2 0 w ++
    [.atom (.copy (.n (20 * w + 2)) (.n 3)), .atom (.copy (.n (20 * w + 3)) (.n (isEq (w - 1)))),
      .atom (.copy (.n (20 * w + 4)) (.n (isSh (w - 1)))),
      .ret [.n (20 * w + 2), .n (20 * w + 3), .n (20 * w + 4)]]

/-- The fold's state after block `k`. -/
def IsOk (rd : Reader) (σ : Val) (k : ℕ) : Prop :=
  LoadHolds rd (σ (.n 0)) k (σ (.n (isX k))) ∧ LoadHolds rd (σ (.n 1)) k (σ (.n (isZ k))) ∧
    (σ (.n (isEq k)), σ (.n (isSh k)), σ (.n (isCa k))) =
      sideStep (if k = 0 then (1, 0, 1) else (σ (.n (isEq (k - 1))), σ (.n (isSh (k - 1))),
        σ (.n (isCa (k - 1))))) (σ (.n (isZ k)), σ (.n (isX k)))

theorem holds_isBlk {C : CallRel} {rd : Reader} {σ : Val} (k : ℕ) (kret : List E → Prop)
    (h : Stmt.HoldsList C rd σ (isBlk k) True kret) : IsOk rd σ k := by
  unfold isBlk at h
  split_ifs at h with hk
  · subst hk
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, word_one, word_zero] at h
    obtain ⟨l4, l5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h
    refine ⟨l4, l5, ?_⟩
    simp only [isEq, isSh, isCa, isX, isZ, ↓reduceIte, sideStep, Prod.mk.injEq]
    refine ⟨?_, ?_, ?_⟩
    · rw [h8, h7, h6, one_mul]
    · rw [h14, h10, h9, h13, h12, h11, h8, h7, h6]; ring
    · rw [h17, h16, h15]; ring
  · have eX : isX k = 16 * k + 2 := by simp [isX, hk]
    have eZ : isZ k = 16 * k + 2 + 1 := by simp [isZ, hk]
    have eE : isEq k = 16 * k + 2 + 15 := by simp [isEq, hk]
    have eS : isSh k = 16 * k + 2 + 10 := by simp [isSh, hk]
    have eC : isCa k = 16 * k + 2 + 14 := by simp [isCa, hk]
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, word_one] at h
    obtain ⟨l0, l1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
    refine ⟨by rw [eX]; exact l0, by rw [eZ]; exact l1, ?_⟩
    simp only [hk, ↓reduceIte, sideStep, Prod.mk.injEq]
    rw [eE, eS, eC, eX, eZ]
    refine ⟨?_, ?_, ?_⟩
    · rw [h15, h4, h3, h2]
    · rw [h10, h5, h9, h8, h7, h6, h4, h3, h2]
    · rw [h14, h11, h13, h12]

theorem isBlk_noRet (k : ℕ) : Stmt.noRetList (isBlk k) = true := by
  unfold isBlk; split <;> rfl

/-- **The template's relation implies its meaning.** -/
theorem is_sound (w : ℕ) (h19 : 19 ≤ w) (h24 : w ≤ 24) (him : IndexMleSound coreProgram) {f : Fn}
    (hfind : coreProgram.find? (isNames.getD (w - 19) "") = some f)
    (hparams : f.params = [.n 0, .n 1, .n 2]) (hbody : f.body = isBody w) (rd : Reader)
    (args rets : List E) :
    coreProgram.Rel rd (isNames.getD (w - 19) "") args rets → MeaningIndexSide w rd args rets := by
  rw [rel_iff_sem hfind, hbody, hparams, isBody]
  simp only [holdsList_append]
  rintro ⟨σ, rfl, h⟩
  simp only [Stmt.HoldsList, Stmt.Holds, List.map_cons, List.map_nil] at h
  obtain ⟨hcall, h⟩ := h
  rw [holdsList_range_flatten w isBlk isBlk_noRet] at h
  obtain ⟨hblk, h⟩ := h
  obtain ⟨⟨as, has, ras, hbel⟩, h⟩ := ops_run (16 * w) 2 0 w h
  obtain ⟨c0, c1, c2, hret⟩ := h
  have hb := fun k (hk : k < w) ↦ holds_isBlk (C := coreProgram.Rel rd) k _ (hblk k hk)
  let x : ℕ → E := fun k ↦ σ (.n (isX k))
  let z : ℕ → E := fun k ↦ σ (.n (isZ k))
  have hS : ∀ k < w, (σ (.n (isEq k)), σ (.n (isSh k)), σ (.n (isCa k))) =
      ((List.range (k + 1)).map fun i ↦ (z i, x i)).foldl sideStep (1, 0, 1) := by
    intro k hk
    induction k with
    | zero => simpa using (hb 0 hk).2.2
    | succ k ih =>
      have e := (hb (k + 1) hk).2.2
      simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel] at e
      rw [e, ih (by omega), List.range_succ (n := k + 1), List.map_append, List.foldl_append]
      rfl
  have rx : ReadsAt rd (σ (.n 0)) ((List.range w).map x) := readsAt_range_map fun k hk ↦ (hb k hk).1
  have rz : ReadsAt rd (σ (.n 1)) ((List.range w).map z) := readsAt_range_map fun k hk ↦ (hb k hk).2.1
  obtain ⟨rs, hrs, rrs, hv⟩ := him w h19 h24 rd _ _ hcall
  have e1 : rs = (List.range w).map x := readsAt_unique rrs rx (by simp [hrs])
  have e2 : as = (List.range w).map x := readsAt_unique ras rx (by simp [has])
  subst e1 e2
  have hf := hS (w - 1) (by omega)
  rw [Nat.sub_add_cancel (by omega)] at hf
  have hfold : sideFold ((List.range w).map z) ((List.range w).map x) =
      (σ (.n (isEq (w - 1))), σ (.n (isSh (w - 1))), σ (.n (isCa (w - 1)))) := by
    rw [hf, sideFold, zip_range_map]
  refine ⟨_, _, hrs, by simp, rrs, rz, hbel, ?_⟩
  rw [← hret, c0, c1, c2, hfold, hv]

/-! ## The specializations -/

set_option maxRecDepth 100000 in
theorem index_side_L19_sound (him : IndexMleSound coreProgram) (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (isNames.getD 0 "") args rets → MeaningIndexSide 19 rd args rets :=
  is_sound 19 (by omega) (by omega) him (f := fn% «index_side__L19»)
    (coreProgram_find?_at (j := idx% «index_side__L19») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem index_side_L20_sound (him : IndexMleSound coreProgram) (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (isNames.getD 1 "") args rets → MeaningIndexSide 20 rd args rets :=
  is_sound 20 (by omega) (by omega) him (f := fn% «index_side__L20»)
    (coreProgram_find?_at (j := idx% «index_side__L20») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem index_side_L21_sound (him : IndexMleSound coreProgram) (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (isNames.getD 2 "") args rets → MeaningIndexSide 21 rd args rets :=
  is_sound 21 (by omega) (by omega) him (f := fn% «index_side__L21»)
    (coreProgram_find?_at (j := idx% «index_side__L21») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem index_side_L22_sound (him : IndexMleSound coreProgram) (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (isNames.getD 3 "") args rets → MeaningIndexSide 22 rd args rets :=
  is_sound 22 (by omega) (by omega) him (f := fn% «index_side__L22»)
    (coreProgram_find?_at (j := idx% «index_side__L22») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem index_side_L23_sound (him : IndexMleSound coreProgram) (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (isNames.getD 4 "") args rets → MeaningIndexSide 23 rd args rets :=
  is_sound 23 (by omega) (by omega) him (f := fn% «index_side__L23»)
    (coreProgram_find?_at (j := idx% «index_side__L23») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem index_side_L24_sound (him : IndexMleSound coreProgram) (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (isNames.getD 5 "") args rets → MeaningIndexSide 24 rd args rets :=
  is_sound 24 (by omega) (by omega) him (f := fn% «index_side__L24»)
    (coreProgram_find?_at (j := idx% «index_side__L24») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

/-- **`index_side`'s core IR implies its meaning**, every specialization, given `index_mle`'s. -/
theorem index_side_sound (him : IndexMleSound coreProgram) : index_side_SoundP coreProgram := by
  intro w h1 h2
  interval_cases w
  exacts [index_side_L19_sound him, index_side_L20_sound him, index_side_L21_sound him, index_side_L22_sound him, index_side_L23_sound him, index_side_L24_sound him]

end
end LeanVM.Guest.B1.Link
