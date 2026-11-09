/-
  LeanVM.Guest.B1.Opening.QueriesRow

  One query's row: its packs and its dot product with the row weights.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesT
public import LeanVM.Guest.B1.Common.Atoms

/-!
# A query's row (`opening_query`, G:1346-1385)

* `oqPack_sound`: the packs put each pair of row words in `K` and make the packed cell
  `E.ofLimbs` of their limbs (`pack64x2`); `oqRow b R σ` is the row's `K` words.
* `oqDot_sound`: the dot product is `rowDot base I (oqRow …) w`, `w` the weights read at `wp`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader} {σ : Val}

/-! ## Atoms -/

theorem oqRowT_atoms (b R : ℕ) : AllAtoms (oqRowT b R) := allAtoms_cons allAtoms_nil

theorem oqPackT_atoms (b R j : ℕ) : AllAtoms (oqPackT b R j) := by
  unfold oqPackT
  exact allAtoms_cons (allAtoms_cons (allAtoms_cons (allAtoms_cons allAtoms_nil)))

theorem oqPacksT_atoms (b R : ℕ) : AllAtoms (oqPacksT b R) :=
  allAtoms_map_flatten fun _ _ => oqPackT_atoms _ _ _

theorem oqWordT_atoms (s : Oq) (b jw t : ℕ) : AllAtoms (oqWordT s b jw t) := by
  unfold oqWordT
  split <;> exact allAtoms_cons (allAtoms_cons (allAtoms_cons allAtoms_nil))

theorem oqTermT_atoms (s : Oq) (wp : V) (b h l : ℕ) : AllAtoms (oqTermT s wp b h l) := by
  unfold oqTermT
  refine allAtoms_append (allAtoms_append ?_ (allAtoms_cons (allAtoms_cons allAtoms_nil))) ?_
  · split
    · exact allAtoms_nil
    · exact oqWordT_atoms _ _ _ _
  · split
    · exact allAtoms_nil
    · exact allAtoms_cons allAtoms_nil

theorem oqGroupT_atoms (s : Oq) (wp : V) (b h : ℕ) : AllAtoms (oqGroupT s wp b h) := by
  unfold oqGroupT
  refine allAtoms_append (allAtoms_append (allAtoms_map_flatten fun _ _ => oqTermT_atoms _ _ _ _ _)
    (allAtoms_cons (allAtoms_cons allAtoms_nil))) ?_
  split
  · exact allAtoms_nil
  · exact allAtoms_cons allAtoms_nil

theorem oqDotT_atoms (s : Oq) (wp : V) (b : ℕ) : AllAtoms (oqDotT s wp b) :=
  allAtoms_map_flatten fun _ _ => oqGroupT_atoms _ _ _ _

/-! ## The packs -/

/-- The row's `K` words: the hinted words' low limbs. -/
def oqRow (b R : ℕ) (σ : Val) : List K := (List.range R).map fun i ↦ (σ (.n (b + i))).limb 0

theorem mem_oqPacksT {b R j : ℕ} (hj : j < R / 2) {a : Atom} (h : Stmt.atom a ∈ oqPackT b R j) :
    Stmt.atom a ∈ oqPacksT b R :=
  List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩, h⟩

/-- **A pack** (`pack64x2(row[2j], row[2j+1])`): both words in `K`, the packed cell the cell of
their limbs. -/
theorem oqPack_sound {b R j : ℕ} (hA : ∀ a, Stmt.atom a ∈ oqPacksT b R → a.Holds rd σ)
    (hj : j < R / 2) :
    IsInK (σ (.n (b + 2 * j))) ∧ IsInK (σ (.n (b + 2 * j + 1))) ∧
      σ (.n (oqPk b R j)) =
        E.ofLimbs ((σ (.n (b + 2 * j))).limb 0) ((σ (.n (b + 2 * j + 1))).limb 0) 0 := by
  have h1 := hA _ (mem_oqPacksT hj (by simp [oqPackT]) :
    Stmt.atom (.assertInK (.n (b + 2 * j)) (.n (b + 2 * j + 1))) ∈ _)
  have h2 := hA _ (mem_oqPacksT hj (by simp [oqPackT]) :
    Stmt.atom (.const (.n (b + R + 3 * j)) (word 0 1 0)) ∈ _)
  have h3 := hA _ (mem_oqPacksT hj (by simp [oqPackT]) :
    Stmt.atom (.mul (.n (b + R + 3 * j + 1)) (.n (b + R + 3 * j)) (.n (b + 2 * j + 1))) ∈ _)
  have h4 := hA _ (mem_oqPacksT hj (by simp [oqPackT]) :
    Stmt.atom (.add (.n (b + R + 3 * j + 2)) (.n (b + 2 * j)) (.n (b + R + 3 * j + 1))) ∈ _)
  simp only [Atom.Holds] at h1 h2 h3 h4
  refine ⟨h1.1, h1.2, ?_⟩
  rw [oqPk, h4, h3, h2, word_y]
  exact pack64x2_eq h1.1 h1.2


/-! ## The dot product -/

/-- The deployed row shapes: level 0 (`base = 1`, `I = 64`) and deeper (`base = 0`, `I = 16`). -/
def Oq.RowShape (s : Oq) : Prop := (s.base = 1 ∧ s.I = 64) ∨ (s.base = 0 ∧ s.I = 16)

/-- `rowDot` with the words given as a function. -/
def dotSum (I lo : ℕ) (W w : ℕ → E) : E :=
  ((List.range (I / lo)).map fun h ↦ w (lo + h) *
    ((List.range lo).map fun l ↦ W (lo * h + l) * w l).foldl (· + ·) 0).foldl (· + ·) 0

theorem rowDot_eq (base I : ℕ) (row : List K) (w : ℕ → E) :
    rowDot base I row w = dotSum I (rowLo I) (rowWord base row) w := rfl

theorem foldl_range_succ (f : ℕ → E) (n : ℕ) :
    ((List.range (n + 1)).map f).foldl (· + ·) 0 = ((List.range n).map f).foldl (· + ·) 0 + f n := by
  rw [List.range_succ, List.map_append, List.foldl_append]
  rfl

theorem mem_oqDotT {s : Oq} {wp : V} {b h : ℕ} (hh : h < s.I / s.lo) {a : Atom}
    (ha : Stmt.atom a ∈ oqGroupT s wp b h) : Stmt.atom a ∈ oqDotT s wp b :=
  List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨h, List.mem_range.mpr hh, rfl⟩, ha⟩

theorem mem_oqGroupT_term {s : Oq} {wp : V} {b h l : ℕ} (hl : l < s.lo) {a : Atom}
    (ha : Stmt.atom a ∈ oqTermT s wp b h l) : Stmt.atom a ∈ oqGroupT s wp b h := by
  unfold oqGroupT
  exact List.mem_append_left _ (List.mem_append_left _
    (List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨l, List.mem_range.mpr hl, rfl⟩, ha⟩))

/-- The weight `wp[l]` the terms read, and `wp[lo + h]` the groups read. -/
def oqW (s : Oq) (b : ℕ) (σ : Val) (i : ℕ) : E :=
  if i < s.lo then σ (.n (oqTs s b 0 i + s.tsz)) else σ (.n (oqGs s b (i - s.lo) + s.G - 2))

/-- **The dot product** (G:1368-1385): from the words `W` the terms read, the template's value is
`dotSum`, the weights read at `wp`. -/
theorem oqDot_sound {s : Oq} (hs : s.RowShape) {wp : V} {b : ℕ} {W : ℕ → E}
    (hA : ∀ a, Stmt.atom a ∈ oqDotT s wp b → a.Holds rd σ)
    (hW : ∀ h < s.I / s.lo, ∀ l < s.lo, σ (.n (oqWordV s b h l)) = W (s.lo * h + l)) :
    (∀ i < s.lo + s.I / s.lo, LoadHolds rd (σ wp) i (oqW s b σ i)) ∧
      σ (.n (oqDot s b)) = dotSum s.I s.lo W (oqW s b σ) := by
  have hlo : s.lo = 8 := by rcases hs with ⟨-, h⟩ | ⟨-, h⟩ <;> simp [Oq.lo, rowLo, h]
  have hng : 0 < s.I / s.lo := by rcases hs with ⟨-, h⟩ | ⟨-, h⟩ <;> simp [hlo, h]
  -- the term atoms
  have tload : ∀ h < s.I / s.lo, ∀ l < s.lo,
      LoadHolds rd (σ wp) l (σ (.n (oqTs s b h l + s.tsz))) := fun h hh l hl => by
    have := hA _ (mem_oqDotT hh (mem_oqGroupT_term hl (by simp [oqTermT] :
      Stmt.atom (.load (.n (oqTs s b h l + s.tsz)) wp l) ∈ _)))
    exact this
  have tmul : ∀ h < s.I / s.lo, ∀ l < s.lo,
      σ (.n (oqTs s b h l + s.tsz + 1)) =
        σ (.n (oqWordV s b h l)) * σ (.n (oqTs s b h l + s.tsz)) := fun h hh l hl => by
    have := hA _ (mem_oqDotT hh (mem_oqGroupT_term hl (by simp [oqTermT] :
      Stmt.atom (.mul (.n (oqTs s b h l + s.tsz + 1)) (.n (oqWordV s b h l))
        (.n (oqTs s b h l + s.tsz))) ∈ _)))
    exact this
  have tadd : ∀ h < s.I / s.lo, ∀ l, l + 1 < s.lo →
      σ (.n (oqTs s b h (l + 1) + s.tsz + 2)) =
        σ (.n (oqPart s b h l)) + σ (.n (oqTs s b h (l + 1) + s.tsz + 1)) := fun h hh l hl => by
    have := hA _ (mem_oqDotT hh (mem_oqGroupT_term hl (by simp [oqTermT] :
      Stmt.atom (.add (.n (oqTs s b h (l + 1) + s.tsz + 2)) (.n (oqPart s b h l))
        (.n (oqTs s b h (l + 1) + s.tsz + 1))) ∈ _)))
    exact this
  -- the group atoms
  have gload : ∀ h < s.I / s.lo,
      LoadHolds rd (σ wp) (s.lo + h) (σ (.n (oqGs s b h + s.G - 2))) := fun h hh => by
    have := hA _ (mem_oqDotT hh (by simp [oqGroupT] :
      Stmt.atom (.load (.n (oqGs s b h + s.G - 2)) wp (s.lo + h)) ∈ oqGroupT s wp b h))
    exact this
  have gmul : ∀ h < s.I / s.lo, σ (.n (oqGs s b h + s.G - 1)) =
      σ (.n (oqGs s b h + s.G - 2)) * σ (.n (oqPart s b h (s.lo - 1))) := fun h hh => by
    have := hA _ (mem_oqDotT hh (by simp [oqGroupT] :
      Stmt.atom (.mul (.n (oqGs s b h + s.G - 1)) (.n (oqGs s b h + s.G - 2))
        (.n (oqPart s b h (s.lo - 1)))) ∈ oqGroupT s wp b h))
    exact this
  have gadd : ∀ h, h + 1 < s.I / s.lo → σ (.n (oqGs s b (h + 1) + s.G)) =
      σ (.n (oqDotAfter s b h)) + σ (.n (oqGs s b (h + 1) + s.G - 1)) := fun h hh => by
    have := hA _ (mem_oqDotT hh (by simp [oqGroupT] :
      Stmt.atom (.add (.n (oqGs s b (h + 1) + s.G)) (.n (oqDotAfter s b h))
        (.n (oqGs s b (h + 1) + s.G - 1))) ∈ oqGroupT s wp b (h + 1)))
    exact this
  -- the weights
  have wl : ∀ h < s.I / s.lo, ∀ l < s.lo, σ (.n (oqTs s b h l + s.tsz)) = oqW s b σ l :=
    fun h hh l hl => by
      simp only [oqW, hl, ↓reduceIte]
      exact loadHolds_unique (tload h hh l hl) (tload 0 hng l hl)
  have wg : ∀ h < s.I / s.lo, σ (.n (oqGs s b h + s.G - 2)) = oqW s b σ (s.lo + h) :=
    fun h hh => by
      simp only [oqW, show ¬ s.lo + h < s.lo by omega, ↓reduceIte, Nat.add_sub_cancel_left]
  refine ⟨fun i hi => ?_, ?_⟩
  · by_cases h' : i < s.lo
    · rw [← wl 0 hng i h']; exact tload 0 hng i h'
    · obtain ⟨h, rfl⟩ : ∃ h, i = s.lo + h := ⟨i - s.lo, by omega⟩
      rw [← wg h (by omega)]; exact gload h (by omega)
  -- the partial sums of a group
  have part : ∀ h < s.I / s.lo, ∀ l < s.lo, σ (.n (oqPart s b h l)) =
      ((List.range (l + 1)).map fun l' ↦ W (s.lo * h + l') * oqW s b σ l').foldl (· + ·) 0 := by
    intro h hh l hl
    induction l with
    | zero =>
      have e : oqPart s b h 0 = oqTs s b h 0 + s.tsz + 1 := by simp [oqPart]
      rw [e, tmul h hh 0 hl, hW h hh 0 hl, wl h hh 0 hl]
      simp
    | succ l ih =>
      have e : oqPart s b h (l + 1) = oqTs s b h (l + 1) + s.tsz + 2 := by simp [oqPart]
      rw [foldl_range_succ, ← ih (by omega), e, tadd h hh l hl, tmul h hh (l + 1) hl,
        hW h hh (l + 1) hl, wl h hh (l + 1) hl]
  have partEnd : ∀ h < s.I / s.lo, σ (.n (oqPart s b h (s.lo - 1))) =
      ((List.range s.lo).map fun l ↦ W (s.lo * h + l) * oqW s b σ l).foldl (· + ·) 0 :=
    fun h hh => by rw [part h hh (s.lo - 1) (by omega), show s.lo - 1 + 1 = s.lo by omega]
  -- the groups
  have grp : ∀ h < s.I / s.lo, σ (.n (oqDotAfter s b h)) =
      ((List.range (h + 1)).map fun h' ↦ oqW s b σ (s.lo + h') *
        ((List.range s.lo).map fun l ↦ W (s.lo * h' + l) * oqW s b σ l).foldl (· + ·) 0).foldl
          (· + ·) 0 := by
    intro h hh
    induction h with
    | zero =>
      have e : oqDotAfter s b 0 = oqGs s b 0 + s.G - 1 := by simp [oqDotAfter]
      rw [e, gmul 0 hh, wg 0 hh, partEnd 0 hh]
      simp
    | succ h ih =>
      have e : oqDotAfter s b (h + 1) = oqGs s b (h + 1) + s.G := by simp [oqDotAfter]
      rw [foldl_range_succ, ← ih (by omega), e, gadd h hh, gmul (h + 1) hh, wg (h + 1) hh,
        partEnd (h + 1) hh]
  rw [oqDot, grp _ (by omega), show s.I / s.lo - 1 + 1 = s.I / s.lo by omega]
  rfl

/-! ## The row's words -/

/-- Every hinted word is in `K` (its pair's pack). -/
theorem oqRow_inK {b R : ℕ} (hR : R % 2 = 0) (hA : ∀ a, Stmt.atom a ∈ oqPacksT b R → a.Holds rd σ)
    {j : ℕ} (hj : j < R) : IsInK (σ (.n (b + j))) := by
  have hp := oqPack_sound hA (j := j / 2) (by omega)
  rcases Nat.mod_two_eq_zero_or_one j with h | h
  · rw [show j = 2 * (j / 2) by omega]; exact hp.1
  · rw [show j = 2 * (j / 2) + 1 by omega, ← Nat.add_assoc]; exact hp.2.1

theorem getD_oqRow {b R j : ℕ} (hj : j < R) : (oqRow b R σ).getD j 0 = (σ (.n (b + j))).limb 0 := by
  simp [oqRow, List.getD_eq_getElem?_getD, hj]

/-- `ofK a + y·(b + c·y) = E.ofLimbs a b c`. -/
theorem ofK_add_y_mul_ofLimbs (a b c : K) : ofK a + y * E.ofLimbs b c 0 = E.ofLimbs a b c := by
  rw [mul_comm, ofLimbs_mul_y, ofK_eq_ofLimbs, ofLimbs_add]
  simp

/-- A deeper level's word from its packed low limbs and its top limb. -/
theorem ofLimbs_add_yy (a b : K) {c : E} (hc : IsInK c) :
    E.ofLimbs a b 0 + y * y * c = E.ofLimbs a b (c.limb 0) := by
  rw [eq_ofK_limb hc, add_y_mul_y_mul_ofK]
  simp [limb_ofK]

/-- **The row's words** (G:1373-1382): the word a term reads is `rowWord`. -/
theorem oqWord_sound {s : Oq} (hs : s.RowShape) {wp : V} {b : ℕ}
    (hP : ∀ a, Stmt.atom a ∈ oqPacksT b s.R → a.Holds rd σ)
    (hD : ∀ a, Stmt.atom a ∈ oqDotT s wp b → a.Holds rd σ) :
    ∀ h < s.I / s.lo, ∀ l < s.lo,
      σ (.n (oqWordV s b h l)) = rowWord s.base (oqRow b s.R σ) (s.lo * h + l) := by
  intro h hh l hl
  have hlo : s.lo = 8 := by rcases hs with ⟨-, h⟩ | ⟨-, h⟩ <;> simp [Oq.lo, rowLo, h]
  rcases hs with ⟨hb, hI⟩ | ⟨hb, hI⟩
  · have hR : s.R = 64 := by simp [Oq.R, hb, hI]
    have hj : s.lo * h + l < s.R := by rw [hlo] at hh hl ⊢; rw [hI] at hh; omega
    have hk := oqRow_inK (by omega) hP hj
    simp only [oqWordV, rowWord, hb, ↓reduceIte, getD_oqRow hj]
    exact eq_ofK_limb hk
  · have hR : s.R = 48 := by simp [Oq.R, hb, hI]
    have hjw : s.lo * h + l < 16 := by rw [hlo] at hh hl ⊢; rw [hI] at hh; omega
    set jw := s.lo * h + l with hjwdef
    have mem : ∀ a, Stmt.atom a ∈ oqWordT s b jw (oqTs s b h l) → a.Holds rd σ := fun a ha =>
      hD a (mem_oqDotT hh (mem_oqGroupT_term hl (by
        simp only [oqTermT, hb, show (0 : ℕ) ≠ 1 by decide, ↓reduceIte, List.mem_append]
        exact Or.inl (Or.inl ha))))
    simp only [oqWordV, rowWord, hb, show (0 : ℕ) ≠ 1 by decide, ↓reduceIte]
    rw [getD_oqRow (by omega), getD_oqRow (by omega), getD_oqRow (by omega)]
    rcases Nat.mod_two_eq_zero_or_one jw with he | ho
    · have h1 := mem _ (by simp [oqWordT, he] : Stmt.atom (.const (.n (oqTs s b h l)) (word 0 0 1)) ∈ _)
      have h2 := mem _ (by simp [oqWordT, he] : Stmt.atom (.mul (.n (oqTs s b h l + 1))
        (.n (oqTs s b h l)) (.n (b + (3 * jw + 2)))) ∈ _)
      have h3 := mem _ (by simp [oqWordT, he] : Stmt.atom (.add (.n (oqTs s b h l + 2))
        (.n (oqPk b s.R (3 * jw / 2))) (.n (oqTs s b h l + 1))) ∈ _)
      simp only [Atom.Holds] at h1 h2 h3
      have hp := oqPack_sound hP (j := 3 * jw / 2) (by omega)
      rw [show 2 * (3 * jw / 2) = 3 * jw by omega] at hp
      have hk := oqRow_inK (by omega) hP (j := 3 * jw + 2) (by omega)
      rw [h3, h2, h1, hp.2.2, word_yy, ofLimbs_add_yy _ _ hk]
      rfl
    · have h1 := mem _ (by simp [oqWordT, ho] : Stmt.atom (.const (.n (oqTs s b h l)) (word 0 1 0)) ∈ _)
      have h2 := mem _ (by simp [oqWordT, ho] : Stmt.atom (.mul (.n (oqTs s b h l + 1))
        (.n (oqTs s b h l)) (.n (oqPk b s.R ((3 * jw + 1) / 2)))) ∈ _)
      have h3 := mem _ (by simp [oqWordT, ho] : Stmt.atom (.add (.n (oqTs s b h l + 2))
        (.n (b + 3 * jw)) (.n (oqTs s b h l + 1))) ∈ _)
      simp only [Atom.Holds] at h1 h2 h3
      have hp := oqPack_sound hP (j := (3 * jw + 1) / 2) (by omega)
      rw [show 2 * ((3 * jw + 1) / 2) = 3 * jw + 1 by omega] at hp
      have hk := oqRow_inK (by omega) hP (j := 3 * jw) (by omega)
      rw [h3, h2, h1, hp.2.2, word_y, eq_ofK_limb hk, ofK_add_y_mul_ofLimbs, limb_ofK,
        show b + (3 * jw + 1) + 1 = b + (3 * jw + 2) by omega]
      simp

end
end LeanVM.Guest.B1
