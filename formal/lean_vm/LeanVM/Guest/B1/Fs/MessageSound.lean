/-
  LeanVM.Guest.B1.Fs.MessageSound

  `opening_message`'s words absorbed by groups, and the soundness of its template.
-/

module

public import LeanVM.Guest.B1.Fs.MessageT

/-!
# `opening_message`: groups and soundness

* `absorbAll_groups`: `n ≥ 1` words absorbed on a capacity leave the last group's words waiting
  on `stCap`, the capacity after the full groups before it (`stF … (omK n)`).
* `om_sound`: on a valuation meeting `omBody n nonce`, the meaning `MeaningOpeningMessage`, for
  each of the four tails the deployed messages have (`OmCase`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

theorem holdsList_atomsRet (as : List Atom) (vs : List V) (next : Prop) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (as.map Stmt.atom ++ [.ret vs]) next kret ↔
      (∀ a ∈ as, a.Holds rd σ) ∧ kret (vs.map σ) := by
  induction as with
  | nil => simp [Stmt.HoldsList, Stmt.Holds]
  | cons a as ih => simp [Stmt.HoldsList, Stmt.Holds, ih, and_assoc]

/-! ## Groups of four -/

/-- Group `g` of the words. -/
def grp (xs : List E) (g : ℕ) : List E := (xs.drop (4 * g)).take 4

/-- The capacity before group `g`: the full groups before it permuted in turn. -/
def stCap (cap xs : List E) : ℕ → List E
  | 0 => cap
  | g + 1 => capOf (Fs.perm ⟨stCap cap xs g, (grp xs g).map (·, dsObserve)⟩)

/-- The sponge with group `g` waiting. -/
def stF (cap xs : List E) (g : ℕ) : Fs := ⟨stCap cap xs g, (grp xs g).map (·, dsObserve)⟩

theorem stCap_succ (cap xs : List E) (g : ℕ) : stCap cap xs (g + 1) = capOf (stF cap xs g).perm :=
  rfl

theorem absorbAll_append (s : Fs) (A B : List E) (t : ℕ) :
    s.absorbAll (A ++ B) t = (s.absorbAll A t).absorbAll B t := by
  simp [Fs.absorbAll, List.foldl_append]

theorem length_grp (xs : List E) (g : ℕ) : (grp xs g).length = min 4 (xs.length - 4 * g) := by
  simp [grp]

theorem absorbAll_groups_take (cap xs : List E) :
    ∀ g, 4 * g < xs.length →
      (⟨cap, []⟩ : Fs).absorbAll (xs.take (4 * g + 4)) dsObserve = stF cap xs g
  | 0, _ => by
    rw [absorbAll_short _ _ _ (by simp)]
    simp [stF, stCap, grp]
  | g + 1, h => by
    rw [show 4 * (g + 1) + 4 = (4 * g + 4) + 4 by ring, List.take_add, absorbAll_append,
      absorbAll_groups_take cap xs g (by omega)]
    have hg : (stF cap xs g).pend.length = 4 := by
      simp only [stF, List.length_map, length_grp]; omega
    obtain ⟨a, rest, hr⟩ : ∃ a rest, (xs.drop (4 * g + 4)).take 4 = a :: rest := by
      cases hc : (xs.drop (4 * g + 4)).take 4 with
      | nil => simp at hc; omega
      | cons a rest => exact ⟨a, rest, rfl⟩
    have hrl : rest.length ≤ 3 := by
      have := congrArg List.length hr
      simp only [List.length_take, List.length_cons] at this
      omega
    rw [hr, show a :: rest = [a] ++ rest from rfl, absorbAll_append]
    have h1 : (stF cap xs g).absorbAll [a] dsObserve =
        ⟨capOf (stF cap xs g).perm, [(a, dsObserve)]⟩ := by
      simp [Fs.absorbAll, Fs.absorb, hg, rateScalars]
    rw [h1, absorbAll_short _ _ _ (by simp; omega)]
    simp only [stF, stCap_succ, grp]
    rw [show 4 * (g + 1) = 4 * g + 4 by ring, hr]
    simp

/-- **The words absorbed by groups.** -/
theorem absorbAll_groups (cap xs : List E) (hn : 1 ≤ xs.length) :
    (⟨cap, []⟩ : Fs).absorbAll xs dsObserve = stF cap xs (omK xs.length) := by
  have h := absorbAll_groups_take cap xs (omK xs.length) (by simp only [omK]; omega)
  rwa [List.take_of_length_le (by simp only [omK]; omega)] at h

/-! ## Membership in the template -/

theorem mem_omWord {n nonce p : ℕ} (hp : p < n) {a : Atom} (ha : a ∈ omWordAs p) :
    a ∈ omAtoms n nonce := by
  simp only [omAtoms, omWords, List.mem_append, List.mem_flatMap, List.mem_range]
  exact Or.inl (Or.inl (Or.inr ⟨p, hp, Or.inl ha⟩))

theorem mem_omMid {n nonce g : ℕ} (hg : g < omK n) : omKeccak g ∈ omAtoms n nonce := by
  simp only [omAtoms, omWords, List.mem_append, List.mem_flatMap, List.mem_range]
  refine Or.inl (Or.inl (Or.inr ⟨4 * g + 3, by simp only [omK] at hg; omega, Or.inr ?_⟩))
  rw [ite_eq_left (by simp only [omK] at hg; omega), show (4 * g + 3) / 4 = g by omega]
  exact List.mem_singleton_self _

theorem mem_omTail {n nonce : ℕ} {a : Atom} (ha : a ∈ (omTail n nonce).1) :
    a ∈ omAtoms n nonce := by
  simp only [omAtoms, List.mem_append]
  exact Or.inl (Or.inr ha)

theorem mem_omFinal {n nonce : ℕ} {a : Atom}
    (ha : a ∈ omFinal n nonce (omTail n nonce).2.1 (omTail n nonce).2.2) :
    a ∈ omAtoms n nonce := by
  simp only [omAtoms, List.mem_append]
  exact Or.inr ha

theorem mem_omHead {n nonce : ℕ} {a : Atom}
    (ha : a ∈ [Atom.copy (.n 7) (.n 0), .copy (.n 8) (.n 1), .copy (.n 9) (.n 2),
      .copy (.n 10) (.n 3), .copy (.n 11) (.n 4)]) : a ∈ omAtoms n nonce := by
  simp only [omAtoms, List.mem_append]
  exact Or.inl (Or.inl (Or.inl ha))


/-! ## The words and the groups' permutations -/

/-- What word `p`'s atoms ask. -/
theorem om_word_holds {p : ℕ} (h : ∀ a ∈ omWordAs p, a.Holds rd σ) :
    LoadHolds rd (σ (.n 5)) p (σ (.n (omW p))) ∧ σ (.n (omW p + 1)) = σ (.n (omW p)) ∧
      σ (.n (omW p + 2)) = word 0 dsObserve ∧ LoadHolds rd (σ (.n 6)) p (σ (.n (omW p))) :=
  ⟨h (.load (.n (omW p)) (.n 5) p) (by simp [omWordAs]),
    h (.copy (.n (omW p + 1)) (.n (omW p))) (by simp [omWordAs]),
    h (.const (.n (omW p + 2)) (word 0 dsObserve)) (by simp [omWordAs]),
    h (.load (.n (omW p)) (.n 6) p) (by simp [omWordAs])⟩

/-- A full group of the words read. -/
theorem grp_map_range (f : ℕ → E) {n g : ℕ} (h : 4 * g + 4 ≤ n) :
    grp ((List.range n).map f) g = [f (4 * g), f (4 * g + 1), f (4 * g + 2), f (4 * g + 3)] := by
  apply List.ext_getElem
  · simp [grp]; omega
  · intro i h1 h2
    simp only [grp, List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range]
    simp only [List.length_cons, List.length_nil] at h2
    interval_cases i <;> rfl

/-- The last group of the words read, of `r ≤ 4` words. -/
theorem grp_map_range_last (f : ℕ → E) {n g : ℕ} (h : 4 * g ≤ n) (h4 : n ≤ 4 * g + 4) :
    grp ((List.range n).map f) g = (List.range (n - 4 * g)).map fun t ↦ f (4 * g + t) := by
  apply List.ext_getElem
  · simp [grp]; omega
  · intro i h1 h2
    simp [grp, List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range]

theorem om_pend4 (a b c d : E) :
    pendCells [(a, dsObserve), (b, dsObserve), (c, dsObserve), (d, dsObserve)] =
      [a, word 0 dsObserve, b, word 0 dsObserve, c, word 0 dsObserve, d, word 0 dsObserve] := rfl

/-- The capacity a permutation's cells `8 .. 12` hold. -/
theorem run5_cellsO {O : ℕ} {S : KeccakState}
    (h : ∀ c : Fin 13, σ (.n (O + c.val)) = cellsOfState S false c) :
    (run5 (O + 8)).map σ = capOf S := by
  have e : ∀ i (hi : i < 5), σ (.n (O + 8 + i)) = cellsOfState S false ⟨8 + i, by omega⟩ :=
    fun i hi ↦ by rw [show O + 8 + i = O + (⟨8 + i, by omega⟩ : Fin 13).val by simp; ring]; exact h _
  simp only [run5, List.map_cons, List.map_nil, capOf]
  rw [show σ (.n (O + 8)) = _ from (by simpa using e 0 (by omega)), e 1 (by omega), e 2 (by omega),
    e 3 (by omega), e 4 (by omega)]
  rfl

/-- The words a valuation meeting the template reads. -/
def omXs (σ : Val) (n : ℕ) : List E := (List.range n).map fun p ↦ σ (.n (omW p))

/-- The capacity it copies in. -/
def omCap0 (σ : Val) : List E := [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)]

/-- Group `g`'s rate cells read the group's waiting scalars. -/
theorem om_rate {n g : ℕ} (hg : 4 * g + 4 ≤ n)
    (hw : ∀ p < n, σ (.n (omW p + 1)) = σ (.n (omW p)) ∧ σ (.n (omW p + 2)) = word 0 dsObserve) :
    (omRate g).map σ = pendCells ((grp (omXs σ n) g).map (·, dsObserve)) := by
  rw [omXs, grp_map_range _ hg]
  simp only [List.map_cons, List.map_nil, om_pend4, omRate]
  rw [(hw _ (by omega)).1, (hw _ (by omega)).2, (hw (4 * g + 1) (by omega)).1,
    (hw (4 * g + 1) (by omega)).2, (hw (4 * g + 2) (by omega)).1, (hw (4 * g + 2) (by omega)).2,
    (hw (4 * g + 3) (by omega)).1, (hw (4 * g + 3) (by omega)).2]

/-- **The groups' permutations**: before group `g ≤ omK n` the capacity read is `stCap`, and
group `g < omK n`'s permutation writes the cells of `stF g`'s. -/
theorem om_mid {n nonce : ℕ} (hall : ∀ a ∈ omAtoms n nonce, a.Holds rd σ) :
    ∀ g ≤ omK n, (run5 (omCap g)).map σ = stCap (omCap0 σ) (omXs σ n) g ∧
      (g < omK n → ∀ c : Fin 13,
        σ (.n (omO g + c.val)) = cellsOfState (stF (omCap0 σ) (omXs σ n) g).perm false c) := by
  have hw : ∀ p < n, σ (.n (omW p + 1)) = σ (.n (omW p)) ∧ σ (.n (omW p + 2)) = word 0 dsObserve :=
    fun p hp ↦ by
      obtain ⟨-, a, b, -⟩ := om_word_holds fun x hx ↦ hall x (mem_omWord hp hx)
      exact ⟨a, b⟩
  have step : ∀ g < omK n, (run5 (omCap g)).map σ = stCap (omCap0 σ) (omXs σ n) g →
      ∀ c : Fin 13,
        σ (.n (omO g + c.val)) = cellsOfState (stF (omCap0 σ) (omXs σ n) g).perm false c := by
    intro g hg hc c
    have hk := hall _ (mem_omMid (nonce := nonce) hg)
    have hlen : (grp (omXs σ n) g).length = 4 := by
      rw [length_grp]; simp only [omXs, List.length_map, List.length_range]
      simp only [omK] at hg; omega
    have hout := keccakA_fs (s := stF (omCap0 σ) (omXs σ n) g) hk
      (by simp only [stF, List.length_map, hlen]; omega) (by
        rw [List.map_append, om_rate (by simp only [omK] at hg; omega) hw, hc]
        simp only [stF, List.length_map, hlen]
        simp)
      (by simp [run13])
    rw [← cells13_run13 σ (omO g) c, hout]
  intro g
  induction g with
  | zero =>
    intro _
    refine ⟨?_, fun h0 ↦ step 0 h0 ?_⟩ <;>
    · simp only [run5, omCap, List.map_cons, List.map_nil, stCap, omCap0]
      rw [show σ (.n 7) = σ (.n 0) from hall (.copy (.n 7) (.n 0)) (mem_omHead (by simp)),
        show σ (.n (7 + 1)) = σ (.n 1) from hall (.copy (.n 8) (.n 1)) (mem_omHead (by simp)),
        show σ (.n (7 + 2)) = σ (.n 2) from hall (.copy (.n 9) (.n 2)) (mem_omHead (by simp)),
        show σ (.n (7 + 3)) = σ (.n 3) from hall (.copy (.n 10) (.n 3)) (mem_omHead (by simp)),
        show σ (.n (7 + 4)) = σ (.n 4) from hall (.copy (.n 11) (.n 4)) (mem_omHead (by simp))]
  | succ g ih =>
    intro hg
    obtain ⟨hc, -⟩ := ih (by omega)
    have hB := step g (by omega) hc
    have hc' : (run5 (omCap (g + 1))).map σ = stCap (omCap0 σ) (omXs σ n) (g + 1) := by
      rw [stCap_succ, ← run5_cellsO hB]
      rfl
    exact ⟨hc', fun h ↦ step (g + 1) h hc'⟩


/-- The word facts a valuation meeting the template has. -/
theorem om_hw {n nonce : ℕ} (hall : ∀ a ∈ omAtoms n nonce, a.Holds rd σ) :
    ∀ p < n, σ (.n (omW p + 1)) = σ (.n (omW p)) ∧ σ (.n (omW p + 2)) = word 0 dsObserve :=
  fun p hp ↦ by
    obtain ⟨-, a, b, -⟩ := om_word_holds fun x hx ↦ hall x (mem_omWord hp hx)
    exact ⟨a, b⟩

/-- A full group's permutation, from the capacity before it. -/
theorem om_group {n g : ℕ} (hw : ∀ p < n, σ (.n (omW p + 1)) = σ (.n (omW p)) ∧
      σ (.n (omW p + 2)) = word 0 dsObserve)
    (hfull : 4 * g + 4 ≤ n) (hk : (omKeccak g).Holds rd σ)
    (hc : (run5 (omCap g)).map σ = stCap (omCap0 σ) (omXs σ n) g) :
    ∀ c : Fin 13,
      σ (.n (omO g + c.val)) = cellsOfState (stF (omCap0 σ) (omXs σ n) g).perm false c := by
  intro c
  have hlen : (grp (omXs σ n) g).length = 4 := by
    rw [length_grp]; simp only [omXs, List.length_map, List.length_range]; omega
  have hout := keccakA_fs (s := stF (omCap0 σ) (omXs σ n) g) hk
    (by simp only [stF, List.length_map, hlen]; omega) (by
      rw [List.map_append, om_rate hfull hw, hc]
      simp only [stF, List.length_map, hlen]
      simp)
    (by simp [run13])
  rw [← cells13_run13 σ (omO g) c, hout]

/-! ## The tails -/

/-- The four tails of the deployed messages: the words left after the full groups but the last,
and the nonce. -/
def OmCase (n nonce : ℕ) : Prop :=
  (nonce = 0 ∧ n - 4 * omK n = 4) ∨ (nonce = 0 ∧ n - 4 * omK n = 2) ∨
    (nonce = 1 ∧ n - 4 * omK n = 4) ∨ (nonce = 1 ∧ n - 4 * omK n = 1)

theorem omCase_deployed : ∀ p ∈ omDeployed, OmCase p.1 p.2 ∧ 1 ≤ p.1 ∧ p.1 + p.2 < 64 := by
  unfold OmCase omK
  decide

theorem omState_none (cap xs : List E) (hn : 1 ≤ xs.length) :
    omState cap xs none = (stF cap xs (omK xs.length)).perm := by
  rw [omState, absorbAll_groups cap xs hn]

theorem omState_some (cap xs : List E) (hn : 1 ≤ xs.length) (nn : E) :
    omState cap xs (some nn) = ((stF cap xs (omK xs.length)).absorb nn dsPowNonce).perm := by
  rw [omState, absorbAll_groups cap xs hn]
  rfl

theorem omXs_length (σ : Val) (n : ℕ) : (omXs σ n).length = n := by simp [omXs]

theorem padAs_holds {b : ℕ} (h : ∀ a ∈ padAs b, a.Holds rd σ) :
    σ (.n (b + 1)) = 0 ∧ σ (.n (b + 2)) = 0 ∧ σ (.n (b + 3)) = 0 ∧ σ (.n (b + 4)) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [← word_zero]
  · exact h (.const (.n (b + 1)) (word 0 0)) (by simp [padAs])
  · exact h (.const (.n (b + 2)) (word 0 0)) (by simp [padAs])
  · exact h (.const (.n (b + 3)) (word 0 0)) (by simp [padAs])
  · exact h (.const (.n (b + 4)) (word 0 0)) (by simp [padAs])

/-- **The tail's last permutation**: the cells of the message's last permutation (`omState`),
the nonce read at `cursor[n]` if there is one. -/
theorem om_tail {n nonce : ℕ} (hcase : OmCase n nonce) (hn : 1 ≤ n)
    (hall : ∀ a ∈ omAtoms n nonce, a.Holds rd σ) :
    ∃ nn : E, (nonce = 1 → LoadHolds rd (σ (.n 5)) n nn) ∧ ∀ c : Fin 13,
      σ (.n ((omTail n nonce).2.1 + c.val)) =
        cellsOfState (omState (omCap0 σ) (omXs σ n) (if nonce = 1 then some nn else none)) false c := by
  have hw := om_hw hall
  have hK := (om_mid hall (omK n) le_rfl).1
  have ht : ∀ a ∈ (omTail n nonce).1, a.Holds rd σ := fun a ha ↦ hall a (mem_omTail ha)
  have hxs : 1 ≤ (omXs σ n).length := by rw [omXs_length]; exact hn
  rcases hcase with ⟨rfl, h4⟩ | ⟨rfl, h2⟩ | ⟨rfl, h4⟩ | ⟨rfl, h1⟩
  · -- the last group full, no nonce
    refine ⟨0, by simp, fun c ↦ ?_⟩
    simp only [omTail, h4, ↓reduceIte] at ht ⊢
    rw [ite_eq_right (by decide), omState_none _ _ hxs, omXs_length]
    exact om_group hw (by omega) (ht _ (by simp)) hK c
  · -- two words left, no nonce
    refine ⟨0, by simp, fun c ↦ ?_⟩
    simp only [omTail, h2, ↓reduceIte, show (2 : ℕ) ≠ 4 by decide] at ht ⊢
    rw [ite_eq_right (by decide), omState_none _ _ hxs, omXs_length]
    obtain ⟨z1, z2, z3, z4⟩ := padAs_holds (b := omE n) fun a ha ↦ ht a (by simp [ha])
    have hk := ht _ (List.mem_append_right _ (List.mem_singleton_self _))
    have hg : grp (omXs σ n) (omK n) = [σ (.n (omW (4 * omK n))), σ (.n (omW (4 * omK n + 1)))] := by
      rw [omXs, grp_map_range_last _ (by omega) (by omega), h2]
      rfl
    have hout := keccakA_fs (s := stF (omCap0 σ) (omXs σ n) (omK n)) hk
      (by simp [stF, hg]) (by
        rw [List.map_append, hK]
        simp only [stF, hg, List.map_cons, List.map_nil, List.length_cons, List.length_nil]
        rw [(hw _ (by omega)).1, (hw _ (by omega)).2, (hw (4 * omK n + 1) (by omega)).1,
          (hw (4 * omK n + 1) (by omega)).2, z1, z2, z3, z4]
        rfl)
      (by simp [run13])
    rw [← cells13_run13 σ _ c, hout]
  · -- the last group full, then the nonce
    simp only [omTail, h4, ↓reduceIte, show (1 : ℕ) ≠ 0 by decide] at ht ⊢
    have he : omE n = omO (omK n) := by simp only [omE, omO, omK] at h4 ⊢; omega
    have hB := om_group hw (by omega) (ht _ (by simp)) hK
    have l13 : LoadHolds rd (σ (.n 5)) n (σ (.n (omE n + 13))) := ht (.load (.n (omE n + 13)) (.n 5) n) (by simp)
    have c14 : σ (.n (omE n + 14)) = σ (.n (omE n + 13)) := ht (.copy (.n (omE n + 14)) (.n (omE n + 13))) (by simp)
    have c15 : σ (.n (omE n + 15)) = word 0 dsPowNonce := ht (.const (.n (omE n + 15)) (word 0 dsPowNonce)) (by simp)
    obtain ⟨z1, z2, z3, z4⟩ := padAs_holds (b := omE n + 16) fun a ha ↦ ht a (by simp [ha])
    refine ⟨σ (.n (omE n + 13)), fun _ ↦ l13, fun c ↦ ?_⟩
    rw [omState_some _ _ hxs, omXs_length]
    have hfull : (stF (omCap0 σ) (omXs σ n) (omK n)).pend.length = 4 := by
      simp only [stF, List.length_map, length_grp, omXs_length]; omega
    have habs : (stF (omCap0 σ) (omXs σ n) (omK n)).absorb (σ (.n (omE n + 13))) dsPowNonce =
        ⟨capOf (stF (omCap0 σ) (omXs σ n) (omK n)).perm, [(σ (.n (omE n + 13)), dsPowNonce)]⟩ := by
      simp [Fs.absorb, hfull, rateScalars]
    have hk := ht _ (List.mem_append_right _ (List.mem_singleton_self _))
    have hout := keccakA_fs (s := ⟨capOf (stF (omCap0 σ) (omXs σ n) (omK n)).perm,
      [(σ (.n (omE n + 13)), dsPowNonce)]⟩) hk (by simp) (by
        rw [List.map_append, he, ← run5_cellsO hB, ← he]
        simp only [List.map_cons, List.map_nil, List.length_cons, List.length_nil]
        rw [c14, c15, show omE n + 17 = omE n + 16 + 1 by ring, z1,
          show omE n + 18 = omE n + 16 + 2 by ring, z2, show omE n + 19 = omE n + 16 + 3 by ring, z3,
          show omE n + 20 = omE n + 16 + 4 by ring, z4]
        rfl)
      (by simp [run13])
    rw [habs, ← cells13_run13 σ _ c, hout]
  · -- one word left, then the nonce
    simp only [omTail, h1, ↓reduceIte, show (1 : ℕ) ≠ 0 by decide, show (1 : ℕ) ≠ 4 by decide] at ht ⊢
    have l0 : LoadHolds rd (σ (.n 5)) n (σ (.n (omE n))) := ht (.load (.n (omE n)) (.n 5) n) (by simp)
    have c1 : σ (.n (omE n + 1)) = σ (.n (omE n)) := ht (.copy (.n (omE n + 1)) (.n (omE n))) (by simp)
    have c2 : σ (.n (omE n + 2)) = word 0 dsPowNonce := ht (.const (.n (omE n + 2)) (word 0 dsPowNonce)) (by simp)
    obtain ⟨z1, z2, z3, z4⟩ := padAs_holds (b := omE n + 3) fun a ha ↦ ht a (by simp [ha])
    refine ⟨σ (.n (omE n)), fun _ ↦ l0, fun c ↦ ?_⟩
    rw [omState_some _ _ hxs, omXs_length]
    have hg : grp (omXs σ n) (omK n) = [σ (.n (omW (4 * omK n)))] := by
      rw [omXs, grp_map_range_last _ (by omega) (by omega), h1]
      rfl
    have habs : (stF (omCap0 σ) (omXs σ n) (omK n)).absorb (σ (.n (omE n))) dsPowNonce =
        ⟨stCap (omCap0 σ) (omXs σ n) (omK n), [(σ (.n (omW (4 * omK n))), dsObserve),
          (σ (.n (omE n)), dsPowNonce)]⟩ := by
      simp [Fs.absorb, stF, hg, rateScalars]
    have hk := ht _ (List.mem_append_right _ (List.mem_singleton_self _))
    have hout := keccakA_fs (s := ⟨stCap (omCap0 σ) (omXs σ n) (omK n),
      [(σ (.n (omW (4 * omK n))), dsObserve), (σ (.n (omE n)), dsPowNonce)]⟩) hk (by simp) (by
        rw [List.map_append, hK]
        simp only [List.map_cons, List.map_nil, List.length_cons, List.length_nil]
        rw [(hw _ (by omega)).1, (hw _ (by omega)).2, c1, c2,
          show omE n + 4 = omE n + 3 + 1 by ring, z1, show omE n + 5 = omE n + 3 + 2 by ring, z2,
          show omE n + 6 = omE n + 3 + 3 by ring, z3, show omE n + 7 = omE n + 3 + 4 by ring, z4]
        rfl)
      (by simp [run13])
    rw [habs, ← cells13_run13 σ _ c, hout]


/-! ## Soundness -/

/-- What the copies out and the cursor's step ask. -/
theorem om_final_holds {n nonce O f : ℕ} (h : ∀ a ∈ omFinal n nonce O f, a.Holds rd σ) :
    σ (.n f) = σ (.n O) ∧ σ (.n (f + 1)) = σ (.n (O + 1)) ∧ σ (.n (f + 2)) = σ (.n (O + 8)) ∧
      σ (.n (f + 3)) = σ (.n (O + 9)) ∧ σ (.n (f + 4)) = σ (.n (O + 10)) ∧
      σ (.n (f + 5)) = σ (.n (O + 11)) ∧ σ (.n (f + 6)) = σ (.n (O + 12)) ∧
      σ (.n (f + 9)) = σ (.n 5) * word (2 ^ (n + nonce)) 0 := by
  refine ⟨h (.copy (.n f) (.n O)) (by simp [omFinal]),
    h (.copy (.n (f + 1)) (.n (O + 1))) (by simp [omFinal]),
    h (.copy (.n (f + 2)) (.n (O + 8))) (by simp [omFinal]),
    h (.copy (.n (f + 3)) (.n (O + 9))) (by simp [omFinal]),
    h (.copy (.n (f + 4)) (.n (O + 10))) (by simp [omFinal]),
    h (.copy (.n (f + 5)) (.n (O + 11))) (by simp [omFinal]),
    h (.copy (.n (f + 6)) (.n (O + 12))) (by simp [omFinal]), ?_⟩
  have e9 : σ (.n (f + 9)) = σ (.n (f + 8)) := h (.copy (.n (f + 9)) (.n (f + 8))) (by simp [omFinal])
  have e8 : σ (.n (f + 8)) = σ (.n 5) * σ (.n (f + 7)) :=
    h (.mul (.n (f + 8)) (.n 5) (.n (f + 7))) (by simp [omFinal])
  have e7 : σ (.n (f + 7)) = word (2 ^ (n + nonce)) 0 :=
    h (.const (.n (f + 7)) (word (2 ^ (n + nonce)) 0)) (by simp [omFinal])
  rw [e9, e8, e7]

/-- A permutation's cells as the message returns them: cells `0`, `1`, then its capacity. -/
theorem om_cells_ret {O : ℕ} {S : KeccakState}
    (hO : ∀ c : Fin 13, σ (.n (O + c.val)) = cellsOfState S false c) :
    [σ (.n O), σ (.n (O + 1)), σ (.n (O + 8)), σ (.n (O + 9)), σ (.n (O + 10)), σ (.n (O + 11)),
      σ (.n (O + 12))] = [cellsOfState S false 0, cellsOfState S false 1] ++ capOf S := by
  have e : ∀ i (hi : i < 13), σ (.n (O + i)) = cellsOfState S false ⟨i, hi⟩ := fun i hi ↦ hO ⟨i, hi⟩
  rw [show σ (.n O) = _ from (by simpa using e 0 (by omega)), e 1 (by omega), e 8 (by omega),
    e 9 (by omega), e 10 (by omega), e 11 (by omega), e 12 (by omega)]
  rfl

/-- **`opening_message` is sound.** -/
theorem om_sound {name : String} {f : Fn} (n nonce : ℕ) (hcase : OmCase n nonce) (hn : 1 ≤ n)
    (h64 : n + nonce < 64) (hfind : coreProgram.find? name = some f)
    (hparams : f.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6])
    (hbody : f.body = omBody n nonce) (rd : Reader) (args rets : List E)
    (h : coreProgram.Rel rd name args rets) : MeaningOpeningMessage n nonce rd args rets := by
  rw [rel_iff_sem hfind, hbody, hparams, omBody] at h
  obtain ⟨σ, hp, hh⟩ := h
  rw [holdsList_atomsRet] at hh
  obtain ⟨hall, hret⟩ := hh
  subst hp
  obtain ⟨nn, hnn, hO⟩ := om_tail hcase hn hall
  have hwd : ∀ p < n, LoadHolds rd (σ (.n 5)) p (σ (.n (omW p))) ∧
      LoadHolds rd (σ (.n 6)) p (σ (.n (omW p))) := fun p hp ↦ by
    obtain ⟨a, -, -, b⟩ := om_word_holds fun x hx ↦ hall x (mem_omWord hp hx)
    exact ⟨a, b⟩
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f9⟩ := om_final_holds fun a ha ↦ hall a (mem_omFinal ha)
  simp only [List.map_cons, List.map_nil]
  refine ⟨omXs σ n, omXs_length σ n, fun k hk ↦ ?_, fun k hk ↦ ?_, nn, hnn, ?_⟩
  · rw [omXs_length] at hk
    simpa [omXs] using (hwd k hk).1
  · rw [omXs_length] at hk
    simpa [omXs] using (hwd k hk).2
  · have hO' := om_cells_ret hO
    simp only [omCap0] at hO'
    rw [← hret, ← hO', ← word_two_pow h64]
    simp only [omRets, List.map_cons, List.map_nil, f0, f1, f2, f3, f4, f5, f6, f9,
      List.cons_append, List.nil_append]

end
end LeanVM.Guest.B1
