/-
  LeanVM.Protocol.Compile.Rom.Extract

  Word extraction: the matrix a Merkle root commits to, read off the random oracle's answers,
  and the facts the random-oracle theorem needs of it: every accepted opening reads the
  extracted row, and, without failure, the word extracted from the log before the root was
  absorbed is the word extracted from the whole log.
-/

module

public import LeanVM.Protocol.Compile.Rom.Log

/-!
# Word extraction from the random oracle

The compiled verifier authenticates a row by climbing a Merkle path to a root
(`LeanVM.Protocol.Compile.Run`, `openOne`). The random-oracle theorem replaces each commitment
of the interactive reading by the word the oracle's answers determine under the root
(`extract`): at position `p`, an opening that climbs to the root at `p` through answered
queries, if there is one, gives the row; otherwise the row is zero. Extracted words are well
shaped (`wellShaped_extract`).

The hash is a partial function `H : Bytes → Option Digest` (the answers recorded so far); the
climb runs in `Option`, a missing answer failing it.

* **Openings read the extracted rows** (`extract_eq_of_openOne`). If `H` is injective on its
  answers (no collision), an accepted opening at position `q` has the leaf the extraction
  chooses at `q mod 2^height`: two climbs to one root through injective answers pass through
  the same nodes (`climb_inj`), and leaves of one length with one hash are equal.
* **Extraction is stable** (`extract_take_eq`). Without failure, if every entry answering the
  root comes before the `j`-th, the word extracted from the first `j` entries is the word
  extracted from the whole log: each node of an accepted climb is an aligned chunk of its
  parent's input, so its entry comes before the parent's (`climb_take`).
-/

namespace LeanVM.Protocol.Compile.Rom

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Rom

@[expose] public section

/-! ## Climbs through partial answers -/

/-- One level of a climb: the parent's input at the position's low bit. -/
def nodeInput (node s : Digest) (q : ℕ) : Bytes :=
  if q % 2 = 0 then digestBytes node ++ digestBytes s else digestBytes s ++ digestBytes node

theorem climb_cons (H : Bytes → Option Digest) (node : Digest) (q : ℕ) (s : Digest)
    (ss : List Digest) :
    climb (m := Option) H node q (s :: ss) =
      (H (nodeInput node s q)).bind fun p ↦ climb (m := Option) H p (q / 2) ss := by
  simp only [climb, nodeInput]
  split <;> rfl

theorem nodeInput_mod (node s : Digest) (q n : ℕ) (hn : n ≠ 0) :
    nodeInput node s (q % 2 ^ n) = nodeInput node s q := by
  simp only [nodeInput, Nat.mod_mod_of_dvd q (dvd_pow_self 2 hn)]

/-- A climb reads the position modulo two to the length of the path. -/
theorem climb_mod (H : Bytes → Option Digest) :
    ∀ (node : Digest) (q : ℕ) (path : List Digest),
      climb (m := Option) H node q path = climb (m := Option) H node (q % 2 ^ path.length) path
  | _, _, [] => rfl
  | node, q, s :: ss => by
    rw [climb_cons, climb_cons, List.length_cons, nodeInput_mod _ _ _ _ (Nat.succ_ne_zero _)]
    have hd : q % 2 ^ (ss.length + 1) / 2 % 2 ^ ss.length = q / 2 % 2 ^ ss.length := by
      rw [pow_succ', Nat.mod_mul_right_div_self, Nat.mod_mod]
    congr 1
    funext p
    rw [climb_mod H p (q / 2) ss, climb_mod H p (q % 2 ^ (ss.length + 1) / 2) ss, hd]

/-- The node input determines the node, given the sibling side. -/
theorem nodeInput_inj {n n' s s' : Digest} {q : ℕ}
    (h : nodeInput n s q = nodeInput n' s' q) : n = n' := by
  unfold nodeInput at h
  split at h
  · exact (pairInput_inj h).1
  · exact (pairInput_inj h).2

/-- Answers that are injective: one answer, one input. -/
def AnswersInj (H : Bytes → Option Digest) : Prop :=
  ∀ x y v, H x = some v → H y = some v → x = y

/-- Two climbs of one length to one root through injective answers start at one node. -/
theorem climb_inj {H : Bytes → Option Digest} (hH : AnswersInj H) {r : Digest} :
    ∀ (path path' : List Digest) (n n' : Digest) (q : ℕ), path.length = path'.length →
      climb (m := Option) H n q path = some r → climb (m := Option) H n' q path' = some r →
        n = n'
  | [], [], n, n', _, _, h, h' => by
    simp only [climb] at h h'
    exact (Option.some.inj h).trans (Option.some.inj h').symm
  | s :: ss, s' :: ss', n, n', q, hl, h, h' => by
    rw [climb_cons, Option.bind_eq_some_iff] at h h'
    obtain ⟨p, hp, hc⟩ := h
    obtain ⟨p', hp', hc'⟩ := h'
    have := climb_inj hH ss ss' p p' (q / 2) (by simpa using hl) hc hc'
    subst this
    exact nodeInput_inj (hH _ _ _ hp hp')

/-- An accepted opening: the shapes match, the leaf is answered, and the climb reaches the
root. -/
theorem openOne_eq_some_true_iff (H : Bytes → Option Digest) (r : Digest) (ht w q : ℕ)
    (o : Opening) :
    openOne (m := Option) H r ht w q o = some true ↔
      o.leaf.length = w ∧ o.path.length = ht ∧ ∃ ld, H (o.leaf.flatMap kBytes) = some ld ∧
        climb (m := Option) H ld q o.path = some r := by
  unfold openOne
  by_cases hs : o.leaf.length = w ∧ o.path.length = ht
  · simp only [hs, and_self, ↓reduceIte, true_and]
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq, decide_eq_true_eq,
      Vector.toList_inj]
    constructor
    · rintro ⟨ld, hld, top, htop, rfl⟩
      exact ⟨ld, hld, htop⟩
    · rintro ⟨ld, hld, htop⟩
      exact ⟨ld, hld, r, htop, rfl⟩
  · simp only [hs, ↓reduceIte, pure, Option.some.injEq, Bool.false_eq_true, false_iff]
    tauto

/-! ## Extraction -/

open Classical in
/-- The leaf of an opening with the property `A`, if any, and the zero row of width `w`
otherwise. -/
noncomputable def pickLeaf (A : Opening → Prop) (w : ℕ) : List K :=
  if h : ∃ o, A o then (Classical.choose h).leaf else List.replicate w 0

/-- The word a root commits to under the answers `H`: at position `p`, the leaf of an accepted
opening at `p`, if any, and the zero row of the width otherwise. -/
noncomputable def extract (H : Bytes → Option Digest) (r : Digest) (ht w : ℕ) : Word := fun p ↦
  pickLeaf (fun o ↦ openOne (m := Option) H r ht w p o = some true) w

/-- Extracted words are well shaped. -/
theorem wellShaped_extract (H : Bytes → Option Digest) (r : Digest) (ht w : ℕ) :
    WellShaped w (extract H r ht w) := by
  intro p
  unfold extract pickLeaf
  split
  · rename_i h
    exact ((openOne_eq_some_true_iff _ _ _ _ _ _).mp (Classical.choose_spec h)).1
  · simp

/-- Two accepted openings at one position through injective answers have one leaf. -/
theorem leaf_eq_of_openOne {H : Bytes → Option Digest} (hH : AnswersInj H) {r : Digest}
    {ht w q : ℕ} {o o' : Opening} (h : openOne (m := Option) H r ht w q o = some true)
    (h' : openOne (m := Option) H r ht w q o' = some true) : o.leaf = o'.leaf := by
  rw [openOne_eq_some_true_iff] at h h'
  obtain ⟨hw, hl, ld, hld, hc⟩ := h
  obtain ⟨hw', hl', ld', hld', hc'⟩ := h'
  have := climb_inj hH _ _ ld ld' q (hl.trans hl'.symm) hc hc'
  subst this
  exact flatMap_kBytes_inj (hw.trans hw'.symm) (hH _ _ _ hld hld')

/-- An accepted opening at `q` is accepted at `q mod 2^height`. -/
theorem openOne_mod {H : Bytes → Option Digest} {r : Digest} {ht w q : ℕ} {o : Opening}
    (h : openOne (m := Option) H r ht w q o = some true) :
    openOne (m := Option) H r ht w (q % 2 ^ ht) o = some true := by
  rw [openOne_eq_some_true_iff] at h ⊢
  obtain ⟨hw, hl, ld, hld, hc⟩ := h
  refine ⟨hw, hl, ld, hld, ?_⟩
  rw [climb_mod, hl, Nat.mod_mod, ← hl, ← climb_mod]
  exact hc

/-- **An accepted opening reads the extracted row.** -/
theorem extract_eq_of_openOne {H : Bytes → Option Digest} (hH : AnswersInj H) {r : Digest}
    {ht w q : ℕ} {o : Opening} (h : openOne (m := Option) H r ht w q o = some true) :
    extract H r ht w (q % 2 ^ ht) = o.leaf := by
  have hm := openOne_mod h
  unfold extract pickLeaf
  split
  · rename_i hex
    exact leaf_eq_of_openOne hH (Classical.choose_spec hex) hm
  · rename_i hex
    exact absurd ⟨o, hm⟩ hex

/-! ## Stability of extraction -/

/-- More answers keep every climb. -/
theorem climb_mono {H H' : Bytes → Option Digest} (hH : ∀ x v, H x = some v → H' x = some v) :
    ∀ (n : Digest) (q : ℕ) (path : List Digest) (r : Digest),
      climb (m := Option) H n q path = some r → climb (m := Option) H' n q path = some r
  | _, _, [], _, h => h
  | n, q, s :: ss, r, h => by
    rw [climb_cons, Option.bind_eq_some_iff] at h ⊢
    obtain ⟨p, hp, hc⟩ := h
    exact ⟨p, hH _ _ hp, climb_mono hH p (q / 2) ss r hc⟩

/-- More answers keep every accepted opening. -/
theorem openOne_mono {H H' : Bytes → Option Digest} (hH : ∀ x v, H x = some v → H' x = some v)
    {r : Digest} {ht w q : ℕ} {o : Opening} (h : openOne (m := Option) H r ht w q o = some true) :
    openOne (m := Option) H' r ht w q o = some true := by
  rw [openOne_eq_some_true_iff] at h ⊢
  obtain ⟨hw, hl, ld, hld, hc⟩ := h
  exact ⟨hw, hl, ld, hH _ _ hld, climb_mono hH _ _ _ _ hc⟩

/-- The answers of a log without collisions are injective. -/
theorem answersInj_look {X : Type} {σ : Seeds X} {ℓ : Log} (hf : ¬ Fail σ ℓ) :
    AnswersInj (look ℓ) := by
  intro x y v hx hy
  obtain ⟨i, hi, hei, -⟩ := (look_eq_some_iff ℓ x v).mp hx
  obtain ⟨j, hj, hej, -⟩ := (look_eq_some_iff ℓ y v).mp hy
  have := index_eq_of_output hf hi hj (by rw [hei, hej])
  subst this
  rw [hei] at hej
  exact (Prod.mk.inj hej).1

/-- Without failure, a climb in the log whose root's entries all come before the `j`-th is a
climb in the first `j` entries, and so are the entries of its start. -/
theorem climb_take {X : Type} {σ : Seeds X} {ℓ : Log} (hf : ¬ Fail σ ℓ) {j : ℕ} {r : Digest}
    (hr : ∀ (i : ℕ) (hi : i < ℓ.length), ℓ[i].2 = r → i < j) :
    ∀ (path : List Digest) (n : Digest) (q : ℕ),
      climb (m := Option) (look ℓ) n q path = some r →
        climb (m := Option) (look (ℓ.take j)) n q path = some r ∧
          ∀ (i : ℕ) (hi : i < ℓ.length), ℓ[i].2 = n → i < j
  | [], n, q, h => by
    simp only [climb, pure, Option.some.injEq] at h
    subst h
    exact ⟨rfl, hr⟩
  | s :: ss, n, q, h => by
    rw [climb_cons, Option.bind_eq_some_iff] at h
    obtain ⟨p, hp, hc⟩ := h
    obtain ⟨hc', hpj⟩ := climb_take hf hr ss p (q / 2) hc
    obtain ⟨k, hk, hek, hn⟩ := (look_eq_some_iff ℓ _ p).mp hp
    have hkj : k < j := hpj k hk (by rw [hek])
    refine ⟨?_, fun i hi hin ↦ ?_⟩
    · rw [climb_cons, look_take_of_first hk hek hn hkj]
      exact hc'
    · refine lt_trans (lt_of_chunk hf hi hk ?_) hkj
      rw [hek, hin]
      unfold nodeInput
      split
      · exact Or.inl (chunk0_append _ _)
      · exact Or.inr (chunk1_append _ _)

/-- Without failure, an accepted opening in the log is accepted in the first `j` entries, if
every entry answering the root comes before the `j`-th. -/
theorem openOne_take {X : Type} {σ : Seeds X} {ℓ : Log} (hf : ¬ Fail σ ℓ) {j : ℕ} {r : Digest}
    (hr : ∀ (i : ℕ) (hi : i < ℓ.length), ℓ[i].2 = r → i < j) {ht w q : ℕ} {o : Opening}
    (h : openOne (m := Option) (look ℓ) r ht w q o = some true) :
    openOne (m := Option) (look (ℓ.take j)) r ht w q o = some true := by
  rw [openOne_eq_some_true_iff] at h ⊢
  obtain ⟨hw, hl, ld, hld, hc⟩ := h
  obtain ⟨hc', hldj⟩ := climb_take hf hr o.path ld q hc
  obtain ⟨k, hk, hek, hn⟩ := (look_eq_some_iff ℓ _ ld).mp hld
  exact ⟨hw, hl, ld, look_take_of_first hk hek hn (hldj k hk (by rw [hek])), hc'⟩

/-- **Extraction is stable.** Without failure, if every entry answering the root comes before
the `j`-th, the word extracted from the first `j` entries is the word extracted from the
log. -/
theorem extract_take_eq {X : Type} {σ : Seeds X} {ℓ : Log} (hf : ¬ Fail σ ℓ) {j : ℕ} {r : Digest}
    (hr : ∀ (i : ℕ) (hi : i < ℓ.length), ℓ[i].2 = r → i < j) (ht w : ℕ) :
    extract (look (ℓ.take j)) r ht w = extract (look ℓ) r ht w := by
  have hpre : ∀ x v, look (ℓ.take j) x = some v → look ℓ x = some v := fun x v h ↦
    look_of_prefix (List.take_prefix j ℓ) h
  have heq : ∀ p, (fun o ↦ openOne (m := Option) (look (ℓ.take j)) r ht w p o = some true) =
      (fun o ↦ openOne (m := Option) (look ℓ) r ht w p o = some true) := fun p ↦
    funext fun o ↦ propext ⟨openOne_mono hpre, openOne_take hf hr⟩
  funext p
  show pickLeaf _ w = pickLeaf _ w
  rw [heq p]

end
end LeanVM.Protocol.Compile.Rom
