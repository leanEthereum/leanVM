/-
  LeanVM.Guest.B1.FoldFinal

  B1 for `fold_final_msg`: the multilinear evaluation of the final message, at each of its
  specializations, one generic argument over the message log.
-/

module

public import LeanVM.Guest.B1.RowWeights

/-!
# `fold_final_msg` (TRIAGE #24)

`fold_final_msg(msg, point, log_len)` (G:815-831) reads `log_len` coordinates, keeps the weights
`1 + p_j` and `p_j`, folds the `2^log_len` message words pairwise at `p_0`, then each level at
`p_j`, and returns the last value: `multilinearEval msg point` (V:687). Its expansion: `ffW j`
per weight, `ff0` per pair of the first level (with its loads), `ffPairs` per later level
(threaded by `ffLevels`); `ffBody L fin` is equal to the four specializations by kernel
evaluation.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-! ## The template -/

/-- The weights of coordinate `j`: `1 + p_j` at `4 + 4j`, `p_j` at `5 + 4j`. -/
def ffW (j : ℕ) : List Stmt :=
  [.atom (.const (.n (2 + 4 * j)) (word 1 0 0)), .atom (.load (.n (3 + 4 * j)) (.n 1) j),
    .atom (.add (.n (4 + 4 * j)) (.n (2 + 4 * j)) (.n (3 + 4 * j))),
    .atom (.load (.n (5 + 4 * j)) (.n 1) j)]

/-- Pair `t` of the first level, its words read at `msg`, from the value `S`. -/
def ff0 (S t : ℕ) : List Stmt :=
  [.atom (.load (.n (S + 5 * t)) (.n 0) (2 * t)), .atom (.mul (.n (S + 5 * t + 1)) (.n 4) (.n (S + 5 * t))),
    .atom (.load (.n (S + 5 * t + 2)) (.n 0) (2 * t + 1)),
    .atom (.mul (.n (S + 5 * t + 3)) (.n 5) (.n (S + 5 * t + 2))),
    .atom (.add (.n (S + 5 * t + 4)) (.n (S + 5 * t + 1)) (.n (S + 5 * t + 3)))]

/-- A later level: the pairs of `cur` folded with the weights `w0`, `w1`, from the value `s`. -/
def ffPairs (w0 w1 : V) : ℕ → List V → List Stmt × List V
  | s, a :: b :: rest =>
    ([.atom (.mul (.n s) w0 a), .atom (.mul (.n (s + 1)) w1 b),
      .atom (.add (.n (s + 2)) (.n s) (.n (s + 1)))] ++ (ffPairs w0 w1 (s + 3) rest).1,
      .n (s + 2) :: (ffPairs w0 w1 (s + 3) rest).2)
  | _, _ => ([], [])

/-- `f` later levels from coordinate `j`, the value `s`, the current level `cur`. -/
def ffLevels : ℕ → ℕ → ℕ → List V → List Stmt × List V
  | 0, _, _, cur => ([], cur)
  | f + 1, j, s, cur =>
    ((ffPairs (.n (4 + 4 * j)) (.n (5 + 4 * j)) s cur).1 ++
        (ffLevels f (j + 1) (s + 3 * (ffPairs (.n (4 + 4 * j)) (.n (5 + 4 * j)) s cur).2.length)
          (ffPairs (.n (4 + 4 * j)) (.n (5 + 4 * j)) s cur).2).1,
      (ffLevels f (j + 1) (s + 3 * (ffPairs (.n (4 + 4 * j)) (.n (5 + 4 * j)) s cur).2.length)
          (ffPairs (.n (4 + 4 * j)) (.n (5 + 4 * j)) s cur).2).2)

/-- The outputs of the first level. -/
def ffOut0 (S m : ℕ) : List V := (List.range m).map fun t => .n (S + 5 * t + 4)

/-- The expansion of `fold_final_msg` at `L + 1`, its last value `fin`. -/
def ffBody (L fin : ℕ) : List Stmt :=
  ((List.range (L + 1)).map ffW).flatten ++ ((List.range (2 ^ L)).map (ff0 (6 + 4 * L))).flatten ++
    (ffLevels L 1 (6 + 4 * L + 5 * 2 ^ L) (ffOut0 (6 + 4 * L) (2 ^ L))).1 ++
    [.atom (.copy (.n (fin + 1)) (.n fin)), .ret [.n (fin + 1)]]

theorem core618_body : Fn.body Data.core618 = ffBody 1 22 := stmtsEqb_sound (by decide +kernel)

theorem core633_body : Fn.body Data.core633 = ffBody 2 42 := stmtsEqb_sound (by decide +kernel)

theorem core591_body : Fn.body Data.core591 = ffBody 3 78 := stmtsEqb_sound (by decide +kernel)

theorem core604_body : Fn.body Data.core604 = ffBody 4 146 := stmtsEqb_sound (by decide +kernel)

/-! ## What it asks -/

/-- What a later level asks. -/
def FfPairsOk (σ : Val) (w0 w1 : V) : ℕ → List V → Prop
  | s, a :: b :: rest => σ (.n s) = σ w0 * σ a ∧ σ (.n (s + 1)) = σ w1 * σ b ∧
      σ (.n (s + 2)) = σ (.n s) + σ (.n (s + 1)) ∧ FfPairsOk σ w0 w1 (s + 3) rest
  | _, _ => True

theorem holds_ffPairs (w0 w1 : V) (next : Prop) (kret : List E → Prop) :
    ∀ s cur, Stmt.HoldsList C rd σ (ffPairs w0 w1 s cur).1 next kret ↔ FfPairsOk σ w0 w1 s cur ∧ next
  | s, a :: b :: rest => by
    rw [ffPairs, holdsList_append, holds_ffPairs w0 w1 next kret (s + 3) rest]
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, FfPairsOk]
    tauto
  | s, [] => by simp [ffPairs, FfPairsOk, Stmt.HoldsList]
  | s, [_] => by simp [ffPairs, FfPairsOk, Stmt.HoldsList]

/-- What the later levels ask. -/
def FfLevelsOk (σ : Val) : ℕ → ℕ → ℕ → List V → Prop
  | 0, _, _, _ => True
  | f + 1, j, s, cur => FfPairsOk σ (.n (4 + 4 * j)) (.n (5 + 4 * j)) s cur ∧
      FfLevelsOk σ f (j + 1) (s + 3 * (ffPairs (.n (4 + 4 * j)) (.n (5 + 4 * j)) s cur).2.length)
        (ffPairs (.n (4 + 4 * j)) (.n (5 + 4 * j)) s cur).2

theorem holds_ffLevels (next : Prop) (kret : List E → Prop) :
    ∀ f j s cur, Stmt.HoldsList C rd σ (ffLevels f j s cur).1 next kret ↔ FfLevelsOk σ f j s cur ∧ next
  | 0, _, _, _ => by simp [ffLevels, FfLevelsOk, Stmt.HoldsList]
  | f + 1, j, s, cur => by
    rw [ffLevels, holdsList_append, holds_ffPairs, holds_ffLevels next kret f, FfLevelsOk]
    tauto

/-! ## The values -/

/-- A level folded with the weights `u`, `v`: `u·a + v·b` per pair. -/
def gPairs (u v : E) : List E → List E
  | a :: b :: rest => (u * a + v * b) :: gPairs u v rest
  | _ => []

theorem gPairs_eq_foldPairs (r : E) : ∀ l, gPairs (1 + r) r l = foldPairs r l
  | a :: b :: rest => by rw [gPairs, foldPairs, gPairs_eq_foldPairs r rest]; ring_nf
  | [] => rfl
  | [_] => rfl

theorem ffPairs_value (w0 w1 : V) :
    ∀ s cur, FfPairsOk σ w0 w1 s cur → (ffPairs w0 w1 s cur).2.map σ = gPairs (σ w0) (σ w1) (cur.map σ)
  | s, a :: b :: rest, ⟨h0, h1, h2, hr⟩ => by
    rw [ffPairs, List.map_cons, ffPairs_value w0 w1 (s + 3) rest hr, h2, h0, h1]
    rfl
  | _, [], _ => rfl
  | _, [_], _ => rfl

theorem length_ffPairs (w0 w1 : V) : ∀ s cur, (ffPairs w0 w1 s cur).2.length = cur.length / 2
  | s, a :: b :: rest => by
    rw [ffPairs, List.length_cons, length_ffPairs w0 w1 (s + 3) rest]
    simp only [List.length_cons]; omega
  | _, [] => rfl
  | _, [_] => by simp [ffPairs]

/-- The later levels fold the current values at the coordinates `p j, p (j + 1), …`, whose weights
are `1 + p j` and `p j`. -/
theorem ffLevels_value (p : ℕ → E) :
    ∀ f j s cur, (∀ i, j ≤ i → i < j + f → σ (.n (4 + 4 * i)) = 1 + p i ∧ σ (.n (5 + 4 * i)) = p i) →
      FfLevelsOk σ f j s cur →
      (ffLevels f j s cur).2.map σ = ((List.range f).map fun i => p (j + i)).foldl
        (fun l r => foldPairs r l) (cur.map σ)
  | 0, _, _, _, _, _ => rfl
  | f + 1, j, s, cur, hw, ⟨hp, hr⟩ => by
    rw [ffLevels, ffLevels_value p f (j + 1) _ _ (fun i h1 h2 => hw i (by omega) (by omega)) hr,
      ffPairs_value _ _ _ _ hp, (hw j le_rfl (by omega)).1, (hw j le_rfl (by omega)).2,
      gPairs_eq_foldPairs, List.range_succ_eq_map, List.map_cons, List.foldl_cons, List.map_map]
    simp only [Nat.add_zero, Function.comp_def]
    congr 2
    funext i
    rw [show j + (i + 1) = j + 1 + i by omega]

/-! ## The first levels, the weights, the body -/

/-- What weight `j` asks. -/
def FfWOk (rd : Reader) (σ : Val) (j : ℕ) : Prop :=
  σ (.n (2 + 4 * j)) = 1 ∧ LoadHolds rd (σ (.n 1)) j (σ (.n (3 + 4 * j))) ∧
    σ (.n (4 + 4 * j)) = σ (.n (2 + 4 * j)) + σ (.n (3 + 4 * j)) ∧
    LoadHolds rd (σ (.n 1)) j (σ (.n (5 + 4 * j)))

/-- What pair `t` of the first level asks. -/
def Ff0Ok (rd : Reader) (σ : Val) (S t : ℕ) : Prop :=
  LoadHolds rd (σ (.n 0)) (2 * t) (σ (.n (S + 5 * t))) ∧
    σ (.n (S + 5 * t + 1)) = σ (.n 4) * σ (.n (S + 5 * t)) ∧
    LoadHolds rd (σ (.n 0)) (2 * t + 1) (σ (.n (S + 5 * t + 2))) ∧
    σ (.n (S + 5 * t + 3)) = σ (.n 5) * σ (.n (S + 5 * t + 2)) ∧
    σ (.n (S + 5 * t + 4)) = σ (.n (S + 5 * t + 1)) + σ (.n (S + 5 * t + 3))

theorem ffBody_holds (L fin : ℕ) (rets : List E) :
    Stmt.HoldsList C rd σ (ffBody L fin) False (fun rs => rs = rets) ↔
      (∀ j < L + 1, FfWOk rd σ j) ∧ (∀ t < 2 ^ L, Ff0Ok rd σ (6 + 4 * L) t) ∧
      FfLevelsOk σ L 1 (6 + 4 * L + 5 * 2 ^ L) (ffOut0 (6 + 4 * L) (2 ^ L)) ∧
      σ (.n (fin + 1)) = σ (.n fin) ∧ [σ (.n (fin + 1))] = rets := by
  rw [ffBody, holdsList_append, holdsList_append, holdsList_append,
    holdsList_range_flatten _ ffW (fun _ => rfl), holdsList_range_flatten _ _ (fun _ => rfl),
    holds_ffLevels]
  simp only [ffW, ff0, Stmt.HoldsList, Stmt.Holds, Atom.Holds, word_one, and_true, FfWOk, Ff0Ok,
    List.map_cons, List.map_nil]

theorem gPairs_flatMap (u v : E) (f g : ℕ → E) :
    ∀ l : List ℕ, gPairs u v (l.flatMap fun t => [f t, g t]) = l.map fun t => u * f t + v * g t
  | [] => rfl
  | t :: l => by
    rw [List.flatMap_cons, List.cons_append, List.cons_append, List.nil_append, gPairs,
      gPairs_flatMap u v f g l, List.map_cons]

theorem flatMap_pair_getElem (f g : ℕ → E) (n i : ℕ) (hi : i < 2 * n) :
    ((List.range n).flatMap fun t => [f t, g t]).getD i 0 = if i % 2 = 0 then f (i / 2) else g (i / 2) := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.getD_eq_getElem?_getD]
    have hl : ((List.range n).flatMap fun t => [f t, g t]).length = 2 * n := by
      simp [List.length_flatMap]; ring
    rcases Nat.lt_or_ge i (2 * n) with h | h
    · rw [List.getElem?_append_left (by rw [hl]; exact h), ← List.getD_eq_getElem?_getD, ih i h]
    · rw [List.getElem?_append_right (by rw [hl]; exact h), hl]
      rcases (show i = 2 * n ∨ i = 2 * n + 1 by omega) with rfl | rfl
      · simp
      · simp [show (2 * n + 1) % 2 = 1 by omega, show (2 * n + 1) / 2 = n by omega]

theorem length_flatMap_pair (f g : ℕ → E) (n : ℕ) :
    ((List.range n).flatMap fun t => [f t, g t]).length = 2 * n := by
  simp [List.length_flatMap]; ring

/-- **`fold_final_msg(msg, point, n)`** (G:815-831; TRIAGE #24): the `2^n` words `m` at `msg`
and the `n` words `ps` at `point`, and the function returns `multilinearEval m ps` (V:687). -/
def MeaningFoldFinalMsg (n : ℕ) (rd : Reader) : List E → List E → Prop
  | [msg, point], rets => ∃ m ps : List E, m.length = 2 ^ n ∧ ps.length = n ∧ ReadsAt rd msg m ∧
      ReadsAt rd point ps ∧ rets = [multilinearEval m ps]
  | _, _ => False

theorem multilinearEval_cons (m : List E) (r : E) (rs : List E) :
    multilinearEval m (r :: rs) = (rs.foldl (fun l r => foldPairs r l) (foldPairs r m)).headD 0 := rfl

theorem fold_final_msg_sound_aux {name : String} {f : Fn} (L fin : ℕ)
    (hfind : coreProgram.find? name = some f) (hparams : f.params = [.n 0, .n 1])
    (hbody : f.body = ffBody L fin)
    (hfin : (ffLevels L 1 (6 + 4 * L + 5 * 2 ^ L) (ffOut0 (6 + 4 * L) (2 ^ L))).2 = [.n fin])
    (rd : Reader) (args rets : List E) (h : coreProgram.Rel rd name args rets) :
    MeaningFoldFinalMsg (L + 1) rd args rets := by
  rw [rel_iff_sem hfind, hbody, hparams] at h
  obtain ⟨σ, hp, h⟩ := h
  rw [ffBody_holds] at h
  obtain ⟨hw, h0, hlv, hc, hret⟩ := h
  simp only [List.map_cons, List.map_nil] at hp
  subst hp hret
  set S := 6 + 4 * L
  set p := fun i => σ (.n (5 + 4 * i))
  have hwt : ∀ i < L + 1, σ (.n (4 + 4 * i)) = 1 + p i ∧ σ (.n (5 + 4 * i)) = p i := fun i hi => by
    obtain ⟨e2, l3, e4, l5⟩ := hw i hi
    exact ⟨by rw [e4, e2, loadHolds_unique l3 l5], rfl⟩
  set m := (List.range (2 ^ L)).flatMap fun t => [σ (.n (S + 5 * t)), σ (.n (S + 5 * t + 2))]
  have hout0 : (ffOut0 S (2 ^ L)).map σ = foldPairs (p 0) m := by
    have h4 := (hwt 0 (by omega)).1
    have h5 := (hwt 0 (by omega)).2
    simp only [Nat.mul_zero, Nat.add_zero] at h4 h5
    rw [← gPairs_eq_foldPairs, ← h4, ← h5, gPairs_flatMap, ffOut0, List.map_map]
    refine List.map_congr_left fun t ht => ?_
    obtain ⟨-, e1, -, e3, e4'⟩ := h0 t (List.mem_range.mp ht)
    simp only [Function.comp_apply]
    rw [e4', e1, e3]
  have hfold := ffLevels_value (σ := σ) p L 1 _ _ (fun i h1 h2 => hwt i (by omega)) hlv
  rw [hfin, hout0] at hfold
  refine ⟨m, (List.range (L + 1)).map p, by rw [length_flatMap_pair, pow_succ]; ring, by simp,
    fun i hi => ?_, fun i hi => ?_, ?_⟩
  · rw [show m[i] = m.getD i 0 by simp [List.getD_eq_getElem?_getD, hi],
      flatMap_pair_getElem _ _ _ _ (by rw [length_flatMap_pair] at hi; exact hi)]
    rw [length_flatMap_pair] at hi
    split
    · rename_i he
      obtain ⟨-, -, -, -, -⟩ := h0 (i / 2) (by omega)
      have := (h0 (i / 2) (by omega)).1
      rwa [show 2 * (i / 2) = i by omega] at this
    · have := (h0 (i / 2) (by omega)).2.2.1
      rwa [show 2 * (i / 2) + 1 = i by omega] at this
  · simp only [List.length_map, List.length_range] at hi
    simp only [List.getElem_map, List.getElem_range]
    exact (hw i hi).2.2.2
  · rw [hc, List.range_succ_eq_map, List.map_cons, multilinearEval_cons, List.map_map]
    simp only [Function.comp_def]
    have e : (fun x => p x.succ) = (fun i => p (1 + i)) :=
      funext fun i => by rw [Nat.succ_eq_add_one, Nat.add_comm]
    rw [e, ← hfold]
    rfl

/-! ## Completeness -/

/-- The honest values of a later level over the values `vals`, folded at `r`. -/
def pairVal (r : E) : List E → ℕ → E
  | a :: _ :: _, 0 => (1 + r) * a
  | _ :: b :: _, 1 => r * b
  | a :: b :: _, 2 => (1 + r) * a + r * b
  | _ :: _ :: rest, i + 3 => pairVal r rest i
  | _, _ => 0

/-- The honest value at `k` of the later levels. -/
def lvEval (pv : ℕ → E) : ℕ → ℕ → ℕ → List E → ℕ → E
  | 0, _, _, vals, _ => vals.headD 0
  | f + 1, j, s, vals, k =>
    if k < s + 3 * (vals.length / 2) then pairVal (pv j) vals (k - s)
    else lvEval pv f (j + 1) (s + 3 * (vals.length / 2)) (foldPairs (pv j) vals) k

/-- The first value after the later levels. -/
def ffEnd : ℕ → ℕ → ℕ → ℕ
  | 0, s, _ => s
  | f + 1, s, c => ffEnd f (s + 3 * (c / 2)) (c / 2)

theorem length_foldPairs (r : E) : ∀ l, (foldPairs r l).length = l.length / 2
  | a :: b :: rest => by rw [foldPairs, List.length_cons, length_foldPairs r rest]; simp; omega
  | [] => rfl
  | [_] => by simp [foldPairs]

theorem pairs_complete (σ : Val) (w0 w1 : V) (r : E) (h0 : σ w0 = 1 + r) (h1 : σ w1 = r) :
    ∀ s cur, (∀ i < 3 * (cur.length / 2), σ (.n (s + i)) = pairVal r (cur.map σ) i) →
      FfPairsOk σ w0 w1 s cur
  | s, a :: b :: rest, hv => by
    have e0 := hv 0 (by simp only [List.length_cons]; omega)
    have e1 := hv 1 (by simp only [List.length_cons]; omega)
    have e2 := hv 2 (by simp only [List.length_cons]; omega)
    simp only [List.map_cons, pairVal, Nat.add_zero] at e0 e1 e2
    refine ⟨by rw [e0, h0], by rw [e1, h1], by rw [e2, e0, e1], pairs_complete σ w0 w1 r h0 h1 (s + 3)
      rest fun i hi => ?_⟩
    have := hv (i + 3) (by simp at hi ⊢; omega)
    rwa [List.map_cons, List.map_cons, pairVal, show s + (i + 3) = s + 3 + i by omega] at this
  | _, [], _ => trivial
  | _, [_], _ => trivial

theorem levels_complete (σ : Val) (pv : ℕ → E) :
    ∀ f j s cur, (∀ i, j ≤ i → i < j + f → σ (.n (4 + 4 * i)) = 1 + pv i ∧ σ (.n (5 + 4 * i)) = pv i) →
      (∀ k, s ≤ k → σ (.n k) = lvEval pv f j s (cur.map σ) k) → FfLevelsOk σ f j s cur
  | 0, _, _, _, _, _ => trivial
  | f + 1, j, s, cur, hw, hv => by
    obtain ⟨hw0, hw1⟩ := hw j le_rfl (by omega)
    have hp : FfPairsOk σ (.n (4 + 4 * j)) (.n (5 + 4 * j)) s cur :=
      pairs_complete σ _ _ (pv j) hw0 hw1 s cur fun i hi => by
        rw [hv (s + i) (by omega), lvEval, ite_pos' (by simp; omega), Nat.add_sub_cancel_left]
    refine ⟨hp, levels_complete σ pv f (j + 1) _ _ (fun i h1 h2 => hw i (by omega) (by omega))
      fun k hk => ?_⟩
    rw [length_ffPairs] at hk
    have hmap : (ffPairs (.n (4 + 4 * j)) (.n (5 + 4 * j)) s cur).2.map σ = foldPairs (pv j) (cur.map σ) := by
      rw [ffPairs_value _ _ _ _ hp, hw0, hw1, gPairs_eq_foldPairs]
    rw [hmap, hv k (by omega), lvEval, ite_neg' (by simp; omega)]
    simp only [List.length_map, length_ffPairs]

theorem le_ffEnd : ∀ f s c, s ≤ ffEnd f s c
  | 0, _, _ => le_rfl
  | f + 1, _, _ => le_trans (Nat.le_add_right _ _) (le_ffEnd f _ _)

theorem lvEval_end (pv : ℕ → E) :
    ∀ f j s vals k, ffEnd f s vals.length ≤ k →
      lvEval pv f j s vals k = (((List.range f).map fun i => pv (j + i)).foldl
        (fun l r => foldPairs r l) vals).headD 0
  | 0, _, _, _, _, _ => rfl
  | f + 1, j, s, vals, k, hk => by
    have hle := le_ffEnd f (s + 3 * (vals.length / 2)) (vals.length / 2)
    rw [lvEval, ite_neg' (by simp only [ffEnd] at hk; omega), lvEval_end pv f (j + 1) _ _ k
      (by rw [length_foldPairs]; exact hk), List.range_succ_eq_map, List.map_cons, List.foldl_cons,
      List.map_map]
    simp only [Nat.add_zero, Function.comp_def]
    congr 2
    refine List.map_congr_left fun i _ => ?_
    rw [Nat.succ_eq_add_one, show j + (i + 1) = j + 1 + i by omega]

theorem foldPairs_range (r : E) : ∀ n (m : List E), m.length = 2 * n →
    foldPairs r m = (List.range n).map fun t => m.getD (2 * t) 0 * (1 + r) + m.getD (2 * t + 1) 0 * r
  | 0, m, h => by
    obtain rfl : m = [] := List.eq_nil_of_length_eq_zero (by simpa using h)
    rfl
  | n + 1, a :: b :: rest, h => by
    rw [foldPairs, foldPairs_range r n rest (by simp at h; omega), List.range_succ_eq_map,
      List.map_cons, List.map_map]
    congr 1
  | n + 1, [], h => by simp at h
  | n + 1, [_], h => by simp at h; omega

theorem list_eq_range_map (l : List E) : l = (List.range l.length).map fun i => l.getD i 0 := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getD_eq_getElem?_getD, h1]

theorem fold_final_msg_complete_aux {name : String} {f : Fn} (L fin : ℕ)
    (hfind : coreProgram.find? name = some f) (hparams : f.params = [.n 0, .n 1])
    (hbody : f.body = ffBody L fin)
    (hfin : (ffLevels L 1 (6 + 4 * L + 5 * 2 ^ L) (ffOut0 (6 + 4 * L) (2 ^ L))).2 = [.n fin])
    (hend : ffEnd L (6 + 4 * L + 5 * 2 ^ L) (2 ^ L) ≤ fin + 1)
    (rd : Reader) (args rets : List E) (h : MeaningFoldFinalMsg (L + 1) rd args rets) :
    coreProgram.Rel rd name args rets := by
  obtain ⟨msg, point, rfl⟩ : ∃ msg point, args = [msg, point] := by
    match args, h with
    | [a, b], _ => exact ⟨a, b, rfl⟩
  obtain ⟨m, ps, hm, hps, hrm, hrp, rfl⟩ := h
  rw [rel_iff_sem hfind, hbody, hparams]
  set pv := fun i => ps.getD i 0
  set mv := fun i => m.getD i 0
  let τ : Val := fun v => if v.idx < 2 then [msg, point].getD v.idx 0
    else if v.idx < (6 + 4 * L) then
      [1, pv ((v.idx - 2) / 4), 1 + pv ((v.idx - 2) / 4), pv ((v.idx - 2) / 4)].getD ((v.idx - 2) % 4) 0
    else if v.idx < (6 + 4 * L + 5 * 2 ^ L) then
      [mv (2 * ((v.idx - (6 + 4 * L)) / 5)), (1 + pv 0) * mv (2 * ((v.idx - (6 + 4 * L)) / 5)),
        mv (2 * ((v.idx - (6 + 4 * L)) / 5) + 1), pv 0 * mv (2 * ((v.idx - (6 + 4 * L)) / 5) + 1),
        (1 + pv 0) * mv (2 * ((v.idx - (6 + 4 * L)) / 5)) + pv 0 * mv (2 * ((v.idx - (6 + 4 * L)) / 5) + 1)].getD
        ((v.idx - (6 + 4 * L)) % 5) 0
    else lvEval pv L 1 (6 + 4 * L + 5 * 2 ^ L) (foldPairs (pv 0) m) v.idx
  have tw : ∀ j c, j < L + 1 → c < 4 → τ (.n (2 + 4 * j + c)) =
      [1, pv j, 1 + pv j, pv j].getD c 0 := fun j c hj hc => by
    show (if 2 + 4 * j + c < 2 then _ else if 2 + 4 * j + c < 6 + 4 * L then _
      else if 2 + 4 * j + c < 6 + 4 * L + 5 * 2 ^ L then _ else _) = _
    rw [ite_neg' (by omega), ite_pos' (by omega), show (2 + 4 * j + c - 2) / 4 = j by omega,
      show (2 + 4 * j + c - 2) % 4 = c by omega]
  have t0 : ∀ t c, t < 2 ^ L → c < 5 → τ (.n ((6 + 4 * L) + 5 * t + c)) =
      [mv (2 * t), (1 + pv 0) * mv (2 * t), mv (2 * t + 1), pv 0 * mv (2 * t + 1),
        (1 + pv 0) * mv (2 * t) + pv 0 * mv (2 * t + 1)].getD c 0 := fun t c ht hc => by
    show (if (6 + 4 * L) + 5 * t + c < 2 then _ else if (6 + 4 * L) + 5 * t + c < 6 + 4 * L then _
      else if (6 + 4 * L) + 5 * t + c < 6 + 4 * L + 5 * 2 ^ L then _ else _) = _
    rw [ite_neg' (by omega), ite_neg' (by omega), ite_pos' (by omega),
      show ((6 + 4 * L) + 5 * t + c - (6 + 4 * L)) / 5 = t by omega, show ((6 + 4 * L) + 5 * t + c - (6 + 4 * L)) % 5 = c by omega]
  have tl : ∀ k, (6 + 4 * L + 5 * 2 ^ L) ≤ k → τ (.n k) = lvEval pv L 1 (6 + 4 * L + 5 * 2 ^ L) (foldPairs (pv 0) m) k := fun k hk => by
    show (if k < 2 then _ else if k < 6 + 4 * L then _
      else if k < 6 + 4 * L + 5 * 2 ^ L then _ else _) = _
    rw [ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega)]
  have hw : ∀ i < L + 1, τ (.n (4 + 4 * i)) = 1 + pv i ∧ τ (.n (5 + 4 * i)) = pv i := fun i hi => by
    have a := tw i 2 hi (by omega)
    have b := tw i 3 hi (by omega)
    rw [show 2 + 4 * i + 2 = 4 + 4 * i by omega] at a
    rw [show 2 + 4 * i + 3 = 5 + 4 * i by omega] at b
    exact ⟨a, b⟩
  have hrp' : ∀ j < L + 1, LoadHolds rd point j (pv j) := fun j hj => by
    have := hrp j (by omega)
    simpa [pv, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show j < ps.length by omega)] using this
  have hrm' : ∀ i < 2 ^ (L + 1), LoadHolds rd msg i (mv i) := fun i hi => by
    have := hrm i (by omega)
    simpa [mv, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < m.length by omega)] using this
  have hout0 : (ffOut0 (6 + 4 * L) (2 ^ L)).map τ = (foldPairs (pv 0) m) := by
    rw [ffOut0, List.map_map, foldPairs_range (pv 0) (2 ^ L) m (by rw [hm, pow_succ]; ring)]
    refine List.map_congr_left fun t ht => ?_
    simp only [Function.comp_apply]
    rw [t0 t 4 (List.mem_range.mp ht) (by omega)]
    simp only [List.getD_cons_succ, List.getD_cons_zero, mv]
    ring
  have hlv : FfLevelsOk τ L 1 (6 + 4 * L + 5 * 2 ^ L) (ffOut0 (6 + 4 * L) (2 ^ L)) :=
    levels_complete τ pv L 1 (6 + 4 * L + 5 * 2 ^ L) _ (fun i h1 h2 => hw i (by omega)) (fun k hk => by rw [tl k hk, hout0])
  have hval := ffLevels_value (σ := τ) pv L 1 (6 + 4 * L + 5 * 2 ^ L) _ (fun i h1 h2 => hw i (by omega)) hlv
  rw [hfin, hout0] at hval
  have hfinv : τ (.n fin) = (((List.range L).map fun i => pv (1 + i)).foldl
      (fun l r => foldPairs r l) (foldPairs (pv 0) m)).headD 0 := by
    rw [← hval]; rfl
  have hfin1 : τ (.n (fin + 1)) = (((List.range L).map fun i => pv (1 + i)).foldl
      (fun l r => foldPairs r l) (foldPairs (pv 0) m)).headD 0 := by
    rw [tl (fin + 1) (le_trans (le_ffEnd _ _ _) hend), lvEval_end pv L 1 (6 + 4 * L + 5 * 2 ^ L) (foldPairs (pv 0) m) (fin + 1)
      (by rw [length_foldPairs, hm, pow_succ, Nat.mul_div_cancel _ (by decide)]; exact hend)]
  refine ⟨τ, rfl, ?_⟩
  rw [ffBody_holds]
  refine ⟨fun j hj => ?_, fun t ht => ?_, hlv, by rw [hfin1, hfinv], ?_⟩
  · have a := tw j 0 hj (by omega); have b := tw j 1 hj (by omega)
    have c := tw j 2 hj (by omega); have d := tw j 3 hj (by omega)
    simp only [Nat.add_zero, List.getD_cons_zero, List.getD_cons_succ,
      show 2 + 4 * j + 1 = 3 + 4 * j by omega, show 2 + 4 * j + 2 = 4 + 4 * j by omega,
      show 2 + 4 * j + 3 = 5 + 4 * j by omega] at a b c d
    have t1 : τ (.n 1) = point := rfl
    exact ⟨a, by rw [t1, b]; exact hrp' j hj, by rw [c, a, b], by rw [t1, d]; exact hrp' j hj⟩
  · have a := t0 t 0 ht (by omega); have b := t0 t 1 ht (by omega)
    have c := t0 t 2 ht (by omega); have d := t0 t 3 ht (by omega)
    have e := t0 t 4 ht (by omega)
    simp only [Nat.add_zero, List.getD_cons_zero, List.getD_cons_succ] at a b c d e
    have t0' : τ (.n 0) = msg := rfl
    obtain ⟨w4, w5⟩ := hw 0 (by omega)
    simp only [Nat.mul_zero, Nat.add_zero] at w4 w5
    refine ⟨by rw [t0', a]; exact hrm' (2 * t) (by rw [pow_succ]; omega), by rw [b, w4, a],
      by rw [t0', c]; exact hrm' (2 * t + 1) (by rw [pow_succ]; omega), by rw [d, w5, c],
      by rw [e, b, d]⟩
  · rw [hfin1, list_eq_range_map ps, hps, List.range_succ_eq_map, List.map_cons,
      multilinearEval_cons, List.map_map]
    congr 3
    simp only [Function.comp_def]
    refine List.map_congr_left fun i _ => ?_
    rw [Nat.succ_eq_add_one, Nat.add_comm]

theorem fold_final_msg_iff {name : String} {f : Fn} (L fin : ℕ)
    (hfind : coreProgram.find? name = some f) (hparams : f.params = [.n 0, .n 1])
    (hbody : f.body = ffBody L fin)
    (hfin : (ffLevels L 1 (6 + 4 * L + 5 * 2 ^ L) (ffOut0 (6 + 4 * L) (2 ^ L))).2 = [.n fin])
    (hend : ffEnd L (6 + 4 * L + 5 * 2 ^ L) (2 ^ L) ≤ fin + 1) (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd name args rets ↔ MeaningFoldFinalMsg (L + 1) rd args rets :=
  ⟨fold_final_msg_sound_aux L fin hfind hparams hbody hfin rd args rets,
    fold_final_msg_complete_aux L fin hfind hparams hbody hfin hend rd args rets⟩

set_option maxRecDepth 100000 in
theorem fold_final_msg_L2_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "fold_final_msg__L2" args rets ↔ MeaningFoldFinalMsg 2 rd args rets :=
  fold_final_msg_iff 1 22 (Program.find?_of_indexOf? (j := 618) (by decide +kernel) rfl) rfl
    core618_body (by decide) (by decide) rd args rets

set_option maxRecDepth 100000 in
theorem fold_final_msg_L3_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "fold_final_msg__L3" args rets ↔ MeaningFoldFinalMsg 3 rd args rets :=
  fold_final_msg_iff 2 42 (Program.find?_of_indexOf? (j := 633) (by decide +kernel) rfl) rfl
    core633_body (by decide) (by decide) rd args rets

set_option maxRecDepth 100000 in
theorem fold_final_msg_L4_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "fold_final_msg__L4" args rets ↔ MeaningFoldFinalMsg 4 rd args rets :=
  fold_final_msg_iff 3 78 (Program.find?_of_indexOf? (j := 591) (by decide +kernel) rfl) rfl
    core591_body (by decide) (by decide) rd args rets

set_option maxRecDepth 100000 in
theorem fold_final_msg_L5_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "fold_final_msg__L5" args rets ↔ MeaningFoldFinalMsg 5 rd args rets :=
  fold_final_msg_iff 4 146 (Program.find?_of_indexOf? (j := 604) (by decide +kernel) rfl) rfl
    core604_body (by decide) (by decide) rd args rets

end
end LeanVM.Guest.B1
