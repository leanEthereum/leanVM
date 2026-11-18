/-
  LeanVM.Protocol.Whir.Sound.DescentC

  The descent over arrays, in the form the cost machine compiles.
-/

module

public import LeanVM.Protocol.Whir.Sound.DescentT
public import LeanVM.Protocol.Whir.Sound.NewtonK
public import LeanVM.Protocol.Whir.Params.Deployed

/-!
# The descent, compiled form

The descent over arrays with no embedding and no structure carrying proofs: a domain point is
`ofK (K.ofBits x)` (`ptE`), one-error decoding has its nodes in `K` (`newtonDecC`), a level's shape
is four numbers (`lvC`), the rounds are walked from the last by structural recursion on their
reversal (`descRevC`). Each is the array descent's (`newtonDecC_eq`, `descRevC_eq`,
`descendTraceC_eq`).
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Protocol.Whir
open LeanVM.Protocol.Whir.Params Newton

@[expose] public section

/-- The domain point `x_x`. -/
def ptE (x : ℕ) : E := ofK (K.ofBits x)

/-- A level's shape `(κ, R, ℓ, A)`. -/
def lvC (μ R i : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  let lv := (levelsOf μ R).getD i junkLv
  if lv.1 + lv.2.1 ≤ 64 ∧ 1 ≤ lv.2.1 then (lv.1, lv.2.1, lv.2.2.1, lv.2.2.2.1) else (0, 1, 0, 1)

theorem lvC_eq (μ R i : ℕ) : lvC μ R i =
    ((codesOf μ R i).κ, (codesOf μ R i).R, (codesOf μ R i).ℓ, (codesOf μ R i).A) := by
  unfold lvC codesOf mkCode
  dsimp only
  split_ifs <;> rfl

/-- The folds of every column. -/
def foldsAC (n : ℕ) (rounds : List FoldRound) (OA : AV) : AV :=
  Array.ofFn fun x : Fin n ↦ foldsCA (ptE x) rounds (OA.getD x #[])

/-- The agreement set's columns. -/
def agreeC (n m : ℕ) (r : FoldRound) (VA QA : AV) : List (Fin n) :=
  (List.finRange n).filter fun (x : Fin n) ↦
    let f := foldCA (ptE x) r (QA.getD x #[])
    let vx := VA.getD x #[]
    (List.finRange (2 ^ m)).all fun k ↦
      let a := vx.getD k 0
      let b := f.getD k 0
      decide (a = b)

/-- Lane `k`'s points on the window, nodes in `K`. -/
def winPtsC {n : ℕ} (d : ℕ) (QA : AV) (cols : List (Fin n)) (k : ℕ) : List (K × E) :=
  (cols.take (d + 3)).map fun (x : Fin n) ↦ (K.ofBits x, (QA.getD x #[]).getD k 0)

/-- Every lane's one-error decoding on the window. -/
def decFs {n : ℕ} (d m : ℕ) (QA : AV) (cols : List (Fin n)) : Array (Option (List K × List E)) :=
  Array.ofFn fun k : Fin (2 ^ (m + 1)) ↦ decode1K d (winPtsC d QA cols k)

/-- The decoded lanes' values on the `n` columns. -/
def valsOf (n m : ℕ) (fs : Array (Option (List K × List E))) : AV :=
  Array.ofFn fun x : Fin n ↦ Array.ofFn fun k : Fin (2 ^ (m + 1)) ↦
    nEvalK ((fs.getD k none).getD ([], [])).1 ((fs.getD k none).getD ([], [])).2 (K.ofBits x)

/-- The columns of `cols` where the values disagree with the word. -/
def badCols {n : ℕ} (m : ℕ) (QA : AV) (cols : List (Fin n)) (V : AV) : List (Fin n) :=
  cols.filter fun (x : Fin n) ↦
    let vx := V.getD x #[]
    let qx := QA.getD x #[]
    (List.finRange (2 ^ (m + 1))).any fun k ↦
      let a := vx.getD k 0
      let b := qx.getD k 0
      !decide (a = b)

/-- The values kept if they disagree with the word on one column at most. -/
def checkStage {n : ℕ} (m : ℕ) (QA : AV) (cols : List (Fin n)) (V : AV) : Option AV :=
  if (badCols m QA cols V).length ≤ 1 then some V else none

/-- The decoded lanes' values, if every lane decodes. -/
def decStage (n m : ℕ) (QA : AV) (cols : List (Fin n)) (fs : Array (Option (List K × List E))) :
    Option AV :=
  if fs.all (·.isSome) then checkStage m QA cols (valsOf n m fs) else none

/-- **One-error decoding over arrays, nodes in `K`.** -/
def newtonDecC (n d m : ℕ) (QA : AV) (cols : List (Fin n)) : Option AV :=
  if d + 3 ≤ cols.length then decStage n m QA cols (decFs d m QA cols) else none

theorem bne_eq_not_decide (a b : E) : (a != b) = !decide (a = b) := by
  rw [bne, beq_eq_decide]

theorem winPtsA_domain {κ R : ℕ} (h : κ + R ≤ 64) (d : ℕ) (QA : AV)
    (cols : List (Fin (2 ^ (κ + R)))) (k : ℕ) :
    winPtsA (domain κ R h) d QA cols k = liftPts (winPtsC d QA cols k) := by
  unfold winPtsA winPtsC liftPts
  rw [List.map_map]
  rfl

theorem newtonDecC_eq {κ R : ℕ} (h : κ + R ≤ 64) (d m : ℕ) (QA : AV)
    (cols : List (Fin (2 ^ (κ + R)))) :
    newtonDecC (2 ^ (κ + R)) d m QA cols = newtonDecA (domain κ R h) d m QA cols := by
  unfold newtonDecC newtonDecA decStage checkStage badCols valsOf decFs
  have hfs : (Array.ofFn fun k : Fin (2 ^ (m + 1)) ↦ decode1 d (winPtsA (domain κ R h) d QA cols k)) =
      (Array.ofFn fun k : Fin (2 ^ (m + 1)) ↦ decode1K d (winPtsC d QA cols k)).map
        (Option.map fun f ↦ (f.1.map ofK, f.2)) := by
    rw [Array.map_ofFn]
    congr 1
    funext k
    rw [winPtsA_domain h, decode1K_eq]
    rfl
  rw [hfs]
  set A := Array.ofFn fun k : Fin (2 ^ (m + 1)) ↦ decode1K d (winPtsC d QA cols k)
  have hall : (A.map (Option.map fun f : List K × List E ↦ (f.1.map ofK, f.2))).all (·.isSome) =
      A.all (·.isSome) := by
    rw [Array.all_map]
    congr 1
    funext o
    simp
  have hget : ∀ k : ℕ, ((A.map (Option.map fun f : List K × List E ↦ (f.1.map ofK, f.2))).getD k
      none).getD ([], []) = (((A.getD k none).getD ([], [])).1.map ofK,
        ((A.getD k none).getD ([], [])).2) := fun k ↦ by
    rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_map]
    rcases A[k]? with _ | o
    · rfl
    · rcases o with _ | f <;> rfl
  have hV : (Array.ofFn fun x : Fin (2 ^ (κ + R)) ↦ Array.ofFn fun k : Fin (2 ^ (m + 1)) ↦
      nEval (((A.map (Option.map fun f : List K × List E ↦ (f.1.map ofK, f.2))).getD k none).getD
        ([], [])).1 (((A.map (Option.map fun f : List K × List E ↦ (f.1.map ofK, f.2))).getD k
          none).getD ([], [])).2 (domain κ R h x)) =
      Array.ofFn fun x : Fin (2 ^ (κ + R)) ↦ Array.ofFn fun k : Fin (2 ^ (m + 1)) ↦
        nEvalK ((A.getD k none).getD ([], [])).1 ((A.getD k none).getD ([], [])).2 (K.ofBits x) := by
    congr 1
    funext x
    congr 1
    funext k
    rw [hget, nEvalK_eq]
    rfl
  dsimp only
  rw [hall, hV]
  simp only [bne_eq_not_decide]

/-- **The descent within a level, compiled form**: the rounds reversed, the last first. -/
def descRevC (n d A ℓ : ℕ) (OA : AV) : List FoldRound → ℕ → AV → Option (ℕ × AV)
  | [], m, VA => some (m, VA)
  | r :: rrev, m, VA =>
    let QA := foldsAC n rrev.reverse OA
    let cols := agreeC n m r VA QA
    if A - (ℓ - (rrev.length + 1)) ≤ cols.length then
      (newtonDecC n d m QA cols).bind fun TA ↦ descRevC n d A ℓ OA rrev (m + 1) TA
    else none

theorem foldsAC_eq {κ R : ℕ} (h : κ + R ≤ 64) (rounds : List FoldRound) (OA : AV) :
    foldsAC (2 ^ (κ + R)) rounds OA = foldsAA (domain κ R h) rounds OA := rfl

theorem agreeC_eq {κ R : ℕ} (h : κ + R ≤ 64) (m : ℕ) (r : FoldRound) (VA QA : AV) :
    agreeC (2 ^ (κ + R)) m r VA QA = agreeA (domain κ R h) m r VA QA := by
  unfold agreeC agreeA
  simp only [beq_eq_decide]
  rfl

theorem descRevC_eq {κ R : ℕ} (h : κ + R ≤ 64) (d A ℓ : ℕ) (OA : AV) :
    ∀ (rs : List FoldRound) (m : ℕ) (VA : AV),
      descRevC (2 ^ (κ + R)) d A ℓ OA rs.reverse m VA =
        descendRoundsA (domain κ R h) d (fun j ↦ A - (ℓ - j)) OA rs m VA := by
  intro rs
  induction rs using List.reverseRecOn with
  | nil => intro m VA; rw [descendRoundsA_nil]; rfl
  | append_singleton rs r ih =>
    intro m VA
    rw [List.reverse_append, List.reverse_singleton, List.singleton_append, descendRoundsA_concat,
      descRevC]
    rw [List.reverse_reverse, List.length_reverse, foldsAC_eq h, agreeC_eq h, newtonDecC_eq h]
    split_ifs
    · rcases newtonDecA (domain κ R h) d m (foldsAA (domain κ R h) rs OA)
        (agreeA (domain κ R h) m r VA (foldsAA (domain κ R h) rs OA)) with _ | TA
      · rfl
      · exact ih (m + 1) TA
    · rfl

/-- **The descent across levels, compiled form.** -/
def descendTraceC (μ R : ℕ) (OAs : List AV) : WhirTrace → ℕ → Option (ℕ × AV)
  | .final rounds folded, i =>
    let s := lvC μ R i
    descRevC (2 ^ (s.1 + s.2.1)) (2 ^ s.1 - 1 + s.2.2.1) s.2.2.2 s.2.2.1 (OAs.getD i #[])
      rounds.reverse 0 (Array.ofFn fun x : Fin (2 ^ (s.1 + s.2.1)) ↦ #[polyOfAtH folded x])
  | .mid rounds high rest, i => (descendTraceC μ R OAs rest (i + 1)).bind fun T' ↦
    let s := lvC μ R i
    let s' := lvC μ R (i + 1)
    if T'.1 = s'.2.2.1 ∧ s.1 = s'.2.2.1 + s'.1 then
      descRevC (2 ^ (s.1 + s.2.1)) (2 ^ s.1 - 1 + s.2.2.1) s.2.2.2 s.2.2.1 (OAs.getD i #[])
        rounds.reverse 0 (upAtA s.1 s'.1 s'.2.2.1 s.2.1 T'.2 high)
    else none

theorem descendTraceC_eq (μ R : ℕ) (OAs : List AV) : ∀ (tr : WhirTrace) (i : ℕ),
    descendTraceC μ R OAs tr i = descendTraceA (codesOf μ R) OAs tr i
  | .final rounds folded, i => by
    rw [descendTraceC, descendTraceA, lvC_eq]
    exact descRevC_eq (codesOf μ R i).h64 _ _ _ _ rounds 0 _
  | .mid rounds high rest, i => by
    rw [descendTraceC, descendTraceA, descendTraceC_eq μ R OAs rest (i + 1), lvC_eq, lvC_eq]
    refine congrArg _ (funext fun T' ↦ ?_)
    dsimp only
    split_ifs
    · exact descRevC_eq (codesOf μ R i).h64 _ _ _ _ rounds 0 _
    · rfl

end
end LeanVM.Protocol.Whir.Sound
