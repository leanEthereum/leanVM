/-
  LeanVM.Protocol.Extraction.AS.TraceShape

  The shape of a decoded WHIR trace.
-/

module

public import LeanVM.Protocol.Extraction.AS.Lite

/-!
# The decoded trace's shape

A trace decoded at the levels `levels` (`decLevelsP`) has, at each level, at most as many rounds and
high-part coefficients as the level's folds, and a final polynomial of at most
`2^(logN − folds) + fold` coefficients, and as many levels as `levels` (`decLevelsP_shape`).
-/

namespace LeanVM.Extraction.AS

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.Whir.Sound
open LeanVM.Protocol.EndToEnd.Sound

@[expose] public section

/-- A trace's shape at the levels `levels`, `A` the folds made before them. -/
def TraceShape (logN : ℕ) : ℕ → List Whir.Level → WhirTrace → Prop
  | A, [lv], .final rounds folded =>
    rounds.length ≤ lv.fold ∧ folded.length ≤ 2 ^ (logN - (A + lv.fold)) + lv.fold
  | A, lv :: nx :: rest, .mid rounds high tr =>
    rounds.length ≤ lv.fold ∧ high.length ≤ lv.fold ∧ TraceShape logN (A + lv.fold) (nx :: rest) tr
  | _, _, _ => False

theorem length_of_mapM {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {r : List β}, l.mapM f = some r → r.length = l.length
  | [], r, h => by simp at h; subst h; rfl
  | a :: l, r, h => by
    rw [List.mapM_cons] at h
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨b, -, rs, hrs, rfl⟩ := h
    simp [length_of_mapM hrs]

theorem decRoundsP_length : ∀ (n : ℕ) {h : List EvP} {rs : List FoldRound},
    decRoundsP n h = some rs → rs.length = n
  | 0, h, rs, hd => by simp [decRoundsP] at hd; subst hd; rfl
  | n + 1, h, rs, hd => by
    unfold decRoundsP at hd
    obtain ⟨r, -, hd⟩ := Option.bind_eq_some_iff.mp hd
    obtain ⟨rs', hrs, rfl⟩ := Option.map_eq_some_iff.mp hd
    simp [decRoundsP_length n hrs]

theorem decLevelsP_shape (logN : ℕ) : ∀ (A : ℕ) (levels : List Whir.Level) {h : List EvP}
    {tr : WhirTrace}, decLevelsP logN A levels h = some tr → TraceShape logN A levels tr
  | _, [], _, _, hd => by simp [decLevelsP] at hd
  | A, [lv], h, tr, hd => by
    unfold decLevelsP at hd
    obtain ⟨rounds, hr, hd⟩ := Option.bind_eq_some_iff.mp hd
    obtain ⟨folded, hf, rfl⟩ := Option.map_eq_some_iff.mp hd
    refine ⟨(decRoundsP_length _ hr).le, ?_⟩
    rw [length_of_mapM hf, List.length_take]
    omega
  | A, lv :: nx :: rest, h, tr, hd => by
    unfold decLevelsP at hd
    obtain ⟨rounds, hr, hd⟩ := Option.bind_eq_some_iff.mp hd
    obtain ⟨high, hh, hd⟩ := Option.bind_eq_some_iff.mp hd
    obtain ⟨tr', ht, rfl⟩ := Option.map_eq_some_iff.mp hd
    refine ⟨(decRoundsP_length _ hr).le, ?_, decLevelsP_shape logN (A + lv.fold) (nx :: rest) ht⟩
    unfold decHighP at hh
    rw [length_of_mapM hh, List.length_take]
    omega

/-- **The body's trace on the lite layout has the ladder's shape.** -/
theorem decBodyL_shape {lay : Fast.LayoutLite} {ρ : ℕ} {h : List EvP} {tr : WhirTrace}
    (hd : decBodyL lay ρ h = some tr) :
    ∃ config, Whir.ladder lay.stackLog ρ = some config ∧ TraceShape lay.stackLog 0 config tr := by
  unfold decBodyL decWhirCutP at hd
  obtain ⟨config, hc, hd⟩ := Option.bind_eq_some_iff.mp hd
  exact ⟨config, hc, decLevelsP_shape _ 0 config hd⟩

end
end LeanVM.Extraction.AS
