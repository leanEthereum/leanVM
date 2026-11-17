/-
  LeanVM.Protocol.Whir.Sound.NewtonDecoder

  A near-tuple decoder from one-error Newton decoding on a window of the agreement set.
-/

module

public import LeanVM.Protocol.Whir.Sound.Descent
public import LeanVM.Protocol.Whir.Sound.Newton

/-!
# The near-tuple decoder of one error

`newtonNearDecoder`: on a set `S` of at least `d + 3` columns, each lane is decoded with one error
(`Newton.decode1`) on the first `d + 3` columns of `S`; if every lane decodes and the tuple is near
on all of `S` (`NearT`), it is the output. A near tuple disagrees with each lane on at most one
column of the window, so one-error decoding returns it (`Newton.decode1_eq`).
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters Polynomial Newton

@[expose] public section

variable {n m : ℕ}

/-- The columns of `S`, in increasing order. -/
def colsOf (S : Finset (Fin n)) : List (Fin n) := (List.finRange n).filter (· ∈ S)

theorem nodup_colsOf (S : Finset (Fin n)) : (colsOf S).Nodup :=
  (List.nodup_finRange n).filter _

theorem mem_colsOf {S : Finset (Fin n)} {x : Fin n} : x ∈ colsOf S ↔ x ∈ S := by
  simp [colsOf]

theorem length_colsOf (S : Finset (Fin n)) : (colsOf S).length = S.card := by
  rw [← List.toFinset_card_of_nodup (nodup_colsOf S)]
  congr 1
  ext x
  simp [mem_colsOf]

/-- The window: the first `d + 3` columns of `S`, in increasing order. -/
def window (d : ℕ) (S : Finset (Fin n)) : List (Fin n) := (colsOf S).take (d + 3)

/-- Lane `v`'s points on the window. -/
def winPts (dom : Fin n ↪ E) (d : ℕ) (Q : (Fin (m + 1) → Bool) → Fin n → E) (S : Finset (Fin n))
    (v : Fin (m + 1) → Bool) : List (E × E) :=
  (window d S).map fun x ↦ (dom x, Q v x)

open Classical in
/-- **One-error near-tuple decoding**: every lane decoded on the window, the tuple kept if
near. -/
noncomputable def newtonDec (dom : Fin n ↪ E) (d : ℕ) (Q : (Fin (m + 1) → Bool) → Fin n → E)
    (S : Finset (Fin n)) : Option ((Fin (m + 1) → Bool) → E[X]) :=
  if d + 3 ≤ S.card then
    if h : ∀ v, (decode1 d (winPts dom d Q S v)).isSome then
      if NearT dom Q d S (fun v ↦ nP ((decode1 d (winPts dom d Q S v)).get (h v)).1
          ((decode1 d (winPts dom d Q S v)).get (h v)).2) then
        some fun v ↦ nP ((decode1 d (winPts dom d Q S v)).get (h v)).1
          ((decode1 d (winPts dom d Q S v)).get (h v)).2
      else none
    else none
  else none

theorem length_window {d : ℕ} {S : Finset (Fin n)} (hS : d + 3 ≤ S.card) :
    (window d S).length = d + 3 := by
  rw [window, List.length_take, length_colsOf]; omega

theorem nodup_winPts (dom : Fin n ↪ E) (d : ℕ) (Q : (Fin (m + 1) → Bool) → Fin n → E)
    (S : Finset (Fin n)) (v : Fin (m + 1) → Bool) : ((winPts dom d Q S v).map (·.1)).Nodup := by
  rw [winPts, List.map_map]
  exact ((nodup_colsOf S).sublist (List.take_sublist _ _)).map dom.injective

/-- A near tuple's lane disagrees with the window's points at one index at most. -/
theorem exists_err {dom : Fin n ↪ E} {d : ℕ} {Q : (Fin (m + 1) → Bool) → Fin n → E}
    {S : Finset (Fin n)} (hS : d + 3 ≤ S.card) {T : (Fin (m + 1) → Bool) → E[X]}
    (hT : NearT dom Q d S T) (v : Fin (m + 1) → Bool) :
    ∃ e < d + 3, ∀ i (hi : i < (winPts dom d Q S v).length), i ≠ e →
      (T v).eval (winPts dom d Q S v)[i].1 = (winPts dom d Q S v)[i].2 := by
  classical
  have hlen : (winPts dom d Q S v).length = d + 3 := by rw [winPts, List.length_map, length_window hS]
  by_cases hex : ∃ e, ∃ he : e < (window d S).length, (T v).eval (dom (window d S)[e]) ≠
      Q v (window d S)[e]
  · obtain ⟨e, he, hbad⟩ := hex
    refine ⟨e, by rw [length_window hS] at he; exact he, fun i hi hie ↦ ?_⟩
    have hi' : i < (window d S).length := by simpa [winPts] using hi
    simp only [winPts, List.getElem_map]
    by_contra hbad'
    have hnd : (window d S).Nodup := (nodup_colsOf S).sublist (List.take_sublist _ _)
    have hmem : ∀ j (hj : j < (window d S).length), (window d S)[j] ∈ S := fun j hj ↦
      mem_colsOf.mp (List.mem_of_mem_take (List.getElem_mem hj))
    have hsub : ({(window d S)[e], (window d S)[i]} : Finset (Fin n)) ⊆
        S.filter fun x ↦ ∃ v, (T v).eval (dom x) ≠ Q v x := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Finset.mem_filter.mpr ⟨hmem e he, v, hbad⟩
      · exact Finset.mem_filter.mpr ⟨hmem i hi', v, hbad'⟩
    have hne : (window d S)[e] ≠ (window d S)[i] := fun h ↦
      hie ((List.Nodup.getElem_inj_iff hnd).mp h).symm
    have := (Finset.card_le_card hsub).trans hT.2
    rw [Finset.card_pair hne] at this
    omega
  · refine ⟨0, by omega, fun i hi _ ↦ ?_⟩
    have hi' : i < (window d S).length := by simpa [winPts] using hi
    simp only [winPts, List.getElem_map]
    by_contra hbad
    exact hex ⟨i, hi', hbad⟩

/-- **The one-error near-tuple decoder.** -/
noncomputable def newtonNearDecoder : NearDecoder where
  dec dom d Q S := newtonDec dom d Q S
  sound dom d Q S T h := by
    unfold newtonDec at h
    split_ifs at h with h0 h1 h2
    · rw [Option.some.injEq] at h
      exact h ▸ h2
  complete dom d Q S T hS hT := by
    have hlane : ∀ v, ∃ f, decode1 d (winPts dom d Q S v) = some f ∧ nP f.1 f.2 = T v := fun v ↦ by
      obtain ⟨e, he, hag⟩ := exists_err hS hT v
      exact decode1_eq (by rw [winPts, List.length_map, length_window hS])
        (nodup_winPts dom d Q S v) (hT.1 v) he hag
    have hall : ∀ v, (decode1 d (winPts dom d Q S v)).isSome := fun v ↦ by
      obtain ⟨f, hf, -⟩ := hlane v; rw [hf]; rfl
    have hTeq : (fun v ↦ nP ((decode1 d (winPts dom d Q S v)).get (hall v)).1
        ((decode1 d (winPts dom d Q S v)).get (hall v)).2) = T := by
      funext v
      obtain ⟨f, hf, hfT⟩ := hlane v
      simp only [hf, Option.get_some, hfT]
    unfold newtonDec
    rw [ite_eq_left hS, dite_eq_left hall, hTeq, ite_eq_left hT]
    rfl

end
end LeanVM.Protocol.Whir.Sound
