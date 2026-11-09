/-
  LeanVM.Guest.B1.KeccakGkr.FlatGI

  `completeAt_flatG`'s obligations on the callees, callee by callee.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.FlatG

/-!
# The callees, one at a time

`atAllG pre ks ps` at `i` is `ks[i]` at the frame pointers so far (`atAllG_getElem`); the results
the callees return (`OutsOk`, `takenOuts`), the frames matching them (`CallsMatch`), the regions
they read (`RegionsOk`, `Kid.lins`, `outRegion`), callee by callee.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

theorem atAllG_length : ∀ (pre : List ℕ) (ks : List KidG) (ps : List ℕ),
    (atAllG pre ks ps).length = min ks.length ps.length
  | _, [], _ => by simp [atAllG]
  | _, _ :: _, [] => by simp [atAllG]
  | pre, k :: ks, p :: ps => by
    simp [atAllG, atAllG_length (pre ++ [p]) ks ps, Nat.succ_min_succ]

theorem atAllG_getElem : ∀ (pre : List ℕ) (ks : List KidG) (ps : List ℕ) (i : ℕ)
    (h : i < (atAllG pre ks ps).length),
    (atAllG pre ks ps)[i] =
      ⟨(ks[i]'(by rw [atAllG_length] at h; omega)).f,
        (ks[i]'(by rw [atAllG_length] at h; omega)).taken,
        (ks[i]'(by rw [atAllG_length] at h; omega)).args (pre ++ ps.take i),
        (ks[i]'(by rw [atAllG_length] at h; omega)).Lin (pre ++ ps.take (i + 1)),
        (ks[i]'(by rw [atAllG_length] at h; omega)).Out (pre ++ ps.take (i + 1))⟩
  | _, [], _, _, h => by simp [atAllG] at h
  | _, _ :: _, [], _, h => by simp [atAllG] at h
  | pre, k :: ks, p :: ps, 0, _ => by simp [atAllG]
  | pre, k :: ks, p :: ps, i + 1, h => by
    simp only [atAllG, List.getElem_cons_succ]
    rw [atAllG_getElem (pre ++ [p]) ks ps i]
    simp

theorem outsOk_getElem : ∀ {ks : List Kid} {outs : List (List E × Layout)}, OutsOk ks outs →
    outs.length = ks.length ∧ ∀ i (h : i < ks.length) (h' : i < outs.length), ks[i].taken = true →
      ks[i].Out outs[i].1 outs[i].2
  | [], [], _ => ⟨rfl, fun i h ↦ by simp at h⟩
  | k :: ks, o :: os, ⟨h0, hs⟩ => by
    obtain ⟨hl, hi⟩ := outsOk_getElem hs
    refine ⟨by simp [hl], fun i h h' ht ↦ ?_⟩
    rcases i with _ | i
    · exact h0 ht
    · exact hi i (by simpa using h) (by simpa using h') ht
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem memL_takenOuts {rd : Reader} : ∀ {ks : List Kid} {outs : List (List E × Layout)},
    MemL rd (takenOuts ks outs) → ∀ i (h : i < ks.length) (h' : i < outs.length),
      ks[i].taken = true → MemL rd outs[i].2
  | k :: ks, o :: os, hm, i, h, h', ht => by
    simp only [takenOuts] at hm
    obtain ⟨h1, h2⟩ := Main.memL_append.mp hm
    rcases i with _ | i
    · simpa [show k.taken = true from ht] using h1
    · exact memL_takenOuts h2 i (by simpa using h) (by simpa using h') ht
  | [], _, _, _, h, _, _ => absurd h (by simp)
  | _ :: _, [], _, _, _, h', _ => absurd h' (by simp)

theorem callsMatch_ofI {σ : Val} : ∀ {cs : List Call} {ks : List Kid} {outs : List (List E × Layout)},
    cs.length = ks.length → outs.length = ks.length →
    (∀ i (h : i < ks.length) (hc : i < cs.length) (ho : i < outs.length),
      cs[i].f = ks[i].f ∧ cs[i].taken = ks[i].taken ∧
        (ks[i].taken = true → cs[i].args.map σ = ks[i].args ∧ cs[i].rets.map σ = outs[i].1)) →
    CallsMatch σ cs ks outs
  | [], [], [], _, _, _ => trivial
  | c :: cs, k :: ks, o :: os, hc, ho, h => by
    have h0 := h 0 (by simp) (by simp) (by simp)
    refine ⟨h0.1, h0.2.1, h0.2.2, callsMatch_ofI (by simpa using hc) (by simpa using ho)
      fun i hi hc' ho' ↦ h (i + 1) (by simpa using hi) (by simpa using hc') (by simpa using ho')⟩
  | [], _ :: _, _, hc, _, _ => absurd hc (by simp)
  | _ :: _, [], _, hc, _, _ => absurd hc (by simp)
  | [], [], _ :: _, _, ho, _ => absurd ho (by simp)
  | _ :: _, _ :: _, [], _, ho, _ => absurd ho (by simp)

theorem regionsOk_ofI {R : ℕ → Prop} : ∀ {Dacc : ℕ → Prop} {ks : List Kid}
    {outs : List (List E × Layout)},
    (∀ i (h : i < ks.length), ks[i].taken = true → ∀ x, RegionL ks[i].Lin x →
      R x ∨ Dacc x ∨ ∃ j, ∃ hjk : j < ks.length, ∃ hjo : j < outs.length,
        j < i ∧ ks[j].taken = true ∧ RegionL outs[j].2 x) →
    RegionsOk R Dacc ks outs
  | _, [], _, _ => trivial
  | _, _ :: _, [], _ => trivial
  | Dacc, k :: ks, o :: os, h => by
    refine ⟨fun ht x hx ↦ ?_, regionsOk_ofI fun i hi ht x hx ↦ ?_⟩
    · rcases h 0 (by simp) ht x hx with h1 | h1 | ⟨j, -, -, hj, -⟩
      · exact Or.inl h1
      · exact Or.inr h1
      · omega
    · rcases h (i + 1) (by simpa using hi) ht x hx with h1 | h1 | ⟨j, hjk, hjo, hj, hjt, hjx⟩
      · exact Or.inl h1
      · exact Or.inr (Or.inl (Or.inl h1))
      · rcases j with _ | j
        · exact Or.inr (Or.inl (Or.inr ⟨hjt, hjx⟩))
        · exact Or.inr (Or.inr ⟨j, by simpa using hjk, by simpa using hjo, by omega, hjt, hjx⟩)

theorem memL_lins_of {rd : Reader} : ∀ {ks : List Kid}, (∀ i (h : i < ks.length), MemL rd ks[i].Lin) →
    MemL rd (Kid.lins ks)
  | [], _ => fun q hq ↦ by simp [Kid.lins] at hq
  | k :: ks, h => by
    simp only [Kid.lins, List.flatMap_cons]
    exact Main.memL_append.mpr ⟨h 0 (by simp), memL_lins_of fun i hi ↦ h (i + 1) (by simpa using hi)⟩

theorem outRegion_ofI {x : ℕ} : ∀ {ks : List Kid} {outs : List (List E × Layout)} (i : ℕ)
    (h : i < ks.length) (h' : i < outs.length), ks[i].taken = true → RegionL outs[i].2 x →
    outRegion ks outs x
  | k :: ks, o :: os, 0, _, _, ht, hx => Or.inl ⟨ht, hx⟩
  | k :: ks, o :: os, i + 1, h, h', ht, hx =>
    Or.inr (outRegion_ofI i (by simpa using h) (by simpa using h') ht hx)
  | [], _, _, h, _, _, _ => absurd h (by simp)
  | _ :: _, [], _, _, h', _, _ => absurd h' (by simp)

end
end LeanVM.Guest.B1
