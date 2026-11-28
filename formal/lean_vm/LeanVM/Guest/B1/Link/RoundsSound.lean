/-
  LeanVM.Guest.B1.Link.RoundsSound

  `k` of `link_round`'s templates in a row are a chain of rounds.
-/

module

public import LeanVM.Guest.B1.Link.RoundSound
public import LeanVM.Guest.B1.Link.RoundsRun

/-!
# Rounds in a row

`lrRounds_sound`: wherever `lrRounds`' atoms hold, they are a chain of `k` rounds (`RoundChain`)
from the state the values `cap`, `cur`, `cl` hold to the one the returned values hold, the
challenges stored at `pts[0 ..]`.
-/

namespace LeanVM.Guest.B1.Link

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

theorem grindWords_length (bits : ℕ) (n : E) :
    (grindWords bits n).length = if bits = 0 then 0 else 1 := by
  unfold grindWords; split <;> rfl

theorem absorbAll_cons (s : Fs) (x : E) (l : List E) (t : ℕ) :
    s.absorbAll (x :: l) t = (s.absorb x t).absorbAll l t := rfl

/-- The state the values hold. -/
def rstOf (σ : Val) (cap : List ℕ) (cur cl : ℕ) : RSt := ⟨cap.map (σ ∘ .n), σ (.n cur), σ (.n cl)⟩

theorem lrRound_step {rd : Reader} {σ : Val} {nt bits o : ℕ} {cap : List ℕ} {cur cl tabs : ℕ}
    {pad : Option ℕ} (hA : ∀ a, Stmt.atom a ∈ lrRound nt bits o cap cur cl tabs pad → a.Holds rd σ)
    (hnt : 1 ≤ nt) (hnt' : nt ≤ 32) (hk : bits = 0 ∨ (bits = 1 ∧ nt % 4 ≠ 3))
    (hpad : ∀ z, pad = some z → ∀ j < 4, σ (.n (z + j)) = 0)
    (hgc : bits ≠ 0 → GcSound1 rd ∧ WinTabs rd (σ (.n tabs))) :
    RoundStep rd nt bits (rstOf σ cap cur cl) (σ (.n (lrD o nt bits pad + 3)))
        (rstOf σ (lrOutCap nt bits o pad) (lrD o nt bits pad + 6) (lrD o nt bits pad + 8)) ∧
      ∀ z, lrPad nt bits o pad = some z → ∀ j < 4, σ (.n (z + j)) = 0 := by
  obtain ⟨n, hr, hok, hy, hcap, hpend, hcur, hcl, hpad'⟩ := lrRound_sound hA hnt hnt' hk hpad hgc
  rw [lrXs_eq] at hr hok hy hcap hpend
  rw [absorbAll_cons] at hok hy hcap hpend
  refine ⟨?_, hpad'⟩
  unfold RoundStep
  simp only [rstOf]
  refine ⟨lrX σ o 0, lrT σ o nt, n, by simp [lrT], hr, hok, ?_, ?_, ?_⟩
  · generalize hG : ((⟨cap.map (σ ∘ .n), []⟩ : Fs).absorb (lrX σ o 0) dsObserve |>.absorbAll
      (lrT σ o nt) dsObserve |>.grindSqueeze bits n) = G at hy hcap hpend ⊢
    obtain ⟨y', c', p'⟩ := G
    simp only at hy hcap hpend
    subst hy hcap hpend
    rfl
  · show σ (.n (lrD o nt bits pad + 6)) = _
    rw [hcur, grindWords_length]
  · exact hcl

/-- `lrRounds` one round further. -/
theorem lrRounds_succ (nt bits pts tabs k o : ℕ) (cap : List ℕ) (cur cl : ℕ) (pad : Option ℕ) :
    lrRounds nt bits pts tabs (k + 1) o cap cur cl pad =
      let prev := lrRounds nt bits pts tabs k o cap cur cl pad
      (prev.1 ++ lrRound nt bits prev.2.2.2.2.1 prev.2.1 prev.2.2.1 prev.2.2.2.1 tabs prev.2.2.2.2.2 ++
          [.atom (.load (.n (lrD prev.2.2.2.2.1 nt bits prev.2.2.2.2.2 + 3)) (.n pts) k)],
        lrOutCap nt bits prev.2.2.2.2.1 prev.2.2.2.2.2, lrD prev.2.2.2.2.1 nt bits prev.2.2.2.2.2 + 6,
        lrD prev.2.2.2.2.1 nt bits prev.2.2.2.2.2 + 8, lrNext nt bits prev.2.2.2.2.1 prev.2.2.2.2.2,
        lrPad nt bits prev.2.2.2.2.1 prev.2.2.2.2.2) := rfl

/-- **`k` rounds in a row are a chain of rounds**, their challenges stored at `pts`. -/
theorem lrRounds_sound {rd : Reader} {σ : Val} {nt bits pts tabs : ℕ} (hnt : 1 ≤ nt) (hnt' : nt ≤ 32)
    (hk : bits = 0 ∨ (bits = 1 ∧ nt % 4 ≠ 3)) (hgc : bits ≠ 0 → GcSound1 rd ∧ WinTabs rd (σ (.n tabs))) :
    ∀ (k o : ℕ) (cap : List ℕ) (cur cl : ℕ) (pad : Option ℕ),
      (∀ a, Stmt.atom a ∈ (lrRounds nt bits pts tabs k o cap cur cl pad).1 → a.Holds rd σ) →
      (∀ z, pad = some z → ∀ j < 4, σ (.n (z + j)) = 0) →
      ∃ l : List (E × RSt), l.length = k ∧ RoundChain rd nt bits (rstOf σ cap cur cl) l ∧
        chainLast (rstOf σ cap cur cl) l = rstOf σ (lrRounds nt bits pts tabs k o cap cur cl pad).2.1
          (lrRounds nt bits pts tabs k o cap cur cl pad).2.2.1
          (lrRounds nt bits pts tabs k o cap cur cl pad).2.2.2.1 ∧
        ReadsAt rd (σ (.n pts)) (l.map Prod.fst) ∧
        ∀ z, (lrRounds nt bits pts tabs k o cap cur cl pad).2.2.2.2.2 = some z → ∀ j < 4, σ (.n (z + j)) = 0
  | 0, o, cap, cur, cl, pad, _, hpad => ⟨[], rfl, trivial, rfl, readsAt_nil _ _, hpad⟩
  | k + 1, o, cap, cur, cl, pad, hA, hpad => by
    obtain ⟨l, hl, hc, hlast, hpts, hpad1⟩ := lrRounds_sound hnt hnt' hk hgc k o cap cur cl pad
      (fun a ha ↦ hA a (by rw [lrRounds_succ]; exact List.mem_append_left _ (List.mem_append_left _ ha))) hpad
    rw [lrRounds_succ] at hA ⊢
    generalize lrRounds nt bits pts tabs k o cap cur cl pad = prev at hA hlast hpad1 ⊢
    obtain ⟨as, cap', cur', cl', o', pad'⟩ := prev
    dsimp only at hA hlast hpad1 ⊢
    have hR : ∀ a, Stmt.atom a ∈ lrRound nt bits o' cap' cur' cl' tabs pad' → a.Holds rd σ :=
      fun a ha ↦ hA a (List.mem_append_left _ (List.mem_append_right _ ha))
    obtain ⟨hstep, hpad2⟩ := lrRound_step hR hnt hnt' hk hpad1 hgc
    have hy := hA (.load (.n (lrD o' nt bits pad' + 3)) (.n pts) k)
      (List.mem_append_right _ (List.mem_singleton.mpr rfl))
    simp only [Atom.Holds] at hy
    refine ⟨l ++ [(_, _)], by simp [hl], roundChain_append hc (by rw [hlast]; exact ⟨hstep, trivial⟩),
      by rw [chainLast_append], ?_, hpad2⟩
    intro j hj
    simp only [List.map_append, List.map_cons, List.map_nil, List.length_append, List.length_map,
      List.length_singleton] at hj
    rcases Nat.lt_or_ge j l.length with h | h
    · have := hpts j (by simpa using h)
      simpa [List.getElem_append_left (show j < (l.map Prod.fst).length by simpa using h)] using this
    · obtain rfl : j = l.length := by omega
      simpa [hl] using hy

/-! ## The templates are atoms -/

/-- Every statement of the list is an atom, decided. -/
theorem allAtoms_iff_forall {ss : List Stmt} : AllAtoms ss ↔ ∀ s ∈ ss, ∃ a, s = .atom a := Iff.rfl

theorem gcPre_atoms (b : ℕ) : AllAtoms (gcPre b) := by
  unfold gcPre gcHead gcTailPre
  refine allAtoms_append (allAtoms_append ?_ (allAtoms_map_flatten fun i _ ↦ ?_)) ?_
  · intro s hs; simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩
  · intro s hs; simp only [gcIterAt, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩
  · intro s hs; simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩

theorem lrRound_atoms (nt bits o : ℕ) (cap : List ℕ) (cur cl tabs : ℕ) (pad : Option ℕ) :
    AllAtoms (lrRound nt bits o cap cur cl tabs pad) := by
  intro s hs
  unfold lrRound at hs
  simp only [List.mem_append, List.mem_flatten, List.mem_map, List.mem_range] at hs
  rcases hs with (((((⟨_, ⟨i, -, rfl⟩, hs⟩ | hs) | hs) | hs) | hs) | ⟨_, ⟨j, -, rfl⟩, hs⟩) | hs
  · unfold lrStep lrScalar at hs
    simp only [List.mem_append] at hs
    rcases hs with hs | hs
    · split at hs
      · simp only [List.mem_singleton] at hs; subst hs; exact ⟨_, rfl⟩
      · simp at hs
    · split at hs <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hs <;>
        rcases hs with rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩
  · split at hs
    · simp at hs
    · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with hs | rfl | rfl | rfl
      · split at hs
        · simp only [List.mem_singleton] at hs; subst hs; exact ⟨_, rfl⟩
        · simp at hs
      all_goals exact ⟨_, rfl⟩
  · unfold lrPadCells at hs
    split at hs
    · simp at hs
    split at hs
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl <;> exact ⟨_, rfl⟩
    split at hs
    · simp at hs
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩
  · simp only [List.mem_singleton] at hs; subst hs; exact ⟨_, rfl⟩
  · split at hs
    · simp at hs
    · exact allAtoms_renameList _ (gcPre_atoms bits) s hs
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl <;> exact ⟨_, rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩

theorem lrRounds_atoms (nt bits pts tabs : ℕ) : ∀ (k o : ℕ) (cap : List ℕ) (cur cl : ℕ) (pad : Option ℕ),
    AllAtoms (lrRounds nt bits pts tabs k o cap cur cl pad).1
  | 0, _, _, _, _, _ => allAtoms_nil
  | k + 1, o, cap, cur, cl, pad => by
    rw [lrRounds_succ]
    exact allAtoms_append (allAtoms_append (lrRounds_atoms nt bits pts tabs k o cap cur cl pad)
      (lrRound_atoms _ _ _ _ _ _ _ _)) (allAtoms_cons allAtoms_nil)

theorem lrRounds_cap_length (nt bits pts tabs : ℕ) : ∀ (k o : ℕ) (cap : List ℕ) (cur cl : ℕ) (pad : Option ℕ),
    cap.length = 5 → (lrRounds nt bits pts tabs k o cap cur cl pad).2.1.length = 5
  | 0, _, _, _, _, _, h => h
  | k + 1, o, cap, cur, cl, pad, _ => by rw [lrRounds_succ]; simp [lrOutCap]

end
end LeanVM.Guest.B1.Link
