/-
  LeanVM.Guest.B1.VsC.RoundsC

  `link_round`'s template, evaluated forward on a chain of rounds, holds and returns the chain's
  states.
-/

module

public import LeanVM.Guest.B1.VsC.Fwd
public import LeanVM.Guest.B1.Link.RoundsSound

/-!
# Rounds, completely

A chain of rounds (`RoundChain`) is determined by its first state and the memory
(`roundStep_det`): the words at the cursor fix the scalars and the nonce, the rest is computed.

`lrRound_complete0`: on a valuation satisfying the template's defining equations (`Fwd.Good`), its
products forward, its state the chain's, the cursor's words not stores, every atom of a round with
no grind holds; its challenge and the state after it are the chain's (by `lrRound_step` and
`roundStep_det`). `lrRounds_complete0`: the same for `k` rounds in a row, each challenge stored at
`pts`.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.B1
open LeanVM.Guest.B1.Link LeanVM.Guest.B1.Fwd LeanVM.Protocol.Verifier

@[expose] public section

/-! ## A chain is determined -/

theorem grindSqueeze_congr {s : Fs} {bits : ℕ} {n n' : E} (h : grindWords bits n = grindWords bits n') :
    s.grindSqueeze bits n = s.grindSqueeze bits n' := by
  unfold grindWords at h
  by_cases hb : bits = 0
  · simp [Fs.grindSqueeze, hb]
  · simp only [hb, ↓reduceIte, List.cons.injEq, and_true] at h
    rw [h]

/-- **One round from a state is determined** by the memory. -/
theorem roundStep_det {rd : Reader} {nt bits : ℕ} {st s1 s2 : RSt} {y1 y2 : E}
    (h1 : RoundStep rd nt bits st y1 s1) (h2 : RoundStep rd nt bits st y2 s2) : y1 = y2 ∧ s1 = s2 := by
  obtain ⟨c0, t, n, ht, hr, -, hg, hc, hl⟩ := h1
  obtain ⟨c0', t', n', ht', hr', -, hg', hc', hl'⟩ := h2
  have he := readsAt_eq hr hr' (by simp [ht, ht', grindWords_length])
  simp only [List.cons_append, List.cons.injEq] at he
  obtain ⟨rfl, he⟩ := he
  obtain ⟨rfl, hgw⟩ := List.append_inj he (by rw [ht, ht'])
  rw [grindSqueeze_congr hgw, hg'] at hg
  simp only [Prod.mk.injEq, Fs.mk.injEq, and_true] at hg
  obtain ⟨rfl, hcap⟩ := hg
  refine ⟨rfl, ?_⟩
  obtain ⟨cap1, cur1, cl1⟩ := s1
  obtain ⟨cap2, cur2, cl2⟩ := s2
  simp only at hcap hc hc' hl hl'
  rw [hgw] at hc
  subst hcap
  rw [hc, hc', hl, hl']

theorem roundChain_append_inv {rd : Reader} {nt bits : ℕ} : ∀ {st : RSt} {l1 l2 : List (E × RSt)},
    RoundChain rd nt bits st (l1 ++ l2) → RoundChain rd nt bits st l1 ∧ RoundChain rd nt bits (chainLast st l1) l2
  | _, [], _, h => ⟨trivial, h⟩
  | _, (_, _) :: _, _, ⟨hs, h⟩ => ⟨⟨hs, (roundChain_append_inv h).1⟩, (roundChain_append_inv h).2⟩

/-! ## The template's side conditions -/

/-- **The atoms of a round needing a side condition, and its hints**: a load at the cursor (a
scalar, or the grind's nonce), a product, or an atom of the inlined `grind_check`. -/
theorem lrRound_side {nt bits o : ℕ} {cap : List ℕ} {cur cl tabs : ℕ} {pad : Option ℕ} {a : Atom}
    (ha : Stmt.atom a ∈ lrRound nt bits o cap cur cl tabs pad) (hn : needsSide a = true ∨ ∃ h, a = .hint h) :
    (∃ d i, a = .load d (.n cur) i ∧ (i ≤ nt ∨ (bits ≠ 0 ∧ i = nt + 1))) ∨ (∃ d x y, a = .mul d x y) ∨
      (bits ≠ 0 ∧ Stmt.atom a ∈ gcInlineT bits (lrF o nt bits pad + 13) (.n (lrF o nt bits pad + 1)) (.n tabs)) := by
  unfold lrRound at ha
  simp only [List.mem_append, List.mem_flatten, List.mem_map, List.mem_range] at ha
  rcases ha with (((((⟨_, ⟨i, hi, rfl⟩, hs⟩ | hs) | hs) | hs) | hs) | ⟨_, ⟨j, -, rfl⟩, hs⟩) | hs
  · unfold lrStep lrScalar at hs
    simp only [List.mem_append] at hs
    rcases hs with hs | hs
    · split at hs
      · simp only [List.mem_singleton, lrPerm, Stmt.atom.injEq] at hs; subst hs; simp [needsSide] at hn
      · simp at hs
    · left
      split at hs <;> simp only [List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at hs <;>
        rcases hs with rfl | rfl | rfl | rfl <;>
        first | exact ⟨_, _, rfl, Or.inl (by omega)⟩ | simp [needsSide] at hn
  · split at hs
    · simp at hs
    · rename_i hb
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at hs
      rcases hs with hs | rfl | rfl | rfl
      · split at hs
        · simp only [List.mem_singleton, lrPerm, Stmt.atom.injEq] at hs; subst hs; simp [needsSide] at hn
        · simp at hs
      · exact Or.inl ⟨_, _, rfl, Or.inr ⟨hb, rfl⟩⟩
      all_goals simp [needsSide] at hn
  · unfold lrPadCells at hs
    split at hs
    · simp at hs
    split at hs
    · simp only [List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at hs
      rcases hs with rfl | rfl <;> simp [needsSide] at hn
    split at hs
    · simp at hs
    · simp only [List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl <;> simp [needsSide] at hn
  · simp only [List.mem_singleton, Stmt.atom.injEq] at hs; subst hs; simp [needsSide] at hn
  · split at hs
    · simp at hs
    · rename_i hb
      exact Or.inr (Or.inr ⟨hb, hs⟩)
  · simp only [List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at hs
    rcases hs with rfl | rfl | rfl <;> first | exact Or.inr (Or.inl ⟨_, _, _, rfl⟩) | simp [needsSide] at hn
  · simp only [List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact Or.inr (Or.inl ⟨_, _, _, rfl⟩) | simp [needsSide] at hn

theorem lrP_le_lrF (o nt bits : ℕ) (pad : Option ℕ) : lrP o nt bits ≤ lrF o nt bits pad := by
  unfold lrF lrPadCells
  split_ifs <;> cases pad <;> simp

theorem le_lrD (o nt bits : ℕ) (pad : Option ℕ) : o ≤ lrD o nt bits pad := by
  have h1 := lrP_le_lrF o nt bits pad
  have h2 : o ≤ lrP o nt bits := by unfold lrP lrE; omega
  unfold lrD lrC
  omega

/-! ## A round -/

/-- **A round with no grind holds on its forward valuation**, from the chain's step. -/
theorem lrRound_complete0 {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val} {nt o : ℕ} {cap : List ℕ}
    {cur cl tabs : ℕ} {pad : Option ℕ} (hnt : 1 ≤ nt) (hnt' : nt ≤ 32)
    (hG : ∀ a, Stmt.atom a ∈ lrRound nt 0 o cap cur cl tabs pad → Good rd S w σ a)
    (hmf : ∀ d x y, Stmt.atom (.mul d x y) ∈ lrRound nt 0 o cap cur cl tabs pad → x.idx < d.idx ∧ y.idx < d.idx)
    (hcS : ∀ d i, Atom.load d (.n cur) i ∉ S)
    (hpad : ∀ z, pad = some z → ∀ j < 4, σ (.n (z + j)) = 0)
    {st st' : RSt} {y : E} (hst : rstOf σ cap cur cl = st) (hstep : RoundStep rd nt 0 st y st') :
    (∀ a, Stmt.atom a ∈ lrRound nt 0 o cap cur cl tabs pad → a.Holds rd σ) ∧
      σ (.n (lrD o nt 0 pad + 3)) = y ∧
      rstOf σ (lrOutCap nt 0 o pad) (lrD o nt 0 pad + 6) (lrD o nt 0 pad + 8) = st' ∧
      ∀ z, lrPad nt 0 o pad = some z → ∀ j < 4, σ (.n (z + j)) = 0 := by
  have hcur : σ (.n cur) = st.cur := by rw [← hst]; rfl
  have hA : ∀ a, Stmt.atom a ∈ lrRound nt 0 o cap cur cl tabs pad → a.Holds rd σ := by
    intro a ha
    refine atoms_holds (atoms := [a]) (S := S) (w := w)
      (fun b hb => by rw [List.mem_singleton.mp hb]; exact hG a ha) (fun b hb hn => ?_) a List.mem_cons_self
    rw [List.mem_singleton.mp hb] at hn ⊢
    rcases lrRound_side ha (Or.inl hn) with ⟨d, i, rfl, hi⟩ | ⟨d, x, y, rfl⟩ | ⟨hb0, -⟩
    · right
      obtain ⟨c0, tail, n, htl, hr, -⟩ := hstep
      have hi' : i < (c0 :: tail ++ grindWords 0 n).length := by
        simp only [grindWords, ↓reduceIte, List.append_nil, List.length_cons, htl]
        rcases hi with hi | ⟨h, -⟩
        · omega
        · exact absurd rfl h
      have hl := hr i hi'
      rw [← hcur] at hl
      simp only [Side, hcS d i, ↓reduceIte]
      exact ⟨hl.1, by rw [hl.2]; rfl⟩
    · simp [needsSide, hmf d x y ha] at hn
    · exact absurd rfl hb0
  obtain ⟨hstep', hpad'⟩ := lrRound_step hA hnt hnt' (Or.inl rfl) hpad (fun h => absurd rfl h)
  rw [hst] at hstep'
  obtain ⟨e1, e2⟩ := roundStep_det hstep' hstep
  exact ⟨hA, e1, e2, hpad'⟩

/-! ## Rounds in a row -/

/-- **`k` rounds with no grind hold on their forward valuation**, from a chain of `k` rounds, the
challenges stored at `pts`; the state after them is the chain's last. The stores `S` are through
values below `m`, the cursors and the template's values from `m` on. -/
theorem lrRounds_complete0 {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val} {nt pts tabs m : ℕ}
    (hnt : 1 ≤ nt) (hnt' : nt ≤ 32) (hSp : ∀ d p off, Atom.load d p off ∈ S → p.idx < m) :
    ∀ (k o : ℕ) (cap : List ℕ) (cur cl : ℕ) (pad : Option ℕ) (st : RSt) (l : List (E × RSt)),
      m ≤ cur → m ≤ o →
      (∀ a, Stmt.atom a ∈ (lrRounds nt 0 pts tabs k o cap cur cl pad).1 → Good rd S w σ a) →
      (∀ d x y, Stmt.atom (.mul d x y) ∈ (lrRounds nt 0 pts tabs k o cap cur cl pad).1 →
        x.idx < d.idx ∧ y.idx < d.idx) →
      (∀ z, pad = some z → ∀ j < 4, σ (.n (z + j)) = 0) →
      rstOf σ cap cur cl = st → l.length = k → RoundChain rd nt 0 st l →
      ReadsAt rd (σ (.n pts)) (l.map Prod.fst) →
      (∀ a, Stmt.atom a ∈ (lrRounds nt 0 pts tabs k o cap cur cl pad).1 → a.Holds rd σ) ∧
        rstOf σ (lrRounds nt 0 pts tabs k o cap cur cl pad).2.1 (lrRounds nt 0 pts tabs k o cap cur cl pad).2.2.1
          (lrRounds nt 0 pts tabs k o cap cur cl pad).2.2.2.1 = chainLast st l ∧
        m ≤ (lrRounds nt 0 pts tabs k o cap cur cl pad).2.2.1 ∧
        m ≤ (lrRounds nt 0 pts tabs k o cap cur cl pad).2.2.2.2.1 ∧
        ∀ z, (lrRounds nt 0 pts tabs k o cap cur cl pad).2.2.2.2.2 = some z → ∀ j < 4, σ (.n (z + j)) = 0
  | 0, o, cap, cur, cl, pad, st, l, hc, ho, _, _, hpad, hst, hl, _, _ => by
    obtain rfl : l = [] := List.eq_nil_of_length_eq_zero hl
    exact ⟨fun a ha => by simp [lrRounds] at ha, hst, hc, ho, hpad⟩
  | k + 1, o, cap, cur, cl, pad, st, l, hc, ho, hG, hmf, hpad, hst, hl, hch, hpts => by
    obtain ⟨l1, p, rfl⟩ : ∃ l1 p, l = l1 ++ [p] :=
      ⟨l.dropLast, l.getLast (by rintro rfl; simp at hl), (List.dropLast_append_getLast _).symm⟩
    obtain ⟨y, st'⟩ := p
    have hl1 : l1.length = k := by simpa using hl
    obtain ⟨hch1, hch2⟩ := roundChain_append_inv hch
    have hpts' : ReadsAt rd (σ (.n pts)) (l1.map Prod.fst ++ [y]) := by simpa using hpts
    have hsub : ∀ a, Stmt.atom a ∈ (lrRounds nt 0 pts tabs k o cap cur cl pad).1 →
        Stmt.atom a ∈ (lrRounds nt 0 pts tabs (k + 1) o cap cur cl pad).1 := fun a ha => by
      rw [lrRounds_succ]; exact List.mem_append_left _ (List.mem_append_left _ ha)
    obtain ⟨hA1, hlast, hc1, ho1, hpad1⟩ := lrRounds_complete0 hnt hnt' hSp k o cap cur cl pad st l1 hc ho
      (fun a ha => hG a (hsub a ha)) (fun d x y ha => hmf d x y (hsub _ ha)) hpad hst hl1 hch1
      (readsAt_prefix hpts')
    have hy := readsAt_last hpts'
    rw [lrRounds_succ] at hG hmf ⊢
    generalize lrRounds nt 0 pts tabs k o cap cur cl pad = prev at hA1 hlast hc1 ho1 hpad1 hG hmf ⊢
    obtain ⟨as, cap', cur', cl', o', pad'⟩ := prev
    dsimp only at hA1 hlast hc1 ho1 hpad1 hG hmf ⊢
    have hmemR : ∀ a, Stmt.atom a ∈ lrRound nt 0 o' cap' cur' cl' tabs pad' →
        Stmt.atom a ∈ as ++ lrRound nt 0 o' cap' cur' cl' tabs pad' ++
          [.atom (.load (.n (lrD o' nt 0 pad' + 3)) (.n pts) k)] := fun a ha =>
      List.mem_append_left _ (List.mem_append_right _ ha)
    obtain ⟨hR, hyv, hout, hpad2⟩ := lrRound_complete0 hnt hnt' (fun a ha => hG a (hmemR a ha))
      (fun d x y ha => hmf d x y (hmemR _ ha))
      (fun d i hS => absurd (hSp d _ i hS) (by show ¬ cur' < m; omega)) hpad1 hlast hch2.1
    have hD := le_lrD o' nt 0 pad'
    refine ⟨fun a ha => ?_, ?_, by omega, by simp only [lrNext]; omega, hpad2⟩
    · rcases List.mem_append.mp ha with ha | ha
      · rcases List.mem_append.mp ha with ha | ha
        · exact hA1 a ha
        · exact hR a ha
      · simp only [List.mem_singleton, Stmt.atom.injEq] at ha
        subst ha
        show LoadHolds rd (σ (.n pts)) k (σ (.n (lrD o' nt 0 pad' + 3)))
        rw [hyv]
        simpa [hl1] using hy
    · rw [chainLast_append]; exact hout

end
end LeanVM.Guest.B1.VsC
