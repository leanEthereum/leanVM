/-
  LeanVM.Guest.B1.VsC.RoundsLoadsC

  Where a chain of rounds with no grind loads: its challenges' cells, and the stream words its
  cursors read.
-/

module

public import LeanVM.Guest.B1.VsC.RoundsC

/-!
# The rounds' loads

A round consumes `nt + 1` stream words with no grind (`rlen`), so the cursor before round `r` of a
chain is the first cursor times `g^(r · rlen)` (`chain_cur`). `lrRounds_loads0`: on the forward
valuation of `k` rounds with no grind (`lrRounds_complete0`'s hypotheses), every load of the
template is a challenge's store at `pts` or a scalar's read at the cursor before round `r < k`,
offset `i ≤ nt`.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.B1
open LeanVM.Guest.B1.Link LeanVM.Guest.B1.Fwd LeanVM.Protocol.Verifier

@[expose] public section

/-- The stream words a round consumes. -/
def rlen (nt bits : ℕ) : ℕ := nt + 1 + if bits = 0 then 0 else 1

theorem roundStep_cur {rd : Reader} {nt bits : ℕ} {st st' : RSt} {y : E} (h : RoundStep rd nt bits st y st') :
    st'.cur = st.cur * gen ^ rlen nt bits := by
  obtain ⟨c0, tail, n, -, -, -, -, hc, -⟩ := h
  rw [hc, grindWords_length]; rfl

/-- **The cursor before round `r`** of a chain. -/
theorem chain_cur {rd : Reader} {nt bits : ℕ} : ∀ (st : RSt) (l : List (E × RSt)), RoundChain rd nt bits st l →
    ∀ r ≤ l.length, (chainLast st (l.take r)).cur = st.cur * gen ^ (r * rlen nt bits)
  | st, [], _, r, hr => by
    obtain rfl : r = 0 := by simpa using hr
    simp [chainLast]
  | st, (y, st') :: l, ⟨hs, hc⟩, r, hr => by
    rcases r with _ | r
    · simp [chainLast]
    · simp only [List.take_succ_cons, chainLast]
      rw [chain_cur st' l hc r (by simpa using hr), roundStep_cur hs, mul_assoc, ← pow_add]
      congr 2; ring

/-- The rounds' atoms, by round: round `r`'s template or its challenge's store. -/
theorem mem_lrRounds {nt bits pts tabs : ℕ} : ∀ (k o : ℕ) (cap : List ℕ) (cur cl : ℕ) (pad : Option ℕ) (a : Atom),
    Stmt.atom a ∈ (lrRounds nt bits pts tabs k o cap cur cl pad).1 →
    ∃ r < k, Stmt.atom a ∈ lrRound nt bits (lrRounds nt bits pts tabs r o cap cur cl pad).2.2.2.2.1
        (lrRounds nt bits pts tabs r o cap cur cl pad).2.1 (lrRounds nt bits pts tabs r o cap cur cl pad).2.2.1
        (lrRounds nt bits pts tabs r o cap cur cl pad).2.2.2.1 tabs (lrRounds nt bits pts tabs r o cap cur cl pad).2.2.2.2.2 ∨
      ∃ d, a = .load d (.n pts) r
  | 0, _, _, _, _, _, a, h => by simp [lrRounds] at h
  | k + 1, o, cap, cur, cl, pad, a, h => by
    rw [lrRounds_succ] at h
    rcases List.mem_append.mp h with h | h
    · rcases List.mem_append.mp h with h | h
      · obtain ⟨r, hr, h'⟩ := mem_lrRounds k o cap cur cl pad a h
        exact ⟨r, by omega, h'⟩
      · exact ⟨k, by omega, Or.inl h⟩
    · simp only [List.mem_singleton, Stmt.atom.injEq] at h
      exact ⟨k, by omega, Or.inr ⟨_, h⟩⟩

theorem lrRounds_mono {nt bits pts tabs o : ℕ} {cap : List ℕ} {cur cl : ℕ} {pad : Option ℕ} {a : Atom} (r : ℕ) :
    ∀ t, Stmt.atom a ∈ (lrRounds nt bits pts tabs r o cap cur cl pad).1 →
      Stmt.atom a ∈ (lrRounds nt bits pts tabs (r + t) o cap cur cl pad).1
  | 0, h => h
  | t + 1, h => by
    rw [← Nat.add_assoc, lrRounds_succ]
    exact List.mem_append_left _ (List.mem_append_left _ (lrRounds_mono r t h))

/-- **The loads of `k` rounds with no grind**: a challenge's store at `pts`, or a scalar's read at the
cursor before round `r`. -/
theorem lrRounds_loads0 {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val} {nt pts tabs m : ℕ}
    (hnt : 1 ≤ nt) (hnt' : nt ≤ 32) (hSp : ∀ d p off, Atom.load d p off ∈ S → p.idx < m)
    (k o : ℕ) (cap : List ℕ) (cur cl : ℕ) (pad : Option ℕ) (st : RSt) (l : List (E × RSt))
    (hc : m ≤ cur) (ho : m ≤ o)
    (hG : ∀ a, Stmt.atom a ∈ (lrRounds nt 0 pts tabs k o cap cur cl pad).1 → Good rd S w σ a)
    (hmf : ∀ d x y, Stmt.atom (.mul d x y) ∈ (lrRounds nt 0 pts tabs k o cap cur cl pad).1 →
      x.idx < d.idx ∧ y.idx < d.idx)
    (hpad : ∀ z, pad = some z → ∀ j < 4, σ (.n (z + j)) = 0)
    (hst : rstOf σ cap cur cl = st) (hl : l.length = k) (hch : RoundChain rd nt 0 st l)
    (hpts : ReadsAt rd (σ (.n pts)) (l.map Prod.fst)) :
    ∀ d p off, Stmt.atom (.load d p off) ∈ (lrRounds nt 0 pts tabs k o cap cur cl pad).1 →
      (p = .n pts ∧ off < k) ∨ ∃ r < k, off ≤ nt ∧ σ p = (chainLast st (l.take r)).cur := by
  intro d p off ha
  obtain ⟨r, hr, h | ⟨d', he⟩⟩ := mem_lrRounds k o cap cur cl pad _ ha
  · -- a round's read at its cursor
    have hsub : ∀ a, Stmt.atom a ∈ (lrRounds nt 0 pts tabs r o cap cur cl pad).1 →
        Stmt.atom a ∈ (lrRounds nt 0 pts tabs k o cap cur cl pad).1 := fun a ha' => by
      obtain ⟨t, rfl⟩ : ∃ t, k = r + t := ⟨k - r, by omega⟩
      exact lrRounds_mono r t ha'
    have hlr : (l.take r).length = r := by simp; omega
    obtain ⟨-, hlast, -, -, -⟩ := lrRounds_complete0 (w := w) hnt hnt' hSp r o cap cur cl pad st (l.take r) hc ho
      (fun a ha' => hG a (hsub a ha')) (fun d x y ha' => hmf d x y (hsub _ ha')) hpad hst hlr
      (by
        have := hch
        rw [← List.take_append_drop r l] at this
        exact (roundChain_append_inv this).1)
      (by
        have := hpts
        rw [← List.take_append_drop r l, List.map_append] at this
        exact readsAt_prefix this)
    rcases lrRound_side h (Or.inl rfl) with ⟨d', i, he, hi⟩ | ⟨_, _, _, he⟩ | ⟨hb, -⟩
    · obtain ⟨rfl, rfl, rfl⟩ := Atom.load.inj he
      refine Or.inr ⟨r, hr, by omega, ?_⟩
      rw [← hlast]; rfl
    · cases he
    · exact absurd rfl hb
  · obtain ⟨rfl, rfl, rfl⟩ := Atom.load.inj he
    exact Or.inl ⟨rfl, hr⟩

end
end LeanVM.Guest.B1.VsC
