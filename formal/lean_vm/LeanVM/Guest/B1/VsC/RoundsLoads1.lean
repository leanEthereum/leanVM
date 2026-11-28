/-
  LeanVM.Guest.B1.VsC.RoundsLoads1

  Where a chain of rounds grinding one bit loads: its challenges' cells, the stream words its
  cursors read, and the window table.
-/

module

public import LeanVM.Guest.B1.VsC.RoundsLoadsC
public import LeanVM.Guest.B1.VsC.RoundsC1

/-!
# The rounds' loads at one bit of grind

`lrRounds_loads1`: on the forward valuation of `k` rounds grinding one bit (`lrRounds_complete1`'s
hypotheses), every load of the template is a challenge's store at `pts`, a read at the cursor
before round `r < k` at offset `i ≤ nt + 1` (the scalars and the nonce), or one of `grind_check`'s
table reads, at `tabs·g^e`, `e < 2^11` (`gcInlineT_load_one`, `lrRound_complete1`'s pointers).
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.B1
open LeanVM.Guest.B1.Link LeanVM.Guest.B1.Fwd LeanVM.Protocol.Verifier LeanVM.Guest.Value

@[expose] public section

/-- A word `a` past `x`, read at offset `b`, is the word `a + b` past `x`. -/
theorem addr_mul_gen_pow {x : E} {a b i : ℕ} (hi : x.limb 0 * addressOfIndex (a + b) = addressOfIndex i) :
    (x * gen ^ a).limb 0 * addressOfIndex b = addressOfIndex i := by
  rw [← hi, gen_pow_eq_ofK, limb0_mul_ofK, mul_assoc, addressOfIndex, addressOfIndex, addressOfIndex, ← pow_add]

/-- Round `r`'s step of a chain longer than `r`. -/
theorem roundChain_step {rd : Reader} {nt bits : ℕ} {st : RSt} {l : List (E × RSt)}
    (h : RoundChain rd nt bits st l) {r : ℕ} (hr : r < l.length) :
    ∃ y st', RoundStep rd nt bits (chainLast st (l.take r)) y st' := by
  rw [← List.take_append_drop r l] at h
  have h2 := (roundChain_append_inv h).2
  cases hd : l.drop r with
  | nil => simp only [List.drop_eq_nil_iff] at hd; omega
  | cons p rest =>
    rw [hd] at h2
    exact ⟨p.1, p.2, h2.1⟩

/-- **The loads of `k` rounds grinding one bit**: a challenge's store at `pts`, a read at the cursor
before round `r`, or a read of the window table. -/
theorem lrRounds_loads1 {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val} {nt pts tabs m : ℕ}
    (hnt : 1 ≤ nt) (hnt' : nt ≤ 32) (hk3 : nt % 4 ≠ 3) (hSp : ∀ d p off, Atom.load d p off ∈ S → p.idx < m)
    (hrc : ∀ v ≤ 11, ∀ e < 2 ^ v, ∃ y t1 t2 : E, LoadHolds rd (gen ^ e) 0 t1 ∧
      wBound v = gen ^ e * y ∧ LoadHolds rd y 0 t2)
    (ht : WinTabs rd (σ (.n tabs)))
    (k o : ℕ) (cap : List ℕ) (cur cl : ℕ) (pad : Option ℕ) (st : RSt) (l : List (E × RSt))
    (hc : m ≤ cur) (ho : m ≤ o) (hto : tabs < o)
    (hG : ∀ a, Stmt.atom a ∈ (lrRounds nt 1 pts tabs k o cap cur cl pad).1 → Good rd S w σ a)
    (hmf : ∀ d x y, Stmt.atom (.mul d x y) ∈ (lrRounds nt 1 pts tabs k o cap cur cl pad).1 →
      x.idx < d.idx ∧ y.idx < d.idx)
    (hSg : ∀ a ∈ S, ∀ r < k, loadInto (lrOg nt pts tabs r o cap cur cl pad)
      (lrOg nt pts tabs r o cap cur cl pad + (gcLen 1 - 2)) a = false)
    (hW : ∀ r < k, ∀ j ≤ gcW 1, w (lrOg nt pts tabs r o cap cur cl pad + j) =
      gcWin 1 (roundWord rd nt (chainLast st (l.take r))) j)
    (hpad : ∀ z, pad = some z → ∀ j < 4, σ (.n (z + j)) = 0)
    (hst : rstOf σ cap cur cl = st) (hl : l.length = k) (hch : RoundChain rd nt 1 st l)
    (hpts : ReadsAt rd (σ (.n pts)) (l.map Prod.fst)) :
    ∀ d p off, Stmt.atom (.load d p off) ∈ (lrRounds nt 1 pts tabs k o cap cur cl pad).1 →
      (p = .n pts ∧ off < k) ∨ (∃ r < k, off ≤ nt + 1 ∧ σ p = (chainLast st (l.take r)).cur) ∨
        (off = 0 ∧ ∃ e < 2 ^ 11, σ p = σ (.n tabs) * gen ^ e) := by
  intro d p off ha
  obtain ⟨r, hr, h | ⟨d', he⟩⟩ := mem_lrRounds k o cap cur cl pad _ ha
  · have hsub : ∀ t, r + t ≤ k → ∀ a, Stmt.atom a ∈ (lrRounds nt 1 pts tabs (r + t) o cap cur cl pad).1 →
        Stmt.atom a ∈ (lrRounds nt 1 pts tabs k o cap cur cl pad).1 := fun t ht' a ha' => by
      obtain ⟨u, hu⟩ : ∃ u, k = r + t + u := ⟨k - (r + t), by omega⟩
      rw [hu]; exact lrRounds_mono (r + t) u ha'
    have hsub0 : ∀ a, Stmt.atom a ∈ (lrRounds nt 1 pts tabs r o cap cur cl pad).1 →
        Stmt.atom a ∈ (lrRounds nt 1 pts tabs k o cap cur cl pad).1 := hsub 0 (by omega)
    have hlr : (l.take r).length = r := by simp; omega
    have hchr : RoundChain rd nt 1 st (l.take r) := by
      have := hch; rw [← List.take_append_drop r l] at this; exact (roundChain_append_inv this).1
    have hptsr : ReadsAt rd (σ (.n pts)) ((l.take r).map Prod.fst) := by
      have := hpts; rw [← List.take_append_drop r l, List.map_append] at this; exact readsAt_prefix this
    obtain ⟨-, hlast, hc1, -, hto1, hpad1⟩ := lrRounds_complete1 (w := w) hnt hnt' hk3 hSp hrc ht r o cap cur cl
      pad st (l.take r) hc ho hto (fun a ha' => hG a (hsub0 a ha')) (fun d x y ha' => hmf d x y (hsub0 _ ha'))
      (fun a ha' r' hr' => hSg a ha' r' (by omega))
      (fun r' hr' j hj => by rw [hW r' (by omega) j hj, List.take_take, Nat.min_eq_left hr'.le]) hpad hst hlr
      hchr hptsr
    rcases lrRound_side h (Or.inl rfl) with ⟨d', i, he, hi⟩ | ⟨_, _, _, he⟩ | ⟨-, hg⟩
    · obtain ⟨rfl, rfl, rfl⟩ := Atom.load.inj he
      refine Or.inr (Or.inl ⟨r, hr, by omega, ?_⟩)
      rw [← hlast]; rfl
    · cases he
    · obtain ⟨rfl, hp⟩ := gcInlineT_load_one hg
      refine Or.inr (Or.inr ⟨rfl, ?_⟩)
      obtain ⟨y, st', hstep⟩ := roundChain_step hch (r := r) (by omega)
      have hmR : ∀ a, Stmt.atom a ∈ lrRound nt 1 (lrRounds nt 1 pts tabs r o cap cur cl pad).2.2.2.2.1
          (lrRounds nt 1 pts tabs r o cap cur cl pad).2.1 (lrRounds nt 1 pts tabs r o cap cur cl pad).2.2.1
          (lrRounds nt 1 pts tabs r o cap cur cl pad).2.2.2.1 tabs (lrRounds nt 1 pts tabs r o cap cur cl pad).2.2.2.2.2 →
          Stmt.atom a ∈ (lrRounds nt 1 pts tabs k o cap cur cl pad).1 := fun a ha' =>
        hsub 1 (by omega) a (by rw [lrRounds_succ]; exact List.mem_append_left _ (List.mem_append_right _ ha'))
      have hF := lrP_le_lrF (lrRounds nt 1 pts tabs r o cap cur cl pad).2.2.2.2.1 nt 1
        (lrRounds nt 1 pts tabs r o cap cur cl pad).2.2.2.2.2
      have hP := lrP_ge (lrRounds nt 1 pts tabs r o cap cur cl pad).2.2.2.2.1 nt 1
      obtain ⟨-, -, -, -, hptr⟩ := lrRound_complete1 hnt hnt' hk3 (fun a ha' => hG a (hmR a ha'))
        (fun d x y ha' => hmf d x y (hmR _ ha')) (fun d i hS => absurd (hSp d _ i hS) (Nat.not_lt.mpr hc1))
        hpad1 hlast hstep (by omega) (fun a ha' => hSg a ha' r hr) hrc ht (fun j hj => hW r hr j hj)
      exact hptr p hp
  · obtain ⟨rfl, rfl, rfl⟩ := Atom.load.inj he
    exact Or.inl ⟨rfl, hr⟩

end
end LeanVM.Guest.B1.VsC
