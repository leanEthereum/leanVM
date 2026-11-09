/-
  LeanVM.Guest.B1.Gkr.WalkC

  The GKR phase's accepting run read back as the walk `verify_bus_gkr` follows: from the words it
  reads, the root, the odd step at an odd depth, and each step of two levels with the sponge, the
  state and the stream offset before it.
-/

module

public import LeanVM.Guest.B1.Gkr.SpecInv
public import LeanVM.Guest.B1.Gkr.Rounds

/-!
# The walk, read back

The walk is a function of the words the phase reads (`xs`) and the carried capacity (`cap0`):
`gkRootS`, `gkRootSt` (the two roots waiting, the state `[root, root, count]`), the odd step's
words `gkOdd` (two children a tree), the slots `gkSl cap0 xs sh j` (sponge, state, offset) before
step `j` of two levels and its words `gkD` (`gkStepAt`: `L = 2j + sh` rounds of four words, then
four children a tree).

`gk_walk`: an accepting run of `gkrPhase depth` from a carried capacity reads the count root
nonzero, takes the odd step at an odd depth, takes every step of two levels (`GkStepD.Ok`), each
reading its words where the last left off, and ends at the last slot, every word read.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## A step's words in the stream -/

/-- A step's words at offset `o` of the stream: `L` rounds of four words, then the three trees'
`c` children each. -/
def gkStepAt (zs : List E) (o L c : ℕ) : GkStepD :=
  ⟨(List.range L).map fun r ↦ (zs.drop (o + 4 * r)).take 4, (zs.drop (o + 4 * L)).take c,
    (zs.drop (o + 4 * L + c)).take c, (zs.drop (o + 4 * L + 2 * c)).take c⟩

theorem tb_flatten_chunk : ∀ (cs : List (List E)) (t : List E), (∀ c ∈ cs, c.length = 4) →
    ∀ r (hr : r < cs.length), ((cs.flatten ++ t).drop (4 * r)).take 4 = cs[r]
  | c :: cs, t, h4, 0, _ => by
    simp only [List.flatten_cons, List.append_assoc, Nat.mul_zero, List.drop_zero,
      List.getElem_cons_zero]
    exact List.take_left' (h4 c (by simp))
  | c :: cs, t, h4, r + 1, hr => by
    rw [List.flatten_cons, List.append_assoc, show 4 * (r + 1) = 4 + 4 * r by ring,
      ← List.drop_drop, List.drop_left' (h4 c (by simp)), List.getElem_cons_succ]
    exact tb_flatten_chunk cs t (fun c' hc' => h4 c' (by simp [hc'])) r (by simpa using hr)

/-- **A step's words, located**: the words starting the stream at `o` are `gkStepAt`'s. -/
theorem gkStepAt_eq {zs rest : List E} {o L c : ℕ} {D : GkStepD} (hd : zs.drop o = D.xs ++ rest)
    (hl : D.cs.length = L) (h4 : ∀ x ∈ D.cs, x.length = 4) (h0 : D.ch0.length = c)
    (h1 : D.ch1.length = c) (h2 : D.ch2.length = c) :
    D = gkStepAt zs o L c ∧ rest = zs.drop (o + 4 * L + 3 * c) := by
  have hfl : D.cs.flatten.length = 4 * L := by rw [flatten_length_four h4, hl]
  have hd' : ∀ k, zs.drop (o + k) = (D.xs ++ rest).drop k := fun k => by
    rw [← hd, List.drop_drop]
  have hch : zs.drop (o + 4 * L) = D.ch0 ++ (D.ch1 ++ (D.ch2 ++ rest)) := by
    rw [hd', GkStepD.xs, List.append_assoc, List.drop_left' hfl, List.append_assoc,
      List.append_assoc]
  have hch1 : zs.drop (o + 4 * L + c) = D.ch1 ++ (D.ch2 ++ rest) := by
    rw [← List.drop_drop, hch, List.drop_left' h0]
  have hch2 : zs.drop (o + 4 * L + 2 * c) = D.ch2 ++ rest := by
    rw [show o + 4 * L + 2 * c = o + 4 * L + c + c by ring, ← List.drop_drop, hch1,
      List.drop_left' h1]
  refine ⟨?_, ?_⟩
  · obtain ⟨cs, ch0, ch1, ch2⟩ := D
    simp only at hl h4 h0 h1 h2 hch hch1 hch2 hd'
    simp only [gkStepAt, GkStepD.mk.injEq]
    refine ⟨?_, by rw [hch, List.take_left' h0], by rw [hch1, List.take_left' h1],
      by rw [hch2, List.take_left' h2]⟩
    apply List.ext_getElem (by simp [hl])
    intro r h1' h2'
    simp only [List.getElem_map, List.getElem_range]
    rw [hd' (4 * r), GkStepD.xs, List.append_assoc]
    exact (tb_flatten_chunk cs _ h4 r h1').symm
  · rw [show o + 4 * L + 3 * c = o + 4 * L + 2 * c + c by ring, ← List.drop_drop, hch2,
      List.drop_left' h2]

/-! ## The walk's slots -/

/-- The root's sponge: the carried capacity, the two roots waiting. -/
def gkRootS (cap0 xs : List E) : Fs :=
  ⟨cap0, [(xs.getD 0 0, dsObserve), (xs.getD 1 0, dsObserve)]⟩

/-- The root's state: the values `[root, root, count]`, no point. -/
def gkRootSt (xs : List E) : GkrState := ⟨[xs.getD 0 0, xs.getD 0 0, xs.getD 1 0], []⟩

/-- The odd step's words: no rounds, two children a tree. -/
def gkOdd (xs : List E) : GkStepD := gkStepAt xs 2 0 2

/-- The slot before the steps of two levels: the root, or after the odd step at an odd depth. -/
def gkSl0 (cap0 xs : List E) (sh : ℕ) : Fs × GkrState × ℕ :=
  if sh = 1 then
    ((gkOdd xs).s' (gkRootS cap0 xs) (gkRootSt xs) 1, (gkOdd xs).st' (gkRootS cap0 xs) (gkRootSt xs) 1,
      8)
  else (gkRootS cap0 xs, gkRootSt xs, 2)

/-- **The walk's slots**: the sponge, the state and the stream offset before step `j` of two
levels. -/
def gkSl (cap0 xs : List E) (sh : ℕ) : ℕ → Fs × GkrState × ℕ
  | 0 => gkSl0 cap0 xs sh
  | j + 1 =>
    ((gkStepAt xs (gkSl cap0 xs sh j).2.2 (2 * j + sh) 4).s' (gkSl cap0 xs sh j).1
        (gkSl cap0 xs sh j).2.1 2,
      (gkStepAt xs (gkSl cap0 xs sh j).2.2 (2 * j + sh) 4).st' (gkSl cap0 xs sh j).1
        (gkSl cap0 xs sh j).2.1 2,
      (gkSl cap0 xs sh j).2.2 + 4 * (2 * j + sh) + 12)

/-- Step `j`'s words. -/
def gkD (cap0 xs : List E) (sh j : ℕ) : GkStepD :=
  gkStepAt xs (gkSl cap0 xs sh j).2.2 (2 * j + sh) 4

theorem gkSl_succ (cap0 xs : List E) (sh j : ℕ) :
    gkSl cap0 xs sh (j + 1) =
      ((gkD cap0 xs sh j).s' (gkSl cap0 xs sh j).1 (gkSl cap0 xs sh j).2.1 2,
        (gkD cap0 xs sh j).st' (gkSl cap0 xs sh j).1 (gkSl cap0 xs sh j).2.1 2,
        (gkSl cap0 xs sh j).2.2 + 4 * (2 * j + sh) + 12) := rfl

/-- A step's new point: its two coordinates, then its rounds' challenges. -/
theorem gkStepD_point_length {D : GkStepD} {s : Fs} {st : GkrState} (h : D.Ok s st 2) :
    (D.st' s st 2).point.length = st.point.length + 2 := by
  show (D.ys s st 2 ++ (D.run s st).1).length = _
  rw [List.length_append, show (D.ys s st 2).length = 2 from rfl, GkStepD.run,
    tb_gkrRun_length _ _ _ _ h.1, h.1]
  ring

/-- **The pairs, read back**: `k` steps of two levels from the slot before them. -/
theorem gkrPairs_invT (cap0 xs : List E) (sh : ℕ)
    (hp0 : (gkSl cap0 xs sh 0).2.1.point.length = sh) :
    ∀ (k : ℕ) (stF : GkrState) (sF : Fs) (rest : List E),
      runT (gkrPairs k (gkSl cap0 xs sh 0).2.1)
        ⟨(gkSl cap0 xs sh 0).1, xs.drop (gkSl cap0 xs sh 0).2.2, [], []⟩ =
          some (stF, ⟨sF, rest, [], []⟩) →
      (∀ j < k, (gkD cap0 xs sh j).Ok (gkSl cap0 xs sh j).1 (gkSl cap0 xs sh j).2.1 2 ∧
        xs.drop (gkSl cap0 xs sh j).2.2 =
          (gkD cap0 xs sh j).xs ++ xs.drop (gkSl cap0 xs sh (j + 1)).2.2) ∧
      stF = (gkSl cap0 xs sh k).2.1 ∧ sF = (gkSl cap0 xs sh k).1 ∧
      rest = xs.drop (gkSl cap0 xs sh k).2.2 ∧
      (gkSl cap0 xs sh k).2.1.point.length = 2 * k + sh
  | 0, stF, sF, rest, h => by
    obtain ⟨e1, e2⟩ := runT_pure_some (a := (gkSl cap0 xs sh 0).2.1) h
    simp only [TSt.mk.injEq] at e2
    exact ⟨fun j hj => absurd hj (by omega), e1, e2.1, e2.2.1, by simpa using hp0⟩
  | k + 1, stF, sF, rest, h => by
    simp only [gkrPairs] at h
    obtain ⟨st1, ⟨s1, rest1, os1, R1⟩, h1, h2⟩ := runT_bind_some h
    have hos : os1 = [] := by
      obtain ⟨-, opre, -, ho, -⟩ := runT_frame _ _ _ _ h1
      exact (List.append_eq_nil_iff.mp ho.symm).2
    have hR : R1 = [] := by
      obtain ⟨C, hC⟩ := runT_roots _ _ _ _ h2
      exact (List.append_eq_nil_iff.mp hC.symm).1
    subst hos hR
    obtain ⟨hall, rfl, rfl, rfl, hpl⟩ := gkrPairs_invT cap0 xs sh hp0 k _ _ _ h1
    obtain ⟨D, hok, hd, rfl, rfl⟩ := gkrStep_invT h2 (Or.inl rfl)
    have hok' := hok
    obtain ⟨hl, h4, h0, h1', h2', -⟩ := hok'
    obtain ⟨rfl, rfl⟩ := gkStepAt_eq hd (hl.trans hpl) h4 h0 h1' h2'
    refine ⟨fun j hj => ?_, rfl, rfl, rfl, ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · exact hall j hj
      · exact ⟨hok, hd⟩
    · rw [gkSl_succ]
      exact (gkStepD_point_length hok).trans (by rw [hpl]; ring)

theorem tb_absorb_two (cap0 : List E) (x0 x1 : E) :
    ((⟨cap0, []⟩ : Fs).absorb x0 dsObserve).absorb x1 dsObserve =
      ⟨cap0, [(x0, dsObserve), (x1, dsObserve)]⟩ := by
  simp [Fs.absorb, rateScalars]

/-- **The GKR phase, read back**: from an accepting run of `gkrPhase depth` from a carried
capacity, the count root is nonzero, the odd step (at an odd depth) and every step of two levels
are taken on the words where the last left off, every word is read, and the run ends at the last
slot. -/
theorem gk_walk {depth : ℕ} {cap0 xs : List E} {r : E × List E × List E} {sF : Fs}
    (h : RunsTo (gkrPhase depth) ⟨cap0, []⟩ xs r sF) (hc : ∃ sp, (⟨cap0, []⟩ : Fs).Carries sp) :
    xs.getD 1 0 ≠ 0 ∧ 2 ≤ xs.length ∧
      (depth % 2 = 1 → (gkOdd xs).Ok (gkRootS cap0 xs) (gkRootSt xs) 1 ∧
        xs.drop 2 = (gkOdd xs).xs ++ xs.drop 8) ∧
      (∀ j < depth / 2, (gkD cap0 xs (depth % 2) j).Ok (gkSl cap0 xs (depth % 2) j).1
          (gkSl cap0 xs (depth % 2) j).2.1 2 ∧
        xs.drop (gkSl cap0 xs (depth % 2) j).2.2 =
          (gkD cap0 xs (depth % 2) j).xs ++ xs.drop (gkSl cap0 xs (depth % 2) (j + 1)).2.2) ∧
      xs.drop (gkSl cap0 xs (depth % 2) (depth / 2)).2.2 = [] ∧
      sF = (gkSl cap0 xs (depth % 2) (depth / 2)).1 ∧
      r = (xs.getD 1 0, (gkSl cap0 xs (depth % 2) (depth / 2)).2.1.point,
        (gkSl cap0 xs (depth % 2) (depth / 2)).2.1.values) ∧
      (gkSl cap0 xs (depth % 2) (depth / 2)).2.1.point.length = depth := by
  obtain ⟨sp, hsp⟩ := hc
  have e := RunsTo.toT h hsp []
  rw [List.append_nil] at e
  unfold gkrPhase at e
  obtain ⟨r1, st1, h1, h2⟩ := runT_bind_some e
  obtain ⟨u, st2, h3, h4⟩ := runT_bind_some h2
  obtain ⟨hne, rfl⟩ := runT_require_some h3
  obtain ⟨rfl, rfl⟩ := runT_pure_some h4
  unfold verifyGkrGrandProducts at h1
  obtain ⟨x0, st3, h5, h6⟩ := runT_bind_some h1
  obtain ⟨zs1, rfl, rfl⟩ := runT_readE_some h5
  obtain ⟨x1, st4, h7, h8⟩ := runT_bind_some h6
  obtain ⟨zs2, rfl, rfl⟩ := runT_readE_some h7
  obtain ⟨stF, st5, h9, h10⟩ := runT_bind_some h8
  obtain ⟨rfl, rfl⟩ := runT_pure_some h10
  rw [tb_absorb_two] at h9
  have hx1 : (x0 :: x1 :: zs2).getD 1 0 = x1 := rfl
  rcases Nat.mod_two_eq_zero_or_one depth with hsh | hsh
  · rw [show depth = 2 * (depth / 2) by omega, gkrLayers_even] at h9
    have h0 : gkSl cap0 (x0 :: x1 :: zs2) (depth % 2) 0 =
        (gkRootS cap0 (x0 :: x1 :: zs2), gkRootSt (x0 :: x1 :: zs2), 2) := by
      simp [gkSl, gkSl0, hsh]
    obtain ⟨hall, rfl, rfl, hrest, hpl⟩ := gkrPairs_invT cap0 (x0 :: x1 :: zs2) (depth % 2)
      (by rw [h0, hsh]; rfl) (depth / 2) stF sF [] (by rw [h0]; exact h9)
    refine ⟨by rw [hx1]; exact hne, by simp, fun h => by omega, hall, hrest.symm, rfl, rfl,
      by rw [hpl]; omega⟩
  · rw [show depth = 2 * (depth / 2) + 1 by omega, gkrLayers_odd] at h9
    obtain ⟨st1, ⟨s1, rest1, os1, R1⟩, h11, h12⟩ := runT_bind_some h9
    have hos : os1 = [] := by
      obtain ⟨-, opre, -, ho, -⟩ := runT_frame _ _ _ _ h11
      exact (List.append_eq_nil_iff.mp ho.symm).2
    have hR : R1 = [] := by
      obtain ⟨C, hC⟩ := runT_roots _ _ _ _ h12
      exact (List.append_eq_nil_iff.mp hC.symm).1
    subst hos hR
    obtain ⟨D, hok, hd, rfl, rfl⟩ := gkrStep_invT h11 (Or.inr rfl)
    have hok' := hok
    obtain ⟨hl, h4, h0', h1', h2', -⟩ := hok'
    obtain ⟨rfl, rfl⟩ := gkStepAt_eq (zs := x0 :: x1 :: zs2) (o := 2) (L := 0) hd
      (by simpa [gkRootSt] using hl) h4 h0' h1' h2'
    have h0 : gkSl cap0 (x0 :: x1 :: zs2) (depth % 2) 0 =
        ((gkOdd (x0 :: x1 :: zs2)).s' (gkRootS cap0 (x0 :: x1 :: zs2))
            (gkRootSt (x0 :: x1 :: zs2)) 1,
          (gkOdd (x0 :: x1 :: zs2)).st' (gkRootS cap0 (x0 :: x1 :: zs2))
            (gkRootSt (x0 :: x1 :: zs2)) 1, 8) := by
      simp [gkSl, gkSl0, hsh]
    obtain ⟨hall, rfl, rfl, hrest, hpl⟩ := gkrPairs_invT cap0 (x0 :: x1 :: zs2) (depth % 2)
      (by rw [h0, hsh]; rfl) (depth / 2) stF sF [] (by rw [h0]; exact h12)
    refine ⟨by rw [hx1]; exact hne, by simp, fun _ => ⟨hok, hd⟩, hall, hrest.symm, rfl, rfl,
      by rw [hpl]; omega⟩

end
end LeanVM.Guest.B1.Tables
