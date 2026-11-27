module

public import LeanVM.Guest.Local.Layout

/-!
# A jump is a hop of the layout

`Layout.visits` reads a run of the machine as a list of hops (`Layout.Hop`): forward, every offset
skipped in a block whose range holds neither end. A jump of the compiled code skips whole arms,
blocks whose ranges tile the offsets between its ends; `hopOk L u v cs` checks that the blocks `cs`
tile `(u, v)` (each starting where the last ended, the first at `u + 1`, the last ending at `v`),
and `hopOk_hop` gives the hop: an offset skipped is in one of the tiles, so its run's block's range
is inside that tile's (`run_sub`), which holds neither `u` nor `v`. A fall-through, `v = u + 1`,
takes no tile.
-/

namespace LeanVM.Guest.Local

namespace Layout

@[expose] public section

/-- The blocks `cs` tile the offsets `[y, v)`, in order. -/
noncomputable def tiles (L : Layout) (v : ℕ) : ℕ → List ℕ → Bool
  | y, [] => Nat.beq y v
  | y, c :: cs => Nat.blt c L.nb && Nat.beq (L.blk c).cs y && Nat.blt y (L.blk c).ce &&
      tiles L v (L.blk c).ce cs

/-- **A jump from `u` to `v` skipping the blocks `cs`.** -/
noncomputable def hopOk (L : Layout) (u v : ℕ) (cs : List ℕ) : Bool := Nat.blt u v && tiles L v (u + 1) cs

end

public section

variable {L : Layout}

/-- An offset of `[y, v)` is in a tile's range, the tile inside `[y, v)`. -/
theorem tiles_cover {v : ℕ} : ∀ {y : ℕ} {cs : List ℕ}, tiles L v y cs = true → ∀ x, y ≤ x → x < v →
    ∃ c, c < L.nb ∧ L.InRange c x ∧ y ≤ (L.blk c).cs ∧ (L.blk c).ce ≤ v
  | y, [], h, x, h1, h2 => by
    simp only [tiles, Nat.beq_eq] at h; omega
  | y, c :: cs, h, x, h1, h2 => by
    simp only [tiles, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
    obtain ⟨⟨⟨hc, hcs⟩, hlt⟩, hr⟩ := h
    have hle : (L.blk c).ce ≤ v := by
      have := tiles_le hr; omega
    by_cases hx : x < (L.blk c).ce
    · exact ⟨c, hc, ⟨by omega, hx⟩, by omega, hle⟩
    · obtain ⟨c', h1', h2', h3', h4'⟩ := tiles_cover hr x (by omega) h2
      exact ⟨c', h1', h2', by omega, h4'⟩
where
  tiles_le : ∀ {y : ℕ} {cs : List ℕ}, tiles L v y cs = true → y ≤ v
    | y, [], h => by simp only [tiles, Nat.beq_eq] at h; omega
    | y, c :: cs, h => by
      simp only [tiles, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
      have := tiles_le h.2; omega

/-- **A jump the check accepts is a hop.** -/
theorem hopOk_hop (hL : L.ok = true) {u v : ℕ} {cs : List ℕ} (h : hopOk L u v cs = true) : Hop L u v := by
  simp only [hopOk, Bool.and_eq_true, Nat.blt_eq] at h
  unfold Hop
  refine ⟨h.1, fun y r h1 h2 hr ↦ ?_⟩
  obtain ⟨c, hc, hy, hcs, hce⟩ := tiles_cover h.2 y (by omega) h2
  obtain ⟨hs1, hs2⟩ := run_sub hL hr hy hc
  constructor
  · rintro ⟨hu1, -⟩; omega
  · rintro ⟨-, hv2⟩; omega

end

end Layout

end LeanVM.Guest.Local
