/-
  LeanVM.Guest.Count.VsBoundBase

  `open_stacked`'s bound per candidate with its name spelled by `natStr` (`osC`), so that the
  kernel evaluates it (`openNames` spells the names by `toString`, whose body the kernel cannot
  see), and by the search tree's lookups (`osCF`); its named callees' words `osBnd` by core index
  (`osBndFast`); `osC c = osCF c` (`osC_eq_fast`).
-/

module

public import LeanVM.Guest.Count.VsWords
public import LeanVM.Guest.Count.VsOsDefs
public import LeanVM.Guest.B1.Whir.Names
public import LeanVM.Guest.B1.Place.OsSpec

namespace LeanVM.Guest.Count

open LeanVM.Guest.Core LeanVM.Guest.B1.Whir

@[expose] public section

/-- **`open_stacked`'s named callees' words**: `wSB` on the names `osKindOf` knows, `0` on the
others (the queries' callees and the loops, which `osBk` bounds by `osSpB`). -/
noncomputable def osBnd (f : String) : ℕ := if (B1.osKindOf f).isSome then wSB f else 0

set_option maxRecDepth 100000 in
theorem osKindIdx_eq : osKindIdx = B1.osKindTable.filterMap fun p => wNameIdx p.1 := by
  decide +kernel

theorem lookup_isSome_of_mem {a : String} {b : B1.OsKind} :
    ∀ {l : List (String × B1.OsKind)}, (a, b) ∈ l → (l.lookup a).isSome
  | [], h => absurd h List.not_mem_nil
  | (x, y) :: l, h => by
    simp only [List.lookup]
    split
    · rfl
    · rename_i hne
      rcases List.mem_cons.mp h with h | h
      · cases h; simp at hne
      · exact lookup_isSome_of_mem h

set_option maxRecDepth 100000 in
/-- Every name of `osKindTable` is in the tree. -/
theorem osKind_named : B1.osKindTable.all (fun p => (wNameIdx p.1).isSome) = true := by
  decide +kernel

theorem osBndFast_eq : osBndFast = osBnd := by
  funext f
  unfold osBndFast
  rcases h : wNameIdx f with _ | j
  · dsimp only
    unfold osBnd
    rcases hk : B1.osKindOf f with _ | K
    · rfl
    · have := List.all_eq_true.mp osKind_named _ (B1.os_mem_of_lookup _ hk)
      simp [h] at this
  · dsimp only
    have hs := wNameIdx_spec h
    have key : j ∈ osKindIdx ↔ (B1.osKindOf f).isSome = true := by
      rw [osKindIdx_eq, List.mem_filterMap]
      constructor
      · rintro ⟨⟨n, K⟩, hp, hpj⟩
        have hn := wNameIdx_spec hpj
        rw [hs, Option.some.injEq] at hn
        subst hn
        exact lookup_isSome_of_mem hp
      · intro hk
        obtain ⟨K, hK⟩ := Option.isSome_iff_exists.mp hk
        exact ⟨(f, K), B1.os_mem_of_lookup _ hK, h⟩
    unfold osBnd
    rw [wSB_idx hs]
    simp only [key]

/-- `open_stacked`'s words at candidate `c`, its name spelled by `natStr`. -/
noncomputable def osC (c : ℕ) : ℕ :=
  B1.osBos B2C.fs (B1.osBk B2C.fs osBnd (fun f => wSK f - B2C.fs f) (osCfg c)) ("open_stacked__L" ++ natStr c) (osCfg c)

theorem osC_eq_fast (c : ℕ) : osC c = osCF c := by
  unfold osC osCF
  rw [fsFast_eq, osBndFast_eq, wSKFast_eq]

/-- `osBosAt` at a candidate is `osC`. -/
theorem osBosAt_eq {μ r : ℕ} (h : candidate μ r < 28) :
    B1.osBosAt B2C.fs osBnd (fun f => wSK f - B2C.fs f) μ r = osC (candidate μ r) := by
  unfold B1.osBosAt osC openName openNames
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h, Option.map_some,
    Option.getD_some, natStr_eq]

end
end LeanVM.Guest.Count
