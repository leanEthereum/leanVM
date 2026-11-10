/-
  LeanVM.Guest.B1.VerifySub.C.ValsB

  `verify_sub`'s honest valuation, its back: the ring map's challenges, `c_table`, `λ` and the
  target, the tail's candidate and arguments.
-/

module

public import LeanVM.Guest.B1.VerifySub.C.Vals
public import LeanVM.Guest.B1.VerifySub.Ctab
public import LeanVM.Guest.B1.VerifySub.Lam

/-!
# The back, honestly

* `vs_maps`: the ring map's nonce `n` read at `verify_keccak`'s cursor and absorbed into its
  capacity `cap` (`vsMapSt`), the grind's cell, and the sixteen challenges `vsRchs cap n` (the
  grind's challenge, fifteen squeezed), the capacity after them;
* `vs_ctabV`: `c_table`'s products `f_p · g_b^(2^(8p))` of the challenges;
* `vs_lam`: `λ` squeezed after the challenges, and the target over the pooled claims;
* `vs_tailV`: the candidate `g^(m - 22 + 7 (rate - 1))`, the stream's next pointer and `tabs`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Tables
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The ring map grind's permutation: the nonce `n` absorbed into the capacity `cap`. -/
def vsMapSt (cap : List E) (n : E) : KeccakState := (⟨cap, []⟩ : Fs).nonceState n

/-- The ring map's sixteen challenges: the grind's challenge, then fifteen squeezed. -/
def vsRchs (cap : List E) (n : E) : List E :=
  challengeOf (vsMapSt cap n) :: ((⟨capOf (vsMapSt cap n), []⟩ : Fs).squeezeN 15).1

/-- `verify_keccak`'s returned capacity. -/
def vsKCap (w : ℕ → E) : List E := [w 590, w 591, w 592, w 593, w 594]

variable {rd : Reader} {w : ℕ → E} {args : List E}

local notation "ς" => vsσ rd w args

/-! ## The ring map's challenges -/

theorem vsMapSqz_noSide (i : ℕ) : (vsMapSqz i).all noSideB = true := by
  simp [vsMapSqz, vsSqzT, keccakA, challengeT, vsCopy, noSideB, needsSide]

theorem flatMap_noSide {f : ℕ → List Stmt} (hf : ∀ i, (f i).all noSideB = true) :
    ∀ l : List ℕ, (l.flatMap f).all noSideB = true
  | [] => rfl
  | i :: l => by rw [List.flatMap_cons, List.all_append, hf i, flatMap_noSide hf l]; rfl

theorem vsMapsT_split : vsMapsT =
    (List.range 5).map (fun i ↦ vsCopy (597 + i) (590 + i)) ++ fsNonceT (.n 595) 0 602 ++
    [keccakA [.n 603, .n 604, .n 8, .n 8, .n 8, .n 9, .n 10, .n 11, .n 597, .n 598, .n 599,
      .n 600, .n 601] (vsRun 605 13)] ++ vsTabsT 618 619 ++
    [grindCallT 14 (.n 606) (.n 619), vsCopy 620 605, vsCopy 621 620] ++
    (List.range' 0 15).flatMap vsMapSqz ++
    (vsAlloc 847 16 :: (List.range 16).map (fun i ↦ vsLd (vsCh i) 847 i)) := by
  rw [vsMapsT, ← List.range_eq_range']
  rfl

/-- **The ring map's challenges** (G:3686-3703): the nonce `n` at `verify_keccak`'s cursor,
the grind's permutation `vsMapSt`, its cell `1` for `grind_check`, `tabs`, the sixteen
challenges `vsRchs` at `vsCh i`, and the capacity after them at `840 .. 844`. -/
theorem vs_maps (hl : args.length = 6) {n : E} (hn : LoadHolds rd (w 595) 0 n) :
    ς (.n 602) = n ∧ ς (.n 606) = cellsOfState (vsMapSt (vsKCap w) n) false 1 ∧
      ς (.n 619) = ς (.n 4) * gen ^ winTabAt ∧
      (∀ i < 16, ς (.n (vsCh i)) = (vsRchs (vsKCap w) n).getD i 0) ∧
      ((⟨capOf (vsMapSt (vsKCap w) n), []⟩ : Fs).squeezeN 15).2 =
        ⟨[ς (.n 840), ς (.n 841), ς (.n 842), ς (.n 843), ς (.n 844)], []⟩ := by
  have hG := vsMapsT_good (rd := rd) (w := w) hl
  rw [vsMapsT_split] at hG
  have hz := vs_zero (rd := rd) (w := w) hl
  have mA : ∀ s ∈ (List.range 5).map (fun i ↦ vsCopy (597 + i) (590 + i)),
      GoodS rd vsSL w ς s := fun s hs ↦ hG s (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_left _ hs))))))
  have mN : ∀ s ∈ fsNonceT (.n 595) 0 602, GoodS rd vsSL w ς s :=
    fun s hs ↦ hG s (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hs))))))
  have mT : ∀ s ∈ vsTabsT 618 619, GoodS rd vsSL w ς s :=
    fun s hs ↦ hG s (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ hs))))
  have mQ : ∀ s ∈ (List.range' 0 15).flatMap vsMapSqz, GoodS rd vsSL w ς s :=
    fun s hs ↦ hG s (List.mem_append_left _ (List.mem_append_right _ hs))
  have hk : (Atom.keccak [.n 603, .n 604, .n 8, .n 8, .n 8, .n 9, .n 10, .n 11, .n 597, .n 598,
      .n 599, .n 600, .n 601] (vsRun 605 13) false false).Holds rd ς :=
    good_atom (hG _ (by simp [keccakA])) rfl
  have c620 : ς (.n 620) = ς (.n 605) := good_copy (hG _ (by simp [vsCopy]))
  have c621 : ς (.n 621) = ς (.n 620) := good_copy (hG _ (by simp [vsCopy]))
  have cA : ∀ i < 5, ς (.n (597 + i)) = w (590 + i) := fun i hi ↦ by
    rw [good_copy (mA _ (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩)),
      vs_w hl (by interval_cases i <;> decide)]
  have c0 := cA 0 (by omega)
  have c1 := cA 1 (by omega)
  have c2 := cA 2 (by omega)
  have c3 := cA 3 (by omega)
  have c4 := cA 4 (by omega)
  simp only [Nat.reduceAdd] at c0 c1 c2 c3 c4
  have e602 : ς (.n 602) = n :=
    good_read (mN _ List.mem_cons_self) (by decide +kernel) (by rw [vs_w hl (by decide)]; exact hn)
  have pk : FsPackOk ς (.n 602) 603 dsPowNonce := good_fsPack fun s hs ↦ mN s (List.mem_cons_of_mem _ hs)
  have h619 := tabs_good (c := 618) (by decide) mT
  have hsqH := holdsList_good (C := fun _ _ _ ↦ True) (kret := fun _ ↦ True)
    (flatMap_noSide vsMapSqz_noSide _) mQ (next := True) trivial
  obtain ⟨hsq, -⟩ := maps_chain hz.1 hz.2.1 hz.2.2.1 hz.2.2.2 15 0 hsqH
  -- the nonce's permutation
  set S := vsMapSt (vsKCap w) n with hS
  have hcells : cells13 ((vsRun 605 13).map ς) = cellsOfState S false := by
    rw [hS, vsMapSt, Fs.nonceState,
      show (⟨vsKCap w, []⟩ : Fs).absorb n dsPowNonce = ⟨vsKCap w, [(n, dsPowNonce)]⟩ by
        simp [Fs.absorb, rateScalars]]
    refine keccakA_fs hk (by simp) ?_
    have hp := fsPackT_cells pk
    rw [e602] at hp
    simp only [List.map_cons, List.map_nil, hz.1, hz.2.1, hz.2.2.1, hz.2.2.2, c0, c1, c2, c3, c4,
      vsKCap]
    simp only [pendCells, List.flatMap_cons, List.flatMap_nil, List.append_nil, ← hp,
      List.length_cons, List.length_nil]
    rfl
  have hc : ∀ c : Fin 13, ς (.n (605 + c.val)) = cellsOfState S false c := fun c ↦ by
    have := congrFun hcells c
    simpa [cells13, vsRun, c.isLt] using this
  have hcap0 : capOf S = (vsRun (vsChCap 0) 5).map ς := by
    simp only [capOf, vsChCap, ↓reduceIte, vsRun5_map]
    rw [← hc 8, ← hc 9, ← hc 10, ← hc 11, ← hc 12]
    rfl
  have hch0 : challengeOf S = ς (.n (vsCh 0)) := by
    rw [Keccak.challengeOf_cells, ← hc 0]
    simp only [vsCh]
    rw [c621, c620]
    rfl
  refine ⟨e602, hc 1, h619, fun i hi ↦ ?_, ?_⟩
  · rw [vsRchs, ← hS, hcap0, hsq, hch0]
    rcases i with _ | i
    · simp only [List.getD_cons_zero]
    · rw [List.getD_cons_succ, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map,
        List.getElem_range']
      simp
  · rw [hcap0, hsq, show vsChCap (0 + 15) = 840 from rfl, vsRun5_map]

/-! ## `c_table` -/

theorem vsSqT_noSide : ∀ b < 8, ∀ q < 7, (vsSqT b (849 + 64 * b) q).all noSideB = true := by
  decide +kernel

end
end LeanVM.Guest.B1.VerifySub
