/-
  LeanVM.Guest.B1.Gkr.EvalC

  What forward evaluation's equations give, statement by statement, for the honest valuations of
  `verify_bus_gkr` and its layer loop: loads reading the memory, products, permutations, and the
  inline Fiat-Shamir templates holding.
-/

module

public import LeanVM.Guest.B1.Fwd.FlatIte
public import LeanVM.Guest.B1.Fwd.NotStored
public import LeanVM.Guest.B1.Gkr.Fs

/-!
# Evaluated statements

On a valuation satisfying `Fwd.Good` for every statement of a body's evaluation list:

* `good_read`: a load that is not one of the body's stores (`loadKey`, checked by kernel
  evaluation) reads the memory's word;
* `good_mul`: a product of older values;
* `keccak_good`: a `KECCAK` of canonical cells holds, its outputs the permutation's;
* `fsNextT_good`, `challengeT_good`: `fs_next` reading a word holds, its cells the word's;
  `challenge_from_state` of a canonical cell is the template's `ChallengeOk`;
* `holdsList_auto`: a block of pure atoms and hints holds;
* `good_slice`, `good_ite`: a slice of a body, or an `ite`'s branches, are in its evaluation list.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1 LeanVM.Guest.B1.Fwd

@[expose] public section

/-! ## Statements in the evaluation list -/

/-- Not an `ite`. -/
def notIteB : Stmt → Bool
  | .ite .. => false
  | _ => true

/-- **A slice of a body** is in its evaluation list, when it has no `ite`. -/
theorem good_slice {pre : List Stmt} {G : Stmt → Prop} (hG : ∀ s ∈ flatIte pre, G s) (n : ℕ)
    (blk : List Stmt) (heq : tbStmtsEqb blk ((pre.drop n).take blk.length) = true)
    (hni : blk.all notIteB = true) : ∀ s ∈ blk, G s := by
  intro s hs
  have e := tbStmtsEqb_sound heq
  have hp : s ∈ pre := by
    rw [e] at hs
    exact List.mem_of_mem_drop (List.mem_of_mem_take hs)
  refine hG s (mem_flatIte_of (fun c z n' h => ?_) hp)
  subst h
  have := List.all_eq_true.mp hni _ hs
  simp [notIteB] at this

/-- **An `ite`'s branches** are in the evaluation list. -/
theorem good_ite {pre : List Stmt} {G : Stmt → Prop} (hG : ∀ s ∈ flatIte pre, G s) (n : ℕ)
    (c : V) (z n' : List Stmt) (heq : tbStmtsEqb [.ite c z n'] ((pre.drop n).take 1) = true) :
    ∀ t ∈ z ++ n', G t := by
  have e := tbStmtsEqb_sound heq
  have hp : Stmt.ite c z n' ∈ pre := by
    have : Stmt.ite c z n' ∈ (pre.drop n).take 1 := by rw [← e]; simp
    exact List.mem_of_mem_drop (List.mem_of_mem_take this)
  exact fun t ht => hG t (mem_flatIte_ite hp t ht)

/-! ## Loads that read -/

/-- A load's key: its destination's and pointer's indices and its offset. -/
def loadKey : Atom → Option (ℕ × ℕ × ℕ)
  | .load d p off => some (d.idx, p.idx, off)
  | _ => none

theorem not_mem_of_loadKey {S : List Atom} {d p off : ℕ} (h : some (d, p, off) ∉ S.map loadKey) :
    Atom.load (.n d) (.n p) off ∉ S := fun hm => h (List.mem_map.mpr ⟨_, hm, rfl⟩)

theorem rdAt_of_loadHolds {rd : Reader} {p w : E} {off : ℕ} (h : LoadHolds rd p off w) :
    rdAt rd p off = w := by
  rw [rdAt, h.2]; rfl

variable {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val}

/-- **A load reading the memory**: its word is the memory's, and it holds. -/
theorem good_read {d p off : ℕ} (hg : Good rd S w σ (.load (.n d) (.n p) off))
    (hS : some (d, p, off) ∉ S.map loadKey) {v : E} (hl : LoadHolds rd (σ (.n p)) off v) :
    σ (.n d) = v ∧ LoadHolds rd (σ (.n p)) off (σ (.n d)) := by
  have e : σ (.n d) = rdAt rd (σ (.n p)) off := hg.resolve_left (not_mem_of_loadKey hS)
  rw [e, rdAt_of_loadHolds hl]
  exact ⟨rfl, hl⟩

/-- A product of older values. -/
theorem good_mul {d x y : ℕ} (hg : Good rd S w σ (.mul (.n d) (.n x) (.n y))) (hx : x < d)
    (hy : y < d) : σ (.n d) = σ (.n x) * σ (.n y) := by
  have h : (V.n x).idx < (V.n d).idx ∧ (V.n y).idx < (V.n d).idx := ⟨hx, hy⟩
  change ite _ _ _ at hg
  split at hg
  · exact hg
  · exact absurd h ‹_›

theorem good_mulS {d x y : ℕ} (hg : GoodS rd S w σ (.atom (.mul (.n d) (.n x) (.n y))))
    (hx : x < d) (hy : y < d) : σ (.n d) = σ (.n x) * σ (.n y) :=
  good_mul (rd := rd) (S := S) (w := w) hg hx hy

theorem good_readS {d p off : ℕ} (hg : GoodS rd S w σ (.atom (.load (.n d) (.n p) off)))
    (hS : some (d, p, off) ∉ S.map loadKey) {v : E} (hl : LoadHolds rd (σ (.n p)) off v) :
    σ (.n d) = v ∧ LoadHolds rd (σ (.n p)) off (σ (.n d)) :=
  good_read (rd := rd) (S := S) (w := w) hg hS hl

/-- **A permutation of canonical cells** holds, its outputs the permutation's. -/
theorem keccak_good {ins outs : List V} (hg : Good rd S w σ (.keccak ins outs false false))
    (hc : AllCanonical (ins.map σ)) (ho : outs.length = 13 := by first | rfl | simp) :
    (Atom.keccak ins outs false false).Holds rd σ ∧
      cells13 (outs.map σ) = cellsOfState (permOf (ins.map σ)) false := by
  obtain ⟨hi, -, he⟩ := hg
  have hout : cells13 (outs.map σ) = cellsOfState (permOf (ins.map σ)) false := funext fun c => by
    rw [cells13, List.getD_eq_getElem _ _ (by simp [ho]), List.getElem_map]
    exact he c (by omega)
  exact ⟨keccakA_of hi ho hc hout, hout⟩

/-! ## Blocks of pure atoms -/

/-- A pure atom or a hint. -/
def autoBG : Stmt → Bool
  | .atom (.hint _) => true
  | .atom a => pureB a
  | _ => false

/-! ## The Fiat-Shamir templates -/

/-- **`fs_next` on its equations**: the word read, its two cells, and the template holding. -/
theorem fsNextT_good {C : CallRel} {kret : List E → Prop} {cur off b : ℕ}
    (hg : ∀ s ∈ fsNextT (.n cur) off b, GoodS rd S w σ s)
    (hS : some (b, cur, off) ∉ S.map loadKey) {v : E} (hl : LoadHolds rd (σ (.n cur)) off v) :
    σ (.n b) = v ∧ (σ (.n (b + 7)), σ (.n (b + 9))) = Keccak.scalarCells v dsObserve ∧
      Stmt.HoldsList C rd σ (fsNextT (.n cur) off b) True kret := by
  obtain ⟨e0, hl0⟩ := good_read (rd := rd) (S := S) (w := w)
    (hg (.atom (.load (.n b) (.n cur) off)) (by simp [fsNextT])) hS hl
  have gl : ∀ j (h : j < 3), σ ([V.n (b + 1), .n (b + 1 + 1), .n (b + 1 + 2)][j]) =
      limbAt (σ (.n b)) j := hg (.atom (.hint (.limbs (.n b) [.n (b + 1), .n (b + 1 + 1),
        .n (b + 1 + 2)]))) (by simp [fsNextT, fsPackT])
  have c3 : σ (.n (b + 1 + 3)) = word dsObserve 0 0 := hg (.atom (.const (.n (b + 1 + 3))
    (word dsObserve 0 0))) (by simp [fsNextT, fsPackT])
  have c4 : σ (.n (b + 1 + 4)) = word 0 0 1 := hg (.atom (.const (.n (b + 1 + 4))
    (word 0 0 1))) (by simp [fsNextT, fsPackT])
  have m5 : σ (.n (b + 1 + 5)) = σ (.n (b + 1 + 4)) * σ (.n (b + 1 + 2)) :=
    good_mul (rd := rd) (S := S) (w := w) (hg (.atom (.mul (.n (b + 1 + 5)) (.n (b + 1 + 4)) (.n (b + 1 + 2))))
      (by simp [fsNextT, fsPackT])) (by omega) (by omega)
  have a6 : σ (.n (b + 1 + 6)) = σ (.n b) + σ (.n (b + 1 + 5)) := hg (.atom (.add
    (.n (b + 1 + 6)) (.n b) (.n (b + 1 + 5)))) (by simp [fsNextT, fsPackT])
  have c7 : σ (.n (b + 1 + 7)) = word 0 dsObserve 0 := hg (.atom (.const (.n (b + 1 + 7))
    (word 0 dsObserve 0))) (by simp [fsNextT, fsPackT])
  have a8 : σ (.n (b + 1 + 8)) = σ (.n (b + 1 + 2)) + σ (.n (b + 1 + 7)) := hg (.atom (.add
    (.n (b + 1 + 8)) (.n (b + 1 + 2)) (.n (b + 1 + 7)))) (by simp [fsNextT, fsPackT])
  have l0 : σ (.n (b + 1)) = ofK ((σ (.n b)).limb 0) := (gl 0 (by omega)).trans (by simp [limbAt])
  have l1 : σ (.n (b + 1 + 1)) = ofK ((σ (.n b)).limb 1) := (gl 1 (by omega)).trans (by simp [limbAt])
  have l2 : σ (.n (b + 1 + 2)) = ofK ((σ (.n b)).limb 2) := (gl 2 (by omega)).trans (by simp [limbAt])
  have hv : ∀ i < 9, σ (.n (b + 1 + i)) = fsPackVals (σ (.n b)) dsObserve i := by
    intro i hi
    interval_cases i
    · exact l0
    · exact l1
    · exact l2
    · exact c3
    · exact c4
    · rw [m5, c4, l2]; rfl
    · rw [a6, m5, c4, l2]; rfl
    · exact c7
    · rw [a8, l2, c7]; rfl
  have hok := fsPackOk_of_vals hv
  have hcells := fsPackVals_cells (σ (.n b)) dsObserve
  rw [← hv 6 (by omega), ← hv 8 (by omega), e0] at hcells
  refine ⟨e0, hcells, (holds_fsNextT _ _ _ _ _).mpr ⟨⟨hl0, hok⟩, trivial⟩⟩

/-- **`challenge_from_state` on its equations**, from a canonical cell. -/
theorem challengeT_good {s0 s1 b : ℕ} (hg : ∀ s ∈ challengeT (.n s0) (.n s1) b, GoodS rd S w σ s)
    (hc : IsCanonical128 (σ (.n s1))) : ChallengeOk σ (.n s0) (.n s1) b := by
  have gl : ∀ j (h : j < 1), σ ([V.n b][j]) = limbAt (σ (.n s1)) j :=
    hg (.atom (.hint (.limbs (.n s1) [.n b]))) (by simp [challengeT])
  have a1 : σ (.n (b + 1)) = σ (.n s1) + σ (.n b) :=
    hg (.atom (.add (.n (b + 1)) (.n s1) (.n b))) (by simp [challengeT])
  have c2 : σ (.n (b + 2)) = word 1 0 1 :=
    hg (.atom (.const (.n (b + 2)) (word 1 0 1))) (by simp [challengeT])
  have m3 : σ (.n (b + 3)) = σ (.n (b + 1)) * σ (.n (b + 2)) :=
    good_mul (rd := rd) (S := S) (w := w) (hg (.atom (.mul (.n (b + 3)) (.n (b + 1)) (.n (b + 2)))) (by simp [challengeT]))
      (by omega) (by omega)
  have c4 : σ (.n (b + 4)) = word 0 0 1 :=
    hg (.atom (.const (.n (b + 4)) (word 0 0 1))) (by simp [challengeT])
  have m5 : σ (.n (b + 5)) = σ (.n (b + 4)) * σ (.n b) :=
    good_mul (rd := rd) (S := S) (w := w) (hg (.atom (.mul (.n (b + 5)) (.n (b + 4)) (.n b))) (by simp [challengeT]))
      (by omega) (by omega)
  have a6 : σ (.n (b + 6)) = σ (.n s0) + σ (.n (b + 5)) :=
    hg (.atom (.add (.n (b + 6)) (.n s0) (.n (b + 5)))) (by simp [challengeT])
  have l0 : σ (.n b) = ofK ((σ (.n s1)).limb 0) := (gl 0 (by omega)).trans (by simp [limbAt])
  refine challengeOk_of_vals hc fun i hi => ?_
  interval_cases i
  · exact l0
  · rw [a1, l0]; rfl
  · exact c2
  · rw [m3, a1, c2, l0]; rfl
  · exact c4
  · rw [m5, c4, l0]; rfl
  · rw [a6, m5, c4, l0]; rfl

end
end LeanVM.Guest.B1.Tables
