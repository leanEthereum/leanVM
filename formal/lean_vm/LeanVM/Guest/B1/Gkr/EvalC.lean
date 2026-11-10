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
* `keccak_good`: a `KECCAK` holds, its outputs the permutation's;
* `fsNextT_good`, `challengeT_good`: `fs_next` reading a word holds, its cells the word's;
  `challenge_from_state` is the template's `ChallengeOk`;
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

/-- **A permutation** holds, its outputs the permutation's. -/
theorem keccak_good {ins outs : List V} (hg : Good rd S w σ (.keccak ins outs false false))
    (ho : outs.length = 13 := by first | rfl | simp) :
    (Atom.keccak ins outs false false).Holds rd σ ∧
      cells13 (outs.map σ) = cellsOfState (permOf (ins.map σ)) false := by
  obtain ⟨hi, -, he⟩ := hg
  have hout : cells13 (outs.map σ) = cellsOfState (permOf (ins.map σ)) false := funext fun c => by
    rw [cells13, List.getD_eq_getElem _ _ (by simp [ho]), List.getElem_map]
    exact he c (by omega)
  exact ⟨keccakA_of hi ho hout, hout⟩

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
    σ (.n b) = v ∧ (σ (.n (b + 1)), σ (.n (b + 2))) = Keccak.scalarCells v dsObserve ∧
      Stmt.HoldsList C rd σ (fsNextT (.n cur) off b) True kret := by
  obtain ⟨e0, hl0⟩ := good_read (rd := rd) (S := S) (w := w)
    (hg (.atom (.load (.n b) (.n cur) off)) (by simp [fsNextT])) hS hl
  have c1 : σ (.n (b + 1)) = σ (.n b) := hg (.atom (.copy (.n (b + 1)) (.n b)))
    (by simp [fsNextT, fsPackT])
  have c2 : σ (.n (b + 1 + 1)) = word 0 dsObserve := hg (.atom (.const (.n (b + 1 + 1))
    (word 0 dsObserve))) (by simp [fsNextT, fsPackT])
  have hok : FsPackOk σ (.n b) (b + 1) dsObserve := ⟨c1, c2⟩
  refine ⟨e0, ?_, (holds_fsNextT _ _ _ _ _).mpr ⟨⟨hl0, hok⟩, trivial⟩⟩
  rw [← e0]
  exact fsPackT_cells hok

/-- **`challenge_from_state` on its equations.** -/
theorem challengeT_good {s0 b : ℕ} (hg : ∀ s ∈ challengeT (.n s0) b, GoodS rd S w σ s) :
    ChallengeOk σ (.n s0) b :=
  hg (.atom (.copy (.n b) (.n s0))) (by simp [challengeT])

end
end LeanVM.Guest.B1.Tables
