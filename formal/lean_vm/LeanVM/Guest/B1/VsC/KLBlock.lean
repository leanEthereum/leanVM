/-
  LeanVM.Guest.B1.VsC.KLBlock

  The sponge templates and blocks of atoms on an evaluated valuation, completely (the archive's
  `FsComplete`, `LayerCBlock`).
-/

module

public import LeanVM.Guest.B1.KeccakGkr.Lib
public import LeanVM.Guest.B1.Fwd.Canon

/-!
# Blocks, completely

Restored from tag `formal-bus-archive` (`KeccakGkr/FsComplete`, `KeccakGkr/LayerCBlock`), in
namespace `VerifySub.KL`:

* `fsNext_complete`: `fs_next`'s word read from memory (not a store), so the word is the memory's,
  its packed cells the scalar's rate cells, and the template holds; `challenge_complete`,
  `keccakA_complete`.
* `block_holds`: a block of atoms on an evaluated valuation holds, its `K` assertions on values
  known in `K` by their equations, the residual atoms (`resid`) given; `side_loadVia`: a load that
  is not a store, through a pointer whose words the memory holds, has its side condition.
-/

namespace LeanVM.Guest.B1.VerifySub.KL

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section


variable {C : CallRel} {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val}

theorem rdAt_load {p : E} {k : ℕ} {v : E} (h : LoadHolds rd p k v) : rdAt rd p k = v := by
  unfold rdAt; rw [h.2]; rfl

/-- **`fs_pack` on an evaluated valuation**: its honest values. -/
theorem fsPack_vals_of_good {x : V} {b t : ℕ} (hg : ∀ s ∈ fsPackT x b t, GoodS rd S w σ s) :
    FsPackOk σ x b t := by
  simp only [fsPackT, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true, GoodS, Good] at hg
  exact hg

/-- **`fs_next` on an evaluated valuation**: the word read from memory, its packed cells the
scalar's rate cells, and the template holds. -/
theorem fsNext_complete {cur : V} {off b : ℕ} (hg : ∀ s ∈ fsNextT cur off b, GoodS rd S w σ s)
    (hnS : Atom.load (.n b) cur off ∉ S) {v : E} (hv : LoadHolds rd (σ cur) off v) :
    σ (.n b) = v ∧ (σ (.n (b + 1)), σ (.n (b + 2))) = Keccak.scalarCells v dsObserve ∧
      ∀ {next : Prop} {kret : List E → Prop},
        next → Stmt.HoldsList C rd σ (fsNextT cur off b) next kret := by
  have hl : GoodS rd S w σ (.atom (.load (.n b) cur off)) := hg _ (List.mem_cons_self ..)
  have hp : ∀ s ∈ fsPackT (.n b) (b + 1) dsObserve, GoodS rd S w σ s :=
    fun s hs ↦ hg s (List.mem_cons_of_mem _ hs)
  simp only [GoodS, Good] at hl
  have eb : σ (.n b) = v := by
    rcases hl with h | h
    · exact absurd h hnS
    · rw [h, rdAt_load hv]
  have hok := fsPack_vals_of_good hp
  refine ⟨eb, ?_, fun {next kret} hn ↦ ?_⟩
  · rw [← eb]; exact fsPackT_cells hok
  · exact (holds_fsNextT cur off b next kret).2 ⟨⟨by rw [eb]; exact hv, hok⟩, hn⟩

/-- **`challenge_from_state` on an evaluated valuation.** -/
theorem challenge_complete {s0 : V} {b : ℕ}
    (hg : ∀ s ∈ challengeT s0 b, GoodS rd S w σ s) :
    ChallengeOk σ s0 b ∧ ∀ {next : Prop} {kret : List E → Prop},
      next → Stmt.HoldsList C rd σ (challengeT s0 b) next kret := by
  simp only [challengeT, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true, GoodS, Good] at hg
  exact ⟨hg, fun {next kret} hn ↦ (holds_challengeT s0 b next kret).2 ⟨hg, hn⟩⟩

/-- **A `KECCAK` atom on an evaluated valuation** holds. -/
theorem keccakA_complete {ins outs : List V} (hg : Good rd S w σ (.keccak ins outs false false)) :
    (Atom.keccak ins outs false false).Holds rd σ :=
  holds_of_good hg trivial





/-- The atoms of a list of statements. -/
def atomsL (B : List Stmt) : List Atom := B.filterMap fun s ↦ match s with
  | .atom a => some a
  | _ => none

theorem mem_atomsL {B : List Stmt} {a : Atom} : a ∈ atomsL B ↔ Stmt.atom a ∈ B := by
  simp only [atomsL, List.mem_filterMap]
  constructor
  · rintro ⟨s, hs, h⟩
    cases s <;> simp_all
  · intro h
    exact ⟨_, h, rfl⟩

/-- The values known in `K` by their equations: hinted limbs, constants without `y` limbs. -/
def inKVals (as : List Atom) : List ℕ := as.flatMap fun a ↦ match a with
  | .hint (.limbs _ ds) => ds.map V.idx
  | .const d e => if e.limb 1 = 0 then [d.idx] else []
  | _ => []

/-- An `assertInK` of two values known in `K`. -/
def inkB (K : List ℕ) : Atom → Bool
  | .assertInK x y => K.contains x.idx && K.contains y.idx
  | _ => false

/-- The atoms whose relation the equations do not give. -/
def resid (as : List Atom) : List Atom :=
  as.filter fun a ↦ needsSide a && !inkB (inKVals as) a

theorem inK_of_inKVals (hσ : ∀ v, σ v = σ (.n v.idx)) {as : List Atom}
    (hg : ∀ a ∈ as, Good rd S w σ a) {i : ℕ} (hi : i ∈ inKVals as) : IsInK (σ (.n i)) := by
  simp only [inKVals, List.mem_flatMap] at hi
  obtain ⟨a, ha, hi⟩ := hi
  have hga := hg a ha
  cases a with
  | hint h =>
    cases h with
    | limbs v ds =>
      simp only [List.mem_map] at hi
      obtain ⟨u, hu, rfl⟩ := hi
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hu
      rw [← hσ, hga j hj, limbAt]
      split
      · exact (isInK_iff _).mpr ⟨_, rfl⟩
      · exact (isInK_iff _).mpr ⟨0, by rw [ofK_zero]⟩
    | _ => simp at hi
  | const d e =>
    simp only at hi
    split at hi
    · rename_i he
      simp only [List.mem_singleton] at hi
      subst hi
      rw [← hσ, hga]
      exact he
    · simp at hi
  | _ => simp at hi

/-- **A block of atoms on an evaluated valuation holds**, its residual atoms given. -/
theorem block_holds {B : List Stmt} (hall : B.all isAtom = true)
    (hσ : ∀ v, σ v = σ (.n v.idx)) (hg : ∀ s ∈ B, GoodS rd S w σ s)
    (hR : ∀ a ∈ resid (atomsL B), a.Holds rd σ ∨ Side rd S σ a) :
    ∀ {next : Prop} {kret : List E → Prop}, next → Stmt.HoldsList C rd σ B next kret := by
  intro next kret hn
  have hgB : ∀ a ∈ atomsL B, Good rd S w σ a := fun a ha ↦ hg _ (mem_atomsL.mp ha)
  have H : ∀ a ∈ atomsL B, a.Holds rd σ := by
    intro a ha
    cases hns : needsSide a
    · refine holds_of_good (hgB a ha) ?_
      cases a with
      | mul d x y =>
        simp only [needsSide, Bool.not_eq_false', Bool.and_eq_true, decide_eq_true_eq] at hns
        simp only [Side]
        rw [ite_pos' hns]
        trivial
      | load | assertEq | assertInK | assertNe | rangeCheck | frameAddr | touch => simp [needsSide] at hns
      | _ => trivial
    · cases hik : inkB (inKVals (atomsL B)) a
      · rcases hR a (List.mem_filter.mpr ⟨ha, by simp [hns, hik]⟩) with h | h
        · exact h
        · exact holds_of_good (hgB a ha) h
      · cases a with
        | assertInK x y =>
          simp only [inkB, Bool.and_eq_true, List.contains_iff_mem] at hik
          show IsInK (σ x) ∧ IsInK (σ y)
          rw [hσ x, hσ y]
          exact ⟨inK_of_inKVals hσ hgB hik.1, inK_of_inKVals hσ hgB hik.2⟩
        | _ => simp [inkB] at hik
  exact (holdsList_atoms (allAtoms_of_all hall) next kret).2
    ⟨fun a ha ↦ H a (mem_atomsL.mpr ha), hn⟩

/-- The two specializations' offsets from the bit position's rounds on (`layOff`). -/
def LayOffP (o : ℕ) : Prop := o = 1 ∨ o = 21

/-- A load that is not a store, through a pointer whose word the memory holds: its side
condition. -/
theorem side_load {d p : V} {off : ℕ} (hS : Atom.load d p off ∉ S) {v : E}
    (h : LoadHolds rd (σ p) off v) : Side rd S σ (.load d p off) := by
  simp only [Side, hS, ↓reduceIte]
  exact ⟨h.1, by rw [h.2]; rfl⟩

/-- `side_load` through a pointer whose words `W` the memory holds. -/
theorem side_loadVia {d p : V} {off : ℕ} (hS : Atom.load d p off ∉ S) {W : List E}
    (hW : ReadsAt rd (σ p) W) (hoff : off < W.length) : Side rd S σ (.load d p off) :=
  side_load hS (hW off hoff)

/-- A load that is not a store reads the memory's word. -/
theorem load_val {d p : V} {off : ℕ} (hg : Good rd S w σ (.load d p off))
    (hS : Atom.load d p off ∉ S) {v : E} (h : LoadHolds rd (σ p) off v) : σ d = v := by
  rcases hg with h' | h'
  · exact absurd h' hS
  · rw [h', rdAt_load h]

/-! ## Small facts -/

theorem good_mul {d x y : V} (h : x.idx < d.idx ∧ y.idx < d.idx) (hg : Good rd S w σ (.mul d x y)) :
    σ d = σ x * σ y := by
  simp only [Good, h.1, h.2, and_self, ↓reduceIte] at hg
  exact hg

theorem holds_mul {d x y : V} (h : x.idx < d.idx ∧ y.idx < d.idx) (hg : Good rd S w σ (.mul d x y)) :
    (Atom.mul d x y).Holds rd σ :=
  holds_of_good hg (by simp only [Side, h.1, h.2, and_self, ↓reduceIte])

theorem holds_store {d p : V} {off : ℕ} (hS : Atom.load d p off ∈ S)
    (hg : Good rd S w σ (.load d p off)) (h : LoadHolds rd (σ p) off (σ d)) :
    (Atom.load d p off).Holds rd σ :=
  holds_of_good hg (by simp only [Side, hS, ↓reduceIte]; exact h)

theorem holds_read {d p : V} {off : ℕ} (hS : Atom.load d p off ∉ S)
    (hg : Good rd S w σ (.load d p off)) {v : E} (h : LoadHolds rd (σ p) off v) :
    (Atom.load d p off).Holds rd σ :=
  holds_of_good hg (side_load hS h)

theorem mul_good {d x y : ℕ} (hx : x < d) (hy : y < d)
    (h : GoodS rd S w σ (.atom (.mul (.n d) (.n x) (.n y)))) : σ (.n d) = σ (.n x) * σ (.n y) := by
  simp only [GoodS, Good] at h
  rwa [ite_pos' ⟨hx, hy⟩] at h

theorem idx_lt {a b : ℕ} (h : a < b) : (V.n a).idx < (V.n b).idx := h

end
end LeanVM.Guest.B1.VerifySub.KL
