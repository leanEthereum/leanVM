/-
  LeanVM.Guest.B1.KeccakGkr.FsComplete

  The sponge templates, completely: on an evaluated valuation (`Fwd.Good`), `fs_next`,
  `challenge_from_state` and a `KECCAK` atom hold once their words are in memory and their inputs
  canonical.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.Lib
public import LeanVM.Guest.B1.Fwd.Eval

/-!
# The sponge templates, completely

* `fsNext_complete`: `fs_next`'s word read from memory (not a store), its limbs hinted, so the
  word is the memory's, the packed cells canonical and the scalar's rate cells
  (`Keccak.scalarCells`), and the template holds.
* `challenge_complete`: `challenge_from_state` on a canonical cell holds (`ChallengeOk`).
* `keccakA_complete`: a `KECCAK` atom on canonical inputs holds.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

variable {C : CallRel} {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val}

theorem rdAt_load {p : E} {k : ℕ} {v : E} (h : LoadHolds rd p k v) : rdAt rd p k = v := by
  unfold rdAt; rw [h.2]; rfl

theorem limbAt_zero' (x : E) : limbAt x 0 = ofK (x.limb 0) := rfl

/-- **`fs_pack` on an evaluated valuation**: its honest values. -/
theorem fsPack_vals_of_good {x : V} {b t : ℕ} (hg : ∀ s ∈ fsPackT x b t, GoodS rd S w σ s) :
    ∀ i < 9, σ (.n (b + i)) = fsPackVals (σ x) t i := by
  simp only [fsPackT, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true, GoodS, Good] at hg
  obtain ⟨hl, e3, -, e4, e5, e6, e7, e8⟩ := hg
  have l0 : σ (.n b) = ofK ((σ x).limb 0) := hl 0 (by simp)
  have l1 : σ (.n (b + 1)) = ofK ((σ x).limb 1) := hl 1 (by simp)
  have l2 : σ (.n (b + 2)) = ofK ((σ x).limb 2) := hl 2 (by simp)
  have m5 : σ (.n (b + 5)) = σ (.n (b + 4)) * σ (.n (b + 2)) := by
    simp only [V.n] at e5
    rwa [ite_pos' (by simp)] at e5
  intro i hi
  interval_cases i
  · exact l0
  · exact l1
  · exact l2
  · exact e3
  · exact e4
  · show σ (.n (b + 5)) = word 0 0 1 * ofK ((σ x).limb 2); rw [m5, e4, l2]
  · show σ (.n (b + 6)) = σ x + word 0 0 1 * ofK ((σ x).limb 2); rw [e6, m5, e4, l2]
  · exact e7
  · show σ (.n (b + 8)) = ofK ((σ x).limb 2) + word 0 t 0; rw [e8, l2, e7]

/-- **`fs_next` on an evaluated valuation**: the word read from memory, its packed cells
canonical and the scalar's rate cells, and the template holds. -/
theorem fsNext_complete {cur : V} {off b : ℕ} (hg : ∀ s ∈ fsNextT cur off b, GoodS rd S w σ s)
    (hnS : Atom.load (.n b) cur off ∉ S) {v : E} (hv : LoadHolds rd (σ cur) off v) :
    σ (.n b) = v ∧ IsCanonical128 (σ (.n (b + 7))) ∧ IsCanonical128 (σ (.n (b + 9))) ∧
      (σ (.n (b + 7)), σ (.n (b + 9))) = Keccak.scalarCells v dsObserve ∧
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
  have hvals := fsPack_vals_of_good hp
  have v6 : σ (.n (b + 7)) = fsPackVals (σ (.n b)) dsObserve 6 := hvals 6 (by norm_num)
  have v8 : σ (.n (b + 9)) = fsPackVals (σ (.n b)) dsObserve 8 := hvals 8 (by norm_num)
  have hc := fsPackVals_canonical (σ (.n b)) dsObserve
  have hcells := fsPackVals_cells (σ (.n b)) dsObserve
  refine ⟨eb, by rw [v6]; exact hc.1, by rw [v8]; exact hc.2, ?_, fun {next kret} hn ↦ ?_⟩
  · rw [v6, v8, ← eb]; exact hcells
  · exact (holds_fsNextT cur off b next kret).2 ⟨⟨by rw [eb]; exact hv, fsPackOk_of_vals hvals⟩, hn⟩

/-- **`challenge_from_state` on an evaluated valuation** of a canonical cell. -/
theorem challenge_complete {s0 s1 : V} {b : ℕ}
    (hg : ∀ s ∈ challengeT s0 s1 b, GoodS rd S w σ s) (hc : IsCanonical128 (σ s1)) :
    ChallengeOk σ s0 s1 b ∧ ∀ {next : Prop} {kret : List E → Prop},
      next → Stmt.HoldsList C rd σ (challengeT s0 s1 b) next kret := by
  simp only [challengeT, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true, GoodS, Good] at hg
  obtain ⟨hl, e1, e2, e3, -, e4, e5, e6⟩ := hg
  have l0 : σ (.n b) = ofK ((σ s1).limb 0) := hl 0 (by simp)
  have m3 : σ (.n (b + 3)) = σ (.n (b + 1)) * σ (.n (b + 2)) := by
    simp only [V.n] at e3
    rwa [ite_pos' (by simp)] at e3
  have m5 : σ (.n (b + 5)) = σ (.n (b + 4)) * σ (.n b) := by
    simp only [V.n] at e5
    rwa [ite_pos' (by simp)] at e5
  have hok : ChallengeOk σ s0 s1 b := challengeOk_of_vals hc fun i hi ↦ by
    interval_cases i
    · exact l0
    · show σ (.n (b + 1)) = σ s1 + ofK ((σ s1).limb 0); rw [e1, l0]
    · exact e2
    · show σ (.n (b + 3)) = (σ s1 + ofK ((σ s1).limb 0)) * word 1 0 1; rw [m3, e1, l0, e2]
    · exact e4
    · show σ (.n (b + 5)) = word 0 0 1 * ofK ((σ s1).limb 0); rw [m5, e4, l0]
    · show σ (.n (b + 6)) = σ s0 + word 0 0 1 * ofK ((σ s1).limb 0); rw [e6, m5, e4, l0]
  exact ⟨hok, fun {next kret} hn ↦ (holds_challengeT s0 s1 b next kret).2 ⟨hok, hn⟩⟩

/-- **A `KECCAK` atom on an evaluated valuation** with canonical inputs holds. -/
theorem keccakA_complete {ins outs : List V} (hg : Good rd S w σ (.keccak ins outs false false))
    (hc : AllCanonical (ins.map σ)) : (Atom.keccak ins outs false false).Holds rd σ :=
  holds_of_good hg fun c => by
    have hc' : c.val < (ins.map σ).length := by simp [hg.1]
    simpa [cells13, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc'] using
      hc _ (List.getElem_mem hc')

end
end LeanVM.Guest.B1.VerifySub
