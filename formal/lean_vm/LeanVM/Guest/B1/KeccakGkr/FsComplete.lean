/-
  LeanVM.Guest.B1.KeccakGkr.FsComplete

  The sponge templates, completely: on an evaluated valuation (`Fwd.Good`), `fs_next`,
  `challenge_from_state` and a `KECCAK` atom hold once their words are in memory.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.Lib
public import LeanVM.Guest.B1.Fwd.Eval

/-!
# The sponge templates, completely

* `fsNext_complete`: `fs_next`'s word read from memory (not a store), so the word is the
  memory's, its packed cells the scalar's rate cells (`Keccak.scalarCells`), and the template
  holds.
* `challenge_complete`: `challenge_from_state` holds (`ChallengeOk`).
* `keccakA_complete`: a `KECCAK` atom holds.
-/

namespace LeanVM.Guest.B1.VerifySub

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

end
end LeanVM.Guest.B1.VerifySub
