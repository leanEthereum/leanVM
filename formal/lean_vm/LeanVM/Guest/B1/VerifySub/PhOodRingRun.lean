/-
  LeanVM.Guest.B1.VerifySub.PhOodRingRun

  A grind, then a packed draw of `18` challenges, on the carried sponge.
-/

module

public import LeanVM.Guest.B1.Link.Packed

/-!
# A grind, then a packed draw

`rwh_grind_packed`: at any permutation `F` (a variable, so that the kernel never unfolds
Keccak-f), a grind then a packed draw of `18` reads the nonce, permutes, checks the proof of work,
and draws the ground challenge, the permutation's cells `2 .. 7` (`packedChallengeOf`) and eleven
from permutations of its capacity. `runsTo_grindPacked`: the same on the carried sponge.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The permutation a grind's nonce takes from the sponge `⟨st, p, none⟩`, at the permutation `F`. -/
def gpState (F : KeccakState → KeccakState) (st : KeccakState) (p : List (E × ℕ)) (n : E) :
    KeccakState :=
  F (duplexInput (Id.run (Compile.absorb (m := Id) F ⟨st, p, none⟩ n dsPowNonce)))

/-- **A grind, then a packed draw of `18`**, at any hash and permutation. -/
theorem rwh_grind_packed (H : List UInt8 → Digest) (F : KeccakState → KeccakState) {α : Type}
    (bits : ℕ) (k : List E → VerifierProgram α) (st : KeccakState) (p : List (E × ℕ)) (n : E)
    (rest : List E) (os : List (List Opening)) (roots : List (Digest × ℕ × ℕ)) :
    Compile.runWithHash (m := Id) H F (.grind bits (.samplePacked 18 k))
        ⟨⟨st, p, none⟩, n :: rest, os, roots⟩ =
      if powOk bits (Keccak.lane (gpState F st p n) 2) = true then
        Compile.runWithHash (m := Id) H F (k (challengeOf (gpState F st p n) ::
            (List.range 6).map (packedChallengeOf (gpState F st p n) ∘ (· + 2)) ++
            (squeezePackedChunks (m := Id) F 11 ⟨gpState F st p n, [], none⟩ 11).1))
          ⟨(squeezePackedChunks (m := Id) F 11 ⟨gpState F st p n, [], none⟩ 11).2, rest, os, roots⟩
      else none := rfl

/-- **A grind, then a packed draw of `18` challenges**, from the carried sponge: the nonce read,
its permutation `S` passing the proof of work, the challenges `S`'s ground one, its cells
`2 .. 7` and the first eleven of two permutations of its capacity. -/
theorem runsTo_grindPacked {α : Type} {bits : ℕ} (hb : bits ≠ 0) (s : Fs) (n : E)
    (hok : powOk bits (Keccak.lane (s.nonceState n) 2) = true) (k : List E → VerifierProgram α)
    {ys : List E} {a : α} {s' : Fs}
    (hk : RunsTo (k (challengeOf (s.nonceState n) ::
        (List.range 6).map (packedChallengeOf (s.nonceState n) ∘ (· + 2)) ++
        (Link.pkSqueeze 2 (capOf (s.nonceState n))).1.take 11))
      ⟨(Link.pkSqueeze 2 (capOf (s.nonceState n))).2, []⟩ ys a s') :
    RunsTo (VerifierProgram.grindProofOfWork bits >>= fun _ =>
      VerifierProgram.sampleChallengesPacked 18 >>= k) s (n :: ys) a s' := by
  intro sp hs rest os roots
  obtain ⟨e1, hc⟩ := Link.spc_carried 2 (capOf (s.nonceState n)) ⟨s.nonceState n, [], none⟩ 11 11
    ⟨rfl, rfl, rfl⟩ (by omega) (by omega) (by omega)
  obtain ⟨sp2, hs2, e2⟩ := hk _ hc rest os roots
  refine ⟨sp2, hs2, ?_⟩
  obtain ⟨st, pd, g⟩ := sp
  have hg : g = none := hs.2.2
  subst hg
  have hS : gpState keccakF1600 st pd n = s.nonceState n := by
    rw [gpState, perm_eq (carries_absorb hs n dsPowNonce)]
    rfl
  have hprog : (VerifierProgram.grindProofOfWork bits >>= fun _ =>
      VerifierProgram.sampleChallengesPacked 18 >>= k) =
      .grind bits (.samplePacked 18 fun xs ↦ (VerifierProgram.ret xs).bind k) := by
    rw [VerifierProgram.grindProofOfWork, ite_eq_right hb]
    rfl
  rw [hprog]
  show Compile.runWithHash (m := Id) keccak256 keccakF1600 _ ⟨⟨st, pd, none⟩, n :: (ys ++ rest), os, roots⟩ = _
  rw [rwh_grind_packed, hS, ite_eq_left hok, e1]
  exact e2

/-- **The draw's challenges, written out**: the ground one, cells `2 .. 7`, then cells `0 .. 7` of
the capacity's permutation and `0 .. 2` of the next one. -/
theorem grindPacked_list (S : KeccakState) :
    challengeOf S :: (List.range 6).map (packedChallengeOf S ∘ (· + 2)) ++
      (Link.pkSqueeze 2 (capOf S)).1.take 11 =
    [challengeOf S, packedChallengeOf S 2, packedChallengeOf S 3, packedChallengeOf S 4,
      packedChallengeOf S 5, packedChallengeOf S 6, packedChallengeOf S 7,
      Link.cellAt (Link.pkPerm (capOf S)) 0, Link.cellAt (Link.pkPerm (capOf S)) 1,
      Link.cellAt (Link.pkPerm (capOf S)) 2, Link.cellAt (Link.pkPerm (capOf S)) 3,
      Link.cellAt (Link.pkPerm (capOf S)) 4, Link.cellAt (Link.pkPerm (capOf S)) 5,
      Link.cellAt (Link.pkPerm (capOf S)) 6, Link.cellAt (Link.pkPerm (capOf S)) 7,
      Link.cellAt (Link.pkPerm (capOf (Link.pkPerm (capOf S)))) 0,
      Link.cellAt (Link.pkPerm (capOf (Link.pkPerm (capOf S)))) 1,
      Link.cellAt (Link.pkPerm (capOf (Link.pkPerm (capOf S)))) 2] := by
  simp [Link.pkSqueeze, List.range_succ]

theorem grindPacked_cap (S : KeccakState) :
    (Link.pkSqueeze 2 (capOf S)).2 = capOf (Link.pkPerm (capOf (Link.pkPerm (capOf S)))) := rfl

end
end LeanVM.Guest.B1.VerifySub
