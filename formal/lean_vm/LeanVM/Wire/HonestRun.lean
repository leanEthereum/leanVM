/-
  LeanVM.Wire.HonestRun

  The honest prover's run (`runFromWithHash`), for a script whose committed words are well shaped
  (`WordsOK`) against a program whose openings and stream are within the wire bounds (`Wired`): its
  phases are openings of one committed tree each, within the bounds, and its stream is as long as
  the program allows.
-/

module

public import LeanVM.Wire.HonestTree

/-!
# The honest prover's run

`Wired p heights n c Q`: along every run of `p` from commitments of the heights `heights`, with at
most `n` openings and `c` stream elements left, every opening asks `1` to `wireMaxQueries` positions
below `2^height` of a commitment of height at most `wireMaxHeight` (`QueryShape`), there are at most
`n` of them, the stream elements read (a scalar one, a packed message its length, a nonce one, a
root two) are at most `c`, and every value returned satisfies `Q` there.

`WordsOK s`: every word the script `s` commits, on any path, has rows of one length, at most
`wireMaxLeafWords`.

`runFrom_wire`: from trees the prover built, a run of a `WordsOK` script against a `Wired` program
makes at most `c` stream elements and at most `n` phases, each the openings of one built tree at
positions within the bounds, hence decodable (`phaseDecodable_opening`).

The pruning idea and its formalization on leanerVM's main branch are scaraven's
(https://github.com/scaraven).
-/

@[expose] public section

namespace LeanVM.Wire

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile
open LeanVM.Prover (Tree Script buildTreeWithHash runFromWithHash)

variable {α β : Type}

/-! ## The program's openings and stream -/

/-- **An opening within the wire bounds**: `1` to `wireMaxQueries` positions, below `2^height`, of
a commitment of height at most `wireMaxHeight`. -/
def QueryShape (height : ℕ) (positions : List ℕ) : Prop :=
  positions ≠ [] ∧ positions.length ≤ wireMaxQueries ∧ height ≤ wireMaxHeight ∧
    ∀ q ∈ positions, q < 2 ^ height

/-- **Openings and stream within the wire bounds** (see the module docstring). -/
def Wired : VerifierProgram α → List ℕ → ℕ → ℕ → (α → List ℕ → ℕ → Prop) → Prop
  | .ret a, hs, n, _, Q => Q a hs n
  | .fail, _, _, _, _ => True
  | .read k, hs, n, c, Q => 1 ≤ c ∧ ∀ x, Wired (k x) hs n (c - 1) Q
  | .sample k, hs, n, c, Q => ∀ x, Wired (k x) hs n c Q
  | .readPacked m k, hs, n, c, Q => m ≤ c ∧ ∀ xs, Wired (k xs) hs n (c - m) Q
  | .samplePacked _ k, hs, n, c, Q => ∀ xs, Wired (k xs) hs n c Q
  | .grind _ k, hs, n, c, Q => 1 ≤ c ∧ Wired k hs n (c - 1) Q
  | .commit height _ k, hs, n, c, Q => 2 ≤ c ∧ Wired k (hs ++ [height]) n (c - 2) Q
  | .query i ps k, hs, n, c, Q =>
    0 < n ∧ QueryShape (hs.getD i 0) ps ∧ ∀ rows, Wired (k rows) hs (n - 1) c Q

/-! ## The script's words -/

/-- **Every word the script commits is well shaped**: rows of one length, at most
`wireMaxLeafWords`. -/
def WordsOK : Script β → Prop
  | .ret _ => True
  | .send _ k => WordsOK k
  | .sample k => ∀ c, WordsOK (k c)
  | .sendPacked _ k => WordsOK k
  | .samplePacked _ k => ∀ cs, WordsOK (k cs)
  | .grind _ k => WordsOK k
  | .commit w k => (∃ L ≤ wireMaxLeafWords, ∀ p, (w p).length = L) ∧ WordsOK k
  | .query k => ∀ rows, WordsOK (k rows)

/-- `WordsOK` of a script the run may hold. -/
def ScriptOK : Option (Script β) → Prop
  | none => True
  | some s => WordsOK s

theorem scriptOK_afterSend {S : Option (Script β)} (h : ScriptOK S) :
    ScriptOK (Script.afterSend S) := by
  rcases S with _ | ⟨_ | _ | _ | _ | _ | _ | _ | _⟩ <;> trivial

theorem scriptOK_afterSample (c : E) {S : Option (Script β)} (h : ScriptOK S) :
    ScriptOK (Script.afterSample c S) := by
  rcases S with _ | ⟨_ | _ | _ | _ | _ | _ | _ | _⟩ <;> first | trivial | exact h c

theorem scriptOK_afterSendPacked {S : Option (Script β)} (h : ScriptOK S) :
    ScriptOK (Script.afterSendPacked S) := by
  rcases S with _ | ⟨_ | _ | _ | _ | _ | _ | _ | _⟩ <;> trivial

theorem scriptOK_afterSamplePacked (cs : List E) {S : Option (Script β)} (h : ScriptOK S) :
    ScriptOK (Script.afterSamplePacked cs S) := by
  rcases S with _ | ⟨_ | _ | _ | _ | _ | _ | _ | _⟩ <;> first | trivial | exact h cs

theorem scriptOK_afterGrind {S : Option (Script β)} (h : ScriptOK S) :
    ScriptOK (Script.afterGrind S) := by
  rcases S with _ | ⟨_ | _ | _ | _ | _ | _ | _ | _⟩ <;> trivial

theorem scriptOK_afterCommit {S : Option (Script β)} (h : ScriptOK S) :
    ScriptOK (Script.afterCommit S) := by
  rcases S with _ | ⟨_ | _ | _ | _ | _ | _ | _ | _⟩ <;> first | trivial | exact h.2

theorem scriptOK_afterQuery (rows : List (List K)) {S : Option (Script β)} (h : ScriptOK S) :
    ScriptOK (Script.afterQuery rows S) := by
  rcases S with _ | ⟨_ | _ | _ | _ | _ | _ | _ | _⟩ <;> first | trivial | exact h rows

theorem wordOf_ok {S : Option (Script β)} (h : ScriptOK S) :
    ∃ L ≤ wireMaxLeafWords, ∀ p, (Script.wordOf S p).length = L := by
  rcases S with _ | ⟨_ | _ | _ | _ | _ | _ | _ | _⟩
  all_goals first
    | exact h.1
    | exact ⟨0, Nat.zero_le _, fun _ ↦ rfl⟩

theorem length_packedOf (n : ℕ) (S : Option (Script β)) : (Script.packedOf n S).length = n := by
  rcases S with _ | ⟨_ | _ | _ | _ | _ | _ | _ | _⟩ <;> simp [Script.packedOf]

/-! ## The run -/

/-- A tree the prover built over `h`, of a word whose rows are of one length, at most
`wireMaxLeafWords`. -/
def TreeOK (h : Bytes → Digest) (t : Tree) : Prop :=
  t = Id.run (buildTreeWithHash (m := Id) h t.height t.word) ∧
    ∃ L ≤ wireMaxLeafWords, ∀ p, (t.word p).length = L

section Run

variable (h : Bytes → Digest) (F : KeccakState → KeccakState) (fuel : ℕ)

/-- **The honest prover's run is within the wire bounds**: from trees it built, a run of a
`WordsOK` script against a `Wired` program makes at most `c` stream elements and at most `n`
phases, each one tree's openings within the bounds. -/
theorem runFrom_wire :
    ∀ (P : VerifierProgram α) (S : Option (Script β)) (sp : Sponge) (cs : List Tree) (n c : ℕ)
      {Q : α → List ℕ → ℕ → Prop} {xs : List E} {os : List (List Opening)},
      (∀ t ∈ cs, TreeOK h t) → Wired P (cs.map (·.height)) n c Q → ScriptOK S →
      Id.run (runFromWithHash (m := Id) h F fuel P S sp cs) = some (xs, os) →
      xs.length ≤ c ∧ os.length ≤ n ∧ ∀ phase ∈ os, ∃ ht w, PhaseDecodable h phase ht w := by
  intro P
  induction P with
  | ret a =>
    intro S sp cs n c Q xs os _ _ _ hp
    simp only [runFromWithHash, Id.run] at hp
    obtain ⟨rfl, rfl⟩ := hp
    simp
  | fail =>
    intro S sp cs n c Q xs os _ _ _ hp
    simp only [runFromWithHash, Id.run] at hp
    obtain ⟨rfl, rfl⟩ := hp
    simp
  | read k ih =>
    intro S sp cs n c Q xs os hcs hw hs hp
    simp only [runFromWithHash, Id.run, bind, pure, Option.map_eq_some_iff] at hp
    obtain ⟨⟨xs', os'⟩, hp, he⟩ := hp
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨h1, h2, h3⟩ := ih _ _ _ cs n (c - 1) hcs (hw.2 _) (scriptOK_afterSend hs) hp
    exact ⟨by simp only [List.length_cons]; have := hw.1; omega, h2, h3⟩
  | sample k ih =>
    intro S sp cs n c Q xs os hcs hw hs hp
    simp only [runFromWithHash, Id.run, bind] at hp
    exact ih _ _ _ cs n c hcs (hw _) (scriptOK_afterSample _ hs) hp
  | readPacked m k ih =>
    intro S sp cs n c Q xs os hcs hw hs hp
    simp only [runFromWithHash, Id.run, bind, pure, Option.map_eq_some_iff] at hp
    obtain ⟨⟨xs', os'⟩, hp, he⟩ := hp
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨h1, h2, h3⟩ := ih _ _ _ cs n (c - m) hcs (hw.2 _) (scriptOK_afterSendPacked hs) hp
    refine ⟨?_, h2, h3⟩
    rw [List.length_append, length_packedOf]
    have := hw.1
    omega
  | samplePacked m k ih =>
    intro S sp cs n c Q xs os hcs hw hs hp
    simp only [runFromWithHash, Id.run, bind] at hp
    exact ih _ _ _ cs n c hcs (hw _) (scriptOK_afterSamplePacked _ hs) hp
  | grind bits k ih =>
    intro S sp cs n c Q xs os hcs hw hs hp
    simp only [runFromWithHash, Id.run, bind, pure] at hp
    split at hp
    · cases hp
    · simp only [Option.map_eq_some_iff] at hp
      obtain ⟨⟨xs', os'⟩, hp, he⟩ := hp
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      obtain ⟨h1, h2, h3⟩ := ih _ _ cs n (c - 1) hcs hw.2 (scriptOK_afterGrind hs) hp
      exact ⟨by simp only [List.length_cons]; have := hw.1; omega, h2, h3⟩
  | commit ht w k ih =>
    intro S sp cs n c Q xs os hcs hw hs hp
    simp only [runFromWithHash, Id.run, bind, pure, Option.map_eq_some_iff] at hp
    obtain ⟨⟨xs', os'⟩, hp, he⟩ := hp
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have hcs' : ∀ t ∈ cs ++ [Id.run (buildTreeWithHash (m := Id) h ht (Script.wordOf S))],
        TreeOK h t := by
      intro t ht'
      rcases List.mem_append.mp ht' with ht' | ht'
      · exact hcs t ht'
      · rw [List.mem_singleton] at ht'
        subst ht'
        exact ⟨rfl, wordOf_ok hs⟩
    have hw' : Wired k ((cs ++ [Id.run (buildTreeWithHash (m := Id) h ht (Script.wordOf S))]).map
        (·.height)) n (c - 2) Q := by
      rw [List.map_append]
      exact hw.2
    obtain ⟨h1, h2, h3⟩ := ih _ _ _ n (c - 2) hcs' hw' (scriptOK_afterCommit hs) hp
    exact ⟨by simp only [List.length_cons]; have := hw.1; omega, h2, h3⟩
  | query i ps k ih =>
    intro S sp cs n c Q xs os hcs hw hs hp
    simp only [runFromWithHash] at hp
    split at hp
    · simp only [Id.run, pure, Option.some.injEq, Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      simp
    · next tree htree =>
      simp only [Id.run, bind, pure, Option.map_eq_some_iff] at hp
      obtain ⟨⟨xs', os'⟩, hp, he⟩ := hp
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      obtain ⟨h1, h2, h3⟩ := ih _ _ _ cs (n - 1) c hcs (hw.2.2 _) (scriptOK_afterQuery _ hs) hp
      refine ⟨h1, by simp only [List.length_cons]; have := hw.1; omega, fun phase hph ↦ ?_⟩
      rcases List.mem_cons.mp hph with rfl | hph
      · have hmem := List.mem_of_getElem? htree
        obtain ⟨hbuilt, L, hL, hwL⟩ := hcs tree hmem
        have hht : (cs.map (·.height)).getD i 0 = tree.height := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_map, htree]
          rfl
        obtain ⟨hne, hlen, hle, hlt⟩ := hw.2.1
        rw [hht] at hle hlt
        refine ⟨tree.height, L, ?_⟩
        rw [hbuilt]
        exact phaseDecodable_opening hwL hne hlen hle hL hlt
      · exact h3 phase hph

end Run

end LeanVM.Wire

end
