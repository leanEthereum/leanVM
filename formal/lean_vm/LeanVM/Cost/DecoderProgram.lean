module

public import LeanVM.Cost.ExtractorProgram
public import LeanVM.Cost.Decoder.Ends

/-!
# The guest decoder's program: the entry and the program of a compiled top

`GuestKnowledgeSoundness` (`Statement/LeanVmGuest.lean`) runs the decoder program's function `0` on
`encodeGuestWitnessDecoderInput prog t = .ctor 0 [encodeValue prog, encodeValue t]`, an execution encoded as
`.ctor 0 [encodeValue κ, encodeFiniteFunction t.memory, encodeValue t.steps]`. The compiled top
(on `Cost/Decoder/Ends.lean`'s input side) is a function of the program, `κ` and the
memory vector `memoryVector t.memory`, whose encoding is the memory's
(`encodeValue_memoryVector`): the entry passes the input's words as they are.

* `decoderEntryBody j`: function `0`, destructuring the input and calling function `j` on the
  program, `κ` and the memory's array; **`runsBody_decoderEntry`**: at `13` more than the
  call (two `case`s and their five fields, three variables, the call); **`outputWithin_decoderEntry`**: the output within a budget `b` covering them, of a program
  within the size bound;
* `decoderProgramOf j deps`: the entry at `0`, then the compiled top's bodies `deps`
  (`j`'s `costDeps`), `.position 0` at every other index up to the last (`ofListPos`; the
  decoder's chain follows the extractor's, whose indices it mostly skips, and a position is
  smaller than `MachineProgram.ofList`'s literal `0`); `decoderProgramOf_includes`, `decoderProgramOf_entry`: given its indices
  increasing (`increasingFrom 0`, a linear check by evaluation), it holds its bodies and its
  entry; `decoderProgramOf_size_le_of_increasing`: its size, exactly its bodies' and one per
  index without a body (`size_ofListPos_add_length`), the sum evaluated in `Cost/DecoderSize.lean`,
  a module of its own.
-/

namespace LeanVM.Cost

open LeanVM.Parameters LeanVM.Semantics LeanVM.Cost.Decoder

public section

/-! ## The entry -/

/-- **The decoder's entry body**: the input's program, the execution's `κ` and its memory's array
passed to function `j`, whose output is the program's. -/
@[expose] def decoderEntryBody (j : ℕ) : Term :=
  .case (.position 0) [.case (.position 1) [.call j [.position 3, .position 0, .position 1]]]

/-- **The entry runs the top** on the input's fields: at `13` more than the call. -/
theorem runsBody_decoderEntry {P : MachineProgram} {j : ℕ}
    (hentry : P[0]? = some (decoderEntryBody j)) (prog : LeanIsaProgram) (t : Execution prog)
    {v : MachineValue} {e : ℕ}
    (h : RunsBody P j [encodeValue prog, encodeValue t.logMemorySize,
      encodeValue (memoryVector t.memory)] v e) :
    RunsBody P 0 [encodeGuestWitnessDecoderInput prog t] v (e + 13) := by
  rw [encodeValue_memoryVector] at h
  let x := encodeGuestWitnessDecoderInput prog t
  let env1 : List MachineValue := [encodeValue prog, encodeValue t, x]
  let env2 : List MachineValue :=
    [encodeValue t.logMemorySize, encodeValue t.memory, encodeValue t.stepCount] ++ env1
  have hargs : RunsList P env2 [.position 3, .position 0, .position 1]
      [encodeValue prog, encodeValue t.logMemorySize, encodeValue t.memory] 3 :=
    RunsList.cons (Runs.var rfl) (RunsList.cons (Runs.var rfl)
      (RunsList.cons (Runs.var rfl) RunsList.nil))
  have hcall := Runs.call hargs h
  have ht : Runs P env1 (.position 1)
      (.constructor 0 [encodeValue t.logMemorySize, encodeValue t.memory, encodeValue
          t.stepCount]) 1 :=
    Runs.var rfl
  have hinner := Runs.case (alts := [.call j [.position 3, .position 0, .position 1]]) ht rfl hcall
  have hx : Runs P [x] (.position 0) (.constructor 0 [encodeValue prog, encodeValue t]) 1 :=
      Runs.var rfl
  have houter := Runs.case (alts := [.case (.position 1) [.call j [.position 3, .position 0,
      .position 1]]]) hx rfl
    hinner
  exact RunsBody.intro hentry (houter.cost_eq (by simp only [List.length_cons, List.length_nil]; omega))

/-- **The program's output is the top's**, within a budget covering the top's price and the
entry's `13`, of a program within the size bound `s`. -/
theorem outputWithin_decoderEntry {P : MachineProgram} {j s : ℕ} (hs : MachineProgram.size P ≤ s)
    (hentry : P[0]? = some (decoderEntryBody j)) (prog : LeanIsaProgram) (t : Execution prog)
    {v : MachineValue} {e b : ℕ}
    (h : RunsBody P j [encodeValue prog, encodeValue t.logMemorySize,
      encodeValue (memoryVector t.memory)] v e) (hb : e + 13 ≤ b) :
    outputWithin P s b (encodeGuestWitnessDecoderInput prog t) = some v :=
  outputWithin_of_runs hs (runsBody_decoderEntry hentry prog t h) hb

/-! ## Programs from lists of bodies, a position at an index without a body -/

/-- `MachineProgram.ofList` with `.position 0` (size `1`, not the literal `0`'s `2`) at an index
without a body: no call of the compiled bodies reaches one. -/
@[expose] def ofListPos (l : List (ℕ × Term)) : MachineProgram :=
  let n := (l.map (·.1)).foldr max 0 + 1
  l.foldl (fun P p ↦ P.setIfInBounds p.1 p.2) (Array.replicate n (.position 0))

/-- **A program built from distinct indices holds its bodies.** -/
theorem includes_ofListPos (l : List (ℕ × Term)) (hl : (l.map (·.1)).Nodup) :
    Includes (ofListPos l) l := by
  intro p hp
  refine getElem?_foldl_set l hl _ (fun r hr ↦ ?_) p hp
  rw [Array.size_replicate]
  exact lt_foldr_max_succ (List.mem_map_of_mem hr)

/-- Setting an index that holds `.position 0` (size `1`): the size gains the body's, less `1`. -/
theorem size_setIfInBounds_pos (A : MachineProgram) (i : ℕ) (t : Term)
    (h : A[i]? = some (.position 0)) :
    MachineProgram.size (A.setIfInBounds i t) + 1 = MachineProgram.size A + t.size := by
  obtain ⟨hi, hA⟩ := Array.getElem?_eq_some_iff.1 h
  have h1 : (Term.position 0).size = 1 := rfl
  unfold MachineProgram.size
  rw [Array.setIfInBounds_def]
  simp only [hi, ↓reduceDIte, Array.toList_set]
  have := sum_map_set_add Term.size A.toList i t (by simpa using hi)
  rw [Array.getElem_toList, hA, h1] at this
  exact this

/-- **A program's size from its bodies, exactly**: with distinct indices, the bodies' sizes and
one per index without a body. -/
theorem size_ofListPos_add_length (l : List (ℕ × Term)) (hl : (l.map (·.1)).Nodup) :
    (ofListPos l).size + l.length = (l.map fun p ↦ p.2.size).sum + ((l.map (·.1)).foldr max 0 + 1) := by
  have key : ∀ (l : List (ℕ × Term)) (A : MachineProgram), (l.map (·.1)).Nodup →
      (∀ p ∈ l, A[p.1]? = some (.position 0)) →
      MachineProgram.size (l.foldl (fun P p ↦ P.setIfInBounds p.1 p.2) A) + l.length =
        MachineProgram.size A + (l.map fun p ↦ p.2.size).sum := by
    intro l
    induction l with
    | nil => intro A _ _; simp
    | cons q l ih =>
      intro A hn hA
      simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
      have hrest : ∀ p ∈ l, (A.setIfInBounds q.1 q.2)[p.1]? = some (.position 0) := by
        intro p hp
        have hne : q.1 ≠ p.1 := fun he ↦ hn.1 ⟨p, hp, he.symm⟩
        rw [Array.getElem?_setIfInBounds_ne hne]
        exact hA p (List.mem_cons_of_mem _ hp)
      have := ih (A.setIfInBounds q.1 q.2) hn.2 hrest
      have := size_setIfInBounds_pos A q.1 q.2 (hA q List.mem_cons_self)
      simp only [List.foldl_cons, List.map_cons, List.sum_cons, List.length_cons]
      omega
  have hrep : ∀ n, MachineProgram.size (Array.replicate n (Term.position 0)) = n := by
    intro n
    simp [MachineProgram.size, Array.toList_replicate, List.map_replicate, List.sum_replicate,
      Term.size]
  have := key l (Array.replicate ((l.map (·.1)).foldr max 0 + 1) (.position 0)) hl
    (fun p hp ↦ by
      rw [Array.getElem?_replicate]
      simp only [lt_foldr_max_succ (List.mem_map_of_mem hp), ↓reduceIte])
  rw [hrep] at this
  unfold ofListPos
  dsimp only
  omega

/-! ## The program of a compiled top -/

/-- The bodies: the entry at `0`, then `deps`. -/
@[expose] def decoderProgramBodiesOf (j : ℕ) (deps : List (ℕ × Term)) : List (ℕ × Term) :=
  (0, decoderEntryBody j) :: deps

/-- **The decoder program of the compiled top `j`** with its bodies `deps` (`j`'s `costDeps`). -/
@[expose] def decoderProgramOf (j : ℕ) (deps : List (ℕ × Term)) : MachineProgram :=
  ofListPos (decoderProgramBodiesOf j deps)

/-- With increasing indices, the program holds its bodies. -/
theorem decoderProgramOf_includes_all {j : ℕ} {deps : List (ℕ × Term)}
    (h : increasingFrom 0 (deps.map (·.1)) = true) :
    Includes (decoderProgramOf j deps) (decoderProgramBodiesOf j deps) :=
  includes_ofListPos _ (by
    rw [decoderProgramBodiesOf, List.map_cons]
    exact nodup_of_increasing h)

/-- With increasing indices, the program holds the top's bodies. -/
theorem decoderProgramOf_includes {j : ℕ} {deps : List (ℕ × Term)}
    (h : increasingFrom 0 (deps.map (·.1)) = true) : Includes (decoderProgramOf j deps) deps :=
  (decoderProgramOf_includes_all h).mono fun _ hp ↦ List.mem_cons_of_mem _ hp

/-- With increasing indices, the program's function `0` is the entry. -/
theorem decoderProgramOf_entry {j : ℕ} {deps : List (ℕ × Term)}
    (h : increasingFrom 0 (deps.map (·.1)) = true) :
    (decoderProgramOf j deps)[0]? = some (decoderEntryBody j) :=
  (decoderProgramOf_includes_all h).get List.mem_cons_self

/-- **The program's size from its bodies, exactly** (`size_ofListPos_add_length`): with increasing
indices, a bound on the bodies' sizes and one per index, less one per body. -/
theorem decoderProgramOf_size_le_of_increasing {j : ℕ} {deps : List (ℕ × Term)} {N : ℕ}
    (hi : increasingFrom 0 (deps.map (·.1)) = true)
    (h : ((decoderProgramBodiesOf j deps).map fun p ↦ p.2.size).sum +
      (((decoderProgramBodiesOf j deps).map (·.1)).foldr max 0 + 1) ≤
        N + (deps.length + 1)) :
    (decoderProgramOf j deps).size ≤ N := by
  have := size_ofListPos_add_length (decoderProgramBodiesOf j deps) (by
    rw [decoderProgramBodiesOf, List.map_cons]
    exact nodup_of_increasing hi)
  rw [show (decoderProgramBodiesOf j deps).length = deps.length + 1 from rfl] at this
  unfold decoderProgramOf
  omega

end

end LeanVM.Cost
