module

public import NativeVm.Transcript.Run
public import NativeVm.Transcript.Layout

/-!
# A query's openings, over Keccak-f[1600]

`openPhase` in `Id`: the climb one level at a time (`climbK_cons`), an opening that checks out
(`OpenOk`: its index is its position and its path climbs to the root), and the phase's result
when every opening checks out (`openPhase_some`) or one does not (`openPhase_none_of_not`), the
shapes checked; where the rows go (`QueryRowsAt`, `InArea`).
-/

@[expose] public section

namespace NativeVm.Transcript

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.KeccakHash

/-- The words of the area of `n` words at `b`. -/
def InArea (b : UInt64) (n : Nat) (a : UInt64) : Prop := ∃ k < n, a = wd b k

/-- The rows' words, one after another, from `b`. -/
def QueryRowsAt (mem : UInt64 → Option UInt64) (b : UInt64) (rows : List (List K)) : Prop :=
  ∀ i (h : i < rows.flatten.length), mem (wd b i) = some (rows.flatten[i]'h).lane

/-- `climb` over Keccak-f[1600]. -/
abbrev climbK (node : Digest) (q : Nat) (path : List Digest) : Digest :=
  Id.run (climb (m := Id) keccakF1600 node q path)

/-- One level of a climb: the node left when the position is even. -/
def parentAt (node : Digest) (q : Nat) (sib : Digest) : Digest :=
  if q % 2 = 0 then keccak256 (digestBytes node ++ digestBytes sib)
  else keccak256 (digestBytes sib ++ digestBytes node)

theorem keccak256With_id (data : List UInt8) :
    Id.run (keccak256With (m := Id) keccakF1600 data) = keccak256 data := (rfl)

theorem climbK_nil (node : Digest) (q : Nat) : climbK node q [] = node := (rfl)

theorem climbK_cons (node : Digest) (q : Nat) (sib : Digest) (path : List Digest) :
    climbK node q (sib :: path) = climbK (parentAt node q sib) (q / 2) path := by
  unfold climbK parentAt
  rw [climb]
  split <;> rfl

/-- A leaf's digest. -/
def openingDigest (o : Opening) : Digest := keccak256 (o.leaf.flatMap K.toBytes)

/-- Opening `o` checks out at position `q` against `root`. -/
def OpenOk (root : Digest) (q : Nat) (o : Opening) : Prop :=
  o.leafIndex = q ∧ climbK (openingDigest o) q o.path = root

theorem openOne_run {root : Digest} {height width q : Nat} {o : Opening}
    (hs : o.leaf.length = width ∧ o.path.length = height) :
    Id.run (Compile.openOne (m := Id) keccakF1600 root height width q o) =
      decide (climbK (openingDigest o) q o.path = root) := by
  unfold Compile.openOne
  rw [ite_eq_left_of_eq_true _ _ (eq_true hs)]
  show decide ((climbK (openingDigest o) q o.path).toList = root.toList) = _
  rw [decide_eq_decide]
  exact ⟨fun h ↦ Vector.toList_inj.mp h, fun h ↦ by rw [h]⟩

theorem openAll_cons (root : Digest) (height width q : Nat) (ps : List Nat) (o : Opening)
    (os : List Opening) :
    Id.run (openAll (m := Id) keccakF1600 root height width (q :: ps) (o :: os)) =
      if Id.run (Compile.openOne (m := Id) keccakF1600 root height width q o) then
        (Id.run (openAll (m := Id) keccakF1600 root height width ps os)).map
          fun r ↦ (o.leaf :: r.1, r.2)
      else none := (rfl)

theorem openPhase_run (root : Digest) (height width : Nat) (ps : List Nat) (phase : List Opening) :
    Id.run (openPhase (m := Id) keccakF1600 root height width ps phase) =
      if (∀ opening ∈ phase, opening.leaf.length = width ∧ opening.path.length = height) ∧
          phase.map Opening.leafIndex = ps then
        match Id.run (openAll (m := Id) keccakF1600 root height width ps phase) with
        | some (rows, _) => some rows
        | none => none
      else none := by
  unfold openPhase
  split <;> rfl

/-- Every opening checks out: the leaves, in order. -/
theorem openAll_some {root : Digest} {height width : Nat} :
    ∀ (ps : List Nat) (os : List Opening),
    (∀ o ∈ os, o.leaf.length = width ∧ o.path.length = height) → os.length = ps.length →
    (∀ k (hk : k < ps.length) (hk' : k < os.length), OpenOk root ps[k] os[k]) →
    Id.run (openAll (m := Id) keccakF1600 root height width ps os) = some (os.map (·.leaf), [])
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, h, _ => absurd h (by simp)
  | _ :: _, [], _, h, _ => absurd h (by simp)
  | q :: ps, o :: os, hs, hl, hok => by
    have ih := openAll_some (root := root) (height := height) (width := width) ps os
      (fun o' ho' ↦ hs o' (List.mem_cons_of_mem _ ho')) (by simpa using hl)
      (fun k hk hk' ↦ hok (k + 1) (by simpa using hk) (by simpa using hk'))
    have h1 := (hok 0 (by simp) (by simp)).2
    simp only [List.getElem_cons_zero] at h1
    rw [openAll_cons, openOne_run (hs o (by simp)), h1, decide_eq_true rfl, ite_eq_left_of_eq_true _ _ (eq_true rfl), ih]
    rfl

/-- An opening that does not check out: no leaves. -/
theorem openAll_none {root : Digest} {height width : Nat} :
    ∀ (ps : List Nat) (os : List Opening),
    (∀ o ∈ os, o.leaf.length = width ∧ o.path.length = height) →
    (∃ k, ∃ (hk : k < ps.length) (hk' : k < os.length),
      climbK (openingDigest os[k]) ps[k] os[k].path ≠ root) →
    Id.run (openAll (m := Id) keccakF1600 root height width ps os) = none
  | [], _, _, ⟨_, hk, _⟩ => absurd hk (by simp)
  | _ :: _, [], _, ⟨_, _, hk', _⟩ => absurd hk' (by simp)
  | q :: ps, o :: os, hs, ⟨k, hk, hk', hne⟩ => by
    rw [openAll_cons, openOne_run (hs o (by simp))]
    cases k with
    | zero =>
      simp only [List.getElem_cons_zero] at hne
      rw [decide_eq_false hne]
      rfl
    | succ k =>
      by_cases hc : climbK (openingDigest o) q o.path = root
      · rw [openAll_none (root := root) (height := height) (width := width) ps os
          (fun o' ho' ↦ hs o' (List.mem_cons_of_mem _ ho')) ⟨k, by simpa using hk,
            by simpa using hk', by simpa using hne⟩]
        split <;> rfl
      · rw [decide_eq_false hc]
        rfl

/-- **Every opening checks out**, the shapes right: the phase's leaves. -/
theorem openPhase_some {root : Digest} {height width : Nat} {ps : List Nat} {phase : List Opening}
    (hs : ∀ o ∈ phase, o.leaf.length = width ∧ o.path.length = height)
    (hl : phase.length = ps.length)
    (hok : ∀ k (hk : k < ps.length) (hk' : k < phase.length), OpenOk root ps[k] phase[k]) :
    Id.run (openPhase (m := Id) keccakF1600 root height width ps phase) =
      some (phase.map (·.leaf)) := by
  have hm : phase.map Opening.leafIndex = ps := List.ext_getElem (by simpa using hl)
    fun k h1 h2 ↦ by simpa using (hok k h2 (by simpa using h1)).1
  rw [openPhase_run, ite_eq_left_of_eq_true _ _ (eq_true ⟨hs, hm⟩),
    openAll_some (root := root) (height := height) (width := width) ps phase hs hl hok]

/-- **An opening that does not check out**: no rows. -/
theorem openPhase_none_of_not {root : Digest} {height width : Nat} {ps : List Nat}
    {phase : List Opening} (hs : ∀ o ∈ phase, o.leaf.length = width ∧ o.path.length = height)
    (hbad : ∃ k, ∃ (hk : k < ps.length) (hk' : k < phase.length), ¬ OpenOk root ps[k] phase[k]) :
    Id.run (openPhase (m := Id) keccakF1600 root height width ps phase) = none := by
  rw [openPhase_run]
  by_cases hm : phase.map Opening.leafIndex = ps
  · rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hs, hm⟩)]
    obtain ⟨k, hk, hk', hn⟩ := hbad
    have hi : phase[k].leafIndex = ps[k] := by
      have := congrArg (·[k]?) hm
      simp only [List.getElem?_map, List.getElem?_eq_getElem hk', List.getElem?_eq_getElem hk,
        Option.map_some, Option.some.injEq] at this
      exact this
    rw [openAll_none (root := root) (height := height) (width := width) ps phase hs
      ⟨k, hk, hk', fun e ↦ hn ⟨hi, e⟩⟩]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false fun h ↦ hm h.2)]

/-- **A phase of the wrong length**: no rows. -/
theorem openPhase_none_of_length {root : Digest} {height width : Nat} {ps : List Nat}
    {phase : List Opening} (hl : phase.length ≠ ps.length) :
    Id.run (openPhase (m := Id) keccakF1600 root height width ps phase) = none := by
  rw [openPhase_run, ite_eq_right_of_eq_false _ _ (eq_false fun h ↦ hl (by rw [← h.2, List.length_map]))]

/-- **An opening of the wrong shape**: no rows. -/
theorem openPhase_none_of_shape {root : Digest} {height width : Nat} {ps : List Nat}
    {phase : List Opening}
    (hs : ∃ o ∈ phase, ¬ (o.leaf.length = width ∧ o.path.length = height)) :
    Id.run (openPhase (m := Id) keccakF1600 root height width ps phase) = none := by
  obtain ⟨o, ho, hn⟩ := hs
  rw [openPhase_run, ite_eq_right_of_eq_false _ _ (eq_false fun h ↦ hn (h.1 o ho))]

end NativeVm.Transcript
