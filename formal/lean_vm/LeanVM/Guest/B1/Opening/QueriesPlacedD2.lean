/-
  LeanVM.Guest.B1.Opening.QueriesPlacedD2

  `opening_queries` is `CompleteAtB`, one statement for every shape.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesPlacedD0

/-!
# `opening_queries`, `CompleteAtB`, one statement

`OqCompleteD fs cert name loop s odd`: when the frames fit (`OqFits`, trivial), on the honest data
of a call (`N` iterations, the rounds' challenges, the final coefficients, the queries' positions,
rows and siblings, the window runs, the caller's buffers in `Lin`: `OqStatic`, `OqLinReg`,
`OqLinMem`), the specialization `name` (loop helper `loop`) is `CompleteAtD`, returning the chain
of the queries' folds (or `0` at the final level); `OqCompleteDB`: `CompleteAtB`, by a tree of at
most `oqBound fs name loop N` words (its frame, its chain buffer, its iterations' frames and its
queries' `walk_path` frames, `oqWalkCount name N` of `oqWalkOfName name`, read off the table
`openingQueriesLoops`). `oqCompleteDB1`, `oqCompleteDB0`: from a specialization's facts (its
bodies the templates, its walk a `walk_path` specialization, its table entry, `oqEntryB`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

/-- The frames fit a specialization's frame runs: neither its queries nor their `walk_path` frames
place a frame run (the path children are hinted into frame cells), so nothing is asked; kept so
the statements reading it stand. -/
def OqFits (_fs : String → ℕ) (_cert : String → V → ℕ) (_name _loop : String) (_s : Oq) (_odd : ℕ) :
    Prop :=
  True

/-- **`opening_queries`, the specialization `name` of the shape `s`, `odd`, is `CompleteAtD`.** -/
def OqCompleteD (fs : String → ℕ) (cert : String → V → ℕ) (name loop : String) (s : Oq)
    (odd : ℕ) : Prop :=
  OqFits fs cert name loop s odd →
    ∀ (κ : ℕ) (Lin : Main.Layout) (N : ℕ) (ecap eflags ecoefs ehs epos eqp : ℕ) (lamInv : E)
      (rounds : List FoldRound) (hsv : List E) (eb qs : ℕ → ℕ) (rows : ℕ → List K)
      (sibs : ℕ → List Digest), N + 1 < ordG → rounds.length = s.folds →
      (s.final = 1 → hsv.length = s.nHs) →
      OqStatic s rounds hsv qs rows sibs (oqCount odd s.base N) →
      OqLinReg (RegionL Lin) s ecap eflags ecoefs ehs epos eqp eb qs (oqCount odd s.base N) →
      (∀ rd, LowDef κ rd → MemL rd Lin →
        OqLinMem rd s (ofK (Parameters.addressOfIndex ecap)) (ofK (Parameters.addressOfIndex eflags))
          (ofK (Parameters.addressOfIndex ecoefs)) (ofK (Parameters.addressOfIndex ehs))
          (ofK (Parameters.addressOfIndex epos)) (ofK (Parameters.addressOfIndex eqp)) rounds hsv eb
          qs rows sibs (oqCount odd s.base N)) →
      CompleteAtD fs cert κ name Lin
        [ofK (Parameters.addressOfIndex ecap), ofK (Parameters.addressOfIndex eflags), lamInv,
          ofK (Parameters.addressOfIndex ecoefs), ofK (Parameters.addressOfIndex ehs),
          ofK (Parameters.addressOfIndex epos), ofK (Parameters.addressOfIndex eqp), gen ^ N]
        (Returns [if s.final = 1 then 0 else
          oqChain odd s.base lamInv (fun k ↦ foldRow (lanesOf s.base (rows k)) (K.ofBits (qs k)) rounds) N])

/-- A specialization's entry of the table: `(name, loop, shape)`. -/
def oqEntryOf (name : String) : Option (String × String × OqShape) :=
  openingQueriesLoops.find? (·.1 = name)

/-- The `walk_path` frames of a call of `N` iterations: one a query (`oqCount`). -/
def oqWalkCount (name : String) (N : ℕ) : ℕ :=
  ((oqEntryOf name).map fun p ↦ oqCount p.2.2.odd p.2.2.base N).getD 0

/-- The `walk_path` specialization a specialization's queries call. -/
def oqWalkOfName (name : String) : String :=
  ((oqEntryOf name).map fun p ↦ oqWalkOf p.2.2.oq).getD ""

/-- The table's entry of `name` has the shape's `base`, `pd`, `cd` and `odd`, as a check. -/
def oqEntryB (name : String) (s : Oq) (odd : ℕ) : Bool :=
  match oqEntryOf name with
  | some p => p.2.2.base == s.base && p.2.2.oq.pd == s.pd && p.2.2.cd == s.cd && p.2.2.odd == odd
  | none => false

theorem oqWalk_of_entryB {name : String} {s : Oq} {odd : ℕ} (h : oqEntryB name s odd = true) :
    (∀ N, oqWalkCount name N = oqCount odd s.base N) ∧ oqWalkOfName name = oqWalkOf s := by
  unfold oqEntryB at h
  unfold oqWalkCount oqWalkOfName
  split at h
  · next p hp =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨hb, hpd⟩, hcd⟩, ho⟩ := h
    simp only [hp, Option.map_some, Option.getD_some, hb, ho, implies_true, true_and]
    have hcd' : p.2.2.oq.cd = s.cd := hcd
    unfold oqWalkOf
    rw [hpd, hcd']
  · exact absurd h (by simp)

/-- `opening_queries`' tree bound: its frame, its chain buffer (`N + 1` cells), its `N + 1`
iterations' frames and its queries' `walk_path` frames. -/
def oqBound (fs : String → ℕ) (name loop : String) (N : ℕ) : ℕ :=
  fs name + (N + 1) + (N + 1) * fs loop + oqWalkCount name N * fs (oqWalkOfName name)

/-- **`opening_queries`, the specialization `name` of the shape `s`, `odd`, is `CompleteAtB`**,
by a tree of at most `oqBound fs name loop N` words: on `[cap, flags, λ⁻¹, coefs, hs, positions,
qptrs, g^N]`, the caller's buffers at `g^e…`, the rounds' challenges, the final coefficients and
the queries' witnesses honest (`OqStatic`, `OqLinMem`, in `Lin`'s region by `OqLinReg`), it
returns the chain of the queries' folds (`oqChain`, the caller scales it), or `0` at the final
level. -/
def OqCompleteDB (fs : String → ℕ) (cert : String → V → ℕ) (name loop : String) (s : Oq)
    (odd : ℕ) : Prop :=
  OqFits fs cert name loop s odd →
    ∀ (κ : ℕ) (Lin : Main.Layout) (N : ℕ) (ecap eflags ecoefs ehs epos eqp : ℕ) (lamInv : E)
      (rounds : List FoldRound) (hsv : List E) (eb qs : ℕ → ℕ) (rows : ℕ → List K)
      (sibs : ℕ → List Digest), N + 1 < ordG → rounds.length = s.folds →
      (s.final = 1 → hsv.length = s.nHs) →
      OqStatic s rounds hsv qs rows sibs (oqCount odd s.base N) →
      OqLinReg (RegionL Lin) s ecap eflags ecoefs ehs epos eqp eb qs (oqCount odd s.base N) →
      (∀ rd, LowDef κ rd → MemL rd Lin →
        OqLinMem rd s (ofK (Parameters.addressOfIndex ecap)) (ofK (Parameters.addressOfIndex eflags))
          (ofK (Parameters.addressOfIndex ecoefs)) (ofK (Parameters.addressOfIndex ehs))
          (ofK (Parameters.addressOfIndex epos)) (ofK (Parameters.addressOfIndex eqp)) rounds hsv eb
          qs rows sibs (oqCount odd s.base N)) →
      CompleteAtB fs cert κ name Lin
        [ofK (Parameters.addressOfIndex ecap), ofK (Parameters.addressOfIndex eflags), lamInv,
          ofK (Parameters.addressOfIndex ecoefs), ofK (Parameters.addressOfIndex ehs),
          ofK (Parameters.addressOfIndex epos), ofK (Parameters.addressOfIndex eqp), gen ^ N]
        (Returns [if s.final = 1 then 0 else
          oqChain odd s.base lamInv (fun k ↦ foldRow (lanesOf s.base (rows k)) (K.ofBits (qs k)) rounds) N])
        (oqBound fs name loop N)

theorem OqCompleteDB.toD {fs : String → ℕ} {cert : String → V → ℕ} {name loop : String} {s : Oq}
    {odd : ℕ} (h : OqCompleteDB fs cert name loop s odd) : OqCompleteD fs cert name loop s odd :=
  fun hfit κ Lin N ecap eflags ecoefs ehs epos eqp lamInv rounds hsv eb qs rows sibs hN hrl hhl hst
      hreg hmem ↦
    (h hfit κ Lin N ecap eflags ecoefs ehs epos eqp lamInv rounds hsv eb qs rows sibs hN hrl hhl hst
      hreg hmem).toCompleteAtD

theorem find_name {f : String} {fn : Fn} (h : coreProgram.find? f = some fn) : fn.name = f := by
  unfold Program.find? at h
  have := List.find?_some h
  simpa using this

theorem loop1_true {s : Oq} {odd : ℕ} {wlk loop : String} {fl : Fn}
    (hfl : coreProgram.find? loop = some fl) (hbl : fl.body = oqLoop1T s odd wlk loop) :
    coreProgram.loop loop = true := by
  rw [Program.loop_of_find? hfl, Fn.loop, hbl, find_name hfl]
  simp [oqLoop1T, oqNextT]

theorem loop0_true {s : Oq} {wlk loop : String} {fl : Fn}
    (hfl : coreProgram.find? loop = some fl) (hbl : fl.body = oqLoop0T s wlk loop) :
    coreProgram.loop loop = true := by
  rw [Program.loop_of_find? hfl, Fn.loop, hbl, find_name hfl]
  simp [oqLoop0T, oqNextT]

/-- **A level-0 specialization is `CompleteAtB`.** -/
theorem oqCompleteDB1 (fs : String → ℕ) (cert : String → V → ℕ)
    {s : Oq} (hs : s.RowShape) (hfin : s.FinOk) (hb1 : s.base = 1) (hpd1 : 1 ≤ s.pd)
    (hcd : 2 ≤ s.cd) {odd : ℕ} (hodd : odd ≤ 1) {name loop : String}
    (hE : oqEntryB name s odd = true) (hW : WalkFn (oqWalkOf s) s.pd s.cd) {fm fl : Fn}
    (hfm : coreProgram.find? name = some fm)
    (hpm : fm.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7])
    (hbm : fm.body = oqMainT s odd (oqWalkOf s) loop)
    (hfl : coreProgram.find? loop = some fl) (hpl : fl.params = oqLoopParams)
    (hbl : fl.body = oqLoop1T s odd (oqWalkOf s) loop) : OqCompleteDB fs cert name loop s odd := by
  intro _ κ Lin N ecap eflags ecoefs ehs epos eqp lamInv rounds hsv eb qs rows sibs hN hrl hhl hst
    hreg hmem
  have hQ : oqCount odd s.base N = odd + 2 * N := by simp [oqCount, hb1]
  obtain ⟨hc, hn⟩ := oqWalk_of_entryB hE
  rw [hQ] at hst hreg hmem
  unfold oqBound
  rw [hc, hn, hQ]
  exact oqMain1_completeAtB fs cert κ hs hfin hb1 hpd1 hcd hodd hW hfm hpm hbm hfl hpl hbl
    (loop1_true hfl hbl) hN hrl hhl hst hreg hmem

/-- **A deeper specialization is `CompleteAtB`.** -/
theorem oqCompleteDB0 (fs : String → ℕ) (cert : String → V → ℕ)
    {s : Oq} (hs : s.RowShape) (hfin : s.FinOk) (hb0 : s.base = 0) (hpd1 : 1 ≤ s.pd)
    (hcd : 2 ≤ s.cd) {name loop : String} (hE : oqEntryB name s 0 = true)
    (hW : WalkFn (oqWalkOf s) s.pd s.cd) {fm fl : Fn}
    (hfm : coreProgram.find? name = some fm)
    (hpm : fm.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7])
    (hbm : fm.body = oqMainT s 0 (oqWalkOf s) loop)
    (hfl : coreProgram.find? loop = some fl) (hpl : fl.params = oqLoopParams)
    (hbl : fl.body = oqLoop0T s (oqWalkOf s) loop) : OqCompleteDB fs cert name loop s 0 := by
  intro _ κ Lin N ecap eflags ecoefs ehs epos eqp lamInv rounds hsv eb qs rows sibs hN hrl hhl hst
    hreg hmem
  have hQ : oqCount 0 s.base N = N := by simp [oqCount, hb0]
  obtain ⟨hc, hn⟩ := oqWalk_of_entryB hE
  rw [hQ] at hst hreg hmem
  unfold oqBound
  rw [hc, hn, hQ]
  exact oqMain0_completeAtB fs cert κ hs hfin hb0 hpd1 hcd hW hfm hpm hbm hfl hpl hbl
    (loop0_true hfl hbl) hN hrl hhl hst hreg hmem

end
end LeanVM.Guest.B1
