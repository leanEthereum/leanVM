/-
  LeanVM.Guest.B1.Opening.QueriesPlacedD2

  `opening_queries` is `CompleteAtB`, one statement for every shape.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesPlacedD0

/-!
# `opening_queries`, `CompleteAtB`, one statement

`OqCompleteD fs cert name loop s`: when the frames fit (`OqFits`, trivial), at every cap depth
`cd ≥ 1` and `odd ≤ base`, on the honest data of a call (`N` iterations, the rounds' challenges,
the final coefficients, the queries' positions, rows and siblings, the window runs, the caller's
buffers in `Lin`, the cap and the flags offset to the cap's leaves: `OqStatic`, `OqLinReg`,
`OqLinMem`), the specialization `name` (loop helper `loop`) is `CompleteAtD`, returning the chain
of the queries' folds (or `0` at the final level); `OqCompleteDB`: `CompleteAtB`, by a tree of at
most `oqBound fs name loop N` words (its frame, its chain buffer, its `N` iterations' frames and
its last call's tail frame). `oqCompleteDB1`, `oqCompleteDB0`: from a specialization's bodies.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

/-- The frames fit a specialization's frame runs: its queries place no frame run (the siblings are
hinted into frame cells), so nothing is asked; kept so the statements reading it stand. -/
def OqFits (_fs : String → ℕ) (_cert : String → V → ℕ) (_name _loop : String) (_s : Oq) : Prop :=
  True

/-- **`opening_queries`, the specialization `name` of the shape `s`, is `CompleteAtD`.** -/
def OqCompleteD (fs : String → ℕ) (cert : String → V → ℕ) (name loop : String) (s : Oq) : Prop :=
  OqFits fs cert name loop s →
    ∀ (κ : ℕ) (Lin : Main.Layout) (N cd odd : ℕ) (ecap eflags ecoefs ehs epos eqp : ℕ) (lamInv : E)
      (rounds : List FoldRound) (hsv : List E) (eb qs : ℕ → ℕ) (rows : ℕ → List K)
      (sibs : ℕ → List Digest), 1 ≤ cd → odd ≤ s.base → N + 1 < ordG → rounds.length = s.folds →
      (s.final = 1 → hsv.length = s.nHs) →
      OqStatic s cd rounds hsv qs rows sibs (oqCount odd s.base N) →
      OqLinReg (RegionL Lin) s cd ecap eflags ecoefs ehs epos eqp eb qs (oqCount odd s.base N) →
      (∀ rd, LowDef κ rd → MemL rd Lin →
        OqLinMem rd s cd (ofK (Parameters.addressOfIndex ecap)) (ofK (Parameters.addressOfIndex eflags))
          (ofK (Parameters.addressOfIndex ecoefs)) (ofK (Parameters.addressOfIndex ehs))
          (ofK (Parameters.addressOfIndex epos)) (ofK (Parameters.addressOfIndex eqp)) rounds hsv eb
          qs rows sibs (oqCount odd s.base N)) →
      CompleteAtD fs cert κ name Lin
        [ofK (Parameters.addressOfIndex ecap), ofK (Parameters.addressOfIndex eflags), lamInv,
          ofK (Parameters.addressOfIndex ecoefs), ofK (Parameters.addressOfIndex ehs),
          ofK (Parameters.addressOfIndex epos), ofK (Parameters.addressOfIndex eqp), gen ^ N, gen ^ odd]
        (Returns [if s.final = 1 then 0 else
          oqChain odd s.base lamInv (fun k ↦ foldRow (lanesOf s.base (rows k)) (K.ofBits (qs k)) rounds) N])

/-- `opening_queries`' tree bound: its frame, its chain buffer (`N + 1` cells), its `N`
iterations' frames and its last loop call's tail frame. -/
def oqBound (fs : String → ℕ) (name loop : String) (N : ℕ) : ℕ :=
  fs name + (N + 1) + (N * fs loop + fs (tailKey loop))

/-- **`opening_queries`, the specialization `name` of the shape `s`, is `CompleteAtB`**, by a tree
of at most `oqBound fs name loop N` words: on `[cap, flags, λ⁻¹, coefs, hs, positions, qptrs, g^N,
g^odd]`, the caller's buffers at `g^e…`, the rounds' challenges, the final coefficients and the
queries' witnesses honest (`OqStatic`, `OqLinMem`, in `Lin`'s region by `OqLinReg`), it returns
the chain of the queries' folds (`oqChain`, the caller scales it), or `0` at the final level. -/
def OqCompleteDB (fs : String → ℕ) (cert : String → V → ℕ) (name loop : String) (s : Oq) : Prop :=
  OqFits fs cert name loop s →
    ∀ (κ : ℕ) (Lin : Main.Layout) (N cd odd : ℕ) (ecap eflags ecoefs ehs epos eqp : ℕ) (lamInv : E)
      (rounds : List FoldRound) (hsv : List E) (eb qs : ℕ → ℕ) (rows : ℕ → List K)
      (sibs : ℕ → List Digest), 1 ≤ cd → odd ≤ s.base → N + 1 < ordG → rounds.length = s.folds →
      (s.final = 1 → hsv.length = s.nHs) →
      OqStatic s cd rounds hsv qs rows sibs (oqCount odd s.base N) →
      OqLinReg (RegionL Lin) s cd ecap eflags ecoefs ehs epos eqp eb qs (oqCount odd s.base N) →
      (∀ rd, LowDef κ rd → MemL rd Lin →
        OqLinMem rd s cd (ofK (Parameters.addressOfIndex ecap)) (ofK (Parameters.addressOfIndex eflags))
          (ofK (Parameters.addressOfIndex ecoefs)) (ofK (Parameters.addressOfIndex ehs))
          (ofK (Parameters.addressOfIndex epos)) (ofK (Parameters.addressOfIndex eqp)) rounds hsv eb
          qs rows sibs (oqCount odd s.base N)) →
      CompleteAtB fs cert κ name Lin
        [ofK (Parameters.addressOfIndex ecap), ofK (Parameters.addressOfIndex eflags), lamInv,
          ofK (Parameters.addressOfIndex ecoefs), ofK (Parameters.addressOfIndex ehs),
          ofK (Parameters.addressOfIndex epos), ofK (Parameters.addressOfIndex eqp), gen ^ N, gen ^ odd]
        (Returns [if s.final = 1 then 0 else
          oqChain odd s.base lamInv (fun k ↦ foldRow (lanesOf s.base (rows k)) (K.ofBits (qs k)) rounds) N])
        (oqBound fs name loop N)

theorem OqCompleteDB.toD {fs : String → ℕ} {cert : String → V → ℕ} {name loop : String} {s : Oq}
    (h : OqCompleteDB fs cert name loop s) : OqCompleteD fs cert name loop s :=
  fun hfit κ Lin N cd odd ecap eflags ecoefs ehs epos eqp lamInv rounds hsv eb qs rows sibs hcd hodd hN
      hrl hhl hst hreg hmem ↦
    (h hfit κ Lin N cd odd ecap eflags ecoefs ehs epos eqp lamInv rounds hsv eb qs rows sibs hcd hodd hN
      hrl hhl hst hreg hmem).toCompleteAtD

theorem find_name {f : String} {fn : Fn} (h : coreProgram.find? f = some fn) : fn.name = f := by
  unfold Program.find? at h
  have := List.find?_some h
  simpa using this

theorem loop1_true {s : Oq} {loop : String} {fl : Fn}
    (hfl : coreProgram.find? loop = some fl) (hbl : fl.body = oqLoop1T s loop) :
    coreProgram.loop loop = true := by
  rw [Program.loop_of_find? hfl, Fn.loop, hbl, find_name hfl]
  simp [oqLoop1T, oqNextT]

theorem loop0_true {s : Oq} {loop : String} {fl : Fn}
    (hfl : coreProgram.find? loop = some fl) (hbl : fl.body = oqLoop0T s loop) :
    coreProgram.loop loop = true := by
  rw [Program.loop_of_find? hfl, Fn.loop, hbl, find_name hfl]
  simp [oqLoop0T, oqNextT]

/-- **A level-0 specialization is `CompleteAtB`.** -/
theorem oqCompleteDB1 (fs : String → ℕ) (cert : String → V → ℕ)
    {s : Oq} (hs : s.RowShape) (hfin : s.FinOk) (hb1 : s.base = 1) {name loop : String} {fm fl : Fn}
    (hfm : coreProgram.find? name = some fm) (hpm : fm.params = oqMainParams)
    (hbm : fm.body = oqMainT s loop)
    (hfl : coreProgram.find? loop = some fl) (hpl : fl.params = oqLoopParams)
    (hbl : fl.body = oqLoop1T s loop) : OqCompleteDB fs cert name loop s := by
  intro _ κ Lin N cd odd ecap eflags ecoefs ehs epos eqp lamInv rounds hsv eb qs rows sibs hcd hodd hN
    hrl hhl hst hreg hmem
  have hQ : oqCount odd s.base N = odd + 2 * N := by simp [oqCount, hb1]
  rw [hQ] at hst hreg hmem
  exact oqMain1_completeAtB fs cert κ hs hfin hb1 hcd (by omega) hfm hpm hbm hfl hpl hbl
    (loop1_true hfl hbl) hN hrl hhl hst hreg hmem

/-- **A deeper specialization is `CompleteAtB`.** -/
theorem oqCompleteDB0 (fs : String → ℕ) (cert : String → V → ℕ)
    {s : Oq} (hs : s.RowShape) (hfin : s.FinOk) (hb0 : s.base = 0) {name loop : String} {fm fl : Fn}
    (hfm : coreProgram.find? name = some fm) (hpm : fm.params = oqMainParams)
    (hbm : fm.body = oqMainT s loop)
    (hfl : coreProgram.find? loop = some fl) (hpl : fl.params = oqLoopParams)
    (hbl : fl.body = oqLoop0T s loop) : OqCompleteDB fs cert name loop s := by
  intro _ κ Lin N cd odd ecap eflags ecoefs ehs epos eqp lamInv rounds hsv eb qs rows sibs hcd hodd hN
    hrl hhl hst hreg hmem
  obtain rfl : odd = 0 := by omega
  have hQ : oqCount 0 s.base N = N := by simp [oqCount, hb0]
  rw [hQ] at hst hreg hmem
  exact oqMain0_completeAtB fs cert κ hs hfin hb0 hcd hfm hpm hbm hfl hpl hbl
    (loop0_true hfl hbl) hN hrl hhl hst hreg hmem

end
end LeanVM.Guest.B1
