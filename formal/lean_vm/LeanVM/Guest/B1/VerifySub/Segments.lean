/-
  LeanVM.Guest.B1.VerifySub.Segments

  An honest child's accepted deferring run, cut into the segments `verify_sub`'s callees run: the
  completeness direction of `Sound.lean`'s composition.
-/

module

public import LeanVM.Guest.B1.VerifySub.Ends
public import LeanVM.Guest.B1.Whir.CompleteIface
public import LeanVM.Guest.B1.VerifySub.CompleteSpec
public import LeanVM.Guest.B1.VerifySub.Sizes
public import LeanVM.Protocol.Compile.RunPure

/-!
# The segments of an honest child's run

`readSizes_inv`: the announced sizes' run reads `eOfNat logMem`, the row counts, `eOfNat r` and
returns `layoutOf bytecode logMem rows` (the guest's bytecode of `2^23` words). `announced_eq`: the
run's sizes are `Verifier.announcedLayoutAndRate`'s, so the bound `minChildStackLog ≤ stackLog`
applies. `commitStack_runId`: the stack's commitment reads the root's two words.

`ChildSegs`: on an accepted run, the child's stream is the concatenation of the segments' words
along `flatPre` (Split.lean's `deferredFlat`): the announced sizes, the stack's root, the
out-of-domain sample, the bus's challenges, its GKR, the tables, the Keccak reduction, the ring
switch, then the stacked opening from the batching challenge's state, each a carried run
(`RunsTo`); the opening a `RunsWith` with `open_stacked`'s hypotheses (`NoZeroChallenge`,
`CapsAgree`) and an end passing the terminal's check. `child_segments`: every
child with the per-child hypotheses has them.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Reads -/

/-- A read's run. -/
theorem runId_readE {st : VerifierProgramState} {x : E} {st' : VerifierProgramState}
    (h : runId VerifierProgram.readScalar st = some (x, st')) :
    st.stream = x :: st'.stream ∧ st.sponge.ground = none := by
  obtain ⟨⟨S, P, g⟩, stream, os, R⟩ := st
  match stream, g, h with
  | [], _, h => exact absurd h (by rintro ⟨⟩)
  | _ :: _, some _, h => exact absurd h (by rintro ⟨⟩)
  | y :: ys, none, h =>
    have e : runId VerifierProgram.readScalar ⟨⟨S, P, none⟩, y :: ys, os, R⟩ =
        some (y, ⟨Id.run (Compile.absorb keccakF1600 ⟨S, P, none⟩ y dsObserve), ys, os, R⟩) := rfl
    rw [e, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩

theorem runId_readN : ∀ (n : ℕ) (st : VerifierProgramState) (xs : List E)
    (st' : VerifierProgramState), runId (VerifierProgram.readScalars n) st = some (xs, st') →
      st.stream = xs ++ st'.stream ∧ xs.length = n
  | 0, st, xs, st', h => by
    have e : runId (VerifierProgram.readScalars 0) st = some ([], st) := rfl
    rw [e, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  | n + 1, st, xs, st', h => by
    simp only [VerifierProgram.readScalars, VerifierProgram.bind_eq, VerifierProgram.pure_eq] at h
    obtain ⟨x, s1, h1, h⟩ := runId_bind_some h
    obtain ⟨ys, s2, h2, h⟩ := runId_bind_some h
    have e : runId (VerifierProgram.ret (x :: ys)) s2 = some (x :: ys, s2) := rfl
    rw [e, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨e1, -⟩ := runId_readE h1
    obtain ⟨e2, l2⟩ := runId_readN n s1 ys s2 h2
    exact ⟨by rw [e1, e2, List.cons_append], by simp [l2]⟩

theorem runId_liftOption_bind {α β : Type} {o : Option α} {k : α → VerifierProgram β}
    {st : VerifierProgramState} {r : β × VerifierProgramState}
    (h : runId ((liftOption o).bind k) st = some r) : ∃ a, o = some a ∧ runId (k a) st = some r := by
  cases o with
  | none => exact absurd h (by rintro ⟨⟩)
  | some a => exact ⟨a, rfl, h⟩

theorem runId_ret_inv {α : Type} {a b : α} {st st' : VerifierProgramState}
    (h : runId (VerifierProgram.ret a) st = some (b, st')) : b = a ∧ st' = st := by
  have e : runId (VerifierProgram.ret a) st = some (a, st) := rfl
  rw [e, Option.some.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.symm⟩

theorem word_eOfNat_of {v : E} (h1 : v.limb 1 = 0) :
    v = eOfNat (kToNat (v.limb 0)) := by
  apply E.ext
  intro i
  fin_cases i
  · simp [eOfNat, ofBits_kToNat]
  · simp [eOfNat, h1]

/-- **The announced sizes' run**: the words `eOfNat logMem`, the row counts, `eOfNat r`, and the
layout `layoutOf bytecode logMem rows`. -/
theorem readSizes_inv {bytecode : List K} (hbl : bytecode.length = 2 ^ 23)
    {st : VerifierProgramState} {L : Layout} {r : ℕ} {st' : VerifierProgramState}
    (h : runId (readAnnouncedSizes bytecode) st = some ((L, r), st')) :
    ∃ (logMem : ℕ) (rowsN : List ℕ),
      st.stream = (eOfNat logMem :: rowsN.map eOfNat ++ [eOfNat r]) ++ st'.stream ∧
      L = Tables.layoutOf bytecode logMem rowsN ∧ 16 ≤ logMem ∧ logMem ≤ 32 ∧
      rowsN.length = 6 ∧ (∀ n ∈ rowsN, n ≤ 2 ^ 32) ∧ 1 ≤ r ∧ r ≤ 4 ∧
      Whir.minLogStack ≤ L.stackLog ∧ L.stackLog ≤ Whir.maxLogStack := by
  unfold readAnnouncedSizes at h
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq] at h
  obtain ⟨xs, s1, h1, h⟩ := runId_bind_some h
  obtain ⟨hs1, hl⟩ := runId_readN _ _ _ _ h1
  obtain ⟨hall, h⟩ := runId_require_bind h
  obtain ⟨hr, h⟩ := runId_require_bind h
  obtain ⟨L', hL', h⟩ := runId_liftOption_bind h
  obtain ⟨hst, h⟩ := runId_require_bind h
  obtain ⟨he, rfl⟩ := runId_ret_inv h
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  have hl8 : xs.length = 8 := by rw [hl]; rfl
  match xs, hl8, hall, hs1, hL', hr with
  | [v0, v1, v2, v3, v4, v5, v6, v7], _, hall, hs1, hL', hr =>
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
      at hall
    obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩ := hall
    set rowsN := [kToNat (v1.limb 0), kToNat (v2.limb 0), kToNat (v3.limb 0), kToNat (v4.limb 0),
      kToNat (v5.limb 0), kToNat (v6.limb 0)] with hrowsN
    have hrows : ((([v0, v1, v2, v3, v4, v5, v6, v7].drop 1).take tables.length).map
        fun value ↦ kToNat (value.limb 0)) = rowsN := rfl
    have e7 : [v0, v1, v2, v3, v4, v5, v6, v7].getLastD 0 = v7 := rfl
    simp only [List.headD_cons, hrows, e7] at hL' hr hst ⊢
    have hcond := hL'
    unfold buildLayout at hcond
    rw [hbl, show log2Strict (2 ^ 23) = some 23 by decide] at hcond
    simp only at hcond
    split at hcond
    · rename_i hc
      obtain ⟨-, h16, h32, hall32, -, hlen⟩ := hc
      have hlen' : rowsN.length = 6 := by rw [hlen]; rfl
      have hr32 : ∀ n ∈ rowsN, n ≤ 2 ^ 32 := by simpa using hall32
      have hLe := buildLayout_eq hbl h16 h32 hlen' hr32
      rw [hL'] at hLe
      obtain rfl := Option.some.inj hLe
      refine ⟨kToNat (v0.limb 0), rowsN, ?_, rfl, h16, h32, hlen', hr32, hr.1, hr.2, hst.1, hst.2⟩
      rw [hs1, ← word_eOfNat_of a0, ← word_eOfNat_of a7]
      simp only [hrowsN, List.map_cons, List.map_nil, ← word_eOfNat_of a1,
        ← word_eOfNat_of a2, ← word_eOfNat_of a3, ← word_eOfNat_of a4,
        ← word_eOfNat_of a5, ← word_eOfNat_of a6]
      rfl
    · simp at hcond

/-! ## The announced sizes are `Verifier.announcedLayoutAndRate`'s -/

/-- Only reads (the run is a parse of the stream). -/
def ReadOnlyA {α : Type} : VerifierProgram α → Prop
  | .ret _ => True
  | .fail => True
  | .read k => ∀ x, ReadOnlyA (k x)
  | .sample _ => False
  | .grind _ _ => False
  | .commit _ _ _ => False
  | .query _ _ _ => False

/-- **Only reads.** Irreducible, as `NoCommit`. -/
@[irreducible] def ReadOnly {α : Type} (p : VerifierProgram α) : Prop := ReadOnlyA p

theorem readOnly_iff {α : Type} (p : VerifierProgram α) : ReadOnly p ↔ ReadOnlyA p := by
  unfold ReadOnly; rfl

theorem ReadOnly.bind {α β : Type} {p : VerifierProgram α} {f : α → VerifierProgram β}
    (hp : ReadOnly p) (hf : ∀ a, ReadOnly (f a)) : ReadOnly (p.bind f) := by
  rw [readOnly_iff] at hp ⊢
  have hf' : ∀ a, ReadOnlyA (f a) := fun a ↦ (readOnly_iff _).1 (hf a)
  clear hf
  induction p with
  | ret a => exact hf' a
  | fail => trivial
  | read k ih => exact fun x ↦ ih x (hp x)
  | sample _ _ => exact hp.elim
  | grind _ _ _ => exact hp.elim
  | commit _ _ _ _ => exact hp.elim
  | query _ _ _ _ => exact hp.elim

theorem readOnly_ret {α : Type} (a : α) : ReadOnly (VerifierProgram.ret a) :=
  (readOnly_iff _).2 trivial

theorem readOnly_fail {α : Type} : ReadOnly (VerifierProgram.fail : VerifierProgram α) :=
  (readOnly_iff _).2 trivial

theorem readOnly_readN : ∀ n, ReadOnly (VerifierProgram.readScalars n)
  | 0 => readOnly_ret _
  | n + 1 => by
    simp only [VerifierProgram.readScalars, VerifierProgram.bind_eq, VerifierProgram.pure_eq]
    refine ReadOnly.bind ((readOnly_iff _).2 fun _ ↦ trivial) fun _ ↦ ?_
    exact ReadOnly.bind (readOnly_readN n) fun _ ↦ readOnly_ret _

theorem readOnly_require (c : Prop) [Decidable c] : ReadOnly (VerifierProgram.require c) := by
  unfold VerifierProgram.require
  split
  · exact readOnly_ret _
  · exact readOnly_fail

theorem readOnly_liftOption {α : Type} (o : Option α) : ReadOnly (Verifier.liftOption o) := by
  cases o
  · exact readOnly_fail
  · exact readOnly_ret _

theorem readOnly_readSizes (bytecode : List K) : ReadOnly (readAnnouncedSizes bytecode) := by
  unfold readAnnouncedSizes
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
  refine ReadOnly.bind (readOnly_readN _) fun _ ↦ ?_
  refine ReadOnly.bind (readOnly_require _) fun _ ↦ ?_
  refine ReadOnly.bind (readOnly_require _) fun _ ↦ ?_
  refine ReadOnly.bind (readOnly_liftOption _) fun _ ↦ ?_
  refine ReadOnly.bind (readOnly_require _) fun _ ↦ ?_
  exact readOnly_ret _

/-- A run that only reads returns what the stream gives, whatever the hashes and the sponge with
nothing waiting. -/
theorem ReadOnlyA.run_eq {α : Type} (p : VerifierProgram α) : ReadOnlyA p →
    ∀ (H H' : Bytes → Id Digest) (F F' : KeccakState → Id KeccakState) (sp sp' : Sponge),
      sp.ground = none → sp'.ground = none → ∀ (T : List E)
      (O O' : List (List Opening)) (R R' : List (Digest × ℕ × ℕ)),
      (Id.run (Compile.runWithHash (m := Id) H F p ⟨sp, T, O, R⟩)).map (·.1) =
        (Id.run (Compile.runWithHash (m := Id) H' F' p ⟨sp', T, O', R'⟩)).map (·.1) := by
  induction p with
  | ret a => intros; rfl
  | fail => intros; rfl
  | read k ih =>
    intro hp H H' F F' sp sp' hg hg' T O O' R R'
    obtain ⟨S, P, g⟩ := sp
    obtain ⟨S', P', g'⟩ := sp'
    simp only at hg hg'
    subst hg hg'
    cases T with
    | nil => rfl
    | cons x xs =>
      exact ih x (hp x) H H' F F' _ _ (absorb_ground _ _ _ _) (absorb_ground _ _ _ _) xs O O' R R'
  | sample _ _ => intro hp; exact hp.elim
  | grind _ _ _ => intro hp; exact hp.elim
  | commit _ _ _ _ => intro hp; exact hp.elim
  | query _ _ _ _ => intro hp; exact hp.elim

/-- **The run's sizes are `Verifier.announcedLayoutAndRate`'s.** -/
theorem announced_eq {bytecode : List K} {sp : Sponge} (hg : sp.ground = none) {T : List E}
    {O : List (List Opening)} {R : List (Digest × ℕ × ℕ)} {L : Layout} {r : ℕ}
    {st' : VerifierProgramState}
    (h : runId (readAnnouncedSizes bytecode) ⟨sp, T, O, R⟩ = some ((L, r), st')) :
    Verifier.announcedLayoutAndRate bytecode T = some (L, r) := by
  have e := ReadOnlyA.run_eq _ ((readOnly_iff _).1 (readOnly_readSizes bytecode))
    (fun _ ↦ default) keccak256 (fun _ ↦ default) keccakF1600 ⟨default, [], none⟩ sp rfl hg T [] O
    [] R
  unfold Verifier.announcedLayoutAndRate
  rw [runPure_eq_withHash, e]
  change (runId (readAnnouncedSizes bytecode) ⟨sp, T, O, R⟩).map (·.1) = _
  rw [h]
  rfl

/-! ## The stack's root -/

/-- **The stack's commitment**: two words, the root their digest, absorbed. -/
theorem commitStack_runId {μ r : ℕ} {st : VerifierProgramState} {u : Unit}
    {st' : VerifierProgramState} (h : runId (commitStack μ r) st = some (u, st')) :
    ∃ x0 x1 : E, st.stream = x0 :: x1 :: st'.stream ∧ st.sponge.ground = none ∧
      st'.sponge = Id.run (Compile.absorb keccakF1600
        (Id.run (Compile.absorb keccakF1600 st.sponge x0 dsObserve)) x1 dsObserve) ∧
      st'.roots = st.roots ++ [(digestFromHalves (x0, x1), Whir.stackShape μ r)] ∧
      st'.openings = st.openings := by
  cases hc : Whir.ladder μ r with
  | none =>
    unfold commitStack at h
    rw [hc] at h
    exact absurd h (by rintro ⟨⟩)
  | some cfg =>
    cases cfg with
    | nil =>
      unfold commitStack at h
      rw [hc] at h
      exact absurd h (by rintro ⟨⟩)
    | cons level rest =>
      rw [Whir.commitStack_eq hc] at h
      obtain ⟨⟨S, P, g⟩, stream, os, R⟩ := st
      match stream, g, h with
      | [], _, h => exact absurd h (by rintro ⟨⟩)
      | [_], _, h => exact absurd h (by rintro ⟨⟩)
      | _ :: _ :: _, some _, h => exact absurd h (by rintro ⟨⟩)
      | x0 :: x1 :: xs, none, h =>
        have e : runId (VerifierProgram.readCommitment (Whir.stackShape μ r).1
            (Whir.stackShape μ r).2) ⟨⟨S, P, none⟩, x0 :: x1 :: xs, os, R⟩ =
            some ((), ⟨Id.run (Compile.absorb keccakF1600 (Id.run (Compile.absorb keccakF1600
              ⟨S, P, none⟩ x0 dsObserve)) x1 dsObserve), xs, os,
              R ++ [(digestFromHalves (x0, x1), (Whir.stackShape μ r).1,
                (Whir.stackShape μ r).2)]⟩) := rfl
        rw [e, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact ⟨x0, x1, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The segments -/

/-- The carried sponge the child's run starts from. -/
def seedFs (seed pi : Digest) : Fs := ⟨capOf (keccakF1600 (seedInput seed pi)), []⟩

/-- The announced words: the memory's log-size, the six row counts, the rate. -/
def sizeWords (logMem : ℕ) (rowsN : List ℕ) (rate : ℕ) : List E :=
  eOfNat logMem :: rowsN.map eOfNat ++ [eOfNat rate]

/-- **An honest child's accepted run, cut into `verify_sub`'s segments** (`pi` the child's
statement's digest): the announced sizes, the stack's root, the out-of-domain sample, the bus's
challenges, its GKR, the tables, the Keccak reduction, the ring switch, then the stacked opening
from the batching challenge's state. -/
structure ChildSegs (bytecode : List K) (seed : Digest) (c : Node.Child) : Type where
  /-- The memory's log-size, the six tables' row counts, the rate. -/
  logMem : ℕ
  rowsN : List ℕ
  rate : ℕ
  /-- The layout. -/
  layout : Layout
  hlayout : layout = Tables.layoutOf bytecode logMem rowsN
  h16 : 16 ≤ logMem
  h32 : logMem ≤ 32
  hrowsL : rowsN.length = 6
  hrows32 : ∀ n ∈ rowsN, n ≤ 2 ^ 32
  hr1 : 1 ≤ rate
  hr4 : rate ≤ 4
  hmu22 : 22 ≤ layout.stackLog
  hmu28 : layout.stackLog ≤ 28
  /-- The announced sizes. -/
  s1 : Fs
  runS : RunsTo (readAnnouncedSizes bytecode) (seedFs seed (Node.statementDigest seed c.statement))
    (sizeWords logMem rowsN rate) (layout, rate) s1
  /-- The stack's root. -/
  x0 : E
  x1 : E
  root : Digest
  hroot : digestFromHalves (x0, x1) = root
  /-- The out-of-domain sample. -/
  xsO : List E
  ood : StackClaim
  s2 : Fs
  runO : RunsTo (readOod layout.stackLog) ((s1.absorb x0 dsObserve).absorb x1 dsObserve) xsO ood s2
  /-- The bus's depth, challenges and GKR. -/
  hdepth : busDepth layout < 64
  xsB : List E
  wb : List E × E
  s3 : Fs
  runB : RunsTo (busChallenges (busDepth layout)) s2 xsB wb s3
  xsG : List E
  rG : E × List E × List E
  s4 : Fs
  runG : RunsTo (Tables.gkrPhase (busDepth layout)) s3 xsG rG s4
  /-- The bus's rest, the tables, the public input. -/
  xsT : List E
  bus : BusResult
  claims : List ColumnClaim
  s5 : Fs
  runT : RunsTo (Tables.tablesSeg (claimedBytecodeValue c.freshClaim) layout
    (Node.statementDigest seed c.statement) wb.1 wb.2 rG.2.1 rG.2.2) s4 xsT (bus, claims) s5
  /-- The output lanes' check and the Keccak reduction. -/
  xsK : List E
  kc : List ColumnClaim × List E × List E
  s6 : Fs
  runK : RunsTo (keccakPhaseClaims layout claims) s5 xsK kc s6
  /-- The ring switch. -/
  xsR : List E
  rs : E × (List E → E)
  s7 : Fs
  runR : RunsTo (ringSwitch kc.2.1 kc.2.2) s6 xsR rs s7
  /-- The stacked opening's claims. -/
  hcl : (stackClaims layout kc.1 rs.1 rs.2 ood).length ≤ maxStackedClaims
  /-- The stacked opening: from the batching challenge's state, on the stream's rest and the
  proof's openings, with no zero challenge or vanishing combiner and openings agreeing in the
  caps, to an end passing the terminal's check. -/
  xsW : List E
  w : Whir.WhirEnd
  s' : Fs
  roots' : List (Digest × ℕ × ℕ)
  runW : Whir.RunsWith (Whir.whirOpen layout.stackLog rate
    (batchTarget (stackClaims layout kc.1 rs.1 rs.2 ood) s7.squeeze.1))
    ⟨capOf s7.perm, []⟩ xsW c.proof.openings [(root, Whir.stackShape layout.stackLog rate)] w s'
    roots'
  nzW : Whir.NoZeroChallenge layout.stackLog rate
    (batchTarget (stackClaims layout kc.1 rs.1 rs.2 ood) s7.squeeze.1) s7.perm xsW
    c.proof.openings root
  capsW : Whir.CapsAgree layout.stackLog rate
    (batchTarget (stackClaims layout kc.1 rs.1 rs.2 ood) s7.squeeze.1) s7.perm xsW
    c.proof.openings root
  acc : w.Accepts (batchBasis (stackClaims layout kc.1 rs.1 rs.2 ood) s7.squeeze.1)
  /-- The stream is the segments' words. -/
  hstream : c.proof.stream = sizeWords logMem rowsN rate ++ [x0, x1] ++ xsO ++ xsB ++ xsG ++
    xsT ++ xsK ++ xsR ++ xsW
  /-- The announced sizes are `Verifier.announcedLayoutAndRate`'s. -/
  hann : Verifier.announcedLayoutAndRate bytecode c.proof.stream = some (layout, rate)

/-! ## Cutting the run -/

/-- A segment's carried run, from a sponge with nothing waiting to one with nothing waiting. -/
theorem seg_runsTo {α : Type} {p : VerifierProgram α} (hp : NoCommit p) (he : EndsClear p)
    {st : VerifierProgramState} {a : α} {st' : VerifierProgramState} (hg : st.sponge.ground = none)
    (h : runId p st = some (a, st')) :
    ∃ xs, st.stream = xs ++ st'.stream ∧ st'.openings = st.openings ∧ st'.roots = st.roots ∧
      st'.sponge.ground = none ∧
      RunsTo p (Tables.fsOfT st.sponge) xs a (Tables.fsOfT st'.sponge) := by
  have hs : Tables.TCar (Tables.fsOfT st.sponge) none st.sponge := ⟨rfl, rfl, hg⟩
  obtain ⟨sp, T, O, R⟩ := st
  obtain ⟨xs, hT, hO, hR, hG⟩ := runsG_of_runId hp hs h
  have hg' := he _ a st' hg h
  rw [hg'] at hG
  exact ⟨xs, hT, hO, hR, hg', hG.toRunsTo⟩

/-- The carried sponge of a Spec sponge with nothing waiting carries it. -/
theorem carries_fsOfT {sp : Sponge} (hg : sp.ground = none) : (Tables.fsOfT sp).Carries sp :=
  ⟨rfl, rfl, hg⟩

/-- Two carried sponges of one Spec sponge are one. -/
theorem fs_eq_of_carries {s : Fs} {sp : Sponge} (h : s.Carries sp) : s = Tables.fsOfT sp :=
  (Tables.eq_fsOfT h).1

/-- **An honest child's run, in segments** (the per-child hypotheses; the guest's bytecode of
`2^23` words). -/
theorem child_segments {bytecode : List K} (hbl : bytecode.length = 2 ^ 23) (seed : Digest)
    (c : Node.Child)
    (hmu : ∀ layout r, Verifier.announcedLayoutAndRate bytecode c.proof.stream = some (layout, r) →
      Coverage.minChildStackLog ≤ layout.stackLog)
    (hrz : Limits.verifyDeferredRefusingZero bytecode seed (Node.statementDigest seed c.statement)
      c.freshClaim c.proof = true)
    (hcaps : ∀ b ∈ Limits.queryStepsOf
      (deferringVerifierProgram c.freshClaim bytecode (Node.statementDigest seed c.statement))
      (Coverage.childVerifierStart seed c), Limits.OpeningsAgree b.1 b.2) :
    Nonempty (ChildSegs bytecode seed c) := by
  obtain ⟨q, stq, t, hpre, hop, ht1, ht2⟩ := accept_rz hrz
  have hpre0 := hpre
  unfold flatPre at hpre
  -- the announced sizes
  obtain ⟨ls, st1, hA, h⟩ := runId_bind_some hpre
  obtain ⟨L, r⟩ := ls
  obtain ⟨logMem, rowsN, hsA, hL, h16, h32, hrowsL, hrows32, hr1, hr4, -, hst28⟩ :=
    readSizes_inv hbl hA
  obtain ⟨xs1, hxs1, hO1, hR1, hg1, runS⟩ :=
    seg_runsTo (noCommit_readSizes _) (endsClear_readSizes _) rfl hA
  have exs1 : xs1 = sizeWords logMem rowsN r := by
    have := hsA.symm.trans hxs1
    exact (List.append_cancel_right this).symm
  subst exs1
  have hann : Verifier.announcedLayoutAndRate bytecode c.proof.stream = some (L, r) :=
    announced_eq (sp := ⟨keccakF1600 (seedInput seed (Node.statementDigest seed c.statement)), [],
      none⟩) rfl hA
  have hmu22 : 22 ≤ L.stackLog := hmu L r hann
  -- the stack's root
  obtain ⟨u, st2, hB, h⟩ := runId_bind_some h
  obtain ⟨x0, x1, hsB, -, hspB, hrB, hoB⟩ := commitStack_runId hB
  have hg2 : st2.sponge.ground = none := by
    rw [hspB, absorb_ground, absorb_ground]; exact hg1
  have hc2 : ((Tables.fsOfT st1.sponge).absorb x0 dsObserve).absorb x1 dsObserve =
      Tables.fsOfT st2.sponge := by
    have := carries_absorb (carries_absorb (carries_fsOfT hg1) x0 dsObserve) x1 dsObserve
    rw [← hspB] at this
    exact fs_eq_of_carries this
  -- the out-of-domain sample
  obtain ⟨ood, st3, hC, h⟩ := runId_bind_some h
  obtain ⟨xsO, hxsO, hO3, hR3, hg3, runO⟩ :=
    seg_runsTo (noCommit_readOod _) (endsAny_readOod _).clear hg2 hC
  -- the bus's depth
  obtain ⟨hdepth, h⟩ := runId_require_bind h
  -- the bus's challenges
  obtain ⟨wb, st4, hD, h⟩ := runId_bind_some h
  obtain ⟨xsB, hxsB, hO4, hR4, hg4, runB⟩ :=
    seg_runsTo (noCommit_busChallenges _) (endsAny_busChallenges _).clear hg3 hD
  -- the bus's GKR
  obtain ⟨rG, st5, hE, h⟩ := runId_bind_some h
  obtain ⟨xsG, hxsG, hO5, hR5, hg5, runG⟩ :=
    seg_runsTo (noCommit_gkrPhase _) (endsClear_gkrPhase _) hg4 hE
  -- the tables
  obtain ⟨bc, st6, hF, h⟩ := runId_bind_some h
  obtain ⟨bus, claims⟩ := bc
  obtain ⟨xsT, hxsT, hO6, hR6, hg6, runT⟩ :=
    seg_runsTo (noCommit_tablesSeg _ _ _ _ _ _ _) (endsAny_tablesSeg _ _ _ _ _ _ _).clear hg5 hF
  -- the Keccak reduction
  obtain ⟨kc, st7, hG, h⟩ := runId_bind_some h
  obtain ⟨xsK, hxsK, hO7, hR7, hg7, runK⟩ :=
    seg_runsTo (noCommit_keccakPhaseClaims _ _) (endsAny_keccakPhaseClaims _ _).clear hg6 hG
  -- the ring switch
  obtain ⟨rs, st8, hH, h⟩ := runId_bind_some h
  obtain ⟨xsR, hxsR, hO8, hR8, hg8, runR⟩ :=
    seg_runsTo (noCommit_ringSwitch _ _) (endsAny_ringSwitch _ _).clear hg7 hH
  obtain ⟨hq, hst⟩ := runId_ret_inv h
  subst q
  subst stq
  -- the stacked opening
  simp only at hop
  obtain ⟨hcl, w, hW, hWz, hacc⟩ := opening_rz hop
  set s7 := Tables.fsOfT st8.sponge with hs7
  have hc8 : s7.Carries st8.sponge := carries_fsOfT hg8
  obtain ⟨hlam, -⟩ := carries_squeeze hc8
  have hsq : Id.run (squeeze keccakF1600 st8.sponge) = (s7.squeeze.1, ⟨s7.perm, [], none⟩) := by
    rw [Keccak.squeeze_id st8.sponge hg8, perm_eq hc8]
    rfl
  rw [hsq] at hW hWz hacc
  have hcS : (⟨capOf s7.perm, []⟩ : Fs).Carries ⟨s7.perm, [], none⟩ := ⟨rfl, rfl, rfl⟩
  have hO : st8.openings = c.proof.openings := by
    rw [hO8, hO7, hO6, hO5, hO4, hO3, hoB, hO1]; rfl
  have hR : st8.roots = [(digestFromHalves (x0, x1), Whir.stackShape L.stackLog r)] := by
    rw [hR8, hR7, hR6, hR5, hR4, hR3, hrB, hR1]; rfl
  obtain ⟨sp8, stream8, os8, roots8⟩ := st8
  simp only at hO hR hW hWz hxsR
  subst hO hR
  have runW := runsWith_of_runId hcS hW ht1 ht2 (endsAny_whirOpen _ _ _ _ _ _ hW)
  have nzW := runsWith_of_runId hcS hWz ht1 ht2
    (endsAny_rz (endsAny_whirOpen _ _ _) _ _ _ hWz)
  -- the caps
  have capsW : Whir.CapsAgree L.stackLog r
      (batchTarget (stackClaims L kc.1 rs.1 rs.2 ood) s7.squeeze.1) s7.perm stream8
      c.proof.openings (digestFromHalves (x0, x1)) := by
    intro b hb
    apply hcaps
    have e0 : Coverage.childVerifierStart seed c =
        deferStart seed (Node.statementDigest seed c.statement) c.proof := rfl
    have hvs := runId_of_rz _ _ _ hop
    rw [e0, deferred_pre, queryStepsOf_bind _ _ _ _ _ hpre0]
    refine List.mem_append_right _ ?_
    rw [queryStepsOf_bind _ _ _ _ _ hvs]
    refine List.mem_append_left _ ?_
    have hreq : runId (VerifierProgram.require
        ((stackClaims L kc.1 rs.1 rs.2 ood).length ≤ maxStackedClaims))
        ⟨sp8, stream8, c.proof.openings, [(digestFromHalves (x0, x1),
          Whir.stackShape L.stackLog r)]⟩ =
        some ((), ⟨sp8, stream8, c.proof.openings, [(digestFromHalves (x0, x1),
          Whir.stackShape L.stackLog r)]⟩) := by
      unfold VerifierProgram.require
      simp only [hcl, ↓reduceIte]
      rfl
    rw [verifyStackedOpening_split, queryStepsOf_bind _ _ _ _ _ hreq]
    refine List.mem_append_right _ ?_
    change b ∈ Limits.queryStepsOf ((Whir.whirOpen L.stackLog r (batchTarget
      (stackClaims L kc.1 rs.1 rs.2 ood) (Id.run (squeeze keccakF1600 sp8)).1)).bind _)
      ⟨(Id.run (squeeze keccakF1600 sp8)).2, stream8, c.proof.openings, _⟩
    rw [hsq, queryStepsOf_bind _ _ _ _ _ hW]
    exact List.mem_append_left _ hb
  refine ⟨⟨logMem, rowsN, r, L, hL, h16, h32, hrowsL, hrows32, hr1, hr4, hmu22, hst28,
    Tables.fsOfT st1.sponge, runS, x0, x1, _, rfl, xsO, ood, Tables.fsOfT st3.sponge,
    hc2 ▸ runO, hdepth, xsB, wb, _, runB, xsG, rG, _, runG, xsT, bus, claims, _, runT, xsK, kc, _,
    runK, xsR, rs, s7, runR, hcl, stream8, w, _, _, runW, ⟨w, _, _, nzW⟩,
    capsW, hacc, ?_, hann⟩⟩
  have h0 : c.proof.stream = (deferStart seed (Node.statementDigest seed c.statement)
    c.proof).stream := rfl
  rw [h0, hxs1, hsB, hxsO, hxsB, hxsG, hxsT, hxsK, hxsR]
  simp only [List.append_assoc, List.cons_append, List.nil_append, sizeWords]

end
end LeanVM.Guest.B1.VerifySub
