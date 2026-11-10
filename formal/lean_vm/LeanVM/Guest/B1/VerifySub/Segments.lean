/-
  LeanVM.Guest.B1.VerifySub.Segments

  An honest child's accepted deferring run, cut into the segments `verify_sub`'s callees run: the
  completeness direction of `Sound.lean`'s composition.
-/

module

public import LeanVM.Protocol.Verifier.Claims
public import LeanVM.Guest.B1.VerifySub.NZBridge
public import LeanVM.Guest.B1.VerifySub.CompleteSpec
public import LeanVM.Guest.B1.VerifySub.Sizes
public import LeanVM.Protocol.WithHashBridge
public import LeanVM.Protocol.WithHash
public import LeanVM.Guest.AcceptableChild

/-!
# The segments of an honest child's run

`flatPre`: the deferring verifier's prefix grouped as `verify_sub` runs it (Split.lean's
`deferredFlat` up to the batching challenge): the announced sizes, the stack's root, the bus
challenges, the bus's GKR, `tablesSeg`, the lanes' check, `keccakSeg`, the ring map's other five
challenges; `specPre_flat`: it is `specPre`.

`runsTo_of_runF`: a carried run of a program without commitments is a `RunsTo` on the words it
reads. `readSizes_inv`: the announced sizes' run reads `eOfNat logMem`, the row counts, `eOfNat r`
and returns `layoutOf bytecode logMem rows` (the guest's bytecode of `2^23` words). `announced_eq`:
the run's sizes are `Verifier.announcedLayoutAndRate`'s, so G7's bound `minChildStackLog ≤ stackLog`
applies.

`child_segments`: on G7's per-child hypotheses, the child's stream is the concatenation of the
segments' words, each segment a carried run (`ChildSegs`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The prefix, grouped as `verify_sub` runs it -/

/-- **The prefix, grouped as `verify_sub` runs it.** -/
def flatPre (c : BytecodeClaim) (bytecode : List K) (pi : Digest) :
    VerifierProgram (Layout × ℕ × List StackClaim) :=
  (readAnnouncedSizes bytecode).bind fun ls ↦
  (commitStack ls.1.stackLog ls.2).bind fun _ ↦
  (VerifierProgram.sampleChallenges busBits).bind fun alphas ↦
  VerifierProgram.sampleChallenge.bind fun beta ↦
  (Tables.gkrPhase (busLayout [0, ls.1.logMemory, ls.1.logBytecode] ls.1.push).depth).bind fun r ↦
  (Tables.tablesSeg (claimedBytecodeValue c) ls.1 pi alphas beta r.2.1 r.2.2).bind fun bc ↦
  (VerifierProgram.require ((lanesOf bc.2).map (·.column) = keccakOutputColumns ∧
    ∀ c ∈ lanesOf bc.2, c.point = ((lanesOf bc.2).headD default).point)).bind fun _ ↦
  (keccakSeg (ls.1.tableLogHeights.getD opKeccak 0) ((lanesOf bc.2).headD default).point
    ((lanesOf bc.2).map (·.value))).bind fun km ↦
  (VerifierProgram.sampleChallenges 5).bind fun chs ↦
  VerifierProgram.ret (ls.1, ls.2, stackClaims ls.1 bc.2 km.1.1 km.1.2.1 km.1.2.2 (km.2 :: chs))

theorem specPre_flat (c : BytecodeClaim) (bytecode : List K) (pi : Digest) :
    specPre (claimedBytecodeValue c) bytecode pi = flatPre c bytecode pi := by
  simp only [specPre, flatPre, restClaims, VerifierProgram.bind_eq, VerifierProgram.pure_eq,
      VerifierProgram.bind_assoc]
  refine congrArg _ (funext fun ls ↦ congrArg _ (funext fun _ ↦ ?_))
  rw [verifyBusBalance_split]
  simp only [Tables.tablesSeg, VerifierProgram.bind_assoc, VerifierProgram.bind_eq,
      VerifierProgram.pure_eq, VerifierProgram.ret_bind]
  refine congrArg _ (funext fun alphas ↦ congrArg _ (funext fun beta ↦ congrArg _ (funext fun r ↦
    congrArg _ (funext fun bus ↦ congrArg _ (funext fun cl ↦ congrArg _ (funext fun pc ↦ ?_))))))
  simp only [keccakPhaseClaims, lanesOf, VerifierProgram.bind_eq, VerifierProgram.pure_eq,
      VerifierProgram.bind_assoc, VerifierProgram.ret_bind]
  refine congrArg _ (funext fun _ ↦ ?_)
  simp only [keccakSeg, VerifierProgram.bind_eq, VerifierProgram.pure_eq,
      VerifierProgram.bind_assoc, VerifierProgram.ret_bind]
  refine congrArg _ (funext fun kr ↦ ?_)
  simp only [ringSwitch, VerifierProgram.bind_eq, VerifierProgram.pure_eq,
      VerifierProgram.bind_assoc, VerifierProgram.ret_bind]
  rw [show ringMapShifts.length = 5 + 1 from rfl, VerifierProgram.sampleChallenges]
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq, VerifierProgram.bind_assoc,
      VerifierProgram.ret_bind]
  refine congrArg _ (funext fun m ↦ congrArg _ (funext fun chs ↦ ?_))
  rfl


/-! ## Carried runs without commitments are `RunsTo` -/

/-- The deployed run from a carried one, on a sponge the start carries. -/
theorem runId_of_runF {α : Type} {p : VerifierProgram α} {st : Whir.FSt} {a : α} {st' : Whir.FSt}
    (h : Whir.runF p st = some (a, st')) {sp : Sponge} (hs : st.sponge.Carries sp) :
    ∃ sp', st'.sponge.Carries sp' ∧
      runId p ⟨sp, st.stream, st.openings, st.roots⟩ =
        some (a, ⟨sp', st'.stream, st'.openings, st'.roots⟩) := by
  rw [runF_eq_runT] at h
  obtain ⟨⟨a', t⟩, ht, he⟩ := Option.map_eq_some_iff.1 h
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact Tables.runId_of_runT p (toT st) sp hs _ t ht

/-- A carried run keeps the words past what it reads, on any rest. -/
theorem runF_frame {α : Type} {p : VerifierProgram α} {st : Whir.FSt} {a : α} {st' : Whir.FSt}
    (h : Whir.runF p st = some (a, st')) :
    ∃ pre opre, st.stream = pre ++ st'.stream ∧ st.openings = opre ++ st'.openings ∧
      ∀ zs orest, Whir.runF p { st with stream := pre ++ zs, openings := opre ++ orest } =
        some (a, { st' with stream := zs, openings := orest }) := by
  rw [runF_eq_runT] at h
  obtain ⟨⟨a', t⟩, ht, he⟩ := Option.map_eq_some_iff.1 h
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  obtain ⟨pre, opre, hs, ho, hf⟩ := Tables.runT_frame p (toT st) a' t ht
  refine ⟨pre, opre, hs, ho, fun zs orest ↦ ?_⟩
  rw [runF_eq_runT]
  have e := hf zs orest
  simp only [toT] at e ⊢
  rw [e]
  rfl

theorem NoCommitA.runF_any {α : Type} (p : VerifierProgram α) : NoCommitA p → ∀ (s : Fs) (T :
    List E)
    (O : List (List Opening)) (R : List (Digest × ℕ × ℕ)) (a : α) (st' : Whir.FSt),
    Whir.runF p ⟨s, T, O, R⟩ = some (a, st') →
      ∀ O2 R2, Whir.runF p ⟨s, T, O2, R2⟩ = some (a, { st' with openings := O2, roots := R2 }) := by
  induction p with
  | ret b =>
    intro _ s T O R a st' h O2 R2
    simp only [Whir.runF, Option.some.injEq, Prod.mk.injEq] at h ⊢
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  | fail => intro _ s T O R a st' h; simp [Whir.runF] at h
  | read k ih =>
    intro hp s T O R a st' h O2 R2
    cases T with
    | nil => simp [Whir.runF] at h
    | cons x xs =>
      simp only [Whir.runF] at h ⊢
      exact ih x (hp x) _ xs O R a st' h O2 R2
  | sample k ih =>
    intro hp s T O R a st' h O2 R2
    exact ih _ (hp _) _ T O R a st' h O2 R2
  | grind b k ih =>
    intro hp s T O R a st' h O2 R2
    cases T with
    | nil => simp [Whir.runF] at h
    | cons n xs =>
      simp only [Whir.runF] at h ⊢
      split at h
      · rename_i hpow
        simp only [hpow, ↓reduceIte]
        exact ih hp _ xs O R a st' h O2 R2
      · simp at h
  | commit _ _ _ _ => intro hp; exact hp.elim
  | query _ _ _ _ => intro hp; exact hp.elim

/-- **A carried run of a program without commitments is a `RunsTo`** on the words it reads. -/
theorem runsTo_of_runF {α : Type} {p : VerifierProgram α} (hp : NoCommit p) {s : Fs} {T : List E}
    {O : List (List Opening)} {R : List (Digest × ℕ × ℕ)} {a : α} {st' : Whir.FSt}
    (h : Whir.runF p ⟨s, T, O, R⟩ = some (a, st')) :
    ∃ xs, T = xs ++ st'.stream ∧ RunsTo p s xs a st'.sponge := by
  obtain ⟨pre, opre, hs, ho, hf⟩ := runF_frame h
  obtain ⟨-, hO⟩ := NoCommit.runF hp h
  refine ⟨pre, hs, fun sp hsp rest os roots ↦ ?_⟩
  have e := hf rest []
  have e2 := NoCommitA.runF_any p ((noCommit_iff _).1 hp) s _ _ R a _ e os roots
  obtain ⟨sp', hc, hr⟩ := runId_of_runF e2 hsp
  exact ⟨sp', hc, hr⟩


/-! ## The announced sizes -/

theorem runF_readN : ∀ (n : ℕ) (st : Whir.FSt) (xs : List E) (st' : Whir.FSt),
    Whir.runF (VerifierProgram.readScalars n) st = some (xs, st') →
      st.stream = xs ++ st'.stream ∧ xs.length = n
  | 0, st, xs, st', h => by
    simp only [VerifierProgram.readScalars, Whir.runF, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  | n + 1, st, xs, st', h => by
    simp only [VerifierProgram.readScalars, VerifierProgram.bind_eq, VerifierProgram.pure_eq] at h
    obtain ⟨x, s1, h1, h⟩ := Whir.runF_bind_some h
    obtain ⟨ys, s2, h2, h⟩ := Whir.runF_bind_some h
    simp only [Whir.runF, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨e2, l2⟩ := runF_readN n s1 ys s2 h2
    obtain ⟨sp, stream, os, R⟩ := st
    cases stream with
    | nil => simp [VerifierProgram.readScalar, Whir.runF] at h1
    | cons y rest =>
      simp only [VerifierProgram.readScalar, Whir.runF, Option.some.injEq, Prod.mk.injEq] at h1
      obtain ⟨rfl, rfl⟩ := h1
      refine ⟨?_, by simp [l2]⟩
      simp only at e2 ⊢
      rw [e2, List.cons_append]

theorem runF_liftOption_bind {α β : Type} {o : Option α} {k : α → VerifierProgram β} {st : Whir.FSt}
    {r : β × Whir.FSt} (h : Whir.runF ((liftOption o).bind k) st = some r) :
    ∃ a, o = some a ∧ Whir.runF (k a) st = some r := by
  cases o with
  | none => simp [Verifier.liftOption, VerifierProgram.bind, Whir.runF] at h
  | some a => exact ⟨a, rfl, h⟩

theorem word_eOfNat_of {v : E} (h1 : v.limb 1 = 0) :
    v = eOfNat (kToNat (v.limb 0)) := by
  apply E.ext
  intro i
  fin_cases i
  · simp [eOfNat, ofBits_kToNat]
  · simp [eOfNat, h1]

/-- **The announced sizes' run**: the words `eOfNat logMem`, the row counts, `eOfNat r`, and the
layout `layoutOf bytecode logMem rows`. -/
theorem readSizes_inv {bytecode : List K} (hbl : bytecode.length = 2 ^ 23) {st : Whir.FSt}
    {L : Layout} {r : ℕ} {st' : Whir.FSt}
    (h : Whir.runF (readAnnouncedSizes bytecode) st = some ((L, r), st')) :
    ∃ (logMem : ℕ) (rowsN : List ℕ),
      st.stream = (eOfNat logMem :: rowsN.map eOfNat ++ [eOfNat r]) ++ st'.stream ∧
      L = Tables.layoutOf bytecode logMem rowsN ∧ 16 ≤ logMem ∧ logMem ≤ 32 ∧
      rowsN.length = 6 ∧ (∀ n ∈ rowsN, n ≤ 2 ^ 32) ∧ 1 ≤ r ∧ r ≤ 4 ∧
      Whir.minLogStack ≤ L.stackLog ∧ L.stackLog ≤ Whir.maxLogStack := by
  unfold readAnnouncedSizes at h
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq] at h
  obtain ⟨xs, s1, h1, h⟩ := Whir.runF_bind_some h
  obtain ⟨hs1, hl⟩ := runF_readN _ _ _ _ h1
  obtain ⟨hall, h⟩ := runF_require_bind h
  obtain ⟨hr, h⟩ := runF_require_bind h
  obtain ⟨L', hL', h⟩ := runF_liftOption_bind h
  obtain ⟨hst, h⟩ := runF_require_bind h
  simp only [Whir.runF, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
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
    -- the layout's conditions
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

theorem ReadOnly.bind {α β : Type} {p : VerifierProgram α} {f : α → VerifierProgram β} (hp :
    ReadOnly p)
    (hf : ∀ a, ReadOnly (f a)) : ReadOnly (p.bind f) := by
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

theorem readOnly_ret {α : Type} (a : α) : ReadOnly (VerifierProgram.ret a) := (readOnly_iff _).2
    trivial

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

/-- A run that only reads returns what the stream gives, whatever the hashes and the sponge. -/
theorem ReadOnlyA.run_eq {α : Type} (p : VerifierProgram α) : ReadOnlyA p →
    ∀ (H H' : Bytes → Id Digest) (F F' : KeccakState → Id KeccakState) (sp sp' : Sponge) (T : List E)
      (O O' : List (List Opening)) (R R' : List (Digest × ℕ × ℕ)),
      (Id.run (Compile.runWithHash (m := Id) H F p ⟨sp, T, O, R⟩)).map (·.1) =
        (Id.run (Compile.runWithHash (m := Id) H' F' p ⟨sp', T, O', R'⟩)).map (·.1) := by
  induction p with
  | ret a => intros; rfl
  | fail => intros; rfl
  | read k ih =>
    intro hp H H' F F' sp sp' T O O' R R'
    cases T with
    | nil => rfl
    | cons x xs => exact ih x (hp x) H H' F F' _ _ xs O O' R R'
  | sample _ _ => intro hp; exact hp.elim
  | grind _ _ _ => intro hp; exact hp.elim
  | commit _ _ _ _ => intro hp; exact hp.elim
  | query _ _ _ _ => intro hp; exact hp.elim

/-- **The run's sizes are `Verifier.announcedLayoutAndRate`'s.** -/
theorem announced_eq {bytecode : List K} {s : Fs} {T : List E} {O : List (List Opening)}
    {R : List (Digest × ℕ × ℕ)} {L : Layout} {r : ℕ} {st' : Whir.FSt} {sp : Sponge}
    (hs : s.Carries sp) (h : Whir.runF (readAnnouncedSizes bytecode) ⟨s, T, O, R⟩ = some ((L, r),
        st')) :
    Verifier.announcedLayoutAndRate bytecode T = some (L, r) := by
  obtain ⟨sp', -, hr⟩ := runId_of_runF h hs
  have e := ReadOnlyA.run_eq _ ((readOnly_iff _).1 (readOnly_readSizes bytecode))
    (fun _ ↦ default) keccak256 (fun _ ↦ default) keccakF1600 ⟨default, []⟩ sp T [] O [] R
  unfold Verifier.announcedLayoutAndRate
  rw [Compile.runPure_eq_withHash, e]
  change (runId (readAnnouncedSizes bytecode) ⟨sp, T, O, R⟩).map (·.1) = _
  rw [hr]
  rfl


/-! ## Squeezes and the stack's root -/

theorem runF_sampleN : ∀ (n : ℕ) (st : Whir.FSt) (xs : List E) (st' : Whir.FSt),
    Whir.runF (VerifierProgram.sampleChallenges n) st = some (xs, st') →
      st.sponge.squeezeN n = (xs, st'.sponge) ∧ st'.stream = st.stream ∧
        st'.openings = st.openings ∧ st'.roots = st.roots
  | 0, st, xs, st', h => by
    simp only [VerifierProgram.sampleChallenges, Whir.runF, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl, rfl, rfl⟩
  | n + 1, st, xs, st', h => by
    simp only [VerifierProgram.sampleChallenges, VerifierProgram.bind_eq,
        VerifierProgram.pure_eq] at h
    rw [show VerifierProgram.sampleChallenge = VerifierProgram.sample VerifierProgram.ret from
        rfl] at h
    simp only [VerifierProgram.bind, Whir.runF] at h
    obtain ⟨ys, s2, h2, h⟩ := Whir.runF_bind_some h
    simp only [Whir.runF, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨e1, e2, e3, e4⟩ := runF_sampleN n _ ys s2 h2
    refine ⟨?_, e2, e3, e4⟩
    simp only [Fs.squeezeN, e1]

/-- **The stack's commitment**: two words, the root their digest, absorbed. -/
theorem commitStack_runF' {μ r : ℕ} {st : Whir.FSt} {u : Unit} {st' : Whir.FSt}
    (h : Whir.runF (commitStack μ r) st = some (u, st')) :
    ∃ (x0 x1 : E) (root : Digest), digestFromHalves (x0, x1) = some root ∧
      st.stream = x0 :: x1 :: st'.stream ∧
      st'.sponge = (st.sponge.absorb x0 dsObserve).absorb x1 dsObserve ∧
      st'.roots = st.roots ++ [(root, Whir.stackShape μ r)] ∧ st'.openings = st.openings := by
  cases hc : Whir.ladder μ r with
  | none =>
    unfold commitStack at h
    rw [hc] at h
    exact absurd h (by simp [Verifier.liftOption, VerifierProgram.bind, Whir.runF])
  | some cfg =>
    cases cfg with
    | nil =>
      unfold commitStack at h
      rw [hc] at h
      exact absurd h (by simp [Verifier.liftOption, VerifierProgram.bind, Whir.runF])
    | cons level rest =>
      rw [Whir.commitStack_eq hc] at h
      obtain ⟨s, stream, os, R⟩ := st
      match stream, h with
      | x0 :: x1 :: xs, h =>
        simp only [VerifierProgram.readCommitment, Whir.runF] at h
        split at h
        · rename_i root hr
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨-, rfl⟩ := h
          exact ⟨x0, x1, root, hr, rfl, rfl, rfl, rfl⟩
        · simp at h


/-! ## The segments -/

/-- **An honest child's accepted run, cut into `verify_sub`'s segments** (`pi` the child's
statement's digest, `S0` the seed's state): the announced sizes, the stack's root, the bus
challenges, the bus's GKR, `tablesSeg`, the lanes' check, `keccakSeg`, the ring map's other five
challenges, then the batching challenge and the stacked opening. -/
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
  runS : RunsTo (readAnnouncedSizes bytecode) ⟨capOf (keccakF1600 (seedInput seed
    (Node.statementDigest seed c.statement))), []⟩
    (eOfNat logMem :: rowsN.map eOfNat ++ [eOfNat rate]) (layout, rate) s1
  /-- The stack's root. -/
  x0 : E
  x1 : E
  root : Digest
  hroot : digestFromHalves (x0, x1) = some root
  /-- The bus challenges. -/
  alphas : List E
  s3 : Fs
  halphas : ((s1.absorb x0 dsObserve).absorb x1 dsObserve).squeezeN busBits = (alphas, s3)
  /-- The bus's GKR. -/
  xsG : List E
  rG : E × List E × List E
  s5 : Fs
  runG : RunsTo (Tables.gkrPhase (busLayout [0, layout.logMemory, layout.logBytecode]
    layout.push).depth) s3.squeeze.2 xsG rG s5
  /-- The bus's rest, the tables, the public input. -/
  xsT : List E
  bus : BusResult
  claims : List ColumnClaim
  s6 : Fs
  runT : RunsTo (Tables.tablesSeg (claimedBytecodeValue c.freshClaim) layout (Node.statementDigest seed c.statement)
    alphas s3.squeeze.1 rG.2.1 rG.2.2) s5 xsT (bus, claims) s6
  /-- The output lanes: the table's columns, one point. -/
  hlanes : (lanesOf claims).map (·.column) = keccakOutputColumns ∧
    ∀ c' ∈ lanesOf claims, c'.point = ((lanesOf claims).headD default).point
  /-- The Keccak reduction and the ring map's first challenge. -/
  xsK : List E
  km : (List ColumnClaim × List E × List E) × E
  s7 : Fs
  runK : RunsTo (keccakSeg (layout.tableLogHeights.getD opKeccak 0)
    ((lanesOf claims).headD default).point ((lanesOf claims).map (·.value))) s6 xsK km s7
  /-- The ring map's other five challenges. -/
  chs : List E
  s8 : Fs
  hchs : s7.squeezeN 5 = (chs, s8)
  /-- The stacked opening: from the batching challenge's state, on the stream's rest and the
  proof's openings, with no zero challenge and openings agreeing in the caps, to an end passing
  the terminal's check. -/
  xsW : List E
  w : Whir.WhirEnd
  s' : Fs
  roots' : List (Digest × ℕ × ℕ)
  runW : Whir.RunsWith (Whir.whirOpen layout.stackLog rate
    (batchTarget (stackClaims layout claims km.1.1 km.1.2.1 km.1.2.2 (km.2 :: chs)) s8.squeeze.1))
    ⟨capOf s8.perm, []⟩ xsW c.proof.openings [(root, Whir.stackShape layout.stackLog rate)] w s'
    roots'
  nzW : Whir.NoZeroChallenge layout.stackLog rate
    (batchTarget (stackClaims layout claims km.1.1 km.1.2.1 km.1.2.2 (km.2 :: chs)) s8.squeeze.1)
    s8.perm xsW c.proof.openings root
  capsW : Whir.CapsAgree layout.stackLog rate
    (batchTarget (stackClaims layout claims km.1.1 km.1.2.1 km.1.2.2 (km.2 :: chs)) s8.squeeze.1)
    s8.perm xsW c.proof.openings root
  acc : w.Accepts
    (batchBasis (stackClaims layout claims km.1.1 km.1.2.1 km.1.2.2 (km.2 :: chs)) s8.squeeze.1)
  /-- The stream is the segments' words. -/
  hstream : c.proof.stream = (eOfNat logMem :: rowsN.map eOfNat ++ [eOfNat rate]) ++ [x0, x1] ++
    xsG ++ xsT ++ xsK ++ xsW
  /-- The announced sizes are `Verifier.announcedLayoutAndRate`'s. -/
  hann : Verifier.announcedLayoutAndRate bytecode c.proof.stream = some (layout, rate)

/-- **An honest child's run, in segments** (G7's per-child hypotheses; the guest's bytecode of
`2^23` words). -/
theorem child_segments {bytecode : List K} (hbl : bytecode.length = 2 ^ 23) (seed : Digest)
    (c : Node.Child)
    (hmu : ∀ layout r, Verifier.announcedLayoutAndRate bytecode c.proof.stream = some (layout, r) →
      Coverage.minChildStackLog ≤ layout.stackLog)
    (hnz : Limits.verifyDeferredNZ bytecode seed (Node.statementDigest seed c.statement) c.freshClaim
      c.proof = true)
    (hcaps : ∀ b ∈ Limits.queryStepsOf
      (deferringVerifierProgram c.freshClaim bytecode (Node.statementDigest seed c.statement))
      (Coverage.childVerifierStart seed c), Limits.OpeningsAgree b.1 b.2) :
    Nonempty (ChildSegs bytecode seed c) := by
  obtain ⟨q, sq, root, xsW, w, s', roots', hpre, hrun, hnzW, hcapsW, hacc⟩ :=
    child_open seed c hnz hcaps
  rw [specPre_flat] at hpre
  unfold flatPre at hpre
  -- the announced sizes
  obtain ⟨ls, sA, hA, h⟩ := Whir.runF_bind_some hpre
  obtain ⟨L, r⟩ := ls
  obtain ⟨logMem, rowsN, hsA, hL, h16, h32, hrowsL, hrows32, hr1, hr4, -, hst28⟩ :=
    readSizes_inv hbl hA
  obtain ⟨xs1, hxs1, runS⟩ := runsTo_of_runF (noCommit_readSizes _) hA
  have exs1 : xs1 = eOfNat logMem :: rowsN.map eOfNat ++ [eOfNat r] := by
    have := hsA.symm.trans hxs1
    exact (List.append_cancel_right this).symm
  subst exs1
  have hmu22 : Coverage.minChildStackLog ≤ L.stackLog := hmu L r (announced_eq (sp := ⟨keccakF1600 (seedInput seed
    (Node.statementDigest seed c.statement)), []⟩) ⟨rfl, rfl⟩ hA)
  obtain ⟨rA, oA⟩ := NoCommit.runF (noCommit_readSizes _) hA
  -- the stack's root
  obtain ⟨u, sB, hB, h⟩ := Whir.runF_bind_some h
  obtain ⟨x0, x1, root', hroot, hsB, hspB, hrB, hoB⟩ := commitStack_runF' hB
  -- the bus challenges
  obtain ⟨alphas, sC, hC, h⟩ := Whir.runF_bind_some h
  obtain ⟨hal, hsC, hoC, hrC⟩ := runF_sampleN _ _ _ _ hC
  rw [runF_sample_bind] at h
  -- the bus's GKR
  obtain ⟨rG, sD, hD, h⟩ := Whir.runF_bind_some h
  obtain ⟨xsG, hxsG, runG⟩ := runsTo_of_runF (noCommit_gkrPhase _) hD
  obtain ⟨rD, oD⟩ := NoCommit.runF (noCommit_gkrPhase _) hD
  -- the tables
  obtain ⟨bc, sE, hE, h⟩ := Whir.runF_bind_some h
  obtain ⟨bus, claims⟩ := bc
  obtain ⟨xsT, hxsT, runT⟩ := runsTo_of_runF (noCommit_tablesSeg _ _ _ _ _ _ _) hE
  obtain ⟨rE, oE⟩ := NoCommit.runF (noCommit_tablesSeg _ _ _ _ _ _ _) hE
  -- the lanes
  obtain ⟨hlanes, h⟩ := runF_require_bind h
  -- the Keccak reduction
  obtain ⟨km, sF, hF, h⟩ := Whir.runF_bind_some h
  obtain ⟨xsK, hxsK, runK⟩ := runsTo_of_runF (noCommit_keccakSeg _ _ _) hF
  obtain ⟨rF, oF⟩ := NoCommit.runF (noCommit_keccakSeg _ _ _) hF
  -- the ring map's other challenges
  obtain ⟨chs, sG, hG, h⟩ := Whir.runF_bind_some h
  obtain ⟨hch, hsG, hoG, hrG⟩ := runF_sampleN _ _ _ _ hG
  simp only [Whir.runF, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  -- the root is the opening's
  have hroot' : root' = root := by
    have e := hrG
    simp only at e
    rw [rF, rE, rD, hrC, hrB, rA] at e
    simp only [deferStart, List.nil_append, List.cons.injEq, Prod.mk.injEq, and_true] at e
    exact e.symm
  subst hroot'
  refine ⟨⟨logMem, rowsN, r, L, hL, h16, h32, hrowsL, hrows32, hr1, hr4, hmu22, hst28, sA.sponge,
    runS, x0, x1, root', hroot, alphas, sC.sponge, ?_, xsG, rG, sD.sponge, ?_, xsT, bus, claims,
    sE.sponge, runT, hlanes, xsK, km, sF.sponge, runK, chs, _, hch, xsW, w, s', roots', hrun,
    hnzW, hcapsW, hacc, ?_, ?_⟩⟩
  · rw [← hspB]; exact hal
  · exact runG
  · -- the stream
    have h0 : c.proof.stream = (deferStart seed (Node.statementDigest seed c.statement)
        c.proof).stream := rfl
    rw [h0, hsA, hsB, ← hsC, hxsG, hxsT, hxsK, ← hsG]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  · exact announced_eq (sp := ⟨keccakF1600 (seedInput seed (Node.statementDigest seed c.statement)), []⟩)
      ⟨rfl, rfl⟩ hA

end
end LeanVM.Guest.B1.VerifySub
