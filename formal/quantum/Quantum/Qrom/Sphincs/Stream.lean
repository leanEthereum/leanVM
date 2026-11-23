module

public import Quantum.Qrom.Sphincs.Cov
public import Quantum.Sphincs.Assembly.Stream

@[expose] public section

/-!
# The digest stream of the regrouped `H_msg` cells

The honest digest of a message `m` is one regrouped cell with a pair value (`Cov.lean`). Its value
is hidden, i.i.d. uniform, and enters the template game only through the reveal at the first
signature of `m`. **The exact reindexing**: the hybrid side's policy reveals the digest coordinate
`.dig m` of the message (`msgNeed`); the event side's reveals the stream entry `.str j` of the
`j`-th distinct signed message in first-request order, marked `.asg m j`, and `.dig m` past the
`N` entries (`strNeed`). Both are template programs over the sampled register of
`Quantum.Sig.Sampled`; the renaming simulation `RenSim` of `Quantum.Sphincs.Assembly.Stream`
(generic in the register) relates them with the renaming `msgLab`, `msgStore` and the invariant
`StreamInv`, so the averaged laws are equal (`evalDistMap_sampled_eq_of_renSim`,
`uavg_realizeT_outcome_eq_sampled`). Adaptive requests are absorbed by the lazy sampling: a stream
entry is fresh when it is marked, as the digest is when it is first revealed.

* `SPos P J N`, `SVal Ω`: template coordinates over base coordinates `P` (positions, randomizers)
  and messages `J`, with values `Ω` and unit-valued marks.
* `streamIdx`, `strNeed`, `strOut`, `msgNeed`: the two policies' coordinates.
* The renaming and `StreamInv` along every reveal: `renSim_revealThen_val` (base coordinates),
  `renSim_revealEntry` (a stream entry, new or marked, exchanged with the digest by `entryEquiv`),
  `renSim_revealFall` (past the stream, kept by `fallEquiv`). After a digest reveal the renamed
  store's digest is the event side's value (`fill_msgStore_dig_entry`, `fill_msgStore_dig_fall`).
  Base program ports are simulated by themselves (`portSim_self`).
* **S★**: `streamOf v`, the stream held by the values. Without a fallback reveal, the views of
  every revealed digest are disclosed by the static `starCover (streamOf v)`
  (`revealed_subset_streamCover`). Averaged over the values, `streamOf` is a uniform stream
  (`uavg_streamOf`), so Minkowski over S★ holds on the template values
  (`uavg_sq_add_sqrt_starCover_streamOf_le`).
-/

open Finset
open scoped ENNReal
open Sphincs hiding HashDomain
open HashSig hiding PublicKey
open Quantum.Sig (Store swapIn swapOpt fill Agrees storeOn fill_storeOn_of_mem)
open Quantum.Xmss.Assembly (RevealVals revealThen tmplSpec)
open Quantum.Xmss.Hybrid (LazyProg restrictTo uavg)
open Quantum.Sphincs.Assembly (RenSim PortSim renSim_revealThen)
open Quantum.Sphincs (View Covered ofViews ofViews_le_revealed rhoCov uavg_comp_equiv price)

namespace Quantum.Qrom.Sphincs

/-! ## Coordinates -/

section coords

variable (P J : Type) (N : ℕ)

/-- **Template coordinates with a digest stream**: the base coordinates `P` (positions and
randomizers), the digest cell of each message, the `N` stream entries, and the marks `asg m j`
(message `m` uses stream entry `j`). -/
inductive SPos where
  | val (p : P)
  | dig (m : J)
  | str (j : Fin N)
  | asg (m : J) (j : Fin N)
  deriving DecidableEq

/-- The coordinates as a sum. -/
def SPos.equivSum : SPos P J N ≃ P ⊕ J ⊕ Fin N ⊕ (J × Fin N) where
  toFun
    | .val p => .inl p
    | .dig m => .inr (.inl m)
    | .str j => .inr (.inr (.inl j))
    | .asg m j => .inr (.inr (.inr (m, j)))
  invFun
    | .inl p => .val p
    | .inr (.inl m) => .dig m
    | .inr (.inr (.inl j)) => .str j
    | .inr (.inr (.inr (m, j))) => .asg m j
  left_inv s := by cases s <;> rfl
  right_inv x := by rcases x with p | m | j | ⟨m, j⟩ <;> rfl

instance instFintypeSPos [Fintype P] [Fintype J] : Fintype (SPos P J N) :=
  Fintype.ofEquiv _ (SPos.equivSum P J N).symm

variable {P J N}

/-- **The values**: `Ω` at a base coordinate, a digest or a stream entry; nothing at a mark. -/
def SVal (Ω : Type) : SPos P J N → Type
  | .val _ => Ω
  | .dig _ => Ω
  | .str _ => Ω
  | .asg _ _ => Unit

instance instFintypeSVal (Ω : Type) [Fintype Ω] : ∀ s : SPos P J N, Fintype (SVal Ω s)
  | .val _ => inferInstanceAs (Fintype Ω)
  | .dig _ => inferInstanceAs (Fintype Ω)
  | .str _ => inferInstanceAs (Fintype Ω)
  | .asg _ _ => inferInstanceAs (Fintype Unit)

instance instDecidableEqSVal (Ω : Type) [DecidableEq Ω] : ∀ s : SPos P J N, DecidableEq (SVal Ω s)
  | .val _ => inferInstanceAs (DecidableEq Ω)
  | .dig _ => inferInstanceAs (DecidableEq Ω)
  | .str _ => inferInstanceAs (DecidableEq Ω)
  | .asg _ _ => inferInstanceAs (DecidableEq Unit)

instance instNonemptySVal (Ω : Type) [Nonempty Ω] : ∀ s : SPos P J N, Nonempty (SVal Ω s)
  | .val _ => inferInstanceAs (Nonempty Ω)
  | .dig _ => inferInstanceAs (Nonempty Ω)
  | .str _ => inferInstanceAs (Nonempty Ω)
  | .asg _ _ => inferInstanceAs (Nonempty Unit)

end coords

/-! ## Labels and the two policies -/

section labels

variable {P J : Type} {N : ℕ} [DecidableEq P] [DecidableEq J]

/-- A base coordinate. -/
def SPos.IsVal : SPos P J N → Prop
  | .val _ => True
  | _ => False

/-- **Base coordinates only**: every reveal and program port outside the digest policy. -/
def ValOnly (T : Finset (SPos P J N)) : Prop :=
  ∀ s ∈ T, s.IsVal

omit [DecidableEq P] [DecidableEq J] in
theorem ValOnly.dig {T : Finset (SPos P J N)} (hT : ValOnly T) (m : J) : SPos.dig m ∉ T :=
  fun h ↦ hT _ h

omit [DecidableEq P] [DecidableEq J] in
theorem ValOnly.str {T : Finset (SPos P J N)} (hT : ValOnly T) (j : Fin N) : SPos.str j ∉ T :=
  fun h ↦ hT _ h

omit [DecidableEq P] [DecidableEq J] in
theorem ValOnly.asg {T : Finset (SPos P J N)} (hT : ValOnly T) (m : J) (j : Fin N) :
    SPos.asg m j ∉ T :=
  fun h ↦ hT _ h

/-- A mark coordinate. -/
def SPos.isAsg : SPos P J N → Bool
  | .asg _ _ => true
  | _ => false

/-- The number of marks of a label. -/
def asgCount (T : Finset (SPos P J N)) : ℕ :=
  (T.filter fun s ↦ s.isAsg = true).card

/-- At most one mark per message. -/
def OneMark (L : Finset (SPos P J N)) : Prop :=
  ∀ m j j', SPos.asg m j ∈ L → SPos.asg m j' ∈ L → j = j'

/-- The stream entry marked for `msg` in the label `L`, if any. -/
noncomputable def markOf (L : Finset (SPos P J N)) (msg : J) : Option (Fin N) :=
  @dite _ (∃ j, SPos.asg msg j ∈ L) (Classical.propDecidable _)
    (fun h ↦ some (Classical.choose h)) fun _ ↦ none

omit [DecidableEq P] [DecidableEq J] in
theorem markOf_of_mem {L : Finset (SPos P J N)} (hL : OneMark L) {msg : J} {j : Fin N}
    (h : SPos.asg msg j ∈ L) : markOf L msg = some j := by
  have hex : ∃ j, SPos.asg msg j ∈ L := ⟨j, h⟩
  unfold markOf
  rw [dite_eq_left hex]
  exact congrArg some (hL msg _ _ (Classical.choose_spec hex) h)

omit [DecidableEq P] [DecidableEq J] in
theorem markOf_of_free {L : Finset (SPos P J N)} {msg : J} (h : ∀ j, SPos.asg msg j ∉ L) :
    markOf L msg = none := by
  unfold markOf
  rw [dite_eq_right fun hex : ∃ j, SPos.asg msg j ∈ L ↦ h _ hex.choose_spec]

theorem mem_of_markOf {L : Finset (SPos P J N)} {msg : J} {j : Fin N}
    (h : markOf L msg = some j) : SPos.asg msg j ∈ L := by
  by_cases hex : ∃ j, SPos.asg msg j ∈ L
  · unfold markOf at h
    rw [dite_eq_left hex, Option.some.injEq] at h
    exact h ▸ hex.choose_spec
  · exact absurd h (by rw [markOf_of_free fun j hj ↦ hex ⟨j, hj⟩]; simp)

/-- A mark of `msg` is added by `U` only if `U` marks `msg`. -/
theorem markOf_union {L U : Finset (SPos P J N)} (hL : OneMark (L ∪ U)) {msg : J}
    (hU : ∀ j, SPos.asg msg j ∉ U) : markOf (L ∪ U) msg = markOf L msg := by
  by_cases hex : ∃ j, SPos.asg msg j ∈ L
  · obtain ⟨j, hj⟩ := hex
    rw [markOf_of_mem hL (Finset.mem_union_left _ hj),
      markOf_of_mem (fun m a b ha hb ↦ hL m a b (Finset.mem_union_left _ ha)
        (Finset.mem_union_left _ hb)) hj]
  · rw [markOf_of_free fun j hj ↦ (Finset.mem_union.1 hj).elim (fun h ↦ hex ⟨j, h⟩) (hU j),
      markOf_of_free fun j hj ↦ hex ⟨j, hj⟩]

/-- **The stream entry of `msg`** at the label `L`: the entry its mark names, otherwise the next
one (the number of marks), none past `N` entries. -/
noncomputable def streamIdx (L : Finset (SPos P J N)) (msg : J) : Option (Fin N) :=
  @dite _ (∃ j, SPos.asg msg j ∈ L) (Classical.propDecidable _)
    (fun h ↦ some (Classical.choose h))
    fun _ ↦ if h : asgCount L < N then some ⟨asgCount L, h⟩ else none

/-- **The event side's digest reveal** of `msg` at the label `L`: the stream entry and its mark,
past the stream the digest. -/
noncomputable def strNeed (L : Finset (SPos P J N)) (msg : J) : Finset (SPos P J N) :=
  match streamIdx L msg with
  | some j => {.str j, .asg msg j}
  | none => {.dig msg}

/-- The coordinate holding the event side's digest of `msg` at the label `L`. -/
noncomputable def strOut (L : Finset (SPos P J N)) (msg : J) : SPos P J N :=
  match streamIdx L msg with
  | some j => .str j
  | none => .dig msg

/-- **The hybrid side's digest reveal** of `msg`: its digest. -/
def msgNeed (msg : J) : Finset (SPos P J N) :=
  {.dig msg}

theorem mem_strNeed_some {L : Finset (SPos P J N)} {msg : J} {j : Fin N}
    (hs : streamIdx L msg = some j) (s : SPos P J N) :
    s ∈ strNeed L msg ↔ s = .str j ∨ s = .asg msg j := by
  simp only [strNeed, hs, Finset.mem_insert, Finset.mem_singleton]

theorem mem_strNeed_none {L : Finset (SPos P J N)} {msg : J} (hs : streamIdx L msg = none)
    (s : SPos P J N) : s ∈ strNeed L msg ↔ s = .dig msg := by
  simp only [strNeed, hs, Finset.mem_singleton]

omit [DecidableEq P] [DecidableEq J] in
theorem strOut_some {L : Finset (SPos P J N)} {msg : J} {j : Fin N}
    (hs : streamIdx L msg = some j) : strOut L msg = .str j := by
  simp only [strOut, hs]

omit [DecidableEq P] [DecidableEq J] in
theorem strOut_none {L : Finset (SPos P J N)} {msg : J} (hs : streamIdx L msg = none) :
    strOut L msg = .dig msg := by
  simp only [strOut, hs]

omit [DecidableEq P] [DecidableEq J] in
theorem mem_msgNeed (msg : J) (s : SPos P J N) : s ∈ msgNeed msg ↔ s = .dig msg :=
  Finset.mem_singleton

theorem asgCount_union_noAsg {L U : Finset (SPos P J N)} (hU : ∀ m j, SPos.asg m j ∉ U) :
    asgCount (L ∪ U) = asgCount L := by
  have hU' : U.filter (fun s ↦ s.isAsg = true) = ∅ :=
    Finset.filter_eq_empty_iff.2 fun s hs ha ↦ by
      cases s with
      | asg m j => exact hU m j hs
      | _ => cases ha
  unfold asgCount
  rw [Finset.filter_union, hU', Finset.union_empty]

theorem oneMark_union_noAsg {L U : Finset (SPos P J N)} (hL : OneMark L)
    (hU : ∀ m j, SPos.asg m j ∉ U) : OneMark (L ∪ U) := fun m j j' h h' ↦
  hL m j j' ((Finset.mem_union.1 h).resolve_right (hU m j))
    ((Finset.mem_union.1 h').resolve_right (hU m j'))

/-- **A message with a stream entry**, after a reveal without marks: marked by it, or unmarked
with the entry the number of marks. -/
theorem streamIdx_some_facts {L U : Finset (SPos P J N)} {msg : J} {j : Fin N}
    (hs : streamIdx L msg = some j) (hU : ∀ m j, SPos.asg m j ∉ U) :
    SPos.asg msg j ∈ L ∪ U ∨
      ((∀ j', SPos.asg msg j' ∉ L ∪ U) ∧ j.val = asgCount (L ∪ U)) := by
  rw [asgCount_union_noAsg hU]
  unfold streamIdx at hs
  by_cases hex : ∃ j', SPos.asg msg j' ∈ L
  · rw [dite_eq_left hex, Option.some.injEq] at hs
    exact Or.inl (Finset.mem_union_left _ (hs ▸ hex.choose_spec))
  · rw [dite_eq_right hex] at hs
    split_ifs at hs with hc
    rw [Option.some.injEq] at hs
    refine Or.inr ⟨fun j' h ↦ (Finset.mem_union.1 h).elim (fun h ↦ hex ⟨j', h⟩) (hU msg j'), ?_⟩
    rw [← hs]

/-- **A message past the stream**, after a reveal without marks: unmarked, the stream used up. -/
theorem streamIdx_none_facts {L U : Finset (SPos P J N)} {msg : J} (hs : streamIdx L msg = none)
    (hU : ∀ m j, SPos.asg m j ∉ U) :
    (∀ j, SPos.asg msg j ∉ L ∪ U) ∧ N ≤ asgCount (L ∪ U) := by
  rw [asgCount_union_noAsg hU]
  unfold streamIdx at hs
  by_cases hex : ∃ j', SPos.asg msg j' ∈ L
  · rw [dite_eq_left hex] at hs
    cases hs
  · rw [dite_eq_right hex] at hs
    split_ifs at hs with hc
    exact ⟨fun j' h ↦ (Finset.mem_union.1 h).elim (fun h ↦ hex ⟨j', h⟩) (hU msg j'), by omega⟩

end labels

/-! ## The renaming of the event side's labels and stores -/

section rename

variable {P J : Type} {N : ℕ} [DecidableEq P] [DecidableEq J] {Ω : Type} [DecidableEq Ω]

/-- **The renamed store**: the digest of a marked message is its stream entry's; the stream and
the marks are dropped; the base values are kept. -/
noncomputable def msgStore (L : Finset (SPos P J N)) (σ : Store (S := SPos P J N) (SVal Ω)) :
    Store (S := SPos P J N) (SVal Ω)
  | .val p => σ (.val p)
  | .dig m => match markOf L m with
    | some j => (σ (.str j) : Option Ω)
    | none => σ (.dig m)
  | .str _ => none
  | .asg _ _ => none

omit [DecidableEq P] [DecidableEq J] [DecidableEq Ω] in
theorem msgStore_dig_some {L : Finset (SPos P J N)} {σ : Store (S := SPos P J N) (SVal Ω)}
    {m : J} {j : Fin N} (h : markOf L m = some j) :
    msgStore L σ (.dig m) = (σ (.str j) : Option Ω) := by
  simp only [msgStore, h]
  rfl

omit [DecidableEq P] [DecidableEq J] [DecidableEq Ω] in
theorem msgStore_dig_none {L : Finset (SPos P J N)} {σ : Store (S := SPos P J N) (SVal Ω)}
    {m : J} (h : markOf L m = none) : msgStore L σ (.dig m) = σ (.dig m) := by
  simp only [msgStore, h]

omit [DecidableEq P] [DecidableEq J] [DecidableEq Ω] in
theorem msgStore_of_isVal (L : Finset (SPos P J N)) (σ : Store (S := SPos P J N) (SVal Ω))
    {s : SPos P J N} (hs : s.IsVal) : msgStore L σ s = σ s := by
  cases s with
  | val p => rfl
  | _ => exact absurd hs id

/-- The coordinates of the renamed label. -/
def InMsg (L : Finset (SPos P J N)) : SPos P J N → Prop
  | .val p => SPos.val p ∈ L
  | .dig m => SPos.dig m ∈ L ∨ ∃ j, SPos.asg m j ∈ L ∧ SPos.str j ∈ L
  | .str _ => False
  | .asg _ _ => False

/-- The coordinates a label coordinate is renamed to, at most: a mark's digest. -/
def expandC : SPos P J N → Finset (SPos P J N)
  | .asg m _ => {.dig m}
  | s => {s}

/-- **The renamed label**: the base coordinates, the fallback digests, and the digests of the
marked messages whose entries are revealed. -/
@[irreducible]
noncomputable def msgLab (L : Finset (SPos P J N)) : Finset (SPos P J N) :=
  @Finset.filter _ (InMsg L) (Classical.decPred _) (L.biUnion expandC)

theorem mem_msgLab {L : Finset (SPos P J N)} {s : SPos P J N} : s ∈ msgLab L ↔ InMsg L s := by
  unfold msgLab
  rw [@Finset.mem_filter _ (InMsg L) (Classical.decPred _)]
  refine and_iff_right_of_imp fun h ↦ Finset.mem_biUnion.2 ?_
  cases s with
  | val p => exact ⟨_, h, Finset.mem_singleton_self _⟩
  | dig m =>
    rcases h with h | ⟨j, hj, -⟩
    · exact ⟨_, h, Finset.mem_singleton_self _⟩
    · exact ⟨_, hj, Finset.mem_singleton_self _⟩
  | str _ => exact False.elim h
  | asg _ _ => exact False.elim h

theorem mem_msgLab_of_isVal {L : Finset (SPos P J N)} {s : SPos P J N} (hs : s.IsVal) :
    s ∈ msgLab L ↔ s ∈ L := by
  rw [mem_msgLab]
  cases s with
  | val p => exact Iff.rfl
  | _ => exact absurd hs id

/-- **The stream invariant** of the event side's label `L` and store `σ`: the store holds values
only on `L`; each message is marked at most once; an entry is revealed exactly when it is marked;
the marked entries lie below the number of marks; a fallback digest is revealed only once the
stream is used up, for an unmarked message. -/
structure StreamInv (L : Finset (SPos P J N)) (σ : Store (S := SPos P J N) (SVal Ω)) : Prop where
  dom : ∀ s, s ∉ L → σ s = none
  one : OneMark L
  str : ∀ j, SPos.str j ∈ L ↔ ∃ m, SPos.asg m j ∈ L
  used : ∀ m j, SPos.asg m j ∈ L → j.val < asgCount L
  dig : ∀ m, SPos.dig m ∈ L → N ≤ asgCount L ∧ ∀ j, SPos.asg m j ∉ L

omit [DecidableEq P] [DecidableEq J] [DecidableEq Ω] in
theorem streamInv_empty :
    StreamInv (∅ : Finset (SPos P J N)) (fun _ ↦ (none : Option (SVal Ω _))) :=
  ⟨fun _ _ ↦ rfl, fun _ _ _ h ↦ absurd h (Finset.notMem_empty _),
    fun _ ↦ iff_of_false (Finset.notMem_empty _) fun ⟨_, h⟩ ↦ Finset.notMem_empty _ h,
    fun _ _ h ↦ absurd h (Finset.notMem_empty _), fun _ h ↦ absurd h (Finset.notMem_empty _)⟩

theorem msgLab_empty : msgLab (∅ : Finset (SPos P J N)) = ∅ := by
  ext s
  rw [mem_msgLab]
  simp only [Finset.notMem_empty, iff_false]
  cases s <;> simp [InMsg]

omit [DecidableEq P] [DecidableEq J] [DecidableEq Ω] in
theorem msgStore_empty :
    msgStore (∅ : Finset (SPos P J N)) (fun _ ↦ none) = fun _ ↦ (none : Option (SVal Ω _)) := by
  funext s
  cases s with
  | dig m => rw [msgStore_dig_none (markOf_of_free fun _ h ↦ Finset.notMem_empty _ h)]
  | _ => rfl

theorem swapIn_apply_of_notMem {T L : Finset (SPos P J N)} (w : RevealVals (SVal Ω) T)
    (σ : Store (S := SPos P J N) (SVal Ω)) {s : SPos P J N} (hs : s ∉ T) :
    swapIn T L w σ s = σ s :=
  dite_eq_right fun h ↦ hs h.1

theorem swapIn_of_subset {T L : Finset (SPos P J N)} (w : RevealVals (SVal Ω) T)
    (σ : Store (S := SPos P J N) (SVal Ω)) (h : T ⊆ L) : swapIn T L w σ = σ :=
  funext fun _ ↦ dite_eq_right fun h' ↦ h'.2 (h h'.1)

theorem swapIn_apply_new {T L : Finset (SPos P J N)} (w : RevealVals (SVal Ω) T)
    {σ : Store (S := SPos P J N) (SVal Ω)} {s : SPos P J N} (hT : s ∈ T) (hL : s ∉ L)
    (hσ : σ s = none) : swapIn T L w σ s = some (w ⟨s, hT⟩) := by
  unfold swapIn
  rw [dite_eq_left ⟨hT, hL⟩, hσ]
  rfl

theorem swapIn_apply_of_mem {T L : Finset (SPos P J N)} (w : RevealVals (SVal Ω) T)
    (σ : Store (S := SPos P J N) (SVal Ω)) {s : SPos P J N} (hT : s ∈ T) (hL : s ∉ L) :
    swapIn T L w σ s = swapOpt (w ⟨s, hT⟩) (σ s) :=
  dite_eq_left ⟨hT, hL⟩

theorem swapIn_apply_of_memL {T L : Finset (SPos P J N)} (w : RevealVals (SVal Ω) T)
    (σ : Store (S := SPos P J N) (SVal Ω)) {s : SPos P J N} (hL : s ∈ L) :
    swapIn T L w σ s = σ s :=
  dite_eq_right fun h ↦ h.2 hL

/-! ### Reveals of base coordinates -/

theorem msgLab_union_val (L : Finset (SPos P J N)) {T : Finset (SPos P J N)} (hT : ValOnly T) :
    msgLab (L ∪ T) = msgLab L ∪ T := by
  ext s
  rw [Finset.mem_union, mem_msgLab, mem_msgLab]
  cases s with
  | val p => exact Finset.mem_union
  | dig m => simp only [InMsg, Finset.mem_union, hT.dig m, hT.str, hT.asg, or_false]
  | str j => simp only [InMsg, false_or, hT.str j]
  | asg m j => simp only [InMsg, false_or, hT.asg m j]

theorem msgStore_swapIn_val {L T : Finset (SPos P J N)} {σ : Store (S := SPos P J N) (SVal Ω)}
    (hL : StreamInv L σ) (hT : ValOnly T) (w : RevealVals (SVal Ω) T) :
    msgStore (L ∪ T) (swapIn T L w σ) = swapIn T (msgLab L) w (msgStore L σ) := by
  funext s
  cases s with
  | val p =>
    show swapIn T L w σ (.val p) = swapIn T (msgLab L) w (msgStore L σ) (.val p)
    unfold swapIn
    simp only [mem_msgLab_of_isVal (show (SPos.val p : SPos P J N).IsVal from trivial)]
    rfl
  | dig m =>
    have hm := markOf_union (oneMark_union_noAsg hL.one hT.asg) (hT.asg m)
    rw [swapIn_apply_of_notMem _ _ (hT.dig m)]
    rcases h : markOf L m with _ | j
    · rw [msgStore_dig_none (hm.trans h), msgStore_dig_none h,
        swapIn_apply_of_notMem _ _ (hT.dig m)]
    · rw [msgStore_dig_some (hm.trans h), msgStore_dig_some h,
        swapIn_apply_of_notMem _ _ (hT.str j)]
  | str j => exact (swapIn_apply_of_notMem _ _ (hT.str j)).symm
  | asg m j => exact (swapIn_apply_of_notMem _ _ (hT.asg m j)).symm

variable [Nonempty Ω]

omit [DecidableEq Ω] in
theorem agrees_msg_val {L T : Finset (SPos P J N)} (σ : Store (S := SPos P J N) (SVal Ω))
    (hT : ValOnly T) (w : RevealVals (SVal Ω) T) :
    Agrees T (msgLab L) (fill (msgStore L σ)) w ↔ Agrees T L (fill σ) w := by
  refine forall_congr' fun s ↦ ?_
  rw [mem_msgLab_of_isVal (hT _ s.2)]
  unfold fill
  rw [msgStore_of_isVal L σ (hT _ s.2)]

theorem sdiff_msgLab_val (L : Finset (SPos P J N)) {T : Finset (SPos P J N)} (hT : ValOnly T) :
    T \ msgLab L = T \ L := by
  ext s
  simp only [Finset.mem_sdiff]
  exact and_congr_right fun hs ↦ not_congr (mem_msgLab_of_isVal (hT _ hs))

omit [Nonempty Ω] in
theorem streamInv_swapIn_val {L T : Finset (SPos P J N)} {σ : Store (S := SPos P J N) (SVal Ω)}
    (hL : StreamInv L σ) (hT : ValOnly T) (w : RevealVals (SVal Ω) T) :
    StreamInv (L ∪ T) (swapIn T L w σ) where
  dom s hs := by
    rw [swapIn_apply_of_notMem _ _ fun h ↦ hs (Finset.mem_union_right _ h)]
    exact hL.dom s fun h ↦ hs (Finset.mem_union_left _ h)
  one := oneMark_union_noAsg hL.one hT.asg
  str j := by
    simp only [Finset.mem_union, hT.str j, or_false, hT.asg, (hL.str j)]
  used m j h := by
    rw [asgCount_union_noAsg hT.asg]
    exact hL.used m j ((Finset.mem_union.1 h).resolve_right (hT.asg m j))
  dig m h := by
    rw [asgCount_union_noAsg hT.asg]
    obtain ⟨h₁, h₂⟩ := hL.dig m ((Finset.mem_union.1 h).resolve_right (hT.dig m))
    exact ⟨h₁, fun j hj ↦ (Finset.mem_union.1 hj).elim (h₂ j) (hT.asg m j)⟩

/-! ### The digest reveal -/

omit [DecidableEq P] [DecidableEq J] [DecidableEq Ω] in
theorem fill_msgStore_dig_some {L : Finset (SPos P J N)} (σ : Store (S := SPos P J N) (SVal Ω))
    {m : J} {j : Fin N} (h : markOf L m = some j) :
    fill (msgStore L σ) (.dig m) = (fill σ (.str j) : Ω) := by
  unfold fill
  rw [msgStore_dig_some h]
  rfl

omit [DecidableEq P] [DecidableEq J] [DecidableEq Ω] in
theorem fill_msgStore_dig_none {L : Finset (SPos P J N)} (σ : Store (S := SPos P J N) (SVal Ω))
    {m : J} (h : markOf L m = none) : fill (msgStore L σ) (.dig m) = fill σ (.dig m) := by
  unfold fill
  rw [msgStore_dig_none h]

/-- The values on `T`, a default value off `T`. -/
noncomputable def extW {T : Finset (SPos P J N)} (w : RevealVals (SVal Ω) T) :
    (s : SPos P J N) → SVal Ω s :=
  fun s ↦ if h : s ∈ T then w ⟨s, h⟩ else Classical.arbitrary _

omit [DecidableEq Ω] in
theorem extW_of_mem {T : Finset (SPos P J N)} (w : RevealVals (SVal Ω) T) {s : SPos P J N}
    (h : s ∈ T) : extW w s = w ⟨s, h⟩ :=
  dite_eq_left h

/-- **The values on `T` and on `T'`** in bijection through an involution of the values that reads
`T` from `T'` and `T'` from `T`. -/
noncomputable def valsEquiv (T T' : Finset (SPos P J N))
    (φ : ((s : SPos P J N) → SVal Ω s) → (s : SPos P J N) → SVal Ω s) (hφ : ∀ v, φ (φ v) = v)
    (h₁ : ∀ v v', (∀ s ∈ T', v s = v' s) → ∀ s ∈ T, φ v s = φ v' s)
    (h₂ : ∀ v v', (∀ s ∈ T, v s = v' s) → ∀ s ∈ T', φ v s = φ v' s) :
    RevealVals (SVal Ω) T ≃ RevealVals (SVal Ω) T' where
  toFun w := restrictTo T' (φ (extW w))
  invFun w' := restrictTo T (φ (extW w'))
  left_inv w := funext fun s ↦ by
    show φ (extW (restrictTo T' (φ (extW w)))) s.1 = w s
    rw [h₁ _ (φ (extW w)) (fun s' hs' ↦ extW_of_mem _ hs') s.1 s.2, hφ, extW_of_mem _ s.2]
  right_inv w' := funext fun s ↦ by
    show φ (extW (restrictTo T (φ (extW w')))) s.1 = w' s
    rw [h₂ _ (φ (extW w')) (fun s' hs' ↦ extW_of_mem _ hs') s.1 s.2, hφ, extW_of_mem _ s.2]

/-- **The exchange of a message's digest and a stream entry** in the values. -/
def swapSD (j : Fin N) (msg : J) (v : (s : SPos P J N) → SVal Ω s) :
    (s : SPos P J N) → SVal Ω s
  | .val p => v (.val p)
  | .dig m => if m = msg then (v (.str j) : Ω) else v (.dig m)
  | .str j' => if j' = j then (v (.dig msg) : Ω) else v (.str j')
  | .asg m j' => v (.asg m j')

omit [DecidableEq P] [DecidableEq Ω] [Nonempty Ω] in
theorem swapSD_dig (j : Fin N) (msg : J) (v : (s : SPos P J N) → SVal Ω s) :
    swapSD j msg v (.dig msg) = (v (.str j) : Ω) := by
  simp only [swapSD]
  rfl

omit [DecidableEq P] [DecidableEq Ω] [Nonempty Ω] in
theorem swapSD_str (j : Fin N) (msg : J) (v : (s : SPos P J N) → SVal Ω s) :
    swapSD j msg v (.str j) = (v (.dig msg) : Ω) := by
  simp only [swapSD]
  rfl

omit [DecidableEq P] [DecidableEq Ω] [Nonempty Ω] in
theorem swapSD_swapSD (j : Fin N) (msg : J) (v : (s : SPos P J N) → SVal Ω s) :
    swapSD j msg (swapSD j msg v) = v := by
  funext s
  cases s with
  | val p => rfl
  | dig m =>
    by_cases h : m = msg
    · subst h
      rw [swapSD_dig, swapSD_str]
    · simp [swapSD, h]
  | str j' =>
    by_cases h : j' = j
    · subst h
      rw [swapSD_str, swapSD_dig]
    · simp [swapSD, h]
  | asg m j' => rfl

section entry

variable {T T' : Finset (SPos P J N)} {msg : J} {j : Fin N}

/-- **The values of a stream entry and of a message's digest** in bijection. -/
noncomputable def entryEquiv (hT : ∀ s, s ∈ T ↔ s = .str j ∨ s = .asg msg j)
    (hT' : ∀ s, s ∈ T' ↔ s = .dig msg) : RevealVals (SVal Ω) T ≃ RevealVals (SVal Ω) T' :=
  valsEquiv T T' (swapSD j msg) (swapSD_swapSD j msg)
    (fun v v' hv s hs ↦ by
      rcases (hT s).1 hs with rfl | rfl
      · rw [swapSD_str, swapSD_str, hv _ ((hT' _).2 rfl)]
      · exact Subsingleton.elim (α := Unit) _ _)
    (fun v v' hv s hs ↦ by
      obtain rfl := (hT' s).1 hs
      rw [swapSD_dig, swapSD_dig, hv _ ((hT _).2 (Or.inl rfl))])

omit [DecidableEq P] [DecidableEq J] in
theorem str_mem_of_entry (hT : ∀ s, s ∈ T ↔ s = .str j ∨ s = .asg msg j) : SPos.str j ∈ T :=
  (hT _).2 (Or.inl rfl)

omit [DecidableEq P] [DecidableEq J] in
theorem asg_mem_of_entry (hT : ∀ s, s ∈ T ↔ s = .str j ∨ s = .asg msg j) : SPos.asg msg j ∈ T :=
  (hT _).2 (Or.inr rfl)

omit [DecidableEq P] [DecidableEq J] in
theorem dig_mem_of_entry (hT' : ∀ s, s ∈ T' ↔ s = .dig msg) : SPos.dig msg ∈ T' :=
  (hT' _).2 rfl

omit [DecidableEq Ω] in
/-- The revealed digest of the hybrid side is the stream entry's value. -/
theorem entryEquiv_dig (hT : ∀ s, s ∈ T ↔ s = .str j ∨ s = .asg msg j)
    (hT' : ∀ s, s ∈ T' ↔ s = .dig msg) (w : RevealVals (SVal Ω) T) (h : SPos.dig msg ∈ T') :
    entryEquiv hT hT' w ⟨.dig msg, h⟩ = (w ⟨.str j, str_mem_of_entry hT⟩ : Ω) := by
  show swapSD j msg (extW w) (.dig msg) = _
  rw [swapSD_dig, extW_of_mem _ (str_mem_of_entry hT)]

variable {L₂ : Finset (SPos P J N)} {σ : Store (S := SPos P J N) (SVal Ω)}
  (hT : ∀ s, s ∈ T ↔ s = .str j ∨ s = .asg msg j) (hT' : ∀ s, s ∈ T' ↔ s = .dig msg)
  (hG : StreamInv L₂ σ)
  (hj : SPos.asg msg j ∈ L₂ ∨ ((∀ j', SPos.asg msg j' ∉ L₂) ∧ j.val = asgCount L₂))

include hT in
omit [DecidableEq P] [DecidableEq J] in
theorem entry_asg_mem (m : J) (j' : Fin N) : SPos.asg m j' ∈ T ↔ m = msg ∧ j' = j := by
  constructor
  · intro h
    rcases (hT _).1 h with h | h
    · cases h
    · exact SPos.asg.inj h
  · rintro ⟨rfl, rfl⟩
    exact asg_mem_of_entry hT

include hT in
omit [DecidableEq P] [DecidableEq J] in
theorem entry_str_mem (j' : Fin N) : SPos.str j' ∈ T ↔ j' = j := by
  constructor
  · intro h
    rcases (hT _).1 h with h | h
    · exact SPos.str.inj h
    · cases h
  · rintro rfl
    exact str_mem_of_entry hT

include hT' in
omit [DecidableEq P] [DecidableEq J] in
theorem entry_dig_mem' (m : J) : SPos.dig m ∈ T' ↔ m = msg := by
  constructor
  · intro h
    exact SPos.dig.inj ((hT' _).1 h)
  · rintro rfl
    exact dig_mem_of_entry hT'

include hT in
omit [DecidableEq P] [DecidableEq J] in
theorem entry_dig_notMem (m : J) : SPos.dig m ∉ T := fun h ↦ by
  rcases (hT _).1 h with h | h <;> cases h

include hT hG in
omit [DecidableEq P] [DecidableEq J] [DecidableEq Ω] [Nonempty Ω] in
theorem entry_marked_sub (hm : SPos.asg msg j ∈ L₂) : T ⊆ L₂ := fun s hs ↦ by
  rcases (hT s).1 hs with rfl | rfl
  · exact (hG.str j).2 ⟨msg, hm⟩
  · exact hm

include hT' hG in
omit [DecidableEq Ω] [Nonempty Ω] in
theorem entry_marked_sub' (hm : SPos.asg msg j ∈ L₂) : T' ⊆ msgLab L₂ := fun s hs ↦ by
  obtain rfl := (hT' s).1 hs
  exact mem_msgLab.2 (Or.inr ⟨j, hm, (hG.str j).2 ⟨msg, hm⟩⟩)

include hT hG in
omit [DecidableEq P] [DecidableEq J] [DecidableEq Ω] [Nonempty Ω] in
theorem entry_new_disj (hfree : ∀ j', SPos.asg msg j' ∉ L₂) (hc : j.val = asgCount L₂) :
    ∀ s ∈ T, s ∉ L₂ := fun s hs ↦ by
  rcases (hT s).1 hs with rfl | rfl
  · intro h
    obtain ⟨m', hm'⟩ := (hG.str j).1 h
    exact absurd (hG.used m' j hm') (by omega)
  · exact hfree j

include hT' hG in
omit [DecidableEq Ω] [Nonempty Ω] in
theorem entry_new_disj' (hfree : ∀ j', SPos.asg msg j' ∉ L₂) (hc : j.val = asgCount L₂) :
    ∀ s ∈ T', s ∉ msgLab L₂ := fun s hs h ↦ by
  obtain rfl := (hT' s).1 hs
  exact Or.elim (mem_msgLab.1 h) (fun h ↦ absurd (hG.dig msg h).1 (by have := j.isLt; omega))
    fun ⟨j', ha, _⟩ ↦ hfree j' ha

include hT hG in
omit [DecidableEq Ω] [Nonempty Ω] in
theorem oneMark_union_entry (hfree : ∀ j', SPos.asg msg j' ∉ L₂) : OneMark (L₂ ∪ T) :=
  fun m a b ha hb ↦ by
    rcases Finset.mem_union.1 ha with ha | ha <;> rcases Finset.mem_union.1 hb with hb | hb
    · exact hG.one m a b ha hb
    · obtain ⟨rfl, -⟩ := (entry_asg_mem hT m b).1 hb
      exact absurd ha (hfree a)
    · obtain ⟨rfl, -⟩ := (entry_asg_mem hT m a).1 ha
      exact absurd hb (hfree b)
    · exact ((entry_asg_mem hT m a).1 ha).2.trans ((entry_asg_mem hT m b).1 hb).2.symm

include hT in
theorem asgCount_union_entry (hfree : SPos.asg msg j ∉ L₂) :
    asgCount (L₂ ∪ T) = asgCount L₂ + 1 := by
  have hf : T.filter (fun s ↦ s.isAsg = true) = {SPos.asg msg j} := by
    ext s
    rw [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hs, ha⟩
      rcases (hT s).1 hs with rfl | rfl
      · cases ha
      · rfl
    · rintro rfl
      exact ⟨asg_mem_of_entry hT, rfl⟩
  unfold asgCount
  rw [Finset.filter_union, hf, Finset.card_union_of_disjoint
    (Finset.disjoint_singleton_right.2 fun h ↦ hfree (Finset.mem_filter.1 h).1),
    Finset.card_singleton]

include hT hT' hG hj in
omit [DecidableEq Ω] [Nonempty Ω] in
/-- The digest reveal grows the renamed label by the message's digest. -/
theorem msgLab_union_entry : msgLab (L₂ ∪ T) = msgLab L₂ ∪ T' := by
  ext s
  rw [Finset.mem_union, mem_msgLab, mem_msgLab]
  cases s with
  | val p =>
    show SPos.val p ∈ L₂ ∪ T ↔ SPos.val p ∈ L₂ ∨ SPos.val p ∈ T'
    rw [Finset.mem_union]
    refine or_congr_right (iff_of_false (fun h ↦ ?_) fun h ↦ ?_)
    · rcases (hT _).1 h with h | h <;> cases h
    · cases (hT' _).1 h
  | str j' =>
    refine iff_of_false id fun h ↦ h.elim id fun h ↦ ?_
    cases (hT' _).1 h
  | asg m j' =>
    refine iff_of_false id fun h ↦ h.elim id fun h ↦ ?_
    cases (hT' _).1 h
  | dig m =>
    show (SPos.dig m ∈ L₂ ∪ T ∨ ∃ j', SPos.asg m j' ∈ L₂ ∪ T ∧ SPos.str j' ∈ L₂ ∪ T) ↔
      (SPos.dig m ∈ L₂ ∨ ∃ j', SPos.asg m j' ∈ L₂ ∧ SPos.str j' ∈ L₂) ∨ SPos.dig m ∈ T'
    rw [entry_dig_mem' hT']
    constructor
    · rintro (h | ⟨j', ha, hs⟩)
      · exact Or.inl (Or.inl ((Finset.mem_union.1 h).resolve_right (entry_dig_notMem hT m)))
      · rcases Finset.mem_union.1 ha with ha | ha
        · rcases Finset.mem_union.1 hs with hs | hs
          · exact Or.inl (Or.inr ⟨j', ha, hs⟩)
          · obtain rfl := (entry_str_mem hT j').1 hs
            rcases hj with hj | ⟨-, hc⟩
            · exact Or.inl (Or.inr ⟨_, ha, (hG.str _).2 ⟨m, ha⟩⟩)
            · exact absurd (hG.used m _ ha) (by omega)
        · exact Or.inr ((entry_asg_mem hT m j').1 ha).1
    · rintro ((h | ⟨j', ha, hs⟩) | hm)
      · exact Or.inl (Finset.mem_union_left _ h)
      · exact Or.inr ⟨j', Finset.mem_union_left _ ha, Finset.mem_union_left _ hs⟩
      · exact Or.inr ⟨j, Finset.mem_union_right _ ((entry_asg_mem hT m j).2 ⟨hm, rfl⟩),
          Finset.mem_union_right _ (str_mem_of_entry hT)⟩

include hT hT' hG hj in
/-- The digest reveal and the renaming of the stores. -/
theorem msgStore_swapIn_entry (w : RevealVals (SVal Ω) T) :
    msgStore (L₂ ∪ T) (swapIn T L₂ w σ) =
      swapIn T' (msgLab L₂) (entryEquiv hT hT' w) (msgStore L₂ σ) := by
  rcases hj with hj | ⟨hfree, hc⟩
  · rw [Finset.union_eq_left.2 (entry_marked_sub hT hG hj),
      swapIn_of_subset _ _ (entry_marked_sub hT hG hj),
      swapIn_of_subset _ _ (entry_marked_sub' hT' hG hj)]
  have hone := oneMark_union_entry hT hG hfree
  have hnT' : ∀ {s : SPos P J N}, s ≠ .dig msg → s ∉ T' := fun hs h ↦ hs ((hT' _).1 h)
  funext s
  cases s with
  | val p =>
    show swapIn T L₂ w σ (.val p) = _
    rw [swapIn_apply_of_notMem _ _ (fun h ↦ by rcases (hT _).1 h with h | h <;> cases h),
      swapIn_apply_of_notMem _ _ (hnT' fun h ↦ by cases h)]
    rfl
  | str j' => exact (swapIn_apply_of_notMem _ _ (hnT' fun h ↦ by cases h)).symm
  | asg m j' => exact (swapIn_apply_of_notMem _ _ (hnT' fun h ↦ by cases h)).symm
  | dig m =>
    by_cases hm : m = msg
    · subst hm
      have hsL : SPos.str j ∉ L₂ := entry_new_disj hT hG hfree hc _ (str_mem_of_entry hT)
      have hdM : SPos.dig m ∉ msgLab L₂ :=
        entry_new_disj' hT' hG hfree hc _ (dig_mem_of_entry hT')
      have hdL : SPos.dig m ∉ L₂ := fun h ↦ hdM (mem_msgLab.2 (Or.inl h))
      rw [msgStore_dig_some (markOf_of_mem hone
          (Finset.mem_union_right _ (asg_mem_of_entry hT))),
        swapIn_apply_new w (str_mem_of_entry hT) hsL (hG.dom _ hsL),
        swapIn_apply_new _ (dig_mem_of_entry hT') hdM
          (by rw [msgStore_dig_none (markOf_of_free hfree)]; exact hG.dom _ hdL),
        entryEquiv_dig]
      rfl
    · have hmk := markOf_union hone (fun j' h ↦ hm ((entry_asg_mem hT m j').1 h).1)
      rw [swapIn_apply_of_notMem _ _ fun h ↦ hm ((entry_dig_mem' hT' m).1 h)]
      rcases h : markOf L₂ m with _ | j'
      · rw [msgStore_dig_none (hmk.trans h), msgStore_dig_none h,
          swapIn_apply_of_notMem _ _ (entry_dig_notMem hT m)]
      · have hj' : j' ≠ j := fun e ↦ by
          subst e
          exact absurd (hG.used m _ (mem_of_markOf h)) (by omega)
        rw [msgStore_dig_some (hmk.trans h), msgStore_dig_some h,
          swapIn_apply_of_notMem _ _ fun h' ↦ hj' ((entry_str_mem hT j').1 h')]

include hT hT' hG hj in
omit [DecidableEq Ω] in
/-- The digest reveal agrees with the store exactly when its renaming agrees with the renamed
store. -/
theorem agrees_entry (w : RevealVals (SVal Ω) T) :
    Agrees T' (msgLab L₂) (fill (msgStore L₂ σ)) (entryEquiv hT hT' w) ↔
      Agrees T L₂ (fill σ) w := by
  rcases hj with hj | ⟨hfree, hc⟩
  · have hmk : markOf L₂ msg = some j := markOf_of_mem hG.one hj
    constructor
    · rintro hA ⟨s, hs⟩ -
      rcases (hT s).1 hs with rfl | rfl
      · have := hA ⟨_, dig_mem_of_entry hT'⟩ (entry_marked_sub' hT' hG hj (dig_mem_of_entry hT'))
        rw [entryEquiv_dig, fill_msgStore_dig_some σ hmk] at this
        exact this
      · exact Subsingleton.elim (α := Unit) _ _
    · rintro hA ⟨s, hs⟩ -
      obtain rfl := (hT' s).1 hs
      rw [entryEquiv_dig, fill_msgStore_dig_some σ hmk]
      exact hA ⟨_, str_mem_of_entry hT⟩ (entry_marked_sub hT hG hj (str_mem_of_entry hT))
  · exact iff_of_true (fun s hs ↦ absurd hs (entry_new_disj' hT' hG hfree hc s.1 s.2))
      fun s hs ↦ absurd hs (entry_new_disj hT hG hfree hc s.1 s.2)

include hT hT' hG hj in
omit [DecidableEq Ω] in
/-- The digest reveal samples as many new values as its renaming. -/
theorem card_entry [Fintype Ω] :
    Fintype.card (RevealVals (SVal Ω) (T' \ msgLab L₂)) =
      Fintype.card (RevealVals (SVal Ω) (T \ L₂)) := by
  rcases hj with hj | ⟨hfree, hc⟩
  · rw [Finset.sdiff_eq_empty_iff_subset.2 (entry_marked_sub' hT' hG hj),
      Finset.sdiff_eq_empty_iff_subset.2 (entry_marked_sub hT hG hj)]
  · rw [Finset.sdiff_eq_self_of_disjoint
        (Finset.disjoint_left.2 (entry_new_disj' hT' hG hfree hc)),
      Finset.sdiff_eq_self_of_disjoint (Finset.disjoint_left.2 (entry_new_disj hT hG hfree hc))]
    exact (Fintype.card_congr (entryEquiv hT hT')).symm

include hT hG hj in
omit [Nonempty Ω] in
/-- The digest reveal keeps the stream invariant. -/
theorem streamInv_entry (w : RevealVals (SVal Ω) T) : StreamInv (L₂ ∪ T) (swapIn T L₂ w σ) := by
  rcases hj with hj | ⟨hfree, hc⟩
  · rw [Finset.union_eq_left.2 (entry_marked_sub hT hG hj),
      swapIn_of_subset _ _ (entry_marked_sub hT hG hj)]
    exact hG
  have hcount := asgCount_union_entry hT (hfree j)
  refine ⟨fun s hs ↦ ?_, oneMark_union_entry hT hG hfree, fun j' ↦ ?_, fun m j' h ↦ ?_,
    fun m h ↦ ?_⟩
  · rw [swapIn_apply_of_notMem _ _ fun h ↦ hs (Finset.mem_union_right _ h)]
    exact hG.dom s fun h ↦ hs (Finset.mem_union_left _ h)
  · rw [Finset.mem_union, entry_str_mem hT]
    constructor
    · rintro (h | rfl)
      · obtain ⟨m, hm⟩ := (hG.str j').1 h
        exact ⟨m, Finset.mem_union_left _ hm⟩
      · exact ⟨msg, Finset.mem_union_right _ (asg_mem_of_entry hT)⟩
    · rintro ⟨m, hm⟩
      rcases Finset.mem_union.1 hm with hm | hm
      · exact Or.inl ((hG.str j').2 ⟨m, hm⟩)
      · exact Or.inr ((entry_asg_mem hT m j').1 hm).2
  · rw [hcount]
    rcases Finset.mem_union.1 h with h | h
    · have := hG.used m j' h
      omega
    · obtain ⟨-, rfl⟩ := (entry_asg_mem hT m j').1 h
      omega
  · have hd := (Finset.mem_union.1 h).resolve_right (entry_dig_notMem hT m)
    exact absurd (hG.dig m hd).1 (by have := j.isLt; omega)

end entry

section fallback

variable {T T' : Finset (SPos P J N)} {msg : J}

/-- The values of a fallback digest reveal, identically. -/
noncomputable def fallEquiv (hT : ∀ s, s ∈ T ↔ s = .dig msg) (hT' : ∀ s, s ∈ T' ↔ s = .dig msg) :
    RevealVals (SVal Ω) T ≃ RevealVals (SVal Ω) T' :=
  valsEquiv T T' id (fun _ ↦ rfl) (fun _ _ hv s hs ↦ hv s ((hT' s).2 ((hT s).1 hs)))
    (fun _ _ hv s hs ↦ hv s ((hT s).2 ((hT' s).1 hs)))

omit [DecidableEq Ω] in
theorem fallEquiv_apply (hT : ∀ s, s ∈ T ↔ s = .dig msg) (hT' : ∀ s, s ∈ T' ↔ s = .dig msg)
    (w : RevealVals (SVal Ω) T) (s : SPos P J N) (h : s ∈ T') :
    fallEquiv hT hT' w ⟨s, h⟩ = w ⟨s, (hT s).2 ((hT' s).1 h)⟩ :=
  extW_of_mem w _

variable {L₂ : Finset (SPos P J N)} {σ : Store (S := SPos P J N) (SVal Ω)}
  (hT : ∀ s, s ∈ T ↔ s = .dig msg) (hT' : ∀ s, s ∈ T' ↔ s = .dig msg) (hG : StreamInv L₂ σ)
  (hfree : ∀ j, SPos.asg msg j ∉ L₂) (hN : N ≤ asgCount L₂)

include hT in
omit [DecidableEq P] [DecidableEq J] in
theorem fall_asg_notMem (m : J) (j : Fin N) : SPos.asg m j ∉ T := fun h ↦ by
  cases (hT _).1 h

include hT in
omit [DecidableEq P] [DecidableEq J] in
theorem fall_str_notMem (j : Fin N) : SPos.str j ∉ T := fun h ↦ by
  cases (hT _).1 h

include hT in
omit [DecidableEq P] [DecidableEq J] in
theorem fall_dig_mem (m : J) : SPos.dig m ∈ T ↔ m = msg := by
  constructor
  · intro h
    exact SPos.dig.inj ((hT _).1 h)
  · rintro rfl
    exact (hT _).2 rfl

include hfree in
theorem fall_mem_msgLab : SPos.dig msg ∈ msgLab L₂ ↔ SPos.dig msg ∈ L₂ :=
  ⟨fun h ↦ Or.elim (mem_msgLab.1 h) id fun ⟨j', ha, _⟩ ↦ absurd ha (hfree j'),
    fun h ↦ mem_msgLab.2 (Or.inl h)⟩

include hT hT' in
/-- The fallback reveal grows the renamed label by the same digest. -/
theorem msgLab_union_fall : msgLab (L₂ ∪ T) = msgLab L₂ ∪ T' := by
  ext s
  rw [Finset.mem_union, mem_msgLab, mem_msgLab]
  cases s with
  | val p =>
    show SPos.val p ∈ L₂ ∪ T ↔ SPos.val p ∈ L₂ ∨ SPos.val p ∈ T'
    rw [Finset.mem_union]
    refine or_congr_right (iff_of_false (fun h ↦ ?_) fun h ↦ ?_)
    · cases (hT _).1 h
    · cases (hT' _).1 h
  | str j' =>
    refine iff_of_false id fun h ↦ h.elim id fun h ↦ ?_
    cases (hT' _).1 h
  | asg m j' =>
    refine iff_of_false id fun h ↦ h.elim id fun h ↦ ?_
    cases (hT' _).1 h
  | dig m =>
    show (SPos.dig m ∈ L₂ ∪ T ∨ ∃ j', SPos.asg m j' ∈ L₂ ∪ T ∧ SPos.str j' ∈ L₂ ∪ T) ↔
      (SPos.dig m ∈ L₂ ∨ ∃ j', SPos.asg m j' ∈ L₂ ∧ SPos.str j' ∈ L₂) ∨ SPos.dig m ∈ T'
    have hTT : SPos.dig m ∈ T ↔ SPos.dig m ∈ T' := by rw [hT, hT']
    simp only [Finset.mem_union, fall_asg_notMem hT, fall_str_notMem hT, or_false, hTT]
    exact or_right_comm

include hT hT' hG hfree in
/-- The fallback reveal and the renaming of the stores. -/
theorem msgStore_swapIn_fall (w : RevealVals (SVal Ω) T) :
    msgStore (L₂ ∪ T) (swapIn T L₂ w σ) =
      swapIn T' (msgLab L₂) (fallEquiv hT hT' w) (msgStore L₂ σ) := by
  have hone := oneMark_union_noAsg hG.one (fall_asg_notMem hT)
  have hnT' : ∀ {s : SPos P J N}, s ≠ .dig msg → s ∉ T' := fun hs h ↦ hs ((hT' _).1 h)
  funext s
  cases s with
  | val p =>
    show swapIn T L₂ w σ (.val p) = _
    rw [swapIn_apply_of_notMem _ _ (fun h ↦ by cases (hT _).1 h),
      swapIn_apply_of_notMem _ _ (hnT' fun h ↦ by cases h)]
    rfl
  | str j' => exact (swapIn_apply_of_notMem _ _ (hnT' fun h ↦ by cases h)).symm
  | asg m j' => exact (swapIn_apply_of_notMem _ _ (hnT' fun h ↦ by cases h)).symm
  | dig m =>
    have hmk := markOf_union hone (fall_asg_notMem hT m)
    by_cases hm : m = msg
    · subst hm
      have hf : markOf L₂ m = none := markOf_of_free hfree
      have hdT := (fall_dig_mem hT m).2 rfl
      have hdT' : SPos.dig m ∈ T' := (hT' _).2 ((hT _).1 hdT)
      rw [msgStore_dig_none (hmk.trans hf)]
      by_cases hd : SPos.dig m ∈ L₂
      · rw [swapIn_apply_of_memL _ _ hd, swapIn_apply_of_memL _ _ ((fall_mem_msgLab hfree).2 hd),
          msgStore_dig_none hf]
      · rw [swapIn_apply_of_mem _ _ hdT hd,
          swapIn_apply_of_mem _ _ hdT' fun h ↦ hd ((fall_mem_msgLab hfree).1 h),
          msgStore_dig_none hf, fallEquiv_apply]
    · have hdT : SPos.dig m ∉ T := fun h ↦ hm ((fall_dig_mem hT m).1 h)
      rw [swapIn_apply_of_notMem _ _ fun h ↦ hdT ((hT _).2 ((hT' _).1 h))]
      rcases h : markOf L₂ m with _ | j'
      · rw [msgStore_dig_none (hmk.trans h), msgStore_dig_none h,
          swapIn_apply_of_notMem _ _ hdT]
      · rw [msgStore_dig_some (hmk.trans h), msgStore_dig_some h,
          swapIn_apply_of_notMem _ _ (fall_str_notMem hT j')]

include hT hT' hfree in
omit [DecidableEq Ω] in
theorem agrees_fall (w : RevealVals (SVal Ω) T) :
    Agrees T' (msgLab L₂) (fill (msgStore L₂ σ)) (fallEquiv hT hT' w) ↔
      Agrees T L₂ (fill σ) w := by
  have hmk : markOf L₂ msg = none := markOf_of_free hfree
  constructor
  · rintro hA ⟨s, hs⟩ hsL
    obtain rfl := (hT _).1 hs
    have := hA ⟨_, (hT' _).2 rfl⟩ ((fall_mem_msgLab hfree).2 hsL)
    rw [fallEquiv_apply, fill_msgStore_dig_none σ hmk] at this
    exact this
  · rintro hA ⟨s, hs⟩ hsL
    obtain rfl := (hT' _).1 hs
    rw [fallEquiv_apply, fill_msgStore_dig_none σ hmk]
    exact hA _ ((fall_mem_msgLab hfree).1 hsL)

include hT hT' hfree in
omit [DecidableEq Ω] [Nonempty Ω] in
theorem card_fall [Fintype Ω] :
    Fintype.card (RevealVals (SVal Ω) (T' \ msgLab L₂)) =
      Fintype.card (RevealVals (SVal Ω) (T \ L₂)) := by
  have h : T' \ msgLab L₂ = T \ L₂ := by
    ext s
    rw [Finset.mem_sdiff, Finset.mem_sdiff, hT, hT']
    refine and_congr_right fun hs ↦ not_congr ?_
    subst hs
    exact fall_mem_msgLab hfree
  rw [h]

include hT hG hfree hN in
omit [Nonempty Ω] in
theorem streamInv_fall (w : RevealVals (SVal Ω) T) : StreamInv (L₂ ∪ T) (swapIn T L₂ w σ) := by
  refine ⟨fun s hs ↦ ?_, oneMark_union_noAsg hG.one (fall_asg_notMem hT), fun j' ↦ ?_,
    fun m j' h ↦ ?_, fun m h ↦ ?_⟩
  · rw [swapIn_apply_of_notMem _ _ fun h ↦ hs (Finset.mem_union_right _ h)]
    exact hG.dom s fun h ↦ hs (Finset.mem_union_left _ h)
  · simp only [Finset.mem_union, fall_str_notMem hT, fall_asg_notMem hT, or_false]
    exact hG.str j'
  · rw [asgCount_union_noAsg (fall_asg_notMem hT)]
    exact hG.used m j' ((Finset.mem_union.1 h).resolve_right (fall_asg_notMem hT m j'))
  · rw [asgCount_union_noAsg (fall_asg_notMem hT)]
    rcases Finset.mem_union.1 h with h | h
    · obtain ⟨h₁, h₂⟩ := hG.dig m h
      exact ⟨h₁, fun j hj ↦ (Finset.mem_union.1 hj).elim (h₂ j) (fall_asg_notMem hT m j)⟩
    · obtain rfl := (fall_dig_mem hT m).1 h
      exact ⟨hN, fun j hj ↦ (Finset.mem_union.1 hj).elim (hfree j) (fall_asg_notMem hT _ j)⟩

end fallback

end rename

/-! ## The renaming simulation of the reveals -/

section sim

variable {P J : Type} {N : ℕ} [DecidableEq P] [DecidableEq J] {Ω : Type} [Fintype Ω]
  [DecidableEq Ω] [Nonempty Ω] {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z]
  [DecidableEq Z] {M : Type} {good : LazyProg X Z (SPos P J N) (SVal Ω) → Prop}

/-- **A reveal of base coordinates** is simulated by itself. -/
theorem renSim_revealThen_val {Q : Finset (SPos P J N) → Prop} {B C : QReg} {α : Type}
    {T : Finset (SPos P J N)} (hT : ValOnly T)
    {k k' : RevealVals (SVal Ω) T × (Finset (SPos P J N) × M) →
      QComp (tmplSpec X Z (SPos P J N) (SVal Ω) M good) B C α}
    (h : ∀ w L₁ m, Q L₁ → RenSim msgLab msgStore StreamInv (fun L' ↦ L' = L₁ ∪ T)
      (k (w, (L₁, m))) (k' (w, (msgLab L₁, m)))) :
    RenSim msgLab msgStore StreamInv Q (revealThen good T k) (revealThen good T k') :=
  renSim_revealThen T T (fun _ ↦ Equiv.refl _) (fun L₁ _ _ _ ↦ msgLab_union_val L₁ hT)
    (fun _ _ w _ hG _ ↦ msgStore_swapIn_val hG hT w) (fun _ σ w _ _ ↦ agrees_msg_val σ hT w)
    (fun L₁ _ _ _ ↦ by rw [sdiff_msgLab_val L₁ hT])
    (fun _ _ w _ hG _ ↦ streamInv_swapIn_val hG hT w) h

/-- **The digest reveal at a stream entry**: the event side reveals entry `j` of the stream and
its mark (`streamIdx L msg = some j`), the hybrid side the digest of `msg`, from the label
`L ∪ U` after a reveal `U` without marks; the values correspond by `entryEquiv`. -/
theorem renSim_revealEntry {L U : Finset (SPos P J N)} (hU : ∀ m j, SPos.asg m j ∉ U) {msg : J}
    {j : Fin N} (hs : streamIdx L msg = some j) {B C : QReg} {α : Type}
    {k : RevealVals (SVal Ω) (strNeed L msg) × (Finset (SPos P J N) × M) →
      QComp (tmplSpec X Z (SPos P J N) (SVal Ω) M good) B C α}
    {k' : RevealVals (SVal Ω) (msgNeed msg) × (Finset (SPos P J N) × M) →
      QComp (tmplSpec X Z (SPos P J N) (SVal Ω) M good) B C α}
    (h : ∀ w L₂ m, L₂ = L ∪ U → RenSim msgLab msgStore StreamInv
      (fun L' ↦ L' = L₂ ∪ strNeed L msg) (k (w, (L₂, m)))
      (k' (entryEquiv (mem_strNeed_some hs) (mem_msgNeed msg) w, (msgLab L₂, m)))) :
    RenSim msgLab msgStore StreamInv (fun L' ↦ L' = L ∪ U) (revealThen good (strNeed L msg) k)
      (revealThen good (msgNeed msg) k') := by
  have hT := mem_strNeed_some hs
  have hT' := mem_msgNeed (P := P) (N := N) msg
  have hj := streamIdx_some_facts hs hU
  exact renSim_revealThen _ _ (fun _ ↦ entryEquiv hT hT')
    (fun _ _ hL hG ↦ by subst hL; exact msgLab_union_entry hT hT' hG hj)
    (fun _ _ w hL hG _ ↦ by subst hL; exact msgStore_swapIn_entry hT hT' hG hj w)
    (fun _ _ w hL hG ↦ by subst hL; exact agrees_entry hT hT' hG hj w)
    (fun _ _ hL hG ↦ by subst hL; exact card_entry hT hT' hG hj)
    (fun _ _ w hL hG _ ↦ by subst hL; exact streamInv_entry hT hG hj w) h

/-- **The digest reveal past the stream** (`streamIdx L msg = none`): both sides reveal the digest
of `msg`, from the label `L ∪ U` after a reveal `U` without marks. -/
theorem renSim_revealFall {L U : Finset (SPos P J N)} (hU : ∀ m j, SPos.asg m j ∉ U) {msg : J}
    (hs : streamIdx L msg = none) {B C : QReg} {α : Type}
    {k : RevealVals (SVal Ω) (strNeed L msg) × (Finset (SPos P J N) × M) →
      QComp (tmplSpec X Z (SPos P J N) (SVal Ω) M good) B C α}
    {k' : RevealVals (SVal Ω) (msgNeed msg) × (Finset (SPos P J N) × M) →
      QComp (tmplSpec X Z (SPos P J N) (SVal Ω) M good) B C α}
    (h : ∀ w L₂ m, L₂ = L ∪ U → RenSim msgLab msgStore StreamInv
      (fun L' ↦ L' = L₂ ∪ strNeed L msg) (k (w, (L₂, m)))
      (k' (fallEquiv (mem_strNeed_none hs) (mem_msgNeed msg) w, (msgLab L₂, m)))) :
    RenSim msgLab msgStore StreamInv (fun L' ↦ L' = L ∪ U) (revealThen good (strNeed L msg) k)
      (revealThen good (msgNeed msg) k') := by
  have hT := mem_strNeed_none hs
  have hT' := mem_msgNeed (P := P) (N := N) msg
  obtain ⟨hfree, hN⟩ := streamIdx_none_facts hs hU
  exact renSim_revealThen _ _ (fun _ ↦ fallEquiv hT hT')
    (fun _ _ _ _ ↦ msgLab_union_fall hT hT')
    (fun _ _ w hL hG _ ↦ by subst hL; exact msgStore_swapIn_fall hT hT' hG hfree w)
    (fun _ _ w hL _ ↦ by subst hL; exact agrees_fall hT hT' hfree w)
    (fun _ _ hL _ ↦ by subst hL; exact card_fall hT hT' hfree)
    (fun _ _ w hL hG _ ↦ by subst hL; exact streamInv_fall hT hG hfree hN w) h

omit [Fintype Ω] [DecidableEq Ω] in
/-- **After the digest reveal at a stream entry**, the renamed store holds the entry's value as
the digest of `msg`. -/
theorem fill_msgStore_dig_entry {L L₁ : Finset (SPos P J N)} {msg : J} {j : Fin N}
    (hs : streamIdx L msg = some j) (hL : strNeed L msg ⊆ L₁)
    {σ : Store (S := SPos P J N) (SVal Ω)} (hG : StreamInv L₁ σ) :
    fill (msgStore L₁ σ) (.dig msg) = (fill σ (.str j) : Ω) :=
  fill_msgStore_dig_some σ (markOf_of_mem hG.one (hL ((mem_strNeed_some hs _).2 (Or.inr rfl))))

omit [Fintype Ω] [DecidableEq P] [DecidableEq J] [DecidableEq Ω] in
/-- **After the digest reveal past the stream**, the renamed store holds the same digest. -/
theorem fill_msgStore_dig_fall {L₁ : Finset (SPos P J N)} {msg : J}
    {σ : Store (S := SPos P J N) (SVal Ω)} (hG : StreamInv L₁ σ) (hd : SPos.dig msg ∈ L₁) :
    fill (msgStore L₁ σ) (.dig msg) = fill σ (.dig msg) :=
  fill_msgStore_dig_none σ (markOf_of_free (hG.dig msg hd).2)

omit [Fintype Ω] [DecidableEq P] [DecidableEq J] [DecidableEq Ω] [Fintype X] [DecidableEq X]
  [Fintype Z] [DecidableEq Z] in
/-- Program ports at base coordinates are simulated by themselves. -/
theorem portSim_self {Q : Finset (SPos P J N) → Prop} {p : LazyProg X Z (SPos P J N) (SVal Ω)}
    (hp : ValOnly p.need) : PortSim (msgStore (Ω := Ω)) StreamInv Q p p := by
  have key : ∀ {T : Finset (SPos P J N)}, ValOnly T →
      ∀ L (σ : Store (S := SPos P J N) (SVal Ω)),
      restrictTo T (fill σ) = restrictTo T (fill (msgStore L σ)) := fun hT L σ ↦
    funext fun s ↦ by
      show fill σ s.1 = fill (msgStore L σ) s.1
      unfold fill
      rw [msgStore_of_isVal L σ (hT _ s.2)]
  cases p with
  | programH T c => exact .progH T T c c fun L σ _ _ ↦ congrArg c (key hp L σ)
  | programK T c => exact .progK T T c c fun L σ _ _ ↦ congrArg c (key hp L σ)
  | programK' T c => exact .progK' T T c c fun L σ _ _ ↦ congrArg c (key hp L σ)

end sim

/-! ## S★: the stream's static disclosures -/

section star

variable {P J : Type} {N : ℕ} [DecidableEq P] [DecidableEq J]

/-- **The stream held by the values**: entry `j` at the coordinate `.str j`. -/
def streamOf {Ω : Type} (v : (s : SPos P J N) → SVal Ω s) : Fin N → Ω :=
  fun j ↦ v (.str j)

/-- The digest coordinates of a label: the stream entries and the fallback digests. -/
def SPos.IsDigest : SPos P J N → Prop
  | .dig _ => True
  | .str _ => True
  | _ => False

omit [DecidableEq P] [DecidableEq J] in
/-- Without a fallback reveal, every digest coordinate of the event side's label is a revealed
stream entry. -/
theorem SPos.isDigest_str {L : Finset (SPos P J N)} (hfall : ∀ m, SPos.dig m ∉ L)
    {s : SPos P J N} (hs : s ∈ L) (hd : s.IsDigest) : ∃ j, s = .str j := by
  cases s with
  | str j => exact ⟨j, rfl⟩
  | dig m => exact absurd hs (hfall m)
  | _ => exact absurd hd id

omit [DecidableEq P] [DecidableEq J] in
/-- No fallback reveal while the stream is not used up. -/
theorem dig_notMem_of_lt {Ω : Type} {L : Finset (SPos P J N)}
    {σ : Store (S := SPos P J N) (SVal Ω)} (hG : StreamInv L σ) (h : asgCount L < N) (m : J) :
    SPos.dig m ∉ L :=
  fun hd ↦ absurd (hG.dig m hd).1 (by omega)

omit [DecidableEq P] [DecidableEq J] in
/-- **The revealed digests are disclosed by S★**: without a fallback reveal (fewer distinct
signed messages than stream entries), every set of views of digest values revealed at the label
`L` discloses no more than the static `starCover (streamOf v)`. -/
theorem revealed_subset_streamCover {L : Finset (SPos P J N)} (hfall : ∀ m, SPos.dig m ∉ L)
    (v : (s : SPos P J N) → SVal (HashOutput × HashOutput) s) {W : Finset View}
    (hW : ∀ w ∈ W, ∃ s ∈ L, ∃ hs : s.IsDigest, w = pairView (by
      cases s with
      | val _ => exact absurd hs id
      | dig m => exact v (.dig m)
      | str j => exact v (.str j)
      | asg _ _ => exact absurd hs id)) :
    ofViews W ≤ starCover (streamOf v) :=
  ofViews_le_revealed _ fun w hw ↦ by
    obtain ⟨s, hs, hd, rfl⟩ := hW w hw
    obtain ⟨j, rfl⟩ := SPos.isDigest_str hfall hs hd
    exact ⟨j, rfl⟩

/-- A stream entry's view is covered by S★. -/
theorem covered_starCover {n : ℕ} (d : Fin n → HashOutput × HashOutput) (j : Fin n) :
    Covered (starCover d) (pairView (d j)) :=
  (Quantum.Sphincs.covered_revealed_iff _ _ _).2 fun _ ↦ ⟨j, rfl, rfl⟩

variable [Fintype P] [Fintype J]

/-- The coordinates other than stream entries. -/
def SPos.NotStr : SPos P J N → Prop
  | .str _ => False
  | _ => True

/-- The values as the stream and the rest. -/
noncomputable def streamSplit (Ω : Type) :
    ((s : SPos P J N) → SVal Ω s) ≃ (Fin N → Ω) × ((s : {s : SPos P J N // s.NotStr}) → SVal Ω s.1)
    where
  toFun v := (streamOf v, fun s ↦ v s.1)
  invFun r
    | .val p => r.2 ⟨.val p, trivial⟩
    | .dig m => r.2 ⟨.dig m, trivial⟩
    | .str j => r.1 j
    | .asg m j => r.2 ⟨.asg m j, trivial⟩
  left_inv v := funext fun s ↦ by cases s <;> rfl
  right_inv r := Prod.ext rfl (funext fun ⟨s, hs⟩ ↦ by
    cases s with
    | str j => exact absurd hs id
    | _ => rfl)

/-- **The stream of uniform values is uniform**: averaging over the values a function of the
stream averages over the stream. -/
theorem uavg_streamOf {Ω : Type} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    (g : (Fin N → Ω) → ℝ≥0∞) :
    uavg (fun v : (s : SPos P J N) → SVal Ω s ↦ g (streamOf v)) = uavg g := by
  classical
  calc uavg (fun v : (s : SPos P J N) → SVal Ω s ↦ g (streamOf v))
      = uavg (fun v ↦ (fun r : (Fin N → Ω) × ((s : {s : SPos P J N // s.NotStr}) → SVal Ω s.1) ↦
          g r.1) (streamSplit Ω v)) := rfl
    _ = uavg (fun r : (Fin N → Ω) × ((s : {s : SPos P J N // s.NotStr}) → SVal Ω s.1) ↦
          g r.1) := uavg_comp_equiv (streamSplit Ω) fun r ↦ g r.1
    _ = uavg g := uavg_comp_fst g

/-- **Minkowski over S★ on the template values**: with the per-call instability
`2^-128 + price S★`, `S★ = starCover (streamOf v)`, the mean over the values of `(a + √(c ε))²` is
at most `(a + √(c (2^-128 + rhoCov / 2^128)))²`. -/
theorem uavg_sq_add_sqrt_starCover_streamOf_le
    (a c : ℝ≥0∞) :
    uavg (fun v : (s : SPos P J signatureLimit) → SVal (HashOutput × HashOutput) s ↦
        (a + (c * ((2 ^ 128)⁻¹ + ENNReal.ofReal (price (starCover (streamOf v))))) ^
          (2⁻¹ : ℝ)) ^ 2) ≤
      (a + (c * ((2 ^ 128)⁻¹ + ENNReal.ofReal (rhoCov / 2 ^ 128))) ^ (2⁻¹ : ℝ)) ^ 2 :=
  (uavg_streamOf fun d ↦
    (a + (c * ((2 ^ 128)⁻¹ + ENNReal.ofReal (price (starCover d)))) ^ (2⁻¹ : ℝ)) ^ 2).trans_le
    (uavg_sq_add_sqrt_starCover_le a c)

end star

end Quantum.Qrom.Sphincs

end
