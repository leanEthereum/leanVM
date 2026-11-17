module

public import Quantum.Qrom.Sphincs.Stream

@[expose] public section

/-!
# The digest streams of `n` users

The `n`-user template coordinates are `Fin n × SPos P J N` with values `fun a ↦ SVal Ω a.2`: user
`i` holds a copy of the single-user coordinates (`Quantum.Qrom.Sphincs.Stream`), in particular its
own digest stream `(i, .str j)`. The renaming of the event side's labels and stores renames each
user's part by the single-user `msgLab`, `msgStore` (`msgLabN`, `msgStoreN`), with the invariant
`StreamInvN` (`StreamInv` per user).

* `atU i T`: user `i`'s copy of single-user coordinates; `labU L i`: user `i`'s part of a label.
* The renaming simulation of the reveals: `renSim_revealThen_valN` (base coordinates of any users),
  `renSim_revealEntryN`, `renSim_revealFallN` (user `i`'s digest reveal at the stream index of
  `labU L i`), all through `renSim_revealAtU` (a single-user simulated reveal at user `i`).
  `portSim_selfN`, `fill_msgStoreN_dig_entry`, `fill_msgStoreN_dig_fall`.
* `streamsOf v`: the users' streams; uniform under uniform values (`uavg_streamsOf`).
-/

open Finset
open scoped ENNReal
open Quantum.Sig (Store swapIn fill Agrees)
open Quantum.Xmss.Assembly (RevealVals revealThen tmplSpec)
open Quantum.Xmss.Hybrid (LazyProg restrictTo uavg)
open Quantum.Sphincs.Assembly (RenSim PortSim renSim_revealThen)
open Quantum.Sphincs (uavg_comp_equiv)

namespace Quantum.Qrom.Sphincs.Multi

/-! ## User coordinates -/

section coords

variable {n : ℕ} {P J : Type} {N : ℕ}

/-- User `i`'s copy of the single-user coordinates `T`. -/
def atU (i : Fin n) (T : Finset (SPos P J N)) : Finset (Fin n × SPos P J N) :=
  {i} ×ˢ T

theorem mem_atU_iff {i : Fin n} {T : Finset (SPos P J N)} {a : Fin n × SPos P J N} :
    a ∈ atU i T ↔ a.1 = i ∧ a.2 ∈ T := by
  simp only [atU, Finset.mem_product, Finset.mem_singleton]

theorem mem_atU {i j : Fin n} {T : Finset (SPos P J N)} {s : SPos P J N} :
    (j, s) ∈ atU i T ↔ j = i ∧ s ∈ T :=
  mem_atU_iff

theorem mk_mem_atU (i : Fin n) {T : Finset (SPos P J N)} {s : SPos P J N} (h : s ∈ T) :
    (i, s) ∈ atU i T :=
  mem_atU.2 ⟨rfl, h⟩

theorem atU_mono (i : Fin n) {T T' : Finset (SPos P J N)} (h : T ⊆ T') : atU i T ⊆ atU i T' :=
  Finset.product_subset_product_right h

theorem atU_union [DecidableEq P] [DecidableEq J] (i : Fin n) (T T' : Finset (SPos P J N)) :
    atU i (T ∪ T') = atU i T ∪ atU i T' :=
  Finset.product_union

/-- User `i`'s part of a label. -/
def labU [DecidableEq P] [DecidableEq J] (L : Finset (Fin n × SPos P J N)) (i : Fin n) :
    Finset (SPos P J N) :=
  (L.filter fun a ↦ a.1 = i).image Prod.snd

theorem mem_labU [DecidableEq P] [DecidableEq J] {L : Finset (Fin n × SPos P J N)} {i : Fin n}
    {s : SPos P J N} : s ∈ labU L i ↔ (i, s) ∈ L := by
  unfold labU
  rw [Finset.mem_image]
  constructor
  · rintro ⟨⟨j, t⟩, ht, rfl⟩
    obtain ⟨h, rfl⟩ := Finset.mem_filter.1 ht
    exact h
  · intro h
    exact ⟨(i, s), Finset.mem_filter.2 ⟨h, rfl⟩, rfl⟩

/-- User `i`'s values. -/
def SValsN.user {Ω : Type} (v : (a : Fin n × SPos P J N) → SVal Ω a.2) (i : Fin n) :
    (s : SPos P J N) → SVal Ω s :=
  fun s ↦ v (i, s)

/-- The values on `T`, a default value off `T`. -/
noncomputable def extWN {Ω : Type} [Nonempty Ω] {T : Finset (Fin n × SPos P J N)}
    (w : RevealVals (fun a : Fin n × SPos P J N ↦ SVal Ω a.2) T) :
    (a : Fin n × SPos P J N) → SVal Ω a.2 :=
  fun a ↦ @dite _ (a ∈ T) (Classical.propDecidable _) (fun h ↦ w ⟨a, h⟩)
    fun _ ↦ Classical.arbitrary _

theorem extWN_of_mem {Ω : Type} [Nonempty Ω] {T : Finset (Fin n × SPos P J N)}
    (w : RevealVals (fun a : Fin n × SPos P J N ↦ SVal Ω a.2) T) {a : Fin n × SPos P J N}
    (h : a ∈ T) : extWN w a = w ⟨a, h⟩ :=
  dite_eq_left h

end coords

/-! ## Labels -/

section labels

variable {n : ℕ} {P J : Type} {N : ℕ} [DecidableEq P] [DecidableEq J]

theorem labU_union (L L' : Finset (Fin n × SPos P J N)) (i : Fin n) :
    labU (L ∪ L') i = labU L i ∪ labU L' i := by
  ext s
  rw [Finset.mem_union, mem_labU, mem_labU, mem_labU, Finset.mem_union]

theorem labU_union_atU_self (L : Finset (Fin n × SPos P J N)) (i : Fin n)
    (T : Finset (SPos P J N)) : labU (L ∪ atU i T) i = labU L i ∪ T := by
  ext s
  rw [mem_labU, Finset.mem_union, Finset.mem_union, mem_labU, mem_atU]
  exact or_congr_right (and_iff_right rfl)

theorem labU_union_atU_of_ne (L : Finset (Fin n × SPos P J N)) {i j : Fin n} (h : j ≠ i)
    (T : Finset (SPos P J N)) : labU (L ∪ atU i T) j = labU L j := by
  ext s
  rw [mem_labU, Finset.mem_union, mem_labU, mem_atU]
  exact or_iff_left fun h' ↦ h h'.1

theorem labU_empty (i : Fin n) : labU (∅ : Finset (Fin n × SPos P J N)) i = ∅ := by
  ext s
  rw [mem_labU]
  simp only [Finset.notMem_empty]

theorem atU_sdiff (i : Fin n) (T : Finset (SPos P J N)) (L : Finset (Fin n × SPos P J N)) :
    atU i T \ L = atU i (T \ labU L i) := by
  ext ⟨j, s⟩
  rw [Finset.mem_sdiff, mem_atU, mem_atU, Finset.mem_sdiff, mem_labU]
  constructor
  · rintro ⟨⟨rfl, h₁⟩, h₂⟩
    exact ⟨rfl, h₁, h₂⟩
  · rintro ⟨rfl, h₁, h₂⟩
    exact ⟨⟨rfl, h₁⟩, h₂⟩

/-- **Base coordinates only**, of any users. -/
def ValOnlyN (T : Finset (Fin n × SPos P J N)) : Prop :=
  ∀ a ∈ T, a.2.IsVal

theorem ValOnlyN.user {T : Finset (Fin n × SPos P J N)} (hT : ValOnlyN T) (i : Fin n) :
    ValOnly (labU T i) :=
  fun _ hs ↦ hT _ (mem_labU.1 hs)

omit [DecidableEq P] [DecidableEq J] in
theorem ValOnlyN.asg {T : Finset (Fin n × SPos P J N)} (hT : ValOnlyN T) (i : Fin n) (m : J)
    (j : Fin N) : (i, SPos.asg m j) ∉ T :=
  fun h ↦ hT _ h

omit [DecidableEq P] [DecidableEq J] in
theorem valOnlyN_atU (i : Fin n) {T : Finset (SPos P J N)} (hT : ValOnly T) :
    ValOnlyN (atU i T) :=
  fun _ ha ↦ hT _ (mem_atU_iff.1 ha).2

omit [DecidableEq P] [DecidableEq J] in
theorem valOnlyN_prod (s : Finset (Fin n)) {T : Finset (SPos P J N)} (hT : ValOnly T) :
    ValOnlyN (s ×ˢ T) :=
  fun _ ha ↦ hT _ (Finset.mem_product.1 ha).2

theorem valOnlyN_union {T T' : Finset (Fin n × SPos P J N)} (hT : ValOnlyN T)
    (hT' : ValOnlyN T') : ValOnlyN (T ∪ T') :=
  fun a ha ↦ (Finset.mem_union.1 ha).elim (hT a) (hT' a)

theorem valOnlyN_biUnion {ι : Type} (s : Finset ι) {t : ι → Finset (Fin n × SPos P J N)}
    (h : ∀ i ∈ s, ValOnlyN (t i)) : ValOnlyN (s.biUnion t) := fun a ha ↦ by
  obtain ⟨i, hi, ha⟩ := Finset.mem_biUnion.1 ha
  exact h i hi a ha

end labels

/-! ## The renaming of all users' labels and stores -/

section rename

variable {n : ℕ} {P J : Type} {N : ℕ} [DecidableEq P] [DecidableEq J] {Ω : Type}

/-- User `i`'s part of a store. -/
def storeU (σ : Store (S := Fin n × SPos P J N) fun a ↦ SVal Ω a.2) (i : Fin n) :
    Store (S := SPos P J N) (SVal Ω) :=
  fun s ↦ σ (i, s)

/-- **The renamed label**: user `i`'s part renamed by `msgLab`. -/
@[irreducible]
noncomputable def msgLabN (L : Finset (Fin n × SPos P J N)) : Finset (Fin n × SPos P J N) :=
  Finset.univ.biUnion fun i ↦ atU i (msgLab (labU L i))

theorem mem_msgLabN {L : Finset (Fin n × SPos P J N)} {i : Fin n} {s : SPos P J N} :
    (i, s) ∈ msgLabN L ↔ s ∈ msgLab (labU L i) := by
  unfold msgLabN
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨j, -, h⟩
    obtain ⟨rfl, h⟩ := mem_atU.1 h
    exact h
  · intro h
    exact ⟨i, Finset.mem_univ _, mk_mem_atU i h⟩

theorem labU_msgLabN (L : Finset (Fin n × SPos P J N)) (i : Fin n) :
    labU (msgLabN L) i = msgLab (labU L i) := by
  ext s
  rw [mem_labU, mem_msgLabN]

theorem mem_msgLabN_of_isVal {L : Finset (Fin n × SPos P J N)} {a : Fin n × SPos P J N}
    (ha : a.2.IsVal) : a ∈ msgLabN L ↔ a ∈ L := by
  obtain ⟨i, s⟩ := a
  rw [mem_msgLabN, mem_msgLab_of_isVal ha, mem_labU]

/-- **The renamed store**: user `i`'s part renamed by `msgStore` at user `i`'s label. -/
noncomputable def msgStoreN (L : Finset (Fin n × SPos P J N))
    (σ : Store (S := Fin n × SPos P J N) fun a ↦ SVal Ω a.2) :
    Store (S := Fin n × SPos P J N) fun a ↦ SVal Ω a.2 :=
  fun a ↦ msgStore (labU L a.1) (storeU σ a.1) a.2

theorem storeU_msgStoreN (L : Finset (Fin n × SPos P J N))
    (σ : Store (S := Fin n × SPos P J N) fun a ↦ SVal Ω a.2) (i : Fin n) :
    storeU (msgStoreN L σ) i = msgStore (labU L i) (storeU σ i) :=
  rfl

/-- **The stream invariant of all users**: `StreamInv` of each user's part. -/
structure StreamInvN (L : Finset (Fin n × SPos P J N))
    (σ : Store (S := Fin n × SPos P J N) fun a ↦ SVal Ω a.2) : Prop where
  user : ∀ i, StreamInv (labU L i) (storeU σ i)

theorem streamInvN_empty :
    StreamInvN (∅ : Finset (Fin n × SPos P J N))
      (fun _ ↦ none : Store (S := Fin n × SPos P J N) fun a ↦ SVal Ω a.2) :=
  ⟨fun i ↦ by
    rw [labU_empty]
    exact streamInv_empty⟩

theorem msgLabN_empty : msgLabN (∅ : Finset (Fin n × SPos P J N)) = ∅ := by
  ext ⟨i, s⟩
  rw [mem_msgLabN, labU_empty, msgLab_empty]
  simp only [Finset.notMem_empty]

theorem msgStoreN_empty :
    msgStoreN (∅ : Finset (Fin n × SPos P J N))
      (fun _ ↦ none : Store (S := Fin n × SPos P J N) fun a ↦ SVal Ω a.2) = fun _ ↦ none := by
  funext ⟨i, s⟩
  show msgStore (labU ∅ i) (fun _ ↦ none) s = none
  rw [labU_empty, msgStore_empty]

/-- User `i`'s part of the values of a reveal. -/
def restrictU {T : Finset (Fin n × SPos P J N)}
    (w : RevealVals (fun a : Fin n × SPos P J N ↦ SVal Ω a.2) T) (i : Fin n) :
    RevealVals (SVal Ω) (labU T i) :=
  fun s ↦ w ⟨(i, s.1), mem_labU.1 s.2⟩

/-- The values of a reveal of user `i`'s copy, as single-user values. -/
def ofAtU {i : Fin n} {T : Finset (SPos P J N)}
    (w : RevealVals (fun a : Fin n × SPos P J N ↦ SVal Ω a.2) (atU i T)) :
    RevealVals (SVal Ω) T :=
  fun s ↦ w ⟨(i, s.1), mk_mem_atU i s.2⟩

omit [DecidableEq P] [DecidableEq J] in
/-- Single-user values on `T` and the values on user `i`'s copy. -/
def atUEquiv (i : Fin n) (T : Finset (SPos P J N)) :
    RevealVals (SVal Ω) T ≃ RevealVals (fun a : Fin n × SPos P J N ↦ SVal Ω a.2) (atU i T) where
  toFun w a := w ⟨a.1.2, (mem_atU_iff.1 a.2).2⟩
  invFun := ofAtU
  left_inv _ := rfl
  right_inv w := funext fun a ↦ by
    obtain ⟨⟨j, s⟩, ha⟩ := a
    obtain ⟨rfl, -⟩ := mem_atU.1 ha
    rfl

omit [DecidableEq P] [DecidableEq J] in
/-- A single-user equivalence of reveal values, at user `i`'s copy. -/
def liftU (i : Fin n) {T T' : Finset (SPos P J N)}
    (e : RevealVals (SVal Ω) T ≃ RevealVals (SVal Ω) T') :
    RevealVals (fun a : Fin n × SPos P J N ↦ SVal Ω a.2) (atU i T) ≃
      RevealVals (fun a : Fin n × SPos P J N ↦ SVal Ω a.2) (atU i T') :=
  ((atUEquiv i T).symm.trans e).trans (atUEquiv i T')

omit [DecidableEq P] [DecidableEq J] in
theorem ofAtU_liftU (i : Fin n) {T T' : Finset (SPos P J N)}
    (e : RevealVals (SVal Ω) T ≃ RevealVals (SVal Ω) T')
    (w : RevealVals (fun a : Fin n × SPos P J N ↦ SVal Ω a.2) (atU i T)) :
    ofAtU (liftU i e w) = e (ofAtU w) :=
  (atUEquiv i T').symm_apply_apply _

omit [DecidableEq P] [DecidableEq J] in
theorem liftU_apply (i : Fin n) {T T' : Finset (SPos P J N)}
    (e : RevealVals (SVal Ω) T ≃ RevealVals (SVal Ω) T')
    (w : RevealVals (fun a : Fin n × SPos P J N ↦ SVal Ω a.2) (atU i T)) {s : SPos P J N}
    (h : (i, s) ∈ atU i T') : liftU i e w ⟨(i, s), h⟩ = e (ofAtU w) ⟨s, (mem_atU.1 h).2⟩ :=
  rfl

theorem card_atU_sdiff [Fintype Ω] (i : Fin n) (T : Finset (SPos P J N))
    (L : Finset (Fin n × SPos P J N)) :
    Fintype.card (RevealVals (fun a : Fin n × SPos P J N ↦ SVal Ω a.2) (atU i T \ L)) =
      Fintype.card (RevealVals (SVal Ω) (T \ labU L i)) :=
  (Fintype.card_congr' (congrArg (RevealVals fun a : Fin n × SPos P J N ↦ SVal Ω a.2)
    (atU_sdiff i T L))).trans (Fintype.card_congr (atUEquiv i (T \ labU L i)).symm)

theorem agrees_atU [Nonempty Ω] {i : Fin n} {T : Finset (SPos P J N)}
    {L : Finset (Fin n × SPos P J N)} {f : (a : Fin n × SPos P J N) → SVal Ω a.2}
    {w : RevealVals (fun a : Fin n × SPos P J N ↦ SVal Ω a.2) (atU i T)} :
    Agrees (atU i T) L f w ↔ Agrees T (labU L i) (fun s ↦ f (i, s)) (ofAtU w) := by
  constructor
  · intro h s hs
    exact h ⟨(i, s.1), mk_mem_atU i s.2⟩ (mem_labU.1 hs)
  · rintro h ⟨⟨j, s⟩, ha⟩ hs
    obtain ⟨rfl, hs'⟩ := mem_atU.1 ha
    exact h ⟨s, hs'⟩ (mem_labU.2 hs)

variable [DecidableEq Ω]

theorem storeU_swapIn (T L : Finset (Fin n × SPos P J N))
    (w : RevealVals (fun a : Fin n × SPos P J N ↦ SVal Ω a.2) T)
    (σ : Store (S := Fin n × SPos P J N) fun a ↦ SVal Ω a.2) (i : Fin n) :
    storeU (swapIn T L w σ) i = swapIn (labU T i) (labU L i) (restrictU w i) (storeU σ i) := by
  funext s
  by_cases h : (i, s) ∈ T ∧ (i, s) ∉ L
  · have h' : s ∈ labU T i ∧ s ∉ labU L i := ⟨mem_labU.2 h.1, fun h' ↦ h.2 (mem_labU.1 h')⟩
    simp only [storeU, swapIn, dite_eq_left h, dite_eq_left h', restrictU]
  · have h' : ¬(s ∈ labU T i ∧ s ∉ labU L i) := fun h' ↦
      h ⟨mem_labU.1 h'.1, fun h'' ↦ h'.2 (mem_labU.2 h'')⟩
    simp only [storeU, swapIn, dite_eq_right h, dite_eq_right h']

theorem storeU_swapIn_atU {i : Fin n} {T : Finset (SPos P J N)}
    (L : Finset (Fin n × SPos P J N))
    (w : RevealVals (fun a : Fin n × SPos P J N ↦ SVal Ω a.2) (atU i T))
    (σ : Store (S := Fin n × SPos P J N) fun a ↦ SVal Ω a.2) :
    storeU (swapIn (atU i T) L w σ) i = swapIn T (labU L i) (ofAtU w) (storeU σ i) := by
  funext s
  by_cases h : (i, s) ∈ atU i T ∧ (i, s) ∉ L
  · have h' : s ∈ T ∧ s ∉ labU L i := ⟨(mem_atU.1 h.1).2, fun h' ↦ h.2 (mem_labU.1 h')⟩
    simp only [storeU, swapIn, dite_eq_left h, dite_eq_left h', ofAtU]
  · have h' : ¬(s ∈ T ∧ s ∉ labU L i) := fun h' ↦
      h ⟨mk_mem_atU i h'.1, fun h'' ↦ h'.2 (mem_labU.2 h'')⟩
    simp only [storeU, swapIn, dite_eq_right h, dite_eq_right h']

theorem storeU_swapIn_atU_of_ne {i j : Fin n} (hj : j ≠ i) {T : Finset (SPos P J N)}
    (L : Finset (Fin n × SPos P J N))
    (w : RevealVals (fun a : Fin n × SPos P J N ↦ SVal Ω a.2) (atU i T))
    (σ : Store (S := Fin n × SPos P J N) fun a ↦ SVal Ω a.2) :
    storeU (swapIn (atU i T) L w σ) j = storeU σ j := by
  funext s
  have h : ¬((j, s) ∈ atU i T ∧ (j, s) ∉ L) := fun h ↦ hj (mem_atU.1 h.1).1
  simp only [storeU, swapIn, dite_eq_right h]

/-! ### Reveals of base coordinates -/

theorem msgLabN_union_val (L : Finset (Fin n × SPos P J N)) {T : Finset (Fin n × SPos P J N)}
    (hT : ValOnlyN T) : msgLabN (L ∪ T) = msgLabN L ∪ T := by
  ext ⟨i, s⟩
  rw [mem_msgLabN, labU_union, msgLab_union_val _ (hT.user i), Finset.mem_union,
    Finset.mem_union, mem_msgLabN, mem_labU]

theorem msgStoreN_swapIn_val {L T : Finset (Fin n × SPos P J N)}
    {σ : Store (S := Fin n × SPos P J N) fun a ↦ SVal Ω a.2} (hL : StreamInvN L σ)
    (hT : ValOnlyN T) (w : RevealVals (fun a : Fin n × SPos P J N ↦ SVal Ω a.2) T) :
    msgStoreN (L ∪ T) (swapIn T L w σ) = swapIn T (msgLabN L) w (msgStoreN L σ) := by
  funext ⟨i, s⟩
  show storeU (msgStoreN (L ∪ T) (swapIn T L w σ)) i s =
    storeU (swapIn T (msgLabN L) w (msgStoreN L σ)) i s
  rw [storeU_msgStoreN, labU_union, storeU_swapIn, storeU_swapIn,
    msgStore_swapIn_val (hL.user i) (hT.user i), labU_msgLabN, storeU_msgStoreN]

theorem streamInvN_swapIn_val {L T : Finset (Fin n × SPos P J N)}
    {σ : Store (S := Fin n × SPos P J N) fun a ↦ SVal Ω a.2} (hL : StreamInvN L σ)
    (hT : ValOnlyN T) (w : RevealVals (fun a : Fin n × SPos P J N ↦ SVal Ω a.2) T) :
    StreamInvN (L ∪ T) (swapIn T L w σ) :=
  ⟨fun i ↦ by
    rw [labU_union, storeU_swapIn]
    exact streamInv_swapIn_val (hL.user i) (hT.user i) _⟩

omit [DecidableEq Ω] in
theorem sdiff_msgLabN_val (L : Finset (Fin n × SPos P J N)) {T : Finset (Fin n × SPos P J N)}
    (hT : ValOnlyN T) : T \ msgLabN L = T \ L := by
  ext a
  simp only [Finset.mem_sdiff]
  exact and_congr_right fun ha ↦ not_congr (mem_msgLabN_of_isVal (hT _ ha))

variable [Nonempty Ω]

omit [DecidableEq Ω] in
theorem fill_msgStoreN_of_isVal (L : Finset (Fin n × SPos P J N))
    (σ : Store (S := Fin n × SPos P J N) fun a ↦ SVal Ω a.2) {a : Fin n × SPos P J N}
    (ha : a.2.IsVal) : fill (msgStoreN L σ) a = fill σ a := by
  obtain ⟨i, s⟩ := a
  exact congrArg (fun o ↦ Option.getD o (Classical.arbitrary _))
    (msgStore_of_isVal (labU L i) (storeU σ i) ha)

omit [DecidableEq Ω] in
theorem agreesN_msg_val {L T : Finset (Fin n × SPos P J N)}
    (σ : Store (S := Fin n × SPos P J N) fun a ↦ SVal Ω a.2) (hT : ValOnlyN T)
    (w : RevealVals (fun a : Fin n × SPos P J N ↦ SVal Ω a.2) T) :
    Agrees T (msgLabN L) (fill (msgStoreN L σ)) w ↔ Agrees T L (fill σ) w := by
  refine forall_congr' fun a ↦ ?_
  rw [mem_msgLabN_of_isVal (hT _ a.2), fill_msgStoreN_of_isVal L σ (hT _ a.2)]

omit [DecidableEq Ω] in
/-- **After user `i`'s digest reveal at a stream entry**, the renamed store holds the entry's
value as user `i`'s digest of `msg`. -/
theorem fill_msgStoreN_dig_entry {L₀ : Finset (SPos P J N)} {L₁ : Finset (Fin n × SPos P J N)}
    {i : Fin n} {msg : J} {j : Fin N} (hs : streamIdx L₀ msg = some j)
    (hL : atU i (strNeed L₀ msg) ⊆ L₁) {σ : Store (S := Fin n × SPos P J N) fun a ↦ SVal Ω a.2}
    (hG : StreamInvN L₁ σ) :
    fill (msgStoreN L₁ σ) (i, .dig msg) = (fill σ (i, .str j) : Ω) :=
  fill_msgStore_dig_entry hs (fun _ hs' ↦ mem_labU.2 (hL (mk_mem_atU i hs'))) (hG.user i)

omit [DecidableEq Ω] in
/-- **After user `i`'s digest reveal past the stream**, the renamed store holds the same
digest. -/
theorem fill_msgStoreN_dig_fall {L₁ : Finset (Fin n × SPos P J N)} {i : Fin n} {msg : J}
    {σ : Store (S := Fin n × SPos P J N) fun a ↦ SVal Ω a.2} (hG : StreamInvN L₁ σ)
    (hd : (i, SPos.dig msg) ∈ L₁) :
    fill (msgStoreN L₁ σ) (i, .dig msg) = fill σ (i, .dig msg) :=
  fill_msgStore_dig_fall (hG.user i) (mem_labU.2 hd)

/-- The values of user `i`'s digest reveal at a stream entry and of user `i`'s digest. -/
noncomputable def entryEquivN (i : Fin n) {L₀ : Finset (SPos P J N)} {msg : J} {j : Fin N}
    (hs : streamIdx L₀ msg = some j) :
    RevealVals (fun a : Fin n × SPos P J N ↦ SVal Ω a.2) (atU i (strNeed L₀ msg)) ≃
      RevealVals (fun a : Fin n × SPos P J N ↦ SVal Ω a.2) (atU i (msgNeed msg)) :=
  liftU i (entryEquiv (mem_strNeed_some hs) (mem_msgNeed msg))

omit [DecidableEq Ω] in
/-- User `i`'s revealed digest of the hybrid side is user `i`'s stream entry's value. -/
theorem entryEquivN_dig (i : Fin n) {L₀ : Finset (SPos P J N)} {msg : J} {j : Fin N}
    (hs : streamIdx L₀ msg = some j)
    (w : RevealVals (fun a : Fin n × SPos P J N ↦ SVal Ω a.2) (atU i (strNeed L₀ msg)))
    (h : (i, SPos.dig msg) ∈ atU i (msgNeed msg)) :
    entryEquivN i hs w ⟨(i, .dig msg), h⟩ =
      (w ⟨(i, .str j), mk_mem_atU i (str_mem_of_entry (mem_strNeed_some hs))⟩ : Ω) :=
  entryEquiv_dig (mem_strNeed_some hs) (mem_msgNeed msg) (ofAtU w) (mem_atU.1 h).2

/-- The values of user `i`'s digest reveal past the stream, identically. -/
noncomputable def fallEquivN (i : Fin n) {L₀ : Finset (SPos P J N)} {msg : J}
    (hs : streamIdx L₀ msg = none) :
    RevealVals (fun a : Fin n × SPos P J N ↦ SVal Ω a.2) (atU i (strNeed L₀ msg)) ≃
      RevealVals (fun a : Fin n × SPos P J N ↦ SVal Ω a.2) (atU i (msgNeed msg)) :=
  liftU i (fallEquiv (mem_strNeed_none hs) (mem_msgNeed msg))

omit [DecidableEq Ω] in
theorem fallEquivN_dig (i : Fin n) {L₀ : Finset (SPos P J N)} {msg : J}
    (hs : streamIdx L₀ msg = none)
    (w : RevealVals (fun a : Fin n × SPos P J N ↦ SVal Ω a.2) (atU i (strNeed L₀ msg)))
    (h : (i, SPos.dig msg) ∈ atU i (msgNeed msg)) :
    fallEquivN i hs w ⟨(i, .dig msg), h⟩ =
      w ⟨(i, .dig msg), mk_mem_atU i ((mem_strNeed_none hs _).2 rfl)⟩ :=
  fallEquiv_apply (mem_strNeed_none hs) (mem_msgNeed msg) (ofAtU w) _ _

end rename

/-! ## The renaming simulation of the reveals -/

section sim

variable {n : ℕ} {P J : Type} {N : ℕ} [DecidableEq P] [DecidableEq J] {Ω : Type} [Fintype Ω]
  [DecidableEq Ω] [Nonempty Ω] {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z]
  [DecidableEq Z] {M : Type}
  {good : LazyProg X Z (Fin n × SPos P J N) (fun a ↦ SVal Ω a.2) → Prop}

/-- **A single-user simulated reveal at user `i`'s copy**: the reveals of `atU i T` and
`atU i T'` with values related by `f` lifted to user `i`, when the single-user renaming of user
`i`'s label and store follows the reveal. -/
theorem renSim_revealAtU (i : Fin n) {Q : Finset (Fin n × SPos P J N) → Prop} {B C : QReg}
    {α : Type} (T T' : Finset (SPos P J N))
    (f : Finset (SPos P J N) → RevealVals (SVal Ω) T ≃ RevealVals (SVal Ω) T')
    {k : RevealVals (fun a : Fin n × SPos P J N ↦ SVal Ω a.2) (atU i T) ×
        (Finset (Fin n × SPos P J N) × M) →
      QComp (tmplSpec X Z (Fin n × SPos P J N) (fun a ↦ SVal Ω a.2) M good) B C α}
    {k' : RevealVals (fun a : Fin n × SPos P J N ↦ SVal Ω a.2) (atU i T') ×
        (Finset (Fin n × SPos P J N) × M) →
      QComp (tmplSpec X Z (Fin n × SPos P J N) (fun a ↦ SVal Ω a.2) M good) B C α}
    (hrl : ∀ L₁ σ, Q L₁ → StreamInvN (Ω := Ω) L₁ σ →
      msgLab (labU L₁ i ∪ T) = msgLab (labU L₁ i) ∪ T')
    (hrs : ∀ L₁ σ w, Q L₁ → StreamInvN (Ω := Ω) L₁ σ →
      Agrees T (labU L₁ i) (fill (storeU σ i)) w →
      msgStore (labU L₁ i ∪ T) (swapIn T (labU L₁ i) w (storeU σ i)) =
        swapIn T' (msgLab (labU L₁ i)) (f (labU L₁ i) w) (msgStore (labU L₁ i) (storeU σ i)))
    (hag : ∀ L₁ σ w, Q L₁ → StreamInvN (Ω := Ω) L₁ σ →
      (Agrees T' (msgLab (labU L₁ i)) (fill (msgStore (labU L₁ i) (storeU σ i)))
          (f (labU L₁ i) w) ↔
        Agrees T (labU L₁ i) (fill (storeU σ i)) w))
    (hcard : ∀ L₁ σ, Q L₁ → StreamInvN (Ω := Ω) L₁ σ →
      Fintype.card (RevealVals (SVal Ω) (T' \ msgLab (labU L₁ i))) =
        Fintype.card (RevealVals (SVal Ω) (T \ labU L₁ i)))
    (hG : ∀ L₁ σ w, Q L₁ → StreamInvN (Ω := Ω) L₁ σ →
      Agrees T (labU L₁ i) (fill (storeU σ i)) w →
      StreamInv (labU L₁ i ∪ T) (swapIn T (labU L₁ i) w (storeU σ i)))
    (h : ∀ w L₁ m, Q L₁ → RenSim msgLabN msgStoreN StreamInvN (fun L' ↦ L' = L₁ ∪ atU i T)
      (k (w, (L₁, m))) (k' (liftU i (f (labU L₁ i)) w, (msgLabN L₁, m)))) :
    RenSim msgLabN msgStoreN StreamInvN Q (revealThen good (atU i T) k)
      (revealThen good (atU i T') k') := by
  refine renSim_revealThen (atU i T) (atU i T') (fun L₁ ↦ liftU i (f (labU L₁ i))) ?_ ?_ ?_ ?_
    ?_ h
  · intro L₁ σ hQ hG'
    ext ⟨j, s⟩
    rw [Finset.mem_union, mem_msgLabN, mem_msgLabN, mem_atU]
    by_cases hj : j = i
    · subst hj
      rw [labU_union_atU_self, hrl L₁ σ hQ hG', Finset.mem_union]
      exact or_congr_right (and_iff_right rfl).symm
    · rw [labU_union_atU_of_ne _ hj]
      exact (or_iff_left fun h' ↦ hj h'.1).symm
  · intro L₁ σ w hQ hG' hA
    funext ⟨j, s⟩
    show storeU (msgStoreN (L₁ ∪ atU i T) (swapIn (atU i T) L₁ w σ)) j s =
      storeU (swapIn (atU i T') (msgLabN L₁) (liftU i (f (labU L₁ i)) w) (msgStoreN L₁ σ)) j s
    by_cases hj : j = i
    · subst hj
      rw [storeU_msgStoreN, storeU_swapIn_atU, storeU_swapIn_atU, labU_union_atU_self,
        hrs L₁ σ (ofAtU w) hQ hG' (agrees_atU.1 hA), ofAtU_liftU, labU_msgLabN,
        storeU_msgStoreN]
    · rw [storeU_msgStoreN, storeU_swapIn_atU_of_ne hj, storeU_swapIn_atU_of_ne hj,
        labU_union_atU_of_ne _ hj, storeU_msgStoreN]
  · intro L₁ σ w hQ hG'
    rw [agrees_atU, agrees_atU, ofAtU_liftU, labU_msgLabN]
    exact hag L₁ σ (ofAtU w) hQ hG'
  · intro L₁ σ hQ hG'
    rw [card_atU_sdiff, card_atU_sdiff, labU_msgLabN]
    exact hcard L₁ σ hQ hG'
  · intro L₁ σ w hQ hG' hA
    refine ⟨fun j ↦ ?_⟩
    by_cases hj : j = i
    · subst hj
      rw [labU_union_atU_self, storeU_swapIn_atU]
      exact hG L₁ σ (ofAtU w) hQ hG' (agrees_atU.1 hA)
    · rw [labU_union_atU_of_ne _ hj, storeU_swapIn_atU_of_ne hj]
      exact hG'.user j

/-- **A reveal of base coordinates** of any users is simulated by itself. -/
theorem renSim_revealThen_valN {Q : Finset (Fin n × SPos P J N) → Prop} {B C : QReg} {α : Type}
    {T : Finset (Fin n × SPos P J N)} (hT : ValOnlyN T)
    {k k' : RevealVals (fun a : Fin n × SPos P J N ↦ SVal Ω a.2) T ×
        (Finset (Fin n × SPos P J N) × M) →
      QComp (tmplSpec X Z (Fin n × SPos P J N) (fun a ↦ SVal Ω a.2) M good) B C α}
    (h : ∀ w L₁ m, Q L₁ → RenSim msgLabN msgStoreN StreamInvN (fun L' ↦ L' = L₁ ∪ T)
      (k (w, (L₁, m))) (k' (w, (msgLabN L₁, m)))) :
    RenSim msgLabN msgStoreN StreamInvN Q (revealThen good T k) (revealThen good T k') :=
  renSim_revealThen T T (fun _ ↦ Equiv.refl _) (fun L₁ _ _ _ ↦ msgLabN_union_val L₁ hT)
    (fun _ _ w _ hG _ ↦ msgStoreN_swapIn_val hG hT w) (fun _ σ w _ _ ↦ agreesN_msg_val σ hT w)
    (fun L₁ _ _ _ ↦ by rw [sdiff_msgLabN_val L₁ hT])
    (fun _ _ w _ hG _ ↦ streamInvN_swapIn_val hG hT w) h

/-- **User `i`'s digest reveal at a stream entry**: the event side reveals user `i`'s entry `j`
and its mark (`streamIdx (labU L i) msg = some j`), the hybrid side user `i`'s digest of `msg`,
from the label `L ∪ U` after a reveal `U` without marks of user `i`. -/
theorem renSim_revealEntryN (i : Fin n) {L U : Finset (Fin n × SPos P J N)}
    (hU : ∀ m j, (i, SPos.asg m j) ∉ U) {msg : J} {j : Fin N}
    (hs : streamIdx (labU L i) msg = some j) {B C : QReg} {α : Type}
    {k : RevealVals (fun a : Fin n × SPos P J N ↦ SVal Ω a.2) (atU i (strNeed (labU L i) msg)) ×
        (Finset (Fin n × SPos P J N) × M) →
      QComp (tmplSpec X Z (Fin n × SPos P J N) (fun a ↦ SVal Ω a.2) M good) B C α}
    {k' : RevealVals (fun a : Fin n × SPos P J N ↦ SVal Ω a.2) (atU i (msgNeed msg)) ×
        (Finset (Fin n × SPos P J N) × M) →
      QComp (tmplSpec X Z (Fin n × SPos P J N) (fun a ↦ SVal Ω a.2) M good) B C α}
    (h : ∀ w L₂ m, L₂ = L ∪ U → RenSim msgLabN msgStoreN StreamInvN
      (fun L' ↦ L' = L₂ ∪ atU i (strNeed (labU L i) msg)) (k (w, (L₂, m)))
      (k' (entryEquivN i hs w, (msgLabN L₂, m)))) :
    RenSim msgLabN msgStoreN StreamInvN (fun L' ↦ L' = L ∪ U)
      (revealThen good (atU i (strNeed (labU L i) msg)) k)
      (revealThen good (atU i (msgNeed msg)) k') := by
  have hT := mem_strNeed_some hs
  have hT' := mem_msgNeed (P := P) (N := N) msg
  have hj : SPos.asg msg j ∈ labU (L ∪ U) i ∨
      ((∀ j', SPos.asg msg j' ∉ labU (L ∪ U) i) ∧ j.val = asgCount (labU (L ∪ U) i)) := by
    rw [labU_union]
    exact streamIdx_some_facts hs fun m j h ↦ hU m j (mem_labU.1 h)
  refine renSim_revealAtU i _ _ (fun _ ↦ entryEquiv hT hT') ?_ ?_ ?_ ?_ ?_ h
  · intro _ _ hL hG
    subst hL
    exact msgLab_union_entry hT hT' (hG.user i) hj
  · intro _ _ w hL hG _
    subst hL
    exact msgStore_swapIn_entry hT hT' (hG.user i) hj w
  · intro _ _ w hL hG
    subst hL
    exact agrees_entry hT hT' (hG.user i) hj w
  · intro _ _ hL hG
    subst hL
    exact card_entry hT hT' (hG.user i) hj
  · intro _ _ w hL hG _
    subst hL
    exact streamInv_entry hT (hG.user i) hj w

/-- **User `i`'s digest reveal past the stream** (`streamIdx (labU L i) msg = none`): both sides
reveal user `i`'s digest of `msg`, from the label `L ∪ U` after a reveal `U` without marks of
user `i`. -/
theorem renSim_revealFallN (i : Fin n) {L U : Finset (Fin n × SPos P J N)}
    (hU : ∀ m j, (i, SPos.asg m j) ∉ U) {msg : J} (hs : streamIdx (labU L i) msg = none)
    {B C : QReg} {α : Type}
    {k : RevealVals (fun a : Fin n × SPos P J N ↦ SVal Ω a.2) (atU i (strNeed (labU L i) msg)) ×
        (Finset (Fin n × SPos P J N) × M) →
      QComp (tmplSpec X Z (Fin n × SPos P J N) (fun a ↦ SVal Ω a.2) M good) B C α}
    {k' : RevealVals (fun a : Fin n × SPos P J N ↦ SVal Ω a.2) (atU i (msgNeed msg)) ×
        (Finset (Fin n × SPos P J N) × M) →
      QComp (tmplSpec X Z (Fin n × SPos P J N) (fun a ↦ SVal Ω a.2) M good) B C α}
    (h : ∀ w L₂ m, L₂ = L ∪ U → RenSim msgLabN msgStoreN StreamInvN
      (fun L' ↦ L' = L₂ ∪ atU i (strNeed (labU L i) msg)) (k (w, (L₂, m)))
      (k' (fallEquivN i hs w, (msgLabN L₂, m)))) :
    RenSim msgLabN msgStoreN StreamInvN (fun L' ↦ L' = L ∪ U)
      (revealThen good (atU i (strNeed (labU L i) msg)) k)
      (revealThen good (atU i (msgNeed msg)) k') := by
  have hT := mem_strNeed_none hs
  have hT' := mem_msgNeed (P := P) (N := N) msg
  obtain ⟨hfree, hN⟩ :
      (∀ j, SPos.asg msg j ∉ labU (L ∪ U) i) ∧ N ≤ asgCount (labU (L ∪ U) i) := by
    rw [labU_union]
    exact streamIdx_none_facts hs fun m j h ↦ hU m j (mem_labU.1 h)
  refine renSim_revealAtU i _ _ (fun _ ↦ fallEquiv hT hT') ?_ ?_ ?_ ?_ ?_ h
  · intro _ _ _ _
    exact msgLab_union_fall hT hT'
  · intro _ _ w hL hG _
    subst hL
    exact msgStore_swapIn_fall hT hT' (hG.user i) hfree w
  · intro _ _ w hL _
    subst hL
    exact agrees_fall hT hT' hfree w
  · intro _ _ hL _
    subst hL
    exact card_fall hT hT' hfree
  · intro _ _ w hL hG _
    subst hL
    exact streamInv_fall hT (hG.user i) hfree hN w

omit [Fintype Ω] [DecidableEq Ω] [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] in
/-- Program ports at base coordinates of any users are simulated by themselves. -/
theorem portSim_selfN {Q : Finset (Fin n × SPos P J N) → Prop}
    {p : LazyProg X Z (Fin n × SPos P J N) (fun a ↦ SVal Ω a.2)} (hp : ValOnlyN p.need) :
    PortSim (msgStoreN (Ω := Ω)) StreamInvN Q p p := by
  have key : ∀ {T : Finset (Fin n × SPos P J N)}, ValOnlyN T →
      ∀ L (σ : Store (S := Fin n × SPos P J N) fun a ↦ SVal Ω a.2),
      restrictTo T (fill σ) = restrictTo T (fill (msgStoreN L σ)) := fun hT L σ ↦
    funext fun a ↦ (fill_msgStoreN_of_isVal L σ (hT _ a.2)).symm
  cases p with
  | programH T c => exact .progH T T c c fun L σ _ _ ↦ congrArg c (key hp L σ)
  | programK T c => exact .progK T T c c fun L σ _ _ ↦ congrArg c (key hp L σ)
  | programK' T c => exact .progK' T T c c fun L σ _ _ ↦ congrArg c (key hp L σ)

end sim

/-! ## The users' streams -/

section star

variable {n : ℕ} {P J : Type} {N : ℕ}

/-- **The users' streams held by the values**: user `i`'s entry `j` at `(i, .str j)`. -/
def streamsOf {Ω : Type} (v : (a : Fin n × SPos P J N) → SVal Ω a.2) : Fin n → Fin N → Ω :=
  fun i j ↦ v (i, .str j)

/-- The values as the users' streams and the rest. -/
noncomputable def streamSplitN (Ω : Type) :
    ((a : Fin n × SPos P J N) → SVal Ω a.2) ≃
      (Fin n → Fin N → Ω) × ((a : {a : Fin n × SPos P J N // a.2.NotStr}) → SVal Ω a.1.2) where
  toFun v := (streamsOf v, fun a ↦ v a.1)
  invFun r
    | (i, .val p) => r.2 ⟨(i, .val p), trivial⟩
    | (i, .dig m) => r.2 ⟨(i, .dig m), trivial⟩
    | (i, .str j) => r.1 i j
    | (i, .asg m j) => r.2 ⟨(i, .asg m j), trivial⟩
  left_inv v := funext fun ⟨i, s⟩ ↦ by cases s <;> rfl
  right_inv r := Prod.ext rfl (funext fun ⟨⟨i, s⟩, hs⟩ ↦ by
    cases s with
    | str j => exact absurd hs id
    | _ => rfl)

/-- **The users' streams of uniform values are uniform.** -/
theorem uavg_streamsOf [DecidableEq P] [DecidableEq J] {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    [Nonempty Ω] [Fintype P] [Fintype J] (g : (Fin n → Fin N → Ω) → ℝ≥0∞) :
    uavg (fun v : (a : Fin n × SPos P J N) → SVal Ω a.2 ↦ g (streamsOf v)) = uavg g := by
  classical
  calc uavg (fun v : (a : Fin n × SPos P J N) → SVal Ω a.2 ↦ g (streamsOf v))
      = uavg (fun v ↦ (fun r : (Fin n → Fin N → Ω) ×
          ((a : {a : Fin n × SPos P J N // a.2.NotStr}) → SVal Ω a.1.2) ↦ g r.1)
            (streamSplitN Ω v)) := rfl
    _ = uavg (fun r : (Fin n → Fin N → Ω) ×
          ((a : {a : Fin n × SPos P J N // a.2.NotStr}) → SVal Ω a.1.2) ↦ g r.1) :=
        uavg_comp_equiv (streamSplitN Ω) fun r ↦ g r.1
    _ = uavg g := uavg_comp_fst g

end star

end Quantum.Qrom.Sphincs.Multi

end
