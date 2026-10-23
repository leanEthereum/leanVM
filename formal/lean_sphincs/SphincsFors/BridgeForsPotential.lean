import SphincsFors.BridgeSignerPost
import SphincsFors.BridgeVirtual
import SphincsFors.BridgeImplication

/-! The FORS potential of the lazy run. Every cached landed message-randomizer pair is an item;
the unsigned ones are candidates whose value is the virtual-future forecast of their witness
count; the remaining budget may create future pairs, each paying the excess forecast of a new
pair. This file defines the potential and proves the facts about fresh pairs, ordinary queries
and signing calls that the one-coin potentials of `BridgeForsPotentialOnce` and `BridgeForsGeneric`
build on. -/

open OracleComp OracleSpec ENNReal

namespace SphincsFors.Security.ForsPotential

open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

variable [Params]

/-- A message and a randomizer. -/
abbrev Pair := Message × Randomness

abbrev State := DebtState HashInput HashOutput Coordinate

instance : Inhabited View := ⟨(⟨0, Nat.two_pow_pos _⟩, fun _ => ⟨0, Nat.two_pow_pos _⟩)⟩

omit [Params] in
theorem payload_pair_injective (root : Digest) {m m' : Message} {ρ ρ' : Randomness}
    (h : messageDigestPayload root m ρ = messageDigestPayload root m' ρ') : m = m' ∧ ρ = ρ' := by
  have hparts := List.append_inj h (by simp [bytesLE_length])
  exact ⟨bytesLE_injective hparts.1, bytesLE_injective hparts.2⟩

section Defs

variable (parameter : PublicParameter) (data : PublicData)

/-- Block `call` of a pair. -/
abbrev pblk (p : Pair) (call : Fin 2) : HashInput := blk parameter data p.1 p.2 call

omit [Params] in
theorem pblk_injective {p q : Pair} {call call' : Fin 2}
    (h : pblk parameter data p call = pblk parameter data q call') : p = q ∧ call = call' := by
  obtain ⟨hfields, -, hpayload⟩ := tweakableInput_injective h
  obtain ⟨hm, hρ⟩ := payload_pair_injective data.root hpayload
  refine ⟨Prod.ext hm hρ, ?_⟩
  have := congrArg TweakFields.hi hfields
  simp only [hashDomainFields, tweakFields] at this
  exact Fin.ext (by
    have h1 := call.isLt
    have h2 := call'.isLt
    have := congrArg BitVec.toNat this
    simp at this
    omega)

omit [Params] in
theorem pblk_ne_of_ne {p q : Pair} (h : p ≠ q) (call call' : Fin 2) :
    pblk parameter data p call ≠ pblk parameter data q call' := fun heq =>
  h (pblk_injective parameter data heq).1

omit [Params] in
theorem pblk_ne_call (p : Pair) : pblk parameter data p 0 ≠ pblk parameter data p 1 := fun heq =>
  absurd (pblk_injective parameter data heq).2 (by decide)

/-- The kept view of a pair whose two blocks are cached. -/
noncomputable def pview (s : State) (p : Pair) : View :=
  (s.cache (pblk parameter data p 0)).elim default fun u0 =>
    (s.cache (pblk parameter data p 1)).elim default fun u1 => viewOf u0 u1

/-- Block 0 of the pair is cached and lands. -/
def LandedIn (s : State) (p : Pair) : Prop :=
  ∃ u0, s.cache (pblk parameter data p 0) = some u0 ∧ Landed parameter (blockIndex u0)

/-- The items are exactly the landed pairs; landed pairs have both blocks; no pair has only
its second block. -/
structure PInv (s : State) (P : List Pair) : Prop where
  nodup : P.Nodup
  mem : ∀ p, p ∈ P ↔ LandedIn parameter data s p
  second : ∀ p, LandedIn parameter data s p → s.cache (pblk parameter data p 1) ≠ none
  first : ∀ p, s.cache (pblk parameter data p 0) = none → s.cache (pblk parameter data p 1) = none

/-- The local index of a leaf index. -/
def localIdx (i : Index) : Fin (2 ^ subtreeHeight) := ⟨i.val % 2 ^ subtreeHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩

theorem localDigestView_fst (digest : MessageDigest) :
    (Lifetime.localDigestView digest).1 = localIdx (digestIndex digest) := rfl

theorem localDigestView_snd (digest : MessageDigest) :
    (Lifetime.localDigestView digest).2 = digestLeaves digest := rfl

/-- The disclosed views account for every revealed FORS secret. -/
def DInv (R : List Coordinate) (d : Multiset View) : Prop :=
  ∀ i t l, Coordinate.ftsSecret i t l ∈ R → ∃ v ∈ d, v.1 = localIdx i ∧ v.2 t = l

/-- The pair was never signed in the log. -/
def Unsigned (L : QueryLog SigningSpec) (p : Pair) : Prop :=
  ∀ entry ∈ L, ∀ sig, entry.2 = some sig → ¬(entry.1 = p.1 ∧ sig.randomness = p.2)

variable (wbar b0 : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))

/-- The excess of the price over the baseline. -/
noncomputable def excess (D : Multiset View) : ℝ≥0∞ := price D - b0

/-- Share of kept views at failing indices. -/
noncomputable def failMass : ℝ≥0∞ :=
  freshAvg Finset.univ fun v : View => if v.1 ∈ Fail then 1 else 0

/-- Witness count of a target as a value. -/
noncomputable def witnessFn (v : View) (D : Multiset View) : ℝ≥0∞ := (witness v D : ℝ≥0∞)

/-- Views of a list of pairs. -/
noncomputable def items (s : State) (P : List Pair) : List View := P.map (pview parameter data s)

/-- The forecast of a candidate. -/
noncomputable def candValue (s : State) (P : List Pair) (d : Multiset View) (n k : ℕ) (p : Pair) : ℝ≥0∞ :=
  creations Finset.univ landing (fun I => virtual Finset.univ wbar (witnessFn (pview parameter data s p)) n I d) k
    (items parameter data s (P.erase p))

/-- The excess forecast of a new pair. -/
noncomputable def hValue (s : State) (P : List Pair) (d : Multiset View) (n k : ℕ) : ℝ≥0∞ :=
  creations Finset.univ landing (fun I => virtual Finset.univ wbar (excess b0) n I d) k (items parameter data s P)

/-- The value of a candidate: one at a failing index, its forecast otherwise; zero once signed. -/
noncomputable def cand (s : State) (P : List Pair) (L : QueryLog SigningSpec) (d : Multiset View) (n k : ℕ)
    (p : Pair) : ℝ≥0∞ :=
  if Unsigned L p then (if (pview parameter data s p).1 ∈ Fail then 1 else candValue parameter data wbar s P d n k p)
  else 0

/-- The potential without the hit and transcript tests. -/
noncomputable def core (s : State) (P : List Pair) (L : QueryLog SigningSpec) (d : Multiset View) (n k : ℕ) :
    ℝ≥0∞ :=
  (P.map (cand parameter data wbar Fail s P L d n k)).sum +
    k * (hValue parameter data wbar b0 s P d n k + failMass Fail) + n * failMass Fail

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)

/-- **The potential.** -/
noncomputable def pot (s : State) (P : List Pair) (L : QueryLog SigningSpec) (d : Multiset View) (k : ℕ) : ℝ≥0∞ :=
  if Realized tg initial s ∨ signatureLimit < L.length then 0
  else core parameter data wbar b0 Fail s P L d (signatureLimit - L.length) k

end Defs

/-! ### The law of a fresh pair -/

section Mean

theorem landing_le_one : landing ≤ 1 := by
  unfold landing
  exact ENNReal.inv_le_one.2 (by exact_mod_cast Nat.one_le_two_pow)

theorem unlanded_mass (parameter : PublicParameter) :
    ∑' u0, Pr{let x ← ($ᵗ HashOutput : ProbComp HashOutput)}[x = u0] *
      (if Landed parameter (blockIndex u0) then (0 : ℝ≥0∞) else 1) = 1 - landing := by
  have htot : (∑' u0, Pr{let x ← ($ᵗ HashOutput : ProbComp HashOutput)}[x = u0] *
      (if Landed parameter (blockIndex u0) then (1 : ℝ≥0∞) else 0)) +
    ∑' u0, Pr{let x ← ($ᵗ HashOutput : ProbComp HashOutput)}[x = u0] *
      (if Landed parameter (blockIndex u0) then (0 : ℝ≥0∞) else 1) = 1 := by
    rw [← ENNReal.tsum_add]
    calc _ = ∑' u0, Pr{let x ← ($ᵗ HashOutput : ProbComp HashOutput)}[x = u0] := by
          refine tsum_congr fun u0 => ?_
          split_ifs <;> simp [-SampleableType.prEvent_uniformSample]
      _ = 1 := OracleComp.tsum_prEvent_eq_one _
  rw [landed_mass parameter] at htot
  exact ENNReal.eq_sub_of_add_eq' ENNReal.one_ne_top (by rw [add_comm]; exact htot)

/-- **Mean over a fresh pair.** -/
theorem pair_mean (parameter : PublicParameter) (F : View → ℝ≥0∞) (C : ℝ≥0∞) :
    ∑' u0, Pr{let x ← ($ᵗ HashOutput : ProbComp HashOutput)}[x = u0] *
      ∑' u1, Pr{let x ← ($ᵗ HashOutput : ProbComp HashOutput)}[x = u1] *
        (if Landed parameter (blockIndex u0) then F (viewOf u0 u1) else C) =
      landing * freshAvg Finset.univ F + (1 - landing) * C := by
  have hsplit : ∀ u0, ∑' u1, Pr{let x ← ($ᵗ HashOutput : ProbComp HashOutput)}[x = u1] *
      (if Landed parameter (blockIndex u0) then F (viewOf u0 u1) else C) =
      (∑' u1, Pr{let x ← ($ᵗ HashOutput : ProbComp HashOutput)}[x = u1] *
        (if Landed parameter (blockIndex u0) then F (Lifetime.localDigestView (truncateMessageDigest u0 u1)) else 0)) +
      C * (if Landed parameter (blockIndex u0) then 0 else 1) := by
    intro u0
    split_ifs
    · simp [-SampleableType.prEvent_uniformSample, viewOf]
    · simp only [mul_zero, tsum_zero, zero_add, mul_one]
      rw [ENNReal.tsum_mul_right, OracleComp.tsum_prEvent_eq_one _, one_mul]
  simp only [hsplit, mul_add, ENNReal.tsum_add]
  rw [fresh_view_mean parameter F]
  congr 1
  simp only [mul_left_comm _ C, ENNReal.tsum_mul_left]
  rw [unlanded_mass parameter, mul_comm]

omit [Params] in
/-- Expectations distribute over a list sum. -/
theorem tsum_list_sum {β γ : Type} (w : β → ℝ≥0∞) (l : List γ) (f : β → γ → ℝ≥0∞) :
    ∑' x, w x * (l.map (f x)).sum = (l.map fun c => ∑' x, w x * f x c).sum := by
  induction l with
  | nil => simp
  | cons c l ih =>
      simp only [List.map_cons, List.sum_cons, mul_add, ENNReal.tsum_add, ih]

end Mean

/-! ### Expectation over the two blocks of a fresh pair -/

section PairE

/-- Expectation over two fresh blocks. -/
noncomputable def pairE (F : HashOutput → HashOutput → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' u0, Pr{let x ← ($ᵗ HashOutput : ProbComp HashOutput)}[x = u0] *
    ∑' u1, Pr{let x ← ($ᵗ HashOutput : ProbComp HashOutput)}[x = u1] * F u0 u1

omit [Params] in
theorem pairE_add (F G : HashOutput → HashOutput → ℝ≥0∞) :
    pairE (fun a b => F a b + G a b) = pairE F + pairE G := by
  simp only [pairE, mul_add, ENNReal.tsum_add]

omit [Params] in
theorem pairE_mono {F G : HashOutput → HashOutput → ℝ≥0∞} (h : ∀ a b, F a b ≤ G a b) : pairE F ≤ pairE G :=
  ENNReal.tsum_le_tsum fun a => mul_le_mul_right (ENNReal.tsum_le_tsum fun b => mul_le_mul_right (h a b) _) _

omit [Params] in
theorem pairE_const (c : ℝ≥0∞) : pairE (fun _ _ => c) = c := by
  simp only [pairE, ENNReal.tsum_mul_right, OracleComp.tsum_prEvent_eq_one _, one_mul]

omit [Params] in
theorem pairE_const_mul (c : ℝ≥0∞) (F : HashOutput → HashOutput → ℝ≥0∞) :
    pairE (fun a b => c * F a b) = c * pairE F := by
  simp only [pairE, mul_left_comm _ c, ENNReal.tsum_mul_left]

omit [Params] in
theorem pairE_list_sum {γ : Type} (l : List γ) (F : HashOutput → HashOutput → γ → ℝ≥0∞) :
    pairE (fun a b => (l.map (F a b)).sum) = (l.map fun c => pairE fun a b => F a b c).sum := by
  induction l with
  | nil => simpa using pairE_const 0
  | cons c l ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [pairE_add, ih]

theorem pairE_landed (parameter : PublicParameter) (F : View → ℝ≥0∞) (C : ℝ≥0∞) :
    pairE (fun u0 u1 => if Landed parameter (blockIndex u0) then F (viewOf u0 u1) else C) =
      landing * freshAvg Finset.univ F + (1 - landing) * C :=
  pair_mean parameter F C

end PairE

/-! ### A new pair -/

section NewPair

variable (parameter : PublicParameter) (data : PublicData) (wbar b0 : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))

/-- Both blocks of a new pair stored. -/
noncomputable def withPair (s : State) (p : Pair) (u0 u1 : HashOutput) : State :=
  (s.store (pblk parameter data p 0) u0).store (pblk parameter data p 1) u1

/-- The items after a new pair. -/
noncomputable def addPair (P : List Pair) (p : Pair) (u0 : HashOutput) : List Pair :=
  if Landed parameter (blockIndex u0) then p :: P else P

variable {parameter data}

omit [Params] in
theorem withPair_other (s : State) (p : Pair) (u0 u1 : HashOutput) (x : HashInput)
    (h0 : x ≠ pblk parameter data p 0) (h1 : x ≠ pblk parameter data p 1) :
    (withPair parameter data s p u0 u1).cache x = s.cache x := by
  unfold withPair
  rw [store_cache_ne _ _ _ h1, store_cache_ne _ _ _ h0]

omit [Params] in
theorem withPair_zero (s : State) (p : Pair) (u0 u1 : HashOutput) :
    (withPair parameter data s p u0 u1).cache (pblk parameter data p 0) = some u0 := by
  unfold withPair
  rw [store_cache_ne _ _ _ (pblk_ne_call parameter data p)]
  simp [DebtState.store]

omit [Params] in
theorem withPair_one (s : State) (p : Pair) (u0 u1 : HashOutput) :
    (withPair parameter data s p u0 u1).cache (pblk parameter data p 1) = some u1 := by
  unfold withPair
  simp [DebtState.store]

omit [Params] in
theorem withPair_other_pair (s : State) (p q : Pair) (hq : q ≠ p) (u0 u1 : HashOutput) (call : Fin 2) :
    (withPair parameter data s p u0 u1).cache (pblk parameter data q call) = s.cache (pblk parameter data q call) :=
  withPair_other s p u0 u1 _ (pblk_ne_of_ne parameter data hq _ _) (pblk_ne_of_ne parameter data hq _ _)

theorem pview_withPair_self (s : State) (p : Pair) (u0 u1 : HashOutput) :
    pview parameter data (withPair parameter data s p u0 u1) p = viewOf u0 u1 := by
  simp only [pview, withPair_zero, withPair_one, Option.elim]

theorem pview_withPair_other (s : State) (p q : Pair) (hq : q ≠ p) (u0 u1 : HashOutput) :
    pview parameter data (withPair parameter data s p u0 u1) q = pview parameter data s q := by
  simp only [pview, withPair_other_pair s p q hq]

theorem items_withPair (s : State) (p : Pair) (u0 u1 : HashOutput) (l : List Pair) (hl : p ∉ l) :
    items parameter data (withPair parameter data s p u0 u1) l = items parameter data s l := by
  unfold items
  refine List.map_congr_left fun q hq => ?_
  exact pview_withPair_other s p q (fun h => hl (h ▸ hq)) u0 u1

theorem not_mem_of_fresh {s : State} {P : List Pair} (hP : PInv parameter data s P) {p : Pair}
    (hp0 : s.cache (pblk parameter data p 0) = none) : p ∉ P := by
  intro hp
  obtain ⟨u, hu, _⟩ := (hP.mem p).1 hp
  rw [hp0] at hu
  cases hu

theorem pinv_withPair {s : State} {P : List Pair} (hP : PInv parameter data s P) {p : Pair}
    (hp0 : s.cache (pblk parameter data p 0) = none) (u0 u1 : HashOutput) :
    PInv parameter data (withPair parameter data s p u0 u1) (addPair parameter P p u0) := by
  have hpP := not_mem_of_fresh hP hp0
  have hland : ∀ q, q ≠ p → (LandedIn parameter data (withPair parameter data s p u0 u1) q ↔
      LandedIn parameter data s q) := by
    intro q hq
    simp only [LandedIn, withPair_other_pair s p q hq]
  refine ⟨?_, fun q => ?_, fun q hq => ?_, fun q hq => ?_⟩
  · unfold addPair
    split_ifs
    · exact List.nodup_cons.2 ⟨hpP, hP.nodup⟩
    · exact hP.nodup
  · by_cases hqp : q = p
    · subst hqp
      unfold addPair
      constructor
      · intro hmem
        split_ifs at hmem with hl
        · exact ⟨u0, withPair_zero s q u0 u1, hl⟩
        · exact absurd hmem hpP
      · rintro ⟨u, hu, hl⟩
        rw [withPair_zero] at hu
        cases hu
        rw [ite_eq_left hl]
        exact List.mem_cons_self ..
    · rw [hland q hqp, ← hP.mem q]
      unfold addPair
      split_ifs
      · simp [hqp]
      · rfl
  · by_cases hqp : q = p
    · subst hqp
      rw [withPair_one]
      simp
    · rw [withPair_other_pair s p q hqp]
      exact hP.second q ((hland q hqp).1 hq)
  · by_cases hqp : q = p
    · subst hqp
      rw [withPair_zero] at hq
      cases hq
    · rw [withPair_other_pair s p q hqp] at hq ⊢
      exact hP.first q hq

end NewPair

/-! ### Properties of the forecast -/

section NewPairCore

variable (parameter : PublicParameter) (data : PublicData) (wbar b0 : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))

theorem excess_props (hb0 : b0 ≠ ⊤) :
    Monotone' (excess b0) ∧ Supermodular (excess b0) ∧ ∀ D, excess b0 D ≠ ⊤ :=
  ⟨excess_mono price_mono b0, excess_super price_mono price_super price_ne_top b0 hb0,
    fun D => ne_top_of_le_ne_top (price_ne_top D) tsub_le_self⟩

theorem witness_props (v : View) :
    Monotone' (witnessFn v) ∧ Supermodular (witnessFn v) ∧ ∀ D, witnessFn v D ≠ ⊤ :=
  ⟨witness_mono v, witness_super v, fun _ => ENNReal.natCast_ne_top _⟩

theorem virtual_cons_le (hw : wbar ≤ 1) {f : Multiset View → ℝ≥0∞}
    (hf : Monotone' f ∧ Supermodular f ∧ ∀ D, f D ≠ ⊤) (n : ℕ) (d : Multiset View) :
    ∀ v I, virtual Finset.univ wbar f n I d ≤ virtual Finset.univ wbar f n (v :: I) d :=
  fun v I => virtual_le_cons Finset.univ_nonempty hw hf.1 hf.2.1 hf.2.2 n I v d

theorem virtual_perm' {f : Multiset View → ℝ≥0∞} (n : ℕ) (d : Multiset View) :
    ∀ I I' : List View, I.Perm I' → virtual Finset.univ wbar f n I d = virtual Finset.univ wbar f n I' d :=
  fun _ _ h => virtual_perm n h d

end NewPairCore

/-! ### Order and congruence of the potential -/

section Order

variable (parameter : PublicParameter) (data : PublicData) (wbar b0 : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))

variable {parameter data}

theorem items_congr {s s' : State} {l : List Pair} (h : ∀ q ∈ l, pview parameter data s' q = pview parameter data s q) :
    items parameter data s' l = items parameter data s l :=
  List.map_congr_left h

theorem candValue_mono (hw : wbar ≤ 1) (s : State) (P : List Pair) (d : Multiset View) (n : ℕ) {k k' : ℕ}
    (hk : k ≤ k') (p : Pair) :
    candValue parameter data wbar s P d n k p ≤ candValue parameter data wbar s P d n k' p :=
  creations_mono_count Finset.univ_nonempty landing_le_one
    (virtual_cons_le wbar hw (witness_props _) n d) (virtual_perm' wbar n d) hk _

theorem hValue_mono (hw : wbar ≤ 1) (hb0 : b0 ≠ ⊤) (s : State) (P : List Pair) (d : Multiset View) (n : ℕ)
    {k k' : ℕ} (hk : k ≤ k') :
    hValue parameter data wbar b0 s P d n k ≤ hValue parameter data wbar b0 s P d n k' :=
  creations_mono_count Finset.univ_nonempty landing_le_one
    (virtual_cons_le wbar hw (excess_props b0 hb0) n d) (virtual_perm' wbar n d) hk _

theorem core_mono (hw : wbar ≤ 1) (hb0 : b0 ≠ ⊤) (s : State) (P : List Pair) (L : QueryLog SigningSpec)
    (d : Multiset View) (n : ℕ) {k k' : ℕ} (hk : k ≤ k') :
    core parameter data wbar b0 Fail s P L d n k ≤ core parameter data wbar b0 Fail s P L d n k' := by
  unfold core
  refine add_le_add (add_le_add (List.sum_le_sum fun q _ => ?_) ?_) le_rfl
  · unfold cand
    split_ifs
    · exact le_rfl
    · exact candValue_mono wbar hw s P d n hk q
    · exact le_rfl
  · exact mul_le_mul' (by exact_mod_cast hk) (add_le_add (hValue_mono wbar b0 hw hb0 s P d n hk) le_rfl)

end Order

/-! ### Counting cached randomizers -/

section Count

variable {parameter : PublicParameter} {data : PublicData}

omit [Params] in
theorem blk_zero_injective (m : Message) : Function.Injective fun ρ : Randomness => blk parameter data m ρ 0 := by
  intro ρ ρ' h
  by_contra hne
  exact blk_ne_of_ne parameter data m ρ ρ' 0 0 (Or.inl hne) h

variable (parameter data) in
/-- Block-0 inputs of a message. -/
noncomputable def zeroInputs (m : Message) : Finset HashInput :=
  Finset.univ.image fun ρ => blk parameter data m ρ 0

omit [Params] in
theorem cachedCount_eq (m : Message) (s : State) :
    cachedCount parameter data m s = ((zeroInputs parameter data m).filter fun x => s.cache x ≠ none).card := by
  unfold cachedCount zeroInputs
  rw [Finset.filter_image, Finset.card_image_of_injective _ (blk_zero_injective m)]

omit [Params] in
theorem card_filter_store_of_not_mem (T : Finset HashInput) (s : State) (x : HashInput) (hx : x ∉ T)
    (u : HashOutput) :
    (T.filter fun y => (s.store x u).cache y ≠ none).card = (T.filter fun y => s.cache y ≠ none).card := by
  congr 1
  refine Finset.filter_congr fun y hy => ?_
  rw [store_cache_ne s x y (fun h => hx (h ▸ hy)) u]

omit [Params] in
theorem count_withPair (m : Message) (s : State) (p : Pair) (u0 u1 : HashOutput) :
    cachedCount parameter data m (withPair parameter data s p u0 u1) ≤ cachedCount parameter data m s + 1 := by
  rw [cachedCount_eq, cachedCount_eq]
  unfold withPair
  rw [card_filter_store_of_not_mem _ _ _ ?_ u1]
  · exact card_filter_store_le _ _ _ _
  · intro hmem
    obtain ⟨ρ, _, hρ⟩ := Finset.mem_image.1 hmem
    exact absurd (pblk_injective parameter data (show pblk parameter data (m, ρ) 0 = pblk parameter data p 1 from hρ)).2
      (by decide)

end Count

/-! ### Paid programs -/

section Good

variable (parameter : PublicParameter) (data : PublicData) (wbar b0 : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))
  (Qtot : ℕ) {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)

/-- The final value: a FORS cover with no decided hit. -/
noncomputable def finalValue (R : List Coordinate) (out : Run HashInput Coordinate HiddenBridge.Outcome × State) :
    ℝ≥0∞ :=
  out.1.1.elim 0 fun outcome =>
    if HiddenBridge.ForsCover parameter data.root outcome (R ++ out.1.2.1) out.2.cache ∧ ¬Realized tg initial out.2
    then 1 else 0

/-- Cached block-0 entries of every message, plus the remaining budget, stay bounded. -/
def CountInv (s : State) (budget : ℕ) : Prop :=
  ∀ m : Message, cachedCount parameter data m s + budget ≤ Qtot

/-- A program whose final value is paid by the potential and the baseline payments. -/
def Good (L : QueryLog SigningSpec) (prog : OracleComp CostSpec HiddenBridge.Outcome) : Prop :=
  ∀ budget (s : State) (P : List Pair) (d : Multiset View) (R : List Coordinate),
    Prepared initial s → PInv parameter data s P → DInv R d → CountInv parameter data Qtot s budget →
      ∑' out, Pr{let x ← interp tg initial model prog budget s}[x = out] * finalValue parameter data tg initial R out ≤
        pot parameter data wbar b0 Fail tg initial s P L d budget + b0 * expectedFlagged tg initial model prog budget s

theorem pot_mono (hw : wbar ≤ 1) (hb0 : b0 ≠ ⊤) (s : State) (P : List Pair) (L : QueryLog SigningSpec)
    (d : Multiset View) {k k' : ℕ} (hk : k ≤ k') :
    pot parameter data wbar b0 Fail tg initial s P L d k ≤ pot parameter data wbar b0 Fail tg initial s P L d k' := by
  unfold pot
  split_ifs
  · exact le_rfl
  · exact core_mono wbar b0 Fail hw hb0 s P L d _ hk

end Good

/-! ### One ordinary query -/

section Ordinary

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)

omit [Params] in
theorem readOutside_cache_ne (x : HashInput) (s : State) :
    ∀ r ∈ support (readOutside x s), ∀ y, y ≠ x → r.2.cache y = s.cache y := by
  intro r hr y hy
  rcases readOutside_support x s r hr with h | ⟨_, h⟩
  · rw [h]
  · rw [h]; exact store_cache_ne s x y hy r.1

omit [Params] in
/-- An ordinary query changes the cache at most at its input. -/
theorem ordinaryStep_cache_ne (x : HashInput) (s : State) :
    ∀ r ∈ support (ordinaryStep model x s.known s), ∀ y, y ≠ x → r.2.cache y = s.cache y := by
  intro r hr y hy
  unfold ordinaryStep at hr
  split at hr
  · exact readOutside_cache_ne x s r hr y hy
  · split at hr
    · exact readOutside_cache_ne x _ r hr y hy
    · split at hr
      · rw [support_map] at hr
        obtain ⟨r', hr', rfl⟩ := hr
        rw [sampleCoordinate_expose _ s r' hr']
        rfl
      · exact readOutside_cache_ne x s r hr y hy

omit [Params] in
theorem ordinaryStep_extends (x : HashInput) (s : State) :
    ∀ r ∈ support (ordinaryStep model x s.known s), Extends s r.2 := by
  intro r hr
  exact extends_costStep model (.inl (.inr (.inl x))) s r (by rw [costStep_ordinary]; exact hr)

theorem forsCover_mono (parameter : PublicParameter) (root : Digest) (outcome : HiddenBridge.Outcome)
    (reveals : List Coordinate) {c c' : QueryCache HashSpec} (h : ∀ x v, c x = some v → c' x = some v)
    (hc : HiddenBridge.ForsCover parameter root outcome reveals c) :
    HiddenBridge.ForsCover parameter root outcome reveals c' := by
  obtain ⟨hvalid, digest, hdig, hrest⟩ := hc
  refine ⟨hvalid, digest, ?_, hrest⟩
  unfold HiddenBridge.cachedDigest at hdig ⊢
  cases h0 : c (tweakableHashInput parameter (.message 0)
      (messageDigestPayload root outcome.1.message outcome.1.signature.randomness)) with
  | none => rw [h0] at hdig; cases hdig
  | some a =>
      cases h1 : c (tweakableHashInput parameter (.message 1)
          (messageDigestPayload root outcome.1.message outcome.1.signature.randomness)) with
      | none => rw [h0, h1] at hdig; cases hdig
      | some b =>
          rw [h0, h1] at hdig
          rw [h _ _ h0, h _ _ h1]
          exact hdig

variable (parameter : PublicParameter) (data : PublicData)

theorem finalValue_presample (y : HashInput) (hk : tg.kind y = .none) (R : List Coordinate)
    (out : Run HashInput Coordinate HiddenBridge.Outcome × State) (s' : State)
    (hs' : s' ∈ support (presample y out.2)) :
    finalValue parameter data tg initial R out ≤ finalValue parameter data tg initial R (out.1, s') := by
  have hreal := realized_presample tg initial y hk out.2 s' hs'
  have hgrow : ∀ x v, out.2.cache x = some v → s'.cache x = some v := by
    cases hc : out.2.cache y with
    | some v =>
        rw [presample_cached y out.2 v hc, support_pure, Set.mem_singleton_iff] at hs'
        rw [hs']
        exact fun _ _ h => h
    | none =>
        rw [presample_fresh y out.2 hc, support_map] at hs'
        obtain ⟨u, _, rfl⟩ := hs'
        exact (extends_store out.2 y u hc).1
  unfold finalValue
  cases out.1.1 with
  | none => exact le_rfl
  | some outcome =>
      simp only [Option.elim]
      split_ifs with h1 h2
      · exact le_rfl
      · exact absurd ⟨forsCover_mono parameter data.root outcome _ hgrow h1.1, fun h => h1.2 (hreal.1 h)⟩ h2
      · exact bot_le
      · exact le_rfl

theorem finalValue_abort (R : List Coordinate) (s : State) :
    finalValue parameter data tg initial R ((none, [], [], []), s) = 0 := rfl

omit [Params] in
theorem interp_mass {α : Type} (computation : OracleComp CostSpec α) (budget : ℕ) (s : State) :
    ∑' out, Pr{let x ← interp tg initial model computation budget s}[x = out] = 1 :=
  OracleComp.tsum_prEvent_eq_one _

theorem finalValue_ordinary (R : List Coordinate) (x : HashInput)
    (next : HashOutput → OracleComp CostSpec HiddenBridge.Outcome) (budget : ℕ) (hb : 1 ≤ budget) (s : State) :
    ∑' out, Pr{let y ← interp tg initial model (liftM (CostSpec.query (.inl (.inr (.inl x)))) >>= next) budget s}[y = out] *
        finalValue parameter data tg initial R out =
      ∑' r, Pr{let y ← ordinaryStep model x s.known s}[y = r] *
        ∑' out, Pr{let x ← interp tg initial model (next r.1) (budget - 1) r.2}[x = out] *
          finalValue parameter data tg initial R out := by
  rw [interp_ordinary, ite_eq_left hb, OracleComp.tsum_prEvent_bind_mul]
  simp only [OracleComp.tsum_prEvent_map_mul]
  rfl

omit [Params] in
theorem flagged_ordinary (x : HashInput) (next : HashOutput → OracleComp CostSpec HiddenBridge.Outcome)
    (budget : ℕ) (hb : 1 ≤ budget) (s : State) :
    expectedFlagged tg initial model (liftM (CostSpec.query (.inl (.inr (.inl x)))) >>= next) budget s =
      (pays tg initial s (.inl (.inr (.inl x))) : ℝ≥0∞) +
        ∑' r, Pr{let y ← ordinaryStep model x s.known s}[y = r] *
          expectedFlagged tg initial model (next r.1) (budget - 1) r.2 := by
  unfold expectedFlagged
  rw [interp_ordinary, ite_eq_left hb, OracleComp.tsum_prEvent_bind_mul]
  simp only [OracleComp.tsum_prEvent_map_mul, flaggedCount_append, flaggedCount_touch, Nat.cast_add, mul_add,
    ENNReal.tsum_add, ENNReal.tsum_mul_right, interp_mass]
  rw [one_mul, OracleComp.tsum_prEvent_eq_one _, one_mul]

/-- Without a new pair, an ordinary query keeps the items and their views. -/
theorem same_items {x : HashInput} {s s' : State} (hext : Extends s s') (hother : ∀ y, y ≠ x → s'.cache y = s.cache y)
    (hnot : ¬∃ p call, x = pblk parameter data p call ∧ s.cache (pblk parameter data p 0) = none)
    {P : List Pair} (hP : PInv parameter data s P) :
    PInv parameter data s' P ∧ ∀ q ∈ P, pview parameter data s' q = pview parameter data s q := by
  have hkeep : ∀ y, s.cache y ≠ none → s'.cache y = s.cache y := by
    intro y hy
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 hy
    rw [hv]; exact hext.1 y v hv
  have hzero : ∀ q, s'.cache (pblk parameter data q 0) = s.cache (pblk parameter data q 0) := by
    intro q
    by_cases hx : x = pblk parameter data q 0
    · by_cases hn : s.cache (pblk parameter data q 0) = none
      · exact absurd ⟨q, 0, hx, hn⟩ hnot
      · exact hkeep _ hn
    · exact hother _ (Ne.symm hx)
  have hland : ∀ q, LandedIn parameter data s' q ↔ LandedIn parameter data s q := by
    intro q; simp only [LandedIn, hzero q]
  refine ⟨⟨hP.nodup, fun q => (hP.mem q).trans (hland q).symm, fun q hq => ?_, fun q hq => ?_⟩, fun q hq => ?_⟩
  · have := hP.second q ((hland q).1 hq)
    rw [hkeep _ this]; exact this
  · rw [hzero q] at hq
    have h1 := hP.first q hq
    by_cases hx : x = pblk parameter data q 1
    · exact absurd ⟨q, 1, hx, hq⟩ hnot
    · rw [hother _ (Ne.symm hx)]; exact h1
  · have hl := (hP.mem q).1 hq
    have h1 := hP.second q hl
    unfold pview
    rw [hzero q, hkeep _ h1]

end Ordinary

omit [Params] in
theorem tsum_swap2 {α : Type} (w : α → ℝ≥0∞) (C : α → α → ℝ≥0∞) :
    ∑' u, w u * ∑' u', w u' * C u' u = ∑' a, w a * ∑' b, w b * C a b := by
  calc ∑' u, w u * ∑' u', w u' * C u' u = ∑' u, ∑' u', w u' * (w u * C u' u) :=
        tsum_congr fun u => by rw [← ENNReal.tsum_mul_left]; exact tsum_congr fun u' => mul_left_comm _ _ _
    _ = ∑' u', ∑' u, w u' * (w u * C u' u) := ENNReal.tsum_comm
    _ = _ := tsum_congr fun u' => ENNReal.tsum_mul_left

/-! ### Leaves and verification -/

section Leaf

variable (parameter : PublicParameter) (data : PublicData) (wbar b0 : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))
  (Qtot : ℕ) {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)

/-- A covered view has a positive witness count. -/
theorem witness_pos_of_covered {R : List Coordinate} {d : Multiset View} (hD : DInv R d) (digest : MessageDigest)
    (hcov : Covered (HiddenBridge.revealedSet R) (fullDigestView digest)) :
    1 ≤ witness (Lifetime.localDigestView digest) d := by
  unfold witness
  refine Finset.one_le_prod fun t _ => ?_
  have hmem := hcov t
  simp only [fullDigestView, HiddenBridge.revealedSet, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  obtain ⟨w, hw, h1, h2⟩ := hD _ _ _ hmem
  unfold matchCount
  refine Multiset.card_pos.2 fun hzero => ?_
  have : w ∈ d.filter fun view => view.1 = (Lifetime.localDigestView digest).1 ∧
      view.2 t = (Lifetime.localDigestView digest).2 t :=
    Multiset.mem_filter.2 ⟨hw, by rw [localDigestView_fst, localDigestView_snd]; exact ⟨h1, h2⟩⟩
  rw [hzero] at this
  exact absurd this (Multiset.notMem_zero _)

end Leaf

/-! ### What a signing call adds -/

/-- The pairs that are not excluded. -/
noncomputable def others (excl : Pair → Prop) (P : List Pair) : List Pair := P.filter fun q => ¬excl q

omit [Params] in
theorem mem_others {excl : Pair → Prop} {P : List Pair} {q : Pair} : q ∈ others excl P ↔ q ∈ P ∧ ¬excl q := by
  unfold others; simp

omit [Params] in
theorem others_nodup {excl : Pair → Prop} {P : List Pair} (h : P.Nodup) : (others excl P).Nodup := h.filter _

section SignDefs

variable (parameter : PublicParameter) (data : PublicData) (m : Message) (s : State)

/-- Randomizers of the message whose block 0 is new and lands. -/
noncomputable def newRand (s' : State) : Finset Randomness :=
  Finset.univ.filter fun ρ => s.cache (blk parameter data m ρ 0) = none ∧ LandedIn parameter data s' (m, ρ)

/-- Pairs created by a signing call. -/
noncomputable def newPairs (s' : State) : List Pair := (newRand parameter data m s s').toList.map fun ρ => (m, ρ)

/-- Disclosure of an existing pair signed by the call. -/
noncomputable def poolDisc (out : Run HashInput Coordinate (Option Signature) × State) : Multiset View :=
  out.1.1.elim 0 fun r => r.elim 0 fun sig =>
    if s.cache (blk parameter data m sig.randomness 0) = none then 0
    else {pview parameter data out.2 (m, sig.randomness)}

/-- Disclosures after a signing call. -/
noncomputable def discAfter (d : Multiset View) (out : Run HashInput Coordinate (Option Signature) × State) :
    Multiset View :=
  d + ((newPairs parameter data m s out.2).map (pview parameter data out.2) : Multiset View) +
    poolDisc parameter data m s out

theorem newPairs_nodup (s' : State) : (newPairs parameter data m s s').Nodup :=
  (Finset.nodup_toList _).map fun _ _ h => (Prod.ext_iff.1 h).2

theorem mem_newPairs {s' : State} {q : Pair} :
    q ∈ newPairs parameter data m s s' ↔ q.1 = m ∧ s.cache (pblk parameter data q 0) = none ∧
      LandedIn parameter data s' q := by
  unfold newPairs newRand
  simp only [List.mem_map, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨ρ, ⟨h0, hl⟩, rfl⟩
    exact ⟨rfl, h0, hl⟩
  · rintro ⟨hm, h0, hl⟩
    exact ⟨q.2, ⟨by rw [← hm]; exact h0, by rw [← hm]; exact hl⟩, by rw [← hm]⟩

end SignDefs

/-! ### The three shapes of a completed signing call -/

section SignShape

variable (parameter : PublicParameter) (data : PublicData) (Fail : Finset (Fin (2 ^ subtreeHeight)))
  (m : Message) {s : State}

theorem newRand_eq_empty {s' : State} (h : ∀ ρ, RelatedAt parameter data m s s' ρ) :
    newRand parameter data m s s' = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun ρ hρ => ?_
  simp only [newRand, Finset.mem_filter, Finset.mem_univ, true_and] at hρ
  obtain ⟨h0, u, hu, hl⟩ := hρ
  rcases (h ρ).2 with he | ⟨_, u', hu', hnl⟩
  · change s'.cache (blk parameter data m ρ 0) = some u at hu
    rw [he, h0] at hu; cases hu
  · change s'.cache (blk parameter data m ρ 0) = some u at hu
    rw [hu'] at hu; cases hu; exact hnl hl

theorem newRand_eq_single {s' : State} {ρ : Randomness} (h : ∀ ρ', ρ' ≠ ρ → RelatedAt parameter data m s s' ρ')
    (h0 : s.cache (blk parameter data m ρ 0) = none) (hl : LandedIn parameter data s' (m, ρ)) :
    newRand parameter data m s s' = {ρ} := by
  ext ρ'
  simp only [newRand, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro ⟨h0', u, hu, hl'⟩
    by_contra hne
    rcases (h ρ' hne).2 with he | ⟨_, u', hu', hnl⟩
    · change s'.cache (blk parameter data m ρ' 0) = some u at hu
      rw [he, h0'] at hu; cases hu
    · change s'.cache (blk parameter data m ρ' 0) = some u at hu
      rw [hu'] at hu; cases hu; exact hnl hl'
  · rintro rfl
    exact ⟨h0, hl⟩

theorem newRand_eq_empty_of_pool {s' : State} {ρ : Randomness} (h : ∀ ρ', ρ' ≠ ρ → RelatedAt parameter data m s s' ρ')
    (h0 : s.cache (blk parameter data m ρ 0) ≠ none) : newRand parameter data m s s' = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun ρ' hρ' => ?_
  simp only [newRand, Finset.mem_filter, Finset.mem_univ, true_and] at hρ'
  obtain ⟨h0', u, hu, hl'⟩ := hρ'
  by_cases hne : ρ' = ρ
  · subst hne; exact h0 h0'
  · rcases (h ρ' hne).2 with he | ⟨_, u', hu', hnl⟩
    · change s'.cache (blk parameter data m ρ' 0) = some u at hu
      rw [he, h0'] at hu; cases hu
    · change s'.cache (blk parameter data m ρ' 0) = some u at hu
      rw [hu'] at hu; cases hu; exact hnl hl'

/-- **Shapes.** A completed signing call adds nothing, one fresh landed pair, or signs a cached
landed pair. -/
theorem sign_shape {reveals : List Coordinate} {r : Option Signature} {s' : State}
    (post : SignPost parameter data m Fail s s' reveals r)
    (out : Run HashInput Coordinate (Option Signature) × State) (hout2 : out.2 = s') (hres : out.1.1 = some r) :
    (newRand parameter data m s s' = ∅ ∧ poolDisc parameter data m s out = 0) ∨
    (∃ ρ u0 u1, newRand parameter data m s s' = {ρ} ∧ poolDisc parameter data m s out = 0 ∧
      s'.cache (blk parameter data m ρ 0) = some u0 ∧ Landed parameter (blockIndex u0) ∧
      s'.cache (blk parameter data m ρ 1) = some u1 ∧ s.cache (blk parameter data m ρ 0) = none ∧
      (∀ ρ', ρ' ≠ ρ → RelatedAt parameter data m s s' ρ') ∧
      (r = none → (viewOf u0 u1).1 ∈ Fail) ∧ (∀ sig, r = some sig → sig.randomness = ρ)) ∨
    (∃ ρ u0 u1 sig, newRand parameter data m s s' = ∅ ∧ poolDisc parameter data m s out = {viewOf u0 u1} ∧
      r = some sig ∧ sig.randomness = ρ ∧ s.cache (blk parameter data m ρ 0) = some u0 ∧
      s'.cache (blk parameter data m ρ 0) = some u0 ∧ s'.cache (blk parameter data m ρ 1) = some u1) := by
  subst hout2
  rcases post with ⟨hrn, _, hrel⟩ | ⟨ρ, u0, u1, ⟨hs0, hl, hs1, hs0r, _, hothers⟩, _, hsig, hfl⟩
  · left
    refine ⟨newRand_eq_empty parameter data m hrel, ?_⟩
    unfold poolDisc; rw [hres, hrn]; rfl
  · rcases hs0r with hn | he
    · -- fresh
      right; left
      refine ⟨ρ, u0, u1, newRand_eq_single parameter data m hothers hn ⟨u0, hs0, hl⟩, ?_, hs0, hl, hs1, hn,
        hothers, fun hrn => (hfl hrn).2 hn, hsig⟩
      unfold poolDisc
      rw [hres]
      rcases r with _ | sig
      · rfl
      · simp only [Option.elim]
        rw [hsig sig rfl, ite_eq_left hn]
    · rcases r with _ | sig
      · left
        refine ⟨newRand_eq_empty_of_pool parameter data m hothers (by rw [he]; exact Option.some_ne_none _), ?_⟩
        unfold poolDisc; rw [hres]; rfl
      · right; right
        refine ⟨ρ, u0, u1, sig, newRand_eq_empty_of_pool parameter data m hothers (by rw [he]; exact Option.some_ne_none _),
          ?_, rfl, hsig sig rfl, he, hs0, hs1⟩
        unfold poolDisc
        rw [hres]
        simp only [Option.elim]
        rw [hsig sig rfl, ite_eq_right (by rw [he]; exact Option.some_ne_none _)]
        congr 1
        simp only [pview]
        change ((out.2.cache (blk parameter data m ρ 0)).elim _ fun u0 =>
          (out.2.cache (blk parameter data m ρ 1)).elim _ fun u1 => viewOf u0 u1) = _
        rw [hs0, hs1]
        rfl

end SignShape

/-! ### Upper values of a signing outcome -/

section SignUpper

variable (parameter : PublicParameter) (data : PublicData) (wbar : ℝ≥0∞) (m : Message) (s : State) (n : ℕ)
  (d : Multiset View) (f : Multiset View → ℝ≥0∞)

/-- The value without disclosure. -/
noncomputable def baseV (J : List View) : ℝ≥0∞ := virtual Finset.univ wbar f n J d

/-- Gain of a fresh view that is disclosed and becomes an item. -/
noncomputable def gainF (J : List View) (u : View) : ℝ≥0∞ :=
  virtual Finset.univ wbar f n (u :: J) (d + {u}) - baseV wbar n d f J

/-- Gain of disclosing an existing item. -/
noncomputable def gainP (J : List View) (v : View) : ℝ≥0∞ :=
  virtual Finset.univ wbar f n J (d + {v}) - baseV wbar n d f J

/-- Upper value of one signing outcome, for future items `J`. -/
noncomputable def upper (excl : Pair → Prop) (out : Run HashInput Coordinate (Option Signature) × State)
    (J : List View) : ℝ≥0∞ :=
  baseV wbar n d f J + freshNewWeight parameter data m s (gainF wbar n d f J) out +
    outWeight parameter data m s 0 (fun ρ v => if excl (m, ρ) then 0 else gainP wbar n d f J v) out

theorem related_self : Related parameter data m s s := ⟨fun _ => rfl, fun _ => Or.inl rfl⟩

variable {parameter data wbar m s n d f}

theorem pview_of_cached {s' : State} {q : Pair} {u0 u1 : HashOutput} (h0 : s'.cache (pblk parameter data q 0) = some u0)
    (h1 : s'.cache (pblk parameter data q 1) = some u1) : pview parameter data s' q = viewOf u0 u1 := by
  simp only [pview, h0, h1, Option.elim]

end SignUpper

/-! ### The fair-share hypotheses -/

section SignExpect

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)
  (parameter : PublicParameter) (data : PublicData) (wbar : ℝ≥0∞) (m : Message) (s : State) (n : ℕ)
  (d : Multiset View) (f : Multiset View → ℝ≥0∞)

/-- The fair-share hypotheses of the grinding signer. -/
structure Fair (Cmax : ℕ) : Prop where
  ne_top : wbar ≠ ⊤
  le_one : wbar ≤ 1
  cmax : Cmax ≤ 2 ^ 128
  share : ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ ≤ wbar * (((2 ^ 128 - Cmax : ℕ) : ℝ≥0∞) / ((2 ^ 128 : ℕ) : ℝ≥0∞)) * landing

end SignExpect

/-! ### The state after a signing call -/

section SignParams

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)
  (parameter : PublicParameter) (data : PublicData) (Fail : Finset (Fin (2 ^ subtreeHeight))) (Qtot : ℕ)
  (m : Message)

variable {parameter data m}

theorem other_message_kept (attempts budget : ℕ) (s : State)
    (out : Run HashInput Coordinate (Option Signature) × State)
    (hout : out ∈ support (interp tg initial model (signCostSourceLoop parameter data m attempts) budget s))
    (q : Pair) (hq : q.1 ≠ m) (call : Fin 2) :
    out.2.cache (pblk parameter data q call) = s.cache (pblk parameter data q call) := by
  refine interp_avoids_cache tg initial model _ _ (avoids_loop parameter data m attempts) budget s out hout _ ⟨?_, ?_⟩
  · exact msgInput_digestInput parameter data.root q.1 q.2 call
  · intro ρ c h
    exact hq (congrArg Prod.fst
      (pblk_injective parameter data (show pblk parameter data q call = pblk parameter data (m, ρ) c from h)).1)

theorem landed_of_cached {s : State} {P : List Pair} (hP : PInv parameter data s P) {q : Pair}
    (hq : q ∈ P) : ∃ u0 u1, s.cache (pblk parameter data q 0) = some u0 ∧ Landed parameter (blockIndex u0) ∧
      s.cache (pblk parameter data q 1) = some u1 := by
  obtain ⟨u0, h0, hl⟩ := (hP.mem q).1 hq
  obtain ⟨u1, h1⟩ := Option.ne_none_iff_exists'.1 (hP.second q ⟨u0, h0, hl⟩)
  exact ⟨u0, u1, h0, hl, h1⟩

/-- **The state after a signing call.** -/
theorem sign_params (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hfail : ∀ ρ digest budget (s1 : State), Prepared initial s1 →
      ∀ out ∈ support (interp tg initial model (finishRest parameter data m ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ Fail)
    (attempts budget : ℕ) (s : State) (P : List Pair) (d : Multiset View) (R : List Coordinate)
    (hprep : Prepared initial s) (hP : PInv parameter data s P) (hD : DInv R d)
    (hC : CountInv parameter data Qtot s budget)
    (out : Run HashInput Coordinate (Option Signature) × State)
    (hout : out ∈ support (interp tg initial model (signCostSourceLoop parameter data m attempts) budget s))
    (r : Option Signature) (hr : out.1.1 = some r) :
    Prepared initial out.2 ∧ PInv parameter data out.2 (newPairs parameter data m s out.2 ++ P) ∧
      DInv (R ++ out.1.2.1) (discAfter parameter data m s d out) ∧
      CountInv parameter data Qtot out.2 (budget - traceCost out.1.2.2.1) ∧
      (∀ q ∈ P, pview parameter data out.2 q = pview parameter data s q) := by
  have hext := interp_extends tg initial model _ budget s out hout
  have hpost := loop_post tg initial model parameter data m (fun ρ call => hparse (m, ρ) call) Fail hfail
    attempts budget s hprep out hout r hr
  have hother := other_message_kept tg initial model attempts budget s out hout
  -- every randomizer of the message is related, or the selected one
  have hrelOr : ∀ ρ, RelatedAt parameter data m s out.2 ρ ∨
      ∃ u0 u1, Selected parameter data m s out.2 ρ u0 u1 := by
    intro ρ
    rcases hpost with ⟨_, _, hrel⟩ | ⟨ρs, u0, u1, hsel, _⟩
    · exact Or.inl (hrel ρ)
    · by_cases h : ρ = ρs
      · subst h; exact Or.inr ⟨u0, u1, hsel⟩
      · exact Or.inl (hsel.2.2.2.2.2 ρ h)
  have hgrow : ∀ q call u, s.cache (pblk parameter data q call) = some u →
      out.2.cache (pblk parameter data q call) = some u := fun q call u h => hext.1 _ u h
  refine ⟨fun x v hx => hext.1 x v (hprep x v hx), ⟨?_, fun q => ?_, fun q hq => ?_, fun q hq => ?_⟩, ?_, ?_, ?_⟩
  · -- no duplicate items
    refine List.nodup_append.2 ⟨newPairs_nodup parameter data m s out.2, hP.nodup, fun a ha b hb hab => ?_⟩
    subst hab
    obtain ⟨_, h0, _⟩ := (mem_newPairs parameter data m s).1 ha
    obtain ⟨u, hu, _⟩ := (hP.mem a).1 hb
    rw [h0] at hu; cases hu
  · -- the items are the landed pairs
    rw [List.mem_append, mem_newPairs]
    constructor
    · rintro (⟨_, _, hl⟩ | hq)
      · exact hl
      · obtain ⟨u0, h0, hl⟩ := (hP.mem q).1 hq
        exact ⟨u0, hgrow q 0 u0 h0, hl⟩
    · rintro ⟨u0, h0, hl⟩
      cases hs0 : s.cache (pblk parameter data q 0) with
      | none =>
          left
          refine ⟨?_, rfl, ⟨u0, h0, hl⟩⟩
          by_contra hm
          rw [hother q hm 0, hs0] at h0
          cases h0
      | some u =>
          right
          have := hgrow q 0 u hs0
          rw [h0] at this
          cases this
          exact (hP.mem q).2 ⟨u0, hs0, hl⟩
  · -- landed pairs have both blocks
    obtain ⟨u0, h0, hl⟩ := hq
    cases hs0 : s.cache (pblk parameter data q 0) with
    | some u =>
        have := hgrow q 0 u hs0
        rw [h0] at this
        cases this
        obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 (hP.second q ⟨u0, hs0, hl⟩)
        rw [hgrow q 1 v hv]
        exact Option.some_ne_none _
    | none =>
        have hm : q.1 = m := by
          by_contra hm
          rw [hother q hm 0, hs0] at h0
          cases h0
        obtain ⟨msg, ρ⟩ := q
        simp only at hm
        subst hm
        rcases hrelOr ρ with hrel | ⟨u0', u1', hsel⟩
        · rcases hrel.2 with he | ⟨_, u, hu, hnl⟩
          · change out.2.cache (blk parameter data msg ρ 0) = some u0 at h0
            rw [he] at h0
            change s.cache (blk parameter data msg ρ 0) = none at hs0
            rw [hs0] at h0; cases h0
          · change out.2.cache (blk parameter data msg ρ 0) = some u0 at h0
            rw [hu] at h0; cases h0; exact absurd hl hnl
        · change out.2.cache (blk parameter data msg ρ 1) ≠ none
          rw [hsel.2.2.1]
          exact Option.some_ne_none _
  · -- no pair has only its second block
    have hs0 : s.cache (pblk parameter data q 0) = none := by
      cases hc : s.cache (pblk parameter data q 0) with
      | none => rfl
      | some u => rw [hgrow q 0 u hc] at hq; cases hq
    have hs1 := hP.first q hs0
    by_cases hm : q.1 = m
    · obtain ⟨msg, ρ⟩ := q
      simp only at hm
      subst hm
      rcases hrelOr ρ with hrel | ⟨u0', u1', hsel⟩
      · change out.2.cache (blk parameter data msg ρ 1) = none
        rw [hrel.1]; exact hs1
      · change out.2.cache (blk parameter data msg ρ 0) = none at hq
        rw [hsel.1] at hq; cases hq
    · rw [hother q hm 1]; exact hs1
  · -- every revealed secret has a disclosed view
    intro i t l hmem
    rcases List.mem_append.1 hmem with hR | hrev
    · obtain ⟨v, hv, h1, h2⟩ := hD i t l hR
      exact ⟨v, Multiset.mem_add.2 (Or.inl (Multiset.mem_add.2 (Or.inl hv))), h1, h2⟩
    · rcases hpost with ⟨_, hnil, _⟩ | ⟨ρs, u0, u1, hsel, hfts, hsig, hfl⟩
      · rw [hnil] at hrev; cases hrev
      · obtain ⟨hi, hl⟩ := hfts _ hrev i t l rfl
        refine ⟨viewOf u0 u1, ?_, by rw [hi]; rfl, by rw [hl]; rfl⟩
        have hv : pview parameter data out.2 (m, ρs) = viewOf u0 u1 := pview_of_cached hsel.1 hsel.2.2.1
        rcases r with _ | sig
        · rw [(hfl rfl).1] at hrev; cases hrev
        · unfold discAfter
          rcases hsel.2.2.2.1 with hn | he
          · have hnew : (m, ρs) ∈ newPairs parameter data m s out.2 :=
              (mem_newPairs parameter data m s).2 ⟨rfl, hn, ⟨u0, hsel.1, hsel.2.1⟩⟩
            refine Multiset.mem_add.2 (Or.inl (Multiset.mem_add.2 (Or.inr ?_)))
            rw [Multiset.mem_coe, ← hv]
            exact List.mem_map_of_mem hnew
          · refine Multiset.mem_add.2 (Or.inr ?_)
            unfold poolDisc
            rw [hr]
            simp only [Option.elim]
            rw [hsig sig rfl, he, ite_eq_right (Option.some_ne_none _), hv]
            exact Multiset.mem_singleton_self _
  · -- the count of cached randomizers
    intro m'
    have h1 : cachedCount parameter data m' out.2 ≤ cachedCount parameter data m' s + traceCost out.1.2.2.1 := by
      rw [cachedCount_eq, cachedCount_eq]
      exact interp_card_le tg initial model _ _ budget s out hout
    have h2 := interp_traceCost_le tg initial model _ budget s out hout
    have h3 := hC m'
    omega
  · -- items keep their views
    intro q hq
    obtain ⟨u0, u1, h0, _, h1⟩ := landed_of_cached hP hq
    rw [pview_of_cached h0 h1, pview_of_cached (hgrow q 0 u0 h0) (hgrow q 1 u1 h1)]

end SignParams

/-! ### The bound for one signing outcome -/

section SignPoint

variable (parameter : PublicParameter) (data : PublicData) (wbar b0 : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))
  (m : Message) (s : State) (P : List Pair) (L : QueryLog SigningSpec) (d : Multiset View)

omit [Params] in
theorem erase_eq_filter' {P : List Pair} (hP : P.Nodup) (q : Pair) : P.erase q = others (· = q) P := by
  rw [hP.erase_eq_filter]
  unfold others
  congr 1
  funext q'
  rw [Bool.eq_iff_iff]
  simp [bne_iff_ne]

omit [Params] in
theorem filter_false' (P : List Pair) : others (fun _ => False) P = P := by unfold others; simp

/-- Bound for one outcome of a signing call. -/
noncomputable def canon (n k : ℕ) (out : Run HashInput Coordinate (Option Signature) × State) : ℝ≥0∞ :=
  freshNewWeight parameter data m s (fun v => if v.1 ∈ Fail then 1 else 0) out +
  (P.map fun q => if Unsigned L q then (if (pview parameter data s q).1 ∈ Fail then 1 else
      creations Finset.univ landing (fun J => upper parameter data wbar m s n d (witnessFn (pview parameter data s q))
        (· = q) out J) k (items parameter data s (others (· = q) P))) else 0).sum +
  k * (creations Finset.univ landing (fun J => upper parameter data wbar m s n d (excess b0) (fun _ => False) out J) k
      (items parameter data s (others (fun _ => False) P)) + failMass Fail) +
  n * failMass Fail

variable {parameter data wbar b0 Fail m s P L d}

theorem freshNewWeight_ge {out : Run HashInput Coordinate (Option Signature) × State} {r : Option Signature}
    (hres : out.1.1 = some r) {ρ : Randomness} {u0 u1 : HashOutput}
    (hs1 : s.cache (blk parameter data m ρ 1) = none) (h0 : out.2.cache (blk parameter data m ρ 0) = some u0)
    (hl : Landed parameter (blockIndex u0)) (h1 : out.2.cache (blk parameter data m ρ 1) = some u1)
    (g : View → ℝ≥0∞) : g (viewOf u0 u1) ≤ freshNewWeight parameter data m s g out := by
  unfold freshNewWeight
  rw [ite_eq_left (by rw [hres]; rfl)]
  refine le_trans (le_of_eq ?_) (Finset.single_le_sum (f := fun ρ' => if s.cache (blk parameter data m ρ' 1) = none then
    (out.2.cache (blk parameter data m ρ' 0)).elim 0 (fun u0 =>
      (out.2.cache (blk parameter data m ρ' 1)).elim 0 fun u1 =>
        if Landed parameter (blockIndex u0) then g (viewOf u0 u1) else 0) else 0)
    (fun _ _ => bot_le) (Finset.mem_univ ρ))
  simp only [hs1, h0, h1, Option.elim, ite_true, ite_eq_left hl]

omit [Params] in
theorem unsigned_of_append {L : QueryLog SigningSpec} {e : (_ : Message) × Option Signature} {q : Pair}
    (h : Unsigned (L ++ [e]) q) : Unsigned L q :=
  fun entry he sig hs => h entry (List.mem_append_left _ he) sig hs

omit [Params] in
theorem not_unsigned_signed {L : QueryLog SigningSpec} {sig : Signature} :
    ¬Unsigned (L ++ [⟨m, some sig⟩]) (m, sig.randomness) := fun h =>
  h ⟨m, some sig⟩ (List.mem_append_right _ (List.mem_singleton_self _)) sig rfl ⟨rfl, rfl⟩

end SignPoint

/-! ### Interpreting a continuation -/

section SignGood

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)
  (parameter : PublicParameter) (data : PublicData) (wbar b0 : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))
  (Qtot : ℕ)

omit [Params] in
theorem interpThen_some {α β : Type} (next : α → OracleComp CostSpec β) (budget : ℕ)
    (o1 : Run HashInput Coordinate α × State) (v : α) (hv : o1.1.1 = some v) :
    interpThen tg initial model next budget o1 =
      (fun o2 => ((o2.1.1, o1.1.2.1 ++ o2.1.2.1, o1.1.2.2.1 ++ o2.1.2.2.1, o1.1.2.2.2 ++ o2.1.2.2.2), o2.2)) <$>
        interp tg initial model (next v) (budget - traceCost o1.1.2.2.1) o1.2 := by
  unfold interpThen
  rw [hv]

omit [Params] in
theorem interpThen_none {α β : Type} (next : α → OracleComp CostSpec β) (budget : ℕ)
    (o1 : Run HashInput Coordinate α × State) (hv : o1.1.1 = none) :
    interpThen tg initial model next budget o1 = pure ((none, o1.1.2.1, o1.1.2.2.1, o1.1.2.2.2), o1.2) := by
  unfold interpThen
  rw [hv]

end SignGood

end SphincsFors.Security.ForsPotential
