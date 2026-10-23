import Sphincs.BridgeForsPotentialOnce
import Sphincs.GroupHeavy

/-! The heavy message of the large route, term level. The one-coin potential of the scan signer pays
a digest query of a live message by one future coin while the group of the message keeps mass on the
identity. One message, the heavy one (more than half of the total budget spent on its digests), is
treated by the law of its signed view `sgn` instead, which needs no coin: a digest query keeps its
mean exactly, and it consumes one fresh slot, taken from a spare slot that every term carries while
no live message is heavy. -/

open OracleComp OracleSpec ENNReal

/-! ### More algebra of the law of the signed view -/

namespace Sphincs.LoopWalk

open SphincsFors.Security.Domination Sphincs.Security.Domination

variable {α V : Type} [Fintype α] [DecidableEq α] {σ : Equiv.Perm α} {p : ℝ≥0∞} {A : ℕ} {U : Finset V}

omit [DecidableEq α] in
theorem ws_const (hp : p ≤ 1) (st : α → St) (c : ℝ≥0∞) :
    ws σ p A st (fun _ => c) c c = (Fintype.card α : ℝ≥0∞) * c := by
  unfold ws
  simp only [walk_const hp st c A, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

omit [DecidableEq α] in
/-- A constant is kept. -/
theorem sgn_const [Nonempty α] (hp : p ≤ 1) (hU : U.Nonempty) (st : α → St) (ext : α → Multiset V) (c : ℝ≥0∞)
    (d : Multiset V) : sgn σ p A U st ext (fun _ => c) d = c := by
  unfold sgn
  rw [freshAvg_const U hU, ws_const hp, ← mul_assoc,
    ENNReal.inv_mul_cancel (by exact_mod_cast Fintype.card_ne_zero) (ENNReal.natCast_ne_top _), one_mul]

omit [DecidableEq α] in
/-- The law of the signed view only adds disclosures. -/
theorem le_sgn [Nonempty α] (hp : p ≤ 1) (hU : U.Nonempty) (st : α → St) (ext : α → Multiset V)
    {F : Multiset V → ℝ≥0∞} (hF : Monotone' F) (d : Multiset V) : F d ≤ sgn σ p A U st ext F d :=
  (le_grp hp hU st ext hF d).trans (grp_le_sgn hU st ext hF d)

omit [DecidableEq α] in
theorem sgn_ne_top [Nonempty α] (hp : p ≤ 1) (hU : U.Nonempty) (st : α → St) (ext : α → Multiset V)
    {F : Multiset V → ℝ≥0∞} (hF : ∀ e, F e ≠ ⊤) (d : Multiset V) : sgn σ p A U st ext F d ≠ ⊤ := by
  set B := (∑ x, F (d + ext x)) + F d + freshAvg U (fun v => F (d + {v})) with hB
  have hBt : B ≠ ⊤ := ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ENNReal.sum_ne_top.2 fun x _ => hF _, hF d⟩,
    freshAvg_ne_top hU fun _ => hF _⟩
  refine ne_top_of_le_ne_top hBt ?_
  unfold sgn
  calc (Fintype.card α : ℝ≥0∞)⁻¹ * ws σ p A st (fun x => F (d + ext x)) (freshAvg U fun v => F (d + {v})) (F d)
      ≤ (Fintype.card α : ℝ≥0∞)⁻¹ * ws σ p A st (fun _ => B) B B := by
        refine mul_le_mul' le_rfl (ws_mono st (fun x => ?_) ?_ ?_)
        · exact le_trans (Finset.single_le_sum (f := fun x => F (d + ext x)) (fun _ _ => bot_le)
            (Finset.mem_univ x)) (le_trans le_self_add le_self_add)
        · exact le_add_self
        · exact le_trans le_add_self le_self_add
    _ = B := by
        rw [ws_const hp, ← mul_assoc,
          ENNReal.inv_mul_cancel (by exact_mod_cast Fintype.card_ne_zero) (ENNReal.natCast_ne_top _), one_mul]

omit [DecidableEq α] in
/-- The law of the signed view commutes with averages. -/
theorem sgn_freshAvg {W : Type} [DecidableEq W] (T : Finset W) (st : α → St) (ext : α → Multiset V)
    (h : W → Multiset V → ℝ≥0∞) (d : Multiset V) :
    sgn σ p A U st ext (fun e => freshAvg T fun t => h t e) d =
      freshAvg T (fun t => sgn σ p A U st ext (h t) d) := by
  unfold sgn
  rw [freshAvg_comm T (fun v t => h t (d + {v}))]
  simp only [freshAvg]
  rw [ws_const_mul, ws_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  ring

omit [DecidableEq α] in
/-- The law of the signed view commutes with one coin. -/
theorem sgn_coin (st : α → St) (ext : α → Multiset V) (F : Multiset V → ℝ≥0∞) (w : ℝ≥0∞) (m d : Multiset V) :
    sgn σ p A U st ext (fun e => w * F (e + m) + (1 - w) * F e) d =
      w * sgn σ p A U st ext F (d + m) + (1 - w) * sgn σ p A U st ext F d := by
  rw [sgn_add st ext (fun e => w * F (e + m)) (fun e => (1 - w) * F e), sgn_const_mul, sgn_const_mul,
    sgn_shift]

omit [DecidableEq α] in
/-- Only the disclosures of cached hits matter. -/
theorem sgn_congr_ext (st : α → St) {ext ext' : α → Multiset V} (h : ∀ x, st x = .hit → ext x = ext' x)
    (F : Multiset V → ℝ≥0∞) (d : Multiset V) : sgn σ p A U st ext F d = sgn σ p A U st ext' F d := by
  unfold sgn ws
  congr 1
  exact Finset.sum_congr rfl fun r _ => walk_congr_item st _ _ (fun x hx => by rw [h x hx]) A r

omit [DecidableEq α] in
/-- Disclosing less at the hits can only lower the law of the signed view of a monotone function. -/
theorem sgn_ext_mono (st : α → St) {ext ext' : α → Multiset V} (h : ∀ x, ext x ≤ ext' x) {F : Multiset V → ℝ≥0∞}
    (hF : Monotone' F) (d : Multiset V) : sgn σ p A U st ext F d ≤ sgn σ p A U st ext' F d := by
  unfold sgn
  exact mul_le_mul' le_rfl (ws_mono st (fun x => hF _ _ (add_le_add le_rfl (h x))) le_rfl le_rfl)

/-- **A stopped law is below the law.** A position that becomes a hit disclosing nothing can only
lower the law of the signed view of a monotone function. -/
theorem sgn_stop_le (hp : p ≤ 1) (hU : U.Nonempty) (st : α → St) (ext : α → Multiset V) {F : Multiset V → ℝ≥0∞}
    (hF : Monotone' F) (d : Multiset V) (y : α) :
    sgn σ p A U (Function.update st y .hit) (Function.update ext y 0) F d ≤ sgn σ p A U st ext F d := by
  have hbf : F d ≤ freshAvg U (fun v => F (d + {v})) := by
    calc F d = freshAvg U (fun _ => F d) := (freshAvg_const U hU _).symm
      _ ≤ _ := freshAvg_mono U fun v _ => hF _ _ (Multiset.le_add_right _ _)
  have hitem : (fun x => F (d + Function.update ext y 0 x)) = Function.update (fun x => F (d + ext x)) y (F d) := by
    funext x
    by_cases hx : x = y
    · subst hx; simp
    · simp [Function.update_of_ne hx]
  unfold sgn ws
  rw [hitem]
  exact mul_le_mul' le_rfl (Finset.sum_le_sum fun r _ =>
    walk_stop_le hp st (fun x => hF _ _ (Multiset.le_add_right _ _)) hbf le_rfl y A r)

end Sphincs.LoopWalk

namespace Sphincs.Security.ForsPotential

open SphincsFors.Security
open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForestPrice ForestSigner
  SphincsFors.Security.Domination Sphincs.LoopWalk

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

variable [Params]

/-! ### The total count and the heavy message -/

section Count

variable (parameter : PublicParameter) (data : PublicData)

/-- The cached digest blocks, over all messages. -/
noncomputable def totalCount (s : State) : ℕ :=
  (Finset.univ.filter fun q : Pair => s.cache (pblk parameter data q) ≠ none).card

/-- The cached digest blocks plus the remaining budget stay bounded. -/
def TotalInv (Qtot : ℕ) (s : State) (budget : ℕ) : Prop := totalCount parameter data s + budget ≤ Qtot

/-- More than half of the total budget was spent on the digests of the message. -/
def Heavy (Qtot : ℕ) (s : State) (m : Message) : Prop := Qtot < 2 * cachedCount parameter data m s

/-- The digest inputs of all pairs. -/
noncomputable def pairInputs : Finset HashInput := Finset.univ.image fun q : Pair => pblk parameter data q

variable {parameter data}

omit [Params] in
theorem totalCount_eq (s : State) :
    totalCount parameter data s = ((pairInputs parameter data).filter fun x => s.cache x ≠ none).card := by
  unfold totalCount pairInputs
  rw [Finset.filter_image, Finset.card_image_of_injective _ (fun a b h => pblk_injective parameter data h)]

omit [Params] in
theorem cachedCount_le_total (m : Message) (s : State) :
    cachedCount parameter data m s ≤ totalCount parameter data s := by
  unfold cachedCount totalCount
  refine Finset.card_le_card_of_injOn (fun ρ => ((m, ρ) : Pair)) (fun ρ hρ => ?_)
    (fun a _ b _ h => (Prod.ext_iff.1 h).2)
  rw [Finset.mem_coe, Finset.mem_filter] at hρ
  have h2 : s.cache (pblk parameter data (m, ρ)) ≠ none := hρ.2
  rw [Finset.mem_coe, Finset.mem_filter]
  exact ⟨by simp, h2⟩

omit [Params] in
theorem cachedCount_add_le {m m' : Message} (h : m ≠ m') (s : State) :
    cachedCount parameter data m s + cachedCount parameter data m' s ≤ totalCount parameter data s := by
  have h1 : cachedCount parameter data m s =
      ((Finset.univ.filter fun ρ : Randomness => s.cache (blk parameter data m ρ) ≠ none).image
        fun ρ => ((m, ρ) : Pair)).card :=
    (Finset.card_image_of_injective _ (fun a b hab => (Prod.ext_iff.1 hab).2)).symm
  have h2 : cachedCount parameter data m' s =
      ((Finset.univ.filter fun ρ : Randomness => s.cache (blk parameter data m' ρ) ≠ none).image
        fun ρ => ((m', ρ) : Pair)).card :=
    (Finset.card_image_of_injective _ (fun a b hab => (Prod.ext_iff.1 hab).2)).symm
  have hdisj : Disjoint
      ((Finset.univ.filter fun ρ : Randomness => s.cache (blk parameter data m ρ) ≠ none).image
        fun ρ => ((m, ρ) : Pair))
      ((Finset.univ.filter fun ρ : Randomness => s.cache (blk parameter data m' ρ) ≠ none).image
        fun ρ => ((m', ρ) : Pair)) := by
    rw [Finset.disjoint_left]
    intro q hq1 hq2
    obtain ⟨ρ, _, rfl⟩ := Finset.mem_image.1 hq1
    obtain ⟨ρ', _, h'⟩ := Finset.mem_image.1 hq2
    exact h (congrArg Prod.fst h').symm
  rw [h1, h2, ← Finset.card_union_of_disjoint hdisj]
  unfold totalCount
  refine Finset.card_le_card fun q hq => ?_
  rw [Finset.mem_union, Finset.mem_image, Finset.mem_image] at hq
  rw [Finset.mem_filter]
  rcases hq with ⟨ρ, hρ, rfl⟩ | ⟨ρ, hρ, rfl⟩
  · have h2 : s.cache (pblk parameter data (m, ρ)) ≠ none := (Finset.mem_filter.1 hρ).2
    exact ⟨by simp, h2⟩
  · have h2 : s.cache (pblk parameter data (m', ρ)) ≠ none := (Finset.mem_filter.1 hρ).2
    exact ⟨by simp, h2⟩

omit [Params] in
/-- The total invariant implies the count invariant of every message. -/
theorem TotalInv.countInv {Qtot : ℕ} {s : State} {budget : ℕ} (hT : TotalInv parameter data Qtot s budget) :
    CountInv parameter data Qtot s budget := by
  intro m
  have := cachedCount_le_total (parameter := parameter) (data := data) m s
  unfold TotalInv at hT
  omega

omit [Params] in
/-- **At most one message is heavy.** -/
theorem heavy_unique {Qtot : ℕ} {s : State} {budget : ℕ} (hT : TotalInv parameter data Qtot s budget)
    {m m' : Message} (h : Heavy parameter data Qtot s m) (h' : Heavy parameter data Qtot s m') : m = m' := by
  by_contra hne
  have := cachedCount_add_le (parameter := parameter) (data := data) hne s
  unfold Heavy at h h'
  unfold TotalInv at hT
  omega

omit [Params] in
/-- A message that is not heavy has at most `Qtot / 2` cached digests. -/
theorem cachedCount_le_of_not_heavy {Qtot : ℕ} {s : State} {m : Message} (h : ¬Heavy parameter data Qtot s m) :
    cachedCount parameter data m s ≤ Qtot / 2 := by
  unfold Heavy at h
  omega

omit [Params] in
theorem cachedCount_mono {s s' : State} (h : Extends s s') (m : Message) :
    cachedCount parameter data m s ≤ cachedCount parameter data m s' := by
  unfold cachedCount
  refine Finset.card_le_card fun ρ hρ => ?_
  rw [Finset.mem_filter] at hρ ⊢
  obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 hρ.2
  exact ⟨hρ.1, by rw [h.1 _ v hv]; exact Option.some_ne_none v⟩

omit [Params] in
/-- Heaviness is monotone along extensions of the state. -/
theorem Heavy.mono {Qtot : ℕ} {s s' : State} (hext : Extends s s') {m : Message}
    (h : Heavy parameter data Qtot s m) : Heavy parameter data Qtot s' m := by
  have := cachedCount_mono (parameter := parameter) (data := data) hext m
  unfold Heavy at h ⊢
  omega

omit [Params] in
theorem cachedCount_congr {s s' : State} {m : Message}
    (h : ∀ ρ, s'.cache (blk parameter data m ρ) = s.cache (blk parameter data m ρ)) :
    cachedCount parameter data m s' = cachedCount parameter data m s := by
  unfold cachedCount
  simp only [h]

omit [Params] in
theorem heavy_congr {Qtot : ℕ} {s s' : State} {m : Message}
    (h : ∀ ρ, s'.cache (blk parameter data m ρ) = s.cache (blk parameter data m ρ)) :
    Heavy parameter data Qtot s' m ↔ Heavy parameter data Qtot s m := by
  unfold Heavy
  rw [cachedCount_congr h]

omit [Params] in
theorem heavy_withPair_other {Qtot : ℕ} (s : State) (p : Pair) (u0 : HashOutput) {m : Message} (hm : m ≠ p.1) :
    Heavy parameter data Qtot (withPair parameter data s p u0) m ↔ Heavy parameter data Qtot s m :=
  heavy_congr fun ρ => withPair_other_pair s p (m, ρ) (fun h => hm (congrArg Prod.fst h)) u0

omit [Params] in
/-- Heaviness after a new pair does not depend on the value of its block. -/
theorem heavy_withPair_value {Qtot : ℕ} (s : State) (p : Pair) (u0 u0' : HashOutput) (m : Message) :
    Heavy parameter data Qtot (withPair parameter data s p u0) m ↔
      Heavy parameter data Qtot (withPair parameter data s p u0') m := by
  have hc : ∀ u : HashOutput, cachedCount parameter data m (withPair parameter data s p u) =
      (Finset.univ.filter fun ρ : Randomness => (m, ρ) = p ∨ s.cache (blk parameter data m ρ) ≠ none).card := by
    intro u
    unfold cachedCount
    refine congrArg Finset.card (Finset.filter_congr fun ρ _ => ?_)
    by_cases hq : ((m, ρ) : Pair) = p
    · have h1 : (withPair parameter data s p u).cache (blk parameter data m ρ) = some u := by
        rw [← hq]; exact withPair_self s (m, ρ) u
      simp [h1, hq]
    · have h1 : (withPair parameter data s p u).cache (blk parameter data m ρ) = s.cache (blk parameter data m ρ) :=
        withPair_other_pair s p (m, ρ) hq u
      simp [h1, hq]
  unfold Heavy
  rw [hc u0, hc u0']

end Count

/-! ### The total invariant is kept -/

section TotalKept

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)
  {parameter : PublicParameter} {data : PublicData} {Qtot : ℕ}

omit [Params] in
theorem totalCount_withPair (s : State) (p : Pair) (u0 : HashOutput) :
    totalCount parameter data (withPair parameter data s p u0) ≤ totalCount parameter data s + 1 := by
  rw [totalCount_eq, totalCount_eq]
  unfold withPair
  exact card_filter_store_le _ _ _ _

omit [Params] in
/-- **A new pair keeps the total invariant.** -/
theorem totalInv_withPair {s : State} {budget : ℕ} (hT : TotalInv parameter data Qtot s budget) (hb : 1 ≤ budget)
    (p : Pair) (u0 : HashOutput) : TotalInv parameter data Qtot (withPair parameter data s p u0) (budget - 1) := by
  have := totalCount_withPair (parameter := parameter) (data := data) s p u0
  unfold TotalInv at hT ⊢
  omega

omit [Params] in
/-- **An ordinary query keeps the total invariant.** -/
theorem totalInv_ordinary {s : State} {budget : ℕ} (hT : TotalInv parameter data Qtot s budget) (hb : 1 ≤ budget)
    (x : HashInput) (r : HashOutput × State) (hr : r ∈ support (ordinaryStep model x s.known s)) :
    TotalInv parameter data Qtot r.2 (budget - 1) := by
  have h1 : totalCount parameter data r.2 ≤ totalCount parameter data s + 1 := by
    rw [totalCount_eq, totalCount_eq]
    exact costStep_card_le model _ (.inl (.inr (.inl x))) s r (by rw [costStep_ordinary]; exact hr)
  unfold TotalInv at hT ⊢
  omega

omit [Params] in
/-- **A program keeps the total invariant**, in particular a signing call. -/
theorem totalInv_interp {α : Type} (prog : OracleComp CostSpec α) {s : State} {budget : ℕ}
    (hT : TotalInv parameter data Qtot s budget) (out : Run HashInput Coordinate α × State)
    (hout : out ∈ support (interp tg initial model prog budget s)) :
    TotalInv parameter data Qtot out.2 (budget - traceCost out.1.2.2.1) := by
  have h1 : totalCount parameter data out.2 ≤ totalCount parameter data s + traceCost out.1.2.2.1 := by
    rw [totalCount_eq, totalCount_eq]
    exact interp_card_le tg initial model _ _ budget s out hout
  have h2 := interp_traceCost_le tg initial model _ budget s out hout
  unfold TotalInv at hT ⊢
  omega

end TotalKept

/-! ### Terms -/

section TermsH

variable (parameter : PublicParameter) (data : PublicData)

/-- **The law of the signed view of a message** applied to a base function. -/
noncomputable def sgnM (s : State) (excl : Pair → Prop) (m : Message) (F : Multiset View → ℝ≥0∞)
    (d : Multiset View) : ℝ≥0∞ :=
  sgn nextRand landing digestAttemptLimit Finset.univ (stOf parameter data m s) (extOf parameter data s excl m) F d

variable (Qtot : ℕ)

/-- The messages of a list that are not heavy: they act through their groups. -/
noncomputable def lightMsgs (s : State) (l : List Message) : List Message :=
  l.filter fun m => decide (¬Heavy parameter data Qtot s m)

/-- The heavy message of a list, if any (unique under the total invariant). -/
noncomputable def heavyMsg (s : State) (l : List Message) : Option Message :=
  l.find? fun m => decide (Heavy parameter data Qtot s m)

variable (w : ℝ≥0∞)

/-- **The inner function of a term**, for `n` signatures left: the law of the signed view of the heavy
message on the one-coin future, or the one-coin future with one spare slot. -/
noncomputable def innerH (s : State) (excl : Pair → Prop) (hv : Option Message) (f : Multiset View → ℝ≥0∞) (n : ℕ)
    (I : List View) : Multiset View → ℝ≥0∞ :=
  match hv with
  | some h => sgnM parameter data s excl h (virtualOnce Finset.univ w f n I)
  | none => virtualOnce Finset.univ w f (n + 1) I

/-- The groups of a list of light messages on the inner function. -/
noncomputable def valH (s : State) (excl : Pair → Prop) (Ls : List Message) (hv : Option Message)
    (f : Multiset View → ℝ≥0∞) (n : ℕ) (I : List View) : Multiset View → ℝ≥0∞ :=
  grpAll parameter data s excl Ls (innerH parameter data w s excl hv f n I)

/-- The base of a term: the groups of the live light messages on the inner function. -/
noncomputable def baseH (s : State) (Ms : List Message) (L : QueryLog SigningSpec) (excl : Pair → Prop)
    (f : Multiset View → ℝ≥0∞) (d : Multiset View) (n : ℕ) (I : List View) : ℝ≥0∞ :=
  valH parameter data w s excl (lightMsgs parameter data Qtot s (live L Ms))
    (heavyMsg parameter data Qtot s (live L Ms)) f n I d

/-- **The forecast of a term**, with one message treated by the law of its signed view. -/
noncomputable def termH (s : State) (Ms : List Message) (L : QueryLog SigningSpec) (excl : Pair → Prop)
    (f : Multiset View → ℝ≥0∞) (d : Multiset View) (n k : ℕ) : ℝ≥0∞ :=
  creations Finset.univ landing (baseH parameter data Qtot w s Ms L excl f d n) k []

end TermsH

section Lists

variable {parameter : PublicParameter} {data : PublicData} {Qtot : ℕ}

omit [Params] in
theorem mem_lightMsgs {s : State} {l : List Message} {m : Message} :
    m ∈ lightMsgs parameter data Qtot s l ↔ m ∈ l ∧ ¬Heavy parameter data Qtot s m := by
  unfold lightMsgs; simp

omit [Params] in
theorem heavyMsg_eq_none {s : State} {l : List Message} :
    heavyMsg parameter data Qtot s l = none ↔ ∀ m ∈ l, ¬Heavy parameter data Qtot s m := by
  unfold heavyMsg; simp

omit [Params] in
/-- The heavy message of a list is in the list and heavy. -/
theorem heavyMsg_some {s : State} {l : List Message} {h : Message} (hh : heavyMsg parameter data Qtot s l = some h) :
    h ∈ l ∧ Heavy parameter data Qtot s h := by
  unfold heavyMsg at hh
  exact ⟨List.mem_of_find?_eq_some hh, by simpa using List.find?_some hh⟩

omit [Params] in
/-- A heavy message of a list in which it is the only heavy one is the heavy message of the list. -/
theorem heavyMsg_eq_some {s : State} {l : List Message} {h : Message} (hmem : h ∈ l)
    (hh : Heavy parameter data Qtot s h) (huniq : ∀ m ∈ l, Heavy parameter data Qtot s m → m = h) :
    heavyMsg parameter data Qtot s l = some h := by
  cases hfind : heavyMsg parameter data Qtot s l with
  | none => exact absurd hh (heavyMsg_eq_none.1 hfind h hmem)
  | some h' =>
      obtain ⟨h1, h2⟩ := heavyMsg_some hfind
      rw [huniq h' h1 h2]

omit [Params] in
/-- Under the total invariant: `some h` iff `h` is in the list and heavy. -/
theorem heavyMsg_eq_some_iff {s : State} {budget : ℕ} (hT : TotalInv parameter data Qtot s budget)
    {l : List Message} {h : Message} :
    heavyMsg parameter data Qtot s l = some h ↔ h ∈ l ∧ Heavy parameter data Qtot s h :=
  ⟨heavyMsg_some, fun hh => heavyMsg_eq_some hh.1 hh.2 fun _ _ hm => heavy_unique hT hm hh.2⟩

omit [Params] in
theorem find?_congr' {α : Type} {p q : α → Bool} : ∀ (l : List α), (∀ a ∈ l, p a = q a) → l.find? p = l.find? q
  | [], _ => rfl
  | a :: l, h => by
      rw [List.find?_cons, List.find?_cons, h a (List.mem_cons_self ..),
        find?_congr' l (fun b hb => h b (List.mem_cons_of_mem _ hb))]

omit [Params] in
theorem lightMsgs_congr {s s' : State} {l : List Message}
    (h : ∀ m ∈ l, (Heavy parameter data Qtot s' m ↔ Heavy parameter data Qtot s m)) :
    lightMsgs parameter data Qtot s' l = lightMsgs parameter data Qtot s l := by
  unfold lightMsgs
  refine List.filter_congr fun m hm => ?_
  rw [Bool.eq_iff_iff]
  simp [h m hm]

omit [Params] in
theorem heavyMsg_congr {s s' : State} {l : List Message}
    (h : ∀ m ∈ l, (Heavy parameter data Qtot s' m ↔ Heavy parameter data Qtot s m)) :
    heavyMsg parameter data Qtot s' l = heavyMsg parameter data Qtot s l := by
  unfold heavyMsg
  refine find?_congr' l fun m hm => ?_
  rw [Bool.eq_iff_iff]
  simp [h m hm]

omit [Params] in
/-- Without a heavy message, every message is light. -/
theorem lightMsgs_of_none {s : State} {l : List Message} (h : heavyMsg parameter data Qtot s l = none) :
    lightMsgs parameter data Qtot s l = l := by
  unfold lightMsgs
  exact List.filter_eq_self.2 fun m hm => by simpa using heavyMsg_eq_none.1 h m hm

omit [Params] in
/-- The list is its heavy message and its light messages. -/
theorem perm_heavy_cons {s : State} {l : List Message} {h : Message} (hnd : l.Nodup)
    (hh : heavyMsg parameter data Qtot s l = some h) (huniq : ∀ m ∈ l, Heavy parameter data Qtot s m → m = h) :
    l.Perm (h :: lightMsgs parameter data Qtot s l) := by
  obtain ⟨hmem, hheavy⟩ := heavyMsg_some hh
  refine (List.perm_cons_erase hmem).trans (List.Perm.cons h (List.Perm.of_eq ?_))
  rw [hnd.erase_eq_filter]
  unfold lightMsgs
  refine List.filter_congr fun m hm => ?_
  rw [Bool.eq_iff_iff]
  simp only [bne_iff_ne, ne_eq, decide_eq_true_eq]
  exact ⟨fun hne hm' => hne (huniq m hm hm'), fun hnh heq => hnh (heq ▸ hheavy)⟩

omit [Params] in
theorem lightMsgs_nodup {s : State} {l : List Message} (h : l.Nodup) : (lightMsgs parameter data Qtot s l).Nodup :=
  h.filter _

end Lists

/-! ### The inner function -/

section InnerH

variable {parameter : PublicParameter} {data : PublicData} {w : ℝ≥0∞}

theorem innerH_some (s : State) (excl : Pair → Prop) (h : Message) (f : Multiset View → ℝ≥0∞) (n : ℕ) (I : List View) :
    innerH parameter data w s excl (some h) f n I = sgnM parameter data s excl h (virtualOnce Finset.univ w f n I) := rfl

theorem innerH_none (s : State) (excl : Pair → Prop) (f : Multiset View → ℝ≥0∞) (n : ℕ) (I : List View) :
    innerH parameter data w s excl none f n I = virtualOnce Finset.univ w f (n + 1) I := rfl

theorem sgnM_mono (s : State) (excl : Pair → Prop) (m : Message) {F : Multiset View → ℝ≥0∞} (hF : Monotone' F) :
    Monotone' (sgnM parameter data s excl m F) := sgn_mono _ _ hF

theorem sgnM_ne_top (s : State) (excl : Pair → Prop) (m : Message) {F : Multiset View → ℝ≥0∞} (hF : ∀ e, F e ≠ ⊤)
    (d : Multiset View) : sgnM parameter data s excl m F d ≠ ⊤ :=
  sgn_ne_top landing_le_one Finset.univ_nonempty _ _ hF d

theorem sgnM_le_of_le (s : State) (excl : Pair → Prop) (m : Message) {F G : Multiset View → ℝ≥0∞}
    (h : ∀ e, F e ≤ G e) (d : Multiset View) : sgnM parameter data s excl m F d ≤ sgnM parameter data s excl m G d :=
  sgn_le_of_le _ _ h d

theorem sgnM_congr (s : State) (excl : Pair → Prop) (m : Message) {F G : Multiset View → ℝ≥0∞}
    (h : ∀ e, F e = G e) (d : Multiset View) : sgnM parameter data s excl m F d = sgnM parameter data s excl m G d :=
  sgn_congr _ _ h d

/-- The law of the signed view of a message sees the state only through the digest blocks of the
message. -/
theorem sgnM_blocksOn {s s' : State} (excl : Pair → Prop) {m : Message}
    (h : ∀ ρ, s'.cache (blk parameter data m ρ) = s.cache (blk parameter data m ρ)) (F : Multiset View → ℝ≥0∞)
    (d : Multiset View) : sgnM parameter data s' excl m F d = sgnM parameter data s excl m F d := by
  have hst : stOf parameter data m s' = stOf parameter data m s := by
    funext ρ
    simp only [stOf]
    rw [h ρ]
  have hext : extOf parameter data s' excl m = extOf parameter data s excl m := by
    funext ρ
    unfold extOf pview
    rw [show s'.cache (pblk parameter data (m, ρ)) = s.cache (pblk parameter data (m, ρ)) from h ρ]
  unfold sgnM
  rw [hst, hext]

/-- The groups of a list commute with the law of the signed view of any message in any state. -/
theorem grpAll_sgn_comm (s : State) (excl : Pair → Prop) (st : Randomness → St) (ext : Randomness → Multiset View)
    (F : Multiset View → ℝ≥0∞) :
    ∀ (Ms : List Message) (d : Multiset View),
      grpAll parameter data s excl Ms (sgn nextRand landing digestAttemptLimit Finset.univ st ext F) d =
        sgn nextRand landing digestAttemptLimit Finset.univ st ext (grpAll parameter data s excl Ms F) d
  | [], _ => rfl
  | m :: Ms, d => by
      simp only [grpAll, grpM]
      rw [grp_congr _ _ (fun e => grpAll_sgn_comm s excl st ext F Ms e) d]
      exact grp_sgn_comm nextRand digestAttemptLimit st ext _ _ _ d

theorem innerH_mono {f : Multiset View → ℝ≥0∞} (hf : Monotone' f) (s : State) (excl : Pair → Prop)
    (hv : Option Message) (n : ℕ) (I : List View) : Monotone' (innerH parameter data w s excl hv f n I) := by
  cases hv with
  | none => exact virtualOnce_mono hf (n + 1) I
  | some h => exact sgnM_mono s excl h (virtualOnce_mono hf n I)

theorem innerH_ne_top (hw : w ≤ 1) {f : Multiset View → ℝ≥0∞} (hfin : ∀ D, f D ≠ ⊤) (s : State) (excl : Pair → Prop)
    (hv : Option Message) (n : ℕ) (I : List View) (e : Multiset View) :
    innerH parameter data w s excl hv f n I e ≠ ⊤ := by
  cases hv with
  | none => exact virtualOnce_ne_top Finset.univ_nonempty hw hfin (n + 1) I e
  | some h => exact sgnM_ne_top s excl h (virtualOnce_ne_top Finset.univ_nonempty hw hfin n I) e

/-- One more future pair is one coin on the inner function. -/
theorem innerH_coin (s : State) (excl : Pair → Prop) (hv : Option Message) (f : Multiset View → ℝ≥0∞) (n : ℕ)
    (v : View) (I : List View) (e : Multiset View) :
    innerH parameter data w s excl hv f n (v :: I) e =
      w * innerH parameter data w s excl hv f n I (e + {v}) + (1 - w) * innerH parameter data w s excl hv f n I e := by
  cases hv with
  | none => rfl
  | some h =>
      have hcoin : ∀ e, virtualOnce Finset.univ w f n (v :: I) e =
          w * virtualOnce Finset.univ w f n I (e + {v}) + (1 - w) * virtualOnce Finset.univ w f n I e := fun _ => rfl
      simp only [innerH_some]
      unfold sgnM
      rw [sgn_congr _ _ hcoin e, sgn_coin]

/-- One more signature left is one fresh slot inside the inner function. -/
theorem innerH_succ (s : State) (excl : Pair → Prop) (hv : Option Message) (f : Multiset View → ℝ≥0∞) (n : ℕ)
    (J : List View) (e : Multiset View) :
    innerH parameter data w s excl hv f (n + 1) J e =
      freshAvg Finset.univ fun v => innerH parameter data w s excl hv f n J (e + {v}) := by
  cases hv with
  | none => exact virtualOnce_succ_nil J e
  | some h =>
      simp only [innerH_some]
      unfold sgnM
      rw [sgn_congr _ _ (virtualOnce_succ_nil J) e, sgn_freshAvg]
      exact congrArg (freshAvg Finset.univ) (funext fun v => sgn_shift _ _ _ {v} e)

theorem innerH_le_cons (hw : w ≤ 1) {f : Multiset View → ℝ≥0∞} (hf : Monotone' f) (s : State) (excl : Pair → Prop)
    (hv : Option Message) (n : ℕ) (I : List View) (v : View) (e : Multiset View) :
    innerH parameter data w s excl hv f n I e ≤ innerH parameter data w s excl hv f n (v :: I) e := by
  cases hv with
  | none => exact virtualOnce_le_consM hw hf (n + 1) I v e
  | some h => exact sgnM_le_of_le s excl h (fun e => virtualOnce_le_consM hw hf n I v e) e

theorem innerH_perm (s : State) (excl : Pair → Prop) (hv : Option Message) (f : Multiset View → ℝ≥0∞) (n : ℕ)
    {I I' : List View} (h : I.Perm I') (e : Multiset View) :
    innerH parameter data w s excl hv f n I e = innerH parameter data w s excl hv f n I' e := by
  cases hv with
  | none => exact virtualOnce_perm (n + 1) h e
  | some m => exact sgnM_congr s excl m (fun e => virtualOnce_perm n h e) e

theorem base_le_innerH (hw : w ≤ 1) {f : Multiset View → ℝ≥0∞} (hf : Monotone' f) (s : State) (excl : Pair → Prop)
    (hv : Option Message) (n : ℕ) (I : List View) (e : Multiset View) :
    f e ≤ innerH parameter data w s excl hv f n I e := by
  cases hv with
  | none => exact base_le_virtualOnceM Finset.univ_nonempty hw hf (n + 1) I e
  | some h =>
      exact (base_le_virtualOnceM Finset.univ_nonempty hw hf n I e).trans
        (le_sgn landing_le_one Finset.univ_nonempty _ _ (virtualOnce_mono hf n I) e)

/-- The witnesses of a fresh view against the baseline and the excess, on the one-coin future. -/
theorem virtualOnce_forecast (hw : w ≤ 1) (b0 : ℝ≥0∞) (n : ℕ) (J : List View) (e : Multiset View) :
    landing * freshAvg Finset.univ (fun v => virtualOnce Finset.univ w (witnessFn v) n J e) ≤
      b0 + virtualOnce Finset.univ w (excess b0) n J e := by
  have hU : (Finset.univ : Finset View).Nonempty := Finset.univ_nonempty
  rw [← virtualOnce_freshAvg hU, ← virtualOnce_const_mul]
  calc virtualOnce Finset.univ w (fun D => landing * freshAvg Finset.univ fun v => witnessFn v D) n J e
      ≤ virtualOnce Finset.univ w (fun D => b0 + excess b0 D) n J e :=
        virtualOnce_mono_base (fun D => show price D ≤ b0 + (price D - b0) from le_add_tsub) n J e
    _ = b0 + virtualOnce Finset.univ w (excess b0) n J e := by
        rw [virtualOnce_add hU (fun _ => b0) (excess b0), virtualOnce_const hU hw]

theorem innerH_forecast (hw : w ≤ 1) (b0 : ℝ≥0∞) (s : State) (excl : Pair → Prop) (hv : Option Message) (n : ℕ)
    (J : List View) (e : Multiset View) :
    landing * freshAvg Finset.univ (fun v => innerH parameter data w s excl hv (witnessFn v) n J e) ≤
      b0 + innerH parameter data w s excl hv (excess b0) n J e := by
  cases hv with
  | none => exact virtualOnce_forecast hw b0 (n + 1) J e
  | some h =>
      simp only [innerH_some]
      unfold sgnM
      calc landing * freshAvg Finset.univ (fun v => sgn nextRand landing digestAttemptLimit Finset.univ
              (stOf parameter data h s) (extOf parameter data s excl h) (virtualOnce Finset.univ w (witnessFn v) n J) e)
          = sgn nextRand landing digestAttemptLimit Finset.univ (stOf parameter data h s) (extOf parameter data s excl h)
              (fun e' => landing * freshAvg Finset.univ fun v => virtualOnce Finset.univ w (witnessFn v) n J e') e := by
            rw [sgn_const_mul, sgn_freshAvg]
        _ ≤ sgn nextRand landing digestAttemptLimit Finset.univ (stOf parameter data h s) (extOf parameter data s excl h)
              (fun e' => b0 + virtualOnce Finset.univ w (excess b0) n J e') e :=
            sgn_le_of_le _ _ (fun e' => virtualOnce_forecast hw b0 n J e') e
        _ = _ := by
            rw [sgn_add _ _ (fun _ => b0), sgn_const landing_le_one Finset.univ_nonempty]

theorem extOf_excl_mono (s : State) {excl excl' : Pair → Prop} (h : ∀ q, excl q → excl' q) (m : Message)
    (ρ : Randomness) : extOf parameter data s excl' m ρ ≤ extOf parameter data s excl m ρ := by
  unfold extOf
  by_cases hx : excl (m, ρ)
  · rw [ite_eq_left hx, ite_eq_left (h _ hx)]
  · rw [ite_eq_right hx]
    split_ifs
    · exact bot_le
    · exact le_rfl

/-- Excluding more pairs lowers the inner function. -/
theorem innerH_excl_mono {f : Multiset View → ℝ≥0∞} (hf : Monotone' f) (s : State) {excl excl' : Pair → Prop}
    (h : ∀ q, excl q → excl' q) (hv : Option Message) (n : ℕ) (I : List View) (e : Multiset View) :
    innerH parameter data w s excl' hv f n I e ≤ innerH parameter data w s excl hv f n I e := by
  cases hv with
  | none => exact le_rfl
  | some m => exact sgn_ext_mono _ (fun ρ => extOf_excl_mono s h m ρ) (virtualOnce_mono hf n I) e

/-- The inner function sees the state only through the digest blocks of the heavy message. -/
theorem innerH_blocksOn {s s' : State} (excl : Pair → Prop) {hv : Option Message}
    (hb : ∀ h, hv = some h → ∀ ρ, s'.cache (blk parameter data h ρ) = s.cache (blk parameter data h ρ))
    (f : Multiset View → ℝ≥0∞) (n : ℕ) (I : List View) (e : Multiset View) :
    innerH parameter data w s' excl hv f n I e = innerH parameter data w s excl hv f n I e := by
  cases hv with
  | none => rfl
  | some h => exact sgnM_blocksOn excl (hb h rfl) _ e

end InnerH

/-! ### Order, congruence and start value of a term -/

section TermBasicH

variable {parameter : PublicParameter} {data : PublicData} {Qtot : ℕ} {w : ℝ≥0∞}

theorem valH_mono {f : Multiset View → ℝ≥0∞} (hf : Monotone' f) (s : State) (excl : Pair → Prop)
    (Ls : List Message) (hv : Option Message) (n : ℕ) (I : List View) :
    Monotone' (valH parameter data w s excl Ls hv f n I) :=
  grpAll_mono s excl (innerH_mono hf s excl hv n I) Ls

theorem valH_ne_top (hw : w ≤ 1) {f : Multiset View → ℝ≥0∞} (hfin : ∀ D, f D ≠ ⊤) (s : State) (excl : Pair → Prop)
    (Ls : List Message) (hv : Option Message) (n : ℕ) (I : List View) (e : Multiset View) :
    valH parameter data w s excl Ls hv f n I e ≠ ⊤ :=
  grpAll_ne_top s excl (innerH_ne_top hw hfin s excl hv n I) Ls e

/-- The value does not depend on the order of the light messages. -/
theorem valH_perm_msgs (s : State) (excl : Pair → Prop) {Ls Ls' : List Message} (h : Ls.Perm Ls')
    (hv : Option Message) (f : Multiset View → ℝ≥0∞) (n : ℕ) (I : List View) (e : Multiset View) :
    valH parameter data w s excl Ls hv f n I e = valH parameter data w s excl Ls' hv f n I e :=
  grpAll_perm s excl _ h e

/-- The value sees the state only through the digest blocks of its messages. -/
theorem valH_blocksOn {s s' : State} (excl : Pair → Prop) {Ls : List Message} {hv : Option Message}
    (hL : ∀ m ∈ Ls, ∀ ρ, s'.cache (blk parameter data m ρ) = s.cache (blk parameter data m ρ))
    (hb : ∀ h, hv = some h → ∀ ρ, s'.cache (blk parameter data h ρ) = s.cache (blk parameter data h ρ))
    (f : Multiset View → ℝ≥0∞) (n : ℕ) (I : List View) (e : Multiset View) :
    valH parameter data w s' excl Ls hv f n I e = valH parameter data w s excl Ls hv f n I e := by
  unfold valH
  rw [grpAll_blocksOn excl _ Ls hL e]
  exact grpAll_congr s excl (fun e' => innerH_blocksOn excl hb f n I e') Ls e

theorem baseH_cons (hw : w ≤ 1) {f : Multiset View → ℝ≥0∞} (hf : MonoFin f) (s : State) (Ms : List Message)
    (L : QueryLog SigningSpec) (excl : Pair → Prop) (d : Multiset View) (n : ℕ) (v : View) (I : List View) :
    baseH parameter data Qtot w s Ms L excl f d n I ≤ baseH parameter data Qtot w s Ms L excl f d n (v :: I) :=
  grpAll_le_of_le s excl (fun e => innerH_le_cons hw hf.1 s excl _ n I v e) _ d

theorem baseH_perm {f : Multiset View → ℝ≥0∞} (s : State) (Ms : List Message)
    (L : QueryLog SigningSpec) (excl : Pair → Prop) (d : Multiset View) (n : ℕ) (I I' : List View) (h : I.Perm I') :
    baseH parameter data Qtot w s Ms L excl f d n I = baseH parameter data Qtot w s Ms L excl f d n I' :=
  grpAll_congr s excl (fun e => innerH_perm s excl _ f n h e) _ d

/-- More future pairs, a larger forecast. -/
theorem termH_mono (hw : w ≤ 1) {f : Multiset View → ℝ≥0∞} (hf : MonoFin f) (s : State) (Ms : List Message)
    (L : QueryLog SigningSpec) (excl : Pair → Prop) (d : Multiset View) (n : ℕ) {k k' : ℕ} (hk : k ≤ k') :
    termH parameter data Qtot w s Ms L excl f d n k ≤ termH parameter data Qtot w s Ms L excl f d n k' :=
  creations_mono_count Finset.univ_nonempty landing_le_one (baseH_cons hw hf s Ms L excl d n)
    (baseH_perm s Ms L excl d n) hk []

/-- The base of a term is below its forecast. -/
theorem baseH_le_termH (hw : w ≤ 1) {f : Multiset View → ℝ≥0∞} (hf : MonoFin f) (s : State) (Ms : List Message)
    (L : QueryLog SigningSpec) (excl : Pair → Prop) (d : Multiset View) (n k : ℕ) :
    baseH parameter data Qtot w s Ms L excl f d n [] ≤ termH parameter data Qtot w s Ms L excl f d n k :=
  termH_mono hw hf s Ms L excl d n (Nat.zero_le k)

/-- The base value is below its forecast. -/
theorem base_le_termH (hw : w ≤ 1) {f : Multiset View → ℝ≥0∞} (hf : MonoFin f) (s : State) (Ms : List Message)
    (L : QueryLog SigningSpec) (excl : Pair → Prop) (d : Multiset View) (n k : ℕ) :
    f d ≤ termH parameter data Qtot w s Ms L excl f d n k := by
  calc f d ≤ innerH parameter data w s excl (heavyMsg parameter data Qtot s (live L Ms)) f n [] d :=
        base_le_innerH hw hf.1 s excl _ n [] d
    _ ≤ baseH parameter data Qtot w s Ms L excl f d n [] := le_grpAll s excl (innerH_mono hf.1 s excl _ n []) _ d
    _ ≤ _ := baseH_le_termH hw hf s Ms L excl d n k

/-- Excluding more pairs lowers the forecast. -/
theorem termH_excl_mono {f : Multiset View → ℝ≥0∞} (hf : MonoFin f) (s : State) (Ms : List Message)
    (L : QueryLog SigningSpec) {excl excl' : Pair → Prop} (h : ∀ q, excl q → excl' q) (d : Multiset View) (n k : ℕ) :
    termH parameter data Qtot w s Ms L excl' f d n k ≤ termH parameter data Qtot w s Ms L excl f d n k := by
  refine creations_mono (fun I => ?_) k []
  unfold baseH valH
  exact le_trans (grpAll_le_of_le s excl' (fun e => innerH_excl_mono hf.1 s h _ n I e) _ d)
    (grpAll_excl_mono s h (innerH_mono hf.1 s excl _ n I) _ d)

/-- A new candidate's forecast is at most the baseline plus one excess. -/
theorem fresh_forecastH (hw : w ≤ 1) (b0 : ℝ≥0∞) (s : State) (Ms : List Message) (L : QueryLog SigningSpec)
    (excl : Pair → Prop) (d : Multiset View) (n k : ℕ) :
    landing * freshAvg Finset.univ (fun v => termH parameter data Qtot w s Ms L excl (witnessFn v) d n k) ≤
      b0 + termH parameter data Qtot w s Ms L excl (excess b0) d n k := by
  unfold termH
  rw [← creations_freshAvg, ← creations_const_mul]
  have hpt : ∀ J, landing * freshAvg Finset.univ (fun v => baseH parameter data Qtot w s Ms L excl (witnessFn v) d n J) ≤
      b0 + baseH parameter data Qtot w s Ms L excl (excess b0) d n J := by
    intro J
    unfold baseH valH
    rw [← grpAll_freshAvg, ← grpAll_const_mul]
    refine le_trans (grpAll_le_of_le s excl (fun e => innerH_forecast hw b0 s excl _ n J e) _ d) (le_of_eq ?_)
    rw [grpAll_add s excl (fun _ => b0), grpAll_const]
  calc creations Finset.univ landing (fun J => landing * freshAvg Finset.univ fun v =>
        baseH parameter data Qtot w s Ms L excl (witnessFn v) d n J) k []
      ≤ creations Finset.univ landing (fun J => b0 + baseH parameter data Qtot w s Ms L excl (excess b0) d n J) k [] :=
        creations_mono hpt k []
    _ = _ := by rw [creations_add (fun _ => b0), creations_const Finset.univ_nonempty landing_le_one]

/-- The forecast sees the state only through the digest blocks. -/
theorem termH_blocks {s s' : State} (h : ∀ q, s'.cache (pblk parameter data q) = s.cache (pblk parameter data q))
    (Ms : List Message) (L : QueryLog SigningSpec) (excl : Pair → Prop) (f : Multiset View → ℝ≥0∞) (d : Multiset View)
    (n k : ℕ) : termH parameter data Qtot w s' Ms L excl f d n k = termH parameter data Qtot w s Ms L excl f d n k := by
  have hb : ∀ m ρ, s'.cache (blk parameter data m ρ) = s.cache (blk parameter data m ρ) := fun m ρ => h (m, ρ)
  have hheavy : ∀ m ∈ live L Ms, (Heavy parameter data Qtot s' m ↔ Heavy parameter data Qtot s m) :=
    fun m _ => heavy_congr (hb m)
  unfold termH
  congr 1
  funext I
  unfold baseH
  rw [lightMsgs_congr hheavy, heavyMsg_congr hheavy]
  exact valH_blocksOn excl (fun m _ => hb m) (fun m _ => hb m) f n I d

/-- **The start value.** With no listed message a term is the one-coin future with its spare slot. -/
theorem termH_nil (s : State) (L : QueryLog SigningSpec) (excl : Pair → Prop) (f : Multiset View → ℝ≥0∞)
    (d : Multiset View) (n k : ℕ) :
    termH parameter data Qtot w s [] L excl f d n k =
      creations Finset.univ landing (fun I => virtualOnce Finset.univ w f (n + 1) I d) k [] := rfl

/-- Listing one more message does not change a term: it has no cached digest yet. -/
theorem termH_addMsg {s : State} {Ms : List Message} (hM : MInv parameter data s Ms) (L : QueryLog SigningSpec)
    (excl : Pair → Prop) (m : Message) (f : Multiset View → ℝ≥0∞) (d : Multiset View) (n k : ℕ) :
    termH parameter data Qtot w s (addMsg Ms m) L excl f d n k = termH parameter data Qtot w s Ms L excl f d n k := by
  unfold addMsg
  split_ifs with hm
  · rfl
  · have hun : ∀ ρ, s.cache (blk parameter data m ρ) = none := by
      intro ρ
      by_contra h
      exact hm (hM.mem m ρ h)
    have hnh : ¬Heavy parameter data Qtot s m := by
      unfold Heavy cachedCount
      simp [hun]
    unfold termH
    congr 1
    funext I
    unfold baseH live
    rw [List.filter_cons]
    split_ifs with hlive
    · unfold lightMsgs heavyMsg
      rw [List.filter_cons, ite_eq_left (by simpa using hnh), List.find?_cons_of_neg (by simpa using hnh)]
      exact grpM_untouched s excl m hun _ d
    · rfl

end TermBasicH

/-! ### A new pair, one term -/

section NewPairH

variable {parameter : PublicParameter} {data : PublicData} {Qtot : ℕ} {w : ℝ≥0∞}

omit [Params] in
theorem cachedCount_withPair_self (s : State) (p : Pair) (hp0 : s.cache (pblk parameter data p) = none)
    (u0 : HashOutput) :
    cachedCount parameter data p.1 (withPair parameter data s p u0) = cachedCount parameter data p.1 s + 1 := by
  unfold cachedCount
  have hset : (Finset.univ.filter fun ρ : Randomness =>
      (withPair parameter data s p u0).cache (blk parameter data p.1 ρ) ≠ none) =
      insert p.2 (Finset.univ.filter fun ρ : Randomness => s.cache (blk parameter data p.1 ρ) ≠ none) := by
    ext ρ
    rw [Finset.mem_insert, Finset.mem_filter, Finset.mem_filter]
    by_cases hρ : ρ = p.2
    · subst hρ
      have h1 : (withPair parameter data s p u0).cache (blk parameter data p.1 p.2) = some u0 := withPair_self s p u0
      simp [h1]
    · have h1 : (withPair parameter data s p u0).cache (blk parameter data p.1 ρ) =
          s.cache (blk parameter data p.1 ρ) :=
        withPair_other_pair s p (p.1, ρ) (fun h => hρ (congrArg Prod.snd h)) u0
      simp [h1, hρ]
  rw [hset, Finset.card_insert_of_notMem]
  rw [Finset.mem_filter]
  have h0 : s.cache (blk parameter data p.1 p.2) = none := hp0
  simp [h0]

omit [Params] in
theorem heavy_withPair_self {s : State} {p : Pair} (hp0 : s.cache (pblk parameter data p) = none) (u0 : HashOutput) :
    Heavy parameter data Qtot (withPair parameter data s p u0) p.1 ↔ Qtot < 2 * (cachedCount parameter data p.1 s + 1) := by
  unfold Heavy
  rw [cachedCount_withPair_self s p hp0 u0]

/-- **One digest query, one term**, for any inner family that is monotone, finite and takes one more
future pair as one coin (`grpAll_probe` is the case of the one-coin future). -/
theorem grpAll_probeG (hw : w ≤ 1) (s : State) (p : Pair) (hp0 : s.cache (pblk parameter data p) = none)
    (excl : Pair → Prop) (Ms : List Message) (hMs : Ms.Nodup) (hp : p.1 ∈ Ms) (hrate : Rate parameter data w s p.1)
    (G : List View → Multiset View → ℝ≥0∞) (hG : ∀ I, Monotone' (G I)) (hGfin : ∀ I e, G I e ≠ ⊤)
    (hcoin : ∀ v I e, G (v :: I) e = w * G I (e + {v}) + (1 - w) * G I e) (I : List View) (d : Multiset View) :
    pairE (fun u0 => grpAll parameter data (withPair parameter data s p u0) excl Ms (G I) d) ≤
      (1 - landing) * grpAll parameter data s excl Ms (G I) d +
        landing * freshAvg Finset.univ (fun v => grpAll parameter data s excl Ms (G (v :: I)) d) := by
  set Ms' := Ms.erase p.1 with hMs'
  have hperm : Ms.Perm (p.1 :: Ms') := List.perm_cons_erase hp
  have hnot : p.1 ∉ Ms' := fun h => (List.Nodup.mem_erase_iff hMs).1 h |>.1 rfl
  set X : Multiset View → ℝ≥0∞ := grpAll parameter data s excl Ms' (G I) with hX
  have hXmono : Monotone' X := grpAll_mono s excl (hG I) Ms'
  have hXfin : ∀ e, X e ≠ ⊤ := grpAll_ne_top s excl (hGfin I) Ms'
  have hst : stOf parameter data p.1 s p.2 = .fresh := by
    have h : s.cache (blk parameter data p.1 p.2) = none := hp0
    simp [stOf, h]
  set Fh : View → ℝ≥0∞ := fun v => grp nextRand landing digestAttemptLimit Finset.univ
    (Function.update (stOf parameter data p.1 s) p.2 .hit)
    (Function.update (extOf parameter data s excl p.1) p.2 (if excl p then 0 else {v})) X d with hFh
  set Cm : ℝ≥0∞ := grp nextRand landing digestAttemptLimit Finset.univ
    (Function.update (stOf parameter data p.1 s) p.2 .miss) (extOf parameter data s excl p.1) X d with hCm
  have hleft : ∀ u0, grpAll parameter data (withPair parameter data s p u0) excl Ms (G I) d =
      if Landed parameter (blockIndex u0) then Fh (viewOf u0) else Cm := by
    intro u0
    rw [grpAll_perm _ excl _ hperm d]
    simp only [grpAll]
    rw [grpM_withPair_self,
      grp_congr _ _ (fun e => grpAll_withPair_other s p u0 excl (G I) Ms' hnot e) d]
    by_cases hl : Landed parameter (blockIndex u0)
    · simp only [hl, ite_true]
      rfl
    · simp only [hl, ite_false]
      exact grp_congr_ext _ (fun ρ hρ => by
        by_cases h : ρ = p.2
        · subst h; rw [Function.update_self] at hρ; cases hρ
        · rw [Function.update_of_ne h]) X d
  rw [show (fun u0 => grpAll parameter data (withPair parameter data s p u0) excl Ms (G I) d) =
      fun u0 => if Landed parameter (blockIndex u0) then Fh (viewOf u0) else Cm
      from funext hleft, pairE_landed parameter Fh Cm]
  have hstep := probe_step (σ := nextRand) (p := landing) (A := digestAttemptLimit) (U := (Finset.univ : Finset View))
    landing_le_one Finset.univ_nonempty (stOf parameter data p.1 s) (extOf parameter data s excl p.1) hXmono hXfin d
    p.2 hst (fun j h0 hj => nextRand_pow_ne p.2 j h0 (lt_trans hj (by unfold digestAttemptLimit; norm_num))) w hw
    (fun v => if excl p then 0 else {v}) (fun v => by split_ifs <;> simp) hrate
  refine le_trans hstep (le_of_eq ?_)
  have hXv : ∀ (v : View) (e : Multiset View), grpAll parameter data s excl Ms' (G (v :: I)) e =
      w * X (e + {v}) + (1 - w) * X e := by
    intro v e
    rw [grpAll_congr s excl (hcoin v I) Ms' e,
      grpAll_add s excl (fun e => w * G I (e + {v})), grpAll_const_mul, grpAll_const_mul,
      grpAll_shift]
  have hR1 : grpAll parameter data s excl Ms (G I) d = grpM parameter data s excl p.1 X d := by
    rw [grpAll_perm _ excl _ hperm d]; rfl
  have hR2 : ∀ v, grpAll parameter data s excl Ms (G (v :: I)) d =
      grpM parameter data s excl p.1 (fun e => w * X (e + {v}) + (1 - w) * X e) d := by
    intro v
    rw [grpAll_perm _ excl _ hperm d]
    simp only [grpAll]
    exact grp_congr _ _ (hXv v) d
  rw [hR1, show (fun v => grpAll parameter data s excl Ms (G (v :: I)) d) = _ from funext hR2]
  unfold grpM
  rw [grp_add _ _ (fun e => (1 - landing) * X e), grp_const_mul, grp_const_mul, grp_freshAvg]

theorem sgnM_withPair_other (s : State) (p : Pair) (u0 : HashOutput) (excl : Pair → Prop) {m : Message}
    (hm : m ≠ p.1) (F : Multiset View → ℝ≥0∞) (d : Multiset View) :
    sgnM parameter data (withPair parameter data s p u0) excl m F d = sgnM parameter data s excl m F d :=
  sgnM_blocksOn excl (fun ρ => withPair_other_pair s p (m, ρ) (fun h => hm (congrArg Prod.fst h)) u0) F d

theorem sgnM_withPair_self (s : State) (p : Pair) (u0 : HashOutput) (excl : Pair → Prop)
    (F : Multiset View → ℝ≥0∞) (d : Multiset View) :
    sgnM parameter data (withPair parameter data s p u0) excl p.1 F d =
      sgn nextRand landing digestAttemptLimit Finset.univ
        (Function.update (stOf parameter data p.1 s) p.2 (if Landed parameter (blockIndex u0) then .hit else .miss))
        (Function.update (extOf parameter data s excl p.1) p.2 (if excl p then 0 else {viewOf u0})) F d := by
  have hext : extOf parameter data (withPair parameter data s p u0) excl p.1 =
      Function.update (extOf parameter data s excl p.1) p.2 (if excl p then 0 else {viewOf u0}) := by
    funext ρ
    by_cases hρ : ρ = p.2
    · subst hρ
      rw [Function.update_self]
      unfold extOf
      rw [show ((p.1, p.2) : Pair) = p from rfl, pview_withPair_self]
    · rw [Function.update_of_ne hρ]
      exact extOf_withPair_other s p u0 excl fun h => hρ (congrArg Prod.snd h)
  unfold sgnM
  rw [stOf_withPair_self, hext]

/-- **A digest query of the heavy message keeps the law of its signed view in the mean** (no rate). -/
theorem sgnM_probe (s : State) (p : Pair) (hp0 : s.cache (pblk parameter data p) = none) (excl : Pair → Prop)
    {X : Multiset View → ℝ≥0∞} (hX : Monotone' X) (hXfin : ∀ e, X e ≠ ⊤) (d : Multiset View) :
    pairE (fun u0 => sgnM parameter data (withPair parameter data s p u0) excl p.1 X d) ≤
      sgnM parameter data s excl p.1 X d := by
  have hst : stOf parameter data p.1 s p.2 = .fresh := by
    have h : s.cache (blk parameter data p.1 p.2) = none := hp0
    simp [stOf, h]
  set Fh : View → ℝ≥0∞ := fun v => sgn nextRand landing digestAttemptLimit Finset.univ
    (Function.update (stOf parameter data p.1 s) p.2 .hit)
    (Function.update (extOf parameter data s excl p.1) p.2 (if excl p then 0 else {v})) X d with hFh
  set Cm : ℝ≥0∞ := sgn nextRand landing digestAttemptLimit Finset.univ
    (Function.update (stOf parameter data p.1 s) p.2 .miss) (extOf parameter data s excl p.1) X d with hCm
  have hleft : ∀ u0, sgnM parameter data (withPair parameter data s p u0) excl p.1 X d =
      if Landed parameter (blockIndex u0) then Fh (viewOf u0) else Cm := by
    intro u0
    rw [sgnM_withPair_self]
    by_cases hl : Landed parameter (blockIndex u0)
    · simp only [hl, ite_true]
      rfl
    · simp only [hl, ite_false]
      exact sgn_congr_ext _ (fun ρ hρ => by
        by_cases h : ρ = p.2
        · subst h; rw [Function.update_self] at hρ; cases hρ
        · rw [Function.update_of_ne h]) X d
  rw [show (fun u0 => sgnM parameter data (withPair parameter data s p u0) excl p.1 X d) =
      fun u0 => if Landed parameter (blockIndex u0) then Fh (viewOf u0) else Cm
      from funext hleft, pairE_landed parameter Fh Cm]
  exact sgn_probe (σ := nextRand) (p := landing) (A := digestAttemptLimit) (U := (Finset.univ : Finset View))
    landing_le_one Finset.univ_nonempty (stOf parameter data p.1 s) (extOf parameter data s excl p.1) hX hXfin d
    p.2 hst (fun j h0 hj => nextRand_pow_ne p.2 j h0 (lt_trans hj (by unfold digestAttemptLimit; norm_num)))
    (fun v => if excl p then 0 else {v}) (fun v => by split_ifs <;> simp)

/-- **The new candidate, heavy message.** A new landed pair that is excluded stops the walks of its
message without disclosing anything. -/
theorem sgnM_stop (s : State) (p : Pair) (excl : Pair → Prop) (hx : excl p) (u0 : HashOutput)
    (hl : Landed parameter (blockIndex u0)) {X : Multiset View → ℝ≥0∞} (hX : Monotone' X) (d : Multiset View) :
    sgnM parameter data (withPair parameter data s p u0) excl p.1 X d ≤ sgnM parameter data s excl p.1 X d := by
  rw [sgnM_withPair_self, ite_eq_left hl, ite_eq_left hx]
  exact sgn_stop_le landing_le_one Finset.univ_nonempty _ _ hX d p.2

/-- The value with a heavy message: the law of its signed view outside the groups. -/
theorem valH_heavy_eq (s : State) (excl : Pair → Prop) (rest : List Message) (h : Message)
    (f : Multiset View → ℝ≥0∞) (n : ℕ) (I : List View) (d : Multiset View) :
    valH parameter data w s excl rest (some h) f n I d =
      sgnM parameter data s excl h (grpAll parameter data s excl rest (virtualOnce Finset.univ w f n I)) d := by
  show grpAll parameter data s excl rest (sgnM parameter data s excl h (virtualOnce Finset.univ w f n I)) d = _
  unfold sgnM
  exact grpAll_sgn_comm s excl _ _ _ rest d

theorem valH_heavy_withPair (s : State) (p : Pair) (u0 : HashOutput) (excl : Pair → Prop) {rest : List Message}
    (hnot : p.1 ∉ rest) (f : Multiset View → ℝ≥0∞) (n : ℕ) (I : List View) (d : Multiset View) :
    valH parameter data w (withPair parameter data s p u0) excl rest (some p.1) f n I d =
      sgnM parameter data (withPair parameter data s p u0) excl p.1
        (grpAll parameter data s excl rest (virtualOnce Finset.univ w f n I)) d := by
  rw [valH_heavy_eq]
  exact sgnM_congr _ excl p.1 (fun e => grpAll_withPair_other s p u0 excl _ rest hnot e) d

/-- **The law of the signed view consumes the spare slot**: a message treated by `sgn` over the
one-coin future is below the same message treated as a group over the future with its spare slot. -/
theorem sgnM_le_spare {f : Multiset View → ℝ≥0∞} (hf : Monotone' f) (s : State) (excl : Pair → Prop)
    (m : Message) (rest : List Message) (n : ℕ) (I : List View) (d : Multiset View) :
    sgnM parameter data s excl m (grpAll parameter data s excl rest (virtualOnce Finset.univ w f n I)) d ≤
      valH parameter data w s excl (m :: rest) none f n I d := by
  have hX : Monotone' (grpAll parameter data s excl rest (virtualOnce Finset.univ w f n I)) :=
    grpAll_mono s excl (virtualOnce_mono hf n I) rest
  refine le_trans (sgn_le_grp Finset.univ_nonempty _ _ hX d) (le_of_eq ?_)
  show _ = grpM parameter data s excl m (grpAll parameter data s excl rest (virtualOnce Finset.univ w f (n + 1) I)) d
  unfold grpM
  refine grp_congr _ _ (fun e => ?_) d
  symm
  rw [grpAll_congr s excl (virtualOnce_succ_nil I) rest e, grpAll_freshAvg]
  exact congrArg (freshAvg Finset.univ) (funext fun v => grpAll_shift s excl _ {v} rest e)

theorem mix_ge {B : ℝ≥0∞} {C : View → ℝ≥0∞} (h : ∀ v, B ≤ C v) :
    B ≤ (1 - landing) * B + landing * freshAvg Finset.univ C := by
  calc B = (1 - landing) * B + landing * B := by rw [← add_mul, tsub_add_cancel_of_le landing_le_one, one_mul]
    _ ≤ _ := by
        gcongr
        calc B = freshAvg Finset.univ (fun _ : View => B) := (freshAvg_const _ Finset.univ_nonempty _).symm
          _ ≤ _ := freshAvg_mono _ fun v _ => h v

/-- **The cases of a new pair.** Either the light and heavy messages are the same before and after
(the message of the pair is light before and after, or not live), or the message of the pair is the
heavy one after: it was heavy before, or it was light and no live message was heavy. -/
theorem newPair_cases {s : State} {Ms : List Message} (hM : MInv parameter data s Ms) {budget : ℕ}
    (hT : TotalInv parameter data Qtot s budget) (hb : 1 ≤ budget) (p : Pair)
    (hp0 : s.cache (pblk parameter data p) = none) (L : QueryLog SigningSpec) (excl : Pair → Prop)
    (f : Multiset View → ℝ≥0∞) (d : Multiset View) (n : ℕ) :
    ((∀ u0 I, baseH parameter data Qtot w (withPair parameter data s p u0) (addMsg Ms p.1) L excl f d n I =
        valH parameter data w (withPair parameter data s p u0) excl
          (lightMsgs parameter data Qtot s (live L (addMsg Ms p.1)))
          (heavyMsg parameter data Qtot s (live L (addMsg Ms p.1))) f n I d) ∧
      heavyMsg parameter data Qtot s (live L (addMsg Ms p.1)) ≠ some p.1 ∧
      (p.1 ∈ lightMsgs parameter data Qtot s (live L (addMsg Ms p.1)) ∨ p.1 ∉ live L (addMsg Ms p.1))) ∨
    (∃ rest : List Message, p.1 ∉ rest ∧
      (∀ u0 I, baseH parameter data Qtot w (withPair parameter data s p u0) (addMsg Ms p.1) L excl f d n I =
        valH parameter data w (withPair parameter data s p u0) excl rest (some p.1) f n I d) ∧
      ((∀ I, valH parameter data w s excl rest (some p.1) f n I d =
          baseH parameter data Qtot w s (addMsg Ms p.1) L excl f d n I) ∨
        (∀ I, valH parameter data w s excl (p.1 :: rest) none f n I d =
          baseH parameter data Qtot w s (addMsg Ms p.1) L excl f d n I))) := by
  set Lv := live L (addMsg Ms p.1) with hLv
  have hnd : Lv.Nodup := live_nodup L (addMsg_nodup hM.nodup _)
  have hoth : ∀ u0 m, m ≠ p.1 → (Heavy parameter data Qtot (withPair parameter data s p u0) m ↔
      Heavy parameter data Qtot s m) := fun u0 m hm => heavy_withPair_other s p u0 hm
  have hself : ∀ u0, Heavy parameter data Qtot (withPair parameter data s p u0) p.1 ↔
      Qtot < 2 * (cachedCount parameter data p.1 s + 1) := fun u0 => heavy_withPair_self hp0 u0
  by_cases hmem : p.1 ∈ Lv
  swap
  · -- the message is not live
    left
    have hc : ∀ u0, ∀ m ∈ Lv, (Heavy parameter data Qtot (withPair parameter data s p u0) m ↔
        Heavy parameter data Qtot s m) := fun u0 m hm => hoth u0 m (fun h => hmem (h ▸ hm))
    refine ⟨fun u0 I => ?_, fun h => hmem (heavyMsg_some h).1, Or.inr hmem⟩
    unfold baseH
    rw [lightMsgs_congr (hc u0), heavyMsg_congr (hc u0)]
  by_cases hH : Heavy parameter data Qtot s p.1
  · -- heavy before and after
    right
    have hsome : heavyMsg parameter data Qtot s Lv = some p.1 := (heavyMsg_eq_some_iff hT).2 ⟨hmem, hH⟩
    have hA : Qtot < 2 * (cachedCount parameter data p.1 s + 1) := by unfold Heavy at hH; omega
    have hc : ∀ u0, ∀ m ∈ Lv, (Heavy parameter data Qtot (withPair parameter data s p u0) m ↔
        Heavy parameter data Qtot s m) := by
      intro u0 m hm
      by_cases hmp : m = p.1
      · rw [hmp]; exact ⟨fun _ => hH, fun _ => (hself u0).2 hA⟩
      · exact hoth u0 m hmp
    refine ⟨lightMsgs parameter data Qtot s Lv, fun h => (mem_lightMsgs.1 h).2 hH, fun u0 I => ?_, Or.inl fun I => ?_⟩
    · unfold baseH
      rw [lightMsgs_congr (hc u0), heavyMsg_congr (hc u0), hsome]
    · unfold baseH
      rw [hsome]
  by_cases hA : Qtot < 2 * (cachedCount parameter data p.1 s + 1)
  · -- light before, heavy after: no other live message is heavy
    right
    have hlight : ∀ m ∈ Lv, m ≠ p.1 → ¬Heavy parameter data Qtot s m := by
      intro m _ hne hm
      have := cachedCount_add_le (parameter := parameter) (data := data) hne s
      unfold Heavy at hm
      unfold TotalInv at hT
      omega
    have hnone : heavyMsg parameter data Qtot s Lv = none := by
      refine heavyMsg_eq_none.2 fun m hm => ?_
      by_cases hmp : m = p.1
      · rw [hmp]; exact hH
      · exact hlight m hm hmp
    have hsome : ∀ u0, heavyMsg parameter data Qtot (withPair parameter data s p u0) Lv = some p.1 := fun u0 =>
      heavyMsg_eq_some hmem ((hself u0).2 hA) fun m hm hm' => by
        by_contra hne
        exact hlight m hm hne ((hoth u0 m hne).1 hm')
    have hrest : ∀ u0, lightMsgs parameter data Qtot (withPair parameter data s p u0) Lv = Lv.erase p.1 := by
      intro u0
      rw [hnd.erase_eq_filter]
      unfold lightMsgs
      refine List.filter_congr fun m hm => ?_
      rw [Bool.eq_iff_iff]
      simp only [bne_iff_ne, ne_eq, decide_eq_true_eq]
      exact ⟨fun hnh heq => hnh (heq ▸ (hself u0).2 hA), fun hne hm' => hlight m hm hne ((hoth u0 m hne).1 hm')⟩
    refine ⟨Lv.erase p.1, fun h => (List.Nodup.mem_erase_iff hnd).1 h |>.1 rfl, fun u0 I => ?_, Or.inr fun I => ?_⟩
    · unfold baseH
      rw [hrest u0, hsome u0]
    · unfold baseH
      rw [hnone, lightMsgs_of_none hnone]
      exact valH_perm_msgs s excl (List.perm_cons_erase hmem).symm none f n I d
  · -- light before and after
    left
    have hc : ∀ u0, ∀ m ∈ Lv, (Heavy parameter data Qtot (withPair parameter data s p u0) m ↔
        Heavy parameter data Qtot s m) := by
      intro u0 m hm
      by_cases hmp : m = p.1
      · rw [hmp]; exact ⟨fun h => absurd ((hself u0).1 h) hA, fun h => absurd h hH⟩
      · exact hoth u0 m hmp
    refine ⟨fun u0 I => ?_, fun h => hH (heavyMsg_some h).2, Or.inl (mem_lightMsgs.2 ⟨hmem, hH⟩)⟩
    unfold baseH
    rw [lightMsgs_congr (hc u0), heavyMsg_congr (hc u0)]

/-- The heavy alternatives of `newPair_cases` are below the old base. -/
theorem heavy_alt_le {f : Multiset View → ℝ≥0∞} (hf : Monotone' f) (s : State) (excl : Pair → Prop) (m : Message)
    (rest : List Message) (n : ℕ) (d : Multiset View) {B : List View → ℝ≥0∞}
    (halt : (∀ I, valH parameter data w s excl rest (some m) f n I d = B I) ∨
      (∀ I, valH parameter data w s excl (m :: rest) none f n I d = B I)) (I : List View) :
    sgnM parameter data s excl m (grpAll parameter data s excl rest (virtualOnce Finset.univ w f n I)) d ≤ B I := by
  rcases halt with h | h
  · rw [← h I, valH_heavy_eq]
  · rw [← h I]
    exact sgnM_le_spare hf s excl m rest n I d

/-- **A new pair, the base of a term**, in the mean over its block. -/
theorem baseH_newPair (hw : w ≤ 1) {f : Multiset View → ℝ≥0∞} (hf : MonoFin f) {s : State} {Ms : List Message}
    (hM : MInv parameter data s Ms) {budget : ℕ} (hT : TotalInv parameter data Qtot s budget) (hb : 1 ≤ budget)
    (p : Pair) (hp0 : s.cache (pblk parameter data p) = none) (L : QueryLog SigningSpec) (excl : Pair → Prop)
    (hrate : MsgLive L p.1 → ¬Heavy parameter data Qtot s p.1 → Rate parameter data w s p.1)
    (d : Multiset View) (n : ℕ) (I : List View) :
    pairE (fun u0 => baseH parameter data Qtot w (withPair parameter data s p u0) (addMsg Ms p.1) L excl f d n I) ≤
      (1 - landing) * baseH parameter data Qtot w s (addMsg Ms p.1) L excl f d n I +
        landing * freshAvg Finset.univ (fun v => baseH parameter data Qtot w s (addMsg Ms p.1) L excl f d n (v :: I)) := by
  have hnd : (live L (addMsg Ms p.1)).Nodup := live_nodup L (addMsg_nodup hM.nodup _)
  have hmix : ∀ B : ℝ≥0∞, B ≤ baseH parameter data Qtot w s (addMsg Ms p.1) L excl f d n I →
      B ≤ (1 - landing) * baseH parameter data Qtot w s (addMsg Ms p.1) L excl f d n I +
        landing * freshAvg Finset.univ (fun v => baseH parameter data Qtot w s (addMsg Ms p.1) L excl f d n (v :: I)) :=
    fun B hB => le_trans hB (mix_ge fun v => baseH_cons hw hf s _ L excl d n v I)
  rcases newPair_cases (w := w) hM hT hb p hp0 L excl f d n with ⟨hsame, hne, hor⟩ | ⟨rest, hnot, hsame, halt⟩
  · have hbl : ∀ u0 h, heavyMsg parameter data Qtot s (live L (addMsg Ms p.1)) = some h →
        ∀ ρ, (withPair parameter data s p u0).cache (blk parameter data h ρ) = s.cache (blk parameter data h ρ) :=
      fun u0 h hh ρ => withPair_other_pair s p (h, ρ)
        (fun heq => hne (hh.trans (congrArg some (congrArg Prod.fst heq)))) u0
    rcases hor with hlight | hnotin
    · -- the message is light before and after: one coin pays
      obtain ⟨hmem, hnh⟩ := mem_lightMsgs.1 hlight
      have hlive : MsgLive L p.1 := (mem_live.1 hmem).2
      rw [show (fun u0 => baseH parameter data Qtot w (withPair parameter data s p u0) (addMsg Ms p.1) L excl f d n I) =
          fun u0 => grpAll parameter data (withPair parameter data s p u0) excl
            (lightMsgs parameter data Qtot s (live L (addMsg Ms p.1)))
            (innerH parameter data w s excl (heavyMsg parameter data Qtot s (live L (addMsg Ms p.1))) f n I) d
          from funext fun u0 => (hsame u0 I).trans
            (grpAll_congr _ excl (fun e => innerH_blocksOn excl (hbl u0) f n I e) _ d)]
      exact grpAll_probeG hw s p hp0 excl _ (lightMsgs_nodup hnd) hlight (hrate hlive hnh)
        (fun I => innerH parameter data w s excl (heavyMsg parameter data Qtot s (live L (addMsg Ms p.1))) f n I)
        (fun I => innerH_mono hf.1 s excl _ n I) (fun I e => innerH_ne_top hw hf.2 s excl _ n I e)
        (fun v I e => innerH_coin s excl _ f n v I e) I d
    · -- the message is not live: nothing changes
      have hpt : ∀ u0, baseH parameter data Qtot w (withPair parameter data s p u0) (addMsg Ms p.1) L excl f d n I =
          baseH parameter data Qtot w s (addMsg Ms p.1) L excl f d n I := fun u0 =>
        (hsame u0 I).trans (valH_blocksOn excl
          (fun m hm ρ => withPair_other_pair s p (m, ρ)
            (fun heq => by
              have h1 : m = p.1 := congrArg Prod.fst heq
              have hmm := (mem_lightMsgs.1 hm).1
              rw [h1] at hmm
              exact hnotin hmm) u0) (hbl u0) f n I d)
      simp only [hpt, pairE_const]
      exact hmix _ le_rfl
  · -- the message is the heavy one after: the law of its signed view keeps its mean
    have hX : Monotone' (grpAll parameter data s excl rest (virtualOnce Finset.univ w f n I)) :=
      grpAll_mono s excl (virtualOnce_mono hf.1 n I) rest
    have hXfin : ∀ e, grpAll parameter data s excl rest (virtualOnce Finset.univ w f n I) e ≠ ⊤ :=
      grpAll_ne_top s excl (virtualOnce_ne_top Finset.univ_nonempty hw hf.2 n I) rest
    rw [show (fun u0 => baseH parameter data Qtot w (withPair parameter data s p u0) (addMsg Ms p.1) L excl f d n I) =
        fun u0 => sgnM parameter data (withPair parameter data s p u0) excl p.1
          (grpAll parameter data s excl rest (virtualOnce Finset.univ w f n I)) d
        from funext fun u0 => (hsame u0 I).trans (valH_heavy_withPair s p u0 excl hnot f n I d)]
    exact hmix _ (le_trans (sgnM_probe s p hp0 excl hX hXfin d) (heavy_alt_le hf.1 s excl p.1 rest n d halt I))

/-- **A new pair, one term.** In the mean the forecast of a term after the block of a new pair is at
most its forecast with one more future pair. The rate is needed only for a live message that is not
heavy. -/
theorem termH_newPair (hw : w ≤ 1) {f : Multiset View → ℝ≥0∞} (hf : MonoFin f) {s : State} {Ms : List Message}
    (hM : MInv parameter data s Ms) {budget : ℕ} (hT : TotalInv parameter data Qtot s budget) (hb : 1 ≤ budget)
    (p : Pair) (hp0 : s.cache (pblk parameter data p) = none) (L : QueryLog SigningSpec) (excl : Pair → Prop)
    (hrate : MsgLive L p.1 → ¬Heavy parameter data Qtot s p.1 → Rate parameter data w s p.1)
    (d : Multiset View) (n k : ℕ) :
    pairE (fun u0 => termH parameter data Qtot w (withPair parameter data s p u0) (addMsg Ms p.1) L excl f d n k) ≤
      termH parameter data Qtot w s Ms L excl f d n (k + 1) := by
  rw [← termH_addMsg hM L excl p.1 f d n (k + 1)]
  unfold termH pairE
  rw [creations_tsum, ← creations_one]
  refine creations_mono (fun I => ?_) k []
  exact baseH_newPair hw hf hM hT hb p hp0 L excl hrate d n I

/-- **The new candidate.** A new landed pair that is excluded stops the walks of its message
without disclosing anything: its forecast in the new state is at most its forecast in the old one. -/
theorem termH_stop {f : Multiset View → ℝ≥0∞} (hf : MonoFin f) {s : State} {Ms : List Message}
    (hM : MInv parameter data s Ms) {budget : ℕ} (hT : TotalInv parameter data Qtot s budget) (hb : 1 ≤ budget)
    (p : Pair) (hp0 : s.cache (pblk parameter data p) = none)
    (L : QueryLog SigningSpec) (excl : Pair → Prop) (hx : excl p) (u0 : HashOutput)
    (hl : Landed parameter (blockIndex u0)) (d : Multiset View) (n k : ℕ) :
    termH parameter data Qtot w (withPair parameter data s p u0) (addMsg Ms p.1) L excl f d n k ≤
      termH parameter data Qtot w s Ms L excl f d n k := by
  rw [← termH_addMsg hM L excl p.1 f d n k]
  have hnd : (live L (addMsg Ms p.1)).Nodup := live_nodup L (addMsg_nodup hM.nodup _)
  refine creations_mono (fun I => ?_) k []
  rcases newPair_cases (w := w) hM hT hb p hp0 L excl f d n with ⟨hsame, hne, hor⟩ | ⟨rest, hnot, hsame, halt⟩
  · have hbl : ∀ h, heavyMsg parameter data Qtot s (live L (addMsg Ms p.1)) = some h →
        ∀ ρ, (withPair parameter data s p u0).cache (blk parameter data h ρ) = s.cache (blk parameter data h ρ) :=
      fun h hh ρ => withPair_other_pair s p (h, ρ)
        (fun heq => hne (hh.trans (congrArg some (congrArg Prod.fst heq)))) u0
    rcases hor with hlight | hnotin
    · set Ls := lightMsgs parameter data Qtot s (live L (addMsg Ms p.1)) with hLs
      set G := innerH parameter data w s excl (heavyMsg parameter data Qtot s (live L (addMsg Ms p.1))) f n I with hG
      have hGmono : Monotone' G := innerH_mono hf.1 s excl _ n I
      have hLnd : Ls.Nodup := lightMsgs_nodup hnd
      set rest := Ls.erase p.1 with hrest
      have hperm : Ls.Perm (p.1 :: rest) := List.perm_cons_erase hlight
      have hnot : p.1 ∉ rest := fun h => (List.Nodup.mem_erase_iff hLnd).1 h |>.1 rfl
      have hst : stOf parameter data p.1 s p.2 = .fresh := by
        have h : s.cache (blk parameter data p.1 p.2) = none := hp0
        simp [stOf, h]
      have h1 : baseH parameter data Qtot w (withPair parameter data s p u0) (addMsg Ms p.1) L excl f d n I =
          grpAll parameter data (withPair parameter data s p u0) excl Ls G d :=
        (hsame u0 I).trans (grpAll_congr _ excl (fun e => innerH_blocksOn excl hbl f n I e) _ d)
      have h2 : baseH parameter data Qtot w s (addMsg Ms p.1) L excl f d n I = grpAll parameter data s excl Ls G d := rfl
      rw [h1, h2, grpAll_perm _ excl _ hperm d, grpAll_perm _ excl _ hperm d]
      simp only [grpAll]
      rw [grpM_withPair_self, ite_eq_left hl, ite_eq_left hx,
        grp_congr _ _ (fun e => grpAll_withPair_other s p u0 excl G rest hnot e) d]
      exact grp_stop_le landing_le_one Finset.univ_nonempty _ _ (grpAll_mono s excl hGmono rest) d p.2 hst
    · exact le_of_eq ((hsame u0 I).trans (valH_blocksOn excl
        (fun m hm ρ => withPair_other_pair s p (m, ρ)
          (fun heq => by
              have h1 : m = p.1 := congrArg Prod.fst heq
              have hmm := (mem_lightMsgs.1 hm).1
              rw [h1] at hmm
              exact hnotin hmm) u0) hbl f n I d))
  · have hX : Monotone' (grpAll parameter data s excl rest (virtualOnce Finset.univ w f n I)) :=
      grpAll_mono s excl (virtualOnce_mono hf.1 n I) rest
    rw [hsame u0 I, valH_heavy_withPair s p u0 excl hnot f n I d]
    exact le_trans (sgnM_stop s p excl hx u0 hl hX d) (heavy_alt_le hf.1 s excl p.1 rest n d halt I)

end NewPairH

/-! ### Signing a message for the first time -/

section SignHeavy

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate)
  (initial : HiddenOutside.Cache HashInput HashOutput) (model : HiddenRows.Model HashInput HashOutput A Coordinate)
  (parameter : PublicParameter) (data : PublicData) (m : Message)

/-- **One signing call, the law of the signed view.** Averaged over the uniform start and the scan,
the upper value of a monotone function of the disclosures is at most the law of the signed view of
the message applied to that function: `sign_term` stopped before the fresh slot. -/
theorem sign_termS (hparse : ∀ ρ, model.parse (blk parameter data m ρ) = none)
    {X : Multiset View → ℝ≥0∞} (hX : Monotone' X) (s : State) (d : Multiset View)
    (excl : Pair → Prop) (budget : ℕ) :
    ∑' out, Pr{let x ← (interp tg initial model
          ((liftM ($ᵗ Randomness : ProbComp Randomness) : OracleComp CostSpec Randomness) >>= fun start =>
            signCostSourceLoop parameter data m digestAttemptLimit start) budget s)}[x = out] *
        (X d + (freshNewWeight parameter data m s (fun v => X (d + {v}) - X d) out +
          outWeight parameter data m s 0 (fun ρ v => if excl (m, ρ) then 0 else X (d + {v}) - X d) out)) ≤
      sgnM parameter data s excl m X d := by
  set gf : View → ℝ≥0∞ := fun v => X (d + {v}) - X d with hgf
  set gp : Randomness → View → ℝ≥0∞ := fun ρ v => if excl (m, ρ) then 0 else X (d + {v}) - X d with hgp
  set c := (Fintype.card Randomness : ℝ≥0∞)⁻¹ with hc
  have hcard : c * (Fintype.card Randomness : ℝ≥0∞) = 1 :=
    ENNReal.inv_mul_cancel (by exact_mod_cast Fintype.card_ne_zero) (ENNReal.natCast_ne_top _)
  have hscan : ∑' out, Pr{let x ← (interp tg initial model
        ((liftM ($ᵗ Randomness : ProbComp Randomness) : OracleComp CostSpec Randomness) >>= fun start =>
          signCostSourceLoop parameter data m digestAttemptLimit start) budget s)}[x = out] *
        (freshNewWeight parameter data m s gf out + outWeight parameter data m s 0 gp out) ≤
      c * ∑ start, walk nextRand landing (stOf parameter data m s) (poolValue parameter data m s gp)
        (freshAvg Finset.univ gf) 0 digestAttemptLimit start := by
    rw [interp_liftProb_bind, OracleComp.tsum_prEvent_bind_mul]
    have hpr : ∀ ρ, Pr{let x ← ($ᵗ Randomness : ProbComp Randomness)}[x = ρ] = c := by
      intro ρ
      rw [SampleableType.prEvent_uniformSample_eq_singleton]
    simp only [hpr]
    rw [ENNReal.tsum_mul_left, tsum_fintype]
    refine mul_le_mul' le_rfl (Finset.sum_le_sum fun start _ => ?_)
    exact scan_bound_comb tg initial model parameter data m hparse s gf gp digestAttemptLimit
      (by unfold digestAttemptLimit; norm_num) budget start
  have hsum : ∑' out, Pr{let x ← (interp tg initial model
        ((liftM ($ᵗ Randomness : ProbComp Randomness) : OracleComp CostSpec Randomness) >>= fun start =>
          signCostSourceLoop parameter data m digestAttemptLimit start) budget s)}[x = out] *
        (X d + (freshNewWeight parameter data m s gf out + outWeight parameter data m s 0 gp out)) ≤
      X d + c * ∑ start, walk nextRand landing (stOf parameter data m s) (poolValue parameter data m s gp)
        (freshAvg Finset.univ gf) 0 digestAttemptLimit start := by
    rw [tsum_congr fun out => mul_add _ _ _, ENNReal.tsum_add, ENNReal.tsum_mul_right]
    exact add_le_add (mul_le_of_le_one_left' (OracleComp.tsum_prEvent_le_one _)) hscan
  refine le_trans hsum ?_
  have hbase : X d = c * ∑ start : Randomness, walk nextRand landing (stOf parameter data m s) (fun _ => X d)
      (X d) (X d) digestAttemptLimit start := by
    simp only [walk_const landing_le_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← mul_assoc, hcard, one_mul]
  have hfr : X d + freshAvg Finset.univ gf = freshAvg Finset.univ (fun v => X (d + {v})) := by
    calc X d + freshAvg Finset.univ gf = freshAvg Finset.univ (fun v => X d + gf v) := by
          rw [freshAvg_add, freshAvg_const _ Finset.univ_nonempty]
      _ = _ := by
          congr 1
          funext v
          exact add_tsub_cancel_of_le (hX _ _ (Multiset.le_add_right _ _))
  have hgoal : c * (∑ start : Randomness, walk nextRand landing (stOf parameter data m s) (fun _ => X d)
        (X d) (X d) digestAttemptLimit start) +
      c * ∑ start, walk nextRand landing (stOf parameter data m s) (poolValue parameter data m s gp)
        (freshAvg Finset.univ gf) 0 digestAttemptLimit start ≤ sgnM parameter data s excl m X d := by
    rw [← mul_add, ← Finset.sum_add_distrib]
    unfold sgnM sgn ws
    refine mul_le_mul' le_rfl (Finset.sum_le_sum fun start _ => ?_)
    rw [← walk_add]
    refine walk_mono _ (fun ρ => ?_) (le_of_eq hfr) (by rw [add_zero]) _ start
    unfold poolValue extOf
    cases h0 : s.cache (blk parameter data m ρ) with
    | none =>
        simp only [Option.elim, add_zero]
        exact hX _ _ (Multiset.le_add_right _ _)
    | some u0 =>
        simp only [Option.elim]
        split_ifs with hl hx
        · simp only [hgp, ite_eq_left hx, add_zero, le_refl]
        · have hv : pview parameter data s (m, ρ) = viewOf u0 := pview_of_cached h0
          simp only [hgp, ite_eq_right hx, hv]
          rw [add_tsub_cancel_of_le (hX _ _ (Multiset.le_add_right _ _))]
        · rw [add_zero]
          exact hX _ _ (Multiset.le_add_right _ _)
        · rw [add_zero]
          exact hX _ _ (Multiset.le_add_right _ _)
  refine le_trans (le_of_eq ?_) hgoal
  rw [← hbase]

end SignHeavy

section SignUpperH

variable (parameter : PublicParameter) (data : PublicData) (Qtot : ℕ) (w : ℝ≥0∞) (m : Message) (s : State) (n : ℕ)
  (d : Multiset View) (f : Multiset View → ℝ≥0∞)

/-- The value of a term through the live messages other than the signed one: the groups of the light
ones on the inner function of the heavy one, if any. -/
noncomputable def restH (L : QueryLog SigningSpec) (Ms : List Message) (excl : Pair → Prop) (J : List View) :
    Multiset View → ℝ≥0∞ :=
  valH parameter data w s excl (lightMsgs parameter data Qtot s (restMsgs m L Ms))
    (heavyMsg parameter data Qtot s (restMsgs m L Ms)) f n J

/-- Upper value of one signing outcome, for the future pairs `J`. -/
noncomputable def upperH (L : QueryLog SigningSpec) (Ms : List Message) (excl : Pair → Prop)
    (out : Run HashInput Coordinate (Option Signature) × State) (J : List View) : ℝ≥0∞ :=
  restH parameter data Qtot w m s n f L Ms excl J d +
    (freshNewWeight parameter data m s
        (fun v => restH parameter data Qtot w m s n f L Ms excl J (d + {v}) - restH parameter data Qtot w m s n f L Ms excl J d) out +
      outWeight parameter data m s 0 (fun ρ v => if excl (m, ρ) then 0 else
        restH parameter data Qtot w m s n f L Ms excl J (d + {v}) - restH parameter data Qtot w m s n f L Ms excl J d) out)

variable {parameter data w s n f}

/-- One more signature left is one fresh slot inside the value. -/
theorem valH_succ (excl : Pair → Prop) (Ls : List Message) (hv : Option Message) (J : List View) (e : Multiset View) :
    valH parameter data w s excl Ls hv f (n + 1) J e =
      freshAvg Finset.univ fun v => valH parameter data w s excl Ls hv f n J (e + {v}) := by
  unfold valH
  rw [grpAll_congr s excl (innerH_succ s excl hv f n J) Ls e, grpAll_freshAvg]
  exact congrArg (freshAvg Finset.univ) (funext fun v => grpAll_shift s excl _ {v} Ls e)

end SignUpperH

section SignExpectH

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)
  {parameter : PublicParameter} {data : PublicData} {Qtot : ℕ} {w : ℝ≥0∞} {m : Message} {s : State} {n : ℕ}
  {d : Multiset View} {f : Multiset View → ℝ≥0∞}

/-- **A dominated term.** Averaged over a signing call of a live message, the upper value of a term
is at most its value with one more signature left: the group of the signed message with one fresh
slot if it is light, the law of its signed view (which takes the spare slot) if it is heavy. -/
theorem term_expectH (hparse : ∀ ρ, model.parse (blk parameter data m ρ) = none) (hf : MonoFin f)
    {Ms : List Message} (hM : MInv parameter data s Ms) {budgetT : ℕ} (hT : TotalInv parameter data Qtot s budgetT)
    {L : QueryLog SigningSpec} (hm : MsgLive L m) (excl : Pair → Prop) (budget k : ℕ) :
    ∑' out, Pr{let x ← interp tg initial model (signCostSource parameter data m) budget s}[x = out] *
        creations Finset.univ landing (fun J => upperH parameter data Qtot w m s n d f L Ms excl out J) k [] ≤
      termH parameter data Qtot w s Ms L excl f d (n + 1) k := by
  rw [← termH_addMsg hM L excl m f d (n + 1) k]
  unfold termH
  rw [creations_tsum]
  refine creations_mono (fun J => ?_) k []
  have hperm : (live L (addMsg Ms m)).Perm (m :: restMsgs m L Ms) := live_perm hm hM.nodup
  have hrestne : ∀ m' ∈ restMsgs m L Ms, m' ≠ m := by
    intro m' hm'
    unfold restMsgs at hm'
    simpa using (List.mem_filter.1 hm').2
  have hX : Monotone' (restH parameter data Qtot w m s n f L Ms excl J) := valH_mono hf.1 s excl _ _ n J
  by_cases hH : Heavy parameter data Qtot s m
  · -- the signed message is heavy: the law of its signed view
    have hnoneR : heavyMsg parameter data Qtot s (restMsgs m L Ms) = none :=
      heavyMsg_eq_none.2 fun m' hm' hh => hrestne m' hm' (heavy_unique hT hh hH)
    have hlightR : lightMsgs parameter data Qtot s (restMsgs m L Ms) = restMsgs m L Ms := lightMsgs_of_none hnoneR
    have hsomeV : heavyMsg parameter data Qtot s (live L (addMsg Ms m)) = some m :=
      (heavyMsg_eq_some_iff hT).2 ⟨hperm.mem_iff.2 (List.mem_cons_self ..), hH⟩
    have hlightV : (lightMsgs parameter data Qtot s (live L (addMsg Ms m))).Perm (restMsgs m L Ms) := by
      have h1 := hperm.filter (fun m' => decide (¬Heavy parameter data Qtot s m'))
      rw [List.filter_cons, ite_eq_right (by simpa using hH)] at h1
      rw [← hlightR]
      exact h1
    refine le_trans (sign_termS tg initial model parameter data m hparse hX s d excl budget) (le_of_eq ?_)
    have hL : sgnM parameter data s excl m (restH parameter data Qtot w m s n f L Ms excl J) d =
        sgnM parameter data s excl m
          (grpAll parameter data s excl (restMsgs m L Ms) (virtualOnce Finset.univ w f (n + 1) J)) d := by
      unfold restH
      rw [hnoneR, hlightR]
      rfl
    have hR : baseH parameter data Qtot w s (addMsg Ms m) L excl f d (n + 1) J =
        sgnM parameter data s excl m
          (grpAll parameter data s excl (restMsgs m L Ms) (virtualOnce Finset.univ w f (n + 1) J)) d := by
      unfold baseH
      rw [hsomeV, valH_perm_msgs s excl hlightV, valH_heavy_eq]
    rw [hL, hR]
  · -- the signed message is light: its group and one fresh slot
    have hhv : heavyMsg parameter data Qtot s (live L (addMsg Ms m)) =
        heavyMsg parameter data Qtot s (restMsgs m L Ms) := by
      cases hR : heavyMsg parameter data Qtot s (restMsgs m L Ms) with
      | none =>
          refine heavyMsg_eq_none.2 fun m' hm' => ?_
          rcases List.mem_cons.1 (hperm.mem_iff.1 hm') with h | h
          · rw [h]; exact hH
          · exact heavyMsg_eq_none.1 hR m' h
      | some h =>
          exact (heavyMsg_eq_some_iff hT).2
            ⟨hperm.mem_iff.2 (List.mem_cons_of_mem _ (heavyMsg_some hR).1), (heavyMsg_some hR).2⟩
    have hlightV : (lightMsgs parameter data Qtot s (live L (addMsg Ms m))).Perm
        (m :: lightMsgs parameter data Qtot s (restMsgs m L Ms)) := by
      have h1 := hperm.filter (fun m' => decide (¬Heavy parameter data Qtot s m'))
      rw [List.filter_cons, ite_eq_left (by simpa using hH)] at h1
      exact h1
    refine le_trans (sign_term tg initial model parameter data m hparse hX s d excl budget) (le_of_eq ?_)
    have hR : baseH parameter data Qtot w s (addMsg Ms m) L excl f d (n + 1) J =
        grpM parameter data s excl m (valH parameter data w s excl
          (lightMsgs parameter data Qtot s (restMsgs m L Ms))
          (heavyMsg parameter data Qtot s (restMsgs m L Ms)) f (n + 1) J) d := by
      unfold baseH
      rw [hhv, valH_perm_msgs s excl hlightV]
      rfl
    rw [hR]
    unfold grpM
    exact grp_congr _ _ (fun e => (valH_succ excl _ _ J e).symm) d

end SignExpectH

section SignPointH

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)
  (parameter : PublicParameter) (data : PublicData) (Qtot : ℕ) (w : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))
  (m : Message)

/-- A term after one signing outcome is below its upper value. -/
theorem post_term_leH (hw : w ≤ 1) {f : Multiset View → ℝ≥0∞} (hf : MonoFin f)
    (hparse : ∀ p, model.parse (pblk parameter data p) = none)
    (hfail : ∀ ρ digest budget (s1 : State), Prepared initial s1 →
      ∀ out ∈ support (interp tg initial model (finishRest parameter data m ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ Fail)
    (budget : ℕ) (s : State) (Ms : List Message) (L : QueryLog SigningSpec) (d : Multiset View)
    (hprep : Prepared initial s)
    (out : Run HashInput Coordinate (Option Signature) × State)
    (hout : out ∈ support (interp tg initial model (signCostSource parameter data m) budget s))
    (r : Option Signature) (hr : out.1.1 = some r) (excl : Pair → Prop)
    (hex : ∀ sig, r = some sig → s.cache (blk parameter data m sig.randomness) ≠ none → ¬excl (m, sig.randomness))
    (n : ℕ) {k' k : ℕ} (hk : k' ≤ k) :
    termH parameter data Qtot w out.2 (addMsg Ms m) (L ++ [⟨m, r⟩]) excl f (discAfter parameter data m s d out) n k' ≤
      creations Finset.univ landing (fun J => upperH parameter data Qtot w m s n d f L Ms excl out J) k [] := by
  have hpost := source_post tg initial model parameter data m (fun ρ => hparse (m, ρ)) Fail hfail
    budget s hprep out hout r hr
  have hshape := sign_shape parameter data Fail m hpost out rfl hr
  refine le_trans (termH_mono hw hf _ _ _ excl _ n hk) (creations_mono (fun J => ?_) k [])
  have hkeep : ∀ m' ∈ restMsgs m L Ms, ∀ ρ,
      out.2.cache (blk parameter data m' ρ) = s.cache (blk parameter data m' ρ) := by
    intro m' hm' ρ
    have hne : m' ≠ m := by
      unfold restMsgs at hm'
      simpa using (List.mem_filter.1 hm').2
    exact other_message_keptS tg initial model budget s out hout (m', ρ) hne
  have hheavy : ∀ m' ∈ restMsgs m L Ms, (Heavy parameter data Qtot out.2 m' ↔ Heavy parameter data Qtot s m') :=
    fun m' hm' => heavy_congr (hkeep m' hm')
  unfold baseH
  rw [live_after L r Ms, lightMsgs_congr hheavy, heavyMsg_congr hheavy,
    valH_blocksOn excl (fun m' hm' => hkeep m' (mem_lightMsgs.1 hm').1) (fun h hh => hkeep h (heavyMsg_some hh).1)]
  exact upper_pointX (valH_mono hf.1 s excl _ _ n J) d excl out r hr Fail hshape hex

end SignPointH

end Sphincs.Security.ForsPotential
