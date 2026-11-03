import FORS.ScanSigner.FairShare
import FORS.LazyRun.InterpreterFacts

/-! What a completed signing call leaves behind in the lazy run: at most one selected pair, wholly
cached, every other randomizer of the message unchanged or rejected, FORS coordinates revealed
only at the leaves the selected digest opens (`ForsOk`), and, on failure, no reveals and a failing
index. -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.HiddenDebt

variable [Params]

open HiddenCost HiddenBridge HiddenOutside HiddenReveal

variable {D R A ι : Type} [Fintype ι] [SampleableType R]
attribute [local instance] saturationDecEqCoordinate
variable (tg : Targeting D R ι) (initial : Cache D R) (model : HiddenRows.Model D R A ι)

omit [Params] [Fintype ι] [SampleableType R] in
/-- A family of known values is known. -/
theorem allSome_of_eq {n : Nat} {α : Type} (values : Fin n → Option α) (u : Fin n → α)
    (h : ∀ index, values index = some (u index)) :
    Completeness.allSome (α := fun _ => α) values = some u := by
  unfold Completeness.allSome
  rw [dif_pos fun index => by rw [h index]; rfl]
  refine congrArg some (funext fun index => Option.some_injective _ ?_)
  rw [Option.some_get, h index]

omit [Fintype ι] in
/-- **A family of unparsed entries, read in order, in the support.** The reads disclose nothing and
touch no other input, so a completed outcome of the whole computation is an outcome of its rest at
one tuple of answers, from a state that holds them. -/
theorem all_read_support {β : Type} : ∀ {n : Nat} (x : Fin n → D), Function.Injective x →
    (∀ index, model.parse (x index) = none) → ∀ (state : DebtState D R ι)
      (rest : (Fin n → R) → OracleComp (SourceCostSpec D R ι) β) (budget : ℕ)
      (out : Run D ι β × DebtState D R ι),
    out ∈ support (interp tg initial model (Concrete.sequenceFin (fun index =>
          (liftM ((SourceCostSpec D R ι).query (.inl (.inr (.inl (x index))))) :
            OracleComp (SourceCostSpec D R ι) R)) >>= rest) budget state) → out.1.1 ≠ none →
    ∃ (u : Fin n → R) (b : ℕ) (s' : DebtState D R ι) (o : Run D ι β × DebtState D R ι),
      Extends state s' ∧
      (∀ index, s'.cache (x index) = some (u index)) ∧
      (∀ index, state.cache (x index) = none ∨ state.cache (x index) = some (u index)) ∧
      (∀ y, (∀ index, y ≠ x index) → s'.cache y = state.cache y) ∧
      o ∈ support (interp tg initial model (rest u) b s') ∧
      out.1.1 = o.1.1 ∧ out.1.2.1 = o.1.2.1 ∧ out.2 = o.2
  | 0, _, _, _, state, rest, budget, out, hout, _ => by
      rw [Concrete.sequenceFin, pure_bind] at hout
      exact ⟨Fin.elim0, budget, state, out, Extends.refl state, fun index => index.elim0,
        fun index => index.elim0, fun _ _ => rfl, hout, rfl, rfl, rfl⟩
  | n + 1, x, hx, hp, state, rest, budget, out, hout, hsome => by
      have hstep : (Concrete.sequenceFin (fun index =>
          (liftM ((SourceCostSpec D R ι).query (.inl (.inr (.inl (x index))))) :
            OracleComp (SourceCostSpec D R ι) R)) >>= rest) =
          liftM ((SourceCostSpec D R ι).query (.inl (.inr (.inl (x 0))))) >>= fun head =>
            (Concrete.sequenceFin fun index : Fin n =>
              (liftM ((SourceCostSpec D R ι).query (.inl (.inr (.inl (x index.succ))))) :
                OracleComp (SourceCostSpec D R ι) R)) >>= fun values =>
              rest (Fin.cases head values) := by
        rw [Concrete.sequenceFin]
        simp only [bind_assoc, pure_bind]
        rfl
      have hzero : ∀ index : Fin n, x index.succ ≠ x 0 := fun index heq =>
        Fin.succ_ne_zero index (hx heq)
      rw [hstep, interp_ordinary] at hout
      split_ifs at hout with hbudget
      · rw [ordinaryStep, hp 0] at hout
        simp only at hout
        rw [support_bind] at hout
        obtain ⟨res, hres, hout⟩ := Set.mem_iUnion₂.1 hout
        rw [support_map] at hout
        obtain ⟨o1, ho1, rfl⟩ := hout
        simp only at hsome
        have hhead : res.2.cache (x 0) = some res.1 ∧
            (state.cache (x 0) = none ∨ state.cache (x 0) = some res.1) ∧
            (∀ y, y ≠ x 0 → res.2.cache y = state.cache y) ∧ Extends state res.2 := by
          cases hc0 : state.cache (x 0) with
          | some v =>
              rw [readOutside_cached _ state v hc0, support_pure, Set.mem_singleton_iff] at hres
              rw [hres]
              exact ⟨hc0, Or.inr rfl, fun _ _ => rfl, Extends.refl state⟩
          | none =>
              rw [readOutside_fresh _ state hc0, support_map] at hres
              obtain ⟨v, _, rfl⟩ := hres
              exact ⟨by simp [DebtState.store], Or.inl rfl, fun y hy => store_cache_ne state _ y hy v,
                extends_store state _ v hc0⟩
        obtain ⟨hhead0, hheads, hheado, hheade⟩ := hhead
        obtain ⟨ut, b, s', o, hext, hs', hstate', hother', ho, hr1, hr2, hr3⟩ :=
          all_read_support (fun index : Fin n => x index.succ)
            (fun a b heq => Fin.succ_injective n (hx heq)) (fun index => hp index.succ) res.2
            (fun values => rest (Fin.cases res.1 values)) (budget - 1) o1 ho1 hsome
        refine ⟨Fin.cases res.1 ut, b, s', o, hheade.trans hext, fun index => ?_, fun index => ?_,
          fun y hy => (hother' y fun index => hy index.succ).trans (hheado y (hy 0)), ho, hr1, hr2, hr3⟩
        · induction index using Fin.cases with
          | zero => rw [hother' (x 0) fun index => (hzero index).symm, hhead0]; rfl
          | succ index => exact hs' index
        · induction index using Fin.cases with
          | zero => exact hheads
          | succ index => rw [← hheado _ (hzero index)]; exact hstate' index
      · rw [support_pure, Set.mem_singleton_iff] at hout
        rw [hout] at hsome
        exact absurd rfl hsome

end FORS.Security.HiddenDebt

namespace FORS.Security.GraphView

variable [Params]

open Concrete Completeness Prefix HiddenGraph HiddenCost HiddenDebt ForsSigner

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable


/-- A reveal is a FORS position the digest opens, or not a FORS position at all. -/
def ForsOk (digest : MessageDigest) (x : Coordinate) : Prop :=
  ∀ i κ l q, x = .fors i κ l q → i = digestIndex digest ∧ l = digestLeaves digest κ

theorem revealsIn_treeCostSource (digest : MessageDigest) (data : PublicData) (κ : FTree) :
    RevealsIn (D := HashInput) (R := HashOutput) (ForsOk digest)
      (treeCostSource data (digestIndex digest) κ (digestLeaves digest κ)) := by
  unfold treeCostSource
  refine revealsIn_bind _ (revealsIn_sequenceFin _ _ fun k => revealsIn_reveal _ _ ?_)
    fun _ => revealsIn_pure _ _
  intro i κ' l q h
  cases h
  exact ⟨rfl, rfl⟩

theorem revealsIn_sequenceDep (P : Coordinate → Prop) : ∀ {n : Nat} {α : Fin n → Type}
    {computation : (i : Fin n) → OracleComp CostSpec (Option (α i))},
    (∀ i, RevealsIn (D := HashInput) (R := HashOutput) P (computation i)) →
    RevealsIn (D := HashInput) (R := HashOutput) P (sequenceDep computation)
  | 0, _, _, _ => revealsIn_pure _ _
  | _ + 1, α, computation, h => by
      unfold sequenceDep
      refine revealsIn_bind _ (h 0) fun head => ?_
      rcases head with _ | head
      · exact revealsIn_pure _ _
      · refine revealsIn_bind _ (revealsIn_sequenceDep P (α := fun i => α i.succ) fun i => h i.succ)
          fun tail => ?_
        rcases tail with _ | tail <;> exact revealsIn_pure _ _

/-- A layer's counter search reveals nothing. -/
theorem revealsIn_layerCostSearch (P : Coordinate → Prop) (parameter : PublicParameter)
    (data : PublicData) (index : Index) (lay : Layer) :
    RevealsIn (D := HashInput) (R := HashOutput) P (layerCostSearch parameter data index lay) := by
  unfold layerCostSearch
  refine revealsIn_bind _ (revealsIn_tick _ _) fun _ => ?_
  refine revealsIn_bind _ (revealsIn_liftHash _ _) fun found => ?_
  rcases found with _ | pair
  · exact revealsIn_pure _ _
  · exact revealsIn_bind _ (revealsIn_tick _ _) fun _ => revealsIn_pure _ _

theorem revealsIn_finishRest (parameter : PublicParameter) (data : PublicData) (message : Message)
    (randomness : Randomness) (digest : MessageDigest) :
    RevealsIn (D := HashInput) (R := HashOutput) (ForsOk digest)
      (finishRest parameter data message randomness digest) := by
  unfold finishRest
  refine revealsIn_bind _ (revealsIn_tick _ _) fun _ => ?_
  refine revealsIn_bind _ (revealsIn_sequenceDep _ fun lay => revealsIn_layerCostSearch _ _ _ _ lay)
    fun found => ?_
  rcases found with _ | found
  · exact revealsIn_pure _ _
  · refine revealsIn_bind _ (revealsIn_sequenceFin _ _ fun lay => revealsIn_sequenceFin _ _ fun chain =>
      revealsIn_reveal _ _ ?_) fun _ => ?_
    · intro i κ l q h
      cases h
    refine revealsIn_bind _ (revealsIn_sequenceFin _ _ fun κ => revealsIn_treeCostSource digest data κ)
      fun _ => ?_
    exact revealsIn_pure _ _

theorem revealsIn_false_tick (amount : ℕ) :
    RevealsIn (D := HashInput) (R := HashOutput) (ι := Coordinate) (fun _ => False) (tick amount) :=
  revealsIn_tick _ _

section Finish

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate)
  (initial : HiddenOutside.Cache HashInput HashOutput) (model : HiddenRows.Model HashInput HashOutput A Coordinate)
  (parameter : PublicParameter) (data : PublicData) (message : Message)

theorem no_reveals_of_false {α : Type} (computation : OracleComp CostSpec α)
    (h : RevealsIn (D := HashInput) (R := HashOutput) (fun _ => False) computation) (budget : ℕ)
    (state : DebtState HashInput HashOutput Coordinate)
    (out : Run HashInput Coordinate α × DebtState HashInput HashOutput Coordinate)
    (hout : out ∈ support (interp tg initial model computation budget state)) : out.1.2.1 = [] := by
  rcases hr : out.1.2.1 with _ | ⟨c, rest⟩
  · rfl
  · exact absurd (interp_reveals tg initial model computation h budget state out hout c (by rw [hr]; simp)) id

/-- A failed final assembly reveals nothing. -/
theorem finishRest_none (randomness : Randomness) (digest : MessageDigest) (budget : ℕ)
    (state : DebtState HashInput HashOutput Coordinate)
    (out : Run HashInput Coordinate (Option Signature) × DebtState HashInput HashOutput Coordinate)
    (hout : out ∈ support (interp tg initial model (finishRest parameter data message randomness digest) budget state))
    (hnone : out.1.1 = some none) : out.1.2.1 = [] := by
  unfold finishRest at hout
  obtain ⟨o1, ho1, h1⟩ := interp_bind_mem tg initial model _ _ budget state out hout
  have hr1 := no_reveals_of_false tg initial model _ (revealsIn_false_tick _) _ _ o1 ho1
  rcases h1 with ⟨_, hn, _⟩ | ⟨_, _, o2, ho2, hres2, hrev2, _⟩
  · rw [hnone] at hn; cases hn
  rw [hrev2, hr1, List.nil_append]
  obtain ⟨o3, ho3, h3⟩ := interp_bind_mem tg initial model _ _ _ _ o2 ho2
  have hr3 := no_reveals_of_false tg initial model _
    (revealsIn_sequenceDep _ fun lay => revealsIn_layerCostSearch _ _ _ _ lay) _ _ o3 ho3
  rcases h3 with ⟨_, hn, _⟩ | ⟨found, hfound, o4, ho4, hres4, hrev4, _⟩
  · rw [hres2, hnone] at *; simp_all
  rw [hrev4, hr3, List.nil_append]
  rcases found with _ | found
  · change o4 ∈ support (interp tg initial model (pure none) _ _) at ho4
    rw [interp_pure, support_pure, Set.mem_singleton_iff] at ho4
    rw [ho4]
  · exfalso
    have hmem := interp_result_mem tg initial model _ _ _ o4 ho4 none (by rw [← hres4, ← hres2, hnone])
    revert hmem
    dsimp only
    intro hmem
    refine post_bind (fun v => v ≠ none) _ (fun _ => post_bind _ _ fun _ => ?_) none hmem rfl
    intro v hv
    rw [support_pure, Set.mem_singleton_iff] at hv
    rw [hv]
    exact fun h => by cases h

/-- **Final assembly, support.** Its digest call reads the blocks of its own pair — the cached ones
as they stand, the rest freshly — and it then signs the digest of that pair. -/
theorem finish_post (hparse : ∀ ρ call, model.parse (pblk parameter data message ρ call) = none)
    (Fail : Finset (Fin (2 ^ subtreeHeight)))
    (hfail : ∀ ρ digest budget (s1 : DebtState HashInput HashOutput Coordinate), Prepared initial s1 →
      ∀ out ∈ support (interp tg initial model (finishRest parameter data message ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ Fail)
    (ρ : Randomness) (budget : ℕ) (s1 : DebtState HashInput HashOutput Coordinate)
    (hprep : Prepared initial s1)
    (out : Run HashInput Coordinate (Option Signature) × DebtState HashInput HashOutput Coordinate)
    (hout : out ∈ support (interp tg initial model (finishCostSource parameter data message ρ) budget s1))
    (r : Option Signature) (hr : out.1.1 = some r) :
    ∃ u : DigestCall → HashOutput,
      (∀ call, s1.cache (pblk parameter data message ρ call) = none ∨
        s1.cache (pblk parameter data message ρ call) = some (u call)) ∧
      pcache parameter data message out.2 ρ = some u ∧
      (∀ x, IsMsgInput x → (∀ call, x ≠ pblk parameter data message ρ call) →
        out.2.cache x = s1.cache x) ∧
      (∀ c ∈ out.1.2.1, ForsOk (truncateMessageDigest u) c) ∧
      (∀ sig, r = some sig → sig.randomness = ρ) ∧
      (r = none → out.1.2.1 = [] ∧ (Lifetime.localDigestView (truncateMessageDigest u)).1 ∈ Fail) := by
  have hsig : ∀ sig, r = some sig → sig.randomness = ρ := by
    intro sig hsig
    have hmem := interp_result_mem tg initial model _ budget s1 out hout r hr
    exact finish_randomness parameter data message ρ r hmem sig hsig
  have hcache := finish_keeps_msg tg initial model parameter data message ρ budget s1 out hout
  rw [finishCostSource_eq] at hout
  obtain ⟨u, b, s2, o, hext, hs2, hstate, hother, ho, hres, hrev, hst⟩ :=
    all_read_support tg initial model _ (pblk_injective parameter data message ρ) (hparse ρ) s1 _
      budget out hout (by rw [hr]; simp)
  have hprep2 : Prepared initial s2 := fun input output hin => hext.1 input output (hprep input output hin)
  have hpc : pcache parameter data message out.2 ρ = some u := by
    unfold pcache
    refine allSome_of_eq _ u fun call => ?_
    rw [hst]
    exact (interp_extends tg initial model _ b s2 o ho).1 _ _ (hs2 call)
  refine ⟨u, hstate, hpc, hcache, fun c hcmem => ?_, hsig, fun hnone => ?_⟩
  · rw [hrev] at hcmem
    exact interp_reveals tg initial model _ (revealsIn_finishRest parameter data message ρ _) b s2 o ho c hcmem
  · have hro : o.1.1 = some none := by rw [← hres, hr, hnone]
    exact ⟨by rw [hrev]; exact finishRest_none tg initial model parameter data message ρ _ b s2 o ho hro,
      hfail ρ _ b s2 hprep2 o ho hro⟩

end Finish

section Loop

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate)
  (initial : HiddenOutside.Cache HashInput HashOutput) (model : HiddenRows.Model HashInput HashOutput A Coordinate)
  (parameter : PublicParameter) (data : PublicData) (message : Message)

/-- One randomizer of the message: its block unchanged or a new rejected one. -/
def RelatedAt (s s' : DebtState HashInput HashOutput Coordinate) (ρ : Randomness) : Prop :=
  s'.cache (blk parameter data message ρ) = s.cache (blk parameter data message ρ) ∨
    (s.cache (blk parameter data message ρ) = none ∧ ∃ u,
      s'.cache (blk parameter data message ρ) = some u ∧ ¬Landed parameter (blockIndex u))

theorem RelatedAt.refl (s : DebtState HashInput HashOutput Coordinate) (ρ : Randomness) :
    RelatedAt parameter data message s s ρ := Or.inl rfl

theorem RelatedAt.trans {s s' s'' : DebtState HashInput HashOutput Coordinate} {ρ : Randomness}
    (h : RelatedAt parameter data message s s' ρ) (h' : RelatedAt parameter data message s' s'' ρ) :
    RelatedAt parameter data message s s'' ρ := by
  rcases h' with h2 | ⟨h2n, u, hu, hnl⟩
  · rcases h with h1 | h1
    · exact Or.inl (h2.trans h1)
    · unfold RelatedAt; rw [h2]; exact Or.inr h1
  · rcases h with h1 | ⟨h1n, _, hu1, _⟩
    · exact Or.inr ⟨h1 ▸ h2n, u, hu, hnl⟩
    · rw [hu1] at h2n; cases h2n

/-- The selected pair of a completed signing call: the whole pair is cached, and its index
block lands. -/
def Selected (s s' : DebtState HashInput HashOutput Coordinate) (ρ : Randomness)
    (u : DigestCall → HashOutput) : Prop :=
  pcache parameter data message s' ρ = some u ∧ Landed parameter (blockIndex (u firstCall)) ∧
  (s.cache (blk parameter data message ρ) = none ∨
    s.cache (blk parameter data message ρ) = some (u firstCall)) ∧
  ∀ ρ', ρ' ≠ ρ → RelatedAt parameter data message s s' ρ'

/-- What a completed signing call leaves behind. -/
def SignPost (Fail : Finset (Fin (2 ^ subtreeHeight))) (s s' : DebtState HashInput HashOutput Coordinate)
    (reveals : List Coordinate) (r : Option Signature) : Prop :=
  (r = none ∧ reveals = [] ∧ ∀ ρ, RelatedAt parameter data message s s' ρ) ∨
  ∃ ρ u, Selected parameter data message s s' ρ u ∧
    (∀ c ∈ reveals, ForsOk (truncateMessageDigest u) c) ∧
    (∀ sig, r = some sig → sig.randomness = ρ) ∧
    (r = none → reveals = [] ∧ (s.cache (blk parameter data message ρ) = none →
      (Lifetime.localDigestView (truncateMessageDigest u)).1 ∈ Fail))

end Loop

end FORS.Security.GraphView
