import SphincsFors.BridgeSignerFors
import SphincsFors.BridgeInterpSupport

/-! What a completed signing call leaves behind in the lazy run: at most one selected pair with
both blocks cached, every other randomizer of the message unchanged or rejected, FORS secrets
revealed only for the selected digest, and, on failure, no reveals and a failing index. -/

open OracleComp OracleSpec ENNReal

namespace SphincsFors.Security.GraphView

open Concrete Completeness Prefix HiddenGraph HiddenCost HiddenDebt ForsSigner

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

variable [Params]

/-- A reveal is a FORS secret of the digest, or not a FORS secret at all. -/
def FtsOk (digest : MessageDigest) (c : Coordinate) : Prop :=
  ∀ i t l, c = .ftsSecret i t l → i = digestIndex digest ∧ l = digestLeaves digest t

theorem revealsIn_finishRest (parameter : PublicParameter) (data : PublicData) (message : Message)
    (randomness : Randomness) (digest : MessageDigest) :
    RevealsIn (D := HashInput) (R := HashOutput) (FtsOk digest)
      (finishRest parameter data message randomness digest) := by
  unfold finishRest
  refine revealsIn_bind _ (revealsIn_tick _ _) fun _ => ?_
  refine revealsIn_bind _ (revealsIn_liftHash _ _) fun found => ?_
  rcases found with _ | ⟨counter, word⟩
  · exact revealsIn_pure _ _
  · refine revealsIn_bind _ (revealsIn_sequenceFin _ _ fun chain => revealsIn_reveal _ _ ?_) fun _ => ?_
    · intro i t l h
      cases h
    refine revealsIn_bind _ (revealsIn_sequenceFin _ _ fun tree => revealsIn_reveal _ _ ?_) fun _ => ?_
    · intro i t l h
      cases h
      exact ⟨rfl, rfl⟩
    exact revealsIn_bind _ (revealsIn_tick _ _) fun _ => revealsIn_pure _ _

omit [Params] in
theorem revealsIn_false_tick (amount : ℕ) :
    RevealsIn (D := HashInput) (R := HashOutput) (ι := Coordinate) (fun _ => False) (tick amount) :=
  revealsIn_tick _ _

section Finish

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate)
  (initial : HiddenOutside.Cache HashInput HashOutput) (model : HiddenRows.Model HashInput HashOutput A Coordinate)
  (parameter : PublicParameter) (data : PublicData) (message : Message)

omit [Params] in
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
  have hr3 := no_reveals_of_false tg initial model _ (revealsIn_liftHash _ _) _ _ o3 ho3
  rcases h3 with ⟨_, hn, _⟩ | ⟨found, hfound, o4, ho4, hres4, hrev4, _⟩
  · rw [hres2, hnone] at *; simp_all
  rw [hrev4, hr3, List.nil_append]
  rcases found with _ | ⟨counter, word⟩
  · change o4 ∈ support (interp tg initial model (pure none) _ _) at ho4
    rw [interp_pure, support_pure, Set.mem_singleton_iff] at ho4
    rw [ho4]
  · exfalso
    have hmem := interp_result_mem tg initial model _ _ _ o4 ho4 none (by rw [← hres4, ← hres2, hnone])
    revert hmem
    dsimp only
    intro hmem
    refine post_bind (fun v => v ≠ none) _ (fun _ => post_bind _ _ fun _ => post_bind _ _ fun _ => ?_) none hmem rfl
    intro v hv
    rw [support_pure, Set.mem_singleton_iff] at hv
    rw [hv]
    exact fun h => by cases h

/-- **Final assembly, support.** -/
theorem finish_post (hparse : ∀ ρ call, model.parse (blk parameter data message ρ call) = none)
    (Fail : Finset (Fin (2 ^ subtreeHeight)))
    (hfail : ∀ ρ digest budget (s1 : DebtState HashInput HashOutput Coordinate), Prepared initial s1 →
      ∀ out ∈ support (interp tg initial model (finishRest parameter data message ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ Fail)
    (ρ : Randomness) (budget : ℕ) (s1 : DebtState HashInput HashOutput Coordinate)
    (hprep : Prepared initial s1) (u0 : HashOutput) (hc0 : s1.cache (blk parameter data message ρ 0) = some u0)
    (out : Run HashInput Coordinate (Option Signature) × DebtState HashInput HashOutput Coordinate)
    (hout : out ∈ support (interp tg initial model (finishCostSource parameter data message ρ) budget s1))
    (r : Option Signature) (hr : out.1.1 = some r) :
    ∃ u1, out.2.cache (blk parameter data message ρ 0) = some u0 ∧
      out.2.cache (blk parameter data message ρ 1) = some u1 ∧
      (s1.cache (blk parameter data message ρ 1) = none ∨ s1.cache (blk parameter data message ρ 1) = some u1) ∧
      (∀ x, IsMsgInput x → x ≠ blk parameter data message ρ 1 → out.2.cache x = s1.cache x) ∧
      (∀ c ∈ out.1.2.1, FtsOk (truncateMessageDigest u0 u1) c) ∧
      (∀ sig, r = some sig → sig.randomness = ρ) ∧
      (r = none → out.1.2.1 = [] ∧ (Lifetime.localDigestView (truncateMessageDigest u0 u1)).1 ∈ Fail) := by
  have hsig : ∀ sig, r = some sig → sig.randomness = ρ := by
    intro sig hsig
    have hmem := interp_result_mem tg initial model _ budget s1 out hout r hr
    exact finish_randomness parameter data message ρ r hmem sig hsig
  rw [finishCostSource_eq] at hout
  rw [interp_ordinary] at hout
  split_ifs at hout with h1
  · rw [ordinaryStep, hparse ρ 0] at hout
    simp only at hout
    rw [readOutside_cached _ s1 u0 hc0, pure_bind, support_map] at hout
    obtain ⟨o, ho, rfl⟩ := hout
    simp only at hr ⊢
    rw [interp_ordinary] at ho
    split_ifs at ho with h2
    · rw [ordinaryStep, hparse ρ 1] at ho
      simp only at ho
      rw [support_bind] at ho
      obtain ⟨res, hres, ho⟩ := Set.mem_iUnion₂.1 ho
      rw [support_map] at ho
      obtain ⟨o', ho', rfl⟩ := ho
      simp only at hr ⊢
      -- the state after reading block 1
      have hs2 : res.2.cache (blk parameter data message ρ 1) = some res.1 ∧
          (s1.cache (blk parameter data message ρ 1) = none ∨ s1.cache (blk parameter data message ρ 1) = some res.1) ∧
          (∀ x, x ≠ blk parameter data message ρ 1 → res.2.cache x = s1.cache x) ∧ Prepared initial res.2 := by
        cases hc1 : s1.cache (blk parameter data message ρ 1) with
        | some u1 =>
            rw [readOutside_cached _ s1 u1 hc1, support_pure, Set.mem_singleton_iff] at hres
            rw [hres]
            exact ⟨hc1, Or.inr rfl, fun _ _ => rfl, hprep⟩
        | none =>
            rw [readOutside_fresh _ s1 hc1, support_map] at hres
            obtain ⟨u, _, rfl⟩ := hres
            exact ⟨by simp [DebtState.store], Or.inl rfl, fun x hx => store_cache_ne s1 _ x hx u,
              prepared_store initial s1 hprep _ u hc1⟩
      obtain ⟨hb1, hb1s, hrest, hprep2⟩ := hs2
      have havoid := interp_avoids_cache tg initial model IsMsgInput _
        (avoids_finishRest parameter data message ρ (truncateMessageDigest u0 res.1)) _ res.2 o' ho'
      refine ⟨res.1, ?_, ?_, hb1s, ?_, ?_, hsig, ?_⟩
      · rw [havoid _ (msgInput_digestInput parameter data.root message ρ 0),
          hrest _ (digestInput_ne parameter data.root message ρ), hc0]
      · rw [havoid _ (msgInput_digestInput parameter data.root message ρ 1), hb1]
      · intro x hx hne
        rw [havoid x hx, hrest x hne]
      · intro c hc
        exact interp_reveals tg initial model _ (revealsIn_finishRest parameter data message ρ _) _ _ o' ho' c hc
      · intro hnone
        rw [hnone] at hr
        exact ⟨finishRest_none tg initial model parameter data message ρ _ _ _ o' ho' hr,
          hfail ρ _ _ res.2 hprep2 o' ho' hr⟩
    · rw [support_pure, Set.mem_singleton_iff] at ho
      rw [ho] at hr
      cases hr
  · rw [support_pure, Set.mem_singleton_iff] at hout
    rw [hout] at hr
    cases hr

end Finish

section Loop

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate)
  (initial : HiddenOutside.Cache HashInput HashOutput) (model : HiddenRows.Model HashInput HashOutput A Coordinate)
  (parameter : PublicParameter) (data : PublicData) (message : Message)

/-- One randomizer of the message: block 1 unchanged, block 0 unchanged or a new rejected one. -/
def RelatedAt (s s' : DebtState HashInput HashOutput Coordinate) (ρ : Randomness) : Prop :=
  s'.cache (blk parameter data message ρ 1) = s.cache (blk parameter data message ρ 1) ∧
  (s'.cache (blk parameter data message ρ 0) = s.cache (blk parameter data message ρ 0) ∨
    (s.cache (blk parameter data message ρ 0) = none ∧ ∃ u,
      s'.cache (blk parameter data message ρ 0) = some u ∧ ¬Landed parameter (blockIndex u)))

theorem RelatedAt.refl (s : DebtState HashInput HashOutput Coordinate) (ρ : Randomness) :
    RelatedAt parameter data message s s ρ := ⟨rfl, Or.inl rfl⟩

theorem RelatedAt.trans {s s' s'' : DebtState HashInput HashOutput Coordinate} {ρ : Randomness}
    (h : RelatedAt parameter data message s s' ρ) (h' : RelatedAt parameter data message s' s'' ρ) :
    RelatedAt parameter data message s s'' ρ := by
  refine ⟨h'.1.trans h.1, ?_⟩
  rcases h'.2 with h2 | ⟨h2n, u, hu, hnl⟩
  · rcases h.2 with h1 | h1
    · exact Or.inl (h2.trans h1)
    · rw [h2]; exact Or.inr h1
  · rcases h.2 with h1 | ⟨h1n, _, hu1, _⟩
    · exact Or.inr ⟨h1 ▸ h2n, u, hu, hnl⟩
    · rw [hu1] at h2n; cases h2n

/-- The selected pair of a completed signing call. -/
def Selected (s s' : DebtState HashInput HashOutput Coordinate) (ρ : Randomness) (u0 u1 : HashOutput) : Prop :=
  s'.cache (blk parameter data message ρ 0) = some u0 ∧ Landed parameter (blockIndex u0) ∧
  s'.cache (blk parameter data message ρ 1) = some u1 ∧
  (s.cache (blk parameter data message ρ 0) = none ∨ s.cache (blk parameter data message ρ 0) = some u0) ∧
  (s.cache (blk parameter data message ρ 1) = none ∨ s.cache (blk parameter data message ρ 1) = some u1) ∧
  ∀ ρ', ρ' ≠ ρ → RelatedAt parameter data message s s' ρ'

/-- What a completed signing call leaves behind. -/
def SignPost (Fail : Finset (Fin (2 ^ subtreeHeight))) (s s' : DebtState HashInput HashOutput Coordinate)
    (reveals : List Coordinate) (r : Option Signature) : Prop :=
  (r = none ∧ reveals = [] ∧ ∀ ρ, RelatedAt parameter data message s s' ρ) ∨
  ∃ ρ u0 u1, Selected parameter data message s s' ρ u0 u1 ∧
    (∀ c ∈ reveals, FtsOk (truncateMessageDigest u0 u1) c) ∧
    (∀ sig, r = some sig → sig.randomness = ρ) ∧
    (r = none → reveals = [] ∧ (s.cache (blk parameter data message ρ 0) = none →
      (Lifetime.localDigestView (truncateMessageDigest u0 u1)).1 ∈ Fail))

omit [Params] in
theorem blk_ne_blk {ρ ρ' : Randomness} {call call' : Fin 2} (h : ρ ≠ ρ' ∨ call ≠ call') :
    blk parameter data message ρ call ≠ blk parameter data message ρ' call' :=
  blk_ne_of_ne parameter data message ρ ρ' call call' h

/-- **Signing walk, support.** -/
theorem walk_post (hparse : ∀ ρ call, model.parse (blk parameter data message ρ call) = none)
    (Fail : Finset (Fin (2 ^ subtreeHeight)))
    (hfail : ∀ ρ digest budget (s1 : DebtState HashInput HashOutput Coordinate), Prepared initial s1 →
      ∀ out ∈ support (interp tg initial model (finishRest parameter data message ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ Fail) :
    ∀ attempts ρ budget (s : DebtState HashInput HashOutput Coordinate), Prepared initial s →
      ∀ out ∈ support (interp tg initial model (signCostSourceWalk parameter data message attempts ρ) budget s),
        ∀ r, out.1.1 = some r → SignPost parameter data message Fail s out.2 out.1.2.1 r := by
  intro attempts
  induction attempts with
  | zero =>
      intro ρ budget s _ out hout r hr
      change out ∈ support (interp tg initial model (pure none) budget s) at hout
      rw [interp_pure, support_pure, Set.mem_singleton_iff] at hout
      subst hout
      cases hr
      exact Or.inl ⟨rfl, rfl, fun ρ => RelatedAt.refl parameter data message s ρ⟩
  | succ attempts ih =>
      intro ρ budget s hprep out hout r hr
      rw [signCostSourceWalk_succ] at hout
      rw [interp_ordinary] at hout
      split_ifs at hout with h1
      · rw [ordinaryStep, hparse ρ 0] at hout
        simp only at hout
        rw [support_bind] at hout
        obtain ⟨res, hres, hout⟩ := Set.mem_iUnion₂.1 hout
        rw [support_map] at hout
        obtain ⟨o, ho, rfl⟩ := hout
        simp only at hr ⊢
        -- the state after the trial read
        have hstep : res.2.cache (blk parameter data message ρ 0) = some res.1 ∧
            (s.cache (blk parameter data message ρ 0) = none ∨
              s.cache (blk parameter data message ρ 0) = some res.1) ∧
            (∀ x, x ≠ blk parameter data message ρ 0 → res.2.cache x = s.cache x) ∧
            Prepared initial res.2 := by
          cases hc0 : s.cache (blk parameter data message ρ 0) with
          | some u =>
              rw [readOutside_cached _ s u hc0, support_pure, Set.mem_singleton_iff] at hres
              rw [hres]
              exact ⟨hc0, Or.inr rfl, fun _ _ => rfl, hprep⟩
          | none =>
              rw [readOutside_fresh _ s hc0, support_map] at hres
              obtain ⟨u, _, rfl⟩ := hres
              exact ⟨by simp [DebtState.store], Or.inl rfl, fun x hx => store_cache_ne s _ x hx u,
                prepared_store initial s hprep _ u hc0⟩
        obtain ⟨hb0, hb0s, hrest, hprep1⟩ := hstep
        by_cases hl : Landed parameter (blockIndex res.1)
        · rw [if_pos hl] at ho
          obtain ⟨u1, hf0, hf1, hf1s, hfother, hfrev, hfsig, hffail⟩ :=
            finish_post tg initial model parameter data message hparse Fail hfail ρ _ res.2 hprep1 res.1 hb0 o ho r hr
          refine Or.inr ⟨ρ, res.1, u1, ⟨hf0, hl, hf1, hb0s, ?_, fun ρ' hρ' => ?_⟩, hfrev, hfsig, fun hn => ?_⟩
          · rw [← hrest _ (blk_ne_blk parameter data message (Or.inr (by decide)))]
            exact hf1s
          · have h0 : o.2.cache (blk parameter data message ρ' 0) = s.cache (blk parameter data message ρ' 0) := by
              rw [hfother _ (msgInput_digestInput parameter data.root message ρ' 0)
                (blk_ne_blk parameter data message (Or.inl hρ')),
                hrest _ (blk_ne_blk parameter data message (Or.inl hρ'))]
            have h1' : o.2.cache (blk parameter data message ρ' 1) = s.cache (blk parameter data message ρ' 1) := by
              rw [hfother _ (msgInput_digestInput parameter data.root message ρ' 1)
                (blk_ne_blk parameter data message (Or.inl hρ')),
                hrest _ (blk_ne_blk parameter data message (Or.inl hρ'))]
            exact ⟨h1', Or.inl h0⟩
          · obtain ⟨hrv, hfl⟩ := hffail hn
            exact ⟨hrv, fun _ => hfl⟩
        · rw [if_neg hl] at ho
          -- every randomizer is related after the rejected trial
          have hrel1 : ∀ ρ', RelatedAt parameter data message s res.2 ρ' := by
            intro ρ'
            refine ⟨hrest _ (blk_ne_blk parameter data message (Or.inr (by decide))), ?_⟩
            by_cases hρ : ρ' = ρ
            · subst hρ
              rcases hb0s with hn | hs
              · exact Or.inr ⟨hn, res.1, hb0, hl⟩
              · exact Or.inl (hb0.trans hs.symm)
            · exact Or.inl (hrest _ (blk_ne_blk parameter data message (Or.inl hρ)))
          rcases ih _ _ res.2 hprep1 o ho r hr with ⟨hrn, hrv, hrel⟩ | ⟨ρs, u0, u1, hsel, hrev, hsig, hfl⟩
          · exact Or.inl ⟨hrn, hrv, fun ρ' => (hrel1 ρ').trans parameter data message (hrel ρ')⟩
          · obtain ⟨hs0, hland, hs1, hs0r, hs1r, hothers⟩ := hsel
            have hr1 := hrel1 ρs
            refine Or.inr ⟨ρs, u0, u1, ⟨hs0, hland, hs1, ?_, ?_, fun ρ' hρ' =>
              (hrel1 ρ').trans parameter data message (hothers ρ' hρ')⟩, hrev, hsig, fun hn => ?_⟩
            · rcases hr1.2 with he | ⟨hn', _⟩
              · rw [← he]; exact hs0r
              · exact Or.inl hn'
            · rw [← hr1.1]; exact hs1r
            · obtain ⟨hrv, hfl'⟩ := hfl hn
              refine ⟨hrv, fun hnone => hfl' ?_⟩
              rcases hr1.2 with he | ⟨_, u, hu, hnl⟩
              · rw [he]; exact hnone
              · rcases hs0r with h | h
                · exact h
                · rw [hu] at h
                  cases h
                  exact absurd hland hnl
      · rw [support_pure, Set.mem_singleton_iff] at hout
        rw [hout] at hr
        cases hr

/-- **Signing loop, support.** -/
theorem loop_post (hparse : ∀ ρ call, model.parse (blk parameter data message ρ call) = none)
    (Fail : Finset (Fin (2 ^ subtreeHeight)))
    (hfail : ∀ ρ digest budget (s1 : DebtState HashInput HashOutput Coordinate), Prepared initial s1 →
      ∀ out ∈ support (interp tg initial model (finishRest parameter data message ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ Fail) :
    ∀ attempts budget (s : DebtState HashInput HashOutput Coordinate), Prepared initial s →
      ∀ out ∈ support (interp tg initial model (signCostSourceLoop parameter data message attempts) budget s),
        ∀ r, out.1.1 = some r → SignPost parameter data message Fail s out.2 out.1.2.1 r := by
  intro attempts budget s hprep out hout r hr
  unfold signCostSourceLoop at hout
  rw [interp_liftProb_bind, support_bind] at hout
  obtain ⟨ρ, _, hout⟩ := Set.mem_iUnion₂.1 hout
  exact walk_post tg initial model parameter data message hparse Fail hfail attempts ρ budget s hprep out hout r hr

/-- The signing walk only queries message inputs of the signed message. -/
theorem avoids_walk :
    ∀ attempts ρ, Avoids (D := HashInput) (R := HashOutput) (ι := Coordinate)
      (fun x => IsMsgInput x ∧ ∀ ρ call, x ≠ blk parameter data message ρ call)
      (signCostSourceWalk parameter data message attempts ρ) := by
  intro attempts
  induction attempts with
  | zero => intro ρ; exact avoids_pure _ _
  | succ attempts ih =>
      intro ρ
      rw [signCostSourceWalk_succ]
      refine (avoids_query_bind _ _ _).2 ⟨fun bytes hb hx => ?_, fun first => ?_⟩
      · cases hb
        exact hx.2 ρ 0 rfl
      · split_ifs
        · rw [finishCostSource_eq]
          refine (avoids_query_bind _ _ _).2 ⟨fun bytes hb hx => ?_, fun a => ?_⟩
          · cases hb
            exact hx.2 ρ 0 rfl
          refine (avoids_query_bind _ _ _).2 ⟨fun bytes hb hx => ?_, fun b => ?_⟩
          · cases hb
            exact hx.2 ρ 1 rfl
          exact avoids_mono (fun x hx => hx.1) (avoids_finishRest parameter data message ρ _)
        · exact ih (ρ + 1)

/-- The signing loop only queries message inputs of the signed message. -/
theorem avoids_loop (attempts : ℕ) :
    Avoids (D := HashInput) (R := HashOutput) (ι := Coordinate)
      (fun x => IsMsgInput x ∧ ∀ ρ call, x ≠ blk parameter data message ρ call)
      (signCostSourceLoop parameter data message attempts) := by
  unfold signCostSourceLoop
  exact avoids_bind _ (avoids_liftProb _ _) fun ρ => avoids_walk parameter data message attempts ρ

end Loop

end SphincsFors.Security.GraphView
