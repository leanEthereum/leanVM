module

public import Common.MultiKey.World1

@[expose] public section

/-!
# The bad event: an input asked of both oracles

In the two-oracle run of the tagged game, an input is asked of the real oracle and of the private
one only if key `i` and some other key clash (`Clash`): some key-generation query of the other
key is a key-generation query of key `i` or publicly owned by key `i`, or some input is publicly
owned by both (`bad_imp_clash`). This needs four facts of the scheme (`Separation`): the signer
asks only inputs its public key owns or its key generation asked, the verifier only inputs its
public key owns, and an input of a key's key generation that another public key owns is owned by
its own. Key `i` is generated with the real oracle from an empty cache and the others with the
private oracle, independently, so each clash has probability at most the scheme's bound `ε` for a
fresh key against a fixed one (`prob_bad_le`: at most `(k - 1) ε` in all).
-/

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal
open HashSig.OverPermutation (sequenceFin)

namespace Common.SufCma.MultiKey

variable {Seed PK SK Req Resp F : Type}

/-! ## Where the two-oracle cache grows -/

/-- The cache `c'` extends `c` by entries satisfying `P` only. -/
def GrowsIn (P : Bool × List UInt8 → Prop) (c c' : TagSpec.QueryCache) : Prop :=
  ∀ t, (c' t).isSome → (c t).isSome ∨ P t

theorem GrowsIn.trans {P P' : Bool × List UInt8 → Prop} {c c₁ c₂ : TagSpec.QueryCache}
    (h₁ : GrowsIn P c c₁) (h₂ : GrowsIn P' c₁ c₂) : GrowsIn (fun t ↦ P t ∨ P' t) c c₂ := by
  intro t ht
  rcases h₂ t ht with h | h
  · rcases h₁ t h with h' | h'
    · exact .inl h'
    · exact .inr (.inl h')
  · exact .inr (.inr h)

theorem GrowsIn.mono {P P' : Bool × List UInt8 → Prop} {c c' : TagSpec.QueryCache}
    (h : GrowsIn P c c') (hP : ∀ t, P t → P' t) : GrowsIn P' c c' :=
  fun t ht ↦ (h t ht).imp id (hP t)

theorem growsIn_refl (P : Bool × List UInt8 → Prop) (c : TagSpec.QueryCache) : GrowsIn P c c :=
  fun _ h ↦ .inl h

/-- A run of the two-oracle world, from the cache `c`. -/
noncomputable abbrev run2 {α : Type} (X : OracleComp TSpec α) (c : TagSpec.QueryCache) :
    ProbComp (α × TagSpec.QueryCache) :=
  (simulateQ TagSpec.romImpl X).run c

theorem mem_support_run2_bind {α β : Type} {X : OracleComp TSpec α} {f : α → OracleComp TSpec β}
    {c : TagSpec.QueryCache} {z : β × TagSpec.QueryCache} (hz : z ∈ support (run2 (X >>= f) c)) :
    ∃ z₁ ∈ support (run2 X c), z ∈ support (run2 (f z₁.1) z₁.2) := by
  simp only [run2, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  exact hz

/-- One step of the two-oracle world at `t` grows the cache by `t` at most. -/
theorem growsIn_step (t : TSpec.Domain) (c : TagSpec.QueryCache)
    {z : TSpec.Range t × TagSpec.QueryCache} (hz : z ∈ support ((TagSpec.romImpl t).run c)) :
    GrowsIn (fun t' ↦ t = .inr t') c z.2 := by
  rcases t with n | t
  · rw [unifFwdImpl.snd_eq_of_mem_support_run n c hz]
    exact growsIn_refl _ c
  · intro t' ht'
    replace hz : z ∈ support (roStep t c) := by rw [← romImpl_inr_run]; exact hz
    unfold roStep at hz
    rcases hc : c t with _ | u
    · rw [hc] at hz
      simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hz
      obtain ⟨u, -, rfl⟩ := hz
      by_cases htt : t' = t
      · exact .inr (by rw [htt])
      · left
        rwa [QueryCache.cacheQuery_of_ne _ _ htt] at ht'
    · rw [hc] at hz
      simp only [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact .inl ht'

/-- A tagged query satisfies `P`; a coin always. -/
def TagOK (P : Bool × List UInt8 → Prop) : TSpec.Domain → Prop
  | .inl _ => True
  | .inr t => P t

/-- Every tagged query of `X`, on every path, satisfies `P` (coins unrestricted). -/
def TQueriesIn (P : Bool × List UInt8 → Prop) {α : Type} : OracleComp TSpec α → Prop
  | .pure _ => True
  | .liftBind t k => TagOK P t ∧ ∀ u, TQueriesIn P (k u)

section TQueriesIn

variable {P : Bool × List UInt8 → Prop} {α β : Type}

theorem tQueriesIn_query_bind (t : TSpec.Domain) (k : TSpec.Range t → OracleComp TSpec α) :
    TQueriesIn P (liftM (TSpec.query t) >>= k) ↔ TagOK P t ∧ ∀ u, TQueriesIn P (k u) :=
  Iff.rfl

theorem tQueriesIn_bind {X : OracleComp TSpec α} {f : α → OracleComp TSpec β}
    (hX : TQueriesIn P X) (hf : ∀ a, TQueriesIn P (f a)) : TQueriesIn P (X >>= f) := by
  induction X using OracleComp.inductionOn with
  | pure a => simpa using hf a
  | query_bind t k ih =>
    rw [bind_assoc, tQueriesIn_query_bind]
    exact ⟨hX.1, fun u ↦ ih u (hX.2 u)⟩

theorem tQueriesIn_map {X : OracleComp TSpec α} (f : α → β) (hX : TQueriesIn P X) :
    TQueriesIn P (f <$> X) := by
  rw [map_eq_bind_pure_comp]
  exact tQueriesIn_bind hX fun _ ↦ trivial

theorem tQueriesIn_mono {P' : Bool × List UInt8 → Prop} (hP : ∀ t, P t → P' t)
    {X : OracleComp TSpec α} (hX : TQueriesIn P X) : TQueriesIn P' X := by
  induction X using OracleComp.inductionOn with
  | pure a => trivial
  | query_bind t k ih =>
    rw [tQueriesIn_query_bind] at hX ⊢
    refine ⟨?_, fun u ↦ ih u (hX.2 u)⟩
    rcases t with n | t
    · trivial
    · exact hP t hX.1

/-- **The cache of a run grows only by its tagged queries.** -/
theorem growsIn_of_tQueriesIn {X : OracleComp TSpec α} (hX : TQueriesIn P X)
    (c : TagSpec.QueryCache) {z : α × TagSpec.QueryCache} (hz : z ∈ support (run2 X c)) :
    GrowsIn P c z.2 := by
  induction X using OracleComp.inductionOn generalizing c with
  | pure a =>
    simp only [run2, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz
    exact growsIn_refl _ c
  | query_bind t k ih =>
    rw [tQueriesIn_query_bind] at hX
    simp only [run2, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      mem_support_bind_iff] at hz
    obtain ⟨z₁, hz₁, hz⟩ := hz
    refine ((growsIn_step t c hz₁).trans (ih z₁.1 (hX.2 z₁.1) z₁.2 hz)).mono fun t' h ↦ ?_
    rcases h with h | h
    · subst h
      exact hX.1
    · exact h

theorem tQueriesIn_coinsT (p : ProbComp α) : TQueriesIn P (simulateQ coinsT p) := by
  induction p using OracleComp.inductionOn with
  | pure a => trivial
  | query_bind n k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query]
    exact tQueriesIn_bind ((tQueriesIn_query_bind (.inl n) pure).mpr ⟨trivial, fun _ ↦ trivial⟩
      |> fun h ↦ by simpa [coinsT] using h) ih

/-- A hash computation over the oracle tagged `b`, its queries in `Q`. -/
theorem tQueriesIn_tag {Q : List UInt8 → Prop} (b : Bool) (hb : ∀ x, Q x → P (b, x))
    (X : OracleComp SchemeHashSpec α) (hX : QueriesIn Q X) :
    TQueriesIn P (simulateQ (fun x ↦ liftM (TSpec.query (.inr (b, x)))) X) := by
  induction X using OracleComp.inductionOn with
  | pure a => trivial
  | query_bind x k ih =>
    rw [queriesIn_query_bind] at hX
    simp only [simulateQ_bind, simulateQ_spec_query]
    exact tQueriesIn_bind ((tQueriesIn_query_bind (.inr (b, x)) pure).mpr
      ⟨hb x hX.1, fun _ ↦ trivial⟩ |> fun h ↦ by simpa using h) fun u ↦ ih u (hX.2 u)

theorem queriesIn_univ (X : OracleComp SchemeHashSpec α) : QueriesIn (fun _ ↦ True) X := by
  induction X using OracleComp.inductionOn with
  | pure a => trivial
  | query_bind x k ih => exact (queriesIn_query_bind x k).mpr ⟨trivial, ih⟩

end TQueriesIn

theorem tQueriesIn_writer {ι : Type} {spec : OracleSpec ι} {L α : Type} [EmptyCollection L]
    [Append L] [LawfulAppend L] {P : Bool × List UInt8 → Prop}
    (f : QueryImpl spec (WriterT L (OracleComp TSpec))) (h : ∀ t, TQueriesIn P (f t).run)
    (X : OracleComp spec α) : TQueriesIn P (simulateQ f X).run := by
  induction X using OracleComp.inductionOn with
  | pure a => trivial
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, WriterT.run_bind']
    exact tQueriesIn_bind (h t) fun z ↦ tQueriesIn_map _ (ih z.1)

/-! ## The phases of the tagged game -/

/-- A tag's oracle has the hash's outputs. -/
theorem support_tag_subset {α : Type} (b : Bool) (X : OracleComp SchemeHashSpec α) :
    support (simulateQ (fun x ↦ (liftM (TSpec.query (.inr (b, x))) : OracleComp TSpec _)) X) ⊆
      support X := by
  induction X using OracleComp.inductionOn with
  | pure a => simp
  | query_bind x k ih =>
    intro a ha
    simp only [simulateQ_bind, simulateQ_spec_query, mem_support_bind_iff] at ha
    obtain ⟨u, -, hu⟩ := ha
    exact (mem_support_bind_iff _ _ _).2 ⟨u, mem_support_query _ u, ih u hu⟩

theorem fst_mem_support_run2 {α : Type} {X : OracleComp TSpec α} {c : TagSpec.QueryCache}
    {z : α × TagSpec.QueryCache} (hz : z ∈ support (run2 X c)) : z.1 ∈ support X :=
  support_simulateQ_run'_subset TagSpec.romImpl X c (by
    rw [StateT.run'_eq]; erw [support_map]; exact ⟨z, hz, rfl⟩)

/-- **A logged computation over a tag's oracle grows the cache by its log only.** -/
theorem growsIn_logged {α : Type} (b : Bool) (X : OracleComp SchemeHashSpec α)
    (c : TagSpec.QueryCache) {z : (α × List (List UInt8)) × TagSpec.QueryCache}
    (hz : z ∈ support (run2 (simulateQ (fun x ↦ (liftM (TSpec.query (.inr (b, x))) :
      OracleComp TSpec _)) (simulateQ logImpl X).run) c)) :
    GrowsIn (fun t ↦ t.1 = b ∧ t.2 ∈ z.1.2) c z.2 := by
  induction X using OracleComp.inductionOn generalizing c z with
  | pure a =>
    simp only [simulateQ_pure, WriterT.run_pure, run2, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz
    exact growsIn_refl _ c
  | query_bind x k ih =>
    have h0 : (logImpl x).run = (fun u ↦ (u, [x])) <$>
        (liftM (SchemeHashSpec.query x) : OracleComp SchemeHashSpec _) := by
      simp [logImpl, run_liftM_query_writer]
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, WriterT.run_bind', h0, bind_map_left, simulateQ_map] at hz
    obtain ⟨z₁, hz₁, hz⟩ := mem_support_run2_bind hz
    rw [run2, simulateQ_map, StateT.run_map, support_map] at hz
    obtain ⟨z₂, hz₂, rfl⟩ := hz
    rw [run2, simulateQ_spec_query] at hz₁
    dsimp only
    refine ((growsIn_step _ c hz₁).trans (ih z₁.1 z₁.2 hz₂)).mono fun t ht ↦ ?_
    rcases ht with ht | ⟨hb, ht⟩
    · cases ht
      exact ⟨rfl, by simp⟩
    · exact ⟨hb, by simp [ht]⟩

/-- Computations in sequence grow the cache by what each grows it by. -/
theorem growsIn_sequenceFin {γ : Type} (Q : γ → Bool × List UInt8 → Prop) :
    ∀ {n : ℕ} (cs : Fin n → OracleComp TSpec γ),
      (∀ j c {z : γ × TagSpec.QueryCache}, z ∈ support (run2 (cs j) c) → GrowsIn (Q z.1) c z.2) →
      ∀ c {z : (Fin n → γ) × TagSpec.QueryCache}, z ∈ support (run2 (sequenceFin cs) c) →
        GrowsIn (fun t ↦ ∃ j, Q (z.1 j) t) c z.2
  | 0, _, _, c, z, hz => by
    simp only [sequenceFin, run2, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz
    exact growsIn_refl _ c
  | n + 1, cs, h, c, z, hz => by
    simp only [sequenceFin] at hz
    obtain ⟨z₁, hz₁, hz⟩ := mem_support_run2_bind hz
    obtain ⟨z₂, hz₂, hz⟩ := mem_support_run2_bind hz
    simp only [run2, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz
    refine ((h 0 c hz₁).trans (growsIn_sequenceFin Q (fun j ↦ cs j.succ)
      (fun j ↦ h j.succ) z₁.2 hz₂)).mono fun t ht ↦ ?_
    rcases ht with ht | ⟨j, ht⟩
    · exact ⟨0, ht⟩
    · exact ⟨j.succ, ht⟩

variable (S : SchemeWithHash Seed PK SK Req Resp F) {k : ℕ}

/-- **The other keys grow the private oracle's cache by their key-generation logs only.** -/
theorem growsIn_setup (i : Fin k) (c : TagSpec.QueryCache)
    {z : (Fin k → Option (KeyRec PK SK)) × TagSpec.QueryCache}
    (hz : z ∈ support (run2 (setup S i) c)) :
    GrowsIn (fun t ↦ ∃ j zj, z.1 j = some zj ∧ t.1 = true ∧ t.2 ∈ zj.2) c z.2 := by
  refine (growsIn_sequenceFin (fun o t ↦ ∃ zj, o = some zj ∧ t.1 = true ∧ t.2 ∈ zj.2) _
    (fun j c' z' hz' ↦ ?_) c hz).mono fun t ⟨j, zj, h1, h2⟩ ↦ ⟨j, zj, h1, h2⟩
  split at hz'
  · simp only [run2, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz'
    subst hz'
    exact growsIn_refl _ c'
  · obtain ⟨z₁, hz₁, hz'⟩ := mem_support_run2_bind hz'
    rw [run2, simulateQ_map, StateT.run_map, support_map] at hz'
    obtain ⟨z₂, hz₂, rfl⟩ := hz'
    have g₁ := growsIn_of_tQueriesIn (tQueriesIn_coinsT (P := fun _ ↦ False) S.sample) c' hz₁
    have g₂ := growsIn_logged true (S.keygen z₁.1) z₁.2 hz₂
    refine (g₁.trans g₂).mono fun t ht ↦ ?_
    rcases ht with ht | ht
    · exact ht.elim
    · exact ⟨z₂.1, rfl, ht⟩

/-- A computation of the tagged oracles inside the reduction logs nothing. -/
theorem run_gameOraclesT_toTR (sk : SK) {α : Type} (X : OracleComp TSpec α) :
    (simulateQ (gameOraclesT S sk) (simulateQ (toTR (Req := Req) (Resp := Resp)) X)).run =
      (·, ∅) <$> X := by
  rw [← QueryImpl.simulateQ_compose,
    run_simulateQ_writer_of_run _ (fun u ↦ (liftM (TSpec.query u) : OracleComp TSpec _))
      (fun u ↦ by simp only [QueryImpl.apply_compose, toTR, simulateQ_spec_query]; rfl)]
  have h : simulateQ (fun u ↦ (liftM (TSpec.query u) : OracleComp TSpec _)) X = X :=
    simulateQ_ofLift_eq_self X
  rw [h]

variable (ownedPub : PK → List UInt8 → Prop) [∀ pk, DecidablePred (ownedPub pk)]

/-- **The reduction with its signing oracle**: the other keys, then the adversary's phase. -/
theorem run_gameOraclesT_reductionT (sk : SK) (i : Fin k)
    (A : (Fin k → PK) → OracleComp (World + (Fin k × Req →ₒ Resp)) (Fin k × F)) (pk : PK) :
    (simulateQ (gameOraclesT S sk) (reductionT S ownedPub i A pk)).run =
      setup S i >>= fun others ↦ (fun p ↦ ((p.1, others), p.2)) <$>
        (simulateQ (gameOraclesT S sk)
          (simulateQ (advImpl S ownedPub i pk others) (A (pksOf pk others)))).run := by
  simp only [reductionT, simulateQ_bind, simulateQ_pure, WriterT.run_bind',
    run_gameOraclesT_toTR, bind_map_left]
  refine bind_congr fun others ↦ ?_
  simp only [WriterT.run_pure, map_bind, map_pure, List.empty_eq, Prod.map_apply, id_eq,
    List.append_nil]
  rw [map_eq_bind_pure_comp]
  rfl

/-! ## The scheme's facts, and the clash -/

/-- `z` is a key record key generation can output. -/
def IsKey (z : KeyRec PK SK) : Prop := ∃ seed, z ∈ support (loggedKeygen S seed)

/-- **The facts of the scheme the reduction needs**, for a public ownership of inputs
`ownedPub` (in the deployed schemes: the input carries the key's public parameter where its
format puts it): the signer asks only inputs its public key owns or its key generation asked; the
verifier only inputs its public key owns; an input of a key's key generation that some public key
owns is owned by its own. -/
structure Separation : Prop where
  sign_queries : ∀ z, IsKey S z → ∀ r,
    QueriesIn (fun x ↦ ownedPub z.1.1 x ∨ x ∈ z.2) (S.sign z.1.2 r)
  verify_queries : ∀ pk f, QueriesIn (ownedPub pk) (S.verify pk f)
  keygen_owned : ∀ z, IsKey S z → ∀ x ∈ z.2, ∀ pk', ownedPub pk' x → ownedPub z.1.1 x

/-- **Key `za` clashes with key `zb`**: a key-generation query of `zb` is one of `za` or is
publicly owned by `za`, or some input is publicly owned by both. -/
def Clash (za zb : KeyRec PK SK) : Prop :=
  ∃ x, (x ∈ zb.2 ∧ (x ∈ za.2 ∨ ownedPub za.1.1 x)) ∨ (ownedPub za.1.1 x ∧ ownedPub zb.1.1 x)

/-- The adversary's phase asks the real oracle only inputs owned by key `i` or not routed to the
private one, and the private oracle only inputs routed there or of another key. -/
def AdvTag (zi : KeyRec PK SK) (others : Fin k → Option (KeyRec PK SK))
    (t : Bool × List UInt8) : Prop :=
  (t.1 = false → t.2 ∈ zi.2 ∨ ownedPub zi.1.1 t.2 ∨ groute ownedPub zi.1.1 others t.2 = false) ∧
  (t.1 = true → groute ownedPub zi.1.1 others t.2 = true ∨
    ∃ j z, others j = some z ∧ (ownedPub z.1.1 t.2 ∨ t.2 ∈ z.2))

theorem tQueriesIn_query {P : Bool × List UInt8 → Prop} {t : TSpec.Domain} (h : TagOK P t) :
    TQueriesIn P (liftM (TSpec.query t) : OracleComp TSpec (TSpec.Range t)) := by
  have := (tQueriesIn_query_bind (P := P) t pure).mpr ⟨h, fun _ ↦ trivial⟩
  simpa using this

variable {S ownedPub}

theorem tQueriesIn_advPhase (sep : Separation S ownedPub) (i : Fin k) (zi : KeyRec PK SK)
    (hzi : IsKey S zi) (others : Fin k → Option (KeyRec PK SK))
    (hothers : ∀ j z, others j = some z → IsKey S z) {α : Type}
    (X : OracleComp (World + (Fin k × Req →ₒ Resp)) α) :
    TQueriesIn (AdvTag ownedPub zi others)
      (simulateQ (gameOraclesT S zi.1.2) (simulateQ (advImpl S ownedPub i zi.1.1 others) X)).run := by
  rw [← QueryImpl.simulateQ_compose]
  refine tQueriesIn_writer _ (fun t ↦ ?_) X
  simp only [QueryImpl.apply_compose]
  have hsignI : ∀ r, TQueriesIn (AdvTag ownedPub zi others)
      ((simulateQ (gameOraclesT S zi.1.2)
        (liftM ((TSpec + (Req →ₒ Resp)).query (.inr r)) : OracleComp _ Resp)).run) := by
    intro r
    have h2 : ((gameOraclesT S zi.1.2) (.inr r)).run = (fun u ↦ (u, [⟨r, u⟩])) <$>
        simulateQ tagF (S.sign zi.1.2 r) := by
      simp [gameOraclesT, signT]
    rw [simulateQ_spec_query, h2]
    exact tQueriesIn_map _ (tQueriesIn_tag false (Q := fun x ↦ ownedPub zi.1.1 x ∨ x ∈ zi.2)
      (fun x hx ↦ ⟨fun _ ↦ hx.elim (fun h ↦ .inr (.inl h)) (fun h ↦ .inl h),
        fun h ↦ (by cases h)⟩) _ (sep.sign_queries zi hzi r))
  rcases t with (n | x) | ⟨j, r⟩
  · simp only [advImpl, simulateQ_spec_query]
    exact tQueriesIn_map _ (tQueriesIn_query trivial)
  · simp only [advImpl, simulateQ_spec_query]
    refine tQueriesIn_map _ (tQueriesIn_query ⟨fun h ↦ ?_, fun h ↦ ?_⟩)
    · exact .inr (.inr h)
    · exact .inl h
  · simp only [advImpl]
    split
    · exact hsignI r
    · split
      · rename_i z hz
        rw [run_gameOraclesT_toTR]
        refine tQueriesIn_map _ (tQueriesIn_tag true (Q := fun x ↦ ownedPub z.1.1 x ∨ x ∈ z.2)
          (fun x hx ↦ ⟨fun h ↦ (by cases h), fun _ ↦ .inr ⟨j, z, hz, hx⟩⟩) _
          (sep.sign_queries z (hothers j z hz) r))
      · exact hsignI r

theorem isKey_of_run2 {b : Bool} {s : Seed} {c : TagSpec.QueryCache}
    {z : KeyRec PK SK × TagSpec.QueryCache}
    (hz : z ∈ support (run2 (simulateQ (fun x ↦ (liftM (TSpec.query (.inr (b, x))) :
      OracleComp TSpec _)) (loggedKeygen S s)) c)) : IsKey S z.1 :=
  ⟨s, support_tag_subset b _ (fst_mem_support_run2 hz)⟩

theorem setup_support (i : Fin k) {others : Fin k → Option (KeyRec PK SK)}
    (h : others ∈ support (setup S i)) :
    others i = none ∧ ∀ j z, others j = some z → IsKey S z := by
  refine ⟨by simpa using mem_support_sequenceFin _ h i, fun j z hz ↦ ?_⟩
  have hj := mem_support_sequenceFin _ h j
  rw [hz] at hj
  split at hj
  · simp at hj
  · simp only [support_bind, support_map, Set.mem_iUnion, Set.mem_image] at hj
    obtain ⟨s, -, z', hz', hzz⟩ := hj
    cases hzz
    exact ⟨s, support_tag_subset true _ hz'⟩

end Common.SufCma.MultiKey
