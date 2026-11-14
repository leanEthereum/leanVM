module

public import LeanDa.RpmScheme
public import LeanDa.RpmGames
public import LeanDa.Security
public import LeanDa.Defs
public import Common.Linear
public import LeanDa.WithHash

@[expose] public section

/-!
# LeanDA in the random-permutation model

Position binding and code binding of LeanDA (`LeanDa.Security`, Benedikt Wagner's framework
`PqDas`) with Keccak-f[1600] idealized as a uniformly random permutation `π` (`Common`): the hash
`H` is Keccak-256, the sponge over `π`, and the membership challenges are the deployed duplex over
`π` (`membershipChallengeWith`), while the adversary queries Keccak-256, `π` and `π⁻¹`. The
verifier (`verifyRpm`) is the scheme's: the challenges of the root, the argument's verification,
and the opening's climb hashed with Keccak-256 (`verifyCellWith`). Its permutation calls in the
challenges' duplex follow the duplex discipline, so the two-oracle transfer
(`keccak256_transfer2`) moves both games to the two-oracle random-oracle model (`H` a random oracle,
`F` an independent random function) within `Q² / 2^508` for `Q` permutation calls.

* **Position binding**: there, a win is a collision of `H` among the cached answers, at most
  `Q² / 2^256` (`prob_hCollision_le`); the end theorem (`leanDa_positionBinding_rpm`,
  `LeanDa.RpmArg`) runs the argument's verification with the adversary.
* **Code binding** (`leanDa_codeBinding_rpm`, for an oracle-free argument): the RPM probability is
  within `Q² / 2^508` of the two-oracle ROM one against the simulated adversary, the first step of
  Wagner's forking route and of the straight-line proof (`LeanDa.RpmCodeBinding`,
  `LeanDa.RpmArg`).

This module is part of the instantiation of Benedikt Wagner's framework for erasure code
commitments (`PqDas`, ported from https://github.com/b-wagn/fv-pq-da) with LeanDA.
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec Common PqDas MeasureTheory
open scoped ENNReal

namespace LeanDa

/-! ## Hashing in the two-oracle random-oracle model -/

/-- The cache of the two-oracle random oracle. -/
abbrev Cache2 := (hfSpec (List UInt8) DigestBytes KState).QueryCache

/-- The hash function a cache gives: its cached answers, `default` elsewhere. -/
def hOf (c : Cache2) (a : List UInt8) : Common.DigestBytes := (c (.inl a)).getD default

theorem hOf_of_le {c c' : Cache2} (h : c ≤ c') {a : List UInt8} {d : Common.DigestBytes}
    (ha : c (.inl a) = some d) : hOf c' a = d := by
  simp [hOf, h ha]

/-- An `H` query caches its answer. -/
theorem mem_support_run_hR (a : List UInt8) (c : Cache2) {z : Common.DigestBytes × Cache2}
    (hz : z ∈ support ((simulateQ (hfSpec (List UInt8) DigestBytes KState).romImpl (hR a)).run c)) :
    c ≤ z.2 ∧ z.2 (.inl a) = some z.1 := by
  rw [hR, hQuery, run_hq] at hz
  exact le_of_mem_support_roStep _ c hz

/-- The inputs a climb hashes. -/
def walkInputs (H : List UInt8 → Common.DigestBytes) : ℕ → Common.DigestBytes → List Common.DigestBytes → List (List UInt8)
  | _, _, [] => []
  | idx, node, s :: rest =>
    (if idx % 2 = 0 then pairBytes node s else pairBytes s node) ::
      walkInputs H (idx / 2) (H (if idx % 2 = 0 then pairBytes node s else pairBytes s node)) rest

theorem walk_cons (H : List UInt8 → Common.DigestBytes) (idx : ℕ) (node s : Common.DigestBytes) (rest : List Common.DigestBytes) :
    walk H idx node (s :: rest) =
      walk H (idx / 2) (H (if idx % 2 = 0 then pairBytes node s else pairBytes s node)) rest := by
  rw [walk, apply_ite H]

/-- The inputs of an opening's climb are the cell's bytes and the climb's. -/
theorem hashInputs_eq (H : List UInt8 → Common.DigestBytes) (idx : ℕ) (a : List UInt8)
    (path : List Common.DigestBytes) :
    hashInputs H idx a path = a :: walkInputs H idx (H a) path := by
  induction path generalizing idx a with
  | nil => rfl
  | cons s rest ih =>
    rw [hashInputs, ih, walkInputs]

/-- **A climb's run**: the cache grows, and in every later cache the climb's result and inputs
are those of the cache's hash function, its inputs cached. -/
theorem run_walkM (idx : ℕ) (node : Common.DigestBytes) (path : List Common.DigestBytes) (c : Cache2)
    {z : Common.DigestBytes × Cache2}
    (hz : z ∈ support ((simulateQ (hfSpec (List UInt8) DigestBytes KState).romImpl
      (walkMWithHash hR idx node path)).run c)) :
    c ≤ z.2 ∧ ∀ c', z.2 ≤ c' → z.1 = walk (hOf c') idx node path ∧
      ∀ a ∈ walkInputs (hOf c') idx node path, c' (.inl a) ≠ none := by
  induction path generalizing idx node c with
  | nil =>
    simp only [walkMWithHash, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨le_rfl, fun c' _ ↦ ⟨rfl, by simp [walkInputs]⟩⟩
  | cons s rest ih =>
    simp only [walkMWithHash, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨w, hw, hz⟩ := hz
    obtain ⟨hcw, hwa⟩ := mem_support_run_hR _ c hw
    obtain ⟨hwz, hrest⟩ := ih (idx / 2) w.1 w.2 hz
    refine ⟨hcw.trans hwz, fun c' hc' ↦ ?_⟩
    have hval := hOf_of_le (hwz.trans hc') hwa
    obtain ⟨h1, h2⟩ := hrest c' hc'
    refine ⟨?_, ?_⟩
    · rw [walk_cons, hval]; exact h1
    · intro a ha
      rw [walkInputs, hval] at ha
      rcases List.mem_cons.mp ha with rfl | ha
      · rw [(hwz.trans hc') hwa]; simp
      · exact h2 a ha

/-- **An opening's verification run**: the cache grows, and in every later cache the result is
`verifyCell` of the cache's hash function, the opening's hash inputs cached. -/
theorem run_verifyCellM (r : ℕ) (com : Common.DigestBytes) (p : Fin (r * 128)) (x : Cell) (τ : CellOpening)
    (c : Cache2) {z : Bool × Cache2}
    (hz : z ∈ support ((simulateQ (hfSpec (List UInt8) DigestBytes KState).romImpl
      (verifyCellMWithHash hR r com p x τ)).run c)) :
    c ≤ z.2 ∧ ∀ c', z.2 ≤ c' → z.1 = verifyCell (hOf c') r com p x τ ∧
      ∀ a ∈ hashInputs (hOf c') p (cellBytes x) τ.path, c' (.inl a) ≠ none := by
  simp only [verifyCellMWithHash, simulateQ_bind, StateT.run_bind, mem_support_bind_iff,
    simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := hz
  obtain ⟨hc1, hd⟩ := mem_support_run_hR _ c hw₁
  obtain ⟨hc2, hwalk⟩ := run_walkM _ _ _ _ hw₂
  refine ⟨hc1.trans hc2, fun c' hc' ↦ ?_⟩
  obtain ⟨hw, hin⟩ := hwalk c' hc'
  have hval1 := hOf_of_le (hc2.trans hc') hd
  refine ⟨?_, ?_⟩
  · simp only [verifyCell, cellDigestWithHash, hval1, ← hw]
  · intro a ha
    rw [hashInputs_eq, hval1] at ha
    rcases List.mem_cons.mp ha with rfl | ha
    · rw [(hc2.trans hc') hd]; simp
    · exact hin a ha

/-- `findCollision` returns inputs of its two lists, unless it returns two equal ones. -/
theorem findCollision_mem (H : List UInt8 → Common.DigestBytes) (l₁ l₂ : List (List UInt8))
    (h : (findCollision H l₁ l₂).1 ≠ (findCollision H l₁ l₂).2) :
    (findCollision H l₁ l₂).1 ∈ l₁ ∧ (findCollision H l₁ l₂).2 ∈ l₂ := by
  induction l₁ generalizing l₂ with
  | nil => simp [findCollision] at h
  | cons a as ih =>
    cases l₂ with
    | nil => simp [findCollision] at h
    | cons b bs =>
      simp only [findCollision] at h ⊢
      split_ifs at h ⊢ with hab
      · simp
      · obtain ⟨h1, h2⟩ := ih bs h
        exact ⟨List.mem_cons_of_mem _ h1, List.mem_cons_of_mem _ h2⟩

/-- A collision of `H` in a cache: two different inputs with the same cached answer. -/
def HCollision (c : Cache2) : Prop :=
  ∃ a b, a ≠ b ∧ c (.inl a) ≠ none ∧ c (.inl a) = c (.inl b)

/-! ## The games -/

theorem permCalls2_eq :
    permCalls2 = queryCost2 (Dg := DigestBytes) (St := KState) keccakPadding := by
  funext t
  rcases t with n | m | q
  · rfl
  · exact (keccakPad_length m).symm
  · rfl

section Games

variable (r : ℕ) {Crs Proof : Type} {rel : Unit × Common.DigestBytes × MembershipChallenge → (Fin (r * 128) → Cell) → Bool}
  (ps : Nark (Unit × Common.DigestBytes × MembershipChallenge) (Fin (r * 128) → Cell) Crs
      Proof rel)

/-- **A verification's run**: the cache grows, and an accepting verification makes the opening
verify for the hash function of every later cache, its hash inputs cached. -/
theorem run_verifyRpm (crs : Crs) (com : Common.DigestBytes × Proof) (p : Fin (r * 128)) (x : Cell)
    (τ : CellOpening) (c : Cache2) {z : Bool × Cache2}
    (hz : z ∈ support ((simulateQ (hfSpec (List UInt8) DigestBytes KState).romImpl
      (verifyRpm hR pR r ps crs com p x τ)).run c)) :
    c ≤ z.2 ∧ (z.1 = true → ∀ c', z.2 ≤ c' → verifyCell (hOf c') r com.1 p x τ = true ∧
      ∀ a ∈ hashInputs (hOf c') p (cellBytes x) τ.path, c' (.inl a) ≠ none) := by
  simp only [verifyRpm, simulateQ_bind, StateT.run_bind, mem_support_bind_iff,
    simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := hz
  have hc1 := le_of_mem_support_run _ c hw₁
  obtain ⟨hc2, hv⟩ := run_verifyCellM r com.1 p x τ _ hw₂
  refine ⟨hc1.trans hc2, fun hwin c' hc' ↦ ?_⟩
  obtain ⟨h1, h2⟩ := hv c' hc'
  simp only [Bool.and_eq_true] at hwin
  exact ⟨h1 ▸ hwin.2, h2⟩

/-- A cached answer is the cache's hash. -/
theorem cache_eq_hOf {c : Cache2} {a : List UInt8} (h : c (.inl a) ≠ none) :
    c (.inl a) = some (hOf c a) := by
  rcases hc : c (.inl a) with _ | d
  · exact absurd hc h
  · simp [hOf, hc]

/-- **A win of the position-binding game is a collision of `H` in the final cache.** -/
theorem posBindingPost_win (crs : Crs)
    (out : (Common.DigestBytes × Proof) × Fin (r * 128) × Cell × CellOpening × Cell × CellOpening) (c : Cache2)
    {z : Bool × Cache2}
    (hz : z ∈ support ((simulateQ (hfSpec (List UInt8) DigestBytes KState).romImpl
      (posBindingPost r ps crs out)).run c)) (hwin : z.1 = true) : HCollision z.2 := by
  obtain ⟨com, p, x, τ, x', τ'⟩ := out
  simp only [posBindingPost, simulateQ_bind, StateT.run_bind, mem_support_bind_iff,
    simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := hz
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hwin
  obtain ⟨⟨hx, hb⟩, hb'⟩ := hwin
  obtain ⟨hc2, hv2⟩ := run_verifyRpm r ps crs com p x' τ' _ hw₂
  obtain ⟨-, hv1⟩ := run_verifyRpm r ps crs com p x τ _ hw₁
  obtain ⟨hτ, hin⟩ := hv1 hb w₂.2 hc2
  obtain ⟨hτ', hin'⟩ := hv2 hb' w₂.2 le_rfl
  obtain ⟨hne, heq⟩ := openingsCollision_spec (hOf w₂.2) hx hτ hτ'
  simp only [openingsCollision] at hne heq
  obtain ⟨ha, hb⟩ := findCollision_mem _ _ _ hne
  show HCollision w₂.2
  have hca := hin _ ha
  have hcb := hin' _ hb
  exact ⟨_, _, hne, hca, by rw [cache_eq_hOf hca, cache_eq_hOf hcb, heq]⟩

/-! ### The duplex discipline of the verifier -/

theorem duplexP_walkM (idx : ℕ) (node : Common.DigestBytes) (path : List Common.DigestBytes) (hist : List KState) :
    DuplexP (fun _ _ ↦ True) (walkMWithHash hR idx node path) hist := by
  induction path generalizing idx node with
  | nil => exact duplexP_pure trivial
  | cons s rest ih => exact duplexP_hR_bind _ _ hist fun d ↦ ih _ _

theorem duplexP_verifyCellM (com : Common.DigestBytes) (p : Fin (r * 128)) (x : Cell) (τ :
    CellOpening)
    (hist : List KState) : DuplexP (fun _ _ ↦ True) (verifyCellMWithHash hR r com p x τ) hist :=
  duplexP_hR_bind _ _ hist fun _ ↦ duplexP_bind (duplexP_walkM _ _ _ hist) fun _ _ _ ↦
    duplexP_pure trivial

theorem duplexP_verifyRpm (crs : Crs) (com : Common.DigestBytes × Proof) (p : Fin (r * 128)) (x : Cell)
    (τ : CellOpening) (hist : List KState) :
    DuplexP (fun _ _ ↦ True) (verifyRpm hR pR r ps crs com p x τ) hist :=
  duplexP_bind (duplexP_membershipChallengeVecR com.1 hist) fun _ hist' _ ↦
    duplexP_bind (duplexP_verifyCellM r com.1 p x τ hist') fun _ _ _ ↦ duplexP_pure trivial

/-- **The position-binding verifier follows the duplex discipline.** -/
theorem duplex_posBindingPost (crs : Crs)
    (out : (Common.DigestBytes × Proof) × Fin (r * 128) × Cell × CellOpening × Cell × CellOpening) :
    Duplex KState.zero keccakNF (posBindingPost r ps crs out) [] :=
  duplex_of_duplexP (Q := fun _ _ ↦ True) <|
    duplexP_bind (duplexP_verifyRpm r ps crs _ _ _ _ []) fun _ hist _ ↦
      duplexP_bind (duplexP_verifyRpm r ps crs _ _ _ _ hist) fun _ _ _ ↦ duplexP_pure trivial

end Games

/-! ## Hash calls in the two-oracle model -/

/-- Calls of `H` in the two-oracle random-oracle model, one each. -/
def hCalls : Rom2.Domain → ℕ
  | .inr (.inl _) => 1
  | _ => 0

/-- **Each step of the shadow world makes at most one `H` call**, none for a coin or a direct
call. -/
theorem isWeightBound_shadowImpl (t : (dSpec2 (List UInt8) DigestBytes KState).Domain)
    (s : SimState DigestBytes KRest KCap) :
    QueryCostAtMost ((shadowImpl keccakPadding t).run s) hCalls
      (queryCost2 (Dg := DigestBytes) keccakPadding t) := by
  have hu : ∀ {β : Type} (p : ProbComp β), QueryCostAtMost (liftM p : OracleComp Rom2 β) hCalls 0 :=
    fun p ↦ isWeightBound_liftM_probComp hCalls (fun _ ↦ rfl) p
  have hF : ∀ x : KState, QueryCostAtMost (fQuery (Msg := List UInt8) (Dg := DigestBytes) x) hCalls 0 :=
    fun x ↦ isWeightBound_query hCalls (.inr (.inr x))
  have hH : ∀ a : List UInt8, QueryCostAtMost (hR a) hCalls 1 :=
    fun a ↦ isWeightBound_query hCalls (.inr (.inl a))
  rcases t with n | m | q | x
  · simp only [shadowImpl, StateT.run_monadLift, monadLift_self]
    exact (hu _).bind fun _ ↦ isWeightBound_pure _ _ 0
  · simp only [shadowImpl, StateT.run_monadLift, monadLift_self]
    refine ((hH m).bind fun _ ↦ isWeightBound_pure _ _ 0).mono ?_
    have := keccakPadding.pad_ne_nil m
    simp only [queryCost2]
    exact List.length_pos_iff.mpr this
  · cases q with
    | forward x =>
      simp only [shadowImpl, simulator2, StateT.run_mk]
      split
      · trivial
      · split
        · refine (QueryCostAtMost.bind (b := 0) ?_ fun _ ↦ isWeightBound_pure _ _ 0)
          unfold rootedAnswer2
          split
          · exact ((hH _).bind fun _ ↦ (hu _).bind fun _ ↦ isWeightBound_pure _ _ 0)
          · exact (hF _).mono (Nat.zero_le _)
        · exact ((hF _).bind fun _ ↦ isWeightBound_pure _ _ 0).mono (Nat.zero_le _)
    | inverse y =>
      simp only [shadowImpl, simulator2, StateT.run_mk]
      split
      · trivial
      · exact ((hu _).bind fun _ ↦ isWeightBound_pure _ _ 0).mono (Nat.zero_le _)
  · simp only [shadowImpl, StateT.run_mk]
    exact ((hF _).bind fun _ ↦ isWeightBound_pure _ _ 0).mono (Nat.zero_le _)

/-! ## Collisions of `H` in the two-oracle model -/

/-- The inputs of `H` a cache holds. -/
def hDom (c : Cache2) : Set (List UInt8) := {a | c (.inl a) ≠ none}

theorem card_digest : Fintype.card Common.DigestBytes = 2 ^ 256 := by
  rw [card_vector_uInt8]; norm_num

/-- The caches of one step of the two-oracle random oracle. -/
theorem romImpl2_step (t : Rom2.Domain) (c : Cache2) {z} (hz : z ∈ support
    (((hfSpec (List UInt8) DigestBytes KState).romImpl t).run c)) :
    z.2 = c ∨ (∃ x u, z.2 = c.cacheQuery (.inr x) u) ∨
      (∃ a u, t = .inr (.inl a) ∧ c (.inl a) = none ∧ z.2 = c.cacheQuery (.inl a) u) := by
  rcases t with n | t
  · rw [roSim.run_apply_inl] at hz
    simp only [support_map, Set.mem_image] at hz
    obtain ⟨_, -, rfl⟩ := hz
    exact Or.inl rfl
  · rw [romImpl_inr_run] at hz
    rcases h : c t with _ | v
    · rw [roStep_of_none h] at hz
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
      obtain ⟨u, -, rfl⟩ := hz
      rcases t with a | x
      · exact Or.inr (Or.inr ⟨a, u, rfl, h, rfl⟩)
      · exact Or.inr (Or.inl ⟨x, u, rfl⟩)
    · rw [roStep_of_some h] at hz
      simp only [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact Or.inl rfl

theorem cacheQuery_inr_inl (c : Cache2) (x : KState) (u : KState) (a : List UInt8) :
    (c.cacheQuery (.inr x) u) (.inl a) = c (.inl a) :=
  QueryCache.cacheQuery_of_ne _ _ (by simp)

theorem cacheQuery_inl_inl (c : Cache2) (a b : List UInt8) (u : Common.DigestBytes) :
    (c.cacheQuery (.inl a) u) (.inl b) = if b = a then some u else c (.inl b) := by
  by_cases h : b = a
  · subst h; simp
  · rw [QueryCache.cacheQuery_of_ne _ _ (by simpa using h)]
    simp [h]

/-- **The birthday bound for `H`**: a computation making at most `Q` calls of `H` in the
two-oracle random-oracle model ends with a collision of `H` in its cache with probability at most
`Q · Q / 2^256`. -/
theorem prob_hCollision_le {α : Type} (X : OracleComp Rom2 α) (Q : ℕ)
    (hX : QueryCostAtMost X hCalls Q) :
    Pr{let z ← (simulateQ (hfSpec (List UInt8) DigestBytes KState).romImpl X).run ∅}[HCollision z.2] ≤
      Q * ((Q : ℝ≥0∞) / 2 ^ 256) := by
  classical
  have h := prEvent_run_bad_le (hfSpec (List UInt8) DigestBytes KState).romImpl HCollision
    (fun c ↦ (hDom c).Finite) hCalls (fun c ↦ (hDom c).ncard) Q ((Q : ℝ≥0∞) / 2 ^ 256)
    ?_ ?_ ?_ X Q hX ∅ (by simp [hDom]) (by simp [hDom])
  · refine h.trans (le_of_eq ?_)
    have : ¬ HCollision (∅ : Cache2) := fun ⟨a, _, _, ha, _⟩ ↦ ha rfl
    simp [this]
  · -- the cache's inputs of `H` stay finite
    intro t c hc z hz
    rcases romImpl2_step t c hz with h | ⟨x, u, h⟩ | ⟨a, u, -, -, h⟩
    · rw [h]; exact hc
    · rw [h]; simpa [hDom, cacheQuery_inr_inl] using hc
    · rw [h]
      refine (hc.insert a).subset fun b hb ↦ ?_
      simp only [hDom, Set.mem_ofPred_eq, cacheQuery_inl_inl] at hb
      by_cases hba : b = a
      · exact Or.inl hba
      · exact Or.inr (by simpa [hDom, hba] using hb)
  · -- one step adds at most one input of `H`, and only an `H` call adds one
    intro t c hc z hz
    rcases romImpl2_step t c hz with h | ⟨x, u, h⟩ | ⟨a, u, rfl, -, h⟩
    · rw [h]; omega
    · rw [h]; simp [hDom]
    · rw [h]
      have : hDom (c.cacheQuery (.inl a) u) = insert a (hDom c) := by
        ext b
        by_cases hba : b = a
        · subst hba; simp [hDom]
        · simp [hDom, cacheQuery_inl_inl, hba]
      rw [this]
      exact (Set.ncard_insert_le a _).trans (by simp [hCalls])
  · -- a fresh `H` answer collides with one of the cached ones with probability at most `Q / 2^256`
    intro t c hc hbad hN
    have hkeep : ∀ c' : Cache2, (∀ b, c' (.inl b) = c (.inl b)) → ¬ HCollision c' := by
      rintro c' hc' ⟨a, b, hab, ha, he⟩
      exact hbad ⟨a, b, hab, by rwa [← hc'], by rwa [← hc', ← hc']⟩
    rcases t with n | a | x
    · refine le_of_eq_of_le (prEvent_eq_zero_of_forall_mem_support _ _ fun z hz ↦ ?_) zero_le
      rcases romImpl2_step _ c hz with h | ⟨x, u, h⟩ | ⟨a, u, h, -, -⟩
      · exact hkeep _ fun b ↦ by rw [h]
      · exact hkeep _ fun b ↦ by rw [h, cacheQuery_inr_inl]
      · cases h
    · rw [romImpl_inr_run]
      rcases h : c (.inl a) with _ | v
      · rw [roStep_of_none h, bind_pure_comp, prEvent_map]
        let V : Finset Common.DigestBytes := hc.toFinset.image (hOf c)
        have hmem : ∀ u : Common.DigestBytes, HCollision (c.cacheQuery (.inl a) u) → u ∈ V := by
          rintro u ⟨a₁, b₁, hne, h₁, he⟩
          simp only [cacheQuery_inl_inl] at h₁ he
          by_cases ha₁ : a₁ = a
          · subst ha₁
            have hb₁ : b₁ ≠ a₁ := Ne.symm hne
            simp only [hb₁, ↓reduceIte] at he
            refine Finset.mem_image.mpr ⟨b₁, hc.mem_toFinset.mpr (by simp [hDom, ← he]), ?_⟩
            simp [hOf, ← he]
          · by_cases hb₁ : b₁ = a
            · subst hb₁
              simp only [ha₁, ↓reduceIte] at he h₁
              refine Finset.mem_image.mpr ⟨a₁, hc.mem_toFinset.mpr (by simp [hDom, he]), ?_⟩
              simp [hOf, he]
            · simp only [ha₁, hb₁, ↓reduceIte] at h₁ he
              exact absurd ⟨a₁, b₁, hne, h₁, he⟩ hbad
        have hV : (V.card : ℝ≥0∞) ≤ Q := by
          have h1 : V.card ≤ hc.toFinset.card := Finset.card_image_le
          rw [← Set.ncard_eq_toFinset_card _ hc] at h1
          have h2 : (hDom c).ncard + 1 ≤ Q := by simpa [hCalls] using hN
          exact_mod_cast (h1.trans (by omega))
        calc Pr{let x ← ($ᵗ Common.DigestBytes : ProbComp Common.DigestBytes)}[HCollision (c.cacheQuery (.inl a) x)]
            ≤ Pr{let x ← ($ᵗ Common.DigestBytes : ProbComp Common.DigestBytes)}[x ∈ V] :=
              prEvent_mono _ _ _ fun u hu ↦ hmem u hu
          _ = V.card / 2 ^ 256 := by
              rw [SampleableType.prEvent_uniformSample, card_digest, Finset.filter_mem_eq_inter,
                Finset.univ_inter]
              norm_num
          _ ≤ hCalls (.inr (.inl a)) * ((Q : ℝ≥0∞) / 2 ^ 256) := by
              simp only [hCalls, Nat.cast_one, one_mul]
              gcongr
      · rw [roStep_of_some h]
        simp only [prEvent_pure]
        simp [hbad]
    · refine le_of_eq_of_le (prEvent_eq_zero_of_forall_mem_support _ _ fun z hz ↦ ?_) zero_le
      rcases romImpl2_step _ c hz with h | ⟨x, u, h⟩ | ⟨a, u, h, -, -⟩
      · exact hkeep _ fun b ↦ by rw [h]
      · exact hkeep _ fun b ↦ by rw [h, cacheQuery_inr_inl]
      · cases h

/-! ## Code binding -/

section CodeBinding

variable (r : ℕ) {Crs Proof : Type} {rel : Unit × Common.DigestBytes × MembershipChallenge → (Fin (r * 128) → Cell) → Bool}
  (ps : Nark (Unit × Common.DigestBytes × MembershipChallenge) (Fin (r * 128) → Cell) Crs
      Proof rel)

/-- **The code-binding game in the two-oracle random-oracle model**: `H` a random oracle, the
challenges' sponge over an independent random function `F`, against the ROM adversary
`advS2 A` (the RPM adversary with its permutation queries answered by the simulator, which
queries `H` and `F`). -/
noncomputable def codeBindingExpRom2 (A : CodeBindingAdvB r Crs Proof) : ProbComp Bool :=
  romRun2 (simulateQ (hInF (E := KRest) (C := KCap)) (liftM ps.setup) >>= fun crs ↦
    advS2 keccakPadding KState.zero (A ((), crs)) >>= fun out ↦ codeBindingPost r ps crs out)

theorem duplexP_mapM {β γ : Type} (f : β → OracleComp Rom2 γ)
    (hf : ∀ b hist, DuplexP (fun _ _ ↦ True) (f b) hist) (l : List β) (hist : List KState) :
    DuplexP (fun _ _ ↦ True) (l.mapM f) hist := by
  induction l generalizing hist with
  | nil => exact duplexP_pure trivial
  | cons b l ih =>
    rw [List.mapM_cons]
    exact duplexP_bind (hf b hist) fun _ hist' _ ↦
      duplexP_bind (ih hist') fun _ _ _ ↦ duplexP_pure trivial

/-- **The code-binding verifier follows the duplex discipline.** -/
theorem duplex_codeBindingPost (crs : Crs)
    (out : (Common.DigestBytes × Proof) × List (Fin (r * 128) × Cell × CellOpening)) :
    Duplex KState.zero keccakNF (codeBindingPost r ps crs out) [] :=
  duplex_of_duplexP (Q := fun _ _ ↦ True) <|
    duplexP_bind (duplexP_mapM _ (fun _ hist ↦ duplexP_verifyRpm r ps crs _ _ _ _ hist) _ [])
      fun _ _ _ ↦ duplexP_pure trivial

/-- **Code binding moves from the random-permutation model to the two-oracle random-oracle
model.** For every argument `ps` and every adversary whose game, verifications included, makes at
most `Q` calls of the permutation on every path, the RPM code-binding probability and the
two-oracle ROM code-binding probability of `advS2 A` differ by at most `Q² / 2^508`. -/
theorem leanDa_codeBinding_rpm (A : CodeBindingAdvB r Crs Proof) (Q : ℕ)
    (hQ : QueryCostAtMost (codeBindingGame2 r ps A) permCalls2 Q) :
    Pr{let b ← codeBindingExpRpm r ps A}[b = true] ≤
        Pr{let b ← codeBindingExpRom2 r ps A}[b = true] + (Q ^ 2 : ℝ≥0∞) / 2 ^ 508 ∧
      Pr{let b ← codeBindingExpRom2 r ps A}[b = true] ≤
        Pr{let b ← codeBindingExpRpm r ps A}[b = true] + (Q ^ 2 : ℝ≥0∞) / 2 ^ 508 := by
  rw [permCalls2_eq] at hQ
  exact keccak256_transfer2 (liftM ps.setup) (fun crs ↦ A ((), crs)) (codeBindingPost r ps)
    (fun x a ↦ duplex_codeBindingPost r ps x a) Q hQ (· = true)

end CodeBinding

end LeanDa
