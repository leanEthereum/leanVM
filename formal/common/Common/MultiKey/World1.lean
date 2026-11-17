module

public import Common.MultiKey.KeyPhase
public import Common.MultiKey.World2

@[expose] public section

/-!
# The tagged game with one oracle is the multi-key game, at key `i`

Forgetting the tags (`untag`), the tagged game for key `i` asks one random oracle for everything:
it is the multi-key game with key `i` generated first. On the event that the forgery is under
key `i` and wins, the two have the same probability (`prob_multiGame_eq_untag`): the reduction's
answers are the multi-key game's (`advPhase_eq`: a request to key `i` is the signing oracle's,
logged as key `i`'s transcript (`keyLog`), a request to another key is that key's signer), and the
keys have the multi-key game's distribution with the oracle's cache
(`Common.SufCma.MultiKey.romRun_sequenceFin_pull`).
-/

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal
open HashSig.OverPermutation (sequenceFin)

namespace Common.SufCma.MultiKey

variable {Seed PK SK Req Resp F : Type}

/-! ## Forgetting the tags -/

/-- The tagged oracles inside the reduction, the tags forgotten, requests forwarded. -/
def untagR : QueryImpl (TSpec + (Req →ₒ Resp)) (OracleComp (World + (Req →ₒ Resp)))
  | .inl t => simulateQ toWR (untag t)
  | .inr r => liftM ((World + (Req →ₒ Resp)).query (.inr r))

theorem untag_coinsT {α : Type} (p : ProbComp α) :
    simulateQ untag (simulateQ coinsT p) = (liftM p : OracleComp World α) := by
  rw [← QueryImpl.simulateQ_compose]
  rfl

theorem untag_tagF {α : Type} (X : OracleComp SchemeHashSpec α) :
    simulateQ untag (simulateQ tagF X) = (liftM X : OracleComp World α) := by
  rw [← QueryImpl.simulateQ_compose]
  rfl

theorem untag_tagG {α : Type} (X : OracleComp SchemeHashSpec α) :
    simulateQ untag (simulateQ tagG X) = (liftM X : OracleComp World α) := by
  rw [← QueryImpl.simulateQ_compose]
  rfl

theorem untagR_toTR {α : Type} (X : OracleComp TSpec α) :
    simulateQ (untagR (Req := Req) (Resp := Resp)) (simulateQ toTR X) =
      simulateQ toWR (simulateQ untag X) := by
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
  congr 1
  funext t
  simp only [QueryImpl.apply_compose, toTR, simulateQ_spec_query]
  rfl

/-- A computation of the world inside the game's oracles logs nothing. -/
theorem run_gameOracles_toWR {SK' : Type} (S' : SchemeWithHash Seed PK SK' Req Resp F) (sk : SK')
    {α : Type} (X : OracleComp World α) :
    (simulateQ (gameOracles S' sk) (simulateQ (toWR (Req := Req) (Resp := Resp)) X)).run =
      (·, ∅) <$> X := by
  rw [← QueryImpl.simulateQ_compose,
    run_simulateQ_writer_of_run _ (fun u ↦ (liftM (World.query u) : OracleComp World _))
      (fun u ↦ by simp only [QueryImpl.apply_compose, toWR, simulateQ_spec_query]; rfl)]
  have h : simulateQ (fun u ↦ (liftM (World.query u) : OracleComp World _)) X = X :=
    simulateQ_ofLift_eq_self X
  rw [h]

variable (S : SchemeWithHash Seed PK SK Req Resp F)

/-- **The tags forgotten, then the signing oracle, is the signing oracle, then the tags
forgotten.** -/
theorem untag_gameOraclesT (sk : SK) {α : Type} (Y : OracleComp (TSpec + (Req →ₒ Resp)) α) :
    simulateQ untag ((simulateQ (gameOraclesT S sk) Y).run) =
      (simulateQ (gameOracles S sk) (simulateQ untagR Y)).run := by
  refine simulateQ_writer_run_comm _ _ _ _ (fun t ↦ ?_) Y
  rcases t with t | r
  · have h1 : ((gameOraclesT S sk) (.inl t)).run =
        (·, ∅) <$> (liftM (TSpec.query t) : OracleComp TSpec _) := rfl
    rw [h1, simulateQ_map, simulateQ_spec_query]
    exact (run_gameOracles_toWR S sk (untag t)).symm
  · have h1 : ((gameOraclesT S sk) (.inr r)).run = (fun u ↦ (u, [⟨r, u⟩])) <$>
        simulateQ tagF (S.sign sk r) := by
      simp [gameOraclesT, signT]
    rw [h1, simulateQ_map, untag_tagF]
    have h2 : untagR (Req := Req) (Resp := Resp) (.inr r) =
        liftM ((World + (Req →ₒ Resp)).query (.inr r)) := rfl
    rw [h2, simulateQ_spec_query, gameOracles_inr]

/-! ## The adversary's phase -/

/-- **A writer simulation whose every step logs the image of another's logs the image of its
log**, through a map of logs that respects appending. -/
theorem run_simulateQ_writer_map_log {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    {L₁ L₂ : Type} [EmptyCollection L₁] [Append L₁] [LawfulAppend L₁] [EmptyCollection L₂]
    [Append L₂] [LawfulAppend L₂] (f₁ : QueryImpl spec (WriterT L₁ (OracleComp spec')))
    (f₂ : QueryImpl spec (WriterT L₂ (OracleComp spec'))) (φ : L₂ → L₁)
    (happ : ∀ a b, φ (a ++ b) = φ a ++ φ b) (hemp : φ ∅ = ∅)
    (h : ∀ t, (f₁ t).run = Prod.map id φ <$> (f₂ t).run) {α : Type} (X : OracleComp spec α) :
    (simulateQ f₁ X).run = Prod.map id φ <$> (simulateQ f₂ X).run := by
  induction X using OracleComp.inductionOn with
  | pure a => simp [hemp]
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, WriterT.run_bind', h, bind_map_left, map_bind, ih, Functor.map_map]
    refine bind_congr fun z ↦ ?_
    congr 1
    funext w
    rcases w with ⟨a, b⟩
    simp only [Prod.map_apply, id_eq, happ]
    rfl

variable {k : ℕ}

theorem keyLog_append (i : Fin k) (a b : QueryLog (Fin k × Req →ₒ Resp)) :
    keyLog i (a ++ b) = keyLog i a ++ keyLog i b :=
  List.filterMap_append

theorem keyLog_empty (i : Fin k) : keyLog i (∅ : QueryLog (Fin k × Req →ₒ Resp)) = ∅ := rfl

/-- The secret keys the multi-key game signs with: key `i`'s, and the others'. -/
def sksOf (sk : SK) (others : Fin k → Option (KeyRec PK SK)) (j : Fin k) : SK :=
  match others j with
  | some z => z.1.2
  | none => sk

variable (ownedPub : PK → List UInt8 → Prop) [∀ pk, DecidablePred (ownedPub pk)]

/-- **The reduction's answers, the tags forgotten, are the multi-key game's**: the signing
oracle's transcript is key `i`'s transcript of the multi-key game. -/
theorem advPhase_eq (i : Fin k) (pk : PK) (sk : SK) (others : Fin k → Option (KeyRec PK SK))
    (hi : others i = none) (hs : ∀ j, j ≠ i → (others j).isSome) {α : Type}
    (X : OracleComp (World + (Fin k × Req →ₒ Resp)) α) :
    (simulateQ (gameOracles S sk)
        (simulateQ untagR (simulateQ (advImpl S ownedPub i pk others) X))).run =
      Prod.map id (keyLog i) <$>
        (simulateQ (gameOracles (S.multiKey k) (sksOf sk others)) X).run := by
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
  refine run_simulateQ_writer_map_log _ _ (keyLog i) (keyLog_append i) (keyLog_empty i)
    (fun t ↦ ?_) X
  rcases t with t | ⟨j, r⟩
  · rw [gameOracles_inl, Functor.map_map]
    simp only [QueryImpl.apply_compose, QueryImpl.simulateQ_compose]
    have h1 : simulateQ untagR (advImpl S ownedPub i pk others (.inl t)) =
        simulateQ (toWR (Req := Req) (Resp := Resp))
          (liftM (World.query t) : OracleComp World _) := by
      rcases t with n | x <;> simp only [advImpl, simulateQ_spec_query] <;> rfl
    rw [h1, run_gameOracles_toWR]
    rfl
  · simp only [QueryImpl.apply_compose, QueryImpl.simulateQ_compose]
    rw [gameOracles_inr, Functor.map_map]
    by_cases hj : j = i
    · subst hj
      have h1 : advImpl S ownedPub j pk others (.inr (j, r)) =
          liftM ((TSpec + (Req →ₒ Resp)).query (.inr r)) := by simp [advImpl]
      have h2 : untagR (Req := Req) (Resp := Resp) (.inr r) =
          liftM ((World + (Req →ₒ Resp)).query (.inr r)) := rfl
      rw [h1, simulateQ_spec_query, h2, simulateQ_spec_query, gameOracles_inr]
      have h3 : sksOf sk others j = sk := by simp [sksOf, hi]
      simp [SchemeWithHash.multiKey, h3, keyLog]
    · obtain ⟨z, hz⟩ := Option.isSome_iff_exists.mp (hs j hj)
      have h1 : advImpl S ownedPub i pk others (.inr (j, r)) =
          simulateQ toTR (simulateQ tagG (S.sign z.1.2 r)) := by simp [advImpl, hj, hz]
      rw [h1, untagR_toTR, untag_tagG, run_gameOracles_toWR]
      have h3 : sksOf sk others j = z.1.2 := by simp [sksOf, hz]
      simp [SchemeWithHash.multiKey, h3, keyLog, hj]

/-! ## The two games, taken apart -/

/-- The other keys, the tags forgotten. -/
def setupW (i : Fin k) : OracleComp World (Fin k → Option (KeyRec PK SK)) :=
  sequenceFin fun j ↦ if j = i then pure none else do
    let s ← (liftM S.sample : OracleComp World Seed)
    some <$> (liftM (loggedKeygen S s) : OracleComp World _)

theorem untag_setup (i : Fin k) : simulateQ untag (setup S i) = setupW S i := by
  unfold setup setupW
  rw [LeanXmss.simulateQ_sequenceFin]
  congr 1
  funext j
  split
  · simp
  · simp only [simulateQ_bind, simulateQ_map, untag_coinsT, untag_tagG]

theorem setupW_spec (i : Fin k) {others : Fin k → Option (KeyRec PK SK)}
    (h : others ∈ support (setupW S i)) : others i = none ∧ ∀ j, j ≠ i → (others j).isSome := by
  refine ⟨?_, fun j hj ↦ ?_⟩
  · have hi := mem_support_sequenceFin _ h i
    simpa using hi
  · have hj' := mem_support_sequenceFin _ h j
    simp only [hj, ↓reduceIte, support_bind, support_map, Set.mem_iUnion, Set.mem_image] at hj'
    obtain ⟨_, _, z, _, hz⟩ := hj'
    rw [← hz]
    rfl

/-- The tagged game's phase after the keys, the tags forgotten. -/
def tailT (i : Fin k)
    (A : (Fin k → PK) → OracleComp (World + (Fin k × Req →ₒ Resp)) (Fin k × F))
    (zi : KeyRec PK SK) (others : Fin k → Option (KeyRec PK SK)) :
    OracleComp World ((Fin k × Bool) × KeyRec PK SK × (Fin k → Option (KeyRec PK SK))) := do
  let p ← (simulateQ (gameOracles S zi.1.2) (simulateQ untagR
    (simulateQ (advImpl S ownedPub i zi.1.1 others) (A (pksOf zi.1.1 others))))).run
  let v ← (liftM (S.verify zi.1.1 p.1.2) : OracleComp World Bool)
  return ((p.1.1, S.win p.2 p.1.2 && v), zi, others)

/-- **The tagged game, the tags forgotten**: key `i`, the others, then the adversary's phase. -/
theorem untag_taggedGame (i : Fin k)
    (A : (Fin k → PK) → OracleComp (World + (Fin k × Req →ₒ Resp)) (Fin k × F)) :
    simulateQ untag (taggedGame S ownedPub i A) =
      (liftM S.sample : OracleComp World Seed) >>= fun s ↦
        (liftM (loggedKeygen S s) : OracleComp World _) >>= fun zi ↦
          setupW S i >>= fun others ↦ tailT S ownedPub i A zi others := by
  simp only [taggedGame, simulateQ_bind, untag_coinsT, untag_tagF, untag_gameOraclesT,
    simulateQ_pure]
  refine bind_congr fun s ↦ bind_congr fun zi ↦ ?_
  simp only [reductionT, simulateQ_bind, untagR_toTR, untag_setup, simulateQ_pure,
    WriterT.run_bind', run_gameOracles_toWR, bind_map_left, tailT, bind_assoc]
  refine bind_congr fun others ↦ ?_
  simp only [WriterT.run_pure, pure_bind, Prod.map_apply, id_eq, List.empty_eq,
    List.nil_append, List.append_nil]

/-- The multi-key game's phase after the keys: the adversary, the forgery verified under its
key; the forgery's index and the win. -/
def tailM (A : (Fin k → PK) → OracleComp (World + (Fin k × Req →ₒ Resp)) (Fin k × F))
    (keys : (Fin k → PK) × (Fin k → SK)) : OracleComp World (Fin k × Bool) := do
  let p ← (simulateQ (gameOracles (S.multiKey k) keys.2) (A keys.1)).run
  let v ← (liftM ((S.multiKey k).verify keys.1 p.1) : OracleComp World Bool)
  return (p.1.1, (S.multiKey k).win p.2 p.1 && v)

/-- **The multi-key ROM game, with the forgery's index.** -/
def multiGameIdx (A : (Fin k → PK) → OracleComp (World + (Fin k × Req →ₒ Resp)) (Fin k × F)) :
    OracleComp World (Fin k × Bool) := do
  let seeds ← (liftM (S.multiKey k).sample : OracleComp World _)
  let keys ← (liftM ((S.multiKey k).keygen seeds) : OracleComp World _)
  tailM S A keys

theorem romGame_multiKey
    (A : (Fin k → PK) → OracleComp (World + (Fin k × Req →ₒ Resp)) (Fin k × F)) :
    romGame (S.multiKey k) A = Prod.snd <$> multiGameIdx S A := by
  rw [romGame_eq]
  simp only [multiGameIdx, tailM, map_bind, map_pure]

/-- The keys of key `i`'s record and the others'. -/
def keysOf (zi : KeyRec PK SK) (others : Fin k → Option (KeyRec PK SK)) :
    (Fin k → PK) × (Fin k → SK) :=
  (pksOf zi.1.1 others, sksOf zi.1.2 others)

/-- An event of a run in the random-oracle model, through a bind, from continuations with the
same event probability on the support. -/
theorem prEvent_romRun_bind_congr {α β γ : Type} (x : OracleComp World α)
    {f : α → OracleComp World β} {g : α → OracleComp World γ} {p : β → Prop} {q : γ → Prop}
    (h : ∀ a ∈ support x, ∀ c, Pr{let z ← romRun (f a) c}[p z.1] = Pr{let z ← romRun (g a) c}[q z.1])
    (c : SchemeHashSpec.QueryCache) :
    Pr{let z ← romRun (x >>= f) c}[p z.1] = Pr{let z ← romRun (x >>= g) c}[q z.1] := by
  rw [romRun_bind, romRun_bind]
  exact prEvent_bind_congr_support _ fun z hz ↦ h z.1 (KeptKey.fst_mem_support_romRun' hz) z.2

/-- An output of a computation ending in `pure (f v)` is some `f v`. -/
theorem romRun_bind_pure_support {α β : Type} (x : OracleComp World α) (f : α → β)
    (c : SchemeHashSpec.QueryCache) {z : β × SchemeHashSpec.QueryCache}
    (hz : z ∈ support (romRun (x >>= fun v ↦ pure (f v)) c)) : ∃ v, z.1 = f v := by
  have h := KeptKey.fst_mem_support_romRun' hz
  simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at h
  obtain ⟨v, -, hv⟩ := h
  exact ⟨v, hv⟩

/-- **On the forgery under key `i`, the tagged game's phase after the keys, the tags forgotten,
is the multi-key game's.** -/
theorem tail_event (i : Fin k)
    (A : (Fin k → PK) → OracleComp (World + (Fin k × Req →ₒ Resp)) (Fin k × F))
    (zi : KeyRec PK SK) (others : Fin k → Option (KeyRec PK SK))
    (hspec : others i = none ∧ ∀ j, j ≠ i → (others j).isSome) (c : SchemeHashSpec.QueryCache) :
    Pr{let z ← romRun (tailT S ownedPub i A zi others) c}[z.1.1 = (i, true)] =
      Pr{let z ← romRun (tailM S A (keysOf zi others)) c}[z.1 = (i, true)] := by
  unfold tailT tailM keysOf
  dsimp only
  rw [advPhase_eq S ownedPub i _ _ others hspec.1 hspec.2, bind_map_left]
  refine prEvent_romRun_bind_congr
    (p := fun y : (Fin k × Bool) × KeyRec PK SK × (Fin k → Option (KeyRec PK SK)) ↦
      y.1 = (i, true)) (q := fun y ↦ y = (i, true)) _ (fun p _ c' ↦ ?_) c
  by_cases hp : p.1.1 = i
  · have hpk : pksOf zi.1.1 others p.1.1 = zi.1.1 := by
      simp [pksOf, hp, hspec.1]
    simp only [SchemeWithHash.multiKey, hpk]
    refine prEvent_romRun_bind_congr
      (p := fun y : (Fin k × Bool) × KeyRec PK SK × (Fin k → Option (KeyRec PK SK)) ↦
        y.1 = (i, true)) (q := fun y ↦ y = (i, true)) _ (fun v _ c'' ↦ ?_) c'
    simp only [romRun, simulateQ_pure, StateT.run_pure, prEvent_pure, Prod.map_fst, Prod.map_snd,
      id_eq, hp]
  · rw [prEvent_eq_zero_of_forall_mem_support _ _ fun z hz ↦ ?_,
      prEvent_eq_zero_of_forall_mem_support _ _ fun z hz ↦ ?_]
    · obtain ⟨v, hv⟩ := romRun_bind_pure_support _ _ c' hz
      rw [hv]
      exact fun h ↦ hp (congrArg Prod.fst h)
    · obtain ⟨v, hv⟩ := romRun_bind_pure_support _ _ c' hz
      rw [hv]
      exact fun h ↦ hp (congrArg Prod.fst h)

theorem liftM_sequenceFin_coins {α : Type} :
    ∀ {n : ℕ} (c : Fin n → ProbComp α),
      (liftM (sequenceFin c) : OracleComp World _) =
        sequenceFin fun j ↦ (liftM (c j) : OracleComp World _)
  | 0, c => by simp [sequenceFin]
  | n + 1, c => by
    simp only [sequenceFin, liftM_bind, liftM_pure]
    refine bind_congr fun h ↦ ?_
    rw [liftM_sequenceFin_coins]

theorem liftM_sequenceFin_hash {α : Type} :
    ∀ {n : ℕ} (c : Fin n → OracleComp SchemeHashSpec α),
      (liftM (sequenceFin c) : OracleComp World _) =
        sequenceFin fun j ↦ (liftM (c j) : OracleComp World _)
  | 0, c => by simp [sequenceFin]
  | n + 1, c => by
    simp only [sequenceFin, liftM_bind, liftM_pure]
    refine bind_congr fun h ↦ ?_
    rw [liftM_sequenceFin_hash]

/-- A key pair from a fresh seed. -/
noncomputable def freshKey (S : SchemeWithHash Seed PK SK Req Resp F) : OracleComp World (PK × SK) :=
  (liftM S.sample : OracleComp World Seed) >>= fun s ↦ liftM (S.keygen s)

/-- Key pairs as the public keys and the secret keys. -/
def unz {PK SK : Type} (pairs : Fin k → PK × SK) : (Fin k → PK) × (Fin k → SK) :=
  (fun j ↦ (pairs j).1, fun j ↦ (pairs j).2)

theorem keysOf_eq (zi : KeyRec PK SK) (others : Fin k → Option (KeyRec PK SK)) :
    keysOf zi others = unz fun j ↦ match others j with
      | some z => z.1
      | none => zi.1 := by
  unfold keysOf unz pksOf sksOf
  refine Prod.ext (funext fun j ↦ ?_) (funext fun j ↦ ?_) <;> dsimp only <;>
    rcases others j with _ | z <;> rfl

/-- **The multi-key game, key `i` first.** -/
theorem multiGameIdx_pull (i : Fin k)
    (A : (Fin k → PK) → OracleComp (World + (Fin k × Req →ₒ Resp)) (Fin k × F)) :
    romRun (multiGameIdx S A) ∅ =ᵈ
      romRun (freshKey S >>= fun y ↦ sequenceFin (fun j ↦ if j = i then pure y else freshKey S) >>=
        fun pairs ↦ tailM S A (unz pairs)) ∅ := by
  have h0 : multiGameIdx S A = sequenceFin (fun _ : Fin k ↦ (liftM S.sample : OracleComp World _))
      >>= fun seeds ↦ sequenceFin (fun j ↦ (liftM (S.keygen (seeds j)) : OracleComp World _)) >>=
        fun pairs ↦ tailM S A (unz pairs) := by
    simp only [multiGameIdx, SchemeWithHash.multiKey, liftM_bind, liftM_sequenceFin_coins,
      liftM_sequenceFin_hash, bind_assoc, liftM_pure, pure_bind]
    rfl
  rw [h0]
  refine EvalDistEq.trans (romRun_sequenceFin_interleave (fun _ ↦ liftM S.sample)
    (fun _ s ↦ liftM (S.keygen s)) (fun _ pairs ↦ tailM S A (unz pairs)) ∅) ?_
  have h1 : (sequenceFin (fun j : Fin k ↦ (liftM S.sample : OracleComp World Seed) >>= fun x ↦
      (x, ·) <$> (liftM (S.keygen x) : OracleComp World (PK × SK))) >>= fun ps ↦
        tailM S A (unz fun j ↦ (ps j).2)) =
      sequenceFin (fun _ : Fin k ↦ freshKey S) >>= fun pairs ↦ tailM S A (unz pairs) := by
    have h2 : (fun _ : Fin k ↦ freshKey S) = fun j ↦ Prod.snd <$>
        ((liftM S.sample : OracleComp World Seed) >>= fun x ↦
          (x, ·) <$> (liftM (S.keygen x) : OracleComp World (PK × SK))) := by
      funext j
      simp only [freshKey, map_bind, Functor.map_map, id_map']
    rw [h2, sequenceFin_map (fun _ ↦ Prod.snd), bind_map_left]
  rw [h1]
  exact romRun_sequenceFin_pull _ i _ ∅

/-- **The tagged game, the tags forgotten, in the same shape.** -/
theorem untag_taggedGame_eq (i : Fin k)
    (A : (Fin k → PK) → OracleComp (World + (Fin k × Req →ₒ Resp)) (Fin k × F)) :
    ((liftM S.sample : OracleComp World Seed) >>= fun s ↦
        (liftM (loggedKeygen S s) : OracleComp World _) >>= fun zi ↦
          setupW S i >>= fun others ↦ tailM S A (keysOf zi others)) =
      freshKey S >>= fun y ↦ sequenceFin (fun j ↦ if j = i then pure y else freshKey S) >>=
        fun pairs ↦ tailM S A (unz pairs) := by
  simp only [freshKey, bind_assoc]
  refine bind_congr fun s ↦ ?_
  rw [← fst_map_loggedKeygen S s, liftM_map, bind_map_left]
  refine bind_congr fun zi ↦ ?_
  simp only [keysOf_eq]
  let m : Fin k → Option (KeyRec PK SK) → PK × SK := fun _ o ↦ match o with
    | some z => z.1
    | none => zi.1
  have hm : (fun j ↦ if j = i then pure zi.1 else
      ((liftM S.sample : OracleComp World Seed) >>= fun s ↦ liftM (S.keygen s))) =
      fun j ↦ m j <$> (if j = i then pure none else do
        let s ← (liftM S.sample : OracleComp World Seed)
        some <$> (liftM (loggedKeygen S s) : OracleComp World _)) := by
    funext j
    split
    · simp [m]
    · simp only [map_bind, Functor.map_map]
      refine bind_congr fun s' ↦ ?_
      rw [← fst_map_loggedKeygen S s', liftM_map]
  rw [hm, sequenceFin_map, bind_map_left]
  rfl

/-- **On the forgery under key `i`, the multi-key game and the tagged game with one oracle
agree.** -/
theorem prob_multiGame_eq_untag (i : Fin k)
    (A : (Fin k → PK) → OracleComp (World + (Fin k × Req →ₒ Resp)) (Fin k × F)) :
    Pr{let z ← romRun (multiGameIdx S A) ∅}[z.1 = (i, true)] =
      Pr{let z ← romRun (simulateQ untag (taggedGame S ownedPub i A)) ∅}[z.1.1 = (i, true)] := by
  rw [(multiGameIdx_pull S i A).prEvent_eq (fun z ↦ z.1 = (i, true)), untag_taggedGame,
    ← untag_taggedGame_eq]
  symm
  refine prEvent_romRun_bind_congr
    (p := fun y : (Fin k × Bool) × KeyRec PK SK × (Fin k → Option (KeyRec PK SK)) ↦
      y.1 = (i, true)) (q := fun y ↦ y = (i, true)) _ (fun s _ c ↦ ?_) ∅
  refine prEvent_romRun_bind_congr
    (p := fun y : (Fin k × Bool) × KeyRec PK SK × (Fin k → Option (KeyRec PK SK)) ↦
      y.1 = (i, true)) (q := fun y ↦ y = (i, true)) _ (fun zi _ c' ↦ ?_) c
  refine prEvent_romRun_bind_congr
    (p := fun y : (Fin k × Bool) × KeyRec PK SK × (Fin k → Option (KeyRec PK SK)) ↦
      y.1 = (i, true)) (q := fun y ↦ y = (i, true)) _ (fun others hothers c'' ↦ ?_) c'
  exact tail_event S ownedPub i A zi others (setupW_spec S i hothers) c''

end Common.SufCma.MultiKey
