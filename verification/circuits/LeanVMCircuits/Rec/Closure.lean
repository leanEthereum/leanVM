module

public import Mathlib.Tactic

@[expose] public section

/-!
Determination rules and their closure.

A rule says: once every premise node is determined, every conclusion node is. `Closure r seeds` is what the rules
determine from the seeds. `closure_agree` is what that means: two assignments of values to nodes that agree on the
seeds, and for which every rule is valid (agreeing on a rule's premises, they agree on its conclusions), agree on
every node of the closure.

`certifyT` replays a list of rule firings, the certificate `CheckBind`'s worklist records, giving a node a time only
when a seed at that time or a firing whose premises have times gives it (the firing at their latest);
`certifyT_sound`: every node it gives time `t` is in the closure of the seeds given by `t`. So the checker's verdict
rests on this small replay, not on the worklist.

Each rule carries a justification of type `J`, why it holds; `LeanVMCircuits.Rec.Bind.Just` checks it against the
circuit.
-/

namespace LeanVMCircuits.Rec.Bind

/-- Determination rules over nodes, each its premises, conclusions and justification, flattened. -/
structure Rules (J : Type) where
  premOff : Array ℕ := #[0]
  prems : Array ℕ := #[]
  conclOff : Array ℕ := #[0]
  concls : Array ℕ := #[]
  why : Array J := #[]
  deriving Inhabited

variable {J : Type}

def Rules.size (r : Rules J) : ℕ := r.why.size

def Rules.push (r : Rules J) (w : J) (ps cs : Array ℕ) : Rules J :=
  { premOff := r.premOff.push (r.prems.size + ps.size), prems := r.prems ++ ps,
    conclOff := r.conclOff.push (r.concls.size + cs.size), concls := r.concls ++ cs, why := r.why.push w }

/-- Rule `i`'s premises. -/
def Rules.prem (r : Rules J) (i : ℕ) : List ℕ :=
  (r.prems.extract (r.premOff.getD i 0) (r.premOff.getD (i + 1) 0)).toList

/-- Rule `i`'s conclusions. -/
def Rules.concl (r : Rules J) (i : ℕ) : List ℕ :=
  (r.concls.extract (r.conclOff.getD i 0) (r.conclOff.getD (i + 1) 0)).toList

/-- What the rules determine from the seeds. -/
inductive Closure (r : Rules J) (seeds : List ℕ) : ℕ → Prop
  | seed {n : ℕ} : n ∈ seeds → Closure r seeds n
  | fire {i n : ℕ} : i < r.size → (∀ p ∈ r.prem i, Closure r seeds p) → n ∈ r.concl i → Closure r seeds n

/-- Rule `i` is valid for two assignments: agreeing on its premises, they agree on its conclusions. -/
def Valid {α : Type} (r : Rules J) (ν ν' : ℕ → α) (i : ℕ) : Prop :=
  (∀ p ∈ r.prem i, ν p = ν' p) → ∀ c ∈ r.concl i, ν c = ν' c

/-- Two assignments agreeing on the seeds, for which every rule is valid, agree on the closure. -/
theorem closure_agree {α : Type} {r : Rules J} {seeds : List ℕ} {ν ν' : ℕ → α}
    (hv : ∀ i < r.size, Valid r ν ν' i) (hs : ∀ n ∈ seeds, ν n = ν' n) {n : ℕ} (h : Closure r seeds n) :
    ν n = ν' n := by
  induction h with
  | seed hn => exact hs _ hn
  | fire hi _ hn ih => exact hv _ hi (fun p hp => ih p hp) _ hn

/-- `closure_agree` asking validity only of the rules the closure fires: those whose premises are all in it. -/
theorem closure_agree_on {α : Type} {r : Rules J} {seeds : List ℕ} {ν ν' : ℕ → α}
    (hv : ∀ i < r.size, (∀ p ∈ r.prem i, Closure r seeds p) → Valid r ν ν' i) (hs : ∀ n ∈ seeds, ν n = ν' n) {n : ℕ}
    (h : Closure r seeds n) : ν n = ν' n := by
  induction h with
  | seed hn => exact hs _ hn
  | fire hi hp hn ih => exact hv _ hi hp (fun p hp => ih p hp) _ hn

/-- The closure grows with its seeds. -/
theorem Closure.mono {r : Rules J} {A B : List ℕ} (hAB : ∀ n ∈ A, n ∈ B) {n : ℕ} (h : Closure r A n) :
    Closure r B n := by
  induction h with
  | seed hn => exact .seed (hAB _ hn)
  | fire hi _ hn ih => exact .fire hi ih hn

/-- The seeds given by time `t`. -/
def seedsBy (seeds : List (ℕ × ℕ)) (t : ℕ) : List ℕ := (seeds.filter (·.1 ≤ t)).map (·.2)

theorem seedsBy_mono {seeds : List (ℕ × ℕ)} {t t' : ℕ} (h : t ≤ t') : ∀ n ∈ seedsBy seeds t, n ∈ seedsBy seeds t' := by
  intro n hn
  simp only [seedsBy, List.mem_map, List.mem_filter, decide_eq_true_eq] at hn ⊢
  obtain ⟨p, ⟨hp, ht⟩, rfl⟩ := hn
  exact ⟨p, ⟨hp, ht.trans h⟩, rfl⟩

/-- Mark the nodes `ns` at time `t`, keeping an earlier time. -/
def markT (m : Array (Option ℕ)) (t : ℕ) (ns : List ℕ) : Array (Option ℕ) :=
  ns.foldl (fun m n => if (m.getD n none).any (· ≤ t) then m else m.setIfInBounds n (some t)) m

/-- The latest time among marked nodes, `none` if one is unmarked. -/
def latest (m : Array (Option ℕ)) : Option ℕ → List ℕ → Option ℕ
  | acc, [] => acc
  | acc, p :: ps => latest m (match acc, m.getD p none with
    | some a, some b => some (max a b)
    | _, _ => none) ps

/-- Fire rule `i` if its premises are marked, at their latest time. -/
def fireT (r : Rules J) (m : Array (Option ℕ)) (i : ℕ) : Array (Option ℕ) :=
  if i < r.size then
    match latest m (some 0) (r.prem i) with
    | some t => markT m t (r.concl i)
    | none => m
  else m

/-- Each node's time in a certificate: the seeds at their times, then each firing in order at its premises' latest. -/
def certifyT (r : Rules J) (nodes : ℕ) (seeds : List (ℕ × ℕ)) (firings : Array ℕ) : Array (Option ℕ) :=
  firings.foldl (fireT r) (seeds.foldl (fun m p => markT m p.1 [p.2]) (Array.replicate nodes none))

theorem markT_marked (t : ℕ) (ns : List ℕ) : ∀ (m : Array (Option ℕ)) (n u : ℕ), (markT m t ns).getD n none = some u →
    m.getD n none = some u ∨ (n ∈ ns ∧ u = t) := by
  induction ns with
  | nil => intro m n u h; exact Or.inl h
  | cons k ks ih =>
    intro m n u h
    rcases ih _ n u h with h | ⟨hn, rfl⟩
    · dsimp only at h
      split at h
      · exact Or.inl h
      · by_cases hk : n = k
        · subst hk
          simp only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_self] at h
          split at h
          · simp at h; exact Or.inr ⟨List.mem_cons_self .., h.symm⟩
          · rw [Array.getD_eq_getD_getElem?]; simp_all
        · left
          simp only [Array.getD_eq_getD_getElem?] at h ⊢
          rwa [Array.getElem?_setIfInBounds_ne (Ne.symm hk)] at h
    · exact Or.inr ⟨List.mem_cons_of_mem _ hn, rfl⟩

theorem latest_some (m : Array (Option ℕ)) : ∀ (ps : List ℕ) (a T : ℕ), latest m (some a) ps = some T →
    a ≤ T ∧ ∀ p ∈ ps, ∃ tp, m.getD p none = some tp ∧ tp ≤ T := by
  have hnone : ∀ ps : List ℕ, latest m none ps = none := by
    intro ps
    induction ps with
    | nil => rfl
    | cons p ps ih => exact ih
  intro ps
  induction ps with
  | nil => intro a T h; simp only [latest, Option.some.injEq] at h; exact ⟨h.le, by simp⟩
  | cons p ps ih =>
    intro a T h
    simp only [latest] at h
    cases hp : m.getD p none with
    | none => rw [hp, hnone] at h; exact absurd h (by simp)
    | some b =>
      rw [hp] at h
      obtain ⟨hab, hps⟩ := ih _ _ h
      refine ⟨(le_max_left a b).trans hab, ?_⟩
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact ⟨b, hp, (le_max_right a b).trans hab⟩
      · exact hps q hq

/-- A node a certificate marks at time `t` is in the closure of the seeds given by `t`. -/
theorem certifyT_sound (r : Rules J) (nodes : ℕ) (seeds : List (ℕ × ℕ)) (firings : Array ℕ) (n t : ℕ)
    (h : (certifyT r nodes seeds firings).getD n none = some t) : Closure r (seedsBy seeds t) n := by
  let Inv := fun (m : Array (Option ℕ)) => ∀ k u, m.getD k none = some u → Closure r (seedsBy seeds u) k
  have hs : ∀ (ps : List (ℕ × ℕ)) (m : Array (Option ℕ)), (∀ p ∈ ps, p ∈ seeds) → Inv m →
      Inv (ps.foldl (fun m p => markT m p.1 [p.2]) m) := by
    intro ps
    induction ps with
    | nil => intro m _ hm; exact hm
    | cons p ps ih =>
      intro m hps hm
      refine ih _ (fun q hq => hps q (List.mem_cons_of_mem _ hq)) fun k u hk => ?_
      rcases markT_marked _ _ m k u hk with hk | ⟨hk', rfl⟩
      · exact hm k u hk
      · simp only [List.mem_singleton] at hk'
        subst hk'
        refine .seed ?_
        simp only [seedsBy, List.mem_map, List.mem_filter, decide_eq_true_eq]
        exact ⟨p, ⟨hps p List.mem_cons_self, le_rfl⟩, rfl⟩
  have h0 : Inv (Array.replicate nodes none) := by
    intro k u hk
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate] at hk
    split at hk <;> simp at hk
  have step : ∀ m i, Inv m → Inv (fireT r m i) := by
    intro m i hm k u hk
    unfold fireT at hk
    split at hk
    · rename_i hi
      split at hk
      · rename_i T hT
        rcases markT_marked _ _ m k u hk with hk | ⟨hk', rfl⟩
        · exact hm k u hk
        · obtain ⟨-, hps⟩ := latest_some m _ _ _ hT
          refine .fire hi (fun p hp => ?_) hk'
          obtain ⟨tp, htp, hle⟩ := hps p hp
          exact (hm p tp htp).mono (seedsBy_mono hle)
      · exact hm k u hk
    · exact hm k u hk
  have hall : ∀ (fs : List ℕ) (m : Array (Option ℕ)), Inv m → Inv (fs.foldl (fireT r) m) := by
    intro fs
    induction fs with
    | nil => intro m hm; exact hm
    | cons f fs ih => intro m hm; exact ih _ (step m f hm)
  unfold certifyT at h
  rw [← Array.foldl_toList] at h
  exact hall firings.toList _ (hs seeds _ (fun _ h => h) h0) n t h

end LeanVMCircuits.Rec.Bind
