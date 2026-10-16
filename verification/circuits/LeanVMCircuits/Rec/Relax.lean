module

public import LeanVMCircuits.Rec.Contracts

@[expose] public section

/-!
The builder's calls replayed with some equalities relaxed.

`Bind.Holds` is every constraint of a circuit but its tests. To read what the other calls make in such an assignment,
replay the calls with each test's equality relaxed (`Call.execR`): the call makes the wires and constants it would,
and holds nothing. When that replay builds the circuit without its tests, an assignment holding every constraint but
the tests satisfies it, and `replayR_sound` gives every other call's contract (`Call.Holds`) and each `block` call's
`HASH` row.
-/

namespace LeanVMCircuits.Rec.Model

/-- Whether a call is an equality. -/
def Call.isEq : Call → Bool
  | .eqE .. | .eqK .. | .eqD .. | .eqConstE .. | .eqConstK .. => true
  | _ => false

/-- A call, or relaxed, an equality without its equality: only the constant it makes. -/
def Call.execR (relax : Bool) (c : Call) : M (List ℕ) :=
  if relax then
    match c with
    | .eqE .. | .eqK .. | .eqD .. => pure []
    | .eqConstE _ c0 c1 c2 => do let _ ← Model.eConst c0 c1 c2; pure []
    | .eqConstK _ v => do let _ ← Model.kConst v; pure []
    | c => c.exec
  else c.exec

/-- The `HASH` row a `block` call makes. -/
def Call.Rows (s : State) (outs : List ℕ) : Call → Prop
  | .hashBlock h m tf => ∃ mux bit x ds ch, ([h, tf, mux, bit, x, ds, outs.getD 0 0, ch] ++ m) ∈ s.hash
  | _ => True

theorem Call.Rows.mono {c : Call} {s s' : State} {outs : List ℕ} (h : c.Rows s outs) (he : Ext s s') :
    c.Rows s' outs := by
  cases c
  case hashBlock =>
    obtain ⟨mux, bit, x, ds, ch, hr⟩ := h
    exact ⟨mux, bit, x, ds, ch, he.hash _ hr⟩
  all_goals trivial

theorem Good.and {α : Type} {P : State → Prop} {m : M α} {Q₁ Q₂ : State → α → State → Prop} (h₁ : Good P m Q₁)
    (h₂ : Good P m Q₂) : Good P m fun s a s' => Q₁ s a s' ∧ Q₂ s a s' := by
  intro s hs hp
  obtain ⟨hi, he, hq₁⟩ := h₁ s hs hp
  exact ⟨hi, he, hq₁, (h₂ s hs hp).2.2⟩

/-- `block`'s `HASH` row. -/
theorem hashBlock_row (h : ℕ) (m : List ℕ) (tf : ℕ) :
    Good (fun _ => True) (hashBlock h m tf) fun _ o s' =>
      ∃ mux bit x ds ch, ([h, tf, mux, bit, x, ds, o, ch] ++ m) ∈ s'.hash := by
  refine (Good.bind fresh_good (P₂ := fun _ _ => True) (fun _ _ _ _ _ _ _ => trivial) fun mux =>
      Good.bind fresh_good (P₂ := fun _ _ => True) (fun _ _ _ _ _ _ _ => trivial) fun bit =>
      Good.bind fresh_good (P₂ := fun _ _ => True) (fun _ _ _ _ _ _ _ => trivial) fun x =>
      Good.bind fresh_good (P₂ := fun _ _ => True) (fun _ _ _ _ _ _ _ => trivial) fun ds =>
        hashRow_good h tf mux bit x ds m).weaken (fun s h => h) ?_
  rintro s o s5 hs - - ⟨mux, -, -, -, -, bit, -, -, -, -, x, -, -, -, -, ds, -, -, -, -, -, ch, hrow⟩
  exact ⟨mux, bit, x, ds, ch, hrow⟩

theorem Call.exec_rows (c : Call) (hok : c.ok = true) :
    Good (Wires c.args) c.exec fun _ outs s' => c.Rows s' outs := by
  cases c
  case hashBlock h m tf =>
    exact (ret_good (hashBlock_row h m tf)).pre (fun _ _ => trivial) |>.weaken (fun _ h => h)
      fun _ _ _ _ _ _ ⟨_, hout, hq⟩ => by subst hout; exact hq
  all_goals exact (Call.exec_good _ hok).weaken (fun _ h => h) fun _ _ _ _ _ _ _ => trivial

/-- A call keeps the invariant, only adds to the circuit, makes its rows, and unless it is a relaxed equality its
outputs are what it computes. -/
theorem Call.execR_good (c : Call) (relax : Bool) (hok : c.ok = true) :
    Good (Wires c.args) (c.execR relax) fun _ outs s' =>
      (∀ st val, Sat st s' val → (relax && c.isEq) = false → c.Holds st val outs) ∧ c.Rows s' outs := by
  have hex : Good (Wires c.args) c.exec fun _ outs s' =>
      (∀ st val, Sat st s' val → (relax && c.isEq) = false → c.Holds st val outs) ∧ c.Rows s' outs :=
    ((c.exec_good hok).and (c.exec_rows hok)).weaken (fun _ h => h) fun _ _ _ _ _ _ h =>
      ⟨fun st val hs _ => h.1 st val hs, h.2⟩
  cases relax with
  | false => simpa [Call.execR] using hex
  | true =>
    cases c
    all_goals simp only [Call.execR, ↓reduceIte]
    all_goals first
      | exact hex
      | exact Good.pure' fun _ _ _ => ⟨fun _ _ _ h => by simp [Call.isEq] at h, trivial⟩
      | exact (Good.bind (eConst_good _ _ _) (P₂ := fun _ _ => True) (fun _ _ _ _ _ _ _ => trivial) fun _ =>
          Good.pure' (Q := fun _ _ _ => True) fun _ _ _ => trivial).pre (fun _ _ => trivial) |>.weaken
          (fun _ h => h) fun _ _ _ _ _ _ _ => ⟨fun _ _ _ h => by simp [Call.isEq] at h, trivial⟩
      | exact (Good.bind (kConst_good _) (P₂ := fun _ _ => True) (fun _ _ _ _ _ _ _ => trivial) fun _ =>
          Good.pure' (Q := fun _ _ _ => True) fun _ _ _ => trivial).pre (fun _ _ => trivial) |>.weaken
          (fun _ h => h) fun _ _ _ _ _ _ _ => ⟨fun _ _ _ h => by simp [Call.isEq] at h, trivial⟩

/-- Replay calls from the `i`th, relaxing those `relax` flags, while each names wires already made and has its
sizes: the final state and every call's outputs. -/
def replayR (calls : Array Call) (relax : Array Bool) (i : ℕ) (s : State) (outs : Array (List ℕ)) :
    Option (State × Array (List ℕ)) :=
  if h : i < calls.size then
    let c := calls[i]
    if c.args.all (· < s.next) && c.ok then
      let r := (c.execR (relax.getD i false)).run s
      replayR calls relax (i + 1) r.2 (outs.push r.1)
    else none
  else some (s, outs)
termination_by calls.size - i

/-- What a replayed call gives in a circuit `t` holding its rows: its contract unless it is a relaxed equality, and
its `HASH` row. -/
def CallFacts (calls : Array Call) (relax : Array Bool) (t : State) (outs : Array (List ℕ)) (j : ℕ) : Prop :=
  ∀ hj : j < calls.size, (∀ st val, Sat st t val → (relax.getD j false && calls[j].isEq) = false →
    calls[j].Holds st val (outs.getD j [])) ∧ calls[j].Rows t (outs.getD j [])

theorem CallFacts.mono {calls : Array Call} {relax : Array Bool} {t t' : State} {outs : Array (List ℕ)} {j : ℕ}
    (h : CallFacts calls relax t outs j) (he : Ext t t') : CallFacts calls relax t' outs j := fun hj =>
  ⟨fun st val hs hr => (h hj).1 st val (hs.mono he) hr, (h hj).2.mono he⟩

theorem getD_push_lt {α : Type} (xs : Array α) (x d : α) {j : ℕ} (hj : j < xs.size) :
    (xs.push x).getD j d = xs.getD j d := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_push, show j ≠ xs.size by omega]

theorem getD_push_eq {α : Type} (xs : Array α) (x d : α) : (xs.push x).getD xs.size d = x := by
  simp [Array.getD_eq_getD_getElem?]

/-- A replay that reaches its end keeps the invariant, and every call's facts hold in the circuit it builds. -/
theorem replayR_sound (calls : Array Call) (relax : Array Bool) (i : ℕ) (s : State) (outs : Array (List ℕ))
    (t : State) (outs' : Array (List ℕ)) (hs : Inv s) (hsize : outs.size = i) (hi : i ≤ calls.size)
    (hpre : ∀ j < i, ∀ t', Ext s t' → CallFacts calls relax t' outs j)
    (h : replayR calls relax i s outs = some (t, outs')) :
    Inv t ∧ Ext s t ∧ outs'.size = calls.size ∧ ∀ j < calls.size, CallFacts calls relax t outs' j := by
  rw [replayR] at h
  split at h
  · rename_i hlt
    dsimp only at h
    split at h
    · rename_i hv
      simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hv
      obtain ⟨hs₁, he₁, hq, hrows⟩ := (calls[i].execR_good (relax.getD i false) hv.2) s hs hv.1
      have ih := replayR_sound calls relax (i + 1) _ _ t outs' hs₁ (by simp [hsize]) hlt ?_ h
      · exact ⟨ih.1, he₁.trans ih.2.1, ih.2.2⟩
      · intro j hj t' he hj'
        by_cases hji : j < i
        · have := hpre j hji t' (he₁.trans he) hj'
          rwa [getD_push_lt _ _ _ (by omega)]
        · have hji : j = i := by omega
          subst hji
          have hg : ∀ o : List ℕ, (outs.push o).getD j [] = o := fun o => by
            subst hsize; exact getD_push_eq _ _ _
          rw [hg]
          exact ⟨fun st val hsat hr => hq st val (hsat.mono he) hr, hrows.mono he⟩
    · simp at h
  · rename_i hge
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hs, Ext.refl _, by omega, fun j hj => hpre j (by omega) _ (Ext.refl _)⟩
termination_by calls.size - i

/-- Two states whose fields `Sat` reads are equal. -/
def sameSat (a b : State) : Bool :=
  a.unions == b.unions && a.emul == b.emul && a.exk == b.exk && a.hash == b.hash && a.split == b.split &&
    a.cast == b.cast && a.pub == b.pub

theorem sat_of_sameSat {st : ℕ → Fin 4 → K} {a b : State} {val : Val} (h : sameSat a b = true) (hs : Sat st a val) :
    Sat st b val := by
  simp only [sameSat, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hu, he⟩, hk⟩, hh⟩, hsp⟩, hc⟩, hp⟩ := h
  exact ⟨hu ▸ hs.unions, he ▸ hs.emul, hk ▸ hs.exk, hh ▸ hs.hash, hsp ▸ hs.split, hc ▸ hs.cast, hp ▸ hs.pub⟩

end LeanVMCircuits.Rec.Model
