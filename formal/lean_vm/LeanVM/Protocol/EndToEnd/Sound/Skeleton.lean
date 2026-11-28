/-
  LeanVM.Protocol.EndToEnd.Sound.Skeleton

  The transcript operations of a verifier program's returning runs, and their replay on the
  sponge without the program's arithmetic.
-/

module

public import LeanVM.Protocol.Relation.ExtractorDef
public import LeanVM.Protocol.Relation.Frame
public import LeanVM.Protocol.Whir.Params.Iface
public import LeanVM.Protocol.Relation.Runs

/-!
# Skeletons

`Skel p sk`: every history along which `p` returns performs the transcript operations `sk`
(`Op`: a read, a sample, a packed message or draw of given length, a proof of work of given bits,
a commitment of given shape, an opening), whatever the values. The verifier's phases have
skeletons fixed by the announced sizes, so the extractor replays the sponge from the skeleton
(`skelReplay`), without the phases' arithmetic: where the replay of `p` returns, the replay of its
skeleton returns the same state, along a history on which `p` returns the same value
(`skelReplay_of_replayU`).

The calculus: `Skel.ret`, `Skel.fail`, a step before a continuation of one skeleton, and
sequencing (`Skel.bind`), the continuation's skeleton the same at every value the first part may
return.
-/

namespace LeanVM.Protocol.EndToEnd.Sound

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Compile.Rom LeanVM.Protocol.KeccakHash

@[expose] public section

/-- A transcript operation. -/
inductive Op where
  | read
  | sample
  | readPacked (n : ℕ)
  | samplePacked (n : ℕ)
  | grind (bits : ℕ)
  | commit (height width : ℕ)
  | query
  deriving DecidableEq

/-- The operation of an event. -/
def Ev.op : Ev → Op
  | .read _ => .read
  | .sample _ => .sample
  | .readPacked xs => .readPacked xs.length
  | .samplePacked cs => .samplePacked cs.length
  | .grind b => .grind b
  | .commit h w _ => .commit h w
  | .query _ => .query

/-- **`p` has skeleton `sk`**: every history along which it returns performs `sk`. -/
def Skel {α : Type} (p : VerifierProgram α) (sk : List Op) : Prop :=
  ∀ h a, p.after h = some (.ret a) → h.map Ev.op = sk

namespace Skel

variable {α β : Type}

theorem ret (a : α) : Skel (.ret a) [] := by
  intro h b hb
  rcases h with _ | ⟨e, h⟩
  · rfl
  · simp [VerifierProgram.after] at hb

theorem fail (sk : List Op) : Skel (.fail : VerifierProgram α) sk := by
  intro h b hb
  rcases h with _ | ⟨e, h⟩ <;> simp [VerifierProgram.after] at hb

theorem read {k : E → VerifierProgram α} {sk : List Op} (hk : ∀ x, Skel (k x) sk) :
    Skel (.read k) (.read :: sk) := by
  intro h b hb
  rcases h with _ | ⟨e, h⟩
  · simp [VerifierProgram.after] at hb
  · cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at hb
    simp only [List.map_cons, Ev.op]
    rw [hk _ h b hb]

theorem sample {k : E → VerifierProgram α} {sk : List Op} (hk : ∀ x, Skel (k x) sk) :
    Skel (.sample k) (.sample :: sk) := by
  intro h b hb
  rcases h with _ | ⟨e, h⟩
  · simp [VerifierProgram.after] at hb
  · cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at hb
    simp only [List.map_cons, Ev.op]
    rw [hk _ h b hb]

theorem readPacked {n : ℕ} {k : List E → VerifierProgram α} {sk : List Op}
    (hk : ∀ xs, xs.length = n → Skel (k xs) sk) : Skel (.readPacked n k) (.readPacked n :: sk) := by
  intro h b hb
  rcases h with _ | ⟨e, h⟩
  · simp [VerifierProgram.after] at hb
  · cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at hb
    split_ifs at hb with hl
    simp only [List.map_cons, Ev.op, hl]
    rw [hk _ hl h b hb]

theorem samplePacked {n : ℕ} {k : List E → VerifierProgram α} {sk : List Op}
    (hk : ∀ cs, cs.length = n → Skel (k cs) sk) :
    Skel (.samplePacked n k) (.samplePacked n :: sk) := by
  intro h b hb
  rcases h with _ | ⟨e, h⟩
  · simp [VerifierProgram.after] at hb
  · cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at hb
    split_ifs at hb with hl
    simp only [List.map_cons, Ev.op, hl]
    rw [hk _ hl h b hb]

theorem grind {bits : ℕ} {k : VerifierProgram α} {sk : List Op} (hk : Skel k sk) :
    Skel (.grind bits k) (.grind bits :: sk) := by
  intro h b hb
  rcases h with _ | ⟨e, h⟩
  · simp [VerifierProgram.after] at hb
  · cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at hb
    split at hb
    · rename_i hbits
      subst hbits
      simp only [List.map_cons, Ev.op]
      rw [hk h b hb]
    · simp at hb

theorem commit {height width : ℕ} {k : VerifierProgram α} {sk : List Op} (hk : Skel k sk) :
    Skel (.commit height width k) (.commit height width :: sk) := by
  intro h b hb
  rcases h with _ | ⟨e, h⟩
  · simp [VerifierProgram.after] at hb
  · cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at hb
    split at hb
    · rename_i hhw
      obtain ⟨rfl, rfl⟩ := hhw
      simp only [List.map_cons, Ev.op]
      rw [hk h b hb]
    · simp at hb

theorem query {i : ℕ} {ps : List ℕ} {k : List (List K) → VerifierProgram α} {sk : List Op}
    (hk : ∀ rows, Skel (k rows) sk) : Skel (.query i ps k) (.query :: sk) := by
  intro h b hb
  rcases h with _ | ⟨e, h⟩
  · simp [VerifierProgram.after] at hb
  · cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at hb
    simp only [List.map_cons, Ev.op]
    rw [hk _ h b hb]

/-- **Sequencing**: a skeleton, then a continuation of one skeleton at every value the first part
may return. -/
theorem bind {p : VerifierProgram α} {f : α → VerifierProgram β} {sk₁ sk₂ : List Op}
    (hp : Skel p sk₁) (hf : ∀ a, VerifierProgram.Returns p a → Skel (f a) sk₂) :
    Skel (p.bind f) (sk₁ ++ sk₂) := by
  intro h b hb
  obtain ⟨a, h₁, h₂, rfl, ha, hfa⟩ := Whir.Params.after_bind_ret hb
  rw [List.map_append, hp h₁ a ha, hf a (Compile.returns_of_after ha) h₂ b hfa]

end Skel

section Replay

variable (F : KeccakState → Option KeccakState)

/-- **The replay of a skeleton**: the sponge driven by the operations, reading the stream and
the openings, without the program's arithmetic; the history it performs (commitments with an
empty word, openings with the proof's leaves). -/
def skelReplay : List Op → VerifierProgramState → Option (List Ev × VerifierProgramState)
  | [], s => some ([], s)
  | .read :: sk, s => match s.stream, s.sponge.ground with
    | x :: xs, none => (absorb (m := Option) F s.sponge x dsObserve).bind fun sp ↦
      (skelReplay sk { s with sponge := sp, stream := xs }).map fun r ↦ (.read x :: r.1, r.2)
    | _, _ => none
  | .sample :: sk, s => (squeeze (m := Option) F s.sponge).bind fun c ↦
      (skelReplay sk { s with sponge := c.2 }).map fun r ↦ (.sample c.1 :: r.1, r.2)
  | .readPacked n :: sk, s =>
    if s.sponge.ground.isNone ∧ n ≤ s.stream.length then
      (observePacked (m := Option) F s.sponge (s.stream.take n)).bind fun sp ↦
        (skelReplay sk { s with sponge := sp, stream := s.stream.drop n }).map fun r ↦
          (.readPacked (s.stream.take n) :: r.1, r.2)
    else none
  | .samplePacked n :: sk, s => (samplesPacked (m := Option) F s.sponge n).bind fun c ↦
      (skelReplay sk { s with sponge := c.2 }).map fun r ↦ (.samplePacked c.1 :: r.1, r.2)
  | .grind bits :: sk, s => match s.stream, s.sponge.ground with
    | n :: xs, none => (absorbNonce (m := Option) F s.sponge n).bind fun c ↦
      (skelReplay sk { s with sponge := c.2, stream := xs }).map fun r ↦ (.grind bits :: r.1, r.2)
    | _, _ => none
  | .commit height width :: sk, s => match s.stream, s.sponge.ground with
    | x0 :: x1 :: xs, none => (absorb (m := Option) F s.sponge x0 dsObserve).bind fun sp0 ↦
      (absorb (m := Option) F sp0 x1 dsObserve).bind fun sp1 ↦
      let roots := s.roots ++ [(digestFromHalves (x0, x1), height, width)]
      (skelReplay sk { s with sponge := sp1, stream := xs, roots := roots }).map fun r ↦
        (.commit height width (fun _ ↦ []) :: r.1, r.2)
    | _, _ => none
  | .query :: sk, s => match s.openings with
    | phase :: rest => (skelReplay sk { s with openings := rest }).map fun r ↦
      (.query (phase.map (·.leaf)) :: r.1, r.2)
    | [] => none

/-- **The replay of a skeleton is the program's replay**: where the replay of `p` returns, along
some history on which `p` returns the same value, the replay of that history's operations
returns that history and the same state. -/
theorem skelReplay_of_replayU {α : Type} :
    ∀ (p : VerifierProgram α) (s : VerifierProgramState) {a : α} {s' : VerifierProgramState},
      replayU F p s = some (a, s') →
        ∃ h, p.after h = some (.ret a) ∧ skelReplay F (h.map Ev.op) s = some (h, s')
  | .ret a, s, _, _, hx => by
    simp only [replayU, Option.some.injEq, Prod.mk.injEq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    exact ⟨[], rfl, rfl⟩
  | .fail, s, _, _, hx => by simp [replayU] at hx
  | .read k, s, _, _, hx => by
    simp only [replayU] at hx
    split at hx
    · rename_i x xs hs hg
      obtain ⟨sp, hsp, hx⟩ := Option.bind_eq_some_iff.mp hx
      obtain ⟨h, hh, hr⟩ := skelReplay_of_replayU (k x) _ hx
      refine ⟨.read x :: h, by simpa [VerifierProgram.after] using hh, ?_⟩
      simp only [List.map_cons, Ev.op, skelReplay, hs, hg, hsp, Option.bind_some, hr,
        Option.map_some]
    · simp at hx
  | .sample k, s, _, _, hx => by
    simp only [replayU] at hx
    obtain ⟨c, hc, hx⟩ := Option.bind_eq_some_iff.mp hx
    obtain ⟨h, hh, hr⟩ := skelReplay_of_replayU (k c.1) _ hx
    refine ⟨.sample c.1 :: h, by simpa [VerifierProgram.after] using hh, ?_⟩
    simp only [List.map_cons, Ev.op, skelReplay, hc, Option.bind_some, hr, Option.map_some]
  | .readPacked n k, s, _, _, hx => by
    simp only [replayU] at hx
    split_ifs at hx with hc
    obtain ⟨sp, hsp, hx⟩ := Option.bind_eq_some_iff.mp hx
    obtain ⟨h, hh, hr⟩ := skelReplay_of_replayU (k (s.stream.take n)) _ hx
    have hl : (s.stream.take n).length = n := by simp [hc.2]
    refine ⟨.readPacked (s.stream.take n) :: h, by simpa [VerifierProgram.after, hl] using hh, ?_⟩
    simp only [List.map_cons, Ev.op, hl, skelReplay, hc, and_self, ↓reduceIte, hsp,
      Option.bind_some, hr, Option.map_some]
  | .samplePacked n k, s, _, _, hx => by
    simp only [replayU] at hx
    obtain ⟨c, hc, hx⟩ := Option.bind_eq_some_iff.mp hx
    obtain ⟨h, hh, hr⟩ := skelReplay_of_replayU (k c.1) _ hx
    have hl : c.1.length = n := Relation.length_samplesPacked_opt F _ _ hc
    refine ⟨.samplePacked c.1 :: h, by simpa [VerifierProgram.after, hl] using hh, ?_⟩
    simp only [List.map_cons, Ev.op, hl, skelReplay, hc, Option.bind_some, hr, Option.map_some]
  | .grind bits k, s, _, _, hx => by
    simp only [replayU] at hx
    split at hx
    · rename_i n xs hs hg
      obtain ⟨c, hc, hx⟩ := Option.bind_eq_some_iff.mp hx
      split_ifs at hx with hp
      obtain ⟨h, hh, hr⟩ := skelReplay_of_replayU k _ hx
      refine ⟨.grind bits :: h, by simpa [VerifierProgram.after] using hh, ?_⟩
      simp only [List.map_cons, Ev.op, skelReplay, hs, hg, hc, Option.bind_some, hr,
        Option.map_some]
    · simp at hx
  | .commit height width k, s, _, _, hx => by
    simp only [replayU] at hx
    split at hx
    · rename_i x0 x1 xs hs hg
      obtain ⟨sp0, hsp0, hx⟩ := Option.bind_eq_some_iff.mp hx
      obtain ⟨sp1, hsp1, hx⟩ := Option.bind_eq_some_iff.mp hx
      obtain ⟨h, hh, hr⟩ := skelReplay_of_replayU k _ hx
      refine ⟨.commit height width (fun _ ↦ []) :: h, by simpa [VerifierProgram.after] using hh, ?_⟩
      simp only [List.map_cons, Ev.op, skelReplay, hs, hg, hsp0, hsp1, Option.bind_some, hr,
        Option.map_some]
    · simp at hx
  | .query i ps k, s, _, _, hx => by
    simp only [replayU] at hx
    split at hx
    · rename_i r phase rest hr ho
      obtain ⟨h, hh, hrep⟩ := skelReplay_of_replayU (k (phase.map (·.leaf))) _ hx
      refine ⟨.query (phase.map (·.leaf)) :: h, by simpa [VerifierProgram.after] using hh, ?_⟩
      simp only [List.map_cons, Ev.op, skelReplay, ho, hrep, Option.map_some]
    · simp at hx

theorem skelReplay_append : ∀ (sk₁ sk₂ : List Op) (s : VerifierProgramState),
    skelReplay F (sk₁ ++ sk₂) s = (skelReplay F sk₁ s).bind fun r ↦
      (skelReplay F sk₂ r.2).map fun r' ↦ (r.1 ++ r'.1, r'.2)
  | [], sk₂, s => by
    simp only [List.nil_append, skelReplay, Option.bind_some, List.nil_append]
    rcases skelReplay F sk₂ s <;> rfl
  | op :: sk₁, sk₂, s => by
    cases op with
    | read =>
      simp only [List.cons_append, skelReplay]
      split
      · rcases absorb (m := Option) F s.sponge _ dsObserve with _ | sp
        · rfl
        · simp only [Option.bind_some, skelReplay_append sk₁ sk₂]
          rcases skelReplay F sk₁ _ with _ | r <;> simp [Function.comp_def]
      · rfl
    | sample =>
      simp only [List.cons_append, skelReplay]
      rcases squeeze (m := Option) F s.sponge with _ | c
      · rfl
      · simp only [Option.bind_some, skelReplay_append sk₁ sk₂]
        rcases skelReplay F sk₁ _ with _ | r <;> simp [Function.comp_def]
    | readPacked n =>
      simp only [List.cons_append, skelReplay]
      split_ifs
      · rcases observePacked (m := Option) F s.sponge (s.stream.take n) with _ | sp
        · rfl
        · simp only [Option.bind_some, skelReplay_append sk₁ sk₂]
          rcases skelReplay F sk₁ _ with _ | r <;> simp [Function.comp_def]
      · rfl
    | samplePacked n =>
      simp only [List.cons_append, skelReplay]
      rcases samplesPacked (m := Option) F s.sponge n with _ | c
      · rfl
      · simp only [Option.bind_some, skelReplay_append sk₁ sk₂]
        rcases skelReplay F sk₁ _ with _ | r <;> simp [Function.comp_def]
    | grind b =>
      simp only [List.cons_append, skelReplay]
      split
      · rcases absorbNonce (m := Option) F s.sponge _ with _ | c
        · rfl
        · simp only [Option.bind_some, skelReplay_append sk₁ sk₂]
          rcases skelReplay F sk₁ _ with _ | r <;> simp [Function.comp_def]
      · rfl
    | commit ht w =>
      simp only [List.cons_append, skelReplay]
      split
      · rcases absorb (m := Option) F s.sponge _ dsObserve with _ | sp0
        · rfl
        · simp only [Option.bind_some]
          rcases absorb (m := Option) F sp0 _ dsObserve with _ | sp1
          · rfl
          · simp only [Option.bind_some, skelReplay_append sk₁ sk₂]
            rcases skelReplay F sk₁ _ with _ | r <;> simp [Function.comp_def]
      · rfl
    | query =>
      simp only [List.cons_append, skelReplay]
      split
      · simp only [skelReplay_append sk₁ sk₂]
        rcases skelReplay F sk₁ _ with _ | r <;> simp [Function.comp_def]
      · rfl

theorem length_skelReplay : ∀ (sk : List Op) (s : VerifierProgramState) {h : List Ev}
    {s' : VerifierProgramState}, skelReplay F sk s = some (h, s') → h.length = sk.length
  | [], s, h, s', hr => by
    simp only [skelReplay, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    rfl
  | op :: sk, s, h, s', hr => by
    cases op <;> simp only [skelReplay] at hr <;> (try split at hr) <;>
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, reduceCtorEq, Prod.mk.injEq] at hr <;>
      first
      | (obtain ⟨_, -, r, hr', rfl, rfl⟩ := hr; simp [length_skelReplay sk _ hr'])
      | (obtain ⟨_, -, _, -, r, hr', rfl, rfl⟩ := hr; simp [length_skelReplay sk _ hr'])
      | (obtain ⟨r, hr', rfl, rfl⟩ := hr; simp [length_skelReplay sk _ hr'])

end Replay

end
end LeanVM.Protocol.EndToEnd.Sound
