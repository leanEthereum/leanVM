/-
  LeanVM.Guest.Bridge.PrefixTrack

  The tree track on a prefix function: its frame's body positions after each leading flow hint, the moves from one to the next, and the `m`-th ISA flow hint compiling the hint that pops the entry after those done.
-/

module

public import LeanVM.Guest.Bridge.Track
public import LeanVM.Guest.Bridge.Prefix

/-!
# The tree track on the prefix class

A frame of a function in the prefix class (`prefixOk`) runs its leading atoms, then the rest of its body, which pops nothing of its own. Its body positions between flow hints are `flowPos body m`: past the leading atoms up to its `m`-th flow hint (`afterFlow`), the rest of the body after them; `flowPos body 0` is the body, where a frame enters (`Ent.enter`).

`TrackOk.flow_step`: from `flowPos body m`, moves of the track over atoms (the ones not flow popping nothing) reach `flowPos body (m + 1)`, the entries done grown by the `m`-th leading flow hint's. `prefix_track`: on a prefix function, the `m`-th ISA flow hint (in offset order, at an offset up to the first jump) compiles that hint; `prefix_witness`: a witness one pops the entry after those done, so (`stream_next`) the next of its stream.
-/

namespace LeanVM.Guest.Bridge

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- An atom the frame's flow carries: a witness or computed hint. -/
def atomFlow : Atom → Bool
  | .hint h => coreFlow h
  | _ => false

/-- The atoms after the first `m` flow hints, the atoms before each skipped. -/
def afterFlow : List Atom → ℕ → List Atom
  | as, 0 => as
  | [], _ + 1 => []
  | a :: as, m + 1 => if atomFlow a then afterFlow as m else afterFlow as (m + 1)

/-- **The body position after the `m`-th leading flow hint.** -/
def flowPos (body : List Stmt) (m : ℕ) : List Stmt :=
  (afterFlow (atomPrefix body).1 m).map Stmt.atom ++ (atomPrefix body).2

end

public section

theorem afterFlow_zero (as : List Atom) : afterFlow as 0 = as := by cases as <;> rfl

theorem flowPos_zero (body : List Stmt) : flowPos body 0 = body := by
  rw [flowPos, afterFlow_zero]; exact (atomPrefix_eq body).symm

theorem afterFlow_succ : ∀ (as : List Atom) (m : ℕ), afterFlow as (m + 1) = afterFlow (afterFlow as m) 1
  | [], 0 => rfl
  | [], _ + 1 => rfl
  | a :: as, 0 => rfl
  | a :: as, m + 1 => by
    simp only [afterFlow]
    split_ifs
    · exact afterFlow_succ as m
    · exact afterFlow_succ as (m + 1)

theorem flowOf_afterFlow : ∀ (as : List Atom) (m : ℕ), flowOf (afterFlow as m) = (flowOf as).drop m
  | as, 0 => by rw [afterFlow_zero, List.drop_zero]
  | [], _ + 1 => rfl
  | a :: as, m + 1 => by
    rw [afterFlow]
    cases a with
    | hint h =>
      cases hf : coreFlow h
      · simp only [atomFlow, hf, Bool.false_eq_true, ↓reduceIte, flowOf]
        exact flowOf_afterFlow as (m + 1)
      · simp only [atomFlow, hf, ↓reduceIte, flowOf, List.drop_succ_cons]
        exact flowOf_afterFlow as m
    | _ => simp only [atomFlow, Bool.false_eq_true, ↓reduceIte, flowOf]; exact flowOf_afterFlow as (m + 1)

theorem atom_pops_nil {rd : Reader} {σ : Val} {a : Atom} (h : atomFlow a = false) : a.pops rd σ = [] := by
  cases a with
  | hint hh => cases hh <;> simp_all [atomFlow, coreFlow, Atom.pops, Core.Hint.pops]
  | _ => rfl

theorem atom_pops_flow {rd : Reader} {σ : Val} {h : Core.Hint} : (Atom.hint h).pops rd σ = h.pops rd σ := rfl

variable {P : Core.Program} {rd : Reader} {Is : List Inst} {T : Tree}

/-- **Past the next flow hint**: from atoms `bs` before the rest `rest`, moves over atoms reach the
atoms after `bs`'s first flow hint, popping its entry, the frame's instance, function and
allocations the same. -/
theorem TrackOk.flow_one : ∀ (bs : List Atom) {rest : List Stmt} {done : List Pop} {e : Ent} {st : List Ent}
    {h0 : Core.Hint} {hs : List Core.Hint}, flowOf bs = h0 :: hs → TrackOk P rd Is T done (e :: st) →
    e.pos = bs.map Stmt.atom ++ rest →
    ∃ e', Relation.ReflTransGen (Move P rd Is) (done, e :: st) (done ++ h0.pops rd e.σ, e' :: st) ∧
      e'.pos = (afterFlow bs 1).map Stmt.atom ++ rest ∧ e'.I = e.I ∧ e'.fn = e.fn ∧ e'.nb = e.nb
  | [], _, _, _, _, _, _, hf, _, _ => by simp [flowOf] at hf
  | b :: bs, rest, done, e, st, h0, hs, hf, h, hpos => by
    have hpos' : e.pos = .atom b :: (bs.map Stmt.atom ++ rest) := by rw [hpos]; rfl
    have hm := Move.atom (P := P) (rd := rd) (Is := Is) (done := done) (st := st) hpos'
    have h1 := h.move hm
    cases hb : atomFlow b with
    | true =>
      obtain ⟨hh, rfl⟩ : ∃ hh, b = .hint hh := by cases b <;> simp_all [atomFlow]
      have hc : coreFlow hh = true := hb
      simp only [flowOf, hc, ↓reduceIte, List.cons.injEq] at hf
      obtain ⟨rfl, -⟩ := hf
      refine ⟨_, Relation.ReflTransGen.single hm, ?_, rfl, rfl, rfl⟩
      simp only [Ent.adv, afterFlow, hb, ↓reduceIte]
    | false =>
      have hp := atom_pops_nil (rd := rd) (σ := e.σ) hb
      have hf' : flowOf bs = h0 :: hs := by
        cases b with
        | hint hh =>
          have hc : coreFlow hh = false := hb
          simpa [flowOf, hc] using hf
        | _ => simpa [flowOf] using hf
      rw [hp, List.append_nil] at hm h1
      obtain ⟨e', hr, hpos2, hI, hfn, hnb⟩ := TrackOk.flow_one bs (rest := rest) hf' h1 (by simp [Ent.adv])
      refine ⟨e', Relation.ReflTransGen.head hm hr, ?_, hI, hfn, hnb⟩
      rw [hpos2]; simp only [afterFlow, hb, Bool.false_eq_true, ↓reduceIte]

/-- **From one flow position to the next**: moves over atoms take the frame from `flowPos body m`
to `flowPos body (m + 1)`, popping the `m`-th leading flow hint's entry. -/
theorem TrackOk.flow_step {body : List Stmt} {m : ℕ} {done : List Pop} {e : Ent} {st : List Ent}
    (h : TrackOk P rd Is T done (e :: st)) (hpos : e.pos = flowPos body m)
    (hm : m < (flowOf (atomPrefix body).1).length) :
    ∃ e', Relation.ReflTransGen (Move P rd Is) (done, e :: st)
        (done ++ ((flowOf (atomPrefix body).1)[m]).pops rd e.σ, e' :: st) ∧
      e'.pos = flowPos body (m + 1) ∧ e'.I = e.I ∧ e'.fn = e.fn ∧ e'.nb = e.nb := by
  have hf : flowOf (afterFlow (atomPrefix body).1 m) =
      (flowOf (atomPrefix body).1)[m] :: (flowOf (atomPrefix body).1).drop (m + 1) := by
    rw [flowOf_afterFlow, List.drop_eq_getElem_cons hm]
  obtain ⟨e', hr, hpos', hI, hfn, hnb⟩ := TrackOk.flow_one _ hf h hpos
  refine ⟨e', hr, ?_, hI, hfn, hnb⟩
  rw [hpos', flowPos, afterFlow_succ _ m]

/-- **The `m`-th ISA flow hint of a prefix function**: at an offset up to the first jump, it
compiles the hint whose entry the frame pops in going from `flowPos body m` to the next. -/
theorem prefix_track {loc : ℕ → ℕ} {body : List Stmt} {code : List OffsetInstruction}
    {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)} (hpre : prefixOk loc body code d = true) {m : ℕ}
    (hm : m < (isaFlow d).length) {done : List Pop} {e : Ent} {st : List Ent}
    (h : TrackOk P rd Is T done (e :: st)) (hpos : e.pos = flowPos body m) :
    ∃ hc : Core.Hint, compiles loc hc (isaFlow d)[m].2 = true ∧ (isaFlow d)[m].1 ≤ firstJump code ∧
      ∃ e', Relation.ReflTransGen (Move P rd Is) (done, e :: st) (done ++ hc.pops rd e.σ, e' :: st) ∧
        e'.pos = flowPos body (m + 1) ∧ e'.I = e.I ∧ e'.fn = e.fn ∧ e'.nb = e.nb := by
  obtain ⟨-, hoff, hl, hc⟩ := prefix_pairs hpre
  have hm' : m < (flowOf (atomPrefix body).1).length := hl ▸ hm
  exact ⟨_, hc m hm' hm, hoff _ (List.getElem_mem hm), h.flow_step hpos hm'⟩

/-- **A witness hint of a prefix function pops the next entry of its stream**: where the pushes
agree with the tree's pops stream by stream, the `m`-th ISA flow hint, a witness of stream `s`
into consecutive cells, compiles a witness of the frame's values `vs` whose words are the next of
`s` after the entries done. -/
theorem prefix_witness {loc : ℕ → ℕ} {body : List Stmt} {code : List OffsetInstruction}
    {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)} (hpre : prefixOk loc body code d = true) {m : ℕ}
    (hm : m < (isaFlow d).length) {s : String} {base len : ℕ}
    (hw : (isaFlow d)[m].2 = .witnessStack s base len) {done : List Pop} {e : Ent} {st : List Ent}
    (h : TrackOk P rd Is T done (e :: st)) (hpos : e.pos = flowPos body m) {qs : List Pop}
    (hs : SameStreams (T.pops P rd) qs) :
    ∃ vs : List V, vs.length = len ∧ consecutive loc base vs = true ∧
      (qs.filter (·.1 == s))[(done.filter (·.1 == s)).length]? = some (s, vs.map e.σ) := by
  obtain ⟨hc, hcomp, -, e', hr, -⟩ := prefix_track hpre hm h hpos
  rw [hw] at hcomp
  rcases hc with _ | _ | _ | _ | _ | _ | _ | _ | _ | _
  all_goals try (simp [compiles] at hcomp; done)
  rename_i s' dst
  cases dst with
  | heap => simp [compiles] at hcomp
  | stack vs =>
    simp only [compiles, Bool.and_eq_true, beq_iff_eq] at hcomp
    obtain ⟨⟨rfl, hlen⟩, hcons⟩ := hcomp
    refine ⟨vs, hlen, hcons, ?_⟩
    have := (h.moves hr).pops
    simp only [Core.Hint.pops, Dest.words, List.append_assoc, List.singleton_append] at this
    exact stream_next hs this.symm

end

end LeanVM.Guest.Bridge
