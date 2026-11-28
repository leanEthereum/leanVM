/-
  LeanVM.Guest.Complete.PopSkel

  A node's pops through its skeleton: its witness hints and its callees, in order.
-/

module

public import LeanVM.Guest.Complete.MainCalleesA
public import LeanVM.Guest.Complete.Free
public import LeanVM.Guest.Memory.Straight

/-!
# Pop skeletons

A node's pops (`splice`) depend on its events only through its witness hints and its calls, in
order: `evSkel` keeps those (`PItem.wit`, `PItem.kid`), `skelPops` reads them back
(`splice_skel`), and a straight block's skeleton is its statements' (`straight_skel`), whatever
its `callIf`s decide.

The callees' side: `KOk rd Qs bs Ps` pairs each callee's post `Q`, whether it is entered `b` and
the list `P` it should pop; then the callees' trees pop their lists stream by stream and are exact
(`kOk_kids`), and so does the node's skeleton (`skelPops_streams`).
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-! ## The skeleton -/

/-- What a block pops, up to the words: a witness hint's entry or a callee's entries. -/
inductive PItem where
  | wit (s : String) (d : Dest)
  | kid
  deriving DecidableEq

/-- An atom's skeleton: a witness hint's entry. -/
def atomSkel : Atom → List PItem
  | .hint (.witness s d) => [.wit s d]
  | _ => []

/-- An event's skeleton. -/
def evSkel : Ev → List PItem
  | .atom a => atomSkel a
  | .inK _ => []
  | .call .. => [.kid]
  | .skip .. => [.kid]

/-- A straight statement's skeleton. -/
def stmtSkel : Stmt → List PItem
  | .atom a => atomSkel a
  | .call .. => [.kid]
  | .callIf .. => [.kid]
  | _ => []

/-- A skeleton's entries: a witness hint's words under `σ`, a callee's entries from `ks` in turn. -/
def skelPops (rd : Reader) (σ : Val) : List PItem → List (List Pop) → List Pop
  | [], _ => []
  | .wit s d :: is, ks => (s, d.words rd σ) :: skelPops rd σ is ks
  | .kid :: is, ks => ks.headD [] ++ skelPops rd σ is ks.tail

section
variable {rd : Reader} {σ : Val}

theorem atom_pops_skel (a : Atom) (is : List PItem) (ks : List (List Pop)) :
    a.pops rd σ ++ skelPops rd σ is ks = skelPops rd σ (atomSkel a ++ is) ks := by
  cases a with
  | hint h => cases h <;> simp [Atom.pops, Hint.pops, atomSkel, skelPops]
  | _ => simp [Atom.pops, atomSkel]

/-- **A node's entries are its skeleton's.** -/
theorem splice_skel : ∀ (es : List Ev) (ks : List (List Pop)),
    splice rd σ es ks = skelPops rd σ (es.flatMap evSkel) ks
  | [], _ => by simp [splice, skelPops]
  | .atom a :: es, ks => by
      simp only [splice, List.flatMap_cons, evSkel]
      rw [splice_skel es ks, atom_pops_skel]
  | .inK _ :: es, ks => by
      simp only [splice, List.flatMap_cons, evSkel, List.nil_append]
      exact splice_skel es ks
  | .call .. :: es, ks => by
      simp only [splice, List.flatMap_cons, evSkel, List.cons_append, List.nil_append, skelPops]
      rw [splice_skel es ks.tail]
  | .skip .. :: es, ks => by
      simp only [splice, List.flatMap_cons, evSkel, List.cons_append, List.nil_append, skelPops]
      rw [splice_skel es ks.tail]

theorem slEvs_skel : ∀ s : Stmt, Stmt.straight s = true → (slEvs σ s).flatMap evSkel = stmtSkel s
  | .atom a, _ => by simp [slEvs, evSkel, stmtSkel]
  | .call .., _ => by simp [slEvs, evSkel, stmtSkel]
  | .callIf c f args, _ => by by_cases h : σ c = 0 <;> simp [slEvs, h, evSkel, stmtSkel]
  | .ite .., h | .match_ .., h | .dispatch .., h | .ret _, h => by simp [Stmt.straight] at h

/-- **A straight block's skeleton** is its statements', whatever its `callIf`s decide. -/
theorem straight_skel : ∀ ss : List Stmt, ss.all Stmt.straight = true →
    (ss.flatMap (slEvs σ)).flatMap evSkel = ss.flatMap stmtSkel
  | [], _ => rfl
  | s :: ss, h => by
      simp only [List.all_cons, Bool.and_eq_true] at h
      rw [List.flatMap_cons, List.flatMap_append, slEvs_skel s h.1, straight_skel ss h.2, List.flatMap_cons]

end

/-! ## Streams -/

theorem sameStreams_cons {p : Pop} {a b : List Pop} (h : SameStreams a b) : SameStreams (p :: a) (p :: b) :=
  show SameStreams ([p] ++ a) ([p] ++ b) from SameStreams.append (fun _ => rfl) h

theorem sameStreams_of_eq {a b : List Pop} (h : a = b) : SameStreams a b := h ▸ fun _ => rfl

theorem sameStreams_trans {a b c : List Pop} (h : SameStreams a b) (h' : SameStreams b c) : SameStreams a c :=
  fun s => (h s).trans (h' s)

/-- **A skeleton's entries agree stream by stream** when its callees' do. -/
theorem skelPops_streams (rd : Reader) (σ : Val) : ∀ (is : List PItem) {ks Ps : List (List Pop)},
    List.Forall₂ SameStreams ks Ps → SameStreams (skelPops rd σ is ks) (skelPops rd σ is Ps)
  | [], _, _, _ => fun _ => rfl
  | .wit _ _ :: is, _, _, h => by
      simp only [skelPops]
      exact sameStreams_cons (skelPops_streams rd σ is h)
  | .kid :: is, _, _, .nil => by
      simp only [skelPops, List.headD_nil, List.tail_nil]
      exact fun _ => rfl
  | .kid :: is, _, _, .cons h hs => by
      simp only [skelPops, List.headD_cons, List.tail_cons]
      exact SameStreams.append h (skelPops_streams rd σ is hs)

/-! ## The callees -/

/-- Each callee pops its list `P` stream by stream and is exact: an entered one by its post `Q`, a
skipped one's list empty. -/
def KOk (rd : Reader) : List (Reader → Tree → Prop) → List Bool → List (List Pop) → Prop
  | Q :: Qs, b :: bs, P :: Ps =>
    (b = true → ∀ t, Q rd t → PopsPost P rd t) ∧ (b = false → P = []) ∧ KOk rd Qs bs Ps
  | [], [], [] => True
  | _, _, _ => False

theorem kOk_append {rd : Reader} : ∀ {Qs : List (Reader → Tree → Prop)} {bs : List Bool} {Ps : List (List Pop)}
    {Qs' : List (Reader → Tree → Prop)} {bs' : List Bool} {Ps' : List (List Pop)},
    KOk rd Qs bs Ps → KOk rd Qs' bs' Ps' → KOk rd (Qs ++ Qs') (bs ++ bs') (Ps ++ Ps')
  | [], [], [], _, _, _, _, h' => h'
  | _ :: _, _ :: _, _ :: _, _, _, _, ⟨h1, h2, h⟩, h' => ⟨h1, h2, kOk_append h h'⟩
  | [], _ :: _, _, _, _, _, h, _ => by simp [KOk] at h
  | [], [], _ :: _, _, _, _, h, _ => by simp [KOk] at h
  | _ :: _, [], _, _, _, _, h, _ => by simp [KOk] at h
  | _ :: _, _ :: _, [], _, _, _, h, _ => by simp [KOk] at h

/-- A callee whose post pops `P`, entered. -/
theorem kOk_pops {rd : Reader} {P : List Pop} {Qs : List (Reader → Tree → Prop)} {bs : List Bool}
    {Ps : List (List Pop)} (h : KOk rd Qs bs Ps) : KOk rd (PopsPost P :: Qs) (true :: bs) (P :: Ps) :=
  ⟨fun _ _ ht => ht, ⟨fun h => absurd h (by simp), h⟩⟩

/-- A callee with no witness hints, entered. -/
theorem kOk_free {rd : Reader} {Qs : List (Reader → Tree → Prop)} {bs : List Bool} {Ps : List (List Pop)}
    (h : KOk rd Qs bs Ps) : KOk rd (FreePost :: Qs) (true :: bs) ([] :: Ps) :=
  ⟨fun _ t ht => ⟨by rw [ht.1]; exact fun _ => rfl, ht.2⟩, ⟨fun h => absurd h (by simp), h⟩⟩

/-- **The callees' trees pop their lists stream by stream**, every node exact. -/
theorem kOk_kids {rd : Reader} {σ : Val} : ∀ {cs : List Call} {Qs : List (Reader → Tree → Prop)} {ts : List Tree}
    {Ps : List (List Pop)}, KOk rd Qs (cs.map Call.taken) Ps → Tree.KidsValid coreProgram rd σ cs ts →
    KidsPost rd Qs cs ts →
    List.Forall₂ SameStreams (Tree.popsKids coreProgram rd ts) Ps ∧ Tree.EveryKids (ExactAt coreProgram rd) ts
  | [], Qs, [], Ps, hk, _, _ => by
      cases Qs <;> cases Ps <;> simp only [List.map_nil, KOk] at hk
      exact ⟨by rw [Tree.popsKids]; exact .nil, by rw [Tree.EveryKids]; trivial⟩
  | [], _, _ :: _, _, _, hv, _ => by simp [Tree.KidsValid] at hv
  | _ :: _, _, [], _, _, hv, _ => by simp [Tree.KidsValid] at hv
  | c :: cs, Qs, t :: ts, Ps, hk, hv, hq => by
      cases Qs with
      | nil => simp [KOk] at hk
      | cons Q Qs =>
        cases Ps with
        | nil => simp [KOk] at hk
        | cons P Ps =>
          obtain ⟨h1, h0, hk⟩ := hk
          simp only [Tree.KidsValid] at hv
          obtain ⟨-, hvt, hv⟩ := hv
          rw [kidsPost_cons] at hq
          obtain ⟨hqt, hq⟩ := hq
          obtain ⟨ih1, ih2⟩ := kOk_kids hk hv hq
          have ht : SameStreams (t.pops coreProgram rd) P ∧ t.Every (ExactAt coreProgram rd) := by
            cases hc : c.taken
            · rw [hc] at hvt
              simp only [Bool.false_eq_true, ↓reduceIte] at hvt
              obtain ⟨⟨f, σ', rfl⟩, -⟩ := hvt
              rw [h0 hc]
              exact ⟨fun _ => by simp [Tree.pops], Tree.every_phantom⟩
            · exact h1 hc t (hqt hc)
          rw [Tree.popsKids, Tree.EveryKids]
          exact ⟨.cons ht.1 ih1, ht.2, ih2⟩

/-! ## Calls of straight blocks -/

/-- Whether a frame of condition `c` is entered under `σ`. -/
noncomputable def takenOf (σ : Val) : Option V → Bool
  | none => true
  | some c => decide (σ c ≠ 0)

theorem straight_taken (σ : Val) (ss : List Stmt) (h : ss.all Stmt.straight = true) :
    (calls (ss.flatMap (slEvs σ))).map Call.taken = ((ss.filterMap Stmt.callS).map (·.1)).map (takenOf σ) := by
  rw [(straight_parts σ ss h).2.2.2, List.map_map, List.map_map]
  congr 1
  funext x
  obtain ⟨c, f, a, r⟩ := x
  cases c <;> rfl

end
end LeanVM.Guest.Complete
