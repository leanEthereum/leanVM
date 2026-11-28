/-
  LeanVM.Guest.Memory.RetempA

  Re-choosing the temporaries of a call tree placed by the aligned allocator
  (`Memory/Retemp.lean`'s re-choice, the callees at `kidPosA`).
-/

module

public import LeanVM.Guest.Memory.Retemp
public import LeanVM.Guest.Memory.RegionsA

/-!
# Re-choosing temporaries, aligned

`Tree.retempA P fs al ν p t`: `Tree.retemp`, the callees placed by the aligned allocator. It keeps
the name, the block and the end (`shape_retempA`), so the callees' positions (`kidPosA_retempKidsA`)
and the words (`wordsA_retempA`); the re-chosen tree is valid on a reader giving it what it reads
(`retempA_valid`), its `HeapBuf`s and placement kept (`bufsOk_retempA`, `placed_retempA`). The
congruences and the paths are `Retemp.lean`'s.
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

variable (P : Core.Program) (fs : String → ℕ) (al : String → Bool) (ν : ℕ → String → Val → V → E)

mutual
/-- **The re-chosen tree**: every instance's temporaries re-chosen, placed from `pos`. -/
def Tree.retempA (pos : ℕ × ℕ) : Tree → Tree
  | .node f σ bufs kids => .node f (retempVal P ν pos.1 f σ) bufs
      (Tree.retempKidsA (kidPosA fs P.loop al pos f bufs kids) kids)
  | .phantom f σ => .phantom f σ

/-- The re-chosen callees at `ps`. -/
def Tree.retempKidsA : List (ℕ × ℕ) → List Tree → List Tree
  | _, [] => []
  | [], k :: ks => k :: ks
  | p :: ps, k :: ks => k.retempA p :: Tree.retempKidsA ps ks
end

variable {P fs al ν}

theorem retempA_node {pos : ℕ × ℕ} {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} :
    (Tree.node f σ bufs kids).retempA P fs al ν pos = .node f (retempVal P ν pos.1 f σ) bufs
      (Tree.retempKidsA P fs al ν (kidPosA fs P.loop al pos f bufs kids) kids) := by
  rw [Tree.retempA]

theorem retempA_phantom {pos : ℕ × ℕ} {f : String} {σ : Val} :
    (Tree.phantom f σ).retempA P fs al ν pos = .phantom f σ := by
  rw [Tree.retempA]

theorem retempKidsA_cons {p : ℕ × ℕ} {ps : List (ℕ × ℕ)} {k : Tree} {ks : List Tree} :
    Tree.retempKidsA P fs al ν (p :: ps) (k :: ks) = k.retempA P fs al ν p :: Tree.retempKidsA P fs al ν ps ks := by
  rw [Tree.retempKidsA]

theorem retempKidsA_nil {ps : List (ℕ × ℕ)} : Tree.retempKidsA P fs al ν ps [] = [] := by
  cases ps <;> rw [Tree.retempKidsA]

theorem name_retempA (pos : ℕ × ℕ) : ∀ t : Tree, (t.retempA P fs al ν pos).name = t.name
  | .node .. => by rw [retempA_node]; rfl
  | .phantom .. => by rw [retempA_phantom]

/-! ## What re-choosing keeps of the layout

A subtree's place in the aligned layout depends on its name, its block and its end (`Shape`), which
re-choosing temporaries keeps (`shape_retempA`); so the callees of a re-chosen node are where the
old node's are (`kidPosA_retempKidsA`). -/

/-- Two subtrees the aligned allocator places alike: one name, one block, one end from every
cursor. -/
def Shape (fs : String → ℕ) (lp al : String → Bool) (k k' : Tree) : Prop :=
  k.name = k'.name ∧ k.block fs lp = k'.block fs lp ∧ ∀ c, k.endA fs lp al c = k'.endA fs lp al c

section ShapeCongr

variable {lp : String → Bool}

theorem blockLast_congr : ∀ {ks ks' : List Tree}, List.Forall₂ (Shape fs lp al) ks ks' →
    Tree.blockLast fs lp ks = Tree.blockLast fs lp ks'
  | [], [], _ => rfl
  | [k], [k'], .cons h _ => by rw [Tree.blockLast, Tree.blockLast]; exact h.2.1
  | k :: k₁ :: ks, k' :: k₁' :: ks', .cons _ h => by
      rw [Tree.blockLast, Tree.blockLast]; exact blockLast_congr h
  | [_], _ :: _ :: _, .cons _ h => by cases h
  | _ :: _ :: _, [_], .cons _ h => by cases h

theorem endF_congr : ∀ {ks ks' : List Tree}, List.Forall₂ (Shape fs lp al) ks ks' →
    ∀ c, Tree.endF fs lp al c ks = Tree.endF fs lp al c ks'
  | [], [], _, c => rfl
  | k :: ks, k' :: ks', .cons h hs, c => by
      rw [endF_cons, endF_cons, h.1, h.2.1, h.2.2]; exact endF_congr hs _

theorem endL_congr : ∀ {ks ks' : List Tree}, List.Forall₂ (Shape fs lp al) ks ks' →
    ∀ c, Tree.endL fs lp al c ks = Tree.endL fs lp al c ks'
  | [], [], _, c => rfl
  | [k], [k'], .cons h _, c => by rw [endL_one, endL_one]; exact h.2.2 c
  | k :: k₁ :: ks, k' :: k₁' :: ks', .cons h hs, c => by
      rw [endL_cons, endL_cons, h.1, h.2.1, h.2.2]; exact endL_congr hs _
  | [_], _ :: _ :: _, .cons _ h, _ => by cases h
  | _ :: _ :: _, [_], .cons _ h, _ => by cases h

theorem posF_congr : ∀ {ks ks' : List Tree}, List.Forall₂ (Shape fs lp al) ks ks' →
    ∀ c, posF fs lp al c ks = posF fs lp al c ks'
  | [], [], _, c => rfl
  | k :: ks, k' :: ks', .cons h hs, c => by
      simp only [posF, h.1, h.2.1, h.2.2, posF_congr hs]

theorem posL_congr : ∀ {ks ks' : List Tree}, List.Forall₂ (Shape fs lp al) ks ks' →
    ∀ tl c, posL fs lp al tl c ks = posL fs lp al tl c ks'
  | [], [], _, _, _ => rfl
  | [_], [_], .cons _ _, _, _ => rfl
  | k :: k₁ :: ks, k' :: k₁' :: ks', .cons h hs, tl, c => by
      simp only [posL, h.1, h.2.1, h.2.2, posL_congr hs]
  | [_], _ :: _ :: _, .cons _ h, _, _ => by cases h
  | _ :: _ :: _, [_], .cons _ h, _, _ => by cases h

theorem kidPosA_congr {ks ks' : List Tree} (h : List.Forall₂ (Shape fs lp al) ks ks') (p : ℕ × ℕ)
    (f : String) (bufs : List ℕ) : kidPosA fs lp al p f bufs ks = kidPosA fs lp al p f bufs ks' := by
  unfold kidPosA
  rw [posF_congr h, posL_congr h]

theorem shape_node {f : String} {σ σ' : Val} {bufs : List ℕ} {ks ks' : List Tree}
    (h : List.Forall₂ (Shape fs lp al) ks ks') :
    Shape fs lp al (.node f σ bufs ks) (.node f σ' bufs ks') := by
  refine ⟨rfl, ?_, fun c => ?_⟩
  · rw [Tree.block, Tree.block, blockLast_congr h]
  · rw [endA_node, endA_node, endF_congr h, endL_congr h]

end ShapeCongr

mutual
/-- **Re-choosing keeps a subtree's shape.** -/
theorem shape_retempA : ∀ (t : Tree) (pos : ℕ × ℕ), Shape fs P.loop al (t.retempA P fs al ν pos) t
  | .node f σ bufs kids, pos => by
      rw [retempA_node]
      exact shape_node (shapeKids_retempA kids _ (by rw [length_kidPosA]))
  | .phantom .., pos => by rw [retempA_phantom]; exact ⟨rfl, rfl, fun _ => rfl⟩

/-- `shape_retempA` for the callees. -/
theorem shapeKids_retempA : ∀ (ks : List Tree) (ps : List (ℕ × ℕ)), ps.length = ks.length →
    List.Forall₂ (Shape fs P.loop al) (Tree.retempKidsA P fs al ν ps ks) ks
  | [], _, _ => by rw [retempKidsA_nil]; exact .nil
  | _ :: _, [], h => absurd h (by simp)
  | k :: ks, p :: ps, h => by
      rw [retempKidsA_cons]
      exact .cons (shape_retempA k p) (shapeKids_retempA ks ps (by simpa using h))
end

theorem block_retempA (t : Tree) (pos : ℕ × ℕ) :
    (t.retempA P fs al ν pos).block fs P.loop = t.block fs P.loop := (shape_retempA t pos).2.1

theorem endA_retempA (t : Tree) (pos : ℕ × ℕ) (c : ℕ) :
    (t.retempA P fs al ν pos).endA fs P.loop al c = t.endA fs P.loop al c := (shape_retempA t pos).2.2 c

theorem wordsA_retempA (t : Tree) (pos : ℕ × ℕ) :
    (t.retempA P fs al ν pos).wordsA fs P.loop al = t.wordsA fs P.loop al := by
  unfold Tree.wordsA
  rw [block_retempA, endA_retempA]

/-- The callees of a re-chosen node are where the old node's are. -/
theorem kidPosA_retempKidsA {pos : ℕ × ℕ} {f : String} {bufs : List ℕ} {kids : List Tree} :
    kidPosA fs P.loop al pos f bufs (Tree.retempKidsA P fs al ν (kidPosA fs P.loop al pos f bufs kids) kids) =
      kidPosA fs P.loop al pos f bufs kids :=
  kidPosA_congr (shapeKids_retempA kids _ (by rw [length_kidPosA])) pos f bufs


/-! ## Validity -/

variable (P fs al ν) (rd rd0 : Reader)

mutual
/-- **What a reader must give a re-chosen tree**: every atom of a path without temporaries
reads what `rd0` reads, and every temporary read (a range check's, a touch's) reads the new
temporary. -/
def Tree.ReadsAsA : ℕ × ℕ → Tree → Prop
  | pos, t@(.node f σ _ kids) =>
      (∀ a, Ev.atom a ∈ t.events P → atomTmps a = [] → ∀ q ∈ atomEqns σ a, rd q.1 = rd0 q.1) ∧
      (∀ a, Ev.atom a ∈ t.events P → ∀ r ∈ tmpReads σ a, rd r.2 = some (ν pos.1 f σ r.1)) ∧
      Tree.ReadsAsKidsA (kidPosA fs P.loop al pos f t.bufs kids) kids
  | _, .phantom .. => True

/-- `Tree.ReadsAsA` of the callees at `ps`. -/
def Tree.ReadsAsKidsA : List (ℕ × ℕ) → List Tree → Prop
  | _, [] => True
  | [], _ :: _ => True
  | p :: ps, k :: ks => k.ReadsAsA p ∧ Tree.ReadsAsKidsA ps ks
end

variable {P fs al ν rd rd0}

theorem readsAsA_node {pos : ℕ × ℕ} {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} :
    (Tree.node f σ bufs kids).ReadsAsA P fs al ν rd rd0 pos ↔
      (∀ a, Ev.atom a ∈ (Tree.node f σ bufs kids).events P → atomTmps a = [] →
        ∀ q ∈ atomEqns σ a, rd q.1 = rd0 q.1) ∧
      (∀ a, Ev.atom a ∈ (Tree.node f σ bufs kids).events P → ∀ r ∈ tmpReads σ a,
        rd r.2 = some (ν pos.1 f σ r.1)) ∧
      Tree.ReadsAsKidsA P fs al ν rd rd0 (kidPosA fs P.loop al pos f bufs kids) kids := by
  rw [Tree.ReadsAsA]; rfl

theorem readsAsKidsA_cons {p : ℕ × ℕ} {ps : List (ℕ × ℕ)} {k : Tree} {ks : List Tree} :
    Tree.ReadsAsKidsA P fs al ν rd rd0 (p :: ps) (k :: ks) ↔
      k.ReadsAsA P fs al ν rd rd0 p ∧ Tree.ReadsAsKidsA P fs al ν rd rd0 ps ks := by
  rw [Tree.ReadsAsKidsA]

section Valid

/-- The events of a re-chosen path hold on the new reader. -/
theorem events_holds_retempA (hF : P.Fresh) {fn : Fn} {f : String} (hf : P.find? f = some fn) {fp : ℕ} {σ : Val}
    {es : List Ev} {vs : List V} (hw : walk σ fn.body = .ret es vs)
    (hes : ∀ e ∈ es, e.Holds rd0 σ)
    (hna : ∀ a, Ev.atom a ∈ es → atomTmps a = [] → ∀ q ∈ atomEqns σ a, rd q.1 = rd0 q.1)
    (hrc : ∀ a, Ev.atom a ∈ es → ∀ r ∈ tmpReads σ a, rd r.2 = some (ν fp f σ r.1)) :
    ∀ e ∈ es, e.Holds rd (retempVal P ν fp f σ) := by
  have hag := evAgree_retemp (ν := ν) hF hf (fp := fp) hw
  intro e he
  cases e with
  | atom a =>
      by_cases ht : atomTmps a = []
      · have h1 := atom_holds_agree a (hes _ he) (hna a he ht)
        refine (atom_holds_congr a fun v hv => ?_).mpr h1
        rw [ht, List.append_nil] at hv
        exact hag _ he v hv
      · refine holds_of_tmpReads ht (hes _ he) (fun v hv => hag _ he v hv) fun r hr => ?_
        rw [hrc a he r hr]
        simp [retempVal, mem_temps_of_event hf hw he hr]
  | inK c =>
      have := hes _ he
      simp only [Ev.Holds] at this ⊢
      rw [hag _ he c (by simp [Ev.uses])]
      exact this
  | call _ _ _ => trivial
  | skip _ _ => trivial

mutual
/-- **The re-chosen tree is valid** on a reader giving it what it reads. -/
theorem retempA_valid (hF : P.Fresh) : ∀ (t : Tree) (pos : ℕ × ℕ) {args rets : List E}, t.Valid P rd0 args rets →
    t.ReadsAsA P fs al ν rd rd0 pos → (t.retempA P fs al ν pos).Valid P rd args rets
  | .node f σ bufs kids, pos, args, rets, ⟨fn, hf, hp, es, vs, hw, hr, hes, hk⟩, hra => by
      have hag := evAgree_retemp (ν := ν) hF hf (fp := pos.1) hw
      have hw' : walk (retempVal P ν pos.1 f σ) fn.body = .ret es vs := by
        rw [walk_retemp hF hf]; exact hw
      have hev : (Tree.node f σ bufs kids).events P = es := events_node hf hw
      rw [readsAsA_node, hev] at hra
      have hvs : vs.map (retempVal P ν pos.1 f σ) = vs.map σ := by
        have := walk_within (σ := σ) fn.body
        rw [hw] at this
        exact List.map_congr_left fun v hv => retempVal_uses hF hf (this.2.2 v hv)
      rw [retempA_node]
      refine ⟨fn, hf, by rw [retempVal_params hF hf]; exact hp, es, vs, hw', by rw [hvs]; exact hr,
        events_holds_retempA hF hf hw hes hra.1 hra.2.1, ?_⟩
      refine retempKidsA_valid hF kids σ _ (calls es) _ (by rw [length_kidPosA])
        (fun c hc v hv => ?_) hk hra.2.2
      obtain ⟨e, he, hce⟩ := List.mem_filterMap.mp hc
      cases e with
      | call g a r =>
          cases hce
          exact hag _ he v (by simpa [Ev.uses] using hv)
      | skip g a =>
          cases hce
          exact hag _ he v (by simpa [Ev.uses] using hv)
      | atom _ => simp [Ev.call?] at hce
      | inK _ => simp [Ev.call?] at hce
  | .phantom .., _, _, _, h, _ => h.elim

/-- `retempA_valid` for the callees. -/
theorem retempKidsA_valid (hF : P.Fresh) : ∀ (ks : List Tree) (σ σ' : Val) (cs : List Call) (ps : List (ℕ × ℕ)),
    ps.length = ks.length → (∀ c ∈ cs, ∀ v ∈ c.args ++ c.rets, σ' v = σ v) →
    Tree.KidsValid P rd0 σ cs ks → Tree.ReadsAsKidsA P fs al ν rd rd0 ps ks →
      Tree.KidsValid P rd σ' cs (Tree.retempKidsA P fs al ν ps ks)
  | [], _, _, [], _, _, _, _, _ => by rw [retempKidsA_nil]; trivial
  | _ :: _, _, _, _, [], hl, _, _, _ => absurd hl (by simp)
  | k :: ks, σ, σ', c :: cs, p :: ps, hl, hag, ⟨hn, hc, hks⟩, hra => by
      rw [readsAsKidsA_cons] at hra
      rw [retempKidsA_cons]
      have hargs : c.args.map σ' = c.args.map σ :=
        List.map_congr_left fun v hv => hag c List.mem_cons_self v (List.mem_append_left _ hv)
      have hrets : c.rets.map σ' = c.rets.map σ :=
        List.map_congr_left fun v hv => hag c List.mem_cons_self v (List.mem_append_right _ hv)
      refine ⟨by rw [name_retempA]; exact hn, ?_, retempKidsA_valid hF ks σ σ' cs ps (by simpa using hl)
        (fun c' hc' => hag c' (List.mem_cons_of_mem _ hc')) hks hra.2⟩
      by_cases ht : c.taken = true
      · rw [ite_eq_left ht] at hc ⊢
        rw [hargs, hrets]
        exact retempA_valid hF k p hc hra.1
      · rw [ite_eq_right ht] at hc ⊢
        obtain ⟨⟨f, σk, rfl⟩, hph⟩ := hc
        rw [retempA_phantom, hargs]
        exact ⟨⟨f, σk, rfl⟩, hph⟩
  | [], _, _, _ :: _, _, _, _, h, _ => h.elim
  | _ :: _, _, _, [], _ :: _, _, _, h, _ => h.elim
end

end Valid


/-! ## What a re-chosen valid tree keeps -/

section Keep

mutual
theorem bufsOk_retempA (hF : P.Fresh) : ∀ (t : Tree) (pos : ℕ × ℕ) {args rets : List E}, t.Valid P rd0 args rets →
    t.BufsOk P → (t.retempA P fs al ν pos).BufsOk P
  | .node f σ bufs kids, pos, _, _, ⟨fn, hf, _, es, vs, hw, _, _, hk⟩, hb => by
      rw [Tree.BufsOk, events_node hf hw] at hb
      rw [retempA_node, Tree.BufsOk, events_retemp hF, events_node hf hw (bufs := bufs) (kids := kids),
        allocs_congr (evAgree_retemp hF hf hw)]
      exact ⟨hb.1, bufsOkKids_retempA hF kids σ (calls es) _ hk hb.2⟩
  | .phantom .., pos, _, _, _, _ => by rw [retempA_phantom, Tree.BufsOk]; trivial

theorem bufsOkKids_retempA (hF : P.Fresh) : ∀ (ks : List Tree) (σ : Val) (cs : List Call) (ps : List (ℕ × ℕ)),
    Tree.KidsValid P rd0 σ cs ks → Tree.BufsOkKids P ks →
      Tree.BufsOkKids P (Tree.retempKidsA P fs al ν ps ks)
  | [], _, _, _, _, _ => by rw [retempKidsA_nil, Tree.BufsOkKids]; trivial
  | _ :: _, _, _, [], _, h => by rw [Tree.retempKidsA]; exact h
  | k :: ks, σ, c :: cs, p :: ps, ⟨_, hc, hks⟩, hb => by
      rw [Tree.BufsOkKids] at hb
      rw [retempKidsA_cons, Tree.BufsOkKids]
      refine ⟨?_, bufsOkKids_retempA hF ks σ cs ps hks hb.2⟩
      by_cases ht : c.taken = true
      · rw [ite_eq_left ht] at hc
        exact bufsOk_retempA hF k p hc hb.1
      · rw [ite_eq_right ht] at hc
        obtain ⟨⟨f, σk, rfl⟩, -⟩ := hc
        rw [retempA_phantom, Tree.BufsOk]; trivial
  | _ :: _, _, [], _ :: _, h, _ => h.elim
end

variable {cert : String → V → ℕ}

mutual
theorem placed_retempA (hF : P.Fresh) : ∀ (t : Tree) (pos : ℕ × ℕ) {args rets : List E}, t.Valid P rd0 args rets →
    t.PlacedA P fs al cert pos → (t.retempA P fs al ν pos).PlacedA P fs al cert pos
  | .node f σ bufs kids, pos, _, _, ⟨fn, hf, _, es, vs, hw, _, _, hk⟩, hp => by
      rw [placedA_node, events_node hf hw] at hp
      have hag := evAgree_retemp (ν := ν) hF hf (fp := pos.1) hw
      rw [retempA_node, placedA_node, events_retemp hF, events_node hf hw (bufs := bufs) (kids := kids),
        kidPosA_retempKidsA]
      refine ⟨⟨by rw [allocDsts_congr hag]; exact hp.1.1, fun q hq => by
        rw [addrs_congr hag q hq]; exact hp.1.2 q hq⟩, ?_⟩
      exact placedKids_retempA hF kids σ (calls es) _ hk hp.2
  | .phantom .., pos, _, _, _, _ => by rw [retempA_phantom]; exact placedA_phantom

theorem placedKids_retempA (hF : P.Fresh) : ∀ (ks : List Tree) (σ : Val) (cs : List Call) (ps : List (ℕ × ℕ)),
    Tree.KidsValid P rd0 σ cs ks → Tree.PlacedKidsA P fs al cert ps ks →
      Tree.PlacedKidsA P fs al cert ps (Tree.retempKidsA P fs al ν ps ks)
  | [], _, _, _, _, _ => by rw [retempKidsA_nil]; exact placedKidsA_nil
  | _ :: _, _, _, [], _, h => by rw [Tree.retempKidsA]; exact h
  | k :: ks, σ, c :: cs, p :: ps, ⟨_, hc, hks⟩, hp => by
      rw [placedKidsA_cons] at hp
      rw [retempKidsA_cons, placedKidsA_cons]
      refine ⟨?_, placedKids_retempA hF ks σ cs ps hks hp.2⟩
      by_cases ht : c.taken = true
      · rw [ite_eq_left ht] at hc
        exact placed_retempA hF k p hc hp.1
      · rw [ite_eq_right ht] at hc
        obtain ⟨⟨f, σk, rfl⟩, -⟩ := hc
        rw [retempA_phantom]; exact placedA_phantom
  | _ :: _, _, [], _ :: _, h, _ => h.elim
end

end Keep

end
end LeanVM.Guest.Memory
