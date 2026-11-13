/-
  LeanVM.Guest.B1.Sig.PopsKit

  Pops of blocks beyond `FallPops`: they depend only on the values a block names (`FallPops.congr`), survive a renaming of its values (`FallPops.rename`), and a block setting up calls pops its own entries with its callees' spliced in (`SplicePops`).
-/

module

public import LeanVM.Guest.Pops
public import LeanVM.Guest.B1.Sig.Frame

/-!
# Pops, generically

* `walk_congr_pops`, `FallPops.congr`, `SplicePops.congr`: a block's path and pops depend only on the values it names;
* `walk_rename`, `FallPops.rename`: a renamed block pops what the original pops under the renamed valuation;
* `SplicePops`: a block falling through, its calls' entries `ks` spliced in; `SplicePops.append`, `SplicePops.call`, `Tree.pops_of_splice`;
* `retPops_of_fallPops`: a block returning after a block popping `ps` pops `ps`;
* `SameStreams.refl`, `.symm`, `.trans`, `sameStreams_flatMap_split`: stream-by-stream equality.
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.B1.Sig

@[expose] public section

variable {rd : Reader}

/-! ## Outcomes -/

/-- The events of an outcome. -/
def Out.evList : Out → List Ev
  | .fall es => es
  | .ret es _ => es
  | .stuck => []

theorem Out.mem_evList_pre {e : Ev} (es : List Ev) : ∀ (o : Out), e ∈ (o.pre es).evList → e ∈ es ∨ e ∈ o.evList
  | .fall _, h | .ret _ _, h => by simpa [Out.pre, Out.evList] using h
  | .stuck, h => by simp [Out.pre, Out.evList] at h

theorem Out.mem_evList_seq {e : Ev} (k : Out) : ∀ (o : Out), e ∈ (o.seq k).evList → e ∈ o.evList ∨ e ∈ k.evList
  | .fall es, h => by
      simp only [Out.seq] at h
      rcases Out.mem_evList_pre es k h with h | h
      · exact Or.inl h
      · exact Or.inr h
  | .ret _ _, h => Or.inl h
  | .stuck, h => by simp [Out.seq, Out.evList] at h

/-! ## Congruence -/

section Congr

variable {σ σ' : Val}

theorem Atom.pops_congr (a : Atom) (h : ∀ v ∈ a.vals, σ v = σ' v) : a.pops rd σ = a.pops rd σ' := by
  cases a with
  | hint x =>
      cases x with
      | witness s d =>
          cases d with
          | stack cs =>
              simp only [Atom.vals, Hint.vals, Dest.vals] at h
              simp only [Atom.pops, Hint.pops, Dest.words, map_congr h]
          | heap p off len =>
              simp only [Atom.vals, Hint.vals, Dest.vals, List.mem_singleton, forall_eq] at h
              simp only [Atom.pops, Hint.pops, Dest.words, h]
      | _ => rfl
  | _ => rfl

/-- An event's pops agree under both valuations. -/
abbrev PopsAgree (rd : Reader) (σ σ' : Val) (o : Out) : Prop := ∀ e ∈ o.evList, Ev.pops rd σ e = Ev.pops rd σ' e

theorem pick_congr_pops {x : V} (hx : σ x = σ' x) (args rets : List V) :
    ∀ (j : Nat) (fs : List String), pick σ x args rets j fs = pick σ' x args rets j fs ∧
      PopsAgree rd σ σ' (pick σ x args rets j fs)
  | _, [] => ⟨rfl, fun _ h => by simp [pick, Out.evList] at h⟩
  | j, f :: fs => by
      simp only [pick, hx]
      split
      · exact ⟨rfl, fun e h => by simp [Out.evList] at h; subst h; rfl⟩
      · exact pick_congr_pops hx args rets (j + 1) fs

mutual
theorem walk1_congr_pops : ∀ (s : Stmt), (∀ v ∈ s.vals, σ v = σ' v) →
    walk1 σ s = walk1 σ' s ∧ PopsAgree rd σ σ' (walk1 σ s)
  | .atom a, h => ⟨rfl, fun e he => by
      simp only [walk1, Out.evList, List.mem_singleton] at he
      subst he
      exact Atom.pops_congr a h⟩
  | .ite c z n, h => by
      simp only [Stmt.vals, List.mem_cons, List.mem_append] at h
      have hz := walk_congr_pops z fun v hv => h v (Or.inl (Or.inr hv))
      have hn := walk_congr_pops n fun v hv => h v (Or.inr hv)
      refine ⟨by simp only [walk1, h c (Or.inl (Or.inl rfl)), hz.1, hn.1], fun e he => ?_⟩
      simp only [walk1] at he
      rcases Out.mem_evList_pre _ _ he with he | he
      · simp only [List.mem_singleton] at he; subst he; rfl
      · split at he
        · exact hz.2 e he
        · exact hn.2 e he
  | .match_ x arms, h => by
      simp only [Stmt.vals, List.mem_cons] at h
      exact walkArms_congr_pops x arms (h x (Or.inl rfl)) (fun v hv => h v (Or.inr hv)) 0
  | .call _ _ _, _ => ⟨rfl, fun e he => by
      simp only [walk1, Out.evList, List.mem_singleton] at he; subst he; rfl⟩
  | .callIf c _ _, h => by
      simp only [Stmt.vals, List.mem_cons] at h
      refine ⟨by simp only [walk1, h c (Or.inl rfl)], fun e he => ?_⟩
      simp only [walk1, Out.evList, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · rfl
      · split <;> rfl
  | .dispatch x _ args rets, h => by
      simp only [Stmt.vals, List.mem_cons, List.mem_append] at h
      exact pick_congr_pops (h x (Or.inl (Or.inl rfl))) args rets 0 _
  | .ret _, _ => ⟨rfl, fun e he => by simp [walk1, Out.evList] at he⟩

theorem walk_congr_pops : ∀ (ss : List Stmt), (∀ v ∈ Stmt.valsList ss, σ v = σ' v) →
    walk σ ss = walk σ' ss ∧ PopsAgree rd σ σ' (walk σ ss)
  | [], _ => ⟨rfl, fun e he => by simp [walk, Out.evList] at he⟩
  | s :: ss, h => by
      simp only [Stmt.valsList, List.mem_append] at h
      have h1 := walk1_congr_pops s fun v hv => h v (Or.inl hv)
      have h2 := walk_congr_pops ss fun v hv => h v (Or.inr hv)
      refine ⟨by simp only [walk, h1.1, h2.1], fun e he => ?_⟩
      simp only [walk] at he
      rcases Out.mem_evList_seq _ _ he with he | he
      · exact h1.2 e he
      · exact h2.2 e he

theorem walkArms_congr_pops (x : V) : ∀ (arms : List (List Stmt)), σ x = σ' x →
    (∀ v ∈ Stmt.valsArms arms, σ v = σ' v) → ∀ (j : Nat),
    walkArms σ x j arms = walkArms σ' x j arms ∧ PopsAgree rd σ σ' (walkArms σ x j arms)
  | [], _, _, _ => ⟨rfl, fun e he => by simp [walkArms, Out.evList] at he⟩
  | a :: as, hx, h, j => by
      simp only [Stmt.valsArms, List.mem_append] at h
      have ha := walk_congr_pops a fun v hv => h v (Or.inl hv)
      have hs := walkArms_congr_pops x as hx (fun v hv => h v (Or.inr hv)) (j + 1)
      refine ⟨by simp only [walkArms, hx, ha.1, hs.1], fun e he => ?_⟩
      simp only [walkArms] at he
      split at he
      · exact ha.2 e he
      · exact hs.2 e he
end

theorem evPops_congr {es : List Ev} (h : ∀ e ∈ es, Ev.pops rd σ e = Ev.pops rd σ' e) :
    evPops rd σ es = evPops rd σ' es :=
  List.flatMap_congr h

/-- **A block's pops depend only on the values it names.** -/
theorem FallPops.congr {ss : List Stmt} {ps : List Pop} (h : ∀ v ∈ Stmt.valsList ss, σ v = σ' v)
    (hf : FallPops rd σ ss ps) : FallPops rd σ' ss ps := by
  obtain ⟨es, hw, hc, rfl⟩ := hf
  obtain ⟨e1, e2⟩ := walk_congr_pops (rd := rd) ss h
  refine ⟨es, by rw [← e1, hw], hc, (evPops_congr fun e he => ?_).symm⟩
  exact e2 e (by rw [hw]; exact he)

theorem FallPops.agree {ss : List Stmt} {ps : List Pop} {hi : Nat} (hb : NumBelow hi (Stmt.valsList ss))
    (hag : AgreeBelow hi σ σ') (hf : FallPops rd σ ss ps) : FallPops rd σ' ss ps :=
  hf.congr fun v hv => let ⟨k, hk, e⟩ := hb v hv; e ▸ hag k hk

end Congr

/-! ## Renaming -/

section Rename

/-- An event's values renamed. -/
def Ev.rename (r : V → V) : Ev → Ev
  | .atom a => .atom (a.rename r)
  | .inK c => .inK (r c)
  | .call f args rets => .call f (args.map r) (rets.map r)
  | .skip f args => .skip f (args.map r)

/-- An outcome's values renamed. -/
def Out.rename (r : V → V) : Out → Out
  | .fall es => .fall (es.map (Ev.rename r))
  | .ret es vs => .ret (es.map (Ev.rename r)) (vs.map r)
  | .stuck => .stuck

theorem Out.rename_pre (r : V → V) (es : List Ev) : ∀ (o : Out),
    (o.pre es).rename r = (o.rename r).pre (es.map (Ev.rename r))
  | .fall _ | .ret _ _ | .stuck => by simp [Out.pre, Out.rename]

theorem Out.rename_seq (r : V → V) (k : Out) : ∀ (o : Out), (o.seq k).rename r = (o.rename r).seq (k.rename r)
  | .fall es => by simp only [Out.seq, Out.rename_pre]; rfl
  | .ret _ _ | .stuck => rfl

variable {σ : Val} (r : V → V)

theorem pick_rename (x : V) (args rets : List V) : ∀ (j : Nat) (fs : List String),
    pick σ (r x) (args.map r) (rets.map r) j fs = (pick (σ ∘ r) x args rets j fs).rename r
  | _, [] => rfl
  | j, f :: fs => by
      simp only [pick, Function.comp_apply]
      split
      · rfl
      · exact pick_rename x args rets (j + 1) fs

mutual
theorem walk1_rename : ∀ (s : Stmt), walk1 σ (s.rename r) = (walk1 (σ ∘ r) s).rename r
  | .atom _ => rfl
  | .ite c z n => by
      simp only [Stmt.rename, walk1, walk_rename z, walk_rename n, Function.comp_apply, Out.rename_pre]
      split <;> rfl
  | .match_ x arms => by simp only [Stmt.rename, walk1, walkArms_rename x arms 0]
  | .call _ _ _ => rfl
  | .callIf c f args => by
      simp only [Stmt.rename, walk1, Out.rename, List.map_cons, List.map_nil, Function.comp_apply]
      split <;> rfl
  | .dispatch x fs args rets => by simp only [Stmt.rename, walk1, pick_rename r x args rets 0 fs]
  | .ret _ => rfl

theorem walk_rename : ∀ (ss : List Stmt), walk σ (Stmt.renameList r ss) = (walk (σ ∘ r) ss).rename r
  | [] => rfl
  | s :: ss => by simp only [Stmt.renameList, walk, walk1_rename s, walk_rename ss, Out.rename_seq]

theorem walkArms_rename (x : V) : ∀ (arms : List (List Stmt)) (j : Nat),
    walkArms σ (r x) j (Stmt.renameArms r arms) = (walkArms (σ ∘ r) x j arms).rename r
  | [], _ => rfl
  | a :: as, j => by
      simp only [Stmt.renameArms, walkArms, walk_rename a, walkArms_rename x as (j + 1), Function.comp_apply]
      split <;> rfl
end

theorem Atom.pops_rename (a : Atom) : (a.rename r).pops rd σ = a.pops rd (σ ∘ r) := by
  cases a with
  | hint x =>
      cases x with
      | witness s d =>
          cases d <;> simp [Atom.rename, Hint.rename, Dest.rename, Atom.pops, Hint.pops, Dest.words]
      | _ => rfl
  | _ => rfl

theorem evPops_rename (es : List Ev) : evPops rd σ (es.map (Ev.rename r)) = evPops rd (σ ∘ r) es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
      simp only [List.map_cons, evPops, List.flatMap_cons] at ih ⊢
      rw [ih]
      cases e <;> simp [Ev.rename, Ev.pops, Atom.pops_rename]

theorem calls_rename_nil {es : List Ev} (h : calls es = []) : calls (es.map (Ev.rename r)) = [] := by
  induction es with
  | nil => rfl
  | cons e es ih =>
      cases e <;> simp_all [calls, Ev.call?, Ev.rename]

/-- **A renamed block pops what the block pops under the renamed valuation.** -/
theorem FallPops.rename {ss : List Stmt} {ps : List Pop} (h : FallPops rd (σ ∘ r) ss ps) :
    FallPops rd σ (Stmt.renameList r ss) ps := by
  obtain ⟨es, hw, hc, rfl⟩ := h
  exact ⟨es.map (Ev.rename r), by rw [walk_rename, hw]; rfl, calls_rename_nil r hc, evPops_rename r es⟩

end Rename

/-! ## Returning -/

theorem walk_append_fall' {σ : Val} : ∀ {xs : List Stmt} {es : List Ev} (ys : List Stmt),
    walk σ xs = .fall es → walk σ (xs ++ ys) = (walk σ ys).pre es
  | [], es, ys, h => by
      rw [walk] at h
      cases h
      rw [List.nil_append]
      cases walk σ ys <;> simp [Out.pre]
  | s :: xs, es, ys, h => by
      rw [walk] at h
      rw [List.cons_append, walk]
      cases hs : walk1 σ s with
      | fall es1 =>
          rw [hs, Out.seq] at h
          cases hx : walk σ xs with
          | fall es2 =>
              rw [hx] at h
              simp only [Out.pre, Out.fall.injEq] at h
              subst h
              rw [Out.seq, walk_append_fall' ys hx]
              cases walk σ ys <;> simp [Out.pre]
          | ret _ _ => rw [hx] at h; simp [Out.pre] at h
          | stuck => rw [hx] at h; simp [Out.pre] at h
      | ret _ _ => rw [hs, Out.seq] at h; cases h
      | stuck => rw [hs, Out.seq] at h; cases h

/-- **A block returning after a block popping `ps`** pops `ps` and sets up no call. -/
theorem retPops_of_fallPops {σ : Val} {xs : List Stmt} {vs : List V} {ps : List Pop}
    (h : FallPops rd σ xs ps) :
    ∃ es, walk σ (xs ++ [.ret vs]) = .ret es vs ∧ calls es = [] ∧ evPops rd σ es = ps := by
  obtain ⟨es, hw, hc, rfl⟩ := h
  exact ⟨es, by rw [walk_append_fall' _ hw]; simp [walk, walk1, Out.seq, Out.pre], hc, rfl⟩

/-! ## Calls -/

section Splice

variable {σ : Val}

/-- **A block falls through popping `ps`**, its calls' entries `ks` spliced in, one per call set up. -/
def SplicePops (rd : Reader) (σ : Val) (ss : List Stmt) (ks : List (List Pop)) (ps : List Pop) : Prop :=
  ∃ es, walk σ ss = .fall es ∧ (calls es).length = ks.length ∧ splice rd σ es ks = ps

theorem splice_append : ∀ (es es' : List Ev) (ks ks' : List (List Pop)), (calls es).length = ks.length →
    splice rd σ (es ++ es') (ks ++ ks') = splice rd σ es ks ++ splice rd σ es' ks'
  | [], _, ks, _, h => by
      have : ks = [] := List.eq_nil_of_length_eq_zero (by simpa [calls] using h.symm)
      subst this; rfl
  | .atom a :: es, es', ks, ks', h => by
      simp only [List.cons_append, splice, List.append_assoc]
      rw [splice_append es es' ks ks' (by simpa only [calls, List.filterMap_cons, Ev.call?, List.length_cons, Nat.add_right_cancel_iff] using h)]
  | .inK _ :: es, es', ks, ks', h => by
      simp only [List.cons_append, splice]
      exact splice_append es es' ks ks' (by simpa only [calls, List.filterMap_cons, Ev.call?, List.length_cons, Nat.add_right_cancel_iff] using h)
  | .call .. :: es, es', ks, ks', h => by
      obtain ⟨k, ks, rfl⟩ : ∃ k t, ks = k :: t := List.exists_cons_of_ne_nil (by
        rintro rfl; simp only [calls, List.filterMap_cons, Ev.call?, List.length_cons, List.length_nil] at h; omega)
      simp only [List.cons_append, splice, List.headD_cons, List.tail_cons, List.append_assoc]
      rw [splice_append es es' ks ks' (by simpa only [calls, List.filterMap_cons, Ev.call?, List.length_cons, Nat.add_right_cancel_iff] using h)]
  | .skip .. :: es, es', ks, ks', h => by
      obtain ⟨k, ks, rfl⟩ : ∃ k t, ks = k :: t := List.exists_cons_of_ne_nil (by
        rintro rfl; simp only [calls, List.filterMap_cons, Ev.call?, List.length_cons, List.length_nil] at h; omega)
      simp only [List.cons_append, splice, List.headD_cons, List.tail_cons, List.append_assoc]
      rw [splice_append es es' ks ks' (by simpa only [calls, List.filterMap_cons, Ev.call?, List.length_cons, Nat.add_right_cancel_iff] using h)]

theorem calls_append' (es es' : List Ev) : calls (es ++ es') = calls es ++ calls es' := List.filterMap_append

theorem splice_nil_of_calls (es : List Ev) (h : calls es = []) : splice rd σ es [] = evPops rd σ es := by
  have := splice_append_of_calls_nil (rd := rd) (σ := σ) (es := es) [] [] h
  simpa [splice] using this

theorem SplicePops.of_fallPops {ss : List Stmt} {ps : List Pop} (h : FallPops rd σ ss ps) :
    SplicePops rd σ ss [] ps := by
  obtain ⟨es, hw, hc, rfl⟩ := h
  exact ⟨es, hw, by rw [hc]; rfl, splice_nil_of_calls es hc⟩

theorem SplicePops.append {xs ys : List Stmt} {ks ks' : List (List Pop)} {p q : List Pop}
    (hx : SplicePops rd σ xs ks p) (hy : SplicePops rd σ ys ks' q) :
    SplicePops rd σ (xs ++ ys) (ks ++ ks') (p ++ q) := by
  obtain ⟨es, hw, hc, rfl⟩ := hx
  obtain ⟨es', hw', hc', rfl⟩ := hy
  exact ⟨es ++ es', by rw [walk_append_fall' ys hw, hw', Out.pre],
    by rw [calls_append', List.length_append, List.length_append, hc, hc'], splice_append es es' ks ks' hc⟩

/-- **A call pops its callee's entries.** -/
theorem SplicePops.call (f : String) (args rets : List V) (k : List Pop) :
    SplicePops rd σ [.call f args rets] [k] k :=
  ⟨[.call f args rets], rfl, rfl, by simp [splice]⟩

theorem SplicePops.congr_pops {ss : List Stmt} {ks : List (List Pop)} {p q : List Pop}
    (h : SplicePops rd σ ss ks p) (e : p = q) : SplicePops rd σ ss ks q := e ▸ h

theorem splice_congr {σ' : Val} : ∀ (es : List Ev) (ks : List (List Pop)),
    (∀ e ∈ es, Ev.pops rd σ e = Ev.pops rd σ' e) → splice rd σ es ks = splice rd σ' es ks
  | [], _, _ => rfl
  | .atom a :: es, ks, h => by
      simp only [splice]
      rw [show a.pops rd σ = a.pops rd σ' from h _ (List.mem_cons_self ..),
        splice_congr es ks fun e he => h e (List.mem_cons_of_mem _ he)]
  | .inK _ :: es, ks, h | .call .. :: es, ks, h | .skip .. :: es, ks, h => by
      simp only [splice]
      rw [splice_congr es _ fun e he => h e (List.mem_cons_of_mem _ he)]

theorem SplicePops.congr {σ' : Val} {ss : List Stmt} {ks : List (List Pop)} {ps : List Pop}
    (h : ∀ v ∈ Stmt.valsList ss, σ v = σ' v) (hf : SplicePops rd σ ss ks ps) : SplicePops rd σ' ss ks ps := by
  obtain ⟨es, hw, hc, rfl⟩ := hf
  obtain ⟨e1, e2⟩ := walk_congr_pops (rd := rd) ss h
  refine ⟨es, by rw [← e1, hw], hc, (splice_congr es ks fun e he => ?_).symm⟩
  exact e2 e (by rw [hw]; exact he)

theorem SplicePops.agree {σ' : Val} {ss : List Stmt} {ks : List (List Pop)} {ps : List Pop} {hi : Nat}
    (hb : NumBelow hi (Stmt.valsList ss)) (hag : AgreeBelow hi σ σ') (hf : SplicePops rd σ ss ks ps) :
    SplicePops rd σ' ss ks ps :=
  hf.congr fun v hv => let ⟨k, hk, e⟩ := hb v hv; e ▸ hag k hk

/-- **A node whose body pops `p` with its callees' entries spliced in, then returns setting up no call**, pops `p`
and the return's entries. -/
theorem Tree.pops_of_splice {P : Core.Program} {f : String} {bufs : List ℕ} {kids : List Tree} {fn : Fn}
    {xs ys : List Stmt} {p : List Pop} {es : List Ev} {vs : List V} (hf : P.find? f = some fn)
    (hb : fn.body = xs ++ ys) (hx : SplicePops rd σ xs (Tree.popsKids P rd kids) p) (hy : walk σ ys = .ret es vs)
    (hc : calls es = []) :
    ∃ es', walk σ fn.body = .ret es' vs ∧
      (Tree.node f σ bufs kids).pops P rd = p ++ evPops rd σ es := by
  obtain ⟨es0, hw0, hc0, rfl⟩ := hx
  have hw : walk σ fn.body = .ret (es0 ++ es) vs := by
    rw [hb, walk_append_fall' ys hw0, hy, Out.pre]
  refine ⟨_, hw, ?_⟩
  have e := splice_append (rd := rd) (σ := σ) es0 es (Tree.popsKids P rd kids) [] hc0
  rw [List.append_nil] at e
  rw [Tree.pops_node hf hw, e, splice_nil_of_calls es hc]

end Splice

/-! ## Streams -/

section Streams

variable {a b c : List Pop}

theorem SameStreams.refl (a : List Pop) : SameStreams a a := fun _ => rfl

theorem SameStreams.symm (h : SameStreams a b) : SameStreams b a := fun s => (h s).symm

theorem SameStreams.trans (h : SameStreams a b) (h' : SameStreams b c) : SameStreams a c :=
  fun s => (h s).trans (h' s)

theorem SameStreams.of_eq (h : a = b) : SameStreams a b := h ▸ SameStreams.refl a

/-- **Interleaved blocks of distinct streams** pop, stream by stream, all of the first, then all of the second. -/
theorem sameStreams_flatMap_split {α : Type} (A B : α → List Pop)
    (hd : ∀ x y, ∀ p ∈ A x, ∀ q ∈ B y, p.1 ≠ q.1) :
    ∀ l : List α, SameStreams (l.flatMap fun x => A x ++ B x) (l.flatMap A ++ l.flatMap B)
  | [] => SameStreams.refl _
  | x :: l => by
      simp only [List.flatMap_cons]
      have ih := sameStreams_flatMap_split A B hd l
      have hc : SameStreams (B x ++ l.flatMap A) (l.flatMap A ++ B x) :=
        sameStreams_append_comm fun p hp q hq => by
          obtain ⟨y, -, hy⟩ := List.mem_flatMap.mp hq
          exact (hd y x q hy p hp).symm
      rw [List.append_assoc, List.append_assoc]
      refine (SameStreams.refl (A x)).append ?_
      rw [← List.append_assoc]
      refine ((SameStreams.refl (B x)).append ih).trans ?_
      simp only [← List.append_assoc]
      exact hc.append (SameStreams.refl _)

end Streams

end
end LeanVM.Guest.Memory
