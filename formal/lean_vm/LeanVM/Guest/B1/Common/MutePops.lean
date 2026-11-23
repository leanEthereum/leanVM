/-
  LeanVM.Guest.B1.Common.MutePops

  Call trees whose functions pop no witness stream: a call-closed set of such functions pops nothing (`Tree.pops_mute`), and a node whose body pops nothing past a prefix pops the prefix's entries, then its remaining callees' (`Tree.pops_of_prefix`).
-/

module

public import LeanVM.Guest.B1.Sig.PopsKit

/-!
# Mute functions

* `atomMute`, `Stmt.mute S`: no `hint_witness`, calls into `S` only; `MuteIn P S`: a call-closed set of such functions;
* `walk_mute`: a mute block's events pop nothing and set up frames of `S` only;
* `splice_mute`: events popping nothing splice their callees' entries in order;
* `Tree.pops_mute`: a valid tree of a function of a mute set pops nothing;
* `Tree.pops_of_prefix`: a valid node whose body is a block popping `p` with its first callees spliced in, then a mute block, pops `p`, then its remaining callees' entries; `popsKids_flatten_mute`: callees of a mute set pop nothing; `Tree.pops_of_prefix_mute`, `Tree.pops_of_prefix_leaf`: a valid node whose body pops `p` in a prefix calling nothing, then nothing, calling a mute set only, pops `p`.
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

/-- An atom popping no witness stream. -/
def atomMute : Atom → Bool
  | .hint (.witness ..) => false
  | _ => true

mutual
/-- A statement popping no witness stream itself, calling only functions of `S`. -/
def Stmt.mute (S : String → Bool) : Stmt → Bool
  | .atom a => atomMute a
  | .ite _ z n => Stmt.muteList S z && Stmt.muteList S n
  | .match_ _ arms => Stmt.muteArms S arms
  | .call f _ _ => S f
  | .callIf _ f _ => S f
  | .dispatch _ fs _ _ => fs.all S
  | .ret _ => true

/-- `Stmt.mute` of a block. -/
def Stmt.muteList (S : String → Bool) : List Stmt → Bool
  | [] => true
  | s :: ss => Stmt.mute S s && Stmt.muteList S ss

/-- `Stmt.mute` of arms. -/
def Stmt.muteArms (S : String → Bool) : List (List Stmt) → Bool
  | [] => true
  | a :: as => Stmt.muteList S a && Stmt.muteArms S as
end

/-- **A call-closed set of functions popping nothing.** -/
def MuteIn (P : Core.Program) (S : String → Bool) : Prop :=
  ∀ g, S g = true → ∀ fn, P.find? g = some fn → Stmt.muteList S fn.body = true

/-- An event popping nothing, setting up a frame of `S` if any. -/
def Ev.Mute (rd : Reader) (σ : Val) (S : String → Bool) (e : Ev) : Prop :=
  e.pops rd σ = [] ∧ ∀ c, e.call? = some c → S c.f = true

/-- Every event of an outcome satisfies `p`. -/
def Out.Every (p : Ev → Prop) : Out → Prop
  | .fall es => ∀ e ∈ es, p e
  | .ret es _ => ∀ e ∈ es, p e
  | .stuck => True

section Walk

variable {rd : Reader} {σ : Val} {S : String → Bool}

theorem Out.every_pre {p : Ev → Prop} {es : List Ev} (h : ∀ e ∈ es, p e) :
    ∀ {o : Out}, o.Every p → (o.pre es).Every p
  | .fall _, ho => List.forall_mem_append.mpr ⟨h, ho⟩
  | .ret _ _, ho => List.forall_mem_append.mpr ⟨h, ho⟩
  | .stuck, _ => trivial

theorem Out.every_seq {p : Ev → Prop} {k : Out} (hk : k.Every p) : ∀ {o : Out}, o.Every p → (o.seq k).Every p
  | .fall _, ho => Out.every_pre ho hk
  | .ret _ _, ho => ho
  | .stuck, _ => trivial

theorem pick_mute {x : V} {args rets : List V} :
    ∀ (fs : List String) (j : ℕ), fs.all S = true → (pick σ x args rets j fs).Every (Ev.Mute rd σ S)
  | [], _, _ => trivial
  | f :: fs, j, h => by
      simp only [List.all_cons, Bool.and_eq_true] at h
      unfold pick
      split_ifs
      · intro e he
        rw [List.mem_singleton] at he
        subst he
        exact ⟨rfl, fun c hc => by cases hc; exact h.1⟩
      · exact pick_mute fs (j + 1) h.2

mutual
theorem walk1_mute : ∀ (s : Stmt), Stmt.mute S s = true → (walk1 σ s).Every (Ev.Mute rd σ S)
  | .atom a, h => by
      intro e he
      rw [List.mem_singleton] at he
      subst he
      refine ⟨?_, fun c hc => by cases hc⟩
      cases a with
      | hint x => cases x <;> first | rfl | simp [Stmt.mute, atomMute] at h
      | _ => rfl
  | .ite c z n, h => by
      simp only [Stmt.mute, Bool.and_eq_true] at h
      rw [walk1]
      refine Out.every_pre (fun e he => ?_) ?_
      · rw [List.mem_singleton] at he
        subst he
        exact ⟨rfl, fun c hc => by cases hc⟩
      · split_ifs
        · exact walk_mute z h.1
        · exact walk_mute n h.2
  | .match_ x arms, h => walkArms_mute x arms 0 h
  | .call f args rets, h => by
      intro e he
      rw [List.mem_singleton] at he
      subst he
      exact ⟨rfl, fun c hc => by cases hc; exact h⟩
  | .callIf c f args, h => by
      intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · exact ⟨rfl, fun c hc => by cases hc⟩
      · split_ifs
        · exact ⟨rfl, fun c hc => by cases hc; exact h⟩
        · exact ⟨rfl, fun c hc => by cases hc; exact h⟩
  | .dispatch x fs args rets, h => pick_mute fs 0 h
  | .ret _, _ => fun _ he => (List.not_mem_nil he).elim

theorem walk_mute : ∀ (ss : List Stmt), Stmt.muteList S ss = true → (walk σ ss).Every (Ev.Mute rd σ S)
  | [], _ => fun _ he => (List.not_mem_nil he).elim
  | s :: ss, h => by
      simp only [Stmt.muteList, Bool.and_eq_true] at h
      rw [walk]
      exact Out.every_seq (walk_mute ss h.2) (walk1_mute s h.1)

theorem walkArms_mute (x : V) : ∀ (arms : List (List Stmt)) (j : ℕ), Stmt.muteArms S arms = true →
    (walkArms σ x j arms).Every (Ev.Mute rd σ S)
  | [], _, _ => trivial
  | a :: as, j, h => by
      simp only [Stmt.muteArms, Bool.and_eq_true] at h
      unfold walkArms
      split_ifs
      · exact walk_mute a h.1
      · exact walkArms_mute x as (j + 1) h.2
end

/-- **Events popping nothing** splice their callees' entries in order. -/
theorem splice_mute : ∀ (es : List Ev) (ks : List (List Pop)), (∀ e ∈ es, e.pops rd σ = []) →
    (calls es).length = ks.length → splice rd σ es ks = ks.flatten
  | [], ks, _, h => by
      have : ks = [] := List.eq_nil_of_length_eq_zero (by simpa [calls] using h.symm)
      subst this; rfl
  | .atom a :: es, ks, hp, h => by
      have ha : a.pops rd σ = [] := hp _ List.mem_cons_self
      rw [splice, ha, List.nil_append]
      exact splice_mute es ks (fun e he => hp e (List.mem_cons_of_mem _ he))
        (by simpa only [calls, List.filterMap_cons, Ev.call?] using h)
  | .inK _ :: es, ks, hp, h => by
      rw [splice]
      exact splice_mute es ks (fun e he => hp e (List.mem_cons_of_mem _ he))
        (by simpa only [calls, List.filterMap_cons, Ev.call?] using h)
  | .call .. :: es, ks, hp, h => by
      obtain ⟨k, ks, rfl⟩ : ∃ k t, ks = k :: t := List.exists_cons_of_ne_nil (by
        rintro rfl; simp only [calls, List.filterMap_cons, Ev.call?, List.length_cons, List.length_nil] at h; omega)
      rw [splice, List.headD_cons, List.tail_cons, List.flatten_cons]
      exact congrArg (k ++ ·) (splice_mute es ks (fun e he => hp e (List.mem_cons_of_mem _ he))
        (by simpa only [calls, List.filterMap_cons, Ev.call?, List.length_cons, Nat.add_right_cancel_iff] using h))
  | .skip .. :: es, ks, hp, h => by
      obtain ⟨k, ks, rfl⟩ : ∃ k t, ks = k :: t := List.exists_cons_of_ne_nil (by
        rintro rfl; simp only [calls, List.filterMap_cons, Ev.call?, List.length_cons, List.length_nil] at h; omega)
      rw [splice, List.headD_cons, List.tail_cons, List.flatten_cons]
      exact congrArg (k ++ ·) (splice_mute es ks (fun e he => hp e (List.mem_cons_of_mem _ he))
        (by simpa only [calls, List.filterMap_cons, Ev.call?, List.length_cons, Nat.add_right_cancel_iff] using h))

end Walk

/-! ## Trees -/

section Trees

variable {P : Core.Program} {rd : Reader} {S : String → Bool}

theorem kidsValid_len {σ : Val} : ∀ {cs : List Call} {ks : List Tree}, Tree.KidsValid P rd σ cs ks →
    cs.length = ks.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, ⟨_, _, h⟩ => by rw [List.length_cons, List.length_cons, kidsValid_len h]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem length_popsKids : ∀ (ks : List Tree), (Tree.popsKids P rd ks).length = ks.length
  | [] => rfl
  | _ :: ks => by rw [Tree.popsKids, List.length_cons, List.length_cons, length_popsKids ks]

theorem calls_mem_of_mute {σ : Val} {es : List Ev} (h : ∀ e ∈ es, Ev.Mute rd σ S e) :
    ∀ c ∈ calls es, S c.f = true := fun c hc => by
  obtain ⟨e, he, hc⟩ := List.mem_filterMap.mp hc
  exact (h e he).2 c hc

mutual
/-- **A valid tree of a function of a mute set pops nothing.** -/
theorem Tree.pops_mute (hS : MuteIn P S) : ∀ (t : Tree) {args rets : List E}, t.Valid P rd args rets →
    S t.name = true → t.pops P rd = []
  | .node f σ bufs kids, _, _, ⟨fn, hf, _, es, vs, hw, _, _, hk⟩, hn => by
      have hm : ∀ e ∈ es, Ev.Mute rd σ S e := by
        have := walk_mute (rd := rd) (σ := σ) fn.body (hS f hn fn hf)
        rwa [hw] at this
      rw [Tree.pops_node hf hw, splice_mute es _ (fun e he => (hm e he).1)
        (by rw [length_popsKids, kidsValid_len hk])]
      exact List.flatten_eq_nil_iff.mpr (Tree.popsKids_mute hS kids σ (calls es) hk (calls_mem_of_mute hm))
  | .phantom .., _, _, h, _ => h.elim

/-- `Tree.pops_mute` for the callees. -/
theorem Tree.popsKids_mute (hS : MuteIn P S) : ∀ (ks : List Tree) (σ : Val) (cs : List Call),
    Tree.KidsValid P rd σ cs ks → (∀ c ∈ cs, S c.f = true) → ∀ p ∈ Tree.popsKids P rd ks, p = []
  | [], _, _, _, _ => fun _ h => (List.not_mem_nil h).elim
  | k :: ks, σ, c :: cs, ⟨hn, hc, hks⟩, hS' => by
      intro p hp
      rw [Tree.popsKids, List.mem_cons] at hp
      rcases hp with rfl | hp
      · by_cases ht : c.taken = true
        · rw [ite_eq_left ht] at hc
          exact Tree.pops_mute hS k hc (hn ▸ hS' c List.mem_cons_self)
        · rw [ite_eq_right ht] at hc
          obtain ⟨⟨f, σ', rfl⟩, -⟩ := hc
          rw [Tree.pops]
      · exact Tree.popsKids_mute hS ks σ cs hks (fun c' h => hS' c' (List.mem_cons_of_mem _ h)) p hp
  | _ :: _, _, [], h, _ => h.elim
end

/-- **Callees of a mute set pop nothing.** -/
theorem popsKids_flatten_mute (hS : MuteIn P S) {σ : Val} {cs : List Call} {ks : List Tree}
    (hk : Tree.KidsValid P rd σ cs ks) (hc : ∀ c ∈ cs, S c.f = true) : (Tree.popsKids P rd ks).flatten = [] :=
  List.flatten_eq_nil_iff.mpr (Tree.popsKids_mute hS ks σ cs hk hc)

/-- **A valid node whose body is a block popping `p`, its first callees' entries `ks` spliced in, then a block popping nothing itself**, pops `p`, then its remaining callees' entries. -/
theorem Tree.pops_of_prefix {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} {fn : Fn}
    {args rets : List E} {xs ys : List Stmt} {ks ks' : List (List Pop)} {p : List Pop}
    (hv : (Tree.node f σ bufs kids).Valid P rd args rets) (hf : P.find? f = some fn) (hb : fn.body = xs ++ ys)
    (hx : SplicePops rd σ xs ks p) (hy : Stmt.muteList (fun _ => true) ys = true)
    (hk : Tree.popsKids P rd kids = ks ++ ks') :
    (Tree.node f σ bufs kids).pops P rd = p ++ ks'.flatten := by
  obtain ⟨fn', hf', -, es, vs, hw, -, -, hkv⟩ := hv
  rw [hf] at hf'
  cases hf'
  obtain ⟨es0, hw0, hc0, rfl⟩ := hx
  rw [hb, walk_append_fall' ys hw0] at hw
  obtain ⟨es1, hw1, rfl⟩ : ∃ es1, walk σ ys = .ret es1 vs ∧ es = es0 ++ es1 := by
    cases h : walk σ ys with
    | fall _ => rw [h, Out.pre] at hw; cases hw
    | ret es1 vs1 =>
        rw [h, Out.pre] at hw
        cases hw
        exact ⟨es1, rfl, rfl⟩
    | stuck => rw [h, Out.pre] at hw; cases hw
  have hm : ∀ e ∈ es1, Ev.Mute rd σ (fun _ => true) e := by
    have := walk_mute (rd := rd) (σ := σ) ys hy
    rwa [hw1] at this
  have hl := kidsValid_len hkv
  rw [← length_popsKids (P := P) (rd := rd), hk, calls_append', List.length_append, List.length_append, hc0] at hl
  have hw' : walk σ fn.body = .ret (es0 ++ es1) vs := by rw [hb, walk_append_fall' ys hw0, hw1, Out.pre]
  rw [Tree.pops_node hf hw', hk, splice_append es0 es1 ks ks' hc0,
    splice_mute es1 ks' (fun e he => (hm e he).1) (by omega)]

theorem calls_nil_of_mute {rd : Reader} {σ : Val} {es : List Ev} (h : ∀ e ∈ es, Ev.Mute rd σ (fun _ => false) e) :
    calls es = [] :=
  List.filterMap_eq_nil_iff.mpr fun e he => by
    cases hc : e.call? with
    | none => rfl
    | some c => exact absurd ((h e he).2 c hc) (by simp)

/-- **A valid node whose body is a block popping `p` and setting up no frame, then a block popping nothing and calling only functions of a mute set**, pops `p`. -/
theorem Tree.pops_of_prefix_mute {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} {fn : Fn}
    {args rets : List E} {xs ys : List Stmt} {p : List Pop} (hS : MuteIn P S)
    (hv : (Tree.node f σ bufs kids).Valid P rd args rets) (hf : P.find? f = some fn) (hb : fn.body = xs ++ ys)
    (hx : FallPops rd σ xs p) (hy : Stmt.muteList S ys = true) :
    (Tree.node f σ bufs kids).pops P rd = p := by
  obtain ⟨fn', hf', -, es, vs, hw, -, -, hkv⟩ := hv
  rw [hf] at hf'
  cases hf'
  obtain ⟨es0, hw0, hc0, rfl⟩ := hx
  rw [hb, walk_append_fall' ys hw0] at hw
  obtain ⟨es1, hw1, rfl⟩ : ∃ es1, walk σ ys = .ret es1 vs ∧ es = es0 ++ es1 := by
    cases h : walk σ ys with
    | fall _ => rw [h, Out.pre] at hw; cases hw
    | ret es1 vs1 =>
        rw [h, Out.pre] at hw
        cases hw
        exact ⟨es1, rfl, rfl⟩
    | stuck => rw [h, Out.pre] at hw; cases hw
  have hm : ∀ e ∈ es1, Ev.Mute rd σ S e := by
    have := walk_mute (rd := rd) (σ := σ) ys hy
    rwa [hw1] at this
  rw [calls_append', hc0, List.nil_append] at hkv
  have hw' : walk σ fn.body = .ret (es0 ++ es1) vs := by rw [hb, walk_append_fall' ys hw0, hw1, Out.pre]
  rw [Tree.pops_node hf hw', splice_append_of_calls_nil es1 _ hc0,
    splice_mute es1 _ (fun e he => (hm e he).1) (by rw [length_popsKids, kidsValid_len hkv]),
    popsKids_flatten_mute hS hkv (calls_mem_of_mute hm), List.append_nil]

/-- **A valid node whose body is a block popping `p` and setting up no frame, then a block popping and calling nothing**, pops `p`. -/
theorem Tree.pops_of_prefix_leaf {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} {fn : Fn}
    {args rets : List E} {xs ys : List Stmt} {p : List Pop}
    (hv : (Tree.node f σ bufs kids).Valid P rd args rets) (hf : P.find? f = some fn) (hb : fn.body = xs ++ ys)
    (hx : FallPops rd σ xs p) (hy : Stmt.muteList (fun _ => false) ys = true) :
    (Tree.node f σ bufs kids).pops P rd = p := by
  obtain ⟨fn', hf', -, es, vs, hw, -, -, hkv⟩ := hv
  rw [hf] at hf'
  cases hf'
  obtain ⟨es0, hw0, hc0, rfl⟩ := hx
  rw [hb, walk_append_fall' ys hw0] at hw
  obtain ⟨es1, hw1, rfl⟩ : ∃ es1, walk σ ys = .ret es1 vs ∧ es = es0 ++ es1 := by
    cases h : walk σ ys with
    | fall _ => rw [h, Out.pre] at hw; cases hw
    | ret es1 vs1 =>
        rw [h, Out.pre] at hw
        cases hw
        exact ⟨es1, rfl, rfl⟩
    | stuck => rw [h, Out.pre] at hw; cases hw
  have hm : ∀ e ∈ es1, Ev.Mute rd σ (fun _ => false) e := by
    have := walk_mute (rd := rd) (σ := σ) ys hy
    rwa [hw1] at this
  have hc1 := calls_nil_of_mute hm
  have hl := kidsValid_len hkv
  rw [calls_append', hc0, hc1, List.length_append, List.length_nil] at hl
  rw [List.eq_nil_of_length_eq_zero hl.symm] at hkv ⊢
  have hw' : walk σ fn.body = .ret (es0 ++ es1) vs := by rw [hb, walk_append_fall' ys hw0, hw1, Out.pre]
  rw [Tree.pops_node hf hw', splice_append_of_calls_nil es1 _ hc0,
    splice_mute es1 _ (fun e he => (hm e he).1) (by rw [hc1]; rfl)]
  simp [Tree.popsKids]

end Trees

end
end LeanVM.Guest.Memory
