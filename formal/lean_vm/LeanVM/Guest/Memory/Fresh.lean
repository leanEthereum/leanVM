/-
  LeanVM.Guest.Memory.Fresh

  The temporaries of a function, the two words a range check reads into its frame: fresh when
  no other part of the body names them; then a path does not depend on them, and each lies on at
  most one range check of a path. A kernel-friendly check of freshness.
-/

module

public import LeanVM.Guest.Memory.Eval

/-!
# Range-check temporaries

`rangeCheck x y t1 t2 k` reads the words at `x` and at `y` into the cells of `t1`, `t2`, which
nothing else uses: the guest's compiler gives each a cell of its own. Their values are whatever
the final memory holds at `x` and `y`, which is the only place a frame's values feed back into
its own memory without the program's control, so the honest memory chooses them last
(`Memory/Retemp.lean`).

`atomUses`, `Stmt.usesList`: every value a block names, the temporaries of its range checks
apart; `Stmt.tmpsList`: those temporaries. A function is `Fn.Fresh` when its temporaries are
distinct and appear nowhere else, nor among its parameters; `Fn.freshB` decides it with bit masks
of the values' indices, so that the kernel checks the guest in time linear in its size
(`fn_fresh_of_freshB`).

Of a path (`walk`): it is the same under two valuations agreeing on the block's uses
(`walk_congr`); its events name only the block's uses, its temporaries are a sublist of the
block's, and its returned values are uses (`walk_evs`).
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

/-! ## Uses and temporaries -/

/-- The values a hint destination names. -/
def destUses : Dest → List V
  | .stack cells => cells
  | .heap ptr _ _ => [ptr]

/-- The values a hint names. -/
def hintUses : Hint → List V
  | .witness _ d => destUses d
  | .bits v _ _ d => v :: destUses d
  | .bitsExp v _ d => v :: destUses d
  | .limbs v ds => v :: ds
  | .log2Ceil b _ _ dst => dst :: destUses b
  | .inverse x dst => [x, dst]
  | .alloc dst _ => [dst]
  | .allocDyn dst s => [dst, s]

/-- The values an atom names, a range check's temporaries apart. -/
def atomUses : Atom → List V
  | .const d _ => [d]
  | .add d a b => [d, a, b]
  | .mul d a b => [d, a, b]
  | .copy d s => [d, s]
  | .load d p _ => [d, p]
  | .assertEq a b => [a, b]
  | .assertNe x inv p => [x, inv, p]
  | .rangeCheck x y _ _ k => [x, y, k]
  | .assertInK a b => [a, b]
  | .blake2s m0 m1 m2 m3 cv0 cv1 o0 o1 md => [m0, m1, m2, m3, cv0, cv1, o0, o1, md]
  | .frameAddr p run => p :: run
  | .hint h => hintUses h

/-- A range check's temporaries. -/
def atomTmps : Atom → List V
  | .rangeCheck _ _ t1 t2 _ => [t1, t2]
  | _ => []

mutual
/-- The values a statement names, its range checks' temporaries apart. -/
def Stmt.uses : Stmt → List V
  | .atom a => atomUses a
  | .ite c z n => c :: (Stmt.usesList z ++ Stmt.usesList n)
  | .match_ x arms => x :: Stmt.usesArms arms
  | .call _ args rets => args ++ rets
  | .callIf c _ args => c :: args
  | .dispatch x _ args rets => x :: (args ++ rets)
  | .ret vs => vs

/-- `Stmt.uses` of a block. -/
def Stmt.usesList : List Stmt → List V
  | [] => []
  | s :: ss => Stmt.uses s ++ Stmt.usesList ss

/-- `Stmt.uses` of arms. -/
def Stmt.usesArms : List (List Stmt) → List V
  | [] => []
  | a :: as => Stmt.usesList a ++ Stmt.usesArms as
end

mutual
/-- The temporaries of a statement's range checks. -/
def Stmt.tmps : Stmt → List V
  | .atom a => atomTmps a
  | .ite _ z n => Stmt.tmpsList z ++ Stmt.tmpsList n
  | .match_ _ arms => Stmt.tmpsArms arms
  | _ => []

/-- `Stmt.tmps` of a block. -/
def Stmt.tmpsList : List Stmt → List V
  | [] => []
  | s :: ss => Stmt.tmps s ++ Stmt.tmpsList ss

/-- `Stmt.tmps` of arms. -/
def Stmt.tmpsArms : List (List Stmt) → List V
  | [] => []
  | a :: as => Stmt.tmpsList a ++ Stmt.tmpsArms as
end

/-- **Fresh temporaries**: distinct, named nowhere else in the body, and no parameter. -/
def _root_.LeanVM.Guest.Core.Fn.Fresh (fn : Fn) : Prop :=
  (Stmt.tmpsList fn.body).Nodup ∧
    ∀ t ∈ Stmt.tmpsList fn.body, t ∉ Stmt.usesList fn.body ∧ t ∉ fn.params

/-- Every function of the program has fresh temporaries. -/
def _root_.LeanVM.Guest.Core.Program.Fresh (P : Core.Program) : Prop := ∀ fn ∈ P, fn.Fresh

/-- The temporaries of a function of the program. -/
def _root_.LeanVM.Guest.Core.Program.temps (P : Core.Program) (f : String) : List V :=
  match P.find? f with
  | some fn => Stmt.tmpsList fn.body
  | none => []

/-! ## Deciding freshness -/

/-- The bit mask of the values' indices. -/
def idxMask : List V → ℕ
  | [] => 0
  | v :: vs => idxMask vs ||| 1 <<< v.idx

/-- The values have distinct indices, none of them in `m`. -/
def idxNodup : List V → ℕ → Bool
  | [], _ => true
  | v :: vs, m => !(m.testBit v.idx) && idxNodup vs (m ||| 1 <<< v.idx)

/-- **Freshness, decided** on the values' indices. -/
def _root_.LeanVM.Guest.Core.Fn.freshB (fn : Fn) : Bool :=
  idxNodup (Stmt.tmpsList fn.body) 0 &&
    (Stmt.tmpsList fn.body).all fun t => !(idxMask (Stmt.usesList fn.body ++ fn.params)).testBit t.idx

theorem testBit_idxMask {v : V} : ∀ {l : List V}, v ∈ l → (idxMask l).testBit v.idx = true
  | w :: ws, h => by
      rw [idxMask, Nat.testBit_or, Bool.or_eq_true]
      rcases List.mem_cons.mp h with rfl | h
      · exact Or.inr (by simp [Nat.testBit_shiftLeft])
      · exact Or.inl (testBit_idxMask h)

theorem idxNodup_spec : ∀ {l : List V} {m : ℕ}, idxNodup l m = true →
    l.Nodup ∧ ∀ v ∈ l, m.testBit v.idx = false
  | [], _, _ => ⟨List.nodup_nil, fun _ h => (List.not_mem_nil h).elim⟩
  | v :: vs, m, h => by
      simp only [idxNodup, Bool.and_eq_true, Bool.not_eq_true'] at h
      have hv := h.1
      obtain ⟨hvs, hm⟩ := idxNodup_spec h.2
      refine ⟨List.nodup_cons.mpr ⟨fun hmem => ?_, hvs⟩, fun w hw => ?_⟩
      · have := hm v hmem
        simp [Nat.testBit_or, Nat.testBit_shiftLeft] at this
      · rcases List.mem_cons.mp hw with rfl | hw
        · exact hv
        · have := hm w hw
          simp only [Nat.testBit_or, Bool.or_eq_false_iff] at this
          exact this.1

theorem fn_fresh_of_freshB {fn : Fn} (h : fn.freshB = true) : fn.Fresh := by
  simp only [Fn.freshB, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at h
  refine ⟨(idxNodup_spec h.1).1, fun t ht => ?_⟩
  have hb := h.2 t ht
  refine ⟨fun hu => ?_, fun hp => ?_⟩
  · rw [testBit_idxMask (List.mem_append_left _ hu)] at hb; exact absurd hb (by simp)
  · rw [testBit_idxMask (List.mem_append_right _ hp)] at hb; exact absurd hb (by simp)

/-! ## Freshness by ranges

A body too large for one kernel check is cut into ranges of its statements: each range's
temporaries have the indices `ts` and none of the function's temporaries `all` is among its uses
(`RangeFresh`); the ranges concatenate (`RangeFresh.append`), and a body whose temporaries are
`all`, distinct and no parameter, is fresh (`fn_fresh_of_rangeFresh`). -/

theorem usesList_append : ∀ (ss ss' : List Stmt),
    Stmt.usesList (ss ++ ss') = Stmt.usesList ss ++ Stmt.usesList ss'
  | [], _ => by rw [List.nil_append, Stmt.usesList, List.nil_append]
  | s :: ss, ss' => by
      rw [List.cons_append, Stmt.usesList, Stmt.usesList, usesList_append ss ss', List.append_assoc]

theorem tmpsList_append : ∀ (ss ss' : List Stmt),
    Stmt.tmpsList (ss ++ ss') = Stmt.tmpsList ss ++ Stmt.tmpsList ss'
  | [], _ => by rw [List.nil_append, Stmt.tmpsList, List.nil_append]
  | s :: ss, ss' => by
      rw [List.cons_append, Stmt.tmpsList, Stmt.tmpsList, tmpsList_append ss ss', List.append_assoc]

theorem idxMask_append : ∀ (l l' : List V), idxMask (l ++ l') = idxMask l ||| idxMask l'
  | [], l' => by rw [List.nil_append, idxMask, Nat.zero_or]
  | v :: vs, l' => by
      rw [List.cons_append, idxMask, idxMask, idxMask_append vs l', Nat.lor_assoc,
        Nat.lor_comm (idxMask l'), ← Nat.lor_assoc]

/-- A range of statements whose temporaries have the indices `ts`, its uses avoiding `all`. -/
def RangeFresh (ss : List Stmt) (ts all : List ℕ) : Prop :=
  (Stmt.tmpsList ss).map V.idx = ts ∧
    (all.all fun t => !(idxMask (Stmt.usesList ss)).testBit t) = true

theorem RangeFresh.append {ss ss' : List Stmt} {ts ts' all : List ℕ} (h : RangeFresh ss ts all)
    (h' : RangeFresh ss' ts' all) : RangeFresh (ss ++ ss') (ts ++ ts') all := by
  refine ⟨by rw [tmpsList_append, List.map_append, h.1, h'.1], ?_⟩
  have h1 := h.2
  have h2 := h'.2
  simp only [List.all_eq_true, Bool.not_eq_true'] at h1 h2 ⊢
  intro t ht
  rw [usesList_append, idxMask_append, Nat.testBit_or, h1 t ht, h2 t ht]
  rfl

/-- The ranges from `a` and from `a + n` make the range from `a`. -/
theorem rangeFresh_drop {l : List Stmt} {a n : ℕ} {ts ts' all : List ℕ}
    (h : RangeFresh ((l.drop a).take n) ts all) (h' : RangeFresh (l.drop (a + n)) ts' all) :
    RangeFresh (l.drop a) (ts ++ ts') all := by
  have := h.append h'
  rwa [← List.drop_drop, List.take_append_drop] at this

theorem rangeFresh_end {l : List Stmt} {a : ℕ} (ha : l.length ≤ a) (all : List ℕ) :
    RangeFresh (l.drop a) [] all := by
  rw [List.drop_eq_nil_of_le ha]
  refine ⟨rfl, ?_⟩
  simp [Stmt.usesList, idxMask]

/-- **A body certified by ranges is fresh**: its temporaries are `all`, distinct, and no
parameter. -/
theorem fn_fresh_of_rangeFresh {fn : Fn} {all : List ℕ} (h : RangeFresh fn.body all all)
    (hnd : all.Nodup) (hp : (all.all fun t => !(idxMask fn.params).testBit t) = true) :
    fn.Fresh := by
  have h2 := h.2
  simp only [List.all_eq_true, Bool.not_eq_true'] at h2 hp
  have hidx : ∀ t ∈ Stmt.tmpsList fn.body, t.idx ∈ all := fun t ht => by
    rw [← h.1]; exact List.mem_map_of_mem ht
  refine ⟨List.Nodup.of_map V.idx (by rw [h.1]; exact hnd), fun t ht => ⟨fun hu => ?_, fun hpm => ?_⟩⟩
  · have := h2 _ (hidx t ht)
    rw [testBit_idxMask hu] at this
    exact absurd this (by simp)
  · have := hp _ (hidx t ht)
    rw [testBit_idxMask hpm] at this
    exact absurd this (by simp)

/-! ## Paths -/

/-- The events of an outcome. -/
def Out.evs : Out → List Ev
  | .fall es => es
  | .ret es _ => es
  | .stuck => []

/-- The values an event names, a range check's temporaries apart. -/
def Ev.uses : Ev → List V
  | .atom a => atomUses a
  | .inK c => [c]
  | .call _ args rets => args ++ rets
  | .skip _ args => args

/-- A range check event's temporaries. -/
def Ev.tmps : Ev → List V
  | .atom a => atomTmps a
  | _ => []

section Walk

variable {σ σ' : Val}

theorem pick_congr {x : V} {args rets : List V} (hx : σ' x = σ x) :
    ∀ (fs : List String) (j : ℕ), pick σ' x args rets j fs = pick σ x args rets j fs
  | [], _ => rfl
  | f :: fs, j => by
      unfold pick
      rw [hx, pick_congr hx fs (j + 1)]

mutual
/-- **A path depends only on the block's uses.** -/
theorem walk1_congr : ∀ (s : Stmt), (∀ v ∈ Stmt.uses s, σ' v = σ v) → walk1 σ' s = walk1 σ s
  | .atom _, _ => rfl
  | .ite c z n, h => by
      simp only [Stmt.uses, List.mem_cons, List.mem_append] at h
      rw [walk1, walk1, h c (Or.inl rfl), walk_congr z fun v hv => h v (Or.inr (Or.inl hv)),
        walk_congr n fun v hv => h v (Or.inr (Or.inr hv))]
  | .match_ x arms, h => by
      simp only [Stmt.uses, List.mem_cons] at h
      rw [walk1, walk1]
      exact walkArms_congr x (h x (Or.inl rfl)) arms 0 fun v hv => h v (Or.inr hv)
  | .call .., _ => rfl
  | .callIf c f args, h => by
      rw [walk1, walk1, h c (by simp [Stmt.uses])]
  | .dispatch x fs args rets, h => by
      rw [walk1, walk1]
      exact pick_congr (h x (by simp [Stmt.uses])) fs 0
  | .ret _, _ => rfl

theorem walk_congr : ∀ (ss : List Stmt), (∀ v ∈ Stmt.usesList ss, σ' v = σ v) →
    walk σ' ss = walk σ ss
  | [], _ => rfl
  | s :: ss, h => by
      simp only [Stmt.usesList, List.mem_append] at h
      rw [walk, walk, walk1_congr s fun v hv => h v (Or.inl hv),
        walk_congr ss fun v hv => h v (Or.inr hv)]

theorem walkArms_congr (x : V) (hx : σ' x = σ x) : ∀ (arms : List (List Stmt)) (j : ℕ),
    (∀ v ∈ Stmt.usesArms arms, σ' v = σ v) → walkArms σ' x j arms = walkArms σ x j arms
  | [], _, _ => rfl
  | a :: as, j, h => by
      simp only [Stmt.usesArms, List.mem_append] at h
      unfold walkArms
      rw [hx, walk_congr a fun v hv => h v (Or.inl hv),
        walkArms_congr x hx as (j + 1) fun v hv => h v (Or.inr hv)]
end

/-- What a path's outcome names: events naming uses only, temporaries a sublist of the block's,
returned values uses. -/
def Out.Within (us ts : List V) : Out → Prop
  | .fall es => (∀ e ∈ es, ∀ v ∈ e.uses, v ∈ us) ∧ (es.flatMap Ev.tmps).Sublist ts
  | .ret es vs => (∀ e ∈ es, ∀ v ∈ e.uses, v ∈ us) ∧ (es.flatMap Ev.tmps).Sublist ts ∧
      ∀ v ∈ vs, v ∈ us
  | .stuck => True

theorem Out.within_mono {us us' ts ts' : List V} (hu : ∀ v ∈ us, v ∈ us') (ht : ts.Sublist ts') :
    ∀ {o : Out}, o.Within us ts → o.Within us' ts'
  | .fall _, ⟨h1, h2⟩ => ⟨fun e he v hv => hu v (h1 e he v hv), h2.trans ht⟩
  | .ret _ _, ⟨h1, h2, h3⟩ => ⟨fun e he v hv => hu v (h1 e he v hv), h2.trans ht,
      fun v hv => hu v (h3 v hv)⟩
  | .stuck, _ => trivial

theorem Out.within_pre {us ts ts' : List V} {es : List Ev} (h1 : ∀ e ∈ es, ∀ v ∈ e.uses, v ∈ us)
    (h2 : (es.flatMap Ev.tmps).Sublist ts) :
    ∀ {o : Out}, o.Within us ts' → (o.pre es).Within us (ts ++ ts')
  | .fall _, ⟨h1', h2'⟩ => ⟨fun e he => (List.mem_append.mp he).elim (h1 e) (h1' e),
      by rw [List.flatMap_append]; exact h2.append h2'⟩
  | .ret _ _, ⟨h1', h2', h3'⟩ => ⟨fun e he => (List.mem_append.mp he).elim (h1 e) (h1' e),
      by rw [List.flatMap_append]; exact h2.append h2', h3'⟩
  | .stuck, _ => trivial

theorem Out.within_seq {us ts ts' : List V} {k : Out} (hk : k.Within us ts') :
    ∀ {o : Out}, o.Within us ts → (o.seq k).Within us (ts ++ ts')
  | .fall _, ⟨h1, h2⟩ => Out.within_pre h1 h2 hk
  | .ret _ _, ⟨h1, h2, h3⟩ => ⟨h1, h2.trans (List.sublist_append_left _ _), h3⟩
  | .stuck, _ => trivial

theorem pick_within {x : V} {args rets : List V} {us : List V}
    (ha : ∀ v ∈ args ++ rets, v ∈ us) :
    ∀ (fs : List String) (j : ℕ), (pick σ x args rets j fs).Within us []
  | [], _ => trivial
  | f :: fs, j => by
      unfold pick
      split_ifs
      · refine ⟨fun e he v hv => ?_, by simp [Ev.tmps]⟩
        rw [List.mem_singleton] at he
        subst he
        exact ha v hv
      · exact pick_within ha fs (j + 1)

mutual
theorem walk1_within : ∀ (s : Stmt), (walk1 σ s).Within (Stmt.uses s) (Stmt.tmps s)
  | .atom a => ⟨fun e he v hv => by rw [List.mem_singleton] at he; subst he; exact hv,
      by simp [Ev.tmps, Stmt.tmps]⟩
  | .ite c z n => by
      rw [walk1, Stmt.tmps, ← List.nil_append (Stmt.tmpsList z ++ Stmt.tmpsList n)]
      refine Out.within_pre (fun e he v hv => ?_) (by simp [Ev.tmps]) ?_
      · rw [List.mem_singleton] at he; subst he
        simp only [Ev.uses, List.mem_singleton] at hv; subst hv
        simp [Stmt.uses]
      · split_ifs
        · exact Out.within_mono (fun v hv => by simp [Stmt.uses, hv])
            (List.sublist_append_left _ _) (walk_within z)
        · exact Out.within_mono (fun v hv => by simp [Stmt.uses, hv])
            (List.sublist_append_right _ _) (walk_within n)
  | .match_ x arms => Out.within_mono (fun v hv => by simp [Stmt.uses, hv]) (by rw [Stmt.tmps])
      (walkArms_within x arms 0)
  | .call f args rets => ⟨fun e he v hv => by
      rw [List.mem_singleton] at he; subst he; simpa [Stmt.uses, Ev.uses] using hv, by simp [Ev.tmps]⟩
  | .callIf c f args => by
      rw [walk1]
      refine ⟨fun e he v hv => ?_, by split_ifs <;> simp [Ev.tmps]⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · simp only [Ev.uses, List.mem_singleton] at hv; subst hv; simp [Stmt.uses]
      · split_ifs at hv <;> simp only [Ev.uses, List.append_nil] at hv <;> simp [Stmt.uses, hv]
  | .dispatch x fs args rets => Out.within_mono (fun v hv => hv) (List.nil_sublist _)
      (pick_within (fun v hv => by simp only [Stmt.uses, List.mem_cons]; exact Or.inr hv) fs 0)
  | .ret vs => ⟨fun _ he => (List.not_mem_nil he).elim, by simp, fun v hv => by simpa [Stmt.uses]⟩

theorem walk_within : ∀ (ss : List Stmt), (walk σ ss).Within (Stmt.usesList ss) (Stmt.tmpsList ss)
  | [] => ⟨fun _ he => (List.not_mem_nil he).elim, by simp⟩
  | s :: ss => by
      rw [walk, Stmt.tmpsList]
      exact Out.within_seq
        (Out.within_mono (fun v hv => by simp [Stmt.usesList, hv]) (List.Sublist.refl _)
          (walk_within ss))
        (Out.within_mono (fun v hv => by simp [Stmt.usesList, hv]) (List.Sublist.refl _)
          (walk1_within s))

theorem walkArms_within (x : V) : ∀ (arms : List (List Stmt)) (j : ℕ),
    (walkArms σ x j arms).Within (Stmt.usesArms arms) (Stmt.tmpsArms arms)
  | [], _ => trivial
  | a :: as, j => by
      unfold walkArms
      split_ifs
      · exact Out.within_mono (fun v hv => by simp [Stmt.usesArms, hv])
          (by rw [Stmt.tmpsArms]; exact List.sublist_append_left _ _) (walk_within a)
      · exact Out.within_mono (fun v hv => by simp [Stmt.usesArms, hv])
          (by rw [Stmt.tmpsArms]; exact List.sublist_append_right _ _) (walkArms_within x as (j + 1))
end

end Walk

end
end LeanVM.Guest.Memory
