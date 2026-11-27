/-
  LeanVM.Guest.CoreMode.Fam.Wit

  Witnessed checks over a body: sub-spines picked by a bitset, names looked up by their codes, and
  the walkers' monotonicity, so that a generated certificate's search runs over the few events it
  names and its result is the check's.
-/

module

public import LeanVM.Guest.CoreMode.Fam.Down
public import LeanVM.Guest.Memory.ScopeDefs
public import LeanVM.Guest.Memory.Static
public import LeanVM.Guest.Bridge.PairDefs
public import LeanVM.Guest.NameIx
public import LeanVM.Guest.Memory.Family
public import LeanVM.Guest.ExecCore

/-!
# Witnessed checks

The carried facts' checks (`carryG`, `carryNzG`, `CoreMode.carryExpB`, `callersG`, `callersM`) search a function's
whole spine for each value they pin, and compare each call site's callee with every entry of a list of names. Their
witnessed forms take from the generator:

* a **sub-spine**: the events at the set bits of a number (`pickB`), the events a search uses. Each search is
  monotone in the events it scans, so its success over the sub-spine is its success over the spine
  (`mem_pickB`, and each search's `_mono`);
* **name tables**: a list of entries keyed by name as a search tree by the name's code (`encS`, `NTab`), each
  entry's payload under its name's code (`tab_all`: a check of the payloads under a callee's code is the check of
  the list's entries of that callee). The table is written by the generator and checked against its list once
  (`tabOk`), or built by the kernel from the list (`NTab.ofNamed`, which holds each entry, `ofNamed_all`).

`allB_ctx`, `sitesB_imp`, `blockAll_imp`, `RangeOk.imp`: the walkers are monotone in their predicates, `allB` with
every context it passes extending its first.
-/

namespace LeanVM.Guest.Res

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Exec (natSeq natSeq_eq)
open LeanVM.Guest.Bridge (blockAll armsAll)

@[expose] public section

/-- **The elements of `l` at the set bits of `b`**, bit `0` the first: by the recursor, for the kernel. -/
def pickB {α : Type} (b : ℕ) (l : List α) : List α :=
  List.rec (motive := fun _ ↦ ℕ → List α) (fun _ ↦ [])
    (fun x _ ih b ↦ bif Nat.beq (Nat.mod b 2) 1 then x :: ih (Nat.div b 2) else ih (Nat.div b 2)) l b

/-- **A name table**: under a name's code (`encS`), the payloads of the entries of that name. -/
abbrev NTab (α : Type) := NTree (List α)

/-- The payloads under a code, the code evaluated first. -/
def NTab.at {α : Type} (t : NTab α) (k : ℕ) : List α := natSeq k fun k ↦ (t.find k).getD []

/-- `a` added under key `k`. -/
def NTab.ins {α : Type} (k : ℕ) (a : α) : NTab α → NTab α
  | .leaf => .node k [a] .leaf .leaf
  | .node k' v l r => if Nat.beq k k' then .node k' (a :: v) l r
      else if Nat.blt k k' then .node k' v (NTab.ins k a l) r else .node k' v l (NTab.ins k a r)

/-- **The table of a list of keyed payloads**, built by the kernel. -/
def NTab.ofList {α : Type} (l : List (ℕ × α)) : NTab α := l.foldr (fun p t ↦ NTab.ins p.1 p.2 t) .leaf

/-- **The table of a list of named entries**: each entry's payload `φ` under its name's code. -/
def NTab.ofNamed {α β : Type} (φ : β → α) (L : List (String × β)) : NTab α :=
  NTab.ofList (L.map fun c ↦ (encS c.1, φ c.2))

/-- A function's witness by its index, `0` when it has none, the index evaluated first. -/
def witAt (t : NTree ℕ) (j : ℕ) : ℕ := natSeq j fun j ↦ (t.find j).getD 0

/-- Every entry of a search tree passes `p` of its key and value. -/
def NTree.allK {α : Type} (p : ℕ → α → Bool) : NTree α → Bool
  | .leaf => true
  | .node k v l r => p k v && NTree.allK p l && NTree.allK p r

/-- **A table of a list**: each entry's payload under its name's code, and each payload under a code an entry's
of a name of that code. -/
def tabOk {α β : Type} [BEq α] (L : List (String × β)) (t : NTab α) (φ : β → α) : Bool :=
  L.all (fun c ↦ (t.at (encS c.1)).contains (φ c.2)) &&
    NTree.allK (fun k is ↦ is.all fun i ↦ L.any fun c ↦ Nat.beq (encS c.1) k && φ c.2 == i) t

end

public section

theorem mem_pickB {α : Type} {x : α} : ∀ {l : List α} {b : ℕ}, x ∈ pickB b l → x ∈ l
  | [], _, h => by simp [pickB] at h
  | y :: l, b, h => by
    change x ∈ (bif Nat.beq (Nat.mod b 2) 1 then y :: pickB (Nat.div b 2) l else pickB (Nat.div b 2) l) at h
    generalize Nat.beq (Nat.mod b 2) 1 = c at h
    cases c
    · exact List.mem_cons_of_mem _ (mem_pickB (h : x ∈ pickB (Nat.div b 2) l))
    · rcases List.mem_cons.mp (h : x ∈ y :: pickB (Nat.div b 2) l) with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mem_pickB h)

/-- **A check of a list's entries of one name, by the table**: the entries `(g, b)` of `L` pass `P b` when the
payloads under `g`'s code pass `Q`, the table holding each entry's payload `φ b` under its name's code. -/
theorem tab_all {α β : Type} [BEq α] [LawfulBEq α] {L : List (String × β)} {t : NTab α} {φ : β → α}
    (hc : L.all (fun c ↦ (t.at (encS c.1)).contains (φ c.2)) = true) {g : String} {P : β → Bool} {Q : α → Bool}
    (hPQ : ∀ b, Q (φ b) = true → P b = true) (h : (t.at (encS g)).all Q = true) :
    L.all (fun c ↦ c.1 != g || P c.2) = true := by
  rw [List.all_eq_true] at hc ⊢
  intro c hcL
  by_cases hg : c.1 = g
  · have hm := hc c hcL
    rw [hg, List.contains_iff_mem] at hm
    rw [hPQ c.2 (List.all_eq_true.mp h _ hm), Bool.or_true]
  · simp [hg]

theorem NTree.find_allK {α : Type} {p : ℕ → α → Bool} : ∀ {t : NTree α} {k : ℕ} {v : α}, NTree.allK p t = true →
    t.find k = some v → p k v = true
  | .leaf, _, _, _, h => by simp [NTree.find] at h
  | .node k' v' l r, k, v, ha, h => by
    simp only [NTree.allK, Bool.and_eq_true] at ha
    simp only [NTree.find] at h
    split_ifs at h with h1 h2
    · cases h; rw [Nat.eq_of_beq_eq_true h1]; exact ha.1.1
    · exact NTree.find_allK ha.1.2 h
    · exact NTree.find_allK ha.2 h

theorem tabOk.all {α β : Type} [BEq α] [LawfulBEq α] {L : List (String × β)} {t : NTab α} {φ : β → α}
    (h : tabOk L t φ = true) : L.all (fun c ↦ (t.at (encS c.1)).contains (φ c.2)) = true :=
  (Bool.and_eq_true _ _ ▸ h).1

/-- A payload under a name's code is an entry's of that name. -/
theorem tabOk.mem {α β : Type} [BEq α] [LawfulBEq α] {L : List (String × β)} {t : NTab α} {φ : β → α}
    (h : tabOk L t φ = true) {g : String} {i : α} (hi : i ∈ t.at (encS g)) : ∃ c ∈ L, c.1 = g ∧ φ c.2 = i := by
  have h2 := (Bool.and_eq_true _ _ ▸ h).2
  unfold NTab.at at hi
  rw [natSeq_eq] at hi
  cases hf : t.find (encS g) with
  | none => rw [hf] at hi; simp at hi
  | some is =>
    rw [hf, Option.getD_some] at hi
    have := List.all_eq_true.mp (NTree.find_allK h2 hf) i hi
    obtain ⟨c, hc, he⟩ := List.any_eq_true.mp this
    simp only [Bool.and_eq_true, beq_iff_eq] at he
    exact ⟨c, hc, encS_inj (Nat.eq_of_beq_eq_true he.1), he.2⟩

private theorem find_ins_self {α : Type} (k : ℕ) (a : α) : ∀ (t : NTab α),
    ((NTab.ins k a t).find k).getD [] = a :: (t.find k).getD []
  | .leaf => by simp [NTab.ins, NTree.find]
  | .node k0 v l r => by
    unfold NTab.ins
    by_cases h1 : Nat.beq k k0 = true
    · simp only [h1, ↓reduceIte]; simp [NTree.find, h1]
    · simp only [h1, Bool.false_eq_true, ↓reduceIte]
      by_cases h2 : Nat.blt k k0 = true
      · simp only [h2, ↓reduceIte]; simp [NTree.find, h1, h2, find_ins_self k a l]
      · simp only [h2, Bool.false_eq_true, ↓reduceIte]; simp [NTree.find, h1, h2, find_ins_self k a r]

private theorem find_ins_ne {α : Type} (k k' : ℕ) (a : α) (hk : k' ≠ k) : ∀ (t : NTab α),
    ((NTab.ins k a t).find k').getD [] = (t.find k').getD []
  | .leaf => by simp [NTab.ins, NTree.find, hk]
  | .node k0 v l r => by
    unfold NTab.ins
    by_cases h1 : Nat.beq k k0 = true
    · simp only [h1, ↓reduceIte]
      have e := Nat.eq_of_beq_eq_true h1
      subst e
      simp [NTree.find, hk]
    · simp only [h1, Bool.false_eq_true, ↓reduceIte]
      by_cases h2 : Nat.blt k k0 = true
      · simp only [h2, ↓reduceIte, NTree.find]
        split_ifs
        · rfl
        · exact find_ins_ne k k' a hk l
        · rfl
      · simp only [h2, Bool.false_eq_true, ↓reduceIte, NTree.find]
        split_ifs
        · rfl
        · rfl
        · exact find_ins_ne k k' a hk r

private theorem getD_find_ins {α : Type} (k k' : ℕ) (a : α) (t : NTab α) :
    ((NTab.ins k a t).find k').getD [] = if k' = k then a :: (t.find k').getD [] else (t.find k').getD [] := by
  split_ifs with h
  · subst h; exact find_ins_self k' a t
  · exact find_ins_ne k k' a h t

theorem mem_at_ofList {α : Type} {k : ℕ} {a : α} : ∀ {l : List (ℕ × α)}, (k, a) ∈ l → a ∈ (NTab.ofList l).at k
  | p :: l, h => by
    unfold NTab.at
    rw [natSeq_eq]
    change a ∈ ((NTab.ins p.1 p.2 (NTab.ofList l)).find k).getD []
    rw [getD_find_ins]
    rcases List.mem_cons.mp h with rfl | h
    · simp
    · have ih := mem_at_ofList h
      unfold NTab.at at ih
      rw [natSeq_eq] at ih
      split_ifs <;> simp [ih]

/-- **A named list's own table holds each entry.** -/
theorem ofNamed_all {α β : Type} [BEq α] [LawfulBEq α] (φ : β → α) (L : List (String × β)) :
    L.all (fun c ↦ ((NTab.ofNamed φ L).at (encS c.1)).contains (φ c.2)) = true := by
  rw [List.all_eq_true]
  intro c hc
  rw [List.contains_iff_mem]
  exact mem_at_ofList (List.mem_map.mpr ⟨c, hc, rfl⟩)

/-- `List.any` over a sublist, by a weaker predicate. -/
theorem any_imp {α : Type} {l l' : List α} {p p' : α → Bool} (hl : ∀ x ∈ l, x ∈ l')
    (hp : ∀ x, p x = true → p' x = true) (h : l.any p = true) : l'.any p' = true := by
  obtain ⟨x, hx, hpx⟩ := List.any_eq_true.mp h
  exact List.any_eq_true.mpr ⟨x, hl x hx, hp x hpx⟩

/-- `List.any` over a sublist. -/
theorem any_sub {α : Type} {l l' : List α} {p : α → Bool} (hl : ∀ x ∈ l, x ∈ l') (h : l.any p = true) :
    l'.any p = true :=
  any_imp hl (fun _ ↦ id) h

/-- `List.all` by a weaker predicate. -/
theorem all_imp {α : Type} {l : List α} {p p' : α → Bool} (hp : ∀ x, p x = true → p' x = true)
    (h : l.all p = true) : l.all p' = true :=
  List.all_eq_true.mpr fun x hx ↦ hp x (List.all_eq_true.mp h x hx)

/-! ## The walkers, monotone -/

theorem walkOk_imp {α : Type} {c c' : ℕ → α → Bool} (h : ∀ j x, c j x = true → c' j x = true) :
    ∀ (j : ℕ) (l : List α), walkOk c j l = true → walkOk c' j l = true
  | _, [], _ => rfl
  | j, x :: l, hw => by
    simp only [walkOk, Bool.and_eq_true] at hw ⊢
    exact ⟨h j x hw.1, walkOk_imp h (j + 1) l hw.2⟩

theorem RangeOk.imp {c c' : ℕ → Fn → Bool} {a n : ℕ} (h : ∀ j fn, c j fn = true → c' j fn = true)
    (hr : RangeOk c a n) : RangeOk c' a n :=
  walkOk_imp h _ _ hr

section

variable {p q : String → List V → List V → Bool}

mutual
theorem sitesS_imp (h : ∀ f a r, q f a r = true → p f a r = true) :
    ∀ (s : Stmt), sitesS q s = true → sitesS p s = true
  | .atom _, _ => rfl
  | .ite _ z n, hs => by
    replace hs : (sitesB q z && sitesB q n) = true := hs
    show (sitesB p z && sitesB p n) = true
    simp only [Bool.and_eq_true] at hs ⊢
    exact ⟨sitesB_imp h z hs.1, sitesB_imp h n hs.2⟩
  | .match_ _ arms, hs => sitesA_imp h arms hs
  | .call f a r, hs => h f a r hs
  | .callIf _ f a, hs => h f a [] hs
  | .dispatch _ fs a r, hs => all_imp (fun f ↦ h f a r) hs
  | .ret _, _ => rfl

theorem sitesB_imp (h : ∀ f a r, q f a r = true → p f a r = true) :
    ∀ (ss : List Stmt), sitesB q ss = true → sitesB p ss = true
  | [], _ => rfl
  | s :: ss, hs => by
    replace hs : (sitesS q s && sitesB q ss) = true := hs
    show (sitesS p s && sitesB p ss) = true
    simp only [Bool.and_eq_true] at hs ⊢
    exact ⟨sitesS_imp h s hs.1, sitesB_imp h ss hs.2⟩

theorem sitesA_imp (h : ∀ f a r, q f a r = true → p f a r = true) :
    ∀ (as : List (List Stmt)), sitesA q as = true → sitesA p as = true
  | [], _ => rfl
  | b :: as, hs => by
    replace hs : (sitesB q b && sitesA q as) = true := hs
    show (sitesB p b && sitesA p as) = true
    simp only [Bool.and_eq_true] at hs ⊢
    exact ⟨sitesB_imp h b hs.1, sitesA_imp h as hs.2⟩
end

end

theorem blockAll_cons (p : Atom → Bool) (s : Stmt) (ss : List Stmt) :
    blockAll p (s :: ss) = (blockAll p [s] && blockAll p ss) := by
  show (_ && _) = ((_ && true) && _)
  rw [Bool.and_true]
  rfl

section

variable {p q : Atom → Bool}

mutual
theorem blockAll1_imp (h : ∀ a, q a = true → p a = true) :
    ∀ (s : Stmt), blockAll q [s] = true → blockAll p [s] = true
  | .atom a, hs => by
    replace hs : (q a && true) = true := hs
    show (p a && true) = true
    simp only [Bool.and_true] at hs ⊢
    exact h a hs
  | .ite _ z n, hs => by
    replace hs : ((blockAll q z && blockAll q n) && true) = true := hs
    show ((blockAll p z && blockAll p n) && true) = true
    simp only [Bool.and_true, Bool.and_eq_true] at hs ⊢
    exact ⟨blockAll_imp h z hs.1, blockAll_imp h n hs.2⟩
  | .match_ _ arms, hs => by
    replace hs : (armsAll q arms && true) = true := hs
    show (armsAll p arms && true) = true
    simp only [Bool.and_true] at hs ⊢
    exact armsAll_imp h arms hs
  | .call .., _ => rfl
  | .callIf .., _ => rfl
  | .dispatch .., _ => rfl
  | .ret _, _ => rfl

theorem blockAll_imp (h : ∀ a, q a = true → p a = true) :
    ∀ (ss : List Stmt), blockAll q ss = true → blockAll p ss = true
  | [], _ => rfl
  | s :: ss, hs => by
    rw [blockAll_cons, Bool.and_eq_true] at hs ⊢
    exact ⟨blockAll1_imp h s hs.1, blockAll_imp h ss hs.2⟩

theorem armsAll_imp (h : ∀ a, q a = true → p a = true) :
    ∀ (as : List (List Stmt)), armsAll q as = true → armsAll p as = true
  | [], _ => rfl
  | b :: as, hs => by
    replace hs : (blockAll q b && armsAll q as) = true := hs
    show (blockAll p b && armsAll p as) = true
    simp only [Bool.and_eq_true] at hs ⊢
    exact ⟨blockAll_imp h b hs.1, armsAll_imp h as hs.2⟩
end

end

section

variable {p q : List Ev → Stmt → Bool} {ctx0 : List Ev}

mutual
theorem allS_ctx (h : ∀ c s, (∀ e ∈ ctx0, e ∈ c) → q c s = true → p c s = true) :
    ∀ (s : Stmt) (ctx : List Ev), (∀ e ∈ ctx0, e ∈ ctx) → allS q s ctx = true → allS p s ctx = true
  | .atom a, ctx, hc, hs => h ctx (.atom a) hc hs
  | .ite c z n, ctx, hc, hs => by
    replace hs : (q ctx (.ite c z n) && allB q z (ctx ++ spineE z) && allB q n (ctx ++ spineE n)) = true := hs
    show (p ctx (.ite c z n) && allB p z (ctx ++ spineE z) && allB p n (ctx ++ spineE n)) = true
    simp only [Bool.and_eq_true] at hs ⊢
    have ha : ∀ l, ∀ e ∈ ctx0, e ∈ ctx ++ l := fun l e he ↦ List.mem_append_left _ (hc e he)
    exact ⟨⟨h _ _ hc hs.1.1, allB_ctx h z _ (ha _) hs.1.2⟩, allB_ctx h n _ (ha _) hs.2⟩
  | .match_ x arms, ctx, hc, hs => by
    replace hs : (q ctx (.match_ x arms) && allA q arms ctx) = true := hs
    show (p ctx (.match_ x arms) && allA p arms ctx) = true
    simp only [Bool.and_eq_true] at hs ⊢
    exact ⟨h _ _ hc hs.1, allA_ctx h arms ctx hc hs.2⟩
  | .call f a r, ctx, hc, hs => h ctx (.call f a r) hc hs
  | .callIf c f a, ctx, hc, hs => h ctx (.callIf c f a) hc hs
  | .dispatch x fs a r, ctx, hc, hs => h ctx (.dispatch x fs a r) hc hs
  | .ret vs, ctx, hc, hs => h ctx (.ret vs) hc hs

theorem allB_ctx (h : ∀ c s, (∀ e ∈ ctx0, e ∈ c) → q c s = true → p c s = true) :
    ∀ (ss : List Stmt) (ctx : List Ev), (∀ e ∈ ctx0, e ∈ ctx) → allB q ss ctx = true → allB p ss ctx = true
  | [], _, _, _ => rfl
  | s :: ss, ctx, hc, hs => by
    replace hs : (allS q s ctx && allB q ss ctx) = true := hs
    show (allS p s ctx && allB p ss ctx) = true
    simp only [Bool.and_eq_true] at hs ⊢
    exact ⟨allS_ctx h s ctx hc hs.1, allB_ctx h ss ctx hc hs.2⟩

theorem allA_ctx (h : ∀ c s, (∀ e ∈ ctx0, e ∈ c) → q c s = true → p c s = true) :
    ∀ (as : List (List Stmt)) (ctx : List Ev), (∀ e ∈ ctx0, e ∈ ctx) → allA q as ctx = true →
      allA p as ctx = true
  | [], _, _, _ => rfl
  | b :: as, ctx, hc, hs => by
    replace hs : (allB q b (ctx ++ spineE b) && allA q as ctx) = true := hs
    show (allB p b (ctx ++ spineE b) && allA p as ctx) = true
    simp only [Bool.and_eq_true] at hs ⊢
    exact ⟨allB_ctx h b _ (fun e he ↦ List.mem_append_left _ (hc e he)) hs.1, allA_ctx h as ctx hc hs.2⟩
end

end

end

end LeanVM.Guest.Res
