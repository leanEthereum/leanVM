/-
  LeanVM.Guest.CoreMode.Fam.CarryWit

  The carried facts' checks (`Res.carryG`, `Res.carryNzG`) from witnessed checks: each search over the
  function's spine run over the sub-spine the generator names, each list of names read through its table.
-/

module

public import LeanVM.Guest.CoreMode.Fam.CarryDefs
public import LeanVM.Guest.CoreMode.Fam.Wit

/-!
# The carried facts, witnessed

The searches of `CarryDefs.lean` (`kOf`, `kIn`, `nzOf`, `tabNz`, `selTabB`, `ptrOk`) are monotone in the events they
scan and the values they are given (`*_mono`), so a search that succeeds over a sub-spine (`pickB b` of the spine,
`b` the generator's bitset of the events its derivations use) succeeds over the spine. `carryGW` and `carryNzW` are
`carryG` and `carryNzG` with every search over the sub-spine and every list of names read through its table
(`NTab`, `tabOk`: the table holds exactly the list's entries, which one kernel evaluation checks per list);
`carryG_of_wit`, `carryNzG_of_wit` give the checks. Each statement's context extends the body's spine (`allB_ctx`),
so a search over the sub-spine serves every statement.
-/

namespace LeanVM.Guest.Res

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Bridge (spine blockAll ptrOk allocOf loadPtr loadPtr0 heapPtr0)

@[expose] public section

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
  cases hf : t.find (encS g) with
  | none => rw [hf] at hi; simp at hi
  | some is =>
    rw [hf, Option.getD_some] at hi
    have := List.all_eq_true.mp (NTree.find_allK h2 hf) i hi
    obtain ⟨c, hc, he⟩ := List.any_eq_true.mp this
    simp only [Bool.and_eq_true, beq_iff_eq] at he
    exact ⟨c, hc, encS_inj (Nat.eq_of_beq_eq_true he.1), he.2⟩

/-! ## The searches, monotone -/

section

variable {kv kv' : List V}

/-- Values listed. -/
theorem kv_mono (hk : ∀ x ∈ kv, x ∈ kv') {v : V} (h : kv.any (veq · v) = true) : kv'.any (veq · v) = true :=
  any_sub hk h

/-! ### Over events -/

variable {sp sp' : List Ev} (hk : ∀ x ∈ kv, x ∈ kv') (hs : ∀ e ∈ sp, e ∈ sp')
include hk hs

theorem kIn0_mono {v : V} (h : kIn0 kv sp v = true) : kIn0 kv' sp' v = true := by
  unfold kIn0 at h ⊢
  simp only [Bool.or_eq_true] at h ⊢
  exact h.imp (any_sub hk) (any_sub hs)

theorem kIn1_mono {v : V} (h : kIn1 kv sp v = true) : kIn1 kv' sp' v = true := by
  unfold kIn1 at h ⊢
  simp only [Bool.or_eq_true] at h ⊢
  refine h.imp (kIn0_mono hk hs) (any_imp hs fun e he ↦ ?_)
  rcases e with ⟨a⟩ | _ | _ | _ <;> (try cases a) <;> try exact he
  all_goals
    simp only [Bool.and_eq_true] at he ⊢
    exact ⟨⟨he.1.1, kIn0_mono hk hs he.1.2⟩, kIn0_mono hk hs he.2⟩

theorem kIn_mono : ∀ {n : ℕ} {v : V}, kIn kv sp n v = true → kIn kv' sp' n v = true
  | 0, v, h => by
    unfold kIn at h ⊢
    simp only [Bool.or_eq_true] at h ⊢
    exact h.imp (any_sub hk) (any_sub hs)
  | n + 1, v, h => by
    unfold kIn at h ⊢
    simp only [Bool.or_eq_true] at h ⊢
    refine h.imp (Or.imp (any_sub hk) (any_sub hs)) (any_imp hs fun e he ↦ ?_)
    rcases e with ⟨a⟩ | _ | _ | _ <;> (try cases a) <;> try exact he
    · simp only [Bool.and_eq_true] at he ⊢
      exact ⟨⟨he.1.1, kIn1_mono hk hs he.1.2⟩, kIn1_mono hk hs he.2⟩
    · simp only [Bool.and_eq_true] at he ⊢
      exact ⟨⟨he.1.1, kIn_mono he.1.2⟩, kIn_mono he.2⟩

omit hk in
theorem tabAt_mono {nz nz' : V → Bool} (hn : ∀ w, nz w = true → nz' w = true) {T J : V} {off : ℕ}
    (h : tabAt sp nz T J off = true) : tabAt sp' nz' T J off = true := by
  unfold tabAt at h ⊢
  refine any_imp hs (fun e he ↦ ?_) h
  rcases e with ⟨a⟩ | _ | _ | _ <;> (try cases a) <;> try exact he
  simp only [Bool.and_eq_true] at he ⊢
  refine ⟨he.1, any_imp hs (fun e he ↦ ?_) he.2⟩
  rcases e with ⟨a⟩ | _ | _ | _ <;> (try cases a) <;> try exact he
  simp only [Bool.and_eq_true] at he ⊢
  refine ⟨he.1, ?_⟩
  revert he
  rename_i c
  cases powOf c with
  | none => exact fun he ↦ he.2
  | some m =>
    intro he
    simp only [Bool.and_eq_true] at he ⊢
    refine ⟨he.2.1, all_imp (fun t ht ↦ any_imp hs (fun e he ↦ ?_) ht) he.2.2⟩
    rcases e with ⟨a⟩ | _ | _ | _ <;> (try cases a) <;> try exact he
    simp only [Bool.and_eq_true] at he ⊢
    exact ⟨he.1, hn _ he.2⟩

omit hk in
theorem tabNz_mono {nz nz' : V → Bool} (hn : ∀ w, nz w = true → nz' w = true) {p : V} {off : ℕ}
    (h : tabNz sp nz p off = true) : tabNz sp' nz' p off = true := by
  unfold tabNz at h ⊢
  refine any_imp hs (fun e he ↦ ?_) h
  rcases e with ⟨a⟩ | _ | _ | _ <;> (try cases a) <;> try exact he
  simp only [Bool.and_eq_true, Bool.or_eq_true] at he ⊢
  exact ⟨he.1, he.2.imp (tabAt_mono hs hn) (tabAt_mono hs hn)⟩

theorem nzOf_mono : ∀ {n : ℕ} {v : V}, nzOf kv sp n v = true → nzOf kv' sp' n v = true
  | 0, v, h => by
    unfold nzOf at h ⊢
    simp only [Bool.or_eq_true] at h ⊢
    exact h.imp (any_sub hk) (any_sub hs)
  | n + 1, v, h => by
    unfold nzOf at h ⊢
    simp only [Bool.or_eq_true] at h ⊢
    refine h.imp (Or.imp (any_sub hk) (any_sub hs)) (any_imp hs fun e he ↦ ?_)
    have ih : ∀ u, nzOf kv sp n u = true → nzOf kv' sp' n u = true := fun u ↦ nzOf_mono
    have ik : ∀ u, kIn kv sp kDepth u = true → kIn kv' sp' kDepth u = true := fun u ↦ kIn_mono hk hs
    rcases e with ⟨a⟩ | _ | _ | _ <;> (try cases a) <;> try exact he
    · simp only [Bool.and_eq_true, Bool.or_eq_true] at he ⊢
      rcases he with (⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩) | ⟨⟨h1, h2⟩, h3⟩
      · exact .inl (.inl ⟨⟨h1, ih _ h2⟩, ih _ h3⟩)
      · exact .inl (.inr ⟨⟨h1, ik _ h2⟩, ih _ h3⟩)
      · exact .inr ⟨⟨h1, ik _ h2⟩, ih _ h3⟩
    · simp only [Bool.and_eq_true, Bool.or_eq_true] at he ⊢
      exact he.imp (fun h ↦ ⟨h.1, ih _ h.2⟩) (fun h ↦ ⟨h.1, ih _ h.2⟩)
    · simp only [Bool.and_eq_true] at he ⊢
      exact ⟨he.1, tabNz_mono hs ih he.2⟩
    · simp only [Bool.and_eq_true, Bool.or_eq_true] at he ⊢
      exact he.imp (fun h ↦ ⟨h.1, ih _ h.2⟩) (fun h ↦ ⟨h.1, ih _ h.2⟩)

end

section

variable {sp sp' : List Ev} (hs : ∀ e ∈ sp, e ∈ sp')
include hs

theorem retNz_mono {j : ℕ} {s : Stmt} (h : retNz j sp s = true) : retNz j sp' s = true := by
  cases s <;> try exact h
  rename_i vs
  revert h
  show (match vs[j]? with | some v => nzOf [] sp nzDepth v | none => false) = true →
    (match vs[j]? with | some v => nzOf [] sp' nzDepth v | none => false) = true
  cases vs[j]? with
  | none => exact id
  | some v => exact nzOf_mono (fun _ h ↦ h) hs

theorem selTabAt_mono {sels : List (V × ℕ)} {T J : V} {off : ℕ} (h : selTabAt sp sels T J off = true) :
    selTabAt sp' sels T J off = true := by
  unfold selTabAt at h ⊢
  refine any_imp (fun _ h ↦ h) (fun c hc ↦ ?_) h
  simp only [Bool.and_eq_true] at hc ⊢
  refine ⟨hc.1, all_imp (fun t ht ↦ any_imp hs (fun e he ↦ ?_) ht) hc.2⟩
  rcases e with ⟨a⟩ | _ | _ | _ <;> (try cases a) <;> try exact he
  simp only [Bool.and_eq_true] at he ⊢
  exact ⟨he.1, nzOf_mono (fun _ h ↦ h) hs he.2⟩

end

/-! ### Over atoms -/

section

variable {sp sp' : List Atom} (hs : ∀ a ∈ sp, a ∈ sp')
include hs

theorem kOf_mono {kv : List V} : ∀ {n : ℕ} {v : V}, kOf kv sp n v = true → kOf kv sp' n v = true
  | 0, v, h => by
    unfold kOf at h ⊢
    simp only [Bool.or_eq_true] at h ⊢
    exact h.imp id (any_sub hs)
  | n + 1, v, h => by
    unfold kOf at h ⊢
    simp only [Bool.or_eq_true] at h ⊢
    refine h.imp (Or.imp id (any_sub hs)) (any_imp hs fun a ha ↦ ?_)
    cases a <;> try exact ha
    simp only [Bool.and_eq_true] at ha ⊢
    exact ⟨⟨ha.1.1, kOf_mono ha.1.2⟩, kOf_mono ha.2⟩

theorem ptrOk_mono {p : V} (h : ptrOk sp p = true) : ptrOk sp' p = true := by
  unfold ptrOk at h ⊢
  simp only [Bool.and_eq_true, Bool.or_eq_true] at h ⊢
  exact ⟨h.1.imp (any_sub hs) (any_sub hs), h.2.imp (any_sub hs) (any_sub hs)⟩

theorem witAtomC_mono {fn : Fn} {a : Atom} (h : witAtomC fn sp a = true) : witAtomC fn sp' a = true := by
  unfold witAtomC at h ⊢
  split at h <;> try exact h
  simp only [Bool.or_eq_true, Bool.and_eq_true] at h ⊢
  exact h.imp (ptrOk_mono hs) (fun h ↦ ⟨⟨kOf_mono hs h.1.1, h.1.2⟩, h.2⟩)

end

end

/-! ## The checks, witnessed -/

@[expose] public section

/-- `selTabB` over a spine and selectors. -/
noncomputable def selTabS (sp : List Ev) (sels : List (V × ℕ)) (v : V) : Bool :=
  sp.any fun
    | .atom (.load d p off) => veq d v && sp.any (fun
        | .atom (.mul q a b) => veq q p && (selTabAt sp sels a b off || selTabAt sp sels b a off)
        | _ => false)
    | _ => false

/-- **`siteNz` by the table of `carriedNz`**, over a sub-spine. -/
noncomputable def siteNzW (T : NTab ℕ) (kv : List V) (sp : List Ev) (f : String) (args : List V) : Bool :=
  (T.at (encS f)).all fun i ↦ match args[i]? with
    | some a => nzOf kv sp nzDepth a
    | none => false

/-- **`nzStmt`, witnessed**: in no context, over a sub-spine. -/
noncomputable def nzStmtW (T : NTab ℕ) (kv : List V) (sp : List Ev) : Stmt → Bool
  | .atom (.hint (.allocDyn _ s)) => nzOf kv sp nzDepth s
  | .call f args _ => siteNzW T kv sp f args
  | .callIf _ f args => siteNzW T kv sp f args
  | .dispatch _ fs args _ => fs.all fun f ↦ siteNzW T kv sp f args
  | _ => true

/-- `kvNz` by the tables of `carriedNz` and `ownNz`. -/
def kvNzW (T O : NTab ℕ) (fn : Fn) : List V :=
  ((T.at (encS fn.name)).filterMap fun i ↦ fn.params[i]?) ++ (if fn.loop then fn.params.take 1 else []) ++
    (O.at (encS fn.name)).map V.n

/-- `upChk` over a sub-spine. -/
noncomputable def upChkW (fn : Fn) (sp : List Ev) (i : ℕ) : Bool :=
  match fn.params[i]? with
  | some p => nzOf [] sp nzDepth p
  | none => allB (fun _ s ↦ retNz (i - fn.params.length) sp s) fn.body (spineE fn.body)

/-- `ownChk` over a sub-spine, the table read first. -/
noncomputable def ownChkW (fn : Fn) (sp : List Ev) (v : V) : Bool :=
  selTabS sp (topSelsC fn.body) v || armNzB v fn.body

/-- **`carryNzG`, witnessed**: the tables of `carriedNz`, `nzUp`, `ownNz`, the sub-spine's bitset `b`. -/
noncomputable def carryNzW (T U O : NTab ℕ) (fn : Fn) (b : ℕ) : Bool :=
  allB (fun _ s ↦ nzStmtW T (kvNzW T O fn) (pickB b (spineE fn.body)) s) fn.body (spineE fn.body) &&
    (U.at (encS fn.name)).all (upChkW fn (pickB b (spineE fn.body))) &&
    (O.at (encS fn.name)).all fun v ↦ ownChkW fn (pickB b (spineE fn.body)) (V.n v)

/-- `pin` over a sub-spine. -/
noncomputable def pinW (fn : Fn) (sp : List Atom) : Kd → V → Bool
  | .inK, v => kOf (cvars fn .inK) sp kDepth v
  | .tab, v => pin fn .tab v

/-- **`siteC` by the table of `carried`**, over a sub-spine. -/
noncomputable def siteCW (T : NTab (ℕ × Kd)) (fn : Fn) (sp : List Atom) (f : String) (args _rets : List V) : Bool :=
  (T.at (encS f)).all fun c ↦ match args[c.1]? with
    | some a => pinW fn sp c.2 a
    | none => false

/-- **`carryG`, witnessed**: the table of `carried`, the sub-spine's bitset `b`. -/
noncomputable def carryGW (T : NTab (ℕ × Kd)) (fn : Fn) (b : ℕ) : Bool :=
  sitesB (siteCW T fn (pickB b (spine fn.body))) fn.body && blockAll (witAtomC fn (pickB b (spine fn.body))) fn.body

end

public section

theorem selTabB_of {body : List Stmt} {sp : List Ev} (hs : ∀ e ∈ sp, e ∈ spineE body) {v : V}
    (h : selTabS sp (topSelsC body) v = true) : selTabB body v = true := by
  unfold selTabS at h
  unfold selTabB
  refine any_imp hs (fun e he ↦ ?_) h
  rcases e with ⟨a⟩ | _ | _ | _ <;> (try cases a) <;> try exact he
  simp only [Bool.and_eq_true] at he ⊢
  refine ⟨he.1, any_imp hs (fun e he ↦ ?_) he.2⟩
  rcases e with ⟨a⟩ | _ | _ | _ <;> (try cases a) <;> try exact he
  simp only [Bool.and_eq_true, Bool.or_eq_true] at he ⊢
  exact ⟨he.1, he.2.imp (selTabAt_mono hs) (selTabAt_mono hs)⟩

theorem kvNzW_sub {T O : NTab ℕ} (hT : tabOk carriedNz T id = true) (hO : tabOk ownNz O id = true) (fn : Fn) :
    ∀ x ∈ kvNzW T O fn, x ∈ kvNz fn := by
  intro x hx
  simp only [kvNzW, kvNz, List.mem_append, List.mem_filterMap, List.mem_map] at hx ⊢
  rcases hx with (⟨i, hi, hx⟩ | hx) | ⟨i, hi, rfl⟩
  · obtain ⟨c, hc, h1, h2⟩ := tabOk.mem hT hi
    exact .inl (.inl ⟨c, hc, by simp only [id] at h2; simp [h1, h2, hx]⟩)
  · exact .inl (.inr hx)
  · obtain ⟨c, hc, h1, h2⟩ := tabOk.mem hO hi
    exact .inr ⟨c, hc, by simp only [id] at h2; simp [h1, h2]⟩

/-- **The nonzero facts' check, from its witnessed check.** -/
theorem carryNzG_of_wit {T U O : NTab ℕ} (hT : tabOk carriedNz T id = true) (hU : tabOk nzUp U id = true)
    (hO : tabOk ownNz O id = true) {fn : Fn} {b : ℕ} (h : carryNzW T U O fn b = true) : carryNzG fn = true := by
  simp only [carryNzW, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have hs : ∀ e ∈ pickB b (spineE fn.body), e ∈ spineE fn.body := fun _ ↦ mem_pickB
  have hk := kvNzW_sub hT hO fn
  have hnz : ∀ ctx, (∀ e ∈ spineE fn.body, e ∈ ctx) → ∀ kv kv', (∀ x ∈ kv, x ∈ kv') → ∀ v,
      nzOf kv (pickB b (spineE fn.body)) nzDepth v = true → nzOf kv' ctx nzDepth v = true :=
    fun ctx hc kv kv' hkv v h ↦ nzOf_mono hkv (fun e he ↦ hc e (hs e he)) h
  have hsite : ∀ ctx, (∀ e ∈ spineE fn.body, e ∈ ctx) → ∀ f args,
      siteNzW T (kvNzW T O fn) (pickB b (spineE fn.body)) f args = true → siteNz (kvNz fn) ctx f args = true := by
    intro ctx hc f args h
    refine tab_all (tabOk.all hT) (φ := id)
      (P := fun i ↦ match args[i]? with | some a => nzOf (kvNz fn) ctx nzDepth a | none => false) (fun i hi ↦ ?_) h
    revert hi
    show (match args[i]? with | some a => nzOf (kvNzW T O fn) (pickB b (spineE fn.body)) nzDepth a | none => false) =
      true → (match args[i]? with | some a => nzOf (kvNz fn) ctx nzDepth a | none => false) = true
    cases args[i]? with
    | none => exact id
    | some a => exact hnz ctx hc _ _ hk a
  simp only [carryNzG, Bool.and_eq_true]
  refine ⟨⟨allB_ctx (ctx0 := spineE fn.body) (fun ctx s hc hq ↦ ?_) fn.body _ (fun _ h ↦ h) h1, ?_⟩, ?_⟩
  · cases s with
    | atom a =>
      cases a with
      | hint hh =>
        cases hh with
        | allocDyn _ s => exact hnz ctx hc _ _ hk s hq
        | _ => rfl
      | _ => rfl
    | call f args _ => exact hsite ctx hc f args hq
    | callIf _ f args => exact hsite ctx hc f args hq
    | dispatch _ fs args _ => exact all_imp (fun f ↦ hsite ctx hc f args) hq
    | _ => rfl
  · refine tab_all (tabOk.all hU) (φ := id) (P := upChk fn) (Q := upChkW fn (pickB b (spineE fn.body)))
      (fun i hi ↦ ?_) h2
    dsimp only [id] at hi
    unfold upChkW at hi
    unfold upChk
    cases hp : fn.params[i]? with
    | some p =>
      rw [hp] at hi
      exact hnz _ (fun _ h ↦ h) [] [] (fun _ h ↦ h) p hi
    | none =>
      rw [hp] at hi
      exact allB_ctx (ctx0 := spineE fn.body)
        (q := fun _ s ↦ retNz (i - fn.params.length) (pickB b (spineE fn.body)) s)
        (p := fun sp s ↦ retNz (i - fn.params.length) sp s)
        (fun ctx s hc hq ↦ retNz_mono (fun e he ↦ hc e (hs e he)) hq) fn.body _ (fun _ h ↦ h) hi
  · refine tab_all (tabOk.all hO) (φ := id) (P := fun v ↦ ownChk fn (V.n v))
      (Q := fun v ↦ ownChkW fn (pickB b (spineE fn.body)) (V.n v)) (fun v hv ↦ ?_) h3
    dsimp only [id] at hv
    unfold ownChkW at hv
    unfold ownChk
    simp only [Bool.or_eq_true] at hv ⊢
    exact hv.elim (fun h ↦ .inr (selTabB_of hs h)) .inl

/-- **The carried facts' check, from its witnessed check.** -/
theorem carryG_of_wit {T : NTab (ℕ × Kd)} (hT : tabOk carried T id = true) {fn : Fn} {b : ℕ}
    (h : carryGW T fn b = true) : carryG fn = true := by
  simp only [carryGW, Bool.and_eq_true] at h
  have hs : ∀ a ∈ pickB b (spine fn.body), a ∈ spine fn.body := fun _ ↦ mem_pickB
  simp only [carryG, Bool.and_eq_true]
  refine ⟨sitesB_imp (fun f args rets hq ↦ ?_) fn.body h.1, blockAll_imp (fun a ↦ witAtomC_mono hs) fn.body h.2⟩
  refine tab_all (tabOk.all hT) (φ := id)
    (P := fun c ↦ match args[c.1]? with | some a => pin fn c.2 a | none => false) (fun c hc ↦ ?_) hq
  revert hc
  obtain ⟨i, k⟩ := c
  show (match args[i]? with | some a => pinW fn (pickB b (spine fn.body)) k a | none => false) = true →
    (match args[i]? with | some a => pin fn k a | none => false) = true
  cases args[i]? with
  | none => exact id
  | some a =>
    cases k with
    | inK => exact kOf_mono hs
    | tab => exact id

end

end LeanVM.Guest.Res
