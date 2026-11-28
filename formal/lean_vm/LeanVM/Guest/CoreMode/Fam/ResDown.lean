/-
  LeanVM.Guest.CoreMode.Fam.ResDown

  The facts carried to callees from their one walk at the generator's hints (`Res.downH`, `Fam/DownDefs.lean`): each
  family's check.
-/

module

public import LeanVM.Guest.CoreMode.Fam.DownDefs
public import LeanVM.Guest.CoreMode.Fam.ResWalk

/-!
# The facts carried to callees, from their walk

The searches of `CarryDefs.lean` (`kOf`, `kIn`, `nzOf`, `tabNz`, `selTabB`, `ptrOk`) and `constExpS` are monotone in the
events they scan and the values they are given (`*_mono`), so a search that succeeds over a sub-spine succeeds over the
spine, and over every statement's context, which extends the body's spine (`allB_ctx`). A site check at the hints gives
its family's (`siteC_of`, `siteNz_of`, `siteExp_of`, `siteG_of`, `siteM_of`, `siteB_of`, through `tab_all`), and the
walk every site's and atom's (`allB_sites`, `allB_block`): `downH_carryG`, `downH_carryNz`, `downH_carryExp`,
`downH_term`, `downH_gl`, `downH_mono`, `downH_any`.
-/

namespace LeanVM.Guest.Res

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Bridge (spine blockAll ptrOk allocOf loadPtr loadPtr0 heapPtr0)
open LeanVM.Guest.Exec (natSeq_eq)

public section

/-! ## The searches, monotone -/

section

variable {kv kv' : List V}

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

/-! ## Each family's site check -/

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

theorem kvNzH_sub {T O : NTab ℕ} (hT : tabOk carriedNz T id = true) (hO : tabOk ownNz O id = true) (fn : Fn) :
    ∀ x ∈ kvNzH T O fn, x ∈ kvNz fn := by
  intro x hx
  simp only [kvNzH, kvNz, List.mem_append, List.mem_filterMap, List.mem_map] at hx ⊢
  rcases hx with (⟨i, hi, hx⟩ | hx) | ⟨i, hi, rfl⟩
  · obtain ⟨c, hc, h1, h2⟩ := tabOk.mem hT hi
    exact .inl (.inl ⟨c, hc, by simp only [id] at h2; simp [h1, h2, hx]⟩)
  · exact .inl (.inr hx)
  · obtain ⟨c, hc, h1, h2⟩ := tabOk.mem hO hi
    exact .inr ⟨c, hc, by simp only [id] at h2; simp [h1, h2]⟩

section

variable {fn : Fn} {f : String} {args : List V}

theorem siteC_of {T : NTab (ℕ × Kd)} (hT : tabIn carried T id = true) {sp : List Atom}
    (hs : ∀ a ∈ sp, a ∈ spine fn.body) {rets : List V} (h : siteCH T fn sp (encS f) args = true) :
    siteC fn f args rets = true := by
  refine tab_all hT (φ := id) (P := fun c ↦ match args[c.1]? with | some a => pin fn c.2 a | none => false)
    (fun c hc ↦ ?_) h
  revert hc
  obtain ⟨i, k⟩ := c
  show (match args[i]? with | some a => pinH fn sp k a | none => false) = true →
    (match args[i]? with | some a => pin fn k a | none => false) = true
  cases args[i]? with
  | none => exact id
  | some a =>
    cases k with
    | inK => exact kOf_mono hs
    | tab => exact id

theorem siteNz_of {T : NTab ℕ} (hT : tabIn carriedNz T id = true) {kv kv' : List V} {sp sp' : List Ev}
    (hk : ∀ x ∈ kv, x ∈ kv') (hs : ∀ e ∈ sp, e ∈ sp') (h : siteNzH T kv sp (encS f) args = true) :
    siteNz kv' sp' f args = true := by
  refine tab_all hT (φ := id) (P := fun i ↦ match args[i]? with | some a => nzOf kv' sp' nzDepth a | none => false)
    (fun i hi ↦ ?_) h
  revert hi
  show (match args[i]? with | some a => nzOf kv sp nzDepth a | none => false) = true →
    (match args[i]? with | some a => nzOf kv' sp' nzDepth a | none => false) = true
  cases args[i]? with
  | none => exact id
  | some a => exact nzOf_mono hk hs

theorem siteExp_of {L : List (String × ℕ × ℕ × ℕ)} {T : NTab (ℕ × ℕ × ℕ)} (hT : tabIn L T id = true) {sp : List Ev}
    (hs : ∀ e ∈ sp, e ∈ spineE fn.body) (h : siteExpH T fn sp (encS f) args = true) :
    (L.all fun c ↦ c.1 != f || match args[c.2.1]? with
      | some a => CoreMode.valExpB fn.body a c.2.2.1 c.2.2.2
      | none => false) = true := by
  refine tab_all hT (φ := id)
    (P := fun c ↦ match args[c.1]? with | some a => CoreMode.valExpB fn.body a c.2.1 c.2.2 | none => false)
    (fun c hc ↦ ?_) h
  revert hc
  obtain ⟨i, lo, hi⟩ := c
  show (match args[i]? with
      | some a => CoreMode.constExpS a lo hi sp || CoreMode.armExpB a lo hi fn.body
      | none => false) = true →
    (match args[i]? with | some a => CoreMode.valExpB fn.body a lo hi | none => false) = true
  cases args[i]? with
  | none => exact id
  | some a =>
    intro h
    unfold CoreMode.valExpB
    unfold CoreMode.constExpS at h ⊢
    simp only [Bool.or_eq_true] at h ⊢
    exact h.imp (any_sub hs) id

theorem siteG_of {R : List (String × String)} {T : NTab ℕ} (hT : tabIn R T encS = true)
    (h : siteGH T fn (encS fn.name) f (encS f) = true) :
    (R.all fun p ↦ p.1 != f || fn.name == p.2 || (fn.name == f && fn.loop)) = true := by
  have := tab_all hT (φ := encS) (P := fun c ↦ fn.name == c || (fn.name == f && fn.loop)) (fun c hc ↦ ?_) h
  · simpa only [Bool.or_assoc] using this
  simp only [Bool.or_eq_true] at hc ⊢
  refine hc.imp (fun h ↦ ?_) id
  rw [encS_inj (Nat.eq_of_beq_eq_true h)]
  exact beq_self_eq_true _

theorem siteM_of {R : List (String × List String)} {T : NTab (List ℕ)}
    (hT : tabIn R T (fun cs : List String ↦ cs.map encS) = true) (h : siteMH T fn (encS fn.name) f (encS f) = true) :
    (R.all fun p ↦ p.1 != f || p.2.contains fn.name || (fn.name == f && fn.loop)) = true := by
  have := tab_all hT (φ := fun cs : List String ↦ cs.map encS)
    (P := fun cs : List String ↦ cs.contains fn.name || (fn.name == f && fn.loop)) (fun cs hc ↦ ?_) h
  · simpa only [Bool.or_assoc] using this
  simp only [Bool.or_eq_true] at hc ⊢
  refine hc.imp (fun h ↦ ?_) id
  obtain ⟨s, hs, he⟩ := List.mem_map.mp (List.contains_iff_mem.mp h)
  rw [List.contains_iff_mem, ← encS_inj he]
  exact hs

theorem siteB_of {L : Link} {T : NTab Unit} (hT : tabIn L.fams T (fun _ ↦ ()) = true)
    (h : siteBH T (encS L.oName) fn (encS fn.name) f (encS f) = true) :
    (!(L.fams.any (·.1 == f)) || fn.name == L.oName || (fn.name == f && fn.loop)) = true := by
  simp only [siteBH, Bool.or_eq_true] at h ⊢
  rcases h with (he | hk) | hl
  · refine .inl (.inl ?_)
    rw [Bool.not_eq_true', Bool.eq_false_iff]
    intro ha
    obtain ⟨c, hc, hcf⟩ := List.any_eq_true.mp ha
    have hm := List.all_eq_true.mp hT c hc
    rw [beq_iff_eq.mp hcf, List.contains_iff_mem] at hm
    rw [List.isEmpty_iff] at he
    rw [he] at hm
    exact List.not_mem_nil hm
  · exact .inl (.inr (by rw [encS_inj (Nat.eq_of_beq_eq_true hk)]; exact beq_self_eq_true _))
  · exact .inr hl

end

/-! ## Each family from the walk -/

section

variable {D : DownT} {fn : Fn} {w : DownHints}

/-- The walk's parts. -/
private theorem downH_parts (h : downH D fn w = true) :
    allB (fun _ s ↦ stmtD D fn (pickB w.g (spine fn.body)) (kvNzH D.cnz D.own fn) (pickB w.nz (spineE fn.body))
      (pickB w.exp (spineE fn.body)) (encS fn.name) s) fn.body (spineE fn.body) = true ∧
    (D.up.at (encS fn.name)).all (upChkH fn (pickB w.nz (spineE fn.body))) = true ∧
    ((D.own.at (encS fn.name)).all fun v ↦ ownChkH fn (pickB w.nz (spineE fn.body)) (V.n v)) = true := by
  unfold downH at h
  rw [natSeq_eq] at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

private theorem siteD_parts {spA : List Atom} {kv : List V} {spN spX : List Ev} {k : ℕ} {f : String}
    {args : List V} {c : ℕ} (h : siteD D fn spA kv spN spX k f args c = true) :
    siteCH D.carried fn spA c args = true ∧ siteNzH D.cnz kv spN c args = true ∧
      siteExpH D.exp fn spX c args = true ∧ siteGH D.term fn k f c = true ∧ siteMH D.gl fn k f c = true ∧
      siteGH D.mono fn k f c = true ∧ siteBH D.any D.anyO fn k f c = true := by
  unfold siteD at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

/-- A family's check of every call site, from the walk. -/
private theorem sites_of {p : String → List V → List V → Bool}
    (hp : ∀ f args rets, siteD D fn (pickB w.g (spine fn.body)) (kvNzH D.cnz D.own fn) (pickB w.nz (spineE fn.body))
      (pickB w.exp (spineE fn.body)) (encS fn.name) f args (encS f) = true → p f args rets = true)
    (h : downH D fn w = true) : sitesB p fn.body = true := by
  refine allB_sites (fun s hs ↦ ?_) fn.body _ (downH_parts h).1
  cases s with
  | call f args rets => exact hp f args rets (by rw [stmtD, natSeq_eq] at hs; exact hs)
  | callIf _ f args => exact hp f args [] (by rw [stmtD, natSeq_eq] at hs; exact hs)
  | dispatch _ fs args rets =>
    rw [stmtD] at hs
    exact all_imp (fun f hf ↦ hp f args rets (by rw [natSeq_eq] at hf; exact hf)) hs
  | _ => rfl

theorem downH_carryG (hT : tabIn carried D.carried id = true) (h : downH D fn w = true) : carryG fn = true := by
  have hs : ∀ a ∈ pickB w.g (spine fn.body), a ∈ spine fn.body := fun _ ↦ mem_pickB
  simp only [carryG, Bool.and_eq_true]
  refine ⟨sites_of (fun f args rets hd ↦ siteC_of hT hs (siteD_parts hd).1) h,
    blockAll_imp (fun a ↦ witAtomC_mono hs) fn.body (allB_block (fun a ha ↦ ?_) fn.body _ (downH_parts h).1)⟩
  rw [stmtD, Bool.and_eq_true] at ha
  exact ha.1

theorem downH_carryNz (hT : tabOk carriedNz D.cnz id = true) (hU : tabIn nzUp D.up id = true)
    (hO : tabOk ownNz D.own id = true) (h : downH D fn w = true) : carryNzG fn = true := by
  obtain ⟨hw, h2, h3⟩ := downH_parts h
  have hs : ∀ e ∈ pickB w.nz (spineE fn.body), e ∈ spineE fn.body := fun _ ↦ mem_pickB
  have hk := kvNzH_sub hT hO fn
  simp only [carryNzG, Bool.and_eq_true]
  refine ⟨⟨allB_ctx (ctx0 := spineE fn.body) (fun ctx s hc hq ↦ ?_) fn.body _ (fun _ h ↦ h) hw, ?_⟩, ?_⟩
  · have hc' : ∀ e ∈ pickB w.nz (spineE fn.body), e ∈ ctx := fun e he ↦ hc e (hs e he)
    have hsite : ∀ f args, siteD D fn (pickB w.g (spine fn.body)) (kvNzH D.cnz D.own fn) (pickB w.nz (spineE fn.body))
        (pickB w.exp (spineE fn.body)) (encS fn.name) f args (encS f) = true → siteNz (kvNz fn) ctx f args = true :=
      fun _ _ hd ↦ siteNz_of (tabOk.all hT) hk hc' (siteD_parts hd).2.1
    cases s with
    | atom a =>
      rw [stmtD, Bool.and_eq_true] at hq
      cases a with
      | hint hh =>
        cases hh with
        | allocDyn _ s => exact nzOf_mono hk hc' hq.2
        | _ => rfl
      | _ => rfl
    | call f args _ => rw [stmtD, natSeq_eq] at hq; exact hsite f args hq
    | callIf _ f args => rw [stmtD, natSeq_eq] at hq; exact hsite f args hq
    | dispatch _ fs args _ =>
      rw [stmtD] at hq
      exact all_imp (fun f hf ↦ hsite f args (by rw [natSeq_eq] at hf; exact hf)) hq
    | _ => rfl
  · refine tab_all hU (φ := id) (P := upChk fn) (Q := upChkH fn (pickB w.nz (spineE fn.body))) (fun i hi ↦ ?_) h2
    dsimp only [id] at hi
    unfold upChkH at hi
    unfold upChk
    cases hp : fn.params[i]? with
    | some p =>
      rw [hp] at hi
      exact nzOf_mono (kv := []) (fun _ h ↦ h) hs hi
    | none =>
      rw [hp] at hi
      exact allB_ctx (ctx0 := spineE fn.body)
        (q := fun _ s ↦ retNz (i - fn.params.length) (pickB w.nz (spineE fn.body)) s)
        (p := fun sp s ↦ retNz (i - fn.params.length) sp s)
        (fun ctx s hc hq ↦ retNz_mono (fun e he ↦ hc e (hs e he)) hq) fn.body _ (fun _ h ↦ h) hi
  · refine tab_all (tabOk.all hO) (φ := id) (P := fun v ↦ ownChk fn (V.n v))
      (Q := fun v ↦ ownChkH fn (pickB w.nz (spineE fn.body)) (V.n v)) (fun v hv ↦ ?_) h3
    dsimp only [id] at hv
    unfold ownChkH at hv
    unfold ownChk
    simp only [Bool.or_eq_true] at hv ⊢
    exact hv.elim (fun h ↦ .inr (selTabB_of hs h)) .inl

theorem downH_carryExp {L : List (String × ℕ × ℕ × ℕ)} (hT : tabIn L D.exp id = true) (h : downH D fn w = true) :
    CoreMode.carryExpB L fn = true := by
  unfold CoreMode.carryExpB
  exact sites_of (fun _ _ _ hd ↦ siteExp_of hT (fun _ ↦ mem_pickB) (siteD_parts hd).2.2.1) h

theorem downH_term {R : List (String × String)} (hT : tabIn R D.term encS = true) (h : downH D fn w = true) :
    callersG R fn = true := by
  unfold callersG
  exact sites_of (fun _ _ _ hd ↦ siteG_of hT (siteD_parts hd).2.2.2.1) h

theorem downH_gl {R : List (String × List String)} (hT : tabIn R D.gl (fun cs : List String ↦ cs.map encS) = true)
    (h : downH D fn w = true) : callersM R fn = true := by
  unfold callersM
  exact sites_of (fun _ _ _ hd ↦ siteM_of hT (siteD_parts hd).2.2.2.2.1) h

theorem downH_mono {R : List (String × String)} (hT : tabIn R D.mono encS = true) (h : downH D fn w = true) :
    callersG R fn = true := by
  unfold callersG
  exact sites_of (fun _ _ _ hd ↦ siteG_of hT (siteD_parts hd).2.2.2.2.2.1) h

theorem downH_any {L : Link} (hT : tabIn L.fams D.any (fun _ ↦ ()) = true) (ho : D.anyO = encS L.oName)
    (h : downH D fn w = true) : callersB L fn = true := by
  unfold callersB
  exact sites_of (fun _ _ _ hd ↦ siteB_of hT (ho ▸ (siteD_parts hd).2.2.2.2.2.2)) h

end

end

end LeanVM.Guest.Res
