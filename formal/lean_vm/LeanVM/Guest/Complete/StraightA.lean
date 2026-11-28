module

public import LeanVM.Guest.Complete.ComposeL
public import LeanVM.Guest.Complete.Straight

/-!
# Straight nodes placing nothing, placed

A function whose body is a straight block (atoms, calls, guarded calls) then a `ret`, its atoms
no `HeapBuf`, no hint to the heap and no `frameAddr` (`plainS`, by the kernel), takes no words of its own and places nothing
of its own: its `HeapBuf`s, `frameAddr`s and heap hints are none (`plain_parts`). So its placed
node (`callAtA_node`, `callAtA_nodeL`) asks only a valuation on which its atoms hold and its guards
are in `K`, its loads in the region it is handed, and its callees placed (`KidsAtF`, `KidsAtL`):
`callAtA_straight`, `callAtA_straightL`. `kidsAtF_monoR`, `kidsAtL_monoR` widen the callees'
region.
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

/-- A straight statement placing nothing: no `HeapBuf`, no hint to the heap, no `frameAddr`. -/
def plainS : Stmt → Bool
  | .atom (.hint (.alloc ..)) => false
  | .atom (.hint (.allocDyn ..)) => false
  | .atom (.hint h) => ((hintDest? h).bind destHeap?).isNone
  | .atom (.frameAddr ..) => false
  | _ => true

theorem plain_parts {σ : Val} {pre : List Stmt} (hs : pre.all Stmt.straight = true)
    (hp : pre.all plainS = true) :
    allocDsts (pre.flatMap (slEvs σ)) = [] ∧ allocs σ (pre.flatMap (slEvs σ)) = [] ∧
      addrs (pre.flatMap (slEvs σ)) = [] ∧ heapHintAddrs σ (pre.flatMap (slEvs σ)) = [] := by
  obtain ⟨h1, h2, h3, -⟩ := straight_parts σ pre hs
  have hpl : ∀ s ∈ pre, plainS s = true := fun s hs' => List.all_eq_true.mp hp s hs'
  have ha : pre.filterMap Stmt.allocSz = [] := List.filterMap_eq_nil_iff.mpr fun s hs' => by
    have := hpl s hs'
    cases s with
    | atom a =>
      cases a with
      | hint h => cases h <;> simp_all [plainS, Stmt.allocSz]
      | _ => simp_all [plainS, Stmt.allocSz]
    | _ => simp [Stmt.allocSz]
  have hd : pre.filterMap Stmt.addrS = [] := List.filterMap_eq_nil_iff.mpr fun s hs' => by
    have := hpl s hs'
    cases s with
    | atom a =>
      cases a with
      | hint h => cases h <;> simp_all [plainS, Stmt.addrS]
      | _ => simp_all [plainS, Stmt.addrS]
    | _ => simp [Stmt.addrS]
  refine ⟨by rw [h1, ha]; rfl, by rw [h2, ha]; rfl, by rw [h3, hd], ?_⟩
  refine List.eq_nil_iff_forall_not_mem.mpr fun A hA => ?_
  obtain ⟨e, he, hA⟩ := List.mem_flatMap.mp hA
  obtain ⟨s, hs', he⟩ := List.mem_flatMap.mp he
  have := hpl s hs'
  cases s with
  | atom a =>
    simp only [slEvs, List.mem_singleton] at he
    subst he
    cases a with
    | hint h =>
      cases h <;> simp_all [plainS, Ev.hintAddrs, hintDest?, Option.isNone_iff_eq_none]
    | _ => simp_all [plainS, Ev.hintAddrs]
  | call f args rets =>
    simp only [slEvs, List.mem_singleton] at he
    subst he
    simp [Ev.hintAddrs] at hA
  | callIf c f args =>
    simp only [slEvs, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · simp [Ev.hintAddrs] at hA
    · split at hA <;> simp [Ev.hintAddrs] at hA
  | _ => simp [slEvs] at he

variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}

theorem kidsAtF_monoR {k : ℕ} {σ : Val} {R R' : ℕ → Prop} {Pre : Reader → Prop} (hR : ∀ i, R i → R' i) :
    ∀ (cs : List Call) (O : Reader → Prop) (Dacc : ℕ → Prop) (Qs : List (Reader → Tree → Prop))
      (cur e : ℕ) (Oend : Reader → Prop) (Dend : ℕ → Prop),
    KidsAtF fs al cert k σ R Pre O Dacc Qs cs cur e Oend Dend →
      KidsAtF fs al cert k σ R' Pre O Dacc Qs cs cur e Oend Dend
  | [], _, _, _, _, _, _, _, h => by rw [KidsAtF] at h ⊢; exact h
  | c :: cs, O, Dacc, Qs, cur, e, Oend, Dend, h => by
    rw [KidsAtF] at h ⊢
    split at h
    · rename_i ht
      simp only [ht, ↓reduceIte]
      obtain ⟨Bc, ec, Rc, Dc, Oc, hRc, hc, hr⟩ := h
      exact ⟨Bc, ec, Rc, Dc, Oc, fun i hi => (hRc i hi).imp_left (hR i), hc,
        kidsAtF_monoR hR cs _ _ _ _ _ _ _ hr⟩
    · rename_i ht
      simp only [ht, Bool.false_eq_true, ↓reduceIte]
      exact ⟨h.1, kidsAtF_monoR hR cs _ _ _ _ _ _ _ h.2⟩

theorem kidsAtL_monoR {k : ℕ} {σ : Val} {R R' : ℕ → Prop} {Pre : Reader → Prop} {tl : ℕ}
    (hR : ∀ i, R i → R' i) :
    ∀ (cs : List Call) (O : Reader → Prop) (Dacc : ℕ → Prop) (Qs : List (Reader → Tree → Prop))
      (cur e Bt : ℕ) (Oend : Reader → Prop) (Dend : ℕ → Prop),
    KidsAtL fs al cert k σ R Pre tl O Dacc Qs cs cur e Bt Oend Dend →
      KidsAtL fs al cert k σ R' Pre tl O Dacc Qs cs cur e Bt Oend Dend
  | [], _, _, _, _, _, _, _, _, h => by rw [KidsAtL] at h ⊢; exact h
  | [c], O, Dacc, Qs, cur, e, Bt, Oend, Dend, h => by
    rw [KidsAtL] at h ⊢
    split at h
    · rename_i ht
      simp only [ht, ↓reduceIte]
      obtain ⟨Rc, Dc, Oc, hRc, hc, hr⟩ := h
      exact ⟨Rc, Dc, Oc, fun i hi => (hRc i hi).imp_left (hR i), hc, hr⟩
    · rename_i ht
      simp only [ht, Bool.false_eq_true, ↓reduceIte]
      exact h
  | c :: c' :: cs, O, Dacc, Qs, cur, e, Bt, Oend, Dend, h => by
    rw [KidsAtL] at h ⊢
    split at h
    · rename_i ht
      simp only [ht, ↓reduceIte]
      obtain ⟨Bc, ec, Rc, Dc, Oc, hRc, hc, hr⟩ := h
      exact ⟨Bc, ec, Rc, Dc, Oc, fun i hi => (hRc i hi).imp_left (hR i), hc,
        kidsAtL_monoR hR (c' :: cs) _ _ _ _ _ _ _ _ hr⟩
    · rename_i ht
      simp only [ht, Bool.false_eq_true, ↓reduceIte]
      exact ⟨h.1, kidsAtL_monoR hR (c' :: cs) _ _ _ _ _ _ _ _ h.2⟩

/-- **A straight node placing nothing completes placed**, not a loop helper: from a valuation on
which its atoms hold and guards are in `K`, its loads in `R`, its callees placed from its cursor. -/
theorem callAtA_straight {k : ℕ} {f : String} {args rets : List E} {R : ℕ → Prop} {Out Pre : Reader → Prop}
    {Post : Reader → Tree → Prop} {fp c e : ℕ} {fn : Fn} {pre : List Stmt} {vs : List V}
    (hf : coreProgram.find? f = some fn) (hb : fn.body = pre ++ [.ret vs]) (hs : pre.all Stmt.straight = true)
    (hp : pre.all plainS = true) (hlp : coreProgram.loop f = false) (hfc : fp + fs f ≤ c) (σ : Val)
    (hpar : fn.params.map σ = args) (hret : vs.map σ = rets)
    (hlo : ∀ q ∈ pre.filterMap stmtLoad?, ∃ i, (σ q.1).limb 0 * addressOfIndex q.2 = addressOfIndex i ∧ R i)
    (Qs : List (Reader → Tree → Prop)) (Oend : Reader → Prop) (Dend : ℕ → Prop)
    (hk : KidsAtF fs al cert k σ R Pre (fun rd => HoldsWords rd []) (fun _ => False) Qs
      ((pre.filterMap Stmt.callS).map (mkCall σ)) c e Oend Dend)
    (hout : ∀ rd, Oend rd → Out rd)
    (hok : ∀ rd, LowDef k rd → Pre rd → Oend rd → ∀ s ∈ pre, SOk rd σ s)
    (hpost : ∀ rd ts, LowDef k rd → Pre rd → Oend rd →
      Tree.KidsValid coreProgram rd σ ((pre.filterMap Stmt.callS).map (mkCall σ)) ts →
      KidsPost rd Qs ((pre.filterMap Stmt.callS).map (mkCall σ)) ts → Post rd (.node f σ [] ts)) :
    CallAtA fs al cert k f args rets R (fun _ => False) Out Pre Post (fs f) fp c e := by
  have hw : walk σ fn.body = .ret (pre.flatMap (slEvs σ)) vs := by rw [hb]; exact walk_straight σ vs pre hs
  obtain ⟨hd, ha, hr, hh⟩ := plain_parts (σ := σ) hs hp
  have hc := (straight_parts σ pre hs).2.2.2
  refine callAtA_node hlp hfc ⟨σ, fn, _, vs, [], Qs, Oend, Dend, hf, hpar, hw, hret, ?_, ?_, ?_, ?_,
    fun _ hi => hi.elim, ?_, hout, fun rd hl hp' ho => events_straight (hok rd hl hp' ho), ?_⟩
  · rw [ha]; exact ⟨by rw [hd]; rfl, by rw [hr]; simp⟩
  · exact ⟨by simp, List.Pairwise.nil⟩
  · intro A hA
    rw [loadAddrs_straight σ pre hs] at hA
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hA
    obtain ⟨i, hi, hR⟩ := hlo q hq
    exact ⟨i, hi, Or.inr (Or.inl hR)⟩
  · rw [hh]; simp
  · rw [ha, hc, List.sum_nil, Nat.add_zero]; exact kidsAtF_monoR (fun i h => Or.inl h) _ _ _ _ _ _ _ _ hk
  · intro rd ts hl hp' ho hv hq
    rw [hc] at hv hq
    rw [ha]
    exact hpost rd ts hl hp' ho hv hq

/-- **A straight loop helper placing nothing completes placed**: `callAtA_straight` with its tail
call at the next frame (`KidsAtL`), of block `Bt`. -/
theorem callAtA_straightL {k : ℕ} {f : String} {args rets : List E} {R : ℕ → Prop} {Out Pre : Reader → Prop}
    {Post : Reader → Tree → Prop} {fp c e Bt : ℕ} {fn : Fn} {pre : List Stmt} {vs : List V}
    (hf : coreProgram.find? f = some fn) (hb : fn.body = pre ++ [.ret vs]) (hs : pre.all Stmt.straight = true)
    (hp : pre.all plainS = true) (hlp : coreProgram.loop f = true) (hfc : fp + (fs f + Bt) ≤ c) (σ : Val)
    (hpar : fn.params.map σ = args) (hret : vs.map σ = rets)
    (hlo : ∀ q ∈ pre.filterMap stmtLoad?, ∃ i, (σ q.1).limb 0 * addressOfIndex q.2 = addressOfIndex i ∧ R i)
    (Qs : List (Reader → Tree → Prop)) (Oend : Reader → Prop) (Dend : ℕ → Prop)
    (hk : KidsAtL fs al cert k σ R Pre (fp + fs f) (fun rd => HoldsWords rd []) (fun _ => False) Qs
      ((pre.filterMap Stmt.callS).map (mkCall σ)) c e Bt Oend Dend)
    (hout : ∀ rd, Oend rd → Out rd)
    (hok : ∀ rd, LowDef k rd → Pre rd → Oend rd → ∀ s ∈ pre, SOk rd σ s)
    (hpost : ∀ rd ts, LowDef k rd → Pre rd → Oend rd →
      Tree.KidsValid coreProgram rd σ ((pre.filterMap Stmt.callS).map (mkCall σ)) ts →
      KidsPost rd Qs ((pre.filterMap Stmt.callS).map (mkCall σ)) ts → Post rd (.node f σ [] ts)) :
    CallAtA fs al cert k f args rets R (fun _ => False) Out Pre Post (fs f + Bt) fp c e := by
  have hw : walk σ fn.body = .ret (pre.flatMap (slEvs σ)) vs := by rw [hb]; exact walk_straight σ vs pre hs
  obtain ⟨hd, ha, hr, hh⟩ := plain_parts (σ := σ) hs hp
  have hc := (straight_parts σ pre hs).2.2.2
  refine callAtA_nodeL hlp hfc ⟨σ, fn, _, vs, [], Qs, Oend, Dend, hf, hpar, hw, hret, ?_, ?_, ?_, ?_,
    fun _ hi => hi.elim, ?_, hout, fun rd hl hp' ho => events_straight (hok rd hl hp' ho), ?_⟩
  · rw [ha]; exact ⟨by rw [hd]; rfl, by rw [hr]; simp⟩
  · exact ⟨by simp, List.Pairwise.nil⟩
  · intro A hA
    rw [loadAddrs_straight σ pre hs] at hA
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hA
    obtain ⟨i, hi, hR⟩ := hlo q hq
    exact ⟨i, hi, Or.inr (Or.inl hR)⟩
  · rw [hh]; simp
  · rw [ha, hc, List.sum_nil, Nat.add_zero]; exact kidsAtL_monoR (fun i h => Or.inl h) _ _ _ _ _ _ _ _ _ hk
  · intro rd ts hl hp' ho hv hq
    rw [hc] at hv hq
    rw [ha]
    exact hpost rd ts hl hp' ho hv hq

end
end LeanVM.Guest.Complete
