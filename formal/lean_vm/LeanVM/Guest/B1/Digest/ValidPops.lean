/-
  LeanVM.Guest.B1.Digest.ValidPops

  The entries every valid tree of a function of a simple shape pops: a body of atoms then a return, a `mul_range` helper of atoms (`loopShape`), a body with no witness hint of its own.
-/

module

public import LeanVM.Guest.B1.Digest.Steps
public import LeanVM.Guest.Memory.PopsNil
public import LeanVM.Guest.B1.Common.MutePops

/-!
# Pops of valid trees

* `valid_holds`: a valid node's body holds at its own valuation;
* `atomWit`, `atom_pops`, `flatMap_atom_pops`: an atom's entries are its witness hint's stream and destination's words;
* `atomsRet`, `valid_pops_atomsRet`: a body of atoms then a return pops its atoms' entries;
* `valid_pops_loop`: a valid tree of a `loopShape` helper pops its atoms' entries, then its next iteration's, when entered;
* `splice_flatten`, `valid_pops_noWit`: a body with no witness hint pops its callees' entries in call order.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

variable {P : Core.Program} {rd : Reader}

/-- **A valid node's body holds at its own valuation.** -/
theorem valid_holds {f : String} {σ : Val} {bufs : List ℕ} {ks : List Tree} {args rets : List E}
    (h : (Memory.Tree.node f σ bufs ks).Valid P rd args rets) :
    ∃ fn, P.find? f = some fn ∧ fn.params.map σ = args ∧
      Stmt.HoldsList (P.Rel rd) rd σ fn.body False (fun rs => rs = rets) := by
  obtain ⟨fn, hf, hp, es, vs, hw, hr, hes, hk⟩ := h
  refine ⟨fn, hf, hp, holdsList_of_walk fn.body ?_⟩
  rw [hw]
  refine ⟨fun e he => ⟨hes e he, fun g a r hg => ?_⟩, hr⟩
  subst hg
  exact Tree.KidsValid.rel σ ks (calls es) hk _ (mem_calls_of_call he) rfl

/-! ## Atoms -/

/-- An atom's witness hint, its stream and destination. -/
def atomWit : Atom → List (String × Dest)
  | .hint (.witness s d) => [(s, d)]
  | _ => []

theorem atom_pops (σ : Val) (a : Atom) : a.pops rd σ = (atomWit a).map fun p => (p.1, p.2.words rd σ) := by
  cases a with
  | hint h => cases h <;> rfl
  | _ => rfl

theorem flatMap_atom_pops (σ : Val) (as : List Atom) :
    as.flatMap (Atom.pops rd σ) = (as.flatMap atomWit).map fun p => (p.1, p.2.words rd σ) := by
  rw [List.map_flatMap]
  exact List.flatMap_congr fun a _ => atom_pops σ a

theorem vpPre_nil : ∀ o : Out, o.pre [] = o
  | .fall _ | .ret _ _ | .stuck => rfl

theorem vpPre_pre (es es' : List Ev) : ∀ o : Out, (o.pre es).pre es' = o.pre (es' ++ es)
  | .fall _ | .ret _ _ => by simp [Out.pre]
  | .stuck => rfl

/-- A block of atoms, then `rest`. -/
theorem vp_walk_atoms (σ : Val) (rest : List Stmt) :
    ∀ as : List Atom, walk σ (as.map Stmt.atom ++ rest) = (walk σ rest).pre (as.map Ev.atom)
  | [] => (vpPre_nil _).symm
  | a :: as => by
    rw [List.map_cons, List.cons_append, walk, vp_walk_atoms σ rest as, walk1, Out.seq, vpPre_pre]
    rfl

theorem vp_evPops_atoms (σ : Val) (as : List Atom) : evPops rd σ (as.map Ev.atom) = as.flatMap (Atom.pops rd σ) := by
  rw [evPops, List.flatMap_map]
  rfl

theorem vp_calls_atoms (as : List Atom) : calls (as.map Ev.atom) = [] :=
  List.filterMap_eq_nil_iff.mpr fun e he => by
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp he
    rfl

/-! ## A body of atoms, then a return -/

/-- A body of atoms then a return: its atoms and returned values. -/
def atomsRet : List Stmt → Option (List Atom × List V)
  | [] => none
  | s :: rest => match s, rest with
    | .ret vs, [] => some ([], vs)
    | .atom a, rest => (atomsRet rest).map fun p => (a :: p.1, p.2)
    | _, _ => none

theorem atomsRet_eq : ∀ {body : List Stmt} {as : List Atom} {vs : List V},
    atomsRet body = some (as, vs) → body = as.map Stmt.atom ++ [.ret vs]
  | [], _, _, h => by simp [atomsRet] at h
  | s :: rest, as, vs, h => by
    unfold atomsRet at h
    split at h
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      rfl
    · obtain ⟨⟨as', vs'⟩, h1, h2⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
      rw [atomsRet_eq h1]
      rfl
    · exact absurd h (by simp)

/-- **A valid tree of a function whose body is atoms then a return** pops its atoms' entries. -/
theorem valid_pops_atomsRet {f : String} {fn : Fn} {as : List Atom} {vs : List V} (hf : P.find? f = some fn)
    (hs : atomsRet fn.body = some (as, vs)) {t : Tree} {args rets : List E} (hn : t.name = f)
    (hv : t.Valid P rd args rets) :
    ∃ σ : Val, fn.params.map σ = args ∧ vs.map σ = rets ∧ (∀ a ∈ as, a.Holds rd σ) ∧
      t.pops P rd = as.flatMap (Atom.pops rd σ) := by
  cases t with
  | phantom => exact hv.elim
  | node f' σ bufs ks =>
    obtain rfl : f' = f := hn
    obtain ⟨fn', hf', hp, es, vs', hw, hr, hes, hk⟩ := hv
    rw [hf] at hf'
    cases hf'
    have hw' : walk σ fn.body = .ret (as.map Ev.atom) vs := by
      rw [atomsRet_eq hs, vp_walk_atoms]
      simp [walk, walk1, Out.seq, Out.pre]
    rw [hw'] at hw
    cases hw
    rw [vp_calls_atoms] at hk
    obtain rfl : ks = [] := by cases ks with
      | nil => rfl
      | cons _ _ => exact hk.elim
    refine ⟨σ, hp, hr, fun a ha => hes (.atom a) (List.mem_map_of_mem ha), ?_⟩
    rw [Tree.pops_node hf hw', ← vp_evPops_atoms, ← splice_nil_of_calls _ (vp_calls_atoms as)]
    rfl

/-! ## Loops of atoms -/

/-- **A valid tree of a `mul_range` helper of atoms** (`loopShape`) at the counter `x`: at a valuation of its atoms
with the counter `x`, it pops its atoms' entries, then, while `x·g ≠ N`, a valid tree's at `x·g`. -/
theorem valid_pops_loop {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn) (hok : loopShape fn f = true)
    {t : Tree} {x : E} {ps rets : List E} (hn : t.name = f) (hv : t.Valid coreProgram rd (x :: ps) rets) :
    ∃ σ : Val, σ (V.n 0) = x ∧ fn.params.tail.map σ = ps ∧ (∀ a ∈ loopAtoms fn, a.Holds rd σ) ∧
      ((x * gen + ps.headD 0 = 0 ∧ t.pops coreProgram rd = (loopAtoms fn).flatMap (Atom.pops rd σ)) ∨
        (x * gen + ps.headD 0 ≠ 0 ∧ ∃ t' : Tree, t'.name = f ∧ t'.Valid coreProgram rd (x * gen :: ps) [] ∧
          t.pops coreProgram rd = (loopAtoms fn).flatMap (Atom.pops rd σ) ++ t'.pops coreProgram rd)) := by
  cases t with
  | phantom => exact hv.elim
  | node f' σ bufs ks =>
  obtain rfl : f' = f := hn
  obtain ⟨fn', hf', hp, es, vs, hw, hr, hes, hk⟩ := hv
  rw [hf] at hf'
  cases hf'
  simp only [loopShape, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨h2, hpar⟩, hok⟩ := hok
  unfold loopAtoms
  split at hok
  · rename_i atoms c g args hsl
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨⟨rfl, hlen⟩, htail⟩, hg⟩, hc⟩ := hok
    simp only [hsl, Option.map_some, Option.getD_some]
    have hw' : walk σ fn.body = .ret (atoms.map Ev.atom ++ [.inK c,
        if σ c = 0 then .skip g args else .call g args []]) [] := by
      rw [splitLoop_eq hsl, vp_walk_atoms]
      rfl
    rw [hw'] at hw
    cases hw
    have hat : ∀ a ∈ atoms, a.Holds rd σ := fun a ha =>
      hes (.atom a) (List.mem_append_left _ (List.mem_map_of_mem ha))
    have hx0 : σ (V.n 0) = x := by
      have := congrArg List.head? hp
      rw [hpar] at this
      obtain ⟨k, hk⟩ : ∃ k, fn.params.length = k + 2 := ⟨fn.params.length - 2, by omega⟩
      rw [hk, List.range_succ_eq_map] at this
      simpa using this
    have hps : fn.params.tail.map σ = ps := by
      have := congrArg List.tail hp
      rwa [← List.map_tail] at this
    have hN : ps.headD 0 = σ (V.n 1) := by
      rw [← hps, hpar]
      obtain ⟨k, hk⟩ : ∃ k, fn.params.length = k + 2 := ⟨fn.params.length - 2, by omega⟩
      rw [hk, List.range_succ_eq_map, List.range_succ_eq_map]
      simp
    split at hc
    · rename_i p q hpq
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨hp', rfl⟩ := hc
      have hcv : σ c = x * gen + ps.headD 0 := by
        rw [addOf_sound hpq hat, genMul_sound hp' hat, hx0, hN]
      have hargs : args.map σ = x * gen :: ps := by
        obtain ⟨a0, rest, rfl⟩ : ∃ a0 rest, args = a0 :: rest := by
          cases args with
          | nil => simp at hlen; omega
          | cons a0 rest => exact ⟨a0, rest, rfl⟩
        simp only [List.headD_cons] at hg
        simp only [List.tail_cons] at htail
        rw [List.map_cons, genMul_sound hg hat, hx0, htail, hps]
      have hpops : ∀ ks' : List (List Pop), splice rd σ (atoms.map Ev.atom ++ [.inK c,
          if σ c = 0 then .skip g args else .call g args []]) ks' =
          atoms.flatMap (Atom.pops rd σ) ++ ks'.headD [] := by
        intro ks'
        rw [splice_append_of_calls_nil _ _ (vp_calls_atoms atoms), vp_evPops_atoms]
        split <;> simp [splice]
      rw [Tree.pops_node hf hw', hpops]
      refine ⟨σ, hx0, hps, hat, ?_⟩
      by_cases h0 : σ c = 0
      · rw [ite_eq_left h0, calls_append', vp_calls_atoms] at hk
        change Tree.KidsValid coreProgram rd σ [⟨g, args, [], false⟩] ks at hk
        refine Or.inl ⟨hcv ▸ h0, ?_⟩
        cases ks with
        | nil => exact hk.elim
        | cons k ks =>
          cases ks with
          | cons _ _ => exact hk.2.2.elim
          | nil =>
            obtain ⟨-, ⟨⟨g', σ', rfl⟩, -⟩, -⟩ := hk
            rw [Tree.popsKids, Tree.popsKids, Tree.pops]
            simp
      · rw [ite_eq_right h0, calls_append', vp_calls_atoms] at hk
        change Tree.KidsValid coreProgram rd σ [⟨g, args, [], true⟩] ks at hk
        cases ks with
        | nil => exact hk.elim
        | cons k ks =>
          cases ks with
          | cons _ _ => exact hk.2.2.elim
          | nil =>
            obtain ⟨hkn, hkv, -⟩ := hk
            refine Or.inr ⟨hcv ▸ h0, k, hkn, by rw [← hargs]; simpa using hkv, ?_⟩
            rw [Tree.popsKids, Tree.popsKids]
            rfl
    · exact absurd hc (by simp)
  · exact absurd hok (by simp)

/-! ## A body with no witness hint -/

/-- **Events with no witness hint splice their callees' entries in order.** -/
theorem splice_flatten {σ : Val} : ∀ (es : List Ev) (ks : List (List Pop)), (∀ e ∈ es, e.noWit) →
    (calls es).length = ks.length → splice rd σ es ks = ks.flatten
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp [calls] at h
  | .atom a :: es, ks, he, hl => by
      have ha : a.pops rd σ = [] := by
        have := he _ List.mem_cons_self
        cases a with
        | hint x => cases x <;> simp_all [Ev.noWit, atomNoWit, Atom.pops, Hint.pops]
        | _ => rfl
      rw [splice, ha, splice_flatten es ks (fun e h => he e (List.mem_cons_of_mem _ h)) hl]; rfl
  | .inK _ :: es, ks, he, hl => by
      rw [splice]; exact splice_flatten es ks (fun e h => he e (List.mem_cons_of_mem _ h)) hl
  | .call .. :: es, ks, he, hl | .skip .. :: es, ks, he, hl => by
      cases ks with
      | nil => simp [calls, Ev.call?] at hl
      | cons k ks =>
        rw [splice, List.headD_cons, List.tail_cons, splice_flatten es ks (fun e h => he e (List.mem_cons_of_mem _ h))
          (by simpa [calls, Ev.call?] using hl), List.flatten_cons]

/-- **A valid node whose body has no witness hint** pops its callees' entries in call order. -/
theorem valid_pops_noWit {f : String} {fn : Fn} (hf : P.find? f = some fn) (hb : Stmt.noWitList fn.body = true)
    {σ : Val} {bufs : List ℕ} {ks : List Tree} {args rets : List E}
    (hv : (Memory.Tree.node f σ bufs ks).Valid P rd args rets) :
    (Memory.Tree.node f σ bufs ks).pops P rd = (Tree.popsKids P rd ks).flatten := by
  obtain ⟨fn', hf', -, es, vs, hw, -, -, hk⟩ := hv
  rw [hf] at hf'
  cases hf'
  have hnw := walk_noWit (σ := σ) fn.body hb
  rw [hw] at hnw
  rw [Tree.pops_node hf hw, splice_flatten es _ hnw (by rw [length_popsKids, kidsValid_len hk])]

end
end LeanVM.Guest.B1.Digest
