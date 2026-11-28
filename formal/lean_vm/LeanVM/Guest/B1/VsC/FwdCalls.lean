/-
  LeanVM.Guest.B1.VsC.FwdCalls

  A body of atoms and calls that loads input arrays and stores output arrays completes from its
  atoms' meaning, its callees complete.
-/

module

public import LeanVM.Guest.B1.VsC.FwdStore
public import LeanVM.Guest.B1.VsC.Quiet
public import LeanVM.Guest.B1.VsC.Mono
public import LeanVM.Guest.Memory.Straight

/-!
# Bodies of atoms and calls, with stores

`callCompletes_storesCalls`: `callCompletes_stores` for a body whose statements before its `ret` are
atoms and calls, each call on parameters, its returns fresh values (`storeCallChecks`, decided by
the kernel). The calls' returns are an oracle `w` fixed before the memory, so the callees' words
are fixed too (`callCompletes_nodeRd` on `σ0 args w`). The atoms' meaning (`hmean`) is stated on
any valuation holding the atoms with the calls returning `w`: the call relation plays no part
(`holdsList_trivC` gives the body's `HoldsList` under the relation that always holds).
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd

@[expose] public section

/-- A statement of a body of atoms and calls. -/
def atomOrCall : Stmt → Bool
  | .atom _ => true
  | .call .. => true
  | _ => false

/-- The returns of a body of atoms and calls then a `ret`. -/
def retOfC : List Stmt → Option (List V)
  | [.ret vs] => some vs
  | .atom _ :: ss => retOfC ss
  | .call .. :: ss => retOfC ss
  | _ => none

theorem retOfC_spec : ∀ {B : List Stmt} {vs : List V}, retOfC B = some vs →
    ∃ ss, B = ss ++ [.ret vs] ∧ ss.all atomOrCall = true
  | [], _, h => by simp [retOfC] at h
  | [.ret ws], vs, h => by
    simp only [retOfC, Option.some.injEq] at h
    subst h
    exact ⟨[], rfl, rfl⟩
  | .atom a :: ss, vs, h => by
    obtain ⟨ss', rfl, hs⟩ := retOfC_spec (B := ss) h
    exact ⟨.atom a :: ss', rfl, by simp [atomOrCall, hs]⟩
  | .call f a r :: ss, vs, h => by
    obtain ⟨ss', rfl, hs⟩ := retOfC_spec (B := ss) h
    exact ⟨.call f a r :: ss', rfl, by simp [atomOrCall, hs]⟩
  | .ret _ :: _ :: _, _, h => by simp [retOfC] at h
  | .ite .. :: _, _, h | .match_ .. :: _, _, h | .callIf .. :: _, _, h
  | .dispatch .. :: _, _, h => by simp [retOfC] at h

/-- A value `.n i`, `i < n`: a parameter. -/
def isParamB (n : ℕ) (v : V) : Bool := decide (v = .n v.idx) && decide (v.idx < n)

/-- A value `.n i`, `n ≤ i`: no parameter. -/
def isFreshB (n : ℕ) (v : V) : Bool := decide (v = .n v.idx) && decide (n ≤ v.idx)

/-- A call on parameters, returning fresh values. -/
def callOkB (n : ℕ) : Stmt → Bool
  | .call _ args rets => args.all (isParamB n) && rets.all (isFreshB n)
  | _ => true

/-- The frame of a call statement. -/
def callOf? : Stmt → Option Call
  | .call f args rets => some ⟨f, args, rets, true⟩
  | _ => none

/-- The frames of a body of atoms and calls. -/
def callsOfB (B : List Stmt) : List Call := B.filterMap callOf?

/-- What the kernel checks of a body of atoms and calls with stores, on `n` parameters. -/
def storeCallChecks (n : ℕ) (ins outs : List (ℕ × ℕ)) (B : List Stmt) : Bool :=
  (chk n B).isSome && (retOfC B).isSome && (atomsOf B).all (stOk ins outs (storesOf n B)) &&
    ((storesOf n B).map storeKey).Nodup && (storesOf n B).all isLoadB && B.all (callOkB n)

/-- The valuation fixed before the memory: the parameters, then the oracle. -/
def σ0 (args : List E) (w : ℕ → E) : Val := fun v => if v.idx < args.length then args.getD v.idx 0 else w v.idx

theorem slEvs_atomOrCall (σ σ' : Val) : ∀ s : Stmt, atomOrCall s = true → slEvs σ s = slEvs σ' s
  | .atom _, _ => rfl
  | .call .., _ => rfl
  | .ite .., h | .match_ .., h | .callIf .., h | .dispatch .., h | .ret _, h => by simp [atomOrCall] at h

theorem straight_of_atomOrCall : ∀ ss : List Stmt, ss.all atomOrCall = true → ss.all Stmt.straight = true
  | [], _ => rfl
  | s :: ss, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h ⊢
    refine ⟨?_, straight_of_atomOrCall ss h.2⟩
    cases s <;> simp_all [atomOrCall, Stmt.straight]

theorem calls_atomOrCall (σ : Val) : ∀ ss : List Stmt, ss.all atomOrCall = true →
    calls (ss.flatMap (slEvs σ)) = callsOfB ss
  | [], _ => rfl
  | s :: ss, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    have ih := calls_atomOrCall σ ss h.2
    simp only [calls, callsOfB, List.flatMap_cons, List.filterMap_append, List.filterMap_cons] at ih ⊢
    rw [ih]
    cases s with
    | atom a => simp [slEvs, Ev.call?, callOf?]
    | call f args rets => simp [slEvs, Ev.call?, callOf?]
    | _ => simp [atomOrCall] at h

theorem mem_callsOfB {ss : List Stmt} {c : Call} (h : c ∈ callsOfB ss) : Stmt.call c.f c.args c.rets ∈ ss := by
  obtain ⟨s, hs, he⟩ := List.mem_filterMap.mp h
  cases s with
  | call f args rets => simp only [callOf?, Option.some.injEq] at he; subst he; exact hs
  | _ => simp [callOf?] at he

theorem atoms_slEvs {a : Atom} : ∀ {ss : List Stmt} {σ : Val}, Ev.atom a ∈ ss.flatMap (slEvs σ) →
    Stmt.atom a ∈ ss
  | [], _, h => by simp at h
  | s :: ss, σ, h => by
    rw [List.flatMap_cons, List.mem_append] at h
    rcases h with h | h
    · cases s with
      | atom b => simp only [slEvs, List.mem_singleton, Ev.atom.injEq] at h; subst h; exact List.mem_cons_self
      | call => simp [slEvs] at h
      | callIf c f args => simp only [slEvs, List.mem_cons, List.not_mem_nil] at h; split at h <;> simp at h
      | _ => simp [slEvs] at h
    · exact List.mem_cons_of_mem _ (atoms_slEvs h)

/-- **A body of atoms and calls holds under the relation that always holds**, from its atoms. -/
theorem holdsList_trivC {rd : Reader} {σ : Val} : ∀ {B : List Stmt} {vs : List V}, retOfC B = some vs →
    (∀ a, Stmt.atom a ∈ B → a.Holds rd σ) →
      Stmt.HoldsList (fun _ _ _ => True) rd σ B False (fun l => l = vs.map σ)
  | [], _, h, _ => by simp [retOfC] at h
  | [.ret ws], vs, h, _ => by
    simp only [retOfC, Option.some.injEq] at h
    subst h
    simp [Stmt.HoldsList, Stmt.Holds]
  | .atom a :: ss, vs, h, hA => by
    simp only [Stmt.HoldsList, Stmt.Holds]
    exact ⟨hA a List.mem_cons_self, holdsList_trivC (B := ss) h fun b hb => hA b (List.mem_cons_of_mem _ hb)⟩
  | .call f a r :: ss, vs, h, hA => by
    simp only [Stmt.HoldsList, Stmt.Holds]
    exact ⟨trivial, holdsList_trivC (B := ss) h fun b hb => hA b (List.mem_cons_of_mem _ hb)⟩
  | .ret _ :: _ :: _, _, h, _ => by simp [retOfC] at h
  | .ite .. :: _, _, h, _ | .match_ .. :: _, _, h, _ | .callIf .. :: _, _, h, _
  | .dispatch .. :: _, _, h, _ => by simp [retOfC] at h

/-- **A body of atoms and calls with stores completes**, from its atoms' meaning, its callees
complete on the oracle's words. -/
theorem callCompletes_storesCalls {k : ℕ} {name : String} {fn : Fn} {args rets : List E}
    (ins outs : List (ℕ × List E)) (w : ℕ → E) (hfind : coreProgram.find? name = some fn)
    (hparams : fn.params = (List.range args.length).map V.n)
    (hck : storeCallChecks args.length (shapeOf ins) (shapeOf outs) fn.body = true)
    (hargs : ∀ q ∈ ins ++ outs, q.1 < args.length)
    (hio : ∀ q ∈ ins, ∀ q' ∈ outs, q.1 ≠ q'.1)
    (hapart : ArraysApart args (shapeOf (ins ++ outs)))
    (hkids : KidsCompl k (σ0 args w)
      (fun rd => HoldsWords rd [] ∧ (HoldsArrays rd args ins ∧ HoldsArrays rd args outs))
      ((callsOfB fn.body).map fun _ => PostQuiet) (callsOfB fn.body))
    (hmean : ∀ rd' (σ : Val) (vs : List V), retOfC fn.body = some vs → fn.params.map σ = args →
      HoldsArrays rd' args ins → (∀ f a r, Stmt.call f a r ∈ fn.body → ∀ v ∈ r, σ v = w v.idx) →
      (∀ a, Stmt.atom a ∈ fn.body → a.Holds rd' σ) → HoldsArrays rd' args outs ∧ vs.map σ = rets) :
    CallCompletes k name args rets (fun rd => HoldsArrays rd args ins ∧ HoldsArrays rd args outs)
      PostQuiet := by
  simp only [storeCallChecks, Bool.and_eq_true, decide_eq_true_eq] at hck
  obtain ⟨⟨⟨⟨⟨hc, hr⟩, hok⟩, hnd⟩, hSl⟩, hco⟩ := hck
  obtain ⟨c', hc⟩ := Option.isSome_iff_exists.mp hc
  obtain ⟨vs, hr⟩ := Option.isSome_iff_exists.mp hr
  obtain ⟨ss, hbody, hss⟩ := retOfC_spec hr
  set S := storesOf args.length fn.body with hSdef
  have hst : ∀ a, Stmt.atom a ∈ fn.body → stOk (shapeOf ins) (shapeOf outs) S a = true := fun a ha =>
    List.all_eq_true.mp hok a (mem_atomsOf' ha)
  have hcalls : callsOfB fn.body = callsOfB ss := by
    rw [hbody]; simp [callsOfB, callOf?]
  have hwalk : ∀ σ, walk σ fn.body = .ret (ss.flatMap (slEvs (σ0 args w))) vs := by
    intro σ
    rw [hbody, walk_straight σ vs ss (straight_of_atomOrCall ss hss)]
    congr 1
    exact List.flatMap_congr fun s hs => slEvs_atomOrCall σ _ s (List.all_eq_true.mp hss s hs)
  have hes : calls (ss.flatMap (slEvs (σ0 args w))) = callsOfB fn.body := by
    rw [calls_atomOrCall _ ss hss, hcalls]
  refine callCompletes_nodeRd fun b => ⟨0, [], σ0 args w, fn, ss.flatMap (slEvs (σ0 args w)), vs,
    (callsOfB fn.body).map fun _ => PostQuiet, wordsIn_nil b, hfind, by rw [hes]; exact hkids,
    fun rd hl _ ⟨hin, hout⟩ => ?_⟩
  -- the forward valuation, and its atoms on `rd`, as in `callCompletes_stores`
  have hS : ∀ a ∈ S, ∃ d q off, a = .load d (.n q.1) off ∧ q ∈ outs ∧ off < q.2.length := by
    intro a ha
    have hl := List.all_eq_true.mp hSl a ha
    have h := hst a (storesOf_mem ha)
    cases a with
    | load d p off =>
      simp only [stOk, ha, ↓reduceIte] at h
      obtain ⟨q, hq, rfl, hk⟩ := inArrays_spec h
      exact ⟨d, q, off, rfl, hq, hk⟩
    | _ => simp [isLoadB] at hl
  have hL : ∀ d p off, Stmt.atom (.load d p off) ∈ fn.body → Atom.load d p off ∉ S →
      ∃ q ∈ ins, p = .n q.1 ∧ off < q.2.length := by
    intro d p off hm hns
    have h := hst _ hm
    simp only [stOk, hns, ↓reduceIte] at h
    exact inArrays_spec h
  set σ := fwdVal rd w args fn.body with hσ
  have G : ∀ a, Stmt.atom a ∈ fn.body → Good rd S w σ a := fwd_good hc
  have hpar : ∀ q ∈ ins ++ outs, σ (.n q.1) = args.getD q.1 0 := fun q hq => fwd_param hc (hargs q hq)
  have hpI : ∀ q ∈ ins, σ (.n q.1) = args.getD q.1 0 := fun q hq => hpar q (List.mem_append_left _ hq)
  have hpO : ∀ q ∈ outs, σ (.n q.1) = args.getD q.1 0 := fun q hq => hpar q (List.mem_append_right _ hq)
  have hshI : ∀ q ∈ ins, (q.1, q.2.length) ∈ shapeOf (ins ++ outs) := fun q hq =>
    List.mem_map.mpr ⟨q, List.mem_append_left _ hq, rfl⟩
  have hshO : ∀ q ∈ outs, (q.1, q.2.length) ∈ shapeOf (ins ++ outs) := fun q hq =>
    List.mem_map.mpr ⟨q, List.mem_append_right _ hq, rfl⟩
  have hu : ∀ s ∈ S, ∀ s' ∈ S, storeAt σ s = storeAt σ s' → storeAt σ s ≠ none → s = s' := by
    intro s hs s' hs' he _
    obtain ⟨d, q, off, rfl, hq, hk⟩ := hS s hs
    obtain ⟨d', q', off', rfl, hq', hk'⟩ := hS s' hs'
    simp only [storeAt, Option.some.injEq, hpO q hq, hpO q' hq'] at he
    obtain ⟨e1, e2⟩ := hapart _ (hshO q hq) _ (hshO q' hq') off hk off' hk' he
    refine List.inj_on_of_nodup_map hnd hs hs' ?_
    have e1' : q.1 = q'.1 := e1
    have e2' : off = off' := e2
    simp only [storeKey, e1', e2']
  set rdS := overlay rd S σ with hrdS
  have hnew : ∀ d p off, Stmt.atom (.load d p off) ∈ fn.body → Atom.load d p off ∉ S →
      LoadHolds rd (σ p) off (σ d) ∧ LoadHolds rdS (σ p) off (σ d) := by
    intro d p off hm hns
    obtain ⟨q, hq, rfl, hk⟩ := hL d p off hm hns
    have hld := readsAt_load (hin q hq) hk
    have hd : σ d = q.2.getD off 0 := by
      rw [← hpI q hq] at hld; exact good_load_eq hld (G _ hm) hns
    rw [hd, hpI q hq]
    refine ⟨hld, hld.1, ?_⟩
    rw [hrdS, overlay_other, hld.2]
    intro s hs he
    obtain ⟨d', q', off', rfl, hq', hk'⟩ := hS s hs
    simp only [storeAt, Option.some.injEq, hpO q' hq'] at he
    obtain ⟨e1, -⟩ := hapart _ (hshO q' hq') _ (hshI q hq) off' hk' off hk he
    exact hio q hq q' hq' (show q'.1 = q.1 from e1).symm
  have hAS : ∀ a, Stmt.atom a ∈ fn.body → a.Holds rdS σ := by
    intro a ha
    have hb := atoms_holds (rd := rdS) (S := S) (w := w) (σ := σ) (atoms := [a])
      (fun b hb => by
        rw [List.mem_singleton] at hb; subst hb
        cases hlb : isLoadB b
        · cases hnb : needsSide b
          · have := hst b ha
            refine good_reader hlb hnb ?_ (G b ha)
            cases b with
            | hint => simp [stOk] at this
            | _ => rfl
          · have := hst b ha
            cases b with
            | load => simp [isLoadB] at hlb
            | hint => simp [stOk] at this
            | _ => simp only [stOk, hnb, Bool.not_true, Bool.false_eq_true] at this
        · cases b with
          | load d p off =>
            by_cases hbs : Atom.load d p off ∈ S
            · exact Or.inl hbs
            · right; rw [rdAt, (hnew d p off ha hbs).2.2]; rfl
          | _ => simp [isLoadB] at hlb)
      (fun b hb hn => by
        rw [List.mem_singleton] at hb; subst hb
        have h := hst b ha
        cases b with
        | load d p off =>
          by_cases hbs : Atom.load d p off ∈ S
          · right
            simp only [Side, hbs, ↓reduceIte]
            obtain ⟨d', q, off', he, hq, hk⟩ := hS _ hbs
            obtain ⟨rfl, rfl, rfl⟩ := Atom.load.inj he
            refine ⟨?_, overlay_store hu hbs⟩
            rw [hpO q hq]; exact (readsAt_load (hout q hq) hk).1
          · exact Or.inl (hnew d p off ha hbs).2
        | hint => simp [stOk] at h
        | _ => simp only [stOk, hn, Bool.not_true, Bool.false_eq_true] at h)
    exact hb a List.mem_cons_self
  have hp : fn.params.map σ = args := by rw [hparams]; exact fwd_params hc
  have hW : ∀ f a r, Stmt.call f a r ∈ fn.body → ∀ v ∈ r, σ v = w v.idx := fun f a r hm v hv =>
    (ev_spec rd w fn.body args hc).2.2 _ hm v hv
  have hinS : HoldsArrays rdS args ins := by
    intro q hq i hi
    have hld := hin q hq i hi
    refine ⟨hld.1, ?_⟩
    rw [hrdS, overlay_other, hld.2]
    intro s hs he
    obtain ⟨d', q', off', rfl, hq', hk'⟩ := hS s hs
    simp only [storeAt, Option.some.injEq, hpO q' hq'] at he
    obtain ⟨e1, -⟩ := hapart _ (hshO q' hq') _ (hshI q hq) off' hk' i hi he
    exact hio q hq q' hq' (show q'.1 = q.1 from e1).symm
  obtain ⟨houtS, -⟩ := hmean rdS σ vs hr hp hinS hW hAS
  have hstore : ∀ d p off, Atom.load d p off ∈ S → LoadHolds rd (σ p) off (σ d) := by
    intro d p off hbs
    obtain ⟨d', q, off', he, hq, hk⟩ := hS _ hbs
    obtain ⟨rfl, rfl, rfl⟩ := Atom.load.inj he
    have h1 := readsAt_load (houtS q hq) hk
    have h2 := readsAt_load (hout q hq) hk
    rw [← hpO q hq] at h1 h2
    have := overlay_store (rd := rd) hu hbs
    rw [← hrdS, h1.2] at this
    rw [← Option.some.inj this]
    exact h2
  have hA : ∀ a, Stmt.atom a ∈ fn.body → a.Holds rd σ := by
    refine fwd_holds hc fun a ha hn => ?_
    have h := hst a ha
    cases a with
    | load d p off =>
      by_cases hbs : Atom.load d p off ∈ S
      · exact Or.inl (hstore d p off hbs)
      · exact Or.inl (hnew d p off ha hbs).1
    | hint => simp [stOk] at h
    | _ => simp only [stOk, hn, Bool.not_true, Bool.false_eq_true] at h
  obtain ⟨-, hret⟩ := hmean rd σ vs hr hp hin hW hA
  have hmemss : ∀ s ∈ ss, s ∈ fn.body := fun s hs => by rw [hbody]; exact List.mem_append_left _ hs
  have hevA : ∀ a, Ev.atom a ∈ ss.flatMap (slEvs (σ0 args w)) → Stmt.atom a ∈ fn.body := fun a ha =>
    hmemss _ (atoms_slEvs ha)
  -- the calls agree with `σ0`: parameters, and the oracle's returns
  have hag : CallsAgree (σ0 args w) σ (calls (ss.flatMap (slEvs (σ0 args w)))) := by
    rw [hes]
    intro c hcm
    have hm := mem_callsOfB hcm
    have hok := List.all_eq_true.mp hco _ hm
    simp only [callOkB, Bool.and_eq_true, List.all_eq_true] at hok
    refine ⟨List.map_congr_left fun v hv => ?_, List.map_congr_left fun v hv => ?_⟩
    · have := hok.1 v hv
      simp only [isParamB, Bool.and_eq_true, decide_eq_true_eq] at this
      obtain ⟨hv1, hv2⟩ := this
      show (if v.idx < args.length then args.getD v.idx 0 else w v.idx) = σ v
      simp only [hv2, ↓reduceIte]
      conv_rhs => rw [hv1]
      exact (fwd_param hc hv2).symm
    · have := hok.2 v hv
      simp only [isFreshB, Bool.and_eq_true, decide_eq_true_eq] at this
      show (if v.idx < args.length then args.getD v.idx 0 else w v.idx) = σ v
      simp only [show ¬ v.idx < args.length by omega, ↓reduceIte]
      exact (hW _ _ _ hm v hv).symm
  refine ⟨σ, hp, hwalk σ, hret, hag, fun e he => ?_, fun ts hv hq => ?_⟩
  · rw [List.mem_flatMap] at he
    obtain ⟨s, hs, he⟩ := he
    cases s with
    | atom a =>
      simp only [slEvs, List.mem_singleton] at he; subst he
      exact hA a (hmemss _ hs)
    | call f a r => simp only [slEvs, List.mem_singleton] at he; subst he; trivial
    | _ => exact absurd (List.all_eq_true.mp hss _ hs) (by simp [atomOrCall])
  · refine postQuiet_node hfind (hwalk σ) (fun a ha => ?_) (fun e he => ?_) hv (by rw [hes]; rw [hes] at hq; exact hq) _
    · have := hst a (hevA a ha)
      cases a with
      | hint => simp [stOk] at this
      | _ => rfl
    · rw [List.mem_flatMap] at he
      obtain ⟨s, hs, he⟩ := he
      cases s with
      | atom a =>
        simp only [slEvs, List.mem_singleton] at he; subst he
        have := hst a (hmemss _ hs)
        cases a with
        | hint => simp [stOk] at this
        | _ => trivial
      | call => simp only [slEvs, List.mem_singleton] at he; subst he; trivial
      | _ => exact absurd (List.all_eq_true.mp hss _ hs) (by simp [atomOrCall])

/-- **A node completes with no words of its own** on a valuation per memory, its callees' trees
on `σ0`'s words given on every memory. -/
theorem callCompletes0_nodeRd {k : ℕ} {f : String} {args rets : List E} {Pre : Reader → Prop}
    {Post : Reader → Tree → Prop} {σ0 : Val} {fn : Fn} {es : List Ev} {vs : List V}
    {Qs : List (Reader → Tree → Prop)} (hf : coreProgram.find? f = some fn)
    (hk : ∀ rd, LowDef k rd → Pre rd → ∃ ts, Tree.KidsValid coreProgram rd σ0 (calls es) ts ∧
      Tree.BufsOkKids coreProgram ts ∧ KidsPost rd Qs (calls es) ts)
    (hrd : ∀ rd, LowDef k rd → Pre rd → ∃ σ : Val,
        fn.params.map σ = args ∧ walk σ fn.body = .ret es vs ∧ vs.map σ = rets ∧
        CallsAgree σ0 σ (calls es) ∧ (∀ e ∈ es, e.Holds rd σ) ∧
        ∀ ts, Tree.KidsValid coreProgram rd σ (calls es) ts → KidsPost rd Qs (calls es) ts →
          Post rd (.node f σ (allocs σ es) ts)) :
    CallCompletes0 k f args rets Pre Post := fun rd hl hP => by
  obtain ⟨ts, hvs, hbs, hqs⟩ := hk rd hl hP
  obtain ⟨σ, hp, hw, hr, hag, hev, hpost⟩ := hrd rd hl hP
  have hvs' := kidsValid_congr _ _ hag hvs
  refine ⟨.node f σ (allocs σ es) ts, rfl, ⟨fn, hf, hp, es, vs, hw, hr, hev, hvs'⟩, ?_, hpost ts hvs' hqs⟩
  rw [Tree.BufsOk, Complete.events_node hf hw]
  exact ⟨rfl, hbs⟩

/-- **`callCompletes_storesCalls` with no words of its own**, its callees' trees given on every
memory. -/
theorem callCompletes0_storesCalls {k : ℕ} {name : String} {fn : Fn} {args rets : List E}
    (ins outs : List (ℕ × List E)) (w : ℕ → E) (hfind : coreProgram.find? name = some fn)
    (hparams : fn.params = (List.range args.length).map V.n)
    (hck : storeCallChecks args.length (shapeOf ins) (shapeOf outs) fn.body = true)
    (hargs : ∀ q ∈ ins ++ outs, q.1 < args.length)
    (hio : ∀ q ∈ ins, ∀ q' ∈ outs, q.1 ≠ q'.1)
    (hapart : ArraysApart args (shapeOf (ins ++ outs)))
    (hkids : ∀ rd, LowDef k rd → HoldsArrays rd args ins ∧ HoldsArrays rd args outs → ∃ ts,
      Tree.KidsValid coreProgram rd (σ0 args w) (callsOfB fn.body) ts ∧ Tree.BufsOkKids coreProgram ts ∧
        KidsPost rd ((callsOfB fn.body).map fun _ => PostQuiet) (callsOfB fn.body) ts)
    (hmean : ∀ rd' (σ : Val) (vs : List V), retOfC fn.body = some vs → fn.params.map σ = args →
      HoldsArrays rd' args ins → (∀ f a r, Stmt.call f a r ∈ fn.body → ∀ v ∈ r, σ v = w v.idx) →
      (∀ a, Stmt.atom a ∈ fn.body → a.Holds rd' σ) → HoldsArrays rd' args outs ∧ vs.map σ = rets) :
    CallCompletes0 k name args rets (fun rd => HoldsArrays rd args ins ∧ HoldsArrays rd args outs)
      PostQuiet := by
  simp only [storeCallChecks, Bool.and_eq_true, decide_eq_true_eq] at hck
  obtain ⟨⟨⟨⟨⟨hc, hr⟩, hok⟩, hnd⟩, hSl⟩, hco⟩ := hck
  obtain ⟨c', hc⟩ := Option.isSome_iff_exists.mp hc
  obtain ⟨vs, hr⟩ := Option.isSome_iff_exists.mp hr
  obtain ⟨ss, hbody, hss⟩ := retOfC_spec hr
  set S := storesOf args.length fn.body with hSdef
  have hst : ∀ a, Stmt.atom a ∈ fn.body → stOk (shapeOf ins) (shapeOf outs) S a = true := fun a ha =>
    List.all_eq_true.mp hok a (mem_atomsOf' ha)
  have hcalls : callsOfB fn.body = callsOfB ss := by
    rw [hbody]; simp [callsOfB, callOf?]
  have hwalk : ∀ σ, walk σ fn.body = .ret (ss.flatMap (slEvs (σ0 args w))) vs := by
    intro σ
    rw [hbody, walk_straight σ vs ss (straight_of_atomOrCall ss hss)]
    congr 1
    exact List.flatMap_congr fun s hs => slEvs_atomOrCall σ _ s (List.all_eq_true.mp hss s hs)
  have hes : calls (ss.flatMap (slEvs (σ0 args w))) = callsOfB fn.body := by
    rw [calls_atomOrCall _ ss hss, hcalls]
  refine callCompletes0_nodeRd (σ0 := σ0 args w) (es := ss.flatMap (slEvs (σ0 args w))) (vs := vs)
    (Qs := (callsOfB fn.body).map fun _ => PostQuiet) hfind (by rw [hes]; exact hkids)
    fun rd hl ⟨hin, hout⟩ => ?_
  -- the forward valuation, and its atoms on `rd`, as in `callCompletes_stores`
  have hS : ∀ a ∈ S, ∃ d q off, a = .load d (.n q.1) off ∧ q ∈ outs ∧ off < q.2.length := by
    intro a ha
    have hl := List.all_eq_true.mp hSl a ha
    have h := hst a (storesOf_mem ha)
    cases a with
    | load d p off =>
      simp only [stOk, ha, ↓reduceIte] at h
      obtain ⟨q, hq, rfl, hk⟩ := inArrays_spec h
      exact ⟨d, q, off, rfl, hq, hk⟩
    | _ => simp [isLoadB] at hl
  have hL : ∀ d p off, Stmt.atom (.load d p off) ∈ fn.body → Atom.load d p off ∉ S →
      ∃ q ∈ ins, p = .n q.1 ∧ off < q.2.length := by
    intro d p off hm hns
    have h := hst _ hm
    simp only [stOk, hns, ↓reduceIte] at h
    exact inArrays_spec h
  set σ := fwdVal rd w args fn.body with hσ
  have G : ∀ a, Stmt.atom a ∈ fn.body → Good rd S w σ a := fwd_good hc
  have hpar : ∀ q ∈ ins ++ outs, σ (.n q.1) = args.getD q.1 0 := fun q hq => fwd_param hc (hargs q hq)
  have hpI : ∀ q ∈ ins, σ (.n q.1) = args.getD q.1 0 := fun q hq => hpar q (List.mem_append_left _ hq)
  have hpO : ∀ q ∈ outs, σ (.n q.1) = args.getD q.1 0 := fun q hq => hpar q (List.mem_append_right _ hq)
  have hshI : ∀ q ∈ ins, (q.1, q.2.length) ∈ shapeOf (ins ++ outs) := fun q hq =>
    List.mem_map.mpr ⟨q, List.mem_append_left _ hq, rfl⟩
  have hshO : ∀ q ∈ outs, (q.1, q.2.length) ∈ shapeOf (ins ++ outs) := fun q hq =>
    List.mem_map.mpr ⟨q, List.mem_append_right _ hq, rfl⟩
  have hu : ∀ s ∈ S, ∀ s' ∈ S, storeAt σ s = storeAt σ s' → storeAt σ s ≠ none → s = s' := by
    intro s hs s' hs' he _
    obtain ⟨d, q, off, rfl, hq, hk⟩ := hS s hs
    obtain ⟨d', q', off', rfl, hq', hk'⟩ := hS s' hs'
    simp only [storeAt, Option.some.injEq, hpO q hq, hpO q' hq'] at he
    obtain ⟨e1, e2⟩ := hapart _ (hshO q hq) _ (hshO q' hq') off hk off' hk' he
    refine List.inj_on_of_nodup_map hnd hs hs' ?_
    have e1' : q.1 = q'.1 := e1
    have e2' : off = off' := e2
    simp only [storeKey, e1', e2']
  set rdS := overlay rd S σ with hrdS
  have hnew : ∀ d p off, Stmt.atom (.load d p off) ∈ fn.body → Atom.load d p off ∉ S →
      LoadHolds rd (σ p) off (σ d) ∧ LoadHolds rdS (σ p) off (σ d) := by
    intro d p off hm hns
    obtain ⟨q, hq, rfl, hk⟩ := hL d p off hm hns
    have hld := readsAt_load (hin q hq) hk
    have hd : σ d = q.2.getD off 0 := by
      rw [← hpI q hq] at hld; exact good_load_eq hld (G _ hm) hns
    rw [hd, hpI q hq]
    refine ⟨hld, hld.1, ?_⟩
    rw [hrdS, overlay_other, hld.2]
    intro s hs he
    obtain ⟨d', q', off', rfl, hq', hk'⟩ := hS s hs
    simp only [storeAt, Option.some.injEq, hpO q' hq'] at he
    obtain ⟨e1, -⟩ := hapart _ (hshO q' hq') _ (hshI q hq) off' hk' off hk he
    exact hio q hq q' hq' (show q'.1 = q.1 from e1).symm
  have hAS : ∀ a, Stmt.atom a ∈ fn.body → a.Holds rdS σ := by
    intro a ha
    have hb := atoms_holds (rd := rdS) (S := S) (w := w) (σ := σ) (atoms := [a])
      (fun b hb => by
        rw [List.mem_singleton] at hb; subst hb
        cases hlb : isLoadB b
        · cases hnb : needsSide b
          · have := hst b ha
            refine good_reader hlb hnb ?_ (G b ha)
            cases b with
            | hint => simp [stOk] at this
            | _ => rfl
          · have := hst b ha
            cases b with
            | load => simp [isLoadB] at hlb
            | hint => simp [stOk] at this
            | _ => simp only [stOk, hnb, Bool.not_true, Bool.false_eq_true] at this
        · cases b with
          | load d p off =>
            by_cases hbs : Atom.load d p off ∈ S
            · exact Or.inl hbs
            · right; rw [rdAt, (hnew d p off ha hbs).2.2]; rfl
          | _ => simp [isLoadB] at hlb)
      (fun b hb hn => by
        rw [List.mem_singleton] at hb; subst hb
        have h := hst b ha
        cases b with
        | load d p off =>
          by_cases hbs : Atom.load d p off ∈ S
          · right
            simp only [Side, hbs, ↓reduceIte]
            obtain ⟨d', q, off', he, hq, hk⟩ := hS _ hbs
            obtain ⟨rfl, rfl, rfl⟩ := Atom.load.inj he
            refine ⟨?_, overlay_store hu hbs⟩
            rw [hpO q hq]; exact (readsAt_load (hout q hq) hk).1
          · exact Or.inl (hnew d p off ha hbs).2
        | hint => simp [stOk] at h
        | _ => simp only [stOk, hn, Bool.not_true, Bool.false_eq_true] at h)
    exact hb a List.mem_cons_self
  have hp : fn.params.map σ = args := by rw [hparams]; exact fwd_params hc
  have hW : ∀ f a r, Stmt.call f a r ∈ fn.body → ∀ v ∈ r, σ v = w v.idx := fun f a r hm v hv =>
    (ev_spec rd w fn.body args hc).2.2 _ hm v hv
  have hinS : HoldsArrays rdS args ins := by
    intro q hq i hi
    have hld := hin q hq i hi
    refine ⟨hld.1, ?_⟩
    rw [hrdS, overlay_other, hld.2]
    intro s hs he
    obtain ⟨d', q', off', rfl, hq', hk'⟩ := hS s hs
    simp only [storeAt, Option.some.injEq, hpO q' hq'] at he
    obtain ⟨e1, -⟩ := hapart _ (hshO q' hq') _ (hshI q hq) off' hk' i hi he
    exact hio q hq q' hq' (show q'.1 = q.1 from e1).symm
  obtain ⟨houtS, -⟩ := hmean rdS σ vs hr hp hinS hW hAS
  have hstore : ∀ d p off, Atom.load d p off ∈ S → LoadHolds rd (σ p) off (σ d) := by
    intro d p off hbs
    obtain ⟨d', q, off', he, hq, hk⟩ := hS _ hbs
    obtain ⟨rfl, rfl, rfl⟩ := Atom.load.inj he
    have h1 := readsAt_load (houtS q hq) hk
    have h2 := readsAt_load (hout q hq) hk
    rw [← hpO q hq] at h1 h2
    have := overlay_store (rd := rd) hu hbs
    rw [← hrdS, h1.2] at this
    rw [← Option.some.inj this]
    exact h2
  have hA : ∀ a, Stmt.atom a ∈ fn.body → a.Holds rd σ := by
    refine fwd_holds hc fun a ha hn => ?_
    have h := hst a ha
    cases a with
    | load d p off =>
      by_cases hbs : Atom.load d p off ∈ S
      · exact Or.inl (hstore d p off hbs)
      · exact Or.inl (hnew d p off ha hbs).1
    | hint => simp [stOk] at h
    | _ => simp only [stOk, hn, Bool.not_true, Bool.false_eq_true] at h
  obtain ⟨-, hret⟩ := hmean rd σ vs hr hp hin hW hA
  have hmemss : ∀ s ∈ ss, s ∈ fn.body := fun s hs => by rw [hbody]; exact List.mem_append_left _ hs
  have hevA : ∀ a, Ev.atom a ∈ ss.flatMap (slEvs (σ0 args w)) → Stmt.atom a ∈ fn.body := fun a ha =>
    hmemss _ (atoms_slEvs ha)
  -- the calls agree with `σ0`: parameters, and the oracle's returns
  have hag : CallsAgree (σ0 args w) σ (calls (ss.flatMap (slEvs (σ0 args w)))) := by
    rw [hes]
    intro c hcm
    have hm := mem_callsOfB hcm
    have hok := List.all_eq_true.mp hco _ hm
    simp only [callOkB, Bool.and_eq_true, List.all_eq_true] at hok
    refine ⟨List.map_congr_left fun v hv => ?_, List.map_congr_left fun v hv => ?_⟩
    · have := hok.1 v hv
      simp only [isParamB, Bool.and_eq_true, decide_eq_true_eq] at this
      obtain ⟨hv1, hv2⟩ := this
      show (if v.idx < args.length then args.getD v.idx 0 else w v.idx) = σ v
      simp only [hv2, ↓reduceIte]
      conv_rhs => rw [hv1]
      exact (fwd_param hc hv2).symm
    · have := hok.2 v hv
      simp only [isFreshB, Bool.and_eq_true, decide_eq_true_eq] at this
      show (if v.idx < args.length then args.getD v.idx 0 else w v.idx) = σ v
      simp only [show ¬ v.idx < args.length by omega, ↓reduceIte]
      exact (hW _ _ _ hm v hv).symm
  refine ⟨σ, hp, hwalk σ, hret, hag, fun e he => ?_, fun ts hv hq => ?_⟩
  · rw [List.mem_flatMap] at he
    obtain ⟨s, hs, he⟩ := he
    cases s with
    | atom a =>
      simp only [slEvs, List.mem_singleton] at he; subst he
      exact hA a (hmemss _ hs)
    | call f a r => simp only [slEvs, List.mem_singleton] at he; subst he; trivial
    | _ => exact absurd (List.all_eq_true.mp hss _ hs) (by simp [atomOrCall])
  · refine postQuiet_node hfind (hwalk σ) (fun a ha => ?_) (fun e he => ?_) hv (by rw [hes]; rw [hes] at hq; exact hq) _
    · have := hst a (hevA a ha)
      cases a with
      | hint => simp [stOk] at this
      | _ => rfl
    · rw [List.mem_flatMap] at he
      obtain ⟨s, hs, he⟩ := he
      cases s with
      | atom a =>
        simp only [slEvs, List.mem_singleton] at he; subst he
        have := hst a (hmemss _ hs)
        cases a with
        | hint => simp [stOk] at this
        | _ => trivial
      | call => simp only [slEvs, List.mem_singleton] at he; subst he; trivial
      | _ => exact absurd (List.all_eq_true.mp hss _ hs) (by simp [atomOrCall])

end
end LeanVM.Guest.B1.VsC
