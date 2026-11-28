/-
  LeanVM.Guest.B1.VsC.Oq.VmcA

  `verify_merkle_cap__L{D}` completes placed: a pure leaf with branches, loading from the cap and
  the flags it is handed.
-/

module

public import LeanVM.Guest.B1.VsC.FreeC
public import LeanVM.Guest.B1.VsC.SlowA
public import LeanVM.Guest.Complete.PureA
public import LeanVM.Guest.Exact.Atoms

/-!
# `verify_merkle_cap`, placed

A leaf whose every atom, in every branch, is a load through one of its array arguments at an
offset below the array's length, or neither a load nor a hint (`loadInBQ`), loads only from those
arrays and hints nothing to the heap on every valid tree (`loadsR_hintsR_of_atomsAll`), whichever
branch its valuation takes. `verify_merkle_cap__L{D}` is such a leaf, places nothing and calls
nothing (`vmcFacts`, one `decide +kernel` a depth), so its layout-free completeness transfers
(`vmcA`): on `[cap, flags]`, the region covering the cap's `2^(D+2)` cells and the flags' `2^D`, it
completes at every position, ending at its cursor, popping nothing, exact.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete

@[expose] public section

/-- A load through one of the arrays `ps` (argument index, length), or neither a load nor a hint. -/
def loadInBQ (ps : List (ℕ × ℕ)) : Atom → Bool
  | .load _ p k => ps.any fun q => p == .n q.1 && decide (k < q.2)
  | .hint _ => false
  | _ => true

/-- **Every atom on a path satisfies what every atom of the body does.** -/
theorem walk_atomsAll {σ : Val} {body : List Stmt} {es : List Ev} {vs : List V} {p : Atom → Bool}
    (h : Stmt.atomsAll p body = true) (hw : walk σ body = .ret es vs) :
    ∀ a, Ev.atom a ∈ es → p a = true := by
  have h' : Stmt.atomsAll (fun a => !(fun a => !p a) a) body = true := by
    simpa only [Bool.not_not] using h
  have hp := walk_partnered (σ := σ) (p := fun a => !p a) (q := fun _ _ => false) body
    (blockNextOk_of_atomsAll body h')
  rw [hw] at hp
  intro a ha
  by_contra hc
  obtain ⟨b, -, hb⟩ := hp a ha (by simpa using hc)
  exact absurd hb (by simp)

/-- **A leaf with branches reading its arguments' arrays loads from them and hints nothing to the
heap**, on every valid tree. -/
theorem loadsR_hintsR_of_atomsAll {f : String} {fn : Fn} {ps : List (ℕ × ℕ)} {args rets : List E}
    {rd : Reader} {t : Tree} (R : ℕ → Prop) (hfind : coreProgram.find? f = some fn)
    (hparams : fn.params = (List.range args.length).map V.n)
    (hL : Stmt.atomsAll (loadInBQ ps) fn.body = true)
    (hnc : ∀ σ es vs, walk σ fn.body = .ret es vs → calls es = [])
    (hargs : ∀ q ∈ ps, q.1 < args.length) (hptr : ∀ q ∈ ps, ∃ b, args.getD q.1 0 = ptrAt b)
    (hn : t.name = f) (hv : t.Valid coreProgram rd args rets) :
    t.LoadsR coreProgram (argRegion args ps) ∧ t.HintsR coreProgram R := by
  cases t with
  | phantom _ _ => exact hv.elim
  | node g σ bufs kids =>
    obtain ⟨fn', hfn, hpar, es, vs, hw, _, _, hk⟩ := hv
    simp only [Tree.name] at hn
    subst hn
    rw [hfind] at hfn
    cases hfn
    have hev : (Memory.Tree.node g σ bufs kids).events coreProgram = es := Complete.events_node hfind hw
    rw [hnc σ es vs hw] at hk
    have hkids : kids = [] := by
      cases kids with
      | nil => rfl
      | cons _ _ => simp [Tree.KidsValid] at hk
    subst hkids
    have hok := walk_atomsAll hL hw
    have hσ : ∀ j < args.length, σ (.n j) = args.getD j 0 := by
      intro j hj
      have hj' : (((List.range args.length).map V.n).map σ)[j]? = args[j]? := by rw [← hparams, hpar]
      simp [hj] at hj'
      simpa [List.getD_eq_getElem?_getD, hj] using hj'
    refine ⟨?_, ?_⟩
    · rw [Tree.LoadsR, hev]
      refine ⟨fun A hA => ?_, by rw [Tree.LoadsRKids]; trivial⟩
      obtain ⟨e, he, hA⟩ := List.mem_filterMap.mp hA
      cases e with
      | atom a =>
        have hk := hok a he
        cases a with
        | load d p off =>
          simp only [Ev.loadAddr?, Option.some.injEq] at hA
          simp only [loadInBQ, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hk
          obtain ⟨q, hqm, rfl, hoff⟩ := hk
          obtain ⟨b, hb⟩ := hptr q hqm
          refine ⟨b + off, ?_, q, hqm, b, hb, by omega, by omega⟩
          rw [← hA, hσ _ (hargs q hqm), hb]
          exact Main.addr_ofK b off
        | _ => simp [Ev.loadAddr?] at hA
      | _ => simp [Ev.loadAddr?] at hA
    · rw [Tree.HintsR, hev]
      refine ⟨fun A hA => ?_, by rw [Tree.HintsRKids]; trivial⟩
      obtain ⟨e, he, hA⟩ := List.mem_flatMap.mp hA
      cases e with
      | atom a =>
        have hk := hok a he
        cases a with
        | hint _ => simp [loadInBQ] at hk
        | _ => simp [Ev.hintAddrs] at hA
      | _ => simp [Ev.hintAddrs] at hA

/-- No call on a path of a body placing nothing and calling nothing. -/
theorem calls_nil_of_pure {σ : Val} {body : List Stmt} {es : List Ev} {vs : List V}
    (h : Stmt.pureList [] body = true) (hw : walk σ body = .ret es vs) : calls es = [] := by
  have hp := walk_pure (σ := σ) body h
  rw [hw] at hp
  refine List.filterMap_eq_nil_iff.mpr fun e he => ?_
  have := hp e he
  cases e with
  | call f _ _ => simp [Ev.pure] at this
  | skip f _ => simp [Ev.pure] at this
  | _ => rfl

/-! ## The deployed depths -/

/-- What the kernel checks of `verify_merkle_cap__L{D}` at position `j`: its two parameters, it
places and calls nothing, every atom loads from the cap (`2^(D+2)` cells) or the flags (`2^D`) or
is neither a load nor a hint, it is no loop helper. -/
noncomputable def vmcFacts (n : String) (j D : ℕ) : Bool :=
  match coreProgram[j]? with
  | some fn => decide (fn.name = n) && decide (fn.params = [.n 0, .n 1]) && Stmt.pureList [] fn.body &&
      Stmt.pureList [fn.name] fn.body && Stmt.atomsAll (loadInBQ [(0, 2 ^ (D + 2)), (1, 2 ^ D)]) fn.body &&
      !fn.loop
  | none => false

set_option maxRecDepth 100000 in
theorem vmc_facts_0 : vmcFacts "verify_merkle_cap__L2" idx% «verify_merkle_cap__L2» 2 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem vmc_facts_1 : vmcFacts "verify_merkle_cap__L3" idx% «verify_merkle_cap__L3» 3 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem vmc_facts_2 : vmcFacts "verify_merkle_cap__L4" idx% «verify_merkle_cap__L4» 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem vmc_facts_3 : vmcFacts "verify_merkle_cap__L5" idx% «verify_merkle_cap__L5» 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem vmc_facts_4 : vmcFacts "verify_merkle_cap__L6" idx% «verify_merkle_cap__L6» 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem vmc_facts_5 : vmcFacts "verify_merkle_cap__L7" idx% «verify_merkle_cap__L7» 7 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem vmc_facts_6 : vmcFacts "verify_merkle_cap__L8" idx% «verify_merkle_cap__L8» 8 = true := by decide +kernel

/-- The function of a deployed depth, with its facts. -/
theorem vmc_fn : ∀ p ∈ merkleCapNames, ∃ fn : Fn, coreProgram.find? p.1 = some fn ∧
    fn.params = [.n 0, .n 1] ∧ Stmt.pureList [] fn.body = true ∧ Stmt.pureList [p.1] fn.body = true ∧
    Stmt.atomsAll (loadInBQ [(0, 2 ^ (p.2 + 2)), (1, 2 ^ p.2)]) fn.body = true ∧ fn.loop = false := by
  have key : ∀ (j D : ℕ) (n : String), vmcFacts n j D = true →
      ∃ fn : Fn, coreProgram.find? n = some fn ∧ fn.params = [.n 0, .n 1] ∧ Stmt.pureList [] fn.body = true ∧
        Stmt.pureList [n] fn.body = true ∧
        Stmt.atomsAll (loadInBQ [(0, 2 ^ (D + 2)), (1, 2 ^ D)]) fn.body = true ∧ fn.loop = false := by
    intro j D n h
    unfold vmcFacts at h
    split at h
    · rename_i fn hj
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true] at h
      obtain ⟨⟨⟨⟨⟨hn, hp⟩, h0⟩, h1⟩, hL⟩, hl⟩ := h
      subst hn
      exact ⟨fn, coreProgram_find?_at hj, hp, h0, h1, hL, hl⟩
    · exact absurd h Bool.false_ne_true
  intro p hp
  simp only [merkleCapNames, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact key _ _ _ vmc_facts_0
  · exact key _ _ _ vmc_facts_1
  · exact key _ _ _ vmc_facts_2
  · exact key _ _ _ vmc_facts_3
  · exact key _ _ _ vmc_facts_4
  · exact key _ _ _ vmc_facts_5
  · exact key _ _ _ vmc_facts_6

theorem vmc_free : ∀ p ∈ merkleCapNames, NoWitG p.1 ∧ ExactFreeG p.1 := by
  intro p hp
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
  have hl : merkleCapNames.length = 7 := rfl
  have hf := verify_merkle_cap_free i (by omega)
  rwa [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map] at hf

variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}

/-- **`verify_merkle_cap__L{D}` completes placed**: on `[cap, flags]`, the region covering the cap's
`2^(D+2)` cells and the flags' `2^D`, where its meaning holds, at every position, ending at its
cursor, popping nothing, exact. -/
theorem vmcA (kd : ℕ) : ∀ p ∈ merkleCapNames, ∀ (icap iflg : ℕ) (rets : List E) (R : ℕ → Prop),
    (∀ i < 2 ^ (p.2 + 2), R (icap + i)) → (∀ i < 2 ^ p.2, R (iflg + i)) → ∀ fp c,
    CallAtA fs al cert kd p.1 [ptrAt icap, ptrAt iflg] rets R (fun _ => False) (fun _ => True)
      (fun rd => MeaningVerifyMerkleCap p.2 rd [ptrAt icap, ptrAt iflg] rets) FreePost (fs p.1) fp c c := by
  intro p hp icap iflg rets R hRc hRf fp c
  obtain ⟨fn, hfind, hpar, h0, h1, hL, hlp⟩ := vmc_fn p hp
  obtain ⟨hw, hx⟩ := vmc_free p hp
  have hloop : coreProgram.loop p.1 = false := by rw [Program.loop_of_find? hfind, hlp]
  have hS : coreProgram.PureIn [p.1] := by
    intro g hg fn' hf'
    rw [List.mem_singleton] at hg
    subst hg
    rw [hfind, Option.some.injEq] at hf'
    subst hf'
    exact h1
  have hnc : ∀ fn' σ es vs, coreProgram.find? p.1 = some fn' → walk σ fn'.body = .ret es vs → calls es = [] := by
    intro fn' σ es vs hf hw'
    rw [hfind, Option.some.injEq] at hf
    subst hf
    exact calls_nil_of_pure h0 hw'
  have h0' : CallCompletes0 kd p.1 [ptrAt icap, ptrAt iflg] rets
      (fun rd => MeaningVerifyMerkleCap p.2 rd [ptrAt icap, ptrAt iflg] rets) FreePost := by
    intro rd _ hm
    obtain ⟨t, hn, hv, hb⟩ := Program.Rel.tree coreProgram_wf
      ((verify_merkle_cap_holds p hp rd [ptrAt icap, ptrAt iflg] rets).mpr hm)
    exact ⟨t, hn, hv, hb, pops_nil_of_noWitness hw hv hn rd, every_exact_of_free hx hv hn rd⟩
  refine callAtA_of_callCompletes0 hS (List.mem_singleton_self _) le_rfl h0' fun rd t _ _ hn hv hb _ => ?_
  obtain ⟨hB, hE⟩ := block_endA_leaf (fs := fs) (al := al) hS (List.mem_singleton_self _) hloop hnc hn hv hb c
  obtain ⟨hlo, hhi⟩ := loadsR_hintsR_of_atomsAll (ps := [(0, 2 ^ (p.2 + 2)), (1, 2 ^ p.2)]) R hfind
    (by rw [hpar]; rfl) hL (fun σ es vs hw' => calls_nil_of_pure h0 hw')
    (by simp) (by simp) hn hv
  refine ⟨hB, hE, loadsR_mono' (fun i hi => ?_) t hlo, hhi⟩
  obtain ⟨q, hq, b, hb, h1, h2⟩ := hi
  have shift : ∀ a, addressOfIndex a = addressOfIndex b → addressOfIndex i = addressOfIndex (a + (i - b)) :=
    fun a he => by rw [← gpow_add', he, gpow_add', show b + (i - b) = i by omega]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · simp only [List.getD_cons_zero] at hb
    exact ⟨icap + (i - b), shift icap (ptrAt_inj hb), hRc (i - b) (by simp at h2; omega)⟩
  · simp only [List.getD_cons_succ, List.getD_cons_zero] at hb
    exact ⟨iflg + (i - b), shift iflg (ptrAt_inj hb), hRf (i - b) (by simp at h2; omega)⟩

end
end LeanVM.Guest.B1.VsC
