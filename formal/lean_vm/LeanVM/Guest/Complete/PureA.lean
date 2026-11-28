module

public import LeanVM.Guest.Complete.TransferA
public import LeanVM.Guest.Complete.MainA
public import LeanVM.Guest.B1.VsC.Fwd

/-!
# Straight leaves reading their arguments' arrays, placed

A leaf whose body is atoms then a `ret`, every load `load(d, p, off)` through a parameter `p`
with `off` below that array's length (`loadOkB ps`, which also excludes hints: `pureChecks`'
condition), loads only from the arrays its arguments point to (`argRegion args ps`) and writes
no heap hint, on every valid tree (`loadsR_hintsR_of_loadOk`). So a pure such leaf proved with no
words of its own (`CallCompletes0`) completes placed, loading from `argRegion`
(`callCompletesA_of_loadOk`): the transfer `callCompletesA_of_callCompletes0_leaf` asks exactly
its loads and heap hints in the region.
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.VsC

@[expose] public section

/-- The cells of the arrays `ps` (argument index, length) the arguments point to. -/
def argRegion (args : List E) (ps : List (ℕ × ℕ)) (i : ℕ) : Prop :=
  ∃ q ∈ ps, ∃ b, args.getD q.1 0 = ptrAt b ∧ b ≤ i ∧ i < b + q.2

/-- **A straight leaf reading its arguments' arrays loads from them and hints nothing to the heap.** -/
theorem loadsR_hintsR_of_loadOk {f : String} {fn : Fn} {ps : List (ℕ × ℕ)} {args rets : List E}
    {rd : Reader} {t : Tree} (R : ℕ → Prop) (hfind : coreProgram.find? f = some fn)
    (hparams : fn.params = (List.range args.length).map V.n)
    (hL : (atomsOf fn.body).all (loadOkB ps) = true) (hr : (retOf fn.body).isSome = true)
    (hargs : ∀ q ∈ ps, q.1 < args.length) (hptr : ∀ q ∈ ps, ∃ b, args.getD q.1 0 = ptrAt b)
    (hn : t.name = f) (hv : t.Valid coreProgram rd args rets) :
    t.LoadsR coreProgram (argRegion args ps) ∧ t.HintsR coreProgram R := by
  obtain ⟨vs0, hr⟩ := Option.isSome_iff_exists.mp hr
  obtain ⟨ss, hbody, hss⟩ := retOf_spec hr
  cases t with
  | phantom _ _ => exact hv.elim
  | node g σ bufs kids =>
    obtain ⟨fn', hfn, hpar, es, vs, hw, _, _, hk⟩ := hv
    simp only [Tree.name] at hn
    subst hn
    rw [hfind] at hfn
    cases hfn
    have hb' : fn.body = (atomsOf ss).map Stmt.atom ++ [.ret vs0] := by rw [hbody, ← eq_map_atomsOf hss]
    have hw' : walk σ fn.body = .ret ((atomsOf ss).map Ev.atom) vs0 := by rw [hb']; exact walk_atoms _ _ _
    rw [hw'] at hw
    cases hw
    have hev : (Memory.Tree.node g σ bufs kids).events coreProgram = (atomsOf ss).map Ev.atom := by
      simp only [Tree.events, Tree.name, Tree.val, hfind, hw']
    rw [calls_atoms] at hk
    have hkids : kids = [] := by
      cases kids with
      | nil => rfl
      | cons _ _ => simp [Tree.KidsValid] at hk
    subst hkids
    have hok : ∀ a ∈ atomsOf ss, loadOkB ps a = true := fun a ha =>
      List.all_eq_true.mp hL a (mem_atomsOf' (by rw [hbody]; exact List.mem_append_left _ (mem_of_mem_atomsOf ha)))
    have hσ : ∀ j < args.length, σ (.n j) = args.getD j 0 := by
      intro j hj
      have hj' : (((List.range args.length).map V.n).map σ)[j]? = args[j]? := by rw [← hparams, hpar]
      simp [hj] at hj'
      simpa [List.getD_eq_getElem?_getD, hj] using hj'
    refine ⟨?_, ?_⟩
    · rw [Tree.LoadsR, hev]
      refine ⟨fun A hA => ?_, by rw [Tree.LoadsRKids]; trivial⟩
      simp only [loadAddrs, List.filterMap_map, List.mem_filterMap, Function.comp] at hA
      obtain ⟨a, ha, hA⟩ := hA
      have hk := hok a ha
      cases a with
      | load d p off =>
        simp only [Ev.loadAddr?, Option.some.injEq] at hA
        simp only [loadOkB, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hk
        obtain ⟨q, hqm, rfl, hoff⟩ := hk
        obtain ⟨b, hb⟩ := hptr q hqm
        refine ⟨b + off, ?_, q, hqm, b, hb, by omega, by omega⟩
        rw [← hA, hσ _ (hargs q hqm), hb]
        exact Main.addr_ofK b off
      | _ => simp [Ev.loadAddr?] at hA
    · rw [Tree.HintsR, hev]
      refine ⟨fun A hA => ?_, by rw [Tree.HintsRKids]; trivial⟩
      simp only [heapHintAddrs, List.flatMap_map, List.mem_flatMap] at hA
      obtain ⟨a, ha, hA⟩ := hA
      have hk := hok a ha
      cases a with
      | hint _ => simp [loadOkB] at hk
      | _ => simp [Ev.hintAddrs] at hA

/-- **A pure straight leaf reading its arguments' arrays, proved with no words of its own,
completes placed**, loading from those arrays: block `fs f`, ending at its cursor. -/
theorem callCompletesA_of_loadOk {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}
    {S : List String} (hS : coreProgram.PureIn S) {k : ℕ} {f : String} (hf : f ∈ S)
    (hlp : coreProgram.loop f = false) {fn : Fn} {ps : List (ℕ × ℕ)} {args rets : List E}
    {Pre : Reader → Prop} {Post : Reader → Tree → Prop} (hfind : coreProgram.find? f = some fn)
    (hparams : fn.params = (List.range args.length).map V.n)
    (hL : (atomsOf fn.body).all (loadOkB ps) = true) (hr : (retOf fn.body).isSome = true)
    (hargs : ∀ q ∈ ps, q.1 < args.length) (hptr : ∀ q ∈ ps, ∃ b, args.getD q.1 0 = ptrAt b)
    (h : CallCompletes0 k f args rets Pre Post) :
    CallCompletesA fs al cert k f args rets (argRegion args ps) (fun _ _ _ => False) (fun _ => True) Pre Post := by
  obtain ⟨vs0, hr'⟩ := Option.isSome_iff_exists.mp hr
  obtain ⟨ss, hbody, hss⟩ := retOf_spec hr'
  refine callCompletesA_of_callCompletes0_leaf hS hf hlp (fun fn' σ es vs hfn hw => ?_) h
    fun rd t _ _ hn hv _ _ => loadsR_hintsR_of_loadOk _ hfind hparams hL hr hargs hptr hn hv
  rw [hfind] at hfn
  cases hfn
  have hb' : fn.body = (atomsOf ss).map Stmt.atom ++ [.ret vs0] := by rw [hbody, ← eq_map_atomsOf hss]
  have hw' : walk σ fn.body = .ret ((atomsOf ss).map Ev.atom) vs0 := by rw [hb']; exact walk_atoms _ _ _
  rw [hw'] at hw
  cases hw
  exact calls_atoms _

end
end LeanVM.Guest.Complete
