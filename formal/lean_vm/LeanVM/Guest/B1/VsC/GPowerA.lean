/-
  LeanVM.Guest.B1.VsC.GPowerA

  `g_power_of_word` completes placed: a straight leaf touching no memory.
-/

module

public import LeanVM.Guest.B1.VsC.GPowerC
public import LeanVM.Guest.Complete.TransferA
public import LeanVM.Guest.B1.VsC.LeafEnd

/-!
# Placed leaves touching no memory

`callCompletes0_leaf_pinned`: `callCompletes_leaf_pinned` with no words of its own
(`CallCompletes0`). `callCompletesA_of_noMem`: a straight leaf with no load and no hint into the
heap (`noMemB`, by the kernel) completes placed at every position from its `CallCompletes0`: block
its frame, ending at its cursor, in any region. `g_power_of_word_completeA`.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- **`callCompletes_leaf_pinned` with no words of its own.** -/
theorem callCompletes0_leaf_pinned {k : ℕ} {name : String} {fn : Fn} {args rets : List E}
    {Pre : Reader → Prop} (hfind : coreProgram.find? name = some fn)
    (hck : ((retOf fn.body).isSome && (atomsOf fn.body).all atomQuiet) = true)
    (hrel : ∀ rd, LowDef k rd → Pre rd → coreProgram.Rel rd name args rets)
    (hpin : ∀ rd σ, LowDef k rd → Pre rd → fn.params.map σ = args →
      (∀ a, Stmt.atom a ∈ fn.body → a.Holds rd σ) → ∀ a, Stmt.atom a ∈ fn.body → a.Exact rd σ) :
    CallCompletes0 k name args rets Pre PostQuiet := by
  simp only [Bool.and_eq_true] at hck
  obtain ⟨hr, hh⟩ := hck
  obtain ⟨vs, hr⟩ := Option.isSome_iff_exists.mp hr
  obtain ⟨ss, hbody, hss⟩ := retOf_spec hr
  have hmem : ∀ a, Stmt.atom a ∈ ss → Stmt.atom a ∈ fn.body := fun a ha => by
    rw [hbody]; exact List.mem_append_left _ ha
  have hq : (atomsOf ss).all atomQuiet = true := List.all_eq_true.mpr fun a ha =>
    List.all_eq_true.mp hh a (mem_atomsOf' (hmem a (mem_of_mem_atomsOf ha)))
  let P : Reader → Val → Prop := fun rd σ =>
    fn.params.map σ = args ∧ Stmt.HoldsList (coreProgram.Rel rd) rd σ fn.body False (fun rs => rs = rets)
  refine callCompletes0_straightRd (fun rd => Classical.epsilon (P rd)) hfind hbody hss hq
    fun rd hl hP => ?_
  have hspec := Classical.epsilon_spec (p := P rd) ((rel_iff_sem hfind _ _).mp (hrel rd hl hP))
  generalize Classical.epsilon (P rd) = σ at hspec ⊢
  obtain ⟨hp, hH⟩ := hspec
  rw [hbody, holdsList_append, holdsList_atoms hss] at hH
  obtain ⟨hA, hret⟩ := hH
  simp only [Stmt.HoldsList, Stmt.Holds] at hret
  have hA' : ∀ a, Stmt.atom a ∈ fn.body → a.Holds rd σ := fun a ha => by
    rw [hbody] at ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hA a ha
    · simp at ha
  exact ⟨hp, hret, fun a ha => ⟨hA a ha, hpin rd σ hl hP hp hA' a (hmem a ha)⟩⟩

/-- An atom touching no memory: no load, no hint into the heap. -/
def noMemB : Atom → Bool
  | .load .. => false
  | .hint h => ((hintDest? h).bind destHeap?).isNone
  | _ => true

/-- **A straight leaf touching no memory loads and hints in any region.** -/
theorem loadsR_hintsR_of_noMem {f : String} {fn : Fn} {args rets : List E} {rd : Reader} {t : Tree}
    (R : ℕ → Prop) (hfind : coreProgram.find? f = some fn) (hL : (atomsOf fn.body).all noMemB = true)
    (hr : (retOf fn.body).isSome = true) (hn : t.name = f) (hv : t.Valid coreProgram rd args rets) :
    t.LoadsR coreProgram R ∧ t.HintsR coreProgram R := by
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
    have hok : ∀ a ∈ atomsOf ss, noMemB a = true := fun a ha =>
      List.all_eq_true.mp hL a (mem_atomsOf' (by rw [hbody]; exact List.mem_append_left _ (mem_of_mem_atomsOf ha)))
    refine ⟨?_, ?_⟩
    · rw [Tree.LoadsR, hev]
      refine ⟨fun A hA => ?_, by rw [Tree.LoadsRKids]; trivial⟩
      simp only [loadAddrs, List.filterMap_map, List.mem_filterMap, Function.comp] at hA
      obtain ⟨a, ha, hA⟩ := hA
      have hk := hok a ha
      cases a with
      | load d p off => simp [noMemB] at hk
      | _ => simp [Ev.loadAddr?] at hA
    · rw [Tree.HintsR, hev]
      refine ⟨fun A hA => ?_, by rw [Tree.HintsRKids]; trivial⟩
      simp only [heapHintAddrs, List.flatMap_map, List.mem_flatMap] at hA
      obtain ⟨a, ha, hA⟩ := hA
      have hk := hok a ha
      cases a with
      | hint h =>
        simp only [noMemB, Option.isNone_iff_eq_none] at hk
        simp [Ev.hintAddrs, hk] at hA
      | _ => simp [Ev.hintAddrs] at hA

/-- **A straight leaf touching no memory, proved with no words of its own, completes placed**:
block `fs f`, ending at its cursor, in any region. -/
theorem leafAtA_of_noMem {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}
    {S : List String} (hS : coreProgram.PureIn S) {k : ℕ} {f : String} (hf : f ∈ S)
    (hlp : coreProgram.loop f = false) {fn : Fn} {args rets : List E} {R : ℕ → Prop}
    {Pre : Reader → Prop} {Post : Reader → Tree → Prop} (hfind : coreProgram.find? f = some fn)
    (hL : (atomsOf fn.body).all noMemB = true) (hr : (retOf fn.body).isSome = true)
    (h : CallCompletes0 k f args rets Pre Post) :
    LeafAtA fs al cert k f args rets R (fun _ => True) Pre Post := by
  obtain ⟨vs0, hr'⟩ := Option.isSome_iff_exists.mp hr
  obtain ⟨ss, hbody, hss⟩ := retOf_spec hr'
  refine leafAtA_of_callCompletes0_leaf hS hf hlp (fun fn' σ es vs hfn hw => ?_) h
    fun rd t _ _ hn hv _ _ => loadsR_hintsR_of_noMem R hfind hL hr hn hv
  rw [hfind] at hfn
  cases hfn
  have hb' : fn.body = (atomsOf ss).map Stmt.atom ++ [.ret vs0] := by rw [hbody, ← eq_map_atomsOf hss]
  have hw' : walk σ fn.body = .ret ((atomsOf ss).map Ev.atom) vs0 := by rw [hb']; exact walk_atoms _ _ _
  rw [hw'] at hw
  cases hw
  exact calls_atoms _

/-- `leafAtA_of_noMem`, its end forgotten. -/
theorem callCompletesA_of_noMem {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}
    {S : List String} (hS : coreProgram.PureIn S) {k : ℕ} {f : String} (hf : f ∈ S)
    (hlp : coreProgram.loop f = false) {fn : Fn} {args rets : List E} {R : ℕ → Prop}
    {Pre : Reader → Prop} {Post : Reader → Tree → Prop} (hfind : coreProgram.find? f = some fn)
    (hL : (atomsOf fn.body).all noMemB = true) (hr : (retOf fn.body).isSome = true)
    (h : CallCompletes0 k f args rets Pre Post) :
    CallCompletesA fs al cert k f args rets R (fun _ _ _ => False) (fun _ => True) Pre Post :=
  (leafAtA_of_noMem (al := al) (cert := cert) (fs := fs) hS hf hlp hfind hL hr h).completesA

/-! ## `g_power_of_word` -/

theorem g_power_of_word_pureIn : coreProgram.PureIn ["g_power_of_word"] := by
  intro g hg fn hf
  simp only [List.mem_singleton] at hg
  subst hg
  rw [find_g_power_of_word] at hf
  obtain rfl := Option.some.inj hf
  decide +kernel

theorem g_power_of_word_not_loop : coreProgram.loop "g_power_of_word" = false := by decide +kernel

/-- `g_power_of_word_complete` with no words of its own. -/
theorem g_power_of_word_complete0 (k : ℕ) (Pre : Reader → Prop) {n : ℕ} (hn : n < 64) :
    CallCompletes0 k "g_power_of_word" [eOfNat n] [gen ^ n] Pre PostQuiet :=
  callCompletes0_leaf_pinned find_g_power_of_word (by decide +kernel)
    (fun rd _ _ => (g_power_of_word_holds rd _ _).mpr ⟨n, hn, rfl, rfl⟩)
    (fun _ _ _ _ _ hA => gpow_pinned hA)

/-- **`g_power_of_word` completes placed**: on `E(n)`, `n < 64`, it returns `g^n`, block its frame,
ending at its cursor, touching no memory. -/
theorem g_power_of_word_leafA (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) (k : ℕ)
    (R : ℕ → Prop) (Pre : Reader → Prop) {n : ℕ} (hn : n < 64) :
    LeafAtA fs al cert k "g_power_of_word" [eOfNat n] [gen ^ n] R (fun _ => True) Pre PostQuiet :=
  leafAtA_of_noMem g_power_of_word_pureIn List.mem_cons_self g_power_of_word_not_loop
    find_g_power_of_word (by decide +kernel) (by decide +kernel) (g_power_of_word_complete0 k Pre hn)

/-- `g_power_of_word_leafA`, its end forgotten. -/
theorem g_power_of_word_completeA (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) (k : ℕ)
    (R : ℕ → Prop) (Pre : Reader → Prop) {n : ℕ} (hn : n < 64) :
    CallCompletesA fs al cert k "g_power_of_word" [eOfNat n] [gen ^ n] R (fun _ _ _ => False) (fun _ => True)
      Pre PostQuiet :=
  (g_power_of_word_leafA fs al cert k R Pre hn).completesA

end
end LeanVM.Guest.B1.VsC
