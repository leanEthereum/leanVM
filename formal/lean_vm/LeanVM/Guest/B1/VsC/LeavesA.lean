/-
  LeanVM.Guest.B1.VsC.LeavesA

  `verify_sub`'s straight leaf callees placed: no words of their own, their loads and heap hints in
  their arguments' arrays.
-/

module

public import LeanVM.Guest.Complete.TransferA
public import LeanVM.Guest.B1.VsC.LeafEnd
public import LeanVM.Guest.B1.VsC.TableSizeC
public import LeanVM.Guest.B1.VsC.SuffixesC
public import LeanVM.Guest.B1.VsC.TablePointC
public import LeanVM.Guest.B1.VsC.PackedMessageC
public import LeanVM.Guest.B1.VsC.OpeningMessageC
public import LeanVM.Guest.B1.VsC.RelC
public import LeanVM.Guest.B1.VsC.AsgA
import LeanVM.Guest.CoreRef

/-!
# Straight leaves, placed

`callCompletesA_leafIn`: a straight leaf (`retOf`), not a loop helper, placing nothing and calling
nothing, whose loads and heap hints go through its arguments' arrays `ps` within their lengths
(`loadHintInB`, all one kernel check `leafPlaceOk`), completes aligned from its `CallCompletes0`:
block its frame, ending at its cursor, in any region holding the arrays' cells (`ArrIn`), with no
data and no words of its own.

Placed this way, each at every specialization `verify_sub` dispatches to: `table_size_completeA`
(its `bits` hint writes the caller's array), `chunk_d_completeA`, `squeeze_point_from_completeA`,
`opening_message_L1_completeA`, `state_ends_completeA`, `one_plus_suffixes_completeA`,
`packed_message_completeA`, `table_point_completeA`; and `assert_small_g_power_completeA` from
`asg_placed`.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

open LeanVM.Guest.B1.Link LeanVM.Guest.B1.Fs LeanVM.Guest.B1.Fwd
open LeanVM.Guest.Value.Keccak

@[expose] public section

/-! ## The generic placement -/

/-- An array's `n` cells from pointer `p` are in `R`. -/
def ArrIn (R : ℕ → Prop) (p : E) (n : ℕ) : Prop :=
  ∀ off < n, ∃ i, p.limb 0 * addressOfIndex off = addressOfIndex i ∧ R i

/-- A heap destination inside an array of `ps`, or none. -/
def destInB (ps : List (ℕ × ℕ)) : Option (V × ℕ × ℕ) → Bool
  | none => true
  | some (p, off, len) => ps.any fun q => p == .n q.1 && decide (off + len ≤ q.2)

/-- A load through an array of `ps` within its length; any other atom's heap hint into one. -/
def loadHintInB (ps : List (ℕ × ℕ)) : Atom → Bool
  | .load _ p k => ps.any fun q => p == .n q.1 && decide (k < q.2)
  | a => destInB ps (atomHeapDest? a)

/-- **What the kernel checks of a straight leaf to place it.** -/
def leafPlaceOk (f : String) (fn : Fn) (n : ℕ) (ps : List (ℕ × ℕ)) : Bool :=
  (retOf fn.body).isSome && !fn.loop && Stmt.pureList [f] fn.body && (atomsOf fn.body).all (loadHintInB ps) &&
    decide (fn.params = (List.range n).map V.n) && ps.all fun q => decide (q.1 < n)

theorem hintAddrs_atom_eq (σ : Val) (a : Atom) : Ev.hintAddrs σ (.atom a) =
    match atomHeapDest? a with
    | some (p, off, len) => (List.range len).map fun k => (σ p).limb 0 * addressOfIndex (off + k)
    | none => [] := by
  cases a <;> rfl

/-- **A straight leaf reading and hinting into its arguments' arrays** loads and hints in `R`. -/
theorem loadsR_hintsR_of_loadHintIn {f : String} {fn : Fn} {ps : List (ℕ × ℕ)} {args rets : List E}
    {rd : Reader} {t : Tree} (R : ℕ → Prop) (hfind : coreProgram.find? f = some fn)
    (hparams : fn.params = (List.range args.length).map V.n)
    (hL : (atomsOf fn.body).all (loadHintInB ps) = true) (hr : (retOf fn.body).isSome = true)
    (hargs : ∀ q ∈ ps, q.1 < args.length) (hptr : ∀ q ∈ ps, ArrIn R (args.getD q.1 0) q.2)
    (hn : t.name = f) (hv : t.Valid coreProgram rd args rets) :
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
    have hok : ∀ a ∈ atomsOf ss, loadHintInB ps a = true := fun a ha =>
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
        simp only [loadHintInB, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hk
        obtain ⟨q, hqm, rfl, hoff⟩ := hk
        obtain ⟨i, hi, hR⟩ := hptr q hqm off hoff
        exact ⟨i, by rw [← hA, hσ _ (hargs q hqm)]; exact hi, hR⟩
      | _ => simp [Ev.loadAddr?] at hA
    · rw [Tree.HintsR, hev]
      refine ⟨fun A hA => ?_, by rw [Tree.HintsRKids]; trivial⟩
      simp only [heapHintAddrs, List.flatMap_map, List.mem_flatMap] at hA
      obtain ⟨a, ha, hA⟩ := hA
      have hk := hok a ha
      rw [hintAddrs_atom_eq] at hA
      have hk' : destInB ps (atomHeapDest? a) = true := by
        cases a with
        | load d p off => rfl
        | _ => exact hk
      cases hd : atomHeapDest? a with
      | none => rw [hd] at hA; simp at hA
      | some x =>
        obtain ⟨p, off, len⟩ := x
        rw [hd] at hA hk'
        dsimp only at hA
        simp only [destInB, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hk'
        obtain ⟨q, hqm, rfl, hle⟩ := hk'
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hA
        rw [List.mem_range] at hj
        obtain ⟨i, hi, hR⟩ := hptr q hqm (off + j) (by omega)
        exact ⟨i, by rw [hσ _ (hargs q hqm)]; exact hi, hR⟩

/-- **A straight leaf with no words of its own completes placed**: block its frame, ending at its
cursor, its arrays' cells in the region. -/
theorem leafAtA_leafIn {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k : ℕ}
    {f : String} {fn : Fn} {ps : List (ℕ × ℕ)} {args rets : List E} {R : ℕ → Prop} {Pre : Reader → Prop}
    {Post : Reader → Tree → Prop} (hfind : coreProgram.find? f = some fn)
    (hck : leafPlaceOk f fn args.length ps = true) (hptr : ∀ q ∈ ps, ArrIn R (args.getD q.1 0) q.2)
    (h : CallCompletes0 k f args rets Pre Post) :
    LeafAtA fs al cert k f args rets R (fun _ => True) Pre Post := by
  simp only [leafPlaceOk, Bool.and_eq_true] at hck
  obtain ⟨⟨⟨⟨⟨hr, hlp⟩, hpure⟩, hL⟩, hparams⟩, hargs⟩ := hck
  have hlp' : coreProgram.loop f = false := by rw [Program.loop_of_find? hfind]; simpa using hlp
  have hS : coreProgram.PureIn [f] := fun g hg fn' hf' => by
    rw [List.mem_singleton] at hg
    subst hg
    rw [hfind] at hf'
    cases hf'
    exact hpure
  have hparams' : fn.params = (List.range args.length).map V.n := of_decide_eq_true hparams
  have hargs' : ∀ q ∈ ps, q.1 < args.length := fun q hq => of_decide_eq_true (List.all_eq_true.mp hargs q hq)
  obtain ⟨vs0, hr'⟩ := Option.isSome_iff_exists.mp hr
  obtain ⟨ss, hbody, hss⟩ := retOf_spec hr'
  refine leafAtA_of_callCompletes0_leaf hS List.mem_cons_self hlp' (fun fn' σ es vs hfn hw => ?_) h
    fun rd t _ _ hn hv _ _ => loadsR_hintsR_of_loadHintIn R hfind hparams' hL hr hargs' hptr hn hv
  rw [hfind] at hfn
  cases hfn
  have hb' : fn.body = (atomsOf ss).map Stmt.atom ++ [.ret vs0] := by rw [hbody, ← eq_map_atomsOf hss]
  rw [hb', walk_atoms] at hw
  cases hw
  exact calls_atoms _

/-- `leafAtA_leafIn`, its end forgotten. -/
theorem callCompletesA_leafIn {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k : ℕ}
    {f : String} {fn : Fn} {ps : List (ℕ × ℕ)} {args rets : List E} {R : ℕ → Prop} {Pre : Reader → Prop}
    {Post : Reader → Tree → Prop} (hfind : coreProgram.find? f = some fn)
    (hck : leafPlaceOk f fn args.length ps = true) (hptr : ∀ q ∈ ps, ArrIn R (args.getD q.1 0) q.2)
    (h : CallCompletes0 k f args rets Pre Post) :
    CallCompletesA fs al cert k f args rets R (fun _ _ _ => False) (fun _ => True) Pre Post :=
  (leafAtA_leafIn (fs := fs) (al := al) (cert := cert) hfind hck hptr h).completesA

/-! ## The kernel's checks per specialization -/

/-- `chunk_d`'s names. -/
def cdNames : List String :=
  ["chunk_d__L19", "chunk_d__L20", "chunk_d__L21", "chunk_d__L22", "chunk_d__L23", "chunk_d__L24"]

set_option maxRecDepth 100000 in
theorem ts_place : ∀ h ≤ 24, ∃ fn, coreProgram.find? (tsNames.getD h "") = some fn ∧
    leafPlaceOk (tsNames.getD h "") fn 2 [(1, h + 1)] = true := by
  intro h hh
  interval_cases h
  · exact ⟨_, coreProgram_find?_at (j := idx% «table_size__L0») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «table_size__L1») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «table_size__L2») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «table_size__L3») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «table_size__L4») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «table_size__L5») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «table_size__L6») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «table_size__L7») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «table_size__L8») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «table_size__L9») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «table_size__L10») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «table_size__L11») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «table_size__L12») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «table_size__L13») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «table_size__L14») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «table_size__L15») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «table_size__L16») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «table_size__L17») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «table_size__L18») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «table_size__L19») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «table_size__L20») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «table_size__L21») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «table_size__L22») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «table_size__L23») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «table_size__L24») rfl, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem tp_place : ∀ h ≤ 24, ∃ fn, coreProgram.find? (tpNames.getD h "") = some fn ∧
    leafPlaceOk (tpNames.getD h "") fn 4 [(1, h), (2, h), (3, h + 1)] = true := by
  intro h hh
  interval_cases h
  · exact ⟨_, coreProgram_find?_at (j := idx% «table_point__L0») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «table_point__L1») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «table_point__L2») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «table_point__L3») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «table_point__L4») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «table_point__L5») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «table_point__L6») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «table_point__L7») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «table_point__L8») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «table_point__L9») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «table_point__L10») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «table_point__L11») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «table_point__L12») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «table_point__L13») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «table_point__L14») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «table_point__L15») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «table_point__L16») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «table_point__L17») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «table_point__L18») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «table_point__L19») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «table_point__L20») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «table_point__L21») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «table_point__L22») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «table_point__L23») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «table_point__L24») rfl, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem ops_place : ∀ n ≤ 40, ∃ fn, coreProgram.find? (opsNames.getD n "") = some fn ∧
    leafPlaceOk (opsNames.getD n "") fn 2 [(0, n + 1), (1, n)] = true := by
  intro n hn
  interval_cases n
  · exact ⟨_, coreProgram_find?_at (j := idx% «one_plus_suffixes__L0») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «one_plus_suffixes__L1») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «one_plus_suffixes__L2») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «one_plus_suffixes__L3») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «one_plus_suffixes__L4») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «one_plus_suffixes__L5») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «one_plus_suffixes__L6») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «one_plus_suffixes__L7») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «one_plus_suffixes__L8») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «one_plus_suffixes__L9») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «one_plus_suffixes__L10») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «one_plus_suffixes__L11») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «one_plus_suffixes__L12») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «one_plus_suffixes__L13») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «one_plus_suffixes__L14») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «one_plus_suffixes__L15») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «one_plus_suffixes__L16») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «one_plus_suffixes__L17») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «one_plus_suffixes__L18») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «one_plus_suffixes__L19») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «one_plus_suffixes__L20») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «one_plus_suffixes__L21») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «one_plus_suffixes__L22») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «one_plus_suffixes__L23») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «one_plus_suffixes__L24») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «one_plus_suffixes__L25») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «one_plus_suffixes__L26») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «one_plus_suffixes__L27») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «one_plus_suffixes__L28») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «one_plus_suffixes__L29») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «one_plus_suffixes__L30») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «one_plus_suffixes__L31») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «one_plus_suffixes__L32») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «one_plus_suffixes__L33») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «one_plus_suffixes__L34») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «one_plus_suffixes__L35») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «one_plus_suffixes__L36») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «one_plus_suffixes__L37») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «one_plus_suffixes__L38») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «one_plus_suffixes__L39») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «one_plus_suffixes__L40») rfl, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem se_place : ∀ w, 19 ≤ w → w ≤ 24 → ∃ fn, coreProgram.find? (seNames.getD (w - 19) "") = some fn ∧
    leafPlaceOk (seNames.getD (w - 19) "") fn 2 [(0, w), (1, w)] = true := by
  intro w hw hw'
  interval_cases w
  · exact ⟨_, coreProgram_find?_at (j := idx% «state_ends__L19») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «state_ends__L20») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «state_ends__L21») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «state_ends__L22») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «state_ends__L23») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «state_ends__L24») rfl, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem spf_place : ∀ n ∈ spfDeployed, ∃ fn, coreProgram.find? (spfName n) = some fn ∧
    leafPlaceOk (spfName n) fn 7 [(6, n)] = true := by
  intro n hn
  simp only [spfDeployed, List.mem_map, List.mem_range] at hn
  obtain ⟨i, hi, rfl⟩ := hn
  interval_cases i
  · exact ⟨_, coreProgram_find?_at (j := idx% «squeeze_point_from__L6») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «squeeze_point_from__L7») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «squeeze_point_from__L8») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «squeeze_point_from__L9») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «squeeze_point_from__L10») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «squeeze_point_from__L11») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «squeeze_point_from__L12») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «squeeze_point_from__L13») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «squeeze_point_from__L14») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «squeeze_point_from__L15») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «squeeze_point_from__L16») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «squeeze_point_from__L17») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «squeeze_point_from__L18») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «squeeze_point_from__L19») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «squeeze_point_from__L20») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «squeeze_point_from__L21») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «squeeze_point_from__L22») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «squeeze_point_from__L23») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «squeeze_point_from__L24») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «squeeze_point_from__L25») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «squeeze_point_from__L26») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «squeeze_point_from__L27») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «squeeze_point_from__L28») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «squeeze_point_from__L29») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «squeeze_point_from__L30») rfl, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem cd_place : ∀ w, 19 ≤ w → w ≤ 24 → ∃ fn, coreProgram.find? (cdNames.getD (w - 19) "") = some fn ∧
    leafPlaceOk (cdNames.getD (w - 19) "") fn 0 [] = true := by
  intro w hw hw'
  interval_cases w
  · exact ⟨_, coreProgram_find?_at (j := idx% «chunk_d__L19») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «chunk_d__L20») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «chunk_d__L21») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «chunk_d__L22») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «chunk_d__L23») rfl, by decide +kernel⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «chunk_d__L24») rfl, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem om1_place : ∃ fn, coreProgram.find? (omName (1, 1)) = some fn ∧
    leafPlaceOk (omName (1, 1)) fn 7 [(5, 2), (6, 1)] = true :=
  ⟨_, coreProgram_find?_at (j := idx% «opening_message__L1_L1») rfl, by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem pm_place : ∃ fn, coreProgram.find? "packed_message__L144" = some fn ∧
    leafPlaceOk "packed_message__L144" fn 6 [(5, 144)] = true :=
  ⟨_, coreProgram_find?_at (j := idx% «packed_message__L144») rfl, by decide +kernel⟩

/-! ## The callees placed -/

section
variable (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ)

/-- **`table_size__L{h}` completes placed**, its `bits` array (which its hint writes) in `R`. -/
theorem table_size_leafA (kd : ℕ) {h : ℕ} (hh : h ≤ 24) {Rn : ℕ} {bits : E} (hR : Rn ≤ 2 ^ h)
    {R : ℕ → Prop} (hb : ArrIn R bits (h + 1)) :
    LeafAtA fs al cert kd (tsNames.getD h "") [eOfNat Rn, bits] [gen ^ Rn, tsLeadW Rn h, tsRestW Rn h] R
      (fun _ => True) (fun rd ↦ ReadsAt rd bits (tsBitsW Rn h)) PostQuiet := by
  obtain ⟨fn, hf, hck⟩ := ts_place h hh
  refine leafAtA_leafIn hf hck (fun q hq => ?_) (table_size_complete kd h hh Rn bits hR)
  simp only [List.mem_singleton] at hq
  subst hq
  exact hb

theorem table_size_completeA (kd : ℕ) {h : ℕ} (hh : h ≤ 24) {Rn : ℕ} {bits : E} (hR : Rn ≤ 2 ^ h)
    {R : ℕ → Prop} (hb : ArrIn R bits (h + 1)) :
    CallCompletesA fs al cert kd (tsNames.getD h "") [eOfNat Rn, bits] [gen ^ Rn, tsLeadW Rn h, tsRestW Rn h] R
      (fun _ _ _ => False) (fun _ => True) (fun rd ↦ ReadsAt rd bits (tsBitsW Rn h)) PostQuiet :=
  (table_size_leafA fs al cert kd hh hR hb).completesA

/-- **`chunk_d__L{w}` completes placed**, touching no memory. -/
theorem chunk_d_leafA (k : ℕ) (Pre : Reader → Prop) {w : ℕ} (hw : 19 ≤ w) (hw' : w ≤ 24) (R : ℕ → Prop) :
    LeafAtA fs al cert k (cdNames.getD (w - 19) "") [] [gen ^ chunkCount w] R (fun _ => True) Pre PostQuiet := by
  obtain ⟨fn, hf, hck⟩ := cd_place w hw hw'
  refine leafAtA_leafIn hf hck (fun q hq => by simp at hq) ?_
  have h := chunk_d_complete k Pre
  interval_cases w
  exacts [h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2]

theorem chunk_d_completeA (k : ℕ) (Pre : Reader → Prop) {w : ℕ} (hw : 19 ≤ w) (hw' : w ≤ 24) (R : ℕ → Prop) :
    CallCompletesA fs al cert k (cdNames.getD (w - 19) "") [] [gen ^ chunkCount w] R (fun _ _ _ => False)
      (fun _ => True) Pre PostQuiet :=
  (chunk_d_leafA fs al cert k Pre hw hw' R).completesA

/-- **`squeeze_point_from__L{n}` completes placed**, its `point` array in `R`. -/
theorem squeeze_point_from_leafA (kd : ℕ) {n : ℕ} (hn : n ∈ spfDeployed) (f0 f1 f2 f3 f4 first point : E)
    {R : ℕ → Prop} (hp : ArrIn R point n) :
    LeafAtA fs al cert kd (spfName n) [f0, f1, f2, f3, f4, first, point]
      ((⟨[f0, f1, f2, f3, f4], []⟩ : Fs).squeezeN (n - 1)).2.cap R (fun _ => True)
      (fun rd ↦ ReadsAt rd point (first :: ((⟨[f0, f1, f2, f3, f4], []⟩ : Fs).squeezeN (n - 1)).1))
      PostQuiet := by
  obtain ⟨fn, hf, hck⟩ := spf_place n hn
  refine leafAtA_leafIn hf hck (fun q hq => ?_)
    (squeeze_point_from_complete kd n hn f0 f1 f2 f3 f4 first point)
  simp only [List.mem_singleton] at hq
  subst hq
  exact hp

/-- **`opening_message__L1_L1` completes placed**, its `cur` and `out` arrays in `R`. -/
theorem opening_message_L1_leafA (kd : ℕ) (f0 f1 f2 f3 f4 cur out nn : E) (xs : List E) (hxs : xs.length = 1)
    {R : ℕ → Prop} (hc : ArrIn R cur 2) (ho : ArrIn R out 1) :
    LeafAtA fs al cert kd (omName (1, 1)) [f0, f1, f2, f3, f4, cur, out] (omRets f0 f1 f2 f3 f4 cur xs nn) R
      (fun _ => True) (fun rd ↦ ReadsAt rd cur (xs ++ [nn]) ∧ ReadsAt rd out xs)
      PostQuiet := by
  obtain ⟨fn, hf, hck⟩ := om1_place
  refine leafAtA_leafIn hf hck (fun q hq => ?_)
    (opening_message_L1_complete kd f0 f1 f2 f3 f4 cur out nn xs hxs)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · exact hc
  · exact ho

/-- **`state_ends__L{w}` completes placed**, its two arrays in `R`. -/
theorem state_ends_leafA (kd : ℕ) {w : ℕ} (hw : 19 ≤ w) (hw' : w ≤ 24) (zeta cbits : E) (zs cs : List E)
    (hz : zs.length = w) (hc : cs.length = w) {R : ℕ → Prop} (hzr : ArrIn R zeta w) (hcr : ArrIn R cbits w) :
    LeafAtA fs al cert kd (seNames.getD (w - 19) "") [zeta, cbits] [prodE (zs.map (1 + ·)), endsProd cs zs] R
      (fun _ => True) (fun rd ↦ ReadsAt rd zeta zs ∧ ReadsAt rd cbits cs) PostQuiet := by
  obtain ⟨fn, hf, hck⟩ := se_place w hw hw'
  refine leafAtA_leafIn hf hck (fun q hq => ?_) (state_ends_complete kd w hw hw' zeta cbits zs cs hz hc)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · exact hzr
  · exact hcr

/-- **`one_plus_suffixes__L{n}` completes placed**, its two arrays in `R`. -/
theorem one_plus_suffixes_leafA (kd : ℕ) {n : ℕ} (hn : n ≤ 40) (chain a : E) (as : List E) (hl : as.length = n)
    {R : ℕ → Prop} (hcr : ArrIn R chain (n + 1)) (har : ArrIn R a n) :
    LeafAtA fs al cert kd (opsNames.getD n "") [chain, a] [0] R (fun _ => True)
      (fun rd ↦ ReadsAt rd a as ∧ ReadsAt rd chain ((List.range (n + 1)).map (belowE as))) PostQuiet := by
  obtain ⟨fn, hf, hck⟩ := ops_place n hn
  refine leafAtA_leafIn hf hck (fun q hq => ?_) (one_plus_suffixes_complete kd n hn chain a as hl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · exact hcr
  · exact har

/-- **`packed_message__L144` completes placed**, its message array in `R`. -/
theorem packed_message_leafA (kd : ℕ) (f0 f1 f2 f3 f4 msg : E) (xs : List E) (hxs : xs.length = 144)
    {R : ℕ → Prop} (hm : ArrIn R msg 144) :
    LeafAtA fs al cert kd "packed_message__L144" [f0, f1, f2, f3, f4, msg]
      ((Fs.squeeze ⟨pkAbsorb 18 xs [f0, f1, f2, f3, f4], []⟩).1 ::
        (Fs.squeeze ⟨pkAbsorb 18 xs [f0, f1, f2, f3, f4], []⟩).2.cap) R (fun _ => True)
      (fun rd ↦ ReadsAt rd msg xs) PostQuiet := by
  obtain ⟨fn, hf, hck⟩ := pm_place
  refine leafAtA_leafIn hf hck (fun q hq => ?_) (packed_message_complete kd f0 f1 f2 f3 f4 msg xs hxs)
  simp only [List.mem_singleton] at hq
  subst hq
  exact hm

/-- **`table_point__L{h}` completes placed**, its three arrays in `R`. -/
theorem table_point_leafA (kd : ℕ) {h : ℕ} (hh : h ≤ 24) (theta tau chi bits top : E) (ts xs cs : List E)
    (hts : ts.length = h) (hxs : xs.length = h) (hcs : cs.length = h) {R : ℕ → Prop} (htr : ArrIn R tau h)
    (hxr : ArrIn R chi h) (hbr : ArrIn R bits (h + 1)) :
    LeafAtA fs al cert kd (tpNames.getD h "") [theta, tau, chi, bits]
      [theta * tpTotalG ts xs cs top h, 1 + (1 + top) * tpPad cs xs, tpFullAt ts xs h] R (fun _ => True) (fun rd ↦ ReadsAt rd tau ts ∧ ReadsAt rd chi xs ∧ ReadsAt rd bits (cs ++ [top])) PostQuiet := by
  obtain ⟨fn, hf, hck⟩ := tp_place h hh
  refine leafAtA_leafIn hf hck (fun q hq => ?_)
    (table_point_complete kd h hh theta tau chi bits top ts xs cs hts hxs hcs)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact htr
  · exact hxr
  · exact hbr

/-- **`assert_small_g_power` completes placed** on `g^e`, `e < 2^36`, the exponent table's nibble
shares at `q` in `R` (`asg_placed`). -/
theorem assert_small_g_power_completeA {k : ℕ} (hk : 4 ≤ k) {e : ℕ} (he : e < 2 ^ 36) {q : E} {R : ℕ → Prop}
    (hR : ∀ t < 144, ∃ m, q.limb 0 * addressOfIndex (34 + t) = addressOfIndex m ∧ R m) :
    CallCompletesA fs al cert k "assert_small_g_power" [gen ^ e, q] [] R (fun _ _ _ => False) (fun _ => True)
      (fun rd => ExpTables rd q) PostQuiet :=
  ⟨fs "assert_small_g_power", fun fp c _ => ⟨c, asg_placed hk he hR fp c⟩⟩

theorem assert_small_g_power_leafA {k : ℕ} (hk : 4 ≤ k) {e : ℕ} (he : e < 2 ^ 36) {q : E} {R : ℕ → Prop}
    (hR : ∀ t < 144, ∃ m, q.limb 0 * addressOfIndex (34 + t) = addressOfIndex m ∧ R m) :
    LeafAtA fs al cert k "assert_small_g_power" [gen ^ e, q] [] R (fun _ => True) (fun rd => ExpTables rd q)
      PostQuiet :=
  fun fp c _ => asg_placed hk he hR fp c

end

end
end LeanVM.Guest.B1.VsC
