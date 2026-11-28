module

public import LeanVM.Guest.Complete.MainA
public import LeanVM.Guest.Complete.Free
public import LeanVM.Guest.Complete.Call0
public import LeanVM.Guest.B1.VsC.Fwd
public import LeanVM.Guest.Complete.MainFree
import LeanVM.Guest.CoreRef
import LeanVM.Guest.ValRef
import LeanVM.Guest.LitRef
import LeanVM.Guest.Data.Consts
import LeanVM.Guest.Data.ValNames.«exponent_tables»

/-!
# A leaf filling the buffer it returns, placed

A straight leaf whose body allocates one `HeapBuf(n)` at `d` first, then atoms with no hint, no
`frameAddr` and every load through `d` below `n`, and returns `d` (or a copy of it): `leafBufB`,
decided by the kernel. On every valid tree returning `ptrAt c`, its buffer is at `c` (`d`'s value
is the return), so the tree is placed at any frame and cursor `c`, ending at `c + n`, loading only
from its buffer (`callAtA_leafBuf`). Its words are the buffer, `vals`, held from `c`; it claims
the buffer as its data, for later callees' regions.

`exponent_tables_callAtA`: `exponent_tables` at the cursor `c`, its tables `expTabAllWords`.
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.VsC

@[expose] public section

/-- An atom after a leaf's one `HeapBuf(n)` at `d`: no hint, no `frameAddr`, loads through `d`
below `n`. -/
def bufAtomB (d : V) (n : ℕ) : Atom → Bool
  | .load _ p off => p == d && decide (off < n)
  | .hint _ => false
  | .frameAddr .. => false
  | _ => true

/-- **A leaf filling the buffer it returns**: its body `HeapBuf(n)` at `d`, atoms passing
`bufAtomB d n`, `ret [r]` with `r` `d` or a copy of it. -/
def leafBufB (d : V) (n : ℕ) (B : List Stmt) : Bool :=
  match retOf B with
  | some [r] =>
    match atomsOf B with
    | .hint (.alloc d' n') :: as => d' == d && n' == n && as.all (bufAtomB d n) &&
        (r == d || decide (Atom.copy r d ∈ as))
    | _ => false
  | _ => false

theorem atomsOf_append_ret : ∀ (ss : List Stmt) (vs : List V), atomsOf (ss ++ [.ret vs]) = atomsOf ss
  | [], _ => rfl
  | s :: ss, vs => by
    cases s <;> simp only [List.cons_append, atomsOf, atomsOf_append_ret ss vs]

theorem leafBufB_spec {d : V} {n : ℕ} {B : List Stmt} (h : leafBufB d n B = true) :
    ∃ (as : List Atom) (r : V), B = (Atom.hint (.alloc d n) :: as).map Stmt.atom ++ [.ret [r]] ∧
      as.all (bufAtomB d n) = true ∧ (r = d ∨ Atom.copy r d ∈ as) := by
  unfold leafBufB at h
  split at h
  · rename_i r hR
    split at h
    · rename_i d' n' as hA
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨rfl, rfl⟩, hall⟩, hr⟩ := h
      obtain ⟨ss, rfl, hss⟩ := retOf_spec hR
      rw [atomsOf_append_ret] at hA
      exact ⟨as, r, by rw [eq_map_atomsOf hss, hA], hall, hr⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

theorem bufAtomB_noAlloc {d : V} {n : ℕ} {a : Atom} (h : bufAtomB d n a = true) : atomAllocB a = false := by
  cases a <;> simp_all [bufAtomB, atomAllocB]

theorem bufAtomB_noAddr {d : V} {n : ℕ} {a : Atom} (h : bufAtomB d n a = true) : atomAddr? a = none := by
  cases a <;> simp_all [bufAtomB, atomAddr?]

theorem bufAtomB_noHint {d : V} {n : ℕ} {a : Atom} (h : bufAtomB d n a = true) (σ : Val) :
    Ev.hintAddrs σ (.atom a) = [] := by
  cases a <;> simp_all [bufAtomB, Ev.hintAddrs]

theorem bufAtomB_load {d : V} {n : ℕ} {a : Atom} (h : bufAtomB d n a = true) {q : V × ℕ}
    (hq : atomLoad? a = some q) : q.1 = d ∧ q.2 < n := by
  cases a with
  | load d' p off =>
    simp only [atomLoad?, Option.some.injEq] at hq
    subst hq
    simpa [bufAtomB] using h
  | _ => simp [atomLoad?] at hq

/-- **A call with no witness hint, exact for free, completes with no words of its own** where its
relation holds. -/
theorem callCompletes0_free (hwf : coreProgram.Wf) {k : ℕ} {f : String} (hw : NoWitG f) (hx : ExactFreeG f)
    {args rets : List E} {Pre : Reader → Prop} (h : ∀ rd, LowDef k rd → Pre rd → coreProgram.Rel rd f args rets) :
    CallCompletes0 k f args rets Pre FreePost := fun rd hl hp => by
  obtain ⟨t, hn, hv, hb⟩ := Program.Rel.tree hwf (h rd hl hp)
  exact ⟨t, hn, hv, hb, pops_nil_of_noWitness hw hv hn rd, every_exact_of_free hx hv hn rd⟩

variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}

/-- **A leaf filling the buffer it returns completes placed** at any frame and cursor `c`: its words
the buffer's `vals` from `c`, ending at `c + n`, claiming the buffer. -/
theorem callAtA_leafBuf {k : ℕ} {f : String} {fn : Fn} {d : V} {n : ℕ}
    (hfind : coreProgram.find? f = some fn) (hlp : coreProgram.loop f = false)
    (hB : leafBufB d n fn.body = true) {args : List E} {fp c : ℕ} {vals : List E} (hlen : vals.length = n)
    {R : ℕ → Prop} {Out Pre : Reader → Prop} {Post : Reader → Tree → Prop}
    (hO : ∀ rd, HoldsWords rd [(c, vals)] → Out rd)
    (h : CallCompletes0 k f args [ptrAt c] (fun rd => HoldsWords rd [(c, vals)] ∧ Pre rd) Post) :
    CallAtA fs al cert k f args [ptrAt c] R (fun i => c ≤ i ∧ i < c + n) Out Pre Post (fs f) fp c (c + n) := by
  obtain ⟨as, r, hbody, hall, hr⟩ := leafBufB_spec hB
  have hok : ∀ a ∈ as, bufAtomB d n a = true := fun a ha => List.all_eq_true.mp hall a ha
  refine ⟨[(c, vals)], ⟨fun q hq => ?_, List.pairwise_singleton _ _⟩, by omega, hO, fun rd hl hw hp => ?_⟩
  · simp only [List.mem_singleton] at hq
    subst hq
    exact Or.inr ⟨le_rfl, by simp [hlen]⟩
  obtain ⟨t, hn, hv, hb, hq⟩ := h rd hl ⟨hw, hp⟩
  have hv0 := hv
  cases t with
  | phantom _ _ => exact hv.elim
  | node g σ bufs kids =>
    obtain ⟨fn', hfn, _, es, vs, hwk, hret, hev, hk⟩ := hv
    simp only [Tree.name] at hn
    subst g
    rw [hfind] at hfn
    obtain rfl := Option.some.inj hfn
    have hw' : walk σ fn.body = .ret ((Atom.hint (.alloc d n) :: as).map Ev.atom) [r] := by
      rw [hbody]; exact walk_atoms _ _ _
    rw [hw'] at hwk
    obtain ⟨rfl, rfl⟩ : (Atom.hint (.alloc d n) :: as).map Ev.atom = es ∧ [r] = vs := by
      simpa using hwk
    have hσr : σ r = ptrAt c := by simpa using hret
    have hσd : σ d = ptrAt c := by
      rcases hr with rfl | hr
      · exact hσr
      · have := hev (.atom (.copy r d)) (List.mem_cons_of_mem _ (List.mem_map_of_mem hr))
        exact (show σ r = σ d from this).symm.trans hσr
    have hev' : (Memory.Tree.node f σ bufs kids).events coreProgram =
        (Atom.hint (.alloc d n) :: as).map Ev.atom := events_node hfind hw'
    rw [calls_atoms] at hk
    have hkids : kids = [] := by
      cases kids with
      | nil => rfl
      | cons _ _ => simp [Tree.KidsValid] at hk
    subst hkids
    have hnoA : as.all (fun a => !atomAllocB a) = true :=
      List.all_eq_true.mpr fun a ha => by simp [bufAtomB_noAlloc (hok a ha)]
    have hal : allocs σ ((Atom.hint (.alloc d n) :: as).map Ev.atom) = [n] := by
      have := allocs_atoms σ hnoA
      simp only [allocs, List.map_cons, List.filterMap_cons, Ev.alloc?] at this ⊢
      rw [this]
    have hdst : allocDsts ((Atom.hint (.alloc d n) :: as).map Ev.atom) = [d] := by
      have := allocDsts_atoms hnoA
      simp only [allocDsts, List.map_cons, List.filterMap_cons, Ev.allocDst?] at this ⊢
      rw [this]
    have haddr : addrs ((Atom.hint (.alloc d n) :: as).map Ev.atom) = [] := by
      rw [addrs_atoms, List.filterMap_eq_nil_iff]
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · rfl
      · exact bufAtomB_noAddr (hok a ha)
    rw [Tree.BufsOk, hev', hal] at hb
    obtain ⟨rfl, -⟩ := hb
    have hown : ∀ i, c ≤ i → i < c + n →
        (Memory.Tree.node f σ [n] []).DataA coreProgram fs al cert (fp, c) i := fun i h1 h2 => by
      rw [dataA_node, hev']
      exact Or.inl (Or.inl ⟨(n, c), by simp [bases], h1, by omega⟩)
    refine ⟨.node f σ [n] [], rfl, hv0, ⟨by rw [hev', hal], by rw [Tree.BufsOkKids]; trivial⟩, ?_, ?_, ?_, ?_,
      ?_, fun i hi => hown i hi.1 hi.2, hq⟩
    · rw [Tree.block, hlp]; simp
    · rw [endA_node, hlp]; simp [endF_nil]
    · rw [placedA_node, hev']
      refine ⟨⟨?_, ?_⟩, placedKidsA_nil⟩
      · rw [hdst]; simp [bases, hσd]
      · rw [haddr]; simp
    · rw [loadsInA_node, hev']
      refine ⟨fun A hA => ?_, loadsInKidsA_nil⟩
      rw [loadAddrs_atoms] at hA
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hA
      obtain ⟨a, ha, hqa⟩ := List.mem_filterMap.mp hq
      rcases List.mem_cons.mp ha with rfl | ha
      · simp [atomLoad?] at hqa
      · obtain ⟨hq1, hq2⟩ := bufAtomB_load (hok a ha) hqa
        refine ⟨c + q.2, ?_, Or.inl (hown _ (by omega) (by omega))⟩
        rw [hq1, hσd]
        exact Main.addr_ofK c q.2
    · rw [hintsIn_node, hev']
      refine ⟨fun A hA => ?_, hintsInKids_nil⟩
      simp only [heapHintAddrs, List.mem_flatMap] at hA
      obtain ⟨e, he, hA⟩ := hA
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
      rcases List.mem_cons.mp ha with rfl | ha
      · simp [Ev.hintAddrs, hintDest?] at hA
      · rw [bufAtomB_noHint (hok a ha)] at hA
        simp at hA

set_option maxRecDepth 100000 in
theorem exponent_tables_leafBuf :
    leafBufB (.n (val% «exponent_tables» "g_squares")) lit% expTabN (fn% «exponent_tables»).body = true := by
  decide +kernel

theorem exponent_tables_not_loop : coreProgram.loop "exponent_tables" = false := by decide +kernel

/-- **`exponent_tables` completes placed** at the cursor `c`, any frame: its tables its words from
`c`, claimed as its data, ending at `c + expTabLen`, every memory holding them holding the tables
(`Out`), popping nothing, every node exact. -/
theorem exponent_tables_callAtA (hwf : coreProgram.Wf) (k fp c : ℕ) (R : ℕ → Prop) :
    CallAtA fs al cert k "exponent_tables" [] [ptrAt c] R (fun i => c ≤ i ∧ i < c + expTabLen)
      (fun rd => ExpTables rd (ptrAt c) ∧ ExpWinTab rd (ptrAt c)) (fun _ => True) FreePost
      (fs "exponent_tables") fp c (c + expTabLen) := by
  have hn : expTabLen = lit% expTabN := by decide
  have hO : ∀ rd, HoldsWords rd [(c, expTabAllWords)] → ExpTables rd (ptrAt c) ∧ ExpWinTab rd (ptrAt c) :=
    fun rd hw => (expTabAll_iff rd _).2 fun o ho => by
      have h := hw _ List.mem_cons_self o (by rw [length_expTabAllWords]; exact ho)
      simpa [expTabAllWords] using h
  rw [hn]
  exact callAtA_leafBuf find_exponent_tables exponent_tables_not_loop exponent_tables_leafBuf
    length_expTabAllWords hO
    (callCompletes0_free hwf et_free.1 et_free.2 fun rd _ hp => (exponent_tables_holds rd [] [_]).mpr (hO rd hp.1))

end
end LeanVM.Guest.Complete
