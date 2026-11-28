module

public import LeanVM.Guest.Complete.Claims.Pops
public import LeanVM.Guest.Complete.TransferA
public import LeanVM.Guest.Complete.MainA
public import LeanVM.Guest.Complete.Free
public import LeanVM.Guest.Complete.ComposeA
import LeanVM.Guest.B1.Common.Vc
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«claim_list_tail»
import LeanVM.Guest.Data.ValNames.«claim_list_last__L»
import LeanVM.Guest.Data.ValNames.«list_split»

/-!
# The claim lists' leaves, placed

`leaf_loadsR_hintsR`: a body of atoms then a return whose loads and heap hints all go through its
array arguments (`argAtomOk`, by the kernel) loads and hints in any region covering those arrays,
on every valid tree. `list_split_callAtA`: `list_split` (no load, no heap hint) on a memory defined
below `2^17`. `clLast_callAtA`: `claim_list_last__L{r}` from its relation, loading its state's `13`
cells and its block's `4r`, hinting its block. `tail_callAtA`: `claim_list_tail`, its dispatch's
callee after its frame.
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Guest.B1.Digest
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}

/-! ## Leaves through their arguments -/

/-- An atom loading or hinting to the heap only through the arrays `ps` (pointer, length). -/
def argAtomOk (ps : List (V × ℕ)) : Atom → Bool
  | .load _ p off => ps.any fun q => decide (q.1 = p) && decide (off < q.2)
  | .hint h => match (hintDest? h).bind destHeap? with
    | some (p, off, len) => ps.any fun q => decide (q.1 = p) && decide (off + len ≤ q.2)
    | none => true
  | _ => true

/-- **A leaf through its arguments** loads and hints in a region covering its arrays. -/
theorem leaf_loadsR_hintsR {f : String} {fn : Fn} {as : List Atom} {vs : List V} {ps : List (V × ℕ)}
    (hf : coreProgram.find? f = some fn) (hs : atomsRet fn.body = some (as, vs))
    (hok : as.all (argAtomOk ps) = true) {args rets : List E} {bs : V → ℕ} {R : ℕ → Prop}
    (hσ : ∀ σ : Val, fn.params.map σ = args → ∀ q ∈ ps, σ q.1 = ptrAt (bs q.1))
    (hR : ∀ q ∈ ps, ∀ i < q.2, R (bs q.1 + i))
    {rd : Reader} {t : Tree} (hn : t.name = f) (hv : t.Valid coreProgram rd args rets) :
    t.LoadsR coreProgram R ∧ t.HintsR coreProgram R := by
  cases t with
  | phantom _ _ => exact hv.elim
  | node g σ bufs kids =>
    obtain ⟨fn', hfn, hpar, es, vs', hw, _, _, hk⟩ := hv
    simp only [Tree.name] at hn
    subst hn
    rw [hf] at hfn
    cases hfn
    have hw' : walk σ fn.body = .ret (as.map Ev.atom) vs := by
      rw [atomsRet_eq hs, walk_atoms]
    rw [hw'] at hw
    cases hw
    have hev : (Memory.Tree.node g σ bufs kids).events coreProgram = as.map Ev.atom := by
      simp only [Tree.events, Tree.name, Tree.val, hf, hw']
    rw [calls_atoms] at hk
    have hkids : kids = [] := by
      cases kids with
      | nil => rfl
      | cons _ _ => simp [Tree.KidsValid] at hk
    subst hkids
    have hok' : ∀ a ∈ as, argAtomOk ps a = true := fun a ha => List.all_eq_true.mp hok a ha
    refine ⟨?_, ?_⟩
    · rw [Tree.LoadsR, hev]
      refine ⟨fun A hA => ?_, by rw [Tree.LoadsRKids]; trivial⟩
      simp only [loadAddrs, List.filterMap_map, List.mem_filterMap, Function.comp] at hA
      obtain ⟨a, ha, hA⟩ := hA
      have hk := hok' a ha
      cases a with
      | load d p off =>
        simp only [Ev.loadAddr?, Option.some.injEq] at hA
        simp only [argAtomOk, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hk
        obtain ⟨q, hqm, hq1, hoff⟩ := hk
        refine ⟨bs q.1 + off, ?_, hR q hqm off hoff⟩
        rw [← hA, ← hq1, hσ σ hpar q hqm]
        exact Main.addr_ofK _ off
      | _ => simp [Ev.loadAddr?] at hA
    · rw [Tree.HintsR, hev]
      refine ⟨fun A hA => ?_, by rw [Tree.HintsRKids]; trivial⟩
      simp only [heapHintAddrs, List.flatMap_map, List.mem_flatMap] at hA
      obtain ⟨a, ha, hA⟩ := hA
      have hk := hok' a ha
      cases a with
      | hint h =>
        simp only [Ev.hintAddrs] at hA
        simp only [argAtomOk] at hk
        revert hA hk
        cases (hintDest? h).bind destHeap? with
        | none => intro hA; simp at hA
        | some x =>
          obtain ⟨p, off, len⟩ := x
          intro hA hk
          simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hk
          obtain ⟨q, hqm, hq1, hlen⟩ := hk
          simp only [List.mem_map, List.mem_range] at hA
          obtain ⟨i, hi, rfl⟩ := hA
          refine ⟨bs q.1 + (off + i), ?_, hR q hqm _ (by omega)⟩
          rw [← hq1, hσ σ hpar q hqm]
          exact Main.addr_ofK _ _
      | _ => simp [Ev.hintAddrs] at hA

/-! ## `list_split` -/

/-- **`list_split`'s relation** on a memory defined below `2^17`, `a < 2^17`. -/
theorem list_split_rel17 (rd : Reader) (hm : Sig.MemOK rd (2 ^ 17)) {a b c : ℕ} (ha : a < 2 ^ 17)
    (hb : b < bigGroups) (hc : c < claimGroup) :
    coreProgram.Rel rd "list_split" [gen ^ (claimBig * a + claimGroup * b + c)] [gen ^ a, gen ^ b, gen ^ c] := by
  rw [rel_iff_fnSem find_list_split]
  vc []
  have hm16 : Sig.MemOK rd (2 ^ 16) := fun i hi => hm i (lt_of_lt_of_le hi (by norm_num))
  obtain ⟨t1, t2, h1, e1, h2⟩ := rc_holds' hm16 (K := 16) (Nat.le_of_lt_succ hc) (by norm_num)
  obtain ⟨t5, t6, h5, e3, h6⟩ := rc_holds' hm16 (K := 7) (Nat.le_of_lt_succ hb) (by norm_num)
  obtain ⟨t3, h3⟩ : ∃ w, LoadHolds rd (gen ^ a) 0 w := gen_pow_eq_ofK a ▸ Sig.load_gpow hm ha
  refine ⟨_, _, _, h1, by rw [word_g16, e1], _, h2, _, _, _, h5, by rw [word_g7, e3], _, h6, _, _,
    h3, e_add_eq_zero_iff.mpr ?_, rfl, rfl, rfl⟩
  rw [claimBig, claimGroup]
  ring

set_option maxRecDepth 100000 in
theorem list_split_atoms : ((atomsRet (fn% «list_split»).body).map fun p => p.1.all (argAtomOk [])) = some true := by
  decide +kernel

/-- **`list_split` completes placed** at any frame and cursor on `n < 2^19` claims, on a memory
defined below `2^17`: block its frame, ending at its cursor, loading and hinting nothing. -/
theorem list_split_callAtA (hwf : coreProgram.Wf) {k : ℕ} (hk : 17 ≤ k) {n : ℕ} (hn : n < 2 ^ 19)
    {R : ℕ → Prop} {Pre : Reader → Prop} (fp c : ℕ) :
    CallAtA fs al cert k "list_split" [gen ^ n] [gen ^ (n / 136), gen ^ (n % 136 / 17), gen ^ (n % 17)] R
      (fun _ => False) (fun _ => True) Pre (fun _ _ => True) (fs "list_split") fp c c := by
  have hlp : coreProgram.loop "list_split" = false := by decide +kernel
  obtain ⟨as, vs, hs, hok⟩ : ∃ as vs, atomsRet (fn% «list_split»).body = some (as, vs) ∧
      as.all (argAtomOk []) = true := by
    have h := list_split_atoms
    cases e : atomsRet (fn% «list_split»).body with
    | none => rw [e] at h; exact absurd h (by simp)
    | some p => rw [e] at h; exact ⟨p.1, p.2, rfl, by simpa using h⟩
  have hnc : ∀ fn σ es vs', coreProgram.find? "list_split" = some fn → walk σ fn.body = .ret es vs' →
      calls es = [] := by
    intro fn σ es vs' hf hw
    rw [find_list_split] at hf
    cases hf
    rw [atomsRet_eq hs, walk_atoms] at hw
    obtain ⟨rfl, -⟩ := Out.ret.inj hw
    exact calls_atoms _
  have hnm : gen ^ n = gen ^ (claimBig * (n / 136) + claimGroup * (n % 136 / 17) + n % 17) := by
    congr 1; simp only [claimBig, claimGroup]; omega
  refine callAtA_of_callCompletes0 list_split_pure List.mem_cons_self le_rfl (fun rd hl _ => ?_)
    fun rd t _ _ hn' hv hb _ => ?_
  · have hr := list_split_rel17 rd (fun i hi => hl.mono hk i hi) (a := n / 136) (b := n % 136 / 17)
      (c := n % 17) (by omega) (by simp only [bigGroups]; omega) (by simp only [claimGroup]; omega)
    rw [← hnm] at hr
    obtain ⟨t, htn, htv, htb⟩ := Program.Rel.tree hwf hr
    exact ⟨t, htn, htv, htb, trivial⟩
  · obtain ⟨hB, hE⟩ := block_endA_leaf (fs := fs) (al := al) list_split_pure List.mem_cons_self hlp hnc hn' hv hb c
    exact ⟨hB, hE, leaf_loadsR_hintsR find_list_split hs hok (bs := fun _ => 0) (fun _ _ q hq => absurd hq List.not_mem_nil)
      (fun q hq => absurd hq List.not_mem_nil) hn' hv⟩

/-! ## `claim_list_last__L{r}` -/

set_option maxRecDepth 100000 in
theorem clLast_facts : ∀ r < 17, coreProgram.loop (clNames.getD r "") = false ∧
    ((atomsRet (coreProgram.getD (idx% «claim_list_last__L0» + r) default).body).map fun p =>
      p.1.all (argAtomOk [(.n (valf% «claim_list_last» "state"), 13), (.n (valf% «claim_list_last» "blk"), 4 * r)])) =
        some true := by
  decide +kernel

/-- **`claim_list_last__L{r}` completes placed** at any frame and cursor where its relation holds,
its state's `13` cells at `sb` and its block's `4r` at `bb` in the region. -/
theorem clLast_callAtA (hwf : coreProgram.Wf) {k r sb bb : ℕ} (hr : r < 17) {d0 d1 : E} {R : ℕ → Prop}
    {Pre : Reader → Prop}
    (hrel : ∀ rd, LowDef k rd → Pre rd → coreProgram.Rel rd (clNames.getD r "") [ptrAt sb, ptrAt bb] [d0, d1])
    (hRs : ∀ i < 13, R (sb + i)) (hRb : ∀ i < 4 * r, R (bb + i)) (fp c : ℕ) :
    CallAtA fs al cert k (clNames.getD r "") [ptrAt sb, ptrAt bb] [d0, d1] R (fun _ => False) (fun _ => True)
      Pre (fun _ _ => True) (fs (clNames.getD r "")) fp c c := by
  obtain ⟨hlp, hfa⟩ := clLast_facts r hr
  obtain ⟨as, vs, hs, hok⟩ : ∃ as vs, atomsRet (coreProgram.getD (idx% «claim_list_last__L0» + r) default).body =
      some (as, vs) ∧ as.all (argAtomOk [(.n (valf% «claim_list_last» "state"), 13),
        (.n (valf% «claim_list_last» "blk"), 4 * r)]) = true := by
    cases e : atomsRet (coreProgram.getD (idx% «claim_list_last__L0» + r) default).body with
    | none => rw [e] at hfa; exact absurd hfa (by simp)
    | some p => rw [e] at hfa; exact ⟨p.1, p.2, rfl, by simpa using hfa⟩
  have hf := find_of_idx (cl_idx r hr)
  have hpar : (coreProgram.getD (idx% «claim_list_last__L0» + r) default).params =
      [V.n (valf% «claim_list_last» "state"), V.n (valf% «claim_list_last» "blk")] := by
    have := cl_all r hr
    simp only [clOk, Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1
  have hmem : clNames.getD r "" ∈ "claim_list_tail" :: clNames :=
    List.mem_cons_of_mem _ (by
      rw [List.getD_eq_getElem _ _ (by simp [clNames]; omega)]; exact List.getElem_mem _)
  have hnc : ∀ fn σ es vs', coreProgram.find? (clNames.getD r "") = some fn → walk σ fn.body = .ret es vs' →
      calls es = [] := by
    intro fn σ es vs' hf' hw
    rw [hf] at hf'
    cases hf'
    rw [atomsRet_eq hs, walk_atoms] at hw
    obtain ⟨rfl, -⟩ := Out.ret.inj hw
    exact calls_atoms _
  refine callAtA_of_callCompletes0 tail_pure hmem le_rfl (fun rd hl hp => ?_) fun rd t _ _ hn hv hb _ => ?_
  · obtain ⟨t, htn, htv, htb⟩ := Program.Rel.tree hwf (hrel rd hl hp)
    exact ⟨t, htn, htv, htb, trivial⟩
  · obtain ⟨hB, hE⟩ := block_endA_leaf (fs := fs) (al := al) tail_pure hmem hlp hnc hn hv hb c
    refine ⟨hB, hE, leaf_loadsR_hintsR hf hs hok (bs := fun v => if v = .n (valf% «claim_list_last» "state") then sb else bb)
      (fun σ hσ q hq => ?_) (fun q hq i hi => ?_) hn hv⟩
    · rw [hpar] at hσ
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hσ
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · simp [hσ.1]
      · simp [hσ.2]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · simpa using hRs i hi
      · simpa using hRb i hi

/-! ## `claim_list_tail` -/

/-- `claim_list_tail`'s valuation: its arguments, the callee's returns, their copies. -/
noncomputable def tailσ (sp blk rest d0 d1 : E) : Val := B1.Val.ofArgs [sp, blk, rest, d0, d1, d0, d1]

/-- **`claim_list_tail` completes placed** on `rest = g^r`, `r < 17`, where its callee's relation
holds: its callee `claim_list_last__L{r}` after its frame, ending at its callee's cursor. -/
theorem tail_callAtA (hwf : coreProgram.Wf) {k r sb bb : ℕ} (hr : r < 17) {d0 d1 : E} {R : ℕ → Prop}
    {Pre : Reader → Prop}
    (hrel : ∀ rd, LowDef k rd → Pre rd → coreProgram.Rel rd (clNames.getD r "") [ptrAt sb, ptrAt bb] [d0, d1])
    (hRs : ∀ i < 13, R (sb + i)) (hRb : ∀ i < 4 * r, R (bb + i)) {fp c : ℕ}
    (hfc : fp + fs "claim_list_tail" ≤ c) :
    CallAtA fs al cert k "claim_list_tail" [ptrAt sb, ptrAt bb, gen ^ r] [d0, d1] R (fun _ => False)
      (fun _ => True) Pre (fun _ _ => True) (fs "claim_list_tail") fp c
      (allocBase (al (clNames.getD r "")) c + fs (clNames.getD r "")) := by
  have hlp : coreProgram.loop "claim_list_tail" = false := by decide +kernel
  set σ := tailσ (ptrAt sb) (ptrAt bb) (gen ^ r) d0 d1 with hσ
  set es : List Ev := Ev.call clNames[r]! [.n (val% «claim_list_tail» "state"), .n (val% «claim_list_tail» "blk")]
      [.n (val% «claim_list_tail» "d0"), .n (val% «claim_list_tail» "d1")] ::
    [Stmt.atom (.copy (.n (val% «claim_list_tail» "s1#0")) (.n (val% «claim_list_tail» "d0"))),
      .atom (.copy (.n (val% «claim_list_tail» "s1#0[1]")) (.n (val% «claim_list_tail» "d1")))].flatMap (slEvs σ)
    with hes
  have hw : walk σ (Fn.body fn% «claim_list_tail») = .ret es [.n (val% «claim_list_tail» "s1#0"),
      .n (val% «claim_list_tail» "s1#0[1]")] := by
    rw [claim_list_tail_shape]
    exact walk_dispatch σ [] [Stmt.atom (.copy (.n (val% «claim_list_tail» "s1#0")) (.n (val% «claim_list_tail» "d0"))),
      .atom (.copy (.n (val% «claim_list_tail» "s1#0[1]")) (.n (val% «claim_list_tail» "d1")))] rfl rfl
      (.n (val% «claim_list_tail» "rest")) clNames
      [.n (val% «claim_list_tail» "state"), .n (val% «claim_list_tail» "blk")]
      [.n (val% «claim_list_tail» "d0"), .n (val% «claim_list_tail» "d1")]
      [.n (val% «claim_list_tail» "s1#0"), .n (val% «claim_list_tail» "s1#0[1]")] (i := r)
      (by simp [clNames]; omega) (by simp [clNames]) (by
        show (gen ^ r : E) = _
        rw [gen_pow_eq_ofK])
  have hal : allocs σ es = [] := by simp [hes, allocs, slEvs, Ev.alloc?]
  have hcalls : calls es = [⟨clNames.getD r "", [.n (val% «claim_list_tail» "state"), .n (val% «claim_list_tail» "blk")],
      [.n (val% «claim_list_tail» "d0"), .n (val% «claim_list_tail» "d1")], true⟩] := by
    simp [hes, calls, slEvs, Ev.call?, clNames_get hr]
  have hcl := clLast_callAtA (fs := fs) (al := al) (cert := cert) hwf hr
    (Pre := fun rd => Pre rd ∧ HoldsWords rd []) (fun rd hl hp => hrel rd hl hp.1) hRs hRb
    (allocBase (al (clNames.getD r "")) c) (allocBase (al (clNames.getD r "")) c + fs (clNames.getD r ""))
  refine callAtA_node hlp hfc ⟨σ, fn% «claim_list_tail», es, [.n (val% «claim_list_tail» "s1#0"),
      .n (val% «claim_list_tail» "s1#0[1]")], [], [fun _ _ => True], fun rd => HoldsWords rd [], fun _ => False,
    find_claim_list_tail, ?_, hw, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [claim_list_tail_params]; rfl
  · rfl
  · rw [hal]; simp [NodeAt, hes, allocDsts, addrs, slEvs, Ev.allocDst?, Ev.addr?, bases]
  · rw [hal]; exact ⟨by simp, List.Pairwise.nil⟩
  · intro A hA; simp [hes, loadAddrs, slEvs, Ev.loadAddr?] at hA
  · intro A hA; simp [hes, heapHintAddrs, slEvs, Ev.hintAddrs] at hA
  · intro i hi; exact hi.elim
  · rw [hcalls, hal, List.sum_nil, Nat.add_zero, KidsAtF]
    simp only [↓reduceIte]
    refine ⟨fs (clNames.getD r ""), allocBase (al (clNames.getD r "")) c + fs (clNames.getD r ""), R,
      fun _ => False, fun _ => True, fun i hi => Or.inl (Or.inl hi), ?_, ?_⟩
    · simp only [List.map_cons, List.map_nil]
      exact hcl
    · rw [KidsAtF]; exact ⟨rfl, fun _ h => h.1, fun _ h => h.elim⟩
  · intro _ _; trivial
  · intro rd _ _ _ ev hev
    rw [hes] at hev
    rcases List.mem_cons.mp hev with rfl | hev
    · trivial
    · refine events_straight (fun s hs => ?_) ev hev
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl <;> rfl
  · intro _ _ _ _ _ _ _; trivial

end
end LeanVM.Guest.Complete
