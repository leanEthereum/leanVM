/-
  LeanVM.Guest.B1.VsC.IndexSideA

  `index_side__L{w}` completes placed: a node of atoms and one call of `index_mle__L{w}`, no
  words of its own, its loads and stores in its three arrays.
-/

module

public import LeanVM.Guest.B1.VsC.IndexSideC
public import LeanVM.Guest.B1.VsC.LeavesA
import LeanVM.Guest.CoreRef

/-!
# `index_side`, placed

`index_side__L{w}(r, zeta, below)` reads `r` and `zeta` (`w` words each), stores `w + 1` words at
`below`, and calls `index_mle__L{w}(r)`, a straight leaf. Neither allocates, so the transfer
`callAtA_of_callCompletes0` applies from `index_side_complete` (no words of its own), given every
valid tree's shape (`is_shape`): block its frame, ending after its callee's frame at the aligned
base of its cursor, its loads (its own and its callee's) in the region holding the three arrays, no
heap hint. The bodies' facts are one kernel decision per width (`is_place`).
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd
open LeanVM.Prover.Exec (allocBase)

open LeanVM.Guest.B1.Link LeanVM.Guest.B1.Fs LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.KeccakGkr
open LeanVM.Guest.Value.Keccak LeanVM.Protocol.Verifier

@[expose] public section

/-- What the kernel checks of `index_side__L{w}` and its callee to place them. -/
def isPlaceOk (w : ℕ) (fi fm : Fn) : Bool :=
  (retOfC fi.body).isSome && !fi.loop && Stmt.pureList [isNames.getD (w - 19) "", imNames.getD (w - 19) ""] fi.body &&
    (atomsOf fi.body).all (loadHintInB [(0, w), (1, w), (2, w + 1)]) && decide (fi.params = [.n 0, .n 1, .n 2]) &&
    leafPlaceOk (imNames.getD (w - 19) "") fm 1 [(0, w)] &&
    Stmt.pureList [isNames.getD (w - 19) "", imNames.getD (w - 19) ""] fm.body

set_option maxRecDepth 100000 in
theorem is_place : ∀ w, 19 ≤ w → w ≤ 24 → ∃ fi fm, coreProgram.find? (isNames.getD (w - 19) "") = some fi ∧
    coreProgram.find? (imNames.getD (w - 19) "") = some fm ∧ fi.body = isBody w ∧ isPlaceOk w fi fm = true := by
  intro w hw hw'
  interval_cases w
  · exact ⟨_, _, coreProgram_find?_at (j := idx% «index_side__L19») rfl,
      coreProgram_find?_at (j := idx% «index_mle__L19») rfl, stmtsEqb_sound (by decide +kernel), by decide +kernel⟩
  · exact ⟨_, _, coreProgram_find?_at (j := idx% «index_side__L20») rfl,
      coreProgram_find?_at (j := idx% «index_mle__L20») rfl, stmtsEqb_sound (by decide +kernel), by decide +kernel⟩
  · exact ⟨_, _, coreProgram_find?_at (j := idx% «index_side__L21») rfl,
      coreProgram_find?_at (j := idx% «index_mle__L21») rfl, stmtsEqb_sound (by decide +kernel), by decide +kernel⟩
  · exact ⟨_, _, coreProgram_find?_at (j := idx% «index_side__L22») rfl,
      coreProgram_find?_at (j := idx% «index_mle__L22») rfl, stmtsEqb_sound (by decide +kernel), by decide +kernel⟩
  · exact ⟨_, _, coreProgram_find?_at (j := idx% «index_side__L23») rfl,
      coreProgram_find?_at (j := idx% «index_mle__L23») rfl, stmtsEqb_sound (by decide +kernel), by decide +kernel⟩
  · exact ⟨_, _, coreProgram_find?_at (j := idx% «index_side__L24») rfl,
      coreProgram_find?_at (j := idx% «index_mle__L24») rfl, stmtsEqb_sound (by decide +kernel), by decide +kernel⟩

variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}

/-- **Every valid tree of `index_side__L{w}` has its placed shape.** -/
theorem is_shape {w : ℕ} {fi fm : Fn} (hfi : coreProgram.find? (isNames.getD (w - 19) "") = some fi)
    (hfm : coreProgram.find? (imNames.getD (w - 19) "") = some fm) (hbd : fi.body = isBody w)
    (hck : isPlaceOk w fi fm = true) (hS : coreProgram.PureIn [isNames.getD (w - 19) "", imNames.getD (w - 19) ""]) {r zeta below : E}
    {rets : List E} {R : ℕ → Prop} (hr : ArrIn R r w) (hz : ArrIn R zeta w) (hb : ArrIn R below (w + 1))
    {rd : Reader} {t : Tree} (hn : t.name = isNames.getD (w - 19) "")
    (hv : t.Valid coreProgram rd [r, zeta, below] rets) (hbo : t.BufsOk coreProgram) (c : ℕ) :
    t.block fs coreProgram.loop = fs (isNames.getD (w - 19) "") ∧
      t.endA fs coreProgram.loop al c =
        allocBase (al (imNames.getD (w - 19) "")) c + fs (imNames.getD (w - 19) "") ∧
      t.LoadsR coreProgram R ∧ t.HintsR coreProgram R := by
  simp only [isPlaceOk, Bool.and_eq_true] at hck
  obtain ⟨⟨⟨⟨⟨⟨hrc, hlp⟩, -⟩, hL⟩, hpar⟩, hleaf⟩, -⟩ := hck
  have hpar' : fi.params = [.n 0, .n 1, .n 2] := of_decide_eq_true hpar
  have hcb' : callsOfB fi.body = [⟨imNames.getD (w - 19) "", [.n 0], [.n 3], true⟩] := by
    rw [hbd]; exact callsOfB_isBody w
  have hlp' : coreProgram.loop (isNames.getD (w - 19) "") = false := by
    rw [Program.loop_of_find? hfi]; simpa using hlp
  -- the callee, a placed leaf
  have hleaf' := hleaf
  simp only [leafPlaceOk, Bool.and_eq_true] at hleaf'
  obtain ⟨⟨⟨⟨⟨hmr, hmlp⟩, -⟩, hmL⟩, hmpar⟩, hmargs⟩ := hleaf'
  have hmlp' : coreProgram.loop (imNames.getD (w - 19) "") = false := by
    rw [Program.loop_of_find? hfm]; simpa using hmlp
  have hmnc : ∀ fn σ es vs, coreProgram.find? (imNames.getD (w - 19) "") = some fn →
      walk σ fn.body = .ret es vs → calls es = [] := by
    intro fn σ es vs hf hw
    rw [hfm] at hf
    cases hf
    obtain ⟨vs0, hr'⟩ := Option.isSome_iff_exists.mp hmr
    obtain ⟨ss, hbody, hss⟩ := retOf_spec hr'
    have hb' : fm.body = (atomsOf ss).map Stmt.atom ++ [.ret vs0] := by rw [hbody, ← eq_map_atomsOf hss]
    rw [hb', walk_atoms] at hw
    cases hw
    exact calls_atoms _
  cases t with
  | phantom _ _ => exact hv.elim
  | node g σ bufs kids =>
    simp only [Tree.name] at hn
    subst hn
    obtain ⟨fn', hfn, hp, es, vs, hw, _, _, hk⟩ := hv
    rw [hfi] at hfn
    cases hfn
    obtain ⟨vs0, hr'⟩ := Option.isSome_iff_exists.mp hrc
    obtain ⟨ss, hbody, hss⟩ := retOfC_spec hr'
    have hw' : walk σ fi.body = .ret (ss.flatMap (slEvs σ)) vs0 := by
      rw [hbody]; exact walk_straight σ vs0 ss (straight_of_atomOrCall ss hss)
    rw [hw'] at hw
    cases hw
    have hcs : calls (ss.flatMap (slEvs σ)) = [⟨imNames.getD (w - 19) "", [.n 0], [.n 3], true⟩] := by
      rw [calls_atomOrCall σ ss hss, ← hcb', hbody]; simp [callsOfB, callOf?]
    rw [hcs] at hk
    rw [hpar'] at hp
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hp
    obtain ⟨p0, p1, p2⟩ := hp
    rcases kids with _ | ⟨t', ks⟩
    · simp only [Tree.KidsValid] at hk
    rcases ks with _ | ⟨_, _⟩
    swap
    · simp only [Tree.KidsValid, and_false] at hk
    obtain ⟨hn0, hv0, -⟩ := hk
    have hn' : t'.name = imNames.getD (w - 19) "" := hn0
    have hv' : t'.Valid coreProgram rd [σ (.n 0)] [σ (.n 3)] := hv0
    have hev : (Memory.Tree.node (isNames.getD (w - 19) "") σ bufs [t']).events coreProgram =
        ss.flatMap (slEvs σ) := Complete.events_node hfi hw'
    have hpure : ∀ e ∈ ss.flatMap (slEvs σ), e.pure [isNames.getD (w - 19) "", imNames.getD (w - 19) ""] := by
      have := walk_pure (σ := σ) fi.body (hS _ List.mem_cons_self fi hfi)
      rwa [hw'] at this
    rw [Tree.BufsOk, hev, allocs_pure hpure] at hbo
    obtain ⟨rfl, hbk⟩ := hbo
    rw [Tree.BufsOkKids] at hbk
    have hm : imNames.getD (w - 19) "" ∈ [isNames.getD (w - 19) "", imNames.getD (w - 19) ""] := by simp
    have hbe := block_endA_leaf (fs := fs) (al := al) hS hm hmlp' hmnc hn' hv' hbk.1
      (allocBase (al (imNames.getD (w - 19) "")) c + fs (imNames.getD (w - 19) ""))
    have hkid := loadsR_hintsR_of_loadHintIn (args := [σ (.n 0)]) R hfm (of_decide_eq_true hmpar) hmL hmr
      (fun q hq => of_decide_eq_true (List.all_eq_true.mp hmargs q hq))
      (fun q hq => by simp only [List.mem_singleton] at hq; subst hq; rw [← p0] at hr; exact hr) hn' hv'
    -- the node's own loads and hints, through its parameters
    have hσ : ∀ j, j < 3 → σ (.n j) = [r, zeta, below].getD j 0 := by
      intro j hj
      interval_cases j
      exacts [p0, p1, p2]
    have hok : ∀ a, Ev.atom a ∈ ss.flatMap (slEvs σ) → loadHintInB [(0, w), (1, w), (2, w + 1)] a = true :=
      fun a ha => List.all_eq_true.mp hL a (mem_atomsOf' (by rw [hbody]; exact List.mem_append_left _ (atoms_slEvs ha)))
    have hptr : ∀ q ∈ [(0, w), (1, w), (2, w + 1)], ArrIn R ([r, zeta, below].getD q.1 0) q.2 := by
      intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      exacts [hr, hz, hb]
    have hq3 : ∀ q ∈ [(0, w), (1, w), (2, w + 1)], q.1 < 3 := by
      intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> simp
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [Tree.block, hlp']; simp
    · rw [endA_node, hlp']
      simp only [Bool.false_eq_true, ↓reduceIte, List.sum_nil, Nat.add_zero, endF_cons, endF_nil, hn']
      rw [hbe.1, hbe.2]
    · rw [Tree.LoadsR, hev]
      refine ⟨fun A hA => ?_, by rw [Tree.LoadsRKids, Tree.LoadsRKids]; exact ⟨hkid.1, trivial⟩⟩
      simp only [loadAddrs, List.mem_filterMap] at hA
      obtain ⟨e, he, hA⟩ := hA
      cases e with
      | atom a =>
        have hk := hok a he
        cases a with
        | load d p off =>
          simp only [Ev.loadAddr?, Option.some.injEq] at hA
          simp only [loadHintInB, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hk
          obtain ⟨q, hqm, rfl, hoff⟩ := hk
          obtain ⟨i, hi, hR⟩ := hptr q hqm off hoff
          exact ⟨i, by rw [← hA, hσ _ (hq3 q hqm)]; exact hi, hR⟩
        | _ => simp [Ev.loadAddr?] at hA
      | _ => simp [Ev.loadAddr?] at hA
    · rw [Tree.HintsR, hev]
      refine ⟨fun A hA => ?_, by rw [Tree.HintsRKids, Tree.HintsRKids]; exact ⟨hkid.2, trivial⟩⟩
      simp only [heapHintAddrs, List.mem_flatMap] at hA
      obtain ⟨e, he, hA⟩ := hA
      cases e with
      | atom a =>
        have hk := hok a (List.mem_flatMap.mpr he)
        rw [hintAddrs_atom_eq] at hA
        have hk' : destInB [(0, w), (1, w), (2, w + 1)] (atomHeapDest? a) = true := by
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
          exact ⟨i, by rw [hσ _ (hq3 q hqm)]; exact hi, hR⟩
      | _ => simp [Ev.hintAddrs] at hA

/-- **`index_side__L{w}` completes placed**: block its frame, ending after its callee's frame at
the aligned base of its cursor, its three arrays in `R`. -/
theorem index_side_completeA (kd : ℕ) {w : ℕ} (hw : 19 ≤ w) (hw' : w ≤ 24) (r zeta below : E) (rs zs : List E)
    (hrs : rs.length = w) (hzs : zs.length = w) (hap : ArraysApart [r, zeta, below] [(0, w), (1, w), (2, w + 1)])
    {R : ℕ → Prop} (hr : ArrIn R r w) (hz : ArrIn R zeta w) (hb : ArrIn R below (w + 1)) :
    CallCompletesA fs al cert kd (isNames.getD (w - 19) "") [r, zeta, below]
      [indexMle rs, (sideFold zs rs).1, (sideFold zs rs).2.1] R (fun _ _ _ => False) (fun _ => True)
      (fun rd ↦ HoldsArrays rd [r, zeta, below] (isIns rs zs) ∧ HoldsArrays rd [r, zeta, below] (isOuts rs w))
      PostQuiet := by
  obtain ⟨fi, fm, hfi, hfm, hbd, hck⟩ := is_place w hw hw'
  have hck' := hck
  simp only [isPlaceOk, Bool.and_eq_true] at hck'
  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, hpi⟩, -⟩, -⟩, -⟩, hpm⟩ := hck'
  have hS : coreProgram.PureIn [isNames.getD (w - 19) "", imNames.getD (w - 19) ""] := by
    intro g hg fn hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · rw [hfi] at hf; cases hf; exact hpi
    · rw [hfm] at hf; cases hf; exact hpm
  have h0 := index_side_complete kd w hw hw' r zeta below rs zs hrs hzs hap
  refine ⟨fs (isNames.getD (w - 19) ""), fun fp c _ => ⟨allocBase (al (imNames.getD (w - 19) "")) c +
    fs (imNames.getD (w - 19) ""), callAtA_of_callCompletes0 hS List.mem_cons_self ?_ h0
      fun rd t _ _ hn hv hbo _ => is_shape hfi hfm hbd hck hS hr hz hb hn hv hbo c⟩⟩
  exact le_trans (le_allocBase _ _) (Nat.le_add_right _ _)

end
end LeanVM.Guest.B1.VsC
