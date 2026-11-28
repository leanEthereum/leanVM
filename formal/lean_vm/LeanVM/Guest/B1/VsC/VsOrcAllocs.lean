/-
  LeanVM.Guest.B1.VsC.VsOrcAllocs

  `verify_sub`'s allocations on an honest context whose body walks through.
-/

module

public import LeanVM.Guest.B1.VsC.VsOrcMem

/-!
# `verify_sub`'s allocations

A walk through windows whose call windows are calls (`isCallS`) has the allocations of the windows' atoms
(`allocs_wins`); a branch whose arms allocate nothing has none (`allocs_ite`). On `vsSS` they are
`wA`'s (`vsSz0`, the stream, `6`, `8`) and `wC`'s (`16`, `64`, `64`), the stream's `logG (σ 54) = 256 p`
(`vsW0_54`, `vsW_42`): **`vsAllocs`**, i.e. `VsAllocsHyp`.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Protocol.Verifier

@[expose] public section

/-- A call window's statement is a call. -/
def isCallS : Stmt → Bool
  | .call .. => true
  | .callIf .. => true
  | .dispatch .. => true
  | _ => false

/-- An atom allocating a `HeapBuf`. -/
def allocAtom : Atom → Bool
  | .hint (.alloc _ _) => true
  | .hint (.allocDyn _ _) => true
  | _ => false

theorem vsSeq_fall {o o' : Out} {es : List Ev} (h : o.seq o' = .fall es) :
    ∃ e1 e2, o = .fall e1 ∧ o' = .fall e2 ∧ es = e1 ++ e2 := by
  cases o with
  | fall e1 =>
    cases o' with
    | fall e2 => exact ⟨e1, e2, rfl, rfl, by simpa [Out.seq, Out.pre] using h.symm⟩
    | ret _ _ => simp [Out.seq, Out.pre] at h
    | stuck => simp [Out.seq, Out.pre] at h
  | ret _ _ => simp [Out.seq] at h
  | stuck => simp [Out.seq] at h

theorem vsPre_fall {o : Out} {es es' : List Ev} (h : o.pre es' = .fall es) : ∃ e, o = .fall e ∧ es = es' ++ e := by
  cases o with
  | fall e => exact ⟨e, rfl, by simpa [Out.pre] using h.symm⟩
  | ret _ _ => simp [Out.pre] at h
  | stuck => simp [Out.pre] at h

theorem allocs_app (σ : Val) (a b : List Ev) : allocs σ (a ++ b) = allocs σ a ++ allocs σ b := by
  unfold allocs; rw [List.filterMap_append]

theorem walk_atoms (σ : Val) : ∀ as : List Atom, walk σ (as.map Stmt.atom) = .fall (as.map Ev.atom)
  | [] => rfl
  | a :: as => by
    rw [List.map_cons, walk, walk_atoms σ as]
    rfl

theorem pick_allocs (σ : Val) (x : V) (args rets : List V) :
    ∀ (j : ℕ) (gs : List String) {es : List Ev}, pick σ x args rets j gs = .fall es → allocs σ es = []
  | _, [], _, h => by simp [pick] at h
  | j, g :: gs, es, h => by
    unfold pick at h
    split at h
    · cases h; rfl
    · exact pick_allocs σ x args rets (j + 1) gs h

theorem call_allocs (σ : Val) {s : Stmt} (hs : isCallS s = true) {es : List Ev} (h : walk σ [s] = .fall es) :
    allocs σ es = [] := by
  obtain ⟨e1, e2, h1, h2, rfl⟩ := vsSeq_fall (o := walk1 σ s) (o' := walk σ []) h
  cases h2
  rw [List.append_nil]
  cases s with
  | call f args rets => simp only [walk1] at h1; cases h1; rfl
  | callIf c f args =>
    simp only [walk1] at h1; cases h1
    split <;> rfl
  | dispatch x gs args rets => exact pick_allocs σ x args rets 0 gs h1
  | _ => simp [isCallS] at hs

/-- **A walk through windows allocates its atoms' `HeapBuf`s.** -/
theorem allocs_wins (σ : Val) : ∀ ws : List W0, (ws.all fun | .run _ => true | .call s => isCallS s) = true →
    ∀ {es : List Ev}, walk σ (flatW ws) = .fall es →
      allocs σ es = (atomsW ws).filterMap fun a => Ev.alloc? σ (.atom a)
  | [], _, es, h => by simp [flatW, walk] at h; subst h; rfl
  | w :: ws, hw, es, h => by
    simp only [List.all_cons, Bool.and_eq_true] at hw
    rw [flatW_cons, walk_append] at h
    obtain ⟨e1, e2, h1, h2, rfl⟩ := vsSeq_fall h
    rw [allocs_app, allocs_wins σ ws hw.2 h2]
    cases w with
    | run as =>
      rw [W0.stmts, walk_atoms] at h1
      cases h1
      simp only [atomsW, List.flatMap_cons, List.filterMap_append]
      unfold allocs
      rw [List.filterMap_map]
      rfl
    | call s =>
      rw [call_allocs σ hw.1 h1]
      simp [atomsW]

theorem alloc?_none (σ : Val) {a : Atom} (h : allocAtom a = false) : Ev.alloc? σ (.atom a) = none := by
  unfold Ev.alloc?
  split <;> simp_all [allocAtom]

theorem filterMap_alloc_nil (σ : Val) (as : List Atom) (h : (as.all fun a => !allocAtom a) = true) :
    as.filterMap (fun a => Ev.alloc? σ (.atom a)) = [] := by
  rw [List.filterMap_eq_nil_iff]
  intro a ha
  exact alloc?_none σ (by simpa using List.all_eq_true.mp h a ha)

theorem filterMap_alloc_filter (σ : Val) : ∀ as : List Atom,
    as.filterMap (fun a => Ev.alloc? σ (.atom a)) = (as.filter allocAtom).filterMap (fun a => Ev.alloc? σ (.atom a))
  | [] => rfl
  | a :: as => by
    rw [List.filterMap_cons, List.filter_cons, filterMap_alloc_filter σ as]
    cases h : allocAtom a
    · rw [alloc?_none σ h]; rfl
    · rfl

/-- **A branch whose arms' windows allocate nothing allocates nothing.** -/
theorem allocs_ite (σ : Val) {c : V} {wz wn : List W0}
    (hz : (wz.all fun | .run _ => true | .call s => isCallS s) = true)
    (hn : (wn.all fun | .run _ => true | .call s => isCallS s) = true)
    (az : ((atomsW wz).all fun a => !allocAtom a) = true) (an : ((atomsW wn).all fun a => !allocAtom a) = true)
    {es : List Ev} (h : walk σ [.ite c (flatW wz) (flatW wn)] = .fall es) : allocs σ es = [] := by
  obtain ⟨e1, e2, h1, h2, rfl⟩ := vsSeq_fall (o := walk1 σ (.ite c (flatW wz) (flatW wn))) (o' := walk σ []) h
  cases h2
  rw [List.append_nil]
  simp only [walk1] at h1
  obtain ⟨e, he, rfl⟩ := vsPre_fall h1
  rw [show allocs σ ([Ev.inK c] ++ e) = allocs σ e from rfl]
  split at he
  · rw [allocs_wins σ wz hz he, filterMap_alloc_nil σ _ az]
  · rw [allocs_wins σ wn hn he, filterMap_alloc_nil σ _ an]

/-! ## `verify_sub`'s -/

theorem wA_allocA : (atomsW wA).filter allocAtom = [.hint (.alloc (.n 6) 6), .hint (.alloc (.n 7) 156), .hint (.alloc (.n 8) 24), .hint (.alloc (.n 9) 4), .hint (.alloc (.n 10) 153), .hint (.alloc (.n 11) 30), .hint (.alloc (.n 12) 24), .hint (.alloc (.n 13) 25), .hint (.alloc (.n 14) 36), .hint (.alloc (.n 15) 24), .hint (.alloc (.n 16) 6), .hint (.alloc (.n 17) 126), .hint (.alloc (.n 18) 25), .hint (.alloc (.n 19) 12), .hint (.alloc (.n 20) 78), .hint (.alloc (.n 21) 64), .hint (.alloc (.n 22) 30), .hint (.alloc (.n 23) 1), .hint (.allocDyn (.n 55) (.n 54)), .hint (.alloc (.n 56) 6), .hint (.alloc (.n 112) 8)] := by decide +kernel

theorem wC_allocA : (atomsW wC).filter allocAtom = [.hint (.alloc (.n 3039) 16), .hint (.alloc (.n 3040) 64), .hint (.alloc (.n 3553) 64)] := by decide +kernel

theorem wB_noAlloc : ((atomsW wB).all fun a => !allocAtom a) = true := by decide +kernel

theorem arms_noAlloc : ((atomsW wI1).all fun a => !allocAtom a) = true ∧ ((atomsW wI2z).all fun a => !allocAtom a) = true ∧
    ((atomsW wI2n).all fun a => !allocAtom a) = true := by decide +kernel

theorem vs_callsS : (wA.all fun | .run _ => true | .call s => isCallS s) = true ∧
    (wB.all fun | .run _ => true | .call s => isCallS s) = true ∧
    (wC.all fun | .run _ => true | .call s => isCallS s) = true ∧
    (wI1.all fun | .run _ => true | .call s => isCallS s) = true ∧
    (wI2z.all fun | .run _ => true | .call s => isCallS s) = true ∧
    (wI2n.all fun | .run _ => true | .call s => isCallS s) = true := by decide +kernel

/-- **`verify_sub`'s allocations on a walk through its body**: `wA`'s and `wC`'s. -/
theorem vs_allocs (σ : Val) {es : List Ev} (h : walk σ vsSS = .fall es) :
    allocs σ es = vsSz0 ++ [logG (σ (.n 54)), 6, 8] ++ [16, 64, 64] := by
  obtain ⟨cA, cB, cC, c1, c2z, c2n⟩ := vs_callsS
  obtain ⟨a1, a2z, a2n⟩ := arms_noAlloc
  unfold vsSS at h
  rw [walk_append] at h
  obtain ⟨eA, r1, hA, h1, rfl⟩ := vsSeq_fall h
  rw [walk_append] at h1
  obtain ⟨eI, r2, hI, h2, rfl⟩ := vsSeq_fall h1
  rw [walk_append] at h2
  obtain ⟨eB, r3, hB, h3, rfl⟩ := vsSeq_fall h2
  rw [walk_append] at h3
  obtain ⟨eJ, eC, hJ, hC, rfl⟩ := vsSeq_fall h3
  rw [← wA_flat] at hA
  rw [← wB_flat] at hB
  rw [← wC_flat] at hC
  rw [← wI1_flat, show ([] : List Stmt) = flatW [] from rfl] at hI
  rw [← wI2z_flat, ← wI2n_flat] at hJ
  rw [allocs_app, allocs_app, allocs_app, allocs_app, allocs_wins σ wA cA hA, allocs_wins σ wB cB hB,
    allocs_wins σ wC cC hC, allocs_ite σ (by decide) c1 (by decide) a1 hI, allocs_ite σ c2z c2n a2z a2n hJ,
    filterMap_alloc_nil σ _ wB_noAlloc, filterMap_alloc_filter σ (atomsW wA), filterMap_alloc_filter σ (atomsW wC),
    wA_allocA, wC_allocA]
  rfl

/-- **`VsAllocsHyp`**: the stream's size `logG (σ 54) = 256 p`. -/
theorem vsAllocs : VsAllocsHyp := by
  intro x hx ⟨es, hw⟩
  have hv : vsEs x.σ0 = es := by
    show outEvs (walk x.σ0 vsSS) = es
    rw [hw]; rfl
  have hp := VsCtx.p_le hx
  have h42 : x.w 42 = gen ^ x.p := vsW_42 rfl hx.hret
  have h54 : x.σ0 (.n 54) = gen ^ (256 * x.p) := vsW0_54 (rd0 := x.rd0) (w := x.w) rfl h42
  have hlog : logG (x.σ0 (.n 54)) = 256 * x.p := by
    rw [h54, Value.gen_pow_eq_ofK, logG_spec (by omega)]
  rw [hv, vs_allocs x.σ0 hw, hlog]
  rfl

end
end LeanVM.Guest.B1.VsC
