/-
  LeanVM.Guest.B1.VsC.VsPost

  `verify_sub`'s final condition `vsPostA` from its skeleton: its pops through its witness hints and its callees'
  lists, its exactness.
-/

module

public import LeanVM.Guest.B1.VsC.VsWins
public import LeanVM.Guest.Complete.PopSkel
public import LeanVM.Guest.Exact.Free

/-!
# `verify_sub`'s final condition

`verify_sub`'s body before its `ret []` is straight parts of atoms, calls and dispatches (`flatB`) around two
branches. On any valuation whose walk falls through, its events' skeleton (`PopSkel.lean`'s `evSkel`) is its
statements' (`skD`: a dispatch is one callee), each branch's taken arm's (`vs_skel`), and every frame is entered.

`vsPostA_of`: `vsPostA` of the node from its walk, the callees' lists (`KOk`, the template `main`'s
`kOk_kids`), its skeleton's entries agreeing stream by stream with `childHints`, and its events exact.

`VsWinHypW`: `VsWinHyp` whose final condition also receives, on each memory, the body's walk and its events
holding (what `SegA` gives), so `vsPostA_of` applies there; `vsWindowsA_of_hypW`.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Node LeanVM.Protocol LeanVM.Protocol.KeccakHash

@[expose] public section

/-! ## The skeleton -/

/-- A statement of a straight part: an atom, a call or a dispatch. -/
def flatB : Stmt → Bool
  | .atom _ | .call .. | .dispatch .. => true
  | _ => false

/-- A straight part's statement's skeleton: a witness hint's entry, or one callee. -/
def skD : Stmt → List PItem
  | .atom a => atomSkel a
  | .call .. | .dispatch .. => [.kid]
  | _ => []

theorem pick_fall {σ : Val} {x : V} {a r : List V} : ∀ {j : ℕ} {fs : List String} {es : List Ev},
    pick σ x a r j fs = .fall es → ∃ f, es = [.call f a r]
  | _, [], _, h => by simp [pick] at h
  | j, f :: fs, es, h => by
    simp only [pick] at h
    split at h
    · exact ⟨f, (Out.fall.inj h).symm⟩
    · exact pick_fall h

theorem seq_fall {o k : Out} {es : List Ev} (h : o.seq k = .fall es) :
    ∃ e1 e2, o = .fall e1 ∧ k = .fall e2 ∧ es = e1 ++ e2 := by
  cases o with
  | fall e1 =>
    cases k with
    | fall e2 => exact ⟨e1, e2, rfl, rfl, (Out.fall.inj h).symm⟩
    | ret _ _ => simp [Out.seq, Out.pre] at h
    | stuck => simp [Out.seq, Out.pre] at h
  | ret _ _ => simp [Out.seq] at h
  | stuck => simp [Out.seq] at h

theorem walk_fall_append {σ : Val} {xs ys : List Stmt} {es : List Ev} (h : walk σ (xs ++ ys) = .fall es) :
    ∃ e1 e2, walk σ xs = .fall e1 ∧ walk σ ys = .fall e2 ∧ es = e1 ++ e2 := by
  rw [Memory.walk_append] at h
  exact seq_fall h

/-- **A straight part's skeleton**: on a walk that falls through, its events' skeleton is its statements', every
frame entered. -/
theorem flat_skel {σ : Val} : ∀ {ss : List Stmt} {es : List Ev}, ss.all flatB = true → walk σ ss = .fall es →
    es.flatMap evSkel = ss.flatMap skD ∧ ∀ c ∈ calls es, c.taken = true
  | [], es, _, h => by
    simp only [walk] at h
    cases h
    simp [calls]
  | s :: ss, es, hok, h => by
    simp only [List.all_cons, Bool.and_eq_true] at hok
    simp only [walk] at h
    obtain ⟨e1, e2, h1, h2, rfl⟩ := seq_fall h
    obtain ⟨ih1, ih2⟩ := flat_skel hok.2 h2
    have hs : e1.flatMap evSkel = skD s ∧ ∀ c ∈ calls e1, c.taken = true := by
      cases s with
      | atom a =>
        simp only [walk1] at h1
        cases h1
        simp [evSkel, skD, calls, Ev.call?]
      | call f args rets =>
        simp only [walk1] at h1
        cases h1
        simp [evSkel, skD, calls, Ev.call?]
      | dispatch x gs args rets =>
        simp only [walk1] at h1
        obtain ⟨g, rfl⟩ := pick_fall h1
        simp [evSkel, skD, calls, Ev.call?]
      | _ => simp [flatB] at hok
    refine ⟨by rw [List.flatMap_append, hs.1, ih1, List.flatMap_cons], fun c hc => ?_⟩
    rw [calls_append, List.mem_append] at hc
    rcases hc with hc | hc
    exacts [hs.2 c hc, ih2 c hc]

/-- **A branch's skeleton**: its taken arm's. -/
theorem ite_skel {σ : Val} {c : V} {z n : List Stmt} {es : List Ev} (hz : z.all flatB = true)
    (hn : n.all flatB = true) (h : walk σ [.ite c z n] = .fall es) :
    es.flatMap evSkel = (if σ c = 0 then z else n).flatMap skD ∧ ∀ c' ∈ calls es, c'.taken = true := by
  simp only [walk] at h
  obtain ⟨e1, e2, h1, h2, rfl⟩ := seq_fall h
  cases h2
  simp only [walk1] at h1
  have key : ∀ {ss : List Stmt}, ss.all flatB = true → (walk σ ss).pre [.inK c] = .fall e1 →
      e1.flatMap evSkel = ss.flatMap skD ∧ ∀ c' ∈ calls e1, c'.taken = true := by
    intro ss hss h1
    cases hw : walk σ ss with
    | fall e =>
      rw [hw] at h1
      simp only [Out.pre] at h1
      cases h1
      obtain ⟨s1, s2⟩ := flat_skel hss hw
      refine ⟨by simp [evSkel, s1], fun c' hc' => s2 c' ?_⟩
      simpa [calls, Ev.call?] using hc'
    | ret _ _ => rw [hw] at h1; simp [Out.pre] at h1
    | stuck => rw [hw] at h1; simp [Out.pre] at h1
  rw [List.append_nil]
  by_cases hc : σ c = 0
  · rw [ite_eq_left hc] at h1 ⊢; exact key hz h1
  · rw [ite_eq_right hc] at h1 ⊢; exact key hn h1

/-- `verify_sub`'s parts are straight. -/
theorem vs_flat : vsA.all flatB = true ∧ vsI1n.all flatB = true ∧ vsB.all flatB = true ∧ vsI2z.all flatB = true ∧
    vsI2n.all flatB = true ∧ vsC.all flatB = true := by
  decide +kernel

set_option maxRecDepth 200000 in
/-- **The parts' skeletons**: the own witness entries `stream_chunks`, `table_logs`, `link_shape`, `split_values`
among the callees, in `childHints`' order. -/
theorem vs_skel_parts :
    vsA.flatMap skD = [.wit "stream_chunks" (.stack [.n 42]), .kid, .kid, .kid,
      .wit "table_logs" (.heap (.n 6) 0 6), .kid, .kid, .kid, .kid, .kid, .kid] ∧
    vsI1n.flatMap skD = [] ∧ vsB.flatMap skD = [.wit "link_shape" (.heap (.n 9) 0 4), .kid] ∧
    vsI2z.flatMap skD = [.kid] ∧ vsI2n.flatMap skD = [] ∧
    vsC.flatMap skD = List.replicate 8 .kid ++ [.wit "split_values" (.heap (.n 14) 0 36)] ++
      List.replicate 14 .kid := by
  decide +kernel

/-- `verify_sub`'s skeleton, its branches' taken arms by their selectors. -/
noncomputable def vsSkel (σ : Val) : List PItem :=
  vsA.flatMap skD ++ (if σ (.n 234) = 0 then [] else vsI1n).flatMap skD ++ vsB.flatMap skD ++
    (if σ (.n 471) = 0 then vsI2z else vsI2n).flatMap skD ++ vsC.flatMap skD

/-- **`verify_sub`'s skeleton** on a walk falling through, every frame entered. -/
theorem vs_skel {σ : Val} {es : List Ev} (h : walk σ vsSS = .fall es) :
    es.flatMap evSkel = vsSkel σ ∧ ∀ c ∈ calls es, c.taken = true := by
  obtain ⟨fA, fI1, fB, fI2z, fI2n, fC⟩ := vs_flat
  unfold vsSS at h
  obtain ⟨eA, r1, hA, h1, rfl⟩ := walk_fall_append h
  obtain ⟨eI1, r2, hI1, h2, rfl⟩ := walk_fall_append h1
  obtain ⟨eB, r3, hB, h3, rfl⟩ := walk_fall_append h2
  obtain ⟨eI2, eC, hI2, hC, rfl⟩ := walk_fall_append h3
  obtain ⟨kA, cA⟩ := flat_skel fA hA
  obtain ⟨kI1, cI1⟩ := ite_skel (by rfl) fI1 hI1
  obtain ⟨kB, cB⟩ := flat_skel fB hB
  obtain ⟨kI2, cI2⟩ := ite_skel fI2z fI2n hI2
  obtain ⟨kC, cC⟩ := flat_skel fC hC
  refine ⟨?_, fun c hc => ?_⟩
  · simp only [List.flatMap_append, kA, kI1, kB, kI2, kC, vsSkel, List.append_assoc]
  · simp only [calls_append, List.mem_append] at hc
    rcases hc with hc | hc | hc | hc | hc
    exacts [cA c hc, cI1 c hc, cB c hc, cI2 c hc, cC c hc]

/-! ## The final condition -/

/-- **`verify_sub`'s final condition** from its walk, its callees' lists (`KOk`), its skeleton's entries agreeing
with `childHints` stream by stream, and its events exact. -/
theorem vsPostA_of {bytecode : List K} {seed : Digest} {c : Child} {rd : Reader} {σ : Val} {es : List Ev}
    {bufs : List ℕ} {ts : List Tree} {Qs : List (Reader → Tree → Prop)} {Ps : List (List Pop)}
    (hw : walk σ vsSS = .fall es) (hK : KOk rd Qs ((calls es).map Call.taken) Ps)
    (hv : Tree.KidsValid coreProgram rd σ (calls es) ts) (hq : KidsPost rd Qs (calls es) ts)
    (hS : SameStreams (skelPops rd σ (es.flatMap evSkel) Ps) (Prover.childHints bytecode seed c))
    (hX : ∀ e ∈ es, e.Exact rd σ) :
    vsPostA bytecode seed c rd (.node "verify_sub" σ bufs ts) := by
  have hwb : walk σ (fn% «verify_sub»).body = .ret es [] := by
    rw [show (fn% «verify_sub»).body = vsSS ++ [.ret []] from vsBody_ss, Memory.walk_append, hw]
    simp [walk, walk1, Out.seq, Out.pre]
  obtain ⟨h1, h2⟩ := kOk_kids hK hv hq
  refine ⟨?_, ?_⟩
  · rw [Tree.pops_node vs_find hwb, splice_skel]
    exact sameStreams_trans (skelPops_streams rd σ _ h1) hS
  · rw [Tree.every_node]
    exact ⟨exactAt_of_walk vs_find hwb hX, h2⟩

/-- **`VsWinHyp`, its final condition also given the body's walk and its events holding** on each memory. -/
def VsWinHypW (al : String → Bool) (k : ℕ) (bytecode : List K) (seed : Digest) : Prop :=
  ∀ (c : Child) (qt qo fp cur : ℕ), VsChildOk bytecode seed c → qt + expTabLen ≤ fp →
    qo + c.freshClaim.cells.length ≤ fp → fp + B2C.fs "verify_sub" ≤ cur →
    (∃ rd, vsPreA seed c qt qo rd) → cur < 2 ^ 60 →
    ∃ (rd0 : Reader) (w : ℕ → E) (Wo : Words),
      WordsInA Wo (fp + 2) (fp + B2C.fs "verify_sub") cur
        (cur + (allocs (vsσ rd0 w seed c qt qo) (vsEs (vsσ rd0 w seed c qt qo))).sum) ∧
      VsHyp B2C.fs al B2C.cert k rd0 w (vsArgs seed c (ptrAt qt) (ptrAt qo))
        (ownData B2C.cert fp cur "verify_sub" (allocs (vsσ rd0 w seed c qt qo) (vsEs (vsσ rd0 w seed c qt qo)))
          (vsEs (vsσ rd0 w seed c qt qo)))
        (vsRegion qt qo c.freshClaim.cells.length) (vsPreA seed c qt qo) (vsSt0 (vsσ rd0 w seed c qt qo) cur Wo)
        fun st => (cur < 2 ^ 60 → st.kc ≤ cur + 2 ^ 40) ∧ ∀ rd, LowDef k rd → vsPreA seed c qt qo rd → st.O rd →
          walk (rdOver (vsσ rd0 w seed c qt qo) rd) vsSS = .fall (vsEs (vsσ rd0 w seed c qt qo)) →
          (∀ ev ∈ vsEs (vsσ rd0 w seed c qt qo), ev.Holds rd (rdOver (vsσ rd0 w seed c qt qo) rd)) → ∀ ts,
          Tree.KidsValid coreProgram rd (rdOver (vsσ rd0 w seed c qt qo) rd) (calls (vsEs (vsσ rd0 w seed c qt qo))) ts →
          KidsPost rd st.Qs (calls (vsEs (vsσ rd0 w seed c qt qo))) ts →
          vsPostA bytecode seed c rd (.node "verify_sub" (rdOver (vsσ rd0 w seed c qt qo) rd)
            (allocs (vsσ rd0 w seed c qt qo) (vsEs (vsσ rd0 w seed c qt qo))) ts)

/-- **`verify_sub`'s window from `VsWinHypW`.** -/
theorem vsWindowsA_of_hypW {al : String → Bool} {k : ℕ} {bytecode : List K} {seed : Digest}
    (h : VsWinHypW al k bytecode seed) : VsWindowsA al k bytecode seed := by
  intro c qt qo fp cur hc ht ho hfc hP hcur
  obtain ⟨rd0, w, Wo, hWo, hH⟩ := h c qt qo fp cur hc ht ho hfc hP hcur
  have ha : (vsArgs seed c (ptrAt qt) (ptrAt qo)).length = 6 := rfl
  obtain ⟨es, st', Qs, hw, hq, hseg, hkc, hK⟩ := vs_seg (fp := fp) ha hH
  have hes : vsEs (vsσ rd0 w seed c qt qo) = es := by
    have h1 : vsEs (vsσ rd0 w seed c qt qo) = outEvs (walk (vsσ rd0 w seed c qt qo) vsSS) := rfl
    exact h1.trans (congrArg outEvs hw)
  have hq' : st'.Qs = Qs := by rw [hq]; rfl
  have ha' : st'.a = cur + (allocs (vsσ rd0 w seed c qt qo) es).sum := hseg.1
  have e0 : (vsSt0 (vsσ rd0 w seed c qt qo) cur Wo).kc = cur + (allocs (vsσ rd0 w seed c qt qo) es).sum := by
    show cur + (allocs _ (vsEs _)).sum = _
    rw [hes]
  rw [hes] at hWo hK
  refine ⟨fn% «verify_sub», vsSS, vsσ rd0 w seed c qt qo, rdOver (vsσ rd0 w seed c qt qo), es, Wo, Qs, st'.O, st'.D,
    st'.kc, hkc, vs_loop, vs_find, vsBody_ss, hWo, ?_, fun rd _ _ _ => ?_, fun rd hl hp ho ts hv hk => ?_⟩
  · rw [hes, ha', e0] at hseg
    exact hseg
  · have hr : ∀ v ∈ (fn% «verify_sub»).params, rdOver (vsσ rd0 w seed c qt qo) rd v = vsσ rd0 w seed c qt qo v :=
      fun v hv => rdOver_eq (by
        rw [vsRcs_eq]; exact Option.isNone_iff_eq_none.mp (List.all_eq_true.mp vs_params_rc v hv))
    rw [List.map_congr_left hr]
    exact vsVal_params ha
  · rw [← hq'] at hk
    obtain ⟨-, -, -, -, -, hr⟩ := hseg
    obtain ⟨hwr, -, -, -, -, -, -, hev⟩ := hr rd hl hp ho
    exact hK rd hl hp ho hwr hev ts hv hk

end
end LeanVM.Guest.B1.VsC
