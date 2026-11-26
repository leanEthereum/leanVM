/-
  LeanVM.Guest.B1.VerifySub.CompleteBT

  `verify_sub` complete within its child's bound by a node whose callees are calls of their names
  within their bounds (`Budget.FlatShape`), `open_stacked` at the child's announced shape.
-/

module

public import LeanVM.Guest.B1.VerifySub.CMatch
public import LeanVM.Guest.B1.VerifySub.CompleteB
public import LeanVM.Guest.B1.Place.OsFinal
public import LeanVM.Guest.ChildShape
public import LeanVM.Guest.AcceptableChild

/-!
# `verify_sub` by its callees' trees

The callees' names, bounds and predicates are `VerifySub/BoundsB`'s (`vsNames`, `vsBsAt`, `vsPs`,
`vsTs`, `vsTsAny`, `vsBoundAt`). `vs_names`: the honest child's callees are calls of
`vsNames μ r (d - 20)`, the bus depth `d`.

`vsPsR`: `verify_sub`'s callees' predicates of the memory, `certify_placement`'s `Pcp`, `verify_tables`' `Pvt` beside its weights, `open_stacked`'s `Pos`. `kidsDepBPR_of`: callees by position, each within its bound by a tree of its predicate. `vsQn`: `verify_sub`'s honest valuation, its own buffers held; `VsKidQ`, `vsNames_kidQ`, `kidsT_valid_mem`: its valid callees satisfying their predicates by name.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.Memory

@[expose] public section

theorem vs_names {bytecode : List K} {seed : Digest} {c : Child} (S : ChildSegs bytecode seed c)
    (bs : List ℕ) (sqE : ℕ) :
    List.Forall₂ (fun k n ↦ ∀ pv, (k pv).f = n) (S.kids bs sqE) (vsNames S.μs S.rate (S.d - 20)) :=
  .cons (fun _ ↦ rfl) (.cons (fun _ ↦ rfl) (.cons (fun _ ↦ rfl) (.cons (fun _ ↦ rfl)
    (.cons (fun _ ↦ rfl) (.cons (fun _ ↦ rfl) (.cons (fun _ ↦ rfl) (.cons (fun _ ↦ rfl)
      (.cons (fun _ ↦ rfl) (.cons (fun _ ↦ rfl) (.cons (fun _ ↦ rfl) (.cons (fun _ ↦ rfl)
        (.cons (fun _ ↦ rfl) (.cons (fun _ ↦ rfl) .nil)))))))))))))

/-! ## Callees by name -/

theorem kidsT_valid_mem {P : Core.Program} {rd : Reader} {σ : Val} :
    ∀ (cs : List Call) (Ts : List (Tree → Prop)) (ks : List Tree), Tree.KidsValid P rd σ cs ks →
      KidsT cs Ts ks → cs.length ≤ Ts.length → ∀ t ∈ ks, (∃ a r, t.Valid P rd a r) → ∃ T ∈ Ts, T t
  | [], _, [], _, _, _, t, ht, _ => absurd ht List.not_mem_nil
  | c :: cs, T :: Ts, k :: ks, ⟨_, hc, hk⟩, ⟨h1, h2⟩, hl, t, ht, ⟨a, r, hv⟩ => by
    rcases List.mem_cons.mp ht with rfl | ht
    · by_cases htk : c.taken = true
      · exact ⟨T, List.mem_cons_self, h1 htk⟩
      · have htk' : c.taken = false := by simpa using htk
        simp only [htk', Bool.false_eq_true, ↓reduceIte] at hc
        obtain ⟨⟨f, σ', rfl⟩, -⟩ := hc
        exact hv.elim
    · obtain ⟨T', hT', h⟩ := kidsT_valid_mem cs Ts ks hk h2 (by simpa using hl) t ht ⟨a, r, hv⟩
      exact ⟨T', List.mem_cons_of_mem _ hT', h⟩
  | _ :: _, [], _, _, _, hl, _, _, _ => by simp at hl
  | [], _, _ :: _, h, _, _, _, _, _ => h.elim
  | _ :: _, _ :: _, [], h, _, _, _, _, _ => h.elim

theorem namedP_imp {fs : String → ℕ} {Q : Tree → Prop} : ∀ (ns : List String) (Bs : List ℕ) (Ps : List (Tree → Prop)),
    List.Forall₂ (fun n P => ∀ t, t.name = n → P t → Q t) ns Ps → ∀ T ∈ namedP fs ns Bs Ps, ∀ t, T t → Q t
  | n :: ns, b :: Bs, P :: Ps, .cons h hs, T, hT, t, hTt => by
    rcases List.mem_cons.mp hT with rfl | hT
    · exact h t hTt.1.1 hTt.2
    · exact namedP_imp ns Bs Ps hs T hT t hTt
  | [], _, _, _, _, hT, _, _ => by simp [namedP] at hT
  | _ :: _, [], _, _, _, hT, _, _ => by simp [namedP] at hT
  | _ :: _, _ :: _, [], _, _, hT, _, _ => by simp [namedP] at hT

theorem kidsT_mono' : ∀ (cs : List Call) (Ts Ts' : List (Tree → Prop)) (ks : List Tree),
    List.Forall₂ (fun T T' => ∀ t, T t → T' t) Ts Ts' → KidsT cs Ts ks → KidsT cs Ts' ks
  | _ :: cs, _ :: Ts, _ :: Ts', k :: ks, .cons h hs, ⟨h1, h2⟩ =>
    ⟨fun ht => h k (h1 ht), kidsT_mono' cs Ts Ts' ks hs h2⟩
  | [], _, _, _, _, _ => trivial
  | _ :: _, [], [], _, _, _ => trivial
  | _ :: _, _ :: _, _ :: _, [], _, _ => trivial

theorem flatShape_mono {f : String} {Ts Ts' : List (Tree → Prop)} {t : Tree}
    (h : Budget.FlatShape coreProgram f Ts t) (hT : List.Forall₂ (fun T T' => ∀ t, T t → T' t) Ts Ts') :
    Budget.FlatShape coreProgram f Ts' t := by
  obtain ⟨σ, bufs, ks, rfl, hw⟩ := h
  exact ⟨σ, bufs, ks, rfl, fun fn es vs hf hw' => ⟨by rw [← hT.length_eq]; exact (hw fn es vs hf hw').1,
    kidsT_mono' _ _ _ _ hT (hw fn es vs hf hw').2⟩⟩

theorem namedP_mono {fs : String → ℕ} : ∀ (ns : List String) (Bs : List ℕ) (Ps Ps' : List (Tree → Prop)),
    List.Forall₂ (fun P P' => ∀ t, P t → P' t) Ps Ps' →
    List.Forall₂ (fun T T' => ∀ t, T t → T' t) (namedP fs ns Bs Ps) (namedP fs ns Bs Ps')
  | n :: ns, b :: Bs, P :: Ps, P' :: Ps', .cons h hs =>
    .cons (fun t ht => ⟨ht.1, h t ht.2⟩) (namedP_mono ns Bs Ps Ps' hs)
  | [], _, _, _, _ => by simp [namedP]
  | _ :: _, [], _, _, _ => by simp [namedP]
  | _ :: _, _ :: _, [], [], _ => by simp [namedP]

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-! ## The predicates -/

/-- **`verify_sub`'s callees' predicates of the memory**: `certify_placement`'s `Pcp`, `verify_tables`' weights
and `Pvt`, `open_stacked`'s `Pos`, the terminal's weights. -/
noncomputable def vsPsR (W : VsWordsOs fs) (Pcp Pvt Pos : Reader → Tree → Prop) : List (Reader → Tree → Prop) :=
  List.replicate 3 (fun _ _ ↦ True) ++ [Pcp] ++ List.replicate 5 (fun _ _ ↦ True) ++
    [fun rd t ↦ (∀ op, Budget.WeighsLe coreProgram (W.ωv op) (vtWB W.toVsWords op) t) ∧ Pvt rd t] ++
    List.replicate 2 (fun _ _ ↦ True) ++ [Pos] ++
    [fun _ t ↦ ∀ op, Budget.WeighsLe coreProgram (W.ωv op) (termWB W.toVsWords op) t]

theorem vsPsR_imp (W : VsWordsOs fs) (Pcp Pvt Pos : Reader → Tree → Prop) (rd : Reader) :
    List.Forall₂ (fun P P' => ∀ t, P t → P' t) ((vsPsR W Pcp Pvt Pos).map (· rd)) (vsPs W) := by
  simp only [vsPsR, vsPs, List.replicate_succ, List.replicate_zero, List.cons_append, List.nil_append,
    List.map_cons, List.map_nil, List.forall₂_cons, List.Forall₂.nil, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first | exact fun _ _ => trivial | exact fun _ h => h.1 | exact fun _ h => h

/-- The certification's, the tables' and the opening's entries, by name. -/
def VsKidQ (Pcp Pvt Pos : Reader → Tree → Prop) (rd : Reader) (t : Tree) : Prop :=
  (t.name = "certify_placement" → Pcp rd t) ∧ (t.name = "verify_tables" → Pvt rd t) ∧
    (t.name ∈ vsOpenNames → Pos rd t)

theorem vsKidQ_of {Pcp Pvt Pos : Reader → Tree → Prop} {rd : Reader} {t : Tree} {n : String} (hn : t.name = n)
    (hb : n ∉ "certify_placement" :: "verify_tables" :: vsOpenNames) : VsKidQ Pcp Pvt Pos rd t := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · exact absurd (by rw [← hn, h]; exact List.mem_cons_self) hb
  · exact absurd (by rw [← hn, h]; exact List.mem_cons_of_mem _ List.mem_cons_self) hb
  · exact absurd (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hn ▸ h))) hb

theorem getD_not_mem {l bad : List String} (h : ∀ s ∈ l, s ∉ bad) (h0 : "" ∉ bad) (i : ℕ) : l.getD i "" ∉ bad := by
  rw [List.getD_eq_getElem?_getD]
  rcases hi : l[i]? with _ | s
  · exact h0
  · exact h s (List.mem_of_getElem? hi)

theorem squeeze_not_mem (i : ℕ) : squeezeNames.getD i "" ∉ "certify_placement" :: "verify_tables" :: vsOpenNames :=
  getD_not_mem (by decide) (by decide) i

theorem busGrind_not_mem (i : ℕ) : busGrindNames.getD i "" ∉ "certify_placement" :: "verify_tables" :: vsOpenNames :=
  getD_not_mem (by decide) (by decide) i

theorem openName_ne (μ : ℕ) : Whir.openName μ ∉ ["certify_placement", "verify_tables"] :=
  getD_not_mem (by decide) (by decide) _

/-- **`verify_sub`'s callees' trees satisfy their entries by name.** -/
theorem vsNames_kidQ (W : VsWordsOs fs) (Bvk μ r d : ℕ) (Pcp Pvt Pos : Reader → Tree → Prop) (rd : Reader) :
    ∀ T ∈ namedP fs (vsNames μ r d) (vsBsAt W Bvk μ r) ((vsPsR W Pcp Pvt Pos).map (· rd)), ∀ t, T t →
      VsKidQ Pcp Pvt Pos rd t := by
  refine namedP_imp _ _ _ ?_
  simp only [vsNames, vsPsR, List.replicate_succ, List.replicate_zero, List.cons_append, List.nil_append,
    List.map_cons, List.map_nil, List.forall₂_cons, List.Forall₂.nil, and_true]
  refine ⟨fun t hn _ => vsKidQ_of hn (by decide), fun t hn _ => vsKidQ_of hn (by decide),
    fun t hn _ => vsKidQ_of hn (by decide), fun t hn hp => ⟨fun _ => hp, fun h => absurd (hn.symm.trans h)
      (by decide), fun h => absurd (hn ▸ h) (by decide)⟩, fun t hn _ => vsKidQ_of hn (by decide),
    fun t hn _ => vsKidQ_of hn (squeeze_not_mem _),
    fun t hn _ => vsKidQ_of hn (by decide), fun t hn _ => vsKidQ_of hn (busGrind_not_mem _),
    fun t hn _ => vsKidQ_of hn (by decide), fun t hn hp => ⟨fun h => absurd (hn.symm.trans h) (by decide),
      fun _ => hp.2, fun h => absurd (hn ▸ h) (by decide)⟩, fun t hn _ => vsKidQ_of hn (by decide),
    fun t hn _ => vsKidQ_of hn (by decide), fun t hn hp => ⟨fun h =>
      absurd (by rw [← hn, h]; exact List.mem_cons_self) (openName_ne μ), fun h =>
      absurd (by rw [← hn, h]; exact List.mem_cons_of_mem _ List.mem_cons_self) (openName_ne μ), fun _ => hp⟩,
    fun t hn _ => vsKidQ_of hn (by decide)⟩

/-! ## The callees -/

theorem kidsDepBPR_of {κ : ℕ} : ∀ (ks : List KidD) (Bs : List ℕ) (Ps : List (Reader → Tree → Prop)),
    ks.length = Bs.length → ks.length = Ps.length →
    (∀ j < ks.length, ∀ pv, ((ks.getD j noKid pv).taken = true →
        CompleteAtDTBR fs cert κ (ks.getD j noKid pv).f (ks.getD j noKid pv).Lin
          (ks.getD j noKid pv).args (ks.getD j noKid pv).Out (Ps.getD j fun _ _ ↦ True) (Bs.getD j 0)) ∧
      ((ks.getD j noKid pv).taken = false → fs (tailKey (ks.getD j noKid pv).f) ≤ Bs.getD j 0)) →
    KidsDepBPR fs cert κ ks Bs Ps
  | [], [], [], _, _, _ => trivial
  | [], _ :: _, _, h, _, _ => by simp at h
  | [], [], _ :: _, _, h, _ => by simp at h
  | _ :: _, [], _, h, _, _ => by simp at h
  | _ :: _, _ :: _, [], _, h, _ => by simp at h
  | _ :: ks, _ :: Bs, _ :: Ps, hl, hl', h =>
    ⟨h 0 (by simp), kidsDepBPR_of ks Bs Ps (by simpa using hl) (by simpa using hl')
      fun j hj ↦ h (j + 1) (by simp; omega)⟩

/-! ## `verify_sub` -/

/-- The honest valuation, its own buffers held. -/
def vsQn {bytecode : List K} {seed : Digest} {c : Child} (S : ChildSegs bytecode seed c) (sqE outE : ℕ)
    (rd : Reader) (σ : Val) : Prop :=
  ∃ b outs, σ = vsσ rd (vsW S.gw (bases b (vsSizes)) outs) (vsArgs seed c sqE outE) ∧
    Main.MemL rd (bufL b (vsSizes) S.ownW)

end
end LeanVM.Guest.B1.VerifySub
