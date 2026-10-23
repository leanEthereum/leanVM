/-
  LeanVM.Guest.Memory.Discharge

  The honest memory of a placed tree: its range-check temporaries re-chosen to read the final
  memory, every write of the frames and of the paths agrees with one function of the address,
  so the image is consistent and the re-chosen tree is valid on it (`HonestAt`).
-/

module

public import LeanVM.Guest.Memory
public import LeanVM.Guest.Memory.Retemp

/-!
# Discharging `HonestAt`

A range check reads an arbitrary word `g^n`, possibly a frame cell, so its temporaries must hold
what the final memory holds there, and that memory holds the temporaries' own cells. The words
fixed independently of the temporaries (`W`: the frame cells other than temporaries' and the
equations of every atom but range checks) are consistent; a temporary's cell `c` reads its
range check's address `a`. `resolveF` extends `W` to a function of the address with
`F c = F a` for every temporary: the value at the end of the chain `c ↦ a ↦ …` through
temporaries' cells, `0` on a cycle (`resolveF_spec`). Choosing each temporary as `F` at its cell
(`Tree.retemp`), every frame write and every equation of the re-chosen tree agrees with `F`.

**Result** (`honestAt_retemp`): a placed tree valid on a memory image, its loads in its data or in
a region `R` outside every frame but `main`'s header cells `0`, `1` (`Tree.LoadsIn`, at the root),
which the image holds, with the certificate's facts about the cells (temporaries' cells hold only
them, the other cells do not depend on them, `frameAddr` runs at their cells), has a re-chosen
tree that is `HonestAt` on its honest memory.
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

/-! ## Resolving chains of temporaries -/

section Resolve

open Classical

variable {α : Type} (W : K → E → Prop) (Θ : α → Prop) (c a : α → K)

/-- The address a temporary's cell reads. -/
noncomputable def nextR (x : K) : Option K :=
  if h : ∃ τ, Θ τ ∧ c τ = x then some (a (Classical.choose h)) else none

/-- `n` steps along the chain. -/
noncomputable def iterR : ℕ → K → Option K
  | 0, x => some x
  | n + 1, x => (iterR n x).bind (nextR Θ c a)

/-- The chain from `x` ends at `e`. -/
def TermR (x e : K) : Prop := ∃ n, iterR Θ c a n x = some e ∧ nextR Θ c a e = none

/-- The word `W` fixes at `x`, `0` if none. -/
noncomputable def baseR (x : K) : E := if h : ∃ w, W x w then Classical.choose h else 0

/-- **The resolved memory**: `W`'s word at the end of the chain, `0` if it does not end. -/
noncomputable def resolveF (x : K) : E :=
  if h : ∃ e, TermR Θ c a x e then baseR W (Classical.choose h) else 0

variable {W Θ c a}

theorem iterR_succ' : ∀ (n : ℕ) (x : K), iterR Θ c a (n + 1) x = (nextR Θ c a x).bind (iterR Θ c a n)
  | 0, x => by simp [iterR]
  | n + 1, x => by
      rw [iterR, iterR_succ' n x, Option.bind_assoc]
      rfl

theorem iterR_none : ∀ {n m : ℕ} {x : K}, n ≤ m → iterR Θ c a n x = none → iterR Θ c a m x = none
  | n, m, x, hnm, h => by
      induction m with
      | zero => obtain rfl : n = 0 := by omega
                exact h
      | succ m ih =>
          rcases Nat.lt_or_ge n (m + 1) with hlt | hge
          · rw [iterR, ih (by omega)]; rfl
          · obtain rfl : n = m + 1 := by omega
            exact h

theorem termR_unique {x e e' : K} (h : TermR Θ c a x e) (h' : TermR Θ c a x e') : e = e' := by
  obtain ⟨n, hn, he⟩ := h
  obtain ⟨n', hn', he'⟩ := h'
  have step : ∀ {n m e}, n < m → iterR Θ c a n x = some e → nextR Θ c a e = none →
      iterR Θ c a m x = none := fun {n m e} hlt hn he =>
    iterR_none (n := n + 1) (by omega) (by rw [iterR, hn]; exact he)
  rcases Nat.lt_trichotomy n n' with hlt | rfl | hgt
  · rw [step hlt hn he] at hn'; cases hn'
  · rw [hn] at hn'; exact Option.some.inj hn'
  · rw [step hgt hn' he'] at hn; cases hn

theorem termR_of_next {x y : K} (hxy : nextR Θ c a x = some y) {e : K} :
    TermR Θ c a x e ↔ TermR Θ c a y e := by
  constructor
  · rintro ⟨n, hn, he⟩
    cases n with
    | zero =>
        simp only [iterR, Option.some.injEq] at hn
        subst hn
        rw [hxy] at he; cases he
    | succ m =>
        rw [iterR_succ', hxy] at hn
        exact ⟨m, hn, he⟩
  · rintro ⟨m, hm, he⟩
    exact ⟨m + 1, by rw [iterR_succ', hxy]; exact hm, he⟩

theorem resolveF_none {x : K} (hx : nextR Θ c a x = none) : resolveF W Θ c a x = baseR W x := by
  have ht : TermR Θ c a x x := ⟨0, rfl, hx⟩
  have hex : ∃ e, TermR Θ c a x e := ⟨x, ht⟩
  simp only [resolveF, hex, ↓reduceDIte]
  rw [termR_unique (Classical.choose_spec hex) ht]

theorem resolveF_next {x y : K} (hxy : nextR Θ c a x = some y) :
    resolveF W Θ c a x = resolveF W Θ c a y := by
  unfold resolveF
  by_cases hy : ∃ e, TermR Θ c a y e
  · have hx : ∃ e, TermR Θ c a x e := let ⟨e, he⟩ := hy; ⟨e, (termR_of_next hxy).mpr he⟩
    simp only [hx, hy, ↓reduceDIte]
    rw [termR_unique (Classical.choose_spec hx) ((termR_of_next hxy).mpr (Classical.choose_spec hy))]
  · have hx : ¬ ∃ e, TermR Θ c a x e := fun ⟨e, he⟩ => hy ⟨e, (termR_of_next hxy).mp he⟩
    simp only [hx, hy, ↓reduceDIte]

/-- **The resolved memory extends `W` and gives each temporary's cell its address's word.** -/
theorem resolveF_spec (hW : ∀ x w w', W x w → W x w' → w = w')
    (hc : ∀ τ τ', Θ τ → Θ τ' → c τ = c τ' → a τ = a τ') (hcW : ∀ τ w, Θ τ → ¬ W (c τ) w) :
    (∀ x w, W x w → resolveF W Θ c a x = w) ∧ ∀ τ, Θ τ → resolveF W Θ c a (c τ) = resolveF W Θ c a (a τ) := by
  refine ⟨fun x w hw => ?_, fun τ hτ => ?_⟩
  · have hx : nextR Θ c a x = none := by
      have hn : ¬ ∃ τ, Θ τ ∧ c τ = x := by
        rintro ⟨τ, hτ, rfl⟩
        exact hcW τ w hτ hw
      simp only [nextR, hn, ↓reduceDIte]
    rw [resolveF_none hx]
    have hex : ∃ w, W x w := ⟨w, hw⟩
    simp only [baseR, hex, ↓reduceDIte]
    exact hW x _ _ (Classical.choose_spec hex) hw
  · have hex : ∃ τ', Θ τ' ∧ c τ' = c τ := ⟨τ, hτ, rfl⟩
    have hn : nextR Θ c a (c τ) = some (a τ) := by
      simp only [nextR, hex, ↓reduceDIte]
      have := Classical.choose_spec hex
      rw [hc _ τ this.1 hτ this.2]
    exact resolveF_next hn

end Resolve

/-! ## The instances of a re-chosen tree -/

section Insts

variable {P : Core.Program} {fs : String → ℕ} {ν : ℕ → String → Val → V → E}
  {H H' : Inst → ℕ → E × E}

mutual
/-- **Every instance of the re-chosen tree is an instance of the tree re-chosen**, at the same
frame. -/
theorem insts_retemp : ∀ (t : Tree) (fp : ℕ) (hdr hdr' : E × E),
    ∀ I' ∈ (t.retemp P fs ν fp).insts fs P.loop H' fp hdr',
      ∃ I ∈ t.insts fs P.loop H fp hdr, I.fp = I'.fp ∧ I'.t = I.t.retemp P fs ν I.fp
  | .node f σ bufs kids, fp, hdr, hdr', I', hI' => by
      rw [retemp_node, insts_node, List.mem_cons] at hI'
      rw [map_total_retempKids_kidPos] at hI'
      rcases hI' with rfl | hI'
      · refine ⟨⟨.node f σ bufs kids, fp, hdr, kidPos fs P.loop fp f bufs (kids.map (Tree.total fs)),
          bases (bufBase fs P.loop fp f (kids.map (Tree.total fs))) bufs⟩,
          by rw [insts_node]; exact List.mem_cons_self, rfl, ?_⟩
        simp only
        rw [retemp_node]
      · obtain ⟨I, hI, h⟩ := instsKids_retemp kids _ _ _ 0 I' hI'
        exact ⟨I, by rw [insts_node]; exact List.mem_cons_of_mem _ hI, h⟩
  | .phantom f σ, fp, hdr, hdr', I', hI' => by
      rw [retemp_phantom, insts_phantom, List.mem_singleton] at hI'
      subst hI'
      exact ⟨⟨.phantom f σ, fp, hdr, [], []⟩, by rw [insts_phantom]; exact List.mem_singleton_self _,
        rfl, by simp only; rw [retemp_phantom]⟩

/-- `insts_retemp` for the callees at `ps`. -/
theorem instsKids_retemp : ∀ (ks : List Tree) (ps : List ℕ) (J J' : Inst) (j : ℕ),
    ∀ I' ∈ Tree.instsKids fs P.loop H' J' j ps (Tree.retempKids P fs ν ps ks),
      ∃ I ∈ Tree.instsKids fs P.loop H J j ps ks, I.fp = I'.fp ∧ I'.t = I.t.retemp P fs ν I.fp
  | [], _, _, _, _, I', hI' => by
      rw [retempKids_nil, instsKids_nil] at hI'; exact (List.not_mem_nil hI').elim
  | _ :: _, [], _, _, _, I', hI' => by
      rw [instsKids_nil_left] at hI'; exact (List.not_mem_nil hI').elim
  | k :: ks, p :: ps, J, J', j, I', hI' => by
      rw [retempKids_cons, instsKids_cons, List.mem_append] at hI'
      rw [instsKids_cons]
      rcases hI' with hI' | hI'
      · obtain ⟨I, hI, h⟩ := insts_retemp k p (H J j) _ I' hI'
        exact ⟨I, List.mem_append_left _ hI, h⟩
      · obtain ⟨I, hI, h⟩ := instsKids_retemp ks ps J J' (j + 1) I' hI'
        exact ⟨I, List.mem_append_right _ hI, h⟩
end

variable (P fs ν) in
/-- The local conditions of `Tree.ReadsAs` at a node. -/
def ReadsAt (rd rd0 : Reader) (fp : ℕ) (f : String) (σ : Val) (es : List Ev) : Prop :=
  (∀ a, Ev.atom a ∈ es → atomTmps a = [] → ∀ q ∈ atomEqns σ a, rd q.1 = rd0 q.1) ∧
    ∀ x y t1 t2 k, Ev.atom (.rangeCheck x y t1 t2 k) ∈ es →
      rd ((σ x).limb 0 * gpow 0) = some (ν fp f σ t1) ∧
        rd ((σ y).limb 0 * gpow 0) = some (ν fp f σ t2)

mutual
/-- **`Tree.ReadsAs` from its instances**: the local conditions at every node instance. -/
theorem readsAs_of_insts {rd rd0 : Reader} : ∀ (t : Tree) (fp : ℕ) (hdr : E × E),
    (∀ I ∈ t.insts fs P.loop H fp hdr, ∀ f σ bufs kids, I.t = .node f σ bufs kids →
      ReadsAt ν rd rd0 I.fp f σ (I.t.events P)) → t.ReadsAs P fs ν rd rd0 fp
  | .node f σ bufs kids, fp, hdr, h => by
      have h0 := h _ (by rw [insts_node]; exact List.mem_cons_self) f σ bufs kids rfl
      rw [readsAs_node]
      exact ⟨h0.1, h0.2, readsAsKids_of_insts kids _ _ 0 fun I hI =>
        h I (by rw [insts_node]; exact List.mem_cons_of_mem _ hI)⟩
  | .phantom .., _, _, _ => by rw [Tree.ReadsAs]; trivial

/-- `readsAs_of_insts` for the callees. -/
theorem readsAsKids_of_insts {rd rd0 : Reader} : ∀ (ks : List Tree) (ps : List ℕ) (J : Inst) (j : ℕ),
    (∀ I ∈ Tree.instsKids fs P.loop H J j ps ks, ∀ f σ bufs kids, I.t = .node f σ bufs kids →
      ReadsAt ν rd rd0 I.fp f σ (I.t.events P)) → Tree.ReadsAsKids P fs ν rd rd0 ps ks
  | [], ps, _, _, _ => by cases ps <;> (rw [Tree.ReadsAsKids]; trivial)
  | _ :: _, [], _, _, _ => by rw [Tree.ReadsAsKids]; trivial
  | k :: ks, p :: ps, J, j, h => by
      rw [readsAsKids_cons]
      exact ⟨readsAs_of_insts k p (H J j) fun I hI =>
          h I (by rw [instsKids_cons]; exact List.mem_append_left _ hI),
        readsAsKids_of_insts ks ps J (j + 1) fun I hI =>
          h I (by rw [instsKids_cons]; exact List.mem_append_right _ hI)⟩
end

theorem node_of_retemp {fp : ℕ} : ∀ {t : Tree} {f : String} {σ' : Val} {bufs : List ℕ}
    {kids' : List Tree}, t.retemp P fs ν fp = .node f σ' bufs kids' →
      ∃ σ kids, t = .node f σ bufs kids ∧ σ' = retempVal P ν fp f σ
  | .node g σ bs ks, f, σ', bufs, kids', h => by
      rw [retemp_node] at h
      cases h
      exact ⟨σ, ks, rfl, rfl⟩
  | .phantom .., _, _, _, _, h => by rw [retemp_phantom] at h; cases h

mutual
/-- **Every instance of the tree has its re-chosen instance**, at the same frame. -/
theorem insts_retemp_fwd : ∀ (t : Tree) (fp : ℕ) (hdr hdr' : E × E),
    ∀ I ∈ t.insts fs P.loop H fp hdr,
      ∃ I' ∈ (t.retemp P fs ν fp).insts fs P.loop H' fp hdr', I'.fp = I.fp ∧ I'.t = I.t.retemp P fs ν I.fp
  | .node f σ bufs kids, fp, hdr, hdr', I, hI => by
      rw [insts_node, List.mem_cons] at hI
      rcases hI with rfl | hI
      · refine ⟨⟨(Tree.node f σ bufs kids).retemp P fs ν fp, fp, hdr',
          kidPos fs P.loop fp f bufs (kids.map (Tree.total fs)),
          bases (bufBase fs P.loop fp f (kids.map (Tree.total fs))) bufs⟩, ?_, rfl, rfl⟩
        rw [retemp_node, insts_node, map_total_retempKids_kidPos]
        exact List.mem_cons_self
      · obtain ⟨I', hI', h⟩ := instsKids_retemp_fwd kids _ _ ⟨(Tree.node f σ bufs kids).retemp P fs ν fp, fp,
          hdr', kidPos fs P.loop fp f bufs (kids.map (Tree.total fs)),
          bases (bufBase fs P.loop fp f (kids.map (Tree.total fs))) bufs⟩ 0 I hI
        refine ⟨I', ?_, h⟩
        rw [retemp_node, insts_node, map_total_retempKids_kidPos]
        exact List.mem_cons_of_mem _ (by rw [← retemp_node]; exact hI')
  | .phantom f σ, fp, hdr, hdr', I, hI => by
      rw [insts_phantom, List.mem_singleton] at hI
      subst hI
      refine ⟨⟨.phantom f σ, fp, hdr', [], []⟩, ?_, rfl, ?_⟩
      · rw [retemp_phantom, insts_phantom]; exact List.mem_singleton_self _
      · simp only; rw [retemp_phantom]

/-- `insts_retemp_fwd` for the callees at `ps`. -/
theorem instsKids_retemp_fwd : ∀ (ks : List Tree) (ps : List ℕ) (J J' : Inst) (j : ℕ),
    ∀ I ∈ Tree.instsKids fs P.loop H J j ps ks,
      ∃ I' ∈ Tree.instsKids fs P.loop H' J' j ps (Tree.retempKids P fs ν ps ks),
        I'.fp = I.fp ∧ I'.t = I.t.retemp P fs ν I.fp
  | [], _, _, _, _, I, hI => by rw [instsKids_nil] at hI; exact (List.not_mem_nil hI).elim
  | _ :: _, [], _, _, _, I, hI => by rw [instsKids_nil_left] at hI; exact (List.not_mem_nil hI).elim
  | k :: ks, p :: ps, J, J', j, I, hI => by
      rw [instsKids_cons, List.mem_append] at hI
      rw [retempKids_cons, instsKids_cons]
      rcases hI with hI | hI
      · obtain ⟨I', hI', h⟩ := insts_retemp_fwd k p (H J j) (H' J' j) I hI
        exact ⟨I', List.mem_append_left _ hI', h⟩
      · obtain ⟨I', hI', h⟩ := instsKids_retemp_fwd ks ps J J' (j + 1) I hI
        exact ⟨I', List.mem_append_right _ hI', h⟩
end

end Insts

/-! ## Equations and data of instances -/

section Parts

variable {P : Core.Program} {fs : String → ℕ} {lp : String → Bool} {H : Inst → ℕ → E × E}

mutual
/-- **An atom's equation on a node instance's path is an equation of the tree.** -/
theorem eqns_of_insts : ∀ (t : Tree) (fp : ℕ) (hdr : E × E), ∀ I ∈ t.insts fs lp H fp hdr,
    (∃ f σ bufs kids, I.t = .node f σ bufs kids) → ∀ a, Ev.atom a ∈ I.t.events P →
      ∀ q ∈ atomEqns I.t.val a, q ∈ t.eqns P
  | .node f σ bufs kids, fp, hdr, I, hI, hn, a, ha, q, hq => by
      rw [insts_node, List.mem_cons] at hI
      rw [Tree.eqns, List.mem_append]
      rcases hI with rfl | hI
      · exact Or.inl (mem_evEqns ha hq)
      · exact Or.inr (eqnsKids_of_insts kids _ _ 0 I hI hn a ha q hq)
  | .phantom .., fp, hdr, I, hI, hn, _, _, _, _ => by
      rw [insts_phantom, List.mem_singleton] at hI
      subst hI
      obtain ⟨_, _, _, _, h⟩ := hn
      cases h

/-- `eqns_of_insts` for the callees. -/
theorem eqnsKids_of_insts : ∀ (ks : List Tree) (ps : List ℕ) (J : Inst) (j : ℕ),
    ∀ I ∈ Tree.instsKids fs lp H J j ps ks, (∃ f σ bufs kids, I.t = .node f σ bufs kids) →
      ∀ a, Ev.atom a ∈ I.t.events P → ∀ q ∈ atomEqns I.t.val a, q ∈ Tree.eqnsKids P ks
  | [], _, _, _, I, hI, _, _, _, _, _ => by
      rw [instsKids_nil] at hI; exact (List.not_mem_nil hI).elim
  | _ :: _, [], _, _, I, hI, _, _, _, _, _ => by
      rw [instsKids_nil_left] at hI; exact (List.not_mem_nil hI).elim
  | k :: ks, p :: ps, J, j, I, hI, hn, a, ha, q, hq => by
      rw [instsKids_cons, List.mem_append] at hI
      rw [Tree.eqnsKids, List.mem_append]
      rcases hI with hI | hI
      · exact Or.inl (eqns_of_insts k p _ I hI hn a ha q hq)
      · exact Or.inr (eqnsKids_of_insts ks ps J (j + 1) I hI hn a ha q hq)
end

variable {cert : String → V → ℕ}

mutual
/-- **A word of a tree's data is a `HeapBuf` word or a run cell of one of its instances.** -/
theorem data_insts : ∀ (t : Tree) (fp : ℕ) (hdr : E × E) (i : ℕ), t.Data P fs cert fp i →
    ∃ K ∈ t.insts fs P.loop H fp hdr, K.Buf i ∨ ∃ f σ bufs kids, K.t = .node f σ bufs kids ∧
      ∃ q ∈ runs (K.t.events P), K.fp + cert f q.1 ≤ i ∧ i < K.fp + cert f q.1 + q.2
  | .node f σ bufs kids, fp, hdr, i, h => by
      rw [data_node] at h
      have hroot : (⟨.node f σ bufs kids, fp, hdr, kidPos fs P.loop fp f bufs (kids.map (Tree.total fs)),
          bases (bufBase fs P.loop fp f (kids.map (Tree.total fs))) bufs⟩ : Inst) ∈
          (Tree.node f σ bufs kids).insts fs P.loop H fp hdr := by
        rw [insts_node]; exact List.mem_cons_self
      rcases h with (h | h) | h
      · exact ⟨_, hroot, Or.inl h⟩
      · exact ⟨_, hroot, Or.inr ⟨f, σ, bufs, kids, rfl, h⟩⟩
      · obtain ⟨K, hK, h⟩ := dataKids_insts kids _ _ 0 i h
        exact ⟨K, by rw [insts_node]; exact List.mem_cons_of_mem _ hK, h⟩
  | .phantom .., _, _, _, h => (data_phantom h).elim

/-- `data_insts` for the callees. -/
theorem dataKids_insts : ∀ (ks : List Tree) (ps : List ℕ) (J : Inst) (j : ℕ) (i : ℕ),
    Tree.DataKids P fs cert ps ks i →
    ∃ K ∈ Tree.instsKids fs P.loop H J j ps ks, K.Buf i ∨ ∃ f σ bufs kids,
      K.t = .node f σ bufs kids ∧
      ∃ q ∈ runs (K.t.events P), K.fp + cert f q.1 ≤ i ∧ i < K.fp + cert f q.1 + q.2
  | [], _, _, _, _, h => (not_dataKids_nil h).elim
  | _ :: _, [], _, _, _, h => by rw [Tree.DataKids] at h; exact h.elim
  | k :: ks, p :: ps, J, j, i, h => by
      rw [dataKids_cons] at h
      rw [instsKids_cons]
      rcases h with h | h
      · obtain ⟨K, hK, h⟩ := data_insts k p (H J j) i h
        exact ⟨K, List.mem_append_left _ hK, h⟩
      · obtain ⟨K, hK, h⟩ := dataKids_insts ks ps J (j + 1) i h
        exact ⟨K, List.mem_append_right _ hK, h⟩
end

end Parts

/-! ## The discharge -/

section Main

variable {P : Core.Program} {fs : String → ℕ} {cert : String → V → ℕ}

/-- Offset `o` of the instance `t` holds a temporary of its function. -/
def TmpOff (P : Core.Program) (cert : String → V → ℕ) (t : Tree) (o : ℕ) : Prop :=
  ∃ f σ bufs kids, t = .node f σ bufs kids ∧ ∃ v ∈ P.temps f, o = cert f v

theorem temps_of_rcRead {f : String} {σ : Val} {t : V} {A : K} (h : RcRead P f σ t A) :
    t ∈ P.temps f := by
  obtain ⟨x, y, t1, t2, k, he, hA⟩ := h
  unfold Tree.events at he
  simp only [Tree.name, Tree.val] at he
  cases hf : P.find? f with
  | none => rw [hf] at he; exact (List.not_mem_nil he).elim
  | some fn =>
      rw [hf] at he
      dsimp only at he
      cases hw : walk σ fn.body with
      | fall es => rw [hw] at he; exact (List.not_mem_nil he).elim
      | stuck => rw [hw] at he; exact (List.not_mem_nil he).elim
      | ret es vs =>
          rw [hw] at he
          have := mem_temps_of_event hf hw he
          rcases hA with ⟨rfl, -⟩ | ⟨rfl, -⟩
          · exact this.1
          · exact this.2

theorem atomEqns_congr {σ σ' : Val} : ∀ (a : Atom), atomTmps a = [] →
    (∀ v ∈ atomUses a, σ' v = σ v) → atomEqns σ' a = atomEqns σ a
  | .load d p off, _, h => by
      simp only [atomEqns, h d (by simp [atomUses]), h p (by simp [atomUses])]
  | .frameAddr p run, _, h => by
      simp only [atomEqns, h p (by simp [atomUses])]
      refine List.ext_getElem (by simp) fun k h1 h2 => ?_
      simp only [List.getElem_mapIdx]
      rw [h _ (List.mem_cons_of_mem _ (List.getElem_mem (by simpa using h1)))]
  | .rangeCheck .., ht, _ => by simp [atomTmps] at ht
  | .const .., _, _ => rfl
  | .add .., _, _ => rfl
  | .mul .., _, _ => rfl
  | .copy .., _, _ => rfl
  | .assertEq .., _, _ => rfl
  | .assertNe .., _, _ => rfl
  | .assertInK .., _, _ => rfl
  | .blake2s .., _, _ => rfl
  | .hint _, _, _ => rfl

variable (P fs cert) in
/-- **What the discharge needs**: a placed tree valid on a memory image, its loads in its data
or in a region `R` outside every frame but `main`'s header cells `0`, `1`, which the image holds,
and the certificate's facts about the cells (for every re-choice `ν` of the temporaries): the
cells fit, a temporary's cells hold only it, the other cells are the old tree's, `frameAddr` runs
at their certificate cells, none a temporary's. -/
structure DischargeHyps (H : Inst → ℕ → E × E) (C : Inst → List (ℕ × E)) (hdr : E × E)
    (T : Tree) (R : ℕ → Prop) (M : MemImage (logMem (T.total fs))) (args rets : List E) : Prop where
  fresh : P.Fresh
  valid : T.Valid P M.read args rets
  bufsOk : T.BufsOk P
  placed : T.Placed P fs cert 0
  loads : T.LoadsIn P fs cert R 0
  region : ∀ i, R i → i < 2 ∨ ∀ I ∈ honestInsts P fs H hdr T, ∀ o < fs I.t.name,
    gpow i ≠ gpow (I.fp + o)
  hdr_read : M.read (gpow 0) = some hdr.1 ∧ M.read (gpow 1) = some hdr.2
  size : T.total fs ≤ 2 ^ 32
  addr : ∀ q ∈ T.eqns P, ∃ i : Fin (2 ^ logMem (T.total fs)), q.1 = gpow i
  cells : CellsOk fs C (honestInsts P fs H hdr T)
  cells' : ∀ ν, CellsOk fs C (honestInsts P fs H hdr (T.retemp P fs ν 0))
  cert_lt : ∀ f, ∀ t ∈ P.temps f, 2 ≤ cert f t ∧ cert f t < fs f
  cert_inj : ∀ f, ∀ t ∈ P.temps f, ∀ t' ∈ P.temps f, cert f t = cert f t' → t = t'
  run : ∀ I ∈ honestInsts P fs H hdr T, ∀ f σ bufs kids, I.t = .node f σ bufs kids →
    ∀ p r rs, Ev.atom (.frameAddr p (r :: rs)) ∈ I.t.events P →
      ∀ (k : ℕ) (hk : k < (r :: rs).length), (cert f r + k, σ (r :: rs)[k]) ∈ C I ∧
        ∀ t ∈ P.temps f, cert f r + k ≠ cert f t
  tmp : ∀ ν, ∀ I' ∈ honestInsts P fs H hdr (T.retemp P fs ν 0), ∀ f σ bufs kids,
    I'.t = .node f σ bufs kids → ∀ t ∈ P.temps f, ∀ q ∈ C I', q.1 = cert f t → q.2 = σ t
  keep : ∀ ν, ∀ I ∈ honestInsts P fs H hdr T, ∀ I' ∈ honestInsts P fs H hdr (T.retemp P fs ν 0),
    I'.fp = I.fp → I'.t = I.t.retemp P fs ν I.fp → ∀ q ∈ I'.cells C, ¬ TmpOff P cert I.t q.1 →
      q ∈ I.cells C

variable {H : Inst → ℕ → E × E} {C : Inst → List (ℕ × E)} {hdr : E × E} {T : Tree}
  {R : ℕ → Prop} {M : MemImage (logMem (T.total fs))} {args rets : List E}

variable (P fs cert H C hdr T) in
/-- The words fixed independently of the temporaries: frame cells other than temporaries', and
the equations of every atom but range checks. -/
def FixedW (x : K) (w : E) : Prop :=
  (∃ I ∈ honestInsts P fs H hdr T, ∃ q ∈ I.cells C, x = gpow (I.fp + q.1) ∧ w = q.2 ∧
      ¬ TmpOff P cert I.t q.1) ∨
    ∃ I ∈ honestInsts P fs H hdr T, (∃ f σ bufs kids, I.t = .node f σ bufs kids) ∧
      ∃ a, Ev.atom a ∈ I.t.events P ∧ atomTmps a = [] ∧ (x, w) ∈ atomEqns I.t.val a

variable (P fs H hdr T) in
/-- The temporaries on the paths: an instance, a temporary, the address its range check reads. -/
def TempsOn (τ : Inst × V × K) : Prop :=
  τ.1 ∈ honestInsts P fs H hdr T ∧ ∃ f σ bufs kids, τ.1.t = .node f σ bufs kids ∧ RcRead P f σ τ.2.1 τ.2.2

/-- A temporary's cell. -/
def tempCell (cert : String → V → ℕ) (τ : Inst × V × K) : K := gpow (τ.1.fp + cert τ.1.t.name τ.2.1)

section Proof

variable (h : DischargeHyps P fs cert H C hdr T R M args rets)
include h

theorem DischargeHyps.within {I : Inst} (hI : I ∈ honestInsts P fs H hdr T) {o : ℕ}
    (ho : o < fs I.t.name) : I.fp + o < T.total fs := by
  have := honest_within (P := P) hI (by have := h.cells.two_le I hI; omega)
  omega

theorem DischargeHyps.inj {x y : ℕ} (hx : x < T.total fs) (hy : y < T.total fs)
    (he : gpow x = gpow y) : x = y := by
  have := h.size
  exact gpow_injOn (by simp only [Set.mem_Iio]; omega) (by simp only [Set.mem_Iio]; omega) he

omit h in
theorem insts_same {I J : Inst} (hI : I ∈ honestInsts P fs H hdr T)
    (hJ : J ∈ honestInsts P fs H hdr T) {i : ℕ} (hFI : I.Frame fs i) (hFJ : J.Frame fs i) : I = J := by
  by_contra hne
  exact (insts_pairwise T 0 hdr).forall hI hJ hne i (Or.inl hFI) (Or.inl hFJ)

theorem DischargeHyps.frames_consistent : Consistent (frameWrites C (honestInsts P fs H hdr T)) :=
  frameWrites_consistent (insts_pairwise T 0 hdr) h.cells fun I hI => by
    have := honest_within (P := P) hI (by have := h.cells.two_le I hI; omega)
    have := h.size
    omega

theorem DischargeHyps.lt_64 : logMem (T.total fs) < 64 := by
  have := logMem_le_maxLogMem h.size; unfold maxLogMem at this; omega

theorem DischargeHyps.eqns_consistent : Consistent (T.eqns P) :=
  h.valid.eqns_consistent h.lt_64 h.addr

/-- **Where a non-range-check equation lies**: a `HeapBuf`, the region, or a run cell whose
`frameAddr` equation is the tree's. -/
theorem DischargeHyps.classify {q : Write}
    {I : Inst} (hI : I ∈ honestInsts P fs H hdr T) {f : String} {σ : Val} {bufs : List ℕ}
    {kids : List Tree} (ht : I.t = .node f σ bufs kids) {a : Atom} (ha : Ev.atom a ∈ I.t.events P)
    (hta : atomTmps a = []) (hq : q ∈ atomEqns σ a) :
    (∃ K ∈ honestInsts P fs H hdr T, ∃ i, K.Buf i ∧ q.1 = gpow i) ∨ (∃ i, R i ∧ q.1 = gpow i) ∨
      ∃ K ∈ honestInsts P fs H hdr T, ∃ g σK bufsK kidsK, K.t = .node g σK bufsK kidsK ∧
        ∃ pK r rs, Ev.atom (.frameAddr pK (r :: rs)) ∈ K.t.events P ∧
          ∃ (k : ℕ) (hk : k < (r :: rs).length), q.1 = gpow (K.fp + (cert g r + k)) ∧
            (q.1, σK (r :: rs)[k]) ∈ T.eqns P := by
  have hpl : ∀ {K : Inst}, K ∈ honestInsts P fs H hdr T → ∀ {g σK bufsK kidsK},
      K.t = .node g σK bufsK kidsK → ∀ {pK r rs}, Ev.atom (.frameAddr pK (r :: rs)) ∈ K.t.events P →
      σK pK = ofK (gpow (K.fp + cert g r)) := fun {K} hK {g σK bufsK kidsK} hKt {pK r rs} he =>
    (Inst.nodeAt (insts_placedAt T 0 hdr h.placed K hK) (insts_placed T 0 hdr K hK) hKt).2 (pK, r)
      (List.mem_filterMap.mpr ⟨_, he, rfl⟩)
  have hrunEq : ∀ {K : Inst}, K ∈ honestInsts P fs H hdr T → ∀ {g σK bufsK kidsK},
      K.t = .node g σK bufsK kidsK → ∀ {pK r rs}, Ev.atom (.frameAddr pK (r :: rs)) ∈ K.t.events P →
      ∀ (k : ℕ) (hk : k < (r :: rs).length),
        (gpow (K.fp + (cert g r + k)), σK (r :: rs)[k]) ∈ T.eqns P := by
    intro K hK g σK bufsK kidsK hKt pK r rs he k hk
    have hm : ((σK pK).limb 0 * gpow k, σK (r :: rs)[k]) ∈ atomEqns σK (.frameAddr pK (r :: rs)) :=
      List.mem_mapIdx.mpr ⟨k, hk, rfl⟩
    have := eqns_of_insts (P := P) T 0 hdr K hK ⟨g, σK, bufsK, kidsK, hKt⟩ _ he _
      (by rw [hKt]; exact hm)
    rw [hpl hK hKt he, show (ofK (gpow (K.fp + cert g r))).limb 0 = gpow (K.fp + cert g r) by simp,
      show gpow (K.fp + cert g r) * gpow k = gpow (K.fp + (cert g r + k)) by
        simp only [gpow, pow_add, mul_assoc]] at this
    exact this
  cases a with
  | load d p off =>
      rw [List.mem_singleton.mp hq]
      obtain ⟨i, hi, hd⟩ := loads_insts T R 0 hdr h.loads I hI ⟨f, σ, bufs, kids, ht⟩ _
        (List.mem_filterMap.mpr ⟨_, ha, by rw [ht]; rfl⟩)
      simp only [Tree.val] at hi
      rcases hd with hd | hR
      · obtain ⟨K, hK, hb | ⟨g, σK, bufsK, kidsK, hKt, qr, hqr, h1, h2⟩⟩ :=
          data_insts (H := H) T 0 hdr i hd
        · exact Or.inl ⟨K, hK, i, hb, hi⟩
        · obtain ⟨e, he, hre⟩ := List.mem_filterMap.mp hqr
          rcases e with ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨pK, _ | ⟨r, rs⟩⟩ | _⟩ | _ | _ | _ <;>
            simp only [Ev.run?, reduceCtorEq, Option.some.injEq] at hre
          subst hre
          simp only at h1 h2
          refine Or.inr (Or.inr ⟨K, hK, g, σK, bufsK, kidsK, hKt, pK, r, rs, he, i - (K.fp + cert g r),
            by simp only [List.length_cons]; omega, ?_, ?_⟩)
          · simp only; rw [hi]; congr 1; omega
          · have := hrunEq hK hKt he (i - (K.fp + cert g r)) (by simp only [List.length_cons]; omega)
            rw [show K.fp + (cert g r + (i - (K.fp + cert g r))) = i by omega] at this
            simp only
            rw [hi]
            exact this
      · exact Or.inr (Or.inl ⟨i, hR, hi⟩)
  | frameAddr p run =>
      obtain ⟨k, hk, rfl⟩ := List.mem_mapIdx.mp hq
      cases run with
      | nil => exact absurd hk (by simp)
      | cons r rs =>
          have he : Ev.atom (.frameAddr p (r :: rs)) ∈ I.t.events P := ha
          have hp := hpl hI ht he
          refine Or.inr (Or.inr ⟨I, hI, f, σ, bufs, kids, ht, p, r, rs, he, k, hk, ?_, ?_⟩)
          · simp only
            rw [hp, show (ofK (gpow (I.fp + cert f r))).limb 0 = gpow (I.fp + cert f r) by simp]
            simp only [gpow, pow_add, mul_assoc]
          · have := hrunEq hI ht he k hk
            simp only
            rw [hp, show (ofK (gpow (I.fp + cert f r))).limb 0 = gpow (I.fp + cert f r) by simp,
              show gpow (I.fp + cert f r) * gpow k = gpow (I.fp + (cert f r + k)) by
                simp only [gpow, pow_add, mul_assoc]]
            exact this
  | rangeCheck _ _ _ _ _ => simp [atomTmps] at hta
  | const _ _ => exact (List.not_mem_nil hq).elim
  | add _ _ _ => exact (List.not_mem_nil hq).elim
  | mul _ _ _ => exact (List.not_mem_nil hq).elim
  | copy _ _ => exact (List.not_mem_nil hq).elim
  | assertEq _ _ => exact (List.not_mem_nil hq).elim
  | assertNe _ _ _ => exact (List.not_mem_nil hq).elim
  | assertInK _ _ => exact (List.not_mem_nil hq).elim
  | blake2s _ _ _ _ _ _ _ _ _ => exact (List.not_mem_nil hq).elim
  | hint _ => exact (List.not_mem_nil hq).elim

omit h in
theorem honest_mem_frameWrites {I : Inst} (hI : I ∈ honestInsts P fs H hdr T) {q : ℕ × E}
    (hq : q ∈ I.cells C) : (gpow (I.fp + q.1), q.2) ∈ frameWrites C (honestInsts P fs H hdr T) :=
  List.mem_flatMap.mpr ⟨I, hI, List.mem_map.mpr ⟨q, hq, rfl⟩⟩

/-- **A non-range-check equation agrees with the frames.** -/
theorem DischargeHyps.cross_fixed {a : Write} (ha : a ∈ frameWrites C (honestInsts P fs H hdr T))
    {I : Inst} (hI : I ∈ honestInsts P fs H hdr T) {f : String} {σ : Val} {bufs : List ℕ}
    {kids : List Tree} (ht : I.t = .node f σ bufs kids) {at' : Atom} (he : Ev.atom at' ∈ I.t.events P)
    (hta : atomTmps at' = []) {q : Write} (hq : q ∈ atomEqns σ at') (hx : a.1 = q.1) : a.2 = q.2 := by
  obtain ⟨J, hJ, c, hc, rfl⟩ := Memory.mem_frameWrites ha
  have hqT : q ∈ T.eqns P := eqns_of_insts T 0 hdr I hI ⟨f, σ, bufs, kids, ht⟩ at' he q (by rw [ht]; exact hq)
  rcases h.classify hI ht he hta hq with ⟨K, hK, i, hb, hqi⟩ | ⟨i, hR, hqi⟩ |
      ⟨K, hK, g, σK, bK, kK, hKt, pK, r, rs, hfa, k, hk, hqi, hqe⟩
  · exact absurd (hx.trans hqi) (frameWrites_not_buf h.cells h.size hK hb _ ha)
  · rcases h.region i hR with hi2 | hR'
    · obtain ⟨I0, hI0, -, hfp0, hh0⟩ := root_inst (P := P) (fs := fs) (H := H) (hdr := hdr) (T := T)
      have hM := h.valid.eqns_read h.lt_64 T q hqT (h.addr q hqT)
      rw [hqi] at hM
      have hrd : ∀ j < 2, (gpow (I0.fp + j), if j = 0 then hdr.1 else hdr.2) ∈
          frameWrites C (honestInsts P fs H hdr T) ∧
            M.read (gpow j) = some (if j = 0 then hdr.1 else hdr.2) := by
        intro j hj
        rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
        · refine ⟨?_, h.hdr_read.1⟩
          have := honest_mem_frameWrites (C := C) hI0 (q := (0, I0.hdr.1)) List.mem_cons_self
          rwa [hh0] at this
        · refine ⟨?_, h.hdr_read.2⟩
          have := honest_mem_frameWrites (C := C) hI0 (q := (1, I0.hdr.2))
            (List.mem_cons_of_mem _ List.mem_cons_self)
          rwa [hh0] at this
      obtain ⟨hw, hr⟩ := hrd i hi2
      have h1 := h.frames_consistent _ ha _ hw (by
        simp only at hx ⊢; rw [hx, hqi, hfp0, Nat.zero_add])
      rw [hM] at hr
      exact h1.trans (Option.some.inj hr).symm
    · exact absurd (hx.trans hqi).symm (hR' J hJ c.1 (h.cells.cell_lt hJ hc))
  · have hrun := (h.run K hK g σK bK kK hKt pK r rs hfa k hk).1
    have hfw := honest_mem_frameWrites hK (q := (cert g r + k, σK (r :: rs)[k]))
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hrun))
    have h1 := h.frames_consistent _ ha _ hfw (by simp only at hx ⊢; rw [hx, hqi])
    have h2 := h.eqns_consistent _ hqe q hqT rfl
    exact h1.trans h2

/-- **The fixed words are consistent.** -/
theorem DischargeHyps.fixed_consistent {x : K} {w w' : E} (hw : FixedW P fs cert H C hdr T x w)
    (hw' : FixedW P fs cert H C hdr T x w') : w = w' := by
  have hfr : ∀ {w}, (∃ I ∈ honestInsts P fs H hdr T, ∃ q ∈ I.cells C, x = gpow (I.fp + q.1) ∧ w = q.2 ∧
      ¬ TmpOff P cert I.t q.1) → (x, w) ∈ frameWrites C (honestInsts P fs H hdr T) := by
    rintro w ⟨I, hI, q, hq, rfl, rfl, -⟩
    exact honest_mem_frameWrites hI hq
  rcases hw with hw | ⟨I, hI, ⟨f, σ, bufs, kids, ht⟩, a, he, hta, hq⟩ <;>
    rcases hw' with hw' | ⟨I', hI', ⟨f', σ', bufs', kids', ht'⟩, a', he', hta', hq'⟩
  · exact h.frames_consistent _ (hfr hw) _ (hfr hw') rfl
  · rw [ht'] at hq'
    exact h.cross_fixed (hfr hw) hI' ht' he' hta' hq' rfl
  · rw [ht] at hq
    exact (h.cross_fixed (hfr hw') hI ht he hta hq rfl).symm
  · have h1 := eqns_of_insts T 0 hdr I hI ⟨f, σ, bufs, kids, ht⟩ a he _ hq
    have h2 := eqns_of_insts T 0 hdr I' hI' ⟨f', σ', bufs', kids', ht'⟩ a' he' _ hq'
    exact h.eqns_consistent _ h1 _ h2 rfl

theorem DischargeHyps.temp_cell {τ : Inst × V × K} (hτ : TempsOn P fs H hdr T τ) :
    ∃ g σ bufs kids, τ.1.t = .node g σ bufs kids ∧ τ.2.1 ∈ P.temps g ∧
      tempCell cert τ = gpow (τ.1.fp + cert g τ.2.1) ∧ τ.1.fp + cert g τ.2.1 < T.total fs ∧
      τ.1.Frame fs (τ.1.fp + cert g τ.2.1) := by
  obtain ⟨hJ, g, σ, bufs, kids, ht, hrc⟩ := hτ
  have hmem := temps_of_rcRead hrc
  have hlt := (h.cert_lt g τ.2.1 hmem).2
  have hn : τ.1.t.name = g := by rw [ht]; rfl
  exact ⟨g, σ, bufs, kids, ht, hmem, by simp only [tempCell, hn],
    h.within hJ (by rw [hn]; exact hlt), ⟨Nat.le_add_right _ _, by rw [hn]; omega⟩⟩

/-- **A temporary's cell is no fixed word.** -/
theorem DischargeHyps.temp_not_fixed {τ : Inst × V × K} (hτ : TempsOn P fs H hdr T τ) (w : E) :
    ¬ FixedW P fs cert H C hdr T (tempCell cert τ) w := by
  obtain ⟨g, σ, bufs, kids, ht, hmem, hcell, hlt, hF⟩ := h.temp_cell hτ
  have hJ := hτ.1
  rw [hcell]
  rintro (⟨I, hI, q, hq, hx, -, hno⟩ | ⟨I, hI, ⟨f, σI, bI, kI, hIt⟩, a, he, hta, hq⟩)
  · have hqlt := h.cells.cell_lt hI hq
    have heq := h.inj hlt (h.within hI hqlt) hx
    obtain rfl := insts_same hJ hI hF ⟨by omega, by omega⟩
    exact hno ⟨g, σ, bufs, kids, ht, τ.2.1, hmem, by omega⟩
  · rw [hIt] at hq
    have hlt' : cert g τ.2.1 < fs τ.1.t.name := by
      have hn : τ.1.t.name = g := by rw [ht]; rfl
      rw [hn]; exact (h.cert_lt g τ.2.1 hmem).2
    rcases h.classify hI hIt he hta hq with ⟨K, hK, i, hb, hqi⟩ | ⟨i, hR, hqi⟩ |
        ⟨K, hK, g', σK, bK, kK, hKt, pK, r, rs, hfa, k, hk, hqi, -⟩
    · have hi := (insts_within T 0 hdr K hK i (Or.inr hb)).2
      have heq := h.inj hlt (by omega) hqi
      rw [heq] at hF
      by_cases hKJ : K = τ.1
      · subst hKJ
        exact (insts_placed T 0 hdr _ hJ).frame_buf hF hb
      · exact (insts_pairwise T 0 hdr).forall hK hJ hKJ i (Or.inr hb) (Or.inl hF)
    · rcases h.region i hR with hi2 | hR'
      · obtain ⟨I0, hI0, hI0t, -⟩ := root_inst (P := P) (fs := fs) (H := H) (hdr := hdr) (T := T)
        have h2 := h.cells.two_le I0 hI0
        have hT2 : 2 ≤ T.total fs := by rw [hI0t] at h2; exact h2.trans (le_total T)
        have heq := h.inj hlt (by omega) hqi
        have := (h.cert_lt g τ.2.1 hmem).1
        omega
      · exact hR' τ.1 hJ (cert g τ.2.1) hlt' hqi.symm
    · have hrun := h.run K hK g' σK bK kK hKt pK r rs hfa k hk
      have hKlt : cert g' r + k < fs K.t.name := (h.cells.off K hK _ hrun.1).2
      have heq := h.inj hlt (h.within hK hKlt) hqi
      obtain rfl := insts_same hJ hK hF ⟨by omega, by omega⟩
      obtain ⟨rfl, -⟩ : g' = g ∧ σK = σ := by
        rw [ht] at hKt; cases hKt; exact ⟨rfl, rfl⟩
      exact hrun.2 τ.2.1 hmem (by omega)

/-- **Temporaries sharing a cell read one address.** -/
theorem DischargeHyps.temp_cell_inj {τ τ' : Inst × V × K} (hτ : TempsOn P fs H hdr T τ)
    (hτ' : TempsOn P fs H hdr T τ') (he : tempCell cert τ = tempCell cert τ') : τ.2.2 = τ'.2.2 := by
  obtain ⟨g, σ, bufs, kids, ht, hmem, hcell, hlt, hF⟩ := h.temp_cell hτ
  obtain ⟨g', σ', bufs', kids', ht', hmem', hcell', hlt', hF'⟩ := h.temp_cell hτ'
  rw [hcell, hcell'] at he
  have heq := h.inj hlt hlt' he
  have hJJ := insts_same hτ.1 hτ'.1 hF (by rw [heq]; exact hF')
  rw [hJJ] at ht
  rw [ht] at ht'
  cases ht'
  have htt : τ.2.1 = τ'.2.1 := h.cert_inj g _ hmem _ hmem' (by rw [hJJ] at heq; omega)
  obtain ⟨-, g1, σ1, b1, k1, h1, hr1⟩ := hτ
  obtain ⟨-, g2, σ2, b2, k2, h2, hr2⟩ := hτ'
  rw [hJJ, h2] at h1
  cases h1
  rw [htt] at hr1
  exact rcRead_unique h.fresh hr1 hr2

/-- A node instance of the valid tree runs its path. -/
theorem DischargeHyps.path {I : Inst} (hI : I ∈ honestInsts P fs H hdr T) {f : String} {σ : Val}
    {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node f σ bufs kids) :
    ∃ fn es vs, P.find? f = some fn ∧ walk σ fn.body = .ret es vs ∧ I.t.events P = es := by
  rcases insts_good T 0 hdr h.valid I hI with ⟨_, _, hv⟩ | ⟨_, _, hph⟩
  · rw [ht] at hv
    obtain ⟨fn, hf, _, es, vs, hw, -⟩ := hv
    exact ⟨fn, es, vs, hf, hw, by rw [ht]; exact events_node hf hw⟩
  · rw [ht] at hph; cases hph

/-- **The honest memory of a placed tree**: its temporaries re-chosen, it is `HonestAt`. -/
theorem honestAt_retemp : ∃ ν, HonestAt P fs H C hdr (T.retemp P fs ν 0) cert
    (honest P fs H C hdr (T.retemp P fs ν 0)).read args rets := by
  obtain ⟨hF1, hF2⟩ := resolveF_spec (W := FixedW P fs cert H C hdr T)
    (Θ := TempsOn P fs H hdr T) (c := tempCell cert) (a := fun τ => τ.2.2)
    (fun _ _ _ hw hw' => h.fixed_consistent hw hw') (fun _ _ hτ hτ' he => h.temp_cell_inj hτ hτ' he)
    (fun _ w hτ => h.temp_not_fixed hτ w)
  set F := resolveF (FixedW P fs cert H C hdr T) (TempsOn P fs H hdr T) (tempCell cert)
    (fun τ => τ.2.2) with hFdef
  refine ⟨fun fp f _ t => F (gpow (fp + cert f t)), ?_⟩
  set ν : ℕ → String → Val → V → E := fun fp f _ t => F (gpow (fp + cert f t)) with hν
  have hF := h.fresh
  have htot : (T.retemp P fs ν 0).total fs = T.total fs := total_retemp T 0
  have hrv : ∀ {fp : ℕ} {f : String} {σ : Val} {t : V}, t ∈ P.temps f →
      retempVal P ν fp f σ t = F (gpow (fp + cert f t)) := fun ht => by
    simp only [retempVal, ht, ↓reduceIte, hν]
  -- The frames of the re-chosen tree agree with `F`.
  have hG1 : ∀ a ∈ frameWrites C (honestInsts P fs H hdr (T.retemp P fs ν 0)), F a.1 = a.2 := by
    intro a ha
    obtain ⟨I', hI', q, hq, rfl⟩ := Memory.mem_frameWrites ha
    obtain ⟨I, hI, hfp, hteq⟩ := insts_retemp (H := H) T 0 hdr hdr I' hI'
    by_cases hto : TmpOff P cert I.t q.1
    · obtain ⟨f, σ, bufs, kids, hIt, v, hv, hqv⟩ := hto
      have hI't : I'.t = .node f (retempVal P ν I.fp f σ) bufs
          (Tree.retempKids P fs ν (kidPos fs P.loop I.fp f bufs (kids.map (Tree.total fs))) kids) := by
        rw [hteq, hIt, retemp_node]
      have h2 := (h.cert_lt f v hv).1
      have hqC : q ∈ C I' := by
        simp only [Inst.cells, List.mem_cons] at hq
        rcases hq with rfl | rfl | hq
        · simp only at hqv; omega
        · simp only at hqv; omega
        · exact hq
      have := h.tmp ν I' hI' f _ _ _ hI't v hv q hqC hqv
      simp only
      rw [this, hrv hv, hfp, hqv]
    · have hq' := h.keep ν I hI I' hI' hfp.symm hteq q hq hto
      simp only
      rw [← hfp]
      exact hF1 _ _ (Or.inl ⟨I, hI, q, hq', rfl, rfl, hto⟩)
  -- The equations of the re-chosen tree agree with `F`, at addresses of the old tree's.
  have hG2 : ∀ q ∈ (T.retemp P fs ν 0).eqns P,
      F q.1 = q.2 ∧ ∃ i : Fin (2 ^ logMem (T.total fs)), q.1 = gpow i := by
    intro q hq
    obtain ⟨I', hI', ⟨f, σ', bufs, kids', hI't⟩, a, he, hqa⟩ :=
      eqns_insts (fs := fs) (lp := P.loop) (H := H) (T.retemp P fs ν 0) 0 hdr q hq
    obtain ⟨I, hI, hfp, hteq⟩ := insts_retemp (H := H) T 0 hdr hdr I' hI'
    obtain ⟨σ, kids, hIt, rfl⟩ := node_of_retemp (hteq.symm.trans hI't)
    obtain ⟨fn, es, vs, hf, hw, hev⟩ := h.path hI hIt
    have hag := evAgree_retemp (ν := ν) hF hf (fp := I.fp) hw
    have hev' : I'.t.events P = es := by
      rw [hI't, events_retemp hF (bufs' := bufs) (ks' := kids), ← hIt, hev]
    rw [hev'] at he
    rw [hI't] at hqa
    simp only [Tree.val] at hqa
    have hIev : Ev.atom a ∈ I.t.events P := by rw [hev]; exact he
    by_cases hta : atomTmps a = []
    · rw [atomEqns_congr a hta fun v hv => hag _ he v hv] at hqa
      have hqT := eqns_of_insts T 0 hdr I hI ⟨f, σ, bufs, kids, hIt⟩ a hIev q (by rw [hIt]; exact hqa)
      exact ⟨hF1 _ _ (Or.inr ⟨I, hI, ⟨f, σ, bufs, kids, hIt⟩, a, hIev, hta, by rw [hIt]; exact hqa⟩),
        h.addr q hqT⟩
    · rcases a with _ | _ | _ | _ | _ | _ | _ | ⟨x, y, t1, t2, k⟩ | _ | _ | _ | _ <;>
        simp only [atomTmps, not_true_eq_false] at hta
      obtain ⟨ht1, ht2⟩ := mem_temps_of_event hf hw he
      have hx : retempVal P ν I.fp f σ x = σ x := hag _ he x (by simp [Ev.uses, atomUses])
      have hy : retempVal P ν I.fp f σ y = σ y := hag _ he y (by simp [Ev.uses, atomUses])
      have hrc : ∀ {t : V} {z : V}, (t = t1 ∧ z = x) ∨ (t = t2 ∧ z = y) →
          F (tempCell cert (I, t, (σ z).limb 0 * gpow 0)) = F ((σ z).limb 0 * gpow 0) := by
        intro t z htz
        refine hF2 (I, t, (σ z).limb 0 * gpow 0) ⟨hI, f, σ, bufs, kids, hIt, x, y, t1, t2, k, ?_, ?_⟩
        · rw [events_eq_node (bufs := []) (ks := []) (bufs' := bufs) (ks' := kids), ← hIt, hev]
          exact he
        · rcases htz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact Or.inl ⟨rfl, rfl⟩
          · exact Or.inr ⟨rfl, rfl⟩
      have hname : I.t.name = f := by rw [hIt]; rfl
      have hT : ∀ {t z : V}, (t = t1 ∧ z = x) ∨ (t = t2 ∧ z = y) →
          ((σ z).limb 0 * gpow 0, σ t) ∈ T.eqns P := by
        intro t z htz
        refine eqns_of_insts T 0 hdr I hI ⟨f, σ, bufs, kids, hIt⟩ _ hIev _ ?_
        rw [hIt]
        rcases htz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ List.mem_cons_self
      simp only [atomEqns, List.mem_cons, List.not_mem_nil, or_false] at hqa
      rcases hqa with rfl | rfl
      · simp only
        rw [hx, hrv ht1]
        obtain ⟨i, hi⟩ := h.addr _ (hT (Or.inl ⟨rfl, rfl⟩))
        refine ⟨?_, i, hi⟩
        rw [← hrc (Or.inl ⟨rfl, rfl⟩)]
        simp only [tempCell, hname]
      · simp only
        rw [hy, hrv ht2]
        obtain ⟨i, hi⟩ := h.addr _ (hT (Or.inr ⟨rfl, rfl⟩))
        refine ⟨?_, i, hi⟩
        rw [← hrc (Or.inr ⟨rfl, rfl⟩)]
        simp only [tempCell, hname]
  have hall : ∀ q ∈ frameWrites C (honestInsts P fs H hdr (T.retemp P fs ν 0)) ++
      (T.retemp P fs ν 0).eqns P, F q.1 = q.2 := by
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hG1 q hq
    · exact (hG2 q hq).1
  have hcons := consistent_of_read (rd := fun x => some (F x)) fun q hq => by rw [hall q hq]
  have hκ' : logMem ((T.retemp P fs ν 0).total fs) < 64 := by rw [htot]; exact h.lt_64
  have haddr' : ∀ q ∈ (T.retemp P fs ν 0).eqns P,
      ∃ i : Fin (2 ^ logMem ((T.retemp P fs ν 0).total fs)), q.1 = gpow i := by
    intro q hq; rw [htot]; exact (hG2 q hq).2
  have hread : ∀ q ∈ (T.retemp P fs ν 0).eqns P,
      (honest P fs H C hdr (T.retemp P fs ν 0)).read q.1 = some q.2 :=
    fun q hq => image_read hκ' hcons (List.mem_append_right _ hq) (haddr' q hq)
  have hRA : T.ReadsAs P fs ν (honest P fs H C hdr (T.retemp P fs ν 0)).read M.read 0 := by
    refine readsAs_of_insts (H := H) T 0 hdr fun I hI f σ bufs kids hIt => ?_
    obtain ⟨fn, es, vs, hf, hw, hev⟩ := h.path hI hIt
    have hag := evAgree_retemp (ν := ν) hF hf (fp := I.fp) hw
    obtain ⟨I', hI', -, hteq'⟩ := insts_retemp_fwd (H := H) (H' := H) (ν := ν) T 0 hdr hdr I hI
    have hI't : I'.t = .node f (retempVal P ν I.fp f σ) bufs
        (Tree.retempKids P fs ν (kidPos fs P.loop I.fp f bufs (kids.map (Tree.total fs))) kids) := by
      rw [hteq', hIt, retemp_node]
    have hev' : I'.t.events P = es := by
      rw [hI't, events_retemp hF (bufs' := bufs) (ks' := kids), ← hIt, hev]
    have hmem' : ∀ {a : Atom} {q : Write}, Ev.atom a ∈ es →
        q ∈ atomEqns (retempVal P ν I.fp f σ) a → q ∈ (T.retemp P fs ν 0).eqns P := fun ha hq =>
      eqns_of_insts _ 0 hdr I' hI' ⟨_, _, _, _, hI't⟩ _ (by rw [hev']; exact ha) _
        (by rw [hI't]; exact hq)
    rw [hev]
    refine ⟨fun a ha hta q hq => ?_, fun x y t1 t2 k he => ?_⟩
    · have hqT := eqns_of_insts T 0 hdr I hI ⟨f, σ, bufs, kids, hIt⟩ a (by rw [hev]; exact ha) q
        (by rw [hIt]; exact hq)
      rw [hread q (hmem' ha (by rw [atomEqns_congr a hta fun v hv => hag _ ha v hv]; exact hq)),
        h.valid.eqns_read h.lt_64 T q hqT (h.addr q hqT)]
    · obtain ⟨ht1, ht2⟩ := mem_temps_of_event hf hw he
      have hx : retempVal P ν I.fp f σ x = σ x := hag _ he x (by simp [Ev.uses, atomUses])
      have hy : retempVal P ν I.fp f σ y = σ y := hag _ he y (by simp [Ev.uses, atomUses])
      have e1 := hread _ (hmem' he List.mem_cons_self)
      have e2 := hread _ (hmem' he (List.mem_cons_of_mem _ List.mem_cons_self))
      simp only [hx, hy, hrv ht1, hrv ht2] at e1 e2
      exact ⟨e1, e2⟩
  exact ⟨⟨retemp_valid hF T 0 h.valid hRA, by rw [htot]; exact h.size, h.cells' ν, haddr',
    fun a ha b hb => hcons a (List.mem_append_right _ ha) b (List.mem_append_right _ hb),
    fun a ha b hb => hcons a (List.mem_append_left _ ha) b (List.mem_append_right _ hb)⟩,
    bufsOk_retemp hF T 0 h.valid h.bufsOk, placed_retemp hF T 0 h.valid h.placed⟩

end Proof

end Main

end
end LeanVM.Guest.Memory
