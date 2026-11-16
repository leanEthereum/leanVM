/-
  LeanVM.Guest.Backend.Guest.Cpl.Insts

  Facts about the instances of the honest memory at any callee headers `H`: a node's path and
  callees, the callees' headers, and the instances of a tree whose temporaries are re-chosen.
-/

module

public import LeanVM.Guest.B2C.Cells
public import LeanVM.Guest.Memory.Retemp
public import LeanVM.Guest.Memory.Discharge
public import LeanVM.Guest.Memory.SizeTotal

/-!
# The instances at any headers

`B2C/Frame.lean` and `B2C/KRetemp.lean` prove these at the certificates' headers `B2C.H`; the proofs
read of the headers only that they are some function of the instance, so here they are stated for
any `H`. `kid_inst`: the `i`-th callee of a node's path is an instance at its `i`-th callee frame
with header `H I i`; `honest_hdrK`: when every `H I i` is of `K`, every instance but `main`'s
returns to registers of `K`; `reInst_of_honest`: when `H` does not see the temporaries, an
instance of the re-chosen tree is the old instance at its frame, re-chosen. `frameE_cell`: a cell
whose candidates all carry one word holds it.
-/

namespace LeanVM.Guest.Backend.Cpl

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B2C

@[expose] public section

/-! ## Cells -/

theorem dedupC_has : ∀ {L : List (ℕ × E)} {x : ℕ × E}, x ∈ L → ∃ q ∈ dedupC L, q.1 = x.1
  | [], _, h => absurd h List.not_mem_nil
  | y :: L, x, h => by
    by_cases hy : y.1 = x.1
    · exact ⟨y, by simp [dedupC], hy⟩
    · rcases List.mem_cons.mp h with rfl | h
      · exact absurd rfl hy
      · obtain ⟨q, hq, he⟩ := dedupC_has h
        refine ⟨q, ?_, he⟩
        simp only [dedupC, List.mem_cons, List.mem_filter, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq]
        exact Or.inr ⟨hq, by rw [he]; exact fun e ↦ hy e.symm⟩

/-- **A cell whose candidates all carry one word holds it.** -/
theorem frameE_cell {n : ℕ} {L : List (ℕ × E)} {c : ℕ} {w : E} (hx : ∃ x ∈ L, x.1 = c) (h2 : 2 ≤ c)
    (hn : c < n) (hall : ∀ x ∈ L, x.1 = c → x.2 = w) : (c, w) ∈ frameE n L := by
  obtain ⟨x, hx, rfl⟩ := hx
  have hx' : x ∈ L.filter fun q ↦ Nat.ble 2 q.1 && Nat.blt q.1 n := by
    simp only [List.mem_filter, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq]; exact ⟨hx, h2, hn⟩
  obtain ⟨q, hq, he⟩ := dedupC_has hx'
  have hqL := (mem_frameE (n := n) (L := L) hq).1
  have := hall q hqL he
  have : q = (x.1, w) := by rw [← he, ← this]
  rw [← this]; exact hq

/-- The cells of a frame: some list's candidates in the frame, one per cell, so they fit and
agree. -/
theorem cellsOk_frameE {C : Inst → List (ℕ × E)}
    (hC : ∀ I, ∃ L, C I = frameE (fs I.t.name) L ∨ C I = []) (Is : List Inst) : CellsOk fs C Is where
  two_le I _ := two_le_fs I.t.name
  off I _ q hq := by
    obtain ⟨L, h | h⟩ := hC I <;> rw [h] at hq
    · exact (mem_frameE hq).2
    · cases hq
  agree I _ q hq q' hq' he := by
    obtain ⟨L, h | h⟩ := hC I <;> rw [h] at hq hq'
    · rw [dedupC_key hq hq' he]
    · cases hq

variable {H : Inst → ℕ → E × E}

/-! ## A node's path and callees -/

theorem kidsValid_length {rd : Reader} {σ : Val} : ∀ {cs : List Call} {ks : List Tree},
    Tree.KidsValid coreProgram rd σ cs ks → ks.length = cs.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by
    simp only [List.length_cons, kidsValid_length h.2.2]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

/-- **A node instance valid on a reader**, along its function's path. -/
theorem node_valid {rd : Reader} {I : Inst} {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree}
    {j : ℕ} (ht : I.t = .node f σ bufs kids) (hj : idxOf f = some j) (hg : I.Good coreProgram rd) :
    ∃ es vs, walk σ (coreOf j).body = .ret es vs ∧ (∀ e ∈ es, e.Holds rd σ) ∧
      Tree.KidsValid coreProgram rd σ (calls es) kids := by
  obtain ⟨i, rfl, hi, -, hf, hc, -⟩ := fn_of_idx hj
  rcases hg with ⟨args, rets, hv⟩ | ⟨f', σ', hp⟩
  · rw [ht] at hv
    obtain ⟨fn, hfn, -, es, vs, hw, -, he, hk⟩ := hv
    rw [hf] at hfn; cases hfn
    exact ⟨es, vs, by rw [hc]; exact hw, he, hk⟩
  · rw [ht] at hp; cases hp

/-- A node's events are its path's. -/
theorem node_events {I : Inst} {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} {j : ℕ}
    (ht : I.t = .node f σ bufs kids) (hj : idxOf f = some j) {es : List Ev} {vs : List V}
    (hw : walk σ (coreOf j).body = .ret es vs) : I.t.events coreProgram = es := by
  obtain ⟨i, rfl, hi, -, hf, hc, -⟩ := fn_of_idx hj
  rw [ht]
  unfold Tree.events
  simp only [Tree.name, Tree.val, hf]
  rw [← hc, hw]

/-- **One callee frame per call.** -/
theorem frame_len {hdr : E × E} {T : Tree} {I : Inst} (hI : I ∈ honestInsts coreProgram fs H hdr T)
    {rd : Reader} {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node f σ bufs kids)
    {es : List Ev} (hk : Tree.KidsValid coreProgram rd σ (calls es) kids) :
    I.kidFps.length = (calls es).length := by
  rw [honest_kidFps hI, length_kidPos, List.length_map, ht]
  exact kidsValid_length hk

theorem kidsValid_at {rd : Reader} {σ : Val} : ∀ {cs : List Call} {ks : List Tree},
    Tree.KidsValid coreProgram rd σ cs ks → ∀ (i : ℕ) (c : Call), cs[i]? = some c →
      ∃ k, ks[i]? = some k ∧ k.name = c.f ∧
        (if c.taken then k.Valid coreProgram rd (c.args.map σ) (c.rets.map σ)
          else (∃ f σ', k = .phantom f σ') ∧ Phantom coreProgram k (c.args.map σ))
  | [], [], _, _, _, h => by simp at h
  | [], _ :: _, h, _, _, _ => h.elim
  | _ :: _, [], h, _, _, _ => h.elim
  | c :: cs, k :: ks, ⟨hn, hk, h⟩, i, c', hc => by
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hc
      subst hc
      exact ⟨k, rfl, hn, hk⟩
    | succ i =>
      simp only [List.getElem?_cons_succ] at hc ⊢
      exact kidsValid_at h i c' hc

/-- **The `i`-th callee of a path**: an instance at the `i`-th callee frame, with the header
`H I i`, valid if the call is taken, else a phantom with the arguments. -/
theorem kid_inst {hdr : E × E} {T : Tree} {I : Inst} (hI : I ∈ honestInsts coreProgram fs H hdr T)
    {rd : Reader} {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node f σ bufs kids)
    {es : List Ev} (hk : Tree.KidsValid coreProgram rd σ (calls es) kids) {i : ℕ} {c : Call} {kfp : ℕ}
    (hc : (calls es)[i]? = some c) (hp : I.kidFps[i]? = some kfp) :
    ∃ J ∈ honestInsts coreProgram fs H hdr T, J.fp = kfp ∧ J.hdr = H I i ∧ J.t.name = c.f ∧
      (if c.taken then J.t.Valid coreProgram rd (c.args.map σ) (c.rets.map σ)
        else (∃ f σ', J.t = .phantom f σ') ∧ Phantom coreProgram J.t (c.args.map σ)) := by
  obtain ⟨k, hki, hn, hv⟩ := kidsValid_at hk i c hc
  obtain ⟨J, hJ, rfl, hfp, hh⟩ := honest_kid hI (by rw [ht]; exact hki)
  rw [hp] at hfp
  exact ⟨J, hJ, (Option.some.inj hfp).symm, hh, hn, hv⟩

theorem idxOf_of_find {f : String} {fn : Fn} (h : coreProgram.find? f = some fn) : ∃ j, idxOf f = some j := by
  cases hj : idxOf f with
  | none =>
    unfold idxOf at hj
    rw [Option.map_eq_none_iff] at hj
    rw [find?_none hj] at h
    cases h
  | some j => exact ⟨j, rfl⟩

/-- A callee's instance: a node valid on its path, or a phantom, of a function of the program,
its parameters' words the arguments. -/
theorem kid_shape {rd : Reader} {J : Inst} {c : Call} {σ : Val} (hn : J.t.name = c.f)
    (hv : if c.taken then J.t.Valid coreProgram rd (c.args.map σ) (c.rets.map σ)
      else (∃ f σ', J.t = .phantom f σ') ∧ Phantom coreProgram J.t (c.args.map σ)) :
    ∃ jc, idxOf c.f = some jc ∧ (coreOf jc).params.map J.t.val = c.args.map σ ∧
      ((c.taken = true ∧ ∃ σJ bufs kids, J.t = .node c.f σJ bufs kids ∧
        J.t.Valid coreProgram rd (c.args.map σ) (c.rets.map σ)) ∨
        (c.taken = false ∧ ∃ σJ, J.t = .phantom c.f σJ)) := by
  split_ifs at hv with htk
  · cases ht : J.t with
    | node g σJ bufs kids =>
      have hv' := hv
      rw [ht] at hv hn
      simp only [Tree.name] at hn
      subst hn
      obtain ⟨fn, hf, hpar, -⟩ := hv
      obtain ⟨jc, hjc⟩ := idxOf_of_find hf
      obtain ⟨i, rfl, hi, hi', hf', hc, -⟩ := fn_of_idx hjc
      rw [hf'] at hf; cases hf
      refine ⟨i + 1, hjc, by rw [hc]; exact hpar, Or.inl ⟨htk, σJ, bufs, kids, rfl, ht ▸ hv'⟩⟩
    | phantom g σJ => rw [ht] at hv; exact hv.elim
  · obtain ⟨⟨g, σJ, ht⟩, fn, hf, hpar⟩ := hv
    rw [ht] at hn hf hpar
    simp only [Tree.name] at hn hf
    subst hn
    obtain ⟨jc, hjc⟩ := idxOf_of_find hf
    obtain ⟨i, rfl, hi, hi', hf', hc, -⟩ := fn_of_idx hjc
    rw [hf'] at hf; cases hf
    exact ⟨i + 1, hjc, by rw [hc, ht]; exact hpar, Or.inr ⟨by simpa using htk, σJ, ht⟩⟩

/-! ## Headers -/

/-- A header of words of `K`. -/
def KHdr (h : E × E) : Prop := IsInK h.1 ∧ IsInK h.2

mutual
/-- Every instance's header is its tree's, or some callee header. -/
theorem insts_hdr (hK : ∀ I i, KHdr (H I i)) : ∀ (t : Tree) (fp : ℕ) (h : E × E),
    ∀ J ∈ t.insts fs coreProgram.loop H fp h, J.hdr = h ∨ KHdr J.hdr
  | .node f σ bufs kids, fp, h, J, hJ => by
      rw [insts_node, List.mem_cons] at hJ
      rcases hJ with rfl | hJ
      · exact Or.inl rfl
      · exact Or.inr (instsKids_hdrK hK kids _ _ 0 J hJ)
  | .phantom .., fp, h, J, hJ => by
      rw [insts_phantom, List.mem_singleton] at hJ
      subst hJ; exact Or.inl rfl

/-- Every instance below a callee has a header of `K`. -/
theorem instsKids_hdrK (hK : ∀ I i, KHdr (H I i)) : ∀ (ks : List Tree) (ps : List ℕ) (I : Inst) (i : ℕ),
    ∀ J ∈ Tree.instsKids fs coreProgram.loop H I i ps ks, KHdr J.hdr
  | [], _, _, _, J, hJ => by rw [instsKids_nil] at hJ; exact absurd hJ List.not_mem_nil
  | _ :: _, [], _, _, J, hJ => by rw [instsKids_nil_left] at hJ; exact absurd hJ List.not_mem_nil
  | k :: ks, p :: ps, I, i, J, hJ => by
      rw [instsKids_cons, List.mem_append] at hJ
      rcases hJ with hJ | hJ
      · rcases insts_hdr hK k p (H I i) J hJ with he | hk
        · rw [he]; exact hK I i
        · exact hk
      · exact instsKids_hdrK hK ks ps I (i + 1) J hJ
end

/-- **Every instance but `main`'s returns to registers of `K`**, every callee header being of
`K`. -/
theorem honest_hdrK (hK : ∀ I i, KHdr (H I i)) {hdr : E × E} {T : Tree} (hT : T.name = "main")
    {J : Inst} (hJ : J ∈ honestInsts coreProgram fs H hdr T) (hn : J.t.name ≠ "main") : KHdr J.hdr := by
  unfold honestInsts at hJ
  cases T with
  | phantom f σ =>
    rw [insts_phantom, List.mem_singleton] at hJ
    subst hJ; exact absurd hT hn
  | node f σ bufs kids =>
    rw [insts_node, List.mem_cons] at hJ
    rcases hJ with rfl | hJ
    · exact absurd hT hn
    · exact instsKids_hdrK hK kids _ _ 0 J hJ

/-! ## Re-chosen temporaries -/

/-- An instance with its tree's temporaries re-chosen, at the same frame, header and callees'
frames (`B2C.reInst`). -/
noncomputable def reInst (ν : ℕ → String → Val → V → E) (I : Inst) : Inst :=
  ⟨I.t.retemp coreProgram fs ν I.fp, I.fp, I.hdr, I.kidFps, I.bufBases⟩

variable {ν : ℕ → String → Val → V → E}

mutual
/-- **Every instance of a re-chosen tree is an instance of the tree re-chosen**, the headers not
seeing the temporaries. -/
theorem insts_reInst (hfr : coreProgram.Fresh) (hH : ∀ J i, H (reInst ν J) i = H J i) :
    ∀ (t : Tree) (fp : ℕ) (hdr : E × E),
    ∀ I' ∈ (t.retemp coreProgram fs ν fp).insts fs coreProgram.loop H fp hdr,
      ∃ I ∈ t.insts fs coreProgram.loop H fp hdr, I' = reInst ν I
  | .node f σ bufs kids, fp, hdr, I', hI' => by
      rw [retemp_node, insts_node, List.mem_cons] at hI'
      rw [map_total_retempKids_kidPos] at hI'
      rcases hI' with rfl | hI'
      · refine ⟨_, by rw [insts_node]; exact List.mem_cons_self, ?_⟩
        simp only [reInst]
        rw [retemp_node]
      · obtain ⟨I, hI, h⟩ := instsKids_reInst hfr hH kids _
          ⟨.node f σ bufs kids, fp, hdr, kidPos fs coreProgram.loop fp f bufs (kids.map (Tree.total fs)),
            bases (bufBase fs coreProgram.loop fp f (kids.map (Tree.total fs))) bufs⟩ _ 0
          (fun i ↦ (congrArg (H · i) (by simp only [reInst]; rw [retemp_node])).trans (hH _ i))
          I' hI'
        exact ⟨I, by rw [insts_node]; exact List.mem_cons_of_mem _ hI, h⟩
  | .phantom f σ, fp, hdr, I', hI' => by
      rw [retemp_phantom, insts_phantom, List.mem_singleton] at hI'
      subst hI'
      refine ⟨_, by rw [insts_phantom]; exact List.mem_singleton_self _, ?_⟩
      simp only [reInst]
      rw [retemp_phantom]

/-- `insts_reInst` for the callees at `ps`, under headers that agree. -/
theorem instsKids_reInst (hfr : coreProgram.Fresh) (hH : ∀ J i, H (reInst ν J) i = H J i) :
    ∀ (ks : List Tree) (ps : List ℕ) (J J' : Inst) (j : ℕ),
    (∀ i, H J' i = H J i) →
    ∀ I' ∈ Tree.instsKids fs coreProgram.loop H J' j ps (Tree.retempKids coreProgram fs ν ps ks),
      ∃ I ∈ Tree.instsKids fs coreProgram.loop H J j ps ks, I' = reInst ν I
  | [], _, _, _, _, _, I', hI' => by
      rw [retempKids_nil, instsKids_nil] at hI'; exact (List.not_mem_nil hI').elim
  | _ :: _, [], _, _, _, _, I', hI' => by
      rw [instsKids_nil_left] at hI'; exact (List.not_mem_nil hI').elim
  | k :: ks, p :: ps, J, J', j, hJ, I', hI' => by
      rw [retempKids_cons, instsKids_cons, List.mem_append, hJ j] at hI'
      rw [instsKids_cons]
      rcases hI' with hI' | hI'
      · obtain ⟨I, hI, h⟩ := insts_reInst hfr hH k p (H J j) I' hI'
        exact ⟨I, List.mem_append_left _ hI, h⟩
      · obtain ⟨I, hI, h⟩ := instsKids_reInst hfr hH ks ps J J' (j + 1) hJ I' hI'
        exact ⟨I, List.mem_append_right _ hI, h⟩
end

/-- **An honest instance of the re-chosen tree is the old one at its frame, re-chosen.** -/
theorem reInst_of_honest (hfr : coreProgram.Fresh) (hH : ∀ J i, H (reInst ν J) i = H J i)
    {hdr : E × E} {T : Tree} {I I' : Inst}
    (hI : I ∈ honestInsts coreProgram fs H hdr T)
    (hI' : I' ∈ honestInsts coreProgram fs H hdr (T.retemp coreProgram fs ν 0)) (hfp : I'.fp = I.fp) :
    I' = reInst ν I := by
  obtain ⟨I0, hI0, rfl⟩ := insts_reInst hfr hH T 0 hdr I' hI'
  have hfp0 : I0.fp = I.fp := hfp
  have h2 := two_le_fs I.t.name
  have h20 := two_le_fs I0.t.name
  obtain rfl : I0 = I := insts_same hI0 hI (i := I.fp) ⟨by omega, by omega⟩ ⟨le_rfl, by omega⟩
  rfl

end
end LeanVM.Guest.Backend.Cpl
