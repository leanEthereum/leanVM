/-
  LeanVM.Guest.B2C.KRetemp

  Checker K's facts about re-choosing the temporaries, at the honest memory's choices: the counts
  do not see them, and a re-chosen instance keeps its old cells but the temporaries'.
-/

module

public import LeanVM.Guest.B2C.Cells
public import LeanVM.Guest.EndComplete
public import LeanVM.Guest.Memory.Size

/-!
# Re-choosing the temporaries

`cntRetemp`: the counts are per instance (`Tree.weight`), which re-choosing keeps.

`reInst ν I` is `I` with its tree's temporaries re-chosen, at the same frame, header and callee
frames. Every instance of a re-chosen tree is the re-chosen instance of the tree's at its frame
(`reInst_of_honest`), since the headers do not see the temporaries (`H_reInst`: `H` reads the
path's events, which re-choosing keeps). Its cells (`C_reInst`) are the old ones but at the
temporaries' cells: the candidates after the temporaries' (`nodeRest`) name only parameters, the
path's values and its returned values, which are not temporaries (`coreProgram_fresh`), and the
table selectors, which are not either (`ArmsFresh`, the sharing check's). So `keep`: the cells of
a re-chosen instance off its temporaries are the old instance's.
-/

namespace LeanVM.Guest.B2C

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-! ## The counts -/

mutual
theorem costW_congr (acs : List (ℕ × List (List ℕ))) {σ σ' : Val} :
    ∀ ss : List Stmt, (∀ v ∈ Stmt.usesList ss, σ' v = σ v) → costW acs σ' ss = costW acs σ ss
  | [], _ => by rw [costW, costW]
  | s :: ss, h => by
    rw [costW, costW, cost1_congr acs s (fun v hv ↦ h v (by rw [Stmt.usesList]; exact List.mem_append_left _ hv)),
      costW_congr acs ss (fun v hv ↦ h v (by rw [Stmt.usesList]; exact List.mem_append_right _ hv))]

theorem cost1_congr (acs : List (ℕ × List (List ℕ))) {σ σ' : Val} :
    ∀ s : Stmt, (∀ v ∈ Stmt.uses s, σ' v = σ v) → cost1 acs σ' s = cost1 acs σ s
  | .ite c z n, h => by
    rw [cost1, cost1, h c (by rw [Stmt.uses]; exact List.mem_cons_self),
      costW_congr acs z (fun v hv ↦ h v (by rw [Stmt.uses]; exact List.mem_cons_of_mem _ (List.mem_append_left _ hv))),
      costW_congr acs n (fun v hv ↦ h v (by rw [Stmt.uses]; exact List.mem_cons_of_mem _ (List.mem_append_right _ hv)))]
  | .match_ x arms, h => by
    rw [cost1, cost1]
    exact costArms_congr acs x _ 0 arms (h x (by rw [Stmt.uses]; exact List.mem_cons_self))
      (fun v hv ↦ h v (by rw [Stmt.uses]; exact List.mem_cons_of_mem _ hv))
  | .atom _, _ => rfl
  | .call .., _ => rfl
  | .callIf .., _ => rfl
  | .dispatch .., _ => rfl
  | .ret _, _ => rfl

theorem costArms_congr (acs : List (ℕ × List (List ℕ))) {σ σ' : Val} (x : V) (key : Option (List (List ℕ))) :
    ∀ (k : ℕ) (arms : List (List Stmt)), σ' x = σ x → (∀ v ∈ Stmt.usesArms arms, σ' v = σ v) →
      costArms acs σ' x key k arms = costArms acs σ x key k arms
  | _, [], _, _ => by rw [costArms, costArms]
  | k, a :: as, hx, h => by
    rw [costArms, costArms, hx,
      costW_congr acs a (fun v hv ↦ h v (by rw [Stmt.usesArms]; exact List.mem_append_left _ hv)),
      costArms_congr acs x key (k + 1) as hx
        (fun v hv ↦ h v (by rw [Stmt.usesArms]; exact List.mem_append_right _ hv))]
end

/-- A path's count does not see the temporaries' values. -/
theorem pathCountN_retemp (ν : ℕ → String → Val → V → E) (fp : ℕ) (f : String) (σ : Val) (op : Opcode) :
    pathCountN f (retempVal coreProgram ν fp f σ) op = pathCountN f σ op := by
  unfold pathCountN
  split
  · rename_i j hj
    obtain ⟨i, rfl, hi, -, hfind, hcore, -⟩ := fn_of_idx hj
    unfold pathCount
    rw [hcore, costW_congr _ _ (fun v hv ↦ retempVal_uses coreProgram_fresh hfind hv)]
  · rfl

mutual
theorem weightV_retemp (ν : ℕ → String → Val → V → E) (op : Opcode) :
    ∀ (t : Tree) (fp : ℕ), weightV (fun f σ ↦ pathCountN f σ op) (t.retemp coreProgram fs ν fp) =
      weightV (fun f σ ↦ pathCountN f σ op) t
  | .node f σ bufs kids, fp => by
      rw [retemp_node, weightV, weightV, pathCountN_retemp, weightVKids_retempKids ν op kids _
        (by rw [length_kidPos, List.length_map])]
  | .phantom .., fp => by rw [retemp_phantom]

theorem weightVKids_retempKids (ν : ℕ → String → Val → V → E) (op : Opcode) :
    ∀ (ks : List Tree) (ps : List ℕ), ps.length = ks.length →
      weightVKids (fun f σ ↦ pathCountN f σ op) (Tree.retempKids coreProgram fs ν ps ks) =
        weightVKids (fun f σ ↦ pathCountN f σ op) ks
  | [], _, _ => by rw [retempKids_nil]
  | _ :: _, [], h => absurd h (by simp)
  | k :: ks, p :: ps, h => by
      rw [retempKids_cons, weightVKids, weightVKids, weightV_retemp ν op k p,
        weightVKids_retempKids ν op ks ps (by simpa using h)]
end

/-- **The instruction counts do not see the temporaries' values.** -/
theorem cntRetemp : End.CntRetemp fs cnt := by
  intro ν t
  funext op
  simp only [cnt, weightV_retemp]

/-! ## Re-chosen instances -/

/-- No table selector is a temporary of its function (the sharing check's). -/
def ArmsFresh : Prop := ∀ j, ∀ a ∈ (plumbOf j).arms, V.n a.1 ∉ Stmt.tmpsList (coreOf j).body

/-- An instance with its tree's temporaries re-chosen, at the same frame, header and callees'
frames. -/
noncomputable def reInst (ν : ℕ → String → Val → V → E) (I : Inst) : Inst :=
  ⟨I.t.retemp coreProgram fs ν I.fp, I.fp, I.hdr, I.kidFps, I.bufBases⟩

variable {ν : ℕ → String → Val → V → E}

/-- The headers do not see the temporaries. -/
theorem H_reInst (J : Inst) (i : ℕ) : H (reInst ν J) i = H J i := by
  obtain ⟨t, fp, hdr, kf, bb⟩ := J
  cases t with
  | node f σ bufs kids =>
    simp only [reInst]
    rw [retemp_node]
    unfold H
    simp only [Tree.name]
    rw [events_retemp coreProgram_fresh (bufs' := bufs) (ks' := kids)]
    cases idxOf f <;> rfl
  | phantom f σ =>
    simp only [reInst]
    rw [retemp_phantom]

mutual
/-- **Every instance of a re-chosen tree is an instance of the tree re-chosen.** -/
theorem insts_reInst : ∀ (t : Tree) (fp : ℕ) (hdr : E × E),
    ∀ I' ∈ (t.retemp coreProgram fs ν fp).insts fs coreProgram.loop H fp hdr,
      ∃ I ∈ t.insts fs coreProgram.loop H fp hdr, I' = reInst ν I
  | .node f σ bufs kids, fp, hdr, I', hI' => by
      rw [retemp_node, insts_node, List.mem_cons] at hI'
      rw [map_total_retempKids_kidPos] at hI'
      rcases hI' with rfl | hI'
      · refine ⟨_, by rw [insts_node]; exact List.mem_cons_self, ?_⟩
        simp only [reInst]
        rw [retemp_node]
      · obtain ⟨I, hI, h⟩ := instsKids_reInst kids _
          ⟨.node f σ bufs kids, fp, hdr, kidPos fs coreProgram.loop fp f bufs (kids.map (Tree.total fs)),
            bases (bufBase fs coreProgram.loop fp f (kids.map (Tree.total fs))) bufs⟩ _ 0
          (fun i ↦ (congrArg (H · i) (by simp only [reInst]; rw [retemp_node])).trans (H_reInst _ i))
          I' hI'
        exact ⟨I, by rw [insts_node]; exact List.mem_cons_of_mem _ hI, h⟩
  | .phantom f σ, fp, hdr, I', hI' => by
      rw [retemp_phantom, insts_phantom, List.mem_singleton] at hI'
      subst hI'
      refine ⟨_, by rw [insts_phantom]; exact List.mem_singleton_self _, ?_⟩
      simp only [reInst]
      rw [retemp_phantom]

/-- `insts_reInst` for the callees at `ps`, under headers that agree. -/
theorem instsKids_reInst : ∀ (ks : List Tree) (ps : List ℕ) (J J' : Inst) (j : ℕ),
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
      · obtain ⟨I, hI, h⟩ := insts_reInst k p (H J j) I' hI'
        exact ⟨I, List.mem_append_left _ hI, h⟩
      · obtain ⟨I, hI, h⟩ := instsKids_reInst ks ps J J' (j + 1) hJ I' hI'
        exact ⟨I, List.mem_append_right _ hI, h⟩
end

/-- **An honest instance of the re-chosen tree is the old one at its frame, re-chosen.** -/
theorem reInst_of_honest {hdr : E × E} {T : Tree} {I I' : Inst}
    (hI : I ∈ honestInsts coreProgram fs H hdr T)
    (hI' : I' ∈ honestInsts coreProgram fs H hdr (T.retemp coreProgram fs ν 0)) (hfp : I'.fp = I.fp) :
    I' = reInst ν I := by
  obtain ⟨I0, hI0, rfl⟩ := insts_reInst T 0 hdr I' hI'
  have hfp0 : I0.fp = I.fp := hfp
  have h2 := two_le_fs I.t.name
  have h20 := two_le_fs I0.t.name
  obtain rfl : I0 = I := insts_same hI0 hI (i := I.fp) ⟨by omega, by omega⟩ ⟨le_rfl, by omega⟩
  rfl

/-! ## The cells of a re-chosen instance -/

/-- The candidates of a node after its temporaries'. -/
noncomputable def nodeRest (j : ℕ) (f : String) (σ : Val) (I : Inst) : List (ℕ × E) :=
  runsE f σ (I.t.events coreProgram) ++ (plumbOf j).stat.map (fun q => (q.1, q.2.word I.fp)) ++
    valE f σ (namedOf (coreOf j).params (I.t.events coreProgram) (pathRets I.t)) ++
    siteE j I (I.t.events coreProgram) ++
    (plumbOf j).arms.map (fun a => (a.2.1, armWord σ a.1 a.2.2)) ++
    (if j = 1 then tableCells else [])

theorem nodeE_split (j : ℕ) (f : String) (σ : Val) (I : Inst) :
    nodeE j f σ I = valE f σ (coreProgram.temps f) ++ nodeRest j f σ I := by
  simp only [nodeE, nodeRest, List.append_assoc]

private theorem flatMap_congr_mem {α β : Type} {f g : α → List β} :
    ∀ {l : List α}, (∀ a ∈ l, f a = g a) → l.flatMap f = l.flatMap g
  | [], _ => rfl
  | a :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons, h a List.mem_cons_self,
      flatMap_congr_mem fun b hb ↦ h b (List.mem_cons_of_mem _ hb)]

private theorem runsE_congr {f : String} {σ σ' : Val} {es : List Ev}
    (h : ∀ e ∈ es, ∀ v ∈ e.uses, σ' v = σ v) : runsE f σ' es = runsE f σ es := by
  unfold runsE
  refine flatMap_congr_mem fun e he ↦ ?_
  cases e with
  | atom a =>
    cases a with
    | frameAddr p run =>
      cases run with
      | nil => rfl
      | cons r rs =>
        have hr : ∀ v ∈ r :: rs, σ' v = σ v := fun v hv ↦
          h _ he v (List.mem_cons_of_mem _ hv)
        refine List.ext_getElem (by simp) fun k h1 h2 ↦ ?_
        simp only [List.getElem_mapIdx]
        rw [hr _ (List.getElem_mem _)]
    | _ => rfl
  | _ => rfl

private theorem valE_congr {f : String} {σ σ' : Val} {vs : List V} (h : ∀ v ∈ vs, σ' v = σ v) :
    valE f σ' vs = valE f σ vs := by
  unfold valE
  exact List.map_congr_left fun v hv ↦ by rw [h v hv]

private theorem armWord_congr {σ σ' : Val} {x b : ℕ} (h : σ' (V.n x) = σ (V.n x)) :
    armWord σ' x b = armWord σ x b := by
  unfold armWord
  simp only [h]

private theorem retempVal_of_not {fp : ℕ} {f : String} {σ : Val} {v : V}
    (h : v ∉ coreProgram.temps f) : retempVal coreProgram ν fp f σ v = σ v := by
  simp only [retempVal, h, ↓reduceIte]

/-- **The candidates after the temporaries' do not see them.** -/
theorem nodeRest_reInst (hA : ArmsFresh) {I : Inst} {f : String} {σ : Val} {bufs : List ℕ}
    {kids : List Tree} {j : ℕ} (ht : I.t = .node f σ bufs kids) (hj : idxOf f = some j) :
    nodeRest j f (retempVal coreProgram ν I.fp f σ) (reInst ν I) = nodeRest j f σ I := by
  obtain ⟨i, rfl, hi, -, hfind, hcore, -, -, -, -⟩ := fn_of_idx hj
  set fn := coreProgram[i] with hfn
  have hfr := coreProgram_fresh fn (List.mem_of_find?_eq_some hfind)
  have htemps : coreProgram.temps f = Stmt.tmpsList fn.body := by rw [Program.temps, hfind]
  have hnot : ∀ v, v ∈ fn.params ∨ v ∈ Stmt.usesList fn.body →
      retempVal coreProgram ν I.fp f σ v = σ v := by
    intro v hv
    refine retempVal_of_not fun ht' ↦ ?_
    rw [htemps] at ht'
    rcases hv with hv | hv
    · exact (hfr.2 v ht').2 hv
    · exact (hfr.2 v ht').1 hv
  have hrt : (reInst ν I).t = (Memory.Tree.node f σ bufs kids).retemp coreProgram fs ν I.fp := by
    simp only [reInst, ht]
  have hev : (reInst ν I).t.events coreProgram = I.t.events coreProgram := by
    rw [hrt, retemp_node, ht, events_retemp coreProgram_fresh (bufs' := bufs) (ks' := kids)]
  have hrets : pathRets (reInst ν I).t = pathRets I.t := by
    rw [hrt, retemp_node, ht]
    unfold pathRets
    simp only [Tree.name, Tree.val, hfind]
    rw [walk_retemp coreProgram_fresh hfind]
  have hwalk : I.t.events coreProgram = (match walk σ fn.body with
      | .ret es _ => es
      | _ => []) := by
    rw [ht]
    unfold Tree.events
    simp only [Tree.name, Tree.val, hfind]
    rfl
  have hevu : ∀ e ∈ I.t.events coreProgram, ∀ v ∈ e.uses, v ∈ Stmt.usesList fn.body := by
    intro e he v hv
    rw [hwalk] at he
    have hw := walk_within (σ := σ) fn.body
    split at he
    · rename_i es vs h
      rw [h] at hw
      exact hw.1 e he v hv
    · exact (List.not_mem_nil he).elim
  have hretu : ∀ v ∈ pathRets I.t, v ∈ Stmt.usesList fn.body := by
    intro v hv
    rw [ht] at hv
    unfold pathRets at hv
    simp only [Tree.name, Tree.val, hfind] at hv
    have hw := walk_within (σ := σ) fn.body
    split at hv
    · rename_i es vs h
      rw [h] at hw
      exact hw.2.2 v hv
    · exact (List.not_mem_nil hv).elim
  have hnamed : ∀ v ∈ namedOf (coreOf (i + 1)).params (I.t.events coreProgram) (pathRets I.t),
      retempVal coreProgram ν I.fp f σ v = σ v := by
    intro v hv
    simp only [namedOf, List.mem_append, List.mem_flatMap, hcore] at hv
    rcases hv with (hv | ⟨e, he, hv⟩) | hv
    · exact hnot v (Or.inl hv)
    · exact hnot v (Or.inr (hevu e he v hv))
    · exact hnot v (Or.inr (hretu v hv))
  have harms : (plumbOf (i + 1)).arms.map (fun a => (a.2.1, armWord (retempVal coreProgram ν I.fp f σ) a.1 a.2.2)) =
      (plumbOf (i + 1)).arms.map (fun a => (a.2.1, armWord σ a.1 a.2.2)) := by
    refine List.map_congr_left fun a ha ↦ ?_
    have hna := hA (i + 1) a ha
    rw [hcore, ← htemps] at hna
    rw [armWord_congr (retempVal_of_not hna)]
  unfold nodeRest
  rw [hev, hrets, runsE_congr fun e he v hv ↦ hnot v (Or.inr (hevu e he v hv)), valE_congr hnamed, harms]
  rfl

private theorem keys_valE {f : String} (σ σ' : Val) (vs : List V) (p : ℕ × E → Bool)
    (hp : ∀ a b c, p (a, b) = p (a, c)) :
    ((valE f σ vs).filter p).map Prod.fst = ((valE f σ' vs).filter p).map Prod.fst := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [valE, List.map_cons, List.filter_cons] at ih ⊢
    rw [hp _ (σ v) (σ' v)]
    split
    · simp only [List.map_cons, ih]
    · exact ih

/-- **A re-chosen instance's cells off its temporaries are its old ones.** -/
theorem C_reInst (hA : ArmsFresh) (I : Inst) {q : ℕ × E} (hq : q ∈ C (reInst ν I))
    (hn : ¬ TmpOff coreProgram cert I.t q.1) : q ∈ C I := by
  obtain ⟨t, fp, hdr, kf, bb⟩ := I
  cases t with
  | phantom f σ =>
    simp only [reInst] at hq
    rw [retemp_phantom] at hq
    exact hq
  | node f σ bufs kids =>
    cases hj : idxOf f with
    | none =>
      simp only [reInst] at hq
      rw [retemp_node] at hq
      simp [C, Tree.name, hj] at hq
    | some j =>
      have ht' : (reInst ν ⟨.node f σ bufs kids, fp, hdr, kf, bb⟩).t =
          .node f (retempVal coreProgram ν fp f σ) bufs
            (Tree.retempKids coreProgram fs ν (kidPos fs coreProgram.loop fp f bufs (kids.map (Tree.total fs)))
              kids) := by
        simp only [reInst]
        rw [retemp_node]
      rw [C_node ht' hj, nodeE_split, nodeRest_reInst (I := ⟨.node f σ bufs kids, fp, hdr, kf, bb⟩) hA rfl hj,
        frameE_append] at hq
      rw [C_node rfl hj, nodeE_split, frameE_append]
      refine dedupC_swap (keys_valE _ _ _ _ fun _ _ _ ↦ rfl) hq fun hm ↦ hn ?_
      obtain ⟨⟨k, w⟩, hkw, hk⟩ := List.mem_map.mp hm
      obtain ⟨hkw, -⟩ := List.mem_filter.mp hkw
      obtain ⟨v, hv, hve⟩ := List.mem_map.mp hkw
      simp only [Prod.mk.injEq] at hve
      exact ⟨f, σ, bufs, kids, rfl, v, hv, by rw [← hk, ← hve.1]⟩

/-- **Checker K's `keep`**: the cells of a re-chosen instance off its temporaries are the old
instance's. -/
theorem kfacts_keep (hA : ArmsFresh) (hdr : E × E) (T : Tree) :
    ∀ ν, ∀ I ∈ honestInsts coreProgram fs H hdr T,
      ∀ I' ∈ honestInsts coreProgram fs H hdr (T.retemp coreProgram fs ν 0),
        I'.fp = I.fp → I'.t = I.t.retemp coreProgram fs ν I.fp → ∀ q ∈ I'.cells C,
          ¬ TmpOff coreProgram cert I.t q.1 → q ∈ I.cells C := by
  intro ν I hI I' hI' hfp _ q hq hn
  obtain rfl := reInst_of_honest hI hI' hfp
  simp only [Inst.cells, List.mem_cons] at hq ⊢
  rcases hq with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (C_reInst hA I h hn))

end
end LeanVM.Guest.B2C
