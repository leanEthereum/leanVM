/-
  LeanVM.Guest.B2C.Table

  `main`'s cells hold the jump table, so the honest memory does.
-/

module

public import LeanVM.Guest.B2C.Cells
public import LeanVM.Guest.End

/-!
# The jump table in `main`'s cells

An instance of `main` that runs has the jump table among its candidates (`nodeE`'s last block),
and every other candidate lies below the table's first slot `167`: its values' certificate cells,
its fixed cells, call sites and table jumps (`mainSmall`, by the kernel), and no frame run, since
`main`'s body has no `frameAddr` (`main_noRun`, through `walk_blockAtoms`: a path's atoms are its
block's). So each slot is the first candidate at its cell (`tableC_node`), and the honest memory
holds the table (`jumpTables_honestC`). A phantom of `main` does not have it; none is honest.
-/

namespace LeanVM.Guest.B2C

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-! ## The atoms of a block -/

mutual
/-- The atoms of a statement. -/
def stmtAtoms : Stmt → List Atom
  | .atom a => [a]
  | .ite _ z n => blockAtoms z ++ blockAtoms n
  | .match_ _ arms => armsAtoms arms
  | _ => []

/-- The atoms of a block. -/
def blockAtoms : List Stmt → List Atom
  | [] => []
  | s :: ss => stmtAtoms s ++ blockAtoms ss

/-- The atoms of arms. -/
def armsAtoms : List (List Stmt) → List Atom
  | [] => []
  | a :: as => blockAtoms a ++ armsAtoms as
end

section Atoms

variable {σ : Val}

theorem evs_seq_mem {o k : Out} {e : Ev} (h : e ∈ (o.seq k).evs) : e ∈ o.evs ∨ e ∈ k.evs := by
  rcases o with es | ⟨es, vs⟩ | _ <;> rcases k with es' | ⟨es', vs'⟩ | _ <;>
    simp_all [Out.seq, Out.pre, Out.evs]

theorem evs_pre_mem {o : Out} {es : List Ev} {e : Ev} (h : e ∈ (o.pre es).evs) : e ∈ es ∨ e ∈ o.evs := by
  rcases o with es' | ⟨es', vs⟩ | _ <;> simp_all [Out.pre, Out.evs]

theorem pick_noAtom {x : V} {args rets : List V} : ∀ (gs : List String) (j : ℕ) {a : Atom},
    Ev.atom a ∉ (pick σ x args rets j gs).evs
  | [], _, a => by simp [pick, Out.evs]
  | g :: gs, j, a => by
    unfold pick
    split_ifs
    · simp [Out.evs]
    · exact pick_noAtom gs (j + 1)

mutual
/-- **A statement's path's atoms are its atoms.** -/
theorem walk1_blockAtoms : ∀ (s : Stmt) {a : Atom}, Ev.atom a ∈ (walk1 σ s).evs → a ∈ stmtAtoms s
  | .atom b, a, h => by
    simp only [walk1, Out.evs, List.mem_singleton, Ev.atom.injEq] at h
    simp [stmtAtoms, h]
  | .ite c z m, a, h => by
    rw [walk1] at h
    rcases evs_pre_mem h with h | h
    · simp at h
    · simp only [stmtAtoms, List.mem_append]
      split_ifs at h
      · exact Or.inl (walk_blockAtoms z h)
      · exact Or.inr (walk_blockAtoms m h)
  | .match_ x arms, a, h => by
    rw [walk1] at h
    exact walkArms_blockAtoms x arms 0 h
  | .call .., a, h => by simp [walk1, Out.evs] at h
  | .callIf c f args, a, h => by
    rw [walk1] at h
    split_ifs at h <;> simp [Out.evs] at h
  | .dispatch x gs args rets, a, h => by
    rw [walk1] at h
    exact absurd h (pick_noAtom gs 0)
  | .ret _, a, h => by simp [walk1, Out.evs] at h

/-- **A block's path's atoms are its atoms.** -/
theorem walk_blockAtoms : ∀ (ss : List Stmt) {a : Atom}, Ev.atom a ∈ (walk σ ss).evs → a ∈ blockAtoms ss
  | [], a, h => by simp [walk, Out.evs] at h
  | s :: ss, a, h => by
    rw [walk] at h
    simp only [blockAtoms, List.mem_append]
    rcases evs_seq_mem h with h | h
    · exact Or.inl (walk1_blockAtoms s h)
    · exact Or.inr (walk_blockAtoms ss h)

theorem walkArms_blockAtoms (x : V) : ∀ (arms : List (List Stmt)) (j : ℕ) {a : Atom},
    Ev.atom a ∈ (walkArms σ x j arms).evs → a ∈ armsAtoms arms
  | [], _, a, h => by simp [walkArms, Out.evs] at h
  | b :: bs, j, a, h => by
    unfold walkArms at h
    simp only [armsAtoms, List.mem_append]
    split_ifs at h
    · exact Or.inl (walk_blockAtoms b h)
    · exact Or.inr (walkArms_blockAtoms x bs (j + 1) h)
end

end Atoms

/-! ## `main`'s candidates -/

/-- An atom that is not a nonempty frame run. -/
def noRun : Atom → Bool
  | .frameAddr _ (_ :: _) => false
  | _ => true

set_option maxRecDepth 100000 in
theorem main_noRun : (blockAtoms Data.core0.body).all noRun = true := by decide +kernel

/-- `main`'s certificate cells, fixed cells, call sites and table jumps lie below `167`. -/
noncomputable def mainSmallB : Bool :=
  (certOf 1).locs.all (fun c => Nat.blt c 167) && (plumbOf 1).stat.all (fun p => Nat.blt p.1 167) &&
    (plumbOf 1).sites.all (fun s => Nat.blt s.q 167 && Nat.blt s.tgt 167) &&
    (plumbOf 1).arms.all (fun a => Nat.blt a.2.1 167)

set_option maxRecDepth 100000 in
theorem mainSmall : mainSmallB = true := by decide +kernel

theorem main_idx : idxOf "main" = some 1 := by decide +kernel

theorem fs_main : fs "main" = mainFrame := by decide +kernel

theorem find_main : coreProgram.find? "main" = some Data.core0 :=
  Program.find?_of_indexOf? (j := 0) (by decide +kernel) rfl

/-- `main`'s candidates but the jump table. -/
noncomputable def mainRest (σ : Val) (I : Inst) : List (ℕ × E) :=
  valE "main" σ (coreProgram.temps "main") ++ runsE "main" σ (I.t.events coreProgram) ++
    (plumbOf 1).stat.map (fun q => (q.1, q.2.word I.fp)) ++
    valE "main" σ (namedOf (coreOf 1).params (I.t.events coreProgram) (pathRets I.t)) ++
    siteE 1 I (I.t.events coreProgram) ++
    (plumbOf 1).arms.map (fun a => (a.2.1, armWord σ a.1 a.2.2))

theorem nodeE_main (σ : Val) (I : Inst) : nodeE 1 "main" σ I = mainRest σ I ++ tableCells := rfl

/-- `main`'s paths run no frame runs. -/
theorem runsE_main {σ : Val} {bufs : List ℕ} {kids : List Memory.Tree} :
    runsE "main" σ ((Memory.Tree.node "main" σ bufs kids).events coreProgram) = [] := by
  unfold runsE
  rw [List.flatMap_eq_nil_iff]
  intro e he
  have he' : e ∈ (walk σ (Fn.body Data.core0)).evs := by
    unfold Tree.events at he
    simp only [Tree.name, Tree.val, find_main] at he
    split at he
    · rename_i es vs hw
      rw [hw]
      exact he
    · exact absurd he List.not_mem_nil
  cases e with
  | atom a =>
    have := List.all_eq_true.mp main_noRun a (walk_blockAtoms _ he')
    cases a with
    | frameAddr p run =>
      cases run with
      | nil => rfl
      | cons r rs => simp [noRun] at this
    | _ => rfl
  | _ => rfl

private theorem getD_lt {l : List ℕ} (h : l.all (fun c => Nat.blt c 167) = true) (n : ℕ) :
    l.getD n 0 < 167 := by
  rw [List.getD_eq_getElem?_getD]
  cases hn : l[n]? with
  | none => simp
  | some c =>
    have := List.all_eq_true.mp h c (List.mem_of_getElem? hn)
    simpa using this

/-- **Every candidate of `main` but the jump table lies below `167`.** -/
theorem mainRest_lt {σ : Val} {bufs : List ℕ} {kids : List Memory.Tree} {I : Inst}
    (ht : I.t = .node "main" σ bufs kids) : ∀ x ∈ mainRest σ I, x.1 < 167 := by
  have hs := mainSmall
  simp only [mainSmallB, Bool.and_eq_true] at hs
  obtain ⟨⟨⟨hl, hst⟩, hsi⟩, har⟩ := hs
  obtain ⟨_, -, -, -, -, -, -, hcert, -, -⟩ := fn_of_idx main_idx
  have hval : ∀ vs : List V, ∀ x ∈ valE "main" σ vs, x.1 < 167 := by
    intro vs x hx
    obtain ⟨v, -, rfl⟩ := List.mem_map.mp hx
    rw [hcert v]
    exact getD_lt hl _
  intro x hx
  simp only [mainRest, List.mem_append] at hx
  rcases hx with ((((hx | hx) | hx) | hx) | hx) | hx
  · exact hval _ x hx
  · rw [ht, runsE_main] at hx
    exact absurd hx List.not_mem_nil
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    simpa using List.all_eq_true.mp hst p hp
  · exact hval _ x hx
  · unfold siteE at hx
    obtain ⟨p, -, hx⟩ := List.mem_flatMap.mp hx
    split at hx
    · rename_i s hs'
      have hsm := List.all_eq_true.mp hsi s (List.mem_of_find?_eq_some hs')
      simp only [Bool.and_eq_true, Nat.blt_eq] at hsm
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hsm.1
      · split at hx
        · exact absurd hx List.not_mem_nil
        · rw [List.mem_singleton.mp hx]
          exact hsm.2
    · exact absurd hx List.not_mem_nil
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    simpa using List.all_eq_true.mp har a ha

/-- **An instance of `main` that runs has the jump table in its cells.** -/
theorem tableC_node {I : Inst} {σ : Val} {bufs : List ℕ} {kids : List Memory.Tree}
    (ht : I.t = .node "main" σ bufs kids) : tableCells ⊆ C I := by
  intro q hq
  have hlo : 167 ≤ q.1 := by
    have := tableCells_offsets ▸ List.mem_map_of_mem (f := Prod.fst) hq
    rw [List.mem_range'_1] at this
    exact this.1
  have hoff := tableCells_off hq
  rw [C_node ht main_idx, nodeE_main, fs_main, frameE, ← List.append_nil (List.filter _ _)]
  refine dedupC_mem (List.mem_filter.mpr ⟨List.mem_append_right _ hq, ?_⟩) fun x hx he ↦ ?_
  · simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq]
    exact ⟨hoff.1, hoff.2⟩
  · obtain ⟨hx, -⟩ := List.mem_filter.mp hx
    rcases List.mem_append.mp hx with hx | hx
    · have := mainRest_lt ht x hx
      omega
    · exact Prod.ext he (tableCells_agree hx hq he)

/-- **The honest memory holds the jump table**, at `B2C.C`. -/
theorem jumpTables_honestC {hdr : E × E} {T : Memory.Tree} {rd : Reader}
    (hH : Honest coreProgram fs H C hdr T rd [] []) (hname : T.name = "main") :
    End.JumpTables (honest coreProgram fs H C hdr T) := by
  intro q hq
  obtain ⟨I, hI, hIt, hfp, -⟩ := root_inst (P := coreProgram) (fs := fs) (H := H) (hdr := hdr) (T := T)
  have hnode : ∃ σ bufs kids, T = .node "main" σ bufs kids := by
    have hv := hH.valid
    cases T with
    | phantom f σ => exact hv.elim
    | node f σ bufs kids =>
      simp only [Tree.name] at hname
      subst hname
      exact ⟨σ, bufs, kids, rfl⟩
  obtain ⟨σ, bufs, kids, hT⟩ := hnode
  have hC := tableC_node (I := I) (by rw [hIt, hT]) hq
  have := hH.read_C hI hC
  rwa [hfp, gpow, pow_zero, one_mul] at this

end
end LeanVM.Guest.B2C
