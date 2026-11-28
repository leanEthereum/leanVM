module

public import LeanVM.Guest.Complete.LoopFHP
public import LeanVM.Guest.B1.Digest.ValidPops
public import LeanVM.Guest.B1.Digest.ChildListCRec
public import LeanVM.Guest.B1.Digest.MonoCRec
public import LeanVM.Guest.B1.Fwd.Eval
public import LeanVM.Guest.B1.Common.MutePops
public import LeanVM.Guest.Memory.PopsNil

/-!
# The children's walks' pops

The walks' hints are free in a valid tree, so their pops ride the constructed trees.

* `atomsPops_of_good`: atoms good for an oracle `w`, whose witness hints are stack hints at `v i`,
  pop `w (v i)`; `blockPops_of_good`: the same for a block of atoms; `leaf_pops`: a leaf of atoms pops
  its atoms' entries.
* `popsKids_zip`: callees whose posts fix their pops when entered pop them, a phantom nothing.
* `idxPops o s m`: claims `s ..< s + m`'s indices (`child_claim_index`); `gapPops o s m`: their gaps
  (`child_claim_gap`, `mGap o`).
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

variable {rd : Reader}

/-! ## Atoms -/

/-- **Atoms good for an oracle** pop their witness hints' oracle words. -/
theorem atomsPops_of_good {as S : List Atom} {w : ℕ → E} {σ : Val} (hg : ∀ a ∈ as, Good rd S w σ a)
    {str : String} {m : ℕ} {v : ℕ → ℕ}
    (hw : as.flatMap atomWit = (List.range m).map fun i => (str, Dest.stack [V.n (v i)])) :
    as.flatMap (Atom.pops rd σ) = (List.range m).map fun i => (str, [w (v i)]) := by
  rw [flatMap_atom_pops, hw, List.map_map]
  refine List.map_congr_left fun i hi => ?_
  have h1 : (str, Dest.stack [V.n (v i)]) ∈ as.flatMap atomWit := by
    rw [hw]; exact List.mem_map_of_mem hi
  obtain ⟨a, ha, hax⟩ := List.mem_flatMap.mp h1
  cases a with
  | hint hh =>
    cases hh with
    | witness s d =>
      simp only [atomWit, List.mem_singleton, Prod.mk.injEq] at hax
      obtain ⟨rfl, rfl⟩ := hax
      have hgx := hg _ ha
      simp only [Good] at hgx
      simp only [Function.comp_apply, Dest.words, List.map_cons, List.map_nil, Prod.mk.injEq, true_and,
        List.cons.injEq, and_true]
      exact hgx _ List.mem_cons_self
    | _ => simp [atomWit] at hax
  | _ => simp [atomWit] at hax

theorem flatMap_slEvs_atomsK (σ : Val) : ∀ pre : List Stmt, (∀ s ∈ pre, ∃ a, s = .atom a) →
    pre.flatMap (slEvs σ) = (atomsIn pre).map Ev.atom
  | [], _ => rfl
  | s :: pre, h => by
    obtain ⟨a, rfl⟩ := h s List.mem_cons_self
    rw [List.flatMap_cons, flatMap_slEvs_atomsK σ pre fun s hs => h s (List.mem_cons_of_mem _ hs)]
    rfl

/-- **A block of atoms good for an oracle** pops its witness hints' oracle words. -/
theorem blockPops_of_good {pre : List Stmt} (hpre : ∀ s ∈ pre, ∃ a, s = .atom a) {S : List Atom}
    {w : ℕ → E} {σ : Val} (hg : ∀ a ∈ atomsIn pre, Good rd S w σ a) {str : String} {m : ℕ} {v : ℕ → ℕ}
    (hw : (atomsIn pre).flatMap atomWit = (List.range m).map fun i => (str, Dest.stack [V.n (v i)])) :
    evPops rd σ (pre.flatMap (slEvs σ)) = (List.range m).map fun i => (str, [w (v i)]) := by
  rw [flatMap_slEvs_atomsK σ pre hpre, vp_evPops_atoms]
  exact atomsPops_of_good hg hw

/-- **A leaf of atoms pops its atoms' entries.** -/
theorem leaf_pops {f : String} {fn : Fn} {σ : Val} {as : List Atom} {vs : List V}
    (hf : coreProgram.find? f = some fn) (hw : walk σ fn.body = .ret (as.map Ev.atom) vs) :
    (Memory.Tree.node f σ [] []).pops coreProgram rd = as.flatMap (Atom.pops rd σ) := by
  rw [Tree.pops, events_node hf hw, Tree.popsKids, splice_nil_of_calls _ (vp_calls_atoms as), vp_evPops_atoms]

/-! ## Callees -/

/-- **Callees whose posts fix their pops**: each entered one pops its entries, a phantom nothing. -/
theorem popsKids_zip {σ : Val} : ∀ (cs : List Call) (ts : List Tree) (ps : List (List Pop)),
    Tree.KidsValid coreProgram rd σ cs ts →
    KidsPost rd (ps.map fun p => fun rd t => t.pops coreProgram rd = p) cs ts → ps.length = cs.length →
    Tree.popsKids coreProgram rd ts = List.zipWith (fun c p => if c.taken then p else []) cs ps
  | [], [], [], _, _, _ => rfl
  | c :: cs, t :: ts, p :: ps, hv, hq, hl => by
    rw [Tree.KidsValid] at hv
    obtain ⟨-, ht, hv⟩ := hv
    rw [List.map_cons, kidsPost_cons] at hq
    rw [Tree.popsKids, List.zipWith_cons_cons,
      popsKids_zip cs ts ps hv hq.2 (by simpa using hl)]
    congr 1
    by_cases hc : c.taken = true
    · simp only [hc, ↓reduceIte]; exact hq.1 hc
    · have hc' : c.taken = false := by simpa using hc
      simp only [hc', Bool.false_eq_true, ↓reduceIte] at ht ⊢
      obtain ⟨⟨f, σ', rfl⟩, -⟩ := ht
      rw [Tree.pops]
  | [], _ :: _, _, hv, _, _ => absurd hv (by simp [Tree.KidsValid])
  | _ :: _, [], _, hv, _, _ => absurd hv (by simp [Tree.KidsValid])
  | [], [], _ :: _, _, _, hl => absurd hl (by simp)
  | _ :: _, _ :: _, [], _, _, hl => absurd hl (by simp)

/-- **A body with no witness hint pops its callees' entries, in order.** -/
theorem pops_noWit {f : String} {fn : Fn} {σ : Val} {bufs : List ℕ} {es : List Ev} {vs : List V} {ts : List Tree}
    (hf : coreProgram.find? f = some fn) (hw : walk σ fn.body = .ret es vs) (hn : Stmt.noWitList fn.body = true)
    (hl : (calls es).length = ts.length) :
    (Memory.Tree.node f σ bufs ts).pops coreProgram rd = (Tree.popsKids coreProgram rd ts).flatten := by
  have hall := walk_noWit (σ := σ) fn.body hn
  rw [hw] at hall
  rw [Tree.pops, events_node hf hw]
  refine splice_mute es _ (fun e he => ?_) (by rw [length_popsKids, hl])
  have := hall e he
  cases e with
  | atom a =>
    cases a with
    | hint x => cases x <;> simp_all [Ev.noWit, atomNoWit, Ev.pops, Atom.pops, Hint.pops]
    | _ => rfl
  | _ => rfl

/-! ## The walk by hinted indices -/

/-- **Claims `s ..< s + m`'s indices.** -/
noncomputable def idxPops (o : ℕ → ℕ) (s m : ℕ) : List Pop :=
  (List.range m).map fun i => ("child_claim_index", [gen ^ o (s + i)])

theorem idxPops_append (o : ℕ → ℕ) (s A B : ℕ) : idxPops o s A ++ idxPops o (s + A) B = idxPops o s (A + B) := by
  simp only [idxPops, List.range_add, List.map_append, List.map_map]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp_apply, Nat.add_assoc]

theorem idxPops_shift (o : ℕ → ℕ) (c s m : ℕ) : idxPops (fun i => o (c + i)) s m = idxPops o (c + s) m := by
  simp only [idxPops, Nat.add_assoc]

theorem idxPops_flatMap (o : ℕ → ℕ) (m : ℕ) : ∀ M : ℕ,
    (List.range' 0 M).flatMap (fun q => idxPops o (m * q) m) = idxPops o 0 (m * M)
  | 0 => by simp [idxPops]
  | M + 1 => by
    rw [← List.range'_append_1 (s := 0) (m := M) (n := 1), List.flatMap_append, idxPops_flatMap o m M]
    simp only [Nat.zero_add, List.range'_one, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    have e := idxPops_append o 0 (m * M) m
    rw [Nat.zero_add] at e
    rw [e, Nat.mul_succ]

theorem idxPops_zero (o : ℕ → ℕ) (s : ℕ) : idxPops o s 0 = [] := rfl

/-! ## The gap walk -/

/-- **Claims `s ..< s + m`'s gaps.** -/
noncomputable def gapPops (o : ℕ → ℕ) (s m : ℕ) : List Pop :=
  (List.range m).map fun i => ("child_claim_gap", [gen ^ mGap o (s + i)])

theorem gapPops_append (o : ℕ → ℕ) (s A B : ℕ) : gapPops o s A ++ gapPops o (s + A) B = gapPops o s (A + B) := by
  simp only [gapPops, List.range_add, List.map_append, List.map_map]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp_apply, Nat.add_assoc]

theorem gapPops_flatMap (o : ℕ → ℕ) (s m : ℕ) : ∀ M : ℕ,
    (List.range' 0 M).flatMap (fun q => gapPops o (s + m * q) m) = gapPops o s (m * M)
  | 0 => by simp [gapPops]
  | M + 1 => by
    rw [← List.range'_append_1 (s := 0) (m := M) (n := 1), List.flatMap_append, gapPops_flatMap o s m M]
    simp only [Nat.zero_add, List.range'_one, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [gapPops_append, Nat.mul_succ]

theorem gapPops_zero (o : ℕ → ℕ) (s : ℕ) : gapPops o s 0 = [] := rfl

end
end LeanVM.Guest.Complete
