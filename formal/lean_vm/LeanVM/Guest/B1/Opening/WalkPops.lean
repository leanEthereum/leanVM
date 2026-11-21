/-
  LeanVM.Guest.B1.Opening.WalkPops

  The witness-stream entries `walk_path` pops at its honest values: its path's children (`merkle_children`).
-/

module

public import LeanVM.Guest.B1.Opening.QueriesComplete3
public import LeanVM.Guest.B1.Sig.PopsKit

/-!
# `walk_path`'s pops

* `noWit`, `fallPops_noWit`, `splicePops_noWit`: a block of atoms none a witness hint pops nothing; `SplicePops.callIf`: a conditional call pops its callee's entries;
* `wpPops w`: the children cells `w.pc` of an honest walk, one `merkle_children` entry;
* `wp_fallPops`: at the honest values the body before its return pops `wpPops w`;
* `wp_node_pops`: a call instance of a `walk_path` specialization at the honest valuation `w.val` pops `wpPops w`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory

@[expose] public section

variable {rd : Reader} {σ : Val}

/-- Every statement an atom, none a witness hint. -/
def noWit (ss : List Stmt) : Bool := ss.all fun s => match s with
  | .atom (.hint (.witness ..)) => false
  | .atom _ => true
  | _ => false

theorem noWit_append (xs ys : List Stmt) : noWit (xs ++ ys) = (noWit xs && noWit ys) := List.all_append

theorem noWit_iff {ss : List Stmt} : noWit ss = true ↔ ∀ s ∈ ss, (match s with
    | .atom (.hint (.witness ..)) => false
    | .atom _ => true
    | _ => false) = true := List.all_eq_true

/-- **A block of atoms none a witness hint pops nothing.** -/
theorem fallPops_noWit (σ : Val) : ∀ {ss : List Stmt}, noWit ss = true → FallPops rd σ ss []
  | [], _ => FallPops.nil
  | s :: ss, h => by
    simp only [noWit, List.all_cons, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    have ih := fallPops_noWit σ (ss := ss) h2
    match s, h1 with
    | .atom a, h1 =>
      have hp : a.pops rd σ = [] := by
        cases a with
        | hint x => cases x <;> simp_all [Atom.pops, Hint.pops]
        | _ => rfl
      simpa [hp] using ih.cons_atom (a := a)

theorem fallPops_eq {ss : List Stmt} {p q : List Pop} (h : FallPops rd σ ss p) (e : p = q) : FallPops rd σ ss q :=
  e ▸ h

theorem fallPops_flatten_nil : ∀ {l : List (List Stmt)}, (∀ x ∈ l, FallPops rd σ x []) →
    FallPops rd σ l.flatten []
  | [], _ => FallPops.nil
  | x :: l, h => by
    rw [List.flatten_cons]
    simpa using (h x (by simp)).append (fallPops_flatten_nil fun y hy => h y (by simp [hy]))

/-! ## Blocks and calls -/

theorem noWit_flatten_map {α : Type} {f : α → List Stmt} : ∀ {l : List α}, (∀ a ∈ l, noWit (f a) = true) →
    noWit (l.map f).flatten = true
  | [], _ => rfl
  | a :: l, h => by
    rw [List.map_cons, List.flatten_cons, noWit_append, h a (by simp),
      noWit_flatten_map fun b hb => h b (by simp [hb])]
    rfl

theorem SplicePops.congr_ks {ss : List Stmt} {ks ks' : List (List Pop)} {p : List Pop}
    (h : SplicePops rd σ ss ks p) (e : ks = ks') : SplicePops rd σ ss ks' p := e ▸ h

/-- **A conditional call pops its callee's entries**, a phantom's when not taken. -/
theorem SplicePops.callIf (c : V) (f : String) (args : List V) (k : List Pop) :
    SplicePops rd σ [.callIf c f args] [k] k := by
  refine ⟨[.inK c, if σ c = 0 then .skip f args else .call f args []], ?_, ?_, ?_⟩
  · simp [walk, walk1, Out.seq, Out.pre]
  · split <;> rfl
  · split <;> simp [splice]

theorem splicePops_noWit {ss : List Stmt} (h : noWit ss = true) : SplicePops rd σ ss [] [] :=
  SplicePops.of_fallPops (fallPops_noWit σ h)

/-! ## The walk -/

theorem oqStepT_noWit (pr ch l K n0 n1 : ℕ) (bit : Bool) : noWit (oqStepT pr ch l K n0 n1 bit) = true := rfl

theorem oqArmT_noWit (s : Oq) (pr kL ch i a : ℕ) : noWit (oqArmT s pr kL ch i a) = true := by
  rw [oqArmT, noWit_append, Bool.and_eq_true]
  refine ⟨noWit_iff.mpr fun st hst => ?_, rfl⟩
  obtain ⟨blk, hb, hst⟩ := List.mem_flatten.mp hst
  obtain ⟨r, -, rfl⟩ := List.mem_map.mp hb
  exact noWit_iff.mp (oqStepT_noWit _ _ _ _ _ _ _) st hst

theorem oqPadT_noWit (pr : ℕ) : noWit (oqPadT pr) = true := rfl

theorem oqCapT_noWit (s : Oq) (bp cap flags : V) (kL ch : ℕ) : noWit (oqCapT s bp cap flags kL ch) = true := rfl

namespace WD

variable (w : WD)

/-- **An honest walk's entries**: its path's children cells, one `merkle_children` entry. -/
def wpPops : List Pop := [("merkle_children", (List.range (4 * w.pd)).map w.pc)]

theorem win_fallPops (hv : w.Hv σ) {i : ℕ} (hi : i < oqNpw w.s) :
    FallPops rd σ (oqWinT w.s (.n 2) (wpPr w.s) 0 wpCh i) [] := by
  have s0 : σ (.n (oqWk w.s wpCh i)) = ofK (addressOfIndex (w.wv i)) := by
    rw [show oqWk w.s wpCh i = oqWk w.s wpCh i + 0 from rfl, hv,
      val_win w hi (by unfold winSz; omega), winV, ite_eq_left rfl, gen_pow_ofK]
  have hlt : w.wv i < 2 ^ oqWw w.s i := (qwVal_path hi w.q).1
  have h6 : 2 ^ oqWw w.s i ≤ 2 ^ 6 := Nat.pow_le_pow_right (by omega) (oqWw_le w.s i)
  have hpre : noWit ([.atom (.load (.n (oqWk w.s wpCh i)) (.n 2) i)] ++
      (if i = 0 then oqPadT (wpPr w.s) else []) ++
      [.atom (.const (.n (oqWk w.s wpCh i + 1 + oqWo i)) (word (2 ^ 63) 0))]) = true := by
    rw [noWit_append, noWit_append]
    split <;> rfl
  have e : oqWinT w.s (.n 2) (wpPr w.s) 0 wpCh i = ([.atom (.load (.n (oqWk w.s wpCh i)) (.n 2) i)] ++
      (if i = 0 then oqPadT (wpPr w.s) else []) ++
      [.atom (.const (.n (oqWk w.s wpCh i + 1 + oqWo i)) (word (2 ^ 63) 0))]) ++
      [.match_ (.n (oqWk w.s wpCh i)) ((List.range (2 ^ oqWw w.s i)).map (oqArmT w.s (wpPr w.s) 0 wpCh i))] := by
    simp [oqWinT]
  rw [e]
  have hm : FallPops rd σ [.match_ (.n (oqWk w.s wpCh i))
      ((List.range (2 ^ oqWw w.s i)).map (oqArmT w.s (wpPr w.s) 0 wpCh i))] [] :=
    FallPops.match_ (k := w.wv i) (by simpa using hlt) (by omega) s0 (by
      rw [List.getElem_map, List.getElem_range]
      exact fallPops_noWit σ (oqArmT_noWit _ _ _ _ _ _))
  exact fallPops_eq ((fallPops_noWit σ hpre).append hm) rfl

/-- **The body before its return pops the children**, at the honest values. -/
theorem wp_fallPops (hv : w.Hv σ) :
    FallPops rd σ (oqPathT w.s (.n 2) (wpPr w.s) 0 wpCh ++ oqCapT w.s (.n 2) (.n 3) (.n 4) 0 wpCh)
      w.wpPops := by
  have hh : FallPops rd σ [.atom (.hint (.witness "merkle_children"
      (.stack ((List.range (4 * w.s.pd)).map fun j ↦ .n (wpCh + j)))))] w.wpPops := by
    refine fallPops_eq (FallPops.atom _) ?_
    simp only [Atom.pops, Hint.pops, Dest.words, List.map_map, wpPops]
    congr 2
    refine List.map_congr_left fun j hj => ?_
    rw [Function.comp_apply, hv, val_pc w (List.mem_range.mp hj)]
  have hw : FallPops rd σ ((List.range (oqNpw w.s)).map (oqWinT w.s (.n 2) (wpPr w.s) 0 wpCh)).flatten [] :=
    fallPops_flatten_nil fun x hx => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      exact w.win_fallPops hv (List.mem_range.mp hi)
  exact fallPops_eq ((hh.append hw).append (fallPops_noWit σ (oqCapT_noWit _ _ _ _ _ _))) (by simp)

/-- **A `walk_path` call instance at the honest values pops the children.** -/
theorem wp_node_pops {P : Core.Program} {wlk : String} {fn : Fn} (hf : P.find? wlk = some fn)
    (hb : fn.body = wpBodyT w.s) (bufs : List ℕ) (kids : List Tree) :
    (Memory.Tree.node wlk (fun v : V ↦ w.val v.idx) bufs kids).pops P rd = w.wpPops := by
  obtain ⟨es, hw, hc, hp⟩ := retPops_of_fallPops (vs := []) (w.wp_fallPops (rd := rd) (σ := fun v : V ↦ w.val v.idx)
    fun _ ↦ rfl)
  rw [Tree.pops_node hf (by rw [hb, wpBodyT_eq]; exact hw)]
  have := splice_append_of_calls_nil (rd := rd) (σ := fun v : V ↦ w.val v.idx) (es := es) [] (Tree.popsKids P rd kids) hc
  rw [List.append_nil] at this
  rw [this, hp]
  simp [splice]

end WD

end
end LeanVM.Guest.B1
