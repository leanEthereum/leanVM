/-
  LeanVM.Guest.B2C.ShareSplit

  A sharing window that is one `match` of straight-line arms, checked by groups of its arms, each
  group in its own kernel evaluation over the cells of its own values.
-/

module

public import LeanVM.Guest.B2C.ShareSound
public import LeanVM.Guest.CheckSplit

/-!
# Sharing windows split by arms

The sharing check's window of one of `verify_sig_lean_sphincs`'s `match`es of `256` straight-line
arms (`Check.checkWinS` splits its soundness window) walks every arm from the state after the
selector, and joins them: the cells any arm occupies, the values every arm names. A group
(`shareWinS`) walks arm `0` and the arms `lo ≤ k < hi` over the cells of its own values
(`locG`), and checks that each arm's end refines the next window's snapshot; the groups together
give the window's check (`shareWin_of_split`): the group's cells are the window's on every value
it names (`locG_get`), so its arms' walks are the window's (`swL_atoms_congr`), and the join of
all the arms refines the snapshot when every arm's end does.
-/

namespace LeanVM.Guest.B2C

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Exec
open LeanVM.Guest.Check

@[expose] public section

/-! ## Walks on agreeing cells -/

theorem any_congr' {α : Type} {p q : α → Bool} : ∀ {l : List α}, (∀ a ∈ l, p a = q a) →
    l.any p = l.any q
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.any_cons, h a List.mem_cons_self,
      any_congr' (fun b hb ↦ h b (List.mem_cons_of_mem _ hb))]

section Congr

variable {L L' : Loc} {A : ℕ → Prop} (hA : ∀ n, A n → L.get? n = L'.get? n)
include hA

theorem cell_congr {v : V} (h : A v.idx) : L.cell v = L'.cell v := by
  unfold Loc.cell; rw [hA _ h]

theorem cellN_congr {n : ℕ} (h : A n) : cellN L n = cellN L' n := cell_congr hA (v := V.n n) h

theorem nameV_congr (sh : ℕ) (kc : ℕ → Option (ℕ × ℕ)) (st : SSt) {v : V} (h : A v.idx) :
    nameV L sh kc st v = nameV L' sh kc st v := by
  unfold nameV; rw [cell_congr hA h]

theorem nameAll_congr (sh : ℕ) (kc : ℕ → Option (ℕ × ℕ)) :
    ∀ (st : SSt) (vs : List V), (∀ v ∈ vs, A v.idx) → nameAll L sh kc st vs = nameAll L' sh kc st vs
  | _, [], _ => rfl
  | st, v :: vs, h => by
    simp only [nameAll, SSt.seq_eq]
    rw [nameV_congr hA sh kc st (h v List.mem_cons_self),
      nameAll_congr sh kc _ vs (fun w hw ↦ h w (List.mem_cons_of_mem _ hw))]

/-- A pending value's facts name values of `A` only. -/
def PfIn (A : ℕ → Prop) (p : PF) : Prop :=
  A p.v ∧ (∀ k ∈ p.keys, ∀ x ∈ k.2, A x) ∧ ∀ x ∈ p.eqs, A x

omit hA in
/-- The pending values' facts name values of `A` only. -/
def PendIn (A : ℕ → Prop) (st : SSt) : Prop := ∀ p ∈ st.pend, PfIn A p

theorem knownIn_congr (st : SSt) {n : ℕ} (h : A n) : knownIn L st n = knownIn L' st n := by
  unfold knownIn; rw [cellN_congr hA h]

theorem keyOk_congr (st : SSt) (c : ℕ) {k : ℕ × List ℕ} (h : ∀ x ∈ k.2, A x) :
    keyOk L st c k = keyOk L' st c k := by
  unfold keyOk
  rw [all_congr' fun x hx ↦ knownIn_congr hA st (h x hx),
    List.map_congr_left fun x hx ↦ cellN_congr hA (h x hx)]

theorem pfOk_congr (st : SSt) {p : PF} (h : PfIn A p) : pfOk L st p = pfOk L' st p := by
  unfold pfOk
  have h1 : p.keys.any (keyOk L st p.c) = p.keys.any (keyOk L' st p.c) :=
    any_congr' fun k hk ↦ keyOk_congr hA st p.c (h.2.1 k hk)
  have h2 : (p.eqs.any fun x ↦ isNamed st x && (cellN L x).beq p.c) =
      (p.eqs.any fun x ↦ isNamed st x && (cellN L' x).beq p.c) :=
    any_congr' fun x hx ↦ by rw [cellN_congr hA (h.2.2 x hx)]
  rw [h1, h2]

theorem splitPend_congr (st : SSt) :
    ∀ (ps : List PF), (∀ p ∈ ps, PfIn A p) → splitPend L st ps = splitPend L' st ps
  | [], _ => rfl
  | p :: ps, h => by
    simp only [splitPend]
    rw [splitPend_congr st ps (fun q hq ↦ h q (List.mem_cons_of_mem _ hq)),
      pfOk_congr hA st (h p List.mem_cons_self)]

theorem discharge_congr : ∀ (n : ℕ) (st : SSt), PendIn A st → discharge L n st = discharge L' n st
  | 0, _, _ => rfl
  | n + 1, st, h => by
    simp only [discharge]
    rw [splitPend_congr hA st st.pend h]
    rcases hs : splitPend L' st st.pend with ⟨ok, rest⟩
    cases ok with
    | nil => rfl
    | cons p ok =>
      simp only [natSeq_eq, SSt.seq_eq]
      apply discharge_congr n
      intro q hq
      exact h q ((splitPend_spec (loc := L') st st.pend hs).2.1 q hq)

end Congr

/-! ### Pending values stay among the walked values -/

theorem nameV_pend {L : Loc} {sh : ℕ} {kc : ℕ → Option (ℕ × ℕ)} {st : SSt} {v : V} :
    ∀ p ∈ (nameV L sh kc st v).pend, p ∈ st.pend ∨ p = ⟨v.idx, L.cell v, none, [], []⟩ := by
  intro p hp
  unfold nameV at hp
  simp only [natSeq_eq, Bool.cond_eq_ite, Bool.or_eq_true] at hp
  split_ifs at hp
  · exact Or.inl hp
  · exact Or.inl hp
  · rcases List.mem_cons.mp hp with rfl | hp
    · exact Or.inr rfl
    · exact Or.inl hp
  · exact Or.inl hp

theorem nameV_pendIn {A : ℕ → Prop} {L : Loc} {sh : ℕ} {kc : ℕ → Option (ℕ × ℕ)} {st : SSt}
    {v : V} (h : PendIn A st) (hv : A v.idx) : PendIn A (nameV L sh kc st v) := by
  intro p hp
  rcases nameV_pend p hp with hp | rfl
  · exact h p hp
  · exact ⟨hv, by simp, by simp⟩

theorem nameAll_pendIn {A : ℕ → Prop} {L : Loc} {sh : ℕ} {kc : ℕ → Option (ℕ × ℕ)} :
    ∀ {st : SSt} {vs : List V}, PendIn A st → (∀ v ∈ vs, A v.idx) → PendIn A (nameAll L sh kc st vs)
  | _, [], h, _ => h
  | _, v :: vs, h, hv => by
    simp only [nameAll, SSt.seq_eq]
    exact nameAll_pendIn (nameV_pendIn h (hv v List.mem_cons_self))
      (fun w hw ↦ hv w (List.mem_cons_of_mem _ hw))

theorem discharge_pendIn {A : ℕ → Prop} {L : Loc} : ∀ (n : ℕ) {st : SSt}, PendIn A st →
    PendIn A (discharge L n st)
  | 0, _, h => h
  | n + 1, st, h => by
    simp only [discharge]
    rcases hs : splitPend L st st.pend with ⟨ok, rest⟩
    cases ok with
    | nil => exact h
    | cons p ok =>
      simp only [natSeq_eq, SSt.seq_eq]
      exact discharge_pendIn n fun q hq ↦ h q ((splitPend_spec (loc := L) st st.pend hs).2.1 q hq)

/-- The values an atom's keys and equalities name are its own. -/
theorem keysOf_vals {a : Core.Atom} {v : ℕ} {k : ℕ × List ℕ} (hk : k ∈ keysOf a v) :
    ∀ x ∈ k.2, ∃ w ∈ Memory.atomUses a, w.idx = x := by
  cases a <;> simp [keysOf, Memory.atomUses, Bool.cond_eq_ite] at hk ⊢ <;> aesop

theorem eqsOf_vals {a : Core.Atom} {v x : ℕ} (hx : x ∈ eqsOf a v) :
    ∃ w ∈ Memory.atomUses a, w.idx = x := by
  cases a <;> simp [eqsOf, Memory.atomUses, Bool.cond_eq_ite] at hx ⊢ <;> aesop

theorem addFacts_pendIn {A : ℕ → Prop} {a : Core.Atom} {ps : List PF}
    (h : ∀ p ∈ ps, PfIn A p) (ha : ∀ w ∈ Memory.atomUses a, A w.idx) :
    ∀ p ∈ addFacts a ps, PfIn A p := by
  intro p hp
  simp only [addFacts, List.mem_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  obtain ⟨h1, h2, h3⟩ := h q hq
  refine ⟨h1, fun k hk x hx ↦ ?_, fun x hx ↦ ?_⟩
  · rcases List.mem_append.mp hk with hk | hk
    · obtain ⟨w, hw, rfl⟩ := keysOf_vals hk x hx
      exact ha w hw
    · exact h2 k hk x hx
  · rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨w, hw, rfl⟩ := eqsOf_vals hx
      exact ha w hw
    · exact h3 x hx

section Congr2

variable {L L' : Loc} {A : ℕ → Prop} (hA : ∀ n, A n → L.get? n = L'.get? n)
include hA

theorem recCst_congr (sh : ℕ) {a : Core.Atom} (ha : ∀ w ∈ Memory.atomUses a, A w.idx)
    (cst : Exec.Trie (ℕ × ℕ)) : recCst L sh a cst = recCst L' sh a cst := by
  cases a <;> simp only [recCst]
  · rw [cell_congr hA (ha _ (by simp [Memory.atomUses]))]
  · rw [cell_congr hA (ha _ (by simp [Memory.atomUses]))]

theorem cellKeys_congr {a : Core.Atom} (ha : ∀ w ∈ Memory.atomUses a, A w.idx) :
    cellKeys L a = cellKeys L' a := by
  cases a <;> simp only [cellKeys]
  case add d x y =>
    simp only [Memory.atomUses, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at ha
    rw [cell_congr hA ha.1, cell_congr hA ha.2.1, cell_congr hA ha.2.2]
  case mul d x y =>
    simp only [Memory.atomUses, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at ha
    rw [cell_congr hA ha.1, cell_congr hA ha.2.1, cell_congr hA ha.2.2]
  case load d p off =>
    simp only [Memory.atomUses, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at ha
    rw [cell_congr hA ha.1, cell_congr hA ha.2]
  case keccak ins outs inOdd outOdd =>
    simp only [Memory.atomUses, List.mem_append] at ha
    rw [List.map_congr_left fun x hx ↦ cell_congr hA (ha x (Or.inl hx))]
    exact List.map_congr_left fun q hq ↦ by
      rw [cell_congr hA (ha q.1 (Or.inr (List.fst_mem_of_mem_zipIdx hq)))]

theorem record_congr (sh : ℕ) {a : Core.Atom} (ha : ∀ w ∈ Memory.atomUses a, A w.idx) (st : SSt) :
    record L sh a st = record L' sh a st := by
  unfold record
  rw [recCst_congr hA sh ha, cellKeys_congr hA ha]

theorem stepAtom_congr (sh : ℕ) {a : Core.Atom} (ha : ∀ w ∈ Memory.atomUses a, A w.idx) (st : SSt)
    (hs : PendIn A st) : stepAtom L sh st a = stepAtom L' sh st a := by
  unfold stepAtom
  simp only [SSt.seq_eq]
  rw [nameAll_congr hA sh _ st _ ha]
  have hp : PendIn A ⟨(nameAll L' sh (constOf a) st (Memory.atomUses a)).occ,
      (nameAll L' sh (constOf a) st (Memory.atomUses a)).cst,
      (nameAll L' sh (constOf a) st (Memory.atomUses a)).keys,
      (nameAll L' sh (constOf a) st (Memory.atomUses a)).named,
      addFacts a (nameAll L' sh (constOf a) st (Memory.atomUses a)).pend⟩ :=
    addFacts_pendIn (nameAll_pendIn hs ha) ha
  rw [discharge_congr hA _ _ hp, record_congr hA sh ha]

end Congr2

theorem record_pend {L : Loc} {sh : ℕ} {a : Core.Atom} {st : SSt} : (record L sh a st).pend = st.pend := by
  unfold record
  cases (Memory.atomUses a).all fun v ↦ isNamed st v.idx <;> rfl

theorem stepAtom_pendIn {A : ℕ → Prop} {L : Loc} {sh : ℕ} {a : Core.Atom} {st : SSt}
    (hs : PendIn A st) (ha : ∀ w ∈ Memory.atomUses a, A w.idx) : PendIn A (stepAtom L sh st a) := by
  unfold stepAtom
  simp only [SSt.seq_eq]
  intro p hp
  rw [record_pend] at hp
  exact discharge_pendIn (st := ⟨_, _, _, _, addFacts a (nameAll L sh (constOf a) st
    (Memory.atomUses a)).pend⟩) _ (addFacts_pendIn (nameAll_pendIn hs ha) ha) p hp

section Congr3

variable {L L' : Loc} {A : ℕ → Prop} (hA : ∀ n, A n → L.get? n = L'.get? n)
include hA

theorem runListed_congr (l : List (ℕ × ℕ)) (base : ℕ) :
    ∀ (k : ℕ) (vs : List V), (∀ v ∈ vs, A v.idx) → runListed L l base k vs = runListed L' l base k vs
  | _, [], _ => rfl
  | k, v :: vs, h => by
    simp only [runListed]
    rw [cell_congr hA (h v List.mem_cons_self),
      runListed_congr l base (k + 1) vs (fun w hw ↦ h w (List.mem_cons_of_mem _ hw))]

theorem atomListed_congr (tt : Exec.Trie ℕ) (P : Plumb) {a : Core.Atom}
    (h : ∀ w ∈ Memory.atomUses a ++ Memory.atomTmps a, A w.idx) :
    atomListed L tt P a = atomListed L' tt P a := by
  cases a with
  | rangeCheck x y t1 t2 k =>
    simp only [atomListed]
    rw [cell_congr hA (h t1 (by simp [Memory.atomTmps])), cell_congr hA (h t2 (by simp [Memory.atomTmps]))]
  | frameAddr p run =>
    cases run with
    | nil => rfl
    | cons r rs =>
      simp only [atomListed]
      rw [cell_congr hA (h r (by simp [Memory.atomUses])),
        runListed_congr hA _ _ 0 (r :: rs) (fun w hw ↦ h w (by
          simp only [Memory.atomUses, List.mem_append, List.mem_cons]
          rcases List.mem_cons.mp hw with hw | hw
          · exact Or.inl (Or.inr (Or.inl hw))
          · exact Or.inl (Or.inr (Or.inr hw))))]
  | _ => rfl

/-- **The sharing walk of atoms on agreeing cells**: the same. -/
theorem swL_atoms_congr (sh : ℕ) (tt : Exec.Trie ℕ) (P : Plumb) :
    ∀ (ss : List Stmt) (st : SSt), ss.all isAtomS = true →
      (∀ v ∈ Memory.Stmt.usesList ss ++ Memory.Stmt.tmpsList ss, A v.idx) → PendIn A st →
        swL L sh tt P st ss = swL L' sh tt P st ss
  | [], _, _, _, _ => by simp only [swL]
  | .atom a :: ss, st, hs, hv, hp => by
    simp only [List.all_cons, isAtomS, Bool.true_and] at hs
    have ha : ∀ w ∈ Memory.atomUses a ++ Memory.atomTmps a, A w.idx := fun w hw ↦ hv w (by
      simp only [Memory.Stmt.usesList, Memory.Stmt.tmpsList, Memory.Stmt.uses, Memory.Stmt.tmps,
        List.mem_append] at hw ⊢
      rcases hw with hw | hw
      · exact Or.inl (Or.inl hw)
      · exact Or.inr (Or.inl hw))
    have hss : ∀ w ∈ Memory.Stmt.usesList ss ++ Memory.Stmt.tmpsList ss, A w.idx := fun w hw ↦ hv w (by
      simp only [Memory.Stmt.usesList, Memory.Stmt.tmpsList, List.mem_append] at hw ⊢
      rcases hw with hw | hw
      · exact Or.inl (Or.inr hw)
      · exact Or.inr (Or.inr hw))
    have hu : ∀ w ∈ Memory.atomUses a, A w.idx := fun w hw ↦ ha w (List.mem_append_left _ hw)
    simp only [swL, swS]
    rw [atomListed_congr hA tt P ha]
    cases atomListed L' tt P a
    · rfl
    · simp only [Bool.cond_true, SSt.seq_eq]
      rw [stepAtom_congr hA sh hu st hp,
        swL_atoms_congr sh tt P ss _ hs hss (stepAtom_pendIn hp hu)]
  | .ite .. :: _, _, hs, _, _ => by simp [isAtomS] at hs
  | .match_ .. :: _, _, hs, _, _ => by simp [isAtomS] at hs
  | .call .. :: _, _, hs, _, _ => by simp [isAtomS] at hs
  | .callIf .. :: _, _, hs, _, _ => by simp [isAtomS] at hs
  | .dispatch .. :: _, _, hs, _, _ => by simp [isAtomS] at hs
  | .ret .. :: _, _, hs, _, _ => by simp [isAtomS] at hs

end Congr3

/-! ## A group's cells -/

/-- A group's cells in window `i`: the window's of the values `lo + gm` on (`gn` of them) packed, those
of arm `0`'s values `lo + am` on (`an`) and of the values named outside the window in a trie. -/
noncomputable def locG (C : Cert) (i gm gn am an : ℕ) : Loc :=
  ⟨listElementOrDefault C.los i 0 + gm, (((listElementOrDefault C.cells i []).drop gm).take
      gn).length,
    packCells (((listElementOrDefault C.cells i []).drop gm).take gn),
    locTrieFrom (((listElementOrDefault C.cells i []).drop am).take an) (listElementOrDefault C.los
        i 0 + am)
      (insTrie (listElementOrDefault C.ins i []) .nil)⟩

/-- What a window split by arms checks once: its cells below `2^16`, the values it names outside
it below it, all within the tries' depth. -/
def shareFits (C : Cert) (i : ℕ) : Bool :=
  (listElementOrDefault C.cells i []).all (fun c ↦ Nat.blt c 65536) &&
    Nat.blt (listElementOrDefault C.los i 0 + (listElementOrDefault C.cells i []).length) (2
        ^ 19) &&
    (listElementOrDefault C.ins i []).all fun p ↦ Nat.blt p.1 (listElementOrDefault C.los i 0)

theorem locG_get {C : Cert} {i gm gn am an : ℕ} (hf : shareFits C i = true)
    (ha : listElementOrDefault C.los i 0 + am + an < 2 ^ 19) {v c : ℕ}
    (h : (locG C i gm gn am an).get? v = some c) : (locW C i).get? v = some c := by
  simp only [shareFits, Bool.and_eq_true, List.all_eq_true, Nat.blt_eq] at hf
  obtain ⟨⟨hc, hlo⟩, hins⟩ := hf
  set cells := listElementOrDefault C.cells i []
  set lo := listElementOrDefault C.los i 0
  have hd : (2 : ℕ) ^ indexDepth = 2 * 2 ^ 19 := by simp [indexDepth]
  -- the window reads `cells[v - lo]` in its range
  have hwin : ∀ (hm : v - lo < cells.length), lo ≤ v → (locW C i).get? v = some cells[v - lo] := by
    intro hm hv
    have hcond : (Nat.ble lo v && Nat.blt v (Nat.add lo cells.length)) = true := by
      simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq]
      exact ⟨hv, by show v < lo + cells.length; omega⟩
    show (bif Nat.ble lo v && Nat.blt v (Nat.add lo cells.length) then
      some (Nat.mod (Nat.div (packCells cells) (Nat.pow 65536 (Nat.sub v lo))) 65536)
      else getF (insTrie (listElementOrDefault C.ins i []) .nil) v) = _
    rw [hcond, Bool.cond_true]
    exact congrArg some (packCells_digit cells _ hm hc)
  have hg : (locG C i gm gn am an).get? v =
      (bif Nat.ble (lo + gm) v && Nat.blt v ((lo + gm) + ((cells.drop gm).take gn).length) then
        some (packCells ((cells.drop gm).take gn) / 65536 ^ (v - (lo + gm)) % 65536)
      else getF (locTrieFrom ((cells.drop am).take an) (lo + am) (insTrie (listElementOrDefault C.ins i []) .nil)) v) := rfl
  rw [hg] at h
  cases hr : (Nat.ble (lo + gm) v && Nat.blt v ((lo + gm) + ((cells.drop gm).take gn).length))
  · rw [hr, Bool.cond_false] at h
    have hlen : lo + am + ((cells.drop am).take an).length < 2 ^ indexDepth := by
      simp only [List.length_take]
      have := Nat.min_le_left an (cells.drop am).length
      omega
    rw [locTrieFrom_getF _ _ _ v hlen] at h
    by_cases ha : lo + am ≤ v ∧ v < lo + am + ((cells.drop am).take an).length
    · simp only [ha, and_self, ↓reduceIte] at h
      simp only [List.length_take, List.length_drop] at ha
      rw [List.getElem?_take] at h
      have hlt : v - (lo + am) < an := by have := Nat.min_le_left an (cells.length - am); omega
      simp only [hlt, ↓reduceIte] at h
      rw [List.getElem?_drop, show am + (v - (lo + am)) = v - lo by omega] at h
      obtain ⟨hm, hg'⟩ := List.getElem?_eq_some_iff.mp h
      rw [hwin hm (by omega), hg']
    · simp only [ha, ↓reduceIte] at h
      have hk : v ∈ (listElementOrDefault C.ins i []).map (·.1) := by
        by_contra hk
        rw [insTrie_getF_of_not _ _ v (fun p hp ↦ by have := hins p hp; omega) hk] at h
        simp [getF_eq] at h
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hk
      have hplo := hins p hp
      have hcond : (Nat.ble lo p.1 && Nat.blt p.1 (Nat.add lo cells.length)) = false := by
        have : Nat.ble lo p.1 = false := by
          rw [Bool.eq_false_iff]; intro h'; rw [Nat.ble_eq] at h'; omega
        rw [this, Bool.false_and]
      show (bif Nat.ble lo p.1 && Nat.blt p.1 (Nat.add lo cells.length) then
        some (Nat.mod (Nat.div (packCells cells) (Nat.pow 65536 (Nat.sub p.1 lo))) 65536)
        else getF (insTrie (listElementOrDefault C.ins i []) .nil) p.1) = _
      rw [hcond, Bool.cond_false]
      exact h
  · rw [hr, Bool.cond_true] at h
    simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hr
    obtain ⟨h1, h2⟩ := hr
    have hm : v - (lo + gm) < ((cells.drop gm).take gn).length := by omega
    have hdg := packCells_digit _ _ hm (fun c' hc' ↦ hc c' (List.mem_of_mem_drop (List.mem_of_mem_take hc')))
    simp only [List.length_take, List.length_drop] at h2
    have e : ((cells.drop gm).take gn)[v - (lo + gm)] = cells[v - lo]'(by omega) := by
      simp only [List.getElem_take, List.getElem_drop]
      congr 1; omega
    rw [hdg, e] at h
    rw [hwin (by omega) (by omega)]
    exact h

/-! ## A sharing window by groups -/

section Congr4

variable {L L' : Loc} {A : ℕ → Prop} (hA : ∀ n, A n → L.get? n = L'.get? n)
include hA

theorem valOk_congr (tt : Exec.Trie ℕ) (tc fc n : ℕ) {v : V} (h : A v.idx) :
    valOk L tt tc fc n v = valOk L' tt tc fc n v := by
  unfold valOk; rw [hA _ h, cell_congr hA h]

theorem nameStep_congr (sh : ℕ) (st : SSt) (vs : List V) (hs : PendIn A st)
    (hv : ∀ v ∈ vs, A v.idx) : nameStep L sh st vs = nameStep L' sh st vs := by
  unfold nameStep
  simp only [SSt.seq_eq]
  rw [nameAll_congr hA sh _ st vs hv, discharge_congr hA _ _ (nameAll_pendIn hs hv)]

end Congr4

/-- The next snapshot's facts on cells and keys, which a join keeps from the state before its
branches, and the cells that state occupies. -/
noncomputable def refinesPre (m : SSt) (s : Snap) : Bool :=
  Nat.beq (Nat.land m.occ s.occ) m.occ &&
    s.cst.all (fun q ↦ getF m.cst q.1 == some q.2) &&
    s.keys.all (fun q ↦ ((getF m.keys q.1).getD []).any fun k ↦ k == q.2)

/-- An arm's end and the next snapshot: the cells it occupies occupied there, the values named
there named. -/
noncomputable def armRef (b : SSt) (s : Snap) : Bool :=
  Nat.beq (Nat.land b.occ s.occ) b.occ && s.named.all (bitN b.named)

/-- Arm `0` and the arms `lo ≤ k < hi` (from index `k`), walked from `st1`, end in states
refining `s`. -/
noncomputable def armsRef (loc : Loc) (sh : ℕ) (tt : Exec.Trie ℕ) (P : Plumb) (st1 : SSt) (s : Snap)
    (lo hi : ℕ) : ℕ → List (List Stmt) → Bool
  | _, [] => true
  | k, a :: as => (bif Nat.beq k 0 || (Nat.ble lo k && Nat.blt k hi) then
      (match swL loc sh tt P st1 a with
        | some b => armRef b s
        | none => false)
      else true) && armsRef loc sh tt P st1 s lo hi (k + 1) as

theorem armsRef_get {loc : Loc} {sh : ℕ} {tt : Exec.Trie ℕ} {P : Plumb} {st1 : SSt} {s : Snap}
    {lo hi : ℕ} : ∀ {k : ℕ} {as : List (List Stmt)}, armsRef loc sh tt P st1 s lo hi k as = true →
      ∀ e (he : e < as.length), (k + e = 0 ∨ (lo ≤ k + e ∧ k + e < hi)) →
        ∃ b, swL loc sh tt P st1 as[e] = some b ∧ armRef b s = true
  | _, [], _, _, he, _ => absurd he (Nat.not_lt_zero _)
  | k, a :: as, h, e, he, hsel => by
    simp only [armsRef, Bool.and_eq_true] at h
    cases e with
    | zero =>
      have hc : (Nat.beq k 0 || (Nat.ble lo k && Nat.blt k hi)) = true := by
        simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq, Nat.blt_eq]; omega
      have h1 := h.1
      rw [hc, Bool.cond_true] at h1
      split at h1
      · rename_i b hb
        exact ⟨b, hb, h1⟩
      · simp at h1
    | succ e =>
      exact armsRef_get h.2 e (by simpa using he) (by omega)

theorem swArms_some {loc : Loc} {sh : ℕ} {tt : Exec.Trie ℕ} {P : Plumb} {st1 : SSt} {Q : SSt → Prop} :
    ∀ (arms : List (List Stmt)), (∀ e (he : e < arms.length), ∃ b, swL loc sh tt P st1 arms[e] = some b ∧ Q b) →
      ∃ bs, swArms loc sh tt P st1 arms = some bs ∧ bs.length = arms.length ∧ ∀ b ∈ bs, Q b
  | [], _ => ⟨[], by simp [swArms], rfl, by simp⟩
  | a :: as, h => by
    obtain ⟨b, hb, hq⟩ := h 0 (by simp)
    obtain ⟨bs, hbs, hl, hq'⟩ := swArms_some as fun e he ↦ by
      have := h (e + 1) (by simp; omega)
      simpa only [List.getElem_cons_succ] using this
    refine ⟨b :: bs, ?_, by simp [hl], ?_⟩
    · simp only [swArms]
      rw [show swL loc sh tt P st1 a = some b by simpa using hb, hbs]
    · intro b' hb'
      rcases List.mem_cons.mp hb' with rfl | hb'
      · exact hq
      · exact hq' b' hb'

theorem land_beq_iff (x y : ℕ) : Nat.beq (Nat.land x y) x = true ↔ ∀ i, x.testBit i → y.testBit i := by
  rw [Nat.beq_eq]
  constructor
  · intro h i hi
    rw [← h, testBit_land'] at hi
    simp only [Bool.and_eq_true] at hi
    exact hi.2
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [testBit_land']
    cases hx : x.testBit i
    · simp
    · simp [h i hx]

theorem testBit_foldl_land_of (bs : List SSt) : ∀ (s n : ℕ), s.testBit n = true →
    (∀ b ∈ bs, b.named.testBit n = true) → (bs.foldl (fun t b ↦ Nat.land t b.named) s).testBit n = true := by
  induction bs with
  | nil => intro s n h _; simpa using h
  | cons b bs ih =>
    intro s n hs hb
    rw [List.foldl_cons]
    apply ih
    · rw [testBit_land', hs, hb b List.mem_cons_self]; rfl
    · exact fun b' hb' ↦ hb b' (List.mem_cons_of_mem _ hb')

/-- **The join refines the snapshot** when the state before the arms and every arm's end do. -/
theorem refines_join {st1 : SSt} {bs : List SSt} {s : Snap} (h1 : refinesPre st1 s = true)
    (hb : ∀ b ∈ bs, armRef b s = true) (hne : bs ≠ []) : refines (joinSt st1 bs) s = true := by
  simp only [refinesPre, Bool.and_eq_true] at h1
  obtain ⟨⟨hocc, hcst⟩, hkeys⟩ := h1
  simp only [refines, joinSt, Bool.and_eq_true]
  refine ⟨⟨⟨?_, ?_⟩, hcst⟩, hkeys⟩
  · rw [land_beq_iff]
    intro i hi
    rcases (testBit_foldl_lor bs st1.occ i).mp hi with hi | ⟨b, hbm, hbi⟩
    · exact (land_beq_iff _ _).mp hocc i hi
    · have := hb b hbm
      simp only [armRef, Bool.and_eq_true] at this
      exact (land_beq_iff _ _).mp this.1 i hbi
  · obtain ⟨b, bs', rfl⟩ := List.exists_cons_of_ne_nil hne
    refine List.all_eq_true.mpr fun n hn ↦ ?_
    have hall : ∀ b' ∈ b :: bs', b'.named.testBit n = true := fun b' hb' ↦ by
      have := hb b' hb'
      simp only [armRef, Bool.and_eq_true, List.all_eq_true] at this
      rw [← bitN_eq]
      exact this.2 n hn
    rw [bitN_eq]
    exact testBit_foldl_land_of bs' _ n (hall b List.mem_cons_self)
      (fun b' hb' ↦ hall b' (List.mem_cons_of_mem _ hb'))

theorem mem_usesArms {x : V} : ∀ {as : List (List Stmt)}, x ∈ Memory.Stmt.usesArms as ↔
    ∃ e, ∃ he : e < as.length, x ∈ Memory.Stmt.usesList as[e]
  | [] => by simp [Memory.Stmt.usesArms]
  | a :: as => by
    simp only [Memory.Stmt.usesArms, List.mem_append, mem_usesArms]
    constructor
    · rintro (h | ⟨e, he, h⟩)
      · exact ⟨0, by simp, by simpa using h⟩
      · exact ⟨e + 1, by simpa using he, by simpa using h⟩
    · rintro ⟨e, he, h⟩
      cases e with
      | zero => exact Or.inl (by simpa using h)
      | succ e => exact Or.inr ⟨e, by simpa using he, by simpa using h⟩

theorem mem_tmpsArms {x : V} : ∀ {as : List (List Stmt)}, x ∈ Memory.Stmt.tmpsArms as ↔
    ∃ e, ∃ he : e < as.length, x ∈ Memory.Stmt.tmpsList as[e]
  | [] => by simp [Memory.Stmt.tmpsArms]
  | a :: as => by
    simp only [Memory.Stmt.tmpsArms, List.mem_append, mem_tmpsArms]
    constructor
    · rintro (h | ⟨e, he, h⟩)
      · exact ⟨0, by simp, by simpa using h⟩
      · exact ⟨e + 1, by simpa using he, by simpa using h⟩
    · rintro ⟨e, he, h⟩
      cases e with
      | zero => exact Or.inl (by simpa using h)
      | succ e => exact Or.inr ⟨e, by simpa using he, by simpa using h⟩

/-- The values a window of one `match` names: the selector's, or arm `e`'s. -/
theorem mem_vals_match {x : V} {a0 : List Stmt} {as : List (List Stmt)} {v : V} :
    v ∈ Memory.Stmt.usesList [.match_ x (a0 :: as)] ++ Memory.Stmt.tmpsList [.match_ x (a0 :: as)] ↔
      v = x ∨ ∃ e, ∃ he : e < (a0 :: as).length,
        v ∈ Memory.Stmt.usesList (a0 :: as)[e] ++ Memory.Stmt.tmpsList (a0 :: as)[e] := by
  simp only [Memory.Stmt.usesList, Memory.Stmt.tmpsList, Memory.Stmt.uses, Memory.Stmt.tmps,
    List.append_nil, List.mem_append, List.mem_cons]
  rw [mem_usesArms, mem_tmpsArms]
  constructor
  · rintro ((h | ⟨e, he, h⟩) | ⟨e, he, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨e, he, Or.inl h⟩
    · exact Or.inr ⟨e, he, Or.inr h⟩
  · rintro (h | ⟨e, he, h | h⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr ⟨e, he, h⟩)
    · exact Or.inr ⟨e, he, h⟩

/-- **The check of a group of a sharing window of one `match`**: arm `0` and the arms
`lo ≤ k < hi`, atoms all, their values named and in the frame over the group's cells (`locG`), and,
from the state after the selector (no value pending), each arm's end and that state refining the
next window's snapshot. Neither the first window nor the last. -/
noncomputable def shareWinS (j : ℕ) (snaps : List Snap) (k lo hi gm gn am an : ℕ) : Bool :=
  !(k == 0) && Nat.blt k snaps.length &&
  Nat.blt (listElementOrDefault (certOf j).los (winW snaps k) 0 + am + an) (2 ^ 19) &&
  (locG (certOf j) (winW snaps k) gm gn am an).seq fun loc ↦ natSeq (bitsOf (plumbOf j).sh) fun sh ↦
  natSeq (tmpCells (plumbOf j)) fun tc ↦ natSeq (fpgCells (plumbOf j)) fun fc ↦
  (byCell (plumbOf j).tmps).seq fun tt ↦
  match stmtsW (coreOf j).body snaps k with
  | [.match_ x (a0 :: as)] =>
      matchAtoms lo hi [.match_ x (a0 :: as)] &&
      (Memory.Stmt.usesList (selStmts lo hi [.match_ x (a0 :: as)]) ++
        Memory.Stmt.tmpsList (selStmts lo hi [.match_ x (a0 :: as)])).all (valOk loc tt tc fc (fsN j)) &&
      (nameStep loc sh (snapAt snaps k).st [x]).seq fun st1 ↦
        st1.pend.isEmpty && refinesPre st1 (snapAt snaps (k + 1)) &&
        armsRef loc sh tt (plumbOf j) st1 (snapAt snaps (k + 1)) lo hi 0 (a0 :: as)
  | _ => false

theorem shareWin_of_split {j k : ℕ} (gs : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ))
    (g0 : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) (hg0 : g0 ∈ gs)
    (hcov : coverOk (gs.map fun g ↦ (g.1, g.2.1)) (stmtsW (coreOf j).body (snapsOf j) k) = true)
    (hf : shareFits (certOf j) (winW (snapsOf j) k) = true)
    (h : ∀ g ∈ gs, shareWinS j (snapsOf j) k g.1 g.2.1 g.2.2.1 g.2.2.2.1 g.2.2.2.2.1 g.2.2.2.2.2 = true) :
    shareWin j (snapsOf j) k = true := by
  obtain ⟨x, a0, as, hss⟩ : ∃ x a0 as, stmtsW (coreOf j).body (snapsOf j) k = [.match_ x (a0 :: as)] := by
    revert hcov
    unfold coverOk
    split
    · rename_i x a0 as heq
      exact fun _ ↦ ⟨x, a0, as, by assumption⟩
    · simp
  have hcov' : ∀ e < as.length, ∃ g ∈ gs, g.1 ≤ e + 1 ∧ e + 1 < g.2.1 := by
    intro e he
    rw [hss] at hcov
    simp only [coverOk, List.all_eq_true, List.mem_range, List.any_eq_true, Bool.and_eq_true,
      Nat.ble_eq, Nat.blt_eq] at hcov
    obtain ⟨g', hg', h1, h2⟩ := hcov e he
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hg'
    exact ⟨g, hg, h1, h2⟩
  -- each group's facts
  have hG : ∀ g ∈ gs, ((k ≠ 0 ∧ k < (snapsOf j).length) ∧
      listElementOrDefault (certOf j).los (winW (snapsOf j) k) 0 + g.2.2.2.2.1 + g.2.2.2.2.2 < 2
          ^ 19) ∧
      (matchAtoms g.1 g.2.1 [Stmt.match_ x (a0 :: as)] = true ∧
        ∀ v ∈ Memory.Stmt.usesList (selStmts g.1 g.2.1 [Stmt.match_ x (a0 :: as)]) ++
            Memory.Stmt.tmpsList (selStmts g.1 g.2.1 [Stmt.match_ x (a0 :: as)]),
          valOk (locG (certOf j) (winW (snapsOf j) k) g.2.2.1 g.2.2.2.1 g.2.2.2.2.1 g.2.2.2.2.2)
            (byCell (plumbOf j).tmps) (tmpCells (plumbOf j)) (fpgCells (plumbOf j)) (fsN j) v = true) ∧
      ((nameStep (locG (certOf j) (winW (snapsOf j) k) g.2.2.1 g.2.2.2.1 g.2.2.2.2.1 g.2.2.2.2.2)
          (bitsOf (plumbOf j).sh) (snapAt (snapsOf j) k).st [x]).pend.isEmpty = true ∧
        refinesPre (nameStep (locG (certOf j) (winW (snapsOf j) k) g.2.2.1 g.2.2.2.1 g.2.2.2.2.1
          g.2.2.2.2.2) (bitsOf (plumbOf j).sh) (snapAt (snapsOf j) k).st [x])
          (snapAt (snapsOf j) (k + 1)) = true) ∧
      armsRef (locG (certOf j) (winW (snapsOf j) k) g.2.2.1 g.2.2.2.1 g.2.2.2.2.1 g.2.2.2.2.2)
        (bitsOf (plumbOf j).sh) (byCell (plumbOf j).tmps) (plumbOf j)
        (nameStep (locG (certOf j) (winW (snapsOf j) k) g.2.2.1 g.2.2.2.1 g.2.2.2.2.1 g.2.2.2.2.2)
          (bitsOf (plumbOf j).sh) (snapAt (snapsOf j) k).st [x])
        (snapAt (snapsOf j) (k + 1)) g.1 g.2.1 0 (a0 :: as) = true := by
    intro g hg
    have hc := h g hg
    unfold shareWinS at hc
    rw [hss] at hc
    simp only [Loc.seq_eq, natSeq_eq, Exec.Trie.seq_eq, SSt.seq_eq, Bool.and_eq_true,
      Bool.not_eq_true', beq_eq_false_iff_ne, Nat.blt_eq, List.all_eq_true] at hc
    exact hc
  obtain ⟨⟨⟨hk0, hkl⟩, -⟩, -⟩ := hG g0 hg0
  -- a group's cells are the window's wherever it has one
  have hag : ∀ g ∈ gs, ∀ n, ((locG (certOf j) (winW (snapsOf j) k) g.2.2.1 g.2.2.2.1 g.2.2.2.2.1
      g.2.2.2.2.2).get? n).isSome →
      (locG (certOf j) (winW (snapsOf j) k) g.2.2.1 g.2.2.2.1 g.2.2.2.2.1 g.2.2.2.2.2).get? n =
        (locW (certOf j) (winW (snapsOf j) k)).get? n := by
    intro g hg n hn
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hn
    rw [hc, locG_get hf (hG g hg).1.2 hc]
  have hsome : ∀ {L : Loc} {tt : Exec.Trie ℕ} {tc fc n : ℕ} {v : V}, valOk L tt tc fc n v = true →
      (L.get? v.idx).isSome := by
    intro L tt tc fc n v h
    simp only [valOk, Bool.and_eq_true] at h
    exact h.1.1.1.2
  -- the values a group names
  have hval : ∀ g ∈ gs, ∀ v ∈ Memory.Stmt.usesList (selStmts g.1 g.2.1 [Stmt.match_ x (a0 :: as)]) ++
      Memory.Stmt.tmpsList (selStmts g.1 g.2.1 [Stmt.match_ x (a0 :: as)]),
      ((locG (certOf j) (winW (snapsOf j) k) g.2.2.1 g.2.2.2.1 g.2.2.2.2.1 g.2.2.2.2.2).get? v.idx).isSome :=
    fun g hg v hv ↦ hsome ((hG g hg).2.1.2 v hv)
  have hsel : ∀ g ∈ gs, ∀ e (he : e < (a0 :: as).length), (e = 0 ∨ (g.1 ≤ e ∧ e < g.2.1)) →
      ∀ v ∈ Memory.Stmt.usesList (a0 :: as)[e] ++ Memory.Stmt.tmpsList (a0 :: as)[e],
        v ∈ Memory.Stmt.usesList (selStmts g.1 g.2.1 [Stmt.match_ x (a0 :: as)]) ++
          Memory.Stmt.tmpsList (selStmts g.1 g.2.1 [Stmt.match_ x (a0 :: as)]) := by
    intro g _ e he hse v hv
    simp only [selStmts]
    refine mem_vals_match.mpr (Or.inr ⟨e, by simp [length_selArms]; simpa using he, ?_⟩)
    cases e with
    | zero => simpa using hv
    | succ e =>
      have he' : e < as.length := by simpa using he
      simp only [List.getElem_cons_succ]
      rw [getElem_selArms g.1 g.2.1 1 as e he' (by omega) (by omega)]
      simpa using hv
  have hatoms : ∀ g ∈ gs, ∀ e (he : e < (a0 :: as).length), (e = 0 ∨ (g.1 ≤ e ∧ e < g.2.1)) →
      (a0 :: as)[e].all isAtomS = true := by
    intro g hg e he hse
    have hm := (hG g hg).2.1.1
    simp only [matchAtoms, Bool.and_eq_true, List.all_eq_true] at hm
    cases e with
    | zero => simpa using List.all_eq_true.mpr hm.1
    | succ e =>
      have he' : e < as.length := by simpa using he
      have := hm.2 _ (List.getElem_mem (l := selArms g.1 g.2.1 1 as) (n := e)
        (by rw [length_selArms]; exact he'))
      rw [getElem_selArms g.1 g.2.1 1 as e he' (by omega) (by omega)] at this
      simpa using List.all_eq_true.mpr this
  -- the state after the selector, the same in every group
  have hst0 : (snapAt (snapsOf j) k).st.pend = [] := rfl
  have hx : ∀ g ∈ gs, x ∈ Memory.Stmt.usesList (selStmts g.1 g.2.1 [Stmt.match_ x (a0 :: as)]) ++
      Memory.Stmt.tmpsList (selStmts g.1 g.2.1 [Stmt.match_ x (a0 :: as)]) := fun g _ ↦ by
    simp only [selStmts]
    exact mem_vals_match.mpr (Or.inl rfl)
  have hn : ∀ g ∈ gs, nameStep (locG (certOf j) (winW (snapsOf j) k) g.2.2.1 g.2.2.2.1 g.2.2.2.2.1
      g.2.2.2.2.2) (bitsOf (plumbOf j).sh) (snapAt (snapsOf j) k).st [x] =
      nameStep (locW (certOf j) (winW (snapsOf j) k)) (bitsOf (plumbOf j).sh) (snapAt (snapsOf j) k).st [x] :=
    fun g hg ↦ nameStep_congr (hag g hg) _ _ [x] (by intro p hp; rw [hst0] at hp; simp at hp)
      (fun v hv ↦ by rw [List.mem_singleton.mp hv]; exact hval g hg x (hx g hg))
  -- every arm's walk
  have harm : ∀ e (he : e < (a0 :: as).length), ∃ b, swL (locW (certOf j) (winW (snapsOf j) k))
      (bitsOf (plumbOf j).sh) (byCell (plumbOf j).tmps) (plumbOf j)
      (nameStep (locW (certOf j) (winW (snapsOf j) k)) (bitsOf (plumbOf j).sh) (snapAt (snapsOf j) k).st [x])
      (a0 :: as)[e] = some b ∧ armRef b (snapAt (snapsOf j) (k + 1)) = true := by
    intro e he
    obtain ⟨g, hg, hse⟩ : ∃ g ∈ gs, e = 0 ∨ (g.1 ≤ e ∧ e < g.2.1) := by
      cases e with
      | zero => exact ⟨g0, hg0, Or.inl rfl⟩
      | succ e =>
        obtain ⟨g, hg, h1, h2⟩ := hcov' e (by simpa using he)
        exact ⟨g, hg, Or.inr ⟨h1, h2⟩⟩
    have hr := (hG g hg).2.2.2
    rw [hn g hg] at hr
    obtain ⟨b, hb, hrb⟩ := armsRef_get hr e he (by omega)
    refine ⟨b, ?_, hrb⟩
    rw [← hb]
    have hpe : ((nameStep (locW (certOf j) (winW (snapsOf j) k)) (bitsOf (plumbOf j).sh)
        (snapAt (snapsOf j) k).st [x]).pend) = [] := by
      have := (hG g hg).2.2.1.1
      rw [hn g hg, List.isEmpty_iff] at this
      exact this
    exact (swL_atoms_congr (hag g hg) _ _ _ _ _ (hatoms g hg e he hse)
      (fun v hv ↦ hval g hg v (hsel g hg e he hse v hv))
      (by intro p hp; rw [hpe] at hp; simp at hp)).symm
  obtain ⟨bs, hbs, hlen, hbs'⟩ := swArms_some _ harm
  have hpre : refinesPre (nameStep (locW (certOf j) (winW (snapsOf j) k)) (bitsOf (plumbOf j).sh)
      (snapAt (snapsOf j) k).st [x]) (snapAt (snapsOf j) (k + 1)) = true := by
    have := (hG g0 hg0).2.2.1.2
    rwa [hn g0 hg0] at this
  have hpe : (nameStep (locW (certOf j) (winW (snapsOf j) k)) (bitsOf (plumbOf j).sh)
      (snapAt (snapsOf j) k).st [x]).pend.isEmpty = true := by
    have := (hG g0 hg0).2.2.1.1
    rwa [hn g0 hg0] at this
  -- the window's check
  unfold shareWin
  simp only [Loc.seq_eq, natSeq_eq, Exec.Trie.seq_eq, Bool.and_eq_true, List.all_eq_true]
  rw [hss]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simp only [shareFits, Bool.and_eq_true, List.all_eq_true] at hf
    exact hf.1.1
  · intro v hv
    rcases mem_vals_match.mp hv with rfl | ⟨e, he, hv⟩
    · rw [← valOk_congr (hag g0 hg0) _ _ _ _ (hval g0 hg0 v (hx g0 hg0))]
      exact (hG g0 hg0).2.1.2 v (hx g0 hg0)
    · obtain ⟨g, hg, hse⟩ : ∃ g ∈ gs, e = 0 ∨ (g.1 ≤ e ∧ e < g.2.1) := by
        cases e with
        | zero => exact ⟨g0, hg0, Or.inl rfl⟩
        | succ e =>
          obtain ⟨g, hg, h1, h2⟩ := hcov' e (by simpa using he)
          exact ⟨g, hg, Or.inr ⟨h1, h2⟩⟩
      have hv' := hsel g hg e he hse v hv
      rw [← valOk_congr (hag g hg) _ _ _ _ (hval g hg v hv')]
      exact (hG g hg).2.1.2 v hv'
  · have hk : (k == 0) = false := by simpa using hk0
    rw [hk, Bool.cond_false]
    simp only [swL, swS, SSt.seq_eq]
    rw [hpe, Bool.cond_true, hbs]
    simp only [joinSt, List.isEmpty_nil, Bool.not_true, Bool.and_false, Bool.cond_false,
      Bool.cond_true, Nat.blt_eq.mpr hkl]
    exact refines_join hpre hbs' (by intro h; rw [h] at hlen; simp at hlen)

end
end LeanVM.Guest.B2C
