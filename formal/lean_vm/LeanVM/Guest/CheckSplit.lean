/-
  LeanVM.Guest.CheckSplit

  A window that is one `match` of straight-line arms, checked by groups of its arms, each group in
  its own kernel evaluation over the cells of its own values.
-/

module

public import LeanVM.Guest.CheckWinC
public import LeanVM.Guest.CheckSound

/-!
# Windows split by arms

`verify_sig_lean_sphincs` dispatches sixteen times on a codeword, each `match` of `256`
straight-line arms (an inlined `sp_forest_key`, about `4,600` instructions and `25,000` values in
all): too much for one kernel evaluation of its window. The window of such a `match` is checked
by groups of its arms (`checkWinS`): group `(lo, hi, rs)` walks the window's one statement with
the arms `lo ≤ k < hi` (and arm `0`, which fixes the join) and the others empty
(`selStmts`), over a trie of the cells of the value ranges `rs` of the window and the values it
names from earlier windows (`Cert.locAtR`), which the group's walk covers (`covOk`). An empty arm
of a straight-line `match` walks its arm's segment to the join with nothing to check, so each
group's walk is the window's with fewer arms.

`winOk_of_split`: groups covering the arms, each passing, give the window's check (`WinOk`). The
group's cells are the window's on every value it covers (`locAtR_agree`: both tries are built from
the certificate's cells, `get_set_eq` reading a trie exactly), so the walk is the window's walk on
the group's arms (`chkL_simple_congr`); the arms' walks of the groups together are the window's
`chkArms` (`chkArms_of_groups`).
-/

namespace LeanVM.Guest.Check

open LeanVM.Parameters LeanVM.Guest LeanVM.Guest.Exec LeanVM.Guest.B2C

@[expose] public section

/-! ## Exact tries -/

theorem get_set_eq {α : Type} (a : α) :
    ∀ (d : ℕ) (t : Exec.Trie α) (n m : ℕ), n + 1 < 2 ^ d →
      (t.set a d n).get m = if m = n then some a else t.get m
  | 0, _, n, _, h => by simp at h
  | d + 1, t, n, m, h => by
    have hp : 2 ^ (d + 1) = 2 * 2 ^ d := by rw [Nat.pow_succ]; ring
    rw [Exec.Trie.set_succ, Exec.Trie.get_eq_node t m]
    by_cases h0 : n = 0
    · subst h0
      simp only [↓reduceIte, Exec.Trie.get_node]
      by_cases hm : m = 0 <;> simp [hm]
    · by_cases h1 : n % 2 = 1
      · simp only [h0, h1, ↓reduceIte, Exec.Trie.get_node]
        by_cases hm : m = 0
        · simp only [hm, ↓reduceIte]
          simp only [Ne.symm h0, ↓reduceIte]
        · by_cases hm1 : m % 2 = 1
          · rw [get_set_eq a d _ _ _ (by omega)]
            by_cases he : m = n
            · subst he; simp [hm, hm1]
            · have : m / 2 ≠ n / 2 := by omega
              simp [hm, hm1, he, this]
          · have : m ≠ n := by omega
            simp [hm, hm1, this]
      · simp only [h0, h1, ↓reduceIte, Exec.Trie.get_node]
        by_cases hm : m = 0
        · simp only [hm, ↓reduceIte]
          simp only [Ne.symm h0, ↓reduceIte]
        · by_cases hm1 : m % 2 = 1
          · have : m ≠ n := by omega
            simp [hm, hm1, this]
          · rw [get_set_eq a d _ _ _ (by omega)]
            by_cases he : m = n
            · subst he; simp [hm, hm1]
            · have : m / 2 - 1 ≠ n / 2 - 1 := by omega
              simp [hm, hm1, he, this]

theorem getF_setF_eq {α : Type} (a : α) {d : ℕ} (t : Exec.Trie α) {n : ℕ} (m : ℕ)
    (h : n + 1 < 2 ^ d) : getF (setF a d t n) m = if m = n then some a else getF t m := by
  rw [getF_eq, setF_eq, get_set_eq a d t n m h, getF_eq]

/-- The cells from value `k` on, read exactly. -/
theorem locTrieFrom_getF : ∀ (cs : List ℕ) (k : ℕ) (t : Exec.Trie ℕ) (x : ℕ),
    k + cs.length < 2 ^ indexDepth →
      getF (locTrieFrom cs k t) x = if k ≤ x ∧ x < k + cs.length then cs[x - k]? else getF t x
  | [], k, t, x, _ => by simp [locTrieFrom]
  | c :: cs, k, t, x, h => by
    simp only [locTrieFrom, natSeq_eq, Exec.Trie.seq_eq]
    rw [locTrieFrom_getF cs (k + 1) _ x (by simp at h; omega),
      getF_setF_eq c t x (by simp at h; omega)]
    simp only [List.length_cons]
    by_cases hx : x = k
    · subst hx; simp
    · by_cases hr : k + 1 ≤ x ∧ x < k + 1 + cs.length
      · have h2 : k ≤ x ∧ x < k + (cs.length + 1) := ⟨by omega, by omega⟩
        simp only [hr, h2, and_self, ↓reduceIte]
        rw [show x - k = (x - (k + 1)) + 1 by omega, List.getElem?_cons_succ]
      · have h2 : ¬ (k ≤ x ∧ x < k + (cs.length + 1)) := by omega
        simp only [hr, h2, hx, ↓reduceIte]

/-- A value not stored by `insTrie` reads as before. -/
theorem insTrie_getF_of_not : ∀ (ps : List (ℕ × ℕ × ℕ)) (t : Exec.Trie ℕ) (x : ℕ),
    (∀ p ∈ ps, p.1 + 1 < 2 ^ indexDepth) → x ∉ ps.map (·.1) →
      getF (insTrie ps t) x = getF t x
  | [], _, _, _, _ => rfl
  | p :: ps, t, x, hf, hx => by
    simp only [insTrie, Exec.Trie.seq_eq]
    simp only [List.map_cons, List.mem_cons, not_or] at hx
    rw [insTrie_getF_of_not ps _ x (fun q hq ↦ hf q (List.mem_cons_of_mem _ hq)) hx.2,
      getF_setF_eq _ t x (hf p List.mem_cons_self)]
    simp [hx.1]

/-- `insTrie` keeps two tries agreeing at `x`, or makes them agree there. -/
theorem insTrie_agree : ∀ (ps : List (ℕ × ℕ × ℕ)) (t t' : Exec.Trie ℕ) (x : ℕ),
    (∀ p ∈ ps, p.1 + 1 < 2 ^ indexDepth) → (getF t x = getF t' x ∨ x ∈ ps.map (·.1)) →
      getF (insTrie ps t) x = getF (insTrie ps t') x
  | [], _, _, _, _, h => by
    rcases h with h | h
    · exact h
    · simp at h
  | p :: ps, t, t', x, hf, h => by
    simp only [insTrie, Exec.Trie.seq_eq]
    have hf' : ∀ q ∈ ps, q.1 + 1 < 2 ^ indexDepth := fun q hq ↦ hf q (List.mem_cons_of_mem _ hq)
    apply insTrie_agree ps _ _ x hf'
    rw [getF_setF_eq _ t x (hf p List.mem_cons_self), getF_setF_eq _ t' x (hf p List.mem_cons_self)]
    by_cases hx : x = p.1
    · left; simp [hx]
    · simp only [hx, ↓reduceIte]
      rcases h with h | h
      · exact Or.inl h
      · simp only [List.map_cons, List.mem_cons] at h
        exact Or.inr (h.resolve_left hx)

/-! ## The cells of value ranges -/

/-- The cells of the values `lo + m` to `lo + m + n` for each range `(m, n)` of `cells`. -/
noncomputable def rangesTrie (cells : List ℕ) (lo : ℕ) (rs : List (ℕ × ℕ)) : Exec.Trie ℕ :=
  rs.foldl (fun (t : Exec.Trie ℕ) r ↦ t.seq fun t ↦
    locTrieFrom ((cells.drop r.1).take r.2) (lo + r.1) t) .nil

theorem rangesTrie_getF_aux (cells : List ℕ) (lo : ℕ) (hlo : lo + cells.length < 2 ^ indexDepth) :
    ∀ (rs : List (ℕ × ℕ)) (t : Exec.Trie ℕ) (x : ℕ), (∀ r ∈ rs, lo + r.1 + r.2 < 2 ^ indexDepth) →
      getF (rs.foldl (fun (t : Exec.Trie ℕ) r ↦
        locTrieFrom ((cells.drop r.1).take r.2) (lo + r.1) t) t) x =
      if ∃ r ∈ rs, lo + r.1 ≤ x ∧ x < lo + r.1 + r.2 ∧ x < lo + cells.length then
        cells[x - lo]? else getF t x
  | [], t, x, _ => by simp
  | r :: rs, t, x, hr1 => by
    simp only [List.foldl_cons]
    rw [rangesTrie_getF_aux cells lo hlo rs _ x (fun q hq ↦ hr1 q (List.mem_cons_of_mem _ hq))]
    have hr0 := hr1 r List.mem_cons_self
    have hlen : lo + r.1 + ((cells.drop r.1).take r.2).length < 2 ^ indexDepth := by
      simp only [List.length_take, List.length_drop]
      have := Nat.min_le_left r.2 (cells.length - r.1)
      omega
    rw [locTrieFrom_getF _ _ t x hlen]
    simp only [List.length_take, List.length_drop, List.mem_cons, exists_eq_or_imp]
    by_cases hs : ∃ r ∈ rs, lo + r.1 ≤ x ∧ x < lo + r.1 + r.2 ∧ x < lo + cells.length
    · simp only [hs, ↓reduceIte, or_true]
    · simp only [hs, ↓reduceIte, or_false]
      by_cases hr : lo + r.1 ≤ x ∧ x < lo + r.1 + min r.2 (cells.length - r.1)
      · have h2 : lo + r.1 ≤ x ∧ x < lo + r.1 + r.2 ∧ x < lo + cells.length :=
          ⟨hr.1, by omega, by omega⟩
        simp only [hr, h2, and_self, ↓reduceIte]
        have hlt : x - (lo + r.1) < r.2 := by omega
        rw [List.getElem?_take]
        simp only [hlt, ↓reduceIte]
        rw [List.getElem?_drop, show r.1 + (x - (lo + r.1)) = x - lo by omega]
      · have h2 : ¬ (lo + r.1 ≤ x ∧ x < lo + r.1 + r.2 ∧ x < lo + cells.length) := by omega
        simp only [hr, h2, ↓reduceIte]

/-- Window `i`'s cells of the value ranges `rs`, and those its statements name outside it. -/
noncomputable def Cert.locAtR (C : Cert) (i : ℕ) (rs : List (ℕ × ℕ)) : Exec.Trie ℕ :=
  (rangesTrie (listElementOrDefault C.cells i []) (listElementOrDefault C.los i 0) rs).seq fun t ↦
      insTrie (listElementOrDefault C.ins i []) t

/-- The window's values and those it names outside it are within the tries' depth. -/
def Cert.winFits (C : Cert) (i : ℕ) : Bool :=
  Nat.blt (listElementOrDefault C.los i 0 + (listElementOrDefault C.cells i []).length) (2 ^ 19) &&
    (listElementOrDefault C.ins i []).all (fun p ↦ Nat.blt p.1 (2 ^ 19))

/-- The value ranges `rs` of window `i` are within the tries' depth. -/
def Cert.rsFit (C : Cert) (i : ℕ) (rs : List (ℕ × ℕ)) : Bool :=
  rs.all fun r ↦ Nat.blt (listElementOrDefault C.los i 0 + r.1 + r.2) (2 ^ 19)

/-- **A group's cells are the window's** at every value it has a cell for. -/
theorem locAtR_agree {C : Cert} {i : ℕ} {rs : List (ℕ × ℕ)} (hfit : C.winFits i = true)
    (hrs : C.rsFit i rs = true) {x : ℕ}
    (hx : (getF (C.locAtR i rs) x).isSome = true) : getF (C.locAtR i rs) x = getF (C.locAt i) x := by
  simp only [Cert.winFits, Bool.and_eq_true, Nat.blt_eq, List.all_eq_true] at hfit
  simp only [Cert.rsFit, Nat.blt_eq, List.all_eq_true] at hrs
  have hd : (2 : ℕ) ^ indexDepth = 2 * 2 ^ 19 := by simp [indexDepth]
  have hlo : listElementOrDefault C.los i 0 + (listElementOrDefault C.cells i []).length < 2 ^
      indexDepth := by omega
  have hins : ∀ p ∈ listElementOrDefault C.ins i [], p.1 + 1 < 2 ^ indexDepth := fun p hp ↦ by
    have := hfit.2 p hp; omega
  unfold Cert.locAtR at hx ⊢
  unfold Cert.locAt
  rw [Exec.Trie.seq_eq] at hx ⊢
  rw [Exec.Trie.seq_eq]
  apply insTrie_agree _ _ _ x hins
  by_cases hk : x ∈ (listElementOrDefault C.ins i []).map (·.1)
  · exact Or.inr hk
  · left
    rw [insTrie_getF_of_not _ _ x hins hk] at hx
    unfold rangesTrie at hx ⊢
    simp only [Exec.Trie.seq_eq] at hx ⊢
    rw [rangesTrie_getF_aux _ _ hlo _ _ _ (fun r hr ↦ by have := hrs r hr; omega)] at hx ⊢
    rw [locTrieFrom_getF _ _ _ x hlo]
    split_ifs at hx ⊢ with h1 h2
    · rfl
    · obtain ⟨r, -, h3, -, h4⟩ := h1
      exact absurd ⟨by omega, h4⟩ h2
    · simp [getF_eq] at hx
    · simp [getF_eq] at hx

/-! ## Walks on agreeing cells -/

/-- Two tries of cells agree on a value. -/
def Agree (l l' : Exec.Trie ℕ) (v : Core.V) : Prop := getF l v.idx = getF l' v.idx

theorem all_congr' {α : Type} {p q : α → Bool} : ∀ {l : List α}, (∀ a ∈ l, p a = q a) →
    l.all p = l.all q
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.all_cons, h a List.mem_cons_self,
      all_congr' (fun b hb ↦ h b (List.mem_cons_of_mem _ hb))]

section Congr

variable {l l' : Exec.Trie ℕ}

theorem cellOf_congr {v : Core.V} (h : Agree l l' v) : cellOf l v = cellOf l' v := by
  unfold cellOf; rw [h]

theorem cellsOf_congr {vs : List Core.V} (h : ∀ v ∈ vs, Agree l l' v) : cellsOf l vs = cellsOf l' vs :=
  List.map_congr_left fun v hv ↦ cellOf_congr (h v hv)

theorem runAt_congr : ∀ (base : ℕ) (vs : List Core.V), (∀ v ∈ vs, Agree l l' v) →
    runAt l base vs = runAt l' base vs
  | _, [], _ => rfl
  | base, v :: vs, h => by
    simp only [runAt, cellOf_congr (h v List.mem_cons_self),
      runAt_congr (base + 1) vs (fun w hw ↦ h w (List.mem_cons_of_mem _ hw))]

theorem atomOk_congr (F : Exec.Facts) (B : Book) (ψ : Exec.Trie Sym) {a : Core.Atom}
    (h : ∀ v ∈ atomVals a, Agree l l' v) : atomOk F B ψ l a = atomOk F B ψ l' a := by
  cases a <;> simp only [atomVals, List.mem_cons, List.mem_append, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at h <;> simp only [atomOk]
  all_goals first
    | (rw [cellOf_congr h])
    | (rw [cellOf_congr h.1, cellOf_congr h.2])
    | (rw [cellOf_congr h.1, cellOf_congr h.2.1, cellOf_congr h.2.2])
    | (rw [cellOf_congr h.1, cellOf_congr h.2.1, cellOf_congr h.2.2.1, cellOf_congr h.2.2.2.1,
        cellOf_congr h.2.2.2.2])
    | (rw [cellsOf_congr fun v hv ↦ h v (Or.inl hv), cellsOf_congr fun v hv ↦ h v (Or.inr hv)])
    | (unfold addrOk; rw [cellOf_congr h.1]; congr 1; funext x; split <;> try rfl
       split <;> try rfl
       rw [runAt_congr _ _ h.2])

end Congr

/-- An atom statement. -/
def isAtomS : Core.Stmt → Bool
  | .atom _ => true
  | _ => false

section Walk

variable (X : Fx) (l' : Exec.Trie ℕ)

theorem pendOk_congr (P : List Core.Atom) (hP : ∀ a ∈ P, ∀ v ∈ atomVals a, Agree X.loc l' v)
    (se : CS) : pendOk X se P = pendOk { X with loc := l' } se P := by
  unfold pendOk
  rw [all_congr' fun a ha ↦ atomOk_congr X.F se.book se.psi (hP a ha)]

theorem blockEnd_congr (st : CS) (P : List Core.Atom)
    (hP : ∀ a ∈ P, ∀ v ∈ atomVals a, Agree X.loc l' v) :
    blockEnd X st P = blockEnd { X with loc := l' } st P := by
  unfold blockEnd chainEnd chainOk
  simp only [pendOk_congr X l' P hP]
  rfl

/-- **The walk of atoms on agreeing cells**: the same. -/
theorem chkL_atoms_congr : ∀ (ss : List Core.Stmt) (st : CS) (P : List Core.Atom),
    ss.all isAtomS = true → (∀ v ∈ stmtsVals ss, Agree X.loc l' v) →
    (∀ a ∈ P, ∀ v ∈ atomVals a, Agree X.loc l' v) →
      chkL X ss st P = chkL { X with loc := l' } ss st P
  | [], st, P, _, _, hP => by
    rw [chkL_nil, chkL_nil]
    exact blockEnd_congr X l' st P hP
  | .atom a :: ss, st, P, hs, hv, hP => by
    simp only [List.all_cons, isAtomS, Bool.true_and] at hs
    have ha : ∀ v ∈ atomVals a, Agree X.loc l' v := fun v hv' ↦
      hv v (by simp only [stmtsVals, stmtVals, List.mem_append]; exact Or.inl hv')
    have hss : ∀ v ∈ stmtsVals ss, Agree X.loc l' v := fun v hv' ↦
      hv v (by simp only [stmtsVals, List.mem_append]; exact Or.inr hv')
    rw [chkL_atom, chkL_atom]
    have hf : (fun B ↦ atomOk X.F B st.psi X.loc a) =
        (fun B ↦ atomOk ({ X with loc := l' } : Fx).F B st.psi ({ X with loc := l' } : Fx).loc a) :=
      funext fun B ↦ atomOk_congr X.F B st.psi ha
    rw [← hf]
    split
    · exact chkL_atoms_congr ss _ P hs hss hP
    · refine chkL_atoms_congr ss _ (a :: P) hs hss ?_
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact ha
      · exact hP b hb
  | .ite .. :: _, _, _, hs, _, _ => by simp [isAtomS] at hs
  | .match_ .. :: _, _, _, hs, _, _ => by simp [isAtomS] at hs
  | .call .. :: _, _, _, hs, _, _ => by simp [isAtomS] at hs
  | .callIf .. :: _, _, _, hs, _, _ => by simp [isAtomS] at hs
  | .dispatch .. :: _, _, _, hs, _, _ => by simp [isAtomS] at hs
  | .ret .. :: _, _, _, hs, _, _ => by simp [isAtomS] at hs

/-- A `match`'s walk from its parts. -/
theorem chkL_match_of {X : Fx} {v : Core.V} {a0 : List Core.Stmt} {as : List (List Core.Stmt)}
    {ss : List Core.Stmt} {st : CS} {P : List Core.Atom} {se : CS} {t : ℕ} {ft : Tgt} {t0 : ℕ}
    {ts : List ℕ} {base : ℕ} {s0 : CS} {J : ℕ} {sj : CS} (h1 : endAt st = some se)
    (h2 : se.seg.exit.kind = .jump (.cell t) ft) (h3 : se.seg.exit.succ = t0 :: ts)
    (h4 : X.F.self ft = true) (h5 : ts.length = as.length)
    (h6 : boundOk X.F se.psi X.mem se.book se.bnd (cellOf X.loc v) (as.length + 1) = true)
    (h7 : tableBase se.book t (cellOf X.loc v) = some base)
    (h8 : armsOk X.G X.entry base 0 (t0 :: ts) = true) (h9 : segAt X t0 se.book se.bnd = some s0)
    (h10 : chkL X a0 s0 [] = .join J) (h11 : chkArms X (.join J) as ts se.book se.bnd = true)
    (h12 : segAt X J se.book se.bnd = some sj) :
    chkL X (.match_ v (a0 :: as) :: ss) st P = chkL X ss sj P := by
  simp only [chkL, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, beq_self_eq_true,
    Bool.and_self, Bool.cond_true]

end Walk

/-! ## Groups of arms -/

/-- The arms `lo ≤ k < hi` of a `match` (arm `k` the `k`-th of the list from index `k`), the
others empty. -/
def selArms (lo hi : ℕ) : ℕ → List (List Core.Stmt) → List (List Core.Stmt)
  | _, [] => []
  | k, a :: as => (bif Nat.ble lo k && Nat.blt k hi then a else []) :: selArms lo hi (k + 1) as

/-- A window of one `match`, with the arms `lo ≤ k < hi` (arm `0` always). -/
def selStmts (lo hi : ℕ) : List Core.Stmt → List Core.Stmt
  | [.match_ v (a0 :: as)] => [.match_ v (a0 :: selArms lo hi 1 as)]
  | ss => ss

/-- A window of one `match` whose arm `0` and arms `lo ≤ k < hi` are atoms. -/
def matchAtoms (lo hi : ℕ) : List Core.Stmt → Bool
  | [.match_ _ (a0 :: as)] => a0.all isAtomS && (selArms lo hi 1 as).all (·.all isAtomS)
  | _ => false

/-- Every arm but `0` of a window of one `match` is in one of the groups `(lo, hi)`. -/
def coverOk (gs : List (ℕ × ℕ)) : List Core.Stmt → Bool
  | [.match_ _ (_ :: as)] =>
      (List.range as.length).all fun e ↦ gs.any fun g ↦ Nat.ble g.1 (e + 1) && Nat.blt (e + 1) g.2
  | _ => false

theorem length_selArms (lo hi : ℕ) : ∀ (k : ℕ) (as : List (List Core.Stmt)),
    (selArms lo hi k as).length = as.length
  | _, [] => rfl
  | k, _ :: as => by simp [selArms, length_selArms lo hi (k + 1) as]

theorem getElem_selArms (lo hi : ℕ) : ∀ (k : ℕ) (as : List (List Core.Stmt)) (e : ℕ)
    (he : e < as.length), lo ≤ k + e → k + e < hi →
      (selArms lo hi k as)[e]'(by rw [length_selArms]; exact he) = as[e]
  | _, [], _, he, _, _ => absurd he (Nat.not_lt_zero _)
  | k, a :: as, 0, _, h1, h2 => by
    have hc : (Nat.ble lo k && Nat.blt k hi) = true := by
      simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq]; omega
    simp only [selArms, List.getElem_cons_zero, hc, Bool.cond_true]
  | k, a :: as, e + 1, he, h1, h2 => by
    simp only [selArms, List.getElem_cons_succ]
    exact getElem_selArms lo hi (k + 1) as e (by simpa using he) (by omega) (by omega)

/-- `chkArms` from each arm's walk. -/
theorem chkArms_of {X : Fx} {r : Res} {B : Book} {bnd : List (ℕ × ℕ)} :
    ∀ {as : List (List Core.Stmt)} {ts : List ℕ}, ts.length = as.length →
      (∀ e (he : e < as.length) (ht : e < ts.length), ∃ st, segAt X ts[e] B bnd = some st ∧
        chkL X as[e] st [] = r) → chkArms X r as ts B bnd = true
  | [], [], _, _ => by simp [chkArms]
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: as, t :: ts, hl, h => by
    simp only [chkArms, Bool.and_eq_true]
    refine ⟨?_, chkArms_of (by simpa using hl) fun e he ht ↦ ?_⟩
    · obtain ⟨st, hst, hw⟩ := h 0 (by simp) (by simp)
      simp only [List.getElem_cons_zero] at hst hw
      rw [hst]
      simp only [hw]
      exact beq_self_eq_true _
    · obtain ⟨st, hst, hw⟩ := h (e + 1) (by simpa using he) (by simpa using ht)
      exact ⟨st, by simpa using hst, by simpa using hw⟩

/-- The arms `lo ≤ k < hi` of a `match` (arm `k` the `k`-th of the list from index `k`), each
from its offset to the join `J`; the others are not walked. -/
noncomputable def chkArmsS (X : Fx) (J lo hi : ℕ) :
    ℕ → List (List Core.Stmt) → List ℕ → Book → List (ℕ × ℕ) → Bool
  | _, [], [], _, _ => true
  | k, a :: as, t :: ts, B, bnd =>
      (bif Nat.ble lo k && Nat.blt k hi then
        (match segAt X t B bnd with
          | some st => chkL X a st [] == Res.join J
          | none => false)
      else true) && chkArmsS X J lo hi (k + 1) as ts B bnd
  | _, _, _, _, _ => false

theorem chkArmsS_get {X : Fx} {J lo hi : ℕ} {B : Book} {bnd : List (ℕ × ℕ)} :
    ∀ {k : ℕ} {as : List (List Core.Stmt)} {ts : List ℕ}, chkArmsS X J lo hi k as ts B bnd = true →
      ts.length = as.length ∧ ∀ e (he : e < as.length) (ht : e < ts.length), lo ≤ k + e → k + e < hi →
        ∃ st, segAt X ts[e] B bnd = some st ∧ chkL X as[e] st [] = .join J
  | _, [], [], _ => ⟨rfl, fun _ he ↦ absurd he (Nat.not_lt_zero _)⟩
  | k, a :: as, t :: ts, h => by
    simp only [chkArmsS, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨hl, ih⟩ := chkArmsS_get h2
    refine ⟨by simp [hl], fun e he ht hlo hhi ↦ ?_⟩
    cases e with
    | zero =>
      have hc : (Nat.ble lo k && Nat.blt k hi) = true := by
        simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq]; omega
      rw [hc, Bool.cond_true] at h1
      split at h1
      · rename_i st hst
        exact ⟨st, hst, by simpa using h1⟩
      · simp at h1
    | succ e => exact ih e (by simpa using he) (by simpa using ht) (by omega) (by omega)
  | _, [], _ :: _, h => by simp [chkArmsS] at h
  | _, _ :: _, [], h => by simp [chkArmsS] at h

/-- **A `match`'s walk with the arms `lo ≤ k < hi` (and arm `0`)**: `chkL`'s on a window of one
`match`, its arms by `chkArmsS`. -/
noncomputable def chkMatchS (X : Fx) (lo hi : ℕ) (v : Core.V) (arms : List (List Core.Stmt))
    (st : CS) : Res :=
  match endAt st with
  | some se => match se.seg.exit.kind, se.seg.exit.succ, arms with
    | .jump (.cell t) ft, t0 :: ts, a0 :: as =>
        bif X.F.self ft && ts.length == as.length &&
            boundOk X.F se.psi X.mem se.book se.bnd (cellOf X.loc v) (as.length + 1) then
          match tableBase se.book t (cellOf X.loc v) with
          | some base =>
              bif armsOk X.G X.entry base 0 (t0 :: ts) then
                match segAt X t0 se.book se.bnd with
                | some s0 => match chkL X a0 s0 [] with
                  | .join J =>
                      bif chkArmsS X J lo hi 1 as ts se.book se.bnd then
                        match segAt X J se.book se.bnd with
                        | some sj => chkL X [] sj []
                        | none => .fail
                      else .fail
                  | _ => .fail
                | none => .fail
              else .fail
          | none => .fail
        else .fail
    | _, _, _ => .fail
  | none => .fail

theorem chkMatchS_dec {X : Fx} {lo hi : ℕ} {v : Core.V} {arms : List (List Core.Stmt)} {st : CS}
    (h : chkMatchS X lo hi v arms st ≠ .fail) :
    ∃ se t ft t0 ts a0 as base s0 J sj, endAt st = some se ∧
      se.seg.exit.kind = .jump (.cell t) ft ∧ se.seg.exit.succ = t0 :: ts ∧ arms = a0 :: as ∧
      X.F.self ft = true ∧ ts.length = as.length ∧
      boundOk X.F se.psi X.mem se.book se.bnd (cellOf X.loc v) (as.length + 1) = true ∧
      tableBase se.book t (cellOf X.loc v) = some base ∧
      armsOk X.G X.entry base 0 (t0 :: ts) = true ∧ segAt X t0 se.book se.bnd = some s0 ∧
      chkL X a0 s0 [] = .join J ∧ chkArmsS X J lo hi 1 as ts se.book se.bnd = true ∧
      segAt X J se.book se.bnd = some sj ∧ chkMatchS X lo hi v arms st = chkL X [] sj [] := by
  revert h
  simp only [chkMatchS]
  split
  · rename_i se hse
    split
    · rename_i t ft t0 ts a0 as hk hs
      simp only [Bool.cond_eq_ite, Bool.and_eq_true, beq_iff_eq]
      split_ifs with hc
      · split
        · rename_i base hb
          split_ifs with ha
          · split
            · rename_i s0 hs0
              split
              · rename_i J hJ
                split_ifs with harms
                · split
                  · rename_i sj hsj
                    intro _
                    exact ⟨se, t, ft, t0, ts, a0, as, base, s0, J, sj, hse, hk, hs, rfl, hc.1.1,
                      hc.1.2, hc.2, hb, ha, hs0, hJ, harms, hsj, rfl⟩
                  · simp
                · simp
              · simp
            · simp
          · simp
        · simp
      · simp
    · simp
  · simp

/-- **A `match` window's walk from its groups'**: groups `(lo, hi, cells)` covering every arm,
whose walks of arm `0` and their arms on their cells do not fail, the cells agreeing with the
window's on the values they name, give the walk of the whole `match`: any group's. -/
theorem chkL_of_groups (X : Fx) (v : Core.V) (a0 : List Core.Stmt) (as : List (List Core.Stmt))
    (st : CS) (gs : List (ℕ × ℕ × Exec.Trie ℕ)) (g0 : ℕ × ℕ × Exec.Trie ℕ) (hg0 : g0 ∈ gs)
    (hcov : ∀ e < as.length, ∃ g ∈ gs, g.1 ≤ e + 1 ∧ e + 1 < g.2.1)
    (ha0 : a0.all isAtomS = true)
    (has : ∀ g ∈ gs, ∀ e (he : e < as.length), g.1 ≤ e + 1 → e + 1 < g.2.1 →
      as[e].all isAtomS = true)
    (hv : ∀ g ∈ gs, Agree g.2.2 X.loc v) (h0v : ∀ g ∈ gs, ∀ x ∈ stmtsVals a0, Agree g.2.2 X.loc x)
    (hav : ∀ g ∈ gs, ∀ e (he : e < as.length), g.1 ≤ e + 1 → e + 1 < g.2.1 →
      ∀ x ∈ stmtsVals as[e], Agree g.2.2 X.loc x)
    (h : ∀ g ∈ gs, chkMatchS { X with loc := g.2.2 } g.1 g.2.1 v (a0 :: as) st ≠ .fail) :
    chkL X [.match_ v (a0 :: as)] st [] = chkMatchS { X with loc := g0.2.2 } g0.1 g0.2.1 v (a0 :: as) st := by
  -- a group's walk of atoms is the window's
  have hw : ∀ g ∈ gs, ∀ (a : List Core.Stmt) (s : CS), a.all isAtomS = true →
      (∀ x ∈ stmtsVals a, Agree g.2.2 X.loc x) →
      chkL { X with loc := g.2.2 } a s [] = chkL X a s [] := fun g _ a s ha hx ↦
    chkL_atoms_congr { X with loc := g.2.2 } X.loc a s [] ha hx (by simp)
  obtain ⟨se, t, ft, t0, ts, a0', as', base, s0, J, sj, h1, h2, h3, harms, h4, h5, h6, h7, h8, h9,
    h10, -, h12, heq⟩ := chkMatchS_dec (h g0 hg0)
  obtain ⟨rfl, rfl⟩ := List.cons.inj harms
  rw [heq, hw g0 hg0 [] sj rfl (by simp [stmtsVals])]
  have h10' : chkL X a0 s0 [] = .join J := by rw [← hw g0 hg0 a0 s0 ha0 (h0v g0 hg0)]; exact h10
  -- every arm's walk, from the group holding it
  have harm : ∀ e (he : e < as.length) (ht : e < ts.length), ∃ st,
      segAt X ts[e] se.book se.bnd = some st ∧ chkL X as[e] st [] = .join J := by
    intro e he ht
    obtain ⟨g, hg, hlo, hhi⟩ := hcov e he
    obtain ⟨se', t', ft', t0', ts', a0'', as'', base', s0', J', sj', h1', h2', h3', harms', -, -, -,
      -, -, h9', h10'', h11', -, -⟩ := chkMatchS_dec (h g hg)
    obtain ⟨rfl, rfl⟩ := List.cons.inj harms'
    have hse : se' = se := Option.some.inj (h1'.symm.trans h1)
    rw [hse, h3] at h3'
    rw [hse] at h9' h11'
    have hts : ts' = ts := (List.cons.inj h3').2.symm
    have ht0 : t0' = t0 := (List.cons.inj h3').1.symm
    rw [hts] at h11'
    rw [ht0] at h9'
    have h9g : segAt X t0 se.book se.bnd = some s0' := h9'
    have hs0 : s0' = s0 := Option.some.inj (h9g.symm.trans h9)
    rw [hs0] at h10''
    have hJ : J' = J := by
      have := (hw g hg a0 s0 ha0 (h0v g hg)).symm.trans h10''
      rw [h10'] at this
      injection this.symm
    rw [hJ] at h11'
    obtain ⟨-, hg'⟩ := chkArmsS_get h11'
    obtain ⟨st', hst', hw'⟩ := hg' e he ht (by omega) (by omega)
    exact ⟨st', hst', by rw [← hw g hg _ st' (has g hg e he hlo hhi) (hav g hg e he hlo hhi)]; exact hw'⟩
  have hlen : ts.length = as.length := h5
  exact chkL_match_of h1 h2 h3 h4 hlen (by rw [← cellOf_congr (hv g0 hg0)]; exact h6)
    (by rw [← cellOf_congr (hv g0 hg0)]; exact h7) h8 h9 h10' (chkArms_of hlen harm) h12

/-! ## A window by groups -/

/-- What a window of one `match` checks once, its groups not: its cells consecutive and within the
tries' depth, those it names outside it the certificate's. -/
def checkWinP (C : Cert) (i : ℕ) : Bool :=
  C.contOk i && C.insOk (listElementOrDefault C.ins i []) && C.winFits i

/-- The walk of a window of one `match` with the arms `lo ≤ k < hi`. -/
noncomputable def chkWinS (X : Fx) (lo hi : ℕ) : List Core.Stmt → CS → Res
  | [.match_ v arms], st => chkMatchS X lo hi v arms st
  | _, _ => .fail

/-- **The check of a group of a window of one `match`**: arm `0` and the arms `lo ≤ k < hi` of the
window's `match` (`selStmts`), atoms all, walked over the cells of the value ranges `rs` of the
window and of the values it names outside it (`Cert.locAtR`), which cover the group's statements;
the executor, the links and the window's start and end as `checkWinC`'s. Not the first window. -/
noncomputable def checkWinS (G : Glob) (j : ℕ) (cf : Core.Fn) (C : Cert) (main : Bool) (i lo hi : ℕ)
    (rs : List (ℕ × ℕ)) : Bool :=
  matchAtoms lo hi (C.stmtsAt cf i) && (C.succAt i).isEmpty &&
  match execWinC C.facts (fnOf j) (C.cutAt i).J (C.cutAt i).env (C.endAt (fnOf j) i) with
  | ⟨segs, _⟩ => listSeq segs fun segs ↦ (index segs).seq fun idx ↦ (C.locAtR i rs).seq fun loc ↦
      !(i == 0) && C.rsFit i rs &&
      covOk loc (selStmts lo hi (C.stmtsAt cf i)) &&
      linkedWeak idx segs (C.fxAt G (fnOf j) cf main i segs idx loc).wJ
        (C.fxAt G (fnOf j) cf main i segs idx loc).wenv &&
      (match segAt (C.fxAt G (fnOf j) cf main i segs idx loc) (C.cutAt i).J
          (bookOf (C.cutAt i).facts .nil) (C.cutAt i).bnd with
        | some st => st.seg.env.sub Sym.beq (envOf (C.cutAt i).env) &&
            winEnd C i idx (chkWinS (C.fxAt G (fnOf j) cf main i segs idx loc) lo hi
              (C.stmtsAt cf i) st)
        | none => false)

theorem winEnd_fail (C : Cert) (i : ℕ) (idx : Exec.Trie Exec.Seg) : winEnd C i idx .fail = false := by
  unfold winEnd
  cases Nat.blt i C.cuts.length <;> simp

theorem mem_armsVals {x : Core.V} : ∀ {as : List (List Core.Stmt)}, x ∈ armsVals as →
    ∃ e, ∃ he : e < as.length, x ∈ stmtsVals as[e]
  | [], h => by simp [armsVals] at h
  | a :: as, h => by
    simp only [armsVals, List.mem_append] at h
    rcases h with h | h
    · exact ⟨0, by simp, by simpa using h⟩
    · obtain ⟨e, he, hx⟩ := mem_armsVals h
      exact ⟨e + 1, by simpa using he, by simpa using hx⟩

theorem mem_armsVals_of {x : Core.V} : ∀ {as : List (List Core.Stmt)} {e : ℕ} (he : e < as.length),
    x ∈ stmtsVals as[e] → x ∈ armsVals as
  | [], _, he, _ => absurd he (Nat.not_lt_zero _)
  | _ :: _, 0, _, h => by simp only [armsVals, List.mem_append]; exact Or.inl (by simpa using h)
  | _ :: as, e + 1, he, h => by
    simp only [armsVals, List.mem_append]
    exact Or.inr (mem_armsVals_of (as := as) (by simpa using he) (by simpa using h))

/-- **A window of one `match` from its groups**: groups covering every arm, each passing
`checkWinS`, give the window's `checkWinC`. -/
theorem checkWinC_of_split {G : Glob} {j : ℕ} {cf : Core.Fn} {C : Cert} {main : Bool} {i : ℕ}
    (gs : List (ℕ × ℕ × List (ℕ × ℕ))) (g0 : ℕ × ℕ × List (ℕ × ℕ)) (hg0 : g0 ∈ gs)
    (hcov : coverOk (gs.map fun g ↦ (g.1, g.2.1)) (C.stmtsAt cf i) = true)
    (hp : checkWinP C i = true) (h : ∀ g ∈ gs, checkWinS G j cf C main i g.1 g.2.1 g.2.2 = true) :
    checkWinC G j cf C main i = true := by
  simp only [checkWinP, Bool.and_eq_true] at hp
  obtain ⟨⟨hcont, hins⟩, hwf⟩ := hp
  -- the window is one `match`
  obtain ⟨v, a0, as, hss⟩ : ∃ v a0 as, C.stmtsAt cf i = [.match_ v (a0 :: as)] := by
    revert hcov
    unfold coverOk
    split
    · rename_i v a0 as heq
      exact fun _ ↦ ⟨v, a0, as, by assumption⟩
    · simp
  have hcov' : ∀ e < as.length, ∃ g ∈ gs, g.1 ≤ e + 1 ∧ e + 1 < g.2.1 := by
    intro e he
    rw [hss] at hcov
    simp only [coverOk, List.all_eq_true, List.mem_range, List.any_eq_true, Bool.and_eq_true,
      Nat.ble_eq, Nat.blt_eq] at hcov
    obtain ⟨g', hg', h1, h2⟩ := hcov e he
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hg'
    exact ⟨g, hg, h1, h2⟩
  have hsucc : C.succAt i = [] := by
    have hc := h g0 hg0
    unfold checkWinS at hc
    simp only [Bool.and_eq_true, List.isEmpty_iff] at hc
    exact hc.1.2
  unfold checkWinC
  rw [hsucc, List.drop_nil, execWinCS_nil]
  rcases hR : execWinC C.facts (fnOf j) (C.cutAt i).J (C.cutAt i).env (C.endAt (fnOf j) i) with
    ⟨segs, dead⟩
  simp only [listSeq_eq, Exec.Trie.seq_eq, Bool.and_eq_true]
  -- each group's facts
  have hG : ∀ g ∈ gs, matchAtoms g.1 g.2.1 [.match_ v (a0 :: as)] = true ∧ i ≠ 0 ∧
      C.rsFit i g.2.2 = true ∧
      covOk (C.locAtR i g.2.2) [.match_ v (a0 :: selArms g.1 g.2.1 1 as)] = true ∧
      linkedWeak (index segs) segs (C.fxAt G (fnOf j) cf main i segs (index segs) (C.locAt i)).wJ
        (C.fxAt G (fnOf j) cf main i segs (index segs) (C.locAt i)).wenv = true ∧
      ∃ st, segAt (C.fxAt G (fnOf j) cf main i segs (index segs) (C.locAt i)) (C.cutAt i).J
          (bookOf (C.cutAt i).facts .nil) (C.cutAt i).bnd = some st ∧
        st.seg.env.sub Sym.beq (envOf (C.cutAt i).env) = true ∧
        winEnd C i (index segs) (chkMatchS (C.fxAt G (fnOf j) cf main i segs (index segs)
          (C.locAtR i g.2.2)) g.1 g.2.1 v (a0 :: as) st) = true := by
    intro g hg
    have hc := h g hg
    unfold checkWinS at hc
    rw [hR, hss] at hc
    simp only [listSeq_eq, Exec.Trie.seq_eq, Bool.and_eq_true, Bool.not_eq_true',
      beq_eq_false_iff_ne, selStmts, chkWinS] at hc
    obtain ⟨⟨hm, -⟩, ⟨⟨⟨⟨hi, hfit⟩, hcovg⟩, hlink⟩, hend⟩⟩ := hc
    refine ⟨hm, hi, hfit, hcovg, hlink, ?_⟩
    split at hend
    · rename_i st hst
      simp only [Bool.and_eq_true] at hend
      exact ⟨st, hst, hend.1, hend.2⟩
    · simp at hend
  obtain ⟨-, hi0, -, -, hlink, st, hst, hsub, hend0⟩ := hG g0 hg0
  -- a group's cells are the window's on its values
  have hagree : ∀ g ∈ gs, ∀ x ∈ stmtsVals [.match_ v (a0 :: selArms g.1 g.2.1 1 as)],
      Agree (C.locAtR i g.2.2) (C.locAt i) x := by
    intro g hg x hx
    obtain ⟨-, -, hrs, hcovg, -⟩ := hG g hg
    exact locAtR_agree hwf hrs (List.all_eq_true.mp hcovg x hx)
  have hsel : ∀ g ∈ gs, ∀ e (he : e < as.length), g.1 ≤ e + 1 → e + 1 < g.2.1 →
      ∀ x ∈ stmtsVals as[e], x ∈ stmtsVals [.match_ v (a0 :: selArms g.1 g.2.1 1 as)] := by
    intro g _ e he hlo hhi x hx
    simp only [stmtsVals, stmtVals, armsVals, List.mem_cons, List.mem_append, List.append_nil]
    refine Or.inr (Or.inr (mem_armsVals_of (as := selArms g.1 g.2.1 1 as) (e := e)
      (by rw [length_selArms]; exact he) ?_))
    rw [getElem_selArms g.1 g.2.1 1 as e he (by omega) (by omega)]
    exact hx
  refine ⟨⟨⟨⟨⟨hcont, hins⟩, ?_⟩, hlink⟩, by simp [hi0]⟩, ?_⟩
  · -- the window's values have cells
    rw [hss]
    unfold covOk
    refine List.all_eq_true.mpr fun x hx ↦ ?_
    have hsome : ∃ g ∈ gs, x ∈ stmtsVals [.match_ v (a0 :: selArms g.1 g.2.1 1 as)] := by
      simp only [stmtsVals, stmtVals, armsVals, List.mem_cons, List.mem_append, List.append_nil]
        at hx ⊢
      rcases hx with hx | hx | hx
      · exact ⟨g0, hg0, Or.inl hx⟩
      · exact ⟨g0, hg0, Or.inr (Or.inl hx)⟩
      · obtain ⟨e, he, hx⟩ := mem_armsVals hx
        obtain ⟨g, hg, hlo, hhi⟩ := hcov' e he
        have := hsel g hg e he hlo hhi x hx
        simp only [stmtsVals, stmtVals, armsVals, List.mem_cons, List.mem_append,
          List.append_nil] at this
        exact ⟨g, hg, this⟩
    obtain ⟨g, hg, hx'⟩ := hsome
    obtain ⟨-, -, hrs, hcovg, -⟩ := hG g hg
    have hs := List.all_eq_true.mp hcovg x hx'
    rw [← locAtR_agree hwf hrs hs]
    exact hs
  · rw [hst]
    simp only [hsub, Bool.true_and]
    rw [walkFrom_nil rfl]
    have hne : ∀ g ∈ gs, chkMatchS (C.fxAt G (fnOf j) cf main i segs (index segs) (C.locAtR i g.2.2))
        g.1 g.2.1 v (a0 :: as) st ≠ .fail := by
      intro g hg hf
      obtain ⟨-, -, -, -, -, st', hst', -, hend⟩ := hG g hg
      obtain rfl := Option.some.inj (hst'.symm.trans hst)
      rw [hf, winEnd_fail] at hend
      exact Bool.false_ne_true hend
    have hatoms : ∀ g ∈ gs, a0.all isAtomS = true ∧ ∀ e (he : e < as.length), g.1 ≤ e + 1 →
        e + 1 < g.2.1 → as[e].all isAtomS = true := by
      intro g hg
      obtain ⟨hm, -⟩ := hG g hg
      simp only [matchAtoms, Bool.and_eq_true, List.all_eq_true] at hm
      refine ⟨List.all_eq_true.mpr hm.1, fun e he hlo hhi ↦ ?_⟩
      have := hm.2 _ (List.getElem_mem (l := selArms g.1 g.2.1 1 as) (n := e)
        (by rw [length_selArms]; exact he))
      rw [getElem_selArms g.1 g.2.1 1 as e he (by omega) (by omega)] at this
      exact List.all_eq_true.mpr this
    rw [hss, chkL_of_groups _ v a0 as st (gs.map fun g ↦ (g.1, g.2.1, C.locAtR i g.2.2))
      (g0.1, g0.2.1, C.locAtR i g0.2.2) (List.mem_map.mpr ⟨g0, hg0, rfl⟩) ?_ (hatoms g0 hg0).1 ?_ ?_ ?_
      ?_ ?_]
    · exact hend0
    · intro e he
      obtain ⟨g, hg, h1, h2⟩ := hcov' e he
      exact ⟨_, List.mem_map.mpr ⟨g, hg, rfl⟩, h1, h2⟩
    · intro g' hg'
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hg'
      exact (hatoms g hg).2
    · intro g' hg'
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hg'
      exact hagree g hg v (by simp [stmtsVals, stmtVals])
    · intro g' hg' x hx
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hg'
      exact hagree g hg x (by
        simp only [stmtsVals, stmtVals, armsVals, List.mem_cons, List.mem_append, List.append_nil]
        exact Or.inr (Or.inl hx))
    · intro g' hg' e he hlo hhi x hx
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hg'
      exact hagree g hg x (hsel g hg e he hlo hhi x hx)
    · intro g' hg'
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hg'
      exact hne g hg

/-- **A window of one `match`, checked by groups** (`checkWinS`) covering its arms. -/
theorem winOk_of_split {j i : ℕ} (gs : List (ℕ × ℕ × List (ℕ × ℕ))) (g0 : ℕ × ℕ × List (ℕ × ℕ))
    (hg0 : g0 ∈ gs) (hcov : coverOk (gs.map fun g ↦ (g.1, g.2.1)) ((certOf j).stmtsAt (coreOf j) i) = true)
    (hp : checkWinP (certOf j) i = true)
    (h : ∀ g ∈ gs, checkWinS glob j (coreOf j) (certOf j) (j == 1) i g.1 g.2.1 g.2.2 = true) :
    WinOk j i :=
  winOk_of_C (checkWinC_of_split gs g0 hg0 hcov hp h)

end
end LeanVM.Guest.Check
