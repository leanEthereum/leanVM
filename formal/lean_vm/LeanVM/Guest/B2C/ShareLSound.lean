/-
  LeanVM.Guest.B2C.ShareLSound

  Soundness of the local sharing check: on every path of a function whose check holds, the
  values the path names at one frame cell hold one word, a fixed cell's constant if it has one.
-/

module

public import LeanVM.Guest.B2C.ShareLAtom

/-!
# Soundness of the local sharing check

Fix a returning path of `walk σ`. A position runs (`Ran`) if it is the parameters' (`0`) or the
path runs it (`Local.RunsL`). The word of a cell (`psi`) is a fixed cell's constant, the value
of a cell holding one value, or the value of a shared cell's first value (by home position)
whose home runs. Every shared value whose home runs holds its cell's word (`shared_eq`), by
induction on its home's place, roots before the other homes of a position: a root is its cell's
first value whose home runs (`root_first`: the values before it in its cell's list, `chain_order`,
are in earlier arms of its branch, which do not run, `Local.runs_arm'`); an `eq`, constant or
key justification ties it to values justified before it, whose homes run as they dominate it
(`cover`, `Local.runs_dom`). Every value a path names occurs at a position that runs
(`Local.walk_names`), so holds its cell's word (`path_of_check`).
-/

namespace LeanVM.Guest.B2C.ShareL

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Local
open LeanVM.Guest.Packed (fld fld_lt)
open LeanVM.Guest.Check LeanVM.Guest.Exec LeanVM.Guest.Memory

@[expose] public section

/-! ## Small facts -/

theorem vn_of_ok {v : V} (h : vnOk v = true) : v = V.n v.idx := by
  unfold vnOk at h
  simp only [band, nbeq_iff] at h
  obtain ⟨h1, h2⟩ := h
  rcases v with ⟨path, tag, idx⟩
  cases path with
  | nil => simp only at h2; subst h2; rfl
  | cons _ _ => cases h1

theorem packCells_inj : ∀ (l l' : List ℕ), (∀ c ∈ l, 1 ≤ c ∧ c < 65536) → (∀ c ∈ l', 1 ≤ c ∧ c < 65536) →
    packCells l = packCells l' → l = l'
  | [], [], _, _, _ => rfl
  | [], c :: cs, _, h', h => by
      have := h' c List.mem_cons_self; simp only [packCells, Nat.add_eq, Nat.mul_eq] at h; omega
  | c :: cs, [], h1, _, h => by
      have := h1 c List.mem_cons_self; simp only [packCells, Nat.add_eq, Nat.mul_eq] at h; omega
  | c :: cs, c' :: cs', h1, h2, h => by
      simp only [packCells, Nat.add_eq, Nat.mul_eq] at h
      have hc := h1 c List.mem_cons_self
      have hc' := h2 c' List.mem_cons_self
      have e1 : c = c' := by omega
      have e2 : packCells cs = packCells cs' := by omega
      rw [e1, packCells_inj cs cs' (fun x hx ↦ h1 x (List.mem_cons_of_mem _ hx))
        (fun x hx ↦ h2 x (List.mem_cons_of_mem _ hx)) e2]

theorem destUses_eq (d : Dest) : destUses d = d.vals := by cases d <;> rfl

theorem hint_sub {hh : Hint} {v : V} (h : v ∈ hintUses hh) : v ∈ hh.vals := by
  cases hh <;> simp only [hintUses, Core.Hint.vals, destUses_eq, List.mem_cons, List.mem_append] at h ⊢ <;> tauto

theorem names_sub {s : Stmt} {v : V} (h : v ∈ names s) : v ∈ ownVals s := by
  cases s with
  | atom a =>
    simp only [names, ownVals, atomVals_eq] at h ⊢
    cases a with
    | hint hh => exact hint_sub h
    | _ => simp only [atomUses, Core.Atom.vals, List.mem_cons, List.mem_append] at h ⊢; tauto
  | _ => simp_all [names, ownVals, appR_eq]

theorem tmps_sub {a : Core.Atom} {v : V} (h : v ∈ atomTmps a) : v ∈ ownVals (.atom a) := by
  simp only [ownVals, atomVals_eq]
  cases a <;> simp only [atomTmps, Core.Atom.vals, List.mem_cons, List.not_mem_nil, or_false] at h ⊢ <;> tauto

theorem mem_getElem? {l : List V} {v : V} (h : v ∈ l) : ∃ i : ℕ, l[i]? = some v := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h
  exact ⟨i, List.getElem?_eq_getElem hi⟩

theorem eqAt_mem {a : Core.Atom} {i : ℕ} {u : V} (h : eqAt a i = some u) : u ∈ atomVals a := by
  rw [atomVals_eq]
  cases a <;> simp only [eqAt, Bool.cond_eq_ite, nbeq_iff] at h <;> (try split_ifs at h) <;>
    (try simp only [Option.some.injEq] at h) <;> (try subst h) <;> simp_all [Core.Atom.vals]

theorem keyAt_mem {a : Core.Atom} {i op : ℕ} {ins : List V} (h : keyAt a i = some (op, ins)) :
    ∀ x ∈ ins, x ∈ atomVals a := by
  rw [atomVals_eq]
  cases a <;> simp only [keyAt, Bool.cond_eq_ite, nbeq_iff] at h <;> (try split_ifs at h) <;>
    (try obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)) <;> simp_all [Core.Atom.vals]

/-! ## The certificate's once-per-function facts -/

theorem locsOk_spec {T : Tabs} : ∀ (locs : List ℕ) (v0 : ℕ),
    List.rec (motive := fun _ ↦ ℕ → Bool) (fun _ ↦ true)
      (fun c _ r v ↦ Nat.beq (vCell (T.vLane v)) c && Local.seqN (v + 1) r) locs v0 = true →
    ∀ k (hk : k < locs.length), vCell (T.vLane (v0 + k)) = locs[k]
  | [], _, _, k, hk => absurd hk (by simp)
  | c :: cs, v0, h, k, hk => by
      change (Nat.beq (vCell (T.vLane v0)) c && Local.seqN (v0 + 1) _) = true at h
      simp only [band, nbeq_iff, seqN_eq] at h
      cases k with
      | zero => simpa using h.1
      | succ k =>
        have := locsOk_spec cs (v0 + 1) h.2 k (by simpa using hk)
        rw [show v0 + (k + 1) = v0 + 1 + k by omega]; simpa using this

/-- `statOk`'s walk from fixed constant `n`. -/
noncomputable def statGo (T : Tabs) (stat : List (ℕ × PC)) : ℕ → Bool :=
  List.rec (motive := fun _ ↦ ℕ → Bool) (fun n ↦ Nat.beq n T.nst)
    (fun q _ r n ↦ match q.2 with
      | .k a b => natSeq (T.tLane n) fun t ↦
          Nat.beq (tO t) q.1 && Nat.beq (tK0 t) a && Nat.beq (tK1 t) b &&
            Nat.beq (Nat.mod (T.oLane q.1) 4) 3 && Local.seqN (n + 1) r
      | .fpg _ => r n) stat

theorem statGo_k (T : Tabs) (o a b : ℕ) (qs : List (ℕ × PC)) (n : ℕ) :
    statGo T ((o, .k a b) :: qs) n = (Nat.beq (tO (T.tLane n)) o && Nat.beq (tK0 (T.tLane n)) a &&
      Nat.beq (tK1 (T.tLane n)) b && Nat.beq (Nat.mod (T.oLane o) 4) 3 && statGo T qs (n + 1)) := by
  simp only [statGo, natSeq_eq, seqN_eq]

theorem statGo_fpg (T : Tabs) (o e : ℕ) (qs : List (ℕ × PC)) (n : ℕ) :
    statGo T ((o, .fpg e) :: qs) n = statGo T qs n := rfl

theorem statOk_spec {T : Tabs} : ∀ (stat : List (ℕ × PC)) (n0 : ℕ), statGo T stat n0 = true →
    (∀ q ∈ stat, ∀ a b, q.2 = .k a b → T.oLane q.1 % 4 = 3) ∧
    ∀ n, n0 ≤ n → n < T.nst → (tO (T.tLane n), PC.k (tK0 (T.tLane n)) (tK1 (T.tLane n))) ∈ stat
  | [], n0, h => by
      change Nat.beq n0 T.nst = true at h
      rw [nbeq_iff] at h
      exact ⟨fun q hq ↦ absurd hq List.not_mem_nil, fun n h1 h2 ↦ by omega⟩
  | (o, pc) :: qs, n0, h => by
      cases pc with
      | k a b =>
        rw [statGo_k] at h
        simp only [band, nbeq_iff] at h
        obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
        obtain ⟨ih1, ih2⟩ := statOk_spec qs (n0 + 1) h5
        refine ⟨fun q hq a' b' hab ↦ ?_, fun n hn1 hn2 ↦ ?_⟩
        · rcases List.mem_cons.mp hq with rfl | hq
          · exact h4
          · exact ih1 q hq a' b' hab
        · by_cases hn : n = n0
          · subst hn; rw [h1, h2, h3]; exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (ih2 n (by omega) hn2)
      | fpg e =>
        rw [statGo_fpg] at h
        obtain ⟨ih1, ih2⟩ := statOk_spec qs n0 h
        refine ⟨fun q hq a' b' hab ↦ ?_, fun n hn1 hn2 ↦ List.mem_cons_of_mem _ (ih2 n hn1 hn2)⟩
        rcases List.mem_cons.mp hq with rfl | hq
        · cases hab
        · exact ih1 q hq a' b' hab

theorem statOk_eq (T : Tabs) (stat : List (ℕ × PC)) : statOk T stat = statGo T stat 0 := rfl


/-! ## Homes -/

section Homes

variable {cf : Core.Fn} {C : Cert} {P : Plumb} {fs : ℕ} {main : Bool} {mc : ℕ} {T : Tabs}

local notation "Kf" => fnK cf C P fs main mc T

/-- A shared value's lane in the shared table. -/
noncomputable def SLv (K : FnK) (u : ℕ) : ℕ := K.T.sLane (vSh (vlane K u) - 1)

/-- A home's place: position, then operand. -/
def keyOf (s : ℕ) : ℕ := sHp s * 256 + sHj s

theorem sHj_lt (s : ℕ) : sHj s < 256 := fld_lt s 34 8

theorem opd_vn (H : CheckL cf C P fs main mc T) {q i : ℕ} {v : V} {st : Stmt} {cx : Ctx}
    (h : Opd cf T q i v st cx) : v = V.n v.idx := by
  obtain ⟨n, n', -, ho⟩ := opd_occ H h
  exact vn_of_ok (occOk_spec _ ho).1

/-- Value `u`'s home. -/
theorem home_at (H : CheckL cf C P fs main mc T) {u : ℕ} (hu : u < C.locs.length) :
    ∃ q i st cx, Opd cf T q i (V.n u) st cx ∧ homeOk Kf st q i cx u (vlane Kf u) = true := by
  obtain ⟨q, i, v, st, cx, ho, rfl, hh⟩ := home_exists H hu
  exact ⟨q, i, st, cx, opd_vn H ho ▸ ho, hh⟩

/-- A shared value's home. -/
theorem shared_home (H : CheckL cf C P fs main mc T) {u : ℕ} (hu : u < C.locs.length)
    (hs : vSh (vlane Kf u) ≠ 0) : ∃ q i st cx, Opd cf T q i (V.n u) st cx ∧ 2 ≤ cellOf Kf u ∧
      vHp (vlane Kf u) = q ∧ vHj (vlane Kf u) = i ∧ vSe (vlane Kf u) = cx.e ∧
      sharedOk Kf st q i cx u (cellOf Kf u) (vSh (vlane Kf u)) (T.oLane (cellOf Kf u)) = true := by
  obtain ⟨q, i, st, cx, ho, hh⟩ := home_at H hu
  obtain ⟨-, -, -, h4, -, h6⟩ := homeOk_spec _ hh
  have hc : 2 ≤ cellOf Kf u := by
    by_contra hc; exact hs (h4 (by unfold cellOf at hc; omega))
  obtain ⟨h1, h2, h3, h7⟩ := h6 hc hs
  exact ⟨q, i, st, cx, ho, hc, h1, h2, h3, h7⟩

/-- An unshared value owns its cell. -/
theorem unshared_owner (H : CheckL cf C P fs main mc T) {u : ℕ} (hu : u < C.locs.length)
    (hs : vSh (vlane Kf u) = 0) (hc : 2 ≤ cellOf Kf u) : T.oLane (cellOf Kf u) = 4 * u + 1 := by
  obtain ⟨q, i, st, cx, ho, hh⟩ := home_at H hu
  exact (homeOk_spec _ hh).2.2.2.2.1 hc hs

/-- A shared value's lane agrees with its value lane. -/
theorem sl_fields (H : CheckL cf C P fs main mc T) {u : ℕ} (hu : u < C.locs.length)
    (hs : vSh (vlane Kf u) ≠ 0) : sCell (SLv Kf u) = cellOf Kf u ∧ sHp (SLv Kf u) = vHp (vlane Kf u) ∧
      sHj (SLv Kf u) = vHj (vlane Kf u) := by
  obtain ⟨q, i, st, cx, -, -, h1, h2, -, hsh⟩ := shared_home H hu hs
  obtain ⟨g1, g2, g3, -⟩ := sharedOk_spec _ hsh
  exact ⟨g1, g2.trans h1.symm, g3.trans h2.symm⟩

/-- A shared operand's home is at or before it. -/
theorem hp_le (H : CheckL cf C P fs main mc T) {q i : ℕ} {v : V} {st : Stmt} {cx : Ctx}
    (ho : Opd cf T q i v st cx) (hs : vSh (vlane Kf v.idx) ≠ 0) :
    vHp (vlane Kf v.idx) < q ∨ (vHp (vlane Kf v.idx) = q ∧ vHj (vlane Kf v.idx) ≤ i) := by
  obtain ⟨n, n', -, hoc⟩ := opd_occ H ho
  rcases (occOk_spec _ hoc).2 with ⟨-, -, hh⟩ | ⟨-, -, hc | ⟨hc, -⟩⟩
  · obtain ⟨-, -, -, h4, -, h6⟩ := homeOk_spec _ hh
    have hc : 2 ≤ vCell (vlane Kf v.idx) := by
      by_contra hc; exact hs (h4 (by omega))
    obtain ⟨h1, h2, -⟩ := h6 hc hs
    exact .inr ⟨h1, h2.le⟩
  · exact absurd hc hs
  · rcases hc with hc | ⟨hc1, hc2⟩
    · exact .inl hc
    · exact .inr ⟨hc1, hc2.le⟩

end Homes

/-! ## Paths -/

/-- Position `q` runs on the path of `σ`: the parameters' (`0`), or a body position the path
runs. -/
def Ran (σ : Val) (cf : Core.Fn) (q : ℕ) : Prop := q = 0 ∨ RunsL σ 1 cf.body q

section Cover

variable {cf : Core.Fn} {C : Cert} {P : Plumb} {fs : ℕ} {main : Bool} {mc : ℕ} {T : Tabs} {σ : Val}

local notation "Kf" => fnK cf C P fs main mc T

/-- **A shared value's home runs** wherever it occurs on the path: its home's block holds the
occurrence. -/
theorem cover (H : CheckL cf C P fs main mc T) {q i : ℕ} {v : V} {st : Stmt} {cx : Ctx}
    (ho : Opd cf T q i v st cx) (hq : Ran σ cf q) (hs : vSh (vlane Kf v.idx) ≠ 0) :
    Ran σ cf (vHp (vlane Kf v.idx)) := by
  have hlt := opd_lt H ho
  obtain ⟨q0, i0, st0, cx0, ho0, -, h1, -, h3, -⟩ := shared_home H hlt hs
  obtain ⟨n, n', -, hoc⟩ := opd_occ H ho
  rcases (occOk_spec _ hoc).2 with ⟨-, -, hh⟩ | ⟨-, -, hc | ⟨hc1, hc2⟩⟩
  · obtain ⟨-, -, -, h4, -, h6⟩ := homeOk_spec _ hh
    have hc : 2 ≤ vCell (vlane Kf v.idx) := by
      by_contra hc; exact hs (h4 (by omega))
    rw [(h6 hc hs).1]; exact hq
  · exact absurd hc hs
  · rw [h1] at hc1 ⊢
    rw [h3] at hc2
    rcases ho0.1 with ⟨rfl, -, -⟩ | ⟨h01, hat⟩
    · exact .inl rfl
    · rcases hq with rfl | hq
      · omega
      · exact .inr (runs_dom (c := c0 T) H.e hat (by omega) hc2 hq)

end Cover

/-! ## A cell's list -/

section Cell

variable {cf : Core.Fn} {C : Cert} {P : Plumb} {fs : ℕ} {main : Bool} {mc : ℕ} {T : Tabs}

local notation "Kf" => fnK cf C P fs main mc T

/-- The shared values of cell `c`. -/
def InCell (cf : Core.Fn) (C : Cert) (P : Plumb) (fs : ℕ) (main : Bool) (mc : ℕ) (T : Tabs) (c u : ℕ) : Prop :=
  u < C.locs.length ∧ vSh (vlane (fnK cf C P fs main mc T) u) ≠ 0 ∧ cellOf (fnK cf C P fs main mc T) u = c

theorem cell_head (H : CheckL cf C P fs main mc T) {c u : ℕ} (hu : InCell cf C P fs main mc T c u)
    (hp : sPrev (SLv Kf u) = 0) : u = (T.oLane c >>> 2) - 1 := by
  obtain ⟨hlt, hs, rfl⟩ := hu
  obtain ⟨q, i, st, cx, -, -, -, -, -, hsh⟩ := shared_home H hlt hs
  obtain ⟨-, -, -, -, h5, -⟩ := sharedOk_spec _ hsh
  have := (h5 hp).1
  omega

theorem cell_prev (H : CheckL cf C P fs main mc T) {c u : ℕ} (hu : InCell cf C P fs main mc T c u)
    (hp : sPrev (SLv Kf u) ≠ 0) : InCell cf C P fs main mc T c (sPrev (SLv Kf u) - 1) ∧
      keyOf (SLv Kf (sPrev (SLv Kf u) - 1)) < keyOf (SLv Kf u) ∧
      sNext (SLv Kf (sPrev (SLv Kf u) - 1)) - 1 = u ∧
      sHead (SLv Kf (sPrev (SLv Kf u) - 1)) = sHead (SLv Kf u) ∧
      (sKind (SLv Kf u) = kRoot → ∃ q i st cx, Opd cf T q i (V.n u) st cx ∧ sHp (SLv Kf u) = q ∧
        cx.t + 1 ≤ sHead (SLv Kf u) ∧ sHp (SLv Kf (sPrev (SLv Kf u) - 1)) < cx.a) := by
  obtain ⟨hlt, hs, rfl⟩ := hu
  obtain ⟨q, i, st, cx, ho, -, -, -, -, hsh⟩ := shared_home H hlt hs
  have hcw0 := fun w hw1 hw2 ↦ (sl_fields H (u := w) hw1 hw2).1
  simp only [SLv, keyOf] at *
  obtain ⟨g1, g2, g3, -, -, h6, -⟩ := sharedOk_spec _ hsh
  obtain ⟨w1, w2, w3, w4, w5, w6, w7⟩ := h6 hp
  replace w1 : _ < C.locs.length := lt_of_lt_of_eq w1 H.nv
  have hcw := hcw0 _ w1 w2
  have hj1 := sHj_lt ((fnK cf C P fs main mc T).T.sLane (vSh (vlane (fnK cf C P fs main mc T)
    (sPrev ((fnK cf C P fs main mc T).T.sLane (vSh (vlane (fnK cf C P fs main mc T) u) - 1)) - 1)) - 1))
  have hj2 := sHj_lt ((fnK cf C P fs main mc T).T.sLane (vSh (vlane (fnK cf C P fs main mc T) u) - 1))
  refine ⟨⟨w1, w2, ?_⟩, ?_, ?_, w5, fun hk ↦ ⟨q, i, st, cx, ho, g2, w7 hk⟩⟩
  · rw [← hcw]; exact w3
  · rw [g2, g3]
    rcases w6 with w6 | ⟨w6, w6'⟩
    · nlinarith
    · rw [w6]; omega
  · omega

theorem cell_order (H : CheckL cf C P fs main mc T) {c u u' : ℕ} (hu : InCell cf C P fs main mc T c u)
    (hu' : InCell cf C P fs main mc T c u') :
    (keyOf (SLv Kf u') < keyOf (SLv Kf u) → sPrev (SLv Kf u) ≠ 0 ∧
      keyOf (SLv Kf u') ≤ keyOf (SLv Kf (sPrev (SLv Kf u) - 1))) ∧
    (keyOf (SLv Kf u) = keyOf (SLv Kf u') → u = u') :=
  chain_order (S := InCell cf C P fs main mc T c) (prev := fun u ↦ sPrev (SLv Kf u))
    (next := fun w ↦ sNext (SLv Kf w) - 1) (key := fun u ↦ keyOf (SLv Kf u))
    (fun _ hu hp ↦ cell_head H hu hp)
    (fun _ hu hp ↦ ⟨(cell_prev H hu hp).1, (cell_prev H hu hp).2.1, (cell_prev H hu hp).2.2.1⟩) hu hu'

/-- The head of a cell's list comes first, and every value of the list names its position. -/
theorem cell_head_first (H : CheckL cf C P fs main mc T) {c : ℕ} :
    ∀ (n u : ℕ), keyOf (SLv Kf u) < n → InCell cf C P fs main mc T c u →
      ∃ h, InCell cf C P fs main mc T c h ∧ sHead (SLv Kf u) = sHp (SLv Kf h) ∧
        ∀ u', InCell cf C P fs main mc T c u' → keyOf (SLv Kf h) ≤ keyOf (SLv Kf u')
  | 0, u, hn, _ => by omega
  | n + 1, u, hn, hu => by
      by_cases hp : sPrev (SLv Kf u) = 0
      · refine ⟨u, hu, ?_, fun u' hu' ↦ ?_⟩
        · obtain ⟨hlt, hs, -⟩ := hu
          obtain ⟨q, i, st, cx, -, -, -, -, -, hsh⟩ := shared_home H hlt hs
          obtain ⟨-, g2, -, -, h5, -⟩ := sharedOk_spec _ hsh
          exact (h5 hp).2.trans g2.symm
        · by_contra hlt
          exact ((cell_order H hu hu').1 (by omega)).1 hp
      · obtain ⟨hw, hk, -, hhd, -⟩ := cell_prev H hu hp
        obtain ⟨h, hh, hhe, hmin⟩ := cell_head_first H n _ (by omega) hw
        exact ⟨h, hh, hhd.symm.trans hhe, hmin⟩

end Cell

/-! ## The cells' words -/

section Words

variable {cf : Core.Fn} {C : Cert} {P : Plumb} {fs : ℕ} {main : Bool} {mc : ℕ} {T : Tabs} {σ : Val}

local notation "Kf" => fnK cf C P fs main mc T

/-- The shared values of cell `c` whose homes run. -/
def RanIn (cf : Core.Fn) (C : Cert) (P : Plumb) (fs : ℕ) (main : Bool) (mc : ℕ) (T : Tabs) (σ : Val) (c u : ℕ) : Prop :=
  InCell cf C P fs main mc T c u ∧ Ran σ cf (sHp (SLv (fnK cf C P fs main mc T) u))

open Classical in
/-- **The word of cell `c`** on the path of `σ`: a fixed cell's constant, a one-value cell's
value, or a shared cell's first value whose home runs. -/
noncomputable def psi (cf : Core.Fn) (C : Cert) (P : Plumb) (fs : ℕ) (main : Bool) (mc : ℕ) (T : Tabs) (σ : Val)
    (c : ℕ) : E :=
  if hs : ∃ a b, (c, PC.k a b) ∈ P.stat then tw (hs.choose, hs.choose_spec.choose)
  else if T.oLane c % 4 = 1 then σ (V.n (T.oLane c >>> 2 ))
  else if hm : ∃ m u, RanIn cf C P fs main mc T σ c u ∧ keyOf (SLv (fnK cf C P fs main mc T) u) = m then
    σ (V.n (Nat.find (p := fun u ↦ RanIn cf C P fs main mc T σ c u ∧
      keyOf (SLv (fnK cf C P fs main mc T) u) = Nat.find hm) (Nat.find_spec hm)))
  else 0

theorem apartL_nodup (H : CheckL cf C P fs main mc T) : (P.stat.map Prod.fst).Nodup := by
  have h := H.apart
  unfold apartOkL at h
  simp only [natSeq_eq, band] at h
  exact (bitsNodup_spec _ _ h.1.1.1.1.2).1

theorem stat_ot (H : CheckL cf C P fs main mc T) {o a b : ℕ} (h : (o, PC.k a b) ∈ P.stat) :
    T.oLane o % 4 = 3 :=
  (statOk_spec P.stat 0 (by rw [← statOk_eq]; exact H.stat)).1 _ h a b rfl

theorem psi_stat (H : CheckL cf C P fs main mc T) {o a b : ℕ} (h : (o, PC.k a b) ∈ P.stat) :
    psi cf C P fs main mc T σ o = tw (a, b) := by
  have hs : ∃ a b, (o, PC.k a b) ∈ P.stat := ⟨a, b, h⟩
  unfold psi
  rw [dite_eq_left_of_eq_true (eq_true hs)]
  have h2 := hs.choose_spec.choose_spec
  have := List.inj_on_of_nodup_map (apartL_nodup H) h2 h rfl
  simp only [Prod.mk.injEq, PC.k.injEq, true_and] at this
  exact congrArg tw (Prod.ext this.1 this.2)

theorem not_stat (H : CheckL cf C P fs main mc T) {c : ℕ} (hc : T.oLane c % 4 ≠ 3) :
    ¬ ∃ a b, (c, PC.k a b) ∈ P.stat := fun ⟨_, _, h⟩ ↦ hc (stat_ot H h)

theorem psi_owner (H : CheckL cf C P fs main mc T) {u : ℕ} (hu : u < C.locs.length)
    (hs : vSh (vlane Kf u) = 0) (hc : 2 ≤ cellOf Kf u) : psi cf C P fs main mc T σ (cellOf Kf u) = σ (V.n u) := by
  have ho := unshared_owner H hu hs hc
  have ho' : T.oLane (cellOf Kf u) = 4 * u + 1 := ho
  unfold psi
  rw [dite_eq_right_of_eq_false (eq_false (not_stat H (by rw [ho']; omega))), ite_eq_left_of_eq_true _ _ (eq_true (by rw [ho']; omega))]
  congr 2; rw [ho']; omega

end Words

/-! ## Every shared value whose home runs holds its cell's word -/

section Shared

variable {cf : Core.Fn} {C : Cert} {P : Plumb} {fs : ℕ} {main : Bool} {mc : ℕ} {T : Tabs} {σ : Val}

local notation "Kf" => fnK cf C P fs main mc T

/-- **A root is its cell's first value whose home runs.** -/
theorem root_first (H : CheckL cf C P fs main mc T) {c u u' : ℕ} (hu : RanIn cf C P fs main mc T σ c u)
    (hr : sKind (SLv Kf u) = kRoot) (hu' : RanIn cf C P fs main mc T σ c u') (hne : u' ≠ u) :
    keyOf (SLv Kf u) < keyOf (SLv Kf u') := by
  rcases Nat.lt_trichotomy (keyOf (SLv Kf u')) (keyOf (SLv Kf u)) with hlt | heq | hgt
  · obtain ⟨hp, hle⟩ := (cell_order H hu.1 hu'.1).1 hlt
    obtain ⟨-, -, -, -, hroot⟩ := cell_prev H hu.1 hp
    obtain ⟨q, i, st, cx, ho, hq, ht, ha⟩ := hroot hr
    obtain ⟨h, hh, hhd, hmin⟩ := cell_head_first H (keyOf (SLv Kf u) + 1) u (by omega) hu.1
    have h1 := hmin u' hu'.1
    have j1 := sHj_lt (SLv Kf h)
    have j2 := sHj_lt (SLv Kf u')
    have j3 := sHj_lt (SLv Kf (sPrev (SLv Kf u) - 1))
    unfold keyOf at h1 hle
    have z1 : sHp (SLv Kf h) ≤ sHp (SLv Kf u') := by nlinarith
    have z2 : sHp (SLv Kf u') ≤ sHp (SLv Kf (sPrev (SLv Kf u) - 1)) := by nlinarith
    rcases ho.1 with ⟨rfl, -, rfl⟩ | ⟨hq1, hat⟩
    · exact absurd ha (by simp [c0])
    · have hrq : RunsL σ 1 cf.body q := by
        rcases hu.2 with h0 | h0
        · omega
        · rw [hq] at h0; exact h0
      have hrz : RunsL σ 1 cf.body (sHp (SLv Kf u')) := by
        rcases hu'.2 with h0 | h0
        · omega
        · exact h0
      exact (runs_arm' (c := c0 T) (by simp [c0]) hat hrq (by omega) (by omega) hrz).elim
  · exact absurd ((cell_order H hu.1 hu'.1).2 heq.symm) (Ne.symm hne)
  · exact hgt

theorem psi_root (H : CheckL cf C P fs main mc T) {c u : ℕ} (hu : RanIn cf C P fs main mc T σ c u)
    (hr : sKind (SLv Kf u) = kRoot) : psi cf C P fs main mc T σ c = σ (V.n u) := by
  have hu0 := hu
  obtain ⟨⟨hlt, hs, rfl⟩, -⟩ := hu0
  obtain ⟨q, i, st, cx, -, -, -, -, -, hsh⟩ := shared_home H hlt hs
  obtain ⟨-, -, -, h4, -, -, hj⟩ := sharedOk_spec _ hsh
  have h3 := (justOk_spec _ hj).1 hr
  classical
  unfold psi
  rw [dite_eq_right_of_eq_false (eq_false (not_stat H h3)), ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
  have hm : ∃ m u', RanIn cf C P fs main mc T σ (cellOf Kf u) u' ∧ keyOf (SLv Kf u') = m := ⟨_, u, hu, rfl⟩
  rw [dite_eq_left_of_eq_true (eq_true hm)]
  have hfind : Nat.find hm = keyOf (SLv Kf u) := by
    rw [Nat.find_eq_iff]
    refine ⟨⟨u, hu, rfl⟩, fun m hm' ⟨u', hu', hk⟩ ↦ ?_⟩
    by_cases hne : u' = u
    · subst hne; omega
    · have := root_first H hu hr hu' hne; omega
  congr 1
  generalize hx : Nat.find (p := fun u' ↦ RanIn cf C P fs main mc T σ (cellOf Kf u) u' ∧
    keyOf (SLv Kf u') = Nat.find hm) _ = x
  have hxs := Nat.find_spec (p := fun u' ↦ RanIn cf C P fs main mc T σ (cellOf Kf u) u' ∧
    keyOf (SLv Kf u') = Nat.find hm) (Nat.find_spec hm)
  rw [hx] at hxs
  rw [hfind] at hxs
  rw [(cell_order H hu.1 hxs.1.1).2 hxs.2.symm]

/-- A home's place: position, roots first, then operand. -/
def rankOf (s : ℕ) : ℕ := sHp s * 512 + (if sKind s = kRoot then 0 else 256) + sHj s

end Shared

theorem rankOf_le_hp (s : ℕ) : sHp s * 512 ≤ rankOf s ∧ rankOf s < sHp s * 512 + 512 := by
  have := sHj_lt s
  unfold rankOf
  by_cases h : sKind s = kRoot <;> simp only [h, ↓reduceIte] <;> omega

theorem rankOf_lt_of_hp {s s' : ℕ} (h : sHp s < sHp s') : rankOf s < rankOf s' := by
  have := rankOf_le_hp s; have := rankOf_le_hp s'; omega

theorem rank_known {K : FnK} {q i w : ℕ} (hs : vSh (vlane K w) ≠ 0) (hk : known K q i w = true) :
    rankOf (SLv K w) < q * 512 + 256 + i := by
  rcases known_spec K hk with ⟨h0, -⟩ | ⟨-, -, hk'⟩
  · exact absurd h0 hs
  · have h1 := rankOf_le_hp (SLv K w)
    have hj := sHj_lt (SLv K w)
    simp only [SLv] at *
    rcases hk' with hk' | ⟨hk', hk''⟩
    · omega
    · unfold rankOf
      rw [hk']
      rcases hk'' with hk'' | hk''
      · simp only [hk'', ↓reduceIte]; omega
      · by_cases h : sKind (K.T.sLane (vSh (vlane K w) - 1)) = kRoot <;> simp only [h, ↓reduceIte] <;> omega

/-- An operand of an atom is an operand of its position. -/
theorem opd_atom {cf : Core.Fn} {T : Tabs} {q i : ℕ} {v : V} {a : Core.Atom} {cx : Ctx}
    (h : Opd cf T q i v (.atom a) cx) {x : V} (hx : x ∈ atomVals a) : ∃ i', Opd cf T q i' x (.atom a) cx := by
  obtain ⟨i', hi'⟩ := mem_getElem? hx
  exact ⟨i', h.1, by simpa [ownVals] using hi'⟩

theorem opd_body {cf : Core.Fn} {T : Tabs} {q i : ℕ} {v : V} {a : Core.Atom} {cx : Ctx}
    (h : Opd cf T q i v (.atom a) cx) : 1 ≤ q ∧ AtL (c0 T) 1 cf.body q (.atom a) cx := by
  rcases h.1 with ⟨-, h2, -⟩ | h1
  · cases h2
  · exact h1

section Main

variable {cf : Core.Fn} {C : Cert} {P : Plumb} {fs : ℕ} {main : Bool} {mc : ℕ} {T : Tabs} {σ : Val}
  {rd : Reader} {es : List Ev} {vs : List V}

local notation "Kf" => fnK cf C P fs main mc T

/-- An atom at a position the returning path runs holds. -/
theorem atom_holds (hw : walk σ cf.body = .ret es vs) (he : ∀ e ∈ es, e.Holds rd σ) {q : ℕ} {a : Core.Atom}
    {cx : Ctx} (hat : AtL (c0 T) 1 cf.body q (.atom a) cx) (hr : RunsL σ 1 cf.body q) : a.Holds rd σ := by
  have := runs_atom hat hr (by rw [hw]; exact fun h ↦ nomatch h)
  rw [hw] at this
  exact he _ this

/-- **Every shared value whose home runs holds its cell's word.** -/
theorem shared_eq (H : CheckL cf C P fs main mc T) (hw : walk σ cf.body = .ret es vs)
    (he : ∀ e ∈ es, e.Holds rd σ) : ∀ (r u : ℕ), rankOf (SLv Kf u) = r →
      RanIn cf C P fs main mc T σ (cellOf Kf u) u → σ (V.n u) = psi cf C P fs main mc T σ (cellOf Kf u) := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
  intro u hr hu
  have hu0 := hu
  obtain ⟨⟨hlt, hs, -⟩, hran⟩ := hu0
  obtain ⟨q, i, st, cx, ho, hc2, hv1, hv2, -, hsh⟩ := shared_home H hlt hs
  obtain ⟨g1, g2, g3, h4, -, -, hj⟩ := sharedOk_spec _ hsh
  have hsl : sHp (SLv Kf u) = q ∧ sHj (SLv Kf u) = i := ⟨g2, g3⟩
  obtain ⟨hroot, hjust⟩ := justOk_spec _ hj
  by_cases hk : sKind (SLv Kf u) = kRoot
  · exact (psi_root H hu hk).symm
  obtain ⟨a, rfl, hcase⟩ := hjust hk
  obtain ⟨hq1, hat⟩ := opd_body ho
  have hrq : RunsL σ 1 cf.body q := by
    rcases hran with h0 | h0
    · rw [hsl.1] at h0; omega
    · rw [hsl.1] at h0; exact h0
  have ha := atom_holds hw he hat hrq
  have hv : (atomVals a)[i]? = some (V.n u) := by simpa [ownVals] using ho.2
  have hru : rankOf (SLv Kf u) = q * 512 + 256 + i := by
    unfold rankOf; simp only [hk, ↓reduceIte]; rw [hsl.1, hsl.2]
  -- the word of a value at a position that runs, from its rank
  have hval : ∀ (x : V) q' i' st' cx', Opd cf T q' i' x st' cx' → Ran σ cf q' →
      (vSh (vlane Kf x.idx) ≠ 0 → rankOf (SLv Kf x.idx) < r) →
      (vSh (vlane Kf x.idx) = 0 → 2 ≤ cellOf Kf x.idx) → σ x = psi cf C P fs main mc T σ (cellOf Kf x.idx) := by
    intro x q' i' st' cx' hox hq' hrk hcx
    have hxlt := opd_lt H hox
    rw [opd_vn H hox]
    by_cases hxs : vSh (vlane Kf x.idx) = 0
    · exact (psi_owner H hxlt hxs (hcx hxs)).symm
    · have hcov := cover H hox hq' hxs
      rw [← (sl_fields H hxlt hxs).2.1] at hcov
      exact ih _ (hrk hxs) x.idx rfl ⟨⟨hxlt, hxs, rfl⟩, hcov⟩
  -- an anchor's position runs, its atom holds
  have hanchor : ∀ m, m < T.nat → aP ((fnK cf C P fs main mc T).T.aLane m) < q →
      q < aE ((fnK cf C P fs main mc T).T.aLane m) →
      ∃ a' cx', AtL (c0 T) 1 cf.body (aP ((fnK cf C P fs main mc T).T.aLane m)) (.atom a') cx' ∧
        RunsL σ 1 cf.body (aP ((fnK cf C P fs main mc T).T.aLane m)) ∧ a'.Holds rd σ ∧
        anchorOk Kf (.atom a') cx' ((fnK cf C P fs main mc T).T.aLane m) = true := by
    intro m hm hp hq
    change aP (T.aLane m) < q at hp
    change q < aE (T.aLane m) at hq
    obtain ⟨st', cx', hat', hok⟩ := anchor_exists H hm
    obtain ⟨a', rfl, hae, -⟩ := anchorOk_spec _ hok
    have hr' := runs_dom (c := c0 T) H.e hat' hp.le (by rw [hae] at hq; exact hq) hrq
    exact ⟨a', cx', hat', hr', atom_holds hw he hat' hr', hok⟩
  -- an anchor's output is shared, in the cell
  have hshared : ∀ x : V, cellOf Kf x.idx = cellOf Kf u → x.idx < C.locs.length → vSh (vlane Kf x.idx) ≠ 0 := by
    intro x hcx hxlt h0
    have := unshared_owner H hxlt h0 (by rw [hcx]; exact hc2)
    rw [hcx] at this
    rw [this] at h4; omega
  -- a value of an earlier position has a smaller rank
  have hearly : ∀ (x : V) q' i' st' cx', Opd cf T q' i' x st' cx' → q' < q → vSh (vlane Kf x.idx) ≠ 0 →
      rankOf (SLv Kf x.idx) < r := by
    intro x q' i' st' cx' hox hq' hxs
    have hxlt := opd_lt H hox
    have hle := hp_le H hox hxs
    rw [← (sl_fields H hxlt hxs).2.1] at hle
    rw [← hr]
    apply rankOf_lt_of_hp
    rw [hsl.1]; omega
  rcases hcase with ⟨-, w, hwq, hws, hwc, hkn⟩ | ⟨-, y, hy, haux, ht0, ht1, ht2⟩ |
      ⟨-, y, hy, hm, hc1, hcell, hk0, hk1, hp, hq⟩ | ⟨-, op, ins, hky, hm, hc0, hcell, hop, hins, hp, hq, hkn⟩
  · -- eq
    rw [eqAt_sound hwq hv ha]
    obtain ⟨i', hoi⟩ := opd_atom ho (eqAt_mem hwq)
    rw [← hwc]
    exact hval w q i' _ cx hoi (.inr hrq) (fun _ ↦ by rw [← hr, hru]; exact rank_known hws hkn)
      (fun h0 ↦ absurd h0 hws)
  · -- fixed constant
    have hst := (statOk_spec P.stat 0 (by rw [← statOk_eq]; exact H.stat)).2 _ (Nat.zero_le _) haux
    rw [ht0, ht1, ht2] at hst
    rw [constAt_sound hy hv ha, psi_stat H hst]
  · -- anchored constant
    obtain ⟨a', cx', hat', hr', ha', hok⟩ := hanchor _ hm hp hq
    obtain ⟨a'', he', hae, -, w, hw, hwc, hcase'⟩ := anchorOk_spec _ hok
    injection he' with he''
    subst he''
    rcases hcase' with ⟨-, hc'⟩ | ⟨hc', -⟩
    · obtain ⟨j, hoj⟩ := opd_atom (cf := cf) (T := T) (v := w) ⟨.inr ⟨(atL_range hat').1, hat'⟩, by simpa [ownVals] using hw⟩
          (List.mem_of_getElem? hw)
      have hwlt := opd_lt H hoj
      have hwc' : cellOf Kf w.idx = cellOf Kf u := hwc.trans hcell
      have e1 : σ w = tw y := by
        rw [constAt_sound hc' hw ha']; exact congrArg tw (Prod.ext hk0 hk1)
      rw [constAt_sound hy hv ha, ← e1, ← hwc']
      exact hval w _ j _ cx' hoj (.inr hr') (hearly w _ j _ cx' hoj hp) (fun h0 ↦ absurd h0 (hshared w hwc' hwlt))
    · exact absurd hc1 hc'
  · -- key
    obtain ⟨a', cx', hat', hr', ha', hok⟩ := hanchor _ hm hp hq
    obtain ⟨a'', he', hae, -, w, hw, hwc, hcase'⟩ := anchorOk_spec _ hok
    injection he' with he''
    subst he''
    rcases hcase' with ⟨hc', -⟩ | ⟨-, op', ins', hk', hop', hins', hcells'⟩
    · rw [hc'] at hc0; cases hc0
    obtain ⟨j, hoj⟩ := opd_atom (cf := cf) (T := T) (v := w) ⟨.inr ⟨(atL_range hat').1, hat'⟩, by simpa [ownVals] using hw⟩
        (List.mem_of_getElem? hw)
    have hwlt := opd_lt H hoj
    have hwc' : cellOf Kf w.idx = cellOf Kf u := hwc.trans hcell
    have hop2 : op' = op := hop'.symm.trans hop
    rw [hop2] at hk' hins'
    -- the inputs' words
    have hin : ins.map σ = (ins.map fun x ↦ cellOf Kf x.idx).map (psi cf C P fs main mc T σ) := by
      rw [List.map_map]
      refine List.map_congr_left fun x hx ↦ ?_
      obtain ⟨ix, hox⟩ := opd_atom ho (keyAt_mem hky x hx)
      rcases known_spec _ (hkn x hx) with ⟨h0, h2⟩ | ⟨hxs, -, -⟩
      · exact hval x q ix _ cx hox (.inr hrq) (fun hne ↦ absurd h0 hne) (fun _ ↦ h2)
      · exact hval x q ix _ cx hox (.inr hrq) (fun _ ↦ by rw [← hr, hru]; exact rank_known hxs (hkn x hx))
          (fun h0 ↦ absurd h0 hxs)
    have hin' : ins'.map σ = (ins'.map fun x ↦ cellOf Kf x.idx).map (psi cf C P fs main mc T σ) := by
      rw [List.map_map]
      refine List.map_congr_left fun x hx ↦ ?_
      obtain ⟨ix, hox⟩ := opd_atom hoj (keyAt_mem hk' x hx)
      exact hval x _ ix _ cx' hox (.inr hr') (hearly x _ ix _ cx' hox hp) (fun _ ↦ hcells' x hx)
    -- the cells agree
    have hkeq : keyCells op (ins.map fun x ↦ cellOf Kf x.idx) = keyCells op (ins'.map fun x ↦ cellOf Kf x.idx) := by
      have e : keyPack Kf op ins = keyPack Kf op ins' := hins.symm.trans hins'
      unfold keyPack at e
      rw [mapR_eq, mapR_eq] at e
      refine packCells_inj _ _ (fun c hc ↦ ?_) (fun c hc ↦ ?_) e
      · rw [mem_keyCells] at hc
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc
        have h2 : 2 ≤ cellOf Kf x.idx := by
          rcases known_spec _ (hkn x hx) with ⟨-, h2⟩ | ⟨hxs, h2, -⟩
          · exact h2
          · have hxlt : x.idx < C.locs.length := by
              obtain ⟨ix, hox⟩ := opd_atom ho (keyAt_mem hky x hx); exact opd_lt H hox
            rw [← (sl_fields H hxlt hxs).1]; exact h2
        exact ⟨by omega, fld_lt _ 0 16⟩
      · rw [mem_keyCells] at hc
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc
        exact ⟨by have := hcells' x hx; omega, fld_lt _ 0 16⟩
    have k1 := keyAt_sound hky hv ha
    have k2 := keyAt_sound hk' hw ha'
    rw [hin, ← keyHolds_keyCells, hkeq] at k1
    rw [hin', ← keyHolds_keyCells] at k2
    rw [k1.unique k2, ← hwc']
    exact hval w _ j _ cx' hoj (.inr hr') (hearly w _ j _ cx' hoj hp) (fun h0 ↦ absurd h0 (hshared w hwc' hwlt))

/-- **The sharing check's conclusion on a path** of a function that returns: one word per cell
for every value the path names, a fixed cell's constant. -/
theorem path_of_check (H : CheckL cf C P fs main mc T) (hw : walk σ cf.body = .ret es vs)
    (he : ∀ e ∈ es, e.Holds rd σ) :
    ∃ Ψ : ℕ → E, (∀ v ∈ cf.params ++ es.flatMap Ev.uses ++ vs, 2 ≤ C.locs.getD v.idx 0 →
        σ v = Ψ (C.locs.getD v.idx 0)) ∧
      ∀ o a b, (o, PC.k a b) ∈ P.stat → Ψ o = OffsetInstruction.immediateWord a b := by
  have hloc : ∀ u < C.locs.length, cellOf Kf u = C.locs.getD u 0 := fun u hu ↦ by
    have := locsOk_spec (T := T) C.locs 0 H.locs u hu
    rw [Nat.zero_add] at this
    simp only [List.getD, List.getElem?_eq_getElem hu, Option.getD_some]; exact this
  refine ⟨psi cf C P fs main mc T σ, fun v hv hc ↦ ?_, fun o a b h ↦ psi_stat H h⟩
  -- an operand at a position that runs
  obtain ⟨q, i, st, cx, ho, hq⟩ : ∃ q i st cx, Opd cf T q i v st cx ∧ Ran σ cf q := by
    rcases List.mem_append.mp hv with hv | hv
    · rcases List.mem_append.mp hv with hv | hv
      · obtain ⟨i, hi⟩ := mem_getElem? hv
        exact ⟨0, i, .ret cf.params, c0 T, ⟨.inl ⟨rfl, rfl, rfl⟩, by simpa [ownVals] using hi⟩, .inl rfl⟩
      · obtain ⟨q, s, c', hat, hr, hn⟩ := walk_names (c := c0 T) (p := 1) hw (List.mem_append_left _ hv)
        obtain ⟨i, hi⟩ := mem_getElem? (names_sub hn)
        exact ⟨q, i, s, c', ⟨.inr ⟨(atL_range hat).1, hat⟩, hi⟩, .inr hr⟩
    · obtain ⟨q, s, c', hat, hr, hn⟩ := walk_names (c := c0 T) (p := 1) hw (List.mem_append_right _ hv)
      obtain ⟨i, hi⟩ := mem_getElem? (names_sub hn)
      exact ⟨q, i, s, c', ⟨.inr ⟨(atL_range hat).1, hat⟩, hi⟩, .inr hr⟩
  have hlt := opd_lt H ho
  rw [← hloc _ hlt] at hc ⊢
  rw [opd_vn H ho]
  by_cases hs : vSh (vlane Kf v.idx) = 0
  · exact (psi_owner H hlt hs hc).symm
  · have hcov := cover H ho hq hs
    rw [← (sl_fields H hlt hs).2.1] at hcov
    exact shared_eq H hw he _ v.idx rfl ⟨⟨hlt, hs, rfl⟩, hcov⟩

end Main

end
end LeanVM.Guest.B2C.ShareL
