/-
  LeanVM.Guest.B2C.ShareLSpec

  What the local sharing check says, position by position and value by value.
-/

module

public import LeanVM.Guest.B2C.ShareL

/-!
# The local sharing check, unpacked

`shareCheckL` holding gives (`checkL_spec`): its once-per-function parts, the parameters'
occurrences, and the walk's step at every position from a pre-order sequence of states. From
those: every operand of a statement (`Opd`) passes `occOk` with some next number
(`opd_occ`), so its value is numbered (`opd_lt`); every value number has a home where `homeOk`
holds (`home_exists`); every anchor is checked at its position (`anchor_exists`).
-/

namespace LeanVM.Guest.B2C.ShareL

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Local LeanVM.Guest.Check LeanVM.Guest.Exec

@[expose] public section

/-! ## Lists and options -/

@[simp] theorem nbeq_iff' {a b : ℕ} : Nat.beq a b = true ↔ a = b :=
  ⟨Nat.eq_of_beq_eq_true, fun h ↦ h ▸ Nat.beq_refl a⟩

section Lists

variable (K : FnK)

/-- **An occurrence**, unfolded: `v` is `V.n v.idx`, and either it is the home (`v.idx` the next
number, `homeOk`), or it was numbered before and, shared, its home is before it and its home's
block holds `q`. -/
theorem occOk_spec {st : Stmt} {q i : ℕ} {cx : Ctx} {v : V} {n n' : ℕ}
    (h : occOk K st q i cx v n = some n') : vnOk v = true ∧
      ((v.idx = n ∧ n' = n + 1 ∧ homeOk K st q i cx v.idx (vlane K v.idx) = true) ∨
       (v.idx < n ∧ n' = n ∧ (vSh (vlane K v.idx) = 0 ∨
          ((vHp (vlane K v.idx) < q ∨ (vHp (vlane K v.idx) = q ∧ vHj (vlane K v.idx) < i)) ∧
            q < vSe (vlane K v.idx))))) := by
  unfold occOk at h
  cases hv : vnOk v <;> rw [hv] at h <;> simp only [Bool.cond_false, Bool.cond_true, reduceCtorEq] at h
  refine ⟨rfl, ?_⟩
  unfold occN at h
  cases h1 : Nat.beq v.idx n <;> rw [h1] at h <;> simp only [Bool.cond_true, Bool.cond_false] at h
  · right
    cases h2 : Nat.blt v.idx n <;> rw [h2] at h <;> simp only [Bool.cond_true, Bool.cond_false, reduceCtorEq] at h
    refine ⟨Nat.blt_eq.mp h2, ?_⟩
    cases h3 : Nat.beq (vSh (vlane K v.idx)) 0 <;> rw [h3] at h <;> simp only [Bool.cond_true, Bool.cond_false] at h
    · unfold covOk at h
      cases h4 : ((Nat.blt (vHp (vlane K v.idx)) q || (Nat.beq (vHp (vlane K v.idx)) q && Nat.blt (vHj (vlane K v.idx)) i)) &&
          Nat.blt q (vSe (vlane K v.idx))) <;> rw [h4] at h <;> simp only [Bool.cond_true, Bool.cond_false, reduceCtorEq] at h
      cases h
      simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq, nbeq_iff'] at h4
      exact ⟨rfl, .inr h4⟩
    · cases h; exact ⟨rfl, .inl (Nat.eq_of_beq_eq_true h3)⟩
  · left
    cases h2 : homeOk K st q i cx v.idx (vlane K v.idx) <;> rw [h2] at h <;>
      simp only [Bool.cond_true, Bool.cond_false, reduceCtorEq] at h
    cases h
    exact ⟨Nat.eq_of_beq_eq_true h1, rfl, rfl⟩

theorem occsOk_spec {st : Stmt} {q : ℕ} {cx : Ctx} : ∀ (vs : List V) (i n n' : ℕ),
    occsOk K st q cx vs i n = some n' → n ≤ n' ∧ ∀ (k : ℕ) (v : V), vs[k]? = some v →
      ∃ m m', n ≤ m ∧ m' ≤ n' ∧ occOk K st q (i + k) cx v m = some m'
  | [], i, n, n', h => by
      cases h; exact ⟨le_rfl, fun k v hv ↦ by simp at hv⟩
  | v :: vs, i, n, n', h => by
      obtain ⟨m, h1, h2⟩ := bindO_eq_some h
      obtain ⟨hle, hrest⟩ := occsOk_spec vs (i + 1) m n' h2
      have hm : n ≤ m := by rcases (occOk_spec K h1).2 with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ <;> omega
      refine ⟨by omega, fun k w hw ↦ ?_⟩
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hw
        subst hw
        exact ⟨n, m, le_rfl, hle, by simpa using h1⟩
      | succ k =>
        simp only [List.getElem?_cons_succ] at hw
        obtain ⟨a, b, ha, hb, hab⟩ := hrest k w hw
        exact ⟨a, b, by omega, hb, by rw [show i + (k + 1) = i + 1 + k by omega]; exact hab⟩

/-- The homes among a statement's operands are the numbers it passes. -/
theorem occsOk_homes {st : Stmt} {q : ℕ} {cx : Ctx} : ∀ (vs : List V) (i n n' : ℕ),
    occsOk K st q cx vs i n = some n' → ∀ u, n ≤ u → u < n' → ∃ (k : ℕ) (v : V), vs[k]? = some v ∧
      v.idx = u ∧ homeOk K st q (i + k) cx u (vlane K u) = true
  | [], i, n, n', h, u, h1, h2 => by cases h; omega
  | v :: vs, i, n, n', h, u, h1, h2 => by
      obtain ⟨m, hm, hr⟩ := bindO_eq_some h
      obtain ⟨-, hs⟩ := occOk_spec K hm
      by_cases hu : u < m
      · rcases hs with ⟨hv, rfl, hh⟩ | ⟨-, rfl, -⟩
        · refine ⟨0, v, rfl, by omega, ?_⟩
          have : u = v.idx := by omega
          subst this; simpa using hh
        · omega
      · obtain ⟨k, w, hw, hwu, hh⟩ := occsOk_homes vs (i + 1) m n' hr u (by omega) h2
        exact ⟨k + 1, w, by simpa using hw, hwu, by rw [show i + (k + 1) = i + 1 + k by omega]; exact hh⟩

/-- The anchors a position checks. -/
theorem anchorsOk_spec {st : Stmt} {q : ℕ} {cx : Ctx} : ∀ (f k k' : ℕ),
    anchorsOk K st q cx f k = some k' → k ≤ k' ∧ ∀ m, k ≤ m → m < k' →
      m < K.T.nat ∧ aP (tget wA 4 5 K.T.an m) = q ∧ anchorOk K st cx (tget wA 4 5 K.T.an m) = true
  | 0, k, k', h => by cases h; exact ⟨le_rfl, fun m h1 h2 ↦ by omega⟩
  | f + 1, k, k', h => by
      change (bif Nat.blt k K.T.nat then
          (bif Nat.beq (aP (tget wA 4 5 K.T.an k)) q then
            (bif anchorOk K st cx (tget wA 4 5 K.T.an k) then anchorsOk K st q cx f (k + 1) else none)
          else some k) else some k) = some k' at h
      cases h1 : Nat.blt k K.T.nat <;> rw [h1] at h <;> simp only [Bool.cond_true, Bool.cond_false] at h
      · cases h; exact ⟨le_rfl, fun m h1 h2 ↦ by omega⟩
      cases h2 : Nat.beq (aP (tget wA 4 5 K.T.an k)) q <;> rw [h2] at h <;> simp only [Bool.cond_true, Bool.cond_false] at h
      · cases h; exact ⟨le_rfl, fun m h1 h2 ↦ by omega⟩
      cases h3 : anchorOk K st cx (tget wA 4 5 K.T.an k) <;> rw [h3] at h <;>
        simp only [Bool.cond_true, Bool.cond_false, reduceCtorEq] at h
      obtain ⟨hle, hr⟩ := anchorsOk_spec f (k + 1) k' h
      refine ⟨by omega, fun m hm1 hm2 ↦ ?_⟩
      by_cases hm : m = k
      · subst hm; exact ⟨Nat.blt_eq.mp h1, Nat.eq_of_beq_eq_true h2, h3⟩
      · exact hr m (by omega) hm2

/-- **A step**, unfolded. -/
theorem step_spec {st st' : ℕ × ℕ} {q : ℕ} {s : Stmt} {cx : Ctx} (h : step K st q s cx = some st') :
    listedOk K s = true ∧ occsOk K s q cx (ownVals s) 0 st.1 = some st'.1 ∧
      anchorsOk K s q cx 32 st.2 = some st'.2 := by
  unfold step at h
  obtain ⟨k, hk, h⟩ := bindO_eq_some h
  cases hl : listedOk K s <;> rw [hl] at h <;> simp only [Bool.cond_true, Bool.cond_false, reduceCtorEq] at h
  obtain ⟨n, hn, h⟩ := bindO_eq_some h
  simp only [seqN_eq] at h
  cases h
  exact ⟨rfl, hn, hk⟩

end Lists

/-- A counter crossing a value between two positions crosses it at a step. -/
theorem crossing (g : ℕ → ℕ) (lo : ℕ) : ∀ (d u : ℕ), (∀ q, lo ≤ q → q < lo + d → g q ≤ g (q + 1)) →
    g lo ≤ u → u < g (lo + d) → ∃ q, lo ≤ q ∧ q < lo + d ∧ g q ≤ u ∧ u < g (q + 1)
  | 0, u, _, h1, h2 => by simp at h2; omega
  | d + 1, u, hm, h1, h2 => by
      by_cases hu : u < g (lo + d)
      · obtain ⟨q, h3, h4, h5, h6⟩ := crossing g lo d u (fun q h1 h2 ↦ hm q h1 (by omega)) h1 hu
        exact ⟨q, h3, by omega, h5, h6⟩
      · exact ⟨lo + d, by omega, by omega, by omega, by rw [show lo + d + 1 = lo + (d + 1) by omega]; exact h2⟩

/-! ## The function -/

section Fn

variable {cf : Core.Fn} {C : Cert} {P : Plumb} {fs : ℕ} {main : Bool} {mc : ℕ} {T : Tabs}

/-- The body's context. -/
def c0 (T : Tabs) : Ctx := ⟨T.e, 0, 0⟩

/-- Operand `i` of position `q` is `v`, of statement `st` in context `cx`: a parameter
(`q = 0`, the parameters as a `ret`) or a value of a body statement. -/
def Opd (cf : Core.Fn) (T : Tabs) (q i : ℕ) (v : V) (st : Stmt) (cx : Ctx) : Prop :=
  ((q = 0 ∧ st = .ret cf.params ∧ cx = c0 T) ∨ (1 ≤ q ∧ AtL (c0 T) 1 cf.body q st cx)) ∧
    (ownVals st)[i]? = some v

/-- **What the check says**, unpacked. -/
structure CheckL (cf : Core.Fn) (C : Cert) (P : Plumb) (fs : ℕ) (main : Bool) (mc : ℕ) (T : Tabs) : Prop where
  lists : listsOk P fs = true
  apart : apartOkL C P main mc = true
  sites : freeOk T (siteCells P) = true
  arms : freeOk T (P.arms.map fun a ↦ a.2.1) = true
  stat : statOk T P.stat = true
  tmps : tmpsOk T P.tmps = true
  locs : locsOk T C.locs = true
  nv : T.nv = C.locs.length
  params : ∀ v ∈ cf.params, fld (tget wV 8 5 T.vl v.idx) 0 16 < fs
  e : T.e = 1 + sizeL cf.body
  run : ∃ (n0 : ℕ) (f : ℕ → ℕ × ℕ), paramsOk (fnK cf C P fs main mc T) cf.params = some n0 ∧ f 1 = (n0, 0) ∧
    f T.e = (C.locs.length, T.nat) ∧
    ∀ q s c', AtL (c0 T) 1 cf.body q s c' → step (fnK cf C P fs main mc T) (f q) q s c' = some (f (q + 1))

theorem checkL_spec (h : shareCheckL cf C P fs main mc T = true) : CheckL cf C P fs main mc T := by
  unfold shareCheckL staticL at h
  simp only [Bool.and_eq_true, allR_eq, List.all_eq_true, Nat.blt_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hl, ha⟩, hs⟩, har⟩, hst⟩, ht⟩, hlo⟩, hnv⟩, hp⟩, h⟩ := h
  have hnv : T.nv = C.locs.length := Nat.eq_of_beq_eq_true hnv
  unfold walkL at h
  split at h
  · rename_i n0 hn0
    unfold segL at h
    rw [List.drop_zero, Nat.sub_zero, List.take_length] at h
    split at h
    · rename_i r hr
      simp only [Bool.and_eq_true, nbeq_iff', beq_iff_eq, List.drop_length] at h
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
      obtain ⟨r1, ⟨r21, r22⟩, r3⟩ := r
      simp only at h1 h2 h3 h4
      subst h1 h4
      obtain ⟨hsz, f, hf1, hfe, hsteps⟩ := fold_body (c := c0 T) (p := 1) hr
      exact ⟨hl, ha, hs, har, hst, ht, hlo, hnv, hp, by rw [← hsz]; rfl, n0, f, hn0, hf1,
        by rw [show T.e = (c0 T).e from rfl, hfe]; exact Prod.ext (h2.trans hnv) h3, hsteps⟩
    · cases h
  · cases h

end Fn

/-! ## Operands, homes, anchors -/

section Facts

variable {cf : Core.Fn} {C : Cert} {P : Plumb} {fs : ℕ} {main : Bool} {mc : ℕ} {T : Tabs}

/-- The walk's counters at a position: before it, and after. -/
theorem steps_mono (H : CheckL cf C P fs main mc T) {f : ℕ → ℕ × ℕ}
    (hst : ∀ q s c', AtL (c0 T) 1 cf.body q s c' → step (fnK cf C P fs main mc T) (f q) q s c' = some (f (q + 1)))
    {q : ℕ} (h1 : 1 ≤ q) (h2 : q < T.e) : (f q).1 ≤ (f (q + 1)).1 ∧ (f q).2 ≤ (f (q + 1)).2 := by
  obtain ⟨s, c', hat⟩ := atL_exists (c0 T) 1 cf.body q h1 (by rw [H.e] at h2; omega)
  obtain ⟨-, ho, ha⟩ := step_spec _ (hst q s c' hat)
  exact ⟨(occsOk_spec _ _ _ _ _ ho).1, (anchorsOk_spec _ _ _ _ ha).1⟩

theorem mono_le {g : ℕ → ℕ} {lo : ℕ} : ∀ (d : ℕ), (∀ q, lo ≤ q → q < lo + d → g q ≤ g (q + 1)) →
    ∀ k ≤ d, g lo ≤ g (lo + k) ∧ g (lo + k) ≤ g (lo + d)
  | 0, _, k, hk => by obtain rfl : k = 0 := by omega
                      exact ⟨le_rfl, le_rfl⟩
  | d + 1, hm, k, hk => by
      have ih := mono_le (g := g) (lo := lo) d (fun q h1 h2 ↦ hm q h1 (by omega))
      have hd : g (lo + d) ≤ g (lo + (d + 1)) := by
        rw [show lo + (d + 1) = lo + d + 1 by omega]; exact hm _ (by omega) (by omega)
      by_cases hkd : k ≤ d
      · exact ⟨(ih k hkd).1, (ih k hkd).2.trans hd⟩
      · obtain rfl : k = d + 1 := by omega
        exact ⟨(ih d le_rfl).1.trans hd, le_rfl⟩

/-- **Every operand passes `occOk`**, with a next number at most the number of values. -/
theorem opd_occ (H : CheckL cf C P fs main mc T) {q i : ℕ} {v : V} {st : Stmt} {cx : Ctx}
    (h : Opd cf T q i v st cx) : ∃ n n', n' ≤ C.locs.length ∧
      occOk (fnK cf C P fs main mc T) st q i cx v n = some n' := by
  obtain ⟨n0, f, hp, hf1, hfe, hst⟩ := H.run
  have hm : ∀ q', 1 ≤ q' → q' < 1 + (T.e - 1) → (f q').1 ≤ (f (q' + 1)).1 := fun q' h1 h2 ↦
    (steps_mono H hst h1 (by omega)).1
  have he1 : 1 + (T.e - 1) = T.e := by rw [H.e]; omega
  have hbound := mono_le (g := fun q ↦ (f q).1) (lo := 1) (T.e - 1) hm
  rw [he1, hfe] at hbound
  have hn0 : n0 ≤ C.locs.length := by simpa [hf1] using (hbound 0 (Nat.zero_le _)).2
  obtain ⟨hq, hv⟩ := h
  rcases hq with ⟨rfl, rfl, rfl⟩ | ⟨h1, hat⟩
  · obtain ⟨-, hk⟩ := occsOk_spec _ _ _ _ _ hp
    obtain ⟨m, m', -, hm', ho⟩ := hk i v hv
    rw [Nat.zero_add] at ho
    exact ⟨m, m', hm'.trans hn0, ho⟩
  · obtain ⟨-, ho, -⟩ := step_spec _ (hst q st cx hat)
    obtain ⟨-, hk⟩ := occsOk_spec _ _ _ _ _ ho
    obtain ⟨m, m', -, hm', hoc⟩ := hk i v hv
    have hq := atL_range hat
    have he := H.e
    have := (hbound (q + 1 - 1) (by omega)).2
    rw [show 1 + (q + 1 - 1) = q + 1 by omega] at this
    rw [Nat.zero_add] at hoc
    exact ⟨m, m', hm'.trans this, hoc⟩

/-- **Every operand's value is numbered.** -/
theorem opd_lt (H : CheckL cf C P fs main mc T) {q i : ℕ} {v : V} {st : Stmt} {cx : Ctx}
    (h : Opd cf T q i v st cx) : v.idx < C.locs.length := by
  obtain ⟨n, n', hn', ho⟩ := opd_occ H h
  rcases (occOk_spec _ ho).2 with ⟨h1, rfl, -⟩ | ⟨h1, rfl, -⟩ <;> omega

/-- **Every value has a home**, where `homeOk` holds. -/
theorem home_exists (H : CheckL cf C P fs main mc T) {u : ℕ} (hu : u < C.locs.length) :
    ∃ q i v st cx, Opd cf T q i v st cx ∧ v.idx = u ∧
      homeOk (fnK cf C P fs main mc T) st q i cx u (vlane (fnK cf C P fs main mc T) u) = true := by
  obtain ⟨n0, f, hp, hf1, hfe, hst⟩ := H.run
  by_cases h0 : u < n0
  · obtain ⟨k, v, hv, hvu, hh⟩ := occsOk_homes _ _ _ _ _ hp u (Nat.zero_le _) h0
    rw [Nat.zero_add] at hh
    exact ⟨0, k, v, .ret cf.params, c0 T, ⟨.inl ⟨rfl, rfl, rfl⟩, hv⟩, hvu, hh⟩
  · have he1 : 1 + (T.e - 1) = T.e := by rw [H.e]; omega
    obtain ⟨q, hq1, hq2, hq3, hq4⟩ := crossing (fun q ↦ (f q).1) 1 (T.e - 1) u
      (fun q h1 h2 ↦ (steps_mono H hst h1 (by omega)).1) (by simp only [hf1]; omega)
      (by simp only [he1, hfe]; exact hu)
    have he := H.e
    obtain ⟨s, c', hat⟩ := atL_exists (c0 T) 1 cf.body q hq1 (by omega)
    obtain ⟨-, ho, -⟩ := step_spec _ (hst q s c' hat)
    obtain ⟨k, v, hv, hvu, hh⟩ := occsOk_homes _ _ _ _ _ ho u hq3 hq4
    rw [Nat.zero_add] at hh
    exact ⟨q, k, v, s, c', ⟨.inr ⟨hq1, hat⟩, hv⟩, hvu, hh⟩

/-- **Every anchor is checked at its position.** -/
theorem anchor_exists (H : CheckL cf C P fs main mc T) {m : ℕ} (hm : m < T.nat) :
    ∃ st cx, AtL (c0 T) 1 cf.body (aP (tget wA 4 5 T.an m)) st cx ∧
      anchorOk (fnK cf C P fs main mc T) st cx (tget wA 4 5 T.an m) = true := by
  obtain ⟨n0, f, hp, hf1, hfe, hst⟩ := H.run
  have he1 : 1 + (T.e - 1) = T.e := by rw [H.e]; omega
  obtain ⟨q, hq1, hq2, hq3, hq4⟩ := crossing (fun q ↦ (f q).2) 1 (T.e - 1) m
    (fun q h1 h2 ↦ (steps_mono H hst h1 (by omega)).2) (by simp only [hf1]; omega)
    (by simp only [he1, hfe]; exact hm)
  have he := H.e
  obtain ⟨s, c', hat⟩ := atL_exists (c0 T) 1 cf.body q hq1 (by omega)
  obtain ⟨-, -, ha⟩ := step_spec _ (hst q s c' hat)
  obtain ⟨-, hk⟩ := anchorsOk_spec _ _ _ _ ha
  obtain ⟨-, hpq, hok⟩ := hk m hq3 hq4
  have hpq' : aP (tget wA 4 5 T.an m) = q := hpq
  exact ⟨s, c', by rw [hpq']; exact hat, hok⟩

end Facts

end
end LeanVM.Guest.B2C.ShareL
