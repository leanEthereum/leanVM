/-
  LeanVM.Guest.B2C.CplSites

  B2's completeness: the call sites of a path's calls are apart.
-/

module

public import LeanVM.Guest.B2C.CplComp
public import LeanVM.Guest.B2C.Frame

/-!
# The call sites apart

The completeness walk keeps the site cells it has set up on the path in a bit set (`CW.uq`): a
call's callee frame pointer cell, and a dispatch's target cell, must be unset there, and are set
after it. Along a block (`sites_Z`), the calls of the path have site cells apart from each other
and from the cells set at its start, all set where the block ends (`SitesG`); at joins, the cells
of either branch are kept. A part hands on what it set (`partEnd`'s `subK`), so along the body
the calls of a path have their sites apart (`sitesApart_of`).
-/

namespace LeanVM.Guest.B2C

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Exec
open LeanVM.Guest.Check LeanVM.Guest.Memory

@[expose] public section

/-- The site cells of a call: its callee frame pointer cell and, for a dispatch, its target. -/
noncomputable def siteCellsC (j : ℕ) (c : Call) : List ℕ :=
  match siteOf j c with
  | some s => s.q :: (if s.tgt = 0 then [] else [s.tgt])
  | none => []

/-- Calls whose site cells are apart from each other and unset in `u0`. -/
def SitesP (j u0 : ℕ) (cs : List Call) : Prop :=
  (∀ c ∈ cs, ∀ x ∈ siteCellsC j c, u0.testBit x = false) ∧
    cs.Pairwise fun c c' ↦ ∀ x ∈ siteCellsC j c, x ∉ siteCellsC j c'

/-- Calls whose site cells are apart, unset in `u0` and set in `u`, which holds `u0`. -/
def SitesG (j u0 : ℕ) (cs : List Call) (u : ℕ) : Prop :=
  SitesP j u0 cs ∧ (∀ c ∈ cs, ∀ x ∈ siteCellsC j c, u.testBit x = true) ∧
    ∀ x, u0.testBit x = true → u.testBit x = true

/-! ## Sets of calls -/

section Sets

variable {j : ℕ}

theorem sitesP_nil (u0 : ℕ) : SitesP j u0 [] := ⟨fun _ h ↦ (by cases h), .nil⟩

theorem sitesG_nil {u0 u : ℕ} (h : ∀ x, u0.testBit x = true → u.testBit x = true) : SitesG j u0 [] u :=
  ⟨sitesP_nil u0, fun _ h ↦ (by cases h), h⟩

theorem sitesG_mono {u0 u u' : ℕ} {cs : List Call} (hg : SitesG j u0 cs u)
    (h : ∀ x, u.testBit x = true → u'.testBit x = true) : SitesG j u0 cs u' :=
  ⟨hg.1, fun c hc x hx ↦ h x (hg.2.1 c hc x hx), fun x hx ↦ h x (hg.2.2 x hx)⟩

theorem sitesP_append {u0 u1 : ℕ} {cs1 cs2 : List Call} (h1 : SitesG j u0 cs1 u1)
    (h2 : SitesP j u1 cs2) : SitesP j u0 (cs1 ++ cs2) := by
  obtain ⟨⟨a1, p1⟩, s1, m1⟩ := h1
  obtain ⟨a2, p2⟩ := h2
  refine ⟨fun c hc x hx ↦ ?_, List.pairwise_append.mpr ⟨p1, p2, fun c hc c' hc' x hx hx' ↦ ?_⟩⟩
  · rcases List.mem_append.mp hc with hc | hc
    · exact a1 c hc x hx
    · cases h : u0.testBit x
      · rfl
      · have := a2 c hc x hx
        rw [m1 x h] at this
        cases this
  · have := a2 c' hc' x hx'
    rw [s1 c hc x hx] at this
    cases this

theorem sitesG_append {u0 u1 u2 : ℕ} {cs1 cs2 : List Call} (h1 : SitesG j u0 cs1 u1)
    (h2 : SitesG j u1 cs2 u2) : SitesG j u0 (cs1 ++ cs2) u2 := by
  refine ⟨sitesP_append h1 h2.1, fun c hc x hx ↦ ?_, fun x hx ↦ h2.2.2 x (h1.2.2 x hx)⟩
  rcases List.mem_append.mp hc with hc | hc
  · exact h2.2.2 x (h1.2.1 c hc x hx)
  · exact h2.2.1 c hc x hx

theorem sitesG_one {u0 u : ℕ} {c : Call} (h0 : ∀ x ∈ siteCellsC j c, u0.testBit x = false)
    (h1 : ∀ x ∈ siteCellsC j c, u.testBit x = true) (hm : ∀ x, u0.testBit x = true → u.testBit x = true) :
    SitesG j u0 [c] u := by
  refine ⟨⟨fun c' hc' ↦ ?_, List.pairwise_singleton _ _⟩, fun c' hc' ↦ ?_, hm⟩
  · rw [List.mem_singleton.mp hc']
    exact h0
  · rw [List.mem_singleton.mp hc']
    exact h1

theorem setK_mono (s n x : ℕ) (h : s.testBit x = true) : (setK s n).testBit x = true := by
  rw [testBit_setK, h, Bool.true_or]

theorem setK_self (s n : ℕ) : (setK s n).testBit n = true := by
  rw [testBit_setK, decide_eq_true rfl, Bool.or_true]

theorem testBit_lorC (a b x : ℕ) : (Nat.lor a b).testBit x = (a.testBit x || b.testBit x) := by
  show (a ||| b).testBit x = _
  rw [Nat.testBit_or]

theorem subK_spec {s t : ℕ} (h : subK s t = true) (x : ℕ) (hs : s.testBit x = true) :
    t.testBit x = true := by
  unfold subK at h
  have he := Nat.eq_of_beq_eq_true h
  rw [← he] at hs
  have : (s &&& t).testBit x = true := hs
  rw [Nat.testBit_and, Bool.and_eq_true] at this
  exact this.2

theorem calls_appendC (a b : List Ev) : calls (a ++ b) = calls a ++ calls b := by
  simp [calls, List.filterMap_append]

/-- A call's site cells, at a site the check accepts. -/
theorem cells_of_site {X : CX} (hX : X.sites = (plumbOf j).sites) {c : Call} {q r t : ℕ}
    (h : siteOk X c.args c.rets q r t = true) : ∀ x ∈ siteCellsC j c, x = q ∨ (t ≠ 0 ∧ x = t) := by
  obtain ⟨s, hs, hq, -, ht⟩ := siteOk_spec h
  rw [siteC_eq hX] at hs
  intro x hx
  unfold siteCellsC at hx
  rw [hs] at hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact Or.inl hq
  · split_ifs at hx with h0
    · cases hx
    · exact Or.inr ⟨ht ▸ h0, by rw [← ht]; exact List.mem_singleton.mp hx⟩

end Sets

/-! ## Along a block -/

section Walk

variable {j : ℕ} {σ : Val} {X : CX}

/-- **What the walk of a block keeps of the site cells**: on a path through it, its calls' site
cells are apart and unset at its start, and set where it joins. -/
def UGood (X : CX) (j : ℕ) (σ : Val) (ss : List Stmt) (st : CW) : Prop :=
  (cw X ss st).ok = true →
    (∀ e, walk σ ss = .fall e → ∀ J c u, (cw X ss st = .join J c u ∨ ∃ m, cw X ss st = .mid J m c u) →
      SitesG j st.uq (calls e) u) ∧
    (∀ e vs, walk σ ss = .ret e vs → SitesP j st.uq (calls e))

theorem u_step {s : Stmt} {ss : List Stmt} {st st'' : CW} {e1 : List Ev}
    (ih : UGood X j σ ss st'') (hw1 : walk1 σ s = .fall e1) (hcw : cw X (s :: ss) st = cw X ss st'')
    (hg : SitesG j st.uq (calls e1) st''.uq) : UGood X j σ (s :: ss) st := by
  intro hok
  rw [hcw] at hok
  obtain ⟨h1, h2⟩ := ih hok
  refine ⟨fun e hw J c u hj ↦ ?_, fun e vs hw ↦ ?_⟩
  · rw [walk, hw1] at hw
    cases hws : walk σ ss with
    | fall e2 =>
      rw [hws] at hw
      simp only [Out.seq, Out.pre, Out.fall.injEq] at hw
      subst hw
      rw [calls_appendC]
      exact sitesG_append hg (h1 e2 hws J c u (hcw ▸ hj))
    | ret _ _ => rw [hws] at hw; cases hw
    | stuck => rw [hws] at hw; cases hw
  · rw [walk, hw1] at hw
    cases hws : walk σ ss with
    | fall _ => rw [hws] at hw; cases hw
    | ret e2 v2 =>
      rw [hws] at hw
      simp only [Out.seq, Out.pre, Out.ret.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      rw [calls_appendC]
      exact sitesP_append hg (h2 e2 _ hws)
    | stuck => rw [hws] at hw; cases hw

theorem u_nil (st : CW) : UGood X j σ [] st := by
  intro hok
  rw [cw_nil] at hok ⊢
  refine ⟨fun e hw J c u hj ↦ ?_, fun e vs hw ↦ (by rw [walk] at hw; cases hw)⟩
  rw [walk] at hw
  cases hw
  rcases endC_ok hok with ⟨t, -, he⟩ | ⟨-, -, se, t, hse, -, -, he⟩ | ⟨-, J', m', c', -, -, -, -, -, he⟩
  · rw [he] at hj
    rcases hj with hj | ⟨m, hj⟩
    · simp only [RC.join.injEq] at hj
      obtain ⟨-, -, rfl⟩ := hj
      exact sitesG_nil fun _ h ↦ h
    · cases hj
  · rw [he] at hj
    rcases hj with hj | ⟨m, hj⟩
    · simp only [RC.join.injEq] at hj
      obtain ⟨-, -, rfl⟩ := hj
      obtain ⟨c, -, rfl⟩ := endAtC_eq hse
      exact sitesG_nil fun _ h ↦ h
    · cases hj
  · rw [he] at hj
    rcases hj with hj | ⟨m, hj⟩
    · cases hj
    · simp only [RC.mid.injEq] at hj
      obtain ⟨-, -, -, rfl⟩ := hj
      exact sitesG_nil fun _ h ↦ h

theorem u_atom (a : Core.Atom) (ss : List Stmt) (st : CW) (ih : ∀ st, UGood X j σ ss st) :
    UGood X j σ (.atom a :: ss) st :=
  u_step (ih _) rfl (cw_atom a ss st) (by
    rw [show calls [Ev.atom a] = [] from rfl]
    exact sitesG_nil fun _ h ↦ h)

theorem u_ret (vs' : List V) (ss : List Stmt) (st : CW) : UGood X j σ (.ret vs' :: ss) st := by
  intro _
  refine ⟨fun e hw ↦ (by rw [walk] at hw; cases hw), fun e vs hw ↦ ?_⟩
  rw [walk] at hw
  simp only [walk1, Out.seq, Out.ret.injEq] at hw
  rw [← hw.1]
  exact sitesP_nil _

theorem u_call (hX : X.sites = (plumbOf j).sites) (hG : X.G = glob) (f : String) (args rets : List V) (ss : List Stmt)
    (st : CW) (ih : ∀ st, UGood X j σ ss st) : UGood X j σ (.call f args rets :: ss) st := by
  intro hok
  obtain ⟨e, q, r, j', sr, -, -, -, -, -, -, -, hsite, hbit, -, -, haf, hcw⟩ := cw_call hG hok
  obtain ⟨se, s', -, -, rfl⟩ := afterC_ok haf
  have hc := cells_of_site (c := ⟨f, args, rets, true⟩) hX hsite
  refine u_step (ih _) rfl hcw ?_ hok
  refine sitesG_one (fun x hx ↦ ?_) (fun x hx ↦ ?_) (fun x hx ↦ setK_mono _ _ _ hx)
  · rcases hc x hx with rfl | ⟨h0, -⟩
    · rw [← bitK_eq]
      exact hbit
    · exact absurd rfl h0
  · rcases hc x hx with rfl | ⟨h0, -⟩
    · exact setK_self _ _
    · exact absurd rfl h0

theorem u_dispatch (hX : X.sites = (plumbOf j).sites) (v : V) (fs : List String) (args rets : List V)
    (ss : List Stmt) (st : CW) (ih : ∀ st, UGood X j σ ss st) :
    UGood X j σ (.dispatch v fs args rets :: ss) st := by
  intro hok
  obtain ⟨t, q, r, base, sr, -, -, -, -, -, -, -, hsite, hbq, hbt, -, -, -, haf, hcw⟩ := cw_dispatch hok
  obtain ⟨se, s', -, -, rfl⟩ := afterC_ok haf
  have hg : ∀ g, SitesG j st.uq (calls [Ev.call g args rets]) (setK (setK st.uq q) t) := by
    intro g
    have hc := cells_of_site (c := ⟨g, args, rets, true⟩) hX hsite
    refine sitesG_one (fun x hx ↦ ?_) (fun x hx ↦ ?_)
      (fun x hx ↦ setK_mono _ _ _ (setK_mono _ _ _ hx))
    · rcases hc x hx with rfl | ⟨-, rfl⟩
      · rw [← bitK_eq]
        exact hbq
      · rw [← bitK_eq]
        exact hbt
    · rcases hc x hx with rfl | ⟨-, rfl⟩
      · exact setK_mono _ _ _ (setK_self _ _)
      · exact setK_self _ _
  have hw1 : walk1 σ (.dispatch v fs args rets) = pick σ v args rets 0 fs := rfl
  rw [hcw] at hok
  obtain ⟨h1, h2⟩ := ih _ hok
  have hpick : ∀ o, pick σ v args rets 0 fs = o → o ≠ .stuck → ∃ g, o = .fall [Ev.call g args rets] := by
    intro o ho hs
    cases o with
    | fall e1 =>
      obtain ⟨k, hk, -, rfl⟩ := tbl_pick (σ := σ) fs 0 ho
      exact ⟨_, rfl⟩
    | ret _ _ =>
      rcases pick_noRetC (σ := σ) (x := v) (a := args) (r := rets) fs 0 with ⟨e', h⟩ | h <;> rw [h] at ho <;>
        cases ho
    | stuck => exact absurd rfl hs
  refine ⟨fun e hw J c u hj ↦ ?_, fun e vs hw ↦ ?_⟩
  · rw [walk, hw1] at hw
    by_cases hs : pick σ v args rets 0 fs = .stuck
    · rw [hs] at hw; cases hw
    obtain ⟨g, hg'⟩ := hpick _ rfl hs
    rw [hg'] at hw
    cases hws : walk σ ss with
    | fall e2 =>
      rw [hws] at hw
      simp only [Out.seq, Out.pre, Out.fall.injEq] at hw
      subst hw
      rw [calls_appendC]
      exact sitesG_append (hg g) (h1 e2 hws J c u (hcw ▸ hj))
    | ret _ _ => rw [hws] at hw; cases hw
    | stuck => rw [hws] at hw; cases hw
  · rw [walk, hw1] at hw
    by_cases hs : pick σ v args rets 0 fs = .stuck
    · rw [hs] at hw; cases hw
    obtain ⟨g, hg'⟩ := hpick _ rfl hs
    rw [hg'] at hw
    cases hws : walk σ ss with
    | fall _ => rw [hws] at hw; cases hw
    | ret e2 v2 =>
      rw [hws] at hw
      simp only [Out.seq, Out.pre, Out.ret.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      rw [calls_appendC]
      exact sitesP_append (hg g) (h2 e2 _ hws)
    | stuck => rw [hws] at hw; cases hw

theorem u_callIf (hX : X.sites = (plumbOf j).sites) (hG : X.G = glob) (c : V) (f : String) (args : List V)
    (ss : List Stmt) (st : CW) (ih : ∀ st, UGood X j σ ss st) :
    UGood X j σ (.callIf c f args :: ss) st := by
  intro hok
  obtain ⟨x, -, -, hcase⟩ := cw_callIf hG hok
  set ev : Ev := if σ c = 0 then Ev.skip f args else Ev.call f args [] with hev
  have hcalls : calls [Ev.inK c, ev] = [⟨f, args, [], !(decide (σ c = 0))⟩] := by
    have h0 : Ev.call? (Ev.inK c) = none := rfl
    have h1 : Ev.call? ev = some ⟨f, args, [], !(decide (σ c = 0))⟩ := callIf_ev c f args
    simp only [calls, List.filterMap_cons, h0, h1, List.filterMap_nil]
  rcases hcase with ⟨e, q, r, j', st', oc', od, of, x', se, t, sr, -, -, -, -, -, -, -, hsite, hbit, -,
      -, -, -, -, -, -, -, -, -, hcw⟩ |
    ⟨e, S, st', oc', od, of, x', se, -, rfl, -, -, -, -, -, -, hsn, -⟩
  · have hc := cells_of_site (c := ⟨f, args, [], !(decide (σ c = 0))⟩) hX hsite
    refine u_step (ih _) rfl hcw ?_ hok
    rw [hcalls]
    refine sitesG_one (fun y hy ↦ ?_) (fun y hy ↦ ?_) (fun y hy ↦ setK_mono _ _ _ hy)
    · rcases hc y hy with rfl | ⟨h0, -⟩
      · rw [← bitK_eq]
        exact hbit
      · exact absurd rfl h0
    · rcases hc y hy with rfl | ⟨h0, -⟩
      · exact setK_self _ _
      · exact absurd rfl h0
  · have hnil : siteCellsC j ⟨f, args, [], !(decide (σ c = 0))⟩ = [] := by
      unfold siteCellsC
      rw [← siteC_eq hX]
      simp only [hsn]
    have hw : walk σ [Stmt.callIf c f args, .ret []] = .ret [Ev.inK c, ev] [] := rfl
    refine ⟨fun e' hw' ↦ (by rw [hw] at hw'; cases hw'), fun e' vs hw' ↦ ?_⟩
    rw [hw] at hw'
    simp only [Out.ret.injEq] at hw'
    rw [← hw'.1, hcalls]
    refine ⟨fun c' hc' y hy ↦ ?_, List.pairwise_singleton _ _⟩
    rw [List.mem_singleton.mp hc', hnil] at hy
    cases hy

theorem cwArms_u {J : ℕ} {se : CW} {key : Option (List Cnt)} :
    ∀ {as : List (List Core.Stmt)} {ts : List ℕ} {c : Cnt} {u : ℕ} {i : ℕ}
    {c' : Cnt} {u' : ℕ}, cwArms X J se key as ts c u i = some (c', u') →
    (∀ x, u.testBit x = true → u'.testBit x = true) ∧
    ∀ k (hk : k < as.length) (hk' : k < ts.length) s ck uk, segAtC X ts[k] se = some s →
      cw X as[k] { s with book := fileB X.loc X.fs as[k] se.book } = .join J ck uk →
      ∀ x, uk.testBit x = true → u'.testBit x = true
  | [], [], c, u, _, c', u', h => by
    simp only [cwArms, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨fun _ h ↦ h, fun k hk ↦ absurd hk (Nat.not_lt_zero _)⟩
  | a :: as, t :: ts, c, u, i, c', u', h => by
    simp only [cwArms] at h
    split at h
    · rename_i s hs
      simp only [Trie.seq_eq] at h
      split at h
      · rename_i J' ca ua hca
        cases hJ : (Nat.beq J J' && armChkK key i ca)
        · rw [hJ] at h; cases h
        rw [hJ] at h
        simp only [Bool.and_eq_true] at hJ
        obtain rfl := Nat.eq_of_beq_eq_true hJ.1
        simp only [Bool.cond_true, Cnt.seq_eq, natSeq_eq] at h
        obtain ⟨hu, hk⟩ := cwArms_u h
        refine ⟨fun x hx ↦ hu x (by rw [testBit_lorC, hx, Bool.true_or]), fun k hk1 hk2 s' ck uk hs' hck ↦ ?_⟩
        cases k with
        | zero =>
          simp only [List.getElem_cons_zero] at hs' hck
          rw [hs] at hs'
          obtain rfl := Option.some.inj hs'
          rw [hca] at hck
          simp only [RC.join.injEq] at hck
          obtain ⟨-, -, rfl⟩ := hck
          exact fun x hx ↦ hu x (by rw [testBit_lorC, hx, Bool.or_true])
        | succ k =>
          exact hk k (by simpa using hk1) (by simpa using hk2) s' ck uk hs' hck
      · cases h
    · cases h
  | [], _ :: _, _, _, _, _, _, h => by simp [cwArms] at h
  | _ :: _, [], _, _, _, _, _, h => by simp [cwArms] at h

theorem armSt_uq (key : Option (List Cnt)) (se : CW) : (armSt key se).uq = se.uq := by
  cases key <;> rfl

theorem walkArms_some {x : V} : ∀ (arms : List (List Stmt)) (i : ℕ) {o : Out},
    walkArms σ x i arms = o → o ≠ .stuck → ∃ k, ∃ hk : k < arms.length, walk σ arms[k] = o
  | [], _, _, h, hs => by simp [walkArms] at h; exact absurd h.symm hs
  | a :: as, i, o, h, hs => by
    unfold walkArms at h
    split_ifs at h
    · exact ⟨0, by simp, h⟩
    · obtain ⟨k, hk, h2⟩ := walkArms_some as (i + 1) h hs
      exact ⟨k + 1, by simpa using hk, by rw [List.getElem_cons_succ]; exact h2⟩

theorem u_ite (c : V) (z n ss : List Stmt) (st : CW) (ihz : ∀ st, UGood X j σ z st)
    (ihn : ∀ st, UGood X j σ n st) (ih : ∀ st, UGood X j σ ss st) :
    UGood X j σ (.ite c z n :: ss) st := by
  intro hok
  obtain ⟨st', od, of, x, t, sn, J, c1, u1, c2, u2, sj, hb, -, -, -, -, -, hsn, hz, hn, hsj, hcw⟩ :=
    cw_ite hok
  obtain ⟨its, cc, -, rfl⟩ := brAtC_eq hb
  obtain ⟨s1, -, -, rfl⟩ := segAtC_eq hsn
  obtain ⟨s2, -, -, rfl⟩ := segAtC_eq hsj
  have hz' := ihz _ (by rw [hz]; rfl)
  have hn' := ihn _ (by rw [hn]; rfl)
  set wb := if σ c = 0 then walk σ z else walk σ n with hwb
  have hbr : (∀ eb, wb = .fall eb → SitesG j st.uq (calls eb) (Nat.lor u1 u2)) ∧
      ∀ eb vb, wb = .ret eb vb → SitesP j st.uq (calls eb) := by
    by_cases h0 : σ c = 0
    · simp only [hwb, h0, ↓reduceIte]
      exact ⟨fun eb hw ↦ sitesG_mono (hz'.1 eb hw J c1 u1 (Or.inl hz))
        (fun y hy ↦ by rw [testBit_lorC, hy, Bool.true_or]), fun eb vb hw ↦ hz'.2 eb vb hw⟩
    · simp only [hwb, h0, ↓reduceIte]
      exact ⟨fun eb hw ↦ sitesG_mono (hn'.1 eb hw J c2 u2 (Or.inl hn))
        (fun y hy ↦ by rw [testBit_lorC, hy, Bool.or_true]), fun eb vb hw ↦ hn'.2 eb vb hw⟩
  have hw1 : walk1 σ (.ite c z n) = wb.pre [.inK c] := rfl
  have hci : ∀ eb, calls ([Ev.inK c] ++ eb) = calls eb := fun eb ↦ by rw [calls_appendC]; rfl
  cases hwbo : wb with
  | fall eb =>
    refine u_step (ih _) (by rw [hw1, hwbo]; rfl) hcw ?_ hok
    rw [hci]
    exact hbr.1 eb hwbo
  | ret eb vb =>
    refine ⟨fun e hw ↦ (by rw [walk, hw1, hwbo] at hw; cases hw), fun e vs hw ↦ ?_⟩
    rw [walk, hw1, hwbo] at hw
    simp only [Out.pre, Out.seq, Out.ret.injEq] at hw
    rw [← hw.1, hci]
    exact hbr.2 eb vb hwbo
  | stuck =>
    refine ⟨fun e hw ↦ (by rw [walk, hw1, hwbo] at hw; cases hw), fun e vs hw ↦ ?_⟩
    rw [walk, hw1, hwbo] at hw
    cases hw

theorem u_match (v : V) (a0 : List Stmt) (as : List (List Stmt)) (ss : List Stmt) (st : CW)
    (iha : ∀ k (hk : k < (a0 :: as).length) st, UGood X j σ (a0 :: as)[k] st)
    (ih : ∀ st, UGood X j σ ss st) : UGood X j σ (.match_ v (a0 :: as) :: ss) st := by
  intro hok
  obtain ⟨t, ft, t0, ts, base, se, s0, J, c0, u0, c, u, sj, -, -, -, -, hl, -, -, -, -, -, hse, hs0,
    h0, -, ha, hsj, hcw⟩ := cw_match hok
  obtain ⟨cse, -, rfl⟩ := endAtC_eq hse
  obtain ⟨s2, -, -, rfl⟩ := segAtC_eq hsj
  obtain ⟨hl', -, hks⟩ := cwArms_spec ha
  obtain ⟨hu0, huk⟩ := cwArms_u ha
  -- each arm's walk, from its segment, keeps the cells apart and joins within `u`
  have harm : ∀ k (hk : k < (a0 :: as).length),
      (∀ eb, walk σ (a0 :: as)[k] = .fall eb → SitesG j st.uq (calls eb) u) ∧
      ∀ eb vb, walk σ (a0 :: as)[k] = .ret eb vb → SitesP j st.uq (calls eb) := by
    intro k hk
    cases k with
    | zero =>
      obtain ⟨s1, -, -, rfl⟩ := segAtC_eq hs0
      have := iha 0 hk _ (by simp only [List.getElem_cons_zero]; rw [h0]; rfl)
      simp only [List.getElem_cons_zero] at this ⊢
      refine ⟨fun eb hw ↦ sitesG_mono ?_ hu0, fun eb vb hw ↦ ?_⟩
      · have r := this.1 eb hw J c0 u0 (Or.inl h0)
        simpa only [armSt_uq] using r
      · have r := this.2 eb vb hw
        simpa only [armSt_uq] using r
    | succ k =>
      have hk1 : k < as.length := by simpa using hk
      obtain ⟨s, ck, uk, hs, hck, -, -⟩ := hks k hk1 (by omega)
      obtain ⟨s1, -, -, rfl⟩ := segAtC_eq hs
      have := iha (k + 1) hk _ (by simp only [List.getElem_cons_succ]; rw [hck]; rfl)
      simp only [List.getElem_cons_succ] at this ⊢
      refine ⟨fun eb hw ↦ sitesG_mono ?_ (huk k hk1 (by omega) _ ck uk hs hck), fun eb vb hw ↦ ?_⟩
      · have r := this.1 eb hw J ck uk (Or.inl hck)
        simpa only [armSt_uq] using r
      · have r := this.2 eb vb hw
        simpa only [armSt_uq] using r
  have hw1 : walk1 σ (.match_ v (a0 :: as)) = walkArms σ v 0 (a0 :: as) := rfl
  cases hwa : walkArms σ v 0 (a0 :: as) with
  | fall eb =>
    obtain ⟨k, hk, hwk⟩ := walkArms_some (σ := σ) (a0 :: as) 0 hwa (fun h ↦ by cases h)
    exact u_step (ih _) (by rw [hw1, hwa]) hcw ((harm k hk).1 eb hwk) hok
  | ret eb vb =>
    obtain ⟨k, hk, hwk⟩ := walkArms_some (σ := σ) (a0 :: as) 0 hwa (fun h ↦ by cases h)
    refine ⟨fun e hw ↦ (by rw [walk, hw1, hwa] at hw; cases hw), fun e vs hw ↦ ?_⟩
    rw [walk, hw1, hwa] at hw
    simp only [Out.seq, Out.ret.injEq] at hw
    rw [← hw.1]
    exact (harm k hk).2 eb vb hwk
  | stuck =>
    refine ⟨fun e hw ↦ (by rw [walk, hw1, hwa] at hw; cases hw), fun e vs hw ↦ ?_⟩
    rw [walk, hw1, hwa] at hw
    cases hw

mutual
/-- **The walk keeps the site cells apart**, for every block and position. -/
theorem sites_Z (hX : X.sites = (plumbOf j).sites) (hG : X.G = glob) : ∀ (ss : List Stmt) (st : CW), UGood X j σ ss st
  | [], st => u_nil st
  | .atom a :: ss, st => u_atom a ss st (sites_Z hX hG ss)
  | .ite c z n :: ss, st => u_ite c z n ss st (sites_Z hX hG z) (sites_Z hX hG n) (sites_Z hX hG ss)
  | .match_ v [] :: ss, st => fun hok ↦ by simp [cw, RC.ok] at hok
  | .match_ v (a0 :: as) :: ss, st => u_match v a0 as ss st (sites_armsZ hX hG (a0 :: as)) (sites_Z hX hG ss)
  | .call f args rets :: ss, st => u_call hX hG f args rets ss st (sites_Z hX hG ss)
  | .callIf c f args :: ss, st => u_callIf hX hG c f args ss st (sites_Z hX hG ss)
  | .dispatch v fs args rets :: ss, st => u_dispatch hX v fs args rets ss st (sites_Z hX hG ss)
  | .ret vs' :: ss, st => u_ret vs' ss st

theorem sites_armsZ (hX : X.sites = (plumbOf j).sites) (hG : X.G = glob) :
    ∀ (arms : List (List Stmt)) (k : ℕ) (hk : k < arms.length) (st : CW), UGood X j σ arms[k] st
  | [], _, hk, _ => absurd hk (Nat.not_lt_zero _)
  | a :: _, 0, _, st => sites_Z hX hG a st
  | _ :: as, k + 1, hk, st => sites_armsZ hX hG as k (by simpa using hk) st
end

end Walk

/-! ## Along the body -/

/-- Calls whose site cells are apart have distinct sites. -/
theorem sitesApart_of_P {j u : ℕ} {es : List Ev} (h : SitesP j u (calls es)) : SitesApart j es := by
  intro i i' c c' s s' hne hc hc' hs hs'
  have hdis : ∀ x, x ∈ siteCellsC j c → x ∈ siteCellsC j c' → False := by
    intro x hx hx'
    obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp hc
    obtain ⟨hi', rfl⟩ := List.getElem?_eq_some_iff.mp hc'
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · exact List.pairwise_iff_getElem.mp h.2 i i' hi hi' hlt x hx hx'
    · exact List.pairwise_iff_getElem.mp h.2 i' i hi' hi hlt x hx' hx
  have hq : s.q ∈ siteCellsC j c := by unfold siteCellsC; rw [hs]; exact List.mem_cons_self
  have hq' : s'.q ∈ siteCellsC j c' := by unfold siteCellsC; rw [hs']; exact List.mem_cons_self
  have ht : s.tgt ≠ 0 → s.tgt ∈ siteCellsC j c := fun h0 ↦ by
    unfold siteCellsC
    simp [hs, h0]
  refine ⟨fun he ↦ hdis _ hq (he ▸ hq'), fun h0 ↦ ⟨fun he ↦ ?_, fun he ↦ hdis _ (ht h0) (he ▸ hq')⟩⟩
  have ht' : s'.tgt ∈ siteCellsC j c' := by
    unfold siteCellsC
    simp [hs', show s'.tgt ≠ 0 from he ▸ h0]
  exact hdis _ (ht h0) (he ▸ ht')

/-- **The call sites of a path through a function the check accepts are apart.** -/
theorem sitesApart_of {j : ℕ} (hok : CplOk j)
    (hchk : ∀ i ≤ (certOf j).cuts.length,
      checkWin glob (fnOf j) (coreOf j) (certOf j) (j == 1) i = true)
    {σ : Val} {es : List Ev} {vs : List V} (hw : walk σ (coreOf j).body = .ret es vs) :
    SitesApart j es := by
  have parts : ∀ i ≤ (certOf j).cuts.length,
      (i < (certOf j).cuts.length → ∀ e, walk σ ((coreOf j).body.drop (partPos j (i + 1) 0)) = .ret e vs →
        SitesP j (partU j (i + 1) 0) (calls e)) →
      ∀ m k, nParts j i - k = m → k < nParts j i →
        ∀ e, walk σ ((coreOf j).body.drop (partPos j i k)) = .ret e vs → SitesP j (partU j i k) (calls e) := by
    intro i hi hnext m
    induction m with
    | zero => intro k hm hk; omega
    | succ m ih =>
      intro k hm hk e he
      have hc := hok i hi
      have hsplit := part_split hk (fun h ↦ ((checkWin_cpl (hchk i hi)).2.2.2.2 h).1) hc
      have hend := cplWin_end (hc k hk)
      obtain ⟨s, -, -, hres⟩ := cplRes_some hend
      have hU := sites_Z (σ := σ) (X := Xp j i k) (j := j) rfl rfl (partStmts j i k) (st0 j i k s)
        (cw_ok_of hres hend)
      unfold partPos at he
      rw [hsplit, walk_appendC] at he
      -- a part before the last: it joins within what the next part starts with
      have hmid : lastPart j i k = false → ∀ i' k', nextPos j i k = partPos j i' k' →
          (∀ J c u, (cplRes j i k = .join J c u ∨ ∃ m, cplRes j i k = .mid J m c u) →
            subK u (partU j i' k') = true) →
          (∀ e, walk σ ((coreOf j).body.drop (partPos j i' k')) = .ret e vs →
            SitesP j (partU j i' k') (calls e)) → SitesP j (partU j i k) (calls e) := by
        intro hlp i' k' hnx hsub hih
        rcases walk_noRetC _ (cplWin_mid (hc k hk) hlp) with ⟨e1, hw1⟩ | hw1
        · rw [hw1] at he
          obtain ⟨e2, hw2, rfl⟩ := seq_fall_ret he
          rw [hnx] at hw2
          rcases hcr : cplRes j i k with ⟨J, c, u⟩ | ⟨J, m, c, u⟩ | _ | e
          · have hg := hU.1 e1 hw1 J c u (Or.inl (hres.symm.trans hcr))
            rw [calls_appendC]
            exact sitesP_append (sitesG_mono hg (subK_spec (hsub J c u (Or.inl hcr)))) (hih e2 hw2)
          · have hg := hU.1 e1 hw1 J c u (Or.inr ⟨m, hres.symm.trans hcr⟩)
            rw [calls_appendC]
            exact sitesP_append (sitesG_mono hg (subK_spec (hsub J c u (Or.inr ⟨m, hcr⟩)))) (hih e2 hw2)
          · rw [hcr] at hend
            have hl : lastPart j i k = true := hend
            rw [hl] at hlp
            cases hlp
          · rw [hcr] at hend
            simp [partEnd] at hend
        · rw [hw1] at he
          cases he
      by_cases hn : k + 1 < nParts j i
      · have hb : Nat.blt (k + 1) (nParts j i) = true := Nat.blt_eq.mpr hn
        refine hmid (by simp only [lastPart, hb]; rfl) i (k + 1) (by unfold nextPos; rw [hb]; rfl)
          (fun J c u hcr ↦ ?_) (ih (k + 1) (by omega) hn)
        rcases hcr with hcr | ⟨m, hcr⟩
        · rw [hcr] at hend
          simp only [partEnd, hb, Bool.cond_true, Bool.and_eq_true] at hend
          exact hend.2
        · rw [hcr] at hend
          simp only [partEnd, Bool.and_eq_true] at hend
          exact hend.2
      · by_cases hci : i < (certOf j).cuts.length
        · have hbi : Nat.blt i (certOf j).cuts.length = true := Nat.blt_eq.mpr hci
          refine hmid (by simp only [lastPart, blt_falseC hn, hbi]; rfl) (i + 1) 0 ?_
            (fun J c u hcr ↦ ?_) (hnext hci)
          · unfold nextPos partPos
            rw [blt_falseC hn, hbi, partS_zero (hok (i + 1) hci 0 (one_le_nParts j (i + 1)))]
            rfl
          · rcases hcr with hcr | ⟨m, hcr⟩
            · rw [hcr] at hend
              simp only [partEnd, blt_falseC hn, hbi, Bool.cond_false, Bool.true_and,
                Bool.and_eq_true] at hend
              exact hend.2
            · rw [hcr] at hend
              simp only [partEnd, blt_falseC hn, Bool.false_and] at hend
              cases hend
        · have hlp : lastPart j i k = true := by
            simp only [lastPart, blt_falseC hn, blt_falseC hci]
            rfl
          have hnx : nextPos j i k = (coreOf j).body.length := by
            unfold nextPos
            rw [blt_falseC hn, blt_falseC hci]
            rfl
          rw [hnx, List.drop_length] at he
          have hw0 : walk σ ([] : List Stmt) = .fall [] := rfl
          rw [hw0] at he
          cases hwp : walk σ (partStmts j i k) with
          | fall _ => rw [hwp] at he; simp [Out.seq, Out.pre] at he
          | ret e1 v1 =>
            rw [hwp] at he
            simp only [Out.seq, Out.ret.injEq] at he
            obtain ⟨rfl, rfl⟩ := he
            exact hU.2 e1 _ hwp
          | stuck => rw [hwp] at he; cases he
  have wins : ∀ m i, (certOf j).cuts.length - i = m → i ≤ (certOf j).cuts.length →
      ∀ e, walk σ ((coreOf j).body.drop (partPos j i 0)) = .ret e vs → SitesP j (partU j i 0) (calls e) := by
    intro m
    induction m with
    | zero =>
      intro i hm hi
      exact parts i hi (fun h ↦ by omega) _ 0 rfl (one_le_nParts j i)
    | succ m ih =>
      intro i hm hi
      exact parts i hi (fun h ↦ ih (i + 1) (by omega) h) _ 0 rfl (one_le_nParts j i)
  refine sitesApart_of_P (wins _ 0 rfl (Nat.zero_le _) es ?_)
  rw [partPos, partS_zero (hok 0 (Nat.zero_le _) 0 (one_le_nParts j 0))]
  exact hw

end
end LeanVM.Guest.B2C
