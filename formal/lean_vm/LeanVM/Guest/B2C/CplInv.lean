/-
  LeanVM.Guest.B2C.CplInv

  Inverting the completeness walk: what a statement's step of `cw` checked when the walk does not
  fail.
-/

module

public import LeanVM.Guest.B2C.Cpl

/-!
# Inverting the walk

`RC.ok r` says the walk did not fail. For each statement, `cw_*` lists what a step that did not
fail checked and where the walk goes on.
-/

namespace LeanVM.Guest.B2C

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Exec
open LeanVM.Guest.Check

@[expose] public section

/-- The walk did not fail. -/
def RC.ok : RC → Bool
  | .fail _ => false
  | _ => true

section Inv

variable {X : CX}

theorem cw_nil (st : CW) : cw X [] st = endC X st := by simp [cw]

theorem cw_atom (a : Core.Atom) (ss : List Core.Stmt) (st : CW) :
    cw X (.atom a :: ss) st = cw X ss ⟨st.seg, st.its, st.book, st.fr, st.tg, st.nx, st.cnt, st.uq, none⟩ := by
  simp [cw]

theorem endC_ok {st : CW} (h : (endC X st).ok = true) :
    (∃ t, st.fresh = some t ∧ endC X st = .join t st.cnt st.uq) ∨
    (st.fresh = none ∧ ∃ se t, endAtC X st = .ok se ∧ se.seg.exit.kind = .next t ∧
      se.seg.exit.succ = [t] ∧ endC X st = .join t se.cnt se.uq) := by
  rcases hf : st.fresh with _ | t
  · rcases he : endAtC X st with e | se
    · simp [endC, hf, he, RC.ok] at h
    · rcases hk : se.seg.exit.kind with t | _ | _ | _ <;>
        simp only [endC, hf, he, hk, RC.ok, Bool.false_eq_true] at h
      cases hs : se.seg.exit.succ == [t]
      · simp [hs] at h
      · refine Or.inr ⟨rfl, se, t, rfl, hk, beq_iff_eq.mp hs, ?_⟩
        simp only [endC, hf, he, hk, hs, Bool.cond_true]
  · exact Or.inl ⟨t, rfl, by simp only [endC, hf]⟩

theorem cw_ite {c : V} {z n ss : List Core.Stmt} {st : CW}
    (h : (cw X (.ite c z n :: ss) st).ok = true) :
    ∃ st' od of x t sn J c1 u1 c2 u2 sj, brAtC X st = .ok (st', X.loc.cell c, od, of, x) ∧
      x.kind = .next t ∧ inFrame X.fs [X.loc.cell c] = true ∧ cellK X st' od = true ∧
      cellK X st' of = true ∧ x.succ = [t] ∧ segAtC X t st' = some sn ∧
      cw X z { st' with book := fileB X.loc X.fs z st'.book } = .join J c1 u1 ∧
      cw X n { sn with book := fileB X.loc X.fs n st'.book } = .join J c2 u2 ∧
      segAtC X J st' = some sj ∧
      cw X (.ite c z n :: ss) st = cw X ss { sj with cnt := Cnt.max c1 c2, uq := Nat.lor u1 u2 } := by
  simp only [cw] at h ⊢
  split at h
  · rename_i st' oc od of x hb
    rw [hb]
    split at h
    · rename_i t hk
      cases hc : (Nat.beq oc (X.loc.cell c) && inFrame X.fs [oc] && cellK X st' od &&
          cellK X st' of && x.succ == [t])
      · rw [hc] at h; cases h
      rw [hc] at h
      simp only [Bool.cond_true]
      simp only [Bool.cond_true] at h
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨⟨⟨⟨hoc, hfr⟩, hod⟩, hof⟩, hsu⟩ := hc
      obtain rfl := Nat.eq_of_beq_eq_true hoc
      split at h
      · rename_i sn hsn
        simp only [Trie.seq_eq] at h ⊢
        split at h
        · rename_i J c1 u1 J' c2 u2 h1 h2
          cases hJ : Nat.beq J J'
          · rw [hJ] at h; cases h
          rw [hJ] at h
          obtain rfl := Nat.eq_of_beq_eq_true hJ
          simp only [Bool.cond_true] at h
          split at h
          · rename_i sj hsj
            refine ⟨st', od, of, x, t, sn, J, c1, u1, c2, u2, sj, rfl, hk, hfr, hod, hof, hsu, hsn,
              h1, h2, hsj, ?_⟩
            simp only [Bool.cond_true, Cnt.seq_eq, natSeq_eq]
          · cases h
        · cases h
        · cases h
        · cases h
      · cases h
    · cases h
  · cases h

theorem afterC_ok {st sr : CW} {q r u : ℕ} {fcs : List (ℕ × FC)} {args rets : List V}
    (h : afterC X st q r u fcs args rets = .ok sr) :
    ∃ se s, endAtC X { st with fr := (q, fcs) :: st.fr } = .ok se ∧ segAtC X (r - X.entry) se = some s ∧
      sr = ⟨s.seg, s.its, s.book, (q, fcs ++ argFC X.loc (2 + args.length) rets) :: st.fr, s.tg, s.nx,
        s.cnt, u, bif rets.isEmpty then s.fresh else none⟩ := by
  unfold afterC at h
  split at h
  · rename_i se hse
    split at h
    · rename_i s hs
      exact ⟨se, s, hse, hs, (Except.ok.inj h).symm⟩
    · cases h
  · cases h

theorem cw_call {f : String} {args rets : List V} {ss : List Core.Stmt} {st : CW}
    (h : (cw X (.call f args rets :: ss) st).ok = true) :
    ∃ e q r j sr, st.seg.exit.kind = .call (.gp e) q r ∧ calleeC X e = some j ∧
      f = (X.G.sig j).name ∧ args.length = (X.G.sig j).nargs ∧ rets.length = (X.G.sig j).nret ∧
      X.entry ≤ r ∧ st.seg.exit.succ = [r - X.entry] ∧ siteOk X args rets q r 0 = true ∧
      bitK st.uq q = false ∧ inFrame X.fs (q :: (args ++ rets).map X.loc.cell) = true ∧ f ≠ X.name ∧
      afterC X st q r (setK st.uq q) (callFC X args ((X.G.sig j).env.map (·.1)) r) args rets = .ok sr ∧
      cw X (.call f args rets :: ss) st = cw X ss sr := by
  simp only [cw] at h ⊢
  split at h
  · rename_i e q r hk
    split at h
    · rename_i j hj
      cases hc : (f == (X.G.sig j).name && Nat.beq args.length (X.G.sig j).nargs &&
          Nat.beq rets.length (X.G.sig j).nret && Nat.ble X.entry r &&
          st.seg.exit.succ == [r - X.entry] && siteOk X args rets q r 0 && !bitK st.uq q &&
          inFrame X.fs (q :: (args ++ rets).map X.loc.cell) && !(f == X.name))
      · rw [hc] at h; cases h
      rw [hc] at h
      simp only [Bool.cond_true] at h ⊢
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := hc
      split at h
      · rename_i sr hsr
        exact ⟨e, q, r, j, sr, hk, hj, h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3,
          Nat.le_of_ble_eq_true h4, h5, h6, h7, h8, (by simpa using h9), hsr, rfl⟩
      · cases h
    · cases h
  · cases h

theorem cw_dispatch {v : V} {fs : List String} {args rets : List V} {ss : List Core.Stmt} {st : CW}
    (h : (cw X (.dispatch v fs args rets :: ss) st).ok = true) :
    ∃ t q r base sr, st.seg.exit.kind = .call (.cell t) q r ∧ tblRead t st.its = some (X.loc.cell v, base) ∧
      v = V.n v.idx ∧ selOk X v = true ∧
      tcOk X base args.length rets.length 0 fs = true ∧ X.entry ≤ r ∧
      st.seg.exit.succ = [r - X.entry] ∧ siteOk X args rets q r t = true ∧
      bitK st.uq q = false ∧ bitK st.uq t = false ∧ q ≠ t ∧
      inFrame X.fs (t :: q :: X.loc.cell v :: (args ++ rets).map X.loc.cell) = true ∧
      (∀ g ∈ fs, g ≠ X.name) ∧
      afterC X { st with tg := (t, X.loc.cell v, base) :: st.tg } q r (setK (setK st.uq q) t)
        (callFC X args [] r) args rets = .ok sr ∧
      cw X (.dispatch v fs args rets :: ss) st = cw X ss sr := by
  simp only [cw] at h ⊢
  split at h
  · rename_i t q r hk
    split at h
    · rename_i o1 base htb
      cases hc : (Nat.beq o1 (X.loc.cell v) && v.path.isEmpty && Nat.beq v.tag 0 && selOk X v &&
          tcOk X base args.length rets.length 0 fs &&
          Nat.ble X.entry r && st.seg.exit.succ == [r - X.entry] && siteOk X args rets q r t &&
          !bitK st.uq q && !bitK st.uq t && !Nat.beq q t &&
          inFrame X.fs (t :: q :: o1 :: (args ++ rets).map X.loc.cell) &&
          fs.all (fun g ↦ !(g == X.name)))
      · rw [hc] at h; cases h
      rw [hc] at h
      simp only [Bool.cond_true] at h ⊢
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, hp1⟩, hp2⟩, hp3⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := hc
      obtain rfl := Nat.eq_of_beq_eq_true h1
      have hvn : v = V.n v.idx := by
        obtain ⟨vp, vt, vi⟩ := v
        simp only [List.isEmpty_iff] at hp1
        obtain rfl := hp1
        obtain rfl := Nat.eq_of_beq_eq_true hp2
        rfl
      split at h
      · rename_i sr hsr
        exact ⟨t, q, r, base, sr, hk, htb, hvn, hp3, h2, Nat.le_of_ble_eq_true h3, h4, h5, h6, h7,
          Nat.ne_of_beq_eq_false h8, h9, fun g hg ↦ (by simpa using List.all_eq_true.mp h10 g hg), hsr, rfl⟩
      · cases h
    · cases h
  · cases h

theorem cw_ret {vs : List V} {ss : List Core.Stmt} {st : CW}
    (h : (cw X (.ret vs :: ss) st).ok = true) :
    ∃ se, endAtC X st = .ok se ∧
      (if X.main = true then se.seg.exit.kind = .jump (.gp (2 ^ 18 - 1)) (.gp 0)
        else se.seg.exit.kind = .ret) ∧ se.cnt.le X.pmax = true ∧ vs.length = X.nret ∧
      runCells (2 + X.nargs) (vs.map X.loc.cell) = true ∧ inFrame X.fs (vs.map X.loc.cell) = true ∧
      cw X (.ret vs :: ss) st = .done := by
  simp only [cw] at h ⊢
  split at h
  · rename_i se hse
    cases hc : ((bif X.main then decide (se.seg.exit.kind = .jump (.gp (2 ^ 18 - 1)) (.gp 0))
          else decide (se.seg.exit.kind = .ret)) && se.cnt.le X.pmax &&
        Nat.beq vs.length X.nret && runCells (2 + X.nargs) (vs.map X.loc.cell) &&
        inFrame X.fs (vs.map X.loc.cell))
    · rw [hc] at h; cases h
    simp only [Bool.and_eq_true] at hc
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hc
    refine ⟨se, hse, ?_, h2, Nat.eq_of_beq_eq_true h3, h4, h5, rfl⟩
    cases hm : X.main
    · rw [hm] at h1; exact of_decide_eq_true h1
    · rw [hm] at h1; exact of_decide_eq_true h1
  · cases h

theorem cw_callIf {c : V} {f : String} {args : List V} {ss : List Core.Stmt} {st : CW}
    (h : (cw X (.callIf c f args :: ss) st).ok = true) :
    ∃ x, peekBr st.its = some (X.loc.cell c, x) ∧
      inFrame X.fs (X.loc.cell c :: args.map X.loc.cell) = true ∧
    ((∃ e q r j st' oc' od of x' se t sr, x.kind = .call (.gp e) q r ∧ calleeC X e = some j ∧
        f = (X.G.sig j).name ∧ args.length = (X.G.sig j).nargs ∧ (X.G.sig j).nret = 0 ∧
        X.entry ≤ r ∧ x.succ = [r - X.entry] ∧ siteOk X args [] q r 0 = true ∧
        bitK st.uq q = false ∧ inFrame X.fs [q] = true ∧ f ≠ X.name ∧
        brAtC X { st with fr := (q, callFC X args ((X.G.sig j).env.map (·.1)) r) :: st.fr } =
          .ok (st', oc', od, of, x') ∧ cellK X st' od = true ∧ cellK X st' of = true ∧
        endAtC X st' = .ok se ∧ se.seg.exit.kind = .next t ∧ t = r - X.entry ∧
        se.seg.exit.succ = [t] ∧ segAtC X t st' = some sr ∧
        cw X (.callIf c f args :: ss) st =
          cw X ss { sr with cnt := Cnt.max se.cnt st'.cnt, uq := setK st.uq q }) ∨
     (∃ e S st' oc' od of x' se, x.kind = .jump (.gp e) (.fpg S) ∧ ss = [.ret []] ∧ e = X.entry ∧
        f = X.name ∧ S = X.fs ∧ args.length = X.nargs ∧ X.nret = 0 ∧ X.main = false ∧
        siteC X args [] = none ∧ brAtC X { st with nx := (argFC X.loc 2 args ++ [(0, .hdr 0), (1, .hdr 1)] ++
          X.self.map (fun o ↦ (o, FC.self))) } = .ok (st', oc', od, of, x') ∧
        cellK X st' od = true ∧ cellK X st' of = true ∧ st'.cnt.le X.pmax = true ∧
        endAtC X st' = .ok se ∧ se.seg.exit.kind = .ret ∧ se.cnt.le X.pmax = true ∧
        cw X (.callIf c f args :: ss) st = .done)) := by
  simp only [cw] at h ⊢
  split at h
  · rename_i oc x hp
    cases hc : (Nat.beq oc (X.loc.cell c) && inFrame X.fs (oc :: args.map X.loc.cell))
    · rw [hc] at h; cases h
    rw [hc] at h
    simp only [Bool.cond_true] at h ⊢
    simp only [Bool.and_eq_true] at hc
    obtain ⟨h1, h2⟩ := hc
    obtain rfl := Nat.eq_of_beq_eq_true h1
    refine ⟨x, hp, h2, ?_⟩
    split at h
    · rename_i e q r hk
      left
      split at h
      · rename_i j hj
        cases hc : (f == (X.G.sig j).name && Nat.beq args.length (X.G.sig j).nargs &&
            Nat.beq (X.G.sig j).nret 0 && Nat.ble X.entry r && x.succ == [r - X.entry] &&
            siteOk X args [] q r 0 && !bitK st.uq q && inFrame X.fs [q] && !(f == X.name))
        · rw [hc] at h; cases h
        rw [hc] at h
        simp only [Bool.cond_true] at h ⊢
        simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
        obtain ⟨⟨⟨⟨⟨⟨⟨⟨g1, g2⟩, g3⟩, g4⟩, g5⟩, g6⟩, g7⟩, g8⟩, g9⟩ := hc
        split at h
        · rename_i st' oc' od of x' hb
          cases hk2 : (cellK X st' od && cellK X st' of)
          · rw [hk2] at h; cases h
          rw [hk2] at h
          simp only [Bool.cond_true] at h ⊢
          simp only [Bool.and_eq_true] at hk2
          split at h
          · rename_i se hse
            split at h
            · rename_i t ht
              cases hk3 : (Nat.beq t (r - X.entry) && se.seg.exit.succ == [t])
              · rw [hk3] at h; cases h
              rw [hk3] at h
              simp only [Bool.cond_true] at h ⊢
              simp only [Bool.and_eq_true, beq_iff_eq] at hk3
              split at h
              · rename_i sr hsr
                exact ⟨e, q, r, j, st', oc', od, of, x', se, t, sr, hk, hj, g1,
                  Nat.eq_of_beq_eq_true g2, Nat.eq_of_beq_eq_true g3, Nat.le_of_ble_eq_true g4,
                  g5, g6, g7, g8, by simpa using g9, hb, hk2.1, hk2.2, hse, ht,
                  Nat.eq_of_beq_eq_true hk3.1, hk3.2,
                  hsr, by simp only [Cnt.seq_eq, natSeq_eq]⟩
              · cases h
            · cases h
          · cases h
        · cases h
      · cases h
    · rename_i e S hk
      right
      split at h
      · cases hc : (Nat.beq e X.entry && f == X.name && Nat.beq S X.fs &&
            Nat.beq args.length X.nargs && Nat.beq X.nret 0 && !X.main && (siteC X args []).isNone)
        · rw [hc] at h; cases h
        rw [hc] at h
        simp only [Bool.cond_true] at h ⊢
        simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
        obtain ⟨⟨⟨⟨⟨⟨g1, g2⟩, g3⟩, g4⟩, g5⟩, g6⟩, g10⟩ := hc
        split at h
        · rename_i st' oc' od of x' hb
          cases hk2 : (cellK X st' od && cellK X st' of && st'.cnt.le X.pmax)
          · rw [hk2] at h; cases h
          rw [hk2] at h
          simp only [Bool.cond_true] at h ⊢
          simp only [Bool.and_eq_true] at hk2
          split at h
          · rename_i se hse
            cases hk3 : (decide (se.seg.exit.kind = .ret) && se.cnt.le X.pmax)
            · rw [hk3] at h; cases h
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hk3
            exact ⟨e, S, st', oc', od, of, x', se, hk, trivial, Nat.eq_of_beq_eq_true g1, g2,
              Nat.eq_of_beq_eq_true g3, Nat.eq_of_beq_eq_true g4, Nat.eq_of_beq_eq_true g5, g6,
              Option.isNone_iff_eq_none.mp g10, hb,
              hk2.1.1, hk2.1.2, hk2.2, hse, hk3.1, hk3.2, rfl⟩
          · cases h
        · cases h
      · cases h
    · cases h
  · cases h

theorem Cnt.get_max (c c' : Cnt) (op : Opcode) : (Cnt.max c c').get op = Nat.max (c.get op) (c'.get op) := by
  cases op <;> rfl

/-- The other arms of a `match` each end at the join with counts at most the result's. -/
theorem cwArms_spec {J : ℕ} {se : CW} : ∀ {as : List (List Core.Stmt)} {ts : List ℕ} {c : Cnt} {u : ℕ}
    {c' : Cnt} {u' : ℕ}, cwArms X J se as ts c u = some (c', u') →
    as.length = ts.length ∧ (∀ op, c.get op ≤ c'.get op) ∧
    ∀ k (hk : k < as.length) (hk' : k < ts.length), ∃ s ck uk, segAtC X ts[k] se = some s ∧
      cw X as[k] { s with book := fileB X.loc X.fs as[k] se.book } = .join J ck uk ∧
      ∀ op, ck.get op ≤ c'.get op
  | [], [], c, u, c', u', h => by
    simp only [cwArms, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, fun _ ↦ le_rfl, fun k hk ↦ absurd hk (Nat.not_lt_zero _)⟩
  | a :: as, t :: ts, c, u, c', u', h => by
    simp only [cwArms] at h
    split at h
    · rename_i s hs
      simp only [Trie.seq_eq] at h
      split at h
      · rename_i J' ca ua hca
        cases hJ : Nat.beq J J'
        · rw [hJ] at h; cases h
        rw [hJ] at h
        obtain rfl := Nat.eq_of_beq_eq_true hJ
        simp only [Bool.cond_true, Cnt.seq_eq, natSeq_eq] at h
        obtain ⟨hl, hc, hk⟩ := cwArms_spec h
        refine ⟨by simp [hl], fun op ↦ ?_, fun k hk1 hk2 ↦ ?_⟩
        · have := hc op
          rw [Cnt.get_max] at this
          exact le_trans (Nat.le_max_left _ _) this
        · cases k with
          | zero =>
            refine ⟨s, ca, ua, hs, hca, fun op ↦ ?_⟩
            have := hc op
            rw [Cnt.get_max] at this
            exact le_trans (Nat.le_max_right _ _) this
          | succ k =>
            exact hk k (by simpa using hk1) (by simpa using hk2)
      · cases h
    · cases h
  | [], _ :: _, _, _, _, _, h => by simp [cwArms] at h
  | _ :: _, [], _, _, _, _, h => by simp [cwArms] at h

theorem cw_match {v : V} {a0 : List Core.Stmt} {as : List (List Core.Stmt)} {ss : List Core.Stmt}
    {st : CW} (h : (cw X (.match_ v (a0 :: as) :: ss) st).ok = true) :
    ∃ t ft t0 ts base se s0 J c0 u0 c u sj, st.seg.exit.kind = .jump (.cell t) ft ∧
      st.seg.exit.succ = t0 :: ts ∧ tblRead t st.its = some (X.loc.cell v, base) ∧
      X.F.self ft = true ∧ ts.length = as.length ∧ v = V.n v.idx ∧ selOk X v = true ∧
      inFrame X.fs [X.loc.cell v, t] = true ∧
      X.arms.any (fun a ↦ Nat.beq a.1 v.idx && Nat.beq a.2.1 t && Nat.beq a.2.2 base) = true ∧
      armsOk X.G X.entry base 0 (t0 :: ts) = true ∧
      endAtC X { st with tg := (t, X.loc.cell v, base) :: st.tg } = .ok se ∧
      segAtC X t0 se = some s0 ∧
      cw X a0 { s0 with book := fileB X.loc X.fs a0 se.book } = .join J c0 u0 ∧
      cwArms X J se as ts c0 u0 = some (c, u) ∧ segAtC X J se = some sj ∧
      cw X (.match_ v (a0 :: as) :: ss) st = cw X ss { sj with cnt := c, uq := u } := by
  simp only [cw] at h ⊢
  split at h
  · rename_i t ft t0 ts hk hsu
    split at h
    · rename_i o1 base htb
      cases hc : (X.F.self ft && Nat.beq ts.length as.length && Nat.beq o1 (X.loc.cell v) &&
          v.path.isEmpty && Nat.beq v.tag 0 && selOk X v && inFrame X.fs [o1, t] &&
          X.arms.any (fun a ↦ Nat.beq a.1 v.idx && Nat.beq a.2.1 t && Nat.beq a.2.2 base) &&
          armsOk X.G X.entry base 0 (t0 :: ts))
      · rw [hc] at h; cases h
      rw [hc] at h
      simp only [Bool.cond_true] at h ⊢
      simp only [Bool.and_eq_true] at hc
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨g1, g2⟩, g3⟩, g7⟩, g8⟩, gsel⟩, g4⟩, g5⟩, g6⟩ := hc
      obtain rfl := Nat.eq_of_beq_eq_true g3
      have hvn : v = V.n v.idx := by
        obtain ⟨vp, vt, vi⟩ := v
        simp only [List.isEmpty_iff] at g7
        obtain rfl := g7
        obtain rfl := Nat.eq_of_beq_eq_true g8
        rfl
      split at h
      · rename_i se hse
        split at h
        · rename_i s0 hs0
          simp only [Trie.seq_eq] at h ⊢
          split at h
          · rename_i J c0 u0 h0
            split at h
            · rename_i c u ha
              split at h
              · rename_i sj hsj
                exact ⟨t, ft, t0, ts, base, se, s0, J, c0, u0, c, u, sj, hk, hsu, htb, g1,
                  Nat.eq_of_beq_eq_true g2, hvn, gsel, g4, g5, g6, hse, hs0, h0, ha, hsj,
                  by simp only [Cnt.seq_eq, natSeq_eq]⟩
              · cases h
            · cases h
          · cases h
          · cases h
        · cases h
      · cases h
    · cases h
  · cases h

end Inv

end
end LeanVM.Guest.B2C
