/-
  LeanVM.Guest.B2C.CplInv

  Inverting the completeness walk: what a statement's step of `cw` checked when the walk does not
  fail.
-/

module

public import LeanVM.Guest.B2C.Cpl
public import LeanVM.Guest.B2C.CplSpec

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

/-! ## Callees by entry -/

theorem functions_lengthC : Data.functions.length = nFns := by decide +kernel

theorem nth_getD {α : Type} : ∀ (l : List α) (n : ℕ) (d : α), listElementOrDefault l n d =
    l.getD n d
  | [], _, _ => rfl
  | _ :: _, 0, _ => rfl
  | _ :: as, n + 1, d => nth_getD as n d

theorem tail_getD {α : Type} (l : List α) (m : ℕ) (d : α) : l.tail.getD m d = l.getD (m + 1) d := by
  cases l <;> simp

theorem headD_getD {α : Type} (l : List α) (d : α) : l.headD d = l.getD 0 d := by
  cases l <;> rfl

/-- **A callee the check finds**: a good function entered there, one of the function's callees,
with its signature. -/
theorem calleeS_spec {X : CX} (hG : X.G = glob.restrict X.callees) {pc j : ℕ} {sg : Sig}
    (h : calleeS X pc = some (j, sg)) :
    2 ≤ j ∧ j < nFns ∧ (fnOf j).entryPc = pc ∧ sg = X.G.sig j ∧ calleeC X pc = some j := by
  have hc : calleeC X pc = some j := by unfold calleeC; rw [h]; rfl
  unfold calleeS at h
  obtain ⟨j', hf, he⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
  have hp := List.find?_some hf
  have hm := List.mem_of_find?_eq_some hf
  have hcs : X.callees.contains j' = true := List.contains_iff_mem.mpr hm
  have hs : X.G.sig j' = glob.sig j' := by rw [hG]; simp only [Glob.restrict, hcs, Bool.cond_true]
  have hg : X.G.good j' = glob.good j' := by rw [hG]; simp only [Glob.restrict, hcs, Bool.true_and]
  rw [hg, hs, Bool.and_eq_true, Nat.beq_eq] at hp
  obtain ⟨hp1, hp2⟩ := hp
  simp only [glob, good, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hp1
  exact ⟨hp1.1, hp1.2, hp2, rfl, hc⟩

/-- A callee the check finds has its signature in `glob`. -/
theorem calleeC_sig {X : CX} (hG : X.G = glob.restrict X.callees) {pc j : ℕ} (h : calleeC X pc = some j) :
    X.G.sig j = glob.sig j := by
  unfold calleeC calleeS at h
  simp only [Option.map_map, Option.map_eq_some_iff, Function.comp_apply] at h
  obtain ⟨j', hf, rfl⟩ := h
  have hcs : X.callees.contains j' = true := List.contains_iff_mem.mpr (List.mem_of_find?_eq_some hf)
  rw [hG]
  simp only [Glob.restrict, hcs, Bool.cond_true]

section Inv

variable {X : CX}

theorem cw_nil (st : CW) : cw X [] st = endC X st := by simp [cw]

theorem cw_atom (a : Core.Atom) (ss : List Core.Stmt) (st : CW) :
    cw X (.atom a :: ss) st =
      cw X ss ⟨st.seg, st.its, st.book, st.fr, st.tg, st.nx, st.cnt, st.uq, none, nvVals (Memory.atomUses a) st.nm⟩ := by
  simp [cw, natSeq_eq]

/-- What `chainEnd` checked. -/
theorem chainEnd_ok {se : CW} {t : ℕ} {ft : Tgt} (h : (chainEnd X se t ft).ok = true) :
    ∃ o b succ, se.seg.exit.succ = succ ∧ succ ≠ [] ∧ tgAt se.tg t = some (o, b) ∧
      X.F.self ft = true ∧ armsOk X.G X.entry b 0 succ = true ∧
      chainEnd X se t ft = .chain o succ se.cnt se.uq := by
  unfold chainEnd at h ⊢
  rcases hs : se.seg.exit.succ with _ | ⟨t0, ts⟩
  · simp [hs, RC.ok] at h
  · rcases hg : tgAt se.tg t with _ | ⟨o, b⟩
    · simp [hs, hg, RC.ok] at h
    · simp only [hs, hg] at h ⊢
      cases hc : (X.F.self ft && armsOk X.G X.entry b 0 (t0 :: ts))
      · simp [hc, RC.ok] at h
      · simp only [Bool.and_eq_true] at hc
        exact ⟨o, b, t0 :: ts, rfl, List.cons_ne_nil _ _, rfl, hc.1, hc.2, rfl⟩

theorem endC_ok {st : CW} (h : (endC X st).ok = true) :
    (∃ t, st.fresh = some t ∧ endC X st = .join t st.cnt st.uq) ∨
    (st.fresh = none ∧ X.stop = none ∧ ∃ se t, endAtC X st = .ok se ∧ se.seg.exit.kind = .next t ∧
      se.seg.exit.succ = [t] ∧ endC X st = .join t se.cnt se.uq) ∨
    (st.fresh = none ∧ ∃ J m c, X.stop = some (J, m) ∧ st.seg.start = J ∧ m ≤ st.seg.items.length ∧
      st.seg.items.length - m ≤ st.its.length ∧
      passL X st (st.its.take (st.its.length - (st.seg.items.length - m))) st.cnt = .ok ([], c) ∧
      endC X st = .mid J m c st.uq) ∨
    (st.fresh = none ∧ X.stop = none ∧ ∃ se t ft o b succ, endAtC X st = .ok se ∧
      se.seg.exit.kind = .jump (.cell t) ft ∧ se.seg.exit.succ = succ ∧ succ ≠ [] ∧
      tgAt se.tg t = some (o, b) ∧ X.F.self ft = true ∧ armsOk X.G X.entry b 0 succ = true ∧
      endC X st = .chain o succ se.cnt se.uq) := by
  rcases hf : st.fresh with _ | t
  · rcases hs : X.stop with _ | ⟨J, m⟩
    · rcases he : endAtC X st with e | se
      · simp [endC, hf, hs, he, RC.ok] at h
      · rcases hk : se.seg.exit.kind with t | _ | _ | ⟨tg, ft⟩
        · simp only [endC, hf, hs, he, hk] at h
          cases hb : se.seg.exit.succ == [t]
          · simp [hb, RC.ok] at h
          · refine Or.inr (Or.inl ⟨rfl, rfl, se, t, rfl, hk, beq_iff_eq.mp hb, ?_⟩)
            simp only [endC, hf, hs, he, hk, hb, Bool.cond_true]
        · simp [endC, hf, hs, he, hk, RC.ok] at h
        · simp [endC, hf, hs, he, hk, RC.ok] at h
        · rcases tg with e | e | t
          · simp [endC, hf, hs, he, hk, RC.ok] at h
          · simp [endC, hf, hs, he, hk, RC.ok] at h
          · have hc : endC X st = chainEnd X se t ft := by simp only [endC, hf, hs, he, hk]
            rw [hc] at h
            obtain ⟨o, b, succ, h1, h2, h3, h4, h5, h6⟩ := chainEnd_ok h
            exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, se, t, ft, o, b, succ, rfl, hk, h1, h2, h3, h4, h5,
              hc.trans h6⟩))
    · right; right; left
      simp only [endC, hf, hs] at h
      cases hb : (Nat.beq st.seg.start J && Nat.ble m st.seg.items.length &&
          Nat.ble (st.seg.items.length - m) st.its.length)
      · rw [hb] at h
        simp [RC.ok] at h
      · rw [hb] at h
        simp only [Bool.cond_true] at h
        have hb' := hb
        simp only [Bool.and_eq_true] at hb'
        obtain ⟨⟨b1, b2⟩, b3⟩ := hb'
        rcases hp : passL X st (st.its.take (st.its.length - (st.seg.items.length - m))) st.cnt with
          e | ⟨rest, c⟩
        · rw [hp] at h
          simp [RC.ok] at h
        · cases rest with
          | nil =>
            refine ⟨rfl, J, m, c, rfl, Nat.eq_of_beq_eq_true b1, Nat.le_of_ble_eq_true b2,
              Nat.le_of_ble_eq_true b3, hp, ?_⟩
            simp only [endC, hf, hs, hb, hp, Bool.cond_true, Cnt.seq_eq]
          | cons x xs =>
            rw [hp] at h
            simp [RC.ok] at h
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
        s.cnt, u, bif rets.isEmpty then s.fresh else none, nvVals rets s.nm⟩ := by
  unfold afterC at h
  split at h
  · rename_i se hse
    split at h
    · rename_i s hs
      exact ⟨se, s, hse, hs, (Except.ok.inj h).symm⟩
    · cases h
  · cases h

theorem cw_call (hG : X.G = glob.restrict X.callees) {f : String} {args rets : List V} {ss : List Core.Stmt} {st : CW}
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
    · rename_i j sg hj
      obtain ⟨-, -, -, rfl, hjc⟩ := calleeS_spec hG hj
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
        exact ⟨e, q, r, j, sr, hk, hjc, h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3,
          Nat.le_of_ble_eq_true h4, h5, h6, h7, h8, (by simpa using h9), hsr, rfl⟩
      · cases h
    · cases h
  · cases h

theorem cw_dispatch {v : V} {fs : List String} {args rets : List V} {ss : List Core.Stmt} {st : CW}
    (h : (cw X (.dispatch v fs args rets :: ss) st).ok = true) :
    ∃ t q r base sr, st.seg.exit.kind = .call (.cell t) q r ∧ tblRead t st.its = some (X.loc.cell v, base) ∧
      v = V.n v.idx ∧ selOk X st v = true ∧
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
      cases hc : (Nat.beq o1 (X.loc.cell v) && v.path.isEmpty && Nat.beq v.tag 0 && selOk X st v &&
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
      (if X.main = true then se.seg.exit.kind = .jump (.gp (2 ^ 19 - 1)) (.gp 0)
        else se.seg.exit.kind = .ret) ∧ se.cnt.le X.pmax = true ∧ vs.length = X.nret ∧
      runCells (2 + X.nargs) (vs.map X.loc.cell) = true ∧ inFrame X.fs (vs.map X.loc.cell) = true ∧
      cw X (.ret vs :: ss) st = .done := by
  simp only [cw] at h ⊢
  split at h
  · rename_i se hse
    cases hc : ((bif X.main then decide (se.seg.exit.kind = .jump (.gp (2 ^ 19 - 1)) (.gp 0))
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

theorem cw_callIf (hG : X.G = glob.restrict X.callees) {c : V} {f : String} {args : List V} {ss : List Core.Stmt}
    {st : CW} (h : (cw X (.callIf c f args :: ss) st).ok = true) :
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
      · rename_i j sg hj
        obtain ⟨-, -, -, rfl, hjc⟩ := calleeS_spec hG hj
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
                exact ⟨e, q, r, j, st', oc', od, of, x', se, t, sr, hk, hjc, g1,
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

/-- How an arm ended, by `armEnd`. -/
theorem armEnd_join {J : ℕ} {r : RC} {c : Cnt} {u : ℕ} (h : armEnd J [] r = some (c, u)) :
    r = .join J c u := by
  cases r with
  | join J' c' u' =>
    simp only [armEnd, List.isEmpty_nil, Bool.true_and] at h
    cases hb : Nat.beq J J'
    · simp [hb] at h
    · simp only [hb, Bool.cond_true, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [Nat.eq_of_beq_eq_true hb]
  | chain o s' c' u' => simp [armEnd] at h
  | mid _ _ _ _ => simp [armEnd] at h
  | done => simp [armEnd] at h
  | fail _ => simp [armEnd] at h

theorem armEnd_chain {o : ℕ} {succ : List ℕ} {r : RC} {c : Cnt} {u : ℕ} (hs : succ ≠ [])
    (h : armEnd o succ r = some (c, u)) : r = .chain o succ c u := by
  cases r with
  | join J' c' u' =>
    cases succ with
    | nil => exact absurd rfl hs
    | cons t ts => simp [armEnd] at h
  | chain o' s' c' u' =>
    simp only [armEnd] at h
    cases hb : (!succ.isEmpty && Nat.beq o o' && succ == s')
    · simp [hb] at h
    · simp only [hb, Bool.cond_true, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, beq_iff_eq] at hb
      obtain ⟨⟨-, h2⟩, rfl⟩ := hb
      rw [Nat.eq_of_beq_eq_true h2]
  | mid _ _ _ _ => simp [armEnd] at h
  | done => simp [armEnd] at h
  | fail _ => simp [armEnd] at h

theorem armEnd_ok {J : ℕ} {succ : List ℕ} {r : RC} {p : Cnt × ℕ} (h : armEnd J succ r = some p) :
    r.ok = true := by
  cases r <;> simp_all [armEnd, RC.ok]

/-- The other arms of a `match` each end as `armEnd J succ` says, with counts at most the
result's. -/
theorem cwArms_spec {J : ℕ} {succ : List ℕ} {v : V} {se : CW} {key : Option (List Cnt)} :
    ∀ {as : List (List Core.Stmt)} {ts : List ℕ} {c : Cnt} {u : ℕ} {k : ℕ}
    {c' : Cnt} {u' : ℕ}, cwArms X J succ v se key as ts c u k = some (c', u') →
    as.length = ts.length ∧ (∀ op, c.get op ≤ c'.get op) ∧
    ∀ i (hk : i < as.length) (hk' : i < ts.length), ∃ s ck uk, segAtC X ts[i] se = some s ∧
      armEnd J succ (cw X as[i] { s with book := (fileB X.loc X.fs as[i] se.book), tg := (armTg X v (k + i) ++ s.tg) })
        = some (ck, uk) ∧
      (∀ op, ck.get op ≤ c'.get op) ∧ armChkK key (k + i) ck = true
  | [], [], c, u, k, c', u', h => by
    simp only [cwArms, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, fun _ ↦ le_rfl, fun i hk ↦ absurd hk (Nat.not_lt_zero _)⟩
  | a :: as, t :: ts, c, u, k, c', u', h => by
    simp only [cwArms] at h
    split at h
    · rename_i s hs
      simp only [Trie.seq_eq] at h
      split at h
      · rename_i ca ua hca
        cases hJ : armChkK key k ca
        · rw [hJ] at h; cases h
        rw [hJ] at h
        simp only [Bool.cond_true, Cnt.seq_eq, natSeq_eq] at h
        obtain ⟨hl, hc, hk⟩ := cwArms_spec h
        refine ⟨by simp [hl], fun op ↦ ?_, fun i hk1 hk2 ↦ ?_⟩
        · have := hc op
          rw [Cnt.get_max] at this
          exact le_trans (Nat.le_max_left _ _) this
        · cases i with
          | zero =>
            refine ⟨s, ca, ua, hs, by simpa using hca, fun op ↦ ?_, by simpa using hJ⟩
            have := hc op
            rw [Cnt.get_max] at this
            exact le_trans (Nat.le_max_right _ _) this
          | succ i =>
            obtain ⟨s', ck, uk, h1, h2, h3, h4⟩ := hk i (by simpa using hk1) (by simpa using hk2)
            exact ⟨s', ck, uk, h1, by rw [show k + (i + 1) = k + 1 + i by omega]; exact h2, h3,
              by rw [show k + (i + 1) = k + 1 + i by omega]; exact h4⟩
      · cases h
    · cases h
  | [], _ :: _, _, _, _, _, _, h => by simp [cwArms] at h
  | _ :: _, [], _, _, _, _, _, h => by simp [cwArms] at h

/-- **A `match` the walk passes**: its table jump, then arm `0` ending at a join, the other arms
there, and the walk goes on after it; or, chained, every arm ending in the next `match`'s table
jump, the `match` the block's last statement. -/
theorem cw_match {v : V} {a0 : List Core.Stmt} {as : List (List Core.Stmt)} {ss : List Core.Stmt}
    {st : CW} (h : (cw X (.match_ v (a0 :: as) :: ss) st).ok = true) :
    ∃ t ft t0 ts base se s0, st.seg.exit.kind = .jump (.cell t) ft ∧
      st.seg.exit.succ = t0 :: ts ∧ tblRead t st.its = some (X.loc.cell v, base) ∧
      X.F.self ft = true ∧ ts.length = as.length ∧ v = V.n v.idx ∧ selOk X st v = true ∧
      inFrame X.fs [X.loc.cell v, t] = true ∧
      X.arms.any (fun a ↦ Nat.beq a.1 v.idx && Nat.beq a.2.1 t && Nat.beq a.2.2 base) = true ∧
      armsOk X.G X.entry base 0 (t0 :: ts) = true ∧ chainPre X st v (as.length + 1) = true ∧
      endAtC X { st with tg := (t, X.loc.cell v, base) :: st.tg } = .ok se ∧
      segAtC X t0 (armSt (armKeyD X.acs v.idx) se) = some s0 ∧
      ((∃ J c0 u0 c u sj,
        cw X a0 { s0 with book := fileB X.loc X.fs a0 se.book, tg := armTg X v 0 ++ s0.tg } = .join J c0 u0 ∧
        armChkK (armKeyD X.acs v.idx) 0 c0 = true ∧
        cwArms X J [] v (armSt (armKeyD X.acs v.idx) se) (armKeyD X.acs v.idx) as ts c0 u0 1 = some (c, u) ∧
        segAtC X J se = some sj ∧
        cw X (.match_ v (a0 :: as) :: ss) st =
          cw X ss { sj with cnt := armCnt (armKeyD X.acs v.idx) se c, uq := u }) ∨
       (∃ o succ c0 u0 c u,
        cw X a0 { s0 with book := fileB X.loc X.fs a0 se.book, tg := armTg X v 0 ++ s0.tg } = .chain o succ c0 u0 ∧
        armChkK (armKeyD X.acs v.idx) 0 c0 = true ∧ ss = [] ∧ succ ≠ [] ∧
        cwArms X o succ v (armSt (armKeyD X.acs v.idx) se) (armKeyD X.acs v.idx) as ts c0 u0 1 = some (c, u) ∧
        cw X (.match_ v (a0 :: as) :: ss) st = .chain o succ (armCnt (armKeyD X.acs v.idx) se c) u)) := by
  simp only [cw] at h ⊢
  split at h
  · rename_i t ft t0 ts hk hsu
    split at h
    · rename_i o1 base htb
      cases hc : (X.F.self ft && Nat.beq ts.length as.length && Nat.beq o1 (X.loc.cell v) &&
          v.path.isEmpty && Nat.beq v.tag 0 && selOk X st v && inFrame X.fs [o1, t] &&
          X.arms.any (fun a ↦ Nat.beq a.1 v.idx && Nat.beq a.2.1 t && Nat.beq a.2.2 base) &&
          armsOk X.G X.entry base 0 (t0 :: ts) && chainPre X st v (as.length + 1))
      · rw [hc] at h; cases h
      rw [hc] at h
      simp only [Bool.cond_true] at h ⊢
      simp only [Bool.and_eq_true] at hc
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨g1, g2⟩, g3⟩, g7⟩, g8⟩, gsel⟩, g4⟩, g5⟩, g6⟩, gch⟩ := hc
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
          refine ⟨t, ft, t0, ts, base, se, s0, hk, hsu, htb, g1, Nat.eq_of_beq_eq_true g2, hvn, gsel,
            g4, g5, g6, gch, hse, hs0, ?_⟩
          split at h
          · rename_i J c0 u0 h0
            cases hck : armChkK (armKeyD X.acs v.idx) 0 c0
            · rw [hck] at h; cases h
            rw [hck] at h
            simp only [Bool.cond_true] at h ⊢
            split at h
            · rename_i c u ha
              split at h
              · rename_i sj hsj
                exact Or.inl ⟨J, c0, u0, c, u, sj, h0, hck, ha, hsj,
                  by simp only [Cnt.seq_eq, natSeq_eq]⟩
              · cases h
            · cases h
          · rename_i o succ c0 u0 h0
            cases hck : (armChkK (armKeyD X.acs v.idx) 0 c0 && ss.isEmpty && !succ.isEmpty)
            · rw [hck] at h; cases h
            rw [hck] at h
            simp only [Bool.cond_true] at h
            have hck' := hck
            simp only [Bool.and_eq_true, List.isEmpty_iff, Bool.not_eq_true', List.isEmpty_eq_false_iff] at hck'
            obtain ⟨⟨hck1, rfl⟩, hsn⟩ := hck'
            split at h
            · rename_i c u ha
              exact Or.inr ⟨o, succ, c0, u0, c, u, h0, hck1, rfl, hsn, ha,
                by simp only [Cnt.seq_eq, natSeq_eq]; rfl⟩
            · cases h
          · cases h
          · cases h
        · cases h
      · cases h
    · cases h
  · cases h

/-- **An entered `match` the walk passes**: arm `0` from the first arm, ending at a join, the
other arms there, and the walk goes on after it; or, chained, every arm ending in the next
`match`'s table jump, the `match` the block's last statement. -/
theorem cwE_ok {o : ℕ} {succ : List ℕ} {se : CW} {ss : List Core.Stmt} (h : (cwE X o succ se ss).ok = true) :
    ∃ v a0 as ss' t0 ts s0, ss = .match_ v (a0 :: as) :: ss' ∧ succ = t0 :: ts ∧
      o = X.loc.cell v ∧ v = V.n v.idx ∧ selOk X se v = true ∧ ts.length = as.length ∧
      inFrame X.fs [o] = true ∧ chainPre X se v (as.length + 1) = true ∧
      segAtC X t0 (armSt (armKeyD X.acs v.idx) se) = some s0 ∧
      ((∃ J c0 u0 c u sj,
        cw X a0 { s0 with book := fileB X.loc X.fs a0 se.book, tg := armTg X v 0 ++ s0.tg } = .join J c0 u0 ∧
        armChkK (armKeyD X.acs v.idx) 0 c0 = true ∧
        cwArms X J [] v (armSt (armKeyD X.acs v.idx) se) (armKeyD X.acs v.idx) as ts c0 u0 1 = some (c, u) ∧
        segAtC X J se = some sj ∧
        cwE X o succ se ss = cw X ss' { sj with cnt := armCnt (armKeyD X.acs v.idx) se c, uq := u }) ∨
       (∃ o' succ' c0 u0 c u,
        cw X a0 { s0 with book := fileB X.loc X.fs a0 se.book, tg := armTg X v 0 ++ s0.tg } = .chain o' succ' c0 u0 ∧
        armChkK (armKeyD X.acs v.idx) 0 c0 = true ∧ ss' = [] ∧ succ' ≠ [] ∧
        cwArms X o' succ' v (armSt (armKeyD X.acs v.idx) se) (armKeyD X.acs v.idx) as ts c0 u0 1 = some (c, u) ∧
        cwE X o succ se ss = .chain o' succ' (armCnt (armKeyD X.acs v.idx) se c) u)) := by
  unfold cwE at h ⊢
  split at h
  · rename_i v a0 as ss'
    split at h
    · rename_i t0 ts
      cases hc : (Nat.beq o (X.loc.cell v) && v.path.isEmpty && Nat.beq v.tag 0 && selOk X se v &&
          Nat.beq ts.length as.length && inFrame X.fs [o] && chainPre X se v (as.length + 1))
      · rw [hc] at h; cases h
      rw [hc] at h
      simp only [Bool.cond_true] at h ⊢
      simp only [Bool.and_eq_true] at hc
      obtain ⟨⟨⟨⟨⟨⟨g1, g7⟩, g8⟩, gsel⟩, g2⟩, g4⟩, gch⟩ := hc
      have hvn : v = V.n v.idx := by
        obtain ⟨vp, vt, vi⟩ := v
        simp only [List.isEmpty_iff] at g7
        obtain rfl := g7
        obtain rfl := Nat.eq_of_beq_eq_true g8
        rfl
      split at h
      · rename_i s0 hs0
        simp only [Trie.seq_eq] at h ⊢
        refine ⟨v, a0, as, ss', t0, ts, s0, rfl, rfl, Nat.eq_of_beq_eq_true g1, hvn, gsel,
          Nat.eq_of_beq_eq_true g2, g4, gch, hs0, ?_⟩
        split at h
        · rename_i J c0 u0 h0
          cases hck : armChkK (armKeyD X.acs v.idx) 0 c0
          · rw [hck] at h; cases h
          rw [hck] at h
          simp only [Bool.cond_true] at h ⊢
          split at h
          · rename_i c u ha
            split at h
            · rename_i sj hsj
              exact Or.inl ⟨J, c0, u0, c, u, sj, h0, hck, ha, hsj,
                by simp only [Cnt.seq_eq, natSeq_eq]⟩
            · cases h
          · cases h
        · rename_i o' succ' c0 u0 h0
          cases hck : (armChkK (armKeyD X.acs v.idx) 0 c0 && ss'.isEmpty && !succ'.isEmpty)
          · rw [hck] at h; cases h
          rw [hck] at h
          simp only [Bool.cond_true] at h
          have hck' := hck
          simp only [Bool.and_eq_true, List.isEmpty_iff, Bool.not_eq_true', List.isEmpty_eq_false_iff] at hck'
          obtain ⟨⟨hck1, rfl⟩, hsn⟩ := hck'
          split at h
          · rename_i c u ha
            exact Or.inr ⟨o', succ', c0, u0, c, u, h0, hck1, rfl, hsn, ha,
              by simp only [Cnt.seq_eq, natSeq_eq]; rfl⟩
          · cases h
        · cases h
        · cases h
      · cases h
    · cases h
  · cases h

end Inv

end
end LeanVM.Guest.B2C
