/-
  LeanVM.Guest.CoreMode.HeapCWinM

  A window that is one long `match`, split by its arms: the arms' passes in slices, each giving what the join
  reads of its arms, then the join.
-/

module

public import LeanVM.Guest.CoreMode.HeapCWinF

/-!
# A `match` in windows

The windows of `HeapCWin` and `HeapCWinF` cut between top-level statements, so one `match` of many long arms is
one window. Its pass is `chkArmsC` over the arms, each arm from the state before the `match` with the serials of
the previous arm's end (`CSt.cnt`), then `joinSt`, which reads of each arm only whether it returns and the
entries it added (`blkSum`), and of the last arm its serials. So the arms split (`chkArmsC_append`): a window of
arms (`armsOkW`) decides that their passes, from the state before the `match` with stated serials, give stated
summaries and end at stated serials; consecutive arm windows chain (`armsWins_chain`), and the join
(`joinOk`), from the summaries, gives the window's end state (`winOk_of_arms`, `winOkF_of_arms`).
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Exec (Trie PowTree natSeq)

@[expose] public section

/-- A state's serials. -/
abbrev Cnt := ℕ × ℕ × ℕ × ℕ

/-- The serials of a state. -/
def cntOf (s : CSt) : Cnt := (s.n, s.nr, s.nc, s.nt)

/-- `st` with the serials `c`. -/
def CSt.withN (st : CSt) (c : Cnt) : CSt :=
  ⟨st.env, st.sc, st.rs, st.ad, st.sv, st.src, st.pf, st.pr, c.1, c.2.1, c.2.2.1, c.2.2.2, st.cd, st.eqs, st.dq⟩

theorem cnt_withN (st s : CSt) : st.cnt s = st.withN (cntOf s) := rfl

theorem withN_cntOf (st : CSt) : st.withN (cntOf st) = st := by cases st; rfl

theorem withN_withN (st : CSt) (c c' : Cnt) : (st.withN c).withN c' = st.withN c' := rfl

theorem cntOf_withN (st : CSt) (c : Cnt) : cntOf (st.withN c) = c := rfl

/-- What a join reads of a block `(returns, start, end)`: whether it returns, and the cells, runs, pointer
facts and pointer runs added after its start. -/
structure BlkSum where
  ret : Bool
  sc : List (ℕ × CCell)
  rs : List (ℕ × PRun)
  pf : List (ℕ × (CCell × List ℕ))
  pr : List (ℕ × (PRun × List ℕ))
  deriving DecidableEq

/-- A block's `BlkSum`. -/
noncomputable def blkSum (b : Bool × CSt × CSt) : BlkSum :=
  ⟨b.1, rng b.2.2.sc b.2.1.n (b.2.2.n - b.2.1.n), rng b.2.2.rs b.2.1.nr (b.2.2.nr - b.2.1.nr),
    rng b.2.2.pf b.2.1.n (b.2.2.n - b.2.1.n), rng b.2.2.pr b.2.1.nr (b.2.2.nr - b.2.1.nr)⟩

/-- `joinSt` from the blocks' summaries and the serials `c`. -/
noncomputable def joinSum (bs : List BlkSum) (st : CSt) (c : Cnt) : CSt :=
  ⟨st.env, insL (joinE CCell.beq (bs.map fun b ↦ (b.ret, b.sc))) st.sc,
    insL (joinE PRun.beq (bs.map fun b ↦ (b.ret, b.rs))) st.rs, st.ad, st.sv, st.src,
    insL (joinE pfBeq (bs.map fun b ↦ (b.ret, b.pf))) st.pf,
    insL (joinE prBeq (bs.map fun b ↦ (b.ret, b.pr))) st.pr, c.1, c.2.1, c.2.2.1, c.2.2.2, st.cd, st.eqs, st.dq⟩

theorem joinSt_sum (bs : List (Bool × CSt × CSt)) (st s : CSt) :
    joinSt bs st s = joinSum (bs.map blkSum) st (cntOf s) := by
  simp only [joinSt, joinSum, List.map_map]; rfl

/-! ## The last block -/

theorem lastSt_ne (b : Bool × CSt × CSt) : ∀ (l : List (Bool × CSt × CSt)) (s s' : CSt),
    lastSt (b :: l) s = lastSt (b :: l) s'
  | [], _, _ => rfl
  | c :: l, s, s' => by simp only [lastSt]; exact lastSt_ne c l s s'

theorem lastSt_cons (b : Bool × CSt × CSt) : ∀ (l : List (Bool × CSt × CSt)) (st : CSt),
    lastSt (b :: l) st = lastSt l b.2.2
  | [], _ => rfl
  | c :: l, st => by simp only [lastSt]; exact lastSt_ne c l st b.2.2

theorem lastSt_append : ∀ (la lb : List (Bool × CSt × CSt)) (s : CSt),
    lastSt (la ++ lb) s = lastSt lb (lastSt la s)
  | [], _, _ => rfl
  | b :: la, lb, s => by rw [List.cons_append, lastSt_cons, lastSt_cons, lastSt_append la lb]

theorem cntOf_lastSt (l : List (Bool × CSt × CSt)) {s s' : CSt} (h : cntOf s = cntOf s') :
    cntOf (lastSt l s) = cntOf (lastSt l s') := by
  cases l with
  | nil => exact h
  | cons b l => rw [lastSt_cons, lastSt_cons]

/-! ## The arms in slices -/

/-- **The arms split**: the pass over `A ++ B` is the pass over `A`, then over `B` from the state before the
`match` with the serials of `A`'s last arm's end. -/
theorem chkArmsC_append (X : CX) (x : V) : ∀ (A B : List (List Stmt)) (j : ℕ) (st : CSt),
    chkArmsC X x j (A ++ B) st = (chkArmsC X x j A st).bind fun la ↦
      (chkArmsC X x (j + A.length) B (st.withN (cntOf (lastSt la st)))).map (la ++ ·)
  | [], B, j, st => by
    simp only [List.nil_append, chkArmsC, Option.bind_some, lastSt, withN_cntOf, List.length_nil,
      Nat.add_zero, List.nil_append, Option.map_id']
  | a :: A, B, j, st => by
    simp only [List.cons_append, chkArmsC]
    cases h : chkC (X.ext (carm x j)) a st with
    | none => rfl
    | some s1 =>
      simp only
      rw [cnt_withN, chkArmsC_append X x A B (j + 1) (st.withN (cntOf s1))]
      cases h2 : chkArmsC X x (j + 1) A (st.withN (cntOf s1)) with
      | none => rfl
      | some la =>
        simp only [Option.bind_some, List.length_cons]
        have hc : cntOf (lastSt la (st.withN (cntOf s1))) = cntOf (lastSt ((endsRet a, st, s1) :: la) st) := by
          rw [lastSt_cons]; exact cntOf_lastSt la (cntOf_withN st (cntOf s1))
        rw [withN_withN, hc, show j + 1 + A.length = j + (A.length + 1) by omega]
        cases chkArmsC X x (j + (A.length + 1)) B (st.withN (cntOf (lastSt ((endsRet a, st, s1) :: la) st))) <;>
          rfl

/-- The arms `A` from arm `j`, from `st` with the serials `c`: their summaries, and the serials of the last
one's end. -/
noncomputable def armsW (X : CX) (x : V) (j : ℕ) (A : List (List Stmt)) (st : CSt) (c : Cnt) :
    Option (List BlkSum × Cnt) :=
  (chkArmsC X x j A (st.withN c)).map fun la ↦ (la.map blkSum, cntOf (lastSt la (st.withN c)))

theorem armsW_append {X : CX} {x : V} {j : ℕ} {A B : List (List Stmt)} {st : CSt} {c c1 c2 : Cnt}
    {l1 l2 : List BlkSum} (h1 : armsW X x j A st c = some (l1, c1))
    (h2 : armsW X x (j + A.length) B st c1 = some (l2, c2)) : armsW X x j (A ++ B) st c = some (l1 ++ l2, c2) := by
  unfold armsW at h1 h2 ⊢
  rw [chkArmsC_append]
  cases ha : chkArmsC X x j A (st.withN c) with
  | none => rw [ha] at h1; cases h1
  | some la =>
    rw [ha] at h1
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨hl1, hc1⟩ := h1
    simp only [Option.bind_some, withN_withN, hc1]
    cases hb : chkArmsC X x (j + A.length) B (st.withN c1) with
    | none => rw [hb] at h2; cases h2
    | some lb =>
      rw [hb] at h2
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
      obtain ⟨hl2, hc2⟩ := h2
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, List.map_append, hl1, hl2, true_and]
      rw [lastSt_append, ← hc2]
      exact cntOf_lastSt lb (by rw [hc1, cntOf_withN])

/-! ## Windows of arms -/

/-- The selector and arms of a block's first statement, a `match`. -/
def matchOf : List Stmt → Option (V × List (List Stmt))
  | .match_ x arms :: _ => some (x, arms)
  | _ => none

theorem matchOf_some : ∀ {L : List Stmt} {x : V} {arms : List (List Stmt)}, matchOf L = some (x, arms) →
    L.take 1 = [.match_ x arms]
  | .match_ _ _ :: _, _, _, h => by simp only [matchOf, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl
  | [], _, _, h => by simp [matchOf] at h
  | .atom _ :: _, _, _, h => by simp [matchOf] at h
  | .ite _ _ _ :: _, _, _, h => by simp [matchOf] at h
  | .call _ _ _ :: _, _, _, h => by simp [matchOf] at h
  | .callIf _ _ _ :: _, _, _, h => by simp [matchOf] at h
  | .dispatch _ _ _ _ :: _, _, _, h => by simp [matchOf] at h
  | .ret _ :: _, _, _, h => by simp [matchOf] at h

/-- **A window of arms**: of the `match` heading `L`, the `k` arms from arm `j`, from `st` with the serials `c`,
give the summaries `l` and end at the serials `c'`. -/
noncomputable def armsOkW (pows : PowTree) (sigOf : String → HSig) (f : Fn) (H : HCert) (L : List Stmt) (j k : ℕ)
    (st : CSt) (c : Cnt) (l : List BlkSum) (c' : Cnt) : Bool :=
  match matchOf L with
  | some (x, arms) => withCx pows sigOf f H fun X ↦ match armsW X x j ((arms.drop j).take k) st c with
    | some p => decide (p.1 = l) && decide (p.2 = c')
    | none => false
  | none => false

theorem armsOk_spec {pows : PowTree} {sigOf : String → HSig} {f : Fn} {H : HCert} {L : List Stmt} {j k : ℕ}
    {st : CSt} {c c' : Cnt} {l : List BlkSum} {x : V} {arms : List (List Stmt)} (hm : matchOf L = some (x, arms))
    (h : armsOkW pows sigOf f H L j k st c l c' = true) :
    armsW (cxOf pows sigOf f H) x j ((arms.drop j).take k) st c = some (l, c') := by
  simp only [armsOkW, hm, withCx_eq] at h
  split at h
  · rename_i p hp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    rw [hp, ← h.1, ← h.2]
  · cases h

/-- **Consecutive windows of arms**: the cut points (arm index, serials there) and each window's summaries. -/
def armsWins (pows : PowTree) (sigOf : String → HSig) (f : Fn) (H : HCert) (L : List Stmt) (st : CSt) :
    List (ℕ × Cnt) → List (List BlkSum) → Prop
  | (a, c) :: (b, c') :: l, s :: ss => armsOkW pows sigOf f H L a (b - a) st c s c' = true ∧ a ≤ b ∧
      armsWins pows sigOf f H L st ((b, c') :: l) ss
  | [_], [] => True
  | _, _ => False

/-- The last cut point. -/
def lastA : List (ℕ × Cnt) → ℕ × Cnt → ℕ × Cnt
  | [], p => p
  | p :: l, _ => lastA l p

theorem armsWins_chain {pows : PowTree} {sigOf : String → HSig} {f : Fn} {H : HCert} {L : List Stmt} {st : CSt}
    {x : V} {arms : List (List Stmt)} (hm : matchOf L = some (x, arms)) :
    ∀ (l : List (ℕ × Cnt)) (ss : List (List BlkSum)) (a : ℕ) (c : Cnt), armsWins pows sigOf f H L st ((a, c) :: l) ss →
      armsW (cxOf pows sigOf f H) x a ((arms.drop a).take ((lastA l (a, c)).1 - a)) st c =
        some (ss.flatten, (lastA l (a, c)).2) ∧ a ≤ (lastA l (a, c)).1
  | [], [], a, c, _ => by
    simp only [lastA, Nat.sub_self, List.take_zero, List.flatten_nil, armsW, chkArmsC, Option.map_some,
      List.map_nil, lastSt, cntOf_withN, and_self, le_refl]
  | [], _ :: _, _, _, h => h.elim
  | (_, _) :: _, [], _, _, h => h.elim
  | (b, c') :: l, s :: ss, a, c, h => by
    obtain ⟨hw, hab, hr⟩ := h
    obtain ⟨hc, hb⟩ := armsWins_chain hm l ss b c' hr
    replace hw := armsOk_spec hm hw
    simp only [lastA] at hc hb ⊢
    have hlen : ((arms.drop a).take (b - a)).length = b - a ∨ ((arms.drop b).take ((lastA l (b, c')).1 - b)) = [] := by
      by_cases hle : b ≤ arms.length
      · left; simp only [List.length_take, List.length_drop]; omega
      · right; simp only [List.take_eq_nil_iff, List.drop_eq_nil_iff]; omega
    have htake : (arms.drop a).take ((lastA l (b, c')).1 - a) =
        (arms.drop a).take (b - a) ++ (arms.drop b).take ((lastA l (b, c')).1 - b) := by
      rw [show (lastA l (b, c')).1 - a = (b - a) + ((lastA l (b, c')).1 - b) by omega, List.take_add, List.drop_drop]
      congr 3; omega
    refine ⟨?_, by omega⟩
    rw [htake, List.flatten_cons]
    rcases hlen with hlen | hnil
    · refine armsW_append hw ?_
      rw [hlen, show a + (b - a) = b by omega]
      exact hc
    · rw [hnil] at hc ⊢
      have hc' := hc
      simp only [armsW, chkArmsC, Option.map_some, List.map_nil, lastSt, cntOf_withN, Option.some.injEq,
        Prod.mk.injEq] at hc'
      obtain ⟨hss, hcc⟩ := hc'
      rw [← hss, List.append_nil, ← hcc]
      simpa only [List.append_nil] using hw

/-- **The join of a split `match`**: `L`'s first statement a `match` with at most `N` arms, naming no ghost
value, and the join of the summaries `sums` (the last arm ending at the serials `c`) from `st` is `st'`. -/
noncomputable def joinOk (L : List Stmt) (N : ℕ) (st : CSt) (sums : List BlkSum) (c : Cnt) (st' : CSt) : Bool :=
  ngL (L.take 1) && match matchOf L with
    | some (_, arms) => Nat.ble arms.length N && decide (joinSum sums st c = st')
    | none => false

theorem chkC_of_arms {pows : PowTree} {sigOf : String → HSig} {f : Fn} {H : HCert} {L : List Stmt} {N : ℕ}
    {st st' : CSt} {l : List (ℕ × Cnt)} {ss : List (List BlkSum)} {cf : Cnt}
    (hj : joinOk L N st ss.flatten cf st' = true) (hw : armsWins pows sigOf f H L st ((0, cntOf st) :: l) ss)
    (hl : lastA l (0, cntOf st) = (N, cf)) :
    noGhostL (L.take 1) = true ∧ endsRet (L.take 1) = false ∧ Memory.Stmt.noRetListS (L.take 1) = nrL (L.take 1) ∧
      chkC (cxOf pows sigOf f H) (L.take 1) st = some st' := by
  unfold joinOk at hj
  cases hm : matchOf L with
  | none => rw [hm] at hj; simp at hj
  | some p =>
    obtain ⟨x, arms⟩ := p
    rw [hm] at hj
    simp only [Bool.and_eq_true, Nat.ble_eq, decide_eq_true_eq, ngL_eq] at hj
    obtain ⟨hng, hN, hjs⟩ := hj
    obtain ⟨hc, -⟩ := armsWins_chain hm l ss 0 (cntOf st) hw
    rw [hl] at hc
    simp only [List.drop_zero, Nat.sub_zero, List.take_of_length_le hN, armsW, withN_cntOf] at hc
    rw [matchOf_some hm]
    refine ⟨by rw [← matchOf_some hm]; exact hng, rfl, (nrL_eq _).symm, ?_⟩
    simp only [chkC]
    cases hk : chkArmsC (cxOf pows sigOf f H) x 0 arms st with
    | none => rw [hk] at hc; cases hc
    | some bs =>
      rw [hk] at hc
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨hs, hcf⟩ := hc
      simp only [CSt.seq_eq, joinSt_sum, hs, hcf, hjs]

/-- **A window that is one `match`, from windows of its arms** (a loop helper's window). -/
theorem winOk_of_arms {pows : PowTree} {sigOf : String → HSig} {f : Fn} {H : HCert} {L : List Stmt} {a N : ℕ}
    {st st' : CSt} {l : List (ℕ × Cnt)} {ss : List (List BlkSum)} {cf : Cnt}
    (hj : joinOk (L.drop a) N st ss.flatten cf st' = true)
    (hr : nrL ((L.drop a).take 1) = true)
    (hw : armsWins pows sigOf f H (L.drop a) st ((0, cntOf st) :: l) ss) (hl : lastA l (0, cntOf st) = (N, cf)) :
    winOk pows sigOf f H ((L.drop a).take (a + 1 - a)) st st' = true := by
  obtain ⟨hg, -, -, hc⟩ := chkC_of_arms hj hw hl
  rw [show a + 1 - a = 1 by omega]
  simp only [winOk, hr, withCx_eq, hc, ngL_eq, hg, decide_true, Bool.and_self]

/-- **A window that is one `match`, from windows of its arms** (a function's window). -/
theorem winOkF_of_arms {pows : PowTree} {sigOf : String → HSig} {f : Fn} {H : HCert} {L : List Stmt} {a N : ℕ}
    {st st' : CSt} {l : List (ℕ × Cnt)} {ss : List (List BlkSum)} {cf : Cnt}
    (hj : joinOk (L.drop a) N st ss.flatten cf st' = true)
    (hw : armsWins pows sigOf f H (L.drop a) st ((0, cntOf st) :: l) ss) (hl : lastA l (0, cntOf st) = (N, cf)) :
    winOkF pows sigOf f H ((L.drop a).take (a + 1 - a)) st st' = true := by
  obtain ⟨hg, he, -, hc⟩ := chkC_of_arms hj hw hl
  rw [show a + 1 - a = 1 by omega]
  simp only [winOkF, he, withCx_eq, hc, ngL_eq, hg, decide_true, Bool.and_self, Bool.not_false]

end

end LeanVM.Guest.CoreMode
