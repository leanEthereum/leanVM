/-
  LeanVM.Guest.B2C.CplWalkT

  The completeness walk's table jumps: a `match` follows the arm its selector picks and a
  `dispatch` calls the callee its selector picks, each through the jump table.
-/

module

public import LeanVM.Guest.B2C.CplSpec
public import LeanVM.Guest.B2C.CplWalk

/-!
# Table jumps along a path

A table jump reads its target through the selector: the selector's cell holds `g^k` for the arm
or callee `k` the path takes, so the read is slot `base + k` of the jump table, which holds the
arm's pc (`armsOk`) or the callee's entry (`tcOk`). The target cell holds the same word: the table's
word there (`FrameHolds.arm`, by `armWord`) for a `match`, the callee's entry (`FrameHolds.site`)
for a `dispatch`. So the table read holds (`TgOk`), the jump leaves to the arm's segment, or the
call to the callee, and the walk goes on as for a call (`walk_callZ`) or an arm (`walk_step`).
-/

namespace LeanVM.Guest.B2C

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Exec
open LeanVM.Guest.Check LeanVM.Guest.Memory

@[expose] public section

/-! ## The jump table -/

theorem tbl_tcOk {X : CX} (hG : X.G = glob.restrict X.callees) {base na nr : ℕ} :
    ∀ (fs : List String) (i : ℕ), tcOk X base na nr i fs = true →
    ∀ k (hk : k < fs.length), ∃ pc j', X.G.jt.get (base + (i + k)) = some pc ∧ calleeC X pc = some j' ∧
      fs[k] = (X.G.sig j').name ∧ (X.G.sig j').nargs = na ∧ (X.G.sig j').nret = nr
  | [], _, _, k, hk => absurd hk (Nat.not_lt_zero _)
  | f :: fs, i, h, k, hk => by
    simp only [tcOk, Bool.and_eq_true] at h
    cases k with
    | zero =>
      obtain ⟨h1, -⟩ := h
      split at h1
      · rename_i pc hpc
        split at h1
        · rename_i j' sg hj'
          obtain ⟨-, -, -, rfl, hjc⟩ := calleeS_spec hG hj'
          simp only [Bool.and_eq_true, beq_iff_eq] at h1
          exact ⟨pc, j', by simpa using hpc, hjc, h1.1.1, Nat.eq_of_beq_eq_true h1.1.2,
            Nat.eq_of_beq_eq_true h1.2⟩
        · cases h1
      · cases h1
    | succ k =>
      obtain ⟨pc, j', h1, h2, h3, h4, h5⟩ := tbl_tcOk hG fs (i + 1) h.2 k (by simpa using hk)
      exact ⟨pc, j', by rw [show i + (k + 1) = i + 1 + k by omega]; exact h1, h2, h3, h4, h5⟩

/-! ## Paths through a table jump -/

section Paths

variable {σ : Val}

/-- The callee a `dispatch` calls: the first `k` with the selector `g^(i + k)`. -/
theorem tbl_pick {x : V} {a r : List V} : ∀ (gs : List String) (i : ℕ) {e : List Ev},
    pick σ x a r i gs = .fall e →
      ∃ k, ∃ hk : k < gs.length, σ x = ofK (addressOfIndex (i + k)) ∧ e = [.call gs[k] a r]
  | [], _, _, h => by simp [pick] at h
  | g :: gs, i, e, h => by
    unfold pick at h
    split_ifs at h with hx
    · exact ⟨0, by simp, by simpa using hx, (Out.fall.inj h).symm⟩
    · obtain ⟨k, hk, h1, h2⟩ := tbl_pick gs (i + 1) h
      refine ⟨k + 1, by simpa using hk, by rw [show i + (k + 1) = i + 1 + k by omega]; exact h1, ?_⟩
      rw [List.getElem_cons_succ]
      exact h2

end Paths

theorem tbl_noRetArms : ∀ {arms : List (List Stmt)}, Stmt.noRetArms arms = true →
    ∀ k (hk : k < arms.length), Stmt.noRetList arms[k] = true
  | [], _, k, hk => absurd hk (Nat.not_lt_zero _)
  | a :: as, h, k, hk => by
    simp only [Stmt.noRetArms, Bool.and_eq_true] at h
    cases k with
    | zero => exact h.1
    | succ k => exact tbl_noRetArms h.2 k (by simpa using hk)

/-- Every arm of a `match` the walk accepts ends as its first (`armEnd J succ`), within the most
counts and, if counted separately, its own. -/
theorem tbl_arm {X : CX} {J : ℕ} {succ : List ℕ} {v : V} {se : CW} {key : Option (List Cnt)}
    {a0 : List Stmt} {as : List (List Stmt)} {t0 : ℕ} {ts : List ℕ} {s0 : CW} {c0 : Cnt} {u0 : ℕ}
    {c : Cnt} {u : ℕ} (hs0 : segAtC X t0 se = some s0)
    (h0 : armEnd J succ (cw X a0 { s0 with book := fileB X.loc X.fs a0 se.book, tg := armTg X v 0 ++ s0.tg }) = some (c0, u0))
    (hk0 : armChkK key 0 c0 = true)
    (ha : cwArms X J succ v se key as ts c0 u0 1 = some (c, u)) (hl : ts.length = as.length) :
    ∀ k (hk : k < (a0 :: as).length), ∃ (hk' : k < (t0 :: ts).length) (s : CW) (ck : Cnt) (uk : ℕ),
      segAtC X (t0 :: ts)[k] se = some s ∧
      armEnd J succ (cw X (a0 :: as)[k] { s with book := fileB X.loc X.fs (a0 :: as)[k] se.book, tg := armTg X v k ++ s.tg }) = some (ck, uk) ∧
      (∀ op, ck.get op ≤ c.get op) ∧ armChkK key k ck = true := by
  obtain ⟨-, hc, hks⟩ := cwArms_spec ha
  intro k hk
  cases k with
  | zero => exact ⟨by simp, s0, c0, u0, hs0, h0, hc, hk0⟩
  | succ k =>
    have hk1 : k < as.length := by simpa using hk
    obtain ⟨s, ck, uk, h1, h2, h3, h4⟩ := hks k hk1 (hl ▸ hk1)
    refine ⟨by simp; omega, s, ck, uk, h1, ?_, h3, by rw [Nat.add_comm]; exact h4⟩
    simp only [List.getElem_cons_succ]
    rw [Nat.add_comm k 1]
    exact h2

theorem tbl_nth_ofList (cs : List (List ℕ)) (k : ℕ) (op : Opcode) :
    (listElementOrDefault (cs.map Cnt.ofList) k Cnt.zero).get op = (listElementOrDefault cs k
        []).getD (opIdx op) 0 := by
  have h : listElementOrDefault (cs.map Cnt.ofList) k Cnt.zero = Cnt.ofList (listElementOrDefault cs
      k []) := by
    induction cs generalizing k with
    | nil => rfl
    | cons c cs ih =>
      cases k with
      | zero => rfl
      | succ k => exact ih k
  rw [h]
  cases op <;> simp only [Cnt.ofList, Cnt.get, opIdx, nth_getD]

/-- The arm a `match` takes, and the separately counted arms its path passes. -/
theorem tbl_walkArmsC {σ : Val} {acs : List (ℕ × List (List ℕ))} {key : Option (List (List ℕ))} {x : V} :
    ∀ (arms : List (List Stmt)) (i : ℕ) {e : List Ev}, walkArms σ x i arms = .fall e →
      ∃ k, ∃ hk : k < arms.length, σ x = ofK (addressOfIndex (i + k)) ∧ walk σ arms[k] = .fall e ∧
        costArms acs σ x key i arms = (fun op ↦ match key with
          | some cs => (listElementOrDefault cs (i + k) []).getD (opIdx op) 0
          | none => 0) + costW acs σ arms[k]
  | [], _, _, h => by simp [walkArms] at h
  | a :: as, i, e, h => by
    unfold walkArms at h
    split_ifs at h with hx
    · refine ⟨0, by simp, by simpa using hx, h, ?_⟩
      simp only [costArms, hx, ↓reduceIte, List.getElem_cons_zero]
      rfl
    · obtain ⟨k, hk, h1, h2, h3⟩ := tbl_walkArmsC as (i + 1) h
      refine ⟨k + 1, by simpa using hk, by rw [show i + (k + 1) = i + 1 + k by omega]; exact h1, ?_, ?_⟩
      · rw [List.getElem_cons_succ]
        exact h2
      · simp only [costArms, hx, ↓reduceIte, List.getElem_cons_succ]
        rw [h3, show i + 1 + k = i + (k + 1) by omega]

section Walk

variable {κ : ℕ} {L : MemoryImage κ} {j fp : ℕ} {σ : Val} {es : List Ev} {vs : List V}
  {kfps : List ℕ} {hdr : E × E} {ck : List (Opcode → ℕ)} {segs : List Exec.Seg} {X : CX}
  {wJ : ℕ} {wenv : Trie Sym}

/-- Entering the join `J` with counts `c`: the run is at its segment. -/
theorem tbl_segJ (H : WH L j fp X segs wJ wenv σ es vs kfps hdr ck) {J : ℕ} {se sj : CW}
    (h : segAtC X J se = some sj) (hok : CWOk L fp X se) (he : EnvAt L fp X wJ wenv J) {W0 : Registers K}
    {n : ℕ} {xc : Opcode → ℕ} {c : Cnt} (u : ℕ) {cr : Opcode → ℕ}
    (hr : RunC guestProgram L W0 ⟨addressOfIndex (X.entry + J), addressOfIndex fp⟩ cr)
    (hc : ∀ op, cr op ≤ c.get op + xc op + ksum ck n op)
    (hnm : ∀ n, se.nm.testBit n = true → V.n n ∈ namedOf (coreOf j).params es vs) :
    PosZ H { sj with cnt := c, uq := u } W0 n xc := by
  obtain ⟨s, hs, hst, rfl⟩ := segAtC_eq h
  have h' : segAtC X J { se with cnt := c, uq := u } =
      some ⟨s, s.items, se.book, se.fr, se.tg, se.nx, c, u, some J, se.nm⟩ := by
    unfold segAtC
    rw [hs]
    simp [hst]
  exact (segAtC_pos H h' hok.book hok.fr hok.tg hok.nx he hr hc hnm).1

theorem walk_matchNilZ (H : WH L j fp X segs wJ wenv σ es vs kfps hdr ck) (v : V) (ss : List Stmt)
    (st : CW) : WGood H (.match_ v [] :: ss) st := by
  intro ebef eaft o W0 pre xc hw hes hs hshape hp hok
  simp [cw, RC.ok] at hok

/-- What the walk of `ss` from a position gives when it ends with `r`. -/
abbrev WOut (_H : WH L j fp X segs wJ wenv σ es vs kfps hdr ck) (r : RC) (o : Out) (ebef : List Ev)
    (W0 : Registers K) (xc : Opcode → ℕ) (ss : List Stmt) : Prop :=
  (∀ J c u, r = .join J c u → ∃ es', o = .fall es' ∧
    Arr L fp X wJ wenv ck W0 J c (calls (ebef ++ es')).length (xc + costW X.acs σ ss)) ∧
  (∀ J m c u, r = .mid J m c u → ∃ es', o = .fall es' ∧
    ArrMid L fp X ck W0 J m c (calls (ebef ++ es')).length (xc + costW X.acs σ ss)) ∧
  (r = .done → ∃ es' vs', o = .ret es' vs' ∧
    FinZ L j fp X ck W0 (calls (ebef ++ es')).length (xc + costW X.acs σ ss) vs') ∧
  (∀ o' succ c u, r = .chain o' succ c u → ∃ es', o = .fall es' ∧
    ArrCh L fp X wJ wenv ck W0 o' succ c (calls (ebef ++ es')).length (xc + costW X.acs σ ss))

theorem arr_monoX {W0 : Registers K} {J n : ℕ} {c c' : Cnt} {x x' : Opcode → ℕ}
    (h : Arr L fp X wJ wenv ck W0 J c n x) (hle : ∀ op, c.get op + x op ≤ c'.get op + x' op) :
    Arr L fp X wJ wenv ck W0 J c' n x' := by
  obtain ⟨⟨cr, hcr, hc⟩, he⟩ := h
  exact ⟨⟨cr, hcr, fun op ↦ by have := hc op; have := hle op; omega⟩, he⟩

theorem tgOk_append {l1 l2 : List (ℕ × ℕ × ℕ)} (h1 : TgOk L fp l1) (h2 : TgOk L fp l2) :
    TgOk L fp (l1 ++ l2) := fun q hq ↦ (List.mem_append.mp hq).elim (h1 q) (h2 q)

theorem chainPre_nm {st st' : CW} (h : st.nm = st'.nm) (v : V) (m : ℕ) :
    chainPre X st v m = chainPre X st' v m := by
  unfold chainPre selOk
  rw [h]

/-- **The arms of a `match`** from its dispatch state `se`, the run arriving at the arm the
selector picks: the arm walks to the join and the walk goes on, or, chained, to the next
`match`'s table jump. -/
theorem tbl_armsZ (H : WH L j fp X segs wJ wenv σ es vs kfps hdr ck) {v : V} {a0 : List Stmt}
    {as : List (List Stmt)} {ss : List Stmt}
    (iha : ∀ k (hk : k < (a0 :: as).length) st, WGood H (a0 :: as)[k] st)
    (ih : ∀ st, WGood H ss st) {ebef eaft : List Ev} {o : Out} {W0 : Registers K} {pre : List Stmt}
    {xc : Opcode → ℕ} (hw : walk σ (.match_ v (a0 :: as) :: ss) = o) (hes : es = ebef ++ o.evs ++ eaft)
    (hs : o ≠ .stuck)
    (hshape : Stmt.noRetList (.match_ v (a0 :: as) :: ss) = true ∨ (lastOkC (.match_ v (a0 :: as) :: ss) = true ∧
      eaft = [] ∧ (coreOf j).body = pre ++ .match_ v (a0 :: as) :: ss))
    {se s0 : CW} {t0 : ℕ} {ts : List ℕ} (hok0 : CWOk L fp X se)
    (hnm0 : ∀ n, se.nm.testBit n = true → V.n n ∈ namedOf (coreOf j).params es vs)
    (hvn : v = V.n v.idx) (hl : ts.length = as.length) (hpre : chainPre X se v (as.length + 1) = true)
    (harr : ∀ k (hk : k < (t0 :: ts).length), σ v = ofK (addressOfIndex k) → ∃ cr,
      RunC guestProgram L W0 ⟨addressOfIndex (X.entry + (t0 :: ts)[k]), addressOfIndex fp⟩ cr ∧
      (∀ op, cr op ≤ se.cnt.get op + xc op + ksum ck (calls ebef).length op) ∧
      EnvAt L fp X wJ wenv (t0 :: ts)[k])
    (hs0 : segAtC X t0 (armSt (armKeyD X.acs v.idx) se) = some s0) {r : RC}
    (hr : (∃ J c0 u0 c u sj,
        cw X a0 { s0 with book := fileB X.loc X.fs a0 se.book, tg := armTg X v 0 ++ s0.tg } = .join J c0 u0 ∧
        armChkK (armKeyD X.acs v.idx) 0 c0 = true ∧
        cwArms X J [] v (armSt (armKeyD X.acs v.idx) se) (armKeyD X.acs v.idx) as ts c0 u0 1 = some (c, u) ∧
        segAtC X J se = some sj ∧
        r = cw X ss { sj with cnt := armCnt (armKeyD X.acs v.idx) se c, uq := u }) ∨
       (∃ o' succ c0 u0 c u,
        cw X a0 { s0 with book := fileB X.loc X.fs a0 se.book, tg := armTg X v 0 ++ s0.tg } = .chain o' succ c0 u0 ∧
        armChkK (armKeyD X.acs v.idx) 0 c0 = true ∧ ss = [] ∧ succ ≠ [] ∧
        cwArms X o' succ v (armSt (armKeyD X.acs v.idx) se) (armKeyD X.acs v.idx) as ts c0 u0 1 = some (c, u) ∧
        r = .chain o' succ (armCnt (armKeyD X.acs v.idx) se c) u))
    (hok : r.ok = true) : WOut H r o ebef W0 xc (.match_ v (a0 :: as) :: ss) := by
  have hkr : armKeyD X.acs v.idx = (armRaw X.acs v.idx).map (fun cs ↦ cs.map Cnt.ofList) := rfl
  generalize armKeyD X.acs v.idx = key at hs0 hr hkr
  have hnr : Stmt.noRet (.match_ v (a0 :: as)) = true := by
    rcases hshape with h | ⟨h, -, -⟩
    · simp only [Stmt.noRetList, Bool.and_eq_true] at h
      exact h.1
    · exact (lastOkC_cons h fun vs hv ↦ by cases hv).1
  -- the arm the path takes
  have hw0 : o = (walkArms σ v 0 (a0 :: as)).seq (walk σ ss) := by rw [← hw]; rfl
  obtain ⟨e1, hwa⟩ : ∃ e1, walkArms σ v 0 (a0 :: as) = .fall e1 := by
    rcases walkArms_noRetC (σ := σ) v (a0 :: as) 0 hnr with h | h
    · exact h
    · exact absurd (show o = .stuck by rw [hw0, h]; rfl) hs
  obtain ⟨k, hka, hvk, hwk, hcost⟩ :=
    tbl_walkArmsC (acs := X.acs) (key := armRaw X.acs v.idx) (a0 :: as) 0 hwa
  rw [Nat.zero_add] at hvk hcost
  have hw' : o = (walk σ ss).pre e1 := by rw [hw0, hwa]; rfl
  have hst' : walk σ ss ≠ .stuck := fun h ↦ hs (by rw [hw', h]; rfl)
  have hes2 : es = ebef ++ e1 ++ ((walk σ ss).evs ++ eaft) := by
    rw [hes, hw', walk_pre_evs hst']
    simp
  have hkt : k < (t0 :: ts).length := by simpa [hl] using hka
  obtain ⟨cr, hcr, hcle, henvk⟩ := harr k hkt hvk
  -- the arm, its counts restarted if counted separately
  have hse'b : (armSt key se).book = se.book := by cases key <;> rfl
  have hse'n : (armSt key se).nm = se.nm := by cases key <;> rfl
  have hok0' : CWOk L fp X (armSt key se) := by
    cases key <;> exact ⟨hok0.env, hok0.book, hok0.fr, hok0.tg, hok0.nx⟩
  have hcnt' : ∀ op, (armSt key se).cnt.get op ≤ se.cnt.get op := by
    intro op
    cases key
    · exact le_rfl
    · cases op <;> exact Nat.zero_le _
  have hnm0' : ∀ n, (armSt key se).nm.testBit n = true → V.n n ∈ namedOf (coreOf j).params es vs := by
    rw [hse'n]; exact hnm0
  let xa : Opcode → ℕ := fun op ↦ xc op + (se.cnt.get op - (armSt key se).cnt.get op)
  have hc1 : cost1 X.acs σ (.match_ v (a0 :: as)) = costArms X.acs σ v (armRaw X.acs v.idx) 0 (a0 :: as) :=
    rfl
  -- the counts: an arm's within the match's
  have hcnt : ∀ (c ck' : Cnt), (∀ op, ck'.get op ≤ c.get op) → armChkK key k ck' = true → ∀ op,
      ck'.get op + (xa op + costW X.acs σ (a0 :: as)[k] op) ≤
        (armCnt key se c).get op + (xc + cost1 X.acs σ (.match_ v (a0 :: as))) op := by
    intro c ck' hckc hchk op
    have h2 := hckc op
    rw [hc1, hcost]
    simp only [Pi.add_apply, xa]
    cases key with
    | none =>
      have hraw : armRaw X.acs v.idx = none := Option.map_eq_none_iff.mp hkr.symm
      rw [hraw]
      simp only [armCnt, armSt, Nat.sub_self, Nat.add_zero]
      omega
    | some cs' =>
      obtain ⟨cs, hraw, rfl⟩ := Option.map_eq_some_iff.mp hkr.symm
      rw [hraw]
      have h3 := Cnt.le_spec hchk op
      rw [tbl_nth_ofList] at h3
      simp only [armCnt, armSt]
      have h4 : ({ se with cnt := Cnt.zero } : CW).cnt.get op = 0 := by cases op <;> rfl
      rw [h4, Nat.sub_zero]
      omega
  -- the arm walked from its segment
  have harm : ∀ (Jx : ℕ) (sx : List ℕ) (c0 : Cnt) (u0 : ℕ) (c : Cnt) (u : ℕ),
      armEnd Jx sx (cw X a0 { s0 with book := fileB X.loc X.fs a0 se.book, tg := armTg X v 0 ++ s0.tg }) =
        some (c0, u0) → armChkK key 0 c0 = true →
      cwArms X Jx sx v (armSt key se) key as ts c0 u0 1 = some (c, u) →
      ∃ ckk ukk r', armEnd Jx sx r' = some (ckk, ukk) ∧ (∀ op, ckk.get op ≤ c.get op) ∧
        armChkK key k ckk = true ∧ WOut H r' (.fall e1) ebef W0 xa (a0 :: as)[k] := by
    intro Jx sx c0 u0 c u h0 hck0 ha
    obtain ⟨hkt', s, ckk, ukk, hsk, hcwk, hckc, hchk⟩ :=
      tbl_arm hs0 (by rw [hse'b]; exact h0) hck0 ha hl k hka
    obtain ⟨hps, -, -, -, -⟩ := segAtC_pos H (xc := xa) (n := (calls ebef).length) hsk hok0'.book
      hok0'.fr hok0'.tg hok0'.nx henvk hcr
      (fun op ↦ by have := hcle op; have := hcnt' op; simp only [xa]; omega) hnm0'
    have hatoms : ∀ a, Stmt.atom a ∈ (a0 :: as)[k] → Ev.atom a ∈ es := fun a ha' ↦ by
      rw [hes2]
      exact List.mem_append_left _ (List.mem_append_right _ (atom_on_pathC hwk ha'))
    have hB := fileB_ok H.frame H.loc H.hev _ (armSt key se).book hok0'.book hatoms
    rw [← H.fs] at hB
    have hsnm : s.nm = se.nm := by
      obtain ⟨_, _, _, hs⟩ := segAtC_eq hsk
      rw [hs, hse'n]
    have htgk : TgOk L fp (armTg X v k) :=
      armTg_ok H hps hvn hvk hka (by rw [chainPre_nm hsnm]; exact hpre)
    have hpk : PosZ H { s with book := fileB X.loc X.fs (a0 :: as)[k] (armSt key se).book, tg := armTg X v k ++ s.tg } W0 (calls ebef).length xa :=
      ⟨hps.seg, ⟨hps.ok.env, hB, hps.ok.fr, tgOk_append htgk hps.ok.tg, hps.ok.nx⟩, hps.run, hps.fresh,
        hps.nm, hps.ix⟩
    have hokk : (cw X (a0 :: as)[k] { s with book := fileB X.loc X.fs (a0 :: as)[k] (armSt key se).book, tg := armTg X v k ++ s.tg }).ok = true := armEnd_ok hcwk
    exact ⟨ckk, ukk, _, hcwk, hckc, hchk, iha k hka _ ebef ((walk σ ss).evs ++ eaft) (.fall e1) W0 [] xa
      hwk hes2 (fun h ↦ by cases h) (Or.inl (tbl_noRetArms hnr k hka)) hpk hokk⟩
  rcases hr with ⟨J, c0, u0, c, u, sj, h0, hck0, ha, hsj, hcw⟩ |
    ⟨o', succ, c0, u0, c, u, h0, hck0, rfl, hsn, ha, hcw⟩
  · -- the join
    obtain ⟨ckk, ukk, r', hr', hckc, hchk, hj1, -, -, -⟩ :=
      harm J [] c0 u0 c u (by simp [armEnd, h0]) hck0 ha
    obtain ⟨es', hfe, hArr⟩ := hj1 J ckk ukk (armEnd_join hr')
    obtain rfl := Out.fall.inj hfe
    obtain ⟨⟨crj, hcrj, hcj⟩, henvJ⟩ := hArr
    have hp'' := tbl_segJ H hsj hok0 henvJ u hcrj (c := armCnt key se c) (n := (calls (ebef ++ e1)).length)
      (xc := xc + cost1 X.acs σ (.match_ v (a0 :: as))) (fun op ↦ by
        have h1 := hcj op
        have h2 := hcnt c ckk hckc hchk op
        simp only [Pi.add_apply] at h1 h2 ⊢
        omega) hnm0
    exact walk_step H ih hnr (show walk1 σ (.match_ v (a0 :: as)) = .fall e1 from hwa) hw hes hs
      hshape hp'' hcw (hcw ▸ hok)
  · -- chained: the arm ends in the next `match`'s table jump
    subst hcw
    obtain ⟨ckk, ukk, r', hr', hckc, hchk, -, -, -, hch⟩ :=
      harm o' succ c0 u0 c u (by simp [armEnd, h0, hsn]) hck0 ha
    obtain ⟨es', hfe, hA⟩ := hch o' succ ckk ukk (armEnd_chain hsn hr')
    obtain rfl := Out.fall.inj hfe
    refine ⟨fun J c' u' hj ↦ (by cases hj), fun J m c' u' hj ↦ (by cases hj), fun hj ↦ (by cases hj),
      fun o2 s2 c2 u2 hj ↦ ?_⟩
    simp only [RC.chain.injEq] at hj
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hj
    refine ⟨e1, by rw [hw']; simp [walk, Out.pre], fun e he hoe ↦ arr_monoX (hA.1 e he hoe) fun op ↦ ?_, hA.2⟩
    have h2 := hcnt c ckk hckc hchk op
    simp only [costW, Pi.add_apply, Pi.zero_apply, Nat.add_zero] at h2 ⊢
    omega

/-- **A `match`**: the run jumps through the table to the arm the path takes, walks it to the
join, and goes on; or, chained, to the next `match`'s table jump. -/
theorem walk_matchZ (H : WH L j fp X segs wJ wenv σ es vs kfps hdr ck) (v : V) (a0 : List Stmt)
    (as : List (List Stmt)) (ss : List Stmt) (st : CW)
    (iha : ∀ k (hk : k < (a0 :: as).length) st, WGood H (a0 :: as)[k] st)
    (ih : ∀ st, WGood H ss st) : WGood H (.match_ v (a0 :: as) :: ss) st := by
  intro ebef eaft o W0 pre xc hw hes hs hshape hp hok
  obtain ⟨t, ft, t0, ts, base, se, s0, hk, hsu, htb, hself, hl, hvn, hsel, hin,
    harm, hao, hpre, hse, hs0, hr⟩ := cw_match hok
  have hfr := inFrame_mem hin
  have hv2 := hfr _ List.mem_cons_self
  have ht2 := hfr t (by simp)
  have hcv : rdc L fp (X.loc.cell v) = some (σ v) :=
    val_cell H.frame H.loc (hp.sel hvn hsel) hv2.1 (H.fs ▸ hv2.2)
  obtain ⟨⟨a1, a2, a3⟩, ham, hae⟩ := List.any_eq_true.mp harm
  simp only [Bool.and_eq_true] at hae
  obtain ⟨⟨ha1, ha2⟩, ha3⟩ := hae
  have e1' : a1 = v.idx := Nat.eq_of_beq_eq_true ha1
  have e2' : a2 = t := Nat.eq_of_beq_eq_true ha2
  have e3' : a3 = base := Nat.eq_of_beq_eq_true ha3
  subst e1' e2' e3'
  rw [H.arms] at ham
  have harmw : L.read (addressOfIndex (fp + a2)) = some (armWord σ v.idx a3) :=
    H.frame.arm _ ham ht2.1 (H.fs ▸ ht2.2)
  -- the selector's arm, if it has one
  have hsel' : ∀ k (hkt : k < (t0 :: ts).length), σ v = ofK (addressOfIndex k) →
      glob.jt.get (a3 + k) = some (X.entry + (t0 :: ts)[k]) ∧
      L.read (addressOfIndex (fp + a2)) = some (ofK (addressOfIndex (X.entry + (t0 :: ts)[k]))) := by
    intro k hkt hvk
    have hslot := tbl_armsOk (t0 :: ts) 0 hao k hkt
    rw [Nat.zero_add, H.G, Glob.restrict_jt] at hslot
    obtain ⟨hfind, hlt⟩ := tbl_slot H.jt H.tab hslot
    have hσk : σ (V.n v.idx) = ofK (addressOfIndex k) := by rw [← hvn]; exact hvk
    refine ⟨hslot, ?_⟩
    rw [harmw, tbl_armWord hσk hfind hlt]
  -- the table read holds if the path takes an arm (else the walk is stuck)
  have hnr : Stmt.noRet (.match_ v (a0 :: as)) = true := by
    rcases hshape with h | ⟨h, -, -⟩
    · simp only [Stmt.noRetList, Bool.and_eq_true] at h
      exact h.1
    · exact (lastOkC_cons h fun vs hv ↦ by cases hv).1
  have hw0 : o = (walkArms σ v 0 (a0 :: as)).seq (walk σ ss) := by rw [← hw]; rfl
  obtain ⟨e1, hwa⟩ : ∃ e1, walkArms σ v 0 (a0 :: as) = .fall e1 := by
    rcases walkArms_noRetC (σ := σ) v (a0 :: as) 0 hnr with h | h
    · exact h
    · exact absurd (show o = .stuck by rw [hw0, h]; rfl) hs
  obtain ⟨k0, hka0, hvk0, -, -⟩ :=
    tbl_walkArmsC (acs := X.acs) (key := armRaw X.acs v.idx) (a0 :: as) 0 hwa
  rw [Nat.zero_add] at hvk0
  have hkt0 : k0 < (t0 :: ts).length := by simpa [hl] using hka0
  obtain ⟨hslot0, harm0⟩ := hsel' k0 hkt0 hvk0
  have htg1 : TgOk L fp ((a2, X.loc.cell v, a3) :: st.tg) := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · refine ⟨σ v, ofK (addressOfIndex (X.entry + (t0 :: ts)[k0])), hcv,
        by rw [hvk0]; exact isInK_ofK _, by rw [gpow_addC] at harm0; exact harm0, isInK_ofK _, ?_⟩
      show L.read ((σ v).limb 0 * addressOfIndex a3) = some (ofK (addressOfIndex (X.entry + (t0 ::
          ts)[k0])))
      rw [hvk0, limb_ofK0, ← gpow_addC, Nat.add_comm k0 a3]
      exact H.jt _ _ hslot0
    · exact hp.ok.tg x hx
  have hp0 : PosZ H { st with tg := (a2, X.loc.cell v, a3) :: st.tg } W0 (calls ebef).length xc :=
    ⟨hp.seg, ⟨hp.ok.env, hp.ok.book, hp.ok.fr, htg1, hp.ok.nx⟩, hp.run, hp.fresh, hp.nm, hp.ix⟩
  -- the jump to the arm
  obtain ⟨hseg, hbk, hfr', htg, hnx, -, hreach⟩ := endAtC_reach H hp0 hse
  simp only at hseg hbk hfr' htg hnx hreach
  have hft : ft.Is L (addressOfIndex fp) (addressOfIndex fp) := self_is H hself
  have hok0 : CWOk L fp X se :=
    ⟨by rw [hseg]; exact hp.ok.env, by rw [hbk]; exact hp.ok.book, by rw [hfr']; exact hp.ok.fr,
      by rw [htg]; exact htg1, by rw [hnx]; exact hp.ok.nx⟩
  have hnm0 : ∀ n, se.nm.testBit n = true → V.n n ∈ namedOf (coreOf j).params es vs := by
    rw [endAtC_nm hse]
    exact hp.nm
  refine tbl_armsZ H iha ih hw hes hs hshape hok0 hnm0 hvn hl
    (by rw [chainPre_nm (endAtC_nm hse)]; exact hpre) (fun k hkt hvk ↦ ?_) hs0 hr hok
  obtain ⟨-, harmk⟩ := hsel' k hkt hvk
  obtain ⟨cr, hcr, hcle, henv⟩ := hreach ⟨addressOfIndex (X.entry + (t0 :: ts)[k]), addressOfIndex
      fp⟩ (by
    rw [hk]
    exact ⟨_, _, ⟨_, by rw [← gpow_addC]; exact harmk, isInK_ofK _, by rw [limb_ofK0]⟩, hft, rfl⟩)
  have htk : (t0 :: ts)[k] ∈ st.seg.exit.succ := by rw [hsu]; exact List.getElem_mem hkt
  exact ⟨cr, hcr, hcle, envAt_of_exit H hp.seg (H.exits _ hp.seg _ (Or.inl rfl)) htk henv⟩

/-- **An entered `match`**: the run arrives, through the table jump ending the part before, at
the arm the path takes, walks it to the join and goes on, or, chained, to the next `match`'s
table jump. -/
theorem walk_enterZ (H : WH L j fp X segs wJ wenv σ es vs kfps hdr ck) (hW : ∀ ss st, WGood H ss st)
    {o : ℕ} {succ : List ℕ} {se : CW} {ss : List Stmt} {ebef eaft : List Ev} {out : Out}
    {W0 : Registers K} {pre : List Stmt} {xc : Opcode → ℕ} (hw : walk σ ss = out)
    (hes : es = ebef ++ out.evs ++ eaft) (hs : out ≠ .stuck)
    (hshape : Stmt.noRetList ss = true ∨ (lastOkC ss = true ∧ eaft = [] ∧ (coreOf j).body = pre ++ ss))
    (hok0 : CWOk L fp X se) (hnm0 : ∀ n, se.nm.testBit n = true → V.n n ∈ namedOf (coreOf j).params es vs)
    (harr : ArrCh L fp X wJ wenv ck W0 o succ se.cnt (calls ebef).length xc)
    (hok : (cwE X o succ se ss).ok = true) : WOut H (cwE X o succ se ss) out ebef W0 xc ss := by
  obtain ⟨v, a0, as, ss', t0, ts, s0, rfl, rfl, rfl, hvn, hsel, hl, hin, hpre, hs0, hr⟩ := cwE_ok hok
  have hfr := inFrame_mem hin
  have hv2 := hfr _ List.mem_cons_self
  have hnamed : v ∈ namedOf (coreOf j).params es vs := by
    unfold selOk at hsel
    rw [hvn]
    rcases Bool.or_eq_true_iff.mp hsel with h | h
    · exact H.named _ h
    · rw [bitK_eq] at h
      exact hnm0 _ h
  have hcv : rdc L fp (X.loc.cell v) = some (σ v) :=
    val_cell H.frame H.loc hnamed hv2.1 (H.fs ▸ hv2.2)
  refine tbl_armsZ H (fun k hk st ↦ hW _ st) (hW ss') hw hes hs hshape hok0 hnm0 hvn hl hpre
    (fun k hkt hvk ↦ ?_) hs0 hr hok
  obtain ⟨⟨cr, hcr, hc⟩, he⟩ := harr.1 k hkt (by rw [hcv, hvk])
  exact ⟨cr, hcr, hc, he⟩

/-- **A `dispatch`**: the run calls, through the table, the callee the path takes, and goes on
at the return point. -/
theorem walk_dispatchZ (H : WH L j fp X segs wJ wenv σ es vs kfps hdr ck) (v : V) (fs : List String)
    (args rets : List V) (ss : List Stmt) (st : CW) (ih : ∀ st, WGood H ss st) :
    WGood H (.dispatch v fs args rets :: ss) st := by
  intro ebef eaft o W0 pre xc hw hes hs hshape hp hok
  obtain ⟨t, q, r, base, sr, hk, -, hvn, hsel, htc, hle, hsu, hsite, -, -, -, hin, hself, haf, hcw⟩ :=
    cw_dispatch hok
  obtain ⟨se, s', hse, hs', rfl⟩ := afterC_ok haf
  -- the callee the path takes
  have hw0 : o = (pick σ v args rets 0 fs).seq (walk σ ss) := by rw [← hw]; rfl
  obtain ⟨e1, hpk⟩ : ∃ e1, pick σ v args rets 0 fs = .fall e1 := by
    rcases pick_noRetC (σ := σ) (x := v) (a := args) (r := rets) fs 0 with h | h
    · exact h
    · exact absurd (show o = .stuck by rw [hw0, h]; rfl) hs
  obtain ⟨k, hkf, hvk, rfl⟩ := tbl_pick fs 0 hpk
  rw [Nat.zero_add] at hvk
  obtain ⟨pc, j', hslot, hj, hf, -, -⟩ := tbl_tcOk H.G fs 0 htc k hkf
  rw [Nat.zero_add, H.G, Glob.restrict_jt] at hslot
  obtain ⟨hj1, hj2, he⟩ := calleeC_some H.G hj
  have hfn : fs[k] = (coreOf j').name := by rw [hf, calleeC_sig H.G hj]; rfl
  have hw' : o = (walk σ ss).pre [.call fs[k] args rets] := by rw [hw0, hpk]; rfl
  have hst' : walk σ ss ≠ .stuck := fun h ↦ hs (by rw [hw', h]; rfl)
  have hes2 : es = ebef ++ Ev.call fs[k] args rets :: ((walk σ ss).evs ++ eaft) := by
    rw [hes, hw', walk_pre_evs hst']
    simp
  set n := (calls ebef).length with hn
  have hci : (calls es)[n]? = some ⟨fs[k], args, rets, true⟩ := by rw [hes2]; exact calls_at rfl
  obtain ⟨s0, hs0, hq0, hr0, ht0⟩ := siteOk_spec hsite
  have hnl := notLast H hci fun h ↦ hself _ (List.getElem_mem hkf) (h.trans H.name.symm)
  have hfr := inFrame_mem hin
  have hin' : inFrame X.fs (s0.q :: args.map X.loc.cell) = true := by
    rw [hq0]
    simp only [inFrame, Bool.and_eq_true] at hin ⊢
    obtain ⟨-, hq, -, h2⟩ := hin
    refine ⟨hq, ?_⟩
    rw [List.map_append, inFrame_append, Bool.and_eq_true] at h2
    exact h2.1
  obtain ⟨kfp, hkfp, hq, hfcs, hret⟩ := call_frame H hci hj1 hj2 hfn hs0 hnl hin' (selfs := [])
    (fun o ho ↦ by cases ho)
  rw [hq0] at hq
  rw [hr0] at hfcs hret
  obtain ⟨-, hkid⟩ := H.kids
  obtain ⟨⟨rr, hrr, hrun⟩, hrets⟩ := hkid n _ kfp hci hkfp rfl
  rw [hret] at hrr
  obtain rfl := Option.some.inj hrr
  -- the table read
  have ht2 := hfr t List.mem_cons_self
  have hent : entryOf fs[k] = pc := by rw [hfn, entryOf_callee hj1 hj2, he]
  have htgt : rdc L fp t = some (ofK (addressOfIndex pc)) := by
    have := (H.frame.site n _ kfp s0 hci hkfp (by rw [← siteC_eq H.sites]; exact hs0)).2
      (by rw [ht0]; have := ht2.1; omega) (by rw [ht0]; exact ht2.1) (by rw [ht0, ← H.fs]; exact ht2.2)
    rw [ht0, gpow_addC] at this
    rw [← hent]
    exact this
  have hv2 := hfr (X.loc.cell v) (by simp)
  have hcv : rdc L fp (X.loc.cell v) = some (σ v) :=
    val_cell H.frame H.loc (hp.sel hvn hsel) hv2.1 (H.fs ▸ hv2.2)
  have htg1 : TgOk L fp ((t, X.loc.cell v, base) :: st.tg) := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · refine ⟨σ v, ofK (addressOfIndex pc), hcv,
        by rw [hvk]; exact isInK_ofK _, htgt, isInK_ofK _, ?_⟩
      show L.read ((σ v).limb 0 * addressOfIndex base) = some (ofK (addressOfIndex pc))
      rw [hvk, limb_ofK0, ← gpow_addC, Nat.add_comm k base]
      exact H.jt _ _ hslot
    · exact hp.ok.tg x hx
  have hp0 : PosZ H { st with tg := (t, X.loc.cell v, base) :: st.tg } W0 n xc :=
    ⟨hp.seg, ⟨hp.ok.env, hp.ok.book, hp.ok.fr, htg1, hp.ok.nx⟩, hp.run, hp.fresh, hp.nm, hp.ix⟩
  -- the call
  have hp1 := posZ_fr H hp0 hq hfcs
  obtain ⟨hseg, hbk, hfr', htg, hnx, -, hreach⟩ := endAtC_reach H hp1 hse
  simp only at hseg hbk hfr' htg hnx hreach
  obtain ⟨cr, hcr, hcle, henv⟩ := hreach ⟨addressOfIndex pc, addressOfIndex kfp⟩ (by
    rw [hk]
    exact ⟨_, addressOfIndex pc, hq, isInK_ofK _, ⟨_, htgt, isInK_ofK _,
        by rw [limb_ofK0]⟩, by simp⟩)
  rw [hent] at hrun
  have hgr : addressOfIndex r = addressOfIndex (X.entry + (r - X.entry)) :=
      by rw [Nat.add_sub_cancel' hle]
  have hrun2 : RunC guestProgram L W0 ⟨addressOfIndex (X.entry + (r - X.entry)), addressOfIndex fp⟩ (cr + ck.getD n 0) := by
    rw [← hgr]
    exact hcr.trans hrun
  have henvR : EnvAt L fp X wJ wenv (r - X.entry) :=
    envAt_of_exit H hp.seg (H.exits _ hp.seg _ (Or.inl rfl)) (by rw [hsu]; simp) henv
  obtain ⟨hps, -⟩ :=
    segAtC_pos H (xc := xc) hs' (by rw [hbk]; exact hp.ok.book) (by rw [hfr']; exact hp1.ok.fr)
      (by rw [htg]; exact htg1) (by rw [hnx]; exact hp.ok.nx) henvR (n := n + 1) hrun2
      (fun op ↦ by rw [Pi.add_apply, ksum_succ]; have := hcle op; omega)
      (by rw [endAtC_nm hse]; exact hp.nm)
  have hc1 : (calls (ebef ++ [.call fs[k] args rets])).length = n + 1 := calls_append_one rfl
  refine walk_step H ih rfl
    (show walk1 σ (.dispatch v fs args rets) = .fall [.call fs[k] args rets] from hpk) hw hes hs
    hshape ?_ hcw hok
  rw [hc1]
  refine ⟨hps.seg, ⟨hps.ok.env, hps.ok.book, fun x hx ↦ ?_, hps.ok.tg, hps.ok.nx⟩, hps.run,
    fun t' ht' ↦ ?_, fun n hn ↦ ?_, hps.ix⟩
  · rcases List.mem_cons.mp hx with rfl | hx
    · refine ⟨kfp, hq, fun p hp' ↦ ?_⟩
      rcases List.mem_append.mp hp' with hp' | hp'
      · exact hfcs p hp'
      · obtain ⟨i, hi, rfl⟩ := argFC_mem hp'
        have hv : X.loc.cell rets[i] ∈ (args ++ rets).map X.loc.cell :=
          List.mem_map.mpr ⟨_, List.mem_append_right _ (List.getElem_mem hi), rfl⟩
        have hc := hfr _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hv)))
        have hm : Ev.call fs[k] args rets ∈ es := by rw [hes2]; simp
        refine ⟨σ rets[i], val_cell H.frame H.loc (uses_named hm (by simp [Ev.uses, List.getElem_mem]))
          hc.1 (H.fs ▸ hc.2), ?_⟩
        have := hrets i hi
        rw [gpow_addC] at this
        exact this
    · exact hp.ok.fr x hx
  · simp only at ht'
    cases hre : rets.isEmpty
    · rw [hre] at ht'; cases ht'
    · rw [hre] at ht'
      exact hps.fresh t' ht'
  · rcases nvVals_spec _ _ n hn with h | h
    · exact hps.nm n h
    · have hm : Ev.call fs[k] args rets ∈ es := by rw [hes2]; simp
      exact uses_named hm (by simp [Ev.uses, h])

end Walk

end
end LeanVM.Guest.B2C
