/-
  LeanVM.Guest.B2C.CplComp

  B2's completeness for one compiled function: the checked parts compose into its run.
-/

module

public import LeanVM.Guest.B2C.CplSpec
public import LeanVM.Guest.B2C.CplRun
public import LeanVM.Guest.B2C.CplWalkZ

/-!
# The composition

Along a path through the body, the run reaches each part's start (`PartReach`): the path from there
returns, and the run is at the part's code offset within the counts handed on to it, in an
environment holding that offset's segment's. The walk of the part (`walk_Z`) takes it to the next
part's start, the next window's (`arr_win`: the environment handed on holds the next window's),
or, in the last part, to the return (`part_last`). From the function's entry (`reach_zero`) this
gives `cpl_run`.
-/

namespace LeanVM.Guest.B2C

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Exec
open LeanVM.Guest.Check LeanVM.Guest.Memory

@[expose] public section

/-- The function's entry registers. -/
noncomputable def entryRegs (j fp : ℕ) : Registers K := ⟨addressOfIndex (fnOf j).entryPc,
    addressOfIndex fp⟩

/-- Where part `k` of window `i` starts in the body. -/
noncomputable def partPos (j i k : ℕ) : ℕ := ((certOf j).cutAt i).start + partS j i k

/-- **The run is at part `k`'s start**: at its segment's start, or past the items the part
starts after, within its counts, the separately counted arms passed counting `x`, and the first
`n` callees'. -/
def PartArr {κ : ℕ} (L : MemoryImage κ) (j fp : ℕ) (ck : List (Opcode → ℕ)) (i k n : ℕ)
    (x : Opcode → ℕ) : Prop :=
  match partEnt j i k with
  | some (o, succ) => partJ j i k = succ.headD 0 ∧ succ ≠ [] ∧
    ArrCh L fp (Xp j i k) (wJW j i) (wenvW j i) ck (entryRegs j fp) o succ (partC j i k) n x
  | none =>
    if partM j i k = 0 then
      Arr L fp (Xp j i k) (wJW j i) (wenvW j i) ck (entryRegs j fp) (partJ j i k) (partC j i k) n x
    else ArrMid L fp (Xp j i k) ck (entryRegs j fp) (partJ j i k) (partM j i k) (partC j i k) n x

/-- **The run reaches part `k` of window `i`** on a path: the path from there returns, and the
run is at the part's start within its counts and the callees' before it. -/
def PartReach {κ : ℕ} (L : MemoryImage κ) (j fp : ℕ) (σ : Val) (es : List Ev) (vs : List V)
    (ck : List (Opcode → ℕ)) (i k : ℕ) : Prop :=
  ∃ ebef erest xc, walk σ ((coreOf j).body.drop (partPos j i k)) = .ret erest vs ∧ es = ebef ++ erest ∧
    xc + costW (listElementOrDefault Data.cplArms j []) σ ((coreOf j).body.drop (partPos j i k)) =
      costW (listElementOrDefault Data.cplArms j []) σ (coreOf j).body ∧
    PartArr L j fp ck i k (calls ebef).length xc

/-- What `CplRun` concludes of one path. -/
def CplGoal {κ : ℕ} (L : MemoryImage κ) (j fp : ℕ) (σ : Val) (vs : List V) (ck : List (Opcode → ℕ)) :
    Prop :=
  ∃ (r : Registers K) (c : Opcode → ℕ), (if j = 1 then r = Registers.final guestProgram else retRegs L (addressOfIndex fp) = some r) ∧
    RunC guestProgram L ⟨addressOfIndex (fnOf j).entryPc, addressOfIndex fp⟩ r c ∧
    (∀ op, c op ≤ pathCount j σ op + (ck.map (· op)).sum) ∧
    ∀ k (hk : k < vs.length),
      L.read (addressOfIndex (fp + (2 + (coreOf j).params.length + k))) = some (σ vs[k])

/-! ## Pieces -/

theorem costW_append (acs : List (ℕ × List (List ℕ))) (σ : Val) :
    ∀ (A B : List Stmt), costW acs σ (A ++ B) = costW acs σ A + costW acs σ B
  | [], B => by rw [List.nil_append, costW, zero_add]
  | a :: A, B => by rw [List.cons_append, costW, costW, costW_append acs σ A B, add_assoc]

theorem blt_falseC {a b : ℕ} (h : ¬ a < b) : Nat.blt a b = false := by
  cases hb : Nat.blt a b
  · rfl
  · exact absurd (Nat.blt_eq.mp hb) h

theorem seq_fall_ret {e1 e : List Ev} {o : Out} {v : List V} (h : (Out.fall e1).seq o = .ret e v) :
    ∃ e2, o = .ret e2 v ∧ e = e1 ++ e2 := by
  cases o with
  | fall e2 => cases h
  | ret e2 v2 =>
    simp only [Out.seq, Out.pre, Out.ret.injEq] at h
    exact ⟨e2, by rw [h.2], h.1.symm⟩
  | stuck => cases h

theorem pmax_get (j i k : ℕ) (op : Opcode) :
    (Xp j i k).pmax.get op = (plumbOf j).pmax.getD (opIdx op) 0 := by
  show (Cnt.ofList (plumbOf j).pmax).get op = _
  cases op <;> simp only [Cnt.ofList, Cnt.get, opIdx, nth_getD]

theorem ksum_le_sum (ck : List (Opcode → ℕ)) (n : ℕ) (op : Opcode) :
    ksum ck n op ≤ (ck.map (· op)).sum := by
  unfold ksum
  conv_rhs => rw [← List.take_append_drop n ck]
  rw [List.map_append, List.sum_append]
  exact Nat.le_add_right _ _

theorem cplRes_some {j i k : ℕ} (h : partEnd j i k (cplRes j i k) = true) :
    ∃ s, getF (index (segsW j i)) (partJ j i k) = some s ∧ s.start = partJ j i k ∧
      ((partEnt j i k = none ∧ cplRes j i k = cw (Xp j i k) (partStmts j i k) (st0 j i k s)) ∨
       (∃ o succ, partEnt j i k = some (o, succ) ∧
        cplRes j i k = cwE (Xp j i k) o succ (st0E j i k s) (partStmts j i k))) := by
  rw [cplRes_eq] at h ⊢
  rcases hg : getF (index (segsW j i)) (partJ j i k) with _ | s
  · simp only [hg] at h
    simp [partEnd] at h
  · simp only [hg] at h ⊢
    cases hb : Nat.beq s.start (partJ j i k)
    · rw [hb] at h
      simp [partEnd] at h
    · refine ⟨s, rfl, Nat.eq_of_beq_eq_true hb, ?_⟩
      simp only [Bool.cond_true]
      rcases he : partEnt j i k with _ | ⟨o, succ⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨o, succ, rfl, rfl⟩

theorem cw_ok_of {j i k : ℕ} {r : RC} (hres : cplRes j i k = r) (h : partEnd j i k (cplRes j i k) = true) :
    r.ok = true := by
  subst hres
  rcases hc : cplRes j i k with ⟨J, c, u⟩ | ⟨o, succ, c, u⟩ | ⟨J, m, c, u⟩ | _ | e
  · rfl
  · rfl
  · rfl
  · rfl
  · rw [hc] at h
    simp [partEnd] at h

theorem cplWin_end {j i k : ℕ} (h : cplWin j i k = true) : partEnd j i k (cplRes j i k) = true := by
  unfold cplWin at h
  simp only [Bool.and_eq_true] at h
  exact h.2

theorem cplWin_mid {j i k : ℕ} (h : cplWin j i k = true) (hl : lastPart j i k = false) :
    Stmt.noRetList (partStmts j i k) = true := by
  unfold cplWin at h
  rw [hl, Bool.cond_false] at h
  simp only [Bool.and_eq_true] at h
  exact h.1.2

theorem cplWin_last {j i k : ℕ} (h : cplWin j i k = true) (hl : lastPart j i k = true) :
    lastOkC (partStmts j i k) = true := by
  unfold cplWin at h
  rw [hl, Bool.cond_true] at h
  simp only [Bool.and_eq_true] at h
  exact h.1.2

theorem partS_zero {j i : ℕ} (h : cplWin j i 0 = true) : partS j i 0 = 0 := by
  have := winOkC_of h
  simp only [winOkC, Bool.and_eq_true] at this
  exact Nat.eq_of_beq_eq_true this.1.1.1.1.2

theorem partM_zero {j i : ℕ} (h : cplWin j i 0 = true) : partM j i 0 = 0 := by
  have := winOkC_of h
  simp only [winOkC, Bool.and_eq_true] at this
  exact Nat.eq_of_beq_eq_true this.1.1.1.2

/-- A window's first part is entered as its window is. -/
theorem partEnt_zero {j i : ℕ} (h : cplWin j i 0 = true) :
    (partEnt j i 0 = none ∧ (certOf j).succAt i = []) ∨ ∃ o succ, partEnt j i 0 = some (o, succ) ∧
      o = (certOf j).selAt i ∧ succ = (certOf j).succAt i ∧ succ ≠ [] := by
  have := winOkC_of h
  simp only [winOkC, Bool.and_eq_true] at this
  have hm := this.1.1.2
  rcases he : partEnt j i 0 with _ | ⟨o, succ⟩
  · rw [he] at hm
    exact Or.inl ⟨rfl, List.isEmpty_iff.mp hm⟩
  · rw [he] at hm
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', List.isEmpty_eq_false_iff] at hm
    exact Or.inr ⟨o, succ, rfl, Nat.eq_of_beq_eq_true hm.1.1, hm.1.2, hm.2⟩

/-! ## The body returns only at its end -/

theorem lastOkC_append : ∀ (A : List Stmt) {B : List Stmt}, Stmt.noRetList A = true →
    lastOkC B = true → lastOkC (A ++ B) = true
  | [], _, _, hB => hB
  | a :: A, B, hA, hB => by
    simp only [Stmt.noRetList, Bool.and_eq_true] at hA
    have ih := lastOkC_append A hA.2 hB
    cases h : A ++ B with
    | nil => rw [h] at ih; simp [lastOkC] at ih
    | cons x xs =>
      rw [List.cons_append, h]
      rw [h] at ih
      cases a <;> simp_all [lastOkC, Stmt.noRet]

/-- **A function the check accepts returns only at its end**: its parts follow one another
through the body, each but the last returning nowhere. -/
theorem lastBody {j : ℕ} (hok : CplOk j)
    (hchk : ∀ i ≤ (certOf j).cuts.length,
      checkWin glob (fnOf j) (coreOf j) (certOf j) (j == 1) i = true) :
    lastOkC (coreOf j).body = true := by
  have parts : ∀ i ≤ (certOf j).cuts.length,
      (i < (certOf j).cuts.length → lastOkC ((coreOf j).body.drop (partPos j (i + 1) 0)) = true) →
      ∀ m k, nParts j i - k = m → k < nParts j i →
        lastOkC ((coreOf j).body.drop (partPos j i k)) = true := by
    intro i hi hnext m
    induction m with
    | zero => intro k hm hk; omega
    | succ m ih =>
      intro k hm hk
      have hc := hok i hi
      have hsplit := part_split hk (fun h ↦ ((checkWin_cpl (hchk i hi)).2.2.2.2 h).1) hc
      unfold partPos
      rw [hsplit]
      by_cases hn : k + 1 < nParts j i
      · have hb : Nat.blt (k + 1) (nParts j i) = true := Nat.blt_eq.mpr hn
        have hlp : lastPart j i k = false := by simp only [lastPart, hb]; rfl
        have hnx : nextPos j i k = partPos j i (k + 1) := by
          unfold nextPos
          rw [hb]
          rfl
        rw [hnx]
        exact lastOkC_append _ (cplWin_mid (hc k hk) hlp) (ih (k + 1) (by omega) hn)
      · by_cases hci : i < (certOf j).cuts.length
        · have hbi : Nat.blt i (certOf j).cuts.length = true := Nat.blt_eq.mpr hci
          have hlp : lastPart j i k = false := by simp only [lastPart, blt_falseC hn, hbi]; rfl
          have hnx : nextPos j i k = partPos j (i + 1) 0 := by
            unfold nextPos partPos
            rw [blt_falseC hn, hbi, partS_zero (hok (i + 1) hci 0 (one_le_nParts j (i + 1)))]
            rfl
          rw [hnx]
          exact lastOkC_append _ (cplWin_mid (hc k hk) hlp) (hnext hci)
        · have hlp : lastPart j i k = true := by
            simp only [lastPart, blt_falseC hn, blt_falseC hci]
            rfl
          have hnx : nextPos j i k = (coreOf j).body.length := by
            unfold nextPos
            rw [blt_falseC hn, blt_falseC hci]
            rfl
          rw [hnx, List.drop_length, List.append_nil]
          exact cplWin_last (hc k hk) hlp
  have wins : ∀ m i, (certOf j).cuts.length - i = m → i ≤ (certOf j).cuts.length →
      lastOkC ((coreOf j).body.drop (partPos j i 0)) = true := by
    intro m
    induction m with
    | zero =>
      intro i hm hi
      exact parts i hi (fun h ↦ by omega) _ 0 rfl (one_le_nParts j i)
    | succ m ih =>
      intro i hm hi
      exact parts i hi (fun h ↦ ih (i + 1) (by omega) h) _ 0 rfl (one_le_nParts j i)
  have h0 := wins _ 0 rfl (Nat.zero_le _)
  rwa [partPos, partS_zero (hok 0 (Nat.zero_le _) 0 (one_le_nParts j 0))] at h0

section Comp

variable {κ : ℕ} {L : MemoryImage κ} {j fp : ℕ} {σ : Val} {es : List Ev} {vs : List V}
  {kfps : List ℕ} {hdr : E × E} {ck : List (Opcode → ℕ)}

theorem partArr_zero {i k n : ℕ} {x : Opcode → ℕ} (he : partEnt j i k = none) (h : partM j i k = 0) :
    PartArr L j fp ck i k n x ↔
    Arr L fp (Xp j i k) (wJW j i) (wenvW j i) ck (entryRegs j fp) (partJ j i k) (partC j i k) n x := by
  unfold PartArr
  simp only [he, h, ↓reduceIte]

theorem partArr_mid {i k n : ℕ} {x : Opcode → ℕ} (he : partEnt j i k = none) (h : partM j i k ≠ 0) :
    PartArr L j fp ck i k n x ↔
    ArrMid L fp (Xp j i k) ck (entryRegs j fp) (partJ j i k) (partM j i k) (partC j i k) n x := by
  unfold PartArr
  simp only [he, h, ↓reduceIte]

theorem partArr_ent {i k n : ℕ} {x : Opcode → ℕ} {o : ℕ} {succ : List ℕ} (he : partEnt j i k = some (o, succ)) :
    PartArr L j fp ck i k n x ↔ partJ j i k = succ.headD 0 ∧ succ ≠ [] ∧
    ArrCh L fp (Xp j i k) (wJW j i) (wenvW j i) ck (entryRegs j fp) o succ (partC j i k) n x := by
  unfold PartArr
  simp only [he]

theorem arrCh_mono {X : CX} {wJ : ℕ} {wenv : Trie Sym} {W0 : Registers K} {o n : ℕ} {succ : List ℕ}
    {x : Opcode → ℕ} {c c' : Cnt} (h : ArrCh L fp X wJ wenv ck W0 o succ c n x) (hc : c.le c' = true) :
    ArrCh L fp X wJ wenv ck W0 o succ c' n x := by
  refine ⟨fun e he hoe ↦ ?_, h.2⟩
  obtain ⟨⟨cr, hr, hle⟩, hen⟩ := h.1 e he hoe
  exact ⟨⟨cr, hr, fun op ↦ by have := hle op; have := Cnt.le_spec hc op; omega⟩, hen⟩

theorem arr_mono {X : CX} {wJ : ℕ} {wenv : Trie Sym} {W0 : Registers K} {J n : ℕ} {x : Opcode → ℕ}
    {c c' : Cnt} (h : Arr L fp X wJ wenv ck W0 J c n x) (hc : c.le c' = true) :
    Arr L fp X wJ wenv ck W0 J c' n x := by
  obtain ⟨⟨cr, hr, hle⟩, he⟩ := h
  exact ⟨⟨cr, hr, fun op ↦ by have := hle op; have := Cnt.le_spec hc op; omega⟩, he⟩

theorem arrMid_mono {X : CX} {W0 : Registers K} {J m n : ℕ} {x : Opcode → ℕ} {c c' : Cnt}
    (h : ArrMid L fp X ck W0 J m c n x) (hc : c.le c' = true) : ArrMid L fp X ck W0 J m c' n x := by
  obtain ⟨s, hs, hst, hm, he, cr, hf, hr, hle⟩ := h
  exact ⟨s, hs, hst, hm, he, cr, hf, hr, fun op ↦ by have := hle op; have := Cnt.le_spec hc op; omega⟩

/-- At a segment's start, no item passed. -/
theorem arrMid_zero {X : CX} {wJ : ℕ} {wenv : Trie Sym} {W0 : Registers K} {J n : ℕ} {x : Opcode → ℕ}
    {c : Cnt} {s : Exec.Seg}
    (h : Arr L fp X wJ wenv ck W0 J c n x) (hs : getF X.idx J = some s) (hst : s.start = J) :
    ArrMid L fp X ck W0 J 0 c n x := by
  obtain ⟨⟨cr, hr, hle⟩, he⟩ := h
  exact ⟨s, hs, hst, Nat.zero_le _, he.1 s hs hst, cr, trivial, hr, fun op ↦ by simpa [itemOps] using hle op⟩

/-- **Into the next window**: the environment window `i` hands on holds the next window's. -/
theorem arr_win (F : FnH L j fp σ es vs kfps hdr ck) {i k : ℕ} (hi : i < (certOf j).cuts.length)
    {c c' : Cnt} {n : ℕ} {x : Opcode → ℕ}
    (h : Arr L fp (Xp j i k) (wJW j i) (wenvW j i) ck (entryRegs j fp) ((certOf j).cutAt (i + 1)).J c n x)
    (hc : c.le c' = true) :
    Arr L fp (Xp j (i + 1) 0) (wJW j (i + 1)) (wenvW j (i + 1)) ck (entryRegs j fp)
      (partJ j (i + 1) 0) c' n x := by
  obtain ⟨⟨cr, hr, hle⟩, he1, he2⟩ := h
  have hb : Nat.blt i (certOf j).cuts.length = true := Nat.blt_eq.mpr hi
  have hc1 := checkWin_cpl (F.chk i hi.le)
  have hc2 := checkWin_cpl (F.chk (i + 1) hi)
  obtain ⟨s0, hs0, -, hsub0⟩ := hc2.2.2.2.1
  have hwJ : wJW j i = ((certOf j).cutAt (i + 1)).J := by simp only [wJW, hb, Bool.cond_true]
  have hwenv : wenvW j i = envOf ((certOf j).cutAt (i + 1)).env := by simp only [wenvW, hb, Bool.cond_true]
  have hE : EnvHolds L (addressOfIndex fp) (envOf ((certOf j).cutAt (i + 1)).env) := by
    cases hg : getF (index (segsW j i)) ((certOf j).cutAt (i + 1)).J with
    | none =>
      rw [← hwenv]
      exact he2 hwJ.symm hg
    | some s =>
      obtain ⟨hst, hsub⟩ := (hc1.2.2.2.2 hi).2 s hg
      exact (he1 s hg hst).sub hsub
  refine ⟨⟨cr, hr, fun op ↦ by have := hle op; have := Cnt.le_spec hc op; omega⟩,
    fun s hs _ ↦ ?_, fun _ hn ↦ ?_⟩
  · have hs' : getF (index (segsW j (i + 1))) ((certOf j).cutAt (i + 1)).J = some s := hs
    obtain rfl := Option.some.inj (hs'.symm.trans hs0)
    exact hE.sub hsub0
  · have hn' : getF (index (segsW j (i + 1))) ((certOf j).cutAt (i + 1)).J = none := hn
    rw [hn'] at hs0
    cases hs0

/-- **Into the next window, entered**: the environment window `i` hands on holds the next
window's, and so the environments of its arms. -/
theorem arrCh_win (F : FnH L j fp σ es vs kfps hdr ck) {i k : ℕ} (hi : i < (certOf j).cuts.length)
    {o : ℕ} {succ : List ℕ} {c c' : Cnt} {n : ℕ} {x : Opcode → ℕ}
    (h : ArrCh L fp (Xp j i k) (wJW j i) (wenvW j i) ck (entryRegs j fp) o succ c n x)
    (hc : c.le c' = true) (hJ : partJ j (i + 1) 0 = succ.headD 0)
    (hent : partEnt j (i + 1) 0 = some (o, succ)) :
    ArrCh L fp (Xp j (i + 1) 0) (wJW j (i + 1)) (wenvW j (i + 1)) ck (entryRegs j fp) o succ c' n x := by
  have hb : Nat.blt i (certOf j).cuts.length = true := Nat.blt_eq.mpr hi
  have hc1 := checkWin_cpl (F.chk i hi.le)
  rcases partEnt_zero (F.ok (i + 1) hi 0 (one_le_nParts j (i + 1))) with ⟨hn, -⟩ | ⟨o', s', he', -, hs', hne⟩
  · rw [hn] at hent; cases hent
  rw [hent] at he'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj he')
  obtain ⟨t0, ts, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hst := checkWin_starts (F.chk (i + 1) hi) (by rw [← hs']; exact hne)
  rw [← hs'] at hst
  have hJ' : ((certOf j).cutAt (i + 1)).J = t0 := hJ
  have hwJ : wJW j i = ((certOf j).cutAt (i + 1)).J := by simp only [wJW, hb, Bool.cond_true]
  have hwenv : wenvW j i = envOf ((certOf j).cutAt (i + 1)).env := by simp only [wenvW, hb, Bool.cond_true]
  -- the next window's environment holds
  have hE : EnvHolds L (addressOfIndex fp) (envOf ((certOf j).cutAt (i + 1)).env) := by
    have he0 := h.2 (by simp)
    simp only [List.getElem_cons_zero] at he0
    rw [← hJ'] at he0
    cases hg : getF (index (segsW j i)) ((certOf j).cutAt (i + 1)).J with
    | none =>
      rw [← hwenv]
      exact he0.2 hwJ.symm hg
    | some s =>
      obtain ⟨hst', hsub⟩ := (hc1.2.2.2.2 hi).2 s hg
      exact (he0.1 s hg hst').sub hsub
  -- the arms' environments hold
  have hEA : ∀ e (he : e < (t0 :: ts).length),
      EnvAt L fp (Xp j (i + 1) 0) (wJW j (i + 1)) (wenvW j (i + 1)) (t0 :: ts)[e] := by
    intro e he
    have hok := List.all_eq_true.mp hst _ (List.getElem_mem he)
    split at hok
    · rename_i s hs
      simp only [Bool.and_eq_true, beq_iff_eq] at hok
      refine ⟨fun s' hs' _ ↦ ?_, fun _ hn ↦ ?_⟩
      · have hs'' : getF (index (segsW j (i + 1))) (t0 :: ts)[e] = some s' := hs'
        rw [hs] at hs''
        obtain rfl := Option.some.inj hs''
        exact hE.sub hok.2
      · have hn' : getF (index (segsW j (i + 1))) (t0 :: ts)[e] = none := hn
        rw [hs] at hn'; cases hn'
    · cases hok
  refine ⟨fun e he hoe ↦ ?_, fun h0 ↦ hEA 0 h0⟩
  obtain ⟨⟨cr, hr, hle⟩, -⟩ := h.1 e he hoe
  exact ⟨⟨cr, hr, fun op ↦ by have := hle op; have := Cnt.le_spec hc op; omega⟩, hEA e he⟩

/-- The run at the function's entry, in window `0`'s first part. -/
theorem reach_zero (F : FnH L j fp σ es vs kfps hdr ck) : PartReach L j fp σ es vs ck 0 0 := by
  have hc0 := F.ok 0 (Nat.zero_le _) 0 (one_le_nParts j 0)
  obtain ⟨s0, hs0, -, hsub0⟩ := (checkWin_cpl (F.chk 0 (Nat.zero_le _))).2.2.2.1
  have hw0 := winOkC_of hc0
  simp only [winOkC, Bool.and_eq_true, Nat.beq_refl, Bool.cond_true] at hw0
  have henv := hw0.2.1.2
  have hX := cxOk F.frame F.pows (index (segsW j 0)) (clocW (certOf j) 0) (nvOf (partStmts j 0 0) 0) none
  have hE : EnvHolds L (addressOfIndex fp) (envOf (certOf j).facts.env) := by
    refine envOf_holds fun p hp ↦ ?_
    have := List.all_eq_true.mp henv p hp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    obtain ⟨h1, h2⟩ := this
    have := hX.stat p.1 _ h2
    rw [Sym.beq_eq h1]
    simp only [PC.word, Nat.add_zero] at this
    simpa [Sym.val, gpow_addC] using this
  have hent0 : partEnt j 0 0 = none := by
    rcases partEnt_zero hc0 with ⟨h, -⟩ | ⟨o, succ, -, -, rfl, hne⟩
    · exact h
    · exact absurd rfl hne
  refine ⟨[], es, 0, ?_, rfl, ?_, (partArr_zero hent0 (partM_zero hc0)).mpr ?_⟩
  · rw [partPos, partS_zero hc0]
    exact F.walk
  · rw [zero_add, partPos, partS_zero hc0]
    rfl
  refine ⟨⟨0, RunC.refl _, fun _ ↦ Nat.zero_le _⟩, fun s hs _ ↦ ?_, fun _ hn ↦ ?_⟩
  · have hs' : getF (index (segsW j 0)) ((certOf j).cutAt 0).J = some s := hs
    obtain rfl := Option.some.inj (hs'.symm.trans hs0)
    exact hE.sub hsub0
  · have hn' : getF (index (segsW j 0)) ((certOf j).cutAt 0).J = none := hn
    rw [hn'] at hs0
    cases hs0

/-- The walk's start of a part, from the run arriving there. -/
theorem posZ_start {i k : ℕ}
    (H : WH L j fp (Xp j i k) (segsW j i) (wJW j i) (wenvW j i) σ es vs kfps hdr ck) {s : Exec.Seg}
    (hs : getF (index (segsW j i)) (partJ j i k) = some s) (hst : s.start = partJ j i k) {n : ℕ}
    {x : Opcode → ℕ} (hent : partEnt j i k = none) (hA : PartArr L j fp ck i k n x)
    (hatoms : ∀ a, Stmt.atom a ∈ partStmts j i k → Ev.atom a ∈ es) :
    PosZ H (st0 j i k s) (entryRegs j fp) n x := by
  have hM : ArrMid L fp (Xp j i k) ck (entryRegs j fp) (partJ j i k) (partM j i k) (partC j i k) n x := by
    simp only [PartArr, hent] at hA
    split_ifs at hA with h0
    · rw [h0]
      exact arrMid_zero hA hs hst
    · exact hA
  obtain ⟨s', hs', -, hm, he, cr, hf, hr, hle⟩ := hM
  have hs1 : getF (Xp j i k).idx (partJ j i k) = some s := hs
  obtain rfl := Option.some.inj (hs'.symm.trans hs1)
  have hmem : s' ∈ segsW j i := by
    rw [getF_eq] at hs
    exact index_get hs
  refine ⟨hmem, ⟨he, fileB_ok H.frame H.loc H.hev _ _
    (fun _ _ h ↦ absurd (show _ ∈ ([] : List LAtom) from h) (by simp)) hatoms,
    fun _ h ↦ (by cases h), fun _ h ↦ (by cases h), fun _ h ↦ (by cases h)⟩,
    ⟨s'.items.take (partM j i k), cr, List.take_append_drop _ _, hf,
      (by simp only [st0]; rw [hst]; exact hr), hle⟩,
    fun t ht ↦ ?_, fun _ h ↦ absurd h (by simp [st0]), (by simp only [st0]; rw [hst]; exact hs)⟩
  unfold st0 at ht
  cases h0 : Nat.beq (partM j i k) 0
  · rw [h0] at ht
    cases ht
  · rw [h0] at ht
    obtain rfl := Option.some.inj ht
    refine ⟨hst, ?_, hs⟩
    show s'.items.drop (partM j i k) = s'.items
    rw [Nat.eq_of_beq_eq_true h0, List.drop_zero]

/-- The walk's state at an entered part's start holds. -/
theorem okE_start {i k : ℕ}
    (H : WH L j fp (Xp j i k) (segsW j i) (wJW j i) (wenvW j i) σ es vs kfps hdr ck) {s : Exec.Seg}
    (hs : getF (index (segsW j i)) (partJ j i k) = some s) (hst : s.start = partJ j i k)
    {o n : ℕ} {succ : List ℕ} {x : Opcode → ℕ}
    (hA : ArrCh L fp (Xp j i k) (wJW j i) (wenvW j i) ck (entryRegs j fp) o succ (partC j i k) n x)
    (hJ : partJ j i k = succ.headD 0) (hne : succ ≠ [])
    (hatoms : ∀ a, Stmt.atom a ∈ partStmts j i k → Ev.atom a ∈ es) :
    CWOk L fp (Xp j i k) (st0E j i k s) := by
  obtain ⟨t0, ts, rfl⟩ := List.exists_cons_of_ne_nil hne
  have he0 := hA.2 (by simp)
  simp only [List.getElem_cons_zero] at he0
  simp only [List.headD_cons] at hJ
  rw [hJ] at hs hst
  exact ⟨he0.1 s hs hst, fileB_ok H.frame H.loc H.hev _ _
    (fun _ _ h ↦ absurd (show _ ∈ ([] : List LAtom) from h) (by simp)) hatoms,
    fun _ h ↦ (by cases h), fun _ h ↦ (by cases h), fun _ h ↦ (by cases h)⟩

/-- **A part's walk**, from the run at its start, by `walk_Z` or, entered, `walk_enterZ`. -/
theorem part_walk (F : FnH L j fp σ es vs kfps hdr ck)
    (hlb : lastOkC (coreOf j).body = true) {i k : ℕ}
    (hi : i ≤ (certOf j).cuts.length) {s : Exec.Seg}
    (hs : getF (index (segsW j i)) (partJ j i k) = some s) (hst : s.start = partJ j i k)
    (hres : (partEnt j i k = none ∧ cplRes j i k = cw (Xp j i k) (partStmts j i k) (st0 j i k s)) ∨
       (∃ o succ, partEnt j i k = some (o, succ) ∧
        cplRes j i k = cwE (Xp j i k) o succ (st0E j i k s) (partStmts j i k)))
    (hok : (cplRes j i k).ok = true) {ebef eaft : List Ev} {out : Out} {pre : List Stmt} {xc : Opcode → ℕ}
    (hw : walk σ (partStmts j i k) = out) (hes : es = ebef ++ out.evs ++ eaft) (hstk : out ≠ .stuck)
    (hshape : Stmt.noRetList (partStmts j i k) = true ∨
      (lastOkC (partStmts j i k) = true ∧ eaft = [] ∧ (coreOf j).body = pre ++ partStmts j i k))
    (hA : PartArr L j fp ck i k (calls ebef).length xc)
    (hatoms : ∀ a, Stmt.atom a ∈ partStmts j i k → Ev.atom a ∈ es) :
    WOut (wh_part F hlb hi (k := k)) (cplRes j i k) out ebef (entryRegs j fp) xc (partStmts j i k) := by
  have H := wh_part F hlb hi (k := k)
  rcases hres with ⟨hent, hres⟩ | ⟨o, succ, hent, hres⟩
  · have hp := posZ_start H hs hst hent hA hatoms
    rw [hres] at hok ⊢
    exact walk_Z H _ _ ebef eaft out (entryRegs j fp) pre xc hw hes hstk hshape hp hok
  · obtain ⟨hJ, hne, hA'⟩ := (partArr_ent hent).mp hA
    rw [hres] at hok ⊢
    exact walk_enterZ H (walk_Z H) hw hes hstk hshape (okE_start H hs hst hA' hJ hne hatoms)
      (fun n h ↦ by simp [st0E] at h) hA' hok

/-- **A part before the last**: its walk takes the run to where it ends. -/
theorem part_mid (F : FnH L j fp σ es vs kfps hdr ck)
    (hlb : lastOkC (coreOf j).body = true) {i k : ℕ}
    (hi : i ≤ (certOf j).cuts.length) (hk : k < nParts j i) (hr : PartReach L j fp σ es vs ck i k)
    (hnr : Stmt.noRetList (partStmts j i k) = true) :
    ∃ ebef erest xc, walk σ ((coreOf j).body.drop (nextPos j i k)) = .ret erest vs ∧ es = ebef ++ erest ∧
      xc + costW (listElementOrDefault Data.cplArms j []) σ ((coreOf j).body.drop (nextPos j i k)) =
        costW (listElementOrDefault Data.cplArms j []) σ (coreOf j).body ∧
      ((∃ J c u, cplRes j i k = .join J c u ∧
        Arr L fp (Xp j i k) (wJW j i) (wenvW j i) ck (entryRegs j fp) J c (calls ebef).length xc) ∨
       (∃ J m c u, cplRes j i k = .mid J m c u ∧
        ArrMid L fp (Xp j i k) ck (entryRegs j fp) J m c (calls ebef).length xc) ∨
       (∃ o succ c u, cplRes j i k = .chain o succ c u ∧
        ArrCh L fp (Xp j i k) (wJW j i) (wenvW j i) ck (entryRegs j fp) o succ c (calls ebef).length xc)) := by
  obtain ⟨ebef, erest, xc, hwr, hes, hxc, hA⟩ := hr
  have hc := F.ok i hi
  have hsplit := part_split hk (fun h ↦ ((checkWin_cpl (F.chk i hi)).2.2.2.2 h).1) hc
  have hend := cplWin_end (hc k hk)
  obtain ⟨s, hs, hst, hres⟩ := cplRes_some hend
  unfold partPos at hwr hxc
  rw [hsplit, walk_appendC] at hwr
  rw [hsplit, costW_append, ← add_assoc] at hxc
  rcases walk_noRetC _ hnr with ⟨e1, hw1⟩ | hw1
  · rw [hw1] at hwr
    obtain ⟨e2, hw2, he⟩ := seq_fall_ret hwr
    have hatoms : ∀ a, Stmt.atom a ∈ partStmts j i k → Ev.atom a ∈ es := fun a ha ↦ by
      rw [hes, he]
      exact List.mem_append_right _ (List.mem_append_left _ (atom_on_pathC hw1 ha))
    have hes' : es = ebef ++ (Out.fall e1).evs ++ e2 := by rw [hes, he, List.append_assoc]; rfl
    obtain ⟨h1, hm, h2, hch⟩ := part_walk F hlb hi hs hst hres (cw_ok_of rfl hend) hw1 hes'
      (fun h ↦ by cases h) (Or.inl hnr) hA hatoms (pre := (coreOf j).body.take (partPos j i k))
    have hes2 : es = (ebef ++ e1) ++ e2 := by rw [hes, he, List.append_assoc]
    rcases hcr : cplRes j i k with ⟨J, c, u⟩ | ⟨o, succ, c, u⟩ | ⟨J, m, c, u⟩ | _ | e
    · obtain ⟨es', he', ha⟩ := h1 J c u hcr
      cases he'
      exact ⟨ebef ++ e1, e2, _, hw2, hes2, hxc, Or.inl ⟨J, c, u, rfl, ha⟩⟩
    · obtain ⟨es', he', ha⟩ := hch o succ c u hcr
      cases he'
      exact ⟨ebef ++ e1, e2, _, hw2, hes2, hxc, Or.inr (Or.inr ⟨o, succ, c, u, rfl, ha⟩)⟩
    · obtain ⟨es', he', ha⟩ := hm J m c u hcr
      cases he'
      exact ⟨ebef ++ e1, e2, _, hw2, hes2, hxc, Or.inr (Or.inl ⟨J, m, c, u, rfl, ha⟩)⟩
    · obtain ⟨es', vs', he', -⟩ := h2 hcr
      cases he'
    · rw [hcr] at hend
      simp [partEnd] at hend
  · rw [hw1] at hwr
    cases hwr

/-- **The last part**: its walk takes the run to the return. -/
theorem part_last (F : FnH L j fp σ es vs kfps hdr ck)
    (hlb : lastOkC (coreOf j).body = true) {i k : ℕ}
    (hi : i ≤ (certOf j).cuts.length) (hk : k < nParts j i) (hr : PartReach L j fp σ es vs ck i k)
    (hn : ¬ k + 1 < nParts j i) (hci : ¬ i < (certOf j).cuts.length) : CplGoal L j fp σ vs ck := by
  obtain ⟨ebef, erest, xc, hwr, hes, hxc, hA⟩ := hr
  have hc := F.ok i hi
  have hsplit := part_split hk (fun h ↦ ((checkWin_cpl (F.chk i hi)).2.2.2.2 h).1) hc
  have hend := cplWin_end (hc k hk)
  obtain ⟨s, hs, hst, hres⟩ := cplRes_some hend
  have hlp : lastPart j i k = true := by simp only [lastPart, blt_falseC hn, blt_falseC hci]; rfl
  have hshp := cplWin_last (hc k hk) hlp
  have hnext : nextPos j i k = (coreOf j).body.length := by
    unfold nextPos
    rw [blt_falseC hn, blt_falseC hci]
    rfl
  have hd : (coreOf j).body.drop (partPos j i k) = partStmts j i k := by
    unfold partPos
    rw [hsplit, hnext, List.drop_length, List.append_nil]
  rw [hd] at hwr hxc
  have hatoms : ∀ a, Stmt.atom a ∈ partStmts j i k → Ev.atom a ∈ es := fun a ha ↦ by
    rw [hes]
    exact List.mem_append_right _ (atoms_last hshp hwr (fun h ↦ by cases h) ha)
  have H := wh_part F hlb hi (k := k)
  have hes' : es = ebef ++ (Out.ret erest vs).evs ++ [] := by rw [hes, List.append_nil]; rfl
  have hbody : (coreOf j).body = (coreOf j).body.take (partPos j i k) ++ partStmts j i k := by
    rw [← hd, List.take_append_drop]
  obtain ⟨-, -, h2, -⟩ := part_walk F hlb hi hs hst hres (cw_ok_of rfl hend) hwr hes'
    (fun h ↦ by cases h) (Or.inr ⟨hshp, rfl, hbody⟩) hA hatoms
  have hdone : cplRes j i k = .done := by
    rcases hcr : cplRes j i k with ⟨J, c, u⟩ | ⟨o, succ, c, u⟩ | ⟨J, m, c, u⟩ | _ | e
    · rw [hcr] at hend
      simp only [partEnd, blt_falseC hn, blt_falseC hci, Bool.cond_false, Bool.false_and] at hend
      cases hend
    · rw [hcr] at hend
      simp only [partEnd, blt_falseC hn, blt_falseC hci, Bool.cond_false, Bool.false_and,
        Bool.and_false] at hend
      cases hend
    · rw [hcr] at hend
      simp only [partEnd, blt_falseC hn, Bool.false_and] at hend
      cases hend
    · rfl
    · rw [hcr] at hend
      simp [partEnd] at hend
  obtain ⟨es', vs', he', ⟨r, cr, hr0, hrun, hcr⟩, hcells⟩ := h2 hdone
  cases he'
  refine ⟨r, cr, hr0, hrun, fun op ↦ ?_, fun k' hk' ↦ ?_⟩
  · have h1 := hcr op
    have h2 := ksum_le_sum ck (calls (ebef ++ erest)).length op
    have h3 : (xc + costW (Xp j i k).acs σ (partStmts j i k)) op =
        costW (listElementOrDefault Data.cplArms j []) σ (coreOf j).body op := congrFun hxc op
    rw [pmax_get j i k op, h3] at h1
    unfold pathCount
    omega
  · obtain ⟨hc1, hc2, hc3⟩ := hcells k' hk'
    have hv : vs[k'] ∈ namedOf (coreOf j).params es vs :=
      List.mem_append_right _ (List.getElem_mem hk')
    have := val_cell H.frame H.loc hv hc2 (H.fs ▸ hc3)
    rw [hc1] at this
    rw [gpow_addC]
    exact this

/-- **One part**: on to the next part, the next window, or the return. -/
theorem part_step (F : FnH L j fp σ es vs kfps hdr ck)
    (hlb : lastOkC (coreOf j).body = true) {i k : ℕ}
    (hi : i ≤ (certOf j).cuts.length) (hk : k < nParts j i) (hr : PartReach L j fp σ es vs ck i k) :
    (k + 1 < nParts j i ∧ PartReach L j fp σ es vs ck i (k + 1)) ∨ CplGoal L j fp σ vs ck ∨
      (i < (certOf j).cuts.length ∧ PartReach L j fp σ es vs ck (i + 1) 0) := by
  have hc := F.ok i hi
  have hend := cplWin_end (hc k hk)
  by_cases hn : k + 1 < nParts j i
  · have hb : Nat.blt (k + 1) (nParts j i) = true := Nat.blt_eq.mpr hn
    have hlp : lastPart j i k = false := by simp only [lastPart, hb]; rfl
    have hnext : nextPos j i k = partPos j i (k + 1) := by
      unfold nextPos
      rw [hb]
      rfl
    obtain ⟨ebef, erest, xc, hw, hes, hxc, hres⟩ := part_mid F hlb hi hk hr (cplWin_mid (hc k hk) hlp)
    refine Or.inl ⟨hn, ebef, erest, xc, hnext ▸ hw, hes, hnext ▸ hxc, ?_⟩
    rcases hres with ⟨J, c, u, hres, hA⟩ | ⟨J, m, c, u, hres, hA⟩ | ⟨o, succ, c, u, hres, hA⟩
    · rw [hres] at hend
      simp only [partEnd, hb, Bool.cond_true, Bool.and_eq_true] at hend
      obtain ⟨⟨⟨⟨hJ, hm0⟩, hen⟩, hle⟩, -⟩ := hend
      obtain rfl := Nat.eq_of_beq_eq_true hJ
      exact (partArr_zero (Option.isNone_iff_eq_none.mp hen) (Nat.eq_of_beq_eq_true hm0)).mpr
        (arr_mono hA hle)
    · rw [hres] at hend
      simp only [partEnd, hb, Bool.true_and, Bool.and_eq_true, Bool.not_eq_true'] at hend
      obtain ⟨⟨⟨⟨⟨hJ, hm⟩, hm0⟩, hen⟩, hle⟩, -⟩ := hend
      obtain rfl := Nat.eq_of_beq_eq_true hJ
      obtain rfl := Nat.eq_of_beq_eq_true hm
      exact (partArr_mid (Option.isNone_iff_eq_none.mp hen)
        (fun h ↦ by rw [h, Nat.beq_refl] at hm0; cases hm0)).mpr (arrMid_mono hA hle)
    · rw [hres] at hend
      simp only [partEnd, hb, Bool.cond_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
        List.isEmpty_eq_false_iff] at hend
      obtain ⟨hne, ⟨⟨he, hJ⟩, hle⟩, -⟩ := hend
      exact (partArr_ent he).mpr ⟨Nat.eq_of_beq_eq_true hJ, hne, arrCh_mono hA hle⟩
  · by_cases hci : i < (certOf j).cuts.length
    · have hbi : Nat.blt i (certOf j).cuts.length = true := Nat.blt_eq.mpr hci
      have hlp : lastPart j i k = false := by simp only [lastPart, blt_falseC hn, hbi]; rfl
      obtain ⟨ebef, erest, xc, hw, hes, hxc, hres⟩ := part_mid F hlb hi hk hr (cplWin_mid (hc k hk) hlp)
      have hnext : nextPos j i k = partPos j (i + 1) 0 := by
        unfold nextPos partPos
        rw [blt_falseC hn, hbi, partS_zero (F.ok (i + 1) hci 0 (one_le_nParts j (i + 1)))]
        rfl
      refine Or.inr (Or.inr ⟨hci, ebef, erest, xc, hnext ▸ hw, hes, hnext ▸ hxc, ?_⟩)
      rcases hres with ⟨J, c, u, hres, hA⟩ | ⟨J, m, c, u, hres, -⟩ | ⟨o, succ, c, u, hres, hA⟩
      · rw [hres] at hend
        simp only [partEnd, blt_falseC hn, hbi, Bool.cond_false, Bool.true_and,
          Bool.and_eq_true] at hend
        obtain ⟨⟨⟨hJ, hen⟩, hle⟩, -⟩ := hend
        obtain rfl := Nat.eq_of_beq_eq_true hJ
        exact (partArr_zero (Option.isNone_iff_eq_none.mp hen)
          (partM_zero (F.ok (i + 1) hci 0 (one_le_nParts j (i + 1))))).mpr (arr_win F hci hA hle)
      · rw [hres] at hend
        simp only [partEnd, blt_falseC hn, Bool.false_and] at hend
        cases hend
      · rw [hres] at hend
        simp only [partEnd, blt_falseC hn, hbi, Bool.cond_false, Bool.true_and, Bool.and_eq_true,
          decide_eq_true_eq, Bool.not_eq_true', List.isEmpty_eq_false_iff] at hend
        obtain ⟨hne, ⟨⟨he, hJ⟩, hle⟩, -⟩ := hend
        exact (partArr_ent he).mpr ⟨Nat.eq_of_beq_eq_true hJ, hne,
          arrCh_win F hci hA hle (Nat.eq_of_beq_eq_true hJ) he⟩
    · exact Or.inr (Or.inl (part_last F hlb hi hk hr hn hci))

theorem parts_goal (F : FnH L j fp σ es vs kfps hdr ck)
    (hlb : lastOkC (coreOf j).body = true) {i : ℕ}
    (hi : i ≤ (certOf j).cuts.length) : ∀ m k, nParts j i - k = m → k < nParts j i →
      PartReach L j fp σ es vs ck i k →
      CplGoal L j fp σ vs ck ∨ (i < (certOf j).cuts.length ∧ PartReach L j fp σ es vs ck (i + 1) 0) := by
  intro m
  induction m with
  | zero => intro k hm hk; omega
  | succ m ih =>
    intro k hm hk hr
    rcases part_step F hlb hi hk hr with ⟨hk', hr'⟩ | h | h
    · exact ih (k + 1) (by omega) hk' hr'
    · exact Or.inl h
    · exact Or.inr h

theorem wins_goal (F : FnH L j fp σ es vs kfps hdr ck)
    (hlb : lastOkC (coreOf j).body = true) :
    ∀ m i, (certOf j).cuts.length - i = m → i ≤ (certOf j).cuts.length →
      PartReach L j fp σ es vs ck i 0 → CplGoal L j fp σ vs ck := by
  intro m
  induction m with
  | zero =>
    intro i hm hi hr
    rcases parts_goal F hlb hi _ 0 rfl (one_le_nParts j i) hr with h | ⟨hci, -⟩
    · exact h
    · omega
  | succ m ih =>
    intro i hm hi hr
    rcases parts_goal F hlb hi _ 0 rfl (one_le_nParts j i) hr with h | ⟨hci, hr'⟩
    · exact h
    · exact ih (i + 1) (by omega) hci hr'

end Comp

/-- **B2's completeness for one compiled function**: a function the completeness check and the
soundness windows' checks accept runs, on every path, from its entry to its return within
`pathMax` and its callees' counts. -/
theorem cpl_run {j : ℕ} (h1 : 1 ≤ j) (hj : j < nFns) (hok : CplOk j)
    (hchk : ∀ i ≤ (certOf j).cuts.length,
      checkWin glob (fnOf j) (coreOf j) (certOf j) (j == 1) i = true)
    (hpows : (certOf j).facts.pows.Ok) : CplRun j := by
  intro κ L hκ hjt htab fp hfp σ es vs hw hev kfps hdr hF ck hK
  have F : FnH L j fp σ es vs kfps hdr ck := ⟨h1, hj, hok, hchk, hpows, hκ, hjt, htab, hfp, hF, hK, hev, hw⟩
  exact wins_goal F (lastBody hok hchk) _ 0 rfl (Nat.zero_le _) (reach_zero F)

end
end LeanVM.Guest.B2C
