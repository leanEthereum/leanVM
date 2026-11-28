/-
  LeanVM.Guest.B1.VsC.RoundsLoopA

  `link_rounds`' loop helper with no grind completes placed, from any iteration.
-/

module

public import LeanVM.Guest.B1.VsC.RoundsLoadsC
public import LeanVM.Guest.B1.VsC.SqueezeLoopA
public import LeanVM.Guest.B1.VsC.RoundsLastC
public import LeanVM.Guest.B1.Link.RoundsLoop
import LeanVM.Guest.CoreRef

/-!
# `link_rounds`' loop, placed, no grind

`__loop0_link_rounds__L{nt}_L0(x, N, recs, point, tabs)`, iteration `j` at `x = g^j`: the record
`j` (seven words) at `recs·g^(7j)`, four rounds of the chain from it (`lrRounds_complete0`), their
challenges stored at `point·g^(4j)`, the record after them at `recs·g^(7j + 7)`, the tail call at
`x·g` while `x·g ≠ N`. Its words are its caller's: the records (`link_rounds`' buffer at
`ptrAt cm`, record `m` the state after `4 m` rounds, `lrRec`), the challenges, the stream words.

`lrL_step0`: one iteration by `callAtA_nodeLRd`, `lrL_callAtA0`: from iteration `j` by induction.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Link LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Protocol.Verifier
open LeanVM.Guest.Value

@[expose] public section

/-! ## The records -/

/-- Record `m`: the state after `4 m` rounds. -/
def lrRec (st0 : RSt) (l : List (E × RSt)) (m : ℕ) : RSt := chainLast st0 (l.take (4 * m))

/-- Iteration `j`'s four rounds. -/
def lrSeg (l : List (E × RSt)) (j : ℕ) : List (E × RSt) := (l.drop (4 * j)).take 4

theorem lrRec_succ (st0 : RSt) (l : List (E × RSt)) (j : ℕ) :
    lrRec st0 l (j + 1) = chainLast (lrRec st0 l j) (lrSeg l j) := by
  unfold lrRec lrSeg
  rw [show 4 * (j + 1) = 4 * j + 4 by ring, List.take_add, chainLast_append']

theorem lrSeg_chain {rd : Reader} {nt bits : ℕ} {st0 : RSt} {l : List (E × RSt)} (h : RoundChain rd nt bits st0 l)
    (j : ℕ) : RoundChain rd nt bits (lrRec st0 l j) (lrSeg l j) := by
  rw [← List.take_append_drop (4 * j) l] at h
  have h2 := (roundChain_append_inv h).2
  rw [← List.take_append_drop 4 (l.drop (4 * j))] at h2
  exact (roundChain_append_inv h2).1

theorem lrSeg_length {l : List (E × RSt)} {j : ℕ} (h : 4 * (j + 1) ≤ l.length) : (lrSeg l j).length = 4 := by
  simp [lrSeg]; omega

theorem lrSeg_pts {rd : Reader} {point : E} {l : List (E × RSt)} (h : ReadsAt rd point (l.map Prod.fst)) {j : ℕ}
    (hj : 4 * (j + 1) ≤ l.length) : ReadsAt rd (point * gen ^ (4 * j)) ((lrSeg l j).map Prod.fst) := by
  refine readsAt_of_getD fun i hi => ?_
  simp only [List.length_map, lrSeg_length hj] at hi
  have := readsAt_getD h (i := 4 * j + i) (by simp; omega)
  simpa [lrSeg, List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop, hi] using this

theorem lrRec_cap {rd : Reader} {nt bits : ℕ} {st0 : RSt} {l : List (E × RSt)} (h5 : st0.cap.length = 5)
    (h : RoundChain rd nt bits st0 l) (m : ℕ) : (lrRec st0 l m).cap.length = 5 := by
  rw [← List.take_append_drop (4 * m) l] at h
  exact chainLast_cap_length h5 (roundChain_append_inv h).1

theorem rstOf_getD {σ : Val} {cap : List ℕ} {cur cl : ℕ} (h : cap.length = 5) :
    (∀ i < 5, (rstOf σ cap cur cl).cells.getD i 0 = σ (.n (cap.getD i 0))) ∧
      (rstOf σ cap cur cl).cells.getD 5 0 = σ (.n cur) ∧ (rstOf σ cap cur cl).cells.getD 6 0 = σ (.n cl) := by
  match cap, h with
  | [a, b, c, d, e], _ =>
    refine ⟨fun i hi => ?_, rfl, rfl⟩
    interval_cases i <;> rfl

/-! ## The template's parts -/

/-- The loop's first fifteen atoms: the record's pointer, the challenges' pointer, the record read. -/
def lrLHead : List Stmt :=
  [.atom (.mul (.n 5) (.n 0) (.n 0)), .atom (.mul (.n 6) (.n 5) (.n 0)), .atom (.mul (.n 7) (.n 6) (.n 6)),
    .atom (.mul (.n 8) (.n 7) (.n 0)), .atom (.mul (.n 9) (.n 2) (.n 8)), .atom (.mul (.n 10) (.n 0) (.n 0)),
    .atom (.mul (.n 11) (.n 10) (.n 10)), .atom (.mul (.n 12) (.n 3) (.n 11)),
    .atom (.load (.n 13) (.n 9) 0), .atom (.load (.n 14) (.n 9) 1), .atom (.load (.n 15) (.n 9) 2),
    .atom (.load (.n 16) (.n 9) 3), .atom (.load (.n 17) (.n 9) 4), .atom (.load (.n 18) (.n 9) 5),
    .atom (.load (.n 19) (.n 9) 6)]

/-- The next record's stores. -/
def lrLStores (nt bits : ℕ) : List Stmt :=
  ((List.range 5).map fun j ↦ .atom (.load (.n ((lrLoopRounds nt bits).2.1.getD j 0)) (.n 9) (7 + j))) ++
    [.atom (.load (.n (lrLoopRounds nt bits).2.2.1) (.n 9) 12),
      .atom (.load (.n (lrLoopRounds nt bits).2.2.2.1) (.n 9) 13)]

/-- The next counter and its condition. -/
def lrLTail (nt bits : ℕ) : List Stmt :=
  let V := (lrLoopRounds nt bits).2.2.2.2.1
  [.atom (.const (.n V) (word 2 0)), .atom (.mul (.n (V + 1)) (.n 0) (.n V)),
    .atom (.add (.n (V + 2)) (.n (V + 1)) (.n 1)), .atom (.const (.n (V + 3)) (word 2 0)),
    .atom (.mul (.n (V + 4)) (.n 0) (.n (V + 3)))]

theorem lrLoopA_eq (nt bits : ℕ) :
    lrLoopA nt bits = lrLHead ++ (lrLoopRounds nt bits).1 ++ lrLStores nt bits ++ lrLTail nt bits := by
  simp only [lrLoopA, lrLHead, lrLStores, lrLTail, List.append_assoc, List.cons_append, List.nil_append]

/-- The loop helper's statements before its `ret`. -/
def lrLPre (nt bits : ℕ) (name : String) : List Stmt :=
  lrLoopA nt bits ++ [.callIf (.n ((lrLoopRounds nt bits).2.2.2.2.1 + 2)) name
    [.n ((lrLoopRounds nt bits).2.2.2.2.1 + 4), .n 1, .n 2, .n 3, .n 4]]

theorem lrLoopBody_pre (nt bits : ℕ) (name : String) : lrLoopBody nt bits name = lrLPre nt bits name ++ [.ret []] := by
  rw [lrLoopBody_eq]; simp [lrLPre]

/-- The record's reads. -/
def lrLReads : List Atom :=
  [.load (.n 13) (.n 9) 0, .load (.n 14) (.n 9) 1, .load (.n 15) (.n 9) 2, .load (.n 16) (.n 9) 3,
    .load (.n 17) (.n 9) 4, .load (.n 18) (.n 9) 5, .load (.n 19) (.n 9) 6]

/-- What the kernel checks of the loop helper's body with no grind. -/
def lrLChecks0 (nt : ℕ) (name : String) : Bool :=
  (chk 5 (lrLoopBody nt 0 name)).isSome &&
    lrLReads.all (fun a => !decide (a ∈ storesOf 5 (lrLoopBody nt 0 name))) &&
    (atomsOf (lrLoopBody nt 0 name)).all (fun a => mulFwdB a && noHint a) &&
    (storesOf 5 (lrLoopBody nt 0 name)).all (fun a => match a with | .load _ p _ => decide (p.idx < 18) | _ => true) &&
    (lrLPre nt 0 name).all Stmt.straight && (lrLPre nt 0 name).all plainSB &&
    (lrLoopA nt 0).all (fun s => match s with | .atom _ => true | _ => false)

/-- The block of the loop's last `m` iterations and its skipped tail. -/
def lrBlock (fs : String → ℕ) (name : String) (m : ℕ) : ℕ := m * fs name + fs (tailKey name)

/-- What the loop reads and writes of its caller's: the chain and its challenges, every record. -/
def LrLPre (nt : ℕ) (st0 : RSt) (l : List (E × RSt)) (q cm : ℕ) (point : E) (rd : Reader) : Prop :=
  RoundChain rd nt 0 st0 l ∧ ReadsAt rd point (l.map Prod.fst) ∧
    ∀ m ≤ q, ReadsAt rd (ptrAt (cm + 7 * m)) (lrRec st0 l m).cells

variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}

set_option maxHeartbeats 2000000 in
/-- **One iteration of the loop with no grind completes placed**, from its tail's completeness. -/
theorem lrL_step0 (k : ℕ) {nt : ℕ} (hnt : 1 ≤ nt) (hnt' : nt ≤ 32) {name : String} {fn : Fn}
    (hfind : coreProgram.find? name = some fn) (hlp : coreProgram.loop name = true)
    (hparams : fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4]) (hbody : fn.body = lrLoopBody nt 0 name)
    (hck : lrLChecks0 nt name = true)
    {st0 : RSt} (h5 : st0.cap.length = 5) {l : List (E × RSt)} {q cm : ℕ} (hq : 4 * q ≤ l.length) (hq16 : q < 16)
    {point tabs : E} {R : ℕ → Prop}
    (hRp : ∀ t < l.length, ∃ i, point.limb 0 * addressOfIndex t = addressOfIndex i ∧ R i)
    (hRc : ∀ t < l.length * rlen nt 0, ∃ i, st0.cur.limb 0 * addressOfIndex t = addressOfIndex i ∧ R i)
    (hRo : ∀ i, cm ≤ i → i < cm + 7 * (q + 2) → R i)
    {j : ℕ} (hj : j < q) {fp c : ℕ} (hfc : fp + lrBlock fs name (q - j) ≤ c)
    (htail : j + 1 < q → ∀ fp' c', fp' + lrBlock fs name (q - (j + 1)) ≤ c' →
      CallAtA fs al cert k name [gen ^ (j + 1), gen ^ q, ptrAt cm, point, tabs] [] R (fun _ => False)
        (fun _ => True) (LrLPre nt st0 l q cm point) PostQuiet (lrBlock fs name (q - (j + 1))) fp' c' c') :
    CallAtA fs al cert k name [gen ^ j, gen ^ q, ptrAt cm, point, tabs] [] R (fun _ => False)
      (fun _ => True) (LrLPre nt st0 l q cm point) PostQuiet (lrBlock fs name (q - j)) fp c c := by
  have hblk : lrBlock fs name (q - j) = fs name + lrBlock fs name (q - (j + 1)) := by
    obtain ⟨m, hm⟩ : ∃ m, q - j = m + 1 := ⟨q - j - 1, by omega⟩
    rw [lrBlock, lrBlock, hm, show q - (j + 1) = m by omega, Nat.add_mul, one_mul]; ring
  rw [hblk] at hfc ⊢
  simp only [lrLChecks0, Bool.and_eq_true] at hck
  obtain ⟨⟨⟨⟨⟨⟨hc, hrd⟩, hat⟩, hSl⟩, hst⟩, hpl⟩, hall⟩ := hck
  replace hrd := List.all_eq_true.mp hrd
  replace hat := List.all_eq_true.mp hat
  replace hSl := List.all_eq_true.mp hSl
  replace hall := List.all_eq_true.mp hall
  obtain ⟨c', hc⟩ := Option.isSome_iff_exists.mp hc
  set args : List E := [gen ^ j, gen ^ q, ptrAt cm, point, tabs] with hargs
  have hc' : chk args.length fn.body = some c' := by rw [hbody]; exact hc
  obtain ⟨σ, hσ⟩ : ∃ σ : Reader → Val, ∀ rd, σ rd = fwdVal rd (fun _ => 0) args fn.body := ⟨_, fun _ => rfl⟩
  set S := storesOf args.length fn.body with hS
  have hSe : S = storesOf 5 (lrLoopBody nt 0 name) := by rw [hS, hbody]; rfl
  set rs := lrLoopRounds nt 0 with hrs
  set Vv := rs.2.2.2.2.1 with hVv
  have hmB : ∀ a, Stmt.atom a ∈ lrLoopA nt 0 → Stmt.atom a ∈ fn.body := fun a ha => by
    rw [hbody, lrLoopBody_pre, lrLPre]; exact List.mem_append_left _ (List.mem_append_left _ ha)
  have hmH : ∀ a, Stmt.atom a ∈ lrLHead → Stmt.atom a ∈ fn.body := fun a ha => hmB a (by
    rw [lrLoopA_eq]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ ha)))
  have hmR : ∀ a, Stmt.atom a ∈ rs.1 → Stmt.atom a ∈ fn.body := fun a ha => hmB a (by
    rw [lrLoopA_eq]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ha)))
  have hmS : ∀ a, Stmt.atom a ∈ lrLStores nt 0 → Stmt.atom a ∈ fn.body := fun a ha => hmB a (by
    rw [lrLoopA_eq]; exact List.mem_append_left _ (List.mem_append_right _ ha))
  have hmT : ∀ a, Stmt.atom a ∈ lrLTail nt 0 → Stmt.atom a ∈ fn.body := fun a ha => hmB a (by
    rw [lrLoopA_eq]; exact List.mem_append_right _ ha)
  have G : ∀ rd a, Stmt.atom a ∈ fn.body → Good rd S (fun _ => 0) (σ rd) a := fun rd a ha => by
    rw [hσ]; exact fwd_good hc' a ha
  -- the values the memory does not change
  have hv : ∀ rd, σ rd (.n 0) = gen ^ j ∧ σ rd (.n 1) = gen ^ q ∧ σ rd (.n 2) = ptrAt cm ∧ σ rd (.n 3) = point ∧
      σ rd (.n 4) = tabs ∧ σ rd (.n 9) = ptrAt (cm + 7 * j) ∧ σ rd (.n 12) = point * gen ^ (4 * j) ∧
      σ rd (.n (Vv + 2)) = gen ^ (j + 1) + gen ^ q ∧ σ rd (.n (Vv + 4)) = gen ^ (j + 1) := by
    intro rd
    have p0 : σ rd (.n 0) = gen ^ j := by rw [hσ]; exact fwd_param hc' (by simp [hargs])
    have p1 : σ rd (.n 1) = gen ^ q := by rw [hσ]; exact fwd_param hc' (by simp [hargs])
    have p2 : σ rd (.n 2) = ptrAt cm := by rw [hσ]; exact fwd_param hc' (by simp [hargs])
    have p3 : σ rd (.n 3) = point := by rw [hσ]; exact fwd_param hc' (by simp [hargs])
    have p4 : σ rd (.n 4) = tabs := by rw [hσ]; exact fwd_param hc' (by simp [hargs])
    have gm : ∀ d x y : ℕ, Stmt.atom (.mul (.n d) (.n x) (.n y)) ∈ fn.body → x < d → y < d →
        σ rd (.n d) = σ rd (.n x) * σ rd (.n y) := fun d x y hm hx hy => good_mul_eq (G rd _ hm) hx hy
    have m5 := gm 5 0 0 (hmH _ (by simp [lrLHead])) (by norm_num) (by norm_num)
    have m6 := gm 6 5 0 (hmH _ (by simp [lrLHead])) (by norm_num) (by norm_num)
    have m7 := gm 7 6 6 (hmH _ (by simp [lrLHead])) (by norm_num) (by norm_num)
    have m8 := gm 8 7 0 (hmH _ (by simp [lrLHead])) (by norm_num) (by norm_num)
    have m9 := gm 9 2 8 (hmH _ (by simp [lrLHead])) (by norm_num) (by norm_num)
    have m10 := gm 10 0 0 (hmH _ (by simp [lrLHead])) (by norm_num) (by norm_num)
    have m11 := gm 11 10 10 (hmH _ (by simp [lrLHead])) (by norm_num) (by norm_num)
    have m12 := gm 12 3 11 (hmH _ (by simp [lrLHead])) (by norm_num) (by norm_num)
    have c0 : σ rd (.n Vv) = word 2 0 := G rd (.const (.n Vv) (word 2 0)) (hmT _ (by simp [lrLTail, hVv, hrs]))
    have m1 := gm (Vv + 1) 0 Vv (hmT _ (by simp [lrLTail, hVv, hrs])) (by omega) (by omega)
    have a2 : σ rd (.n (Vv + 2)) = σ rd (.n (Vv + 1)) + σ rd (.n 1) :=
      G rd (.add (.n (Vv + 2)) (.n (Vv + 1)) (.n 1)) (hmT _ (by simp [lrLTail, hVv, hrs]))
    have c3 : σ rd (.n (Vv + 3)) = word 2 0 :=
      G rd (.const (.n (Vv + 3)) (word 2 0)) (hmT _ (by simp [lrLTail, hVv, hrs]))
    have m4 := gm (Vv + 4) 0 (Vv + 3) (hmT _ (by simp [lrLTail, hVv, hrs])) (by omega) (by omega)
    refine ⟨p0, p1, p2, p3, p4, ?_, ?_, ?_, ?_⟩
    · rw [m9, m8, m7, m6, m5, p2, p0, ← ptrAt_mul_gen_pow']; ring
    · rw [m12, m11, m10, p3, p0]; ring
    · rw [a2, m1, c0, p0, p1, word_gen, gen_pow_mul_gen]
    · rw [m4, c3, p0, word_gen, gen_pow_mul_gen]
  obtain ⟨σ0, hσ0⟩ : ∃ σ0, σ0 = σ (fun _ => none) := ⟨_, rfl⟩
  have hv0 := hv (fun _ => none)
  rw [← hσ0] at hv0
  have h78 : σ0 (.n (Vv + 2)) = gen ^ (j + 1) + gen ^ q := hv0.2.2.2.2.2.2.2.1
  obtain ⟨es, hes⟩ : ∃ es, es = (lrLPre nt 0 name).flatMap (slEvs σ0) := ⟨_, rfl⟩
  have hesr : ∀ rd, (lrLPre nt 0 name).flatMap (slEvs (σ rd)) = es := fun rd => by
    rw [hes]
    refine slEvs_congr _ fun c f args hm => ?_
    simp only [lrLPre, List.mem_append, List.mem_singleton, Stmt.callIf.injEq] at hm
    rcases hm with hm | ⟨rfl, -, -⟩
    · exact absurd (hall _ hm) (by simp)
    · rw [(hv rd).2.2.2.2.2.2.2.1, h78]
  have hw : ∀ rd, walk (σ rd) fn.body = .ret es [] := fun rd => by
    rw [hbody, lrLoopBody_pre, walk_straight _ _ _ hst, hesr]
  obtain ⟨hd0, ha0, hr0, hh0⟩ : allocDsts es = [] ∧ allocs σ0 es = [] ∧ addrs es = [] ∧ heapHintAddrs σ0 es = [] := by
    rw [hes]; exact plainSB_parts hst hpl
  have hcalls : calls es = [⟨name, [.n (Vv + 4), .n 1, .n 2, .n 3, .n 4], [], decide (σ0 (.n (Vv + 2)) ≠ 0)⟩] := by
    rw [hes, (straight_parts σ0 _ hst).2.2.2]
    have : (lrLoopA nt 0).filterMap Stmt.callS = [] := List.filterMap_eq_nil_iff.mpr fun s hs => by
      have := hall s hs
      split at this <;> simp_all [Stmt.callS]
    simp [lrLPre, List.filterMap_append, this, Stmt.callS, mkCall, hVv, hrs]
  have hargs1 : [V.n (Vv + 4), .n 1, .n 2, .n 3, .n 4].map σ0 = [gen ^ (j + 1), gen ^ q, ptrAt cm, point, tabs] := by
    have h1 : σ0 (.n 1) = gen ^ q := hv0.2.1
    have h2 : σ0 (.n 2) = ptrAt cm := hv0.2.2.1
    have h3 : σ0 (.n 3) = point := hv0.2.2.2.1
    have h4 : σ0 (.n 4) = tabs := hv0.2.2.2.2.1
    have h80 : σ0 (.n (Vv + 4)) = gen ^ (j + 1) := hv0.2.2.2.2.2.2.2.2
    simp only [List.map_cons, List.map_nil, h1, h2, h3, h4, h80]
  have htk : decide (σ0 (.n (Vv + 2)) ≠ 0) = decide (j + 1 ≠ q) := by
    rw [h78]
    refine decide_eq_decide.mpr ⟨fun h he => h (by rw [he]; exact e_add_eq_zero_iff.mpr rfl), fun h he => h ?_⟩
    exact gen_pow_inj (by omega) (by omega) (e_add_eq_zero_iff.mp he)
  refine callAtA_nodeLRd hlp hfc ⟨σ0, fn, es, [], [], [PostQuiet], fun _ => True, fun _ => False, hfind,
    ⟨by simp, List.Pairwise.nil⟩, fun _ h => h.elim, ?_, fun _ _ => trivial, ?_⟩
  · -- the tail call
    rw [hcalls, ha0, htk, KidsAtL]
    by_cases hlt : j + 1 < q
    · have ht : decide (j + 1 ≠ q) = true := decide_eq_true (by omega)
      simp only [ht, ↓reduceIte]
      refine ⟨R, fun _ => False, fun _ => True, fun i hi => Or.inl (Or.inl hi), ?_, fun _ _ _ => trivial,
        fun _ h => h.elim⟩
      rw [hargs1]
      exact (htail hlt (fp + fs name) c (by omega)).mono (fun _ h => h) (fun _ h => h) (fun _ _ => trivial)
        (fun _ h => h.1) (fun _ _ _ h => h)
    · have ht : decide (j + 1 ≠ q) = false := decide_eq_false (by omega)
      simp only [ht, Bool.false_eq_true, ↓reduceIte]
      refine ⟨⟨fun v => ([V.n (Vv + 4), .n 1, .n 2, .n 3, .n 4].map σ0).getD v.idx 0, fn, hfind,
        by rw [hparams]; rfl⟩, ?_, by simp, fun _ _ => trivial, fun _ h => h.elim⟩
      rw [lrBlock, show q - (j + 1) = 0 by omega]; simp
  · -- each memory
    intro rd _ ⟨hch, hpts, hrec⟩ _
    obtain ⟨p0, p1, p2, p3, p4, p9, p12, p78, p80⟩ := hv rd
    obtain ⟨-, ha, -, -⟩ := plainSB_parts (σ := σ rd) hst hpl
    rw [hesr rd] at ha
    have hj4 : 4 * (j + 1) ≤ l.length := by omega
    have hrj := hrec j hj.le
    have hrj1 := hrec (j + 1) (by omega)
    have h5j := lrRec_cap h5 hch j
    obtain ⟨e0, e1, e2, e3, e4, eu, ev, hcl, hstj⟩ := cells_eq_seven h5j
    -- the record's reads
    have hreads : ∀ i < 7, σ rd (.n (13 + i)) = (lrRec st0 l j).cells.getD i 0 ∧
        (Atom.load (.n (13 + i)) (.n 9) i).Holds rd (σ rd) := by
      intro i hi
      have hm : Stmt.atom (.load (.n (13 + i)) (.n 9) i) ∈ fn.body := hmH _ (by interval_cases i <;> simp [lrLHead])
      have hS' : Atom.load (.n (13 + i)) (.n 9) i ∉ S := fun h => by
        have hm' : Atom.load (.n (13 + i)) (.n 9) i ∈ lrLReads := by interval_cases i <;> simp [lrLReads]
        have := hrd _ hm'
        simp only [Bool.not_eq_true', decide_eq_false_iff_not] at this
        exact this (by rw [hSe] at h; exact h)
      have hx : LoadHolds rd (σ rd (.n 9)) i ((lrRec st0 l j).cells.getD i 0) := by
        rw [p9]; exact readsAt_getD hrj (by rw [hcl]; simp; omega)
      exact ⟨good_load_eq hx (G rd _ hm) hS', holds_load_of_good (G rd _ hm) hS' hx⟩
    have hst0 : rstOf (σ rd) [13, 14, 15, 16, 17] 18 19 = lrRec st0 l j := by
      have f0 := (hreads 0 (by norm_num)).1; have f1 := (hreads 1 (by norm_num)).1
      have f2 := (hreads 2 (by norm_num)).1; have f3 := (hreads 3 (by norm_num)).1
      have f4 := (hreads 4 (by norm_num)).1; have f5 := (hreads 5 (by norm_num)).1
      have f6 := (hreads 6 (by norm_num)).1
      rw [hcl] at f0 f1 f2 f3 f4 f5 f6
      simp only [Nat.reduceAdd, List.getD_cons_zero, List.getD_cons_succ] at f0 f1 f2 f3 f4 f5 f6
      rw [hstj]
      simp only [rstOf, List.map_cons, List.map_nil, Function.comp_apply, f0, f1, f2, f3, f4, f5, f6]
    have hSp : ∀ d p off, Atom.load d p off ∈ S → p.idx < 18 := fun d p off h => by
      have := hSl _ (by rw [hSe] at h; exact h)
      simpa using this
    have hmf : ∀ d x y, Stmt.atom (.mul d x y) ∈ rs.1 → x.idx < d.idx ∧ y.idx < d.idx := fun d x y ha => by
      have := hat _ (mem_atomsOf' (by rw [← hbody]; exact hmR _ ha))
      simp only [Bool.and_eq_true] at this
      simpa [mulFwdB] using this.1
    have hseg := lrSeg_chain hch j
    have hsegl := lrSeg_length hj4
    have hsegp : ReadsAt rd (σ rd (.n 12)) ((lrSeg l j).map Prod.fst) := by rw [p12]; exact lrSeg_pts hpts hj4
    obtain ⟨hR, hlast, -, -, -⟩ := lrRounds_complete0 (m := 18) (S := S) (w := fun _ => 0) (σ := σ rd) (pts := 12)
      (tabs := 4) hnt hnt' hSp 4 20 [13, 14, 15, 16, 17] 18 19 none _ _ (by norm_num) (by norm_num)
      (fun a ha => G rd a (hmR a ha)) hmf (fun z hz => absurd hz (by simp)) hst0 hsegl hseg hsegp
    have hLd := lrRounds_loads0 (m := 18) (S := S) (w := fun _ => 0) (σ := σ rd) (pts := 12) (tabs := 4)
      hnt hnt' hSp 4 20 [13, 14, 15, 16, 17] 18 19 none _ _ (by norm_num) (by norm_num)
      (fun a ha => G rd a (hmR a ha)) hmf (fun z hz => absurd hz (by simp)) hst0 hsegl hseg hsegp
    rw [← lrRec_succ] at hlast
    have hlen : rs.2.1.length = 5 := lrRounds_cap_length _ _ _ _ _ _ _ _ _ _ rfl
    have hlen' : (lrRounds nt 0 12 4 4 20 [13, 14, 15, 16, 17] 18 19 none).2.1.length = 5 := hlen
    have hrs' : rs = lrRounds nt 0 12 4 4 20 [13, 14, 15, 16, 17] 18 19 none := rfl
    -- every atom of the iteration
    have hA : ∀ a, Stmt.atom a ∈ lrLoopA nt 0 → a.Holds rd (σ rd) := by
      intro a ha
      rw [lrLoopA_eq] at ha
      simp only [List.mem_append] at ha
      rcases ha with ((ha | ha) | ha) | ha
      · simp only [lrLHead, List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
        rcases ha with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h
        exacts [holds_of_good' (G rd _ (hmH _ (by simp [lrLHead]))) rfl,
          holds_of_good' (G rd _ (hmH _ (by simp [lrLHead]))) rfl,
          holds_of_good' (G rd _ (hmH _ (by simp [lrLHead]))) rfl,
          holds_of_good' (G rd _ (hmH _ (by simp [lrLHead]))) rfl,
          holds_of_good' (G rd _ (hmH _ (by simp [lrLHead]))) rfl,
          holds_of_good' (G rd _ (hmH _ (by simp [lrLHead]))) rfl,
          holds_of_good' (G rd _ (hmH _ (by simp [lrLHead]))) rfl,
          holds_of_good' (G rd _ (hmH _ (by simp [lrLHead]))) rfl, (hreads 0 (by norm_num)).2, (hreads 1 (by norm_num)).2, (hreads 2 (by norm_num)).2,
          (hreads 3 (by norm_num)).2, (hreads 4 (by norm_num)).2, (hreads 5 (by norm_num)).2,
          (hreads 6 (by norm_num)).2]
      · exact hR a ha
      · -- the next record stored
        have hrec1 : ReadsAt rd (σ rd (.n 9) * gen ^ 7) (lrRec st0 l (j + 1)).cells := by
          rw [p9, ptrAt_mul_gen_pow', show cm + 7 * j + 7 = cm + 7 * (j + 1) by ring]; exact hrj1
        rw [← hlast] at hrec1
        simp only [lrLStores, List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil,
          or_false, Stmt.atom.injEq] at ha
        rcases ha with ⟨i, hi, rfl⟩ | rfl | rfl
        · show LoadHolds rd (σ rd (.n 9)) (7 + i) (σ rd (.n (rs.2.1.getD i 0)))
          rw [← loadHolds_mul_gen_pow,
            ← (rstOf_getD (σ := σ rd) (cur := rs.2.2.1) (cl := rs.2.2.2.1) hlen).1 i (by omega)]
          exact readsAt_getD hrec1 (by simp [RSt.cells, rstOf, hlen']; omega)
        · show LoadHolds rd (σ rd (.n 9)) 12 (σ rd (.n rs.2.2.1))
          rw [show (12 : ℕ) = 7 + 5 from rfl, ← loadHolds_mul_gen_pow,
            ← (rstOf_getD (σ := σ rd) (cur := rs.2.2.1) (cl := rs.2.2.2.1) hlen).2.1]
          exact readsAt_getD hrec1 (by simp [RSt.cells, rstOf, hlen'])
        · show LoadHolds rd (σ rd (.n 9)) 13 (σ rd (.n rs.2.2.2.1))
          rw [show (13 : ℕ) = 7 + 6 from rfl, ← loadHolds_mul_gen_pow,
            ← (rstOf_getD (σ := σ rd) (cur := rs.2.2.1) (cl := rs.2.2.2.1) hlen).2.2]
          exact readsAt_getD hrec1 (by simp [RSt.cells, rstOf, hlen'])
      · simp only [lrLTail, List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
        rcases ha with rfl | rfl | rfl | rfl | rfl <;>
          exact holds_of_good' (G rd _ (hmT _ (by simp [lrLTail]))) (by simp [needsSide])
    refine ⟨σ rd, by rw [hparams]; simp [p0, p1, p2, p3, p4, hargs], hw rd, rfl, by rw [ha, ha0], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [ha0]
      exact ⟨by rw [hd0]; rfl, by rw [hr0]; simp⟩
    · rw [hcalls]
      intro cl hcl
      simp only [List.mem_singleton] at hcl
      subst hcl
      exact ⟨by rw [hargs1]; simp only [List.map_cons, List.map_nil, p1, p2, p3, p4, p80], rfl⟩
    · -- the loads
      intro A hA
      rw [ha0]
      rw [← hesr rd] at hA
      rw [Memory.loadAddrs_straight _ _ hst] at hA
      obtain ⟨⟨x, off⟩, hq', rfl⟩ := List.mem_map.mp hA
      obtain ⟨s, hs, hq'⟩ := List.mem_filterMap.mp hq'
      simp only [lrLPre, List.mem_append, List.mem_singleton] at hs
      rcases hs with hs | rfl
      swap
      · simp [stmtLoad?] at hq'
      obtain ⟨a, rfl⟩ : ∃ a, s = .atom a := by
        have := hall s hs
        split at this
        · exact ⟨_, rfl⟩
        · simp at this
      cases a with
      | load d p o =>
        simp only [stmtLoad?, Option.some.injEq, Prod.mk.injEq] at hq'
        obtain ⟨rfl, rfl⟩ := hq'
        rw [lrLoopA_eq] at hs
        simp only [List.mem_append] at hs
        have hown : ∀ o', o' < 14 → ∃ i, (σ rd (.n 9)).limb 0 * addressOfIndex o' = addressOfIndex i ∧
            (ownData cert fp c name [] es i ∨ R i ∨ False) := fun o' ho' =>
          ⟨cm + 7 * j + o', by rw [p9]; exact Main.addr_ofK _ _, Or.inr (Or.inl (hRo _ (by omega) (by omega)))⟩
        rcases hs with ((hs | hs) | hs) | hs
        · simp only [lrLHead, List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at hs
          rcases hs with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
            first | (obtain ⟨rfl, rfl, rfl⟩ := Atom.load.inj h; exact hown _ (by norm_num)) | cases h
        · rcases hLd d p o hs with ⟨rfl, hoff⟩ | ⟨r, hr, hoff, hq⟩
          · obtain ⟨i, hi, hRi⟩ := hRp (4 * j + o) (by omega)
            refine ⟨i, ?_, Or.inr (Or.inl hRi)⟩
            rw [p12, ← hi, gen_pow_eq_ofK, limb0_mul_ofK, mul_assoc, addressOfIndex, addressOfIndex,
              addressOfIndex, ← pow_add]
          · have hcr : (chainLast (lrRec st0 l j) ((lrSeg l j).take r)).cur =
                st0.cur * gen ^ ((4 * j + r) * rlen nt 0) := by
              have e : chainLast (lrRec st0 l j) ((lrSeg l j).take r) = chainLast st0 (l.take (4 * j + r)) := by
                unfold lrRec lrSeg
                rw [List.take_take, show min r 4 = r by omega, ← chainLast_append', ← List.take_add]
              rw [e, chain_cur st0 l hch _ (by omega)]
            obtain ⟨i, hi, hRi⟩ := hRc ((4 * j + r) * rlen nt 0 + o) (by
              have : (4 * j + r + 1) * rlen nt 0 ≤ l.length * rlen nt 0 := Nat.mul_le_mul_right _ (by omega)
              have hR0 : rlen nt 0 = nt + 1 := by simp [rlen]
              rw [hR0] at this ⊢; nlinarith)
            refine ⟨i, ?_, Or.inr (Or.inl hRi)⟩
            rw [hq, hcr, ← hi, gen_pow_eq_ofK, limb0_mul_ofK, mul_assoc, addressOfIndex, addressOfIndex,
              addressOfIndex, ← pow_add]
        · simp only [lrLStores, List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil,
            or_false, Stmt.atom.injEq] at hs
          rcases hs with ⟨i, hi, h⟩ | h | h <;> obtain ⟨rfl, rfl, rfl⟩ := Atom.load.inj h
          · exact hown _ (by omega)
          · exact hown _ (by norm_num)
          · exact hown _ (by norm_num)
        · simp only [lrLTail, List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at hs
          rcases hs with h | h | h | h | h <;> cases h
      | _ => simp [stmtLoad?] at hq'
    · intro A hA
      rw [← hesr rd, (plainSB_parts (σ := σ rd) hst hpl).2.2.2] at hA
      simp at hA
    · intro ev hev
      rw [← hesr rd] at hev
      obtain ⟨s, hs, hev⟩ := List.mem_flatMap.mp hev
      simp only [lrLPre, List.mem_append, List.mem_singleton] at hs
      rcases hs with hs | rfl
      · obtain ⟨a, rfl⟩ : ∃ a, s = .atom a := by
          have := hall s hs
          split at this
          · exact ⟨_, rfl⟩
          · simp at this
        simp only [slEvs, List.mem_singleton] at hev
        subst hev
        exact hA a hs
      · simp only [slEvs, List.mem_cons, List.not_mem_nil, or_false] at hev
        rcases hev with rfl | rfl
        · show IsInK (σ rd (.n (Vv + 2))); rw [p78]; exact isInK_add (gen_pow_isInK _) (gen_pow_isInK _)
        · split <;> trivial
    · intro ts hv' hp'
      refine postQuiet_node hfind (hw rd) (fun a ha' => ?_) (fun ev hev => ?_) hv' ?_ _
      · rw [← hesr rd] at ha'
        obtain ⟨s, hs, hev⟩ := List.mem_flatMap.mp ha'
        simp only [lrLPre, List.mem_append, List.mem_singleton] at hs
        rcases hs with hs | rfl
        · obtain ⟨b, rfl⟩ : ∃ b, s = .atom b := by
            have := hall s hs
            split at this
            · exact ⟨_, rfl⟩
            · simp at this
          simp only [slEvs, List.mem_singleton, Ev.atom.injEq] at hev
          subst hev
          have := (hat a (mem_atomsOf' (by rw [← hbody]; exact hmB _ hs)))
          simp only [Bool.and_eq_true] at this
          cases a with
          | hint hh => simp [noHint] at this
          | _ => rfl
        · simp only [slEvs, List.mem_cons, List.not_mem_nil, or_false] at hev
          rcases hev with h | h
          · cases h
          · split at h <;> cases h
      · rw [← hesr rd] at hev
        obtain ⟨s, hs, hev⟩ := List.mem_flatMap.mp hev
        simp only [lrLPre, List.mem_append, List.mem_singleton] at hs
        rcases hs with hs | rfl
        · obtain ⟨b, rfl⟩ : ∃ b, s = .atom b := by
            have := hall s hs
            split at this
            · exact ⟨_, rfl⟩
            · simp at this
          simp only [slEvs, List.mem_singleton] at hev
          subst hev
          have := hat b (mem_atomsOf' (by rw [← hbody]; exact hmB _ hs))
          simp only [Bool.and_eq_true] at this
          cases b with
          | hint hh => simp [noHint] at this
          | _ => trivial
        · simp only [slEvs, List.mem_cons, List.not_mem_nil, or_false] at hev
          rcases hev with rfl | rfl
          · trivial
          · split <;> trivial
      · rw [hcalls] at hp' ⊢; exact hp'

/-- **The loop with no grind completes placed from iteration `j`**, at any frame past its block. -/
theorem lrL_callAtA0 (k : ℕ) {nt : ℕ} (hnt : 1 ≤ nt) (hnt' : nt ≤ 32) {name : String} {fn : Fn}
    (hfind : coreProgram.find? name = some fn) (hlp : coreProgram.loop name = true)
    (hparams : fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4]) (hbody : fn.body = lrLoopBody nt 0 name)
    (hck : lrLChecks0 nt name = true)
    {st0 : RSt} (h5 : st0.cap.length = 5) {l : List (E × RSt)} {q cm : ℕ} (hq : 4 * q ≤ l.length) (hq16 : q < 16)
    {point tabs : E} {R : ℕ → Prop}
    (hRp : ∀ t < l.length, ∃ i, point.limb 0 * addressOfIndex t = addressOfIndex i ∧ R i)
    (hRc : ∀ t < l.length * rlen nt 0, ∃ i, st0.cur.limb 0 * addressOfIndex t = addressOfIndex i ∧ R i)
    (hRo : ∀ i, cm ≤ i → i < cm + 7 * (q + 2) → R i) :
    ∀ j < q, ∀ fp c, fp + lrBlock fs name (q - j) ≤ c →
      CallAtA fs al cert k name [gen ^ j, gen ^ q, ptrAt cm, point, tabs] [] R (fun _ => False)
        (fun _ => True) (LrLPre nt st0 l q cm point) PostQuiet (lrBlock fs name (q - j)) fp c c := by
  have key : ∀ t j, j + 1 + t = q → ∀ fp c, fp + lrBlock fs name (q - j) ≤ c →
      CallAtA fs al cert k name [gen ^ j, gen ^ q, ptrAt cm, point, tabs] [] R (fun _ => False)
        (fun _ => True) (LrLPre nt st0 l q cm point) PostQuiet (lrBlock fs name (q - j)) fp c c := by
    intro t
    induction t with
    | zero =>
      intro j hj fp c hfc
      exact lrL_step0 k hnt hnt' hfind hlp hparams hbody hck h5 hq hq16 hRp hRc hRo
        (by omega) hfc (fun h' => absurd h' (by omega))
    | succ t ih =>
      intro j hj fp c hfc
      exact lrL_step0 k hnt hnt' hfind hlp hparams hbody hck h5 hq hq16 hRp hRc hRo
        (by omega) hfc (fun _ => ih (j + 1) (by omega))
  intro j hj
  exact key (q - j - 1) j (by omega)

end
end LeanVM.Guest.B1.VsC
