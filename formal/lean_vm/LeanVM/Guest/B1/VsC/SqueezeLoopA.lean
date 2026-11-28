/-
  LeanVM.Guest.B1.VsC.SqueezeLoopA

  `squeeze_packed`'s loop helper completes placed, from any iteration.
-/

module

public import LeanVM.Guest.B1.VsC.SqueezeFwd
public import LeanVM.Guest.B1.VsC.LinkCalleesA
public import LeanVM.Guest.Complete.ComposeRd
public import LeanVM.Guest.Value.FieldBits
import LeanVM.Guest.CoreRef

/-!
# `squeeze_packed`'s loop, placed

`__loop0_squeeze_packed(x, N, recs, out)`, iteration `j` at `x = g^j`: the capacity record `j` at
`recs·g^(5j)`, four permutations of it, their cells stored at `out·g^(32j)` and the next record at
`recs·g^(5j + 5)`, then the tail call at `x·g` while `x·g ≠ N`. It places nothing; its words are its
caller's: the records (`squeeze_packed`'s buffer at `ptrAt cm`) and the packed draw's cells at
`out` (`SpLPre`).

`spL_step`: one iteration by `callAtA_nodeLRd`, on the forward evaluation per memory, its stores'
words by `spPerms_fwd`. `spL_callAtA`: from iteration `j`, by induction, at any frame past its block
(`spBlock`, the `q - j` iterations then the skipped tail's frame).
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Link LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Protocol.Verifier
open LeanVM.Guest.Value
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

/-! ## The template's parts -/

/-- A straight statement placing nothing: no `HeapBuf`, no hint to the heap, no `frameAddr`. -/
def plainSB : Stmt → Bool
  | .atom (.hint (.alloc ..)) => false
  | .atom (.hint (.allocDyn ..)) => false
  | .atom (.hint h) => ((hintDest? h).bind destHeap?).isNone
  | .atom (.frameAddr ..) => false
  | _ => true

theorem plainSB_parts {σ : Val} {pre : List Stmt} (hs : pre.all Stmt.straight = true)
    (hp : pre.all plainSB = true) :
    allocDsts (pre.flatMap (slEvs σ)) = [] ∧ allocs σ (pre.flatMap (slEvs σ)) = [] ∧
      addrs (pre.flatMap (slEvs σ)) = [] ∧ heapHintAddrs σ (pre.flatMap (slEvs σ)) = [] := by
  obtain ⟨h1, h2, h3, -⟩ := straight_parts σ pre hs
  have hpl : ∀ s ∈ pre, plainSB s = true := fun s hs' => List.all_eq_true.mp hp s hs'
  have ha : pre.filterMap Stmt.allocSz = [] := List.filterMap_eq_nil_iff.mpr fun s hs' => by
    have := hpl s hs'
    cases s with
    | atom a =>
      cases a with
      | hint h => cases h <;> simp_all [plainSB, Stmt.allocSz]
      | _ => simp_all [plainSB, Stmt.allocSz]
    | _ => simp [Stmt.allocSz]
  have hd : pre.filterMap Stmt.addrS = [] := List.filterMap_eq_nil_iff.mpr fun s hs' => by
    have := hpl s hs'
    cases s with
    | atom a =>
      cases a with
      | hint h => cases h <;> simp_all [plainSB, Stmt.addrS]
      | _ => simp_all [plainSB, Stmt.addrS]
    | _ => simp [Stmt.addrS]
  refine ⟨by rw [h1, ha]; rfl, by rw [h2, ha]; rfl, by rw [h3, hd], ?_⟩
  refine List.eq_nil_iff_forall_not_mem.mpr fun A hA => ?_
  obtain ⟨e, he, hA⟩ := List.mem_flatMap.mp hA
  obtain ⟨s, hs', he⟩ := List.mem_flatMap.mp he
  have := hpl s hs'
  cases s with
  | atom a =>
    simp only [slEvs, List.mem_singleton] at he
    subst he
    cases a with
    | hint h =>
      cases h <;> simp_all [plainSB, Ev.hintAddrs, hintDest?, Option.isNone_iff_eq_none]
    | _ => simp_all [plainSB, Ev.hintAddrs]
  | call f args rets =>
    simp only [slEvs, List.mem_singleton] at he
    subst he
    simp [Ev.hintAddrs] at hA
  | callIf c f args =>
    simp only [slEvs, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · simp [Ev.hintAddrs] at hA
    · split at hA <;> simp [Ev.hintAddrs] at hA
  | _ => simp [slEvs] at he

theorem ptrAt_mul_gen_pow' (q m : ℕ) : ptrAt q * gen ^ m = ptrAt (q + m) := by
  rw [gen_pow_eq_ofK, ptrAt, ptrAt, ← gpow_add']; exact (map_mul (algebraMap K E) _ _).symm

/-- The loop helper's name. -/
def spLName : String := "__loop0_squeeze_packed"

theorem find_spL : coreProgram.find? spLName = some fn% «squeeze_packed_loop0» :=
  coreProgram_find?_at (j := idx% «squeeze_packed_loop0») rfl

theorem spL_loop : coreProgram.loop spLName = true := by decide +kernel

theorem spL_params : (fn% «squeeze_packed_loop0»).params = [.n 0, .n 1, .n 2, .n 3] := rfl

/-- The loop helper's statements before its `ret`. -/
def spLPre : List Stmt := spLoopA ++ [.callIf (.n 78) spLName [.n 80, .n 1, .n 2, .n 3]]

theorem spL_body : (fn% «squeeze_packed_loop0»).body = spLPre ++ [.ret []] := by
  rw [spLoop_body]; simp [spLoopBody, spLPre, spLName]

/-- The loop's first twenty atoms: the record's pointer, the cells' pointer, the record read, the
zeros. -/
def spLHead : List Stmt :=
  [.atom (.mul (.n 4) (.n 0) (.n 0)), .atom (.mul (.n 5) (.n 4) (.n 4)), .atom (.mul (.n 6) (.n 5) (.n 0)),
    .atom (.mul (.n 7) (.n 2) (.n 6)), .atom (.mul (.n 8) (.n 0) (.n 0)), .atom (.mul (.n 9) (.n 8) (.n 8)),
    .atom (.mul (.n 10) (.n 9) (.n 9)), .atom (.mul (.n 11) (.n 10) (.n 10)),
    .atom (.mul (.n 12) (.n 11) (.n 11)), .atom (.mul (.n 13) (.n 3) (.n 12)),
    .atom (.load (.n 14) (.n 7) 0), .atom (.load (.n 15) (.n 7) 1), .atom (.load (.n 16) (.n 7) 2),
    .atom (.load (.n 17) (.n 7) 3), .atom (.load (.n 18) (.n 7) 4), .atom (.const (.n 19) (word 1 0)),
    .atom (.const (.n 20) (word 0 0)), .atom (.const (.n 21) (word 0 0)), .atom (.const (.n 22) (word 0 0)),
    .atom (.const (.n 23) (word 0 0))]

/-- The loop's last five atoms: the next counter and its condition. -/
def spLTail : List Stmt :=
  [.atom (.const (.n 76) (word 2 0)), .atom (.mul (.n 77) (.n 0) (.n 76)), .atom (.add (.n 78) (.n 77) (.n 1)),
    .atom (.const (.n 79) (word 2 0)), .atom (.mul (.n 80) (.n 0) (.n 79))]

theorem spLoopA_eq : spLoopA = spLHead ++ spPermsT 24 [14, 15, 16, 17, 18] 20 13 0 4 ++
    ((List.range 5).map fun j ↦ .atom (.load (.n (71 + j)) (.n 7) (5 + j))) ++ spLTail := rfl

/-- The record's reads. -/
def spLReads : List Atom :=
  [.load (.n 14) (.n 7) 0, .load (.n 15) (.n 7) 1, .load (.n 16) (.n 7) 2, .load (.n 17) (.n 7) 3,
    .load (.n 18) (.n 7) 4]

/-- What the kernel checks of the loop helper's body. -/
def spLChecks : Bool :=
  (chk 4 (spLPre ++ [.ret []])).isSome &&
    spLReads.all (fun a => !decide (a ∈ storesOf 4 (spLPre ++ [.ret []]))) &&
    (atomsOf spLoopA).all (fun a => isLoadB a || (!needsSide a && atomQuiet a && noHint a)) &&
    spLPre.all Stmt.straight && spLPre.all plainSB &&
    (spLPre.filterMap stmtLoad?).all (fun q => (q.1 == .n 7 && decide (q.2 < 10)) || (q.1 == .n 13 && decide (q.2 < 32))) &&
    (atomsOf spLoopA).all atomQuiet && spLoopA.all (fun s => match s with | .atom _ => true | _ => false)

set_option maxRecDepth 100000 in
theorem spL_checks : spLChecks = true := by decide +kernel

/-! ## The words -/

/-- Capacity record `j`: the capacity after `4 j` permutations. -/
def spRec (cap : List E) (j : ℕ) : List E := (pkSqueeze (4 * j) cap).2

theorem spRec_succ (cap : List E) (j : ℕ) : spRec cap (j + 1) = (pkSqueeze 4 (spRec cap j)).2 := by
  unfold spRec; rw [show 4 * (j + 1) = 4 * j + 4 by ring, pkSqueeze_add]

theorem spRec_length {cap : List E} (hcap : cap.length = 5) (j : ℕ) : (spRec cap j).length = 5 :=
  pkSqueeze_cap_length _ _ hcap

/-- Iteration `j`'s cells within the packed draw's. -/
theorem pk_cells_split {cap : List E} {p j : ℕ} (hj : 4 * (j + 1) ≤ p) {i : ℕ} (hi : i < 32) :
    (pkSqueeze p cap).1.getD (32 * j + i) 0 = (pkSqueeze 4 (spRec cap j)).1.getD i 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, p = 4 * j + (4 + m) := ⟨p - 4 * j - 4, by omega⟩
  rw [pkSqueeze_add, pkSqueeze_add 4 m, List.getD_append_right _ _ _ _ (by rw [pkSqueeze_length]; omega),
    pkSqueeze_length, show 32 * j + i - 8 * (4 * j) = i by omega,
    List.getD_append _ _ _ _ (by rw [pkSqueeze_length]; omega)]
  rfl

/-- What the loop reads and writes of its caller's: every record, and the packed draw's cells. -/
def SpLPre (cap : List E) (p q cm : ℕ) (out : E) (rd : Reader) : Prop :=
  (∀ j ≤ q, ReadsAt rd (ptrAt (cm + 5 * j)) (spRec cap j)) ∧ ReadsAt rd out (pkSqueeze p cap).1

/-- The loop's region: the cells at `out`, the records. -/
def spLR (p q cm : ℕ) (out : E) (i : ℕ) : Prop :=
  ptrRegion [(out, 8 * p)] i ∨ (cm ≤ i ∧ i < cm + 5 * (q + 2))

/-- The block of the loop's last `m` iterations and its skipped tail. -/
def spBlock (fs : String → ℕ) (m : ℕ) : ℕ := m * fs spLName + fs (tailKey spLName)

/-! ## One iteration -/

theorem slEvs_congr {σ σ' : Val} : ∀ pre : List Stmt,
    (∀ c f args, Stmt.callIf c f args ∈ pre → (σ c = 0 ↔ σ' c = 0)) → pre.flatMap (slEvs σ) = pre.flatMap (slEvs σ')
  | [], _ => rfl
  | s :: pre, h => by
    rw [List.flatMap_cons, List.flatMap_cons, slEvs_congr pre fun c f args hm => h c f args (List.mem_cons_of_mem _ hm)]
    congr 1
    cases s with
    | callIf c f args =>
      have := h c f args List.mem_cons_self
      by_cases h0 : σ c = 0
      · simp [slEvs, h0, this.mp h0]
      · have h1 : ¬σ' c = 0 := fun h' => h0 (this.mpr h')
        simp [slEvs, h0, h1]
    | _ => rfl

variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}

set_option maxHeartbeats 1000000 in
/-- **One iteration of the loop completes placed**, from its tail's completeness. -/
theorem spL_step (k : ℕ) {cap : List E} (hcap : cap.length = 5) {p q cm : ℕ} (hpq : 4 * q ≤ p) (hq : q < 16)
    {out : E} {fpm : ℕ} (hout : PtrsBelow [(out, 8 * p)] fpm) {j : ℕ} (hj : j < q) {fp c : ℕ}
    (hfc : fp + spBlock fs (q - j) ≤ c)
    (htail : j + 1 < q → ∀ fp' c', fp' + spBlock fs (q - (j + 1)) ≤ c' →
      CallAtA fs al cert k spLName [gen ^ (j + 1), gen ^ q, ptrAt cm, out] [] (spLR p q cm out) (fun _ => False)
        (fun _ => True) (SpLPre cap p q cm out) PostQuiet (spBlock fs (q - (j + 1))) fp' c' c') :
    CallAtA fs al cert k spLName [gen ^ j, gen ^ q, ptrAt cm, out] [] (spLR p q cm out) (fun _ => False)
      (fun _ => True) (SpLPre cap p q cm out) PostQuiet (spBlock fs (q - j)) fp c c := by
  have hblk : spBlock fs (q - j) = fs spLName + spBlock fs (q - (j + 1)) := by
    obtain ⟨m, hm⟩ : ∃ m, q - j = m + 1 := ⟨q - j - 1, by omega⟩
    rw [spBlock, spBlock, hm, show q - (j + 1) = m by omega, Nat.add_mul, one_mul]; ring
  rw [hblk] at hfc ⊢
  have hck := spL_checks
  simp only [spLChecks, Bool.and_eq_true] at hck
  obtain ⟨⟨⟨⟨⟨⟨⟨hc, hrd⟩, hat⟩, hst⟩, hpl⟩, hlo⟩, hqa⟩, hall⟩ := hck
  replace hrd := List.all_eq_true.mp hrd
  replace hat := List.all_eq_true.mp hat
  replace hlo := List.all_eq_true.mp hlo
  replace hqa := List.all_eq_true.mp hqa
  replace hall := List.all_eq_true.mp hall
  obtain ⟨c', hc⟩ := Option.isSome_iff_exists.mp hc
  set fn := fn% «squeeze_packed_loop0» with hfn
  set args : List E := [gen ^ j, gen ^ q, ptrAt cm, out] with hargs
  have hc' : chk args.length fn.body = some c' := by rw [spL_body]; exact hc
  obtain ⟨σ, hσ⟩ : ∃ σ : Reader → Val, ∀ rd, σ rd = fwdVal rd (fun _ => 0) args fn.body := ⟨_, fun _ => rfl⟩
  set S := storesOf args.length fn.body with hS
  have hSe : S = storesOf 4 (spLPre ++ [.ret []]) := by rw [hS, spL_body]; rfl
  have hmB : ∀ a, Stmt.atom a ∈ spLoopA → Stmt.atom a ∈ fn.body := fun a ha => by
    rw [spL_body, spLPre]; exact List.mem_append_left _ (List.mem_append_left _ ha)
  have hmH : ∀ a, Stmt.atom a ∈ spLHead → Stmt.atom a ∈ fn.body := fun a ha => hmB a (by
    rw [spLoopA_eq]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ ha)))
  have hmT : ∀ a, Stmt.atom a ∈ spLTail → Stmt.atom a ∈ fn.body := fun a ha => hmB a (by
    rw [spLoopA_eq]; exact List.mem_append_right _ ha)
  have G : ∀ rd a, Stmt.atom a ∈ fn.body → Good rd S (fun _ => 0) (σ rd) a := fun rd a ha => by
    rw [hσ]; exact fwd_good hc' a ha
  -- the values the memory does not change
  have hv : ∀ rd, σ rd (.n 0) = gen ^ j ∧ σ rd (.n 1) = gen ^ q ∧ σ rd (.n 2) = ptrAt cm ∧ σ rd (.n 3) = out ∧
      σ rd (.n 7) = ptrAt (cm + 5 * j) ∧ σ rd (.n 13) = out * gen ^ (32 * j) ∧
      σ rd (.n 78) = gen ^ (j + 1) + gen ^ q ∧ σ rd (.n 80) = gen ^ (j + 1) := by
    intro rd
    have p0 : σ rd (.n 0) = gen ^ j := by rw [hσ]; exact fwd_param hc' (by simp [hargs])
    have p1 : σ rd (.n 1) = gen ^ q := by rw [hσ]; exact fwd_param hc' (by simp [hargs])
    have p2 : σ rd (.n 2) = ptrAt cm := by rw [hσ]; exact fwd_param hc' (by simp [hargs])
    have p3 : σ rd (.n 3) = out := by rw [hσ]; exact fwd_param hc' (by simp [hargs])
    have gm : ∀ d x y : ℕ, Stmt.atom (.mul (.n d) (.n x) (.n y)) ∈ fn.body → x < d → y < d →
        σ rd (.n d) = σ rd (.n x) * σ rd (.n y) := fun d x y hm hx hy => good_mul_eq (G rd _ hm) hx hy
    have m4 := gm 4 0 0 (hmH _ (by simp [spLHead])) (by norm_num) (by norm_num)
    have m5 := gm 5 4 4 (hmH _ (by simp [spLHead])) (by norm_num) (by norm_num)
    have m6 := gm 6 5 0 (hmH _ (by simp [spLHead])) (by norm_num) (by norm_num)
    have m7 := gm 7 2 6 (hmH _ (by simp [spLHead])) (by norm_num) (by norm_num)
    have m8 := gm 8 0 0 (hmH _ (by simp [spLHead])) (by norm_num) (by norm_num)
    have m9 := gm 9 8 8 (hmH _ (by simp [spLHead])) (by norm_num) (by norm_num)
    have m10 := gm 10 9 9 (hmH _ (by simp [spLHead])) (by norm_num) (by norm_num)
    have m11 := gm 11 10 10 (hmH _ (by simp [spLHead])) (by norm_num) (by norm_num)
    have m12 := gm 12 11 11 (hmH _ (by simp [spLHead])) (by norm_num) (by norm_num)
    have m13 := gm 13 3 12 (hmH _ (by simp [spLHead])) (by norm_num) (by norm_num)
    have c76 : σ rd (.n 76) = word 2 0 := G rd (.const (.n 76) (word 2 0)) (hmT _ (by simp [spLTail]))
    have m77 := gm 77 0 76 (hmT _ (by simp [spLTail])) (by norm_num) (by norm_num)
    have a78 : σ rd (.n 78) = σ rd (.n 77) + σ rd (.n 1) :=
      G rd (.add (.n 78) (.n 77) (.n 1)) (hmT _ (by simp [spLTail]))
    have c79 : σ rd (.n 79) = word 2 0 := G rd (.const (.n 79) (word 2 0)) (hmT _ (by simp [spLTail]))
    have m80 := gm 80 0 79 (hmT _ (by simp [spLTail])) (by norm_num) (by norm_num)
    refine ⟨p0, p1, p2, p3, ?_, ?_, ?_, ?_⟩
    · rw [m7, m6, m5, m4, p2, p0, ← ptrAt_mul_gen_pow']; ring
    · rw [m13, m12, m11, m10, m9, m8, p3, p0]; ring
    · rw [a78, m77, c76, p0, p1, word_gen, gen_pow_mul_gen]
    · rw [m80, c79, p0, word_gen, gen_pow_mul_gen]
  obtain ⟨σ0, hσ0⟩ : ∃ σ0, σ0 = σ (fun _ => none) := ⟨_, rfl⟩
  have hv0 := hv (fun _ => none)
  rw [← hσ0] at hv0
  have h78 : σ0 (.n 78) = gen ^ (j + 1) + gen ^ q := hv0.2.2.2.2.2.2.1
  set es := spLPre.flatMap (slEvs σ0) with hes
  have hesr : ∀ rd, spLPre.flatMap (slEvs (σ rd)) = es := fun rd => by
    refine slEvs_congr _ fun c f args hm => ?_
    simp only [spLPre, List.mem_append, List.mem_singleton, Stmt.callIf.injEq] at hm
    rcases hm with hm | ⟨rfl, -, -⟩
    · exact absurd (hall _ hm) (by simp)
    · rw [(hv rd).2.2.2.2.2.2.1, h78]
  have hw : ∀ rd, walk (σ rd) fn.body = .ret es [] := fun rd => by
    rw [spL_body, walk_straight _ _ _ hst, hesr]
  obtain ⟨hd0, ha0, hr0, hh0⟩ : allocDsts es = [] ∧ allocs σ0 es = [] ∧ addrs es = [] ∧ heapHintAddrs σ0 es = [] :=
    plainSB_parts hst hpl
  have hcalls : calls es = [⟨spLName, [.n 80, .n 1, .n 2, .n 3], [], decide (σ0 (.n 78) ≠ 0)⟩] := by
    rw [hes, (straight_parts σ0 spLPre hst).2.2.2]
    have : spLoopA.filterMap Stmt.callS = [] := List.filterMap_eq_nil_iff.mpr fun s hs => by
      have := hall s hs
      split at this <;> simp_all [Stmt.callS]
    simp [spLPre, List.filterMap_append, this, Stmt.callS, mkCall]
  have hargs1 : [V.n 80, .n 1, .n 2, .n 3].map σ0 = [gen ^ (j + 1), gen ^ q, ptrAt cm, out] := by
    have h1 : σ0 (.n 1) = gen ^ q := hv0.2.1
    have h2 : σ0 (.n 2) = ptrAt cm := hv0.2.2.1
    have h3 : σ0 (.n 3) = out := hv0.2.2.2.1
    have h80 : σ0 (.n 80) = gen ^ (j + 1) := hv0.2.2.2.2.2.2.2
    simp only [List.map_cons, List.map_nil, h1, h2, h3, h80]
  have htk : decide (σ0 (.n 78) ≠ 0) = decide (j + 1 ≠ q) := by
    rw [h78]
    refine decide_eq_decide.mpr ⟨fun h he => h (by rw [he]; exact e_add_eq_zero_iff.mpr rfl), fun h he => h ?_⟩
    exact gen_pow_inj (by omega) (by omega) (e_add_eq_zero_iff.mp he)
  refine callAtA_nodeLRd spL_loop hfc ⟨σ0, fn, es, [], [], [PostQuiet], fun _ => True, fun _ => False, find_spL,
    ⟨by simp, List.Pairwise.nil⟩, fun _ h => h.elim, ?_, fun _ _ => trivial, ?_⟩
  · -- the tail call
    rw [hcalls, ha0, htk, KidsAtL]
    by_cases hlt : j + 1 < q
    · have ht : decide (j + 1 ≠ q) = true := decide_eq_true (by omega)
      simp only [ht, ↓reduceIte]
      refine ⟨spLR p q cm out, fun _ => False, fun _ => True, fun i hi => Or.inl (Or.inl hi), ?_, fun _ _ _ => trivial,
        fun _ h => h.elim⟩
      rw [hargs1]
      exact (htail hlt (fp + fs spLName) c (by omega)).mono (fun _ h => h) (fun _ h => h) (fun _ _ => trivial)
        (fun _ h => h.1) (fun _ _ _ h => h)
    · have ht : decide (j + 1 ≠ q) = false := decide_eq_false (by omega)
      simp only [ht, Bool.false_eq_true, ↓reduceIte]
      refine ⟨⟨fun v => ([V.n 80, .n 1, .n 2, .n 3].map σ0).getD v.idx 0, fn, find_spL, by rw [spL_params]; rfl⟩,
        ?_, by simp, fun _ _ => trivial, fun _ h => h.elim⟩
      rw [spBlock, show q - (j + 1) = 0 by omega]; simp
  · -- each memory
    intro rd _ ⟨hrec, hout'⟩ _
    obtain ⟨p0, p1, p2, p3, p7, p13, p78, p80⟩ := hv rd
    obtain ⟨-, ha, -, -⟩ := plainSB_parts (σ := σ rd) hst hpl
    rw [hesr rd] at ha
    have hrj := hrec j hj.le
    have hrj1 := hrec (j + 1) (by omega)
    -- the record's reads
    have hreads : ∀ i < 5, σ rd (.n (14 + i)) = (spRec cap j).getD i 0 ∧
        (Atom.load (.n (14 + i)) (.n 7) i).Holds rd (σ rd) := by
      intro i hi
      have hm : Stmt.atom (.load (.n (14 + i)) (.n 7) i) ∈ fn.body := hmH _ (by interval_cases i <;> simp [spLHead])
      have hS' : Atom.load (.n (14 + i)) (.n 7) i ∉ S := fun h => by
        have hm' : Atom.load (.n (14 + i)) (.n 7) i ∈ spLReads := by interval_cases i <;> simp [spLReads]
        have := hrd _ hm'
        simp only [Bool.not_eq_true', decide_eq_false_iff_not] at this
        exact this (by rw [hSe] at h; exact h)
      have hx : LoadHolds rd (σ rd (.n 7)) i ((spRec cap j).getD i 0) := by
        rw [p7]; exact readsAt_getD hrj (by rw [spRec_length hcap]; exact hi)
      exact ⟨good_load_eq hx (G rd _ hm) hS', holds_load_of_good (G rd _ hm) hS' hx⟩
    have hcapv : [14, 15, 16, 17, 18].map (σ rd ∘ .n) = spRec cap j := by
      have e := fun i (hi : i < 5) => (hreads i hi).1
      obtain ⟨c0, c1, c2, c3, c4, he⟩ : ∃ c0 c1 c2 c3 c4, spRec cap j = [c0, c1, c2, c3, c4] := by
        have hl := spRec_length hcap j
        match spRec cap j, hl with | [c0, c1, c2, c3, c4], _ => exact ⟨c0, c1, c2, c3, c4, rfl⟩
      rw [he] at e ⊢
      have e0 := e 0 (by norm_num); have e1 := e 1 (by norm_num); have e2 := e 2 (by norm_num)
      have e3 := e 3 (by norm_num); have e4 := e 4 (by norm_num)
      simp only [Nat.add_zero, List.getD_cons_zero, List.getD_cons_succ] at e0 e1 e2 e3 e4
      simp [e0, e1, e2, e3, e4]
    have hmP : ∀ a, Stmt.atom a ∈ spPermsT 24 [14, 15, 16, 17, 18] 20 13 0 4 → Stmt.atom a ∈ fn.body :=
      fun a ha => hmB a (by
        rw [spLoopA_eq]
        exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ha)))
    have hz : ∀ i < 4, σ rd (.n (20 + i)) = 0 := fun i hi => by
      have := G rd (.const (.n (20 + i)) (word 0 0)) (hmH _ (by interval_cases i <;> simp [spLHead]))
      rw [this, word_zero]
    obtain ⟨hfc', hfo⟩ := spPerms_fwd (rd := rd) (o := 24) (cap := [14, 15, 16, 17, 18]) hz 4
      fun j' hj' => holds_of_good' (G rd _ (hmP _ (spKec_mem hj'))) rfl
    rw [hcapv] at hfc' hfo
    -- every atom of the iteration
    have hA : ∀ a, Stmt.atom a ∈ spLoopA → a.Holds rd (σ rd) := by
      intro a ha
      have hab := hmB a ha
      cases hlb : isLoadB a
      · have := hat a (mem_atomsOf' ha)
        simp only [hlb, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true'] at this
        exact holds_of_good' (G rd a hab) this.1.1
      rw [spLoopA_eq] at ha
      simp only [List.mem_append] at ha
      rcases ha with ((ha | ha) | ha) | ha
      · simp only [spLHead, List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
        rcases ha with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
          subst h <;> simp [isLoadB] at hlb
        exacts [(hreads 0 (by norm_num)).2, (hreads 1 (by norm_num)).2, (hreads 2 (by norm_num)).2,
          (hreads 3 (by norm_num)).2, (hreads 4 (by norm_num)).2]
      · obtain ⟨j', hj', rfl | ⟨i, hi, rfl⟩⟩ := mem_spPermsT ha
        · simp [spKec, isLoadB] at hlb
        · show LoadHolds rd (σ rd (.n 13)) (0 + 8 * j' + i) (σ rd (.n (24 + 13 * j' + i)))
          rw [p13, hfo j' hj' i hi, loadHolds_mul_gen_pow, Nat.zero_add,
            ← pk_cells_split (p := p) (by omega) (by omega)]
          exact readsAt_getD hout' (by rw [pkSqueeze_length]; omega)
      · obtain ⟨i, hi, he⟩ := List.mem_map.mp ha
        obtain rfl := Stmt.atom.inj he.symm
        have hi' := List.mem_range.mp hi
        show LoadHolds rd (σ rd (.n 7)) (5 + i) (σ rd (.n (71 + i)))
        have e := congrArg (fun l => l.getD i 0) hfc'
        simp only [spCap, Nat.reduceEqDiff, ↓reduceIte, List.map_map, Function.comp_def] at e
        rw [List.getD_eq_getElem _ _ (by simp; omega)] at e
        simp only [List.getElem_map, List.getElem_range, show 24 + 13 * (4 - 1) + 8 + i = 71 + i by omega] at e
        rw [p7, e, ← loadHolds_mul_gen_pow, ptrAt_mul_gen_pow', ← spRec_succ,
          show cm + 5 * j + 5 = cm + 5 * (j + 1) by ring]
        exact readsAt_getD hrj1 (by rw [spRec_length hcap]; exact hi')
      · simp only [spLTail, List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
        rcases ha with h | h | h | h | h <;> subst h <;> simp [isLoadB] at hlb
    refine ⟨σ rd, by rw [spL_params]; simp [p0, p1, p2, p3, hargs], hw rd, rfl, by rw [ha, ha0], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [ha0]
      exact ⟨by rw [hd0]; rfl, by rw [hr0]; simp⟩
    · rw [hcalls]
      intro cl hcl
      simp only [List.mem_singleton] at hcl
      subst hcl
      obtain ⟨-, h1, h2, h3, -, -, -, h80⟩ := hv rd
      exact ⟨by rw [hargs1]; simp only [List.map_cons, List.map_nil, h1, h2, h3, h80], rfl⟩
    · intro A hA
      rw [← hesr rd, loadAddrs_straight _ _ hst] at hA
      obtain ⟨⟨x, off⟩, hq, rfl⟩ := List.mem_map.mp hA
      have := hlo _ hq
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
      rcases this with ⟨rfl, hoff⟩ | ⟨rfl, hoff⟩
      · refine ⟨cm + 5 * j + off, by rw [p7]; exact Main.addr_ofK _ _, Or.inr (Or.inl (Or.inr ⟨by omega, by omega⟩))⟩
      · obtain ⟨i, -, hi⟩ := hout (out, 8 * p) List.mem_cons_self (32 * j + off) (by omega)
        refine ⟨i, ?_, Or.inr (Or.inl (Or.inl ⟨_, List.mem_cons_self, 32 * j + off, by omega, hi⟩))⟩
        rw [p13, ← hi, gen_pow_eq_ofK, limb0_mul_ofK, mul_assoc, addressOfIndex, addressOfIndex, addressOfIndex,
          ← pow_add]
    · intro A hA
      rw [← hesr rd, (plainSB_parts (σ := σ rd) hst hpl).2.2.2] at hA
      simp at hA
    · intro ev hev
      rw [← hesr rd] at hev
      obtain ⟨s, hs, hev⟩ := List.mem_flatMap.mp hev
      simp only [spLPre, List.mem_append, List.mem_singleton] at hs
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
        · show IsInK (σ rd (.n 78)); rw [p78]; exact isInK_add (gen_pow_isInK _) (gen_pow_isInK _)
        · split <;> trivial
    · intro ts hv' hp'
      refine postQuiet_node find_spL (hw rd) (fun a ha' => ?_) (fun ev hev => ?_) hv' ?_ _
      · rw [← hesr rd] at ha'
        obtain ⟨s, hs, hev⟩ := List.mem_flatMap.mp ha'
        simp only [spLPre, List.mem_append, List.mem_singleton] at hs
        rcases hs with hs | rfl
        · obtain ⟨b, rfl⟩ : ∃ b, s = .atom b := by
            have := hall s hs
            split at this
            · exact ⟨_, rfl⟩
            · simp at this
          simp only [slEvs, List.mem_singleton, Ev.atom.injEq] at hev
          subst hev
          exact hqa a (mem_atomsOf' hs)
        · simp only [slEvs, List.mem_cons, List.not_mem_nil, or_false] at hev
          rcases hev with h | h
          · cases h
          · split at h <;> cases h
      · rw [← hesr rd] at hev
        obtain ⟨s, hs, hev⟩ := List.mem_flatMap.mp hev
        simp only [spLPre, List.mem_append, List.mem_singleton] at hs
        rcases hs with hs | rfl
        · obtain ⟨b, rfl⟩ : ∃ b, s = .atom b := by
            have := hall s hs
            split at this
            · exact ⟨_, rfl⟩
            · simp at this
          simp only [slEvs, List.mem_singleton] at hev
          subst hev
          have := hat b (mem_atomsOf' hs)
          cases b with
          | hint hh => simp [isLoadB, noHint] at this
          | _ => trivial
        · simp only [slEvs, List.mem_cons, List.not_mem_nil, or_false] at hev
          rcases hev with rfl | rfl
          · trivial
          · split <;> trivial
      · rw [hcalls] at hp' ⊢; exact hp'

/-- **The loop completes placed from iteration `j`**, at any frame past its block. -/
theorem spL_callAtA (k : ℕ) {cap : List E} (hcap : cap.length = 5) {p q cm : ℕ} (hpq : 4 * q ≤ p) (hq : q < 16)
    {out : E} {fpm : ℕ} (hout : PtrsBelow [(out, 8 * p)] fpm) :
    ∀ j < q, ∀ fp c, fp + spBlock fs (q - j) ≤ c →
      CallAtA fs al cert k spLName [gen ^ j, gen ^ q, ptrAt cm, out] [] (spLR p q cm out) (fun _ => False)
        (fun _ => True) (SpLPre cap p q cm out) PostQuiet (spBlock fs (q - j)) fp c c := by
  have key : ∀ t j, j + 1 + t = q → ∀ fp c, fp + spBlock fs (q - j) ≤ c →
      CallAtA fs al cert k spLName [gen ^ j, gen ^ q, ptrAt cm, out] [] (spLR p q cm out) (fun _ => False)
        (fun _ => True) (SpLPre cap p q cm out) PostQuiet (spBlock fs (q - j)) fp c c := by
    intro t
    induction t with
    | zero => intro j hj fp c hfc; exact spL_step k hcap hpq hq hout (by omega) hfc fun h' => absurd h' (by omega)
    | succ t ih => intro j hj fp c hfc; exact spL_step k hcap hpq hq hout (by omega) hfc fun _ => ih (j + 1) (by omega)
  intro j hj
  exact key (q - j - 1) j (by omega)

end
end LeanVM.Guest.B1.VsC
