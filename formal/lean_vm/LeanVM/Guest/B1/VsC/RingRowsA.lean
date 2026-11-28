/-
  LeanVM.Guest.B1.VsC.RingRowsA

  `ring_rows` completes placed: the rows are its caller's words.
-/

module

public import LeanVM.Guest.B1.VsC.RingRowsLoopA
public import LeanVM.Guest.B1.VsC.RsRunA
public import LeanVM.ToMathlib.List
import LeanVM.Guest.CoreRef
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«ring_rows»

/-!
# `ring_rows`, placed

`ring_rows(chain, zs, ps, c_table, g^count)`, `count < 64`, placed at frame `fp`, its cursor `c`
right after: row `0` copied from the table, the count split `count = 8 q + r` from six hinted bits,
the loop over the `q` full chunks (`rrg_placed`, entered when `q ≠ 0`), the remainder's
`rs_eq_rows_all__L{r}` (`rs_eq_rows_all_placed'`) at the aligned bases from `c`. It has no words of
its own: rows `0 ..= count` of `chain` (`rgRows`, row `m` the table times the products over the
first `m` coordinates) are its caller's, which its callees' stores find there (`rg_chunk`). One
valuation fixed before the memory (`rgVal`), by `callAtA_node`.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.Value LeanVM.Protocol.Verifier LeanVM.Guest.B1.Link
open LeanVM.Prover.Exec (allocBase bitWord)

@[expose] public section

/-! ## The template -/

/-- The statements after the count's check, before the dispatch. -/
def rgTPre : List Stmt :=
  [.atom (.const (.n 107) (word 1 0)), .atom (.add (.n 108) (.n 107) (.n 102)), .atom (.const (.n 109) (word 1 0)),
    .callIf (.n 108) name% «ring_rows_loop0» [.n 109, .n 102, .n 0, .n 1, .n 2],
    .atom (.mul (.n 110) (.n 102) (.n 102)), .atom (.mul (.n 111) (.n 110) (.n 110)),
    .atom (.mul (.n 112) (.n 111) (.n 111)), .atom (.mul (.n 113) (.n 112) (.n 112)),
    .atom (.mul (.n 114) (.n 113) (.n 113)), .atom (.mul (.n 115) (.n 114) (.n 114)),
    .atom (.mul (.n 116) (.n 115) (.n 115)), .atom (.mul (.n 117) (.n 116) (.n 116)),
    .atom (.mul (.n 118) (.n 117) (.n 117)), .atom (.mul (.n 119) (.n 0) (.n 118)),
    .atom (.mul (.n 120) (.n 1) (.n 112)), .atom (.mul (.n 121) (.n 2) (.n 112))]

/-- `ring_rows`' statements before its dispatch. -/
def rgPre : List Stmt := rgInits ++ rgA ++ rgTPre

/-- The dispatch's names. -/
def rgDNames : List String :=
  ["rs_eq_rows_all__L0", "rs_eq_rows_all__L1", "rs_eq_rows_all__L2", "rs_eq_rows_all__L3",
    "rs_eq_rows_all__L4", "rs_eq_rows_all__L5", "rs_eq_rows_all__L6", "rs_eq_rows_all__L7"]

set_option maxRecDepth 100000 in
theorem rg_body' : (fn% «ring_rows»).body = rgPre ++
    .dispatch (.n 88) rgDNames [.n 119, .n 120, .n 121] [.n 122] :: ([] ++ [.ret []]) :=
  stmtsEqb_sound (by decide +kernel)

theorem rg_not_loop : coreProgram.loop "ring_rows" = false := by decide +kernel

theorem rg_params : (fn% «ring_rows»).params = [.n 0, .n 1, .n 2, .n 3, .n 4] := rfl

theorem rgPre_straight : rgPre.all Stmt.straight = true := by decide

set_option maxRecDepth 100000 in
theorem rgPre_allocSz : rgPre.filterMap Stmt.allocSz = [] := by decide

set_option maxRecDepth 100000 in
theorem rgPre_addrS : rgPre.filterMap Stmt.addrS = [] := by decide

set_option maxRecDepth 100000 in
theorem rgPre_callS : rgPre.filterMap Stmt.callS =
    [(some (.n 108), name% «ring_rows_loop0», [.n 109, .n 102, .n 0, .n 1, .n 2], [])] := by decide

set_option maxRecDepth 100000 in
theorem rgPre_loads : rgPre.filterMap Stmt.loadS = (List.range 64).flatMap fun k => [(.n 3, k), (.n 0, k)] := by
  decide

set_option maxRecDepth 100000 in
theorem rgPre_quiet : rgPre.all stmtQuietB = true := by decide

set_option maxRecDepth 100000 in
theorem rgPre_noHeap : rgPre.all noHeapHintB = true := by decide

/-- The count's bits' hint. -/
def rgHint : Stmt := .atom (.hint (.bitsExp (.n 4) 6 (.stack [.n 69, .n 70, .n 71, .n 72, .n 73, .n 74])))

set_option maxRecDepth 100000 in
theorem rgPre_noComputed : rgPre.all (fun s => stmtsEqb [s] [rgHint] || noComputedB s) = true := by decide

theorem rgDNames_get {r : ℕ} (hr : r < 8) : rgDNames[r]! = rsEqRowsAllNames.getD r "" := by
  interval_cases r <;> rfl

/-! ## The valuation and the rows -/

/-- `ring_rows`' values after the table's words. -/
def rgValsB (chain z p : E) (count : ℕ) : List E :=
  let b : ℕ → E := fun i => bitWord (count.testBit i)
  let v78 := word 1 0 + b 0 * word 3 0
  let v82 := word 1 0 + b 1 * word 5 0
  let v83 := v78 * v82
  let v87 := word 1 0 + b 2 * word 17 0
  let v88 := v83 * v87
  let v92 := word 1 0 + b 3 * word 3 0
  let v96 := word 1 0 + b 4 * word 5 0
  let v97 := v92 * v96
  let v101 := word 1 0 + b 5 * word 17 0
  let v102 := v97 * v101
  let v103 := v102 * v102
  let v104 := v103 * v103
  let v105 := v104 * v104
  let v110 := v102 * v102
  let v111 := v110 * v110
  let v112 := v111 * v111
  let v113 := v112 * v112
  let v114 := v113 * v113
  let v115 := v114 * v114
  let v116 := v115 * v115
  let v117 := v116 * v116
  let v118 := v117 * v117
  [b 0, b 1, b 2, b 3, b 4, b 5,
    word 1 0, word 3 0, b 0 * word 3 0, v78,
    word 1 0, word 5 0, b 1 * word 5 0, v82, v83,
    word 1 0, word 17 0, b 2 * word 17 0, v87, v88,
    word 1 0, word 3 0, b 3 * word 3 0, v92,
    word 1 0, word 5 0, b 4 * word 5 0, v96, v97,
    word 1 0, word 17 0, b 5 * word 17 0, v101, v102,
    v103, v104, v105, v105 * v88,
    word 1 0, word 1 0 + v102, word 1 0,
    v110, v111, v112, v113, v114, v115, v116, v117, v118,
    chain * v118, z * v112, p * v112, 0]

/-- `ring_rows`' valuation: value `i`. -/
def rgVal (chain z p ct : E) (cs : List E) (count : ℕ) (i : ℕ) : E :=
  if i < 5 then [chain, z, p, ct, gen ^ count].getD i 0 else if i < 69 then cs.getD (i - 5) 0
  else (rgValsB chain z p count).getD (i - 69) 0

/-- Row `m`'s word `k`: the table's times the products over the first `m` coordinates. -/
def rgRow (cs zs ps : List E) (m k : ℕ) : E := ringRow (cs.getD k 0) (zs.take m) (ps.take m) k

/-- Rows `0 ..= count` of `64`. -/
def rgRows (cs zs ps : List E) (count : ℕ) : List E :=
  (List.range (64 * (count + 1))).map fun o => rgRow cs zs ps (o / 64) (o % 64)

theorem rgRows_at {rd : Reader} {chain : E} {cs zs ps : List E} {count : ℕ}
    (h : ReadsAt rd chain (rgRows cs zs ps count)) {m : ℕ} (hm : m ≤ count) {k : ℕ} (hk : k < 64) :
    LoadHolds rd chain (64 * m + k) (rgRow cs zs ps m k) := by
  have := h (64 * m + k) (by simp [rgRows]; nlinarith)
  simp only [rgRows, List.getElem_map, List.getElem_range] at this
  rwa [show (64 * m + k) / 64 = m by omega, show (64 * m + k) % 64 = k by omega] at this

/-- **A chunk's leaf words from the rows**: coordinates `8 t ..< 8 t + n`, rows `8 t ..= 8 t + n`. -/
theorem rg_chunk {rd : Reader} {chain z p : E} {cs zs ps : List E} {count : ℕ} (lz : zs.length = count)
    (lp : ps.length = count) (hz : ReadsAt rd z zs) (hp : ReadsAt rd p ps)
    (hrows : ∀ m ≤ count, ∀ k < 64, LoadHolds rd chain (64 * m + k) (rgRow cs zs ps m k)) {t n : ℕ}
    (htn : 8 * t + n ≤ count) :
    RraPre (chain * gen ^ (64 * (8 * t))) (z * gen ^ (8 * t)) (p * gen ^ (8 * t)) ((zs.drop (8 * t)).take n)
      ((ps.drop (8 * t)).take n) ((List.range 64).map (rgRow cs zs ps (8 * t))) n rd := by
  refine ⟨?_, ?_, ?_, fun i hi k hk => ?_⟩
  · refine readsAt_mul_gen_pow.mpr fun i hi => ?_
    simp only [List.length_take, List.length_drop] at hi
    have := readsAt_getD hz (i := 8 * t + i) (by omega)
    rwa [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
      ← List.getD_eq_getElem?_getD]
  · refine readsAt_mul_gen_pow.mpr fun i hi => ?_
    simp only [List.length_take, List.length_drop] at hi
    have := readsAt_getD hp (i := 8 * t + i) (by omega)
    rwa [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
      ← List.getD_eq_getElem?_getD]
  · refine readsAt_mul_gen_pow.mpr fun k hk => ?_
    simp only [List.length_map, List.length_range] at hk
    rw [List.getD_map_range _ hk]
    exact hrows (8 * t) (by omega) k hk
  · rw [loadHolds_mul_gen_pow, List.getD_map_range _ hk,
      show 64 * (8 * t) + (64 * (i + 1) + k) = 64 * (8 * t + (i + 1)) + k by ring]
    have := hrows (8 * t + (i + 1)) (by omega) k hk
    rw [rgRow, List.take_add (l := zs) (i := 8 * t) (j := i + 1), List.take_add (l := ps) (i := 8 * t) (j := i + 1)] at this
    rw [rgRow, List.take_take, List.take_take]
    simp only [show min (i + 1) n = i + 1 by omega]
    rw [← ringRow_append _ _ _ _ _ _ (by simp [lz, lp])]
    exact this

/-! ## Placed -/

variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}

/-- `ring_rows`' end from its cursor `c`: the loop at the aligned base, the remainder's leaf at the
aligned base past it. -/
def rgEnd (fs : String → ℕ) (al : String → Bool) (count c : ℕ) : ℕ :=
  let c2 := llEnd fs al "rs_eq_rows_all__L8" (count / 8) 0
    (allocBase (al name% «ring_rows_loop0») c + llBlk fs name% «ring_rows_loop0» (count / 8) 0)
  allocBase (al (rsEqRowsAllNames.getD (count % 8) "")) c2 + fs (rsEqRowsAllNames.getD (count % 8) "")

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- **`ring_rows` completes placed**, `count < 64`, its rows its caller's words. -/
theorem ring_rows_placed (k : ℕ) {count : ℕ} (hcount : count < 64) {chain z p ct : E} {zs ps cs : List E}
    (lz : zs.length = count) (lp : ps.length = count) (lc : cs.length = 64) {R : ℕ → Prop}
    (hRc : PtrCells R chain (64 * (count + 1))) (hRz : PtrCells R z count) (hRp : PtrCells R p count)
    (hRt : PtrCells R ct 64) (fp c : ℕ) (hfc : fp + fs "ring_rows" ≤ c) :
    CallAtA fs al cert k "ring_rows" [chain, z, p, ct, gen ^ count] [] R (fun _ => False) (fun _ => True)
      (fun rd => ReadsAt rd ct cs ∧ ReadsAt rd z zs ∧ ReadsAt rd p ps ∧ ReadsAt rd chain (rgRows cs zs ps count))
      PostQuiet (fs "ring_rows") fp c (rgEnd fs al count c) := by
  set q := count / 8 with hq
  set r := count % 8 with hr
  have hpqr : count = 8 * q + r := by omega
  have hq8 : q < 8 := by omega
  have hr8 : r < 8 := by omega
  obtain ⟨hb1, hb2⟩ := bits64' count hcount
  set σ : Val := fun v => rgVal chain z p ct cs count v.idx with hσ
  have w3 : word 3 0 = gen ^ 1 + 1 := word_two_pow_xor_one (a := 1) (by norm_num)
  have w5 : word 5 0 = gen ^ 2 + 1 := word_two_pow_xor_one (a := 2) (by norm_num)
  have w17 : word 17 0 = gen ^ 4 + 1 := word_two_pow_xor_one (a := 4) (by norm_num)
  have h88 : σ (.n 88) = gen ^ r := by
    show (word 1 0 + bitWord (count.testBit 0) * word 3 0) * (word 1 0 + bitWord (count.testBit 1) * word 5 0) *
      (word 1 0 + bitWord (count.testBit 2) * word 17 0) = _
    rw [w3, w5, w17, bitf, bitf, bitf, ← pow_add, ← pow_add]; congr 1; omega
  have h102 : σ (.n 102) = gen ^ q := by
    show (word 1 0 + bitWord (count.testBit 3) * word 3 0) * (word 1 0 + bitWord (count.testBit 4) * word 5 0) *
      (word 1 0 + bitWord (count.testBit 5) * word 17 0) = _
    rw [w3, w5, w17, bitf, bitf, bitf, ← pow_add, ← pow_add]; congr 1; omega
  have e106 : σ (.n 106) = σ (.n 102) * σ (.n 102) * (σ (.n 102) * σ (.n 102)) * (σ (.n 102) * σ (.n 102) *
      (σ (.n 102) * σ (.n 102))) * σ (.n 88) := rfl
  have hassert : σ (.n 106) + σ (.n 4) = 0 := by
    rw [e106, h102, h88, show σ (.n 4) = gen ^ count from rfl, hpqr]
    rw [show gen ^ q * gen ^ q * (gen ^ q * gen ^ q) * (gen ^ q * gen ^ q * (gen ^ q * gen ^ q)) * gen ^ r =
      gen ^ (8 * q + r) by ring]
    exact add_self_E _
  have h108 : σ (.n 108) = word 1 0 + σ (.n 102) := rfl
  have e112 : σ (.n 112) = (fun x : E => x * x)^[3] (σ (.n 102)) := rfl
  have h112 : σ (.n 112) = gen ^ (8 * q) := by
    rw [e112, h102]; simp only [Function.iterate_succ, Function.comp, Function.iterate_zero, id]; ring
  have e118 : σ (.n 118) = (fun x : E => x * x)^[9] (σ (.n 102)) := rfl
  have h118 : σ (.n 118) = gen ^ (64 * (8 * q)) := by
    rw [e118, h102]; simp only [Function.iterate_succ, Function.comp, Function.iterate_zero, id]; ring
  have h119 : σ (.n 119) = chain * gen ^ (64 * (8 * q)) := by
    rw [show σ (.n 119) = chain * σ (.n 118) from rfl, h118]
  have h120 : σ (.n 120) = z * gen ^ (8 * q) := by rw [show σ (.n 120) = z * σ (.n 112) from rfl, h112]
  have h121 : σ (.n 121) = p * gen ^ (8 * q) := by rw [show σ (.n 121) = p * σ (.n 112) from rfl, h112]
  have h122 : σ (.n 122) = 0 := rfl
  have hcsv : ∀ j < 64, σ (.n (5 + j)) = cs.getD j 0 := by
    intro j hj
    show rgVal chain z p ct cs count (5 + j) = _
    unfold rgVal
    simp only [show ¬(5 + j < 5) by omega, show 5 + j < 69 by omega, ↓reduceIte, Nat.add_sub_cancel_left]
  -- the path
  set es := rgPre.flatMap (slEvs σ) ++ .call rgDNames[r]! [.n 119, .n 120, .n 121] [.n 122] ::
    ([] : List Stmt).flatMap (slEvs σ) with hes
  have hw : walk σ (fn% «ring_rows»).body = .ret es [] := by
    rw [rg_body']
    exact walk_dispatch σ rgPre _ rgPre_straight rfl (.n 88) rgDNames _ _ _ (i := r)
      (by simp [rgDNames]; omega) (by simp [rgDNames]) (by rw [h88, gen_pow_eq_ofK])
  have hpre := straight_parts σ rgPre rgPre_straight
  have hallocs : allocs σ es = [] := by
    rw [hes, allocs_append, hpre.2.1, rgPre_allocSz]; rfl
  have hdsts : allocDsts es = [] := by
    rw [hes, allocDsts_append, hpre.1, rgPre_allocSz]; rfl
  have haddrs : addrs es = [] := by
    rw [hes, addrs_append, hpre.2.2.1, rgPre_addrS]; rfl
  have hcalls : calls es = [⟨name% «ring_rows_loop0», [.n 109, .n 102, .n 0, .n 1, .n 2], [],
      decide (σ (.n 108) ≠ 0)⟩, ⟨rgDNames[r]!, [.n 119, .n 120, .n 121], [.n 122], true⟩] := by
    rw [hes, calls_append, hpre.2.2.2, rgPre_callS]; rfl
  have htk : decide (σ (.n 108) ≠ 0) = decide (q ≠ 0) := by
    rw [h108, h102, word_one]
    refine decide_eq_decide.mpr ⟨fun h he => h (by rw [he, pow_zero]; exact add_self_E _), fun h he => h ?_⟩
    have := e_add_eq_zero_iff.mp he
    rw [← pow_zero gen] at this
    exact (gen_pow_inj (by omega) (by omega) this).symm
  rw [rgDNames_get hr8] at hcalls hes
  have hrows : ∀ rd, ReadsAt rd chain (rgRows cs zs ps count) →
      ∀ m ≤ count, ∀ j < 64, LoadHolds rd chain (64 * m + j) (rgRow cs zs ps m j) :=
    fun rd h m hm j hj => rgRows_at h hm hj
  -- the leaf
  have hleafA := rs_eq_rows_all_placed' (fs := fs) (al := al) (cert := cert) (k := k) r hr8.le
    (row := σ (.n 119)) (z := σ (.n 120)) (p := σ (.n 121)) (zs := (zs.drop (8 * q)).take r)
    (ps := (ps.drop (8 * q)).take r) (c := (List.range 64).map (rgRow cs zs ps (8 * q)))
    (by simp [lz]; omega) (by simp [lp]; omega) (by simp) (R := R)
    ⟨by rw [h119]; exact ptrCells_shift hRc (by omega),
      by rw [h120]; exact ptrCells_shift hRz (by omega), by rw [h121]; exact ptrCells_shift hRp (by omega)⟩
  have hlast : ∀ rd, ReadsAt rd z zs → ReadsAt rd p ps → ReadsAt rd chain (rgRows cs zs ps count) →
      RraPre (σ (.n 119)) (σ (.n 120)) (σ (.n 121)) ((zs.drop (8 * q)).take r) ((ps.drop (8 * q)).take r)
        ((List.range 64).map (rgRow cs zs ps (8 * q))) r rd := by
    intro rd hz hp hc
    rw [h119, h120, h121]
    exact rg_chunk lz lp hz hp (hrows rd hc) (by omega)
  have hRkk : ∀ i, R i → (R i ∨ ownData cert fp c "ring_rows" [] es i) ∨ False := fun i h => Or.inl (Or.inl h)
  set c1 := allocBase (al name% «ring_rows_loop0») c with hc1
  set c2 := llEnd fs al "rs_eq_rows_all__L8" q 0 (c1 + llBlk fs name% «ring_rows_loop0» q 0) with hc2
  have hend : rgEnd fs al count c = allocBase (al (rsEqRowsAllNames.getD r "")) c2 + fs (rsEqRowsAllNames.getD r "") :=
    rfl
  rw [hend]
  refine callAtA_node rg_not_loop hfc
    ⟨σ, fn% «ring_rows», es, [], [], [PostQuiet, PostQuiet],
      fun _ => True, fun _ => False, find_ring_rows, by rw [rg_params]; rfl, hw, rfl,
      ?_, ?_, ?_, ?_, fun i hi => hi.elim, ?_, fun _ _ => trivial, ?_, ?_⟩
  · rw [hallocs]
    exact ⟨by rw [hdsts]; simp [bases], by rw [haddrs]; simp⟩
  · rw [hallocs]; exact ⟨by simp, List.Pairwise.nil⟩
  · -- the loads
    intro A hA
    rw [hallocs]
    have hnil : loadAddrs σ (Ev.call (rsEqRowsAllNames.getD r "") [.n 119, .n 120, .n 121] [.n 122] ::
        ([] : List Stmt).flatMap (slEvs σ)) = [] := rfl
    rw [hes, loadAddrs_append, loadAddrs_straight _ _ rgPre_straight, rgPre_loads, hnil, List.append_nil] at hA
    obtain ⟨⟨x, off⟩, hm, rfl⟩ := List.mem_map.mp hA
    obtain ⟨j, hj, hm⟩ := List.mem_flatMap.mp hm
    rw [List.mem_range] at hj
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
    have h3 : σ (.n 3) = ct := rfl
    have h0 : σ (.n 0) = chain := rfl
    rcases hm with ⟨hx, ho⟩ | ⟨hx, ho⟩ <;> subst hx <;> rw [ho]
    · obtain ⟨i, hi, hRi⟩ := hRt j hj
      exact ⟨i, by rw [h3]; exact hi, Or.inr (Or.inl hRi)⟩
    · obtain ⟨i, hi, hRi⟩ := hRc j (by omega)
      exact ⟨i, by rw [h0]; exact hi, Or.inr (Or.inl hRi)⟩
  · -- no heap hint
    intro A hA
    rw [hes, heapHintAddrs_append, heapHintAddrs_nil_of rgPre rgPre_noHeap] at hA
    simp [Ev.hintAddrs, heapHintAddrs] at hA
  · -- the callees
    rw [hcalls, hallocs, htk]
    by_cases hq0 : q = 0
    · have hd : decide (q ≠ 0) = false := decide_eq_false (by omega)
      simp only [KidsAtF, hd, Bool.false_eq_true, ↓reduceIte, List.headD_cons, List.tail_cons]
      refine ⟨⟨fun v => ([V.n 109, .n 102, .n 0, .n 1, .n 2].map σ).getD v.idx 0, fn% «ring_rows_loop0», find_loopRg,
        by rw [rrg_T.params]; rfl⟩, fs (rsEqRowsAllNames.getD r ""),
        allocBase (al (rsEqRowsAllNames.getD r "")) c2 + fs (rsEqRowsAllNames.getD r ""), R, fun _ => False,
        fun _ => True, hRkk, ?_, rfl, fun _ _ => trivial, fun _ h => h.elim⟩
      have e : allocBase (al name% «ring_rows_loop0») (c + ([] : List ℕ).sum) +
          fs (tailKey name% «ring_rows_loop0») = c2 := by
        simp only [hc2, hc1, llBlk, llEnd, hq0, List.sum_nil, Nat.add_zero, Nat.sub_self,
          zero_mul, zero_add, Function.iterate_zero, id]
      rw [e]
      exact (hleafA _ _).mono (fun _ h => h) (fun _ h => h) (fun _ _ => trivial)
        (fun rd h => hlast rd h.1.2.1 h.1.2.2.1 h.1.2.2.2) (fun _ _ _ h => h)
    · have hd : decide (q ≠ 0) = true := decide_eq_true hq0
      simp only [KidsAtF, hd, ↓reduceIte, List.headD_cons, List.tail_cons]
      have hloop := rrg_placed (fs := fs) (al := al) (cert := cert) (k := k) (q := q) (j := 0) (by omega)
        (by omega) (chain := chain) (z := z) (p := p) (Zs := fun t => (zs.drop (8 * t)).take 8)
        (Ps := fun t => (ps.drop (8 * t)).take 8) (Cs := fun t => (List.range 64).map (rgRow cs zs ps (8 * t)))
        (fun t ht => by simp [lz]; omega) (fun t ht => by simp [lp]; omega) (fun t ht => by simp) (R := R)
        (ptrCells_mono hRc (by omega)) (ptrCells_mono hRz (by omega)) (ptrCells_mono hRp (by omega)) c1
        (c1 + llBlk fs name% «ring_rows_loop0» q 0)
      have h0 : [V.n 109, .n 102, .n 0, .n 1, .n 2].map σ = [gen ^ 0, gen ^ q, chain, z, p] := by
        simp only [List.map_cons, List.map_nil, h102, pow_zero]
        rfl
      refine ⟨llBlk fs name% «ring_rows_loop0» q 0, c2, R, fun _ => False, fun _ => True,
        hRkk, ?_, fs (rsEqRowsAllNames.getD r ""),
        allocBase (al (rsEqRowsAllNames.getD r "")) c2 + fs (rsEqRowsAllNames.getD r ""),
        R, fun _ => False, fun _ => True, fun i hi => Or.inl (Or.inl hi), ?_, rfl,
        fun _ _ => trivial, fun _ h => h.elim⟩
      · rw [h0, show c + ([] : List ℕ).sum = c by simp]
        refine hloop.mono (fun _ h => h) (fun _ h => h) (fun _ _ => trivial) (fun rd h t _ ht => ?_)
          (fun _ _ _ h => h)
        have := rg_chunk (n := 8) (t := t) lz lp h.1.2.1 h.1.2.2.1 (hrows rd h.1.2.2.2) (by omega)
        simp only [← pow_mul]
        rwa [show t * 512 = 64 * (8 * t) by ring, show t * 8 = 8 * t by ring]
      · exact (hleafA _ _).mono (fun _ h => h) (fun _ h => h) (fun _ _ => trivial)
          (fun rd h => hlast rd h.1.2.1 h.1.2.2.1 h.1.2.2.2) (fun _ _ _ h => h)
  · -- the events
    intro rd _ hP _ ev hev
    rw [hes] at hev
    simp only [List.mem_append, List.mem_cons] at hev
    rcases hev with hev | rfl | hev
    · obtain ⟨s, hs, hev⟩ := List.mem_flatMap.mp hev
      have hK108 : IsInK (σ (.n 108)) := by
        rw [h108, h102, word_one, ← pow_zero gen]; exact isInK_add (gen_pow_isInK _) (gen_pow_isInK _)
      have hs' : SOkV rd σ s := by
        simp only [rgPre, List.mem_append] at hs
        rcases hs with (hs | hs) | hs
        · simp only [rgInits, List.mem_flatten, List.mem_map, List.mem_range] at hs
          obtain ⟨_, ⟨j, hj, rfl⟩, hs⟩ := hs
          simp only [rgInit, List.mem_cons, List.not_mem_nil, or_false] at hs
          rcases hs with rfl | rfl
          · show LoadHolds rd (σ (.n 3)) j (σ (.n (5 + j)))
            rw [hcsv j hj, show σ (.n 3) = ct from rfl, List.getD_eq_getElem _ _ (by omega)]
            exact hP.1 j (by omega)
          · show LoadHolds rd (σ (.n 0)) j (σ (.n (5 + j)))
            rw [hcsv j hj, show σ (.n 0) = chain from rfl]
            have := hrows rd hP.2.2.2 0 (Nat.zero_le _) j hj
            rwa [Nat.mul_zero, Nat.zero_add, rgRow, ringRow_nil] at this
        · simp only [rgA, List.mem_cons, List.not_mem_nil, or_false] at hs
          rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          exacts [trivial, bitWord_sq _, rfl, rfl, rfl, rfl, bitWord_sq _, rfl, rfl, rfl, rfl, rfl, bitWord_sq _, rfl,
            rfl, rfl, rfl, rfl, bitWord_sq _, rfl, rfl, rfl, rfl, bitWord_sq _, rfl, rfl, rfl, rfl, rfl,
            bitWord_sq _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hassert]
        · simp only [rgTPre, List.mem_cons, List.not_mem_nil, or_false] at hs
          rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          exacts [rfl, rfl, rfl, hK108, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl]
      exact events_sokV hs' hev
    · trivial
    · simp at hev
  · -- the post
    intro rd ts _ _ _ hv hp'
    refine postQuiet_node find_ring_rows hw (fun a ha => ?_) (fun ev hev => ?_) hv (by rw [hcalls] at hp' ⊢; exact hp') _
    · rw [hes] at ha
      simp only [List.mem_append, List.mem_cons, reduceCtorEq, false_or] at ha
      rcases ha with ha | ha
      · obtain ⟨s, hs, ha⟩ := List.mem_flatMap.mp ha
        exact quiet_of_slEvs (List.all_eq_true.mp rgPre_quiet s hs) ha
      · simp at ha
    · rw [hes] at hev
      simp only [List.mem_append, List.mem_cons] at hev
      rcases hev with hev | rfl | hev
      · obtain ⟨s, hs, hev⟩ := List.mem_flatMap.mp hev
        have := List.all_eq_true.mp rgPre_noComputed s hs
        simp only [Bool.or_eq_true] at this
        rcases this with hh | hnc
        · obtain rfl := List.head_eq_of_cons_eq (stmtsEqb_sound hh)
          simp only [rgHint, slEvs, List.mem_singleton] at hev
          subst hev
          exact ⟨count, by omega, by rw [show σ (.n 4) = gen ^ count from rfl, gen_pow_eq_ofK], rfl⟩
        · exact exact_of_slEvs hnc hev
      · trivial
      · simp at hev

end
end LeanVM.Guest.B1.VsC
