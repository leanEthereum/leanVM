/-
  LeanVM.Guest.B1.VsC.RsRunA

  `rs_eq_run` completes placed: its chain its own `HeapBuf`.
-/

module

public import LeanVM.Guest.B1.VsC.RsRunLoopA
public import LeanVM.Guest.B1.VsC.SqueezePackedA
public import LeanVM.Guest.B1.Eq.RsEqRun
import LeanVM.Guest.CoreRef
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«rs_eq_run»

/-!
# `rs_eq_run`, placed

`rs_eq_run(z, p1, g^count, seed)`, `count < 64`, placed at frame `fp`, its cursor `c` right after:
the count split `count = 8 q + r` from six hinted bits, its chain (`allocDyn` of `64 (q + 2)` words)
at `c`, its own words the honest rows `0 ..= ⌈count / 8⌉` (`rsWords`, row `h` the seed times the
products over the first `8 h` coordinates, `rsR`), row `0` copied from the seed, the loop over the
`q` full chunks (`rrl_placed`, entered when `q ≠ 0`) and the remainder's `rs_eq_rows__L{r}`
(`rs_eq_rows_placed`) at the aligned bases past it. One valuation fixed before the memory
(`rsVals`), by `callAtA_node`, as `squeeze_packed_completeA`. It returns the last row's pointer, whose
`64` words (`rsOut`) the caller reads.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.Value LeanVM.Protocol.Verifier LeanVM.Guest.B1.Link
open LeanVM.Prover.Exec (allocBase bitWord)

@[expose] public section

/-! ## The template -/

/-- `rs_eq_run`'s statements before its dispatch. -/
def rsPre : List Stmt := rsA ++ rsAlloc ++ rsInits ++ rsG ++ rsT0

/-- The dispatch's names. -/
def rsDNames : List String :=
  ["rs_eq_rows__L0", "rs_eq_rows__L1", "rs_eq_rows__L2", "rs_eq_rows__L3", "rs_eq_rows__L4",
    "rs_eq_rows__L5", "rs_eq_rows__L6", "rs_eq_rows__L7"]

set_option maxRecDepth 100000 in
theorem rs_body' : (fn% «rs_eq_run»).body = rsPre ++
    .dispatch (.n 23) rsDNames [.n 127, .n 128, .n 129] [.n 130] ::
      ([.atom (.copy (.n 131) (.n 130))] ++ [.ret [.n 131]]) :=
  stmtsEqb_sound (by decide +kernel)

theorem rs_not_loop : coreProgram.loop "rs_eq_run" = false := by decide +kernel

theorem rs_params : (fn% «rs_eq_run»).params = [.n 0, .n 1, .n 2, .n 3] := rfl

theorem rsPre_straight : rsPre.all Stmt.straight = true := by decide

set_option maxRecDepth 100000 in
theorem rsPre_allocSz : rsPre.filterMap Stmt.allocSz = [(.n 50, .inr (.n 49))] := by decide

set_option maxRecDepth 100000 in
theorem rsPre_addrS : rsPre.filterMap Stmt.addrS = [] := by decide

set_option maxRecDepth 100000 in
theorem rsPre_callS : rsPre.filterMap Stmt.callS =
    [(some (.n 116), name% «rs_eq_run_loop0», [.n 117, .n 37, .n 50, .n 0, .n 1], [])] := by decide

set_option maxRecDepth 100000 in
theorem rsPre_loads : rsPre.filterMap Stmt.loadS = (List.range 64).flatMap fun k => [(.n 3, k), (.n 50, k)] := by
  decide

set_option maxRecDepth 100000 in
theorem rsPre_quiet : rsPre.all stmtQuietB = true := by decide

set_option maxRecDepth 100000 in
theorem rsPre_noHeap : rsPre.all noHeapHintB = true := by decide

/-- The count's bits' hint. -/
def rsHint : Stmt := .atom (.hint (.bitsExp (.n 2) 6 (.stack [.n 4, .n 5, .n 6, .n 7, .n 8, .n 9])))

set_option maxRecDepth 100000 in
theorem rsPre_noComputed : rsPre.all (fun s => stmtsEqb [s] [rsHint] || noComputedB s) = true := by decide

theorem rsDNames_get {r : ℕ} (hr : r < 8) : rsDNames[r]! = rsEqRowsNames.getD r "" := by
  interval_cases r <;> rfl

/-! ## The valuation and the own words -/

/-- The last row's index, `⌈count / 8⌉`. -/
def rsH (count : ℕ) : ℕ := (count + 7) / 8

/-- The count's two parts' generators: `g^r` and `g^q` from the six bits. -/
def rsV23 (count : ℕ) : E :=
  (word 1 0 + bitWord (count.testBit 0) * word 3 0) * (word 1 0 + bitWord (count.testBit 1) * word 5 0) *
    (word 1 0 + bitWord (count.testBit 2) * word 17 0)

def rsV37 (count : ℕ) : E :=
  (word 1 0 + bitWord (count.testBit 3) * word 3 0) * (word 1 0 + bitWord (count.testBit 4) * word 5 0) *
    (word 1 0 + bitWord (count.testBit 5) * word 17 0)

/-- `rs_eq_run`'s values before the seed's words: the arguments, the count's bits, the chain at `c`. -/
def rsValsA (z p1 seed : E) (count c : ℕ) : List E :=
  let b : ℕ → E := fun i => bitWord (count.testBit i)
  let v13 := word 1 0 + b 0 * word 3 0
  let v17 := word 1 0 + b 1 * word 5 0
  let v18 := v13 * v17
  let v22 := word 1 0 + b 2 * word 17 0
  let v23 := v18 * v22
  let v27 := word 1 0 + b 3 * word 3 0
  let v31 := word 1 0 + b 4 * word 5 0
  let v32 := v27 * v31
  let v36 := word 1 0 + b 5 * word 17 0
  let v37 := v32 * v36
  let v38 := v37 * v37
  let v39 := v38 * v38
  let v40 := v39 * v39
  let v43 := v37 * word 4 0
  let v44 := v43 * v43
  let v45 := v44 * v44
  let v46 := v45 * v45
  let v47 := v46 * v46
  let v48 := v47 * v47
  let v49 := v48 * v48
  [z, p1, gen ^ count, seed, b 0, b 1, b 2, b 3, b 4, b 5,
    word 1 0, word 3 0, b 0 * word 3 0, v13,
    word 1 0, word 5 0, b 1 * word 5 0, v17, v18,
    word 1 0, word 17 0, b 2 * word 17 0, v22, v23,
    word 1 0, word 3 0, b 3 * word 3 0, v27,
    word 1 0, word 5 0, b 4 * word 5 0, v31, v32,
    word 1 0, word 17 0, b 5 * word 17 0, v36, v37,
    v38, v39, v40, v40 * v23,
    word 4 0, v43, v44, v45, v46, v47, v48, v49, ptrAt c]

/-- `rs_eq_run`'s values after the seed's words: the loop's guard, the remainder's pointers. -/
def rsValsB (z p1 : E) (count c : ℕ) : List E :=
  let v37 := rsV37 count
  let v118 := v37 * v37
  let v119 := v118 * v118
  let v120 := v119 * v119
  let v121 := v37 * v37
  let v122 := v121 * v121
  let v123 := v122 * v122
  let v124 := v123 * v123
  let v125 := v124 * v124
  let v126 := v125 * v125
  let v130 := ptrAt (c + 64 * rsH count)
  [word 1 0, word 1 0 + v37, word 1 0, v118, v119, v120, v121, v122, v123, v124, v125, v126,
    ptrAt c * v126, z * v120, p1 * v120, v130, v130]

/-- `rs_eq_run`'s valuation: value `i`. -/
def rsVal (z p1 seed : E) (cs : List E) (count c : ℕ) (i : ℕ) : E :=
  if i < 51 then (rsValsA z p1 seed count c).getD i 0 else if i < 115 then cs.getD (i - 51) 0
  else (rsValsB z p1 count c).getD (i - 115) 0

/-- `rs_eq_run`'s own words: rows `0 ..= ⌈count / 8⌉` of `64`. -/
def rsWords (cs zs ps : List E) (count : ℕ) : List E :=
  (List.range (64 * (rsH count + 1))).map fun o => rsR cs zs ps (o / 64) (o % 64)

theorem rsWords_row {rd : Reader} {cs zs ps : List E} {count c : ℕ}
    (h : ReadsAt rd (ptrAt c) (rsWords cs zs ps count)) {hh : ℕ} (hhh : hh ≤ rsH count) {k : ℕ} (hk : k < 64) :
    LoadHolds rd (ptrAt c) (64 * hh + k) (rsR cs zs ps hh k) := by
  have := h (64 * hh + k) (by simp [rsWords]; nlinarith)
  simp only [rsWords, List.getElem_map, List.getElem_range] at this
  rwa [show (64 * hh + k) / 64 = hh by omega, show (64 * hh + k) % 64 = k by omega] at this

theorem bits64' : ∀ p < 64, (p.testBit 0).toNat + 2 * (p.testBit 1).toNat + 4 * (p.testBit 2).toNat = p % 8 ∧
    (p.testBit 3).toNat + 2 * (p.testBit 4).toNat + 4 * (p.testBit 5).toNat = p / 8 := by
  decide

/-- A chunk's leaf meaning, from its `ChunkOk`. -/
theorem meaning_of_chunkOk {rd : Reader} {chain z p : E} {t : ℕ} {zt pt ct : List E}
    (h : ChunkOk rd chain z p t zt pt ct) {n : ℕ} (hz : zt.length = n) (hp : pt.length = n) (hn : 0 < n) :
    MeaningRsEqRows n rd [chain * gen ^ (64 * t), z * gen ^ (8 * t), p * gen ^ (8 * t)]
      [chain * gen ^ (64 * t) * gen ^ 64] :=
  Or.inr ⟨hn, zt, pt, ct, hz, hp, h.2.2.1, h.1, h.2.1, h.2.2.2.1, h.2.2.2.2, rfl⟩

theorem ptrCells_mapR {R R' : ℕ → Prop} {x : E} {n : ℕ} (h : PtrCells R x n) (hR : ∀ i, R i → R' i) :
    PtrCells R' x n := fun off hoff => by
  obtain ⟨i, hi, hr⟩ := h off hoff
  exact ⟨i, hi, hR i hr⟩

/-! ## Placed -/

variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}

/-- `rs_eq_run`'s end from its cursor `c`: its chain, the loop at the aligned base, the remainder's
leaf at the aligned base past it. -/
def rsEnd (fs : String → ℕ) (al : String → Bool) (count c : ℕ) : ℕ :=
  let cur := c + 64 * (count / 8 + 2)
  let c2 := llEnd fs al "rs_eq_rows__L8" (count / 8) 0
    (allocBase (al name% «rs_eq_run_loop0») cur + llBlk fs name% «rs_eq_run_loop0» (count / 8) 0)
  allocBase (al (rsEqRowsNames.getD (count % 8) "")) c2 + fs (rsEqRowsNames.getD (count % 8) "")

/-- The last row's words. -/
def RsOut (cs zs ps : List E) (row : E) (rd : Reader) : Prop :=
  ∀ j < 64, LoadHolds rd row j (ringRow (cs.getD j 0) zs ps j)

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- **`rs_eq_run` completes placed**, `count < 64`: its chain at its cursor, returning the last row's
pointer, whose words the caller reads (`RsOut`). -/
theorem rs_eq_run_placed (k : ℕ) {count : ℕ} (hcount : count < 64) {z p1 seed : E} {zs ps cs : List E}
    (lz : zs.length = count) (lp : ps.length = count) (lc : cs.length = 64) {R : ℕ → Prop}
    (hRz : PtrCells R z count) (hRp : PtrCells R p1 count) (hRs : PtrCells R seed 64) (fp c : ℕ)
    (hfc : fp + fs "rs_eq_run" ≤ c) :
    CallAtA fs al cert k "rs_eq_run" [z, p1, gen ^ count, seed] [ptrAt (c + 64 * rsH count)] R
      (fun i => c + 64 * rsH count ≤ i ∧ i < c + 64 * rsH count + 64)
      (RsOut cs zs ps (ptrAt (c + 64 * rsH count)))
      (fun rd => ReadsAt rd z zs ∧ ReadsAt rd p1 ps ∧ ReadsAt rd seed cs) PostQuiet (fs "rs_eq_run") fp c
      (rsEnd fs al count c) := by
  set q := count / 8 with hq
  set r := count % 8 with hr
  have hpqr : count = 8 * q + r := by omega
  have hq8 : q < 8 := by omega
  have hr8 : r < 8 := by omega
  have hH : rsH count = if r = 0 then q else q + 1 := by unfold rsH; split <;> omega
  have hHle : rsH count ≤ q + 1 := by rw [hH]; split <;> omega
  obtain ⟨hb1, hb2⟩ := bits64' count hcount
  set σ : Val := fun v => rsVal z p1 seed cs count c v.idx with hσ
  -- the values
  have w3 : word 3 0 = gen ^ 1 + 1 := word_two_pow_xor_one (a := 1) (by norm_num)
  have w5 : word 5 0 = gen ^ 2 + 1 := word_two_pow_xor_one (a := 2) (by norm_num)
  have w17 : word 17 0 = gen ^ 4 + 1 := word_two_pow_xor_one (a := 4) (by norm_num)
  have w4 : word 4 0 = gen ^ 2 := word_two_pow (a := 2) (by norm_num)
  have h23 : σ (.n 23) = gen ^ r := by
    show (word 1 0 + bitWord (count.testBit 0) * word 3 0) * (word 1 0 + bitWord (count.testBit 1) * word 5 0) *
      (word 1 0 + bitWord (count.testBit 2) * word 17 0) = _
    rw [w3, w5, w17, bitf, bitf, bitf, ← pow_add, ← pow_add]; congr 1; omega
  have h37 : σ (.n 37) = gen ^ q := by
    show (word 1 0 + bitWord (count.testBit 3) * word 3 0) * (word 1 0 + bitWord (count.testBit 4) * word 5 0) *
      (word 1 0 + bitWord (count.testBit 5) * word 17 0) = _
    rw [w3, w5, w17, bitf, bitf, bitf, ← pow_add, ← pow_add]; congr 1; omega
  have e41 : σ (.n 41) = σ (.n 37) * σ (.n 37) * (σ (.n 37) * σ (.n 37)) * (σ (.n 37) * σ (.n 37) *
      (σ (.n 37) * σ (.n 37))) * σ (.n 23) := rfl
  have hassert : σ (.n 41) + σ (.n 2) = 0 := by
    rw [e41, h37, h23, show σ (.n 2) = gen ^ count from rfl, hpqr]
    rw [show gen ^ q * gen ^ q * (gen ^ q * gen ^ q) * (gen ^ q * gen ^ q * (gen ^ q * gen ^ q)) * gen ^ r =
      gen ^ (8 * q + r) by ring]
    exact add_self_E _
  have e49 : σ (.n 49) = (fun x : E => x * x)^[6] (σ (.n 37) * word 4 0) := rfl
  have h49 : σ (.n 49) = gen ^ (64 * (q + 2)) := by
    rw [e49, h37, w4]; simp only [Function.iterate_succ, Function.comp, Function.iterate_zero, id]; ring
  have h50 : σ (.n 50) = ptrAt c := rfl
  have h116 : σ (.n 116) = word 1 0 + σ (.n 37) := rfl
  have e120 : σ (.n 120) = σ (.n 37) * σ (.n 37) * (σ (.n 37) * σ (.n 37)) *
      (σ (.n 37) * σ (.n 37) * (σ (.n 37) * σ (.n 37))) := rfl
  have h120 : σ (.n 120) = gen ^ (8 * q) := by rw [e120, h37]; ring
  have e126 : σ (.n 126) = (fun x : E => x * x)^[6] (σ (.n 37)) := rfl
  have h126 : σ (.n 126) = gen ^ (64 * q) := by
    rw [e126, h37]; simp only [Function.iterate_succ, Function.comp, Function.iterate_zero, id]; ring
  have h127 : σ (.n 127) = ptrAt (c + 64 * q) := by
    rw [show σ (.n 127) = σ (.n 50) * σ (.n 126) from rfl, h50, h126, ptrAt_mul_gen_pow']
  have h128 : σ (.n 128) = z * gen ^ (8 * q) := by rw [show σ (.n 128) = z * σ (.n 120) from rfl, h120]
  have h129 : σ (.n 129) = p1 * gen ^ (8 * q) := by rw [show σ (.n 129) = p1 * σ (.n 120) from rfl, h120]
  have h130 : σ (.n 130) = ptrAt (c + 64 * rsH count) := rfl
  have hcsv : ∀ j < 64, σ (.n (51 + j)) = cs.getD j 0 := by
    intro j hj
    show rsVal z p1 seed cs count c (51 + j) = _
    unfold rsVal
    simp only [show ¬(51 + j < 51) by omega, show 51 + j < 115 by omega, ↓reduceIte, Nat.add_sub_cancel_left]
  -- the path
  set es := rsPre.flatMap (slEvs σ) ++ .call rsDNames[r]! [.n 127, .n 128, .n 129] [.n 130] ::
    [Stmt.atom (.copy (.n 131) (.n 130))].flatMap (slEvs σ) with hes
  have hw : walk σ (fn% «rs_eq_run»).body = .ret es [.n 131] := by
    rw [rs_body']
    exact walk_dispatch σ rsPre _ rsPre_straight rfl (.n 23) rsDNames _ _ _ (i := r)
      (by simp [rsDNames]; omega) (by simp [rsDNames]) (by rw [h23, gen_pow_eq_ofK])
  have hpre := straight_parts σ rsPre rsPre_straight
  have hallocs : allocs σ es = [64 * (q + 2)] := by
    rw [hes, allocs_append, hpre.2.1, allocs, List.filterMap_cons, ← allocs]
    simp [rsPre_allocSz, Ev.alloc?, slEvs, allocs, h49, logG_gen_pow (show 64 * (q + 2) < 2 ^ 64 - 1 by omega)]
  have hdsts : allocDsts es = [.n 50] := by
    rw [hes, allocDsts_append, hpre.1, allocDsts, List.filterMap_cons, ← allocDsts]
    simp [rsPre_allocSz, Ev.allocDst?, slEvs, allocDsts]
  have haddrs : addrs es = [] := by
    rw [hes, addrs_append, hpre.2.2.1, addrs, List.filterMap_cons, ← addrs]
    simp [rsPre_addrS, Ev.addr?, slEvs, addrs]
  have hcalls : calls es = [⟨name% «rs_eq_run_loop0», [.n 117, .n 37, .n 50, .n 0, .n 1], [], decide (σ (.n 116) ≠ 0)⟩,
      ⟨rsDNames[r]!, [.n 127, .n 128, .n 129], [.n 130], true⟩] := by
    rw [hes, calls_append, hpre.2.2.2, calls, List.filterMap_cons, ← calls]
    simp [rsPre_callS, mkCall, Ev.call?, slEvs, calls]
  have htk : decide (σ (.n 116) ≠ 0) = decide (q ≠ 0) := by
    rw [h116, h37, word_one]
    refine decide_eq_decide.mpr ⟨fun h he => h (by rw [he, pow_zero]; exact add_self_E _), fun h he => h ?_⟩
    have := e_add_eq_zero_iff.mp he
    rw [← pow_zero gen] at this
    exact (gen_pow_inj (by omega) (by omega) this).symm
  rw [rsDNames_get hr8] at hcalls hes
  -- the own words
  set H := rsH count with hHdef
  have hH8 : count ≤ 8 * H := by rw [hH]; split <;> omega
  set Wo : Words := [(c, rsWords cs zs ps count)] with hWo
  have hrow : ∀ rd, HoldsWords rd Wo → ∀ hh ≤ H, ∀ j < 64, LoadHolds rd (ptrAt c) (64 * hh + j) (rsR cs zs ps hh j) :=
    fun rd hw hh hhh j hj => rsWords_row (hw _ List.mem_cons_self) hhh hj
  have hown : ∀ i, c ≤ i → i < c + 64 * (q + 2) → ownData cert fp c "rs_eq_run" [64 * (q + 2)] es i :=
    fun i h1 h2 => Or.inl ⟨(64 * (q + 2), c), by simp [bases], h1, by omega⟩
  -- the chunks
  have hchunk : ∀ rd, ReadsAt rd z zs → ReadsAt rd p1 ps → HoldsWords rd Wo → ∀ t, 8 * t < count →
      ChunkOk rd (ptrAt c) z p1 t ((zs.drop (8 * t)).take 8) ((ps.drop (8 * t)).take 8)
        ((List.range 64).map (rsR cs zs ps t)) := by
    intro rd hz hp hw t ht
    refine chunks_of_rows lz lp lc hz hp (fun _ => ?_) (fun hh h1 h2 j hj => ?_) t ht
    · intro j hj
      have := hrow rd hw 0 (Nat.zero_le _) j (by omega)
      rwa [Nat.mul_zero, Nat.zero_add, rsR, Nat.mul_zero, ringRow_nil, List.getD_eq_getElem _ _ hj] at this
    · rw [take_min_length lz, take_min_length lp]
      simpa only [rsR] using hrow rd hw hh h2 j hj
  have hlast : ∀ rd, ReadsAt rd z zs → ReadsAt rd p1 ps → HoldsWords rd Wo →
      MeaningRsEqRows r rd [σ (.n 127), σ (.n 128), σ (.n 129)] [σ (.n 130)] := by
    intro rd hz hp hw
    rw [h127, h128, h129, h130]
    by_cases hr0 : r = 0
    · exact Or.inl ⟨hr0, by simp only [hH, hr0, ↓reduceIte]⟩
    · have hc := hchunk rd hz hp hw q (by omega)
      have := meaning_of_chunkOk hc (n := r) (by simp [lz]; omega) (by simp [lp]; omega) (by omega)
      rw [ptrAt_mul_gen_pow', ptrAt_mul_gen_pow'] at this
      simp only [hH, hr0, ↓reduceIte]
      rw [show c + 64 * (q + 1) = c + 64 * q + 64 by ring]
      exact this
  have hout : ∀ rd, HoldsWords rd Wo → RsOut cs zs ps (ptrAt (c + 64 * H)) rd := by
    intro rd hw j hj
    rw [← ptrAt_mul_gen_pow', loadHolds_mul_gen_pow]
    have := hrow rd hw H le_rfl j hj
    rwa [rsR, List.take_of_length_le (by rw [lz]; omega), List.take_of_length_le (by rw [lp]; omega)] at this
  -- the regions
  set Rk : ℕ → Prop := fun i => R i ∨ (c ≤ i ∧ i < c + 64 * (q + 2)) with hRk
  have hRkk : ∀ i, Rk i → (R i ∨ ownData cert fp c "rs_eq_run" [64 * (q + 2)] es i) ∨ False := by
    intro i hi
    rcases hi with hi | hi
    · exact Or.inl (Or.inl hi)
    · exact Or.inl (Or.inr (hown i hi.1 hi.2))
  have hleafA := rs_eq_rows_placed (fs := fs) (al := al) (cert := cert) k hr8.le (row := σ (.n 127))
    (z := σ (.n 128)) (p := σ (.n 129)) (rets := [σ (.n 130)]) (R := Rk)
    (by rw [h127]; exact ptrAt_cells fun i hi => Or.inr ⟨by omega, by omega⟩)
    (by rw [h128]; exact ptrCells_mapR (ptrCells_shift hRz (by omega)) fun i h => Or.inl h)
    (by rw [h129]; exact ptrCells_mapR (ptrCells_shift hRp (by omega)) fun i h => Or.inl h)
  set cur := c + 64 * (q + 2) with hcur
  set c1 := allocBase (al name% «rs_eq_run_loop0») cur with hc1
  set c2 := llEnd fs al "rs_eq_rows__L8" q 0 (c1 + llBlk fs name% «rs_eq_run_loop0» q 0) with hc2
  have hend : rsEnd fs al count c = allocBase (al (rsEqRowsNames.getD r "")) c2 + fs (rsEqRowsNames.getD r "") := rfl
  rw [hend]
  refine callAtA_node rs_not_loop hfc
    ⟨σ, fn% «rs_eq_run», es, [.n 131], Wo, [PostQuiet, PostQuiet],
      fun rd => HoldsWords rd Wo, fun _ => False, find_rs_eq_run, by rw [rs_params]; rfl, hw, rfl,
      ?_, ?_, ?_, ?_, fun i hi => ?_, ?_, fun rd h => ?_, ?_, ?_⟩
  · -- placed
    rw [hallocs]
    exact ⟨by rw [hdsts]; simp [bases, h50], by rw [haddrs]; simp⟩
  · rw [hallocs]
    refine ⟨fun q' hq' => ?_, List.pairwise_singleton _ _⟩
    rw [List.mem_singleton] at hq'; subst hq'
    refine Or.inr ⟨le_rfl, ?_⟩
    simp only [rsWords, List.length_map, List.length_range, List.sum_cons, List.sum_nil, Nat.add_zero]
    omega
  · -- the loads
    intro A hA
    rw [hallocs]
    have hnil : loadAddrs σ (Ev.call (rsEqRowsNames.getD r "") [.n 127, .n 128, .n 129] [.n 130] ::
        [Stmt.atom (.copy (.n 131) (.n 130))].flatMap (slEvs σ)) = [] := rfl
    rw [hes, loadAddrs_append, loadAddrs_straight _ _ rsPre_straight, rsPre_loads, hnil, List.append_nil] at hA
    obtain ⟨⟨x, off⟩, hm, rfl⟩ := List.mem_map.mp hA
    obtain ⟨j, hj, hm⟩ := List.mem_flatMap.mp hm
    rw [List.mem_range] at hj
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
    have h3 : σ (.n 3) = seed := rfl
    rcases hm with ⟨hx, ho⟩ | ⟨hx, ho⟩ <;> subst hx <;> rw [ho]
    · obtain ⟨i, hi, hRi⟩ := hRs j hj
      exact ⟨i, by rw [h3]; exact hi, Or.inr (Or.inl hRi)⟩
    · exact ⟨c + j, by rw [h50]; exact Main.addr_ofK _ _, Or.inl (hown _ (by omega) (by omega))⟩
  · -- no heap hint
    intro A hA
    rw [hes, heapHintAddrs_append, heapHintAddrs_nil_of rsPre rsPre_noHeap, heapHintAddrs, List.flatMap_cons,
      ← heapHintAddrs] at hA
    simp [Ev.hintAddrs, slEvs, heapHintAddrs] at hA
  · -- the claimed data
    rw [hallocs]
    exact Or.inl (hown i (by omega) (by omega))
  · -- the callees
    rw [hcalls, hallocs, htk]
    by_cases hq0 : q = 0
    · have hd : decide (q ≠ 0) = false := decide_eq_false (by omega)
      simp only [KidsAtF, hd, Bool.false_eq_true, ↓reduceIte, List.headD_cons, List.tail_cons]
      refine ⟨⟨fun v => ([V.n 117, .n 37, .n 50, .n 0, .n 1].map σ).getD v.idx 0, fn% «rs_eq_run_loop0», find_loop5,
        by rw [rrl_T.params]; rfl⟩, fs (rsEqRowsNames.getD r ""),
        allocBase (al (rsEqRowsNames.getD r "")) c2 + fs (rsEqRowsNames.getD r ""), Rk, fun _ => False,
        fun _ => True, hRkk, ?_, rfl,
        fun _ h => h.1, fun _ h => h.elim⟩
      have e : allocBase (al name% «rs_eq_run_loop0») (c + [64 * (q + 2)].sum) +
          fs (tailKey name% «rs_eq_run_loop0») = c2 := by
        simp only [hc2, hc1, hcur, llBlk, llEnd, hq0, List.sum_cons, List.sum_nil, Nat.add_zero, Nat.sub_self,
          zero_mul, zero_add, Function.iterate_zero, id]
      rw [e]
      exact (hleafA _ _).mono (fun _ h => h) (fun _ h => h) (fun _ _ => trivial)
        (fun rd h => hlast rd h.1.1 h.1.2.1 h.2) (fun _ _ _ h => h)
    · have hd : decide (q ≠ 0) = true := decide_eq_true hq0
      simp only [KidsAtF, hd, ↓reduceIte, List.headD_cons, List.tail_cons]
      have hloop := rrl_placed (fs := fs) (al := al) (cert := cert) (k := k) (q := q) (j := 0) (by omega)
        (by omega) (chain := ptrAt c) (z := z) (p := p1) (R := Rk)
        (ptrAt_cells fun i hi => Or.inr ⟨by omega, by omega⟩)
        (ptrCells_mapR (ptrCells_mono hRz (by omega)) fun i h => Or.inl h)
        (ptrCells_mapR (ptrCells_mono hRp (by omega)) fun i h => Or.inl h) c1
        (c1 + llBlk fs name% «rs_eq_run_loop0» q 0)
      have h0 : [V.n 117, .n 37, .n 50, .n 0, .n 1].map σ = [gen ^ 0, gen ^ q, ptrAt c, z, p1] := by
        simp only [List.map_cons, List.map_nil, h37, h50, pow_zero]
        rfl
      refine ⟨llBlk fs name% «rs_eq_run_loop0» q 0, c2, Rk, fun _ => False, fun _ => True,
        hRkk, ?_,
        fs (rsEqRowsNames.getD r ""), allocBase (al (rsEqRowsNames.getD r "")) c2 + fs (rsEqRowsNames.getD r ""),
        Rk, fun _ => False, fun _ => True, fun i hi => (hRkk i hi).elim (fun h => Or.inl h) False.elim, ?_, rfl,
        fun _ h => h.1.1, fun _ h => h.elim⟩
      · rw [h0, show c + [64 * (q + 2)].sum = cur by simp [hcur]]
        refine hloop.mono (fun _ h => h) (fun _ h => h) (fun _ _ => trivial) (fun rd h t _ ht => ?_)
          (fun _ _ _ h => h)
        have hc := hchunk rd h.1.1 h.1.2.1 h.2 t (by omega)
        have := meaning_of_chunkOk hc (n := 8) (by simp [lz]; omega) (by simp [lp]; omega) (by omega)
        simp only [llArgs, ← pow_mul]
        rwa [show t * 64 = 64 * t by ring, show t * 8 = 8 * t by ring]
      · exact (hleafA _ _).mono (fun _ h => h) (fun _ h => h) (fun _ _ => trivial)
          (fun rd h => hlast rd h.1.1 h.1.2.1 h.2.1) (fun _ _ _ h => h)
  · exact hout rd h
  · -- the events
    intro rd _ hP hw ev hev
    rw [hes] at hev
    simp only [List.mem_append, List.mem_cons] at hev
    rcases hev with hev | rfl | hev
    · obtain ⟨s, hs, hev⟩ := List.mem_flatMap.mp hev
      have hK116 : IsInK (σ (.n 116)) := by
        rw [h116, h37, word_one, ← pow_zero gen]; exact isInK_add (gen_pow_isInK _) (gen_pow_isInK _)
      have hs' : SOkV rd σ s := by
        simp only [rsPre, List.mem_append] at hs
        rcases hs with (((hs | hs) | hs) | hs) | hs
        · simp only [rsA, List.mem_cons, List.not_mem_nil, or_false] at hs
          rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          exacts [trivial, bitWord_sq _, rfl, rfl, rfl, rfl, bitWord_sq _, rfl, rfl, rfl, rfl, rfl, bitWord_sq _, rfl,
            rfl, rfl, rfl, rfl, bitWord_sq _, rfl, rfl, rfl, rfl, bitWord_sq _, rfl, rfl, rfl, rfl, rfl,
            bitWord_sq _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hassert]
        · simp only [rsAlloc, List.mem_cons, List.not_mem_nil, or_false] at hs
          rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          exacts [rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial]
        · simp only [rsInits, List.mem_flatten, List.mem_map, List.mem_range] at hs
          obtain ⟨_, ⟨j, hj, rfl⟩, hs⟩ := hs
          simp only [rsInit, List.mem_cons, List.not_mem_nil, or_false] at hs
          rcases hs with rfl | rfl
          · show LoadHolds rd (σ (.n 3)) j (σ (.n (51 + j)))
            rw [hcsv j hj, show σ (.n 3) = seed from rfl, List.getD_eq_getElem _ _ (by omega)]
            exact hP.2.2 j (by omega)
          · show LoadHolds rd (σ (.n 50)) j (σ (.n (51 + j)))
            rw [hcsv j hj, h50]
            have := hrow rd hw 0 (Nat.zero_le _) j hj
            rwa [Nat.mul_zero, Nat.zero_add, rsR, Nat.mul_zero, ringRow_nil] at this
        · simp only [rsG, List.mem_cons, List.not_mem_nil, or_false] at hs
          rcases hs with rfl | rfl | rfl
          exacts [rfl, rfl, rfl]
        · simp only [rsT0, List.mem_cons, List.not_mem_nil, or_false] at hs
          rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          exacts [hK116, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl]
      exact events_sokV hs' hev
    · trivial
    · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, slEvs, List.mem_singleton] at hev
      subst hev
      rfl
  · -- the post
    intro rd ts _ _ _ hv hp'
    refine postQuiet_node find_rs_eq_run hw (fun a ha => ?_) (fun ev hev => ?_) hv (by rw [hcalls] at hp' ⊢; exact hp') _
    · rw [hes] at ha
      simp only [List.mem_append, List.mem_cons, reduceCtorEq, false_or] at ha
      rcases ha with ha | ha
      · obtain ⟨s, hs, ha⟩ := List.mem_flatMap.mp ha
        exact quiet_of_slEvs (List.all_eq_true.mp rsPre_quiet s hs) ha
      · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, slEvs, List.mem_singleton] at ha
        cases ha; rfl
    · rw [hes] at hev
      simp only [List.mem_append, List.mem_cons] at hev
      rcases hev with hev | rfl | hev
      · obtain ⟨s, hs, hev⟩ := List.mem_flatMap.mp hev
        have := List.all_eq_true.mp rsPre_noComputed s hs
        simp only [Bool.or_eq_true] at this
        rcases this with hh | hnc
        · obtain rfl := List.head_eq_of_cons_eq (stmtsEqb_sound hh)
          simp only [rsHint, slEvs, List.mem_singleton] at hev
          subst hev
          exact ⟨count, by omega, by rw [show σ (.n 2) = gen ^ count from rfl, gen_pow_eq_ofK], rfl⟩
        · exact exact_of_slEvs hnc hev
      · trivial
      · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, slEvs, List.mem_singleton] at hev
        subst hev; trivial

end
end LeanVM.Guest.B1.VsC
