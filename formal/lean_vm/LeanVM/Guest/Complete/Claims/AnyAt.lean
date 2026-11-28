module

public import LeanVM.Guest.Complete.Claims.AnyLoops
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«child_claim_list_any»

/-!
# `child_claim_list_any`, placed

`any_callAtA`: `child_claim_list_any` at `(fp, c)` on `n < 2^19` honest records (`RecMem`: slots
`o j` below `L`, marks `base · g^j` at `g^(rg + o j)`, cells at `g^(eP + 4 o j)`, all in the
region), its chain buffer at `c` holding `chainCells`, then `child_claim_list_any_loop0` over the
`n / 136` big frames, `child_claim_list_any_loop1` over the `n % 136 / 17` groups (`anyL_callAtA`),
the dispatch to `child_claim_list_last__L{n % 17}` (`ccl_callAtA`); it returns the cells' digest by
a tree of honest shape (`anyHonest`), ending at `anyEnd fs al n c`.
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Guest.Value.Keccak LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}

/-- The records after the first `s`, the marks `base · g^s`. -/
theorem recMem_drop {rd : Reader} {region limit entries base : E} {n : ℕ} {o : ℕ → ℕ} {cells : List E}
    (h : RecMem rd region limit entries base n o cells) {s k : ℕ} (hsk : s + k ≤ n) :
    RecMem rd region limit entries (base * gen ^ s) k (fun j => o (s + j)) (cells.drop (4 * s)) := by
  intro j hj
  obtain ⟨h1, h2, h3⟩ := h (s + j) (by omega)
  refine ⟨h1, by rwa [mul_assoc, ← pow_add], fun c hc => ?_⟩
  have e : (cells.drop (4 * s)).getD (4 * j + c) 0 = cells.getD (4 * (s + j) + c) 0 := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]
    rw [show 4 * s + (4 * j + c) = 4 * (s + j) + c by ring]
  rw [e]
  exact h3 c hc

set_option maxRecDepth 100000 in
theorem anyP1_noHeap : anyP1.all noHeapHintC = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem any_noWit : Stmt.noWitList (Fn.body fn% «child_claim_list_any») = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem anyPost_noHeap : anyPost.all noHeapHintC = true := by decide +kernel

/-- `child_claim_list_any`'s arguments on `n` records. -/
def anyArgs (eP rg : ℕ) (base : E) (L n : ℕ) : List E :=
  [gen ^ eP, gen ^ rg, base, gen ^ L, gen ^ (n / 136), gen ^ (n % 136 / 17), gen ^ (n % 17)]

/-- `child_claim_list_any`'s end at `(fp, c)` on `n` records: its buffer, its loops, its last group. -/
def anyEnd (fs : String → ℕ) (al : String → Bool) (n c : ℕ) : ℕ :=
  allocBase (al (cclNames.getD (n % 17) ""))
    (allocBase (al name% «child_claim_list_any_loop1»)
      (allocBase (al name% «child_claim_list_any_loop0») (c + 13 * (n / 136 + n % 136 / 17 + 1)) +
        lpBlk fs name% «child_claim_list_any_loop0» (n / 136)) +
      lpBlk fs name% «child_claim_list_any_loop1» (n % 136 / 17)) + fs (cclNames.getD (n % 17) "")

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- **`child_claim_list_any` completes placed** on `n < 2^19` honest records in the region `R`: its
chain buffer at `c`, its loops and its last group after it, its tree of honest shape. -/
theorem any_callAtA {k : ℕ} (hk : 17 ≤ k) {eP rg L n : ℕ} {base : E} {o : ℕ → ℕ} {cells : List E}
    (hn : n < 2 ^ 19) (hl : cells.length = 4 * n) (hL33 : L < 2 ^ 33) {R : ℕ → Prop}
    (hR2 : ∀ j < n, R (rg + o j)) (hR3 : ∀ j < n, ∀ c < 4, R (eP + 4 * o j + c)) {Pre : Reader → Prop}
    (hmem : ∀ rd, LowDef k rd → Pre rd →
      RecMem rd (gen ^ rg) (gen ^ L) (gen ^ eP) base n o cells ∧ BoundMem rd L)
    {fp c : ℕ} (hfc : fp + fs "child_claim_list_any" ≤ c) :
    CallAtA fs al cert k "child_claim_list_any" (anyArgs eP rg base L n)
      (digestCells (keccak256 (cellsBytes cells))) R (fun _ => False) (fun _ => True) Pre
      (fun rd t => anyHonest n t ∧ t.pops coreProgram rd = idxPops o 0 n) (fs "child_claim_list_any") fp c
      (anyEnd fs al n c) := by
  set a := n / 136 with ha
  set b := n % 136 / 17 with hb
  set r := n % 17 with hr
  have hnm : n = 136 * a + 17 * b + r := by omega
  have hb8 : b < 8 := by omega
  have hr17 : r < 17 := by omega
  set chain : E := ptrAt c with hchain
  set Wo : Words := [(c, chainCells cells a b)] with hWo
  set D := keccak256 (cellsBytes cells) with hD
  set last : E := gen ^ L * gen⁻¹ with hlastdef
  have hlast : last * gen = gen ^ L := by
    rw [hlastdef, mul_assoc, inv_mul_cancel₀ gen_ne_zero, mul_one]
  have hlc : (chainCells cells a b).length = 13 * (a + b + 1) := length_chainCells cells a b
  set cur0 := c + 13 * (a + b + 1) with hcur0
  set f0 := allocBase (al name% «child_claim_list_any_loop0») cur0 with hf0
  set cur1 := f0 + lpBlk fs name% «child_claim_list_any_loop0» a with hcur1
  set f1 := allocBase (al name% «child_claim_list_any_loop1») cur1 with hf1
  set cur2 := f1 + lpBlk fs name% «child_claim_list_any_loop1» b with hcur2
  set f2 := allocBase (al (cclNames.getD r "")) cur2 with hf2
  have hend : anyEnd fs al n c = f2 + fs (cclNames.getD r "") := rfl
  have h0le := le_allocBase (al name% «child_claim_list_any_loop0») cur0
  have h1le := le_allocBase (al name% «child_claim_list_any_loop1») cur1
  have h2le := le_allocBase (al (cclNames.getD r "")) cur2
  have hce : c + 13 * (a + b + 1) ≤ anyEnd fs al n c := by rw [hend]; omega
  have hWoIn : WordsInA Wo (fp + 2) (fp + fs "child_claim_list_any") c (c + 13 * (a + b + 1)) :=
    ⟨fun q hq => by
      simp only [hWo, List.mem_singleton] at hq
      subst hq
      exact Or.inr ⟨le_rfl, by rw [hlc]⟩, List.pairwise_singleton _ _⟩
  have hlow : ∀ rd, LowDef k rd → ∀ i < 2 ^ 17, ∃ t, LoadHolds rd (gen ^ i) 0 t := fun rd hl' i hi =>
    ⟨_, by rw [gen_pow_eq_ofK]; exact B1.loadHolds_low hl' (lt_of_lt_of_le hi (Nat.pow_le_pow_right (by norm_num) hk))⟩
  have hz : ∀ rd, HoldsWords rd Wo → ReadsAt rd chain (chainCells cells a b) ∧ StateAt rd chain 0 zeroState := by
    intro rd hw
    have hch : ReadsAt rd chain (chainCells cells a b) := hw _ List.mem_cons_self
    refine ⟨hch, ?_⟩
    have := state_of_reads hch (Nat.zero_le (a + b))
    rw [Nat.mul_zero, pow_zero, mul_one, show clU a 0 = 0 by simp [clU]] at this
    exact this
  by_cases hex : ∃ rd0, LowDef k rd0 ∧ Pre rd0 ∧ HoldsWords rd0 Wo
  swap
  · refine ⟨Wo, ⟨fun q hq => ?_, List.pairwise_singleton _ _⟩, by omega, fun _ _ => trivial,
      fun rd hl' hw hp => absurd ⟨rd, hl', hp, hw⟩ hex⟩
    simp only [hWo, List.mem_singleton] at hq
    subst hq
    exact Or.inr ⟨le_rfl, by rw [hlc]; omega⟩
  obtain ⟨rd0, hl0, hp0, hw0⟩ := hex
  set args : List E := [gen ^ eP, gen ^ rg, base, gen ^ L, gen ^ a, gen ^ b, gen ^ r] with hargs
  have hV0 := anyBody_core (rd := rd0) (entries := gen ^ eP) (region := gen ^ rg) (base := base)
    (limit := gen ^ L) (a := a) (b := b) (c := r) D (hz rd0 hw0).2 (hlow rd0 hl0 a (by omega))
    (hlow rd0 hl0 b (by omega))
  set σ0 := anyσ rd0 args chain D with hσ0
  set es := anyP1.flatMap (slEvs σ0) ++ .call (cclNames.getD r "") anyDispArgs anyDispRets ::
    anyPost.flatMap (slEvs σ0) with hes
  -- what every valuation with `AnyVals` gives
  have hpar : ∀ rd σ, AnyVals rd σ args a b chain D →
      σ (.n (val% «child_claim_list_any» "entries_ptr")) = gen ^ eP ∧
      σ (.n (val% «child_claim_list_any» "region")) = gen ^ rg ∧
      σ (.n (val% «child_claim_list_any» "base")) = base ∧
      σ (.n (val% «child_claim_list_any» "limit_g")) = gen ^ L ∧
      σ (.n (val% «child_claim_list_any» "bigs")) = gen ^ a ∧
      σ (.n (val% «child_claim_list_any» "groups")) = gen ^ b ∧
      σ (.n (val% «child_claim_list_any» "rest")) = gen ^ r := by
    intro rd σ hV
    have h := hV.par
    simp only [hargs, List.cons.injEq, and_true] at h
    exact h
  have hlastv : ∀ rd σ, AnyVals rd σ args a b chain D → σ (.n (val% «child_claim_list_any» "last_g")) = last := by
    intro rd σ hV
    calc σ (.n (val% «child_claim_list_any» "last_g"))
        = σ (.n (val% «child_claim_list_any» "last_g")) * gen * gen⁻¹ := by
          rw [mul_assoc, mul_inv_cancel₀ gen_ne_zero, mul_one]
      _ = last := by rw [hV.v8, (hpar rd σ hV).2.2.2.1]
  have hguards : ∀ rd σ, AnyVals rd σ args a b chain D → anyP1.flatMap (slEvs σ) = anyP1.flatMap (slEvs σ0) := by
    intro rd σ hV
    refine slEvs_congr anyP1 fun c' f' a' hm => ?_
    have hk' := List.all_eq_true.mp anyP1_kinds _ hm
    simp only [isAtomS, Bool.false_or, Bool.or_eq_true] at hk'
    rcases hk' with hk' | hk'
    · have := stmtEqb_sound hk'
      simp only [any17S, Stmt.callIf.injEq] at this
      obtain ⟨rfl, -, -⟩ := this
      rw [hV.v32, hV0.v32]
    · have := stmtEqb_sound hk'
      simp only [any18S, Stmt.callIf.injEq] at this
      obtain ⟨rfl, -, -⟩ := this
      rw [hV.v50, hV0.v50]
  have hpost : ∀ σ : Val, anyPost.flatMap (slEvs σ) = anyPost.flatMap (slEvs σ0) := by
    intro σ
    refine slEvs_congr anyPost fun c' f' a' hm => absurd ?_ (List.not_mem_nil (a := (some c', f', a', ([] : List V))))
    rw [← anyPost_parts.2.2.1]
    exact List.mem_filterMap.mpr ⟨_, hm, rfl⟩
  have hwalk : ∀ rd σ, AnyVals rd σ args a b chain D → walk σ (Fn.body fn% «child_claim_list_any») = .ret es anyVs := by
    intro rd σ hV
    rw [any_body, anyDispS, Memory.walk_dispatch σ anyP1 anyPost anyP1_straight anyPost_straight _ cclNames
      anyDispArgs anyDispRets anyVs (i := r) (by simp [cclNames]; omega) (by simp [cclNames])
      (by rw [(hpar rd σ hV).2.2.2.2.2.2, gen_pow_eq_ofK]), hguards rd σ hV, hpost σ, cclNames_get hr17]
  have hal : ∀ rd σ, AnyVals rd σ args a b chain D → allocs σ es = [13 * (a + b + 1)] := by
    intro rd σ hV
    obtain ⟨-, hpa', -, -⟩ := straight_parts σ _ anyP1_straight
    obtain ⟨-, hqa', -, -⟩ := straight_parts σ _ anyPost_straight
    rw [hes, es3_allocs, ← hguards rd σ hV, ← hpost σ, hpa', hqa', anyP1_allocs, anyPost_parts.1]
    simp only [List.map_cons, List.map_nil, Sum.elim_inr, hV.v16, List.append_nil]
    rw [logG_gen_pow (show 13 * (a + b + 1) < 2 ^ 64 - 1 by omega)]
  have hal0 := hal rd0 σ0 hV0
  obtain ⟨hpd, hpa, hpad, hpc⟩ := straight_parts σ0 _ anyP1_straight
  obtain ⟨hqd, hqa, hqad, hqc⟩ := straight_parts σ0 _ anyPost_straight
  have hcalls : calls es = anyCalls n σ0 := by
    rw [hes, es3_calls, hpc, hqc, anyP1_calls, anyPost_parts.2.2.1]
    have h32 : decide (σ0 (.n (val% «child_claim_list_any» "s3#1")) ≠ 0) = decide (a ≠ 0) := by
      rw [hV0.v32]; exact decide_eq_decide.mpr (one_add_gen_ne (by omega))
    have h50 : decide (σ0 (.n (val% «child_claim_list_any» "s6#1")) ≠ 0) = decide (b ≠ 0) := by
      rw [hV0.v50]; exact decide_eq_decide.mpr (one_add_gen_ne (by omega))
    simp only [List.map_cons, List.map_nil, mkCall, h32, h50, List.cons_append, List.nil_append, anyCalls]
    rfl
  have hown' : ∀ i, c ≤ i → i < c + 13 * (a + b + 1) →
      ownData cert fp c "child_claim_list_any" [13 * (a + b + 1)] es i := fun i h1 h2 =>
    Or.inl ⟨(13 * (a + b + 1), c), by simp [bases], h1, h2⟩
  have hown : ∀ i, c ≤ i → i < c + 13 * (a + b + 1) →
      ownData cert fp c "child_claim_list_any" (allocs σ0 es) es i := fun i h1 h2 => by
    rw [hal0]; exact hown' i h1 h2
  obtain ⟨e0, e1, e2, e3, e4, e5, e6⟩ := hpar rd0 σ0 hV0
  have hσargs0 : [σ0 (.n (val% «child_claim_list_any» "s3#2")), σ0 (.n (val% «child_claim_list_any» "bigs")),
      σ0 (.n (val% «child_claim_list_any» "chain")), σ0 (.n (val% «child_claim_list_any» "entries_ptr")),
      σ0 (.n (val% «child_claim_list_any» "region")), σ0 (.n (val% «child_claim_list_any» "base")),
      σ0 (.n (val% «child_claim_list_any» "last_g"))] = [1, gen ^ a, gen ^ c, gen ^ eP, gen ^ rg, base, last] := by
    rw [hV0.v33, e4, hV0.v17, e0, e1, e2, hlastv rd0 σ0 hV0, hchain, ptrAt_eq_gpow]
  have hσargs1 : [σ0 (.n (val% «child_claim_list_any» "s6#2")), σ0 (.n (val% «child_claim_list_any» "groups")),
      σ0 (.n (val% «child_claim_list_any» "mid")), σ0 (.n (val% «child_claim_list_any» "entries_ptr")),
      σ0 (.n (val% «child_claim_list_any» "region")), σ0 (.n (val% «child_claim_list_any» "mid_base")),
      σ0 (.n (val% «child_claim_list_any» "last_g"))] =
      [1, gen ^ b, gen ^ (c + 13 * a), gen ^ eP, gen ^ rg, base * gen ^ (136 * a), last] := by
    rw [hV0.v51, e5, hV0.v39, e0, e1, hV0.v48, e2, hlastv rd0 σ0 hV0, hchain, ptrAt_mul_gpow, ptrAt_eq_gpow]
  have hσargs2 : anyDispArgs.map σ0 =
      [gen ^ (c + 13 * (a + b)), gen ^ eP, gen ^ rg, base * gen ^ (136 * a + 17 * b), last] := by
    simp only [anyDispArgs, List.map_cons, List.map_nil]
    rw [hV0.v57, e0, e1, hV0.v63, e2, hlastv rd0 σ0 hV0, hchain, ptrAt_mul_gpow, ptrAt_eq_gpow]
  have hσrets : anyDispRets.map σ0 = digestCells D := by
    simp only [anyDispRets, List.map_cons, List.map_nil]
    rw [hV0.v64, hV0.v65]; rfl
  obtain ⟨hl0', hpar0, hpl0, hnh0⟩ := anyLoop0_facts
  obtain ⟨hl1', hpar1, hpl1, hnh1⟩ := anyLoop1_facts
  have hgc : ∀ (rd : Reader) (t : ℕ), HoldsWords rd Wo → t ≤ a + b →
      StateAt rd (gen ^ c * gen ^ (13 * t)) 0
        (absorbChunks (8 * clU a t) zeroState (cellsBytes (cells.take (68 * clU a t)))) := by
    intro rd t hw ht
    have := state_of_reads (hz rd hw).1 ht
    rwa [hchain, ptrAt_eq_gpow] at this
  refine callAtA_nodeRd any_loop hfc ⟨σ0, fn% «child_claim_list_any», es, anyVs, Wo,
    [fun rd t => t.pops coreProgram rd = idxPops o 0 (136 * a),
      fun rd t => t.pops coreProgram rd = idxPops (fun i => o (136 * a + i)) 0 (17 * b),
      fun rd t => t.pops coreProgram rd = idxPops (fun j => o (136 * a + 17 * b + j)) 0 r],
    fun rd => HoldsWords rd Wo, fun _ => False,
    find_child_claim_list_any, by rw [hal0]; simpa using hWoIn, fun i hi => hi.elim, ?_, fun _ _ => trivial, ?_⟩
  · -- the callees
    rw [hcalls, hal0, List.sum_cons, List.sum_nil, Nat.add_zero, anyCalls]
    refine kidsAtF_loop (M := a) (fun ha0 => ?_) (fun ha0 => ?_) (kidsAtF_loop (M := b) (fun hb0 => ?_) (fun hb0 => ?_) ?_)
    · simp only [List.map_cons, List.map_nil]
      rw [hσargs0]
      refine anyL_callAtA (find_of_idx any136_idx) hl0' hpl0 hnh0 any136_ok any136c_head any136c_edge
        any136c_recs any136_nb any136_wits (by norm_num) (chP := c) (n0 := 0) (pre0 := []) (o := o) (cells := cells) rfl
        (by rw [hl]; omega) hlast hL33 (by omega) ha0 (fun rd hl' hp => ⟨fun q hq => ?_,
          fun j hj => (hmem rd hl' hp.1).1 j (by omega), (hmem rd hl' hp.1).2⟩)
        (fun q hq c' hc' => Or.inr (hown' _ (by omega) (by omega))) (fun i hi => Or.inl (hR2 i (by omega)))
        (fun i hi c' hc' => Or.inl (hR3 i (by omega) c' hc')) _ _ le_rfl
      have := hgc rd q hp.2 (by omega)
      rw [clU_big hq] at this
      rw [List.nil_append, show 0 + 64 * q = 8 * (8 * q) by ring, show 4 * 136 * q = 68 * (8 * q) by ring]
      exact this
    · refine ⟨B1.Val.ofArgs [1, gen ^ a, gen ^ c, gen ^ eP, gen ^ rg, base, last],
        ⟨coreProgram.getD idx% «child_claim_list_any_loop0» default, find_of_idx any136_idx, ?_⟩⟩
      simp only [List.map_cons, List.map_nil]
      rw [hσargs0, hpar0]
      simp [Tree.val, B1.ofArgs_n]
    · simp only [List.map_cons, List.map_nil]
      rw [hσargs1]
      refine anyL_callAtA (find_of_idx any17_idx) hl1' hpl1 hnh1 any17_ok any17c_parts.1 any17c_parts.2.1
        any17c_parts.2.2 any17_nb any17_wits (by norm_num) (chP := c + 13 * a) (n0 := 64 * a)
        (pre0 := cellsBytes (cells.take (544 * a))) (o := fun i => o (136 * a + i))
        (cells := cells.drop (544 * a))
        (by
          rw [length_cellsBytes, List.length_take, Nat.min_eq_left (by omega)]
          show 16 * (544 * a) = 136 * (64 * a); ring)
        (by rw [List.length_drop, hl]; omega) hlast hL33 (by omega) hb0 (fun rd hl' hp => ⟨fun q hq => ?_, ?_,
          (hmem rd hl' hp.1).2⟩)
        (fun q hq c' hc' => Or.inr (hown' _ (by omega) (by omega))) (fun i hi => Or.inl (hR2 _ (by omega)))
        (fun i hi c' hc' => Or.inl (hR3 _ (by omega) c' hc')) _ _ le_rfl
      · have := hgc rd (a + q) hp.2 (by omega)
        rw [clU_grp, ← pow_add] at this
        rw [← pow_add, show c + 13 * a + 13 * q = c + 13 * (a + q) by ring,
          show 64 * a + 8 * q = 8 * (8 * a + q) by ring, ← cellsBytes_append, ← List.take_add,
          show 544 * a + 4 * 17 * q = 68 * (8 * a + q) by ring]
        exact this
      · have := recMem_drop (hmem rd hl' hp.1).1 (s := 136 * a) (k := 17 * b) (by omega)
        rwa [show 4 * (136 * a) = 544 * a by ring] at this
    · refine ⟨B1.Val.ofArgs [1, gen ^ b, gen ^ (c + 13 * a), gen ^ eP, gen ^ rg, base * gen ^ (136 * a), last],
        ⟨coreProgram.getD idx% «child_claim_list_any_loop1» default, find_of_idx any17_idx, ?_⟩⟩
      simp only [List.map_cons, List.map_nil]
      rw [hσargs1, hpar1]
      simp [Tree.val, B1.ofArgs_n]
    · rw [KidsAtF]
      simp only [↓reduceIte, List.headD_cons, List.tail_cons, ← hr]
      rw [hσargs2, hσrets]
      have hpre : (cellsBytes (cells.take (68 * (8 * a + b)))).length = rate * (8 * (8 * a + b)) := by
        rw [length_cellsBytes, List.length_take, Nat.min_eq_left (by omega)]
        show 16 * (68 * (8 * a + b)) = 136 * (8 * (8 * a + b)); ring
      have hcl := ccl_callAtA (fs := fs) (al := al) (cert := cert) (k := k) hr17 (sP := c + 13 * (a + b))
        (os := fun j => o (136 * a + 17 * b + j)) (cells := cells.drop (68 * (8 * a + b)))
        (n := 8 * (8 * a + b)) (pre := cellsBytes (cells.take (68 * (8 * a + b))))
        (marks := base * gen ^ (136 * a + 17 * b)) (L := L) (eP := eP) (rg := rg)
        (R := fun i => R i ∨ ownData cert fp c "child_claim_list_any" [13 * (a + b + 1)] es i)
        (Pre := fun rd => Pre rd ∧ HoldsWords rd Wo) hpre (by rw [List.length_drop, hl]; omega) hlast hL33
        (fun rd hl' hp => ⟨by
            have := hgc rd (a + b) hp.2 le_rfl
            rwa [clU_last, ← pow_add] at this, by
            have := recMem_drop (hmem rd hl' hp.1).1 (s := 136 * a + 17 * b) (k := r) (by omega)
            rwa [show 4 * (136 * a + 17 * b) = 68 * (8 * a + b) by ring] at this,
          (hmem rd hl' hp.1).2⟩)
        (fun o' ho => Or.inr (hown' _ (by omega) (by omega))) (fun j hj => Or.inl (hR2 _ (by omega)))
        (fun j hj c' hc' => Or.inl (hR3 _ (by omega) c' hc'))
        (allocBase (al (cclNames.getD r "")) cur2) (allocBase (al (cclNames.getD r "")) cur2 + fs (cclNames.getD r ""))
      rw [← cellsBytes_append, List.take_append_drop] at hcl
      refine ⟨fs (cclNames.getD r ""), allocBase (al (cclNames.getD r "")) cur2 + fs (cclNames.getD r ""),
        fun i => R i ∨ ownData cert fp c "child_claim_list_any" [13 * (a + b + 1)] es i, fun _ => False, fun _ => True,
        fun i hi => Or.inl hi, ?_, ?_⟩
      · exact hcl.mono (fun _ h => h) (fun _ h => h) (fun _ _ => trivial) (fun _ h => h) (fun _ _ _ h => h)
      · rw [KidsAtF, hend]
        exact ⟨rfl, fun _ h => h.1, fun _ h => h.elim⟩
  · -- on each memory
    intro rd hl' hp hw
    have hV := anyBody_core (rd := rd) (entries := gen ^ eP) (region := gen ^ rg) (base := base)
      (limit := gen ^ L) (a := a) (b := b) (c := r) D (hz rd hw).2 (hlow rd hl' a (by omega))
      (hlow rd hl' b (by omega))
    set σ := anyσ rd args chain D with hσ
    obtain ⟨hpd', -, hpad', -⟩ := straight_parts σ _ anyP1_straight
    obtain ⟨hqd', -, hqad', -⟩ := straight_parts σ _ anyPost_straight
    obtain ⟨f0', f1', f2', f3', f4', f5', f6'⟩ := hpar rd σ hV
    have hmE : ∀ s ∈ anyP1 ++ anyPost, ∀ x, s = .atom x → x.Holds rd σ := by
      intro s hs x rfl
      refine hV.atoms x (cl_mem_atoms ?_)
      rw [anyFlat_split]
      simp only [List.mem_append, List.mem_cons] at hs ⊢
      rcases hs with hs | hs <;> simp [hs]
    refine ⟨σ, ?_, hwalk rd σ hV, ?_, by rw [hal rd σ hV, hal0], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [any_param, f0', f1', f2', f3', f4', f5', f6']; rfl
    · show [σ (.n (val% «child_claim_list_any» "s11#0")), σ (.n (val% «child_claim_list_any» "s11#0[1]"))] = _
      rw [hV.v68, hV.v69]; rfl
    · rw [hal0]
      refine ⟨?_, fun q hq => ?_⟩
      · rw [hes, ← hguards rd σ hV, ← hpost σ, es3_allocDsts, hpd', hqd', anyP1_allocs, anyPost_parts.1]
        simp [bases, hV.v17, hchain]
      · rw [hes, ← hguards rd σ hV, ← hpost σ, es3_addrs, hpad', hqad', anyP1_addrs, anyPost_parts.2.1] at hq
        simp at hq
    · rw [hcalls]
      intro cl hcl
      simp only [anyCalls, List.mem_cons, List.not_mem_nil, or_false] at hcl
      rcases hcl with rfl | rfl | rfl
      · simp [hV.v33, hV0.v33, e4, f4', hV.v17, hV0.v17, e0, f0', e1, f1', e2, f2', hlastv rd σ hV,
          hlastv rd0 σ0 hV0]
      · simp [hV.v51, hV0.v51, e5, f5', hV.v39, hV0.v39, e0, f0', e1, f1', hV.v48, hV0.v48, e2, f2',
          hlastv rd σ hV, hlastv rd0 σ0 hV0]
      · simp [anyDispArgs, anyDispRets, hV.v57, hV0.v57, e0, f0', e1, f1', hV.v63, hV0.v63, e2, f2',
          hlastv rd σ hV, hlastv rd0 σ0 hV0, hV.v64, hV0.v64, hV.v65, hV0.v65]
    · intro A hA
      rw [hes, ← hguards rd σ hV, ← hpost σ, es3_loads, Memory.loadAddrs_straight σ _ anyP1_straight,
        Memory.loadAddrs_straight σ _ anyPost_straight, anyP1_loads, anyPost_parts.2.2.2] at hA
      simp only [List.map_nil, List.append_nil, List.map_map, List.mem_map, List.mem_range,
        Function.comp] at hA
      obtain ⟨c', hc13, rfl⟩ := hA
      refine ⟨c + c', by rw [hV.v17]; exact Main.addr_ofK _ _, Or.inl (hown _ (by omega) (by omega))⟩
    · intro A hA
      have h1 := heapHintAddrs_nil_of (σ := σ) anyP1_noHeap
      have h2 := heapHintAddrs_nil_of (σ := σ) anyPost_noHeap
      simp only [heapHintAddrs] at h1 h2
      rw [hes, ← hguards rd σ hV, ← hpost σ] at hA
      simp only [heapHintAddrs, List.flatMap_append, List.flatMap_cons, h1, h2] at hA
      simp [Ev.hintAddrs] at hA
    · intro ev hev
      rw [hes, ← hguards rd σ hV, ← hpost σ] at hev
      rcases List.mem_append.mp hev with he | he
      · refine events_straight (fun s hs => ?_) ev he
        have hk' := List.all_eq_true.mp anyP1_kinds s hs
        simp only [Bool.or_eq_true] at hk'
        rcases hk' with (hk' | hk') | hk'
        · exact sOk_atomS hk' (hmE s (by simp [hs]))
        · rw [stmtEqb_sound hk']
          show IsInK (σ (.n (val% «child_claim_list_any» "s3#1")))
          rw [hV.v32, ← pow_zero gen]; exact gen_pow_add_isInK _ _
        · rw [stmtEqb_sound hk']
          show IsInK (σ (.n (val% «child_claim_list_any» "s6#1")))
          rw [hV.v50, ← pow_zero gen]; exact gen_pow_add_isInK _ _
      rcases List.mem_cons.mp he with rfl | he
      · trivial
      · exact events_straight (fun s hs => sOk_atomS (List.all_eq_true.mp anyPost_atoms s hs)
          (hmE s (by simp [hs]))) ev he
    · intro ts hv hq
      refine ⟨⟨σ, ts, by rw [hal0]; rfl, ⟨f4', f5', f6', hV.v16, hV.v33, hV.v51⟩,
        fun fn es' vs' hf hw' => ?_, by simp [anyCalls, anyTs], kidsT_true _ _ _ (by simp [anyTs])⟩, ?_⟩
      · rw [find_child_claim_list_any] at hf
        cases hf
        rw [hwalk rd σ hV] at hw'
        obtain ⟨he', -⟩ := Out.ret.inj hw'
        rw [← he', hcalls]
        simp only [anyCalls]
      · rw [hcalls] at hv hq
        have hk := popsKids_zip (anyCalls n σ0) ts [idxPops o 0 (136 * a),
          idxPops (fun i => o (136 * a + i)) 0 (17 * b), idxPops (fun j => o (136 * a + 17 * b + j)) 0 r]
          hv hq rfl
        rw [pops_noWit find_child_claim_list_any (hwalk rd σ hV) any_noWit
          (by rw [hcalls]; exact kidsValid_len hv), hk]
        simp only [anyCalls, List.zipWith_cons_cons, List.zipWith_nil_right, List.flatten_cons, List.flatten_nil,
          List.append_nil, ↓reduceIte]
        rw [idxPops_shift, idxPops_shift, Nat.add_zero, Nat.add_zero]
        have e0 : (if decide (n / 136 ≠ 0) = true then idxPops o 0 (136 * a) else []) = idxPops o 0 (136 * a) := by
          by_cases h0 : a = 0
          · rw [h0]; simp [idxPops_zero]
          · simp [← ha, h0]
        have e1 : (if decide (n % 136 / 17 ≠ 0) = true then idxPops o (136 * a) (17 * b) else []) =
            idxPops o (136 * a) (17 * b) := by
          by_cases h0 : b = 0
          · rw [h0]; simp [idxPops_zero]
          · simp [← hb, h0]
        have h1 := idxPops_append o 0 (136 * a) (17 * b)
        have h2 := idxPops_append o 0 (136 * a + 17 * b) r
        rw [Nat.zero_add] at h1 h2
        rw [e0, e1, ← List.append_assoc, h1, h2, show 136 * a + 17 * b + r = n by omega]

end
end LeanVM.Guest.Complete
