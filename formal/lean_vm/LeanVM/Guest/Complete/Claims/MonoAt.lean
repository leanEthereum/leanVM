module

public import LeanVM.Guest.Complete.Claims.MonoLoops
public import LeanVM.Guest.Complete.Claims.AnyAt
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«child_claim_list_mono»

/-!
# `child_claim_list_mono`, placed

`mono_callAtA`: `child_claim_list_mono` at `(fp, c)` on `n < 2^19` claims at strictly increasing
slots `o j` (`MRec`: below `L`, every mark `base` at `g^(rg + o j)`, cells at `g^(eP + 4 o j)`, all
in the region, the walk ending at most at `L`), its chain buffer at `c` holding `monoCells`, then
`child_claim_list_mono_loop0` over the `n / 136` big frames, `child_claim_list_mono_loop1` over the
`n % 136 / 17` groups (`monoL_callAtA`), the dispatch to `child_claim_list_mono_last__L{n % 17}`
(`mlc_callAtA`); it returns the cells' digest by a tree of honest shape (`monoHonest`), ending at
`monoEnd fs al n c`.
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Guest.Value.Keccak LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}

set_option maxRecDepth 100000 in
theorem monoP1_noHeap : monoP1.all noHeapHintC = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem mono_noWit : Stmt.noWitList (Fn.body fn% «child_claim_list_mono») = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem monoPost_noHeap : monoPost.all noHeapHintC = true := by decide +kernel

/-- `child_claim_list_mono`'s end at `(fp, c)` on `n` claims: its buffer, its loops, its last group. -/
def monoEnd (fs : String → ℕ) (al : String → Bool) (n c : ℕ) : ℕ :=
  allocBase (al (mlNames.getD (n % 17) ""))
    (allocBase (al name% «child_claim_list_mono_loop1»)
      (allocBase (al name% «child_claim_list_mono_loop0») (c + 15 * (n / 136 + n % 136 / 17 + 1)) +
        lpBlk fs name% «child_claim_list_mono_loop0» (n / 136)) +
      lpBlk fs name% «child_claim_list_mono_loop1» (n % 136 / 17)) + fs (mlNames.getD (n % 17) "")

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- **`child_claim_list_mono` completes placed** on `n < 2^19` claims at strictly increasing slots
in the region `R`: its chain buffer at `c`, its loops and its last group after it, its tree of
honest shape. -/
theorem mono_callAtA {k : ℕ} (hk : 17 ≤ k) {eP rg L n : ℕ} {base : E} {o : ℕ → ℕ} {cells : List E}
    (hn : n < 2 ^ 19) (hl : cells.length = 4 * n) (hinc : ∀ i < n, mStart o i ≤ o i)
    (hend : mStart o n ≤ L) {R : ℕ → Prop}
    (hR2 : ∀ j < n, R (rg + o j)) (hR3 : ∀ j < n, ∀ c < 4, R (eP + 4 * o j + c)) {Pre : Reader → Prop}
    (hmem : ∀ rd, LowDef k rd → Pre rd →
      MRec rd (gen ^ rg) L (gen ^ eP) base n o cells ∧ BoundMem rd (L + 1))
    {fp c : ℕ} (hfc : fp + fs "child_claim_list_mono" ≤ c) :
    CallAtA fs al cert k "child_claim_list_mono" (anyArgs eP rg base L n)
      (digestCells (keccak256 (cellsBytes cells))) R (fun _ => False) (fun _ => True) Pre
      (fun rd t => monoHonest n t ∧ t.pops coreProgram rd = gapPops o 0 n) (fs "child_claim_list_mono") fp c
      (monoEnd fs al n c) := by
  set a := n / 136 with ha
  set b := n % 136 / 17 with hb
  set r := n % 17 with hr
  have hnm : n = 136 * a + 17 * b + r := by omega
  have hb8 : b < 8 := by omega
  have hr17 : r < 17 := by omega
  set chain : E := ptrAt c with hchain
  set Wo : Words := [(c, monoCells (gen ^ rg) (gen ^ eP) o cells a b)] with hWo
  set D := keccak256 (cellsBytes cells) with hD
  have hlc : (monoCells (gen ^ rg) (gen ^ eP) o cells a b).length = 15 * (a + b + 1) :=
    length_monoCells _ _ o cells a b
  set cur0 := c + 15 * (a + b + 1) with hcur0
  set f0 := allocBase (al name% «child_claim_list_mono_loop0») cur0 with hf0
  set cur1 := f0 + lpBlk fs name% «child_claim_list_mono_loop0» a with hcur1
  set f1 := allocBase (al name% «child_claim_list_mono_loop1») cur1 with hf1
  set cur2 := f1 + lpBlk fs name% «child_claim_list_mono_loop1» b with hcur2
  set f2 := allocBase (al (mlNames.getD r "")) cur2 with hf2
  have hend' : monoEnd fs al n c = f2 + fs (mlNames.getD r "") := rfl
  have h0le := le_allocBase (al name% «child_claim_list_mono_loop0») cur0
  have h1le := le_allocBase (al name% «child_claim_list_mono_loop1») cur1
  have h2le := le_allocBase (al (mlNames.getD r "")) cur2
  have hWoIn : WordsInA Wo (fp + 2) (fp + fs "child_claim_list_mono") c (c + 15 * (a + b + 1)) :=
    ⟨fun q hq => by
      simp only [hWo, List.mem_singleton] at hq
      subst hq
      exact Or.inr ⟨le_rfl, by rw [hlc]⟩, List.pairwise_singleton _ _⟩
  have hlow : ∀ rd, LowDef k rd → ∀ i < 2 ^ 17, ∃ t, LoadHolds rd (gen ^ i) 0 t := fun rd hl' i hi =>
    ⟨_, by rw [gen_pow_eq_ofK]; exact B1.loadHolds_low hl' (lt_of_lt_of_le hi (Nat.pow_le_pow_right (by norm_num) hk))⟩
  have hgm : ∀ (rd : Reader) (t : ℕ), HoldsWords rd Wo → t ≤ a + b →
      MonoRecAt rd (gen ^ c * gen ^ (15 * t)) (8 * clU a t) (cellsBytes (cells.take (68 * clU a t)))
        (gen ^ rg) (gen ^ eP) (mStart o (17 * clU a t)) := by
    intro rd t hw ht
    have hch : ReadsAt rd (gen ^ c) (monoCells (gen ^ rg) (gen ^ eP) o cells a b) := by
      rw [gen_pow_eq_ofK]; exact hw _ List.mem_cons_self
    exact monoRec_of_reads hch ht
  have hz : ∀ rd, HoldsWords rd Wo → MonoRecAt rd chain 0 [] (gen ^ rg) (gen ^ eP) 0 := by
    intro rd hw
    have h0 := hgm rd 0 hw (Nat.zero_le _)
    have e1 : gen ^ c * gen ^ (15 * 0) = gen ^ c := by simp
    rw [e1, show clU a 0 = 0 by simp [clU], show mStart o (17 * 0) = 0 by simp [mStart]] at h0
    rw [hchain, ptrAt_eq_gpow]
    exact h0
  have hbd : ∀ rd, LowDef k rd → Pre rd → BoundMem rd L := fun rd hl' hp i hi =>
    (hmem rd hl' hp).2 i (by omega)
  by_cases hex : ∃ rd0, LowDef k rd0 ∧ Pre rd0 ∧ HoldsWords rd0 Wo
  swap
  · refine ⟨Wo, ⟨fun q hq => ?_, List.pairwise_singleton _ _⟩, by omega, fun _ _ => trivial,
      fun rd hl' hw hp => absurd ⟨rd, hl', hp, hw⟩ hex⟩
    simp only [hWo, List.mem_singleton] at hq
    subst hq
    exact Or.inr ⟨le_rfl, by rw [hlc]; omega⟩
  obtain ⟨rd0, hl0, hp0, hw0⟩ := hex
  set args : List E := [gen ^ eP, gen ^ rg, base, gen ^ L, gen ^ a, gen ^ b, gen ^ r] with hargs
  have hV0 := monoBody_core (rd := rd0) (entries := gen ^ eP) (region := gen ^ rg) (base := base)
    (limit := gen ^ L) (a := a) (b := b) (c := r) D (hz rd0 hw0) (hlow rd0 hl0 a (by omega))
    (hlow rd0 hl0 b (by omega))
  set σ0 := monoσ rd0 args chain D with hσ0
  set es := monoP1.flatMap (slEvs σ0) ++ .call (mlNames.getD r "") monoDispArgs monoDispRets ::
    monoPost.flatMap (slEvs σ0) with hes
  have hpar : ∀ rd σ, MonoVals rd σ args a b chain D →
      σ (.n (val% «child_claim_list_mono» "entries_ptr")) = gen ^ eP ∧
      σ (.n (val% «child_claim_list_mono» "region")) = gen ^ rg ∧
      σ (.n (val% «child_claim_list_mono» "base")) = base ∧
      σ (.n (val% «child_claim_list_mono» "limit_g")) = gen ^ L ∧
      σ (.n (val% «child_claim_list_mono» "bigs")) = gen ^ a ∧
      σ (.n (val% «child_claim_list_mono» "groups")) = gen ^ b ∧
      σ (.n (val% «child_claim_list_mono» "rest")) = gen ^ r := by
    intro rd σ hV
    have h := hV.par
    simp only [hargs, List.cons.injEq, and_true] at h
    exact h
  have hguards : ∀ rd σ, MonoVals rd σ args a b chain D → monoP1.flatMap (slEvs σ) = monoP1.flatMap (slEvs σ0) := by
    intro rd σ hV
    refine slEvs_congr monoP1 fun c' f' a' hm => ?_
    have hk' := List.all_eq_true.mp monoP1_kinds _ hm
    simp only [isAtomS, Bool.false_or, Bool.or_eq_true] at hk'
    rcases hk' with hk' | hk'
    · have := stmtEqb_sound hk'
      simp only [mono31S, Stmt.callIf.injEq] at this
      obtain ⟨rfl, -, -⟩ := this
      rw [hV.v31, hV0.v31]
    · have := stmtEqb_sound hk'
      simp only [mono41S, Stmt.callIf.injEq] at this
      obtain ⟨rfl, -, -⟩ := this
      rw [hV.v41, hV0.v41]
  have hpost : ∀ σ : Val, monoPost.flatMap (slEvs σ) = monoPost.flatMap (slEvs σ0) := by
    intro σ
    refine slEvs_congr monoPost fun c' f' a' hm => absurd ?_ (List.not_mem_nil (a := (some c', f', a', ([] : List V))))
    rw [← monoPost_parts.2.2.1]
    exact List.mem_filterMap.mpr ⟨_, hm, rfl⟩
  have hwalk : ∀ rd σ, MonoVals rd σ args a b chain D → walk σ (Fn.body fn% «child_claim_list_mono») = .ret es monoVs := by
    intro rd σ hV
    rw [mono_body, monoDispS, Memory.walk_dispatch σ monoP1 monoPost monoP1_straight monoPost_straight _ mlNames
      monoDispArgs monoDispRets monoVs (i := r) (by simp [mlNames]; omega) (by simp [mlNames])
      (by rw [(hpar rd σ hV).2.2.2.2.2.2, gen_pow_eq_ofK]), hguards rd σ hV, hpost σ, mlNames_get hr17]
  have hal : ∀ rd σ, MonoVals rd σ args a b chain D → allocs σ es = [15 * (a + b + 1)] := by
    intro rd σ hV
    obtain ⟨-, hpa', -, -⟩ := straight_parts σ _ monoP1_straight
    obtain ⟨-, hqa', -, -⟩ := straight_parts σ _ monoPost_straight
    rw [hes, es3_allocs, ← hguards rd σ hV, ← hpost σ, hpa', hqa', monoP1_allocs, monoPost_parts.1]
    simp only [List.map_cons, List.map_nil, Sum.elim_inr, hV.v15, List.append_nil]
    rw [logG_gen_pow (show 15 * (a + b + 1) < 2 ^ 64 - 1 by omega)]
  have hal0 := hal rd0 σ0 hV0
  obtain ⟨hpd, hpa, hpad, hpc⟩ := straight_parts σ0 _ monoP1_straight
  obtain ⟨hqd, hqa, hqad, hqc⟩ := straight_parts σ0 _ monoPost_straight
  have hcalls : calls es = monoCalls n σ0 := by
    rw [hes, es3_calls, hpc, hqc, monoP1_calls, monoPost_parts.2.2.1]
    have h31 : decide (σ0 (.n (val% «child_claim_list_mono» "s4#1")) ≠ 0) = decide (a ≠ 0) := by
      rw [hV0.v31]; exact decide_eq_decide.mpr (one_add_gen_ne (by omega))
    have h41 : decide (σ0 (.n (val% «child_claim_list_mono» "s6#1")) ≠ 0) = decide (b ≠ 0) := by
      rw [hV0.v41]; exact decide_eq_decide.mpr (one_add_gen_ne (by omega))
    simp only [List.map_cons, List.map_nil, mkCall, h31, h41, List.cons_append, List.nil_append, monoCalls]
    rfl
  have hown' : ∀ i, c ≤ i → i < c + 15 * (a + b + 1) →
      ownData cert fp c "child_claim_list_mono" [15 * (a + b + 1)] es i := fun i h1 h2 =>
    Or.inl ⟨(15 * (a + b + 1), c), by simp [bases], h1, h2⟩
  have hown : ∀ i, c ≤ i → i < c + 15 * (a + b + 1) →
      ownData cert fp c "child_claim_list_mono" (allocs σ0 es) es i := fun i h1 h2 => by
    rw [hal0]; exact hown' i h1 h2
  obtain ⟨e0, e1, e2, e3, e4, e5, e6⟩ := hpar rd0 σ0 hV0
  have hσargs0 : [σ0 (.n (val% «child_claim_list_mono» "s4#2")), σ0 (.n (val% «child_claim_list_mono» "bigs")),
      σ0 (.n (val% «child_claim_list_mono» "chain")), σ0 (.n (val% «child_claim_list_mono» "base"))] =
      [1, gen ^ a, gen ^ c, base] := by
    rw [hV0.v32, e4, hV0.v16, e2, hchain, ptrAt_eq_gpow]
  have hσargs1 : [σ0 (.n (val% «child_claim_list_mono» "s6#2")), σ0 (.n (val% «child_claim_list_mono» "groups")),
      σ0 (.n (val% «child_claim_list_mono» "mid")), σ0 (.n (val% «child_claim_list_mono» "base"))] =
      [1, gen ^ b, gen ^ (c + 15 * a), base] := by
    rw [hV0.v42, e5, hV0.v39, e2, hchain, ptrAt_mul_gpow, ptrAt_eq_gpow]
  have hσargs2 : monoDispArgs.map σ0 = [gen ^ (c + 15 * (a + b)), gen ^ rg, base, gen ^ L] := by
    simp only [monoDispArgs, List.map_cons, List.map_nil]
    rw [hV0.v49, e1, e2, e3, hchain, ptrAt_mul_gpow, ptrAt_eq_gpow]
  have hσrets : monoDispRets.map σ0 = digestCells D := by
    simp only [monoDispRets, List.map_cons, List.map_nil]
    rw [hV0.v50, hV0.v51]; rfl
  obtain ⟨hl0', hsh0, hpar0, hpl0, hnh0⟩ := monoLoop0_facts
  obtain ⟨hl1', hsh1, hpar1, hpl1, hnh1⟩ := monoLoop1_facts
  refine callAtA_nodeRd mono_loop hfc ⟨σ0, fn% «child_claim_list_mono», es, monoVs, Wo,
    [fun rd t => t.pops coreProgram rd = gapPops o 0 (136 * a),
      fun rd t => t.pops coreProgram rd = gapPops o (136 * a) (17 * b),
      fun rd t => t.pops coreProgram rd = gapPops o (136 * a + 17 * b) r],
    fun rd => HoldsWords rd Wo, fun _ => False,
    find_child_claim_list_mono, by rw [hal0]; simpa using hWoIn, fun i hi => hi.elim, ?_, fun _ _ => trivial, ?_⟩
  · -- the callees
    rw [hcalls, hal0, List.sum_cons, List.sum_nil, Nat.add_zero, monoCalls]
    refine kidsAtF_loop (M := a) (fun ha0 => ?_) (fun ha0 => ?_) (kidsAtF_loop (M := b) (fun hb0 => ?_) (fun hb0 => ?_) ?_)
    · simp only [List.map_cons, List.map_nil]
      rw [hσargs0]
      refine monoL_callAtA (find_of_idx mono136_idx) hl0' hsh0 hpl0 hnh0 mono136_ok mc136_ok word_g136 word_g544
        mono136_nb mono136_wits (by norm_num) (by norm_num) (chP := c) (n0 := 0) (pre0 := []) (s0 := 0) (o := o)
        (cells := cells) (L := L) (rg := rg) (eP := eP) rfl (by rw [hl]; omega) (by omega) ha0
        (fun i hi => by simp only [Nat.zero_add]; exact hinc i (by omega))
        (fun rd hl' hp => ⟨fun q hq => ?_, fun j hj => by simp only [Nat.zero_add]; exact (hmem rd hl' hp.1).1 j (by omega),
          hbd rd hl' hp.1⟩)
        (fun q hq c' hc' => Or.inr (hown' _ (by omega) (by omega)))
        (fun i hi => Or.inl (by simp only [Nat.zero_add]; exact hR2 i (by omega)))
        (fun i hi c' hc' => Or.inl (by simp only [Nat.zero_add]; exact hR3 i (by omega) c' hc')) _ _ le_rfl
      have := hgm rd q hp.2 (by omega)
      rw [clU_big hq] at this
      rw [List.nil_append, show 0 + 64 * q = 8 * (8 * q) by ring, show 4 * 136 * q = 68 * (8 * q) by ring,
        show 0 + 136 * q = 17 * (8 * q) by ring]
      exact this
    · refine ⟨B1.Val.ofArgs [1, gen ^ a, gen ^ c, base],
        ⟨coreProgram.getD idx% «child_claim_list_mono_loop0» default, find_of_idx mono136_idx, ?_⟩⟩
      simp only [List.map_cons, List.map_nil]
      rw [hσargs0, hpar0]
      simp [Tree.val, B1.ofArgs_n]
    · simp only [List.map_cons, List.map_nil]
      rw [hσargs1]
      refine monoL_callAtA (find_of_idx mono17_idx) hl1' hsh1 hpl1 hnh1 mono17_ok mc17_ok word_g17 word_g68
        mono17_nb mono17_wits (by norm_num) (by norm_num) (chP := c + 15 * a) (n0 := 64 * a)
        (pre0 := cellsBytes (cells.take (544 * a))) (s0 := 136 * a) (o := o)
        (cells := cells.drop (544 * a)) (L := L) (rg := rg) (eP := eP)
        (by
          rw [length_cellsBytes, List.length_take, Nat.min_eq_left (by omega)]
          show 16 * (544 * a) = 136 * (64 * a); ring)
        (by rw [List.length_drop, hl]; omega) (by omega) hb0
        (fun i hi => hinc _ (by omega))
        (fun rd hl' hp => ⟨fun q hq => ?_, ?_, hbd rd hl' hp.1⟩)
        (fun q hq c' hc' => Or.inr (hown' _ (by omega) (by omega))) (fun i hi => Or.inl (hR2 _ (by omega)))
        (fun i hi c' hc' => Or.inl (hR3 _ (by omega) c' hc')) _ _ le_rfl
      · have := hgm rd (a + q) hp.2 (by omega)
        rw [clU_grp, ← pow_add] at this
        rw [← pow_add, show c + 15 * a + 15 * q = c + 15 * (a + q) by ring,
          show 64 * a + 8 * q = 8 * (8 * a + q) by ring, ← cellsBytes_append, ← List.take_add,
          show 544 * a + 4 * 17 * q = 68 * (8 * a + q) by ring,
          show 136 * a + 17 * q = 17 * (8 * a + q) by ring]
        exact this
      · have := mRec_drop (hmem rd hl' hp.1).1 (s := 136 * a) (k := 17 * b) (by omega)
        rwa [show 4 * (136 * a) = 544 * a by ring] at this
    · refine ⟨B1.Val.ofArgs [1, gen ^ b, gen ^ (c + 15 * a), base],
        ⟨coreProgram.getD idx% «child_claim_list_mono_loop1» default, find_of_idx mono17_idx, ?_⟩⟩
      simp only [List.map_cons, List.map_nil]
      rw [hσargs1, hpar1]
      simp [Tree.val, B1.ofArgs_n]
    · rw [KidsAtF]
      simp only [↓reduceIte, List.headD_cons, List.tail_cons, ← hr]
      rw [hσargs2, hσrets]
      have hpre : (cellsBytes (cells.take (68 * (8 * a + b)))).length = rate * (8 * (8 * a + b)) := by
        rw [length_cellsBytes, List.length_take, Nat.min_eq_left (by omega)]
        show 16 * (68 * (8 * a + b)) = 136 * (8 * (8 * a + b)); ring
      have hcl := mlc_callAtA (fs := fs) (al := al) (cert := cert) (k := k) hr17 (rP := c + 15 * (a + b))
        (s := 136 * a + 17 * b) (o := o) (cells := cells.drop (68 * (8 * a + b)))
        (n := 8 * (8 * a + b)) (pre := cellsBytes (cells.take (68 * (8 * a + b))))
        (mark := base) (L := L) (eP := eP) (rg := rg)
        (R := fun i => R i ∨ ownData cert fp c "child_claim_list_mono" [15 * (a + b + 1)] es i)
        (Pre := fun rd => Pre rd ∧ HoldsWords rd Wo) hpre (by rw [List.length_drop, hl]; omega)
        (fun i hi => hinc _ (by omega)) (by rw [show 136 * a + 17 * b + r = n by omega]; exact hend)
        (fun rd hl' hp => ⟨by
            have := hgm rd (a + b) hp.2 le_rfl
            rwa [clU_last, ← pow_add, show 17 * (8 * a + b) = 136 * a + 17 * b by ring] at this, by
            have := mRec_drop (hmem rd hl' hp.1).1 (s := 136 * a + 17 * b) (k := r) (by omega)
            rwa [show 4 * (136 * a + 17 * b) = 68 * (8 * a + b) by ring] at this,
          (hmem rd hl' hp.1).2⟩)
        (fun o' ho => Or.inr (hown' _ (by omega) (by omega))) (fun j hj => Or.inl (hR2 _ (by omega)))
        (fun j hj c' hc' => Or.inl (hR3 _ (by omega) c' hc'))
        (allocBase (al (mlNames.getD r "")) cur2) (allocBase (al (mlNames.getD r "")) cur2 + fs (mlNames.getD r ""))
      rw [← cellsBytes_append, List.take_append_drop] at hcl
      refine ⟨fs (mlNames.getD r ""), allocBase (al (mlNames.getD r "")) cur2 + fs (mlNames.getD r ""),
        fun i => R i ∨ ownData cert fp c "child_claim_list_mono" [15 * (a + b + 1)] es i, fun _ => False, fun _ => True,
        fun i hi => Or.inl hi, ?_, ?_⟩
      · exact hcl.mono (fun _ h => h) (fun _ h => h) (fun _ _ => trivial) (fun _ h => h) (fun _ _ _ h => h)
      · rw [KidsAtF, hend']
        exact ⟨rfl, fun _ h => h.1, fun _ h => h.elim⟩
  · -- on each memory
    intro rd hl' hp hw
    have hV := monoBody_core (rd := rd) (entries := gen ^ eP) (region := gen ^ rg) (base := base)
      (limit := gen ^ L) (a := a) (b := b) (c := r) D (hz rd hw) (hlow rd hl' a (by omega))
      (hlow rd hl' b (by omega))
    set σ := monoσ rd args chain D with hσ
    obtain ⟨hpd', -, hpad', -⟩ := straight_parts σ _ monoP1_straight
    obtain ⟨hqd', -, hqad', -⟩ := straight_parts σ _ monoPost_straight
    obtain ⟨f0', f1', f2', f3', f4', f5', f6'⟩ := hpar rd σ hV
    have hmE : ∀ s ∈ monoP1 ++ monoPost, ∀ x, s = .atom x → x.Holds rd σ := by
      intro s hs x rfl
      refine hV.atoms x (cl_mem_atoms ?_)
      rw [monoFlat_split]
      simp only [List.mem_append, List.mem_cons] at hs ⊢
      rcases hs with hs | hs <;> simp [hs]
    refine ⟨σ, ?_, hwalk rd σ hV, ?_, by rw [hal rd σ hV, hal0], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [mono_param, f0', f1', f2', f3', f4', f5', f6']; rfl
    · show [σ (.n (val% «child_claim_list_mono» "s11#0")), σ (.n (val% «child_claim_list_mono» "s11#0[1]"))] = _
      rw [hV.v54, hV.v55]; rfl
    · rw [hal0]
      refine ⟨?_, fun q hq => ?_⟩
      · rw [hes, ← hguards rd σ hV, ← hpost σ, es3_allocDsts, hpd', hqd', monoP1_allocs, monoPost_parts.1]
        simp [bases, hV.v16, hchain]
      · rw [hes, ← hguards rd σ hV, ← hpost σ, es3_addrs, hpad', hqad', monoP1_addrs, monoPost_parts.2.1] at hq
        simp at hq
    · rw [hcalls]
      intro cl hcl
      simp only [monoCalls, List.mem_cons, List.not_mem_nil, or_false] at hcl
      rcases hcl with rfl | rfl | rfl
      · simp [hV.v32, hV0.v32, e4, f4', hV.v16, hV0.v16, e2, f2']
      · simp [hV.v42, hV0.v42, e5, f5', hV.v39, hV0.v39, e2, f2']
      · simp [monoDispArgs, monoDispRets, hV.v49, hV0.v49, e1, f1', e2, f2', e3, f3', hV.v50, hV0.v50,
          hV.v51, hV0.v51]
    · intro A hA
      rw [hes, ← hguards rd σ hV, ← hpost σ, es3_loads, Memory.loadAddrs_straight σ _ monoP1_straight,
        Memory.loadAddrs_straight σ _ monoPost_straight, monoP1_loads, monoPost_parts.2.2.2] at hA
      simp only [List.map_nil, List.append_nil, List.map_map, List.mem_map, List.mem_range,
        Function.comp] at hA
      obtain ⟨c', hc15, rfl⟩ := hA
      refine ⟨c + c', by rw [hV.v16]; exact Main.addr_ofK _ _, Or.inl (hown _ (by omega) (by omega))⟩
    · intro A hA
      have h1 := heapHintAddrs_nil_of (σ := σ) monoP1_noHeap
      have h2 := heapHintAddrs_nil_of (σ := σ) monoPost_noHeap
      simp only [heapHintAddrs] at h1 h2
      rw [hes, ← hguards rd σ hV, ← hpost σ] at hA
      simp only [heapHintAddrs, List.flatMap_append, List.flatMap_cons, h1, h2] at hA
      simp [Ev.hintAddrs] at hA
    · intro ev hev
      rw [hes, ← hguards rd σ hV, ← hpost σ] at hev
      rcases List.mem_append.mp hev with he | he
      · refine events_straight (fun s hs => ?_) ev he
        have hk' := List.all_eq_true.mp monoP1_kinds s hs
        simp only [Bool.or_eq_true] at hk'
        rcases hk' with (hk' | hk') | hk'
        · exact sOk_atomS hk' (hmE s (by simp [hs]))
        · rw [stmtEqb_sound hk']
          show IsInK (σ (.n (val% «child_claim_list_mono» "s4#1")))
          rw [hV.v31, ← pow_zero gen]; exact gen_pow_add_isInK _ _
        · rw [stmtEqb_sound hk']
          show IsInK (σ (.n (val% «child_claim_list_mono» "s6#1")))
          rw [hV.v41, ← pow_zero gen]; exact gen_pow_add_isInK _ _
      rcases List.mem_cons.mp he with rfl | he
      · trivial
      · exact events_straight (fun s hs => sOk_atomS (List.all_eq_true.mp monoPost_atoms s hs)
          (hmE s (by simp [hs]))) ev he
    · intro ts hv hq
      refine ⟨⟨σ, ts, by rw [hal0]; rfl, ⟨f4', f5', f6', hV.v15, hV.v32, hV.v42⟩,
        fun fn es' vs' hf hw' => ?_, by simp [monoCalls, monoTs], kidsT_true _ _ _ (by simp [monoTs])⟩, ?_⟩
      · rw [find_child_claim_list_mono] at hf
        cases hf
        rw [hwalk rd σ hV] at hw'
        obtain ⟨he', -⟩ := Out.ret.inj hw'
        rw [← he', hcalls]
        simp only [monoCalls]
      · rw [hcalls] at hv hq
        have hk := popsKids_zip (monoCalls n σ0) ts [gapPops o 0 (136 * a),
          gapPops o (136 * a) (17 * b), gapPops o (136 * a + 17 * b) r] hv hq rfl
        rw [pops_noWit find_child_claim_list_mono (hwalk rd σ hV) mono_noWit
          (by rw [hcalls]; exact kidsValid_len hv), hk]
        simp only [monoCalls, List.zipWith_cons_cons, List.zipWith_nil_right, List.flatten_cons, List.flatten_nil,
          List.append_nil, ↓reduceIte]
        have e0 : (if decide (n / 136 ≠ 0) = true then gapPops o 0 (136 * a) else []) = gapPops o 0 (136 * a) := by
          by_cases h0 : a = 0
          · rw [h0]; simp [gapPops_zero]
          · simp [← ha, h0]
        have e1 : (if decide (n % 136 / 17 ≠ 0) = true then gapPops o (136 * a) (17 * b) else []) =
            gapPops o (136 * a) (17 * b) := by
          by_cases h0 : b = 0
          · rw [h0]; simp [gapPops_zero]
          · simp [← hb, h0]
        have h1 := gapPops_append o 0 (136 * a) (17 * b)
        have h2 := gapPops_append o 0 (136 * a + 17 * b) r
        rw [Nat.zero_add] at h1 h2
        rw [e0, e1, ← List.append_assoc, h1, h2, show 136 * a + 17 * b + r = n by omega]

end
end LeanVM.Guest.Complete
