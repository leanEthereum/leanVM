module

public import LeanVM.Guest.Complete.Claims.Leaves
public import LeanVM.Guest.Complete.LoopFHA
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«claim_list_chain»
import LeanVM.Guest.Data.ValNames.«claim_list_chain_loop0»
import LeanVM.Guest.Data.ValNames.«claim_list_chain_loop1»

/-!
# `claim_list_chain`, placed

`argStmt_regions`: a block whose loads and heap hints go through the arrays `ps` loads and hints in
a region covering them. `grpL_callAtA`: a frame loop (`claim_list_chain_loop0`, `_loop1`: its state
at `.n 9`, `chain · x^13`, its claims at `.n ep`, `entries · x^(4m)`) entered at `1` completes placed
from its blocks (`LoopBlock`), loading the chain's states and the claims, hinting the claims.
`chain_callAtA`: `claim_list_chain` at `(fp, c)` on `n < 2^19` claims' cells at `e`, its chain
buffer at `c` holding `chainCells`, its two loops and `claim_list_tail` after it, its tree of
honest shape (`chHonest`).
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Guest.Value.Keccak LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}

/-! ## Blocks through their arrays -/

theorem ptrAt_eq_gpow (b : ℕ) : ptrAt b = gen ^ b := (gen_pow_eq_ofK b).symm

theorem ptrAt_mul_gpow (q m : ℕ) : ptrAt q * gen ^ m = ptrAt (q + m) := by
  rw [gen_pow_eq_ofK, ptrAt, ptrAt, ← gpow_add']; exact (map_mul (algebraMap K E) _ _).symm

theorem hintAddrs_atom_hint {σ : Val} {h : Hint} {A : K} (hA : A ∈ Ev.hintAddrs σ (.atom (.hint h))) :
    ∃ p off len, (hintDest? h).bind destHeap? = some (p, off, len) ∧ ∃ i < len,
      A = (σ p).limb 0 * addressOfIndex (off + i) := by
  simp only [Ev.hintAddrs] at hA
  split at hA
  · rename_i p off len heq
    simp only [List.mem_map, List.mem_range] at hA
    obtain ⟨i, hi, rfl⟩ := hA
    exact ⟨p, off, len, heq, i, hi, rfl⟩
  · simp at hA

/-- A statement loading or hinting to the heap only through the arrays `ps`. -/
def argStmtOk (ps : List (V × ℕ)) : Stmt → Bool
  | .atom a => argAtomOk ps a
  | _ => true

theorem argStmt_regions {pre : List Stmt} {ps : List (V × ℕ)} (hok : pre.all (argStmtOk ps) = true)
    {σ : Val} {bs : V → ℕ} (hσ : ∀ q ∈ ps, σ q.1 = ptrAt (bs q.1)) {R : ℕ → Prop}
    (hR : ∀ q ∈ ps, ∀ i < q.2, R (bs q.1 + i)) :
    (∀ q ∈ pre.filterMap stmtLoad?, ∃ i, (σ q.1).limb 0 * addressOfIndex q.2 = addressOfIndex i ∧ R i) ∧
      ∀ A ∈ heapHintAddrs σ (pre.flatMap (slEvs σ)), ∃ i, A = addressOfIndex i ∧ R i := by
  have hok' : ∀ s ∈ pre, argStmtOk ps s = true := fun s hs => List.all_eq_true.mp hok s hs
  refine ⟨fun q hq => ?_, fun A hA => ?_⟩
  · obtain ⟨s, hs, hq⟩ := List.mem_filterMap.mp hq
    have hk := hok' s hs
    match s, hq, hk with
    | .atom (.load d p off), hq, hk =>
      simp only [stmtLoad?, Option.some.injEq] at hq
      subst hq
      simp only [argStmtOk, argAtomOk, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hk
      obtain ⟨q', hqm, hq1, hoff⟩ := hk
      refine ⟨bs q'.1 + off, ?_, hR q' hqm off hoff⟩
      rw [← hq1, hσ q' hqm]
      exact Main.addr_ofK _ off
  · obtain ⟨ev, he, hA⟩ := List.mem_flatMap.mp hA
    obtain ⟨s, hs, he⟩ := List.mem_flatMap.mp he
    have hk := hok' s hs
    cases s with
    | atom a =>
      simp only [slEvs, List.mem_singleton] at he
      subst he
      cases a with
      | hint h =>
        obtain ⟨p, off, len, hd, i, hi, rfl⟩ := hintAddrs_atom_hint hA
        simp only [argStmtOk, argAtomOk, hd, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hk
        obtain ⟨q, hqm, hq1, hlen⟩ := hk
        refine ⟨bs q.1 + (off + i), ?_, hR q hqm _ (by omega)⟩
        rw [← hq1, hσ q hqm]
        exact Main.addr_ofK _ _
      | _ => simp [Ev.hintAddrs] at hA
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

/-! ## The frame loops -/

/-- **A frame loop entered at `1` completes placed**: its state at `.n 9` (`26` cells from
`cb + 13j` at iteration `j`), its claims at `.n ep` (`4m` cells from `eb + 4mj`), in the region. -/
theorem grpL_callAtA {k : ℕ} {L : String} {fn : Fn} {m ep : ℕ} (hf : coreProgram.find? L = some fn)
    (hok : loopShapeF fn L = true) (hlp : coreProgram.loop L = true) (hpar : fn.params = [.n 0, .n 1, .n 2, .n 3])
    (hpl : (loopPre fn).all loopPlainHB = true)
    (hargs : (loopPre fn).all (argStmtOk [(.n 9, 26), (.n ep, 4 * m)]) = true)
    (hm9 : monoIs (atomsIn (loopPre fn)) (.n 9) (.n 2) (.n 0) 13 = true)
    (hmE : monoIs (atomsIn (loopPre fn)) (.n ep) (.n 3) (.n 0) (4 * m) = true) (hep : ep ≠ 9)
    {M cb eb : ℕ} (hM : M < 2 ^ 34) {R : ℕ → Prop} {Pre : Reader → Prop}
    (hRc : ∀ j < M, ∀ i < 26, R (cb + 13 * j + i)) (hRe : ∀ j < M, ∀ i < 4 * m, R (eb + 4 * m * j + i))
    (hblk : ∀ j < M, ∀ rd, LowDef k rd → Pre rd → LoopBlock rd fn (gen ^ j) (gen ^ M) [ptrAt cb, ptrAt eb])
    (hM0 : M ≠ 0) (fp c : ℕ) (hfc : fp + lpBlk fs L M ≤ c) :
    CallAtA fs al cert k L [1, gen ^ M, ptrAt cb, ptrAt eb] [] R (fun _ => False) (fun _ => True) Pre
      (fun _ _ => True) (lpBlk fs L M) fp c c := by
  have hpre : ∀ s ∈ loopPre fn, ∃ a, s = .atom a := by
    intro s hs
    have := List.all_eq_true.mp hpl s hs
    cases s with
    | atom a => exact ⟨a, rfl⟩
    | _ => simp [loopPlainHB] at this
  have h := loopFH_callAtA (fs := fs) (al := al) (cert := cert) (k := k) hf hok hlp hpl hM
    (rest := [ptrAt cb, ptrAt eb]) (R := R) (Pre := Pre) (fun j hj rd hl hp => ?_) 0 (Nat.pos_of_ne_zero hM0)
    fp c (by simpa using hfc)
  · simpa using h
  obtain ⟨σ, hσ, hs⟩ := hblk j hj rd hl hp
  rw [hpar] at hσ
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hσ
  obtain ⟨h0, h1, h2, h3⟩ := hσ
  have hsok : ∀ s ∈ loopPre fn, SOk rd σ s := by
    intro s hsm
    obtain ⟨a, rfl⟩ := hpre s hsm
    exact (hs _ hsm).1
  have hat : ∀ a ∈ atomsIn (loopPre fn), a.Holds rd σ := fun a ha => hsok _ (cl_atom_mem ha)
  have v9 : σ (.n 9) = ptrAt (cb + 13 * j) := by
    rw [monoIs_sound hm9 hat, h2, h0, ← pow_mul, ptrAt_mul_gpow, mul_comm j 13]
  have vE : σ (.n ep) = ptrAt (eb + 4 * m * j) := by
    rw [monoIs_sound hmE hat, h3, h0, ← pow_mul, ptrAt_mul_gpow, mul_comm j (4 * m)]
  have hne : (V.n ep) ≠ V.n 9 := fun h => hep (by cases h; rfl)
  refine ⟨σ, by rw [hpar]; simp [h0, h1, h2, h3], hsok, argStmt_regions hargs
    (bs := fun v => if v = .n 9 then cb + 13 * j else eb + 4 * m * j) (fun q hq => ?_) (fun q hq i hi => ?_)⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · simp [v9]
    · simp [vE, hne]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · simpa using hRc j hj i hi
    · simpa [hne] using hRe j hj i hi

/-! ## The callees, chained -/

/-- **A loop callee entered when `M ≠ 0`**, its block `lpBlk` either way, then the rest. -/
theorem kidsAtF_loop {k : ℕ} {σ : Val} {R : ℕ → Prop} {Pre O : Reader → Prop} {Dacc : ℕ → Prop}
    {Q : Reader → Tree → Prop} {Qs : List (Reader → Tree → Prop)} {L : String} {args : List V} {M : ℕ}
    {cs : List Call} {cur e : ℕ} {Oend : Reader → Prop} {Dend : ℕ → Prop}
    (htk : M ≠ 0 → CallAtA fs al cert k L (args.map σ) [] R (fun _ => False) (fun _ => True)
      (fun rd => Pre rd ∧ O rd) Q (lpBlk fs L M) (allocBase (al L) cur) (allocBase (al L) cur + lpBlk fs L M)
      (allocBase (al L) cur + lpBlk fs L M))
    (hph : M = 0 → ∃ σ', Phantom coreProgram (.phantom L σ') (args.map σ))
    (hrest : KidsAtF fs al cert k σ R Pre O Dacc Qs cs (allocBase (al L) cur + lpBlk fs L M) e Oend Dend) :
    KidsAtF fs al cert k σ R Pre O Dacc (Q :: Qs) (⟨L, args, [], decide (M ≠ 0)⟩ :: cs) cur e Oend Dend := by
  rw [KidsAtF]
  by_cases hM : M = 0
  · simp only [hM, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
    refine ⟨hph hM, ?_⟩
    rw [hM, lpBlk, Nat.zero_mul, Nat.zero_add] at hrest
    exact hrest
  · simp only [hM, ne_eq, not_false_eq_true, decide_true, ↓reduceIte, List.map_nil, List.headD_cons,
      List.tail_cons]
    refine ⟨lpBlk fs L M, _, R, fun _ => False, fun _ => True, fun i hi => Or.inl hi, htk hM, ?_⟩
    rw [show (fun rd => O rd ∧ True) = O from funext fun _ => and_true _,
      show (fun i => Dacc i ∨ False) = Dacc from funext fun _ => or_false _]
    exact hrest

theorem kidsT_true : ∀ (cs : List Call) (Ts : List (Tree → Prop)) (ks : List Tree), (∀ T ∈ Ts, ∀ t, T t) →
    KidsT cs Ts ks
  | c :: cs, T :: Ts, k :: ks, h => ⟨fun _ => h T List.mem_cons_self k,
      kidsT_true cs Ts ks fun T' hT' => h T' (List.mem_cons_of_mem _ hT')⟩
  | [], _, _, _ => by simp [KidsT]
  | _ :: _, [], _, _ => by simp [KidsT]
  | _ :: _, _ :: _, [], _ => by simp [KidsT]

/-- A statement hinting nothing to the heap. -/
def noHeapHintC : Stmt → Bool
  | .atom (.hint h) => ((hintDest? h).bind destHeap?).isNone
  | _ => true

theorem heapHintAddrs_nil_of {σ : Val} {pre : List Stmt} (h : pre.all noHeapHintC = true) :
    heapHintAddrs σ (pre.flatMap (slEvs σ)) = [] := by
  refine List.eq_nil_iff_forall_not_mem.mpr fun A hA => ?_
  obtain ⟨ev, he, hA⟩ := List.mem_flatMap.mp hA
  obtain ⟨s, hs, he⟩ := List.mem_flatMap.mp he
  have hk := List.all_eq_true.mp h s hs
  cases s with
  | atom a =>
    simp only [slEvs, List.mem_singleton] at he
    subst he
    cases a with
    | hint x =>
      obtain ⟨p, off, len, hd, -⟩ := hintAddrs_atom_hint hA
      simp [noHeapHintC, hd] at hk
    | _ => simp [Ev.hintAddrs] at hA
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

set_option maxRecDepth 100000 in
theorem chainFlat_noHeapHint : chainFlat.all noHeapHintC = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem big_facts : loopShapeF (coreProgram.getD idx% «claim_list_chain_loop0» default) name% «claim_list_chain_loop0» = true ∧
    coreProgram.loop name% «claim_list_chain_loop0» = true ∧
    (coreProgram.getD idx% «claim_list_chain_loop0» default).params = [.n 0, .n 1, .n 2, .n 3] ∧
    (loopPre (coreProgram.getD idx% «claim_list_chain_loop0» default)).all loopPlainHB = true ∧
    (loopPre (coreProgram.getD idx% «claim_list_chain_loop0» default)).all
      (argStmtOk [(.n 9, 26), (.n (val% «claim_list_chain_loop0» "blk"), 4 * 136)]) = true ∧
    monoIs (atomsIn (loopPre (coreProgram.getD idx% «claim_list_chain_loop0» default))) (.n 9) (.n 2) (.n 0) 13 = true ∧
    monoIs (atomsIn (loopPre (coreProgram.getD idx% «claim_list_chain_loop0» default)))
      (.n (val% «claim_list_chain_loop0» "blk")) (.n 3) (.n 0) (4 * 136) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem grp_facts : loopShapeF (coreProgram.getD idx% «claim_list_chain_loop1» default) name% «claim_list_chain_loop1» = true ∧
    coreProgram.loop name% «claim_list_chain_loop1» = true ∧
    (coreProgram.getD idx% «claim_list_chain_loop1» default).params = [.n 0, .n 1, .n 2, .n 3] ∧
    (loopPre (coreProgram.getD idx% «claim_list_chain_loop1» default)).all loopPlainHB = true ∧
    (loopPre (coreProgram.getD idx% «claim_list_chain_loop1» default)).all
      (argStmtOk [(.n 9, 26), (.n (val% «claim_list_chain_loop1» "blk"), 4 * 17)]) = true ∧
    monoIs (atomsIn (loopPre (coreProgram.getD idx% «claim_list_chain_loop1» default))) (.n 9) (.n 2) (.n 0) 13 = true ∧
    monoIs (atomsIn (loopPre (coreProgram.getD idx% «claim_list_chain_loop1» default)))
      (.n (val% «claim_list_chain_loop1» "blk")) (.n 3) (.n 0) (4 * 17) = true := by
  decide +kernel

/-! ## `claim_list_chain` -/

/-- `claim_list_chain`'s arguments on `n` claims at `e`. -/
def chArgs (e n : ℕ) : List E := [ptrAt e, gen ^ n, gen ^ (n / 136), gen ^ (n % 136 / 17), gen ^ (n % 17)]

/-- `claim_list_chain`'s end at `(fp, c)` on `n` claims: its buffer, its loops' blocks, `claim_list_tail`
and its callee. -/
def chEnd (fs : String → ℕ) (al : String → Bool) (n c : ℕ) : ℕ :=
  let f2 := allocBase (al "claim_list_tail")
    (allocBase (al name% «claim_list_chain_loop1»)
      (allocBase (al name% «claim_list_chain_loop0») (c + 13 * (n / 136 + n % 136 / 17 + 1)) +
        lpBlk fs name% «claim_list_chain_loop0» (n / 136)) + lpBlk fs name% «claim_list_chain_loop1» (n % 136 / 17))
  allocBase (al (clNames.getD (n % 17) "")) (f2 + fs "claim_list_tail") + fs (clNames.getD (n % 17) "")

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- **`claim_list_chain` completes placed** on `n < 2^19` claims' cells at `e` in the region `R`: its
chain buffer at `c`, the states after each frame, its callees after it, its tree of honest shape. -/
theorem chain_callAtA (hwf : coreProgram.Wf) {k : ℕ} {e n : ℕ} {cells : List E} (hn : n < 2 ^ 19)
    (hl : cells.length = 4 * n) {R : ℕ → Prop} (hR : ∀ i, e ≤ i → i < e + 4 * n → R i) {Pre : Reader → Prop}
    (hP : ∀ rd, Pre rd → ReadsAt rd (ptrAt e) cells)
    (hdef : ∀ rd, LowDef k rd → Pre rd → ∀ i, (i = n / 136 ∨ i = n % 136 / 17 ∨ i = n % 17 ∨ i = n) →
      ∃ t, LoadHolds rd (gen ^ i) 0 t)
    {fp c : ℕ} (hfc : fp + fs "claim_list_chain" ≤ c) :
    CallAtA fs al cert k "claim_list_chain" (chArgs e n) (digestCells (keccak256 (cellsBytes cells))) R
      (fun _ => False) (fun _ => True) Pre (fun _ t => chHonest n t) (fs "claim_list_chain") fp c (chEnd fs al n c) := by
  set a := n / 136 with ha
  set b := n % 136 / 17 with hb
  set r := n % 17 with hr
  have hnm : n = 136 * a + 17 * b + r := by omega
  have hb8 : b < 8 := by omega
  have hr17 : r < 17 := by omega
  set chain : E := ptrAt c with hchain
  set Wo : Words := [(c, chainCells cells a b)] with hWo
  set D := keccak256 (cellsBytes cells) with hD
  have hlc : (chainCells cells a b).length = 13 * (a + b + 1) := length_chainCells cells a b
  set cur0 := c + 13 * (a + b + 1) with hcur0
  set f0 := allocBase (al name% «claim_list_chain_loop0») cur0 with hf0
  set cur1 := f0 + lpBlk fs name% «claim_list_chain_loop0» a with hcur1
  set f1 := allocBase (al name% «claim_list_chain_loop1») cur1 with hf1
  set cur2 := f1 + lpBlk fs name% «claim_list_chain_loop1» b with hcur2
  set f2 := allocBase (al "claim_list_tail") cur2 with hf2
  have hend : chEnd fs al n c = allocBase (al (clNames.getD r "")) (f2 + fs "claim_list_tail") +
      fs (clNames.getD r "") := rfl
  have h0le := le_allocBase (al name% «claim_list_chain_loop0») cur0
  have h1le := le_allocBase (al name% «claim_list_chain_loop1») cur1
  have h2le := le_allocBase (al "claim_list_tail") cur2
  have h3le := le_allocBase (al (clNames.getD r "")) (f2 + fs "claim_list_tail")
  have hce : c + 13 * (a + b + 1) ≤ chEnd fs al n c := by rw [hend]; omega
  have hWoIn : WordsInA Wo (fp + 2) (fp + fs "claim_list_chain") c (c + 13 * (a + b + 1)) :=
    ⟨fun q hq => by
      simp only [hWo, List.mem_singleton] at hq
      subst hq
      exact Or.inr ⟨le_rfl, by rw [hlc]⟩, List.pairwise_singleton _ _⟩
  -- the memory facts
  have hmem : ∀ rd, Pre rd → HoldsWords rd Wo → ReadsAt rd chain (chainCells cells a b) ∧
      ClaimChainMem rd chain (ptrAt e) n ∧ StateAt rd chain 0 zeroState := by
    intro rd hp hw
    have hch : ReadsAt rd chain (chainCells cells a b) := hw _ List.mem_cons_self
    refine ⟨hch, claimChainMem_of_reads hl (hP rd hp) hch, ?_⟩
    have := state_of_reads hch (Nat.zero_le (a + b))
    rw [Nat.mul_zero, pow_zero, mul_one, show clU a 0 = 0 by simp [clU]] at this
    exact this
  by_cases hex : ∃ rd0, LowDef k rd0 ∧ Pre rd0 ∧ HoldsWords rd0 Wo
  swap
  · refine ⟨Wo, ⟨fun q hq => ?_, List.pairwise_singleton _ _⟩, by omega, fun _ _ => trivial,
      fun rd hl hw hp => absurd ⟨rd, hl, hp, hw⟩ hex⟩
    simp only [hWo, List.mem_singleton] at hq
    subst hq
    exact Or.inr ⟨le_rfl, by rw [hlc]; omega⟩
  obtain ⟨rd0, hl0, hp0, hw0⟩ := hex
  have hV0 := chain_core (rd := rd0) (entries := ptrAt e) (n := n) D (hmem rd0 hp0 hw0).2.2
    (hdef rd0 hl0 hp0)
  set σ0 := chσ rd0 (ptrAt e) n chain D with hσ0
  set es := chP1.flatMap (slEvs σ0) ++ .call "claim_list_tail" [.n (val% «claim_list_chain» "last"),
      .n (val% «claim_list_chain» "d0~9"), .n (val% «claim_list_chain» "rest")]
      [.n (val% «claim_list_chain» "d0"), .n (val% «claim_list_chain» "d1")] :: chPost.flatMap (slEvs σ0) with hes
  set vs : List V := [.n (val% «claim_list_chain» "s13#0"), .n (val% «claim_list_chain» "s13#0[1]")]
  obtain ⟨hpd, hpa, hpad, hpc⟩ := straight_parts σ0 _ chP1_straight
  obtain ⟨hqd, hqa, hqad, hqc⟩ := straight_parts σ0 _ chPost_straight
  -- what every valuation with `ChVals` gives
  have hguards : ∀ rd σ, ChVals rd σ (ptrAt e) n chain D → chP1.flatMap (slEvs σ) = chP1.flatMap (slEvs σ0) := by
    intro rd σ hV
    refine slEvs_congr chP1 fun c' f' a' hm => ?_
    have hk := List.all_eq_true.mp chP1_kinds _ hm
    simp only [isAtomS, Bool.false_or, Bool.or_eq_true] at hk
    rcases hk with hk | hk
    · have := stmtEqb_sound hk
      simp only [clBigS, Stmt.callIf.injEq] at this
      obtain ⟨rfl, -, -⟩ := this
      rw [hV.v49, hV0.v49]
    · have := stmtEqb_sound hk
      simp only [clGrpS, Stmt.callIf.injEq] at this
      obtain ⟨rfl, -, -⟩ := this
      rw [hV.v69, hV0.v69]
  have hpost : ∀ σ : Val, chPost.flatMap (slEvs σ) = chPost.flatMap (slEvs σ0) := by
    intro σ
    refine slEvs_congr chPost fun c' f' a' hm => absurd ?_ (List.not_mem_nil (a := (some c', f', a', ([] : List V))))
    rw [← chPost_parts.2.2.1]
    exact List.mem_filterMap.mpr ⟨_, hm, rfl⟩
  have hwalk : ∀ rd σ, ChVals rd σ (ptrAt e) n chain D → walk σ (Fn.body fn% «claim_list_chain») = .ret es vs := by
    intro rd σ hV
    rw [chain_body, ← List.cons_append, ← List.append_assoc, walk_straight σ _ _ (by
      rw [List.all_append, chP1_straight, List.all_cons, chPost_straight]; rfl), List.flatMap_append,
      List.flatMap_cons, hguards rd σ hV, hpost σ]
    rfl
  have hal : ∀ rd σ, ChVals rd σ (ptrAt e) n chain D → allocs σ es = [13 * (a + b + 1)] := by
    intro rd σ hV
    obtain ⟨-, hpa', -, -⟩ := straight_parts σ _ chP1_straight
    obtain ⟨-, hqa', -, -⟩ := straight_parts σ _ chPost_straight
    rw [hes, es3_allocs, ← hguards rd σ hV, ← hpost σ, hpa', hqa', chP1_allocs, chPost_parts.1]
    simp only [List.map_cons, List.map_nil, Sum.elim_inr, hV.v33, List.append_nil]
    rw [logG_gen_pow (show 13 * (n / 136 + n % 136 / 17 + 1) < 2 ^ 64 - 1 by omega)]
  have hal0 := hal rd0 σ0 hV0
  have hcalls : calls es = chCalls n σ0 := by
    rw [hes, es3_calls, hpc, hqc, chP1_calls, chPost_parts.2.2.1]
    have h49 : decide (σ0 (.n (val% «claim_list_chain» "s2#1")) ≠ 0) = decide (a ≠ 0) := by
      rw [hV0.v49]; exact decide_eq_decide.mpr (one_add_gen_ne (by omega))
    have h69 : decide (σ0 (.n (val% «claim_list_chain» "s5#1")) ≠ 0) = decide (b ≠ 0) := by
      rw [hV0.v69]; exact decide_eq_decide.mpr (one_add_gen_ne (by omega))
    simp only [List.map_cons, List.map_nil, mkCall, h49, h69, List.cons_append, List.nil_append, chCalls]
    rfl
  have hown' : ∀ i, c ≤ i → i < c + 13 * (a + b + 1) →
      ownData cert fp c "claim_list_chain" [13 * (a + b + 1)] es i := fun i h1 h2 =>
    Or.inl ⟨(13 * (a + b + 1), c), by simp [bases], h1, h2⟩
  have hown : ∀ i, c ≤ i → i < c + 13 * (a + b + 1) →
      ownData cert fp c "claim_list_chain" (allocs σ0 es) es i := fun i h1 h2 => by
    rw [hal0]; exact hown' i h1 h2
  have hσargs0 : [σ0 (.n (val% «claim_list_chain» "s2#2")), σ0 (.n (val% «claim_list_chain» "bigs")),
      σ0 (.n (val% «claim_list_chain» "chain")), σ0 (.n (val% «claim_list_chain» "entries_ptr"))] =
      [1, gen ^ a, ptrAt c, ptrAt e] := by rw [hV0.v50, hV0.v23, hV0.v34, hV0.v0]
  have hσargs1 : [σ0 (.n (val% «claim_list_chain» "s5#2")), σ0 (.n (val% «claim_list_chain» "groups")),
      σ0 (.n (val% «claim_list_chain» "mid")), σ0 (.n (val% «claim_list_chain» "mid_entries"))] =
      [1, gen ^ b, ptrAt (c + 13 * a), ptrAt (e + 544 * a)] := by
    rw [hV0.v70, hV0.v24, hV0.v56, hV0.v67, ptrAt_mul_gpow, ptrAt_mul_gpow]
  have hσargs2 : [σ0 (.n (val% «claim_list_chain» "last")), σ0 (.n (val% «claim_list_chain» "d0~9")),
      σ0 (.n (val% «claim_list_chain» "rest"))] = [ptrAt (c + 13 * (a + b)), ptrAt (e + (544 * a + 68 * b)), gen ^ r] := by
    rw [hV0.v76, hV0.v84, hV0.v25, ptrAt_mul_gpow, ptrAt_mul_gpow]
  have hσrets : [σ0 (.n (val% «claim_list_chain» "d0")), σ0 (.n (val% «claim_list_chain» "d1"))] =
      [(digestHalves D).1, (digestHalves D).2] := by rw [hV0.v85, hV0.v86]
  obtain ⟨hf0, hl0', hpar0, hpl0, hargs0, hm90, hmE0⟩ := big_facts
  obtain ⟨hf1, hl1', hpar1, hpl1, hargs1, hm91, hmE1⟩ := grp_facts
  refine callAtA_nodeRd ch_loop hfc ⟨σ0, fn% «claim_list_chain», es, vs, Wo,
    [fun _ _ => True, fun _ _ => True, fun _ _ => True], fun rd => HoldsWords rd Wo, fun _ => False,
    find_claim_list_chain, by rw [hal0]; simpa using hWoIn, fun i hi => hi.elim, ?_, fun _ _ => trivial, ?_⟩
  · -- the callees
    rw [hcalls, hal0, List.sum_cons, List.sum_nil, Nat.add_zero, chCalls]
    refine kidsAtF_loop (M := a) (fun ha0 => ?_) (fun ha0 => ?_) (kidsAtF_loop (M := b) (fun hb0 => ?_) (fun hb0 => ?_) ?_)
    · simp only [List.map_cons, List.map_nil]
      rw [hσargs0]
      exact grpL_callAtA (M := a) (cb := c) (eb := e) (find_of_idx big_idx) hf0 hl0' hpar0 hpl0 hargs0 hm90 hmE0
        (by decide) (by omega) (fun j hj i hi => Or.inr (hown' _ (by omega) (by omega)))
        (fun j hj i hi => Or.inl (hR _ (by omega) (by omega)))
        (fun j hj rd _ hp => cl_bigBlocks hl (hP rd hp.1) (hmem rd hp.1 hp.2).2.1 j hj) ha0 _ _ le_rfl
    · refine ⟨B1.Val.ofArgs [1, gen ^ a, ptrAt c, ptrAt e], ⟨coreProgram.getD idx% «claim_list_chain_loop0» default,
        find_of_idx big_idx, ?_⟩⟩
      simp only [List.map_cons, List.map_nil]
      rw [hσargs0, hpar0]
      simp [Tree.val, B1.ofArgs_n]
    · simp only [List.map_cons, List.map_nil]
      rw [hσargs1]
      exact grpL_callAtA (M := b) (cb := c + 13 * a) (eb := e + 544 * a) (find_of_idx grp_idx) hf1 hl1' hpar1
        hpl1 hargs1 hm91 hmE1 (by decide) (by omega) (fun j hj i hi => Or.inr (hown' _ (by omega) (by omega)))
        (fun j hj i hi => Or.inl (hR _ (by omega) (by omega)))
        (fun j hj rd _ hp => by
          have := cl_grpBlocks hl (hP rd hp.1) (hmem rd hp.1 hp.2).2.1 j hj
          rwa [ptrAt_mul_gpow, ptrAt_mul_gpow] at this) hb0 _ _ le_rfl
    · refine ⟨B1.Val.ofArgs [1, gen ^ b, ptrAt (c + 13 * a), ptrAt (e + 544 * a)],
        ⟨coreProgram.getD idx% «claim_list_chain_loop1» default, find_of_idx grp_idx, ?_⟩⟩
      simp only [List.map_cons, List.map_nil]
      rw [hσargs1, hpar1]
      simp [Tree.val, B1.ofArgs_n]
    · rw [KidsAtF]
      simp only [↓reduceIte, List.map_cons, List.map_nil, List.headD_cons, List.tail_cons]
      rw [hσargs2, hσrets]
      refine ⟨fs "claim_list_tail", _, fun i => R i ∨ ownData cert fp c "claim_list_chain" [13 * (a + b + 1)] es i,
        fun _ => False, fun _ => True, fun i hi => Or.inl hi,
        tail_callAtA hwf hr17 (fun rd _ hp => ?_) (fun i hi => Or.inr (hown' _ (by omega) (by omega)))
          (fun i hi => Or.inl (hR _ (by omega) (by omega))) le_rfl, ?_⟩
      · have hr' := hP rd hp.1
        have hS := state_of_reads (hmem rd hp.1 hp.2).1 (le_refl (a + b))
        rw [clU_last] at hS
        have hpre : (cellsBytes (cells.take (68 * (8 * a + b)))).length = rate * (8 * (8 * a + b)) := by
          rw [length_cellsBytes, List.length_take, Nat.min_eq_left (by omega)]
          show 16 * (68 * (8 * a + b)) = 136 * (8 * (8 * a + b)); omega
        have := claimLast_complete hr17 hpre hS (cells := cells.drop (68 * (8 * a + b))) (by simp; omega)
          (readsAt_drop' hr' _)
        rw [← cellsBytes_append, List.take_append_drop, ptrAt_mul_gpow, ptrAt_mul_gpow,
          show 68 * (8 * a + b) = 544 * a + 68 * b by ring] at this
        exact this
      · rw [KidsAtF, hend]
        exact ⟨rfl, fun _ h => h.1, fun _ h => h.elim⟩
  · -- on each memory
    intro rd hl hp hw
    obtain ⟨hch, hcm, hz⟩ := hmem rd hp hw
    have hV := chain_core (rd := rd) (entries := ptrAt e) (n := n) D hz (hdef rd hl hp)
    set σ := chσ rd (ptrAt e) n chain D with hσ
    have hes' : es = chainFlat.flatMap (slEvs σ) := by
      rw [hes, ← hguards rd σ hV, ← hpost σ, chainFlat_split, List.flatMap_append, List.flatMap_cons]
      rfl
    obtain ⟨hpd', -, hpad', -⟩ := straight_parts σ _ chP1_straight
    obtain ⟨hqd', -, hqad', -⟩ := straight_parts σ _ chPost_straight
    have hmE : ∀ s ∈ chP1 ++ chPost, ∀ x, s = .atom x → x.Holds rd σ := by
      intro s hs x rfl
      refine hV.atoms x (cl_mem_atoms ?_)
      rw [chainFlat_split]
      simp only [List.mem_append, List.mem_cons] at hs ⊢
      rcases hs with hs | hs <;> simp [hs]
    refine ⟨σ, ?_, hwalk rd σ hV, ?_, by rw [hal rd σ hV, hal0], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [ch_param, hV.v0, hV.v1, hV.v23, hV.v24, hV.v25]; rfl
    · show [σ (.n (val% «claim_list_chain» "s13#0")), σ (.n (val% «claim_list_chain» "s13#0[1]"))] = _
      rw [hV.v87, hV.v88]; rfl
    · rw [hal0]
      refine ⟨?_, fun q hq => ?_⟩
      · rw [hes, ← hguards rd σ hV, ← hpost σ, es3_allocDsts, hpd', hqd', chP1_allocs, chPost_parts.1]
        simp [bases, hV.v34, hchain]
      · rw [hes, ← hguards rd σ hV, ← hpost σ, es3_addrs, hpad', hqad', chP1_addrs, chPost_parts.2.1] at hq
        simp at hq
    · rw [hcalls]
      intro cl hcl
      simp only [chCalls, List.mem_cons, List.not_mem_nil, or_false] at hcl
      rcases hcl with rfl | rfl | rfl
      · simp [hV.v50, hV0.v50, hV.v23, hV0.v23, hV.v34, hV0.v34, hV.v0, hV0.v0]
      · simp [hV.v70, hV0.v70, hV.v24, hV0.v24, hV.v56, hV0.v56, hV.v67, hV0.v67]
      · simp [hV.v76, hV0.v76, hV.v84, hV0.v84, hV.v25, hV0.v25, hV.v85, hV0.v85, hV.v86, hV0.v86]
    · intro A hA
      rw [hes, ← hguards rd σ hV, ← hpost σ, es3_loads, Memory.loadAddrs_straight σ _ chP1_straight,
        Memory.loadAddrs_straight σ _ chPost_straight, chP1_loads, chPost_parts.2.2.2] at hA
      simp only [List.map_nil, List.append_nil, List.map_map, List.mem_map, List.mem_range,
        Function.comp] at hA
      obtain ⟨c', hc13, rfl⟩ := hA
      refine ⟨c + c', by rw [hV.v34]; exact Main.addr_ofK _ _, Or.inl (hown _ (by omega) (by omega))⟩
    · intro A hA
      rw [hes', heapHintAddrs_nil_of chainFlat_noHeapHint] at hA
      exact absurd hA List.not_mem_nil
    · intro ev hev
      rw [hes, ← hguards rd σ hV, ← hpost σ] at hev
      rcases List.mem_append.mp hev with he | he
      · refine events_straight (fun s hs => ?_) ev he
        have hk := List.all_eq_true.mp chP1_kinds s hs
        simp only [Bool.or_eq_true] at hk
        rcases hk with (hk | hk) | hk
        · exact sOk_atomS hk (hmE s (by simp [hs]))
        · rw [stmtEqb_sound hk]
          show IsInK (σ (.n (val% «claim_list_chain» "s2#1")))
          rw [hV.v49, ← pow_zero gen]; exact gen_pow_add_isInK _ _
        · rw [stmtEqb_sound hk]
          show IsInK (σ (.n (val% «claim_list_chain» "s5#1")))
          rw [hV.v69, ← pow_zero gen]; exact gen_pow_add_isInK _ _
      rcases List.mem_cons.mp he with rfl | he
      · trivial
      · refine events_straight (fun s hs => ?_) ev he
        rw [chPost_eq] at hs
        rcases List.mem_append.mp hs with hs' | hs'
        · exact sOk_atomS (List.all_eq_true.mp chChk_atoms s hs') (hmE s (by rw [chPost_eq]; simp [hs']))
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs'
          rcases hs' with rfl | rfl <;> exact sOk_atomS rfl (hmE _ (by rw [chPost_eq]; simp))
    · intro ts _ _
      refine ⟨σ, ts, by rw [hal0]; rfl, ⟨hV.v23, hV.v24, hV.v25, hV.v33, hV.v50, hV.v70⟩,
        fun fn es' vs' hf hw' => ?_, by simp [chCalls, chTs], kidsT_true _ _ _ (by simp [chTs])⟩
      rw [find_claim_list_chain] at hf
      cases hf
      rw [hwalk rd σ hV] at hw'
      obtain ⟨he', -⟩ := Out.ret.inj hw'
      rw [← he', hcalls]
      simp only [chCalls]

end
end LeanVM.Guest.Complete
