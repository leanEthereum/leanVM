module

public import LeanVM.Guest.Complete.Agg.W2V
public import LeanVM.Guest.B1.Bits.GrindFwd

/-!
# `aggregate_claims`' second run, the inlined grind

`grind_check(nxt[1], tabs, 3)` inlined (`aggGrindA`, `gcInlineT 3 91 (.n 79) (.n 5)`) on the honest
valuation. Its evaluation memory need not hold the low words its range checks read, so the grind's
completeness (`gcInline_holds_of_good`) runs on `rdTot (aRd0 …)`, the evaluation memory made total
(`0` where undefined), which reads as it does (`good_rdTot`). The proof of work passes by the
batching's grind (`batched_of_run`), the windows are the oracle's (`aOrc`), the tables the window
table's (`aTab`, past `main`'s words and before the own words).

`w2_grindT`: the grind's pure facts, its loads in the window table (`mainR`), and on every memory with
`LowDef k`, `11 ≤ k`, `MainPreA` and the own words, its range checks' and loads' words.
-/

namespace LeanVM.Guest.Complete.Agg

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Guest.Value.Keccak LeanVM.Guest.B1.Main LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.VsC
open LeanVM.Guest.Complete
open LeanVM.Node LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

attribute [local instance high] LeanVM.Guest.Core.instDecidableEqAtom

/-! ## A total reader -/

/-- `rd`, `0` where it is undefined. -/
def rdTot (rd : Reader) : Reader := fun A => some ((rd A).getD 0)

theorem good_rdTot {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val} {a : Atom} (h : Good rd S w σ a) :
    Good (rdTot rd) S w σ a := by
  cases a <;> exact h

theorem hrc_rdTot (rd : Reader) : ∀ v ≤ 11, ∀ e < 2 ^ v, ∃ y t1 t2 : E, LoadHolds (rdTot rd) (gen ^ e) 0 t1 ∧
    wBound v = gen ^ e * y ∧ LoadHolds (rdTot rd) y 0 t2 := fun v hv e he =>
  ⟨gen ^ (2 ^ v - 1 - e), _, _, ⟨gen_pow_isInK e, rfl⟩,
    by rw [wBound_eq hv, ← pow_add, show e + (2 ^ v - 1 - e) = 2 ^ v - 1 by omega], ⟨gen_pow_isInK _, rfl⟩⟩

/-! ## The grind's shape -/

/-- The grind's table reads `(d, p, x)`: `d` read through `p = tabs·x`. -/
def gLd : List (ℕ × ℕ × ℕ) :=
  [(102, 101, 96), (110, 109, 95), (119, 118, 94), (128, 127, 93), (137, 136, 92), (146, 145, 91)]

/-- The grind's range checks `(x, y, t1, t2, k, K)`: `k` its own value `K`. -/
def gRc : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) :=
  [(96, 98, 99, 100, 97, 8), (95, 104, 105, 106, 103, 14), (94, 113, 114, 115, 112, 23),
    (93, 122, 123, 124, 121, 32), (92, 131, 132, 133, 130, 41), (91, 140, 141, 142, 139, 50)]

/-- A product with its factors before it. -/
def fwdB : Atom → Bool
  | .mul d x y => decide (x.idx < d.idx) && decide (y.idx < d.idx)
  | _ => true

set_option maxRecDepth 400000 in
theorem grind_split : (∀ x ∈ aggGrindA, isNL x = true ∨
      (∃ q ∈ gLd, x = .load (.n q.1) (.n q.2.1) 0) ∨
      ∃ q ∈ gRc, x = .rangeCheck (.n q.1) (.n q.2.1) (.n q.2.2.1) (.n q.2.2.2.1) (.n q.2.2.2.2.1)) ∧
    aggGrindA.all fwdB = true ∧
    (∀ q ∈ gLd, Atom.mul (.n q.2.1) (.n 5) (.n q.2.2) ∈ aggGrindA ∧ Atom.load (.n q.1) (.n q.2.1) 0 ∉ storesOf 6 aggP) ∧
    Atom.hint (.windowsExp (.n 79) 3 11 5 (.stack [.n 91, .n 92, .n 93, .n 94, .n 95])) ∈ aggGrindA ∧
    Atom.hint (.windowsExp (.n 79) 58 6 1 (.stack [.n 96])) ∈ aggGrindA ∧
    (∀ a ∈ storesOf 6 aggP, loadInto 91 (91 + (gcLen 3 - 2)) a = false) ∧ 3 ∈ grindBitsDeployed := by
  decide +kernel

theorem gcW_3 : gcW 3 = 5 := rfl
theorem gcTop_3 : gcTop 3 = 6 := rfl

/-- **The windows are powers below the table's length.** -/
theorem gcWin_pow (W : E) {j : ℕ} (hj : j ≤ 5) : ∃ e, gcWin 3 W j = gen ^ e ∧ (j < 5 → e < 2 ^ 11) ∧ (j = 5 → e < 64) := by
  by_cases h5 : j = 5
  · subst h5
    refine ⟨gcV 3 W 0, ?_, fun h => absurd h (by norm_num), fun _ => ?_⟩
    · unfold gcWin; exact gv_top
    · have := gcV_zero_lt (b := 3) (by rfl) W
      rwa [gcTop_3] at this
  · refine ⟨gcV 3 W (5 - j) % 2 ^ 11, ?_, fun _ => Nat.mod_lt _ (by positivity), fun h => absurd h h5⟩
    unfold gcWin
    rw [show 2 + j = gcW 3 + 2 - (5 - j) by rw [gcW_3]; omega]
    exact gv_win (by omega) (by rw [gcW_3]; omega)

/-- **A range check of two powers** reads defined words on a memory defined low. -/
theorem memT_rc_pow {rd : Reader} {σ : Val} {x y t1 t2 kk : V} {e n k : ℕ}
    (hx : σ x = gen ^ e) (hk : σ kk = gen ^ n) (hxy : σ kk = σ x * σ y) (hen : e ≤ n) (hn : n < 2 ^ k)
    (hl : LowDef k rd) : MemT rd σ (.rangeCheck x y t1 t2 kk) := by
  have hy : σ y = gen ^ (n - e) := by
    have : gen ^ e * σ y = gen ^ e * gen ^ (n - e) := by
      calc gen ^ e * σ y = σ x * σ y := by rw [hx]
        _ = gen ^ n := hxy.symm.trans hk
        _ = gen ^ e * gen ^ (n - e) := by rw [← pow_add, Nat.add_sub_cancel' hen]
    exact mul_left_cancel₀ (pow_ne_zero _ Value.gen_ne_zero) this
  exact ⟨by rw [hx, gen_pow_addr]; exact hl e (by omega), by rw [hy, gen_pow_addr]; exact hl _ (by omega)⟩

/-- **An atom's pure facts from its relation**, its products forward and a range check's word
nonzero. -/
theorem pureT_of_holds {rd : Reader} {σ : Val} {a : Atom} (h : a.Holds rd σ) (hf : fwdB a = true)
    (hrc : ∀ x y t1 t2 k, a = .rangeCheck x y t1 t2 k → σ x ≠ 0) : PureT σ a := by
  cases a with
  | mul d x y =>
    simp only [fwdB, Bool.and_eq_true, decide_eq_true_eq] at hf
    simp [PureT, hf]
  | assertEq x y => exact h
  | assertInK x y => exact h
  | rangeCheck x y t1 t2 k => exact ⟨h.1.1, h.2.2.1, fun _ => hrc x y t1 t2 k rfl⟩
  | touch t p => exact h.1
  | _ => trivial

theorem valAt_append_not : ∀ {W W' : Words} {i : ℕ}, ¬ InW W i → valAt (W ++ W') i = valAt W' i
  | [], _, _, _ => rfl
  | q :: W, W', i, h => by
    have hq : ¬ (q.1 ≤ i ∧ i < q.1 + q.2.length) := fun hq => h ⟨q, List.mem_cons_self, hq⟩
    simp only [List.cons_append, valAt, hq, ↓reduceIte]
    exact valAt_append_not fun ⟨q', hq', h'⟩ => h ⟨q', List.mem_cons_of_mem _ hq', h'⟩

section
variable {al : String → Bool} {s : NodeStatement} {w : NodeWitness} {cover : List E} {c : ℕ}

/-- **The evaluation memory holds the window table.** -/
theorem aRd0_tab (hl : (aLists s w).map List.length = aBufs w.children.length) (hc : c < 2 ^ 62)
    (hlo : mLo al (mainCounts s w) ≤ c)
    (hmw : (mainLists s w cover).map List.length = (mainCounts s w).bufs) {n : ℕ} (hn : n < 2 ^ winTabBits) :
    aRd0 al s w cover c (addressOfIndex (mGS al (mainCounts s w) + winTabAt + n)) = some (eOfNat n) ∧
      InW (aAll al s w cover c) (mGS al (mainCounts s w) + winTabAt + n) := by
  have hT : mGS al (mainCounts s w) + winTabAt + n < mLo al (mainCounts s w) := by
    unfold mLo expTabLen; omega
  have hin : InW (aAll al s w cover c) (mGS al (mainCounts s w) + winTabAt + n) :=
    inW_append_right ⟨aTab al s w, List.mem_singleton_self _, by simp [aTab]; omega⟩
  refine ⟨?_, hin⟩
  have hnot : ¬ InW (aWo s w c ++ mainWords s w cover) (mGS al (mainCounts s w) + winTabAt + n) := by
    rintro ⟨q, hq, h1, h2⟩
    rcases List.mem_append.mp hq with hq | hq
    · rcases (aWo_in hl c 0 0).1 q hq with h | h <;> omega
    · have := (mainWords_in hmw).1 q hq
      have hm : mTop (mainCounts s w) ≤ mGS al (mainCounts s w) := by
        unfold mGS; exact le_trans (le_allocBase _ _) (Nat.le_add_right _ _)
      omega
  rw [aRd0, rdW_inW hin (by omega), aAll, valAt_append_not hnot]
  simp [valAt, aTab, show mGS al (mainCounts s w) + winTabAt ≤ mGS al (mainCounts s w) + winTabAt + n by omega,
    show n < 2 ^ winTabBits from hn]

/-- **The grind on the honest valuation**: its pure facts, its table reads in `main`'s region, and on
every memory defined low with `main`'s words and the own words, its range checks' and reads' words. -/
theorem w2_grindT (hr : NodeRelation guestBytecode guestSeed s w) (hne : w.children ≠ [])
    (hl : (aLists s w).map List.length = aBufs w.children.length) (hc : c < 2 ^ 62) (hn : w.children.length ≤ 16)
    (hlo : mLo al (mainCounts s w) ≤ c) (hmw : (mainLists s w cover).map List.length = (mainCounts s w).bufs)
    {k fp : ℕ} {es : List Memory.Ev} {D : ℕ → Prop} (hk : 11 ≤ k) :
    (∀ x ∈ aggGrindA, PureT (aV al s w cover c) x) ∧
      (∀ x ∈ aggGrindA, ∀ A, Memory.Ev.loadAddr? (aV al s w cover c) (.atom x) = some A →
        ∃ i, A = addressOfIndex i ∧
          (ownData B2C.cert fp c "aggregate_claims" (aBufs w.children.length) es i ∨ mainR al (mainCounts s w) i ∨ D i)) ∧
      ∀ rd, LowDef k rd → MainPreA al s w cover rd → HoldsWords rd (aWo s w c) →
        ∀ x ∈ aggGrindA, MemT rd (aV al s w cover c) x := by
  obtain ⟨hsplit, hfwd, hld, hw1, hw2, hS, hb3⟩ := grind_split
  set W := cellsOfState (aN w) false 1 with hW
  have v79 : aV al s w cover c (.n 79) = W := w2_nonce (al := al) (cover := cover) hl hc hn 1
  have v5 : aV al s w cover c (.n 5) = ptrAt (mGS al (mainCounts s w) + winTabAt) := aV_param (by norm_num)
  have hT : mGS al (mainCounts s w) + winTabAt + 2 ^ winTabBits ≤ mLo al (mainCounts s w) := by
    unfold mLo expTabLen; omega
  -- the windows
  have hwv : ∀ j ≤ 5, aV al s w cover c (.n (91 + j)) = gcWin 3 W j := by
    intro j hj
    by_cases h5 : j = 5
    · subst h5
      have := (aV_good (al := al) (s := s) (w := w) (cover := cover) (c := c) (mem_grind hw2)) (.n 96) (by simp)
      exact this
    · have := (aV_good (al := al) (s := s) (w := w) (cover := cover) (c := c) (mem_grind hw1)) (.n (91 + j))
        (by simp; omega)
      rw [this]
      interval_cases j <;> rfl
  have hwin : ∀ j ≤ gcW 3, aOrc w c (91 + j) = gcWin 3 (aV al s w cover c (.n 79)) j := by
    intro j hj
    rw [gcW_3] at hj
    rw [v79]
    interval_cases j <;> rfl
  -- the tables on the total reader
  have hTab : WinTabs (rdTot (aRd0 al s w cover c)) (aV al s w cover c (.n 5)) := by
    intro n hn'
    rw [v5]
    refine ⟨ofK_isInK _, ?_⟩
    rw [addr_ptr]
    show some ((aRd0 al s w cover c _).getD 0) = _
    rw [(aRd0_tab hl hc hlo hmw hn').1]
    rfl
  have hg : ∀ st ∈ gcInlineT 3 91 (.n 79) (.n 5), GoodS (rdTot (aRd0 al s w cover c)) (storesOf 6 aggP) (aOrc w c) (aV al s w cover c) st := by
    intro st hst
    rw [← w2_grind] at hst
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hst
    exact good_rdTot (aV_good (mem_grind ha))
  have hv := gcInline_vals_of_good hb3 (w := .n 79) (tabs := .n 5) (by decide) (by decide) hg hS
    (hrc_rdTot _) hTab hwin
  -- the proof of work
  have hlow : ((aV al s w cover c (.n 79)).limb 0).lane.toNat % 2 ^ 3 = 0 := by
    have hp := (batched_of_run (aBatched hr hne)).1
    rw [show Batch.batchLambdaGrindBits = 3 by decide] at hp
    rw [v79, hW, aN, aggN]
    exact (grindOk_iff (s := aggAbs (aCs w)) (by norm_num) _).mp (Or.inr hp)
  have hH := gcInline_holds_of_good (C := fun _ _ _ => True) hb3 (w := .n 79) (tabs := .n 5) (by decide) (by decide)
    hg hS (hrc_rdTot _) hTab hwin hlow (next := True) trivial (kret := fun _ => True)
  rw [← w2_grind] at hH
  have hAt : ∀ x ∈ aggGrindA, x.Holds (rdTot (aRd0 al s w cover c)) (aV al s w cover c) := fun x hx =>
    ((holdsList_atoms (fun st hst => by obtain ⟨a, -, rfl⟩ := List.mem_map.mp hst; exact ⟨a, rfl⟩) _ _).mp hH).1 x
      (List.mem_map_of_mem hx)
  -- the range checks
  have hrcv : ∀ q ∈ gRc, ∃ e n, aV al s w cover c (.n q.1) = gen ^ e ∧ aV al s w cover c (.n q.2.2.2.2.1) = gen ^ n ∧
      e ≤ n ∧ n < 2 ^ 11 := by
    have hit : ∀ i, 1 ≤ i → i ≤ 5 → aV al s w cover c (.n (91 + (5 + 9 * i) - 2)) = gen ^ 2047 := fun i h1 h5 => by
      rw [hv (5 + 9 * i) (by omega) (by unfold gcLen; rw [gcW_3]; omega),
        show 5 + 9 * i = gcW 3 + 9 * i + 0 by rw [gcW_3, Nat.add_zero], gv_iter (by omega) (by rw [gcW_3]; omega) (by norm_num)]
      show wBound 11 = _
      rw [wBound_eq (by norm_num)]
      norm_num
    have hw : ∀ j, j < 5 → ∃ e, aV al s w cover c (.n (91 + j)) = gen ^ e ∧ e ≤ 2047 := fun j hj => by
      obtain ⟨e, he, he4, -⟩ := gcWin_pow W (j := j) (by omega)
      exact ⟨e, (hwv j (by omega)).trans he, by have := he4 hj; omega⟩
    intro q hq
    simp only [gRc, List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨e, he, -, he5⟩ := gcWin_pow W (j := 5) le_rfl
      refine ⟨e, 63, (hwv 5 le_rfl).trans he, ?_, by have := he5 rfl; omega, by norm_num⟩
      have h97 : aV al s w cover c (.n 97) = gcVals (rdTot (aRd0 al s w cover c)) 3 (aV al s w cover c (.n 79))
          (aV al s w cover c (.n 5)) 8 := hv 8 (by norm_num) (by decide)
      rw [h97]
      unfold gcVals
      simp only [gcW_3, gcTop_3]
      norm_num [wBound_eq]
    · obtain ⟨e, he, hle⟩ := hw 4 (by norm_num)
      exact ⟨e, 2047, he, hit 1 (by norm_num) (by norm_num), hle, by norm_num⟩
    · obtain ⟨e, he, hle⟩ := hw 3 (by norm_num)
      exact ⟨e, 2047, he, hit 2 (by norm_num) (by norm_num), hle, by norm_num⟩
    · obtain ⟨e, he, hle⟩ := hw 2 (by norm_num)
      exact ⟨e, 2047, he, hit 3 (by norm_num) (by norm_num), hle, by norm_num⟩
    · obtain ⟨e, he, hle⟩ := hw 1 (by norm_num)
      exact ⟨e, 2047, he, hit 4 (by norm_num) (by norm_num), hle, by norm_num⟩
    · obtain ⟨e, he, hle⟩ := hw 0 (by norm_num)
      exact ⟨e, 2047, he, hit 5 (by norm_num) (by norm_num), hle, by norm_num⟩
  -- the table reads
  have hldv : ∀ q ∈ gLd, ∃ e < 2 ^ winTabBits, aV al s w cover c (.n q.2.1) = ptrAt (mGS al (mainCounts s w) + winTabAt + e) := by
    intro q hq
    have hq' : 91 ≤ q.2.2 ∧ q.2.2 ≤ 96 := by
      simp only [gLd, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
    obtain ⟨e, he, he4, he5⟩ := gcWin_pow W (j := q.2.2 - 91) (by omega)
    have hm : aV al s w cover c (.n q.2.1) = aV al s w cover c (.n 5) * aV al s w cover c (.n q.2.2) :=
      aGood_mul (rd0 := aRd0 al s w cover c) (o := aOrc w c) (aggArgs_length al (mainCounts s w))
      (mem_grind (hld q hq).1)
      (by simp only [gLd, List.mem_cons, List.mem_nil_iff, or_false] at hq
          rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num)
      (by simp only [gLd, List.mem_cons, List.mem_nil_iff, or_false] at hq
          rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num)
    refine ⟨e, ?_, ?_⟩
    · by_cases h5 : q.2.2 - 91 = 5
      · have := he5 h5; show e < 2 ^ 11; omega
      · exact he4 (by omega)
    · show aV al s w cover c (.n q.2.1) = _
      rw [hm, v5, show q.2.2 = 91 + (q.2.2 - 91) by omega, hwv _ (by omega), he, ptrAt_mul_gen_pow]
  refine ⟨fun x hx => ?_, fun x hx A hA => ?_, fun rd hlow' hP hO x hx => ?_⟩
  · refine pureT_of_holds (hAt x hx) (List.all_eq_true.mp hfwd x hx) fun x' y t1 t2 kk he => ?_
    rcases hsplit x hx with hN | ⟨q, -, rfl⟩ | ⟨q, hq, rfl⟩
    · subst he; simp [isNL] at hN
    · cases he
    · obtain ⟨e, n, hxe, -⟩ := hrcv q hq
      simp only [Atom.rangeCheck.injEq] at he
      rw [← he.1, hxe]
      exact pow_ne_zero _ Value.gen_ne_zero
  · rcases hsplit x hx with hN | ⟨q, hq, rfl⟩ | ⟨q, -, rfl⟩
    · rw [(isNL_spec (rd := fun _ => none) hN).2] at hA; exact absurd hA (by simp)
    · obtain ⟨e, he, hp⟩ := hldv q hq
      simp only [Memory.Ev.loadAddr?, Option.some.injEq] at hA
      rw [← hA, hp, addr_ptr, Nat.add_zero]
      refine ⟨_, rfl, Or.inr (Or.inl (Or.inr ⟨by omega, by unfold expTabLen; omega⟩))⟩
    · simp [Memory.Ev.loadAddr?] at hA
  · rcases hsplit x hx with hN | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · exact (isNL_spec hN).1
    · obtain ⟨e, he, hp⟩ := hldv q hq
      obtain ⟨-, hin⟩ := aRd0_tab hl hc hlo hmw he
      have := aLoad_fresh (al := al) (s := s) (w := w) (cover := cover) (c := c) (off := 0)
        (mem_grind (hx)) (hld q hq).2 hp (by rwa [Nat.add_zero]) (by omega)
      exact this.2 rd (holds_aAll hO hP)
    · obtain ⟨e, n, hxe, hkn, hen, hn11⟩ := hrcv q hq
      have hxy : aV al s w cover c (.n q.2.2.2.2.1) = aV al s w cover c (.n q.1) * aV al s w cover c (.n q.2.1) := (hAt _ hx).2.1
      exact memT_rc_pow hxe hkn hxy hen (lt_of_lt_of_le hn11 (Nat.pow_le_pow_right (by norm_num) hk)) hlow'

end

end
end LeanVM.Guest.Complete.Agg
