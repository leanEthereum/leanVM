/-
  LeanVM.Guest.B1.Opening

  B1 for the stacked WHIR opening's stream gadgets: `opening_final_message` at each of its
  specializations, one generic argument over the message length.
-/

module

public import LeanVM.Guest.B1.FiatShamir

/-!
# `opening_final_message` (TRIAGE #33)

`opening_final_message(fs0, fs1, cursor, out, n)` (G:944-949) reads `n` stream words, absorbing
each (`fs_next`), and stores them at `out`: `readN n` (V:432). Its expansion is `n` blocks of
`fs_next` and a store, `ofmBlock i` at value `4 + 15·i` (the state of block `i` is
`.n (4 + 15·i)`, `.n (5 + 15·i)`, its word `.n (6 + 15·i)`), then `ofmTail n`: `ofmBody n`,
equal by `rfl` to each compiled specialization (`__L4`, `__L8`, `__L16`, `__L32`).
`opening_final_message_iff` is proved once, for every `0 < n < 64`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-! ## Repeated blocks -/

/-- Blocks without a return, one per index below `n`, hold exactly when each does. -/
theorem holdsList_range_flatten (n : ℕ) (blk : ℕ → List Stmt)
    (h : ∀ i, Stmt.noRetList (blk i) = true) (next : Prop) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ ((List.range n).map blk).flatten next kret ↔
      (∀ i < n, Stmt.HoldsList C rd σ (blk i) True kret) ∧ next := by
  rw [holdsList_flatten _ (fun b hb => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hb
    exact h i)]
  simp only [List.mem_map, List.mem_range, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]

/-! ## The template -/

/-- Block `i`: read the word at offset `i`, absorb it, store it at `out`. -/
def ofmBlock (i : ℕ) : List Stmt :=
  fsNextT (.n (4 + 15 * i)) (.n (5 + 15 * i)) (.n 2) i (6 + 15 * i) ++
    [.atom (.load (.n (6 + 15 * i)) (.n 3) i)]

/-- The returns: the state, and the cursor `n` words on. -/
def ofmTail (n : ℕ) : List Stmt :=
  [.atom (.copy (.n (6 + 15 * n)) (.n (4 + 15 * n))), .atom (.copy (.n (7 + 15 * n)) (.n (5 + 15 * n))),
    .atom (.const (.n (8 + 15 * n)) (word (2 ^ n) 0 0)),
    .atom (.mul (.n (9 + 15 * n)) (.n 2) (.n (8 + 15 * n))),
    .atom (.copy (.n (10 + 15 * n)) (.n (9 + 15 * n))),
    .ret [.n (6 + 15 * n), .n (7 + 15 * n), .n (10 + 15 * n)]]

/-- The expansion of `opening_final_message` at `n`. -/
def ofmBody (n : ℕ) : List Stmt :=
  [.atom (.copy (.n 4) (.n 0)), .atom (.copy (.n 5) (.n 1))] ++
    ((List.range n).map ofmBlock).flatten ++ ofmTail n

/-- What block `i` asks of a valuation. -/
def OfmOk (rd : Reader) (σ : Val) (i : ℕ) : Prop :=
  LoadHolds rd (σ (.n 2)) i (σ (.n (6 + 15 * i))) ∧
    (∃ cv, (σ (.n (4 + 15 * i)), σ (.n (5 + 15 * i))) = digestScalars cv ∧
      ∀ k, 2 ≤ k → k < 14 → σ (.n (6 + 15 * i + 1 + k)) = fsVals (σ (.n (6 + 15 * i))) cv 1 k) ∧
    LoadHolds rd (σ (.n 3)) i (σ (.n (6 + 15 * i)))

theorem holds_ofmBlock (i : ℕ) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (ofmBlock i) True kret ↔ OfmOk rd σ i := by
  rw [ofmBlock, holdsList_append, holds_fsNextT]
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, OfmOk]
  tauto

/-! ## The meaning -/

/-- **`opening_final_message(n)`** (G:944-949; TRIAGE #33): from the state of `cv`, the `n` words
`xs` at the cursor are read (`readN n`, V:432, to the state `cv'`) and stored at `out`; the
function returns `cv'`'s cells and the cursor `n` words on. -/
def MeaningOpeningFinalMessage (n : ℕ) (rd : Reader) : List E → List E → Prop
  | [s0, s1, cur, out], rets =>
      ∃ cv xs cv', (s0, s1) = digestScalars cv ∧ xs.length = n ∧ ReadsAt rd cur xs ∧
        ReadsAt rd out xs ∧ RunsTo (Prog.readN n) cv xs xs cv' ∧
        rets = [(digestScalars cv').1, (digestScalars cv').2, cur * gen ^ n]
  | _, _ => False

/-- The states of the chain after each prefix of `xs`. -/
def cvAt (cv : Digest) (xs : List E) : ℕ → Digest
  | 0 => cv
  | i + 1 => absorbCv (cvAt cv xs i) (xs.getD i 0) 1

theorem cvAt_eq (cv : Digest) (xs : List E) (i : ℕ) (hi : i ≤ xs.length) :
    cvAt cv xs i = obsAll cv (xs.take i) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [cvAt, ih (by omega), List.take_add_one]
    simp only [obsAll, List.foldl_append, List.getElem?_eq_getElem (show i < xs.length by omega),
      Option.toList_some, List.foldl_cons, List.foldl_nil, List.getD_eq_getElem?_getD,
      Option.getD_some]
    rfl

/-- The honest valuation, block by block. -/
def ofmSig (base : Val) (cv : Digest) (xs : List E) : ℕ → Val
  | 0 => setl base 4 [(digestScalars cv).1, (digestScalars cv).2]
  | i + 1 => setv (setl (ofmSig base cv xs i) (6 + 15 * i) [xs.getD i 0]) (7 + 15 * i) 14
      (fsVals (xs.getD i 0) (cvAt cv xs i) 1)

theorem ofmSig_lt (base : Val) (cv : Digest) (xs : List E) :
    ∀ (m i k : ℕ), i ≤ m → k < 6 + 15 * i → ofmSig base cv xs m (.n k) = ofmSig base cv xs i (.n k)
  | 0, i, k, h, _ => by rw [show i = 0 by omega]
  | m + 1, i, k, h, hk => by
    rcases Nat.lt_or_ge i (m + 1) with hi | hi
    · rw [ofmSig, set_n_lt (by omega), setl, set_n_lt (by omega)]
      exact ofmSig_lt base cv xs m i k (by omega) hk
    · rw [show i = m + 1 by omega]

theorem ofmSig_base (base : Val) (cv : Digest) (xs : List E) (m k : ℕ) (hk : k < 4) :
    ofmSig base cv xs m (.n k) = base (.n k) := by
  rw [ofmSig_lt base cv xs m 0 k (by omega) (by omega), ofmSig, setl, set_n_lt hk]

/-- The state cells of block `i ≤ m`. -/
theorem ofmSig_state (base : Val) (cv : Digest) (xs : List E) (m i : ℕ) (hi : i ≤ m) :
    ofmSig base cv xs m (.n (4 + 15 * i)) = (digestScalars (cvAt cv xs i)).1 ∧
      ofmSig base cv xs m (.n (5 + 15 * i)) = (digestScalars (cvAt cv xs i)).2 := by
  rw [ofmSig_lt base cv xs m i _ hi (by omega), ofmSig_lt base cv xs m i _ hi (by omega)]
  cases i with
  | zero =>
    simp only [ofmSig, setl, List.length_cons, List.length_nil]
    rw [set_n_in (by omega) (by omega), set_n_in (by omega) (by omega)]
    exact ⟨rfl, rfl⟩
  | succ i =>
    rw [ofmSig, set_n_in (by omega) (by omega), set_n_in (by omega) (by omega),
      show 4 + 15 * (i + 1) - (7 + 15 * i) = 12 by omega,
      show 5 + 15 * (i + 1) - (7 + 15 * i) = 13 by omega]
    exact ⟨rfl, rfl⟩

/-- Block `i < m`'s word and own values. -/
theorem ofmSig_block (base : Val) (cv : Digest) (xs : List E) (m i : ℕ) (hi : i < m) :
    ofmSig base cv xs m (.n (6 + 15 * i)) = xs.getD i 0 ∧
      ∀ k, 2 ≤ k → k < 14 → ofmSig base cv xs m (.n (6 + 15 * i + 1 + k)) =
        fsVals (xs.getD i 0) (cvAt cv xs i) 1 k := by
  have hw : ofmSig base cv xs m (.n (6 + 15 * i)) = xs.getD i 0 := by
    rw [ofmSig_lt base cv xs m (i + 1) _ hi (by omega), ofmSig, set_n_lt (by omega), setl,
      set_n_in (by omega) (by simp), Nat.sub_self]
    rfl
  refine ⟨hw, fun k hk1 hk2 => ?_⟩
  rw [ofmSig_lt base cv xs m (i + 1) _ hi (by omega), ofmSig, set_n_in (by omega) (by omega),
    show 6 + 15 * i + 1 + k - (7 + 15 * i) = k by omega]

/-! ## The theorem -/

theorem obsAll_eq_cvAt (cv : Digest) (xs : List E) : obsAll cv xs = cvAt cv xs xs.length := by
  rw [cvAt_eq cv xs _ le_rfl, List.take_length]

theorem word_pow_two {n : ℕ} (h : n < 64) : word (2 ^ n) 0 0 = gen ^ n := word_two_pow h

/-- **`opening_final_message` at every `0 < n < 64`**, for a compiled function whose body is
`ofmBody n`. -/
theorem opening_final_message_iff {name : String} {f : Fn} (n : ℕ) (hn : 0 < n) (hn64 : n < 64)
    (hfind : coreProgram.find? name = some f) (hparams : f.params = [.n 0, .n 1, .n 2, .n 3])
    (hbody : f.body = ofmBody n) (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd name args rets ↔ MeaningOpeningFinalMessage n rd args rets := by
  rw [rel_iff_sem hfind, hbody, hparams, ofmBody]
  simp only [holdsList_append, holdsList_range_flatten n ofmBlock (fun _ => rfl), holds_ofmBlock, ofmTail, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons,
    List.map_nil]
  constructor
  · rintro ⟨σ, hp, h4, h5, hblk, t1, t2, t3, t4, t5, hret⟩
    subst hp
    set xs := (List.range n).map fun i => σ (.n (6 + 15 * i))
    have hxs : ∀ i < n, xs.getD i 0 = σ (.n (6 + 15 * i)) := fun i hi => by
      simp [xs, List.getD_eq_getElem?_getD, hi]
    obtain ⟨cv, hcv, -⟩ := (hblk 0 hn).2.1
    simp only [Nat.mul_zero, Nat.add_zero] at hcv
    have hst : ∀ i ≤ n, (σ (.n (4 + 15 * i)), σ (.n (5 + 15 * i))) =
        digestScalars (cvAt cv xs i) := by
      intro i hi
      induction i with
      | zero => exact hcv
      | succ i ih =>
        obtain ⟨-, ⟨cvi, hcvi, e⟩, -⟩ := hblk i (by omega)
        have hc : cvi = cvAt cv xs i := digestScalars_injective (hcvi.symm.trans (ih (by omega)))
        subst hc
        have e12 : σ (.n (4 + 15 * (i + 1))) = fsVals (σ (.n (6 + 15 * i))) (cvAt cv xs i) 1 12 := by
          rw [show 4 + 15 * (i + 1) = 6 + 15 * i + 1 + 12 by ring]; exact e 12 (by omega) (by omega)
        have e13 : σ (.n (5 + 15 * (i + 1))) = fsVals (σ (.n (6 + 15 * i))) (cvAt cv xs i) 1 13 := by
          rw [show 5 + 15 * (i + 1) = 6 + 15 * i + 1 + 13 by ring]; exact e 13 (by omega) (by omega)
        rw [e12, e13, cvAt, hxs i (by omega)]
        show ((digestScalars (absorbCv (cvAt cv xs i) (σ (.n (6 + 15 * i))) 1)).1,
          (digestScalars (absorbCv (cvAt cv xs i) (σ (.n (6 + 15 * i))) 1)).2) = _
        rw [Prod.mk.eta]
    rw [h4, h5] at hcv
    have hlen : xs.length = n := by simp [xs]
    have hr : RunsTo (Prog.readN n) cv xs xs (obsAll cv xs) := by
      have := runsTo_readN cv xs; rwa [hlen] at this
    refine ⟨cv, xs, _, hcv, hlen, fun k hk => ?_, fun k hk => ?_, hr, ?_⟩
    · have hk' : k < n := hlen ▸ hk
      have := (hblk k hk').1
      simpa [xs] using this
    · have hk' : k < n := hlen ▸ hk
      have := (hblk k hk').2.2
      simpa [xs] using this
    · rw [← hret, t1, t2, t5, t4, t3, word_pow_two hn64, obsAll_eq_cvAt, hlen,
        ← hst n le_rfl]
  · intro hm
    obtain ⟨s0, s1, cur, out, rfl⟩ : ∃ s0 s1 cur out, args = [s0, s1, cur, out] := by
      match args, hm with
      | [a, b, c, d], _ => exact ⟨a, b, c, d, rfl⟩
    obtain ⟨cv, xs, cv', hcv, hlen, hcur, hout, hrun, hret⟩ := hm
    obtain ⟨-, rfl⟩ := (runsTo_readN cv xs).iff.mp (hlen ▸ hrun)
    subst hret
    set base := Val.ofArgs [s0, s1, cur, out]
    set τ := setl (ofmSig base cv xs n) (6 + 15 * n)
      [(digestScalars (cvAt cv xs n)).1, (digestScalars (cvAt cv xs n)).2, word (2 ^ n) 0 0,
        cur * word (2 ^ n) 0 0, cur * word (2 ^ n) 0 0]
    have hτ : ∀ k < 6 + 15 * n, τ (.n k) = ofmSig base cv xs n (.n k) := fun k hk => by
      simp only [τ, setl]; rw [set_n_lt hk]
    have hbase : ∀ k < 4, τ (.n k) = base (.n k) := fun k hk => by
      rw [hτ k (by omega), ofmSig_base _ _ _ _ _ hk]
    obtain ⟨hs0, hs1⟩ := ofmSig_state base cv xs n n le_rfl
    refine ⟨τ, ?_, ?_, ?_, ?blk, ?tail⟩
    · simp only [hbase 0 (by omega), hbase 1 (by omega), hbase 2 (by omega), hbase 3 (by omega)]
      rfl
    · rw [hτ 4 (by omega), hbase 0 (by omega)]
      have := (ofmSig_state base cv xs n 0 (by omega)).1
      simp only [Nat.mul_zero, Nat.add_zero] at this
      rw [this]
      exact (congrArg Prod.fst hcv).symm
    · rw [hτ 5 (by omega), hbase 1 (by omega)]
      have := (ofmSig_state base cv xs n 0 (by omega)).2
      simp only [Nat.mul_zero, Nat.add_zero] at this
      rw [this]
      exact (congrArg Prod.snd hcv).symm
    case blk =>
      intro i hi
      obtain ⟨hw, hv⟩ := ofmSig_block base cv xs n i hi
      obtain ⟨hst0, hst1⟩ := ofmSig_state base cv xs n i (by omega)
      have hi' : i < xs.length := hlen ▸ hi
      have hx : xs.getD i 0 = xs[i] := by simp [List.getD_eq_getElem?_getD, hi']
      refine ⟨?_, ⟨cvAt cv xs i, ?_, fun k hk1 hk2 => ?_⟩, ?_⟩
      · rw [hbase 2 (by omega), hτ _ (by omega), hw, hx]; exact hcur i hi'
      · rw [hτ _ (by omega), hτ _ (by omega), hst0, hst1]
      · rw [hτ _ (by omega), hτ _ (by omega), hw, hv k hk1 hk2]
      · rw [hbase 3 (by omega), hτ _ (by omega), hw, hx]; exact hout i hi'
    case tail =>
      have hlk : ∀ j, j < 5 → τ (.n (6 + 15 * n + j)) =
          [(digestScalars (cvAt cv xs n)).1, (digestScalars (cvAt cv xs n)).2, word (2 ^ n) 0 0,
            cur * word (2 ^ n) 0 0, cur * word (2 ^ n) 0 0].getD j 0 := fun j hj => by
        simp only [τ, setl]
        rw [set_n_in (by omega) (by simp only [List.length_cons, List.length_nil]; omega),
          Nat.add_sub_cancel_left]
      have l6 := hlk 0 (by omega)
      have l7 := hlk 1 (by omega)
      have l8 := hlk 2 (by omega)
      have l9 := hlk 3 (by omega)
      have l10 := hlk 4 (by omega)
      simp only [Nat.add_zero, List.getD_cons_zero, List.getD_cons_succ,
        show 6 + 15 * n + 1 = 7 + 15 * n by omega, show 6 + 15 * n + 2 = 8 + 15 * n by omega,
        show 6 + 15 * n + 3 = 9 + 15 * n by omega, show 6 + 15 * n + 4 = 10 + 15 * n by omega]
        at l6 l7 l8 l9 l10
      have l4 : τ (.n (4 + 15 * n)) = (digestScalars (cvAt cv xs n)).1 := by
        rw [hτ _ (by omega)]; exact hs0
      have l5 : τ (.n (5 + 15 * n)) = (digestScalars (cvAt cv xs n)).2 := by
        rw [hτ _ (by omega)]; exact hs1
      have l2 : τ (.n 2) = cur := hbase 2 (by omega)
      refine ⟨by rw [l6, l4], by rw [l7, l5], l8, by rw [l9, l2, l8], by rw [l10, l9], ?_⟩
      rw [l6, l7, l10, word_pow_two hn64, obsAll_eq_cvAt, hlen]

/-! ## The specializations -/

set_option maxRecDepth 100000 in
theorem opening_final_message_L4_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "opening_final_message__L4" args rets ↔
      MeaningOpeningFinalMessage 4 rd args rets :=
  opening_final_message_iff 4 (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 616) (by decide +kernel) rfl) rfl rfl rd args rets

set_option maxRecDepth 100000 in
theorem opening_final_message_L8_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "opening_final_message__L8" args rets ↔
      MeaningOpeningFinalMessage 8 rd args rets :=
  opening_final_message_iff 8 (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 631) (by decide +kernel) rfl) rfl rfl rd args rets

set_option maxRecDepth 100000 in
theorem opening_final_message_L16_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "opening_final_message__L16" args rets ↔
      MeaningOpeningFinalMessage 16 rd args rets :=
  opening_final_message_iff 16 (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 588) (by decide +kernel) rfl) rfl rfl rd args rets

set_option maxRecDepth 100000 in
theorem opening_final_message_L32_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "opening_final_message__L32" args rets ↔
      MeaningOpeningFinalMessage 32 rd args rets :=
  opening_final_message_iff 32 (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 602) (by decide +kernel) rfl) rfl rfl rd args rets

end
end LeanVM.Guest.B1
