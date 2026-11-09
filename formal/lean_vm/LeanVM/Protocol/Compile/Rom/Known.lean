/-
  LeanVM.Protocol.Compile.Rom.Known

  The decoding of a log without failure is stable: a state decoded once keeps its decoding in
  every longer prefix, a permutation of the sponge from a decoded state is read by the decoder at
  its entry, and the seed is decoded at the entry that computes it.
-/

module

public import LeanVM.Protocol.Compile.Rom.Potential

/-!
# Stability of the decoding without failure

`LeanVM.Protocol.Compile.Rom.Decode` reads a log entry by entry. In a log without failure
(`Fail`), that reading agrees with the compiled verifier's run: this module proves the facts the
final inequality (`LeanVM.Protocol.Compile.Rom.Final`) uses.

* `Known σ P ℓ c inf`: the capacity `c` is the capacity of the output of a permutation entry of
  `ℓ`, and every prefix of `ℓ` past that entry decodes it as `inf`; if `inf` is in the middle of
  a commitment, the entry's input ends with the root's first half (`HalfOk`). Once a capacity is
  decoded its decoding is fixed (`known_of_set`): only an entry whose output has that capacity
  could change it, and the capacities of outputs are distinct.
* `duplex_read`: if the state's capacity `c` is `Known` and the log answers the permutation input
  `duplexOf c ps` of the waiting scalars `ps`, the decoder reads that entry with `c`'s decoding,
  consuming `ps`: its record is among the log's records, and the output's decoding is `Known`.
  The entry comes after the state's (`lt_of_cap`); it is not a seed, whose input has the zero
  capacity; and the commitments its scalars complete read the word extracted from the hash
  entries before it, which is the word extracted from the whole log, every root it absorbs
  being answered before it (`lt_of_rootOf`, `extract_take_eq`, `consume_congr`).
* `seed_known`: if the seeding of the statement `x` computes the seed `s₀` through the log's
  answers, the entry that computes it is read as `x`'s seed (`Seeds.inj`): the record
  `st (root x) …` of `s₀` is among the log's records, and `s₀`'s decoding is `Known`. The
  seeding's hash entries all come before it (`seed_order`, from `Seeds.refs`).
-/

namespace LeanVM.Protocol.Compile.Rom

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.KeccakHash LeanVM.Protocol.Rom

@[expose] public section

variable {X : Type} {σ : Seeds X} {P : VerifierProgram Bool}

/-! ## Recording decodings -/

theorem setInfo_of_ne {f : (Fin 9 → UInt64) → Option Info} {c c' : Fin 9 → UInt64}
    (o : Option Info) (h : c' ≠ c) : setInfo f c o c' = f c' := by
  rcases o with _ | j
  · rfl
  · simp [setInfo, h]

theorem setInfo_self (f : (Fin 9 → UInt64) → Option Info) (c : Fin 9 → UInt64) {i : Info} :
    setInfo f c (some i) c = some i := by
  simp [setInfo]

theorem decode_take_succ (σ : Seeds X) (P : VerifierProgram Bool) (ℓ : Log) {j : ℕ} (hj : j <
    ℓ.length) :
    decode σ P (ℓ.take (j + 1)) = decStep σ P (ℓ.take j) (decode σ P (ℓ.take j)) ℓ[j] := by
  rw [← List.take_append_getElem hj]
  exact decode_append σ P _ ℓ[j]

/-- The records of a log extend the records of every prefix. -/
theorem kinds_prefix (σ : Seeds X) (P : VerifierProgram Bool) (l r : Log) :
    (decode σ P l).kinds <+: (decode σ P (l ++ r)).kinds := by
  induction r using List.reverseRecOn with
  | nil => simp
  | append_singleton r e ih =>
    rw [← List.append_assoc]
    rcases e with p | ⟨t, u⟩
    · rw [decode_append_inl]; exact ih
    · rw [kinds_decode_append_inr]
      exact ih.trans (List.prefix_append _ _)

theorem kinds_mem_of_take (σ : Seeds X) (P : VerifierProgram Bool) (ℓ : Log) (j : ℕ)
    {κ : Shape × KeccakState} (h : κ ∈ (decode σ P (ℓ.take j)).kinds) :
    κ ∈ (decode σ P ℓ).kinds := by
  have := kinds_prefix σ P (ℓ.take j) (ℓ.drop j)
  rw [List.take_append_drop] at this
  exact this.subset h

/-! ## Known states -/

/-- A decoding in the middle of a commitment was set by an entry whose input ends with the
root's first half. -/
def HalfOk (s : KeccakState) (inf : Info) : Prop :=
  ∀ ht w k x₀, inf.2 = .half ht w k x₀ → slotE s 3 = x₀ ∧ slotTag s 3 = 1

/-- The capacity `c` is the capacity of the output of the permutation entry `m` of `ℓ`, and every
prefix of `ℓ` past that entry decodes it as `inf`. -/
def Known (σ : Seeds X) (P : VerifierProgram Bool) (ℓ : Log) (c : Fin 9 → UInt64) (inf : Info) :
    Prop :=
  ∃ (m : ℕ) (hm : m < ℓ.length) (s u : KeccakState), ℓ[m] = .inr (s, u) ∧ capOf u = c ∧
    HalfOk s inf ∧ ∀ j, m < j → j ≤ ℓ.length → (decode σ P (ℓ.take j)).info c = some inf

/-- **Decodings are stable without failure.** -/
theorem known_of_set {ℓ : Log} (hf : ¬ Fail σ ℓ) {m : ℕ} (hm : m < ℓ.length) {s u : KeccakState}
    (hem : ℓ[m] = .inr (s, u)) {inf : Info} (hh : HalfOk s inf)
    (h : (decode σ P (ℓ.take (m + 1))).info (capOf u) = some inf) :
    Known σ P ℓ (capOf u) inf := by
  refine ⟨m, hm, s, u, hem, rfl, hh, fun j hj hjl ↦ ?_⟩
  induction j, hj using Nat.le_induction with
  | base => exact h
  | succ j hmj ih =>
    have hjl' : j < ℓ.length := by omega
    rw [decode_take_succ σ P ℓ hjl']
    rcases hej : ℓ[j] with p | ⟨t', u'⟩
    · exact ih (by omega)
    · show setInfo _ (capOf u') _ (capOf u) = some inf
      rw [setInfo_of_ne _ (fCap_ne hf hm hjl' (by omega) hem hej), ih (by omega)]

/-! ## The waiting scalars of a permutation input -/

/-- The slots of a permutation input up to its first zero tag are its parsed scalars. -/
theorem slot_of_parsePending {t : KeccakState} {i : ℕ} (hi : i < (parsePending t).length) :
    slotE t i = ((parsePending t)[i]).1 ∧ (slotTag t i).toNat = ((parsePending t)[i]).2 := by
  have hi' : i < ((List.range 4).takeWhile fun i ↦ slotTag t i ≠ 0).length := by
    simpa [parsePending] using hi
  have hti : ((List.range 4).takeWhile fun i ↦ slotTag t i ≠ 0)[i] = i := by
    have hpre := List.takeWhile_prefix (fun i ↦ decide (slotTag t i ≠ 0)) (l := List.range 4)
    rw [List.IsPrefix.getElem hpre hi', List.getElem_range]
  simp only [parsePending, List.getElem_map]
  rw [hti]
  exact ⟨rfl, rfl⟩

/-- A consumption that ends in the middle of a commitment ended with the root's first half, of
tag `1`, unless nothing was consumed. -/
theorem consume_done_half {W : Digest → ℕ → ℕ → Word} :
    ∀ (ps : List (E × ℕ)) (h : List Ev) (pos : Pos) {h' : List Ev} {ht w : ℕ} {k :
        VerifierProgram Bool}
      {x₀ : E}, consume W h pos ps = .done h' (.half ht w k x₀) →
        ps = [] ∨ ps.getLast? = some (x₀, 1)
  | [], _, _, _, _, _, _, _, _ => Or.inl rfl
  | (x, tag) :: rest, h, .node p, h', ht, w, k, x₀, hc => by
    right
    simp only [consume] at hc
    split at hc
    · split at hc
      · rcases consume_done_half rest _ _ hc with rfl | hl
        · simp only [consume, Cons.done.injEq] at hc
          exact absurd hc.2 (by simp)
        · rcases rest with _ | ⟨y, rest'⟩
          · simp at hl
          · simpa using hl
      · cases hc
    · split at hc
      · rename_i htag
        rcases rest with _ | ⟨y, rest'⟩
        · simp only [consume, Cons.done.injEq, Pos.half.injEq] at hc
          obtain ⟨-, -, -, -, rfl⟩ := hc
          simp [htag]
        · rcases consume_done_half (y :: rest') _ _ hc with h0 | hl
          · simp at h0
          · simpa using hl
      · cases hc
    · split at hc <;> cases hc
    · cases hc
  | (x, tag) :: rest, h, .half ht' w' k' x₀', h', ht, w, k, x₀, hc => by
    right
    simp only [consume] at hc
    split at hc
    · split at hc
      · rcases consume_done_half rest _ _ hc with rfl | hl
        · simp only [consume, Cons.done.injEq] at hc
          exact absurd hc.2 (by simp)
        · rcases rest with _ | ⟨y, rest'⟩
          · simp at hl
          · simpa using hl
      · cases hc
    · cases hc

/-- Every decoding in the middle of a commitment comes from an input whose last slot is the
root's first half. -/
theorem halfOk_stepF (ℓ : Log) (δ : Dec) (t u : KeccakState) {inf : Info}
    (h : (stepF σ P ℓ δ t).2 u = some inf) : HalfOk t inf := by
  intro ht w k x₀ hinf
  obtain ⟨hh, hpos⟩ := inf
  simp only at hinf
  subst hinf
  unfold stepF at h
  split at h
  · unfold rootStep at h
    split at h <;> simp at h
  · split at h
    · rename_i h0 pos0 _
      generalize hc : consume (extract (lookH ℓ)) h0 pos0 (parsePending t) = c at h
      rcases c with ⟨h1, ⟨p1⟩ | ⟨ht1, w1, k1, x1⟩⟩ | ⟨h1, b, k1, n⟩ | _
      · simp only [decodeAt] at h
        split at h
        · simp at h
        · simp only [forced] at h; split at h <;> simp at h
        · simp only [forced] at h; split at h <;> simp at h
        · simp only [forced] at h; split at h <;> simp at h
        · simp at h
      · simp only [decodeAt] at h
        split at h
        · rename_i hlen
          simp only [Option.some.injEq, Prod.mk.injEq, Pos.half.injEq] at h
          obtain ⟨-, -, -, -, rfl⟩ := h
          rcases consume_done_half _ _ _ hc with h0 | hl
          · rw [h0] at hlen; simp at hlen
          · have h3 : 3 < (parsePending t).length := by omega
            obtain ⟨he, htg⟩ := slot_of_parsePending h3
            have hlast : (parsePending t)[3] = (x1, 1) := by
              rw [List.getLast?_eq_getElem?, hlen] at hl
              have hl' : (parsePending t)[3]? = some (x1, 1) := by simpa using hl
              exact Option.some.inj ((List.getElem?_eq_getElem h3).symm.trans hl')
            rw [hlast] at he htg
            refine ⟨he, ?_⟩
            apply UInt64.toNat_inj.mp
            simpa using htg
        · simp at h
      · simp [decodeAt] at h
      · simp [decodeAt] at h
    · simp at h

/-! ## Commitments read stable words -/

/-- The scalar before the waiting ones, at a position in the middle of a commitment. -/
def prePos : Pos → List (E × ℕ)
  | .node _ => []
  | .half _ _ _ x₀ => [(x₀, 1)]

/-- The roots adjacent scalars of tag `1` encode. -/
def rootsList (l : List (E × ℕ)) : List Digest :=
  (l.zip l.tail).filterMap fun ab ↦
    if ab.1.2 = 1 ∧ ab.2.2 = 1 then digestFromHalves (ab.1.1, ab.2.1) else none

theorem rootsList_cons_cons (a b : E × ℕ) (l : List (E × ℕ)) :
    rootsList (a :: b :: l) =
      (if a.2 = 1 ∧ b.2 = 1 then digestFromHalves (a.1, b.1) else none).toList ++
        rootsList (b :: l) := by
  simp only [rootsList, List.tail_cons, List.zip_cons_cons, List.filterMap_cons]
  split <;> simp_all

theorem rootsList_subset_cons (a : E × ℕ) (l : List (E × ℕ)) :
    ∀ r ∈ rootsList l, r ∈ rootsList (a :: l) := by
  intro r hr
  rcases l with _ | ⟨b, l⟩
  · simp [rootsList] at hr
  · rw [rootsList_cons_cons]
    exact List.mem_append_right _ hr

/-- **Consumption reads only the words of the roots it completes.** -/
theorem consume_congr {W W' : Digest → ℕ → ℕ → Word} :
    ∀ (ps : List (E × ℕ)) (h : List Ev) (pos : Pos),
      (∀ r ∈ rootsList (prePos pos ++ ps), ∀ ht w, W r ht w = W' r ht w) →
        consume W h pos ps = consume W' h pos ps
  | [], _, _, _ => rfl
  | (x, tag) :: rest, h, .node p, hW => by
    simp only [consume]
    split
    · split
      · exact consume_congr rest _ _ fun r hr ↦ hW r (by
          simpa [prePos] using rootsList_subset_cons (x, tag) rest r (by simpa [prePos] using hr))
      · rfl
    · split
      · rename_i htag
        exact consume_congr rest _ _ fun r hr ↦ hW r (by
          simp only [prePos, List.nil_append] at hr ⊢
          rw [htag]
          simpa using hr)
      · rfl
    · rfl
    · rfl
  | (x, tag) :: rest, h, .half ht w k x₀, hW => by
    simp only [consume]
    split
    · rename_i htag
      split
      · rename_i r hr
        have hrW : ∀ ht w, W r ht w = W' r ht w := hW r (by
          simp only [prePos, List.singleton_append]
          rw [rootsList_cons_cons]
          simp [htag, hr])
        rw [hrW ht w]
        refine consume_congr rest _ _ fun r' hr' ↦ hW r' ?_
        simp only [prePos, List.nil_append, List.singleton_append] at hr' ⊢
        exact rootsList_subset_cons _ _ r' (rootsList_subset_cons _ _ r' hr')
      · rfl
    · rfl

theorem mem_rootsList {l : List (E × ℕ)} {r : Digest} (hr : r ∈ rootsList l) :
    ∃ (i : ℕ) (hi : i + 1 < l.length), l[i].2 = 1 ∧ l[i + 1].2 = 1 ∧
      digestFromHalves (l[i].1, l[i + 1].1) = some r := by
  induction l with
  | nil => simp [rootsList] at hr
  | cons a l ih =>
    rcases l with _ | ⟨b, l⟩
    · simp [rootsList] at hr
    · rw [rootsList_cons_cons] at hr
      rcases List.mem_append.mp hr with hr | hr
      · split at hr
        · rename_i htag
          refine ⟨0, by simp, htag.1, htag.2, ?_⟩
          simpa using hr
        · simp at hr
      · obtain ⟨i, hi, h1, h2, h3⟩ := ih hr
        exact ⟨i + 1, by simpa using hi, h1, h2, h3⟩

/-- The roots a permutation input completes are roots it absorbs (`RootOf`): adjacent waiting
scalars, and, in the middle of a commitment, the first half in the last slot of the input that
produced the state. -/
theorem rootOf_of_mem_rootsList {ℓ' : Log} {c : Fin 9 → UInt64} {ps : List (E × ℕ)}
    (hv : ValidPending ps) {pos : Pos}
    (hpre : ∀ ht w k x₀, pos = .half ht w k x₀ → ∃ s', predIn ℓ' (duplexOf c ps) = some s' ∧
      slotE s' 3 = x₀ ∧ slotTag s' 3 = 1)
    {r : Digest} (hr : r ∈ rootsList (prePos pos ++ ps)) : RootOf ℓ' (duplexOf c ps) r := by
  have htag : ∀ i (hi : i < ps.length), ps[i].2 = 1 → slotTag (duplexOf c ps) i = 1 := by
    intro i hi h1
    rw [slotTag_duplexOf c ps (by have := hv.1; omega)]
    simp [hi, h1]
  have hslot : ∀ i (hi : i < ps.length), slotE (duplexOf c ps) i = ps[i].1 := fun i hi ↦
    slotE_duplexOf c ps hi (by have := hv.1; omega)
  have hpair : ∀ i (hi : i + 1 < ps.length), ps[i].2 = 1 → ps[i + 1].2 = 1 →
      digestFromHalves (ps[i].1, ps[i + 1].1) = some r → RootOf ℓ' (duplexOf c ps) r := by
    intro i hi h1 h2 h3
    refine Or.inl ⟨i, by have := hv.1; omega, ?_⟩
    simp only [pairRoot, htag i (by omega) h1, htag (i + 1) hi h2, and_self, ↓reduceIte,
      hslot i (by omega), hslot (i + 1) hi]
    exact h3
  rcases pos with p | ⟨ht, w, k, x₀⟩
  · obtain ⟨i, hi, h1, h2, h3⟩ := mem_rootsList (by simpa [prePos] using hr)
    exact hpair i hi h1 h2 h3
  · obtain ⟨i, hi, h1, h2, h3⟩ := mem_rootsList hr
    simp only [prePos, List.singleton_append, List.length_cons] at hi h1 h2 h3
    cases i with
    | zero =>
      obtain ⟨s', hs', hx, ht3⟩ := hpre ht w k x₀ rfl
      simp only [List.getElem_cons_zero, List.getElem_cons_succ] at h1 h2 h3
      right
      have hp0 : 0 < ps.length := by omega
      rw [straddleRoot, hs', Option.bind_some]
      simp only [ht3, htag 0 hp0 h2, and_self, ↓reduceIte, hx, hslot 0 hp0]
      exact h3
    | succ i =>
      simp only [List.getElem_cons_succ] at h1 h2 h3
      exact hpair i (by omega) h1 h2 h3

/-! ## Reading a permutation -/

/-- The predecessor of a permutation input is the input of the entry that produced its state. -/
theorem predIn_take {ℓ : Log} (hf : ¬ Fail σ ℓ) {m j : ℕ} (hm : m < ℓ.length) (hmj : m < j)
    {s u t : KeccakState} (hem : ℓ[m] = .inr (s, u)) (hc : capOf t = capOf u) :
    predIn (ℓ.take j) t = some s := by
  unfold predIn
  refine Option.map_eq_some_iff.mpr ⟨(s, u), ?_, rfl⟩
  -- the first entry with that capacity among the permutation entries of the prefix
  have hsplit : ℓ.take j = ℓ.take m ++ [ℓ[m]] ++ (ℓ.drop (m + 1)).take (j - m - 1) := by
    rw [← List.take_succ_eq_append_getElem hm, ← List.take_add]
    congr 1; omega
  rw [hsplit, rightOf_append, rightOf_append, hem, rightOf_inr, List.find?_append,
    List.find?_append]
  have hnone : (rightOf (ℓ.take m)).find? (fun e ↦ decide (capOf e.2 = capOf t)) = none := by
    rw [List.find?_eq_none]
    intro e he hce
    obtain ⟨i, hi, hei⟩ : ∃ (i : ℕ) (hi : i < (ℓ.take m).length), (ℓ.take m)[i] = .inr e := by
      have := mem_rightOf.mp he
      obtain ⟨i, hi, hei⟩ := List.mem_iff_getElem.mp this
      exact ⟨i, hi, hei⟩
    simp only [List.length_take] at hi
    have hei' : ℓ[i] = .inr (e.1, e.2) := by simpa using hei
    simp only [decide_eq_true_eq] at hce
    exact fCap_ne hf (by omega) hm (by omega) hei' hem (hce.trans hc)
  rw [hnone]
  simp [hc]

/-- **A permutation from a known state is read at its entry.** If the state's capacity `c` is
known at `(h₀, pos₀)` and the log answers the permutation input of the valid waiting scalars
`ps`, the entry is read by consuming `ps` from `(h₀, pos₀)`, with the words of the whole log:
its record is among the log's records, and the output's decoding is known. -/
theorem duplex_read {ℓ : Log} (hf : ¬ Fail σ ℓ) {c : Fin 9 → UInt64} {h₀ : List Ev} {pos₀ : Pos}
    (hk : Known σ P ℓ c (h₀, pos₀)) {ps : List (E × ℕ)} (hv : ValidPending ps) {v : KeccakState}
    (hl : lookF ℓ (duplexOf c ps) = some v) :
    ((decodeAt (consume (extract (lookH ℓ)) h₀ pos₀ ps) ps).1, v) ∈ (decode σ P ℓ).kinds ∧
      ∀ inf, (decodeAt (consume (extract (lookH ℓ)) h₀ pos₀ ps) ps).2 v = some inf →
        Known σ P ℓ (capOf v) inf := by
  obtain ⟨m, hm, s, u, hem, hcu, hhalf, hall⟩ := hk
  obtain ⟨j, hj, hej, hn⟩ := (lookF_eq_some_iff ℓ _ v).mp hl
  have hmj : m < j := lt_of_cap hf hm hj hem hej (by rw [capOf_duplexOf, hcu])
  have hinfo : (decode σ P (ℓ.take j)).info c = some (h₀, pos₀) := hall j hmj hj.le
  have hfj := not_fail_take hf j
  -- not a seed: a seed's input has the zero capacity
  have hroot : rootAt σ (ℓ.take j) (duplexOf c ps) = none := by
    unfold rootAt
    split
    · rename_i hex
      exfalso
      obtain ⟨x, ds, -, hfin⟩ := hex
      have h0 := σ.cap0 x ds
      rw [hfin, capOf_duplexOf] at h0
      exact fCap_ne_zero hf hm hem (hcu.trans h0)
    · rfl
  -- the words the entry's commitments read are the whole log's
  have hW : ∀ r ∈ rootsList (prePos pos₀ ++ ps), ∀ ht w,
      extract (lookH (ℓ.take j)) r ht w = extract (lookH ℓ) r ht w := by
    intro r hr ht w
    refine extract_take_eq hf (fun i hi x hei ↦ lt_of_rootOf hf hi hj hei hej ?_) ht w
    refine rootOf_of_mem_rootsList hv (fun ht' w' k' x₀ hpos ↦ ?_) hr
    refine ⟨s, predIn_take hf hm hmj hem (by rw [capOf_duplexOf, hcu]), ?_⟩
    exact hhalf ht' w' k' x₀ (by rw [hpos])
  have hstep : stepF σ P (ℓ.take j) (decode σ P (ℓ.take j)) (duplexOf c ps) =
      decodeAt (consume (extract (lookH ℓ)) h₀ pos₀ ps) ps := by
    unfold stepF
    rw [hroot, capOf_duplexOf, hinfo, parsePending_duplexOf c hv]
    simp only
    rw [consume_congr ps h₀ pos₀ hW]
  have hdec := decode_take_succ σ P ℓ hj
  rw [hej] at hdec
  refine ⟨?_, fun inf hi ↦ ?_⟩
  · refine kinds_mem_of_take σ P ℓ (j + 1) ?_
    rw [hdec]
    show _ ∈ (decode σ P (ℓ.take j)).kinds ++
      [((stepF σ P (ℓ.take j) (decode σ P (ℓ.take j)) (duplexOf c ps)).1, v)]
    rw [hstep]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  · have hi' : (stepF σ P (ℓ.take j) (decode σ P (ℓ.take j)) (duplexOf c ps)).2 v = some inf := by
      rw [hstep]; exact hi
    refine known_of_set hf hj hej (halfOk_stepF _ _ _ _ hi') ?_
    rw [hdec]
    show setInfo _ (capOf v) ((stepF σ P _ _ (duplexOf c ps)).2 v) (capOf v) = some inf
    rw [hi', setInfo_self]

/-! ## The seed -/

/-- **The seeding's hash entries come before its permutation entry.** Every hash answer of the
seeding is answered by an entry before the `j`-th, the permutation entry of its input. -/
theorem seed_order {ℓ : Log} (hf : ¬ Fail σ ℓ) {x : X} {ds : List Digest}
    (hans : Answered (lookH ℓ) (σ.seed x) ds) {j : ℕ} (hj : j < ℓ.length) {v : KeccakState}
    (hej : ℓ[j] = .inr ((σ.seed x).fin ds, v)) :
    Answered (lookH (ℓ.take j)) (σ.seed x) ds := by
  obtain ⟨hlen, hall⟩ := hans
  -- the entry answering step `i` comes before `j`
  have key : ∀ n, ∀ i (hi : i < ds.length), ds.length - i ≤ n →
      ∀ f, (σ.seed x).hs[i]? = some f → ∀ k (hk : k < ℓ.length),
        ℓ[k] = .inl (f (ds.take i), ds[i]) → k < j := by
    intro n
    induction n with
    | zero => intro i hi hn; omega
    | succ n ih =>
      intro i hi hn f hf' k hk hek
      rcases σ.refs x ds hlen i hi with hl | ⟨j', f', hij, hf'', o, ho, hc⟩
      · exact lt_of_laneDigest hf hk hj hek hej hl
      · have hj' : j' < ds.length := by
          rw [hlen]; exact (List.getElem?_eq_some_iff.mp hf'').1
        obtain ⟨g, hg, hgl⟩ := hall j' hj'
        rw [hf''] at hg
        cases hg
        obtain ⟨k', hk', hek', -⟩ := (lookH_eq_some_iff ℓ _ _).mp hgl
        have hk'j := ih j' hj' (by omega) f' hf'' k' hk' hek'
        exact lt_trans (lt_of_chunk hf hk hk' hek hek' (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ ho)) hc) hk'j
  refine ⟨hlen, fun i hi ↦ ?_⟩
  obtain ⟨f, hf', hH⟩ := hall i hi
  refine ⟨f, hf', ?_⟩
  obtain ⟨k, hk, hek, hn⟩ := (lookH_eq_some_iff ℓ _ _).mp hH
  exact lookH_take_of_first hk hek hn (key ds.length i hi (by omega) f hf' k hk hek)

/-- The seed of a statement, computed through answers in `Option`. -/
theorem seedRun_option {H : Bytes → Option Digest} {F : KeccakState → Option KeccakState} {σ₀ : Seed}
    {s₀ : KeccakState} (h : σ₀.run H F = some s₀) :
    ∃ ds, Answered H σ₀ ds ∧ F (σ₀.fin ds) = some s₀ := by
  simp only [Seed.run, bind, Option.bind_eq_some_iff] at h
  obtain ⟨ds, hds, hF⟩ := h
  exact ⟨ds, answered_of_hsRun hds, hF⟩

/-- **The seed is decoded.** If the seeding of `x` computes `s₀` through the log's answers and
its root is a root of the program, the record `st (root x)` of `s₀` is among the log's records
and `s₀`'s decoding is known. -/
theorem seed_known {ℓ : Log} (hf : ¬ Fail σ ℓ) {x : X} {s₀ : KeccakState}
    (hs : (σ.seed x).run (lookH ℓ) (lookF ℓ) = some s₀) (hr : RootOk P (σ.root x)) :
    (Shape.st (σ.root x) (nodeAt P (σ.root x)) none, s₀) ∈ (decode σ P ℓ).kinds ∧
      Known σ P ℓ (capOf s₀) (σ.root x, .node (nodeAt P (σ.root x))) := by
  obtain ⟨ds, hans, hF⟩ := seedRun_option hs
  obtain ⟨j, hj, hej, -⟩ := (lookF_eq_some_iff ℓ _ s₀).mp hF
  have hans' := seed_order hf hans hj hej
  have hfj := not_fail_take hf j
  have hroot : rootAt σ (ℓ.take j) ((σ.seed x).fin ds) = some x := by
    unfold rootAt
    have hex : ∃ x' ds', Answered (lookH (ℓ.take j)) (σ.seed x') ds' ∧
        (σ.seed x').fin ds' = (σ.seed x).fin ds := ⟨x, ds, hans', rfl⟩
    simp only [hex, ↓reduceDIte]
    obtain ⟨ds', hans'', hfin⟩ := hex.choose_spec
    rw [σ.inj _ (answersInj_lookH hfj) _ _ _ _ hans'' hans' hfin]
  have hstep : stepF σ P (ℓ.take j) (decode σ P (ℓ.take j)) ((σ.seed x).fin ds) =
      (.st (σ.root x) (nodeAt P (σ.root x)) none,
        fun _ ↦ some (σ.root x, .node (nodeAt P (σ.root x)))) := by
    unfold stepF
    rw [hroot]
    simp only [rootStep, hr, ↓reduceIte]
  have hdec := decode_take_succ σ P ℓ hj
  rw [hej] at hdec
  refine ⟨?_, ?_⟩
  · refine kinds_mem_of_take σ P ℓ (j + 1) ?_
    rw [hdec]
    show _ ∈ (decode σ P (ℓ.take j)).kinds ++
      [((stepF σ P (ℓ.take j) (decode σ P (ℓ.take j)) ((σ.seed x).fin ds)).1, s₀)]
    rw [hstep]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  · refine known_of_set hf hj hej (fun _ _ _ _ h ↦ by cases h) ?_
    rw [hdec]
    show setInfo _ (capOf s₀) ((stepF σ P _ _ ((σ.seed x).fin ds)).2 s₀) (capOf s₀) = _
    rw [hstep, setInfo_self]

end
end LeanVM.Protocol.Compile.Rom
