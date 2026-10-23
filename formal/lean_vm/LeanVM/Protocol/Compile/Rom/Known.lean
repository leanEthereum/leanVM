/-
  LeanVM.Protocol.Compile.Rom.Known

  The decoding of a log without failure is stable: a digest decoded once keeps its decoding in
  every longer prefix, a chain step from a decoded state is read by the decoder at its entry,
  and the seed is decoded at the entry that completes the seeding.
-/

module

public import LeanVM.Protocol.Compile.Rom.Potential

/-!
# Stability of the decoding without failure

`LeanVM.Protocol.Compile.Rom.Decode` reads a log entry by entry. In a log without failure
(`Fail`), that reading agrees with the compiled verifier's run: this module proves the three
facts the final inequality (`LeanVM.Protocol.Compile.Rom.Final`) uses.

* `Known σ P ℓ c inf`: the digest `c` is the output of an entry of `ℓ`, and every prefix of `ℓ`
  past that entry decodes `c` as `inf`. Once a digest is decoded its decoding is fixed
  (`known_of_set`): only an entry with output `c` could change it, and outputs are distinct.
* `entry_read`: if `cv` is `Known` and the `j`-th entry is the chain step `cv ‖ (x, tag)`, the
  decoder reads that entry with `cv`'s decoding: its record is among the log's records, and the
  output's decoding is `Known`. The entry comes after `cv`'s (`lt_of_chunk`), and it is not the
  last input of any seeding: that input would extend the digest of an earlier seeding input,
  which has no 64 bytes, while every decoded digest is the output of a 64-byte input
  (`info_input_length`).
* `seed_known`: if the seeding of the statement `x` computes the seed `s₀` through the log's
  answers, some entry completes it, the decoder reads it as `x`'s seed (`Seeds.inj`), the record
  `bnd (root x) …` of `s₀` is among the log's records, and `s₀`'s decoding is `Known`. The
  seeding's entries come in order (`lt_of_seedInput`, `lt_of_chunk`).
-/

namespace LeanVM.Protocol.Compile.Rom

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Rom

@[expose] public section

variable {X : Type} {σ : Seeds X} {P : Prog Bool}

/-! ## Recording decodings -/

theorem setInfo_eq_some {f : Digest → Option Info} {u c : Digest} {o : Option Info} {i : Info}
    (h : setInfo f u o c = some i) : (c = u ∧ o = some i) ∨ f c = some i := by
  rcases o with _ | j
  · exact Or.inr h
  · simp only [setInfo, Function.update_apply] at h
    split at h
    · exact Or.inl ⟨by assumption, h⟩
    · exact Or.inr h

theorem setInfo_of_ne {f : Digest → Option Info} {u c : Digest} (o : Option Info) (h : c ≠ u) :
    setInfo f u o c = f c := by
  rcases o with _ | j
  · rfl
  · simp [setInfo, h]

theorem setInfo_self (f : Digest → Option Info) (u : Digest) {i : Info} :
    setInfo f u (some i) u = some i := by
  simp [setInfo]

/-- A decoded digest is the output of an entry. -/
theorem info_output (σ : Seeds X) (P : Prog Bool) (ℓ' : Log) {c : Digest} {i : Info}
    (h : (decode σ P ℓ').info c = some i) : ∃ (m : ℕ) (hm : m < ℓ'.length), ℓ'[m].2 = c := by
  induction ℓ' using List.reverseRecOn generalizing i with
  | nil => simp [Dec.init] at h
  | append_singleton ℓ e ih =>
    obtain ⟨t, u⟩ := e
    rw [info_decode_append] at h
    rcases setInfo_eq_some h with ⟨rfl, -⟩ | h
    · exact ⟨ℓ.length, by simp, by simp⟩
    · obtain ⟨m, hm, hmc⟩ := ih h
      exact ⟨m, by simp; omega, by rw [List.getElem_append_left hm]; exact hmc⟩

theorem decode_take_succ (σ : Seeds X) (P : Prog Bool) (ℓ : Log) {j : ℕ} (hj : j < ℓ.length) :
    decode σ P (ℓ.take (j + 1)) =
      decStep σ P (ℓ.take j) (decode σ P (ℓ.take j)) ℓ[j].1 ℓ[j].2 := by
  rw [← List.take_append_getElem hj]
  exact decode_append σ P _ ℓ[j].1 ℓ[j].2

/-- The records of a log extend the records of every prefix. -/
theorem kinds_prefix (σ : Seeds X) (P : Prog Bool) (l r : Log) :
    (decode σ P l).kinds <+: (decode σ P (l ++ r)).kinds := by
  induction r using List.reverseRecOn with
  | nil => simp
  | append_singleton r e ih =>
    obtain ⟨t, u⟩ := e
    rw [← List.append_assoc, kinds_decode_append]
    exact ih.trans (List.prefix_append _ _)

theorem kinds_mem_of_take (σ : Seeds X) (P : Prog Bool) (ℓ : Log) (j : ℕ)
    {κ : Shape × Digest} (h : κ ∈ (decode σ P (ℓ.take j)).kinds) : κ ∈ (decode σ P ℓ).kinds := by
  have := kinds_prefix σ P (ℓ.take j) (ℓ.drop j)
  rw [List.take_append_drop] at this
  exact this.subset h

/-! ## Known digests -/

/-- The digest `c` is the output of an entry of `ℓ`, and every prefix past that entry decodes it
as `inf`. -/
def Known (σ : Seeds X) (P : Prog Bool) (ℓ : Log) (c : Digest) (inf : Info) : Prop :=
  ∃ (m : ℕ) (hm : m < ℓ.length), ℓ[m].2 = c ∧
    ∀ j, m < j → j ≤ ℓ.length → (decode σ P (ℓ.take j)).info c = some inf

/-- **Decodings are stable without failure.** -/
theorem known_of_set {ℓ : Log} (hf : ¬ Fail σ ℓ) {m : ℕ} (hm : m < ℓ.length) {inf : Info}
    (h : (decode σ P (ℓ.take (m + 1))).info ℓ[m].2 = some inf) : Known σ P ℓ ℓ[m].2 inf := by
  refine ⟨m, hm, rfl, fun j hj hjl ↦ ?_⟩
  induction j, hj using Nat.le_induction with
  | base => exact h
  | succ j hmj ih =>
    have hjl' : j < ℓ.length := by omega
    rw [decode_take_succ σ P ℓ hjl']
    show setInfo _ ℓ[j].2 _ ℓ[m].2 = some inf
    rw [setInfo_of_ne _ (output_ne hf hm hjl' (by omega)), ih (by omega)]

/-! ## The seeding -/

theorem goPend_none_mono {H H' : Bytes → Option Digest}
    (hH : ∀ x v, H x = some v → H' x = some v) :
    ∀ (as : List (Bytes × Bytes)) (d : Digest), goPend H as d = none → goPend H' as d = none
  | [], _, _ => rfl
  | a :: as, d, h => by
    simp only [goPend] at h ⊢
    split at h
    · simp at h
    · rename_i d' hd
      rw [hH _ _ hd]
      exact goPend_none_mono hH as d' h

theorem pend_none_mono {H H' : Bytes → Option Digest} (hH : ∀ x v, H x = some v → H' x = some v)
    {σ : Seed} (h : pend H σ = none) : pend H' σ = none := by
  simp only [pend] at h ⊢
  split at h
  · simp at h
  · rename_i d hd
    rw [hH _ _ hd]
    exact goPend_none_mono hH _ _ h

theorem goPend_unanswered {H : Bytes → Option Digest} :
    ∀ (as : List (Bytes × Bytes)) (d : Digest) {x : Bytes} {b : Bool},
      goPend H as d = some (x, b) → H x = none
  | [], _, _, _, h => by simp [goPend] at h
  | a :: as, d, x, b, h => by
    simp only [goPend] at h
    split at h
    · rename_i hn
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1]; exact hn
    · exact goPend_unanswered as _ h

theorem pend_unanswered {H : Bytes → Option Digest} {σ : Seed} {x : Bytes} {b : Bool}
    (h : pend H σ = some (x, b)) : H x = none := by
  simp only [pend] at h
  split at h
  · rename_i hn
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]; exact hn
  · exact goPend_unanswered _ _ h

theorem goPend_complete {H H' : Bytes → Option Digest} (hH : ∀ x v, H x = some v → H' x = some v)
    {x : Bytes} {u : Digest} (hx : H' x = some u) :
    ∀ (as : List (Bytes × Bytes)) (d : Digest), goPend H as d = some (x, true) →
      goPend H' as d = none
  | [], _, h => by simp [goPend] at h
  | a :: as, d, h => by
    simp only [goPend] at h ⊢
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq, List.isEmpty_iff] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [hx]; rfl
    · rename_i d' hd
      rw [hH _ _ hd]
      exact goPend_complete hH hx as d' h

theorem pend_complete {H H' : Bytes → Option Digest} (hH : ∀ x v, H x = some v → H' x = some v)
    {σ : Seed} {x : Bytes} {u : Digest} (hx : H' x = some u) (h : pend H σ = some (x, true)) :
    pend H' σ = none := by
  simp only [pend] at h ⊢
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq, List.isEmpty_iff] at h
    obtain ⟨rfl, hs⟩ := h
    rw [hx]
    simp only [hs, goPend]
  · rename_i d hd
    rw [hH _ _ hd]
    exact goPend_complete hH hx _ _ h

theorem stepAt_info_none (ℓ : Log) (cv : Digest) (x : E) (tag : ℕ) (u : Digest) :
    (stepAt ℓ cv x tag none).2 u = none := rfl

theorem look_mono_append (ℓ : Log) (t : Bytes) (u : Digest) :
    ∀ x v, look ℓ x = some v → look (ℓ ++ [(t, u)]) x = some v :=
  fun _ _ h ↦ look_append_of_some h _

/-- The last pending input of a seeding: the last step at the digest of the input before it,
which is the first input or the input of another step. -/
theorem goPend_true {H : Bytes → Option Digest} {t : Bytes} :
    ∀ (as : List (Bytes × Bytes)) (d : Digest), goPend H as d = some (t, true) →
      ∃ (hne : as ≠ []), (t = Seed.input (as.getLast hne) d ∧ as.dropLast = []) ∨
        ∃ a ∈ as.dropLast, ∃ d' d'', H (Seed.input a d') = some d'' ∧
          t = Seed.input (as.getLast hne) d''
  | [], _, h => by simp [goPend] at h
  | a :: as, d, h => by
    refine ⟨List.cons_ne_nil _ _, ?_⟩
    simp only [goPend] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq, List.isEmpty_iff] at h
      obtain ⟨rfl, rfl⟩ := h
      exact Or.inl ⟨rfl, rfl⟩
    · rename_i d' hd
      obtain ⟨hne, h1 | ⟨a', ha', e, e', he, ht⟩⟩ := goPend_true as d' h
      · obtain ⟨rfl, hdrop⟩ := h1
        refine Or.inr ⟨a, ?_, d, d', hd, by rw [List.getLast_cons hne]⟩
        rw [List.dropLast_cons_of_ne_nil hne]; exact List.mem_cons_self
      · refine Or.inr ⟨a', ?_, e, e', he, by rw [List.getLast_cons hne]; exact ht⟩
        rw [List.dropLast_cons_of_ne_nil hne]; exact List.mem_cons_of_mem _ ha'

/-- The last pending input of a seeding is a step's input at a digest the answers give to an
earlier input of the seeding, the first or another step's. -/
theorem pend_true {H : Bytes → Option Digest} {σ₀ : Seed} {t : Bytes}
    (h : pend H σ₀ = some (t, true)) (hne : σ₀.steps ≠ []) :
    ∃ prev d, H prev = some d ∧ t = Seed.input (σ₀.steps.getLast hne) d ∧
      (prev = σ₀.first ∨ ∃ a ∈ σ₀.steps.dropLast, ∃ d', prev = Seed.input a d') := by
  simp only [pend] at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq, List.isEmpty_iff] at h
    exact absurd h.2 hne
  · rename_i d hd
    obtain ⟨hne', h1 | ⟨a, ha, d', d'', he, ht⟩⟩ := goPend_true _ d h
    · exact ⟨σ₀.first, d, hd, h1.1, Or.inl rfl⟩
    · exact ⟨Seed.input a d', d'', he, ht, Or.inr ⟨a, ha, d', rfl⟩⟩

/-- The last input of a seeding of the family has 64 bytes. -/
theorem pend_length {H : Bytes → Option Digest} {x : X} {t : Bytes}
    (h : pend H (σ.seed x) = some (t, true)) : t.length = 64 := by
  obtain ⟨s, hs, hlast⟩ := σ.last x
  have hne : (σ.seed x).steps ≠ [] := by intro he; rw [he] at hlast; simp at hlast
  obtain ⟨prev, d, -, rfl, -⟩ := pend_true h hne
  rw [List.getLast?_eq_some_getLast hne, Option.some.injEq] at hlast
  rw [hlast]
  simp [Seed.input, digestBytes_length, hs]

/-- A decoded digest is the output of an entry whose input has the 64 bytes of a chain input. -/
theorem info_input_length (σ : Seeds X) (P : Prog Bool) (ℓ' : Log) {c : Digest} {i : Info}
    (h : (decode σ P ℓ').info c = some i) :
    ∃ (m : ℕ) (hm : m < ℓ'.length), ℓ'[m].2 = c ∧ ℓ'[m].1.length = 64 := by
  induction ℓ' using List.reverseRecOn generalizing i with
  | nil => simp [Dec.init] at h
  | append_singleton ℓ e ih =>
    obtain ⟨t, u⟩ := e
    rw [info_decode_append] at h
    rcases setInfo_eq_some h with ⟨rfl, hs⟩ | h
    · refine ⟨ℓ.length, by simp, by simp, ?_⟩
      simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self,
        List.getElem_cons_zero]
      unfold step at hs
      split at hs
      · rename_i x hx
        unfold rootAt at hx
        split at hx
        · rename_i hex
          exact pend_length (Option.some.inj hx ▸ hex.choose_spec)
        · cases hx
      · split at hs
        · rename_i hp
          obtain ⟨-, rfl⟩ := parse_eq_some hp
          simp [digestBytes_length, blockOf_length]
        · cases hs
    · obtain ⟨m, hm, hmc, hl⟩ := ih h
      exact ⟨m, by simp; omega, by rw [List.getElem_append_left hm]; exact hmc,
        by rw [List.getElem_append_left hm]; exact hl⟩

/-- Without failure, the log's answers are injective. -/
theorem look_inj {ℓ : Log} (hf : ¬ Fail σ ℓ) {a b : Bytes} {v : Digest} (ha : look ℓ a = some v)
    (hb : look ℓ b = some v) : a = b := by
  obtain ⟨i, hi, hei, -⟩ := (look_eq_some_iff ℓ a v).mp ha
  obtain ⟨j, hj, hej, -⟩ := (look_eq_some_iff ℓ b v).mp hb
  have := index_eq_of_output hf hi hj (by rw [hei, hej])
  subst this
  rw [hei] at hej
  exact (Prod.mk.inj hej).1

/-! ## Reading a chain step -/

/-- **A chain step from a known state is read at its entry.** -/
theorem entry_read {ℓ : Log} (hf : ¬ Fail σ ℓ) {cv : Digest} {inf : Info}
    (hk : Known σ P ℓ cv inf) {j : ℕ} (hj : j < ℓ.length) {x : E} {tag : ℕ} (htag : tag < 256)
    (ht : ℓ[j].1 = digestBytes cv ++ blockOf x tag) :
    ((stepAt (ℓ.take j) cv x tag (some inf)).1, ℓ[j].2) ∈ (decode σ P ℓ).kinds ∧
      ∀ inf', (stepAt (ℓ.take j) cv x tag (some inf)).2 ℓ[j].2 = some inf' →
        Known σ P ℓ ℓ[j].2 inf' := by
  obtain ⟨m, hm, hmc, hall⟩ := hk
  have hmj : m < j := lt_of_chunk hf hm hj (Or.inl (by rw [ht, hmc]; exact chunk0_append _ _))
  have hinfo : (decode σ P (ℓ.take j)).info cv = some inf := hall j hmj hj.le
  have hroot : rootAt σ (ℓ.take j) ℓ[j].1 = none := by
    unfold rootAt
    split
    · rename_i hex
      exfalso
      obtain ⟨x', hx'⟩ := hex
      obtain ⟨s, -, hlast⟩ := σ.last x'
      have hne : (σ.seed x').steps ≠ [] := by intro he; rw [he] at hlast; simp at hlast
      obtain ⟨prev, d, hprev, htd, hpl⟩ := pend_true hx' hne
      rw [List.getLast?_eq_some_getLast hne, Option.some.injEq] at hlast
      rw [hlast] at htd
      have hd : d = cv := by
        have := congrArg chunk0 (htd.symm.trans ht)
        simp only [Seed.input, List.nil_append, chunk0_append] at this
        exact digestBytes_injective this
      subst hd
      obtain ⟨m', hm', hem', -⟩ := (look_eq_some_iff _ prev d).mp hprev
      obtain ⟨k, hk, hkc, hkl⟩ := info_input_length σ P _ hinfo
      have hfj := not_fail_take hf j
      have hkm : k = m' := index_eq_of_output hfj hk hm' (by rw [hkc, hem'])
      subst hkm
      rw [hem'] at hkl
      simp only at hkl
      rcases hpl with rfl | ⟨a, ha, d', rfl⟩
      · exact σ.first_len x' hkl
      · exact σ.mid_len x' a ha d' hkl
    · rfl
  have hstep : step σ P (ℓ.take j) (decode σ P (ℓ.take j)) ℓ[j].1 =
      stepAt (ℓ.take j) cv x tag (some inf) := by
    unfold step
    rw [hroot, ht, parse_chain cv x htag]
    simp only [hinfo]
  have hdec := decode_take_succ σ P ℓ hj
  refine ⟨?_, fun inf' hi ↦ ?_⟩
  · refine kinds_mem_of_take σ P ℓ (j + 1) ?_
    rw [hdec]
    show _ ∈ (decode σ P (ℓ.take j)).kinds ++ [((step σ P _ _ ℓ[j].1).1, ℓ[j].2)]
    rw [hstep]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  · refine known_of_set hf hj ?_
    rw [hdec]
    show setInfo _ ℓ[j].2 ((step σ P _ _ ℓ[j].1).2 ℓ[j].2) ℓ[j].2 = some inf'
    rw [hstep, hi, setInfo_self]

/-! ## The seed -/

/-- The seeding's remaining steps, answered through the log, end at an entry that the entries
before it leave as the last pending step. -/
theorem goPend_entry {ℓ : Log} (hf : ¬ Fail σ ℓ) {s₀ : Digest} :
    ∀ (as : List (Bytes × Bytes)), (∀ a ∈ as, a ∈ σ.steps ∨ a.1 = []) → as ≠ [] →
      ∀ (d : Digest) (m : ℕ) (hm : m < ℓ.length), ℓ[m].2 = d →
        as.foldlM (fun d a ↦ look ℓ (Seed.input a d)) d = some s₀ →
          ∃ (j : ℕ) (hj : j < ℓ.length), m < j ∧ ℓ[j].2 = s₀ ∧
            goPend (look (ℓ.take j)) as d = some (ℓ[j].1, true)
  | [], _, hne, _, _, _, _, _ => absurd rfl hne
  | a :: as, has, _, d, m, hm, hmd, hfold => by
    simp only [List.foldlM_cons, bind, Option.bind_eq_some_iff] at hfold
    obtain ⟨d', hd', hfold⟩ := hfold
    obtain ⟨m', hm', hem', hn'⟩ := (look_eq_some_iff ℓ _ d').mp hd'
    have hmm' : m < m' := by
      rcases has a List.mem_cons_self with ha | ha
      · exact lt_of_seedInput hf hm hm' ha (by rw [hem', hmd])
      · refine lt_of_chunk hf hm hm' (Or.inl ?_)
        rw [hem', hmd]
        obtain ⟨pre, suf⟩ := a
        simp only at ha
        subst ha
        simp only [Seed.input, List.nil_append, chunk0_append]
    rcases as with _ | ⟨a₁, as₁⟩
    · simp only [List.foldlM_nil, pure, Option.some.injEq] at hfold
      refine ⟨m', hm', hmm', by rw [hem', hfold], ?_⟩
      simp only [goPend, hem', hn', List.isEmpty_nil]
    · obtain ⟨j, hj, hm'j, hjs, hg⟩ := goPend_entry hf (a₁ :: as₁)
        (fun b hb ↦ has b (List.mem_cons_of_mem _ hb)) (List.cons_ne_nil _ _) d' m' hm'
        (by rw [hem']) hfold
      refine ⟨j, hj, hmm'.trans hm'j, hjs, ?_⟩
      simp only [goPend]
      rw [look_take_of_first hm' hem' hn' hm'j]
      exact hg

/-- **The seed's entry.** If the seeding of `x` computes `s₀` through the log's answers, some
entry outputs `s₀` while the entries before it leave its input as the last pending input. -/
theorem seed_entry {ℓ : Log} (hf : ¬ Fail σ ℓ) {x : X} {s₀ : Digest}
    (hs : (σ.seed x).run (look ℓ) = some s₀) :
    ∃ (j : ℕ) (hj : j < ℓ.length), ℓ[j].2 = s₀ ∧
      pend (look (ℓ.take j)) (σ.seed x) = some (ℓ[j].1, true) := by
  simp only [Seed.run, bind, Option.bind_eq_some_iff] at hs
  obtain ⟨d, hd, hfold⟩ := hs
  obtain ⟨m, hm, hem, hn⟩ := (look_eq_some_iff ℓ _ d).mp hd
  rcases hsteps : (σ.seed x).steps with _ | ⟨a, as⟩
  · rw [hsteps] at hfold
    simp only [List.foldlM_nil, pure, Option.some.injEq] at hfold
    refine ⟨m, hm, by rw [hem, hfold], ?_⟩
    simp only [pend, hem, hn, hsteps, List.isEmpty_nil]
  · rw [hsteps] at hfold
    obtain ⟨j, hj, hmj, hjs, hg⟩ := goPend_entry hf (a :: as)
      (fun b hb ↦ σ.steps_mem x b (by rw [hsteps]; exact hb)) (List.cons_ne_nil _ _) d m hm
      (by rw [hem]) hfold
    refine ⟨j, hj, hjs, ?_⟩
    simp only [pend]
    rw [look_take_of_first hm hem hn hmj, hsteps]
    exact hg

/-- **The seed is decoded.** If the seeding of `x` computes `s₀` through the log's answers and
its root is a root of the program, the record `bnd (root x)` of `s₀` is among the log's records
and `s₀`'s decoding is known. -/
theorem seed_known {ℓ : Log} (hf : ¬ Fail σ ℓ) {x : X} {s₀ : Digest}
    (hs : (σ.seed x).run (look ℓ) = some s₀) (hr : RootOk P (σ.root x)) :
    (Shape.bnd (σ.root x) (nodeAt P (σ.root x)), s₀) ∈ (decode σ P ℓ).kinds ∧
      ∀ inf, stInfo (σ.root x) (nodeAt P (σ.root x)) = some inf → Known σ P ℓ s₀ inf := by
  obtain ⟨j, hj, hjs, hp⟩ := seed_entry hf hs
  have hroot : rootAt σ (ℓ.take j) ℓ[j].1 = some x := by
    unfold rootAt
    have hex : ∃ x', pend (look (ℓ.take j)) (σ.seed x') = some (ℓ[j].1, true) := ⟨x, hp⟩
    have hfj := not_fail_take hf j
    have hx := σ.inj _ (fun a b v ha hb ↦ look_inj hfj ha hb) _ _ _ hex.choose_spec hp
    simp only [hex, ↓reduceDIte, hx]
  have hstep : step σ P (ℓ.take j) (decode σ P (ℓ.take j)) ℓ[j].1 =
      (.bnd (σ.root x) (nodeAt P (σ.root x)),
        fun _ ↦ stInfo (σ.root x) (nodeAt P (σ.root x))) := by
    unfold step
    rw [hroot]
    simp only [rootStep, hr, ↓reduceIte]
  have hdec := decode_take_succ σ P ℓ hj
  subst hjs
  refine ⟨?_, fun inf hi ↦ ?_⟩
  · refine kinds_mem_of_take σ P ℓ (j + 1) ?_
    rw [hdec]
    show _ ∈ (decode σ P (ℓ.take j)).kinds ++ [((step σ P _ _ ℓ[j].1).1, ℓ[j].2)]
    rw [hstep]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  · refine known_of_set hf hj ?_
    rw [hdec]
    show setInfo _ ℓ[j].2 ((step σ P _ _ ℓ[j].1).2 ℓ[j].2) ℓ[j].2 = some inf
    rw [hstep]
    simp only [hi, setInfo_self]

end
end LeanVM.Protocol.Compile.Rom
