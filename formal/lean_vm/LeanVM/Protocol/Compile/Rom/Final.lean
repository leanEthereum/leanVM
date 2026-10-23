/-
  LeanVM.Protocol.Compile.Rom.Final

  The final inequality of the random-oracle theorem: if the compiled verifier accepts under the
  answers of a log without failure, and its extracted history passes through a doomed boundary,
  the potential of the log is one.
-/

module

public import LeanVM.Protocol.Compile.Rom.Known
public import LeanVM.Protocol.Compile.Rom.History

/-!
# The final inequality

`final_ineq`: let `C : Cert P` be a doom certificate, `ℓ` a log without failure, and `π` a proof
the seeded verifier accepts with every hash answered by `ℓ` (`verify (look ℓ) σ P π = some
true`). If some boundary prefix of the extracted history (`extractedHistory`) is doomed, then
`1 ≤ pot C.D σ P ℓ`.

The run is followed group by group. A *boundary* of the run is the seed or the point right
after a prover move (a scalar, a commitment, a nonce). At each boundary `h`, with chain state
`cv` and node `p`:

* the decoder knows `cv` at `h` (`Known`), and some record of the log has term at least
  `[D h] · gv ℓ cv h p` (`seed_known`, `move`);
* the run's squeezes and openings until the next prover move or the verdict are the ones `gv`
  follows (`follow`): the squeezes are lookups in `ℓ`, and the openings return the extracted
  rows because the answers are injective (`answer_of_openAll`). So `gv ℓ cv h p` is `esc D` at
  the group's end, which is `1` if `D h` holds there and not at the end.

The run's final history is not doomed (`Cert.final`) and prover moves keep doom (`Cert.read`,
`Cert.grind`, `Cert.commit`), so from the first doomed boundary some group leaves doom; its record
has term `1`. Commitments read the word extracted from the entries before their root is
absorbed, which is the word extracted from the whole log (`extract_take_eq`, using
`lt_of_rootOf`). After a nonce, the record that carries the group is whichever of the nonce's
two entries came first: the chain step (`Shape.grd`, whose factor is the proof of work's result
`1`) or the proof of work (`Shape.pow`).
-/

namespace LeanVM.Protocol.Compile.Rom

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Rom
open scoped ENNReal

@[expose] public section

/- The enumeration of `Digest` must never be unfolded by unification. -/
attribute [local irreducible] instFintypeDigest

variable {X : Type} {σ : Seeds X} {P : Prog Bool}

/-! ## Histories without boundaries -/

/-- No prefix of `h'` strictly longer than `h` is a boundary. -/
def NoBnd (h h' : List Ev) : Prop :=
  ∀ n, h.length < n → n ≤ h'.length → ¬ Boundary (h'.take n)

theorem noBnd_refl (h : List Ev) : NoBnd h h := fun _ h1 h2 ↦ absurd h1 (by omega)

theorem noBnd_append_single {h : List Ev} {e : Ev} (he : ¬ Boundary (h ++ [e])) :
    NoBnd h (h ++ [e]) := by
  intro n h1 h2
  have : n = h.length + 1 := by simp at h2; omega
  subst this
  rw [List.take_of_length_le (by simp)]
  exact he

theorem noBnd_trans {h h₁ h₂ : List Ev} (h01 : NoBnd h h₁) (h12 : NoBnd h₁ h₂)
    (hp : h₁ <+: h₂) : NoBnd h h₂ := by
  intro n hn hn2
  by_cases hn1 : n ≤ h₁.length
  · obtain ⟨r, rfl⟩ := hp
    rw [List.take_append_of_le_length hn1]
    exact h01 n hn hn1
  · exact h12 n (by omega) hn2

/-- A prover move or the accepting verdict: where a group of challenges ends. -/
def Move : Prog Bool → Prop
  | .ret true => True
  | .read _ => True
  | .grind _ _ => True
  | .commit _ _ _ => True
  | _ => False

theorem esc_move {D : List Ev → Prop} {h : List Ev} {p : Prog Bool} (hm : Move p)
    (hD : ¬ D h) : esc D h p = 1 := by
  cases p with
  | ret a => cases a <;> simp_all [Move, esc]
  | read _ => simp [esc, hD]
  | grind _ _ => simp [esc, hD]
  | commit _ _ _ => simp [esc, hD]
  | sample _ => exact absurd hm id
  | query _ _ _ => exact absurd hm id
  | fail => exact absurd hm id

/-! ## Following a group -/

section Follow

variable (C : Cert P) {ℓ : Log}

theorem settle_self_of_move {h : List Ev} {p : Prog Bool} (hm : Move p) :
    settle h p = some (h, p) := by
  cases p with
  | query _ _ _ => exact absurd hm id
  | _ => rfl

theorem settle_sample (h : List Ev) (k : E → Prog Bool) :
    settle h (.sample k) = some (h, .sample k) := rfl

/-- **Following a group.** From a chain state the decoder knows, the run's squeezes and
openings up to the next prover move or the verdict are those `gv` follows. -/
theorem follow (hf : ¬ Fail σ ℓ) :
    ∀ (p : Prog Bool) (s : St) (h : List Ev) {s_f : St} {hist : List Ev},
      RootsInv (look ℓ) s h → P.Reachable h → P.after h = some p →
      (∀ h' p', settle h p = some (h', p') → Known σ P ℓ s.cv (.st h' p')) →
      xrun (look ℓ) p s h = some (true, s_f, hist) →
      ∃ (p_e : Prog Bool) (s_e : St) (h_e : List Ev),
        gv C.D ℓ s.cv h p = esc C.D h_e p_e ∧ xrun (look ℓ) p_e s_e h_e = some (true, s_f, hist) ∧
        RootsInv (look ℓ) s_e h_e ∧ P.Reachable h_e ∧ P.after h_e = some p_e ∧
        Known σ P ℓ s_e.cv (.st h_e p_e) ∧ Move p_e ∧ h <+: h_e ∧ NoBnd h h_e ∧
        s_e.stream = s.stream
  | .ret true, s, h, _, _, hR, hr, ha, hk, hx =>
    ⟨.ret true, s, h, rfl, hx, hR, hr, ha, hk h _ rfl, trivial, List.prefix_refl _, noBnd_refl h,
      rfl⟩
  | .ret false, s, h, _, _, _, _, _, _, hx => by simp [xrun] at hx
  | .fail, s, h, _, _, _, _, _, _, hx => by simp [xrun] at hx
  | .read k, s, h, _, _, hR, hr, ha, hk, hx =>
    ⟨.read k, s, h, rfl, hx, hR, hr, ha, hk h _ rfl, trivial, List.prefix_refl _, noBnd_refl h,
      rfl⟩
  | .grind b k, s, h, _, _, hR, hr, ha, hk, hx =>
    ⟨.grind b k, s, h, rfl, hx, hR, hr, ha, hk h _ rfl, trivial, List.prefix_refl _,
      noBnd_refl h, rfl⟩
  | .commit ht w k, s, h, _, _, hR, hr, ha, hk, hx =>
    ⟨.commit ht w k, s, h, rfl, hx, hR, hr, ha, hk h _ rfl, trivial, List.prefix_refl _,
      noBnd_refl h, rfl⟩
  | .sample k, s, h, s_f, hist, hR, hr, ha, hk, hx => by
    simp only [xrun, absorbBlock_option, Option.bind_eq_some_iff] at hx
    obtain ⟨u, hu, hx⟩ := hx
    obtain ⟨j, hj, hej, -⟩ := (look_eq_some_iff ℓ _ u).mp hu
    have hj1 : ℓ[j].1 = digestBytes s.cv ++ blockOf 0 2 := by rw [hej]
    have hj2 : ℓ[j].2 = u := by rw [hej]
    obtain ⟨-, hknown⟩ := entry_read hf (hk h _ (settle_sample h k)) hj (by norm_num) hj1
    rw [hj2] at hknown
    have hk' : ∀ h' p', settle (h ++ [Ev.sample (challengeOf u)]) (k (challengeOf u)) =
        some (h', p') → Known σ P ℓ u (.st h' p') := by
      intro h' p' hs
      refine hknown _ ?_
      simp only [stepAt, stepSt, and_self, ↓reduceIte, stInfo, hs, Option.map_some]
    have hr' := Prog.Reachable.sample (challengeOf u) hr ha
    have ha' : P.after (h ++ [Ev.sample (challengeOf u)]) = some (k (challengeOf u)) := by
      rw [Prog.after_append_single _ ha]; simp [Prog.after]
    obtain ⟨p_e, s_e, h_e, hg, hx', hR', hre, hae, hke, hm, hp, hnb, hst⟩ :=
      follow hf (k (challengeOf u)) { s with cv := u } _ (rootsInv_append_sample hR _ _) hr' ha'
        hk' hx
    refine ⟨p_e, s_e, h_e, ?_, hx', hR', hre, hae, hke, hm,
      (List.prefix_append _ _).trans hp, ?_, hst⟩
    · simp only [gv, hu]
      exact hg
    · exact noBnd_trans (noBnd_append_single (not_boundary_append_sample h _)) hnb hp
  | .query i ps k, s, h, s_f, hist, hR, hr, ha, hk, hx => by
    simp only [xrun] at hx
    split at hx
    · simp at hx
    · rename_i root ht w hroot
      split at hx
      · rename_i rows rest ho
        have hans := answer_of_openAll (answersInj_look hf) hR hroot ho
        have hr' := Prog.Reachable.query hr ha hans
        have ha' : P.after (h ++ [Ev.query rows]) = some (k rows) := by
          rw [Prog.after_append_single _ ha]; simp [Prog.after]
        have hk' : ∀ h' p', settle (h ++ [Ev.query rows]) (k rows) = some (h', p') →
            Known σ P ℓ ({ s with openings := rest } : St).cv (.st h' p') := by
          intro h' p' hs
          refine hk h' p' ?_
          simp only [settle, hans]
          exact hs
        obtain ⟨p_e, s_e, h_e, hg, hx', hR', hre, hae, hke, hm, hp, hnb, hst⟩ :=
          follow hf (k rows) _ _ (rootsInv_append_query hR rows rest) hr' ha' hk' hx
        refine ⟨p_e, s_e, h_e, ?_, hx', hR', hre, hae, hke, hm,
          (List.prefix_append _ _).trans hp, ?_, hst⟩
        · simp only [gv, hans]
          exact hg
        · exact noBnd_trans (noBnd_append_single (not_boundary_append_query h _)) hnb hp
      · simp at hx

end Follow

/-! ## Prover moves -/

section Move

variable (C : Cert P) {ℓ : Log}

/-- A record of the log whose term bounds the doomed group value at a boundary. -/
def Carried (C : Cert P) (ℓ : Log) (cv : Digest) (h : List Ev) (p : Prog Bool) : Prop :=
  ∃ κ ∈ (decode σ P ℓ).kinds, ind (C.D h) * gv C.D ℓ cv h p ≤ term C.D ℓ κ

/-- A lookup absent from a later prefix is absent from an earlier one. -/
theorem look_take_none_of_le {ℓ : Log} {x : Bytes} {i j : ℕ} (hij : i ≤ j)
    (h : look (ℓ.take j) x = none) : look (ℓ.take i) x = none := by
  rcases hl : look (ℓ.take i) x with _ | v
  · rfl
  · have := look_of_prefix (List.take_prefix_take_left hij) hl
    rw [h] at this
    cases this

/-- Without failure, the first entry with output `c` in a prefix past its entry is that
entry. -/
theorem find?_take_output {ℓ : Log} (hf : ¬ Fail σ ℓ) {i j : ℕ} (hi : i < ℓ.length)
    (hij : i < j) (hj : j ≤ ℓ.length) :
    (ℓ.take j).find? (fun e ↦ decide (e.2 = ℓ[i].2)) = some ℓ[i] := by
  rw [List.find?_eq_some_iff_getElem]
  refine ⟨by simp, i, by simp; omega, by simp, fun k hk ↦ ?_⟩
  simp only [List.getElem_take, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
  exact output_ne hf (by omega) hi hk

/-- **A prover move.** From a chain state the decoder knows at a prover move, the run reaches
the next boundary, where the decoder knows the new state and a record carries the group that
starts there; doom is kept. -/
theorem move (hf : ¬ Fail σ ℓ) {p : Prog Bool} (hm : Move p) (hp : ∀ a, p ≠ .ret a) {s : St}
    {h : List Ev} {s_f : St} {hist : List Ev} (hR : RootsInv (look ℓ) s h) (hr : P.Reachable h)
    (ha : P.after h = some p) (hk : Known σ P ℓ s.cv (.st h p))
    (hx : xrun (look ℓ) p s h = some (true, s_f, hist)) :
    ∃ (s' : St) (h' : List Ev) (p' : Prog Bool),
      s'.stream.length < s.stream.length ∧ RootsInv (look ℓ) s' h' ∧ P.Reachable h' ∧
      Boundary h' ∧ P.after h' = some p' ∧
      (∀ h'' p'', settle h' p' = some (h'', p'') → Known σ P ℓ s'.cv (.st h'' p'')) ∧
      Carried (σ := σ) C ℓ s'.cv h' p' ∧ xrun (look ℓ) p' s' h' = some (true, s_f, hist) ∧
      (C.D h → C.D h') ∧ h' = h ++ (h'.drop h.length) ∧ h'.length = h.length + 1 := by
  cases p with
  | ret a => exact absurd rfl (hp a)
  | sample _ => exact absurd hm id
  | query _ _ _ => exact absurd hm id
  | fail => exact absurd hm id
  | read k =>
    simp only [xrun] at hx
    split at hx
    · simp at hx
    · rename_i x xs hs
      simp only [absorbBlock_option, Option.bind_eq_some_iff] at hx
      obtain ⟨u, hu, hx⟩ := hx
      obtain ⟨j, hj, hej, -⟩ := (look_eq_some_iff ℓ _ u).mp hu
      obtain ⟨hkind, hknown⟩ := entry_read hf hk hj (x := x) (tag := 1) (by norm_num)
        (by rw [hej])
      have hj2 : ℓ[j].2 = u := by rw [hej]
      rw [hj2] at hkind hknown
      have hr' := Prog.Reachable.read x hr ha
      have ha' : P.after (h ++ [Ev.read x]) = some (k x) := by
        rw [Prog.after_append_single _ ha]; simp [Prog.after]
      refine ⟨_, h ++ [Ev.read x], k x, by simp [hs], rootsInv_append_read hR x u xs, hr',
        boundary_append_read h x, ha', fun h'' p'' hse ↦ hknown _ ?_, ⟨_, hkind, ?_⟩, hx,
        fun hD ↦ C.read x hr ha hD, by simp, by simp⟩
      · simp only [stepAt, stepSt, ↓reduceIte, stInfo, hse, Option.map_some]
      · simp only [stepAt, stepSt, ↓reduceIte, term, le_refl]
  | grind b k =>
    simp only [xrun] at hx
    split at hx
    · simp at hx
    · rename_i n xs hs
      simp only [absorbBlock_option, Option.bind_eq_some_iff] at hx
      obtain ⟨base, hbase, d, hd, cv', hcv', hx⟩ := hx
      split at hx
      · rename_i hpow
        obtain ⟨jb, hjb, hejb, hnb⟩ := (look_eq_some_iff ℓ _ base).mp hbase
        obtain ⟨jp, hjp, hejp, hnp⟩ := (look_eq_some_iff ℓ _ d).mp hd
        obtain ⟨jg, hjg, hejg, hng⟩ := (look_eq_some_iff ℓ _ cv').mp hcv'
        -- the base
        obtain ⟨-, hkb⟩ := entry_read hf hk hjb (x := 0) (tag := 3) (by norm_num)
          (by rw [hejb])
        have hkb' : Known σ P ℓ base (.base h b k s.cv) := by
          have := hkb (.base h b k s.cv) (by simp [stepAt, stepSt])
          rwa [show ℓ[jb].2 = base by rw [hejb]] at this
        -- the chain step after the nonce
        obtain ⟨hkg, hkng⟩ := entry_read hf hk hjg (x := n) (tag := 4) (by norm_num)
          (by rw [hejg])
        have hjg2 : ℓ[jg].2 = cv' := by rw [hejg]
        rw [hjg2] at hkg hkng
        -- the proof of work
        obtain ⟨hkp, -⟩ := entry_read hf hkb' hjp (x := n) (tag := 4) (by norm_num)
          (by rw [hejp])
        have hjp2 : ℓ[jp].2 = d := by rw [hejp]
        rw [hjp2] at hkp
        have hr' := Prog.Reachable.grind hr ha
        have ha' : P.after (h ++ [Ev.grind b]) = some k := by
          rw [Prog.after_append_single _ ha]; simp [Prog.after]
        have hpowd : ind (powOk b n d = true) = 1 := ind_of hpow
        -- which of the two entries of the nonce came first
        have hne : jp ≠ jg := by
          intro hpg
          subst hpg
          have hin : digestBytes base ++ blockOf n 4 = digestBytes s.cv ++ blockOf n 4 :=
            congrArg Prod.fst (hejp.symm.trans hejg)
          have hbc : base = s.cv := (chainInput_inj hin).1
          have hc : chunk0 ℓ[jb].1 = digestBytes ℓ[jb].2 := by
            rw [hejb, hbc]; exact chunk0_append _ _
          exact lt_irrefl _ (lt_of_chunk hf hjb hjb (Or.inl hc))
        have hcarry : Carried (σ := σ) C ℓ cv' (h ++ [Ev.grind b]) k := by
          rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
          · -- the proof of work first
            refine ⟨_, hkp, ?_⟩
            have hgn : look (ℓ.take jp) (digestBytes s.cv ++ blockOf n 4) = none :=
              look_take_none_of_le hlt.le hng
            simp only [stepAt, ↓reduceIte, hgn, term, hpowd, one_mul, hcv', gvOpt, le_refl]
          · -- the chain step first
            refine ⟨_, hkg, ?_⟩
            have hpn : powIn (ℓ.take jg) s.cv n = none := by
              unfold powIn
              rcases hb' : look (ℓ.take jg) (digestBytes s.cv ++ blockOf 0 3) with _ | base'
              · rfl
              · have : base' = base := by
                  have := look_of_prefix (List.take_prefix jg ℓ) hb'
                  rw [hbase] at this
                  exact (Option.some.inj this).symm
                subst this
                exact look_take_none_of_le hlt.le hnp
            have hrho : rho ℓ b s.cv n = 1 := by
              simp only [rho, powIn, hbase, Option.bind_some, hd, hpowd]
            simp only [stepAt, stepSt, show ¬ (4 = 3 ∧ n = 0) by omega, ↓reduceIte, hpn, term,
              hrho, one_mul, le_refl]
        refine ⟨_, h ++ [Ev.grind b], k, by simp [hs], rootsInv_append_grind hR b cv' xs, hr',
          boundary_append_grind h b, ha', fun h'' p'' hse ↦ hkng _ ?_, hcarry, hx,
          fun hD ↦ C.grind hr ha hD, by simp, by simp⟩
        simp only [stepAt, stepSt, show ¬ (4 = 3 ∧ n = 0) by omega, ↓reduceIte, stInfo, hse,
          Option.map_some]
      · simp at hx
  | commit ht w k =>
    simp only [xrun] at hx
    split at hx
    · rename_i x0 x1 xs hs
      simp only [absorbBlock_option, Option.bind_eq_some_iff] at hx
      obtain ⟨cv0, h0, cv1, h1, hx⟩ := hx
      split at hx
      · rename_i root hroot
        obtain ⟨j0, hj0, hej0, -⟩ := (look_eq_some_iff ℓ _ cv0).mp h0
        obtain ⟨j1, hj1, hej1, -⟩ := (look_eq_some_iff ℓ _ cv1).mp h1
        obtain ⟨-, hk0⟩ := entry_read hf hk hj0 (x := x0) (tag := 1) (by norm_num)
          (by rw [hej0])
        have hk0' : Known σ P ℓ cv0 (.half h ht w k x0) := by
          have := hk0 (.half h ht w k x0) (by simp [stepAt, stepSt])
          rwa [show ℓ[j0].2 = cv0 by rw [hej0]] at this
        obtain ⟨hk1, hkn1⟩ := entry_read hf hk0' hj1 (x := x1) (tag := 1) (by norm_num)
          (by rw [hej1])
        have hj12 : ℓ[j1].2 = cv1 := by rw [hej1]
        rw [hj12] at hk1 hkn1
        -- the word extracted before the root is absorbed is the word of the whole log
        have h01 : j0 < j1 := lt_of_chunk hf hj0 hj1 (Or.inl (by
          rw [hej1, hej0]; exact chunk0_append _ _))
        have hrt : ∀ (i : ℕ) (hi : i < ℓ.length), ℓ[i].2 = root → i < j1 := by
          intro i hi hir
          refine lt_of_rootOf hf hi hj1 ⟨cv0, x0, x1, ℓ[j0], by rw [hej1], ?_, ?_, ?_⟩
          · have := find?_take_output hf hj0 h01 hj1.le
            rwa [show ℓ[j0].2 = cv0 by rw [hej0]] at this
          · rw [hej0]; exact List.drop_left' (digestBytes_length _)
          · rw [hir]; exact hroot
        have hW : extract (look (ℓ.take j1)) root ht w = extract (look ℓ) root ht w :=
          extract_take_eq hf hrt ht w
        have hr' := Prog.Reachable.commit (extract (look ℓ) root ht w) hr ha
          (wellShaped_extract _ _ _ _)
        have ha' : P.after (h ++ [Ev.commit ht w (extract (look ℓ) root ht w)]) = some k := by
          rw [Prog.after_append_single _ ha]; simp [Prog.after]
        refine ⟨_, _, k, by simp [hs], rootsInv_append_commit hR root ht w cv1 xs, hr',
          boundary_append_commit _ _ _ _, ha', fun h'' p'' hse ↦ hkn1 _ ?_, ⟨_, hk1, ?_⟩, hx,
          fun hD ↦ C.commit _ hr ha (wellShaped_extract _ _ _ _) hD, by simp, by simp⟩
        · simp only [stepAt, ↓reduceIte, hroot, hW, stInfo, hse, Option.map_some]
        · simp only [stepAt, ↓reduceIte, hroot, hW, term, le_refl]
      · simp at hx
    · simp at hx

end Move

/-! ## The final inequality -/

section Final

variable (C : Cert P) {ℓ : Log}

theorem eq_take_of_prefix {h₀ h₁ hist : List Ev} (h0 : h₀ <+: hist) (h1 : h₁ <+: hist)
    (hl : h₀.length ≤ h₁.length) : h₀ = h₁.take h₀.length :=
  List.prefix_iff_eq_take.mp (List.prefix_of_prefix_length_le h0 h1 hl)

theorem term_le_termSum {κ : Shape × Digest} (hκ : κ ∈ (decode σ P ℓ).kinds) :
    term C.D ℓ κ ≤ termSum C.D σ P ℓ :=
  List.single_le_sum (fun _ _ ↦ bot_le) _ (List.mem_map_of_mem hκ)

/-- **The run from a boundary.** From a boundary of an accepting run at which the decoder knows
the chain state and a record carries the group, if a boundary at least as long on the
extracted history is doomed, the records' terms sum to at least one. -/
theorem from_boundary (hf : ¬ Fail σ ℓ) {s_f : St} {hist : List Ev} :
    ∀ (n : ℕ) (s : St) (h : List Ev) (p : Prog Bool), s.stream.length < n →
      RootsInv (look ℓ) s h → P.Reachable h → P.after h = some p →
      (∀ h' p', settle h p = some (h', p') → Known σ P ℓ s.cv (.st h' p')) →
      Carried (σ := σ) C ℓ s.cv h p → xrun (look ℓ) p s h = some (true, s_f, hist) →
      (∃ h₀, h₀ <+: hist ∧ h.length ≤ h₀.length ∧ Boundary h₀ ∧ C.D h₀) →
      1 ≤ termSum C.D σ P ℓ
  | 0, _, _, _, hn, _, _, _, _, _, _, _ => absurd hn (Nat.not_lt_zero _)
  | n + 1, s, h, p, hn, hR, hr, ha, hk, hcarry, hx, hbad => by
    obtain ⟨p_e, s_e, h_e, hg, hx', hR', hre, hae, hke, hm, hpre, hnb, hst⟩ :=
      follow C hf p s h hR hr ha hk hx
    obtain ⟨κ, hκ, hterm⟩ := hcarry
    have hhist : h <+: hist := xrun_prefix _ _ _ _ hx
    have hehist : h_e <+: hist := xrun_prefix _ _ _ _ hx'
    by_cases hesc : C.D h ∧ ¬ C.D h_e
    · -- the group leaves doom: its record's term is one
      calc (1 : ℝ≥0∞) = ind (C.D h) * gv C.D ℓ s.cv h p := by
            rw [ind_of hesc.1, one_mul, hg, esc_move hm hesc.2]
        _ ≤ term C.D ℓ κ := hterm
        _ ≤ termSum C.D σ P ℓ := term_le_termSum C hκ
    have hcase : C.D h_e ∨ ¬ C.D h := by tauto
    -- a doomed boundary past `h` is past the group
    have hpast : ¬ C.D h → ∀ h₀, h₀ <+: hist → h.length ≤ h₀.length → Boundary h₀ → C.D h₀ →
        h_e.length < h₀.length := by
      intro hD h₀ hh₀ hl hb hD₀
      by_contra hle
      rw [not_lt] at hle
      rcases Nat.lt_or_eq_of_le hl with hlt | heq
      · rw [eq_take_of_prefix hh₀ hehist hle] at hb
        exact hnb _ hlt hle hb
      · have : h₀ = h := by
          rw [eq_take_of_prefix hh₀ hhist (by omega), ← heq, List.take_length]
        exact hD (this ▸ hD₀)
    by_cases hret : p_e = .ret true
    · subst hret
      simp only [xrun, Option.some.injEq, Prod.mk.injEq] at hx'
      obtain ⟨-, -, rfl⟩ := hx'
      rcases hcase with hD | hD
      · exact absurd hD (C.final hre hae)
      · obtain ⟨h₀, hh₀, hl, hb, hD₀⟩ := hbad
        have := hpast hD h₀ hh₀ hl hb hD₀
        have := hh₀.length_le
        omega
    have hpm : ∀ a, p_e ≠ .ret a := by
      intro a hpa
      subst hpa
      cases a
      · exact hm
      · exact hret rfl
    obtain ⟨s', h', p', hlt, hR'', hr'', hb'', ha'', hk'', hc'', hx'', hDD, -, hlen'⟩ :=
      move C hf hm hpm hR' hre hae hke hx'
    refine from_boundary hf n s' h' p' (by rw [hst] at hlt; omega) hR'' hr'' ha'' hk'' hc''
      hx'' ?_
    rcases hcase with hD | hD
    · exact ⟨h', xrun_prefix _ _ _ _ hx'', le_rfl, hb'', hDD hD⟩
    · obtain ⟨h₀, hh₀, hl, hb, hD₀⟩ := hbad
      exact ⟨h₀, hh₀, by have := hpast hD h₀ hh₀ hl hb hD₀; omega, hb, hD₀⟩

/-- **The final inequality.** If the seeded verifier of the statement `x`, whose root is a root
of the program, accepts `π` with every hash answered by a log without failure, and some boundary
prefix of the extracted history past the root is doomed, the potential of the log is at least
one. -/
theorem final_ineq (hf : ¬ Fail σ ℓ) {x : X} {π : Proof} (hroot : RootOk P (σ.root x))
    (hv : verify (look ℓ) (σ.seed x) (nodeAt P (σ.root x)) π = some true)
    (hbad : ∃ h₀, h₀ <+: extractedFrom (look ℓ) (σ.seed x) (nodeAt P (σ.root x)) (σ.root x) π ∧
      (σ.root x).length ≤ h₀.length ∧ Boundary h₀ ∧ C.D h₀) :
    1 ≤ pot C.D σ P ℓ := by
  obtain ⟨seed, s, hseed, hx⟩ := xrun_of_verify_from (σ.root x) hv
  obtain ⟨hkind, hknown⟩ := seed_known (P := P) hf hseed hroot
  have hS : 1 ≤ termSum C.D σ P ℓ := by
    refine from_boundary C hf (π.stream.length + 1) ⟨seed, π.stream, π.openings, []⟩ (σ.root x)
      (nodeAt P (σ.root x)) (Nat.lt_succ_self _) ?_ hroot.1 (after_nodeAt hroot) ?_ ?_ hx hbad
    · show commits (σ.root x) = []
      exact hroot.2.2.2.1
    · intro h' p' hse
      exact hknown _ (by simp only [stInfo, hse, Option.map_some])
    · exact ⟨_, hkind, by simp only [term, le_refl]⟩
  simp only [pot, hf, ↓reduceIte]
  exact le_min le_rfl hS

end Final

end
end LeanVM.Protocol.Compile.Rom
