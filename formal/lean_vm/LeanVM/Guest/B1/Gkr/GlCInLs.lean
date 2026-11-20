/-
  LeanVM.Guest.B1.Gkr.GlCInLs

  `gkr_layers__L{o}`, its loop and `gkr_last_layers__L{r}_L{o}` load from any region their layers
  load from.
-/

module

public import LeanVM.Guest.B1.Gkr.Gls
public import LeanVM.Guest.B1.Tables.Kids.Walk
public import LeanVM.Guest.B1.Tables.Kids.Loop9
public import LeanVM.Guest.Data.NameStrings

/-!
# The radix-four layers' dispatch, loading from a region

The three functions load nothing; they call the layers (`glcChain`), the loop itself and the
last layers. `GlLayIn`: layer `j`'s relation loading from `R`. With every layer `j < 4n + r`'s
relation loading from `R` (`hL`):

* `glcLast_relIn`: `gkr_last_layers__L{r}_L{o}` (the layers `4n .. 4n + r - 1`);
* `glsl_relIn`: `gkr_layers__L{o}`'s loop, every iteration `m < n`, by the depth of its
  derivation;
* `gls_relIn`: `gkr_layers__L{o}` at `n_four = g^n`, `rem_g = g^r`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest.B1

@[expose] public section

/-- **Layer `j`'s relation, loading from `R`.** -/
def GlLayIn (rd : Reader) (R : ℕ → Prop) (o : ℕ) (layers rounds pts start gmu tabs stream : E)
    (j : ℕ) : Prop :=
  coreProgram.RelIn rd R (glName (j % 4) o) [layers, rounds, pts, gen ^ (j / 4), gen ^ j, start,
    gmu, tabs, stream] []

theorem glc_xj {n p : ℕ} (hp : p < 4) :
    gen ^ n * gen ^ n * (gen ^ n * gen ^ n) * gen ^ p = gen ^ (4 * n + p) ∧ (4 * n + p) % 4 = p ∧
      (4 * n + p) / 4 = n := by
  refine ⟨by rw [glc_pow4, ← pow_add], by omega, by omega⟩

/-! ## The chain of layer calls -/

theorem glcStep_all {f : Stmt → Bool} (o : ℕ) (hd : List V) (x0 c0 p : ℕ)
    (ha : ∀ d w, f (.atom (.const d w)) = true) (hm : ∀ d x y, f (.atom (.mul d x y)) = true)
    (hc : ∀ g args rets, f (.call g args rets) = true) :
    (glcStep o hd x0 c0 p).all f = true := by
  unfold glcStep
  split <;> simp [ha, hm, hc]

theorem glcChain_all {f : Stmt → Bool} (o : ℕ) (hd : List V) (x0 c0 r : ℕ)
    (ha : ∀ d w, f (.atom (.const d w)) = true) (hm : ∀ d x y, f (.atom (.mul d x y)) = true)
    (hc : ∀ g args rets, f (.call g args rets) = true) :
    (glcChain o hd x0 c0 r).all f = true := by
  rw [glcChain, List.all_eq_true]
  intro s hs
  obtain ⟨l, hl, hsl⟩ := List.mem_flatten.mp hs
  obtain ⟨p, -, rfl⟩ := List.mem_map.mp hl
  exact List.all_eq_true.mp (glcStep_all o hd x0 c0 p ha hm hc) s hsl

theorem glcChain_callS (o : ℕ) (hd : List V) (x0 c0 : ℕ) : ∀ r,
    (glcChain o hd x0 c0 r).filterMap Main.Stmt.callS = (List.range r).map fun p ↦
      (none, glName p o, hd ++ [.n (glcXj x0 c0 p), .n 5, .n 6, .n 7, .n 8], [])
  | 0 => rfl
  | r + 1 => by
    rw [glcChain, List.range_succ, List.map_append, List.flatten_append, List.filterMap_append,
      ← glcChain, glcChain_callS o hd x0 c0 r, List.map_append]
    congr 1
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
    unfold glcStep
    split <;> rfl

/-- A loadless block's loads lie anywhere. -/
theorem loads_none {pre : List Stmt} (h : pre.filterMap Stmt.loadS = []) {σ : Val}
    {R : ℕ → Prop} :
    ∀ q ∈ pre.filterMap Stmt.loadS, ∃ i, (σ q.1).limb 0 * addressOfIndex q.2 = addressOfIndex i ∧
      R i := by
  rw [h]; intro q hq; exact absurd hq (by simp)

theorem glcChain_loadS (o : ℕ) (hd : List V) (x0 c0 r : ℕ) :
    (glcChain o hd x0 c0 r).filterMap Stmt.loadS = [] := by
  rw [List.filterMap_eq_nil_iff]
  intro s hs
  have := List.all_eq_true.mp (glcChain_all (f := fun s ↦ (Stmt.loadS s).isNone) o hd x0 c0 r
    (fun _ _ ↦ rfl) (fun _ _ _ ↦ rfl) (fun _ _ _ ↦ rfl)) s hs
  simpa using this

/-! ## `gkr_last_layers__L{r}_L{o}` -/

/-- `gkr_last_layers__L{r}_L{o}`'s statements before its `ret`. -/
def glcLastPre (r o : ℕ) : List Stmt :=
  glcChain o [.n 0, .n 1, .n 2, .n 3] 4 9 r ++ [.atom (.const (.n (9 + 2 * (r - 1))) (word 0 0))]

/-- **`gkr_last_layers__L{r}_L{o}` loads from `R`**, its layers `4n + p`, `p < r`, loading from
`R`. -/
theorem glcLast_relIn {o r n : ℕ} (ho : o < 2) (hr : r < 4) {rd : Reader} {R : ℕ → Prop}
    {layers rounds pts start gmu tabs stream : E} {rets : List E}
    (hL : ∀ p < r, GlLay rd o layers rounds pts start gmu tabs stream (4 * n + p) →
      GlLayIn rd R o layers rounds pts start gmu tabs stream (4 * n + p))
    (h : coreProgram.Rel rd (glcLastN r o) [layers, rounds, pts, gen ^ n, gen ^ (4 * n), start,
      gmu, tabs, stream] rets) :
    coreProgram.RelIn rd R (glcLastN r o) [layers, rounds, pts, gen ^ n, gen ^ (4 * n), start,
      gmu, tabs, stream] rets := by
  obtain ⟨fn, hf, hp, hb⟩ := glcFnCheck_sound ((glc_layers_check o ho).2.2 r hr)
  have hall : ∀ {f : Stmt → Bool}, (∀ d w, f (.atom (.const d w)) = true) →
      (∀ d x y, f (.atom (.mul d x y)) = true) →
      (∀ g args rets, f (.call g args rets) = true) → (glcLastPre r o).all f = true :=
    fun ha hm hc ↦ by
      rw [glcLastPre, List.all_append, glcChain_all o _ 4 9 r ha hm hc, List.all_cons, ha]; rfl
  have hnd : (glcLastPre r o).all noDispB = true :=
    hall (fun _ _ ↦ rfl) (fun _ _ _ ↦ rfl) fun _ _ _ ↦ rfl
  refine relIn_of_flatRel hf (by rw [hb, glcLastBody, glcLastPre, List.append_assoc]; rfl)
    (hall (fun _ _ ↦ rfl) (fun _ _ _ ↦ rfl) fun _ _ _ ↦ rfl) h
    (hnl := hall (fun _ _ ↦ rfl) (fun _ _ _ ↦ rfl) fun _ _ _ ↦ rfl)
    fun σ hpar hhl ↦ ?_
  rw [hp] at hpar
  simp only [glcPar9, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, List.cons.injEq, and_true] at hpar
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hpar
  rw [hb, glcLastBody, holdsList_append, holdsList_noRet _ (glcChain_noRet ..)] at hhl
  obtain ⟨hx, hcalls⟩ := glcChain_sound r hhl.1
  refine ⟨fun s hs ↦ dispOk_of_noDisp (List.all_eq_true.mp hnd s hs), loads_none ?_,
    fun c hc _ ↦ ?_⟩
  · rw [glcLastPre, List.filterMap_append, glcChain_loadS]; rfl
  · rw [filterMap_callSF hnd, glcLastPre, List.filterMap_append, glcChain_callS] at hc
    simp only [List.filterMap_cons, Main.Stmt.callS, List.filterMap_nil, List.append_nil,
      List.map_map, List.mem_map, List.mem_range] at hc
    obtain ⟨p, hpr, rfl⟩ := hc
    have hl := hL p hpr (by
      unfold GlLay
      obtain ⟨e1, e2, e3⟩ := glc_xj (n := n) (by omega : p < 4)
      have := hcalls p hpr
      simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, h0, h1, h2, h3,
        h4, h5, h6, h7, h8] at this
      rw [e2, e3, pow_add]
      exact this)
    unfold GlLayIn at hl
    obtain ⟨-, e2, e3⟩ := glc_xj (n := n) (by omega : p < 4)
    rw [e2, e3, pow_add] at hl
    simp only [Function.comp, Main.mkCall, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append, h0, h1, h2, h3, h5, h6, h7, h8, hx p hpr, h4]
    exact hl

/-! ## `gkr_layers__L{o}`'s loop -/

/-- The loop's statements before its `ret`. -/
def glcLsLPre (o : ℕ) : List Stmt := (glcLsLBody o).dropLast

theorem glcLsL_facts : ∀ o < 2, tbStmtsEqb (glcLsLBody o) (glcLsLPre o ++ [.ret []]) = true ∧
    (glcLsLPre o).all Stmt.flat = true ∧ (glcLsLPre o).all noDispB = true ∧
    (glcLsLPre o).all noLoadIte = true ∧ (glcLsLPre o).filterMap Stmt.loadS = [] := by
  decide +kernel

theorem glcLsLPre_eq (o : ℕ) : glcLsLPre o = [.atom (.mul (.n 9) (.n 0) (.n 0)),
    .atom (.mul (.n 10) (.n 9) (.n 9))] ++ glcChain o [.n 2, .n 3, .n 4, .n 0] 10 11 4 ++
    [.atom (.const (.n 17) (word 2 0)), .atom (.mul (.n 18) (.n 0) (.n 17)),
      .atom (.add (.n 19) (.n 18) (.n 1)), .atom (.const (.n 20) (word 2 0)),
      .atom (.mul (.n 21) (.n 0) (.n 20)),
      .callIf (.n 19) (glcLsLN o) [.n 21, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8]] := by
  rw [glcLsLPre, glcLsLBody, List.append_assoc, List.append_assoc, List.dropLast_append_of_ne_nil
    (by simp), List.dropLast_append_of_ne_nil (by simp)]
  rfl

/-- **`gkr_layers__L{o}`'s loop loads from `R`**, every iteration `m < n`, its layers `j < 4n`
loading from `R`. -/
theorem glsl_relIn {o n : ℕ} (ho : o < 2) {rd : Reader} {R : ℕ → Prop}
    {layers rounds pts start gmu tabs stream : E}
    (hL : ∀ j < 4 * n, GlLay rd o layers rounds pts start gmu tabs stream j →
      GlLayIn rd R o layers rounds pts start gmu tabs stream j) :
    ∀ d m, m < n → coreProgram.relN rd d (glcLsLN o) [gen ^ m, gen ^ n, layers, rounds, pts, start,
        gmu, tabs, stream] [] →
      coreProgram.RelIn rd R (glcLsLN o) [gen ^ m, gen ^ n, layers, rounds, pts, start, gmu, tabs,
        stream] [] := by
  obtain ⟨hbe, hfl, hnd, hnl, hld⟩ := glcLsL_facts o ho
  intro d
  induction d with
  | zero => intro m _ h; exact h.elim
  | succ d ih =>
    intro m hm h
    obtain ⟨fn, hf, hsem⟩ := h
    obtain ⟨fn', hf', hp, hb⟩ := glcFnCheck_sound (glc_layers_check o ho).2.1
    rw [hf] at hf'
    obtain rfl := Option.some.inj hf'
    refine relIn_of_flat hf (by rw [hb]; exact tbStmtsEqb_sound hbe) hfl hsem (hnl := hnl)
      fun σ hpar hhl ↦ ?_
    rw [hp] at hpar
    simp only [glcPar9, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
      List.nil_append, List.cons_append, List.cons.injEq, and_true] at hpar
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hpar
    rw [hb, glcLsLBody, holdsList_append, holdsList_append,
      holdsList_noRet _ (by rfl : Stmt.noRetList [.atom (.mul (.n 9) (.n 0) (.n 0)),
        .atom (.mul (.n 10) (.n 9) (.n 9))] = true),
      holdsList_noRet _ (glcChain_noRet ..)] at hhl
    obtain ⟨hpre, hch, hpost⟩ := hhl
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hpre
    obtain ⟨m9, m10⟩ := hpre
    obtain ⟨hx, hcalls⟩ := glcChain_sound 4 hch
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at hpost
    obtain ⟨c17, m18, a19, c20, m21, -, hnext, -⟩ := hpost
    rw [tb_word_gen] at c17 c20
    have e10 : σ (.n 10) = gen ^ m * gen ^ m * (gen ^ m * gen ^ m) := by rw [m10, m9, h0]
    refine ⟨fun s hs ↦ dispOk_of_noDisp (List.all_eq_true.mp hnd s hs), loads_none hld,
      fun c hc ht ↦ ?_⟩
    rw [filterMap_callSF hnd, glcLsLPre_eq, List.filterMap_append, List.filterMap_append,
      glcChain_callS] at hc
    simp only [List.filterMap_cons, Main.Stmt.callS, List.filterMap_nil, List.nil_append,
      List.map_append, List.map_map, List.mem_append, List.mem_map, List.mem_range,
      List.map_cons, List.map_nil, List.mem_singleton, Function.comp_apply] at hc
    rcases hc with ⟨p, hp4, rfl⟩ | rfl
    · obtain ⟨e1, e2, e3⟩ := glc_xj (n := m) hp4
      have hl := hL (4 * m + p) (by omega) (by
        unfold GlLay
        have := relN_le_rel coreProgram d _ _ _ (hcalls p hp4)
        simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, h0, h2, h3, h4,
          h5, h6, h7, h8, e10, e1] at this
        rw [e2, e3]
        exact this)
      unfold GlLayIn at hl
      rw [e2, e3] at hl
      simp only [Main.mkCall, List.map_cons, List.map_nil, List.cons_append, List.nil_append, h0,
        h2, h3, h4, h5, h6, h7, h8, hx p hp4, e10, e1]
      exact hl
    · simp only [Main.mkCall, decide_eq_true_eq] at ht ⊢
      have e21 : σ (.n 21) = gen ^ (m + 1) := by rw [m21, c20, h0, pow_succ]
      have e19 : σ (.n 19) = gen ^ (m + 1) + gen ^ n := by rw [a19, m18, c17, h0, h1, pow_succ]
      have hm1 : m + 1 < n := by
        rcases Nat.lt_or_ge (m + 1) n with h' | h'
        · exact h'
        · exfalso
          apply ht
          rw [e19, show m + 1 = n by omega, e_add_eq_zero_iff]
      have hrel := hnext ht
      simp only [List.map_cons, List.map_nil, e21, h1, h2, h3, h4, h5, h6, h7, h8] at hrel ⊢
      exact ih (m + 1) hm1 hrel

/-! ## `gkr_layers__L{o}` -/

/-- `gkr_layers__L{o}`'s statements before its `ret`. -/
def glcLsPre (o : ℕ) : List Stmt :=
  [.atom (.const (.n 9) (word 1 0)), .atom (.add (.n 10) (.n 9) (.n 3)),
    .atom (.const (.n 11) (word 1 0)),
    .callIf (.n 10) (glcLsLN o) [.n 11, .n 3, .n 0, .n 1, .n 2, .n 5, .n 6, .n 7, .n 8],
    .atom (.mul (.n 12) (.n 3) (.n 3)), .atom (.mul (.n 13) (.n 12) (.n 12)),
    .dispatch (.n 4) [glcLastN 0 o, glcLastN 1 o, glcLastN 2 o, glcLastN 3 o]
      [.n 0, .n 1, .n 2, .n 3, .n 13, .n 5, .n 6, .n 7, .n 8] [.n 14],
    .atom (.const (.n 15) (word 0 0))]

theorem glcLsBody_eq (o : ℕ) : glcLsBody o = glcLsPre o ++ [.ret [.n 15]] := rfl

theorem glcLs_flat (o : ℕ) : (glcLsPre o).all Stmt.flat = true := rfl

theorem glcLs_noLoadIte (o : ℕ) : (glcLsPre o).all noLoadIte = true := rfl

theorem glcLs_loadS (o : ℕ) : (glcLsPre o).filterMap Stmt.loadS = [] := rfl

theorem glcLs_callSF (σ : Val) (o : ℕ) : (glcLsPre o).filterMap (Stmt.callSF σ) =
    [(some (.n 10), glcLsLN o, [.n 11, .n 3, .n 0, .n 1, .n 2, .n 5, .n 6, .n 7, .n 8], []),
      (none, [glcLastN 0 o, glcLastN 1 o, glcLastN 2 o, glcLastN 3 o].getD (logG (σ (.n 4))) "",
        [.n 0, .n 1, .n 2, .n 3, .n 13, .n 5, .n 6, .n 7, .n 8], [.n 14])] := rfl

/-- **`gkr_layers__L{o}` loads from `R`** at `n_four = g^n`, `rem_g = g^r`, its layers
`j < 4n + r` loading from `R`. -/
theorem gls_relIn {o n r : ℕ} (ho : o < 2) (hr : r < 4) {rd : Reader} {R : ℕ → Prop}
    {layers rounds pts start gmu tabs stream : E} {rets : List E}
    (hL : ∀ j < 4 * n + r, GlLay rd o layers rounds pts start gmu tabs stream j →
      GlLayIn rd R o layers rounds pts start gmu tabs stream j)
    (h : coreProgram.Rel rd (glcLsN o) [layers, rounds, pts, gen ^ n, gen ^ r, start, gmu, tabs,
      stream] rets) :
    coreProgram.RelIn rd R (glcLsN o) [layers, rounds, pts, gen ^ n, gen ^ r, start, gmu, tabs,
      stream] rets := by
  obtain ⟨fn, hf, hp, hb⟩ := glcFnCheck_sound (glc_layers_check o ho).1
  refine relIn_of_flatRel hf (by rw [hb, glcLsBody_eq]) (glcLs_flat o) h
    (hnl := glcLs_noLoadIte o) fun σ hpar hhl ↦ ?_
  rw [hp] at hpar
  simp only [glcPar9, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, List.cons.injEq, and_true] at hpar
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hpar
  rw [hb, glcLsBody] at hhl
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at hhl
  obtain ⟨c9, a10, c11, -, hloop, m12, m13, ⟨jj, hjj, hx, hlast⟩, -⟩ := hhl
  rw [tb_word_one] at c9 c11
  have hjr : jj = r := by
    simp only [List.length_cons, List.length_nil] at hjj
    rw [h4, ← gen_pow_eq_ofK] at hx
    exact (gen_pow_inj (by omega) (by omega) hx).symm
  subst hjr
  have e4 : σ (.n 4) = ofK (addressOfIndex jj) := by rw [h4, gen_pow_eq_ofK]
  have e13 : σ (.n 13) = gen ^ (4 * n) := by rw [m13, m12, h3, glc_pow4]
  refine ⟨fun s hs ↦ ?_, loads_none (glcLs_loadS o), fun c hc ht ↦ ?_⟩
  · simp only [glcLsPre, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | trivial | exact ⟨jj, by simp; omega, by omega, e4⟩
  · rw [glcLs_callSF] at hc
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · -- the loop
      simp only [Main.mkCall, decide_eq_true_eq] at ht ⊢
      have hn0 : 0 < n := by
        rcases Nat.eq_zero_or_pos n with h0' | h0'
        · exfalso; apply ht; rw [a10, c9, h3, h0', pow_zero, e_add_self]
        · exact h0'
      obtain ⟨d, hd⟩ := hloop ht
      simp only [List.map_cons, List.map_nil, c11, h0, h1, h2, h3, h5, h6, h7, h8] at hd ⊢
      rw [show (1 : E) = gen ^ 0 from (pow_zero _).symm] at hd ⊢
      exact glsl_relIn ho (fun j hj ↦ hL j (by omega)) d 0 hn0 hd
    · -- the last layers
      have hf' : [glcLastN 0 o, glcLastN 1 o, glcLastN 2 o, glcLastN 3 o].getD
          (logG (σ (.n 4))) "" = glcLastN jj o := by
        rw [e4, logG_spec (by omega)]
        interval_cases jj <;> rfl
      have e : [glcLastN 0 o, glcLastN 1 o, glcLastN 2 o, glcLastN 3 o][jj] = glcLastN jj o := by
        interval_cases jj <;> rfl
      rw [e] at hlast
      simp only [Main.mkCall, hf', List.map_cons, List.map_nil, h0, h1, h2, h3, h5, h6, h7, h8,
        e13] at hlast ⊢
      exact glcLast_relIn ho hr (fun p hp ↦ hL _ (by omega)) hlast

end
end LeanVM.Guest.B1.Tables
