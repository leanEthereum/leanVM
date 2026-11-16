/-
  LeanVM.Guest.EndExecRE

  `check_opening_terminal`'s exponent and dimension facts, read off what `verify_sub` hands it
  (`Res.TermFront`), and the families on them sound at the honest frames: its order residuals
  (F7, F8) and its claims' low points (F9).
-/

module

public import LeanVM.Guest.EndExecRF
public import LeanVM.Guest.Res.TermDefs
public import LeanVM.Guest.B1.Terminal.HoldsOf

/-!
# `check_opening_terminal`'s facts and families

`ExpQ r J`, `DimQ r J`: at an instance `J` of a function listed in `Res.expFacts`
(`Res.dimFacts`), each listed parameter holds its fact (`ExpH`, `DimH`) on the reference memory.
`TermQ r J`: at an instance of `check_opening_terminal`, `Res.TermFront` of its arguments.
`expQ_of_termQ`, `dimQ_of_termQ`: the facts from `TermFront`: `kappa_base`'s words are `g`-powers of
`[0, log_mem, τ_0, …, τ_5]`, `tau_keccak_g = g^τ_5`; a pooled claim's low point, of length its
source's exponent plus its adjustment (`claimLowDim`), is a prefix of the bus point (`g_bus_mu`) or
of the tables' point (`g_zc_n`), at most `40` long.

`ltExp_top` (F7, F8): at an honest frame with `ExpQ`, the base of an order residual is `g^e`, `e`
below its fact's bound. `dim_top` (F9): with `DimQ`, the low base is `g^(e + c)` (`lowOk_top`), so
`[T]·g^(e + c + d)` is the chain's point at `e + c + d`, below `[o]`'s exponent plus `t`.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Mode LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B2C (idxOf entryOf FrameHolds fsN fn_of_idx cellJ namedOf)
open LeanVM.Guest.Bridge (FnAl)
open LeanVM.Guest.Res (Wit witOk constOf powOf inFr expFacts expOf baseAt ltFactB dimFacts dimShape dimB
  claimPairs busPairs tabPairs TermFront)
open LeanVM.Protocol.Verifier (gen Layout BusResult ColumnClaim)
open LeanVM.Prover.Exec

@[expose] public section

/-- An exponent fact: the word `x` (offset `none`), or the word read at `x·g^k`, is `g^e`, `e < b`. -/
def ExpH (rd : Reader) : Option ℕ → ℕ → E → Prop
  | none, b, x => ∃ e < b, x = gen ^ e
  | some k, b, x => ∃ e < b, LoadHolds rd x k (gen ^ e)

/-- A dimension fact: `gb = g^m`, and for each pair `(k, c)` the word at `kb·g^k` is `g^e`, `e + c ≤ m`. -/
def DimH (rd : Reader) (kb gb : E) (ps : List (ℕ × ℕ)) : Prop :=
  ∃ m < 2 ^ 33, gb = gen ^ m ∧ ∀ p ∈ ps, ∃ e, LoadHolds rd kb p.1 (gen ^ e) ∧ e + p.2 ≤ m

/-- **The exponent facts at an instance.** -/
def ExpQ (r : Ref) (J : Inst) : Prop :=
  ∀ f σ bufs kids, J.t = .node f σ bufs kids → ∀ fn, coreProgram.find? f = some fn → ∀ c ∈ expFacts,
    c.1 = f → ∀ v, fn.params[c.2.1]? = some v → ExpH r.img.read c.2.2.1 c.2.2.2 (σ v)

/-- **The exponent facts of the functions but `check_opening_terminal`** at an instance. -/
def ExpQv (r : Ref) (J : Inst) : Prop :=
  ∀ f σ bufs kids, J.t = .node f σ bufs kids → ∀ fn, coreProgram.find? f = some fn → ∀ c ∈ expFacts,
    c.1 = f → c.1 ≠ name% «check_opening_terminal» → ∀ v, fn.params[c.2.1]? = some v →
      ExpH r.img.read c.2.2.1 c.2.2.2 (σ v)

/-- **The dimension facts at an instance.** -/
def DimQ (r : Ref) (J : Inst) : Prop :=
  ∀ f σ bufs kids, J.t = .node f σ bufs kids → ∀ fn, coreProgram.find? f = some fn → ∀ c ∈ dimFacts,
    c.1 = f → ∀ vk vb, fn.params[c.2.1]? = some vk → fn.params[c.2.2.1]? = some vb →
      DimH r.img.read (σ vk) (σ vb) c.2.2.2

/-- **What `verify_sub` hands `check_opening_terminal`, at its instances.** -/
def TermQ (r : Ref) (J : Inst) : Prop :=
  ∀ f σ bufs kids, J.t = .node f σ bufs kids → f = name% «check_opening_terminal» → ∀ fn,
    coreProgram.find? f = some fn → TermFront r.img.read (fn.params.map σ)

end

public section

/-! ## The facts from `TermFront` -/

theorem term_fn {fn : Fn} (hf : coreProgram.find? name% «check_opening_terminal» = some fn) :
    fn.params = B1.VerifySub.termParams := by
  obtain ⟨fn', hf', hp, -⟩ := B1.VerifySub.termFound
  obtain rfl : fn = fn' := Option.some.inj (hf.symm.trans hf')
  exact hp

theorem expFacts_cot {c : String × ℕ × Option ℕ × ℕ} (hc : c ∈ expFacts)
    (hn : c.1 = name% «check_opening_terminal») :
    c.1 = name% «check_opening_terminal» ∧ ((c.2.1 = 7 ∧ c.2.2.1 = none ∧ c.2.2.2 = 31) ∨
      ∃ k < 8, c.2.1 = 8 ∧ c.2.2.1 = some k ∧ c.2.2.2 = if k = 0 then 1 else 31) := by
  simp only [expFacts, List.mem_append, List.mem_cons, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false] at hc
  rcases hc with ((rfl | rfl) | ⟨k, hk, rfl⟩) | rfl | rfl
  · exact ⟨rfl, Or.inl ⟨rfl, rfl, rfl⟩⟩
  · exact ⟨rfl, Or.inr ⟨0, by omega, rfl, rfl, rfl⟩⟩
  · exact ⟨rfl, Or.inr ⟨k + 1, by omega, rfl, rfl, by simp⟩⟩
  · exact absurd hn (by decide)
  · exact absurd hn (by decide)

theorem dimFacts_cot {c : String × ℕ × ℕ × List (ℕ × ℕ)} (hc : c ∈ dimFacts) :
    c.1 = name% «check_opening_terminal» ∧ c.2.1 = 8 ∧
      ((c.2.2.1 = 4 ∧ c.2.2.2 = busPairs) ∨ (c.2.2.1 = 5 ∧ c.2.2.2 = tabPairs)) := by
  simp only [dimFacts, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · exact ⟨rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨rfl, rfl, Or.inr ⟨rfl, rfl⟩⟩

theorem claimSrc_lt (j : ℕ) : B1.Tables.claimKappaSrc.getD j 0 < 8 := by
  have h : B1.Tables.claimKappaSrc.all (· < 8) = true := by decide
  rw [List.getD_eq_getElem?_getD]
  cases hj : B1.Tables.claimKappaSrc[j]? with
  | none => simp
  | some x => simpa using List.all_eq_true.mp h x (List.mem_of_getElem? hj)

section

variable {rd : Reader} {σ : Core.Val}

/-- The base's word at `kb·g^k`, `k < 8`, is `g` to its exponent. -/
theorem kb_load {lm : ℕ} {hs : List ℕ} (hl : hs.length = 6) {kb : E}
    (h : B1.ReadsAt rd kb (1 :: gen ^ lm :: hs.map (gen ^ ·))) {k : ℕ} (hk : k < 8) :
    LoadHolds rd kb k (gen ^ ([0, lm] ++ hs).getD k 0) := by
  have := h k (by simp [hl]; omega)
  rwa [B1.VerifySub.kb_words hl hk] at this

/-- **The exponent facts from `TermFront`.** -/
theorem expH_of_front (hT : TermFront rd (B1.VerifySub.termParams.map σ)) {c : String × ℕ × Option ℕ × ℕ}
    (hc : c ∈ expFacts) (hn : c.1 = name% «check_opening_terminal») {v : V}
    (hv : B1.VerifySub.termParams[c.2.1]? = some v) : ExpH rd c.2.2.1 c.2.2.2 (σ v) := by
  simp only [B1.VerifySub.termParams, List.map_cons, List.map_nil, TermFront] at hT
  obtain ⟨lm, hs, layout, bus, claims, hl, h31, hm30, -, -, -, hkb, -, htau, -⟩ := hT
  obtain ⟨-, ⟨hp, ho, hb⟩ | ⟨k, hk, hp, ho, hb⟩⟩ := expFacts_cot hc hn
  · rw [hp] at hv
    obtain rfl : v = .n 7 := by simpa [B1.VerifySub.termParams] using hv.symm
    rw [ho, hb]
    refine ⟨_, ?_, htau⟩
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact h31 _ (List.getElem_mem _)
  · rw [hp] at hv
    obtain rfl : v = .n 8 := by simpa [B1.VerifySub.termParams] using hv.symm
    rw [ho, hb]
    refine ⟨_, ?_, kb_load hl hkb hk⟩
    rcases Nat.lt_or_ge k 2 with h2 | h2
    · interval_cases k
      · simp
      · simp; omega
    · rw [show (if k = 0 then 1 else 31) = 31 by simp only [show ¬ k = 0 by omega, ↓reduceIte], List.getD_eq_getElem _ _ (by simp [hl]; omega), List.getElem_append_right (by simp; omega)]
      exact h31 _ (List.getElem_mem _)

/-- A pooled claim's pair: its low point's length, a prefix of the bus point or the tables' point. -/
theorem pair_dim {lm : ℕ} {hs : List ℕ} {layout : Layout} {bus : BusResult} {claims : List ColumnClaim}
    {zeta chi rm gmu gzcn : E} (hlm : layout.logMemory = lm) (hhs : layout.tableLogHeights = hs)
    (hT : B1.Tables.TCtx rd layout bus claims [zeta, chi, rm, gmu, gzcn]) :
    ∃ chis : List E, gmu = gen ^ bus.point.length ∧ gzcn = gen ^ chis.length ∧ chis.length ≤ bus.point.length ∧
      ∀ j < B1.Tables.nPooled, ∃ p : List E, p.length = ([0, lm] ++ hs).getD (B1.Tables.claimKappaSrc.getD j 0) 0 +
        B1.Tables.claimKappaAdj j ∧ (j < B1.Tables.nBusClaims → p.length ≤ bus.point.length) ∧
        (B1.Tables.nBusClaims ≤ j → p.length ≤ chis.length) := by
  obtain ⟨chis, -, hgmu, -, hgzc, hchL, hcl, -, hpts⟩ := hT
  refine ⟨chis, hgmu, hgzc, hchL, fun j hj ↦ ?_⟩
  have hjl : j < (claims.map (·.point)).length := by
    simp only [List.length_map, hcl]; exact lt_trans hj (by decide)
  obtain ⟨hlen, hbus, htab, -⟩ := hpts j _ (List.getElem?_eq_getElem hjl)
  refine ⟨_, by rw [hlen hj, B1.Tables.claimLowDim, hlm, hhs]; rfl, fun hb ↦ ?_, fun hb ↦ ?_⟩
  · have := congrArg List.length (hbus hb); rw [List.length_take] at this; omega
  · have := congrArg List.length (htab hb hj); rw [List.length_take] at this; omega

/-- **The dimension facts from `TermFront`.** -/
theorem dimH_of_front (hT : TermFront rd (B1.VerifySub.termParams.map σ)) {c : String × ℕ × ℕ × List (ℕ × ℕ)}
    (hc : c ∈ dimFacts) {vk vb : V} (hvk : B1.VerifySub.termParams[c.2.1]? = some vk)
    (hvb : B1.VerifySub.termParams[c.2.2.1]? = some vb) : DimH rd (σ vk) (σ vb) c.2.2.2 := by
  simp only [B1.VerifySub.termParams, List.map_cons, List.map_nil, TermFront] at hT
  obtain ⟨lm, hs, layout, bus, claims, hl, -, -, hlm, hhs, hb40, hkb, -, -, -, -, -, -, hctx⟩ := hT
  obtain ⟨chis, hgmu, hgzc, hchL, hpair⟩ := pair_dim hlm hhs hctx
  obtain ⟨-, hk8, hcase⟩ := dimFacts_cot hc
  rw [hk8] at hvk
  obtain rfl : vk = .n 8 := by simpa [B1.VerifySub.termParams] using hvk.symm
  have hp : ∀ j < B1.Tables.nPooled, ∀ p, p = claimPairs[j]! → LoadHolds rd (σ (.n 8)) p.1
      (gen ^ ([0, lm] ++ hs).getD p.1 0) := fun j hj p hp ↦ kb_load hl hkb (by
        rw [hp, getElem!_pos claimPairs j (by simpa [claimPairs] using hj)]
        simp only [claimPairs, List.getElem_map, List.getElem_range]
        exact claimSrc_lt j)
  have hcp : ∀ j (hj : j < claimPairs.length), claimPairs[j] =
      (B1.Tables.claimKappaSrc.getD j 0, B1.Tables.claimKappaAdj j) := fun j hj ↦ by
    simp [claimPairs]
  have hcpl : claimPairs.length = B1.Tables.nPooled := by simp [claimPairs]
  rcases hcase with ⟨hb4, hps⟩ | ⟨hb5, hps⟩
  · rw [hb4] at hvb
    obtain rfl : vb = .n 4 := by simpa [B1.VerifySub.termParams] using hvb.symm
    refine ⟨_, by omega, hgmu, fun p hpm ↦ ?_⟩
    rw [hps] at hpm
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hpm
    have hi4 : i < B1.Tables.nBusClaims := by simp only [busPairs, List.length_take] at hi; omega
    have hiP : i < B1.Tables.nPooled := lt_trans hi4 (by decide)
    obtain ⟨q, hq, hqb, -⟩ := hpair i hiP
    simp only [busPairs, List.getElem_take, hcp i (by omega)]
    exact ⟨_, kb_load hl hkb (claimSrc_lt i), by have := hqb hi4; omega⟩
  · rw [hb5] at hvb
    obtain rfl : vb = .n 5 := by simpa [B1.VerifySub.termParams] using hvb.symm
    refine ⟨_, by omega, hgzc, fun p hpm ↦ ?_⟩
    rw [hps] at hpm
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hpm
    have hiP : B1.Tables.nBusClaims + i < B1.Tables.nPooled := by
      simp only [tabPairs, List.length_drop, hcpl] at hi; omega
    obtain ⟨q, hq, -, hqt⟩ := hpair _ hiP
    have hci := hcp (B1.Tables.nBusClaims + i) (by rw [hcpl]; exact hiP)
    simp only [tabPairs, List.getElem_drop, hci]
    exact ⟨_, kb_load hl hkb (claimSrc_lt _), by have := hqt (by omega); omega⟩

end

variable {r : Ref}

/-- **The exponent facts at an instance with `TermQ`**, given those of the other functions. -/
theorem expQ_of_termQ {J : Inst} (h : TermQ r J) (hvt : ExpQv r J) : ExpQ r J := by
  intro f σ bufs kids hJ fn hf c hc hcf v hv
  by_cases hn : c.1 = name% «check_opening_terminal»
  swap
  · exact hvt f σ bufs kids hJ fn hf c hc hcf hn v hv
  obtain ⟨hc1, -⟩ := expFacts_cot hc hn
  rw [hc1] at hcf
  subst hcf
  have hp := term_fn hf
  have hT := h _ σ bufs kids hJ rfl fn hf
  rw [hp] at hT hv
  exact expH_of_front hT hc hn hv

/-- **The dimension facts at an instance with `TermQ`.** -/
theorem dimQ_of_termQ {J : Inst} (h : TermQ r J) : DimQ r J := by
  intro f σ bufs kids hJ fn hf c hc hcf vk vb hvk hvb
  obtain ⟨hc1, -⟩ := dimFacts_cot hc
  rw [hc1] at hcf
  subst hcf
  have hp := term_fn hf
  have hT := h _ σ bufs kids hJ rfl fn hf
  rw [hp] at hT hvk hvb
  exact dimH_of_front hT hc hvk hvb

/-! ## At the honest frames -/

section

variable {A : String → FnAl} {K : Mode.Cert} {i : ℕ} {e : Bridge.Ent} {j : ℕ} {w : Wit}

/-- The honest frame's instance, of function `j`. -/
theorem TopAt.found (t : TopAt A r K i e j) : ∃ f bufs kids, e.I.t = .node f e.σ bufs kids ∧
    coreProgram.find? f = some (coreOf j) ∧ (coreOf j).name = f := by
  obtain ⟨f, bufs, kids, hn⟩ := t.node
  obtain ⟨i', rfl, hi', hname, hfi, hc, -⟩ := fn_of_idx t.idx
  rw [hn] at hfi hname
  simp only [Tree.name] at hfi hname
  exact ⟨f, bufs, kids, hn, by rw [hc]; exact hfi, by rw [hc]; exact hname⟩

/-- A parameter's cell holds its word. -/
theorem TopAt.param (t : TopAt A r K i e j) (hr : r.Ok) {p : V} (hp : p ∈ (coreOf j).params)
    (hin : inFr j (cellJ j p) = true) : refMem r.img (e.I.fp + cellJ j p) = e.σ p := by
  obtain ⟨vs, -, hF, -⟩ := t.events hr
  simp only [inFr, Bool.and_eq_true, decide_eq_true_eq] at hin
  exact t.cell hr hF (List.mem_append_left _ (List.mem_append_left _ hp)) hin.1 hin.2

end

/-- A word read through a frame cell names its base. -/
theorem rbase_hp_load (hr : r.Ok) {fp q k : ℕ} {P v : E} (hP : refMem r.img (fp + q) = P)
    (hld : LoadHolds r.img.read P k v) : RBase (refMem r.img) fp (.hp q k) v := by
  have hκ : r.κ ≤ 28 := logMemorySize_le_28 (e := r.exec) hr.size
  obtain ⟨-, hrd⟩ := hld
  obtain ⟨x, hx, hxa⟩ := read_pow hrd hκ
  refine ⟨x, ⟨?_, hx⟩, ?_⟩
  · rw [hP, Mode.limb_mul_ofK]; exact hxa
  · rw [hxa] at hrd
    exact ((refRd_img hκ r.img) _ _ (by unfold maxCells at hx; omega) hrd).2

theorem expOf_spec {j : ℕ} {B : Base} {p : V} {b : ℕ} (h : expOf j B = some (p, b)) :
    ∃ c ∈ expFacts, c.1 = (coreOf j).name ∧ (coreOf j).params[c.2.1]? = some p ∧
      baseAt j p c.2.2.1 B = true ∧ c.2.2.2 = b := by
  obtain ⟨c, hc, hf⟩ := List.exists_of_findSome?_eq_some h
  split_ifs at hf with h1
  split at hf
  · rename_i p' hp'
    split_ifs at hf with h2
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hf)
    exact ⟨c, hc, by simpa using h1, hp', h2, rfl⟩
  · cases hf

section

variable {A : String → FnAl} {K : Mode.Cert} {i : ℕ} {e : Bridge.Ent} {j : ℕ} {w : Wit}

/-- **A base with an exponent fact, at an honest frame**: its word is `g^κ`, `κ < b`. -/
theorem expBase_top (t : TopAt A r K i e j) (hr : r.Ok) (hE : ExpQ r e.I)
    {B : Base} {p : V} {b : ℕ} (hB : expOf j B = some (p, b)) (hin : inFr j (cellJ j p) = true) :
    ∃ κ < b, RBase (refMem r.img) e.I.fp B (gen ^ κ) := by
  obtain ⟨c, hc, hn, hp, hbase, rfl⟩ := expOf_spec hB
  obtain ⟨f, bufs, kids, hJ, hf, hname⟩ := t.found
  have hH := hE f e.σ bufs kids hJ _ hf c hc (by rw [hn, hname]) p hp
  have hpc := t.param hr (List.mem_of_getElem? hp) hin
  obtain ⟨c1, c2, oo, bb⟩ := c
  simp only at hH hbase hp
  cases oo with
  | none =>
    cases B with
    | fr o =>
      simp only [baseAt, beq_iff_eq] at hbase
      obtain ⟨κ, hκ, hv⟩ := hH
      exact ⟨κ, hκ, by rw [← hbase]; show refMem r.img (e.I.fp + cellJ j p) = _; rw [hpc, hv]⟩
    | hp _ _ => simp [baseAt] at hbase
  | some k =>
    cases B with
    | fr _ => simp [baseAt] at hbase
    | hp q k' =>
      simp only [baseAt, Bool.and_eq_true, beq_iff_eq] at hbase
      obtain ⟨hq, rfl⟩ := hbase
      obtain ⟨κ, hκ, hld⟩ := hH
      exact ⟨κ, hκ, rbase_hp_load hr (by rw [← hq, hpc]) hld⟩

/-- **F7, F8 at an honest frame.** -/
theorem ltExp_top (t : TopAt A r K i e j) (hr : r.Ok) (hE : ExpQ r e.I)
    {x : Mode.Res} (hx : ltFactB j x = true) : RRes (refMem r.img) e.I.fp x := by
  match x, hx with
  | .lt (.ex B tt) (.num N), hx =>
    simp only [ltFactB] at hx
    cases hB : expOf j B with
    | none => rw [hB] at hx; cases hx
    | some pb =>
      obtain ⟨p, b⟩ := pb
      rw [hB] at hx
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hx
      obtain ⟨⟨⟨hin, hb⟩, hN⟩, hlt⟩ := hx
      obtain ⟨κ, hκ, hR⟩ := expBase_top t hr hE hB hin
      exact ⟨κ + tt, N, ⟨_, κ, hR, by rw [ofK_gpow], by omega, rfl⟩, rfl, by omega⟩
  | .lt (.ex _ _) (.ex _ _), hx => simp [ltFactB] at hx
  | .lt (.num _) _, hx => simp [ltFactB] at hx
  | .sub _ _, hx => simp [ltFactB] at hx
  | .nz _, hx => simp [ltFactB] at hx
  | .name _, hx => simp [ltFactB] at hx

theorem dimShape_eq {a b : Rng} {B : Base} {o t : ℕ} (h : dimShape a b = some (B, o, t)) :
    ∃ T, a.q.bs = [(.fr T, 1), (B, 1)] ∧ b.q.bs = [(.fr T, 1)] ∧ b.hi = .ex (.fr o) t := by
  unfold dimShape at h
  split at h
  · rename_i T B' T' o' t' hA hB hH
    split_ifs at h with hT
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨T, hA, by rw [hB, hT], hH⟩
  · cases h

/-- **A claim's low base at an honest frame**: the word at `[pk]·g^k` times `g^c`, with `ok k c`. -/
theorem lowOk_top (t : TopAt A r K i e j) (hr : r.Ok) (hW : witOk j w = true) {pk : V} {B : Base}
    {ok : ℕ → ℕ → Bool} (h : Res.lowOk j w pk B ok = true) (hpk : pk ∈ (coreOf j).params) :
    ∃ k c, ok k c = true ∧ ∀ v, LoadHolds r.img.read (e.σ pk) k (gen ^ v) →
      RBase (refMem r.img) e.I.fp B (gen ^ (v + c)) := by
  obtain ⟨vs, -, hF, hev, hwa, -⟩ := t.wit hr hW
  have hall : ∀ a ∈ w.as, a.Holds r.img.read e.σ := fun a ha ↦ hev _ (hwa _ ha)
  cases B with
  | hp q k =>
    simp only [Res.lowOk, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hin, hq⟩, hok⟩ := h
    have hpc := t.param hr hpk (by rw [hq]; exact hin)
    rw [hq] at hpc
    exact ⟨k, 0, hok, fun v hld ↦ by rw [Nat.add_zero]; exact rbase_hp_load hr hpc hld⟩
  | fr P =>
    simp only [Res.lowOk, Bool.and_eq_true, List.any_eq_true] at h
    obtain ⟨hin, m, hm, hmb⟩ := h
    cases m with
    | mul P' y z =>
      simp only [Bool.and_eq_true, beq_iff_eq, List.any_eq_true] at hmb
      obtain ⟨hP, l, hl, hlb⟩ := hmb
      cases l with
      | load y' p k =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hlb
        obtain ⟨⟨rfl, hpp⟩, hc⟩ := hlb
        split at hc
        · rename_i c hcz
          obtain ⟨wc, hwc, hpw⟩ := Option.bind_eq_some_iff.mp hcz
          have hzw : e.σ z = wc := hall _ (constOf_sound hwc)
          have hmul : e.σ P' = e.σ y' * e.σ z := hall _ hm
          have hld : LoadHolds r.img.read (e.σ p) k (e.σ y') := hall _ hl
          rw [hpp] at hld
          simp only [inFr, Bool.and_eq_true, decide_eq_true_eq] at hin
          have hcell := t.cell hr hF (namedOf_atom (x := P') (hwa _ hm) (by simp [atomUses]))
            (by rw [hP]; exact hin.1) (by rw [hP]; exact hin.2)
          rw [hP] at hcell
          refine ⟨k, c, hc, fun v hv ↦ ?_⟩
          show refMem r.img (e.I.fp + P) = _
          rw [hcell, hmul, B1.loadHolds_unique hld hv, hzw, powOf_sound hpw, ← Value.gen_pow_eq_ofK, ← pow_add]
        · cases hc
      | _ => simp at hlb
    | _ => simp at hmb

/-- **F9 at an honest frame**: the claim's low point is the chain's point at its length. -/
theorem dim_top (t : TopAt A r K i e j) (hr : r.Ok) (hW : witOk j w = true) (hD : DimQ r e.I) {x : Mode.Res}
    (hx : dimB j w x = true) : RRes (refMem r.img) e.I.fp x := by
  match x, hx with
  | .sub a [b], hx =>
    simp only [dimB] at hx
    cases hs : dimShape a b with
    | none => rw [hs] at hx; cases hx
    | some s =>
      obtain ⟨B, o, tt⟩ := s
      rw [hs] at hx
      obtain ⟨T, hA, hB, hH⟩ := dimShape_eq hs
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.any_eq_true] at hx
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hal, hah⟩, had⟩, hbl⟩, hbS⟩, hbd⟩, hfp⟩, hk⟩, ht1⟩, hoin⟩, c, hc, hcx⟩ := hx
      obtain ⟨hcn, hcx⟩ := hcx
      split at hcx
      · rename_i pk pb hpk hpb
        simp only [Bool.and_eq_true, beq_iff_eq] at hcx
        obtain ⟨ho, hlow⟩ := hcx
        obtain ⟨f, bufs, kids, hJ, hf, hname⟩ := t.found
        obtain ⟨m, hm, hgb, hps⟩ := hD f e.σ bufs kids hJ _ hf c hc (by rw [hcn, hname]) pk pb hpk hpb
        obtain ⟨kk, cc, hok, hR⟩ := lowOk_top t hr hW hlow (List.mem_of_getElem? hpk)
        simp only [List.contains_iff_mem] at hok
        obtain ⟨κ, hld, hκm⟩ := hps _ hok
        have hRB := hR κ hld
        have hpbc := t.param hr (List.mem_of_getElem? hpb) (by rw [ho]; exact hoin)
        rw [ho] at hpbc
        refine ⟨0, 1, by rw [hal]; rfl, by rw [hah]; rfl, fun vq hvq jj _ hjj ↦
          ⟨b, List.mem_singleton_self _, fun vb ylo yhi hvb hlo hhi ↦ ?_⟩⟩
        obtain rfl : jj = 0 := by omega
        rw [hbl] at hlo
        change ylo = 0 at hlo
        rw [hH] at hhi
        obtain ⟨vo, mo, hvo, hvo', hmo, rfl⟩ := hhi
        change refMem r.img (e.I.fp + o) = vo at hvo
        rw [hpbc, hgb, hvo', ofK_gpow] at hvo
        obtain rfl : m = mo := Value.gen_pow_inj (by omega) (by omega) hvo
        simp only at hκm
        refine ⟨a.q.k - b.q.k + (κ + cc), by omega, by omega, ?_⟩
        obtain ⟨wq, hwq, rfl⟩ := hvq
        obtain ⟨wb, hwb, rfl⟩ := hvb
        rw [hA] at hwq
        rw [hB] at hwb
        obtain ⟨u1, w1, hu1, ⟨u2, w2, hu2, hw2, rfl⟩, rfl⟩ := hwq
        obtain ⟨u1', w1', hu1', hw1', rfl⟩ := hwb
        simp only [RBs] at hw2 hw1'
        subst hw2 hw1'
        rw [rbase_uniq hu2 hRB, rbase_uniq hu1 hu1', hfp, had, hbS, hbd]
        simp only [pow_one, mul_one, Nat.mul_zero, Nat.add_zero, one_mul, ofK_gpow]
        rw [show a.q.k = b.q.k + (a.q.k - b.q.k) by omega, pow_add, pow_add,
          show b.q.k + (a.q.k - b.q.k) - b.q.k = a.q.k - b.q.k by omega]
        ring
      · cases hcx
  | .sub _ [], hx => simp [dimB] at hx
  | .sub _ (_ :: _ :: _), hx => simp [dimB] at hx
  | .lt _ _, hx => simp [dimB] at hx
  | .nz _, hx => simp [dimB] at hx
  | .name _, hx => simp [dimB] at hx
end

end

end LeanVM.Guest.EndExec
