/-
  LeanVM.Guest.CoreMode.Fn.check_opening_terminal.ResE

  `check_opening_terminal`'s exponent and dimension facts, read off what `verify_sub` hands it
  (`Res.TermFront`), and the families on them sound at the honest frames: its order residuals
  and its claims' low points.
-/

module

public import LeanVM.Guest.CoreMode.Fam.ResF
public import LeanVM.Guest.EndExecCoreFn
public import LeanVM.Guest.CoreMode.Fam.TermDefs
public import LeanVM.Guest.B1.Terminal.HoldsOf
public import LeanVM.Guest.CoreMode.Fn.check_opening_terminal.Data
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«check_opening_terminal»

/-!
# `check_opening_terminal`'s facts and families

`TermFront rd args`: what `verify_sub`'s front (`B1.VerifySub.vs_front`) gives of
`check_opening_terminal`'s arguments, read by name: `kappa_base` reads `[1, g^log_mem, g^τ_0, …,
g^τ_5]`, `g_log_mem = g^log_mem`, `tau_keccak_g = g^τ_5`, the heights below `31`, `log_mem ≤ 30`;
`col_offsets` holds `certify_placement`'s offsets (`PCtx`, `KappasBelow`), the stack at most `2^30`;
`g_squares·g^34` the selector's nibble shares; `verify_tables`' context (`TCtx`) on
`[zeta, chi, rm, g_bus_mu, g_zc_n]`.
`TermQ r J`: at an instance of `check_opening_terminal`, `Res.TermFront` of its arguments.
`expH_of_front`, `dimH_of_front`: its own facts (`Own.check_opening_terminal.expFacts`, `dimFacts`) from `TermFront`:
`kappa_base`'s words are `g`-powers of `[0, log_mem, τ_0, …, τ_5]`, `tau_keccak_g = g^τ_5`, `gmv = g^sl`, `sl ≤ 30`;
a pooled claim's low point, of length its source's exponent plus its adjustment (`claimLowDim`), is a prefix of the
bus point (`g_bus_mu`) or of the tables' point (`g_zc_n`), at most `40` long.
-/

namespace LeanVM.Guest.Res

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## What `verify_sub` hands the terminal -/

/-- **What `verify_sub`'s front gives of `check_opening_terminal`'s arguments.** -/
def TermFront (rd : Reader) : List E → Prop
  | [gsq, zeta, chi, rm, gmu, gzcn, glm, gtau, kb, _lam, off, _zv, _ct, _pt, _pt1, _, _, _, _oz, gm] =>
      ∃ (logMem : ℕ) (hs : List ℕ) (layout : Layout) (bus : BusResult) (claims : List ColumnClaim),
        hs.length = 6 ∧ (∀ h ∈ hs, h < 31) ∧ logMem ≤ 30 ∧
        layout.logMemory = logMem ∧ layout.tableLogHeights = hs ∧ bus.point.length ≤ 40 ∧
        ReadsAt rd kb (1 :: gen ^ logMem :: hs.map (gen ^ ·)) ∧
        glm = gen ^ logMem ∧ gtau = gen ^ hs.getD 5 0 ∧
        Tables.PCtx rd (columnKappas logMem Tables.guestLogBytecode hs) off ∧
        Tables.KappasBelow (columnKappas logMem Tables.guestLogBytecode hs) ∧
        (stackOffsets (Tables.committedKappas (columnKappas logMem Tables.guestLogBytecode hs))).2 ≤ 30 ∧
        Tables.GTabsAt rd (gsq * gen ^ 34) ∧
        Tables.TCtx rd layout bus claims [zeta, chi, rm, gmu, gzcn] ∧ ∃ sl ≤ 30, gm = gen ^ sl
  | _ => False

end

end LeanVM.Guest.Res

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Mode LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B2C (idxOf entryOf FrameHolds fsN fn_of_idx cellJ namedOf)
open LeanVM.Guest.Bridge (FnAl)
open LeanVM.Guest.Res (Wit witOk constOf powOf inFr expFacts expOf baseAt ltFactB dimFacts dimShape dimB
  claimPairs busPairs tabPairs TermFront)
open LeanVM.Protocol.Verifier (gen Layout BusResult ColumnClaim)
open LeanVM.Prover.Exec

@[expose] public section

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

theorem expFacts_cot {c : String × ℕ × Option ℕ × ℕ} (hc : c ∈ CoreMode.Own.check_opening_terminal.expFacts) :
    c.1 = name% «check_opening_terminal» ∧ ((c.2.1 = 7 ∧ c.2.2.1 = none ∧ c.2.2.2 = 31) ∨
      (∃ k < 8, c.2.1 = 8 ∧ c.2.2.1 = some k ∧ c.2.2.2 = if k = 0 then 1 else 31) ∨
      (c.2.1 = 19 ∧ c.2.2.1 = none ∧ c.2.2.2 = 31)) := by
  simp only [CoreMode.Own.check_opening_terminal.expFacts, List.mem_append, List.mem_cons, List.mem_map,
    List.mem_range, List.not_mem_nil, or_false] at hc
  rcases hc with ((rfl | rfl) | ⟨k, hk, rfl⟩) | rfl
  · exact ⟨rfl, Or.inl ⟨rfl, rfl, rfl⟩⟩
  · exact ⟨rfl, Or.inr (Or.inl ⟨0, by omega, rfl, rfl, rfl⟩)⟩
  · exact ⟨rfl, Or.inr (Or.inl ⟨k + 1, by omega, rfl, rfl, by simp⟩)⟩
  · exact ⟨rfl, Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)⟩

theorem dimFacts_cot {c : String × ℕ × ℕ × List (ℕ × ℕ)} (hc : c ∈ CoreMode.Own.check_opening_terminal.dimFacts) :
    c.1 = name% «check_opening_terminal» ∧ c.2.1 = 8 ∧
      ((c.2.2.1 = 4 ∧ c.2.2.2 = busPairs) ∨ (c.2.2.1 = 5 ∧ c.2.2.2 = tabPairs)) := by
  simp only [CoreMode.Own.check_opening_terminal.dimFacts, List.mem_cons, List.not_mem_nil, or_false] at hc
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
    (hc : c ∈ CoreMode.Own.check_opening_terminal.expFacts) {v : V}
    (hv : B1.VerifySub.termParams[c.2.1]? = some v) : ExpH rd c.2.2.1 c.2.2.2 (σ v) := by
  simp only [B1.VerifySub.termParams, List.map_cons, List.map_nil, TermFront] at hT
  obtain ⟨lm, hs, layout, bus, claims, hl, h31, hm30, -, -, -, hkb, -, htau, -, -, -, -, -, sl, hsl, hgm⟩ := hT
  obtain ⟨-, ⟨hp, ho, hb⟩ | ⟨k, hk, hp, ho, hb⟩ | ⟨hp, ho, hb⟩⟩ := expFacts_cot hc
  · rw [hp] at hv
    obtain rfl : v = .n (val% «check_opening_terminal» "tau_keccak_g") := by simpa [B1.VerifySub.termParams] using hv.symm
    rw [ho, hb]
    refine ⟨_, ?_, htau⟩
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact h31 _ (List.getElem_mem _)
  · rw [hp] at hv
    obtain rfl : v = .n (val% «check_opening_terminal» "kappa_base") := by simpa [B1.VerifySub.termParams] using hv.symm
    rw [ho, hb]
    refine ⟨_, ?_, kb_load hl hkb hk⟩
    rcases Nat.lt_or_ge k 2 with h2 | h2
    · interval_cases k
      · simp
      · simp; omega
    · rw [show (if k = 0 then 1 else 31) = 31 by simp only [show ¬ k = 0 by omega, ↓reduceIte], List.getD_eq_getElem _ _ (by simp [hl]; omega), List.getElem_append_right (by simp; omega)]
      exact h31 _ (List.getElem_mem _)
  · rw [hp] at hv
    obtain rfl : v = .n (val% «check_opening_terminal» "gmv") := by simpa [B1.VerifySub.termParams] using hv.symm
    rw [ho, hb]
    exact ⟨sl, by omega, hgm⟩

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
    (hc : c ∈ CoreMode.Own.check_opening_terminal.dimFacts) {vk vb : V} (hvk : B1.VerifySub.termParams[c.2.1]? = some vk)
    (hvb : B1.VerifySub.termParams[c.2.2.1]? = some vb) : DimH rd (σ vk) (σ vb) c.2.2.2 := by
  simp only [B1.VerifySub.termParams, List.map_cons, List.map_nil, TermFront] at hT
  obtain ⟨lm, hs, layout, bus, claims, hl, -, -, hlm, hhs, hb40, hkb, -, -, -, -, -, -, hctx, -⟩ := hT
  obtain ⟨chis, hgmu, hgzc, hchL, hpair⟩ := pair_dim hlm hhs hctx
  obtain ⟨-, hk8, hcase⟩ := dimFacts_cot hc
  rw [hk8] at hvk
  obtain rfl : vk = .n (val% «check_opening_terminal» "kappa_base") := by simpa [B1.VerifySub.termParams] using hvk.symm
  have hp : ∀ j < B1.Tables.nPooled, ∀ p, p = claimPairs[j]! → LoadHolds rd (σ (.n (val% «check_opening_terminal» "kappa_base"))) p.1
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
    obtain rfl : vb = .n (val% «check_opening_terminal» "g_bus_mu") := by simpa [B1.VerifySub.termParams] using hvb.symm
    refine ⟨_, by omega, hgmu, fun p hpm ↦ ?_⟩
    rw [hps] at hpm
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hpm
    have hi4 : i < B1.Tables.nBusClaims := by simp only [busPairs, List.length_take] at hi; omega
    have hiP : i < B1.Tables.nPooled := lt_trans hi4 (by decide)
    obtain ⟨q, hq, hqb, -⟩ := hpair i hiP
    simp only [busPairs, List.getElem_take, hcp i (by omega)]
    exact ⟨_, kb_load hl hkb (claimSrc_lt i), by have := hqb hi4; omega⟩
  · rw [hb5] at hvb
    obtain rfl : vb = .n (val% «check_opening_terminal» "g_zc_n") := by simpa [B1.VerifySub.termParams] using hvb.symm
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

/-! ## At the honest frames -/

section

variable {A : String → FnAl} {K : Mode.Cert} {i : ℕ} {e : Bridge.Ent} {j : ℕ} {w : Wit}

end

section

variable {A : String → FnAl} {K : Mode.Cert} {i : ℕ} {e : Bridge.Ent} {j : ℕ} {w : Wit}

end

end

end LeanVM.Guest.EndExec
