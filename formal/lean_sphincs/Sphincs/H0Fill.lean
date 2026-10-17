import Sphincs.BridgeHeavyCert

/-! **Certificates rebuilt from their scalars.** A Poisson table, an option and a near certificate
are deterministic functions of a few scalars: the functions below rebuild them, as
`scripts/forest_certificates.py` does (`fill_poisT`, `fill_opt`, `make_optN`). Nothing is proved
about these functions: the checkers `checkPT`, `checkOptF` and `checkOptN` check what they return.

**Covers checked option by option.** The chain of a cover reads only the threshold and the bound of
each option: `checkOptB` checks one option and these two numbers, `checkCoverQ` checks the rest of the
cover on the numbers alone, and together they give `checkCoverW` (`checkCoverW_of`). The kernel then
evaluates one option at a time. -/

namespace Sphincs.Security.H0

open SphincsFors.Security.H0

/-! ### Rebuilding -/

/-- The entries of a Poisson table after the first: `p (n + 1) = ⌈p n · m / ((n + 1) 2^64)⌉`. -/
def poisGo (m : ℕ) : ℕ → ℕ → ℕ → List ℕ
  | 0, _, _ => []
  | k + 1, n, p =>
      ((p * m + ((n + 1) * 2 ^ 64 - 1)) / ((n + 1) * 2 ^ 64)) ::
        poisGo m k (n + 1) ((p * m + ((n + 1) * 2 ^ 64 - 1)) / ((n + 1) * 2 ^ 64))

/-- The Poisson table of rate `m / 2^64` with entries `0, …, n1 + 1`, precision `P` and `J + 1` terms
of the exponential series. -/
def fillPoisT (m P J n1 : ℕ) : PoisT :=
  ⟨m, P, J, ⌈(2 : ℚ) ^ P / expLow ((m : ℚ) / 2 ^ 64) J P⌉.toNat ::
    poisGo m (n1 + 1) 0 ⌈(2 : ℚ) ^ P / expLow ((m : ℚ) / 2 ^ 64) J P⌉.toNat⟩

/-- `convexify` after the first two entries: `a`, `b` are the last two entries. -/
def convexGo : ℚ → ℚ → List ℚ → List ℚ
  | _, _, [] => []
  | a, b, x :: xs => (max x (2 * b - a)) :: convexGo b (max x (2 * b - a)) xs

/-- The least convex increasing list above a list (from the left). -/
def convexify : List ℚ → List ℚ
  | [] => []
  | [x] => [x]
  | x :: y :: xs => x :: max y x :: convexGo x (max y x) xs

/-- The leaf table above the bounds `f 0, …, f n1`, on the grid `2^-P`. -/
def leafTab (n1 P : ℕ) (f : ℕ → ℚ) : List ℚ :=
  convexify ((convexify ((List.range (n1 + 1)).map f)).map (rup · P))

/-- The extension slope of a leaf table with cap `cap`. -/
def leafJ (n1 : ℕ) (tab : List ℚ) (cap : ℚ) : ℚ :=
  max (max (tab.getD n1 0 - tab.getD (n1 - 1) 0) (cap - tab.getD n1 0)) 0

/-- The bound of the Poisson mean of a leaf table extended with slope `J`. -/
def leafMean (t : PoisT) (tab : List ℚ) (J : ℚ) : ℚ :=
  ((List.range (t.n1 + 1)).map fun n => t.pb n * tab.getD n 0).sum +
    t.pb (t.n1 + 1) * (tab.getD t.n1 0 / (1 - t.r) + J / (1 - t.r) ^ 2)

/-- The option with cap `c1`, Chernoff parameter `θ`, `s` squarings and threshold `cthr`. -/
def fillOpt (b : ℕ) (t : PoisT) (c1 θ : ℚ) (s : ℕ) (cthr : ℚ) : OptF :=
  let eC := expUp (θ * c1) s t.P
  let A2 := rup ((eC - 1 - θ * c1) / c1 ^ 2) (2 * 127 + 64)
  let o0 : OptF := ⟨c1, θ, cthr, s, eC, A2, [], 0, [], 0, 0, 0, 0⟩
  let gt := leafTab t.n1 (64 + 127) (gBound o0)
  let ht := leafTab t.n1 (64 + 64) (hBound o0)
  let Jg := leafJ t.n1 gt κQ
  let Jh := leafJ t.n1 ht (eC - 1)
  let Eg := rup (leafMean t gt Jg) (64 + 127 + 2 * b)
  let Ee := rup (leafMean t ht Jh) (64 + 2 * b)
  let B := rup (2 ^ b * Eg + sqUp t.P b (1 + Ee) / (expLow (θ * cthr) t.J t.P * eLowQ * θ)) (64 + 127)
  ⟨c1, θ, cthr, s, eC, A2, gt, Jg, ht, Jh, Eg, Ee, B⟩

/-- The near certificate of a Poisson table. -/
def fillOptN (b : ℕ) (t : PoisT) : OptN :=
  let nt := leafTab t.n1 (64 + 127) nBound
  let Jn := leafJ t.n1 nt (16 * κQ)
  ⟨nt, Jn, rup (leafMean t nt Jn) (64 + 127 + 2 * b)⟩

/-! ### Covers option by option -/

/-- The check of one option, with its threshold and its bound `p = (cthr, B)`. -/
def checkOptB (b : ℕ) (t : PoisT) (o : OptF) (p : ℚ × ℚ) : Bool :=
  checkOptF b t o && decide (o.cthr = p.1) && decide (o.B = p.2)

/-- `checkEntryF` on the thresholds and the bounds of the options. -/
def checkEntryQ (b N : ℕ) (ps : List (ℚ × ℚ)) (e : EntryF) : Bool :=
  match ps[e.2.2]? with
  | none => false
  | some p =>
      decide (2 * e.2.1 ≤ 2 ^ 128) && decide (p.1 ≤ ForsPotential.betaWQ e.2.1) &&
        decide ((e.2.1 : ℚ) * p.2 + ((e.2.1 : ℚ) + kCreditF b + N) / 2 ^ 200 ≤
          ((e.1 : ℚ) / 2 ^ 128) ^ 2 + (kCreditF b : ℚ) / 2 ^ 127)

/-- `chainF` on the thresholds and the bounds of the options. -/
def chainQ (b N qtop : ℕ) (ps : List (ℚ × ℚ)) : ℕ → List EntryF → Bool
  | last, [] => decide (qtop < last)
  | last, e :: rest => decide (e.1 ≤ last) && checkEntryQ b N ps e && chainQ b N qtop ps (e.2.1 + 1) rest

/-- The checks of a light cover that do not open its options. -/
def checkCoverQ (b N qstart : ℕ) (c : CoverW) (ps : List (ℚ × ℚ)) : Bool :=
  checkRate b N c.qtop c.tab && checkPT c.tab && chainQ b N c.qtop ps qstart c.entries

/-- The checks of a heavy cover that do not open its options. -/
def checkCoverQH (b N qstart : ℕ) (c : CoverW) (ps : List (ℚ × ℚ)) : Bool :=
  checkRateH b N c.qtop c.tab && checkPT c.tab && chainQ b N c.qtop ps qstart c.entries

theorem checkEntryQ_map (b N : ℕ) (opts : List OptF) (e : EntryF) :
    checkEntryQ b N (opts.map fun o => (o.cthr, o.B)) e = checkEntryF b N opts e := by
  unfold checkEntryQ checkEntryF
  rw [List.getElem?_map]
  cases opts[e.2.2]? <;> rfl

theorem chainQ_map (b N qtop : ℕ) (opts : List OptF) : ∀ (es : List EntryF) (last : ℕ),
    chainQ b N qtop (opts.map fun o => (o.cthr, o.B)) last es = chainF b N qtop opts last es
  | [], _ => rfl
  | e :: rest, last => by
      simp only [chainQ, chainF, checkEntryQ_map, chainQ_map b N qtop opts rest]

/-- Options checked one by one pass `checkOptF`, and `ps` lists their thresholds and bounds. -/
theorem checkOptB_all {b : ℕ} {t : PoisT} : ∀ {opts : List OptF} {ps : List (ℚ × ℚ)},
    List.Forall₂ (fun o p => checkOptB b t o p = true) opts ps →
      opts.all (checkOptF b t) = true ∧ (opts.map fun o => (o.cthr, o.B)) = ps
  | _, _, .nil => ⟨rfl, rfl⟩
  | _, _, .cons (a := o) (b := p) h hs => by
      obtain ⟨h1, h2⟩ := checkOptB_all hs
      simp only [checkOptB, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨ho, hc⟩, hB⟩ := h
      refine ⟨by simp only [List.all_cons, ho, h1, Bool.and_self], ?_⟩
      simp only [List.map_cons, h2, hc, hB]

/-- **A light cover from its options checked one by one.** -/
theorem checkCoverW_of {b N qstart : ℕ} {c : CoverW} (ps : List (ℚ × ℚ))
    (ho : List.Forall₂ (fun o p => checkOptB b c.tab o p = true) c.opts ps)
    (h : checkCoverQ b N qstart c ps = true) : checkCoverW b N qstart c = true := by
  obtain ⟨h1, h2⟩ := checkOptB_all ho
  simp only [checkCoverQ, Bool.and_eq_true] at h
  simp only [checkCoverW, Bool.and_eq_true]
  exact ⟨⟨⟨h.1.1, h.1.2⟩, h1⟩, by rw [← chainQ_map, h2]; exact h.2⟩

/-- **A heavy cover from its options checked one by one.** -/
theorem checkCoverH_of {b N qstart : ℕ} {c : CoverW} (ps : List (ℚ × ℚ))
    (ho : List.Forall₂ (fun o p => checkOptB b c.tab o p = true) c.opts ps)
    (h : checkCoverQH b N qstart c ps = true) : checkCoverH b N qstart c = true := by
  obtain ⟨h1, h2⟩ := checkOptB_all ho
  simp only [checkCoverQH, Bool.and_eq_true] at h
  simp only [checkCoverH, Bool.and_eq_true]
  exact ⟨⟨⟨h.1.1, h.1.2⟩, h1⟩, by rw [← chainQ_map, h2]; exact h.2⟩

end Sphincs.Security.H0
