/-
  LeanVM.Guest.B1.Tables.TermAtProof

  `check_opening_terminal` complete in the uniform placed form (`CompleteTermAt`).
-/

module

public import LeanVM.Guest.B1.Tables.TermAtBody
public import LeanVM.Guest.B1.VerifySub.CompleteIface
public import LeanVM.Guest.B1.Tables.LoopSize
public import LeanVM.Guest.B1.Tables.FlatAtB
public import LeanVM.Guest.B1.Tables.VtCStraightB

/-!
# `check_opening_terminal`, placed

Its five `HeapBuf`s hold the run's chains and rows (`termOwn`, over the table point fixed by
`CompleteTermAt`); its 97 callees (three prefix chains, `__loop83`, the 92 selectors,
`rs_eq_run`) are pure, on the caller's words and those buffers; every load reads one of them.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub LeanVM.Guest.B1.Sig
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

/-- The terminal's callee `i`: three prefix chains, `__loop83`, the selectors, `rs_eq_run`. -/
def termKid (b : ℕ) (LB : Main.Layout) (a0 a1 a3 a4 a5 a6 a11 a13 : E) (K O : ℕ → ℕ)
    (sel : ℕ → E) (i : ℕ) : Kid :=
  if i = 0 then ⟨"eq_prefix_chain", true, [ofK (Parameters.gpow b), word 1 0 0, a0, a13, a3], LB,
    Returns []⟩
  else if i = 1 then ⟨"eq_prefix_chain", true,
    [ofK (Parameters.gpow (b + 35)), word 1 0 0, a1, a13, a4], LB, Returns []⟩
  else if i = 2 then ⟨"eq_prefix_chain", true,
    [ofK (Parameters.gpow (b + 35 + 35)), word 1 0 0, a1, a13 * word 256 0 0, a6], LB, Returns []⟩
  else if i = 3 then ⟨"__loop83", decide (word 2 0 0 + a5 ≠ 0),
    [word 2 0 0, a5, ofK (Parameters.gpow (b + 35 + 35 + 35)), a13], LB, Returns []⟩
  else if i < 96 then ⟨csNames.getD (K (i - 4)) "", true, [gen ^ O (i - 4), a13], LB,
    Returns [sel (i - 4)]⟩
  else ⟨"rs_eq_run", true,
    [ofK (Parameters.gpow (b + 35 + 35 + 35 + 35)), a11, a13, a6 * word 256 0 0], LB, Returns []⟩

/-- The terminal's frame `i`, under `σ`. -/
noncomputable def termCall (σ : Val) (i : ℕ) : Option V × String × List V × List V :=
  if i = 0 then (none, "eq_prefix_chain", [.n 17, .n 18, .n 0, .n 13, .n 3], [])
  else if i = 1 then (none, "eq_prefix_chain", [.n 19, .n 20, .n 1, .n 13, .n 4], [])
  else if i = 2 then (none, "eq_prefix_chain", [.n 21, .n 22, .n 1, .n 24, .n 6], [])
  else if i = 3 then (some (.n 32), "__loop83", [.n 33, .n 5, .n 25, .n 13], [])
  else if i < 96 then (none, csNames.getD (logG (σ (.n (37 + 3 * (i - 4))))) "",
    [.n (36 + 3 * (i - 4)), .n 13], [.n (selV (i - 4))])
  else (none, "rs_eq_run", [.n 1750, .n 11, .n 13, .n 1816], [])

theorem term_calls' (σ : Val) : tSegs.flatten.filterMap (Stmt.callSF σ) =
    (List.range 97).map (termCall σ) := by
  rw [term_calls, show 97 = 4 + 92 + 1 from rfl, List.range_add, List.range_add, List.map_append,
    List.map_append]
  simp only [List.map_map]
  congr 1

/-- A selector block's offset and log words, and its dispatch's selector. -/
theorem sel_more {rd : Reader} {σ : Val} {kret : List E → Prop} {c : ℕ}
    (h : Stmt.HoldsList (coreProgram.Rel rd) rd σ (selBlk c) True kret) {K O : ℕ} (hK : K ≤ 28)
    (lo : LoadHolds rd (σ (.n 9)) c (gen ^ O)) (lk : LoadHolds rd (σ (.n 10)) c (gen ^ K)) :
    σ (.n (36 + 3 * c)) = gen ^ O ∧ σ (.n (37 + 3 * c)) = gen ^ K ∧
      ∃ j < csNames.length, j < 2 ^ 64 - 1 ∧ σ (.n (37 + 3 * c)) = ofK (gpow j) := by
  simp only [selBlk, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, List.map_cons,
    List.map_nil] at h
  obtain ⟨l1, l2, -⟩ := h
  have e2 := loadHolds_unique l2 lk
  refine ⟨loadHolds_unique l1 lo, e2, K, by simp [csNames]; omega, by omega, by
    rw [e2, gen_pow_eq_ofK]⟩

/-- Every dispatch of a list whose selectors are powers of `g` naming a callee. -/
theorem dispOk_of {σ : Val} {l : List Stmt}
    (h : ∀ p ∈ l.filterMap Stmt.dispX, ∃ j < p.2.length, j < 2 ^ 64 - 1 ∧ σ p.1 = ofK (gpow j)) :
    ∀ s ∈ l, DispOk σ s := by
  intro s hs
  cases s with
  | dispatch x fs args rets => exact h (x, fs) (List.mem_filterMap.mpr ⟨_, hs, rfl⟩)
  | _ => trivial

/-- A terminal callee's bound, by its name: a prefix chain, `rs_eq_run`, `__loop83` over at most
32 steps, a column selector its frame. -/
def termNameBd (fs : String → ℕ) (f : String) : ℕ :=
  if f = "eq_prefix_chain" then eqpcBound fs else if f = "rs_eq_run" then rsBound fs
  else if f = "__loop83" then 33 * fs "__loop83" else fs f

/-- The largest column selector's frame. -/
def csMax (fs : String → ℕ) : ℕ := (csNames.map fs).foldl max 0

/-- The 97 callees' bound: three prefix chains, `__loop83`, 92 selectors, `rs_eq_run`. -/
abbrev termKidsTot (fs : String → ℕ) : ℕ :=
  3 * eqpcBound fs + 33 * fs "__loop83" + 92 * csMax fs + rsBound fs

/-- The terminal's bound: its frame, its `HeapBuf`s at `τ = 20` and its 97 callees. -/
abbrev termBound (fs : String → ℕ) : ℕ := fs "check_opening_terminal" + 1996 + termKidsTot fs

theorem fs_le_termNameBd (fs : String → ℕ) (f : String) : fs f ≤ termNameBd fs f := by
  unfold termNameBd
  split_ifs with h1 h2 h3 <;> (try subst h1) <;> (try subst h2) <;> (try subst h3) <;>
    (try simp only [eqpcBound, rsBound]) <;> omega

set_option maxRecDepth 100000 in
theorem cs_names_facts : ∀ j < 29, csNames.getD j "" ≠ "eq_prefix_chain" ∧ csNames.getD j "" ≠ "rs_eq_run" ∧
    csNames.getD j "" ≠ "__loop83" := by decide

theorem cs_foldl_max_ge : ∀ (l : List ℕ) (a x : ℕ), x ∈ l ∨ x ≤ a → x ≤ l.foldl max a
  | [], _, _, h => h.resolve_left (by simp)
  | y :: l, a, x, h => by
    rw [List.foldl_cons]
    refine cs_foldl_max_ge l _ x ?_
    rcases h with h | h
    · rcases List.mem_cons.mp h with rfl | h
      · exact Or.inr (le_max_right _ _)
      · exact Or.inl h
    · exact Or.inr (le_trans h (le_max_left _ _))

theorem cs_le_csMax (fs : String → ℕ) {j : ℕ} (hj : j < 29) : termNameBd fs (csNames.getD j "") ≤ csMax fs := by
  obtain ⟨a, b, c⟩ := cs_names_facts j hj
  simp only [termNameBd, a, b, c, ↓reduceIte]
  exact cs_foldl_max_ge _ 0 _ (Or.inl (List.mem_map_of_mem (f := fs)
    (List.getD_eq_getElem csNames "" (by simpa [csNames] using hj) ▸ List.getElem_mem _ :
      csNames.getD j "" ∈ csNames)))

/-- **The terminal's callees' bound**, each at its name's bound. -/
theorem termKids_bound (fs : String → ℕ) (b : ℕ) (LB : Main.Layout) (a0 a1 a3 a4 a5 a6 a11 a13 : E)
    (K O : ℕ → ℕ) (sel : ℕ → E) (hK : ∀ c < 92, K c < 29) :
    kidsBound fs (fun k => termNameBd fs k.f)
      ((List.range 97).map (termKid b LB a0 a1 a3 a4 a5 a6 a11 a13 K O sel)) ≤ termKidsTot fs := by
  set c : ℕ → ℕ := fun i => if i < 3 then eqpcBound fs else if i = 3 then 33 * fs "__loop83"
    else if i < 96 then csMax fs else rsBound fs with hc
  unfold kidsBound
  rw [List.map_map]
  refine le_trans (List.sum_le_sum (g := c) fun i hi => ?_) (le_of_eq ?_)
  · have hi' := List.mem_range.mp hi
    refine le_trans (?_ : _ ≤ termNameBd fs (termKid b LB a0 a1 a3 a4 a5 a6 a11 a13 K O sel i).f) ?_
    · simp only [Function.comp]
      split
      · exact le_rfl
      · exact fs_le_termNameBd fs _
    · simp only [hc]
      unfold termKid
      split_ifs with h0 h1 h2 h3 h4 h5 h6 h7 <;> (try omega) <;> simp_all [termNameBd]
      exact cs_le_csMax fs (hK _ (by omega))
  · rw [show 97 = 4 + 92 + 1 from rfl, List.range_add, List.range_add, List.map_append, List.map_append,
      List.sum_append, List.sum_append]
    have hmid : ((List.range 92).map (4 + ·)).map c = List.replicate 92 (csMax fs) := by
      rw [List.map_map]
      refine List.ext_getElem (by simp) fun j h1 h2 => ?_
      simp only [List.getElem_map, List.getElem_range, Function.comp, List.getElem_replicate, hc]
      simp only [List.length_map, List.length_range] at h1
      rw [ite_neg' (by omega), ite_neg' (by omega), ite_pos' (by omega)]
    rw [hmid, show List.range 4 = [0, 1, 2, 3] from rfl,
      show List.map (fun x => 4 + 92 + x) (List.range 1) = [96] from rfl, List.sum_replicate, smul_eq_mul]
    show _ = 3 * eqpcBound fs + 33 * fs "__loop83" + 92 * csMax fs + rsBound fs
    have c0 : c 0 = eqpcBound fs := by rw [hc]; rfl
    have c1 : c 1 = eqpcBound fs := by rw [hc]; rfl
    have c2 : c 2 = eqpcBound fs := by rw [hc]; rfl
    have c3 : c 3 = 33 * fs "__loop83" := by rw [hc]; rfl
    have c96 : c 96 = rsBound fs := by rw [hc]; rfl
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, c0, c1, c2, c3, c96]
    omega

/-- `check_opening_terminal`'s weight: its frame's and its 97 callees'. -/
abbrev termBoundW (ω : String → ℕ) : ℕ := ω "check_opening_terminal" + termKidsTot ω

set_option maxHeartbeats 8000000 in
/-- **`check_opening_terminal` is complete, placed, by a bounded tree within weights** (TRIAGE #42,
#43): `CompleteTermAtW`. -/
theorem check_opening_terminal_completeAtW (fs : String → ℕ) (cert : String → V → ℕ) {Θ : Type}
    (wt : Θ → String → ℕ) (κ : ℕ) :
    CompleteTermAtW fs cert κ TCtx PCtx wt (termBound fs) fun θ => termBoundW (wt θ) := by
  intro layout bus claims lam fp cs w chis args Lin hacc hlen' hgz hpre
  classical
  by_cases hex : ∃ rd0, LowDef κ rd0 ∧ MemL rd0 Lin
  swap
  · intro fp'
    exact ⟨0, [], [], [], ⟨rfl, rfl⟩, by simp [Within], disj_nil, Nat.zero_le _, fun rd hl hL =>
      absurd ⟨rd, hl, by simpa using hL⟩ hex⟩
  obtain ⟨rd0, hl0, hL0⟩ := hex
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, rfl⟩ :=
    args17 (P := TermPre TCtx PCtx rd0 layout bus claims lam fp cs w)
    (fun l hl hP => by
      rcases l with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | ⟨a7,
          _ | ⟨a8, _ | ⟨a9, _ | ⟨a10, _ | ⟨a11, _ | ⟨a12, _ | ⟨a13, _ | ⟨a14, _ | ⟨a15,
          _ | ⟨a16, _ | ⟨_, _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
      all_goals first | exact hP.elim | exact absurd rfl hl) (hpre rd0 hl0 hL0).1
  have hp0 := (hpre rd0 hl0 hL0).1
  obtain ⟨hT, hP, -, hglm, hgtau, hlp, hzv, hct, hpt, hin, hyr, hst, hpl, hsl, hμ28, hlm1, hbp,
    hxl, hfpl, hcsl⟩ := hp0
  obtain ⟨chis0, hzeta, hgmu, hchi0, hgzcn, hchl, hcl, hcols, hpts⟩ := hT
  obtain ⟨hkl, -, -⟩ := hP
  -- the claims' lengths, by index
  have hlens : ∀ j (p : List E), (claims.map (·.point))[j]? = some p →
      p.length = (layout.placements.getD (claimColumns.getD j 0) default).vars := by
    intro j p hp
    obtain ⟨hj, rfl⟩ : ∃ hj : j < claims.length, p = claims[j].point := by
      simp only [List.getElem?_map, Option.map_eq_some_iff] at hp
      obtain ⟨c, hc, rfl⟩ := hp
      obtain ⟨hj, hcj⟩ := List.getElem?_eq_some_iff.mp hc
      exact ⟨hj, by rw [hcj]⟩
    rw [hlen' _ (List.getElem_mem hj), ← hcols,
      List.getD_eq_getElem (claims.map (·.column)) _ (by simpa using hj), List.getElem_map]
  -- the table point, fixed
  set m1 := chis0.length
  have hm1 : m1 ≤ chis.length := by
    by_contra h
    have := gen_pow_inj' (a := chis.length) (b := m1) (by omega) (by omega)
      (by rw [← hgz, hgzcn]; rfl)
    omega
  set chisF := chis.take m1
  set τ := layout.tableLogHeights.getD opBlake2s 0 with hτdef
  set n := layout.logMemory with hndef
  set ptw := w.point ++ List.replicate (pointCap - w.point.length) 0 with hptwdef
  set kps := columnKappas layout.logMemory layout.logBytecode layout.tableLogHeights with hkps
  -- every honest memory reads the same words
  have hallZ : ∀ rd, LowDef κ rd → MemL rd Lin → ReadsAt rd a0 bus.point := fun rd h1 h2 => by
    obtain ⟨⟨⟨c, hz, -⟩, -⟩, -⟩ := hpre rd h1 h2; exact hz
  have hallC : ∀ rd, LowDef κ rd → MemL rd Lin → ReadsAt rd a1 chisF := fun rd h1 h2 => by
    exact readsAt_take (hpre rd h1 h2).2 m1
  have hallP : ∀ rd, LowDef κ rd → MemL rd Lin → ReadsAt rd a13 ptw := fun rd h1 h2 => by
    obtain ⟨⟨-, -, -, -, -, -, -, -, hp, -⟩, -⟩ := hpre rd h1 h2; exact hp
  have hallF : ∀ rd, LowDef κ rd → MemL rd Lin → ReadsAt rd a11 fp := fun rd h1 h2 => by
    obtain ⟨⟨-, -, -, -, -, -, hz, -⟩, -⟩ := hpre rd h1 h2; exact hz
  have hallT : ∀ rd, LowDef κ rd → MemL rd Lin → ReadsAt rd a12 cs := fun rd h1 h2 => by
    obtain ⟨⟨-, -, -, -, -, -, -, ht, -⟩, -⟩ := hpre rd h1 h2; exact ht
  have hallL : ∀ rd, LowDef κ rd → MemL rd Lin → ReadsAt rd a8 (powersFrom lam lam claims.length) :=
    fun rd h1 h2 => by obtain ⟨⟨-, -, -, -, -, hl, -⟩, -⟩ := hpre rd h1 h2; exact hl
  have hallK : ∀ rd, LowDef κ rd → MemL rd Lin →
      ReadsAt rd a10 ((committedKappas kps).map (gen ^ ·)) := fun rd h1 h2 => by
    obtain ⟨⟨-, ⟨-, hk, -⟩, -⟩, -⟩ := hpre rd h1 h2; exact hk
  have hallO : ∀ rd, LowDef κ rd → MemL rd Lin →
      ReadsAt rd a9 ((stackOffsets (committedKappas kps)).1.map (gen ^ ·)) := fun rd h1 h2 => by
    obtain ⟨⟨-, ⟨-, -, ho⟩, -⟩, -⟩ := hpre rd h1 h2; exact ho
  have hallCp : ∀ rd, LowDef κ rd → MemL rd Lin → ReadsAt rd a7
      ((List.range nPooled).map fun j => gen ^ ((claims.map (·.point)).getD j []).length) := by
    intro rd h1 h2
    obtain ⟨⟨⟨c, -, -, -, -, -, -, -, hpts'⟩, -⟩, -⟩ := hpre rd h1 h2
    intro j hj
    simp only [List.length_map, List.length_range] at hj
    have hjl : j < claims.length := by
      rw [hcl]; exact lt_of_lt_of_le hj (by decide)
    rw [List.getElem_map, List.getElem_range, List.getD_eq_getElem _ _ (by simpa using hjl),
      List.getElem_map]
    exact (hpts' j claims[j].point (by simp [hjl])).1 hj
  -- the layout's sizes and offsets
  obtain ⟨K, hK⟩ : ∃ K : ℕ → ℕ, ∀ c, K c = (committedKappas kps).getD c 0 := ⟨_, fun _ => rfl⟩
  obtain ⟨O, hO⟩ : ∃ O : ℕ → ℕ, ∀ c, O c = offAt kps c := ⟨_, fun _ => rfl⟩
  have hcl92 : (committedKappas kps).length = 92 := committedKappas_length _ hkl
  have hlog : log2Ceil (stackTotal kps) ≤ layout.stackLog := by
    rw [hsl, placementsOf_snd]; exact le_max_right _ _
  have hKμ : ∀ c < 92, K c ≤ layout.stackLog := fun c hc => by
    rw [hK]
    exact le_trans (le_log2Ceil_of_two_pow_le
      (stackTotal_eq kps ▸ single_le_sum_map _ c (by omega))) hlog
  have hOμ : ∀ c < 92, O c < 2 ^ layout.stackLog := fun c hc => by
    have h1 := stackOffsets_bound (committedKappas kps) (c := c) (by omega)
    have h2 := Nat.one_le_two_pow (n := (committedKappas kps).getD c 0)
    rw [← stackTotal_eq] at h1
    have htot : stackTotal kps ≤ 2 ^ layout.stackLog :=
      le_trans (le_two_pow_log2Ceil _) (Nat.pow_le_pow_right (by norm_num) hlog)
    rw [hO, offAt]
    omega
  have hdvd : ∀ c < 92, 2 ^ K c ∣ O c := fun c hc => by
    rw [hK, hO, offAt]; exact stackOffsets_dvd _ (by omega)
  have hK0 : ∀ c < 3, K c = layout.logMemory := fun c hc => by
    rw [hK, committedKappas_getD _ hkl (by omega), blockCols_lo c (by omega), hkps,
      columnKappas_mem _ _ _ (by omega)]
  have hK5 : K 5 = τ + 8 := by
    rw [hK, committedKappas_getD _ hkl (by omega), qflock_col.2.2, hkps]
    exact columnKappas_qflock _ _ _
  have hlm28 : n ≤ 28 := by
    have := hKμ 0 (by omega); rw [hK0 0 (by omega)] at this; omega
  have hτ : τ + 8 ≤ layout.stackLog := by
    have := hKμ 5 (by omega); rwa [hK5] at this
  have hptl : ptw.length = 42 := by simp [ptw, pointCap]; omega
  have hvars : ∀ col < 110, (layout.placements.getD col default).vars = kps.getD col 0 :=
    fun col hc => by rw [hpl, placementsOf_getD kps (by rw [hkl]; exact hc)]; split <;> rfl
  -- the table point reaches `q_flock`'s
  have hτm : τ ≤ m1 := by
    have hj : 81 < claims.length := by rw [hcl]; decide
    have hp : (claims.map (·.point))[81]? = some claims[81].point := by simp [hj]
    have h1 := hlens 81 _ hp
    rw [hvars _ (claim_cols 81 (by decide)).1, hkps,
      show claimColumns.getD 81 0 = 73 + (claimColumns.getD 81 0 - 73) by decide,
      columnKappas_blake _ _ _ (by decide)] at h1
    have h1' : claims[81].point.length = τ := h1
    have h3 := (hpts 81 _ hp).2.2.1 (by decide) (by decide)
    have := congrArg List.length h3
    rw [List.length_take] at this
    omega
  have hm33 : m1 < 33 := by omega
  have hchF : chisF.length = m1 := by simp only [chisF, List.length_take]; omega
  have hn33 : n < 33 := by omega
  have hτ28 : τ + 8 ≤ 28 := by omega
  -- the honest memory, on any memory agreeing with one holding the words
  have hMem : ∀ b rd, LowDef κ rd → MemL rd Lin →
      MemL rd (bufL b (termSizes τ) (termOwn bus.point chisF ptw fp a2 n τ)) → ∀ rd' : Reader,
      (∀ i, RegionL (Lin ++ bufL b (termSizes τ) (termOwn bus.point chisF ptw fp a2 n τ)) i →
        rd' (gpow i) = rd (gpow i)) →
      TermMem rd' [ofK (Parameters.gpow b), ofK (Parameters.gpow (b + 35)),
        ofK (Parameters.gpow (b + 35 + 35)), ofK (Parameters.gpow (b + 35 + 35 + 35)),
        ofK (Parameters.gpow (b + 35 + 35 + 35 + 35))]
        [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16] := by
    intro b rd hlow hL hB rd' hag
    have hag1 : ∀ i, RegionL Lin i → rd' (gpow i) = rd (gpow i) :=
      fun i hi => hag i (regionL_append.mpr (Or.inl hi))
    exact termMem_of (memL_of_agree hB fun i hi => hag i (regionL_append.mpr (Or.inr hi)))
      (readsAt_transfer hallZ hlow hL hag1) (readsAt_transfer hallC hlow hL hag1)
      (readsAt_transfer hallP hlow hL hag1) (readsAt_transfer hallF hlow hL hag1) hptl hgmu
      (by rw [hchF]; exact hgzcn) hglm hgtau hbp (by omega) (by omega) hτ28 hn33 hlm1 hfpl
  obtain ⟨sel, hsel⟩ : ∃ sel : ℕ → E, ∀ c, sel c = ∏ t ∈ Finset.range (28 - K c),
      (1 + bitE ((O c).testBit (K c + t)) + ptw.getD (K c + t) 0) := ⟨_, fun _ => rfl⟩
  have hK28 : ∀ c < 92, K c ≤ 28 := fun c hc => le_trans (hKμ c hc) hμ28
  have hO28 : ∀ c < 92, O c < 2 ^ 28 := fun c hc =>
    lt_of_lt_of_le (hOμ c hc) (Nat.pow_le_pow_right (by norm_num) hμ28)
  have hkLin : ∀ b i, (termKid b (Lin ++ bufL b (termSizes τ) (termOwn bus.point chisF ptw fp a2 n τ))
      a0 a1 a3 a4 a5 a6 a11 a13 K O sel i).Lin =
      Lin ++ bufL b (termSizes τ) (termOwn bus.point chisF ptw fp a2 n τ) := fun b i => by
    unfold termKid; split_ifs <;> rfl
  refine Main.CompleteAtW.bmono ?_ (show fs "check_opening_terminal" + (termSizes τ).sum +
    termKidsTot fs ≤ termBound fs by
      simp only [termSizes, termBound, List.sum_cons, List.sum_nil]; omega)
  refine completeAt_flatW find_check_opening_terminal term_not_loop κ Lin _ _ term_body term_flat
    term_addrs (termSizes τ) (fun _ => termOwn bus.point chisF ptw fp a2 n τ)
    (fun _ => termOwn_fit _ _ _ _ _ _ _)
    (fun fp' => (List.range 97).map (termKid (fp' + fs "check_opening_terminal")
      (Lin ++ bufL (fp' + fs "check_opening_terminal") (termSizes τ)
        (termOwn bus.point chisF ptw fp a2 n τ)) a0 a1 a3 a4 a5 a6 a11 a13 K O sel))
    (fun k => termNameBd fs k.f) (fun k θ => termNameBd (wt θ) k.f) (termKidsTot fs) (fun θ => termKidsTot (wt θ)) ?_
    (fun fp' => termKids_bound fs _ _ _ _ _ _ _ _ _ _ _ _ _ fun c hc => by have := hK28 c hc; omega)
    (fun fp' θ => (Main.kidsBoundW_le_kidsBound _ θ (wt θ) _ (fun _ => le_rfl) _).trans
      (termKids_bound (wt θ) _ _ _ _ _ _ _ _ _ _ _ _ _ fun c hc => by have := hK28 c hc; omega)) ?_ ?_ ?_
  · intro fp' k hk ht
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hk
    simp only [List.mem_range] at hi
    have hM : ∀ rd, LowDef κ rd → MemL rd (Lin ++ bufL (fp' + fs "check_opening_terminal")
        (termSizes τ) (termOwn bus.point chisF ptw fp a2 n τ)) → ∀ rd' : Reader,
        (∀ i, RegionL (Lin ++ bufL (fp' + fs "check_opening_terminal") (termSizes τ)
          (termOwn bus.point chisF ptw fp a2 n τ)) i → rd' (gpow i) = rd (gpow i)) →
        TermMem rd' _ _ ∧ ReadsAt rd' a13 ptw := fun rd hlow hL rd' hag => by
      obtain ⟨hL1, hL2⟩ := Main.memL_append.mp hL
      exact ⟨hMem _ rd hlow hL1 hL2 rd' hag, readsAt_transfer hallP hlow hL1
        fun i hi => hag i (regionL_append.mpr (Or.inl hi))⟩
    unfold termKid at ht ⊢
    split_ifs at ht ⊢ with h0 h1 h2 h3 h4
    · refine vtc_completeAt_of_rel_lowW (B := fun fs' => termNameBd fs' _) pure_eqpc (by simp) κ ?_
        fun fs' rd _ t rets' hn hv hbo =>
        le_trans (eqpc_total (fs := fs') (m := bus.point.length) (by omega) hn (by rw [← hgmu]; exact hv)
          hbo) (le_of_eq (by simp [termNameBd]))
      intro rd hlow hL rd' hag
      obtain ⟨⟨c17, -⟩, -⟩ := hM rd hlow hL rd' hag
      rw [word_one]; exact (eq_prefix_chain_iff _ _ _).mpr c17
    · refine vtc_completeAt_of_rel_lowW (B := fun fs' => termNameBd fs' _) pure_eqpc (by simp) κ ?_
        fun fs' rd _ t rets' hn hv hbo =>
        le_trans (eqpc_total (fs := fs') (m := m1) (by omega) hn (by rw [← hgzcn]; exact hv)
          hbo) (le_of_eq (by simp [termNameBd]))
      intro rd hlow hL rd' hag
      obtain ⟨⟨-, c19, -⟩, -⟩ := hM rd hlow hL rd' hag
      rw [word_one]; exact (eq_prefix_chain_iff _ _ _).mpr c19
    · refine vtc_completeAt_of_rel_lowW (B := fun fs' => termNameBd fs' _) pure_eqpc (by simp) κ ?_
        fun fs' rd _ t rets' hn hv hbo =>
        le_trans (eqpc_total (fs := fs') (m := τ) (by omega) hn (by rw [← hgtau]; exact hv)
          hbo) (le_of_eq (by simp [termNameBd]))
      intro rd hlow hL rd' hag
      obtain ⟨⟨-, -, c21, -⟩, -⟩ := hM rd hlow hL rd' hag
      rw [word_one, word_g8]; exact (eq_prefix_chain_iff _ _ _).mpr c21
    · rw [word_gen, hglm] at ht ⊢
      have hn2 : 1 < n := by
        rcases Nat.lt_or_ge 1 n with h | h
        · exact h
        · exfalso; simp only [decide_eq_true_eq] at ht; apply ht
          rw [show n = 1 by omega, pow_one]; exact e_add_self _
      refine vtc_completeAt_of_rel_lowW (B := fun fs' => termNameBd fs' _) pure_l83 (by simp) κ ?_
        fun fs' rd _ t rets' hn hv hbo => ?_
      · intro rd hlow hL rd' hag
        obtain ⟨⟨-, -, -, -, hpi, -⟩, hpt'⟩ := hM rd hlow hL rd' hag
        have hX : ∀ k < n, LoadHolds rd' a13 k (ptw.getD k 0) := fun k hk => readsAt_get hpt' (by omega)
        have hc := hpi n hglm hn33 _ hX
        exact loop83_complete hn2 hn33 hX hc
      · have := l83_total (fs := fs') (j := 1) (m := n) hn2 hn (by rw [pow_one]; exact hv) hbo
        have : (n - 1) * fs' "__loop83" ≤ 32 * fs' "__loop83" := Nat.mul_le_mul_right _ (by omega)
        show _ ≤ termNameBd fs' "__loop83"
        rw [show termNameBd fs' "__loop83" = 33 * fs' "__loop83" by simp [termNameBd]]; omega
    · have hc : i - 4 < 92 := by omega
      have hlt : K (i - 4) < csNames.length := by simp [csNames]; have := hK28 _ hc; omega
      rw [List.getD_eq_getElem _ _ hlt]
      refine vtc_completeAt_of_rel_lowW (B := fun fs' => termNameBd fs' _) pure_cs (List.getElem_mem hlt) κ ?_
        fun fs' rd _ t rets' hn hv hbo => ?_
      swap
      · rw [cs_total (fs := fs') (List.getElem_mem hlt) hn hv hbo]
        exact fs_le_termNameBd fs' _
      intro rd hlow hL rd' hag
      obtain ⟨-, hpt'⟩ := hM rd hlow hL rd' hag
      refine column_selector_any' hlt ⟨O (i - 4), (List.range 28).map fun k => ptw.getD k 0,
        hO28 _ hc, hdvd _ hc, rfl, by simp, fun k hk _ => ?_, ?_⟩
      · simp only [List.getElem_map, List.getElem_range]
        exact readsAt_get hpt' (by simp at hk; omega)
      · rw [eqAbove_eq_prod _ (by simp), hsel]
        congr 1
        refine Finset.prod_congr rfl fun t ht => ?_
        rw [getD_map_range _ _ (by simp at ht; omega)]
    · refine vtc_completeAt_of_rel_lowW (B := fun fs' => termNameBd fs' _) pure_rs (by simp) κ ?_
        fun fs' rd _ t rets' hn hv hbo =>
        le_trans (rs_total (fs := fs') (m := τ + 8) (by omega) hn
          (by rw [hgtau, word_g8, ← pow_add] at hv; exact hv) hbo) (le_of_eq (by simp [termNameBd]))
      intro rd hlow hL rd' hag
      obtain ⟨⟨-, -, -, -, -, hrs, -⟩, -⟩ := hM rd hlow hL rd' hag
      rw [word_g8]; exact (rs_eq_run_iff _ _ _).mpr hrs
  · intro fp' k hk _ i hi
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hk
    rw [hkLin] at hi
    exact regionL_append.mp hi
  · intro fp' rd hB hL k hk
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hk
    rw [hkLin]
    exact Main.memL_append.mpr ⟨hL, hB⟩
  intro fp' outs ho rd hlow hB hL
  have hM := hMem (fp' + fs "check_opening_terminal") rd hlow hL hB rd (fun _ _ => rfl)
  obtain ⟨σ, hpar, hh, s17, s19, s21, s25, s1750⟩ :=
    term_body_complete (hpre rd hlow hL).1 hlens hacc hM
  have hpar' := hpar
  rw [core14_params] at hpar'
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at hpar'
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, -⟩ := hpar'
  have hh' := hh
  rw [term_body, holdsList_append, holdsList_flatten_noRet _ tSegs_noRet] at hh'
  obtain ⟨hseg, -⟩ := hh'
  have g0 := hseg tPre (by unfold tSegs; simp)
  have g1 := hseg ((List.range 92).map selBlk).flatten (by unfold tSegs; simp)
  have g2 := hseg ((List.range 112).map claimBlk).flatten (by unfold tSegs; simp)
  have g3 := hseg tPostA (by unfold tSegs; simp)
  have g5 := hseg tPostB (by unfold tSegs; simp)
  rw [holdsList_range_flatten 92 selBlk (fun _ => rfl), and_true] at g1
  rw [holdsList_range_flatten 112 claimBlk claimBlk_noRet, and_true] at g2
  obtain ⟨f18, f20, f22, f24, f32, f33, f34⟩ := tpre_facts g0
  have f1749 := tpostA_facts g3
  obtain ⟨f1816, f1825⟩ := tpostB_facts g5
  have hX : ∀ k < 28, LoadHolds rd (σ (.n 13)) k (ptw.getD k 0) := fun k hk => by
    rw [q13]; exact readsAt_get (hallP rd hlow hL) (by omega)
  have hlo : ∀ c < 92, LoadHolds rd (σ (.n 9)) c (gen ^ O c) := fun c hc => by
    rw [q9, hO]; exact readsAt_map_iff.mp (hallO rd hlow hL) c (by rw [stackOffsets_length, hcl92]; exact hc)
  have hlk : ∀ c < 92, LoadHolds rd (σ (.n 10)) c (gen ^ K c) := fun c hc => by
    rw [q10, hK]; exact readsAt_map_iff.mp (hallK rd hlow hL) c (by rw [hcl92]; exact hc)
  have hsm := fun c (hc : c < 92) => sel_more (g1 c hc) (hK28 c hc) (hlo c hc) (hlk c hc)
  have hsv : ∀ c < 92, σ (.n (selV c)) = sel c := fun c hc => by
    rw [hsel]; exact (sel_fact (g1 c hc) (hK28 c hc) (hO28 c hc) (hlo c hc) (hlk c hc) hX).1
  have h1749 : σ (.n 1749) = gen ^ (64 * (τ + 9)) := by
    rw [f1749, q6, hgtau, word_g8, word_gen, ← pow_add, ← pow_succ, sqI_gen]; norm_num
  have h1825 : σ (.n 1825) = ofK (Parameters.gpow (fp' + fs "check_opening_terminal" + 35 + 35 + 35 + 35)) *
      gen ^ (64 * (τ + 8)) := by
    rw [f1825, s1750, q6, hgtau, word_g8, ← pow_add, sqI_gen]; norm_num
  refine ⟨σ, hpar, dispOk_of fun p hp => ?_, hh, ?_, ?_, ?_, ?_⟩
  · rw [term_disps] at hp
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hp
    exact (hsm c (List.mem_range.mp hc)).2.2
  · rw [term_allocs]
    simp only [List.map_cons, List.map_nil, Sum.elim_inr, Sum.elim_inl, id]
    rw [h1749, logG_g _ (by omega)]
    rfl
  · rw [term_allocs]
    simp only [List.map_cons, List.map_nil]
    rw [s17, s19, s21, s25, s1750, termBases]
    rfl
  · rw [term_calls' σ]
    refine callsMatch_of σ _ _ outs (by simp) ho fun i h1 h2 h3 => ?_
    simp only [List.length_map, List.length_range] at h1
    simp only [List.getElem_map, List.getElem_range]
    unfold termCall termKid
    split_ifs with i0 i1 i2 i3 i4
    · simp only [Main.mkCall, List.map_cons, List.map_nil]
      exact ⟨trivial, trivial, fun _ => ⟨by rw [s17, f18, q0, q13, q3], fun hO => hO.1.symm⟩⟩
    · simp only [Main.mkCall, List.map_cons, List.map_nil]
      exact ⟨trivial, trivial, fun _ => ⟨by rw [s19, f20, q1, q13, q4], fun hO => hO.1.symm⟩⟩
    · simp only [Main.mkCall, List.map_cons, List.map_nil]
      exact ⟨trivial, trivial, fun _ => ⟨by rw [s21, f22, q1, f24, q13, q6], fun hO => hO.1.symm⟩⟩
    · simp only [Main.mkCall, List.map_cons, List.map_nil]
      exact ⟨trivial, by rw [f32, q5], fun _ => ⟨by rw [f33, q5, s25, q13], fun hO => hO.1.symm⟩⟩
    · have hc : i - 4 < 92 := by omega
      simp only [Main.mkCall, List.map_cons, List.map_nil]
      refine ⟨by rw [(hsm _ hc).2.1, logG_g _ (by have := hK28 _ hc; omega)], trivial,
        fun _ => ⟨by rw [(hsm _ hc).1, q13], fun hO => by rw [hO.1, hsv _ hc]⟩⟩
    · simp only [Main.mkCall, List.map_cons, List.map_nil]
      exact ⟨trivial, trivial, fun _ => ⟨by rw [s1750, q11, q13, f1816, q6], fun hO => hO.1.symm⟩⟩
  · have hℓ : ∀ j < 109, ((claims.map (·.point)).getD j []).length < 33 := fun j hj => by
      have hjl : j < claims.length := by rw [hcl]; exact lt_trans hj (by decide)
      rw [List.getD_eq_getElem _ _ (by simpa using hjl), List.getElem_map]
      obtain ⟨-, h5, h6, -⟩ := hpts j claims[j].point (by simp [hjl])
      by_cases hj5 : j < 5
      · have := congrArg List.length (h5 hj5); rw [List.length_take] at this; omega
      · have := congrArg List.length (h6 (by omega) (by show j < 109; omega))
        rw [List.length_take] at this; omega
    generalize hbd : fp' + fs "check_opening_terminal" = b at s17 s19 s21 s25 s1750 h1825 ⊢
    intro q hq
    have hb := List.all_eq_true.mp term_loads q hq
    obtain ⟨p, off⟩ := q
    simp only [termLoadB, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq] at hb
    rcases hb with ⟨t, ht, hp, hlo⟩ | ⟨j, hj, ⟨hk3, hp⟩, h0⟩
    · simp only [termLoadT, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        (dsimp only at hp hlo ⊢; subst hp)
      · obtain ⟨i, hi, hr⟩ := addr_in_region hallP hlow hL (j := off) (by rw [hptl]; omega)
        exact ⟨i, by rw [q13]; exact hi, Or.inl hr⟩
      · exact ⟨b + 35 + 35 + 35 + off, by rw [s25, addr_k], Or.inr (region_buf
          (w := twPi a2 (fun k => ptw.getD k 0) n) (by simp [bufL, termBases, termOwn])
          (by simp [twPi]; omega))⟩
      · exact ⟨b + 35 + 35 + 35 + (n + off), by rw [f34, s25, q5, hglm, addr_gen, Nat.add_assoc],
          Or.inr (region_buf (w := twPi a2 (fun k => ptw.getD k 0) n)
            (by simp [bufL, termBases, termOwn]) (by simp [twPi]; omega))⟩
      · obtain ⟨i, hi, hr⟩ := addr_in_region hallO hlow hL (j := off)
          (by simp only [List.length_map, stackOffsets_length, hcl92]; omega)
        exact ⟨i, by rw [q9]; exact hi, Or.inl hr⟩
      · obtain ⟨i, hi, hr⟩ := addr_in_region hallK hlow hL (j := off)
          (by simp only [List.length_map, hcl92]; omega)
        exact ⟨i, by rw [q10]; exact hi, Or.inl hr⟩
      · obtain ⟨i, hi, hr⟩ := addr_in_region hallCp hlow hL (j := off)
          (by simp only [List.length_map, List.length_range]; show off < 109; omega)
        exact ⟨i, by rw [q7]; exact hi, Or.inl hr⟩
      · obtain ⟨i, hi, hr⟩ := addr_in_region hallL hlow hL (j := off)
          (by rw [length_powersFrom', hcl]; exact hlo)
        exact ⟨i, by rw [q8]; exact hi, Or.inl hr⟩
      · obtain ⟨i, hi, hr⟩ := addr_in_region hallT hlow hL (j := off) (by rw [hcsl]; omega)
        exact ⟨i, by rw [q12]; exact hi, Or.inl hr⟩
      · exact ⟨b + 35 + 35 + 35 + 35 + off, by rw [s1750, addr_k], Or.inr (region_buf
          (w := twRows fp (ptw.take (τ + 8)) τ) (by simp [bufL, termBases, termOwn])
          (by simp [twRows]; omega))⟩
      · exact ⟨b + 35 + 35 + 35 + 35 + (64 * (τ + 8) + off), by rw [h1825, addr_gen, Nat.add_assoc],
          Or.inr (region_buf (w := twRows fp (ptw.take (τ + 8)) τ)
            (by simp [bufL, termBases, termOwn]) (by simp [twRows]; omega))⟩
    · subst hp h0
      have hj112 : j < 112 := by simpa using hj
      have hj' : j < 109 := by unfold claimKind at hk3; split_ifs at hk3 <;> omega
      obtain ⟨lc, hptr⟩ := claim_ptr_facts hk3 (g2 j hj112)
      have hcp := (hallCp rd hlow hL) j (by simp only [List.length_map, List.length_range]; exact hj')
      simp only [List.getElem_map, List.getElem_range] at hcp
      rw [q7] at lc
      have hv := loadHolds_unique lc hcp
      have hl33 := hℓ j hj'
      generalize ((claims.map (·.point)).getD j []).length = ℓ at hv hl33
      by_cases k0 : claimKind j = 0
      · simp only [k0, ↓reduceIte] at hptr
        exact ⟨b + ℓ, by dsimp only; rw [hptr, s17, hv, addr_gen, Nat.add_zero],
          Or.inr (region_buf (w := twChain bus.point (ptw.take bus.point.length) bus.point.length)
            (by simp [bufL, termBases, termOwn]) (by simp [twChain]; omega))⟩
      · by_cases k1 : claimKind j = 1
        · rw [ite_neg' k0, ite_pos' k1] at hptr
          exact ⟨b + 35 + ℓ, by dsimp only; rw [hptr, s19, hv, addr_gen, Nat.add_zero],
            Or.inr (region_buf (w := twChain chisF (ptw.take chisF.length) chisF.length)
              (by simp [bufL, termBases, termOwn]) (by simp [twChain]; omega))⟩
        · rw [ite_neg' k0, ite_neg' k1] at hptr
          exact ⟨b + 35 + 35 + ℓ,
            by dsimp only; rw [hptr, s21, hv, addr_gen, Nat.add_zero],
            Or.inr (region_buf (w := twChain (chisF.take τ) ((ptw.drop 8).take τ) τ)
              (by simp [bufL, termBases, termOwn]) (by simp [twChain]; omega))⟩

/-- **`check_opening_terminal` is complete, placed, by a bounded tree** (TRIAGE #42, #43):
`CompleteTermAtB`. -/
theorem check_opening_terminal_completeAtB (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) :
    CompleteTermAtB fs cert κ TCtx PCtx (termBound fs) :=
  (check_opening_terminal_completeAtW fs cert (Θ := Empty) (fun e => e.elim) κ).toB

/-- **`check_opening_terminal` is complete, placed** (TRIAGE #42, #43): `CompleteTermAt`. -/
theorem check_opening_terminal_completeAt (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) :
    CompleteTermAt fs cert κ TCtx PCtx :=
  fun layout bus claims lam fp cs w chis args Lin h1 h2 h3 h4 =>
    (check_opening_terminal_completeAtB fs cert κ layout bus claims lam fp cs w chis args Lin h1 h2 h3
      h4).toCompleteAtD

end
end LeanVM.Guest.B1
