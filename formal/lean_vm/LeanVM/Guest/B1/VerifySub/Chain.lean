/-
  LeanVM.Guest.B1.VerifySub.Chain

  `verify_sub`'s phases chained into the deferring verifier's acceptance of the decoded child
  proof: `Main.SubSoundW bytecode vsPiOf` from the phases' statements.
-/

module

public import LeanVM.Guest.B1.VerifySub.Phases
public import LeanVM.Guest.B1.Whir.Run
public import LeanVM.Guest.B1.Whir.FactsAll
public import LeanVM.Guest.B1.Common.MemSize
public import LeanVM.Guest.B1.Digest.Steps
public import LeanVM.Guest.B1.Stack.Certify
public import LeanVM.Protocol.WithHashBridge
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_sub»

/-!
# The phases, chained

`deferFlat`: the deferring verifier's program (`deferringVerifierProgram`) regrouped phase by phase
(`deferringVerifierProgram_flat`). The pure steps between the phases: `buildLayout` places the two
memory columns and `q_keccak` (`placement_of_buildLayout`), so `bindPublicInput` runs to
`vsPublicClaims` (`runsTo_bindPublicInput`), the `q_keccak` placement and the memory term
(`runsTo_memoryTermClaim`) are found; the configuration of a stack of `16 .. 30` variables at a rate
`1 .. 4` has a level (`ladder_cons`), so `commitStack` reads the root's two words
(`runsWith_commitStack`).

`subSoundW_of_phases`: from the phases' statements (`Phases.lean`), a run of `verify_sub`'s body
returns nothing, holds the fresh claim's cells at `defer_out`, and the deferring verifier accepts
the decoded proof `vsPiOf` (the stream's words up to the cursor handed to `open_stacked`, then
`open_stacked`'s words and openings) for the statement at its arguments: `Main.SubSoundW bytecode
vsPiOf`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The program, regrouped -/

/-- **The deferring verifier's program, phase by phase.** -/
def deferFlat (fresh : FreshClaim) (bytecode : List K) (pi : Digest) : VerifierProgram Bool :=
  (readAnnouncedSizes bytecode).bind fun ll ↦
  (commitStack ll.1.stackLog ll.2).bind fun _ ↦
  (readOod ll.1.stackLog).bind fun ood ↦
  (verifyLink (freshSplit fresh) ll.1).bind fun link ↦
  (bindPublicInput ll.1 pi).bind fun pub ↦
  (keccakValidity ll.1 link).bind fun kv ↦
  (liftOption (ll.1.placements.getD qkeccak none)).bind fun qp ↦
  (ringSwitch [keccakRingClaim qp kv.2.1 kv.2.2, link.ring]).bind fun rb ↦
  (memoryTermClaim ll.1 link).bind fun mt ↦
  (verifyStackedOpening ll.1.stackLog ll.2
    (rb.1 :: mt :: (linkColumnClaims link ++ pub ++ kv.1).filterMap (·.onStack ll.1) ++ [ood])
    rb.2).bind fun _ ↦
  VerifierProgram.ret true

theorem deferringVerifierProgram_flat (fresh : FreshClaim) (bytecode : List K) (pi : Digest) :
    deferringVerifierProgram fresh bytecode pi = deferFlat fresh bytecode pi := by
  simp only [deferringVerifierProgram, verifyExecution, deferFlat, VerifierProgram.bind_eq,
    VerifierProgram.pure_eq, VerifierProgram.bind_assoc]

/-! ## The pure steps -/

theorem liftOption_some {α : Type} (a : α) : liftOption (some a) = VerifierProgram.ret a := rfl

theorem runsTo_liftOption {α : Type} {o : Option α} {a : α} (h : o = some a) (s : Fs) :
    RunsTo (liftOption o) s [] a s := by
  rw [h, liftOption_some]; exact runsTo_ret a s

theorem foldl_set_length (f : ℕ → ℕ) : ∀ (o : List ℕ) (acc : List ℕ × ℕ),
    (o.foldl (fun acc i ↦ (acc.1.set i acc.2, acc.2 + f i)) acc).1.length = acc.1.length
  | [], _ => rfl
  | i :: o, acc => by
    simp only [List.foldl_cons, foldl_set_length f o, List.length_set]

theorem stackOffsets_length (sizes : List ℕ) : (stackOffsets sizes).1.length = sizes.length := by
  simp only [stackOffsets]
  rw [foldl_set_length (fun i ↦ 2 ^ sizes.getD i 0)]
  simp

/-- **`buildLayout` places the memory's two columns and `q_keccak`.** -/
theorem placement_of_buildLayout {bytecode : List K} {lm : ℕ} {rows : List ℕ} {layout : Layout}
    (h : buildLayout bytecode lm rows = some layout) {c : ℕ} (hc : c < 3) :
    ∃ p : Placement, layout.placements.getD c none = some p := by
  obtain ⟨-, -, -, -, -, -, hpl⟩ := Stack.buildLayout_some h
  rw [hpl]
  generalize hk : columnKappas tables lm _ = kappas
  have hkl : 3 ≤ kappas.length := by rw [← hk]; simp [columnKappas]
  have hq : qkeccakSlot c = none := by
    interval_cases c <;> decide +kernel
  have hlen : (stackOffsets (stackBlocks.map fun b ↦ kappas.getD b.column 0)).1.length =
      stackBlocks.length := by rw [stackOffsets_length]; simp
  have hbl : 3 ≤ stackBlocks.length := by decide +kernel
  have hcol : ∀ i < 3, (stackBlocks.map (·.column))[i]? = some i := by
    intro i hi; interval_cases i <;> decide +kernel
  have hlk : ∃ o, ((stackBlocks.map (·.column)).zip
      (stackOffsets (stackBlocks.map fun b ↦ kappas.getD b.column 0)).1).lookup c = some o := by
    generalize ho : (stackOffsets (stackBlocks.map fun b ↦ kappas.getD b.column 0)).1 = os at hlen
    have hos : c < os.length := by omega
    obtain ⟨o, ho'⟩ : ∃ o, os[c]? = some o := ⟨os[c], List.getElem?_eq_getElem hos⟩
    clear ho
    have key : ∀ (cols : List ℕ) (os : List ℕ) (j : ℕ), j ≤ c → cols[c - j]? = some c →
        (∀ i < c - j, cols[i]? ≠ some c) → os[c - j]? = some o → ∃ o', (cols.zip os).lookup c = some o' := by
      intro cols os j _ hc1 hne ho1
      induction cols generalizing os j with
      | nil => simp at hc1
      | cons x xs ih =>
        cases os with
        | nil => simp at ho1
        | cons y ys =>
          simp only [List.zip_cons_cons, List.lookup_cons]
          by_cases hx : x = c
          · exact ⟨y, by simp [hx]⟩
          · have hcj : c - j ≠ 0 := by
              intro h0; rw [h0] at hc1; simp at hc1; exact hx hc1
            rw [show (c == x) = false from beq_eq_false_iff_ne.mpr fun h ↦ hx h.symm]
            refine ih ys (j + 1) (by omega) ?_ ?_ ?_
            · rw [show c - (j + 1) = c - j - 1 by omega]
              rw [show c - j = (c - j - 1) + 1 by omega] at hc1; simpa using hc1
            · intro i hi h; exact hne (i + 1) (by omega) (by simpa using h)
            · rw [show c - (j + 1) = c - j - 1 by omega]
              rw [show c - j = (c - j - 1) + 1 by omega] at ho1; simpa using ho1
    refine key _ os 0 (Nat.zero_le _) (by simpa using hcol c hc) (fun i hi ↦ ?_) (by simpa using ho')
    rw [hcol i (by omega)]; simp; omega
  obtain ⟨o, ho⟩ := hlk
  have hst : (stack kappas).1 = (stackBlocks.map (·.column)).zip
      (stackOffsets (stackBlocks.map fun b ↦ kappas.getD b.column 0)).1 := rfl
  have hkc : c < kappas.length := by omega
  refine ⟨⟨kappas[c], o⟩, ?_⟩
  simp only [List.getD_eq_getElem?_getD] at ho
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_zipIdx,
    zero_add, List.getElem?_eq_getElem hkc, Option.map_some, Option.getD_some, hq, hst, ho]

/-- **The public input's binding**: a challenge, the memory's placement found, the two claims. -/
theorem runsTo_bindPublicInput {layout : Layout} (p : Placement)
    (hp : layout.placements.getD memory0 none = some p) (pi : Digest) (s : Fs) :
    RunsTo (bindPublicInput layout pi) s [] (vsPublicClaims layout pi s.squeeze.1) s.squeeze.2 := by
  have h := (runsTo_sampleE s).bind (f := fun rm ↦ (do
      let halves := digestHalves pi
      let memory ← liftOption (layout.placements.getD memory0 none)
      let publicPoint := rm :: List.replicate (memory.variableCount - 1) 0
      let publicLimbs := ([0, 1] : List (Fin 2)).map fun limb ↦
        multilinearEval [ofK (halves.1.limb limb), ofK (halves.2.limb limb)] [rm]
      return List.zipWith (fun column value ↦ (⟨column, publicPoint, value⟩ : ColumnClaim))
        [memory0, memory1] publicLimbs : VerifierProgram (List ColumnClaim)))
    ((runsTo_liftOption hp s.squeeze.2).bind (f := fun memory ↦ (pure (List.zipWith
        (fun column value ↦ (⟨column, s.squeeze.1 :: List.replicate (memory.variableCount - 1) 0,
          value⟩ : ColumnClaim)) [memory0, memory1]
        (([0, 1] : List (Fin 2)).map fun limb ↦ multilinearEval [ofK ((digestHalves pi).1.limb limb),
          ofK ((digestHalves pi).2.limb limb)] [s.squeeze.1])) : VerifierProgram (List ColumnClaim)))
      (runsTo_ret _ _))
  simp only [List.nil_append] at h
  refine RunsTo.of_eq h rfl rfl ?_ rfl
  rw [List.getD_eq_getElem?_getD] at hp
  simp [vsPublicClaims, Stack.publicClaimsPure, hp]

/-- **The memory term**: both memory placements found. -/
theorem runsTo_memoryTermClaim {layout : Layout} (link : LinkEnd) (p0 p1 : Placement)
    (h0 : layout.placements.getD memory0 none = some p0)
    (h1 : layout.placements.getD memory1 none = some p1) (s : Fs) :
    ∃ mt, Stack.memoryTermPure layout link = some mt ∧ RunsTo (memoryTermClaim layout link) s [] mt s := by
  refine ⟨_, by simp only [Stack.memoryTermPure, h0, h1]; rfl, ?_⟩
  have e : memoryTermClaim layout link = VerifierProgram.ret
      (fun (x : List E) ↦ sumE ([(p0.stackPoint link.memoryPoint layout.stackLog, link.memoryScales.1),
        (p1.stackPoint link.memoryPoint layout.stackLog, link.memoryScales.2)].map
          fun (point, scale) ↦ scale * eqEval point x), link.memoryValue) := by
    simp only [memoryTermClaim, h0, h1, liftOption_some, VerifierProgram.bind_eq,
      VerifierProgram.pure_eq, VerifierProgram.ret_bind]
  rw [e]; exact runsTo_ret _ s

theorem levelsB_nil (c : Whir.OsCfg) (logN lvl : ℕ) (lvs : List Whir.OsLv) :
    Whir.levelsB c logN lvl lvs [] = false := by
  rcases lvs with _ | ⟨_, _ | _⟩ <;> rfl

/-- **A stack of `16 .. 30` variables at a rate `1 .. 4` has a first level.** -/
theorem ladder_cons {μ r : ℕ} (h1 : Whir.minOpenLog ≤ μ) (h2 : μ ≤ 30) (h3 : 1 ≤ r) (h4 : r ≤ 4) :
    ∃ level rest, Whir.ladder μ r = some (level :: rest) := by
  have hmo : Whir.minOpenLog = 16 := rfl
  obtain ⟨cfg, hcfg, hok⟩ := Whir.candB_sound (Whir.candB_all (μ - Whir.minOpenLog) (r - 1)
    (by have : Whir.ligNSizes = 15 := rfl; omega) (by omega))
  rw [show μ - Whir.minOpenLog + Whir.minOpenLog = μ by omega, show r - 1 + 1 = r by omega] at hcfg
  rcases cfg with _ | ⟨level, rest⟩
  · exfalso
    have hl := hok.2.2.2.2.2.2.2.2.2.2.2.2.2
    rw [levelsB_nil] at hl
    exact absurd hl (by decide)
  · exact ⟨level, rest, hcfg⟩

/-- **The stack's commitment**: its two words, the root and the stack's shape appended. -/
theorem runsWith_commitStack {μ r : ℕ} (h1 : Whir.minOpenLog ≤ μ) (h2 : μ ≤ 30) (h3 : 1 ≤ r)
    (h4 : r ≤ 4) (s : Fs) (x0 x1 : E) :
    Whir.RunsWith (commitStack μ r) s [x0, x1] [] [] () ((s.absorb x0 dsObserve).absorb x1 dsObserve)
      [(digestFromHalves (x0, x1), Whir.stackShape μ r)] := by
  obtain ⟨level, rest, hcfg⟩ := ladder_cons h1 h2 h3 h4
  rw [Whir.commitStack_eq hcfg]
  exact Whir.runsWith_commitP s x0 x1 _ _ []

/-! ## Acceptance -/

/-- **A run of the regrouped program to its end is an acceptance.** -/
theorem verifyDeferred_of_runsWith {bytecode : List K} {seed pi : Digest} {fresh : FreshClaim}
    {s0 s1 : Fs} (hs0 : s0.Carries ⟨keccakF1600 (seedInput seed pi), [], none⟩) {xs : List E}
    {os : List (List Opening)} {roots : List (Digest × ℕ × ℕ)}
    (h : Whir.RunsWith (deferFlat fresh bytecode pi) s0 xs os [] true s1 roots) :
    verifyDeferred bytecode seed pi fresh ⟨xs, os⟩ = true := by
  obtain ⟨sp, -, hsp⟩ := h ⟨keccakF1600 (seedInput seed pi), [], none⟩ hs0 [] []
  simp only [List.append_nil] at hsp
  rw [← deferringVerifierProgram_flat] at hsp
  rw [verifyDeferred_eq_withHash]
  simp only [verifyDeferredWithHash, Compile.runProofWithHash]
  simp only [runId] at hsp
  exact congrArg (fun o : Option (Bool × VerifierProgramState) ↦ match o with
    | some (true, s) => (s.stream.isEmpty && s.openings.isEmpty : Bool)
    | _ => false) hsp

/-! ## The chain -/

theorem vs_params (σ : Val) : (fn% «verify_sub»).params.map σ =
    [σ (.n (val% «verify_sub» "pi_0")), σ (.n (val% «verify_sub» "pi_1")),
      σ (.n (val% «verify_sub» "seed_0")), σ (.n (val% «verify_sub» "seed_1")),
      σ (.n (val% «verify_sub» "g_squares")), σ (.n (val% «verify_sub» "defer_out"))] := rfl

theorem instructionVariableCount_eq {bytecode : List K}
    (hbl : bytecode.length = 2 ^ (Main.bytecodeLog + bytecodeSlotBits)) :
    Node.instructionVariableCount bytecode = Main.bytecodeLog := by
  rw [Node.instructionVariableCount, hbl, Nat.shiftRight_eq_div_pow, pow_add,
    Nat.mul_div_cancel _ (by positivity), Nat.log2_two_pow]

theorem splitColumns_length : (splitColumns tables).length = guest_const% N_SPLIT := by
  decide +kernel

/-- **`verify_sub` is sound**, given its phases' statements: a run of its body returns nothing, and
the deferring verifier accepts the decoded child proof `vsPiOf` for the statement at its
arguments, the fresh claim's cells at `defer_out`. -/
theorem subSoundW_of_phases (hSeed : PhSeed) (hSizes : PhSizes) (hRoot : PhRoot) (hOod : PhOod)
    (hLink : PhLink) (hKeccak : PhKeccak) (hRing : PhRing) (hOpen : PhOpen) (hExport : PhExport)
    (bytecode : List K) : Main.SubSoundW bytecode vsPiOf := by
  intro hbl κ L hκ C V hU hle σ rets hb hpre
  have R : VsRun bytecode L C V σ rets := ⟨hbl, hκ, hU, hle, hb, hpre⟩
  obtain ⟨hrets, hcells⟩ := hExport bytecode L C V σ rets R
  refine ⟨hrets, _, _, _, _, _, _, vs_params σ, vsSeed σ, vsPi σ, vsFresh L.read σ,
    (digestScalars_digestOfScalars _).symm, (digestScalars_digestOfScalars _).symm, ?_, ?_, hcells,
    ?_⟩
  · simp only [vsFresh, wordsAt_length]; exact (instructionVariableCount_eq hbl).symm
  · simp only [vsFresh, wordsAt_length, splitColumns_length]
  -- the phases
  have hs0 := hSeed bytecode L C V σ rets R
  obtain ⟨hw0, hr1, hbuild, hl1, hl4, hst1, hst2, hsize, hrate⟩ := hSizes bytecode L C V σ rets R
  obtain ⟨hw1, habs⟩ := hRoot bytecode L C V σ rets R
  obtain ⟨hw2, hr3, -⟩ := hOod bytecode L C V σ rets R
  obtain ⟨xsL, link, s4, hw3, hcK, hr4, hsq, hLF⟩ := hLink bytecode L C V σ rets R
  obtain ⟨xsK, outs, kp, ks, s6, hw4, hcR, hr6, hpend, hcap, hKF⟩ :=
    hKeccak bytecode L C V σ rets R link hLF
  obtain ⟨p0, hp0⟩ := placement_of_buildLayout hbuild (c := memory0) (by decide)
  obtain ⟨p1, hp1⟩ := placement_of_buildLayout hbuild (c := memory1) (by decide)
  obtain ⟨qp, hqp⟩ := placement_of_buildLayout hbuild (c := qkeccak) (by decide)
  obtain ⟨f, g, rho, lam, hw5, hr8, hRF⟩ :=
    hRing bytecode L C V σ rets R link outs kp ks s6 qp hLF hKF hpend hcap hqp
  obtain ⟨mt, hmt, hrmt⟩ := runsTo_memoryTermClaim link p0 p1 hp0 hp1 (vsF8 σ)
  obtain ⟨hcur, s9, roots9, hr9⟩ :=
    hOpen bytecode L C V σ rets R link outs kp ks f g rho lam qp mt hLF hKF hRF hqp hmt
  -- the run
  have hpub := runsTo_bindPublicInput p0 hp0 (vsPi σ) s4
  rw [hsq] at hpub
  have hcom := runsWith_commitStack hst1 hst2 hl1 hl4 (vsF1 σ) (σ (.n (val% «verify_sub» "x@9")))
    (σ (.n (val% «verify_sub» "x@10")))
  rw [habs] at hcom
  set osW := vsOsW L.read V ((vsLayout bytecode σ).stackLog - Whir.minOpenLog) (vsLir σ) (vsOsArgs σ) (vsOsRets σ)
    with hosW
  have hrun : Whir.RunsWith (deferFlat (vsFresh L.read σ) bytecode (vsPi σ)) (vsF0 σ)
      (vsAnnounced σ ++ ([σ (.n (val% «verify_sub» "x@9")), σ (.n (val% «verify_sub» "x@10"))] ++
        ([vsOodNonce σ, vsOodValue L.read σ] ++ (xsL ++ ([] ++ (xsK ++ ([] ++
          ([vsRingNonce σ] ++ ([] ++ (osW.1 ++ []))))))))))
      ([] ++ ([] ++ ([] ++ ([] ++ ([] ++ ([] ++ ([] ++ ([] ++ ([] ++ (osW.2 ++ []))))))))))
      [] true s9 roots9 := by
    refine Whir.RunsWith.bind' (Whir.RunsTo.withRoots hr1 []) ?_
    refine Whir.RunsWith.bind' hcom ?_
    refine Whir.RunsWith.bind' (Whir.RunsTo.withRoots hr3 _) ?_
    refine Whir.RunsWith.bind' (Whir.RunsTo.withRoots hr4 _) ?_
    refine Whir.RunsWith.bind' (Whir.RunsTo.withRoots hpub _) ?_
    refine Whir.RunsWith.bind' (Whir.RunsTo.withRoots hr6 _) ?_
    refine Whir.RunsWith.bind' (Whir.RunsTo.withRoots (runsTo_liftOption hqp s6) _) ?_
    refine Whir.RunsWith.bind' (Whir.RunsTo.withRoots hr8 _) ?_
    refine Whir.RunsWith.bind' (Whir.RunsTo.withRoots hrmt _) ?_
    refine Whir.RunsWith.bind' hr9 ?_
    exact Whir.runsWith_ret true s9 roots9
  -- the decoded proof
  set W := vsAnnounced σ ++ [σ (.n (val% «verify_sub» "x@9")), σ (.n (val% «verify_sub» "x@10"))] ++
    [vsOodNonce σ, vsOodValue L.read σ] ++ xsL ++ xsK ++ [vsRingNonce σ] with hW
  have hA : ReadsAt L.read (vsStream σ) (vsAnnounced σ ++
      [σ (.n (val% «verify_sub» "x@9")), σ (.n (val% «verify_sub» "x@10"))] ++
      [vsOodNonce σ, vsOodValue L.read σ]) :=
    Digest.readsAt_append.2 ⟨Digest.readsAt_append.2 ⟨hw0, hw1⟩, by
      rw [show (vsAnnounced σ ++ [σ (.n (val% «verify_sub» "x@9")),
        σ (.n (val% «verify_sub» "x@10"))]).length = 10 from rfl]; exact hw2⟩
  have hlA : (vsAnnounced σ ++ [σ (.n (val% «verify_sub» "x@9")), σ (.n (val% «verify_sub» "x@10"))] ++
      [vsOodNonce σ, vsOodValue L.read σ]).length = 12 := rfl
  have hB := Digest.readsAt_append.2 ⟨hA, by rw [hlA]; exact hw3⟩
  have hlB : (vsAnnounced σ ++ [σ (.n (val% «verify_sub» "x@9")), σ (.n (val% «verify_sub» "x@10"))] ++
      [vsOodNonce σ, vsOodValue L.read σ] ++ xsL).length = 12 + xsL.length := by
    rw [List.length_append, hlA]
  have hC := Digest.readsAt_append.2 ⟨hB, by rw [hlB, ← hcK]; exact hw4⟩
  have hlC : (vsAnnounced σ ++ [σ (.n (val% «verify_sub» "x@9")), σ (.n (val% «verify_sub» "x@10"))] ++
      [vsOodNonce σ, vsOodValue L.read σ] ++ xsL ++ xsK).length = 12 + xsL.length + xsK.length := by
    rw [List.length_append, hlB]
  have hWr : ReadsAt L.read (vsStream σ) W := Digest.readsAt_append.2 ⟨hC, by
    rw [hlC, pow_add, ← mul_assoc, ← hcK, ← hcR]
    intro k hk
    simp only [List.length_cons, List.length_nil] at hk
    obtain rfl : k = 0 := by omega
    exact hw5⟩
  have hcurW : vsCursor σ = vsStream σ * gen ^ W.length := by
    rw [hcur, hcR, hcK, hW, List.length_append, hlC]
    simp only [mul_assoc, ← pow_add, ← pow_succ, List.length_cons, List.length_nil]
  have hWlen : W.length ≤ 2 ^ 32 := by
    by_contra hlt
    have h32 : 2 ^ κ ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) hκ
    have h2 := mem_size_big hκ L (p := vsStream σ) (n := 2 ^ 32 + 1) (by norm_num)
      fun j hj ↦ ⟨_, hWr j (by omega)⟩
    omega
  have hne : vsStream σ ≠ 0 := ne_zero_of_load (by omega) L (hw0 0 (by simp [vsAnnounced]))
  have hπ : vsPiOf L.read σ V = ⟨W ++ osW.1, osW.2⟩ := by
    have hidx : dispatchIdx (σ (.n (val% «verify_sub» "size_sel"))) = (vsLayout bytecode σ).stackLog - Whir.minOpenLog :=
      dispatchIdx_eq (by have : Whir.openArms = 15 := rfl; have : Whir.minOpenLog = 16 := rfl; omega) hsize
    have hrt : rateOf (σ (.n (val% «verify_sub» "rate_sel"))) = vsLir σ := by
      rw [hrate, rateOf_eq hl1 hl4]
    simp only [vsPiOf, piOfW, hidx, hrt, hosW]
    rw [show σ (.n (val% «verify_sub» "stream")) = vsStream σ from rfl,
      cursorLen_eq hne hcurW hWlen, wordsAt_eq hWr]
  rw [hπ]
  refine verifyDeferred_of_runsWith hs0 (Whir.RunsWith.of_eq hrun rfl ?_ (by simp) rfl rfl rfl rfl)
  simp [hW, List.append_assoc]

end
end LeanVM.Guest.B1.VerifySub
