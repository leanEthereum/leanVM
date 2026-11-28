/-
  LeanVM.Guest.B1.VsC.CertifyA

  `certify_stack` completes placed: `CertifyStackCompleteA`.
-/

module

public import LeanVM.Guest.B1.VsC.CertifyR
public import LeanVM.Guest.B1.VsC.Log2A
public import LeanVM.Guest.B1.VsC.RstA

/-!
# `certify_stack`, placed

`certify_stack(kappa_base, g_squares)` placed at frame `fp` and cursor `c`: its five `HeapBuf`s
(`8, 8, 8, 8, 104` words) at `c`, holding its honest words (`csWords`); its one callee
`log2_ceil_in_the_exponent__L16_L34` (`log2_placed`) at the aligned base past them. On each memory
the valuation is the forward evaluation (`fwdVal`), its oracle the buffers' pointers and `log2`'s
return `g^stackLog` (`csOrc`); every atom holds (`cs_run`); the node pops the order (`stackHints`),
its only witness, every node exact. The template's facts are one kernel decision (`csChecks`).
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Stack LeanVM.Guest.B1.Whir LeanVM.Guest.B1.Fwd LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

/-! ## The template's facts -/

/-- `certify_stack`'s call. -/
def csCall : Call := ⟨"log2_ceil_in_the_exponent__L16_L34", [.n 301, .n 1], [.n 302], true⟩

/-- A load of fresh shape is no store. -/
def csFreshB (S : List Atom) (a : Atom) : Bool :=
  match a with
  | .load d p _ => !(freshShape d.idx p.idx && d == .n d.idx && p == .n p.idx) || !S.contains a
  | _ => true

/-- An atom statement, quiet. -/
def quietAtomB : Stmt → Bool
  | .atom a => atomQuiet a
  | _ => false

/-- The statements before the witness, and after it. -/
def csPre : List Stmt := csLoads ++ (csKeys 0 8 12).1 ++ [.atom (.hint (.alloc (.n 163) 8))]

def csPost : List Stmt :=
  [.atom (.hint (.alloc (.n 164) 8))] ++ csRanks 163 164 165 ++
    [.call "log2_ceil_in_the_exponent__L16_L34" [.n 301, .n 1] [.n 302], .atom (.hint (.alloc (.n 303) 104))] ++
    (csOuts 303 164 0 8 304).1 ++
    [.atom (.copy (.n 374) (.n 302)), .atom (.copy (.n 375) (.n 303)), osCst 376 (csW 52), osMul 377 303 376]

/-- The witness. -/
abbrev csWit : Atom := .hint (.witness "stk_group_order" (.heap (.n 163) 0 8))

theorem csBodyA_wit : csBodyA = csPre ++ .atom csWit :: csPost := by
  rw [csBodyA_eq]; simp only [csPre, csPost, List.append_assoc, List.cons_append, List.nil_append]

/-- What the kernel checks of `certify_stack`. -/
def csChecks : Bool :=
  (chk 2 csBody).isSome && csBodyA.all atomOrCall && (atomsOf csBodyA).all (csFreshB (storesOf 2 csBody)) &&
    decide (csBodyA.filterMap Stmt.allocSz =
      [(.n 10, .inl 8), (.n 11, .inl 8), (.n 163, .inl 8), (.n 164, .inl 8), (.n 303, .inl 104)]) &&
    decide (csBodyA.filterMap Stmt.addrS = []) && (atomsOf csBodyA).all trivExact &&
    csPre.all quietAtomB && (atomsOf csPost).all atomQuiet

set_option maxRecDepth 100000 in
theorem csChecks_ok : csChecks = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem cs_callsOfB : callsOfB csBodyA = [csCall] := rfl

/-! ## Pieces -/

theorem ptrAtV_mul (a m : ℕ) : ptrAtV a * gen ^ m = ptrAtV (a + m) := by
  rw [gen_pow_eq_ofK, ptrAtV, ptrAtV, ← ofK_mul, addressOfIndex, addressOfIndex, addressOfIndex, ← pow_add]

/-- Quiet atom statements before a path pop nothing. -/
theorem splice_quiet_pre {rd : Reader} {σ σ' : Val} : ∀ (ss : List Stmt), ss.all quietAtomB = true →
    ∀ (rest : List Memory.Ev) (ks : List (List Pop)), splice rd σ (ss.flatMap (slEvs σ') ++ rest) ks = splice rd σ rest ks
  | [], _, rest, ks => by rw [List.flatMap_nil, List.nil_append]
  | s :: ss, h, rest, ks => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    cases s with
    | atom a =>
      rw [List.flatMap_cons, slEvs, List.singleton_append, List.cons_append, splice,
        splice_quiet_pre ss h.2 rest ks]
      have hq : atomQuiet a = true := h.1
      cases a with
      | hint hh => cases hh <;> simp_all [atomQuiet, Atom.pops, Hint.pops]
      | _ => rfl
    | _ => simp [quietAtomB] at h

/-- The callee's words: `g^T` in, `g^stackLog` out. -/
theorem cs_log2 {bytecode : List K} {lm : ℕ} {rows : List ℕ} {layout : Layout}
    (hbl : buildLayout bytecode lm rows = some layout) (hL : layout.stackLog ≤ 30) :
    csTot (csKv layout) (csρ layout) 8 < 2 ^ 34 ∧
      max 16 (log2Ceil (csTot (csKv layout) (csρ layout) 8)) = layout.stackLog := by
  obtain ⟨hk30, hst, hT⟩ := cs_layout hbl hL
  obtain ⟨-, hR, -⟩ := csOrd_facts layout fun g hg => by have := hk30 g hg; omega
  rw [ranks_total hR] at hst hT
  exact ⟨lt_of_le_of_lt hT (by norm_num), hst.symm⟩

/-- `certify_stack`'s oracle at the cursor `c`: its buffers' pointers, `log2`'s return `g^L`. -/
def csOrc (c L : ℕ) (i : ℕ) : E :=
  if i = 10 then ptrAtV c else if i = 11 then ptrAtV (c + 8) else if i = 163 then ptrAtV (c + 16)
  else if i = 164 then ptrAtV (c + 24) else if i = 303 then ptrAtV (c + 32) else if i = 302 then gen ^ L else 0

set_option maxRecDepth 100000 in
theorem cs_heapB : (atomsOf csBodyA).all (fun a => decide (a = csWit) || (atomHeapDest? a).isNone) = true := by
  decide +kernel

theorem hintAddrs_none {σ : Val} {a : Atom} (h : (atomHeapDest? a).isNone = true) : Memory.Ev.hintAddrs σ (.atom a) = [] := by
  have := heapHintAddrs_atoms (σ := σ) [a] (by simp [h])
  simpa [heapHintAddrs] using this

/-! ## The node -/

variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}

/-- **`certify_stack` completes placed** on a layout `buildLayout` returns, its stack within `2^30`:
its buffers at its cursor `c`, its outputs at `c + 32` placing the stack, its callee past them. -/
theorem cs_placed {k : ℕ} (hk : 11 ≤ k) {bytecode : List K} {lm : ℕ} {rows : List ℕ} {layout : Layout}
    (hbl : buildLayout bytecode lm rows = some layout) (hL : layout.stackLog ≤ 30) {qt qk : ℕ} {R : ℕ → Prop}
    (hRt : ∀ t < 178, R (qt + t)) (hRk : ∀ t < 8, R (qk + t)) (fp c : ℕ)
    (hfc : fp + fs "certify_stack" ≤ c) :
    ∃ e, ((∀ f, fs f < 2 ^ 16) → e ≤ c + 2 ^ 19) ∧ CallAtA fs al cert k "certify_stack" [ptrAtV qk, ptrAtV qt]
      [gen ^ layout.stackLog, ptrAtV (c + 32), ptrAtV (c + 32 + 52)] R
      (fun i => c + 32 ≤ i ∧ i < c + 32 + 104)
      (fun rd => StackPlaced rd layout (gen ^ layout.stackLog) (ptrAtV (c + 32)) (ptrAtV (c + 32 + 52)))
      (fun rd => ExpTables rd (ptrAtV qt) ∧ ReadsAt rd (ptrAtV qk) (kappaSources layout.logMemory layout.tableLogHeights))
      (fun rd t => t.pops coreProgram rd = Prover.stackHints (stackKappas layout) ∧ t.Every (ExactAt coreProgram rd))
      (fs "certify_stack") fp c e := by
  have hck := csChecks_ok
  simp only [csChecks, Bool.and_eq_true, decide_eq_true_eq] at hck
  obtain ⟨⟨⟨⟨⟨⟨⟨hc, haoc⟩, hfr⟩, hasz⟩, hadr⟩, htx⟩, hqpre⟩, hqpost⟩ := hck
  obtain ⟨c', hc⟩ := Option.isSome_iff_exists.mp hc
  obtain ⟨hTlt, hTL⟩ := cs_log2 hbl hL
  obtain ⟨hk30, -, -⟩ := cs_layout hbl hL
  obtain ⟨hperm, -, -⟩ := csOrd_facts layout fun g hg => by have := hk30 g hg; omega
  have hord8 : (csOrd (stackKappas layout)).length = 8 := by
    rw [hperm.length_eq, List.length_range]
  set T := csTot (csKv layout) (csρ layout) 8 with hT
  set L := layout.stackLog with hLdef
  have hlp : coreProgram.loop "certify_stack" = false := by
    rw [Program.loop_of_find? find_certify_stack, Fn.loop, certify_stack_body, csBody_split]; simp
  have hchk : chk [ptrAtV qk, ptrAtV qt].length (fn% «certify_stack»).body = some c' := by
    rw [certify_stack_body]; exact hc
  set w := csOrc c L with hw
  set σ : Reader → Val := fun rd => fwdVal rd w [ptrAtV qk, ptrAtV qt] (fn% «certify_stack»).body with hσ
  set σ0 : Val := fun v => if v.idx = 301 then gen ^ T else σ (fun _ => none) v with hσ0
  set es := csBodyA.flatMap (slEvs σ0) with hes
  have hes' : ∀ τ : Val, csBodyA.flatMap (slEvs τ) = es := fun τ =>
    List.flatMap_congr fun st hs' => slEvs_atomOrCall τ σ0 st (List.all_eq_true.mp haoc st hs')
  have hwalk : ∀ τ : Val, walk τ (fn% «certify_stack»).body = .ret es [.n 374, .n 375, .n 377] := fun τ => by
    rw [certify_stack_body, csBody_split, walk_straight τ _ _ (straight_of_atomOrCall _ haoc), hes']
  have hmemB : ∀ s, s ∈ csBodyA → s ∈ (fn% «certify_stack»).body := fun s hs => by
    rw [certify_stack_body, csBody_split]; exact List.mem_append_left _ hs
  have hS : storesOf [ptrAtV qk, ptrAtV qt].length (fn% «certify_stack»).body = storesOf 2 csBody := by
    rw [certify_stack_body]; rfl
  have hspec : ∀ rd, ∀ s ∈ (fn% «certify_stack»).body,
      GoodS rd (storesOf 2 csBody) w (σ rd) s := fun rd s hs => by
    have := (ev_spec rd w (fn% «certify_stack»).body [ptrAtV qk, ptrAtV qt] hchk).2.2 s hs
    rw [hS] at this; exact this
  have hG : ∀ rd, ∀ a, Stmt.atom a ∈ csBodyA → Good rd (storesOf 2 csBody) w (σ rd) a :=
    fun rd a ha => hspec rd _ (hmemB _ ha)
  have hF : FreshOk (storesOf 2 csBody) csBodyA := fun d p off hm hfs => by
    have := List.all_eq_true.mp hfr _ (mem_atomsOf' hm)
    simpa [csFreshB, hfs] using this
  have hp0 : ∀ rd, σ rd (.n 0) = ptrAtV qk := fun rd => fwd_param hchk (by simp)
  have hp1 : ∀ rd, σ rd (.n 1) = ptrAtV qt := fun rd => fwd_param hchk (by simp)
  have hal1 : ∀ rd d (n : ℕ), Stmt.atom (.hint (.alloc (.n d) n)) ∈ csBodyA → σ rd (.n d) = w d :=
    fun rd d n hm => hG rd _ hm
  have inA : ∀ st ∈ [Stmt.atom (.hint (.alloc (.n 10) 8)), .atom (.hint (.alloc (.n 11) 8)),
      .atom (.hint (.alloc (.n 163) 8)), .atom (.hint (.alloc (.n 164) 8)), .atom (.hint (.alloc (.n 303) 104))],
      st ∈ csBodyA := by
    intro st hst
    rw [csBodyA_eq]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hst
    rcases hst with rfl | rfl | rfl | rfl | rfl
    · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
          (List.mem_cons_self)))))))
    · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
          (List.mem_cons_of_mem _ List.mem_cons_self)))))))
    · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_right _ List.mem_cons_self))))
    · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))))
    · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
        (List.mem_cons_of_mem _ List.mem_cons_self)))
  have h10 : ∀ rd, σ rd (.n 10) = ptrAtV c := fun rd => by
    rw [hal1 rd 10 8 (inA _ (by simp))]; simp [hw, csOrc]
  have h11 : ∀ rd, σ rd (.n 11) = ptrAtV (c + 8) := fun rd => by
    rw [hal1 rd 11 8 (inA _ (by simp))]; simp [hw, csOrc]
  have h163 : ∀ rd, σ rd (.n 163) = ptrAtV (c + 16) := fun rd => by
    rw [hal1 rd 163 8 (inA _ (by simp))]; simp [hw, csOrc]
  have h164 : ∀ rd, σ rd (.n 164) = ptrAtV (c + 24) := fun rd => by
    rw [hal1 rd 164 8 (inA _ (by simp))]; simp [hw, csOrc]
  have h303 : ∀ rd, σ rd (.n 303) = ptrAtV (c + 32) := fun rd => by
    rw [hal1 rd 303 104 (inA _ (by simp))]; simp [hw, csOrc]
  have hcallM : Stmt.call "log2_ceil_in_the_exponent__L16_L34" [.n 301, .n 1] [.n 302] ∈ csBodyA := by
    rw [csBodyA_eq]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self))
  have h302 : ∀ rd, σ rd (.n 302) = gen ^ L := fun rd => by
    have := hspec rd _ (hmemB _ hcallM) (.n 302) List.mem_cons_self
    rw [this]; simp [hw, csOrc]
  have hsp := straight_parts σ0 csBodyA (straight_of_atomOrCall _ haoc)
  have hal : ∀ τ : Val, allocs τ es = [8, 8, 8, 8, 104] := fun τ => by
    rw [← hes' τ, (straight_parts τ csBodyA (straight_of_atomOrCall _ haoc)).2.1, hasz]; rfl
  have hdst : allocDsts es = [.n 10, .n 11, .n 163, .n 164, .n 303] := by rw [hes, hsp.1, hasz]; rfl
  have haddr : addrs es = [] := by rw [hes, hsp.2.2.1, hadr]
  have hcl : calls es = [csCall] := by rw [hes, calls_atomOrCall σ0 _ haoc, cs_callsOfB]
  have hown : ∀ i, c ≤ i → i < c + 136 → ownData cert fp c "certify_stack" [8, 8, 8, 8, 104] es i :=
    fun i h1 h2 => Or.inl (bufs_cover [8, 8, 8, 8, 104] c i h1 (by simpa using h2))
  -- the own words and the callee
  set Wo : Words := csWords layout c with hWo
  have hWoA : WordsInA Wo (fp + 2) (fp + fs "certify_stack") c (c + 136) := by
    refine ⟨fun q hq => Or.inr ?_, ?_⟩
    · simp only [hWo, csWords, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl <;> simp [hord8, csOutsW_length]
    · simp only [hWo, csWords, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, List.Pairwise.nil, and_true, List.length_map, List.length_range, hord8, csOutsW_length,
        false_implies, implies_true]
      omega
  set fl := allocBase (al "log2_ceil_in_the_exponent__L16_L34") (c + 136) with hfl
  have hlog := log2_placed (fs := fs) (al := al) (cert := cert) (k := k) (by omega) hTlt (by rw [hTL]; omega)
    (q := ptrAtV qt) (R := R) (fun t ht => ⟨qt + t, ptrAtV_addr qt t, hRt t ht⟩) fl (fl + fs "log2_ceil_in_the_exponent__L16_L34") le_rfl
  rw [hTL] at hlog
  have hca : csCall.args.map σ0 = [gen ^ T, ptrAtV qt] := by
    simp only [csCall, List.map_cons, List.map_nil, hσ0]
    simp [hp1]
  have hcr : csCall.rets.map σ0 = [gen ^ L] := by
    simp only [csCall, List.map_cons, List.map_nil, hσ0]
    simp [h302]
  have hub : (∀ f, fs f < 2 ^ 16) → lcEnd fs al L (fl + fs "log2_ceil_in_the_exponent__L16_L34") ≤ c + 2 ^ 19 := by
    intro hfs
    have := allocBase_le (al "log2_ceil_in_the_exponent__L16_L34") (c + 136)
    have := hfs "log2_ceil_in_the_exponent__L16_L34"
    have := hfs "assert_small_g_power"
    have := allocBase_le (al "assert_small_g_power") (fl + fs "log2_ceil_in_the_exponent__L16_L34")
    have := allocBase_le (al "assert_small_g_power")
      (allocBase (al "assert_small_g_power") (fl + fs "log2_ceil_in_the_exponent__L16_L34") + fs "assert_small_g_power")
    unfold lcEnd
    split <;> omega
  refine ⟨lcEnd fs al L (fl + fs "log2_ceil_in_the_exponent__L16_L34"), hub, callAtA_nodeRd hlp hfc ⟨σ0, fn% «certify_stack», es, [.n 374, .n 375, .n 377], Wo,
    [PostQuiet], fun rd => HoldsWords rd Wo, fun _ => False, find_certify_stack, ?_, fun i hi => ?_, ?_,
    fun rd h => ?_, fun rd hl hP hO => ?_⟩⟩
  · rw [hal]; exact hWoA
  · rw [hal]; exact Or.inl (hown i (by omega) (by omega))
  · rw [hcl, hal]
    simp only [KidsAtF, csCall, ↓reduceIte, List.headD_cons, List.sum_cons, List.sum_nil, Nat.add_zero]
    have h0 := hca
    have h1 := hcr
    simp only [csCall] at h0 h1
    rw [h0, h1]
    refine ⟨fs "log2_ceil_in_the_exponent__L16_L34", lcEnd fs al L (fl + fs "log2_ceil_in_the_exponent__L16_L34"), R, fun _ => False, fun _ => True,
      fun i hi => Or.inl (Or.inl hi), hlog.mono (R' := R) (D' := fun _ => False) (Out' := fun _ => True)
        (Pre' := fun rd => (ExpTables rd (ptrAtV qt) ∧
          ReadsAt rd (ptrAtV qk) (kappaSources layout.logMemory layout.tableLogHeights)) ∧ HoldsWords rd Wo)
        (Post' := PostQuiet) (fun _ h => h) (fun _ h => h) (fun _ h => h) (fun rd h => h.1.1)
        (fun _ _ _ h => h), rfl, fun rd h => h.1, fun _ h => h.elim⟩
  · have := csOuts_placed hbl hL (out := ptrAtV (c + 32)) (h _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))
    rwa [ptrAtV_mul] at this
  -- on a memory
  simp only [hal]
  obtain ⟨hrun, h301, hld⟩ := cs_run hk hl hbl hL (hG rd) hF (hp0 rd) (hp1 rd) (h10 rd) (h11 rd) (h163 rd)
    (h164 rd) (h303 rd) hP.1 hP.2 hO
  have hev : ∀ ev ∈ es, ev.Holds rd (σ rd) := by
    intro ev hev'
    rw [← hes' (σ rd)] at hev'
    rcases mem_slEvs_aoc haoc hev' with ⟨a, rfl, ha⟩ | ⟨f, a1, r1, rfl, -⟩
    · exact hrun a ha
    · trivial
  have hgood : ∀ i, CsLoadIn c qt qk i → ownData cert fp c "certify_stack" [8, 8, 8, 8, 104] es i ∨ R i ∨ False := by
    intro i hi
    rcases hi with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl (hown i h1 h2)
    · have := hRt (i - qt) (by omega); rw [Nat.add_sub_cancel' h1] at this; exact Or.inr (Or.inl this)
    · have := hRk (i - qk) (by omega); rw [Nat.add_sub_cancel' h1] at this; exact Or.inr (Or.inl this)
  have hpar : (fn% «certify_stack»).params.map (σ rd) = [ptrAtV qk, ptrAtV qt] := by
    rw [certify_stack_params]; exact fwd_params hchk
  have hfin : ∀ st ∈ [Stmt.atom (.copy (.n 374) (.n 302)), .atom (.copy (.n 375) (.n 303)), osCst 376 (csW 52),
      osMul 377 303 376], st ∈ csBodyA := fun st hst => by
    rw [csBodyA_eq]
    exact List.mem_append_right _ hst
  have g374 := hG rd (.copy (.n 374) (.n 302)) (hfin _ (by simp))
  have g375 := hG rd (.copy (.n 375) (.n 303)) (hfin _ (by simp))
  have g376 := hG rd (.const (.n 376) (csW 52)) (hfin _ (by simp [osCst]))
  have g377 := hG rd (.mul (.n 377) (.n 303) (.n 376)) (hfin _ (by simp [osMul]))
  have hret : [V.n 374, .n 375, .n 377].map (σ rd) = [gen ^ L, ptrAtV (c + 32), ptrAtV (c + 32 + 52)] := by
    have e374 : σ rd (.n 374) = σ rd (.n 302) := g374
    have e375 : σ rd (.n 375) = σ rd (.n 303) := g375
    have e376 : σ rd (.n 376) = csW 52 := g376
    have e377 := good_mul g377 (by omega) (by omega)
    simp only [List.map_cons, List.map_nil, e374, e375, e377, e376, h302, h303, csW_eq (show 52 < 64 by omega),
      ptrAtV_mul]
  refine ⟨σ rd, hpar, hwalk _, hret, trivial, ⟨by rw [hdst]; simp [bases, h10, h11, h163, h164, h303],
    by rw [haddr]; simp⟩, fun c' hc' => ?_, fun A hA => ?_, fun A hA => ?_, hev, fun ts hv hp => ?_⟩
  · rw [hcl, List.mem_singleton] at hc'
    subst hc'
    refine ⟨?_, ?_⟩
    · rw [hca]; simp only [csCall, List.map_cons, List.map_nil, h301, hp1, hT]
    · rw [hcr]; simp only [csCall, List.map_cons, List.map_nil, h302]
  · rw [loadAddrs, List.mem_filterMap] at hA
    obtain ⟨ev, hev', hA⟩ := hA
    rw [← hes' (σ rd)] at hev'
    rcases mem_slEvs_aoc haoc hev' with ⟨a, rfl, ha⟩ | ⟨f, a1, r1, rfl, -⟩
    · cases a with
      | load d p off =>
        simp only [Memory.Ev.loadAddr?, Option.some.injEq] at hA
        subst hA
        obtain ⟨i, hi, hin⟩ := hld d p off ha
        exact ⟨i, hi, hgood i hin⟩
      | _ => simp [Memory.Ev.loadAddr?] at hA
    · simp [Memory.Ev.loadAddr?] at hA
  · rw [heapHintAddrs, List.mem_flatMap] at hA
    obtain ⟨ev, hev', hA⟩ := hA
    rw [← hes' (σ rd)] at hev'
    rcases mem_slEvs_aoc haoc hev' with ⟨a, rfl, ha⟩ | ⟨f, a1, r1, rfl, -⟩
    · have hb := List.all_eq_true.mp cs_heapB a (mem_atomsOf' ha)
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hb
      rcases hb with rfl | hb
      · simp only [Memory.Ev.hintAddrs, hintDest?, destHeap?, Option.bind_some, List.mem_map,
          List.mem_range] at hA
        obtain ⟨j, hj, rfl⟩ := hA
        refine ⟨c + 16 + j, by rw [h163, ptrAtV_addr, Nat.zero_add], Or.inl (hown _ (by omega) (by omega))⟩
      · rw [hintAddrs_none hb] at hA; exact absurd hA List.not_mem_nil
    · simp [Memory.Ev.hintAddrs] at hA
  · rw [hcl] at hv hp
    obtain ⟨hkq, hke⟩ := kids_quiet [csCall] ts hv hp
    have hx : ∀ e ∈ es, e.Exact rd (σ rd) := by
      intro ev hev'
      rw [← hes' (σ rd)] at hev'
      rcases mem_slEvs_aoc haoc hev' with ⟨a, rfl, ha⟩ | ⟨f, a1, r1, rfl, -⟩
      · exact exact_of_trivExact (List.all_eq_true.mp htx a (mem_atomsOf' ha))
      · trivial
    refine ⟨?_, ?_⟩
    · rw [pops_node find_certify_stack (hwalk _), hes, csBodyA_wit, List.flatMap_append, List.flatMap_cons,
        splice_quiet_pre csPre hqpre, slEvs, List.singleton_append, splice,
        splice_quietKids _ _ (fun a ha => List.all_eq_true.mp hqpost a (mem_atomsOf' (atoms_slEvs ha))) hkq,
        List.append_nil, stackHints_eq]
      have wO : ReadsAt rd (ptrAtV (c + 16)) ((csOrd (stackKappas layout)).map Prover.count) :=
        hO _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
      show [("stk_group_order", Dest.words rd (σ rd) (.heap (.n 163) 0 8))] = _
      refine congrArg (fun l => [("stk_group_order", l)]) ?_
      refine List.ext_getElem (by simp [Dest.words, hord8]) fun j h1 h2 => ?_
      have := (wO j h2).2
      simp only [Dest.words, List.getElem_map, List.getElem_range, h163, Nat.zero_add] at this ⊢
      rw [this]; rfl
    · rw [Tree.every_node]
      exact ⟨exactAt_of_walk find_certify_stack (hwalk _) hx, hke⟩

/-- **`certify_stack` completes placed** (`CertifyStackCompleteA`), every `k ≥ 11`, its end within
`2^20` of its cursor when every frame is below `2^16`. -/
theorem cs_completeAE {k : ℕ} (hk : 11 ≤ k) :
    CertifyStackCompleteAE fs al cert k (fun c e => FsSmall fs → e ≤ c + 2 ^ 20) := by
  intro bytecode lm rows layout qt qk fp hbl hL _ _
  have h178 : 178 ≤ winTabAt + 2 ^ winTabBits := by decide
  have h8 : 8 ≤ 2 + nTables := by decide
  obtain ⟨e, hb, h⟩ := cs_placed (fs := fs) (al := al) (cert := cert) hk hbl hL
    (R := fun i => (qt ≤ i ∧ i < qt + (winTabAt + 2 ^ winTabBits)) ∨ (qk ≤ i ∧ i < qk + (2 + nTables)))
    (fun t ht => Or.inl ⟨Nat.le_add_right qt t, Nat.add_lt_add_left (lt_of_lt_of_le ht h178) qt⟩)
    (fun t ht => Or.inr ⟨Nat.le_add_right qk t, Nat.add_lt_add_left (lt_of_lt_of_le ht h8) qk⟩) fp (fp + fs "certify_stack") le_rfl
  exact ⟨e, fun hfs => by have := hb hfs; omega, h⟩

/-- **`certify_stack` completes placed** (`CertifyStackCompleteA`), every `k ≥ 11`. -/
theorem cs_completeA {k : ℕ} (hk : 11 ≤ k) : CertifyStackCompleteA fs al cert k :=
  (cs_completeAE hk).toA

/-- **`certify_stack` completes placed, its end within `2^20` of its cursor**, every frame below
`2^16`. -/
theorem cs_completeAB {k : ℕ} (hk : 11 ≤ k) (hfs : FsSmall fs) : CertifyStackCompleteAB fs al cert k 20 :=
  (cs_completeAE hk).mono fun _ _ h _ => h hfs

end
end LeanVM.Guest.B1.VsC
