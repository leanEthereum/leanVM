/-
  LeanVM.Guest.B1.VerifySub.CMatch

  `verify_sub`'s frames on an honest child match its callees: names, arguments and returns.
-/

module

public import LeanVM.Guest.B1.VerifySub.Complete
public import LeanVM.Guest.B1.VerifySub.H.Sig

/-!
# The frames

`vs_calls`: the sixteen frames `verify_sub`'s body sets up (by the kernel, the dispatches' names
read off their selectors). `vs_callsMatch`: on an honest child they match `S.kids`: the names,
the arguments (the honest valuation's values, `C/Vals`, against the child's honest values) and the
returns (the oracle's).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.Memory

@[expose] public section

/-! ## The frames, by the kernel -/

/-- A frame's shape: a call's name, or a dispatch's selector and names. -/
def vsCallSk : Stmt → Option (Option V × (String ⊕ (V × List String)) × List V × List V)
  | .call f a r => some (none, .inl f, a, r)
  | .callIf c f a => some (some c, .inl f, a, [])
  | .dispatch x fs a r => some (none, .inr (x, fs), a, r)
  | _ => none

/-- A frame's shape, its dispatch resolved on `σ`. -/
noncomputable def vsResolve (σ : Val) :
    Option V × (String ⊕ (V × List String)) × List V × List V → Option V × String × List V × List V
  | (c, .inl f, a, r) => (c, f, a, r)
  | (c, .inr (x, fs), a, r) => (c, fs.getD (logG (σ x)) "", a, r)

theorem callSF_sk (σ : Val) (s : Stmt) : Stmt.callSF σ s = (vsCallSk s).map (vsResolve σ) := by
  cases s <;> rfl

/-- Numbered values. -/
def vsNs (l : List ℕ) : List V := l.map V.n

/-- **The sixteen frames' shapes.** -/
def vsCallSkL : List (Option V × (String ⊕ (V × List String)) × List V × List V) :=
  [(none, .inl "g_power_of_word", vsNs [61], vsNs [64]),
    (none, .inl "g_power_of_word", vsNs [27], vsNs [72]),
    (none, .inl "log2_ceil_in_the_exponent__L0_L34", vsNs [252, 4], vsNs [253]),
    (none, .inl "certify_placement", vsNs [83, 4], vsNs [274, 275]),
    (none, .inl "log2_ceil_in_the_exponent__L15_L34", vsNs [274, 4], vsNs [276]),
    (none, .inl "grind_check__L15", vsNs [289, 302], []),
    (none, .inr (.n 278, vsSqpNames), vsNs [296, 297, 298, 299, 300, 303, 304],
      vsNs [305, 306, 307, 308, 309]),
    (none, .inl "opening_message__L1_L1", vsNs [305, 306, 307, 308, 309, 312, 310],
      vsNs [313, 314, 315, 316, 317, 318, 319, 320]),
    (none, .inr (.n 322, vsBgNames), vsNs [314, 328], vsNs [329]),
    (none, .inl "verify_bus_gkr", vsNs [554, 555, 556, 557, 558, 320, 253, 254, 561],
      vsNs [562, 563, 564, 565, 566, 567, 568]),
    (none, .inl "verify_tables", vsNs [562, 563, 564, 565, 566, 567, 0, 1, 254, 253, 71, 26, 4,
      335, 559, 6, 569, 568, 572, 570], vsNs [573, 574, 575, 576, 577, 578, 579, 580, 581, 582]),
    (none, .inl "verify_keccak", vsNs [573, 574, 575, 576, 577, 578, 583, 569, 587, 584, 585, 589],
      vsNs [590, 591, 592, 593, 594, 595, 596]),
    (none, .inl "grind_check__L13", vsNs [606, 619], []),
    (none, .inl "ring_switch_target", vsNs [585, 847], vsNs [1361]),
    (none, .inr (.n 1922, vsOpenNames), vsNs [1370, 1371, 1372, 1373, 1374, 1917, 268, 271, 1928,
      1930], vsNs [1931, 1932, 1933, 1934, 1935]),
    (none, .inl "check_opening_terminal", vsNs [4, 254, 569, 581, 253, 579, 72, 583, 83, 1375, 275,
      584, 848, 1932, 1933, 1934, 1935, 1931, 304, 276], [])]

theorem vs_callsSk : vsCPre.filterMap vsCallSk = vsCallSkL := by decide +kernel

theorem vs_filterMap_map {α β γ : Type} (g : α → Option β) (f : β → γ) :
    ∀ l : List α, l.filterMap (fun x ↦ (g x).map f) = (l.filterMap g).map f
  | [] => rfl
  | a :: l => by
    cases h : g a <;> simp [h, vs_filterMap_map g f l]

/-- **The frames** of `verify_sub`'s body on `σ`. -/
theorem vs_calls (σ : Val) : (vsCPre.filterMap (Stmt.callSF σ)).map (Main.mkCall σ) =
    (vsCallSkL.map (vsResolve σ)).map (Main.mkCall σ) := by
  rw [show Stmt.callSF σ = fun s ↦ (vsCallSk s).map (vsResolve σ) from funext (callSF_sk σ),
    vs_filterMap_map, vs_callsSk]

/-! ## The returns -/

theorem vsRetVars_w : ∀ j < 16, ∀ k < (vsRetVars.getD j []).length,
    (vsRetVars.getD j []).getD k 0 ∈ vsWVars := by decide

/-- **A frame's returns are the oracle's**: the callee's results. -/
theorem vs_rets {rd : Reader} {args : List E} (hl : args.length = 6) (bs : List ℕ)
    (outs : List (List E × Main.Layout)) {j : ℕ} (hj : j < 16)
    (hlen : (outs.getD j ([], [])).1.length = (vsRetVars.getD j []).length) :
    (vsNs (vsRetVars.getD j [])).map (vsσ rd (vsW bs outs) args) = (outs.getD j ([], [])).1 := by
  apply List.ext_getElem (by rw [vsNs, List.length_map, List.length_map, hlen])
  intro k h1 h2
  have hk : k < (vsRetVars.getD j []).length := by
    rw [vsNs, List.length_map, List.length_map] at h1; exact h1
  simp only [vsNs, List.getElem_map]
  rw [← List.getD_eq_getElem _ 0 hk,
    vs_w hl (vsRetVars_w j hj k hk), vsW_ret bs outs hj hk, List.getD_eq_getElem _ _ (by omega)]

/-! ## The honest valuation's values -/

/-- **What the honest valuation gives the frames' arguments** on an honest child. -/
structure VsHonVals {bytecode : List K} {seed : Digest} {c : Child} (S : ChildSegs bytecode seed c)
    (bs : List ℕ) (sqE outE : ℕ) (outs : List (List E × Main.Layout)) (σ : Val) : Prop where
  e61 : σ (.n 61) = eOfNat S.rate
  e27 : σ (.n 27) = eOfNat S.logMem
  e268 : σ (.n 268) = S.x0
  e271 : σ (.n 271) = S.x1
  oodCell : σ (.n 289) = cellsOfState S.oodSt false 1
  oodCap : [σ (.n 296), σ (.n 297), σ (.n 298), σ (.n 299), σ (.n 300)] = capOf S.oodSt
  oodCh : σ (.n 303) = challengeOf S.oodSt
  e312 : σ (.n 312) = ptr (vb bs 1) * gen ^ 11
  s3cap : [σ (.n 554), σ (.n 555), σ (.n 556), σ (.n 557), σ (.n 558)] = S.s3.cap
  beta : σ (.n 559) = S.wb.2
  e583 : σ (.n 583) = gen ^ S.τ
  e587 : σ (.n 587) = ptr (S.cL bs)
  ringCell : σ (.n 606) = cellsOfState S.ringSt false 1
  s7cap : [σ (.n 1370), σ (.n 1371), σ (.n 1372), σ (.n 1373), σ (.n 1374)] = capOf S.s7.perm
  lam : σ (.n 1375) = S.lam
  target : σ (.n 1917) = S.target
  e1928 : σ (.n 1928) = ptr (S.cW bs)
  e278 : σ (.n 278) = gen ^ (S.μs - 22)
  e322 : σ (.n 322) = gen ^ (S.d - 16)
  e1922 : σ (.n 1922) = gen ^ Whir.candidate S.μs S.rate
  e252 : σ (.n 252) = gen ^ S.pushT
  tabs : ∀ d ∈ [302, 328, 561, 572, 589, 619, 1930], σ (.n d) = ptr sqE * gen ^ winTabAt

namespace ChildSegs

variable {bytecode : List K} {seed : Digest} {c : Child} (S : ChildSegs bytecode seed c)

/-- The stream buffer's first words: the sizes, the root's two, the out-of-domain nonce. -/
theorem stream_words (hbl : bytecode.length = 2 ^ 23) :
    (vsStreamW c.proof.stream).take 8 = sizeWords S.logMem S.rowsN S.rate ∧
      (vsStreamW c.proof.stream).getD 0 0 = eOfNat S.logMem ∧
      (vsStreamW c.proof.stream).getD 7 0 = eOfNat S.rate ∧
      (vsStreamW c.proof.stream).getD 8 0 = S.x0 ∧ (vsStreamW c.proof.stream).getD 9 0 = S.x1 ∧
      (vsStreamW c.proof.stream).getD 10 0 = S.oodN := by
  obtain ⟨a, b, c', d, e, f, hr⟩ : ∃ a b c d e f, S.rowsN = [a, b, c, d, e, f] := by
    have := S.hrowsL
    match h : S.rowsN, this with
    | [a, b, c, d, e, f], _ => exact ⟨a, b, c, d, e, f, rfl⟩
  rw [S.stream_eq hbl]
  simp [sizeWords, hr]

end ChildSegs

theorem vs_sq_getD {k : ℕ} (hk : k < 34) : expTabAllWords.getD k 0 = gen ^ 2 ^ k := by
  have h := congrArg (fun l ↦ l.getD k 0) expTableWords_sq
  simp only [List.drop_zero] at h
  rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hk, ← List.getD_eq_getElem?_getD] at h
  rw [h, Tables.gSquaresList, List.getD_eq_getElem _ _ (by simpa using hk)]
  simp

/-! ## The push blocks' total -/

section
variable {rd : Reader} {w : ℕ → E} {args : List E}

local notation "ς" => vsσ rd w args

theorem vsPushStep_memT {b : ℕ} (hb : b < 54) {s : Stmt} (hs : s ∈ vsPushStep b) : s ∈ vsPushT := by
  rw [vsPushT]
  exact List.mem_append_left _ (List.mem_flatMap.2 ⟨b, List.mem_range.2 hb, hs⟩)

/-- **A push block's square**: `g^(2^κ_b)` read from `g_squares`. -/
theorem vs_pushVal (hl : args.length = 6) {sqE logMem : ℕ} {hs : List ℕ}
    (hh : ∀ x ∈ hs, x < 29) (hm : logMem ≤ 32)
    (hkb : ∀ s < 8, ς (.n (84 + s)) = gen ^ (([0, logMem] ++ hs).getD s 0))
    (hp4 : ς (.n 4) = ptr sqE) (hsq : ReadsAt rd (ptr sqE) expTabAllWords) {b : ℕ} (hb : b < 54) :
    ς (.n (vsPushD b)) = gen ^ 2 ^ pushKappa logMem hs b := by
  have hsrc : Tables.blockKappaSrc.getD b 0 < 8 := blockKappaSrc_lt b (by show b < 153; omega)
  have hk := pushKappa_lt hh hm hb
  have hg := vsPushT_good (rd := rd) (w := w) hl _ (vsPushStep_memT hb (vsPushStep_ld b))
  rw [vsg_rdAt hg (vsSPpush_notS b hb), vs_pushP hl hb, hp4, hkb _ hsrc]
  have hr := hsq (pushKappa logMem hs b) (by rw [length_expTabAllWords]; omega)
  rw [← List.getD_eq_getElem _ 0, vs_sq_getD hk, pushKappa, ← loadHolds_mul_gen_pow] at hr
  rw [vs_rdAt_of_load hr, pushKappa]

/-- **The push blocks' total** `g^(Σ_b 2^κ_b)`, block by block. -/
theorem vs_pushProd (hl : args.length = 6) {sqE logMem : ℕ} {hs : List ℕ}
    (hh : ∀ x ∈ hs, x < 29) (hm : logMem ≤ 32)
    (hkb : ∀ s < 8, ς (.n (84 + s)) = gen ^ (([0, logMem] ++ hs).getD s 0))
    (hp4 : ς (.n 4) = ptr sqE) (hsq : ReadsAt rd (ptr sqE) expTabAllWords) :
    ∀ n < 54, ς (.n (vsPV n)) =
      gen ^ ((List.range (n + 1)).map fun b ↦ 2 ^ pushKappa logMem hs b).sum := by
  intro n
  induction n with
  | zero =>
    intro _
    rw [show vsPV 0 = vsPushD 0 from rfl, vs_pushVal hl hh hm hkb hp4 hsq (by norm_num)]
    simp
  | succ n ih =>
    intro hn
    have hm3 : vsMul (vsPV (n + 1)) (vsPV n) (92 + 3 * (n + 1)) ∈ vsPushStep (n + 1) := by
      simp [vsPushStep]
    have e := vsg_mul (by unfold vsPV; omega) (by unfold vsPV; omega)
      (vsPushT_good (rd := rd) (w := w) hl _ (vsPushStep_memT hn hm3))
    rw [e, ih (by omega), show 92 + 3 * (n + 1) = vsPushD (n + 1) by simp [vsPushD],
      vs_pushVal hl hh hm hkb hp4 hsq hn, ← pow_add, List.range_succ (n := n + 1), List.map_append,
      List.sum_append]
    simp

end

/-! ## The honest valuation's values on an honest child -/

/-- **The honest valuation's values.** -/
theorem vs_honVals {bytecode : List K} (hbl : bytecode.length = 2 ^ 23) {seed : Digest}
    {c : Child} (S : ChildSegs bytecode seed c) (b sqE outE : ℕ) {Lin : Main.Layout}
    (hexp : ∀ q ∈ vsExpLin sqE, q ∈ Lin)
    {outs : List (List E × Main.Layout)} (O : VsOuts S (bases b (vsSizes S.d)) sqE outs)
    {rd : Reader} (hB : Main.MemL rd (bufL b (vsSizes S.d) S.ownW)) (hL : Main.MemL rd Lin) :
    VsHonVals S (bases b (vsSizes S.d)) sqE outE outs
      (vsσ rd (vsW (bases b (vsSizes S.d)) outs) (vsArgs seed c sqE outE)) := by
  set bs := bases b (vsSizes S.d) with hbs
  set w := vsW bs outs with hw
  set args := vsArgs seed c sqE outE with hargs
  have hl : args.length = 6 := rfl
  have own : ∀ i < 15, ReadsAt rd (ptr (bs.getD i 0)) (S.ownW.getD i []) :=
    fun i hi ↦ hB _ (vs_own_mem S b hi)
  have wa : ∀ {i a : ℕ}, i < 15 → vsAllocVars.getD i 0 = a → w a = ptr (bs.getD i 0) :=
    fun hi ha ↦ vsW_a hi ha
  have wr : ∀ {j k a : ℕ}, j < 16 → k < (vsRetVars.getD j []).length →
      (vsRetVars.getD j []).getD k 0 = a → w a = (outs.getD j ([], [])).1.getD k 0 :=
    fun hj hk ha ↦ vsW_r hj hk ha
  have hd := S.d_bounds hbl
  have hhs := (S.hs_bounds hbl).1
  -- the stream
  set ws := vsStreamW c.proof.stream with hwsd
  have hS : ReadsAt rd (w 25) ws := by
    rw [wa (i := 1) (a := 25) (by norm_num) rfl]; exact own 1 (by norm_num)
  have hSl := vs_streamW_length c.proof.stream
  have hSl' : 8192 ≤ ws.length := hSl
  have hws : ∀ k < 11, LoadHolds rd (w 25) k (ws.getD k 0) := fun k hk ↦ vs_rdg hS (by omega)
  obtain ⟨st8, st0, st7, st8', st9, st10⟩ := S.stream_words hbl
  have W := fun k (hk : k < 10) ↦ vs_word (rd := rd) (w := w) hl hk (hws k (by omega))
  -- the root's sponge
  have hseed := vs_seedCap (rd := rd) (w := w) hl (seed := seed)
    (pi := statementDigest seed c.statement) rfl rfl rfl rfl
  have hroot := vs_rootFs (rd := rd) (w := w) hl (ws := ws) (by omega) (fun k hk ↦ hws k (by omega))
  rw [hseed, st8, st8', st9, show (⟨capOf (keccakF1600 (seedInput seed (statementDigest seed
    c.statement))), []⟩ : Fs) = seedFs seed (statementDigest seed c.statement) from rfl,
    ← S.sR_eq] at hroot
  -- the out-of-domain sample
  obtain ⟨-, o289, o296, o303, o302, o312⟩ := vs_ood (rd := rd) (w := w) hl hws
  have hOod : vsOodSt rd w args (ws.getD 10 0) = S.oodSt := by
    rw [vsOodSt, ← hroot, st10]; rfl
  rw [hOod] at o289 o296 o303
  -- the depths
  have h64 : w 64 = gen ^ S.rate := by
    rw [wr (j := 0) (k := 0) (a := 64) (by norm_num) (by decide) rfl, O.o0]; rfl
  have h276 : w 276 = gen ^ S.μs := by
    rw [wr (j := 4) (k := 0) (a := 276) (by norm_num) (by decide) rfl, O.o4, S.μs_eq hbl]; rfl
  have h253 := vs_w253 hbl S O
  -- the slot weights and `β`
  have o7 := O.o7
  have eF : vsFpwFs w = ⟨capOf S.busSt, []⟩ := by
    simp only [vsFpwFs]
    rw [wr (j := 7) (k := 2) (a := 315) (by norm_num) (by decide) rfl,
      wr (j := 7) (k := 3) (a := 316) (by norm_num) (by decide) rfl,
      wr (j := 7) (k := 4) (a := 317) (by norm_num) (by decide) rfl,
      wr (j := 7) (k := 5) (a := 318) (by norm_num) (by decide) rfl,
      wr (j := 7) (k := 6) (a := 319) (by norm_num) (by decide) rfl, o7]
    rfl
  obtain ⟨-, hβ⟩ := vs_fpw (rd := rd) (w := w) (args := args) hl
  rw [eF] at hβ
  obtain ⟨-, -, hwb, hs3⟩ := S.bus_inv hbl
  -- the tables' evaluations and the stream's cursors
  have hxl := (S.H_run hbl).2.2.2
  obtain ⟨c561, c572, c589, h583, h587⟩ := vs_callsV (rd := rd) (w := w) (args := args) hl
  have h582 : w 582 = ptr (S.cT bs + (13 + (3 * S.nT + 1))) := by
    rw [wr (j := 10) (k := 9) (a := 582) (by norm_num) (by decide) rfl, O.o10, vs_ptr_add]
    simp only [Tables.VtHonest.retsH, Fs.squeeze, capOf, List.cons_append, List.nil_append,
      List.getD_cons_succ, List.getD_cons_zero]
    rw [show ofK (addressOfIndex (S.vtB bs sqE (S.leavesB (outs.take 10))).cur) = ptr (S.cT bs)
      from rfl, mul_assoc, mul_assoc, ← pow_succ', ← pow_add]
    rfl
  have o11 := O.o11
  have h595 : w 595 = ptr (S.cK bs + S.xsK.length) := by
    rw [wr (j := 11) (k := 5) (a := 595) (by norm_num) (by decide) rfl, o11, vs_ptr_add]
    simp only [capOf, List.cons_append, List.nil_append, List.getD_cons_succ, List.getD_cons_zero]
  -- the ring map
  have hnonce : LoadHolds rd (w 595) 0 S.ringN := by
    rw [h595]
    have h := S.sub_stream b (P := sizeWords S.logMem S.rowsN S.rate ++ [S.x0, S.x1] ++
      [S.oodN, S.oodV] ++ [S.busN] ++ S.xsG ++ S.xsT ++ S.xsK) (X := [S.ringN])
      (R := S.xsW ++ streamPad c.proof.stream) (by rw [S.stream_eq hbl, streamPad]; simp)
    have hr := subOf_memL hB h 0 (by simp)
    simp only [List.length_append, S.sizeWords_length, List.length_cons, List.length_nil] at hr
    rwa [show vb bs 1 + (8 + 2 + 2 + 1 + S.xsG.length + S.xsT.length + S.xsK.length) =
      S.cK bs + S.xsK.length by simp only [ChildSegs.cK, ChildSegs.cT, ChildSegs.cG]; omega] at hr
  have hK : vsKCap w = capOf S.s6.perm := by
    simp only [vsKCap]
    rw [wr (j := 11) (k := 0) (a := 590) (by norm_num) (by decide) rfl,
      wr (j := 11) (k := 1) (a := 591) (by norm_num) (by decide) rfl,
      wr (j := 11) (k := 2) (a := 592) (by norm_num) (by decide) rfl,
      wr (j := 11) (k := 3) (a := 593) (by norm_num) (by decide) rfl,
      wr (j := 11) (k := 4) (a := 594) (by norm_num) (by decide) rfl, o11]
    rfl
  obtain ⟨-, m606, m619, -, mEnd⟩ := vs_maps (rd := rd) (w := w) (args := args) hl hnonce
  have hMap : vsMapSt (vsKCap w) S.ringN = S.ringSt := by rw [hK, S.ringSt_eq hbl]; rfl
  rw [hMap] at m606 mEnd
  have hs7 : S.s7 = ⟨[vsσ rd w args (.n 840), vsσ rd w args (.n 841), vsσ rd w args (.n 842),
      vsσ rd w args (.n 843), vsσ rd w args (.n 844)], []⟩ := by
    rw [S.ring_inv.2.2.2.1, mEnd]
  -- λ and the target
  have hcol : S.claims.map (·.column) = Tables.claimColumns :=
    Tables.VtHonest.vtH_columns (S.H_run hbl).1 S.hrowsL
  have hcl : S.claims.length = 159 := by
    rw [← List.length_map (f := (·.column)), hcol]; exact claimColumns_length
  have hpoolW : ReadsAt rd (w 6) S.H.poolW := by
    rw [wa (i := 0) (a := 6) (by norm_num) rfl]; exact own 0 (by norm_num)
  have hx4 := (S.H_run hbl).1.hx4
  have hpool : ReadsAt rd (w 6) ((S.claims.take 4).map (·.value)) := by
    rw [S.pool_vals hbl]
    have := hpoolW
    rw [Tables.VtHonest.poolW, List.append_assoc] at this
    exact (Main.readsAt_append'.1 this).1
  have hpi : ReadsAt rd (w 6 * gen ^ 157) ((S.claims.drop 157).map (·.value)) := by
    rw [S.pi_vals hbl]
    have := hpoolW
    rw [Tables.VtHonest.poolW] at this
    have h2 := (Main.readsAt_append'.1 this).2
    rwa [List.length_append, List.length_replicate, hx4] at h2
  have hcew : ReadsAt rd (w 582) (((S.claims.drop 4).take 153).map (·.value)) := by
    rw [S.col_vals hbl, (S.evs_eq hbl).1, h582, show 13 + (3 * S.nT + 1) = 14 + 3 * S.nT by omega]
    have hT : ReadsAt rd (ptr (S.cT bs)) S.xsT := subOf_memL hB (S.sub_xsT b hbl)
    rw [← List.take_append_drop (14 + 3 * S.nT) S.xsT] at hT
    have h2 := (Main.readsAt_append'.1 hT).2
    rwa [List.length_take, Nat.min_eq_left (by omega), ← vs_ptr_add] at h2
  have hv : ReadsAt rd (w 310) [S.oodV] := by
    rw [wa (i := 7) (a := 310) (by norm_num) rfl]; exact own 7 (by norm_num)
  obtain ⟨hlsq, htg⟩ := vs_lam (rd := rd) (w := w) (args := args) hl hcl hcol hpool hcew hpi hv
  rw [← hs7] at hlsq
  -- the tail
  obtain ⟨t1922, -, t1928, t1930⟩ := vs_tailV (rd := rd) (w := w) (args := args) hl S.hr1 S.hmu22 h64 h276
  -- the push blocks' total
  have hp4 : vsσ rd w args (.n 4) = ptr sqE := vsC_param hl (by norm_num)
  have hsq0 := hL (sqE, expTabAllWords) (hexp _ (by unfold vsExpLin; exact List.mem_singleton_self _))
  have hsq : ReadsAt rd (ptr sqE) expTabAllWords := by dsimp only at hsq0; exact hsq0
  have h72 : w 72 = gen ^ S.logMem := by
    rw [wr (j := 1) (k := 0) (a := 72) (by norm_num) (by decide) rfl, O.o1]; rfl
  obtain ⟨-, -, -, -, -, -, -, -, h84, h85, h86⟩ :=
    vs_sizesV (rd := rd) (w := w) (args := args) hl S.hr1 S.h16 h64 h72
  have hdims : ReadsAt rd (w 71) (vsDimsW S.logMem S.hs) := by
    rw [wa (i := 3) (a := 71) (by norm_num) rfl]; exact own 3 (by norm_num)
  have hkb : ∀ s < 8, vsσ rd w args (.n (84 + s)) = gen ^ ([0, S.logMem] ++ S.hs).getD s 0 := by
    intro s hs
    rw [← S.kb_pow hbl hs]
    rcases s with _ | _ | t
    · exact h84
    · exact h85
    · rw [show 84 + (t + 2) = 86 + t by omega, h86 t (by omega),
        vs_rdAt_of_load (vs_rdg hdims (k := 1 + t) (by simp [vsDimsW, S.hs_length]; omega))]
      simp only [vsDimsW, List.getD_cons_succ, show 1 + t = t + 1 by omega]
  have hτ : S.τ = S.hs.getD 5 0 := S.τ_eq
  have hlam : vsσ rd w args (.n 1375) = S.lam := by
    show _ = S.s7.squeeze.1
    rw [hlsq]
  refine ⟨(W 7 (by omega)).1.trans st7, (W 0 (by omega)).1.trans st0,
    (W 8 (by omega)).1.trans st8', (W 9 (by omega)).1.trans st9, o289, o296, o303,
    by rw [o312, wa (i := 1) (a := 25) (by norm_num) rfl]; rfl, ?_, ?_, ?_, ?_, m606, ?_, ?_, ?_,
    ?_, (vs_placeV (rd := rd) (w := w) (args := args) hl S.hmu22 h276).1,
    (vs_busGrind (rd := rd) (w := w) (args := args) hl (by omega) h253).1, t1922, ?_, ?_⟩
  · rw [hs3, hβ]
  · rw [hwb, hβ]
  · rw [h583, vs_rdAt_of_load (vs_rdg hdims (k := 6) (by simp [vsDimsW, S.hs_length])), hτ]
    simp only [vsDimsW, List.getD_cons_succ]
    rw [S.hs_count hbl, List.getD_eq_getElem _ _ (by simp [S.hs_length]), List.getElem_map,
      List.getD_eq_getElem _ _ (by simp [S.hs_length])]
  · rw [h587, h582, ← vs_ptr_add,
      show S.cL bs = S.cT bs + (13 + (3 * S.nT + 1)) + 101 by
        simp only [ChildSegs.cL, ChildSegs.cE]; omega]
  · exact (congrArg (fun p : E × Fs ↦ p.2.cap) hlsq).symm
  · exact hlam
  · rw [htg, S.target_eq hbl, hlam,
      wr (j := 13) (k := 0) (a := 1361) (by norm_num) (by decide) rfl, O.o13,
      wr (j := 11) (k := 6) (a := 596) (by norm_num) (by decide) rfl, o11, S.ring_inv.2.2.1]
    rfl
  · rw [t1928, h595, ← pow_one gen, ← vs_ptr_add,
      show S.cW bs = S.cK bs + S.xsK.length + 1 by
        simp only [ChildSegs.cW, ChildSegs.cR, S.ring_inv.1, List.length_cons, List.length_nil]]
  · have h := vs_pushProd (rd := rd) (w := w) (args := args) hl hhs S.h32 hkb hp4 hsq 53 (by norm_num)
    exact h
  · have c328 := (vs_busGrind (rd := rd) (w := w) (args := args) hl (by omega) h253).2.2
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [o302, hp4]
    · rw [c328, hp4]
    · rw [c561, hp4]
    · rw [c572, hp4]
    · rw [c589, hp4]
    · rw [m619, hp4]
    · rw [t1930, hp4]


/-! ## The frames match -/

theorem vs_rets' {rd : Reader} {args : List E} (hl : args.length = 6) (bs : List ℕ)
    (outs : List (List E × Main.Layout)) {j : ℕ} (hj : j < 16) {rs : List ℕ}
    (hrs : vsRetVars.getD j [] = rs) (hlen : (outs.getD j ([], [])).1.length = rs.length) :
    (vsNs rs).map (vsσ rd (vsW bs outs) args) = (outs.getD j ([], [])).1 := by
  subst hrs; exact vs_rets hl bs outs hj hlen

theorem vs_squeezeN_capLen : ∀ (n : ℕ) (s : Fs), s.cap.length = 5 → (s.squeezeN n).2.cap.length = 5
  | 0, _, h => h
  | n + 1, s, _ => vs_squeezeN_capLen n s.squeeze.2 (by simp [Fs.squeeze, capOf])

/-- **The frames match the callees** on an honest child. -/
theorem vs_callsMatch {bytecode : List K} (hbl : bytecode.length = 2 ^ 23) {seed : Digest}
    {c : Child} (S : ChildSegs bytecode seed c) {sqE outE : ℕ} {Lin : Main.Layout}
    (hexp : ∀ q ∈ vsExpLin sqE, q ∈ Lin) : VsCallsMatch S sqE outE Lin := by
  intro b outs O rd hB hL
  have V := vs_honVals hbl S b sqE outE hexp O hB hL
  set bs := bases b (vsSizes S.d) with hbs
  set w := vsW bs outs with hw
  set args := vsArgs seed c sqE outE with hargs
  set σ := vsσ rd w args with hσ
  have hl : args.length = 6 := rfl
  have pa : ∀ {i a : ℕ}, i < 15 → vsAllocVars.getD i 0 = a → σ (.n a) = ptr (bs.getD i 0) :=
    fun hi ha ↦ by
      rw [hσ, vs_w hl (by rw [← ha]; exact vs_allocVars_w _ (vsAllocVars_idx _ hi).1)]
      exact vsW_a hi ha
  have pr : ∀ {j k a : ℕ}, j < 16 → k < (vsRetVars.getD j []).length →
      (vsRetVars.getD j []).getD k 0 = a → σ (.n a) = (outs.getD j ([], [])).1.getD k 0 :=
    fun hj hk ha ↦ by
      rw [hσ, vs_w hl (by rw [← ha]; exact vsRetVars_w _ hj _ hk)]; exact vsW_r hj hk ha
  have p4 : σ (.n 4) = ptr sqE := vsC_param hl (by norm_num)
  have hd := S.d_bounds hbl
  rw [vs_calls]
  refine callsMatch_kidsAt _ _ _ _ rfl (by rw [S.kids_length, O.len]) fun j hj ↦ ?_
  have hj16 : j < 16 := by rw [List.length_map, List.length_map] at hj; exact hj
  rw [vs_kidsAt_getD]
  interval_cases j
  · refine ⟨rfl, rfl, fun _ ↦ ⟨?_, vs_rets' hl bs outs (j := 0) (by norm_num) rfl (by rw [O.o0]; simp)⟩⟩
    show [σ (.n 61)] = [eOfNat S.rate]
    rw [V.e61]
  · refine ⟨rfl, rfl, fun _ ↦ ⟨?_, vs_rets' hl bs outs (j := 1) (by norm_num) rfl (by rw [O.o1]; simp)⟩⟩
    show [σ (.n 27)] = [eOfNat S.logMem]
    rw [V.e27]
  · refine ⟨rfl, rfl, fun _ ↦ ⟨?_, vs_rets' hl bs outs (j := 2) (by norm_num) rfl (by rw [O.o2]; simp)⟩⟩
    show [σ (.n 252), σ (.n 4)] = [gen ^ S.pushT, ptr sqE]
    rw [V.e252, p4]
  · -- `certify_placement`
    obtain ⟨e10, e11, e136, e137, e293, hr3, -⟩ := O.o3
    refine ⟨rfl, rfl, fun _ ↦ ⟨?_, vs_rets' hl bs outs (j := 3) (by norm_num) rfl (by rw [hr3]; simp)⟩⟩
    show [σ (.n 83), σ (.n 4)] = [ptr (vb bs 4), ptr sqE]
    rw [pa (i := 4) (a := 83) (by norm_num) rfl, p4]; rfl
  · -- `log2_ceil_in_the_exponent__L15_L34`
    obtain ⟨e10, e11, e136, e137, e293, hr3, -⟩ := O.o3
    refine ⟨rfl, rfl, fun _ ↦ ⟨?_, vs_rets' hl bs outs (j := 4) (by norm_num) rfl (by rw [O.o4]; simp)⟩⟩
    show [σ (.n 274), σ (.n 4)] = [gen ^ Tables.stackTotal S.kappas, ptr sqE]
    rw [pr (j := 3) (k := 0) (a := 274) (by norm_num) (by decide) rfl, hr3, p4]; rfl
  · -- `grind_check__L15`
    refine ⟨rfl, rfl, fun _ ↦ ⟨?_, vs_rets' hl bs outs (j := 5) (rs := []) (by norm_num) rfl (by rw [O.o5]; simp)⟩⟩
    show [σ (.n 289), σ (.n 302)] = [cellsOfState S.oodSt false 1, ptr sqE * gen ^ winTabAt]
    rw [V.oodCell, V.tabs 302 (by simp)]
  · -- `squeeze_point_from`
    have hl6 : S.sZ.cap.length = 5 := vs_squeezeN_capLen _ _ (by simp [capOf])
    refine ⟨?_, rfl, fun _ ↦ ⟨?_, vs_rets' hl bs outs (j := 6) (by norm_num) rfl (by rw [O.o6, hl6]; simp)⟩⟩
    · show vsSqpNames.getD (logG (σ (.n 278))) "" = squeezeNames.getD (S.μs - 22) ""
      rw [V.e278, LeanVM.Guest.Memory.logG_gen_pow (by have := S.hmu28; show S.layout.stackLog - 22 < _; omega)]
      rfl
    · show [σ (.n 296), σ (.n 297), σ (.n 298), σ (.n 299), σ (.n 300), σ (.n 303), σ (.n 304)] =
        capOf S.oodSt ++ [challengeOf S.oodSt, ptr (vb bs 6)]
      rw [← V.oodCap, V.oodCh, pa (i := 6) (a := 304) (by norm_num) rfl]; rfl
  · -- `opening_message__L1_L1`
    have hl6 : S.sZ.cap.length = 5 := vs_squeezeN_capLen _ _ (by simp [capOf])
    refine ⟨rfl, rfl, fun _ ↦ ⟨?_, vs_rets' hl bs outs (j := 7) (by norm_num) rfl (by rw [O.o7]; simp [capOf])⟩⟩
    have h6 := vs_rets' (rd := rd) hl bs outs (j := 6) (rs := [305, 306, 307, 308, 309]) (by norm_num) rfl (by rw [O.o6, hl6]; simp)
    rw [O.o6] at h6
    show (vsNs [305, 306, 307, 308, 309]).map σ ++ [σ (.n 312), σ (.n 310)] =
      S.sZ.cap ++ [ptr (vb bs 1) * gen ^ 11, ptr (vb bs 7)]
    rw [h6, V.e312, pa (i := 7) (a := 310) (by norm_num) rfl]; rfl
  · -- `bus_grind_check`
    refine ⟨?_, rfl, fun _ ↦ ⟨?_, vs_rets' hl bs outs (j := 8) (by norm_num) rfl (by rw [O.o8]; simp)⟩⟩
    · show vsBgNames.getD (logG (σ (.n 322))) "" = busGrindNames.getD (S.d - 16) ""
      rw [V.e322, LeanVM.Guest.Memory.logG_gen_pow (by omega)]
      rfl
    · show [σ (.n 314), σ (.n 328)] = [cellsOfState S.busSt false 1, ptr sqE * gen ^ winTabAt]
      rw [pr (j := 7) (k := 1) (a := 314) (by norm_num) (by decide) rfl, O.o7, V.tabs 328 (by simp)]
      rfl
  · -- `verify_bus_gkr`
    obtain ⟨b9, hr9, -⟩ := O.o9
    obtain ⟨-, -, hc4, -, -, -⟩ := S.gkr_inv hbl
    refine ⟨rfl, rfl, fun _ ↦ ⟨?_, vs_rets' hl bs outs (j := 9) (by norm_num) rfl (by rw [hr9]; simp [hc4])⟩⟩
    show (vsNs [554, 555, 556, 557, 558]).map σ ++ [σ (.n 320), σ (.n 253), σ (.n 254), σ (.n 561)] =
      S.s3.cap ++ [ptr (ChildSegs.cG bs), gen ^ S.d, ptr (vb bs 5), ptr sqE * gen ^ winTabAt]
    rw [show (vsNs [554, 555, 556, 557, 558]).map σ = [σ (.n 554), σ (.n 555), σ (.n 556),
      σ (.n 557), σ (.n 558)] from rfl, V.s3cap,
      pr (j := 7) (k := 7) (a := 320) (by norm_num) (by decide) rfl, O.o7,
      show σ (.n 253) = gen ^ S.d from (vs_w hl (a := 253) (by decide)).trans (vs_w253 hbl S O),
      pa (i := 5) (a := 254) (by norm_num) rfl, V.tabs 561 (by simp)]
    simp only [capOf, List.cons_append, List.nil_append, List.getD_cons_succ, List.getD_cons_zero]
    rw [mul_assoc, ← pow_add, ← vs_ptr_add]
    rfl
  · -- `verify_tables`
    obtain ⟨b9, hr9, hm9⟩ := O.o9
    obtain ⟨-, -, hc4, -, hpl, -⟩ := S.gkr_inv hbl
    refine ⟨rfl, rfl, fun _ ↦ ⟨?_, vs_rets' hl bs outs (j := 10) (by norm_num) rfl
      (by rw [O.o10]; simp [Tables.VtHonest.retsH, Fs.squeeze, capOf])⟩⟩
    have e9 : ∀ k < 5, σ (.n (562 + k)) = S.s4.cap.getD k 0 := fun k hk ↦ by
      rw [pr (j := 9) (k := k) (a := 562 + k) (by norm_num) (by simp [vsRetVars]; omega)
        (by interval_cases k <;> rfl), hr9, List.getD_append _ _ _ _ (by omega)]
    have e567 : σ (.n 567) = ptr (S.cT bs) := by
      rw [pr (j := 9) (k := 5) (a := 567) (by norm_num) (by decide) rfl, hr9,
        List.getD_append_right _ _ _ _ (by omega), hc4]
      show ptr (ChildSegs.cG bs) * gen ^ S.xsG.length = _
      rw [← vs_ptr_add]; rfl
    have h6 : (outs.getD 9 ([], [])).1.getD 6 0 = ptr b9 := by
      rw [hr9, List.getD_append_right _ _ _ _ (by omega), hc4]; rfl
    have e568 : σ (.n 568) = ptr (S.leavesB (outs.take 10)) := by
      rw [pr (j := 9) (k := 6) (a := 568) (by norm_num) (by decide) rfl]
      have hex : ∃ b, (ChildSegs.gkRes (outs.take 10)).1.getD 6 0 = ptr b ∧
          (b, S.rG.2.2) ∈ (ChildSegs.gkRes (outs.take 10)).2 := by
        refine ⟨b9, ?_, ?_⟩
        · rw [ChildSegs.gkRes, take_getD _ _ (by norm_num)]; exact h6
        · rw [ChildSegs.gkRes, take_getD _ _ (by norm_num)]; exact hm9
      unfold ChildSegs.leavesB
      split
      · rename_i h
        rw [← (Classical.choose_spec h).1, ChildSegs.gkRes, take_getD _ _ (by norm_num)]
      · exact absurd hex ‹_›
    have hμ : S.H.μ = S.d := hpl
    show [σ (.n 562), σ (.n 563), σ (.n 564), σ (.n 565), σ (.n 566), σ (.n 567), σ (.n 0),
      σ (.n 1), σ (.n 254), σ (.n 253), σ (.n 71), σ (.n 26), σ (.n 4), σ (.n 335), σ (.n 559),
      σ (.n 6), σ (.n 569), σ (.n 568), σ (.n 572), σ (.n 570)] =
      S.H.args (S.vtB bs sqE (S.leavesB (outs.take 10)))
    rw [e9 0 (by norm_num), e9 1 (by norm_num), e9 2 (by norm_num), e9 3 (by norm_num),
      e9 4 (by norm_num), e567, show σ (.n 0) = args.getD 0 0 from vsC_param hl (by norm_num),
      show σ (.n 1) = args.getD 1 0 from vsC_param hl (by norm_num), pa (i := 5) (a := 254) (by norm_num) rfl,
      show σ (.n 253) = gen ^ S.d from (vs_w hl (a := 253) (by decide)).trans (vs_w253 hbl S O),
      pa (i := 3) (a := 71) (by norm_num) rfl, pa (i := 2) (a := 26) (by norm_num) rfl, p4,
      pa (i := 8) (a := 335) (by norm_num) rfl, V.beta, pa (i := 0) (a := 6) (by norm_num) rfl,
      pa (i := 9) (a := 569) (by norm_num) rfl, e568, V.tabs 572 (by simp),
      pa (i := 10) (a := 570) (by norm_num) rfl, Tables.VtHonest.args, hμ]
    rfl
  · -- `verify_keccak`
    have hxl := (S.H_run hbl).2.2.2
    refine ⟨rfl, rfl, fun _ ↦ ⟨?_, vs_rets' hl bs outs (j := 11) (by norm_num) rfl
      (by rw [O.o11]; simp [capOf])⟩⟩
    have eK : ∀ k < 6, σ (.n (573 + k)) = (S.H.retsH (S.vtB bs sqE (S.leavesB (outs.take 10)))).getD k 0 :=
      fun k hk ↦ by
        rw [pr (j := 10) (k := k) (a := 573 + k) (by norm_num) (by simp [vsRetVars]; omega)
          (by interval_cases k <;> rfl), O.o10]
    show [σ (.n 573), σ (.n 574), σ (.n 575), σ (.n 576), σ (.n 577), σ (.n 578), σ (.n 583),
      σ (.n 569), σ (.n 587), σ (.n 584), σ (.n 585), σ (.n 589)] =
      S.H.s3.squeeze.2.cap ++ [ptr (S.cK bs), gen ^ S.τ, ptr (vb bs 9), ptr (S.cL bs),
        ptr (vb bs 11), ptr (vb bs 12), ptr (sqE + winTabAt)]
    rw [eK 0 (by norm_num), eK 1 (by norm_num), eK 2 (by norm_num), eK 3 (by norm_num),
      eK 4 (by norm_num), eK 5 (by norm_num), V.e583, pa (i := 9) (a := 569) (by norm_num) rfl,
      V.e587, pa (i := 11) (a := 584) (by norm_num) rfl, pa (i := 12) (a := 585) (by norm_num) rfl,
      V.tabs 589 (by simp), ← vs_ptr_add sqE winTabAt]
    simp only [Tables.VtHonest.retsH, Fs.squeeze, capOf, List.cons_append, List.nil_append,
      List.getD_cons_succ, List.getD_cons_zero]
    rw [show ofK (addressOfIndex (S.vtB bs sqE (S.leavesB (outs.take 10))).cur) = ptr (S.cT bs)
      from rfl, show ptr (S.cT bs) * gen ^ 13 * gen * gen ^ (3 * S.H.n) * gen ^ 153 = ptr (S.cK bs) by
        rw [show S.cK bs = S.cT bs + 13 + 1 + 3 * S.H.n + 153 by
          simp only [ChildSegs.cK]; rw [hxl]; show _ = _ + 13 + 1 + 3 * S.nT + 153; omega,
          vs_ptr_add, vs_ptr_add, vs_ptr_add, vs_ptr_add, pow_one]]
    rfl
  · -- `grind_check__L13`
    refine ⟨rfl, rfl, fun _ ↦ ⟨?_, vs_rets' hl bs outs (j := 12) (rs := []) (by norm_num) rfl
      (by rw [O.o12]; simp)⟩⟩
    show [σ (.n 606), σ (.n 619)] = [cellsOfState S.ringSt false 1, ptr sqE * gen ^ winTabAt]
    rw [V.ringCell, V.tabs 619 (by simp)]
  · -- `ring_switch_target`
    refine ⟨rfl, rfl, fun _ ↦ ⟨?_, vs_rets' hl bs outs (j := 13) (by norm_num) rfl
      (by rw [O.o13]; simp)⟩⟩
    show [σ (.n 585), σ (.n 847)] = [ptr (vb bs 12), ptr (vb bs 13)]
    rw [pa (i := 12) (a := 585) (by norm_num) rfl, pa (i := 13) (a := 847) (by norm_num) rfl]; rfl
  · -- `open_stacked`
    obtain ⟨b14, b14', hr14, -⟩ := O.o14
    refine ⟨?_, rfl, fun _ ↦ ⟨?_, vs_rets' hl bs outs (j := 14) (by norm_num) rfl
      (by rw [hr14]; simp)⟩⟩
    · show vsOpenNames.getD (logG (σ (.n 1922))) "" = Whir.openName S.μs S.rate
      have := S.hmu28
      have := S.hr4
      rw [V.e1922, LeanVM.Guest.Memory.logG_gen_pow (by
        unfold Whir.candidate; show S.layout.stackLog - 22 + 7 * (S.rate - 1) < _; omega),
        vsOpenNames_eq]
      rfl
    · show [σ (.n 1370), σ (.n 1371), σ (.n 1372), σ (.n 1373), σ (.n 1374), σ (.n 1917),
        σ (.n 268), σ (.n 271), σ (.n 1928), σ (.n 1930)] =
        capOf S.s7.perm ++ [S.target, (digestHalves S.root).1, (digestHalves S.root).2,
          ptr (S.cW bs), ptr sqE * gen ^ winTabAt]
      rw [← V.s7cap, V.target, V.e268, V.e271, V.e1928, V.tabs 1930 (by simp), ← S.hroot,
        digestScalars_digestOfScalars]
      rfl
  · -- `check_opening_terminal`
    obtain ⟨e10, e11, e136, e137, e293, hr3, hL3⟩ := O.o3
    obtain ⟨b14, b14', hr14, hL14⟩ := O.o14
    refine ⟨rfl, (@decide_eq_true _ (Classical.propDecidable _) O.term).symm, fun _ ↦ ⟨?_,
      vs_rets' hl bs outs (j := 15) (rs := []) (by norm_num) rfl (by rw [O.o15]; simp)⟩⟩
    have r10 : ∀ k < 10, σ (.n (573 + k)) =
        (S.H.retsH (S.vtB bs sqE (S.leavesB (outs.take 10)))).getD k 0 := fun k hk ↦ by
      rw [pr (j := 10) (k := k) (a := 573 + k) (by norm_num) (by simp [vsRetVars]; omega)
        (by interval_cases k <;> rfl), O.o10]
    have r14 : ∀ k < 5, σ (.n (1931 + k)) = [S.w.target, ptr b14, ptr b14', S.w.inner,
        S.w.residual].getD k 0 := fun k hk ↦ by
      rw [pr (j := 14) (k := k) (a := 1931 + k) (by norm_num) (by simp [vsRetVars]; omega)
        (by interval_cases k <;> rfl), hr14]
    show [σ (.n 4), σ (.n 254), σ (.n 569), σ (.n (573 + 8)), σ (.n 253), σ (.n (573 + 6)),
      σ (.n 72), σ (.n 583), σ (.n 83), σ (.n 1375), σ (.n 275), σ (.n 584), σ (.n 848),
      σ (.n (1931 + 1)), σ (.n (1931 + 2)), σ (.n (1931 + 3)), σ (.n (1931 + 4)),
      σ (.n (1931 + 0)), σ (.n 304), σ (.n 276)] =
      termArgs (ChildSegs.termB bs sqE (outs.take 15)) S.H.rm (gen ^ S.d) (gen ^ S.nT) (gen ^ S.logMem)
        (gen ^ S.τ) S.lam S.w.inner S.w.residual S.w.target
        (gen ^ max 15 (log2Ceil (Tables.stackTotal S.kappas)))
    rw [p4, pa (i := 5) (a := 254) (by norm_num) rfl, pa (i := 9) (a := 569) (by norm_num) rfl,
      r10 8 (by norm_num),
      show σ (.n 253) = gen ^ S.d from (vs_w hl (a := 253) (by decide)).trans (vs_w253 hbl S O),
      r10 6 (by norm_num), pr (j := 1) (k := 0) (a := 72) (by norm_num) (by decide) rfl, O.o1,
      V.e583, pa (i := 4) (a := 83) (by norm_num) rfl, V.lam,
      pr (j := 3) (k := 1) (a := 275) (by norm_num) (by decide) rfl, hr3,
      pa (i := 11) (a := 584) (by norm_num) rfl, pa (i := 14) (a := 848) (by norm_num) rfl,
      r14 1 (by norm_num), r14 2 (by norm_num), r14 3 (by norm_num), r14 4 (by norm_num),
      r14 0 (by norm_num), pa (i := 6) (a := 304) (by norm_num) rfl,
      pr (j := 4) (k := 0) (a := 276) (by norm_num) (by decide) rfl, O.o4]
    simp only [termArgs, ChildSegs.termB, ChildSegs.termBs, ChildSegs.cpRes, ChildSegs.osRes,
      take_getD _ _ (show 3 < 15 by norm_num), take_getD _ _ (show 14 < 15 by norm_num), hL3, hL14,
      Tables.cpOwn, Tables.VtHonest.retsH, Fs.squeeze, capOf, List.cons_append, List.nil_append,
      List.getD_cons_succ, List.getD_cons_zero]
    rfl

end
end LeanVM.Guest.B1.VerifySub
