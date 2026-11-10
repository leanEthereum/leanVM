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
    (none, .inl "grind_check__L14", vsNs [606, 619], []),
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
  obtain ⟨-, o289, o296, o303, -, o312⟩ := vs_ood (rd := rd) (w := w) hl hws
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
  obtain ⟨-, -, -, h583, h587⟩ := vs_callsV (rd := rd) (w := w) (args := args) hl
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
  obtain ⟨-, m606, -, -, mEnd⟩ := vs_maps (rd := rd) (w := w) (args := args) hl hnonce
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
  obtain ⟨t1922, -, t1928, -⟩ := vs_tailV (rd := rd) (w := w) (args := args) hl S.hr1 S.hmu22 h64 h276
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
    (vs_busGrind (rd := rd) (w := w) (args := args) hl (by omega) h253).1, t1922, ?_⟩
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


end
end LeanVM.Guest.B1.VerifySub
