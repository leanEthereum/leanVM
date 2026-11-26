/-
  LeanVM.Guest.B1.VerifySub.CMatch

  `verify_sub`'s frames on an honest child match its callees: names, arguments and returns.
-/

module

public import LeanVM.Guest.B1.VerifySub.Complete
public import LeanVM.Guest.B1.VerifySub.H.Sig
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_sub»

/-!
# The frames

`vs_calls`: the fourteen frames `verify_sub`'s body sets up (by the kernel, the dispatches' names
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

/-- **The fourteen frames' shapes.** -/
def vsCallSkL : List (Option V × (String ⊕ (V × List String)) × List V × List V) :=
  [(none, .inl "g_power_of_word", vsNs [61], vsNs [64]),
    (none, .inl "g_power_of_word", vsNs [27], vsNs [72]),
    (none, .inl "log2_ceil_in_the_exponent__L0_L34", vsNs [252, 4], vsNs [253]),
    (none, .inl "certify_placement", vsNs [83, 4], vsNs [274, 275]),
    (none, .inl "log2_ceil_in_the_exponent__L16_L34", vsNs [274, 4], vsNs [276]),
    (none, .inr (.n (val% «verify_sub» "size_sel"), vsSqpNames), vsNs [296, 297, 298, 299, 300, 288, 355],
      vsNs [356, 357, 358, 359, 360]),
    (none, .inl "opening_message__L1_L1", vsNs [356, 357, 358, 359, 360, 363, 361],
      vsNs [364, 365, 366, 367, 368, 369, 370, 371]),
    (none, .inr (.n (val% «verify_sub» "bus_grind"), vsBgNames), vsNs [365, 379], vsNs [380]),
    (none, .inl "verify_bus_gkr", vsNs [590, 591, 592, 593, 594, 371, 253, 254, 596, 25],
      vsNs [597, 598, 599, 600, 601, 602, 603]),
    (none, .inl "verify_tables", vsNs [597, 598, 599, 600, 601, 602, 0, 1, 254, 253, 71, 26, 4,
      386, 582, 6, 604, 603, 607, 605, 25], vsNs [608, 609, 610, 611, 612, 613, 614, 615, 616, 617]),
    (none, .inl "verify_keccak", vsNs [608, 609, 610, 611, 612, 613, 618, 604, 622, 619, 620, 624, 25],
      vsNs [625, 626, 627, 628, 629, 630, 631]),
    (none, .inl "ring_switch_target", vsNs [620, 918], vsNs [1432]),
    (none, .inr (.n (val% «verify_sub» "size_sel"), vsOpenNames), vsNs [66, 1441, 1442, 1443, 1444, 1445, 1987, 268, 271,
      1989, 1991], vsNs [1992, 1993, 1994, 1995, 1996]),
    (none, .inl "check_opening_terminal", vsNs [4, 254, 604, 616, 253, 614, 72, 618, 83, 1433, 275,
      619, 919, 1993, 1994, 1995, 1996, 1992, 355, 276], [])]

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

theorem vsRetVars_w : ∀ j < 14, ∀ k < (vsRetVars.getD j []).length,
    (vsRetVars.getD j []).getD k 0 ∈ vsWVars := by decide

/-- **A frame's returns are the oracle's**: the callee's results. -/
theorem vs_rets {rd : Reader} {args : List E} (hl : args.length = 6) (gw : E × E) (bs : List ℕ)
    (outs : List (List E × Main.Layout)) {j : ℕ} (hj : j < 14)
    (hlen : (outs.getD j ([], [])).1.length = (vsRetVars.getD j []).length) :
    (vsNs (vsRetVars.getD j [])).map (vsσ rd (vsW gw bs outs) args) = (outs.getD j ([], [])).1 := by
  apply List.ext_getElem (by rw [vsNs, List.length_map, List.length_map, hlen])
  intro k h1 h2
  have hk : k < (vsRetVars.getD j []).length := by
    rw [vsNs, List.length_map, List.length_map] at h1; exact h1
  simp only [vsNs, List.getElem_map]
  rw [← List.getD_eq_getElem _ 0 hk,
    vs_w hl (vsRetVars_w j hj k hk), vsW_ret gw bs outs hj hk, List.getD_eq_getElem _ _ (by omega)]

/-! ## The honest valuation's values -/

/-- **What the honest valuation gives the frames' arguments** on an honest child. -/
structure VsHonVals {bytecode : List K} {seed : Digest} {c : Child} (S : ChildSegs bytecode seed c)
    (bs : List ℕ) (sqE outE : ℕ) (outs : List (List E × Main.Layout)) (σ : Val) : Prop where
  e61 : σ (.n (val% «verify_sub» "x@8")) = eOfNat S.rate
  e27 : σ (.n (val% «verify_sub» "x@1")) = eOfNat S.logMem
  e268 : σ (.n (val% «verify_sub» "x@9")) = S.x0
  e271 : σ (.n (val% «verify_sub» "x@10")) = S.x1
  oodCell : σ (.n (val% «verify_sub» "nxt[1]@3")) = cellsOfState S.oodSt false 1
  oodCap : [σ (.n (val% «verify_sub» "nxt[8]@3")), σ (.n (val% «verify_sub» "nxt[9]@3")), σ (.n (val% «verify_sub» "nxt[10]@3")), σ (.n (val% «verify_sub» "nxt[11]@3")), σ (.n (val% «verify_sub» "nxt[12]@3"))] = capOf S.oodSt
  oodCh : σ (.n (val% «verify_sub» "nxt[0]@3")) = challengeOf S.oodSt
  e312 : σ (.n (val% «verify_sub» "word0~9")) = ptr (vb bs 1) * gen ^ 11
  s3cap : [σ (.n (val% «verify_sub» "nxt[8]@19")), σ (.n (val% «verify_sub» "nxt[9]@19")), σ (.n (val% «verify_sub» "nxt[10]@19")), σ (.n (val% «verify_sub» "nxt[11]@19")), σ (.n (val% «verify_sub» "nxt[12]@19"))] = S.s3.cap
  beta : σ (.n (val% «verify_sub» "nxt[0]@19")) = S.wb.2
  e583 : σ (.n (val% «verify_sub» "tau_keccak_g")) = gen ^ S.τ
  e587 : σ (.n (val% «verify_sub» "fs0@5~8")) = ptr (S.cL bs)
  ringCell : σ (.n (val% «verify_sub» "nxt[1]@20")) = cellsOfState S.ringSt false 1
  s7cap : [σ (.n (val% «verify_sub» "nxt[8]@36")), σ (.n (val% «verify_sub» "nxt[9]@36")), σ (.n (val% «verify_sub» "nxt[10]@36")), σ (.n (val% «verify_sub» "nxt[11]@36")), σ (.n (val% «verify_sub» "nxt[12]@36"))] = capOf S.s7.perm
  lam : σ (.n (val% «verify_sub» "nxt[0]@36")) = S.lam
  target : σ (.n (val% «verify_sub» "target@136")) = S.target
  e1928 : σ (.n (val% «verify_sub» "sumcheck_target~2")) = ptr (S.cW bs)
  e278 : σ (.n (val% «verify_sub» "size_sel")) = gen ^ (S.μs - 20)
  e66 : σ (.n (val% «verify_sub» "rate_sel")) = Whir.rateSel S.rate
  e322 : σ (.n (val% «verify_sub» "bus_grind")) = gen ^ (S.d - 20)
  e252 : σ (.n (val% «verify_sub» "push_total@54")) = gen ^ S.pushT
  tabs : ∀ d ∈ [379, 596, 607, 624, 1991], σ (.n d) = ptr sqE * gen ^ winTabAt

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
    (hh : ∀ x ∈ hs, x < 33) (hm : logMem ≤ 32)
    (hkb : ∀ s < 8, ς (.n ((val% «verify_sub» "kb[0]") + s)) = gen ^ (([0, logMem] ++ hs).getD s 0))
    (hp4 : ς (.n (val% «verify_sub» "g_squares")) = ptr sqE) (hsq : ReadsAt rd (ptr sqE) expTabAllWords) {b : ℕ} (hb : b < 54) :
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
    (hh : ∀ x ∈ hs, x < 33) (hm : logMem ≤ 32)
    (hkb : ∀ s < 8, ς (.n ((val% «verify_sub» "kb[0]") + s)) = gen ^ (([0, logMem] ++ hs).getD s 0))
    (hp4 : ς (.n (val% «verify_sub» "g_squares")) = ptr sqE) (hsq : ReadsAt rd (ptr sqE) expTabAllWords) :
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
    {outs : List (List E × Main.Layout)} (O : VsOuts S (bases b (vsSizes)) sqE outs)
    {rd : Reader} (hB : Main.MemL rd (bufL b (vsSizes) S.ownW)) (hL : Main.MemL rd Lin) :
    VsHonVals S (bases b (vsSizes)) sqE outE outs
      (vsσ rd (vsW S.gw (bases b (vsSizes)) outs) (vsArgs seed c sqE outE)) := by
  set bs := bases b (vsSizes) with hbs
  set w := vsW S.gw bs outs with hw
  set args := vsArgs seed c sqE outE with hargs
  have hl : args.length = 6 := rfl
  have own : ∀ i < 15, ReadsAt rd (ptr (bs.getD i 0)) (S.ownW.getD i []) :=
    fun i hi ↦ hB _ (vs_own_mem S b hi)
  have wa : ∀ {i a : ℕ}, i < 15 → vsAllocVars.getD i 0 = a → w a = ptr (bs.getD i 0) :=
    fun hi ha ↦ vsW_a hi ha
  have wr : ∀ {j k a : ℕ}, j < 14 → k < (vsRetVars.getD j []).length →
      (vsRetVars.getD j []).getD k 0 = a → w a = (outs.getD j ([], [])).1.getD k 0 :=
    fun hj hk ha ↦ vsW_r hj hk ha
  have hd := S.d_bounds hbl
  have hhs := S.hs_lt33 hbl
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
  obtain ⟨-, o289, o296, o303, o312⟩ := vs_ood (rd := rd) (w := w) hl hws
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
  have o7 := O.o6
  have eF : vsFpwFs w = ⟨capOf S.busSt, []⟩ := by
    simp only [vsFpwFs]
    rw [wr (j := 6) (k := 2) (a := 366) (by norm_num) (by decide) rfl,
      wr (j := 6) (k := 3) (a := 367) (by norm_num) (by decide) rfl,
      wr (j := 6) (k := 4) (a := 368) (by norm_num) (by decide) rfl,
      wr (j := 6) (k := 5) (a := 369) (by norm_num) (by decide) rfl,
      wr (j := 6) (k := 6) (a := 370) (by norm_num) (by decide) rfl, o7]
    rfl
  obtain ⟨-, hβ⟩ := vs_fpw (rd := rd) (w := w) (args := args) hl
  rw [eF] at hβ
  obtain ⟨-, -, hwb, hs3⟩ := S.bus_inv hbl
  -- the tables' evaluations and the stream's cursors
  have hxl := (S.H_run hbl).2.2.2
  obtain ⟨c561, c572, c589, h583, h587⟩ := vs_callsV (rd := rd) (w := w) (args := args) hl
  have h582 : w 617 = ptr (S.cT bs + (13 + (3 * S.nT + 1))) := by
    rw [wr (j := 9) (k := 9) (a := 617) (by norm_num) (by decide) rfl, O.o9, vs_ptr_add]
    simp only [Tables.VtHonest.retsH, Fs.squeeze, capOf, List.cons_append, List.nil_append,
      List.getD_cons_succ, List.getD_cons_zero]
    rw [show ofK (addressOfIndex (S.vtB bs sqE (S.leavesB (outs.take 9))).cur) = ptr (S.cT bs)
      from rfl, mul_assoc, mul_assoc, ← pow_succ', ← pow_add]
    rfl
  have o11 := O.o10
  have h595 : w 630 = ptr (S.cK bs + S.xsK.length) := by
    rw [wr (j := 10) (k := 5) (a := 630) (by norm_num) (by decide) rfl, o11, vs_ptr_add]
    simp only [capOf, List.cons_append, List.nil_append, List.getD_cons_succ, List.getD_cons_zero]
  -- the ring map
  have hnonce : LoadHolds rd (w 630) 0 S.ringN := by
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
    rw [wr (j := 10) (k := 0) (a := 625) (by norm_num) (by decide) rfl,
      wr (j := 10) (k := 1) (a := 626) (by norm_num) (by decide) rfl,
      wr (j := 10) (k := 2) (a := 627) (by norm_num) (by decide) rfl,
      wr (j := 10) (k := 3) (a := 628) (by norm_num) (by decide) rfl,
      wr (j := 10) (k := 4) (a := 629) (by norm_num) (by decide) rfl, o11]
    rfl
  obtain ⟨-, m606, -, mEnd⟩ := vs_maps (rd := rd) (w := w) (args := args) hl hnonce
  have hMap : vsMapSt (vsKCap w) S.ringN = S.ringSt := by rw [hK, S.ringSt_eq hbl]; rfl
  rw [hMap] at m606 mEnd
  have hs7 : S.s7 = ⟨[vsσ rd w args (.n (val% «verify_sub» "nxt[8]@35")), vsσ rd w args (.n (val% «verify_sub» "nxt[9]@35")), vsσ rd w args (.n (val% «verify_sub» "nxt[10]@35")),
      vsσ rd w args (.n (val% «verify_sub» "nxt[11]@35")), vsσ rd w args (.n (val% «verify_sub» "nxt[12]@35"))], []⟩ := by
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
  have hcew : ReadsAt rd (w 617) (((S.claims.drop 4).take 153).map (·.value)) := by
    rw [S.col_vals hbl, (S.evs_eq hbl).1, h582, show 13 + (3 * S.nT + 1) = 14 + 3 * S.nT by omega]
    have hT : ReadsAt rd (ptr (S.cT bs)) S.xsT := subOf_memL hB (S.sub_xsT b hbl)
    rw [← List.take_append_drop (14 + 3 * S.nT) S.xsT] at hT
    have h2 := (Main.readsAt_append'.1 hT).2
    rwa [List.length_take, Nat.min_eq_left (by omega), ← vs_ptr_add] at h2
  have hv : ReadsAt rd (w 361) [S.oodV] := by
    rw [wa (i := 7) (a := 361) (by norm_num) rfl]; exact own 7 (by norm_num)
  obtain ⟨hlsq, htg⟩ := vs_lam (rd := rd) (w := w) (args := args) hl hcl hcol hpool hcew hpi hv
  rw [← hs7] at hlsq
  -- the tail
  obtain ⟨t1928, t1930⟩ := vs_tailV (rd := rd) (w := w) (args := args) hl
  -- the push blocks' total
  have hp4 : vsσ rd w args (.n (val% «verify_sub» "g_squares")) = ptr sqE := vsC_param hl (by norm_num)
  have hsq0 := hL (sqE, expTabAllWords) (hexp _ (by unfold vsExpLin; exact List.mem_singleton_self _))
  have hsq : ReadsAt rd (ptr sqE) expTabAllWords := by dsimp only at hsq0; exact hsq0
  have h72 : w 72 = gen ^ S.logMem := by
    rw [wr (j := 1) (k := 0) (a := 72) (by norm_num) (by decide) rfl, O.o1]; rfl
  obtain ⟨-, -, -, -, -, -, -, -, h84, h85, h86⟩ :=
    vs_sizesV (rd := rd) (w := w) (args := args) hl S.hr1 S.hlm1 h64 h72
  have hdims : ReadsAt rd (w 71) (vsDimsW S.logMem S.hs) := by
    rw [wa (i := 3) (a := 71) (by norm_num) rfl]; exact own 3 (by norm_num)
  have hkb : ∀ s < 8, vsσ rd w args (.n ((val% «verify_sub» "kb[0]") + s)) = gen ^ ([0, S.logMem] ++ S.hs).getD s 0 := by
    intro s hs
    rw [← S.kb_pow hbl hs]
    rcases s with _ | _ | t
    · exact h84
    · exact h85
    · rw [show 84 + (t + 2) = 86 + t by omega, h86 t (by omega),
        vs_rdAt_of_load (vs_rdg hdims (k := 1 + t) (by simp [vsDimsW, S.hs_length]; omega))]
      simp only [vsDimsW, List.getD_cons_succ, show 1 + t = t + 1 by omega]
  have hτ : S.τ = S.hs.getD 5 0 := S.τ_eq
  have hlam : vsσ rd w args (.n (val% «verify_sub» "nxt[0]@36")) = S.lam := by
    show _ = S.s7.squeeze.1
    rw [hlsq]
  refine ⟨(W 7 (by omega)).1.trans st7, (W 0 (by omega)).1.trans st0,
    (W 8 (by omega)).1.trans st8', (W 9 (by omega)).1.trans st9, o289, o296, o303,
    by rw [o312, wa (i := 1) (a := 25) (by norm_num) rfl]; rfl, ?_, ?_, ?_, ?_, m606, ?_, ?_, ?_,
    ?_, (vs_placeV (rd := rd) (w := w) (args := args) hl S.hmu20 h276).1, ?_,
    (vs_busGrind (rd := rd) (w := w) (args := args) hl (by omega) h253).1, ?_, ?_⟩
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
      wr (j := 11) (k := 0) (a := 1432) (by norm_num) (by decide) rfl, O.o11,
      wr (j := 10) (k := 6) (a := 631) (by norm_num) (by decide) rfl, o11, S.ring_inv.2.2.1]
    rfl
  · rw [t1928, h595, ← pow_one gen, ← vs_ptr_add,
      show S.cW bs = S.cK bs + S.xsK.length + 1 by
        simp only [ChildSegs.cW, ChildSegs.cR, S.ring_inv.1, List.length_cons, List.length_nil]]
  · rw [(vs_sizesV (rd := rd) (w := w) (args := args) hl S.hr1 S.hlm1 h64 h72).2.1, Whir.rateSel,
      gen_pow_eq_ofK]
  · have h := vs_pushProd (rd := rd) (w := w) (args := args) hl hhs (S.h30.trans (by norm_num)) hkb hp4 hsq 53 (by norm_num)
    exact h
  · have c328 := (vs_busGrind (rd := rd) (w := w) (args := args) hl (by omega) h253).2.2
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl
    · rw [c328, hp4]
    · rw [c561, hp4]
    · rw [c572, hp4]
    · rw [c589, hp4]
    · rw [t1930, hp4]


/-! ## The frames match -/

theorem vs_rets' {rd : Reader} {args : List E} (hl : args.length = 6) (gw : E × E) (bs : List ℕ)
    (outs : List (List E × Main.Layout)) {j : ℕ} (hj : j < 14) {rs : List ℕ}
    (hrs : vsRetVars.getD j [] = rs) (hlen : (outs.getD j ([], [])).1.length = rs.length) :
    (vsNs rs).map (vsσ rd (vsW gw bs outs) args) = (outs.getD j ([], [])).1 := by
  subst hrs; exact vs_rets hl gw bs outs hj hlen

theorem vs_squeezeN_capLen : ∀ (n : ℕ) (s : Fs), s.cap.length = 5 → (s.squeezeN n).2.cap.length = 5
  | 0, _, h => h
  | n + 1, s, _ => vs_squeezeN_capLen n s.squeeze.2 (by simp [Fs.squeeze, capOf])

/-- **The frames match the callees** on an honest child. -/
theorem vs_callsMatch {bytecode : List K} (hbl : bytecode.length = 2 ^ 23) {seed : Digest}
    {c : Child} (S : ChildSegs bytecode seed c) {sqE outE : ℕ} {Lin : Main.Layout}
    (hexp : ∀ q ∈ vsExpLin sqE, q ∈ Lin) : VsCallsMatch S sqE outE Lin := by
  intro b outs O rd hB hL
  have V := vs_honVals hbl S b sqE outE hexp O hB hL
  set bs := bases b (vsSizes) with hbs
  set w := vsW S.gw bs outs with hw
  set args := vsArgs seed c sqE outE with hargs
  set σ := vsσ rd w args with hσ
  have hl : args.length = 6 := rfl
  have pa : ∀ {i a : ℕ}, i < 15 → vsAllocVars.getD i 0 = a → σ (.n a) = ptr (bs.getD i 0) :=
    fun hi ha ↦ by
      rw [hσ, vs_w hl (by rw [← ha]; exact vs_allocVars_w _ (vsAllocVars_idx _ hi).1)]
      exact vsW_a hi ha
  have pr : ∀ {j k a : ℕ}, j < 14 → k < (vsRetVars.getD j []).length →
      (vsRetVars.getD j []).getD k 0 = a → σ (.n a) = (outs.getD j ([], [])).1.getD k 0 :=
    fun hj hk ha ↦ by
      rw [hσ, vs_w hl (by rw [← ha]; exact vsRetVars_w _ hj _ hk)]; exact vsW_r hj hk ha
  have p4 : σ (.n (val% «verify_sub» "g_squares")) = ptr sqE := vsC_param hl (by norm_num)
  have hd := S.d_bounds hbl
  rw [vs_calls]
  refine callsMatch_kidsAt _ _ _ _ rfl (by rw [S.kids_length, O.len]) fun j hj ↦ ?_
  have hj16 : j < 14 := by rw [List.length_map, List.length_map] at hj; exact hj
  rw [vs_kidsAt_getD]
  interval_cases j
  · refine ⟨rfl, rfl, fun _ ↦ ⟨?_, vs_rets' hl _ bs outs (j := 0) (by norm_num) rfl (by rw [O.o0]; simp)⟩⟩
    show [σ (.n (val% «verify_sub» "x@8"))] = [eOfNat S.rate]
    rw [V.e61]
  · refine ⟨rfl, rfl, fun _ ↦ ⟨?_, vs_rets' hl _ bs outs (j := 1) (by norm_num) rfl (by rw [O.o1]; simp)⟩⟩
    show [σ (.n (val% «verify_sub» "x@1"))] = [eOfNat S.logMem]
    rw [V.e27]
  · refine ⟨rfl, rfl, fun _ ↦ ⟨?_, vs_rets' hl _ bs outs (j := 2) (by norm_num) rfl (by rw [O.o2]; simp)⟩⟩
    show [σ (.n (val% «verify_sub» "push_total@54")), σ (.n (val% «verify_sub» "g_squares"))] = [gen ^ S.pushT, ptr sqE]
    rw [V.e252, p4]
  · -- `certify_placement`
    obtain ⟨e10, e11, e136, e137, e293, hr3, -⟩ := O.o3
    refine ⟨rfl, rfl, fun _ ↦ ⟨?_, vs_rets' hl _ bs outs (j := 3) (by norm_num) rfl (by rw [hr3]; simp)⟩⟩
    show [σ (.n (val% «verify_sub» "kappa_base")), σ (.n (val% «verify_sub» "g_squares"))] = [ptr (vb bs 4), ptr sqE]
    rw [pa (i := 4) (a := 83) (by norm_num) rfl, p4]; rfl
  · -- `log2_ceil_in_the_exponent__L16_L34`
    obtain ⟨e10, e11, e136, e137, e293, hr3, -⟩ := O.o3
    refine ⟨rfl, rfl, fun _ ↦ ⟨?_, vs_rets' hl _ bs outs (j := 4) (by norm_num) rfl (by rw [O.o4]; simp)⟩⟩
    show [σ (.n (val% «verify_sub» "g_total")), σ (.n (val% «verify_sub» "g_squares"))] = [gen ^ Tables.stackTotal S.kappas, ptr sqE]
    rw [pr (j := 3) (k := 0) (a := 274) (by norm_num) (by decide) rfl, hr3, p4]; rfl
  · -- `squeeze_point_from`
    have hl6 : S.sZ.cap.length = 5 := vs_squeezeN_capLen _ _ (by simp [capOf])
    refine ⟨?_, rfl, fun _ ↦ ⟨?_, vs_rets' hl _ bs outs (j := 5) (by norm_num) rfl (by rw [O.o5, hl6]; simp)⟩⟩
    · show vsSqpNames.getD (logG (σ (.n (val% «verify_sub» "size_sel")))) "" = squeezeNames.getD (S.μs - 20) ""
      rw [V.e278, LeanVM.Guest.Memory.logG_gen_pow (by have := S.hmu30; show S.layout.stackLog - 20 < _; omega)]
      rfl
    · show [σ (.n (val% «verify_sub» "nxt[8]@3")), σ (.n (val% «verify_sub» "nxt[9]@3")), σ (.n (val% «verify_sub» "nxt[10]@3")), σ (.n (val% «verify_sub» "nxt[11]@3")), σ (.n (val% «verify_sub» "nxt[12]@3")), σ (.n (val% «verify_sub» "nxt[0]@3")), σ (.n (val% «verify_sub» "ood_z"))] =
        capOf S.oodSt ++ [challengeOf S.oodSt, ptr (vb bs 6)]
      rw [← V.oodCap, V.oodCh, pa (i := 6) (a := 355) (by norm_num) rfl]; rfl
  · -- `opening_message__L1_L1`
    have hl6 : S.sZ.cap.length = 5 := vs_squeezeN_capLen _ _ (by simp [capOf])
    refine ⟨rfl, rfl, fun _ ↦ ⟨?_, vs_rets' hl _ bs outs (j := 6) (by norm_num) rfl (by rw [O.o6]; simp [capOf])⟩⟩
    have h6 := vs_rets' (rd := rd) hl S.gw bs outs (j := 5) (rs := [356, 357, 358, 359, 360]) (by norm_num) rfl (by rw [O.o5, hl6]; simp)
    rw [O.o5] at h6
    show (vsNs [356, 357, 358, 359, 360]).map σ ++ [σ (.n (val% «verify_sub» "word0~9")), σ (.n (val% «verify_sub» "ood_value"))] =
      S.sZ.cap ++ [ptr (vb bs 1) * gen ^ 11, ptr (vb bs 7)]
    rw [h6, V.e312, pa (i := 7) (a := 361) (by norm_num) rfl]; rfl
  · -- `bus_grind_check`
    refine ⟨?_, rfl, fun _ ↦ ⟨?_, vs_rets' hl _ bs outs (j := 7) (by norm_num) rfl (by rw [O.o7]; simp)⟩⟩
    · show vsBgNames.getD (logG (σ (.n (val% «verify_sub» "bus_grind")))) "" = busGrindNames.getD (S.d - 20) ""
      rw [V.e322, LeanVM.Guest.Memory.logG_gen_pow (by omega)]
      rfl
    · show [σ (.n (val% «verify_sub» "pow_word")), σ (.n (val% «verify_sub» "done~2"))] = [cellsOfState S.busSt false 1, ptr sqE * gen ^ winTabAt]
      rw [pr (j := 6) (k := 1) (a := 365) (by norm_num) (by decide) rfl, O.o6, V.tabs 379 (by simp)]
      rfl
  · -- `verify_bus_gkr`
    obtain ⟨b9, hr9, -⟩ := O.o8
    obtain ⟨-, -, hc4, -, -, -⟩ := S.gkr_inv hbl
    refine ⟨rfl, rfl, fun _ ↦ ⟨?_, vs_rets' hl _ bs outs (j := 8) (by norm_num) rfl (by rw [hr9]; simp [hc4])⟩⟩
    show (vsNs [590, 591, 592, 593, 594]).map σ ++
        [σ (.n (val% «verify_sub» "cursor@1")), σ (.n (val% «verify_sub» "g_bus_mu")), σ (.n (val% «verify_sub» "zeta")), σ (.n (val% «verify_sub» "fs0@3~8")), σ (.n (val% «verify_sub» "stream"))] =
      S.s3.cap ++ [ptr (ChildSegs.cG bs), gen ^ S.d, ptr (vb bs 5), ptr sqE * gen ^ winTabAt,
        ptr (vb bs 1)]
    rw [show (vsNs [590, 591, 592, 593, 594]).map σ = [σ (.n (val% «verify_sub» "nxt[8]@19")), σ (.n (val% «verify_sub» "nxt[9]@19")), σ (.n (val% «verify_sub» "nxt[10]@19")),
      σ (.n (val% «verify_sub» "nxt[11]@19")), σ (.n (val% «verify_sub» "nxt[12]@19"))] from rfl, V.s3cap,
      pr (j := 6) (k := 7) (a := 371) (by norm_num) (by decide) rfl, O.o6,
      show σ (.n (val% «verify_sub» "g_bus_mu")) = gen ^ S.d from (vs_w hl (a := 253) (by decide)).trans (vs_w253 hbl S O),
      pa (i := 5) (a := 254) (by norm_num) rfl, V.tabs 596 (by simp),
      pa (i := 1) (a := 25) (by norm_num) rfl]
    simp only [capOf, List.cons_append, List.nil_append, List.getD_cons_succ, List.getD_cons_zero]
    rw [mul_assoc, ← pow_add, ← vs_ptr_add]
    rfl
  · -- `verify_tables`
    obtain ⟨b9, hr9, hm9⟩ := O.o8
    obtain ⟨-, -, hc4, -, hpl, -⟩ := S.gkr_inv hbl
    refine ⟨rfl, rfl, fun _ ↦ ⟨?_, vs_rets' hl _ bs outs (j := 9) (by norm_num) rfl
      (by rw [O.o9]; simp [Tables.VtHonest.retsH, Fs.squeeze, capOf])⟩⟩
    have e9 : ∀ k < 5, σ (.n ((val% «verify_sub» "fs0@3") + k)) = S.s4.cap.getD k 0 := fun k hk ↦ by
      rw [pr (j := 8) (k := k) (a := 597 + k) (by norm_num) (by simp [vsRetVars]; omega)
        (by interval_cases k <;> rfl), hr9, List.getD_append _ _ _ _ (by omega)]
    have e567 : σ (.n (val% «verify_sub» "cursor@2")) = ptr (S.cT bs) := by
      rw [pr (j := 8) (k := 5) (a := 602) (by norm_num) (by decide) rfl, hr9,
        List.getD_append_right _ _ _ _ (by omega), hc4]
      show ptr (ChildSegs.cG bs) * gen ^ S.xsG.length = _
      rw [← vs_ptr_add]; rfl
    have h6 : (outs.getD 8 ([], [])).1.getD 6 0 = ptr b9 := by
      rw [hr9, List.getD_append_right _ _ _ _ (by omega), hc4]; rfl
    have e568 : σ (.n (val% «verify_sub» "gkr_leaves")) = ptr (S.leavesB (outs.take 9)) := by
      rw [pr (j := 8) (k := 6) (a := 603) (by norm_num) (by decide) rfl]
      have hex : ∃ b, (ChildSegs.gkRes (outs.take 9)).1.getD 6 0 = ptr b ∧
          (b, S.rG.2.2) ∈ (ChildSegs.gkRes (outs.take 9)).2 := by
        refine ⟨b9, ?_, ?_⟩
        · rw [ChildSegs.gkRes, take_getD _ _ (by norm_num)]; exact h6
        · rw [ChildSegs.gkRes, take_getD _ _ (by norm_num)]; exact hm9
      unfold ChildSegs.leavesB
      split
      · rename_i h
        rw [← (Classical.choose_spec h).1, ChildSegs.gkRes, take_getD _ _ (by norm_num)]
      · exact absurd hex ‹_›
    have hμ : S.H.μ = S.d := hpl
    show [σ (.n (val% «verify_sub» "fs0@3")), σ (.n (val% «verify_sub» "fs1@3")), σ (.n (val% «verify_sub» "fs2@3")), σ (.n (val% «verify_sub» "fs3@3")), σ (.n (val% «verify_sub» "fs4@3")), σ (.n (val% «verify_sub» "cursor@2")), σ (.n (val% «verify_sub» "pi_0")),
      σ (.n (val% «verify_sub» "pi_1")), σ (.n (val% «verify_sub» "zeta")), σ (.n (val% «verify_sub» "g_bus_mu")), σ (.n (val% «verify_sub» "dims_g")), σ (.n (val% «verify_sub» "table_rows")), σ (.n (val% «verify_sub» "g_squares")), σ (.n (val% «verify_sub» "fp_w")), σ (.n (val% «verify_sub» "nxt[0]@19")),
      σ (.n (val% «verify_sub» "claim_pool")), σ (.n (val% «verify_sub» "chi")), σ (.n (val% «verify_sub» "gkr_leaves")), σ (.n (val% «verify_sub» "fs0@4~11")), σ (.n (val% «verify_sub» "bc_point")), σ (.n (val% «verify_sub» "stream"))] =
      S.H.args (S.vtB bs sqE (S.leavesB (outs.take 9)))
    rw [e9 0 (by norm_num), e9 1 (by norm_num), e9 2 (by norm_num), e9 3 (by norm_num),
      e9 4 (by norm_num), e567, show σ (.n (val% «verify_sub» "pi_0")) = args.getD 0 0 from vsC_param hl (by norm_num),
      show σ (.n (val% «verify_sub» "pi_1")) = args.getD 1 0 from vsC_param hl (by norm_num), pa (i := 5) (a := 254) (by norm_num) rfl,
      show σ (.n (val% «verify_sub» "g_bus_mu")) = gen ^ S.d from (vs_w hl (a := 253) (by decide)).trans (vs_w253 hbl S O),
      pa (i := 3) (a := 71) (by norm_num) rfl, pa (i := 2) (a := 26) (by norm_num) rfl, p4,
      pa (i := 8) (a := 386) (by norm_num) rfl, V.beta, pa (i := 0) (a := 6) (by norm_num) rfl,
      pa (i := 9) (a := 604) (by norm_num) rfl, e568, V.tabs 607 (by simp),
      pa (i := 10) (a := 605) (by norm_num) rfl, pa (i := 1) (a := 25) (by norm_num) rfl,
      Tables.VtHonest.args, hμ]
    rfl
  · -- `verify_keccak`
    have hxl := (S.H_run hbl).2.2.2
    refine ⟨rfl, rfl, fun _ ↦ ⟨?_, vs_rets' hl _ bs outs (j := 10) (by norm_num) rfl
      (by rw [O.o10]; simp [capOf])⟩⟩
    have eK : ∀ k < 6, σ (.n ((val% «verify_sub» "fs0@4") + k)) = (S.H.retsH (S.vtB bs sqE (S.leavesB (outs.take 9)))).getD k 0 :=
      fun k hk ↦ by
        rw [pr (j := 9) (k := k) (a := 608 + k) (by norm_num) (by simp [vsRetVars]; omega)
          (by interval_cases k <;> rfl), O.o9]
    show [σ (.n (val% «verify_sub» "fs0@4")), σ (.n (val% «verify_sub» "fs1@4")), σ (.n (val% «verify_sub» "fs2@4")), σ (.n (val% «verify_sub» "fs3@4")), σ (.n (val% «verify_sub» "fs4@4")), σ (.n (val% «verify_sub» "cursor@3")), σ (.n (val% «verify_sub» "tau_keccak_g")),
      σ (.n (val% «verify_sub» "chi")), σ (.n (val% «verify_sub» "fs0@5~8")), σ (.n (val% «verify_sub» "z_vals")), σ (.n (val% «verify_sub» "slices")), σ (.n (val% «verify_sub» "fs0@5~10")), σ (.n (val% «verify_sub» "stream"))] =
      S.H.s3.squeeze.2.cap ++ [ptr (S.cK bs), gen ^ S.τ, ptr (vb bs 9), ptr (S.cL bs),
        ptr (vb bs 11), ptr (vb bs 12), ptr (sqE + winTabAt), ptr (vb bs 1)]
    rw [eK 0 (by norm_num), eK 1 (by norm_num), eK 2 (by norm_num), eK 3 (by norm_num),
      eK 4 (by norm_num), eK 5 (by norm_num), V.e583, pa (i := 9) (a := 604) (by norm_num) rfl,
      V.e587, pa (i := 11) (a := 619) (by norm_num) rfl, pa (i := 12) (a := 620) (by norm_num) rfl,
      V.tabs 624 (by simp), ← vs_ptr_add sqE winTabAt, pa (i := 1) (a := 25) (by norm_num) rfl]
    simp only [Tables.VtHonest.retsH, Fs.squeeze, capOf, List.cons_append, List.nil_append,
      List.getD_cons_succ, List.getD_cons_zero]
    rw [show ofK (addressOfIndex (S.vtB bs sqE (S.leavesB (outs.take 9))).cur) = ptr (S.cT bs)
      from rfl, show ptr (S.cT bs) * gen ^ 13 * gen * gen ^ (3 * S.H.n) * gen ^ 153 = ptr (S.cK bs) by
        rw [show S.cK bs = S.cT bs + 13 + 1 + 3 * S.H.n + 153 by
          simp only [ChildSegs.cK]; rw [hxl]; show _ = _ + 13 + 1 + 3 * S.nT + 153; omega,
          vs_ptr_add, vs_ptr_add, vs_ptr_add, vs_ptr_add, pow_one]]
    rfl
  · -- `ring_switch_target`
    refine ⟨rfl, rfl, fun _ ↦ ⟨?_, vs_rets' hl _ bs outs (j := 11) (by norm_num) rfl
      (by rw [O.o11]; simp)⟩⟩
    show [σ (.n (val% «verify_sub» "slices")), σ (.n (val% «verify_sub» "map_challenges"))] = [ptr (vb bs 12), ptr (vb bs 13)]
    rw [pa (i := 12) (a := 620) (by norm_num) rfl, pa (i := 13) (a := 918) (by norm_num) rfl]; rfl
  · -- `open_stacked`
    obtain ⟨b14, b14', hr14, -⟩ := O.o12
    refine ⟨?_, rfl, fun _ ↦ ⟨?_, vs_rets' hl _ bs outs (j := 12) (by norm_num) rfl
      (by rw [hr14]; simp)⟩⟩
    · show vsOpenNames.getD (logG (σ (.n (val% «verify_sub» "size_sel")))) "" = Whir.openName S.μs
      have := S.hmu30
      rw [V.e278, LeanVM.Guest.Memory.logG_gen_pow (by
        show S.layout.stackLog - 20 < _; omega), vsOpenNames_eq]
      rfl
    · show [σ (.n (val% «verify_sub» "rate_sel")), σ (.n (val% «verify_sub» "nxt[8]@36")), σ (.n (val% «verify_sub» "nxt[9]@36")), σ (.n (val% «verify_sub» "nxt[10]@36")), σ (.n (val% «verify_sub» "nxt[11]@36")), σ (.n (val% «verify_sub» "nxt[12]@36")),
        σ (.n (val% «verify_sub» "target@136")), σ (.n (val% «verify_sub» "x@9")), σ (.n (val% «verify_sub» "x@10")), σ (.n (val% «verify_sub» "sumcheck_target~2")), σ (.n (val% «verify_sub» "sumcheck_target~4"))] =
        Whir.rateSel S.rate :: capOf S.s7.perm ++ [S.target, (digestHalves S.root).1,
          (digestHalves S.root).2, ptr (S.cW bs), ptr sqE * gen ^ winTabAt]
      rw [V.e66, ← V.s7cap, V.target, V.e268, V.e271, V.e1928, V.tabs 1991 (by simp), ← S.hroot,
        digestScalars_digestOfScalars]
      rfl
  · -- `check_opening_terminal`
    obtain ⟨e10, e11, e136, e137, e293, hr3, hL3⟩ := O.o3
    obtain ⟨b14, b14', hr14, hL14⟩ := O.o12
    refine ⟨rfl, (@decide_eq_true _ (Classical.propDecidable _) O.term).symm, fun _ ↦ ⟨?_,
      vs_rets' hl _ bs outs (j := 13) (rs := []) (by norm_num) rfl (by rw [O.o13]; simp)⟩⟩
    have r10 : ∀ k < 10, σ (.n ((val% «verify_sub» "fs0@4") + k)) =
        (S.H.retsH (S.vtB bs sqE (S.leavesB (outs.take 9)))).getD k 0 := fun k hk ↦ by
      rw [pr (j := 9) (k := k) (a := 608 + k) (by norm_num) (by simp [vsRetVars]; omega)
        (by interval_cases k <;> rfl), O.o9]
    have r14 : ∀ k < 5, σ (.n ((val% «verify_sub» "sumcheck_target") + k)) = [S.w.target, ptr b14, ptr b14', S.w.inner,
        S.w.residual].getD k 0 := fun k hk ↦ by
      rw [pr (j := 12) (k := k) (a := 1992 + k) (by norm_num) (by simp [vsRetVars]; omega)
        (by interval_cases k <;> rfl), hr14]
    show [σ (.n (val% «verify_sub» "g_squares")), σ (.n (val% «verify_sub» "zeta")), σ (.n (val% «verify_sub» "chi")), σ (.n (val% «verify_sub» "rm")), σ (.n (val% «verify_sub» "g_bus_mu")), σ (.n (val% «verify_sub» "g_zc_n")),
      σ (.n (val% «verify_sub» "g_log_mem")), σ (.n (val% «verify_sub» "tau_keccak_g")), σ (.n (val% «verify_sub» "kappa_base")), σ (.n (val% «verify_sub» "nxt[0]@36")), σ (.n (val% «verify_sub» "col_offsets")), σ (.n (val% «verify_sub» "z_vals")), σ (.n (val% «verify_sub» "c_table")),
      σ (.n (val% «verify_sub» "point")), σ (.n (val% «verify_sub» "point1")), σ (.n (val% «verify_sub» "inner_total")), σ (.n (val% «verify_sub» "yr_at_tail")),
      σ (.n (val% «verify_sub» "sumcheck_target")), σ (.n (val% «verify_sub» "ood_z")), σ (.n (val% «verify_sub» "gmv"))] =
      termArgs (ChildSegs.termB bs sqE (outs.take 13)) S.H.rm (gen ^ S.d) (gen ^ S.nT) (gen ^ S.logMem)
        (gen ^ S.τ) S.lam S.w.inner S.w.residual S.w.target
        (gen ^ max 16 (log2Ceil (Tables.stackTotal S.kappas)))
    rw [p4, pa (i := 5) (a := 254) (by norm_num) rfl, pa (i := 9) (a := 604) (by norm_num) rfl,
      r10 8 (by norm_num),
      show σ (.n (val% «verify_sub» "g_bus_mu")) = gen ^ S.d from (vs_w hl (a := 253) (by decide)).trans (vs_w253 hbl S O),
      r10 6 (by norm_num), pr (j := 1) (k := 0) (a := 72) (by norm_num) (by decide) rfl, O.o1,
      V.e583, pa (i := 4) (a := 83) (by norm_num) rfl, V.lam,
      pr (j := 3) (k := 1) (a := 275) (by norm_num) (by decide) rfl, hr3,
      pa (i := 11) (a := 619) (by norm_num) rfl, pa (i := 14) (a := 919) (by norm_num) rfl,
      r14 1 (by norm_num), r14 2 (by norm_num), r14 3 (by norm_num), r14 4 (by norm_num),
      r14 0 (by norm_num), pa (i := 6) (a := 355) (by norm_num) rfl,
      pr (j := 4) (k := 0) (a := 276) (by norm_num) (by decide) rfl, O.o4]
    simp only [termArgs, ChildSegs.termB, ChildSegs.termBs, ChildSegs.cpRes, ChildSegs.osRes,
      take_getD _ _ (show 3 < 13 by norm_num), take_getD _ _ (show 12 < 13 by norm_num), hL3, hL14,
      Tables.cpOwn, Tables.VtHonest.retsH, Fs.squeeze, capOf, List.cons_append, List.nil_append,
      List.getD_cons_succ, List.getD_cons_zero]
    rfl

end
end LeanVM.Guest.B1.VerifySub
