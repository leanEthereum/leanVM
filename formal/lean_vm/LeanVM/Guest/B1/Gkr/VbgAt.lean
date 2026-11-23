/-
  LeanVM.Guest.B1.Gkr.VbgAt

  `verify_bus_gkr` is complete in the uniform placed form (`CompleteAtD`).
-/

module

public import LeanVM.Guest.B1.Gkr.VbgLoads
public import LeanVM.Guest.B1.Gkr.GlCInVbg
public import LeanVM.Guest.B1.Gkr.GlCInZeta
public import LeanVM.Guest.B1.Tables.FlatLiftOut
public import LeanVM.Guest.Data.NameStrings
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_bus_gkr»

/-!
# `verify_bus_gkr`, placed (TRIAGE G #43)

`vbg_run`: at `2 ≤ depth`, on a memory defined below `2^κ` (`κ ≥ 6`, the range check of
`g^depth`) holding the cursor's words, the point at `zeta` and the eight buffers whole
(`vbgOwnW`), the honest valuation (`vbgFlat.σ`, the allocations answered by the buffers'
pointers) satisfies every statement with its calls by relations loading from a region `R`
holding the cursor's words, the point and the buffers, its loads land inside the buffers
(`vbg_loadOk`, `vbg_ptrs`; the radix-four arm's fourteen words past the cursor are the run's at
`depth ≥ 2`, `gk_xs_len`), its allocations are the buffers and it returns the accepting run's
capacity, cursor and the values' buffer. The radix-four layers' dispatch loads from `R`
(`vbg_layers_relIn`), and the point's copy `verify_bus_gkr_loop0` (`vbz_relIn`).

`verify_bus_gkr_completeAt`: `flat_completeAtOut` for `vbgFlat`, the buffers at the bump
allocator's positions from `fp + fs "verify_bus_gkr"`, returned (`VbgOut`: the values' buffer is
among them).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-! ## Kernel facts -/

/-- An atom, or an `ite` of atoms. -/
def atomsDeep : Stmt → Bool
  | .atom _ => true
  | .ite _ z n => (z ++ n).all fun t ↦ match t with
    | .atom _ => true
    | _ => false
  | _ => false

/-- The radix-four layers' dispatch. -/
def vbgCallL : Stmt :=
  .dispatch (.n (val% «verify_bus_gkr» "odd_g")) [glcLsN 0, glcLsN 1] [.n (val% «verify_bus_gkr» "layers"), .n (val% «verify_bus_gkr» "rounds"), .n (val% «verify_bus_gkr» "gkr_pts"), .n (val% «verify_bus_gkr» "n_four"), .n (val% «verify_bus_gkr» "rem_g"), .n (val% «verify_bus_gkr» "start_g"), .n (val% «verify_bus_gkr» "g_bus_mu"), .n (val% «verify_bus_gkr» "tabs"),
    .n (val% «verify_bus_gkr» "stream")] [.n (val% «verify_bus_gkr» "done")]

/-- `verify_bus_gkr_loop0`'s call. -/
def vbgCallZ : Stmt := .callIf (.n (val% «verify_bus_gkr» "s36#1")) name% «verify_bus_gkr_loop0» [.n (val% «verify_bus_gkr» "s36#2"), .n (val% «verify_bus_gkr» "g_bus_mu"), .n (val% «verify_bus_gkr» "zeta"), .n (val% «verify_bus_gkr» "final_point_row")]

/-- Every statement is an atom, an `ite` of atoms, the dispatch or the call. -/
def vbgKindB (s : Stmt) : Bool :=
  atomsDeep s || tbStmtsEqb [s] [vbgCallL] || tbStmtsEqb [s] [vbgCallZ]

theorem vbg_kinds : vbgPre.all vbgKindB = true := by decide +kernel

theorem vbg_allocs : vbgPre.filterMap Main.Stmt.allocSz = [(.n (val% «verify_bus_gkr» "layers"), .inr (.n (val% «verify_bus_gkr» "layers~5"))),
    (.n (val% «verify_bus_gkr» "gkr_sizes"), .inl 66), (.n (val% «verify_bus_gkr» "rounds"), .inr (.n (val% «verify_bus_gkr» "rounds~1"))),
    (.n (val% «verify_bus_gkr» "gkr_pts"), .inr (.n (val% «verify_bus_gkr» "gkr_pts~1"))), (.n (val% «verify_bus_gkr» "depth_odd"), .inl 33), (.n (val% «verify_bus_gkr» "four_bounds"), .inl 33), (.n (val% «verify_bus_gkr» "four_rem"), .inl 33),
    (.n (val% «verify_bus_gkr» "leaves"), .inl 3)] := by
  decide +kernel

theorem vsh_atomsDeep {C C' : CallRel} {rd : Reader} {σ : Val} :
    ∀ {s : Stmt}, atomsDeep s = true → VSH C rd σ s → VSH C' rd σ s
  | .atom _, _, h => h
  | .ite c z n, hs, h => by
    simp only [atomsDeep, List.all_eq_true] at hs
    have ha : ∀ t ∈ z ++ n, SHolds C rd σ t → SHolds C' rd σ t := by
      intro t ht h'
      have := hs t ht
      cases t with
      | atom a => exact h'
      | _ => simp at this
    exact ⟨h.1, fun hc t ht ↦ ha t (List.mem_append_left _ ht) (h.2.1 hc t ht),
      fun hc t ht ↦ ha t (List.mem_append_right _ ht) (h.2.2 hc t ht)⟩

/-- The cursor's words reach `14` past depth one: two roots and the first steps. -/
theorem gk_xs_len {depth : ℕ} (hd2 : 2 ≤ depth) {cap0 xs : List E} {r : E × List E × List E}
    {cap' : List E} (hrun : RunsTo (gkrPhase depth) ⟨cap0, []⟩ xs r ⟨cap', []⟩)
    (hc : ∃ sp, (⟨cap0, []⟩ : Fs).Carries sp) : 14 ≤ xs.length := by
  obtain ⟨-, hx2, hodd, hsteps, -, -, -, -⟩ := gk_walk hrun hc
  obtain ⟨hok, hdr⟩ := hsteps 0 (by omega)
  have hpl0 := gkSl0_point_len cap0 xs (depth % 2) (by omega)
  have hl := gkStepD_xs_length hok
  have h0' : 2 ≤ (gkSl cap0 xs (depth % 2) 0).2.2 := by rw [gkSl0_off]; split <;> omega
  have h1' : (gkSl cap0 xs (depth % 2) 1).2.2 =
      (gkSl cap0 xs (depth % 2) 0).2.2 + 4 * (2 * 0 + depth % 2) + 12 := rfl
  have hle := tb_drop_le hdr (by rw [hl, hpl0, h1']; norm_num; omega) (by rw [h1']; omega)
  rw [h1'] at hle
  omega

theorem vbg_load_cls {d p : V} {off : ℕ} (hm : Stmt.atom (.load d p off) ∈ vbgEvL) :
    p = .n p.idx ∧ ((p.idx = (val% «verify_bus_gkr» "cursor@1") ∧ off < 14) ∨ (p.idx = (val% «verify_bus_gkr» "nxt") ∧ off < 10) ∨
      (p.idx = (val% «verify_bus_gkr» "gkr_pts") ∧ off < 42) ∨
      (((p.idx = (val% «verify_bus_gkr» "depth_odd") ∨ p.idx = (val% «verify_bus_gkr» "four_bounds")) ∨ p.idx = (val% «verify_bus_gkr» "four_rem")) ∧ off < 33) ∨
      (((p.idx = (val% «verify_bus_gkr» "odd_g~0") ∨ p.idx = (val% «verify_bus_gkr» "n_four~0")) ∨ p.idx = (val% «verify_bus_gkr» "rem_g~0")) ∧ off = 0) ∨
      (p.idx = (val% «verify_bus_gkr» "last") ∧ off < 10) ∨ (p.idx = (val% «verify_bus_gkr» "leaves") ∧ off < 3) ∨
      (p.idx = (val% «verify_bus_gkr» "gkr_sizes") ∧ off < 66) ∨ (p.idx = (val% «verify_bus_gkr» "rounds~0") ∧ off = 0) ∨
      (p.idx = (val% «verify_bus_gkr» "gkr_pts~0") ∧ off = 33)) := by
  have hok := List.all_eq_true.mp vbg_loadOk _ hm
  obtain ⟨path, tag, k⟩ := p
  cases path with
  | nil =>
    cases tag with
    | zero =>
      refine ⟨rfl, ?_⟩
      simp only [vbgLoadOk, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
        at hok
      exact hok
    | succ t => simp [vbgLoadOk] at hok
  | cons a l => simp [vbgLoadOk] at hok

/-- The honest valuation of `verify_bus_gkr` on its buffers at `g^eL .. g^eS`, the cursor at
`g^ec`, `zeta` at `g^ez`. -/
noncomputable def vbgσ (rd : Reader) (depth : ℕ) (cap0 : List E) (tabs stream : E)
    (ec ez eL eR eP eO eB eM eV eS : ℕ) : Val :=
  vbgFlat.σ rd (vbgW (ofK (addressOfIndex eL)) (ofK (addressOfIndex eS)) (ofK (addressOfIndex eR))
      (ofK (addressOfIndex eP)) (ofK (addressOfIndex eO)) (ofK (addressOfIndex eB))
      (ofK (addressOfIndex eM)) (ofK (addressOfIndex eV)))
    (cap0 ++ [ofK (addressOfIndex ec), gen ^ depth, ofK (addressOfIndex ez), tabs, stream])

/-- The values of the dispatch to `gkr_layers__L{o}` and of `verify_bus_gkr_loop0`'s call. -/
def VbgVals (σ : Val) (depth eL eR eP : ℕ) (tabs stream : E) : Prop :=
  σ (.n (val% «verify_bus_gkr» "odd_g")) = gen ^ (depth % 2) ∧ σ (.n (val% «verify_bus_gkr» "n_four")) = gen ^ ((depth - 1) / 8) ∧
    σ (.n (val% «verify_bus_gkr» "rem_g")) = gen ^ ((depth - 1) / 2 % 4) ∧ σ (.n (val% «verify_bus_gkr» "start_g")) = gen ^ (2 - depth % 2) ∧
    σ (.n (val% «verify_bus_gkr» "s36#2")) = 1 ∧ σ (.n (val% «verify_bus_gkr» "g_bus_mu")) = gen ^ depth ∧ σ (.n (val% «verify_bus_gkr» "layers")) = ofK (addressOfIndex eL) ∧
    σ (.n (val% «verify_bus_gkr» "rounds")) = ofK (addressOfIndex eR) ∧ σ (.n (val% «verify_bus_gkr» "gkr_pts")) = ofK (addressOfIndex eP) ∧
    σ (.n (val% «verify_bus_gkr» "tabs")) = tabs ∧ σ (.n (val% «verify_bus_gkr» "stream")) = stream ∧ σ (.n (val% «verify_bus_gkr» "s36#1")) = 1 + gen ^ depth

/-- The buffers of `verify_bus_gkr` in a region, and the cursor's words and the point. -/
structure VbgR (R : ℕ → Prop) (depth : ℕ) (xs : List E) (ec ez eL eR eP : ℕ) : Prop where
  z : ∀ i < depth, R (ez + i)
  r : ∀ i < (depth / 2 + 2) * 40, R (eP + i)
  x : ∀ i < xs.length, R (ec + i)
  l : ∀ i < 10 * (depth + 2), R (eL + i)
  rr : ∀ i < 7 * gkRecCount depth, R (eR + i)

/-- **`verify_bus_gkr`'s honest valuation on a memory holding its words**: every statement holds,
its calls loading from `R`; its loads land inside its buffers; its allocations are the buffers; it
returns the accepting run's capacity, cursor and the values' buffer. -/
theorem vbg_run {depth κ : ℕ} (hd2 : 2 ≤ depth) (hd : depth ≤ 32) (hκ : 6 ≤ κ)
    {cap0 xs : List E} {r : E × List E × List E} {cap' : List E}
    (hrun : RunsTo (gkrPhase depth) ⟨cap0, []⟩ xs r ⟨cap', []⟩)
    (hc : ∃ sp, (⟨cap0, []⟩ : Fs).Carries sp) {tabs stream : E}
    {ec ez eL eR eP eO eB eM eV eS : ℕ} {rd : Reader} {R : ℕ → Prop} (hlow : LowDef κ rd)
    (hx : TbReadsAt rd (ofK (addressOfIndex ec)) xs)
    (hz : TbReadsAt rd (ofK (addressOfIndex ez)) r.2.1)
    (hL : TbReadsAt rd (ofK (addressOfIndex eL)) (vbgLayersW depth cap0 xs (ofK (addressOfIndex
        ec))))
    (hR : TbReadsAt rd (ofK (addressOfIndex eR)) (vbgRoundsW depth cap0 xs (ofK
        (addressOfIndex ec))))
    (hP : TbReadsAt rd (ofK (addressOfIndex eP)) (vbgRowsW depth cap0 xs))
    (hO : TbReadsAt rd (ofK (addressOfIndex eO)) vbgOddW)
    (hB : TbReadsAt rd (ofK (addressOfIndex eB)) vbgBndW)
    (hM : TbReadsAt rd (ofK (addressOfIndex eM)) vbgRemW)
    (hV : TbReadsAt rd (ofK (addressOfIndex eV)) (vbgValsW depth cap0 xs))
    (hS : TbReadsAt rd (ofK (addressOfIndex eS)) vbgSizesW)
    (hReg : VbgR R depth xs ec ez eL eR eP) :
    (∀ s ∈ vbgPre, VSH (coreProgram.RelIn rd R) rd
      (vbgσ rd depth cap0 tabs stream ec ez eL eR eP eO eB eM eV eS) s) ∧
    LoadsInBuf (vbgσ rd depth cap0 tabs stream ec ez eL eR eP eO eB eM eV eS)
      [(ofK (addressOfIndex ec), xs.length), (ofK (addressOfIndex eL), 10 * (depth + 2)),
        (ofK (addressOfIndex eS), 66), (ofK (addressOfIndex eR), 7 * gkRecCount depth),
        (ofK (addressOfIndex eP), (depth / 2 + 2) * 40),
        (ofK (addressOfIndex eO), 33), (ofK (addressOfIndex eB), 33),
        (ofK (addressOfIndex eM), 33), (ofK (addressOfIndex eV), 3)] vbgEvL ∧
    (vbgPre.filterMap Main.Stmt.allocSz).map
      (fun x => x.2.elim id fun s => logG (vbgσ rd depth cap0 tabs stream ec ez eL eR eP eO eB eM
        eV eS s)) = vbgSizes depth ∧
    ((vbgPre.filterMap Main.Stmt.allocSz).map Prod.fst).map
        (vbgσ rd depth cap0 tabs stream ec ez eL eR eP eO eB eM eV eS) =
      [ofK (addressOfIndex eL), ofK (addressOfIndex eS), ofK (addressOfIndex eR),
        ofK (addressOfIndex eP), ofK (addressOfIndex eO), ofK (addressOfIndex eB),
        ofK (addressOfIndex eM), ofK (addressOfIndex eV)] ∧
    vbgRets.map (vbgσ rd depth cap0 tabs stream ec ez eL eR eP eO eB eM eV eS) =
      cap' ++ [ofK (addressOfIndex ec) * gen ^ xs.length, ofK (addressOfIndex eV)] ∧
    VbgVals (vbgσ rd depth cap0 tabs stream ec ez eL eR eP eO eB eM eV eS) depth eL eR eP tabs
      stream := by
  obtain ⟨sp, hsp⟩ := hc
  obtain ⟨-, -, -, hsteps, -, -, -, -⟩ := gk_walk hrun ⟨sp, hsp⟩
  have hsc : capOf sp.state = cap0 := hsp.1
  have hcl : cap0.length = 5 := by rw [← hsc]; simp [capOf]
  have hpl : ∀ j ≤ depth / 2, (gkSl cap0 xs (depth % 2) j).2.1.point.length = 2 * j + depth % 2 :=
    gkSl_point_len (gkSl0_point_len cap0 xs (depth % 2) (by omega)) fun j hj ↦ (hsteps j hj).1
  have hm := vbg_memLay (eL := eL) (eR := eR) (eP := eP) (eO := eO) (eB := eB) (eM := eM)
    (eV := eV) (eS := eS) hd hcl hpl hL hR hP hO hB hM hV hS
  have h64 : (64 : ℕ) ≤ 2 ^ κ := by
    calc (64 : ℕ) = 2 ^ 6 := by norm_num
      _ ≤ 2 ^ κ := Nat.pow_le_pow_right (by norm_num) hκ
  have hrc : (rd (addressOfIndex depth)).isSome = true ∧ (rd (addressOfIndex (32 - depth))).isSome =
      true :=
    ⟨hlow depth (by omega), hlow (32 - depth) (by omega)⟩
  obtain ⟨hh, hrt⟩ := verify_bus_gkr_body (tabs := tabs) (stream := stream) (by omega) hd hrun
    ⟨sp, hsp⟩ hx hz hm hrc
  have hx14 := gk_xs_len hd2 hrun ⟨sp, hsp⟩
  set args : List E := cap0 ++ [ofK (addressOfIndex ec), gen ^ depth, ofK (addressOfIndex ez),
    tabs, stream] with hargs
  set W := vbgW (ofK (addressOfIndex eL)) (ofK (addressOfIndex eS)) (ofK (addressOfIndex eR))
      (ofK (addressOfIndex eP)) (ofK (addressOfIndex eO)) (ofK (addressOfIndex eB))
      (ofK (addressOfIndex eM)) (ofK (addressOfIndex eV)) with hW
  have hσe : vbgσ rd depth cap0 tabs stream ec ez eL eR eP eO eB eM eV eS =
      B1.Val.ofArgs (ev rd W args vbgEvL) := rfl
  rw [hσe]
  set σ := B1.Val.ofArgs (ev rd W args vbgEvL) with hσ
  have hl : args.length = 10 := by rw [hargs]; simp [hcl]
  obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp vb_chk
  have hG : ∀ s ∈ vbgEvL, GoodS rd vbgS W σ s := by
    have h := (ev_spec rd W vbgEvL args (by rw [hl]; exact hc')).2.2
    rw [hl] at h
    exact h
  obtain ⟨e5, e6, e15, e16, e17, e18, e64, e66, e67, e166, e399, e401, e427, eS17, e88, e91⟩ :=
    vbg_ptrs hσ hG hcl hargs hW
  have g : ∀ a : Atom, vbgEvL.any (fun t ↦ tbStmtsEqb [.atom a] [t]) = true → Good rd vbgS W σ a :=
    fun a h ↦ hG _ (vbg_mem h)
  have mul : ∀ d x y : ℕ, vbgEvL.any (fun t ↦ tbStmtsEqb [.atom (.mul (.n d) (.n x) (.n y))] [t])
      = true → x < d → y < d → σ (.n d) = σ (.n x) * σ (.n y) :=
    fun d x y h hx hy ↦ good_mul (g _ h) hx hy
  have e7 : σ (.n (val% «verify_bus_gkr» "zeta")) = ofK (addressOfIndex ez) := by
    rw [hσ, ev_params rd W (by rw [hl]; exact hc') (by rw [hl]; omega), hargs]; simp [hcl]
  have e8 : σ (.n (val% «verify_bus_gkr» "tabs")) = tabs := by
    rw [hσ, ev_params rd W (by rw [hl]; exact hc') (by rw [hl]; omega), hargs]; simp [hcl]
  have e9 : σ (.n (val% «verify_bus_gkr» "stream")) = stream := by
    rw [hσ, ev_params rd W (by rw [hl]; exact hc') (by rw [hl]; omega), hargs]; simp [hcl]
  have one : ∀ d : ℕ, vbgEvL.any (fun t ↦ tbStmtsEqb [.atom (.const (.n d) (word 1 0))] [t]) =
      true → σ (.n d) = 1 := fun d h ↦ by rw [← tb_word_one]; exact g _ h
  have c424 := one (val% «verify_bus_gkr» "s36#0") (by decide +kernel)
  have c426 := one (val% «verify_bus_gkr» "s36#2") (by decide +kernel)
  -- the tables at `depth`: `depth_odd`, `four_bounds`, `four_rem`
  have tab : ∀ {e : ℕ} {f : ℕ → ℕ}, TbReadsAt rd (ofK (addressOfIndex e))
      ((List.range 33).map fun k ↦ gen ^ f k) →
      LoadHolds rd (ofK (addressOfIndex e) * gen ^ depth) 0 (gen ^ f depth) := by
    intro e f h
    rw [tb_loadHolds_mul_gen_pow, Nat.add_zero]
    have := h depth (by simp; omega)
    simpa using this
  have r167 := good_read (g (.load (.n (val% «verify_bus_gkr» "odd_g")) (.n (val% «verify_bus_gkr» "odd_g~0")) 0) (by decide +kernel)) (by decide +kernel)
    (by rw [e166]; exact tab hO)
  have r400 := good_read (g (.load (.n (val% «verify_bus_gkr» "n_four")) (.n (val% «verify_bus_gkr» "n_four~0")) 0) (by decide +kernel)) (by decide +kernel)
    (by rw [e399]; exact tab hB)
  have r402 := good_read (g (.load (.n (val% «verify_bus_gkr» "rem_g")) (.n (val% «verify_bus_gkr» "rem_g~0")) 0) (by decide +kernel)) (by decide +kernel)
    (by rw [e401]; exact tab hM)
  have c168 : σ (.n (val% «verify_bus_gkr» "start_g~0")) = gen ^ 2 := by
    rw [← tb_word_four]; exact g (.const (.n (val% «verify_bus_gkr» "start_g~0")) (word 4 0)) (by decide +kernel)
  have e169 : σ (.n (val% «verify_bus_gkr» "start_g")) = gen ^ (2 - depth % 2) := by
    have h := g (.mul (.n (val% «verify_bus_gkr» "start_g~0")) (.n (val% «verify_bus_gkr» "start_g")) (.n (val% «verify_bus_gkr» "odd_g"))) (by decide +kernel)
    have hn : ¬ ((V.n (val% «verify_bus_gkr» "start_g")).idx < (V.n (val% «verify_bus_gkr» "start_g~0")).idx ∧ (V.n (val% «verify_bus_gkr» "odd_g")).idx < (V.n (val% «verify_bus_gkr» "start_g~0")).idx) := by
      show ¬ ((val% «verify_bus_gkr» "start_g") < (val% «verify_bus_gkr» "start_g~0") ∧ (val% «verify_bus_gkr» "odd_g") < (val% «verify_bus_gkr» "start_g~0")); omega
    simp only [Good, hn, ↓reduceIte] at h
    rw [h, c168, r167.1]
    have hs : depth % 2 ≤ 2 := by omega
    rw [show (gen : E) ^ 2 = gen ^ (2 - depth % 2) * gen ^ (depth % 2) by
        rw [← pow_add, Nat.sub_add_cancel hs],
      mul_assoc, mul_inv_cancel₀ (gen_pow_ne_zero _), mul_one]
  -- the root-most slot, the last slot and the last row
  have m170 := mul (val% «verify_bus_gkr» "nxt~0") (val% «verify_bus_gkr» "start_g") (val% «verify_bus_gkr» "start_g") (by decide +kernel) (by omega) (by omega)
  have m171 := mul (val% «verify_bus_gkr» "nxt~1") (val% «verify_bus_gkr» "nxt~0") (val% «verify_bus_gkr» "nxt~0") (by decide +kernel) (by omega) (by omega)
  have m172 := mul (val% «verify_bus_gkr» "nxt~2") (val% «verify_bus_gkr» "nxt~1") (val% «verify_bus_gkr» "start_g") (by decide +kernel) (by omega) (by omega)
  have m173 := mul (val% «verify_bus_gkr» "nxt~3") (val% «verify_bus_gkr» "nxt~2") (val% «verify_bus_gkr» "nxt~2") (by decide +kernel) (by omega) (by omega)
  have m174 := mul (val% «verify_bus_gkr» "nxt") (val% «verify_bus_gkr» "layers") (val% «verify_bus_gkr» "nxt~3") (by decide +kernel) (by omega) (by omega)
  have e174 : σ (.n (val% «verify_bus_gkr» "nxt")) = ofK (addressOfIndex eL) * gen ^ (10 * (2 - depth % 2)) := by
    rw [m174, m173, m172, m171, m170, e169, e16, ← pow_add, ← pow_add, ← pow_add, ← pow_add]
    ring_nf
  have m403 := mul (val% «verify_bus_gkr» "n_pairs~0") (val% «verify_bus_gkr» "n_four") (val% «verify_bus_gkr» "n_four") (by decide +kernel) (by omega) (by omega)
  have m404 := mul (val% «verify_bus_gkr» "n_pairs~1") (val% «verify_bus_gkr» "n_pairs~0") (val% «verify_bus_gkr» "n_pairs~0") (by decide +kernel) (by omega) (by omega)
  have m405 := mul (val% «verify_bus_gkr» "n_pairs") (val% «verify_bus_gkr» "n_pairs~1") (val% «verify_bus_gkr» "rem_g") (by decide +kernel) (by omega) (by omega)
  have e405 : σ (.n (val% «verify_bus_gkr» "n_pairs")) = gen ^ ((depth - 1) / 2) := by
    rw [m405, m404, m403, r400.1, r402.1, ← pow_add, ← pow_add, ← pow_add]
    exact congrArg (gen ^ ·) (by omega)
  have m407 := mul (val% «verify_bus_gkr» "last~0") (val% «verify_bus_gkr» "n_pairs") (val% «verify_bus_gkr» "n_pairs") (by decide +kernel) (by omega) (by omega)
  have m408 := mul (val% «verify_bus_gkr» "last~1") (val% «verify_bus_gkr» "last~0") (val% «verify_bus_gkr» "start_g") (by decide +kernel) (by omega) (by omega)
  have m409 := mul (val% «verify_bus_gkr» "last~2") (val% «verify_bus_gkr» "last~1") (val% «verify_bus_gkr» "last~1") (by decide +kernel) (by omega) (by omega)
  have m410 := mul (val% «verify_bus_gkr» "last~3") (val% «verify_bus_gkr» "last~2") (val% «verify_bus_gkr» "last~2") (by decide +kernel) (by omega) (by omega)
  have m411 := mul (val% «verify_bus_gkr» "last~4") (val% «verify_bus_gkr» "last~3") (val% «verify_bus_gkr» "last~1") (by decide +kernel) (by omega) (by omega)
  have m412 := mul (val% «verify_bus_gkr» "last~5") (val% «verify_bus_gkr» "last~4") (val% «verify_bus_gkr» "last~4") (by decide +kernel) (by omega) (by omega)
  have m413 := mul (val% «verify_bus_gkr» "last") (val% «verify_bus_gkr» "layers") (val% «verify_bus_gkr» "last~5") (by decide +kernel) (by omega) (by omega)
  have e408 : σ (.n (val% «verify_bus_gkr» "last~1")) = gen ^ depth := by
    rw [m408, m407, e405, e169, ← pow_add, ← pow_add]
    exact congrArg (gen ^ ·) (by omega)
  have e413 : σ (.n (val% «verify_bus_gkr» "last")) = ofK (addressOfIndex eL) * gen ^ (10 * depth) := by
    rw [m413, m412, m411, m410, m409, e408, e16, ← pow_add, ← pow_add, ← pow_add, ← pow_add]
    ring_nf
  have c415 : σ (.n (val% «verify_bus_gkr» "final_point_row~0")) = gen := by
    rw [← tb_word_gen]; exact g (.const (.n (val% «verify_bus_gkr» "final_point_row~0")) (word 2 0)) (by decide +kernel)
  have m416 := mul (val% «verify_bus_gkr» "final_point_row~1") (val% «verify_bus_gkr» "n_pairs") (val% «verify_bus_gkr» "final_point_row~0") (by decide +kernel) (by omega) (by omega)
  have m417 := mul (val% «verify_bus_gkr» "final_point_row~2") (val% «verify_bus_gkr» "final_point_row~1") (val% «verify_bus_gkr» "final_point_row~1") (by decide +kernel) (by omega) (by omega)
  have m418 := mul (val% «verify_bus_gkr» "final_point_row~3") (val% «verify_bus_gkr» "final_point_row~2") (val% «verify_bus_gkr» "final_point_row~2") (by decide +kernel) (by omega) (by omega)
  have m419 := mul (val% «verify_bus_gkr» "final_point_row~4") (val% «verify_bus_gkr» "final_point_row~3") (val% «verify_bus_gkr» "final_point_row~1") (by decide +kernel) (by omega) (by omega)
  have m420 := mul (val% «verify_bus_gkr» "final_point_row~5") (val% «verify_bus_gkr» "final_point_row~4") (val% «verify_bus_gkr» "final_point_row~4") (by decide +kernel) (by omega) (by omega)
  have m421 := mul (val% «verify_bus_gkr» "final_point_row~6") (val% «verify_bus_gkr» "final_point_row~5") (val% «verify_bus_gkr» "final_point_row~5") (by decide +kernel) (by omega) (by omega)
  have m422 := mul (val% «verify_bus_gkr» "final_point_row~7") (val% «verify_bus_gkr» "final_point_row~6") (val% «verify_bus_gkr» "final_point_row~6") (by decide +kernel) (by omega) (by omega)
  have m423 := mul (val% «verify_bus_gkr» "final_point_row") (val% «verify_bus_gkr» "gkr_pts") (val% «verify_bus_gkr» "final_point_row~7") (by decide +kernel) (by omega) (by omega)
  have e423 : σ (.n (val% «verify_bus_gkr» "final_point_row")) = ofK (addressOfIndex eP) * gen ^ (40 * ((depth - 1) / 2 + 1)) := by
    rw [m423, m422, m421, m420, m419, m418, m417, m416, c415, e405, e18, ← pow_succ]
    ring
  have a425 : σ (.n (val% «verify_bus_gkr» "s36#1")) = σ (.n (val% «verify_bus_gkr» "s36#0")) + σ (.n (val% «verify_bus_gkr» "g_bus_mu")) :=
    g (.add (.n (val% «verify_bus_gkr» "s36#1")) (.n (val% «verify_bus_gkr» "s36#0")) (.n (val% «verify_bus_gkr» "g_bus_mu"))) (by decide +kernel)
  -- `gkr_sizes` at `depth`: the round records' and the point rows' sizes
  have hs0 : LoadHolds rd (ofK (addressOfIndex eS) * gen ^ depth) 0 (gen ^ (7 * gkRecCount depth)) := by
    rw [tb_loadHolds_mul_gen_pow, Nat.add_zero, ← vbgSizesW_lo (by omega),
      List.getD_eq_getElem _ _ (by simp [vbgSizesW]; omega)]
    exact hS depth (by simp [vbgSizesW]; omega)
  have hs33 : LoadHolds rd (ofK (addressOfIndex eS) * gen ^ depth) 33
      (gen ^ ((depth / 2 + 2) * 40)) := by
    rw [tb_loadHolds_mul_gen_pow, ← vbgSizesW_hi (by omega), Nat.add_comm depth 33,
      List.getD_eq_getElem _ _ (by simp [vbgSizesW]; omega)]
    exact hS (33 + depth) (by simp [vbgSizesW]; omega)
  have r89 := good_read (g (.load (.n (val% «verify_bus_gkr» "rounds~1")) (.n (val% «verify_bus_gkr» "rounds~0")) 0) (by decide +kernel))
    (by decide +kernel) (by rw [e88]; exact hs0)
  have r92 := good_read (g (.load (.n (val% «verify_bus_gkr» "gkr_pts~1")) (.n (val% «verify_bus_gkr» "gkr_pts~0")) 33) (by decide +kernel))
    (by decide +kernel) (by rw [e91]; exact hs33)
  refine ⟨fun s hs ↦ ?_, fun d p off hm ↦ ?_, ?_, ?_, hrt, r167.1, r400.1, r402.1, e169, c426,
    e6, e16, e17, e18, e8, e9, by rw [a425, c424, e6]⟩
  · -- the statements
    have hv := vsh_of_holdsList vbgPre vbg_iteOk hh s hs
    have hk := List.all_eq_true.mp vbg_kinds s hs
    simp only [vbgKindB, Bool.or_eq_true] at hk
    rcases hk with (ha | hL') | hZ
    · exact vsh_atomsDeep ha hv
    · have e := tbStmtsEqb_sound hL'
      simp only [List.cons.injEq, and_true] at e
      subst e
      obtain ⟨j, hj, hx, h⟩ := hv
      refine ⟨j, hj, hx, ?_⟩
      have hjo : j = depth % 2 := by
        rw [r167.1, ← gen_pow_eq_ofK] at hx
        simp only [List.length_cons, List.length_nil] at hj
        exact (gen_pow_inj (by omega) (by omega) hx).symm
      subst hjo
      have e : [glcLsN 0, glcLsN 1][depth % 2] = glcLsN (depth % 2) := by
        rcases Nat.mod_two_eq_zero_or_one depth with h0 | h0 <;> simp [h0]
      rw [e] at h ⊢
      simp only [List.map_cons, List.map_nil, e16, e17, e18, r400.1, r402.1, e169, e6, e8, e9]
        at h ⊢
      exact vbg_layers_relIn hd hrun ⟨sp, hsp⟩ hm hReg.x hReg.l hReg.rr hReg.r h
    · have e := tbStmtsEqb_sound hZ
      simp only [List.cons.injEq, and_true] at e
      subst e
      refine ⟨hv.1, fun hne ↦ ?_⟩
      obtain ⟨n, h⟩ := hv.2 hne
      simp only [List.map_cons, List.map_nil, c426, e6, e7, e423] at h ⊢
      rw [show (1 : E) = gen ^ 0 from (pow_zero _).symm] at h ⊢
      rw [tb_ofK_gpow_mul] at h ⊢
      exact vbz_relIn (ptrIn_ofK hReg.z) (ptrIn_ofK fun i hi ↦ by
        rw [Nat.add_assoc]; exact hReg.r _ (by omega)) n 0 (by omega) h
  · -- the loads
    obtain ⟨hp, hcls⟩ := vbg_load_cls hm
    rw [hp]
    rcases hcls with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨(h1 | h1) | h1, h2⟩ |
      ⟨(h1 | h1) | h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1]
    · exact ⟨(ofK (addressOfIndex ec), xs.length), List.mem_cons_self, 0,
        by rw [e5]; simp, by omega⟩
    · exact ⟨(ofK (addressOfIndex eL), 10 * (depth + 2)), by simp, 10 * (2 - depth % 2), e174,
        by omega⟩
    · exact ⟨(ofK (addressOfIndex eP), (depth / 2 + 2) * 40), by simp, 0, by rw [e18]; simp,
        by omega⟩
    · exact ⟨(ofK (addressOfIndex eO), 33), by simp, 0, by rw [e64]; simp, by omega⟩
    · exact ⟨(ofK (addressOfIndex eB), 33), by simp, 0, by rw [e66]; simp, by omega⟩
    · exact ⟨(ofK (addressOfIndex eM), 33), by simp, 0, by rw [e67]; simp, by omega⟩
    · exact ⟨(ofK (addressOfIndex eO), 33), by simp, depth, e166, by omega⟩
    · exact ⟨(ofK (addressOfIndex eB), 33), by simp, depth, e399, by omega⟩
    · exact ⟨(ofK (addressOfIndex eM), 33), by simp, depth, e401, by omega⟩
    · exact ⟨(ofK (addressOfIndex eL), 10 * (depth + 2)), by simp, 10 * depth, e413, by omega⟩
    · exact ⟨(ofK (addressOfIndex eV), 3), by simp, 0, by rw [e427]; simp, by omega⟩
    · exact ⟨(ofK (addressOfIndex eS), 66), by simp, 0, by rw [eS17]; simp, by omega⟩
    · exact ⟨(ofK (addressOfIndex eS), 66), by simp, depth, e88, by omega⟩
    · exact ⟨(ofK (addressOfIndex eS), 66), by simp, depth, e91, by omega⟩
  · -- the sizes
    have hgk : gkRecCount depth ≤ 1000 := by
      have : ∀ d ≤ 32, gkRecCount d ≤ 1000 := by decide
      exact this _ hd
    rw [vbg_allocs]
    simp only [List.map_cons, List.map_nil, Sum.elim_inr, Sum.elim_inl, id, e15, r89.1, r92.1,
      vbgSizes]
    rw [gen_pow_eq_ofK, logG_spec (by omega), gen_pow_eq_ofK, logG_spec (by omega),
      gen_pow_eq_ofK, logG_spec (by omega)]
  · -- the bases
    rw [vbg_allocs]
    simp only [List.map_cons, List.map_nil, e16, eS17, e17, e18, e64, e66, e67, e427]

theorem vbgLayersW_length {depth : ℕ} {cap0 xs : List E} {cur : E}
    (hcl : cap0.length = 5) :
    (vbgLayersW depth cap0 xs cur).length = 10 * (depth + 2) := by
  rw [vbgLayersW, List.length_flatMap]
  have : (List.range (depth + 2)).map (fun l ↦ (vbgLayBlock depth cap0 xs cur l).length) =
      List.replicate (depth + 2) 10 := by
    apply List.ext_getElem (by simp)
    intro i _ _
    simp [vbgLayBlock_length hcl]
  rw [this, List.sum_replicate, smul_eq_mul, mul_comm]


variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- `verify_bus_gkr`'s buffers' first words at `fp`: layers, `gkr_sizes`, rounds, rows,
`depth_odd`, `four_bounds`, `four_rem`, the values. -/
def vbgEL (fs : String → ℕ) (fp : ℕ) : ℕ := fp + fs "verify_bus_gkr"
def vbgES (fs : String → ℕ) (depth fp : ℕ) : ℕ := vbgEL fs fp + 10 * (depth + 2)
def vbgER (fs : String → ℕ) (depth fp : ℕ) : ℕ := vbgES fs depth fp + 66
def vbgEP (fs : String → ℕ) (depth fp : ℕ) : ℕ := vbgER fs depth fp + 7 * gkRecCount depth
def vbgEO (fs : String → ℕ) (depth fp : ℕ) : ℕ := vbgEP fs depth fp + (depth / 2 + 2) * 40
def vbgEB (fs : String → ℕ) (depth fp : ℕ) : ℕ := vbgEO fs depth fp + 33
def vbgEM (fs : String → ℕ) (depth fp : ℕ) : ℕ := vbgEB fs depth fp + 33
def vbgEV (fs : String → ℕ) (depth fp : ℕ) : ℕ := vbgEM fs depth fp + 33

/-- `verify_bus_gkr`'s layout at `fp`: the cursor's words, the point, the buffers. -/
noncomputable def vbgL (fs : String → ℕ) (depth : ℕ) (cap0 xs point : List E) (ec ez fp : ℕ) :
    List (ℕ × List E) :=
  flatL "verify_bus_gkr" [(ec, xs), (ez, point)] (vbgSizes depth)
    (fun _ ↦ vbgOwnW depth cap0 xs (ofK (addressOfIndex ec))) fs fp

/-- The buffers `verify_bus_gkr` loads from, at `fp`. -/
noncomputable def vbgBufs (fs : String → ℕ) (depth : ℕ) (xs : List E) (ec fp : ℕ) : List (E × ℕ) :=
  [(ofK (addressOfIndex ec), xs.length), (ofK (addressOfIndex (vbgEL fs fp)), 10 * (depth + 2)),
    (ofK (addressOfIndex (vbgES fs depth fp)), 66),
    (ofK (addressOfIndex (vbgER fs depth fp)), 7 * gkRecCount depth),
    (ofK (addressOfIndex (vbgEP fs depth fp)), (depth / 2 + 2) * 40),
    (ofK (addressOfIndex (vbgEO fs depth fp)), 33), (ofK (addressOfIndex (vbgEB fs depth fp)), 33),
    (ofK (addressOfIndex (vbgEM fs depth fp)), 33), (ofK (addressOfIndex (vbgEV fs depth fp)), 3)]

theorem vbg_bufL (fs : String → ℕ) (depth : ℕ) (cap0 xs : List E) (cur : E) (fp : ℕ) :
    bufL (fp + fs "verify_bus_gkr") (vbgSizes depth)
      (vbgOwnW depth cap0 xs cur) =
      [(vbgEL fs fp, vbgLayersW depth cap0 xs cur), (vbgES fs depth fp, vbgSizesW),
        (vbgER fs depth fp, vbgRoundsW depth cap0 xs cur),
        (vbgEP fs depth fp, vbgRowsW depth cap0 xs),
        (vbgEO fs depth fp, vbgOddW), (vbgEB fs depth fp, vbgBndW),
        (vbgEM fs depth fp, vbgRemW),
        (vbgEV fs depth fp, vbgValsW depth cap0 xs)] := by
  simp [bufL, bases, vbgSizes, vbgOwnW, vbgEL, vbgES, vbgER, vbgEP, vbgEO, vbgEB, vbgEM, vbgEV,
    Nat.add_assoc]

/-- **What `verify_bus_gkr`'s placed lift needs**: its buffers' honest words fit their sizes, the
buffers it loads from lie in its layout, and on every memory defined below `2^κ` holding the layout
its honest valuation runs (`vbg_run` at the bump allocator's bases), its calls' values
(`VbgVals`) and its buffers' words (`vbgLay`). -/
theorem vbg_lift_facts {κ depth : ℕ} (hd2 : 2 ≤ depth) (hd : depth ≤ 32) (hκ : 6 ≤ κ)
    {cap0 xs : List E} {r : E × List E × List E} {cap' : List E}
    (hrun : RunsTo (gkrPhase depth) ⟨cap0, []⟩ xs r ⟨cap', []⟩)
    (hc : ∃ sp, (⟨cap0, []⟩ : Fs).Carries sp) (tabs stream : E) (ec ez : ℕ) :
    (∀ _fp : ℕ, List.Forall₂ (fun c s => c.length ≤ s)
      (vbgOwnW depth cap0 xs (ofK (addressOfIndex ec))) (vbgSizes depth)) ∧
    (∀ fp, ∀ q ∈ vbgBufs fs depth xs ec fp, ∃ b, q.1 = ofK (addressOfIndex b) ∧
      ∀ i < q.2, RegionL (vbgL fs depth cap0 xs r.2.1 ec ez fp) (b + i)) ∧
    (∀ fp rd, LowDef κ rd → MemL rd (vbgL fs depth cap0 xs r.2.1 ec ez fp) →
      let σ := vbgσ rd depth cap0 tabs stream ec ez (vbgEL fs fp) (vbgER fs depth fp)
        (vbgEP fs depth fp) (vbgEO fs depth fp) (vbgEB fs depth fp) (vbgEM fs depth fp)
        (vbgEV fs depth fp) (vbgES fs depth fp)
      ((∀ s ∈ vbgPre, VSH (coreProgram.RelIn rd (RegionL (vbgL fs depth cap0 xs r.2.1 ec ez fp)))
          rd σ s) ∧
        LoadsInBuf σ (vbgBufs fs depth xs ec fp) vbgEvL ∧
        (vbgPre.filterMap Main.Stmt.allocSz).map (fun x => x.2.elim id fun s => logG (σ s)) =
          vbgSizes depth ∧
        ((vbgPre.filterMap Main.Stmt.allocSz).map Prod.fst).map σ =
          (bases (fp + fs "verify_bus_gkr") (vbgSizes depth)).map (fun b
              => ofK (addressOfIndex b)) ∧
        vbgRets.map σ = cap' ++ [ofK (addressOfIndex ec) * gen ^ xs.length,
          ofK (addressOfIndex (vbgEV fs depth fp))]) ∧
      VbgVals σ depth (vbgEL fs fp) (vbgER fs depth fp) (vbgEP fs depth fp) tabs stream ∧
      MemLay rd (vbgLay depth cap0 xs (ofK (addressOfIndex ec)) (vbgEL fs fp) (vbgER fs depth fp)
        (vbgEP fs depth fp) (vbgEO fs depth fp) (vbgEB fs depth fp) (vbgEM fs depth fp)
        (vbgEV fs depth fp) (vbgES fs depth fp))) := by
  have hcl : cap0.length = 5 := by
    obtain ⟨sp, hsp⟩ := hc
    have hsc : capOf sp.state = cap0 := hsp.1
    rw [← hsc]; simp [capOf]
  have hpl : ∀ j ≤ depth / 2, (gkSl cap0 xs (depth % 2) j).2.1.point.length = 2 * j + depth % 2 := by
    obtain ⟨-, -, -, hsteps, -⟩ := gk_walk hrun hc
    exact gkSl_point_len (gkSl0_point_len cap0 xs (depth % 2) (by omega)) fun j hj ↦ (hsteps j hj).1
  have hrp : r.2.1.length = depth := by
    obtain ⟨-, -, -, -, -, -, hr, hpl'⟩ := gk_walk hrun hc
    rw [hr]; exact hpl'
  have hvl : (vbgValsW depth cap0 xs).length = 3 :=
    (gkSl_inv (xs := xs) (sh := depth % 2) hcl (depth / 2)).2.1
  have hlr : (vbgRoundsW depth cap0 xs (ofK (addressOfIndex ec))).length = 7 * gkRecCount depth :=
    vbgRoundsW_length hd
  have hlp : (vbgRowsW depth cap0 xs).length = (depth / 2 + 2) * 40 := vbgRowsW_length hd hpl
  have hls : vbgSizesW.length = 66 := by simp [vbgSizesW]
  have hown : ∀ _fp : ℕ, List.Forall₂ (fun c s => c.length ≤ s)
      (vbgOwnW depth cap0 xs (ofK (addressOfIndex ec))) (vbgSizes depth) := by
    intro fp
    simp only [vbgOwnW, vbgSizes, List.forall₂_cons, List.Forall₂.nil, and_true]
    exact ⟨by rw [vbgLayersW_length hcl], by rw [hls], by rw [hlr], by rw [hlp],
      by simp [vbgOddW], by simp [vbgBndW], by simp [vbgRemW], by rw [hvl]⟩
  have hreg : ∀ fp, vbgL fs depth cap0 xs r.2.1 ec ez fp = [(ec, xs), (ez, r.2.1)] ++
      [(vbgEL fs fp, vbgLayersW depth cap0 xs (ofK (addressOfIndex ec))), (vbgES fs depth fp, vbgSizesW),
        (vbgER fs depth fp, vbgRoundsW depth cap0 xs (ofK (addressOfIndex ec))),
        (vbgEP fs depth fp, vbgRowsW depth cap0 xs),
        (vbgEO fs depth fp, vbgOddW), (vbgEB fs depth fp, vbgBndW),
        (vbgEM fs depth fp, vbgRemW),
        (vbgEV fs depth fp, vbgValsW depth cap0 xs)] := fun fp ↦ by
    rw [← vbg_bufL]; rfl
  have own : ∀ fp b (ws : List E), (b, ws) ∈
      [(vbgEL fs fp, vbgLayersW depth cap0 xs (ofK (addressOfIndex ec))), (vbgES fs depth fp, vbgSizesW),
        (vbgER fs depth fp, vbgRoundsW depth cap0 xs (ofK (addressOfIndex ec))),
        (vbgEP fs depth fp, vbgRowsW depth cap0 xs),
        (vbgEO fs depth fp, vbgOddW), (vbgEB fs depth fp, vbgBndW),
        (vbgEM fs depth fp, vbgRemW),
        (vbgEV fs depth fp, vbgValsW depth cap0 xs)] →
      ∀ i < ws.length, RegionL (vbgL fs depth cap0 xs r.2.1 ec ez fp) (b + i) :=
    fun fp b ws hm i hi ↦ by
      rw [hreg]; exact regionL_append_right ⟨(b, ws), hm, by omega, by simpa using hi⟩
  refine ⟨hown, ?_, ?_⟩
  · -- the buffers lie in the layout
    intro fp q hq
    simp only [vbgBufs, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨ec, rfl, fun i hi ↦ by
        rw [hreg]; exact regionL_append_left ⟨(ec, xs), by simp, by omega, by simpa using hi⟩⟩
    · exact ⟨_, rfl, fun i hi ↦ own fp (vbgEL fs fp) (vbgLayersW depth cap0 xs (ofK (addressOfIndex ec))) (by simp) i (by rw [vbgLayersW_length hcl]; exact hi)⟩
    · exact ⟨_, rfl, fun i hi ↦ own fp (vbgES fs depth fp) vbgSizesW (by simp) i (by rw [hls]; exact hi)⟩
    · exact ⟨_, rfl, fun i hi ↦ own fp (vbgER fs depth fp) (vbgRoundsW depth cap0 xs (ofK (addressOfIndex ec))) (by simp) i (by rw [hlr]; exact hi)⟩
    · exact ⟨_, rfl, fun i hi ↦ own fp (vbgEP fs depth fp) (vbgRowsW depth cap0 xs) (by simp) i (by rw [hlp]; exact hi)⟩
    · exact ⟨_, rfl, fun i hi ↦ own fp (vbgEO fs depth fp) vbgOddW (by simp) i (by simpa [vbgOddW] using hi)⟩
    · exact ⟨_, rfl, fun i hi ↦ own fp (vbgEB fs depth fp) vbgBndW (by simp) i (by simpa [vbgBndW] using hi)⟩
    · exact ⟨_, rfl, fun i hi ↦ own fp (vbgEM fs depth fp) vbgRemW (by simp) i (by simpa [vbgRemW] using hi)⟩
    · exact ⟨_, rfl, fun i hi ↦ own fp (vbgEV fs depth fp) (vbgValsW depth cap0 xs) (by simp) i (by rw [hvl]; exact hi)⟩
  · -- the run
    intro fp rd hlow hL
    have hL' := hL
    rw [hreg] at hL'
    obtain ⟨hLin, hB⟩ := Main.memL_append.mp hL'
    have hx : TbReadsAt rd (ofK (addressOfIndex ec)) xs := hLin (ec, xs) (by simp)
    have hz : TbReadsAt rd (ofK (addressOfIndex ez)) r.2.1 := hLin (ez, r.2.1) (by simp)
    have hw : ∀ b ws, (b, ws) ∈ [(vbgEL fs fp, vbgLayersW depth cap0 xs (ofK (addressOfIndex ec))), (vbgES fs depth fp, vbgSizesW), (vbgER fs depth fp, vbgRoundsW depth cap0 xs (ofK (addressOfIndex ec))),
        (vbgEP fs depth fp, vbgRowsW depth cap0 xs),
        (vbgEO fs depth fp, vbgOddW), (vbgEB fs depth fp, vbgBndW),
        (vbgEM fs depth fp, vbgRemW),
        (vbgEV fs depth fp, vbgValsW depth cap0 xs)] → TbReadsAt rd (ofK (addressOfIndex b)) ws :=
      fun b ws h ↦ hB (b, ws) h
    have hReg : VbgR (RegionL (vbgL fs depth cap0 xs r.2.1 ec ez fp)) depth xs ec ez
        (vbgEL fs fp) (vbgER fs depth fp) (vbgEP fs depth fp) :=
      ⟨fun i hi ↦ by
          rw [hreg]; exact regionL_append_left ⟨(ez, r.2.1), by simp, by simp, by rw [hrp]; omega⟩,
        fun i hi ↦ own fp (vbgEP fs depth fp) (vbgRowsW depth cap0 xs) (by simp) i (by rw [hlp]; exact hi),
        fun i hi ↦ by
          rw [hreg]; exact regionL_append_left ⟨(ec, xs), by simp, by simp, by simpa using hi⟩,
        fun i hi ↦ own fp (vbgEL fs fp) (vbgLayersW depth cap0 xs (ofK (addressOfIndex ec))) (by simp) i (by rw [vbgLayersW_length hcl]; exact hi),
        fun i hi ↦ own fp (vbgER fs depth fp) (vbgRoundsW depth cap0 xs (ofK (addressOfIndex ec))) (by simp) i (by rw [hlr]; exact hi)⟩
    have hLw := hw (vbgEL fs fp) (vbgLayersW depth cap0 xs (ofK (addressOfIndex ec))) (by simp)
    have hRw := hw (vbgER fs depth fp) (vbgRoundsW depth cap0 xs (ofK (addressOfIndex ec))) (by simp)
    have hPw := hw (vbgEP fs depth fp) (vbgRowsW depth cap0 xs) (by simp)
    have hOw := hw (vbgEO fs depth fp) vbgOddW (by simp)
    have hBw := hw (vbgEB fs depth fp) vbgBndW (by simp)
    have hMw := hw (vbgEM fs depth fp) vbgRemW (by simp)
    have hVw := hw (vbgEV fs depth fp) (vbgValsW depth cap0 xs) (by simp)
    have hSw := hw (vbgES fs depth fp) vbgSizesW (by simp)
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := vbg_run (tabs := tabs) (stream := stream) hd2 hd hκ hrun hc
      hlow hx hz hLw hRw hPw hOw hBw hMw hVw hSw hReg
    refine ⟨⟨h1, h2, h3, h4.trans ?_, h5⟩, h6,
      vbg_memLay hd hcl hpl hLw hRw hPw hOw hBw hMw hVw hSw⟩
    simp [bases, vbgSizes, vbgEL, vbgES, vbgER, vbgEP, vbgEO, vbgEB, vbgEM, vbgEV, Nat.add_assoc]

/-- What `verify_bus_gkr` returns: the capacity `cap'`, the cursor `cur` and a pointer to a buffer
of its returned layout holding the values `vals`. -/
def VbgOut (cap' : List E) (cur : E) (vals : List E) (rets : List E) (Lout : List (ℕ × List E)) :
    Prop :=
  ∃ b, rets = cap' ++ [cur, ofK (addressOfIndex b)] ∧ (b, vals) ∈ Lout

/-- **`verify_bus_gkr` is complete, placed** (TRIAGE G #43): at `2 ≤ depth ≤ 32`, on memories
defined below `2^κ`, `κ ≥ 6`, an accepting run of `gkrPhase depth` from a carried capacity `cap0`
reading the words `xs` at the cursor `g^ec`, the run's point at `zeta = g^ez`, its eight buffers
at the bump allocator's positions holding their honest words (`vbgOwnW`), returned. It returns
the run's capacity, the cursor past `xs` and a returned buffer holding the run's values. -/
theorem verify_bus_gkr_completeAt {κ depth : ℕ} (hd2 : 2 ≤ depth) (hd : depth ≤ 32) (hκ : 6 ≤ κ)
    {cap0 xs : List E} {r : E × List E × List E} {cap' : List E}
    (hrun : RunsTo (gkrPhase depth) ⟨cap0, []⟩ xs r ⟨cap', []⟩)
    (hc : ∃ sp, (⟨cap0, []⟩ : Fs).Carries sp) (tabs stream : E) (ec ez : ℕ) :
    CompleteAtD fs cert κ "verify_bus_gkr" [(ec, xs), (ez, r.2.1)]
      (cap0 ++ [ofK (addressOfIndex ec), gen ^ depth, ofK (addressOfIndex ez), tabs, stream])
      (VbgOut cap' (ofK (addressOfIndex ec) * gen ^ xs.length) r.2.2) := by
  have hcl : cap0.length = 5 := by
    obtain ⟨sp, hsp⟩ := hc
    have hsc : capOf sp.state = cap0 := hsp.1
    rw [← hsc]; simp [capOf]
  have hvals : vbgValsW depth cap0 xs = r.2.2 := by
    obtain ⟨-, -, -, -, -, -, hr, -⟩ := gk_walk hrun hc
    rw [hr]; rfl
  obtain ⟨hown, hbufs, hfacts⟩ := vbg_lift_facts (fs := fs) hd2 hd hκ hrun hc tabs stream ec ez
  exact flat_completeAtOut vbgFlat [(ec, xs), (ez, r.2.1)] _
    (fun fp ↦ cap' ++ [ofK (addressOfIndex ec) * gen ^ xs.length,
      ofK (addressOfIndex (vbgEV fs depth fp))]) _ (by simp [vbgFlat, hcl]) (vbgSizes depth)
    (fun _ ↦ vbgOwnW depth cap0 xs (ofK (addressOfIndex ec))) hown
    (fun fp ↦ ⟨vbgEV fs depth fp, rfl, by
      rw [show fp + fs vbgFlat.name = fp + fs "verify_bus_gkr" from rfl, vbg_bufL, ← hvals]
      simp⟩)
    (fun fp ↦ vbgW (ofK (addressOfIndex (vbgEL fs fp))) (ofK (addressOfIndex (vbgES fs depth fp)))
      (ofK (addressOfIndex (vbgER fs depth fp))) (ofK (addressOfIndex (vbgEP fs depth fp)))
      (ofK (addressOfIndex (vbgEO fs depth fp))) (ofK (addressOfIndex (vbgEB fs depth fp)))
      (ofK (addressOfIndex (vbgEM fs depth fp))) (ofK (addressOfIndex (vbgEV fs depth fp))))
    (vbgBufs fs depth xs ec) hbufs (fun fp rd hlow hL ↦ (hfacts fp rd hlow hL).1)

end
end LeanVM.Guest.B1.Tables
