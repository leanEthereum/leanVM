/-
  LeanVM.Guest.B1.Gkr.VbgAt

  `verify_bus_gkr` is complete in the uniform placed form (`CompleteAtD`).
-/

module

public import LeanVM.Guest.B1.Gkr.VbgLoads
public import LeanVM.Guest.B1.Gkr.VbgL7
public import LeanVM.Guest.B1.Tables.Kids.Loop8

/-!
# `verify_bus_gkr`, placed (TRIAGE G #43)

`vbg_run`: on a memory defined below `2^κ` (`κ ≥ 6`, the range check of `g^depth`) holding the
cursor's words, the point at `zeta` and the six buffers whole (`vbgOwnW`), the honest valuation
(`vbgFlat.σ`, the allocations answered by the buffers' pointers) satisfies every statement with
its calls by relations loading from a region `R` holding the cursor's words, the point and the
buffers, its loads land inside the buffers (`vbg_loadOk`, `vbg_ptrs`), its allocations are the
buffers and it returns the accepting run's capacity, cursor and values. `__loop7`'s relation
loads from `R` (`loop8_relIn`), and `__loop6`'s (`vbg_loop7_relIn`).

`verify_bus_gkr_completeAt`: `flat_completeAt` for `vbgFlat`, the buffers at the bump allocator's
positions from `fp + fs "verify_bus_gkr"`.
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

/-- `__loop6`'s call. -/
def vbgCall7 : Stmt :=
  .callIf (.n 312) "__loop6" [.n 313, .n 315, .n 66, .n 6, .n 15, .n 16, .n 56]

/-- `__loop7`'s call. -/
def vbgCall8 : Stmt := .callIf (.n 325) "__loop7" [.n 326, .n 6, .n 7, .n 323]

/-- Every statement is an atom, an `ite` of atoms, or one of the two calls. -/
def vbgKindB (s : Stmt) : Bool :=
  atomsDeep s || tbStmtsEqb [s] [vbgCall7] || tbStmtsEqb [s] [vbgCall8]

theorem vbg_kinds : vbgPre.all vbgKindB = true := by decide +kernel

theorem vbg_allocs : vbgPre.filterMap Main.Stmt.allocSz = [(.n 15, .inr (.n 14)),
    (.n 16, .inl 6034), (.n 17, .inl 1640), (.n 56, .inl 8), (.n 65, .inl 33),
    (.n 66, .inl 33)] := by
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

/-- The cursor's words reach `8`: two roots and the first step. -/
theorem gk_xs_len {depth : ℕ} (hd1 : 1 ≤ depth) {cap0 xs : List E} {r : E × List E × List E}
    {cap' : List E} (hrun : RunsTo (gkrPhase depth) ⟨cap0, []⟩ xs r ⟨cap', []⟩)
    (hc : ∃ sp, (⟨cap0, []⟩ : Fs).Carries sp) : 8 ≤ xs.length := by
  obtain ⟨-, hx2, hodd, hsteps, -, -, -, -⟩ := gk_walk hrun hc
  rcases Nat.mod_two_eq_zero_or_one depth with h0 | h1
  · obtain ⟨hok, hdr⟩ := hsteps 0 (by omega)
    have hpl0 := gkSl0_point_len cap0 xs (depth % 2) (by omega)
    have hl := gkStepD_xs_length hok
    have h02 : (gkSl cap0 xs (depth % 2) 0).2.2 = 2 := by rw [gkSl0_off]; simp [h0]
    have h1' : (gkSl cap0 xs (depth % 2) 1).2.2 = 14 := by
      show (gkSl cap0 xs (depth % 2) 0).2.2 + 4 * (2 * 0 + depth % 2) + 12 = 14
      rw [h02, h0]
    rw [h02, h1'] at hdr
    have := tb_drop_le hdr (by rw [hl, hpl0, h0]; norm_num) (by omega)
    omega
  · obtain ⟨hok, hdr⟩ := hodd h1
    have h6 : (gkOdd xs).xs.length = 6 := by rw [gkStepD_xs_length hok]; rfl
    have := tb_drop_le hdr (by rw [h6]) (by omega)
    omega

theorem vbg_load_cls {d p : V} {off : ℕ} (hm : Stmt.atom (.load d p off) ∈ vbgEvL) :
    p = .n p.idx ∧ ((p.idx = 5 ∧ off < 2) ∨ (p.idx = 15 ∧ off < 34) ∨ (p.idx = 56 ∧ off < 8) ∨
      ((p.idx = 65 ∨ p.idx = 66) ∧ off < 33) ∨ (p.idx = 133 ∧ off = 0) ∨
      (p.idx = 171 ∧ off < 6) ∨ (p.idx = 181 ∧ off = 0) ∨ ((p.idx = 310 ∨ p.idx = 314) ∧ off = 0) ∨
      (p.idx = 321 ∧ off < 10)) := by
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

/-- The honest valuation of `verify_bus_gkr` on its buffers at `g^eL .. g^eD`, the cursor at
`g^ec`, `zeta` at `g^ez`. -/
noncomputable def vbgσ (rd : Reader) (depth : ℕ) (cap0 : List E) (ec ez eL eR eP eK ePa eD : ℕ) :
    Val :=
  vbgFlat.σ rd (vbgW (ofK (addressOfIndex eL)) (ofK (addressOfIndex eR)) (ofK (addressOfIndex eP))
      (ofK (addressOfIndex eK)) (ofK (addressOfIndex ePa)) (ofK (addressOfIndex eD)))
    (cap0 ++ [ofK (addressOfIndex ec), gen ^ depth, ofK (addressOfIndex ez)])

/-- The values the calls of `__loop6` and `__loop7` start and end at, and `__loop6`'s buffers. -/
def VbgVals (σ : Val) (depth eL eR eK eD : ℕ) : Prop :=
  σ (.n 313) = 1 ∧ σ (.n 315) = gen ^ (depth / 2) ∧ σ (.n 326) = 1 ∧ σ (.n 6) = gen ^ depth ∧
    σ (.n 66) = ofK (addressOfIndex eD) ∧ σ (.n 15) = ofK (addressOfIndex eL) ∧ σ (.n 16) = ofK
        (addressOfIndex eR) ∧ σ (.n 56) = ofK (addressOfIndex eK) ∧
    σ (.n 312) = 1 + gen ^ (depth / 2)

/-- **`verify_bus_gkr`'s honest valuation on a memory holding its words**: every statement holds,
its calls loading from `R`; its loads land inside its buffers; its allocations are the buffers; it
returns the accepting run's capacity, cursor and values. -/
theorem vbg_run {depth κ : ℕ} (hd1 : 1 ≤ depth) (hd : depth ≤ 32) (hκ : 6 ≤ κ)
    {cap0 xs : List E} {r : E × List E × List E} {cap' : List E}
    (hrun : RunsTo (gkrPhase depth) ⟨cap0, []⟩ xs r ⟨cap', []⟩)
    (hc : ∃ sp, (⟨cap0, []⟩ : Fs).Carries sp) {ec ez eL eR eP eK ePa eD : ℕ} {rd : Reader}
    {R : ℕ → Prop} (hlow : LowDef κ rd) (hx : TbReadsAt rd (ofK (addressOfIndex ec)) xs)
    (hz : TbReadsAt rd (ofK (addressOfIndex ez)) r.2.1)
    (hL : TbReadsAt rd (ofK (addressOfIndex eL)) (vbgLayersW depth cap0 xs (ofK (addressOfIndex
        ec)) eP))
    (hR : TbReadsAt rd (ofK (addressOfIndex eR)) (vbgRoundsW depth cap0 xs (ofK
        (addressOfIndex ec))))
    (hP : TbReadsAt rd (ofK (addressOfIndex eP)) (vbgRowsW depth cap0 xs))
    (hK : TbReadsAt rd (ofK (addressOfIndex eK)) kmnWords)
    (hPa : TbReadsAt rd (ofK (addressOfIndex ePa)) vbgPairsW) (hD : TbReadsAt rd (ofK
        (addressOfIndex eD)) vbgDshW)
    (hRz : ∀ i < depth, R (ez + i)) (hRr : ∀ i < 1640, R (eP + i))
    (hRx : ∀ i < xs.length, R (ec + i)) (hRL : ∀ i < 17 * (depth + 2), R (eL + i))
    (hRR : ∀ i < 6034, R (eR + i)) (hRK : ∀ i < 8, R (eK + i)) (hRD : ∀ i < 33, R (eD + i)) :
    (∀ s ∈ vbgPre, VSH (coreProgram.RelIn rd R) rd (vbgσ rd depth cap0 ec ez eL eR eP eK ePa eD)
      s) ∧
    LoadsInBuf (vbgσ rd depth cap0 ec ez eL eR eP eK ePa eD)
      [(ofK (addressOfIndex ec), xs.length), (ofK (addressOfIndex eL), 17 * (depth + 2)), (ofK
          (addressOfIndex eR), 6034),
        (ofK (addressOfIndex eP), 1640), (ofK (addressOfIndex eK), 8),
        (ofK (addressOfIndex ePa), 33), (ofK (addressOfIndex eD), 33)] vbgEvL ∧
    (vbgPre.filterMap Main.Stmt.allocSz).map
      (fun x => x.2.elim id fun s => logG (vbgσ rd depth cap0 ec ez eL eR eP eK ePa eD s)) =
        vbgSizes depth ∧
    ((vbgPre.filterMap Main.Stmt.allocSz).map Prod.fst).map
        (vbgσ rd depth cap0 ec ez eL eR eP eK ePa eD) =
      [ofK (addressOfIndex eL), ofK (addressOfIndex eR), ofK (addressOfIndex eP),
        ofK (addressOfIndex eK), ofK (addressOfIndex ePa), ofK (addressOfIndex eD)] ∧
    vbgRets.map (vbgσ rd depth cap0 ec ez eL eR eP eK ePa eD) =
      cap' ++ [ofK (addressOfIndex ec) * gen ^ xs.length] ++ r.2.2 ∧
    VbgVals (vbgσ rd depth cap0 ec ez eL eR eP eK ePa eD) depth eL eR eK eD := by
  obtain ⟨hcnt, hx2, hodd, hsteps, hend, hsF, hr, hplm⟩ := gk_walk hrun hc
  obtain ⟨sp, hsp⟩ := hc
  have hsc : capOf sp.state = cap0 := hsp.1
  have hcl : cap0.length = 5 := by rw [← hsc]; simp [capOf]
  have hcan : AllCanonical cap0 := by rw [← hsc]; exact tb_capOf_canonical _
  have hpl : ∀ j ≤ depth / 2, (gkSl cap0 xs (depth % 2) j).2.1.point.length = 2 * j + depth % 2 :=
    gkSl_point_len (gkSl0_point_len cap0 xs (depth % 2) (by omega)) fun j hj ↦ (hsteps j hj).1
  have hm := vbg_memLay (eL := eL) (eR := eR) (eP := eP) (eK := eK) (ePa := ePa) (eD := eD) hd hcl
    hcan hpl hL hR hP hK hPa hD
  have h64 : (64 : ℕ) ≤ 2 ^ κ := by
    calc (64 : ℕ) = 2 ^ 6 := by norm_num
      _ ≤ 2 ^ κ := Nat.pow_le_pow_right (by norm_num) hκ
  have hrc : (rd (addressOfIndex depth)).isSome = true ∧ (rd (addressOfIndex (32 - depth))).isSome =
      true :=
    ⟨hlow depth (by omega), hlow (32 - depth) (by omega)⟩
  obtain ⟨hh, hrt⟩ := verify_bus_gkr_body hd1 hd hrun ⟨sp, hsp⟩ hx hz hm hrc
  have hx8 := gk_xs_len hd1 hrun ⟨sp, hsp⟩
  set args : List E := cap0 ++ [ofK (addressOfIndex ec), gen ^ depth, ofK (addressOfIndex ez)]
      with hargs
  set W := vbgW (ofK (addressOfIndex eL)) (ofK (addressOfIndex eR)) (ofK (addressOfIndex eP)) (ofK
      (addressOfIndex eK)) (ofK (addressOfIndex ePa)) (ofK (addressOfIndex eD))
    with hW
  have hσe : vbgσ rd depth cap0 ec ez eL eR eP eK ePa eD = B1.Val.ofArgs (ev rd W args vbgEvL) :=
    rfl
  rw [hσe]
  set σ := B1.Val.ofArgs (ev rd W args vbgEvL) with hσ
  have hl : args.length = 8 := by rw [hargs]; simp [hcl]
  obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp vb_chk
  have hG : ∀ s ∈ vbgEvL, GoodS rd vbgS W σ s := by
    have h := (ev_spec rd W vbgEvL args (by rw [hl]; exact hc')).2.2
    rw [hl] at h
    exact h
  -- the level-0 slot's cursor and row
  have hLb := tbReadsAt_flatMap_eq (w := 17) _ (depth + 2)
    (fun c _ ↦ vbgLayBlock_length hcl hcan c) hL
  have hb0 := hLb 0 (by omega)
  simp only [Nat.mul_zero, pow_zero, mul_one] at hb0
  obtain ⟨w5, w9⟩ := vbgLayBlock0 (depth := depth) (xs := xs) (cur := ofK (addressOfIndex ec))
      (eP := eP)
    hcl hcan
  have h5 : LoadHolds rd (ofK (addressOfIndex eL)) 5 (ofK (addressOfIndex ec) * gen ^ 2) := by
    have := hb0 5 (by rw [vbgLayBlock_length hcl hcan]; omega)
    rwa [← List.getD_eq_getElem _ 0, w5] at this
  have h9 : LoadHolds rd (ofK (addressOfIndex eL)) 9 (ofK (addressOfIndex eP)) := by
    have := hb0 9 (by rw [vbgLayBlock_length hcl hcan]; omega)
    rwa [← List.getD_eq_getElem _ 0, w9] at this
  obtain ⟨e5, e6, e14, e15, e16, e17, e56, e65, e66, e133, e171, e181, e310, e314, e321⟩ :=
    vbg_ptrs hσ hG hcl hargs hW h5 h9
  have g : ∀ a : Atom, vbgEvL.any (fun t ↦ tbStmtsEqb [.atom a] [t]) = true → Good rd vbgS W σ a :=
    fun a h ↦ hG _ (vbg_mem h)
  have e7 : σ (.n 7) = ofK (addressOfIndex ez) := by
    rw [hσ, ev_params rd W (by rw [hl]; exact hc') (by rw [hl]; omega), hargs]; simp [hcl]
  have one : ∀ d : ℕ, vbgEvL.any (fun t ↦ tbStmtsEqb [.atom (.const (.n d) (word 1 0 0))] [t]) =
      true → σ (.n d) = 1 := fun d h ↦ by rw [← tb_word_one]; exact g _ h
  have c313 := one 313 (by decide +kernel)
  have c326 := one 326 (by decide +kernel)
  -- `pairs[depth]`
  have hpd : LoadHolds rd (σ (.n 314)) 0 (gen ^ (depth / 2)) := by
    rw [e314, tb_loadHolds_mul_gen_pow, Nat.add_zero]
    have := hPa depth (by simp [vbgPairsW]; omega)
    simpa [vbgPairsW] using this
  have r315 := good_read (g (.load (.n 315) (.n 314) 0) (by decide +kernel)) (by decide +kernel) hpd
  have r311 := good_read (g (.load (.n 311) (.n 310) 0) (by decide +kernel)) (by decide +kernel)
    (by rw [e310, ← e314]; exact hpd)
  have c309 := one 309 (by decide +kernel)
  have a312 : σ (.n 312) = σ (.n 309) + σ (.n 311) :=
    g (.add (.n 312) (.n 309) (.n 311)) (by decide +kernel)
  -- the last slot's row
  have hdb := hLb depth (by omega)
  have hrow : LoadHolds rd (σ (.n 321)) 9
      (ofK (addressOfIndex eP) * gen ^ (40 * ((depth - depth % 2) / 2 + depth % 2))) := by
    rw [e321, show (17 * depth) = 17 * depth from rfl]
    have := hdb 9 (by rw [vbgLayBlock_length hcl hcan]; omega)
    rw [← List.getD_eq_getElem _ 0] at this
    have inv := gkSl_inv (xs := xs) (sh := depth % 2) hcl hcan ((depth - depth % 2) / 2)
    unfold vbgLayBlock at this
    simp only [and_self, le_refl, ↓reduceIte, vbgSlotW] at this
    rwa [gkSlotWords_getD9 inv.1 inv.2.2.2] at this
  have r323 := good_read (g (.load (.n 323) (.n 321) 9) (by decide +kernel)) (by decide +kernel) hrow
  refine ⟨fun s hs ↦ ?_, fun d p off hm ↦ ?_, ?_, ?_, hrt, c313, r315.1, c326, e6, e66, e15, e16,
    e56, by rw [a312, c309, r311.1]⟩
  · -- the statements
    have hv := vsh_of_holdsList vbgPre vbg_iteOk hh s hs
    have hk := List.all_eq_true.mp vbg_kinds s hs
    simp only [vbgKindB, Bool.or_eq_true] at hk
    rcases hk with (ha | h7) | h8
    · exact vsh_atomsDeep ha hv
    · have e := tbStmtsEqb_sound h7
      simp only [List.cons.injEq, and_true] at e
      subst e
      refine ⟨hv.1, fun hne ↦ ?_⟩
      have h := hv.2 hne
      have hm0 : 0 < depth / 2 := by
        rcases Nat.eq_zero_or_pos (depth / 2) with h0 | h0
        · exfalso; apply hne
          rw [a312, c309, r311.1, h0, pow_zero, e_add_self]
        · exact h0
      simp only [List.map_cons, List.map_nil, c313, r315.1, e66, e6, e15, e16, e56] at h ⊢
      exact vbg_loop7_relIn hd hrun ⟨sp, hsp⟩ hm hRx hRL hRR hRr hRK hRD hm0 h
    · have e := tbStmtsEqb_sound h8
      simp only [List.cons.injEq, and_true] at e
      subst e
      refine ⟨hv.1, fun hne ↦ ?_⟩
      obtain ⟨n, h⟩ := hv.2 hne
      simp only [List.map_cons, List.map_nil, c326, e6, e7, r323.1] at h ⊢
      rw [show (1 : E) = gen ^ 0 from (pow_zero _).symm] at h ⊢
      rw [tb_ofK_gpow_mul] at h ⊢
      exact loop8_relIn (ptrIn_ofK hRz) (ptrIn_ofK fun i hi ↦ by
        rw [Nat.add_assoc]; exact hRr _ (by omega)) n 0 (by omega) h
  · -- the loads
    obtain ⟨hp, hcls⟩ := vbg_load_cls hm
    rw [hp]
    rcases hcls with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1 | h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
      ⟨h1, h2⟩ | ⟨h1 | h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1]
    · exact ⟨(ofK (addressOfIndex ec), xs.length), List.mem_cons_self, 0,
        by rw [e5]; simp, by omega⟩
    · exact ⟨(ofK (addressOfIndex eL), 17 * (depth + 2)), by simp, 0, by rw [e15]; simp, by omega⟩
    · exact ⟨(ofK (addressOfIndex eK), 8), by simp, 0, by rw [e56]; simp, by omega⟩
    · exact ⟨(ofK (addressOfIndex ePa), 33), by simp, 0, by rw [e65]; simp, by omega⟩
    · exact ⟨(ofK (addressOfIndex eD), 33), by simp, 0, by rw [e66]; simp, by omega⟩
    · exact ⟨(ofK (addressOfIndex eD), 33), by simp, depth, e133, by omega⟩
    · exact ⟨(ofK (addressOfIndex ec), xs.length), List.mem_cons_self, 2, e171, by omega⟩
    · exact ⟨(ofK (addressOfIndex eP), 1640), by simp, 40, e181, by omega⟩
    · exact ⟨(ofK (addressOfIndex ePa), 33), by simp, depth, e310, by omega⟩
    · exact ⟨(ofK (addressOfIndex ePa), 33), by simp, depth, e314, by omega⟩
    · exact ⟨(ofK (addressOfIndex eL), 17 * (depth + 2)), by simp, 17 * depth, e321, by omega⟩
  · -- the sizes
    rw [vbg_allocs]
    simp only [List.map_cons, List.map_nil, Sum.elim_inr, Sum.elim_inl, id, e14, vbgSizes]
    rw [gen_pow_eq_ofK, logG_spec (by omega)]
  · -- the bases
    rw [vbg_allocs]
    simp only [List.map_cons, List.map_nil, e15, e16, e17, e56, e65, e66]

theorem vbgLayersW_length {depth : ℕ} {cap0 xs : List E} {cur : E} {eP : ℕ}
    (hcl : cap0.length = 5) (hcan : AllCanonical cap0) :
    (vbgLayersW depth cap0 xs cur eP).length = 17 * (depth + 2) := by
  rw [vbgLayersW, List.length_flatMap]
  have : (List.range (depth + 2)).map (fun l ↦ (vbgLayBlock depth cap0 xs cur eP l).length) =
      List.replicate (depth + 2) 17 := by
    apply List.ext_getElem (by simp)
    intro i _ _
    simp [vbgLayBlock_length hcl hcan]
  rw [this, List.sum_replicate, smul_eq_mul, mul_comm]

theorem flatMap_const_length {f : ℕ → List E} {m w : ℕ} (hw : ∀ c < m, (f c).length = w) :
    ((List.range m).flatMap f).length = m * w := by
  rw [List.length_flatMap]
  have : (List.range m).map (fun c ↦ (f c).length) = List.replicate m w := by
    apply List.ext_getElem (by simp)
    intro i h1 _
    simp only [List.getElem_map, List.getElem_range, List.getElem_replicate]
    exact hw i (by simpa using h1)
  rw [this, List.sum_replicate, smul_eq_mul]

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- `verify_bus_gkr`'s layout at `fp`: the cursor's words, the point, the buffers. -/
noncomputable def vbgL (fs : String → ℕ) (depth : ℕ) (cap0 xs point : List E) (ec ez fp : ℕ) :
    List (ℕ × List E) :=
  flatL "verify_bus_gkr" [(ec, xs), (ez, point)] (vbgSizes depth)
    (fun fp ↦ vbgOwnW depth cap0 xs (ofK (addressOfIndex ec))
      (fp + fs "verify_bus_gkr" + 17 * (depth + 2) + 6034)) fs fp

/-- `verify_bus_gkr`'s buffers' first words at `fp`: layers, rounds, rows, `k_mod_next`, pairs,
`depth_shift`. -/
def vbgEL (fs : String → ℕ) (fp : ℕ) : ℕ := fp + fs "verify_bus_gkr"
def vbgER (fs : String → ℕ) (depth fp : ℕ) : ℕ := vbgEL fs fp + 17 * (depth + 2)
def vbgEP (fs : String → ℕ) (depth fp : ℕ) : ℕ := vbgER fs depth fp + 6034
def vbgEK (fs : String → ℕ) (depth fp : ℕ) : ℕ := vbgEP fs depth fp + 1640
def vbgEPa (fs : String → ℕ) (depth fp : ℕ) : ℕ := vbgEK fs depth fp + 8
def vbgED (fs : String → ℕ) (depth fp : ℕ) : ℕ := vbgEPa fs depth fp + 33

/-- The buffers `verify_bus_gkr` loads from, at `fp`. -/
noncomputable def vbgBufs (fs : String → ℕ) (depth : ℕ) (xs : List E) (ec fp : ℕ) : List (E × ℕ) :=
  [(ofK (addressOfIndex ec), xs.length), (ofK (addressOfIndex (fp + fs "verify_bus_gkr")), 17 *
      (depth + 2)),
    (ofK (addressOfIndex (fp + fs "verify_bus_gkr" + 17 * (depth + 2))), 6034),
    (ofK (addressOfIndex (fp + fs "verify_bus_gkr" + 17 * (depth + 2) + 6034)), 1640),
    (ofK (addressOfIndex (fp + fs "verify_bus_gkr" + 17 * (depth + 2) + 6034 + 1640)), 8),
    (ofK (addressOfIndex (fp + fs "verify_bus_gkr" + 17 * (depth + 2) + 6034 + 1640 + 8)), 33),
    (ofK (addressOfIndex (fp + fs "verify_bus_gkr" + 17 * (depth + 2) + 6034 + 1640 + 8 + 33)),
      33)]

/-- **What `verify_bus_gkr`'s placed lift needs**: its buffers' honest words fit their sizes, the
buffers it loads from lie in its layout, and on every memory defined below `2^κ` holding the layout
its honest valuation runs (`vbg_run` at the bump allocator's bases), its calls' values
(`VbgVals`) and its buffers' words (`vbgLay`). -/
theorem vbg_lift_facts {κ depth : ℕ} (hd1 : 1 ≤ depth) (hd : depth ≤ 32) (hκ : 6 ≤ κ)
    {cap0 xs : List E} {r : E × List E × List E} {cap' : List E}
    (hrun : RunsTo (gkrPhase depth) ⟨cap0, []⟩ xs r ⟨cap', []⟩)
    (hc : ∃ sp, (⟨cap0, []⟩ : Fs).Carries sp) (ec ez : ℕ) :
    (∀ fp, List.Forall₂ (fun c s => c.length ≤ s)
      (vbgOwnW depth cap0 xs (ofK (addressOfIndex ec)) (fp + fs "verify_bus_gkr" + 17 * (depth + 2)
          + 6034))
      (vbgSizes depth)) ∧
    (∀ fp, ∀ q ∈ vbgBufs fs depth xs ec fp, ∃ b, q.1 = ofK (addressOfIndex b) ∧
      ∀ i < q.2, RegionL (vbgL fs depth cap0 xs r.2.1 ec ez fp) (b + i)) ∧
    (∀ fp rd, LowDef κ rd → MemL rd (vbgL fs depth cap0 xs r.2.1 ec ez fp) →
      let σ := vbgσ rd depth cap0 ec ez (vbgEL fs fp) (vbgER fs depth fp) (vbgEP fs depth fp)
        (vbgEK fs depth fp) (vbgEPa fs depth fp) (vbgED fs depth fp)
      ((∀ s ∈ vbgPre, VSH (coreProgram.RelIn rd (RegionL (vbgL fs depth cap0 xs r.2.1 ec ez fp)))
          rd σ s) ∧
        LoadsInBuf σ (vbgBufs fs depth xs ec fp) vbgEvL ∧
        (vbgPre.filterMap Main.Stmt.allocSz).map (fun x => x.2.elim id fun s => logG (σ s)) =
          vbgSizes depth ∧
        ((vbgPre.filterMap Main.Stmt.allocSz).map Prod.fst).map σ =
          (bases (fp + fs "verify_bus_gkr") (vbgSizes depth)).map (fun b
              => ofK (addressOfIndex b)) ∧
        vbgRets.map σ = cap' ++ [ofK (addressOfIndex ec) * gen ^ xs.length] ++ r.2.2) ∧
      VbgVals σ depth (vbgEL fs fp) (vbgER fs depth fp) (vbgEK fs depth fp) (vbgED fs depth fp) ∧
      MemLay rd (vbgLay depth cap0 xs (ofK (addressOfIndex ec)) (vbgEL fs fp) (vbgER fs depth fp)
        (vbgEP fs depth fp) (vbgEK fs depth fp) (vbgEPa fs depth fp) (vbgED fs depth fp))) := by
  obtain ⟨-, hx2, -, -, -, -, -, hplm⟩ := gk_walk hrun hc
  have hcl : cap0.length = 5 := by
    obtain ⟨sp, hsp⟩ := hc
    have hsc : capOf sp.state = cap0 := hsp.1
    rw [← hsc]; simp [capOf]
  have hcan : AllCanonical cap0 := by
    obtain ⟨sp, hsp⟩ := hc
    have hsc : capOf sp.state = cap0 := hsp.1
    rw [← hsc]; exact tb_capOf_canonical _
  have hpl : ∀ j ≤ depth / 2, (gkSl cap0 xs (depth % 2) j).2.1.point.length = 2 * j + depth % 2 := by
    obtain ⟨-, -, -, hsteps, -⟩ := gk_walk hrun hc
    exact gkSl_point_len (gkSl0_point_len cap0 xs (depth % 2) (by omega)) fun j hj ↦ (hsteps j hj).1
  have hrp : r.2.1.length = depth := by
    obtain ⟨-, -, -, -, -, -, hr, hpl'⟩ := gk_walk hrun hc
    rw [hr]; exact hpl'
  have hown : ∀ fp, List.Forall₂ (fun c s => c.length ≤ s)
      (vbgOwnW depth cap0 xs (ofK (addressOfIndex ec)) (fp + fs "verify_bus_gkr" + 17 * (depth + 2)
          + 6034))
      (vbgSizes depth) := by
    intro fp
    simp only [vbgOwnW, vbgSizes, List.forall₂_cons, List.Forall₂.nil, and_true]
    refine ⟨by rw [vbgLayersW_length hcl hcan], ?_, ?_, by simp [kmnWords], by simp [vbgPairsW],
      by simp [vbgDshW]⟩
    · unfold vbgRoundsW; rw [flatMap_const_length (fun c _ ↦ vbgRecBlock_length hd c)]
    · unfold vbgRowsW; rw [flatMap_const_length (fun c _ ↦ vbgRowBlock_length hd hpl c)]
  have hbuf : ∀ fp, bufL (fp + fs "verify_bus_gkr") (vbgSizes depth)
      (vbgOwnW depth cap0 xs (ofK (addressOfIndex ec)) (fp + fs "verify_bus_gkr" + 17 * (depth + 2)
          + 6034)) =
      [(fp + fs "verify_bus_gkr", vbgLayersW depth cap0 xs (ofK (addressOfIndex ec)) (fp + fs "verify_bus_gkr" + 17 * (depth + 2) + 6034)),
        (fp + fs "verify_bus_gkr" + 17 * (depth + 2), vbgRoundsW depth cap0 xs (ofK
            (addressOfIndex ec))),
        (fp + fs "verify_bus_gkr" + 17 * (depth + 2) + 6034, vbgRowsW depth cap0 xs),
        (fp + fs "verify_bus_gkr" + 17 * (depth + 2) + 6034 + 1640, kmnWords),
        (fp + fs "verify_bus_gkr" + 17 * (depth + 2) + 6034 + 1640 + 8, vbgPairsW),
        (fp + fs "verify_bus_gkr" + 17 * (depth + 2) + 6034 + 1640 + 8 + 33, vbgDshW)] := by
    intro fp; simp [bufL, bases, vbgSizes, vbgOwnW]
  refine ⟨hown, ?_, ?_⟩
  · -- the buffers lie in the layout
    intro fp q hq
    have own : ∀ b (ws : List E), (b, ws) ∈ bufL (fp + fs "verify_bus_gkr") (vbgSizes depth)
        (vbgOwnW depth cap0 xs (ofK (addressOfIndex ec)) (fp + fs "verify_bus_gkr" + 17 * (depth + 2) + 6034)) →
        ∀ i < ws.length, RegionL (flatL "verify_bus_gkr" [(ec, xs), (ez, r.2.1)] (vbgSizes depth)
          (fun fp ↦ vbgOwnW depth cap0 xs (ofK (addressOfIndex ec)) (fp + fs "verify_bus_gkr" + 17 * (depth + 2) + 6034))
          fs fp) (b + i) := fun b ws hm i hi ↦
      regionL_append_right ⟨(b, ws), hm, by omega, by simpa using hi⟩
    simp only [vbgBufs, List.mem_cons, List.not_mem_nil, or_false] at hq
    rw [hbuf] at own
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨ec, rfl, fun i hi ↦ regionL_append_left ⟨(ec, xs), by simp, by omega, by simpa using hi⟩⟩
    · exact ⟨_, rfl, fun i hi ↦ own _ (vbgLayersW depth cap0 xs (ofK (addressOfIndex ec)) (fp + fs "verify_bus_gkr" + 17 * (depth + 2) + 6034)) (by simp) i
        (by rw [vbgLayersW_length hcl hcan]; exact hi)⟩
    · have hlr : (vbgRoundsW depth cap0 xs (ofK (addressOfIndex ec))).length = 6034 := by
        unfold vbgRoundsW; rw [flatMap_const_length (fun c _ ↦ vbgRecBlock_length hd c)]
      exact ⟨_, rfl, fun i hi ↦ own _ (vbgRoundsW depth cap0 xs (ofK (addressOfIndex ec))) (by simp) i (by omega)⟩
    · have hlp : (vbgRowsW depth cap0 xs).length = 1640 := by
        unfold vbgRowsW; rw [flatMap_const_length (fun c _ ↦ vbgRowBlock_length hd hpl c)]
      exact ⟨_, rfl, fun i hi ↦ own _ (vbgRowsW depth cap0 xs) (by simp) i (by omega)⟩
    · exact ⟨_, rfl, fun i hi ↦ own _ kmnWords (by simp) i (by simpa [kmnWords] using hi)⟩
    · exact ⟨_, rfl, fun i hi ↦ own _ vbgPairsW (by simp) i (by simpa [vbgPairsW] using hi)⟩
    · exact ⟨_, rfl, fun i hi ↦ own _ vbgDshW (by simp) i (by simpa [vbgDshW] using hi)⟩
  · -- the run
    intro fp rd hlow hL
    have hL' := hL
    simp only [vbgL, flatL] at hL'
    obtain ⟨hLin, hB⟩ := Main.memL_append.mp hL'
    rw [hbuf] at hB
    have hx : TbReadsAt rd (ofK (addressOfIndex ec)) xs := hLin (ec, xs) (by simp)
    have hz : TbReadsAt rd (ofK (addressOfIndex ez)) r.2.1 := hLin (ez, r.2.1) (by simp)
    have hLw := hB _ (List.mem_cons_self)
    have hRw := hB _ (List.mem_cons_of_mem _ List.mem_cons_self)
    have hPw := hB _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    have hKw := hB _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self)))
    have hPaw := hB _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))
    have hDw := hB _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        List.mem_cons_self)))))
    have hlp : (vbgRowsW depth cap0 xs).length = 1640 := by
      unfold vbgRowsW; rw [flatMap_const_length (fun c _ ↦ vbgRowBlock_length hd hpl c)]
    have hreg : vbgL fs depth cap0 xs r.2.1 ec ez fp = [(ec, xs), (ez, r.2.1)] ++
        bufL (fp + fs "verify_bus_gkr") (vbgSizes depth)
          (vbgOwnW depth cap0 xs (ofK (addressOfIndex ec)) (fp + fs "verify_bus_gkr" + 17 * (depth + 2) + 6034)) := rfl
    have hRz : ∀ i < depth, RegionL (vbgL fs depth cap0 xs r.2.1 ec ez fp) (ez + i) := by
      intro i hi
      rw [hreg]
      refine regionL_append_left ⟨(ez, r.2.1), by simp, by simp, ?_⟩
      simp only [hrp]; omega
    have hRr : ∀ i < 1640, RegionL (vbgL fs depth cap0 xs r.2.1 ec ez fp)
        (fp + fs "verify_bus_gkr" + 17 * (depth + 2) + 6034 + i) := by
      intro i hi
      rw [hreg, hbuf]
      refine regionL_append_right ⟨(fp + fs "verify_bus_gkr" + 17 * (depth + 2) + 6034, vbgRowsW depth cap0 xs),
        by simp, by simp, ?_⟩
      simp only [hlp]; omega
    have hRx : ∀ i < xs.length, RegionL (vbgL fs depth cap0 xs r.2.1 ec ez fp) (ec + i) :=
      fun i hi ↦ by
        rw [hreg]; exact regionL_append_left ⟨(ec, xs), by simp, by simp, by simpa using hi⟩
    have hRL : ∀ i < 17 * (depth + 2), RegionL (vbgL fs depth cap0 xs r.2.1 ec ez fp)
        (fp + fs "verify_bus_gkr" + i) := by
      intro i hi
      rw [hreg, hbuf]
      refine regionL_append_right ⟨(fp + fs "verify_bus_gkr", vbgLayersW depth cap0 xs (ofK (addressOfIndex ec))
        (fp + fs "verify_bus_gkr" + 17 * (depth + 2) + 6034)), by simp, by simp, ?_⟩
      simp only [vbgLayersW_length hcl hcan]; omega
    have hRR : ∀ i < 6034, RegionL (vbgL fs depth cap0 xs r.2.1 ec ez fp)
        (fp + fs "verify_bus_gkr" + 17 * (depth + 2) + i) := by
      intro i hi
      have hlr : (vbgRoundsW depth cap0 xs (ofK (addressOfIndex ec))).length = 6034 := by
        unfold vbgRoundsW; rw [flatMap_const_length (fun c _ ↦ vbgRecBlock_length hd c)]
      rw [hreg, hbuf]
      refine regionL_append_right ⟨(fp + fs "verify_bus_gkr" + 17 * (depth + 2),
        vbgRoundsW depth cap0 xs (ofK (addressOfIndex ec))), by simp, by simp, ?_⟩
      simp only [hlr]; omega
    have hRK : ∀ i < 8, RegionL (vbgL fs depth cap0 xs r.2.1 ec ez fp)
        (fp + fs "verify_bus_gkr" + 17 * (depth + 2) + 6034 + 1640 + i) := by
      intro i hi
      rw [hreg, hbuf]
      refine regionL_append_right ⟨(fp + fs "verify_bus_gkr" + 17 * (depth + 2) + 6034 + 1640,
        kmnWords), by simp, by simp, ?_⟩
      simp only [kmnWords, List.length_map, List.length_range]; omega
    have hRD : ∀ i < 33, RegionL (vbgL fs depth cap0 xs r.2.1 ec ez fp)
        (fp + fs "verify_bus_gkr" + 17 * (depth + 2) + 6034 + 1640 + 8 + 33 + i) := by
      intro i hi
      rw [hreg, hbuf]
      refine regionL_append_right ⟨(fp + fs "verify_bus_gkr" + 17 * (depth + 2) + 6034 + 1640 + 8 +
        33, vbgDshW), by simp, by simp, ?_⟩
      simp only [vbgDshW, List.length_map, List.length_range]; omega
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := vbg_run (R := RegionL (vbgL fs depth cap0 xs r.2.1 ec ez fp))
      hd1 hd hκ hrun hc hlow hx hz hLw hRw hPw hKw hPaw hDw hRz hRr hRx hRL hRR hRK hRD
    exact ⟨⟨h1, h2, h3, h4.trans (by simp [bases, vbgSizes]), h5⟩,
      h6, vbg_memLay hd hcl hcan hpl hLw hRw hPw hKw hPaw hDw⟩

/-- **`verify_bus_gkr` is complete, placed** (TRIAGE G #43): at `1 ≤ depth ≤ 32`, on memories
defined below `2^κ`, `κ ≥ 6`, an accepting run of `gkrPhase depth` from a carried capacity `cap0`
reading the words `xs` at the cursor `g^ec`, the run's point at `zeta = g^ez`, its six buffers at
the bump allocator's positions holding their honest words (`vbgOwnW`). It returns the run's
capacity, the cursor past `xs` and the three values. -/
theorem verify_bus_gkr_completeAt {κ depth : ℕ} (hd1 : 1 ≤ depth) (hd : depth ≤ 32) (hκ : 6 ≤ κ)
    {cap0 xs : List E} {r : E × List E × List E} {cap' : List E}
    (hrun : RunsTo (gkrPhase depth) ⟨cap0, []⟩ xs r ⟨cap', []⟩)
    (hc : ∃ sp, (⟨cap0, []⟩ : Fs).Carries sp) (ec ez : ℕ) :
    CompleteAtD fs cert κ "verify_bus_gkr" [(ec, xs), (ez, r.2.1)]
      (cap0 ++ [ofK (addressOfIndex ec), gen ^ depth, ofK (addressOfIndex ez)])
      (Returns (cap' ++ [ofK (addressOfIndex ec) * gen ^ xs.length] ++ r.2.2)) := by
  have hcl : cap0.length = 5 := by
    obtain ⟨sp, hsp⟩ := hc
    have hsc : capOf sp.state = cap0 := hsp.1
    rw [← hsc]; simp [capOf]
  obtain ⟨hown, hbufs, hfacts⟩ := vbg_lift_facts (fs := fs) hd1 hd hκ hrun hc ec ez
  exact flat_completeAt vbgFlat [(ec, xs), (ez, r.2.1)] _ _ (by simp [vbgFlat, hcl]) (vbgSizes depth)
    (fun fp ↦ vbgOwnW depth cap0 xs (ofK (addressOfIndex ec)) (fp + fs "verify_bus_gkr" + 17 * (depth + 2) + 6034)) hown
    (fun fp ↦ vbgW (ofK (addressOfIndex (vbgEL fs fp))) (ofK (addressOfIndex (vbgER fs depth fp)))
      (ofK (addressOfIndex (vbgEP fs depth fp))) (ofK (addressOfIndex (vbgEK fs depth fp)))
      (ofK (addressOfIndex (vbgEPa fs depth fp))) (ofK (addressOfIndex (vbgED fs depth fp))))
    (vbgBufs fs depth xs ec) hbufs (fun fp rd hlow hL ↦ (hfacts fp rd hlow hL).1)

end
end LeanVM.Guest.B1.Tables
