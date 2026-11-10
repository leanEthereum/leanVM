/-
  LeanVM.Guest.B1.Gkr.VbgAt

  `verify_bus_gkr` is complete in the uniform placed form (`CompleteAtD`).
-/

module

public import LeanVM.Guest.B1.Gkr.VbgLoads
public import LeanVM.Guest.B1.Gkr.VbgL7
public import LeanVM.Guest.B1.Tables.Kids.Loop8
public import LeanVM.Guest.B1.Tables.FlatLiftOut

/-!
# `verify_bus_gkr`, placed (TRIAGE G #43)

`vbg_run`: at `2 ≤ depth`, on a memory defined below `2^κ` (`κ ≥ 6`, the range check of
`g^depth`) holding the cursor's words, the point at `zeta` and the seven buffers whole
(`vbgOwnW`), the honest valuation (`vbgFlat.σ`, the allocations answered by the buffers'
pointers) satisfies every statement with its calls by relations loading from a region `R`
holding the cursor's words, the point and the buffers, its loads land inside the buffers
(`vbg_loadOk`, `vbg_ptrs`; the radix-four arm's fourteen words past the cursor are the run's at
`depth ≥ 2`, `gk_xs_len`), its allocations are the buffers and it returns the accepting run's
capacity, cursor and the values' buffer. `__loop7`'s relation loads from `R` (`loop8_relIn`), and
`__loop6`'s (`vbg_loop7_relIn`).

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

/-- `__loop6`'s call. -/
def vbgCall7 : Stmt :=
  .callIf (.n 379) "__loop6" [.n 380, .n 382, .n 375, .n 16, .n 8, .n 17, .n 63, .n 142, .n 6,
    .n 64]

/-- `__loop7`'s call. -/
def vbgCall8 : Stmt := .callIf (.n 392) "__loop7" [.n 393, .n 6, .n 7, .n 390]

/-- Every statement is an atom, an `ite` of atoms, or one of the two calls. -/
def vbgKindB (s : Stmt) : Bool :=
  atomsDeep s || tbStmtsEqb [s] [vbgCall7] || tbStmtsEqb [s] [vbgCall8]

theorem vbg_kinds : vbgPre.all vbgKindB = true := by decide +kernel

theorem vbg_allocs : vbgPre.filterMap Main.Stmt.allocSz = [(.n 16, .inr (.n 15)),
    (.n 17, .inl 6034), (.n 18, .inl 1640), (.n 64, .inl 8), (.n 73, .inl 33),
    (.n 74, .inl 33), (.n 394, .inl 3)] := by
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
    p = .n p.idx ∧ ((p.idx = 5 ∧ off < 14) ∨ (p.idx = 16 ∧ off < 39) ∨ (p.idx = 18 ∧ off < 42) ∨
      (p.idx = 64 ∧ off < 8) ∨ ((p.idx = 73 ∨ p.idx = 74) ∧ off < 33) ∨
      (((p.idx = 141 ∨ p.idx = 377) ∨ p.idx = 381) ∧ off = 0) ∨ (p.idx = 388 ∧ off < 10) ∨
      (p.idx = 394 ∧ off < 3)) := by
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

theorem gkSlotWords_getD9 {s : Fs} {cur : E} {st : GkrState} {row pos half par : E}
    (hcl : s.cap.length = 5) (hvl : st.values.length = 3) :
    (gkSlotWords s cur st row pos half par).getD 9 0 = row := by
  obtain ⟨c0, c1, c2, c3, c4, hc⟩ := tb_list5_eq hcl
  obtain ⟨v0, v1, v2, hv⟩ := tb_list3_eq hvl
  simp [gkSlotWords, hc, hv]

/-- The honest valuation of `verify_bus_gkr` on its buffers at `g^eL .. g^eV`, the cursor at
`g^ec`, `zeta` at `g^ez`. -/
noncomputable def vbgσ (rd : Reader) (depth : ℕ) (cap0 : List E) (tabs : E)
    (ec ez eL eR eP eK eB eO eV : ℕ) : Val :=
  vbgFlat.σ rd (vbgW (ofK (addressOfIndex eL)) (ofK (addressOfIndex eR)) (ofK (addressOfIndex eP))
      (ofK (addressOfIndex eK)) (ofK (addressOfIndex eB)) (ofK (addressOfIndex eO))
      (ofK (addressOfIndex eV)))
    (cap0 ++ [ofK (addressOfIndex ec), gen ^ depth, ofK (addressOfIndex ez), tabs])

/-- The values the calls of `__loop6` and `__loop7` start and end at, and `__loop6`'s
arguments. -/
def VbgVals (σ : Val) (depth eL eR eK : ℕ) (tabs : E) : Prop :=
  σ (.n 380) = 1 ∧ σ (.n 382) = gen ^ ((depth - 1) / 2) ∧ σ (.n 375) = gen ^ (2 - depth % 2) ∧
    σ (.n 393) = 1 ∧ σ (.n 6) = gen ^ depth ∧ σ (.n 16) = ofK (addressOfIndex eL) ∧
    σ (.n 17) = ofK (addressOfIndex eR) ∧ σ (.n 64) = ofK (addressOfIndex eK) ∧
    σ (.n 8) = tabs ∧ σ (.n 142) = gen ^ (depth % 2) ∧
    σ (.n 379) = 1 + gen ^ ((depth - 1) / 2)

/-- The seven buffers of `verify_bus_gkr` in a region, and the cursor's words and the point. -/
structure VbgR (R : ℕ → Prop) (depth : ℕ) (xs : List E) (ec ez eL eR eP eK : ℕ) : Prop where
  z : ∀ i < depth, R (ez + i)
  r : ∀ i < 1640, R (eP + i)
  x : ∀ i < xs.length, R (ec + i)
  l : ∀ i < 13 * (depth + 2), R (eL + i)
  rr : ∀ i < 6034, R (eR + i)
  k : ∀ i < 8, R (eK + i)

/-- **`verify_bus_gkr`'s honest valuation on a memory holding its words**: every statement holds,
its calls loading from `R`; its loads land inside its buffers; its allocations are the buffers; it
returns the accepting run's capacity, cursor and the values' buffer. -/
theorem vbg_run {depth κ : ℕ} (hd2 : 2 ≤ depth) (hd : depth ≤ 32) (hκ : 6 ≤ κ)
    {cap0 xs : List E} {r : E × List E × List E} {cap' : List E}
    (hrun : RunsTo (gkrPhase depth) ⟨cap0, []⟩ xs r ⟨cap', []⟩)
    (hc : ∃ sp, (⟨cap0, []⟩ : Fs).Carries sp) {tabs : E} {ec ez eL eR eP eK eB eO eV : ℕ}
    {rd : Reader} {R : ℕ → Prop} (hlow : LowDef κ rd) (hx : TbReadsAt rd (ofK (addressOfIndex ec)) xs)
    (hz : TbReadsAt rd (ofK (addressOfIndex ez)) r.2.1)
    (hL : TbReadsAt rd (ofK (addressOfIndex eL)) (vbgLayersW depth cap0 xs (ofK (addressOfIndex
        ec)) eP))
    (hR : TbReadsAt rd (ofK (addressOfIndex eR)) (vbgRoundsW depth cap0 xs (ofK
        (addressOfIndex ec))))
    (hP : TbReadsAt rd (ofK (addressOfIndex eP)) (vbgRowsW depth cap0 xs))
    (hK : TbReadsAt rd (ofK (addressOfIndex eK)) kmnWords)
    (hB : TbReadsAt rd (ofK (addressOfIndex eB)) vbgBndW)
    (hO : TbReadsAt rd (ofK (addressOfIndex eO)) vbgOddW)
    (hV : TbReadsAt rd (ofK (addressOfIndex eV)) (vbgValsW depth cap0 xs))
    (hReg : VbgR R depth xs ec ez eL eR eP eK) :
    (∀ s ∈ vbgPre, VSH (coreProgram.RelIn rd R) rd (vbgσ rd depth cap0 tabs ec ez eL eR eP eK eB eO eV)
      s) ∧
    LoadsInBuf (vbgσ rd depth cap0 tabs ec ez eL eR eP eK eB eO eV)
      [(ofK (addressOfIndex ec), xs.length), (ofK (addressOfIndex eL), 13 * (depth + 2)),
        (ofK (addressOfIndex eR), 6034), (ofK (addressOfIndex eP), 1640),
        (ofK (addressOfIndex eK), 8), (ofK (addressOfIndex eB), 33),
        (ofK (addressOfIndex eO), 33), (ofK (addressOfIndex eV), 3)] vbgEvL ∧
    (vbgPre.filterMap Main.Stmt.allocSz).map
      (fun x => x.2.elim id fun s => logG (vbgσ rd depth cap0 tabs ec ez eL eR eP eK eB eO eV s)) =
        vbgSizes depth ∧
    ((vbgPre.filterMap Main.Stmt.allocSz).map Prod.fst).map
        (vbgσ rd depth cap0 tabs ec ez eL eR eP eK eB eO eV) =
      [ofK (addressOfIndex eL), ofK (addressOfIndex eR), ofK (addressOfIndex eP),
        ofK (addressOfIndex eK), ofK (addressOfIndex eB), ofK (addressOfIndex eO),
        ofK (addressOfIndex eV)] ∧
    vbgRets.map (vbgσ rd depth cap0 tabs ec ez eL eR eP eK eB eO eV) =
      cap' ++ [ofK (addressOfIndex ec) * gen ^ xs.length, ofK (addressOfIndex eV)] ∧
    VbgVals (vbgσ rd depth cap0 tabs ec ez eL eR eP eK eB eO eV) depth eL eR eK tabs := by
  obtain ⟨hcnt, hx2, hodd, hsteps, hend, hsF, hr, hplm⟩ := gk_walk hrun hc
  obtain ⟨sp, hsp⟩ := hc
  have hsc : capOf sp.state = cap0 := hsp.1
  have hcl : cap0.length = 5 := by rw [← hsc]; simp [capOf]
  have hpl : ∀ j ≤ depth / 2, (gkSl cap0 xs (depth % 2) j).2.1.point.length = 2 * j + depth % 2 :=
    gkSl_point_len (gkSl0_point_len cap0 xs (depth % 2) (by omega)) fun j hj ↦ (hsteps j hj).1
  have hm := vbg_memLay (eL := eL) (eR := eR) (eP := eP) (eK := eK) (eB := eB) (eO := eO)
    (eV := eV) hd hcl hpl hL hR hP hK hB hO hV
  have h64 : (64 : ℕ) ≤ 2 ^ κ := by
    calc (64 : ℕ) = 2 ^ 6 := by norm_num
      _ ≤ 2 ^ κ := Nat.pow_le_pow_right (by norm_num) hκ
  have hrc : (rd (addressOfIndex depth)).isSome = true ∧ (rd (addressOfIndex (32 - depth))).isSome =
      true :=
    ⟨hlow depth (by omega), hlow (32 - depth) (by omega)⟩
  obtain ⟨hh, hrt⟩ := verify_bus_gkr_body (tabs := tabs) (by omega) hd hrun ⟨sp, hsp⟩ hx hz hm hrc
  have hx14 := gk_xs_len hd2 hrun ⟨sp, hsp⟩
  set args : List E := cap0 ++ [ofK (addressOfIndex ec), gen ^ depth, ofK (addressOfIndex ez),
    tabs] with hargs
  set W := vbgW (ofK (addressOfIndex eL)) (ofK (addressOfIndex eR)) (ofK (addressOfIndex eP)) (ofK
      (addressOfIndex eK)) (ofK (addressOfIndex eB)) (ofK (addressOfIndex eO))
      (ofK (addressOfIndex eV)) with hW
  have hσe : vbgσ rd depth cap0 tabs ec ez eL eR eP eK eB eO eV =
      B1.Val.ofArgs (ev rd W args vbgEvL) := rfl
  rw [hσe]
  set σ := B1.Val.ofArgs (ev rd W args vbgEvL) with hσ
  have hl : args.length = 9 := by rw [hargs]; simp [hcl]
  obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp vb_chk
  have hG : ∀ s ∈ vbgEvL, GoodS rd vbgS W σ s := by
    have h := (ev_spec rd W vbgEvL args (by rw [hl]; exact hc')).2.2
    rw [hl] at h
    exact h
  obtain ⟨e5, e6, e15, e16, e17, e18, e64, e73, e74, e141, e377, e381, e388, e394⟩ :=
    vbg_ptrs hσ hG hcl hargs hW
  have g : ∀ a : Atom, vbgEvL.any (fun t ↦ tbStmtsEqb [.atom a] [t]) = true → Good rd vbgS W σ a :=
    fun a h ↦ hG _ (vbg_mem h)
  have e7 : σ (.n 7) = ofK (addressOfIndex ez) := by
    rw [hσ, ev_params rd W (by rw [hl]; exact hc') (by rw [hl]; omega), hargs]; simp [hcl]
  have e8 : σ (.n 8) = tabs := by
    rw [hσ, ev_params rd W (by rw [hl]; exact hc') (by rw [hl]; omega), hargs]; simp [hcl]
  have one : ∀ d : ℕ, vbgEvL.any (fun t ↦ tbStmtsEqb [.atom (.const (.n d) (word 1 0))] [t]) =
      true → σ (.n d) = 1 := fun d h ↦ by rw [← tb_word_one]; exact g _ h
  have c380 := one 380 (by decide +kernel)
  have c393 := one 393 (by decide +kernel)
  have c376 := one 376 (by decide +kernel)
  have c143 := one 143 (by decide +kernel)
  -- `loop_bounds[depth]`, `depth_odd[depth]`
  have hbd : LoadHolds rd (σ (.n 381)) 0 (gen ^ ((depth - 1) / 2)) := by
    rw [e381, tb_loadHolds_mul_gen_pow, Nat.add_zero]
    have := hB depth (by simp [vbgBndW]; omega)
    simpa [vbgBndW] using this
  have r382 := good_read (g (.load (.n 382) (.n 381) 0) (by decide +kernel)) (by decide +kernel) hbd
  have r378 := good_read (g (.load (.n 378) (.n 377) 0) (by decide +kernel)) (by decide +kernel)
    (by rw [e377, ← e381]; exact hbd)
  have a379 : σ (.n 379) = σ (.n 376) + σ (.n 378) :=
    g (.add (.n 379) (.n 376) (.n 378)) (by decide +kernel)
  have hod : LoadHolds rd (σ (.n 141)) 0 (gen ^ (depth % 2)) := by
    rw [e141, tb_loadHolds_mul_gen_pow, Nat.add_zero]
    have := hO depth (by simp [vbgOddW]; omega)
    simpa [vbgOddW] using this
  have r142 := good_read (g (.load (.n 142) (.n 141) 0) (by decide +kernel)) (by decide +kernel) hod
  have c374 : σ (.n 374) = gen ^ 2 := by
    rw [← tb_word_four]; exact g (.const (.n 374) (word 4 0)) (by decide +kernel)
  have e375 : σ (.n 375) = gen ^ (2 - depth % 2) := by
    have h := g (.mul (.n 374) (.n 375) (.n 142)) (by decide +kernel)
    have hn : ¬ ((V.n 375).idx < (V.n 374).idx ∧ (V.n 142).idx < (V.n 374).idx) := by
      show ¬ (375 < 374 ∧ 142 < 374); omega
    simp only [Good, hn, ↓reduceIte] at h
    rw [h, c374, r142.1]
    have hs : depth % 2 ≤ 2 := by omega
    rw [show (gen : E) ^ 2 = gen ^ (2 - depth % 2) * gen ^ (depth % 2) by
        rw [← pow_add, Nat.sub_add_cancel hs],
      mul_assoc, mul_inv_cancel₀ (gen_pow_ne_zero _), mul_one]
  -- the last slot's row
  have hLb := tbReadsAt_flatMap_eq (w := 13) _ (depth + 2)
    (fun c _ ↦ vbgLayBlock_length hcl c) hL
  have hdb := hLb depth (by omega)
  have hrow : LoadHolds rd (σ (.n 388)) 9
      (ofK (addressOfIndex eP) * gen ^ (40 * ((depth - depth % 2) / 2 + depth % 2))) := by
    rw [e388]
    have := hdb 9 (by rw [vbgLayBlock_length hcl]; omega)
    rw [← List.getD_eq_getElem _ 0] at this
    have inv := gkSl_inv (xs := xs) (sh := depth % 2) hcl ((depth - depth % 2) / 2)
    unfold vbgLayBlock at this
    simp only [show 1 ≤ depth by omega, and_self, le_refl, ↓reduceIte, vbgSlotW] at this
    rwa [gkSlotWords_getD9 inv.1 inv.2.1] at this
  have r390 := good_read (g (.load (.n 390) (.n 388) 9) (by decide +kernel)) (by decide +kernel) hrow
  refine ⟨fun s hs ↦ ?_, fun d p off hm ↦ ?_, ?_, ?_, hrt, c380, r382.1, e375, c393, e6, e16, e17,
    e64, e8, r142.1, by rw [a379, c376, r378.1]⟩
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
      have hm0 : 0 < (depth - 1) / 2 := by
        rcases Nat.eq_zero_or_pos ((depth - 1) / 2) with h0 | h0
        · exfalso; apply hne
          rw [a379, c376, r378.1, h0, pow_zero, e_add_self]
        · exact h0
      simp only [List.map_cons, List.map_nil, c380, r382.1, e375, e16, e8, e17, r142.1, e6,
        e64] at h ⊢
      exact vbg_loop7_relIn hd hrun ⟨sp, hsp⟩ hm hReg.x hReg.l hReg.rr hReg.r hReg.k hm0 h
    · have e := tbStmtsEqb_sound h8
      simp only [List.cons.injEq, and_true] at e
      subst e
      refine ⟨hv.1, fun hne ↦ ?_⟩
      obtain ⟨n, h⟩ := hv.2 hne
      simp only [List.map_cons, List.map_nil, c393, e6, e7, r390.1] at h ⊢
      rw [show (1 : E) = gen ^ 0 from (pow_zero _).symm] at h ⊢
      rw [tb_ofK_gpow_mul] at h ⊢
      exact loop8_relIn (ptrIn_ofK hReg.z) (ptrIn_ofK fun i hi ↦ by
        rw [Nat.add_assoc]; exact hReg.r _ (by omega)) n 0 (by omega) h
  · -- the loads
    obtain ⟨hp, hcls⟩ := vbg_load_cls hm
    rw [hp]
    rcases hcls with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1 | h1, h2⟩ |
      ⟨(h1 | h1) | h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1]
    · exact ⟨(ofK (addressOfIndex ec), xs.length), List.mem_cons_self, 0,
        by rw [e5]; simp, by omega⟩
    · exact ⟨(ofK (addressOfIndex eL), 13 * (depth + 2)), by simp, 0, by rw [e16]; simp,
        by omega⟩
    · exact ⟨(ofK (addressOfIndex eP), 1640), by simp, 0, by rw [e18]; simp, by omega⟩
    · exact ⟨(ofK (addressOfIndex eK), 8), by simp, 0, by rw [e64]; simp, by omega⟩
    · exact ⟨(ofK (addressOfIndex eB), 33), by simp, 0, by rw [e73]; simp, by omega⟩
    · exact ⟨(ofK (addressOfIndex eO), 33), by simp, 0, by rw [e74]; simp, by omega⟩
    · exact ⟨(ofK (addressOfIndex eO), 33), by simp, depth, e141, by omega⟩
    · exact ⟨(ofK (addressOfIndex eB), 33), by simp, depth, e377, by omega⟩
    · exact ⟨(ofK (addressOfIndex eB), 33), by simp, depth, e381, by omega⟩
    · exact ⟨(ofK (addressOfIndex eL), 13 * (depth + 2)), by simp, 13 * depth, e388, by omega⟩
    · exact ⟨(ofK (addressOfIndex eV), 3), by simp, 0, by rw [e394]; simp, by omega⟩
  · -- the sizes
    rw [vbg_allocs]
    simp only [List.map_cons, List.map_nil, Sum.elim_inr, Sum.elim_inl, id, e15, vbgSizes]
    rw [gen_pow_eq_ofK, logG_spec (by omega)]
  · -- the bases
    rw [vbg_allocs]
    simp only [List.map_cons, List.map_nil, e16, e17, e18, e64, e73, e74, e394]

theorem vbgLayersW_length {depth : ℕ} {cap0 xs : List E} {cur : E} {eP : ℕ}
    (hcl : cap0.length = 5) :
    (vbgLayersW depth cap0 xs cur eP).length = 13 * (depth + 2) := by
  rw [vbgLayersW, List.length_flatMap]
  have : (List.range (depth + 2)).map (fun l ↦ (vbgLayBlock depth cap0 xs cur eP l).length) =
      List.replicate (depth + 2) 13 := by
    apply List.ext_getElem (by simp)
    intro i _ _
    simp [vbgLayBlock_length hcl]
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

/-- `verify_bus_gkr`'s buffers' first words at `fp`: layers, rounds, rows, `k_mod_next`,
`loop_bounds`, `depth_odd`, the values. -/
def vbgEL (fs : String → ℕ) (fp : ℕ) : ℕ := fp + fs "verify_bus_gkr"
def vbgER (fs : String → ℕ) (depth fp : ℕ) : ℕ := vbgEL fs fp + 13 * (depth + 2)
def vbgEP (fs : String → ℕ) (depth fp : ℕ) : ℕ := vbgER fs depth fp + 6034
def vbgEK (fs : String → ℕ) (depth fp : ℕ) : ℕ := vbgEP fs depth fp + 1640
def vbgEB (fs : String → ℕ) (depth fp : ℕ) : ℕ := vbgEK fs depth fp + 8
def vbgEO (fs : String → ℕ) (depth fp : ℕ) : ℕ := vbgEB fs depth fp + 33
def vbgEV (fs : String → ℕ) (depth fp : ℕ) : ℕ := vbgEO fs depth fp + 33

/-- `verify_bus_gkr`'s layout at `fp`: the cursor's words, the point, the buffers. -/
noncomputable def vbgL (fs : String → ℕ) (depth : ℕ) (cap0 xs point : List E) (ec ez fp : ℕ) :
    List (ℕ × List E) :=
  flatL "verify_bus_gkr" [(ec, xs), (ez, point)] (vbgSizes depth)
    (fun fp ↦ vbgOwnW depth cap0 xs (ofK (addressOfIndex ec)) (vbgEP fs depth fp)) fs fp

/-- The buffers `verify_bus_gkr` loads from, at `fp`. -/
noncomputable def vbgBufs (fs : String → ℕ) (depth : ℕ) (xs : List E) (ec fp : ℕ) : List (E × ℕ) :=
  [(ofK (addressOfIndex ec), xs.length), (ofK (addressOfIndex (vbgEL fs fp)), 13 * (depth + 2)),
    (ofK (addressOfIndex (vbgER fs depth fp)), 6034), (ofK (addressOfIndex (vbgEP fs depth fp)), 1640),
    (ofK (addressOfIndex (vbgEK fs depth fp)), 8), (ofK (addressOfIndex (vbgEB fs depth fp)), 33),
    (ofK (addressOfIndex (vbgEO fs depth fp)), 33), (ofK (addressOfIndex (vbgEV fs depth fp)), 3)]

theorem vbg_bufL (fs : String → ℕ) (depth : ℕ) (cap0 xs : List E) (cur : E) (fp : ℕ) :
    bufL (fp + fs "verify_bus_gkr") (vbgSizes depth)
      (vbgOwnW depth cap0 xs cur (vbgEP fs depth fp)) =
      [(vbgEL fs fp, vbgLayersW depth cap0 xs cur (vbgEP fs depth fp)),
        (vbgER fs depth fp, vbgRoundsW depth cap0 xs cur),
        (vbgEP fs depth fp, vbgRowsW depth cap0 xs), (vbgEK fs depth fp, kmnWords),
        (vbgEB fs depth fp, vbgBndW), (vbgEO fs depth fp, vbgOddW),
        (vbgEV fs depth fp, vbgValsW depth cap0 xs)] := by
  simp [bufL, bases, vbgSizes, vbgOwnW, vbgEL, vbgER, vbgEP, vbgEK, vbgEB, vbgEO, vbgEV,
    Nat.add_assoc]

/-- **What `verify_bus_gkr`'s placed lift needs**: its buffers' honest words fit their sizes, the
buffers it loads from lie in its layout, and on every memory defined below `2^κ` holding the layout
its honest valuation runs (`vbg_run` at the bump allocator's bases), its calls' values
(`VbgVals`) and its buffers' words (`vbgLay`). -/
theorem vbg_lift_facts {κ depth : ℕ} (hd2 : 2 ≤ depth) (hd : depth ≤ 32) (hκ : 6 ≤ κ)
    {cap0 xs : List E} {r : E × List E × List E} {cap' : List E}
    (hrun : RunsTo (gkrPhase depth) ⟨cap0, []⟩ xs r ⟨cap', []⟩)
    (hc : ∃ sp, (⟨cap0, []⟩ : Fs).Carries sp) (tabs : E) (ec ez : ℕ) :
    (∀ fp, List.Forall₂ (fun c s => c.length ≤ s)
      (vbgOwnW depth cap0 xs (ofK (addressOfIndex ec)) (vbgEP fs depth fp)) (vbgSizes depth)) ∧
    (∀ fp, ∀ q ∈ vbgBufs fs depth xs ec fp, ∃ b, q.1 = ofK (addressOfIndex b) ∧
      ∀ i < q.2, RegionL (vbgL fs depth cap0 xs r.2.1 ec ez fp) (b + i)) ∧
    (∀ fp rd, LowDef κ rd → MemL rd (vbgL fs depth cap0 xs r.2.1 ec ez fp) →
      let σ := vbgσ rd depth cap0 tabs ec ez (vbgEL fs fp) (vbgER fs depth fp) (vbgEP fs depth fp)
        (vbgEK fs depth fp) (vbgEB fs depth fp) (vbgEO fs depth fp) (vbgEV fs depth fp)
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
      VbgVals σ depth (vbgEL fs fp) (vbgER fs depth fp) (vbgEK fs depth fp) tabs ∧
      MemLay rd (vbgLay depth cap0 xs (ofK (addressOfIndex ec)) (vbgEL fs fp) (vbgER fs depth fp)
        (vbgEP fs depth fp) (vbgEK fs depth fp) (vbgEB fs depth fp) (vbgEO fs depth fp)
        (vbgEV fs depth fp))) := by
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
  have hlr : (vbgRoundsW depth cap0 xs (ofK (addressOfIndex ec))).length = 6034 := by
    unfold vbgRoundsW; rw [flatMap_const_length (fun c _ ↦ vbgRecBlock_length hd c)]
  have hlp : (vbgRowsW depth cap0 xs).length = 1640 := by
    unfold vbgRowsW; rw [flatMap_const_length (fun c _ ↦ vbgRowBlock_length hd hpl c)]
  have hown : ∀ fp, List.Forall₂ (fun c s => c.length ≤ s)
      (vbgOwnW depth cap0 xs (ofK (addressOfIndex ec)) (vbgEP fs depth fp)) (vbgSizes depth) := by
    intro fp
    simp only [vbgOwnW, vbgSizes, List.forall₂_cons, List.Forall₂.nil, and_true]
    exact ⟨by rw [vbgLayersW_length hcl], by rw [hlr], by rw [hlp], by simp [kmnWords],
      by simp [vbgBndW], by simp [vbgOddW], by rw [hvl]⟩
  have hreg : ∀ fp, vbgL fs depth cap0 xs r.2.1 ec ez fp = [(ec, xs), (ez, r.2.1)] ++
      [(vbgEL fs fp, vbgLayersW depth cap0 xs (ofK (addressOfIndex ec)) (vbgEP fs depth fp)),
        (vbgER fs depth fp, vbgRoundsW depth cap0 xs (ofK (addressOfIndex ec))),
        (vbgEP fs depth fp, vbgRowsW depth cap0 xs), (vbgEK fs depth fp, kmnWords),
        (vbgEB fs depth fp, vbgBndW), (vbgEO fs depth fp, vbgOddW),
        (vbgEV fs depth fp, vbgValsW depth cap0 xs)] := fun fp ↦ by
    rw [← vbg_bufL]; rfl
  have own : ∀ fp b (ws : List E), (b, ws) ∈
      [(vbgEL fs fp, vbgLayersW depth cap0 xs (ofK (addressOfIndex ec)) (vbgEP fs depth fp)),
        (vbgER fs depth fp, vbgRoundsW depth cap0 xs (ofK (addressOfIndex ec))),
        (vbgEP fs depth fp, vbgRowsW depth cap0 xs), (vbgEK fs depth fp, kmnWords),
        (vbgEB fs depth fp, vbgBndW), (vbgEO fs depth fp, vbgOddW),
        (vbgEV fs depth fp, vbgValsW depth cap0 xs)] →
      ∀ i < ws.length, RegionL (vbgL fs depth cap0 xs r.2.1 ec ez fp) (b + i) :=
    fun fp b ws hm i hi ↦ by
      rw [hreg]; exact regionL_append_right ⟨(b, ws), hm, by omega, by simpa using hi⟩
  refine ⟨hown, ?_, ?_⟩
  · -- the buffers lie in the layout
    intro fp q hq
    simp only [vbgBufs, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨ec, rfl, fun i hi ↦ by
        rw [hreg]; exact regionL_append_left ⟨(ec, xs), by simp, by omega, by simpa using hi⟩⟩
    · exact ⟨_, rfl, fun i hi ↦ own fp (vbgEL fs fp) (vbgLayersW depth cap0 xs (ofK (addressOfIndex ec)) (vbgEP fs depth fp)) (by simp) i (by rw [vbgLayersW_length hcl]; exact hi)⟩
    · exact ⟨_, rfl, fun i hi ↦ own fp (vbgER fs depth fp) (vbgRoundsW depth cap0 xs (ofK (addressOfIndex ec))) (by simp) i (by rw [hlr]; exact hi)⟩
    · exact ⟨_, rfl, fun i hi ↦ own fp (vbgEP fs depth fp) (vbgRowsW depth cap0 xs) (by simp) i (by rw [hlp]; exact hi)⟩
    · exact ⟨_, rfl, fun i hi ↦ own fp (vbgEK fs depth fp) kmnWords (by simp) i (by simpa [kmnWords] using hi)⟩
    · exact ⟨_, rfl, fun i hi ↦ own fp (vbgEB fs depth fp) vbgBndW (by simp) i (by simpa [vbgBndW] using hi)⟩
    · exact ⟨_, rfl, fun i hi ↦ own fp (vbgEO fs depth fp) vbgOddW (by simp) i (by simpa [vbgOddW] using hi)⟩
    · exact ⟨_, rfl, fun i hi ↦ own fp (vbgEV fs depth fp) (vbgValsW depth cap0 xs) (by simp) i (by rw [hvl]; exact hi)⟩
  · -- the run
    intro fp rd hlow hL
    have hL' := hL
    rw [hreg] at hL'
    obtain ⟨hLin, hB⟩ := Main.memL_append.mp hL'
    have hx : TbReadsAt rd (ofK (addressOfIndex ec)) xs := hLin (ec, xs) (by simp)
    have hz : TbReadsAt rd (ofK (addressOfIndex ez)) r.2.1 := hLin (ez, r.2.1) (by simp)
    have hw : ∀ b ws, (b, ws) ∈ [(vbgEL fs fp, vbgLayersW depth cap0 xs (ofK (addressOfIndex ec))
        (vbgEP fs depth fp)), (vbgER fs depth fp, vbgRoundsW depth cap0 xs (ofK (addressOfIndex ec))),
        (vbgEP fs depth fp, vbgRowsW depth cap0 xs), (vbgEK fs depth fp, kmnWords),
        (vbgEB fs depth fp, vbgBndW), (vbgEO fs depth fp, vbgOddW),
        (vbgEV fs depth fp, vbgValsW depth cap0 xs)] → TbReadsAt rd (ofK (addressOfIndex b)) ws :=
      fun b ws h ↦ hB (b, ws) h
    have hReg : VbgR (RegionL (vbgL fs depth cap0 xs r.2.1 ec ez fp)) depth xs ec ez
        (vbgEL fs fp) (vbgER fs depth fp) (vbgEP fs depth fp) (vbgEK fs depth fp) :=
      ⟨fun i hi ↦ by
          rw [hreg]; exact regionL_append_left ⟨(ez, r.2.1), by simp, by simp, by rw [hrp]; omega⟩,
        fun i hi ↦ own fp (vbgEP fs depth fp) (vbgRowsW depth cap0 xs) (by simp) i (by rw [hlp]; exact hi),
        fun i hi ↦ by
          rw [hreg]; exact regionL_append_left ⟨(ec, xs), by simp, by simp, by simpa using hi⟩,
        fun i hi ↦ own fp (vbgEL fs fp) (vbgLayersW depth cap0 xs (ofK (addressOfIndex ec)) (vbgEP fs depth fp)) (by simp) i (by rw [vbgLayersW_length hcl]; exact hi),
        fun i hi ↦ own fp (vbgER fs depth fp) (vbgRoundsW depth cap0 xs (ofK (addressOfIndex ec))) (by simp) i (by rw [hlr]; exact hi),
        fun i hi ↦ own fp (vbgEK fs depth fp) kmnWords (by simp) i (by simpa [kmnWords] using hi)⟩
    have hLw := hw (vbgEL fs fp) (vbgLayersW depth cap0 xs (ofK (addressOfIndex ec)) (vbgEP fs depth fp)) (by simp)
    have hRw := hw (vbgER fs depth fp) (vbgRoundsW depth cap0 xs (ofK (addressOfIndex ec))) (by simp)
    have hPw := hw (vbgEP fs depth fp) (vbgRowsW depth cap0 xs) (by simp)
    have hKw := hw (vbgEK fs depth fp) kmnWords (by simp)
    have hBw := hw (vbgEB fs depth fp) vbgBndW (by simp)
    have hOw := hw (vbgEO fs depth fp) vbgOddW (by simp)
    have hVw := hw (vbgEV fs depth fp) (vbgValsW depth cap0 xs) (by simp)
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := vbg_run (tabs := tabs) hd2 hd hκ hrun hc hlow hx hz hLw hRw
      hPw hKw hBw hOw hVw hReg
    refine ⟨⟨h1, h2, h3, h4.trans ?_, h5⟩, h6,
      vbg_memLay hd hcl hpl hLw hRw hPw hKw hBw hOw hVw⟩
    simp [bases, vbgSizes, vbgEL, vbgER, vbgEP, vbgEK, vbgEB, vbgEO, vbgEV, Nat.add_assoc]

/-- What `verify_bus_gkr` returns: the capacity `cap'`, the cursor `cur` and a pointer to a buffer
of its returned layout holding the values `vals`. -/
def VbgOut (cap' : List E) (cur : E) (vals : List E) (rets : List E) (Lout : List (ℕ × List E)) :
    Prop :=
  ∃ b, rets = cap' ++ [cur, ofK (addressOfIndex b)] ∧ (b, vals) ∈ Lout

/-- **`verify_bus_gkr` is complete, placed** (TRIAGE G #43): at `2 ≤ depth ≤ 32`, on memories
defined below `2^κ`, `κ ≥ 6`, an accepting run of `gkrPhase depth` from a carried capacity `cap0`
reading the words `xs` at the cursor `g^ec`, the run's point at `zeta = g^ez`, its seven buffers
at the bump allocator's positions holding their honest words (`vbgOwnW`), returned. It returns
the run's capacity, the cursor past `xs` and a returned buffer holding the run's values. -/
theorem verify_bus_gkr_completeAt {κ depth : ℕ} (hd2 : 2 ≤ depth) (hd : depth ≤ 32) (hκ : 6 ≤ κ)
    {cap0 xs : List E} {r : E × List E × List E} {cap' : List E}
    (hrun : RunsTo (gkrPhase depth) ⟨cap0, []⟩ xs r ⟨cap', []⟩)
    (hc : ∃ sp, (⟨cap0, []⟩ : Fs).Carries sp) (tabs : E) (ec ez : ℕ) :
    CompleteAtD fs cert κ "verify_bus_gkr" [(ec, xs), (ez, r.2.1)]
      (cap0 ++ [ofK (addressOfIndex ec), gen ^ depth, ofK (addressOfIndex ez), tabs])
      (VbgOut cap' (ofK (addressOfIndex ec) * gen ^ xs.length) r.2.2) := by
  have hcl : cap0.length = 5 := by
    obtain ⟨sp, hsp⟩ := hc
    have hsc : capOf sp.state = cap0 := hsp.1
    rw [← hsc]; simp [capOf]
  have hvals : vbgValsW depth cap0 xs = r.2.2 := by
    obtain ⟨-, -, -, -, -, -, hr, -⟩ := gk_walk hrun hc
    rw [hr]; rfl
  obtain ⟨hown, hbufs, hfacts⟩ := vbg_lift_facts (fs := fs) hd2 hd hκ hrun hc tabs ec ez
  exact flat_completeAtOut vbgFlat [(ec, xs), (ez, r.2.1)] _
    (fun fp ↦ cap' ++ [ofK (addressOfIndex ec) * gen ^ xs.length,
      ofK (addressOfIndex (vbgEV fs depth fp))]) _ (by simp [vbgFlat, hcl]) (vbgSizes depth)
    (fun fp ↦ vbgOwnW depth cap0 xs (ofK (addressOfIndex ec)) (vbgEP fs depth fp)) hown
    (fun fp ↦ ⟨vbgEV fs depth fp, rfl, by
      rw [show fp + fs vbgFlat.name = fp + fs "verify_bus_gkr" from rfl, vbg_bufL, ← hvals]
      simp⟩)
    (fun fp ↦ vbgW (ofK (addressOfIndex (vbgEL fs fp))) (ofK (addressOfIndex (vbgER fs depth fp)))
      (ofK (addressOfIndex (vbgEP fs depth fp))) (ofK (addressOfIndex (vbgEK fs depth fp)))
      (ofK (addressOfIndex (vbgEB fs depth fp))) (ofK (addressOfIndex (vbgEO fs depth fp)))
      (ofK (addressOfIndex (vbgEV fs depth fp))))
    (vbgBufs fs depth xs ec) hbufs (fun fp rd hlow hL ↦ (hfacts fp rd hlow hL).1)

end
end LeanVM.Guest.B1.Tables
