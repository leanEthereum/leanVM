/-
  LeanVM.Guest.B1.Gkr.VbgAt

  `verify_bus_gkr` is complete in the uniform placed form (`CompleteAtD`).
-/

module

public import LeanVM.Guest.B1.Gkr.VbgLoads
public import LeanVM.Guest.B1.Gkr.VbgL7
public import LeanVM.Guest.B1.Tables.Kids.Loop8
public import LeanVM.Guest.B1.Tables.FlatLiftOut
public import LeanVM.Guest.Data.NameStrings

/-!
# `verify_bus_gkr`, placed (TRIAGE G #43)

`vbg_run`: at `2 ≤ depth`, on a memory defined below `2^κ` (`κ ≥ 6`, the range check of
`g^depth`) holding the cursor's words, the point at `zeta` and the eight buffers whole
(`vbgOwnW`), the honest valuation (`vbgFlat.σ`, the allocations answered by the buffers'
pointers) satisfies every statement with its calls by relations loading from a region `R`
holding the cursor's words, the point and the buffers, its loads land inside the buffers
(`vbg_loadOk`, `vbg_ptrs`; the radix-four arm's fourteen words past the cursor are the run's at
`depth ≥ 2`, `gk_xs_len`), its allocations are the buffers and it returns the accepting run's
capacity, cursor and the values' buffer. `verify_bus_gkr_loop1`'s relation loads from `R`
(`loop8_relIn`), and `verify_bus_gkr_loop0`'s (`vbg_loop7_relIn`).

`verify_bus_gkr_completeAt`: `flat_completeAtOut` for `vbgFlat`, the buffers at the bump
allocator's positions from `fp + fs "verify_bus_gkr"`, returned (`VbgOut`: the values' buffer is
among them).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Core LeanVM.Core.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd LeanVM.Core.Memory
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

/-- `verify_bus_gkr_loop0`'s call. -/
def vbgCall7 : Stmt :=
  .callIf (.n 419) name% «verify_bus_gkr_loop0» [.n 420, .n 165, .n 417, .n 173, .n 8, .n 176,
    .n 52, .n 187, .n 6, .n 53]

/-- `verify_bus_gkr_loop1`'s call. -/
def vbgCall8 : Stmt := .callIf (.n 430) name% «verify_bus_gkr_loop1» [.n 431, .n 6, .n 7, .n 428]

/-- Every statement is an atom, an `ite` of atoms, or one of the two calls. -/
def vbgKindB (s : Stmt) : Bool :=
  atomsDeep s || tbStmtsEqb [s] [vbgCall7] || tbStmtsEqb [s] [vbgCall8]

theorem vbg_kinds : vbgPre.all vbgKindB = true := by decide +kernel

theorem vbg_allocs : vbgPre.filterMap Main.Stmt.allocSz = [(.n 53, .inl 8), (.n 62, .inl 33),
    (.n 63, .inl 33), (.n 130, .inl 33), (.n 173, .inr (.n 172)), (.n 176, .inr (.n 175)),
    (.n 185, .inr (.n 184)), (.n 432, .inl 3)] := by
  decide +kernel

theorem vbgRecs_le : ∀ d < 33, vbgRecs d ≤ 256 := by decide +kernel

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
    p = .n p.idx ∧ ((p.idx = 5 ∧ off < 14) ∨ (p.idx = 53 ∧ off < 8) ∨
      (((p.idx = 62 ∨ p.idx = 63) ∨ p.idx = 130) ∧ off < 33) ∨
      (((p.idx = 164 ∨ p.idx = 174) ∨ p.idx = 186) ∧ off = 0) ∨ (p.idx = 173 ∧ off < 13) ∨
      (p.idx = 185 ∧ off < 42) ∨ (p.idx = 426 ∧ off < 10) ∨ (p.idx = 432 ∧ off < 3)) := by
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
    (ec ez eL eR eP eK eB eO eN eV : ℕ) : Val :=
  vbgFlat.σ rd (vbgW (ofK (addressOfIndex eL)) (ofK (addressOfIndex eR)) (ofK (addressOfIndex eP))
      (ofK (addressOfIndex eK)) (ofK (addressOfIndex eB)) (ofK (addressOfIndex eO))
      (ofK (addressOfIndex eN)) (ofK (addressOfIndex eV)))
    (cap0 ++ [ofK (addressOfIndex ec), gen ^ depth, ofK (addressOfIndex ez), tabs])

/-- The values the calls of `verify_bus_gkr_loop0` and `verify_bus_gkr_loop1` start and end at,
and `verify_bus_gkr_loop0`'s arguments. -/
def VbgVals (σ : Val) (depth eL eR eK : ℕ) (tabs : E) : Prop :=
  σ (.n 420) = 1 ∧ σ (.n 165) = gen ^ ((depth - 1) / 2) ∧ σ (.n 417) = gen ^ (2 - depth % 2) ∧
    σ (.n 431) = 1 ∧ σ (.n 6) = gen ^ depth ∧ σ (.n 173) = ofK (addressOfIndex eL) ∧
    σ (.n 176) = ofK (addressOfIndex eR) ∧ σ (.n 53) = ofK (addressOfIndex eK) ∧
    σ (.n 8) = tabs ∧ σ (.n 187) = gen ^ (depth % 2) ∧
    σ (.n 419) = 1 + gen ^ ((depth - 1) / 2)

/-- The buffers of `verify_bus_gkr` its callees read in a region, and the cursor's words and the
point. -/
structure VbgR (R : ℕ → Prop) (depth : ℕ) (xs : List E) (ec ez eL eR eP eK : ℕ) : Prop where
  z : ∀ i < depth, R (ez + i)
  r : ∀ i < 40 * ((depth - 1) / 2 + 2), R (eP + i)
  x : ∀ i < xs.length, R (ec + i)
  l : ∀ i < 13 * ((depth - 1) / 2 + 1), R (eL + i)
  rr : ∀ i < 7 * vbgRecs depth, R (eR + i)
  k : ∀ i < 8, R (eK + i)

/-- **`verify_bus_gkr`'s honest valuation on a memory holding its words**: every statement holds,
its calls loading from `R`; its loads land inside its buffers; its allocations are the buffers; it
returns the accepting run's capacity, cursor and the values' buffer. -/
theorem vbg_run {depth κ : ℕ} (hd2 : 2 ≤ depth) (hd : depth ≤ 32) (hκ : 6 ≤ κ)
    {cap0 xs : List E} {r : E × List E × List E} {cap' : List E}
    (hrun : RunsTo (gkrPhase depth) ⟨cap0, []⟩ xs r ⟨cap', []⟩)
    (hc : ∃ sp, (⟨cap0, []⟩ : Fs).Carries sp) {tabs : E} {ec ez eL eR eP eK eB eO eN eV : ℕ}
    {rd : Reader} {R : ℕ → Prop} (hlow : LowDef κ rd)
    (hx : TbReadsAt rd (ofK (addressOfIndex ec)) xs)
    (hz : TbReadsAt rd (ofK (addressOfIndex ez)) r.2.1)
    (hL : TbReadsAt rd (ofK (addressOfIndex eL)) (vbgLayersW depth cap0 xs (ofK (addressOfIndex
        ec)) eP))
    (hR : TbReadsAt rd (ofK (addressOfIndex eR)) (vbgRoundsW depth cap0 xs (ofK
        (addressOfIndex ec))))
    (hP : TbReadsAt rd (ofK (addressOfIndex eP)) (vbgRowsW depth cap0 xs))
    (hK : TbReadsAt rd (ofK (addressOfIndex eK)) kmnWords)
    (hB : TbReadsAt rd (ofK (addressOfIndex eB)) vbgBndW)
    (hO : TbReadsAt rd (ofK (addressOfIndex eO)) vbgOddW)
    (hN : TbReadsAt rd (ofK (addressOfIndex eN)) vbgRlenW)
    (hV : TbReadsAt rd (ofK (addressOfIndex eV)) (vbgValsW depth cap0 xs))
    (hReg : VbgR R depth xs ec ez eL eR eP eK) :
    (∀ s ∈ vbgPre, VSH (coreProgram.RelIn rd R) rd
      (vbgσ rd depth cap0 tabs ec ez eL eR eP eK eB eO eN eV) s) ∧
    LoadsInBuf (vbgσ rd depth cap0 tabs ec ez eL eR eP eK eB eO eN eV)
      [(ofK (addressOfIndex ec), xs.length), (ofK (addressOfIndex eK), 8),
        (ofK (addressOfIndex eB), 33), (ofK (addressOfIndex eO), 33),
        (ofK (addressOfIndex eN), 33), (ofK (addressOfIndex eL), 13 * ((depth - 1) / 2 + 1)),
        (ofK (addressOfIndex eR), 7 * vbgRecs depth),
        (ofK (addressOfIndex eP), 40 * ((depth - 1) / 2 + 2)), (ofK (addressOfIndex eV), 3)]
      vbgEvL ∧
    (vbgPre.filterMap Main.Stmt.allocSz).map (fun x => x.2.elim id fun s =>
        logG (vbgσ rd depth cap0 tabs ec ez eL eR eP eK eB eO eN eV s)) =
      vbgSizes depth ∧
    ((vbgPre.filterMap Main.Stmt.allocSz).map Prod.fst).map
        (vbgσ rd depth cap0 tabs ec ez eL eR eP eK eB eO eN eV) =
      [ofK (addressOfIndex eK), ofK (addressOfIndex eB), ofK (addressOfIndex eO),
        ofK (addressOfIndex eN), ofK (addressOfIndex eL), ofK (addressOfIndex eR),
        ofK (addressOfIndex eP), ofK (addressOfIndex eV)] ∧
    vbgRets.map (vbgσ rd depth cap0 tabs ec ez eL eR eP eK eB eO eN eV) =
      cap' ++ [ofK (addressOfIndex ec) * gen ^ xs.length, ofK (addressOfIndex eV)] ∧
    VbgVals (vbgσ rd depth cap0 tabs ec ez eL eR eP eK eB eO eN eV) depth eL eR eK tabs := by
  obtain ⟨hcnt, hx2, hodd, hsteps, hend, hsF, hr, hplm⟩ := gk_walk hrun hc
  obtain ⟨sp, hsp⟩ := hc
  have hsc : capOf sp.state = cap0 := hsp.1
  have hcl : cap0.length = 5 := by rw [← hsc]; simp [capOf]
  have hpl : ∀ j ≤ depth / 2, (gkSl cap0 xs (depth % 2) j).2.1.point.length = 2 * j + depth % 2 :=
    gkSl_point_len (gkSl0_point_len cap0 xs (depth % 2) (by omega)) fun j hj ↦ (hsteps j hj).1
  have hm := vbg_memLay (eL := eL) (eR := eR) (eP := eP) (eK := eK) (eB := eB) (eO := eO)
    (eN := eN) (eV := eV) hd hcl hpl hL hR hP hK hB hO hN hV
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
      (ofK (addressOfIndex eN)) (ofK (addressOfIndex eV)) with hW
  have hσe : vbgσ rd depth cap0 tabs ec ez eL eR eP eK eB eO eN eV =
      B1.Val.ofArgs (ev rd W args vbgEvL) := rfl
  rw [hσe]
  set σ := B1.Val.ofArgs (ev rd W args vbgEvL) with hσ
  have hl : args.length = 9 := by rw [hargs]; simp [hcl]
  obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp vb_chk
  have hG : ∀ s ∈ vbgEvL, GoodS rd vbgS W σ s := by
    have h := (ev_spec rd W vbgEvL args (by rw [hl]; exact hc')).2.2
    rw [hl] at h
    exact h
  obtain ⟨e5, e6, e53, e62, e63, e130, e173, e176, e185, e432, e164, e174, e186, hsz⟩ :=
    vbg_ptrs hσ hG hcl hargs hW
  have g : ∀ a : Atom, vbgEvL.any (fun t ↦ tbStmtsEqb [.atom a] [t]) = true → Good rd vbgS W σ a :=
    fun a h ↦ hG _ (vbg_mem h)
  have e7 : σ (.n 7) = ofK (addressOfIndex ez) := by
    rw [hσ, ev_params rd W (by rw [hl]; exact hc') (by rw [hl]; omega), hargs]; simp [hcl]
  have e8 : σ (.n 8) = tabs := by
    rw [hσ, ev_params rd W (by rw [hl]; exact hc') (by rw [hl]; omega), hargs]; simp [hcl]
  have one : ∀ d : ℕ, vbgEvL.any (fun t ↦ tbStmtsEqb [.atom (.const (.n d) (word 1 0))] [t]) =
      true → σ (.n d) = 1 := fun d h ↦ by rw [← tb_word_one]; exact g _ h
  have c418 := one 418 (by decide +kernel)
  have c420 := one 420 (by decide +kernel)
  have c431 := one 431 (by decide +kernel)
  -- `loop_bounds[depth]`, `rounds_len[depth]`, `depth_odd[depth]`
  have r165 := good_read (g (.load (.n 165) (.n 164) 0) (by decide +kernel)) (by decide +kernel)
    (show LoadHolds rd (σ (.n 164)) 0 (gen ^ ((depth - 1) / 2)) by
      rw [e164, tb_loadHolds_mul_gen_pow, Nat.add_zero]
      have := hB depth (by simp [vbgBndW]; omega)
      simpa [vbgBndW] using this)
  have r175 := good_read (g (.load (.n 175) (.n 174) 0) (by decide +kernel)) (by decide +kernel)
    (show LoadHolds rd (σ (.n 174)) 0 (gen ^ (7 * vbgRecs depth)) by
      rw [e174, tb_loadHolds_mul_gen_pow, Nat.add_zero]
      have := hN depth (by simp [vbgRlenW]; omega)
      simpa [vbgRlenW] using this)
  have r187 := good_read (g (.load (.n 187) (.n 186) 0) (by decide +kernel)) (by decide +kernel)
    (show LoadHolds rd (σ (.n 186)) 0 (gen ^ (depth % 2)) by
      rw [e186, tb_loadHolds_mul_gen_pow, Nat.add_zero]
      have := hO depth (by simp [vbgOddW]; omega)
      simpa [vbgOddW] using this)
  obtain ⟨e172, e184, e426⟩ := hsz _ r165.1
  have a419 : σ (.n 419) = σ (.n 418) + σ (.n 165) :=
    g (.add (.n 419) (.n 418) (.n 165)) (by decide +kernel)
  have c416 : σ (.n 416) = gen ^ 2 := by
    rw [← tb_word_four]; exact g (.const (.n 416) (word 4 0)) (by decide +kernel)
  have e417 : σ (.n 417) = gen ^ (2 - depth % 2) := by
    have h := g (.mul (.n 416) (.n 417) (.n 187)) (by decide +kernel)
    have hn : ¬ ((V.n 417).idx < (V.n 416).idx ∧ (V.n 187).idx < (V.n 416).idx) := by
      show ¬ (417 < 416 ∧ 187 < 416); omega
    simp only [Good, hn, ↓reduceIte] at h
    rw [h, c416, r187.1]
    have hs : depth % 2 ≤ 2 := by omega
    rw [show (gen : E) ^ 2 = gen ^ (2 - depth % 2) * gen ^ (depth % 2) by
        rw [← pow_add, Nat.sub_add_cancel hs],
      mul_assoc, mul_inv_cancel₀ (gen_pow_ne_zero _), mul_one]
  -- the last record's row
  have hLb := tbReadsAt_flatMap_eq (w := 13) _ ((depth - 1) / 2 + 1)
    (fun c _ ↦ vbgSlotW_length hcl _) (by unfold vbgLayersW at hL; exact hL)
  have hdb := hLb ((depth - 1) / 2) (by omega)
  have hrow : LoadHolds rd (σ (.n 426)) 9 (ofK (addressOfIndex eP) *
      gen ^ (40 * ((depth - 1) / 2 + 1 - depth % 2 + depth % 2))) := by
    rw [e426]
    have := hdb 9 (by rw [vbgSlotW_length hcl]; omega)
    rw [← List.getD_eq_getElem _ 0] at this
    have inv := gkSl_inv (xs := xs) (sh := depth % 2) hcl ((depth - 1) / 2 + 1 - depth % 2)
    unfold vbgSlotW at this
    rwa [gkSlotWords_getD9 inv.1 inv.2.1] at this
  have r428 := good_read (g (.load (.n 428) (.n 426) 9) (by decide +kernel)) (by decide +kernel) hrow
  refine ⟨fun s hs ↦ ?_, fun d p off hm ↦ ?_, ?_, ?_, hrt, c420, r165.1, e417, c431, e6, e173,
    e176, e53, e8, r187.1, by rw [a419, c418, r165.1]⟩
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
          rw [a419, c418, r165.1, h0, pow_zero, e_add_self]
        · exact h0
      simp only [List.map_cons, List.map_nil, c420, r165.1, e417, e173, e8, e176, r187.1, e6,
        e53] at h ⊢
      exact vbg_loop7_relIn hd hrun ⟨sp, hsp⟩ hm hReg.x hReg.l hReg.rr hReg.r hReg.k hm0 h
    · have e := tbStmtsEqb_sound h8
      simp only [List.cons.injEq, and_true] at e
      subst e
      refine ⟨hv.1, fun hne ↦ ?_⟩
      obtain ⟨n, h⟩ := hv.2 hne
      simp only [List.map_cons, List.map_nil, c431, e6, e7, r428.1] at h ⊢
      rw [show (1 : E) = gen ^ 0 from (pow_zero _).symm] at h ⊢
      rw [tb_ofK_gpow_mul] at h ⊢
      exact loop8_relIn (ptrIn_ofK hReg.z) (ptrIn_ofK fun i hi ↦ by
        rw [Nat.add_assoc]; exact hReg.r _ (by omega)) n 0 (by omega) h
  · -- the loads
    obtain ⟨hp, hcls⟩ := vbg_load_cls hm
    rw [hp]
    rcases hcls with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨(h1 | h1) | h1, h2⟩ | ⟨(h1 | h1) | h1, h2⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1]
    · exact ⟨(ofK (addressOfIndex ec), xs.length), List.mem_cons_self, 0,
        by rw [e5]; simp, by omega⟩
    · exact ⟨(ofK (addressOfIndex eK), 8), by simp, 0, by rw [e53]; simp, by omega⟩
    · exact ⟨(ofK (addressOfIndex eB), 33), by simp, 0, by rw [e62]; simp, by omega⟩
    · exact ⟨(ofK (addressOfIndex eO), 33), by simp, 0, by rw [e63]; simp, by omega⟩
    · exact ⟨(ofK (addressOfIndex eN), 33), by simp, 0, by rw [e130]; simp, by omega⟩
    · exact ⟨(ofK (addressOfIndex eB), 33), by simp, depth, e164, by omega⟩
    · exact ⟨(ofK (addressOfIndex eN), 33), by simp, depth, e174, by omega⟩
    · exact ⟨(ofK (addressOfIndex eO), 33), by simp, depth, e186, by omega⟩
    · exact ⟨(ofK (addressOfIndex eL), 13 * ((depth - 1) / 2 + 1)), by simp, 0,
        by rw [e173]; simp, by omega⟩
    · exact ⟨(ofK (addressOfIndex eP), 40 * ((depth - 1) / 2 + 2)), by simp, 0,
        by rw [e185]; simp, by omega⟩
    · exact ⟨(ofK (addressOfIndex eL), 13 * ((depth - 1) / 2 + 1)), by simp, 13 * ((depth - 1) / 2),
        e426, by omega⟩
    · exact ⟨(ofK (addressOfIndex eV), 3), by simp, 0, by rw [e432]; simp, by omega⟩
  · -- the sizes
    have hrl := vbgRecs_le depth (by omega)
    rw [vbg_allocs]
    simp only [List.map_cons, List.map_nil, Sum.elim_inr, Sum.elim_inl, id, e172, r175.1, e184,
      vbgSizes]
    rw [gen_pow_eq_ofK, gen_pow_eq_ofK, gen_pow_eq_ofK, logG_spec (by omega), logG_spec (by omega),
      logG_spec (by omega)]
  · -- the bases
    rw [vbg_allocs]
    simp only [List.map_cons, List.map_nil, e53, e62, e63, e130, e173, e176, e185, e432]

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- `verify_bus_gkr`'s buffers' first words at `fp`, in allocation order: `k_mod_next`,
`loop_bounds`, `depth_odd`, `rounds_len`, `layers`, the round records, the rows, the values. -/
def vbgEK (fs : String → ℕ) (fp : ℕ) : ℕ := fp + fs "verify_bus_gkr"
def vbgEB (fs : String → ℕ) (fp : ℕ) : ℕ := vbgEK fs fp + 8
def vbgEO (fs : String → ℕ) (fp : ℕ) : ℕ := vbgEB fs fp + 33
def vbgEN (fs : String → ℕ) (fp : ℕ) : ℕ := vbgEO fs fp + 33
def vbgEL (fs : String → ℕ) (fp : ℕ) : ℕ := vbgEN fs fp + 33
def vbgER (fs : String → ℕ) (depth fp : ℕ) : ℕ := vbgEL fs fp + 13 * ((depth - 1) / 2 + 1)
def vbgEP (fs : String → ℕ) (depth fp : ℕ) : ℕ := vbgER fs depth fp + 7 * vbgRecs depth
def vbgEV (fs : String → ℕ) (depth fp : ℕ) : ℕ := vbgEP fs depth fp + 40 * ((depth - 1) / 2 + 2)

/-- `verify_bus_gkr`'s layout at `fp`: the cursor's words, the point, the buffers. -/
noncomputable def vbgL (fs : String → ℕ) (depth : ℕ) (cap0 xs point : List E) (ec ez fp : ℕ) :
    List (ℕ × List E) :=
  flatL "verify_bus_gkr" [(ec, xs), (ez, point)] (vbgSizes depth)
    (fun fp ↦ vbgOwnW depth cap0 xs (ofK (addressOfIndex ec)) (vbgEP fs depth fp)) fs fp

/-- The buffers `verify_bus_gkr` loads from, at `fp`. -/
noncomputable def vbgBufs (fs : String → ℕ) (depth : ℕ) (xs : List E) (ec fp : ℕ) : List (E × ℕ) :=
  [(ofK (addressOfIndex ec), xs.length), (ofK (addressOfIndex (vbgEK fs fp)), 8),
    (ofK (addressOfIndex (vbgEB fs fp)), 33), (ofK (addressOfIndex (vbgEO fs fp)), 33),
    (ofK (addressOfIndex (vbgEN fs fp)), 33),
    (ofK (addressOfIndex (vbgEL fs fp)), 13 * ((depth - 1) / 2 + 1)),
    (ofK (addressOfIndex (vbgER fs depth fp)), 7 * vbgRecs depth),
    (ofK (addressOfIndex (vbgEP fs depth fp)), 40 * ((depth - 1) / 2 + 2)),
    (ofK (addressOfIndex (vbgEV fs depth fp)), 3)]

theorem vbg_bufL (fs : String → ℕ) (depth : ℕ) (cap0 xs : List E) (cur : E) (fp : ℕ) :
    bufL (fp + fs "verify_bus_gkr") (vbgSizes depth)
      (vbgOwnW depth cap0 xs cur (vbgEP fs depth fp)) =
      [(vbgEK fs fp, kmnWords), (vbgEB fs fp, vbgBndW), (vbgEO fs fp, vbgOddW),
        (vbgEN fs fp, vbgRlenW), (vbgEL fs fp, vbgLayersW depth cap0 xs cur (vbgEP fs depth fp)),
        (vbgER fs depth fp, vbgRoundsW depth cap0 xs cur),
        (vbgEP fs depth fp, vbgRowsW depth cap0 xs),
        (vbgEV fs depth fp, vbgValsW depth cap0 xs)] := by
  simp [bufL, bases, vbgSizes, vbgOwnW, vbgEL, vbgER, vbgEP, vbgEK, vbgEB, vbgEO, vbgEN, vbgEV,
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
        (vbgEK fs fp) (vbgEB fs fp) (vbgEO fs fp) (vbgEN fs fp) (vbgEV fs depth fp)
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
      VbgVals σ depth (vbgEL fs fp) (vbgER fs depth fp) (vbgEK fs fp) tabs ∧
      MemLay rd (vbgLay depth cap0 xs (ofK (addressOfIndex ec)) (vbgEL fs fp) (vbgER fs depth fp)
        (vbgEP fs depth fp) (vbgEK fs fp) (vbgEB fs fp) (vbgEO fs fp) (vbgEN fs fp)
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
  have hll : ∀ eP, (vbgLayersW depth cap0 xs (ofK (addressOfIndex ec)) eP).length =
      13 * ((depth - 1) / 2 + 1) := fun _ ↦ vbgLayersW_length hcl
  have hlr : (vbgRoundsW depth cap0 xs (ofK (addressOfIndex ec))).length = 7 * vbgRecs depth :=
    vbgRoundsW_length (by omega)
  have hlp : (vbgRowsW depth cap0 xs).length = 40 * ((depth - 1) / 2 + 2) :=
    vbgRowsW_length hd hpl
  have hown : ∀ fp, List.Forall₂ (fun c s => c.length ≤ s)
      (vbgOwnW depth cap0 xs (ofK (addressOfIndex ec)) (vbgEP fs depth fp)) (vbgSizes depth) := by
    intro fp
    simp only [vbgOwnW, vbgSizes, List.forall₂_cons, List.Forall₂.nil, and_true]
    exact ⟨by simp [kmnWords], by simp [vbgBndW], by simp [vbgOddW], by simp [vbgRlenW],
      by rw [hll], by rw [hlr], by rw [hlp], by rw [hvl]⟩
  have hreg : ∀ fp, vbgL fs depth cap0 xs r.2.1 ec ez fp = [(ec, xs), (ez, r.2.1)] ++
      [(vbgEK fs fp, kmnWords), (vbgEB fs fp, vbgBndW), (vbgEO fs fp, vbgOddW),
        (vbgEN fs fp, vbgRlenW),
        (vbgEL fs fp, vbgLayersW depth cap0 xs (ofK (addressOfIndex ec)) (vbgEP fs depth fp)),
        (vbgER fs depth fp, vbgRoundsW depth cap0 xs (ofK (addressOfIndex ec))),
        (vbgEP fs depth fp, vbgRowsW depth cap0 xs),
        (vbgEV fs depth fp, vbgValsW depth cap0 xs)] := fun fp ↦ by
    rw [← vbg_bufL]; rfl
  have own : ∀ fp b (ws : List E), (b, ws) ∈
      [(vbgEK fs fp, kmnWords), (vbgEB fs fp, vbgBndW), (vbgEO fs fp, vbgOddW),
        (vbgEN fs fp, vbgRlenW),
        (vbgEL fs fp, vbgLayersW depth cap0 xs (ofK (addressOfIndex ec)) (vbgEP fs depth fp)),
        (vbgER fs depth fp, vbgRoundsW depth cap0 xs (ofK (addressOfIndex ec))),
        (vbgEP fs depth fp, vbgRowsW depth cap0 xs),
        (vbgEV fs depth fp, vbgValsW depth cap0 xs)] →
      ∀ i < ws.length, RegionL (vbgL fs depth cap0 xs r.2.1 ec ez fp) (b + i) :=
    fun fp b ws hm i hi ↦ by
      rw [hreg]; exact regionL_append_right ⟨(b, ws), hm, by omega, by simpa using hi⟩
  have ownL := fun fp ↦ own fp (vbgEL fs fp)
    (vbgLayersW depth cap0 xs (ofK (addressOfIndex ec)) (vbgEP fs depth fp)) (by simp)
  have ownR := fun fp ↦ own fp (vbgER fs depth fp)
    (vbgRoundsW depth cap0 xs (ofK (addressOfIndex ec))) (by simp)
  have ownP := fun fp ↦ own fp (vbgEP fs depth fp) (vbgRowsW depth cap0 xs) (by simp)
  have ownK := fun fp ↦ own fp (vbgEK fs fp) kmnWords (by simp)
  refine ⟨hown, ?_, ?_⟩
  · -- the buffers lie in the layout
    intro fp q hq
    simp only [vbgBufs, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨ec, rfl, fun i hi ↦ by
        rw [hreg]; exact regionL_append_left ⟨(ec, xs), by simp, by omega, by simpa using hi⟩⟩
    · exact ⟨_, rfl, fun i hi ↦ ownK fp i (by simpa [kmnWords] using hi)⟩
    · exact ⟨_, rfl, fun i hi ↦ own fp (vbgEB fs fp) vbgBndW (by simp) i
        (by simpa [vbgBndW] using hi)⟩
    · exact ⟨_, rfl, fun i hi ↦ own fp (vbgEO fs fp) vbgOddW (by simp) i
        (by simpa [vbgOddW] using hi)⟩
    · exact ⟨_, rfl, fun i hi ↦ own fp (vbgEN fs fp) vbgRlenW (by simp) i
        (by simpa [vbgRlenW] using hi)⟩
    · exact ⟨_, rfl, fun i hi ↦ ownL fp i (by rw [hll]; exact hi)⟩
    · exact ⟨_, rfl, fun i hi ↦ ownR fp i (by rw [hlr]; exact hi)⟩
    · exact ⟨_, rfl, fun i hi ↦ ownP fp i (by rw [hlp]; exact hi)⟩
    · exact ⟨_, rfl, fun i hi ↦ own fp (vbgEV fs depth fp) (vbgValsW depth cap0 xs) (by simp) i
        (by rw [hvl]; exact hi)⟩
  · -- the run
    intro fp rd hlow hL
    have hL' := hL
    rw [hreg] at hL'
    obtain ⟨hLin, hB⟩ := Main.memL_append.mp hL'
    have hx : TbReadsAt rd (ofK (addressOfIndex ec)) xs := hLin (ec, xs) (by simp)
    have hz : TbReadsAt rd (ofK (addressOfIndex ez)) r.2.1 := hLin (ez, r.2.1) (by simp)
    have hReg : VbgR (RegionL (vbgL fs depth cap0 xs r.2.1 ec ez fp)) depth xs ec ez
        (vbgEL fs fp) (vbgER fs depth fp) (vbgEP fs depth fp) (vbgEK fs fp) :=
      ⟨fun i hi ↦ by
          rw [hreg]; exact regionL_append_left ⟨(ez, r.2.1), by simp, by simp, by rw [hrp]; omega⟩,
        fun i hi ↦ ownP fp i (by rw [hlp]; exact hi),
        fun i hi ↦ by
          rw [hreg]; exact regionL_append_left ⟨(ec, xs), by simp, by simp, by simpa using hi⟩,
        fun i hi ↦ ownL fp i (by rw [hll]; exact hi),
        fun i hi ↦ ownR fp i (by rw [hlr]; exact hi),
        fun i hi ↦ ownK fp i (by simpa [kmnWords] using hi)⟩
    have hLw := hB (vbgEL fs fp, vbgLayersW depth cap0 xs (ofK (addressOfIndex ec))
      (vbgEP fs depth fp)) (by simp)
    have hRw := hB (vbgER fs depth fp, vbgRoundsW depth cap0 xs (ofK (addressOfIndex ec)))
      (by simp)
    have hPw := hB (vbgEP fs depth fp, vbgRowsW depth cap0 xs) (by simp)
    have hKw := hB (vbgEK fs fp, kmnWords) (by simp)
    have hBw := hB (vbgEB fs fp, vbgBndW) (by simp)
    have hOw := hB (vbgEO fs fp, vbgOddW) (by simp)
    have hNw := hB (vbgEN fs fp, vbgRlenW) (by simp)
    have hVw := hB (vbgEV fs depth fp, vbgValsW depth cap0 xs) (by simp)
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := vbg_run (tabs := tabs) hd2 hd hκ hrun hc hlow hx hz hLw hRw
      hPw hKw hBw hOw hNw hVw hReg
    refine ⟨⟨h1, h2, h3, h4.trans ?_, h5⟩, h6,
      vbg_memLay hd hcl hpl hLw hRw hPw hKw hBw hOw hNw hVw⟩
    simp [bases, vbgSizes, vbgEL, vbgER, vbgEP, vbgEK, vbgEB, vbgEO, vbgEN, vbgEV, Nat.add_assoc]

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
      (ofK (addressOfIndex (vbgEP fs depth fp))) (ofK (addressOfIndex (vbgEK fs fp)))
      (ofK (addressOfIndex (vbgEB fs fp))) (ofK (addressOfIndex (vbgEO fs fp)))
      (ofK (addressOfIndex (vbgEN fs fp))) (ofK (addressOfIndex (vbgEV fs depth fp))))
    (vbgBufs fs depth xs ec) hbufs (fun fp rd hlow hL ↦ (hfacts fp rd hlow hL).1)

end
end LeanVM.Guest.B1.Tables
