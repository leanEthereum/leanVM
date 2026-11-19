module

public import NativeVm.Code.Phase6.OpenRows

/-!
# A Keccak opening and the final check

`openC first sw wb` refines `keccakOpen logSteps claim first (2 - first) value` (`open_refines`):
the slot sumcheck (`qkeccakSlotBits` rounds, its claim at `eSC`, its point at `eSlot`; the word at
`ePtN` kept at `eKd` meanwhile, as the plain sumcheck reads it), then the slot weights' table (the
claim's two segment weights at `sw`, its bit weights at `wb`; `pure_rows`) folded at the slot point,
one `multilinearEval` per bit position (`colC_spec`), the `64` weights at `eOW`.

`finC` checks `multilinearEval mu low · dot weights slices` against the claim at `eSC`
(`fin_refines`).

Both write only `OpenW`'s elements; `finC` keeps the slot point.
-/

@[expose] public section

namespace NativeVm.Code.P6

open Native NativeVm.Model NativeVm.Code LeanVM.Parameters LeanVM.Protocol.Verifier Finset
open NativeVm.Transcript (wd wdisp Env rf_trans)
open NativeVm.Field (eOf emle emul emul_spec eRegs)

variable {env : Env} {inp : Input} {s0 s : QState} {t : TState} {g : Nat → EW}

/-! ## The model's side -/

/-- What an element outside `OpenW` is not. -/
theorem notOpen {i : Nat} (h : ¬ OpenW i) : i ≠ eKd ∧ i ≠ eKn ∧ ¬ Tmp i ∧
    (i < eSlot ∨ eSlot + 6 ≤ i) ∧ (i < eG ∨ eWF ≤ i) ∧ (i < eOW ∨ eOW + 64 ≤ i) := by
  refine ⟨fun e ↦ h (.inr (.inr (.inl e))), fun e ↦ h (.inr (.inl e)), fun e ↦ h (.inl e), ?_, ?_, ?_⟩
  · by_contra c; exact h (.inr (.inr (.inr (.inl (by omega)))))
  · by_contra c; exact h (.inr (.inr (.inr (.inr (.inl (by omega))))))
  · by_contra c; exact h (.inr (.inr (.inr (.inr (.inr (by omega))))))

/-- The last row of the fold of `keccakOpen`'s rows has `64` entries. -/
theorem openRows_size : ∀ (L : List EW) (rows : Array (Array EW)),
    rows.size = 2 ^ L.length → (∀ r < rows.size, (rows.getD r #[]).size = 64) →
    ((L.foldl (fun rows challenge ↦ (Array.range (rows.size / 2)).map fun i ↦
      Array.zipWith (fun lo hi ↦ lo + challenge * (lo + hi)) (rows.getD (2 * i) #[])
        (rows.getD (2 * i + 1) #[])) rows).getD 0 #[]).size = 64
  | [], rows, hs, hw => by
    rw [List.length_nil, Nat.pow_zero] at hs
    exact hw 0 (by omega)
  | c :: L, rows, hs, hw => by
    have hs' : rows.size / 2 = 2 ^ L.length := by
      rw [hs, List.length_cons, Nat.pow_succ, Nat.mul_div_cancel _ (by decide)]
    have h2 : ∀ i < rows.size / 2, 2 * i + 1 < rows.size := fun i hi ↦ by omega
    rw [List.foldl_cons]
    exact openRows_size L _ (by rw [Array.size_map, Array.size_range, hs']) fun r hr ↦ by
      rw [Array.size_map, Array.size_range] at hr
      rw [getD_map_range _ _ _ hr, Array.size_zipWith, hw _ (by have := h2 r hr; omega),
        hw _ (h2 r hr), Nat.min_self]

/-- **The table's entry is `keccakSlotWeights`'**: row `r`'s segment weight times the bit weight. -/
theorem rowW_slot {logSteps : Nat} {claim : KeccakClaimW} {first sw r z : Nat} (hf : first ≤ 1)
    (hseg : ∀ k < 2, g (sw + k) =
      (eqKernel (claim.point.extract (logSteps - 4) claim.point.size)).getD k 0) :
    (claim.weights.getD (z + 64 * (r % 25)) 0).toE * (rowW first sw g r).toE =
      (slotRow logSteps claim first (2 - first) r z).toE := by
  have hw : z + 64 * (r % 25) = 64 * (r % 25) + z := by omega
  have s0' : g sw = (eqKernel (claim.point.extract (logSteps - 4) claim.point.size)).getD 0 0 := by
    simpa using hseg 0 (by omega)
  have s1' := hseg 1 (by omega)
  rw [hw]
  unfold slotRow rowW
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hf with rfl | rfl <;>
    simp only [Nat.sub_zero, Nat.add_sub_cancel] <;> split_ifs <;>
    first
    | (exfalso; omega)
    | (simp only [NativeVm.Equiv.EW.toE_zero, mul_zero])
    | (rw [NativeVm.Equiv.EW.toE_mul, mul_comm, show r / 25 = 0 by omega, s0'])
    | (rw [NativeVm.Equiv.EW.toE_mul, mul_comm, show r / 25 = 1 by omega, s1'])
    | (rw [NativeVm.Equiv.EW.toE_mul, mul_comm, show r / 25 - 1 = 0 by omega, s0'])

/-! ## The opening -/

/-- An opening from segment `first`, the segment weights at `sw`, the bit weights at `wb`. -/
def openC (first sw wb : Nat) : List Stmt :=
  blk (cpEl ePtN eKd) :: blk (setW ePtN 0) :: scP 3 eSlot 6 :: blk (cpEl eKd ePtN) ::
    blk (rowsC first sw wb) :: colC

theorem open_refines (hin : Inputs env inp s0.mem) {first sw wb : Nat} (hf : first ≤ 1)
    (hsw : sw + 2 ≤ eSlot) (hsw' : ¬ OpenW sw ∧ ¬ OpenW (sw + 1))
    (hwb : ∀ j < 1600, ¬ OpenW (wb + j)) (hwb' : wb + 1600 ≤ scrN)
    (logSteps : Nat) (claim : KeccakClaimW) (value : EW) (g : Nat → EW) (hsc : g eSC = value)
    (hseg : ∀ k < 2, g (sw + k) =
      (eqKernel (claim.point.extract (logSteps - 4) claim.point.size)).getD k 0)
    (hw : ∀ j < 1600, g (wb + j) = claim.weights.getD j 0) :
    Refines (St env s0 g) (blk (openC first sw wb))
      (keccakOpen logSteps claim first (2 - first) value)
      (fun r t s ↦ ∃ g', St env s0 g' t s ∧ r.1.size = 6 ∧
        (∀ i < 6, g' (eSlot + i) = r.1.getD i 0) ∧ r.2.1.size = 64 ∧
        (∀ z < 64, g' (eOW + z) = r.2.1.getD z 0) ∧ g' eSC = r.2.2 ∧
        ∀ i, ¬ OpenW i → g' i = g i)
      (Kept env rs6 s0) := by
  have hN := scrN_lt
  set g1 := Function.update (Function.update g eKd (g ePtN)) ePtN (EW.ofK (0 : Nat).toUInt64)
    with hg1
  unfold Model.keccakOpen
  rw [qkeccakSlotBits_eq]
  refine Pure6.then (pure_cp hin (by p6_omega) (by p6_omega)) (Pure6.then
    (pure_setW hin (by p6_omega)) (Refines.blk_cons (scP_refines env inp s0 hin (np := 0)
      (by omega) (by p6_omega) (by p6_omega) value g1
      (by rw [hg1, Function.update_of_ne (by p6_ne), Function.update_of_ne (by p6_ne), hsc])
      (by rw [hg1, Function.update_self])) ?_))
  rintro ⟨slot, v⟩
  refine Refines.pure fun t s ⟨hsz, g2, h2, hag, hsc2⟩ ↦ ?_
  simp only at hsz hag hsc2 ⊢
  set g3 := Function.update g2 ePtN (g2 eKd) with hg3
  have hA : ∀ i, ¬ OpenW i → g3 i = g i := fun i hi ↦ by
    obtain ⟨n1, n2, n3, n4, _, _⟩ := notOpen hi
    rw [hg3]
    by_cases hp : i = ePtN
    · subst hp
      rw [Function.update_self, hag _ (by unfold Tmp; p6_ne), wrA_out (by rw [hsz]; p6_omega), hg1,
        Function.update_of_ne (by p6_ne), Function.update_self]
    · rw [Function.update_of_ne hp, hag _ n3, wrA_out (by rw [hsz]; omega), hg1,
        Function.update_of_ne hp, Function.update_of_ne n1]
  have hB : ∀ i < 6, g3 (eSlot + i) = slot.getD i 0 := fun i hi ↦ by
    rw [hg3, Function.update_of_ne (by p6_ne), hag _ (by unfold Tmp; p6_omega),
      wrA_in (by omega)]
  have hC : g3 eSC = v := by rw [hg3, Function.update_of_ne (by p6_ne), hsc2]
  have hwbr : ∀ j < 1600, wb + j < eRows ∨ eRows + 4096 ≤ wb + j := fun j hj ↦ by
    have := (notOpen (hwb j hj)).2.2.2.2.1
    p6_omega
  refine WP.blk_cons (WP.mono (pure_cp hin (src := eKd) (dst := ePtN) (by p6_omega) (by p6_omega)
    t s h2) (fun s3 h3 ↦ ?_) (fun _ h ↦ h))
  refine WP.blk_cons (WP.mono (pure_rows hin (first := first) (by p6_omega) hwbr hwb' t s3 h3)
    (fun s4 h4 ↦ ?_) (fun _ h ↦ h))
  refine WP.mono (colC_spec hin h4) (fun s5 ⟨g5, h5, hfr5, hcol⟩ ↦ ?_) (fun _ h ↦ h)
  set g4 := ovr g3 eRows 4096 (rowF first sw wb g3) with hg4
  set rows := keccakSlotWeights logSteps claim first (2 - first) with hrows
  obtain ⟨hrs, hrw⟩ := slotWeights_size logSteps claim first (2 - first)
  have h4o : ∀ i, (i < eRows ∨ eRows + 4096 ≤ i) → ¬ ColW i → g5 i = g3 i := fun i h1 h2 ↦ by
    rw [hfr5 i h2, hg4, ovr_out h1]
  have hSlot : ∀ i < 6, g5 (eSlot + i) = slot.getD i 0 := fun i hi ↦ by
    rw [h4o _ (by p6_omega) (by unfold ColW eWk; p6_omega), hB i hi]
  have hentry : ∀ z < 64, ∀ r < 64, (g4 (eRows + 64 * z + r)).toE =
      ((rows.getD r #[]).getD z 0).toE := fun z hz r hr ↦ by
    have e1 : (64 * z + r) / 64 = z := by omega
    have e2 : (64 * z + r) % 64 = r := by omega
    have hsw2 : ¬ OpenW (sw + 1 - first) := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hf with rfl | rfl
      · exact hsw'.2
      · exact hsw'.1
    have hsw1 : rowW first sw g3 r = rowW first sw g r := by
      unfold rowW
      rw [hA _ hsw'.1, hA _ hsw2]
    rw [hg4, ovr_in (by omega) (by omega), show eRows + 64 * z + r - eRows = 64 * z + r by omega,
      rowF, e1, e2, NativeVm.Equiv.EW.toE_ofE, hA _ (hwb _ (by omega)), hw _ (by omega), hsw1,
      rowW_slot hf hseg, slotWeights_getD logSteps claim (by omega) hr hz]
  refine ⟨g5, h5, hsz, hSlot, ?_, fun z hz ↦ ?_, ?_, fun i hi ↦ ?_⟩
  · rw [← Array.foldl_toList]
    exact openRows_size slot.toList rows (by rw [Array.length_toList, hsz, hrs]; rfl) (by
      rw [hrs]; exact hrw)
  · rw [← NativeVm.Equiv.EW.toE_inj, hcol z hz,
      openRows_getD slot rows (by rw [hsz, hrs]; rfl) (by rw [hrs]; exact hrw) hz, colV]
    congr 1
    · rw [hrs, vals]
      exact List.map_congr_left fun r hr ↦ hentry z hz r (List.mem_range.1 hr)
    · rw [← hsz]
      exact vals_eq slot fun i hi ↦ by
        rw [hg4, ovr_out (by p6_omega), hB i (by omega)]
  · rw [h4o _ (by p6_omega) (by unfold ColW eWk; p6_omega), hC]
  · obtain ⟨_, n2, _, _, n5, n6⟩ := notOpen hi
    rw [h4o _ (by p6_omega) (by unfold ColW eWk; p6_omega), hA i hi]

/-! ## The final check -/

/-- `multilinearEval mu low` into `eCh`, `emle`'s work area at `eWk`. -/
def mleC : List Stmt := I (.lea .r13 (at_ .rbp (wdisp (2 * eMu)))) ::
  I (.lea .r14 (at_ .rbp (wdisp (2 * eWk)))) :: I (.lea .rsi (at_ .rbp (wdisp (2 * eLow)))) ::
  I (.movi .r15 16) :: emle :: (ldSb ++ stEl eCh)

/-- `dot` of the weights and the slices, times the element at `eCh`, against the claim. -/
def chkC : List Stmt :=
  ssum (.imm (Int64.ofNat 64)) (dterm eOW eSl) :: (ldB eCh ++ [emul] ++ chkEl eSC)

/-- The final check: `multilinearEval mu low · dot weights slices` against the claim at `eSC`,
`mu` at `eMu`, `low` at `eLow`, the weights at `eOW`, the slices at `eSl`. -/
def finC : List Stmt := blk mleC :: chkC

theorem mleC_spec (hin : Inputs env inp s0.mem) {x : E} (h : St env s0 g t s)
    (hx : LeanVM.Protocol.Verifier.multilinearEval (vals g eMu 16) (vals g eLow 4) = x) :
    WP (blk mleC) s (fun s' ↦ ∃ g', St env s0 g' t s' ∧ g' eCh = EW.ofE x ∧
      ∀ i, i ≠ eCh → (i < eWk ∨ eWk + 8 ≤ i) → g' i = g i) fun _ ↦ False := by
  have hN := scrN_lt
  have hp := h.2.2.1
  unfold mleC
  refine NativeVm.Transcript.wp_reg (by rfl) (NativeVm.Transcript.wp_reg (by rfl)
    (NativeVm.Transcript.wp_reg (by rfl) (NativeVm.Transcript.wp_reg (by rfl) ?_)))
  refine emle_st hin (a := eMu) (b := eWk) (c := eLow) (m := 4)
    ((((h.setReg (r := .r13) (by decide) (by decide) _).setReg (r := .r14) (by decide)
      (by decide) _).setReg (r := .rsi) (by decide) (by decide) _).setReg (r := .r15) (by decide)
      (by decide) _)
    ?_ ?_ ?_ (by rfl) (by omega) (by p6_omega) (by simp only [eWk]; p6_omega) (by p6_omega)
    (by simp only [eWk]; p6_omega) (by simp only [eWk]; p6_omega) fun s1 g1 h1 hag he _ ↦ ?_
  · simp only [QState.setReg_reg, reduceCtorEq, ↓reduceIte]
    exact eval_el hp _
  · simp only [QState.setReg_reg, reduceCtorEq, ↓reduceIte]
    exact eval_el (by simpa using hp) _
  · simp only [QState.setReg_reg, reduceCtorEq, ↓reduceIte]
    exact eval_el (by simpa using hp) _
  rw [show (2 : Nat) ^ 4 = 16 from rfl, hx] at he
  obtain ⟨v9, v10⟩ := regs_of_eOf (x := EW.ofE x) (by rw [he, NativeVm.Equiv.EW.toE_ofE])
  rw [← List.append_nil (stEl eCh)]
  refine stEl_spec (by p6_omega) h1.2.2.1 h1.2.2.2 v9 v10 fun s2 hs2 hm2 hr2 ↦ WP.blk_nil
    ⟨_, St.mk' hin h1 hs2 hm2 (by rw [hr2]) (by rw [hr2]), Function.update_self .., fun i h1 h2 ↦ ?_⟩
  rw [Function.update_of_ne h1, hag i (by simp only [eWk] at h2 ⊢; omega)]

theorem fin_refines (hin : Inputs env inp s0.mem) {mu low wts slices : Array EW} {value : EW}
    (g : Nat → EW) (hmu : mu.size = 16) (hmuG : ∀ i < 16, g (eMu + i) = mu.getD i 0)
    (hlow : low.size = 4) (hlowG : ∀ i < 4, g (eLow + i) = low.getD i 0)
    (hwts : wts.size = 64) (hwG : ∀ z < 64, g (eOW + z) = wts.getD z 0)
    (hsl : slices.size = 64) (hslG : ∀ z < 64, g (eSl + z) = slices.getD z 0)
    (hsc : g eSC = value) :
    Refines (St env s0 g) (blk finC)
      (Model.require (multilinearEval mu low * dot wts slices == value))
      (fun _ t s ↦ ∃ g', St env s0 g' t s ∧
        ∀ i, (¬ OpenW i ∨ (eSlot ≤ i ∧ i < eSlot + 6)) → g' i = g i) (Kept env rs6 s0) := by
  have hN := scrN_lt
  have hx : LeanVM.Protocol.Verifier.multilinearEval (vals g eMu 16) (vals g eLow 4) =
      (multilinearEval mu low).toE := by
    rw [NativeVm.Equiv.toE_multilinearEval, ← hmu, ← hlow,
      vals_eq mu fun i hi ↦ hmuG i (by omega), vals_eq low fun i hi ↦ hlowG i (by omega)]
  refine Refines.pre_blk (P' := fun t s ↦ ∃ g', (g' eCh = EW.ofE (multilinearEval mu low).toE ∧
      ∀ i, i ≠ eCh → (i < eWk ∨ eWk + 8 ≤ i) → g' i = g i) ∧ St env s0 g' t s)
    (fun t s h ↦ WP.mono (mleC_spec hin h hx) (fun _ ⟨g', h1, h2, h3⟩ ↦ ⟨g', ⟨h2, h3⟩, h1⟩)
      (fun _ h ↦ h)) (Refines.ex fun g' ⟨hch, hfr⟩ ↦ ?_)
  have hfr' : ∀ i, (¬ OpenW i ∨ (eSlot ≤ i ∧ i < eSlot + 6)) → g' i = g i := fun i hi ↦ by
    refine hfr i (fun e ↦ ?_) ?_
    · subst e
      rcases hi with hi | hi
      · exact hi (.inl (.inr (.inr (.inr rfl))))
      · p6_omega
    · rcases hi with hi | hi
      · have := (notOpen hi).2.2.2.2.1; simp only [eWk]; p6_omega
      · simp only [eWk]; p6_omega
  have hv : value = g' eSC := by rw [hfr _ (by p6_ne) (by simp only [eWk]; p6_omega), hsc]
  rw [hv]
  intro t s h
  unfold chkC
  simp only [List.append_assoc]
  refine WP.blk_cons (WP.mono (ssum_spec (N := 64) (Lt := dRegs)
    (T := fun i ↦ (g' (eOW + i)).toE * (g' (eSl + i)).toE) (by decide) (by omega)
    (fun _ _ ↦ rfl) (fun i hi t ht h15 hm ↦ dterm_spec
      (by rw [ht .rbp (by decide)]; exact h.2.2.1) (h.2.2.2.congr fun a _ ↦ by rw [hm])
      (by p6_omega) (by p6_omega) h15)) (fun s1 ⟨e1, e2, e3⟩ ↦ ?_) (fun _ h ↦ h))
  have h1 : St env s0 g' t s1 := h.frame hin e2 e3
  refine ldB_spec h1.2.2.1 h1.2.2.2 (by p6_omega) ?_
  refine WP.blk_cons (WP.mono (emul_spec _) (fun s2 ⟨f1, f2, f3⟩ ↦ ?_) (fun _ h ↦ h))
  have h2 : St env s0 g' t s2 :=
    ((h1.setReg (r := .r11) (by decide) (by decide) _).setReg (r := .r12) (by decide) (by decide)
      _).frame hin f2 f3
  refine Refines.mono (chkEl_refines (g := g') (by p6_omega) (multilinearEval mu low * dot wts slices))
    (fun _ _ h ↦ h) (fun _ t s h ↦ ⟨g', h, hfr'⟩) (fun _ h ↦ h) t s2 ⟨h2, ?_⟩
  rw [f1]
  simp only [QState.setReg_reg, reduceCtorEq, ↓reduceIte]
  have hsum : ∑ i ∈ range 64, (g' (eOW + i)).toE * (g' (eSl + i)).toE =
      ∑ i ∈ range 64, (wts.getD i 0).toE * (slices.getD i 0).toE :=
    sum_congr rfl fun i hi ↦ by
      have := mem_range.1 hi
      rw [hfr _ (by p6_ne) (by simp only [eWk]; p6_omega), hwG i this,
        hfr _ (by p6_ne) (by simp only [eWk]; p6_omega), hslG i this]
  rw [e1, hch, eOf_toE, NativeVm.Equiv.EW.toE_ofE, NativeVm.Equiv.EW.toE_mul, toE_dot_range,
    hwts, hsl, Nat.min_self, hsum, mul_comm]

end NativeVm.Code.P6
