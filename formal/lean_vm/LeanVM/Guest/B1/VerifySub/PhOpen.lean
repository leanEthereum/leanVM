/-
  LeanVM.Guest.B1.VerifySub.PhOpen

  `verify_sub`'s stacked opening: `open_stacked`'s words and openings run `verifyStackedOpening` on
  the verifier's claims.
-/

module

public import LeanVM.Guest.B1.VerifySub.PhOpenT
public import LeanVM.Guest.B1.VerifySub.PhOpenLib
public import LeanVM.Guest.B1.VerifySub.Keccak
public import LeanVM.Guest.B1.VerifySub.Chain
public import LeanVM.Guest.B1.VerifySub.Sound
public import LeanVM.Guest.B1.Whir.Verify
public import LeanVM.Guest.B1.Whir.LastRun
public import LeanVM.Guest.B1.Stack.Section
public import LeanVM.Guest.B1.Ring.Target
public import LeanVM.Guest.B1.Common.MemSize

/-!
# The stacked opening

`phOpen_of_ood`: from the out-of-domain phase (whose point `PhOpen` reads at `ood_z`), the opening
phase holds. Its steps:

* the claims after the ring claim, by Horner in `lam` (`vsOpenT`): `target@2` is the merged ring
  claim's target (`ring_switch_target` on the merged slices, `vsMergeT`, `ringMerge_two_snd`) plus
  `lam` times the memory term's value, the `55` sent values with a placement (`onStack_vals`,
  `filter_zip_take`, `lcc_values`), the public input's two limbs on their line (`vsPubT`), the
  Keccak word and the out-of-domain value (`horner_chain`): the batched value `verifyStackedOpening`
  hands `verifyWhir`;
* `open_stacked`'s dispatch selects the stack's size (`size_sel`), and its specialization runs
  `verifyWhir` at every basis passing the terminal's check (`Whir.open_stacked_verifyWhir`);
* `check_stack_terminal` makes that check on `stackedBasis` of the verifier's claims
  (`Stack.stack_section_sound`), under `StackCtxAt`: the facts the earlier phases leave, the row
  point at most `24` wide (`chis_le`: `g_n` is one of the tables' heights, `vsTallT`), the kappa
  sources at `kappa_base` (`vs_kappa_reads`).

`subSoundW_of_ood`: `verify_sub` is sound from the out-of-domain, link and ring phases.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {bytecode : List K} {κ : ℕ} {L : MemoryImage κ} {C : CallRel} {V : FrameMap} {σ : Val}
  {rets : List E}

/-! ## The layout's facts -/

/-- Table `t`'s height word, `kb[2 + t]`. -/
theorem heights_at {rd : Reader} (S : SizesOk bytecode rd σ) {t : ℕ} (ht : t < nTables) :
    σ (.n (115 + t)) = gen ^ (vsLayout bytecode σ).tableLogHeights.getD t 0 := by
  have hlen : (vsLayout bytecode σ).tableLogHeights.length = 6 := by
    obtain ⟨-, -, -, hth, -⟩ := Stack.buildLayout_some S.build
    rw [hth, List.length_zipWith]; simp [vsRows, vsAnnounced, tableLogFloors, nTables]
  have := congrArg (fun l ↦ l.getD t 0) S.heights
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht, Option.map_some,
    Option.getD_some] at this
  rw [this, List.getElem?_eq_getElem (by rw [hlen]; exact ht),
    List.getD_eq_getElem _ _ (by rw [hlen]; exact ht)]
  rfl

/-- **The kappa sources** at `kappa_base`. -/
theorem vs_kappa_reads {rd : Reader} (S : SizesOk bytecode rd σ) (F : ReadsFacts C rd σ) :
    ReadsAt rd (σ (.n 112))
      (Stack.kappaSources (vsLayout bytecode σ).logMemory (vsLayout bytecode σ).tableLogHeights) := by
  have e : Stack.kappaSources (vsLayout bytecode σ).logMemory (vsLayout bytecode σ).tableLogHeights =
      (List.range 8).map fun i ↦ σ (.n (113 + i)) := by
    rw [Stack.kappaSources]
    apply List.ext_getElem (by simp [nTables])
    intro i h1 h2
    simp only [List.length_cons, List.length_map, List.length_range, nTables] at h1
    interval_cases i
    · exact F.kb.1.symm
    · exact (F.kb.2.1.trans S.logMem).symm
    · exact (heights_at S (t := 0) (by decide)).symm
    · exact (heights_at S (t := 1) (by decide)).symm
    · exact (heights_at S (t := 2) (by decide)).symm
    · exact (heights_at S (t := 3) (by decide)).symm
    · exact (heights_at S (t := 4) (by decide)).symm
    · exact (heights_at S (t := 5) (by decide)).symm
  rw [e]; exact F.kb.2.2

/-- A run of words on a memory image of at most `2^32` words is shorter than `2^33`. -/
theorem readsAt_length_lt (hκ : κ ≤ 32) (L : MemoryImage κ) {p : E} {xs : List E}
    (h : ReadsAt L.read p xs) : xs.length < 2 ^ 33 := by
  by_contra hge
  push Not at hge
  have h1 := mem_size_big hκ L (p := p) (n := 2 ^ 33) le_rfl fun j hj ↦ ⟨_, h j (by omega)⟩
  have h2 : 2 ^ κ ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) hκ
  omega

/-- **The row point is at most `24` wide**: `g_n` is one of the six tables' heights. -/
theorem chis_le (R : VsRun bytecode L C V σ rets) {chis : List E}
    (hchi : ReadsAt L.read (σ (.n 15)) chis) (hgn : σ (.n 408) = gen ^ chis.length) :
    chis.length ≤ 24 := by
  have S := R.sizesOk
  have h := R.slice vsTallT_eq
  simp only [vsTallT, Stmt.HoldsList, Stmt.Holds, Atom.Holds] at h
  obtain ⟨-, -, -, -, -, -, a416, -, -, -, a422, a423, -, -, -, a429, a430, -, -, -, a436, a437, -, -,
    -, a443, a444, -, -, -, a450, a451, a452, a453, -⟩ := h
  have key : ∀ t < nTables, σ (.n 408) + σ (.n (115 + t)) = 0 → chis.length ≤ 24 := by
    intro t ht h0
    have e := eq_of_add_zero h0
    rw [hgn, heights_at S ht] at e
    have hl := readsAt_length_lt R.hκ L hchi
    have h24 := S.heights24 t ht
    rw [Digest.gen_pow_inj' (by omega) (by omega) e]
    exact h24
  have h0 : σ (.n 451) = 0 := by rw [a452, word_zero, add_zero] at a453; exact a453
  rw [a451, a444, a437, a430, a423] at h0
  simp only [mul_eq_zero] at h0
  rcases h0 with ((((h | h) | h) | h) | h) | h
  · rw [a416] at h; exact key 0 (by decide) h
  · rw [a422] at h; exact key 1 (by decide) h
  · rw [a429] at h; exact key 2 (by decide) h
  · rw [a436] at h; exact key 3 (by decide) h
  · rw [a443] at h; exact key 4 (by decide) h
  · rw [a450] at h; exact key 5 (by decide) h

/-! ## The public input's limbs -/

theorem mle_line (x y c : E) : multilinearEval [x, y] [c] = x + c * (x + y) := by
  simp [multilinearEval, foldPairs]
  ring

/-- **The public input's two limbs on their line**, `pi_m0` at `2905`, `pi_m1` at `2908`. -/
theorem vs_public (R : VsRun bytecode L C V σ rets) :
    σ (.n 2905) = multilinearEval [ofK ((digestHalves (vsPi σ)).1.limb 0),
      ofK ((digestHalves (vsPi σ)).2.limb 0)] [vsRm σ] ∧
    σ (.n 2908) = multilinearEval [ofK ((digestHalves (vsPi σ)).1.limb 1),
      ofK ((digestHalves (vsPi σ)).2.limb 1)] [vsRm σ] := by
  have h := R.slice vsPubT_eq
  rw [vsPubT, holdsList_append, holdsList_append, holds_splitLimbsT, holds_splitLimbsT] at h
  obtain ⟨⟨l0, -, -, h0⟩, ⟨l1, -, -, h1⟩, h⟩ := h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at h
  obtain ⟨a2903, a2904, a2905, a2906, -⟩ := h
  have hk := R.slice vsKeccakT_eq
  simp only [vsKeccakT, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at hk
  obtain ⟨a2907, a2908, -⟩ := hk
  have hpi : digestHalves (vsPi σ) = (σ (.n 0), σ (.n 1)) := digestScalars_digestOfScalars _
  rw [hpi, mle_line, mle_line]
  simp only [show (2895 + 3 : ℕ) = 2898 from rfl, show (2899 + 3 : ℕ) = 2902 from rfl] at h0 h1
  refine ⟨?_, ?_⟩
  · rw [a2905, a2904, a2903, l0, l1]; rfl
  · rw [a2908, a2907, a2906, h0, h1]; rfl

/-! ## The phase -/

/-- **The stacked opening**, sound, from the out-of-domain phase. -/
theorem phOpen_of_ood (hOod : PhOod) : PhOpen := by
  intro bytecode κ L C V σ rets R link outs kp ks f g rho lam qp memoryTerm hLF hKF hRF hqp hmt
  have S := R.sizesOk
  have F := readsFacts (R.slice vsReadsT_eq)
  obtain ⟨hexp, hwin, h11⟩ := R.pre
  obtain ⟨-, -, hoz⟩ := hOod bytecode L C V σ rets R
  obtain ⟨r, chis, qPoint, hr, -, hrl, hchi, hgn, hhc, heq, hql, hsent, hmp, hms, hmv, hpc, hsl, hsll,
    hcols, -, -⟩ := hLF
  obtain ⟨op, houts, hop, hkp, hks, hksl, hopl, hkpl⟩ := hKF
  obtain ⟨hf8, hg8, hmc, hct, hrho, hlam⟩ := hRF
  -- the statements
  have aO : ∀ {x : Atom}, Stmt.atom x ∈ vsOpenT → x.Holds L.read σ := fun h ↦ R.atom_in vsOpenT_eq h
  have aM : ∀ {x : Atom}, Stmt.atom x ∈ vsMergeT → x.Holds L.read σ := fun h ↦ R.atom_in vsMergeT_eq h
  have e3987 : σ (.n 3987) = word 2 0 :=
    aO (x := .const (.n 3987) (word 2 0)) (membB_sound (by decide +kernel))
  have e3988 : σ (.n 3988) = σ (.n 2920) * σ (.n 3987) :=
    aO (x := .mul (.n 3988) (.n 2920) (.n 3987)) (membB_sound (by decide +kernel))
  have e3989 : σ (.n 3989) = word 365917469723852800 0 :=
    aO (x := .const (.n 3989) (word 365917469723852800 0)) (membB_sound (by decide +kernel))
  have e3990 : σ (.n 3990) = σ (.n 4) * σ (.n 3989) :=
    aO (x := .mul (.n 3990) (.n 4) (.n 3989)) (membB_sound (by decide +kernel))
  have e4013 : σ (.n 4013) = word 0 1 :=
    aO (x := .const (.n 4013) (word 0 1)) (membB_sound (by decide +kernel))
  have e4014 : σ (.n 4014) = σ (.n 4013) * σ (.n 802) :=
    aO (x := .mul (.n 4014) (.n 4013) (.n 802)) (membB_sound (by decide +kernel))
  have l3811 : LoadHolds L.read (σ (.n 23)) 0 (σ (.n 3811)) :=
    aO (x := .load (.n 3811) (.n 23) 0) (membB_sound (by decide +kernel))
  have e3812 : σ (.n 3812) = σ (.n 3811) * σ (.n 3027) :=
    aO (x := .mul (.n 3812) (.n 3811) (.n 3027)) (membB_sound (by decide +kernel))
  have e3813 : σ (.n 3813) = σ (.n 3812) + σ (.n 2921) :=
    aO (x := .add (.n 3813) (.n 3812) (.n 2921)) (membB_sound (by decide +kernel))
  have e3814 : σ (.n 3814) = σ (.n 3813) * σ (.n 3027) :=
    aO (x := .mul (.n 3814) (.n 3813) (.n 3027)) (membB_sound (by decide +kernel))
  have e3815 : σ (.n 3815) = σ (.n 3814) + σ (.n 2908) :=
    aO (x := .add (.n 3815) (.n 3814) (.n 2908)) (membB_sound (by decide +kernel))
  have e3816 : σ (.n 3816) = σ (.n 3815) * σ (.n 3027) :=
    aO (x := .mul (.n 3816) (.n 3815) (.n 3027)) (membB_sound (by decide +kernel))
  have e3817 : σ (.n 3817) = σ (.n 3816) + σ (.n 2905) :=
    aO (x := .add (.n 3817) (.n 3816) (.n 2905)) (membB_sound (by decide +kernel))
  have e3818 : σ (.n 3818) = σ (.n 3817) * σ (.n 3027) :=
    aO (x := .mul (.n 3818) (.n 3817) (.n 3027)) (membB_sound (by decide +kernel))
  have e3984 : σ (.n 3984) = σ (.n 3983) + σ (.n 779) :=
    aO (x := .add (.n 3984) (.n 3983) (.n 779)) (membB_sound (by decide +kernel))
  have e3985 : σ (.n 3985) = σ (.n 3984) * σ (.n 3027) :=
    aO (x := .mul (.n 3985) (.n 3984) (.n 3027)) (membB_sound (by decide +kernel))
  have e3986 : σ (.n 3986) = σ (.n 3810) + σ (.n 3985) :=
    aO (x := .add (.n 3986) (.n 3810) (.n 3985)) (membB_sound (by decide +kernel))
  have hblk : ∀ j < 55, ∀ {x : Atom}, Stmt.atom x ∈ vsHornBlk j → x.Holds L.read σ := fun j hj x hx ↦
    aO (List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩, hx⟩)))
  -- the cursor
  have hcur : vsCursor σ = vsCurR σ * gen := by
    show σ (.n 3988) = σ (.n 2920) * gen
    rw [e3988, e3987, word_gen]
  -- the sent values
  obtain ⟨Vals, hVals⟩ : ∃ W, W = link.columns.flatMap fun c ↦ c.2.map (·.2) := ⟨_, rfl⟩
  rw [← hVals] at hsent
  have hcl6 : link.columns.length = 6 := by
    have := congrArg List.length hcols
    simp only [List.length_map, List.length_zipIdx] at this
    rw [this]; rfl
  have hLCc := Stack.linkColumnClaims_colPts link (fun t ↦ chis.take ((vsLayout bytecode σ).tableLogHeights.getD t 0))
    hcols
  have hLCcol : (linkColumnClaims link).map (·.column) =
      (Stack.sentCols.zip Stack.sentKinds).map (·.1.2) := by
    have h1 := congrArg (List.map Prod.fst) hLCc
    simp only [List.map_map] at h1
    rw [show ((Stack.sentCols.zip Stack.sentKinds).map fun z ↦ z.1.2) =
        ((Stack.sentCols.zip Stack.sentKinds).map Prod.fst).map Prod.snd by simp [List.map_map],
      List.map_fst_zip (by rw [Stack.sent_ok.1]; rfl)]
    exact h1
  have hLClen : (linkColumnClaims link).length = 80 := by
    have := congrArg List.length hLCc
    simp only [List.length_map] at this
    rw [this, Stack.sent_ok.1]
  have hVlen : Vals.length = 80 := by
    rw [hVals, ← lcc_values link (by rw [hcl6]; decide), List.length_map, hLClen]
  have hLCv : ((linkColumnClaims link).filterMap (·.onStack (vsLayout bytecode σ))).map (·.2) = Vals.take 55 := by
    rw [onStack_vals S.build _ _ Stack.sent_ok.2 hLCcol,
      filter_zip_take (fun c : ColumnClaim ↦ c.value) (fun z : (ℕ × ℕ) × ℕ ↦ z.2 != 1000) _ _ 55
        (by rw [hLClen, List.length_zip, Stack.sent_ok.1]; rfl) ?_,
      lcc_values link (by rw [hcl6]; decide), ← hVals]
    intro i hi
    rw [List.getElem_zip]
    have hk : ∀ i (h : i < Stack.sentKinds.length), ((Stack.sentKinds[i] != 1000) = true ↔ i < 55) := by
      decide +kernel
    exact hk i _
  have hsv : ∀ i < 55, σ (.n (3819 + 3 * (54 - i))) = Vals.getD i 0 := by
    intro i hi
    have l := hblk (54 - i) (by omega) (x := .load (.n (3819 + 3 * (54 - i))) (.n 1076) (54 - (54 - i)))
      (by simp [vsHornBlk])
    rw [show 54 - (54 - i) = i by omega] at l
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact loadHolds_unique l (hsent i (by omega))
  -- Horner's chain over the sent values
  have hpub := vs_public R
  have hood : σ (.n 3811) = vsOodValue L.read σ := by
    simp only [vsOodValue, wordsAt, List.range_one, List.map_cons, List.map_nil, List.headD_cons]
    rw [l3811.2]; rfl
  have hchain : σ (.n 3983) = lam * Stack.hornerL lam
      (uL (fun j ↦ σ (.n (3819 + 3 * j))) 55 ++ [σ (.n 2905), σ (.n 2908), σ (.n 2921), σ (.n 3811)]) :=
    horner_chain (fun j ↦ σ (.n (3818 + 3 * j))) (fun j ↦ σ (.n (3819 + 3 * j))) lam
      [σ (.n 2905), σ (.n 2908), σ (.n 2921), σ (.n 3811)] 55
      (by
        simp only [Stack.hornerL, Nat.mul_zero, Nat.add_zero]
        rw [e3818, e3817, e3816, e3815, e3814, e3813, e3812, ← hlam]
        ring)
      (fun j hj ↦ by
        have a1 := hblk j hj (x := .add (.n (3820 + 3 * j)) (.n (3818 + 3 * j)) (.n (3819 + 3 * j)))
          (by simp [vsHornBlk])
        have a2 := hblk j hj (x := .mul (.n (3821 + 3 * j)) (.n (3820 + 3 * j)) (.n 3027))
          (by simp [vsHornBlk])
        simp only [Atom.Holds] at a1 a2
        show σ (.n (3818 + 3 * (j + 1))) = _
        rw [show 3818 + 3 * (j + 1) = 3821 + 3 * j by ring, a2, a1, ← hlam])
      55 le_rfl
  have huL : uL (fun j ↦ σ (.n (3819 + 3 * j))) 55 = Vals.take 55 := by
    apply List.ext_getElem (by rw [uL_length, List.length_take, hVlen]; rfl)
    intro i h1 h2
    rw [uL_length] at h1
    rw [uL_getElem, List.getElem_take, show 55 - 1 - i = 54 - i by omega, hsv i h1,
      List.getD_eq_getElem _ _ (by omega)]
  -- the merged ring claim's target
  have hrst := R.call_in vsMergeT_eq (f := "ring_switch_target") (args := [.n 3553, .n 3039])
    (rs := [.n 3810]) (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_singleton.2 rfl)))
  simp only [List.map_cons, List.map_nil] at hrst
  obtain ⟨s, ch, hs64, hch16, hsR, hchR, hret⟩ := ring_switch_target_holds L.read _ _ (R.hle _ _ _ hrst)
  simp only [List.cons.injEq, and_true] at hret
  have ru : ∀ {p : E} {l1 l2 : List E}, ReadsAt L.read p l1 → ReadsAt L.read p l2 →
      l1.length = l2.length → l1 = l2 := fun h1 h2 hl ↦
    List.ext_getElem hl fun k hk1 hk2 ↦ loadHolds_unique (h1 k hk1) (h2 k hk2)
  have hmerged : ReadsAt L.read (σ (.n 3553))
      ((List.range kBits).map fun i ↦ ks.getD i 0 + rho * link.ring.slices.getD i 0) := by
    intro i hi
    simp only [List.length_map, List.length_range] at hi
    have hb : ∀ {x : Atom}, Stmt.atom x ∈ vsMergeBlk i → x.Holds L.read σ := fun hx ↦
      aM (List.mem_cons_of_mem _ (List.mem_append_left _
        (List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩, hx⟩)))
    have l1 := hb (x := .load (.n (3554 + 4 * i)) (.n 21) i) (by simp [vsMergeBlk])
    have l2 := hb (x := .load (.n (3555 + 4 * i)) (.n 1076) (80 + i)) (by simp [vsMergeBlk])
    have m3 := hb (x := .mul (.n (3556 + 4 * i)) (.n 3026) (.n (3555 + 4 * i))) (by simp [vsMergeBlk])
    have a4 := hb (x := .add (.n (3557 + 4 * i)) (.n (3554 + 4 * i)) (.n (3556 + 4 * i)))
      (by simp [vsMergeBlk])
    have l5 := hb (x := .load (.n (3557 + 4 * i)) (.n 3553) i) (by simp [vsMergeBlk])
    simp only [Atom.Holds] at l1 l2 m3 a4 l5
    have k1 : σ (.n (3554 + 4 * i)) = ks.getD i 0 := by
      rw [List.getD_eq_getElem _ _ (by omega)]; exact loadHolds_unique l1 (hks i (by omega))
    have k2 : σ (.n (3555 + 4 * i)) = link.ring.slices.getD i 0 := by
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact loadHolds_unique l2 ((loadHolds_mul_gen_pow _ _ 80 i _).1 (hsl i (by omega)))
    simp only [List.getElem_map, List.getElem_range]
    rw [a4, m3, k1, k2, ← hrho] at l5
    exact l5
  have hsM := ru hsR hmerged (by simp [hs64])
  have hchM := ru hchR hmc (by simp [hch16, hf8, hg8]; rfl)
  have h3810 : σ (.n 3810) = (ringMerge [keccakRingClaim qp kp ks, link.ring] f g rho).2 := by
    rw [hret, ringMerge_two_snd qp kp ks link.ring f g rho hksl hsll, hsM, hchM,
      List.take_left' (by rw [hf8]; rfl), List.drop_left' (by rw [hf8]; rfl)]
  -- `open_stacked`
  have hdisp := R.mem_slice vsOpenT_eq (s := vsOsDispatch) (membB_sound (by decide +kernel))
  simp only [vsOsDispatch, Stmt.Holds, List.map_cons, List.map_nil] at hdisp
  obtain ⟨⟨j, hj, hsel, hC⟩, -⟩ := hdisp
  have hjμ : j = (vsLayout bytecode σ).stackLog - Whir.minOpenLog :=
    (dispatchIdx_eq hj hsel).symm.trans (dispatchIdx_eq (by
      have := S.st2; have := S.st1
      simp only [Whir.openArms, Whir.minOpenLog] at *; omega) S.sizeSel)
  have hnm : vsOsNames[j] = Whir.openName (vsLayout bytecode σ).stackLog := by
    rw [vsOsNames_get j hj, Whir.openName_eq (by
      have := S.st2; have := S.st1; simp only [Whir.ligNSizes, Whir.minOpenLog] at *; omega), ← hjμ]
  rw [hnm] at hC
  obtain ⟨fn, hfind, hpar, hbody⟩ := R.hU _ _ _ hC
  have hp : fn.params.map (V (Whir.openName (vsLayout bytecode σ).stackLog)
      [σ (.n 96), σ (.n 3033), σ (.n 3034), σ (.n 3035), σ (.n 3036), σ (.n 3037), σ (.n 3986),
        σ (.n 134), σ (.n 137), σ (.n 3988), σ (.n 3990)]
      [σ (.n 3991), σ (.n 3992), σ (.n 3993), σ (.n 3994), σ (.n 3995), σ (.n 3996)]) =
      Whir.rateSel (vsLir σ) :: [σ (.n 3033), σ (.n 3034), σ (.n 3035), σ (.n 3036), σ (.n 3037)] ++
        [σ (.n 3986), σ (.n 134), σ (.n 137), σ (.n 3988), σ (.n 3990)] := by
    rw [hpar, ← S.rateSel]; rfl
  have hwt : WinTabs L.read (σ (.n 3990)) := by
    rw [e3990, e3989, word_winTab]; exact winTabs_of_expWinTab hwin
  have hwb := winTabBits_le_of_winTabs R.hκ L hwt
  obtain ⟨w, s', roots', -, hwl, ⟨pt, pt1, cur', hrets, hpt, hpt1⟩, hrun⟩ :=
    Whir.open_stacked_verifyWhir R.hκ hwb L C V R.hU R.hle (vsLayout bytecode σ).stackLog (vsLir σ) S.st1 S.st2 S.lir1
      S.lir4 (vsRoot σ) [σ (.n 3033), σ (.n 3034), σ (.n 3035), σ (.n 3036), σ (.n 3037)] (σ (.n 3986))
      (σ (.n 134)) (σ (.n 137)) (σ (.n 3988)) (σ (.n 3990)) _ fn _ rfl
      (digestScalars_digestOfScalars _).symm hwt hfind hp hbody
  simp only [List.cons.injEq, and_true] at hrets
  obtain ⟨e3991, e3992, e3993, e3994, e3995, -⟩ := hrets
  -- `check_stack_terminal`
  have hcst := R.call_in vsOpenT_eq (show vsCstCall ∈ vsOpenT from membB_sound (by decide +kernel))
  simp only [List.map_cons, List.map_nil] at hcst
  obtain ⟨-, hM⟩ := (Stack.stack_section_sound h11 R.hκ L).2.2 _ _ (R.hle _ _ _ hcst)
  set v0 := multilinearEval [ofK ((digestHalves (vsPi σ)).1.limb 0),
    ofK ((digestHalves (vsPi σ)).2.limb 0)] [vsRm σ] with hv0
  set v1 := multilinearEval [ofK ((digestHalves (vsPi σ)).1.limb 1),
    ofK ((digestHalves (vsPi σ)).2.limb 1)] [vsRm σ] with hv1
  have hτ : σ (.n 120) = gen ^ (vsLayout bytecode σ).tableLogHeights.getD opKeccak 0 := heights_at S (t := 5) (by decide)
  have hopl' : op.length = (vsLayout bytecode σ).tableLogHeights.getD opKeccak 0 + qkeccakSlotBits := by
    have e := hopl
    rw [hτ, ← pow_add] at e
    have h1 := readsAt_length_lt R.hκ L hop
    have h2 : (vsLayout bytecode σ).tableLogHeights.getD opKeccak 0 ≤ 24 := S.heights24 5 (by decide)
    have hq6 : qkeccakSlotBits = 6 := by decide +kernel
    rw [hq6] at e ⊢
    exact (Digest.gen_pow_inj' (by omega) (by omega) e).symm
  obtain ⟨claims, hcl, hterm⟩ := hM (vsLayout bytecode σ) link chis r qPoint op kp f g w.point
    (vsOodZ L.read σ (vsLayout bytecode σ).stackLog) rho lam (vsRm σ) outs ks (vsOodValue L.read σ) v0 v1 (by
      dsimp only [Stack.StackCtxAt]
      refine ⟨⟨bytecode, vsRows σ, ?_⟩, hexp, vs_kappa_reads S F, S.placed, hchi, hgn, chis_le R hchi hgn,
        hhc, hpc, hcols, hql, heq, hr, hrl, S.logMem, hmp, by rw [hms], ?_, rfl, hop, hkp, ⟨_, houts⟩,
        hopl', hkpl, hf8, hg8, hct, hrho.symm, hlam.symm, hwl, ?_, ?_, wordsAt_length _ _ _, hoz⟩
      · rw [(Stack.buildLayout_some S.build).1]; exact S.build
      · rw [hms, e4014, e4013, word_y, y_eq]; rfl
      · rw [e3992, hwl]; exact hpt
      · rw [e3993, hwl]; exact hpt1)
  change (σ (.n 3994) + _) * σ (.n 3995) = σ (.n 3991) at hterm
  simp only [Stack.stackedClaims, hqp, hmt, Option.some.injEq] at hcl
  -- the claims' values
  obtain ⟨p0, hp0⟩ := placement_of_buildLayout S.build (c := memory0) (by decide)
  obtain ⟨p1, hp1⟩ := placement_of_buildLayout S.build (c := memory1) (by decide)
  have hmt2 : memoryTerm.2 = link.memoryValue := by
    simp only [Stack.memoryTermPure, hp0, hp1, Option.some.injEq] at hmt; rw [← hmt]
  have hFM : ((linkColumnClaims link ++ Stack.publicClaimsPure (vsLayout bytecode σ) (vsRm σ) v0 v1 ++ outs).filterMap
      (·.onStack (vsLayout bytecode σ))).map (·.2) = Vals.take 55 ++ [v0, v1, σ (.n 2921)] := by
    have hpub2 : ((Stack.publicClaimsPure (vsLayout bytecode σ) (vsRm σ) v0 v1).filterMap
        (·.onStack (vsLayout bytecode σ))).map (·.2) = [v0, v1] := by
      simp only [Stack.publicClaimsPure, List.filterMap_cons, List.filterMap_nil, ColumnClaim.onStack, hp0,
        hp1, Option.map_some, List.map_cons, List.map_nil]
    have hout2 : (outs.filterMap (·.onStack (vsLayout bytecode σ))).map (·.2) = [σ (.n 2921)] := by
      simp only [houts, List.filterMap_cons, List.filterMap_nil, ColumnClaim.onStack, hqp, Option.map_some,
        List.map_cons, List.map_nil]
    rw [List.filterMap_append, List.filterMap_append, List.map_append, List.map_append, hLCv, hpub2, hout2]
    simp
  have hvals : claims.map (·.2) = (ringMerge [keccakRingClaim qp kp ks, link.ring] f g rho).2 ::
      link.memoryValue :: (Vals.take 55 ++ [v0, v1, σ (.n 2921), vsOodValue L.read σ]) := by
    rw [← hcl]
    simp only [List.map_cons, List.map_append, List.map_nil, hmt2]
    rw [hFM]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  have hlen : claims.length ≤ maxStackedClaims := by
    have := congrArg List.length hvals
    simp only [List.length_map, List.length_cons, List.length_append, List.length_take, hVlen,
      List.length_nil] at this
    rw [this]; decide
  have htarget : σ (.n 3986) = dot (powers lam claims.length) (claims.map (·.2)) := by
    rw [show claims.length = (claims.map (·.2)).length from (List.length_map _).symm,
      Stack.dot_powers_hornerL, hvals]
    simp only [Stack.hornerL]
    rw [e3986, e3985, e3984, hchain, huL, hpub.1, hpub.2, hood, h3810, hmv, ← hlam]
    ring
  have hbasis : (w.inner + Stack.stackedBasis claims lam w.point) * w.residual = w.target := by
    rw [← e3994, ← e3995, ← e3991]; exact hterm
  have hW := hrun (Stack.stackedBasis claims lam) hbasis
  refine ⟨hcur, s', roots', ?_⟩
  have hb := Whir.RunsWith.bind
    (Whir.runsWith_require (c := claims.length ≤ maxStackedClaims) hlen (vsF8 σ)
      [(vsRoot σ, Whir.stackShape (vsLayout bytecode σ).stackLog (vsLir σ))])
    (f := fun _ ↦ verifyWhir (vsLayout bytecode σ).stackLog (vsLir σ) (dot (powers lam claims.length) (claims.map (·.2)))
      fun point ↦ dot (powers lam claims.length) (claims.map fun c ↦ c.1 point))
    (by rw [← htarget]; exact hW)
  rw [List.nil_append, List.nil_append] at hb
  subst hcl
  exact hb

/-- **`verify_sub` is sound**, given the out-of-domain, link and ring phases: the opening's follows
from the out-of-domain phase. -/
theorem subSoundW_of_ood (hOod : PhOod) (hLink : PhLink) (hRing : PhRing) (bytecode : List K) :
    Main.SubSoundW bytecode vsPiOf :=
  subSoundW_of hOod hLink hRing (phOpen_of_ood hOod) bytecode

end
end LeanVM.Guest.B1.VerifySub
