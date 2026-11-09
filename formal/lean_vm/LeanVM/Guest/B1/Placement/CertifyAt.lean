/-
  LeanVM.Guest.B1.Placement.CertifyAt

  `certify_placement` is complete in the uniform placed form (`CompleteAtD`): its five buffers
  at the bump allocator's positions, the offsets' returned.
-/

module

public import LeanVM.Guest.B1.Placement.CertifyComplete
public import LeanVM.Guest.B1.Tables.FlatAtT

/-!
# `certify_placement`, placed (TRIAGE G #67)

At frame pointer `fp` the buffers lie at `e10 = fp + fs "certify_placement"` (the groups' keys),
`e11 = e10 + 9` (their sizes), `e138 = e11 + 9` (the group order), `e139 = e138 + 9` (the groups'
bases) and `e295 = e139 + 9` (the columns' offsets, `101` words); the function returns the stack's
total and the offsets' pointer, and its returned layout is `cpOwn` there (`cpOut`).
`certify_placement_completeAt`: `CompleteAtD` on the base, squares and rank-key runs `cpLin`, for
`κ ≥ 14`, by `completeAt_flatOutD` on the honest valuation `cpσ` (`cp_body_holds`), every load in
the inputs or the buffers (`cp_loads_ok`). `cp_out_ctx`: the returned offsets satisfy `PCtx`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier hiding Layout gpow
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-- What `certify_placement` returns: the stack's total and the offsets' pointer, and its five
buffers holding `cpOwn`. -/
def cpOut (lm : ℕ) (hs : List ℕ) : List E → Layout → Prop := fun rets L =>
  ∃ e10 e11 e138 e139 e295 : ℕ, rets = [gen ^ stackTotal (columnKappas lm guestLogBytecode hs),
    ofK (addressOfIndex e295)] ∧ L = cpOwn lm hs e10 e11 e138 e139 e295

/-- The buffers' words, in allocation order. -/
noncomputable def cpOwnL (lm : ℕ) (hs : List ℕ) : List (List E) :=
  [(List.range 9).map (cpKey lm hs), (List.range 9).map fun g ↦ gen ^ cpSize lm hs g,
    (cpGOrd lm hs).map (gen ^ ·), (List.range 9).map fun g ↦ gen ^ cpGP lm hs (cpRho lm hs g),
    (stackOffsets (cpKs lm hs)).1.map (gen ^ ·)]

/-- The buffers' sizes. -/
abbrev cpSizes : List ℕ := [9, 9, 9, 9, 101]

theorem cp_bufL (lm : ℕ) (hs : List ℕ) (b : ℕ) :
    bufL b cpSizes (cpOwnL lm hs) = cpOwn lm hs b (b + 9) (b + 9 + 9) (b + 9 + 9 + 9)
      (b + 9 + 9 + 9 + 9) := rfl

theorem cp_own_len (lm : ℕ) (hs : List ℕ) :
    List.Forall₂ (fun c s => c.length ≤ s) (cpOwnL lm hs) cpSizes := by
  simp [cpOwnL, cpGOrd_length, tb_stackOffsets_length, cpKs_length]

theorem cp_flat : cpPre.all Stmt.flat = true := by decide +kernel

theorem cp_addrs : cpPre.filterMap Main.Stmt.addrS = [] := by decide +kernel

theorem cp_allocs : cpPre.filterMap Main.Stmt.allocSz =
    [(.n 10, .inl 9), (.n 11, .inl 9), (.n 138, .inl 9), (.n 139, .inl 9), (.n 295, .inl 101)] := by
  decide +kernel

theorem cp_not_loop : coreProgram.loop "certify_placement" = false := by decide +kernel

theorem cp_noLoadIte : cpPre.all noLoadIte = true := by decide +kernel

/-- Neither a dispatch nor a call. -/
def noCallB : Stmt → Bool
  | .atom _ | .ite .. => true
  | _ => false

theorem cp_noCall : cpPre.all noCallB = true := by decide +kernel

theorem cpGroup_loads : ∀ gi < 9, (cpGroup gi).filterMap Stmt.loadS =
    [(.n (cpQ gi + 4), 178), (.n 10, gi), (.n (cpZ gi), 0), (.n 11, gi)] := by decide +kernel

theorem cpRank_loads : ∀ r < 8, (cpRank (r + 1)).filterMap Stmt.loadS =
    [(.n 138, r + 1), (.n (133 + 18 * (r + 1) + 5), 0), (.n (133 + 18 * (r + 1) + 14), 0),
      (.n (133 + 18 * (r + 1) + 15), 0)] := by decide +kernel

theorem cpCols_loads : ∀ gi < 9, (cpCols gi).filterMap Stmt.loadS =
    (.n (cpD gi), cpAdj gi) :: (.n 139, gi) ::
      (List.range (cpLen gi)).map fun j ↦ (.n 295, cpC0 gi + j) := by decide +kernel

theorem cp_loads {q : V × ℕ} (hq : q ∈ cpPre.filterMap Stmt.loadS) :
    (∃ i < 8, q = (.n 0, i)) ∨
      (∃ gi < 9, q = (.n (cpQ gi + 4), 178) ∨ q = (.n 10, gi) ∨ q = (.n (cpZ gi), 0) ∨
        q = (.n 11, gi)) ∨
      q = (.n 138, 0) ∨ q = (.n 145, 0) ∨ q = (.n 148, 0) ∨ q = (.n 149, 0) ∨
      (∃ r < 8, q = (.n 138, r + 1) ∨ q = (.n (133 + 18 * (r + 1) + 5), 0) ∨
        q = (.n (133 + 18 * (r + 1) + 14), 0) ∨ q = (.n (133 + 18 * (r + 1) + 15), 0)) ∨
      (∃ gi < 9, q = (.n (cpD gi), cpAdj gi) ∨ q = (.n 139, gi) ∨
        ∃ j < cpLen gi, q = (.n 295, cpC0 gi + j)) := by
  simp only [cpPre, List.filterMap_append, List.filterMap_flatten, List.map_map,
    List.mem_append, List.mem_flatten, List.mem_map, List.mem_range] at hq
  rcases hq with ((((((((⟨_, ⟨i, hi, rfl⟩, hq⟩ | hq) | ⟨_, ⟨gi, hgi, rfl⟩, hq⟩) | hq) | hq) |
    ⟨_, ⟨r, hr, rfl⟩, hq⟩) | hq) | ⟨_, ⟨gi, hgi, rfl⟩, hq⟩) | hq)
  · simp only [Function.comp_apply, List.filterMap_cons, Stmt.loadS, List.filterMap_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hq
    exact Or.inl ⟨i, hi, hq⟩
  · simp [Stmt.loadS] at hq
  · simp only [Function.comp_apply, cpGroup_loads gi hgi, List.mem_cons, List.not_mem_nil,
      or_false] at hq
    exact Or.inr (Or.inl ⟨gi, hgi, hq⟩)
  · simp [Stmt.loadS] at hq
  · simp only [cpRank0, List.filterMap_cons, Stmt.loadS, List.filterMap_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hq
    rcases hq with h | h | h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · simp only [Function.comp_apply, cpRank_loads r hr, List.mem_cons, List.not_mem_nil,
      or_false] at hq
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨r, hr, hq⟩))))))
  · simp [Stmt.loadS] at hq
  · simp only [Function.comp_apply, cpCols_loads gi hgi, List.mem_cons, List.mem_map,
      List.mem_range] at hq
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨gi, hgi, ?_⟩))))))
    rcases hq with h | h | ⟨j, hj, h⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨j, hj, h.symm⟩)
  · simp [Stmt.loadS] at hq

theorem cp_limb_mul (b c k : ℕ) : (ofK (addressOfIndex b) * gen ^ c).limb 0 * addressOfIndex k =
    addressOfIndex (b + c + k) := by
  have e : ofK (addressOfIndex b) * gen ^ c = ofK (addressOfIndex (b + c)) := by
    rw [gen_pow_eq_ofK, ← ofK_mul, addressOfIndex, addressOfIndex, addressOfIndex, pow_add]
  rw [e, tb_addr_ofK]

theorem cp_regionL {L : Layout} {q : ℕ × List E} (hq : q ∈ L) {k : ℕ} (hk : k < q.2.length) :
    RegionL L (q.1 + k) := ⟨q, hq, by omega, by omega⟩

/-- **Every load of the honest valuation lies in the inputs or the buffers.** -/
theorem cp_loads_ok {lm : ℕ} {hs : List ℕ} (hl : hs.length = 6) (hlm : lm ≤ 32)
    (hhs : ∀ h ∈ hs, h < 29) (h5 : hs.getD 5 0 ≤ 27) (ekb esq e10 e11 e138 e139 e295 : ℕ)
    (rd : Reader) {q : V × ℕ} (hq : q ∈ cpPre.filterMap Stmt.loadS) :
    ∃ i, (cpσ lm hs ekb esq e10 e11 e138 e139 e295 rd q.1).limb 0 * addressOfIndex q.2 =
        addressOfIndex i ∧
      (RegionL (cpLin lm hs ekb esq) i ∨ RegionL (cpOwn lm hs e10 e11 e138 e139 e295) i) := by
  set σ := cpσ lm hs ekb esq e10 e11 e138 e139 e295 rd with hσ
  have hKb : ∀ s < 8, RegionL (cpLin lm hs ekb esq) (ekb + s) := fun s h8 ↦
    cp_regionL (q := (ekb, 1 :: gen ^ lm :: hs.map (gen ^ ·))) (by simp [cpLin])
      (by simp [hl]; omega)
  have hSq : ∀ s < 34, RegionL (cpLin lm hs ekb esq) (esq + s) := fun s h8 ↦
    cp_regionL (q := (esq, gSquaresList)) (by simp [cpLin]) (by simp [gSquaresList]; omega)
  have hRk : ∀ s < 34, RegionL (cpLin lm hs ekb esq) (esq + 178 + s) := fun s h8 ↦
    cp_regionL (q := (esq + 178, rankKeysList)) (by simp [cpLin]) (by simp [rankKeysList]; omega)
  have h10 : ∀ g < 9, RegionL (cpOwn lm hs e10 e11 e138 e139 e295) (e10 + g) := fun g hg ↦
    cp_regionL (q := (e10, (List.range 9).map (cpKey lm hs))) (by simp [cpOwn]) (by simp; omega)
  have h11 : ∀ g < 9, RegionL (cpOwn lm hs e10 e11 e138 e139 e295) (e11 + g) := fun g hg ↦
    cp_regionL (q := (e11, (List.range 9).map fun g ↦ gen ^ cpSize lm hs g)) (by simp [cpOwn])
      (by simp; omega)
  have h138 : ∀ g < 9, RegionL (cpOwn lm hs e10 e11 e138 e139 e295) (e138 + g) := fun g hg ↦
    cp_regionL (q := (e138, (cpGOrd lm hs).map (gen ^ ·))) (by simp [cpOwn])
      (by simp [cpGOrd_length]; omega)
  have h139 : ∀ g < 9, RegionL (cpOwn lm hs e10 e11 e138 e139 e295) (e139 + g) := fun g hg ↦
    cp_regionL (q := (e139, (List.range 9).map fun g ↦ gen ^ cpGP lm hs (cpRho lm hs g)))
      (by simp [cpOwn]) (by simp; omega)
  have h295 : ∀ c < 101, RegionL (cpOwn lm hs e10 e11 e138 e139 e295) (e295 + c) := fun c hc ↦
    cp_regionL (q := (e295, (stackOffsets (cpKs lm hs)).1.map (gen ^ ·))) (by simp [cpOwn])
      (by simp [tb_stackOffsets_length, cpKs_length]; omega)
  have hκ : ∀ gi, cpKg lm hs gi < 34 := fun gi ↦ cpKc_lt hl hlm hhs h5 _
  have hp0 := cpPi_lt (lm := lm) (hs := hs) (r := 0) (by norm_num)
  have hptr : ∀ gi < 9, σ (.n (cpQ gi + 4)) = ofK (addressOfIndex esq) * gen ^ cpKg lm hs gi ∧
      σ (.n (cpZ gi)) = ofK (addressOfIndex esq) * gen ^ cpKg lm hs gi := fun gi hgi ↦
    cpσ_grp_ptrs lm hs ekb esq e10 e11 e138 e139 e295 rd hgi
  rcases cp_loads hq with ⟨i, hi, rfl⟩ | ⟨gi, hgi, rfl | rfl | rfl | rfl⟩ | rfl | rfl | rfl | rfl |
    ⟨r, hr, rfl | rfl | rfl | rfl⟩ | ⟨gi, hgi, rfl | rfl | ⟨j, hj, rfl⟩⟩
  · exact ⟨ekb + i, tb_addr_ofK _ _, Or.inl (hKb i hi)⟩
  · refine ⟨esq + 178 + cpKg lm hs gi, ?_, Or.inl (hRk _ (hκ gi))⟩
    show (σ (.n (cpQ gi + 4))).limb 0 * addressOfIndex 178 = _
    rw [(hptr gi hgi).1, cp_limb_mul]
    congr 1; omega
  · exact ⟨e10 + gi, tb_addr_ofK _ _, Or.inr (h10 gi hgi)⟩
  · refine ⟨esq + cpKg lm hs gi, ?_, Or.inl (hSq _ (hκ gi))⟩
    show (σ (.n (cpZ gi))).limb 0 * addressOfIndex 0 = _
    rw [(hptr gi hgi).2, cp_limb_mul, Nat.add_zero]
  · exact ⟨e11 + gi, tb_addr_ofK _ _, Or.inr (h11 gi hgi)⟩
  · exact ⟨e138 + 0, tb_addr_ofK _ _, Or.inr (h138 0 (by norm_num))⟩
  · refine ⟨e10 + cpPi lm hs 0, ?_, Or.inr (h10 _ hp0)⟩
    rw [show σ (.n 145) = ofK (addressOfIndex e10) * gen ^ cpPi lm hs 0 from
      cpσ_rank0 lm hs ekb esq _ _ _ _ _ rd (j := 5) (by norm_num), cp_limb_mul]
    rfl
  · refine ⟨e139 + cpPi lm hs 0, ?_, Or.inr (h139 _ hp0)⟩
    rw [show σ (.n 148) = ofK (addressOfIndex e139) * gen ^ cpPi lm hs 0 from
      cpσ_rank0 lm hs ekb esq _ _ _ _ _ rd (j := 8) (by norm_num), cp_limb_mul]
    rfl
  · refine ⟨e11 + cpPi lm hs 0, ?_, Or.inr (h11 _ hp0)⟩
    rw [show σ (.n 149) = ofK (addressOfIndex e11) * gen ^ cpPi lm hs 0 from
      cpσ_rank0 lm hs ekb esq _ _ _ _ _ rd (j := 9) (by norm_num), cp_limb_mul]
    rfl
  · exact ⟨e138 + (r + 1), tb_addr_ofK _ _, Or.inr (h138 _ (by omega))⟩
  · have hp := cpPi_lt (lm := lm) (hs := hs) (r := r + 1) (by omega)
    refine ⟨e10 + cpPi lm hs (r + 1), ?_, Or.inr (h10 _ hp)⟩
    rw [show σ (.n (133 + 18 * (r + 1) + 5)) = ofK (addressOfIndex e10) * gen ^ cpPi lm hs (r + 1)
      from cpσ_rank lm hs ekb esq _ _ _ _ _ rd (r := r + 1) (j := 5) (by omega) (by omega)
        (by norm_num), cp_limb_mul]
    rfl
  · have hp := cpPi_lt (lm := lm) (hs := hs) (r := r + 1) (by omega)
    refine ⟨e139 + cpPi lm hs (r + 1), ?_, Or.inr (h139 _ hp)⟩
    rw [show σ (.n (133 + 18 * (r + 1) + 14)) =
        ofK (addressOfIndex e139) * gen ^ cpPi lm hs (r + 1)
      from cpσ_rank lm hs ekb esq _ _ _ _ _ rd (r := r + 1) (j := 14) (by omega) (by omega)
        (by norm_num), cp_limb_mul]
    rfl
  · have hp := cpPi_lt (lm := lm) (hs := hs) (r := r + 1) (by omega)
    refine ⟨e11 + cpPi lm hs (r + 1), ?_, Or.inr (h11 _ hp)⟩
    rw [show σ (.n (133 + 18 * (r + 1) + 15)) =
        ofK (addressOfIndex e11) * gen ^ cpPi lm hs (r + 1)
      from cpσ_rank lm hs ekb esq _ _ _ _ _ rd (r := r + 1) (j := 15) (by omega) (by omega)
        (by norm_num), cp_limb_mul]
    rfl
  · obtain ⟨g1, g2, -⟩ := cp_col_geom gi hgi
    refine ⟨esq + cpKg lm hs gi, ?_, Or.inl (hSq _ (hκ gi))⟩
    have hc : σ (.n (cpD gi)) = cpColV lm hs esq gi (cpD gi) :=
      cpσ_col lm hs ekb esq e10 e11 e138 e139 e295 rd hgi le_rfl (by omega)
    show (σ (.n (cpD gi))).limb 0 * addressOfIndex (cpAdj gi) = _
    rw [hc, cpColV, tb_ite_pos rfl, cp_limb_mul, Nat.add_assoc]
    rfl
  · exact ⟨e139 + gi, tb_addr_ofK _ _, Or.inr (h139 gi hgi)⟩
  · refine ⟨e295 + (cpC0 gi + j), tb_addr_ofK _ _, Or.inr (h295 _ ?_)⟩
    have := cpC0_le gi hgi; unfold cpLen at hj; omega

/-- **`certify_placement` is complete, placed**: on its base, squares and rank-key runs, at every
frame pointer, on memories defined below `2^κ`, `κ ≥ 14`, its buffers at the bump allocator's
positions, the offsets' returned. -/
theorem certify_placement_completeAt (fs : String → ℕ) (cert : String → V → ℕ) {k : ℕ}
    (hk : 14 ≤ k) {lm : ℕ} {hs : List ℕ} (hl : hs.length = 6) (hlm : lm ≤ 32)
    (hhs : ∀ h ∈ hs, h < 29) (h5 : hs.getD 5 0 ≤ 27) (ekb esq : ℕ) :
    CompleteAtD fs cert k "certify_placement" (cpLin lm hs ekb esq)
      [ofK (addressOfIndex ekb), ofK (addressOfIndex esq)] (cpOut lm hs) := by
  obtain ⟨fn, hf, hp, hb⟩ := cpFound
  set f := "certify_placement"
  refine completeAt_flatOutD (fs := fs) (cert := cert) hf cp_not_loop k (cpLin lm hs ekb esq) _
    (fun fp ↦ [gen ^ stackTotal (columnKappas lm guestLogBytecode hs),
      ofK (addressOfIndex (fp + fs f + 9 + 9 + 9 + 9))]) _ hb cp_flat cp_addrs
    cpSizes (fun _ ↦ cpOwnL lm hs) (fun _ ↦ cp_own_len lm hs)
    (fun fp ↦ ⟨_, _, _, _, _, rfl, cp_bufL lm hs (fp + fs f)⟩) (fun _ ↦ [])
    (fun _ _ h ↦ absurd h (by simp)) (fun _ _ h ↦ absurd h (by simp))
    (fun _ _ _ _ _ h ↦ absurd h (by simp)) ?_
  intro fp outs ho rd hlow hB hLin
  rw [cp_bufL] at hB ⊢
  have hm := memLay_append.mpr ⟨hB, hLin⟩
  have hbody := cp_body_holds hl hlm hhs h5 ekb esq (fp + fs f) (fp + fs f + 9)
    (fp + fs f + 9 + 9) (fp + fs f + 9 + 9 + 9) (fp + fs f + 9 + 9 + 9 + 9) rd hm (hlow.mono hk)
  set σ := cpσ lm hs ekb esq (fp + fs f) (fp + fs f + 9) (fp + fs f + 9 + 9)
    (fp + fs f + 9 + 9 + 9) (fp + fs f + 9 + 9 + 9 + 9) rd with hσ
  have hnc : ∀ s ∈ cpPre, noCallB s = true := fun s hs ↦ List.all_eq_true.mp cp_noCall s hs
  refine ⟨σ, by rw [hp]; rfl, fun s hs ↦ ?_, by rw [hb]; exact hbody, ?_, ?_, ?_, ?_⟩
  · have := hnc s hs
    cases s <;> first | exact True.intro | simp [noCallB] at this
  · rw [cp_allocs]; rfl
  · rw [cp_allocs]; rfl
  · have : cpPre.filterMap (Stmt.callSF σ) = [] := by
      rw [List.filterMap_eq_nil_iff]
      intro s hs
      have := hnc s hs
      cases s <;> first | rfl | simp [noCallB] at this
    rw [this]
    match outs, ho with
    | [], _ => exact True.intro
  · rw [flatMap_loadsEv _ cpPre cp_noLoadIte]
    intro q hq
    exact cp_loads_ok hl hlm hhs h5 ekb esq _ _ _ _ _ rd hq

/-- **Within its frame and buffers:** `certify_placement` is complete, placed, on its base,
squares and rank-key runs, at every frame pointer, on memories defined below `2^κ`, `κ ≥ 14`, its
buffers at the bump allocator's positions, the offsets' returned. -/
theorem certify_placement_completeAtB (fs : String → ℕ) (cert : String → V → ℕ) {k : ℕ}
    (hk : 14 ≤ k) {lm : ℕ} {hs : List ℕ} (hl : hs.length = 6) (hlm : lm ≤ 32)
    (hhs : ∀ h ∈ hs, h < 29) (h5 : hs.getD 5 0 ≤ 27) (ekb esq : ℕ) :
    CompleteAtDTB fs cert k "certify_placement" (cpLin lm hs ekb esq)
      [ofK (addressOfIndex ekb), ofK (addressOfIndex esq)] (cpOut lm hs) (fun _ ↦ True)
      (fs "certify_placement" + cpSizes.sum) := by
  obtain ⟨fn, hf, hp, hb⟩ := cpFound
  set f := "certify_placement"
  refine (completeAt_flatOutDTB (fs := fs) (cert := cert) hf cp_not_loop k (cpLin lm hs ekb esq) _
    (fun fp ↦ [gen ^ stackTotal (columnKappas lm guestLogBytecode hs),
      ofK (addressOfIndex (fp + fs f + 9 + 9 + 9 + 9))]) _ hb cp_flat cp_addrs
    cpSizes (fun _ ↦ cpOwnL lm hs) (fun _ ↦ cp_own_len lm hs)
    (fun fp ↦ ⟨_, _, _, _, _, rfl, cp_bufL lm hs (fp + fs f)⟩) (fun _ ↦ []) (fun _ ↦ True) [] []
    0 (fun _ ↦ trivial) (fun _ ↦ le_rfl) (fun _ ↦ le_rfl) (fun _ _ h ↦ absurd h (by simp))
    (fun _ _ _ _ _ h ↦ absurd h (by simp)) ?_).mono (by simp) fun _ _ ↦ trivial
  intro fp outs ho rd hlow hB hLin
  rw [cp_bufL] at hB ⊢
  have hm := memLay_append.mpr ⟨hB, hLin⟩
  have hbody := cp_body_holds hl hlm hhs h5 ekb esq (fp + fs f) (fp + fs f + 9)
    (fp + fs f + 9 + 9) (fp + fs f + 9 + 9 + 9) (fp + fs f + 9 + 9 + 9 + 9) rd hm (hlow.mono hk)
  set σ := cpσ lm hs ekb esq (fp + fs f) (fp + fs f + 9) (fp + fs f + 9 + 9)
    (fp + fs f + 9 + 9 + 9) (fp + fs f + 9 + 9 + 9 + 9) rd with hσ
  have hnc : ∀ s ∈ cpPre, noCallB s = true := fun s hs ↦ List.all_eq_true.mp cp_noCall s hs
  refine ⟨σ, by rw [hp]; rfl, fun s hs ↦ ?_, by rw [hb]; exact hbody, ?_, ?_, ?_, ?_, trivial⟩
  · have := hnc s hs
    cases s <;> first | exact True.intro | simp [noCallB] at this
  · rw [cp_allocs]; rfl
  · rw [cp_allocs]; rfl
  · have : cpPre.filterMap (Stmt.callSF σ) = [] := by
      rw [List.filterMap_eq_nil_iff]
      intro s hs
      have := hnc s hs
      cases s <;> first | rfl | simp [noCallB] at this
    simp only [flatCalls, this, List.map_nil]
    match outs, ho with
    | [], _ => exact True.intro
  · rw [flatMap_loadsEv _ cpPre cp_noLoadIte]
    intro q hq
    exact cp_loads_ok hl hlm hhs h5 ekb esq _ _ _ _ _ rd hq

/-- **The returned offsets satisfy `PCtx`** on any memory holding the buffers. -/
theorem cp_out_ctx {lm : ℕ} {hs : List ℕ} {rets : List E} {L : Layout} (h : cpOut lm hs rets L)
    {rd : Reader} (hm : MemL rd L) :
    PCtx rd (columnKappas lm guestLogBytecode hs) (rets.getD 1 0) := by
  obtain ⟨e10, e11, e138, e139, e295, rfl, rfl⟩ := h
  exact cp_ctx hm

end
end LeanVM.Guest.B1.Tables
