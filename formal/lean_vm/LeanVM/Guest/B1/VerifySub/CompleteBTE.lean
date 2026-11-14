/-
  LeanVM.Guest.B1.VerifySub.CompleteBTE

  `verify_sub` complete within its child's bound by a node exact at every node, given its `verify_tables`,
  `verify_keccak`, `open_stacked` and `check_opening_terminal` callees' trees exact.
-/

module

public import LeanVM.Guest.B1.VerifySub.CompleteBT
public import LeanVM.Guest.B1.Exact.GPower
public import LeanVM.Guest.B1.Bits.BusGrindPlacedE
public import LeanVM.Guest.B1.Bits.Log2PlacedAll
public import LeanVM.Guest.Budget.BoundedE
public import LeanVM.Guest.Exact.Kids

/-!
# `verify_sub`, every node exact

`vsPsRE`: `vsPsR`'s predicates, each tree also exact on the memory. `vs_kidsDepBPRE`: `vs_kidsDepBPR` by trees of them:
`g_power_of_word` (`gpw_exactOk`) and the callees without a computed hint in their subtrees (`certify_placement`, the
squeeze's arms, `opening_message__L1_L1`, `verify_bus_gkr`, `ring_switch_target`) exact on every valid tree, the two
`log2_ceil_in_the_exponent`s, the two `grind_check`s and the bus grind's arm by their E forms, `verify_tables`,
`verify_keccak` (`VkCompleteAtBKE`), `open_stacked` and the terminal given. `verify_sub_completeBTGE`:
`verify_sub_completeBTG` by a tree also exact (`flatShape_every`, `verify_sub`'s own body without a computed hint).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.Memory

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-! ## Exact on every valid tree -/

theorem everyOn_exactOk {k : ℕ} {f : String} {Lin : Main.Layout} {args : List E} (hg : ExactOk f) :
    EveryOn k f Lin args fun rd => ExactAt coreProgram rd :=
  fun _ _ _ _ _ hn hv => every_exact_of_ok hg hv hn

theorem cp_exactFree : ExactFreeG "certify_placement" :=
  exactFreeG_of (j := idx% «certify_placement») (by decide +kernel)

theorem om_exactFree : ExactFreeG "opening_message__L1_L1" :=
  exactFreeG_of (j := idx% «opening_message__L1_L1») (by decide +kernel)

theorem vbg_exactFree : ExactFreeG "verify_bus_gkr" :=
  exactFreeG_of (j := idx% «verify_bus_gkr») (by decide +kernel)

theorem rst_exactFree : ExactFreeG "ring_switch_target" :=
  exactFreeG_of (j := idx% «ring_switch_target») (by decide +kernel)

theorem squeeze_exactFree : ∀ n ∈ squeezeNames, ExactFreeG n := by
  simp only [squeezeNames, List.mem_cons, List.not_mem_nil, or_false]
  rintro n (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · exact exactFreeG_of (j := idx% «squeeze_point_from__L20») (by decide +kernel)
  · exact exactFreeG_of (j := idx% «squeeze_point_from__L21») (by decide +kernel)
  · exact exactFreeG_of (j := idx% «squeeze_point_from__L22») (by decide +kernel)
  · exact exactFreeG_of (j := idx% «squeeze_point_from__L23») (by decide +kernel)
  · exact exactFreeG_of (j := idx% «squeeze_point_from__L24») (by decide +kernel)
  · exact exactFreeG_of (j := idx% «squeeze_point_from__L25») (by decide +kernel)
  · exact exactFreeG_of (j := idx% «squeeze_point_from__L26») (by decide +kernel)
  · exact exactFreeG_of (j := idx% «squeeze_point_from__L27») (by decide +kernel)
  · exact exactFreeG_of (j := idx% «squeeze_point_from__L28») (by decide +kernel)
  · exact exactFreeG_of (j := idx% «squeeze_point_from__L29») (by decide +kernel)
  · exact exactFreeG_of (j := idx% «squeeze_point_from__L30») (by decide +kernel)

/-- `verify_sub`'s own computed hints are pinned by the next atom: it has none. -/
theorem vs_pinned : Stmt.blockNextOk isComputed pinsInverse (fn% «verify_sub»).body = true := by
  decide +kernel

/-! ## The callees' E forms -/

/-- **`verify_keccak`'s bounded completeness, exact at every node.** -/
def VkCompleteAtBKE (fs : String → ℕ) (cert : String → V → ℕ) (κ Bvk : ℕ) : Prop :=
  ∀ (τ : ℕ) (f chis outs xs op point slices : List E) (word : E) (s' : Fs)
    (curE chiE olE zvE slE tbE : ℕ), 9 ≤ τ → τ ≤ 28 → τ ≤ chis.length → outs.length = 25 →
    f.length = 5 → (∃ sp, (⟨f, []⟩ : Fs).Carries sp) →
    RunsTo (verifyKeccak τ (chis.take τ) outs) ⟨f, []⟩ xs ([⟨qkeccak, op, word⟩], point, slices) s' →
    CompleteAtDTBR fs cert κ "verify_keccak"
      [(curE, xs), (chiE, chis), (olE, outs), (zvE, op), (zvE + qkeccakVarsCap, point),
        (slE, slices), (tbE, winTabWords)]
      (f ++ [ofK (Parameters.addressOfIndex curE), gen ^ τ, ofK (Parameters.addressOfIndex chiE),
        ofK (Parameters.addressOfIndex olE), ofK (Parameters.addressOfIndex zvE),
        ofK (Parameters.addressOfIndex slE), ofK (Parameters.addressOfIndex tbE)])
      (Returns (capOf s'.perm ++ [ofK (Parameters.addressOfIndex curE) * gen ^ xs.length, word]))
      (fun rd t => t.Every (ExactAt coreProgram rd)) Bvk

/-- **A `grind_check` on a passing proof of work, exact**, the window table from the caller's. -/
theorem grind_kidBE {bits : ℕ} (hb : bits ∈ grindBitsDeployed) {κ : ℕ} (hκ : 11 ≤ κ) {B : ℕ}
    (hT : TotalLe coreProgram fs (grindCheckName bits) fun _ ↦ B) {w : E} (sqE : ℕ)
    (hpow : (w.limb 0).lane.toNat % 2 ^ bits = 0) :
    CompleteAtDTBR fs cert κ (grindCheckName bits) (vsExpLin sqE) [w, ptr sqE * gen ^ winTabAt]
      (Returns []) (fun rd t => True ∧ t.Every (ExactAt coreProgram rd)) B :=
  (grind_check_completeDTBR_of hb hκ hT fun _ _ hL ↦ ⟨rfl, w, _, rfl, winTabs_vsExp hL, hpow⟩).mono le_rfl
    fun _ _ h => ⟨trivial, h.2⟩

namespace ChildSegs

variable {bytecode : List K} {seed : Digest} {c : Child} (S : ChildSegs bytecode seed c)

/-- **The bus grind's arm on the honest child, exact.** -/
theorem busGrind_kidE (hbl : bytecode.length = 2 ^ 23) {κ : ℕ} (hκ : 11 ≤ κ) (sqE : ℕ) :
    CompleteAtDTBR fs cert κ (busGrindNames.getD (S.d - 20) "") (vsExpLin sqE)
      [cellsOfState S.busSt false 1, ptr sqE * gen ^ winTabAt] (Returns [0])
      (fun rd t => True ∧ t.Every (ExactAt coreProgram rd)) (busGrindMax fs) := by
  have hd := S.d_bounds hbl
  rw [busGrindName_eq]
  exact (bus_grind_check_completeDTBRF (d := S.d - 20) (List.mem_range.2 (by omega)) hκ
    fun _ _ hL ↦ ⟨rfl, _, _, rfl, winTabs_vsExp hL, S.busPow hbl⟩).mono (le_busGrindMax (by omega))
    fun _ _ h => ⟨trivial, h.2⟩

/-- **`verify_keccak` on the honest child, exact.** -/
theorem vk_kidBE (hbl : bytecode.length = 2 ^ 23) {κ Bvk : ℕ} (hvk : VkCompleteAtBKE fs cert κ Bvk)
    (bs : List ℕ) (sqE : ℕ) :
    CompleteAtDTBR fs cert κ "verify_keccak" ((S.kids bs sqE).getD 11 noKid []).Lin
      ((S.kids bs sqE).getD 11 noKid []).args ((S.kids bs sqE).getD 11 noKid []).Out
      (fun rd t => t.Every (ExactAt coreProgram rd)) Bvk := by
  obtain ⟨-, -, hrun⟩ := S.keccak_run hbl
  obtain ⟨h9, h22, hn, ho, hf, -⟩ := S.keccak_facts hbl
  obtain ⟨-, -, h5⟩ := S.H_spec hbl
  have hc : ∃ sp, (⟨S.H.s3.squeeze.2.cap, []⟩ : Fs).Carries sp := by rw [← h5]; exact S.c5
  exact hvk S.τ _ S.H.chiW S.outs S.xsK S.kOut.point S.kc.2.1 S.kc.2.2 S.kOut.value S.s6 (S.cK bs)
    (vb bs 9) (S.cL bs) (vb bs 11) (vb bs 12) (sqE + winTabAt) h9 (by omega) hn ho hf hc hrun

end ChildSegs

/-! ## The callees -/

/-- **`verify_sub`'s callees' predicates of the memory, each tree also exact.** -/
noncomputable def vsPsRE (W : VsWordsOs fs) (Pcp Pvt Pos : Reader → Tree → Prop) : List (Reader → Tree → Prop) :=
  (vsPsR W Pcp Pvt Pos).map fun P rd t => P rd t ∧ t.Every (ExactAt coreProgram rd)

theorem vsPsRE_imp (W : VsWordsOs fs) (Pcp Pvt Pos : Reader → Tree → Prop) (rd : Reader) :
    List.Forall₂ (fun P P' => ∀ t, P t → P' t) ((vsPsRE W Pcp Pvt Pos).map (· rd))
      ((vsPsR W Pcp Pvt Pos).map (· rd)) := by
  rw [vsPsRE, List.map_map]
  generalize vsPsR W Pcp Pvt Pos = Ps
  induction Ps with
  | nil => exact .nil
  | cons P Ps ih => exact .cons (fun _ h => h.1) ih

theorem vsPsRE_every (W : VsWordsOs fs) (Pcp Pvt Pos : Reader → Tree → Prop) (rd : Reader) :
    ∀ P ∈ (vsPsRE W Pcp Pvt Pos).map (· rd), ∀ t, P t → t.Every (ExactAt coreProgram rd) := by
  intro P hP t hPt
  simp only [vsPsRE, List.map_map, List.mem_map, Function.comp_apply] at hP
  obtain ⟨Q, -, rfl⟩ := hP
  exact hPt.2

/-- **`verify_sub`'s callees on an honest child, each within its bound by a tree of its predicate of the memory and
exact**, given `verify_tables`', `verify_keccak`'s, `open_stacked`'s and the terminal's. -/
theorem vs_kidsDepBPRE {bytecode : List K} (hbl : bytecode.length = 2 ^ 23) {seed : Digest}
    {c : Child} (S : ChildSegs bytecode seed c) {κ : ℕ} (hκ : 16 ≤ κ) (W : VsWordsOs fs) {Bvk : ℕ}
    (hvk : VkCompleteAtBKE fs cert κ Bvk) (bs : List ℕ) (sqE : ℕ) {Pcp Pvt Pos : Reader → Tree → Prop}
    (hcp : CompleteAtDTBR fs cert κ "certify_placement" (Tables.cpLin S.logMem S.hs (vb bs 4) sqE)
      [ptr (vb bs 4), ptr sqE] (Tables.cpOut S.logMem S.hs) Pcp (fs "certify_placement" + Tables.cpSizes.sum))
    (hvt : ∀ B, CompleteAtDTBR fs cert κ "verify_tables" (S.H.linL B) (S.H.args B) (Returns (S.H.retsH B))
      (fun rd t ↦ ((∀ op, Budget.WeighsLe coreProgram (W.ωv op) (vtWB W.toVsWords op) t) ∧ Pvt rd t) ∧
        t.Every (ExactAt coreProgram rd))
      (vtMax fs W.Kf W.Ksh W.K10))
    (hos : ∀ pv, CompleteAtDTBR fs cert κ (Whir.openName S.μs) ((S.kids bs sqE).getD 14 noKid pv).Lin
      ((S.kids bs sqE).getD 14 noKid pv).args ((S.kids bs sqE).getD 14 noKid pv).Out
      (fun rd t => Pos rd t ∧ t.Every (ExactAt coreProgram rd)) (osBosAt fs W.Bnd S.μs))
    (hterm : ∀ pv, ((S.kids bs sqE).getD 15 noKid pv).taken = true →
      CompleteAtDTBR fs cert κ ((S.kids bs sqE).getD 15 noKid pv).f
        ((S.kids bs sqE).getD 15 noKid pv).Lin ((S.kids bs sqE).getD 15 noKid pv).args
        ((S.kids bs sqE).getD 15 noKid pv).Out
        (fun rd t ↦ (∀ op, Budget.WeighsLe coreProgram (W.ωv op) (termWB W.toVsWords op) t) ∧
          t.Every (ExactAt coreProgram rd))
        (termBound fs W.Beqc W.K15 W.Bcs W.Brs)) :
    KidsDepBPR fs cert κ (S.kids bs sqE) (vsBsAt W Bvk S.μs S.rate) (vsPsRE W Pcp Pvt Pos) := by
  refine kidsDepBPR_of _ _ _ (by rw [ChildSegs.kids_length]; rfl) (by rw [ChildSegs.kids_length]; rfl)
    fun j hj pv ↦ ?_
  have hj16 : j < 16 := by simpa [ChildSegs.kids_length] using hj
  have hμ1 := S.hmu20
  have hμ2 := S.hmu30
  have hd := S.d_bounds hbl
  have hdE : S.d = log2Ceil S.pushT := S.d_eq hbl
  have hst := S.stackTotal_le hbl
  obtain ⟨hhs, h5⟩ := S.hs_bounds hbl
  have hstat : ∀ g ∈ vsStaticS, TotalLe coreProgram fs g fun _ ↦ W.Kst g := W.hst
  have hgp : ExactOk "g_power_of_word" := gpw_exactOk
  interval_cases j <;> simp only [vsBsAt, vsBsWith, List.getD_cons_succ, List.getD_cons_zero]
  · exact ⟨fun _ ↦ ((vs_gpw_completeAtB κ [] (by have := S.hr4; omega) W.hg).toDTB.toR.andEvery
      (everyOn_exactOk hgp)), fun h ↦ by cases h⟩
  · exact ⟨fun _ ↦ ((vs_gpw_completeAtB κ [] (by have := S.h30; omega) W.hg).toDTB.toR.andEvery
      (everyOn_exactOk hgp)), fun h ↦ by cases h⟩
  · refine ⟨fun _ ↦ (log2_L0_completeAtBE κ (by omega) S.pushT sqE ?_ ?_).mono le_rfl fun _ _ h => ⟨trivial, h⟩,
      fun h ↦ by cases h⟩
    · have := log2Ceil_le_iff.mp (show log2Ceil S.pushT ≤ 31 by omega)
      calc S.pushT ≤ 2 ^ 31 := this
        _ < 2 ^ 34 := by norm_num
    · show max 0 (log2Ceil S.pushT) < 34; omega
  · exact ⟨fun _ ↦ hcp.andEvery (everyOn_exactOk (.free cp_exactFree)), fun h ↦ by cases h⟩
  · have hl : log2Ceil (Tables.stackTotal S.kappas) ≤ 30 := log2Ceil_le_iff.mpr hst
    exact ⟨fun _ ↦ (log2_L16_completeAtBE κ (by omega) _ sqE (lt_of_le_of_lt hst (by norm_num)) (by omega)).mono
      le_rfl fun _ _ h => ⟨trivial, h⟩, fun h ↦ by cases h⟩
  · exact ⟨fun _ ↦ grind_kidBE (bits := 15) (κ := κ) (by decide) (by omega) (hstat _ mem_st15) sqE S.oodPow,
      fun h ↦ by cases h⟩
  · exact ⟨fun _ ↦ (S.spf_kid κ W bs).toDTB.toR.andEvery (everyOn_exactOk (.free (squeeze_exactFree _
      (squeezeName_mem hμ1 hμ2)))), fun h ↦ by cases h⟩
  · exact ⟨fun _ ↦ (S.om_kid κ W bs).toDTB.toR.andEvery (everyOn_exactOk (.free om_exactFree)), fun h ↦ by cases h⟩
  · exact ⟨fun _ ↦ S.busGrind_kidE hbl (by omega) sqE, fun h ↦ by cases h⟩
  · exact ⟨fun _ ↦ (S.vbg_kidB hbl (by omega) W bs sqE).toDTB.toR.andEvery (everyOn_exactOk (.free vbg_exactFree)),
      fun h ↦ by cases h⟩
  · exact ⟨fun _ ↦ hvt _, fun h ↦ by cases h⟩
  · exact ⟨fun _ ↦ (S.vk_kidBE hbl hvk bs sqE).mono le_rfl fun _ _ h => ⟨trivial, h⟩, fun h ↦ by cases h⟩
  · exact ⟨fun _ ↦ grind_kidBE (bits := 13) (κ := κ) (by decide) (by omega) (hstat _ mem_st13) sqE S.ringPow,
      fun h ↦ by cases h⟩
  · exact ⟨fun _ ↦ (rst_completeAtB κ (S.keccak_facts hbl).2.2.2.2.2.2.2 S.rchs_length W.hl14).toDTB.toR.andEvery
      (everyOn_exactOk (.free rst_exactFree)), fun h ↦ by cases h⟩
  · exact ⟨fun _ ↦ hos pv, fun h ↦ by cases h⟩
  · refine ⟨fun ht ↦ hterm pv ht, fun _ ↦ ?_⟩
    show fs "check_opening_terminal" ≤ termBound fs W.Beqc W.K15 W.Bcs W.Brs
    unfold termBound
    omega

/-! ## `verify_sub` -/

/-- **A node of flat shape whose function's computed hints are pinned is exact** when each of its callees'
predicates gives it. -/
theorem flatShape_every {rd : Reader} {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hpin : Stmt.blockNextOk isComputed pinsInverse fn.body = true) {Ts : List (Tree → Prop)} {t : Tree}
    {args rets : List E} (h : Budget.FlatShape coreProgram f Ts t) (hv : t.Valid coreProgram rd args rets)
    (hT : ∀ T ∈ Ts, ∀ t, T t → t.Every (ExactAt coreProgram rd)) : t.Every (ExactAt coreProgram rd) := by
  obtain ⟨σ, bufs, ks, rfl, hw⟩ := h
  have hv' := hv
  obtain ⟨fn', hf', -, es, vs, hwk, -, -, hkv⟩ := hv'
  rw [hf] at hf'
  cases hf'
  obtain ⟨hl, hK⟩ := hw fn es vs hf hwk
  exact Tree.every_node.mpr ⟨exactAt_of_body hf hpin hv rd, everyKids_of_kidsT hkv hl hK
    fun _ T hm _ t _ _ hTt => hT T (List.of_mem_zip hm).2 t hTt⟩

theorem namedP_every {Q : Tree → Prop} : ∀ (ns : List String) (Bs : List ℕ) (Ps : List (Tree → Prop)),
    (∀ P ∈ Ps, ∀ t, P t → Q t) → ∀ T ∈ namedP fs ns Bs Ps, ∀ t, T t → Q t
  | n :: ns, b :: Bs, P :: Ps, h, T, hT, t, hTt => by
    rcases List.mem_cons.mp hT with rfl | hT
    · exact h P List.mem_cons_self t hTt.2
    · exact namedP_every ns Bs Ps (fun P' hP' => h P' (List.mem_cons_of_mem _ hP')) T hT t hTt
  | [], _, _, _, _, hT, _, _ => by simp [namedP] at hT
  | _ :: _, [], _, _, _, hT, _, _ => by simp [namedP] at hT
  | _ :: _, _ :: _, [], _, _, hT, _, _ => by simp [namedP] at hT

/-- **`verify_sub` is complete on an honest child within its own bound, exact at every node**, generic in what its
`certify_placement`, `verify_tables` and `open_stacked` callees' trees satisfy: `verify_sub_completeBTG`, given
`verify_tables`', `verify_keccak`'s, `open_stacked`'s and the terminal's trees exact. -/
theorem verify_sub_completeBTGE {bytecode : List K} (hbl : bytecode.length = 2 ^ 23) (W : VsWordsOs fs) {Bvk κ : ℕ}
    (hκ : 16 ≤ κ) (hvk : VkCompleteAtBKE fs cert κ Bvk) {seed : Digest} {c : Child}
    (S : ChildSegs bytecode seed c) (sqE outE : ℕ) (Lin : Main.Layout)
    (hst : c.proof.stream.length ≤ Coverage.childStreamCap)
    (hexp : ∀ q ∈ vsExpLin sqE, q ∈ Lin) (hout : (outE, DeferredClaim.cells c.freshClaim) ∈ Lin)
    {Pcp Pvt Pos : Reader → Tree → Prop}
    (hcp : ∀ e1 e2, CompleteAtDTBR fs cert κ "certify_placement" (Tables.cpLin S.logMem S.hs e1 e2)
      [ptr e1, ptr e2] (Tables.cpOut S.logMem S.hs) Pcp (fs "certify_placement" + Tables.cpSizes.sum))
    (hvt : ∀ B, CompleteAtDTBR fs cert κ "verify_tables" (S.H.linL B) (S.H.args B) (Returns (S.H.retsH B))
      (fun rd t ↦ ((∀ op, Budget.WeighsLe coreProgram (W.ωv op) (vtWB W.toVsWords op) t) ∧ Pvt rd t) ∧
        t.Every (ExactAt coreProgram rd))
      (vtMax fs W.Kf W.Ksh W.K10))
    (hos : ∀ bs pv, CompleteAtDTBR fs cert κ (Whir.openName S.μs) ((S.kids bs sqE).getD 14 noKid pv).Lin
      ((S.kids bs sqE).getD 14 noKid pv).args ((S.kids bs sqE).getD 14 noKid pv).Out
      (fun rd t => Pos rd t ∧ t.Every (ExactAt coreProgram rd)) (osBosAt fs W.Bnd S.μs))
    (hterm : ∀ bs pv, ((S.kids bs sqE).getD 15 noKid pv).taken = true →
      CompleteAtDTBR fs cert κ ((S.kids bs sqE).getD 15 noKid pv).f
        ((S.kids bs sqE).getD 15 noKid pv).Lin ((S.kids bs sqE).getD 15 noKid pv).args
        ((S.kids bs sqE).getD 15 noKid pv).Out
        (fun rd t ↦ (∀ op, Budget.WeighsLe coreProgram (W.ωv op) (termWB W.toVsWords op) t) ∧
          t.Every (ExactAt coreProgram rd))
        (termBound fs W.Beqc W.K15 W.Bcs W.Brs)) :
    CompleteAtDTBR fs cert κ "verify_sub" Lin (vsArgs seed c sqE outE) (Returns [])
      (fun rd t ↦ (vsTsAny fs W Bvk S.μs S.rate t ∧ ∃ σ bufs ks, t = .node "verify_sub" σ bufs ks ∧
        vsQn S sqE outE rd σ ∧ ∀ k ∈ ks, (∃ a r, k.Valid coreProgram rd a r) → VsKidQ Pcp Pvt Pos rd k) ∧
        t.Every (ExactAt coreProgram rd))
      (vsBoundAt W Bvk S.μs S.rate) := by
  have hd := S.d_bounds hbl
  obtain ⟨hkr, hkm, hσ⟩ := vs_obligations hbl S fs (κ := κ) (by omega) hexp hout (vs_callsMatch hbl S hexp)
  have h := completeAt_flatDepRBPR (fs := fs) (cert := cert) find_vs vs_not_loop κ Lin _ []
    (vs_body.trans vsT_splitPre) vs_cflat vs_caddrs vs_notIte (vsSizes S.d) (fun _ ↦ S.ownW)
    (fun _ ↦ S.ownW_fits hbl hst)
    (fun fp ↦ S.kids (bases (fp + fs "verify_sub") (vsSizes S.d)) sqE)
    (vsNames S.μs S.rate (S.d - 20)) (vsBsAt W Bvk S.μs S.rate) (vsPsRE W Pcp Pvt Pos) (vsQn S sqE outE)
    (fun _ ↦ vs_names S _ sqE)
    (fun fp ↦ vs_kidsDepBPRE hbl S hκ W hvk _ sqE (hcp _ _) hvt (hos _) (hterm _))
    hkr hkm fun fp outs hlen ho rd hlow hB hL hLo =>
      let ⟨σ, e, h⟩ := hσ fp outs hlen ho rd hlow hB hL hLo
      ⟨σ, ⟨_, outs, e, hB⟩, h⟩
  refine CompleteAtDTBR.monoV h (by simp only [vsSizes, List.sum_cons, List.sum_nil, vsBoundAt, ChildSegs.μs]; omega)
    fun rd t rets hv ⟨hF0, hn⟩ ↦ ?_
  have hE : t.Every (ExactAt coreProgram rd) := flatShape_every find_vs vs_pinned hF0 hv
    (namedP_every _ _ _ (vsPsRE_every W Pcp Pvt Pos rd))
  have hF := flatShape_mono hF0 (namedP_mono _ _ _ _ (vsPsRE_imp W Pcp Pvt Pos rd))
  refine ⟨⟨⟨S.d - 20, by omega, flatShape_mono hF (namedP_mono _ _ _ _ (vsPsR_imp W _ _ _ rd))⟩, ?_⟩, hE⟩
  obtain ⟨σ, bufs, ks, rfl, hQn⟩ := hn
  refine ⟨σ, bufs, ks, rfl, hQn, fun k hk hkv ↦ ?_⟩
  obtain ⟨σ', bufs', ks', e, hw⟩ := hF
  cases e
  obtain ⟨fn, hf, -, es, vs, hwk, -, -, hkk⟩ := hv
  obtain ⟨hl, hkT⟩ := hw fn es vs hf hwk
  obtain ⟨T, hT, hTt⟩ := kidsT_valid_mem _ _ _ hkk hkT hl k hk hkv
  exact vsNames_kidQ W Bvk S.μs S.rate (S.d - 20) _ _ _ rd T hT k hTt

end
end LeanVM.Guest.B1.VerifySub
