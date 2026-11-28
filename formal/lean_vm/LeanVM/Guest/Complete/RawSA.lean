/-
  LeanVM.Guest.Complete.RawSA

  `main_loop3`, the raw leanSPHINCS signatures, placed: its completeness and its subtree's shape,
  on memories defined where its range check reads.
-/

module

public import LeanVM.Guest.Complete.RawS
public import LeanVM.Guest.Complete.RawXA
public import LeanVM.Guest.Complete.EndBound
public import LeanVM.Guest.B1.Fwd.PureIn
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«main_loop3»
import LeanVM.Guest.Data.ValNames.«verify_sig_lean_sphincs»

/-!
# `main_loop3`, placed

`main_loop3`, `verify_sig_lean_sphincs` and `sp_wots` place nothing (`l3_pureIn`); `sp_wots` loads
nothing and hints no heap word (`spw_facts`), `verify_sig_lean_sphincs` hints no heap word
(`vsls_quiet`) and loads only its claim's four cells and the byte table (its completing valuation's
fact, `Sig.verify_sig_lean_sphincs_complete_vals`), `main_loop3` loads only its coverage cell
(`l3_loads`). So every tree the completeness proofs build has its shape:
`verify_sig_lean_sphincs` its frame, its three `sp_wots` frames after its cursor (`vslsEnd`,
`verify_sig_lean_sphincs_completesA`); `main_loop3` from iteration `j` its `nrs - j` frames and
its tail's, each iteration's check at the aligned base (`l3Step`, `l3_stepA`, which also reads the
raw index's range check's words where `P` has them defined). `l3_atEvery`: placed at every frame and
cursor.
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1.Main (l4Pre l4_body l4_params l4_find)
open LeanVM.Guest.B1.Digest (gen_pow_mul_ginv gen_pow_add_isInK gen_pow_inj' ginvW)
open LeanVM.Guest.B1.VsC (LlShape)
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

set_option linter.constructorNameAsVariable false

/-! ## The facts -/

/-- `main_loop3`'s subtree's functions. -/
abbrev l3Names : List String := [name% «main_loop3», "verify_sig_lean_sphincs", "sp_wots"]

set_option maxRecDepth 100000 in
theorem l3_pureIn : coreProgram.PureIn l3Names := Tables.pureIn_of_pureInB (by decide +kernel)

theorem l3_loop : coreProgram.loop name% «main_loop3» = true := by decide +kernel
theorem vsls_not_loop : coreProgram.loop "verify_sig_lean_sphincs" = false := by decide +kernel
theorem spw_not_loop : coreProgram.loop "sp_wots" = false := by decide +kernel

set_option maxRecDepth 100000 in
theorem spw_facts : Stmt.pureList [] (fn% «sp_wots»).body = true ∧
    Stmt.atomsAll (loadVarB []) (fn% «sp_wots»).body = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem vsls_quiet : Stmt.atomsAll quietB (fn% «verify_sig_lean_sphincs»).body = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem l3_loads : Stmt.atomsAll (loadVarB [(val% «main_loop3» "s2#1", 1)])
    (coreProgram.getD idx% «main_loop3» default).body = true := by
  rw [l4_body]; decide +kernel

/-! ## `sp_wots` -/

/-- **Every valid tree of `sp_wots` has its shape**: its frame, ending at its cursor, loading
nothing, hinting no heap word. -/
theorem spw_shape {al : String → Bool} {R : ℕ → Prop} {rd : Reader} {args rets : List E} {t : Tree}
    (hn : t.name = "sp_wots") (hv : t.Valid coreProgram rd args rets) (hb : t.BufsOk coreProgram) :
    LlShape B2C.fs al (B2C.fs "sp_wots") id R t := by
  have hnc : ∀ fn σ es vs, coreProgram.find? "sp_wots" = some fn → walk σ fn.body = .ret es vs →
      calls es = [] := by
    intro fn σ es vs hfn hw
    rw [Sig.find_sp_wots] at hfn
    cases hfn
    exact calls_nil_of_pure' spw_facts.1 hw
  have hS : "sp_wots" ∈ l3Names := List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  refine ⟨(block_endA_leaf (fs := B2C.fs) (al := al) l3_pureIn hS spw_not_loop hnc hn hv hb 0).1,
    fun c => (block_endA_leaf (fs := B2C.fs) (al := al) l3_pureIn hS spw_not_loop hnc hn hv hb c).2, ?_⟩
  cases t with
  | phantom _ _ => exact hv.elim
  | node g σ bufs kids =>
    obtain ⟨fn, hfn, -, es, vs, hw, -, -, hk⟩ := hv
    simp only [Tree.name] at hn
    subst hn
    rw [Sig.find_sp_wots] at hfn
    cases hfn
    rw [hnc _ σ es vs Sig.find_sp_wots hw] at hk
    have hkids : kids = [] := by
      cases kids with
      | nil => rfl
      | cons _ _ => simp [Tree.KidsValid] at hk
    subst hkids
    have hown := loads_of_loadVarB (R := R) spw_facts.2 hw (by simp)
    have hev : (Memory.Tree.node "sp_wots" σ bufs []).events coreProgram = es := events_node Sig.find_sp_wots hw
    refine ⟨?_, ?_⟩
    · rw [Tree.LoadsR, hev, Tree.LoadsRKids]; exact ⟨hown.1, trivial⟩
    · rw [Tree.HintsR, hev, Tree.HintsRKids]; exact ⟨hown.2, trivial⟩

/-! ## `verify_sig_lean_sphincs` -/

/-- `sp_wots`'s step of the cursor: its frame at the aligned base. -/
noncomputable def spStep (al : String → Bool) (c : ℕ) : ℕ := allocBase (al "sp_wots") c + B2C.fs "sp_wots"

/-- `verify_sig_lean_sphincs`'s end from the cursor `c`: its three `sp_wots` frames. -/
noncomputable def vslsEnd (al : String → Bool) (c : ℕ) : ℕ := spStep al (spStep al (spStep al c))

/-- `verify_sig_lean_sphincs`'s completeness, placed: `SphincsPost` and its shape. -/
def SphincsPostA (al : String → Bool) (R : ℕ → Prop) (pk : Sphincs.PublicKey) (m : HashSig.Message)
    (sig : Sphincs.Signature) (rd : Reader) (t : Tree) : Prop :=
  SphincsPost pk m sig rd t ∧ LlShape B2C.fs al (B2C.fs "verify_sig_lean_sphincs") (vslsEnd al) R t

set_option maxRecDepth 100000 in
/-- **`verify_sig_lean_sphincs` completes with its shape**: on the claim at `P` and the byte table at
`B`, its loads among their cells. -/
theorem verify_sig_lean_sphincs_completesA {al : String → Bool} {k : ℕ} (hk : 8 ≤ k) (P B : ℕ)
    (pk : Sphincs.PublicKey) (m : HashSig.Message) (sig : Sphincs.Signature)
    (hv : Sphincs.verifyWithKeccak pk m sig = true) {R : ℕ → Prop}
    (hR : (∀ o < 4, R (P + o)) ∧ ∀ v < 256, R (B + v)) :
    CallCompletes0 k "verify_sig_lean_sphincs" [ptrAt P, ptrAt B] [] (SphincsPre (ptrAt P) (ptrAt B) pk m)
      (SphincsPostA al R pk m sig) := by
  refine callCompletes0_node fun rd hl ⟨hbb, hat⟩ => ?_
  have hm : Sig.MemOK rd 256 := fun i hi => hl.mono hk i (by norm_num; omega)
  obtain ⟨σ, h0, h1, hb, hwk, -, hcs, hS⟩ := Sig.verify_sig_lean_sphincs_complete_vals (fun _ _ _ => True)
    rd (ptrAt P) (ptrAt B) pk m sig (fun _ _ _ _ _ _ _ => trivial) hm hbb hat hv
  have hwf := coreProgram_wf _ (List.mem_of_find?_eq_some Sig.find_verify_sig_lean_sphincs)
  have hw := walk_straight σ [] sPreR sStraight
  have hsat : (walk σ (sPreR ++ [Stmt.ret []])).Sat (fun _ _ _ => True) rd σ False (fun rs => rs = []) := by
    rw [sBody_straight] at hwf hb
    generalize hB : sPreR ++ [Stmt.ret []] = B at hwf hb ⊢
    exact walk_sat (P := coreProgram) _ hwf hb
  rw [hw] at hsat
  rw [← sBody_straight] at hw
  have hev : ∀ e ∈ sPreR.flatMap (slEvs σ), e.Holds rd σ := fun e he => (hsat.1 e he).1
  have hc : calls (sPreR.flatMap (slEvs σ)) = [⟨"sp_wots", Sig.sCallArgs 0, [Sig.sLeafOf 0], true⟩,
      ⟨"sp_wots", Sig.sCallArgs 1, [Sig.sLeafOf 1], true⟩, ⟨"sp_wots", Sig.sCallArgs 2, [Sig.sLeafOf 2], true⟩] := by
    rw [(straight_parts σ _ sStraight).2.2.2, sCalls]
    rfl
  obtain ⟨hld, hps⟩ := hwk _ [] hw
  obtain ⟨hV0, hV1, hV2⟩ := sp_layers_valid hv
  obtain ⟨t0, hn0, hv0, hb0, hp0, hx0⟩ := layer_completes (k := k) (by omega) hV0 hcs.1 rd hl trivial
  obtain ⟨t1, hn1, hv1, hb1, hp1, hx1⟩ := layer_completes (k := k) (by omega) hV1 hcs.2.1 rd hl trivial
  obtain ⟨t2, hn2, hv2, hb2, hp2, hx2⟩ := layer_completes (k := k) (by omega) hV2 hcs.2.2 rd hl trivial
  have hs0 := spw_shape (al := al) (R := R) hn0 hv0 hb0
  have hs1 := spw_shape (al := al) (R := R) hn1 hv1 hb1
  have hs2 := spw_shape (al := al) (R := R) hn2 hv2 hb2
  have hpure : ∀ e ∈ sPreR.flatMap (slEvs σ), e.pure l3Names := by
    have := walk_pure (σ := σ) _ (l3_pureIn _ (List.mem_cons_of_mem _ List.mem_cons_self) _
      Sig.find_verify_sig_lean_sphincs)
    rwa [hw] at this
  have halloc : allocs σ (sPreR.flatMap (slEvs σ)) = [] := allocs_pure hpure
  have hev' : (Memory.Tree.node "verify_sig_lean_sphincs" σ (allocs σ (sPreR.flatMap (slEvs σ))) [t0, t1, t2]).events
      coreProgram = sPreR.flatMap (slEvs σ) := events_node Sig.find_verify_sig_lean_sphincs hw
  refine ⟨σ, _, _, [], [t0, t1, t2], Sig.find_verify_sig_lean_sphincs, ?_, hw, rfl, hev, ?_, ?_, ⟨?_, ?_⟩,
    ?_, ?_, ?_, ?_⟩
  · rw [Sig.verify_sig_lean_sphincs_params]
    simp only [List.map_cons, List.map_nil, h0, h1]
  · rw [hc]
    exact kidsValid_cons_taken rfl hn0 hv0 (kidsValid_cons_taken rfl hn1 hv1
      (kidsValid_cons_taken rfl hn2 hv2 kidsValid_nil))
  · rw [Tree.BufsOkKids, Tree.BufsOkKids, Tree.BufsOkKids, Tree.BufsOkKids]
    exact ⟨hb0, hb1, hb2, trivial⟩
  · rw [pops_node Sig.find_verify_sig_lean_sphincs hw, Tree.popsKids, Tree.popsKids, Tree.popsKids,
      Tree.popsKids, hp0, hp1, hp2]
    exact hps
  · refine Tree.every_node.mpr ⟨exactAt_of_walk Sig.find_verify_sig_lean_sphincs hw
      (Sig.sNode_exact hw hev hS), ?_⟩
    rw [Tree.EveryKids, Tree.EveryKids, Tree.EveryKids, Tree.EveryKids]
    exact ⟨hx0, hx1, hx2, trivial⟩
  · rw [Tree.block, vsls_not_loop]; simp
  · intro c
    rw [endA_node, vsls_not_loop]
    simp only [Bool.false_eq_true, ↓reduceIte, halloc, List.sum_nil, Nat.add_zero, endF_cons, endF_nil, hn0, hn1,
      hn2, hs0.1, hs1.1, hs2.1, hs0.2.1, hs1.2.1, hs2.2.1, id_eq, vslsEnd, spStep]
  · rw [Tree.LoadsR, hev', Tree.LoadsRKids, Tree.LoadsRKids, Tree.LoadsRKids, Tree.LoadsRKids]
    refine ⟨fun A hA => ?_, hs0.2.2.1, hs1.2.2.1, hs2.2.2.1, trivial⟩
    rcases hld A hA with ⟨o, ho, rfl⟩ | ⟨v, hv', rfl⟩
    · exact ⟨P + o, Main.addr_ofK P o, hR.1 o ho⟩
    · exact ⟨B + v, Main.addr_ofK B v, hR.2 v hv'⟩
  · rw [Tree.HintsR, hev', Tree.HintsRKids, Tree.HintsRKids, Tree.HintsRKids, Tree.HintsRKids]
    exact ⟨hints_of_quietB vsls_quiet hw, hs0.2.2.2, hs1.2.2.2, hs2.2.2.2, trivial⟩

/-! ## `main_loop3` -/

/-- `main_loop3`'s iteration's step of the cursor: its check at the aligned base, then the check's
`sp_wots` frames. -/
noncomputable def l3Step (al : String → Bool) (c : ℕ) : ℕ :=
  vslsEnd al (allocBase (al "verify_sig_lean_sphincs") c + B2C.fs "verify_sig_lean_sphincs")

theorem le_spStep (al : String → Bool) (c : ℕ) : c ≤ spStep al c :=
  le_trans (le_allocBase _ c) (Nat.le_add_right _ _)

theorem le_l3Step (al : String → Bool) (c : ℕ) : c ≤ l3Step al c := by
  have h0 := le_trans (le_allocBase (al "verify_sig_lean_sphincs") c)
    (Nat.le_add_right _ (B2C.fs "verify_sig_lean_sphincs"))
  exact le_trans h0 (le_trans (le_spStep al _) (le_trans (le_spStep al _) (le_spStep al _)))

theorem le_l3Iter (al : String → Bool) : ∀ (n c : ℕ), c ≤ (l3Step al)^[n] c
  | 0, _ => le_rfl
  | n + 1, c => by
      rw [Function.iterate_succ_apply]
      exact le_trans (le_l3Step al c) (le_l3Iter al n _)

/-- `main_loop3`'s iteration's step, bounded: the check's frame and its three `sp_wots` frames. -/
theorem l3Step_le (al : String → Bool) (c : ℕ) : l3Step al c ≤ c + 2 ^ 19 := by
  unfold l3Step vslsEnd spStep
  have h1 := allocStep_le (al "verify_sig_lean_sphincs") "verify_sig_lean_sphincs" c
  have h2 := allocStep_le (al "sp_wots") "sp_wots"
    (allocBase (al "verify_sig_lean_sphincs") c + B2C.fs "verify_sig_lean_sphincs")
  have h3 := allocStep_le (al "sp_wots") "sp_wots"
    (allocBase (al "sp_wots") (allocBase (al "verify_sig_lean_sphincs") c + B2C.fs "verify_sig_lean_sphincs") +
      B2C.fs "sp_wots")
  have h4 := allocStep_le (al "sp_wots") "sp_wots"
    (allocBase (al "sp_wots") (allocBase (al "sp_wots") (allocBase (al "verify_sig_lean_sphincs") c +
      B2C.fs "verify_sig_lean_sphincs") + B2C.fs "sp_wots") + B2C.fs "sp_wots")
  omega

theorem l3Iter_le (al : String → Bool) : ∀ (n c : ℕ), (l3Step al)^[n] c ≤ c + n * 2 ^ 19
  | 0, c => by simp
  | n + 1, c => by
      rw [Function.iterate_succ_apply]
      have h1 := l3Iter_le al n (l3Step al c)
      have h2 := l3Step_le al c
      rw [Nat.succ_mul]
      omega

/-- `main_loop3`'s completeness from `g^j`, placed: `RawSPost`, its block over the iterations
left, its end each iteration's `l3Step`, loading and hinting in `R`. -/
def RawSPostA (al : String → Bool) (R : ℕ → Prop) (D : RawSigs) (j nrs : ℕ) (rd : Reader) (t : Tree) : Prop :=
  RawSPost D j nrs rd t ∧ LlShape B2C.fs al (loopBlock name% «main_loop3» (nrs - j)) (l3Step al)^[nrs - j] R t

set_option maxRecDepth 100000 in
/-- **One iteration of `main_loop3` completes, with its shape**, given its tail's. -/
theorem l3_stepA {al : String → Bool} {k : ℕ} (hk : 8 ≤ k) {nrs Y nrx : ℕ} (hnrs : nrs < 2 ^ 34) (D : RawSigs)
    (hs : ∀ i < nrs, D.slot i < Y)
    (hv : ∀ i < nrs, Sphincs.verifyWithKeccak (D.pk i) (D.msg i) (D.sig i) = true) (C T B : ℕ) {R : ℕ → Prop}
    (hR : (∀ i < nrs, R (C + D.slot i) ∧ ∀ o < 4, R (T + 4 * D.slot i + o)) ∧ ∀ v < 256, R (B + v))
    {P : Reader → Prop}
    (hP : ∀ rd, LowDef k rd → P rd →
      RawSPre D nrs nrx (ptrAt C) (ptrAt T) (ptrAt B) rd ∧ ∀ j < Y, (rd (addressOfIndex j)).isSome)
    {j : ℕ} (hj : j < nrs)
    (htail : j + 1 < nrs → CallCompletes0 k name% «main_loop3» (l3Args (j + 1) nrs Y nrx (ptrAt C) (ptrAt T) (ptrAt B))
      [] P (RawSPostA al R D (j + 1) nrs)) :
    CallCompletes0 k name% «main_loop3» (l3Args j nrs Y nrx (ptrAt C) (ptrAt T) (ptrAt B)) [] P
      (RawSPostA al R D j nrs) := by
  refine callCompletes0_node fun rd hl hP0 => ?_
  obtain ⟨hp, hd⟩ := hP rd hl hP0
  have hsj := hs j hj
  set s := D.slot j with hsd
  set σ := l3σ rd j nrs Y nrx s (ptrAt C) (ptrAt T) (ptrAt B) with hσ
  have hw := walk_straight σ [] l4Pre l4Pre_straight
  rw [← l4_body] at hw
  obtain ⟨-, -, -, hpc⟩ := straight_parts σ _ l4Pre_straight
  have hev : ∀ e ∈ l4Pre.flatMap (slEvs σ), e.Holds rd σ := by
    refine slEvs_holds fun st hst => ?_
    simp only [l4Pre, List.mem_cons, List.not_mem_nil, or_false] at hst
    rcases hst with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
    all_goals simp only [SlOk, Atom.Holds, hσ, l3σ, B1.ofArgs_n, List.getD_cons_succ,
      List.getD_cons_zero]
    · refine ⟨read_def (hd s hsj), ?_, read_def (hd _ (by omega))⟩
      rw [gen_pow_mul_ginv (by omega), ← pow_add]; congr 1; omega
    · exact (hp j hj).1
    · rw [word_gen, gen_pow_mul_gen]; exact gen_pow_add_isInK _ _
  have hc : calls (l4Pre.flatMap (slEvs σ)) =
      [⟨"verify_sig_lean_sphincs", [.n (val% «main_loop3» "s3#2"), .n (val% «main_loop3» "byte_bits")], [], true⟩,
        ⟨name% «main_loop3», l3TArgs, [], decide (σ (.n (val% «main_loop3» "s5#2")) ≠ 0)⟩] := by
    rw [hpc]; rfl
  -- the check
  have hsp : SphincsPre (ptrAt (T + 4 * s)) (ptrAt B) (D.pk j) (D.msg j) rd := by
    rw [← ptrAt_mul_gen_pow]; exact (hp j hj).2
  obtain ⟨t0, hn0, hv0, hb0, ⟨hp0, hx0⟩, hsh0⟩ := verify_sig_lean_sphincs_completesA (al := al) hk (T + 4 * s) B
    (D.pk j) (D.msg j) (D.sig j) (hv j hj) (R := R) ⟨fun o ho => (hR.1 j hj).2 o ho, hR.2⟩ rd hl hsp
  have hv0' : t0.Valid coreProgram rd
      ([V.n (val% «main_loop3» "s3#2"), .n (val% «main_loop3» "byte_bits")].map σ) [] := by
    have ea : [V.n (val% «main_loop3» "s3#2"), .n (val% «main_loop3» "byte_bits")].map σ =
        [ptrAt (T + 4 * s), ptrAt B] := by
      simp only [List.map_cons, List.map_nil, hσ, l3σ, B1.ofArgs_n, List.getD_cons_succ,
        List.getD_cons_zero, gen4, ptrAt_mul_gen_pow]
    rw [ea]; exact hv0
  -- the tail
  have e52 : σ (.n (val% «main_loop3» "s5#2")) = gen ^ j * word 2 0 + gen ^ nrs := rfl
  obtain ⟨t1, hk1, hb1, hp1, hx1, hsh1⟩ : ∃ t1 : Tree,
      Tree.KidsValid coreProgram rd σ [⟨name% «main_loop3», l3TArgs, [],
        decide (σ (.n (val% «main_loop3» "s5#2")) ≠ 0)⟩] [t1] ∧ t1.BufsOk coreProgram ∧
      t1.pops coreProgram rd = (List.range' (j + 1) (nrs - (j + 1))).flatMap (l3Pops D) ∧
      t1.Every (ExactAt coreProgram rd) ∧
      LlShape B2C.fs al (loopBlock name% «main_loop3» (nrs - (j + 1))) (l3Step al)^[nrs - (j + 1)] R t1 := by
    by_cases hlt : j + 1 < nrs
    · obtain ⟨t1, hn, hv1, hb, ⟨hp', hx⟩, hsh⟩ := htail hlt rd hl hP0
      have htk : decide (σ (.n (val% «main_loop3» "s5#2")) ≠ 0) = true := by
        rw [e52, guard_taken hnrs (by omega)]; exact decide_eq_true (by omega)
      have et : l3TArgs.map σ = l3Args (j + 1) nrs Y nrx (ptrAt C) (ptrAt T) (ptrAt B) := by
        simp only [l3TArgs, l3Args, List.map_cons, List.map_nil, hσ, l3σ, B1.ofArgs_n, List.getD_cons_succ,
          List.getD_cons_zero, word_gen, gen_pow_mul_gen]
      have hv1' : t1.Valid coreProgram rd (l3TArgs.map σ) [] := by rw [et]; exact hv1
      exact ⟨t1, kidsValid_cons_taken htk hn hv1' kidsValid_nil, hb, hp', hx, hsh⟩
    · have htk : decide (σ (.n (val% «main_loop3» "s5#2")) ≠ 0) = false := by
        rw [e52, guard_taken hnrs (by omega)]; exact decide_eq_false (by omega)
      refine ⟨.phantom name% «main_loop3» (B1.Val.ofArgs (l3TArgs.map σ)),
        kidsValid_cons_skip htk l4_find (by rw [l4_params]; rfl) kidsValid_nil, ?_, ?_, Tree.every_phantom, ?_⟩
      · rw [Tree.BufsOk]; trivial
      · rw [Tree.pops, show nrs - (j + 1) = 0 by omega]; rfl
      · rw [show nrs - (j + 1) = 0 by omega]; exact phantom_shape
  -- the shape
  have hpure : ∀ e ∈ l4Pre.flatMap (slEvs σ), e.pure l3Names := by
    have := walk_pure (σ := σ) _ (l3_pureIn _ List.mem_cons_self _ l4_find)
    rwa [hw] at this
  have halloc : allocs σ (l4Pre.flatMap (slEvs σ)) = [] := allocs_pure hpure
  have hev' : (Memory.Tree.node name% «main_loop3» σ (allocs σ (l4Pre.flatMap (slEvs σ))) [t0, t1]).events
      coreProgram = l4Pre.flatMap (slEvs σ) := events_node l4_find hw
  have hptrs : ∀ q ∈ [(val% «main_loop3» "s2#1", 1)], ∃ b, σ (.n q.1) = ptrAt b ∧ ∀ o < q.2, R (b + o) := by
    intro q hq
    simp only [List.mem_singleton] at hq
    subst hq
    refine ⟨C + s, ?_, fun o ho => ?_⟩
    · simp only [hσ, l3σ, B1.ofArgs_n, List.getD_cons_succ, List.getD_cons_zero, ptrAt_mul_gen_pow]
    · rw [Nat.lt_one_iff.mp ho, Nat.add_zero]; exact (hR.1 j hj).1
  have hown := loads_of_loadVarB l3_loads hw hptrs
  refine ⟨σ, _, _, [], [t0, t1], l4_find, by rw [l4_params]; rfl, hw, rfl, hev, ?_, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [hc]
    exact kidsValid_cons_taken rfl hn0 hv0' hk1
  · rw [Tree.BufsOkKids, Tree.BufsOkKids, Tree.BufsOkKids]
    exact ⟨hb0, hb1, trivial⟩
  · rw [pops_node l4_find hw, Tree.popsKids, Tree.popsKids, Tree.popsKids, l3_splice, hp0, hp1,
      show nrs - j = nrs - (j + 1) + 1 by omega, List.range'_succ, List.flatMap_cons]
    rfl
  · refine Tree.every_node.mpr ⟨exactAt_of_walk l4_find hw (exact_of_pinned l3_pin hw hev rd), ?_⟩
    rw [Tree.EveryKids, Tree.EveryKids, Tree.EveryKids]
    exact ⟨hx0, hx1, trivial⟩
  · have e : loopBlock name% «main_loop3» (nrs - j) =
        B2C.fs name% «main_loop3» + loopBlock name% «main_loop3» (nrs - (j + 1)) := by
      simp only [loopBlock]
      rw [show nrs - j = nrs - (j + 1) + 1 by omega, Nat.succ_mul]
      omega
    rw [e, Tree.block, l3_loop, ← hsh1.1]
    simp [Tree.blockLast]
  · intro c
    rw [endA_node, l3_loop, show nrs - j = nrs - (j + 1) + 1 by omega, Function.iterate_succ_apply]
    simp [halloc, endL_cons, endL_one, hn0, hsh0.1, hsh0.2.1, hsh1.2.1, l3Step]
  · rw [Tree.LoadsR, hev', Tree.LoadsRKids, Tree.LoadsRKids, Tree.LoadsRKids]
    exact ⟨hown.1, hsh0.2.2.1, hsh1.2.2.1, trivial⟩
  · rw [Tree.HintsR, hev', Tree.HintsRKids, Tree.HintsRKids, Tree.HintsRKids]
    exact ⟨hown.2, hsh0.2.2.2, hsh1.2.2.2, trivial⟩

/-- **`main_loop3` completes with its shape** from every counter below the count. -/
theorem main_loop3_completesA {al : String → Bool} {k : ℕ} (hk : 8 ≤ k) {nrs Y nrx : ℕ} (hnrs : nrs < 2 ^ 34)
    (D : RawSigs) (hs : ∀ i < nrs, D.slot i < Y)
    (hv : ∀ i < nrs, Sphincs.verifyWithKeccak (D.pk i) (D.msg i) (D.sig i) = true) (C T B : ℕ) {R : ℕ → Prop}
    (hR : (∀ i < nrs, R (C + D.slot i) ∧ ∀ o < 4, R (T + 4 * D.slot i + o)) ∧ ∀ v < 256, R (B + v))
    {P : Reader → Prop}
    (hP : ∀ rd, LowDef k rd → P rd →
      RawSPre D nrs nrx (ptrAt C) (ptrAt T) (ptrAt B) rd ∧ ∀ j < Y, (rd (addressOfIndex j)).isSome) :
    ∀ j < nrs, CallCompletes0 k name% «main_loop3» (l3Args j nrs Y nrx (ptrAt C) (ptrAt T) (ptrAt B)) [] P
      (RawSPostA al R D j nrs) := by
  have key : ∀ t j, j + 1 + t = nrs → CallCompletes0 k name% «main_loop3»
      (l3Args j nrs Y nrx (ptrAt C) (ptrAt T) (ptrAt B)) [] P (RawSPostA al R D j nrs) := by
    intro t
    induction t with
    | zero => intro j hj; exact l3_stepA hk hnrs D hs hv C T B hR hP (by omega) fun h => absurd h (by omega)
    | succ t ih => intro j hj; exact l3_stepA hk hnrs D hs hv C T B hR hP (by omega) fun _ => ih (j + 1) (by omega)
  intro j hj
  exact key (nrs - j - 1) j (by omega)

/-- **`main_loop3` placed**: from its first iteration, at every frame and every cursor, ending
after its `nrs` checks, its block over its `nrs` iterations. -/
theorem l3_atEvery {al : String → Bool} {k : ℕ} (hk : 8 ≤ k) {nrs Y nrx : ℕ} (hnrs : nrs < 2 ^ 19) (h0 : 0 < nrs)
    (D : RawSigs) (hs : ∀ i < nrs, D.slot i < Y)
    (hv : ∀ i < nrs, Sphincs.verifyWithKeccak (D.pk i) (D.msg i) (D.sig i) = true) (C T B : ℕ) {R : ℕ → Prop}
    (hR : (∀ i < nrs, R (C + D.slot i) ∧ ∀ o < 4, R (T + 4 * D.slot i + o)) ∧ ∀ v < 256, R (B + v))
    {P : Reader → Prop}
    (hP : ∀ rd, LowDef k rd → P rd →
      RawSPre D nrs nrx (ptrAt C) (ptrAt T) (ptrAt B) rd ∧ ∀ j < Y, (rd (addressOfIndex j)).isSome) (lo : ℕ) :
    AtEveryB al k name% «main_loop3» (l3Args 0 nrs Y nrx (ptrAt C) (ptrAt T) (ptrAt B)) [] R P (RawSPost D 0 nrs)
      (loopBlock name% «main_loop3» nrs) lo (2 ^ 60) (2 ^ 40) := by
  intro fp cur _ _
  refine ⟨(l3Step al)^[nrs] cur, fun _ => by
      have h := l3Iter_le al nrs cur
      have : nrs * 2 ^ 19 ≤ 2 ^ 19 * 2 ^ 19 := Nat.mul_le_mul_right _ hnrs.le
      omega,
    (callAtA_of_callCompletes0 (fs := B2C.fs) (al := al) (cert := B2C.cert) l3_pureIn
    List.mem_cons_self (le_l3Iter al nrs cur) (main_loop3_completesA hk (by omega) D hs hv C T B hR hP 0 h0)
    fun rd t _ _ _ _ _ hq => ⟨by simpa using hq.2.1, by simpa using hq.2.2.1 cur, hq.2.2.2.1, hq.2.2.2.2⟩).mono
    (fun _ h => h) (fun _ h => h) (fun _ h => h) (fun _ h => h) fun _ _ _ hq => hq.1⟩

end
end LeanVM.Guest.Complete
