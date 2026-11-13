/-
  LeanVM.Guest.B1.Tables.VtC.AWeight

  **`verify_tables` is complete, placed, within its bound, by a tree within its weights**: its
  callees' weights by their certificates (`WeightLe`), `shared_selector_tables`' on its run length,
  the rounds loop's at the honest round count (at most `32`).
-/

module

public import LeanVM.Guest.B1.Tables.VtC.ABound
public import LeanVM.Guest.B1.Selectors.SharedWeight
public import LeanVM.Guest.Budget.Weighs
public import LeanVM.Guest.Data.NameStrings

/-!
# `verify_tables` within its weights

For weights `ω i` (one per index `i`, an opcode's instructions per frame): `vtKidW ω Wss W10`, a
callee's tree, if `shared_selector_tables`', within `Wss i`, if `verify_tables_loop0`'s, within `W10
i`, on every valid run (`Budget.WeighsLe`). `verify_tables_completeAtTBW`:
`verify_tables_completeAtTB` by a node of honest shape (`Budget.NodeHonest`) whose entered callees
are `vtKidW`, the shared tables' within `Wss` on every run length `g^n`, `n < 64`, the rounds loop
`K10w` an iteration (`Budget.LoopW`) at the honest round count `H.n ≤ 32`. `vt_weight_le`: such a
node, valid, weighs at most its frame's weight and `vtBs (Kw i) (Wss i) (32 · K10w i)`, its other
callees within their certificates' `Kw i`. `verify_tables_completeAtTBW'`: by a tree within those
weights.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Fwd
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

/-- **A callee of `verify_tables` within its weights**: the shared tables' within `Wss i`, the
rounds loop's within `W10 i`, on every valid run. -/
def vtKidW {ι : Type} (ω : ι → String → ℕ) (Wss W10 : ι → ℕ) (t : Tree) : Prop :=
  ∀ i, (t.name = "shared_selector_tables" → Budget.WeighsLe coreProgram (ω i) (Wss i) t) ∧
    (t.name = name% «verify_tables_loop0» → Budget.WeighsLe coreProgram (ω i) (W10 i) t)

variable {fs : String → ℕ} {cert : String → V → ℕ}

set_option maxRecDepth 20000 in
/-- **`verify_tables` is complete, placed, within its bound, by a node of honest shape whose
callees are within their weights.** -/
theorem verify_tables_completeAtTBW {κ : ℕ} (hκ : 14 ≤ κ) {H : VtHonest} (h : H.Ok)
    (hs : VtShape H) (B : VtBases) (Kf : String → ℕ) (Ksh K10 : ℕ)
    (hKf : ∀ g ∈ vtKidS, g ≠ name% «verify_tables_loop0» → g ≠ name% «shared_selector_tables_loop0»
        → g ≠ "shared_selector_tables" →
      TotalLe coreProgram fs g (fun _ ↦ Kf g))
    (hsh : TotalLeOn coreProgram fs "shared_selector_tables"
      (fun a ↦ ∃ n < 64, a.getD 5 0 = gen ^ n) (fun _ ↦ Ksh))
    (h10 : TotalLeOn coreProgram fs name% «verify_tables_loop0» LoopPre
      (fun a ↦ logG (a.getD 1 0) * K10 + fs name% «verify_tables_loop0»))
    {ι : Type} (ω : ι → String → ℕ) (Wss K10w : ι → ℕ)
    (hssw : ∀ i (rd : Reader) (t : Tree) (args rets : List E), t.name = "shared_selector_tables" →
      (∃ n < 64, args.getD 5 0 = gen ^ n) → t.Valid coreProgram rd args rets →
      t.BufsOk coreProgram → t.weight (ω i) ≤ Wss i)
    (h10w : ∀ i, Budget.LoopW (ω i) name% «verify_tables_loop0» (K10w i)) :
    CompleteAtDTB fs cert κ "verify_tables" (H.linL B) (H.args B) (Returns (H.retsH B))
      (Budget.NodeHonest coreProgram "verify_tables" (fun σ ↦ ∀ s ∈ vtPre, DispOk σ s)
        (flatCalls vtPre) (fun _ ↦ H.sizes) (List.replicate 119 (vtKidW ω Wss fun i ↦ 32 * K10w i)))
      (fs "verify_tables" + H.sizes.sum + ((vtBs Kf Ksh (vtRunB fs K10 H.n)).sum + ifFrames fs vtPre)) := by
  have hrun : ∀ fp rd, LowDef κ rd → MemL rd (vtL (H.linL B) H.sizes (fun _ ↦ H.ownW B) fs fp) →
      (∀ s ∈ vtPre, VSH (coreProgram.RelIn rd (RegionL (vtL (H.linL B) H.sizes
        (fun _ ↦ H.ownW B) fs fp))) rd (vtσ rd (vtW H (B.at (fp + fs "verify_tables")))
          (H.args B)) s) ∧
      LoadsInBuf (vtσ rd (vtW H (B.at (fp + fs "verify_tables"))) (H.args B))
        (H.bufs (B.at (fp + fs "verify_tables"))) vtPre ∧
      (vtPre.filterMap Main.Stmt.allocSz).map (fun x => x.2.elim id fun s => logG
        (vtσ rd (vtW H (B.at (fp + fs "verify_tables"))) (H.args B) s)) = H.sizes ∧
      ((vtPre.filterMap Main.Stmt.allocSz).map Prod.fst).map
        (vtσ rd (vtW H (B.at (fp + fs "verify_tables"))) (H.args B)) =
        (bases (fp + fs "verify_tables") H.sizes).map (fun b => ofK (addressOfIndex b)) ∧
      vtRets.map (vtσ rd (vtW H (B.at (fp + fs "verify_tables"))) (H.args B)) = H.retsH B := by
    intro fp rd hlow hL
    have hlow14 : LowDefB 14 rd := hlow.mono hκ
    have hm : MemLay rd (H.linL (B.at (fp + fs "verify_tables")) ++
        H.ownL (B.at (fp + fs "verify_tables"))) := hL
    obtain ⟨-, h2, h3, h4, h5⟩ :=
      vt_rel_complete_vtW h hs (B.at (fp + fs "verify_tables")) hlow14 hm
    exact ⟨vt_relIn_complete h hs _ (vtW_ok H _) hlow14 hm, h2, h3, h4, h5⟩
  -- the honest values around the rounds loop's call
  have hvals : ∀ fp rd, LowDef κ rd →
      MemL rd (vtL (H.linL B) H.sizes (fun _ ↦ H.ownW B) fs fp) →
      let σ := vtσ rd (vtW H (B.at (fp + fs "verify_tables"))) (H.args B)
      σ (.n 2544) = gen ^ H.n ∧ σ (.n 2635) = 1 + gen ^ H.n ∧ σ (.n 2636) = 1 := by
    intro fp rd _ _
    have hl : (H.args B).length = 20 := rfl
    have g1 := vt_goodL (rd := rd) (w := vtW H (B.at (fp + fs "verify_tables"))) hl 2591
      [.atom (.hint (.witness "zc_tau_max" (.stack [.n 2544])))] (by decide +kernel)
    have g2 := vt_goodL (rd := rd) (w := vtW H (B.at (fp + fs "verify_tables"))) hl 2664
      [.atom (.const (.n 2634) (word 1 0)), .atom (.add (.n 2635) (.n 2634) (.n 2544)),
        .atom (.const (.n 2636) (word 1 0))] (by decide +kernel)
    generalize vtσ rd (vtW H (B.at (fp + fs "verify_tables"))) (H.args B) = σ at g1 g2 ⊢
    simp only [GoodL, GoodS, fixNe, Good, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq, and_true] at g1 g2
    obtain ⟨c19, a20, c21⟩ := g2
    have w17 : σ (.n 2544) = gen ^ H.n := by
      rw [g1]; exact (vtW_ok H (B.at (fp + fs "verify_tables"))).w2544
    refine ⟨w17, ?_, ?_⟩
    · rw [a20, c19, w17, tb_word_one]
    · rw [c21, tb_word_one]
  have hn32 : H.n < 33 := by
    have := hs.hτ33
    unfold VtHonest.n
    have hall : ∀ x ∈ tableHeightsOf H.rows, x < 33 := by
      intro x hx
      obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hx
      have ht6 : t < 6 := by
        have h6 := hs.hr
        have ht' := ht
        unfold tableHeightsOf at ht'
        rw [List.length_zipWith] at ht'
        omega
      have := hs.hτ33 t ht6
      rw [vtHt, List.getD_eq_getElem _ _ ht] at this
      exact this
    clear this
    generalize tableHeightsOf H.rows = l at hall
    have : ∀ a, a < 33 → l.foldl max a < 33 := by
      induction l with
      | nil => intro a ha; exact ha
      | cons x l ih =>
        intro a ha
        exact ih (fun y hy ↦ hall y (List.mem_cons_of_mem _ hy)) _
          (max_lt ha (hall x List.mem_cons_self))
    exact this 0 (by norm_num)
  -- a callee within its weights
  have hkw : ∀ fp rd, LowDef κ rd → MemL rd (vtL (H.linL B) H.sizes (fun _ ↦ H.ownW B) fs fp) →
      ∀ (i : ℕ) (c : Call), (flatCalls vtPre (vtσ rd (vtW H (B.at (fp + fs "verify_tables")))
        (H.args B)))[i]? = some c → c.taken = true → ∀ (t : Tree) (r : List E), t.name = c.f →
        t.Valid coreProgram rd (c.args.map (vtσ rd (vtW H (B.at (fp + fs "verify_tables")))
          (H.args B))) r → t.BufsOk coreProgram → vtKidW ω Wss (fun i ↦ 32 * K10w i) t := by
    intro fp rd hlow hL i c hc ht t r hn hv hbo j
    obtain ⟨hvsh, -⟩ := hrun fp rd hlow hL
    obtain ⟨v17, v20, v21⟩ := hvals fp rd hlow hL
    generalize vtσ rd (vtW H (B.at (fp + fs "verify_tables"))) (H.args B) = σ at hvsh v17 v20 v21 hc hv
    obtain ⟨s, hs', tup, hst, rfl⟩ := flatCalls_getElem vtPre i c hc
    obtain ⟨hsm, -⟩ := getElem?_filter_mem hs'
    have hkind := List.all_eq_true.mp vt_callKinds s hsm
    have hvs := hvsh s hsm
    cases s with
    | call f a rr =>
      simp only [Stmt.callSF, Main.Stmt.callS, Option.some.injEq] at hst
      subst hst
      simp only [mkCall] at hn hv ⊢
      simp only [vtCallKindB, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.or_eq_true,
        beq_iff_eq, List.isEmpty_iff] at hkind
      obtain ⟨⟨h10', -⟩, hsh'⟩ := hkind
      refine ⟨fun hfs ↦ ?_, fun hfs ↦ absurd (hn.symm.trans hfs) h10'⟩
      have hf : f = "shared_selector_tables" := hn.symm.trans hfs
      subst hf
      obtain ⟨ha6, hr0⟩ := hsh'.resolve_left (by simp)
      subst hr0
      have hrel : coreProgram.Rel rd "shared_selector_tables" (a.map σ) [] :=
        Program.RelIn.rel hvs
      have hout := shared_selector_tables_holds rd _ _ hrel
      obtain ⟨a0, a1, a2, a3, a4, a5, rfl⟩ : ∃ a0 a1 a2 a3 a4 a5, a = [a0, a1, a2, a3, a4, a5] := by
        match a, ha6 with
        | [a0, a1, a2, a3, a4, a5], _ => exact ⟨a0, a1, a2, a3, a4, a5, rfl⟩
      simp only [List.map_cons, List.map_nil, SharedSelOut] at hout
      obtain ⟨m, hm, hlen, -⟩ := hout
      exact Budget.weighsLe_of_on (hssw j) hn hv ⟨m, hm, by simpa using hlen⟩
    | callIf cnd f a =>
      simp only [Stmt.callSF, Main.Stmt.callS, Option.some.injEq] at hst
      subst hst
      simp only [mkCall, decide_eq_true_eq] at hn hv ht ⊢
      simp only [vtCallKindB, Bool.and_eq_true, beq_iff_eq] at hkind
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hkind
      refine ⟨fun hfs ↦ absurd (hn.symm.trans hfs) (by decide), fun _ ↦ ?_⟩
      have hn0 : H.n ≠ 0 := by
        intro h0; apply ht; rw [v20, h0, pow_zero]; exact e_add_eq_zero_iff.mpr rfl
      refine Budget.weighsLe_of_on (Pre := fun args ↦ ∃ e, e ≠ 0 ∧ e ≤ 32 ∧ args.getD 0 0 = 1 ∧
        args.getD 1 0 = gen ^ e) (fun rd' t' args' rets' hn' ⟨e, he0, he, h0, h1⟩ hv' hb' ↦ ?_)
        hn hv ⟨H.n, hn0, by omega, by simp [v21], by simp [v17]⟩
      have := (h10w j).at hn' hv' hb' h0 h1 he0 (by omega)
      exact this.trans (Nat.mul_le_mul_right _ he)
    | dispatch x fs' a rr =>
      simp only [Stmt.callSF, Option.some.injEq] at hst
      subst hst
      obtain ⟨jj, hj, hxj, -⟩ := hvs
      have hok := List.all_eq_true.mp vtFlat.hcall _ hsm
      simp only [callOk, Bool.and_eq_true, decide_eq_true_eq] at hok
      simp only [vtCallKindB, List.all_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq] at hkind
      have hlog : logG (σ x) = jj := by rw [hxj]; exact logG_spec (hj.trans hok.2)
      simp only [mkCall, hlog, List.getD_eq_getElem _ _ hj] at hn
      obtain ⟨⟨k1, -⟩, k2⟩ := hkind _ (List.getElem_mem hj)
      exact ⟨fun hfs ↦ absurd (hn.symm.trans hfs) k2, fun hfs ↦ absurd (hn.symm.trans hfs) k1⟩
    | _ => simp [Stmt.callSF, Main.Stmt.callS] at hst
  refine (flat_completeAtTB vtFlat (H.linL B) (H.args B) (H.retsH B) rfl H.sizes
    (fun _ ↦ H.ownW B) (fun _ ↦ by rw [← ownW_lengths H B]; exact forall₂_length_le _)
    (fun fp ↦ vtW H (B.at (fp + fs "verify_tables")))
    (fun fp ↦ H.bufs (B.at (fp + fs "verify_tables"))) ?hbufs ?hrun (fun σ ↦ ∀ s ∈ vtPre, DispOk σ s)
    (List.replicate 119 (vtKidW ω Wss fun i ↦ 32 * K10w i)) ?hQ
    (by change (vtPre.filter callB).length ≤ _; rw [vt_ncalls]; simp)
    (fun fp rd hlow hL i c hc ht t r hn hv hbo ↦ by
      have hk := hkw fp rd hlow hL i c hc ht t r hn hv hbo
      simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]; split <;> simp_all)
    (vtBs Kf Ksh (vtRunB fs K10 H.n)) _ ?hB
    (fun σ ↦ callsBound_le vtPre σ (vtBs Kf Ksh (vtRunB fs K10 H.n)))).mono le_rfl fun _ h ↦ h
  case hQ =>
    intro fp rd hlow hL s hs
    cases s with
    | dispatch x fs' a rr =>
      obtain ⟨jj, hj, hxj, -⟩ := (hrun fp rd hlow hL).1 _ hs
      have hok := List.all_eq_true.mp vtFlat.hcall _ hs
      simp only [callOk, Bool.and_eq_true, decide_eq_true_eq] at hok
      exact ⟨jj, hj, by omega, hxj⟩
    | _ => trivial
  case hbufs =>
    intro fp q hq
    obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
    refine ⟨q'.1, rfl, fun i hi ↦ ?_⟩
    unfold RegionL
    exact ⟨q', hq', by omega, by omega⟩
  case hrun =>
    intro fp rd hlow hL
    have h := hrun fp rd hlow hL
    exact ⟨h.1, fun d p off hm ↦ h.2.1 d p off (vtEvL_load_mem hm), h.2.2⟩
  case hB =>
    intro fp rd hlow hL i c hc ht rd' hlow' hL' t r hn hv hbo
    obtain ⟨hvsh, -⟩ := hrun fp rd hlow hL
    obtain ⟨v17, v20, v21⟩ := hvals fp rd hlow hL
    change (flatCalls vtPre (vtσ rd (vtW H (B.at (fp + fs "verify_tables"))) (H.args B)))[i]? =
      some c at hc
    change t.Valid coreProgram rd'
      (c.args.map (vtσ rd (vtW H (B.at (fp + fs "verify_tables"))) (H.args B))) r at hv
    generalize vtσ rd (vtW H (B.at (fp + fs "verify_tables"))) (H.args B) = σ at hvsh v17 v20 v21 hc hv
    obtain ⟨s, hs, tup, hst, rfl⟩ := flatCalls_getElem vtPre i c hc
    obtain ⟨hsm, -⟩ := getElem?_filter_mem hs
    have hbi : (vtBs Kf Ksh (vtRunB fs K10 H.n)).getD i 0 = vtCallBnd Kf Ksh (vtRunB fs K10 H.n) s := by
      simp [vtBs, List.getD_eq_getElem?_getD, hs]
    rw [hbi]
    have hok := List.all_eq_true.mp vtFlat.hcall s hsm
    have hkind := List.all_eq_true.mp vt_callKinds s hsm
    have hvs := hvsh s hsm
    cases s with
    | call f a rr =>
      simp only [Stmt.callSF, Main.Stmt.callS, Option.some.injEq] at hst
      subst hst
      simp only [mkCall] at hn hv ⊢
      simp only [callOk, List.contains_iff_mem] at hok
      simp only [vtCallKindB, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.or_eq_true,
        beq_iff_eq, List.isEmpty_iff] at hkind
      obtain ⟨⟨h10', h9'⟩, hsh'⟩ := hkind
      simp only [vtCallBnd]
      split
      · rename_i hfs
        subst hfs
        obtain ⟨ha6, hr0⟩ := hsh'.resolve_left (by simp)
        subst hr0
        have hrel : coreProgram.Rel rd "shared_selector_tables" (a.map σ) [] :=
          Program.RelIn.rel hvs
        have hout := shared_selector_tables_holds rd _ _ hrel
        obtain ⟨a0, a1, a2, a3, a4, a5, rfl⟩ : ∃ a0 a1 a2 a3 a4 a5, a = [a0, a1, a2, a3, a4, a5] := by
          match a, ha6 with
          | [a0, a1, a2, a3, a4, a5], _ => exact ⟨a0, a1, a2, a3, a4, a5, rfl⟩
        simp only [List.map_cons, List.map_nil, SharedSelOut] at hout
        obtain ⟨m, hm, hlen, -⟩ := hout
        exact hsh rd' t _ r hn ⟨m, hm, by simpa using hlen⟩ hv hbo
      · rename_i hfs
        exact hKf f hok h10' h9' hfs rd' t _ r hn hv hbo
    | callIf cnd f a =>
      simp only [Stmt.callSF, Main.Stmt.callS, Option.some.injEq] at hst
      subst hst
      simp only [mkCall, decide_eq_true_eq] at hn hv ht ⊢
      simp only [vtCallKindB, Bool.and_eq_true, beq_iff_eq] at hkind
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hkind
      simp only [vtCallBnd]
      have hn0 : 0 < H.n := by
        rcases Nat.eq_zero_or_pos H.n with h0 | h0
        · exfalso; apply ht; rw [v20, h0, pow_zero]; exact e_add_eq_zero_iff.mpr rfl
        · exact h0
      have hpre : LoopPre ([V.n 2636, V.n 2544, V.n 2627, V.n 18, V.n 16, V.n 2544, V.n 2630].map σ) := by
        simp only [List.map_cons, List.map_nil, v21, v17]
        exact loopPre_gen hn0 (by omega) _
      have := h10 rd' t _ r hn hpre hv hbo
      simp only [List.map_cons, List.getD_cons_succ, List.getD_cons_zero, v17,
        gen_pow_eq_ofK] at this
      rw [logG_spec (by omega)] at this
      unfold vtRunB
      rw [ite_neg' (show ¬H.n = 0 by omega)]
      exact this
    | dispatch x fs' a rr =>
      simp only [Stmt.callSF, Option.some.injEq] at hst
      subst hst
      obtain ⟨j, hj, hxj, -⟩ := hvs
      simp only [callOk, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem,
        decide_eq_true_eq] at hok
      simp only [vtCallKindB, List.all_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq] at hkind
      have hlog : logG (σ x) = j := by rw [hxj]; exact logG_spec (by omega)
      simp only [mkCall, hlog, List.getD_eq_getElem _ _ hj] at hn hv ⊢
      simp only [vtCallBnd]
      obtain ⟨⟨k1, k9⟩, k2⟩ := hkind _ (List.getElem_mem hj)
      exact (hKf _ (hok.1 _ (List.getElem_mem hj)) k1 k9 k2 rd' t _ r hn hv hbo).trans
        (le_foldr_max (List.mem_map.mpr ⟨_, List.getElem_mem hj, rfl⟩))
    | _ => simp [Stmt.callSF, Main.Stmt.callS] at hst


/-- **A call's weight bound by its callee**: the shared tables' `Wss`, the rounds loop's `W10`, the
others' `Kw`. -/
def vtCallW (Kw : String → ℕ) (Wss W10 : ℕ) (f : String) : ℕ :=
  if f = "shared_selector_tables" then Wss else if f = name% «verify_tables_loop0» then W10 else Kw
      f

/-- **The entered calls of a flat body weigh at most** the bounds of their statements. -/
theorem callsW_flatCalls_le {σ : Val} (W : Call → ℕ) (bnd : Stmt → ℕ) : ∀ (pre : List Stmt),
    (∀ s ∈ pre, ∀ tup, Stmt.callSF σ s = some tup → W (Main.mkCall σ tup) ≤ bnd s) →
    Budget.callsW W (flatCalls pre σ) ≤ ((pre.filter callB).map bnd).sum
  | [], _ => by simp [flatCalls, Budget.callsW]
  | s :: ss, h => by
    have ih := callsW_flatCalls_le W bnd ss fun s' hs' => h s' (List.mem_cons_of_mem _ hs')
    unfold Budget.callsW flatCalls at ih ⊢
    rcases hs : Stmt.callSF σ s with _ | tup
    · simp only [List.filterMap_cons, hs]
      refine ih.trans ?_
      rw [List.filter_cons]
      split <;> simp
    · have hb : callB s = true := by
        cases s <;> simp_all [callB, Stmt.callSF, Main.Stmt.callS]
      have := h s List.mem_cons_self tup hs
      simp only [List.filterMap_cons, hs, List.map_cons, List.sum_cons, List.filter_cons, hb,
        ↓reduceIte]
      split <;> omega

/-- **`verify_tables`' node of honest shape weighs at most** its frame's weight and its calls'
bounds: the shared tables' `Wss i`, the rounds loop's `32 · K10w i`, the others' `Kw i`. -/
theorem vt_weight_le {ι : Type} (ω : ι → String → ℕ) (Kw : ι → String → ℕ) (Wss K10w : ι → ℕ)
    (hKw : ∀ i, ∀ g ∈ vtKidS, g ≠ name% «verify_tables_loop0» → g ≠
        name% «shared_selector_tables_loop0» → g ≠ "shared_selector_tables" →
      WeightLe coreProgram (ω i) g (fun _ ↦ Kw i g))
    {sizes : List ℕ} {t : Tree} {rd : Reader} {args rets : List E}
    (h : Budget.NodeHonest coreProgram "verify_tables" (fun σ ↦ ∀ s ∈ vtPre, DispOk σ s)
      (flatCalls vtPre) (fun _ ↦ sizes) (List.replicate 119 (vtKidW ω Wss fun i ↦ 32 * K10w i)) t)
    (hv : t.Valid coreProgram rd args rets) (hb : t.BufsOk coreProgram) (i : ι) :
    t.weight (ω i) ≤ ω i "verify_tables" + (vtBs (Kw i) (Wss i) (32 * K10w i)).sum := by
  have hB : ∀ σ', (∀ s ∈ vtPre, DispOk σ' s) → ∀ c T,
      (c, T) ∈ (flatCalls vtPre σ').zip (List.replicate 119 (vtKidW ω Wss fun i ↦ 32 * K10w i)) →
      c.taken = true → ∀ (t' : Tree) (rets' : List E), t'.name = c.f →
      t'.Valid coreProgram rd (c.args.map σ') rets' → t'.BufsOk coreProgram → T t' →
      t'.weight (ω i) ≤ vtCallW (Kw i) (Wss i) (32 * K10w i) c.f := by
    intro σ' hQ' c T hc ht t' rets' hn hv' hb' hT
    have hTe : T = vtKidW ω Wss fun i ↦ 32 * K10w i :=
      List.eq_of_mem_replicate (List.of_mem_zip hc).2
    subst hTe
    have hcm := (List.of_mem_zip hc).1
    obtain ⟨k, hk⟩ := List.getElem?_of_mem hcm
    obtain ⟨s, hs', tup, hst, rfl⟩ := flatCalls_getElem vtPre k c hk
    obtain ⟨hsm, -⟩ := getElem?_filter_mem hs'
    have hkind := List.all_eq_true.mp vt_callKinds s hsm
    have hok := List.all_eq_true.mp vtFlat.hcall s hsm
    simp only [vtCallW]
    split
    · exact (hT i).1 (by rwa [hn]) rd _ _ hv' hb'
    split
    · exact (hT i).2 (by rwa [hn]) rd _ _ hv' hb'
    rename_i hsh h10
    have hf : ∀ g, (Main.mkCall σ' tup).f = g → g ∈ vtKidS ∧ g ≠
        name% «shared_selector_tables_loop0» := by
      intro g hg
      cases s with
      | call f a rr =>
        simp only [Stmt.callSF, Main.Stmt.callS, Option.some.injEq] at hst
        subst hst
        simp only [Main.mkCall] at hg
        subst hg
        simp only [callOk, List.contains_iff_mem] at hok
        simp only [vtCallKindB, Bool.and_eq_true, bne_iff_ne, ne_eq] at hkind
        exact ⟨hok, hkind.1.2⟩
      | callIf cnd f a =>
        simp only [Stmt.callSF, Main.Stmt.callS, Option.some.injEq] at hst
        subst hst
        simp only [vtCallKindB, Bool.and_eq_true, beq_iff_eq] at hkind
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hkind
        simp [Main.mkCall] at h10
      | dispatch x fs' a rr =>
        simp only [Stmt.callSF, Option.some.injEq] at hst
        subst hst
        obtain ⟨jj, hj, hjb, hxj⟩ := hQ' _ hsm
        have hlog : logG (σ' x) = jj := by rw [hxj]; exact logG_spec hjb
        simp only [Main.mkCall, hlog, List.getD_eq_getElem _ _ hj] at hg
        subst hg
        simp only [callOk, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem,
          decide_eq_true_eq] at hok
        simp only [vtCallKindB, List.all_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq] at hkind
        exact ⟨hok.1 _ (List.getElem_mem hj), (hkind _ (List.getElem_mem hj)).1.2⟩
      | _ => simp [Stmt.callSF, Main.Stmt.callS] at hst
    obtain ⟨hmem, h9⟩ := hf _ rfl
    exact hKw i _ hmem h10 h9 hsh rd t' _ rets' hn hv' hb'
  obtain ⟨σ, hQ, hle⟩ := Budget.NodeHonest.weight_le (ω i)
    (fun _ c ↦ vtCallW (Kw i) (Wss i) (32 * K10w i) c.f) h hv hb hB
  · refine hle.trans (Nat.add_le_add_left (callsW_flatCalls_le _ _ vtPre ?_) _)
    intro s hs tup hst
    have hkind := List.all_eq_true.mp vt_callKinds s hs
    cases s with
    | call f a rr =>
      simp only [Stmt.callSF, Main.Stmt.callS, Option.some.injEq] at hst
      subst hst
      simp only [vtCallKindB, Bool.and_eq_true, bne_iff_ne, ne_eq] at hkind
      show vtCallW (Kw i) (Wss i) (32 * K10w i) f ≤ vtCallBnd (Kw i) (Wss i) (32 * K10w i) (.call f a rr)
      by_cases h1 : f = "shared_selector_tables" <;> simp [vtCallW, vtCallBnd, h1, hkind.1.1]
    | callIf cnd f a =>
      simp only [Stmt.callSF, Main.Stmt.callS, Option.some.injEq] at hst
      subst hst
      simp only [vtCallKindB, Bool.and_eq_true, beq_iff_eq] at hkind
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hkind
      simp [Main.mkCall, vtCallW, vtCallBnd]
    | dispatch x fs' a rr =>
      simp only [Stmt.callSF, Option.some.injEq] at hst
      subst hst
      obtain ⟨jj, hj, hjb, hxj⟩ := hQ _ hs
      simp only [vtCallKindB, List.all_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq] at hkind
      have hlog : logG (σ x) = jj := by rw [hxj]; exact logG_spec hjb
      show vtCallW (Kw i) (Wss i) (32 * K10w i) (fs'.getD (logG (σ x)) "") ≤
        vtCallBnd (Kw i) (Wss i) (32 * K10w i) (.dispatch x fs' a rr)
      rw [hlog, List.getD_eq_getElem _ _ hj]
      obtain ⟨⟨k1, -⟩, k2⟩ := hkind _ (List.getElem_mem hj)
      simp only [vtCallW, vtCallBnd, k1, k2, ↓reduceIte]
      exact le_foldr_max (List.mem_map.mpr ⟨_, List.getElem_mem hj, rfl⟩)
    | _ => simp [Stmt.callSF, Main.Stmt.callS] at hst

/-- **`verify_tables` is complete, placed, within its bound, by a tree within its weights**:
`ω i "verify_tables" + (vtBs (Kw i) (Wss i) (32 · K10w i)).sum` at each `ω i`. -/
theorem verify_tables_completeAtTBW' {κ : ℕ} (hκ : 14 ≤ κ) {H : VtHonest} (h : H.Ok)
    (hs : VtShape H) (B : VtBases) (Kf : String → ℕ) (Ksh K10 : ℕ)
    (hKf : ∀ g ∈ vtKidS, g ≠ name% «verify_tables_loop0» → g ≠ name% «shared_selector_tables_loop0»
        → g ≠ "shared_selector_tables" →
      TotalLe coreProgram fs g (fun _ ↦ Kf g))
    (hsh : TotalLeOn coreProgram fs "shared_selector_tables"
      (fun a ↦ ∃ n < 64, a.getD 5 0 = gen ^ n) (fun _ ↦ Ksh))
    (h10 : TotalLeOn coreProgram fs name% «verify_tables_loop0» LoopPre
      (fun a ↦ logG (a.getD 1 0) * K10 + fs name% «verify_tables_loop0»))
    {ι : Type} (ω : ι → String → ℕ) (Kw : ι → String → ℕ) (Wss K10w : ι → ℕ)
    (hKw : ∀ i, ∀ g ∈ vtKidS, g ≠ name% «verify_tables_loop0» → g ≠
        name% «shared_selector_tables_loop0» → g ≠ "shared_selector_tables" →
      WeightLe coreProgram (ω i) g (fun _ ↦ Kw i g))
    (hssw : ∀ i (rd : Reader) (t : Tree) (args rets : List E), t.name = "shared_selector_tables" →
      (∃ n < 64, args.getD 5 0 = gen ^ n) → t.Valid coreProgram rd args rets →
      t.BufsOk coreProgram → t.weight (ω i) ≤ Wss i)
    (h10w : ∀ i, Budget.LoopW (ω i) name% «verify_tables_loop0» (K10w i)) :
    CompleteAtDTB fs cert κ "verify_tables" (H.linL B) (H.args B) (Returns (H.retsH B))
      (fun t ↦ ∀ i, Budget.WeighsLe coreProgram (ω i)
        (ω i "verify_tables" + (vtBs (Kw i) (Wss i) (32 * K10w i)).sum) t)
      (fs "verify_tables" + H.sizes.sum + ((vtBs Kf Ksh (vtRunB fs K10 H.n)).sum + ifFrames fs vtPre)) :=
  (verify_tables_completeAtTBW hκ h hs B Kf Ksh K10 hKf hsh h10 ω Wss K10w hssw h10w).mono le_rfl
    fun _ ht i _ _ _ hv hb ↦ vt_weight_le ω Kw Wss K10w hKw ht hv hb i

end
end LeanVM.Guest.B1.Tables
