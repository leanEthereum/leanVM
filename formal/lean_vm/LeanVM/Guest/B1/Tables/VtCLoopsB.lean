/-
  LeanVM.Guest.B1.Tables.VtCLoopsB

  `verify_tables`' loops complete, placed, by bounded trees: the 65 selector loops, the two index
  loops, the table sumcheck's rounds (`__loop79`) and its equality prefix (`__loop80`).
-/

module

public import LeanVM.Guest.B1.Tables.VerifyTablesCLoops
public import LeanVM.Guest.B1.Tables.VtCPadB

/-!
# `verify_tables`' loops, placed, bounded

Each loop is pure (`VtCPad`) and a `mul_range` loop over a straight-line body with no `HeapBuf`
(`vtc_loop_total`): `m` iterations weigh at most `m` frames and their callees (none, or one
`sumcheck_round4` for `__loop79`), plus the frame of the last tail, set up and not entered. The
lifts (`sel_completeAtB`, `idx_completeAtB`, `loop79_completeAtB`, `loop80_completeAtB`) take
the iterations' words on every memory agreeing with an honest one on `Lin`, and their `D` twins
follow.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ} {Θ : Type} {w : Θ → String → ℕ}

private theorem vtcl_mem {l : List Stmt} {s : Stmt} (i : ℕ) (h : l[i]? = some s) : s ∈ l :=
  List.mem_of_getElem? h

/-- A loop's step: `x·g + N` and `x·g` from the five statements at `i`. -/
theorem vtcl_tail {rd : Reader} {σ : Val} {pre : List Stmt}
    (hes : ∀ e ∈ pre.flatMap (Main.slEvs σ), e.Holds rd σ) (v i : ℕ)
    (h0 : pre[i]? = some (.atom (.const (.n v) (word 2 0 0))))
    (h1 : pre[i + 1]? = some (.atom (.mul (.n (v + 1)) (.n 0) (.n v))))
    (h2 : pre[i + 2]? = some (.atom (.add (.n (v + 2)) (.n (v + 1)) (.n 1))))
    (h3 : pre[i + 3]? = some (.atom (.const (.n (v + 3)) (word 2 0 0))))
    (h4 : pre[i + 4]? = some (.atom (.mul (.n (v + 4)) (.n 0) (.n (v + 3))))) :
    σ (.n (v + 2)) = σ (.n 0) * gen + σ (.n 1) ∧ σ (.n (v + 4)) = σ (.n 0) * gen := by
  have a0 := vtc_atom hes (vtcl_mem _ h0)
  have a1 := vtc_atom hes (vtcl_mem _ h1)
  have a2 := vtc_atom hes (vtcl_mem _ h2)
  have a3 := vtc_atom hes (vtcl_mem _ h3)
  have a4 := vtc_atom hes (vtcl_mem _ h4)
  simp only [Atom.Holds, word_gen] at a0 a1 a2 a3 a4
  exact ⟨by rw [a2, a1, a0], by rw [a4, a3]⟩

theorem vtcl_nokids {rd : Reader} {σ : Val} {kids : List Tree}
    (hk : Tree.KidsValid coreProgram rd σ
      (List.map (Main.mkCall σ) ([] : List (Option V × String × List V × List V))) kids) :
    Tree.totalKids fs kids ≤ 0 := by
  match kids, hk with
  | [], _ => simp [Tree.totalKids]

/-! ## The selector loops -/

noncomputable def vtcSelP : List Stmt := (selPre "").take 33

theorem vtc_selP_ok : vtcSelP.all Main.Stmt.straight = true ∧ vtcSelP.filterMap Main.Stmt.allocSz = [] ∧
    vtcSelP.filterMap Main.Stmt.callS = [] := by decide +kernel

theorem vtc_sel_body {self : String} (hok : selOk self = true) : ∃ fn, coreProgram.find? self = some fn ∧
    fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7] ∧
    fn.body = vtcSelP ++ [.callIf (.n 35) self [.n 37, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7], .ret []] := by
  unfold selOk at hok
  split at hok
  · next f hf =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    exact ⟨f, hf, hok.1, by rw [stmtsEqb_sound hok.2]; rfl⟩
  · exact absurd hok (by simp)

/-- **A selector loop's trees** over `m` iterations. -/
theorem vtc_sel_total {self : String} (hok : selOk self = true) {rd : Reader} {m : ℕ} {rest : List E}
    {t : Tree} {rets : List E} (hm : 0 < m) (hn : t.name = self)
    (hv : t.Valid coreProgram rd (1 :: gen ^ m :: rest) rets) (hbo : t.BufsOk coreProgram) :
    t.total fs ≤ m * (fs self + 0) + fs self := by
  obtain ⟨fn, hf, hpar, hb⟩ := vtc_sel_body hok
  refine vtc_loop_total (fs := fs) hf hb vtc_selP_ok.1 vtc_selP_ok.2.1 rd m rest 0 ?_ m 0 t rets
    (by omega) hm hn (by rwa [pow_zero]) hbo
  intro σ j _ hp hes
  rw [hpar] at hp
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at hp
  obtain ⟨h0, h1, hr⟩ := hp
  subst hr
  obtain ⟨e1, e2⟩ := vtcl_tail hes 33 28 rfl rfl rfl rfl rfl
  refine ⟨by rw [e1, h0, h1], by simp [e2, h0, h1], fun kids hk _ => ?_⟩
  rw [vtc_selP_ok.2.2] at hk
  exact vtcl_nokids hk

/-- **A selector loop is complete, placed, by a bounded tree.** -/
theorem sel_completeAtB {self : String} (hok : selOk self = true) (hsel : self ∈ selNames)
    {sb ec zh go sq ka : E} {m : ℕ} (hm0 : 0 < m) (k : ℕ) {Lin : Main.Layout}
    (hB : ∀ rd, LowDef k rd → MemL rd Lin → ∀ rd' : Reader,
      (∀ i, RegionL Lin i → rd' (gpow i) = rd (gpow i)) → ∀ j < m, SelBody rd' sb ec zh go sq ka (gen ^ j)) :
    CompleteAtB fs cert k self Lin [1, gen ^ m, sb, ec, zh, go, sq, ka] (Returns [])
      (m * (fs self + 0) + fs self) :=
  vtc_completeAt_of_rel_lowB pure_sel hsel k
    (fun rd hl hL rd' hag => sel_complete hok hm0 rfl (hB rd hl hL rd' hag))
    fun _ _ _ _ hn hv hbo => vtc_sel_total hok hm0 hn hv hbo

/-- `sel_completeAtB` within weights. -/
theorem sel_completeAtW {self : String} (hok : selOk self = true) (hsel : self ∈ selNames)
    {sb ec zh go sq ka : E} {m : ℕ} (hm0 : 0 < m) (k : ℕ) {Lin : Main.Layout}
    (hB : ∀ rd, LowDef k rd → MemL rd Lin → ∀ rd' : Reader,
      (∀ i, RegionL Lin i → rd' (gpow i) = rd (gpow i)) → ∀ j < m, SelBody rd' sb ec zh go sq ka (gen ^ j)) :
    Main.CompleteAtW fs cert w k self Lin [1, gen ^ m, sb, ec, zh, go, sq, ka] (Returns [])
      (m * (fs self + 0) + fs self) fun θ => m * (w θ self + 0) + w θ self :=
  Main.CompleteAtB.toW_total (sel_completeAtB hok hsel hm0 k hB) fun _ _ _ _ hn hv hbo =>
    vtc_sel_total hok hm0 hn hv hbo

theorem sel_completeAtD {self : String} (hok : selOk self = true) (hsel : self ∈ selNames)
    {sb ec zh go sq ka : E} {m : ℕ} (hm0 : 0 < m) (k : ℕ) {Lin : Main.Layout}
    (hB : ∀ rd, LowDef k rd → MemL rd Lin → ∀ rd' : Reader,
      (∀ i, RegionL Lin i → rd' (gpow i) = rd (gpow i)) → ∀ j < m, SelBody rd' sb ec zh go sq ka (gen ^ j)) :
    CompleteAtD fs cert k self Lin [1, gen ^ m, sb, ec, zh, go, sq, ka] (Returns []) :=
  (sel_completeAtB (fs := fs) (cert := cert) hok hsel hm0 k hB).toCompleteAtD

/-! ## The index loops -/

noncomputable def vtcIdxP : List Stmt := (idxPre "").take 17

theorem vtc_idxP_ok : vtcIdxP.all Main.Stmt.straight = true ∧ vtcIdxP.filterMap Main.Stmt.allocSz = [] ∧
    vtcIdxP.filterMap Main.Stmt.callS = [] := by decide +kernel

theorem vtc_idx_body {self : String} (hok : idxOk self = true) : ∃ fn, coreProgram.find? self = some fn ∧
    fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4] ∧
    fn.body = vtcIdxP ++ [.callIf (.n 18) self [.n 20, .n 1, .n 2, .n 3, .n 4], .ret []] := by
  unfold idxOk at hok
  split at hok
  · next f hf =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    exact ⟨f, hf, hok.1, by rw [stmtsEqb_sound hok.2]; rfl⟩
  · exact absurd hok (by simp)

/-- **An index loop's trees** over `m` iterations. -/
theorem vtc_idx_total {self : String} (hok : idxOk self = true) {rd : Reader} {m : ℕ} {rest : List E}
    {t : Tree} {rets : List E} (hm : 0 < m) (hn : t.name = self)
    (hv : t.Valid coreProgram rd (1 :: gen ^ m :: rest) rets) (hbo : t.BufsOk coreProgram) :
    t.total fs ≤ m * (fs self + 0) + fs self := by
  obtain ⟨fn, hf, hpar, hb⟩ := vtc_idx_body hok
  refine vtc_loop_total (fs := fs) hf hb vtc_idxP_ok.1 vtc_idxP_ok.2.1 rd m rest 0 ?_ m 0 t rets
    (by omega) hm hn (by rwa [pow_zero]) hbo
  intro σ j _ hp hes
  rw [hpar] at hp
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at hp
  obtain ⟨h0, h1, hr⟩ := hp
  subst hr
  obtain ⟨e1, e2⟩ := vtcl_tail hes 16 12 rfl rfl rfl rfl rfl
  refine ⟨by rw [e1, h0, h1], by simp [e2, h0, h1], fun kids hk _ => ?_⟩
  rw [vtc_idxP_ok.2.2] at hk
  exact vtcl_nokids hk

/-- **An index loop is complete, placed, by a bounded tree.** -/
theorem idx_completeAtB {self : String} (hok : idxOk self = true) (hself : self ∈ ["__loop14", "__loop16"])
    {ch z fac : E} {m : ℕ} (hm0 : 0 < m) (k : ℕ) {Lin : Main.Layout}
    (hB : ∀ rd, LowDef k rd → MemL rd Lin → ∀ rd' : Reader,
      (∀ i, RegionL Lin i → rd' (gpow i) = rd (gpow i)) → ∀ j < m, IdxBody rd' ch z fac (gen ^ j)) :
    CompleteAtB fs cert k self Lin [1, gen ^ m, ch, z, fac] (Returns []) (m * (fs self + 0) + fs self) :=
  vtc_completeAt_of_rel_lowB pure_idx hself k
    (fun rd hl hL rd' hag => idx_complete hok hm0 rfl (hB rd hl hL rd' hag))
    fun _ _ _ _ hn hv hbo => vtc_idx_total hok hm0 hn hv hbo

/-- `idx_completeAtB` within weights. -/
theorem idx_completeAtW {self : String} (hok : idxOk self = true) (hself : self ∈ ["__loop14", "__loop16"])
    {ch z fac : E} {m : ℕ} (hm0 : 0 < m) (k : ℕ) {Lin : Main.Layout}
    (hB : ∀ rd, LowDef k rd → MemL rd Lin → ∀ rd' : Reader,
      (∀ i, RegionL Lin i → rd' (gpow i) = rd (gpow i)) → ∀ j < m, IdxBody rd' ch z fac (gen ^ j)) :
    Main.CompleteAtW fs cert w k self Lin [1, gen ^ m, ch, z, fac] (Returns []) (m * (fs self + 0) + fs self)
      fun θ => m * (w θ self + 0) + w θ self :=
  Main.CompleteAtB.toW_total (idx_completeAtB hok hself hm0 k hB) fun _ _ _ _ hn hv hbo =>
    vtc_idx_total hok hm0 hn hv hbo

theorem idx_completeAtD {self : String} (hok : idxOk self = true) (hself : self ∈ ["__loop14", "__loop16"])
    {ch z fac : E} {m : ℕ} (hm0 : 0 < m) (k : ℕ) {Lin : Main.Layout}
    (hB : ∀ rd, LowDef k rd → MemL rd Lin → ∀ rd' : Reader,
      (∀ i, RegionL Lin i → rd' (gpow i) = rd (gpow i)) → ∀ j < m, IdxBody rd' ch z fac (gen ^ j)) :
    CompleteAtD fs cert k self Lin [1, gen ^ m, ch, z, fac] (Returns []) :=
  (idx_completeAtB (fs := fs) (cert := cert) hok hself hm0 k hB).toCompleteAtD

/-! ## `__loop80` -/

noncomputable def vtcP80 : List Stmt := (Fn.body Data.core139).take 17

theorem vtc_core139 : Fn.body Data.core139 =
    vtcP80 ++ [.callIf (.n 18) "__loop80" [.n 20, .n 1, .n 2, .n 3, .n 4], .ret []] :=
  stmtsEqb_sound (by decide +kernel)

theorem vtc_p80_ok : vtcP80.all Main.Stmt.straight = true ∧ vtcP80.filterMap Main.Stmt.allocSz = [] ∧
    vtcP80.filterMap Main.Stmt.callS = [] := by decide +kernel

/-- **`__loop80`'s trees** over `m` iterations. -/
theorem vtc_l80_total {rd : Reader} {m : ℕ} {rest : List E} {t : Tree} {rets : List E} (hm : 0 < m)
    (hn : t.name = "__loop80") (hv : t.Valid coreProgram rd (1 :: gen ^ m :: rest) rets)
    (hbo : t.BufsOk coreProgram) : t.total fs ≤ m * (fs "__loop80" + 0) + fs "__loop80" := by
  refine vtc_loop_total (fs := fs) find_loop80 vtc_core139 vtc_p80_ok.1 vtc_p80_ok.2.1 rd m rest 0 ?_ m 0 t
    rets (by omega) hm hn (by rwa [pow_zero]) hbo
  intro σ j _ hp hes
  simp only [show Fn.params Data.core139 = [.n 0, .n 1, .n 2, .n 3, .n 4] from rfl, List.map_cons,
    List.map_nil, List.cons.injEq] at hp
  obtain ⟨h0, h1, hr⟩ := hp
  subst hr
  obtain ⟨e1, e2⟩ := vtcl_tail hes 16 12 rfl rfl rfl rfl rfl
  refine ⟨by rw [e1, h0, h1], by simp [e2, h0, h1], fun kids hk _ => ?_⟩
  rw [vtc_p80_ok.2.2] at hk
  exact vtcl_nokids hk

/-- **`__loop80` is complete, placed, by a bounded tree.** -/
theorem loop80_completeAtB {peq zeta chi : E} {m : ℕ} (hm0 : 0 < m) (k : ℕ) {Lin : Main.Layout}
    (hB : ∀ rd, LowDef k rd → MemL rd Lin → ∀ rd' : Reader,
      (∀ i, RegionL Lin i → rd' (gpow i) = rd (gpow i)) → ∀ j < m, PeqBody rd' peq zeta chi (gen ^ j)) :
    CompleteAtB fs cert k "__loop80" Lin [1, gen ^ m, peq, zeta, chi] (Returns [])
      (m * (fs "__loop80" + 0) + fs "__loop80") :=
  vtc_completeAt_of_rel_lowB pure80 (by simp) k
    (fun rd hl hL rd' hag => loop80_complete hm0 (hB rd hl hL rd' hag))
    fun _ _ _ _ hn hv hbo => vtc_l80_total hm0 hn hv hbo

/-- `loop80_completeAtB` within weights. -/
theorem loop80_completeAtW {peq zeta chi : E} {m : ℕ} (hm0 : 0 < m) (k : ℕ) {Lin : Main.Layout}
    (hB : ∀ rd, LowDef k rd → MemL rd Lin → ∀ rd' : Reader,
      (∀ i, RegionL Lin i → rd' (gpow i) = rd (gpow i)) → ∀ j < m, PeqBody rd' peq zeta chi (gen ^ j)) :
    Main.CompleteAtW fs cert w k "__loop80" Lin [1, gen ^ m, peq, zeta, chi] (Returns [])
      (m * (fs "__loop80" + 0) + fs "__loop80") fun θ => m * (w θ "__loop80" + 0) + w θ "__loop80" :=
  Main.CompleteAtB.toW_total (loop80_completeAtB hm0 k hB) fun _ _ _ _ hn hv hbo => vtc_l80_total hm0 hn hv hbo

theorem loop80_completeAtD {peq zeta chi : E} {m : ℕ} (hm0 : 0 < m) (k : ℕ) {Lin : Main.Layout}
    (hB : ∀ rd, LowDef k rd → MemL rd Lin → ∀ rd' : Reader,
      (∀ i, RegionL Lin i → rd' (gpow i) = rd (gpow i)) → ∀ j < m, PeqBody rd' peq zeta chi (gen ^ j)) :
    CompleteAtD fs cert k "__loop80" Lin [1, gen ^ m, peq, zeta, chi] (Returns []) :=
  (loop80_completeAtB (fs := fs) (cert := cert) hm0 k hB).toCompleteAtD

/-! ## `__loop79` -/

noncomputable def vtcP79 : List Stmt := (Fn.body Data.core138).take 27

theorem vtc_core138 : Fn.body Data.core138 =
    vtcP79 ++ [.callIf (.n 28) "__loop79" [.n 30, .n 1, .n 2, .n 3, .n 4, .n 5], .ret []] :=
  stmtsEqb_sound (by decide +kernel)

theorem vtc_p79_ok : vtcP79.all Main.Stmt.straight = true ∧ vtcP79.filterMap Main.Stmt.allocSz = [] ∧
    vtcP79.filterMap Main.Stmt.callS = [(none, "sumcheck_round4", [.n 9, .n 10, .n 11, .n 12],
      [.n 13, .n 14, .n 15, .n 16, .n 17])] := by decide +kernel

set_option maxRecDepth 100000 in
theorem vtc_sr4_leaf : vtcLeafOk "sumcheck_round4" = true := by decide +kernel

/-- **`__loop79`'s trees** over `m` rounds, each with its `sumcheck_round4`. -/
theorem vtc_l79_total {rd : Reader} {m : ℕ} {rest : List E} {t : Tree} {rets : List E} (hm : 0 < m)
    (hn : t.name = "__loop79") (hv : t.Valid coreProgram rd (1 :: gen ^ m :: rest) rets)
    (hbo : t.BufsOk coreProgram) :
    t.total fs ≤ m * (fs "__loop79" + fs "sumcheck_round4") + fs "__loop79" := by
  refine vtc_loop_total (fs := fs) find_loop79 vtc_core138 vtc_p79_ok.1 vtc_p79_ok.2.1 rd m rest _ ?_ m 0 t
    rets (by omega) hm hn (by rwa [pow_zero]) hbo
  intro σ j _ hp hes
  simp only [show Fn.params Data.core138 = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5] from rfl,
    List.map_cons, List.map_nil, List.cons.injEq] at hp
  obtain ⟨h0, h1, hr⟩ := hp
  subst hr
  obtain ⟨e1, e2⟩ := vtcl_tail hes 26 22 rfl rfl rfl rfl rfl
  refine ⟨by rw [e1, h0, h1], by simp [e2, h0, h1], fun kids hk hbk => ?_⟩
  rw [vtc_p79_ok.2.2] at hk
  simp only [List.map_cons, List.map_nil, Main.mkCall] at hk
  match kids, hk, hbk with
  | [k], ⟨hnk, hvk, _⟩, ⟨hbk, _⟩ =>
    simp only [↓reduceIte] at hvk
    simp [Tree.totalKids, vtc_leaf_total_of_ok vtc_sr4_leaf hnk hvk hbk]

/-- **`__loop79` is complete, placed, by a bounded tree.** -/
theorem loop79_completeAtB {rounds chi gn cprod : E} {m : ℕ} (hm0 : 0 < m) (k : ℕ) {Lin : Main.Layout}
    (hB : ∀ rd, LowDef k rd → MemL rd Lin → ∀ rd' : Reader,
      (∀ i, RegionL Lin i → rd' (gpow i) = rd (gpow i)) → ∀ j < m, ZcRound rd' rounds chi gn cprod (gen ^ j)) :
    CompleteAtB fs cert k "__loop79" Lin [1, gen ^ m, rounds, chi, gn, cprod] (Returns [])
      (m * (fs "__loop79" + fs "sumcheck_round4") + fs "__loop79") :=
  vtc_completeAt_of_rel_lowB pure79 (by simp) k
    (fun rd hl hL rd' hag => loop79_complete hm0 (hB rd hl hL rd' hag))
    fun _ _ _ _ hn hv hbo => vtc_l79_total hm0 hn hv hbo

/-- `loop79_completeAtB` within weights. -/
theorem loop79_completeAtW {rounds chi gn cprod : E} {m : ℕ} (hm0 : 0 < m) (k : ℕ) {Lin : Main.Layout}
    (hB : ∀ rd, LowDef k rd → MemL rd Lin → ∀ rd' : Reader,
      (∀ i, RegionL Lin i → rd' (gpow i) = rd (gpow i)) → ∀ j < m, ZcRound rd' rounds chi gn cprod (gen ^ j)) :
    Main.CompleteAtW fs cert w k "__loop79" Lin [1, gen ^ m, rounds, chi, gn, cprod] (Returns [])
      (m * (fs "__loop79" + fs "sumcheck_round4") + fs "__loop79")
      fun θ => m * (w θ "__loop79" + w θ "sumcheck_round4") + w θ "__loop79" :=
  Main.CompleteAtB.toW_total (loop79_completeAtB hm0 k hB) fun _ _ _ _ hn hv hbo => vtc_l79_total hm0 hn hv hbo

theorem loop79_completeAtD {rounds chi gn cprod : E} {m : ℕ} (hm0 : 0 < m) (k : ℕ) {Lin : Main.Layout}
    (hB : ∀ rd, LowDef k rd → MemL rd Lin → ∀ rd' : Reader,
      (∀ i, RegionL Lin i → rd' (gpow i) = rd (gpow i)) → ∀ j < m, ZcRound rd' rounds chi gn cprod (gen ^ j)) :
    CompleteAtD fs cert k "__loop79" Lin [1, gen ^ m, rounds, chi, gn, cprod] (Returns []) :=
  (loop79_completeAtB (fs := fs) (cert := cert) hm0 k hB).toCompleteAtD

end
end LeanVM.Guest.B1.VerifySub
