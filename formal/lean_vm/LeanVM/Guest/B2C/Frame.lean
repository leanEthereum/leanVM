/-
  LeanVM.Guest.B2C.Frame

  What the honest memory holds of an instance's frame: every value its path names at its cell,
  the fixed cells' words, from the sharing check.
-/

module

public import LeanVM.Guest.B2C.Static

/-!
# The frame an instance runs on

`C I` keeps the first candidate at each cell. At a value's cell every candidate carries the
value's word (`cand_val`): a temporary's only if the value is that temporary, a frame run's or a
named value's by the sharing check (`shareOk_path`), a fixed constant cell's by the same, no fixed
frame pointer cell, call site or table target being a value's cell (`valOk`, `apartOk`). So the
honest memory reads each named value at its cell (`read_val`).
-/

namespace LeanVM.Guest.B2C

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Exec LeanVM.Guest.Check

@[expose] public section

/-! ## Bits -/

section Bits

theorem bitsNodup_spec : ∀ (l : List ℕ) (s : ℕ), bitsNodup l s = true → l.Nodup ∧ ∀ c ∈ l, s.testBit c = false
  | [], _, _ => ⟨List.nodup_nil, fun _ h ↦ absurd h List.not_mem_nil⟩
  | c :: cs, s, h => by
    simp only [bitsNodup, Bool.and_eq_true, Bool.not_eq_true', bitN_eq] at h
    obtain ⟨h1, h2⟩ := bitsNodup_spec cs _ h.2
    refine ⟨List.nodup_cons.mpr ⟨fun hc ↦ ?_, h1⟩, fun c' hc' ↦ ?_⟩
    · have := h2 c hc
      rw [testBit_setBit] at this
      simp at this
    · rcases List.mem_cons.mp hc' with rfl | hc'
      · exact h.1
      · have := h2 c' hc'
        rw [testBit_setBit, Bool.or_eq_false_iff] at this
        exact this.1

theorem apart_spec {s t c : ℕ} (h : apart s t = true) (hs : s.testBit c = true) : t.testBit c = false := by
  simp only [apart, nbeq_iff] at h
  have := congrArg (fun x ↦ x.testBit c) h
  simp only [testBit_land', hs, Bool.true_and, Nat.zero_testBit] at this
  exact this

theorem lt_of_testBit_lt {x c n : ℕ} (hx : x < 2 ^ n) (h : x.testBit c = true) : c < n := by
  by_contra hc
  have : x < 2 ^ c := lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (by omega))
  rw [Nat.testBit_lt_two_pow this] at h
  cases h

theorem mem_bitsOf {l : List ℕ} {c : ℕ} (h : c ∈ l) : (bitsOf l).testBit c = true := (testBit_bitsOf l c).mpr h

theorem testBit_lor_l {x y c : ℕ} (h : x.testBit c = true) : (Nat.lor x y).testBit c = true := by
  rw [testBit_lor', h, Bool.true_or]

theorem testBit_lor_r {x y c : ℕ} (h : y.testBit c = true) : (Nat.lor x y).testBit c = true := by
  rw [testBit_lor', h, Bool.or_true]

end Bits

/-! ## The cells apart -/

section Apart

/-- **What `apartOk` says**. -/
structure Apart (j : ℕ) : Prop where
  statTmp : ∀ q ∈ (plumbOf j).stat, ∀ p ∈ (plumbOf j).tmps, p.2 ≠ q.1
  site : ∀ c ∈ siteCells (plumbOf j), (∀ p ∈ (plumbOf j).tmps, p.2 ≠ c) ∧ (∀ p ∈ (plumbOf j).runs, p.2 ≠ c) ∧
    (∀ q ∈ (plumbOf j).stat, q.1 ≠ c) ∧ c ∉ (certOf j).locs
  arm : ∀ a ∈ (plumbOf j).arms, (∀ p ∈ (plumbOf j).tmps, p.2 ≠ a.2.1) ∧ (∀ p ∈ (plumbOf j).runs, p.2 ≠ a.2.1) ∧
    (∀ q ∈ (plumbOf j).stat, q.1 ≠ a.2.1) ∧ a.2.1 ∉ (certOf j).locs ∧ a.2.1 ∉ siteCells (plumbOf j)
  statNodup : ((plumbOf j).stat.map Prod.fst).Nodup
  siteNodup : (siteCells (plumbOf j)).Nodup
  armNodup : ((plumbOf j).arms.map fun a ↦ a.2.1).Nodup
  main : j = 1 → (∀ p ∈ (plumbOf j).tmps, p.2 < 167) ∧ (∀ p ∈ (plumbOf j).runs, p.2 < 167) ∧
    (∀ q ∈ (plumbOf j).stat, q.1 < 167) ∧ (∀ c ∈ (certOf j).locs, c < 167) ∧
    (∀ c ∈ siteCells (plumbOf j), c < 167) ∧ ∀ a ∈ (plumbOf j).arms, a.2.1 < 167

theorem apart_of {j : ℕ} (h : apartOk j = true) : Apart j := by
  unfold apartOk at h
  simp only [natSeq_eq, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨ha, hb⟩, hc⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  have tc : ∀ p ∈ (plumbOf j).tmps, (tmpCells (plumbOf j)).testBit p.2 = true := fun p hp ↦
    mem_bitsOf (List.mem_map_of_mem hp)
  have rc : ∀ p ∈ (plumbOf j).runs, (bitsOf ((plumbOf j).runs.map Prod.snd)).testBit p.2 = true :=
    fun p hp ↦ mem_bitsOf (List.mem_map_of_mem hp)
  have stc : ∀ q ∈ (plumbOf j).stat, (bitsOf ((plumbOf j).stat.map Prod.fst)).testBit q.1 = true :=
    fun q hq ↦ mem_bitsOf (List.mem_map_of_mem hq)
  have scc : ∀ c ∈ siteCells (plumbOf j), (bitsOf (siteCells (plumbOf j))).testBit c = true :=
    fun c hc ↦ mem_bitsOf hc
  have acc : ∀ a ∈ (plumbOf j).arms, (bitsOf ((plumbOf j).arms.map fun a ↦ a.2.1)).testBit a.2.1 = true :=
    fun a ha ↦ mem_bitsOf (List.mem_map_of_mem (f := fun a : ℕ × ℕ × ℕ ↦ a.2.1) ha)
  refine ⟨fun q hq p hp he ↦ ?_, fun c hc ↦ ?_, fun a ha ↦ ?_, (bitsNodup_spec _ _ h4).1,
    (bitsNodup_spec _ _ h5).1, (bitsNodup_spec _ _ h6).1, fun hj ↦ ?_⟩
  · have := apart_spec ha (stc q hq)
    rw [← he, tc p hp] at this; cases this
  · have hs := apart_spec hb (scc c hc)
    simp only [testBit_lor', Bool.or_eq_false_iff] at hs
    obtain ⟨⟨⟨ht, hr⟩, hst⟩, hv⟩ := hs
    refine ⟨fun p hp he ↦ ?_, fun p hp he ↦ ?_, fun q hq he ↦ ?_, fun hl ↦ ?_⟩
    · rw [← he, tc p hp] at ht; cases ht
    · rw [← he, rc p hp] at hr; cases hr
    · rw [← he, stc q hq] at hst; cases hst
    · rw [mem_bitsOf hl] at hv; cases hv
  · have hs := apart_spec hc (acc a ha)
    simp only [testBit_lor', Bool.or_eq_false_iff] at hs
    obtain ⟨⟨⟨⟨ht, hr⟩, hst⟩, hv⟩, hsc⟩ := hs
    refine ⟨fun p hp he ↦ ?_, fun p hp he ↦ ?_, fun q hq he ↦ ?_, fun hl ↦ ?_, fun hl ↦ ?_⟩
    · rw [← he, tc p hp] at ht; cases ht
    · rw [← he, rc p hp] at hr; cases hr
    · rw [← he, stc q hq] at hst; cases hst
    · rw [mem_bitsOf hl] at hv; cases hv
    · rw [scc _ hl] at hsc; cases hsc
  · subst hj
    simp only [show Nat.beq 1 1 = true from rfl, Bool.cond_true, Nat.blt_eq] at h7
    have hlt : ∀ c, (Nat.lor (Nat.lor (Nat.lor (Nat.lor (tmpCells (plumbOf 1)) (bitsOf ((plumbOf 1).runs.map Prod.snd)))
        (bitsOf ((plumbOf 1).stat.map Prod.fst))) (bitsOf (certOf 1).locs)) (bitsOf (siteCells (plumbOf 1)))).testBit c
          = true ∨ (bitsOf ((plumbOf 1).arms.map fun a ↦ a.2.1)).testBit c = true → c < 167 := fun c hc ↦
      lt_of_testBit_lt h7 (by
        rcases hc with hc | hc
        · exact testBit_lor_l hc
        · exact testBit_lor_r hc)
    refine ⟨fun p hp ↦ hlt _ (Or.inl ?_), fun p hp ↦ hlt _ (Or.inl ?_), fun q hq ↦ hlt _ (Or.inl ?_),
      fun c hc ↦ hlt _ (Or.inl ?_), fun c hc ↦ hlt _ (Or.inl ?_), fun a ha ↦ hlt _ (Or.inr (acc a ha))⟩
    · exact testBit_lor_l (testBit_lor_l (testBit_lor_l (testBit_lor_l (tc p hp))))
    · exact testBit_lor_l (testBit_lor_l (testBit_lor_l (testBit_lor_r (rc p hp))))
    · exact testBit_lor_l (testBit_lor_l (testBit_lor_r (stc q hq)))
    · exact testBit_lor_l (testBit_lor_r (mem_bitsOf hc))
    · exact testBit_lor_r (scc c hc)

theorem apart_j {j : ℕ} (hS : ShareOk j) : Apart j := by
  obtain ⟨-, h0, -, -⟩ := shareWin_spec (hS 0 (Nat.zero_le _))
  exact apart_of (h0 rfl).2.2.2.1

end Apart

/-! ## A cell's candidates -/

section Cand

theorem dedupC_has : ∀ {L : List (ℕ × E)} {x : ℕ × E}, x ∈ L → ∃ q ∈ dedupC L, q.1 = x.1
  | [], _, h => absurd h List.not_mem_nil
  | y :: L, x, h => by
    by_cases hy : y.1 = x.1
    · exact ⟨y, by simp [dedupC], hy⟩
    · rcases List.mem_cons.mp h with rfl | h
      · exact absurd rfl hy
      · obtain ⟨q, hq, he⟩ := dedupC_has h
        refine ⟨q, ?_, he⟩
        simp only [dedupC, List.mem_cons, List.mem_filter, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq]
        exact Or.inr ⟨hq, by rw [he]; exact fun e ↦ hy e.symm⟩

/-- **A cell whose candidates all carry one word holds it.** -/
theorem frameE_cell {n : ℕ} {L : List (ℕ × E)} {c : ℕ} {w : E} (hx : ∃ x ∈ L, x.1 = c) (h2 : 2 ≤ c)
    (hn : c < n) (hall : ∀ x ∈ L, x.1 = c → x.2 = w) : (c, w) ∈ frameE n L := by
  obtain ⟨x, hx, rfl⟩ := hx
  have hx' : x ∈ L.filter fun q ↦ Nat.ble 2 q.1 && Nat.blt q.1 n := by
    simp only [List.mem_filter, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq]; exact ⟨hx, h2, hn⟩
  obtain ⟨q, hq, he⟩ := dedupC_has hx'
  have hqL := (mem_frameE (n := n) (L := L) hq).1
  have := hall q hqL he
  have : q = (x.1, w) := by rw [← he, ← this]
  rw [← this]; exact hq

theorem siteOf_mem {j : ℕ} {c : Call} {s : Site} (h : siteOf j c = some s) : s ∈ (plumbOf j).sites :=
  List.mem_of_find?_eq_some h

theorem mem_siteE {j : ℕ} {I : Inst} {es : List Ev} {x : ℕ × E} (h : x ∈ siteE j I es) :
    x.1 ∈ siteCells (plumbOf j) := by
  simp only [siteE, List.mem_flatMap] at h
  obtain ⟨p, -, hx⟩ := h
  cases hs : siteOf j p.1 with
  | none => rw [hs] at hx; cases hx
  | some s =>
    rw [hs] at hx
    simp only [siteCells, List.mem_flatMap]
    refine ⟨s, siteOf_mem hs, ?_⟩
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact List.mem_cons_self
    · split_ifs at hx with ht
      · cases hx
      · simp only [List.mem_singleton] at hx
        subst hx
        have : Nat.beq s.tgt 0 = false := Bool.eq_false_iff.mpr fun hb ↦ ht (nbeq_iff.mp hb)
        simp [this]

/-- A value's cell, from its window's check. -/
theorem valOk_global {j : ℕ} {G : Glob} {f : CompiledFn} {main : Bool} (hS : ShareOk j)
    (hchk : ∀ i ≤ (certOf j).cuts.length, checkWin G f (coreOf j) (certOf j) main i = true) {v : V}
    (hv : v ∈ (coreOf j).params ++ Stmt.usesList (coreOf j).body ++ Stmt.tmpsList (coreOf j).body) :
    v = V.n v.idx ∧ cellJ j v < fsN j ∧ bitN (fpgCells (plumbOf j)) (cellJ j v) = false ∧
      (bitN (tmpCells (plumbOf j)) (cellJ j v) = false ∨ (v.idx, cellJ j v) ∈ (plumbOf j).tmps) := by
  have hcont := cont_of hchk
  obtain ⟨-, h0, -, -⟩ := shareWin_spec (hS 0 (Nat.zero_le _))
  obtain ⟨-, -, hsn, -, hpv⟩ := h0 rfl
  have hA : ∀ i ≤ (snapsOf j).length, ∀ v c, (locW (certOf j) (winW (snapsOf j) i)).get? v.idx = some c →
      cellJ j v = c := fun i hi v c h ↦
    locW_get hcont (winW_le hsn hi) (checkWin_parts (hchk _ (winW_le hsn hi))).2 rfl (shareWin_spec (hS i hi)).1 h
  -- the window's check, at the window's cells
  have glob : ∀ (loc : Loc), (∀ v c, loc.get? v.idx = some c → cellJ j v = c) →
      valOk loc (byCell (plumbOf j).tmps) (tmpCells (plumbOf j)) (fpgCells (plumbOf j)) (fsN j) v = true →
      v = V.n v.idx ∧ cellJ j v < fsN j ∧ bitN (fpgCells (plumbOf j)) (cellJ j v) = false ∧
        (bitN (tmpCells (plumbOf j)) (cellJ j v) = false ∨ (v.idx, cellJ j v) ∈ (plumbOf j).tmps) := by
    intro loc hl h
    obtain ⟨h1, h2, h3, h4, h5⟩ := valOk_spec h
    have hc : loc.cell v = cellJ j v := (fitV_of hl (vs := [v]) (fun u hu ↦ by
      rw [List.mem_singleton.mp hu]; exact h) v List.mem_cons_self).2
    rw [hc] at h3 h4 h5
    refine ⟨h1, h3, h4, ?_⟩
    rcases h5 with h5 | h5
    · exact Or.inl h5
    · exact Or.inr (listedT_spec h5).2
  rcases List.mem_append.mp hv with hv | hv
  · rcases List.mem_append.mp hv with hv | hv
    · exact glob _ (hA 0 (Nat.zero_le _)) (hpv v hv)
    · obtain ⟨i, hi, hw⟩ := mem_windows Stmt.usesList usesList_append hS _ 0 (Nat.zero_add _)
        (by rw [fromW_zero]; exact hv)
      obtain ⟨-, -, hval, -⟩ := shareWin_spec (hS i hi)
      exact glob _ (hA i hi) (hval v (List.mem_append_left _ hw))
  · obtain ⟨i, hi, hw⟩ := mem_windows Stmt.tmpsList tmpsList_append hS _ 0 (Nat.zero_add _)
      (by rw [fromW_zero]; exact hv)
    obtain ⟨-, -, hval, -⟩ := shareWin_spec (hS i hi)
    exact glob _ (hA i hi) (hval v (List.mem_append_right _ hw))

end Cand

/-! ## A value's cell -/

section Val

theorem cellJ_mem {j : ℕ} {v : V} (h : 2 ≤ cellJ j v) : cellJ j v ∈ (certOf j).locs := by
  unfold cellJ at h ⊢
  by_cases hv : v.idx < (certOf j).locs.length
  · rw [List.getD_eq_getElem _ _ hv]; exact List.getElem_mem hv
  · rw [List.getD_eq_default _ _ (by omega)] at h; omega

/-- A node instance's path: its events and returned values. -/
theorem node_path {I : Inst} {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} {j : ℕ}
    (ht : I.t = .node f σ bufs kids) (hj : idxOf f = some j) {es : List Ev} {vs : List V}
    (hw : walk σ (coreOf j).body = .ret es vs) :
    I.t.events coreProgram = es ∧ pathRets I.t = vs := by
  obtain ⟨i, rfl, hi, -, hf, hc, -⟩ := fn_of_idx hj
  rw [hc] at hw
  refine ⟨by rw [ht]; exact events_node hf hw, ?_⟩
  unfold pathRets
  rw [ht]
  simp only [Tree.name, Tree.val, hf, hw]

/-- The values a path names are its function's. -/
theorem namedOf_sub {j : ℕ} {σ : Val} {es : List Ev} {vs : List V} (hw : walk σ (coreOf j).body = .ret es vs)
    {v : V} (hv : v ∈ namedOf (coreOf j).params es vs) :
    v ∈ (coreOf j).params ++ Stmt.usesList (coreOf j).body ++ Stmt.tmpsList (coreOf j).body := by
  have hwi := walk_within (σ := σ) (coreOf j).body
  rw [hw] at hwi
  obtain ⟨h1, -, h3⟩ := hwi
  simp only [namedOf, List.mem_append, List.mem_flatMap] at hv ⊢
  rcases hv with (hv | ⟨e, he, hv⟩) | hv
  · exact Or.inl (Or.inl hv)
  · exact Or.inl (Or.inr (h1 e he v hv))
  · exact Or.inl (Or.inr (h3 v hv))

variable {j : ℕ} {G : Glob} {fc : CompiledFn} {main : Bool}

/-- **Every candidate at a value's cell carries its word.** -/
theorem cand_val (hS : ShareOk j)
    (hchk : ∀ i ≤ (certOf j).cuts.length, checkWin G fc (coreOf j) (certOf j) main i = true)
    {I : Inst} {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree}
    (ht : I.t = .node f σ bufs kids) (hj : idxOf f = some j) {es : List Ev} {vs : List V}
    (hw : walk σ (coreOf j).body = .ret es vs) {Ψ : ℕ → E}
    (hΨ : ∀ u ∈ namedOf (coreOf j).params es vs, 2 ≤ cellJ j u → σ u = Ψ (cellJ j u))
    (hst : ∀ o a b c, (o, PC.k a b c) ∈ (plumbOf j).stat → Ψ o = OInstr.imm a b c)
    {v : V} (hv : v ∈ namedOf (coreOf j).params es vs) (h2 : 2 ≤ cellJ j v)
    {x : ℕ × E} (hx : x ∈ nodeE j f σ I) (hxc : x.1 = cellJ j v) : x.2 = σ v := by
  obtain ⟨i, rfl, -, -, -, hc, -, hcert, -⟩ := fn_of_idx hj
  have hcJ : ∀ u, cert f u = cellJ (i + 1) u := fun u ↦ hcert u
  have FS := fnStatic hS hchk
  have AP := apart_j hS
  obtain ⟨hev, hvs⟩ := node_path ht hj hw
  obtain ⟨-, -, hfc, htc⟩ := valOk_global hS hchk (namedOf_sub hw hv)
  have hvΨ := hΨ v hv h2
  simp only [nodeE, List.mem_append, hev, hvs] at hx
  rcases hx with (((((hx | hx) | hx) | hx) | hx) | hx) | hx
  · -- a temporary's
    simp only [valE, List.mem_map] at hx
    obtain ⟨t, htm, rfl⟩ := hx
    obtain ⟨j', hj', htl⟩ := temps_of htm
    rw [hj] at hj'; cases hj'
    obtain ⟨ht1, ht2⟩ := FS.tmp t htl
    simp only [hcJ] at hxc
    rw [hxc] at ht2
    have hin : (tmpCells (plumbOf (i + 1))).testBit (cellJ (i + 1) v) = true :=
      mem_bitsOf (List.mem_map_of_mem (f := Prod.snd) ht2)
    rw [bitN_eq] at htc
    rcases htc with htc | htc
    · rw [hin] at htc; cases htc
    · have := FS.tmpsFun _ htc _ ht2 rfl
      simp only at this
      show σ t = σ v
      rw [ht1, ← this, ← (valOk_global hS hchk (namedOf_sub hw hv)).1]
  · -- a frame run's
    obtain ⟨p, r, rs, he, k, hk, rfl⟩ := mem_runsE hx
    have ha : Atom.frameAddr p (r :: rs) ∈ lAtoms (coreOf (i + 1)).body :=
      walk_atoms _ (by rw [hw]; exact he)
    obtain ⟨-, hrc, -⟩ := FS.run p r rs ha k hk
    simp only [hcJ] at hxc
    have hu : (r :: rs)[k] ∈ namedOf (coreOf (i + 1)).params es vs := by
      simp only [namedOf, List.mem_append, List.mem_flatMap]
      exact Or.inl (Or.inr ⟨_, he, by simp only [Ev.uses, atomUses]; exact List.mem_cons_of_mem _ (List.getElem_mem hk)⟩)
    have hcu : cellJ (i + 1) (r :: rs)[k] = cellJ (i + 1) v := by rw [hrc, hxc]
    show σ (r :: rs)[k] = σ v
    rw [hΨ _ hu (by rw [hcu]; exact h2), hcu, hvΨ]
  · -- a fixed cell's
    simp only [List.mem_map] at hx
    obtain ⟨q, hq, rfl⟩ := hx
    simp only at hxc ⊢
    rcases q with ⟨o, ⟨a, b, c⟩ | e⟩
    · simp only at hxc
      subst hxc
      rw [hvΨ, hst _ a b c hq]; rfl
    · simp only at hxc
      have : (fpgCells (plumbOf (i + 1))).testBit o = true :=
        mem_bitsOf (List.mem_filterMap.mpr ⟨_, hq, rfl⟩)
      rw [bitN_eq, ← hxc, this] at hfc; cases hfc
  · -- a named value's
    simp only [valE, List.mem_map] at hx
    obtain ⟨u, hu, rfl⟩ := hx
    simp only [hcJ] at hxc ⊢
    rw [hΨ u hu (by rw [hxc]; exact h2), hxc, hvΨ]
  · exact absurd (cellJ_mem h2) (hxc ▸ (AP.site _ (mem_siteE hx)).2.2.2)
  · simp only [List.mem_map] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    exact absurd (cellJ_mem h2) (hxc ▸ (AP.arm a ha).2.2.2.1)
  · split_ifs at hx with h1
    · have hlt := (AP.main h1).2.2.2.1 _ (cellJ_mem h2)
      have hge : 167 ≤ x.1 := by
        have : x.1 ∈ tableCells.map Prod.fst := List.mem_map_of_mem hx
        rw [tableCells_offsets, List.mem_range'] at this
        omega
      omega
    · cases hx

/-- **The honest memory reads each named value at its cell.** -/
theorem read_val {hdr : E × E} {T : Tree} {rd : Reader} {args rets : List E}
    (h : Honest coreProgram fs H C hdr T rd args rets) (hS : ShareOk j)
    (hchk : ∀ i ≤ (certOf j).cuts.length, checkWin G fc (coreOf j) (certOf j) main i = true)
    {I : Inst} (hI : I ∈ honestInsts coreProgram fs H hdr T) {f : String} {σ : Val} {bufs : List ℕ}
    {kids : List Tree} (ht : I.t = .node f σ bufs kids) (hj : idxOf f = some j) {es : List Ev} {vs : List V}
    (hw : walk σ (coreOf j).body = .ret es vs) (he : ∀ e ∈ es, e.Holds rd σ)
    {v : V} (hv : v ∈ namedOf (coreOf j).params es vs) (h2 : 2 ≤ cellJ j v) (hn : cellJ j v < fsN j) :
    (honest coreProgram fs H C hdr T).read (gpow (I.fp + cellJ j v)) = some (σ v) := by
  obtain ⟨Ψ, hΨ, hst⟩ := shareOk_path hS hchk hw he
  obtain ⟨i, rfl, -, -, -, -, hfs, hcert, -⟩ := fn_of_idx hj
  have hmem : (cellJ (i + 1) v, σ v) ∈ C I := by
    rw [C_node ht hj, hfs]
    refine frameE_cell ⟨(cert f v, σ v), ?_, hcert v⟩ h2 hn fun x hx hxc ↦
      cand_val hS hchk ht hj hw (Ψ := Ψ) (fun u hu hc ↦ hΨ u (by simpa [namedOf, List.append_assoc] using hu) hc)
        hst hv h2 hx hxc
    obtain ⟨hev, hvs⟩ := node_path ht hj hw
    simp only [nodeE, List.mem_append, valE, List.mem_map, hev, hvs]
    exact Or.inl (Or.inl (Or.inl (Or.inr ⟨v, hv, rfl⟩)))
  rw [gpow, pow_add]
  exact h.read_C hI hmem

end Val

end
end LeanVM.Guest.B2C
