/-
  LeanVM.Guest.B2C.Frame

  What the honest memory holds of an instance's frame: every value its path names at its cell,
  the fixed cells' words, from the sharing check.
-/

module

public import LeanVM.Guest.B2C.Static
public import LeanVM.Guest.Value.Tower

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
  env : ∀ p ∈ (certOf j).facts.env, (p.1, PC.fpg 0) ∈ (plumbOf j).stat
  main : j = 1 → (∀ p ∈ (plumbOf j).tmps, p.2 < 167) ∧ (∀ p ∈ (plumbOf j).runs, p.2 < 167) ∧
    (∀ q ∈ (plumbOf j).stat, q.1 < 167) ∧ (∀ c ∈ (certOf j).locs, c < 167) ∧
    (∀ c ∈ siteCells (plumbOf j), c < 167) ∧ ∀ a ∈ (plumbOf j).arms, a.2.1 < 167

theorem apart_of {j : ℕ} (h : apartOk j = true) : Apart j := by
  unfold apartOk at h
  simp only [natSeq_eq, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨ha, hb⟩, hc⟩, h4⟩, h5⟩, h6⟩, h8⟩, h7⟩ := h
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
    (bitsNodup_spec _ _ h5).1, (bitsNodup_spec _ _ h6).1, fun p hp ↦ ?_, fun hj ↦ ?_⟩
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
  · simp only [List.all_eq_true, List.any_eq_true, Bool.and_eq_true, nbeq_iff, beq_iff_eq] at h8
    obtain ⟨q, hq, h1, h2⟩ := h8 p hp
    rw [← h1, ← h2]; exact hq
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
  exact apart_of (shareStatic_spec hS.1).2.2.2.1

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
  obtain ⟨-, -, hsn, -, hpv⟩ := shareStatic_spec hS.1
  have hA : ∀ i ≤ (snapsOf j).length, ∀ v c, (locW (certOf j) (winW (snapsOf j) i)).get? v.idx = some c →
      cellJ j v = c := fun i hi v c h ↦
    locW_get hcont (winW_le hsn hi) (checkWin_parts (hchk _ (winW_le hsn hi))).2 rfl (shareWin_spec (hS.2 i hi)).1 h
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
      obtain ⟨-, hval, -⟩ := shareWin_spec (hS.2 i hi)
      exact glob _ (hA i hi) (hval v (List.mem_append_left _ hw))
  · obtain ⟨i, hi, hw⟩ := mem_windows Stmt.tmpsList tmpsList_append hS _ 0 (Nat.zero_add _)
      (by rw [fromW_zero]; exact hv)
    obtain ⟨-, hval, -⟩ := shareWin_spec (hS.2 i hi)
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

/-! ## The fixed cells, the temporaries, the table targets -/

section Others

variable {j : ℕ} {G : Glob} {fc : CompiledFn} {main : Bool}

/-- The run value at a fixed cell is a named value of the path at it. -/
theorem run_named {f : String} {σ : Val} (hj : idxOf f = some j) {es : List Ev} {vs : List V}
    (hw : walk σ (coreOf j).body = .ret es vs) (FS : FnStatic j) {x : ℕ × E} (hx : x ∈ runsE f σ es) :
    ∃ u ∈ namedOf (coreOf j).params es vs, cellJ j u = x.1 ∧ x.2 = σ u := by
  obtain ⟨i, rfl, -, -, -, -, -, hcert, -⟩ := fn_of_idx hj
  obtain ⟨p, r, rs, he, k, hk, rfl⟩ := mem_runsE hx
  have ha : Atom.frameAddr p (r :: rs) ∈ lAtoms (coreOf (i + 1)).body := walk_atoms _ (by rw [hw]; exact he)
  obtain ⟨-, hrc, -⟩ := FS.run p r rs ha k hk
  refine ⟨(r :: rs)[k], ?_, by rw [hrc, hcert]; rfl, rfl⟩
  simp only [namedOf, List.mem_append, List.mem_flatMap]
  exact Or.inl (Or.inr ⟨_, he, by simp only [Ev.uses, atomUses]; exact List.mem_cons_of_mem _ (List.getElem_mem hk)⟩)

theorem cellJ_tmp_listed {u : V} {c : ℕ} (htc : bitN (tmpCells (plumbOf j)) c = false ∨
    (u.idx, c) ∈ (plumbOf j).tmps) {t : V} (hl : (t.idx, c) ∈ (plumbOf j).tmps) : (u.idx, c) ∈ (plumbOf j).tmps := by
  rcases htc with htc | htc
  · have := mem_bitsOf (List.mem_map_of_mem (f := Prod.snd) hl)
    simp only at this
    unfold tmpCells at htc
    rw [bitN_eq, this] at htc; cases htc
  · exact htc

/-- **The honest memory reads each fixed cell's word.** -/
theorem read_stat {hdr : E × E} {T : Tree} {rd : Reader} {args rets : List E}
    (h : Honest coreProgram fs H C hdr T rd args rets) (hS : ShareOk j)
    (hchk : ∀ i ≤ (certOf j).cuts.length, checkWin G fc (coreOf j) (certOf j) main i = true)
    {I : Inst} (hI : I ∈ honestInsts coreProgram fs H hdr T) {f : String} {σ : Val} {bufs : List ℕ}
    {kids : List Tree} (ht : I.t = .node f σ bufs kids) (hj : idxOf f = some j) {es : List Ev} {vs : List V}
    (hw : walk σ (coreOf j).body = .ret es vs) (he : ∀ e ∈ es, e.Holds rd σ)
    {q : ℕ × PC} (hq : q ∈ (plumbOf j).stat) (h2 : 2 ≤ q.1) (hn : q.1 < fsN j) :
    (honest coreProgram fs H C hdr T).read (gpow (I.fp + q.1)) = some (q.2.word I.fp) := by
  obtain ⟨Ψ, hΨ, hst⟩ := shareOk_path hS hchk hw he
  have hΨ' : ∀ u ∈ namedOf (coreOf j).params es vs, 2 ≤ cellJ j u → σ u = Ψ (cellJ j u) :=
    fun u hu hc ↦ hΨ u (by simpa [namedOf, List.append_assoc] using hu) hc
  have FS := fnStatic hS hchk
  have AP := apart_j hS
  obtain ⟨i, rfl, -, -, -, -, hfs, hcert, -⟩ := fn_of_idx hj
  have hcJ : ∀ u, cert f u = cellJ (i + 1) u := fun u ↦ hcert u
  obtain ⟨hev, hvs⟩ := node_path ht hj hw
  -- a value at the cell: the cell holds a constant, the value's word
  have hval : ∀ u ∈ namedOf (coreOf (i + 1)).params es vs, cellJ (i + 1) u = q.1 → σ u = q.2.word I.fp := by
    intro u hu hcu
    obtain ⟨-, -, hfc, -⟩ := valOk_global hS hchk (namedOf_sub hw hu)
    rcases q with ⟨o, ⟨a, b, c⟩ | e⟩
    · simp only at hcu ⊢
      rw [hΨ' u hu (by rw [hcu]; exact h2), hcu, hst o a b c hq]; rfl
    · simp only at hcu
      have : (fpgCells (plumbOf (i + 1))).testBit o = true := mem_bitsOf (List.mem_filterMap.mpr ⟨_, hq, rfl⟩)
      rw [bitN_eq, hcu, this] at hfc; cases hfc
  have hmem : (q.1, q.2.word I.fp) ∈ C I := by
    rw [C_node ht hj, hfs]
    refine frameE_cell ⟨(q.1, q.2.word I.fp), ?_, rfl⟩ h2 hn fun x hx hxc ↦ ?_
    · simp only [nodeE, List.mem_append, List.mem_map]
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨q, hq, rfl⟩))))
    simp only [nodeE, List.mem_append, hev, hvs] at hx
    rcases hx with (((((hx | hx) | hx) | hx) | hx) | hx) | hx
    · simp only [valE, List.mem_map] at hx
      obtain ⟨t, htm, rfl⟩ := hx
      obtain ⟨j', hj', htl⟩ := temps_of htm
      rw [hj] at hj'; cases hj'
      have := (FS.tmp t htl).2
      exact absurd (by rw [← hcJ]; exact hxc) (AP.statTmp q hq _ this)
    · obtain ⟨u, hu, hcu, hx2⟩ := run_named hj hw FS hx
      rw [hx2]; exact hval u hu (hcu.trans hxc)
    · simp only [List.mem_map] at hx
      obtain ⟨q', hq', rfl⟩ := hx
      simp only at hxc ⊢
      rw [List.inj_on_of_nodup_map AP.statNodup hq' hq hxc]
    · simp only [valE, List.mem_map] at hx
      obtain ⟨u, hu, rfl⟩ := hx
      simp only [hcJ] at hxc ⊢
      exact hval u hu hxc
    · exact absurd hxc ((AP.site _ (mem_siteE hx)).2.2.1 q hq).symm
    · simp only [List.mem_map] at hx
      obtain ⟨a, ha, rfl⟩ := hx
      exact absurd hxc ((AP.arm a ha).2.2.1 q hq).symm
    · split_ifs at hx with h1
      · have hlt := (AP.main h1).2.2.1 q hq
        have : x.1 ∈ tableCells.map Prod.fst := List.mem_map_of_mem hx
        rw [tableCells_offsets, List.mem_range'] at this
        omega
      · cases hx
  rw [gpow, pow_add]
  exact h.read_C hI hmem

/-- **The honest memory reads each temporary of the path at its cell.** -/
theorem read_tmp {hdr : E × E} {T : Tree} {rd : Reader} {args rets : List E}
    (h : Honest coreProgram fs H C hdr T rd args rets) (hS : ShareOk j)
    (hchk : ∀ i ≤ (certOf j).cuts.length, checkWin G fc (coreOf j) (certOf j) main i = true)
    {I : Inst} (hI : I ∈ honestInsts coreProgram fs H hdr T) {f : String} {σ : Val} {bufs : List ℕ}
    {kids : List Tree} (ht : I.t = .node f σ bufs kids) (hj : idxOf f = some j) {es : List Ev} {vs : List V}
    (hw : walk σ (coreOf j).body = .ret es vs) {t : V} (htm : t ∈ coreProgram.temps f)
    (h2 : 2 ≤ cellJ j t) (hn : cellJ j t < fsN j) :
    (honest coreProgram fs H C hdr T).read (gpow (I.fp + cellJ j t)) = some (σ t) := by
  have FS := fnStatic hS hchk
  have AP := apart_j hS
  obtain ⟨i, rfl, -, -, -, -, hfs, hcert, -⟩ := fn_of_idx hj
  have hcJ : ∀ u, cert f u = cellJ (i + 1) u := fun u ↦ hcert u
  obtain ⟨hev, hvs⟩ := node_path ht hj hw
  obtain ⟨j', hj', htl⟩ := temps_of htm
  rw [hj] at hj'; cases hj'
  obtain ⟨ht1, ht2⟩ := FS.tmp t htl
  -- a value at a temporary's cell is that temporary
  have same : ∀ u : V, u = V.n u.idx → (u.idx, cellJ (i + 1) t) ∈ (plumbOf (i + 1)).tmps → u = t := by
    intro u hu hl
    have := FS.tmpsFun _ hl _ ht2 rfl
    simp only at this
    rw [hu, ht1, this]
  have hmem : (cellJ (i + 1) t, σ t) ∈ C I := by
    rw [C_node ht hj, hfs]
    refine frameE_cell ⟨(cert f t, σ t), ?_, hcert t⟩ h2 hn fun x hx hxc ↦ ?_
    · simp only [nodeE, List.mem_append, valE, List.mem_map]
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨t, htm, rfl⟩)))))
    simp only [nodeE, List.mem_append, hev, hvs] at hx
    rcases hx with (((((hx | hx) | hx) | hx) | hx) | hx) | hx
    · simp only [valE, List.mem_map] at hx
      obtain ⟨t', htm', rfl⟩ := hx
      obtain ⟨j', hj', htl'⟩ := temps_of htm'
      rw [hj] at hj'; cases hj'
      obtain ⟨ht1', ht2'⟩ := FS.tmp t' htl'
      simp only [hcJ] at hxc ⊢
      rw [same t' ht1' (hxc ▸ ht2')]
    · obtain ⟨p, r, rs, he', k, hk, rfl⟩ := mem_runsE hx
      have ha : Atom.frameAddr p (r :: rs) ∈ lAtoms (coreOf (i + 1)).body := walk_atoms _ (by rw [hw]; exact he')
      obtain ⟨-, -, hrun⟩ := FS.run p r rs ha k hk
      exact absurd (by simp only [hcJ] at hxc; exact hxc) (FS.runsTmp _ hrun _ ht2).symm
    · simp only [List.mem_map] at hx
      obtain ⟨q, hq, rfl⟩ := hx
      exact absurd hxc.symm (AP.statTmp q hq _ ht2)
    · simp only [valE, List.mem_map] at hx
      obtain ⟨u, hu, rfl⟩ := hx
      simp only [hcJ] at hxc ⊢
      obtain ⟨hu1, -, -, htc⟩ := valOk_global hS hchk (namedOf_sub hw hu)
      rw [hxc] at htc
      rw [same u hu1 (cellJ_tmp_listed htc ht2)]
    · exact absurd (hxc ▸ rfl) ((AP.site _ (mem_siteE hx)).1 _ ht2)
    · simp only [List.mem_map] at hx
      obtain ⟨a, ha, rfl⟩ := hx
      exact absurd hxc.symm ((AP.arm a ha).1 _ ht2)
    · split_ifs at hx with h1
      · have hlt := (AP.main h1).1 _ ht2
        have : x.1 ∈ tableCells.map Prod.fst := List.mem_map_of_mem hx
        rw [tableCells_offsets, List.mem_range'] at this
        simp only at hlt
        omega
      · cases hx
  rw [gpow, pow_add]
  exact h.read_C hI hmem

/-- **The honest memory reads each table jump's target.** -/
theorem read_arm {hdr : E × E} {T : Tree} {rd : Reader} {args rets : List E}
    (h : Honest coreProgram fs H C hdr T rd args rets) (hS : ShareOk j)
    (hchk : ∀ i ≤ (certOf j).cuts.length, checkWin G fc (coreOf j) (certOf j) main i = true)
    {I : Inst} (hI : I ∈ honestInsts coreProgram fs H hdr T) {f : String} {σ : Val} {bufs : List ℕ}
    {kids : List Tree} (ht : I.t = .node f σ bufs kids) (hj : idxOf f = some j) {es : List Ev} {vs : List V}
    (hw : walk σ (coreOf j).body = .ret es vs)
    {a : ℕ × ℕ × ℕ} (ha : a ∈ (plumbOf j).arms) (h2 : 2 ≤ a.2.1) (hn : a.2.1 < fsN j) :
    (honest coreProgram fs H C hdr T).read (gpow (I.fp + a.2.1)) = some (armWord σ a.1 a.2.2) := by
  have FS := fnStatic hS hchk
  have AP := apart_j hS
  obtain ⟨i, rfl, -, -, -, -, hfs, hcert, -⟩ := fn_of_idx hj
  have hcJ : ∀ u, cert f u = cellJ (i + 1) u := fun u ↦ hcert u
  obtain ⟨hev, hvs⟩ := node_path ht hj hw
  obtain ⟨hat, har, has, hal, hsc⟩ := AP.arm a ha
  have hmem : (a.2.1, armWord σ a.1 a.2.2) ∈ C I := by
    rw [C_node ht hj, hfs]
    refine frameE_cell ⟨(a.2.1, armWord σ a.1 a.2.2), ?_, rfl⟩ h2 hn fun x hx hxc ↦ ?_
    · simp only [nodeE, List.mem_append, List.mem_map]
      exact Or.inl (Or.inr ⟨a, ha, rfl⟩)
    simp only [nodeE, List.mem_append, hev, hvs] at hx
    rcases hx with (((((hx | hx) | hx) | hx) | hx) | hx) | hx
    · simp only [valE, List.mem_map] at hx
      obtain ⟨t, htm, rfl⟩ := hx
      obtain ⟨j', hj', htl⟩ := temps_of htm
      rw [hj] at hj'; cases hj'
      exact absurd (by simp only [hcJ] at hxc; exact hxc) (hat _ (FS.tmp t htl).2)
    · obtain ⟨u, hu, hcu, -⟩ := run_named hj hw FS hx
      obtain ⟨p, r, rs, he', k, hk, rfl⟩ := mem_runsE hx
      have ha' : Atom.frameAddr p (r :: rs) ∈ lAtoms (coreOf (i + 1)).body := walk_atoms _ (by rw [hw]; exact he')
      obtain ⟨-, -, hrun⟩ := FS.run p r rs ha' k hk
      exact absurd (by simp only [hcJ] at hxc; exact hxc) (har _ hrun)
    · simp only [List.mem_map] at hx
      obtain ⟨q, hq, rfl⟩ := hx
      exact absurd hxc (has q hq)
    · simp only [valE, List.mem_map] at hx
      obtain ⟨u, hu, rfl⟩ := hx
      simp only [hcJ] at hxc
      exact absurd (hxc ▸ cellJ_mem (hxc ▸ h2)) hal
    · exact absurd (hxc ▸ mem_siteE hx) hsc
    · simp only [List.mem_map] at hx
      obtain ⟨a', ha', rfl⟩ := hx
      simp only at hxc ⊢
      rw [List.inj_on_of_nodup_map (f := fun a : ℕ × ℕ × ℕ ↦ a.2.1) AP.armNodup ha' ha hxc]
    · split_ifs at hx with h1
      · have hlt := (AP.main h1).2.2.2.2.2 a ha
        have : x.1 ∈ tableCells.map Prod.fst := List.mem_map_of_mem hx
        rw [tableCells_offsets, List.mem_range'] at this
        omega
      · cases hx
  rw [gpow, pow_add]
  exact h.read_C hI hmem

end Others

/-! ## A callee's arguments -/

section Args

/-- The first window's check places the parameters at cells `2, 3, …`. -/
theorem checkWin_params {G : Glob} {f : CompiledFn} {cf : Core.Fn} {C : Check.Cert} {main : Bool}
    (hc : checkWin G f cf C main 0 = true) (hcont : Cont C C.cuts.length) :
    ∀ m (hm : m < cf.params.length), C.locs.getD cf.params[m].idx 0 = 2 + m := by
  have hins := (checkWin_parts hc).2
  unfold checkWin at hc
  rcases hR : execWin C.facts f (C.cutAt 0).J (C.cutAt 0).env (C.endAt f 0) with ⟨segs, dead⟩
  rw [hR] at hc
  simp only [listSeq_eq, Trie.seq_eq, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, h0⟩, -⟩ := hc
  simp only [beq_self_eq_true, Bool.cond_true, Bool.and_eq_true] at h0
  intro m hm
  have := runAt_sound h0.1 m hm
  unfold cellOf at this
  rcases hg : getF (C.locAt 0) cf.params[m].idx with _ | c
  · rw [hg, Option.getD_none] at this; omega
  · rw [hg, Option.getD_some] at this
    rw [locAt_val hcont (Nat.zero_le _) hins rfl hg, this]

variable {j : ℕ} {G : Glob} {fc : CompiledFn} {main : Bool}

/-- **A callee's frame holds its arguments** at cells `2 + k`, whether it runs or not. -/
theorem read_args {hdr : E × E} {T : Tree} {rd : Reader} {args rets : List E}
    (h : Honest coreProgram fs H C hdr T rd args rets) (hS : ShareOk j)
    (hchk : ∀ i ≤ (certOf j).cuts.length, checkWin G fc (coreOf j) (certOf j) main i = true)
    {J : Inst} (hJ : J ∈ honestInsts coreProgram fs H hdr T) {g : String} (hj : idxOf g = some j)
    (hgood : (∃ σ bufs kids es vs, J.t = .node g σ bufs kids ∧
      walk σ (coreOf j).body = .ret es vs ∧ ∀ e ∈ es, e.Holds rd σ) ∨ ∃ σ, J.t = .phantom g σ)
    (k : ℕ) (hk : k < (coreOf j).params.length) :
    (honest coreProgram fs H C hdr T).read (gpow (J.fp + (2 + k))) = some (J.t.val (coreOf j).params[k]) := by
  have hcont := cont_of hchk
  have hpc := checkWin_params (hchk 0 (Nat.zero_le _)) hcont k hk
  have hpk : (coreOf j).params[k] ∈ (coreOf j).params ++ Stmt.usesList (coreOf j).body ++
      Stmt.tmpsList (coreOf j).body := List.mem_append_left _ (List.mem_append_left _ (List.getElem_mem hk))
  obtain ⟨hvn, hlt, hfc, -⟩ := valOk_global hS hchk hpk
  rw [show cellJ j (coreOf j).params[k] = 2 + k from hpc] at hlt hfc
  rcases hgood with ⟨σ, bufs, kids, es, vs, ht, hw, he⟩ | ⟨σ, ht⟩
  · have := read_val h hS hchk hJ ht hj hw he (v := (coreOf j).params[k])
      (by simp only [namedOf, List.mem_append]; exact Or.inl (Or.inl (List.getElem_mem hk)))
      (by rw [show cellJ j (coreOf j).params[k] = 2 + k from hpc]; omega)
      (by rw [show cellJ j (coreOf j).params[k] = 2 + k from hpc]; exact hlt)
    rw [show cellJ j (coreOf j).params[k] = 2 + k from hpc] at this
    rw [ht]; exact this
  · obtain ⟨i, rfl, -, -, -, -, hfs, hcert, -⟩ := fn_of_idx hj
    have AP := apart_j hS
    have hmem : (2 + k, σ (coreOf (i + 1)).params[k]) ∈ C J := by
      rw [C_phantom ht hj, hfs]
      refine frameE_cell ⟨(cert g (coreOf (i + 1)).params[k], σ (coreOf (i + 1)).params[k]), ?_, ?_⟩
        (by omega) hlt fun x hx hxc ↦ ?_
      · simp only [phantomE, List.mem_append, valE, List.mem_map]
        exact Or.inl ⟨_, List.getElem_mem hk, rfl⟩
      · rw [hcert]; exact hpc
      simp only [phantomE, List.mem_append, valE, List.mem_map] at hx
      rcases hx with ⟨u, hu, rfl⟩ | ⟨p, hp, rfl⟩
      · obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.mp hu
        simp only at hxc ⊢
        rw [hcert, checkWin_params (hchk 0 (Nat.zero_le _)) hcont m hm] at hxc
        obtain rfl : m = k := by omega
        rfl
      · simp only at hxc
        have hst := AP.env p hp
        have : (fpgCells (plumbOf (i + 1))).testBit p.1 = true := mem_bitsOf (List.mem_filterMap.mpr ⟨_, hst, rfl⟩)
        rw [bitN_eq, ← hxc, this] at hfc; cases hfc
    rw [gpow, pow_add, ht]
    exact h.read_C hJ hmem

/-- The fixed cells lie in the frame. -/
theorem stat_in (hS : ShareOk j) {q : ℕ × PC} (hq : q ∈ (plumbOf j).stat) : 2 ≤ q.1 ∧ q.1 < fsN j := by
  obtain ⟨-, hlists, -, -, -⟩ := shareStatic_spec hS.1
  simp only [listsOk, Exec.Trie.seq_eq, natSeq_eq, Bool.and_eq_true, List.all_eq_true] at hlists
  have := (hlists.1.1.1.1.1 q hq).1
  simp only [Nat.ble_eq, Nat.blt_eq] at this
  exact this

/-- **A callee's frame holds its frame pointer** in its entry environment's cells, whether it runs
or not. -/
theorem read_self {hdr : E × E} {T : Tree} {rd : Reader} {args rets : List E}
    (h : Honest coreProgram fs H C hdr T rd args rets) (hS : ShareOk j)
    (hchk : ∀ i ≤ (certOf j).cuts.length, checkWin G fc (coreOf j) (certOf j) main i = true)
    {J : Inst} (hJ : J ∈ honestInsts coreProgram fs H hdr T) {g : String} (hj : idxOf g = some j)
    (hgood : (∃ σ bufs kids es vs, J.t = .node g σ bufs kids ∧
      walk σ (coreOf j).body = .ret es vs ∧ ∀ e ∈ es, e.Holds rd σ) ∨ ∃ σ, J.t = .phantom g σ)
    {o : ℕ} (ho : o ∈ (certOf j).facts.env.map Prod.fst) :
    (honest coreProgram fs H C hdr T).read (gpow (J.fp + o)) = some (ofK (gpow J.fp)) := by
  have AP := apart_j hS
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ho
  have hst := AP.env p hp
  obtain ⟨h2, hn⟩ := stat_in hS hst
  rcases hgood with ⟨σ, bufs, kids, es, vs, ht, hw, he⟩ | ⟨σ, ht⟩
  · have := read_stat h hS hchk hJ ht hj hw he hst h2 hn
    simpa [PC.word] using this
  · obtain ⟨i, rfl, -, -, -, -, hfs, hcert, -⟩ := fn_of_idx hj
    have hmem : (p.1, ofK (gpow J.fp)) ∈ C J := by
      rw [C_phantom ht hj, hfs]
      refine frameE_cell ⟨(p.1, ofK (gpow J.fp)), ?_, rfl⟩ h2 hn fun x hx hxc ↦ ?_
      · simp only [phantomE, List.mem_append, List.mem_map]
        exact Or.inr ⟨p, hp, rfl⟩
      simp only [phantomE, List.mem_append, valE, List.mem_map] at hx
      rcases hx with ⟨u, hu, rfl⟩ | ⟨p', -, rfl⟩
      · simp only [hcert] at hxc
        obtain ⟨-, -, hfc, -⟩ := valOk_global hS hchk (v := u)
          (List.mem_append_left _ (List.mem_append_left _ hu))
        have : (fpgCells (plumbOf (i + 1))).testBit p.1 = true := mem_bitsOf (List.mem_filterMap.mpr ⟨_, hst, rfl⟩)
        rw [bitN_eq, show cellJ (i + 1) u = p.1 from hxc, this] at hfc; cases hfc
      · rfl
    rw [gpow, pow_add]
    exact h.read_C hJ hmem

end Args

/-! ## The frame's placement -/

section Place

variable {j : ℕ}

theorem kidsValid_length {rd : Reader} {σ : Val} : ∀ {cs : List Call} {ks : List Tree},
    Tree.KidsValid coreProgram rd σ cs ks → ks.length = cs.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by
    simp only [List.length_cons, kidsValid_length h.2.2]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

/-- A node instance valid on a reader, along its function's path. -/
theorem node_valid {rd : Reader} {I : Inst} {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree}
    (ht : I.t = .node f σ bufs kids) (hj : idxOf f = some j) (hg : I.Good coreProgram rd) :
    ∃ es vs, walk σ (coreOf j).body = .ret es vs ∧ (∀ e ∈ es, e.Holds rd σ) ∧
      Tree.KidsValid coreProgram rd σ (calls es) kids := by
  obtain ⟨i, rfl, hi, -, hf, hc, -⟩ := fn_of_idx hj
  rcases hg with ⟨args, rets, hv⟩ | ⟨f', σ', hp⟩
  · rw [ht] at hv
    obtain ⟨fn, hfn, -, es, vs, hw, -, he, hk⟩ := hv
    rw [hf] at hfn; cases hfn
    exact ⟨es, vs, by rw [hc]; exact hw, he, hk⟩
  · rw [ht] at hp; cases hp

/-- **One callee frame per call.** -/
theorem frame_len {hdr : E × E} {T : Tree} {I : Inst} (hI : I ∈ honestInsts coreProgram fs H hdr T)
    {rd : Reader} {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node f σ bufs kids)
    {es : List Ev} (hk : Tree.KidsValid coreProgram rd σ (calls es) kids) :
    I.kidFps.length = (calls es).length := by
  rw [honest_kidFps hI, length_kidPos, List.length_map, ht]
  exact kidsValid_length hk

/-- **The frame addresses** are the runs' addresses in the frame. -/
theorem frame_addr {hdr : E × E} {T : Tree} {rd : Reader} {args rets : List E}
    (h : HonestAt coreProgram fs H C hdr T cert rd args rets) {I : Inst}
    (hI : I ∈ honestInsts coreProgram fs H hdr T) {f : String} {σ : Val} {bufs : List ℕ}
    {kids : List Tree} (ht : I.t = .node f σ bufs kids) (hj : idxOf f = some j) {es : List Ev} {vs : List V}
    (hw : walk σ (coreOf j).body = .ret es vs) :
    ∀ q ∈ addrs es, σ q.1 = ofK (gpow (I.fp + cellJ j q.2)) := by
  obtain ⟨hev, -⟩ := node_path ht hj hw
  obtain ⟨i, rfl, -, -, -, -, -, hcert, -⟩ := fn_of_idx hj
  intro q hq
  rw [(h.nodeAt hI ht).2 q (by rw [hev]; exact hq), hcert]; rfl

/-- **A loop's last callee frame** is right after its own. -/
theorem frame_tail {hdr : E × E} {T : Tree} {I : Inst} (hI : I ∈ honestInsts coreProgram fs H hdr T)
    {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node f σ bufs kids)
    (hj : idxOf f = some j) (hl : (coreOf j).loop = true) {kfp : ℕ} (hk : I.kidFps.getLast? = some kfp) :
    kfp = I.fp + fsN j := by
  obtain ⟨i, rfl, hi, -, hf, hc, hfs, -⟩ := fn_of_idx hj
  have hlp : coreProgram.loop I.t.name = true := by
    rw [ht]; simp only [Tree.name, Core.Program.loop, hf, ← hc]; exact hl
  have hne : I.t.kids ≠ [] := by
    intro he
    have hlen := congrArg List.length (honest_kidFps hI)
    rw [length_kidPos, List.length_map, he] at hlen
    rw [List.length_eq_zero_iff.mp hlen] at hk
    cases hk
  rw [honest_kidFps_getLast? hI hlp hne] at hk
  rw [← Option.some.inj hk, ht]
  simp only [Tree.name, hfs]

end Place

/-! ## The call sites -/

section Sites

variable {j : ℕ} {G : Glob} {fc : CompiledFn} {main : Bool}

/-- A candidate of `siteE`: a call of the path, its callee frame and its site. -/
theorem siteE_cases {I : Inst} {es : List Ev} {x : ℕ × E} (h : x ∈ siteE j I es) :
    ∃ (i : ℕ) (c : Call) (kfp : ℕ) (s : Site), (calls es)[i]? = some c ∧ I.kidFps[i]? = some kfp ∧
      siteOf j c = some s ∧
      (x = (s.q, ofK (gpow kfp)) ∨ (s.tgt ≠ 0 ∧ x = (s.tgt, ofK (gpow (entryOf c.f))))) := by
  simp only [siteE, List.mem_flatMap] at h
  obtain ⟨p, hp, hx⟩ := h
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hp
  have hi1 : i < (calls es).length := by simp at hi; omega
  have hi2 : i < I.kidFps.length := by simp at hi; omega
  refine ⟨i, (calls es)[i], I.kidFps[i], ?_⟩
  cases hs : siteOf j ((calls es).zip I.kidFps)[i].1 with
  | none => rw [hs] at hx; cases hx
  | some s =>
    rw [hs] at hx
    simp only [List.getElem_zip] at hs hx
    refine ⟨s, List.getElem?_eq_getElem hi1, List.getElem?_eq_getElem hi2, hs, ?_⟩
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact Or.inl rfl
    · split_ifs at hx with ht
      · cases hx
      · exact Or.inr ⟨ht, List.mem_singleton.mp hx⟩

/-- A site's own two cells differ. -/
theorem site_q_tgt (AP : Apart j) {s : Site} (hs : s ∈ (plumbOf j).sites) (ht : s.tgt ≠ 0) : s.q ≠ s.tgt := by
  have := (List.nodup_flatMap.mp AP.siteNodup).1 s hs
  have hb : Nat.beq s.tgt 0 = false := Bool.eq_false_iff.mpr fun hb ↦ ht (nbeq_iff.mp hb)
  simp only [hb, Bool.cond_false, List.nodup_cons, List.mem_singleton] at this
  exact this.1

/-- What the completeness check says of the sites of a path's calls (`Cpl`). -/
def SitesApart (j : ℕ) (es : List Ev) : Prop :=
  ∀ (i i' : ℕ) (c c' : Call) (s s' : Site), i ≠ i' → (calls es)[i]? = some c → (calls es)[i']? = some c' → siteOf j c = some s →
    siteOf j c' = some s' → s.q ≠ s'.q ∧ (s.tgt ≠ 0 → s.tgt ≠ s'.tgt ∧ s.tgt ≠ s'.q)

/-- Every candidate at a cell of a call's site, other than that site's, is ruled out. -/
theorem cand_site (hS : ShareOk j)
    (hchk : ∀ i ≤ (certOf j).cuts.length, checkWin G fc (coreOf j) (certOf j) main i = true)
    {I : Inst} {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree}
    (ht : I.t = .node f σ bufs kids) (hj : idxOf f = some j) {es : List Ev} {vs : List V}
    (hw : walk σ (coreOf j).body = .ret es vs) {o : ℕ} (ho : o ∈ siteCells (plumbOf j)) (h2 : 2 ≤ o)
    {x : ℕ × E} (hx : x ∈ nodeE j f σ I) (hxc : x.1 = o) : x ∈ siteE j I es := by
  have FS := fnStatic hS hchk
  have AP := apart_j hS
  obtain ⟨i, rfl, -, -, -, -, -, hcert, -⟩ := fn_of_idx hj
  have hcJ : ∀ u, cert f u = cellJ (i + 1) u := fun u ↦ hcert u
  obtain ⟨hev, hvs⟩ := node_path ht hj hw
  obtain ⟨hst, hsr, hss, hsl⟩ := AP.site o ho
  simp only [nodeE, List.mem_append, hev, hvs] at hx
  rcases hx with (((((hx | hx) | hx) | hx) | hx) | hx) | hx
  · simp only [valE, List.mem_map] at hx
    obtain ⟨t, htm, rfl⟩ := hx
    obtain ⟨j', hj', htl⟩ := temps_of htm
    rw [hj] at hj'; cases hj'
    exact absurd (by simp only [hcJ] at hxc; exact hxc) (hst _ (FS.tmp t htl).2)
  · obtain ⟨p, r, rs, he', k, hk, rfl⟩ := mem_runsE hx
    have ha' : Atom.frameAddr p (r :: rs) ∈ lAtoms (coreOf (i + 1)).body := walk_atoms _ (by rw [hw]; exact he')
    obtain ⟨-, -, hrun⟩ := FS.run p r rs ha' k hk
    exact absurd (by simp only [hcJ] at hxc; exact hxc) (hsr _ hrun)
  · simp only [List.mem_map] at hx
    obtain ⟨q, hq, rfl⟩ := hx
    exact absurd hxc (hss q hq)
  · simp only [valE, List.mem_map] at hx
    obtain ⟨u, hu, rfl⟩ := hx
    simp only [hcJ] at hxc
    exact absurd (hxc ▸ cellJ_mem (hxc ▸ h2)) hsl
  · exact hx
  · simp only [List.mem_map] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    exact absurd (hxc ▸ ho) (AP.arm a ha).2.2.2.2
  · split_ifs at hx with h1
    · have hlt := (AP.main h1).2.2.2.2.1 o ho
      have : x.1 ∈ tableCells.map Prod.fst := List.mem_map_of_mem hx
      rw [tableCells_offsets, List.mem_range'] at this
      omega
    · cases hx

end Sites

/-! ## The headers -/

section Hdr

/-- A header of words of `K`. -/
def KHdr (h : E × E) : Prop := IsInK h.1 ∧ IsInK h.2

theorem kHdr_ofK (a b : K) : KHdr (ofK a, ofK b) := ⟨Value.ofK_isInK a, Value.ofK_isInK b⟩

theorem kHdr_zero : KHdr (0, 0) := by
  have := kHdr_ofK 0 0
  simpa [ofK_zero] using this

/-- A callee's header is its caller's, or of `K`. -/
theorem H_cases (I : Inst) (i : ℕ) : H I i = I.hdr ∨ KHdr (H I i) := by
  unfold H
  split
  · split
    · split
      · exact Or.inl rfl
      · split
        · exact Or.inr (kHdr_ofK _ _)
        · exact Or.inr kHdr_zero
    · exact Or.inr kHdr_zero
  · exact Or.inr kHdr_zero

/-- Not a loop's: its callees' headers are of `K`. -/
theorem H_K {I : Inst} (hl : coreProgram.loop I.t.name = false) (i : ℕ) : KHdr (H I i) := by
  unfold H
  split
  · rename_i f _ _ _ j ht hj
    split
    · split
      · rename_i h
        rw [ht] at hl
        simp only [Tree.name] at hl
        rw [hl] at h
        exact absurd h.1 (by simp)
      · split
        · exact kHdr_ofK _ _
        · exact kHdr_zero
    · exact kHdr_zero
  · exact kHdr_zero

mutual
/-- Every instance's header is its tree's, or of `K`. -/
theorem insts_hdr : ∀ (t : Tree) (fp : ℕ) (h : E × E), ∀ J ∈ t.insts fs coreProgram.loop H fp h,
    J.hdr = h ∨ KHdr J.hdr
  | .node f σ bufs kids, fp, h, J, hJ => by
      rw [insts_node, List.mem_cons] at hJ
      rcases hJ with rfl | hJ
      · exact Or.inl rfl
      · rcases instsKids_hdr kids _ _ 0 J hJ with he | hk
        · exact Or.inl he
        · exact Or.inr hk
  | .phantom .., fp, h, J, hJ => by
      rw [insts_phantom, List.mem_singleton] at hJ
      subst hJ; exact Or.inl rfl

theorem instsKids_hdr : ∀ (ks : List Tree) (ps : List ℕ) (I : Inst) (i : ℕ),
    ∀ J ∈ Tree.instsKids fs coreProgram.loop H I i ps ks, J.hdr = I.hdr ∨ KHdr J.hdr
  | [], _, _, _, J, hJ => by rw [instsKids_nil] at hJ; exact absurd hJ List.not_mem_nil
  | _ :: _, [], _, _, J, hJ => by rw [instsKids_nil_left] at hJ; exact absurd hJ List.not_mem_nil
  | k :: ks, p :: ps, I, i, J, hJ => by
      rw [instsKids_cons, List.mem_append] at hJ
      rcases hJ with hJ | hJ
      · rcases insts_hdr k p (H I i) J hJ with he | hk
        · rw [he]; exact H_cases I i
        · exact Or.inr hk
      · exact instsKids_hdr ks ps I (i + 1) J hJ
end

theorem instsKids_hdrK {I : Inst} (hI : ∀ i, KHdr (H I i)) : ∀ (ks : List Tree) (ps : List ℕ) (i : ℕ),
    ∀ J ∈ Tree.instsKids fs coreProgram.loop H I i ps ks, KHdr J.hdr
  | [], _, _, J, hJ => by rw [instsKids_nil] at hJ; exact absurd hJ List.not_mem_nil
  | _ :: _, [], _, J, hJ => by rw [instsKids_nil_left] at hJ; exact absurd hJ List.not_mem_nil
  | k :: ks, p :: ps, i, J, hJ => by
      rw [instsKids_cons, List.mem_append] at hJ
      rcases hJ with hJ | hJ
      · rcases insts_hdr k p (H I i) J hJ with he | hk
        · rw [he]; exact hI i
        · exact hk
      · exact instsKids_hdrK hI ks ps (i + 1) J hJ

theorem main_not_loop : coreProgram.loop "main" = false := by decide +kernel

/-- **Every instance but `main`'s returns to registers of `K`.** -/
theorem honest_hdrK {hdr : E × E} {T : Tree} (hT : T.name = "main") {J : Inst}
    (hJ : J ∈ honestInsts coreProgram fs H hdr T) (hn : J.t.name ≠ "main") : KHdr J.hdr := by
  unfold honestInsts at hJ
  cases T with
  | phantom f σ =>
    rw [insts_phantom, List.mem_singleton] at hJ
    subst hJ; exact absurd hT hn
  | node f σ bufs kids =>
    rw [insts_node, List.mem_cons] at hJ
    rcases hJ with rfl | hJ
    · exact absurd hT hn
    · refine instsKids_hdrK (fun i ↦ H_K ?_ i) kids _ 0 J hJ
      simp only [Tree.name] at hT ⊢
      rw [hT]; exact main_not_loop

end Hdr

/-! ## The callees -/

section Kids

theorem kidsValid_at {rd : Reader} {σ : Val} : ∀ {cs : List Call} {ks : List Tree},
    Tree.KidsValid coreProgram rd σ cs ks → ∀ (i : ℕ) (c : Call), cs[i]? = some c →
      ∃ k, ks[i]? = some k ∧ k.name = c.f ∧
        (if c.taken then k.Valid coreProgram rd (c.args.map σ) (c.rets.map σ)
          else (∃ f σ', k = .phantom f σ') ∧ Phantom coreProgram k (c.args.map σ))
  | [], [], _, _, _, h => by simp at h
  | [], _ :: _, h, _, _, _ => h.elim
  | _ :: _, [], h, _, _, _ => h.elim
  | c :: cs, k :: ks, ⟨hn, hk, h⟩, i, c', hc => by
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hc
      subst hc
      exact ⟨k, rfl, hn, hk⟩
    | succ i =>
      simp only [List.getElem?_cons_succ] at hc ⊢
      exact kidsValid_at h i c' hc

/-- **The `i`-th callee of a path**: an instance at the `i`-th callee frame, with the header
`H I i`, valid if the call is taken, else a phantom with the arguments. -/
theorem kid_inst {hdr : E × E} {T : Tree} {I : Inst} (hI : I ∈ honestInsts coreProgram fs H hdr T)
    {rd : Reader} {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node f σ bufs kids)
    {es : List Ev} (hk : Tree.KidsValid coreProgram rd σ (calls es) kids) {i : ℕ} {c : Call} {kfp : ℕ}
    (hc : (calls es)[i]? = some c) (hp : I.kidFps[i]? = some kfp) :
    ∃ J ∈ honestInsts coreProgram fs H hdr T, J.fp = kfp ∧ J.hdr = H I i ∧ J.t.name = c.f ∧
      (if c.taken then J.t.Valid coreProgram rd (c.args.map σ) (c.rets.map σ)
        else (∃ f σ', J.t = .phantom f σ') ∧ Phantom coreProgram J.t (c.args.map σ)) := by
  obtain ⟨k, hki, hn, hv⟩ := kidsValid_at hk i c hc
  obtain ⟨J, hJ, rfl, hfp, hh⟩ := honest_kid hI (by rw [ht]; exact hki)
  rw [hp] at hfp
  exact ⟨J, hJ, (Option.some.inj hfp).symm, hh, hn, hv⟩

end Kids

end
end LeanVM.Guest.B2C
