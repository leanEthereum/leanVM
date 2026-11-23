/-
  LeanVM.Guest.EndExecCore

  `ExecGaps.core` on the tracks' invariant: each frame of a function on the core route, at each
  state of its run, is an honest instance of it, whose valuation is the core route's honest one.
-/

module

public import LeanVM.Guest.EndExecEntry
public import LeanVM.Guest.CoreMode.Fam.Kid
public import LeanVM.Guest.CoreMode.WalkS
public import LeanVM.Guest.Bridge.JumpCells
public import LeanVM.Guest.Bridge.JumpCells.All
public import LeanVM.Guest.Bridge.ProgAlKeys
public import LeanVM.Guest.EndExecLoop
public import LeanVM.Guest.EndExecChain
public import LeanVM.Guest.EndExecCoreResAll
public import LeanVM.Guest.EndExecCoreSt

/-!
# The core route's honest frames

`coreHonAll_X`: for core data of the deployed guest at a function's entry (`CfOk`), at each state
of the tracks' invariant at an offset of the function, the top frame of the tree track (`trackAt_X`)
is an honest instance (`RefOk.frames`) of the function at that entry (the alignment's function there,
`res_of_top`'s argument; entries distinct, `fnOf_entry_inj`), a node of a valid tree, so its path's
events hold (`insts_good`); its frame holds each value the path names at its certificate cell
(`FrameHolds.val`), which are the alignment context's cells (`locAt_ofData`) for its pointers, and
`2 + k` for its parameters (`honB`); its heap certificate's residuals, of families (`resOk`), hold at its
valuation (`resOk_inst`).
-/

namespace LeanVM.Guest.Bridge

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

public section

section Walk

variable {σ : Val}

theorem sel_mono {P : Prop} {x : V} {seen seen' : List Atom} {es es' : List Ev}
    (h : ∀ a, (a ∈ seen ∨ Ev.atom a ∈ es) → a ∈ seen' ∨ Ev.atom a ∈ es') :
    (P ∨ ∃ a, (a ∈ seen ∨ Ev.atom a ∈ es) ∧ x ∈ Memory.atomUses a) →
      P ∨ ∃ a, (a ∈ seen' ∨ Ev.atom a ∈ es') ∧ x ∈ Memory.atomUses a
  | .inl p => .inl p
  | .inr ⟨a, ha, hu⟩ => .inr ⟨a, h a ha, hu⟩

/-- **`selGo`'s selectors**: on a path that returns, the selector `x` of each `match` and `dispatch` of the body
is at its cell, and a dispatch's a parameter or a use of an atom seen before it or on the path. -/
theorem selGo_sel {j : ℕ} {ps : List V} {σ : Val} : ∀ (seen : List Atom) (ss : List Stmt) {es : List Ev} {vs : List V},
    CoreMode.selGo j ps seen ss = true → ss.all CoreMode.topOk = true → walk σ ss = .ret es vs →
    ∀ s ∈ stmtsOf ss, ∀ x, ((∃ arms, s = .match_ x arms) ∨ ∃ fs args rets, s = .dispatch x fs args rets) →
      CoreMode.cellB j x = true ∧ ((∃ fs args rets, s = .dispatch x fs args rets) ∧ x ∈ ps ∨
        ∃ a, (a ∈ seen ∨ Ev.atom a ∈ es) ∧ x ∈ Memory.atomUses a)
  | _, [], _, _, _, _, _, s, hm, _, _ => by simp [stmtsOf] at hm
  | seen, .atom b :: ss, es, vs, h, ht, hw, s, hm, x, hs => by
    simp only [CoreMode.selGo] at h
    simp only [List.all_cons, Bool.and_eq_true] at ht
    rw [walk_atom_cons] at hw
    obtain ⟨es', hw', rfl⟩ := pre_eq_ret hw
    simp only [stmtsOf, stmtsSub, List.mem_cons, List.nil_append] at hm
    rcases hm with rfl | hm
    · rcases hs with ⟨_, h'⟩ | ⟨_, _, _, h'⟩ <;> cases h'
    obtain ⟨hc, hr⟩ := selGo_sel (b :: seen) ss h ht.2 hw' s hm x hs
    refine ⟨hc, sel_mono (fun a ha ↦ ?_) hr⟩
    rcases ha with ha | ha
    · rcases List.mem_cons.mp ha with rfl | ha
      · exact Or.inr (by simp)
      · exact Or.inl ha
    · exact Or.inr (by simp [ha])
  | seen, .match_ y arms' :: ss, es, vs, h, ht, hw, s, hm, x, hs => by
    simp only [CoreMode.selGo, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true] at h
    obtain ⟨⟨⟨hc, ⟨a, ha, hu⟩⟩, hna⟩, h⟩ := h
    simp only [List.all_cons, Bool.and_eq_true] at ht
    simp only [stmtsOf, stmtsSub, List.mem_cons, List.mem_append] at hm
    rcases hm with rfl | hm | hm
    · rcases hs with ⟨_, h'⟩ | ⟨_, _, _, h'⟩ <;> cases h'
      exact ⟨hc, Or.inr ⟨a, Or.inl ha, hu⟩⟩
    · rcases hs with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩
      · have := List.all_eq_true.mp hna _ hm
        simp at this
      · have h1' := ht.1
        simp only [CoreMode.topOk, Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false, stmtsSub] at h1'
        exact absurd rfl (h1'.2 _ hm)
    · rw [walk] at hw
      rcases seq_eq_ret hw with ⟨es1, es2, -, h2, rfl⟩ | h1
      · obtain ⟨hc', hr⟩ := selGo_sel seen ss h ht.2 h2 s hm x hs
        exact ⟨hc', sel_mono (fun a ha ↦ ha.imp id (List.mem_append_right _)) hr⟩
      · exact absurd h1 (CoreMode.walk1_noRetP _ (by
          have h1' := ht.1
          simp only [CoreMode.topOk, Bool.and_eq_true] at h1'
          exact h1'.1) _ _)
  | seen, .ite c z n :: ss, es, vs, h, ht, hw, s, hm, x, hs => by
    simp only [CoreMode.selGo, Bool.and_eq_true] at h
    obtain ⟨⟨hz, hn⟩, h⟩ := h
    simp only [List.all_cons, Bool.and_eq_true] at ht
    simp only [stmtsOf, stmtsSub, List.mem_cons, List.mem_append] at hm
    rcases hm with rfl | hm | hm
    · rcases hs with ⟨_, h'⟩ | ⟨_, _, _, h'⟩ <;> cases h'
    · rcases hs with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩
      · rcases hm with hm | hm
        · have := List.all_eq_true.mp hz _ hm
          simp at this
        · have := List.all_eq_true.mp hn _ hm
          simp at this
      · have h1' := ht.1
        simp only [CoreMode.topOk, Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false, stmtsSub,
          List.mem_append] at h1'
        exact absurd rfl (h1'.2 _ hm)
    · rw [walk] at hw
      rcases seq_eq_ret hw with ⟨es1, es2, -, h2, rfl⟩ | h1
      · obtain ⟨hc', hr⟩ := selGo_sel seen ss h ht.2 h2 s hm x hs
        exact ⟨hc', sel_mono (fun a ha ↦ ha.imp id (List.mem_append_right _)) hr⟩
      · exact absurd h1 (CoreMode.walk1_noRetP _ (by
          have h1' := ht.1
          simp only [CoreMode.topOk, Bool.and_eq_true] at h1'
          exact h1'.1) _ _)
  | seen, .ret vs' :: ss, es, vs, h, ht, hw, s, hm, x, hs => by
    simp only [CoreMode.selGo, Bool.and_eq_true] at h
    simp only [stmtsOf, stmtsSub, List.mem_cons, List.nil_append] at hm
    rcases hm with rfl | hm
    · rcases hs with ⟨_, h'⟩ | ⟨_, _, _, h'⟩ <;> cases h'
    rcases hs with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩
    · have := List.all_eq_true.mp h.1 _ hm
      simp at this
    · have := List.all_eq_true.mp h.2 _ hm
      simp at this
  | seen, .call f args rets :: ss, es, vs, h, ht, hw, s, hm, x, hs => by
    simp only [CoreMode.selGo] at h
    simp only [List.all_cons, Bool.and_eq_true] at ht
    rw [walk_call_cons] at hw
    obtain ⟨es', hw', rfl⟩ := pre_eq_ret hw
    simp only [stmtsOf, stmtsSub, List.mem_cons, List.nil_append] at hm
    rcases hm with rfl | hm
    · rcases hs with ⟨_, h'⟩ | ⟨_, _, _, h'⟩ <;> cases h'
    obtain ⟨hc, hr⟩ := selGo_sel seen ss h ht.2 hw' s hm x hs
    exact ⟨hc, sel_mono (fun a ha ↦ ha.imp id (fun h ↦ by simp [h])) hr⟩
  | seen, .callIf c f args :: ss, es, vs, h, ht, hw, s, hm, x, hs => by
    simp only [CoreMode.selGo] at h
    simp only [List.all_cons, Bool.and_eq_true] at ht
    rw [walk_callIf_cons] at hw
    obtain ⟨es', hw', rfl⟩ := pre_eq_ret hw
    simp only [stmtsOf, stmtsSub, List.mem_cons, List.nil_append] at hm
    rcases hm with rfl | hm
    · rcases hs with ⟨_, h'⟩ | ⟨_, _, _, h'⟩ <;> cases h'
    obtain ⟨hc, hr⟩ := selGo_sel seen ss h ht.2 hw' s hm x hs
    exact ⟨hc, sel_mono (fun a ha ↦ ha.imp id (fun h ↦ by simp [h])) hr⟩
  | seen, .dispatch y fs' args' rets' :: ss, es, vs, h, ht, hw, s, hm, x, hs => by
    simp only [CoreMode.selGo, Bool.and_eq_true, Bool.or_eq_true, List.contains_iff_mem, decide_eq_true_eq,
      List.any_eq_true] at h
    obtain ⟨⟨hc, hsel⟩, h⟩ := h
    simp only [List.all_cons, Bool.and_eq_true] at ht
    simp only [stmtsOf, stmtsSub, List.mem_cons, List.nil_append] at hm
    rcases hm with rfl | hm
    · rcases hs with ⟨_, h'⟩ | ⟨_, _, _, h'⟩ <;> cases h'
      rcases hsel with hp | ⟨a, ha, hu⟩
      · exact ⟨hc, Or.inl ⟨⟨_, _, _, rfl⟩, hp⟩⟩
      · exact ⟨hc, Or.inr ⟨a, Or.inl ha, hu⟩⟩
    · obtain ⟨f, -, es', rfl, hw'⟩ := CoreMode.walk_dispatch_ret hw
      obtain ⟨hc', hr⟩ := selGo_sel seen ss h ht.2 hw' s hm x hs
      exact ⟨hc', sel_mono (fun a ha ↦ ha.imp id (fun h ↦ by simp [h])) hr⟩

theorem selGo_sound {j : ℕ} {ps : List V} {σ : Val} (seen : List Atom) (ss : List Stmt) {es : List Ev} {vs : List V}
    (h : CoreMode.selGo j ps seen ss = true) (ht : ss.all CoreMode.topOk = true) (hw : walk σ ss = .ret es vs)
    (x : V) (arms : List (List Stmt)) (hm : Stmt.match_ x arms ∈ stmtsOf ss) : CoreMode.cellB j x = true ∧
      ∃ a, (a ∈ seen ∨ Ev.atom a ∈ es) ∧ x ∈ Memory.atomUses a := by
  obtain ⟨hc, ⟨⟨_, _, _, h'⟩, -⟩ | hr⟩ := selGo_sel seen ss h ht hw _ hm x (Or.inl ⟨arms, rfl⟩)
  · cases h'
  · exact ⟨hc, hr⟩

theorem selGoD_sound {j : ℕ} {ps : List V} {σ : Val} (seen : List Atom) (ss : List Stmt) {es : List Ev} {vs : List V}
    (h : CoreMode.selGo j ps seen ss = true) (ht : ss.all CoreMode.topOk = true) (hw : walk σ ss = .ret es vs)
    (x : V) (fs : List String) (args rets : List V) (hm : Stmt.dispatch x fs args rets ∈ stmtsOf ss) :
    CoreMode.cellB j x = true ∧ (x ∈ ps ∨ ∃ a, (a ∈ seen ∨ Ev.atom a ∈ es) ∧ x ∈ Memory.atomUses a) := by
  obtain ⟨hc, hr⟩ := selGo_sel seen ss h ht hw _ hm x (Or.inr ⟨fs, args, rets, rfl⟩)
  exact ⟨hc, hr.imp (·.2) id⟩

end Walk

end

end LeanVM.Guest.Bridge

namespace LeanVM.Guest.Bridge

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B2C
open LeanVM.Guest.Check (getF getF_eq)

public section

/-- **A chained `match`'s target cell, on the arm the path takes**: each chain's arms jump through one
cell (`chainOneB`), and a path takes one of them (`walk_takes`). -/
theorem chain_taken {j : ℕ} {σ : Val} {es : List Ev} {vs : List V} (hj1 : 0 < j) (hj2 : j < nFns)
    (hw : walk σ (coreOf j).body = .ret es vs) {ch : ℕ × ℕ × List ℕ × ℕ × ℕ} (hch : ch ∈ (plumbOf j).chains)
    {t : ℕ} (ht : t ∈ ch.2.2.1) : ∃ k, ch.2.2.1[k]? = some t ∧ σ (V.n ch.2.1) = ofK (addressOfIndex k) := by
  have hc := (Chained.chainOk_all _ hj1 hj2).1
  simp only [chainFn, Bool.and_eq_true, List.all_eq_true] at hc
  obtain ⟨-, hm⟩ := hc.2 ch hch
  split at hm
  · rename_i x arms y arms' hp _
    simp only [Bool.and_eq_true, decide_eq_true_eq, Nat.beq_eq] at hm
    obtain ⟨⟨⟨hx, -⟩, hlen⟩, -⟩ := hm
    subst hx
    obtain ⟨k, hk, hσ⟩ :=
      EndExec.walk_takes (lastBody (Cplw.cplOk_all _ hj1 hj2) (End.winOk_of (by omega) hj2)) hw hp
    have hkt : k < ch.2.2.1.length := hlen ▸ hk
    refine ⟨k, ?_, hσ⟩
    have hone := List.all_eq_true.mp EndExec.chainOneB_true _ (List.mem_range.mpr hj2)
    have hch' := List.all_eq_true.mp (List.all_eq_true.mp hone ch hch)
    rw [List.getElem?_eq_getElem hkt, beq_iff_eq.mp (hch' _ (List.getElem_mem hkt)), beq_iff_eq.mp (hch' t ht)]
  · cases hm

/-- **What a frame's jumps read**, for function `j` (`main`'s frame `0`) at frame `fp` holding what its
check reads (`FrameHolds`), the jump table in memory: `jumpCells_of`'s fixed cells, conditions and table
targets, a chained `match`'s on the arm the path takes, at any state of the frame. -/
theorem jumpF_of {κ : ℕ} {L : MemoryImage κ} {j fp : ℕ} {σ : Val} {es : List Ev} {vs : List V} {kfps : List ℕ}
    {hdr : E × E} (hj1 : 0 < j) (hroot : j = 1 → fp = 0) (hj2 : j < nFns)
    (hlocs : (certOf j).locs.all (fun c ↦ Nat.blt c (2 ^ cellBits)) = true)
    (hF : FrameHolds L j fp σ es vs kfps hdr) (hwc : walk σ (coreOf j).body = .ret es vs)
    (hjt : Check.JTHolds glob L) (htab : End.JumpTables L)
    (hsel : ∀ x arms, Stmt.match_ x arms ∈ stmtsOf (coreOf j).body →
      CoreMode.Rd L fp ((ctxOf j).locAt x.idx) = some (σ x))
    (hdsel : ∀ x fs args rets, Stmt.dispatch x fs args rets ∈ stmtsOf (coreOf j).body →
      CoreMode.Rd L fp ((ctxOf j).locAt x.idx) = some (σ x)) :
    CoreMode.JumpF L (ctxOf j) (coreOf j).body fp σ := by
  have hrd : ∀ o, CoreMode.Rd L fp o = cellAt L fp o := fun o ↦ by
    simp [CoreMode.Rd, cellAt, addressOfIndex, pow_add]
  have hd := JumpCells.jcData_all j (by omega) (by have : nFns = fn_count% := rfl; omega)
  unfold jcData jcDataD at hd
  simp only [Bool.and_eq_true] at hd
  obtain ⟨⟨⟨⟨⟨⟨⟨hstat, harms⟩, -⟩, -⟩, hextra⟩, hblock⟩, -⟩, -⟩ := hd
  have hcont := Check.cont_of (End.winOk_of (by omega) hj2)
  have hstatB : ∀ {o : ℕ} {w : PC}, (o, w) ∈ (plumbOf j).stat →
      cellAt L fp o = some (w.word fp) ∧ (∀ a b, w = .k a b → a < 2 ^ 64 ∧ b < 2 ^ 64) := by
    intro o w hm
    have hb := List.all_eq_true.mp hstat _ hm
    simp only [cellIn, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hb
    refine ⟨hF.stat _ hm hb.1.1 hb.1.2, fun a b hw' ↦ ?_⟩
    subst hw'
    simpa only [Bool.and_eq_true, Nat.blt_eq] using hb.2
  refine ⟨?zero, ?nz, ?self, ?pcw, ?cond, ?arm, fun _ _ _ x arms hm ↦ hsel x arms hm,
    fun _ _ _ x fs args rets hm ↦ hdsel x fs args rets hm⟩
  case zero =>
    intro o hz
    rw [hrd]
    unfold AlignCtx.zeroAt at hz
    split at hz
    · rename_i k0 k1 hso
      simp only [Bool.and_eq_true, Nat.beq_eq] at hz
      obtain ⟨rfl, rfl⟩ := hz
      rw [(hstatB (statOf_ofData hso)).1]
      simp [PC.word, Mode.imm_zero]
    · cases hz
  case nz =>
    intro o hz
    rw [hrd]
    unfold AlignCtx.nzAt at hz
    split at hz
    · rename_i k0 k1 hso
      obtain ⟨hr, hk⟩ := hstatB (statOf_ofData hso)
      obtain ⟨ha, hb⟩ := hk k0 k1 rfl
      refine ⟨_, hr, Mode.imm_ne_zero ha hb fun ⟨h0, h1⟩ ↦ ?_⟩
      subst h0 h1
      simp at hz
    · cases hz
  case self =>
    intro o hz
    rw [hrd]
    unfold AlignCtx.selfAt at hz
    split at hz
    · rename_i hso
      rw [(hstatB (statOf_ofData hso)).1]
      simp [PC.word, addressOfIndex]
    · rename_i hso
      have h1 : j = 1 := by simpa [ctxOf, AlignCtx.ofData] using hz
      rw [(hstatB (statOf_ofData hso)).1, hroot h1]
      simp only [PC.word]
      rw [(Exec.imm_of_ofBits rfl).trans Exec.ofK_one]
      simp
    · cases hz
  case pcw =>
    intro o t hz
    rw [hrd]
    unfold AlignCtx.pcAt at hz
    split at hz
    · rename_i k0 hso
      rw [(hstatB (statOf_ofData hso)).1]
      simp only [PC.word]
      rw [Exec.imm_of_ofBits (Mode.PowTree.find_ok' (Exec.PowTree.ok_of_okW Checked.powTree_ok) hz)]
    · cases hz
  case cond =>
    intro es' vs' hw' c hc
    rw [hwc, Out.ret.injEq] at hw'
    obtain ⟨rfl, rfl⟩ := hw'
    rw [hrd]
    have hcc : c ∈ condsOf (coreOf j).body := walk_inK _ (by rw [hwc, evsOf_ret]; exact hc)
    have hco := blockB_conds _ _ hblock c hcc
    unfold condOk at hco
    simp only [Bool.and_eq_true, Nat.blt_eq] at hco
    obtain ⟨hidx, hxc⟩ := hco
    split at hxc
    · rename_i x hxs
      have hloc := cellW_spec hcont hxs
      simp only [cellIn, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hxc
      have hval := hF.val c (List.mem_append_left _ (List.mem_append_right _
        (List.mem_flatMap.mpr ⟨_, hc, by simp [Ev.uses]⟩))) (by rw [cellJ, hloc]; exact hxc.1)
        (by rw [cellJ, hloc]; exact hxc.2)
      have hxn : (extraOf j).lookup c.idx = none := by
        cases hl : (extraOf j).lookup c.idx with
        | none => rfl
        | some c' =>
          have hm := mem_of_lookupN hl
          have := List.all_eq_true.mp hextra _ hm
          split at this
          · rename_i y hy
            rw [cellW_spec hcont hy] at hloc
            simp only [Nat.blt_eq] at this
            omega
          · cases this
      have hla : (ctxOf j).locAt c.idx = (certOf j).locs.getD c.idx 0 := locAt_ofData hlocs hxn hidx
      rw [hla]
      exact hval
    · cases hxc
  case arm =>
    intro x arms hmem od a ha hax k t hσk ht'
    have hnum : x = V.n x.idx := numbered_eq (blockB_sels _ _ hblock _ hmem x arms rfl)
    have hσx : σ (V.n a.1) = ofK (addressOfIndex k) := by rw [hax, ← hnum]; simpa [addressOfIndex] using hσk
    have hglob : glob.jt.get (a.2 + k) = some t := by
      change Data.jtTrie.get (a.2 + k) = some t
      rw [← getF_eq]; exact ht'
    obtain ⟨hf, hlt⟩ := tbl_slot hjt htab hglob
    have hword := tbl_armWord hσx hf hlt
    have hmem' := arms_ofData ha
    have hb := List.all_eq_true.mp harms _ hmem'
    simp only [cellIn, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hb
    unfold armsOf at hmem'
    rcases List.mem_append.mp hmem' with hmem' | hmem'
    · obtain ⟨q, hq, hqe⟩ := List.mem_map.mp hmem'
      simp only [Prod.mk.injEq] at hqe
      obtain ⟨rfl, rfl⟩ := hqe
      rw [hrd, cellAt, hF.arm q hq hb.1 hb.2, hword]
    · obtain ⟨ch, hch, hm⟩ := List.mem_flatMap.mp hmem'
      obtain ⟨t', ht'', hqe⟩ := List.mem_map.mp hm
      simp only [Prod.mk.injEq] at hqe
      obtain ⟨rfl, rfl⟩ := hqe
      obtain ⟨k', hk', hσk'⟩ := chain_taken hj1 hj2 hwc hch ht''
      obtain ⟨-, -, -, -, hrd'⟩ := hF.chain ch hch k' t' hk' hσk'
      rw [hrd, cellAt, hrd' hb.1 hb.2, hword]

end

end LeanVM.Guest.Bridge

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B2C (idxOf entryOf FrameHolds plumbOf fsN fn_of_idx cellJ namedOf)
open LeanVM.Guest.Bridge (FnAl ProgAl AtPc Ent entOf alOf alignAt alignAt_step)
open LeanVM.Prover.Exec

public section

theorem ptrOf_uses {a : Atom} {p : V} (h : CoreMode.ptrOf a = some p) : p ∈ Memory.atomUses a := by
  cases a with
  | load d p' off => cases h; simp [Memory.atomUses]
  | hint hh =>
    simp only [CoreMode.ptrOf, Option.map_eq_some_iff] at h
    obtain ⟨⟨p', off, len⟩, hd, rfl⟩ := h
    cases hh with
    | witness s d => cases d <;> simp_all [CoreMode.hintHeap, Memory.atomUses, Memory.hintUses, Memory.destUses]
    | bits v st nb d => cases d <;> simp_all [CoreMode.hintHeap, Memory.atomUses, Memory.hintUses, Memory.destUses]
    | bitsExp v nb d => cases d <;> simp_all [CoreMode.hintHeap, Memory.atomUses, Memory.hintUses, Memory.destUses]
    | digitsExp v nb nd db st sc d =>
      cases d <;> simp_all [CoreMode.hintHeap, Memory.atomUses, Memory.hintUses, Memory.destUses]
    | windowsExp v st w c d => cases d <;> simp_all [CoreMode.hintHeap, Memory.atomUses, Memory.hintUses, Memory.destUses]
    | _ => simp [CoreMode.hintHeap] at hd
  | _ => cases h

/-- **A callee a context names by entry** is a compiled function entered there. -/
theorem ctxOf_ent {j t : ℕ} {g : String} (h : (Bridge.ctxOf j).entOk t g = true) :
    ∃ c, B2C.idxOf g = some c ∧ (Bridge.ctxOf c).entry = t := by
  simp only [Bridge.ctxOf, Bridge.AlignCtx.ofData, Bridge.AlignCtx.entOk] at h
  have hb : ∀ p ∈ (Bridge.entsOf j).map (fun e ↦ (e.2, e.1)), p.1 + 1 < 2 ^ Exec.indexDepth := by
    intro p hp
    simp only [Bridge.entsOf, List.map_map, List.mem_map, Function.comp_apply] at hp
    obtain ⟨c, hc, rfl⟩ := hp
    exact Bridge.entry_key (Bridge.calleesOf_mem hc).2
  split at h
  · rename_i g' hg
    have hgg : g' = g := by simpa using h
    subst hgg
    have hm := Bridge.trieOf_mem hb hg
    simp only [Bridge.entsOf, List.map_map, List.mem_map, Function.comp_apply, Prod.mk.injEq] at hm
    obtain ⟨c, hc, rfl, rfl⟩ := hm
    obtain ⟨h1, h2⟩ := Bridge.calleesOf_mem hc
    exact ⟨c, B2C.idxOf_coreOf h1 h2, rfl⟩
  · cases h

/-- **The core route's frames are honest**, on the tracks' invariant. -/
theorem coreHonAll_X {Ks : List Mode.Cert} {Km : Mode.Cert} {E0 : Mode.Env} {A : String → FnAl}
    {Y : Ref → St → Prop} (certs : ModeCerts Ks Km E0) (hKs : ∀ K ∈ Ks, K.F.entry ≠ 0)
    (hP : ProgAl guestProgram coreProgram A) (hmain : entOf A "main" = End.mainEntry) (hJ : JumpCellsAt A)
    (hL : AlLayout A) (hAX : ∀ f j, B2C.idxOf f = some j → (A f).X = Bridge.ctxOf j) (hLk : LinkOk Res.anyLink) :
    CoreHonAll Ks (XOf Y) := by
  intro r hr K hK Cf hCf hent s i hon' hi hpc
  obtain ⟨f, hf, hcode, hentry, -⟩ := certs.fn K hK
  have hif : i < f.instructionCount := by
    rw [← CompiledFunction.length_code (CompiledFunction.wellChunked_of_mem hf), ← hcode]; exact hi
  have hge : proLen ≤ s.steps := by
    rcases hon'.1.1 with ⟨hlt, hpcs, -⟩ | ⟨hge, -⟩
    · have := consecutive_entry functions_consecutive _ f0_mem f hf (by rw [f0_entry']; omega)
        (by rw [f0_entry']; show f.entryPc < 0 + proLen; omega)
      rw [f0_entry'] at this
      exact absurd (hentry.trans this) (hKs K hK)
    · exact hge
  have hpcf := guest_pc_lt hf hif
  obtain ⟨done, e0, st, htr⟩ := trackAt_X hP hmain hJ hL hr hon' hge (by omega)
  obtain ⟨e, st', hst, hE, hfp, hat⟩ := htr.top
  obtain ⟨rd, hH, hXh⟩ := hr.honest
  obtain ⟨hI, j, bufs, kids, vs, hj, hIt, hfn, hw, hF⟩ :=
    htr.frames hr.name hH hXh.covers e (by rw [hst]; exact List.mem_cons_self)
  -- the frame's function is `K`'s
  have hentK : entryOf e.I.t.name = K.F.entry := by
    obtain ⟨off, hpcoff, p, hal, -⟩ := hat
    obtain ⟨cf, hcf, hcent, hcentry, hlen⟩ := hL _ _ hE.find
    obtain ⟨ins, -, -, -, -, hins, -⟩ :=
      alignAt_step (hP.ok _ _ hE.find) (show alignAt _ _ _ _ off = some p from hal)
    have hoff : off < cf.instructionCount := lt_of_lt_of_le (List.getElem?_eq_some_iff.mp hins).1 hlen
    rw [hcent] at hpcoff
    have heq : cf.entryPc = f.entryPc := by
      rcases le_total cf.entryPc f.entryPc with h1 | h1
      · exact (consecutive_entry functions_consecutive cf hcf f hf h1 (by omega)).symm
      · exact consecutive_entry functions_consecutive f hf cf hcf h1 (by omega)
    rw [hcentry, heq, hentry]
  -- it is `Cf`'s function
  obtain ⟨j0, hj0, he0, hc0, hx0, hb0⟩ := hCf
  obtain ⟨-, -, -, -, -, -, -, -, -, hjn⟩ := fn_of_idx hj
  have hjj : j = j0 := fnOf_entry_inj hjn hj0 (by rw [← B2C.entryOf_of hj, hentK, ← hent, he0])
  subst hjj
  rw [hc0] at hfn
  -- the honest valuation
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hb0
  obtain ⟨⟨⟨hb0, hres0⟩, hgl0⟩, hfa0⟩ := hb0
  simp only [CoreMode.honB, Bool.and_eq_true, List.all_eq_true] at hb0
  obtain ⟨⟨⟨⟨⟨⟨⟨hlocs, hbody⟩, hptr⟩, hpar⟩, hcells⟩, hrc⟩, hj1⟩, hselB⟩ := hb0
  have hfpL : e.I.fp = s.fp := hfp
  -- `main`'s instance is the root, in frame `0`
  have hroot : j = 1 → s.fp = 0 := fun h1 ↦ by
    rw [← hfpL]
    rcases Bridge.insts_main_or _ _ _ hH.valid e.I hI with ⟨h0, -⟩ | h0
    · exact h0
    · exact absurd ((B2C.idx_one_iff hj).mp h1) h0
  have hXA : (A e.I.t.name).X = Cf.X := by rw [hAX _ _ hj, hx0]
  have hJC : Bridge.JumpCells r.img A e s.pc := hJ r hr _ _ _ _ _ (by rw [← hst]; exact htr)
  have hparF : ∀ k < Cf.fn.params.length, CoreMode.Rd r.img s.fp (2 + k) = some (e.σ (V.n k)) := by
    -- a parameter at its cell
    intro k hk
    have hc := hcells k (List.mem_range.mpr hk)
    simp only [Nat.beq_eq, decide_eq_true_eq] at hc
    have hpe := CoreMode.paramsN_eq _ 0 hpar
    have hnamed : V.n k ∈ namedOf (coreOf j).params (e.pre ++ e.es) vs := by
      simp only [namedOf, List.mem_append]
      refine Or.inl (Or.inl ?_)
      rw [hc0, hpe]
      simpa using hk
    have := hF.val (V.n k) hnamed (by omega) (by omega)
    rw [hc.1] at this
    rw [← hfpL]
    simpa [CoreMode.Rd, addressOfIndex, pow_add] using this
  have hfind : coreProgram.find? e.I.t.name = some Cf.fn := by rw [hfn]; exact hE.find
  have hpN : Cf.fn.params = (List.range Cf.fn.params.length).map V.n := by
    rw [List.range_eq_range']; exact CoreMode.paramsN_eq _ 0 hpar
  suffices hB : CoreMode.HonB r.img Cf s.fp e.σ by
    cases hck : CoreMode.cmK Cf.fn with
    | some m =>
      -- a frame loop of the gap walk: its ghost words its caller's entries, bound and frame
      have hgl1 := hgl0
      simp only [CoreMode.glOk, hck, Option.isSome_some, Bool.cond_true, CoreMode.cmGl, Option.any_some,
        Bool.and_eq_true, decide_eq_true_eq, Nat.beq_eq] at hgl1
      obtain ⟨⟨⟨hglv, hgh⟩, hng⟩, hgw0⟩ := hgl1
      obtain ⟨gw, hsub, hglF⟩ := CoreMode.FnReg.cmLoops_ok _ (CoreMode.lookup_memL hck) hr _ hI e.σ bufs kids
        (by rw [find_name' hfind]; exact hIt) _ (by rw [find_name' hfind]; exact hfind) hck hF.hdr1
      refine ⟨CoreMode.setG e.σ gw, CoreMode.honB_setG hB hng, fun hxw ↦ ?_, ?_, fun c j hc ↦ by rw [List.isEmpty_iff.mp hgw0] at hc; cases hc⟩
      · exact resOk_instG hr hI hIt hfind hres0 hparF hxw
          (fun m hm ↦ CoreMode.setG_eq (show (V.n m).idx < CoreMode.GB from hm))
          (fun x hx ↦ by cases x <;> simp [CoreMode.mlSub, cmK_mlK hck] at hx)
          (fun x hx ↦ by cases x <;> simp [CoreMode.stSub, cmK_stK hck] at hx) hsub
          (fun x hx ↦ by rw [List.isEmpty_iff.mp hgw0, CoreMode.gwFam_nil] at hx; cases hx)
      · rw [← hfpL]
        exact hglF Cf rfl hglv hgh
    | none =>
    cases hsk : CoreMode.stK Cf.fn with
    | some p =>
      -- a stream-cursor loop: its ghost words its caller's stream and frame
      obtain ⟨D, v, S⟩ := p
      have hgl1 := hgl0
      simp only [CoreMode.glOk, hck, hsk, Option.isSome_none, Bool.cond_false, Option.isSome_some, Bool.cond_true,
        CoreMode.stGl, Option.any_some,
        Bool.and_eq_true, decide_eq_true_eq, Nat.beq_eq] at hgl1
      obtain ⟨⟨⟨hglv, hgh⟩, hng⟩, hgw0⟩ := hgl1
      have hmk := stK_mlK hsk
      obtain ⟨a, ha, haD, hsub⟩ := st_inst hr hI hIt hfind hsk
      have hD0 : D ≠ 0 := stK_D hsk
      refine ⟨CoreMode.setG e.σ [refMem r.img (a + D), ofK (Parameters.g ^ a)], CoreMode.honB_setG hB hng,
        fun hxw ↦ ?_, ?_, fun c j hc ↦ by rw [List.isEmpty_iff.mp hgw0] at hc; cases hc⟩
      · exact resOk_instG hr hI hIt hfind hres0 hparF hxw
          (fun m hm ↦ CoreMode.setG_eq (show (V.n m).idx < CoreMode.GB from hm))
          (fun x hx ↦ by cases x <;> simp [CoreMode.mlSub, hmk] at hx) hsub
          (fun x hx ↦ by rw [CoreMode.cmSub_none hck] at hx; cases hx)
          (fun x hx ↦ by rw [List.isEmpty_iff.mp hgw0, CoreMode.gwFam_nil] at hx; cases hx)
      · rw [← hfpL]
        exact stGlF hglv hgh hD0 (rd_hdr hF.hdr1 ha) haD
    | none =>
    cases hmk : CoreMode.mlK Cf.fn with
    | none =>
      have hgl1 := hgl0
      simp only [CoreMode.glOk, hck, hsk, hmk, Option.isSome_none, Bool.cond_false] at hgl1
      rcases Bool.or_eq_true_iff.mp hgl1 with hgl1 | hal
      · rcases Bool.or_eq_true_iff.mp hgl1 with hgl1 | hgl1
        · -- no ghost: its residuals and linked cells at its valuation
          rw [Bool.and_eq_true, Bool.and_eq_true] at hgl1
          obtain ⟨⟨hgl1, -⟩, hgw0⟩ := hgl1
          refine ⟨e.σ, hB, fun hxw ↦ ?_, ?_, fun c j hc ↦ ?_⟩
          · exact resOk_inst hr hI hIt hfind hres0 hmk hsk hck (List.isEmpty_iff.mp hgw0) hparF hxw
          · rw [← hfpL]
            exact glF_inst hr hI hIt hfind hpN hLk hgl1 hF.hdr1 _
          · rw [List.isEmpty_iff.mp hgw0] at hc; cases hc
        · -- its ghost words its own parameter words
          rw [Bool.and_eq_true] at hgl1
          obtain ⟨hgle, hgs⟩ := hgl1
          have hng : CoreMode.ngB Cf.fn = true := by
            simp only [CoreMode.gwSlots, Bool.and_eq_true] at hgs; exact hgs.2
          refine ⟨CoreMode.setG e.σ (Cf.H.sig.gw.map fun x ↦ (r.img.read (x.1.addrW (CoreMode.vw e.σ))).getD 0),
            CoreMode.honB_setG hB hng, fun hxw ↦ ?_, fun d b k h ↦ ?_, CoreMode.gwR_setG hgs⟩
          · exact resOk_instG hr hI hIt hfind hres0 hparF hxw
              (fun m hm ↦ CoreMode.setG_eq (show (V.n m).idx < CoreMode.GB from hm))
              (fun x hx ↦ by cases x <;> simp [CoreMode.mlSub, hmk] at hx)
              (fun x hx ↦ by cases x <;> simp [CoreMode.stSub, hsk] at hx)
              (fun x hx ↦ by rw [CoreMode.cmSub_none hck] at hx; cases hx)
              (fun x hx ↦ gwFam_inst hr hI hIt hfind (fun v hv ↦ CoreMode.setG_eq hv) hng (CoreMode.gwR_setG hgs) hx)
          · rw [List.isEmpty_iff.mp hgle] at h; cases h
      · -- a loop callee of `anyLink`: its ghost word its caller's frame address
        simp only [CoreMode.alGl, Bool.and_eq_true, Nat.beq_eq] at hal
        obtain ⟨⟨⟨hany, hgh⟩, hng⟩, hgw0⟩ := hal
        have hnp : Cf.fn.params.length < CoreMode.GB := by
          have := hng
          simp only [CoreMode.ngB, Bool.and_eq_true, Nat.blt_eq] at this
          exact this.1.1
        obtain ⟨a, hglF⟩ := alGlF_inst hr hI hIt hfind hpN hLk hany hF.hdr1 hgh hnp
        refine ⟨CoreMode.setG e.σ [ofK (Parameters.g ^ a)], CoreMode.honB_setG hB hng, fun hxw ↦ ?_, ?_,
          fun c j hc ↦ by rw [List.isEmpty_iff.mp hgw0] at hc; cases hc⟩
        · exact resOk_instG hr hI hIt hfind hres0 hparF hxw
            (fun m hm ↦ CoreMode.setG_eq (show (V.n m).idx < CoreMode.GB from hm))
            (fun x hx ↦ by cases x <;> simp [CoreMode.mlSub, hmk] at hx)
            (fun x hx ↦ by cases x <;> simp [CoreMode.stSub, hsk] at hx)
            (fun x hx ↦ by rw [CoreMode.cmSub_none hck] at hx; cases hx)
            (fun x hx ↦ by rw [List.isEmpty_iff.mp hgw0, CoreMode.gwFam_nil] at hx; cases hx)
        · rw [← hfpL]
          exact hglF
    | some k =>
      -- the ghost family: its ghost word the caller's entries table
      have hgl1 := hgl0
      simp only [CoreMode.glOk, hck, hsk, hmk, Option.isSome_none, Option.isSome_some, Bool.cond_false,
        Bool.cond_true, CoreMode.mlGl, Option.any_some, Bool.and_eq_true, decide_eq_true_eq, Nat.beq_eq] at hgl1
      obtain ⟨⟨⟨hglv, hgh⟩, hng⟩, hgw0⟩ := hgl1
      obtain ⟨gw, hsub, hglF⟩ := CoreMode.FnReg.mlLoops_ok _ (CoreMode.lookup_memL hmk) hr _ hI e.σ bufs kids
        (by rw [find_name' hfind]; exact hIt) _ (by rw [find_name' hfind]; exact hfind) hmk hF.hdr1
      refine ⟨CoreMode.setG e.σ gw, CoreMode.honB_setG hB hng, fun hxw ↦ ?_, ?_,
        fun c j hc ↦ by rw [List.isEmpty_iff.mp hgw0] at hc; cases hc⟩
      · exact resOk_instG hr hI hIt hfind hres0 hparF hxw
          (fun m hm ↦ CoreMode.setG_eq (show (V.n m).idx < CoreMode.GB from hm)) hsub
          (fun x hx ↦ by cases x <;> simp [CoreMode.stSub, hsk] at hx)
          (fun x hx ↦ by rw [CoreMode.cmSub_none hck] at hx; cases hx)
          (fun x hx ↦ by rw [List.isEmpty_iff.mp hgw0, CoreMode.gwFam_nil] at hx; cases hx)
      · rw [← hfpL]
        exact hglF Cf rfl hglv hgh
  refine ⟨⟨e.pre ++ e.es, vs, rd, by rw [hfn]; exact hw, ?_⟩, fun es0 vs0 hw0 a p hl hpa ↦ ?_,
    fun hneed es0 vs0 hw0 p r0 rs hl ↦ ?_, hparF,
    fun es0 vs0 hw0 v hv ↦ ?_, fun es0 vs0 hw0 k hk ↦ ?_, fun es0 vs0 hw0 i0 c q s0 hc htk hs0 ↦ ?_,
    fun es0 vs0 hw0 i0 c q s0 hc htk hs0 htg0 t hte ↦ ?_, ?_,
    fun es0 vs0 hw0 e0 he0 ↦ ?_, fun es0 vs0 hw0 i0 c hc hi0 off oc od q S hoff hoc hod hq hfetch hso hS ↦ ?_,
    fun hmX ↦ hroot ?_⟩
  · -- the events hold: the instance is a node of the valid tree
    rcases insts_good (P := coreProgram) (rd := rd) _ _ _ hH.valid e.I hI with ⟨args, rets, hv⟩ | ⟨f', σ', hph⟩
    · rw [hIt] at hv
      obtain ⟨fn', hfind, -, es', vs', hw', -, hh', -⟩ := hv
      rw [hE.find, Option.some.injEq] at hfind
      subst hfind
      rw [hw, Memory.Out.ret.injEq] at hw'
      obtain ⟨rfl, -⟩ := hw'
      exact hh'
    · rw [hIt] at hph; cases hph
  · -- a pointer at its cell
    rw [hfn, hw, Memory.Out.ret.injEq] at hw0
    obtain ⟨rfl, rfl⟩ := hw0
    have hmem := Bridge.walk_atomS (σ := e.σ) Cf.fn.body (by rw [hfn, hw]; exact hl)
    have hc := hptr _ hmem
    simp only [CoreMode.ptrCellB, hpa, Bool.and_eq_true, Option.isNone_iff_eq_none, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨hx, hidx⟩, h2⟩, h3⟩ := hc
    have hloc : Cf.X.locAt p.idx = cellJ j p := by
      rw [← hx0]
      exact Bridge.locAt_ofData (List.all_eq_true.mpr hlocs) hx hidx
    have hnamed : p ∈ namedOf (coreOf j).params (e.pre ++ e.es) vs := by
      unfold namedOf
      exact List.mem_append_left _ (List.mem_append_right _
        (List.mem_flatMap.mpr ⟨_, hl, by simpa [Ev.uses] using ptrOf_uses hpa⟩))
    have := hF.val p hnamed h2 h3
    rw [hloc, ← hfpL]
    simpa [CoreMode.Rd, addressOfIndex, pow_add] using this
  · -- a frame run's pointer, its first value's cell's address
    rw [hfn, hw, Memory.Out.ret.injEq] at hw0
    obtain ⟨rfl, rfl⟩ := hw0
    have hmem := Bridge.walk_atomS (σ := e.σ) Cf.fn.body (by rw [hfn, hw]; exact hl)
    simp only [CoreMode.faOkB, hneed, Bool.not_true, Bool.false_or, List.all_eq_true] at hfa0
    have hc := hfa0 _ hmem
    simp only [CoreMode.faCellB, Bool.and_eq_true, Option.isNone_iff_eq_none, decide_eq_true_eq] at hc
    obtain ⟨hx, hidx⟩ := hc
    have hloc : Cf.X.locAt r0.idx = cellJ j r0 := by
      rw [← hx0]
      exact Bridge.locAt_ofData (List.all_eq_true.mpr hlocs) hx hidx
    rw [hloc, ← hfpL]
    exact hF.addr (p, r0) (List.mem_filterMap.mpr ⟨_, hl, rfl⟩)
  · -- a returned value at its cell
    rw [hfn, hw, Memory.Out.ret.injEq] at hw0
    obtain ⟨rfl, rfl⟩ := hw0
    have hc := hrc _ (Bridge.walk_retS _ (by rw [hfn]; exact hw))
    simp only [CoreMode.retCellB, List.all_eq_true] at hc
    have hc := hc v hv
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨hx, hidx⟩, h2⟩, h3⟩ := hc
    have hloc : Cf.X.locAt v.idx = cellJ j v := by
      rw [← hx0]
      exact Bridge.locAt_ofData (List.all_eq_true.mpr hlocs) hx hidx
    have hnamed : v ∈ namedOf (coreOf j).params (e.pre ++ e.es) vs := List.mem_append_right _ hv
    have := hF.val v hnamed h2 h3
    rw [hloc, ← hfpL]
    simpa [CoreMode.Rd, addressOfIndex, pow_add] using this
  · -- its returned values after its parameters
    rw [hfn, hw, Memory.Out.ret.injEq] at hw0
    obtain ⟨rfl, rfl⟩ := hw0
    obtain ⟨args, rets, hv⟩ := inst_valid' hr hI hIt
    have hv' := hv
    obtain ⟨fn', hfind, hargs, es', vs', hw', hrets, -, -⟩ := hv'
    have hfe : fn' = e.fn := Option.some.inj (hfind.symm.trans hE.find)
    rw [hfe, hw, Memory.Out.ret.injEq] at hw'
    obtain ⟨rfl, rfl⟩ := hw'
    rw [hfe, ← hfn] at hargs
    have hnm : e.I.t.name = "main" → e.I.fp = 0 := fun hm ↦ hfpL.trans (hroot ((B2C.idx_one_iff hj).mpr hm))
    obtain ⟨-, -, -, -, -, hrr⟩ := B2C.inst_runs B2C.b2Hyps hr.name hH hXh.covers (e.I.t.total B2C.fs + 1) e.I hI
      (Nat.lt_succ_self _) hnm args rets (by rw [hIt]; exact hv)
    subst hargs hrets
    have := hrr k (by simpa using hk)
    rw [← hfpL]
    simpa [CoreMode.Rd, addressOfIndex, pow_add] using this
  · -- a call's callee frame
    rw [hfn, hw, Memory.Out.ret.injEq] at hw0
    obtain ⟨rfl, rfl⟩ := hw0
    obtain ⟨kfp, hk, hq, h0, h1, -⟩ := hJC.site _ _ hw i0 c q s0 hc htk (by rw [hXA]; exact hs0)
    have hkid := (hF.kid i0 c kfp hc hk).2.2.1
    have hret := kid_rets hr hI hIt hE.find hw hc hk htk
    refine ⟨kfp, ?_, ?_, ?_, fun k hk' ↦ ?_, fun k hk' ↦ ?_⟩
    · rw [← hfpL]; simpa [CoreMode.Rd, Bridge.cellAt, addressOfIndex, pow_add] using hq
    · simpa [CoreMode.Rd, Bridge.cellAt, addressOfIndex, pow_add] using h0
    · rw [← hfpL]; simpa [CoreMode.Rd, Bridge.cellAt, addressOfIndex, pow_add] using h1
    · simpa [CoreMode.Rd, addressOfIndex, pow_add] using hkid k hk'
    · have := hret k hk'
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk', Option.getD_some] at this
      simpa [CoreMode.Rd, addressOfIndex, pow_add] using this
  · -- a dispatch's target cell: its callee's entry
    rw [hfn, hw, Memory.Out.ret.injEq] at hw0
    obtain ⟨rfl, rfl⟩ := hw0
    obtain ⟨kfp, -, -, -, -, htgt⟩ := hJC.site _ _ hw i0 c q s0 hc htk (by rw [hXA]; exact hs0)
    rw [← hXA, hAX _ _ hj] at hte
    obtain ⟨c', hc', hce⟩ := ctxOf_ent hte
    rw [hAX _ _ hc', hce] at htgt
    rw [← hfpL]
    simpa [CoreMode.Rd, Bridge.cellAt, addressOfIndex, pow_add] using htgt htg0

  · -- what its jumps read
    rw [← hx0, ← hc0]
    simp only [Nat.blt_eq] at hj1
    have hJT := B2C.jumpTables_cover hH.toHonest hXh.covers hr.name
    rw [← hfpL]
    have hwb : walk e.σ (coreOf j).body = .ret (e.pre ++ e.es) vs := by rw [hc0, hfn]; exact hw
    -- a selector used by a top-level atom before it: at its cell
    have hselU : ∀ x, (CoreMode.cellB j x = true ∧ (x ∈ (coreOf j).params ∨ ∃ a, (a ∈ ([] : List Atom) ∨
        Ev.atom a ∈ e.pre ++ e.es) ∧ x ∈ Memory.atomUses a)) →
        CoreMode.Rd r.img e.I.fp ((Bridge.ctxOf j).locAt x.idx) = some (e.σ x) := by
      rintro x ⟨hc, hsel⟩
      simp only [CoreMode.cellB, Bool.and_eq_true, Option.isNone_iff_eq_none, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨hx, hidx⟩, h2⟩, h3⟩ := hc
      have hloc : (Bridge.ctxOf j).locAt x.idx = cellJ j x := Bridge.locAt_ofData (List.all_eq_true.mpr hlocs) hx hidx
      have hnamed : x ∈ namedOf (coreOf j).params (e.pre ++ e.es) vs := by
        unfold namedOf
        rcases hsel with hp | ⟨a, ha, hu⟩
        · exact List.mem_append_left _ (List.mem_append_left _ hp)
        rcases ha with ha | ha
        · cases ha
        exact List.mem_append_left _ (List.mem_append_right _
          (List.mem_flatMap.mpr ⟨_, ha, by simpa [Ev.uses] using hu⟩))
      have := hF.val x hnamed h2 h3
      rw [hloc]
      simpa [CoreMode.Rd, addressOfIndex, pow_add] using this
    refine Bridge.jumpF_of hj1 (fun h ↦ hfpL.trans (hroot h)) hj0 (List.all_eq_true.mpr hlocs) hF (by rw [hc0, hfn]; exact hw)
      (End.jtHolds_of hJT) hJT (fun x arms hm ↦ ?_) (fun x fs args rets hm ↦ ?_)
    · have hnl : CoreMode.loopBC Cf.fn = false := by
        cases hl : CoreMode.loopBC Cf.fn
        · rfl
        · exact absurd (hc0 ▸ hm) (CoreMode.loopBC_noMatch hl)
      simp only [hnl, Bool.or_false] at hbody hselB
      simp only [CoreMode.bodyCore, Bool.and_eq_true] at hbody
      obtain ⟨hc, hu⟩ := Bridge.selGo_sound [] _ (hc0 ▸ hselB) (hc0 ▸ hbody.2) hwb x arms hm
      exact hselU x ⟨hc, Or.inr hu⟩
    · have hnl : CoreMode.loopBC Cf.fn = false := by
        cases hl : CoreMode.loopBC Cf.fn
        · rfl
        · exact absurd (hc0 ▸ hm) (CoreMode.loopBC_noDsp hl)
      simp only [hnl, Bool.or_false] at hbody hselB
      simp only [CoreMode.bodyCore, Bool.and_eq_true] at hbody
      exact hselU x (Bridge.selGoD_sound [] _ (hc0 ▸ hselB) (hc0 ▸ hbody.2) hwb x fs args rets hm)

  · -- the events hold on the reference: the tree is valid on it
    rw [hfn, hw, Memory.Out.ret.injEq] at hw0
    obtain ⟨rfl, rfl⟩ := hw0
    rcases insts_good (P := coreProgram) _ _ _ (hXh.covers.valid hH.toHonest) e.I hI with ⟨args, rets, hv⟩ |
      ⟨f', σ', hph⟩
    · rw [hIt] at hv
      obtain ⟨fn', hfind, -, es', vs', hw', -, hh', -⟩ := hv
      rw [hE.find, Option.some.injEq] at hfind
      subst hfind
      rw [hw, Memory.Out.ret.injEq] at hw'
      obtain ⟨rfl, -⟩ := hw'
      exact hh' e0 he0
    · rw [hIt] at hph; cases hph
  · -- a loop's tail call, its next frame
    rw [hfn, hw, Memory.Out.ret.injEq] at hw0
    obtain ⟨rfl, rfl⟩ := hw0
    have hfm := End.fnOf_mem hj0
    have hlenf : (fnOf j).code.length = (fnOf j).instructionCount :=
      CompiledFunction.length_code (CompiledFunction.wellChunked_of_mem hfm)
    have hX : Cf.X = Bridge.ctxOf j := hx0.symm
    rw [hX] at hoff hfetch hso
    have hcode := Bridge.jump_of_fetch hfm (by rw [hlenf]; exact hoff) hoc hod hq hfetch
    simp only [Nat.blt_eq] at hj1
    rw [← hfpL]
    exact Bridge.tailF_of (by omega) hj0 hF hc hi0 hcode hso hS
  · -- `main`'s frame
    rw [← hx0] at hmX
    simpa [Bridge.ctxOf, Bridge.AlignCtx.ofData] using hmX

end

end LeanVM.Guest.EndExec
