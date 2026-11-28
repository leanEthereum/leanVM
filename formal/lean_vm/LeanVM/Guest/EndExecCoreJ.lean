/-
  LeanVM.Guest.EndExecCoreJ

  What a frame of the honest tree reads at its jumps: the selectors at their cells, the chained
  `match`es' targets, the fixed cells, conditions and table targets.
-/

module

public import LeanVM.Guest.CoreMode.WalkS
public import LeanVM.Guest.CoreMode.SelNest
public import LeanVM.Guest.Bridge.JumpCells
public import LeanVM.Guest.Bridge.JumpCells.All
public import LeanVM.Guest.Bridge.ProgAlKeys
public import LeanVM.Guest.EndExecLoop
public import LeanVM.Guest.EndExecChain

/-!
# The honest frames' jumps

`selGo_selM`, `selGo_selD`, `selGo_reach`: a `match`'s or a dispatch's selector, on a path that
reaches it, is at its cell and used by an atom on the path. `chain_taken`: a chained `match`'s target
cell, on the arm the path takes. `jumpF_of`: for function `j` at frame `fp` holding what its check
reads (`FrameHolds`), the jump table in memory, what its jumps read (`CoreMode.JumpF`).
`ctxOf_ent`: a callee a context names by entry is the compiled function entered there. The bus
era's `EndExecCore` but its main theorem, unchanged.
-/

namespace LeanVM.Guest.Bridge

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

public section

section Walk

variable {σ : Val}

/-- **`selGo`'s top-level selectors**: on a path that returns, the selector `x` of each top-level `match` is at its
cell and used by an atom seen before it or on the path. -/
theorem selGo_selM {j : ℕ} {ps : List V} {B : List Stmt} {σ : Val} : ∀ (seen : List Atom) (ss : List Stmt) {es : List Ev} {vs : List V},
    CoreMode.selGo j ps B seen ss = true → ss.all CoreMode.topOk = true → walk σ ss = .ret es vs →
    ∀ x arms, Stmt.match_ x arms ∈ ss →
      CoreMode.cellB j x = true ∧ ∃ a, (a ∈ seen ∨ Ev.atom a ∈ es) ∧ x ∈ Memory.atomUses a
  | _, [], _, _, _, _, _, _, _, hm => absurd hm List.not_mem_nil
  | seen, .atom b :: ss, es, vs, h, ht, hw, x, arms, hm => by
    simp only [CoreMode.selGo] at h
    simp only [List.all_cons, Bool.and_eq_true] at ht
    rw [walk_atom_cons] at hw
    obtain ⟨es', hw', rfl⟩ := pre_eq_ret hw
    rcases List.mem_cons.mp hm with h' | hm
    · cases h'
    obtain ⟨hc, a, ha, hu⟩ := selGo_selM (b :: seen) ss h ht.2 hw' x arms hm
    refine ⟨hc, a, ?_, hu⟩
    rcases ha with ha | ha
    · rcases List.mem_cons.mp ha with rfl | ha
      · exact Or.inr (by simp)
      · exact Or.inl ha
    · exact Or.inr (by simp [ha])
  | seen, .match_ y arms' :: ss, es, vs, h, ht, hw, x, arms, hm => by
    simp only [CoreMode.selGo, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true] at h
    obtain ⟨⟨⟨hc, ⟨a, ha, hu⟩⟩, -⟩, h⟩ := h
    simp only [List.all_cons, Bool.and_eq_true] at ht
    rcases List.mem_cons.mp hm with h' | hm
    · cases h'
      exact ⟨hc, a, Or.inl ha, hu⟩
    · rw [walk] at hw
      rcases seq_eq_ret hw with ⟨es1, es2, -, h2, rfl⟩ | h1
      · obtain ⟨hc', a', ha', hu'⟩ := selGo_selM seen ss h ht.2 h2 x arms hm
        exact ⟨hc', a', ha'.imp id (List.mem_append_right _), hu'⟩
      · exact absurd h1 (CoreMode.walk1_noRetP _ (CoreMode.noRet_of_topOk ht.1) _ _)
  | seen, .ite c z n :: ss, es, vs, h, ht, hw, x, arms, hm => by
    simp only [CoreMode.selGo, Bool.and_eq_true] at h
    obtain ⟨-, h⟩ := h
    simp only [List.all_cons, Bool.and_eq_true] at ht
    rcases List.mem_cons.mp hm with h' | hm
    · cases h'
    · rw [walk] at hw
      rcases seq_eq_ret hw with ⟨es1, es2, -, h2, rfl⟩ | h1
      · obtain ⟨hc', a', ha', hu'⟩ := selGo_selM seen ss h ht.2 h2 x arms hm
        exact ⟨hc', a', ha'.imp id (List.mem_append_right _), hu'⟩
      · exact absurd h1 (CoreMode.walk1_noRetP _ (CoreMode.noRet_of_topOk ht.1) _ _)
  | seen, .ret vs' :: ss, es, vs, h, ht, hw, x, arms, hm => by
    simp only [CoreMode.selGo, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hm with h' | hm
    · cases h'
    · exact (CoreMode.noMatch_mem h.1 (mem_stmtsOf hm)).elim
  | seen, .call f args rets :: ss, es, vs, h, ht, hw, x, arms, hm => by
    simp only [CoreMode.selGo] at h
    simp only [List.all_cons, Bool.and_eq_true] at ht
    rw [walk_call_cons] at hw
    obtain ⟨es', hw', rfl⟩ := pre_eq_ret hw
    rcases List.mem_cons.mp hm with h' | hm
    · cases h'
    obtain ⟨hc, a, ha, hu⟩ := selGo_selM seen ss h ht.2 hw' x arms hm
    exact ⟨hc, a, ha.imp id (fun h ↦ by simp [h]), hu⟩
  | seen, .callIf c f args :: ss, es, vs, h, ht, hw, x, arms, hm => by
    simp only [CoreMode.selGo] at h
    simp only [List.all_cons, Bool.and_eq_true] at ht
    rw [walk_callIf_cons] at hw
    obtain ⟨es', hw', rfl⟩ := pre_eq_ret hw
    rcases List.mem_cons.mp hm with h' | hm
    · cases h'
    obtain ⟨hc, a, ha, hu⟩ := selGo_selM seen ss h ht.2 hw' x arms hm
    exact ⟨hc, a, ha.imp id (fun h ↦ by simp [h]), hu⟩
  | seen, .dispatch y fs' args' rets' :: ss, es, vs, h, ht, hw, x, arms, hm => by
    simp only [CoreMode.selGo, Bool.and_eq_true] at h
    simp only [List.all_cons, Bool.and_eq_true] at ht
    rcases List.mem_cons.mp hm with h' | hm
    · cases h'
    obtain ⟨f, -, es', rfl, hw'⟩ := CoreMode.walk_dispatch_ret hw
    obtain ⟨hc, a, ha, hu⟩ := selGo_selM seen ss h.2 ht.2 hw' x arms hm
    exact ⟨hc, a, ha.imp id (fun h ↦ by simp [h]), hu⟩

/-- **`selGo`'s dispatches' selectors**: on a path that returns, the selector `x` of each `dispatch` of the body is
at its cell, a parameter or used by an atom seen before it or on the path. -/
theorem selGo_selD {j : ℕ} {ps : List V} {B : List Stmt} {σ : Val} : ∀ (seen : List Atom) (ss : List Stmt) {es : List Ev} {vs : List V},
    CoreMode.selGo j ps B seen ss = true → ss.all CoreMode.topOk = true → walk σ ss = .ret es vs →
    ∀ x fs args rets, Stmt.dispatch x fs args rets ∈ stmtsOf ss →
      CoreMode.cellB j x = true ∧ (x ∈ ps ∨ ∃ a, (a ∈ seen ∨ Ev.atom a ∈ es) ∧ x ∈ Memory.atomUses a)
  | _, [], _, _, _, _, _, _, _, _, _, hm => by simp [stmtsOf] at hm
  | seen, s :: ss, es, vs, h, ht, hw, x, fs, args, rets, hm => by
    simp only [List.all_cons, Bool.and_eq_true] at ht
    rw [stmtsOf, List.mem_cons, List.mem_append] at hm
    -- a nested dispatch: none (`topOk`)
    have hsub : Stmt.dispatch x fs args rets ∉ stmtsSub s := fun hs ↦ by
      have h1 := ht.1
      cases s with
      | ret _ | call _ _ _ | dispatch _ _ _ _ | atom _ | callIf _ _ _ => simp [stmtsSub] at hs
      | _ =>
        simp only [CoreMode.topOk, Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false] at h1
        exact absurd rfl (h1.2 _ hs)
    rcases hm with hm | hm | hm
    · -- the head
      subst hm
      simp only [CoreMode.selGo, Bool.and_eq_true, Bool.or_eq_true, List.contains_iff_mem, decide_eq_true_eq,
        List.any_eq_true] at h
      obtain ⟨⟨hc, hsel⟩, -⟩ := h
      rcases hsel with hp | ⟨a, ha, hu⟩
      · exact ⟨hc, Or.inl hp⟩
      · exact ⟨hc, Or.inr ⟨a, Or.inl ha, hu⟩⟩
    · exact absurd hm hsub
    · -- the tail
      cases s with
      | atom b =>
        simp only [CoreMode.selGo] at h
        rw [walk_atom_cons] at hw
        obtain ⟨es', hw', rfl⟩ := pre_eq_ret hw
        obtain ⟨hc, hr⟩ := selGo_selD (b :: seen) ss h ht.2 hw' x fs args rets hm
        refine ⟨hc, hr.imp id fun ⟨a, ha, hu⟩ ↦ ⟨a, ?_, hu⟩⟩
        rcases ha with ha | ha
        · rcases List.mem_cons.mp ha with rfl | ha
          · exact Or.inr (by simp)
          · exact Or.inl ha
        · exact Or.inr (by simp [ha])
      | ret _ =>
        simp only [CoreMode.selGo, Bool.and_eq_true] at h
        have := List.all_eq_true.mp h.2 _ hm
        simp at this
      | match_ _ _ | ite _ _ _ =>
        simp only [CoreMode.selGo, Bool.and_eq_true] at h
        rw [walk] at hw
        rcases seq_eq_ret hw with ⟨es1, es2, -, h2, rfl⟩ | h1
        · obtain ⟨hc, hr⟩ := selGo_selD seen ss h.2 ht.2 h2 x fs args rets hm
          exact ⟨hc, hr.imp id fun ⟨a, ha, hu⟩ ↦ ⟨a, ha.imp id (List.mem_append_right _), hu⟩⟩
        · exact absurd h1 (CoreMode.walk1_noRetP _ (CoreMode.noRet_of_topOk ht.1) _ _)
      | call f a r =>
        simp only [CoreMode.selGo] at h
        rw [walk_call_cons] at hw
        obtain ⟨es', hw', rfl⟩ := pre_eq_ret hw
        obtain ⟨hc, hr⟩ := selGo_selD seen ss h ht.2 hw' x fs args rets hm
        exact ⟨hc, hr.imp id fun ⟨a, ha, hu⟩ ↦ ⟨a, ha.imp id (fun h ↦ by simp [h]), hu⟩⟩
      | callIf c f a =>
        simp only [CoreMode.selGo] at h
        rw [walk_callIf_cons] at hw
        obtain ⟨es', hw', rfl⟩ := pre_eq_ret hw
        obtain ⟨hc, hr⟩ := selGo_selD seen ss h ht.2 hw' x fs args rets hm
        exact ⟨hc, hr.imp id fun ⟨a, ha, hu⟩ ↦ ⟨a, ha.imp id (fun h ↦ by simp [h]), hu⟩⟩
      | dispatch y fs' args' rets' =>
        simp only [CoreMode.selGo, Bool.and_eq_true] at h
        obtain ⟨f, -, es', rfl, hw'⟩ := CoreMode.walk_dispatch_ret hw
        obtain ⟨hc, hr⟩ := selGo_selD seen ss h.2 ht.2 hw' x fs args rets hm
        exact ⟨hc, hr.imp id fun ⟨a, ha, hu⟩ ↦ ⟨a, ha.imp id (fun h ↦ by simp [h]), hu⟩⟩

/-- **A reached `match`'s selector**: at a cursor of the body from which the path's events are its last ones, a
`match`'s selector is at its cell and used by an atom on the path (`selGo_selM` at the top level, `sel_nested` in a
top-level `ite`'s branch; `selGo` leaves none elsewhere). -/
theorem selGo_reach {j : ℕ} {σ : Val} {body : List Stmt} {ps : List V}
    (hsel : CoreMode.selGo j ps body [] body = true) (htop : body.all CoreMode.topOk = true)
    {zs : Zip} {x : V} {arms : List (List Stmt)} {ss : List Stmt} {pre es : List Ev} {vs : List V}
    (hz : ZOk body zs) (hc : zs.cur = .match_ x arms :: ss) (hw : walk σ body = .ret (pre ++ es) vs)
    (hp : walk σ zs.pos = .ret es vs) :
    CoreMode.cellB j x = true ∧ ∃ a, Ev.atom a ∈ pre ++ es ∧ x ∈ Memory.atomUses a := by
  rcases CoreMode.zok_cases hz hc with hm | ⟨t, c, u, hu, Q, hsub, hB, hpos⟩ | ⟨u, hu, w, hw', hs⟩
  · obtain ⟨hcl, a, ha, hua⟩ := selGo_selM [] body hsel htop hw x arms hm
    exact ⟨hcl, a, ha.resolve_left List.not_mem_nil, hua⟩
  · cases u with
    | ite c0 z n => exact CoreMode.sel_nested hsel htop hw hB hsub rfl (hpos ▸ hp)
    | match_ y as =>
      refine (CoreMode.selGo_arms hsel y as hu x arms (subBlock_sub (s := .match_ y as) (c := c) ?_)).elim
      rw [hsub]; simp
    | atom _ | call _ _ _ | callIf _ _ _ | dispatch _ _ _ _ | ret _ =>
      have : (Q ++ Stmt.match_ x arms :: ss).length = 0 := by rw [← hsub]; rfl
      simp at this
  · exact (CoreMode.selGo_deep hsel u hu w hw' x arms hs).elim

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
    (hsel : ∀ zs x arms ss pre es' vs', ZOk (coreOf j).body zs → zs.cur = .match_ x arms :: ss →
      walk σ (coreOf j).body = .ret (pre ++ es') vs' → walk σ zs.pos = .ret es' vs' →
      CoreMode.Rd L fp ((ctxOf j).locAt x.idx) = some (σ x))
    (hdsel : ∀ x fs args rets, Stmt.dispatch x fs args rets ∈ stmtsOf (coreOf j).body →
      CoreMode.Rd L fp ((ctxOf j).locAt x.idx) = some (σ x)) :
    CoreMode.JumpF L (ctxOf j) (coreOf j).body fp σ := by
  have hrd : ∀ o, CoreMode.Rd L fp o = cellAt L fp o := fun o ↦ by
    simp [CoreMode.Rd, cellAt, addressOfIndex, pow_add]
  have hd := JumpCells.jcData_all j (by omega) (by have : nFns = fn_count% := rfl; omega)
  unfold jcData jcDataD at hd
  simp only [Bool.and_eq_true] at hd
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hstat, harms⟩, -⟩, -⟩, hextra⟩, hblock⟩, -⟩, -⟩, -⟩ := hd
  have hcont := Check.cont_of (End.winOk_of (by omega) hj2)
  have hstatB : ∀ {o : ℕ} {w : PC}, (o, w) ∈ (plumbOf j).stat →
      cellAt L fp o = some (w.word fp) ∧ (∀ a b, w = .k a b → a < 2 ^ 64 ∧ b < 2 ^ 64) := by
    intro o w hm
    have hb := List.all_eq_true.mp hstat _ hm
    simp only [cellIn, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hb
    refine ⟨hF.stat _ hm hb.1.1 hb.1.2, fun a b hw' ↦ ?_⟩
    subst hw'
    simpa only [Bool.and_eq_true, Nat.blt_eq] using hb.2
  refine ⟨?zero, ?nz, ?self, ?pcw, ?cond, ?arm, hsel, fun _ _ _ x fs args rets hm ↦ hdsel x fs args rets hm⟩
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


end

end LeanVM.Guest.EndExec
