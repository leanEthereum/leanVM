/-
  LeanVM.Guest.Backend.Complete.FrameCalls

  The call-like statements on the path.
-/

module

public import LeanVM.Guest.Backend.Complete.FrameStmts
public import LeanVM.Guest.Backend.Complete.FrameHW

/-!
# Calls on the path

`StmtW` for a call (`stmtW_call`) and a conditional call into another function (`stmtW_callIf`):
the statement's flush and `emit`, the operands' cells, the next frame pointer `nfp` (its word the
callee frame `g^kf[i]` of the call's index `i`), the entry cell, the condition; its words are the
call's instructions on the frame words (`FrameHW`'s `callPre_segW`, `callRets_segW`, `jw_of`), the
callee frame holding the header and arguments and, after an entered call, the returns (`AgKids`).
-/

namespace LeanVM.Guest.Backend.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- The memories `Ag` hold the frame words below the frame size (`AgOf`'s first part). -/
def AgOwn (I : Inst) (Ag : Val → (ℕ → E) → (ℕ → E × E) → (κ : ℕ) → MemoryImage κ → Prop) : Prop :=
  ∀ σ' Ψ kh κ (L : MemoryImage κ), Ag σ' Ψ kh κ L → ∀ n < I.size,
    L.read (addressOfIndex (I.fp + n)) = some (fwd I.hdr ⟨patchT I Ψ σ', kh⟩ n)

/-- The memories `Ag` hold the path's callee frames (`AgOf`'s `FrameOK.kid` and third part): call
`i` of `cl` at the callee frame `I.kf[i]` has its header `kh i` and its arguments (and a registered
loop helper's self pointer), an entered call its returns. -/
def AgKids (ctx : Backend.Ctx) (I : Inst)
    (Ag : Val → (ℕ → E) → (ℕ → E × E) → (κ : ℕ) → MemoryImage κ → Prop) (cl : List Call) : Prop :=
  ∀ σ' Ψ kh κ (L : MemoryImage κ), Ag σ' Ψ kh κ L → ∀ (i : ℕ) (c : Call) (kfp : ℕ),
    cl[i]? = some c → I.kf[i]? = some kfp →
    L.read (addressOfIndex (kfp + 0)) = some (kh i).1 ∧
    L.read (addressOfIndex (kfp + 1)) = some (kh i).2 ∧
    (∀ k (hk : k < c.args.length), L.read (addressOfIndex (kfp + (2 + k))) = some (σ' c.args[k])) ∧
    (((ctx.loops[c.f]?).any (·.registered)) = true →
      L.read (addressOfIndex (kfp + (2 + c.args.length))) = some (ofK (addressOfIndex kfp))) ∧
    (c.taken = true → ∀ k (hk : k < c.rets.length),
      L.read (addressOfIndex (kfp + (2 + c.args.length + k))) = some (σ' c.rets[k]))

section Prims

variable {ctx : Backend.Ctx} {I : Inst} {C : (ℕ → E) → Prop} {st : St}

/-- `mapM_cellOf_fat` with the cells below the next free one. -/
theorem mapM_cellOf_lt (hok : I.Ok) {ok : V → Prop} : ∀ (l : List V) (st : St)
    (C : (ℕ → E) → Prop), VW I C st ok → (∀ v ∈ l, ok v) →
    FAt ctx I C st (l.mapM cellOf) (fun cs C' st' => st'.locs = st.locs ∧ st'.rest = st.rest ∧
      cs.length = l.length ∧ (∀ i (hi : i < cs.length) (hl : i < l.length),
        2 ≤ cs[i] ∧ cs[i] < st'.next ∧ ∀ Ψ, C' Ψ → Ψ cs[i] = I.σ l[i]) ∧ KeepB C C' st.next)
  | [], _, C, _, _ => by
      rw [List.mapM_nil]
      exact FAt.pure ⟨rfl, rfl, rfl, fun i hi => absurd hi (by simp), KeepB.refl C _⟩
  | v :: l, st, C, hv, hk => by
      rw [List.mapM_cons]
      refine FAt.bind (cellOf_fat v hok hv (hk v List.mem_cons_self))
        fun c st₁ C₁ hs₁ hn₁ _ ⟨c2, clt, hlo₁, hr₁, hwc, hk₁⟩ => ?_
      refine FAt.bind (mapM_cellOf_lt hok l st₁ C₁ (hv.step hs₁ hn₁ hlo₁)
        fun v hv' => hk v (List.mem_cons_of_mem _ hv'))
        fun cs st₂ C₂ hs₂ hn₂ _ ⟨hlo₂, hr₂, hlen, hcs, hk₂⟩ => ?_
      refine FAt.pure ⟨hlo₂.trans hlo₁, hr₂.trans hr₁, by simp [hlen], fun i hi hl => ?_,
        hk₁.trans hk₂ hn₁⟩
      cases i with
      | zero => exact ⟨c2, lt_of_lt_of_le clt hn₂, fun Ψ hΨ => hwc Ψ (hs₂ Ψ hΨ)⟩
      | succ i => exact hcs i (by simpa using hi) (by simpa using hl)

/-- A loop's count reads the state only, and is some for a registered loop helper only. -/
theorem loopCount_same (f : String) (args : List V) (cells : List Cell) :
    wpP (loopCount f args cells) ctx st fun r st' => st' = st ∧
      (r.isSome = true → ((ctx.loops[f]?).any (·.registered)) = true) := by
  unfold loopCount
  refine wp_bind.mpr (wp_read.mpr ?_)
  split
  · next li hli =>
    by_cases hr : li.registered = true
    · simp only [hr, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      refine wp_bind.mpr (wp_get.mpr ?_)
      split
      · exact wp_pure.mpr ⟨rfl, fun _ => by simp [hli, hr]⟩
      · exact wp_pure.mpr ⟨rfl, fun _ => by simp [hli, hr]⟩
      · exact wp_failP
    · simp only [hr, Bool.not_false, ↓reduceIte]
      refine wp_bind.mpr (wp_pure.mpr (wp_pure.mpr ⟨rfl, fun h => by simp at h⟩))
  · exact wp_pure.mpr ⟨rfl, fun h => by simp at h⟩

theorem loopCount_fat (f : String) (args : List V) (cells : List Cell) :
    FAt ctx I C st (loopCount f args cells) fun r C' st' => C' = C ∧ st' = st ∧
      (r.isSome = true → ((ctx.loops[f]?).any (·.registered)) = true) :=
  FAt.ofSame (wp_mono (loopCount_same f args cells) fun _ st' ⟨h, hr⟩ => by
    subst h
    exact ⟨rfl, rfl, rfl, LocsLe.refl _, rfl, rfl, hr⟩)

/-- A control statement pushed, then the statement's end, the state reached exactly. -/
theorem push_end' {X : PStmt} {R : PUnit → ((ℕ → E) → Prop) → St → Prop}
    (h : COk I C st.next st.scope st.locs → R ⟨⟩ C
      { st with out := st.out.push X, lazy := none, used := [], shift := none }) :
    FBAt ctx I C st (push X >>= fun _ => endStmt) R := fun hc => by
  unfold push endStmt
  exact wp_bind.mpr (wp_modify.mpr (wp_modify.mpr ⟨C, hc.sat, hc.blind, Stronger.refl C, le_rfl,
    LocsLe.refl _, h hc⟩))

/-- A fresh cell's word leaves free the cells below it the constraint left free. -/
theorem blindAt_assign {c o : ℕ} {w : E} (hb : BlindAt C c) (hc : c ≠ o) :
    BlindAt (fun Ψ => C Ψ ∧ Ψ o = w) c := fun Ψ x ⟨h1, h2⟩ =>
  ⟨hb Ψ x h1, by rw [Function.update_of_ne (Ne.symm hc)]; exact h2⟩

end Prims

section Words

local macro "comega" : tactic => `(tactic| ((try simp only [Cell] at *); omega))

variable {κ₀ : ℕ} {Γ : Site κ₀}
  {Ag : Val → (ℕ → E) → (ℕ → E × E) → (κ : ℕ) → MemoryImage κ → Prop} {cl : List Call}
  {ctx : Backend.Ctx} {I : Inst}

/-- **The words of straight-line instructions, then one control statement**, for any path
outcome: the headers `hs` of the control statement at its position. -/
theorem blkW_ops_ctl' (hok : OpOK Γ I Ag cl) {C : (ℕ → E) → Prop} {ops : List PStmt}
    {X : PStmt} {main : Bool} {ss tl : List Stmt} {o : Out} {i₀ : ℕ}
    (hs : ℕ → List (E × E)) (hlen : ∀ pos, (hs pos).length = (calls (outEs o)).length)
    (hW : (∀ h o, PStmt.op h o ∈ ops → o ∈ I.ops) →
      ∀ s ∈ ops, ∃ h o, s = PStmt.op h o ∧ ∀ Ψ, C Ψ → OpW I Ψ o)
    (hX : ∀ Ψ, C Ψ → ∀ σ', I.Same σ' → ∀ (kh : ℕ → E × E) (cs : List Stmt) (pos : ℕ)
      (ks : List (ℕ × ℕ)) (next : List Stmt → List (ℕ × ℕ) → Prop)
      (kj : List (ℕ × ℕ) → E → E → Prop) (kret khalt : Prop),
      (∀ o' ∈ stmtOps X pos, o' ∈ I.ops) → ctrlSplit cs = ctrlSplit (ss ++ tl) →
      KsAt cl I.kf kh i₀ (calls (outEs o)) (hs pos) ks →
      OutK o tl next (if main then khalt else kret) ks →
      wLc Γ I.fp σ' I.hdr ⟨patchT I Ψ σ', kh⟩ (Ag σ' Ψ kh) cl [X] cs pos ks next kj kret khalt) :
    BlkW Γ I main Ag cl C (ops ++ [X]) ss tl o i₀ := by
  refine ⟨fun pos => hs (pos + blockSize ops), fun pos => hlen _,
    fun Ψ hΨ σ' hσ kh cs pos ks next kj kret khalt hbo hcs hks hk => ?_⟩
  rw [wLc_append _ _ _ _ _ _ _ ops [X] (List.cons_ne_nil _ _)]
  have hbo₁ : ∀ o' ∈ blockOps ops pos, o' ∈ I.ops := fun o' ho =>
    hbo o' (by rw [bops_append]; exact List.mem_append_left _ ho)
  refine wLc_ops hok hΨ hσ kh ops (hW fun _ o hm => hbo₁ o (op_mem_blockOps ops pos hm)) pos hbo₁
    cs ks _ _ kret khalt (hX Ψ hΨ σ' hσ kh cs _ ks next kj kret khalt (fun o' ho => hbo o' (by
      rw [bops_append]
      exact List.mem_append_right _ (by simpa [blockOps] using ho))) hcs hks hk)

/-- The cursor at a control statement after a core statement that is not an atom. -/
theorem ctrlSplit_ctl {s : Stmt} (hs : ∀ a, s ≠ .atom a) (cs : List Stmt) :
    ctrlSplit (s :: cs) = some (s, cs) := by
  cases s with
  | atom a => exact absurd rfl (hs a)
  | _ => rfl

/-- **A call on the path**: the statement's flush and `emit`, the arguments' cells, the returns'
cells, the next frame pointer (word `g^kf[i₀]`), the entry (word the callee's entry), the pooled
`1`; its words: the entry, the arguments and the header (the return pc, this frame) written into
the callee frame, the jump, the returns read back. -/
theorem stmtW_call (hok : OpOK Γ I Ag cl) (hI : I.Ok) (hAg : AgOwn I Ag) (hK : AgKids ctx I Ag cl)
    (hkw : ∀ g, I.kw (.entry g) = kwOf Γ (.entry g))
    (hent : ∀ g, kwOf Γ (.entry g) = ofK (addressOfIndex (Γ.ent g)))
    {f : String} {args rets : List V} {rest tl : List Stmt}
    (hu : ∀ v ∈ args ++ rets, v ∉ I.tmps) :
    StmtW Γ Ag cl ctx I (.call f args rets) rest tl := by
  intro C st sc sc' i₀ o hsc _ hw _ _ hcl _ hinv
  simp only [walk1] at hw
  subst hw
  simp only [scopeStmt] at hsc
  have hown := (scopeFlat_inv hsc).choose_spec.2.2.2.2
  have hcp : ∀ (k : ℕ) (d x : V),
      (∀ j < k, ∃ b, (Stmt.call f args rets :: rest)[j]? = some (Stmt.atom b)) →
      (Stmt.call f args rets :: rest)[k]? = some (Stmt.atom (.copy d x)) →
      (sc.live.contains x = true ∨ st.locs[x]? = none) ∧ I.σ d = I.σ x := by
    intro k d x hj hk
    cases k with
    | zero => simp at hk
    | succ k =>
      obtain ⟨b, hb⟩ := hj 0 (Nat.succ_pos _)
      simp at hb
  have hcl0 : cl[i₀]? = some ⟨f, args, rets, true⟩ := by
    have := hcl 0 (by simp [outEs, calls, Ev.call?])
    simpa [outEs, calls, Ev.call?] using this
  have h1K : IsInK (1 : E) := (isInK_iff 1).mpr ⟨1, ofK_one.symm⟩
  refine FBAt.mono (FBAt.and_wp (R := fun _ C' st' =>
    VW I C' st' (fun v => sc'.live.contains v = true) ∧ st'.rest = sc'.rest ∧
    (sc'.retDone = false → RetBlind ctx C') ∧
    (∀ v, st'.locs[v]? ≠ none → st.locs[v]? ≠ none ∨ v ∈ allocsOf (flushSeg st.rest) ∨
      sc'.live.contains v = true) ∧ COk I C' st'.next st'.scope st'.locs ∧
    (Fits I st' → ∃ blk, st'.out.toList = st.out.toList ++ blk ∧
      BlkW Γ I ctx.isMain Ag cl C' blk [.call f args rets] (rest ++ tl)
        (.fall [.call f args rets]) i₀)) ?_ (chainKeep_call' st)) ?_
  rotate_left
  · rintro _ C' st' _ hn _ ⟨⟨h1, h2, h3, h4, hcok, h6⟩, hch⟩
    have hch' : st'.chainIn = none := by rw [hch]; exact hinv.chain
    exact ⟨fun _ _ _ => winv_flat hsc hinv hcok hn h2 h1 h3 h4 hch', hch', h6⟩
  rw [placeStmt]
  simp only [bind_assoc]
  refine FBAt.fat_bind (begin_fat flushSeg_lock hI hsc hinv hcp)
    fun _ st₁ C₁ hs₁ hn₁ hl₁ _ hE₁ ⟨hr₁, hvw₁, hrb₁, hloc₁⟩ => ?_
  refine FBAt.read_bind ?_
  split
  · simp only [bind_assoc]
    exact fun _ => wp_bind.mpr wp_failP
  simp only [bind_assoc]
  refine FBAt.fat_bind (mapM_cellOf_lt hI args st₁ C₁ hvw₁
    fun v hv => hown v (List.mem_append_left _ hv))
    fun las st₂ C₂ hs₂ hn₂ hl₂ _ hE₂ ⟨hlo₂, hr₂, hlen₂, hlas, hkb₂⟩ => ?_
  have hE₂' := hE₁.step hE₂ hs₂ hn₂ hl₂
  refine FBAt.fat_bind (mapM_cellAt_all_fat rets)
    fun lrs st₃ C₃ hs₃ hn₃ hl₃ _ hE₃ ⟨hC₃, hst₃, hlen₃, hlrs⟩ => ?_
  subst hC₃ hst₃
  unfold placeCall
  simp only [bind_assoc]
  refine FBAt.fat_bind (fresh_fat (fun _ => ofK (addressOfIndex (I.kf.getD i₀ 0)))
    (wblind_const _ _)) fun nfp st₄ C₄ hs₄ hn₄ hl₄ _ hE₄ ⟨hnfp, hst₄, hC₄⟩ => ?_
  have hE₄' := hE₂'.step hE₄ hs₄ hn₄ hl₄
  refine FBAt.fat_bind (fresh_fat (fun _ => I.kw (.entry f)) (wblind_const _ _))
    fun entry st₅ C₅ hs₅ hn₅ hl₅ _ hE₅ ⟨hentry, hst₅, hC₅⟩ => ?_
  have hE₅' := hE₄'.step hE₅ hs₅ hn₅ hl₅
  subst hnfp hst₄ hC₄ hentry hst₅ hC₅
  unfold oneCell
  refine FBAt.fat_bind (constCell_fatB (1, 0) (hI.kconst 1 0)
    (le_trans hinv.two (le_trans hn₁ (le_trans hn₂ (le_trans (Nat.le_succ _) (Nat.le_succ _))))))
    fun one st₆ C₆ hs₆ hn₆ hl₆ _ hE₆ ⟨ho2, hon, hlo₆, hr₆, hoΨ, hkb₆⟩ => ?_
  have hE₆' := hE₅'.step hE₆ hs₆ hn₆ hl₆
  refine FBAt.fat_bind takeHints_fat fun hints st₇ C₇ hs₇ hn₇ hl₇ _ hE₇ ⟨hC₇, hst₇⟩ => ?_
  have hE₇' := hE₆'.step hE₇ hs₇ hn₇ hl₇
  subst hC₇ hst₇
  refine FBAt.fat_bind (loopCount_fat f args las)
    fun loop st₈ C₈ hs₈ hn₈ hl₈ hcok₈ hE₈ ⟨hC₈, hst₈, hloop⟩ => ?_
  have hE₈' := hE₇'.step hE₈ hs₈ hn₈ hl₈
  subst hC₈ hst₈
  refine push_end' fun hc => ?_
  have hC61 : ∀ Ψ, C₈ Ψ → C₁ Ψ := fun Ψ h => hs₂ Ψ (hs₆ Ψ h).1.1
  have hlo : st₆.locs = st₁.locs := hlo₆.trans hlo₂
  have hn16 : st₁.next ≤ st₆.next :=
    le_trans hn₂ (le_trans (Nat.le_succ _) (le_trans (Nat.le_succ _) hn₆))
  refine ⟨hvw₁.step hC61 hn16 hlo, hr₆.trans (hr₂.trans hr₁),
    fun hr => RetBlind.keep (hrb₁ hr) (le_trans hinv.abi hn₁) fun c hc' hb => ?_,
    fun v hv => (hloc₁ v (by rw [← hlo]; exact hv)).elim Or.inl fun h => Or.inr (Or.inl h),
    hc, fun hF => ?_⟩
  · have hc3 : c < st₃.next := lt_of_lt_of_le hc' hn₂
    exact hkb₆ c (Nat.lt_succ_of_lt (Nat.lt_succ_of_lt hc3))
      (blindAt_assign (blindAt_assign (hkb₂ c hc' hb) (Nat.ne_of_lt hc3))
        (Nat.ne_of_lt (Nat.lt_succ_of_lt hc3)))
  obtain ⟨ops, hops, hopsW⟩ := hE₈'
  have hF₈ : Fits I { st₆ with pending := #[] } := ⟨hF.1, hF.2⟩
  have hsz : st₆.next ≤ I.size := hF.1
  have hn56 : st₃.next + 1 + 1 ≤ st₆.next := hn₆
  refine ⟨ops ++ [.call hints ⟨f, st₃.next, st₃.next + 1, one, las, lrs, loop, false⟩],
    by have hops' : st₆.out.toList = st.out.toList ++ ops := hops
       simp [hops'], ?_⟩
  refine blkW_ops_ctl' hok (fun pos => [(Γ.tgt (pos + (callPre ⟨f, st₃.next, st₃.next + 1, one, las, lrs, loop,
      false⟩).length + 1), ofK (addressOfIndex I.fp))])
    (fun _ => by simp [outEs, calls, Ev.call?]) (hopsW hF₈)
    fun Ψ hΨ σ' hσ kh cs pos ks next kj kret khalt hXo hcs hks hk => ?_
  obtain ⟨-, hks⟩ := hks
  obtain ⟨⟨kfp, hks0, hkf⟩, -, hkh⟩ := hks 0 (by simp [outEs, calls, Ev.call?])
  simp only [Nat.add_zero, List.getD_cons_zero] at hks0 hkf hkh
  obtain ⟨ks', rfl⟩ : ∃ ks', ks = (i₀, kfp) :: ks' := by
    cases ks with
    | nil => simp at hks0
    | cons p ks' => simp only [List.getElem?_cons_zero, Option.some.injEq] at hks0; exact ⟨ks', by rw [hks0]⟩
  have hcs' : ctrlSplit cs = some (.call f args rets, rest ++ tl) := by rw [hcs]; rfl
  have hr : Rds (Ag σ' Ψ kh) I.fp I.size (fwd I.hdr ⟨patchT I Ψ σ', kh⟩) :=
    fun κ L hL n hn => hAg σ' Ψ kh κ L hL n hn
  have hΨ5 := hs₆ Ψ hΨ
  have hkfp : I.kf.getD i₀ 0 = kfp := by simp [List.getD_eq_getElem?_getD, hkf]
  have hset : LOp.set (st₃.next + 1) (.entry f) ∈ I.ops := hXo _ (by simp [stmtOps, callPre])
  have hjmp : LOp.jump one (st₃.next + 1) st₃.next ∈ I.ops := hXo _ (by simp [stmtOps])
  have hfpo : LOp.deref st₃.next 1 0 .fp ∈ I.ops := hXo _ (by simp [stmtOps, callPre])
  have hnfp2 : 2 ≤ st₃.next := le_trans hinv.two (le_trans hn₁ hn₂)
  have hetc : ¬ I.tc (st₃.next + 1) := not_tc_of hI hset (by simp [opCells]) fun _ h => nomatch h
  have hntc : ¬ I.tc st₃.next := not_tc_of hI hfpo (by simp [opCells]) fun _ h => nomatch h
  have hotc : ¬ I.tc one := not_tc_of hI hjmp (by simp [opCells]) fun _ h => nomatch h
  have hfo : fwd I.hdr ⟨patchT I Ψ σ', kh⟩ one = 1 :=
    (fwd_patchT ho2 hotc).trans ((hoΨ Ψ hΨ).trans word_one)
  have hfe : fwd I.hdr ⟨patchT I Ψ σ', kh⟩ (st₃.next + 1) = ofK (addressOfIndex (Γ.ent f)) :=
    (fwd_patchT (by comega) hetc).trans (hΨ5.2.trans ((hkw f).trans (hent f)))
  have hfn : fwd I.hdr ⟨patchT I Ψ σ', kh⟩ st₃.next = ofK (addressOfIndex kfp) :=
    (fwd_patchT hnfp2 hntc).trans (hΨ5.1.2.trans (by rw [hkfp]))
  have hlas' : ∀ k (hk : k < las.length) (hk' : k < args.length), las[k] < I.size ∧
      fwd I.hdr ⟨patchT I Ψ σ', kh⟩ las[k] = σ' args[k] := by
    intro k hk hk'
    obtain ⟨h2, hlt, hw⟩ := hlas k hk hk'
    have ho : LOp.deref st₃.next (argBase + k) las[k] .cell ∈ I.ops := hXo _ (by
      simp only [stmtOps, callPre, List.mem_append, List.mem_map]
      exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl ⟨(las[k], k),
        List.mk_mem_zipIdx_iff_getElem?.mpr (by simp), rfl⟩)))))
    have htc : ¬ I.tc las[k] := not_tc_of hI ho (by simp [opCells]) fun p h => by
      have := (LOp.deref.inj h).2.1
      simp [argBase] at this
    refine ⟨by comega, (fwd_patchT h2 htc).trans ((hw Ψ hΨ5.1.1).trans ?_)⟩
    exact (hσ _ (hu _ (List.mem_append_left _ (List.getElem_mem _)))).symm
  have hlrs' : ∀ k (hk : k < lrs.length) (hk' : k < rets.length), lrs[k] < I.size ∧
      fwd I.hdr ⟨patchT I Ψ σ', kh⟩ lrs[k] = σ' rets[k] := by
    intro k hk hk'
    obtain ⟨h2, hlt, hw⟩ := hvw₁ rets[k] (.cell lrs[k])
      (hown _ (List.mem_append_right _ (List.getElem_mem _))) (by rw [← hlo₂]; exact hlrs k hk hk')
    have ho : LOp.deref st₃.next (argBase + las.length + k) lrs[k] .cell ∈ I.ops := hXo _ (by
      simp only [stmtOps, callRets, List.mem_append, List.mem_map]
      exact Or.inr ⟨(lrs[k], k), List.mk_mem_zipIdx_iff_getElem?.mpr (by simp), rfl⟩)
    have htc : ¬ I.tc lrs[k] := not_tc_of hI ho (by simp [opCells]) fun p h => by
      have := (LOp.deref.inj h).2.1
      simp [argBase] at this
    simp only [locBase] at h2 hlt
    refine ⟨by comega, (fwd_patchT h2 htc).trans ((hw Ψ (hC61 Ψ hΨ)).trans ?_)⟩
    exact (hσ _ (hu _ (List.mem_append_right _ (List.getElem_mem _)))).symm
  simp only [wLc, wS, hcs']
  refine ⟨callPre_segW hr (by comega) (by comega) (by comega)
    ((fwd_patchT (by comega) hetc).trans (hΨ5.2.trans (hkw f))) hfn
    (fun k hk => ⟨(hlas' k hk (hlen₂ ▸ hk)).1, fun κ L hL => by
      rw [(hlas' k hk (hlen₂ ▸ hk)).2]
      exact (hK σ' Ψ kh κ L hL i₀ _ kfp hcl0 hkf).2.2.1 k (hlen₂ ▸ hk)⟩)
    (fun hl κ L hL => by
      rw [hfn]
      have := (hK σ' Ψ kh κ L hL i₀ _ kfp hcl0 hkf).2.2.2.1 (hloop hl)
      simpa [hlen₂, argBase] using this)
    (fun κ L hL => by
      have := hK σ' Ψ kh κ L hL i₀ _ kfp hcl0 hkf
      rw [hkh] at this
      exact ⟨this.1, this.2.1⟩) (by simp),
    jw_of hr (by comega) (by comega) (by comega) (by rw [hfo]; exact h1K)
      (by rw [hfe]; exact (isInK_iff _).mpr ⟨_, rfl⟩)
      (by rw [hfn]; exact (isInK_iff _).mpr ⟨_, rfl⟩)
      (fun h0 => absurd (hfo ▸ h0) one_ne_zero) fun _ => ?_⟩
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine ⟨trivial, ⟨⟨_, hcl0, rfl, rfl⟩, hfe, hfn, hkh⟩, callRets_segW hr (by comega) hfn
    fun k hk => ⟨(hlrs' k hk (hlen₃ ▸ hk)).1, fun κ L hL => ?_⟩, ?_⟩
  · rw [(hlrs' k hk (hlen₃ ▸ hk)).2]
    have := (hK σ' Ψ kh κ L hL i₀ _ kfp hcl0 hkf).2.2.2.2 rfl k (hlen₃ ▸ hk)
    simpa [argBase, hlen₂] using this
  · have := hk (rest ++ tl) rfl
    simpa [outEs, calls, Ev.call?] using this

end Words

end
end LeanVM.Guest.Backend.Complete
