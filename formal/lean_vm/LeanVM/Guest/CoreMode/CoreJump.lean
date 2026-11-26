/-
  LeanVM.Guest.CoreMode.CoreJump

  The core route's frame interface, its second part: the frame's hints, jumps and calls.
-/

module

public import LeanVM.Guest.CoreMode.CoreFacts
public import LeanVM.Guest.CoreMode.PairJumpC
public import LeanVM.Guest.CoreMode.PairCallIf

/-!
# Jumps and calls

The second part of `frameSpec_core` (`CoreSound.lean`): the hints' heap cells and flows, a jump's target by the frame walk's tables (`core_tgt`), a conditional call skipped (`core_jfall`) or taken (`core_jtaken`), a dispatch through the jump table (`core_jtd`), and a call's callee frame (`slotGetL_call`, `evM_mode`).
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Bridge (AlignCtx Zip ZOk fwdJ flowAtom isaFlowHint stmtsOf stmtsSub zok_stmts Pairs fwdOff_eq
  walk_ret_cons walk_atom_cons pre_eq_ret)
open LeanVM.Guest.Check (getF)
open LeanVM.Prover.Exec (Hint St Ctx Fine Moves StepOk HintOk refMem maxCells runOp Mem gpow_inj
  Mem.get_of_written OpModed OnRef Agree)
open LeanVM.Guest.Check (getF)
open LeanVM.Guest.Mode (Names written_of_get written_mono names_inj opOfOff RefOk HintIn Holds entryAbs
  FrameSpec Out HintsAt ResAt RetAll RetHolds HW RW MonoVal BsVal BaseVal IdxVal stOf CodeOk)

@[expose] public section

variable {κ : ℕ}

/-! ## The frame interface -/

theorem refOk_fp {M : ℕ → E} {s s' : St} (h : s'.fp = s.fp) {op : Prover.Exec.Op} (hr : RefOk M s op) :
    RefOk M s' op := by
  unfold RefOk at hr ⊢
  rw [h]
  exact hr

theorem lt_maxCells_63 {x : ℕ} (h : x < maxCells) : x < 2 ^ 63 := by
  unfold maxCells at h
  omega

theorem compiles_heap {loc : ℕ → ℕ} {hc : Core.Hint} {h : Prover.Exec.Hint} (hco : Bridge.compiles loc hc h = true)
    {p : V} {off len : ℕ} (hd : hintHeap hc = some (p, off, len)) : isaHeap h = some (loc p.idx, off, len) := by
  cases hc with
  | witness s d =>
    cases d with
    | stack => simp [hintHeap] at hd
    | heap p' off' len' =>
      simp only [hintHeap, Option.some.injEq, Prod.mk.injEq] at hd
      obtain ⟨rfl, rfl, rfl⟩ := hd
      cases h <;> simp only [Bridge.compiles, Bool.false_eq_true] at hco
      simp only [Bool.and_eq_true, beq_iff_eq] at hco
      obtain ⟨⟨⟨-, rfl⟩, rfl⟩, rfl⟩ := hco
      rfl
  | bits _ _ _ d | bitsExp _ _ d | digitsExp _ _ _ _ _ _ d | windowsExp _ _ _ _ d =>
    cases d with
    | stack => simp [hintHeap] at hd
    | heap p' off' len' =>
      simp only [hintHeap, Option.some.injEq, Prod.mk.injEq] at hd
      obtain ⟨rfl, rfl, rfl⟩ := hd
      cases h <;> simp only [Bridge.compiles, Bool.false_eq_true] at hco
      cases ‹Prover.Exec.BitsDest› <;> simp_all [Bridge.destOk, isaHeap]
  | _ => simp [hintHeap] at hd

/-- **A flow hint's atom wrote its cells** once the hints at the pc ran: the ISA hint it pairs with
wrote them from its pointer's exponent, the pointer at the frame cell holding the atom's. -/
theorem flow_wrk {img : MemoryImage κ} (hκ : κ ≤ 28) {X : AlignCtx} {C : Ctx} {hs : List Prover.Exec.Hint}
    {s s1 : St} (e1 : hs.foldlM (Prover.Exec.runHint C) s = .ok s1) (hs0 : Fine (refMem img) s)
    (hm : Moves (refMem img) s s1) {σ : Val} {as : List Atom}
    (hpairs : List.Forall₂ (Pairs X) (as.filter flowAtom) (hs.filter isaFlowHint)) {a : Atom} {y : K}
    (ha : a ∈ as) (hfa : flowAtom a = true)
    (hr : ∀ p, ptrOf a = some p → Rd img s.fp (X.locAt p.idx) = some (σ p)) (hw : Writes σ a y) :
    WrK s1.mem y := by
  obtain ⟨h, hh, hc, rfl, hco⟩ := forall₂_mem hpairs a (List.mem_filter.mpr ⟨ha, hfa⟩)
  obtain ⟨p, off, len, hd, k, hk, rfl⟩ := hw
  obtain ⟨b, hget, hwr⟩ := hints_heap hs ⟨hs0.agree.wf, hs0.dl⟩ e1 h (List.mem_filter.mp hh).1
    (compiles_heap hco hd)
  have hlt := written_lt hm.fine (written_of_get hget)
  rw [hm.fp.symm] at hget
  have hval : ofK (g ^ b) = σ p := rd_get hκ hm.fine (by unfold maxCells at hlt; omega)
    (by rw [hm.fp]; exact hr p (by simp [ptrOf, hd])) hget
  refine ⟨b + off + k, ?_, written_lt hm.fine (hwr k hk), hwr k hk⟩
  rw [cellAt, ← hval, limb_ofK]
  simp [addressOfIndex, pow_add, mul_assoc]

theorem heapK_params {Cf : CFun} (hk : HeapK Cf) : Cf.fn.params = (List.range Cf.fn.params.length).map V.n := by
  cases hk with
  | m1 hok _ _ _ _ _ =>
    unfold heapOk at hok; simp only [Bool.and_eq_true] at hok
    rw [List.range_eq_range']; exact paramsN_eq _ 0 hok.1.1.1
  | c hok _ _ _ _ => exact heapOkC_params hok

theorem fwdOff_spec {X : AlignCtx} {i t o : ℕ} (h : X.fwdOff i t = some o) : X.entry + i < t ∧ o = t - X.entry := by
  unfold AlignCtx.fwdOff at h
  simp only [Bool.cond_eq_ite, Nat.blt_eq] at h
  split_ifs at h with h1
  · rw [Exec.natSeq_eq] at h
    exact ⟨by simpa using h1, (Option.some.inj h).symm⟩

theorem siteAt_spec {X : AlignCtx} {q : ℕ} {args rets : List V} {s : B2C.Site} (h : X.siteAt q args rets = some s) :
    getF X.sites q = some s ∧ s.args.length = args.length ∧ s.rets.length = rets.length := by
  unfold AlignCtx.siteAt at h
  split at h
  · rename_i s' hs'
    simp only [Bool.cond_eq_ite, Bool.and_eq_true, beq_iff_eq] at h
    split_ifs at h with hh
    cases h
    exact ⟨hs', by rw [hh.1]; simp, by rw [hh.2]; simp⟩
  · cases h

theorem siteAt_eq {X : AlignCtx} {q : ℕ} {args rets : List V} {s : B2C.Site} (h : X.siteAt q args rets = some s) :
    getF X.sites q = some s ∧ s.args = args.map (·.idx) ∧ s.rets = rets.map (·.idx) := by
  unfold AlignCtx.siteAt at h
  split at h
  · rename_i s' hs'
    simp only [Bool.cond_eq_ite, Bool.and_eq_true, beq_iff_eq] at h
    split_ifs at h with hh
    cases h
    exact ⟨hs', hh.1, hh.2⟩
  · cases h

theorem entOk_spec {X : AlignCtx} {t : ℕ} {f : String} (h : X.entOk t f = true) : getF X.ents t = some f := by
  unfold AlignCtx.entOk at h
  split at h
  · rename_i f' hf'
    rw [hf', beq_iff_eq.mp h]
  · cases h

theorem jumpCallOk_spec {Cf : CFun} {oc od of t : ℕ} {f : String} (h : jumpCallOk Cf (.jump oc od of) = true)
    (hpt : Cf.X.pcAt od = some t) (hent : getF Cf.X.ents t = some f) :
    ¬ (Cf.frame.entry ≤ t ∧ t < Cf.frame.entry + Cf.frame.len) ∧ t < 2 ^ 30 ∧ Cf.X.selfAt of = false ∧
      ∃ G s, Cf.frame.sigs.get t = some G ∧ getF Cf.X.sites of = some s ∧ s.r < 2 ^ 30 ∧
        callOkC Cf G f s.args.length s.rets.length = true := by
  simp only [jumpCallOk, hpt, hent, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
  obtain ⟨-, ⟨⟨⟨hout, ht⟩, hsf⟩, -⟩, h⟩ := h
  refine ⟨fun ⟨h1, h2⟩ ↦ by simp [h1, h2] at hout, ht, hsf, ?_⟩
  split at h
  · rename_i G s hG hs
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨G, s, hG, hs, h.1, h.2⟩
  · cases h

/-- **A `JUMP` through its call site's target cell** goes through no `0`, no pc, no table target cell,
from a cell not the own frame's. -/
theorem jumpCallOk_dsp {Cf : CFun} {oc od of : ℕ} (h : jumpCallOk Cf (.jump oc od of) = true) {s : B2C.Site}
    (hs : getF Cf.X.sites of = some s) (he : s.tgt = od) :
    od ≠ 0 ∧ Cf.X.pcAt od = none ∧ getF Cf.X.arms od = none ∧ Cf.X.selfAt of = false := by
  simp only [jumpCallOk, Bool.and_eq_true] at h
  have h1 := h.1
  simp only [dspNo, hs, he, Nat.beq_refl, Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true',
    Option.isNone_iff_eq_none] at h1
  obtain ⟨⟨⟨h0, hp⟩, ha⟩, hsf⟩ := h1
  exact ⟨fun e ↦ by simp [e] at h0, hp, ha, hsf⟩

/-- A call's site has no dispatch target cell its jump's. -/
theorem jumpCallOk_tgt {Cf : CFun} {oc od of t : ℕ} (h : jumpCallOk Cf (.jump oc od of) = true)
    (hpt : Cf.X.pcAt od = some t) : ∀ s, getF Cf.X.sites of = some s → s.tgt ≠ od := fun s hs he ↦ by
  have := (jumpCallOk_dsp h hs he).2.1
  rw [hpt] at this; cases this

theorem jumpCallOk_next {Cf : CFun} {oc od of t : ℕ} {f : String} (h : jumpCallOk Cf (.jump oc od of) = true)
    (hpt : Cf.X.pcAt od = some t) (hent : getF Cf.X.ents t = some f) : Cf.X.nextAt of = false := by
  simp only [jumpCallOk, hpt, hent, Bool.and_eq_true, Bool.not_eq_true'] at h
  exact h.2.1.2

theorem mapM_base_lt {n : ℕ} : ∀ (bs : List (Mode.Base × ℕ)) (cb : List (ℕ × ℕ)), bs.mapM baseOfMono = some cb →
    (∀ b ∈ bs, ∀ o, b.1 = .fr o → o - 2 < n) → ∀ b ∈ cb, b.1 < n
  | [], cb, h, _, b, hb => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; cases hb
  | (x, e) :: bs, cb, h, hl, b, hb => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨y, hy, ys, hys, rfl⟩ := h
    rcases List.mem_cons.mp hb with rfl | hb
    · cases x with
      | fr o =>
        simp only [baseOfMono] at hy
        split_ifs at hy
        cases hy
        exact hl (.fr o, e) List.mem_cons_self o rfl
      | hp q d => simp [baseOfMono] at hy
    · exact mapM_base_lt bs ys hys (fun b hb ↦ hl b (List.mem_cons_of_mem _ hb)) b hb

theorem monoC_bases_lt {G : Mode.Sig} {n : ℕ} {ent : Bool} {m : Mode.Mono} {c : CCell}
    (hm : monoS G n ent m = true) (hc : monoC m = some c) : ∀ b ∈ c.bases, b.1 < n := by
  obtain ⟨-, cb, hcb, rfl⟩ := monoC_spec hc
  refine mapM_base_lt m.bs cb hcb fun b hb o ho ↦ ?_
  have h := List.all_eq_true.mp hm b hb
  rw [ho] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.2
/-! ## The shape -/

theorem bodyC_ctrl {body : List Stmt} (h : bodyCore body = true) : ∀ s ∈ stmtsOf body, ctrlOk s = true := by
  simp only [bodyCore, Bool.and_eq_true, List.all_eq_true] at h
  exact h.1

theorem matchLens_mem {body : List Stmt} {x : V} {arms : List (List Stmt)} (h : Stmt.match_ x arms ∈ stmtsOf body) :
    (x.idx, arms.length) ∈ matchLens body :=
  List.mem_filterMap.mpr ⟨_, h, rfl⟩

theorem armsCover_at {X : AlignCtx} {e : ℕ} {ml : List (ℕ × ℕ)} {a : ℕ × ℕ} {ts : List ℕ}
    (h : armsCover X e ml a ts = true) {p : ℕ × ℕ} (hp : p ∈ ml) (hpa : p.1 = a.1) {j : ℕ} (hj : j < p.2) :
    ∃ t, getF X.jt (a.2 + j) = some t ∧ e ≤ t ∧ t < 2 ^ 30 ∧ t - e ∈ ts := by
  have h1 := List.all_eq_true.mp h p hp
  simp only [hpa, Nat.beq_refl, Bool.not_true, Bool.false_or, List.all_eq_true, List.mem_range] at h1
  have h2 := h1 j hj
  split at h2
  · rename_i t ht
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at h2
    exact ⟨t, ht, h2.1.1, h2.1.2, h2.2⟩
  · cases h2

theorem tgtGo_at {Cf : CFun} {ml : List (ℕ × ℕ)} : ∀ {n : ℕ} {code : List OffsetInstruction},
    tgtGo Cf ml n code = true → ∀ {i k oc od of : ℕ}, code[i]? = some (.jump oc od of) →
      Cf.frame.tgt.get (n + i) = some k →
      (dspSite Cf.X od of = true ∧ dspJ Cf k od of = true) ∨ (dspSite Cf.X od of = false ∧
      od ≠ 0 ∧ Cf.X.pcAt od = none ∧ Cf.frame.calls.get k = none ∧ ∃ a ts, getF Cf.X.arms od = some a ∧
        Cf.frame.arms.get k = some ts ∧ armsCover Cf.X Cf.frame.entry ml a ts = true)
  | _, [], _, _, _, _, _, _, h, _ => by simp at h
  | n, ins :: code, h, i, k, oc, od, of, hi, ht => by
    simp only [tgtGo, Bool.and_eq_true] at h
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      rw [Nat.add_zero] at ht
      have h1 := h.1
      rw [ht] at h1
      simp only at h1
      cases hd : dspSite Cf.X od of
      · rw [hd, Bool.cond_false] at h1
        simp only [Bool.and_eq_true, Bool.not_eq_true', Option.isNone_iff_eq_none] at h1
        obtain ⟨⟨⟨h0, hpc⟩, hcl⟩, h2⟩ := h1
        split at h2
        · rename_i a ts ha hts
          exact .inr ⟨rfl, fun e ↦ by simp [e] at h0, hpc, hcl, a, ts, ha, hts, h2⟩
        · cases h2
      · rw [hd, Bool.cond_true] at h1
        exact .inl ⟨rfl, h1⟩
    | succ i =>
      exact tgtGo_at h.2 (by simpa using hi) (by rw [show n + 1 + i = n + (i + 1) by omega]; exact ht)

/-- A `JUMP` the frame walk reads no table for is no dispatch's. -/
theorem tgtGo_none {Cf : CFun} {ml : List (ℕ × ℕ)} : ∀ {n : ℕ} {code : List OffsetInstruction},
    tgtGo Cf ml n code = true → ∀ {i oc od of : ℕ}, code[i]? = some (.jump oc od of) →
      Cf.frame.tgt.get (n + i) = none → dspSite Cf.X od of = false
  | _, [], h, _, _, _, _, hi, _ => by simp at hi
  | n, ins :: code, h, i, oc, od, of, hi, ht => by
    simp only [tgtGo, Bool.and_eq_true] at h
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      rw [Nat.add_zero] at ht
      have h1 := h.1
      rw [ht] at h1
      simp only [Bool.not_eq_true'] at h1
      exact h1
    | succ i =>
      exact tgtGo_none h.2 (by simpa using hi) (by rw [show n + 1 + i = n + (i + 1) by omega]; exact ht)

/-! ## Jumps -/

/-- **A jump's hints' atoms and reads** write only what is written once its hints ran. -/
theorem jump_events {img : MemoryImage κ} (hκ : κ ≤ 28) {X : AlignCtx} {H : HCert} {C : Ctx}
    {sigOf : String → HSig} {rd : Reader} {ws0 : List E}
    {hs : List Prover.Exec.Hint} {s s1 : St} (e1 : hs.foldlM (Prover.Exec.runHint C) s = .ok s1)
    (hs0 : Fine (refMem img) s) (hm : Moves (refMem img) s s1) {σ : Val} {as bs : List Atom}
    (hq : ∀ a ∈ as, flowAtom a = false → stopS H.readT a = false) (hbs : ∀ a ∈ bs, stopS H.readT a = false)
    (hpairs : List.Forall₂ (Pairs X) (as.filter flowAtom) (hs.filter isaFlowHint))
    (hptr : ∀ a ∈ as, ∀ p, ptrOf a = some p → Rd img s.fp (X.locAt p.idx) = some (σ p))
    {pre rest : List Ev} (hrw : ReadsAt sigOf H rd σ ws0 pre ((as ++ bs).map Ev.atom ++ rest))
    (hW : ∀ y, WrittenC sigOf H rd σ ws0 pre y → WrK s.mem y) :
    ∀ y, WrittenC sigOf H rd σ ws0 (pre ++ (as ++ bs).map Ev.atom) y → WrK s1.mem y := by
  have hside : ∀ a ∈ as ++ bs, a ∉ as.filter flowAtom → stopS H.readT a = false := by
    intro a ha hn
    rcases List.mem_append.mp ha with ha | ha
    · cases hfa : flowAtom a
      · exact hq a ha hfa
      · exact absurd (List.mem_filter.mpr ⟨ha, hfa⟩) hn
    · exact hbs a ha
  intro y hy
  rcases written_extendC (fs := as.filter flowAtom) hrw hside hy with h | ⟨a, ha, hwa⟩
  · exact (hW y h).mono hm.le
  · rw [List.mem_filter] at ha
    exact flow_wrk hκ e1 hs0 hm hpairs ha.1 ha.2 (hptr a ha.1) hwa

/-- The head statement a jump steps by, on the core route's shape: a branch, a `match` or a return. -/
theorem head_cases {Cf : CFun} {zs : Zip} (_hzsok : ZOk Cf.fn.body zs)
    (_hctrl : ∀ s ∈ stmtsOf Cf.fn.body, ctrlOk s = true)
    {i oc od of : ℕ} {tabs : List (ℕ × Zip × ℕ)} {r : Option Zip × List (ℕ × Zip)}
    (hh : headStepH Cf.P i oc od of tabs zs = some r) :
    (∃ x fs args rets ss, zs.cur = .dispatch x fs args rets :: ss) ∨
    (∃ c f args ss, zs.cur = .callIf c f args :: ss) ∨ (∃ c zb nb ss, zs.cur = .ite c zb nb :: ss) ∨
      (∃ x arms ss, zs.cur = .match_ x arms :: ss) ∨ (∃ vs ss, zs.cur = .ret vs :: ss) ∨
      ∃ f args rets ss, zs.cur = .call f args rets :: ss := by
  obtain ⟨st, ss, hcur, hna⟩ := headH_stmt hh
  cases st with
  | atom a => exact absurd rfl (hna a)
  | dispatch x fs args rets => exact Or.inl ⟨x, fs, args, rets, ss, hcur⟩
  | callIf c f args => exact Or.inr (Or.inl ⟨c, f, args, ss, hcur⟩)
  | ite c zb nb => exact Or.inr (Or.inr (Or.inl ⟨c, zb, nb, ss, hcur⟩))
  | match_ x arms => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨x, arms, ss, hcur⟩)))
  | ret vs => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨vs, ss, hcur⟩))))
  | call f args rets => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨f, args, rets, ss, hcur⟩))))

theorem headH_match_nz {P : PairCtx} {i oc od of : ℕ} {tabs : List (ℕ × Zip × ℕ)} {zs : Zip}
    {r : Option Zip × List (ℕ × Zip)} {x : V} {arms : List (List Stmt)} {ss : List Stmt}
    (h : headStepH P i oc od of tabs zs = some r) (hz : zs.cur = .match_ x arms :: ss) :
    P.X.nzAt oc = true ∧ P.X.selfAt of = true ∧ ∃ a, getF P.X.arms od = some a := by
  simp only [headStepH, hz] at h
  cases hs : (P.X.nzAt oc && P.X.selfAt of) <;> simp only [hs, Bool.cond_true, Bool.cond_false] at h
  · cases h
  simp only [Bool.and_eq_true] at hs
  refine ⟨hs.1, hs.2, ?_⟩
  cases ha : getF P.X.arms od
  · rw [ha] at h; cases h
  · exact ⟨_, rfl⟩

theorem lookup_mem {α β : Type} [BEq α] [LawfulBEq α] {a : α} {b : β} :
    ∀ {l : List (α × β)}, l.lookup a = some b → (a, b) ∈ l
  | [], h => by simp at h
  | (a', b') :: l, h => by
    simp only [List.lookup] at h
    split at h
    · rename_i hab
      cases h
      rw [beq_iff_eq] at hab
      subst hab
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (lookup_mem h)

/-- A dispatch site's `JUMP`: what `dspSite` says. -/
theorem dspSite_of {X : AlignCtx} {od of : ℕ} {args rets : List V} {s : B2C.Site} (hpc : X.pcAt od = none)
    (hsite : X.siteAt of args rets = some s) (htg : s.tgt = od) (hd0 : od ≠ 0) : dspSite X od of = true := by
  obtain ⟨hs, -, -⟩ := siteAt_spec hsite
  have h0 : Nat.beq od 0 = false := by cases h : Nat.beq od 0 <;> simp_all [Nat.beq_eq]
  simp only [dspSite, hpc, hs, h0, htg, Nat.beq_refl, Option.isNone_none, Bool.not_false, Bool.and_self]

/-- **A dispatch's `JUMP` the walk reads callees for**: its callees' entries `dspPc`, each callee of the
dispatch at its site among them. -/
theorem dsp_at {Cf : CFun} (hcb : (stmtsOf Cf.fn.body).all (dspB Cf) = true) {k od of : ℕ} (hdj : dspJ Cf k od of = true) {x : V}
    {fs : List String} {args rets : List V} {s : B2C.Site} (hst : Stmt.dispatch x fs args rets ∈ stmtsOf Cf.fn.body)
    (hsite : Cf.X.siteAt of args rets = some s) :
    ∃ pcs, Cf.frame.calls.get k = some pcs ∧ Cf.frame.arms.get k = none ∧ Cf.X.selfAt of = false ∧
      Cf.X.nextAt of = false ∧ s.r < 2 ^ 30 ∧ s.tgt = od ∧ (∀ t ∈ pcs, dspPc Cf s t = true) ∧
      ∀ f ∈ fs, ∃ t ∈ pcs, Cf.X.entOk t f = true := by
  obtain ⟨hs, -, -⟩ := siteAt_spec hsite
  simp only [dspJ, Bool.and_eq_true, Bool.not_eq_true', Option.isNone_iff_eq_none] at hdj
  obtain ⟨⟨⟨ha, hsf⟩, hnx⟩, hdj⟩ := hdj
  rw [hs] at hdj
  split at hdj
  · rename_i pcs s' fs' hpcs hs' hfs
    cases hs'
    simp only [Bool.and_eq_true, Nat.beq_eq, decide_eq_true_eq, List.all_eq_true, List.any_eq_true] at hdj
    obtain ⟨⟨⟨htg, hr⟩, hpc⟩, hfs'⟩ := hdj
    have hc := List.all_eq_true.mp hcb _ hst
    simp only [dspB, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Option.isNone_iff_eq_none, beq_iff_eq] at hc
    have hfe : fs' = fs := by
      rcases hc.2 _ (lookup_mem hfs) with h | h
      · rw [hsite] at h; cases h
      · exact h
    subst hfe
    exact ⟨pcs, hpcs, ha, hsf, hnx, hr, htg, hpc, hfs'⟩
  · cases hdj

/-- **A dispatch's target cell holds the picked callee's entry**, by `HonF.tgt`, at a call on the path. -/
theorem honF_dsp {img : MemoryImage κ} {Cf : CFun} {fp : ℕ} {σ : Val} (hσ : HonF img Cf fp σ) {f : String}
    {args rets : List V} {pre es : List Ev}
    {vs : List V} (hb : walk σ Cf.fn.body = .ret (pre ++ Ev.call f args rets :: es) vs) {q : ℕ} {s : B2C.Site}
    (hsite : Cf.X.siteAt q args rets = some s) (htg : s.tgt ≠ 0) {t : ℕ} (he : Cf.X.entOk t f = true) :
    Rd img fp s.tgt = some (ofK (g ^ t)) :=
  hσ.tgt _ _ hb (calls pre).length ⟨f, args, rets, true⟩ q s calls_mid rfl hsite htg t he

/-- **The frame walk's table jumps land at their arms**, of the reference: a `JUMP` the walk reads
a table for is a `match`'s, its target the slot of the arm the selector picks, or a dispatch's, its
target the entry of the callee the path calls. -/
theorem core_tgt {img : MemoryImage κ} {Cf : CFun} {code : List OffsetInstruction}
    (hpair : pairOk Cf.X Cf.H Cf.frame.O Cf.frame.S Cf.fn.body code Cf.d = true)
    (hctrl : ∀ s ∈ stmtsOf Cf.fn.body, ctrlOk s = true) (htgt : tgtOk Cf code = true)
    (hcb : (stmtsOf Cf.fn.body).all (dspB Cf) = true) {fp i : ℕ} {σ : Val} (hσ : HonF img Cf fp σ) {pos : List Stmt} {pre es : List Ev}
    {vs : List V} (hat : pairAt Cf.P Cf.fn.body code Cf.d i = some pos)
    (hb : walk σ Cf.fn.body = .ret (pre ++ es) vs) (hwp : walk σ pos = .ret es vs) :
    TgtOk img Cf.frame code i fp := by
  intro c d f hci cv dv hcv hne hdv pc hpcl hdl kk hk
  rw [tgtOk, Exec.listSeq_eq] at htgt
  obtain ⟨as, bs, z, zs, tabs, r, hpos, hzpos, -, -, -, -, hzsok, hr, -, -, -⟩ := pair_jump hpair hat hci
  rw [hpos, hzpos, ← List.append_assoc, ← List.map_append] at hwp
  obtain ⟨es1, hes1, hes⟩ := walk_atoms_ret hwp
  cases hz : Cf.X.zeroAt c
  swap
  · exact absurd (Option.some.inj ((hσ.jc.zero c hz).symm.trans hcv)).symm hne
  have hpcn : Cf.X.pcAt d = none := by
    rcases tgtGo_at htgt hci (by rw [Nat.zero_add]; exact hk) with ⟨hds, -⟩ | ⟨-, -, hpcn, -⟩
    · simp only [dspSite, Bool.and_eq_true, Option.isNone_iff_eq_none] at hds
      exact hds.1.2
    · exact hpcn
  cases hf : fwdJ Cf.X i c d f
  swap
  · obtain ⟨-, -, t, -, ht, -⟩ := jumpH_fwd hr hz hf
    have ht' : Cf.X.pcAt d = some t := ht
    rw [hpcn] at ht'; cases ht'
  have hh := headH_of hr hz hf
  rcases head_cases hzsok hctrl hh with ⟨x, fs, args, rets, ss, hcur⟩ | ⟨c', f', args', ss, hcur⟩ | hh4
  · -- a dispatch: its target cell the entry of the callee the path calls
    obtain ⟨-, hd0, s, c0, o, hsite, htg, -⟩ := headH_dispatch hh hcur
    have hds := dspSite_of hpcn hsite htg hd0
    rcases tgtGo_at htgt hci (by rw [Nat.zero_add]; exact hk) with ⟨-, hdj⟩ | ⟨hds', -⟩
    swap
    · rw [hds] at hds'; cases hds'
    have hmem : Stmt.dispatch x fs args rets ∈ stmtsOf Cf.fn.body :=
      zok_stmts hzsok (by rw [Zip.pos_head hcur]; exact List.mem_cons_self)
    obtain ⟨pcs, hpcs, harm, -, -, -, -, hpc, hfs⟩ := dsp_at hcb hdj hmem hsite
    refine ⟨fun pcs' h ↦ ?_, fun ts h ↦ by rw [harm] at h; cases h⟩
    rw [hpcs, Option.some.injEq] at h
    subst h
    rw [Zip.pos_head hcur] at hes1
    obtain ⟨f0, hf0, es2, rfl, -⟩ := walk_dispatch_ret hes1
    obtain ⟨t, ht, hte⟩ := hfs f0 hf0
    have hpt := hpc t ht
    simp only [dspPc] at hpt
    split at hpt
    · rename_i f1 hf1
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hpt
      have hrd := honF_dsp hσ (pre := pre ++ (as ++ bs).map Ev.atom) (by rw [hb, hes, List.append_assoc]) hsite
        (by omega) hte
      rw [htg, hdv, Option.some.injEq] at hrd
      subst hrd
      have hgt : (g : K) ^ t = g ^ pc := by simpa using hdl
      have := gpow_lt_inj (by omega) (by unfold pcLim at hpcl; omega) hgt
      rw [← this]
      exact ht
    · cases hpt
  · obtain ⟨-, t, -, ht, -⟩ := headH_callIf hh hcur
    have ht' : Cf.X.pcAt d = some t := ht
    rw [hpcn] at ht'; cases ht'
  rcases hh4 with ⟨cc, zb, nb, ss, hcur⟩ | ⟨x, arms, ss, hcur⟩ | ⟨vs', ss, hcur⟩ |
    ⟨f, args, rets, ss, hcur⟩
  rotate_left 3
  · obtain ⟨-, s0, t, -, -, -, ht, -⟩ := headH_call hh hcur
    have ht' : Cf.X.pcAt d = some t := ht
    rw [hpcn] at ht'; cases ht'
  · obtain ⟨-, -, t, -, -, -, ht, -⟩ := headH_ite hh hcur
    have ht' : Cf.X.pcAt d = some t := ht
    rw [hpcn] at ht'; cases ht'
  · obtain ⟨-, hsfm, -⟩ := headH_match_nz hh hcur
    rcases tgtGo_at htgt hci (by rw [Nat.zero_add]; exact hk) with ⟨-, hdj⟩ | ⟨-, hd0, -, hcl, a, ts0, ha, hts0, hcov⟩
    · simp only [dspJ, Bool.and_eq_true, Bool.not_eq_true'] at hdj
      have hsf2 : Cf.X.selfAt f = true := hsfm
      rw [hdj.1.1.2] at hsf2; cases hsf2
    refine ⟨fun pcs h ↦ by (rw [hcl] at h; cases h), fun ts hts ↦ ?_⟩
    rw [hts0, Option.some.injEq] at hts
    subst hts
    obtain ⟨-, -, hax, -⟩ := jumpH_match hr hcur hz hf ha
    obtain ⟨k0, hk0, hσx, -⟩ := side_arm hcur hes1
    have hmem : Stmt.match_ x arms ∈ stmtsOf Cf.fn.body :=
      zok_stmts hzsok (by rw [Zip.pos_head hcur]; exact List.mem_cons_self)
    obtain ⟨t, hjt, he, ht30, hts⟩ := armsCover_at hcov (matchLens_mem hmem) hax.symm hk0
    have hrd := hσ.jc.arm x arms hmem d a ha hax k0 t hσx hjt
    rw [hrd, Option.some.injEq] at hdv
    subst hdv
    have hgt : (g : K) ^ t = g ^ pc := by simpa using hdl
    have := gpow_lt_inj (by omega) (by unfold pcLim at hpcl; omega) hgt
    exact ⟨t - Cf.frame.entry, hts, by omega⟩
  · obtain ⟨-, -, h01⟩ := headH_ret hh hcur
    have h01' : if Cf.X.main then Cf.X.selfAt f = true ∧ Cf.X.pcAt d = some Cf.X.halt else d = 0 ∧ f = 1 := h01
    have hd0 : d ≠ 0 ∧ Cf.X.pcAt d = none := by
      rcases tgtGo_at htgt hci (by rw [Nat.zero_add]; exact hk) with ⟨hds, -⟩ | ⟨-, hd0, hpn, -⟩
      · simp only [dspSite, Bool.and_eq_true, Bool.not_eq_true', Option.isNone_iff_eq_none] at hds
        exact ⟨fun h ↦ by simp [h] at hds, hds.1.2⟩
      · exact ⟨hd0, hpn⟩
    split at h01'
    · rw [hd0.2] at h01'; cases h01'.2
    · exact absurd h01'.1 hd0.1

/-- **A jump falling through**, its condition cell `0`: the next offset's position, the events since
this offset's its hints' atoms and reads, a branch's condition, atoms writing nothing. -/
theorem core_jfall {img : MemoryImage κ} (hκ : κ ≤ 28) {Cf : CFun} {code : List OffsetInstruction}
    (hpair : pairOk Cf.X Cf.H Cf.frame.O Cf.frame.S Cf.fn.body code Cf.d = true)
    (hctrl : ∀ s ∈ stmtsOf Cf.fn.body, ctrlOk s = true)
    {C : Ctx} {s s1 : St} {i oc od of : ℕ} (hins : code[i]? = some (.jump oc od of)) (hoc : oc < 2 ^ 28)
    (e1 : ((Cf.d.2.2.lookup (Cf.X.entry + i)).getD []).foldlM (Prover.Exec.runHint C) s = .ok s1)
    (hs : Fine (refMem img) s) (hm : Moves (refMem img) s s1) (hc0 : s1.mem.get (s1.fp + oc) = some 0)
    {σ : Val} (hσ : HonF img Cf s.fp σ) {pos : List Stmt} {pre es : List Ev} {vs : List V}
    (hat : pairAt Cf.P Cf.fn.body code Cf.d i = some pos) (hb : walk σ Cf.fn.body = .ret (pre ++ es) vs)
    (hwp : walk σ pos = .ret es vs) {rd : Reader} (hrw : ReadsAt Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) pre es)
    (hW : ∀ y, WrittenC Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) pre y → WrK s.mem y) :
    ∃ pos', pairAt Cf.P Cf.fn.body code Cf.d (i + 1) = some pos' ∧ ∃ evs es', es = evs ++ es' ∧
      walk σ pos' = .ret es' vs ∧ (∀ e ∈ evs, EvM Cf.sigOf rd σ e) ∧
      ∀ y, WrittenC Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) (pre ++ evs) y → WrK s1.mem y := by
  obtain ⟨as, bs, z, zs, tabs, r, hpos, hzpos, hq, hbs, hpairs, -, hzsok, hr, h1, -, -⟩ := pair_jump hpair hat hins
  rw [hpos, hzpos, ← List.append_assoc, ← List.map_append] at hwp
  obtain ⟨es1, hes1, rfl⟩ := walk_atoms_ret hwp
  have hev := jump_events hκ e1 hs hm hq hbs hpairs (fun a ha p hp ↦ hσ.ptr _ _ hb a p
    (List.mem_append_right _ (List.mem_append_left _ (by simp [ha]))) hp)
    (rest := es1) (by simpa [List.append_assoc] using hrw) hW
  have hnz : Cf.X.nzAt oc = true → False := fun h ↦ by
    obtain ⟨w, hw, hw0⟩ := hσ.jc.nz oc h
    exact hw0 (rd_get hκ hm.fine hoc (by rw [hm.fp]; exact hw) hc0).symm
  cases hz : Cf.X.zeroAt oc
  swap
  · have hr0 := jumpH_zero hr hz
    subst hr0
    refine ⟨z.pos, h1 z rfl, as.map Ev.atom, bs.map Ev.atom ++ es1, by simp, ?_, evM_atoms _,
      fun y hy ↦ hev y (by rw [List.map_append, ← List.append_assoc]; exact writtenC_prefix hy)⟩
    rw [hzpos, Bridge.walk_atoms, hes1]
    rfl
  cases hf : fwdJ Cf.X i oc od of
  swap
  · exact absurd (jumpH_fwd hr hz hf).1 (fun h ↦ hnz h)
  have hh := headH_of hr hz hf
  rcases head_cases hzsok hctrl hh with ⟨x, fs, args, rets, ss, hcur⟩ | ⟨c, f, args, ss, hcur⟩ | hh4
  · exact absurd (headH_dispatch hh hcur).1 (fun h ↦ hnz h)
  · obtain ⟨hloc, t, ca, -, -, hca, rfl, -⟩ := headH_callIf hh hcur
    obtain ⟨cs, hcs, hcpos, -⟩ := normG_pos _ _ hca
    rw [Zip.pos_head hcur, hcpos, Bridge.walk_callIf_cons] at hes1
    obtain ⟨es2, hes2, rfl⟩ := pre_eq_ret hes1
    obtain ⟨es3, hes3, rfl⟩ := walk_atoms_ret hes2
    have hcond := hσ.jc.cond _ _ hb c (by simp)
    have hloc' : Cf.X.locAt c.idx = oc := hloc
    rw [hloc'] at hcond
    have hσc : σ c = 0 := (rd_get hκ hm.fine hoc (by rw [hm.fp]; exact hcond) hc0).symm
    refine ⟨ca.pos, h1 ca rfl, (as ++ bs).map Ev.atom ++ [Ev.inK c, Ev.skip f args] ++ cs.map Ev.atom, es3,
      by simp [hσc], hes3, evM_app (evM_app (evM_atoms _) (evM_inK_cons (evM_skip_cons evM_nil))) (evM_atoms _),
      fun y hy ↦ ?_⟩
    have h2 : WrittenC Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ)
        (pre ++ (as ++ bs).map Ev.atom ++ [Ev.inK c] ++ [Ev.skip f args]) y := by
      rcases writtenC_append (a := pre ++ (as ++ bs).map Ev.atom ++ [Ev.inK c] ++ [Ev.skip f args])
          (b := cs.map Ev.atom) (by simpa [List.append_assoc] using hy) with h | ⟨e, he, hwe⟩
      · exact h
      · obtain ⟨b, hb', rfl⟩ := List.mem_map.mp he
        exact absurd hwe (no_writes_of_stopL (hcs b hb'))
    exact hev y (writtenC_noAtom (e := Ev.inK c) (fun a h ↦ by cases h) (fun f a r h ↦ by cases h)
      (writtenC_noAtom (e := Ev.skip f args) (fun a h ↦ by cases h) (fun f a r h ↦ by cases h) h2))
  rcases hh4 with ⟨c, zb, nb, ss, hcur⟩ | ⟨x, arms, ss, hcur⟩ | ⟨vs', ss, hcur⟩ |
    ⟨f, args, rets, ss, hcur⟩
  rotate_left 3
  · exact absurd (headH_call hh hcur).1 (fun h ↦ hnz h)
  · obtain ⟨hloc, -, t, cz, cn, o, -, hcz, -, -, rfl⟩ := headH_ite hh hcur
    obtain ⟨es2, rfl, hes2⟩ := side_ite hcur hes1
    have hcond := hσ.jc.cond _ _ hb c (by simp)
    have hloc' : Cf.X.locAt c.idx = oc := hloc
    rw [hloc'] at hcond
    have hσc : σ c = 0 := (rd_get hκ hm.fine hoc (by rw [hm.fp]; exact hcond) hc0).symm
    simp only [hσc, ↓reduceIte] at hes2
    obtain ⟨evs, es3, rfl, hes3, hevN, hWn⟩ := succ_normC hcz hes2
    refine ⟨cz.pos, h1 cz rfl, (as ++ bs).map Ev.atom ++ Ev.inK c :: evs, es3, by simp, hes3,
      evM_app (evM_atoms _) (evM_inK_cons hevN), fun y hy ↦ ?_⟩
    have h2 := hWn (pre ++ (as ++ bs).map Ev.atom ++ [Ev.inK c]) y (by simpa [List.append_assoc] using hy)
    exact hev y (writtenC_noAtom (fun a h ↦ by cases h) (fun f a r h ↦ by cases h) h2)
  · exact absurd (headH_match_nz hh hcur).1 (fun h ↦ hnz h)
  · exact absurd (headH_ret hh hcur).2.1 (fun h ↦ hnz h)

/-- **A jump taken**, its condition cell nonzero: a return (`od = 0`, `of = 1`, the events past the
position writing what is written once its hints ran), or a jump in the frame, through its own frame
pointer, to the offset of the side the run takes, the events to there its hints' atoms and reads, a
branch's condition, atoms writing nothing. -/
theorem core_jtaken {img : MemoryImage κ} (hκ : κ ≤ 28) {Cf : CFun} {code : List OffsetInstruction}
    (hpair : pairOk Cf.X Cf.H Cf.frame.O Cf.frame.S Cf.fn.body code Cf.d = true)
    (hctrl : ∀ s ∈ stmtsOf Cf.fn.body, ctrlOk s = true)
    (hlen : ∀ o < code.length, Cf.X.entry + o < 2 ^ 30)
    {C : Ctx} {s s1 s' : St} {i oc od of : ℕ} (hins : code[i]? = some (.jump oc od of))
    (hcj : ∀ t f, Cf.X.pcAt od = some t → getF Cf.X.ents t = some f → Cf.X.selfAt of = false)
    (hsf : Cf.X.selfAt of = true) (hdn : ∀ s, getF Cf.X.sites of = some s → s.tgt = od → Cf.X.selfAt of = false)
    (hoc : oc < 2 ^ 28)
    (hod : od < 2 ^ 28)
    (e1 : ((Cf.d.2.2.lookup (Cf.X.entry + i)).getD []).foldlM (Prover.Exec.runHint C) s = .ok s1)
    (hs : Fine (refMem img) s) (hm : Moves (refMem img) s s1) {v : E} (hcv : s1.mem.get (s1.fp + oc) = some v)
    (hv0 : v ≠ 0) (hd : s1.mem.get (s1.fp + od) = some (ofK (g ^ s'.pc))) (hpcs : s'.pc < 2 ^ 30)
    {σ : Val} (hσ : HonF img Cf s.fp σ) {pos : List Stmt} {pre es : List Ev} {vs : List V}
    (hat : pairAt Cf.P Cf.fn.body code Cf.d i = some pos) (hb : walk σ Cf.fn.body = .ret (pre ++ es) vs)
    (hwp : walk σ pos = .ret es vs) {rd : Reader} (hrw : ReadsAt Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) pre es)
    (hW : ∀ y, WrittenC Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) pre y → WrK s.mem y) :
    ((if Cf.X.main then Cf.X.selfAt of = true ∧ Cf.X.pcAt od = some Cf.X.halt else od = 0 ∧ of = 1) ∧
      (∀ e ∈ es, EvM Cf.sigOf rd σ e) ∧
      ∀ y, WrittenC Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) (pre ++ es) y → WrK s1.mem y) ∨
    (Cf.X.selfAt of = true ∧ ∃ o pos', s'.pc = Cf.X.entry + o ∧ i < o ∧
      pairAt Cf.P Cf.fn.body code Cf.d o = some pos' ∧ ∃ evs es', es = evs ++ es' ∧
        walk σ pos' = .ret es' vs ∧ (∀ e ∈ evs, EvM Cf.sigOf rd σ e) ∧
        ∀ y, WrittenC Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) (pre ++ evs) y → WrK s1.mem y) := by
  obtain ⟨as, bs, z, zs, tabs, r, hpos, hzpos, hq, hbs, hpairs, -, hzsok, hr, -, h2, h3⟩ := pair_jump hpair hat hins
  rw [hpos, hzpos, ← List.append_assoc, ← List.map_append] at hwp
  obtain ⟨es1, hes1, rfl⟩ := walk_atoms_ret hwp
  have hev := jump_events hκ e1 hs hm hq hbs hpairs (fun a ha p hp ↦ hσ.ptr _ _ hb a p
    (List.mem_append_right _ (List.mem_append_left _ (by simp [ha]))) hp)
    (rest := es1) (by simpa [List.append_assoc] using hrw) hW
  -- the target pc, a constant one's
  have hpcw : ∀ t, Cf.X.pcAt od = some t → t < 2 ^ 30 → s'.pc = t := fun t ht ht30 ↦ by
    have h := rd_get hκ hm.fine hod (by rw [hm.fp]; exact hσ.jc.pcw od t ht) hd
    have hgt : (g : K) ^ s'.pc = g ^ t := by simpa using congrArg (fun e : E ↦ e.limb 0) h
    exact gpow_lt_inj (by omega) (by omega) hgt
  cases hz : Cf.X.zeroAt oc
  swap
  · exact absurd (rd_get hκ hm.fine hoc (by rw [hm.fp]; exact hσ.jc.zero oc hz) hcv) hv0
  cases hf : fwdJ Cf.X i oc od of
  swap
  · obtain ⟨-, hself, t, o, ht, ho, hr0⟩ := jumpH_fwd hr hz hf
    subst hr0
    obtain ⟨rfl, hlt⟩ := fwdOff_eq (X := Cf.X) ho
    have hat' := h2 _ List.mem_cons_self
    have ho' := pairAt_lt hpair hat'
    have hto : Cf.X.entry + (t - Cf.X.entry) = t := by omega
    refine Or.inr ⟨hself, t - Cf.X.entry, z.pos, by rw [hpcw t ht (by have := hlen _ ho'; omega), hto], by omega,
      hat', as.map Ev.atom, bs.map Ev.atom ++ es1, by simp, ?_, evM_atoms _,
      fun y hy ↦ hev y (by rw [List.map_append, ← List.append_assoc]; exact writtenC_prefix hy)⟩
    rw [hzpos, Bridge.walk_atoms, hes1]
    rfl
  have hh := headH_of hr hz hf
  rcases head_cases hzsok hctrl hh with ⟨x, fs, args, rets, ss, hcur⟩ | ⟨c', f', args', ss, hcur⟩ | hh4
  · obtain ⟨-, -, s0, -, -, hsite, htg, -⟩ := headH_dispatch hh hcur
    rw [hdn s0 (siteAt_spec hsite).1 htg] at hsf
    cases hsf
  · obtain ⟨-, t, -, ht, hent, -⟩ := headH_callIf hh hcur
    rw [hcj t f' ht (entOk_spec hent)] at hsf
    cases hsf
  rcases hh4 with ⟨c, zb, nb, ss, hcur⟩ | ⟨x, arms, ss, hcur⟩ | ⟨vs', ss, hcur⟩ |
    ⟨f, args, rets, ss, hcur⟩
  rotate_left 3
  · obtain ⟨-, s0, t, -, -, -, ht, hent, -⟩ := headH_call hh hcur
    rw [hcj t f ht (entOk_spec hent)] at hsf
    cases hsf
  · obtain ⟨hloc, hself, t, cz, cn, o, ht, -, hcn, ho, rfl⟩ := headH_ite hh hcur
    obtain ⟨es2, rfl, hes2⟩ := side_ite hcur hes1
    have hcond := hσ.jc.cond _ _ hb c (by simp)
    have hloc' : Cf.X.locAt c.idx = oc := hloc
    rw [hloc'] at hcond
    have hσc : σ c ≠ 0 := fun h0 ↦ hv0 (by rw [rd_get hκ hm.fine hoc (by rw [hm.fp]; exact hcond) hcv, h0])
    simp only [hσc, ↓reduceIte] at hes2
    obtain ⟨evs, es3, rfl, hes3, hevN, hWn⟩ := succ_normC hcn hes2
    obtain ⟨rfl, hlt⟩ := fwdOff_eq (X := Cf.X) ho
    have hat' := h2 _ List.mem_cons_self
    have ho' := pairAt_lt hpair hat'
    refine Or.inr ⟨hself, t - Cf.X.entry, cn.pos, by rw [hpcw t ht (by have := hlen _ ho'; omega)]; omega,
      by omega, hat', (as ++ bs).map Ev.atom ++ Ev.inK c :: evs, es3, by simp, hes3,
      evM_app (evM_atoms _) (evM_inK_cons hevN), fun y hy ↦ ?_⟩
    have h2' := hWn (pre ++ (as ++ bs).map Ev.atom ++ [Ev.inK c]) y (by simpa [List.append_assoc] using hy)
    exact hev y (writtenC_noAtom (fun a h ↦ by cases h) (fun f a r h ↦ by cases h) h2')
  · obtain ⟨-, hself, a, ha⟩ := headH_match_nz hh hcur
    obtain ⟨-, -, hax, -⟩ := jumpH_match hr hcur hz hf ha
    obtain ⟨k0, hk0, hσx, hes2⟩ := side_arm hcur hes1
    have hmem : Stmt.match_ x arms ∈ stmtsOf Cf.fn.body :=
      zok_stmts hzsok (by rw [Zip.pos_head hcur]; exact List.mem_cons_self)
    obtain ⟨t, hjt, hlt, c', hc', hat'⟩ := h3 x arms ss a hcur hz hf ha k0 hk0
    obtain ⟨evs, es3, rfl, hes3, hevN, hWn⟩ := succ_normC hc' hes2
    have ho' := pairAt_lt hpair hat'
    have ht30 : t < 2 ^ 30 := by have := hlen _ ho'; omega
    have hpct : s'.pc = t := by
      have h := rd_get hκ hm.fine hod (by rw [hm.fp]; exact hσ.jc.arm x arms hmem od a ha hax k0 t hσx hjt) hd
      have hgt : (g : K) ^ s'.pc = g ^ t := by simpa using congrArg (fun e : E ↦ e.limb 0) h
      exact gpow_lt_inj (by omega) (by omega) hgt
    refine Or.inr ⟨hself, t - Cf.X.entry, c'.pos, by omega, by omega, hat', (as ++ bs).map Ev.atom ++ evs, es3,
      by simp, hes3, evM_app (evM_atoms _) hevN, fun y hy ↦ ?_⟩
    exact hev y (hWn _ y (by simpa [List.append_assoc] using hy))
  · obtain ⟨-, -, h01⟩ := headH_ret hh hcur
    rw [Zip.pos_head hcur, walk_ret_cons, Out.ret.injEq] at hes1
    obtain ⟨rfl, -⟩ := hes1
    exact Or.inl ⟨h01, by simpa using evM_atoms (sigOf := Cf.sigOf) (rd := rd) (σ := σ) (as ++ bs),
      fun y hy ↦ hev y (by simpa using hy)⟩

theorem slotsIn_at {E : Mode.Env} {b n : ℕ} (h : slotsIn E b n = true) {j : ℕ} (hj : j < n) :
    E.jtLo ≤ b + j ∧ b + j < E.jtHi ∧ (E.jt.get (b + j)).isSome = true := by
  have h3 := List.all_eq_true.mp h j (List.mem_range.mpr hj)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h3
  exact ⟨h3.1.1, h3.1.2, h3.2⟩

theorem jtdGo_at {Cf : CFun} {E : Mode.Env} {ml : List (ℕ × ℕ)} {dl : List (V × ℕ × List ℕ × List ℕ)} :
    ∀ {code : List OffsetInstruction},
    jtdGo Cf E ml dl code = true → ∀ {i o1 o2 o3 : ℕ}, code[i]? = some (.deref o1 o2 o3 .cell) →
      jtd Cf.X o1 o2 o3 = true → ∃ oc of, code[i + 1]? = some (.jump oc o3 of) ∧ Cf.X.zeroAt oc = false ∧
        Cf.X.pcAt o3 = none ∧ o3 ≠ 0 ∧
        ((∃ a, getF Cf.X.arms o3 = some a ∧ ∀ p ∈ ml, p.1 = a.1 → slotsIn E a.2 p.2 = true) ∨
          (getF Cf.X.arms o3 = none ∧ ∃ s, getF Cf.X.sites of = some s ∧ s.tgt = o3 ∧ dspRd Cf E dl s o1 o2 = true))
  | [], _, _, _, _, _, h, _ => by simp at h
  | ins :: code, h, i, o1, o2, o3, hi, hj => by
    simp only [jtdGo, Bool.and_eq_true] at h
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      have h1 := h.1
      simp only [hj, Bool.not_true, Bool.false_or] at h1
      split at h1
      · rename_i oc od of rest
        simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq, Option.isNone_iff_eq_none] at h1
        obtain ⟨⟨⟨⟨rfl, hz⟩, hpc⟩, h0⟩, h2⟩ := h1
        refine ⟨oc, of, rfl, hz, hpc, fun e ↦ by simp [e] at h0, ?_⟩
        split at h2
        · rename_i a ha
          refine Or.inl ⟨a, ha, fun p hp hpa ↦ ?_⟩
          have h3 := List.all_eq_true.mp h2 p hp
          simpa only [hpa, Nat.beq_refl, Bool.not_true, Bool.false_or] using h3
        · rename_i ha
          split at h2
          · rename_i s hs
            simp only [Bool.and_eq_true, Nat.beq_eq] at h2
            exact Or.inr ⟨ha, s, hs, h2.1, h2.2⟩
          · cases h2
      · cases h1
    | succ i => exact jtdGo_at h.2 (by simpa using hi) hj

theorem pick_seq_sel {σ : Val} {x : V} {args rets : List V} {k : Out} {es : List Ev} {vs : List V} :
    ∀ (fs : List String) (j : ℕ), (pick σ x args rets j fs).seq k = .ret es vs →
      ∃ i < fs.length, σ x = ofK (g ^ (j + i))
  | [], _, h => by simp [pick, Out.seq] at h
  | f :: fs, j, h => by
    unfold pick at h
    split_ifs at h with hx
    · exact ⟨0, by simp, by simpa [addressOfIndex] using hx⟩
    · obtain ⟨i, hi, hxi⟩ := pick_seq_sel fs (j + 1) h
      exact ⟨i + 1, by simpa using hi, by rw [hxi]; congr 2; omega⟩

/-- A path through a `dispatch` takes callee `k` of its list at its selector's word `g^k`. -/
theorem side_dsp {zs : Zip} {σ : Val} {x : V} {fs : List String} {args rets : List V} {ss : List Stmt}
    (hz : zs.cur = .dispatch x fs args rets :: ss) {es : List Ev} {vs : List V} (hp : walk σ zs.pos = .ret es vs) :
    ∃ k < fs.length, σ x = ofK (g ^ k) := by
  rw [Zip.pos_head hz, walk, walk1] at hp
  obtain ⟨k, hk, hx⟩ := pick_seq_sel fs 0 hp
  exact ⟨k, hk, by simpa using hx⟩

/-- **A `DEREF` reading the jump table reads a written cell**: its table jump follows, by a `match` on
its selector, whose arm the path takes is a slot of the table; the selector's word its pointer. -/
theorem core_jtd {img : MemoryImage κ} (hκ : κ ≤ 28) {K : Mode.Cert} {Cf : CFun}
    (hpair : pairOk Cf.X Cf.H Cf.frame.O Cf.frame.S Cf.fn.body K.code Cf.d = true)
    (hctrl : ∀ s ∈ stmtsOf Cf.fn.body, ctrlOk s = true) (hjtd : jtdOk Cf K.E K.code = true)
    (hcalls : (∀ x fs a r, Stmt.dispatch x fs a r ∉ stmtsOf Cf.fn.body) ∨ K.code.all (jumpCallOk Cf) = true)
    {s s1 : St} {i o1 o2 o3 : ℕ} (hins : K.code[i]? = some (.deref o1 o2 o3 .cell)) (hj : jtd Cf.X o1 o2 o3 = true)
    (ho1 : o1 < 2 ^ 28) (henv : Mode.EnvOk s K.E) (hm : Moves (refMem img) s s1)
    {σ : Val} (hσ : HonF img Cf s.fp σ) {pos : List Stmt} {pre es : List Ev} {vs : List V}
    (hat : pairAt Cf.P Cf.fn.body K.code Cf.d i = some pos) (hb : walk σ Cf.fn.body = .ret (pre ++ es) vs)
    (hwp : walk σ pos = .ret es vs) : HeapRd s1 (.deref o1 o2 o3 .cell) := by
  rw [jtdOk, Exec.listSeq_eq, Exec.listSeq_eq] at hjtd
  obtain ⟨oc, of, hci, hz, hpcn, h0, hcase⟩ := jtdGo_at hjtd hins hj
  obtain ⟨pos', bs, hat', hpos⟩ := pair_next hpair hat (fun oc' od' of' h ↦ by rw [hins] at h; cases h)
  rw [hpos] at hwp
  obtain ⟨es', hwp', hes⟩ := walk_atoms_ret hwp
  obtain ⟨as, bs2, z, zs, tabs, r, hpos2, hzpos, -, -, -, -, hzsok, hr, -, -, -⟩ := pair_jump hpair hat' hci
  rw [hpos2, hzpos, ← List.append_assoc, ← List.map_append] at hwp'
  obtain ⟨es1, hes1, hes'⟩ := walk_atoms_ret hwp'
  have hf : fwdJ Cf.X (i + 1) oc o3 of = false := by simp [fwdJ, hpcn]
  have hh := headH_of hr hz hf
  obtain ⟨-, hjtHi, henv3⟩ := henv
  -- the slot `o2 + k` of a written jump table, read through a cell holding `g^k`
  have fin : ∀ k, Rd img s.fp o1 = some (ofK (g ^ k)) → K.E.jtLo ≤ o2 + k → o2 + k < K.E.jtHi →
      (K.E.jt.get (o2 + k)).isSome = true → HeapRd s1 (.deref o1 o2 o3 .cell) := by
    intro k hsel hlo hhi hjt
    obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hjt
    have hw := written_mono hm.le (written_of_get (henv3 _ e hlo hhi he))
    intro p y hp hy
    have hpv : p = ofK (g ^ k) := rd_get hκ hm.fine ho1 (by rw [hm.fp]; exact hsel) hp
    have h1 := hy.1
    rw [hpv, ← ofK_mul', ← pow_add, limb_ofK] at h1
    have hlt : k + o2 < 2 ^ 63 := by have := lt_maxCells_63 (x := o2 + k) (by omega); omega
    have hyx := gpow_inj hlt (lt_maxCells_63 hy.2) h1
    rw [← hyx, show k + o2 = o2 + k by omega]
    exact hw
  have hnd : ∀ x arms ss, zs.cur = .match_ x arms :: ss → ∃ a, getF Cf.X.arms o3 = some a := fun x arms ss hcur ↦
    (headH_match_nz hh hcur).2.2
  have hother : (∃ x arms ss, zs.cur = .match_ x arms :: ss) ∨
      ∃ x fs args rets ss, zs.cur = .dispatch x fs args rets :: ss := by
    rcases head_cases hzsok hctrl hh with hd | ⟨c', f', args', ss, hcur⟩ | hh4
    · exact Or.inr hd
    · obtain ⟨-, t, -, ht, -⟩ := headH_callIf hh hcur
      have ht' : Cf.X.pcAt o3 = some t := ht
      rw [hpcn] at ht'; cases ht'
    rcases hh4 with ⟨c, zb, nb, ss, hcur⟩ | h | ⟨vs', ss, hcur⟩ | ⟨f, args, rets, ss, hcur⟩
    rotate_left 3
    · obtain ⟨-, s0, t, -, -, -, ht, -⟩ := headH_call hh hcur
      have ht' : Cf.X.pcAt o3 = some t := ht
      rw [hpcn] at ht'; cases ht'
    · obtain ⟨-, -, t, -, -, -, ht, -⟩ := headH_ite hh hcur
      have ht' : Cf.X.pcAt o3 = some t := ht
      rw [hpcn] at ht'; cases ht'
    · exact Or.inl h
    · obtain ⟨-, -, h01⟩ := headH_ret hh hcur
      split at h01
      · obtain ⟨-, ht⟩ := h01
        have ht' : Cf.X.pcAt o3 = some _ := ht
        rw [hpcn] at ht'; cases ht'
      · exact absurd h01.1 h0
  rcases hcase with ⟨a, ha, hslots⟩ | ⟨ha, st, hst, htg, hd⟩
  · obtain ⟨x, arms, ss, hcur⟩ : ∃ x arms ss, zs.cur = .match_ x arms :: ss := by
      rcases hother with h | ⟨x, fs, args, rets, ss, hcur⟩
      · exact h
      obtain ⟨-, -, s0, -, -, hsite, htg', -⟩ := headH_dispatch hh hcur
      have hcalls := hcalls.resolve_left fun hn ↦ hn _ _ _ _
        (zok_stmts hzsok (by rw [Zip.pos_head hcur]; exact List.mem_cons_self))
      have hcj := List.all_eq_true.mp hcalls _ (List.mem_of_getElem? hci)
      have := (jumpCallOk_dsp hcj (siteAt_spec hsite).1 htg').2.2.1
      rw [ha] at this; cases this
    obtain ⟨-, -, hax, -⟩ := jumpH_match hr hcur hz hf ha
    obtain ⟨k, hk, hσx, -⟩ := side_arm hcur hes1
    have hmem : Stmt.match_ x arms ∈ stmtsOf Cf.fn.body :=
      zok_stmts hzsok (by rw [Zip.pos_head hcur]; exact List.mem_cons_self)
    obtain ⟨hlo, hhi, hjt⟩ := slotsIn_at (hslots _ (matchLens_mem hmem) hax.symm) hk
    simp only [jtd, ha, Bool.and_eq_true, Nat.beq_eq] at hj
    obtain ⟨hbase, hloc⟩ := hj
    have hsel := hσ.jc.sel zs x arms ss _ es1 vs hzsok hcur
      (by rw [hes, hes', ← List.append_assoc, ← List.append_assoc] at hb; exact hb) hes1
    rw [← hax, hloc, hσx] at hsel
    exact fin k hsel (by rw [← hbase]; exact hlo) (by rw [← hbase]; exact hhi) (by rw [← hbase]; exact hjt)
  · obtain ⟨x, fs, args, rets, ss, hcur⟩ : ∃ x fs args rets ss, zs.cur = .dispatch x fs args rets :: ss := by
      rcases hother with ⟨x, arms, ss, hcur⟩ | h
      · obtain ⟨a, ha'⟩ := hnd x arms ss hcur
        rw [ha] at ha'; cases ha'
      · exact h
    obtain ⟨-, -, s0, -, -, hsite, -, -⟩ := headH_dispatch hh hcur
    obtain ⟨hs0, hargs, hrets⟩ := siteAt_eq hsite
    have hs1 : getF Cf.X.sites of = some s0 := hs0
    rw [hst] at hs1
    cases hs1
    have hmem : Stmt.dispatch x fs args rets ∈ stmtsOf Cf.fn.body :=
      zok_stmts hzsok (by rw [Zip.pos_head hcur]; exact List.mem_cons_self)
    have hdl : (x, fs.length, args.map (·.idx), rets.map (·.idx)) ∈ dspLens Cf.fn.body :=
      List.mem_filterMap.mpr ⟨_, hmem, rfl⟩
    have hq := List.all_eq_true.mp hd _ hdl
    simp only [hargs, hrets, beq_self_eq_true, Bool.and_self, Bool.not_true, Bool.false_or, Bool.and_eq_true,
      Nat.beq_eq] at hq
    obtain ⟨ho1x, hsl⟩ := hq
    obtain ⟨k, hk, hσx⟩ := side_dsp hcur hes1
    obtain ⟨hlo, hhi, hjt⟩ := slotsIn_at hsl hk
    have hsel := hσ.jc.dsel _ _ hb x fs args rets hmem
    rw [ho1x, hσx] at hsel
    exact fin k hsel hlo hhi hjt

/-- **The entry abstraction holds** of its parts, its self cell (a loop's) holding its frame's address. -/
theorem holds_entryAbs {E0 : Mode.Env} {G : Mode.Sig} {s : St}
    (h0 : Mode.Holds s ⟨Mode.foldlT .nil G.entry, .nil, .nil, [], G.pre, Mode.jtRng E0 :: G.preR, G.term, [], .nil,
      G.preP, []⟩)
    (hself : ∀ o, G.self = some o → s.mem.written (s.fp + o) = true ∧ s.mem.get (s.fp + o) = some (ofK (g ^ s.fp))) :
    Mode.Holds s (entryAbs E0 G) := by
  unfold entryAbs
  rcases hs : G.self with _ | o
  · exact h0
  · obtain ⟨hwo, hgo⟩ := hself o hs
    refine ((h0.addW hwo).addV ⟨_, hgo, ?_⟩).addNz ⟨_, hgo, Mode.ofK_gpow_ne_zero _⟩
    exact ⟨1, rfl, by simp [Mode.Mono.own]⟩

/-- The reference's words of a frame's slots, a prefix of `ws` the frame's cells hold. -/
theorem wsAt_take {img : MemoryImage κ} {fp n : ℕ} {ws : List E}
    (h : ∀ b < n, Rd img fp (2 + b) = some (slotW ws b)) {k : ℕ} (hkn : k ≤ n) (hk : k ≤ ws.length) :
    wsAt img fp k = ws.take k := by
  apply List.ext_getElem (by simp [wsAt]; omega)
  intro b h1 h2
  simp only [wsAt, List.length_map, List.length_range] at h1
  simp only [wsAt, List.getElem_map, List.getElem_range, List.getElem_take]
  rw [h b (by omega), slotW_get (by omega)]
  rfl

/-- The reference's words of a frame's slots, the words `ws` its cells hold. -/
theorem wsAt_eq {img : MemoryImage κ} {fp n : ℕ} {ws : List E} (hn : ws.length = n)
    (h : ∀ b < n, Rd img fp (2 + b) = some (slotW ws b)) : wsAt img fp n = ws := by
  rw [wsAt_take h le_rfl (by omega), List.take_of_length_le (by omega)]

/-- **A top-level `const`, `copy` or `mul` before the `ret` is on the path** (`defOf`), defining its value. -/
theorem defOf_mem {σ : Val} {n : ℕ} {a : Atom} : ∀ {body : List Stmt}, body.all topOk = true →
    ∀ {es : List Ev} {vs : List V}, walk σ body = .ret es vs → defOf body n = some a → Ev.atom a ∈ es
  | [], _, _, _, _, h => by simp [defOf] at h
  | s :: ss, ht, es, vs, hw, h => by
    simp only [List.all_cons, Bool.and_eq_true] at ht
    cases s with
    | ret vs' => simp [defOf] at h
    | atom a' =>
      rw [walk_atom_cons] at hw
      obtain ⟨es', hw', rfl⟩ := pre_eq_ret hw
      have hrec : defOf ss n = some a → Ev.atom a ∈ Ev.atom a' :: es' :=
        fun h' ↦ List.mem_cons_of_mem _ (defOf_mem ht.2 hw' h')
      cases a' with
      | const d c =>
        simp only [defOf] at h
        cases hb : (vnum d).any (Nat.beq · n) <;> simp only [hb, Bool.cond_true, Bool.cond_false] at h
        · exact hrec h
        · cases h; exact List.mem_cons_self
      | copy d c =>
        simp only [defOf] at h
        cases hb : (vnum d).any (Nat.beq · n) <;> simp only [hb, Bool.cond_true, Bool.cond_false] at h
        · exact hrec h
        · cases h; exact List.mem_cons_self
      | mul d x y =>
        simp only [defOf] at h
        cases hb : (vnum d).any (Nat.beq · n) <;> simp only [hb, Bool.cond_true, Bool.cond_false] at h
        · exact hrec h
        · cases h; exact List.mem_cons_self
      | _ => exact hrec (by simpa [defOf] using h)
    | _ =>
      obtain ⟨es1, es2, h2, rfl⟩ := walk_cons_noRet (noRet_of_topOk ht.1) hw
      exact List.mem_append_right _ (defOf_mem ht.2 h2 (by simpa [defOf] using h))

/-- The atom `defOf` finds defines value `n`. -/
theorem defOf_dst {n : ℕ} {a : Atom} : ∀ {body : List Stmt}, defOf body n = some a →
    (∃ c, a = .const (V.n n) c) ∨ (∃ x, a = .copy (V.n n) x) ∨ ∃ x y, a = .mul (V.n n) x y
  | [], h => by simp [defOf] at h
  | s :: ss, h => by
    cases s with
    | ret vs' => simp [defOf] at h
    | atom a' =>
      cases a' with
      | const d c =>
        simp only [defOf] at h
        cases hb : (vnum d).any (Nat.beq · n) <;> simp only [hb, Bool.cond_true, Bool.cond_false] at h
        · exact defOf_dst h
        · cases h
          obtain ⟨k, hk, hkn⟩ := (Option.any_eq_true _ _).mp hb
          rw [Nat.beq_eq] at hkn; subst hkn
          exact Or.inl ⟨c, by rw [vnum_eq hk]⟩
      | copy d c =>
        simp only [defOf] at h
        cases hb : (vnum d).any (Nat.beq · n) <;> simp only [hb, Bool.cond_true, Bool.cond_false] at h
        · exact defOf_dst h
        · cases h
          obtain ⟨k, hk, hkn⟩ := (Option.any_eq_true _ _).mp hb
          rw [Nat.beq_eq] at hkn; subst hkn
          exact Or.inr (Or.inl ⟨c, by rw [vnum_eq hk]⟩)
      | mul d x y =>
        simp only [defOf] at h
        cases hb : (vnum d).any (Nat.beq · n) <;> simp only [hb, Bool.cond_true, Bool.cond_false] at h
        · exact defOf_dst h
        · cases h
          obtain ⟨k, hk, hkn⟩ := (Option.any_eq_true _ _).mp hb
          rw [Nat.beq_eq] at hkn; subst hkn
          exact Or.inr (Or.inr ⟨x, y, by rw [vnum_eq hk]⟩)
      | _ => exact defOf_dst (by simpa [defOf] using h)
    | _ => exact defOf_dst (by simpa [defOf] using h)

/-- **A value's word, its monomial's** (`wordNf`), on an honest path. -/
theorem wordNf_val {pows : Exec.PowTree} (hp : pows.Ok) {body : List Stmt} (htop : body.all topOk = true)
    {σ : Val} {rd : Reader} {es : List Ev} {vs : List V} (hw : walk σ body = .ret es vs)
    (hh : ∀ e ∈ es, e.Holds rd σ) : ∀ k n, (wordNf pows body k n).valW (vw σ) = σ (V.n n)
  | 0, n => by simp [wordNf, CCell.valW, prodW, vw, addressOfIndex]
  | k + 1, n => by
    have hself : (⟨[(n, 1)], 0⟩ : CCell).valW (vw σ) = σ (V.n n) := by
      simp [CCell.valW, prodW, vw, addressOfIndex]
    unfold wordNf
    cases hd : defOf body n with
    | none => exact hself
    | some a =>
      have hmem := defOf_mem htop hw hd
      have hH : a.Holds rd σ := hh _ hmem
      rcases defOf_dst hd with ⟨c, rfl⟩ | ⟨x, rfl⟩ | ⟨x, y, rfl⟩
      · simp only
        cases hpw : powOf pows c with
        | none => exact hself
        | some e =>
          have hc : σ (V.n n) = c := hH
          simp only [CCell.valW, prodW, one_mul, hc, powOf_ok hp hpw]
      · simp only
        cases hx : vnum x with
        | none => exact hself
        | some m =>
          have hc : σ (V.n n) = σ x := hH
          rw [wordNf_val hp htop hw hh k m, hc, vnum_eq hx]
      · simp only
        cases hx : vnum x with
        | none => exact hself
        | some m1 =>
          cases hy : vnum y with
          | none => exact hself
          | some m2 =>
            have hc : σ (V.n n) = σ x * σ y := hH
            rw [valW_mul, wordNf_val hp htop hw hh k m1, wordNf_val hp htop hw hh k m2, hc, vnum_eq hx, vnum_eq hy]

theorem keyOk_get : ∀ {args : List V} {ks : List ℕ}, keyOk args ks = true → ∀ {i a : ℕ}, ks[i]? = some a →
    args[i]? = some (V.n a)
  | [], [], _, _, _, h => by simp at h
  | v :: vs, k :: ks, h, i, a, hi => by
    simp only [keyOk, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      split at h1
      · rename_i k' hk
        rw [Nat.beq_eq] at h1; subst h1
        simp [vnum_eq hk]
      · cases h1
    | succ i => simpa using keyOk_get h2 (by simpa using hi)
  | [], _ :: _, h, _, _, _ => by simp [keyOk] at h
  | _ :: _, [], h, _, _, _ => by simp [keyOk] at h

theorem slotW_app_get {A B : List E} {n i : ℕ} {w : E} (hA : A.length = n) (h : B[i]? = some w) :
    slotW (A ++ B) (n + i) = w := by
  subst hA
  unfold slotW
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left, h, Option.getD_some]

/-- **A run extended by its next point is written** (`rngXExt`): its cells below the upper bound's exponent `e` the
run's, the one at `e` its next point (`nextPt`). -/
theorem rw_slotXExt {s : St} {ws : List E} {r : Mode.Rng} {q : CRun} {b : ℕ} {c : CCell} (hr : rngX r = some q)
    (hqb : q.hi = .val b) (hqc : nextPt q = some c) (hcs : SlotEq s ws (rngM r).bs) (h : RW s r)
    (hpt : WrK s.mem (c.addrW (slotW ws))) :
    ∀ x, (⟨q.base, q.stride, q.lo, .mono ⟨[(b, 1)], 1⟩⟩ : CRun).Set (slotW ws) x → WrK s.mem x := by
  intro x hx
  obtain ⟨ylo, yhi, j, h1, h2, h3, h4, rfl⟩ := runSet_iff.mp hx
  have hRW := rw_slotX hr hcs h
  obtain ⟨lo, hi, c0, hlo, hhi, hmc, hq⟩ := rngX_spec hr
  -- the upper bound's word, `g^e`
  obtain ⟨vq, xlo, xhi, -, -, hih, -⟩ := h
  have hhi' : idxX r.hi = some (.val b) := by rw [hhi, ← hqb, hq]
  have hc3 : SlotEq s ws (idxB r.hi) := fun x hx ↦ hcs x (by simp [rngM, hx])
  have hwb : slotW ws b = ofK (addressOfIndex xhi) ∧ xhi < capE := by
    rcases idxX_spec hhi' with ⟨n, -, -, hn⟩ | ⟨o, d, ho, h2o, -, hd⟩
    · cases hn
    · rw [ho] at hih hc3
      obtain ⟨v, e, hv, hve, he, rfl⟩ := hih
      obtain ⟨o', ho', -, hget⟩ := hc3 _ List.mem_cons_self
      simp only [Mode.Base.fr.injEq] at ho'
      subst ho'
      simp only [BaseVal] at hv
      have hb : b = o - 2 ∧ d = 0 := by
        unfold idxO at hd
        cases hd0 : Nat.beq d 0
        · rw [hd0] at hd; cases hd
        · rw [hd0] at hd
          simp only [Bool.cond_true, CIdx.val.injEq] at hd
          exact ⟨hd, Nat.eq_of_beq_eq_true hd0⟩
      obtain ⟨rfl, rfl⟩ := hb
      rw [← hget _ hv, hve, Nat.add_zero]
      exact ⟨rfl, by rw [capE_eq]; exact he⟩
  obtain ⟨hwb, hxc⟩ := hwb
  -- the extended bound's exponent, `e + 1`
  have hy : yhi = xhi + 1 := by
    have e1 : (idxC (.mono ⟨[(b, 1)], 1⟩)).valW (slotW ws) = ofK (addressOfIndex (xhi + 1)) := by
      simp only [idxC, CCell.valW, prodW, pow_one, mul_one, hwb, addressOfIndex, pow_add, ofK_mul']
    obtain ⟨hy1, hy2⟩ := rep_spec h2
    rw [e1] at hy2
    have := capE_eq
    exact (gpow_inj_lt (by omega) (by omega) hy2).symm
  rcases Nat.lt_or_ge j xhi with hj | hj
  · refine hRW _ (runSet_iff.mpr ⟨ylo, xhi, j, h1, ?_, h3, hj, rfl⟩)
    rw [hqb, idxC, valW_baseC, hwb]
    exact rep_of hxc
  · obtain rfl : j = xhi := by omega
    have hcv : c.valW (slotW ws) = q.base.valW (slotW ws) * ofK (addressOfIndex (q.stride * j)) := by
      unfold nextPt at hqc
      rw [hqb] at hqc
      cases hqc
      have hb1 : (⟨[(b, q.stride)], 0⟩ : CCell).valW (slotW ws) = ofK (addressOfIndex (q.stride * j)) := by
        show prodW (slotW ws) [(b, q.stride)] * ofK (addressOfIndex 0) = _
        rw [prodW, prodW, hwb, mul_one, addressOfIndex, ← ofK_pow', ← pow_mul, ← ofK_mul', addressOfIndex,
          addressOfIndex, pow_zero, mul_one, Nat.mul_comm]
      rw [valW_mul, hb1]
    unfold CCell.addrW at hpt
    rw [hcv] at hpt
    exact hpt

/-- A frame base's slot word, from the linked form (`SlotGetL`). -/
theorem slotGet_ofL {gl : List (ℕ × ℕ × ℕ)} {gp : List ((ℕ × ℕ) × ℕ)} {s : St} {ws : List E} {i : Mode.Idx}
    {ci : CIdx} (hi : idxX i = some ci) (h : SlotGetL gl gp s ws (idxB i)) : SlotGet s ws (idxB i) := by
  intro b hb
  rcases idxX_spec hi with ⟨n, rfl, -, -⟩ | ⟨o, c, rfl, h2, -, -⟩
  · simp [idxB] at hb
  · simp only [idxB, List.mem_singleton] at hb
    subst hb
    obtain ⟨w, hw, hv⟩ := h _ List.mem_cons_self
    simp only [BaseL, h2, ↓reduceIte, Option.some.injEq] at hw
    subst hw
    exact ⟨o, rfl, h2, hv⟩

theorem idxL_of_idxX {gl : List (ℕ × ℕ × ℕ)} {i : Mode.Idx} {ci : CIdx} (h : idxX i = some ci) :
    idxL gl i = some ci := by
  cases i with
  | num n => exact h
  | ex b c =>
    cases b with
    | fr o => exact h
    | hp q d => simp [idxX] at h

/-- **A bound's exponent, the caller's cells linked**: a constant's or a frame cell's (`idxX`), or a caller's cell's
(`isHp1`, its word the linked slot's). -/
theorem rep_idxValL {gl : List (ℕ × ℕ × ℕ)} {gp : List ((ℕ × ℕ) × ℕ)} {s : St} {ws : List E} {i : Mode.Idx}
    {ci : CIdx} (hi : idxL gl i = some ci) (hb : bndX i = true) (hc : SlotGetL gl gp s ws (idxB i)) {x : ℕ}
    (h : rep ((idxC ci).valW (slotW ws)) = some x) (hx : (idxC ci).off ≤ x) : IdxVal s i x := by
  rcases Bool.or_eq_true_iff.mp hb with hb | hb
  · obtain ⟨ci', hci'⟩ := Option.isSome_iff_exists.mp hb
    rw [idxL_of_idxX hci', Option.some.injEq] at hi
    subst hi
    exact rep_idxVal hci' (slotGet_ofL hci' hc) h hx
  · match i, hb, hi with
    | .ex (.hp q d) c, hb, hi =>
      simp only [isHp1, Bool.and_eq_true, Nat.beq_eq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      simp only [idxL, and_self, ↓reduceIte, Option.map_eq_some_iff] at hi
      obtain ⟨p, hp, rfl⟩ := hi
      obtain ⟨w, hw, hv⟩ := hc _ List.mem_cons_self
      simp only [BaseL, ↓reduceIte, hp, Option.map_some, Option.some.injEq] at hw
      have hval : (idxC (bif Nat.beq p.2 0 then CIdx.val p.1 else .mono ⟨[(p.1, 1)], p.2⟩)).valW (slotW ws) = w := by
        rw [← hw]
        cases hk : Nat.beq p.2 0
        · simp [idxC, CCell.valW, prodW, addressOfIndex]
        · rw [Nat.beq_eq] at hk
          simp [idxC, valW_baseC, hk]
      rw [hval] at h
      obtain ⟨hx1, hwx⟩ := rep_spec h
      rw [capE_eq] at hx1
      exact ⟨w, x, hv, by rw [hwx, addressOfIndex], hx1, rfl⟩

/-- **A run of exponent bounds, the caller's cells linked** (`boundsX`): its heap run's cells written, its bounds
having exponents, it is written. -/
theorem slot_rwLX {gl : List (ℕ × ℕ × ℕ)} {gp : List ((ℕ × ℕ) × ℕ)} {s : St} {ws : List E} {r : Mode.Rng}
    {q : CRun} (hr : rngL gl gp r = some q) (hbx : boundsX r = true) (hc : SlotGetL gl gp s ws (rngM r).bs)
    (hel : IdxEx (slotW ws) q.lo) (heh : IdxEx (slotW ws) q.hi) (h : ∀ x, q.Set (slotW ws) x → WrK s.mem x) :
    RW s r := by
  obtain ⟨lo, hi, c, hlo, hhi, hmc, rfl⟩ := rngL_spec hr
  simp only [boundsX, Bool.and_eq_true] at hbx
  obtain ⟨hbl, hbh⟩ := hbx
  have hcq : SlotGetL gl gp s ws r.q.bs := fun b hb ↦ hc b (by simp [rngM, hb])
  have hcl : SlotGetL gl gp s ws (idxB r.lo) := fun b hb ↦ hc b (by simp [rngM, hb])
  have hch : SlotGetL gl gp s ws (idxB r.hi) := fun b hb ↦ hc b (by simp [rngM, hb])
  obtain ⟨ylo, hylo, hylo'⟩ := hel
  obtain ⟨yhi, hyhi, hyhi'⟩ := heh
  refine ⟨_, ylo, yhi, monoVal_slotL' hmc hcq, rep_idxValL hlo hbl hcl hylo hylo',
    rep_idxValL hhi hbh hch hyhi hyhi', fun j h1 h2 ↦ ?_⟩
  have hx := h _ (runSet_iff.mpr ⟨ylo, yhi, j, hylo, hyhi, h1, h2, rfl⟩)
  rw [run_cell]
  exact names_wrk hx

/-- **The read `hpValS` names holds** on the path: at the pointer's word past `d`, the value it names. -/
theorem hpValS_rd {pows : Exec.PowTree} (hp : pows.Ok) {body : List Stmt} (htop : body.all topOk = true)
    {σ : Val} {rd : Reader} {es : List Ev} {vs : List V} (hw : walk σ body = .ret es vs)
    (hh : ∀ e ∈ es, e.Holds rd σ) {a d n : ℕ} (h : hpValS pows body a d = some n) :
    rd ((σ (V.n a)).limb 0 * addressOfIndex d) = some (σ (V.n n)) := by
  unfold hpValS at h
  split at h
  · rename_i n' hn
    cases h
    exact (hh _ (hpVal_mem htop hw hn)).2
  · split at h
    · rename_i b k hwk
      have hl : LoadHolds rd (σ (V.n b)) (d + k) (σ (V.n n)) := hh _ (hpVal_mem htop hw h)
      have hv := wordNf_val hp htop hw hh baseFuel a
      rw [hwk] at hv
      rw [← hv]
      have e1 : (⟨[(b, 1)], k⟩ : CCell).valW (vw σ) = σ (V.n b) * ofK (addressOfIndex k) := by
        simp [CCell.valW, prodW, vw]
      rw [e1, Mode.limb_mul_ofK, mul_assoc, addressOfIndex, addressOfIndex, ← pow_add, Nat.add_comm]
      exact hl.2
    · cases h

/-- **A callee's ghost words** (`hpArgOk`): ghost `j` the word of the monomial `ghostW` names for the callee's pointer
base `(hpBs G)[j]`, at the call's argument values `ks`. -/
theorem gargsW_ghost {Cf : CFun} {G : Mode.Sig} {f : String} {args : List V} {σ : Val}
    (hgl : (gargsOf Cf.H.gargs f args).length = (Cf.sigOf f).ghosts)
    (hgh : Nat.beq (Cf.sigOf f).ghosts (hpBs G).length = true) (hpa : hpArgOk Cf G f = true) :
    (gargsW Cf.H σ f args).length = (hpBs G).length ∧ ∀ (j : ℕ) (p : ℕ × ℕ), (hpBs G)[j]? = some p → ∃ ks c, keyOk args ks = true ∧
      ghostW Cf ks p = some c ∧ (gargsW Cf.H σ f args)[j]? = some (c.valW (vw σ)) := by
  rw [Nat.beq_eq] at hgh
  simp only [hpArgOk, Bool.and_eq_true, List.all_eq_true] at hpa
  obtain ⟨-, hpa⟩ := hpa
  have hlen : (gargsW Cf.H σ f args).length = (hpBs G).length := by
    simp only [gargsW, List.length_map, hgl, hgh]
  refine ⟨hlen, fun j p hj ↦ ?_⟩
  unfold gargsW
  unfold gargsOf at hgl ⊢
  cases hfd : Cf.H.gargs.find? (fun p ↦ decide (p.1 = f) && keyOk args p.2.1) with
  | none =>
    rw [hfd] at hgl
    simp only [List.length_nil] at hgl
    rw [hgh] at hgl
    rw [List.eq_nil_of_length_eq_zero hgl.symm] at hj
    cases hj
  | some x =>
    have hmem := List.mem_of_find?_eq_some hfd
    have hf := List.find?_some hfd
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hf
    have h1 := hpa x hmem
    simp only [hf.1, beq_self_eq_true, Bool.not_true, Bool.false_or, decide_eq_true_eq] at h1
    have hj' := congrArg (·[j]?) h1
    simp only [List.getElem?_map, hj, Option.map_some] at hj'
    cases hc : ghostW Cf x.2.1 p with
    | none =>
      rw [hc] at hj'
      cases h : x.2.2[j]? <;> simp [h] at hj'
    | some c =>
      rw [hc] at hj'
      cases h : x.2.2[j]? with
      | none => simp [h] at hj'
      | some c' =>
        simp only [h, Option.map_some, Option.some.injEq] at hj'
        exact ⟨x.2.1, c, hf.2, hc, by simp [h, hj']⟩

theorem glOfs_cons (n q d : ℕ) (l : List (ℕ × ℕ)) :
    glOfs n ((q, d) :: l) = if q = 1 then (d, n, 0) :: glOfs (n + 1) l else glOfs (n + 1) l := by
  by_cases h : q = 1
  · subst h; rfl
  · have : Nat.beq q 1 = false := by cases hb : Nat.beq q 1 <;> simp_all [Nat.beq_eq]
    simp [glOfs, this, h]

theorem gpOfs_cons (n q d : ℕ) (l : List (ℕ × ℕ)) :
    gpOfs n ((q, d) :: l) = if q = 1 then gpOfs (n + 1) l else ((q, d), n) :: gpOfs (n + 1) l := by
  by_cases h : q = 1
  · subst h; rfl
  · have : Nat.beq q 1 = false := by cases hb : Nat.beq q 1 <;> simp_all [Nat.beq_eq]
    simp [gpOfs, this, h]

/-- **`(d, n + j, 0)` for the caller's cell `(1, d)`, the `j`-th of `ps`** (`glOfs`). -/
theorem glOfs_lookup {d : ℕ} : ∀ {n : ℕ} {ps : List (ℕ × ℕ)}, (1, d) ∈ ps →
    (glOfs n ps).lookup d = some (n + ps.idxOf (1, d), 0)
  | _, [], h => by cases h
  | n, (q, d') :: ps, h => by
    rw [List.idxOf_cons, glOfs_cons]
    by_cases he : (q, d') = (1, d)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      simp
    · have hm : (1, d) ∈ ps := by
        rcases List.mem_cons.mp h with h | h
        · exact absurd h.symm he
        · exact h
      have hb : ((q, d') == (1, d)) = false := by simpa using he
      simp only [hb, Bool.false_eq_true, ↓reduceIte]
      have ih := glOfs_lookup (n := n + 1) hm
      by_cases hq : q = 1
      · subst hq
        have hd : d ≠ d' := fun h ↦ he (by rw [h])
        simp only [↓reduceIte]
        rw [List.lookup_cons, show (d == d') = false by simpa using hd, ih]
        simp only [Option.some.injEq, Prod.mk.injEq, and_true]
        omega
      · simp only [hq, ↓reduceIte]
        rw [ih]
        simp only [Option.some.injEq, Prod.mk.injEq, and_true]
        omega

/-- **`((q, d), n + j)` for the word at an argument's cell `(q, d)`, `q ≠ 1`, the `j`-th of `ps`** (`gpOfs`). -/
theorem gpOfs_lookup {q d : ℕ} (hq : q ≠ 1) : ∀ {n : ℕ} {ps : List (ℕ × ℕ)}, (q, d) ∈ ps →
    (gpOfs n ps).lookup (q, d) = some (n + ps.idxOf (q, d))
  | _, [], h => by cases h
  | n, (q', d') :: ps, h => by
    rw [List.idxOf_cons, gpOfs_cons]
    by_cases he : (q', d') = (q, d)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      simp [hq]
    · have hm : (q, d) ∈ ps := by
        rcases List.mem_cons.mp h with h | h
        · exact absurd h.symm he
        · exact h
      have hb : ((q', d') == (q, d)) = false := by simpa using he
      simp only [hb, Bool.false_eq_true, ↓reduceIte]
      have ih := gpOfs_lookup hq (n := n + 1) hm
      by_cases hq' : q' = 1
      · simp only [hq', ↓reduceIte]
        rw [ih]
        simp only [Option.some.injEq]
        omega
      · simp only [hq', ↓reduceIte]
        rw [List.lookup_cons, show ((q, d) == (q', d')) = false by simpa using Ne.symm he, ih]
        simp only [Option.some.injEq]
        omega

/-- **A callee's bases at its entry** `s` (`baseC1`): its argument cells `2 + b` hold the words `ws`, the caller's
cells `(1, d)` of `ps` (through header cell `1`, the caller's frame `fpc`) and the words at its arguments' cells `(q, d)`
of `ps` the ghost slots' after them: `SlotGetL`. -/
theorem slotGetL_call {img : MemoryImage κ} (hκ : κ ≤ 28) {s : St} (hs : Fine (refMem img) s) {G : Mode.Sig}
    {na : ℕ} {ws : List E} {ps : List (ℕ × ℕ)} (hws : ∀ b < na, Rd img s.fp (2 + b) = some (slotW ws b))
    (hw : ∀ o ∈ G.entry, s.mem.written (s.fp + o) = true) {fpc : ℕ} (h1 : Rd img s.fp 1 = some (ofK (g ^ fpc)))
    (h1w : s.mem.written (s.fp + 1) = true)
    (hcell : ∀ d, (1, d) ∈ ps → s.mem.written (fpc + d) = true ∧ d < 2 ^ 28 ∧
      Rd img fpc d = some (slotW ws (na + ps.idxOf (1, d))))
    (hcellq : ∀ q d, (q, d) ∈ ps → q ≠ 1 → 2 ≤ q → q - 2 < na → ∃ x, Names (slotW ws (q - 2) * ofK (g ^ d)) x ∧
      s.mem.written x = true ∧ refMem img x = slotW ws (na + ps.idxOf (q, d)))
    {bs : List (Mode.Base × ℕ)} (hall : ∀ b ∈ bs, baseC1 G na ps b.1 = true) :
    SlotGetL (glOfs na ps) (gpOfs na ps) s ws bs := by
  intro b hb
  have h := hall b hb
  rcases hb1 : b.1 with o | ⟨q, d⟩
  · rw [hb1] at h
    simp only [baseC1, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at h
    obtain ⟨⟨⟨h2, hn⟩, h28⟩, hent⟩ := h
    obtain ⟨u, hu⟩ := Mem.get_of_written (hw o hent)
    refine ⟨slotW ws (o - 2), by simp [BaseL, h2], ?_⟩
    show s.mem.get (s.fp + o) = some _
    rw [hu, rd_get hκ hs h28 (by have := hws (o - 2) hn; rwa [show 2 + (o - 2) = o by omega] at this) hu]
  · rw [hb1] at h
    simp only [baseC1, Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq, decide_eq_true_eq,
      List.contains_iff_mem] at h
    obtain ⟨hd, hq⟩ := h
    rcases hq with rfl | ⟨⟨⟨h2, hn⟩, h28⟩, hent⟩
    · obtain ⟨hwd, hd28, hrd⟩ := hcell d hd
      refine ⟨slotW ws (na + ps.idxOf (1, d)), by simp [BaseL, glOfs_lookup hd], ?_⟩
      obtain ⟨p, hp⟩ := Mem.get_of_written h1w
      have hp' : p = ofK (g ^ fpc) := rd_get hκ hs (by norm_num) h1 hp
      subst hp'
      obtain ⟨u, hu⟩ := Mem.get_of_written hwd
      have hlt := written_lt hs hwd
      have hfpc : fpc < maxCells := by omega
      refine ⟨_, fpc + d, hp, Mode.names_shift (by simp) hlt, ?_⟩
      rw [hu, rd_getA hκ hs.agree hfpc hd28 hrd hu]
    · have hq1 : q ≠ 1 := by omega
      obtain ⟨x, hx, hwx, hrx⟩ := hcellq q d hd hq1 h2 hn
      refine ⟨slotW ws (na + ps.idxOf (q, d)), by simp [BaseL, hq1, gpOfs_lookup hq1 hd], ?_⟩
      obtain ⟨p, hp⟩ := Mem.get_of_written (hw q hent)
      have hp' : p = slotW ws (q - 2) :=
        rd_get hκ hs h28 (by have := hws (q - 2) hn; rwa [show 2 + (q - 2) = q by omega] at this) hp
      subst hp'
      obtain ⟨u, hu⟩ := Mem.get_of_written hwx
      refine ⟨_, x, hp, hx, ?_⟩
      rw [hu, ← hrx, hs.agree.get _ _ hu]

/-- A call checked by `callChkM` names no callee ghost. -/
theorem callChk_ghosts {Cf : CFun} {g : String} {args : List V} (h : callChkM Cf g args = true)
    (hl : (Cf.hcs.lookup g).isSome = true) : (Cf.sigOf g).ghosts = 0 := by
  simp only [callChkM, Bool.and_eq_true, Bool.or_eq_true, Option.isNone_iff_eq_none] at h
  rcases h.1.1.2 with h1 | h1
  · rw [h1] at hl; cases hl
  · simpa using h1

/-- **A call of a callee on a mode contract has its returned words' monomials** (`EvM`), once the callee returned
in a memory agreeing with the reference, its frame's cells holding the call's words and its signature's
`retV` (`RetHolds`): each returned word's monomial `fitB` checked one its mode signature promises. -/
theorem evM_mode {img : MemoryImage κ} (hκ : κ ≤ 28) {Cf : CFun} {f : String} {args rets : List V}
    (hchk : callChkM Cf f args = true) (hl : Cf.hcs.lookup f = none) {G : Mode.Sig}
    (hrm : ∀ p ∈ (Cf.sigOf f).retM, retMIn G args.length rets.length p = true) {rd : Reader} {σ : Val}
    {m : Mem} {fp : ℕ} (hR : RetHolds (Mode.stOf m fp) G) (ha : Agree m (refMem img)) (hfp : fp < maxCells)
    (hws : ∀ b < args.length + rets.length, Rd img fp (2 + b) = some (slotW ((args ++ rets).map σ) b)) :
    EvM Cf.sigOf rd σ (.call f args rets) := by
  simp only [callChkM, hl, Option.isSome_none, Bool.false_or, Bool.and_eq_true, List.isEmpty_iff] at hchk
  obtain ⟨⟨⟨⟨-, ⟨h2, h3⟩⟩, -⟩, -⟩, -⟩ := hchk
  refine ⟨fun k c hkc ↦ ?_, fun i m' him ↦ ?_, fun p hp ↦ ?_⟩
  · have hr := hrm _ hkc
    simp only [retMIn, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, Nat.beq_eq] at hr
    obtain ⟨⟨hk, h28⟩, q, hq, ⟨hq1, hqS⟩, hqI⟩ := hr
    obtain ⟨u, hu, hmv⟩ := hR.2.2.2.2.1 q hq
    -- the returned word, the cell `2 + na + k`'s
    have hS1 : monoS G (args.length + rets.length) false ⟨0, 0, [(.fr (2 + args.length + k), 1)]⟩ = true := by
      simp [monoS]; omega
    obtain ⟨o, ho, -, hget⟩ := slotEq_of (s := Mode.stOf m fp) hκ ha hfp hws hS1 _ List.mem_cons_self
    simp only [Mode.Base.fr.injEq] at ho
    subst ho
    rw [← hq1] at hget
    have hu1 := hget u hu
    rw [hq1, show 2 + args.length + k - 2 = args.length + k by omega, List.map_append, slotW_append] at hu1
    simp only [List.length_map, show ¬ args.length + k < args.length by omega, ↓reduceIte,
      show args.length + k - args.length = k by omega] at hu1
    -- the monomial, over the argument cells
    have hwsA : ∀ b < args.length, Rd img fp (2 + b) = some (slotW (args.map σ) b) := fun b hb ↦ by
      rw [hws b (by omega), List.map_append, slotW_lt (by simpa using hb)]
    unfold monoIs at hqI
    split at hqI
    · rename_i c' hmc
      rw [CCell.beq_eq hqI] at hmc
      have hv := monoVal_slot hmc (slotEq_of (s := Mode.stOf m fp) hκ ha hfp hwsA hqS) hmv
      rw [List.getElem?_map, List.getElem?_eq_getElem (by omega), Option.map_some, ← hv, hu1,
        slotW_get (by simp; omega), List.getElem_map]
    · cases hqI
  · rw [h2] at him; cases him
  · rw [h3] at hp; cases hp

theorem resBnd_spec {n c N : ℕ} {x : CRes} (h : resBnd n c N x = true) :
    ∃ m, x = .lt (.val n) (.num m) ∧ m + c ≤ N + 1 ∧ m < capE := by
  unfold resBnd at h
  split at h
  · rename_i n' m
    simp only [Bool.and_eq_true, Nat.beq_eq, decide_eq_true_eq] at h
    obtain ⟨⟨rfl, h1⟩, h2⟩ := h
    exact ⟨m, rfl, h1, h2⟩
  · cases h

/-- **A frame run's cell at a return is written** (`faNeed`): the walk's state at the return (`atF_ret`) has the
frame run's pointer cell holding `fp·g^e` and the cell `e + k` written (`faRetOk`), and the pointer's word is the
frame run's cell 0 (`HonB.fa`). -/
theorem faw_wrk {M : Mode.Cert} {Cf : CFun} (hok : CoreOk M Cf) {img : MemoryImage κ} {s s1 : St} {i c : ℕ}
    (hi : i < M.code.length) (hci : M.code[i]? = some (.jump c 0 1)) (hat : AtF img Cf.frame M.code i s)
    (hle : s.mem ≤ s1.mem) (hfine : Fine (refMem img) s1) {σ : Val} (hσ : HonB img Cf s.fp σ) {es : List Ev}
    {vs : List V} (hw : walk σ Cf.fn.body = .ret es vs) (hn : faNeed Cf = true) {x : K} (h : FAW σ Cf.H.fas es x) :
    WrK s1.mem x := by
  have hr := hok.faret
  simp only [faRetOk, hn, Bool.not_true, Bool.false_or, List.all_eq_true, List.mem_range] at hr
  have hr' := hr i hi
  rw [hci] at hr'
  obtain ⟨A, hA, hH⟩ := atF_ret hok.frame.2.1 hok.frame.2.2 hi hat
  simp only [hA, List.all_eq_true] at hr'
  -- a frame run's cell `k` written in the walk's state, at its address
  have hcell : ∀ (p r : V) (rs : List V) (k : ℕ), Ev.atom (.frameAddr p (r :: rs)) ∈ es →
      (A.w.get (Cf.X.locAt r.idx + k)).isSome = true → WrK s1.mem (cellAt σ p k) := by
    intro p r rs k hfa hkk
    have hp := hσ.fa hn es vs hw p r rs hfa
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hkk
    have hwr : s1.mem.written (s.fp + (Cf.X.locAt r.idx + k)) = true := written_mono hle (hH.2.w _ hu)
    refine ⟨s.fp + (Cf.X.locAt r.idx + k), ?_, written_lt hfine hwr, hwr⟩
    simp only [cellAt, hp, limb_ofK, addressOfIndex, pow_add]
    simp [mul_assoc]
  rcases h with ⟨p, run, k, v, hfa, hrk, ⟨a, ha, hva⟩, rfl⟩ | ⟨kp, k, run, hm, hfa, hne, hle', rfl⟩
  · cases run with
    | nil => simp at hrk
    | cons r rs =>
    have hfa' := hr' _ (Bridge.walk_atomS Cf.fn.body (by rw [hw]; exact hfa))
    simp only [faRetAt, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hfa'
    have hk : k < rs.length + 1 := by simpa using (List.getElem?_eq_some_iff.mp hrk).1
    have hkk := hfa'.1 k hk
    have hdst : dstIn Cf.fn.body v = true := by
      unfold dstIn
      exact List.any_eq_true.mpr ⟨.atom a, Bridge.walk_atomS Cf.fn.body (by rw [hw]; exact ha), by simpa using hva⟩
    rw [hrk] at hkk
    simp only [hdst, Bool.not_true, Bool.false_or] at hkk
    exact hcell p r rs k hfa hkk
  · cases run with
    | nil => exact absurd rfl hne
    | cons r rs =>
    have hfa' := hr' _ (Bridge.walk_atomS Cf.fn.body (by rw [hw]; exact hfa))
    simp only [faRetAt, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hfa'
    have hq := hfa'.2 (kp, k) hm
    have hb : Nat.ble (rs.length + 1) k = true := Nat.ble_eq.mpr (by simpa using hle')
    simp only [hb, decide_true, Bool.and_true, Bool.not_true, Bool.false_or] at hq
    exact hcell (V.n kp) r rs k hfa hq

/-- **The frame walk's residual divisors are nonzero** in the reference: each written in the walk's state at its
offset (`atF_ret`) and a nonzero residual of the mode certificate there (`nzrOk`), which `ResAt` makes hold. -/
theorem nzr_hnz {img : MemoryImage κ} (hκ : κ ≤ 28) {K : Mode.Cert} {Cf : CFun}
    (hn : nzrOk Cf K.F.res K.code = true) (har : armsOk Cf.frame = true) (hacc : FrameAcc Cf.frame K.code)
    {i : ℕ} (hi : i < K.code.length) {s : St} (hat : AtF img Cf.frame K.code i s) (hs : Fine (refMem img) s)
    (hres : ResAt (refMem img) K i s) :
    ∀ o ∈ (Cf.frame.nzr.get i).getD [], ∃ v, Rd img s.fp o = some v ∧ v ≠ 0 := by
  intro o ho
  have h := List.all_eq_true.mp hn i (List.mem_range.mpr hi)
  cases hz : Cf.frame.nzr.get i with
  | none => rw [hz] at ho; cases ho
  | some os =>
    rw [hz, Option.getD_some] at ho
    obtain ⟨A, hA, hH⟩ := atF_ret har hacc hi hat
    simp only [hz, hA, List.all_eq_true] at h
    have ho' := h o ho
    simp only [Bool.and_eq_true, Option.isSome_iff_exists, List.contains_iff_mem] at ho'
    obtain ⟨⟨u, hu⟩, hr⟩ := ho'
    have hw := hH.2.w o hu
    obtain ⟨v, hv, hv0⟩ := hres s ⟨hs, Mem.le_refl _, rfl, rfl, rfl⟩ (.nz o) hr hw
    exact ⟨v, rdE_of_get hκ hs.agree hv hv0, hv0⟩

/-- `main`'s own precondition at the constant cell `g^o`, `o` an entry cell of its frame `0`, written. -/
theorem mainPre_wrk {Cf : CFun} {G : Mode.Sig} {c : CCell} (h : mainPre Cf G c = true) {M : ℕ → E} {s : St}
    (hfp : s.fp = 0) (hw : ∀ o ∈ G.entry, s.mem.written (s.fp + o) = true) (hs : Fine M s) (w : ℕ → E) :
    WrK s.mem (c.addrW w) := by
  simp only [mainPre, Bool.and_eq_true, List.isEmpty_iff, List.contains_iff_mem] at h
  obtain ⟨⟨-, hb⟩, ho⟩ := h
  have hwo := hw c.off ho
  rw [hfp, Nat.zero_add] at hwo
  refine ⟨c.off, ?_, written_lt hs hwo, hwo⟩
  simp [CCell.addrW, CCell.valW, hb, prodW, addressOfIndex]

/-- **The frame's hints at its offsets** are the executor's at those pcs. -/
theorem hintsF_of {adv : Prover.Exec.Advice} {C : Ctx} {K : Mode.Cert} {Cf : CFun}
    (hC : Prover.Exec.Ctx.of guestProgram adv = .ok C) (ha : adv.hints = Data.adviceHints) (hK : CodeOk C K)
    (hfe : Cf.frame.entry = K.F.entry)
    (hh : ∀ i < K.code.length, Mode.hintsAt Data.adviceHints (K.F.entry + i) =
      Mode.hintsAt Cf.frame.hints (K.F.entry + i)) :
    ∀ j < K.code.length, (C.hints[Cf.frame.entry + j]?).getD [] = Mode.hintsAt Cf.frame.hints (Cf.frame.entry + j) := by
  intro j hj
  have hpcj : K.F.entry + j < 2 ^ guestProgram.logSize := (Prover.Exec.ctx_of_spec hC).1 ▸ Mode.code_pc hK hj
  rw [hfe, Mode.ctx_hints hC (ha ▸ Mode.adviceHints_incr) hpcj, ha, hh j hj]

/-- **The pairing's hints at an offset** are the frame's. -/
theorem hintsD_of {K : Mode.Cert} {Cf : CFun} (hd : Cf.d.2.2 = Cf.frame.hints) (hx : Cf.X.entry = K.F.entry)
    (hf : Cf.frame.entry = K.F.entry) (j : ℕ) :
    (Cf.d.2.2.lookup (Cf.X.entry + j)).getD [] = Mode.hintsAt Cf.frame.hints (Cf.frame.entry + j) := by
  rw [lookupD_hintsAt, hd, hx, hf]

/-- **A `DEREF` of a heap cell finds it written**: the pairing's read (`pair_readC`), its cell written by the path's
writes before it (`hW`) or by a hint's flow (`flow_wrk`). -/
theorem heapRd_pair {img : MemoryImage κ} (hκ : κ ≤ 28) {Cf : CFun} {code : List OffsetInstruction} {C : Ctx}
    {s s1 : St} {i a o c : ℕ} {pos : List Stmt} {σ : Val} {rd : Reader} {pre es : List Ev} {vs : List V}
    (hpair : pairOk Cf.X Cf.H Cf.frame.O Cf.frame.S Cf.fn.body code Cf.d = true)
    (hpos : pairAt Cf.P Cf.fn.body code Cf.d i = some pos) (hci : code[i]? = some (.deref a o c .cell))
    (hO : hasP Cf.frame.O i = true) (hj : jtd Cf.X a o c = false) (ha : a < 2 ^ 28) (hσ : HonF img Cf s.fp σ)
    (hb : walk σ Cf.fn.body = .ret (pre ++ es) vs) (hwp : walk σ pos = .ret es vs)
    (hrw : ReadsAt Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) pre es)
    (hW : ∀ x, WrittenC Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) pre x → WrK s.mem x)
    (hhd : (Cf.d.2.2.lookup (Cf.X.entry + i)).getD [] = Mode.hintsAt Cf.frame.hints (Cf.frame.entry + i))
    (hs : Fine (refMem img) s) (hm : Moves (refMem img) s s1)
    (e1 : (Mode.hintsAt Cf.frame.hints (Cf.frame.entry + i)).foldlM (Prover.Exec.runHint C) s = .ok s1) :
    HeapRd s1 (.deref a o c .cell) := by
  obtain ⟨as, dv, pv, off, hpairs, hcell, -, hmem, hwr⟩ := pair_readC hpair hpos hci hO hj hwp hrw
  have hwk : WrK s1.mem (cellAt σ pv off) := by
    rcases hwr with h | ⟨a', ha', hfa', hma, hwa⟩
    · exact (hW _ h).mono hm.le
    · rw [hhd] at hpairs
      exact flow_wrk hκ e1 hs hm hpairs ha' hfa'
        (fun q hq ↦ hσ.ptr _ _ hb a' q (List.mem_append_right _ hma) hq) hwa
  simp only [cellsAt, Bool.and_eq_true, Nat.beq_eq] at hcell
  obtain ⟨⟨hloc, hoff⟩, -⟩ := hcell
  intro p x hp hx
  have hrd : Rd img s1.fp a = some (σ pv) := by
    rw [hm.fp, ← hloc]; exact hσ.ptr _ _ hb (.load dv pv off) pv (List.mem_append_right _ hmem) rfl
  have hpv : p = σ pv := rd_get hκ hm.fine ha hrd hp
  obtain ⟨x', hx', hlt', hw'⟩ := hwk
  have h1 := hx.1
  rw [limb0_mul_ofK, hpv, ← hoff] at h1
  have hxx : x = x' := gpow_inj (lt_maxCells_63 hx.2) (lt_maxCells_63 hlt') (h1.symm.trans hx')
  rw [hxx]
  exact hw'

/-- **A fall-through's writes**: a cell the pairing says the path has written by the next position
(`pair_fallC`) is written after the step: by the path before it (`hW`), by a hint's flow (`flow_wrk`), or as a
store's heap cell (`StoreW`). -/
theorem fall_wrk {img : MemoryImage κ} (hκ : κ ≤ 28) {Cf : CFun} {code : List OffsetInstruction} {C : Ctx}
    {s s1 s' : St} {i : ℕ} {σ : Val} {rd : Reader} {pre evs es : List Ev} {vs : List V} {as : List Atom} {y : K}
    (hi : i < code.length) (hsmall : SmallOps code[i]) (hσ : HonF img Cf s.fp σ)
    (hb : walk σ Cf.fn.body = .ret (pre ++ (evs ++ es)) vs)
    (hW : ∀ x, WrittenC Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) pre x → WrK s.mem x)
    (hpairs : List.Forall₂ (Pairs Cf.X) (as.filter flowAtom)
      (((Cf.d.2.2.lookup (Cf.X.entry + i)).getD []).filter isaFlowHint))
    (hhd : (Cf.d.2.2.lookup (Cf.X.entry + i)).getD [] = Mode.hintsAt Cf.frame.hints (Cf.frame.entry + i))
    (hs : Fine (refMem img) s) (hm : Moves (refMem img) s s1) (hle' : s1.mem ≤ s'.mem) (hfp' : s'.fp = s.fp)
    (hf' : Fine (refMem img) s')
    (e1 : (Mode.hintsAt Cf.frame.hints (Cf.frame.entry + i)).foldlM (Prover.Exec.runHint C) s = .ok s1)
    (hstw : StoreW Cf.frame code i s')
    (hy : WrittenC Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) pre y ∨
      (∃ a ∈ as, flowAtom a = true ∧ Ev.atom a ∈ evs ∧ Writes σ a y) ∨
      ∃ (o1 o2 o3 : ℕ) (dv pv : V) (off : ℕ), code[i]? = some (.deref o1 o2 o3 .cell) ∧ hasP Cf.frame.S i = true ∧
        cellsAt Cf.X o1 o2 o3 dv pv off = true ∧ Ev.atom (.load dv pv off) ∈ evs ∧ y = cellAt σ pv off) :
    WrK s'.mem y := by
  rcases hy with h | ⟨a, ha', hfa', hma, hwa⟩ | ⟨o1, o2, o3, dv, pv, off, hci, hS, hcell, hmem, rfl⟩
  · exact (hW y h).mono (Mem.le_trans hm.le hle')
  · rw [hhd] at hpairs
    exact (flow_wrk hκ e1 hs hm hpairs ha' hfa' (fun q hq ↦ hσ.ptr _ _ hb a q
      (List.mem_append_right _ (List.mem_append_left _ hma)) hq) hwa).mono hle'
  · obtain ⟨p, x, hp, hx, hw⟩ := hstw o1 o2 o3 hci (by rw [has_hasP]; exact hS)
    simp only [cellsAt, Bool.and_eq_true, Nat.beq_eq] at hcell
    obtain ⟨⟨hloc, hoff⟩, -⟩ := hcell
    rw [List.getElem?_eq_getElem hi, Option.some.injEq] at hci
    rw [hci] at hsmall
    obtain ⟨so1, -, -⟩ := hsmall
    have hrd : Rd img s'.fp o1 = some (σ pv) := by
      rw [hfp', ← hloc]
      exact hσ.ptr _ _ hb (.load dv pv off) pv (List.mem_append_right _ (List.mem_append_left _ hmem)) rfl
    have hpv : p = σ pv := rd_get hκ hf' so1 hrd hp
    refine ⟨x, ?_, hx.2, hw⟩
    have h1 := hx.1
    rw [limb0_mul_ofK, hpv, ← hoff] at h1
    exact h1

/-- A pointer run's cells are written. -/
theorem rw_of_pw {s : St} {r : Mode.Rng} {os : List ℕ} (h : Mode.PW s r os) : RW s r := by
  obtain ⟨vq, xlo, xhi, hv, hlo, hhi, hall⟩ := h
  refine ⟨vq, xlo, xhi, hv, hlo, hhi, fun j h1 h2 ↦ ?_⟩
  obtain ⟨x, hx, p, hp, -⟩ := hall j h1 h2
  exact ⟨x, hx, written_of_get hp⟩

/-- **A callee's guarantees, written once it returns**: a cell of its heap signature's guarantees (`PostSet`) at the
call's words, from its mode signature's (`RetHolds`, a loop's runs `postL`, `postLP`), each heap guarantee matched
to mode ones as `fitB` or `fitBL` checks (the union of their cases). -/
theorem post_wrk {img : MemoryImage κ} (hκ : κ ≤ 28) {G : Mode.Sig} {h : HSig} {args rets : List V} {σ : Val}
    {rd : Reader} {m m' : Mem} {fp n : ℕ} {y : K} (ham' : Agree m' (refMem img)) (hm' : m ≤ m') (hfp : fp < maxCells)
    (hws : ∀ b < n, Rd img fp (2 + b) = some (slotW ((args ++ rets).map σ) b)) (hrd : rd = img.read)
    (hR : Mode.RetHolds (Mode.stOf m fp) G) (hL : ∀ r ∈ G.postL, RW (Mode.stOf m fp) r)
    (hLP : ∀ q ∈ G.postLP, Mode.PW (Mode.stOf m fp) q.1 q.2)
    (hpost : ∀ c ∈ h.post, (G.post.any (fun m ↦ monoS G n false m && monoIs m c) ||
      G.postR.any fun r ↦ monoS G n false r.q && ptIn c r) = true)
    (hpostR : ∀ q ∈ h.postR, (((G.postR ++ G.postL).any fun r ↦ (monoS G n false r.q && rngIs r q) ||
      (monoS G n false (rngM r) && rngXIs r q) || (monoS G n false (rngM r) && rngXExt G n G.post r q)) ||
      (G.postP ++ G.postLP).any fun r ↦ monoS G n false (rngM r.1) && rngXIs r.1 q) = true)
    (hpostP : ∀ p ∈ h.postP, (hpAll G n G.post p || hpRunIn G n p) = true)
    (hpostPR : ∀ p ∈ h.postPR, ((G.postP ++ G.postLP).any fun r ↦ monoS G n false (rngM r.1) && prunIs r p) = true)
    (hpostQ : ∀ p ∈ h.postQ, rngQIn G n p = true) (hy : PostSet rd h ((args ++ rets).map σ) y) : WrK m' y := by
  have hSE : ∀ {m0 : Mode.Mono}, monoS G n false m0 = true →
      SlotEq (Mode.stOf m' fp) ((args ++ rets).map σ) m0.bs := fun hm1 ↦
    slotEq_of (s := Mode.stOf m' fp) hκ ham' hfp hws hm1
  have hRm : ∀ {s3 : St}, s3 = Mode.stOf m' fp → Mode.stOf m fp = Mode.stOf m fp := fun _ ↦ rfl
  have hRL : ∀ r ∈ G.postR ++ G.postL, RW (Mode.stOf m fp) r := fun r hr ↦
    (List.mem_append.mp hr).elim (hR.2.2.1 r) (hL r)
  have hPL : ∀ q ∈ G.postP ++ G.postLP, Mode.PW (Mode.stOf m fp) q.1 q.2 := fun q hq ↦
    (List.mem_append.mp hq).elim (hR.2.2.2.1 q) (hLP q)
  rcases hy with (⟨c, hc, rfl⟩ | ⟨r, hr, hx⟩) | (⟨p, hp, hps⟩ | ⟨p, hp, a, ha', hpa⟩) |
    ⟨p, hp, w', hw', hrs⟩
  · rcases Bool.or_eq_true_iff.mp (hpost c hc) with h | h
    · obtain ⟨m0, hm0', hmc⟩ := List.any_eq_true.mp h
      rw [Bool.and_eq_true] at hmc
      obtain ⟨hmS, hmc⟩ := hmc
      unfold monoIs at hmc
      split at hmc
      · rename_i c' hc'
        rw [← CCell.beq_eq hmc]
        exact hw_slot hc' (hSE hmS) (Mode.HW.mono (s := Mode.stOf m fp) (s' := Mode.stOf m' fp)
          hm' rfl (hR.2.1 m0 hm0'))
      · cases hmc
    · obtain ⟨r, hr, hrc⟩ := List.any_eq_true.mp h
      rw [Bool.and_eq_true] at hrc
      exact ptIn_slot hrc.2 (hSE hrc.1) (Mode.RW.mono (s := Mode.stOf m fp)
        (s' := Mode.stOf m' fp) hm' rfl (hR.2.2.1 r hr))
  · rcases Bool.or_eq_true_iff.mp (hpostR r hr) with hrq0 | hrq0
    swap
    · -- a run of a pointer run's (a loop's)
      obtain ⟨r', hr', hrq⟩ := List.any_eq_true.mp hrq0
      rw [Bool.and_eq_true] at hrq
      obtain ⟨hmS, hrq⟩ := hrq
      unfold rngXIs at hrq
      split at hrq
      · rename_i q hq
        obtain rfl := of_decide_eq_true hrq
        exact rw_slotX hq (hSE hmS) (rw_of_pw (Mode.PW.mono (s := Mode.stOf m fp)
          (s' := Mode.stOf m' fp) hm' rfl (hPL r' hr'))) y hx
      · cases hrq
    obtain ⟨r', hr', hrq⟩ := List.any_eq_true.mp hrq0
    rcases Bool.or_eq_true_iff.mp hrq with hrq | hrq
    swap
    · -- a run extended by its next point (`rngXExt`)
      rw [Bool.and_eq_true] at hrq
      obtain ⟨hmS, hrq⟩ := hrq
      unfold rngXExt at hrq
      split at hrq
      · rename_i q hq
        split at hrq
        · rename_i b c hqb hqc
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hrq
          obtain ⟨rfl, hpt⟩ := hrq
          obtain ⟨m0, hm0', hmc⟩ := List.any_eq_true.mp hpt
          rw [Bool.and_eq_true] at hmc
          obtain ⟨hmS0, hmc⟩ := hmc
          unfold monoIs at hmc
          split at hmc
          · rename_i c' hc'
            rw [CCell.beq_eq hmc] at hc'
            exact rw_slotXExt hq hqb hqc (hSE hmS) (Mode.RW.mono (s := Mode.stOf m fp)
              (s' := Mode.stOf m' fp) hm' rfl (hRL r' hr'))
              (hw_slot hc' (hSE hmS0) (Mode.HW.mono (s := Mode.stOf m fp) (s' := Mode.stOf m' fp)
                hm' rfl (hR.2.1 m0 hm0'))) y hx
          · cases hmc
        · cases hrq
      · cases hrq
    rcases Bool.or_eq_true_iff.mp hrq with hrq | hrq
    · rw [Bool.and_eq_true] at hrq
      obtain ⟨hmS, hrq⟩ := hrq
      unfold rngIs at hrq
      split at hrq
      · rename_i q hq
        obtain rfl := of_decide_eq_true hrq
        exact rw_slot hq (hSE hmS) (Mode.RW.mono (s := Mode.stOf m fp) (s' := Mode.stOf m' fp)
          hm' rfl (hRL r' hr')) y hx
      · cases hrq
    · rw [Bool.and_eq_true] at hrq
      obtain ⟨hmS, hrq⟩ := hrq
      unfold rngXIs at hrq
      split at hrq
      · rename_i q hq
        obtain rfl := of_decide_eq_true hrq
        exact rw_slotX hq (hSE hmS) (Mode.RW.mono (s := Mode.stOf m fp) (s' := Mode.stOf m' fp)
          hm' rfl (hRL r' hr')) y hx
      · cases hrq
  · obtain ⟨w', hw', o, ho, rfl⟩ := hps
    rcases Bool.or_eq_true_iff.mp (hpostP p hp) with hall | hall
    swap
    · -- a pointer fact a guaranteed run over one pointer base gives (`hpRunIn`)
      rw [hrd] at hw'
      exact hpRun_wr hκ ham' hall (fun r hr ↦ Mode.RW.mono (s := Mode.stOf m fp)
        (s' := Mode.stOf m' fp) hm' rfl (hR.2.2.1 r hr)) hSE hw' ho
    unfold hpAll at hall
    obtain ⟨m0, hm0', hmm⟩ := List.any_eq_true.mp (List.all_eq_true.mp hall o ho)
    split at hmm
    · rename_i q d hqd
      simp only [Bool.and_eq_true, Nat.beq_eq] at hmm
      obtain ⟨⟨hsl, hpb⟩, rfl⟩ := hmm
      rw [CCell.beq_eq hpb, hrd] at hw'
      have h2 : 2 ≤ q := by
        simp only [hpSlot, Bool.and_eq_true, decide_eq_true_eq] at hsl; exact hsl.1.1.1
      exact hw_hp (s := Mode.stOf m' fp) hκ ham' h2 (hSE (monoS_fr hsl))
        (Mode.HW.mono (s := Mode.stOf m fp) (s' := Mode.stOf m' fp) hm' rfl
          (hpOf_spec hqd ▸ hR.2.1 m0 hm0')) hw'
    · cases hmm
  · obtain ⟨r', hr', hrp⟩ := List.any_eq_true.mp (hpostPR p hp)
    simp only [prunIs, rngXIs, Bool.and_eq_true, decide_eq_true_eq] at hrp
    obtain ⟨hmS, hrq, hos⟩ := hrp
    split at hrq
    · rename_i q hq
      obtain rfl := of_decide_eq_true hrq
      rw [hrd, ← hos] at hpa
      exact pw_slotX (s := Mode.stOf m' fp) hκ ham' hq (hSE hmS)
        (Mode.PW.mono (s := Mode.stOf m fp) (s' := Mode.stOf m' fp) hm' rfl (hPL r' hr'))
        y ⟨a, ha', hpa⟩
    · cases hrq
  · -- a run at a cell's word, one of the guaranteed runs over one pointer base (`rngQIn`)
    obtain ⟨r', hr', hrq⟩ := List.any_eq_true.mp (hpostQ p hp)
    rw [Bool.and_eq_true, decide_eq_true_eq] at hrq
    obtain ⟨hq, hsl⟩ := hrq
    rw [hrd] at hw'
    exact rw_slotQ (c := p.1) (q := p.2) hκ ham' hq (fun q' d bs hs ↦ by rw [hs] at hsl; exact hSE hsl)
      (Mode.RW.mono (s := Mode.stOf m fp) (s' := Mode.stOf m' fp) hm' rfl (hR.2.2.1 r' hr'))
      y ⟨w', hw', hrs⟩

/-- **A callee's entry facts at a call through `fitB`**, its ghost slots the caller's pointer bases (`hpArgOk`): the
callee frame's entry cells written, its preconditions at the call's words and its ghosts' (`gargsW`) from the
caller's writes `hW` and the words in the reference, its termination facts and the jump table's run. -/
theorem entry_fitB {img : MemoryImage κ} (hκ : κ ≤ 28) {Cf : CFun} {G : Mode.Sig} {E0 : Mode.Env} {f : String}
    {args rets : List V} {σ : Val} {rd : Reader} {pre es evs : List Ev} {vs : List V} {s s' : St}
    (hf' : Fine (refMem img) s') (hle : s.mem ≤ s'.mem) (hu : s'.mem.used ≤ 2 ^ κ) (hentry : EntryFr img G s')
    (hwsE : ∀ b < args.length + rets.length, Rd img s'.fp (2 + b) = some (slotW ((args ++ rets).map σ) b))
    (hk1 : Rd img s'.fp 1 = some (ofK (g ^ s.fp))) (hG1 : 1 ∈ G.entry)
    (hentw : ∀ o ∈ Cf.frame.sig.entry, s.mem.written (s.fp + o) = true) (hσ : HonF img Cf s.fp σ)
    (hp : Cf.pows.Ok) (htop : Cf.fn.body.all topOk = true) (hb : walk σ Cf.fn.body = .ret (pre ++ es) vs)
    (hh : ∀ e ∈ pre ++ es, e.Holds rd σ) (hrd : rd = img.read) (hfit : FitB G (Cf.sigOf f) args.length rets.length)
    (hpa : hpArgOk Cf G f = true)
    (hreq : CallPre Cf.sigOf Cf.H rd σ (WrittenC Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) (pre ++ evs)) f args)
    (hW : ∀ x, WrittenC Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) (pre ++ evs) x → WrK s'.mem x)
    (hexR : ∀ q ∈ (Cf.sigOf f).preR, IdxEx (slotW (args.map σ ++ gargsW Cf.H σ f args)) q.lo ∧
      IdxEx (slotW (args.map σ ++ gargsW Cf.H σ f args)) q.hi)
    (hexPR : ∀ p ∈ (Cf.sigOf f).prePR, IdxEx (slotW (args.map σ ++ gargsW Cf.H σ f args)) p.1.lo ∧
      IdxEx (slotW (args.map σ ++ gargsW Cf.H σ f args)) p.1.hi)
    (hjt : RW s' (Mode.jtRng E0)) (hterm : ∀ p ∈ G.term, Mode.LTF (Mode.stOf s'.mem s'.fp) p.1 p.2) :
    Mode.Holds s' ⟨Mode.foldlT .nil G.entry, .nil, .nil, [], G.pre, Mode.jtRng E0 :: G.preR, G.term, [], .nil,
      G.preP, []⟩ := by
  have hGpreP := hfit.preP
  have hGpre := hfit.pre
  have hGpb := hfit.pb
  have hGpreR := hfit.preR
  have hhgh := hfit.ghosts
  simp only [Bool.and_eq_true, List.all_eq_true] at hGpreP
  simp only [List.all_eq_true] at hGpre hGpb hGpreR
  have hws1 : ∀ b < args.length, Rd img s'.fp (2 + b) =
      some (slotW (args.map σ ++ gargsW Cf.H σ f args) b) := fun b hb' ↦ by
    rw [hwsE b (by omega), List.map_append, slotW_lt (by simpa using hb'), slotW_lt (by simpa using hb')]
  have hSG : ∀ {m : Mode.Mono}, monoS G args.length true m = true →
      SlotGet s' (args.map σ ++ gargsW Cf.H σ f args) m.bs := fun hm' ↦
    slotGet_of hκ hf'.agree hf'.fp hws1 hentry.w hm'
  obtain ⟨hgl, ⟨hrpre, hrpreR⟩, hrptr⟩ := hreq
  have hGL := gargsW_ghost (σ := σ) hgl hhgh hpa
  have hcell : ∀ d, (1, d) ∈ hpBs G → s'.mem.written (s.fp + d) = true ∧ d < 2 ^ 28 ∧
      Rd img s.fp d = some (slotW (args.map σ ++ gargsW Cf.H σ f args)
        (args.length + (hpBs G).idxOf (1, d))) := by
    intro d hd
    have hp1 := List.all_eq_true.mp (Bool.and_eq_true_iff.mp hpa).1 (1, d) hd
    simp only [Nat.beq_refl, Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq,
      List.contains_iff_mem] at hp1
    obtain ⟨⟨⟨h2, hdn⟩, hd28⟩, hde⟩ := hp1
    refine ⟨written_mono hle (hentw d hde), hd28, ?_⟩
    obtain ⟨ks, c, -, hc, hget⟩ := hGL.2 _ _ (List.getElem?_idxOf hd)
    simp only [ghostW, Nat.beq_refl, Bool.cond_true, Option.some.injEq] at hc
    subst hc
    rw [slotW_app_get (List.length_map _) (by simpa using hget)]
    have := hσ.par (d - 2) hdn
    rw [show 2 + (d - 2) = d by omega] at this
    rw [this]
    simp [CCell.valW, prodW, vw, addressOfIndex]
  have hcellq : ∀ q d, (q, d) ∈ hpBs G → q ≠ 1 → 2 ≤ q → q - 2 < args.length → ∃ x,
      Names (slotW (args.map σ ++ gargsW Cf.H σ f args) (q - 2) * ofK (g ^ d)) x ∧
        s'.mem.written x = true ∧
        refMem img x = slotW (args.map σ ++ gargsW Cf.H σ f args) (args.length + (hpBs G).idxOf (q, d)) := by
    intro q d hqd hq1 h2 hqn
    obtain ⟨ks, c, hks, hc, hget⟩ := hGL.2 _ _ (List.getElem?_idxOf hqd)
    have hqb : Nat.beq q 1 = false := Bool.eq_false_iff.mpr fun h ↦ hq1 (Nat.eq_of_beq_eq_true h)
    simp only [ghostW, hqb, Bool.cond_false, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hc
    obtain ⟨a, ha, n, hn, rfl⟩ := hc
    have harg := keyOk_get hks ha
    -- the argument's cell, a precondition of the callee
    have hpc := hGpb (q, d) hqd
    simp only [hqb, Bool.false_or] at hpc
    obtain ⟨c', hc', hbeq⟩ := List.any_eq_true.mp hpc
    rw [CCell.beq_eq hbeq] at hc'
    have hWc := hW _ (hrpre _ hc')
    have hsa : slotW (args.map σ ++ gargsW Cf.H σ f args) (q - 2) = σ (V.n a) := by
      rw [slotW_lt (by simpa using hqn), slotW_get (by simpa using hqn), List.getElem_map]
      rw [(List.getElem?_eq_some_iff.mp harg).2]
    have hval : (⟨[(q - 2, 1)], d⟩ : CCell).valW (slotW (args.map σ ++ gargsW Cf.H σ f args)) =
        σ (V.n a) * ofK (g ^ d) := by
      simp [CCell.valW, prodW, hsa, addressOfIndex]
    rw [CCell.addrW, hval] at hWc
    obtain ⟨x, hxn, hxw⟩ := names_wrk hWc
    refine ⟨x, by rw [hsa]; exact hxn, hxw, ?_⟩
    -- the word there, the caller's value the `load` names
    have hL2 := hpValS_rd hp htop hb hh hn
    rw [hrd] at hL2
    have hx := hxn.1
    rw [Mode.limb_mul_ofK] at hx
    simp only [addressOfIndex] at hL2
    rw [slotW_app_get (List.length_map _) (by simpa using hget), wordNf_val hp htop hb hh,
      ← readD_ref hκ hxn.2, ← hx, hL2]
    rfl
  refine ⟨fun o ho ↦ hentry.w o (foldlT_nil_get ho), fun o x hx ↦ (by rw [trieNil_get rfl] at hx; cases hx),
    fun o hx ↦ (by rw [trieNil_get rfl] at hx; cases hx), fun p hp ↦ (by cases hp), fun m hm' ↦ ?_,
    fun r hr ↦ ?_, fun p hp ↦ ?_, fun p hp ↦ (by cases hp), fun c a b hx ↦ (by rw [trieNil_get rfl] at hx; cases hx),
    fun q hq ↦ ?_, fun q hq ↦ (by cases hq)⟩
  · rcases Bool.or_eq_true_iff.mp (hGpre m hm') with hc0 | hc
    swap
    · -- a product over pointer bases: a one-point run over the ghost slots
      rw [Bool.and_eq_true] at hc
      obtain ⟨hbs, h⟩ := hc
      obtain ⟨q, hq, hrq⟩ := List.any_eq_true.mp h
      exact slot_hwL hrq (slotGetL_call hκ hf' hws1 hentry.w hk1 (hentry.w 1 hG1) hcell hcellq
        (fun b hb ↦ List.all_eq_true.mp hbs b hb)) fun x hx ↦ hW x (hrpreR q hq x hx)
    rcases Bool.or_eq_true_iff.mp hc0 with hc | hc
    · obtain ⟨hmS, hc⟩ := Bool.and_eq_true_iff.mp hc
      split at hc
      · rename_i c hmc
        obtain ⟨c', hc', hbeq⟩ := List.any_eq_true.mp hc
        rw [CCell.beq_eq hbeq] at hc'
        exact slot_hw hmc (hSG hmS) (hW _ (hrpre c hc'))
      · cases hc
    · unfold hpIn at hc
      split at hc
      · rename_i q d hqd
        simp only [Bool.and_eq_true] at hc
        obtain ⟨⟨hsl, hcl⟩, hps⟩ := hc
        obtain ⟨p', hp', hpp⟩ := List.any_eq_true.mp hps
        simp only [Bool.and_eq_true, List.contains_iff_mem] at hpp
        obtain ⟨hpb, hko⟩ := hpp
        have h2 : 2 ≤ q := by
          simp only [hpSlot, Bool.and_eq_true, decide_eq_true_eq] at hsl; exact hsl.1.1.1
        obtain ⟨c', hc', hbeq⟩ := List.any_eq_true.mp hcl
        rw [CCell.beq_eq hbeq] at hc'
        rw [hpOf_spec hqd]
        refine hp_hw (s := s') hκ hf'.agree hu h2 (hSG (monoS_fr hsl)) (hW _ (hrpre _ hc')) fun w hw ↦ ?_
        refine hW _ (hrptr _ (Or.inl ⟨p', hp', w, ?_, m.k, hko, rfl⟩))
        rw [CCell.beq_eq hpb, hrd]
        exact hw
      · cases hc
  · rcases List.mem_cons.mp hr with rfl | hr
    · exact hjt
    rcases Bool.or_eq_true_iff.mp (hGpreR r hr) with h0 | h0
    swap
    · -- a run of exponent bounds over pointer bases (`hpBs`), its bounds the arguments' (`boundsX`)
      rw [Bool.and_eq_true, Bool.and_eq_true] at h0
      obtain ⟨⟨hbx, hbs⟩, h⟩ := h0
      obtain ⟨q, hq, hrq⟩ := List.any_eq_true.mp h
      unfold rngLIs at hrq
      split at hrq
      · rename_i q' hq'
        have hqq : q' = q := of_decide_eq_true hrq
        subst hqq
        have hpw := hexR q' hq
        exact slot_rwLX hq' hbx (slotGetL_call hκ hf' hws1 hentry.w hk1 (hentry.w 1 hG1) hcell hcellq
          (fun b hb ↦ List.all_eq_true.mp hbs b hb)) hpw.1 hpw.2
          fun x hx ↦ hW x (hrpreR q' hq x hx)
      · cases hrq
    rcases Bool.or_eq_true_iff.mp h0 with h0 | h0
    swap
    · -- a run of constant bounds over pointer bases (`hpBs`): the caller's cells, the words at arguments' cells
      rw [Bool.and_eq_true, Bool.and_eq_true] at h0
      obtain ⟨⟨hnb, hbs⟩, h⟩ := h0
      obtain ⟨q, hq, hrq⟩ := List.any_eq_true.mp h
      unfold rngLIs at hrq
      split at hrq
      · rename_i q' hq'
        obtain rfl := of_decide_eq_true hrq
        exact slot_rwL hq' hnb (slotGetL_call hκ hf' hws1 hentry.w hk1 (hentry.w 1 hG1) hcell hcellq
          (fun b hb ↦ List.all_eq_true.mp hbs b hb)) fun x hx ↦ hW x (hrpreR q' hq x hx)
      · cases hrq
    rcases Bool.or_eq_true_iff.mp h0 with h0 | h0
    · obtain ⟨hmS, h⟩ := Bool.and_eq_true_iff.mp h0
      rcases Bool.or_eq_true_iff.mp h with h | h
      · obtain ⟨q, hq, hrq⟩ := List.any_eq_true.mp h
        unfold rngIs at hrq
        split at hrq
        · rename_i q' hq'
          obtain rfl := of_decide_eq_true hrq
          exact slot_rw hq' (hSG hmS) fun x hx ↦ hW x (hrpreR q' hq x hx)
        · cases hrq
      · split at h
        · rename_i c l hmc hl
          exact pts_slot hmc hl (hSG hmS) fun p hp ↦ by
            obtain ⟨c', hc', hbeq⟩ := List.any_eq_true.mp (List.all_eq_true.mp h p hp)
            rw [← CCell.beq_eq hbeq]
            exact hW _ (hrpre c' hc')
        · cases h
    · obtain ⟨hmS, h⟩ := Bool.and_eq_true_iff.mp h0
      obtain ⟨q, hq, hrq⟩ := List.any_eq_true.mp h
      unfold rngXIs at hrq
      split at hrq
      · rename_i q' hq'
        have hqq : q' = q := of_decide_eq_true hrq
        subst hqq
        have hpw := hexR q' hq
        exact slot_rwX hq' (hSG hmS) hpw.1 hpw.2 fun x hx ↦ hW x (hrpreR q' hq x hx)
      · cases hrq
  · exact Mode.LTF.mono (s := Mode.stOf s'.mem s'.fp) (s' := s') (Mem.le_refl _) rfl
      (hterm p hp)
  · obtain ⟨⟨hmS, hpr⟩, hrr⟩ := hGpreP q hq
    obtain ⟨p', hp', hpp⟩ := List.any_eq_true.mp hpr
    simp only [prunIs, rngXIs, Bool.and_eq_true, decide_eq_true_eq] at hpp
    obtain ⟨hrq, hos⟩ := hpp
    split at hrq
    · rename_i q' hq'
      have hpq : q' = p'.1 := of_decide_eq_true hrq
      obtain ⟨q2, hq2, hrr'⟩ := List.any_eq_true.mp hrr
      unfold rngXIs at hrr'
      rw [hq'] at hrr'
      have hq2e : q' = q2 := of_decide_eq_true hrr'
      subst hq2e
      have hpw := hexPR p' hp'
      rw [← hpq] at hpw
      refine slot_pwX (s := s') hκ hf'.agree hu hq' (hSG hmS) hpw.1 hpw.2
        (fun x hx ↦ hW x (hrpreR q' hq2 x hx)) fun x hx ↦ ?_
      obtain ⟨a, ha, hpa⟩ := hx
      refine hW x (hrptr x (Or.inr ⟨p', hp', a, ?_⟩))
      rw [← hpq, ← hos, hrd]
      exact ⟨ha, hpa⟩
    · cases hrq

/-- **A call's split, and the callee frame**: the path's events at a call's position are the events up to the
call (`evs`), the call, atoms writing nothing and the rest (`hk`, the pairing's); the call's preconditions
are written by the events before it (`hrw`); the callee frame holds the header and the call's words. -/
theorem call_split {img : MemoryImage κ} (hκ : κ ≤ 28) {Cf : CFun} {s s1 s' : St} {f : String} {args rets : List V}
    {st : B2C.Site} {of : ℕ} {pos' : List Stmt} {as : List Atom} {σ : Val} {pre es : List Ev} {vs : List V}
    {rd : Reader} (hm : Moves (refMem img) s s1) (sof : of < 2 ^ 28)
    (h1 : s1.mem.get (s1.fp + of) = some (ofK (g ^ s'.fp))) (hsite : Cf.X.siteAt of args rets = some st)
    (hσ : HonF img Cf s.fp σ) (hb : walk σ Cf.fn.body = .ret (pre ++ es) vs)
    (hrw : ReadsAt Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) pre es)
    (hk : ∃ (evs : List Ev) (cs : List Atom) (es' : List Ev), es = evs ++ Ev.call f args rets :: (cs.map Ev.atom ++ es') ∧
      walk σ pos' = .ret es' vs ∧ (∀ a ∈ cs, stopL a = false) ∧ (∀ a ∈ as, Ev.atom a ∈ evs) ∧
      (∀ e ∈ evs, EvM Cf.sigOf rd σ e) ∧ ∀ x, WrittenC Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) (pre ++ evs) x →
        WrittenC Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) pre x ∨
        ∃ a ∈ as, flowAtom a = true ∧ Ev.atom a ∈ evs ∧ Writes σ a x) :
    ∃ (evs : List Ev) (cs : List Atom) (es' : List Ev), es = evs ++ Ev.call f args rets :: (cs.map Ev.atom ++ es') ∧
      walk σ pos' = .ret es' vs ∧ (∀ a ∈ cs, stopL a = false) ∧ (∀ a ∈ as, Ev.atom a ∈ evs) ∧
      (∀ e ∈ evs, EvM Cf.sigOf rd σ e) ∧ (∀ x, WrittenC Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) (pre ++ evs) x →
        WrittenC Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) pre x ∨
        ∃ a ∈ as, flowAtom a = true ∧ Ev.atom a ∈ evs ∧ Writes σ a x) ∧
      ReqOk Cf.sigOf Cf.H rd σ (WrittenC Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) (pre ++ evs))
        (.call f args rets) ∧
      ∃ kfp, (g : Parameters.K) ^ s'.fp = g ^ kfp ∧
        (∀ b < args.length + rets.length, Rd img s'.fp (2 + b) = some (slotW ((args ++ rets).map σ) b)) ∧
        Rd img s'.fp 0 = some (ofK (g ^ st.r)) ∧ Rd img s'.fp 1 = some (ofK (g ^ s.fp)) := by
  obtain ⟨evs, cs, es', rfl, hwp', hcs, hasin, hevM, hW'⟩ := hk
  have hreq := hrw evs (.call f args rets) (cs.map Ev.atom ++ es') rfl hevM
  obtain ⟨kfp, hq, hk0, hk1, hargs, hrets⟩ := hσ.kid _ _ hb ((calls (pre ++ evs)).length)
    ⟨f, args, rets, true⟩ of st (by rw [← List.append_assoc]; exact calls_mid) rfl hsite
  have hfpE : (g : Parameters.K) ^ s'.fp = g ^ kfp :=
    (pow_of_ofK (rd_get hκ hm.fine sof (by rw [hm.fp]; exact hq) h1)).symm.symm
  refine ⟨evs, cs, es', rfl, hwp', hcs, hasin, hevM, hW', hreq, kfp, hfpE, fun b hb' ↦ ?_,
    by rw [rd_pow hfpE]; exact hk0, by rw [rd_pow hfpE]; exact hk1⟩
  rw [rd_pow hfpE, List.map_append]
  by_cases hb1 : b < args.length
  · rw [slotW_lt (by simpa using hb1), slotW_get (by simpa using hb1)]
    simpa using hargs b hb1
  · rw [slotW_append]
    simp only [List.length_map, hb1, ↓reduceIte]
    rw [slotW_get (by simp; omega)]
    have := hrets (b - args.length) (by show b - args.length < rets.length; omega)
    rw [show 2 + args.length + (b - args.length) = 2 + b by omega] at this
    simpa using this

/-- **The caller's writes once a call returns**: what its events up to the call wrote (`hW`, `hW'`: or a hint's
flow), the callee's guarantees (`hcall`), atoms after the call writing nothing. -/
theorem resume_wrk {img : MemoryImage κ} (hκ : κ ≤ 28) {Cf : CFun} {C : Ctx} {hl : List Prover.Exec.Hint}
    {s s1 : St} {m' : Mem} {σ : Val} {rd : Reader} {pre evs es' : List Ev} {cs as : List Atom} {vs : List V}
    {f : String} {args rets : List V} {y : K} (hs : Fine (refMem img) s) (hm : Moves (refMem img) s s1)
    (hle0 : s.mem ≤ m') (hle1 : s1.mem ≤ m') (e1 : hl.foldlM (Prover.Exec.runHint C) s = .ok s1)
    (hpairs : List.Forall₂ (Pairs Cf.X) (as.filter flowAtom) (hl.filter isaFlowHint)) (hσ : HonF img Cf s.fp σ)
    (hb : walk σ Cf.fn.body = .ret (pre ++ (evs ++ Ev.call f args rets :: (cs.map Ev.atom ++ es'))) vs)
    (hW : ∀ x, WrittenC Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) pre x → WrK s.mem x)
    (hW' : ∀ x, WrittenC Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) (pre ++ evs) x →
      WrittenC Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) pre x ∨ ∃ a ∈ as, flowAtom a = true ∧ Ev.atom a ∈ evs ∧ Writes σ a x)
    (hcs : ∀ a ∈ cs, stopL a = false) (hcall : EvW Cf.sigOf rd σ (.call f args rets) y → WrK m' y)
    (hy : WrittenC Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) (pre ++ evs ++ Ev.call f args rets :: cs.map Ev.atom) y) :
    WrK m' y := by
  rcases writtenC_append hy with h | ⟨e, he, hwe⟩
  · rcases hW' y h with h | ⟨a, ha, hfa, hma, hwa⟩
    · exact (hW y h).mono hle0
    · exact (flow_wrk hκ e1 hs hm hpairs ha hfa (fun q hq ↦ hσ.ptr _ _ hb a q
        (List.mem_append_right _ (List.mem_append_left _ hma)) hq) hwa).mono hle1
  rcases List.mem_cons.mp he with rfl | he
  · exact hcall hwe
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
    exact absurd hwe (no_writes_of_stopL (hcs a ha))

end

end LeanVM.Guest.CoreMode
