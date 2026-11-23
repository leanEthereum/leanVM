/-
  LeanVM.Guest.CoreMode.CoreFacts

  The core route's frame interface, its first part: the heap facts and the body's values.
-/

module

public import LeanVM.Guest.CoreMode.CoreSlot
public import LeanVM.Guest.CoreMode.CorePtr
public import LeanVM.Guest.CoreMode.CoreLink
public import LeanVM.Guest.CoreMode.Core
public import LeanVM.Guest.CoreMode.WalkS
public import LeanVM.Guest.TrieFacts

/-!
# The heap facts and the body's values

The first part of `frameSpec_core` (`CoreSound.lean`): the heap facts (`heapK_sound`: `heapOk` or the check with calls give every event's needs written before it and the promised cells written by the end), the products promised at the return, and the guarantees over the body's values and its returned products.
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

/-! ## Tries -/

theorem foldlT_cons (t : Exec.Trie Unit) (a : ℕ) (l : List ℕ) :
    Mode.foldlT t (a :: l) = Mode.foldlT (t.set () Exec.envDepth a) l := by
  show (t.set () Exec.envDepth a).seq _ = _
  rw [Exec.Trie.seq_eq]
  rfl

theorem foldlT_keep : ∀ (l : List ℕ) (t : Exec.Trie Unit) {o : ℕ}, (∀ x ∈ l, x + 1 < 2 ^ Exec.envDepth) →
    t.get o = some () → (Mode.foldlT t l).get o = some ()
  | [], _, _, _, h => h
  | a :: l, t, o, hl, h => by
    rw [foldlT_cons]
    refine foldlT_keep l _ (fun x hx ↦ hl x (List.mem_cons_of_mem _ hx)) ?_
    rw [Check.get_set_eq () _ t a o (hl a List.mem_cons_self)]
    split_ifs <;> simp [h]

theorem foldlT_mem : ∀ (l : List ℕ) (t : Exec.Trie Unit) {o : ℕ}, (∀ x ∈ l, x + 1 < 2 ^ Exec.envDepth) →
    o ∈ l → (Mode.foldlT t l).get o = some ()
  | [], _, _, _, h => absurd h List.not_mem_nil
  | a :: l, t, o, hl, h => by
    rw [foldlT_cons]
    rcases List.mem_cons.mp h with rfl | h
    · refine foldlT_keep l _ (fun x hx ↦ hl x (List.mem_cons_of_mem _ hx)) ?_
      rw [Check.get_set_eq () _ t o o (hl o List.mem_cons_self)]
      simp
    · exact foldlT_mem l _ (fun x hx ↦ hl x (List.mem_cons_of_mem _ hx)) h

theorem trieNil_get {α : Type} {t : Exec.Trie α} (h : trieNil t = true) (n : ℕ) : t.get n = none := by
  cases t with
  | nil => rfl
  | node => simp [trieNil] at h

theorem tgtIn_of_none {o : ℕ} (ho : o ≠ 0) : ∀ {t : Exec.Trie B2C.Site}, tgtNone t = true → tgtIn o t = false
  | .nil, _ => rfl
  | .node v l r, h => by
    have h' : (siteTgt true 0 v && tgtNone l && tgtNone r) = true := h
    simp only [Bool.and_eq_true] at h'
    obtain ⟨⟨hv, hl⟩, hr⟩ := h'
    show (siteTgt false o v || tgtIn o l || tgtIn o r) = false
    rw [tgtIn_of_none ho hl, tgtIn_of_none ho hr]
    cases v with
    | none => rfl
    | some s =>
      simp only [siteTgt, Nat.beq_eq] at hv ⊢
      simp only [hv, Bool.or_false]
      cases o with
      | zero => exact absurd rfl ho
      | succ n => rfl

theorem has_hasP {t : Exec.Trie Unit} {i : ℕ} : has t i = hasP t i := by
  simp only [has, hasP, Check.getF_eq]

/-! ## The checks' conjuncts, by name -/

/-- **`fitB`'s conjuncts**, by name. -/
structure FitB (G : Mode.Sig) (h : HSig) (na nr : ℕ) : Prop where
  self : (match G.self with
    | some o => decide (o < 2 ^ 28)
    | none => true) = true
  preP : (G.preP.all fun r ↦ monoS G na true (rngM r.1) && h.prePR.any (prunIs r ·) && h.preR.any (rngXIs r.1 ·)) = true
  ent0 : G.entry.contains 0 = true
  ent1 : G.entry.contains 1 = true
  postP : h.postP.all (fun p ↦ hpAll G (na + nr) G.post p || hpRunIn G (na + nr) p) = true
  postPR : (h.postPR.all fun p ↦ (G.postP ++ G.postLP).any fun r ↦
    monoS G (na + nr) false (rngM r.1) && prunIs r p) = true
  retM : h.retM.all (retMIn G na nr) = true
  postQ : h.postQ.all (rngQIn G (na + nr)) = true
  pre : G.pre.all (fun m ↦ (monoS G na true m && match monoC m with
    | some c => cellIn c h.pre
    | none => false) || hpIn G na true h.preP h.pre m ||
    (m.bs.all (baseC1 G na (hpBs G) ·.1) && h.preR.any (ptLIs (glOfs na (hpBs G)) (gpOfs na (hpBs G)) m ·))) = true
  pb : (hpBs G).all (fun p ↦ Nat.beq p.1 1 || cellIn ⟨[(p.1 - 2, 1)], p.2⟩ h.pre) = true
  preR : G.preR.all (fun r ↦ (monoS G na true r.q && ((h.preR.any fun q ↦ rngIs r q) ||
    match monoC r.q, runPts ⟨[], 0⟩ r with
    | some c, some l => l.all fun p ↦ cellIn ⟨c.bases, c.off + p.off⟩ h.pre
    | _, _ => false)) || (monoS G na true (rngM r) && h.preR.any (rngXIs r ·)) ||
    (numB r && r.q.bs.all (baseC1 G na (hpBs G) ·.1) &&
      h.preR.any (rngLIs (glOfs na (hpBs G)) (gpOfs na (hpBs G)) r ·)) ||
    (boundsX r && (rngM r).bs.all (baseC1 G na (hpBs G) ·.1) &&
      h.preR.any (rngLIs (glOfs na (hpBs G)) (gpOfs na (hpBs G)) r ·))) = true
  post : h.post.all (fun c ↦ G.post.any (fun m ↦ monoS G (na + nr) false m && monoIs m c) ||
    G.postR.any fun r ↦ monoS G (na + nr) false r.q && ptIn c r) = true
  postR : allAnyPos (fun r q ↦ (monoS G (na + nr) false r.q && rngIs r q) ||
    (monoS G (na + nr) false (rngM r) && rngXIs r q) ||
    (monoS G (na + nr) false (rngM r) && rngXExt G (na + nr) G.post r q)) (G.postR ++ G.postL) h.postR = true
  ghosts : Nat.beq h.ghosts (hpBs G).length = true

theorem FitB.of_ok {G : Mode.Sig} {h : HSig} {na nr : ℕ} (hf : fitB G h na nr = true) : FitB G h na nr := by
  simp only [fitB, Bool.and_eq_true] at hf
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, ⟨h7, h8⟩⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩ := hf
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

/-- **`sigOk`'s conjuncts**, by name. -/
structure SigOkP (G : Mode.Sig) (Cf : CFun) (np nr : ℕ) (jt : Mode.Rng) : Prop where
  self : G.self.isNone = true
  term : G.term.isEmpty = true
  postL : G.postL.isEmpty = true
  postP : (G.postP.all fun r ↦ monoR G np nr (rngM r.1) && expI G Cf.H.res np (np + nr) r.1.lo &&
    expI G Cf.H.res np (np + nr) r.1.hi &&
    Cf.H.sig.postPR.any (prunIs r ·) && Cf.H.sig.postR.any (rngXIs r.1 ·)) = true
  postLP : G.postLP.isEmpty = true
  postT : G.postT.isEmpty = true
  postC : G.postC.isEmpty = true
  preP : Cf.H.sig.preP.all (hpAll G np G.pre) = true
  prePR : (Cf.H.sig.prePR.all fun p ↦ G.preP.any fun r ↦ monoS G np false (rngM r.1) && prunIs r p) = true
  pre : preCov G np (Cf.H.sig.pre.filter fun c ↦ !mainPre Cf G c) = true
  preR : Cf.H.sig.preR.all (fun q ↦ ((jt :: G.preR).any fun r ↦ (monoS G np false r.q && rngIs r q) ||
    (monoS G np false (rngM r) && rngXIs r q) || ((rngM r).bs.all (baseS Cf.gl (gpOf np Cf.H.sig.gw) np ·.1) &&
      rngLIs Cf.gl (gpOf np Cf.H.sig.gw) r q)) || runCov G np q ||
    G.pre.any fun m ↦ m.bs.all (baseS Cf.gl (gpOf np Cf.H.sig.gw) np ·.1) && ptLIs Cf.gl (gpOf np Cf.H.sig.gw) m q) = true
  post : G.post.all (fun m ↦ (monoR G np nr m && match monoC m with
    | some c => cellIn c Cf.posts
    | none => false) || postIn Cf.X Cf.fn.body G np (Cf.post.map (·.1)) m ||
    hpIn G np true Cf.H.sig.postP Cf.posts m || postNIn Cf.X Cf.fn.body G np Cf.H.sig m) = true
  postR : (G.postR.all fun r ↦ (monoR G np nr r.q && ((Cf.H.sig.postR.any fun q ↦ rngIs r q) ||
    match monoC r.q, runPts ⟨[], 0⟩ r with
    | some c, some l => l.all fun p ↦ cellIn ⟨c.bases, c.off + p.off⟩ Cf.posts
    | _, _ => false)) || postRIn Cf.X Cf.fn.body G np (Cf.post.map (·.1)) r ||
    (monoR G np nr (rngM r) && expI G Cf.H.res np (np + nr) r.lo && expI G Cf.H.res np (np + nr) r.hi &&
      Cf.H.sig.postR.any (rngXIs r ·)) || postRB G Cf np r || postRNIn Cf.X Cf.fn.body G np Cf.H r) = true
  ghosts : Nat.ble Cf.H.sig.ghosts (Cf.gl.length + Cf.H.sig.gw.length) = true
  gw : (Cf.H.sig.gw.all fun x ↦ Nat.blt x.2 Cf.H.sig.ghosts && match x.1.bases with
    | [(p, 1)] => Nat.blt p np
    | _ => false) = true

theorem SigOkP.of_ok {G : Mode.Sig} {Cf : CFun} {np nr : ℕ} {jt : Mode.Rng} (h : sigOk G Cf np nr jt = true) :
    SigOkP G Cf np nr jt := by
  simp only [sigOk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩, h15⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩

/-! ## The shape -/

theorem retsN_len {σ : Val} {body : List Stmt} {n : ℕ} (hn : retsN n (stmtsOf body) = true)
    {es : List Ev} {vs : List V} (hw : walk σ body = .ret es vs) : vs.length = n := by
  have h := List.all_eq_true.mp hn _ (Bridge.walk_retS body hw)
  simpa using h

theorem calls_mid {a b : List Ev} {f : String} {args rets : List V} :
    (calls (a ++ Ev.call f args rets :: b))[(calls a).length]? = some ⟨f, args, rets, true⟩ := by
  simp [calls, List.filterMap_append, Ev.call?]

theorem foldlT_nil_get {l : List ℕ} {o : ℕ} (h : (Mode.foldlT .nil l).get o = some ()) : o ∈ l := by
  rw [Mode.foldlT_eq] at h
  rcases get_foldl_set_unit l .nil h with h | h
  · exact h
  · cases h

theorem slotW_params' {σ : Val} {ps : List V} (hp : ps = (List.range ps.length).map V.n) {b : ℕ}
    (hb : b < ps.length) : slotW (ps.map σ) b = σ (V.n b) := by
  rw [hp, List.map_map]
  exact slotW_params hb

theorem ownG_zero {G : HSig} (h : G.ghosts = 0) (σ : Val) : ownG G σ = [] := by
  simp [ownG, h]

theorem slotW_lt {ws ws' : List E} {b : ℕ} (hb : b < ws.length) : slotW (ws ++ ws') b = slotW ws b := by
  rw [slotW_append]; simp [hb]

theorem slotW_get {ws : List E} {b : ℕ} (hb : b < ws.length) : slotW ws b = ws[b] := by
  unfold slotW
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb, Option.getD_some]

/-- **The reference's word at cell `x`**, read at its address (`0` past the image). -/
theorem readD_ref {img : MemoryImage κ} (hκ : κ ≤ 28) {x : ℕ} (hx : x < maxCells) :
    (img.read (g ^ x)).getD 0 = refMem img x := by
  unfold maxCells at hx
  cases h : img.read (g ^ x) with
  | some v =>
    obtain ⟨i, hi, hv⟩ := (MemoryImage.read_eq_some_iff (by omega) img).mp h
    have hi' : (i : ℕ) < 2 ^ 28 := lt_of_lt_of_le i.isLt (Nat.pow_le_pow_right (by norm_num) hκ)
    have hxi : x = i := gpow_inj (by omega) (by omega) hi
    subst hxi
    simp [refMem, i.isLt, ← hv]
  | none =>
    by_cases hk : x < 2 ^ κ
    · rw [MemoryImage.read_eq_none_iff] at h
      exact absurd rfl (h ⟨x, hk⟩)
    · simp [refMem, hk]

/-- **An honest frame's own parameter words** (`HonF.gw`, `HonB.par`) at the bases `gpOf` names, its ghost words
after its parameters: `GpF`. -/
theorem gpF_of {img : MemoryImage κ} (hκ : κ ≤ 28) {Cf : CFun} {fp : ℕ} {σ : Val} (hσ : HonF img Cf fp σ)
    (hgw : ∀ x ∈ Cf.H.sig.gw, x.2 < Cf.H.sig.ghosts ∧ ∀ p, x.1.bases = [(p, 1)] → p < Cf.fn.params.length) :
    GpF img (gpOf Cf.fn.params.length Cf.H.sig.gw) fp (Cf.fn.params.map σ ++ ownG Cf.H.sig σ) := by
  intro q d b hl
  obtain ⟨⟨c, j⟩, hx, hm⟩ := List.mem_filterMap.mp (lookup_memL hl)
  obtain ⟨hj, hp⟩ := hgw _ hx
  split at hm
  · rename_i p hb
    simp only [Option.some.injEq, Prod.mk.injEq] at hm
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hm
    have hpl := hp p hb
    refine ⟨σ (V.n p), hσ.par p hpl, fun x hn ↦ ?_⟩
    rw [slotW_append]
    split_ifs with h0
    · simp at h0
    rw [List.length_map, show Cf.fn.params.length + j - Cf.fn.params.length = j by omega]
    rw [slotW_get (by simp [ownG]; exact hj)]
    simp only [ownG, List.getElem_map, List.getElem_range]
    rw [hσ.gw c j hx]
    have hb' : c.bases = [(p, 1)] := hb
    have ha : c.addrW (vw σ) = g ^ x := by
      rw [← hn.1]
      simp [CCell.addrW, CCell.valW, hb', prodW, vw, addressOfIndex]
    rw [ha, readD_ref hκ hn.2]
  · cases hm

theorem rd_pow {img : MemoryImage κ} {a b : ℕ} (h : (g : K) ^ a = g ^ b) (o : ℕ) : Rd img a o = Rd img b o := by
  simp only [Rd, h]

theorem pow_of_ofK {a b : ℕ} (h : ofK ((g : K) ^ a) = ofK (g ^ b)) : (g : K) ^ a = g ^ b :=
  ofK_injective h

/-! ## The heap facts -/

/-- A body without `frameAddr` atoms guarantees no frame run cell (`FAW`). -/
theorem noFAW {body : List Stmt} (h : noFA body = true) {σ : Val} {es : List Ev} {vs : List V}
    (hw : walk σ body = .ret es vs) {fas : List (ℕ × ℕ)} (x : K) : ¬ FAW σ fas es x := by
  rintro (⟨p, run, i, v, he, -⟩ | ⟨kp, i, run, -, he, -⟩) <;>
  · have hs := Bridge.walk_atomS body (by rw [hw]; exact he)
    have := List.all_eq_true.mp h _ hs
    simp at this

theorem postOkW_of {sigOf : String → HSig} {H : HCert} {rd : Reader} {σ : Val} {ws0 : List E} {es : List Ev}
    {vs : List V} (hn : ∀ x, ¬ FAW σ H.fas es x) (h : PostOkC sigOf H rd σ ws0 es vs) :
    PostOkW sigOf H rd σ ws0 es vs :=
  ⟨h.1.mono fun x hx ↦ hx.resolve_right (hn x), fun x hx ↦ (h.2.1 x hx).resolve_right (hn x),
    fun x hx ↦ (h.2.2.1 x hx).resolve_right (hn x), h.2.2.2.mono fun x hx ↦ hx.resolve_right (hn x)⟩

/-- A call needs its callee's preconditions written, no word at a cell (`HCert.ders`) among its ghosts. -/
theorem callReq_pre {sigOf : String → HSig} {H : HCert} {rd : Reader} {σ : Val} {W : K → Prop} {g : String}
    {args : List V} (hd : H.ders = []) (h : CallReq sigOf H rd σ W g args) : CallPre sigOf H rd σ W g args :=
  h.2 fun k _ c hc ↦ by rw [hd] at hc; cases hc

/-- What made a call event of a body the core route takes: a `call` statement, or a `callIf`
returning nothing. -/
theorem body_callS {body : List Stmt} (_hb : bodyCore body = true) {σ : Val} {es : List Ev} {vs : List V}
    (hw : walk σ body = .ret es vs) {f : String} {a r : List V} (he : Ev.call f a r ∈ es) :
    Stmt.call f a r ∈ stmtsOf body ∨ (r = [] ∧ ∃ c, Stmt.callIf c f a ∈ stmtsOf body) ∨
      ∃ x fs, Stmt.dispatch x fs a r ∈ stmtsOf body ∧ f ∈ fs := by
  obtain ⟨t, ht, hc⟩ := Bridge.walk_callS body (by rw [hw]; exact he)
  cases t with
  | call g a' r' =>
    simp only [Bridge.CallS] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact Or.inl ht
  | callIf c g a' =>
    simp only [Bridge.CallS] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact Or.inr (Or.inl ⟨rfl, c, ht⟩)
  | dispatch x fs a' r' =>
    simp only [Bridge.CallS] at hc
    obtain ⟨hf, rfl, rfl⟩ := hc
    exact Or.inr (Or.inr ⟨x, fs, ht, hf⟩)
  | _ => simp [Bridge.CallS] at hc

/-- A call of the body passes `callChk`. -/
theorem callsB_chk {Cf : CFun} (hcb : callsB Cf = true) {f : String} {a r : List V}
    (hs : Stmt.call f a r ∈ stmtsOf Cf.fn.body ∨ (r = [] ∧ ∃ c, Stmt.callIf c f a ∈ stmtsOf Cf.fn.body) ∨
      ∃ x fs, Stmt.dispatch x fs a r ∈ stmtsOf Cf.fn.body ∧ f ∈ fs) :
    callChkM Cf f a = true := by
  rcases hs with hs | ⟨-, c, hs⟩ | ⟨x, fs, hs, hf⟩
  · exact List.all_eq_true.mp hcb _ hs
  · exact List.all_eq_true.mp hcb _ hs
  · have := List.all_eq_true.mp hcb _ hs
    simp only [Bool.and_eq_true] at this
    exact List.all_eq_true.mp this.1 f hf

/-- **A guarantee written at return**: by the events, or a frame run's cell where frame run cells are guaranteed
(`faNeed`; written by the walk's facts at the returns, `faw_wrk`). -/
def WrF (Cf : CFun) (rd : Reader) (σ : Val) (es : List Ev) (x : K) : Prop :=
  WrittenC Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) es x ∨ (faNeed Cf = true ∧ FAW σ Cf.H.fas es x)

theorem heapOkC_params {pows : Exec.PowTree} {sigOf : String → HSig} {f : Fn} {H : HCert}
    (h : heapOkC pows sigOf f H = true) : f.params = (List.range f.params.length).map V.n := by
  unfold heapOkC at h
  simp only [Bool.and_eq_true] at h
  rw [List.range_eq_range']; exact paramsN_eq _ 0 h.1.1.1.1.1

/-- **The heap facts of an honest path**, each call's callee's returned words given: its parameters `V.n k`;
every event's needs written before it; the promised cells and the signature's runs written by the end, at the
parameters' and returned words; the returned words' monomials, words and equations. -/
theorem heapK_sound {Cf : CFun} (hk : HeapK Cf) (hp : Cf.pows.Ok) (hst : bodyCore Cf.fn.body = true) {σ : Val}
    {rd : Reader} {es : List Ev} {vs : List V} (hw : walk σ Cf.fn.body = .ret es vs) (hh : ∀ e ∈ es, e.Holds rd σ)
    (hR : ResF Cf.H σ) (hG : GwOk Cf.H.sig rd σ) (hM : ∀ e ∈ es, EvM Cf.sigOf rd σ e) :
    Cf.fn.params = (List.range Cf.fn.params.length).map V.n ∧
    ReadsOkC Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) es ∧
    (∀ c ∈ Cf.posts, WrF Cf rd σ es (c.addrW (slotW (Cf.fn.params.map σ ++ vs.map σ)))) ∧
    (∀ r ∈ Cf.H.sig.postR, ∀ x, r.Set (slotW (Cf.fn.params.map σ ++ vs.map σ)) x → WrF Cf rd σ es x) ∧
    RetMOk Cf.H.sig (Cf.fn.params.map σ) (vs.map σ) ∧
    (∀ p ∈ Cf.post, WrittenC Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) es (p.1.addr σ)) ∧
    PtrOk (WrF Cf rd σ es) rd Cf.H.sig.postP Cf.H.sig.postPR (Cf.fn.params.map σ ++ vs.map σ) ∧
    (∀ x, QSet rd Cf.H.sig.postQ (Cf.fn.params.map σ ++ vs.map σ) x → WrF Cf rd σ es x) ∧
    RetVOk rd Cf.H.sig (Cf.fn.params.map σ ++ vs.map σ) ∧ RetEqOk Cf.H.sig (Cf.fn.params.map σ ++ vs.map σ) ∧
    SigOk (WrF Cf rd σ es) Cf.H.sig.postN Cf.H.sig.postRN (Cf.H.sig.nv.map (vw σ)) := by
  cases hk with
  | m1 hok hpo hstr0 hrm hpv hre =>
    simp only [Bool.and_eq_true, List.isEmpty_iff] at hstr0
    obtain ⟨⟨⟨⟨⟨hstr, hpP⟩, hpPR⟩, hpQ⟩, hN1⟩, hN2⟩ := hstr0
    have hok' := hok
    unfold heapOk at hok'
    simp only [Bool.and_eq_true] at hok'
    obtain ⟨⟨⟨hpar, hpre⟩, hpts⟩, -⟩ := hok'
    have hpar' : Cf.fn.params = (List.range Cf.fn.params.length).map V.n := by
      rw [List.range_eq_range']; exact paramsN_eq _ 0 hpar
    simp only [HSig.pointsOnly, Bool.and_eq_true, List.isEmpty_iff] at hpts
    obtain ⟨⟨⟨hpost, -⟩, hpostR⟩, -⟩ := hpts
    have hrw := heapOk_sound hp hok hw hh
    have hconv : ∀ es1 x, Written Cf.H σ es1 x → WrittenC Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) es1 x := by
      rintro es1 x (⟨c, hc, rfl⟩ | ⟨a, ha, hwa⟩)
      · exact Or.inl (Or.inl (Or.inl ⟨c, hc, addr_pre hpar' hpre hc _⟩))
      · exact Or.inr ⟨.atom a, ha, hwa⟩
    refine ⟨hpar', fun es1 e es2 he ↦ ?_, fun c hc ↦ Or.inl ?_, fun r hr ↦ (by rw [hpostR] at hr; cases hr),
      fun k c hkc ↦ (by rw [hrm] at hkc; cases hkc), fun p hp' ↦ hconv _ _ (postOk_sound hp hpo hw hh p hp'),
      ⟨fun x hx ↦ (by
        rcases hx with ⟨p, hp', -⟩ | ⟨p, hp', -⟩
        · rw [hpP] at hp'; cases hp'
        · rw [hpPR] at hp'; cases hp'),
      fun x ⟨p, hp', _⟩ ↦ (by rw [hpQ] at hp'; cases hp'),
      fun i m him ↦ (by rw [hpv] at him; cases him), fun p hp' ↦ (by rw [hre] at hp'; cases hp'),
      by rw [hN1, hN2]; exact ⟨fun _ hc ↦ (by cases hc), fun _ hr ↦ (by cases hr)⟩⟩⟩
    · cases e with
      | atom a => exact fun x hr ↦ hconv _ _ (hrw es1 a es2 x he hr)
      | call f args rets =>
        rcases body_callS hst hw (by rw [he]; exact List.mem_append_right _ List.mem_cons_self) with h | ⟨-, c, h⟩ | ⟨x, fs, h, -⟩ <;>
          simpa [isCall] using List.all_eq_true.mp hstr _ h
      | _ => trivial
    · simp only [CFun.posts, hpost, List.append_nil, List.mem_filter] at hc
      obtain ⟨hc, hpov⟩ := hc
      obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hc
      have h1 := hconv _ _ (postOk_sound hp hpo hw hh p hp')
      have hv : p.1.addrW (slotW (Cf.fn.params.map σ ++ vs.map σ)) = p.1.addrW (slotW (Cf.fn.params.map σ)) := by
        unfold CCell.addrW
        rw [valW_congr fun b hb ↦ ?_]
        have := List.all_eq_true.mp (List.all_eq_true.mp hpov p.1 List.mem_cons_self) b hb
        exact slotW_lt (by simpa using Nat.blt_eq.mp this)
      have ha := addr_pre (σ := σ) hpar' hpov List.mem_cons_self []
      rw [List.append_nil] at ha
      rw [hv, ha]
      exact h1
  | c hok hterm hcb hpost hders =>
    have hpar' := heapOkC_params hok
    have hself : Cf.sigOf Cf.fn.name = Cf.H.sig := by simp [CFun.sigOf]
    obtain ⟨hreads, hpo, hretm, hrv, hre⟩ := heapOkC_sound hp hok hself hw hh hM
      (fun p hp ↦ (by rw [hterm] at hp; cases hp)) hR (derOk_nil hders rd σ) hG
    have hW : SigOk (WrF Cf rd σ es) Cf.H.sig.post Cf.H.sig.postR (Cf.fn.params.map σ ++ vs.map σ) ∧
        PtrOk (WrF Cf rd σ es) rd Cf.H.sig.postP Cf.H.sig.postPR (Cf.fn.params.map σ ++ vs.map σ) ∧
        (∀ x, QSet rd Cf.H.sig.postQ (Cf.fn.params.map σ ++ vs.map σ) x → WrF Cf rd σ es x) ∧
        SigOk (WrF Cf rd σ es) Cf.H.sig.postN Cf.H.sig.postRN (Cf.H.sig.nv.map (vw σ)) := by
      cases hn : faNeed Cf
      · have hnofa : (noFA Cf.fn.body || noPost Cf.H.sig || Cf.H.fas.isEmpty) = true := by
          unfold faNeed at hn
          revert hn
          cases (noFA Cf.fn.body || noPost Cf.H.sig || Cf.H.fas.isEmpty) <;> simp
        have hW : PostOkW Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) es vs := by
          rcases Bool.or_eq_true_iff.mp hnofa with h | h
          · rcases Bool.or_eq_true_iff.mp h with h | h
            · exact postOkW_of (noFAW h hw) hpo
            simp only [noPost, Bool.and_eq_true, List.isEmpty_iff] at h
            obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
            refine ⟨⟨fun c hc ↦ by simp [h1] at hc, fun r hr ↦ by simp [h2] at hr⟩, fun x hx ↦ ?_,
              fun x ⟨p, hp', _⟩ ↦ by simp [h5] at hp', fun c hc ↦ by simp [h6] at hc, fun r hr ↦ by simp [h7] at hr⟩
            simp [PtrSigSet, h3, h4] at hx
          · exact heapOkC_soundW hp hok hself hw hh hM (fun p hp ↦ (by rw [hterm] at hp; cases hp)) hR
              (derOk_nil hders rd σ) hG (List.isEmpty_iff.mp h)
        exact ⟨hW.1.mono fun x hx ↦ Or.inl hx, fun x hx ↦ Or.inl (hW.2.1 x hx), fun x hx ↦ Or.inl (hW.2.2.1 x hx),
          hW.2.2.2.mono fun x hx ↦ Or.inl hx⟩
      · exact ⟨hpo.1.mono fun x hx ↦ hx.imp_right fun h ↦ ⟨hn, h⟩,
          fun x hx ↦ (hpo.2.1 x hx).imp_right fun h ↦ ⟨hn, h⟩,
          fun x hx ↦ (hpo.2.2.1 x hx).imp_right fun h ↦ ⟨hn, h⟩,
          hpo.2.2.2.mono fun x hx ↦ hx.imp_right fun h ↦ ⟨hn, h⟩⟩
    obtain ⟨⟨hpc, hpr⟩, hptr, hq, hN⟩ := hW
    refine ⟨hpar', hreads, fun c hc ↦ ?_, fun r hr x hx ↦ hpr r hr x hx, hretm,
      fun p hp' ↦ (by rw [hpost] at hp'; cases hp'), hptr, hq, hrv, hre, hN⟩
    simp only [CFun.posts, hpost, List.map_nil, List.filter_nil, List.nil_append] at hc
    exact hpc c hc

/-- **Every event's needs on an honest path are written before it**, once the calls before it have their
callees' returned words. -/
theorem heapK_reads {Cf : CFun} (hk : HeapK Cf) (hp : Cf.pows.Ok) (hst : bodyCore Cf.fn.body = true) {σ : Val}
    {rd : Reader} {es : List Ev} {vs : List V} (hw : walk σ Cf.fn.body = .ret es vs) (hh : ∀ e ∈ es, e.Holds rd σ)
    (hR : ResF Cf.H σ) (hG : GwOk Cf.H.sig rd σ) : ReadsOkP Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) es := by
  cases hk with
  | m1 hok hpo hstr0 hrm hpv hre =>
    have hM : ∀ e ∈ es, EvM Cf.sigOf rd σ e := fun e he ↦ by
      cases e with
      | call f args rets =>
        simp only [Bool.and_eq_true] at hstr0
        rcases body_callS hst hw he with h | ⟨-, c, h⟩ | ⟨x, fs, h, -⟩ <;>
          simpa [isCall] using List.all_eq_true.mp hstr0.1.1.1.1.1 _ h
      | _ => trivial
    exact fun es1 e es2 he _ ↦
      (heapK_sound (.m1 hok hpo hstr0 hrm hpv hre) hp hst hw hh hR hG hM).2.1 es1 e es2 he
  | c hok hterm hcb hpost hders =>
    exact (heapOkC_soundP hp hok (by simp [CFun.sigOf]) hw hh
      (fun p hp ↦ (by rw [hterm] at hp; cases hp)) hR (derOk_nil hders rd σ) hG).1

/-- A path through a call: the function's heap check is the one with calls. -/
theorem callsB_of {Cf : CFun} (hk : HeapK Cf) (hst : bodyCore Cf.fn.body = true) {σ : Val} {es : List Ev}
    {vs : List V} (hw : walk σ Cf.fn.body = .ret es vs) {f : String} {args rets : List V}
    (he : Ev.call f args rets ∈ es) : callsB Cf = true := by
  cases hk with
  | m1 _ _ hstr0 _ _ _ =>
    simp only [Bool.and_eq_true] at hstr0
    rcases body_callS hst hw he with h | ⟨-, c, h⟩ | ⟨x, fs, h, -⟩ <;>
      simpa [isCall] using List.all_eq_true.mp hstr0.1.1.1.1.1 _ h
  | c _ _ hcb _ _ => exact hcb

theorem callsB_of' {Cf : CFun} (hk : HeapK Cf) : callsB Cf = true := by
  cases hk with
  | m1 _ _ hstr0 _ _ _ =>
    simp only [Bool.and_eq_true] at hstr0
    refine List.all_eq_true.mpr fun s hs ↦ ?_
    have := List.all_eq_true.mp hstr0.1.1.1.1.1 s hs
    cases s <;> simp_all [isCall]
  | c _ _ hcb _ _ => exact hcb

/-- A path through a call: no word at a cell among the heap certificate's ghosts. -/
theorem ders_of {Cf : CFun} (hk : HeapK Cf) (hst : bodyCore Cf.fn.body = true) {σ : Val} {es : List Ev}
    {vs : List V} (hw : walk σ Cf.fn.body = .ret es vs) {f : String} {args rets : List V}
    (he : Ev.call f args rets ∈ es) : Cf.H.ders = [] := by
  cases hk with
  | m1 _ _ hstr0 _ _ _ =>
    simp only [Bool.and_eq_true] at hstr0
    rcases body_callS hst hw he with h | ⟨-, c, h⟩ | ⟨x, fs, h, -⟩ <;>
      simpa [isCall] using List.all_eq_true.mp hstr0.1.1.1.1.1 _ h
  | c _ _ _ _ hd => exact hd

/-- **A call's callee runs' bounds have exponents** (`callsB`'s `idxPow`). -/
theorem callsB_spec {Cf : CFun} (hcb : callsB Cf = true) {f : String} {args rets : List V}
    (hs : Stmt.call f args rets ∈ stmtsOf Cf.fn.body ∨
      (rets = [] ∧ ∃ c, Stmt.callIf c f args ∈ stmtsOf Cf.fn.body) ∨
      ∃ x fs, Stmt.dispatch x fs args rets ∈ stmtsOf Cf.fn.body ∧ f ∈ fs) :
    (∀ q ∈ (Cf.sigOf f).preR, (idxPowG Cf f args q.lo && idxPowG Cf f args q.hi) = true) ∧
    ∀ p ∈ (Cf.sigOf f).prePR, (idxPowG Cf f args p.1.lo && idxPowG Cf f args p.1.hi) = true := by
  have := callsB_chk hcb hs
  simp only [callChkM, Bool.and_eq_true] at this
  exact ⟨List.all_eq_true.mp this.1.2, List.all_eq_true.mp this.2⟩

theorem forall₂_mem {α β : Type} {R : α → β → Prop} : ∀ {l1 : List α} {l2 : List β}, List.Forall₂ R l1 l2 →
    ∀ a ∈ l1, ∃ b ∈ l2, R a b
  | _, _, .nil, _, ha => absurd ha List.not_mem_nil
  | _, _, .cons h t, a, ha => by
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨_, List.mem_cons_self, h⟩
    · obtain ⟨b, hb, hr⟩ := forall₂_mem t a ha
      exact ⟨b, List.mem_cons_of_mem _ hb, hr⟩

theorem lookupD_hintsAt (x : ℕ) : ∀ l : List (ℕ × List Prover.Exec.Hint), (l.lookup x).getD [] = Mode.hintsAt l x
  | [] => rfl
  | (k, v) :: l => by
    unfold Mode.hintsAt
    rw [List.lookup_cons, List.find?_cons]
    by_cases h : x = k
    · subst h; simp
    · rw [beq_false_of_ne h, beq_false_of_ne (Ne.symm h)]
      exact lookupD_hintsAt x l

/-! ## Promised products, at the return -/

/-- The bases `bs` translated by `f` into powers of core values: each base's word the value's. -/
def BaseCellsF (f : Mode.Base × ℕ → Option (ℕ × ℕ)) (s : St) (σ : Val) (bs : List (Mode.Base × ℕ)) : Prop :=
  ∀ b ∈ bs, ∀ k e, f b = some (k, e) → ∀ u, BaseVal s b.1 u ↔ u = σ (V.n k)

/-- `f` keeps the exponents. -/
def ExpKeep (f : Mode.Base × ℕ → Option (ℕ × ℕ)) : Prop := ∀ b e k e', f (b, e) = some (k, e') → e' = e

theorem expKeep_P (X : AlignCtx) (body : List Stmt) (np : ℕ) : ExpKeep (baseOfP X body np) := by
  intro b e k e' h
  cases b with
  | fr o =>
    simp only [baseOfP] at h
    split_ifs at h
    · cases h; rfl
    · obtain ⟨n, -, he⟩ := Option.map_eq_some_iff.mp h
      cases he; rfl
  | hp q d =>
    simp only [baseOfP] at h
    split_ifs at h
    obtain ⟨n, -, he⟩ := Option.map_eq_some_iff.mp h
    cases he; rfl

theorem bsVal_eqF {f : Mode.Base × ℕ → Option (ℕ × ℕ)} (hf : ExpKeep f) {s : St} {σ : Val} :
    ∀ (bs : List (Mode.Base × ℕ)) (cb : List (ℕ × ℕ)),
    bs.mapM f = some cb → BaseCellsF f s σ bs → ∀ w, (BsVal s bs w ↔ w = prodB σ cb)
  | [], cb, h, _, w => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    simp [BsVal, prodB]
  | (b, e) :: bs, cb, h, hc, w => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨⟨k, e'⟩, hx, xs, hxs, rfl⟩ := h
    obtain rfl := hf b e k e' hx
    have hb := hc (b, _) List.mem_cons_self k _ hx
    have ih := bsVal_eqF hf bs xs hxs (fun b hb ↦ hc b (List.mem_cons_of_mem _ hb))
    constructor
    · rintro ⟨u, w', hu, hw', rfl⟩
      rw [(hb u).mp hu, (ih w').mp hw']
      rfl
    · rintro rfl
      exact ⟨_, _, (hb _).mpr rfl, (ih _).mpr rfl, rfl⟩

theorem monoF_spec {f : Mode.Base × ℕ → Option (ℕ × ℕ)} {m : Mode.Mono} {c : CCell} (h : monoF f m = some c) :
    m.fp = 0 ∧ ∃ cb, m.bs.mapM f = some cb ∧ c = ⟨cb, m.k⟩ := by
  unfold monoF at h
  split_ifs at h with h0
  obtain ⟨cb, hcb, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨h0, cb, hcb, rfl⟩

theorem monoVal_iffF {f : Mode.Base × ℕ → Option (ℕ × ℕ)} (hf : ExpKeep f) {s : St} {σ : Val} {m : Mode.Mono}
    {c : CCell} (hm : monoF f m = some c) (hc : BaseCellsF f s σ m.bs) (v : E) : MonoVal s m v ↔ v = c.val σ := by
  obtain ⟨h0, cb, hcb, rfl⟩ := monoF_spec hm
  have hb := bsVal_eqF hf m.bs cb hcb hc
  simp only [MonoVal, h0, pow_zero, one_mul, CCell.val, addressOfIndex]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [(hb w).mp hw, mul_comm]
  · rintro rfl
    exact ⟨_, (hb _).mpr rfl, mul_comm _ _⟩

theorem wrk_hwF {f : Mode.Base × ℕ → Option (ℕ × ℕ)} (hf : ExpKeep f) {s : St} {σ : Val} {m : Mode.Mono}
    {c : CCell} (hm : monoF f m = some c) (hc : BaseCellsF f s σ m.bs) (h : WrK s.mem (c.addr σ)) : HW s m := by
  obtain ⟨x, hx, hlt, hw⟩ := h
  exact ⟨c.val σ, x, (monoVal_iffF hf hm hc _).mpr rfl, ⟨hx, hlt⟩, hw⟩

theorem wrk_rwF {f : Mode.Base × ℕ → Option (ℕ × ℕ)} (hf : ExpKeep f) {s : St} {σ : Val} {r : Mode.Rng} {c : CCell}
    {l : List CCell} (hm : monoF f r.q = some c) (hc : BaseCellsF f s σ r.q.bs) (hl : runPts c r = some l)
    (h : ∀ p ∈ l, WrK s.mem (p.addr σ)) : RW s r := by
  unfold runPts at hl
  split at hl
  · rename_i a b hlo hhi
    cases hl
    refine ⟨c.val σ, a, b, (monoVal_iffF hf hm hc _).mpr rfl, by rw [hlo]; rfl, by rw [hhi]; rfl, fun j hj1 hj2 ↦ ?_⟩
    obtain ⟨x, hx, hlt, hw⟩ := h _ (List.mem_map.mpr ⟨j - a, List.mem_range.mpr (by omega), rfl⟩)
    refine ⟨x, ⟨?_, hlt⟩, hw⟩
    rw [← hx]
    simp only [CCell.addr, CCell.val, addressOfIndex, pow_add, ofK_mul', show a + (j - a) = j by omega]
    ring_nf
  · cases hl

/-! ## Guarantees over the body's values -/

theorem slotW_idxOf {nv : List ℕ} {w : ℕ → E} {v : ℕ} (h : v ∈ nv) : slotW (nv.map w) (nv.idxOf v) = w v := by
  have hl : nv.idxOf v < nv.length := List.idxOf_lt_length_of_mem h
  rw [slotW, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hl, Option.map_some,
    Option.getD_some, List.getElem_idxOf]

theorem prodW_mapN {nv : List ℕ} {w : ℕ → E} : ∀ (l : List (ℕ × ℕ)), (∀ b ∈ l, b.1 ∈ nv) →
    prodW (slotW (nv.map w)) (l.map fun b ↦ (nv.idxOf b.1, b.2)) = prodW w l
  | [], _ => rfl
  | (b, e) :: l, h => by
    simp only [List.map_cons, prodW]
    rw [slotW_idxOf (h _ List.mem_cons_self), prodW_mapN l fun x hx ↦ h x (List.mem_cons_of_mem _ hx)]

theorem mapN_valW {nv : List ℕ} {w : ℕ → E} {c : CCell} (h : c.vals.all (nv.contains ·) = true) :
    (c.mapN nv).valW (slotW (nv.map w)) = c.valW w := by
  simp only [CCell.valW, CCell.mapN]
  rw [prodW_mapN]
  intro b hb
  have := List.all_eq_true.mp h b.1 (List.mem_map_of_mem (f := (·.1)) hb)
  simpa using this

theorem idxC_mapN (nv : List ℕ) : ∀ i : CIdx, idxC (i.mapN nv) = (idxC i).mapN nv
  | .num _ => rfl
  | .val _ => rfl
  | .mono _ => rfl

theorem mapN_runSet {nv : List ℕ} {w : ℕ → E} {q : CRun} (h : q.vals.all (nv.contains ·) = true) (x : K) :
    (q.mapN nv).Set (slotW (nv.map w)) x ↔ q.Set w x := by
  simp only [CRun.vals, List.all_append, Bool.and_eq_true] at h
  obtain ⟨⟨hb, hl⟩, hh⟩ := h
  simp only [CRun.Set, CRun.mapN, RunSet, idxC_mapN]
  rw [mapN_valW hb, mapN_valW (by rwa [idxC_vals]), mapN_valW (by rwa [idxC_vals])]

/-- **A run bound over values** (`idxN`) with an exponent (`idxOkN`) is the bound's value. -/
theorem idxN_val {X : AlignCtx} {body : List Stmt} {np : ℕ} {s : St} {σ : Val} {res : List CRes} {i : Mode.Idx}
    {ci : CIdx} {img : MemoryImage κ} {fp : ℕ} {xs : List ℕ} (hi : idxN X body np i = some ci)
    (hc : BaseCellsF (baseOfP X body np) s σ (idxB i))
    (hres : ∀ r ∈ res, r.Holds σ) (hx : ExpW img xs fp) (hpar : ∀ k < np, Rd img fp (2 + k) = some (σ (V.n k)))
    (hok : idxOkN res xs np ci = true) :
    ∃ x, IdxVal s i x ∧ rep ((idxC ci).valW (vw σ)) = some x := by
  cases i with
  | num n =>
    simp only [idxN] at hi
    split_ifs at hi with hn
    cases hi
    exact ⟨n, rfl, rep_const (by rw [capE_eq]; exact hn)⟩
  | ex b c =>
    simp only [idxN] at hi
    split_ifs at hi with hc0
    subst hc0
    split at hi
    · rename_i v hbv
      cases hi
      simp only [idxOkN, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hok
      rcases hok with hok | ⟨hvn, hvx⟩
      swap
      · -- a parameter an entry run bounds by its exponent (`ExpW`)
        obtain ⟨e, he, hr⟩ := hx _ hvx
        have hσv : σ (V.n v) = ofK (g ^ e) := by
          have := hpar v hvn
          rw [hr, Option.some.injEq] at this
          exact this.symm
        have hB := hc (b, 1) (by simp [idxB]) v 1 hbv
        refine ⟨e, ⟨σ (V.n v), e, (hB _).mpr rfl, hσv, he, by simp⟩, ?_⟩
        rw [idxC, valW_baseC, show vw σ v = σ (V.n v) from rfl, hσv]
        exact rep_of (by rw [capE_eq]; exact he)
      simp only [expV, List.any_eq_true] at hok
      obtain ⟨r, hr, hrv⟩ := hok
      match r, hrv with
      | .lt (.val v') (.num m), hrv =>
        simp only [Bool.and_eq_true, Nat.beq_eq, decide_eq_true_eq] at hrv
        obtain ⟨rfl, hm⟩ := hrv
        obtain ⟨ya, yb, hya, -, -⟩ := hres _ hr
        rw [idxC, valW_baseC] at hya
        obtain ⟨hya1, hσa⟩ := rep_spec hya
        have hB := hc (b, 1) (by simp [idxB]) v' 1 hbv
        refine ⟨ya, ⟨σ (V.n v'), ya, (hB _).mpr rfl, ?_, by rw [← capE_eq]; exact hya1, by simp⟩, ?_⟩
        · rw [show σ (V.n v') = vw σ v' from rfl, hσa]
        · rw [idxC, valW_baseC]; exact hya
    · cases hi

/-- **A run over values written** (`postRNIn`'s) is its mode run written. -/
theorem rwN_exp {X : AlignCtx} {body : List Stmt} {np : ℕ} {s : St} {σ : Val} {res : List CRes} {r : Mode.Rng}
    {c : CCell} {lo hi : CIdx} {img : MemoryImage κ} {fp : ℕ} {xs : List ℕ}
    (hm : monoF (baseOfP X body np) r.q = some c)
    (hc : BaseCellsF (baseOfP X body np) s σ (rngM r).bs) (hlo : idxN X body np r.lo = some lo)
    (hhi : idxN X body np r.hi = some hi) (hres : ∀ r ∈ res, r.Holds σ) (hx : ExpW img xs fp)
    (hpar : ∀ k < np, Rd img fp (2 + k) = some (σ (V.n k))) (hokl : idxOkN res xs np lo = true)
    (hokh : idxOkN res xs np hi = true)
    (h : ∀ x, (⟨⟨c.bases, c.off + r.d⟩, r.S, lo, hi⟩ : CRun).Set (vw σ) x → WrK s.mem x) : Mode.RW s r := by
  have hcq : BaseCellsF (baseOfP X body np) s σ r.q.bs := fun b hb ↦ hc b (by simp [rngM, hb])
  have hcl : BaseCellsF (baseOfP X body np) s σ (idxB r.lo) := fun b hb ↦ hc b (by simp [rngM, hb])
  have hch : BaseCellsF (baseOfP X body np) s σ (idxB r.hi) := fun b hb ↦ hc b (by simp [rngM, hb])
  obtain ⟨xlo, hxlo, hylo⟩ := idxN_val hlo hcl hres hx hpar hokl
  obtain ⟨xhi, hxhi, hyhi⟩ := idxN_val hhi hch hres hx hpar hokh
  refine ⟨c.val σ, xlo, xhi, (monoVal_iffF (expKeep_P _ _ _) hm hcq _).mpr rfl, hxlo, hxhi, fun j h1 h2 ↦ ?_⟩
  have hx := h _ (runSet_iff.mpr ⟨xlo, xhi, j, hylo, hyhi, h1, h2, rfl⟩)
  rw [val_eq, run_cell]
  exact names_wrk hx

/-- A top-level statement other than a `ret` has no `ret` in it. -/
theorem noRet_of_topOk {s : Stmt} (h : topOk s = true) (hr : ∀ vs, s ≠ .ret vs := by intro _ h; cases h) :
    Core.Stmt.noRet s = true := by
  cases s with
  | ret vs => exact absurd rfl (hr vs)
  | call => simp [Core.Stmt.noRet]
  | dispatch => simp [Core.Stmt.noRet]
  | _ =>
    simp only [topOk, Bool.and_eq_true] at h
    exact h.1

/-- On a returning path of a body of the core route's shape, the first top-level `ret`'s values. -/
theorem retVals_eq {σ : Val} : ∀ {body : List Stmt}, body.all topOk = true → ∀ {es : List Ev} {vs : List V},
    walk σ body = .ret es vs → retVals body = some vs
  | [], _, _, _, h => by simp [walk] at h
  | s :: ss, ht, es, vs, h => by
    simp only [List.all_cons, Bool.and_eq_true] at ht
    cases s with
    | ret vs' =>
      rw [walk_ret_cons, Out.ret.injEq] at h
      obtain ⟨-, rfl⟩ := h
      rfl
    | _ =>
      obtain ⟨es1, es2, h2, -⟩ := walk_cons_noRet (noRet_of_topOk ht.1) h
      exact retVals_eq ht.2 h2

/-- **A top-level `load` before the `ret` is on the path.** -/
theorem hpVal_mem {σ : Val} {k d n : ℕ} : ∀ {body : List Stmt}, body.all topOk = true →
    ∀ {es : List Ev} {vs : List V}, walk σ body = .ret es vs → hpVal body k d = some n →
      Ev.atom (.load (V.n n) (V.n k) d) ∈ es
  | [], _, _, _, _, h => by simp [hpVal] at h
  | s :: ss, ht, es, vs, hw, h => by
    simp only [List.all_cons, Bool.and_eq_true] at ht
    cases s with
    | ret vs' => simp [hpVal] at h
    | atom a =>
      rw [walk_atom_cons] at hw
      obtain ⟨es', hw', rfl⟩ := pre_eq_ret hw
      have hrec : hpVal ss k d = some n → Ev.atom (.load (V.n n) (V.n k) d) ∈ Ev.atom a :: es' :=
        fun h' ↦ List.mem_cons_of_mem _ (hpVal_mem ht.2 hw' h')
      cases a with
      | load v p off =>
        simp only [hpVal] at h
        split at h
        · rename_i k' n' hp hv
          cases hb : (Nat.beq k' k && Nat.beq off d) <;> simp only [hb, Bool.cond_true, Bool.cond_false] at h
          · exact hrec h
          · simp only [Bool.and_eq_true, Nat.beq_eq] at hb
            obtain ⟨rfl, rfl⟩ := hb
            cases h
            rw [← vnum_eq hp, ← vnum_eq hv]
            exact List.mem_cons_self
        · exact hrec h
      | _ => exact hrec h
    | _ =>
      obtain ⟨es1, es2, h2, rfl⟩ := walk_cons_noRet (noRet_of_topOk ht.1) hw
      exact List.mem_append_right _ (hpVal_mem ht.2 h2 h)

/-- **A top-level `const` before the `ret` is on the path.** -/
theorem constOf_mem {σ : Val} {n : ℕ} {c : E} : ∀ {body : List Stmt}, body.all topOk = true →
    ∀ {es : List Ev} {vs : List V}, walk σ body = .ret es vs → constOf body n = some c →
      Ev.atom (.const (V.n n) c) ∈ es
  | [], _, _, _, _, h => by simp [constOf] at h
  | s :: ss, ht, es, vs, hw, h => by
    simp only [List.all_cons, Bool.and_eq_true] at ht
    cases s with
    | ret vs' => simp [constOf] at h
    | atom a =>
      rw [walk_atom_cons] at hw
      obtain ⟨es', hw', rfl⟩ := pre_eq_ret hw
      have hrec : constOf ss n = some c → Ev.atom (.const (V.n n) c) ∈ Ev.atom a :: es' :=
        fun h' ↦ List.mem_cons_of_mem _ (constOf_mem ht.2 hw' h')
      cases a with
      | const d c' =>
        simp only [constOf] at h
        split at h
        · rename_i n' hd
          cases hb : Nat.beq n' n <;> simp only [hb, Bool.cond_true, Bool.cond_false] at h
          · exact hrec h
          · rw [Nat.beq_eq] at hb
            subst hb
            cases h
            rw [← vnum_eq hd]
            exact List.mem_cons_self
        · exact hrec h
      | _ => exact hrec h
    | _ =>
      obtain ⟨es1, es2, h2, rfl⟩ := walk_cons_noRet (noRet_of_topOk ht.1) hw
      exact List.mem_append_right _ (constOf_mem ht.2 h2 h)

/-- The executor's word at a cell, nonzero, is the reference's. -/
theorem rdE_of_get {img : MemoryImage κ} (hκ : κ ≤ 28) {m : Mem} (ha : Agree m (refMem img)) {fp o : ℕ}
    {u : E} (hg : m.get (fp + o) = some u) (hu : u ≠ 0) : Rd img fp o = some u := by
  have h1 := ha.get _ _ hg
  unfold refMem at h1
  split_ifs at h1 with hc
  · rw [Rd, ← pow_add, show (g : K) ^ (fp + o) = addressOfIndex (⟨fp + o, hc⟩ : Fin (2 ^ κ)) from rfl,
      MemoryImage.read_gpow (by omega)]
    exact congrArg some h1
  · exact absurd h1.symm hu

/-- A bound's cell, by its value, holds a power of `g` in the reference. -/
theorem expW_idx {img : MemoryImage κ} (hκ : κ ≤ 28) {s : St} (ha : Agree s.mem (refMem img)) {i : Mode.Idx} {x : ℕ}
    (h : IdxVal s i x) {o : ℕ} (ho : o ∈ boundCells i) : ∃ e, e < 2 ^ 62 ∧ Rd img s.fp o = some (ofK (g ^ e)) := by
  match i, h, ho with
  | .ex (.fr o') c, h, ho =>
    simp only [boundCells, List.mem_singleton] at ho
    subst ho
    obtain ⟨v, e, hv, rfl, he, -⟩ := h
    exact ⟨e, he, rdE_of_get hκ ha hv (Mode.ofK_gpow_ne_zero _)⟩

/-- **The entry runs' exponent cells hold powers of `g`**, from the entry facts. -/
theorem expW_of {img : MemoryImage κ} (hκ : κ ≤ 28) {s : St} (ha : Agree s.mem (refMem img)) {G : Mode.Sig}
    (hR : ∀ r ∈ G.preR, RW s r) (hP : ∀ p ∈ G.preP, Mode.PW s p.1 p.2) : ExpW img (expCells G) s.fp := by
  intro o ho
  obtain ⟨r, hr, ho⟩ := List.mem_flatMap.mp ho
  have hlh : (∃ x, IdxVal s r.lo x) ∧ ∃ x, IdxVal s r.hi x := by
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨-, xl, xh, -, hl, hh, -⟩ := hR r hr
      exact ⟨⟨xl, hl⟩, xh, hh⟩
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
      obtain ⟨-, xl, xh, -, hl, hh, -⟩ := hP p hp
      exact ⟨⟨xl, hl⟩, xh, hh⟩
  obtain ⟨⟨xl, hl⟩, xh, hh⟩ := hlh
  rcases List.mem_append.mp ho with ho | ho
  · exact expW_idx hκ ha hl ho
  · exact expW_idx hκ ha hh ho

/-- The entry runs' exponent cells hold powers of `g`, from the entry abstraction. -/
theorem expW_entry {img : MemoryImage κ} (hκ : κ ≤ 28) {E0 : Mode.Env} {G : Mode.Sig} {s : St} (ha : Agree s.mem (refMem img))
    (h : Mode.Holds s (entryAbs E0 G)) : ExpW img (expCells G) s.fp := by
  unfold entryAbs at h
  rcases hs : G.self with _ | o
  · rw [hs] at h
    exact expW_of hκ ha (fun r hr ↦ h.r r (List.mem_cons_of_mem _ hr)) h.p
  · rw [hs] at h
    simp only [Mode.Abs.addW, Mode.Abs.addV, Mode.Abs.addNz] at h
    exact expW_of hκ ha (fun r hr ↦ h.r r (List.mem_cons_of_mem _ hr)) h.p

/-- **A run bound `expI` at return has an exponent**, at least its offset: its cell's word the slot's, a power of
`g` by the entry runs (`ExpW`), or a parameter's bounded by a residual true of the instance `σ`. -/
theorem rep_expI {img : MemoryImage κ} {fp : ℕ} {G : Mode.Sig} {res : List CRes} {σ : Val} {ws : List E} {np n : ℕ}
    (hws : ∀ b < n, Rd img fp (2 + b) = some (slotW ws b)) (hx : ExpW img (expCells G) fp)
    (hpar : ∀ k < np, Rd img fp (2 + k) = some (σ (V.n k))) (hres : ∀ r ∈ res, r.Holds σ)
    {i : Mode.Idx} {ci : CIdx} (hi : idxX i = some ci) (he : expI G res np n i = true) :
    IdxEx (slotW ws) ci := by
  rcases idxX_spec hi with ⟨m, rfl, hm, rfl⟩ | ⟨o, c, rfl, h2, -, rfl⟩
  · exact idxEx_num _ hm
  · simp only [expI, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.contains_iff_mem,
      Nat.beq_eq, List.any_eq_true] at he
    obtain ⟨⟨-, hon⟩, ⟨rfl, hoe⟩ | ⟨hnp, r, hr, hrr⟩⟩ := he
    · obtain ⟨e, he, hr⟩ := hx o hoe
      have h1 := hws (o - 2) hon
      rw [show 2 + (o - 2) = o by omega, hr, Option.some.injEq] at h1
      exact idxEx_idxO (by omega) h1.symm
    · match r, hrr with
      | .lt (.val b') (.num m), hrr =>
        simp only [expRes, Bool.and_eq_true, Nat.beq_eq, decide_eq_true_eq] at hrr
        obtain ⟨rfl, hmc⟩ := hrr
        obtain ⟨ya, yb, hya, hyb, hlt⟩ := hres _ hr
        rw [idxC, valW_const] at hyb
        obtain ⟨hyb1, hyb2⟩ := rep_spec hyb
        rw [capE_eq] at hyb1
        have hmb : m = yb := gpow_inj_lt (by omega) (by omega) hyb2
        subst hmb
        rw [idxC, valW_baseC] at hya
        obtain ⟨-, hσa⟩ := rep_spec hya
        have h1 := hws (o - 2) hon
        rw [hpar (o - 2) hnp, Option.some.injEq] at h1
        refine idxEx_idxO (e := ya) (by omega) ?_
        rw [← h1]
        exact hσa

/-- A run's bounds `expI` at return have exponents. -/
theorem rngX_rep_exp {img : MemoryImage κ} {fp : ℕ} {G : Mode.Sig} {res : List CRes} {σ : Val} {ws : List E}
    {np n : ℕ} (hws : ∀ b < n, Rd img fp (2 + b) = some (slotW ws b)) (hx : ExpW img (expCells G) fp)
    (hpar : ∀ k < np, Rd img fp (2 + k) = some (σ (V.n k))) (hres : ∀ r ∈ res, r.Holds σ)
    {r : Mode.Rng} {q : CRun} (h : rngX r = some q) (hlo : expI G res np n r.lo = true)
    (hhi : expI G res np n r.hi = true) : IdxEx (slotW ws) q.lo ∧ IdxEx (slotW ws) q.hi := by
  obtain ⟨lo, hi, c, hl, hh, -, rfl⟩ := rngX_spec h
  exact ⟨rep_expI hws hx hpar hres hl hlo, rep_expI hws hx hpar hres hh hhi⟩

/-- **A callee's run bound at a call has an exponent** (`idxPow`), at the call's argument words. -/
theorem idxPow_rep {pows : Exec.PowTree} (hp : pows.Ok) {body : List Stmt} (htop : body.all topOk = true)
    {σ : Val} {rd : Reader} {es : List Ev} {vs : List V} (hw : walk σ body = .ret es vs)
    (hh : ∀ e ∈ es, e.Holds rd σ) {args : List V} {ws : List E} {i : CIdx}
    (h : idxPow pows body args i = true) : IdxEx (slotW (args.map σ ++ ws)) i := by
  cases i with
  | num n =>
    simp only [idxPow, decide_eq_true_eq] at h
    exact idxEx_num _ h
  | val b =>
    simp only [idxPow] at h
    split at h
    · rename_i v hv
      have hb : b < args.length := (List.getElem?_eq_some_iff.mp hv).1
      simp only [constPow] at h
      split at h
      · rename_i n hn
        split at h
        · rename_i c hc
          split at h
          · rename_i e he
            have hel := of_decide_eq_true h
            have hmem := constOf_mem htop hw hc
            have hσc : σ (V.n n) = c := hh _ hmem
            refine idxEx_val hel ?_
            rw [slotW_lt (by simpa using hb), slotW_get (by simpa using hb), List.getElem_map,
              show args[b] = v from (List.getElem?_eq_some_iff.mp hv).2, vnum_eq hn, hσc, powOf_ok hp he]
          · cases h
        · cases h
      · cases h
    · cases h
  | mono c =>
    obtain ⟨bs, k⟩ := c
    simp only [idxPow] at h
    split at h
    · rename_i b
      split at h
      · rename_i v hv
        have hb : b < args.length := (List.getElem?_eq_some_iff.mp hv).1
        split at h
        · rename_i n hn
          split at h
          · rename_i c hc
            split at h
            · rename_i e he
              have hel := of_decide_eq_true h
              have hσc : σ (V.n n) = c := hh _ (constOf_mem htop hw hc)
              have := idxEx_idxO (w := slotW (args.map σ ++ ws)) (b := b) (c := k) hel (by
                rw [slotW_lt (by simpa using hb), slotW_get (by simpa using hb), List.getElem_map,
                  show args[b] = v from (List.getElem?_eq_some_iff.mp hv).2, vnum_eq hn, hσc, powOf_ok hp he])
              cases k <;> exact this
            · cases h
          · cases h
        · cases h
      · cases h
    · cases h

/-- **A callee's run bound at a call has an exponent** (`idxPowC`): `idxPow`'s, or a parameter's whose
cell is an entry run's exponent cell (`ExpW`). -/
theorem idxPowC_rep {img : MemoryImage κ} {Cf : CFun} (hp : Cf.pows.Ok) (htop : Cf.fn.body.all topOk = true)
    {fp : ℕ} {σ : Val} {rd : Reader} {es : List Ev} {vs : List V} (hw : walk σ Cf.fn.body = .ret es vs)
    (hh : ∀ e ∈ es, e.Holds rd σ) (hpar : ∀ k < Cf.fn.params.length, Rd img fp (2 + k) = some (σ (V.n k)))
    (hx : ExpW img Cf.xc fp) (hres : ResF Cf.H σ) {args : List V} {ws : List E} {i : CIdx}
    (h : idxPowC Cf args i = true) : IdxEx (slotW (args.map σ ++ ws)) i := by
  rcases Bool.or_eq_true_iff.mp h with h | h
  swap
  · -- an argument a residual bounds
    cases i with
    | val b =>
      simp only [resArg] at h
      split at h
      · rename_i v hv
        have hb : b < args.length := (List.getElem?_eq_some_iff.mp hv).1
        split at h
        · rename_i k hk
          obtain ⟨r, hr, hrk⟩ := List.any_eq_true.mp h
          match r, hrk with
          | .lt (.val k') (.num n), hrk =>
            simp only [Bool.and_eq_true, Nat.beq_eq, decide_eq_true_eq] at hrk
            obtain ⟨rfl, hn⟩ := hrk
            obtain ⟨ya, yb, hya, -, -⟩ := hres _ hr
            refine ⟨ya, ?_, Nat.zero_le _⟩
            rw [idxC, valW_baseC] at hya ⊢
            rw [slotW_lt (by simpa using hb), slotW_get (by simpa using hb), List.getElem_map,
              show args[b] = v from (List.getElem?_eq_some_iff.mp hv).2, vnum_eq hk]
            exact hya
        · cases h
      · cases h
    | num n => simp [resArg] at h
    | mono c =>
      obtain ⟨cb, off⟩ := c
      simp only [resArg] at h
      split at h
      · rename_i b _
        split at h
        · rename_i v hv
          have hb : b < args.length := (List.getElem?_eq_some_iff.mp hv).1
          split at h
          · rename_i k hk
            obtain ⟨r, hr, hrk⟩ := List.any_eq_true.mp h
            match r, hrk with
            | .lt (.val k') (.num n), hrk =>
              simp only [Bool.and_eq_true, Nat.beq_eq, decide_eq_true_eq] at hrk
              obtain ⟨rfl, hn⟩ := hrk
              obtain ⟨ya, yb, hya, hyb, hlt⟩ := hres _ hr
              rw [idxC, valW_baseC] at hya
              rw [idxC, rep_const (by omega), Option.some.injEq] at hyb
              subst hyb
              have hw : slotW (args.map σ ++ ws) b = ofK (g ^ ya) := by
                rw [slotW_lt (by simpa using hb), slotW_get (by simpa using hb), List.getElem_map,
                  show args[b] = v from (List.getElem?_eq_some_iff.mp hv).2, vnum_eq hk]
                exact (rep_spec hya).2
              have := idxEx_idxO (w := slotW (args.map σ ++ ws)) (b := b) (c := off)
                (by rw [capE_eq] at hn; omega) hw
              cases off <;> exact this
          · cases h
        · cases h
      · cases h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · exact idxPow_rep hp htop hw hh h
  cases i with
  | val b =>
    simp only [expArg] at h
    split at h
    · rename_i v hv
      have hb : b < args.length := (List.getElem?_eq_some_iff.mp hv).1
      split at h
      · rename_i k hk
        simp only [Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at h
        obtain ⟨hkn, hke⟩ := h
        obtain ⟨e, he, hr⟩ := hx _ hke
        have h1 := hpar k hkn
        rw [hr, Option.some.injEq] at h1
        refine idxEx_val he ?_
        rw [slotW_lt (by simpa using hb), slotW_get (by simpa using hb), List.getElem_map,
          show args[b] = v from (List.getElem?_eq_some_iff.mp hv).2, vnum_eq hk, ← h1]
      · cases h
    · cases h
  | num n => simp [expArg] at h
  | mono c => simp [expArg] at h


/-- **A callee's run bound at a call has an exponent** (`idxPowG`): `idxPowC`'s, or its ghost slot's, a parameter's word
whose entry cell has an exponent (`ExpW`). -/
theorem idxPowG_rep {img : MemoryImage κ} {Cf : CFun} (hp : Cf.pows.Ok) (htop : Cf.fn.body.all topOk = true)
    {fp : ℕ} {σ : Val} {rd : Reader} {es : List Ev} {vs : List V} (hw : walk σ Cf.fn.body = .ret es vs)
    (hh : ∀ e ∈ es, e.Holds rd σ) (hpar : ∀ k < Cf.fn.params.length, Rd img fp (2 + k) = some (σ (V.n k)))
    (hx : ExpW img Cf.xc fp) (hres : ResF Cf.H σ) {f : String} {args : List V} {i : CIdx}
    (h : idxPowG Cf f args i = true) : IdxEx (slotW (args.map σ ++ gargsW Cf.H σ f args)) i := by
  rcases Bool.or_eq_true_iff.mp h with h | h
  · exact idxPowC_rep hp htop hw hh hpar hx hres h
  cases i with
  | val b =>
    simp only [ghostArg, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hb, h⟩ := h
    split at h
    · rename_i c hc
      split at h
      · rename_i k hck
        simp only [Bool.and_eq_true, Nat.beq_eq, decide_eq_true_eq, List.contains_iff_mem] at h
        obtain ⟨⟨hoff, hk⟩, hxc⟩ := h
        obtain ⟨e, he, hrd⟩ := hx _ hxc
        have hσk : σ (V.n k) = ofK (g ^ e) := by
          have := hpar k hk
          rw [hrd] at this
          exact (Option.some.inj this).symm
        have hs : slotW (args.map σ ++ gargsW Cf.H σ f args) b = σ (V.n k) := by
          unfold slotW gargsW
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simpa using hb), List.length_map,
            List.getElem?_map, hc]
          obtain ⟨cb, co⟩ := c
          simp only at hck hoff
          subst hck hoff
          simp [CCell.valW, prodW, vw]
        refine ⟨e, ?_, Nat.zero_le _⟩
        rw [idxC, valW_baseC, hs, hσk]
        exact rep_of (by rw [capE_eq]; exact he)
      · cases h
    · cases h
  | num n => simp [ghostArg] at h
  | mono c => simp [ghostArg] at h
/-- **The promised products' bases at the return**: a parameter's frame cell, a return cell holding the
returned value, the word past a parameter's a top-level `load` read, written. -/
theorem baseCellsP_of {img : MemoryImage κ} (hκ : κ ≤ 28) {Cf : CFun} {G : Mode.Sig} {m : Mode.Mono}
    (hm : monoOkP G Cf.fn.params.length m = true) (htop : Cf.fn.body.all topOk = true) {s : St}
    (hs : Fine (refMem img) s) (hw : ∀ o ∈ G.entry, s.mem.written (s.fp + o) = true)
    (hwr : ∀ o ∈ G.ret, s.mem.written (s.fp + o) = true) {σ : Val} (hσ : HonF img Cf s.fp σ) {es : List Ev}
    {vs : List V} (hb : walk σ Cf.fn.body = .ret es vs)
    (hW : ∀ a, Ev.atom a ∈ es → ∀ y, Writes σ a y → WrK s.mem y) :
    BaseCellsF (baseOfP Cf.X Cf.fn.body Cf.fn.params.length) s σ m.bs := by
  have hframe : ∀ o, o < 2 ^ 28 → s.mem.written (s.fp + o) = true → ∀ v, Rd img s.fp o = some v →
      ∀ u, BaseVal s (.fr o) u ↔ u = v := fun o ho hwo v hrd u ↦ by
    obtain ⟨u', hu'⟩ := Mem.get_of_written hwo
    have hv := rd_get hκ hs ho hrd hu'
    simp only [Mode.BaseVal, hu', Option.some.injEq]
    rw [hv]
    exact eq_comm
  intro b hbm k e hf u
  have h := List.all_eq_true.mp hm b hbm
  obtain ⟨b1, e0⟩ := b
  cases b1 with
  | fr o =>
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.contains_iff_mem] at h
    obtain ⟨ho, hcase⟩ := h
    simp only [baseOfP] at hf
    split_ifs at hf with hpar
    · cases hf
      have hr : Rd img s.fp o = some (σ (V.n (o - 2))) := by
        have := hσ.par (o - 2) hpar.2
        rwa [show 2 + (o - 2) = o by omega] at this
      have hwo : s.mem.written (s.fp + o) = true := by
        rcases hcase with ⟨⟨hoe, -⟩, -⟩ | hret
        · exact hw o hoe
        · exact hwr o hret
      exact hframe o ho hwo _ hr u
    · obtain ⟨n, hn, he⟩ := Option.map_eq_some_iff.mp hf
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have hret : o ∈ G.ret := by
        rcases hcase with ⟨⟨-, h2⟩, h3⟩ | hret
        · exact absurd ⟨h2, h3⟩ hpar
        · exact hret
      unfold retAtCell at hn
      rw [retVals_eq htop hb, Option.bind_some] at hn
      obtain ⟨v, hv, hvn⟩ := Option.bind_eq_some_iff.mp hn
      have hvm := List.mem_of_find?_eq_some hv
      have hloc : Cf.X.locAt v.idx = o :=
        Nat.beq_eq.mp (List.find?_some (p := fun w : V ↦ Nat.beq (Cf.X.locAt w.idx) o) hv)
      have hr : Rd img s.fp o = some (σ (V.n n)) := by
        rw [← vnum_eq hvn, ← hloc]
        exact hσ.rets _ _ hb v hvm
      exact hframe o ho (hwr o hret) _ hr u
  | hp q d =>
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at h
    obtain ⟨⟨⟨hqe, hq2⟩, hqn⟩, hq28⟩ := h
    simp only [baseOfP, show 2 ≤ q ∧ q - 2 < Cf.fn.params.length from ⟨hq2, hqn⟩] at hf
    obtain ⟨n, hn, he⟩ := Option.map_eq_some_iff.mp hf
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have hl := hpVal_mem htop hb hn
    have hrq : Rd img s.fp q = some (σ (V.n (q - 2))) := by
      have := hσ.par (q - 2) hqn
      rwa [show 2 + (q - 2) = q by omega] at this
    obtain ⟨P, hP⟩ := Mem.get_of_written (hw q hqe)
    have hPv : P = σ (V.n (q - 2)) := rd_get hκ hs hq28 hrq hP
    obtain ⟨x, hx, hxlt, hxw⟩ := hW _ hl _ rfl
    obtain ⟨-, hrd⟩ := hσ.holds _ _ hb _ hl
    have hcx : (σ (V.n (q - 2))).limb 0 * addressOfIndex d = g ^ x := hx
    rw [hcx] at hrd
    have hrefx : refMem img x = σ (V.n n) :=
      (Prover.Exec.refRd_img hκ img x _ (by unfold maxCells at hxlt; omega) hrd).2
    obtain ⟨u', hu'⟩ := Mem.get_of_written hxw
    have hu'v : u' = σ (V.n n) := by rw [← hrefx]; exact (hs.agree.get _ _ hu').symm
    have hnames : (P * ofK (g ^ d)).limb 0 = g ^ x := by
      rw [limb0_mul_ofK, hPv, ← hcx]
    constructor
    · rintro ⟨p, y, hp, hy, hu⟩
      rw [hP, Option.some.injEq] at hp
      subst hp
      have hyx : y = x := gpow_inj (by have := hy.2; unfold maxCells at this; omega)
        (by unfold maxCells at hxlt; omega) (hy.1.symm.trans hnames)
      subst hyx
      rw [hu', Option.some.injEq] at hu
      rw [← hu, hu'v]
    · rintro rfl
      exact ⟨P, x, hP, ⟨hnames, hxlt⟩, by rw [hu', hu'v]⟩

/-! ## Returned products -/

theorem retVGo_sound {X : AlignCtx} {G : Mode.Sig} {np : ℕ} {hx : HX} {H : HCert} (hR : hx.R = H.readT)
    (hP : ∀ k c, Check.getF hx.pre k = some c → c ∈ H.sig.pre) (hpows : hx.pows.Ok) {σ : Val} {rd : Reader} :
    ∀ (ss : List Stmt) {st : HSt} {W : K → Prop} {es : List Ev} {vs : List V},
      (∀ c ∈ H.sig.pre, W (c.addr σ)) → retVGo X G np hx ss st = true → EnvOk σ st.env → ScOk W σ st.sc →
      walk σ ss = .ret es vs → AllHold rd σ es → ∀ p ∈ G.retV, p.1 < 2 ^ 28 ∧ p.1 ∈ G.ret ∧
        monoS G np true p.2 = true ∧ ∃ c v, monoC p.2 = some c ∧ v ∈ vs ∧ X.locAt v.idx = p.1 ∧ σ v = c.val σ
  | [], _, _, _, _, _, h, _, _, _, _ => by simp [retVGo] at h
  | .atom a :: ss, st, W, es, vs, hpre, h, he, hs, hw, hh => by
    simp only [retVGo] at h
    cases ha : atomH hx st a with
    | none => rw [ha] at h; cases h
    | some st1 =>
      rw [ha] at h
      simp only [HSt.seq_eq] at h
      rw [Bridge.walk_atom_cons] at hw
      obtain ⟨es', hw', rfl⟩ := Bridge.pre_eq_ret hw
      obtain ⟨-, he1, hs1⟩ := atomH_ok hR hP hpows hpre ha he hs (hh _ List.mem_cons_self)
      exact retVGo_sound hR hP hpows ss (fun c hc ↦ Or.inl (hpre c hc)) h he1 hs1 hw'
        (fun e he ↦ hh e (List.mem_cons_of_mem _ he))
  | .ret vs' :: _, st, W, es, vs, hpre, h, he, hs, hw, _ => by
    rw [Bridge.walk_ret_cons, Out.ret.injEq] at hw
    obtain ⟨-, rfl⟩ := hw
    simp only [retVGo, List.all_eq_true] at h
    intro p hp
    have hp' := h p hp
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hp'
    obtain ⟨⟨⟨h28, hret⟩, hmo⟩, hc⟩ := hp'
    refine ⟨h28, hret, hmo, ?_⟩
    split at hc
    · rename_i c hmc
      obtain ⟨v, hv, hb⟩ := List.any_eq_true.mp hc
      simp only [Bool.and_eq_true, Nat.beq_eq] at hb
      obtain ⟨hloc, hm⟩ := hb
      split at hm
      · rename_i c' hc'
        exact ⟨c, v, hmc, hv, hloc, by rw [monoOf_ok he hc', CCell.beq_eq hm]⟩
      · cases hm
    · cases hc
  | .ite .. :: _, _, _, _, _, _, h, _, _, _, _ => by simp [retVGo] at h
  | .match_ .. :: _, _, _, _, _, _, h, _, _, _, _ => by simp [retVGo] at h
  | .call .. :: _, _, _, _, _, _, h, _, _, _, _ => by simp [retVGo] at h
  | .callIf .. :: _, _, _, _, _, _, h, _, _, _, _ => by simp [retVGo] at h
  | .dispatch .. :: _, _, _, _, _, _, h, _, _, _, _ => by simp [retVGo] at h

/-- **The returned products**: on a path that returns, each product of `retV` is a return cell whose
monomial is a returned value's at its cell (`heapOk`'s pass), or returned word `p.1 - 2 - np`'s of
the heap signature's `retM`. -/
theorem retVOk_sound {Cf : CFun} {G : Mode.Sig} (hp : Cf.pows.Ok) (hok : retVOk Cf G = true) {σ : Val}
    {rd : Reader} {es : List Ev} {vs : List V} (hw : walk σ Cf.fn.body = .ret es vs) (hh : ∀ e ∈ es, e.Holds rd σ) :
    ∀ p ∈ G.retV, p.1 < 2 ^ 28 ∧ p.1 ∈ G.ret ∧ monoS G Cf.fn.params.length true p.2 = true ∧
      ∃ c, monoC p.2 = some c ∧ ((∃ v, v ∈ vs ∧ Cf.X.locAt v.idx = p.1 ∧ σ v = c.val σ) ∨
        (2 + Cf.fn.params.length ≤ p.1 ∧ (p.1 - 2 - Cf.fn.params.length, c) ∈ Cf.H.sig.retM)) := by
  unfold retVOk at hok
  rcases Bool.or_eq_true_iff.mp hok with h | hok
  · rcases Bool.or_eq_true_iff.mp h with h | h
    · intro p hpm; rw [List.isEmpty_iff.mp h] at hpm; cases hpm
    · intro p hpm
      have h1 := List.all_eq_true.mp h p hpm
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at h1
      obtain ⟨⟨⟨⟨h28, hret⟩, hmo⟩, h2⟩, hc⟩ := h1
      refine ⟨h28, hret, hmo, ?_⟩
      split at hc
      · rename_i c hmc
        obtain ⟨q, hq, hqe⟩ := List.any_eq_true.mp hc
        simp only [Bool.and_eq_true, Nat.beq_eq] at hqe
        refine ⟨c, hmc, Or.inr ⟨h2, ?_⟩⟩
        rw [← hqe.1, ← CCell.beq_eq hqe.2]
        exact hq
      · cases hc
  rw [Exec.Trie.seq_eq, Exec.Trie.seq_eq] at hok
  intro p hpm
  obtain ⟨h1, h2, h3, c, v, h4, h5, h6, h7⟩ := retVGo_sound (hx := ⟨Cf.pows, Cf.H.readT, trieFrom Cf.H.sig.pre 0 .nil⟩)
    (H := Cf.H) (rd := rd) rfl
    (fun k c h ↦ (getF_trieFrom _ _ _ h).resolve_right (by simp [getF_nil])) hp Cf.fn.body
    (W := fun x ↦ ∃ c ∈ Cf.H.sig.pre, c.addr σ = x) (fun c hc ↦ ⟨c, hc, rfl⟩) hok envOk_nil
    (fun n c h ↦ by simp [getF_nil] at h) hw hh p hpm
  exact ⟨h1, h2, h3, c, h4, Or.inl ⟨v, h5, h6, h7⟩⟩

end

end LeanVM.Guest.CoreMode
