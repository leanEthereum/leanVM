/-
  LeanVM.Compiler.Complete.FrameAssemble

  The frame side assembled: the constructs' lemmas at the walk's instance of a function of a
  compiled program, and the block lemma at its body.
-/

module

public import LeanVM.Compiler.Complete.FrameBody
public import LeanVM.Compiler.Complete.FrameInner
public import LeanVM.Compiler.Complete.FrameCalls
public import LeanVM.Compiler.Complete.FrameAddr
public import LeanVM.Compiler.Complete.FramePool
public import LeanVM.Compiler.Complete.FrameIte
public import LeanVM.Compiler.Complete.FrameSelf
public import LeanVM.Compiler.Complete.FrameStage

/-!
# The frame side, assembled

`bodyW_of` (FrameInner.lean) gives the block lemma at a body from the lemmas of its constructs on
the body's blocks (`InBody`). Here the straight-line and call statements' lemmas (`stmtW_atom'`,
`stmtW_frameAddr`, `stmtW_call`, `stmtW_callIf`, `stmtW_dispatch`, `stmtW_ret'`) are taken at the
walk's instance of a function of a compiled program (`instK`, the memories `agK`): its facts
(`Inst.Ok`, `OpOK`, the own frame and the callee frames on the memories, the layout's words) and
the core body's (a block of the body names only the body's values, calls itself by no `call`).
-/

namespace LeanVM.Compiler.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-! ## The blocks of a body -/

section Body

variable {body : List Stmt}

theorem usesArms_mem {a : List Stmt} : ∀ {arms : List (List Stmt)}, a ∈ arms →
    ∀ v ∈ Stmt.usesList a, v ∈ Stmt.usesArms arms
  | [], ha, _, _ => by cases ha
  | b :: bs, ha, v, hv => by
      simp only [Stmt.usesArms, List.mem_append]
      rcases List.mem_cons.mp ha with rfl | hb
      · exact Or.inl hv
      · exact Or.inr (usesArms_mem hb v hv)

theorem tmpsArms_mem {a : List Stmt} : ∀ {arms : List (List Stmt)}, a ∈ arms →
    ∀ t ∈ Stmt.tmpsList a, t ∈ Stmt.tmpsArms arms
  | [], ha, _, _ => by cases ha
  | b :: bs, ha, t, ht => by
      simp only [Stmt.tmpsArms, List.mem_append]
      rcases List.mem_cons.mp ha with rfl | hb
      · exact Or.inl ht
      · exact Or.inr (tmpsArms_mem hb t ht)

theorem callsA_mem {a : List Stmt} {f : String} : ∀ {arms : List (List Stmt)}, a ∈ arms →
    callsL f a = true → callsA f arms = true
  | [], ha, _ => by cases ha
  | b :: bs, ha, hf => by
      simp only [callsA, Bool.or_eq_true]
      rcases List.mem_cons.mp ha with rfl | hb
      · exact Or.inl hf
      · exact Or.inr (callsA_mem hb hf)

/-- **A block of a body** names only the body's values and temporaries, and calls a function by a
`call` or a `dispatch` only if the body does. -/
theorem inBody_sub {ss : List Stmt} (h : InBody body ss) :
    (∀ v ∈ Stmt.usesList ss, v ∈ Stmt.usesList body) ∧
    (∀ t ∈ Stmt.tmpsList ss, t ∈ Stmt.tmpsList body) ∧
    ∀ f, callsL f ss = true → callsL f body = true := by
  induction h with
  | top => exact ⟨fun _ h => h, fun _ h => h, fun _ h => h⟩
  | tail _ ih =>
      obtain ⟨h1, h2, h3⟩ := ih
      refine ⟨fun v hv => h1 v ?_, fun t ht => h2 t ?_, fun f hf => h3 f ?_⟩
      · simp only [Stmt.usesList, List.mem_append]; exact Or.inr hv
      · simp only [Stmt.tmpsList, List.mem_append]; exact Or.inr ht
      · simp [callsL, hf]
  | iteZ _ ih =>
      obtain ⟨h1, h2, h3⟩ := ih
      refine ⟨fun v hv => h1 v ?_, fun t ht => h2 t ?_, fun f hf => h3 f ?_⟩
      · simp only [Stmt.usesList, Stmt.uses, List.mem_append, List.mem_cons]
        exact Or.inl (Or.inr (Or.inl hv))
      · simp only [Stmt.tmpsList, Stmt.tmps, List.mem_append]; exact Or.inl (Or.inl ht)
      · simp [callsL, callsS, hf]
  | iteN _ ih =>
      obtain ⟨h1, h2, h3⟩ := ih
      refine ⟨fun v hv => h1 v ?_, fun t ht => h2 t ?_, fun f hf => h3 f ?_⟩
      · simp only [Stmt.usesList, Stmt.uses, List.mem_append, List.mem_cons]
        exact Or.inl (Or.inr (Or.inr hv))
      · simp only [Stmt.tmpsList, Stmt.tmps, List.mem_append]; exact Or.inl (Or.inr ht)
      · simp [callsL, callsS, hf]
  | @arm x arms rest a _ ha ih =>
      obtain ⟨h1, h2, h3⟩ := ih
      have hu := usesArms_mem ha
      have ht' := tmpsArms_mem ha
      have hc := fun f => callsA_mem (f := f) ha
      refine ⟨fun v hv => h1 v ?_, fun t ht => h2 t ?_, fun f hf => h3 f ?_⟩
      · simp only [Stmt.usesList, Stmt.uses, List.mem_append, List.mem_cons]
        exact Or.inl (Or.inr (hu v hv))
      · simp only [Stmt.tmpsList, Stmt.tmps, List.mem_append]; exact Or.inl (ht' t ht)
      · simp [callsL, callsS, hc f hf]

/-- A statement of a block of a body names only the body's values. -/
theorem inBody_uses {s : Stmt} {rest : List Stmt} (h : InBody body (s :: rest)) :
    ∀ v ∈ Stmt.uses s, v ∈ Stmt.usesList body := fun v hv =>
  (inBody_sub h).1 v (by simp only [Stmt.usesList, List.mem_append]; exact Or.inl hv)

/-- A statement of a block of a body has only the body's temporaries. -/
theorem inBody_tmps {s : Stmt} {rest : List Stmt} (h : InBody body (s :: rest)) :
    ∀ t ∈ Stmt.tmps s, t ∈ Stmt.tmpsList body := fun t ht =>
  (inBody_sub h).2.1 t (by simp only [Stmt.tmpsList, List.mem_append]; exact Or.inl ht)

/-- A statement of a block of a body calls by `call` or `dispatch` only what the body does. -/
theorem inBody_calls {s : Stmt} {rest : List Stmt} (h : InBody body (s :: rest)) (f : String)
    (hf : callsS f s = true) : callsL f body = true :=
  (inBody_sub h).2.2 f (by simp [callsL, hf])

end Body

/-! ## The walk's instance of a function of a compiled program -/

section Inst

variable {κ₀ : ℕ} {W : World κ₀} {tf : TracedFn} {pf : Placed} {fp : ℕ} {hdr : E × E} {σ : Val}
  {es : List Ev} {kfps : List ℕ}

theorem instK_ok (hW : W.Compiled) (htf : tf ∈ W.p) (hpa : World.PlacedAs W tf pf)
    (hta : TmpsApart tf pf) (hrd : ∃ rd, (instOf W tf pf fp hdr σ es).Rd rd) :
    (instK W tf pf fp hdr σ es kfps).Ok :=
  let h := instOf_ok (fp := fp) (hdr := hdr) (σ := σ) (es := es) hW htf hpa hta hrd
  ⟨h.rd, h.kconst, h.ksize, h.tsep, h.tops, h.kend, h.hsh⟩

theorem opOK_K (hW : W.Compiled) (htf : tf ∈ W.p) (hpa : World.PlacedAs W tf pf) (hsc : Scoped tf)
    (hta : TmpsApart tf pf) {vs : List V} (hw : walk σ tf.core.body = .ret es vs)
    (hrd : ∃ rd, (instOf W tf pf fp hdr σ es).Rd rd) :
    OpOK (World.cplSite W tf.core.name) (instK W tf pf fp hdr σ es kfps)
      (agK W tf pf fp hdr es kfps (instK W tf pf fp hdr σ es kfps)) (calls es) :=
  opOK_of hW htf hpa hsc hta hw (instOf_ok hW htf hpa hta hrd) kfps

theorem agOwn_K : AgOwn (instK W tf pf fp hdr σ es kfps)
    (agK W tf pf fp hdr es kfps (instK W tf pf fp hdr σ es kfps)) :=
  fun _ _ _ _ _ hA n hn => hA.1 n hn

theorem agKids_K : AgKids (ctxOf (loopTable W.p) (sigTable W.p) tf) (instK W tf pf fp hdr σ es kfps)
    (agK W tf pf fp hdr es kfps (instK W tf pf fp hdr σ es kfps)) (calls es) := by
  intro σ' Ψ kh κ L hA i c kfp hc hk
  obtain ⟨h0, h1, h2, h3⟩ := hA.2.1.kid i c kfp hc hk
  exact ⟨h0, h1, h2, h3, fun ht k hk' => hA.2.2.1 i c kfp hc hk ht k hk'⟩

theorem hent_K (hW : W.Compiled) (g : String) :
    kwOf (World.cplSite W tf.core.name) (.entry g) =
      ofK (addressOfIndex ((World.cplSite W tf.core.name).ent g)) := by
  have hp : W.layout.PowOk := layout_gpow _ _
  have hlt : W.ent g < u128Bound := by
    have := World.ent_lt hW g
    unfold u128Bound
    omega
  exact Layout.immediateWord_pow hp hlt

theorem hlocB_K (hW : W.Compiled) (htf : tf ∈ W.p) (hpa : World.PlacedAs W tf pf) (q : ℕ)
    (hq : q ≤ (instK W tf pf fp hdr σ es kfps).ops.length) :
    kwOf (World.cplSite W tf.core.name) (.local q) = (World.cplSite W tf.core.name).tgt q := by
  obtain ⟨pre, post, f, hat⟩ := fnAt_of_placedAs hW htf hpa
  obtain ⟨hent, hfit, hsize⟩ := hat.entry hW
  have h30 := W.logSize_le
  have hlen : (instK W tf pf fp hdr σ es kfps).ops.length = blockSize pf.fn.body :=
    blockOps_length _ _
  have hp : W.layout.PowOk := layout_gpow _ _
  have hlt : W.ent tf.core.name + q < u128Bound := by
    rw [hlen] at hq
    unfold u128Bound
    omega
  exact Layout.immediateWord_pow hp hlt

end Inst

/-! ## The straight-line and call statements of a body -/

section Flat

variable {κ₀ : ℕ} {W : World κ₀} {tf : TracedFn} {pf : Placed} {fp : ℕ} {hdr : E × E} {σ : Val}
  {es : List Ev} {vs : List V} {kfps : List ℕ}

/-- **The straight-line and call statements of a scoped function's body, at the walk's
instance**. -/
theorem flatW_K (hW : W.Compiled) (htf : tf ∈ W.p) (hsc : Scoped tf) (hpa : World.PlacedAs W tf pf)
    (hta : TmpsApart tf pf) (hns : NoSelfCall tf) (hfp : tf.core.name = "main" → fp = 0)
    (hw : walk σ tf.core.body = .ret es vs)
    (ha : ∀ q ∈ addrs es, σ q.1 = ofK (addressOfIndex (fp + (cellP pf.locs q.2).getD 0)))
    (hrd : ∃ rd, (instOf W tf pf fp hdr σ es).Rd rd) :
    FlatW (World.cplSite W tf.core.name)
      (agK W tf pf fp hdr es kfps (instK W tf pf fp hdr σ es kfps)) (calls es)
      (ctxOf (loopTable W.p) (sigTable W.p) tf) (instK W tf pf fp hdr σ es kfps)
      (InBody tf.core.body) := by
  have hI := instK_ok (kfps := kfps) hW htf hpa hta hrd
  have hok := opOK_K (kfps := kfps) hW htf hpa hsc hta hw hrd
  have hfresh := hta.fresh
  have hmain : (ctxOf (loopTable W.p) (sigTable W.p) tf).isMain = true →
      (instK W tf pf fp hdr σ es kfps).fp = 0 := fun h => hfp (by simpa [ctxOf] using h)
  have hRd : ∀ rd, (instK W tf pf fp hdr σ es kfps).Rd rd →
      ∀ e ∈ (instK W tf pf fp hdr σ es kfps).es, evNT rd (instK W tf pf fp hdr σ es kfps).σ e :=
    fun _ h => h
  have hnt : ∀ v ∈ Stmt.usesList tf.core.body, v ∉ (instK W tf pf fp hdr σ es kfps).tmps :=
    fun v hv ht => (hfresh.2 v ht).1 hv
  have hnoself : callsL tf.core.name tf.core.body = false := by
    unfold NoSelfCall noSelfCallB at hns
    simpa using hns
  intro s rest tl hin hite hmatch hcif
  have hus := inBody_uses hin
  have hut := inBody_tmps hin
  cases s with
  | atom a =>
      have hu : ∀ v ∈ atomUses a, v ∉ (instK W tf pf fp hdr σ es kfps).tmps :=
        fun v hv => hnt v (hus v hv)
      have ht : ∀ t ∈ atomTmps a, t ∈ (instK W tf pf fp hdr σ es kfps).tmps :=
        fun t ht => hut t ht
      have hnm : ∀ v ∈ atomUses a, v ∈ (instK W tf pf fp hdr σ es kfps).named :=
        fun v hv => List.mem_append_left _ (hus v hv)
      by_cases hfa : ∃ p run, a = .frameAddr p run
      · obtain ⟨p, run, rfl⟩ := hfa
        refine stmtW_frameAddr poolKeepStmt hok hI hmain hRd hu ht hnm ?_
        intro q hq
        replace hq : q ∈ addrs es := hq
        have hwi := walk_within (σ := σ) tf.core.body
        rw [hw] at hwi
        obtain ⟨e, he, hq'⟩ : ∃ e ∈ es, Ev.addr? e = some q := by
          simpa [addrs, List.mem_filterMap] using hq
        have hu1 : q.1 ∈ e.uses := by
          match e, hq' with
          | .atom (.frameAddr p (r :: rs)), hq' =>
            simp only [Ev.addr?, Option.some.injEq] at hq'
            subst hq'
            simp [Ev.uses, atomUses]
        have hnq : q.1 ∉ Stmt.tmpsList tf.core.body := fun ht => (hfresh.2 _ ht).1 (hwi.1 e he _ hu1)
        show zeroTmps (Stmt.tmpsList tf.core.body) σ q.1 = _
        rw [zeroTmps_off hnq]
        exact ha q hq
      · exact stmtW_atom' poolKeepStmt hok hI hmain hRd hu ht hnm
          (fun p run h => hfa ⟨p, run, h⟩) hI.hsh
  | ite c z nz => exact absurd rfl (hite c z nz)
  | match_ x arms => exact absurd rfl (hmatch x arms)
  | call f args rets =>
      refine stmtW_call poolKeepStmt hok hI agOwn_K agKids_K (fun _ => rfl) (hent_K hW) ?_
        (fun v hv => hnt v (hus v (by simpa [Stmt.uses] using hv)))
      intro hf
      have := inBody_calls hin tf.core.name (by simp [callsS, hf, ctxOf])
      rw [hnoself] at this
      cases this
  | callIf c f args =>
      exact stmtW_callIf poolKeepStmt hok hI hRd agOwn_K agKids_K (fun _ => rfl) (hent_K hW)
        (hcif c f args rfl) (fun v hv => hnt v (hus v (by simpa [Stmt.uses] using hv)))
  | dispatch x fs args rets =>
      refine stmtW_dispatch poolKeepStmt hok hI agOwn_K agKids_K (fun _ => rfl)
        (fun q hq => hlocB_K hW htf hpa q hq) ?_
        (fun v hv => hnt v (hus v (by simpa [Stmt.uses] using hv)))
      intro g hg hgn
      have := inBody_calls hin tf.core.name (by
        simp only [callsS]
        rw [List.contains_iff_mem]
        rw [hgn] at hg
        simpa [ctxOf] using hg)
      rw [hnoself] at this
      cases this
  | ret rvs => exact stmtW_ret' hok hI hmain agOwn_K hI.kend

end Flat

/-! ## The block lemma at a body -/

/-- The quantifiers of `BodyW`: a scoped function of a compiled program with temporaries apart and
no direct self call, at a frame, callee frames and header, on a path of `σ` whose addresses are
its frame's and whose events hold on some reader; `P` of its body at the walk's instance. -/
def AtBody (P : ∀ {κ₀ : ℕ}, World κ₀ → TracedFn → Placed → ℕ → E × E → Val → List Ev →
    List ℕ → Prop) : Prop :=
  ∀ {κ₀ : ℕ} (W : World κ₀), W.Compiled → ∀ tf ∈ W.p, Scoped tf → ∀ pf, World.PlacedAs W tf pf →
  TmpsApart tf pf → NoSelfCall tf →
  ∀ (fp : ℕ), (tf.core.name = "main" → fp = 0) → ∀ (kfps : List ℕ) (hdr : E × E) (σ : Val)
    (es : List Ev) (vs : List V), walk σ tf.core.body = .ret es vs →
    (∀ q ∈ addrs es, σ q.1 = ofK (addressOfIndex (fp + (cellP pf.locs q.2).getD 0))) →
    (∃ rd, (instOf W tf pf fp hdr σ es).Rd rd) → P W tf pf fp hdr σ es kfps

/-- **No value a statement of a body reads is a later frame address's** (owed: from `Scoped`). -/
def FaBody : Prop := AtBody fun W tf pf fp hdr σ es kfps =>
  ∀ s rest, InBody tf.core.body (s :: rest) →
    FaAfter (instK W tf pf fp hdr σ es kfps).σ s rest

/-- **A body's self `callIf`s** (owed: `selfW_of`, once its loop premise is under `PremW`). -/
def SelfBody : Prop := AtBody fun W tf pf fp hdr σ es kfps =>
  SelfW (World.cplSite W tf.core.name) (agK W tf pf fp hdr es kfps (instK W tf pf fp hdr σ es kfps))
    (calls es) (ctxOf (loopTable W.p) (sigTable W.p) tf) (instK W tf pf fp hdr σ es kfps)
    (InBody tf.core.body)

/-- **A body's `match`es and chains** (owed: `MatchW`). -/
def MatchBody : Prop := AtBody fun W tf pf fp hdr σ es kfps =>
  MatchW (World.cplSite W tf.core.name) (agK W tf pf fp hdr es kfps (instK W tf pf fp hdr σ es kfps))
    (calls es) (ctxOf (loopTable W.p) (sigTable W.p) tf) (instK W tf pf fp hdr σ es kfps)
    (InBody tf.core.body)

/-- **The block lemma at a body**, from the constructs' lemmas. -/
theorem bodyW_assembled (hfa : FaBody) (hself : SelfBody) (hmatch : MatchBody) : BodyW := by
  intro κ₀ W hW tf htf hsc pf hpa hta hns fp hfp kfps hdr σ es vs hw ha hrd
  have hI := instK_ok (kfps := kfps) hW htf hpa hta hrd
  have hok := opOK_K (kfps := kfps) hW htf hpa hsc hta hw hrd
  have hfresh := hta.fresh
  have hmain : (ctxOf (loopTable W.p) (sigTable W.p) tf).isMain = true →
      (instK W tf pf fp hdr σ es kfps).fp = 0 := fun h => hfp (by simpa [ctxOf] using h)
  exact bodyW_of tf.core.body hok hI
    (hfa W hW tf htf hsc pf hpa hta hns fp hfp kfps hdr σ es vs hw ha hrd)
    (flatW_K hW htf hsc hpa hta hns hfp hw ha hrd)
    (hself W hW tf htf hsc pf hpa hta hns fp hfp kfps hdr σ es vs hw ha hrd)
    (fun c z nz rest hin ht => (hfresh.2 c ht).1
      (inBody_uses hin c (by simp [Stmt.uses])))
    (iteStmt hok hI hmain (fun _ h => h) agOwn_K (fun _ => rfl)
      (fun q hq => hlocB_K hW htf hpa q hq))
    (hmatch W hW tf htf hsc pf hpa hta hns fp hfp kfps hdr σ es vs hw ha hrd) []

/-- **The frame side's statement**, from the remaining construct lemmas. -/
theorem frameWords_assembled (hfa : FaBody) (hself : SelfBody) (hmatch : MatchBody) :
    FrameWordsStmt :=
  frameWords_of_body (bodyW_assembled hfa hself hmatch)

/-- info: 'LeanVM.Compiler.Complete.frameWords_assembled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms frameWords_assembled

/-- **A body's self `callIf`s** at the walk's instance. -/
theorem selfBody : SelfBody := by
  intro κ₀ W hW tf htf hsc pf hpa hta hns fp hfp kfps hdr σ es vs hw ha hrd
  have hI := instK_ok (kfps := kfps) hW htf hpa hta hrd
  have hok := opOK_K (kfps := kfps) hW htf hpa hsc hta hw hrd
  have hfresh := hta.fresh
  refine selfW_of placeNew_ok poolKeepStmt hok hI (fun h => hfp (by simpa [ctxOf] using h))
    (fun _ h => h) agOwn_K agKids_K (fun _ => rfl) (hent_K hW) (fun h => by simpa [ctxOf] using h)
    hI.kend (fun hreg => ⟨frame_of_loopH hW htf hpa hreg, hreg⟩) ?_
  intro c f args rest hin v hv ht
  exact (hfresh.2 v ht).1 (inBody_uses hin v (by simpa [Stmt.uses] using hv))

/-- **The frame side's statement**, from the remaining construct lemmas. -/
theorem frameWords_of_fa_match (hfa : FaBody) (hmatch : MatchBody) : FrameWordsStmt :=
  frameWords_assembled hfa selfBody hmatch

/-- info: 'LeanVM.Compiler.Complete.frameWords_of_fa_match' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms frameWords_of_fa_match

/-! ## The `match`es of a body -/

/-- **No value an arm's path reads is a later arm's frame address** (owed: from `Scoped`). -/
def AFaBody : Prop := AtBody fun W tf pf fp hdr σ es kfps =>
  ∀ x arms rest, InBody tf.core.body (.match_ x arms :: rest) → ∀ j (hj : j < arms.length),
    ∀ v ∈ pathVals (instK W tf pf fp hdr σ es kfps).σ arms[j]
      (walk (instK W tf pf fp hdr σ es kfps).σ arms[j]), ∀ run,
      Atom.frameAddr v run ∉ armsAtoms (arms.drop (j + 1))

/-- **A body's chains of `match`es** (owed: `ChainHeadW`). -/
def ChainBody : Prop := AtBody fun W tf pf fp hdr σ es kfps =>
  ChainHeadW (Γ := World.cplSite W tf.core.name)
    (Ag := agK W tf pf fp hdr es kfps (instK W tf pf fp hdr σ es kfps)) (cl := calls es)
    (ctx := ctxOf (loopTable W.p) (sigTable W.p) tf) (I := instK W tf pf fp hdr σ es kfps)
    (InBody tf.core.body)

/-- **A body's `match`es**, from the arms' frame address fact and the chains. -/
theorem matchBody_of (hfa : FaBody) (hafa : AFaBody) (hch : ChainBody) : MatchBody := by
  intro κ₀ W hW tf htf hsc pf hpa hta hns fp hfp kfps hdr σ es vs hw ha hrd
  have hI := instK_ok (kfps := kfps) hW htf hpa hta hrd
  have hok := opOK_K (kfps := kfps) hW htf hpa hsc hta hw hrd
  have hfresh := hta.fresh
  exact matchW_of placeMono placeNew_ok hok hI (fun h => hfp (by simpa [ctxOf] using h)) agOwn_K
    (fun _ => rfl) (fun q hq => hlocB_K hW htf hpa q hq)
    (fun x arms rest hg => ⟨fun a ha => .arm hg ha, .tail hg⟩)
    (hfa W hW tf htf hsc pf hpa hta hns fp hfp kfps hdr σ es vs hw ha hrd)
    (fun x arms rest hin ht => (hfresh.2 x ht).1 (inBody_uses hin x (by simp [Stmt.uses])))
    (hafa W hW tf htf hsc pf hpa hta hns fp hfp kfps hdr σ es vs hw ha hrd)
    (inBlockOf hok hI) (hch W hW tf htf hsc pf hpa hta hns fp hfp kfps hdr σ es vs hw ha hrd)

/-- **The frame side's statement**, from the frame address facts and the chains. -/
theorem frameWords_of_fa_chain (hfa : FaBody) (hafa : AFaBody) (hch : ChainBody) :
    FrameWordsStmt :=
  frameWords_of_fa_match hfa (matchBody_of hfa hafa hch)

/-- info: 'LeanVM.Compiler.Complete.frameWords_of_fa_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms frameWords_of_fa_chain

end
end LeanVM.Compiler.Complete
