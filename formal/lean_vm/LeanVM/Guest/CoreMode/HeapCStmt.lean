/-
  LeanVM.Guest.CoreMode.HeapCStmt

  The heap check's soundness: the events a path covers, and each statement's pass.
-/

module

public import LeanVM.Guest.CoreMode.HeapCInv

/-!
# Covered events and statements

What a path's events write (`EW`, `Cov`), and each statement's pass sound on its events: an atom, a call, a conditional call, a dispatch, a return.
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Exec (Trie PowTree natSeq natSeq_eq)
open LeanVM.Guest.Check (getF setF getF_eq setF_eq)

@[expose] public section

/-! ## Covered events -/

section Cov

variable {sigOf : String → HSig} {H : HCert} {σ : Val} {rd : Reader}

/-- An address an event of `es` writes. -/
def EW (sigOf : String → HSig) (rd : Reader) (σ : Val) (es : List Ev) (x : K) : Prop := ∃ e ∈ es, EvW sigOf rd σ e x

/-- **The needs of `es` are covered**: each event's in `W` or written by the events before it, once the calls
before it have their callees' returned words (`EvM`, a property of the calls already made). -/
def CovC (sigOf : String → HSig) (H : HCert) (rd : Reader) (σ : Val) (W : K → Prop) (es : List Ev) : Prop :=
  ∀ es1 e es2, es = es1 ++ e :: es2 → (∀ e' ∈ es1, EvM sigOf rd σ e') →
    ReqOk sigOf H rd σ (fun x ↦ W x ∨ EW sigOf rd σ es1 x) e

/-- The events hold, and each entered call's callee's returned words' monomials (`EvM`). -/
def EvsOk (sigOf : String → HSig) (rd : Reader) (σ : Val) (es : List Ev) : Prop :=
  ∀ e ∈ es, e.Holds rd σ ∧ EvM sigOf rd σ e

/-- The own guarantees written in `W` at the parameters' words `ws0` and the returned `vs`, the
returned words' monomials, and the words at return. -/
def PostW0 (_sigOf : String → HSig) (H : HCert) (rd : Reader) (σ : Val) (ws0 : List E) (W : K → Prop)
    (vs : List V) : Prop :=
  SigOk W H.sig.post H.sig.postR (ws0 ++ vs.map σ) ∧ PtrOk W rd H.sig.postP H.sig.postPR (ws0 ++ vs.map σ) ∧
    RetMOk H.sig ws0 (vs.map σ) ∧ RetVOk rd H.sig (ws0 ++ vs.map σ) ∧ RetEqOk H.sig (ws0 ++ vs.map σ) ∧
    (∀ x, QSet rd H.sig.postQ (ws0 ++ vs.map σ) x → W x) ∧
    SigOk W H.sig.postN H.sig.postRN (H.sig.nv.map (vw σ))

/-- **The frame run cells the certificate guarantees at return** (`HCert.fas`), at `σ`. -/
def FAX (H : HCert) (σ : Val) (x : K) : Prop := ∃ p ∈ H.fas, x = cellAt σ (V.n p.1) p.2

/-- `PostW0` in `W` or among the frame run cells guaranteed at return. -/
def PostW (_sigOf : String → HSig) (H : HCert) (rd : Reader) (σ : Val) (ws0 : List E) (W : K → Prop) (vs : List V) :
    Prop :=
  PostW0 _sigOf H rd σ ws0 (fun x ↦ W x ∨ FAX H σ x) vs

theorem SigOk.mono {W W' : K → Prop} (hw : ∀ x, W x → W' x) {cs : List CCell} {rs : List CRun} {ws : List E}
    (h : SigOk W cs rs ws) : SigOk W' cs rs ws :=
  ⟨fun c hc ↦ hw _ (h.1 c hc), fun r hr ↦ (h.2 r hr).mono hw⟩

theorem ReqOk.mono {W W' : K → Prop} (hw : ∀ x, W x → W' x) : ∀ {e : Ev}, ReqOk sigOf H rd σ W e →
    ReqOk sigOf H rd σ W' e
  | .atom _, h => fun x hx ↦ hw x (h x hx)
  | .call .., h => ⟨fun k hk c hc ↦ hw _ (h.1 k hk c hc), fun hd ↦
      ⟨(h.2 hd).1, SigOk.mono hw (h.2 hd).2.1, fun x hx ↦ hw _ ((h.2 hd).2.2 x hx)⟩⟩
  | .inK _, _ => trivial
  | .skip .., _ => trivial

theorem CovC.mono {W W' : K → Prop} (hw : ∀ x, W x → W' x) {es : List Ev} (h : CovC sigOf H rd σ W es) :
    CovC sigOf H rd σ W' es :=
  fun es1 e es2 he hm ↦ (h es1 e es2 he hm).mono fun x hx ↦ hx.imp_left (hw x)

theorem covC_nil (W : K → Prop) : CovC sigOf H rd σ W [] := fun es1 _ _ he ↦ by simp at he

theorem ew_append_left {es1 es2 : List Ev} {x : K} (h : EW sigOf rd σ es1 x) : EW sigOf rd σ (es1 ++ es2) x :=
  let ⟨e, he, hx⟩ := h
  ⟨e, List.mem_append_left _ he, hx⟩

theorem ew_append_right {es1 es2 : List Ev} {x : K} (h : EW sigOf rd σ es2 x) : EW sigOf rd σ (es1 ++ es2) x :=
  let ⟨e, he, hx⟩ := h
  ⟨e, List.mem_append_right _ he, hx⟩

theorem covC_append {W : K → Prop} {es1 es2 : List Ev} (h1 : CovC sigOf H rd σ W es1)
    (h2 : (∀ e ∈ es1, EvM sigOf rd σ e) → CovC sigOf H rd σ (fun x ↦ W x ∨ EW sigOf rd σ es1 x) es2) :
    CovC sigOf H rd σ W (es1 ++ es2) := by
  intro p e q he hm
  rcases List.append_eq_append_iff.mp he with ⟨a', rfl, h⟩ | ⟨c', rfl, h⟩
  · refine (h2 (fun e he ↦ hm e (List.mem_append_left _ he)) a' e q h
      (fun e he ↦ hm e (List.mem_append_right _ he))).mono fun x hx ↦ ?_
    rcases hx with (hx | hx) | hx
    · exact Or.inl hx
    · exact Or.inr (ew_append_left hx)
    · exact Or.inr (ew_append_right hx)
  · cases c' with
    | nil =>
      simp only [List.nil_append] at h
      refine (h2 (fun e he ↦ hm e (by simpa using he)) [] e q (by rw [← h]; rfl) (by simp)).mono fun x hx ↦ ?_
      rcases hx with hx | ⟨_, hb, _⟩
      · simpa using hx
      · simp at hb
    | cons e' c'' =>
      rw [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact h1 p e c'' rfl hm

theorem covC_single {W : K → Prop} {e : Ev} (h : ReqOk sigOf H rd σ W e) : CovC sigOf H rd σ W [e] := by
  intro p b q he _
  cases p with
  | nil =>
    rw [List.nil_append, List.cons.injEq] at he
    obtain ⟨rfl, -⟩ := he
    exact h.mono fun x hx ↦ Or.inl hx
  | cons _ p => simp at he

theorem holds_append {es1 es2 : List Ev} (h : ∀ e ∈ es1 ++ es2, e.Holds rd σ) :
    (∀ e ∈ es1, e.Holds rd σ) ∧ ∀ e ∈ es2, e.Holds rd σ :=
  ⟨fun e he ↦ h e (List.mem_append_left _ he), fun e he ↦ h e (List.mem_append_right _ he)⟩

theorem evsOk_of {es : List Ev} (hh : ∀ e ∈ es, e.Holds rd σ) (hm : ∀ e ∈ es, EvM sigOf rd σ e) :
    EvsOk sigOf rd σ es := fun e he ↦ ⟨hh e he, hm e he⟩

theorem evsOk_append {es1 es2 : List Ev} (h : EvsOk sigOf rd σ (es1 ++ es2)) :
    EvsOk sigOf rd σ es1 ∧ EvsOk sigOf rd σ es2 :=
  ⟨fun e he ↦ h e (List.mem_append_left _ he), fun e he ↦ h e (List.mem_append_right _ he)⟩

/-- **What an outcome gives**: its events holding, its needs covered; returning, each call's returned words
given (`EvsOk`), the own guarantees written. -/
def OutC (sigOf : String → HSig) (H : HCert) (σ : Val) (rd : Reader) (ws0 : List E) (W : K → Prop) (o : Out) :
    Prop :=
  (∀ es, o = .fall es → (∀ e ∈ es, e.Holds rd σ) → CovC sigOf H rd σ W es) ∧
  (∀ es vs, o = .ret es vs → (∀ e ∈ es, e.Holds rd σ) →
    CovC sigOf H rd σ W es ∧ (EvsOk sigOf rd σ es → PostW sigOf H rd σ ws0 (fun x ↦ W x ∨ EW sigOf rd σ es x) vs))

/-- **What a block's pass gives on the path**: its outcome's, and, falling through, the state at
its end valid. -/
def BlockC (sigOf : String → HSig) (H : HCert) (σ : Val) (rd : Reader) (ws0 : List E) (W : K → Prop) (o : Out)
    (st' : CSt) : Prop :=
  OutC sigOf H σ rd ws0 W o ∧
    ∀ es, o = .fall es → EvsOk sigOf rd σ es → StOk rd (fun x ↦ W x ∨ EW sigOf rd σ es x) σ st'

theorem PostW0.mono {ws0 : List E} {W W' : K → Prop} (hw : ∀ x, W x → W' x) {vs : List V}
    (h : PostW0 sigOf H rd σ ws0 W vs) : PostW0 sigOf H rd σ ws0 W' vs :=
  ⟨SigOk.mono hw h.1, fun x hx ↦ hw _ (h.2.1 x hx), h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
    fun x hx ↦ hw _ (h.2.2.2.2.2.1 x hx), SigOk.mono hw h.2.2.2.2.2.2⟩

theorem PostW.mono {ws0 : List E} {W W' : K → Prop} (hw : ∀ x, W x → W' x) {vs : List V}
    (h : PostW sigOf H rd σ ws0 W vs) : PostW sigOf H rd σ ws0 W' vs :=
  PostW0.mono (fun x hx ↦ hx.imp_left (hw x)) h

theorem PostW0.toW {ws0 : List E} {W : K → Prop} {vs : List V} (h : PostW0 sigOf H rd σ ws0 W vs) :
    PostW sigOf H rd σ ws0 W vs :=
  h.mono fun _ ↦ Or.inl

theorem outC_pre {ws0 : List E} {W : K → Prop} {o : Out} (h : OutC sigOf H σ rd ws0 W o) (c : V) :
    OutC sigOf H σ rd ws0 W (o.pre [.inK c]) := by
  have key : ∀ es', CovC sigOf H rd σ W es' → CovC sigOf H rd σ W ([Ev.inK c] ++ es') := fun es' hc ↦
    covC_append (covC_single trivial) fun _ ↦ hc.mono fun _ ↦ Or.inl
  have hew : ∀ es' x, (W x ∨ EW sigOf rd σ es' x) → (W x ∨ EW sigOf rd σ ([Ev.inK c] ++ es') x) := fun es' x hx ↦
    hx.imp_right ew_append_right
  refine ⟨fun es hw hh ↦ ?_, fun es vs hw hh ↦ ?_⟩
  · cases o with
    | fall es' =>
      simp only [Out.pre, Out.fall.injEq] at hw
      subst hw
      exact key es' (h.1 es' rfl (holds_append hh).2)
    | ret => simp [Out.pre] at hw
    | stuck => simp [Out.pre] at hw
  · cases o with
    | ret es' vs' =>
      simp only [Out.pre, Out.ret.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      obtain ⟨h1, h2⟩ := h.2 es' vs' rfl (holds_append hh).2
      exact ⟨key es' h1, fun hm ↦ (h2 (evsOk_append hm).2).mono (hew es')⟩
    | fall => simp [Out.pre] at hw
    | stuck => simp [Out.pre] at hw

/-- **A statement, then a block.** -/
theorem blockC_seq {ws0 : List E} {W : K → Prop} {o1 : Out} {ss : List Stmt} {st' : CSt}
    {W1 : List Ev → K → Prop} (h1 : OutC sigOf H σ rd ws0 W o1)
    (h2 : ∀ es, o1 = .fall es → EvsOk sigOf rd σ es →
      (∀ x, W1 es x → W x ∨ EW sigOf rd σ es x) ∧ BlockC sigOf H σ rd ws0 (W1 es) (walk σ ss) st') :
    BlockC sigOf H σ rd ws0 W (o1.seq (walk σ ss)) st' := by
  cases o1 with
  | fall es1 =>
    have hW : ∀ es2 x, EvsOk sigOf rd σ es1 → (W1 es1 x ∨ EW sigOf rd σ es2 x) →
        (W x ∨ EW sigOf rd σ (es1 ++ es2) x) := fun es2 x hh hx ↦ by
      rcases hx with hx | hx
      · rcases (h2 es1 rfl hh).1 x hx with hx | hx
        · exact Or.inl hx
        · exact Or.inr (ew_append_left hx)
      · exact Or.inr (ew_append_right hx)
    have hcov : ∀ es2, (∀ e ∈ es1 ++ es2, e.Holds rd σ) →
        ((∀ e ∈ es1, EvM sigOf rd σ e) → CovC sigOf H rd σ (W1 es1) es2) →
        CovC sigOf H rd σ W (es1 ++ es2) := fun es2 hh hc ↦
      covC_append (h1.1 es1 rfl (holds_append hh).1)
        fun hm ↦ (hc hm).mono fun x hx ↦ (h2 es1 rfl (evsOk_of (holds_append hh).1 hm)).1 x hx
    refine ⟨⟨fun es hw hh ↦ ?_, fun es vs hw hh ↦ ?_⟩, fun es hw hh ↦ ?_⟩
    · simp only [Out.seq] at hw
      cases hk : walk σ ss with
      | fall es2 =>
        rw [hk] at hw
        simp only [Out.pre, Out.fall.injEq] at hw
        subst hw
        exact hcov es2 hh fun hm ↦
          (h2 es1 rfl (evsOk_of (holds_append hh).1 hm)).2.1.1 es2 hk (holds_append hh).2
      | ret => rw [hk] at hw; simp [Out.pre] at hw
      | stuck => rw [hk] at hw; simp [Out.pre] at hw
    · simp only [Out.seq] at hw
      cases hk : walk σ ss with
      | ret es2 vs2 =>
        rw [hk] at hw
        simp only [Out.pre, Out.ret.injEq] at hw
        obtain ⟨rfl, rfl⟩ := hw
        refine ⟨hcov es2 hh fun hm ↦
          ((h2 es1 rfl (evsOk_of (holds_append hh).1 hm)).2.1.2 es2 vs2 hk (holds_append hh).2).1, fun he ↦ ?_⟩
        exact (((h2 es1 rfl (evsOk_append he).1).2.1.2 es2 vs2 hk (holds_append hh).2).2
          (evsOk_append he).2).mono fun x hx ↦ hW es2 x (evsOk_append he).1 hx
      | fall => rw [hk] at hw; simp [Out.pre] at hw
      | stuck => rw [hk] at hw; simp [Out.pre] at hw
    · simp only [Out.seq] at hw
      cases hk : walk σ ss with
      | fall es2 =>
        rw [hk] at hw
        simp only [Out.pre, Out.fall.injEq] at hw
        subst hw
        exact ((h2 es1 rfl (evsOk_append hh).1).2.2 es2 hk (evsOk_append hh).2).mono
          fun x hx ↦ hW es2 x (evsOk_append hh).1 hx
      | ret => rw [hk] at hw; simp [Out.pre] at hw
      | stuck => rw [hk] at hw; simp [Out.pre] at hw
  | ret es1 vs1 =>
    refine ⟨⟨fun es hw _ ↦ by simp [Out.seq] at hw, fun es vs hw hh ↦ ?_⟩, fun es hw _ ↦ by simp [Out.seq] at hw⟩
    simp only [Out.seq, Out.ret.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    exact h1.2 es1 vs1 rfl hh
  | stuck =>
    exact ⟨⟨fun es hw _ ↦ by simp [Out.seq] at hw, fun es vs hw _ ↦ by simp [Out.seq] at hw⟩,
      fun es hw _ ↦ by simp [Out.seq] at hw⟩

end Cov

/-! ## Statements -/

section Stmts

variable {sigOf : String → HSig} {H : HCert} {f : Fn} {X : CX} {σ : Val} {rd : Reader} {W : K → Prop}

theorem bitsOk_ok (hX : XOk sigOf H rd f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt}
    (hs : StOk rd W σ st) {m : CCell} {dst p : V} {off : ℕ} :
    ∀ {k n : ℕ}, bitsOk X st m dst p off k n = true → ∀ k', k ≤ k' → k' < k + n → W ((m.shift (off + k')).addr σ)
  | _, 0, _, k', h1, h2 => by omega
  | k, n + 1, h, k', h1, h2 => by
    simp only [bitsOk, Bool.and_eq_true] at h
    obtain ⟨h0, hr⟩ := h
    rcases Nat.eq_or_lt_of_le h1 with rfl | h1
    · cases hw : readWitT X.R dst p (off + k) with
      | none => rw [hw] at h0; cases h0
      | some w => rw [hw] at h0; exact ptOk_ok hX hpre hs h0
    · exact bitsOk_ok hX hpre hs hr k' (by omega) (by omega)

theorem atomC_other {st : CSt} {a : Atom} (hl : ∀ d p off, a ≠ .load d p off) (ha : ∀ d x y, a ≠ .add d x y)
    (hm : ∀ d x y, a ≠ .mul d x y) (hg : ∀ p off len nb fl dst, a ≠ .hint (.log2Ceil (.heap p off len) nb fl dst)) :
    atomC0 X st a = (atomH X.toH st.toH a).map st.ofH := by
  cases a with
  | hint h =>
    cases h with
    | log2Ceil bits nb fl dst =>
      cases bits with
      | heap p off len => exact absurd rfl (hg p off len nb fl dst)
      | stack _ => rfl
    | _ => rfl
  | _ => first | rfl | exact absurd rfl (hl _ _ _) | exact absurd rfl (ha _ _ _) | exact absurd rfl (hm _ _ _)

/-- A read through a load event of its cell: the word stored there. -/
theorem hvDef_ok {st : CSt} (hs : StOk rd W σ st) {c : CCell} {d : V} (hd : rd (c.addr σ) = some (σ d)) :
    ∀ w, StOk rd W σ (hvDef X st c d w)
  | .ev n => by
    unfold hvDef
    dsimp only
    cases hk : vnum d with
    | none => exact hs
    | some k =>
      dsimp only
      cases hv : getF X.hv k with
      | none => exact hs
      | some _ =>
      cases hn : getF st.sv n with
      | none => exact hs
      | some p =>
        dsimp only
        cases hb : p.1.beq c with
        | false => exact hs
        | true =>
          refine def_stOk hs ?_
          have := hs.sv n p hn
          rw [CCell.beq_eq hb, hd, Option.some.injEq] at this
          rw [← vnum_eq hk, this, val_eq]
  | .pre _ => hs
  | .run _ _ => hs
  | .res _ => hs
  | .pf _ => hs
  | .pfr _ _ => hs
  | .word _ => hs
  | .pts => hs
  | .empty => hs
  | .skip _ => hs
  | .cat _ => hs
  | .mrg _ _ => hs
  | .perm _ _ => hs
  | .prep _ _ _ => hs
  | .app _ _ _ => hs
  | .keep _ _ _ _ => hs

  | .prep2 _ _ _ _ => hs
  | .vp _ _ => hs
  | .catM _ _ _ => hs
  | .mrgE _ _ _ => hs
  | .ab _ _ _ => hs
  | .abx _ _ _ _ _ => hs
  | .evs _ _ _ => hs
  | .back _ _ _ => hs
  | .der _ _ _ _ _ _ => hs
  | .wnil => hs
  | .wcons _ _ => hs
  | .drv _ _ _ _ _ => hs

/-- **The runs at a word read**: the cell `c` holding `m`'s word, its runs at words into the run scope. -/
theorem promoteQ_ok {st : CSt} (hs : StOk rd W σ st) {c m : CCell} (hm : rd (c.addr σ) = some (m.valW (vw σ))) :
    StOk rd W σ (promoteQ c m st) := by
  unfold promoteQ
  refine pushRL_ok hs (fun _ h ↦ h) fun q hq x hx ↦ ?_
  obtain ⟨p, hp, he⟩ := List.mem_filterMap.mp hq
  cases hb : p.1.beq c with
  | false => rw [hb] at he; cases he
  | true =>
    rw [hb] at he
    simp only [Bool.cond_true, Option.some.injEq] at he
    subst he
    obtain ⟨ylo, yhi, j, h1, h2, h3, h4, h5⟩ := hx
    refine hs.dq p hp _ (by rw [CCell.beq_eq hb]; exact hm) x ⟨ylo, yhi, j, h1, h2, h3, h4, ?_⟩
    rw [h5, valW_mul]

theorem gwDef_ok {G : HSig} (hG : GwOk G rd σ) {st : CSt} (hs : StOk rd W σ st) {c : CCell} {d : V}
    (hd : rd (c.addr σ) = some (σ d)) : StOk rd W σ (gwDef G st c d) := by
  unfold gwDef
  cases hk : vnum d with
  | none => exact hs
  | some k =>
    cases hp : G.gw.find? (fun p ↦ p.1.beq c) with
    | none => exact hs
    | some p =>
      dsimp only
      refine def_stOk hs ?_
      have hb : p.1.beq c = true := List.find?_some (p := fun q : CCell × ℕ ↦ q.1.beq c) hp
      have hm' : (c, p.2) ∈ G.gw := by
        rw [← CCell.beq_eq hb]
        exact List.mem_of_find?_eq_some hp
      rw [addr_eq] at hd
      rw [val_baseC, ← vnum_eq hk]
      exact (hG c p.2 hm' _ hd).symm

theorem loadPush_ok {st : CSt} (hs : StOk rd W σ st) {W' : K → Prop} (hw : ∀ x, W x → W' x) {c : CCell} {d : V}
    (hc : W' (c.addr σ)) (hd : rd (c.addr σ) = some (σ d)) : StOk rd W' σ (loadPush st c d) := by
  unfold loadPush
  cases hm : monoOf st.env d with
  | none =>
    dsimp only
    rw [CSt.seq_eq]
    exact srcPut_stOk (push_stOk hs hw hc) hd
  | some m =>
    dsimp only
    rw [CSt.seq_eq, CSt.seq_eq]
    have hm' : rd (c.addr σ) = some (m.valW (vw σ)) := by rw [hd, monoOf_ok hs.env hm, val_eq]
    exact promoteQ_ok (srcPut_stOk (pushV_stOk hs hw hc hm') hd) hm'

/-- A division's quotient: its word. -/
theorem divOf_ok {st : CSt} (hs : StOk rd W σ st) {d q b : V} (hq : σ d = σ q * σ b) {k : ℕ} {c : CCell}
    (h : divOf X st d q b = some (k, c)) : σ (V.n k) = c.val σ := by
  unfold divOf at h
  cases hkq : vnum q with
  | none => simp [hkq] at h
  | some kq =>
    cases hdv : getF X.dv kq with
    | none => simp [hkq, hdv] at h
    | some u =>
      cases hkd : vnum d with
      | none => simp [hkq, hdv, hkd] at h
      | some kd =>
        cases hmd : getF st.env kd with
        | none => simp [hkq, hdv, hkd, hmd] at h
        | some md =>
          cases hmb : monoOf st.env b with
          | none => simp [hkq, hdv, hkd, hmd, hmb] at h
          | some mb =>
            simp only [hkq, hdv, hkd, hmd, hmb] at h
            cases hc : (mb.bases.isEmpty && Nat.ble mb.off md.off) with
            | false => rw [hc] at h; simp at h
            | true =>
              rw [hc] at h
              simp only [Bool.cond_true, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              simp only [Bool.and_eq_true] at hc
              obtain ⟨hb0, hle⟩ := hc
              have hle := Nat.le_of_ble_eq_true hle
              have hdv' : σ d = md.val σ := by rw [vnum_eq hkd]; exact hs.env kd md hmd
              have hbv : σ b = ofK (addressOfIndex mb.off) := by
                rw [monoOf_ok hs.env hmb, val_eq, valW_nil hb0]
              have hsplit : addressOfIndex md.off = addressOfIndex (md.off - mb.off) * addressOfIndex mb.off := by
                simp only [addressOfIndex, ← pow_add, Nat.sub_add_cancel hle]
              rw [← vnum_eq hkq]
              apply mul_right_cancel₀ (ofK_gpow_ne_zero mb.off)
              rw [← hbv, ← hq, hdv', hbv, CCell.val, CCell.val, hsplit, ofK_mul, mul_assoc]

/-- The returned values' monomials: each the word it is. -/
theorem retDefs_ok {rets : List V} : ∀ {l : List (ℕ × CCell)} {st : CSt}, StOk rd W σ st →
    (∀ k m, (k, m) ∈ l → ∀ r, rets[k]? = some r → σ r = m.valW (vw σ)) → StOk rd W σ (retDefs rets l st)
  | [], _, hs, _ => hs
  | (k, m) :: l, st, hs, hl => by
    have hl' : ∀ k m, (k, m) ∈ l → ∀ r, rets[k]? = some r → σ r = m.valW (vw σ) :=
      fun k m h ↦ hl k m (List.mem_cons_of_mem _ h)
    unfold retDefs
    cases hr : nth rets k with
    | none => exact retDefs_ok hs hl'
    | some r =>
      dsimp only
      cases hk : vnum r with
      | none => exact retDefs_ok hs hl'
      | some kr =>
        simp only [CSt.seq_eq]
        refine retDefs_ok (def_stOk hs ?_) hl'
        rw [← vnum_eq hk, val_eq]
        exact hl k m List.mem_cons_self r (by rw [← nth_eq]; exact hr)

/-- A callee's `retM` at the slots `ms` naming its arguments' words: each returned value its word. -/
theorem instRM_ok {ms : List CCell} {ws : List E} (hms : MsOk (vw σ) ms (slotW ws)) {G : HSig} {rets : List V}
    (hM : RetMOk G ws (rets.map σ)) :
    ∀ k m, (k, m) ∈ instRM ms G.retM → ∀ r, rets[k]? = some r → σ r = m.valW (vw σ) := by
  intro k m hkm r hr
  obtain ⟨⟨k', c⟩, hc, he⟩ := List.mem_filterMap.mp hkm
  cases hi : instC ms c with
  | none => simp [hi] at he
  | some c' =>
    simp only [hi, Option.map_some, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have h1 := hM k' c hc
    rw [List.getElem?_map, hr, Option.map_some, Option.some.injEq] at h1
    rw [h1, instC_ok hms hi]

/-- A `mul`, not a division: `heapOk`'s. -/
theorem atomH_part (hX : XOk sigOf H rd f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt} {st1 : HSt}
    {a : Atom} (h1 : atomH X.toH st.toH a = some st1) (hs : StOk rd W σ st) (ha : a.Holds rd σ) :
    (∀ x, Reads H σ a x → W x) ∧ StOk rd (fun x ↦ W x ∨ Writes σ a x) σ (st.ofH st1) := by
  obtain ⟨hr, he, hsc⟩ := atomH_ok (X := X.toH) (H := H) (rd := rd) hX.R hX.pre hX.pows hpre h1 hs.env hs.sc ha
  have h := hs.mono (W' := fun x ↦ W x ∨ Writes σ a x) fun _ ↦ Or.inl
  exact ⟨hr, he, hsc, h.rs, h.ad, h.sv, h.src, h.pf, h.pr, h.cd, h.eqs, h.dq⟩

theorem addS_fields (st : CSt) (k : ℕ) (a b : CCell) :
    (st.addS k a b).env = st.env ∧ (st.addS k a b).sc = st.sc ∧ (st.addS k a b).rs = st.rs ∧
      (st.addS k a b).sv = st.sv ∧ (st.addS k a b).src = st.src ∧ (st.addS k a b).pf = st.pf ∧
      (st.addS k a b).pr = st.pr ∧ (st.addS k a b).cd = st.cd ∧ (st.addS k a b).eqs = st.eqs ∧
      (st.addS k a b).dq = st.dq := by
  unfold CSt.addS
  cases getF st.ad k <;> simp [Trie.seq_eq]

theorem addS_adOk {σ : Val} {st : CSt} (had : AdOk σ st.ad) {k : ℕ} {a b : CCell}
    (h : σ (V.n k) = a.valW (vw σ) + b.valW (vw σ)) : AdOk σ (st.addS k a b).ad := by
  unfold CSt.addS
  cases hk : getF st.ad k with
  | some _ => exact had
  | none =>
    simp only [Trie.seq_eq]
    intro k' p hp
    rcases Check.getF_setF hp with ⟨rfl, rfl⟩ | hp
    · exact h
    · exact had k' p hp

/-- **An atom of the path**: its reads in `W`, the state after it valid with its writes. -/
theorem atomC0_ok (hX : XOk sigOf H rd f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st st' : CSt} {a : Atom}
    (h : atomC0 X st a = some st') (hs : StOk rd W σ st) (ha : a.Holds rd σ) :
    (∀ x, Reads H σ a x → W x) ∧ StOk rd (fun x ↦ W x ∨ Writes σ a x) σ st' := by
  by_cases hl : ∃ d p off, a = .load d p off
  · obtain ⟨d, p, off, rfl⟩ := hl
    have hrd : rd (cellAt σ p off) = some (σ d) := by simp only [Atom.Holds, LoadHolds] at ha; exact ha.2
    simp only [atomC0] at h
    cases hm : monoOf st.env p with
    | none => rw [hm] at h; cases h
    | some m =>
      simp only [hm, CCell.seq_eq] at h
      have hcell := cellAt_shift σ (monoOf_ok hs.env hm) off
      have hrd' : rd ((m.shift off).addr σ) = some (σ d) := by rw [← hcell]; exact hrd
      have hW : (fun x ↦ W x ∨ Writes σ (.load d p off) x) ((m.shift off).addr σ) :=
        Or.inr (by rw [← hcell]; rfl)
      cases hw : readWitT X.R d p off with
      | none =>
        simp only [hw, Option.some.injEq] at h
        subst h
        refine ⟨fun x hx ↦ ?_, loadPush_ok (gwDef_ok (by rw [hX.sig]; exact hX.gw) hs hrd') (fun _ ↦ Or.inl) hW hrd'⟩
        obtain ⟨hr, -⟩ := hx
        unfold HCert.readWit at hr
        rw [← hX.R, hw] at hr
        cases hr
      | some wt =>
        simp only [hw] at h
        cases hp : ptOkD X st (m.shift off) wt with
        | false => rw [hp] at h; cases h
        | true =>
          simp only [hp, Bool.cond_true, CSt.seq_eq, Option.some.injEq] at h
          subst h
          refine ⟨fun x hx ↦ ?_, loadPush_ok (gwDef_ok (by rw [hX.sig]; exact hX.gw) (hvDef_ok hs hrd' wt) hrd') (fun _ ↦ Or.inl) hW hrd'⟩
          obtain ⟨-, rfl⟩ := hx
          rw [hcell]
          exact ptOkD_ok hX hpre hs hp
  by_cases hd : ∃ d x y, a = .add d x y
  · obtain ⟨d, x, y, rfl⟩ := hd
    refine ⟨fun x hx ↦ by simp [Reads] at hx, ?_⟩
    simp only [atomC0] at h
    cases hk : vnum d with
    | none => simp only [hk, Option.some.injEq] at h; subst h; exact hs.mono fun _ ↦ Or.inl
    | some k =>
      cases hx : monoOf st.env x with
      | none => simp only [hk, hx, Option.some.injEq] at h; subst h; exact hs.mono fun _ ↦ Or.inl
      | some mx =>
        cases hy : monoOf st.env y with
        | none => simp only [hk, hx, hy, Option.some.injEq] at h; subst h; exact hs.mono fun _ ↦ Or.inl
        | some my =>
          simp only [hk, hx, hy, Option.some.injEq] at h
          subst h
          obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩ := addS_fields st k mx my
          have h := hs.mono (W' := fun z ↦ W z ∨ Writes σ (.add d x y) z) fun _ ↦ Or.inl
          refine ⟨e1 ▸ hs.env, e2 ▸ h.sc, e3 ▸ h.rs, addS_adOk hs.ad ?_, e4 ▸ hs.sv, e5 ▸ hs.src, e6 ▸ h.pf,
            e7 ▸ h.pr, e8 ▸ h.cd, e9 ▸ h.eqs, e10 ▸ h.dq⟩
          rw [← vnum_eq hk, show σ d = σ x + σ y from ha, ← val_eq, ← val_eq, ← monoOf_ok hs.env hx,
              ← monoOf_ok hs.env hy]
  by_cases hmu : ∃ d x y, a = .mul d x y
  · obtain ⟨d, x, y, rfl⟩ := hmu
    have hxy : σ d = σ x * σ y := ha
    simp only [atomC0] at h
    cases h1 : divOf X st d x y with
    | some p =>
      obtain ⟨k, c⟩ := p
      rw [h1, Option.some.injEq] at h
      subst h
      refine ⟨fun x hx ↦ by simp [Reads] at hx, (def_stOk hs ?_).mono fun _ ↦ Or.inl⟩
      exact divOf_ok hs hxy h1
    | none =>
      cases h2 : divOf X st d y x with
      | some p =>
        obtain ⟨k, c⟩ := p
        rw [h1, h2, Option.some.injEq] at h
        subst h
        refine ⟨fun x hx ↦ by simp [Reads] at hx, (def_stOk hs ?_).mono fun _ ↦ Or.inl⟩
        exact divOf_ok hs (by rw [hxy, mul_comm]) h2
      | none =>
        rw [h1, h2] at h
        cases h3 : atomH X.toH st.toH (.mul d x y) with
        | none => rw [h3] at h; cases h
        | some st1 =>
          rw [h3, Option.map_some, Option.some.injEq] at h
          subst h
          exact atomH_part hX hpre h3 hs ha
  by_cases hlg : ∃ p off len nb fl dst, a = .hint (.log2Ceil (.heap p off len) nb fl dst)
  · obtain ⟨p, off, len, nb, fl, dst, rfl⟩ := hlg
    simp only [atomC0] at h
    cases hm : monoOf st.env p with
    | none => rw [hm] at h; cases h
    | some m =>
      rw [hm] at h
      dsimp only at h
      cases hb : bitsOk X st m dst p off 0 (min nb len) with
      | false => rw [hb] at h; cases h
      | true =>
        rw [hb, Bool.cond_true, Option.some.injEq] at h
        subst h
        refine ⟨fun x hx ↦ ?_, hs.mono fun _ ↦ Or.inl⟩
        obtain ⟨k, hk, rfl⟩ := hx
        rw [cellAt_shift σ (monoOf_ok hs.env hm)]
        exact bitsOk_ok hX hpre hs hb k (Nat.zero_le _) (by omega)
  · simp only [not_exists] at hl hd hmu hlg
    rw [atomC_other hl hd hmu hlg] at h
    cases h1 : atomH X.toH st.toH a with
    | none => rw [h1] at h; cases h
    | some st1 =>
      rw [h1, Option.map_some, Option.some.injEq] at h
      subst h
      exact atomH_part hX hpre h1 hs ha

theorem addEq_ok {st : CSt} (hs : StOk rd W σ st) {p : CCell × CCell} (hp : p.1.valW (vw σ) = p.2.valW (vw σ)) :
    StOk rd W σ (st.addEq p) :=
  ⟨hs.env, hs.sc, hs.rs, hs.ad, hs.sv, hs.src, hs.pf, hs.pr, hs.cd,
    fun q hq ↦ (List.mem_cons.mp hq).elim (fun h ↦ h ▸ hp) (hs.eqs q), hs.dq⟩

theorem addEqs_ok {st : CSt} (hs : StOk rd W σ st) {l : List (CCell × CCell)}
    (hl : ∀ p ∈ l, p.1.valW (vw σ) = p.2.valW (vw σ)) : StOk rd W σ (st.addEqs l) :=
  ⟨hs.env, hs.sc, hs.rs, hs.ad, hs.sv, hs.src, hs.pf, hs.pr, hs.cd,
    fun q hq ↦ (List.mem_append.mp hq).elim (hl q) (hs.eqs q), hs.dq⟩

theorem eqPair_ok {st : CSt} (hs : StOk rd W σ st) {a b : V} (hab : σ a = σ b) : StOk rd W σ (eqPair X st a b) := by
  unfold eqPair
  cases hk : vnum a with
  | none => exact hs
  | some k =>
    dsimp only
    cases h1 : getF X.eqk k with
    | none => exact hs
    | some _ =>
      cases h2 : monoOf st.env a with
      | none => exact hs
      | some ma =>
        cases h3 : monoOf st.env b with
        | none => exact hs
        | some mb =>
          refine addEq_ok hs ?_
          rw [← val_eq, ← val_eq, ← monoOf_ok hs.env h2, ← monoOf_ok hs.env h3, hab]

/-- **An atom's equation kept** holds. -/
theorem eqAt_ok {st : CSt} (hs : StOk rd W σ st) {a : Atom} (ha : a.Holds rd σ) : StOk rd W σ (eqAt X st a) := by
  cases a with
  | mul d x y =>
    have hxy : σ d = σ x * σ y := ha
    cases hk : vnum d with
    | none => simp only [eqAt, hk]; exact hs
    | some k =>
      cases h1 : getF X.eqk k with
      | none => simp only [eqAt, hk, h1]; exact hs
      | some _ =>
        cases h2 : getF st.env k with
        | none => simp only [eqAt, hk, h1, h2]; exact hs
        | some md =>
          cases h3 : monoOf st.env x with
          | none => simp only [eqAt, hk, h1, h2, h3]; exact hs
          | some mx =>
            cases h4 : monoOf st.env y with
            | none => simp only [eqAt, hk, h1, h2, h3, h4]; exact hs
            | some my =>
              simp only [eqAt, hk, h1, h2, h3, h4]
              refine addEq_ok hs ?_
              rw [valW_mul, ← val_eq, ← val_eq, ← val_eq, ← monoOf_ok hs.env h3, ← monoOf_ok hs.env h4,
                ← hs.env k md h2, ← vnum_eq hk, hxy]
  | assertEq x y => exact eqPair_ok hs (CoreMode.char2_eq (show σ x + σ y = 0 from ha))
  | copy d s => exact eqPair_ok hs (show σ d = σ s from ha)
  | _ => exact hs

/-- **An atom**: its reads written; the state after it valid with its writes. -/
theorem atomC_ok (hX : XOk sigOf H rd f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st st' : CSt} {a : Atom}
    (h : atomC X st a = some st') (hs : StOk rd W σ st) (ha : a.Holds rd σ) :
    (∀ x, Reads H σ a x → W x) ∧ StOk rd (fun x ↦ W x ∨ Writes σ a x) σ st' := by
  unfold atomC at h
  rw [CSt.seq_eq] at h
  have hs0 := eqAt_ok (X := X) hs ha
  generalize eqAt X st a = st0 at h hs0
  cases hl : longRun st0 a with
  | none =>
    rw [hl] at h
    exact atomC0_ok hX hpre h hs0 ha
  | some r =>
    rw [hl, Option.some.injEq] at h
    subst h
    cases a with
    | hint hh =>
      cases hd : hintHeap hh with
      | none => simp [longRun, hd] at hl
      | some t =>
        obtain ⟨p, off, len⟩ := t
        cases hb : Nat.ble 2048 len with
        | false => simp [longRun, hd, hb] at hl
        | true =>
          simp only [longRun, hd, hb, Bool.cond_true] at hl
          obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.mp hl
          refine ⟨fun x hx ↦ ?_, pushR_stOk (hs0.mono fun _ ↦ Or.inl) (fun _ h ↦ h) ?_⟩
          · cases hh <;> simp_all [hintHeap, Reads]
          rintro x ⟨ylo, yhi, j, h1, h2, h3, h4, rfl⟩
          have hj : j < len := by
            obtain ⟨hyc, -⟩ := rep_spec h2
            rcases Nat.lt_or_ge len capE with hl | hl
            · rw [rep_const hl, Option.some.injEq] at h2
              omega
            · omega
          refine Or.inr ⟨p, off, len, hd, j, hj, ?_⟩
          rw [valW_shift, one_mul, mul_assoc, ← ofK_mul, addressOfIndex, addressOfIndex, ← pow_add, ← val_eq,
            ← monoOf_ok hs0.env hm, cellAt, limb0_mul_ofK, addressOfIndex]
    | _ => simp [longRun] at hl

theorem instPP_ok {ms : List CCell} : ∀ {ps l : List (CCell × List ℕ)}, instPP ms ps = some l →
    ∀ p ∈ l, ∃ p0 ∈ ps, instC ms p0.1 = some p.1 ∧ p.2 = p0.2
  | [], l, h, p, hp => by simp only [instPP, Option.some.injEq] at h; subst h; simp at hp
  | p0 :: ps, l, h, p, hp => by
    simp only [instPP] at h
    cases h1 : instC ms p0.1 with
    | none => simp [h1] at h
    | some c =>
      cases h2 : instPP ms ps with
      | none => simp [h1, h2] at h
      | some l' =>
        simp only [h1, h2, Option.some.injEq] at h
        subst h
        rcases List.mem_cons.mp hp with rfl | hp
        · exact ⟨p0, List.mem_cons_self, h1, rfl⟩
        · obtain ⟨p1, hp1, e⟩ := instPP_ok h2 p hp
          exact ⟨p1, List.mem_cons_of_mem _ hp1, e⟩

theorem instPRL_ok {ms : List CCell} : ∀ {ps : List (CRun × List ℕ)} {l : List (PRun × List ℕ)},
    instPRL ms ps = some l → ∀ p ∈ l, ∃ p0 ∈ ps, instR ms p0.1 = some p.1 ∧ p.2 = p0.2
  | [], l, h, p, hp => by simp only [instPRL, Option.some.injEq] at h; subst h; simp at hp
  | p0 :: ps, l, h, p, hp => by
    simp only [instPRL] at h
    cases h1 : instR ms p0.1 with
    | none => simp [h1] at h
    | some q =>
      cases h2 : instPRL ms ps with
      | none => simp [h1, h2] at h
      | some l' =>
        simp only [h1, h2, Option.some.injEq] at h
        subst h
        rcases List.mem_cons.mp hp with rfl | hp
        · exact ⟨p0, List.mem_cons_self, h1, rfl⟩
        · obtain ⟨p1, hp1, e⟩ := instPRL_ok h2 p hp
          exact ⟨p1, List.mem_cons_of_mem _ hp1, e⟩

/-- A pointer fact at a site: the cells past the word at the signature's cell. -/
theorem ptrSet_inst {ms : List CCell} {ws : List E} (hms : MsOk (vw σ) ms (slotW ws)) {c c0 : CCell}
    (hi : instC ms c0 = some c) {offs : List ℕ} {x : K} :
    PtrSet rd (c.addr σ) offs x ↔ PtrSet rd (c0.addrW (slotW ws)) offs x := by
  rw [addr_eq, CCell.addrW, CCell.addrW, instC_ok hms hi]

/-- **A callee's guarantees pushed**: the state valid with them written. -/
theorem pushPost_ok {G : HSig} {ms : List CCell} {ws : List E} (hms : MsOk (vw σ) ms (slotW ws)) {st st' : CSt}
    (hs : StOk rd W σ st) (h : pushPost G ms st = some st') :
    StOk rd (fun x ↦ W x ∨ PostSet rd G ws x) σ st' := by
  unfold pushPost at h
  cases h1 : instAll ms G.post with
  | none => simp [h1] at h
  | some ps =>
    cases h2 : instPP ms G.postP with
    | none => simp [h1, h2] at h
    | some pps =>
      cases h3 : instAllR ms G.postR with
      | none => simp [h1, h2, h3] at h
      | some rs =>
        cases h4 : instPRL ms G.postPR with
        | none => simp [h1, h2, h3, h4] at h
        | some prs =>
          simp only [h1, h2, h3, h4, Option.some.injEq] at h
          subst h
          refine pushPRL_ok (pushRL_ok (pushPL_ok (pushL_ok hs (fun _ ↦ Or.inl) fun c hc ↦ ?_) (fun _ h ↦ h)
            fun p hp x hx ↦ ?_) (fun _ h ↦ h) fun q hq ↦ ?_) (fun _ h ↦ h) fun p hp a ha x hx ↦ ?_
          · obtain ⟨c0, hc0, hi⟩ := instAll_ok h1 c hc
            refine Or.inr (Or.inl (Or.inl ⟨c0, hc0, ?_⟩))
            rw [addr_eq, CCell.addrW, CCell.addrW, instC_ok hms hi]
          · obtain ⟨p0, hp0, hi, he⟩ := instPP_ok h2 p hp
            refine Or.inr (Or.inr (Or.inl (Or.inl ⟨p0, hp0, ?_⟩)))
            rw [← he]
            exact (ptrSet_inst hms hi).mp hx
          · obtain ⟨r0, hr0, hi⟩ := instAllR_ok h3 q hq
            exact fun x hx ↦ Or.inr (Or.inl (Or.inr ⟨r0, hr0, (instR_set hms hi).mp hx⟩))
          · obtain ⟨p0, hp0, hi, he⟩ := instPRL_ok h4 p hp
            refine Or.inr (Or.inr (Or.inl (Or.inr ⟨p0, hp0, a, (instR_set hms hi).mp ha, ?_⟩)))
            rw [← he]
            exact hx

theorem pfBeq_eq {p q : CCell × List ℕ} (h : pfBeq p q = true) : p = q := by
  unfold pfBeq at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact Prod.ext (CCell.beq_eq h.1) h.2

theorem prBeq_eq {p q : PRun × List ℕ} (h : prBeq p q = true) : p = q := by
  unfold prBeq at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact Prod.ext (PRun.beq_eq h.1) h.2

theorem instArmsP_mem {sigOf : String → HSig} {ms : List CCell} : ∀ {gs : List String}
    {ps : List (List (CCell × List ℕ))} {rs : List (List (PRun × List ℕ))}, instArmsP sigOf ms gs = some (ps, rs) →
    ∀ g ∈ gs, ∃ p ∈ ps, ∃ r ∈ rs, instPP ms (sigOf g).postP = some p ∧ instPRL ms (sigOf g).postPR = some r
  | [], ps, rs, _, g, hg => by simp at hg
  | g :: gs, ps, rs, h, g0, hg0 => by
    simp only [instArmsP] at h
    cases h1 : instPP ms (sigOf g).postP with
    | none => simp [h1] at h
    | some p =>
      cases h2 : instPRL ms (sigOf g).postPR with
      | none => simp [h1, h2] at h
      | some r =>
        cases h3 : instArmsP sigOf ms gs with
        | none => simp [h1, h2, h3] at h
        | some pr =>
          obtain ⟨ps', rs'⟩ := pr
          simp only [h1, h2, h3, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rcases List.mem_cons.mp hg0 with rfl | hg0
          · exact ⟨p, List.mem_cons_self, r, List.mem_cons_self, h1, h2⟩
          · obtain ⟨p', hp', r', hr', e1, e2⟩ := instArmsP_mem h3 g0 hg0
            exact ⟨p', List.mem_cons_of_mem _ hp', r', List.mem_cons_of_mem _ hr', e1, e2⟩

/-- **The pointer guarantees every arm gives, pushed**: those of the taken arm. -/
theorem pushPtrM_ok {G : String → HSig} {ms : List CCell} {ws : List E} (hms : MsOk (vw σ) ms (slotW ws))
    {gs : List String} {g : String} (hg : g ∈ gs) {W' : K → Prop} {st : CSt} (hs : StOk rd W' σ st)
    (hW : ∀ x, PostSet rd (G g) ws x → W' x) : StOk rd W' σ (pushPtrM (instArmsP G ms gs) st) := by
  cases hi : instArmsP G ms gs with
  | none => exact hs
  | some pr =>
    obtain ⟨ps, rs⟩ := pr
    cases ps with
    | nil => exact hs
    | cons p ps =>
      cases rs with
      | nil => exact hs
      | cons r rs =>
        obtain ⟨pg, hpg, rg, hrg, e1, e2⟩ := instArmsP_mem hi g hg
        simp only [pushPtrM]
        refine pushPRL_ok (pushPL_ok hs (fun _ h ↦ h) fun q hq x hx ↦ ?_) (fun _ h ↦ h) fun q hq a ha x hx ↦ ?_
        · obtain ⟨hq1, hq2⟩ := List.mem_filter.mp hq
          have hqg : q ∈ pg := by
            rcases List.mem_cons.mp hpg with rfl | hpg
            · exact hq1
            · obtain ⟨q', hq', he⟩ := List.any_eq_true.mp (List.all_eq_true.mp hq2 pg hpg)
              rwa [← pfBeq_eq he]
          obtain ⟨p0, hp0, hi0, he⟩ := instPP_ok e1 q hqg
          refine hW x (Or.inr (Or.inl (Or.inl ⟨p0, hp0, ?_⟩)))
          rw [← he]
          exact (ptrSet_inst hms hi0).mp hx
        · obtain ⟨hq1, hq2⟩ := List.mem_filter.mp hq
          have hqg : q ∈ rg := by
            rcases List.mem_cons.mp hrg with rfl | hrg
            · exact hq1
            · obtain ⟨q', hq', he⟩ := List.any_eq_true.mp (List.all_eq_true.mp hq2 rg hrg)
              rwa [← prBeq_eq he]
          obtain ⟨p0, hp0, hi0, he⟩ := instPRL_ok e2 q hqg
          refine hW x (Or.inr (Or.inl (Or.inr ⟨p0, hp0, a, (instR_set hms hi0).mp ha, ?_⟩)))
          rw [← he]
          exact hx

theorem svPut_ok : ∀ {l : List (ℕ × CCell × CCell)} {st : CSt}, StOk rd W σ st →
    (∀ p ∈ l, rd (p.2.1.addr σ) = some (p.2.2.valW (vw σ))) → StOk rd W σ (svPut l st)
  | [], _, hs, _ => hs
  | p :: l, st, hs, hl => by
    simp only [svPut, Trie.seq_eq]
    refine svPut_ok ⟨hs.env, hs.sc, hs.rs, hs.ad, fun n q hq ↦ ?_, hs.src, hs.pf, hs.pr, hs.cd, hs.eqs, hs.dq⟩
      fun p' hp' ↦ hl p' (List.mem_cons_of_mem _ hp')
    change getF (setF p.2 Exec.indexDepth st.sv p.1) n = some q at hq
    rcases Check.getF_setF hq with ⟨-, rfl⟩ | hq
    · exact hl p List.mem_cons_self
    · exact hs.sv n q hq

/-- A callee's words at return, at a call: in the final memory. -/
theorem postVE_ok {G : HSig} {ms : List CCell} {ws : List E} (hms : MsOk (vw σ) ms (slotW ws)) (hv : RetVOk rd G ws)
    {n0 : ℕ} : ∀ p ∈ postVE G ms n0, rd (p.2.1.addr σ) = some (p.2.2.valW (vw σ)) := by
  intro p hp
  obtain ⟨⟨i, m⟩, him, hq⟩ := List.mem_filterMap.mp hp
  dsimp only at hq
  cases hc : nth G.post i with
  | none => rw [hc] at hq; cases hq
  | some c =>
    rw [hc] at hq
    dsimp only at hq
    cases hc' : instC ms c with
    | none => rw [hc'] at hq; cases hq
    | some c' =>
      cases hm' : instC ms m with
      | none => rw [hc', hm'] at hq; cases hq
      | some m' =>
        rw [hc', hm', Option.some.injEq] at hq
        subst hq
        obtain ⟨c0, hc0, hr⟩ := hv i m him
        rw [← nth_eq, hc, Option.some.injEq] at hc0
        subst hc0
        rw [addr_eq, CCell.addrW, instC_ok hms hc', instC_ok hms hm']
        exact hr

/-- A run at a word, its base's and bounds' words given. -/
theorem runSetB_congr {v v' : ℕ → E} {w : E} {b b' lo lo' hi hi' : CCell} {S : ℕ} (hb : b.valW v = b'.valW v')
    (hl : lo.valW v = lo'.valW v') (hh : hi.valW v = hi'.valW v') {x : K} :
    RunSetB v w b S lo hi x ↔ RunSetB v' w b' S lo' hi' x := by
  simp only [RunSetB, hb, hl, hh]

theorem instQ_mem {ms : List CCell} : ∀ {qs : List (CCell × CRun)} {p : CCell × PRun}, p ∈ instQ ms qs →
    ∃ q ∈ qs, instC ms q.1 = some p.1 ∧ instR ms q.2 = some p.2
  | [], _, h => by simp [instQ] at h
  | (c, q) :: l, p, h => by
    simp only [instQ] at h
    cases hc : instC ms c with
    | none =>
      simp only [hc] at h
      obtain ⟨q', hq', h1, h2⟩ := instQ_mem h
      exact ⟨q', List.mem_cons_of_mem _ hq', h1, h2⟩
    | some c' =>
      cases hq : instR ms q with
      | none =>
        simp only [hc, hq] at h
        obtain ⟨q', hq', h1, h2⟩ := instQ_mem h
        exact ⟨q', List.mem_cons_of_mem _ hq', h1, h2⟩
      | some q' =>
        simp only [hc, hq] at h
        rcases List.mem_cons.mp h with rfl | h
        · exact ⟨(c, q), List.mem_cons_self, hc, hq⟩
        · obtain ⟨q'', hq'', h1, h2⟩ := instQ_mem h
          exact ⟨q'', List.mem_cons_of_mem _ hq'', h1, h2⟩

/-- **A callee's runs at words**, instantiated: written where its `PostSet` is, wherever their cells are in
memory. -/
theorem instQ_ok {G : HSig} {ms : List CCell} {ws : List E} (hms : MsOk (vw σ) ms (slotW ws)) {W' : K → Prop}
    (hW : ∀ x, PostSet rd G ws x → W' x) : DqOk rd W' σ (instQ ms G.postQ) := by
  intro p hp w hw x hx
  obtain ⟨q, hq, h1, h2⟩ := instQ_mem hp
  obtain ⟨e1, e2, e3, e4⟩ := instR_ok hms h2
  refine hW x (Or.inr (Or.inr ⟨q, hq, w, ?_, ?_⟩))
  · rw [addr_eq, CCell.addrW, instC_ok hms h1] at hw
    exact hw
  · rw [← e2]
    exact (runSetB_congr e1 e3 e4).mp hx

theorem addDq_ok {st : CSt} (hs : StOk rd W σ st) {l : List (CCell × PRun)} (hl : DqOk rd W σ l) :
    StOk rd W σ (st.addDq l) :=
  ⟨hs.env, hs.sc, hs.rs, hs.ad, hs.sv, hs.src, hs.pf, hs.pr, hs.cd, hs.eqs,
    fun p hp ↦ (List.mem_append.mp hp).elim (hl p) (hs.dq p)⟩

/-- **A call**: its callee's preconditions written; the state after it valid with its writes. -/
theorem callC_ok (hX : XOk sigOf H rd f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st st' : CSt} {g : String}
    {args rets : List V} (hs : StOk rd W σ st) (h : callC X st g args rets = some st') :
    CallReq sigOf H rd σ W g args ∧
      (EvM sigOf rd σ (.call g args rets) →
        StOk rd (fun x ↦ W x ∨ EvW sigOf rd σ (.call g args rets) x) σ st') := by
  unfold callC at h
  cases ha : monos st.env args with
  | none => simp [ha] at h
  | some ma =>
    cases hc : getF X.C st.nc with
    | none => simp [ha, hc] at h
    | some wl =>
      simp only [ha, hc] at h
      obtain ⟨hma, hla⟩ := monos_ok hs.env args ma ha
      cases hq : reqG X st ma g args wl with
      | none => simp [hq] at h
      | some wl' =>
        have hreq := reqG_ok hX hpre hs hma hla hq
        refine ⟨hreq, fun hM ↦ ?_⟩
        cases wl' with
        | cons _ _ => simp [hq] at h
        | nil =>
          simp only [hq, CSt.seq_eq] at h
          have hs1 := retDefs_ok (rets := rets) hs.nextC (instRM_ok (G := X.sigOf g) hma (by rw [hX.sigOf]; exact hM.1))
          generalize retDefs rets (instRM ma (X.sigOf g).retM) st.nextC = st1 at h hs1
          cases hr : monos st1.env rets with
          | none => simp [hr] at h
          | some mr =>
            simp only [hr] at h
            obtain ⟨hmr, -⟩ := monos_ok hs1.env rets mr hr
            have hm := msOk_append hma hmr (by simpa using hla)
            rw [← List.map_append] at hm
            cases hpp : pushPost (X.sigOf g) (ma ++ mr) st1 with
            | none => rw [hpp] at h; cases h
            | some st2 =>
              rw [hpp, Option.map_some, Option.some.injEq] at h
              subst h
              have := pushPost_ok hm hs1 hpp
              rw [hX.sigOf] at this
              refine addDq_ok (addEqs_ok (svPut_ok this (postVE_ok hm (by rw [hX.sigOf]; exact hM.2.1)))
                fun p hp ↦ ?_) (instQ_ok hm fun x hx ↦ Or.inr (by rw [hX.sigOf] at hx; exact hx))
              obtain ⟨q, hq, hqe⟩ := List.mem_filterMap.mp hp
              cases h1 : instC (ma ++ mr) q.1 with
              | none => simp [h1] at hqe
              | some a =>
                cases h2 : instC (ma ++ mr) q.2 with
                | none => simp [h1, h2] at hqe
                | some b =>
                  simp only [h1, h2, Option.some.injEq] at hqe
                  subst hqe
                  rw [instC_ok hm h1, instC_ok hm h2]
                  rw [hX.sigOf] at hq
                  exact hM.2.2 q hq

/-- An empty run: its bounds one word. -/
theorem runSet_eq {w : ℕ → E} {b lo hi : CCell} {S : ℕ} (h : lo.valW w = hi.valW w) {x : K} :
    ¬ RunSet w b S lo hi x := by
  rintro ⟨ylo, yhi, j, h1, h2, h3, h4, -⟩
  rw [h, h2, Option.some.injEq] at h1
  omega

theorem cond_some {α : Type} {b : Bool} {x : Option α} {y : α} (h : (bif b then x else none) = some y) :
    b = true ∧ x = some y := by
  cases b <;> simp_all

/-- **An `ite`'s zero branch**: the guard `0`, the equation of its sum kept. -/
theorem zeroEq_ok {st : CSt} (hs : StOk rd W σ st) {c : V} (h0 : σ c = 0) : StOk rd W σ (zeroEq st c) := by
  unfold zeroEq
  cases hsum : sumOf st c with
  | none => exact hs
  | some p =>
    refine addEq_ok hs (CoreMode.char2_eq ?_)
    unfold sumOf at hsum
    cases hk : vnum c with
    | none => rw [hk] at hsum; cases hsum
    | some k =>
      rw [hk] at hsum
      rw [← hs.ad k p hsum, ← vnum_eq hk]
      exact h0

theorem keepL_mem {X : CX} {st : CSt} {qs : List PRun} : ∀ {n : ℕ} {wl : List Wit} {ks : List PRun},
    keepL X st qs n wl = some ks → ∀ q ∈ ks, q ∈ qs
  | _, [], ks, h, q, hq => by simp only [keepL, Option.some.injEq] at h; subst h; simp at hq
  | 0, _ :: _, ks, h, q, hq => by simp [keepL] at h
  | n + 1, w :: wl, ks, h, q, hq => by
    cases w with
    | keep j b lo hi =>
      simp only [keepL] at h
      cases hn : nth qs j with
      | none => simp [hn] at h
      | some q0 =>
        simp only [hn] at h
        obtain ⟨-, h⟩ := cond_some h
        split at h
        · rename_i wl1 _
          obtain ⟨ks1, hk1, rfl⟩ := Option.map_eq_some_iff.mp h
          rcases List.mem_cons.mp hq with rfl | hq
          · rw [nth_eq] at hn
            exact List.mem_of_getElem? hn
          · exact keepL_mem hk1 q hq
        · cases h
    | _ => simp [keepL] at h

theorem keepL_ok (hX : XOk sigOf H rd f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt}
    (hs : StOk rd W σ st) {qs : List PRun} : ∀ {n : ℕ} {wl : List Wit} {ks : List PRun},
    keepL X st qs n wl = some ks → ∀ q ∈ ks, RunF W (vw σ) q.base q.stride q.lo q.hi
  | _, [], ks, h, q, hq => by simp only [keepL, Option.some.injEq] at h; subst h; simp at hq
  | 0, _ :: _, ks, h, q, hq => by simp [keepL] at h
  | n + 1, w :: wl, ks, h, q, hq => by
    cases w with
    | keep j b lo hi =>
      simp only [keepL] at h
      cases hn : nth qs j with
      | none => simp [hn] at h
      | some q0 =>
        simp only [hn] at h
        obtain ⟨he, h⟩ := cond_some h
        simp only [Bool.and_eq_true] at he
        obtain ⟨⟨hb, hl⟩, hh⟩ := he
        cases hr : runOk X st ⟨b, q0.stride, lo, hi⟩ wl with
        | none => simp [hr] at h
        | some wl1 =>
          simp only [hr] at h
          obtain ⟨ks1, hk1, rfl⟩ := Option.map_eq_some_iff.mp h
          rcases List.mem_cons.mp hq with rfl | hq
          · have h1 := runOk_ok (Q := ⟨b, q.stride, lo, hi⟩) hX hpre hs hr
            exact (runF_congr (eqVM_ok hs.eqs hb).symm (eqVM_ok hs.eqs hl).symm (eqVM_ok hs.eqs hh).symm).mp h1
          · exact keepL_ok hX hpre hs hk1 q hq
    | _ => simp [keepL] at h

/-- **A conditional call** `callIf c g args`: its callee's preconditions written; the state after it valid
with its events' writes (`e`, entered or not). -/
theorem callIfC_ok (hX : XOk sigOf H rd f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st st' : CSt} {c : V}
    {g : String} {args : List V} (hs : StOk rd W σ st) (h : callIfC X st c g args = some st') :
    (σ c ≠ 0 → CallReq sigOf H rd σ W g args) ∧
      StOk rd (fun x ↦ W x ∨ EW sigOf rd σ [.inK c, if σ c = 0 then .skip g args else .call g args []] x) σ st' := by
  unfold callIfC at h
  cases ha : monos st.env args with
  | none => simp [ha] at h
  | some ma =>
    cases hc : getF X.C st.nc with
    | none => simp [ha, hc] at h
    | some wl =>
      simp only [ha, hc] at h
      obtain ⟨hma, hla⟩ := monos_ok hs.env args ma ha
      cases hq : reqG (X.ext (cnz c)) st ma g args wl with
      | none => simp [hq] at h
      | some wl' =>
        have hreq := fun h0 ↦ reqG_ok (hX.ext (cnz_ok h0)) hpre hs hma hla hq
        refine ⟨hreq, ?_⟩
        simp only [hq] at h
        -- the guard is the sum of a run's bounds whose bounds are its operands
        have hcs : ∀ p, sumOf st c = some p → ∀ q : PRun, boundsOf p q = true →
            σ c = q.lo.valW (vw σ) + q.hi.valW (vw σ) := fun p hsum q hq2 ↦ by
          unfold sumOf at hsum
          cases hk : vnum c with
          | none => rw [hk] at hsum; cases hsum
          | some k =>
            rw [hk] at hsum
            rw [vnum_eq hk, hs.ad k p hsum]
            unfold boundsOf at hq2
            simp only [Bool.or_eq_true, Bool.and_eq_true] at hq2
            rcases hq2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · rw [CCell.beq_eq h1, CCell.beq_eq h2]
            · rw [CCell.beq_eq h1, CCell.beq_eq h2, add_comm]
        have hcall : σ c ≠ 0 → ∀ x, PostSet rd (sigOf g) (args.map σ) x →
            EW sigOf rd σ [.inK c, if σ c = 0 then .skip g args else .call g args []] x := fun h0 x hx ↦ by
          refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
          rw [ite_eq_right h0]
          simp only [EvW, List.append_nil]
          exact hx
        cases hsum : sumOf st c with
        | none =>
          simp only [hsum] at h
          obtain ⟨-, h⟩ := cond_some h
          simp only [Option.some.injEq] at h; subst h; exact hs.nextC.mono fun _ ↦ Or.inl
        | some p =>
          cases hqs : instAllR ma (X.sigOf g).postR with
          | none =>
            simp only [hsum, hqs] at h
            obtain ⟨-, h⟩ := cond_some h
            simp only [Option.some.injEq] at h; subst h; exact hs.nextC.mono fun _ ↦ Or.inl
          | some qs =>
            cases hps : instPRL ma (X.sigOf g).postPR with
            | none =>
              simp only [hsum, hqs, hps] at h
              obtain ⟨-, h⟩ := cond_some h
              simp only [Option.some.injEq] at h; subst h; exact hs.nextC.mono fun _ ↦ Or.inl
            | some prs =>
            simp only [hsum, hqs, hps] at h
            cases hk : keepL (X.ext (czero c)) (zeroEq st c) qs wl'.length wl' with
            | none => simp [hk] at h
            | some ks =>
            simp only [hk, Option.some.injEq] at h
            subst h
            refine pushPRL_ok (pushRL_ok hs.nextC (fun _ ↦ Or.inl) (fun q hq x hx ↦ ?_)) (fun _ h ↦ h)
              fun q hq a ha x hx ↦ ?_
            · rcases List.mem_append.mp hq with hq | hq
              swap
              · by_cases h0 : σ c = 0
                · exact Or.inl (keepL_ok (hX.ext (czero_ok h0)) hpre (zeroEq_ok hs h0) hk q hq x hx)
                · obtain ⟨r0, hr0, hi⟩ := instAllR_ok hqs q (keepL_mem hk q hq)
                  rw [hX.sigOf] at hr0
                  exact Or.inr (hcall h0 x (Or.inl (Or.inr ⟨r0, hr0, (instR_set hma hi).mp hx⟩)))
              obtain ⟨hq1, hq2⟩ := List.mem_filter.mp hq
              by_cases h0 : σ c = 0
              · exact absurd hx (runSet_eq (CoreMode.char2_eq (hcs p hsum q hq2 ▸ h0)))
              · obtain ⟨r0, hr0, hi⟩ := instAllR_ok hqs q hq1
                rw [hX.sigOf] at hr0
                exact Or.inr (hcall h0 x (Or.inl (Or.inr ⟨r0, hr0, (instR_set hma hi).mp hx⟩)))
            · obtain ⟨hq1, hq2⟩ := List.mem_filter.mp hq
              by_cases h0 : σ c = 0
              · exact absurd ha (runSet_eq (CoreMode.char2_eq (hcs p hsum q.1 hq2 ▸ h0)))
              · obtain ⟨p0, hp0, hi, he⟩ := instPRL_ok hps q hq1
                rw [hX.sigOf] at hp0
                refine Or.inr (hcall h0 x (Or.inr (Or.inl (Or.inr ⟨p0, hp0, a, (instR_set hma hi).mp ha, ?_⟩))))
                rw [← he]
                exact hx

theorem instArms_mem {sigOf : String → HSig} {ms : List CCell} : ∀ {gs : List String}
    {ps : List (List CCell)} {rs : List (List PRun)}, instArms sigOf ms gs = some (ps, rs) →
    ∀ g ∈ gs, ∃ p ∈ ps, ∃ r ∈ rs, instAll ms (sigOf g).post = some p ∧ instAllR ms (sigOf g).postR = some r
  | [], ps, rs, _, g, hg => by simp at hg
  | g :: gs, ps, rs, h, g0, hg0 => by
    simp only [instArms] at h
    cases h1 : instAll ms (sigOf g).post with
    | none => simp [h1] at h
    | some p =>
      cases h2 : instAllR ms (sigOf g).postR with
      | none => simp [h1, h2] at h
      | some r =>
        cases h3 : instArms sigOf ms gs with
        | none => simp [h1, h2, h3] at h
        | some pr =>
          obtain ⟨ps', rs'⟩ := pr
          simp only [h1, h2, h3, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rcases List.mem_cons.mp hg0 with rfl | hg0
          · exact ⟨p, List.mem_cons_self, r, List.mem_cons_self, h1, h2⟩
          · obtain ⟨p', hp', r', hr', e1, e2⟩ := instArms_mem h3 g0 hg0
            exact ⟨p', List.mem_cons_of_mem _ hp', r', List.mem_cons_of_mem _ hr', e1, e2⟩

/-- A callee's guarantees at a site, instantiated: written where its `PostSet` is. -/
theorem postE_ok {G : HSig} {ms : List CCell} {ws : List E} (hms : MsOk (vw σ) ms (slotW ws)) {cs : List CCell}
    {rs : List PRun} {ps : List (CCell × List ℕ)} {prs : List (PRun × List ℕ)} (h1 : instAll ms G.post = some cs)
    (h2 : instAllR ms G.postR = some rs) (h3 : instPP ms G.postP = some ps) (h4 : instPRL ms G.postPR = some prs)
    {W' : K → Prop} (hW : ∀ x, PostSet rd G ws x → W' x) :
    CdAOk rd W' σ ⟨cs, rs, ps, prs⟩ := by
  refine ⟨fun c hc ↦ ?_, fun q hq x hx ↦ ?_, fun p hp x hx ↦ ?_, fun p hp a ha x hx ↦ ?_⟩
  · obtain ⟨c0, hc0, hi⟩ := instAll_ok h1 c hc
    refine hW _ (Or.inl (Or.inl ⟨c0, hc0, ?_⟩))
    rw [addr_eq, CCell.addrW, CCell.addrW, instC_ok hms hi]
  · obtain ⟨r0, hr0, hi⟩ := instAllR_ok h2 q hq
    exact hW x (Or.inl (Or.inr ⟨r0, hr0, (instR_set hms hi).mp hx⟩))
  · obtain ⟨p0, hp0, hi, he⟩ := instPP_ok h3 p hp
    refine hW x (Or.inr (Or.inl (Or.inl ⟨p0, hp0, ?_⟩)))
    rw [← he]
    exact (ptrSet_inst hms hi).mp hx
  · obtain ⟨p0, hp0, hi, he⟩ := instPRL_ok h4 p hp
    refine hW x (Or.inr (Or.inl (Or.inr ⟨p0, hp0, a, (instR_set hms hi).mp ha, ?_⟩)))
    rw [← he]
    exact hx

theorem condE_nth {sigOf : String → HSig} {ms : List CCell} : ∀ {gs : List String} {k : ℕ} {a : CdA},
    nth (condE sigOf ms gs) k = some a → ∃ hk : k < gs.length, a = ⟨[], [], [], []⟩ ∨
      (instAll ms (sigOf gs[k]).post = some a.cs ∧ instAllR ms (sigOf gs[k]).postR = some a.rs ∧
      instPP ms (sigOf gs[k]).postP = some a.ps ∧ instPRL ms (sigOf gs[k]).postPR = some a.prs)
  | [], _, _, he => by simp [condE, nth] at he
  | g :: gs, 0, a, he => by
    simp only [condE, nth, Option.some.injEq] at he
    refine ⟨by simp, ?_⟩
    split at he
    · rename_i cs rs ps prs h1 h2 h3 h4
      subst he
      exact Or.inr ⟨h1, h2, h3, h4⟩
    · exact Or.inl he.symm
  | g :: gs, k + 1, a, he => by
    simp only [condE, nth] at he
    obtain ⟨hk, h⟩ := condE_nth he
    exact ⟨by simpa using hk, by simpa using h⟩

theorem addCd_ok {st : CSt} (hs : StOk rd W σ st) {l : List CdE} (hl : CdOk rd W σ l) : StOk rd W σ (st.addCd l) :=
  ⟨hs.env, hs.sc, hs.rs, hs.ad, hs.sv, hs.src, hs.pf, hs.pr, fun e he ↦ (List.mem_append.mp he).elim (fun h ↦ hs.cd e (List.mem_filter.mp h).1) (hl e), hs.eqs, hs.dq⟩

/-- **A dispatch's returned pointers hold** in `W'`: each returned word `j`'s cells at the offsets. -/
def VpOk (W' : K → Prop) (σ : Val) (rets : List V) (vps : List (ℕ × List ℕ)) : Prop :=
  ∀ j offs, (j, offs) ∈ vps → ∀ o ∈ offs, ∃ r, rets[j]? = some r ∧ W' ((σ r * ofK (addressOfIndex o)).limb 0)

theorem vpPts_ok (hX : XOk sigOf H rd f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt} (hs : StOk rd W σ st)
    {mr : List CCell} {rets : List V} (hmr : MsOk (vw σ) mr (slotW (rets.map σ))) (hl : mr.length = rets.length) :
    ∀ {vps : List (ℕ × List ℕ)} {wl wl' : List Wit}, vpPts X st mr vps wl = some wl' → VpOk W σ rets vps
  | [], _, _, _ => fun j offs h ↦ by simp at h
  | (j, offs) :: l, wl, wl', h => by
    simp only [vpPts] at h
    cases hm : nth mr j with
    | none => rw [hm] at h; cases h
    | some m =>
      rw [hm] at h
      dsimp only at h
      cases hp : ptsW X st m offs wl with
      | none => rw [hp] at h; cases h
      | some ws' =>
        rw [hp] at h
        intro j' offs' hj o ho
        rcases List.mem_cons.mp hj with he | hj
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
          have hm' := hm
          rw [nth_eq] at hm'
          obtain ⟨hjl, -⟩ := List.getElem?_eq_some_iff.mp hm'
          rw [hl] at hjl
          have hr : rets[j']? = some rets[j'] := List.getElem?_eq_getElem hjl
          refine ⟨rets[j'], hr, ?_⟩
          have := ptsW_ok hX hpre hs hp o ho
          rwa [addr_eq, CCell.addrW, valW_shift, hmr j' m hm, slotW_map_of hr] at this
        · exact vpPts_ok hX hpre hs hmr hl h j' offs' hj o ho

/-- **An arm's returned pointers**: written by the caller's events or the arm's call, where the arm's
callee names its returned words (`RetMOk`). -/
theorem vpArm_ok (hX : XOk sigOf H rd f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt} (hs : StOk rd W σ st)
    {ma : List CCell} {args : List V} (hma : MsOk (vw σ) ma (slotW (args.map σ))) (hla : ma.length = args.length)
    {g : String} {rets : List V} {vps : List (ℕ × List ℕ)} {wl wl' : List Wit}
    (h : vpArm X st ma g rets vps wl = some wl') (hM : RetMOk (sigOf g) (args.map σ) (rets.map σ)) :
    VpOk (fun y ↦ W y ∨ EvW sigOf rd σ (.call g args rets) y) σ rets vps := by
  cases vps with
  | nil => intro j offs h; simp at h
  | cons p vps =>
    unfold vpArm at h
    dsimp only at h
    cases hr : monos st.env rets with
    | none => rw [hr] at h; cases h
    | some mr0 =>
      rw [hr] at h
      dsimp only at h
      obtain ⟨hmr0, hl0⟩ := monos_ok hs.env rets mr0 hr
      rw [hX.sigOf] at h
      obtain ⟨hmr, hlr⟩ := msOk_setRM hmr0 (by simpa using hl0) (l := instRM ma (sigOf g).retM)
        fun k m hkm hk ↦ by
          have hk2 : k < rets.length := by simpa using hk
          have hk' : rets[k]? = some rets[k] := List.getElem?_eq_getElem hk2
          rw [slotW_map_of hk']
          exact (instRM_ok hma hM k m hkm _ hk').symm
      have hm := msOk_append hma hmr (by simpa using hla)
      rw [← List.map_append] at hm
      cases hpp : pushPost (sigOf g) (ma ++ setRM mr0 (instRM ma (sigOf g).retM)) st with
      | none => rw [hpp] at h; cases h
      | some S =>
        rw [hpp] at h
        dsimp only at h
        exact vpPts_ok (hX := hX) (hpre := fun c hc ↦ Or.inl (hpre c hc)) (pushPost_ok hm hs hpp) hmr
          (by simpa using hlr) h

/-- **A dispatch arm `j`'s blocks hold** in `W'`: each run `abArmR j e` written. -/
def AbOk (W' : K → Prop) (σ : Val) (j : ℕ) (abs : List AbE) : Prop :=
  ∀ e ∈ abs, RunF W' (vw σ) (abArmR j e).base (abArmR j e).stride (abArmR j e).lo (abArmR j e).hi

/-- A block's base or bound after the dispatch: at the taken arm `i`, arm `i`'s. -/
theorem abBase_valW {w : ℕ → E} {mx : CCell} {i : ℕ} (hmi : mx.valW w = ofK (addressOfIndex i)) (c : CCell) (a : ℕ) :
    (c.shift (a * i)).valW w = (abBase mx c a).valW w := by
  rw [valW_shift]
  unfold abBase
  cases ha : Nat.beq a 0 with
  | true =>
    obtain rfl := Nat.eq_of_beq_eq_true ha
    rw [Bool.cond_true, Nat.zero_mul, addressOfIndex, pow_zero, show ofK (1 : K) = 1 from map_one (algebraMap K E),
      mul_one]
  | false =>
    rw [Bool.cond_false, valW_mul, valW_pow, hmi, ← ofK_pow, addressOfIndex, addressOfIndex, ← pow_mul,
      Nat.mul_comm a i]

theorem abRuns_ok (hX : XOk sigOf H rd f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt}
    (hs : StOk rd W σ st) {j : ℕ} : ∀ {abs : List AbE} {wl wl' : List Wit},
      abRuns X st j abs wl = some wl' → AbOk W σ j abs
  | [], _, _, _ => fun p hp ↦ by simp at hp
  | e :: l, wl, wl', h => by
    simp only [abRuns] at h
    cases hr : runOk X st (abArmR j e) wl with
    | none => rw [hr] at h; cases h
    | some ws' =>
      rw [hr] at h
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · have R := runOk_ok hX hpre hs hr
        exact R
      · exact abRuns_ok hX hpre hs h p hp

/-- **An arm's blocks**: written by the caller's events or the arm's call. -/
theorem abArm_ok (hX : XOk sigOf H rd f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt} (hs : StOk rd W σ st)
    {ma : List CCell} {args : List V} (hma : MsOk (vw σ) ma (slotW (args.map σ))) (hla : ma.length = args.length)
    {g : String} {rets : List V} {j : ℕ} {abs : List AbE} {wl wl' : List Wit}
    (h : abArm X st ma g rets j abs wl = some wl') (hM : RetMOk (sigOf g) (args.map σ) (rets.map σ)) :
    AbOk (fun y ↦ W y ∨ EvW sigOf rd σ (.call g args rets) y) σ j abs := by
  cases abs with
  | nil => intro p hp; simp at hp
  | cons p abs =>
    unfold abArm at h
    dsimp only at h
    cases hr : monos st.env rets with
    | none => rw [hr] at h; cases h
    | some mr0 =>
      rw [hr] at h
      dsimp only at h
      obtain ⟨hmr0, hl0⟩ := monos_ok hs.env rets mr0 hr
      rw [hX.sigOf] at h
      obtain ⟨hmr, hlr⟩ := msOk_setRM hmr0 (by simpa using hl0) (l := instRM ma (sigOf g).retM)
        fun k m hkm hk ↦ by
          have hk2 : k < rets.length := by simpa using hk
          have hk' : rets[k]? = some rets[k] := List.getElem?_eq_getElem hk2
          rw [slotW_map_of hk']
          exact (instRM_ok hma hM k m hkm _ hk').symm
      have hm := msOk_append hma hmr (by simpa using hla)
      rw [← List.map_append] at hm
      cases hpp : pushPost (sigOf g) (ma ++ setRM mr0 (instRM ma (sigOf g).retM)) st with
      | none => rw [hpp] at h; cases h
      | some S =>
        rw [hpp] at h
        dsimp only at h
        exact abRuns_ok (hX := hX) (hpre := fun c hc ↦ Or.inl (hpre c hc)) (pushPost_ok hm hs hpp) h

theorem reqArmsX_ok (hX : XOk sigOf H rd f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt}
    (hs : StOk rd W σ st) {ms : List CCell} {args : List V} (hms : MsOk (vw σ) ms (slotW (args.map σ)))
    (hla : ms.length = args.length) {x : V} {mx : CCell} (hmx : mx.valW (vw σ) = σ x)
    {rets : List V} {vps : List (ℕ × List ℕ)} {abs : List AbE} :
    ∀ {j : ℕ} {gs : List String} {wl wl' : List Wit} {kept : List String},
      reqArmsX X st ms args rets vps abs x mx j gs wl = some (wl', kept) → ∀ i (hi : i < gs.length),
        σ x = ofK (addressOfIndex (j + i)) →
        gs[i] ∈ kept ∧ CallReq sigOf H rd σ W gs[i] args ∧
          (RetMOk (sigOf gs[i]) (args.map σ) (rets.map σ) →
            VpOk (fun y ↦ W y ∨ EvW sigOf rd σ (.call gs[i] args rets) y) σ rets vps) ∧
          (RetMOk (sigOf gs[i]) (args.map σ) (rets.map σ) →
            AbOk (fun y ↦ W y ∨ EvW sigOf rd σ (.call gs[i] args rets) y) σ (j + i) abs)
  | _, [], _, _, _, _, i, hi, _ => by simp at hi
  | j, g :: gs, wl, wl', kept, h, i, hi, hy => by
    simp only [reqArmsX] at h
    cases hk : armSkip X st mx j wl with
    | some ws' =>
      rw [hk] at h
      cases i with
      | zero => exact absurd (hmx.trans hy) (armSkip_ok hX hs hk)
      | succ i =>
        obtain ⟨m, r, v, a⟩ := reqArmsX_ok hX hpre hs hms hla hmx h i (by simpa using hi)
          (by rw [hy, show j + (i + 1) = j + 1 + i by omega])
        simp only [List.getElem_cons_succ]
        refine ⟨m, r, v, ?_⟩
        rw [show j + (i + 1) = j + 1 + i by omega]
        exact a
    | none =>
      rw [hk] at h
      dsimp only at h
      cases hr : reqG (X.ext (carm x j)) (condSt mx j st.cd st) ms g args wl with
      | none => rw [hr] at h; cases h
      | some ws' =>
        rw [hr] at h
        dsimp only at h
        cases hv : vpArm (X.ext (carm x j)) (condSt mx j st.cd st) ms g rets vps ws' with
        | none => rw [hv] at h; cases h
        | some ws'' =>
        rw [hv] at h
        dsimp only at h
        cases ha : abArm (X.ext (carm x j)) (condSt mx j st.cd st) ms g rets j abs ws'' with
        | none => rw [ha] at h; cases h
        | some ws3 =>
        rw [ha] at h
        dsimp only at h
        cases h2 : reqArmsX X st ms args rets vps abs x mx (j + 1) gs ws3 with
        | none => rw [h2] at h; cases h
        | some pr =>
          rw [h2] at h
          obtain ⟨wl2, kept2⟩ := pr
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          cases i with
          | zero =>
            have hX' := hX.ext (carm_ok (by rw [hy, Nat.add_zero]))
            have hs' := condSt_ok (by rw [hmx, hy, Nat.add_zero]) hs.cd st.cd (fun _ h ↦ h) hs
            exact ⟨List.mem_cons_self, reqG_ok hX' hpre hs' hms hla hr, fun hM ↦ vpArm_ok hX' hpre hs' hms hla hv hM,
              fun hM ↦ abArm_ok hX' hpre hs' hms hla ha hM⟩
          | succ i =>
            obtain ⟨m, r, v, a⟩ := reqArmsX_ok hX hpre hs hms hla hmx h2 i (by simpa using hi)
              (by rw [hy, show j + (i + 1) = j + 1 + i by omega])
            simp only [List.getElem_cons_succ]
            refine ⟨List.mem_cons_of_mem _ m, r, v, ?_⟩
            rw [show j + (i + 1) = j + 1 + i by omega]
            exact a

/-- **A dispatch**: every arm's preconditions written; the state after it valid with the taken arm's
writes. -/
theorem wordAt_ok {G : HSig} {ms : List CCell} {ws : List E} (hms : MsOk (vw σ) ms (slotW ws))
    (hv : RetVOk rd G ws) {c m : CCell} (h : wordAt G ms c = some m) : rd (c.addr σ) = some (m.valW (vw σ)) := by
  unfold wordAt at h
  split at h
  · rename_i p hf
    have hp := List.mem_of_find?_eq_some hf
    have hb := List.find?_some hf
    obtain ⟨cc, hcc, hrd⟩ := hv p.1 p.2 hp
    rw [← nth_eq] at hcc
    simp only [hcc] at hb
    cases hi : instC ms cc with
    | none => rw [hi] at hb; cases hb
    | some c' =>
      rw [hi] at hb
      rw [addr_eq, CCell.addrW, ← CCell.beq_eq hb, instC_ok hms hi, instC_ok hms h]
      exact hrd
  · cases h

theorem armsV_ok {sigOf : String → HSig} {ms : List CCell} {ws : List E} (hms : MsOk (vw σ) ms (slotW ws))
    {gs : List String} {g : String} (hg : g ∈ gs) (hv : RetVOk rd (sigOf g) ws) {c m : CCell}
    (h : armsV sigOf ms gs c = some m) : rd (c.addr σ) = some (m.valW (vw σ)) := by
  cases gs with
  | nil => cases h
  | cons g0 gs' =>
    simp only [armsV] at h
    cases h0 : wordAt (sigOf g0) ms c with
    | none => rw [h0] at h; cases h
    | some m0 =>
      rw [h0] at h
      dsimp only at h
      have key : ∀ b : Bool, (bif b then some m0 else none) = some m → b = true ∧ m0 = m := by
        intro b hb; cases b <;> simp_all
      obtain ⟨hall, rfl⟩ := key _ h
      rcases List.mem_cons.mp hg with rfl | hg
      · exact wordAt_ok hms hv h0
      · have := List.all_eq_true.mp hall g hg
        cases hw : wordAt (sigOf g) ms c with
        | none => rw [hw] at this; cases this
        | some m' =>
          rw [hw] at this
          dsimp only at this
          rw [← CCell.beq_eq this]
          exact wordAt_ok hms hv hw

theorem meetVL_ok {sigOf : String → HSig} {ms : List CCell} {ws : List E} (hms : MsOk (vw σ) ms (slotW ws))
    {gs : List String} {g : String} (hg : g ∈ gs) (hv : RetVOk rd (sigOf g) ws) :
    ∀ (cs : List CCell) (n : ℕ), ∀ q ∈ meetVL sigOf ms gs cs n, rd (q.2.1.addr σ) = some (q.2.2.valW (vw σ))
  | [], _, q, hq => by simp [meetVL] at hq
  | c :: cs, n, q, hq => by
    unfold meetVL at hq
    cases ha : armsV sigOf ms gs c with
    | none => rw [ha] at hq; exact meetVL_ok hms hg hv cs (n + 1) q hq
    | some m =>
      rw [ha] at hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact armsV_ok hms hg hv ha
      · exact meetVL_ok hms hg hv cs (n + 1) q hq

theorem dispC_ok (hX : XOk sigOf H rd f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st st' : CSt}
    {x : V} {fs : List String} {args rets : List V} (hs : StOk rd W σ st)
    (h : dispC X st x fs args rets = some st') :
    ∀ i (hi : i < fs.length), σ x = ofK (addressOfIndex i) →
      CallReq sigOf H rd σ W fs[i] args ∧
      (EvM sigOf rd σ (.call fs[i] args rets) →
        StOk rd (fun x' ↦ W x' ∨ EvW sigOf rd σ (.call fs[i] args rets) x') σ st') := by
  intro i hi hxi
  unfold dispC at h
  cases ha : monos st.env args with
  | none => simp [ha] at h
  | some ma =>
    cases hmx : monoOf st.env x with
    | none => simp [ha, hmx] at h
    | some mx =>
      cases hc : getF X.C st.nc with
      | none => simp [ha, hmx, hc] at h
      | some wl =>
        simp only [ha, hmx, hc] at h
        obtain ⟨hma, hla⟩ := monos_ok hs.env args ma ha
        cases hq : reqArmsX X st ma args rets (vpHead wl).1 (abHead (vpHead wl).2).1 x mx 0 fs
            (abHead (vpHead wl).2).2 with
        | none => simp [hq] at h
        | some pr =>
          obtain ⟨wl', kept⟩ := pr
          obtain ⟨hgk, hreq, hvp, hab⟩ := reqArmsX_ok hX hpre hs hma hla
            (by rw [← val_eq, ← monoOf_ok hs.env hmx]) hq i hi (by simpa using hxi)
          refine ⟨hreq, fun hM ↦ ?_⟩
          have hmxv : mx.valW (vw σ) = σ x := by rw [← val_eq, ← monoOf_ok hs.env hmx]
          have hvp := hvp hM.1
          have hab := hab hM.1
          generalize hgi : fs[i] = g at hgk hM hvp hab ⊢
          cases wl' with
          | cons _ _ => simp [hq] at h
          | nil =>
            cases kept with
            | nil => simp at hgk
            | cons g0 gs =>
            have hg := hgk
            simp only [hq, CSt.seq_eq] at h
            -- the returned words' monomials every arm gives, the taken arm's among them
            have hs1 := retDefs_ok (rets := rets) (l := (instRM ma (X.sigOf g0).retM).filter
                (meetM (gs.map fun g' ↦ instRM ma (X.sigOf g').retM))) hs.nextC fun k m hkm ↦ by
              obtain ⟨hk1, hk2⟩ := List.mem_filter.mp hkm
              have hg' : (k, m) ∈ instRM ma (X.sigOf g).retM := by
                rcases List.mem_cons.mp hg with rfl | hg
                · exact hk1
                · obtain ⟨q, hq', he⟩ := List.any_eq_true.mp
                    (List.all_eq_true.mp hk2 _ (List.mem_map.mpr ⟨g, hg, rfl⟩))
                  simp only [Bool.and_eq_true] at he
                  obtain ⟨e1, e2⟩ := he
                  obtain ⟨k', m'⟩ := q
                  simp only at e1 e2
                  rwa [Nat.eq_of_beq_eq_true e1, CCell.beq_eq e2] at hq'
              exact instRM_ok (G := X.sigOf g) hma (by rw [hX.sigOf]; exact hM.1) k m hg'
            generalize retDefs rets _ st.nextC = st1 at h hs1
            cases hr : monos st1.env rets with
            | none => simp [hr] at h
            | some mr =>
            simp only [hr] at h
            obtain ⟨hmr, -⟩ := monos_ok hs1.env rets mr hr
            have hmr' := hmr
            have hm := msOk_append hma hmr (by simpa using hla)
            rw [← List.map_append] at hm
            cases hi : instArms X.sigOf (ma ++ mr) (g0 :: gs) with
            | none => simp [hi] at h
            | some pr =>
              obtain ⟨ps, rs⟩ := pr
              cases ps with
              | nil => simp [hi] at h
              | cons p ps =>
                cases rs with
                | nil => simp [hi] at h
                | cons r rs =>
                  simp only [hi, Option.some.injEq] at h
                  subst h
                  obtain ⟨pg, hpg, rg, hrg, e1, e2⟩ := instArms_mem hi g hg
                  rw [hX.sigOf] at e1 e2
                  refine addCd_ok ?_ ?_
                  swap
                  · cases hb : Nat.blt fs.length capE with
                    | false => intro e he; simp at he
                    | true =>
                      intro e he k a ha hj
                      rw [Bool.cond_true, List.mem_singleton] at he
                      subst he
                      obtain ⟨hk, ha'⟩ := condE_nth ha
                      have hlt := Nat.blt_eq.mp hb
                      rw [capE_eq] at hlt
                      have hki : k = i := gpow_inj_lt (by omega) (by omega)
                        (by rw [← hj, hmxv, hxi])
                      subst hki
                      rcases ha' with rfl | ⟨e1', e2', e3', e4'⟩
                      · exact ⟨fun _ h ↦ by simp at h, fun _ h ↦ by simp at h, fun _ h ↦ by simp at h,
                          fun _ h ↦ by simp at h⟩
                      rw [hgi, hX.sigOf] at e1' e2' e3' e4'
                      exact postE_ok hm e1' e2' e3' e4' (fun x hx ↦ Or.inr hx)
                  refine pushRL_ok ?_ (fun _ h ↦ h) fun q hq ↦ ?_
                  swap
                  · -- the blocks' runs: the taken arm's, its index the selector's exponent
                    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hq
                    have hmi : mx.valW (vw σ) = ofK (addressOfIndex i) := by rw [hmxv, hxi]
                    obtain ⟨q0, a, S, h0, b⟩ := e
                    have h1 := hab _ he
                    simp only [abArmR, Nat.zero_add] at h1
                    exact (runF_congr (abBase_valW hmi q0 a) rfl (abBase_valW hmi h0 b)).mp h1
                  refine pushL_ok (pushPtrM_ok hm hg ?_ fun x hx ↦ Or.inr (by rw [← hX.sigOf]; exact hx))
                    (fun _ h ↦ h) fun c hc ↦ ?_
                  swap
                  · -- the returned pointers' cells
                    obtain ⟨⟨j, offs⟩, hp, hc⟩ := List.mem_flatMap.mp hc
                    cases hn : nth mr j with
                    | none => simp [hn] at hc
                    | some m =>
                      simp only [hn] at hc
                      obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hc
                      obtain ⟨r, hr', hw⟩ := hvp j offs hp o ho
                      rwa [addr_eq, CCell.addrW, valW_shift, hmr' j m hn, slotW_map_of hr']
                  refine pushRL_ok (svPut_ok (pushL_ok hs1 (fun _ ↦ Or.inl) fun c hc ↦ ?_) ?_) (fun _ h ↦ h)
                    fun q hq ↦ ?_
                  pick_goal 2
                  · exact meetVL_ok hm hg (by rw [hX.sigOf]; exact hM.2.1) _ _
                  · obtain ⟨hc1, hc2⟩ := List.mem_filter.mp hc
                    have hcg : c ∈ pg := by
                      rcases List.mem_cons.mp hpg with rfl | hpg
                      · exact hc1
                      · obtain ⟨c', hc', he⟩ := List.any_eq_true.mp (List.all_eq_true.mp hc2 pg hpg)
                        rwa [← CCell.beq_eq he]
                    obtain ⟨c0, hc0, hi0⟩ := instAll_ok e1 c hcg
                    refine Or.inr (Or.inl (Or.inl ⟨c0, hc0, ?_⟩))
                    rw [addr_eq, CCell.addrW, CCell.addrW, instC_ok hm hi0]
                  · obtain ⟨hq1, hq2⟩ := List.mem_filter.mp hq
                    have hqg : q ∈ rg := by
                      rcases List.mem_cons.mp hrg with rfl | hrg
                      · exact hq1
                      · obtain ⟨q', hq', he⟩ := List.any_eq_true.mp (List.all_eq_true.mp hq2 rg hrg)
                        unfold PRun.beq at he
                        simp only [Bool.and_eq_true] at he
                        obtain ⟨⟨⟨e1, e2⟩, e3⟩, e4⟩ := he
                        obtain ⟨b, s, l, hh⟩ := q
                        obtain ⟨b', s', l', hh'⟩ := q'
                        simp only at e1 e2 e3 e4
                        rwa [CCell.beq_eq e1, Nat.eq_of_beq_eq_true e2, CCell.beq_eq e3, CCell.beq_eq e4] at hq'
                    obtain ⟨r0, hr0, hi0⟩ := instAllR_ok e2 q hqg
                    exact fun x hx ↦ Or.inr (Or.inl (Or.inr ⟨r0, hr0, (instR_set hm hi0).mp hx⟩))

/-- **Runs at words at return**, witnessed: each at the word a load event stored at its cell, written. -/
theorem reqQ_ok (hX : XOk sigOf H rd f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt} (hs : StOk rd W σ st)
    {ms : List CCell} {ws : List E} (hms : MsOk (vw σ) ms (slotW ws)) :
    ∀ {qs : List (CCell × CRun)} {wl wl' : List Wit}, reqQ X st ms qs wl = some wl' → ∀ x, QSet rd qs ws x → W x
  | [], _, _, _, x, hx => by obtain ⟨p, hp, -⟩ := hx; cases hp
  | (c, q) :: l, wl, wl', h, x, hx => by
    cases wl with
    | nil => simp [reqQ] at h
    | cons w wl1 =>
      cases w
      all_goals try (simp [reqQ] at h; done)
      rename_i n
      simp only [reqQ] at h
      cases hc : instC ms c with
      | none => simp [hc] at h
      | some c' =>
        cases hq : instR ms q with
        | none => simp [hc, hq] at h
        | some q' =>
          cases hp : getF st.sv n with
          | none => simp [hc, hq, hp] at h
          | some p =>
            simp only [hc, hq, hp] at h
            cases hb : p.1.beq c' with
            | false => simp [hb] at h
            | true =>
              simp only [hb, Bool.cond_true] at h
              cases hr : runOk X st ⟨p.2.mul q'.base, q'.stride, q'.lo, q'.hi⟩ wl1 with
              | none => simp [hr] at h
              | some wl2 =>
                simp only [hr] at h
                obtain ⟨p0, hp0, w0, hw0, hx0⟩ := hx
                rcases List.mem_cons.mp hp0 with rfl | hp0
                · have hsv := hs.sv n p hp
                  have hcw : rd (c.addrW (slotW ws)) = some (p.2.valW (vw σ)) := by
                    rw [← hsv, CCell.beq_eq hb, addr_eq, CCell.addrW, CCell.addrW, instC_ok hms hc]
                  have hw1 : w0 = p.2.valW (vw σ) := by rw [hcw] at hw0; exact (Option.some.inj hw0).symm
                  subst hw1
                  obtain ⟨e1, e2, e3, e4⟩ := instR_ok hms hq
                  apply runOk_ok hX hpre hs hr
                  obtain ⟨ylo, yhi, j, h1, h2, h3, h4, h5⟩ := hx0
                  refine ⟨ylo, yhi, j, by rw [e3]; exact h1, by rw [e4]; exact h2, h3, h4, ?_⟩
                  rw [h5, valW_mul, e1, e2]
                · exact reqQ_ok hX hpre hs hms h x ⟨p0, hp0, w0, hw0, hx0⟩

/-- **A return**: the own guarantees written. -/
theorem retC1_ok (hX : XOk sigOf H rd f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt} {vs : List V}
    (hs : StOk rd W σ st) (h : retC1 X st vs = true) : PostW0 sigOf H rd σ (f.params.map σ) W vs := by
  unfold retC1 at h
  cases hp : monos st.env X.params with
  | none => simp [hp] at h
  | some mp =>
    cases hv : monos st.env vs with
    | none => simp [hp, hv] at h
    | some mv =>
      cases ht : getF X.T st.nt with
      | none => simp [hp, hv, ht] at h
      | some wl =>
        simp only [hp, hv, ht] at h
        obtain ⟨hmp, hlp⟩ := monos_ok hs.env _ mp hp
        obtain ⟨hmv, hlv⟩ := monos_ok hs.env vs mv hv
        have hmp' := hmp
        have hm := msOk_append hmp hmv (by simpa using hlp)
        rw [← List.map_append, hX.params] at hm
        cases h1 : reqP X st (mp ++ mv) X.sig.post wl with
        | none => simp [h1] at h
        | some wl' =>
          simp only [h1] at h
          cases h2 : reqR X st (mp ++ mv) X.sig.postR wl' with
          | none => simp [h2] at h
          | some wl2 =>
          simp only [h2] at h
          cases h3 : reqPP X st (mp ++ mv) X.sig.postP wl2 with
          | none => simp [h3] at h
          | some wl3 =>
          simp only [h3] at h
          cases h4 : reqPR X st (mp ++ mv) X.sig.postPR wl3 with
          | none => simp [h4] at h
          | some wl4 =>
          simp only [h4] at h
          cases h5 : reqQ X st (mp ++ mv) X.sig.postQ wl4 with
          | none => simp [h5] at h
          | some wl5 =>
          simp only [h5] at h
          cases h6 : reqN X st wl5 with
          | none => simp [h6] at h
          | some wl'' =>
            have hN : SigOk W H.sig.postN H.sig.postRN (H.sig.nv.map (vw σ)) := by
              unfold reqN at h6
              split at h6
              · rename_i mn hmn
                rw [hX.sig] at hmn h6
                have hmn' : MsOk (vw σ) mn (slotW (H.sig.nv.map (vw σ))) := by
                  have := (monos_ok hs.env _ mn hmn).1
                  rwa [List.map_map] at this
                cases h7 : reqP X st mn H.sig.postN wl5 with
                | none => rw [h7] at h6; cases h6
                | some wl7 =>
                  rw [h7] at h6
                  exact ⟨reqP_ok hX hpre hs hmn' h7, reqR_ok hX hpre hs hmn' h6⟩
              · cases h6
            rw [hX.sig] at h1 h2 h3 h4 h5
            rw [List.map_append] at hm
            cases wl'' with
            | cons _ _ => rw [h6] at h; simp at h
            | nil =>
            rw [hX.sig, h6] at h
            dsimp only at h
            simp only [Bool.and_eq_true] at h
            obtain ⟨⟨hM, hV⟩, hQ⟩ := h
            refine ⟨⟨reqP_ok hX hpre hs hm h1, reqR_ok hX hpre hs hm h2⟩,
              ptrOk_of (reqPP_ok hX hpre hs hm h3) (reqPR_ok hX hpre hs hm h4), fun k c hkc ↦ ?_, fun i m him ↦ ?_,
              fun p hp ↦ ?_, reqQ_ok hX hpre hs hm h5, hN⟩
            pick_goal 3
            · unfold retEqC at hQ
              have hq := List.all_eq_true.mp hQ p hp
              cases ha : instC (mp ++ mv) p.1 with
              | none => rw [ha] at hq; cases hq
              | some a =>
                cases hb : instC (mp ++ mv) p.2 with
                | none => rw [ha, hb] at hq; cases hq
                | some b =>
                  rw [ha, hb] at hq
                  rw [← instC_ok hm ha, ← instC_ok hm hb]
                  exact eqV_ok hs.eqs hq
            · unfold retMC at hM
              have hkc' := List.all_eq_true.mp hM (k, c) hkc
              dsimp only at hkc'
              cases hmk : nth mv k with
              | none => rw [hmk] at hkc'; cases hkc'
              | some m =>
                cases hic : instC mp c with
                | none => rw [hmk, hic] at hkc'; cases hkc'
                | some c' =>
                  rw [hmk, hic] at hkc'
                  have hk : k < vs.length := by
                    rw [← hlv]; rw [nth_eq] at hmk; exact (List.getElem?_eq_some_iff.mp hmk).1
                  rw [List.getElem?_map, List.getElem?_eq_getElem hk, Option.map_some, Option.some.injEq]
                  have h1 := hmv k m hmk
                  rw [slotW, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hk,
                    Option.map_some, Option.getD_some] at h1
                  rw [← h1, CCell.beq_eq hkc', instC_ok hmp' hic, hX.params]
            · unfold retVC at hV
              have hi := List.all_eq_true.mp hV (i, m) him
              dsimp only at hi
              cases hc : nth H.sig.post i with
              | none => rw [hc] at hi; cases nth wl i <;> simp at hi
              | some c =>
                obtain ⟨n, hw⟩ : ∃ n, nth wl i = some (.ev n) := by
                  cases hw : nth wl i with
                  | none => rw [hw, hc] at hi; simp at hi
                  | some w => cases w <;> first | exact ⟨_, rfl⟩ | (rw [hw, hc] at hi; simp at hi)
                rw [hw, hc] at hi
                dsimp only at hi
                cases hq : getF st.sv n with
                | none => rw [hq] at hi; simp at hi
                | some q =>
                  cases hc' : instC (mp ++ mv) c with
                  | none => rw [hq, hc'] at hi; simp at hi
                  | some c' =>
                    cases hm' : instC (mp ++ mv) m with
                    | none => rw [hq, hc', hm'] at hi; simp at hi
                    | some m' =>
                      rw [hq, hc', hm'] at hi
                      simp only [Bool.and_eq_true] at hi
                      refine ⟨c, by rw [← nth_eq, hc], ?_⟩
                      have := hs.sv n q hq
                      rw [CCell.beq_eq hi.1, CCell.beq_eq hi.2, addr_eq, CCell.addrW, instC_ok hm hc',
                        instC_ok hm hm'] at this
                      exact this

/-- The frame run cells pushed at a return are among those the certificate guarantees. -/
theorem faCells_ok (hX : XOk sigOf H rd f σ X) {env : Trie CCell} (he : EnvOk σ env) :
    ∀ c ∈ faCells env X.fas, FAX H σ (c.addr σ) := by
  intro c hc
  simp only [faCells, List.mem_map] at hc
  obtain ⟨p, hp, rfl⟩ := hc
  refine ⟨p, hX.fas ▸ hp, ?_⟩
  have hm : monoOf env (V.n p.1) = some ((getF env p.1).getD (baseC p.1)) := by simp [monoOf, vnum]
  exact (cellAt_shift σ (monoOf_ok he hm) p.2).symm

/-- **A return**: the frame run cells guaranteed at return pushed, then the own guarantees written, in `W`
or among those cells. -/
theorem retC_ok (hX : XOk sigOf H rd f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt} {vs : List V}
    (hs : StOk rd W σ st) (h : retC X st vs = true) : PostW sigOf H rd σ (f.params.map σ) W vs := by
  unfold retC at h
  rw [CSt.seq_eq] at h
  exact retC1_ok hX (fun c hc ↦ Or.inl (hpre c hc))
    (pushL_ok hs (fun _ ↦ Or.inl) fun c hc ↦ Or.inr (faCells_ok hX hs.env c hc)) h

end Stmts

end

end LeanVM.Guest.CoreMode
