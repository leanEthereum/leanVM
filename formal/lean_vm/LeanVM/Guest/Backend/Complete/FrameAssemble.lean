/-
  LeanVM.Guest.Backend.Complete.FrameAssemble

  The frame side assembled: the constructs' lemmas at the walk's instance of a function of a
  compiled program, and the block lemma at its body.
-/

module

public import LeanVM.Guest.Backend.Complete.FrameBody
public import LeanVM.Guest.Backend.Complete.FrameInner
public import LeanVM.Guest.Backend.Complete.FrameCalls
public import LeanVM.Guest.Backend.Complete.FrameAddr
public import LeanVM.Guest.Backend.Complete.FramePool

/-!
# The frame side, assembled

`bodyW_of` (FrameInner.lean) gives the block lemma at a body from the lemmas of its constructs on
the body's blocks (`InBody`). Here the straight-line and call statements' lemmas (`stmtW_atom'`,
`stmtW_frameAddr`, `stmtW_call`, `stmtW_callIf`, `stmtW_dispatch`, `stmtW_ret'`) are taken at the
walk's instance of a function of a compiled program (`instK`, the memories `agK`): its facts
(`Inst.Ok`, `OpOK`, the own frame and the callee frames on the memories, the layout's words) and
the core body's (a block of the body names only the body's values, calls itself by no `call`).
-/

namespace LeanVM.Guest.Backend.Complete

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

end
end LeanVM.Guest.Backend.Complete
