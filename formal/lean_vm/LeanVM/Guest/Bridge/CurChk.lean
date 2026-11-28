/-
  LeanVM.Guest.Bridge.CurChk

  The bump pointer check of a function, on Hotwire's hints: `curChkX`, by `decide +kernel` per
  function, and what it gives (`curFactsX_of : curChkX … = true → CurFactsX …`).
-/

module

public import LeanVM.Guest.Bridge.AllocCur

/-!
# The bump pointer check

The bus era's `curChk` (tag `formal-bus-archive`, `Bridge/AllocDefs.lean`) on Hotwire's hints and
stated on the alignment context alone: `curChkX X body code d` asks

* at each pc of the advice, the hints in their order (`Memory.ordHints`: buffers, then at most one
  frame hint, none once a frame is pending), Hotwire's replacement of `bufsFirst`;
* every jump before a buffer hint on a constant `0` or a forward jump in the frame to a constant pc,
  no buffer hint between (`bufsJumps`);
* each frame hint passing `frameOk`, every jump through a call site's frame cell one frame hint's
  and no jump two frame hints' (`sitesOk`);
* no constant jump target (`targetsOk`), `match` arm target (`blockM`, `armTgtsX`, over the
  context's table jumps) or call site's return pc (over the context's sites, `allT`) pending;
* at most as many buffer hints as allocation atoms in the body (`cntL`).

The address hints' check (the bus era's `addrOk`) is `AddrReady`'s, apart.
-/

namespace LeanVM.Guest.Bridge

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Check (getF)
open LeanVM.Guest.Exec (Trie)

@[expose] public section

/-- An allocation atom. -/
def allocAtom : Atom → Bool
  | .hint h => !coreFlow h
  | _ => false

/-- Every value of a trie passes `p`: by the recursor, for the kernel. -/
noncomputable def allT {α : Type} (p : α → Bool) (t : Trie α) : Bool :=
  Trie.rec (motive := fun _ ↦ Bool) true (fun v _ _ hl hr ↦ Option.all p v && hl && hr) t

/-- Every jump through a call site's frame cell is the next jump of a frame hint at that cell, and
no jump is the next jump of two frame hints. -/
noncomputable def sitesOk (X : AlignCtx) (code : List OffsetInstruction) (fr : List (ℕ × Prover.Exec.Hint)) :
    ℕ → List OffsetInstruction → Bool
  | _, [] => true
  | i, ins :: rest => (match ins with
      | .jump _ _ q => (!(getF X.sites q).isSome ||
          fr.any (fun r ↦ allocPtr r.2 == some q && Nat.beq (nextJump code r.1) i)) &&
          decide ((fr.filter fun r ↦ Nat.beq (nextJump code r.1) i).length ≤ 1)
      | _ => true) && sitesOk X code fr (i + 1) rest

/-- No constant jump target pending, the frame hints `fr`. -/
noncomputable def targetsOk (X : AlignCtx) (code : List OffsetInstruction) (fr : List (ℕ × Prover.Exec.Hint)) :
    List OffsetInstruction → Bool
  | [] => true
  | ins :: rest => (match ins with
      | .jump _ od _ => match X.pcAt od with
        | some t => !pendIn code fr (t - X.entry)
        | none => true
      | _ => true) && targetsOk X code fr rest

/-- Every jump before a buffer hint of `bs` passes `bufJumpOk`, the code from offset `i`. -/
noncomputable def bufsJumps (X : AlignCtx) (bs : List (ℕ × Prover.Exec.Hint)) : ℕ → List OffsetInstruction → Bool
  | _, [] => true
  | i, ins :: rest => (match ins with
      | .jump oc od of => !(bs.any fun q ↦ decide (i < q.1)) || bufJumpOk X bs i oc od of
      | _ => true) && bufsJumps X bs (i + 1) rest

/-- The allocation atoms of a block, nested ones included: by the recursor, for the kernel. -/
noncomputable def cntL : List Stmt → ℕ :=
  Stmt.rec_1 (motive_1 := fun _ ↦ ℕ) (motive_2 := fun _ ↦ ℕ) (motive_3 := fun _ ↦ ℕ)
    (fun a ↦ bif allocAtom a then 1 else 0) (fun _ _ _ hz hn ↦ hz + hn) (fun _ _ ha ↦ ha) (fun _ _ _ ↦ 0)
    (fun _ _ _ ↦ 0) (fun _ _ _ _ ↦ 0) (fun _ ↦ 0) 0 (fun _ _ hs hss ↦ hs + hss) 0 (fun _ _ ha has ↦ ha + has)

/-- Every `match` of a block, nested ones included, passes `ok` on its selector and arm count: by
the recursor, for the kernel. -/
noncomputable def blockM (ok : V → ℕ → Bool) : List Stmt → Bool :=
  Stmt.rec_1 (motive_1 := fun _ ↦ Bool) (motive_2 := fun _ ↦ Bool) (motive_3 := fun _ ↦ Bool)
    (fun _ ↦ true) (fun _ _ _ hz hn ↦ hz && hn) (fun x arms ha ↦ ok x arms.length && ha) (fun _ _ _ ↦ true)
    (fun _ _ _ ↦ true) (fun _ _ _ _ ↦ true) (fun _ ↦ true) true (fun _ _ hs hss ↦ hs && hss) true
    (fun _ _ ha has ↦ ha && has)

/-- No arm target of a `match` of selector `x` and `n` arms pending, the frame hints `fr`: through
each table jump of the selector (`X.arms`), each of its `n` slots. -/
noncomputable def armTgtsX (X : AlignCtx) (code : List OffsetInstruction) (fr : List (ℕ × Prover.Exec.Hint))
    (x : V) (n : ℕ) : Bool :=
  allT (fun a ↦ !(Nat.beq a.1 x.idx) || (List.range n).all fun k ↦ match getF X.jt (a.2 + k) with
    | some t => !pendIn code fr (t - X.entry)
    | none => true) X.arms

/-- **The bump pointer check** of a function's context, body, code and advice. -/
noncomputable def curChkX (X : AlignCtx) (body : List Stmt) (code : List OffsetInstruction)
    (d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)) : Bool :=
  Exec.listSeq (allocHints d) fun hs ↦
    Exec.listSeq (hs.filter fun q ↦ isFrame X q.2) fun fr ↦
    Exec.listSeq (hs.filter fun q ↦ isBuf X q.2) fun bs ↦
  d.2.2.all (fun q ↦ ordHints (isBuf X) (isFrame X) (pendIn code fr (q.1 - X.entry)) q.2) &&
    bufsJumps X bs 0 code && fr.all (fun q ↦ frameOk X code q.1 q.2) && sitesOk X code fr 0 code &&
    decide (cntL body ≤ bs.length) &&
    (fr.isEmpty || (targetsOk X code fr code && blockM (armTgtsX X code fr) body &&
      allT (fun s ↦ !pendIn code fr (s.r - X.entry)) X.sites))

/-- A jump through a next frame only in a loop helper. -/
noncomputable def nextOkX (X : AlignCtx) (loop : Bool) (code : List OffsetInstruction) : Bool :=
  loop || code.all fun ins ↦ match ins with
    | .jump _ _ q => !X.nextAt q
    | _ => true

/-- A loop helper's final conditional call through no call site of the context (the bus era's
`loopChk`, over the context's sites). -/
noncomputable def loopChkX (fn : Fn) (X : AlignCtx) : Bool :=
  match fn.body.reverse with
  | .ret [] :: .callIf _ _ args :: rpre =>
      noRetB rpre.reverse && allT (fun s ↦ !(s.args == args.map (·.idx) && s.rets == [])) X.sites
  | _ => false

/-- **A function's allocation track check**: the bump pointer check, a jump through a next frame
only in a loop helper, a loop helper's last call through no call site. -/
noncomputable def allocFnChk (X : AlignCtx) (fn : Fn) (code : List OffsetInstruction)
    (d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)) : Bool :=
  curChkX X fn.body code d && nextOkX X fn.loop code && (!fn.loop || loopChkX fn X)

end

public section

/-! ## Tries -/

theorem allT_getF {α : Type} {p : α → Bool} :
    ∀ (t : Trie α) (k : ℕ) {a : α}, allT p t = true → getF t k = some a → p a = true
  | .nil, _, _, _, h => by cases h
  | .node v l r, 0, a, hA, h => by
    change (Option.all p v && allT p l && allT p r) = true at hA
    change v = some a at h
    subst h
    simp only [Bool.and_eq_true, Option.all_some] at hA
    exact hA.1.1
  | .node v l r, m + 1, a, hA, h => by
    change (Option.all p v && allT p l && allT p r) = true at hA
    change Bool.rec (getF r (Nat.div m 2)) (getF l (Nat.div m 2)) (Nat.beq (Nat.mod m 2) 0) = some a at h
    simp only [Bool.and_eq_true] at hA
    cases hb : Nat.beq (Nat.mod m 2) 0
    · rw [hb] at h; exact allT_getF r _ hA.2 h
    · rw [hb] at h; exact allT_getF l _ hA.1.2 h

/-! ## The check's walks -/

theorem bufsJumps_at {X : AlignCtx} {bs : List (ℕ × Prover.Exec.Hint)} :
    ∀ (k : ℕ) (l : List OffsetInstruction), bufsJumps X bs k l = true → ∀ i oc od of, l[i]? = some (.jump oc od of) →
      (∀ q ∈ bs, q.1 ≤ k + i) ∨ bufJumpOk X bs (k + i) oc od of = true
  | _, [], _, _, _, _, _, h => by simp at h
  | k, ins :: rest, h, i, oc, od, of, hi => by
    simp only [bufsJumps, Bool.and_eq_true] at h
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      simp only [Bool.or_eq_true, Bool.not_eq_true', List.any_eq_false, decide_eq_true_eq, not_lt,
        Nat.add_zero] at h ⊢
      exact h.1
    | succ i =>
      simp only [List.getElem?_cons_succ] at hi
      have := bufsJumps_at (k + 1) rest h.2 i oc od of hi
      rwa [show k + 1 + i = k + (i + 1) by omega] at this

theorem sitesOk_at {X : AlignCtx} {code : List OffsetInstruction} {fr : List (ℕ × Prover.Exec.Hint)} :
    ∀ (k : ℕ) (l : List OffsetInstruction), sitesOk X code fr k l = true → ∀ i oc od q, l[i]? = some (.jump oc od q) →
      ((getF X.sites q).isSome = true →
        ∃ r ∈ fr, allocPtr r.2 = some q ∧ nextJump code r.1 = k + i) ∧
      (fr.filter fun r ↦ Nat.beq (nextJump code r.1) (k + i)).length ≤ 1
  | _, [], _, _, _, _, _, h => by simp at h
  | k, ins :: rest, h, i, oc, od, q, hi => by
    simp only [sitesOk, Bool.and_eq_true] at h
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      simp only [Bool.or_eq_true, Bool.not_eq_true', List.any_eq_true, Bool.and_eq_true, beq_iff_eq,
        Nat.beq_eq, decide_eq_true_eq, Nat.add_zero] at h ⊢
      obtain ⟨⟨h1, h2⟩, -⟩ := h
      refine ⟨fun hs ↦ ?_, h2⟩
      rcases h1 with h1 | h1
      · rw [h1] at hs; cases hs
      · exact h1
    | succ i =>
      simp only [List.getElem?_cons_succ] at hi
      have := sitesOk_at (k + 1) rest h.2 i oc od q hi
      rwa [show k + 1 + i = k + (i + 1) by omega] at this

theorem targetsOk_at {X : AlignCtx} {code : List OffsetInstruction} {fr : List (ℕ × Prover.Exec.Hint)} :
    ∀ (l : List OffsetInstruction), targetsOk X code fr l = true → ∀ (i oc od of : ℕ),
      l[i]? = some (OffsetInstruction.jump oc od of) →
      ∀ t, X.pcAt od = some t → pendIn code fr (t - X.entry) = false
  | [], _, _, _, _, _, h, _, _ => by simp at h
  | ins :: rest, h, i, oc, od, of, hi, t, ht => by
    simp only [targetsOk, Bool.and_eq_true] at h
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      have := h.1
      simp only [ht, Bool.not_eq_true'] at this
      exact this
    | succ i =>
      simp only [List.getElem?_cons_succ] at hi
      exact targetsOk_at rest h.2 i oc od of hi t ht


/-! ## The body's `match`es and allocations -/

/-- `blockM` of a statement. -/
noncomputable def stmtM (ok : V → ℕ → Bool) : Stmt → Bool :=
  Stmt.rec (motive_1 := fun _ ↦ Bool) (motive_2 := fun _ ↦ Bool) (motive_3 := fun _ ↦ Bool)
    (fun _ ↦ true) (fun _ _ _ hz hn ↦ hz && hn) (fun x arms ha ↦ ok x arms.length && ha) (fun _ _ _ ↦ true)
    (fun _ _ _ ↦ true) (fun _ _ _ _ ↦ true) (fun _ ↦ true) true (fun _ _ hs hss ↦ hs && hss) true
    (fun _ _ ha has ↦ ha && has)

/-- `blockM` of arms. -/
noncomputable def armsM (ok : V → ℕ → Bool) : List (List Stmt) → Bool :=
  Stmt.rec_2 (motive_1 := fun _ ↦ Bool) (motive_2 := fun _ ↦ Bool) (motive_3 := fun _ ↦ Bool)
    (fun _ ↦ true) (fun _ _ _ hz hn ↦ hz && hn) (fun x arms ha ↦ ok x arms.length && ha) (fun _ _ _ ↦ true)
    (fun _ _ _ ↦ true) (fun _ _ _ _ ↦ true) (fun _ ↦ true) true (fun _ _ hs hss ↦ hs && hss) true
    (fun _ _ ha has ↦ ha && has)

section M

variable (ok : V → ℕ → Bool)

mutual
theorem blockM_sels : ∀ (ss : List Stmt), blockM ok ss = true → ∀ s ∈ stmtsOf ss, ∀ x arms,
    s = .match_ x arms → ok x arms.length = true
  | [], _, s, hs => by simp [stmtsOf] at hs
  | s' :: ss, h, s, hs => by
    change (stmtM ok s' && blockM ok ss) = true at h
    rw [Bool.and_eq_true] at h
    rw [stmtsOf, List.mem_cons, List.mem_append] at hs
    rcases hs with rfl | hs | hs
    · intro x arms he
      subst he
      have h1 := h.1
      change (ok x arms.length && armsM ok arms) = true at h1
      exact ((Bool.and_eq_true _ _).mp h1).1
    · exact stmtM_sels s' h.1 s hs
    · exact blockM_sels ss h.2 s hs

theorem stmtM_sels : ∀ (s' : Stmt), stmtM ok s' = true → ∀ s ∈ stmtsSub s', ∀ x arms,
    s = .match_ x arms → ok x arms.length = true
  | .ite c' z n, h, s, hs => by
    change (blockM ok z && blockM ok n) = true at h
    simp only [Bool.and_eq_true] at h
    simp only [stmtsSub, List.mem_append] at hs
    rcases hs with hs | hs
    · exact blockM_sels z h.1 s hs
    · exact blockM_sels n h.2 s hs
  | .match_ x arms, h, s, hs => by
    change (ok x arms.length && armsM ok arms) = true at h
    rw [Bool.and_eq_true] at h
    exact armsM_sels arms h.2 s hs
  | .atom _, _, _, hs | .call .., _, _, hs | .callIf .., _, _, hs | .dispatch .., _, _, hs | .ret _, _, _, hs => by
    simp [stmtsSub] at hs

theorem armsM_sels : ∀ (arms : List (List Stmt)), armsM ok arms = true → ∀ s ∈ stmtsArms arms, ∀ x as,
    s = .match_ x as → ok x as.length = true
  | [], _, s, hs => by simp [stmtsArms] at hs
  | a :: as, h, s, hs => by
    change (blockM ok a && armsM ok as) = true at h
    rw [Bool.and_eq_true] at h
    rw [stmtsArms, List.mem_append] at hs
    rcases hs with hs | hs
    · exact blockM_sels a h.1 s hs
    · exact armsM_sels as h.2 s hs
end

end M

/-- `cntL` of a statement. -/
noncomputable def cntS : Stmt → ℕ :=
  Stmt.rec (motive_1 := fun _ ↦ ℕ) (motive_2 := fun _ ↦ ℕ) (motive_3 := fun _ ↦ ℕ)
    (fun a ↦ bif allocAtom a then 1 else 0) (fun _ _ _ hz hn ↦ hz + hn) (fun _ _ ha ↦ ha) (fun _ _ _ ↦ 0)
    (fun _ _ _ ↦ 0) (fun _ _ _ _ ↦ 0) (fun _ ↦ 0) 0 (fun _ _ hs hss ↦ hs + hss) 0 (fun _ _ ha has ↦ ha + has)

/-- `cntL` of arms. -/
noncomputable def cntA : List (List Stmt) → ℕ :=
  Stmt.rec_2 (motive_1 := fun _ ↦ ℕ) (motive_2 := fun _ ↦ ℕ) (motive_3 := fun _ ↦ ℕ)
    (fun a ↦ bif allocAtom a then 1 else 0) (fun _ _ _ hz hn ↦ hz + hn) (fun _ _ ha ↦ ha) (fun _ _ _ ↦ 0)
    (fun _ _ _ ↦ 0) (fun _ _ _ _ ↦ 0) (fun _ ↦ 0) 0 (fun _ _ hs hss ↦ hs + hss) 0 (fun _ _ ha has ↦ ha + has)

section Cnt

variable {σ : Val}

/-- The events of an outcome. -/
def evs : Out → List Ev
  | .fall es => es
  | .ret es _ => es
  | .stuck => []

theorem nA_pre (es : List Ev) : ∀ o : Out, (allocDsts (evs (o.pre es))).length ≤
    (allocDsts es).length + (allocDsts (evs o)).length
  | .fall _ | .ret _ _ => by simp [Out.pre, evs, allocDsts]
  | .stuck => by simp [Out.pre, evs, allocDsts]

theorem nA_seq (k : Out) : ∀ o : Out, (allocDsts (evs (o.seq k))).length ≤
    (allocDsts (evs o)).length + (allocDsts (evs k)).length
  | .fall es => by simp only [Out.seq]; exact nA_pre es k
  | .ret _ _ => by simp [Out.seq, evs]
  | .stuck => by simp [Out.seq, evs, allocDsts]

theorem nA_pick {x : V} {args rets : List V} :
    ∀ (fs : List String) (j : ℕ), (allocDsts (evs (pick σ x args rets j fs))).length = 0
  | [], _ => by simp [pick, evs, allocDsts]
  | f :: fs, j => by
    rw [pick]
    split_ifs
    · simp [evs, allocDsts, Ev.allocDst?]
    · exact nA_pick fs (j + 1)

mutual
theorem nA_walk1 : ∀ (s : Stmt), (allocDsts (evs (walk1 σ s))).length ≤ cntS s
  | .atom a => by
    change (allocDsts [Ev.atom a]).length ≤ bif allocAtom a then 1 else 0
    rcases a with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨_ | _ | _ | _ | _ | _ | _ | _⟩ | _ <;>
      simp [allocDsts, Ev.allocDst?, allocAtom, coreFlow]
  | .ite c z n => by
    change _ ≤ cntL z + cntL n
    rw [walk1]
    refine (nA_pre _ _).trans ?_
    have h1 := nA_walk z
    have h2 := nA_walk n
    have h0 : (allocDsts [Ev.inK c]).length = 0 := rfl
    split_ifs <;> omega
  | .match_ x arms => by
    change _ ≤ cntA arms
    rw [walk1]
    exact nA_arms x arms 0
  | .call f args rets => by
    change (allocDsts [Ev.call f args rets]).length ≤ 0
    exact Nat.le_of_eq rfl
  | .callIf c f args => by
    change (allocDsts [.inK c, if σ c = 0 then .skip f args else .call f args []]).length ≤ 0
    split_ifs <;> exact Nat.le_of_eq rfl
  | .dispatch x fs args rets => by rw [walk1, nA_pick]; exact Nat.zero_le _
  | .ret _ => by simp [walk1, evs, allocDsts]

theorem nA_walk : ∀ (ss : List Stmt), (allocDsts (evs (walk σ ss))).length ≤ cntL ss
  | [] => by simp [walk, evs, allocDsts]
  | s :: ss => by
    change _ ≤ cntS s + cntL ss
    rw [walk]
    exact (nA_seq _ _).trans (Nat.add_le_add (nA_walk1 s) (nA_walk ss))

theorem nA_arms (x : V) : ∀ (arms : List (List Stmt)) (j : ℕ), (allocDsts (evs (walkArms σ x j arms))).length ≤ cntA arms
  | [], _ => by simp [walkArms, evs, allocDsts]
  | a :: as, j => by
    change _ ≤ cntL a + cntA as
    rw [walkArms]
    split_ifs
    · exact (nA_walk a).trans (Nat.le_add_right _ _)
    · exact (nA_arms x as (j + 1)).trans (Nat.le_add_left _ _)
end

/-- **A path allocates at most `cntL` buffers.** -/
theorem allocDsts_le_cnt {body : List Stmt} {es : List Ev} {vs : List V} (h : walk σ body = .ret es vs) :
    (allocDsts es).length ≤ cntL body := by
  have := nA_walk (σ := σ) body
  rw [h] at this
  exact this

end Cnt

/-! ## What the check gives -/

theorem armTgtsX_at {X : AlignCtx} {code : List OffsetInstruction} {fr : List (ℕ × Prover.Exec.Hint)} {x : V}
    {n : ℕ} (h : armTgtsX X code fr x n = true) {od : ℕ} {a : ℕ × ℕ} (ha : getF X.arms od = some a)
    (hax : a.1 = x.idx) {k t : ℕ} (hk : k < n) (ht : getF X.jt (a.2 + k) = some t) :
    pendIn code fr (t - X.entry) = false := by
  have h1 := allT_getF _ _ h ha
  simp only [hax, Nat.beq_refl, Bool.not_true, Bool.false_or, List.all_eq_true, List.mem_range] at h1
  have := h1 k hk
  simp only [ht, Bool.not_eq_true'] at this
  exact this

/-- **What the bump pointer check gives.** -/
theorem curFactsX_of {X : AlignCtx} {body : List Stmt} {code : List OffsetInstruction}
    {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)} (h : curChkX X body code d = true) :
    CurFactsX X body code d := by
  simp only [curChkX, Exec.listSeq_eq, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hord, hj⟩, hfr⟩, hso⟩, -⟩, hrest⟩ := h
  have hnil : (frames X d).isEmpty = true → ∀ off, pendIn code (frames X d) off = false := fun h0 off ↦ by
    rw [List.isEmpty_iff.mp h0]; rfl
  refine ⟨hord, fun i oc od of hi ↦ ?_, hfr, fun i ins hi hjj ↦ ?_, fun i oc od of hi hsi ↦ ?_,
    fun i oc od of hi t ht ↦ ?_, fun s hs x arms he od a k t ha hax hk ht ↦ ?_, fun q args rets s hs ↦ ?_⟩
  · have := bufsJumps_at 0 code hj i oc od of hi
    rwa [Nat.zero_add] at this
  · cases ins with
    | jump oc od of =>
      have := (sitesOk_at 0 code hso i oc od of hi).2
      rwa [Nat.zero_add] at this
    | _ => cases hjj
  · have := (sitesOk_at 0 code hso i oc od of hi).1 hsi
    rwa [Nat.zero_add] at this
  · rcases hrest with h0 | ⟨⟨ht', -⟩, -⟩
    · exact hnil h0 _
    · exact targetsOk_at code ht' i oc od of hi t ht
  · rcases hrest with h0 | ⟨⟨-, hb⟩, -⟩
    · exact hnil h0 _
    · exact armTgtsX_at (blockM_sels _ body hb s hs x arms he) ha hax hk ht
  · rcases hrest with h0 | ⟨-, hs'⟩
    · exact hnil h0 _
    · unfold AlignCtx.siteAt at hs
      split at hs
      · rename_i s' hs''
        have hss : s' = s := by
          cases hc : (s'.args == args.map (·.idx) && s'.rets == rets.map (·.idx))
          · simp [hc] at hs
          · simp only [hc, Bool.cond_true, Option.some.injEq] at hs; exact hs
        subst hss
        have := allT_getF _ _ hs' hs''
        simp only [Bool.not_eq_true'] at this
        exact this
      · cases hs

/-- **A buffer count from the check**: at most as many allocation atoms as buffer hints. -/
theorem cnt_of_curChkX {X : AlignCtx} {body : List Stmt} {code : List OffsetInstruction}
    {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)} (h : curChkX X body code d = true) :
    cntL body ≤ (bufsOf X d).length := by
  simp only [curChkX, Exec.listSeq_eq, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.2

/-- **A jump through a next frame is a loop helper's.** -/
theorem loop_of_nextOk {X : AlignCtx} {loop : Bool} {code : List OffsetInstruction} (h : nextOkX X loop code = true)
    {off oc od of : ℕ} (hi : code[off]? = some (.jump oc od of)) (hn : X.nextAt of = true) : loop = true := by
  unfold nextOkX at h
  rw [Bool.or_eq_true] at h
  rcases h with h | h
  · exact h
  · have := List.all_eq_true.mp h _ (List.mem_of_getElem? hi)
    simp only [hn, Bool.not_true] at this
    cases this

theorem siteAt_spec {X : AlignCtx} {q : ℕ} {args rets : List V} {s : B2C.Site} (h : X.siteAt q args rets = some s) :
    getF X.sites q = some s ∧ s.args = args.map (·.idx) ∧ s.rets = rets.map (·.idx) := by
  unfold AlignCtx.siteAt at h
  split at h
  · rename_i s' hs'
    cases hc : (s'.args == args.map (·.idx) && s'.rets == rets.map (·.idx))
    · simp [hc] at h
    · simp only [hc, Bool.cond_true, Option.some.injEq] at h
      subst h
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      exact ⟨hs', hc.1, hc.2⟩
  · cases h

/-- **A loop helper's call through a call site is not its last.** -/
theorem loopX_notLast {fn : Fn} {X : AlignCtx} (h : loopChkX fn X = true) {σ : Val} {es : List Ev} {vs : List V}
    (hw : walk σ fn.body = .ret es vs) {i : ℕ} {c : Call} (hc : (calls es)[i]? = some c) {q : ℕ} {s : B2C.Site}
    (hs : X.siteAt q c.args c.rets = some s) : i + 1 < (calls es).length := by
  have hlt : i < (calls es).length := (List.getElem?_eq_some_iff.mp hc).1
  by_contra hge
  have hi : i + 1 = (calls es).length := by omega
  obtain ⟨hs', ha, hr⟩ := siteAt_spec hs
  unfold loopChkX at h
  split at h
  case h_2 => cases h
  rename_i cc g args rpre hrev
  rw [Bool.and_eq_true] at h
  obtain rfl := loop_last_call hrev h.1 hw hc hi
  have ha' : s.args = args.map (·.idx) := ha
  have hr' : s.rets = [] := hr
  have hm := allT_getF _ _ h.2 hs'
  simp [ha', hr'] at hm

end

end LeanVM.Guest.Bridge
