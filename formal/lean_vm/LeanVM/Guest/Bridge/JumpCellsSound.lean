/-
  LeanVM.Guest.Bridge.JumpCellsSound

  What the jump cells' checks give: a body's conditions and selectors, its statements at every aligned position, and a loop helper's last call.
-/

module

public import LeanVM.Guest.Bridge.JumpCellsDefs
public import LeanVM.Guest.Bridge.AlignRun
public import LeanVM.Guest.Memory.StaticSound
public import LeanVM.Guest.Bridge.Track

/-!
# The jump cells' checks

`blockB_conds`, `blockB_sels`: a body passing `blockB cOk` has every condition passing `cOk` and every `match` selector numbered. `noRetB_spec`: `noRetB` is `Memory.Stmt.noRetListS`. `walk_inK`: a condition a path tests is one of the body's (`condsOf`). `zok_stmts`: every statement of an aligned position (a zipper of the body, `ZOk`) is one of the body's. `loop_last`: on a loop helper passing `loopChk`, the last call of every path is the final conditional call's, which no site of `Plumb` matches.
-/

namespace LeanVM.Guest.Bridge

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B2C

public section

/-! ## The recursor checks -/

section Rec

variable (cOk : V → Bool)

mutual
theorem blockB_conds : ∀ (ss : List Stmt), blockB cOk ss = true → ∀ c ∈ condsOf ss, cOk c = true
  | [], _, c, hc => by simp [condsOf] at hc
  | s :: ss, h, c, hc => by
    change (stmtB cOk s && blockB cOk ss) = true at h
    rw [Bool.and_eq_true] at h
    rw [condsOf, List.mem_append] at hc
    rcases hc with hc | hc
    · exact stmtB_conds s h.1 c hc
    · exact blockB_conds ss h.2 c hc

theorem stmtB_conds : ∀ (s : Stmt), stmtB cOk s = true → ∀ c ∈ condsSub s, cOk c = true
  | .ite c' z n, h, c, hc => by
    change (cOk c' && blockB cOk z && blockB cOk n) = true at h
    simp only [Bool.and_eq_true] at h
    simp only [condsSub, List.mem_cons, List.mem_append] at hc
    rcases hc with rfl | hc | hc
    · exact h.1.1
    · exact blockB_conds z h.1.2 c hc
    · exact blockB_conds n h.2 c hc
  | .match_ x arms, h, c, hc => by
    change (numbered x && armsB cOk arms) = true at h
    rw [Bool.and_eq_true] at h
    exact armsB_conds arms h.2 c hc
  | .callIf c' _ _, h, c, hc => by
    simp only [condsSub, List.mem_singleton] at hc
    subst hc
    exact h
  | .atom _, _, _, hc | .call .., _, _, hc | .dispatch .., _, _, hc | .ret _, _, _, hc => by
    simp [condsSub] at hc

theorem armsB_conds : ∀ (arms : List (List Stmt)), armsB cOk arms = true → ∀ c ∈ condsArms arms, cOk c = true
  | [], _, c, hc => by simp [condsArms] at hc
  | a :: as, h, c, hc => by
    change (blockB cOk a && armsB cOk as) = true at h
    rw [Bool.and_eq_true] at h
    rw [condsArms, List.mem_append] at hc
    rcases hc with hc | hc
    · exact blockB_conds a h.1 c hc
    · exact armsB_conds as h.2 c hc
end

mutual
theorem blockB_sels : ∀ (ss : List Stmt), blockB cOk ss = true → ∀ s ∈ stmtsOf ss, ∀ x arms,
    s = .match_ x arms → numbered x = true
  | [], _, s, hs => by simp [stmtsOf] at hs
  | s' :: ss, h, s, hs => by
    change (stmtB cOk s' && blockB cOk ss) = true at h
    rw [Bool.and_eq_true] at h
    rw [stmtsOf, List.mem_cons, List.mem_append] at hs
    rcases hs with rfl | hs | hs
    · intro x arms he
      subst he
      have h1 := h.1
      change (numbered x && armsB cOk arms) = true at h1
      exact ((Bool.and_eq_true _ _).mp h1).1
    · exact stmtB_sels s' h.1 s hs
    · exact blockB_sels ss h.2 s hs

theorem stmtB_sels : ∀ (s' : Stmt), stmtB cOk s' = true → ∀ s ∈ stmtsSub s', ∀ x arms,
    s = .match_ x arms → numbered x = true
  | .ite c' z n, h, s, hs => by
    change (cOk c' && blockB cOk z && blockB cOk n) = true at h
    simp only [Bool.and_eq_true] at h
    simp only [stmtsSub, List.mem_append] at hs
    rcases hs with hs | hs
    · exact blockB_sels z h.1.2 s hs
    · exact blockB_sels n h.2 s hs
  | .match_ x arms, h, s, hs => by
    change (numbered x && armsB cOk arms) = true at h
    rw [Bool.and_eq_true] at h
    exact armsB_sels arms h.2 s hs
  | .atom _, _, _, hs | .call .., _, _, hs | .callIf .., _, _, hs | .dispatch .., _, _, hs | .ret _, _, _, hs => by
    simp [stmtsSub] at hs

theorem armsB_sels : ∀ (arms : List (List Stmt)), armsB cOk arms = true → ∀ s ∈ stmtsArms arms, ∀ x as,
    s = .match_ x as → numbered x = true
  | [], _, s, hs => by simp [stmtsArms] at hs
  | a :: as, h, s, hs => by
    change (blockB cOk a && armsB cOk as) = true at h
    rw [Bool.and_eq_true] at h
    rw [stmtsArms, List.mem_append] at hs
    rcases hs with hs | hs
    · exact blockB_sels a h.1 s hs
    · exact armsB_sels as h.2 s hs
end

end Rec

/-- No `ret` in a statement, by the recursor. -/
noncomputable def noRetS : Stmt → Bool :=
  Stmt.rec (motive_1 := fun _ ↦ Bool) (motive_2 := fun _ ↦ Bool) (motive_3 := fun _ ↦ Bool)
    (fun _ ↦ true) (fun _ _ _ hz hn ↦ hz && hn) (fun _ _ ha ↦ ha) (fun _ _ _ ↦ true) (fun _ _ _ ↦ true)
    (fun _ _ _ _ ↦ true) (fun _ ↦ false) true (fun _ _ hs hss ↦ hs && hss) true (fun _ _ ha has ↦ ha && has)

/-- No `ret` in arms, by the recursor. -/
noncomputable def noRetA : List (List Stmt) → Bool :=
  Stmt.rec_2 (motive_1 := fun _ ↦ Bool) (motive_2 := fun _ ↦ Bool) (motive_3 := fun _ ↦ Bool)
    (fun _ ↦ true) (fun _ _ _ hz hn ↦ hz && hn) (fun _ _ ha ↦ ha) (fun _ _ _ ↦ true) (fun _ _ _ ↦ true)
    (fun _ _ _ _ ↦ true) (fun _ ↦ false) true (fun _ _ hs hss ↦ hs && hss) true (fun _ _ ha has ↦ ha && has)

mutual
theorem noRetB_spec : ∀ (ss : List Stmt), noRetB ss = true → Memory.Stmt.noRetListS ss = true
  | [], _ => rfl
  | s :: ss, h => by
    change (noRetS s && noRetB ss) = true at h
    rw [Bool.and_eq_true] at h
    simp only [Memory.Stmt.noRetListS, Bool.and_eq_true]
    exact ⟨noRetS_spec s h.1, noRetB_spec ss h.2⟩

theorem noRetS_spec : ∀ (s : Stmt), noRetS s = true → Memory.Stmt.noRet s = true
  | .ite _ z n, h => by
    change (noRetB z && noRetB n) = true at h
    rw [Bool.and_eq_true] at h
    simp only [Memory.Stmt.noRet, Bool.and_eq_true]
    exact ⟨noRetB_spec z h.1, noRetB_spec n h.2⟩
  | .match_ _ arms, h => by
    simp only [Memory.Stmt.noRet]
    exact noRetA_spec arms h
  | .ret _, h => by cases h
  | .atom _, _ | .call .., _ | .callIf .., _ | .dispatch .., _ => by simp [Memory.Stmt.noRet]

theorem noRetA_spec : ∀ (arms : List (List Stmt)), noRetA arms = true → Memory.Stmt.noRetArms arms = true
  | [], _ => rfl
  | a :: as, h => by
    change (noRetB a && noRetA as) = true at h
    rw [Bool.and_eq_true] at h
    simp only [Memory.Stmt.noRetArms, Bool.and_eq_true]
    exact ⟨noRetB_spec a h.1, noRetA_spec as h.2⟩
end

/-! ## Conditions on a path -/

/-- The events of an outcome. -/
def evsOf : Out → List Ev
  | .fall es => es
  | .ret es _ => es
  | .stuck => []

theorem evsOf_ret (es : List Ev) (vs : List V) : evsOf (.ret es vs) = es := by simp [evsOf]

theorem evsOf_pre {es : List Ev} {e : Ev} : ∀ {o : Out}, e ∈ evsOf (o.pre es) → e ∈ es ∨ e ∈ evsOf o
  | .fall _, h | .ret _ _, h => List.mem_append.mp h
  | .stuck, h => by simp [Out.pre, evsOf] at h

theorem evsOf_seq {k : Out} {e : Ev} : ∀ {o : Out}, e ∈ evsOf (o.seq k) → e ∈ evsOf o ∨ e ∈ evsOf k
  | .fall _, h => (evsOf_pre h)
  | .ret _ _, h => Or.inl h
  | .stuck, h => by simp [Out.seq, evsOf] at h

section Walk

variable {σ : Val}

theorem pick_inK {x : V} {args rets : List V} {c : V} : ∀ (fs : List String) (j : ℕ),
    Ev.inK c ∉ evsOf (pick σ x args rets j fs)
  | [], _ => by simp [pick, evsOf]
  | f :: fs, j => by
    unfold pick
    split_ifs
    · simp [evsOf]
    · exact pick_inK fs (j + 1)

mutual
theorem walk1_inK {c : V} : ∀ (s : Stmt), Ev.inK c ∈ evsOf (walk1 σ s) → c ∈ condsSub s
  | .atom _, h => by simp [walk1, evsOf] at h
  | .ite c' z n, h => by
    rw [walk1] at h
    rcases evsOf_pre h with h | h
    · simp only [List.mem_singleton, Ev.inK.injEq] at h; subst h; simp [condsSub]
    · split_ifs at h
      · exact List.mem_cons_of_mem _ (List.mem_append_left _ (walk_inK z h))
      · exact List.mem_cons_of_mem _ (List.mem_append_right _ (walk_inK n h))
  | .match_ x arms, h => walkArms_inK x arms 0 h
  | .call .., h => by simp [walk1, evsOf] at h
  | .callIf c' _ _, h => by
    simp only [walk1, evsOf, List.mem_cons, Ev.inK.injEq, List.not_mem_nil, or_false] at h
    rcases h with rfl | h
    · simp [condsSub]
    · split_ifs at h
  | .dispatch _ fs _ _, h => absurd h (pick_inK fs 0)
  | .ret _, h => by simp [walk1, evsOf] at h

theorem walk_inK {c : V} : ∀ (ss : List Stmt), Ev.inK c ∈ evsOf (walk σ ss) → c ∈ condsOf ss
  | [], h => by simp [walk, evsOf] at h
  | s :: ss, h => by
    rw [walk] at h
    rcases evsOf_seq h with h | h
    · exact List.mem_append_left _ (walk1_inK s h)
    · exact List.mem_append_right _ (walk_inK ss h)

theorem walkArms_inK {c : V} (x : V) : ∀ (arms : List (List Stmt)) (j : ℕ),
    Ev.inK c ∈ evsOf (walkArms σ x j arms) → c ∈ condsArms arms
  | [], _, h => by simp [walkArms, evsOf] at h
  | a :: as, j, h => by
    unfold walkArms at h
    split_ifs at h
    · exact List.mem_append_left _ (walk_inK a h)
    · exact List.mem_append_right _ (walkArms_inK x as (j + 1) h)
end

end Walk

/-! ## Statements of aligned positions -/

theorem mem_stmtsOf {s : Stmt} : ∀ {ss : List Stmt}, s ∈ ss → s ∈ stmtsOf ss
  | _ :: _, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ (mem_stmtsOf h))

mutual
theorem sub_stmtsOf {s t : Stmt} : ∀ {ss : List Stmt}, s ∈ stmtsOf ss → t ∈ stmtsSub s → t ∈ stmtsOf ss
  | s' :: ss, hs, ht => by
    rw [stmtsOf, List.mem_cons, List.mem_append] at hs
    rcases hs with rfl | hs | hs
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ ht)
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ (sub_stmtsSub hs ht))
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ (sub_stmtsOf hs ht))

theorem sub_stmtsSub {s t : Stmt} : ∀ {s' : Stmt}, s ∈ stmtsSub s' → t ∈ stmtsSub s → t ∈ stmtsSub s'
  | .ite _ z n, hs, ht => by
    rw [stmtsSub, List.mem_append] at hs ⊢
    rcases hs with hs | hs
    · exact Or.inl (sub_stmtsOf hs ht)
    · exact Or.inr (sub_stmtsOf hs ht)
  | .match_ _ arms, hs, ht => sub_stmtsArms hs ht
  | .atom _, hs, _ | .call .., hs, _ | .callIf .., hs, _ | .dispatch .., hs, _ | .ret _, hs, _ => by
    simp [stmtsSub] at hs

theorem sub_stmtsArms {s t : Stmt} : ∀ {arms : List (List Stmt)}, s ∈ stmtsArms arms → t ∈ stmtsSub s →
    t ∈ stmtsArms arms
  | a :: as, hs, ht => by
    rw [stmtsArms, List.mem_append] at hs ⊢
    rcases hs with hs | hs
    · exact Or.inl (sub_stmtsOf hs ht)
    · exact Or.inr (sub_stmtsArms hs ht)
end

theorem stmtsOf_arms {a : List Stmt} {t : Stmt} : ∀ {arms : List (List Stmt)}, a ∈ arms → t ∈ stmtsOf a →
    t ∈ stmtsArms arms
  | _ :: _, ha, ht => by
    rw [stmtsArms, List.mem_append]
    rcases List.mem_cons.mp ha with rfl | ha
    · exact Or.inl ht
    · exact Or.inr (stmtsOf_arms ha ht)

theorem subBlock_sub {s t : Stmt} {c : ℕ} (ht : t ∈ subBlock s c) : t ∈ stmtsSub s := by
  cases s with
  | ite _ z n =>
    simp only [subBlock, Bool.cond_eq_ite, Nat.beq_eq] at ht
    rw [stmtsSub, List.mem_append]
    split_ifs at ht
    · exact Or.inl (mem_stmtsOf ht)
    · exact Or.inr (mem_stmtsOf ht)
  | match_ _ arms =>
    simp only [subBlock, List.getD_eq_getElem?_getD] at ht
    rcases h : arms[c]? with _ | a
    · rw [h] at ht; simp at ht
    · rw [h, Option.getD_some] at ht
      exact stmtsOf_arms (List.mem_of_getElem? h) (mem_stmtsOf ht)
  | _ => simp [subBlock] at ht

theorem blockAt_stmts (body : List Stmt) : ∀ (up : List (ℕ × ℕ)) {t : Stmt}, t ∈ blockAt body up →
    t ∈ stmtsOf body
  | [], _, ht => mem_stmtsOf ht
  | (k, c) :: up, t, ht => by
    simp only [blockAt] at ht
    rcases Nat.lt_or_ge k (blockAt body up).length with hk | hk
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some] at ht
      exact sub_stmtsOf (blockAt_stmts body up (List.getElem_mem hk)) (subBlock_sub ht)
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hk, Option.getD_none] at ht
      have h0 : subBlock (default : Stmt) c = [] := rfl
      rw [h0] at ht
      exact absurd ht List.not_mem_nil

theorem zUp_stmts (body : List Stmt) : ∀ (up : List (ℕ × ℕ)) {t : Stmt},
    t ∈ ((zUp body up).map (·.2.2)).flatten → t ∈ stmtsOf body
  | [], _, ht => by simp [zUp] at ht
  | (k, c) :: up, t, ht => by
    simp only [zUp, List.map_cons, List.flatten_cons, List.mem_append] at ht
    rcases ht with ht | ht
    · exact blockAt_stmts body up (List.mem_of_mem_drop ht)
    · exact zUp_stmts body up ht

/-- **Every statement of an aligned position is one of the body's.** -/
theorem zok_stmts {body : List Stmt} {z : Zip} (hz : ZOk body z) {t : Stmt} (ht : t ∈ z.pos) :
    t ∈ stmtsOf body := by
  obtain ⟨hup, hcur⟩ := zOk_iff.mp hz
  simp only [Zip.pos, List.mem_append] at ht
  rcases ht with ht | ht
  · rw [hcur] at ht
    exact blockAt_stmts body _ (List.mem_of_mem_drop ht)
  · rw [hup] at ht
    exact zUp_stmts body _ ht

/-! ## A loop helper's last call -/

/-- **A loop helper's last call** is its final conditional call's, which no site matches. -/
theorem loop_last {fn : Fn} {p : Plumb} (h : loopChk fn p = true) {σ : Val} {es : List Ev} {vs : List V}
    (hw : walk σ fn.body = .ret es vs) {i : ℕ} {c : Call} (hc : (calls es)[i]? = some c)
    (hi : i + 1 = (calls es).length) : ∀ s ∈ p.sites, ¬(s.args = c.args.map (·.idx) ∧ s.rets = c.rets.map (·.idx)) := by
  unfold loopChk at h
  split at h
  case h_2 => cases h
  rename_i cc g args rpre hrev
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
    beq_eq_false_iff_ne] at h
  obtain ⟨hnr, hs⟩ := h
  have hbody : fn.body = rpre.reverse ++ [.callIf cc g args, .ret []] := by
    rw [← List.reverse_reverse fn.body, hrev]; simp
  rw [hbody, walk_append] at hw
  rcases walk_noRet (σ := σ) _ (noRetB_spec _ hnr) with ⟨es1, he1⟩ | he1
  · rw [he1] at hw
    have hw2 : walk σ [Stmt.callIf cc g args, Stmt.ret []] =
        .ret [.inK cc, if σ cc = 0 then .skip g args else .call g args []] [] := by
      rw [walk_callIf_cons, walk_ret_cons]; rfl
    rw [hw2] at hw
    simp only [Out.seq, Out.pre] at hw
    obtain ⟨rfl, -⟩ := Out.ret.inj hw
    have hcalls : calls (es1 ++ [Ev.inK cc, if σ cc = 0 then Ev.skip g args else Ev.call g args []]) =
        calls es1 ++ [⟨g, args, [], !decide (σ cc = 0)⟩] := by
      rw [calls_append']
      congr 1
      by_cases h0 : σ cc = 0
      · simp only [calls, h0, ↓reduceIte, decide_true, Bool.not_true]; rfl
      · simp only [calls, h0, ↓reduceIte, decide_false, Bool.not_false]; rfl
    rw [hcalls] at hc hi
    rw [List.length_append, List.length_singleton] at hi
    rw [List.getElem?_append_right (by omega), show i - (calls es1).length = 0 by omega] at hc
    obtain rfl := Option.some.inj hc.symm
    intro s hsm ⟨ha, hr⟩
    rcases hs s hsm with h1 | h1
    · exact h1 ha
    · exact h1 (by simpa using hr)
  · rw [he1] at hw; cases hw

end

end LeanVM.Guest.Bridge
