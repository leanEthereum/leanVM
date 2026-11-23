/-
  LeanVM.Guest.Memory.SelArm

  A body at an arm of a selector: every `match` and `dispatch` on it taking that arm, walked as the
  body on every path that does not get stuck.
-/

module

public import LeanVM.Guest.Memory.Tree
public import LeanVM.Guest.Renumber

/-!
# A body at an arm of a selector

`selL x r ss`: the block with each `match` on `V.n x` replaced by its arm `r`'s block, inline, and each `dispatch` on it
by the call of its callee `r`, where there is one (by the recursor, for the kernel). `walk_sel`: where `r` is the only
index below `n` the selector's word can be the `g`-power of and every `match` and `dispatch` on it has at most `n` arms,
the block at arm `r` walks as the block, unless that is stuck; `exists_sel` gives such an `r` for every valuation. A
check of a body may so be split at a selector (`selSplit`): a check of each arm's body is one of the body's paths
(`selSplit_sound`). The core route's heap check (`CoreMode.heapOkC`) and the static weight checker (`Memory.chkFn`)
split so.
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

/-- The value `v` is `V.n x`. -/
def selIs (x : ℕ) (v : V) : Bool := decide (v = V.n x)

/-- **A statement at arm `r` of the selector `V.n x`**, by the recursor: a `match` on it its arm `r`'s block, inline, a
`dispatch` on it the call of its callee `r`, where there is one; nested blocks likewise. -/
noncomputable def selS (x r : ℕ) : Stmt → List Stmt :=
  Stmt.rec (motive_1 := fun _ ↦ List Stmt) (motive_2 := fun _ ↦ List Stmt) (motive_3 := fun _ ↦ List (List Stmt))
    (fun a ↦ [.atom a]) (fun c _ _ rz rn ↦ [.ite c rz rn])
    (fun y _ ra ↦ bif selIs x y && Nat.blt r ra.length then ra.getD r [] else [.match_ y ra])
    (fun f args rets ↦ [.call f args rets]) (fun c f args ↦ [.callIf c f args])
    (fun y fs args rets ↦ bif selIs x y && Nat.blt r fs.length then [.call (fs.getD r "") args rets]
      else [.dispatch y fs args rets])
    (fun vs ↦ [.ret vs]) [] (fun _ _ a b ↦ a ++ b) [] (fun _ _ a b ↦ a :: b)

/-- A block at arm `r` (`selS`). -/
noncomputable def selL (x r : ℕ) : List Stmt → List Stmt :=
  Stmt.rec_1 (motive_1 := fun _ ↦ List Stmt) (motive_2 := fun _ ↦ List Stmt) (motive_3 := fun _ ↦ List (List Stmt))
    (fun a ↦ [.atom a]) (fun c _ _ rz rn ↦ [.ite c rz rn])
    (fun y _ ra ↦ bif selIs x y && Nat.blt r ra.length then ra.getD r [] else [.match_ y ra])
    (fun f args rets ↦ [.call f args rets]) (fun c f args ↦ [.callIf c f args])
    (fun y fs args rets ↦ bif selIs x y && Nat.blt r fs.length then [.call (fs.getD r "") args rets]
      else [.dispatch y fs args rets])
    (fun vs ↦ [.ret vs]) [] (fun _ _ a b ↦ a ++ b) [] (fun _ _ a b ↦ a :: b)

/-- Arms at arm `r` (`selS`). -/
noncomputable def selA (x r : ℕ) : List (List Stmt) → List (List Stmt) :=
  Stmt.rec_2 (motive_1 := fun _ ↦ List Stmt) (motive_2 := fun _ ↦ List Stmt) (motive_3 := fun _ ↦ List (List Stmt))
    (fun a ↦ [.atom a]) (fun c _ _ rz rn ↦ [.ite c rz rn])
    (fun y _ ra ↦ bif selIs x y && Nat.blt r ra.length then ra.getD r [] else [.match_ y ra])
    (fun f args rets ↦ [.call f args rets]) (fun c f args ↦ [.callIf c f args])
    (fun y fs args rets ↦ bif selIs x y && Nat.blt r fs.length then [.call (fs.getD r "") args rets]
      else [.dispatch y fs args rets])
    (fun vs ↦ [.ret vs]) [] (fun _ _ a b ↦ a ++ b) [] (fun _ _ a b ↦ a :: b)

/-- **Every `match` and `dispatch` on `V.n x` has at most `n` arms**, by the recursor. -/
noncomputable def armLeS (x n : ℕ) : Stmt → Bool :=
  Stmt.rec (motive_1 := fun _ ↦ Bool) (motive_2 := fun _ ↦ Bool) (motive_3 := fun _ ↦ Bool)
    (fun _ ↦ true) (fun _ _ _ rz rn ↦ rz && rn) (fun y arms ra ↦ (!selIs x y || Nat.ble arms.length n) && ra)
    (fun _ _ _ ↦ true) (fun _ _ _ ↦ true) (fun y fs _ _ ↦ !selIs x y || Nat.ble fs.length n) (fun _ ↦ true) true
    (fun _ _ a b ↦ a && b) true (fun _ _ a b ↦ a && b)

/-- A block's (`armLeS`). -/
noncomputable def armLeL (x n : ℕ) : List Stmt → Bool :=
  Stmt.rec_1 (motive_1 := fun _ ↦ Bool) (motive_2 := fun _ ↦ Bool) (motive_3 := fun _ ↦ Bool)
    (fun _ ↦ true) (fun _ _ _ rz rn ↦ rz && rn) (fun y arms ra ↦ (!selIs x y || Nat.ble arms.length n) && ra)
    (fun _ _ _ ↦ true) (fun _ _ _ ↦ true) (fun y fs _ _ ↦ !selIs x y || Nat.ble fs.length n) (fun _ ↦ true) true
    (fun _ _ a b ↦ a && b) true (fun _ _ a b ↦ a && b)

/-- Arms' (`armLeS`). -/
noncomputable def armLeA (x n : ℕ) : List (List Stmt) → Bool :=
  Stmt.rec_2 (motive_1 := fun _ ↦ Bool) (motive_2 := fun _ ↦ Bool) (motive_3 := fun _ ↦ Bool)
    (fun _ ↦ true) (fun _ _ _ rz rn ↦ rz && rn) (fun y arms ra ↦ (!selIs x y || Nat.ble arms.length n) && ra)
    (fun _ _ _ ↦ true) (fun _ _ _ ↦ true) (fun y fs _ _ ↦ !selIs x y || Nat.ble fs.length n) (fun _ ↦ true) true
    (fun _ _ a b ↦ a && b) true (fun _ _ a b ↦ a && b)

/-- The first top-level `match` on a value `V.n x`: `x` and its arms. -/
def topSel : List Stmt → Option (ℕ × ℕ)
  | [] => none
  | .match_ y arms :: ss => bif selIs y.idx y then some (y.idx, arms.length) else topSel ss
  | _ :: ss => topSel ss

/-- **A check of a body split at its first top-level selector**: of `n` arms, `0 < n < 2^62`, every `match` and
`dispatch` on it of at most `n` arms, `chk` of each arm's body. -/
noncomputable def selSplit (body : List Stmt) (chk : List Stmt → Bool) : Bool :=
  match topSel body with
  | some (x, n) => Nat.blt 0 n && Nat.blt n 4611686018427387904 && armLeL x n body &&
      (List.range n).all fun r ↦ chk (selL x r body)
  | none => false

end

@[expose] public section

/-- An outcome agrees with another, unless that one is stuck. -/
def OutAg (o' o : Out) : Prop := o' = o ∨ o = .stuck

theorem outAg_refl (o : Out) : OutAg o o := Or.inl rfl

theorem outAg_pre {o' o : Out} (es : List Ev) (h : OutAg o' o) : OutAg (o'.pre es) (o.pre es) := by
  rcases h with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem outAg_seq {a' a b' b : Out} (ha : OutAg a' a) (hb : OutAg b' b) : OutAg (a'.seq b') (a.seq b) := by
  rcases ha with rfl | rfl
  · cases a' with
    | fall es => exact outAg_pre es hb
    | ret es vs => exact Or.inl rfl
    | stuck => exact Or.inl rfl
  · exact Or.inr rfl

theorem Out.seq_assoc : ∀ (o k l : Out), (o.seq k).seq l = o.seq (k.seq l)
  | .fall es, .fall es', l => by cases l <;> simp [Out.seq, Out.pre, List.append_assoc]
  | .fall es, .ret es' vs, l => by simp [Out.seq, Out.pre]
  | .fall es, .stuck, l => by simp [Out.seq, Out.pre]
  | .ret es vs, k, l => by simp [Out.seq]
  | .stuck, k, l => by simp [Out.seq]

theorem walk_append {σ : Val} : ∀ (l l' : List Stmt), walk σ (l ++ l') = (walk σ l).seq (walk σ l')
  | [], l' => by
      rw [List.nil_append, walk]
      cases walk σ l' <;> simp [Out.seq, Out.pre]
  | s :: l, l' => by rw [List.cons_append, walk, walk, walk_append l l', Out.seq_assoc]

theorem walk_singleC (σ : Val) (s : Stmt) : walk σ [s] = walk1 σ s := by
  rw [walk, walk]
  cases walk1 σ s <;> simp [Out.seq, Out.pre]

theorem selIs_eq {x : ℕ} {v : V} (h : selIs x v = true) : v = V.n x := of_decide_eq_true h

theorem selA_length (x r : ℕ) : ∀ arms : List (List Stmt), (selA x r arms).length = arms.length
  | [] => rfl
  | _ :: as => by
    show (_ :: selA x r as).length = _
    rw [List.length_cons, List.length_cons, selA_length x r as]

theorem selA_getD (x r : ℕ) : ∀ (arms : List (List Stmt)) (i : ℕ), (selA x r arms).getD i [] = selL x r (arms.getD i [])
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: as, i + 1 => selA_getD x r as i

section Split

variable {σ : Val}

/-- The first arm from `j` whose `g`-power the selector's word is: none, or arm `r`'s, `r` the only index among
them it can be. -/
theorem walkArms_sel {x r : ℕ} : ∀ (arms : List (List Stmt)) (j : ℕ),
    (∀ i, j ≤ i → i < j + arms.length → σ (V.n x) = ofK (addressOfIndex i) → i = r) →
    walkArms σ (V.n x) j arms = .stuck ∨ (j ≤ r ∧ walkArms σ (V.n x) j arms = walk σ (arms.getD (r - j) []))
  | [], j, _ => Or.inl (by rw [walkArms])
  | a :: as, j, hu => by
    rw [walkArms]
    split_ifs with h
    · have := hu j le_rfl (by simp) h
      subst this
      right; simp
    · rcases walkArms_sel as (j + 1) (fun i h1 h2 h3 ↦ hu i (by omega) (by simp at h2 ⊢; omega) h3) with
        h' | ⟨hj, h'⟩
      · exact Or.inl h'
      · right
        refine ⟨by omega, ?_⟩
        rw [h', show r - j = (r - (j + 1)) + 1 by omega]
        rfl

/-- The same for a fused dispatch: none, or the call of callee `r`. -/
theorem pick_sel {x r : ℕ} {args rets : List V} : ∀ (fs : List String) (j : ℕ),
    (∀ i, j ≤ i → i < j + fs.length → σ (V.n x) = ofK (addressOfIndex i) → i = r) →
    pick σ (V.n x) args rets j fs = .stuck ∨
      (j ≤ r ∧ pick σ (V.n x) args rets j fs = .fall [.call (fs.getD (r - j) "") args rets])
  | [], j, _ => Or.inl (by rw [pick])
  | f :: fs, j, hu => by
    rw [pick]
    split_ifs with h
    · have := hu j le_rfl (by simp) h
      subst this
      right; simp
    · rcases pick_sel fs (j + 1) (fun i h1 h2 h3 ↦ hu i (by omega) (by simp at h2 ⊢; omega) h3) with
        h' | ⟨hj, h'⟩
      · exact Or.inl h'
      · right
        refine ⟨by omega, ?_⟩
        rw [h', show r - j = (r - (j + 1)) + 1 by omega]
        rfl

mutual
/-- **A statement at arm `r` walks as the statement**, unless that is stuck: `r` the only index below `n` the
selector's word can be the `g`-power of, every `match` and `dispatch` on it of at most `n` arms. -/
theorem walk1_sel {x r n : ℕ} (hu : ∀ i < n, σ (V.n x) = ofK (addressOfIndex i) → i = r) :
    ∀ s : Stmt, armLeS x n s = true → OutAg (walk σ (selS x r s)) (walk1 σ s)
  | .atom a, _ => by
    rw [show selS x r (.atom a) = [.atom a] from rfl, walk_singleC]; exact outAg_refl _
  | .ite c z m, h => by
    have h' : (armLeL x n z && armLeL x n m) = true := h
    simp only [Bool.and_eq_true] at h'
    rw [show selS x r (.ite c z m) = [.ite c (selL x r z) (selL x r m)] from rfl, walk_singleC]
    simp only [walk1]
    split_ifs
    · exact outAg_pre _ (walk_sel hu z h'.1)
    · exact outAg_pre _ (walk_sel hu m h'.2)
  | .match_ y arms, h => by
    have h' : ((!selIs x y || Nat.ble arms.length n) && armLeA x n arms) = true := h
    simp only [Bool.and_eq_true] at h'
    obtain ⟨hl, ha⟩ := h'
    have IH := walkA_sel hu arms ha
    show OutAg (walk σ (bif selIs x y && Nat.blt r (selA x r arms).length then (selA x r arms).getD r []
      else [.match_ y (selA x r arms)])) (walkArms σ y 0 arms)
    rw [selA_length]
    cases hs : selIs x y
    · simp only [Bool.false_and, Bool.cond_false]
      rw [walk_singleC]; exact IH.1 y 0
    · cases hr : Nat.blt r arms.length
      · simp only [Bool.and_false, Bool.cond_false]
        rw [walk_singleC]; exact IH.1 y 0
      · simp only [Bool.and_self, Bool.cond_true]
        have hy := selIs_eq hs
        subst hy
        simp only [hs, Bool.not_true, Bool.false_or, Nat.ble_eq] at hl
        rcases walkArms_sel (σ := σ) (r := r) arms 0 (fun i _ h2 h3 ↦ hu i (by omega) h3) with h0 | ⟨-, h0⟩
        · exact Or.inr h0
        · rw [h0, selA_getD, Nat.sub_zero]; exact IH.2 r
  | .call f args rets, _ => by
    rw [show selS x r (.call f args rets) = [.call f args rets] from rfl, walk_singleC]; exact outAg_refl _
  | .callIf c f args, _ => by
    rw [show selS x r (.callIf c f args) = [.callIf c f args] from rfl, walk_singleC]; exact outAg_refl _
  | .dispatch y fs args rets, h => by
    have hl : (!selIs x y || Nat.ble fs.length n) = true := h
    show OutAg (walk σ (bif selIs x y && Nat.blt r fs.length then [.call (fs.getD r "") args rets]
      else [.dispatch y fs args rets])) (pick σ y args rets 0 fs)
    cases hs : selIs x y
    · simp only [Bool.false_and, Bool.cond_false]
      rw [walk_singleC]; exact outAg_refl _
    · cases hr : Nat.blt r fs.length
      · simp only [Bool.and_false, Bool.cond_false]
        rw [walk_singleC]; exact outAg_refl _
      · simp only [Bool.and_self, Bool.cond_true]
        have hy := selIs_eq hs
        subst hy
        simp only [hs, Bool.not_true, Bool.false_or, Nat.ble_eq] at hl
        rw [walk_singleC]
        rcases pick_sel (σ := σ) (r := r) (args := args) (rets := rets) fs 0
          (fun i _ h2 h3 ↦ hu i (by omega) h3) with h0 | ⟨-, h0⟩
        · exact Or.inr h0
        · rw [h0, Nat.sub_zero]; exact Or.inl rfl
  | .ret vs, _ => by
    rw [show selS x r (.ret vs) = [.ret vs] from rfl, walk_singleC]; exact outAg_refl _

/-- **A block at arm `r` walks as the block**, unless that is stuck (`walk1_sel`). -/
theorem walk_sel {x r n : ℕ} (hu : ∀ i < n, σ (V.n x) = ofK (addressOfIndex i) → i = r) :
    ∀ ss : List Stmt, armLeL x n ss = true → OutAg (walk σ (selL x r ss)) (walk σ ss)
  | [], _ => outAg_refl _
  | s :: ss, h => by
    have h' : (armLeS x n s && armLeL x n ss) = true := h
    simp only [Bool.and_eq_true] at h'
    rw [show selL x r (s :: ss) = selS x r s ++ selL x r ss from rfl, walk_append, walk]
    exact outAg_seq (walk1_sel hu s h'.1) (walk_sel hu ss h'.2)

/-- Arms at arm `r` (`walk1_sel`): their walks from any index, and each arm's. -/
theorem walkA_sel {x r n : ℕ} (hu : ∀ i < n, σ (V.n x) = ofK (addressOfIndex i) → i = r) :
    ∀ arms : List (List Stmt), armLeA x n arms = true →
      (∀ y j, OutAg (walkArms σ y j (selA x r arms)) (walkArms σ y j arms)) ∧
        ∀ i, OutAg (walk σ (selL x r (arms.getD i []))) (walk σ (arms.getD i []))
  | [], _ => ⟨fun y j ↦ outAg_refl _, fun i ↦ outAg_refl _⟩
  | a :: as, h => by
    have h' : (armLeL x n a && armLeA x n as) = true := h
    simp only [Bool.and_eq_true] at h'
    have IHa := walk_sel hu a h'.1
    have IHs := walkA_sel hu as h'.2
    refine ⟨fun y j ↦ ?_, fun i ↦ ?_⟩
    · rw [show selA x r (a :: as) = selL x r a :: selA x r as from rfl, walkArms, walkArms]
      split_ifs
      · exact IHa
      · exact IHs.1 y (j + 1)
    · cases i with
      | zero => exact IHa
      | succ i => exact IHs.2 i
end

/-- **An arm for every valuation**: the only index below `n` the selector's word is the `g`-power of, or `0` if
none is. -/
theorem exists_sel (x : ℕ) {n : ℕ} (h0 : 0 < n) (hn : n < 4611686018427387904) :
    ∃ r < n, ∀ i < n, σ (V.n x) = ofK (addressOfIndex i) → i = r := by
  by_cases h : ∃ i < n, σ (V.n x) = ofK (addressOfIndex i)
  · obtain ⟨r, hr, hx⟩ := h
    refine ⟨r, hr, fun i hi hxi ↦ ?_⟩
    have hc : 4611686018427387904 < 2 ^ 64 - 1 := by norm_num
    have he := congrArg logG (hxi.symm.trans hx)
    rwa [logG_spec (lt_trans (lt_trans hi hn) hc), logG_spec (lt_trans (lt_trans hr hn) hc)] at he
  · exact ⟨0, h0, fun i hi hxi ↦ absurd ⟨i, hi, hxi⟩ h⟩

/-- **A split check is one of the body's paths**: on a returning path, some arm's body walks as the body, and passes
`chk`. -/
theorem selSplit_sound {body : List Stmt} {chk : List Stmt → Bool} (h : selSplit body chk = true) {es : List Ev}
    {vs : List V} (hw : walk σ body = .ret es vs) : ∃ body', chk body' = true ∧ walk σ body' = .ret es vs := by
  unfold selSplit at h
  split at h
  · rename_i x n _
    simp only [Bool.and_eq_true, Nat.blt_eq, List.all_eq_true, List.mem_range] at h
    obtain ⟨⟨⟨h0, hn⟩, hle⟩, hall⟩ := h
    obtain ⟨r, hr, hu⟩ := exists_sel (σ := σ) x h0 hn
    refine ⟨selL x r body, hall r hr, ?_⟩
    rcases walk_sel hu body hle with h' | h'
    · rw [h', hw]
    · rw [hw] at h'; cases h'
  · cases h

end Split

theorem selSplit_mono {body : List Stmt} {c1 c2 : List Stmt → Bool} (hc : ∀ b, c1 b = true → c2 b = true)
    (h : selSplit body c1 = true) : selSplit body c2 = true := by
  unfold selSplit at h ⊢
  split at h
  · simp only [Bool.and_eq_true, List.all_eq_true] at h ⊢
    exact ⟨h.1, fun r hr ↦ hc _ (h.2 r hr)⟩
  · cases h

end

end LeanVM.Guest.Memory
