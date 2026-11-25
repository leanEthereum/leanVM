/-
  LeanVM.Guest.CoreMode.Post

  A function's heap guarantees at its return: each cell it promises its callers is a
  precondition's or written by an atom of its path.
-/

module

public import LeanVM.Guest.CoreMode.HeapSound
public import LeanVM.Guest.Bridge.Track
public import LeanVM.Guest.CoreLemmas

/-!
# The heap guarantees at a return

`postOk pows H post body`: no promised cell, or the heap check's pass (`atomH`, its environment and scope) over `body` up to
its `ret`, where each promised cell `(c, w)` of `post` has its witness `w` (`witOk`: a write event in
scope or a precondition, of that very cell). A branch or a `match` on the way has no `ret` in it; its
blocks are passed as the heap check does (`chkL`), for the serials, and what they write is not
used. `postOk_sound`: on the path, every event holding, each promised cell is written after the path
(`Written`).
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Exec (Trie PowTree natSeq natSeq_eq)
open LeanVM.Guest.Check (getF)

@[expose] public section

/-- A monomial's power. -/
def powC (c : CCell) : ℕ → CCell
  | 0 => ⟨[], 0⟩
  | e + 1 => (powC c e).mul c

/-- **A cell's monomial in the environment**: each base value replaced by its monomial. -/
noncomputable def substC (env : Trie CCell) (c : CCell) : CCell :=
  c.bases.foldr (fun b acc ↦ (powC ((getF env b.1).getD (baseC b.1)) b.2).mul acc) ⟨[], c.off⟩

/-- The pass over a block to its `ret`, where each promised cell has its witness; a branch or a
`match` on the way, with no `ret` in it, passed as the heap check does. -/
noncomputable def postGo (X : HX) (post : List (CCell × Wit)) : List Stmt → HSt → Bool
  | .atom a :: ss, st => match atomH X st a with
    | some st' => st'.seq fun st' ↦ postGo X post ss st'
    | none => false
  | .ite _ z n :: ss, st => Stmt.noRetList z && Stmt.noRetList n && match chkL X z st with
    | some s1 => match chkL X n (st.withN s1.n) with
      | some s2 => (st.withN s2.n).seq fun st' ↦ postGo X post ss st'
      | none => false
    | none => false
  | .match_ _ arms :: ss, st => Stmt.noRetArms arms && match chkArms X arms st with
    | some n => (st.withN n).seq fun st' ↦ postGo X post ss st'
    | none => false
  | .ret _ :: _, st => post.all fun p ↦ witOk X.pre st.sc (substC st.env p.1) p.2
  | _, _ => false

/-- **The heap guarantees' check** of a function: no promised cell, or the heap check's pass to its `ret`, each
promised cell witnessed there. -/
noncomputable def postOk (pows : PowTree) (H : HCert) (post : List (CCell × Wit)) (body : List Stmt) : Bool :=
  post.isEmpty || H.readT.seq fun R ↦ (trieFrom H.sig.pre 0 .nil).seq fun P ↦ postGo ⟨pows, R, P⟩ post body ⟨.nil, .nil, 0⟩

section

variable {σ : Val} {rd : Reader} {H : HCert} {X : HX}

theorem witOk_sound {W : K → Prop} (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ))
    (hP : ∀ k c, getF X.pre k = some c → c ∈ H.sig.pre) {sc : Trie CCell} (hs : ScOk W σ sc) {c : CCell}
    {w : Wit} (h : witOk X.pre sc c w = true) : W (c.addr σ) := by
  cases w with
  | ev n =>
    simp only [witOk] at h
    split at h
    · rename_i c' hc
      rw [← CCell.beq_eq h]
      exact (hs : ∀ n c, getF sc n = some c → W (c.addr σ)) n c' hc
    · cases h
  | pre k =>
    simp only [witOk] at h
    split at h
    · rename_i c' hc
      rw [← CCell.beq_eq h]
      exact hpre c' (hP k c' hc)
    · cases h
  | _ => simp [witOk] at h

theorem pick_noRetP {x : V} {args rets : List V} : ∀ (fs : List String) (j : ℕ) {es : List Ev}
    {vs : List V}, pick σ x args rets j fs ≠ .ret es vs
  | [], _, _, _, h => by simp [pick] at h
  | f :: fs, j, _, _, h => by
      unfold pick at h
      split_ifs at h
      exact pick_noRetP fs (j + 1) h

mutual
/-- A statement with no `ret` does not return. -/
theorem walk1_noRetP : ∀ (s : Stmt), Stmt.noRet s = true → ∀ es vs, walk1 σ s ≠ .ret es vs
  | .atom _, _, _, _, h => by simp [walk1] at h
  | .ite c z n, hn, es, vs, h => by
      simp only [Stmt.noRet, Bool.and_eq_true] at hn
      rw [walk1] at h
      split_ifs at h
      · cases hz : walk σ z <;> rw [hz] at h <;> simp only [Out.pre, reduceCtorEq] at h
        exact walk_noRetP z hn.1 _ _ hz
      · cases hz : walk σ n <;> rw [hz] at h <;> simp only [Out.pre, reduceCtorEq] at h
        exact walk_noRetP n hn.2 _ _ hz
  | .match_ x arms, hn, es, vs, h => by
      simp only [Stmt.noRet] at hn
      rw [walk1] at h
      exact walkArms_noRetP x arms hn 0 es vs h
  | .call .., _, _, _, h => by simp [walk1] at h
  | .callIf .., _, _, _, h => by simp [walk1] at h
  | .dispatch x fs args rets, _, es, vs, h => by
      rw [walk1] at h
      exact pick_noRetP fs 0 h
  | .ret _, hn, _, _, _ => by simp [Stmt.noRet] at hn

/-- A block with no `ret` does not return. -/
theorem walk_noRetP : ∀ (ss : List Stmt), Stmt.noRetList ss = true → ∀ es vs, walk σ ss ≠ .ret es vs
  | [], _, _, _, h => by simp [walk] at h
  | s :: ss, hn, es, vs, h => by
      simp only [Stmt.noRetList, Bool.and_eq_true] at hn
      rw [walk] at h
      cases h1 : walk1 σ s with
      | fall es1 =>
        rw [h1] at h
        cases h2 : walk σ ss <;> rw [h2] at h <;> simp only [Out.seq, Out.pre, reduceCtorEq] at h
        exact walk_noRetP ss hn.2 _ _ h2
      | ret es1 vs1 => exact walk1_noRetP s hn.1 es1 vs1 h1
      | stuck => rw [h1] at h; simp [Out.seq] at h

/-- Arms with no `ret` do not return. -/
theorem walkArms_noRetP (x : V) : ∀ (arms : List (List Stmt)), Stmt.noRetArms arms = true →
    ∀ (j : ℕ) es vs, walkArms σ x j arms ≠ .ret es vs
  | [], _, _, _, _, h => by simp [walkArms] at h
  | a :: as, hn, j, es, vs, h => by
      simp only [Stmt.noRetArms, Bool.and_eq_true] at hn
      unfold walkArms at h
      split_ifs at h
      · exact walk_noRetP a hn.1 _ _ h
      · exact walkArms_noRetP x as hn.2 (j + 1) _ _ h
end

/-- A statement with no `ret` before a block that returns: its events, then the block's. -/
theorem walk_cons_noRet {s : Stmt} (hn : Stmt.noRet s = true) {ss : List Stmt} {es : List Ev} {vs : List V}
    (h : walk σ (s :: ss) = .ret es vs) : ∃ es1 es2, walk σ ss = .ret es2 vs ∧ es = es1 ++ es2 := by
  rw [walk] at h
  rcases Bridge.seq_eq_ret h with ⟨es1, es2, -, h2, rfl⟩ | h1
  · exact ⟨es1, es2, h2, rfl⟩
  · exact absurd h1 (walk1_noRetP s hn es vs)

theorem val_powC (c : CCell) : ∀ e, (powC c e).val σ = c.val σ ^ e
  | 0 => by
    simp only [powC, CCell.val, prodB, addressOfIndex, pow_zero, one_mul]
    exact map_one (algebraMap K E)
  | e + 1 => by rw [powC, val_mul, val_powC c e, pow_succ]

theorem val_foldrC {env : Trie CCell} (he : EnvOk σ env) (off : ℕ) : ∀ bs : List (ℕ × ℕ),
    (bs.foldr (fun b acc ↦ (powC ((getF env b.1).getD (baseC b.1)) b.2).mul acc) ⟨[], off⟩).val σ =
      prodB σ bs * ofK (addressOfIndex off)
  | [] => rfl
  | b :: bs => by
    have hb : ((getF env b.1).getD (baseC b.1)).val σ = σ (V.n b.1) := by
      cases h : getF env b.1 with
      | none => exact val_baseC (σ := σ) b.1
      | some c' => exact (he b.1 c' h).symm
    rw [List.foldr_cons, val_mul, val_powC, val_foldrC he off bs, hb]
    simp only [prodB]
    ring

theorem val_substC {env : Trie CCell} (he : EnvOk σ env) (c : CCell) : (substC env c).val σ = c.val σ :=
  val_foldrC he c.off c.bases

theorem postGo_sound (hR: X.R = H.readT) (hP : ∀ k c, getF X.pre k = some c → c ∈ H.sig.pre)
    (hpows : X.pows.Ok) {post : List (CCell × Wit)} :
    ∀ (ss : List Stmt) {st : HSt} {W : K → Prop} {es : List Ev} {vs : List V},
      (∀ c ∈ H.sig.pre, W (c.addr σ)) → postGo X post ss st = true → EnvOk σ st.env → ScOk W σ st.sc →
      walk σ ss = .ret es vs → AllHold rd σ es → ∀ p ∈ post, W (p.1.addr σ) ∨ WL σ es (p.1.addr σ)
  | [], _, _, _, _, _, h, _, _, _, _ => by simp [postGo] at h
  | .atom a :: ss, st, W, es, vs, hpre, h, he, hs, hw, hh => by
    simp only [postGo] at h
    cases ha : atomH X st a with
    | none => rw [ha] at h; cases h
    | some st1 =>
      rw [ha] at h
      simp only [HSt.seq_eq] at h
      rw [Bridge.walk_atom_cons] at hw
      obtain ⟨es', hw', rfl⟩ := Bridge.pre_eq_ret hw
      obtain ⟨-, he1, hs1⟩ := atomH_ok hR hP hpows hpre ha he hs (hh _ List.mem_cons_self)
      intro p hp
      rcases postGo_sound hR hP hpows ss (fun c hc ↦ Or.inl (hpre c hc)) h he1 hs1 hw'
        (fun e he ↦ hh e (List.mem_cons_of_mem _ he)) p hp with (hw1 | hw1) | hw1
      · exact Or.inl hw1
      · exact Or.inr ⟨a, List.mem_cons_self, hw1⟩
      · obtain ⟨b, hb, hx⟩ := (hw1 : ∃ b, Ev.atom b ∈ es' ∧ Writes σ b (p.1.addr σ))
        exact Or.inr ⟨b, List.mem_cons_of_mem _ hb, hx⟩
  | .ret _ :: _, st, W, es, vs, hpre, h, he, hs, _, _ => by
    simp only [postGo, List.all_eq_true] at h
    intro p hp
    have := witOk_sound hpre hP hs (h p hp)
    rw [CCell.addr, val_substC he] at this
    exact Or.inl this
  | .ite c z n :: ss, st, W, es, vs, hpre, h, he, hs, hw, hh => by
    simp only [postGo, Bool.and_eq_true] at h
    obtain ⟨⟨hz, hn⟩, h⟩ := h
    have hnr : Stmt.noRet (.ite c z n) = true := by simp [Stmt.noRet, hz, hn]
    obtain ⟨es1, es2, hw2, rfl⟩ := walk_cons_noRet hnr hw
    split at h
    · split at h
      · rw [HSt.seq_eq] at h
        intro p hp
        rcases postGo_sound hR hP hpows ss hpre h he hs hw2 (fun e he' ↦ hh e (List.mem_append_right _ he')) p hp
          with h1 | h1
        · exact Or.inl h1
        · exact Or.inr (wl_append h1)
      · cases h
    · cases h
  | .match_ x arms :: ss, st, W, es, vs, hpre, h, he, hs, hw, hh => by
    simp only [postGo, Bool.and_eq_true] at h
    obtain ⟨ha, h⟩ := h
    have hnr : Stmt.noRet (.match_ x arms) = true := by simp [Stmt.noRet, ha]
    obtain ⟨es1, es2, hw2, rfl⟩ := walk_cons_noRet hnr hw
    split at h
    · rw [HSt.seq_eq] at h
      intro p hp
      rcases postGo_sound hR hP hpows ss hpre h he hs hw2 (fun e he' ↦ hh e (List.mem_append_right _ he')) p hp
        with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (wl_append h1)
    · cases h
  | .call .. :: _, _, _, _, _, _, h, _, _, _, _ => by simp [postGo] at h
  | .callIf .. :: _, _, _, _, _, _, h, _, _, _, _ => by simp [postGo] at h
  | .dispatch .. :: _, _, _, _, _, _, h, _, _, _, _ => by simp [postGo] at h

/-- **The heap guarantees are written**: on a path of a function passing `postOk`
that returns, every event holding, each promised cell is a precondition's or written by an atom of
the path. -/
theorem postOk_sound {pows : PowTree} (hpw : pows.Ok) {post : List (CCell × Wit)} {body : List Stmt}
    (hok : postOk pows H post body = true) {es : List Ev} {vs : List V}
    (hw : walk σ body = .ret es vs) (hh : ∀ e ∈ es, e.Holds rd σ) : ∀ p ∈ post, Written H σ es (p.1.addr σ) := by
  unfold postOk at hok
  intro p hp
  rcases Bool.or_eq_true_iff.mp hok with hok | hok
  · exact absurd hp (List.isEmpty_iff.mp hok ▸ List.not_mem_nil)
  rw [Trie.seq_eq, Trie.seq_eq] at hok
  rcases postGo_sound (X := ⟨pows, H.readT, trieFrom H.sig.pre 0 .nil⟩) (H := H) (rd := rd) rfl
    (fun k c h ↦ (getF_trieFrom _ _ _ h).resolve_right (by simp [getF_nil])) hpw body
    (W := fun x ↦ ∃ c ∈ H.sig.pre, c.addr σ = x) (fun c hc ↦ ⟨c, hc, rfl⟩) hok envOk_nil
    (fun n c h ↦ by simp [getF_nil] at h) hw hh p hp with h | h
  · exact Or.inl h
  · exact Or.inr h

end

end

end LeanVM.Guest.CoreMode
