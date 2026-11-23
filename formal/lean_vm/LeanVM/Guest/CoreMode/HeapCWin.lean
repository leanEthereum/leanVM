/-
  LeanVM.Guest.CoreMode.HeapCWin

  The heap check of a long loop helper in windows: the pass over consecutive slices of the body,
  each from a stated state to a stated state, assembled into `heapOkC`.
-/

module

public import LeanVM.Guest.CoreMode.HeapC
public import LeanVM.Guest.Memory.StaticCut

/-!
# The heap check in windows

`heapOkC` is one kernel evaluation over the whole body; for a body of many large `match`es
(`main_loop2`'s) that evaluation alone runs past the build's memory cap. The pass is linear: over `ss₁ ++ ss₂`, `ss₁` without a
top-level `ret`, it is the pass over `ss₁` then over `ss₂` from where it ended (`chkC_append`). So the body's
pass splits at cut points `a₀ = 0 < a₁ < … < aₙ`, with the states `Sᵢ` the pass reaches there stated as
literals: each window (`winOk`) decides that the pass over the statements `aᵢ` to `aᵢ₊₁ - 1` goes from `Sᵢ`
to `Sᵢ₊₁` (`CSt` with `DecidableEq`), that they contain no `ret`, and that they name no ghost value. The head
(`headOk`) decides the rest of `heapOkC` for a loop helper: the parameters, the shape of the tail, the entry
state `S₀`; the tail (`tailOkW`), the tail call and the guarantees at `ret []` from `Sₙ`. `heapOkC_of_wins`
assembles them.
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Exec (Trie PowTree natSeq)
open LeanVM.Guest.Check (getF setF)

@[expose] public section

/-! ## Equality of states, for the kernel -/

/-- Two tries equal, by the recursor (the derived `DecidableEq` does not reduce in the kernel). -/
noncomputable def trieEq {α : Type} [DecidableEq α] (a : Trie α) : Trie α → Bool :=
  Trie.rec (motive := fun _ ↦ Trie α → Bool)
    (fun b ↦ Trie.casesOn (motive := fun _ ↦ Bool) b true fun _ _ _ ↦ false)
    (fun v _ _ il ir b ↦ Trie.casesOn (motive := fun _ ↦ Bool) b false fun v' l' r' ↦
      decide (v = v') && il l' && ir r') a

theorem trieEq_iff {α : Type} [DecidableEq α] : ∀ (a b : Trie α), trieEq a b = true ↔ a = b
  | .nil, .nil => by simp [trieEq]
  | .nil, .node _ _ _ => by simp [trieEq]
  | .node _ _ _, .nil => by simp [trieEq]
  | .node v l r, .node v' l' r' => by
    have hl := trieEq_iff l l'
    have hr := trieEq_iff r r'
    simp only [trieEq] at hl hr ⊢
    simp only [Bool.and_eq_true, decide_eq_true_eq, hl, hr, Trie.node.injEq, and_assoc]

noncomputable section

instance trieDecEq {α : Type} [DecidableEq α] : DecidableEq (Trie α) := fun a b ↦
  decidable_of_iff _ (trieEq_iff a b)

deriving instance DecidableEq for PRun
deriving instance DecidableEq for CdA
deriving instance DecidableEq for CdE
deriving instance DecidableEq for CSt

end

/-- **The context `heapOkC` builds** for `f` and its certificate. -/
noncomputable def cxOf (pows : PowTree) (sigOf : String → HSig) (f : Fn) (H : HCert) : CX :=
  ⟨pows, H.readT, trieFrom H.sig.pre 0 .nil, trieFrom H.calls 0 .nil, trieFrom H.rets 0 .nil,
    trieFrom H.res 0 .nil, keysT H.divs .nil, keysT H.hvs .nil, H.gargs, sigOf, H.sig, f.params, [],
    keysT H.eqs .nil, H.fas, H.ders⟩

/-- `k (cxOf pows sigOf f H)`, the context's tries evaluated first (as `heapOkC` does). -/
noncomputable def withCx {β : Type} (pows : PowTree) (sigOf : String → HSig) (f : Fn) (H : HCert) (k : CX → β) :
    β :=
  H.readT.seq fun R ↦ (trieFrom H.sig.pre 0 .nil).seq fun P ↦ (trieFrom H.calls 0 .nil).seq fun C ↦
    (trieFrom H.rets 0 .nil).seq fun T ↦ (trieFrom H.res 0 .nil).seq fun RS ↦ (keysT H.divs .nil).seq fun DV ↦
      (keysT H.hvs .nil).seq fun HV ↦ (keysT H.eqs .nil).seq fun EQ ↦
        k ⟨pows, R, P, C, T, RS, DV, HV, H.gargs, sigOf, H.sig, f.params, [], EQ, H.fas, H.ders⟩

theorem withCx_eq {β : Type} (pows : PowTree) (sigOf : String → HSig) (f : Fn) (H : HCert) (k : CX → β) :
    withCx pows sigOf f H k = k (cxOf pows sigOf f H) := by
  simp only [withCx, Trie.seq_eq, cxOf]


/-! ## Blocks by the recursors -/

/-- A value below the words at cells' and the ghosts' numbers (`DB`). -/
def okV (v : V) : Bool := Nat.blt v.idx DB

/-- No value a block names is a ghost's. -/
def noGhostL (ss : List Stmt) : Bool := (Stmt.usesList ss ++ Stmt.tmpsList ss).all okV

/-- Every value below the ghosts', by the recursor. -/
noncomputable def allV (l : List V) : Bool := List.rec (motive := fun _ ↦ Bool) true (fun v _ r ↦ okV v && r) l

theorem allV_eq (l : List V) : allV l = l.all okV := by
  induction l with
  | nil => rfl
  | cons v l ih => simp only [allV] at ih ⊢; simp only [List.all_cons, ih]

/-- An atom's values below the ghosts'. -/
noncomputable def atomOkV : Atom → Bool
  | .keccak ins outs _ _ => allV ins && allV outs
  | a => allV (atomUses a ++ atomTmps a)

theorem atomOkV_eq (a : Atom) : atomOkV a = ((atomUses a).all okV && (atomTmps a).all okV) := by
  cases a <;> simp [atomOkV, allV_eq, atomUses, atomTmps, List.all_append, Bool.and_assoc]

/-- No `ret` in a statement, by the recursor (`Memory.Stmt.noRet`, in the form the kernel reduces fast). -/
noncomputable def nrS : Stmt → Bool :=
  Stmt.rec (motive_1 := fun _ ↦ Bool) (motive_2 := fun _ ↦ Bool) (motive_3 := fun _ ↦ Bool)
    (fun _ ↦ true) (fun _ _ _ rz rn ↦ rz && rn) (fun _ _ ra ↦ ra) (fun _ _ _ ↦ true) (fun _ _ _ ↦ true)
    (fun _ _ _ _ ↦ true) (fun _ ↦ false) true (fun _ _ a b ↦ a && b) true (fun _ _ a b ↦ a && b)

/-- No `ret` in a block, by the recursor. -/
noncomputable def nrL : List Stmt → Bool :=
  Stmt.rec_1 (motive_1 := fun _ ↦ Bool) (motive_2 := fun _ ↦ Bool) (motive_3 := fun _ ↦ Bool)
    (fun _ ↦ true) (fun _ _ _ rz rn ↦ rz && rn) (fun _ _ ra ↦ ra) (fun _ _ _ ↦ true) (fun _ _ _ ↦ true)
    (fun _ _ _ _ ↦ true) (fun _ ↦ false) true (fun _ _ a b ↦ a && b) true (fun _ _ a b ↦ a && b)

/-- No `ret` in arms, by the recursor. -/
noncomputable def nrA : List (List Stmt) → Bool :=
  Stmt.rec_2 (motive_1 := fun _ ↦ Bool) (motive_2 := fun _ ↦ Bool) (motive_3 := fun _ ↦ Bool)
    (fun _ ↦ true) (fun _ _ _ rz rn ↦ rz && rn) (fun _ _ ra ↦ ra) (fun _ _ _ ↦ true) (fun _ _ _ ↦ true)
    (fun _ _ _ _ ↦ true) (fun _ ↦ false) true (fun _ _ a b ↦ a && b) true (fun _ _ a b ↦ a && b)

/-- No ghost value in a statement, by the recursor. -/
noncomputable def ngS : Stmt → Bool :=
  Stmt.rec (motive_1 := fun _ ↦ Bool) (motive_2 := fun _ ↦ Bool) (motive_3 := fun _ ↦ Bool)
    (fun a ↦ atomOkV a) (fun c _ _ rz rn ↦ okV c && rz && rn)
    (fun x _ ra ↦ okV x && ra) (fun _ args rets ↦ allV args && allV rets) (fun c _ args ↦ okV c && allV args)
    (fun x _ args rets ↦ okV x && allV args && allV rets) (fun vs ↦ allV vs) true (fun _ _ a b ↦ a && b)
    true (fun _ _ a b ↦ a && b)

/-- No ghost value in a block, by the recursor. -/
noncomputable def ngL : List Stmt → Bool :=
  Stmt.rec_1 (motive_1 := fun _ ↦ Bool) (motive_2 := fun _ ↦ Bool) (motive_3 := fun _ ↦ Bool)
    (fun a ↦ atomOkV a) (fun c _ _ rz rn ↦ okV c && rz && rn)
    (fun x _ ra ↦ okV x && ra) (fun _ args rets ↦ allV args && allV rets) (fun c _ args ↦ okV c && allV args)
    (fun x _ args rets ↦ okV x && allV args && allV rets) (fun vs ↦ allV vs) true (fun _ _ a b ↦ a && b)
    true (fun _ _ a b ↦ a && b)

/-- No ghost value in arms, by the recursor. -/
noncomputable def ngA : List (List Stmt) → Bool :=
  Stmt.rec_2 (motive_1 := fun _ ↦ Bool) (motive_2 := fun _ ↦ Bool) (motive_3 := fun _ ↦ Bool)
    (fun a ↦ atomOkV a) (fun c _ _ rz rn ↦ okV c && rz && rn)
    (fun x _ ra ↦ okV x && ra) (fun _ args rets ↦ allV args && allV rets) (fun c _ args ↦ okV c && allV args)
    (fun x _ args rets ↦ okV x && allV args && allV rets) (fun vs ↦ allV vs) true (fun _ _ a b ↦ a && b)
    true (fun _ _ a b ↦ a && b)

theorem nrL_eq (ss : List Stmt) : nrL ss = Memory.Stmt.noRetListS ss :=
  Stmt.rec_1 (motive_1 := fun s ↦ nrS s = Memory.Stmt.noRet s) (motive_2 := fun ss ↦ nrL ss = Memory.Stmt.noRetListS ss)
    (motive_3 := fun as ↦ nrA as = Memory.Stmt.noRetArms as)
    (fun _ ↦ by simp [nrS, Memory.Stmt.noRet])
    (fun _ _ _ hz hn ↦ by
      show (nrL _ && nrL _) = _
      rw [hz, hn]; simp [Memory.Stmt.noRet])
    (fun _ _ ha ↦ by
      show (nrA _) = _
      rw [ha]; simp [Memory.Stmt.noRet])
    (fun _ _ _ ↦ by simp [nrS, Memory.Stmt.noRet]) (fun _ _ _ ↦ by simp [nrS, Memory.Stmt.noRet])
    (fun _ _ _ _ ↦ by simp [nrS, Memory.Stmt.noRet]) (fun _ ↦ by simp [nrS, Memory.Stmt.noRet])
    (by simp [nrL, Memory.Stmt.noRetListS])
    (fun _ _ hs hl ↦ by
      show (nrS _ && nrL _) = _
      rw [hs, hl]; simp [Memory.Stmt.noRetListS])
    (by simp [nrA, Memory.Stmt.noRetArms])
    (fun _ _ hs hl ↦ by
      show (nrL _ && nrA _) = _
      rw [hs, hl]; simp [Memory.Stmt.noRetArms]) ss

theorem ngL_eq (ss : List Stmt) : ngL ss = noGhostL ss := by
  have h := Stmt.rec_1 (motive_1 := fun s ↦ ngS s = ((Stmt.uses s).all okV && (Stmt.tmps s).all okV))
    (motive_2 := fun ss ↦ ngL ss = ((Stmt.usesList ss).all okV && (Stmt.tmpsList ss).all okV))
    (motive_3 := fun as ↦ ngA as = ((Stmt.usesArms as).all okV && (Stmt.tmpsArms as).all okV))
    (fun _ ↦ by simp [ngS, Stmt.uses, Stmt.tmps, atomOkV_eq])
    (fun _ _ _ hz hn ↦ by
      show (okV _ && ngL _ && ngL _) = _
      rw [hz, hn]; simp only [Stmt.uses, Stmt.tmps, List.all_cons, List.all_append]
      cases okV _ <;> cases (Stmt.usesList _).all okV <;> cases (Stmt.usesList _).all okV <;>
        cases (Stmt.tmpsList _).all okV <;> cases (Stmt.tmpsList _).all okV <;> rfl)
    (fun _ _ ha ↦ by
      show (okV _ && ngA _) = _
      rw [ha]; simp only [Stmt.uses, Stmt.tmps, List.all_cons, Bool.and_assoc])
    (fun _ _ _ ↦ by simp [ngS, Stmt.uses, Stmt.tmps, allV_eq, List.all_append])
    (fun _ _ _ ↦ by simp [ngS, Stmt.uses, Stmt.tmps, allV_eq])
    (fun _ _ _ _ ↦ by simp [ngS, Stmt.uses, Stmt.tmps, Bool.and_assoc, allV_eq, List.all_append])
    (fun _ ↦ by simp [ngS, Stmt.uses, Stmt.tmps, allV_eq])
    (by simp [ngL, Stmt.usesList, Stmt.tmpsList])
    (fun _ _ hs hl ↦ by
      show (ngS _ && ngL _) = _
      rw [hs, hl]; simp only [Stmt.usesList, Stmt.tmpsList, List.all_append]
      cases (Stmt.uses _).all okV <;> cases (Stmt.usesList _).all okV <;>
        cases (Stmt.tmps _).all okV <;> cases (Stmt.tmpsList _).all okV <;> rfl)
    (by simp [ngA, Stmt.usesArms, Stmt.tmpsArms])
    (fun _ _ hs hl ↦ by
      show (ngL _ && ngA _) = _
      rw [hs, hl]; simp only [Stmt.usesArms, Stmt.tmpsArms, List.all_append]
      cases (Stmt.usesList _).all okV <;> cases (Stmt.usesArms _).all okV <;>
        cases (Stmt.tmpsList _).all okV <;> cases (Stmt.tmpsArms _).all okV <;> rfl) ss
  rw [h, noGhostL, List.all_append]

theorem noRetListS_append : ∀ (a b : List Stmt), Memory.Stmt.noRetListS (a ++ b) = (Memory.Stmt.noRetListS a && Memory.Stmt.noRetListS b)
  | [], _ => by simp [Memory.Stmt.noRetListS]
  | s :: a, b => by simp only [List.cons_append, Memory.Stmt.noRetListS, noRetListS_append a b, Bool.and_assoc]

theorem noGhostL_append (a b : List Stmt) : noGhostL (a ++ b) = (noGhostL a && noGhostL b) := by
  simp only [noGhostL, usesList_append, tmpsList_append, List.all_append]
  cases (Stmt.usesList a).all okV <;> cases (Stmt.usesList b).all okV <;>
    cases (Stmt.tmpsList a).all okV <;> cases (Stmt.tmpsList b).all okV <;> rfl

theorem endsRet_of_noRet : ∀ (ss : List Stmt), Memory.Stmt.noRetListS ss = true → endsRet ss = false
  | [], _ => rfl
  | s :: ss, h => by
    simp only [Memory.Stmt.noRetListS, Bool.and_eq_true] at h
    cases s with
    | ret _ => simp [Memory.Stmt.noRet] at h
    | atom _ => exact endsRet_of_noRet ss h.2
    | ite _ _ _ => exact endsRet_of_noRet ss h.2
    | match_ _ _ => exact endsRet_of_noRet ss h.2
    | call _ _ _ => exact endsRet_of_noRet ss h.2
    | callIf _ _ _ => exact endsRet_of_noRet ss h.2
    | dispatch _ _ _ _ => exact endsRet_of_noRet ss h.2

/-! ## The pass over a concatenation -/

/-- **The pass is linear**: over `ss₁ ++ ss₂`, `ss₁` without a top-level `ret`, the pass over `ss₁`, then
over `ss₂` from its end. -/
theorem chkC_append (X : CX) : ∀ (ss₁ ss₂ : List Stmt) (st : CSt), endsRet ss₁ = false →
    chkC X (ss₁ ++ ss₂) st = (chkC X ss₁ st).bind (chkC X ss₂)
  | [], _, _, _ => by simp [chkC]
  | s :: ss₁, ss₂, st, h => by
    have ih : ∀ st, chkC X (ss₁ ++ ss₂) st = (chkC X ss₁ st).bind (chkC X ss₂) := fun st ↦
      chkC_append X ss₁ ss₂ st (by cases s <;> simp_all [endsRet])
    cases s with
    | ret _ => simp [endsRet] at h
    | atom a =>
      simp only [List.cons_append, chkC]
      cases atomC X st a <;> simp [CSt.seq_eq, ih]
    | ite c z n =>
      simp only [List.cons_append, chkC]
      cases h1 : chkC (X.ext (czero c)) z (zeroEq st c) with
      | none => rfl
      | some s1 =>
        simp only
        split <;> simp [CSt.seq_eq, ih]
    | match_ x arms =>
      simp only [List.cons_append, chkC]
      cases chkArmsC X x 0 arms st <;> simp [CSt.seq_eq, ih]
    | call g args rets =>
      simp only [List.cons_append, chkC]
      cases callC X st g args rets <;> simp [CSt.seq_eq, ih]
    | callIf c g args =>
      simp only [List.cons_append, chkC]
      cases callIfC X st c g args <;> simp [CSt.seq_eq, ih]
    | dispatch x fs args rets =>
      simp only [List.cons_append, chkC]
      cases dispC X st x fs args rets <;> simp [CSt.seq_eq, ih]

/-! ## Windows -/

/-- **A window**: the statements `ss` have no `ret` and name no ghost value (by the recursors), and the pass
over them goes from `st` to `st'`. -/
noncomputable def winOk (pows : PowTree) (sigOf : String → HSig) (f : Fn) (H : HCert) (ss : List Stmt)
    (st st' : CSt) : Bool :=
  nrL ss && ngL ss && withCx pows sigOf f H fun X ↦ decide (chkC X ss st = some st')

theorem winOk_spec {pows : PowTree} {sigOf : String → HSig} {f : Fn} {H : HCert} {ss : List Stmt} {st st' : CSt}
    (h : winOk pows sigOf f H ss st st' = true) :
    Memory.Stmt.noRetListS ss = true ∧ noGhostL ss = true ∧ chkC (cxOf pows sigOf f H) ss st = some st' := by
  simp only [winOk, withCx_eq, Bool.and_eq_true, decide_eq_true_eq, nrL_eq, ngL_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- **Consecutive windows** of the block `L`: the cut points and the states there, each window the
statements from one cut point to the next. -/
def winsOk (pows : PowTree) (sigOf : String → HSig) (f : Fn) (H : HCert) (L : List Stmt) :
    List (ℕ × CSt) → Prop
  | (a, S) :: (b, S') :: l => winOk pows sigOf f H ((L.drop a).take (b - a)) S S' = true ∧ a ≤ b ∧
      winsOk pows sigOf f H L ((b, S') :: l)
  | _ => True

/-- The last cut point and state. -/
def lastW : List (ℕ × CSt) → ℕ × CSt → ℕ × CSt
  | [], p => p
  | p :: l, _ => lastW l p

/-- **Windows chained**: from the first cut point to the last, the pass goes from the first state to the last,
and the statements between have no `ret` and name no ghost value. -/
theorem winsOk_chain {pows : PowTree} {sigOf : String → HSig} {f : Fn} {H : HCert} {L : List Stmt} :
    ∀ (l : List (ℕ × CSt)) (a : ℕ) (S : CSt), winsOk pows sigOf f H L ((a, S) :: l) →
      chkC (cxOf pows sigOf f H) (L.drop a) S =
          chkC (cxOf pows sigOf f H) (L.drop (lastW l (a, S)).1) (lastW l (a, S)).2 ∧
        Memory.Stmt.noRetListS ((L.drop a).take ((lastW l (a, S)).1 - a)) = true ∧
        noGhostL ((L.drop a).take ((lastW l (a, S)).1 - a)) = true ∧ a ≤ (lastW l (a, S)).1
  | [], a, S, _ => by simp [lastW, Memory.Stmt.noRetListS, noGhostL, Stmt.usesList, Stmt.tmpsList]
  | (b, S') :: l, a, S, h => by
    obtain ⟨hw, hab, hr⟩ := h
    obtain ⟨hc, hn, hg, hb⟩ := winsOk_chain l b S' hr
    obtain ⟨hwn, hwg, hwc⟩ := winOk_spec hw
    simp only [lastW] at hc hn hg hb ⊢
    have hsplit : L.drop a = (L.drop a).take (b - a) ++ L.drop b := by
      conv_lhs => rw [← List.take_append_drop (b - a) (L.drop a)]
      rw [List.drop_drop]; congr 2; omega
    have htake : (L.drop a).take ((lastW l (b, S')).1 - a) =
        (L.drop a).take (b - a) ++ (L.drop b).take ((lastW l (b, S')).1 - b) := by
      rw [show (lastW l (b, S')).1 - a = (b - a) + ((lastW l (b, S')).1 - b) by omega, List.take_add,
        List.drop_drop]
      congr 3; omega
    refine ⟨?_, ?_, ?_, by omega⟩
    · rw [hsplit, chkC_append _ _ _ _ (endsRet_of_noRet _ hwn), hwc, Option.bind_some, hc]
    · rw [htake, noRetListS_append, hwn, hn]; rfl
    · rw [htake, noGhostL_append, hwg, hg]; rfl

/-! ## The context stated

Every window builds `cxOf`'s tries from the certificate (`withCx`), which for a large certificate costs more than
the window's pass. The tries can be stated once instead, as literals (`cxOf_lit`, each equation decided once),
after which a window reads them at no building cost (`withCx_cx`). -/

/-- The entry at a position of a list, by the recursors: what a stated context's tries hold, read from the
certificate's lists (a literal of the trie's shape, each entry a position of a list in the certificate). -/
noncomputable def nthO {α : Type} (l : List α) : ℕ → Option α :=
  List.rec (motive := fun _ ↦ ℕ → Option α) (fun _ ↦ none)
    (fun a _ ih n ↦ Nat.rec (motive := fun _ ↦ Option α) (some a) (fun m _ ↦ ih m) n) l

/-- A list without its first `n` entries, by the recursors: where a long list's positions are read from
(`nthO`), so that no reading walks far. -/
noncomputable def dropO {α : Type} (l : List α) (n : ℕ) : List α :=
  Nat.rec (motive := fun _ ↦ List α → List α) (fun l ↦ l)
    (fun _ ih l ↦ ih (List.rec (motive := fun _ ↦ List α) [] (fun _ t _ ↦ t) l)) n l

/-- **The context with its tries stated.** -/
theorem cxOf_lit {pows : PowTree} {sigOf : String → HSig} {f : Fn} {H : HCert}
    {R : Trie (List (ℕ × ℕ × Wit))} {P : Trie CCell} {C T : Trie (List Wit)} {RS : Trie CRes} {DV HV EQ : Trie Unit}
    (hR : H.readT = R) (hP : trieFrom H.sig.pre 0 .nil = P) (hC : trieFrom H.calls 0 .nil = C)
    (hT : trieFrom H.rets 0 .nil = T) (hRS : trieFrom H.res 0 .nil = RS) (hDV : keysT H.divs .nil = DV)
    (hHV : keysT H.hvs .nil = HV) (hEQ : keysT H.eqs .nil = EQ) :
    cxOf pows sigOf f H = ⟨pows, R, P, C, T, RS, DV, HV, H.gargs, sigOf, H.sig, f.params, [], EQ, H.fas, H.ders⟩ := by
  subst hR hP hC hT hRS hDV hHV hEQ; rfl

/-- `withCx` at a stated context. -/
theorem withCx_cx {β : Type} {pows : PowTree} {sigOf : String → HSig} {f : Fn} {H : HCert} {X0 : CX}
    (h : cxOf pows sigOf f H = X0) (k : CX → β) : withCx pows sigOf f H k = k X0 := by
  rw [withCx_eq, h]

/-! ## A loop helper assembled -/

/-- **The head of a loop helper's check**: the parameters, the preconditions over them, the termination
fact `[(.val 0, ei)]`, no `retM`/`postV`/`retEq`, the tail's shape (`loopTail`), the parameters and the two
tail statements naming no ghost, the frame run cells at return (`faOk`), the windows reaching past the body (`N`), and the entry state `S₀`. -/
noncomputable def headOk (pows : PowTree) (sigOf : String → HSig) (f : Fn) (H : HCert) (ei : CIdx) (N : ℕ)
    (S0 : CSt) : Bool :=
  paramsN f.params 0 && preOver f.params.length H.sig.pre &&
    H.sig.term.all (fun p ↦ idxOver f.params.length p.1 && idxOver f.params.length p.2) &&
    decide (H.sig.term = [(.val 0, ei)]) &&
    H.sig.retM.isEmpty && H.sig.postV.isEmpty && H.sig.retEq.isEmpty && H.sig.postQ.isEmpty &&
    f.params.all okV && noGhostL (f.body.drop (f.body.length - 2)) &&
    faOk (topAtoms f.body) (dstKeys (topAtoms f.body)) H.fas &&
    (match endOf ei with
      | some endc => (loopTail f endc).isSome
      | none => false) &&
    decide ((loopBody f).length ≤ N) &&
    withCx pows sigOf f H fun X ↦ decide (initC X = some S0)

/-- **The tail of a loop helper's check**: from the state `Sn` after its body without the tail, the tail call
and the guarantees at its `ret []`. -/
noncomputable def tailOkW (pows : PowTree) (sigOf : String → HSig) (f : Fn) (H : HCert) (ei : CIdx) (Sn : CSt) :
    Bool :=
  match f.body.reverse with
  | .ret [] :: .callIf c g args :: _ => withCx pows sigOf f H fun X ↦ match callIfC X Sn c g args with
    | some st2 => tailC X st2 args ei
    | none => false
  | _ => false

/-- **A loop helper's heap check from windows**: the head, consecutive windows from `(0, S₀)` to `(N, Sₙ)`
over the body without its tail, and the tail. -/
theorem heapOkC1_of_wins {pows : PowTree} {sigOf : String → HSig} {f : Fn} {H : HCert} {ei : CIdx} {N : ℕ}
    {S0 Sn : CSt} {l : List (ℕ × CSt)} (hh : headOk pows sigOf f H ei N S0 = true)
    (hw : winsOk pows sigOf f H (loopBody f) ((0, S0) :: l)) (hl : lastW l (0, S0) = (N, Sn))
    (ht : tailOkW pows sigOf f H ei Sn = true) : heapOkC1 pows sigOf f H = true := by
  simp only [headOk, Bool.and_eq_true, decide_eq_true_eq, withCx_eq] at hh
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hpar, hpov⟩, hto⟩, hterm⟩, hrm⟩, hpv⟩, hre⟩, hpq⟩, hpok⟩, hng2⟩, hfa⟩, hlt⟩, hN⟩, hinit⟩ := hh
  obtain ⟨hc, hnr, hng, -⟩ := winsOk_chain l 0 S0 hw
  rw [hl] at hc hnr hng
  simp only [List.drop_zero, Nat.sub_zero] at hc hnr hng
  rw [List.take_of_length_le hN] at hnr hng
  rw [List.drop_of_length_le hN] at hc
  have hbody : f.body = loopBody f ++ f.body.drop (f.body.length - 2) := (List.take_append_drop _ _).symm
  have hghost : noGhost f = true := by
    have h1 := noGhostL_append (loopBody f) (f.body.drop (f.body.length - 2))
    rw [← hbody, hng, hng2] at h1
    simp only [noGhostL, List.all_append, Bool.and_true, Bool.and_eq_true] at h1
    simp only [noGhost, List.all_append, Bool.and_eq_true]
    exact ⟨⟨h1.1, h1.2⟩, hpok⟩
  unfold heapOkC1
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨hpar, hpov⟩, hto⟩, hghost⟩, hfa⟩, ?_⟩
  simp only [Trie.seq_eq]
  have hX : (⟨pows, H.readT, trieFrom H.sig.pre 0 .nil, trieFrom H.calls 0 .nil, trieFrom H.rets 0 .nil,
      trieFrom H.res 0 .nil, keysT H.divs .nil, keysT H.hvs .nil, H.gargs, sigOf, H.sig, f.params, [],
      keysT H.eqs .nil, H.fas, H.ders⟩ : CX) = cxOf pows sigOf f H := rfl
  rw [hX, hinit, hterm]
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨hrm, hpv⟩, hre⟩, hpq⟩, ?_⟩
  -- the tail's shape
  revert hlt
  split
  · rename_i endc hend
    intro hlt
    have hrev : ∃ c g i' rest rpre, f.body.reverse = .ret [] :: .callIf c g (i' :: rest) :: rpre := by
      unfold loopTail at hlt
      split at hlt
      · rename_i c g i' rest rpre _ _ hrev _
        exact ⟨c, g, i', rest, rpre, hrev⟩
      · cases hlt
    obtain ⟨c, g, i', rest, rpre, hrev⟩ := hrev
    unfold loopC
    rw [hend, hrev]
    simp only
    rw [loopShape_of hlt hnr]
    simp only
    rw [hc]
    simp only [chkC]
    unfold tailOkW at ht
    simp only [hrev, withCx_eq] at ht
    exact ht
  · intro hlt; cases hlt

/-- `heapOkC1_of_wins` for a certificate with no split. -/
theorem heapOkC_of_wins {pows : PowTree} {sigOf : String → HSig} {f : Fn} {H : HCert} {ei : CIdx} {N : ℕ}
    {S0 Sn : CSt} {l : List (ℕ × CSt)} (hh : headOk pows sigOf f H ei N S0 = true)
    (hw : winsOk pows sigOf f H (loopBody f) ((0, S0) :: l)) (hl : lastW l (0, S0) = (N, Sn))
    (ht : tailOkW pows sigOf f H ei Sn = true) (ha : H.arms = [] := by rfl) : heapOkC pows sigOf f H = true :=
  heapOkC_of1 ha (heapOkC1_of_wins hh hw hl ht)

end

end LeanVM.Guest.CoreMode
