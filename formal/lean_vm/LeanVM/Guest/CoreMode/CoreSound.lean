/-
  LeanVM.Guest.CoreMode.CoreSound

  The core route meets the frame interface: `frameSpec_core`.
-/

module

public import LeanVM.Guest.CoreMode.CoreSlot

/-!
# The core route's frame interface, proved

`frameSpec_core`: a function passing the kernel's checks (`CoreOk`) meets `FrameSpec` for `CoreAt`
on a reference image, at states on its run where its frames have honest valuations (`CoreHon`).

* The heap facts (`heapK_sound`): milestone 1's check or the check with calls give every event's needs
  written before it (`ReadsOkC`) and the promised cells written by the end.
* Entry: the frame walk's entry (`atF_entry`), the pairing at the body (`pairAt_zero`), the heap
  preconditions the signature's, written at entry (`hw_slot`).
* A step: `frame_step`, its oracle's heap cell written by the pairing (`pair_readC`), a fall-through
  at the pairing's next position (`pair_fallC`), a store's cell written by its `DEREF` (`StoreW`); the
  return, the last instruction, with the signature's guarantees (`pair_retC`); a call (`pair_callC`):
  the callee's mode signature's entry facts from its heap signature's preconditions (`jumpCallOk`,
  `fitB`), and the caller resumed in any memory agreeing with the reference past the callee's
  guarantees (`Resume`), the callee frame's cells holding the call's words (`HonF.kid`).
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Bridge (AlignCtx Zip ZOk fwdJ flowAtom isaFlowHint stmtsOf stmtsSub zok_stmts Pairs)
open LeanVM.Prover.Exec (Hint St Ctx Fine Moves StepOk HintOk refMem maxCells runOp Mem gpow_inj
  Mem.get_of_written OpModed OnRef Agree)
open LeanVM.Guest.Check (getF)
open LeanVM.Guest.Mode (Names written_of_get written_mono names_inj opOfOff RefOk HintIn Holds entryAbs
  FrameSpec Out HintsAt ResAt RetAll RetHolds HW RW MonoVal BsVal BaseVal IdxVal stOf CodeOk)

@[expose] public section

variable {κ : ℕ}

/-! ## Tries -/

theorem trie_get_set_eq {α : Type} (a : α) :
    ∀ (d : ℕ) (t : Exec.Trie α) (n m : ℕ), n + 1 < 2 ^ d →
      (t.set a d n).get m = if m = n then some a else t.get m
  | 0, _, n, _, h => by simp at h
  | d + 1, t, n, m, h => by
    have hp : 2 ^ (d + 1) = 2 * 2 ^ d := by rw [Nat.pow_succ]; ring
    rw [Exec.Trie.set_succ, Exec.Trie.get_eq_node t m]
    by_cases h0 : n = 0
    · subst h0
      simp only [↓reduceIte, Exec.Trie.get_node]
      by_cases hm : m = 0 <;> simp [hm]
    · by_cases h1 : n % 2 = 1
      · simp only [h0, h1, ↓reduceIte, Exec.Trie.get_node]
        by_cases hm : m = 0
        · simp only [hm, ↓reduceIte]
          simp only [Ne.symm h0, ↓reduceIte]
        · by_cases hm1 : m % 2 = 1
          · rw [trie_get_set_eq a d _ _ _ (by omega)]
            by_cases he : m = n
            · subst he; simp [hm, hm1]
            · have : m / 2 ≠ n / 2 := by omega
              simp [hm, hm1, he, this]
          · have : m ≠ n := by omega
            simp [hm, hm1, this]
      · simp only [h0, h1, ↓reduceIte, Exec.Trie.get_node]
        by_cases hm : m = 0
        · simp only [hm, ↓reduceIte]
          simp only [Ne.symm h0, ↓reduceIte]
        · by_cases hm1 : m % 2 = 1
          · have : m ≠ n := by omega
            simp [hm, hm1, this]
          · rw [trie_get_set_eq a d _ _ _ (by omega)]
            by_cases he : m = n
            · subst he; simp [hm, hm1]
            · have : m / 2 - 1 ≠ n / 2 - 1 := by omega
              simp [hm, hm1, he, this]

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
    rw [trie_get_set_eq () _ t a o (hl a List.mem_cons_self)]
    split_ifs <;> simp [h]

theorem foldlT_mem : ∀ (l : List ℕ) (t : Exec.Trie Unit) {o : ℕ}, (∀ x ∈ l, x + 1 < 2 ^ Exec.envDepth) →
    o ∈ l → (Mode.foldlT t l).get o = some ()
  | [], _, _, _, h => absurd h List.not_mem_nil
  | a :: l, t, o, hl, h => by
    rw [foldlT_cons]
    rcases List.mem_cons.mp h with rfl | h
    · refine foldlT_keep l _ (fun x hx ↦ hl x (List.mem_cons_of_mem _ hx)) ?_
      rw [trie_get_set_eq () _ t o o (hl o List.mem_cons_self)]
      simp
    · exact foldlT_mem l _ (fun x hx ↦ hl x (List.mem_cons_of_mem _ hx)) h

theorem trieNil_get {α : Type} {t : Exec.Trie α} (h : trieNil t = true) (n : ℕ) : t.get n = none := by
  cases t with
  | nil => rfl
  | node => simp [trieNil] at h

theorem has_hasP {t : Exec.Trie Unit} {i : ℕ} : has t i = hasP t i := by
  simp only [has, hasP, Check.getF_eq]

/-! ## The shape -/

theorem retLast_jump {X : AlignCtx} : ∀ {n : ℕ} {code : List OffsetInstruction} {i oc od of : ℕ},
    retLast X n code = true → code[i]? = some (.jump oc od of) →
      (i + 1 = code.length ∧ od = 0 ∧ of = 1 ∧ X.zeroAt oc = false ∧ fwdJ X (n + i) oc od of = false) ∨
      (i + 1 < code.length ∧ X.zeroAt oc = false ∧ fwdJ X (n + i) oc od of = false ∧ ¬ (od = 0 ∧ of = 1))
  | _, [], _, _, _, _, h, _ => by simp [retLast] at h
  | n, ins :: rest, i, oc, od, of, h, hi => by
    cases rest with
    | nil =>
      cases i with
      | succ i => simp at hi
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
        subst hi
        simp only [retLast, retIns, Bool.and_eq_true, Nat.beq_eq, Bool.not_eq_true'] at h
        exact Or.inl ⟨rfl, h.1.1.1, h.1.1.2, h.1.2, by simpa using h.2⟩
    | cons ins' rest' =>
      rw [retLast, Bool.and_eq_true] at h
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
        subst hi
        have h1 := h.1
        simp only [callIns, Bool.and_eq_true, Bool.not_eq_true'] at h1
        refine Or.inr ⟨by simp, h1.1.1, by simpa using h1.1.2, fun ⟨h0, h1'⟩ ↦ ?_⟩
        rw [h0, h1'] at h1
        simp at h1
      | succ i =>
        simp only [List.getElem?_cons_succ] at hi
        rcases retLast_jump h.2 hi with ⟨h1, h2, h3, h4, h5⟩ | ⟨h1, h2, h3, h4⟩
        · refine Or.inl ⟨by simp only [List.length_cons] at h1 ⊢; omega, h2, h3, h4, ?_⟩
          rw [show n + (i + 1) = n + 1 + i by omega]
          exact h5
        · refine Or.inr ⟨by simp only [List.length_cons] at h1 ⊢; omega, h2, ?_, h4⟩
          rw [show n + (i + 1) = n + 1 + i by omega]
          exact h3

theorem straight_straightC : ∀ {body : List Stmt}, straight body = true → straightC body = true
  | [], _ => rfl
  | s :: body, h => by
    simp only [straight, List.all_cons, Bool.and_eq_true] at h
    simp only [straightC, List.all_cons, Bool.and_eq_true]
    refine ⟨?_, straight_straightC (by simpa [straight] using h.2)⟩
    cases s <;> simp_all

/-- **The events of a body of atoms, calls and returns**: its atoms' and its calls'. -/
theorem straightC_ev {σ : Val} : ∀ {body : List Stmt}, straightC body = true → ∀ {es : List Ev} {vs : List V},
    walk σ body = .ret es vs → ∀ e ∈ es, (∃ a, e = .atom a ∧ Stmt.atom a ∈ body) ∨
      ∃ f args rets, e = .call f args rets ∧ Stmt.call f args rets ∈ body
  | [], _, es, vs, hw => by simp [walk] at hw
  | s :: body, h, es, vs, hw => by
    simp only [straightC, List.all_cons, Bool.and_eq_true] at h
    have ih := @straightC_ev σ body (by simpa [straightC] using h.2)
    cases s with
    | atom b =>
      rw [Bridge.walk_atom_cons] at hw
      obtain ⟨es', hw', rfl⟩ := Bridge.pre_eq_ret hw
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact Or.inl ⟨b, rfl, List.mem_cons_self⟩
      · rcases ih hw' e he with ⟨a, h1, h2⟩ | ⟨f, args, rets, h1, h2⟩
        · exact Or.inl ⟨a, h1, List.mem_cons_of_mem _ h2⟩
        · exact Or.inr ⟨f, args, rets, h1, List.mem_cons_of_mem _ h2⟩
    | call f args rets =>
      rw [Bridge.walk_call_cons] at hw
      obtain ⟨es', hw', rfl⟩ := Bridge.pre_eq_ret hw
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact Or.inr ⟨f, args, rets, rfl, List.mem_cons_self⟩
      · rcases ih hw' e he with ⟨a, h1, h2⟩ | ⟨f, args, rets, h1, h2⟩
        · exact Or.inl ⟨a, h1, List.mem_cons_of_mem _ h2⟩
        · exact Or.inr ⟨f, args, rets, h1, List.mem_cons_of_mem _ h2⟩
    | ret vs' =>
      rw [Bridge.walk_ret_cons, Memory.Out.ret.injEq] at hw
      obtain ⟨rfl, -⟩ := hw
      intro e he
      cases he
    | _ => simp at h

/-- The returned values of a body of atoms, calls and returns are a `ret`'s. -/
theorem straightC_ret {σ : Val} : ∀ {body : List Stmt}, straightC body = true → ∀ {es : List Ev} {vs : List V},
    walk σ body = .ret es vs → Stmt.ret vs ∈ body
  | [], _, es, vs, hw => by simp [walk] at hw
  | s :: body, h, es, vs, hw => by
    simp only [straightC, List.all_cons, Bool.and_eq_true] at h
    cases s with
    | atom b =>
      rw [Bridge.walk_atom_cons] at hw
      obtain ⟨es', hw', rfl⟩ := Bridge.pre_eq_ret hw
      exact List.mem_cons_of_mem _ (straightC_ret (by simpa [straightC] using h.2) hw')
    | call f args rets =>
      rw [Bridge.walk_call_cons] at hw
      obtain ⟨es', hw', rfl⟩ := Bridge.pre_eq_ret hw
      exact List.mem_cons_of_mem _ (straightC_ret (by simpa [straightC] using h.2) hw')
    | ret vs' =>
      rw [Bridge.walk_ret_cons, Memory.Out.ret.injEq] at hw
      obtain ⟨-, rfl⟩ := hw
      exact List.mem_cons_self
    | _ => simp at h

theorem retsN_len {σ : Val} {body : List Stmt} (hs : straightC body = true) {n : ℕ} (hn : retsN n body = true)
    {es : List Ev} {vs : List V} (hw : walk σ body = .ret es vs) : vs.length = n := by
  have h := List.all_eq_true.mp hn _ (straightC_ret hs hw)
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

theorem slotW_lt {ws ws' : List E} {b : ℕ} (hb : b < ws.length) : slotW (ws ++ ws') b = slotW ws b := by
  rw [slotW_append]; simp [hb]

theorem slotW_get {ws : List E} {b : ℕ} (hb : b < ws.length) : slotW ws b = ws[b] := by
  unfold slotW
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb, Option.getD_some]

theorem rd_pow {img : MemoryImage κ} {a b : ℕ} (h : (g : K) ^ a = g ^ b) (o : ℕ) : Rd img a o = Rd img b o := by
  simp only [Rd, h]

theorem pow_of_ofK {a b : ℕ} (h : ofK ((g : K) ^ a) = ofK (g ^ b)) : (g : K) ^ a = g ^ b :=
  ofK_injective h

/-! ## The heap facts -/

/-- **The heap facts of an honest path**: its parameters `V.n k`; every event's needs written before
it; the promised cells and the signature's runs written by the end, at the parameters' and returned
words; the returned words' monomials. -/
theorem heapK_sound {Cf : CFun} (hk : HeapK Cf) (hp : Cf.pows.Ok) (hst : straightC Cf.fn.body = true) {σ : Val}
    {rd : Reader} {es : List Ev} {vs : List V} (hw : walk σ Cf.fn.body = .ret es vs) (hh : ∀ e ∈ es, e.Holds rd σ) :
    Cf.fn.params = (List.range Cf.fn.params.length).map V.n ∧
    ReadsOkC Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) es ∧
    (∀ c ∈ Cf.posts, WrittenC Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) es
      (c.addrW (slotW (Cf.fn.params.map σ ++ vs.map σ)))) ∧
    (∀ r ∈ Cf.H.sig.postR, ∀ x, r.Set (slotW (Cf.fn.params.map σ ++ vs.map σ)) x →
      WrittenC Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) es x) ∧
    RetMOk Cf.H.sig (Cf.fn.params.map σ) (vs.map σ) := by
  cases hk with
  | m1 hok hpo hstr hpov hrm =>
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
      · exact Or.inl (Or.inl (Or.inl ⟨c, hc, addr_pre hpar' hpre hc⟩))
      · exact Or.inr ⟨.atom a, ha, hwa⟩
    have hnc : ∀ e ∈ es, ∃ a, e = .atom a := fun e he ↦ by
      rcases straightC_ev hst hw e he with ⟨a, rfl, -⟩ | ⟨f, args, rets, rfl, hm⟩
      · exact ⟨a, rfl⟩
      · have := List.all_eq_true.mp hstr _ hm
        simp at this
    refine ⟨hpar', fun es1 e es2 he ↦ ?_, fun c hc ↦ ?_, fun r hr ↦ (by rw [hpostR] at hr; cases hr),
      fun k c hkc ↦ (by rw [hrm] at hkc; cases hkc)⟩
    · obtain ⟨a, rfl⟩ := hnc e (by rw [he]; simp)
      exact fun x hr ↦ hconv _ _ (hrw es1 a es2 x he hr)
    · simp only [CFun.posts, hpost, List.append_nil] at hc
      obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hc
      have h1 := hconv _ _ (postOk_sound hp hpo hw hh p hp')
      have hv : p.1.addrW (slotW (Cf.fn.params.map σ ++ vs.map σ)) = p.1.addrW (slotW (Cf.fn.params.map σ)) := by
        unfold CCell.addrW
        rw [valW_congr fun b hb ↦ ?_]
        have := List.all_eq_true.mp (List.all_eq_true.mp hpov p.1 (List.mem_map_of_mem hp')) b hb
        exact slotW_lt (by simpa using Nat.blt_eq.mp this)
      rw [hv, addr_pre hpar' hpov (List.mem_map_of_mem hp')]
      exact h1
  | c hok hterm hres hcb hpost =>
    have hok' := hok
    unfold heapOkC at hok'
    simp only [Bool.and_eq_true] at hok'
    obtain ⟨⟨⟨hpar, -⟩, -⟩, -⟩ := hok'
    have hpar' : Cf.fn.params = (List.range Cf.fn.params.length).map V.n := by
      rw [List.range_eq_range']; exact paramsN_eq _ 0 hpar
    have hself : Cf.sigOf Cf.fn.name = Cf.H.sig := by simp [CFun.sigOf]
    have hM : ∀ e ∈ es, EvM Cf.sigOf σ e := fun e he ↦ by
      rcases straightC_ev hst hw e he with ⟨a, rfl, -⟩ | ⟨f, args, rets, rfl, hm⟩
      · trivial
      · have := List.all_eq_true.mp hcb _ hm
        simp only [Bool.and_eq_true, List.isEmpty_iff] at this
        intro k c hkc
        rw [this.2] at hkc
        cases hkc
    obtain ⟨hreads, ⟨⟨hpc, hpr⟩, -⟩, hretm⟩ := heapOkC_sound hp hok hself hw hh hM
      (fun p hp ↦ (by rw [hterm] at hp; cases hp))
      ⟨fun a b h ↦ (by rw [hres] at h; cases h), fun c r h ↦ (by rw [hres] at h; cases h),
        fun q r h ↦ (by rw [hres] at h; cases h)⟩
    refine ⟨hpar', hreads, fun c hc ↦ ?_, fun r hr x hx ↦ hpr r hr x hx, hretm⟩
    simp only [CFun.posts, hpost, List.map_nil, List.nil_append] at hc
    exact hpc c hc

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
monomial is a returned value's at its cell (milestone 1's pass), or returned word `p.1 - 2 - np`'s of
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
  | bits v start nbits d =>
    cases d with
    | stack => simp [hintHeap] at hd
    | heap p' off' len' =>
      simp only [hintHeap, Option.some.injEq, Prod.mk.injEq] at hd
      obtain ⟨rfl, rfl, rfl⟩ := hd
      cases h <;> simp only [Bridge.compiles, Bool.false_eq_true] at hco
      rename_i x bd n
      cases bd <;> simp_all [Bridge.destOk, isaHeap]
  | bitsExp v nbits d =>
    cases d with
    | stack => simp [hintHeap] at hd
    | heap p' off' len' =>
      simp only [hintHeap, Option.some.injEq, Prod.mk.injEq] at hd
      obtain ⟨rfl, rfl, rfl⟩ := hd
      cases h <;> simp only [Bridge.compiles, Bool.false_eq_true] at hco
      rename_i x bd n
      cases bd <;> simp_all [Bridge.destOk, isaHeap]
  | digitsExp v nbits ndigits digitBits start sc d =>
    cases d with
    | stack => simp [hintHeap] at hd
    | heap p' off' len' =>
      simp only [hintHeap, Option.some.injEq, Prod.mk.injEq] at hd
      obtain ⟨rfl, rfl, rfl⟩ := hd
      cases h <;> simp only [Bridge.compiles, Bool.false_eq_true] at hco
      rename_i x bd nb nd db st sc'
      cases bd <;> simp_all [Bridge.destOk, isaHeap]
  | windowsExp v start width count d =>
    cases d with
    | stack => simp [hintHeap] at hd
    | heap p' off' len' =>
      simp only [hintHeap, Option.some.injEq, Prod.mk.injEq] at hd
      obtain ⟨rfl, rfl, rfl⟩ := hd
      cases h <;> simp only [Bridge.compiles, Bool.false_eq_true] at hco
      rename_i x bd pos st w c
      cases bd <;> simp_all [Bridge.destOk, isaHeap]
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
  have h : paramsN Cf.fn.params 0 = true := by
    cases hk with
    | m1 hok _ _ _ _ => unfold heapOk at hok; simp only [Bool.and_eq_true] at hok; exact hok.1.1.1
    | c hok _ _ _ _ => unfold heapOkC at hok; simp only [Bool.and_eq_true] at hok; exact hok.1.1.1
  rw [List.range_eq_range']; exact paramsN_eq _ 0 h

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

theorem entOk_spec {X : AlignCtx} {t : ℕ} {f : String} (h : X.entOk t f = true) : getF X.ents t = some f := by
  unfold AlignCtx.entOk at h
  split at h
  · rename_i f' hf'
    rw [hf', beq_iff_eq.mp h]
  · cases h

theorem jumpCallOk_spec {Cf : CFun} {oc od of t : ℕ} {f : String} (h : jumpCallOk Cf (.jump oc od of) = true)
    (hpt : Cf.X.pcAt od = some t) (hent : getF Cf.X.ents t = some f) :
    ¬ (Cf.frame.entry ≤ t ∧ t < Cf.frame.entry + Cf.frame.len) ∧ t < 2 ^ 30 ∧
      ∃ G s, Cf.frame.sigs.get t = some G ∧ getF Cf.X.sites of = some s ∧ s.r < 2 ^ 30 ∧
        fitB G (Cf.sigOf f) s.args.length s.rets.length = true := by
  simp only [jumpCallOk, hpt, hent, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
  obtain ⟨⟨hout, ht⟩, h⟩ := h
  refine ⟨fun ⟨h1, h2⟩ ↦ by simp [h1, h2] at hout, ht, ?_⟩
  split at h
  · rename_i G s hG hs
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨G, s, hG, hs, h.1, h.2⟩
  · cases h

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

/-- **The core route meets the frame interface**: a function passing the kernel's checks, on the
executor's tables for the guest's advice, its code the executor's, at states `Y` on a reference run
where its frames have honest valuations. -/
theorem frameSpec_core {K : Mode.Cert} {Cf : CFun} (hok : CoreOk K Cf) {adv : Prover.Exec.Advice} {C : Ctx}
    (hC : Prover.Exec.Ctx.of guestProgram adv = .ok C) (ha : adv.hints = Data.adviceHints) (hK : CodeOk C K)
    {img : MemoryImage κ} {Y : St → Prop} (hκ : κ ≤ 28) (hY : ∀ s, Y s → ∃ n, OnRef guestProgram img n s)
    (hH : CoreHon img Y K Cf) : FrameSpec C (refMem img) Y K (CoreAt img Cf K.code) := by
  have hsh := hok.shape
  simp only [shapeOk, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, List.all_eq_true,
    Option.isNone_iff_eq_none] at hsh
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hstC, hret⟩, hfp1⟩, hmainX⟩, hpc0⟩, hrN⟩, htgt0⟩, hnzr0⟩, hent⟩, hend⟩, hincr⟩ := hsh
  obtain ⟨henv, harm, hacc⟩ := frameAcc_of hincr hok.frame
  have hsig := hok.sig
  simp only [sigOk, Bool.and_eq_true, Option.isNone_iff_eq_none, List.isEmpty_iff, List.all_eq_true] at hsig
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hself, hterm⟩, hpostL⟩, hpostP⟩, hpostLP⟩, hpostT⟩, hpostC⟩, hpreP⟩, hprePR⟩, hpre⟩,
    hpreR⟩, hpost⟩, hpostR⟩ := hsig
  have hent' : ∀ x ∈ K.F.sig.entry, x + 1 < 2 ^ Exec.envDepth := hok.fsig ▸ hent
  have hpar := heapK_params hok.heap
  set np := Cf.fn.params.length with hnp
  have hws0 : ∀ {fp : ℕ} {σ : Val}, HonF img Cf fp σ →
      ∀ b < np, Rd img fp (2 + b) = some (slotW (Cf.fn.params.map σ) b) := by
    intro fp σ hσ b hb
    rw [slotW_params' hpar hb]
    exact hσ.par b hb
  refine ⟨fun hle hfp h ↦ h.mono hle hfp, ?_, ?_⟩
  · -- the entry
    intro s hH0 hs
    have hA : entryAbs K.E K.F.sig = ⟨Mode.foldlT .nil K.F.sig.entry, .nil, .nil, [], K.F.sig.pre,
        Mode.jtRng K.E :: K.F.sig.preR, K.F.sig.term, [], .nil, K.F.sig.preP, []⟩ := by
      unfold entryAbs
      rw [hself]
    rw [hA] at hH0
    have hw : ∀ o ∈ K.F.sig.entry, s.mem.written (s.fp + o) = true := fun o ho ↦
      hH0.w o (foldlT_mem _ _ hent' ho)
    refine coreAt_of ⟨atF_mono (s := s) (Mem.le_refl _) rfl (atF_entry henv ⟨fun o ho ↦ hw o (hok.fsig ▸ ho),
      fun o hso ↦ by rw [hok.fsig, hself] at hso; cases hso⟩), fun o ho ↦ hw o (hok.fsig ▸ ho), fun σ hσ ↦ ?_⟩
    obtain ⟨es, vs, rd, hwk, hhd⟩ := hσ.path
    refine ⟨Cf.fn.body, [], es, vs, rd, pairAt_zero hok.pair, by simpa using hwk, hwk, by simpa using hhd,
      fun y hy ↦ ?_⟩
    have hSE : ∀ {m : Mode.Mono}, monoS K.F.sig np false m = true → SlotEq s (Cf.fn.params.map σ) m.bs :=
      fun hm ↦ slotEq_of hκ hs.agree hs.fp (hws0 hσ) hm
    rcases hy with ((⟨c, hc, rfl⟩ | ⟨r, hr, hx⟩) | (⟨p, hp, -⟩ | ⟨p, hp, -⟩)) | ⟨e, he, -⟩
    · rcases Bool.or_eq_true_iff.mp (hpre c hc) with h | h
      · obtain ⟨m, hm, hmc⟩ := List.any_eq_true.mp h
        rw [Bool.and_eq_true] at hmc
        obtain ⟨hmS, hmc⟩ := hmc
        unfold monoIs at hmc
        split at hmc
        · rename_i c' hc'
          rw [← CCell.beq_eq hmc]
          exact hw_slot hc' (hSE hmS) (hH0.h m hm)
        · cases hmc
      · obtain ⟨r, hr, hrc⟩ := List.any_eq_true.mp h
        rw [Bool.and_eq_true] at hrc
        exact ptIn_slot hrc.2 (hSE hrc.1) (hH0.r r (List.mem_cons_of_mem _ hr))
    · obtain ⟨r', hr', hrq⟩ := List.any_eq_true.mp (hpreR r hr)
      rw [Bool.and_eq_true] at hrq
      obtain ⟨hmS, hrq⟩ := hrq
      unfold rngIs at hrq
      split at hrq
      · rename_i q hq
        obtain rfl := of_decide_eq_true hrq
        exact rw_slot hq (hSE hmS) (hH0.r r' (List.mem_cons_of_mem _ hr')) y hx
      · cases hrq
    · rw [hpreP] at hp; cases hp
    · rw [hprePR] at hp; cases hp
    · cases he
  · -- a step
    intro s i hi hpc hat hs hYs hsz _ _ _ hjtR _ _ _ hh _ href Inv k
    obtain ⟨hAtF0, hentw, hheap⟩ := hat s.mem (Mem.le_refl _) hs.agree
    have hAtF : AtF img Cf.frame K.code i s := atF_mono (s := Mode.stOf s.mem s.fp) (Mem.le_refl _) rfl hAtF0
    obtain ⟨σ0, hσ0⟩ := hH s i hYs hi hpc
    obtain ⟨n, hon⟩ := hY s hYs
    have hpcF : s.pc = Cf.frame.entry + i := by rw [hok.fentry]; exact hpc
    have hsize := (Prover.Exec.ctx_of_spec hC).1
    have hhintsF : ∀ j < K.code.length, (C.hints[Cf.frame.entry + j]?).getD [] =
        Mode.hintsAt Cf.frame.hints (Cf.frame.entry + j) := by
      intro j hj
      have hpcj : K.F.entry + j < 2 ^ guestProgram.logSize := hsize ▸ Mode.code_pc hK hj
      rw [hok.fentry, Mode.ctx_hints hC (ha ▸ Mode.adviceHints_incr) hpcj, ha, hok.hints j hj]
    have hhd : ∀ j, (Cf.d.2.2.lookup (Cf.X.entry + j)).getD [] = Mode.hintsAt Cf.frame.hints (Cf.frame.entry + j) :=
      fun j ↦ by rw [lookupD_hintsAt, hok.dhints, hok.xentry, hok.fentry]
    have hrwOf : ∀ σ pre es vs rd, walk σ Cf.fn.body = .ret (pre ++ es) vs → (∀ e ∈ pre ++ es, e.Holds rd σ) →
        ReadsOkC Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) (pre ++ es) :=
      fun σ pre es vs rd hb hh0 ↦ (heapK_sound hok.heap hok.pows hstC hb hh0).2.1
    have he1 : ∀ s1, (Mode.hintsAt Cf.frame.hints (Cf.frame.entry + i)).foldlM (Prover.Exec.runHint C) s = .ok s1 →
        ((C.hints[s.pc]?).getD []).foldlM (Prover.Exec.runHint C) s = .ok s1 := fun s1 e1 ↦ by
      rw [hpcF, hhintsF i hi]; exact e1
    have hlen : Cf.frame.len = K.code.length := hok.flen
    refine frame_step (prog := guestProgram) (k := n - s.steps) hκ harm hacc hok.fpows hend hsz
      (fun j hj ↦ by rw [hok.fentry]; exact hK.ops j hj) hhintsF (hok.fentry ▸ hok.fetch) hok.small hi hpcF hAtF hs
      hon.2 (fun h ↦ absurd h (by simp [hfp1]))
      (fun pre h post hp s1 e hm hin ↦ hh pre h post (by rw [hpcF, hhintsF i hi]; exact hp) s1 e hm hin)
      (fun o ho ↦ by simp [trieNil_get hnzr0] at ho) ?_
      (fun c d f _ cv dv _ _ _ _ _ _ kk hk ↦ by rw [trieNil_get htgt0] at hk; cases hk)
      (fun s1 hm ↦ refOk_fp hm.fp href) ?_ ?_
    · -- the oracle's heap cell, written
      intro hOi s1 e1 hm
      have main : ∀ a o c, K.code[i] = .deref a o c .cell → HeapRd s1 (.deref a o c .cell) := by
        intro a o c hci
        obtain ⟨pos, pre, es, vs, rd, hpos, hb, hwp, hh0, hW⟩ := hheap σ0 hσ0
        obtain ⟨as, dv, pv, off, hpairs, hcell, -, hmem, hwr⟩ := pair_readC hok.pair hpos
          (by rw [List.getElem?_eq_getElem hi, hci]) (by rw [← has_hasP]; exact hOi) hwp
          (hrwOf σ0 pre es vs rd hb hh0)
        have hwk : WrK s1.mem (cellAt σ0 pv off) := by
          rcases hwr with h | ⟨a', ha', hfa', hma, hwa⟩
          · exact (hW _ h).mono hm.le
          · rw [hhd i] at hpairs
            exact flow_wrk hκ e1 hs hm hpairs ha' hfa'
              (fun q hq ↦ hσ0.ptr _ _ hb a' q (List.mem_append_right _ hma) hq) hwa
        simp only [cellsAt, Bool.and_eq_true, Nat.beq_eq] at hcell
        obtain ⟨⟨hloc, hoff⟩, -⟩ := hcell
        intro p x hp hx
        have hsm := hok.small i hi
        rw [hci] at hsm
        obtain ⟨sa, -, -⟩ := hsm
        have hrd : Rd img s1.fp a = some (σ0 pv) := by
          rw [hm.fp, ← hloc]; exact hσ0.ptr _ _ hb (.load dv pv off) pv (List.mem_append_right _ hmem) rfl
        have hpv : p = σ0 pv := rd_get hκ hm.fine sa hrd hp
        obtain ⟨x', hx', hlt', hw'⟩ := hwk
        have h1 := hx.1
        rw [limb0_mul_ofK, hpv, ← hoff] at h1
        have hxx : x = x' := gpow_inj (lt_maxCells_63 hx.2) (lt_maxCells_63 hlt') (h1.symm.trans hx')
        rw [hxx]
        exact hw'
      generalize hci : K.code[i] = ins
      cases ins with
      | deref a o c mode =>
        cases mode with
        | cell => exact main a o c hci
        | pc => trivial
        | fp => trivial
      | _ => trivial
    · -- falling through
      intro s1 s' e1 hm hmo e' hpc' hfp' hf' hle' hat' hstw
      have hle : s.mem ≤ s'.mem := Mem.le_trans hm.le hle'
      have hi1 : i + 1 < K.code.length := by
        by_contra hn
        obtain ⟨cur, pend, h0, hh0⟩ := hat'
        obtain ⟨rfl, rfl⟩ := preF_end hacc (by omega) h0
        rcases hh0 with ⟨A, hA, -⟩ | ⟨g', hg', -⟩
        · cases hA
        · cases hg'
      have hnj : ∀ oc od of, K.code[i]? ≠ some (.jump oc od of) := by
        intro oc od of hci
        rcases retLast_jump hret hci with ⟨h1, -⟩ | ⟨-, hz, hfw, hnr⟩
        · omega
        · -- a call's jump does not fall through
          have hcode : K.code[i] = .jump oc od of := Option.some.inj ((List.getElem?_eq_getElem hi).symm.trans hci)
          have hsm := hok.small i hi
          rw [hcode] at hsm
          obtain ⟨soc, sod, -⟩ := hsm
          have e2 := e'
          rw [hcode] at e2
          obtain ⟨vc, vd, vf, hvc, hvd, -, -, hcase⟩ := Mode.jump_vals ⟨hm.fine.agree.wf, hm.fine.dl⟩ e2
          obtain ⟨pos, pre, es, vs, rd, hpos, -, -, -, -⟩ := hheap σ0 hσ0
          obtain ⟨f, args, rets, st, t, o, pos', hsite, hpt, hentF, hnzc, -⟩ :=
            pair_callC hok.pair hpos hci hz (by simpa using hfw) hnr hmainX hstC
          rcases hcase with ⟨rfl, -, -⟩ | ⟨-, rfl, -, hpcs, -⟩
          · obtain ⟨w, hw, hw0⟩ := hσ0.nz oc hnzc
            exact hw0 (rd_get hκ hm.fine soc (by rw [hm.fp]; exact hw) hvc).symm
          · have hcall := List.all_eq_true.mp hok.calls _ (List.getElem_mem hi)
            rw [hcode] at hcall
            obtain ⟨hout, ht30, -⟩ := jumpCallOk_spec hcall hpt (entOk_spec hentF)
            have := rd_get hκ hm.fine sod (by rw [hm.fp]; exact hσ0.pcw od t hpt) hvd
            have hpe : s'.pc = t := gpow_inj (by omega) (by omega) (pow_of_ofK this)
            exact hout ⟨by rw [← hpe, hpc', hpcF]; omega, by rw [← hpe, hpc', hpcF, hlen]; omega⟩
      refine k s1 s' (he1 s1 e1) hm hmo e' hf' hle' (.move (i + 1) (hfp'.trans hm.fp.symm) hi1
        (by rw [hpc', hpc]; omega) (coreAt_of ⟨atF_mono (s := s') (Mem.le_refl _) rfl hat',
          fun o ho ↦ by rw [hfp']; exact written_mono hle (hentw o ho), fun σ hσ ↦ ?_⟩))
      rw [hfp'] at hσ
      obtain ⟨pos, pre, es, vs, rd, hpos, hb, hwp, hh0, hW⟩ := hheap σ hσ
      obtain ⟨pos', hpos', as, hpairs, hfallP⟩ := pair_fallC (sigOf := Cf.sigOf) (rd := rd)
        (ws0 := Cf.fn.params.map σ) hok.pair hpos hnj
      obtain ⟨evs, es', rfl, hwp', hWr⟩ := hfallP hwp (hrwOf σ pre _ vs rd hb hh0)
      refine ⟨pos', pre ++ evs, es', vs, rd, hpos', by rw [List.append_assoc]; exact hb, hwp',
        by rw [List.append_assoc]; exact hh0, fun y hy ↦ ?_⟩
      rcases hWr y hy with h | ⟨a, ha', hfa', hma, hwa⟩ | ⟨o1, o2, o3, dv, pv, off, hci, hS, hcell, hmem, rfl⟩
      · exact (hW y h).mono hle
      · rw [hhd i] at hpairs
        exact (flow_wrk hκ e1 hs hm hpairs ha' hfa' (fun q hq ↦ hσ.ptr _ _ hb a q
          (List.mem_append_right _ (List.mem_append_left _ hma)) hq) hwa).mono hle'
      · obtain ⟨p, x, hp, hx, hw⟩ := hstw o1 o2 o3 hci (by rw [has_hasP]; exact hS)
        simp only [cellsAt, Bool.and_eq_true, Nat.beq_eq] at hcell
        obtain ⟨⟨hloc, hoff⟩, -⟩ := hcell
        have hsm := hok.small i hi
        rw [List.getElem?_eq_getElem hi, Option.some.injEq] at hci
        rw [hci] at hsm
        obtain ⟨so1, -, -⟩ := hsm
        have hrd : Rd img s'.fp o1 = some (σ pv) := by
          rw [hfp', ← hloc]
          exact hσ.ptr _ _ hb (.load dv pv off) pv (List.mem_append_right _ (List.mem_append_left _ hmem)) rfl
        have hpv : p = σ pv := rd_get hκ hf' so1 hrd hp
        refine ⟨x, ?_, hx.2, hw⟩
        have h1 := hx.1
        rw [limb0_mul_ofK, hpv, ← hoff] at h1
        exact h1
    · -- a jump taken
      intro s1 s' e1 hm hmo e' hf' hle' hjo hjt
      obtain ⟨oc, od, of, hci, h0, h1, hpcs⟩ := hjt
      have hcode : K.code[i] = .jump oc od of := Option.some.inj ((List.getElem?_eq_getElem hi).symm.trans hci)
      have hsm := hok.small i hi
      rw [hcode] at hsm
      obtain ⟨soc, sod, sof⟩ := hsm
      have hw1 : ∀ o ∈ K.F.sig.entry, s1.mem.written (s1.fp + o) = true := fun o ho ↦ by
        rw [hm.fp]; exact written_mono hm.le (hentw o (hok.fsig ▸ ho))
      rcases retLast_jump hret hci with ⟨-, rfl, rfl, hz, hfw⟩ | ⟨hi1, hz, hfw, hnr⟩
      · -- the return
        have hrj : ∃ c, K.code[i]? = some (.jump c 0 1) := ⟨oc, hci⟩
        cases hjo with
        | «local» t hnr => exact absurd hrj hnr
        | halt hnr => exact absurd hrj hnr
        | tail e hnr => exact absurd hrj hnr
        | call G t hnr => exact absurd hrj hnr
        | ret _ hregs hretw =>
          refine k s1 s' (he1 s1 e1) hm hmo e' hf' hle' (.ret oc hci (by omega) h0 h1 ?_)
          obtain ⟨pos, pre, es, vs, rd, hpos, hb, hwp, hh0, hW⟩ := hheap σ0 hσ0
          obtain ⟨-, hreads, hposts, hpostRs, hretM⟩ := heapK_sound hok.heap hok.pows hstC hb hh0
          obtain ⟨as, hpairs, hpr⟩ := pair_retC hok.pair hpos hci hz (by simpa using hfw) hpc0 hstC hwp hreads
          rw [hhd i] at hpairs
          have W1 : ∀ x, WrittenC Cf.sigOf Cf.H rd σ0 (Cf.fn.params.map σ0) (pre ++ es) x → WrK s1.mem x := by
            intro x hx
            rcases hpr x hx with h | ⟨a, ha, hfa, hma, hwa⟩
            · exact (hW _ h).mono hm.le
            · exact flow_wrk hκ e1 hs hm hpairs ha hfa
                (fun q hq ↦ hσ0.ptr _ _ hb a q (List.mem_append_right _ hma) hq) hwa
          have hvl : vs.length = retN Cf.fn.body := retsN_len hstC hrN hb
          have hws : ∀ b < np + retN Cf.fn.body, Rd img s1.fp (2 + b) =
              some (slotW (Cf.fn.params.map σ0 ++ vs.map σ0) b) := by
            intro b hb'
            rw [hm.fp]
            by_cases hb1 : b < np
            · rw [slotW_lt (by simpa using hb1)]; exact hws0 hσ0 b hb1
            · rw [slotW_append]
              simp only [List.length_map, show ¬ b < Cf.fn.params.length from hb1, ↓reduceIte]
              rw [slotW_get (by simp; omega)]
              have := hσ0.retc _ _ hb (b - np) (by omega)
              rw [show 2 + Cf.fn.params.length + (b - np) = 2 + b by omega] at this
              simpa using this
          have hSG : ∀ {m : Mode.Mono}, monoR K.F.sig np (retN Cf.fn.body) m = true →
              SlotGet (Mode.stOf s1.mem s1.fp) (Cf.fn.params.map σ0 ++ vs.map σ0) m.bs :=
            fun hm' ↦ slotGet_ret (s := Mode.stOf s1.mem s1.fp) hκ hm.fine.agree hm.fine.fp hws hw1
              (fun o ho ↦ hretw o (hok.fsig ▸ ho)) hm'
          refine ⟨⟨fun o ho ↦ hretw o (hok.fsig ▸ ho), fun m hm' ↦ ?_, fun r hr ↦ ?_, fun q hq ↦ ?_,
            fun p hp ↦ ?_, fun p hp ↦ ?_, fun q hq ↦ ?_⟩, fun r hr ↦ ?_, fun q hq ↦ ?_⟩
          · obtain ⟨hmR, hc⟩ := hpost m hm'
            split at hc
            · rename_i c hmc
              obtain ⟨c', hc', hbeq⟩ := List.any_eq_true.mp hc
              rw [CCell.beq_eq hbeq] at hc'
              exact slot_hw hmc (hSG hmR) (W1 _ (hposts c hc'))
            · cases hc
          · obtain ⟨hmR, h⟩ := hpostR r hr
            rcases Bool.or_eq_true_iff.mp h with h | h
            · obtain ⟨q, hq, hrq⟩ := List.any_eq_true.mp h
              unfold rngIs at hrq
              split at hrq
              · rename_i q' hq'
                obtain rfl := of_decide_eq_true hrq
                exact slot_rw hq' (hSG hmR) fun x hx ↦ W1 x (hpostRs q' hq x hx)
              · cases hrq
            · split at h
              · rename_i c l hmc hl
                exact pts_slot hmc hl (hSG hmR) fun p hp ↦ by
                  obtain ⟨c', hc', hbeq⟩ := List.any_eq_true.mp (List.all_eq_true.mp h p hp)
                  rw [← CCell.beq_eq hbeq]
                  exact W1 _ (hposts c' hc')
              · cases h
          · rw [hpostP] at hq; cases hq
          · obtain ⟨h28, hret', hmo', c, hmc, hcase⟩ := retVOk_sound hok.pows hok.retv hb hh0 p hp
            obtain ⟨u, hu⟩ := Mem.get_of_written (hretw p.1 (hok.fsig ▸ hret'))
            have hSG0 : SlotGet (Mode.stOf s1.mem s1.fp) (Cf.fn.params.map σ0) p.2.bs :=
              slotGet_of (s := Mode.stOf s1.mem s1.fp) hκ hm.fine.agree hm.fine.fp
                (fun b hb' ↦ by rw [hm.fp]; exact hws0 hσ0 b hb') hw1 hmo'
            refine ⟨u, hu, ?_⟩
            have hval := monoVal_slot' hmc hSG0
            suffices hu' : u = c.valW (slotW (Cf.fn.params.map σ0)) by rw [hu']; exact hval
            rcases hcase with ⟨v, hv, hloc, hvv⟩ | ⟨h2, hrm⟩
            · have hrd : Rd img s1.fp p.1 = some (σ0 v) := by
                rw [hm.fp, ← hloc]; exact hσ0.rets _ _ hb v hv
              rw [rd_get hκ hm.fine h28 hrd hu, hvv, val_eq]
              refine valW_congr fun b hb' ↦ ?_
              rw [slotW_params' hpar (monoC_bases_lt hmo' hmc b hb')]
              rfl
            · have hk := hretM _ c hrm
              rw [List.getElem?_map] at hk
              obtain ⟨v, hv, hvv⟩ := Option.map_eq_some_iff.mp hk
              have hkl : p.1 - 2 - np < vs.length := (List.getElem?_eq_some_iff.mp hv).1
              have hrd := hσ0.retc _ _ hb (p.1 - 2 - np) hkl
              rw [show 2 + Cf.fn.params.length + (p.1 - 2 - np) = p.1 by omega, hm.fp.symm] at hrd
              rw [rd_get hκ hm.fine h28 hrd hu, (List.getElem?_eq_some_iff.mp hv).2, hvv]
          · rw [hpostT] at hp; cases hp
          · rw [hpostC] at hq; cases hq
          · rw [hpostL] at hr; cases hr
          · rw [hpostLP] at hq; cases hq
      · -- a call
        obtain ⟨pos, pre, es, vs, rd, hpos, hb, hwp, hh0, hW⟩ := hheap σ0 hσ0
        obtain ⟨f, args, rets, st, t, o, pos', hsite, hpt, hentF, hnzc, hfo, hat', as, hpairs, hkC⟩ :=
          pair_callC hok.pair hpos hci hz (by simpa using hfw) hnr hmainX hstC
        rw [hhd i] at hpairs
        have hcall := List.all_eq_true.mp hok.calls _ (List.getElem_mem hi)
        rw [hcode] at hcall
        obtain ⟨hout, ht30, G, st', hG, hst', hr30, hfit⟩ := jumpCallOk_spec hcall hpt (entOk_spec hentF)
        obtain ⟨hst'', hna, hnr'⟩ := siteAt_spec hsite
        rw [hst''] at hst'
        cases hst'
        rw [hna, hnr'] at hfit
        simp only [fitB, Bool.and_eq_true, Option.isNone_iff_eq_none, List.isEmpty_iff, List.contains_iff_mem,
          List.all_eq_true] at hfit
        obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hGself, hGpreP⟩, hG0⟩, hG1⟩, hhpostP⟩, hhpostPR⟩, hhretM⟩, hGpre⟩, hGpreR⟩, hhpost⟩,
          hhpostR⟩ := hfit
        have hpe : s'.pc = t := by
          have := rd_get hκ hm.fine sod (by rw [hm.fp]; exact hσ0.pcw od t hpt) h0
          exact gpow_inj (by omega) (by omega) (pow_of_ofK this)
        -- the walk's split at the call, the callee frame
        have hsplit : ∀ {σ : Val} {pre es : List Ev} {vs : List V} {rd : Reader}, HonF img Cf s.fp σ →
            pairAt Cf.P Cf.fn.body K.code Cf.d i = some pos → walk σ Cf.fn.body = .ret (pre ++ es) vs →
            walk σ pos = .ret es vs → (∀ e ∈ pre ++ es, e.Holds rd σ) →
            ∃ (evs : List Ev) (cs : List Atom) (es' : List Ev), es = evs ++ Ev.call f args rets :: (cs.map Ev.atom ++ es') ∧
              walk σ pos' = .ret es' vs ∧ (∀ a ∈ cs, stopL a = false) ∧ (∀ a ∈ as, Ev.atom a ∈ evs) ∧
              (∀ x, WrittenC Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) (pre ++ evs) x →
                WrittenC Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) pre x ∨
                ∃ a ∈ as, flowAtom a = true ∧ Ev.atom a ∈ evs ∧ Writes σ a x) ∧
              ReqOk Cf.sigOf Cf.H rd σ (WrittenC Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) (pre ++ evs))
                (.call f args rets) ∧
              ∃ kfp, (g : Parameters.K) ^ s'.fp = g ^ kfp ∧
                (∀ b < args.length + rets.length, Rd img s'.fp (2 + b) = some (slotW ((args ++ rets).map σ) b)) ∧
                Rd img s'.fp 0 = some (ofK (g ^ st.r)) ∧ Rd img s'.fp 1 = some (ofK (g ^ s.fp)) := by
          intro σ pre es vs rd hσ hp hb hwp hh0
          obtain ⟨evs, cs, es', rfl, hwp', hcs, hasin, hW'⟩ := hkC hwp (hrwOf σ pre _ vs rd hb hh0)
          have hreq := hrwOf σ pre _ vs rd hb hh0 (pre ++ evs) (.call f args rets) (cs.map Ev.atom ++ es')
            (by simp)
          obtain ⟨kfp, hq, hk0, hk1, hargs, hrets⟩ := hσ.kid _ _ hb ((calls (pre ++ evs)).length)
            ⟨f, args, rets, true⟩ of st (by rw [← List.append_assoc]; exact calls_mid) rfl hsite
          have hfpE : (g : Parameters.K) ^ s'.fp = g ^ kfp :=
            (pow_of_ofK (rd_get hκ hm.fine sof (by rw [hm.fp]; exact hq) h1)).symm.symm
          refine ⟨evs, cs, es', rfl, hwp', hcs, hasin, hW', hreq, kfp, hfpE, fun b hb' ↦ ?_,
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
        obtain ⟨evs, cs, es', heq, hwp', hcs, hasin, hW', hreq, kfp, hfpE, hwsE, hk0, hk1⟩ :=
          hsplit hσ0 hpos hb hwp hh0
        have hWs1 : ∀ x, WrittenC Cf.sigOf Cf.H rd σ0 (Cf.fn.params.map σ0) (pre ++ evs) x → WrK s1.mem x := by
          intro x hx
          rcases hW' x hx with h | ⟨a, ha, hfa, hma, hwa⟩
          · exact (hW _ h).mono hm.le
          · subst heq
            exact flow_wrk hκ e1 hs hm hpairs ha hfa (fun q hq ↦ hσ0.ptr _ _ hb a q
              (List.mem_append_right _ (List.mem_append_left _ hma)) hq) hwa
        cases hjo with
        | ret hr _ _ =>
          obtain ⟨c', hc'⟩ := hr
          rw [hci, Option.some.injEq, OffsetInstruction.jump.injEq] at hc'
          exact absurd ⟨hc'.2.1, hc'.2.2⟩ hnr
        | «local» t' _ _ hpc'' hat'' =>
          exfalso
          have ht' : K.code.length ≤ t' := by
            by_contra hlt
            exact hout ⟨by rw [← hpe, hpc'']; omega, by rw [← hpe, hpc'', hlen]; omega⟩
          obtain ⟨cur, pend, h0', hh0'⟩ := hat''
          obtain ⟨rfl, rfl⟩ := preF_end hacc ht' h0'
          rcases hh0' with ⟨A, hA, -⟩ | ⟨g', hg', -⟩
          · cases hA
          · cases hg'
        | halt _ hfpo _ => exact absurd hfpo (by simp [hfp1])
        | tail e _ hpc'' _ _ _ _ _ =>
          exfalso
          exact hout ⟨by rw [← hpe, hpc''], by rw [← hpe, hpc'', hlen]; omega⟩
        | call G' t' _ htl hsig hentry hrr hcont =>
          rw [hpe, hG, Option.some.injEq] at hsig
          subst hsig
          -- the return offset
          have ht'r : st.r = K.F.entry + t' := by
            have h2 := hrr
            unfold retRegs at h2
            rw [show img.read (g ^ s'.fp * addressOfIndex 0) = Rd img s'.fp 0 from rfl, hk0] at h2
            simp only [Option.bind_some] at h2
            obtain ⟨fw, -, hfw'⟩ := Option.map_eq_some_iff.mp h2
            simp only [Registers.mk.injEq, limb_ofK] at hfw'
            rw [← hok.fentry]
            exact gpow_inj (by omega) (by omega) hfw'.1
          obtain ⟨-, hoo⟩ := fwdOff_spec hfo
          rw [hok.xentry, ht'r, show K.F.entry + t' - K.F.entry = t' by omega] at hoo
          subst hoo
          have hsigK : K.E.sigs.get s'.pc = some G := by rw [← hok.fsigs, hpe]; exact hG
          refine k s1 s' (he1 s1 e1) hm hmo e' hf' hle' (.call fun hTE ↦ ⟨G, o, hsigK, by omega, ?_, ?_,
            hentry.w, ?_, ?_⟩)
          · obtain ⟨u, hu⟩ := Mem.get_of_written (hentry.w 0 hG0)
            rw [hu, rd_get hκ hf' (by norm_num) hk0 hu, ht'r]
          · obtain ⟨u, hu⟩ := Mem.get_of_written (hentry.w 1 hG1)
            rw [hu, rd_get hκ hf' (by norm_num) hk1 hu, hm.fp]
          · -- the callee's entry facts
            have hA : entryAbs K.E G = ⟨Mode.foldlT .nil G.entry, .nil, .nil, [], G.pre,
                Mode.jtRng K.E :: G.preR, G.term, [], .nil, G.preP, []⟩ := by
              unfold entryAbs
              rw [hGself]
            rw [hA]
            have hSG : ∀ {m : Mode.Mono}, monoS G args.length true m = true →
                SlotGet s' (args.map σ0) m.bs := fun hm' ↦
              slotGet_of hκ hf'.agree hf'.fp (fun b hb' ↦ by
                rw [hwsE b (by omega), List.map_append, slotW_lt (by simpa using hb')]) hentry.w hm'
            have hW1 : ∀ x, WrittenC Cf.sigOf Cf.H rd σ0 (Cf.fn.params.map σ0) (pre ++ evs) x → WrK s'.mem x :=
              fun x hx ↦ (hWs1 x hx).mono hle'
            obtain ⟨⟨hrpre, hrpreR⟩, -⟩ := hreq
            refine ⟨fun o ho ↦ hentry.w o (foldlT_nil_get ho), fun o x hx ↦ (by rw [trieNil_get rfl] at hx; cases hx),
              fun o hx ↦ (by rw [trieNil_get rfl] at hx; cases hx), fun p hp ↦ (by cases hp), fun m hm' ↦ ?_,
              fun r hr ↦ ?_, fun p hp ↦ ?_, fun p hp ↦ (by cases hp), fun c a b hx ↦ (by rw [trieNil_get rfl] at hx; cases hx),
              fun q hq ↦ (by rw [hGpreP] at hq; cases hq), fun q hq ↦ (by cases hq)⟩
            · obtain ⟨hmS, hc⟩ := hGpre m hm'
              split at hc
              · rename_i c hmc
                obtain ⟨c', hc', hbeq⟩ := List.any_eq_true.mp hc
                rw [CCell.beq_eq hbeq] at hc'
                exact slot_hw hmc (hSG hmS) (hW1 _ (hrpre c hc'))
              · cases hc
            · rcases List.mem_cons.mp hr with rfl | hr
              · exact hjtR s' (Mem.le_trans hm.le hle')
              obtain ⟨hmS, h⟩ := hGpreR r hr
              rcases Bool.or_eq_true_iff.mp h with h | h
              · obtain ⟨q, hq, hrq⟩ := List.any_eq_true.mp h
                unfold rngIs at hrq
                split at hrq
                · rename_i q' hq'
                  obtain rfl := of_decide_eq_true hrq
                  exact slot_rw hq' (hSG hmS) fun x hx ↦ hW1 x (hrpreR q' hq x hx)
                · cases hrq
              · split at h
                · rename_i c l hmc hl
                  exact pts_slot hmc hl (hSG hmS) fun p hp ↦ by
                    obtain ⟨c', hc', hbeq⟩ := List.any_eq_true.mp (List.all_eq_true.mp h p hp)
                    rw [← CCell.beq_eq hbeq]
                    exact hW1 _ (hrpre c' hc')
                · cases h
            · exact Mode.LTF.mono (s := Mode.stOf s'.mem s'.fp) (s' := s') (Mem.le_refl _) rfl
                (hTE G hsigK hentry.w p hp)
          · -- resumed once the callee guarantees its signature
            intro m hm0 hwf hu hfpE hfpC hR hL hLP hT m' hm' ham'
            have hle0 : s.mem ≤ m' := Mem.le_trans hm.le (Mem.le_trans hle' (Mem.le_trans hm0 hm'))
            refine ⟨?_, fun o' ho' ↦ ?_, fun σ hσ ↦ ?_⟩
            · have := hcont { Mode.stOf m' s1.fp with pc := Cf.frame.entry + o }
                ⟨ham', Prover.Exec.Dlog.ok_empty, Prover.Exec.Dlog.small_empty, hfpC⟩ rfl rfl
                (Mem.le_trans hle' (Mem.le_trans hm0 hm')) (fun o' ho' ↦ written_mono hm' (hR.1 o' ho'))
              exact atF_mono (s := { Mode.stOf m' s1.fp with pc := Cf.frame.entry + o }) (Mem.le_refl _) rfl this
            · show m'.written (s1.fp + o') = true
              rw [hm.fp]; exact written_mono hle0 (hentw o' ho')
            · change HonF img Cf s1.fp σ at hσ
              rw [hm.fp] at hσ
              obtain ⟨pos2, pre2, es2, vs2, rd2, hpos2, hb2, hwp2, hh2, hW2⟩ := hheap σ hσ
              rw [hpos, Option.some.injEq] at hpos2
              subst hpos2
              obtain ⟨evs2, cs2, es2', rfl, hwp2', hcs2, hasin2, hW2', -, kfp2, hfpE2, hwsE2, -, -⟩ :=
                hsplit hσ hpos hb2 hwp2 hh2
              refine ⟨pos', pre2 ++ evs2 ++ Ev.call f args rets :: cs2.map Ev.atom, es2', vs2, rd2, hat',
                by simpa using hb2, hwp2', by simpa using hh2, fun y hy ↦ ?_⟩
              rcases writtenC_append hy with h | ⟨e, he, hwe⟩
              · rcases hW2' y h with h | ⟨a, ha, hfa, hma, hwa⟩
                · exact (hW2 y h).mono hle0
                · exact ((flow_wrk hκ e1 hs hm hpairs ha hfa (fun q hq ↦ hσ.ptr _ _ hb2 a q
                    (List.mem_append_right _ (List.mem_append_left _ hma)) hq) hwa).mono
                    (Mem.le_trans hle' (Mem.le_trans hm0 hm')))
              rcases List.mem_cons.mp he with rfl | he
              · -- the callee's guarantees
                have hSE : ∀ {m0 : Mode.Mono}, monoS G (args.length + rets.length) false m0 = true →
                    SlotEq (Mode.stOf m' s'.fp) ((args ++ rets).map σ) m0.bs := fun hm1 ↦
                  slotEq_of (s := Mode.stOf m' s'.fp) hκ ham' hf'.fp hwsE2 hm1
                have hRm : ∀ {s3 : St}, s3 = Mode.stOf m' s'.fp → Mode.stOf m s'.fp = Mode.stOf m s'.fp := fun _ ↦ rfl
                rcases hwe with (⟨c, hc, rfl⟩ | ⟨r, hr, hx⟩) | (⟨p, hp, -⟩ | ⟨p, hp, -⟩)
                · rcases Bool.or_eq_true_iff.mp (hhpost c hc) with h | h
                  · obtain ⟨m0, hm0', hmc⟩ := List.any_eq_true.mp h
                    rw [Bool.and_eq_true] at hmc
                    obtain ⟨hmS, hmc⟩ := hmc
                    unfold monoIs at hmc
                    split at hmc
                    · rename_i c' hc'
                      rw [← CCell.beq_eq hmc]
                      exact hw_slot hc' (hSE hmS) (Mode.HW.mono (s := Mode.stOf m s'.fp) (s' := Mode.stOf m' s'.fp)
                        hm' rfl (hR.2.1 m0 hm0'))
                    · cases hmc
                  · obtain ⟨r, hr, hrc⟩ := List.any_eq_true.mp h
                    rw [Bool.and_eq_true] at hrc
                    exact ptIn_slot hrc.2 (hSE hrc.1) (Mode.RW.mono (s := Mode.stOf m s'.fp)
                      (s' := Mode.stOf m' s'.fp) hm' rfl (hR.2.2.1 r hr))
                · obtain ⟨r', hr', hrq⟩ := List.any_eq_true.mp (hhpostR r hr)
                  rw [Bool.and_eq_true] at hrq
                  obtain ⟨hmS, hrq⟩ := hrq
                  unfold rngIs at hrq
                  split at hrq
                  · rename_i q hq
                    obtain rfl := of_decide_eq_true hrq
                    exact rw_slot hq (hSE hmS) (Mode.RW.mono (s := Mode.stOf m s'.fp) (s' := Mode.stOf m' s'.fp)
                      hm' rfl (hR.2.2.1 r' hr')) y hx
                  · cases hrq
                · rw [hhpostP] at hp; cases hp
                · rw [hhpostPR] at hp; cases hp
              · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
                exact absurd hwe (no_writes_of_stopL (hcs2 a ha))

end

end LeanVM.Guest.CoreMode
