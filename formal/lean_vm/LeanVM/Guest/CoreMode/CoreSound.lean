/-
  LeanVM.Guest.CoreMode.CoreSound

  The core route meets the frame interface: `frameSpec_core`.
-/

module

public import LeanVM.Guest.CoreMode.CoreSlot
public import LeanVM.Guest.CoreMode.CorePtr
public import LeanVM.Guest.CoreMode.CoreLink
public import LeanVM.Guest.CoreMode.Core
public import LeanVM.Guest.CoreMode.PairJumpC
public import LeanVM.Guest.CoreMode.PairCallIf
public import LeanVM.Guest.CoreMode.WalkS

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
  return, the last instruction, with the signature's guarantees (`pair_retC`); a call or a conditional
  call entered (`pair_callAny`): the callee's mode signature's entry facts from its heap signature's
  preconditions (`jumpCallOk`, `fitB`; a loop's self cell from the frame walk, `holds_entryAbs`), and the
  caller resumed in any memory agreeing with the reference past the callee's guarantees (`Resume`, a
  loop's runs among them), the callee frame's cells holding the call's words (`HonF.kid`); a conditional
  call skipped falls through (`core_jfall`).
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

theorem rd_pow {img : MemoryImage κ} {a b : ℕ} (h : (g : K) ^ a = g ^ b) (o : ℕ) : Rd img a o = Rd img b o := by
  simp only [Rd, h]

theorem pow_of_ofK {a b : ℕ} (h : ofK ((g : K) ^ a) = ofK (g ^ b)) : (g : K) ^ a = g ^ b :=
  ofK_injective h

/-! ## The heap facts -/

/-- **The guarantees at return written by the events** (`PostOkC` without frame run cells). -/
def PostOkW (sigOf : String → HSig) (H : HCert) (rd : Reader) (σ : Val) (ws0 : List E) (es : List Ev)
    (vs : List V) : Prop :=
  SigOk (WrittenC sigOf H rd σ ws0 es) H.sig.post H.sig.postR (ws0 ++ vs.map σ) ∧
    PtrOk (WrittenC sigOf H rd σ ws0 es) rd H.sig.postP H.sig.postPR (ws0 ++ vs.map σ)

/-- A body without `frameAddr` atoms guarantees no frame run cell (`FAW`). -/
theorem noFAW {body : List Stmt} (h : noFA body = true) {σ : Val} {es : List Ev} {vs : List V}
    (hw : walk σ body = .ret es vs) (x : K) : ¬ FAW σ es x := by
  rintro ⟨p, run, i, v, he, -⟩
  have hs := Bridge.walk_atomS body (by rw [hw]; exact he)
  have := List.all_eq_true.mp h _ hs
  simp at this

theorem postOkW_of {sigOf : String → HSig} {H : HCert} {rd : Reader} {σ : Val} {ws0 : List E} {es : List Ev}
    {vs : List V} (hn : ∀ x, ¬ FAW σ es x) (h : PostOkC sigOf H rd σ ws0 es vs) : PostOkW sigOf H rd σ ws0 es vs :=
  ⟨h.1.mono fun x hx ↦ hx.resolve_right (hn x), fun x hx ↦ (h.2 x hx).resolve_right (hn x)⟩

/-- A call needs its callee's preconditions written, no word at a cell (`HCert.ders`) among its ghosts. -/
theorem callReq_pre {sigOf : String → HSig} {H : HCert} {rd : Reader} {σ : Val} {W : K → Prop} {g : String}
    {args : List V} (hd : H.ders = []) (h : CallReq sigOf H rd σ W g args) : CallPre sigOf H rd σ W g args :=
  h.2 fun k _ c hc ↦ by rw [hd] at hc; cases hc

/-- What made a call event of a body the core route takes: a `call` statement, or a `callIf`
returning nothing. -/
theorem body_callS {body : List Stmt} (_hb : bodyC body = true) {σ : Val} {es : List Ev} {vs : List V}
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
    callChk Cf f a = true := by
  rcases hs with hs | ⟨-, c, hs⟩ | ⟨x, fs, hs, hf⟩
  · exact List.all_eq_true.mp hcb _ hs
  · exact List.all_eq_true.mp hcb _ hs
  · have := List.all_eq_true.mp hcb _ hs
    simp only [Bool.and_eq_true] at this
    exact List.all_eq_true.mp this.1 f hf

/-- **The heap facts of an honest path**, each call's callee's returned words given: its parameters `V.n k`;
every event's needs written before it; the promised cells and the signature's runs written by the end, at the
parameters' and returned words; the returned words' monomials, words and equations. -/
theorem heapK_sound {Cf : CFun} (hk : HeapK Cf) (hp : Cf.pows.Ok) (hst : bodyC Cf.fn.body = true) {σ : Val}
    {rd : Reader} {es : List Ev} {vs : List V} (hw : walk σ Cf.fn.body = .ret es vs) (hh : ∀ e ∈ es, e.Holds rd σ)
    (hR : ResF Cf.H σ) (hM : ∀ e ∈ es, EvM Cf.sigOf rd σ e) :
    Cf.fn.params = (List.range Cf.fn.params.length).map V.n ∧
    ReadsOkC Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) es ∧
    (∀ c ∈ Cf.posts, WrittenC Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) es
      (c.addrW (slotW (Cf.fn.params.map σ ++ vs.map σ)))) ∧
    (∀ r ∈ Cf.H.sig.postR, ∀ x, r.Set (slotW (Cf.fn.params.map σ ++ vs.map σ)) x →
      WrittenC Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) es x) ∧
    RetMOk Cf.H.sig (Cf.fn.params.map σ) (vs.map σ) ∧
    (∀ p ∈ Cf.post, WrittenC Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) es (p.1.addr σ)) ∧
    PtrOk (WrittenC Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) es) rd Cf.H.sig.postP Cf.H.sig.postPR
      (Cf.fn.params.map σ ++ vs.map σ) ∧
    RetVOk rd Cf.H.sig (Cf.fn.params.map σ ++ vs.map σ) ∧ RetEqOk Cf.H.sig (Cf.fn.params.map σ ++ vs.map σ) := by
  cases hk with
  | m1 hok hpo hstr0 hrm hpv hre =>
    simp only [Bool.and_eq_true, List.isEmpty_iff] at hstr0
    obtain ⟨⟨hstr, hpP⟩, hpPR⟩ := hstr0
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
    refine ⟨hpar', fun es1 e es2 he ↦ ?_, fun c hc ↦ ?_, fun r hr ↦ (by rw [hpostR] at hr; cases hr),
      fun k c hkc ↦ (by rw [hrm] at hkc; cases hkc), fun p hp' ↦ hconv _ _ (postOk_sound hp hpo hw hh p hp'),
      ⟨fun x hx ↦ (by
        rcases hx with ⟨p, hp', -⟩ | ⟨p, hp', -⟩
        · rw [hpP] at hp'; cases hp'
        · rw [hpPR] at hp'; cases hp'),
      fun i m him ↦ (by rw [hpv] at him; cases him), fun p hp' ↦ (by rw [hre] at hp'; cases hp')⟩⟩
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
  | c hok hterm hcb hpost hders hnofa =>
    have hok' := hok
    unfold heapOkC at hok'
    simp only [Bool.and_eq_true] at hok'
    obtain ⟨⟨⟨⟨⟨hpar, -⟩, -⟩, -⟩, -⟩, -⟩ := hok'
    have hpar' : Cf.fn.params = (List.range Cf.fn.params.length).map V.n := by
      rw [List.range_eq_range']; exact paramsN_eq _ 0 hpar
    have hself : Cf.sigOf Cf.fn.name = Cf.H.sig := by simp [CFun.sigOf]
    obtain ⟨hreads, hpo, hretm, hrv, hre⟩ := heapOkC_sound hp hok hself hw hh hM
      (fun p hp ↦ (by rw [hterm] at hp; cases hp)) hR (derOk_nil hders rd σ)
    have hW : PostOkW Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) es vs := by
      rcases Bool.or_eq_true_iff.mp hnofa with h | h
      · exact postOkW_of (noFAW h hw) hpo
      · simp only [noPost, Bool.and_eq_true, List.isEmpty_iff] at h
        obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
        refine ⟨⟨fun c hc ↦ by simp [h1] at hc, fun r hr ↦ by simp [h2] at hr⟩, fun x hx ↦ ?_⟩
        simp [PtrSigSet, h3, h4] at hx
    obtain ⟨⟨hpc, hpr⟩, hptr⟩ := hW
    refine ⟨hpar', hreads, fun c hc ↦ ?_, fun r hr x hx ↦ hpr r hr x hx, hretm,
      fun p hp' ↦ (by rw [hpost] at hp'; cases hp'), hptr, hrv, hre⟩
    simp only [CFun.posts, hpost, List.map_nil, List.filter_nil, List.nil_append] at hc
    exact hpc c hc

/-- **Every event's needs on an honest path are written before it**, once the calls before it have their
callees' returned words. -/
theorem heapK_reads {Cf : CFun} (hk : HeapK Cf) (hp : Cf.pows.Ok) (hst : bodyC Cf.fn.body = true) {σ : Val}
    {rd : Reader} {es : List Ev} {vs : List V} (hw : walk σ Cf.fn.body = .ret es vs) (hh : ∀ e ∈ es, e.Holds rd σ)
    (hR : ResF Cf.H σ) : ReadsOkP Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) es := by
  cases hk with
  | m1 hok hpo hstr0 hrm hpv hre =>
    have hM : ∀ e ∈ es, EvM Cf.sigOf rd σ e := fun e he ↦ by
      cases e with
      | call f args rets =>
        simp only [Bool.and_eq_true] at hstr0
        rcases body_callS hst hw he with h | ⟨-, c, h⟩ | ⟨x, fs, h, -⟩ <;>
          simpa [isCall] using List.all_eq_true.mp hstr0.1.1 _ h
      | _ => trivial
    exact fun es1 e es2 he _ ↦
      (heapK_sound (.m1 hok hpo hstr0 hrm hpv hre) hp hst hw hh hR hM).2.1 es1 e es2 he
  | c hok hterm hcb hpost hders hnofa =>
    exact (heapOkC_soundP hp hok (by simp [CFun.sigOf]) hw hh
      (fun p hp ↦ (by rw [hterm] at hp; cases hp)) hR (derOk_nil hders rd σ)).1

/-- A path through a call: the function's heap check is the one with calls. -/
theorem callsB_of {Cf : CFun} (hk : HeapK Cf) (hst : bodyC Cf.fn.body = true) {σ : Val} {es : List Ev}
    {vs : List V} (hw : walk σ Cf.fn.body = .ret es vs) {f : String} {args rets : List V}
    (he : Ev.call f args rets ∈ es) : callsB Cf = true := by
  cases hk with
  | m1 _ _ hstr0 _ _ _ =>
    simp only [Bool.and_eq_true] at hstr0
    rcases body_callS hst hw he with h | ⟨-, c, h⟩ | ⟨x, fs, h, -⟩ <;>
      simpa [isCall] using List.all_eq_true.mp hstr0.1.1 _ h
  | c _ _ hcb _ _ _ => exact hcb

theorem callsB_of' {Cf : CFun} (hk : HeapK Cf) : callsB Cf = true := by
  cases hk with
  | m1 _ _ hstr0 _ _ _ =>
    simp only [Bool.and_eq_true] at hstr0
    refine List.all_eq_true.mpr fun s hs ↦ ?_
    have := List.all_eq_true.mp hstr0.1.1 s hs
    cases s <;> simp_all [isCall]
  | c _ _ hcb _ _ _ => exact hcb

/-- A path through a call: no word at a cell among the heap certificate's ghosts. -/
theorem ders_of {Cf : CFun} (hk : HeapK Cf) (hst : bodyC Cf.fn.body = true) {σ : Val} {es : List Ev}
    {vs : List V} (hw : walk σ Cf.fn.body = .ret es vs) {f : String} {args rets : List V}
    (he : Ev.call f args rets ∈ es) : Cf.H.ders = [] := by
  cases hk with
  | m1 _ _ hstr0 _ _ _ =>
    simp only [Bool.and_eq_true] at hstr0
    rcases body_callS hst hw he with h | ⟨-, c, h⟩ | ⟨x, fs, h, -⟩ <;>
      simpa [isCall] using List.all_eq_true.mp hstr0.1.1 _ h
  | c _ _ _ _ hd _ => exact hd

/-- **A call's callee runs' bounds have exponents** (`callsB`'s `idxPow`). -/
theorem callsB_spec {Cf : CFun} (hcb : callsB Cf = true) {f : String} {args rets : List V}
    (hs : Stmt.call f args rets ∈ stmtsOf Cf.fn.body ∨
      (rets = [] ∧ ∃ c, Stmt.callIf c f args ∈ stmtsOf Cf.fn.body) ∨
      ∃ x fs, Stmt.dispatch x fs args rets ∈ stmtsOf Cf.fn.body ∧ f ∈ fs) :
    (∀ q ∈ (Cf.sigOf f).preR, (idxPowC Cf args q.lo && idxPowC Cf args q.hi) = true) ∧
    ∀ p ∈ (Cf.sigOf f).prePR, (idxPowC Cf args p.1.lo && idxPowC Cf args p.1.hi) = true := by
  have := callsB_chk hcb hs
  simp only [callChk, Bool.and_eq_true] at this
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
    (hx : ExpW img Cf.xc fp) {args : List V} {ws : List E} {i : CIdx}
    (h : idxPowC Cf args i = true) : IdxEx (slotW (args.map σ ++ ws)) i := by
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
    | m1 hok _ _ _ _ _ => unfold heapOk at hok; simp only [Bool.and_eq_true] at hok; exact hok.1.1.1
    | c hok _ _ _ _ _ => unfold heapOkC at hok; simp only [Bool.and_eq_true] at hok; exact hok.1.1.1.1.1
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
    ¬ (Cf.frame.entry ≤ t ∧ t < Cf.frame.entry + Cf.frame.len) ∧ t < 2 ^ 30 ∧ Cf.X.selfAt of = false ∧
      ∃ G s, Cf.frame.sigs.get t = some G ∧ getF Cf.X.sites of = some s ∧ s.r < 2 ^ 30 ∧
        callOkC Cf G f s.args.length s.rets.length = true := by
  simp only [jumpCallOk, hpt, hent, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
  obtain ⟨-, ⟨⟨⟨hout, ht⟩, hsf⟩, -⟩, h⟩ := h
  refine ⟨fun ⟨h1, h2⟩ ↦ by simp [h1, h2] at hout, ht, hsf, ?_⟩
  split at h
  · rename_i G s hG hs
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨G, s, hG, hs, h.1, h.2⟩
  · cases h

/-- **A `JUMP` through its call site's target cell** goes through no `0`, no pc, no table target cell,
from a cell not the own frame's. -/
theorem jumpCallOk_dsp {Cf : CFun} {oc od of : ℕ} (h : jumpCallOk Cf (.jump oc od of) = true) {s : B2C.Site}
    (hs : getF Cf.X.sites of = some s) (he : s.tgt = od) :
    od ≠ 0 ∧ Cf.X.pcAt od = none ∧ getF Cf.X.arms od = none ∧ Cf.X.selfAt of = false := by
  simp only [jumpCallOk, Bool.and_eq_true] at h
  have h1 := h.1
  simp only [dspNo, hs, he, Nat.beq_refl, Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true',
    Option.isNone_iff_eq_none] at h1
  obtain ⟨⟨⟨h0, hp⟩, ha⟩, hsf⟩ := h1
  exact ⟨fun e ↦ by simp [e] at h0, hp, ha, hsf⟩

/-- A call's site has no dispatch target cell its jump's. -/
theorem jumpCallOk_tgt {Cf : CFun} {oc od of t : ℕ} (h : jumpCallOk Cf (.jump oc od of) = true)
    (hpt : Cf.X.pcAt od = some t) : ∀ s, getF Cf.X.sites of = some s → s.tgt ≠ od := fun s hs he ↦ by
  have := (jumpCallOk_dsp h hs he).2.1
  rw [hpt] at this; cases this

theorem jumpCallOk_next {Cf : CFun} {oc od of t : ℕ} {f : String} (h : jumpCallOk Cf (.jump oc od of) = true)
    (hpt : Cf.X.pcAt od = some t) (hent : getF Cf.X.ents t = some f) : Cf.X.nextAt of = false := by
  simp only [jumpCallOk, hpt, hent, Bool.and_eq_true, Bool.not_eq_true'] at h
  exact h.2.1.2

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
/-! ## The shape -/

theorem bodyC_ctrl {body : List Stmt} (h : bodyC body = true) : ∀ s ∈ stmtsOf body, ctrlOk s = true := by
  simp only [bodyC, Bool.and_eq_true, List.all_eq_true] at h
  exact h.1

theorem matchLens_mem {body : List Stmt} {x : V} {arms : List (List Stmt)} (h : Stmt.match_ x arms ∈ stmtsOf body) :
    (x.idx, arms.length) ∈ matchLens body :=
  List.mem_filterMap.mpr ⟨_, h, rfl⟩

theorem armsCover_at {X : AlignCtx} {e : ℕ} {ml : List (ℕ × ℕ)} {a : ℕ × ℕ} {ts : List ℕ}
    (h : armsCover X e ml a ts = true) {p : ℕ × ℕ} (hp : p ∈ ml) (hpa : p.1 = a.1) {j : ℕ} (hj : j < p.2) :
    ∃ t, getF X.jt (a.2 + j) = some t ∧ e ≤ t ∧ t < 2 ^ 30 ∧ t - e ∈ ts := by
  have h1 := List.all_eq_true.mp h p hp
  simp only [hpa, Nat.beq_refl, Bool.not_true, Bool.false_or, List.all_eq_true, List.mem_range] at h1
  have h2 := h1 j hj
  split at h2
  · rename_i t ht
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at h2
    exact ⟨t, ht, h2.1.1, h2.1.2, h2.2⟩
  · cases h2

theorem tgtGo_at {Cf : CFun} {ml : List (ℕ × ℕ)} : ∀ {n : ℕ} {code : List OffsetInstruction},
    tgtGo Cf ml n code = true → ∀ {i k oc od of : ℕ}, code[i]? = some (.jump oc od of) →
      Cf.frame.tgt.get (n + i) = some k →
      (dspSite Cf.X od of = true ∧ dspJ Cf k od of = true) ∨ (dspSite Cf.X od of = false ∧
      od ≠ 0 ∧ Cf.X.pcAt od = none ∧ Cf.frame.calls.get k = none ∧ ∃ a ts, getF Cf.X.arms od = some a ∧
        Cf.frame.arms.get k = some ts ∧ armsCover Cf.X Cf.frame.entry ml a ts = true)
  | _, [], _, _, _, _, _, _, h, _ => by simp at h
  | n, ins :: code, h, i, k, oc, od, of, hi, ht => by
    simp only [tgtGo, Bool.and_eq_true] at h
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      rw [Nat.add_zero] at ht
      have h1 := h.1
      rw [ht] at h1
      simp only at h1
      cases hd : dspSite Cf.X od of
      · rw [hd, Bool.cond_false] at h1
        simp only [Bool.and_eq_true, Bool.not_eq_true', Option.isNone_iff_eq_none] at h1
        obtain ⟨⟨⟨h0, hpc⟩, hcl⟩, h2⟩ := h1
        split at h2
        · rename_i a ts ha hts
          exact .inr ⟨rfl, fun e ↦ by simp [e] at h0, hpc, hcl, a, ts, ha, hts, h2⟩
        · cases h2
      · rw [hd, Bool.cond_true] at h1
        exact .inl ⟨rfl, h1⟩
    | succ i =>
      exact tgtGo_at h.2 (by simpa using hi) (by rw [show n + 1 + i = n + (i + 1) by omega]; exact ht)

/-- A `JUMP` the frame walk reads no table for is no dispatch's. -/
theorem tgtGo_none {Cf : CFun} {ml : List (ℕ × ℕ)} : ∀ {n : ℕ} {code : List OffsetInstruction},
    tgtGo Cf ml n code = true → ∀ {i oc od of : ℕ}, code[i]? = some (.jump oc od of) →
      Cf.frame.tgt.get (n + i) = none → dspSite Cf.X od of = false
  | _, [], h, _, _, _, _, hi, _ => by simp at hi
  | n, ins :: code, h, i, oc, od, of, hi, ht => by
    simp only [tgtGo, Bool.and_eq_true] at h
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      rw [Nat.add_zero] at ht
      have h1 := h.1
      rw [ht] at h1
      simp only [Bool.not_eq_true'] at h1
      exact h1
    | succ i =>
      exact tgtGo_none h.2 (by simpa using hi) (by rw [show n + 1 + i = n + (i + 1) by omega]; exact ht)

/-! ## Jumps -/

/-- **A jump's hints' atoms and reads** write only what is written once its hints ran. -/
theorem jump_events {img : MemoryImage κ} (hκ : κ ≤ 28) {X : AlignCtx} {H : HCert} {C : Ctx}
    {sigOf : String → HSig} {rd : Reader} {ws0 : List E}
    {hs : List Prover.Exec.Hint} {s s1 : St} (e1 : hs.foldlM (Prover.Exec.runHint C) s = .ok s1)
    (hs0 : Fine (refMem img) s) (hm : Moves (refMem img) s s1) {σ : Val} {as bs : List Atom}
    (hq : ∀ a ∈ as, flowAtom a = false → stopS H.readT a = false) (hbs : ∀ a ∈ bs, stopS H.readT a = false)
    (hpairs : List.Forall₂ (Pairs X) (as.filter flowAtom) (hs.filter isaFlowHint))
    (hptr : ∀ a ∈ as, ∀ p, ptrOf a = some p → Rd img s.fp (X.locAt p.idx) = some (σ p))
    {pre rest : List Ev} (hrw : ReadsAt sigOf H rd σ ws0 pre ((as ++ bs).map Ev.atom ++ rest))
    (hW : ∀ y, WrittenC sigOf H rd σ ws0 pre y → WrK s.mem y) :
    ∀ y, WrittenC sigOf H rd σ ws0 (pre ++ (as ++ bs).map Ev.atom) y → WrK s1.mem y := by
  have hside : ∀ a ∈ as ++ bs, a ∉ as.filter flowAtom → stopS H.readT a = false := by
    intro a ha hn
    rcases List.mem_append.mp ha with ha | ha
    · cases hfa : flowAtom a
      · exact hq a ha hfa
      · exact absurd (List.mem_filter.mpr ⟨ha, hfa⟩) hn
    · exact hbs a ha
  intro y hy
  rcases written_extendC (fs := as.filter flowAtom) hrw hside hy with h | ⟨a, ha, hwa⟩
  · exact (hW y h).mono hm.le
  · rw [List.mem_filter] at ha
    exact flow_wrk hκ e1 hs0 hm hpairs ha.1 ha.2 (hptr a ha.1) hwa

/-- The head statement a jump steps by, on the core route's shape: a branch, a `match` or a return. -/
theorem head_cases {Cf : CFun} {zs : Zip} (_hzsok : ZOk Cf.fn.body zs)
    (_hctrl : ∀ s ∈ stmtsOf Cf.fn.body, ctrlOk s = true)
    {i oc od of : ℕ} {tabs : List (ℕ × Zip × ℕ)} {r : Option Zip × List (ℕ × Zip)}
    (hh : headStepH Cf.P i oc od of tabs zs = some r) :
    (∃ x fs args rets ss, zs.cur = .dispatch x fs args rets :: ss) ∨
    (∃ c f args ss, zs.cur = .callIf c f args :: ss) ∨ (∃ c zb nb ss, zs.cur = .ite c zb nb :: ss) ∨
      (∃ x arms ss, zs.cur = .match_ x arms :: ss) ∨ (∃ vs ss, zs.cur = .ret vs :: ss) ∨
      ∃ f args rets ss, zs.cur = .call f args rets :: ss := by
  obtain ⟨st, ss, hcur, hna⟩ := headH_stmt hh
  cases st with
  | atom a => exact absurd rfl (hna a)
  | dispatch x fs args rets => exact Or.inl ⟨x, fs, args, rets, ss, hcur⟩
  | callIf c f args => exact Or.inr (Or.inl ⟨c, f, args, ss, hcur⟩)
  | ite c zb nb => exact Or.inr (Or.inr (Or.inl ⟨c, zb, nb, ss, hcur⟩))
  | match_ x arms => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨x, arms, ss, hcur⟩)))
  | ret vs => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨vs, ss, hcur⟩))))
  | call f args rets => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨f, args, rets, ss, hcur⟩))))

theorem headH_match_nz {P : PairCtx} {i oc od of : ℕ} {tabs : List (ℕ × Zip × ℕ)} {zs : Zip}
    {r : Option Zip × List (ℕ × Zip)} {x : V} {arms : List (List Stmt)} {ss : List Stmt}
    (h : headStepH P i oc od of tabs zs = some r) (hz : zs.cur = .match_ x arms :: ss) :
    P.X.nzAt oc = true ∧ P.X.selfAt of = true ∧ ∃ a, getF P.X.arms od = some a := by
  simp only [headStepH, hz] at h
  cases hs : (P.X.nzAt oc && P.X.selfAt of) <;> simp only [hs, Bool.cond_true, Bool.cond_false] at h
  · cases h
  simp only [Bool.and_eq_true] at hs
  refine ⟨hs.1, hs.2, ?_⟩
  cases ha : getF P.X.arms od
  · rw [ha] at h; cases h
  · exact ⟨_, rfl⟩

theorem lookup_mem {α β : Type} [BEq α] [LawfulBEq α] {a : α} {b : β} :
    ∀ {l : List (α × β)}, l.lookup a = some b → (a, b) ∈ l
  | [], h => by simp at h
  | (a', b') :: l, h => by
    simp only [List.lookup] at h
    split at h
    · rename_i hab
      cases h
      rw [beq_iff_eq] at hab
      subst hab
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (lookup_mem h)

/-- A dispatch site's `JUMP`: what `dspSite` says. -/
theorem dspSite_of {X : AlignCtx} {od of : ℕ} {args rets : List V} {s : B2C.Site} (hpc : X.pcAt od = none)
    (hsite : X.siteAt of args rets = some s) (htg : s.tgt = od) (hd0 : od ≠ 0) : dspSite X od of = true := by
  obtain ⟨hs, -, -⟩ := siteAt_spec hsite
  have h0 : Nat.beq od 0 = false := by cases h : Nat.beq od 0 <;> simp_all [Nat.beq_eq]
  simp only [dspSite, hpc, hs, h0, htg, Nat.beq_refl, Option.isNone_none, Bool.not_false, Bool.and_self]

/-- **A dispatch's `JUMP` the walk reads callees for**: its callees' entries `dspPc`, each callee of the
dispatch at its site among them. -/
theorem dsp_at {Cf : CFun} (hcb : callsB Cf = true) {k od of : ℕ} (hdj : dspJ Cf k od of = true) {x : V}
    {fs : List String} {args rets : List V} {s : B2C.Site} (hst : Stmt.dispatch x fs args rets ∈ stmtsOf Cf.fn.body)
    (hsite : Cf.X.siteAt of args rets = some s) :
    ∃ pcs, Cf.frame.calls.get k = some pcs ∧ Cf.frame.arms.get k = none ∧ Cf.X.selfAt of = false ∧
      Cf.X.nextAt of = false ∧ s.r < 2 ^ 30 ∧ s.tgt = od ∧ (∀ t ∈ pcs, dspPc Cf s t = true) ∧
      ∀ f ∈ fs, ∃ t ∈ pcs, Cf.X.entOk t f = true := by
  obtain ⟨hs, -, -⟩ := siteAt_spec hsite
  simp only [dspJ, Bool.and_eq_true, Bool.not_eq_true', Option.isNone_iff_eq_none] at hdj
  obtain ⟨⟨⟨ha, hsf⟩, hnx⟩, hdj⟩ := hdj
  rw [hs] at hdj
  split at hdj
  · rename_i pcs s' fs' hpcs hs' hfs
    cases hs'
    simp only [Bool.and_eq_true, Nat.beq_eq, decide_eq_true_eq, List.all_eq_true, List.any_eq_true] at hdj
    obtain ⟨⟨⟨htg, hr⟩, hpc⟩, hfs'⟩ := hdj
    have hc := List.all_eq_true.mp hcb _ hst
    simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Option.isNone_iff_eq_none, beq_iff_eq] at hc
    have hfe : fs' = fs := by
      rcases hc.2 _ (lookup_mem hfs) with h | h
      · rw [hsite] at h; cases h
      · exact h
    subst hfe
    exact ⟨pcs, hpcs, ha, hsf, hnx, hr, htg, hpc, hfs'⟩
  · cases hdj

/-- **A dispatch's target cell holds the picked callee's entry**, by `HonF.tgt`, at a call on the path. -/
theorem honF_dsp {img : MemoryImage κ} {Cf : CFun} {fp : ℕ} {σ : Val} (hσ : HonF img Cf fp σ) {f : String}
    {args rets : List V} {pre es : List Ev}
    {vs : List V} (hb : walk σ Cf.fn.body = .ret (pre ++ Ev.call f args rets :: es) vs) {q : ℕ} {s : B2C.Site}
    (hsite : Cf.X.siteAt q args rets = some s) (htg : s.tgt ≠ 0) {t : ℕ} (he : Cf.X.entOk t f = true) :
    Rd img fp s.tgt = some (ofK (g ^ t)) :=
  hσ.tgt _ _ hb (calls pre).length ⟨f, args, rets, true⟩ q s calls_mid rfl hsite htg t he

/-- **The frame walk's table jumps land at their arms**, of the reference: a `JUMP` the walk reads
a table for is a `match`'s, its target the slot of the arm the selector picks, or a dispatch's, its
target the entry of the callee the path calls. -/
theorem core_tgt {img : MemoryImage κ} {Cf : CFun} {code : List OffsetInstruction}
    (hpair : pairOk Cf.X Cf.H Cf.frame.O Cf.frame.S Cf.fn.body code Cf.d = true)
    (hctrl : ∀ s ∈ stmtsOf Cf.fn.body, ctrlOk s = true) (hmain : Cf.X.main = false) (htgt : tgtOk Cf code = true)
    (hcb : callsB Cf = true) {fp i : ℕ} {σ : Val} (hσ : HonF img Cf fp σ) {pos : List Stmt} {pre es : List Ev}
    {vs : List V} (hat : pairAt Cf.P Cf.fn.body code Cf.d i = some pos)
    (hb : walk σ Cf.fn.body = .ret (pre ++ es) vs) (hwp : walk σ pos = .ret es vs) :
    TgtOk img Cf.frame code i fp := by
  intro c d f hci cv dv hcv hne hdv pc hpcl hdl kk hk
  rw [tgtOk, Exec.listSeq_eq] at htgt
  obtain ⟨as, bs, z, zs, tabs, r, hpos, hzpos, -, -, -, -, hzsok, hr, -, -, -⟩ := pair_jump hpair hat hci
  rw [hpos, hzpos, ← List.append_assoc, ← List.map_append] at hwp
  obtain ⟨es1, hes1, hes⟩ := walk_atoms_ret hwp
  cases hz : Cf.X.zeroAt c
  swap
  · exact absurd (Option.some.inj ((hσ.jc.zero c hz).symm.trans hcv)).symm hne
  have hpcn : Cf.X.pcAt d = none := by
    rcases tgtGo_at htgt hci (by rw [Nat.zero_add]; exact hk) with ⟨hds, -⟩ | ⟨-, -, hpcn, -⟩
    · simp only [dspSite, Bool.and_eq_true, Option.isNone_iff_eq_none] at hds
      exact hds.1.2
    · exact hpcn
  cases hf : fwdJ Cf.X i c d f
  swap
  · obtain ⟨-, -, t, -, ht, -⟩ := jumpH_fwd hr hz hf
    have ht' : Cf.X.pcAt d = some t := ht
    rw [hpcn] at ht'; cases ht'
  have hh := headH_of hr hz hf
  rcases head_cases hzsok hctrl hh with ⟨x, fs, args, rets, ss, hcur⟩ | ⟨c', f', args', ss, hcur⟩ | hh4
  · -- a dispatch: its target cell the entry of the callee the path calls
    obtain ⟨-, hd0, s, c0, o, hsite, htg, -⟩ := headH_dispatch hh hcur
    have hds := dspSite_of hpcn hsite htg hd0
    rcases tgtGo_at htgt hci (by rw [Nat.zero_add]; exact hk) with ⟨-, hdj⟩ | ⟨hds', -⟩
    swap
    · rw [hds] at hds'; cases hds'
    have hmem : Stmt.dispatch x fs args rets ∈ stmtsOf Cf.fn.body :=
      zok_stmts hzsok (by rw [Zip.pos_head hcur]; exact List.mem_cons_self)
    obtain ⟨pcs, hpcs, harm, -, -, -, -, hpc, hfs⟩ := dsp_at hcb hdj hmem hsite
    refine ⟨fun pcs' h ↦ ?_, fun ts h ↦ by rw [harm] at h; cases h⟩
    rw [hpcs, Option.some.injEq] at h
    subst h
    rw [Zip.pos_head hcur] at hes1
    obtain ⟨f0, hf0, es2, rfl, -⟩ := walk_dispatch_ret hes1
    obtain ⟨t, ht, hte⟩ := hfs f0 hf0
    have hpt := hpc t ht
    simp only [dspPc] at hpt
    split at hpt
    · rename_i f1 hf1
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hpt
      have hrd := honF_dsp hσ (pre := pre ++ (as ++ bs).map Ev.atom) (by rw [hb, hes, List.append_assoc]) hsite
        (by omega) hte
      rw [htg, hdv, Option.some.injEq] at hrd
      subst hrd
      have hgt : (g : K) ^ t = g ^ pc := by simpa using hdl
      have := gpow_lt_inj (by omega) (by unfold pcLim at hpcl; omega) hgt
      rw [← this]
      exact ht
    · cases hpt
  · obtain ⟨-, t, -, ht, -⟩ := headH_callIf hh hcur
    have ht' : Cf.X.pcAt d = some t := ht
    rw [hpcn] at ht'; cases ht'
  rcases hh4 with ⟨cc, zb, nb, ss, hcur⟩ | ⟨x, arms, ss, hcur⟩ | ⟨vs', ss, hcur⟩ |
    ⟨f, args, rets, ss, hcur⟩
  rotate_left 3
  · obtain ⟨-, s0, t, -, -, -, ht, -⟩ := headH_call hh hcur
    have ht' : Cf.X.pcAt d = some t := ht
    rw [hpcn] at ht'; cases ht'
  · obtain ⟨-, -, t, -, -, -, ht, -⟩ := headH_ite hh hcur
    have ht' : Cf.X.pcAt d = some t := ht
    rw [hpcn] at ht'; cases ht'
  · obtain ⟨-, hsfm, -⟩ := headH_match_nz hh hcur
    rcases tgtGo_at htgt hci (by rw [Nat.zero_add]; exact hk) with ⟨-, hdj⟩ | ⟨-, hd0, -, hcl, a, ts0, ha, hts0, hcov⟩
    · simp only [dspJ, Bool.and_eq_true, Bool.not_eq_true'] at hdj
      have hsf2 : Cf.X.selfAt f = true := hsfm
      rw [hdj.1.1.2] at hsf2; cases hsf2
    refine ⟨fun pcs h ↦ by (rw [hcl] at h; cases h), fun ts hts ↦ ?_⟩
    rw [hts0, Option.some.injEq] at hts
    subst hts
    obtain ⟨-, -, hax, -⟩ := jumpH_match hr hcur hz hf ha
    obtain ⟨k0, hk0, hσx, -⟩ := side_arm hcur hes1
    have hmem : Stmt.match_ x arms ∈ stmtsOf Cf.fn.body :=
      zok_stmts hzsok (by rw [Zip.pos_head hcur]; exact List.mem_cons_self)
    obtain ⟨t, hjt, he, ht30, hts⟩ := armsCover_at hcov (matchLens_mem hmem) hax.symm hk0
    have hrd := hσ.jc.arm x arms hmem d a ha hax k0 t hσx hjt
    rw [hrd, Option.some.injEq] at hdv
    subst hdv
    have hgt : (g : K) ^ t = g ^ pc := by simpa using hdl
    have := gpow_lt_inj (by omega) (by unfold pcLim at hpcl; omega) hgt
    exact ⟨t - Cf.frame.entry, hts, by omega⟩
  · obtain ⟨-, -, h01⟩ := headH_ret hh hcur
    simp only [show (PairCtx.ofH Cf.X Cf.H Cf.frame.O Cf.frame.S).X.main = false from hmain, Bool.false_eq_true,
      ↓reduceIte] at h01
    have hd0 : d ≠ 0 := by
      rcases tgtGo_at htgt hci (by rw [Nat.zero_add]; exact hk) with ⟨hds, -⟩ | ⟨-, hd0, -⟩
      · simp only [dspSite, Bool.and_eq_true, Bool.not_eq_true'] at hds
        exact fun h ↦ by simp [h] at hds
      · exact hd0
    exact absurd h01.1 hd0

/-- **A jump falling through**, its condition cell `0`: the next offset's position, the events since
this offset's its hints' atoms and reads, a branch's condition, atoms writing nothing. -/
theorem core_jfall {img : MemoryImage κ} (hκ : κ ≤ 28) {Cf : CFun} {code : List OffsetInstruction}
    (hpair : pairOk Cf.X Cf.H Cf.frame.O Cf.frame.S Cf.fn.body code Cf.d = true)
    (hctrl : ∀ s ∈ stmtsOf Cf.fn.body, ctrlOk s = true)
    {C : Ctx} {s s1 : St} {i oc od of : ℕ} (hins : code[i]? = some (.jump oc od of)) (hoc : oc < 2 ^ 28)
    (e1 : ((Cf.d.2.2.lookup (Cf.X.entry + i)).getD []).foldlM (Prover.Exec.runHint C) s = .ok s1)
    (hs : Fine (refMem img) s) (hm : Moves (refMem img) s s1) (hc0 : s1.mem.get (s1.fp + oc) = some 0)
    {σ : Val} (hσ : HonF img Cf s.fp σ) {pos : List Stmt} {pre es : List Ev} {vs : List V}
    (hat : pairAt Cf.P Cf.fn.body code Cf.d i = some pos) (hb : walk σ Cf.fn.body = .ret (pre ++ es) vs)
    (hwp : walk σ pos = .ret es vs) {rd : Reader} (hrw : ReadsAt Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) pre es)
    (hW : ∀ y, WrittenC Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) pre y → WrK s.mem y) :
    ∃ pos', pairAt Cf.P Cf.fn.body code Cf.d (i + 1) = some pos' ∧ ∃ evs es', es = evs ++ es' ∧
      walk σ pos' = .ret es' vs ∧ (∀ e ∈ evs, EvM Cf.sigOf rd σ e) ∧
      ∀ y, WrittenC Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) (pre ++ evs) y → WrK s1.mem y := by
  obtain ⟨as, bs, z, zs, tabs, r, hpos, hzpos, hq, hbs, hpairs, -, hzsok, hr, h1, -, -⟩ := pair_jump hpair hat hins
  rw [hpos, hzpos, ← List.append_assoc, ← List.map_append] at hwp
  obtain ⟨es1, hes1, rfl⟩ := walk_atoms_ret hwp
  have hev := jump_events hκ e1 hs hm hq hbs hpairs (fun a ha p hp ↦ hσ.ptr _ _ hb a p
    (List.mem_append_right _ (List.mem_append_left _ (by simp [ha]))) hp)
    (rest := es1) (by simpa [List.append_assoc] using hrw) hW
  have hnz : Cf.X.nzAt oc = true → False := fun h ↦ by
    obtain ⟨w, hw, hw0⟩ := hσ.jc.nz oc h
    exact hw0 (rd_get hκ hm.fine hoc (by rw [hm.fp]; exact hw) hc0).symm
  cases hz : Cf.X.zeroAt oc
  swap
  · have hr0 := jumpH_zero hr hz
    subst hr0
    refine ⟨z.pos, h1 z rfl, as.map Ev.atom, bs.map Ev.atom ++ es1, by simp, ?_, evM_atoms _,
      fun y hy ↦ hev y (by rw [List.map_append, ← List.append_assoc]; exact writtenC_prefix hy)⟩
    rw [hzpos, walk_atoms, hes1]
    rfl
  cases hf : fwdJ Cf.X i oc od of
  swap
  · exact absurd (jumpH_fwd hr hz hf).1 (fun h ↦ hnz h)
  have hh := headH_of hr hz hf
  rcases head_cases hzsok hctrl hh with ⟨x, fs, args, rets, ss, hcur⟩ | ⟨c, f, args, ss, hcur⟩ | hh4
  · exact absurd (headH_dispatch hh hcur).1 (fun h ↦ hnz h)
  · obtain ⟨hloc, t, ca, -, -, hca, rfl, -⟩ := headH_callIf hh hcur
    obtain ⟨cs, hcs, hcpos, -⟩ := normG_pos _ _ hca
    rw [Zip.pos_head hcur, hcpos, Bridge.walk_callIf_cons] at hes1
    obtain ⟨es2, hes2, rfl⟩ := pre_eq_ret hes1
    obtain ⟨es3, hes3, rfl⟩ := walk_atoms_ret hes2
    have hcond := hσ.jc.cond _ _ hb c (by simp)
    have hloc' : Cf.X.locAt c.idx = oc := hloc
    rw [hloc'] at hcond
    have hσc : σ c = 0 := (rd_get hκ hm.fine hoc (by rw [hm.fp]; exact hcond) hc0).symm
    refine ⟨ca.pos, h1 ca rfl, (as ++ bs).map Ev.atom ++ [Ev.inK c, Ev.skip f args] ++ cs.map Ev.atom, es3,
      by simp [hσc], hes3, evM_app (evM_app (evM_atoms _) (evM_inK_cons (evM_skip_cons evM_nil))) (evM_atoms _),
      fun y hy ↦ ?_⟩
    have h2 : WrittenC Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ)
        (pre ++ (as ++ bs).map Ev.atom ++ [Ev.inK c] ++ [Ev.skip f args]) y := by
      rcases writtenC_append (a := pre ++ (as ++ bs).map Ev.atom ++ [Ev.inK c] ++ [Ev.skip f args])
          (b := cs.map Ev.atom) (by simpa [List.append_assoc] using hy) with h | ⟨e, he, hwe⟩
      · exact h
      · obtain ⟨b, hb', rfl⟩ := List.mem_map.mp he
        exact absurd hwe (no_writes_of_stopL (hcs b hb'))
    exact hev y (writtenC_noAtom (e := Ev.inK c) (fun a h ↦ by cases h) (fun f a r h ↦ by cases h)
      (writtenC_noAtom (e := Ev.skip f args) (fun a h ↦ by cases h) (fun f a r h ↦ by cases h) h2))
  rcases hh4 with ⟨c, zb, nb, ss, hcur⟩ | ⟨x, arms, ss, hcur⟩ | ⟨vs', ss, hcur⟩ |
    ⟨f, args, rets, ss, hcur⟩
  rotate_left 3
  · exact absurd (headH_call hh hcur).1 (fun h ↦ hnz h)
  · obtain ⟨hloc, -, t, cz, cn, o, -, hcz, -, -, rfl⟩ := headH_ite hh hcur
    obtain ⟨es2, rfl, hes2⟩ := side_ite hcur hes1
    have hcond := hσ.jc.cond _ _ hb c (by simp)
    have hloc' : Cf.X.locAt c.idx = oc := hloc
    rw [hloc'] at hcond
    have hσc : σ c = 0 := (rd_get hκ hm.fine hoc (by rw [hm.fp]; exact hcond) hc0).symm
    simp only [hσc, ↓reduceIte] at hes2
    obtain ⟨evs, es3, rfl, hes3, hevN, hWn⟩ := succ_normC hcz hes2
    refine ⟨cz.pos, h1 cz rfl, (as ++ bs).map Ev.atom ++ Ev.inK c :: evs, es3, by simp, hes3,
      evM_app (evM_atoms _) (evM_inK_cons hevN), fun y hy ↦ ?_⟩
    have h2 := hWn (pre ++ (as ++ bs).map Ev.atom ++ [Ev.inK c]) y (by simpa [List.append_assoc] using hy)
    exact hev y (writtenC_noAtom (fun a h ↦ by cases h) (fun f a r h ↦ by cases h) h2)
  · exact absurd (headH_match_nz hh hcur).1 (fun h ↦ hnz h)
  · exact absurd (headH_ret hh hcur).2.1 (fun h ↦ hnz h)

/-- **A jump taken**, its condition cell nonzero: a return (`od = 0`, `of = 1`, the events past the
position writing what is written once its hints ran), or a jump in the frame, through its own frame
pointer, to the offset of the side the run takes, the events to there its hints' atoms and reads, a
branch's condition, atoms writing nothing. -/
theorem core_jtaken {img : MemoryImage κ} (hκ : κ ≤ 28) {Cf : CFun} {code : List OffsetInstruction}
    (hpair : pairOk Cf.X Cf.H Cf.frame.O Cf.frame.S Cf.fn.body code Cf.d = true)
    (hctrl : ∀ s ∈ stmtsOf Cf.fn.body, ctrlOk s = true) (hmain : Cf.X.main = false)
    (hlen : ∀ o < code.length, Cf.X.entry + o < 2 ^ 30)
    {C : Ctx} {s s1 s' : St} {i oc od of : ℕ} (hins : code[i]? = some (.jump oc od of))
    (hcj : ∀ t f, Cf.X.pcAt od = some t → getF Cf.X.ents t = some f → Cf.X.selfAt of = false)
    (hsf : Cf.X.selfAt of = true) (hdn : ∀ s, getF Cf.X.sites of = some s → s.tgt = od → Cf.X.selfAt of = false)
    (hoc : oc < 2 ^ 28)
    (hod : od < 2 ^ 28)
    (e1 : ((Cf.d.2.2.lookup (Cf.X.entry + i)).getD []).foldlM (Prover.Exec.runHint C) s = .ok s1)
    (hs : Fine (refMem img) s) (hm : Moves (refMem img) s s1) {v : E} (hcv : s1.mem.get (s1.fp + oc) = some v)
    (hv0 : v ≠ 0) (hd : s1.mem.get (s1.fp + od) = some (ofK (g ^ s'.pc))) (hpcs : s'.pc < 2 ^ 30)
    {σ : Val} (hσ : HonF img Cf s.fp σ) {pos : List Stmt} {pre es : List Ev} {vs : List V}
    (hat : pairAt Cf.P Cf.fn.body code Cf.d i = some pos) (hb : walk σ Cf.fn.body = .ret (pre ++ es) vs)
    (hwp : walk σ pos = .ret es vs) {rd : Reader} (hrw : ReadsAt Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) pre es)
    (hW : ∀ y, WrittenC Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) pre y → WrK s.mem y) :
    (od = 0 ∧ of = 1 ∧ (∀ e ∈ es, EvM Cf.sigOf rd σ e) ∧
      ∀ y, WrittenC Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) (pre ++ es) y → WrK s1.mem y) ∨
    (Cf.X.selfAt of = true ∧ ∃ o pos', s'.pc = Cf.X.entry + o ∧ i < o ∧
      pairAt Cf.P Cf.fn.body code Cf.d o = some pos' ∧ ∃ evs es', es = evs ++ es' ∧
        walk σ pos' = .ret es' vs ∧ (∀ e ∈ evs, EvM Cf.sigOf rd σ e) ∧
        ∀ y, WrittenC Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) (pre ++ evs) y → WrK s1.mem y) := by
  obtain ⟨as, bs, z, zs, tabs, r, hpos, hzpos, hq, hbs, hpairs, -, hzsok, hr, -, h2, h3⟩ := pair_jump hpair hat hins
  rw [hpos, hzpos, ← List.append_assoc, ← List.map_append] at hwp
  obtain ⟨es1, hes1, rfl⟩ := walk_atoms_ret hwp
  have hev := jump_events hκ e1 hs hm hq hbs hpairs (fun a ha p hp ↦ hσ.ptr _ _ hb a p
    (List.mem_append_right _ (List.mem_append_left _ (by simp [ha]))) hp)
    (rest := es1) (by simpa [List.append_assoc] using hrw) hW
  -- the target pc, a constant one's
  have hpcw : ∀ t, Cf.X.pcAt od = some t → t < 2 ^ 30 → s'.pc = t := fun t ht ht30 ↦ by
    have h := rd_get hκ hm.fine hod (by rw [hm.fp]; exact hσ.jc.pcw od t ht) hd
    have hgt : (g : K) ^ s'.pc = g ^ t := by simpa using congrArg (fun e : E ↦ e.limb 0) h
    exact gpow_lt_inj (by omega) (by omega) hgt
  cases hz : Cf.X.zeroAt oc
  swap
  · exact absurd (rd_get hκ hm.fine hoc (by rw [hm.fp]; exact hσ.jc.zero oc hz) hcv) hv0
  cases hf : fwdJ Cf.X i oc od of
  swap
  · obtain ⟨-, hself, t, o, ht, ho, hr0⟩ := jumpH_fwd hr hz hf
    subst hr0
    obtain ⟨rfl, hlt⟩ := fwdOff_eq (X := Cf.X) ho
    have hat' := h2 _ List.mem_cons_self
    have ho' := pairAt_lt hpair hat'
    have hto : Cf.X.entry + (t - Cf.X.entry) = t := by omega
    refine Or.inr ⟨hself, t - Cf.X.entry, z.pos, by rw [hpcw t ht (by have := hlen _ ho'; omega), hto], by omega,
      hat', as.map Ev.atom, bs.map Ev.atom ++ es1, by simp, ?_, evM_atoms _,
      fun y hy ↦ hev y (by rw [List.map_append, ← List.append_assoc]; exact writtenC_prefix hy)⟩
    rw [hzpos, walk_atoms, hes1]
    rfl
  have hh := headH_of hr hz hf
  rcases head_cases hzsok hctrl hh with ⟨x, fs, args, rets, ss, hcur⟩ | ⟨c', f', args', ss, hcur⟩ | hh4
  · obtain ⟨-, -, s0, -, -, hsite, htg, -⟩ := headH_dispatch hh hcur
    rw [hdn s0 (siteAt_spec hsite).1 htg] at hsf
    cases hsf
  · obtain ⟨-, t, -, ht, hent, -⟩ := headH_callIf hh hcur
    rw [hcj t f' ht (entOk_spec hent)] at hsf
    cases hsf
  rcases hh4 with ⟨c, zb, nb, ss, hcur⟩ | ⟨x, arms, ss, hcur⟩ | ⟨vs', ss, hcur⟩ |
    ⟨f, args, rets, ss, hcur⟩
  rotate_left 3
  · obtain ⟨-, s0, t, -, -, -, ht, hent, -⟩ := headH_call hh hcur
    rw [hcj t f ht (entOk_spec hent)] at hsf
    cases hsf
  · obtain ⟨hloc, hself, t, cz, cn, o, ht, -, hcn, ho, rfl⟩ := headH_ite hh hcur
    obtain ⟨es2, rfl, hes2⟩ := side_ite hcur hes1
    have hcond := hσ.jc.cond _ _ hb c (by simp)
    have hloc' : Cf.X.locAt c.idx = oc := hloc
    rw [hloc'] at hcond
    have hσc : σ c ≠ 0 := fun h0 ↦ hv0 (by rw [rd_get hκ hm.fine hoc (by rw [hm.fp]; exact hcond) hcv, h0])
    simp only [hσc, ↓reduceIte] at hes2
    obtain ⟨evs, es3, rfl, hes3, hevN, hWn⟩ := succ_normC hcn hes2
    obtain ⟨rfl, hlt⟩ := fwdOff_eq (X := Cf.X) ho
    have hat' := h2 _ List.mem_cons_self
    have ho' := pairAt_lt hpair hat'
    refine Or.inr ⟨hself, t - Cf.X.entry, cn.pos, by rw [hpcw t ht (by have := hlen _ ho'; omega)]; omega,
      by omega, hat', (as ++ bs).map Ev.atom ++ Ev.inK c :: evs, es3, by simp, hes3,
      evM_app (evM_atoms _) (evM_inK_cons hevN), fun y hy ↦ ?_⟩
    have h2' := hWn (pre ++ (as ++ bs).map Ev.atom ++ [Ev.inK c]) y (by simpa [List.append_assoc] using hy)
    exact hev y (writtenC_noAtom (fun a h ↦ by cases h) (fun f a r h ↦ by cases h) h2')
  · obtain ⟨-, hself, a, ha⟩ := headH_match_nz hh hcur
    obtain ⟨-, -, hax, -⟩ := jumpH_match hr hcur hz hf ha
    obtain ⟨k0, hk0, hσx, hes2⟩ := side_arm hcur hes1
    have hmem : Stmt.match_ x arms ∈ stmtsOf Cf.fn.body :=
      zok_stmts hzsok (by rw [Zip.pos_head hcur]; exact List.mem_cons_self)
    obtain ⟨t, hjt, hlt, c', hc', hat'⟩ := h3 x arms ss a hcur hz hf ha k0 hk0
    obtain ⟨evs, es3, rfl, hes3, hevN, hWn⟩ := succ_normC hc' hes2
    have ho' := pairAt_lt hpair hat'
    have ht30 : t < 2 ^ 30 := by have := hlen _ ho'; omega
    have hpct : s'.pc = t := by
      have h := rd_get hκ hm.fine hod (by rw [hm.fp]; exact hσ.jc.arm x arms hmem od a ha hax k0 t hσx hjt) hd
      have hgt : (g : K) ^ s'.pc = g ^ t := by simpa using congrArg (fun e : E ↦ e.limb 0) h
      exact gpow_lt_inj (by omega) (by omega) hgt
    refine Or.inr ⟨hself, t - Cf.X.entry, c'.pos, by omega, by omega, hat', (as ++ bs).map Ev.atom ++ evs, es3,
      by simp, hes3, evM_app (evM_atoms _) hevN, fun y hy ↦ ?_⟩
    exact hev y (hWn _ y (by simpa [List.append_assoc] using hy))
  · obtain ⟨-, -, h01⟩ := headH_ret hh hcur
    simp only [show (PairCtx.ofH Cf.X Cf.H Cf.frame.O Cf.frame.S).X.main = false from hmain, Bool.false_eq_true,
      ↓reduceIte] at h01
    rw [Zip.pos_head hcur, walk_ret_cons, Out.ret.injEq] at hes1
    obtain ⟨rfl, -⟩ := hes1
    exact Or.inl ⟨h01.1, h01.2, by simpa using evM_atoms (sigOf := Cf.sigOf) (rd := rd) (σ := σ) (as ++ bs),
      fun y hy ↦ hev y (by simpa using hy)⟩

theorem jtdGo_at {Cf : CFun} {E : Mode.Env} {ml : List (ℕ × ℕ)} : ∀ {code : List OffsetInstruction},
    jtdGo Cf E ml code = true → ∀ {i o1 o2 o3 : ℕ}, code[i]? = some (.deref o1 o2 o3 .cell) →
      jtd Cf.X o1 o2 o3 = true → ∃ oc of, code[i + 1]? = some (.jump oc o3 of) ∧ Cf.X.zeroAt oc = false ∧
        Cf.X.pcAt o3 = none ∧ o3 ≠ 0 ∧ ∃ a, getF Cf.X.arms o3 = some a ∧ ∀ p ∈ ml, p.1 = a.1 → ∀ j < p.2,
          E.jtLo ≤ a.2 + j ∧ a.2 + j < E.jtHi ∧ (E.jt.get (a.2 + j)).isSome = true
  | [], _, _, _, _, _, h, _ => by simp at h
  | ins :: code, h, i, o1, o2, o3, hi, hj => by
    simp only [jtdGo, Bool.and_eq_true] at h
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      have h1 := h.1
      simp only [hj, Bool.not_true, Bool.false_or] at h1
      split at h1
      · rename_i oc od of rest
        simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq, Option.isNone_iff_eq_none] at h1
        obtain ⟨⟨⟨⟨rfl, hz⟩, hpc⟩, h0⟩, h2⟩ := h1
        split at h2
        · rename_i a ha
          refine ⟨oc, of, rfl, hz, hpc, fun e ↦ by simp [e] at h0, a, ha, fun p hp hpa j hj' ↦ ?_⟩
          have h3 := List.all_eq_true.mp h2 p hp
          simp only [hpa, Nat.beq_refl, Bool.not_true, Bool.false_or, List.all_eq_true, List.mem_range,
            Bool.and_eq_true, decide_eq_true_eq] at h3
          exact ⟨(h3 j hj').1.1, (h3 j hj').1.2, (h3 j hj').2⟩
        · cases h2
      · cases h1
    | succ i => exact jtdGo_at h.2 (by simpa using hi) hj

/-- **A `DEREF` reading the jump table reads a written cell**: its table jump follows, by a `match` on
its selector, whose arm the path takes is a slot of the table; the selector's word its pointer. -/
theorem core_jtd {img : MemoryImage κ} (hκ : κ ≤ 28) {K : Mode.Cert} {Cf : CFun}
    (hpair : pairOk Cf.X Cf.H Cf.frame.O Cf.frame.S Cf.fn.body K.code Cf.d = true)
    (hctrl : ∀ s ∈ stmtsOf Cf.fn.body, ctrlOk s = true) (hjtd : jtdOk Cf K.E K.code = true)
    (hcalls : K.code.all (jumpCallOk Cf) = true)
    {s s1 : St} {i o1 o2 o3 : ℕ} (hins : K.code[i]? = some (.deref o1 o2 o3 .cell)) (hj : jtd Cf.X o1 o2 o3 = true)
    (ho1 : o1 < 2 ^ 28) (henv : Mode.EnvOk s K.E) (hm : Moves (refMem img) s s1)
    {σ : Val} (hσ : HonF img Cf s.fp σ) {pos : List Stmt} {pre es : List Ev} {vs : List V}
    (hat : pairAt Cf.P Cf.fn.body K.code Cf.d i = some pos) (hb : walk σ Cf.fn.body = .ret (pre ++ es) vs)
    (hwp : walk σ pos = .ret es vs) : HeapRd s1 (.deref o1 o2 o3 .cell) := by
  rw [jtdOk, Exec.listSeq_eq] at hjtd
  obtain ⟨oc, of, hci, hz, hpcn, h0, a, ha, hslots⟩ := jtdGo_at hjtd hins hj
  obtain ⟨pos', bs, hat', hpos⟩ := pair_next hpair hat (fun oc' od' of' h ↦ by rw [hins] at h; cases h)
  rw [hpos] at hwp
  obtain ⟨es', hwp', hes⟩ := walk_atoms_ret hwp
  obtain ⟨as, bs2, z, zs, tabs, r, hpos2, hzpos, -, -, -, -, hzsok, hr, -, -, -⟩ := pair_jump hpair hat' hci
  rw [hpos2, hzpos, ← List.append_assoc, ← List.map_append] at hwp'
  obtain ⟨es1, hes1, hes'⟩ := walk_atoms_ret hwp'
  have hf : fwdJ Cf.X (i + 1) oc o3 of = false := by simp [fwdJ, hpcn]
  have hh := headH_of hr hz hf
  obtain ⟨x, arms, ss, hcur⟩ : ∃ x arms ss, zs.cur = .match_ x arms :: ss := by
    rcases head_cases hzsok hctrl hh with ⟨x, fs, args, rets, ss, hcur⟩ | ⟨c', f', args', ss, hcur⟩ | hh4
    · obtain ⟨-, -, s0, -, -, hsite, htg, -⟩ := headH_dispatch hh hcur
      have hcj := List.all_eq_true.mp hcalls _ (List.mem_of_getElem? hci)
      have := (jumpCallOk_dsp hcj (siteAt_spec hsite).1 htg).2.2.1
      rw [ha] at this; cases this
    · obtain ⟨-, t, -, ht, -⟩ := headH_callIf hh hcur
      have ht' : Cf.X.pcAt o3 = some t := ht
      rw [hpcn] at ht'; cases ht'
    rcases hh4 with ⟨c, zb, nb, ss, hcur⟩ | h | ⟨vs', ss, hcur⟩ | ⟨f, args, rets, ss, hcur⟩
    rotate_left 3
    · obtain ⟨-, s0, t, -, -, -, ht, -⟩ := headH_call hh hcur
      have ht' : Cf.X.pcAt o3 = some t := ht
      rw [hpcn] at ht'; cases ht'
    · obtain ⟨-, -, t, -, -, -, ht, -⟩ := headH_ite hh hcur
      have ht' : Cf.X.pcAt o3 = some t := ht
      rw [hpcn] at ht'; cases ht'
    · exact h
    · obtain ⟨-, -, h01⟩ := headH_ret hh hcur
      split at h01
      · obtain ⟨-, ht⟩ := h01
        have ht' : Cf.X.pcAt o3 = some _ := ht
        rw [hpcn] at ht'; cases ht'
      · exact absurd h01.1 h0
  obtain ⟨-, -, hax, -⟩ := jumpH_match hr hcur hz hf ha
  obtain ⟨k, hk, hσx, -⟩ := side_arm hcur hes1
  have hmem : Stmt.match_ x arms ∈ stmtsOf Cf.fn.body :=
    zok_stmts hzsok (by rw [Zip.pos_head hcur]; exact List.mem_cons_self)
  obtain ⟨hlo, hhi, hjt⟩ := hslots _ (matchLens_mem hmem) hax.symm k hk
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hjt
  obtain ⟨-, hjtHi, henv3⟩ := henv
  have hw := written_mono hm.le (written_of_get (henv3 _ e hlo hhi he))
  simp only [jtd, ha, Bool.and_eq_true, Nat.beq_eq] at hj
  obtain ⟨hbase, hloc⟩ := hj
  have hsel := hσ.jc.sel _ _ hb x arms hmem
  rw [← hax, hloc] at hsel
  intro p y hp hy
  have hpv : p = σ x := rd_get hκ hm.fine ho1 (by rw [hm.fp]; exact hsel) hp
  have h1 := hy.1
  rw [hpv, hσx, ← ofK_mul', ← pow_add, limb_ofK] at h1
  have hlt : k + o2 < 2 ^ 63 := by have := lt_maxCells_63 (x := a.2 + k) (by omega); omega
  have hyx := gpow_inj hlt (lt_maxCells_63 hy.2) h1
  rw [← hyx, show k + o2 = a.2 + k by omega]
  exact hw

/-- **The entry abstraction holds** of its parts, its self cell (a loop's) holding its frame's address. -/
theorem holds_entryAbs {E0 : Mode.Env} {G : Mode.Sig} {s : St}
    (h0 : Mode.Holds s ⟨Mode.foldlT .nil G.entry, .nil, .nil, [], G.pre, Mode.jtRng E0 :: G.preR, G.term, [], .nil,
      G.preP, []⟩)
    (hself : ∀ o, G.self = some o → s.mem.written (s.fp + o) = true ∧ s.mem.get (s.fp + o) = some (ofK (g ^ s.fp))) :
    Mode.Holds s (entryAbs E0 G) := by
  unfold entryAbs
  rcases hs : G.self with _ | o
  · exact h0
  · obtain ⟨hwo, hgo⟩ := hself o hs
    refine ((h0.addW hwo).addV ⟨_, hgo, ?_⟩).addNz ⟨_, hgo, Mode.ofK_gpow_ne_zero _⟩
    exact ⟨1, rfl, by simp [Mode.Mono.own]⟩

/-- The reference's words of a frame's slots, a prefix of `ws` the frame's cells hold. -/
theorem wsAt_take {img : MemoryImage κ} {fp n : ℕ} {ws : List E}
    (h : ∀ b < n, Rd img fp (2 + b) = some (slotW ws b)) {k : ℕ} (hkn : k ≤ n) (hk : k ≤ ws.length) :
    wsAt img fp k = ws.take k := by
  apply List.ext_getElem (by simp [wsAt]; omega)
  intro b h1 h2
  simp only [wsAt, List.length_map, List.length_range] at h1
  simp only [wsAt, List.getElem_map, List.getElem_range, List.getElem_take]
  rw [h b (by omega), slotW_get (by omega)]
  rfl

/-- The reference's words of a frame's slots, the words `ws` its cells hold. -/
theorem wsAt_eq {img : MemoryImage κ} {fp n : ℕ} {ws : List E} (hn : ws.length = n)
    (h : ∀ b < n, Rd img fp (2 + b) = some (slotW ws b)) : wsAt img fp n = ws := by
  rw [wsAt_take h le_rfl (by omega), List.take_of_length_le (by omega)]

/-- A call checked by `callChk` names no callee ghost. -/
theorem callChk_ghosts {Cf : CFun} {g : String} {args : List V} (h : callChk Cf g args = true) :
    (Cf.sigOf g).ghosts = 0 := by
  simp only [callChk, Bool.and_eq_true] at h
  simpa using h.1.1.2

/-- **The core route meets the frame interface**: a function passing the kernel's checks, on the
executor's tables for the guest's advice, its code the executor's, at states `Y` on a reference run
where its frames have honest valuations. -/
theorem frameSpec_core {K : Mode.Cert} {Cf : CFun} (hok : CoreOk K Cf) {adv : Prover.Exec.Advice} {C : Ctx}
    (hC : Prover.Exec.Ctx.of guestProgram adv = .ok C) (ha : adv.hints = Data.adviceHints) (hK : CodeOk C K)
    {img : MemoryImage κ} {Y : St → Prop} (hκ : κ ≤ 28) (hY : ∀ s, Y s → ∃ n, OnRef guestProgram img n s)
    (hH : CoreHon img Y K Cf) (hU : UsedNext C img Y) {Ct : Mode.Cts} (hCt : CtOk img Ct K Cf) :
    FrameSpec C (refMem img) Y Ct K (CoreAt img Cf K.code) := by
  have hsh := hok.shape
  simp only [shapeOk, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, List.all_eq_true,
    Option.isNone_iff_eq_none] at hsh
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hbody, hmainX⟩, hself1⟩, hpc0⟩, hrN⟩, htgt⟩, hsout⟩, hfp1⟩, hnzr0⟩, hent⟩, hend⟩, hincr⟩ := hsh
  have hctrl := bodyC_ctrl hbody
  obtain ⟨henv, harm, hacc⟩ := hok.frame
  have hown := hok.sig
  unfold ownOk at hown
  have hsigM : Cf.hc = false → sigOk K.F.sig Cf Cf.fn.params.length (retN Cf.fn.body) = true := fun h ↦ by
    rw [h] at hown; exact hown
  obtain ⟨hself, hghost⟩ : K.F.sig.self = none ∧ (Cf.hc = true → Cf.H.sig.ghosts = 0) := by
    cases hc : Cf.hc
    · have hs := hsigM hc
      simp only [sigOk, Bool.and_eq_true, Option.isNone_iff_eq_none] at hs
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hs
      exact ⟨h1, fun h ↦ by cases h⟩
    · rw [hc] at hown
      simp only [hcOwn, Bool.cond_true, Bool.and_eq_true, Option.isNone_iff_eq_none] at hown
      exact ⟨hown.1.1.1.1, fun _ ↦ by simpa using hown.2⟩
  have hent' : ∀ x ∈ K.F.sig.entry, x + 1 < 2 ^ Exec.envDepth := hok.fsig ▸ hent
  have hpar := heapK_params hok.heap
  set np := Cf.fn.params.length with hnp
  have hws0 : ∀ {fp : ℕ} {σ : Val}, HonF img Cf fp σ →
      ∀ b < np, Rd img fp (2 + b) = some (slotW (Cf.fn.params.map σ) b) := by
    intro fp σ hσ b hb
    rw [slotW_params' hpar hb]
    exact hσ.par b hb
  have hws0' : ∀ {fp : ℕ} {σ : Val}, HonF img Cf fp σ →
      ∀ b < np, Rd img fp (2 + b) = some (slotW (Cf.fn.params.map σ ++ ownG Cf.H.sig σ) b) := by
    intro fp σ hσ b hb
    rw [slotW_lt (by simpa using hb)]
    exact hws0 hσ b hb
  refine ⟨fun hle hfp h ↦ h.mono hle hfp, ?_, ?_⟩
  · -- the entry
    intro s hH0 hs
    cases hhc : Cf.hc
    case true =>
      -- a heap contract: its preconditions at the parameters' words
      rw [preAt_ownH hCt hhc] at hH0
      obtain ⟨hw, hpreH⟩ := hH0
      refine coreAt_of (by rw [CFun.xc, hhc]; intro o ho; cases ho) ⟨atF_mono (s := s) (Mem.le_refl _) rfl
        (atF_entry henv ⟨fun o ho ↦ hw o (hok.fsig ▸ ho), fun o hso ↦ by rw [hok.fsig, hself] at hso; cases hso⟩),
        fun o ho ↦ hw o (hok.fsig ▸ ho), fun σ hσ ↦ ?_⟩
      obtain ⟨es, vs, -, hwk, -⟩ := hσ.path
      refine ⟨Cf.fn.body, [], es, vs, img.read, rfl, pairAt_zero hok.pair, by simpa using hwk, hwk,
        by simpa using hσ.holds _ _ hwk, by simp, fun y hy ↦ ?_⟩
      simp only [WrittenC, ownG_zero (hghost hhc), List.append_nil] at hy
      rcases hy with hy | ⟨e, he, -⟩
      · exact hpreH y (by rw [wsAt_eq (by simp [hnp]) (hws0 hσ)]; exact hy)
      · cases he
    rw [preAt_own hCt hhc] at hH0
    have hsig := hsigM hhc
    simp only [sigOk, Bool.and_eq_true, Option.isNone_iff_eq_none, List.isEmpty_iff, List.all_eq_true] at hsig
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hpreP⟩, hprePR⟩, hpre⟩, hpreR⟩, -⟩, -⟩, -⟩ := hsig
    have hA : entryAbs K.E K.F.sig = ⟨Mode.foldlT .nil K.F.sig.entry, .nil, .nil, [], K.F.sig.pre,
        Mode.jtRng K.E :: K.F.sig.preR, K.F.sig.term, [], .nil, K.F.sig.preP, []⟩ := by
      unfold entryAbs
      rw [hself]
    rw [hA] at hH0
    have hw : ∀ o ∈ K.F.sig.entry, s.mem.written (s.fp + o) = true := fun o ho ↦
      hH0.w o (foldlT_mem _ _ hent' ho)
    refine coreAt_of (by rw [CFun.xc_of hhc, hok.fsig]; exact expW_of hκ hs.agree (fun r hr ↦ hH0.r r (List.mem_cons_of_mem _ hr)) hH0.p)
      ⟨atF_mono (s := s) (Mem.le_refl _) rfl (atF_entry henv ⟨fun o ho ↦ hw o (hok.fsig ▸ ho),
      fun o hso ↦ by rw [hok.fsig, hself] at hso; cases hso⟩), fun o ho ↦ hw o (hok.fsig ▸ ho), fun σ hσ ↦ ?_⟩
    obtain ⟨es, vs, -, hwk, -⟩ := hσ.path
    refine ⟨Cf.fn.body, [], es, vs, img.read, rfl, pairAt_zero hok.pair, by simpa using hwk, hwk,
      by simpa using hσ.holds _ _ hwk, by simp,
      fun y hy ↦ ?_⟩
    have hSE : ∀ {m : Mode.Mono}, monoS K.F.sig np false m = true →
        SlotEq s (Cf.fn.params.map σ ++ ownG Cf.H.sig σ) m.bs :=
      fun hm ↦ slotEq_of hκ hs.agree hs.fp (hws0' hσ) hm
    simp only [WrittenC] at hy
    rcases hy with ((⟨c, hc, rfl⟩ | ⟨r, hr, hx⟩) | (⟨p, hp, hps⟩ | ⟨p, hp, a, ha', hpa⟩)) | ⟨e, he, -⟩
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
    · rcases Bool.or_eq_true_iff.mp (hpreR r hr) with hany | hcov
      swap
      · exact rw_cov hcov (fun r' _ hm ↦ hSE hm) (fun r' hr' ↦ hH0.r r' (List.mem_cons_of_mem _ hr')) y hx
      obtain ⟨r', hr', hrq⟩ := List.any_eq_true.mp hany
      rcases Bool.or_eq_true_iff.mp hrq with hrq | hrq
      · rcases Bool.or_eq_true_iff.mp hrq with hrq | hrq
        · rw [Bool.and_eq_true] at hrq
          obtain ⟨hmS, hrq⟩ := hrq
          unfold rngIs at hrq
          split at hrq
          · rename_i q hq
            obtain rfl := of_decide_eq_true hrq
            exact rw_slot hq (hSE hmS) (hH0.r r' (List.mem_cons_of_mem _ hr')) y hx
          · cases hrq
        · rw [Bool.and_eq_true] at hrq
          obtain ⟨hmS, hrq⟩ := hrq
          unfold rngXIs at hrq
          split at hrq
          · rename_i q hq
            obtain rfl := of_decide_eq_true hrq
            exact rw_slotX hq (hSE hmS) (hH0.r r' (List.mem_cons_of_mem _ hr')) y hx
          · cases hrq
      · -- a run over the caller's linked cells
        rw [Bool.and_eq_true] at hrq
        obtain ⟨hbs, hrq⟩ := hrq
        unfold rngLIs at hrq
        split at hrq
        · rename_i q hq
          obtain rfl := of_decide_eq_true hrq
          exact rw_slotL hq (slotEqL_of hκ hs.agree hs.fp (hws0' hσ) hσ.gl hbs) (hH0.r r' (List.mem_cons_of_mem _ hr'))
            y hx
        · cases hrq
    · obtain ⟨w', hw', o, ho, rfl⟩ := hps
      have hall := hpreP p hp
      unfold hpAll at hall
      obtain ⟨m, hm, hmm⟩ := List.any_eq_true.mp (List.all_eq_true.mp hall o ho)
      split at hmm
      · rename_i q d hqd
        simp only [Bool.and_eq_true, Nat.beq_eq] at hmm
        obtain ⟨⟨hsl, hpb⟩, rfl⟩ := hmm
        rw [CCell.beq_eq hpb] at hw'
        have h2 : 2 ≤ q := by simp only [hpSlot, Bool.and_eq_true, decide_eq_true_eq] at hsl; exact hsl.1.1.1
        exact hw_hp hκ hs.agree h2 (hSE (monoS_fr hsl)) (hpOf_spec hqd ▸ hH0.h m hm) hw'
      · cases hmm
    · obtain ⟨r', hr', hrp⟩ := List.any_eq_true.mp (hprePR p hp)
      simp only [prunIs, rngXIs, Bool.and_eq_true, decide_eq_true_eq] at hrp
      obtain ⟨hmS, hrq, hos⟩ := hrp
      split at hrq
      · rename_i q hq
        obtain rfl := of_decide_eq_true hrq
        rw [← hos] at hpa
        exact pw_slotX hκ hs.agree hq (hSE hmS) (hH0.p r' hr') y ⟨a, ha', hpa⟩
      · cases hrq
    · cases he
  · -- a step
    intro s i hi hpc hat hs hYs hsz _ henvK _ hjtR _ _ _ hh _ href Inv k
    obtain ⟨hAtF0, hentw, hheap⟩ := hat.2 s.mem (Mem.le_refl _) hs.agree
    have hxw := hat.1
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
        ResF Cf.H σ → (∀ e ∈ pre, EvM Cf.sigOf rd σ e) → ReadsAt Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) pre es :=
      fun σ pre es vs rd hb hh0 hR hM ↦ readsAt_of_P (heapK_reads hok.heap hok.pows hbody hb hh0 hR) hM
    have he1 : ∀ s1, (Mode.hintsAt Cf.frame.hints (Cf.frame.entry + i)).foldlM (Prover.Exec.runHint C) s = .ok s1 →
        ((C.hints[s.pc]?).getD []).foldlM (Prover.Exec.runHint C) s = .ok s1 := fun s1 e1 ↦ by
      rw [hpcF, hhintsF i hi]; exact e1
    have hlen : Cf.frame.len = K.code.length := hok.flen
    have hlenX : ∀ o < K.code.length, Cf.X.entry + o < 2 ^ 30 := fun o ho ↦ by
      have h := hK.ops o ho
      rw [hok.xentry]
      by_contra hn
      rw [Array.getElem?_eq_none (by omega)] at h
      cases h
    have hsm : ∀ oc od of, K.code[i]? = some (.jump oc od of) → oc < 2 ^ 28 ∧ od < 2 ^ 28 ∧ of < 2 ^ 28 :=
      fun oc od of hci ↦ by
        have h := hok.small i hi
        rw [List.getElem?_eq_getElem hi, Option.some.injEq] at hci
        rw [hci] at h
        exact h
    refine frame_step (prog := guestProgram) (k := n - s.steps) hκ harm hacc hok.fpows hend hsz
      (fun j hj ↦ by rw [hok.fentry]; exact hK.ops j hj) hhintsF (hok.fentry ▸ hok.fetch) hok.small hi hpcF hAtF hs
      hon.2 (fun h ↦ absurd h (by simp [hfp1]))
      (fun pre h post hp s1 e hm hin ↦ hh pre h post (by rw [hpcF, hhintsF i hi]; exact hp) s1 e hm hin)
      (fun o ho ↦ by simp [trieNil_get hnzr0] at ho) ?_ ?_
      (fun s1 hm ↦ refOk_fp hm.fp href) ?_ ?_
    · -- the oracle's heap cell, written
      intro hOi s1 e1 hm
      have main : ∀ a o c, K.code[i] = .deref a o c .cell → HeapRd s1 (.deref a o c .cell) := by
        intro a o c hci
        obtain ⟨pos, pre, es, vs, rd, hrd, hpos, hb, hwp, hh0, hM0, hW⟩ := hheap σ0 hσ0
        by_cases hj : jtd Cf.X a o c = true
        · have hsm := hok.small i hi
          rw [hci] at hsm
          exact core_jtd hκ hok.pair hctrl hok.jtd hok.calls (by rw [List.getElem?_eq_getElem hi, hci]) hj hsm.1 henvK hm hσ0
            hpos hb hwp
        obtain ⟨as, dv, pv, off, hpairs, hcell, -, hmem, hwr⟩ := pair_readC hok.pair hpos
          (by rw [List.getElem?_eq_getElem hi, hci]) (by rw [← has_hasP]; exact hOi) (Bool.eq_false_iff.mpr hj) hwp
          (hrwOf σ0 pre es vs rd hb hh0 (hσ0.res hxw) hM0)
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
    · -- a table jump's target, one of its arms
      obtain ⟨pos, pre, es, vs, rd, hrd, hpos, hb, hwp, -, -, -⟩ := hheap σ0 hσ0
      exact core_tgt hok.pair hctrl hmainX htgt (callsB_of' hok.heap) hσ0 hpos hb hwp
    · -- falling through
      intro s1 s' e1 hm hmo e' hpc' hfp' hf' hle' hat' hstw hc0
      have hle : s.mem ≤ s'.mem := Mem.le_trans hm.le hle'
      have hi1 : i + 1 < K.code.length := by
        by_contra hn
        obtain ⟨cur, pend, h0, hh0⟩ := hat'
        obtain ⟨rfl, rfl⟩ := preF_end hacc (by omega) h0
        rcases hh0 with ⟨A, hA, -⟩ | ⟨g', hg', -⟩
        · cases hA
        · cases hg'
      refine k s1 s' (he1 s1 e1) hm hmo e' hf' hle' (.move (i + 1) (hfp'.trans hm.fp.symm) hi1
        (by rw [hpc', hpc]; omega) (coreAt_of (by rw [hfp']; exact hxw) ⟨atF_mono (s := s') (Mem.le_refl _) rfl hat',
          fun o ho ↦ by rw [hfp']; exact written_mono hle (hentw o ho), fun σ hσ ↦ ?_⟩))
      rw [hfp'] at hσ
      obtain ⟨pos, pre, es, vs, rd, hrd, hpos, hb, hwp, hh0, hM0, hW⟩ := hheap σ hσ
      by_cases hj : ∃ oc od of, K.code[i]? = some (.jump oc od of)
      · -- a jump not taken
        obtain ⟨oc, od, of, hci⟩ := hj
        have e1' : ((Cf.d.2.2.lookup (Cf.X.entry + i)).getD []).foldlM (Prover.Exec.runHint C) s = .ok s1 := by
          rw [hhd i]; exact e1
        obtain ⟨pos', hpos', evs, es', rfl, hwp', hevs, hWr⟩ := core_jfall hκ hok.pair hctrl hci (hsm oc od of hci).1 e1'
          hs hm (hc0 oc od of hci) hσ hpos hb hwp (hrwOf σ pre _ vs rd hb hh0 (hσ.res hxw) hM0) hW
        exact ⟨pos', pre ++ evs, es', vs, rd, hrd, hpos', by rw [List.append_assoc]; exact hb, hwp',
          by rw [List.append_assoc]; exact hh0, evM_app hM0 hevs, fun y hy ↦ (hWr y hy).mono hle'⟩
      have hnj : ∀ oc od of, K.code[i]? ≠ some (.jump oc od of) := fun oc od of h ↦ hj ⟨oc, od, of, h⟩
      obtain ⟨pos', hpos', as, hpairs, hfallP⟩ := pair_fallC (sigOf := Cf.sigOf) (rd := rd)
        (ws0 := Cf.fn.params.map σ) hok.pair hpos hnj
      obtain ⟨evs, es', rfl, hwp', hevs, hWr⟩ := hfallP hwp (hrwOf σ pre _ vs rd hb hh0 (hσ.res hxw) hM0)
      refine ⟨pos', pre ++ evs, es', vs, rd, hrd, hpos', by rw [List.append_assoc]; exact hb, hwp',
        by rw [List.append_assoc]; exact hh0, evM_app hM0 hevs, fun y hy ↦ ?_⟩
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
      intro s1 s' e1 hm hmo e' hf' hle' hjo hjt hcn
      obtain ⟨oc, od, of, hci, h0, h1, hpcs⟩ := hjt
      have hcode : K.code[i] = .jump oc od of := Option.some.inj ((List.getElem?_eq_getElem hi).symm.trans hci)
      have hsm := hok.small i hi
      rw [hcode] at hsm
      obtain ⟨soc, sod, sof⟩ := hsm
      have hw1 : ∀ o ∈ K.F.sig.entry, s1.mem.written (s1.fp + o) = true := fun o ho ↦ by
        rw [hm.fp]; exact written_mono hm.le (hentw o (hok.fsig ▸ ho))
      have e1' : ((Cf.d.2.2.lookup (Cf.X.entry + i)).getD []).foldlM (Prover.Exec.runHint C) s = .ok s1 := by
        rw [hhd i]; exact e1
      obtain ⟨v, hv, hv0⟩ := hcn oc od of hci
      have hz : Cf.X.zeroAt oc = false := by
        cases hzz : Cf.X.zeroAt oc
        · rfl
        · exact absurd (rd_get hκ hm.fine soc (by rw [hm.fp]; exact hσ0.jc.zero oc hzz) hv) hv0
      have hcall0 := List.all_eq_true.mp hok.calls _ (List.getElem_mem hi)
      rw [hcode] at hcall0
      by_cases hsf : Cf.X.selfAt of = true
      · -- a jump in the frame: a branch's side, a `match`'s arm, a forward jump
        have hof1 : of ≠ 1 := fun h ↦ by rw [h, hself1] at hsf; cases hsf
        have hcj : ∀ t f, Cf.X.pcAt od = some t → getF Cf.X.ents t = some f → Cf.X.selfAt of = false :=
          fun t f ht hf ↦ (jumpCallOk_spec hcall0 ht hf).2.2.1
        have hdn : ∀ s, getF Cf.X.sites of = some s → s.tgt = od → Cf.X.selfAt of = false :=
          fun s hs he ↦ (jumpCallOk_dsp hcall0 hs he).2.2.2
        have hpcs' : s'.pc < 2 ^ 30 := by omega
        obtain ⟨pos, pre, es, vs, rd, hrd, hpos, hb, hwp, hh0, hM0, hW⟩ := hheap σ0 hσ0
        rcases core_jtaken hκ hok.pair hctrl hmainX hlenX hci hcj hsf hdn soc sod e1' hs hm hv hv0 h0 hpcs' hσ0 hpos hb hwp
          (hrwOf σ0 pre es vs rd hb hh0 (hσ0.res hxw) hM0) hW with ⟨-, h1', -⟩ | ⟨-, o, pos0, hpco, hio, hpos0, -⟩
        · exact absurd h1' hof1
        have hol := pairAt_lt hok.pair hpos0
        cases hjo with
        | «local» t hnr hfp' hpc' hat' =>
          have hto : t = o := by rw [hok.fentry, ← hok.xentry] at hpc'; omega
          subst hto
          have hle : s.mem ≤ s'.mem := Mem.le_trans hm.le hle'
          refine k s1 s' (he1 s1 e1) hm hmo e' hf' hle' (.move t hfp' hol (by rw [hpc', hok.fentry])
            (coreAt_of (by rw [hfp', hm.fp]; exact hxw) ⟨atF_mono (s := s') (Mem.le_refl _) rfl hat',
              fun o ho ↦ by rw [hfp', hm.fp]; exact written_mono hle (hentw o ho), fun σ hσ ↦ ?_⟩))
          rw [hfp', hm.fp] at hσ
          obtain ⟨pos, pre, es, vs, rd, hrd, hpos, hb, hwp, hh0, hM0, hW⟩ := hheap σ hσ
          rcases core_jtaken hκ hok.pair hctrl hmainX hlenX hci hcj hsf hdn soc sod e1' hs hm hv hv0 h0 hpcs' hσ hpos hb
            hwp (hrwOf σ pre es vs rd hb hh0 (hσ.res hxw) hM0) hW with ⟨-, h1', -⟩ |
              ⟨-, o', pos', hpco', -, hpos', evs, es', rfl, hwp', hevs, hWr⟩
          · exact absurd h1' hof1
          have ho' : o' = t := by omega
          subst ho'
          exact ⟨pos', pre ++ evs, es', vs, rd, hrd, hpos', by rw [List.append_assoc]; exact hb, hwp',
            by rw [List.append_assoc]; exact hh0, evM_app hM0 hevs, fun y hy ↦ (hWr y hy).mono hle'⟩
        | ret _ _ hr =>
          obtain ⟨c, hc⟩ := hr
          rw [hci, Option.some.injEq, OffsetInstruction.jump.injEq] at hc
          exact absurd hc.2.2 hof1
        | halt _ h1 => simp [hfp1] at h1
        | tail e _ hpc' => rw [hpc', hok.fentry, ← hok.xentry] at hpco; omega
        | call G t _ _ hG _ _ _ =>
          have h := List.all_eq_true.mp hsout o (List.mem_range.mpr (by rw [hlen]; exact hol))
          simp only [Bool.or_eq_true, Nat.beq_eq] at h
          rcases h with h | h
          · omega
          rw [hpco, hok.xentry, ← hok.fentry] at hG
          rw [hG] at h
          cases h
      have hsf' : Cf.X.selfAt of = false := by simpa using hsf
      have hfw : fwdJ Cf.X i oc od of = false := by simp [fwdJ, hsf']
      by_cases hr01 : od = 0 ∧ of = 1
      · -- the return
        obtain ⟨rfl, rfl⟩ := hr01
        have hrj : ∃ c, K.code[i]? = some (.jump c 0 1) := ⟨oc, hci⟩
        cases hjo with
        | «local» t hnr => exact absurd hrj hnr
        | halt hnr => exact absurd hrj hnr
        | tail e hnr => exact absurd hrj hnr
        | call G t hnr => exact absurd hrj hnr
        | ret hregs hretw _ =>
          refine k s1 s' (he1 s1 e1) hm hmo e' hf' hle' (.ret oc hci (by omega) h0 h1 ?_)
          obtain ⟨pos, pre, es, vs, rd, hrd, hpos, hb, hwp, hh0, hM0, hW⟩ := hheap σ0 hσ0
          obtain ⟨as, hpairs, hevR, hpr⟩ := pair_retC hok.pair hpos hci hz hfw hpc0 hself1 hwp
            (hrwOf σ0 pre es vs rd hb hh0 (hσ0.res hxw) hM0)
          obtain ⟨-, -, hposts, hpostRs, hretM, hpostM, hptrs, hretV, hretE⟩ :=
            heapK_sound hok.heap hok.pows hbody hb hh0 (hσ0.res hxw) (evM_app hM0 hevR)
          rw [hhd i] at hpairs
          have W1 : ∀ x, WrittenC Cf.sigOf Cf.H rd σ0 (Cf.fn.params.map σ0) (pre ++ es) x → WrK s1.mem x := by
            intro x hx
            rcases hpr x hx with h | ⟨a, ha, hfa, hma, hwa⟩
            · exact (hW _ h).mono hm.le
            · exact flow_wrk hκ e1 hs hm hpairs ha hfa
                (fun q hq ↦ hσ0.ptr _ _ hb a q (List.mem_append_right _ hma) hq) hwa
          have hvl : vs.length = retN Cf.fn.body := retsN_len hrN hb
          have hxw1 : Cf.hc = false → ExpW img (expCells K.F.sig) s1.fp := fun hc ↦ by
            rw [hm.fp, ← hok.fsig, ← CFun.xc_of hc]; exact hxw
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
          have htop : Cf.fn.body.all topOk = true := by
            simp only [bodyC, Bool.and_eq_true] at hbody
            exact hbody.2
          have hcellsP : ∀ m, monoOkP K.F.sig Cf.fn.params.length m = true →
              BaseCellsF (baseOfP Cf.X Cf.fn.body Cf.fn.params.length) (Mode.stOf s1.mem s1.fp) σ0 m.bs :=
            fun m hmk ↦ baseCellsP_of (s := s1) hκ hmk htop hm.fine hw1
              (fun o ho ↦ hretw o (hok.fsig ▸ ho)) (hm.fp ▸ hσ0) hb
              (fun a ha y hy ↦ W1 y (Or.inr ⟨.atom a, ha, hy⟩))
          have hin : ∀ c, cellIn c (Cf.post.map (·.1)) = true → WrK s1.mem (c.addr σ0) := by
            intro c hc
            obtain ⟨c', hc', hbeq⟩ := List.any_eq_true.mp hc
            rw [← CCell.beq_eq hbeq]
            obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc'
            exact W1 _ (hpostM p hp)
          have hSG : ∀ {m : Mode.Mono}, monoR K.F.sig np (retN Cf.fn.body) m = true →
              SlotGet (Mode.stOf s1.mem s1.fp) (Cf.fn.params.map σ0 ++ vs.map σ0) m.bs :=
            fun hm' ↦ slotGet_ret (s := Mode.stOf s1.mem s1.fp) hκ hm.fine.agree hm.fine.fp hws hw1
              (fun o ho ↦ hretw o (hok.fsig ▸ ho)) hm'
          cases hhc : Cf.hc
          case true =>
            -- a heap contract: its guarantees and returned words at its slots' words
            rw [postAt_ownH hCt hhc]
            have hwsA : wsAt img s1.fp (Cf.fn.params.length + retN Cf.fn.body) =
                Cf.fn.params.map σ0 ++ vs.map σ0 := wsAt_eq (by simp [hvl]) hws
            have hwsP : wsAt img s1.fp Cf.fn.params.length = Cf.fn.params.map σ0 :=
              wsAt_eq (by simp) fun b hb' ↦ by rw [hws b (by omega), slotW_lt (by simpa using hb')]
            refine ⟨fun o ho ↦ hretw o (hok.fsig ▸ ho), fun y hy ↦ ?_, ?_⟩
            · rw [hwsA] at hy
              rcases hy with (⟨c, hc, rfl⟩ | ⟨r, hr, hx⟩) | hp
              · exact W1 _ (hposts c (List.mem_append_right _ hc))
              · exact W1 _ (hpostRs r hr _ hx)
              · rw [← hrd] at hp; exact W1 _ (hptrs _ hp)
            · rw [hwsP, hwsA, List.drop_left' (by simp)]
              exact ⟨hretM, hrd ▸ hretV, hretE⟩
          rw [postAt_own hCt hhc]
          have hsig := hsigM hhc
          simp only [sigOk, Bool.and_eq_true, Option.isNone_iff_eq_none, List.isEmpty_iff, List.all_eq_true] at hsig
          obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, hpostL⟩, hpostP⟩, hpostLP⟩, hpostT⟩, hpostC⟩, -⟩, -⟩, -⟩, -⟩, hpost⟩, hpostR⟩, -⟩ :=
            hsig
          refine ⟨⟨fun o ho ↦ hretw o (hok.fsig ▸ ho), fun m hm' ↦ ?_, fun r hr ↦ ?_, fun q hq ↦ ?_,
            fun p hp ↦ ?_, fun p hp ↦ ?_, fun q hq ↦ ?_⟩, fun r hr ↦ ?_, fun q hq ↦ ?_⟩
          · rcases Bool.or_eq_true_iff.mp (hpost m hm') with hc | hc
            · rcases Bool.or_eq_true_iff.mp hc with hc | hc
              · rw [Bool.and_eq_true] at hc
                obtain ⟨hmR, hc⟩ := hc
                split at hc
                · rename_i c hmc
                  obtain ⟨c', hc', hbeq⟩ := List.any_eq_true.mp hc
                  rw [CCell.beq_eq hbeq] at hc'
                  exact slot_hw hmc (hSG hmR) (W1 _ (hposts c hc'))
                · cases hc
              · simp only [postIn, Bool.and_eq_true] at hc
                obtain ⟨hmk, hc⟩ := hc
                split at hc
                · rename_i c hmc
                  exact wrk_hwF (expKeep_P _ _ _) hmc (hcellsP m hmk) (hin c hc)
                · cases hc
            · unfold hpIn at hc
              split at hc
              · rename_i q d hqd
                simp only [Bool.and_eq_true] at hc
                obtain ⟨⟨hsl, hcl⟩, hps⟩ := hc
                obtain ⟨p', hp', hpp⟩ := List.any_eq_true.mp hps
                simp only [Bool.and_eq_true, List.contains_iff_mem] at hpp
                obtain ⟨hpb, hko⟩ := hpp
                have h2 : 2 ≤ q := by
                  simp only [hpSlot, Bool.and_eq_true, decide_eq_true_eq] at hsl; exact hsl.1.1.1
                have hmR : monoR K.F.sig np (retN Cf.fn.body) ⟨0, 0, [(.fr q, 1)]⟩ = true := by
                  simp only [hpSlot, Bool.and_eq_true, decide_eq_true_eq, Bool.not_true, Bool.false_or,
                    List.contains_iff_mem] at hsl
                  have h28 : q < 268435456 := hsl.1.2
                  simp [monoR, hsl.1.1.1, h28, hsl.1.1.2, hsl.2]
                have hu1 : s1.mem.used ≤ 2 ^ κ := le_trans hle'.used
                  (hU s _ s1 s' hYs (by rw [hpc]; exact hK.ops i hi) (he1 s1 e1) hm e')
                obtain ⟨c', hc', hbeq⟩ := List.any_eq_true.mp hcl
                rw [CCell.beq_eq hbeq] at hc'
                rw [hpOf_spec hqd]
                refine hp_hw (s := Mode.stOf s1.mem s1.fp) hκ hm.fine.agree hu1 h2 (hSG hmR)
                  (W1 _ (hposts _ hc')) fun w hw ↦ ?_
                refine W1 _ (hptrs _ (Or.inl ⟨p', hp', w, ?_, m.k, hko, rfl⟩))
                rw [CCell.beq_eq hpb, hrd]
                exact hw
              · cases hc
          · rcases Bool.or_eq_true_iff.mp (hpostR r hr) with h | h
            swap
            · -- bounded by an entry run's exponent cell
              simp only [Bool.and_eq_true] at h
              obtain ⟨⟨⟨hmR, hlo⟩, hhi⟩, hq⟩ := h
              obtain ⟨q, hq, hrq⟩ := List.any_eq_true.mp hq
              unfold rngXIs at hrq
              split at hrq
              · rename_i q' hq'
                obtain rfl := of_decide_eq_true hrq
                obtain ⟨hl, hh⟩ := rngX_rep_exp hws (hxw1 hhc) (fun k hk ↦ by rw [hm.fp]; exact hσ0.par k hk) (hσ0.res hxw) hq' hlo hhi
                exact slot_rwX hq' (hSG hmR) hl hh fun x hx ↦ W1 x (hpostRs q' hq x hx)
              · cases hrq
            rcases Bool.or_eq_true_iff.mp h with h | h
            swap
            · simp only [postRIn, Bool.and_eq_true] at h
              obtain ⟨hmk, hc⟩ := h
              split at hc
              · rename_i c hmc
                split at hc
                · rename_i l hl
                  exact wrk_rwF (expKeep_P _ _ _) hmc (hcellsP r.q hmk) hl fun p hp ↦ hin p (List.all_eq_true.mp hc p hp)
                · cases hc
              · cases hc
            rw [Bool.and_eq_true] at h
            obtain ⟨hmR, h⟩ := h
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
          · obtain ⟨⟨⟨⟨hmR, hlo⟩, hhi⟩, hpr⟩, hrr⟩ := hpostP q hq
            obtain ⟨p', hp', hpp⟩ := List.any_eq_true.mp hpr
            simp only [prunIs, rngXIs, Bool.and_eq_true, decide_eq_true_eq] at hpp
            obtain ⟨hrq, hos⟩ := hpp
            split at hrq
            · rename_i q' hq'
              have hpq : q' = p'.1 := of_decide_eq_true hrq
              obtain ⟨q2, hq2, hrr'⟩ := List.any_eq_true.mp hrr
              unfold rngXIs at hrr'
              rw [hq'] at hrr'
              have hq2e : q' = q2 := of_decide_eq_true hrr'
              subst hq2e
              have hu1 : s1.mem.used ≤ 2 ^ κ := le_trans hle'.used
                (hU s _ s1 s' hYs (by rw [hpc]; exact hK.ops i hi) (he1 s1 e1) hm e')
              obtain ⟨hl, hh⟩ := rngX_rep_exp hws (hxw1 hhc) (fun k hk ↦ by rw [hm.fp]; exact hσ0.par k hk) (hσ0.res hxw) hq' hlo hhi
              refine slot_pwX (s := Mode.stOf s1.mem s1.fp) hκ hm.fine.agree hu1 hq' (hSG hmR) hl hh
                (fun x hx ↦ W1 x (hpostRs q' hq2 x hx)) fun x hx ↦ ?_
              obtain ⟨a, ha, hpa⟩ := hx
              refine W1 x (hptrs x (Or.inr ⟨p', hp', a, ?_⟩))
              rw [← hpq, ← hos, hrd]
              exact ⟨ha, hpa⟩
            · cases hrq
          · obtain ⟨h28, hret', hmo', c, hmc, hcase⟩ := retVOk_sound hok.pows (by simpa [hhc] using hok.retv) hb hh0 p hp
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
        obtain ⟨pos, pre, es, vs, rd, hrd, hpos, hb, hwp, hh0, hM0, hW⟩ := hheap σ0 hσ0
        have hcall := List.all_eq_true.mp hok.calls _ (List.getElem_mem hi)
        rw [hcode] at hcall
        -- the call's pairing (a `call`, a `callIf` entered, or a `dispatch`), its callee the same for
        -- every honest valuation of the frame, entered at `t`, its mode signature there `G`
        obtain ⟨f, args, rets, st, t, o, pos', hsite, hfo, hat', as, hpairs, hkC, hpe, hout, ht30, G, hG, hr30,
            hentf, hfit⟩ : ∃ f args rets st t o pos', Cf.X.siteAt of args rets = some st ∧ Cf.X.fwdOff i st.r = some o ∧
            pairAt Cf.P Cf.fn.body K.code Cf.d o = some pos' ∧ ∃ as : List Atom,
            List.Forall₂ (Pairs Cf.X) (as.filter flowAtom)
              (((Cf.d.2.2.lookup (Cf.X.entry + i)).getD []).filter isaFlowHint) ∧
            (∀ {σ : Val} {pre es : List Ev} {vs : List V} {rd : Reader}, HonF img Cf s.fp σ →
              walk σ Cf.fn.body = .ret (pre ++ es) vs → walk σ pos = .ret es vs →
              ReadsAt Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) pre es →
              ∃ (evs : List Ev) (cs : List Atom) (es' : List Ev),
                es = evs ++ Ev.call f args rets :: (cs.map Ev.atom ++ es') ∧ walk σ pos' = .ret es' vs ∧
                (∀ a ∈ cs, stopL a = false) ∧ (∀ a ∈ as, Ev.atom a ∈ evs) ∧
                (∀ e ∈ evs, EvM Cf.sigOf rd σ e) ∧ ∀ x, WrittenC Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) (pre ++ evs) x →
                  WrittenC Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) pre x ∨
                  ∃ a ∈ as, flowAtom a = true ∧ Ev.atom a ∈ evs ∧ Writes σ a x) ∧
            s'.pc = t ∧ ¬ (Cf.frame.entry ≤ t ∧ t < Cf.frame.entry + Cf.frame.len) ∧ t < 2 ^ 30 ∧
            ∃ G, Cf.frame.sigs.get t = some G ∧ st.r < 2 ^ 30 ∧ getF Cf.X.ents t = some f ∧
              callOkC Cf G f st.args.length st.rets.length = true := by
          cases hpcod : Cf.X.pcAt od with
          | some t =>
            obtain ⟨f, args, rets, st, t', o, pos', hsite, hpt, hentF, hfo, hat', as, hpairs, hkA⟩ :=
              pair_callAny hok.pair hpos hci hz hfw hr01 hmainX hsf'
                (fun t f ht he ↦ jumpCallOk_next hcall ht (entOk_spec he)) (jumpCallOk_tgt hcall hpcod)
            rw [hpcod, Option.some.injEq] at hpt
            subst hpt
            obtain ⟨hout, ht30, -, G, st', hG, hst', hr30, hfit⟩ := jumpCallOk_spec hcall hpcod (entOk_spec hentF)
            rw [(siteAt_spec hsite).1, Option.some.injEq] at hst'
            subst hst'
            refine ⟨f, args, rets, st, t, o, pos', hsite, hfo, hat', as, hpairs, ?_, ?_, hout, ht30, G, hG, hr30,
              entOk_spec hentF, hfit⟩
            · intro σ pre es vs rd hσ hb' hwp' hrw
              rcases hkA with hkA | ⟨c, hloc, rfl, hkA⟩
              · exact hkA hwp' hrw
              obtain ⟨evs, cs, es', rfl, hwp2, hcs, hasin, hevM, hW'⟩ := hkA hwp' hrw
              have hcond := hσ.jc.cond _ _ hb' c (by simp)
              rw [hloc] at hcond
              have hσc : σ c ≠ 0 := fun h0 ↦ hv0 (by rw [rd_get hκ hm.fine soc (by rw [hm.fp]; exact hcond) hv, h0])
              refine ⟨evs ++ [Ev.inK c], cs, es', by simp [hσc], hwp2, hcs, fun a ha ↦ by simp [hasin a ha],
                evM_app hevM (evM_inK_cons evM_nil), fun x hx ↦ ?_⟩
              rcases hW' x (writtenC_noAtom (e := Ev.inK c) (pre := pre ++ evs) (fun a h ↦ by cases h)
                  (fun f a r h ↦ by cases h) (by simpa [List.append_assoc] using hx)) with h | ⟨a, ha, hfa, hma, hwa⟩
              · exact Or.inl h
              · exact Or.inr ⟨a, ha, hfa, by simp [hma], hwa⟩
            · have := rd_get hκ hm.fine sod (by rw [hm.fp]; exact hσ0.jc.pcw od t hpcod) h0
              exact gpow_inj (by omega) (by omega) (pow_of_ofK this)
          | none =>
            -- a dispatch: the callee its target cell names, by `HonF.tgt` the same for every honest valuation
            obtain ⟨x, fs, args, rets, st, o, pos', hmem, hsite, htg, hfo, hat', as, hpairs, hkD⟩ :=
              pair_dispatch hok.pair hpos hci hz hfw hr01 hmainX hsf' hpcod
            have hd0 : od ≠ 0 := (jumpCallOk_dsp hcall (siteAt_spec hsite).1 htg).1
            have hds := dspSite_of hpcod hsite htg hd0
            rw [tgtOk, Exec.listSeq_eq] at htgt
            obtain ⟨kk, hkk⟩ : ∃ kk, Cf.frame.tgt.get (0 + i) = some kk := by
              cases hk : Cf.frame.tgt.get (0 + i) with
              | none => rw [tgtGo_none htgt hci hk] at hds; cases hds
              | some kk => exact ⟨kk, rfl⟩
            obtain ⟨-, hdj⟩ : dspSite Cf.X od of = true ∧ dspJ Cf kk od of = true := by
              rcases tgtGo_at htgt hci hkk with h | ⟨h, -⟩
              · exact h
              · rw [hds] at h; cases h
            obtain ⟨pcs, -, -, -, -, hr30, -, hpcs, hfs⟩ := dsp_at (callsB_of' hok.heap) hdj hmem hsite
            -- the callee a path's dispatch calls: entered at the entry its target cell holds
            have hpick : ∀ {σ : Val} {pre es : List Ev} {vs : List V} {f : String} {evs es' : List Ev},
                HonF img Cf s.fp σ → walk σ Cf.fn.body = .ret (pre ++ es) vs →
                es = evs ++ Ev.call f args rets :: es' → f ∈ fs → ∃ t ∈ pcs, Cf.X.entOk t f = true ∧
                  Rd img s.fp od = some (ofK (g ^ t)) := by
              intro σ pre es vs f evs es' hσ hb' hes hf
              obtain ⟨t, ht, hte⟩ := hfs f hf
              refine ⟨t, ht, hte, ?_⟩
              rw [← htg]
              exact honF_dsp hσ (pre := pre ++ evs) (by rw [hb', hes, List.append_assoc]) hsite (by omega) hte
            obtain ⟨f0, hf0, evs0, cs0, es0, hes0, -⟩ := hkD hwp (hrwOf σ0 pre es vs rd hb hh0 (hσ0.res hxw) hM0)
            obtain ⟨t, ht, hte, hrdt⟩ := hpick hσ0 hb hes0 hf0
            have hpt := hpcs t ht
            simp only [dspPc] at hpt
            split at hpt
            swap
            · cases hpt
            rename_i f1 hf1
            have hf10 : f1 = f0 := by
              have := entOk_spec hte
              rw [hf1, Option.some.injEq] at this
              exact this
            subst hf10
            simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hpt
            obtain ⟨⟨hout, ht30⟩, hpt⟩ := hpt
            split at hpt
            swap
            · cases hpt
            rename_i G hG
            refine ⟨f1, args, rets, st, t, o, pos', hsite, hfo, hat', as, hpairs, ?_, ?_,
              fun ⟨h1, h2⟩ ↦ by simp [h1, h2] at hout, ht30, G, hG, hr30, hf1, hpt⟩
            · intro σ pre es vs rd hσ hb' hwp' hrw
              obtain ⟨f', hf', evs, cs, es', hes, hrest⟩ := hkD hwp' hrw
              obtain ⟨t', ht', hte', hrdt'⟩ := hpick hσ hb' hes hf'
              have htt : t' = t := by
                rw [hrdt, Option.some.injEq] at hrdt'
                have h30 : t' < 2 ^ 30 := by
                  have hp' := hpcs t' ht'
                  simp only [dspPc] at hp'
                  split at hp'
                  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hp'
                    exact hp'.1.2
                  · cases hp'
                exact gpow_inj (by omega) (by omega) (pow_of_ofK hrdt'.symm)
              subst htt
              have hff : f' = f1 := by
                have := entOk_spec hte'
                rw [hf1, Option.some.injEq] at this
                exact this.symm
              subst hff
              exact ⟨evs, cs, es', hes, hrest⟩
            · have := rd_get hκ hm.fine sod (by rw [hm.fp]; exact hrdt) h0
              exact gpow_inj (by omega) (by omega) (pow_of_ofK this)
        rw [hhd i] at hpairs
        obtain ⟨hst'', hna, hnr'⟩ := siteAt_spec hsite
        rw [hna, hnr'] at hfit
        obtain ⟨hG0, hG1⟩ : 0 ∈ G.entry ∧ 1 ∈ G.entry := by
          unfold callOkC at hfit
          split at hfit
          · simp only [Bool.and_eq_true, List.contains_iff_mem] at hfit
            exact ⟨hfit.1.2, hfit.2⟩
          · simp only [fitB, Bool.and_eq_true, List.contains_iff_mem] at hfit
            obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, h0⟩, h1⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hfit
            exact ⟨h0, h1⟩
        -- the walk's split at the call, the callee frame
        have hsplit : ∀ {σ : Val} {pre es : List Ev} {vs : List V} {rd : Reader}, HonF img Cf s.fp σ →
            pairAt Cf.P Cf.fn.body K.code Cf.d i = some pos → walk σ Cf.fn.body = .ret (pre ++ es) vs →
            walk σ pos = .ret es vs → (∀ e ∈ pre ++ es, e.Holds rd σ) → (∀ e ∈ pre, EvM Cf.sigOf rd σ e) →
            ∃ (evs : List Ev) (cs : List Atom) (es' : List Ev), es = evs ++ Ev.call f args rets :: (cs.map Ev.atom ++ es') ∧
              walk σ pos' = .ret es' vs ∧ (∀ a ∈ cs, stopL a = false) ∧ (∀ a ∈ as, Ev.atom a ∈ evs) ∧
              (∀ e ∈ evs, EvM Cf.sigOf rd σ e) ∧ (∀ x, WrittenC Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) (pre ++ evs) x →
                WrittenC Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) pre x ∨
                ∃ a ∈ as, flowAtom a = true ∧ Ev.atom a ∈ evs ∧ Writes σ a x) ∧
              ReqOk Cf.sigOf Cf.H rd σ (WrittenC Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) (pre ++ evs))
                (.call f args rets) ∧
              ∃ kfp, (g : Parameters.K) ^ s'.fp = g ^ kfp ∧
                (∀ b < args.length + rets.length, Rd img s'.fp (2 + b) = some (slotW ((args ++ rets).map σ) b)) ∧
                Rd img s'.fp 0 = some (ofK (g ^ st.r)) ∧ Rd img s'.fp 1 = some (ofK (g ^ s.fp)) := by
          intro σ pre es vs rd hσ hp hb hwp hh0 hM0
          obtain ⟨evs, cs, es', rfl, hwp', hcs, hasin, hevM, hW'⟩ := hkC hσ hb hwp (hrwOf σ pre _ vs rd hb hh0 (hσ.res hxw) hM0)
          have hreq := hrwOf σ pre _ vs rd hb hh0 (hσ.res hxw) hM0 evs (.call f args rets) (cs.map Ev.atom ++ es')
            rfl hevM
          obtain ⟨kfp, hq, hk0, hk1, hargs, hrets⟩ := hσ.kid _ _ hb ((calls (pre ++ evs)).length)
            ⟨f, args, rets, true⟩ of st (by rw [← List.append_assoc]; exact calls_mid) rfl hsite
          have hfpE : (g : Parameters.K) ^ s'.fp = g ^ kfp :=
            (pow_of_ofK (rd_get hκ hm.fine sof (by rw [hm.fp]; exact hq) h1)).symm.symm
          refine ⟨evs, cs, es', rfl, hwp', hcs, hasin, hevM, hW', hreq, kfp, hfpE, fun b hb' ↦ ?_,
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
        obtain ⟨evs, cs, es', heq, hwp', hcs, hasin, hevM, hW', hreq, kfp, hfpE, hwsE, hk0, hk1⟩ :=
          hsplit hσ0 hpos hb hwp hh0 hM0
        have hcallE : Ev.call f args rets ∈ pre ++ es := by rw [heq]; simp
        obtain ⟨hpwR, hpwPR⟩ := callsB_spec (callsB_of hok.heap hbody hb hcallE) (body_callS hbody hb hcallE)
        have htop : Cf.fn.body.all topOk = true := (Bool.and_eq_true_iff.mp hbody).2
        have hexp : ∀ j, idxPowC Cf args j = true →
            IdxEx (slotW (args.map σ0)) j := fun j h ↦ by
          simpa using idxPowC_rep (ws := []) hok.pows htop hb hh0 hσ0.par hxw h
        have hWs1 : ∀ x, WrittenC Cf.sigOf Cf.H rd σ0 (Cf.fn.params.map σ0) (pre ++ evs) x → WrK s1.mem x := by
          intro x hx
          rcases hW' x hx with h | ⟨a, ha, hfa, hma, hwa⟩
          · exact (hW _ h).mono hm.le
          · subst heq
            exact flow_wrk hκ e1 hs hm hpairs ha hfa (fun q hq ↦ hσ0.ptr _ _ hb a q
              (List.mem_append_right _ (List.mem_append_left _ hma)) hq) hwa
        cases hjo with
        | ret _ _ hr =>
          obtain ⟨c', hc'⟩ := hr
          rw [hci, Option.some.injEq, OffsetInstruction.jump.injEq] at hc'
          exact absurd ⟨hc'.2.1, hc'.2.2⟩ hr01
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
          have hCtt : Ct s'.pc = hcAt img Cf G f := ct_callee hCt hsigK (by rw [hpe]; exact hentf)
          cases hl : Cf.hcs.lookup f
          case some p =>
            -- a callee whose contract is its heap signature's: no translation
            have hp : p = (args.length, rets.length) := by
              simp only [callOkC, hl, Bool.and_eq_true, decide_eq_true_eq] at hfit
              exact hfit.1.1
            subst hp
            have hCs : Ct s'.pc = some (heapCtr img (Cf.sigOf f) G args.length rets.length) := by
              rw [hCtt]; simp [hcAt, hl]
            refine k s1 s' (he1 s1 e1) hm hmo e' hf' hle' (.call fun hTE ↦ ⟨G, o, hsigK, by omega, ?_, ?_,
              hentry.w, ?_, ?_⟩)
            · obtain ⟨u, hu⟩ := Mem.get_of_written (hentry.w 0 hG0)
              rw [hu, rd_get hκ hf' (by norm_num) hk0 hu, ht'r]
            · obtain ⟨u, hu⟩ := Mem.get_of_written (hentry.w 1 hG1)
              rw [hu, rd_get hκ hf' (by norm_num) hk1 hu, hm.fp]
            · -- its preconditions at its arguments' words, written before the call
              unfold Mode.PreAt
              rw [hCs]
              refine ⟨hentry.w, fun y hy ↦ ?_⟩
              obtain ⟨hgl, ⟨hrpre, hrpreR⟩, hrptr⟩ := callReq_pre (ders_of hok.heap hbody hb hcallE) hreq
              have hga : gargsW Cf.H σ0 f args = [] := by
                rw [← List.length_eq_zero_iff]
                simp only [gargsW, List.length_map, hgl]
                exact callChk_ghosts (callsB_chk (callsB_of' hok.heap) (body_callS hbody hb hcallE))
              rw [hga, List.append_nil] at hrpre hrpreR hrptr
              have hwsA : wsAt img s'.fp args.length = args.map σ0 := by
                rw [wsAt_take hwsE (by omega) (by simp), List.map_append, List.take_left' (by simp)]
              rw [hwsA] at hy
              have hW1 : ∀ x, WrittenC Cf.sigOf Cf.H rd σ0 (Cf.fn.params.map σ0) (pre ++ evs) x → WrK s'.mem x :=
                fun x hx ↦ (hWs1 x hx).mono hle'
              rcases hy with (⟨c, hc, rfl⟩ | ⟨r, hr, hx⟩) | hp
              · exact hW1 _ (hrpre c hc)
              · exact hW1 _ (hrpreR r hr _ hx)
              · rw [← hrd] at hp; exact hW1 _ (hrptr _ hp)
            · -- resumed once the callee guarantees its contract
              intro m hm0 hwf hu hfpE hfpC hP hT
              unfold Mode.PostAt at hP
              rw [hCs] at hP
              obtain ⟨hRet, hPost, hRM, hRV, hRE⟩ := hP
              refine ⟨by rw [Mode.stOf, hm.fp]; exact hxw, fun m' hm' ham' ↦ ?_⟩
              have hle0 : s.mem ≤ m' := Mem.le_trans hm.le (Mem.le_trans hle' (Mem.le_trans hm0 hm'))
              refine ⟨?_, fun o' ho' ↦ ?_, fun σ hσ ↦ ?_⟩
              · have := hcont { Mode.stOf m' s1.fp with pc := Cf.frame.entry + o }
                  ⟨ham', Prover.Exec.Dlog.ok_empty, Prover.Exec.Dlog.small_empty, hfpC⟩ rfl rfl
                  (Mem.le_trans hle' (Mem.le_trans hm0 hm')) (fun o' ho' ↦ written_mono hm' (hRet o' ho'))
                exact atF_mono (s := { Mode.stOf m' s1.fp with pc := Cf.frame.entry + o }) (Mem.le_refl _) rfl this
              · show m'.written (s1.fp + o') = true
                rw [hm.fp]; exact written_mono hle0 (hentw o' ho')
              · change HonF img Cf s1.fp σ at hσ
                rw [hm.fp] at hσ
                obtain ⟨pos2, pre2, es2, vs2, rd2, hrd2, hpos2, hb2, hwp2, hh2, hM2, hW2⟩ := hheap σ hσ
                rw [hpos, Option.some.injEq] at hpos2
                subst hpos2
                obtain ⟨evs2, cs2, es2', rfl, hwp2', hcs2, hasin2, hevM2, hW2', -, kfp2, hfpE2, hwsE2, -, -⟩ :=
                  hsplit hσ hpos hb2 hwp2 hh2 hM2
                -- the callee's returned words, its contract's
                have hEv : EvM Cf.sigOf rd2 σ (.call f args rets) := by
                  have hwF : wsAt img s'.fp (args.length + rets.length) = (args ++ rets).map σ :=
                    wsAt_eq (by simp) hwsE2
                  have hwP : wsAt img s'.fp args.length = args.map σ := by
                    rw [wsAt_take hwsE2 (by omega) (by simp), List.map_append, List.take_left' (by simp)]
                  rw [hwF, hwP, List.map_append, List.drop_left' (by simp)] at hRM
                  rw [hwF] at hRV hRE
                  subst hrd2
                  exact ⟨hRM, by simpa using hRV, by simpa using hRE⟩
                refine ⟨pos', pre2 ++ evs2 ++ Ev.call f args rets :: cs2.map Ev.atom, es2', vs2, rd2, hrd2, hat',
                  by simpa using hb2, hwp2', by simpa using hh2,
                  evM_app (evM_app hM2 hevM2) fun e he ↦ ?_, fun y hy ↦ ?_⟩
                · rcases List.mem_cons.mp he with rfl | he
                  · exact hEv
                  · exact evM_atoms _ e he
                rcases writtenC_append hy with h | ⟨e, he, hwe⟩
                · rcases hW2' y h with h | ⟨a, ha, hfa, hma, hwa⟩
                  · exact (hW2 y h).mono hle0
                  · exact ((flow_wrk hκ e1 hs hm hpairs ha hfa (fun q hq ↦ hσ.ptr _ _ hb2 a q
                      (List.mem_append_right _ (List.mem_append_left _ hma)) hq) hwa).mono
                      (Mem.le_trans hle' (Mem.le_trans hm0 hm')))
                rcases List.mem_cons.mp he with rfl | he
                · -- the callee's guarantees, its contract's
                  subst hrd2
                  refine (hPost y ?_).mono hm'
                  rw [wsAt_eq (by simp) hwsE2]
                  exact hwe
                · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
                  exact absurd hwe (no_writes_of_stopL (hcs2 a ha))
          -- a callee of a mode contract, through `fitB`
          have hCn : Ct s'.pc = none := by rw [hCtt]; simp [hcAt, hl]
          simp only [callOkC, hl, fitB, Bool.and_eq_true, List.isEmpty_iff, List.contains_iff_mem,
            List.all_eq_true] at hfit
          obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hGself, hGpreP⟩, -⟩, -⟩, hhpostP⟩, hhpostPR⟩, -⟩, hGpre⟩, hGpreR⟩, hhpost⟩,
            hhpostR⟩, hhgh⟩ := hfit
          refine k s1 s' (he1 s1 e1) hm hmo e' hf' hle' (.call fun hTE ↦ ⟨G, o, hsigK, by omega, ?_, ?_,
            hentry.w, ?_, ?_⟩)
          · obtain ⟨u, hu⟩ := Mem.get_of_written (hentry.w 0 hG0)
            rw [hu, rd_get hκ hf' (by norm_num) hk0 hu, ht'r]
          · obtain ⟨u, hu⟩ := Mem.get_of_written (hentry.w 1 hG1)
            rw [hu, rd_get hκ hf' (by norm_num) hk1 hu, hm.fp]
          · -- the callee's entry facts
            rw [Mode.preAt_none hCn]
            refine holds_entryAbs ?_ fun o ho ↦ ?_
            swap
            · -- its self cell (a loop's)
              have ho28 : o < 2 ^ 28 := by rw [ho] at hGself; simpa using hGself
              obtain ⟨hwo, hro⟩ := hentry.self o ho
              obtain ⟨u, hu⟩ := Mem.get_of_written hwo
              exact ⟨hwo, by rw [hu, rd_get hκ hf' ho28 hro hu]⟩
            have hSG : ∀ {m : Mode.Mono}, monoS G args.length true m = true →
                SlotGet s' (args.map σ0) m.bs := fun hm' ↦
              slotGet_of hκ hf'.agree hf'.fp (fun b hb' ↦ by
                rw [hwsE b (by omega), List.map_append, slotW_lt (by simpa using hb')]) hentry.w hm'
            have hW1 : ∀ x, WrittenC Cf.sigOf Cf.H rd σ0 (Cf.fn.params.map σ0) (pre ++ evs) x → WrK s'.mem x :=
              fun x hx ↦ (hWs1 x hx).mono hle'
            obtain ⟨hgl, ⟨hrpre, hrpreR⟩, hrptr⟩ := callReq_pre (ders_of hok.heap hbody hb hcallE) hreq
            have hga : gargsW Cf.H σ0 f args = [] := by
              rw [← List.length_eq_zero_iff]
              simp only [gargsW, List.length_map, hgl]
              simpa using hhgh
            rw [hga, List.append_nil] at hrpre hrpreR hrptr
            refine ⟨fun o ho ↦ hentry.w o (foldlT_nil_get ho), fun o x hx ↦ (by rw [trieNil_get rfl] at hx; cases hx),
              fun o hx ↦ (by rw [trieNil_get rfl] at hx; cases hx), fun p hp ↦ (by cases hp), fun m hm' ↦ ?_,
              fun r hr ↦ ?_, fun p hp ↦ ?_, fun p hp ↦ (by cases hp), fun c a b hx ↦ (by rw [trieNil_get rfl] at hx; cases hx),
              fun q hq ↦ ?_, fun q hq ↦ (by cases hq)⟩
            · rcases Bool.or_eq_true_iff.mp (hGpre m hm') with hc | hc
              · obtain ⟨hmS, hc⟩ := Bool.and_eq_true_iff.mp hc
                split at hc
                · rename_i c hmc
                  obtain ⟨c', hc', hbeq⟩ := List.any_eq_true.mp hc
                  rw [CCell.beq_eq hbeq] at hc'
                  exact slot_hw hmc (hSG hmS) (hW1 _ (hrpre c hc'))
                · cases hc
              · unfold hpIn at hc
                split at hc
                · rename_i q d hqd
                  simp only [Bool.and_eq_true] at hc
                  obtain ⟨⟨hsl, hcl⟩, hps⟩ := hc
                  obtain ⟨p', hp', hpp⟩ := List.any_eq_true.mp hps
                  simp only [Bool.and_eq_true, List.contains_iff_mem] at hpp
                  obtain ⟨hpb, hko⟩ := hpp
                  have h2 : 2 ≤ q := by
                    simp only [hpSlot, Bool.and_eq_true, decide_eq_true_eq] at hsl; exact hsl.1.1.1
                  have hu' : s'.mem.used ≤ 2 ^ κ :=
                    hU s _ s1 s' hYs (by rw [hpc]; exact hK.ops i hi) (he1 s1 e1) hm e'
                  obtain ⟨c', hc', hbeq⟩ := List.any_eq_true.mp hcl
                  rw [CCell.beq_eq hbeq] at hc'
                  rw [hpOf_spec hqd]
                  refine hp_hw (s := s') hκ hf'.agree hu' h2 (hSG (monoS_fr hsl)) (hW1 _ (hrpre _ hc')) fun w hw ↦ ?_
                  refine hW1 _ (hrptr _ (Or.inl ⟨p', hp', w, ?_, m.k, hko, rfl⟩))
                  rw [CCell.beq_eq hpb, hrd]
                  exact hw
                · cases hc
            · rcases List.mem_cons.mp hr with rfl | hr
              · exact hjtR s' (Mem.le_trans hm.le hle')
              rcases Bool.or_eq_true_iff.mp (hGpreR r hr) with h0 | h0
              · obtain ⟨hmS, h⟩ := Bool.and_eq_true_iff.mp h0
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
              · obtain ⟨hmS, h⟩ := Bool.and_eq_true_iff.mp h0
                obtain ⟨q, hq, hrq⟩ := List.any_eq_true.mp h
                unfold rngXIs at hrq
                split at hrq
                · rename_i q' hq'
                  have hqq : q' = q := of_decide_eq_true hrq
                  subst hqq
                  have hpw := Bool.and_eq_true_iff.mp (hpwR q' hq)
                  exact slot_rwX hq' (hSG hmS) (hexp _ hpw.1) (hexp _ hpw.2) fun x hx ↦ hW1 x (hrpreR q' hq x hx)
                · cases hrq
            · exact Mode.LTF.mono (s := Mode.stOf s'.mem s'.fp) (s' := s') (Mem.le_refl _) rfl
                (hTE G hsigK hentry.w p hp)
            · obtain ⟨⟨hmS, hpr⟩, hrr⟩ := hGpreP q hq
              obtain ⟨p', hp', hpp⟩ := List.any_eq_true.mp hpr
              simp only [prunIs, rngXIs, Bool.and_eq_true, decide_eq_true_eq] at hpp
              obtain ⟨hrq, hos⟩ := hpp
              split at hrq
              · rename_i q' hq'
                have hpq : q' = p'.1 := of_decide_eq_true hrq
                obtain ⟨q2, hq2, hrr'⟩ := List.any_eq_true.mp hrr
                unfold rngXIs at hrr'
                rw [hq'] at hrr'
                have hq2e : q' = q2 := of_decide_eq_true hrr'
                subst hq2e
                have hpw := Bool.and_eq_true_iff.mp (hpwPR p' hp')
                rw [← hpq] at hpw
                have hu' : s'.mem.used ≤ 2 ^ κ :=
                  hU s _ s1 s' hYs (by rw [hpc]; exact hK.ops i hi) (he1 s1 e1) hm e'
                refine slot_pwX (s := s') hκ hf'.agree hu' hq' (hSG hmS) (hexp _ hpw.1) (hexp _ hpw.2)
                  (fun x hx ↦ hW1 x (hrpreR q' hq2 x hx)) fun x hx ↦ ?_
                obtain ⟨a, ha, hpa⟩ := hx
                refine hW1 x (hrptr x (Or.inr ⟨p', hp', a, ?_⟩))
                rw [← hpq, ← hos, hrd]
                exact ⟨ha, hpa⟩
              · cases hrq
          · -- resumed once the callee guarantees its signature
            intro m hm0 hwf hu hfpE hfpC hP hT
            rw [Mode.postAt_none hCn] at hP
            obtain ⟨hR, hL, hLP⟩ := hP
            refine ⟨by rw [Mode.stOf, hm.fp]; exact hxw, fun m' hm' ham' ↦ ?_⟩
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
              obtain ⟨pos2, pre2, es2, vs2, rd2, hrd2, hpos2, hb2, hwp2, hh2, hM2, hW2⟩ := hheap σ hσ
              rw [hpos, Option.some.injEq] at hpos2
              subst hpos2
              obtain ⟨evs2, cs2, es2', rfl, hwp2', hcs2, hasin2, hevM2, hW2', -, kfp2, hfpE2, hwsE2, -, -⟩ :=
                hsplit hσ hpos hb2 hwp2 hh2 hM2
              have hEv : EvM Cf.sigOf rd2 σ (.call f args rets) :=
                callChk_evM (rets := rets) (callsB_chk (callsB_of' hok.heap)
                  (body_callS (r := rets) hbody hb2 (by simp))) hl rd2 σ
              refine ⟨pos', pre2 ++ evs2 ++ Ev.call f args rets :: cs2.map Ev.atom, es2', vs2, rd2, hrd2, hat',
                by simpa using hb2, hwp2', by simpa using hh2,
                evM_app (evM_app hM2 hevM2) fun e he ↦ ?_, fun y hy ↦ ?_⟩
              · rcases List.mem_cons.mp he with rfl | he
                · exact hEv
                · exact evM_atoms _ e he
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
                have hRL : ∀ r ∈ G.postR ++ G.postL, RW (Mode.stOf m s'.fp) r := fun r hr ↦
                  (List.mem_append.mp hr).elim (hR.2.2.1 r) (hL r)
                have hPL : ∀ q ∈ G.postP ++ G.postLP, Mode.PW (Mode.stOf m s'.fp) q.1 q.2 := fun q hq ↦
                  (List.mem_append.mp hq).elim (hR.2.2.2.1 q) (hLP q)
                rcases hwe with (⟨c, hc, rfl⟩ | ⟨r, hr, hx⟩) | (⟨p, hp, hps⟩ | ⟨p, hp, a, ha', hpa⟩)
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
                  rcases Bool.or_eq_true_iff.mp hrq with hrq | hrq
                  · rw [Bool.and_eq_true] at hrq
                    obtain ⟨hmS, hrq⟩ := hrq
                    unfold rngIs at hrq
                    split at hrq
                    · rename_i q hq
                      obtain rfl := of_decide_eq_true hrq
                      exact rw_slot hq (hSE hmS) (Mode.RW.mono (s := Mode.stOf m s'.fp) (s' := Mode.stOf m' s'.fp)
                        hm' rfl (hRL r' hr')) y hx
                    · cases hrq
                  · rw [Bool.and_eq_true] at hrq
                    obtain ⟨hmS, hrq⟩ := hrq
                    unfold rngXIs at hrq
                    split at hrq
                    · rename_i q hq
                      obtain rfl := of_decide_eq_true hrq
                      exact rw_slotX hq (hSE hmS) (Mode.RW.mono (s := Mode.stOf m s'.fp) (s' := Mode.stOf m' s'.fp)
                        hm' rfl (hRL r' hr')) y hx
                    · cases hrq
                · obtain ⟨w', hw', o, ho, rfl⟩ := hps
                  have hall := hhpostP p hp
                  unfold hpAll at hall
                  obtain ⟨m0, hm0', hmm⟩ := List.any_eq_true.mp (List.all_eq_true.mp hall o ho)
                  split at hmm
                  · rename_i q d hqd
                    simp only [Bool.and_eq_true, Nat.beq_eq] at hmm
                    obtain ⟨⟨hsl, hpb⟩, rfl⟩ := hmm
                    rw [CCell.beq_eq hpb, hrd2] at hw'
                    have h2 : 2 ≤ q := by
                      simp only [hpSlot, Bool.and_eq_true, decide_eq_true_eq] at hsl; exact hsl.1.1.1
                    exact hw_hp (s := Mode.stOf m' s'.fp) hκ ham' h2 (hSE (monoS_fr hsl))
                      (Mode.HW.mono (s := Mode.stOf m s'.fp) (s' := Mode.stOf m' s'.fp) hm' rfl
                        (hpOf_spec hqd ▸ hR.2.1 m0 hm0')) hw'
                  · cases hmm
                · obtain ⟨r', hr', hrp⟩ := List.any_eq_true.mp (hhpostPR p hp)
                  simp only [prunIs, rngXIs, Bool.and_eq_true, decide_eq_true_eq] at hrp
                  obtain ⟨hmS, hrq, hos⟩ := hrp
                  split at hrq
                  · rename_i q hq
                    obtain rfl := of_decide_eq_true hrq
                    rw [hrd2, ← hos] at hpa
                    exact pw_slotX (s := Mode.stOf m' s'.fp) hκ ham' hq (hSE hmS)
                      (Mode.PW.mono (s := Mode.stOf m s'.fp) (s' := Mode.stOf m' s'.fp) hm' rfl (hPL r' hr'))
                      y ⟨a, ha', hpa⟩
                  · cases hrq
              · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
                exact absurd hwe (no_writes_of_stopL (hcs2 a ha))

end

end LeanVM.Guest.CoreMode
