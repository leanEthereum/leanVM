/-
  LeanVM.Guest.CoreMode.CoreSound

  The core route meets the frame interface: `frameSpec_core`.
-/

module

public import LeanVM.Guest.CoreMode.Core

/-!
# The core route's frame interface, proved

`frameSpec_core`: a function passing the kernel's checks (`CoreOk`) meets `FrameSpec` for `CoreAt`
on a reference image, at states on its run where its frames have honest valuations (`CoreHon`).

* Entry: the frame walk's entry (`atF_entry`), the pairing at the body (`pairAt_zero`), the heap
  preconditions the signature's, written at entry (`hw_wrk`).
* A step: `frame_step`, its oracle's heap cell written by the pairing (`pair_read`, `heapOk_sound`), a
  fall-through at the pairing's next position (`pair_fall`), a store's cell written by its `DEREF`
  (`StoreW`); the return, the last instruction, with the signature's guarantees (`postOk_sound`,
  `pair_ret`: the events past the position write nothing new).
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Bridge (AlignCtx Zip ZOk fwdJ flowAtom isaFlowHint stmtsOf stmtsSub zok_stmts Pairs)
open LeanVM.Prover.Exec (Hint St Ctx Fine Moves StepOk HintOk refMem maxCells runOp Mem gpow_inj
  Mem.get_of_written OpModed OnRef)
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
      i + 1 = code.length ∧ od = 0 ∧ of = 1 ∧ X.zeroAt oc = false ∧ fwdJ X (n + i) oc od of = false
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
        exact ⟨rfl, h.1.1.1, h.1.1.2, h.1.2, by simpa using h.2⟩
    | cons ins' rest' =>
      rw [retLast, Bool.and_eq_true] at h
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
        subst hi
        simp [isJumpI] at h
      | succ i =>
        simp only [List.getElem?_cons_succ] at hi
        obtain ⟨h1, h2, h3, h4, h5⟩ := retLast_jump h.2 hi
        refine ⟨by simp only [List.length_cons] at h1 ⊢; omega, h2, h3, h4, ?_⟩
        rw [show n + (i + 1) = n + 1 + i by omega]
        exact h5

theorem retLast_last {X : AlignCtx} : ∀ {n : ℕ} {code : List OffsetInstruction},
    retLast X n code = true → ∃ oc od of, code[code.length - 1]? = some (.jump oc od of)
  | _, [], h => by simp [retLast] at h
  | n, ins :: rest, h => by
    cases rest with
    | nil =>
      cases ins with
      | jump oc od of => exact ⟨oc, od, of, rfl⟩
      | _ => simp [retLast, retIns] at h
    | cons ins' rest' =>
      rw [retLast, Bool.and_eq_true] at h
      obtain ⟨oc, od, of, h'⟩ := retLast_last h.2
      exact ⟨oc, od, of, by simpa using h'⟩

theorem straight_stmts : ∀ {body : List Stmt}, straight body = true → ∀ s ∈ stmtsOf body,
    (∃ a, s = .atom a) ∨ ∃ vs, s = .ret vs
  | [], _, s, hs => by simp [stmtsOf] at hs
  | b :: body, h, s, hs => by
    simp only [straight, List.all_cons, Bool.and_eq_true] at h
    simp only [stmtsOf, List.mem_cons, List.mem_append] at hs
    rcases hs with rfl | hs | hs
    · cases s with
      | atom a => exact Or.inl ⟨a, rfl⟩
      | ret vs => exact Or.inr ⟨vs, rfl⟩
      | _ => simp at h
    · cases b with
      | atom => simp [stmtsSub] at hs
      | ret => simp [stmtsSub] at hs
      | _ => simp at h
    · exact straight_stmts (by simpa [straight] using h.2) s hs

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

/-! ## The return -/

/-- **At the return**, the events past the pairing's position write nothing new but what its flow
hints' atoms write: the head statement the pairing jumps by, past atoms that are no stores, is the
body's `ret`. -/
theorem pair_ret {X : AlignCtx} {H : HCert} {O S : Exec.Trie Unit} {body : List Stmt}
    {code : List OffsetInstruction} {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)}
    (hok : pairOk X H O S body code d = true) {i : ℕ} {pos : List Stmt}
    (hat : pairAt (PairCtx.ofH X H O S) body code d i = some pos) {oc od of : ℕ}
    (hci : code[i]? = some (.jump oc od of)) (hz : X.zeroAt oc = false) (hf : fwdJ X i oc od of = false)
    (hst : straight body = true)
    {σ : Val} {pre es : List Ev} {vs : List V} (hp : walk σ pos = .ret es vs) (hrw : ReadsWritten H σ (pre ++ es)) :
    ∃ as : List Atom, List.Forall₂ (Pairs X) (as.filter flowAtom) (((d.2.2.lookup (X.entry + i)).getD []).filter isaFlowHint) ∧
      ∀ x, Written H σ (pre ++ es) x → Written H σ pre x ∨
        ∃ a ∈ as, flowAtom a = true ∧ Ev.atom a ∈ es ∧ Writes σ a x := by
  obtain ⟨ins, z, as, hins, -, hpos, hq, hpairs, hcase⟩ := pairAt_step hok hat
  rw [hci] at hins
  cases hins
  rcases hcase with ⟨hnj, -⟩ | ⟨oc', od', of', zs, heq, -, -, -, hzs, ⟨bs, hzpos, hbs⟩, tabs, r, hr, -⟩
  · exact absurd rfl (hnj oc od of)
  simp only [OffsetInstruction.jump.injEq] at heq
  obtain ⟨rfl, rfl, rfl⟩ := heq
  -- the head statement is the body's `ret`
  have hhead : ∃ vs' ss, zs.cur = .ret vs' :: ss := by
    unfold jumpStepH at hr
    simp only [PairCtx.ofH, hz, hf, Bool.cond_false] at hr
    rcases hcur : zs.cur with _ | ⟨s, ss⟩
    · simp [headStepH, hcur] at hr
    · have hs : s ∈ stmtsOf body := zok_stmts hzs (by rw [Bridge.Zip.pos_head hcur]; exact List.mem_cons_self)
      rcases straight_stmts hst s hs with ⟨a, rfl⟩ | ⟨vs', rfl⟩
      · simp [headStepH, hcur] at hr
      · exact ⟨vs', ss, rfl⟩
  obtain ⟨vs', ss, hcur⟩ := hhead
  refine ⟨as, hpairs, ?_⟩
  rw [hpos, hzpos, ← List.append_assoc, ← List.map_append] at hp
  obtain ⟨es', hes', rfl⟩ := walk_atoms_ret hp
  rw [Bridge.Zip.pos_head hcur, Bridge.walk_ret_cons] at hes'
  simp only [Out.ret.injEq] at hes'
  obtain ⟨rfl, -⟩ := hes'
  obtain ⟨-, -, -, hW⟩ := atoms_written (fs := as.filter flowAtom) (ss := zs.pos) (pre := pre)
    (es := (as ++ bs).map Ev.atom ++ []) (vs := vs) hp hrw (fun a ha hn ↦ by
        rcases List.mem_append.mp ha with ha | ha
        · cases hfa : flowAtom a
          · exact hq a ha hfa
          · exact absurd (List.mem_filter.mpr ⟨ha, hfa⟩) hn
        · exact hbs a ha)
  intro x hx
  rcases hW x (by simpa using hx) with h | ⟨a, ha, hwa⟩
  · exact Or.inl h
  · rw [List.mem_filter] at ha
    exact Or.inr ⟨a, ha.1, ha.2, by simp [ha.1], hwa⟩


/-! ## The signature's products, at an honest frame -/

/-- The signature's bases: frame cells holding the parameters' values. -/
def BaseCells (s : St) (σ : Val) (bs : List (Mode.Base × ℕ)) : Prop :=
  ∀ b ∈ bs, ∃ o, b.1 = .fr o ∧ s.mem.get (s.fp + o) = some (σ (V.n (o - 2)))

theorem bsVal_eq {s : St} {σ : Val} : ∀ (bs : List (Mode.Base × ℕ)) (cb : List (ℕ × ℕ)),
    bs.mapM baseOfMono = some cb → BaseCells s σ bs → ∀ w, (BsVal s bs w ↔ w = prodB σ cb)
  | [], cb, h, _, w => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    simp [BsVal, prodB]
  | (b, e) :: bs, cb, h, hc, w => by
    obtain ⟨o, hb, hget⟩ := hc (b, e) List.mem_cons_self
    simp only at hb
    subst hb
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨x, hx, xs, hxs, rfl⟩ := h
    simp only [baseOfMono] at hx
    split_ifs at hx
    cases hx
    have ih := bsVal_eq bs xs hxs (fun b hb ↦ hc b (List.mem_cons_of_mem _ hb))
    constructor
    · rintro ⟨u, w', hu, hw', rfl⟩
      have hu' : u = σ (V.n (o - 2)) := Option.some.inj (hu.symm.trans hget)
      rw [hu', (ih w').mp hw']
      rfl
    · rintro rfl
      exact ⟨_, _, hget, (ih _).mpr rfl, rfl⟩

theorem monoC_spec {m : Mode.Mono} {c : CCell} (h : monoC m = some c) :
    m.fp = 0 ∧ ∃ cb, m.bs.mapM baseOfMono = some cb ∧ c = ⟨cb, m.k⟩ := by
  unfold monoC at h
  split_ifs at h with h0
  obtain ⟨cb, hcb, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨h0, cb, hcb, rfl⟩

theorem monoVal_iff {s : St} {σ : Val} {m : Mode.Mono} {c : CCell} (hm : monoC m = some c)
    (hc : BaseCells s σ m.bs) (v : E) : MonoVal s m v ↔ v = c.val σ := by
  obtain ⟨h0, cb, hcb, rfl⟩ := monoC_spec hm
  have hb := bsVal_eq m.bs cb hcb hc
  simp only [MonoVal, h0, pow_zero, one_mul, CCell.val, addressOfIndex]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [(hb w).mp hw, mul_comm]
  · rintro rfl
    exact ⟨_, (hb _).mpr rfl, mul_comm _ _⟩

theorem hw_wrk {s : St} {σ : Val} {m : Mode.Mono} {c : CCell} (hm : monoC m = some c)
    (hc : BaseCells s σ m.bs) (h : HW s m) : WrK s.mem (c.addr σ) := by
  obtain ⟨v, x, hv, hx, hw⟩ := h
  rw [(monoVal_iff hm hc v).mp hv] at hx
  exact ⟨x, hx.1, hx.2, hw⟩

theorem wrk_hw {s : St} {σ : Val} {m : Mode.Mono} {c : CCell} (hm : monoC m = some c)
    (hc : BaseCells s σ m.bs) (h : WrK s.mem (c.addr σ)) : HW s m := by
  obtain ⟨x, hx, hlt, hw⟩ := h
  exact ⟨c.val σ, x, (monoVal_iff hm hc _).mpr rfl, ⟨hx, hlt⟩, hw⟩

theorem wrk_rw {s : St} {σ : Val} {r : Mode.Rng} {c : CCell} {l : List CCell} (hm : monoC r.q = some c)
    (hc : BaseCells s σ r.q.bs) (hl : runPts c r = some l) (h : ∀ p ∈ l, WrK s.mem (p.addr σ)) : RW s r := by
  unfold runPts at hl
  split at hl
  · rename_i a b hlo hhi
    cases hl
    refine ⟨c.val σ, a, b, (monoVal_iff hm hc _).mpr rfl, by rw [hlo]; rfl, by rw [hhi]; rfl, fun j hj1 hj2 ↦ ?_⟩
    obtain ⟨x, hx, hlt, hw⟩ := h _ (List.mem_map.mpr ⟨j - a, List.mem_range.mpr (by omega), rfl⟩)
    refine ⟨x, ⟨?_, hlt⟩, hw⟩
    rw [← hx]
    simp only [CCell.addr, CCell.val, addressOfIndex, pow_add, ofK_mul', show a + (j - a) = j by omega]
    ring_nf
  · cases hl

/-- **The signature's bases at an honest frame**: entry cells, written, holding the parameters. -/
theorem baseCells_of {img : MemoryImage κ} (hκ : κ ≤ 28) {Cf : CFun} {G : Mode.Sig} {m : Mode.Mono}
    (hm : monoOk G Cf.fn.params.length m = true) {s : St} (hs : Fine (refMem img) s)
    (hw : ∀ o ∈ G.entry, s.mem.written (s.fp + o) = true) {σ : Val} (hσ : HonF img Cf s.fp σ) :
    BaseCells s σ m.bs := by
  intro b hb
  have h := List.all_eq_true.mp hm b hb
  rcases hb1 : b.1 with o | ⟨q, d⟩
  · rw [hb1] at h
    simp only [Bool.and_eq_true, List.contains_iff_mem, decide_eq_true_eq] at h
    obtain ⟨⟨⟨ho, h2⟩, hnp⟩, h28⟩ := h
    refine ⟨o, rfl, ?_⟩
    obtain ⟨u, hu⟩ := Mem.get_of_written (hw o ho)
    have hr : Rd img s.fp o = some (σ (V.n (o - 2))) := by
      have := hσ.par (o - 2) hnp
      rwa [show 2 + (o - 2) = o by omega] at this
    rw [hu, rd_get hκ hs h28 hr hu]
  · rw [hb1] at h
    cases h


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

/-- **The core route meets the frame interface**: a function passing the kernel's checks, on the
executor's tables for the guest's advice, its code the executor's, at states `Y` on a reference run
where its frames have honest valuations. -/
theorem frameSpec_core {K : Mode.Cert} {Cf : CFun} (hok : CoreOk K Cf) {adv : Prover.Exec.Advice} {C : Ctx}
    (hC : Prover.Exec.Ctx.of guestProgram adv = .ok C) (ha : adv.hints = Data.adviceHints) (hK : CodeOk C K)
    {img : MemoryImage κ} {Y : St → Prop} (hκ : κ ≤ 28) (hY : ∀ s, Y s → ∃ n, OnRef guestProgram img n s)
    (hH : CoreHon img Y K Cf) : FrameSpec C (refMem img) Y K (CoreAt img Cf K.code) := by
  have hsh := hok.shape
  simp only [shapeOk, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, List.all_eq_true] at hsh
  obtain ⟨⟨⟨⟨⟨⟨⟨hst, hret⟩, hfp1⟩, htgt0⟩, hnzr0⟩, hent⟩, hend⟩, hincr⟩ := hsh
  obtain ⟨henv, harm, hacc⟩ := frameAcc_of hincr hok.frame
  have hsig := hok.sig
  simp only [sigOk, Bool.and_eq_true, Option.isNone_iff_eq_none, List.isEmpty_iff, List.all_eq_true] at hsig
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hself, hterm⟩, hpostL⟩, hpostP⟩, hpostLP⟩, hretV⟩, hpostT⟩, hpostC⟩, hpre⟩, hpost⟩,
    hpostR⟩ := hsig
  have hent' : ∀ x ∈ K.F.sig.entry, x + 1 < 2 ^ Exec.envDepth := hok.fsig ▸ hent
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
    refine ⟨atF_entry henv ⟨fun o ho ↦ hw o (hok.fsig ▸ ho), fun o hso ↦ by rw [hok.fsig, hself] at hso; cases hso⟩,
      fun o ho ↦ hw o (hok.fsig ▸ ho), fun σ hσ ↦ ?_⟩
    obtain ⟨es, vs, rd, hwk, -⟩ := hσ.path
    refine ⟨Cf.fn.body, [], es, vs, pairAt_zero hok.pair, by simpa using hwk, hwk, fun y hy ↦ ?_⟩
    rcases hy with ⟨c, hc, rfl⟩ | ⟨a, ha', -⟩
    · obtain ⟨m, hm, hmc⟩ := List.any_eq_true.mp (hpre c hc)
      rw [Bool.and_eq_true] at hmc
      obtain ⟨hmk, hmc⟩ := hmc
      split at hmc
      · rename_i c' hc'
        rw [← CCell.beq_eq hmc]
        exact hw_wrk hc' (baseCells_of hκ hmk hs hw hσ) (hH0.h m hm)
      · cases hmc
    · cases ha'
  · -- a step
    intro s i hi hpc hat hs hYs hsz _ _ _ _ _ _ _ hh _ href Inv k
    obtain ⟨hAtF, hentw, hheap⟩ := hat
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
    have hrwOf : ∀ σ, HonF img Cf s.fp σ → ∀ pre es vs, walk σ Cf.fn.body = .ret (pre ++ es) vs →
        ReadsWritten Cf.H σ (pre ++ es) ∧ ∃ rd, ∀ e ∈ pre ++ es, e.Holds rd σ := by
      intro σ hσ pre es vs hb
      obtain ⟨es0, vs0, rd, hw0, hh0⟩ := hσ.path
      rw [hb, Memory.Out.ret.injEq] at hw0
      obtain ⟨rfl, -⟩ := hw0
      exact ⟨heapOk_sound hok.pows hok.heap hb hh0, rd, hh0⟩
    have he1 : ∀ s1, (Mode.hintsAt Cf.frame.hints (Cf.frame.entry + i)).foldlM (Prover.Exec.runHint C) s = .ok s1 →
        ((C.hints[s.pc]?).getD []).foldlM (Prover.Exec.runHint C) s = .ok s1 := fun s1 e1 ↦ by
      rw [hpcF, hhintsF i hi]; exact e1
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
        obtain ⟨pos, pre, es, vs, hpos, hb, hwp, hW⟩ := hheap σ0 hσ0
        obtain ⟨as, dv, pv, off, hpairs, hcell, -, hmem, hwr⟩ := pair_read hok.pair hpos
          (by rw [List.getElem?_eq_getElem hi, hci]) (by rw [← has_hasP]; exact hOi) hwp
          (hrwOf σ0 hσ0 pre es vs hb).1
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
      have hnj : ∀ oc od of, K.code[i]? ≠ some (.jump oc od of) := fun oc od of h ↦ by
        have := (retLast_jump hret h).1
        omega
      refine k s1 s' (he1 s1 e1) hm hmo e' hf' hle' (.move (i + 1) (hfp'.trans hm.fp.symm) hi1
        (by rw [hpc', hpc]; omega) ⟨hat', fun o ho ↦ by rw [hfp']; exact written_mono hle (hentw o ho),
          fun σ hσ ↦ ?_⟩)
      rw [hfp'] at hσ
      obtain ⟨pos, pre, es, vs, hpos, hb, hwp, hW⟩ := hheap σ hσ
      obtain ⟨pos', hpos', as, hpairs, hfallP⟩ := pair_fall hok.pair hpos hnj
      obtain ⟨evs, es', rfl, hwp', hWr⟩ := hfallP hwp (hrwOf σ hσ pre _ vs hb).1
      refine ⟨pos', pre ++ evs, es', vs, hpos', by rw [List.append_assoc]; exact hb, hwp', fun y hy ↦ ?_⟩
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
    · -- the return
      intro s1 s' e1 hm hmo e' hf' hle' hjo hjt
      obtain ⟨oc, od, of, hci, h0, h1, hpcs⟩ := hjt
      obtain ⟨-, rfl, rfl, hz, hfw⟩ := retLast_jump hret hci
      have hrj : ∃ c, K.code[i]? = some (.jump c 0 1) := ⟨oc, hci⟩
      cases hjo with
      | «local» t hnr => exact absurd hrj hnr
      | halt hnr => exact absurd hrj hnr
      | tail e hnr => exact absurd hrj hnr
      | call G t hnr => exact absurd hrj hnr
      | ret hregs hretw =>
        refine k s1 s' (he1 s1 e1) hm hmo e' hf' hle' (.ret oc hci (by omega) h0 h1 ?_)
        obtain ⟨pos, pre, es, vs, hpos, hb, hwp, hW⟩ := hheap σ0 hσ0
        obtain ⟨hrw, rd, hh0⟩ := hrwOf σ0 hσ0 pre es vs hb
        obtain ⟨as, hpairs, hpr⟩ := pair_ret hok.pair hpos hci hz (by simpa using hfw) hst hwp hrw
        rw [hhd i] at hpairs
        have hposts : ∀ p ∈ Cf.post, WrK s1.mem (p.1.addr σ0) := fun p hp ↦ by
          rcases hpr _ (postOk_sound hok.pows hok.post hb hh0 p hp) with h | ⟨a, ha, hfa, hma, hwa⟩
          · exact (hW _ h).mono hm.le
          · exact flow_wrk hκ e1 hs hm hpairs ha hfa
              (fun q hq ↦ hσ0.ptr _ _ hb a q (List.mem_append_right _ hma) hq) hwa
        have hw1 : ∀ o ∈ K.F.sig.entry, s1.mem.written (s1.fp + o) = true := fun o ho ↦ by
          rw [hm.fp]; exact written_mono hm.le (hentw o (hok.fsig ▸ ho))
        have hσ1 : HonF img Cf s1.fp σ0 := hm.fp ▸ hσ0
        have hcells : ∀ m, monoOk K.F.sig Cf.fn.params.length m = true → BaseCells (stOf s1.mem s1.fp) σ0 m.bs :=
          fun m hmk ↦ baseCells_of (s := s1) hκ hmk hm.fine hw1 hσ1
        have hin : ∀ c, cellIn c (Cf.post.map (·.1)) = true → WrK s1.mem (c.addr σ0) := by
          intro c hc
          obtain ⟨c', hc', hbeq⟩ := List.any_eq_true.mp hc
          obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc'
          rw [← CCell.beq_eq hbeq]
          exact hposts p hp
        refine ⟨⟨fun o ho ↦ hretw o (hok.fsig ▸ ho), fun m hm' ↦ ?_, fun r hr ↦ ?_, fun q hq ↦ ?_, fun p hp ↦ ?_,
          fun p hp ↦ ?_, fun q hq ↦ ?_⟩, fun r hr ↦ ?_, fun q hq ↦ ?_⟩
        · have h := hpost m hm'
          simp only [postIn, Bool.and_eq_true] at h
          obtain ⟨hmk, hc⟩ := h
          split at hc
          · rename_i c hmc
            exact wrk_hw hmc (hcells m hmk) (hin c hc)
          · cases hc
        · have h := hpostR r hr
          simp only [postRIn, Bool.and_eq_true] at h
          obtain ⟨hmk, hc⟩ := h
          split at hc
          · rename_i c hmc
            split at hc
            · rename_i l hl
              exact wrk_rw hmc (hcells r.q hmk) hl fun p hp ↦ hin p (List.all_eq_true.mp hc p hp)
            · cases hc
          · cases hc
        · rw [hpostP] at hq; cases hq
        · rw [hretV] at hp; cases hp
        · rw [hpostT] at hp; cases hp
        · rw [hpostC] at hq; cases hq
        · rw [hpostL] at hr; cases hr
        · rw [hpostLP] at hq; cases hq

end

end LeanVM.Guest.CoreMode
