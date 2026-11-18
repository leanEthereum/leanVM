/-
  LeanVM.Guest.CoreMode.CoreSound

  The core route meets the frame interface: `frameSpec_core`.
-/

module

public import LeanVM.Guest.CoreMode.Core
public import LeanVM.Guest.CoreMode.PairJump

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
open LeanVM.Guest.Bridge (AlignCtx Zip ZOk fwdJ flowAtom isaFlowHint stmtsOf stmtsSub zok_stmts Pairs fwdOff_eq
  walk_ret_cons walk_atom_cons pre_eq_ret)
open LeanVM.Guest.Check (getF)
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
  unfold monoC monoF at h
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

theorem rw_wrk {s : St} {σ : Val} {r : Mode.Rng} {c : CCell} {l : List CCell} (hm : monoC r.q = some c)
    (hc : BaseCells s σ r.q.bs) (hl : runPts c r = some l) (h : RW s r) : ∀ p ∈ l, WrK s.mem (p.addr σ) := by
  unfold runPts at hl
  split at hl
  · rename_i a b hlo hhi
    cases hl
    obtain ⟨vq, xlo, xhi, hvq, hxlo, hxhi, hall⟩ := h
    rw [hlo] at hxlo
    rw [hhi] at hxhi
    simp only [Mode.IdxVal] at hxlo hxhi
    subst hxlo hxhi
    rw [(monoVal_iff hm hc vq).mp hvq] at hall
    intro p hp
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hp
    rw [List.mem_range] at hj
    obtain ⟨x, hx, hw⟩ := hall (xlo + j) (by omega) (by omega)
    refine ⟨x, ?_, hx.2, hw⟩
    rw [← hx.1]
    simp only [CCell.addr, CCell.val, addressOfIndex, pow_add, ofK_mul']
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
      obtain ⟨es1, es2, h2, -⟩ := walk_cons_noRet ht.1 h
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
      obtain ⟨es1, es2, h2, rfl⟩ := walk_cons_noRet ht.1 hw
      exact List.mem_append_right _ (hpVal_mem ht.2 h2 h)

/-- **The promised products' bases at the return**: a parameter's frame cell, a return cell holding the
returned value, the word past a parameter's a top-level `load` read, written. -/
theorem baseCellsP_of {img : MemoryImage κ} (hκ : κ ≤ 28) {Cf : CFun} {G : Mode.Sig} {m : Mode.Mono}
    (hm : monoOkP G Cf.fn.params.length m = true) (htop : Cf.fn.body.all topOk = true) {s : St}
    (hs : Fine (refMem img) s) (hw : ∀ o ∈ G.entry, s.mem.written (s.fp + o) = true)
    (hwr : ∀ o ∈ G.ret, s.mem.written (s.fp + o) = true) {σ : Val} (hσ : HonF img Cf s.fp σ) {es : List Ev}
    {vs : List V} (hb : walk σ Cf.fn.body = .ret es vs) (hW : ∀ y, Written Cf.H σ es y → WrK s.mem y) :
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
    obtain ⟨x, hx, hxlt, hxw⟩ := hW _ (Or.inr ⟨_, hl, rfl⟩)
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
        monoOk G np p.2 = true ∧ ∃ c v, monoC p.2 = some c ∧ v ∈ vs ∧ X.locAt v.idx = p.1 ∧ σ v = c.val σ
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

/-- **The returned products**: on a path that returns, each product of `retV` is a return cell
holding a returned value whose word is the product's. -/
theorem retVOk_sound {Cf : CFun} {G : Mode.Sig} (hp : Cf.pows.Ok) (hok : retVOk Cf G = true) {σ : Val}
    {rd : Reader} {es : List Ev} {vs : List V} (hw : walk σ Cf.fn.body = .ret es vs) (hh : ∀ e ∈ es, e.Holds rd σ) :
    ∀ p ∈ G.retV, p.1 < 2 ^ 28 ∧ p.1 ∈ G.ret ∧ monoOk G Cf.fn.params.length p.2 = true ∧
      ∃ c v, monoC p.2 = some c ∧ v ∈ vs ∧ Cf.X.locAt v.idx = p.1 ∧ σ v = c.val σ := by
  unfold retVOk at hok
  rcases Bool.or_eq_true_iff.mp hok with h | hok
  · intro p hp; rw [List.isEmpty_iff.mp h] at hp; cases hp
  rw [Exec.Trie.seq_eq, Exec.Trie.seq_eq] at hok
  exact retVGo_sound (hx := ⟨Cf.pows, Cf.H.readT, trieFrom Cf.H.sig.pre 0 .nil⟩) (H := Cf.H) (rd := rd) rfl
    (fun k c h ↦ (getF_trieFrom _ _ _ h).resolve_right (by simp [getF_nil])) hp Cf.fn.body
    (W := fun x ↦ ∃ c ∈ Cf.H.sig.pre, c.addr σ = x) (fun c hc ↦ ⟨c, hc, rfl⟩) hok envOk_nil
    (fun n c h ↦ by simp [getF_nil] at h) hw hh


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
      od ≠ 0 ∧ Cf.X.pcAt od = none ∧ Cf.frame.calls.get k = none ∧ ∃ a ts, getF Cf.X.arms od = some a ∧
        Cf.frame.arms.get k = some ts ∧ armsCover Cf.X Cf.frame.entry ml a ts = true
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
      simp only [Bool.and_eq_true, Bool.not_eq_true', Option.isNone_iff_eq_none] at h1
      obtain ⟨⟨⟨h0, hpc⟩, hcl⟩, h2⟩ := h1
      split at h2
      · rename_i a ts ha hts
        exact ⟨fun e ↦ by simp [e] at h0, hpc, hcl, a, ts, ha, hts, h2⟩
      · cases h2
    | succ i =>
      exact tgtGo_at h.2 (by simpa using hi) (by rw [show n + 1 + i = n + (i + 1) by omega]; exact ht)

/-! ## Jumps -/

theorem written_prefix {H : HCert} {σ : Val} {l l' : List Ev} {x : K} (h : Written H σ l x) :
    Written H σ (l ++ l') x := by
  rcases h with h | ⟨a, ha, hw⟩
  · exact Or.inl h
  · exact Or.inr ⟨a, List.mem_append_left _ ha, hw⟩

/-- **A jump's hints' atoms and reads** write only what is written once its hints ran. -/
theorem jump_events {img : MemoryImage κ} (hκ : κ ≤ 28) {X : AlignCtx} {H : HCert} {C : Ctx}
    {hs : List Prover.Exec.Hint} {s s1 : St} (e1 : hs.foldlM (Prover.Exec.runHint C) s = .ok s1)
    (hs0 : Fine (refMem img) s) (hm : Moves (refMem img) s s1) {σ : Val} {as bs : List Atom}
    (hq : ∀ a ∈ as, flowAtom a = false → stopS H.readT a = false) (hbs : ∀ a ∈ bs, stopS H.readT a = false)
    (hpairs : List.Forall₂ (Pairs X) (as.filter flowAtom) (hs.filter isaFlowHint))
    (hptr : ∀ a ∈ as, ∀ p, ptrOf a = some p → Rd img s.fp (X.locAt p.idx) = some (σ p))
    {pre rest : List Ev} (hrw : ReadsWritten H σ (pre ++ (as ++ bs).map Ev.atom ++ rest))
    (hW : ∀ y, Written H σ pre y → WrK s.mem y) :
    ∀ y, Written H σ (pre ++ (as ++ bs).map Ev.atom) y → WrK s1.mem y := by
  have hside : ∀ a, Ev.atom a ∈ (as ++ bs).map Ev.atom → a ∉ as.filter flowAtom → stopS H.readT a = false := by
    intro a ha hn
    simp only [List.map_append, List.mem_append, List.mem_map, Ev.atom.injEq, exists_eq_right] at ha
    rcases ha with ha | ha
    · cases hfa : flowAtom a
      · exact hq a ha hfa
      · exact absurd (List.mem_filter.mpr ⟨ha, hfa⟩) hn
    · exact hbs a ha
  intro y hy
  rcases written_extend (fs := as.filter flowAtom) hrw hside hy with h | ⟨a, ha, hwa⟩
  · exact (hW y h).mono hm.le
  · rw [List.mem_filter] at ha
    exact flow_wrk hκ e1 hs0 hm hpairs ha.1 ha.2 (hptr a ha.1) hwa

/-- The head statement a jump steps by, on the core route's shape: a branch, a `match` or a return. -/
theorem head_cases {Cf : CFun} {zs : Zip} (hzsok : ZOk Cf.fn.body zs) (hctrl : ∀ s ∈ stmtsOf Cf.fn.body, ctrlOk s = true)
    {i oc od of : ℕ} {tabs : List (ℕ × Zip × ℕ)} {r : Option Zip × List (ℕ × Zip)}
    (hh : headStepH Cf.P i oc od of tabs zs = some r) :
    (∃ c zb nb ss, zs.cur = .ite c zb nb :: ss) ∨ (∃ x arms ss, zs.cur = .match_ x arms :: ss) ∨
      ∃ vs ss, zs.cur = .ret vs :: ss := by
  obtain ⟨st, ss, hcur, hna⟩ := headH_stmt hh
  have hc := hctrl st (zok_stmts hzsok (by rw [Zip.pos_head hcur]; exact List.mem_cons_self))
  cases st with
  | atom a => exact absurd rfl (hna a)
  | ite c zb nb => exact Or.inl ⟨c, zb, nb, ss, hcur⟩
  | match_ x arms => exact Or.inr (Or.inl ⟨x, arms, ss, hcur⟩)
  | ret vs => exact Or.inr (Or.inr ⟨vs, ss, hcur⟩)
  | _ => simp [ctrlOk] at hc

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

/-- **The frame walk's table jumps land at their arms**, of the reference: a `JUMP` the walk reads
a table for is a `match`'s, its target the slot of the arm the selector picks. -/
theorem core_tgt {img : MemoryImage κ} {Cf : CFun} {code : List OffsetInstruction}
    (hpair : pairOk Cf.X Cf.H Cf.frame.O Cf.frame.S Cf.fn.body code Cf.d = true)
    (hctrl : ∀ s ∈ stmtsOf Cf.fn.body, ctrlOk s = true) (hmain : Cf.X.main = false) (htgt : tgtOk Cf code = true)
    {fp i : ℕ} {σ : Val} (hσ : HonF img Cf fp σ) {pos : List Stmt} {es : List Ev} {vs : List V}
    (hat : pairAt Cf.P Cf.fn.body code Cf.d i = some pos) (hwp : walk σ pos = .ret es vs) :
    TgtOk img Cf.frame code i fp := by
  intro c d f hci cv dv hcv hne hdv pc hpcl hdl kk hk
  rw [tgtOk, Exec.listSeq_eq] at htgt
  obtain ⟨hd0, hpcn, hcl, a, ts0, ha, hts0, hcov⟩ := tgtGo_at htgt hci (by rw [Nat.zero_add]; exact hk)
  refine ⟨fun pcs h ↦ by (rw [hcl] at h; cases h), fun ts hts ↦ ?_⟩
  rw [hts0, Option.some.injEq] at hts
  subst hts
  obtain ⟨as, bs, z, zs, tabs, r, hpos, hzpos, -, -, -, -, hzsok, hr, -, -, -⟩ := pair_jump hpair hat hci
  rw [hpos, hzpos, ← List.append_assoc, ← List.map_append] at hwp
  obtain ⟨es1, hes1, -⟩ := walk_atoms_ret hwp
  cases hz : Cf.X.zeroAt c
  swap
  · exact absurd (Option.some.inj ((hσ.jc.zero c hz).symm.trans hcv)).symm hne
  cases hf : fwdJ Cf.X i c d f
  swap
  · obtain ⟨-, -, t, -, ht, -⟩ := jumpH_fwd hr hz hf
    have ht' : Cf.X.pcAt d = some t := ht
    rw [hpcn] at ht'; cases ht'
  have hh := headH_of hr hz hf
  rcases head_cases hzsok hctrl hh with ⟨cc, zb, nb, ss, hcur⟩ | ⟨x, arms, ss, hcur⟩ | ⟨vs', ss, hcur⟩
  · obtain ⟨-, -, t, -, -, -, ht, -⟩ := headH_ite hh hcur
    have ht' : Cf.X.pcAt d = some t := ht
    rw [hpcn] at ht'; cases ht'
  · obtain ⟨-, -, hax, -⟩ := jumpH_match hr hcur hz hf ha
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
    (hwp : walk σ pos = .ret es vs) (hrw : ReadsWritten Cf.H σ (pre ++ es))
    (hW : ∀ y, Written Cf.H σ pre y → WrK s.mem y) :
    ∃ pos', pairAt Cf.P Cf.fn.body code Cf.d (i + 1) = some pos' ∧ ∃ evs es', es = evs ++ es' ∧
      walk σ pos' = .ret es' vs ∧ ∀ y, Written Cf.H σ (pre ++ evs) y → WrK s1.mem y := by
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
    refine ⟨z.pos, h1 z rfl, as.map Ev.atom, bs.map Ev.atom ++ es1, by simp, ?_,
      fun y hy ↦ hev y (by rw [List.map_append, ← List.append_assoc]; exact written_prefix hy)⟩
    rw [hzpos, walk_atoms, hes1]
    rfl
  cases hf : fwdJ Cf.X i oc od of
  swap
  · exact absurd (jumpH_fwd hr hz hf).1 (fun h ↦ hnz h)
  have hh := headH_of hr hz hf
  rcases head_cases hzsok hctrl hh with ⟨c, zb, nb, ss, hcur⟩ | ⟨x, arms, ss, hcur⟩ | ⟨vs', ss, hcur⟩
  · obtain ⟨hloc, -, t, cz, cn, o, -, hcz, -, -, rfl⟩ := headH_ite hh hcur
    obtain ⟨es2, rfl, hes2⟩ := side_ite hcur hes1
    have hcond := hσ.jc.cond _ _ hb c (by simp)
    have hloc' : Cf.X.locAt c.idx = oc := hloc
    rw [hloc'] at hcond
    have hσc : σ c = 0 := (rd_get hκ hm.fine hoc (by rw [hm.fp]; exact hcond) hc0).symm
    simp only [hσc, ↓reduceIte] at hes2
    obtain ⟨evs, es3, rfl, hes3, hWn⟩ := succ_norm hcz hes2
    refine ⟨cz.pos, h1 cz rfl, (as ++ bs).map Ev.atom ++ Ev.inK c :: evs, es3, by simp, hes3, fun y hy ↦ ?_⟩
    have h2 := hWn (pre ++ (as ++ bs).map Ev.atom ++ [Ev.inK c]) y (by simpa [List.append_assoc] using hy)
    exact hev y (written_noAtom (fun a h ↦ by cases h) h2)
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
    {C : Ctx} {s s1 s' : St} {i oc od of : ℕ} (hins : code[i]? = some (.jump oc od of)) (hoc : oc < 2 ^ 28)
    (hod : od < 2 ^ 28)
    (e1 : ((Cf.d.2.2.lookup (Cf.X.entry + i)).getD []).foldlM (Prover.Exec.runHint C) s = .ok s1)
    (hs : Fine (refMem img) s) (hm : Moves (refMem img) s s1) {v : E} (hcv : s1.mem.get (s1.fp + oc) = some v)
    (hv0 : v ≠ 0) (hd : s1.mem.get (s1.fp + od) = some (ofK (g ^ s'.pc))) (hpcs : s'.pc < 2 ^ 30)
    {σ : Val} (hσ : HonF img Cf s.fp σ) {pos : List Stmt} {pre es : List Ev} {vs : List V}
    (hat : pairAt Cf.P Cf.fn.body code Cf.d i = some pos) (hb : walk σ Cf.fn.body = .ret (pre ++ es) vs)
    (hwp : walk σ pos = .ret es vs) (hrw : ReadsWritten Cf.H σ (pre ++ es))
    (hW : ∀ y, Written Cf.H σ pre y → WrK s.mem y) :
    (od = 0 ∧ of = 1 ∧ ∀ y, Written Cf.H σ (pre ++ es) y → WrK s1.mem y) ∨
    (Cf.X.selfAt of = true ∧ ∃ o pos', s'.pc = Cf.X.entry + o ∧ i < o ∧
      pairAt Cf.P Cf.fn.body code Cf.d o = some pos' ∧ ∃ evs es', es = evs ++ es' ∧
        walk σ pos' = .ret es' vs ∧ ∀ y, Written Cf.H σ (pre ++ evs) y → WrK s1.mem y) := by
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
      hat', as.map Ev.atom, bs.map Ev.atom ++ es1, by simp, ?_,
      fun y hy ↦ hev y (by rw [List.map_append, ← List.append_assoc]; exact written_prefix hy)⟩
    rw [hzpos, walk_atoms, hes1]
    rfl
  have hh := headH_of hr hz hf
  rcases head_cases hzsok hctrl hh with ⟨c, zb, nb, ss, hcur⟩ | ⟨x, arms, ss, hcur⟩ | ⟨vs', ss, hcur⟩
  · obtain ⟨hloc, hself, t, cz, cn, o, ht, -, hcn, ho, rfl⟩ := headH_ite hh hcur
    obtain ⟨es2, rfl, hes2⟩ := side_ite hcur hes1
    have hcond := hσ.jc.cond _ _ hb c (by simp)
    have hloc' : Cf.X.locAt c.idx = oc := hloc
    rw [hloc'] at hcond
    have hσc : σ c ≠ 0 := fun h0 ↦ hv0 (by rw [rd_get hκ hm.fine hoc (by rw [hm.fp]; exact hcond) hcv, h0])
    simp only [hσc, ↓reduceIte] at hes2
    obtain ⟨evs, es3, rfl, hes3, hWn⟩ := succ_norm hcn hes2
    obtain ⟨rfl, hlt⟩ := fwdOff_eq (X := Cf.X) ho
    have hat' := h2 _ List.mem_cons_self
    have ho' := pairAt_lt hpair hat'
    refine Or.inr ⟨hself, t - Cf.X.entry, cn.pos, by rw [hpcw t ht (by have := hlen _ ho'; omega)]; omega,
      by omega, hat', (as ++ bs).map Ev.atom ++ Ev.inK c :: evs, es3, by simp, hes3, fun y hy ↦ ?_⟩
    have h2' := hWn (pre ++ (as ++ bs).map Ev.atom ++ [Ev.inK c]) y (by simpa [List.append_assoc] using hy)
    exact hev y (written_noAtom (fun a h ↦ by cases h) h2')
  · obtain ⟨-, hself, a, ha⟩ := headH_match_nz hh hcur
    obtain ⟨-, -, hax, -⟩ := jumpH_match hr hcur hz hf ha
    obtain ⟨k0, hk0, hσx, hes2⟩ := side_arm hcur hes1
    have hmem : Stmt.match_ x arms ∈ stmtsOf Cf.fn.body :=
      zok_stmts hzsok (by rw [Zip.pos_head hcur]; exact List.mem_cons_self)
    obtain ⟨t, hjt, hlt, c', hc', hat'⟩ := h3 x arms ss a hcur hz hf ha k0 hk0
    obtain ⟨evs, es3, rfl, hes3, hWn⟩ := succ_norm hc' hes2
    have ho' := pairAt_lt hpair hat'
    have ht30 : t < 2 ^ 30 := by have := hlen _ ho'; omega
    have hpct : s'.pc = t := by
      have h := rd_get hκ hm.fine hod (by rw [hm.fp]; exact hσ.jc.arm x arms hmem od a ha hax k0 t hσx hjt) hd
      have hgt : (g : K) ^ s'.pc = g ^ t := by simpa using congrArg (fun e : E ↦ e.limb 0) h
      exact gpow_lt_inj (by omega) (by omega) hgt
    refine Or.inr ⟨hself, t - Cf.X.entry, c'.pos, by omega, by omega, hat', (as ++ bs).map Ev.atom ++ evs, es3,
      by simp, hes3, fun y hy ↦ ?_⟩
    exact hev y (hWn _ y (by simpa [List.append_assoc] using hy))
  · obtain ⟨-, -, h01⟩ := headH_ret hh hcur
    simp only [show (PairCtx.ofH Cf.X Cf.H Cf.frame.O Cf.frame.S).X.main = false from hmain, Bool.false_eq_true,
      ↓reduceIte] at h01
    rw [Zip.pos_head hcur, walk_ret_cons, Out.ret.injEq] at hes1
    obtain ⟨rfl, -⟩ := hes1
    exact Or.inl ⟨h01.1, h01.2, fun y hy ↦ hev y (by simpa using hy)⟩

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
    rcases head_cases hzsok hctrl hh with ⟨c, zb, nb, ss, hcur⟩ | h | ⟨vs', ss, hcur⟩
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

/-- **The core route meets the frame interface**: a function passing the kernel's checks, on the
executor's tables for the guest's advice, its code the executor's, at states `Y` on a reference run
where its frames have honest valuations. -/
theorem frameSpec_core {K : Mode.Cert} {Cf : CFun} (hok : CoreOk K Cf) {adv : Prover.Exec.Advice} {C : Ctx}
    (hC : Prover.Exec.Ctx.of guestProgram adv = .ok C) (ha : adv.hints = Data.adviceHints) (hK : CodeOk C K)
    {img : MemoryImage κ} {Y : St → Prop} (hκ : κ ≤ 28) (hY : ∀ s, Y s → ∃ n, OnRef guestProgram img n s)
    (hH : CoreHon img Y K Cf) : FrameSpec C (refMem img) Y K (CoreAt img Cf K.code) := by
  have hsh := hok.shape
  simp only [shapeOk, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, List.all_eq_true] at hsh
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hbody, hmain⟩, hself1⟩, htgt⟩, hsigs⟩, hfp1⟩, hnzr0⟩, hent⟩, hend⟩, hincr⟩ := hsh
  have hctrl := bodyC_ctrl hbody
  obtain ⟨henv, harm, hacc⟩ := hok.frame
  have hsig := hok.sig
  simp only [sigOk, Bool.and_eq_true, Option.isNone_iff_eq_none, List.isEmpty_iff, List.all_eq_true] at hsig
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hself, hterm⟩, hpostL⟩, hpostP⟩, hpostLP⟩, hpostT⟩, hpostC⟩, hpre⟩, hpost⟩,
    hpostR⟩ := hsig
  have hent' : ∀ x ∈ K.F.sig.entry, x + 1 < 2 ^ Exec.envDepth := hok.fsig ▸ hent
  have hsize := (Prover.Exec.ctx_of_spec hC).1
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
    · rcases Bool.or_eq_true_iff.mp (hpre c hc) with hp | hp
      · obtain ⟨m, hm, hmc⟩ := List.any_eq_true.mp hp
        rw [Bool.and_eq_true] at hmc
        obtain ⟨hmk, hmc⟩ := hmc
        split at hmc
        · rename_i c' hc'
          rw [← CCell.beq_eq hmc]
          exact hw_wrk hc' (baseCells_of hκ hmk hs hw hσ) (hH0.h m hm)
        · cases hmc
      · obtain ⟨rr, hrr, hmc⟩ := List.any_eq_true.mp hp
        rw [Bool.and_eq_true] at hmc
        obtain ⟨hmk, hmc⟩ := hmc
        split at hmc
        · rename_i c' hc'
          split at hmc
          · rename_i l hl
            obtain ⟨c'', hc'', hbeq⟩ := List.any_eq_true.mp hmc
            rw [← CCell.beq_eq hbeq]
            exact rw_wrk hc' (baseCells_of hκ hmk hs hw hσ) hl (hH0.r rr (List.mem_cons_of_mem _ hrr)) c'' hc''
          · cases hmc
        · cases hmc
    · cases ha'
  · -- a step
    intro s i hi hpc hat hs hYs hsz _ henvK _ _ _ _ _ hh _ href Inv k
    obtain ⟨hAtF, hentw, hheap⟩ := hat
    obtain ⟨σ0, hσ0⟩ := hH s i hYs hi hpc
    obtain ⟨n, hon⟩ := hY s hYs
    have hpcF : s.pc = Cf.frame.entry + i := by rw [hok.fentry]; exact hpc
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
    have hlen : ∀ o < K.code.length, Cf.X.entry + o < 2 ^ 30 := fun o ho ↦ by
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
        obtain ⟨pos, pre, es, vs, hpos, hb, hwp, hW⟩ := hheap σ0 hσ0
        by_cases hj : jtd Cf.X a o c = true
        · have hsm := hok.small i hi
          rw [hci] at hsm
          exact core_jtd hκ hok.pair hctrl hok.jtd (by rw [List.getElem?_eq_getElem hi, hci]) hj hsm.1 henvK hm hσ0
            hpos hb hwp
        obtain ⟨as, dv, pv, off, hpairs, hcell, -, hmem, hwr⟩ := pair_read hok.pair hpos
          (by rw [List.getElem?_eq_getElem hi, hci]) (by rw [← has_hasP]; exact hOi) (Bool.eq_false_iff.mpr hj) hwp
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
    · -- a table jump's target, one of its arms
      obtain ⟨pos, pre, es, vs, hpos, -, hwp, -⟩ := hheap σ0 hσ0
      exact core_tgt hok.pair hctrl hmain htgt hσ0 hpos hwp
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
        (by rw [hpc', hpc]; omega) ⟨hat', fun o ho ↦ by rw [hfp']; exact written_mono hle (hentw o ho),
          fun σ hσ ↦ ?_⟩)
      rw [hfp'] at hσ
      obtain ⟨pos, pre, es, vs, hpos, hb, hwp, hW⟩ := hheap σ hσ
      by_cases hj : ∃ oc od of, K.code[i]? = some (.jump oc od of)
      · -- a jump not taken
        obtain ⟨oc, od, of, hci⟩ := hj
        have e1' : ((Cf.d.2.2.lookup (Cf.X.entry + i)).getD []).foldlM (Prover.Exec.runHint C) s = .ok s1 := by
          rw [hhd i]; exact e1
        obtain ⟨pos', hpos', evs, es', rfl, hwp', hWr⟩ := core_jfall hκ hok.pair hctrl hci (hsm oc od of hci).1 e1' hs hm
          (hc0 oc od of hci) hσ hpos hb hwp (hrwOf σ hσ pre _ vs hb).1 hW
        exact ⟨pos', pre ++ evs, es', vs, hpos', by rw [List.append_assoc]; exact hb, hwp',
          fun y hy ↦ (hWr y hy).mono hle'⟩
      have hnj : ∀ oc od of, K.code[i]? ≠ some (.jump oc od of) := fun oc od of h ↦ hj ⟨oc, od, of, h⟩
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
    · -- a jump taken
      intro s1 s' e1 hm hmo e' hf' hle' hjo hjt hcn
      obtain ⟨oc, od, of, hci, hd, hfv, hpcs⟩ := hjt
      obtain ⟨v, hv, hv0⟩ := hcn oc od of hci
      obtain ⟨hoc, hod, -⟩ := hsm oc od of hci
      have e1' : ((Cf.d.2.2.lookup (Cf.X.entry + i)).getD []).foldlM (Prover.Exec.runHint C) s = .ok s1 := by
        rw [hhd i]; exact e1
      have hpcs' : s'.pc < 2 ^ 30 := by omega
      have hrj : ∀ c, K.code[i]? = some (.jump c 0 1) → od = 0 ∧ of = 1 := fun c h ↦ by
        rw [hci, Option.some.injEq, OffsetInstruction.jump.injEq] at h
        exact ⟨h.2.1, h.2.2⟩
      obtain ⟨pos, pre, es, vs, hpos, hb, hwp, hW⟩ := hheap σ0 hσ0
      rcases core_jtaken hκ hok.pair hctrl hmain hlen hci hoc hod e1' hs hm hv hv0 hd hpcs' hσ0 hpos hb hwp
        (hrwOf σ0 hσ0 pre es vs hb).1 hW with ⟨rfl, rfl, hWr⟩ | ⟨hselfo, o, -, hpco, hio, -⟩
      · -- the return
        have hrj' : ∃ c, K.code[i]? = some (.jump c 0 1) := ⟨oc, hci⟩
        cases hjo with
        | «local» t hnr => exact absurd hrj' hnr
        | halt hnr => exact absurd hrj' hnr
        | tail e hnr => exact absurd hrj' hnr
        | call G t hnr => exact absurd hrj' hnr
        | ret hregs hretw =>
          refine k s1 s' (he1 s1 e1) hm hmo e' hf' hle' (.ret oc hci (by omega) hd hfv ?_)
          obtain ⟨-, rd, hh0⟩ := hrwOf σ0 hσ0 pre es vs hb
          have hposts : ∀ p ∈ Cf.post, WrK s1.mem (p.1.addr σ0) := fun p hp ↦
            hWr _ (postOk_sound hok.pows hok.post hb hh0 p hp)
          have hw1 : ∀ o ∈ K.F.sig.entry, s1.mem.written (s1.fp + o) = true := fun o ho ↦ by
            rw [hm.fp]; exact written_mono hm.le (hentw o (hok.fsig ▸ ho))
          have hσ1 : HonF img Cf s1.fp σ0 := hm.fp ▸ hσ0
          have hcells : ∀ m, monoOk K.F.sig Cf.fn.params.length m = true → BaseCells (stOf s1.mem s1.fp) σ0 m.bs :=
            fun m hmk ↦ baseCells_of (s := s1) hκ hmk hm.fine hw1 hσ1
          have htop : Cf.fn.body.all topOk = true := by
            simp only [bodyC, Bool.and_eq_true] at hbody
            exact hbody.2
          have hcellsP : ∀ m, monoOkP K.F.sig Cf.fn.params.length m = true →
              BaseCellsF (baseOfP Cf.X Cf.fn.body Cf.fn.params.length) (stOf s1.mem s1.fp) σ0 m.bs :=
            fun m hmk ↦ baseCellsP_of (s := s1) hκ hmk htop hm.fine hw1 (fun o ho ↦ hretw o (hok.fsig ▸ ho)) hσ1
              hb hWr
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
              exact wrk_hwF (expKeep_P _ _ _) hmc (hcellsP m hmk) (hin c hc)
            · cases hc
          · have h := hpostR r hr
            simp only [postRIn, Bool.and_eq_true] at h
            obtain ⟨hmk, hc⟩ := h
            split at hc
            · rename_i c hmc
              split at hc
              · rename_i l hl
                exact wrk_rwF (expKeep_P _ _ _) hmc (hcellsP r.q hmk) hl fun p hp ↦ hin p (List.all_eq_true.mp hc p hp)
              · cases hc
            · cases hc
          · rw [hpostP] at hq; cases hq
          · obtain ⟨h28, hret, hmo, c, v, hmc, hv, hloc, hval⟩ :=
              retVOk_sound hok.pows hok.retv hb hh0 p hp
            obtain ⟨u, hu⟩ := Mem.get_of_written (hretw p.1 (hok.fsig ▸ hret))
            have hrd : Rd img s1.fp p.1 = some (σ0 v) := by
              rw [hm.fp, ← hloc]; exact hσ0.rets _ _ hb v hv
            refine ⟨u, hu, (monoVal_iff hmc (hcells p.2 hmo) u).mpr ?_⟩
            rw [rd_get hκ hm.fine h28 hrd hu, hval]
          · rw [hpostT] at hp; cases hp
          · rw [hpostC] at hq; cases hq
          · rw [hpostL] at hr; cases hr
          · rw [hpostLP] at hq; cases hq
      · -- a jump in the frame
        have hof1 : of ≠ 1 := fun h ↦ by rw [h, hself1] at hselfo; cases hselfo
        cases hjo with
        | «local» t hnr hfp' hpc' hat' =>
          have hto : t = o := by rw [hok.fentry, ← hok.xentry] at hpc'; omega
          subst hto
          have hle : s.mem ≤ s'.mem := Mem.le_trans hm.le hle'
          refine k s1 s' (he1 s1 e1) hm hmo e' hf' hle' (.move t hfp' ?_ (by rw [hpc', hok.fentry]) ⟨hat',
            fun o ho ↦ by rw [hfp', hm.fp]; exact written_mono hle (hentw o ho), fun σ hσ ↦ ?_⟩)
          · obtain ⟨cur, pend, h0, hh0⟩ := hat'
            by_contra hn
            obtain ⟨rfl, rfl⟩ := preF_end hacc (by omega) h0
            rcases hh0 with ⟨A, hA, -⟩ | ⟨g', hg', -⟩
            · cases hA
            · cases hg'
          rw [hfp', hm.fp] at hσ
          obtain ⟨pos, pre, es, vs, hpos, hb, hwp, hW⟩ := hheap σ hσ
          rcases core_jtaken hκ hok.pair hctrl hmain hlen hci hoc hod e1' hs hm hv hv0 hd hpcs' hσ hpos hb hwp
            (hrwOf σ hσ pre es vs hb).1 hW with ⟨-, h1, -⟩ | ⟨-, o', pos', hpco', -, hpos', evs, es', rfl, hwp', hWr⟩
          · exact absurd h1 hof1
          have ho' : o' = t := by omega
          subst ho'
          exact ⟨pos', pre ++ evs, es', vs, hpos', by rw [List.append_assoc]; exact hb, hwp',
            fun y hy ↦ (hWr y hy).mono hle'⟩
        | ret _ _ hr => obtain ⟨c, hc⟩ := hr; exact absurd (hrj c hc).2 hof1
        | halt _ h1 => simp [hfp1] at h1
        | tail e _ hpc' => rw [hpc', hok.fentry, ← hok.xentry] at hpco; omega
        | call G t _ hG => rw [trieNil_get hsigs] at hG; cases hG

end

end LeanVM.Guest.CoreMode
