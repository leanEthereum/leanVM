/-
  LeanVM.Guest.CoreMode.HeapSound

  The heap check's soundness on the path: every address an atom of a valuation's path reads is
  a precondition's or written by an atom before it.
-/

module

public import LeanVM.Guest.CoreMode.Heap
public import LeanVM.Guest.Exec
public import LeanVM.Guest.Value.Tower
public import LeanVM.Guest.TrieFacts

/-!
# The heap check is sound

`heapOk_sound`: for a function passing `heapOk`, a valuation `σ` whose path (`walk σ f.body`, `Memory/Eval.lean`) returns, every event of it holding on a reader, reads only what is written before (`ReadsWritten`): each address an atom of the path reads (`Reads`) is a precondition's address or written (`Writes`) by an atom earlier on the path.

The proof follows the pass along the path. Its environment is valid (`EnvOk`: each entry's monomial is the value's word under `σ`), since its entries come from atoms of the path, the valuation being fixed; its scope's cells are written (`ScOk W`: each one's address is in `W`, the preconditions' and the path's writes so far), each entered by a write event of the path. An `ite` or a `match` is followed into the block the path takes, from the state before it, and the pass goes on after it with that state, which is still valid. `Cov W es`: each read of `es` is in `W` or written by an atom of `es` before it.
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Exec (Trie PowTree natSeq natSeq_eq)
open LeanVM.Guest.Check (getF setF limbNat getF_eq setF_eq)
open LeanVM.Guest.Value (eq_ofLimbs ofLimbs_mul_ofK ofLimbs_limb0)

public section

/-! ## Monomials -/

section Mono

variable (σ : Val)

theorem vnum_eq {v : V} {k : ℕ} (h : vnum v = some k) : v = V.n k := by
  obtain ⟨path, tag, idx⟩ := v
  unfold vnum at h
  cases path with
  | cons _ _ => simp at h
  | nil =>
    cases ht : Nat.beq tag 0
    · simp [ht] at h
    · simp only [List.isEmpty_nil, ht, Bool.and_self, Bool.cond_true, Option.some.injEq] at h
      rw [Nat.eq_of_beq_eq_true ht, ← h]

theorem prodB_insB (k e : ℕ) : ∀ l, prodB σ (insB k e l) = σ (V.n k) ^ e * prodB σ l
  | [] => by simp [insB, prodB]
  | (k', e') :: l => by
    unfold insB
    cases h1 : Nat.beq k k'
    · cases h2 : Nat.blt k k'
      · simp only [Bool.cond_false]
        rw [prodB, prodB_insB k e l, prodB]
        ring
      · simp only [Bool.cond_false, Bool.cond_true, prodB]
    · obtain rfl := Nat.eq_of_beq_eq_true h1
      simp only [Bool.cond_true, prodB]
      rw [pow_add]
      ring

theorem prodB_mergeB : ∀ a b, prodB σ (mergeB a b) = prodB σ a * prodB σ b
  | [], b => by simp [mergeB, prodB]
  | (k, e) :: a, b => by
    rw [mergeB, prodB_insB, prodB_mergeB a b, prodB]
    ring

theorem ofK_mul' (a b : K) : ofK (a * b) = ofK a * ofK b := map_mul (algebraMap K E) a b

theorem val_mul (a b : CCell) : (a.mul b).val σ = a.val σ * b.val σ := by
  simp only [CCell.val, CCell.mul, prodB_mergeB, addressOfIndex, pow_add, ofK_mul']
  ring

theorem val_baseC (k : ℕ) : (baseC k).val σ = σ (V.n k) := by
  simp only [CCell.val, baseC, prodB, pow_one, mul_one, addressOfIndex, pow_zero]
  rw [show ofK (1 : K) = 1 from map_one (algebraMap K E), mul_one]

theorem limb0_mul_ofK (x : E) (k : K) : (x * ofK k).limb 0 = x.limb 0 * k := by
  conv_lhs => rw [eq_ofLimbs x]
  rw [ofLimbs_mul_ofK, ofLimbs_limb0]

/-- A `DEREF` through a value of monomial `m` at offset `off` names the cell `m · g^off`. -/
theorem cellAt_shift {p : V} {m : CCell} (h : σ p = m.val σ) (off : ℕ) :
    cellAt σ p off = (m.shift off).addr σ := by
  simp only [cellAt, CCell.addr, CCell.val, CCell.shift, h, addressOfIndex, pow_add, ofK_mul',
    ← mul_assoc, limb0_mul_ofK]

theorem basesBeq_eq : ∀ {a b : List (ℕ × ℕ)}, basesBeq a b = true → a = b
  | [], [], _ => rfl
  | (x, e) :: l, (x', e') :: l', h => by
    simp only [basesBeq, Bool.and_eq_true] at h
    rw [Nat.eq_of_beq_eq_true h.1.1, Nat.eq_of_beq_eq_true h.1.2, basesBeq_eq h.2]
  | [], _ :: _, h => by simp [basesBeq] at h
  | _ :: _, [], h => by simp [basesBeq] at h

theorem CCell.beq_eq {a b : CCell} (h : a.beq b = true) : a = b := by
  obtain ⟨ab, ao⟩ := a
  obtain ⟨bb, bo⟩ := b
  simp only [CCell.beq, Bool.and_eq_true] at h
  rw [Nat.eq_of_beq_eq_true h.1, basesBeq_eq h.2]

end Mono

/-! ## Tries -/

section Tries

variable {α : Type}

theorem getF_nil (k : ℕ) : getF (Trie.nil : Trie α) k = none := rfl

theorem getF_trieFrom : ∀ (l : List α) (i : ℕ) (t : Trie α) {k : ℕ} {b : α},
    getF (trieFrom l i t) k = some b → b ∈ l ∨ getF t k = some b
  | [], _, _, _, _, h => Or.inr h
  | a :: l, i, t, k, b, h => by
    rw [trieFrom, Trie.seq_eq, natSeq_eq] at h
    rcases getF_trieFrom l (i + 1) _ h with h | h
    · exact Or.inl (List.mem_cons_of_mem _ h)
    · rcases Check.getF_setF h with ⟨-, rfl⟩ | h
      · exact Or.inl List.mem_cons_self
      · exact Or.inr h

end Tries

/-! ## The pass's invariant -/

section Inv

variable {σ : Val}

/-- **The environment is valid**: each entry is its value's word under `σ`. -/
@[expose] def EnvOk (σ : Val) (env : Trie CCell) : Prop := ∀ k c, getF env k = some c → σ (V.n k) = c.val σ

/-- **The scope is written**: each cell's address is in `W`. -/
@[expose] def ScOk (W : K → Prop) (σ : Val) (sc : Trie CCell) : Prop := ∀ n c, getF sc n = some c → W (c.addr σ)

theorem ScOk.mono {W W' : K → Prop} (hw : ∀ x, W x → W' x) {sc : Trie CCell} (h : ScOk W σ sc) :
    ScOk W' σ sc :=
  fun n c hc ↦ hw _ (h n c hc)

theorem envOk_nil : EnvOk σ .nil := fun _ _ h ↦ by simp [getF_nil] at h

theorem monoOf_ok {env : Trie CCell} (he : EnvOk σ env) {v : V} {c : CCell} (h : monoOf env v = some c) :
    σ v = c.val σ := by
  unfold monoOf at h
  cases hv : vnum v with
  | none => simp [hv] at h
  | some k =>
    rw [hv, Option.some.injEq] at h
    rw [vnum_eq hv, ← h]
    cases hk : getF env k with
    | none => rw [Option.getD_none, val_baseC]
    | some c' => rw [Option.getD_some]; exact he k c' hk

theorem envPut_ok {env : Trie CCell} (he : EnvOk σ env) {k : ℕ} {c : CCell} (hc : σ (V.n k) = c.val σ) :
    EnvOk σ (envPut env k c) := by
  unfold envPut
  cases getF env k with
  | some _ => exact he
  | none =>
    intro k' c' h
    rw [CCell.seq_eq, Trie.seq_eq] at h
    rcases Check.getF_setF h with ⟨rfl, rfl⟩ | h
    · exact hc
    · exact he k' c' h

theorem def_ok {st : HSt} (he : EnvOk σ st.env) {k : ℕ} {c : CCell} (hc : σ (V.n k) = c.val σ) :
    EnvOk σ (st.def k c).env ∧ (st.def k c).sc = st.sc :=
  ⟨envPut_ok he hc, rfl⟩

theorem push_ok {W : K → Prop} {st : HSt} (hs : ScOk W σ st.sc) {c : CCell} (hc : W (c.addr σ)) :
    (st.push c).env = st.env ∧ ScOk W σ (st.push c).sc := by
  unfold HSt.push
  rw [Trie.seq_eq]
  refine ⟨rfl, fun n c' h ↦ ?_⟩
  change getF (setF c Exec.indexDepth st.sc st.n) n = some c' at h
  rcases Check.getF_setF h with ⟨-, rfl⟩ | h
  · exact hc
  · exact hs n c' h

theorem pushN_ok {W : K → Prop} {m : CCell} {off : ℕ} :
    ∀ (len : ℕ) {st : HSt}, ScOk W σ st.sc → (∀ j < len, W ((m.shift (off + j)).addr σ)) →
      (st.pushN m off len).env = st.env ∧ ScOk W σ (st.pushN m off len).sc
  | 0, _, hs, _ => ⟨rfl, hs⟩
  | len + 1, st, hs, hc => by
    rw [HSt.pushN, HSt.seq_eq, CCell.seq_eq]
    obtain ⟨he1, hs1⟩ := pushN_ok len hs fun j hj ↦ hc j (by omega)
    obtain ⟨he2, hs2⟩ := push_ok hs1 (hc len (by omega))
    exact ⟨he2.trans he1, hs2⟩

theorem copyH_ok {st : HSt} (he : EnvOk σ st.env) {x y : V} (hxy : σ x = σ y) :
    EnvOk σ (copyH st x y).env ∧ (copyH st x y).sc = st.sc := by
  unfold copyH
  cases hx : vnum x with
  | none => exact ⟨he, rfl⟩
  | some kx =>
    cases hy : vnum y with
    | none => exact ⟨he, rfl⟩
    | some ky =>
      have hx' := vnum_eq hx
      have hy' := vnum_eq hy
      dsimp only
      cases hcx : getF st.env kx with
      | none =>
        refine def_ok he ?_
        rw [← hx', hxy, hy']
        cases hcy : getF st.env ky with
        | none => rw [Option.getD_none, val_baseC]
        | some c => rw [Option.getD_some]; exact he ky c hcy
      | some cx =>
        cases hcy : getF st.env ky with
        | none =>
          refine def_ok he ?_
          rw [← hy', ← hxy, hx']
          exact he kx cx hcx
        | some _ => exact ⟨he, rfl⟩

theorem powOf_ok {pows : PowTree} (hp : pows.Ok) {c : E} {e : ℕ} (h : powOf pows c = some e) :
    c = ofK (addressOfIndex e) := by
  unfold powOf at h
  have hc : c = E.ofLimbs (K.ofBits (limbNat c 0)) (K.ofBits (limbNat c 1)) := by
    simp only [limbNat, K.ofBits, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    exact (ofLimbs_limb c).symm
  cases h1 : Nat.beq (limbNat c 1) 0
  · simp [h1] at h
  · rw [h1, Bool.cond_true] at h
    rw [hc, Nat.eq_of_beq_eq_true h1, show K.ofBits 0 = 0 from rfl, ← ofK_eq_ofLimbs]
    congr 1
    cases h0 : Nat.beq (limbNat c 0) 1
    · rw [h0, Bool.cond_false] at h
      exact Exec.PowTree.find_ok hp h
    · rw [h0, Bool.cond_true, Option.some.injEq] at h
      rw [Nat.eq_of_beq_eq_true h0, ← h, addressOfIndex, pow_zero]
      rfl

end Inv

/-! ## Covered reads -/

section Cov

variable (H : HCert) (σ : Val)

/-- An address an atom of `es` writes. -/
@[expose] def WL (es : List Ev) (x : K) : Prop := ∃ b, Ev.atom b ∈ es ∧ Writes σ b x

/-- **The reads of `es` are covered**: in `W`, or written by an atom of `es` before. -/
def Cov (W : K → Prop) (es : List Ev) : Prop :=
  ∀ es1 a es2 x, es = es1 ++ Ev.atom a :: es2 → Reads H σ a x → W x ∨ WL σ es1 x

variable {H σ}

theorem Cov.mono {W W' : K → Prop} (hw : ∀ x, W x → W' x) {es : List Ev} (h : Cov H σ W es) :
    Cov H σ W' es :=
  fun es1 a es2 x he hr ↦ (h es1 a es2 x he hr).imp_left (hw x)

theorem cov_nil (W : K → Prop) : Cov H σ W [] := fun es1 _ _ _ he _ ↦ by simp at he

theorem cov_append {W : K → Prop} {es1 es2 : List Ev} (h1 : Cov H σ W es1)
    (h2 : Cov H σ (fun x ↦ W x ∨ WL σ es1 x) es2) : Cov H σ W (es1 ++ es2) := by
  intro p a q x he hr
  rcases List.append_eq_append_iff.mp he with ⟨a', rfl, h⟩ | ⟨c', rfl, h⟩
  · rcases h2 a' a q x h hr with (hw | ⟨b, hb, hx⟩) | ⟨b, hb, hx⟩
    · exact Or.inl hw
    · exact Or.inr ⟨b, List.mem_append_left _ hb, hx⟩
    · exact Or.inr ⟨b, List.mem_append_right _ hb, hx⟩
  · cases c' with
    | nil =>
      simp only [List.nil_append] at h
      rcases h2 [] a q x (by rw [← h]; rfl) hr with hw | ⟨b, hb, _⟩
      · simpa using hw
      · simp at hb
    | cons e c'' =>
      rw [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact h1 p a c'' x rfl hr

theorem cov_atom {W : K → Prop} {a : Atom} (h : ∀ x, Reads H σ a x → W x) : Cov H σ W [Ev.atom a] := by
  intro p b q x he hr
  cases p with
  | nil =>
    rw [List.nil_append, List.cons.injEq] at he
    obtain ⟨he, -⟩ := he
    cases he
    exact Or.inl (h x hr)
  | cons _ p => simp at he

theorem cov_inK {W : K → Prop} {c : V} : Cov H σ W [Ev.inK c] := by
  intro p b q x he hr
  cases p with
  | nil => simp at he
  | cons _ p => simp at he

theorem wl_append {es1 es2 : List Ev} {x : K} (h : WL σ es2 x) : WL σ (es1 ++ es2) x :=
  let ⟨b, hb, hx⟩ := h
  ⟨b, List.mem_append_right _ hb, hx⟩

theorem wl_append_left {es1 es2 : List Ev} {x : K} (h : WL σ es1 x) : WL σ (es1 ++ es2) x :=
  let ⟨b, hb, hx⟩ := h
  ⟨b, List.mem_append_left _ hb, hx⟩

end Cov

/-! ## Atoms -/

section Atoms

variable {σ : Val} {rd : Reader} {H : HCert} {X : HX}

theorem reads_log2 {h : Hint} {x : K} (hr : Reads H σ (.hint h) x) : heapRead h = true := by
  cases h with
  | log2Ceil b n fl d =>
    cases b with
    | heap => rfl
    | stack => simp [Reads] at hr
  | _ => simp [Reads] at hr

theorem hintHeap_log2 {h : Hint} (hh : heapRead h = true) : hintHeap h = none := by
  cases h with
  | log2Ceil => rfl
  | _ => simp [heapRead] at hh

theorem char2_eq {a b : E} (h : a + b = 0) : a = b := by
  have := congrArg (· + b) h
  simpa [add_assoc, CharTwo.add_self_eq_zero] using this

/-- **An atom of the path**: its reads are in `W`, the environment stays valid, the scope's new
cells are its writes. -/
theorem atomH_ok (hR : X.R = H.readT) (hP : ∀ k c, getF X.pre k = some c → c ∈ H.sig.pre)
    (hpows : X.pows.Ok) {W : K → Prop} (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st st' : HSt} {a : Atom}
    (h : atomH X st a = some st') (he : EnvOk σ st.env) (hs : ScOk W σ st.sc) (ha : a.Holds rd σ) :
    (∀ x, Reads H σ a x → W x) ∧ EnvOk σ st'.env ∧ ScOk (fun x ↦ W x ∨ Writes σ a x) σ st'.sc := by
  have hsw : ScOk (fun x ↦ W x ∨ Writes σ a x) σ st.sc := hs.mono fun _ ↦ Or.inl
  cases a with
  | const d c =>
    refine ⟨fun x hr ↦ by simp [Reads] at hr, ?_⟩
    unfold atomH at h
    cases hd : vnum d with
    | none => simp only [hd, Option.some.injEq] at h; subst h; exact ⟨he, hsw⟩
    | some k =>
      cases hc : powOf X.pows c with
      | none => simp only [hd, hc, Option.some.injEq] at h; subst h; exact ⟨he, hsw⟩
      | some e =>
        simp only [hd, hc, Option.some.injEq] at h
        subst h
        obtain ⟨h1, h2⟩ := def_ok (c := ⟨[], e⟩) (k := k) he (by
          rw [← vnum_eq hd, show σ d = c from ha, powOf_ok hpows hc]
          simp [CCell.val, prodB])
        exact ⟨h1, h2 ▸ hsw⟩
  | mul d a b =>
    refine ⟨fun x hr ↦ by simp [Reads] at hr, ?_⟩
    unfold atomH at h
    cases hd : vnum d with
    | none => simp only [hd, Option.some.injEq] at h; subst h; exact ⟨he, hsw⟩
    | some k =>
      cases ha' : monoOf st.env a with
      | none => simp only [hd, ha', Option.some.injEq] at h; subst h; exact ⟨he, hsw⟩
      | some ma =>
        cases hb : monoOf st.env b with
        | none => simp only [hd, ha', hb, Option.some.injEq] at h; subst h; exact ⟨he, hsw⟩
        | some mb =>
          simp only [hd, ha', hb, Option.some.injEq] at h
          subst h
          obtain ⟨h1, h2⟩ := def_ok (c := ma.mul mb) (k := k) he (by
            rw [← vnum_eq hd, show σ d = σ a * σ b from ha, val_mul, monoOf_ok he ha', monoOf_ok he hb])
          exact ⟨h1, h2 ▸ hsw⟩
  | copy d s =>
    refine ⟨fun x hr ↦ by simp [Reads] at hr, ?_⟩
    simp only [atomH, Option.some.injEq] at h
    subst h
    obtain ⟨h1, h2⟩ := copyH_ok he (show σ d = σ s from ha)
    exact ⟨h1, h2 ▸ hsw⟩
  | assertEq a b =>
    refine ⟨fun x hr ↦ by simp [Reads] at hr, ?_⟩
    simp only [atomH, Option.some.injEq] at h
    subst h
    obtain ⟨h1, h2⟩ := copyH_ok he (char2_eq (show σ a + σ b = 0 from ha))
    exact ⟨h1, h2 ▸ hsw⟩
  | load d p off =>
    unfold atomH at h
    cases hm : monoOf st.env p with
    | none => simp [hm] at h
    | some m =>
      simp only [hm, CCell.seq_eq] at h
      cases hl : loadOk X st.sc d p off (m.shift off) with
      | false => simp [hl] at h
      | true =>
        simp only [hl, Bool.cond_true, Option.some.injEq] at h
        subst h
        have hcell := cellAt_shift σ (monoOf_ok he hm) off
        obtain ⟨h1, h2⟩ := push_ok (W := fun x ↦ W x ∨ Writes σ (.load d p off) x) hsw
          (c := m.shift off) (Or.inr (by rw [← hcell]; rfl))
        refine ⟨fun x hr ↦ ?_, h1 ▸ he, h2⟩
        obtain ⟨hw, rfl⟩ := hr
        rw [hcell]
        unfold loadOk at hl
        rw [hR] at hl
        unfold HCert.readWit at hw
        cases hwit : readWitT H.readT d p off with
        | none => rw [hwit] at hw; simp at hw
        | some w =>
          rw [hwit] at hl
          cases w with
          | ev n =>
            simp only [witOk] at hl
            cases hn : getF st.sc n with
            | none => rw [hn] at hl; simp at hl
            | some c' =>
              rw [hn] at hl
              rw [← CCell.beq_eq hl]
              exact hs n c' hn
          | pre k =>
            simp only [witOk] at hl
            cases hk : getF X.pre k with
            | none => rw [hk] at hl; simp at hl
            | some c' =>
              rw [hk] at hl
              rw [← CCell.beq_eq hl]
              exact hpre c' (hP k c' hk)
          | run => simp [witOk] at hl
          | res => simp [witOk] at hl
          | pf => simp [witOk] at hl
          | pfr => simp [witOk] at hl
          | word => simp [witOk] at hl
          | pts => simp [witOk] at hl
          | empty => simp [witOk] at hl
          | skip => simp [witOk] at hl
          | cat => simp [witOk] at hl
          | mrg => simp [witOk] at hl
          | perm => simp [witOk] at hl
          | prep => simp [witOk] at hl
          | app => simp [witOk] at hl
          | keep => simp [witOk] at hl
          | vp => simp [witOk] at hl
          | catM => simp [witOk] at hl
          | mrgE => simp [witOk] at hl
          | ab => simp [witOk] at hl
          | abx => simp [witOk] at hl
          | prep2 => simp [witOk] at hl
          | evs => simp [witOk] at hl
          | back => simp [witOk] at hl
          | der => simp [witOk] at hl
          | wnil => simp [witOk] at hl
          | wcons => simp [witOk] at hl
          | drv => simp [witOk] at hl
  | hint hn =>
    unfold atomH at h
    cases hh : hintHeap hn with
    | none =>
      cases hr : heapRead hn with
      | true => simp [hh, hr] at h
      | false =>
        simp only [hh, hr, Bool.cond_false, Option.some.injEq] at h
        subst h
        refine ⟨fun x hx ↦ ?_, he, hsw⟩
        rw [reads_log2 hx] at hr
        simp at hr
    | some t =>
      obtain ⟨p, off, len⟩ := t
      cases hm : monoOf st.env p with
      | none => simp [hh, hm] at h
      | some m =>
        simp only [hh, hm, Option.some.injEq] at h
        subst h
        obtain ⟨h1, h2⟩ := pushN_ok (W := fun x ↦ W x ∨ Writes σ (.hint hn) x) (m := m) (off := off) len hsw
          fun j hj ↦ Or.inr ⟨p, off, len, hh, j, hj, (cellAt_shift σ (monoOf_ok he hm) (off + j)).symm⟩
        refine ⟨fun x hx ↦ ?_, h1 ▸ he, h2⟩
        rw [hintHeap_log2 (reads_log2 hx)] at hh
        exact absurd hh (by simp)
  | _ =>
    simp only [atomH, Option.some.injEq] at h
    subst h
    exact ⟨fun x hr ↦ by simp [Reads] at hr, he, hsw⟩

end Atoms

/-! ## Blocks -/

section Blocks

variable {σ : Val} {rd : Reader} {H : HCert} {X : HX}

/-- The events hold. -/
@[expose] def AllHold (rd : Reader) (σ : Val) (es : List Ev) : Prop := ∀ e ∈ es, e.Holds rd σ

/-- An outcome's reads are covered. -/
def Covers (H : HCert) (σ : Val) (rd : Reader) (W : K → Prop) (o : Out) : Prop :=
  ∀ es vs, (o = .fall es ∨ o = .ret es vs) → AllHold rd σ es → Cov H σ W es

/-- **What a block's pass gives on the path**: falling through, its reads covered, the state at
its end valid, its scope written by `W` and the block's writes; returning, its reads covered. -/
def BlockOk (H : HCert) (σ : Val) (rd : Reader) (W : K → Prop) (o : Out) (st' : HSt) : Prop :=
  (∀ es, o = .fall es → AllHold rd σ es →
    Cov H σ W es ∧ EnvOk σ st'.env ∧ ScOk (fun x ↦ W x ∨ WL σ es x) σ st'.sc) ∧
  (∀ es vs, o = .ret es vs → AllHold rd σ es → Cov H σ W es)

theorem BlockOk.covers {W : K → Prop} {o : Out} {st' : HSt} (h : BlockOk H σ rd W o st') :
    Covers H σ rd W o := by
  rintro es vs (hw | hw) hh
  · exact (h.1 es hw hh).1
  · exact h.2 es vs hw hh

theorem allHold_append {es1 es2 : List Ev} (h : AllHold rd σ (es1 ++ es2)) :
    AllHold rd σ es1 ∧ AllHold rd σ es2 :=
  ⟨fun e he ↦ h e (List.mem_append_left _ he), fun e he ↦ h e (List.mem_append_right _ he)⟩

theorem covers_inK {W : K → Prop} {o : Out} (h : Covers H σ rd W o) (c : V) :
    Covers H σ rd W (o.pre [.inK c]) := by
  have key : ∀ es', Cov H σ W es' → Cov H σ W ([Ev.inK c] ++ es') := fun es' hc ↦
    cov_append cov_inK (hc.mono fun _ ↦ Or.inl)
  rintro es vs (hw | hw) hh
  · cases o with
    | fall es' =>
      simp only [Out.pre, Out.fall.injEq] at hw
      subst hw
      exact key es' (h es' [] (Or.inl rfl) (allHold_append hh).2)
    | ret => simp [Out.pre] at hw
    | stuck => simp [Out.pre] at hw
  · cases o with
    | ret es' vs' =>
      simp only [Out.pre, Out.ret.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      exact key es' (h es' vs' (Or.inr rfl) (allHold_append hh).2)
    | fall => simp [Out.pre] at hw
    | stuck => simp [Out.pre] at hw

/-- **A statement, then a block**: the statement's reads covered, and, where it falls through, the
block's pass from a state whose `W1` the statement's writes cover. -/
theorem blockOk_seq {W : K → Prop} {o1 : Out} {ss : List Stmt} {st' : HSt} {W1 : List Ev → K → Prop}
    (h1 : Covers H σ rd W o1)
    (h2 : ∀ es, o1 = .fall es → AllHold rd σ es →
      (∀ x, W1 es x → W x ∨ WL σ es x) ∧ BlockOk H σ rd (W1 es) (walk σ ss) st') :
    BlockOk H σ rd W (o1.seq (walk σ ss)) st' := by
  cases o1 with
  | fall es1 =>
    have hfall : ∀ es2, AllHold rd σ (es1 ++ es2) → Cov H σ (W1 es1) es2 → Cov H σ W (es1 ++ es2) :=
      fun es2 hh hc ↦ cov_append (h1 es1 [] (Or.inl rfl) (allHold_append hh).1)
        (hc.mono fun x hx ↦ (h2 es1 rfl (allHold_append hh).1).1 x hx)
    refine ⟨fun es hw hh ↦ ?_, fun es vs hw hh ↦ ?_⟩
    · simp only [Out.seq] at hw
      cases hk : walk σ ss with
      | fall es2 =>
        rw [hk] at hw
        simp only [Out.pre, Out.fall.injEq] at hw
        subst hw
        obtain ⟨hw1, hb⟩ := h2 es1 rfl (allHold_append hh).1
        obtain ⟨hc, he, hs⟩ := hb.1 es2 hk (allHold_append hh).2
        refine ⟨hfall es2 hh hc, he, hs.mono fun x hx ↦ ?_⟩
        rcases hx with hx | hx
        · rcases hw1 x hx with hx | hx
          · exact Or.inl hx
          · exact Or.inr (wl_append_left hx)
        · exact Or.inr (wl_append hx)
      | ret => rw [hk] at hw; simp [Out.pre] at hw
      | stuck => rw [hk] at hw; simp [Out.pre] at hw
    · simp only [Out.seq] at hw
      cases hk : walk σ ss with
      | ret es2 vs2 =>
        rw [hk] at hw
        simp only [Out.pre, Out.ret.injEq] at hw
        obtain ⟨rfl, -⟩ := hw
        obtain ⟨-, hb⟩ := h2 es1 rfl (allHold_append hh).1
        exact hfall es2 hh (hb.2 es2 vs2 hk (allHold_append hh).2)
      | fall => rw [hk] at hw; simp [Out.pre] at hw
      | stuck => rw [hk] at hw; simp [Out.pre] at hw
  | ret es1 vs1 =>
    refine ⟨fun es hw _ ↦ by simp [Out.seq] at hw, fun es vs hw hh ↦ ?_⟩
    simp only [Out.seq, Out.ret.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    exact h1 es1 vs1 (Or.inr rfl) hh
  | stuck => exact ⟨fun es hw _ ↦ by simp [Out.seq] at hw, fun es vs hw _ ↦ by simp [Out.seq] at hw⟩

mutual
/-- **The pass over a block, on the path.** -/
theorem chkL_ok (hR : X.R = H.readT) (hP : ∀ k c, getF X.pre k = some c → c ∈ H.sig.pre)
    (hpows : X.pows.Ok) : ∀ (ss : List Stmt) {st st' : HSt} {W : K → Prop}, (∀ c ∈ H.sig.pre, W (c.addr σ)) →
    chkL X ss st = some st' → EnvOk σ st.env → ScOk W σ st.sc → BlockOk H σ rd W (walk σ ss) st'
  | [], st, st', W, _, h, he, hs => by
    simp only [chkL, Option.some.injEq] at h
    subst h
    refine ⟨fun es hw _ ↦ ?_, fun es vs hw _ ↦ by simp [walk] at hw⟩
    simp only [walk, Out.fall.injEq] at hw
    subst hw
    exact ⟨cov_nil W, he, hs.mono fun _ ↦ Or.inl⟩
  | .atom a :: ss, st, st', W, hpre, h, he, hs => by
    simp only [chkL] at h
    cases ha : atomH X st a with
    | none => rw [ha] at h; exact absurd h (by simp)
    | some st1 =>
      rw [ha] at h
      simp only [HSt.seq_eq] at h
      rw [walk]
      refine blockOk_seq (W1 := fun _ x ↦ W x ∨ Writes σ a x) ?_ fun es hw hh ↦ ?_
      · rintro es vs (hw | hw) hh
        · simp only [walk1, Out.fall.injEq] at hw
          subst hw
          exact cov_atom (atomH_ok hR hP hpows hpre ha he hs (hh _ List.mem_cons_self)).1
        · simp [walk1] at hw
      · simp only [walk1, Out.fall.injEq] at hw
        subst hw
        obtain ⟨-, he1, hs1⟩ := atomH_ok hR hP hpows hpre ha he hs (hh _ List.mem_cons_self)
        exact ⟨fun x hx ↦ hx.imp_right fun hx ↦ ⟨a, List.mem_singleton_self _, hx⟩,
          chkL_ok hR hP hpows ss (fun c hc ↦ Or.inl (hpre c hc)) h he1 hs1⟩
  | .ite c z n :: ss, st, st', W, hpre, h, he, hs => by
    simp only [chkL] at h
    cases h1 : chkL X z st with
    | none => rw [h1] at h; exact absurd h (by simp)
    | some s1 =>
      simp only [h1] at h
      cases h2 : chkL X n (st.withN s1.n) with
      | none => simp [h2] at h
      | some s2 =>
        simp only [h2, HSt.seq_eq] at h
        rw [walk]
        refine blockOk_seq (W1 := fun _ ↦ W) ?_ fun es _ _ ↦
          ⟨fun x hx ↦ Or.inl hx, chkL_ok hR hP hpows ss hpre h he hs⟩
        simp only [walk1]
        refine covers_inK ?_ c
        by_cases hc : σ c = 0
        · rw [ite_eq_left hc]
          exact (chkL_ok hR hP hpows z hpre h1 he hs).covers
        · rw [ite_eq_right hc]
          exact (chkL_ok hR hP hpows n hpre h2 he hs).covers
  | .match_ x arms :: ss, st, st', W, hpre, h, he, hs => by
    simp only [chkL] at h
    cases h1 : chkArms X arms st with
    | none => rw [h1] at h; exact absurd h (by simp)
    | some m =>
      rw [h1] at h
      simp only [HSt.seq_eq] at h
      rw [walk]
      exact blockOk_seq (W1 := fun _ ↦ W) (chkArms_ok hR hP hpows arms hpre h1 he hs x 0) fun es _ _ ↦
        ⟨fun x hx ↦ Or.inl hx, chkL_ok hR hP hpows ss hpre h he hs⟩
  | .ret vs :: ss, st, st', W, _, h, _, _ => by
    simp only [chkL, Option.some.injEq] at h
    subst h
    refine ⟨fun es hw _ ↦ by simp [walk, walk1, Out.seq] at hw, fun es vs' hw _ ↦ ?_⟩
    simp only [walk, walk1, Out.seq, Out.ret.injEq] at hw
    obtain ⟨rfl, -⟩ := hw
    exact cov_nil W
  | .call .. :: _, _, _, _, _, h, _, _ => by simp [chkL] at h
  | .callIf .. :: _, _, _, _, _, h, _, _ => by simp [chkL] at h
  | .dispatch .. :: _, _, _, _, _, h, _, _ => by simp [chkL] at h

/-- **The pass over the arms, on the path**: the arm a `match` takes is covered. -/
theorem chkArms_ok (hR : X.R = H.readT) (hP : ∀ k c, getF X.pre k = some c → c ∈ H.sig.pre)
    (hpows : X.pows.Ok) : ∀ (arms : List (List Stmt)) {st : HSt} {m : ℕ} {W : K → Prop},
    (∀ c ∈ H.sig.pre, W (c.addr σ)) → chkArms X arms st = some m → EnvOk σ st.env → ScOk W σ st.sc →
    ∀ x j, Covers H σ rd W (walkArms σ x j arms)
  | [], _, _, _, _, _, _, _, x, j => by
    rintro es vs (hw | hw) <;> simp [walkArms] at hw
  | a :: as, st, m, W, hpre, h, he, hs, x, j => by
    simp only [chkArms] at h
    cases h1 : chkL X a st with
    | none => rw [h1] at h; exact absurd h (by simp)
    | some s1 =>
      rw [h1] at h
      rw [walkArms]
      split_ifs
      · exact (chkL_ok hR hP hpows a hpre h1 he hs).covers
      · exact chkArms_ok hR hP hpows as hpre h he hs x (j + 1)
end

end Blocks

/-! ## The function -/

/-- **The heap check is sound**: on a path of a function passing `heapOk` that returns, every
event holding, each address an atom reads is a precondition's or written by an atom before it. -/
theorem heapOk_sound {pows : PowTree} (hp : pows.Ok) {sigOf : String → HSig} {f : Fn} {H : HCert}
    (hok : heapOk pows sigOf f H = true) {σ : Val} {rd : Reader} {es : List Ev} {vs : List V}
    (hw : walk σ f.body = .ret es vs) (hh : ∀ e ∈ es, e.Holds rd σ) : ReadsWritten H σ es := by
  unfold heapOk at hok
  simp only [Bool.and_eq_true] at hok
  obtain ⟨-, hc⟩ := hok
  rw [Trie.seq_eq, Trie.seq_eq] at hc
  obtain ⟨st', hst⟩ := Option.isSome_iff_exists.mp hc
  have hb := chkL_ok (X := ⟨pows, H.readT, trieFrom H.sig.pre 0 .nil⟩) (H := H) (rd := rd) rfl
    (fun k c h ↦ (getF_trieFrom _ _ _ h).resolve_right (by simp [getF_nil])) hp f.body
    (W := fun x ↦ ∃ c ∈ H.sig.pre, c.addr σ = x) (fun c hc ↦ ⟨c, hc, rfl⟩) hst envOk_nil
    (fun n c h ↦ by simp [getF_nil] at h)
  intro es1 a es2 x he hr
  exact hb.2 es vs hw hh es1 a es2 x he hr

/-! ## The signature -/

theorem paramsN_eq : ∀ (vs : List V) (i : ℕ), paramsN vs i = true → vs = (List.range' i vs.length).map V.n
  | [], _, _ => rfl
  | v :: vs, i, h => by
    simp only [paramsN, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    cases hv : vnum v with
    | none => rw [hv] at h1; simp at h1
    | some k =>
      rw [hv] at h1
      rw [List.length_cons, List.range'_succ, List.map_cons, vnum_eq hv, Nat.eq_of_beq_eq_true h1,
        ← paramsN_eq vs (i + 1) h2]

end

end LeanVM.Guest.CoreMode
