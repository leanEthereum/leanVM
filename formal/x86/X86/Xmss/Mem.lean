module

public import X86.Keccak.Spec
public import X86.Xmss.Code
public import X86.Xmss.Model

/-!
# The context's words, and steps through the code

The proofs of `XmssVerifier.body` name the context's words by index (`wd b k`, word `k` from the
base `b`), read every address of the code in that form (`eval_ctx`, `eval_ctxAt`, `eval_sigAt`), and
step through blocks instruction by instruction (`WP.load'`, `WP.store'`, `WP.storei'`, `WP.reg'`).
`hash_call` is `Keccak.hash_spec` on words of the context, `MemFrame` the words a statement may
write.
-/

@[expose] public section

namespace X86.XmssVerifier

open Keccak

/-! ## Words of the context -/

/-- The address of the context's word `k`. -/
def wd (b : UInt64) (k : Nat) : UInt64 := b + (8 * k).toUInt64

/-- Every word of the context is in memory. -/
def Dom (b : UInt64) (mem : UInt64 → Option UInt64) : Prop :=
  ∀ k < Context.ctxWords, (mem (wd b k)).isSome

/-- The words of the context outside `W` and the scratch area are unchanged, and every word stays in
memory. -/
def MemFrame (b : UInt64) (W : Nat → Prop) (s s' : QState) : Prop :=
  Dom b s'.mem ∧
    ∀ k, scratchWords ≤ k → k < Context.ctxWords → ¬ W k → s'.mem (wd b k) = s.mem (wd b k)

theorem wd_inj {b : UInt64} {k k' : Nat} (hk : k < 2 ^ 61) (hk' : k' < 2 ^ 61) :
    wd b k = wd b k' ↔ k = k' := by
  unfold wd
  rw [UInt64.add_right_inj]
  constructor
  · intro e
    have := congrArg UInt64.toNat e
    simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat'] at this
    omega
  · rintro rfl
    rfl

theorem wd_add (b : UInt64) (k j : Nat) : wd b k + (8 * j).toUInt64 = wd b (k + j) := by
  simp only [wd, Nat.toUInt64_eq, Nat.mul_add, UInt64.ofNat_add, UInt64.add_assoc]

theorem setMem_wd (s : QState) {b : UInt64} {k k' : Nat} (v : UInt64) (hk : k < 2 ^ 61)
    (hk' : k' < 2 ^ 61) :
    (s.setMem (wd b k) v).mem (wd b k') = if k' = k then some v else s.mem (wd b k') := by
  rw [QState.setMem_mem]
  simp only [wd_inj hk' hk]

theorem Dom.setMem {b : UInt64} {s : QState} (h : Dom b s.mem) (a v : UInt64) :
    Dom b (s.setMem a v).mem := fun k hk ↦ by
  rw [QState.setMem_mem]
  split
  · rfl
  · exact h k hk

theorem Dom.setReg {b : UInt64} {s : QState} (h : Dom b s.mem) (r : Reg64) (v : UInt64) :
    Dom b (s.setReg r v).mem := h

theorem Dom.isSome {b : UInt64} {mem : UInt64 → Option UInt64} (h : Dom b mem) (k : Nat)
    (hk : k < Context.ctxWords := by decide) : (mem (wd b k)).isSome := h k hk

theorem MemFrame.refl {b : UInt64} {W : Nat → Prop} {s : QState} (h : Dom b s.mem) :
    MemFrame b W s s := ⟨h, fun _ _ _ _ ↦ rfl⟩

theorem MemFrame.trans {b : UInt64} {W W' W'' : Nat → Prop} {s₁ s₂ s₃ : QState}
    (h : MemFrame b W s₁ s₂) (h' : MemFrame b W' s₂ s₃) (hW : ∀ k, W k ∨ W' k → W'' k) :
    MemFrame b W'' s₁ s₃ :=
  ⟨h'.1, fun k h1 h2 h3 ↦ (h'.2 k h1 h2 fun hk ↦ h3 (hW k (.inr hk))).trans
    (h.2 k h1 h2 fun hk ↦ h3 (hW k (.inl hk)))⟩

theorem MemFrame.mono {b : UInt64} {W W' : Nat → Prop} {s s' : QState} (h : MemFrame b W s s')
    (hW : ∀ k, W k → W' k) : MemFrame b W' s s' :=
  ⟨h.1, fun k h1 h2 h3 ↦ h.2 k h1 h2 fun hk ↦ h3 (hW k hk)⟩

theorem MemFrame.setReg {b : UInt64} {W : Nat → Prop} {s s' : QState} (h : MemFrame b W s s')
    (r : Reg64) (v : UInt64) : MemFrame b W s (s'.setReg r v) := h

theorem MemFrame.of_setReg {b : UInt64} {W : Nat → Prop} {s s' : QState} {r : Reg64}
    {v : UInt64} (h : MemFrame b W (s.setReg r v) s') : MemFrame b W s s' := h

theorem MemFrame.setMem {b : UInt64} {W : Nat → Prop} {s s' : QState} (h : MemFrame b W s s')
    {k : Nat} (hk : W k) (hk' : k < Context.ctxWords) (v : UInt64) :
    MemFrame b W s (s'.setMem (wd b k) v) :=
  ⟨h.1.setMem _ _, fun k' h1 h2 h3 ↦ by
    rw [setMem_wd _ _ (by unfold Context.ctxWords at hk'; omega)
      (by unfold Context.ctxWords at h2; omega)]
    split
    · subst k'
      exact absurd hk h3
    · exact h.2 k' h1 h2 h3⟩

/-- A word of the context unchanged by a frame that does not write it. -/
theorem MemFrame.get {b : UInt64} {W : Nat → Prop} {s s' : QState} (h : MemFrame b W s s')
    {k : Nat} (h1 : scratchWords ≤ k) (h2 : k < Context.ctxWords) (h3 : ¬ W k) :
    s'.mem (wd b k) = s.mem (wd b k) := h.2 k h1 h2 h3

/-! ## Addresses of the code -/

theorem wdisp_toUInt64 (k : Nat) : (wdisp k).toUInt64 = (8 * k).toUInt64 := (rfl)

theorem eval_ctx (s : QState) (k : Nat) : (ctx k).eval s = wd (s.reg .rdi) k := by
  simp [Addr.eval, ctx, at_, wd, wdisp_toUInt64]

theorem eval_ctxAt {s : QState} {j : Nat} (hrax : s.reg .rax = (8 * j).toUInt64) (k : Nat) :
    (ctxAt k).eval s = wd (s.reg .rdi) (j + k) := by
  simp only [Addr.eval, ctxAt, wdisp_toUInt64, hrax]
  rw [show Width.W8.bytes.toUInt64 = 1 from rfl, UInt64.mul_one]
  rw [← wd_add (s.reg .rdi) j k]
  rfl

theorem eval_sigAt {s : QState} {b : UInt64} {K j : Nat} (hr14 : s.reg .r14 = wd b K)
    (hrax : s.reg .rax = (8 * j).toUInt64) (k : Nat) : (sigAt k).eval s = wd b (K + j + k) := by
  simp only [Addr.eval, sigAt, wdisp_toUInt64, hrax, hr14]
  rw [show Width.W8.bytes.toUInt64 = 1 from rfl, UInt64.mul_one, wd_add, wd_add]

theorem eval_r14 {s : QState} {b : UInt64} {K : Nat} (hr14 : s.reg .r14 = wd b K) :
    (at_ .r14 0).eval s = wd b K ∧ (at_ .r14 8).eval s = wd b (K + 1) := by
  refine ⟨?_, ?_⟩
  · simp only [Addr.eval, at_, hr14, UInt64.add_zero]
    exact UInt64.add_zero _
  · simp only [Addr.eval, at_, hr14, UInt64.add_zero]
    exact wd_add b K 1

theorem eval_rdi (s : QState) {d : Int64} {k : Nat} (h : d.toUInt64 = (8 * k).toUInt64) :
    (at_ .rdi d).eval s = wd (s.reg .rdi) k := by
  simp [Addr.eval, at_, wd, h]

/-! ## The code's word indices -/

theorem bufA_val : bufA = 1152 := (rfl)
theorem bufL_val : bufL = 1168 := (rfl)
theorem dhiW_val : dhiW = 1162 := (rfl)
theorem inputW_val : inputW = 128 := (rfl)
theorem ctxWords_val : Context.ctxWords = 3200 := (rfl)
theorem scratchWords_val : scratchWords = 84 := (rfl)

/-! ## Literals -/

theorem natLit_toUInt64 (n : Nat) [n.AtLeastTwo] :
    (no_index (OfNat.ofNat n : Nat)).toUInt64 = (OfNat.ofNat n : UInt64) := (rfl)

theorem natOne_toUInt64 : (1 : Nat).toUInt64 = 1 := (rfl)

theorem int64Lit_toUInt64 (n : Nat) :
    (no_index (OfNat.ofNat n : Int64)).toUInt64 = (OfNat.ofNat n : UInt64) := (rfl)

/-! ## Counters -/

theorem toUInt64_add_one (t : Nat) : t.toUInt64 + 1 = (t + 1).toUInt64 := by
  simp [Nat.toUInt64_eq, UInt64.ofNat_add]

theorem toNat_toUInt64 {t : Nat} (h : t < 2 ^ 64) : t.toUInt64.toNat = t := by
  simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat']
  omega

theorem toUInt64_lt_iff {t n : Nat} (ht : t < 2 ^ 64) (hn : n < 2 ^ 64) :
    t.toUInt64 < n.toUInt64 ↔ t < n := by
  rw [UInt64.lt_iff_toNat_lt, toNat_toUInt64 ht, toNat_toUInt64 hn]

theorem toUInt64_eq_iff {t n : Nat} (ht : t < 2 ^ 64) (hn : n < 2 ^ 64) :
    t.toUInt64 = n.toUInt64 ↔ t = n := by
  rw [← UInt64.toNat_inj, toNat_toUInt64 ht, toNat_toUInt64 hn]

theorem shiftRight_toUInt64_add (x : UInt64) {a c : Nat} (h : a + c < 64) :
    x >>> a.toUInt64 >>> c.toUInt64 = x >>> (a + c).toUInt64 := by
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_shiftRight, toNat_toUInt64 (show a < 2 ^ 64 by omega),
    toNat_toUInt64 (show c < 2 ^ 64 by omega), toNat_toUInt64 (show a + c < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (show a < 64 by omega),
    Nat.mod_eq_of_lt (show c < 64 by omega), Nat.shiftRight_add]

/-- `16 i`, the offset of digest `i`, by a shift. -/
theorem toUInt64_shl4 {i : Nat} (h : i < 2 ^ 59) :
    i.toUInt64 <<< 4 = (8 * (2 * i)).toUInt64 := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_shiftLeft, toNat_toUInt64 (by omega), toNat_toUInt64 (by omega)]
  simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftLeft_eq]
  omega

/-! ## Register frames -/

theorem rf_trans {l l' l'' : List Reg64} {s₁ s₂ s₃ : QState} (h : RegsFrame l s₁ s₂)
    (h' : RegsFrame l' s₂ s₃) (hl : l ⊆ l'' := by simp) (hl' : l' ⊆ l'' := by simp) :
    RegsFrame l'' s₁ s₃ :=
  fun r hr ↦ (h' r fun h ↦ hr (hl' h)).trans (h r fun h ↦ hr (hl h))

theorem rf_setReg {l : List Reg64} {s s' : QState} (h : RegsFrame l s s') {r : Reg64} (hr : r ∈ l)
    (v : UInt64) : RegsFrame l s (s'.setReg r v) := fun r' hr' ↦ by
  rw [QState.setReg_reg]
  split
  · subst r'
    exact absurd hr hr'
  · exact h r' hr'

theorem rf_setMem {l : List Reg64} {s s' : QState} (h : RegsFrame l s s') (a v : UInt64) :
    RegsFrame l s (s'.setMem a v) := h

theorem rf_refl (l : List Reg64) (s : QState) : RegsFrame l s s := fun _ _ ↦ rfl

theorem rf_mono {l l' : List Reg64} {s s' : QState} (h : RegsFrame l s s') (hl : l ⊆ l') :
    RegsFrame l' s s' :=
  fun r hr ↦ h r fun h ↦ hr (hl h)

/-! ## Steps through a block -/

variable {s : QState} {P E : QState → Prop} {xs : List Stmt}

theorem WP.reg' {i : QInstr} {s' : QState} (hs : i.step s = some s') (h : WP (blk xs) s' P E) :
    WP (blk (I i :: xs)) s P E :=
  WP.blk_cons (WP.ins hs h)

theorem WP.load' {d : Reg64} {a : Addr} {b : UInt64} {k : Nat} {v : UInt64}
    (ha : a.eval s = wd b k) (hv : s.mem (wd b k) = some v) (h : WP (blk xs) (s.setReg d v) P E) :
    WP (blk (I (.load d a) :: xs)) s P E :=
  WP.reg' (by simp [QInstr.step, ha, hv]) h

theorem WP.store' {a : Addr} {r : Reg64} {b : UInt64} {k : Nat} (ha : a.eval s = wd b k)
    (hd : (s.mem (wd b k)).isSome) (h : WP (blk xs) (s.setMem (wd b k) (s.reg r)) P E) :
    WP (blk (I (.store a r) :: xs)) s P E := by
  refine WP.reg' ?_ h
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hd
  simp [QInstr.step, ha, hv]

theorem WP.storei' {a : Addr} {n : Int64} {b : UInt64} {k : Nat} (ha : a.eval s = wd b k)
    (hd : (s.mem (wd b k)).isSome) (h : WP (blk xs) (s.setMem (wd b k) n.toUInt64) P E) :
    WP (blk (I (.storei a n) :: xs)) s P E := by
  refine WP.reg' ?_ h
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hd
  simp [QInstr.step, ha, hv]

/-- A statement by its specification, then the rest of the block. -/
theorem WP.then {x : Stmt} {Q : QState → Prop} (h : WP x s Q E)
    (k : ∀ s₁, Q s₁ → WP (blk xs) s₁ P E) : WP (blk (x :: xs)) s P E :=
  WP.blk_cons (WP.mono h k fun _ h ↦ h)

theorem WP.ite_true {c : Cond} {t e : Stmt} (hc : c.eval s = true) (h : WP t s P E) :
    WP (.ite c t e) s P E :=
  WP.ite (by rw [hc]; exact h)

theorem WP.ite_false {c : Cond} {t e : Stmt} (hc : c.eval s = false) (h : WP e s P E) :
    WP (.ite c t e) s P E :=
  WP.ite (by rw [hc]; exact h)

/-! ## The hash -/

/-- The words `ws` at word `k0` of the context. -/
def WordsIn (b : UInt64) (mem : UInt64 → Option UInt64) (k0 : Nat) (ws : List UInt64) : Prop :=
  ∀ i (h : i < ws.length), mem (wd b (k0 + i)) = some ws[i]

theorem wordsIn_nil (b : UInt64) (mem : UInt64 → Option UInt64) (k : Nat) : WordsIn b mem k [] :=
  fun _ h ↦ absurd h (by simp)

theorem wordsIn_cons {b : UInt64} {mem : UInt64 → Option UInt64} {k : Nat} {w : UInt64}
    {ws : List UInt64} :
    WordsIn b mem k (w :: ws) ↔ mem (wd b k) = some w ∧ WordsIn b mem (k + 1) ws := by
  constructor
  · intro h
    refine ⟨?_, fun i hi ↦ ?_⟩
    · have := h 0 (by simp)
      simp only [Nat.add_zero, List.getElem_cons_zero] at this
      exact this
    have := h (i + 1) (by simp; omega)
    rwa [show k + (i + 1) = k + 1 + i by omega] at this
  · rintro ⟨h0, h⟩ i hi
    cases i with
    | zero =>
      simp only [Nat.add_zero, List.getElem_cons_zero]
      exact h0
    | succ i =>
      have := h i (by simp at hi; omega)
      rwa [show k + 1 + i = k + (i + 1) by omega] at this

theorem wordsIn_append {b : UInt64} {mem : UInt64 → Option UInt64} {k : Nat}
    {xs ys : List UInt64} :
    WordsIn b mem k (xs ++ ys) ↔ WordsIn b mem k xs ∧ WordsIn b mem (k + xs.length) ys := by
  induction xs generalizing k with
  | nil => simp [wordsIn_nil]
  | cons x xs ih =>
    rw [List.cons_append, wordsIn_cons, wordsIn_cons, ih, List.length_cons,
      show k + 1 + xs.length = k + (xs.length + 1) by omega, and_assoc]

theorem pairWords_succ (n : Nat) (f : Nat → W2) :
    pairWords (n + 1) f = pairWords n f ++ [(f n).1, (f n).2] := by
  simp [pairWords, List.range_succ, List.flatMap_append]

theorem pairWords_length (n : Nat) (f : Nat → W2) : (pairWords n f).length = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pairWords_succ, List.length_append, ih]
    simp
    omega

theorem wordsIn_pairWords {b : UInt64} {mem : UInt64 → Option UInt64} {k n : Nat}
    {f : Nat → W2} (h : ∀ c < n, mem (wd b (k + 2 * c)) = some (f c).1 ∧
      mem (wd b (k + 2 * c + 1)) = some (f c).2) :
    WordsIn b mem k (pairWords n f) := by
  induction n with
  | zero => exact wordsIn_nil _ _ _
  | succ n ih =>
    rw [pairWords_succ, wordsIn_append, pairWords_length]
    refine ⟨ih fun c hc ↦ h c (by omega), ?_⟩
    simp only [wordsIn_cons]
    exact ⟨(h n (by omega)).1, (h n (by omega)).2, wordsIn_nil _ _ _⟩

theorem wordsBytes_length (ws : List UInt64) : (wordsBytes ws).length = 8 * ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [wordsBytes, List.flatMap_cons, List.length_append] at ih ⊢
    rw [ih]
    simp [LeanVM.Protocol.KeccakHash.wordBytes]
    omega

/-- `Keccak.hash` of the words `ws` at word `k0` of the context, from `rdi` at the context's base:
the digest's first two lanes in scratch words `0` and `1`. -/
theorem hash_call {b : UInt64}
    (hrdi : s.reg .rdi = b) (hdom : Dom b s.mem) {k0 : Nat} {ws : List UInt64}
    (hk0 : scratchWords ≤ k0) (hk : k0 + ws.length ≤ Context.ctxWords) (hrsi : s.reg .rsi = wd b k0)
    (hrbx : s.reg .rbx = (8 * ws.length).toUInt64) (hws : WordsIn b s.mem k0 ws) :
    WP Keccak.hash s (fun s' ↦ s'.mem (wd b 0) = some (hashW ws).1 ∧
      s'.mem (wd b 1) = some (hashW ws).2 ∧ MemFrame b (fun _ ↦ False) s s' ∧
      RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8] s s') E := by
  unfold Context.ctxWords at hk
  unfold scratchWords at hk0
  have hlen : ws.length < 2 ^ 32 := by omega
  have hb : HoldsBytes ws (8 * ws.length) := by
    refine ⟨by omega, fun x hx ↦ ?_⟩
    rw [List.drop_eq_nil_of_le (by rw [wordsBytes_length])] at hx
    cases hx
  have hspec := hash_spec (E := E) hb hrbx (by omega)
    (by
      intro i hi
      rw [hrsi, wd_add]
      exact hws i hi)
    (by
      intro k hk'
      rw [hrdi]
      exact hdom k (by unfold Context.ctxWords scratchWords at *; omega))
    (by
      intro i hi k hk'
      rw [hrsi, hrdi, wd_add]
      unfold scratchWords at hk'
      exact fun e ↦ by
        have := (wd_inj (b := b) (by omega) (by omega)).mp e
        omega)
  refine WP.mono hspec ?_ fun _ h ↦ h
  rintro s' ⟨h1, h2, h3, h4⟩
  rw [hrdi] at h1 h2 h3
  rw [List.take_of_length_le (by rw [wordsBytes_length])] at h1
  refine ⟨h1 0 (by decide), h1 1 (by decide), ⟨fun k hk' ↦ ?_, fun k hk1 hk2 _ ↦ ?_⟩, h4⟩
  · by_cases hks : k < scratchWords
    · exact h2 k hks
    · rw [h3 _ fun k' hk'' e ↦ ?_]
      · exact hdom k hk'
      · have := (wd_inj (b := b) (by unfold Context.ctxWords at hk'; omega)
          (by unfold scratchWords at hk''; omega)).mp e
        unfold scratchWords at hks hk''
        omega
  · rw [h3 _ fun k' hk' e ↦ ?_]
    have := (wd_inj (b := b) (by unfold Context.ctxWords at hk2; omega)
      (by unfold scratchWords at hk'; omega)).mp e
    unfold scratchWords at hk1 hk'
    omega

/-- Run the register instruction at the head of a block, reading registers through the updates
(rewriting with the given facts). -/
syntax "rstep" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| rstep) => `(tactic| (
      refine WP.reg' rfl ?_
      try simp only [QState.setReg_reg, reduceCtorEq, ite_true, ite_false, ↓reduceIte,
        int64Lit_toUInt64, natLit_toUInt64, natOne_toUInt64]))
  | `(tactic| rstep [$ls,*]) => `(tactic| (
      refine WP.reg' rfl ?_
      try simp only [QState.setReg_reg, reduceCtorEq, ite_true, ite_false, ↓reduceIte,
        int64Lit_toUInt64, natLit_toUInt64, natOne_toUInt64, $ls,*]))

/-- Every word of the context stays in memory through register and memory updates. -/
macro "dom_tac" : tactic => `(tactic| (
  repeat (first | with_reducible refine Dom.setMem ?_ _ _ | with_reducible refine Dom.setReg ?_ _ _)
  with_reducible assumption))

/-- A word of the context is in memory, through register and memory updates. -/
macro "isSome_tac" : tactic => `(tactic| (
  refine Dom.isSome ?_ _ ?_
  · dom_tac
  · first | decide | (rw [ctxWords_val]; omega)))

/-- Peel register and memory updates off a `MemFrame` goal, leaving the frame of the state below
and, for each store, that its word is in the frame and in the context. -/
macro "frame_tac" : tactic => `(tactic| (
  repeat (first
    | with_reducible refine MemFrame.setReg ?_ _ _
    | with_reducible refine MemFrame.setMem ?_ ?_ ?_ _)))

/-- Peel register and memory updates off a `RegsFrame` goal, each register written in the frame. -/
macro "rf_tac" : tactic => `(tactic| (
  repeat (first
    | with_reducible refine rf_setMem ?_ _ _
    | with_reducible refine rf_setReg ?_ (by simp) _)))

/-- Read memory through updates of the context's words. -/
syntax "mem_simp" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| mem_simp) => `(tactic|
      simp (disch := omega) only [QState.setReg_mem, QState.setMem_mem, QState.setReg_reg,
        QState.setMem_reg,
        reduceCtorEq, wd_inj, bufA_val,
        bufL_val, dhiW_val, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte, ite_true, ite_false,
        int64Lit_toUInt64])
  | `(tactic| mem_simp [$ls,*]) => `(tactic|
      simp (disch := omega) only [QState.setReg_mem, QState.setMem_mem, QState.setReg_reg,
        QState.setMem_reg,
        reduceCtorEq, wd_inj, bufA_val,
        bufL_val, dhiW_val, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte, ite_true, ite_false,
        int64Lit_toUInt64, $ls,*])

end X86.XmssVerifier
