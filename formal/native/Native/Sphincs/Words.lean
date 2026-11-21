module

public import Native.Sphincs.Code
public import Native.Keccak.Spec
public import Native.Frame

/-!
# The context as words

`Inv base V s`: `rdi` is at the context, whose word `k` is `V k`. A load or a store at a context
word reads or updates `V` (`wp_load`, `wp_store`), and `Keccak.hash` of words of the context
changes only the scratch words, leaving the digest in words `0` to `3` (`hash_ok`).
-/

@[expose] public section

namespace Native.SphincsVerifier

open Keccak LeanVM.Protocol.KeccakHash

/-- `rdi` is at the context, whose word `k` is `V k`. -/
structure Inv (base : UInt64) (V : Nat → UInt64) (s : QState) : Prop where
  rdi : s.reg .rdi = base
  mem : ∀ k < Context.ctxWords, s.mem (base + (8 * k).toUInt64) = some (V k)

/-- The context fits below `2^64`. -/
def Fits (base : UInt64) : Prop := base.toNat + 8 * Context.ctxWords ≤ 2 ^ 64

/-- The `n` words from `j`. -/
def words (V : Nat → UInt64) (j n : Nat) : List UInt64 := (List.range n).map fun i ↦ V (j + i)

theorem words_length (V : Nat → UInt64) (j n : Nat) : (words V j n).length = n := by simp [words]

theorem words_getElem (V : Nat → UInt64) (j n i : Nat) (h : i < (words V j n).length) :
    (words V j n)[i] = V (j + i) := by simp [words]

theorem words_congr {V V' : Nat → UInt64} {j n : Nat} (h : ∀ i < n, V' (j + i) = V (j + i)) :
    words V' j n = words V j n := by
  simp only [words, List.map_inj_left, List.mem_range]
  exact h

theorem words_add (V : Nat → UInt64) (j n m : Nat) :
    words V j (n + m) = words V j n ++ words V (j + n) m := by
  simp only [words, List.range_add, List.map_append, List.map_map]
  congr 1
  simp only [List.map_inj_left]
  intro i _
  simp [Nat.add_assoc]

theorem words_succ (V : Nat → UInt64) (j n : Nat) : words V j (n + 1) = V j :: words V (j + 1) n := by
  simp only [words, List.range_succ_eq_map, List.map_cons, List.map_map, Nat.add_zero]
  congr 1
  simp only [List.map_inj_left]
  intro i _
  simp [Function.comp, Nat.add_assoc, Nat.add_comm 1]

theorem words_zero (V : Nat → UInt64) (j : Nat) : words V j 0 = [] := rfl

theorem words_one (V : Nat → UInt64) (j : Nat) : words V j 1 = [V j] := rfl

theorem ite_no {α : Type} {c : Prop} [Decidable c] (h : ¬c) {a b : α} :
    (if c then a else b) = b := by simp [h]

theorem ite_yes {α : Type} {c : Prop} [Decidable c] (h : c) {a b : α} :
    (if c then a else b) = a := by simp [h]

theorem dite_no {α : Type} {c : Prop} [Decidable c] (h : ¬c) {a : c → α} {b : ¬c → α} :
    dite c a b = b h := by simp [h]

theorem dite_yes {α : Type} {c : Prop} [Decidable c] (h : c) {a : c → α} {b : ¬c → α} :
    dite c a b = a h := by simp [h]

/-! ## Addresses -/

theorem toInt64_toUInt64 (n : Nat) : n.toInt64.toUInt64 = n.toUInt64 := Int64.toUInt64_ofNat'

theorem ctx_inj {base : UInt64} {j k : Nat} (hj : j < Context.ctxWords) (hk : k < Context.ctxWords)
    (h : base + (8 * j).toUInt64 = base + (8 * k).toUInt64) : j = k := by
  have h' := congrArg UInt64.toNat ((UInt64.add_right_inj base).mp h)
  simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat'] at h'
  unfold Context.ctxWords at hj hk
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h'
  omega

theorem cw_eval (s : QState) (k : Nat) : (cw k).eval s = s.reg .rdi + (8 * k).toUInt64 := by
  simp only [cw, at_, Addr.eval, UInt64.add_zero, toInt64_toUInt64]

theorem cwi_eval (s : QState) {r : Reg64} {n : Nat} (hr : s.reg r = n.toUInt64) (k : Nat) :
    (cwi r k).eval s = s.reg .rdi + (8 * (n + k)).toUInt64 := by
  simp only [cwi, Addr.eval, Width.bytes, hr, toInt64_toUInt64]
  simp only [Nat.toUInt64_eq, Nat.mul_add, UInt64.ofNat_add, UInt64.ofNat_mul, UInt64.add_assoc]
  congr 1
  rw [UInt64.mul_comm]

/-! ## Numbers in registers -/

theorem toNat_toUInt64' {n : Nat} (h : n < 2 ^ 64) : n.toUInt64.toNat = n := by
  simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt h

/-- An immediate literal as a word. -/
theorem imm_nat (k : Nat) : (OfNat.ofNat k : Int64).toUInt64 = k.toUInt64 := Int64.toUInt64_ofNat'

theorem toUInt64_inj {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (h : a.toUInt64 = b.toUInt64) : a = b := by
  have := congrArg UInt64.toNat h
  rwa [toNat_toUInt64' ha, toNat_toUInt64' hb] at this

theorem toUInt64_add (a b : Nat) : a.toUInt64 + b.toUInt64 = (a + b).toUInt64 := by
  simp only [Nat.toUInt64_eq, UInt64.ofNat_add]

theorem toUInt64_sub {a b : Nat} (h : b ≤ a) : a.toUInt64 - b.toUInt64 = (a - b).toUInt64 := by
  rw [show a = (a - b) + b by omega, ← toUInt64_add, UInt64.add_sub_cancel, Nat.add_sub_cancel]

theorem toUInt64_shl {a n : Nat} (hn : n < 64) (h : a * 2 ^ n < 2 ^ 64) :
    a.toUInt64 <<< n.toUInt64 = (a * 2 ^ n).toUInt64 := by
  have ha : a < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)) h
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_shiftLeft, toNat_toUInt64' ha, toNat_toUInt64' (show n < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt hn, toNat_toUInt64' h, Nat.shiftLeft_eq, Nat.mod_eq_of_lt h]

theorem toUInt64_shr {a n : Nat} (hn : n < 64) (ha : a < 2 ^ 64) :
    a.toUInt64 >>> n.toUInt64 = (a / 2 ^ n).toUInt64 := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_shiftRight, toNat_toUInt64' ha, toNat_toUInt64' (by omega), Nat.mod_eq_of_lt hn,
    toNat_toUInt64' (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ha), Nat.shiftRight_eq_div_pow]

theorem toUInt64_and_mask {a k : Nat} (hk : k < 64) (ha : a < 2 ^ 64) :
    a.toUInt64 &&& (2 ^ k - 1 : Nat).toUInt64 = (a % 2 ^ k).toUInt64 := by
  apply UInt64.toNat_inj.mp
  have hk' : 2 ^ k < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hk
  rw [UInt64.toNat_and, toNat_toUInt64' ha, toNat_toUInt64' (by omega),
    toNat_toUInt64' (Nat.lt_of_le_of_lt (Nat.mod_le _ _) ha), Nat.and_two_pow_sub_one_eq_mod]

/-- An unsigned comparison of a register holding `n` with an immediate `k`. -/
theorem cond_ltu_imm {s : QState} {r : Reg64} {n K : Nat} {k : Int64} (hr : s.reg r = n.toUInt64)
    (hk : k.toUInt64 = K.toUInt64) (hn : n < 2 ^ 64) (hK : K < 2 ^ 64) :
    (Cond.cmp .ltu r (.imm k)).eval s = decide (n < K) := by
  simp only [Cond.eval, Rhs.eval, hr, hk, decide_eq_decide]
  rw [UInt64.lt_iff_toNat_lt, toNat_toUInt64' hn, toNat_toUInt64' hK]

theorem cond_ltu_reg {s : QState} {r r' : Reg64} {n K : Nat} (hr : s.reg r = n.toUInt64)
    (hk : s.reg r' = K.toUInt64) (hn : n < 2 ^ 64) (hK : K < 2 ^ 64) :
    (Cond.cmp .ltu r (.reg r')).eval s = decide (n < K) := by
  simp only [Cond.eval, Rhs.eval, hr, hk, decide_eq_decide]
  rw [UInt64.lt_iff_toNat_lt, toNat_toUInt64' hn, toNat_toUInt64' hK]

theorem cond_eq_imm {s : QState} {r : Reg64} {n K : Nat} {k : Int64} (hr : s.reg r = n.toUInt64)
    (hk : k.toUInt64 = K.toUInt64) (hn : n < 2 ^ 64) (hK : K < 2 ^ 64) :
    (Cond.cmp .eq r (.imm k)).eval s = decide (n = K) := by
  simp only [Cond.eval, Rhs.eval, hr, hk]
  by_cases h : n = K
  · subst h; simp
  · simp only [h, decide_false]
    exact beq_false_of_ne fun h' ↦ h (toUInt64_inj hn hK h')

theorem cond_ne_imm {s : QState} {r : Reg64} {n K : Nat} {k : Int64} (hr : s.reg r = n.toUInt64)
    (hk : k.toUInt64 = K.toUInt64) (hn : n < 2 ^ 64) (hK : K < 2 ^ 64) :
    (Cond.cmp .ne r (.imm k)).eval s = decide (n ≠ K) := by
  simp only [Cond.eval, Rhs.eval, hr, hk]
  by_cases h : n = K
  · subst h; simp
  · simp only [h, ne_eq, not_false_eq_true, decide_true]
    exact bne_iff_ne.mpr fun h' ↦ h (toUInt64_inj hn hK h')

@[simp] theorem QState.setReg_setReg_same (s : QState) (r : Reg64) (a b : UInt64) :
    (s.setReg r a).setReg r b = s.setReg r b := by
  simp [QState.setReg]

/-! ## The invariant under updates -/

theorem Inv.setReg {base : UInt64} {V : Nat → UInt64} {s : QState} (hI : Inv base V s) {d : Reg64}
    (hd : d ≠ .rdi) (v : UInt64) : Inv base V (s.setReg d v) :=
  ⟨by simp [hI.rdi, Ne.symm hd], hI.mem⟩

theorem Inv.setMem {base : UInt64} {V : Nat → UInt64} {s : QState} (hI : Inv base V s) {k : Nat}
    (hk : k < Context.ctxWords) (v : UInt64) :
    Inv base (Function.update V k v) (s.setMem (base + (8 * k).toUInt64) v) := by
  refine ⟨hI.rdi, fun j hj ↦ ?_⟩
  simp only [QState.setMem_mem, Function.update_apply]
  by_cases h : j = k
  · subst h; simp
  · have h' : base + (8 * j).toUInt64 ≠ base + (8 * k).toUInt64 := fun h' ↦ h (ctx_inj hj hk h')
    simp only [h', h, ite_false]
    exact hI.mem j hj

theorem Inv.frame {base : UInt64} {V : Nat → UInt64} {s s' : QState} (hI : Inv base V s)
    (hm : s'.mem = s.mem) (hr : s'.reg .rdi = s.reg .rdi) : Inv base V s' :=
  ⟨hr.trans hI.rdi, hm ▸ hI.mem⟩

/-! ## Loads and stores -/

variable {base : UInt64} {V : Nat → UInt64} {s : QState} {P E : QState → Prop}

theorem wp_load (hI : Inv base V s) {d : Reg64} {a : Addr} {k : Nat}
    (ha : a.eval s = base + (8 * k).toUInt64) (hk : k < Context.ctxWords)
    (h : P (s.setReg d (V k))) : WP (I (.load d a)) s P E := by
  apply WP.ins'
  simp only [QInstr.step, ha, hI.mem k hk, Option.map_some]
  exact h

theorem wp_store (hI : Inv base V s) {a : Addr} {r : Reg64} {k : Nat}
    (ha : a.eval s = base + (8 * k).toUInt64) (hk : k < Context.ctxWords)
    (h : P (s.setMem (base + (8 * k).toUInt64) (s.reg r))) : WP (I (.store a r)) s P E := by
  apply WP.ins'
  simp only [QInstr.step, ha, hI.mem k hk, Option.map_some]
  exact h

theorem wp_storei (hI : Inv base V s) {a : Addr} {c : Int64} {k : Nat}
    (ha : a.eval s = base + (8 * k).toUInt64) (hk : k < Context.ctxWords)
    (h : P (s.setMem (base + (8 * k).toUInt64) c.toUInt64)) : WP (I (.storei a c)) s P E := by
  apply WP.ins'
  simp only [QInstr.step, ha, hI.mem k hk, Option.map_some]
  exact h

/-- A load of context word `k`, at the head of a block. -/
theorem blk_load (hI : Inv base V s) {d : Reg64} {a : Addr} {k : Nat} {rest : List Stmt}
    (ha : a.eval s = base + (8 * k).toUInt64) (hk : k < Context.ctxWords)
    (h : WP (blk rest) (s.setReg d (V k)) P E) : WP (blk (I (.load d a) :: rest)) s P E :=
  WP.blk_cons (wp_load hI ha hk h)

/-- A store to context word `k`, at the head of a block. -/
theorem blk_store (hI : Inv base V s) {a : Addr} {r : Reg64} {k : Nat} {rest : List Stmt}
    (ha : a.eval s = base + (8 * k).toUInt64) (hk : k < Context.ctxWords)
    (h : WP (blk rest) (s.setMem (base + (8 * k).toUInt64) (s.reg r)) P E) :
    WP (blk (I (.store a r) :: rest)) s P E :=
  WP.blk_cons (wp_store hI ha hk h)

/-- An instruction that is not a load or a store, at the head of a block. -/
theorem blk_ins {i : QInstr} {rest : List Stmt}
    (h : match i.step s with | some s' => WP (blk rest) s' P E | none => False) :
    WP (blk (I i :: rest)) s P E :=
  WP.blk_cons (WP.ins' h)

theorem blk_load_cw (hI : Inv base V s) {d : Reg64} {k : Nat} {rest : List Stmt}
    (hk : k < Context.ctxWords) (h : WP (blk rest) (s.setReg d (V k)) P E) :
    WP (blk (I (.load d (cw k)) :: rest)) s P E :=
  blk_load hI (by rw [cw_eval, hI.rdi]) hk h

theorem blk_store_cw (hI : Inv base V s) {r : Reg64} {k : Nat} {rest : List Stmt}
    (hk : k < Context.ctxWords)
    (h : WP (blk rest) (s.setMem (base + (8 * k).toUInt64) (s.reg r)) P E) :
    WP (blk (I (.store (cw k) r) :: rest)) s P E :=
  blk_store hI (by rw [cw_eval, hI.rdi]) hk h

theorem blk_storei_cw (hI : Inv base V s) {c : Int64} {k : Nat} {rest : List Stmt}
    (hk : k < Context.ctxWords)
    (h : WP (blk rest) (s.setMem (base + (8 * k).toUInt64) c.toUInt64) P E) :
    WP (blk (I (.storei (cw k) c) :: rest)) s P E :=
  WP.blk_cons (wp_storei hI (by rw [cw_eval, hI.rdi]) hk h)

theorem blk_load_cwi (hI : Inv base V s) {d r : Reg64} {n k : Nat} {rest : List Stmt}
    (hr : s.reg r = n.toUInt64) (hk : n + k < Context.ctxWords)
    (h : WP (blk rest) (s.setReg d (V (n + k))) P E) :
    WP (blk (I (.load d (cwi r k)) :: rest)) s P E :=
  blk_load hI (by rw [cwi_eval s hr, hI.rdi]) hk h

/-- A store to context word `k`, the state after it abstracted to its words and registers. -/
theorem blk_store_cw' (hI : Inv base V s) {r : Reg64} {k : Nat} {rest : List Stmt}
    (hk : k < Context.ctxWords)
    (h : ∀ s', Inv base (Function.update V k (s.reg r)) s' → s'.reg = s.reg → WP (blk rest) s' P E) :
    WP (blk (I (.store (cw k) r) :: rest)) s P E :=
  blk_store_cw hI hk (h _ (hI.setMem hk _) rfl)

/-- A store of an immediate to context word `k`, the state after it abstracted. -/
theorem blk_storei_cw' (hI : Inv base V s) {c : Int64} {k : Nat} {rest : List Stmt}
    (hk : k < Context.ctxWords)
    (h : ∀ s', Inv base (Function.update V k c.toUInt64) s' → s'.reg = s.reg →
      WP (blk rest) s' P E) :
    WP (blk (I (.storei (cw k) c) :: rest)) s P E :=
  blk_storei_cw hI hk (h _ (hI.setMem hk _) rfl)

/-- A loop, by an invariant and a variant, ending where the invariant holds and the condition
fails. -/
theorem wp_loop {c : Cond} {b : Stmt} (I : QState → Prop) (μ : QState → Nat) (h0 : I s)
    (hstep : ∀ s, I s → c.eval s = true → WP b s (fun s₁ ↦ I s₁ ∧ μ s₁ < μ s) E) :
    WP (.loop c b) s (fun s' ↦ I s' ∧ c.eval s' = false) E :=
  WP.loop I μ h0 hstep fun _ h hc ↦ ⟨h, hc⟩

/-- A block, by an invariant indexed by how many of its statements have run. -/
theorem wp_blk_forall {xs : List Stmt} (Q : Nat → QState → Prop) (h0 : Q 0 s)
    (hstep : ∀ i (hi : i < xs.length) s, Q i s → WP xs[i] s (Q (i + 1)) E) :
    WP (blk xs) s (Q xs.length) E := by
  induction xs generalizing s Q with
  | nil => exact WP.blk_nil h0
  | cons x xs ih =>
    apply WP.blk_cons
    refine WP.mono (hstep 0 (by simp) s h0) (fun s1 h1 ↦ ?_) (fun _ h ↦ h)
    have := ih (Q := fun i ↦ Q (i + 1)) h1 fun i hi s hs ↦ by
      have := hstep (i + 1) (by simp; omega) s hs
      rwa [List.getElem_cons_succ] at this
    simpa using this

/-! ## What the verifier keeps -/

/-- The words no part of the verifier writes: all but the scratch area and the working words, of
which the buffers' first two (`PK.seed`) and the address's two zero fields are kept. -/
def Kept (k : Nat) : Prop :=
  ¬(k < 84 ∨ (mdBuf ≤ k ∧ k < bigBuf + 134)) ∨ k = smallBuf ∨ k = smallBuf + 1 ∨ k = bigBuf ∨
    k = bigBuf + 1 ∨ k = adrsRec + 1 ∨ k = adrsRec + 2

/-- `V'` agrees with `V` on the kept words. -/
def Frame (V V' : Nat → UInt64) : Prop := ∀ k, Kept k → V' k = V k

theorem Frame.refl (V : Nat → UInt64) : Frame V V := fun _ _ ↦ rfl

theorem Frame.trans {V₁ V₂ V₃ : Nat → UInt64} (h₁ : Frame V₁ V₂) (h₂ : Frame V₂ V₃) :
    Frame V₁ V₃ := fun k hk ↦ (h₂ k hk).trans (h₁ k hk)

theorem Frame.update {V V' : Nat → UInt64} (h : Frame V V') {k : Nat} (hk : ¬Kept k) (v : UInt64) :
    Frame V (Function.update V' k v) := fun j hj ↦ by
  have hne : j ≠ k := fun h' ↦ hk (h' ▸ hj)
  rw [Function.update_of_ne hne]
  exact h j hj

theorem Frame.of_eq {V V' : Nat → UInt64} (h : ∀ k, Kept k → V' k = V k) : Frame V V' := h

/-! ## Hashing words of the context -/

/-- **`Keccak.hash` of `len` bytes held by the context words from `j`**: the digest in words `0`
to `3`, the words from `84` kept. -/
theorem hash_ok (hb : Fits base) (hI : Inv base V s) {j len : Nat}
    (hrsi : s.reg .rsi = base + (8 * j).toUInt64) (hrbx : s.reg .rbx = len.toUInt64)
    (hj : scratchWords ≤ j) (hjn : j + (len + 7) / 8 ≤ Context.ctxWords) (hlen0 : 0 < len)
    (hlen : len < 2 ^ 32)
    (hz : ∀ b ∈ (wordsBytes (words V j ((len + 7) / 8))).drop len, b = 0) :
    WP hash s (fun s' ↦ ∃ V', Inv base V' s' ∧ (∀ k, scratchWords ≤ k → V' k = V k) ∧
      (∀ k (hk : k < 4), V' k = (keccak256 ((wordsBytes (words V j ((len + 7) / 8))).take len))[k]) ∧
      RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8] s s') E := by
  unfold Fits at hb
  unfold Context.ctxWords at hjn hb
  have hsw : scratchWords = 84 := rfl
  have hn := words_length V j ((len + 7) / 8)
  have hscr : ∀ k, scratchAddr base k = base + (8 * k).toUInt64 := fun _ ↦ rfl
  have haddr : ∀ i, base + (8 * j).toUInt64 + (8 * i).toUInt64 = base + (8 * (j + i)).toUInt64 := by
    intro i
    simp only [Nat.toUInt64_eq, Nat.mul_add, UInt64.ofNat_add, UInt64.add_assoc]
  have hbase : (base + (8 * j).toUInt64).toNat = base.toNat + 8 * j := by
    simp only [UInt64.toNat_add, Nat.toUInt64_eq, UInt64.toNat_ofNat']
    rw [Nat.mod_eq_of_lt (show 8 * j < 2 ^ 64 by omega), Nat.mod_eq_of_lt (by omega)]
  refine WP.mono (hash_spec (ws := words V j ((len + 7) / 8)) (len := len)
    ⟨hn, hz⟩ hrbx hlen ?_ ?_ ?_) ?_ (fun _ h ↦ h)
  · intro i hi
    rw [hrsi, haddr, words_getElem]
    rw [hn] at hi
    exact hI.mem _ (by unfold Context.ctxWords; omega)
  · intro k hk
    rw [hI.rdi, hscr, hI.mem k (by unfold Context.ctxWords; omega)]
    rfl
  · intro i hi k hk h
    rw [hrsi, haddr, hI.rdi, hscr] at h
    rw [hn] at hi
    have := ctx_inj (by unfold Context.ctxWords; omega) (by unfold Context.ctxWords; omega) h
    omega
  · rintro s' ⟨hd, hs, hout, hf⟩
    have hrdi' : s'.reg .rdi = base := by rw [hf .rdi (by simp)]; exact hI.rdi
    refine ⟨fun k ↦ if k < scratchWords then (s'.mem (base + (8 * k).toUInt64)).getD 0 else V k,
      ⟨hrdi', fun k hk ↦ ?_⟩, fun k hk ↦ by simp [Nat.not_lt.mpr hk], fun k hk ↦ ?_, hf⟩
    · by_cases h : k < scratchWords
      · simp only [h, ite_true]
        have := hs k h
        rw [hI.rdi, hscr] at this
        obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp this
        rw [hv]; rfl
      · simp only [h, ite_false]
        rw [hout _ (fun k' hk' h' ↦ ?_)]
        · exact hI.mem k hk
        · rw [hI.rdi, hscr] at h'
          have := ctx_inj (base := base) hk (by unfold Context.ctxWords; omega) h'
          omega
    · have h4 : k < scratchWords := by omega
      simp only [h4, ite_true]
      have := hd k hk
      rw [hI.rdi, hscr] at this
      rw [this]; rfl

end Native.SphincsVerifier
