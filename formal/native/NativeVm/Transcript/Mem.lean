module

public import NativeVm.Transcript.Code
public import Native.Keccak.Spec
public import Native.Keccak.Permute

/-!
# Words, addresses and steps

The facts the gadgets' proofs share: word addresses (`wd`) and their (in)equalities, within an area
and across disjoint areas (`wd_ne_of_disj`); what a block keeps (`Keep`, `CtxIn`); one instruction at
a time (`wp_load`, `wp_store`, `wp_storei`, `wp_reg`, `wp_failIf`, `wp_then`); and the shared
blocks: copies and zeroing of the context's words (`copyCtx_spec`, `zeroCtx_spec`), and
`Keccak.hash` and `Keccak.permute` on the context's scratch area (`hashAt_spec`, `permuteAt_spec`).
-/

@[expose] public section

namespace NativeVm.Transcript

open Native LeanVM.Semantics LeanVM.Protocol.KeccakHash Native.Keccak

/-! ## Numbers -/

theorem toNat_toUInt64 {n : Nat} (h : n < 2 ^ 64) : n.toUInt64.toNat = n := by
  simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat']
  omega

theorem toUInt64_inj {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    a.toUInt64 = b.toUInt64 ↔ a = b := by
  rw [← UInt64.toNat_inj, toNat_toUInt64 ha, toNat_toUInt64 hb]

theorem toUInt64_lt {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    a.toUInt64 < b.toUInt64 ↔ a < b := by
  rw [UInt64.lt_iff_toNat_lt, toNat_toUInt64 ha, toNat_toUInt64 hb]

theorem toUInt64_le {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    a.toUInt64 ≤ b.toUInt64 ↔ a ≤ b := by
  rw [UInt64.le_iff_toNat_le, toNat_toUInt64 ha, toNat_toUInt64 hb]

theorem toUInt64_succ (n : Nat) : n.toUInt64 + 1 = (n + 1).toUInt64 := by
  simp [Nat.toUInt64_eq, UInt64.ofNat_add]

theorem toUInt64_add (a b : Nat) : a.toUInt64 + b.toUInt64 = (a + b).toUInt64 := by
  simp [Nat.toUInt64_eq, UInt64.ofNat_add]

theorem toUInt64_shl (c n : Nat) (hn : n < 64) :
    c.toUInt64 <<< n.toUInt64 = (2 ^ n * c).toUInt64 := by
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_shiftLeft, Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (show n % 2 ^ 64 < 64 by omega), Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega)]
  rw [Nat.mul_comm (2 ^ n), Nat.mod_mul_mod]

theorem wdisp_toUInt64 (k : Nat) : (wdisp k).toUInt64 = (8 * k).toUInt64 := (rfl)

theorem int64_toUInt64 (n : Nat) :
    (no_index (OfNat.ofNat n : Int64)).toUInt64 = (OfNat.ofNat n : UInt64) := (rfl)

theorem natLit_toUInt64 (n : Nat) [n.AtLeastTwo] :
    (no_index (OfNat.ofNat n : Nat)).toUInt64 = (OfNat.ofNat n : UInt64) := (rfl)

/-! ## Word addresses -/

theorem wd_add (b : UInt64) (k j : Nat) : wd b k + (8 * j).toUInt64 = wd b (k + j) := by
  simp only [wd, Nat.toUInt64_eq, Nat.mul_add, UInt64.ofNat_add, UInt64.add_assoc]

theorem wd_zero (b : UInt64) : wd b 0 = b := by simp [wd]

theorem wd_inj {b : UInt64} {k k' : Nat} (hk : k < 2 ^ 61) (hk' : k' < 2 ^ 61) :
    wd b k = wd b k' ↔ k = k' := by
  unfold wd
  rw [UInt64.add_right_inj, toUInt64_inj (by omega) (by omega)]
  omega

theorem wd_toNat {b : UInt64} {n k : Nat} (h : Fits b n) (hk : k < n) :
    (wd b k).toNat = b.toNat + 8 * k := by
  unfold Fits at h
  unfold wd
  rw [UInt64.toNat_add, toNat_toUInt64 (by omega)]
  omega

/-- Words of disjoint areas differ. -/
theorem wd_ne_of_disj {b c : UInt64} {n m i j : Nat} (hb : Fits b n) (hc : Fits c m)
    (hd : Disj b n c m) (hi : i < n) (hj : j < m) : wd b i ≠ wd c j := fun e ↦ by
  have := congrArg UInt64.toNat e
  rw [wd_toNat hb hi, wd_toNat hc hj] at this
  unfold Disj at hd
  omega

theorem Disj.symm {b c : UInt64} {n m : Nat} (h : Disj b n c m) : Disj c m b n := Or.symm h

/-! ## What a block keeps -/

/-- `m'` is `m` outside `W`. -/
def Keep (W : UInt64 → Prop) (m m' : UInt64 → Option UInt64) : Prop := ∀ a, ¬ W a → m' a = m a

/-- The context's words `lo ≤ k < hi`. -/
def CtxIn (ctx : UInt64) (lo hi : Nat) (a : UInt64) : Prop := ∃ k, lo ≤ k ∧ k < hi ∧ a = wd ctx k

theorem Keep.refl (W : UInt64 → Prop) (m : UInt64 → Option UInt64) : Keep W m m := fun _ _ ↦ rfl

theorem Keep.trans {W W' : UInt64 → Prop} {m₁ m₂ m₃ : UInt64 → Option UInt64}
    (h : Keep W m₁ m₂) (h' : Keep W' m₂ m₃) {V : UInt64 → Prop}
    (hW : ∀ a, W a → V a) (hW' : ∀ a, W' a → V a) : Keep V m₁ m₃ :=
  fun a ha ↦ (h' a fun h ↦ ha (hW' a h)).trans (h a fun h ↦ ha (hW a h))

theorem Keep.mono {W V : UInt64 → Prop} {m m' : UInt64 → Option UInt64} (h : Keep W m m')
    (hW : ∀ a, W a → V a) : Keep V m m' := fun a ha ↦ h a fun h ↦ ha (hW a h)

theorem Keep.update {W : UInt64 → Prop} {m m' : UInt64 → Option UInt64} (h : Keep W m m')
    {a : UInt64} (ha : W a) (v : Option UInt64) : Keep W m (Function.update m' a v) :=
  fun a' ha' ↦ by
    rw [Function.update_of_ne (fun e ↦ ha' (by rw [e]; exact ha))]
    exact h a' ha'

theorem Keep.setMem {W : UInt64 → Prop} {s s' : QState} (h : Keep W s.mem s'.mem) {a : UInt64}
    (ha : W a) (v : UInt64) : Keep W s.mem (s'.setMem a v).mem := h.update ha _

theorem Keep.setReg {W : UInt64 → Prop} {m : UInt64 → Option UInt64} {s' : QState}
    (h : Keep W m s'.mem) (r : Reg64) (v : UInt64) : Keep W m (s'.setReg r v).mem := h

theorem Keep.ofSetReg {W : UInt64 → Prop} {m : UInt64 → Option UInt64} {s : QState} {r : Reg64}
    {v : UInt64} (h : Keep W s.mem m) : Keep W (s.setReg r v).mem m := h

theorem CtxIn.mono {ctx : UInt64} {lo hi lo' hi' : Nat} {a : UInt64} (h : CtxIn ctx lo hi a)
    (hlo : lo' ≤ lo) (hhi : hi ≤ hi') : CtxIn ctx lo' hi' a := by
  obtain ⟨k, h1, h2, rfl⟩ := h
  exact ⟨k, by omega, by omega, rfl⟩

theorem CtxIn.word {ctx : UInt64} {lo hi k : Nat} (h1 : lo ≤ k) (h2 : k < hi) :
    CtxIn ctx lo hi (wd ctx k) := ⟨k, h1, h2, rfl⟩

/-- A context word outside the range is not in it. -/
theorem not_ctxIn {ctx : UInt64} {lo hi k : Nat} (hk : k < lo ∨ hi ≤ k) (hk' : k < 2 ^ 61)
    (hhi : hi ≤ 2 ^ 61) : ¬ CtxIn ctx lo hi (wd ctx k) := by
  rintro ⟨k', h1, h2, e⟩
  rw [wd_inj hk' (by omega)] at e
  omega

/-- The context's word `k` outside the range is kept. -/
theorem Keep.ctx {ctx : UInt64} {lo hi k : Nat} {m m' : UInt64 → Option UInt64}
    (h : Keep (CtxIn ctx lo hi) m m') (hk : k < lo ∨ hi ≤ k) (hk' : k < 2 ^ 61)
    (hhi : hi ≤ 2 ^ 61) : m' (wd ctx k) = m (wd ctx k) := h _ (not_ctxIn hk hk' hhi)

/-! ## Addresses of the code -/

theorem eval_at (r : Reg64) (d : Int64) (s : QState) : (at_ r d).eval s = s.reg r + d.toUInt64 := by
  simp [Addr.eval, at_]

theorem eval_wd {s : QState} {r : Reg64} {b : UInt64} {j : Nat} (h : s.reg r = wd b j) (k : Nat) :
    (at_ r (wdisp k)).eval s = wd b (j + k) := by
  rw [eval_at, h, wdisp_toUInt64, wd_add]

theorem eval_cw {s : QState} {b : UInt64} (h : s.reg .rdi = b) (k : Nat) : (cw k).eval s = wd b k := by
  rw [eval_wd (j := 0) (by rw [h, wd_zero]), Nat.zero_add]

/-- An indexed address, the index in bytes. -/
theorem eval_idx8 {s : QState} {base ix : Reg64} {b : UInt64} {j i : Nat}
    (hb : s.reg base = wd b j) (hi : s.reg ix = (8 * i).toUInt64) (k : Nat) :
    ({ base := base, idx := some (ix, .W8), disp := wdisp k } : Addr).eval s = wd b (j + i + k) := by
  simp only [Addr.eval, hb, hi, wdisp_toUInt64]
  rw [show Width.W8.bytes.toUInt64 = 1 from rfl, UInt64.mul_one, wd_add, wd_add]

/-- An indexed address, the index in words. -/
theorem eval_idx64 {s : QState} {base ix : Reg64} {b : UInt64} {j i : Nat}
    (hb : s.reg base = wd b j) (hi : s.reg ix = i.toUInt64) (k : Nat) :
    ({ base := base, idx := some (ix, .W64), disp := wdisp k } : Addr).eval s = wd b (j + i + k) := by
  simp only [Addr.eval, hb, hi, wdisp_toUInt64]
  rw [show Width.W64.bytes.toUInt64 = 8 from rfl, ← wd_add b (j + i) k, ← wd_add b j i]
  congr 1
  simp only [Nat.toUInt64_eq, UInt64.ofNat_mul]
  rw [UInt64.mul_comm]
  rfl

/-- An indexed address, the index in words, any displacement. -/
theorem eval_idx64' {s : QState} {base ix : Reg64} {b : UInt64} {j i k : Nat} {d : Int64}
    (hb : s.reg base = wd b j) (hi : s.reg ix = i.toUInt64) (hd : d.toUInt64 = (8 * k).toUInt64) :
    ({ base := base, idx := some (ix, .W64), disp := d } : Addr).eval s = wd b (j + i + k) := by
  have := eval_idx64 (s := s) (k := k) hb hi
  simp only [Addr.eval, wdisp_toUInt64] at this ⊢
  rw [hd]
  exact this

/-! ## One instruction at a time -/

variable {s : QState} {P E : QState → Prop} {xs : List Stmt}

theorem wp_reg {i : QInstr} {s' : QState} (hs : i.step s = some s') (h : WP (blk xs) s' P E) :
    WP (blk (I i :: xs)) s P E :=
  WP.blk_cons (WP.ins hs h)

theorem wp_load {d : Reg64} {a : Addr} {x v : UInt64} (ha : a.eval s = x) (hv : s.mem x = some v)
    (h : WP (blk xs) (s.setReg d v) P E) : WP (blk (I (.load d a) :: xs)) s P E :=
  wp_reg (by simp [QInstr.step, ha, hv]) h

theorem wp_store {a : Addr} {r : Reg64} {x : UInt64} (ha : a.eval s = x) (hd : (s.mem x).isSome)
    (h : WP (blk xs) (s.setMem x (s.reg r)) P E) : WP (blk (I (.store a r) :: xs)) s P E := by
  refine wp_reg ?_ h
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hd
  simp [QInstr.step, ha, hv]

theorem wp_storei {a : Addr} {n : Int64} {x : UInt64} (ha : a.eval s = x) (hd : (s.mem x).isSome)
    (h : WP (blk xs) (s.setMem x n.toUInt64) P E) : WP (blk (I (.storei a n) :: xs)) s P E := by
  refine wp_reg ?_ h
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hd
  simp [QInstr.step, ha, hv]

theorem cond_geu (a : Reg64) (b : Rhs) (s : QState) :
    (Cond.cmp .geu a b).eval s = decide (b.eval s ≤ s.reg a) := (rfl)

theorem cond_ltu (a : Reg64) (b : Rhs) (s : QState) :
    (Cond.cmp .ltu a b).eval s = decide (s.reg a < b.eval s) := (rfl)

theorem cond_ne (a : Reg64) (b : Rhs) (s : QState) :
    (Cond.cmp .ne a b).eval s = (s.reg a != b.eval s) := (rfl)

theorem cond_eq (a : Reg64) (b : Rhs) (s : QState) :
    (Cond.cmp .eq a b).eval s = (s.reg a == b.eval s) := (rfl)

theorem rhs_imm (k : Int64) (s : QState) : (Rhs.imm k).eval s = k.toUInt64 := (rfl)

theorem rhs_reg (r : Reg64) (s : QState) : (Rhs.reg r).eval s = s.reg r := (rfl)

theorem wp_failIf {c : Cond} (hc : c.eval s = false) (h : WP (blk xs) s P E) :
    WP (blk (failIf c :: xs)) s P E :=
  WP.blk_cons (WP.ite (by rw [hc]; exact WP.skip h))

theorem wp_failIf_fail {c : Cond} (hc : c.eval s = true) (h : E s) :
    WP (blk (failIf c :: xs)) s P E :=
  WP.blk_cons (WP.ite (by rw [hc]; exact WP.fail h))

theorem wp_then {x : Stmt} {Q : QState → Prop} (h : WP x s Q E)
    (k : ∀ s₁, Q s₁ → WP (blk xs) s₁ P E) : WP (blk (x :: xs)) s P E :=
  WP.blk_cons (WP.mono h k fun _ h ↦ h)

theorem wp_done (h : P s) : WP (blk []) s P E := WP.blk_nil h

/-- The end of a block, its state named. -/
theorem wp_done_gen (h : ∀ s', s = s' → P s') : WP (blk []) s P E := WP.blk_nil (h s rfl)

theorem wp_ite_true {c : Cond} {t e : Stmt} (hc : c.eval s = true) (h : WP t s P E) :
    WP (.ite c t e) s P E :=
  WP.ite (by rw [hc]; exact h)

theorem wp_ite_false {c : Cond} {t e : Stmt} (hc : c.eval s = false) (h : WP e s P E) :
    WP (.ite c t e) s P E :=
  WP.ite (by rw [hc]; exact h)

/-! ## Register frames -/

theorem rf_refl (l : List Reg64) (s : QState) : RegsFrame l s s := fun _ _ ↦ rfl

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

theorem rf_mono {l l' : List Reg64} {s s' : QState} (h : RegsFrame l s s') (hl : l ⊆ l' := by simp) :
    RegsFrame l' s s' :=
  fun r hr ↦ h r fun h ↦ hr (hl h)

/-- Peel register and memory updates off a `RegsFrame` goal. -/
macro "rf_tac" : tactic => `(tactic| (
  repeat (first
    | with_reducible refine rf_setMem ?_ _ _
    | with_reducible refine rf_setReg ?_ (by simp) _)
  try exact rf_refl _ _))

/-! ## Copies and zeroing -/

/-- Copy piece `t`. -/
def copyP (src dst t : Nat) : List Stmt := [I (.load .rax (cw (src + t))), I (.store (cw (dst + t)) .rax)]

theorem copyCtx_eq (src dst n : Nat) : copyCtx src dst n = blk ((List.range n).flatMap (copyP src dst)) :=
  (rfl)

/-- **A copy of context words**, the ranges disjoint. -/
theorem copyCtx_spec {ctx : UInt64} {src dst n : Nat} {f : Nat → UInt64} (hrdi : s.reg .rdi = ctx)
    (hsrc : src + n ≤ 2 ^ 61) (hdst : dst + n ≤ 2 ^ 61) (hdis : src + n ≤ dst ∨ dst + n ≤ src)
    (hv : ∀ t < n, s.mem (wd ctx (src + t)) = some (f t))
    (hd : ∀ t < n, (s.mem (wd ctx (dst + t))).isSome) :
    WP (copyCtx src dst n) s (fun s' ↦ (∀ t < n, s'.mem (wd ctx (dst + t)) = some (f t)) ∧
      Keep (CtxIn ctx dst (dst + n)) s.mem s'.mem ∧ RegsFrame [.rax] s s') E := by
  rw [copyCtx_eq]
  refine Keccak.Proof.wp_range_flatMap (s := s) _ (fun j s' ↦ (∀ t < j, s'.mem (wd ctx (dst + t)) =
    some (f t)) ∧ Keep (CtxIn ctx dst (dst + j)) s.mem s'.mem ∧ RegsFrame [.rax] s s') n ?_
    ⟨fun t ht ↦ absurd ht (by omega), Keep.refl _ _, rf_refl _ _⟩
  intro j hj s' ⟨hw, hk, hr⟩
  have hrdi' : s'.reg .rdi = ctx := (hr _ (by simp)).trans hrdi
  have hsj : s'.mem (wd ctx (src + j)) = some (f j) := by
    rw [hk.ctx (by omega) (by omega) (by omega)]
    exact hv j hj
  refine wp_load (eval_cw hrdi' _) hsj (wp_store (eval_cw hrdi' _) ?_ (wp_done ⟨?_, ?_, ?_⟩))
  · rw [QState.setReg_mem, hk.ctx (by omega) (by omega) (by omega)]
    exact hd j hj
  · intro t ht
    simp only [QState.setMem_mem, QState.setReg_mem, QState.setReg_reg, ↓reduceIte]
    split
    · rename_i e
      rw [wd_inj (by omega) (by omega)] at e
      rw [show t = j by omega]
    · rename_i e
      rw [wd_inj (by omega) (by omega)] at e
      exact hw t (by omega)
  · refine Keep.update (hk.mono fun a ha ↦ ha.mono le_rfl (by omega)) (CtxIn.word (by omega)
      (by omega)) _
  · exact rf_setMem (rf_setReg hr (by simp) _) _ _

/-- Zero piece `t`. -/
def zeroP (dst t : Nat) : List Stmt := [I (.storei (cw (dst + t)) 0)]

theorem zeroCtx_eq (dst n : Nat) : zeroCtx dst n = blk ((List.range n).flatMap (zeroP dst)) := (rfl)

/-- **Zeroing context words.** -/
theorem zeroCtx_spec {ctx : UInt64} {dst n : Nat} (hrdi : s.reg .rdi = ctx) (hdst : dst + n ≤ 2 ^ 61)
    (hd : ∀ t < n, (s.mem (wd ctx (dst + t))).isSome) :
    WP (zeroCtx dst n) s (fun s' ↦ (∀ t < n, s'.mem (wd ctx (dst + t)) = some 0) ∧
      Keep (CtxIn ctx dst (dst + n)) s.mem s'.mem ∧ s'.reg = s.reg) E := by
  rw [zeroCtx_eq]
  refine Keccak.Proof.wp_range_flatMap (s := s) _ (fun j s' ↦ (∀ t < j, s'.mem (wd ctx (dst + t)) =
    some 0) ∧ Keep (CtxIn ctx dst (dst + j)) s.mem s'.mem ∧ s'.reg = s.reg) n ?_
    ⟨fun t ht ↦ absurd ht (by omega), Keep.refl _ _, rfl⟩
  intro j hj s' ⟨hw, hk, hr⟩
  have hrdi' : s'.reg .rdi = ctx := by rw [hr]; exact hrdi
  refine wp_storei (eval_cw hrdi' _) ?_ (wp_done ⟨?_, ?_, ?_⟩)
  · rw [hk.ctx (by omega) (by omega) (by omega)]
    exact hd j hj
  · intro t ht
    simp only [QState.setMem_mem]
    split
    · rfl
    · rename_i e
      rw [wd_inj (by omega) (by omega)] at e
      exact hw t (by omega)
  · exact Keep.update (hk.mono fun a ha ↦ ha.mono le_rfl (by omega)) (CtxIn.word (by omega)
      (by omega)) _
  · exact hr

/-! ## Keccak on the scratch area -/

theorem scratchAddr_ctx (ctx : UInt64) (k : Nat) :
    scratchAddr (ctx + (wdisp scratchW).toUInt64) k = wd ctx (scratchW + k) := by
  simp only [scratchAddr, wd, wdisp_toUInt64, Nat.mul_add, Nat.toUInt64_eq, UInt64.ofNat_add,
    UInt64.add_assoc]

theorem sub_add_cancel' (a b : UInt64) : a + b - b = a := by simp

/-- Moving `rdi` to the scratch area and back keeps every register but those of `rs`. -/
theorem rf_rdi_back {rs : List Reg64} {s s₁ : QState} {d : UInt64} (hrs : Reg64.rdi ∉ rs)
    (h : RegsFrame rs (s.setReg .rdi (s.reg .rdi + d)) s₁) :
    RegsFrame rs s (s₁.setReg .rdi (s₁.reg .rdi - d)) := by
  intro r hr
  have h1 := h .rdi hrs
  simp only [QState.setReg_reg, ↓reduceIte] at h1
  simp only [QState.setReg_reg]
  split
  · subst r; rw [h1, sub_add_cancel']
  · rw [h r hr]; simp_all

/-- **`Keccak.hash` on the context's scratch area.** -/
theorem hashAt_spec {ctx : UInt64} {ws : List UInt64} {len : Nat} (hrdi : s.reg .rdi = ctx)
    (hb : HoldsBytes ws len) (hlen : s.reg .rbx = len.toUInt64) (hlen32 : len < 2 ^ 32)
    (hin : WordsAt s.mem (s.reg .rsi) ws)
    (hscr : ∀ k < scratchWords, (s.mem (wd ctx (scratchW + k))).isSome)
    (hdisj : ∀ i < ws.length, ∀ k < scratchWords,
      s.reg .rsi + (8 * i).toUInt64 ≠ wd ctx (scratchW + k)) :
    WP hashAt s (fun s' ↦
      (∀ k (hk : k < 4), s'.mem (wd ctx (scratchW + k)) =
        some (keccak256 ((wordsBytes ws).take len))[k]) ∧
      (∀ k < scratchWords, (s'.mem (wd ctx (scratchW + k))).isSome) ∧
      Keep (CtxIn ctx scratchW (scratchW + scratchWords)) s.mem s'.mem ∧
      RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8] s s') E := by
  unfold hashAt
  refine wp_reg rfl (wp_then (Keccak.hash_spec hb (by simpa using hlen) hlen32
    (by simpa using hin) (fun k hk ↦ ?_) (fun i hi k hk ↦ ?_)) ?_)
  · simp only [QState.setReg_reg, ↓reduceIte, QState.setReg_mem, hrdi, scratchAddr_ctx]
    exact hscr k hk
  · simp only [QState.setReg_reg, ↓reduceIte, reduceCtorEq, hrdi, scratchAddr_ctx]
    exact hdisj i hi k hk
  rintro s₁ ⟨h1, h2, h3, h4⟩
  simp only [QState.setReg_reg, ↓reduceIte, QState.setReg_mem, hrdi, scratchAddr_ctx] at h1 h2 h3
  refine wp_reg rfl (wp_done ⟨fun k hk ↦ h1 k hk, fun k hk ↦ h2 k hk, fun a ha ↦ ?_,
    rf_rdi_back (by simp) (by rw [hrdi] at h4 ⊢; exact h4)⟩)
  simp only [QState.setReg_mem]
  exact h3 a fun k hk e ↦ ha ⟨scratchW + k, by omega, by omega, e⟩

/-- **`Keccak.permute` on the context's scratch lanes.** -/
theorem permuteAt_spec {ctx : UInt64} {A : KeccakState} (hrdi : s.reg .rdi = ctx)
    (hscr : ∀ k < scratchWords, (s.mem (wd ctx (scratchW + k))).isSome)
    (hA : ∀ i < 25, s.mem (wd ctx (scratchW + i)) = some (Keccak.lane A i)) :
    WP permuteAt s (fun s' ↦
      (∀ i < 25, s'.mem (wd ctx (scratchW + i)) = some (Keccak.lane (keccakF1600 A) i)) ∧
      (∀ k < scratchWords, (s'.mem (wd ctx (scratchW + k))).isSome) ∧
      Keep (CtxIn ctx scratchW (scratchW + scratchWords)) s.mem s'.mem ∧
      RegsFrame [.rax, .rcx, .r8] s s') E := by
  unfold permuteAt
  refine wp_reg rfl (wp_then (Keccak.Proof.permute_spec (A := A) rfl (fun k hk ↦ ?_) (fun t ht ↦ ?_)) ?_)
  · simp only [QState.setReg_reg, ↓reduceIte, QState.setReg_mem, hrdi, scratchAddr_ctx]
    exact hscr k hk
  · simp only [QState.setReg_reg, ↓reduceIte, QState.setReg_mem, hrdi, scratchAddr_ctx, Nat.zero_add]
    exact hA t ht
  rintro s₁ ⟨h1, h2, h3, h4⟩
  simp only [Keccak.Proof.ScrOk, Keccak.Proof.ScrFrame, Keccak.Proof.Words, QState.setReg_reg,
    ↓reduceIte, QState.setReg_mem, hrdi, scratchAddr_ctx, Nat.zero_add] at h1 h3 h4
  refine wp_reg rfl (wp_done ⟨fun i hi ↦ h4 i hi, fun k hk ↦ h1 k hk, fun a ha ↦ ?_,
    rf_rdi_back (by simp) (by rw [hrdi] at h2 ⊢; exact h2)⟩)
  simp only [QState.setReg_mem]
  exact h3 a fun k _ hk e ↦ ha ⟨scratchW + k, by omega, by unfold scratchWords; omega, e⟩

/-! ## What every run keeps, inside a proof -/

/-- A run keeps which words exist and the registers the statement does not write. -/
theorem WP.frame {c : Stmt} (h : WP c s P E) :
    WP c s (fun s' ↦ P s' ∧ (∀ a, (s'.mem a).isSome = (s.mem a).isSome) ∧
        ∀ r, c.writes r = false → s'.reg r = s.reg r)
      (fun s' ↦ E s' ∧ (∀ a, (s'.mem a).isSome = (s.mem a).isSome) ∧
        ∀ r, c.writes r = false → s'.reg r = s.reg r) := by
  obtain ⟨o, hx, ho⟩ := h
  refine ⟨o, hx, ?_⟩
  have hd := Exec.mem_isSome hx
  have hr := fun r (h : c.writes r = false) ↦ Exec.reg_frame hx h
  cases o with
  | ok s' => exact ⟨ho, hd, hr⟩
  | err s' => exact ⟨ho, hd, hr⟩

/-- A statement by its specification, which words exist kept. -/
theorem wp_then' {x : Stmt} {Q : QState → Prop} (h : WP x s Q E)
    (k : ∀ s₁, Q s₁ → (∀ a, (s₁.mem a).isSome = (s.mem a).isSome) → WP (blk xs) s₁ P E) :
    WP (blk (x :: xs)) s P E :=
  WP.blk_cons (WP.mono (WP.frame h) (fun s₁ h₁ ↦ k s₁ h₁.1 h₁.2.1) fun _ h ↦ h.1)

/-- The context's words exist. -/
def Dom (ctx : UInt64) (mem : UInt64 → Option UInt64) : Prop := ∀ k < ctxEnd, (mem (wd ctx k)).isSome

theorem Dom.of_isSome {ctx : UInt64} {m m' : UInt64 → Option UInt64} (h : Dom ctx m)
    (h' : ∀ a, (m' a).isSome = (m a).isSome) : Dom ctx m' := fun k hk ↦ by rw [h']; exact h k hk

theorem Dom.setMem {ctx : UInt64} {s : QState} (h : Dom ctx s.mem) (a v : UInt64) :
    Dom ctx (s.setMem a v).mem := fun k hk ↦ by
  rw [QState.setMem_mem]
  split
  · rfl
  · exact h k hk

theorem Dom.setReg {ctx : UInt64} {s : QState} (h : Dom ctx s.mem) (r : Reg64) (v : UInt64) :
    Dom ctx (s.setReg r v).mem := h

theorem Dom.isSome {ctx : UInt64} {m : UInt64 → Option UInt64} (h : Dom ctx m) {k : Nat}
    (hk : k < ctxEnd) : (m (wd ctx k)).isSome := h k hk

/-- The context's words exist through register and memory updates. -/
macro "dom_tac" : tactic => `(tactic| (
  repeat (first
    | with_reducible refine Dom.setMem ?_ _ _
    | with_reducible refine Dom.setReg ?_ _ _
    | with_reducible assumption)))

/-! ## The layout's numbers -/

theorem scratchW_val : scratchW = 32 := (rfl)
theorem laneW_val : laneW = 116 := (rfl)
theorem rateW_val : rateW = 141 := (rfl)
theorem countW_val : countW = 157 := (rfl)
theorem groundW_val : groundW = 158 := (rfl)
theorem climbW_val : climbW = 161 := (rfl)
theorem qRootW_val : qRootW = 169 := (rfl)
theorem ctxEnd_val : ctxEnd = 175 := (rfl)
theorem scratchWords_val : scratchWords = 84 := (rfl)
theorem workWords_val : workWords = 69 := (rfl)
theorem workRoots_val : workRoots = 5 := (rfl)
theorem rootStride_val : rootStride = 8 := (rfl)
theorem maxRoots_val : maxRoots = 8 := (rfl)

/-- The word of a root's entry. -/
abbrev rootW (j k : Nat) : Nat := workRoots + rootStride * j + k

/-- Unfold the layout's numbers, then `omega`. -/
macro "lay_omega" : tactic => `(tactic| first
  | omega
  | (simp only [scratchW_val, laneW_val, rateW_val, countW_val, groundW_val, climbW_val,
      qRootW_val, ctxEnd_val, scratchWords_val, workWords_val, workRoots_val, rootStride_val,
      maxRoots_val, rootW, workCursor, workPhase, workPhasePtr, workPhaseCount, workRootCount, ctxWireLen,
      ctxBytecode, ctxBytecodeLen, ctxPublic, ctxDecoded, ctxWork]
     done)
  | (simp only [scratchW_val, laneW_val, rateW_val, countW_val, groundW_val, climbW_val,
      qRootW_val, ctxEnd_val, scratchWords_val, workWords_val, workRoots_val, rootStride_val,
      maxRoots_val, rootW, workCursor, workPhase, workPhasePtr, workPhaseCount, workRootCount, ctxWireLen,
      ctxBytecode, ctxBytecodeLen, ctxPublic, ctxDecoded, ctxWork]
     omega)
  | (simp only [scratchW_val, laneW_val, rateW_val, countW_val, groundW_val, climbW_val,
      qRootW_val, ctxEnd_val, scratchWords_val, workWords_val, workRoots_val, rootStride_val,
      maxRoots_val, rootW, workCursor, workPhase, workPhasePtr, workPhaseCount, workRootCount, ctxWireLen,
      ctxBytecode, ctxBytecodeLen, ctxPublic, ctxDecoded, ctxWork] at *
     done)
  | (simp only [scratchW_val, laneW_val, rateW_val, countW_val, groundW_val, climbW_val,
      qRootW_val, ctxEnd_val, scratchWords_val, workWords_val, workRoots_val, rootStride_val,
      maxRoots_val, rootW, workCursor, workPhase, workPhasePtr, workPhaseCount, workRootCount, ctxWireLen,
      ctxBytecode, ctxBytecodeLen, ctxPublic, ctxDecoded, ctxWork] at *
     omega))

/-- Read registers through register and memory updates. -/
macro "reg_simp" : tactic => `(tactic|
  simp only [QState.setMem_reg, QState.setReg_reg, QState.setReg_mem, reduceCtorEq, ↓reduceIte,
    int64_toUInt64])

theorem ite_of_not {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : ¬ c) :
    (if c then a else b) = b := by simp [h]

theorem ite_nat_ne {α : Sort _} {a b : Nat} (x y : α) (h : a ≠ b) : (if a = b then x else y) = y :=
  by simp [h]

theorem ite_nat_eq {α : Sort _} {a b : Nat} (x y : α) (h : a = b) : (if a = b then x else y) = x :=
  by simp [h]

/-- A context word exists, through register and memory updates. -/
macro "some_tac" : tactic => `(tactic| (
  refine Dom.isSome ?_ (by lay_omega)
  repeat (first
    | with_reducible refine Dom.setMem ?_ _ _
    | with_reducible refine Dom.setReg ?_ _ _
    | with_reducible assumption)))

theorem isSome_setMem (s : QState) {a : UInt64} (v : UInt64) (h : (s.mem a).isSome) (a' : UInt64) :
    ((s.setMem a v).mem a').isSome = (s.mem a').isSome := by
  rw [QState.setMem_mem]
  split
  · subst a'; rw [h]; rfl
  · rfl

/-- Which words exist, through register updates and stores to words of the context that exist. -/
macro "isSome_tac" : tactic => `(tactic| (
  repeat (first
    | rw [QState.setReg_mem]
    | rw [isSome_setMem _ _ (by some_tac)])))

theorem setMem_wd_ne (s : QState) {b : UInt64} {k k' : Nat} (v : UInt64) (h : k' ≠ k)
    (hk : k < 2 ^ 61) (hk' : k' < 2 ^ 61) : (s.setMem (wd b k) v).mem (wd b k') = s.mem (wd b k') := by
  rw [QState.setMem_mem]; simp only [wd_inj hk' hk, h, ↓reduceIte]

theorem setMem_wd_eq (s : QState) {b : UInt64} {k k' : Nat} (v : UInt64) (h : k' = k) :
    (s.setMem (wd b k) v).mem (wd b k') = some v := by
  subst h; simp

/-- Read a word through register and memory updates: the addresses of one area compared by index. -/
macro "mem_simp" : tactic => `(tactic|
  simp (disch := lay_omega) only [QState.setReg_mem, setMem_wd_ne, setMem_wd_eq, QState.setReg_reg,
    QState.setMem_reg, reduceCtorEq, ↓reduceIte, int64_toUInt64])

end NativeVm.Transcript
