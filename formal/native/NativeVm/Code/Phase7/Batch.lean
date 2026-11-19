module

public import NativeVm.Code.Phase7.Preds
public import NativeVm.Code.Phase7.EOps
public import NativeVm.Code.Phase7.Subspace
public import NativeVm.Code.Phase7.Novel
public import NativeVm.Code.Phase7.Steps
public import NativeVm.Transcript.QueryPre

/-!
# A level's queries: the batched value and the final check

Two loops over a level's queries (`queriesR`, the rows at `rowsR`), the loop state in scratch words
since the kernels clobber the registers: the query index at `cI`, the current row's address at
`tmpO + 18`, the batched sum at `tmpO + 16`. Per query `x` (`qNovel`, `qFold`):

* `subAtC` writes `what = subspaceAtTable (subspaceTable μ) x` at `whatO` (the table at `tabO`);
* `novelEvalC` evaluates the coefficients at `hiO` (`cJ` of them) at `what`, its buffer at `novO`;
* `foldRowC` folds the row (`tmpO + 24` words, the level's index at `cIdx`, the rounds at
  `roundsR`), its buffer at `foldO`.

`batchC` adds `w · (fold + what[μ] · novel)`, `w` the query's weight (`EWArr` at the address in
`cK`), into `tmpO + 16` (`batchedW`); `finalCheckC` fails unless `fold = novel` for every query
(`finalOkW`). Both write only the words `WB`: `cI`, `tmpO + 16 .. tmpO + 24` and
`whatO .. foldO + 256`.
-/

@[expose] public section

namespace NativeVm.Code.P7

open Native NativeVm.Model LeanVM.Parameters
open NativeVm.Transcript (wd Fits Disj Env cw wdisp ctxWork wd_inj wd_zero wd_toNat wp_load
  wp_store wp_storei wp_reg toNat_toUInt64 toUInt64_lt)

/-- The working area's words `batchC` and `finalCheckC` write. -/
def WB (k : Nat) : Prop :=
  k = cI ∨ (tmpO + 16 ≤ k ∧ k < tmpO + 24) ∨ (whatO ≤ k ∧ k < foldO + 256)

namespace BT

/-! ## The words written -/

/-- `m'` is `m` but for the words `WB`. -/
def KeepB (W : UInt64) (m m' : UInt64 → Option UInt64) : Prop :=
  ∀ a, (∀ k, WB k → a ≠ wd W k) → m' a = m a

/-- `m'` is `m` but for the kernels' buffers, `whatO .. foldO + 256`. -/
def KeepH (W : UInt64) (m m' : UInt64 → Option UInt64) : Prop :=
  ∀ a, (∀ k, whatO ≤ k → k < foldO + 256 → a ≠ wd W k) → m' a = m a

/-- The same words exist. -/
def DomEq (m m' : UInt64 → Option UInt64) : Prop := ∀ a, (m' a).isSome = (m a).isSome

/-- Unfold the scratch offsets, then `omega`. -/
macro "bomega" : tactic => `(tactic| (
  simp only [WB, cI, cJ, cK, cMu, cIdx, tmpO, hiO, tabO, whatO, novO, foldO, sc, scratch_off,
    queries_off, rows_off, rounds_off, whir_off, whirWords_val] at *
  omega))

theorem WB_cI : WB cI := .inl rfl

theorem WB_18 : WB (tmpO + 18) := .inr (.inl ⟨by omega, by omega⟩)

theorem WB_lt {k : Nat} (h : WB k) : k < 2 ^ 61 := by bomega

variable {W : UInt64} {m m₁ m₂ m₃ : UInt64 → Option UInt64}

theorem KeepB.refl (W : UInt64) (m : UInt64 → Option UInt64) : KeepB W m m := fun _ _ ↦ rfl

theorem KeepB.trans (h₁ : KeepB W m₁ m₂) (h₂ : KeepB W m₂ m₃) : KeepB W m₁ m₃ :=
  fun a ha ↦ (h₂ a ha).trans (h₁ a ha)

theorem KeepH.refl (W : UInt64) (m : UInt64 → Option UInt64) : KeepH W m m := fun _ _ ↦ rfl

theorem KeepH.trans (h₁ : KeepH W m₁ m₂) (h₂ : KeepH W m₂ m₃) : KeepH W m₁ m₃ :=
  fun a ha ↦ (h₂ a ha).trans (h₁ a ha)

theorem KeepH.toB (h : KeepH W m₁ m₂) : KeepB W m₁ m₂ :=
  fun a ha ↦ h a fun k h1 h2 ↦ ha k (.inr (.inr ⟨h1, h2⟩))

theorem DomEq.refl (m : UInt64 → Option UInt64) : DomEq m m := fun _ ↦ rfl

theorem DomEq.trans (h₁ : DomEq m₁ m₂) (h₂ : DomEq m₂ m₃) : DomEq m₁ m₃ :=
  fun a ↦ (h₂ a).trans (h₁ a)

theorem KeepB.get (h : KeepB W m₁ m₂) {j : Nat} (hj : ¬ WB j) (hj' : j < 2 ^ 61) :
    m₂ (wd W j) = m₁ (wd W j) :=
  h _ fun _ hk e ↦ hj ((wd_inj hj' (WB_lt hk)).mp e ▸ hk)

theorem KeepH.get (h : KeepH W m₁ m₂) {j : Nat} (hj : j < whatO ∨ foldO + 256 ≤ j)
    (hj' : j < 2 ^ 61) : m₂ (wd W j) = m₁ (wd W j) :=
  h _ fun _ h1 h2 e ↦ by
    have := (wd_inj hj' (by bomega)).mp e
    omega

theorem KeepB.same (h : KeepB W m₁ m₂) {o n : Nat} (hW : ∀ j < n, ¬ WB (o + j))
    (hn : o + n < 2 ^ 61) : Same m₁ m₂ (wd W o) n := fun j hj ↦ by
  rw [wd_wd]
  exact h.get (hW j hj) (by omega)

theorem KeepH.same (h : KeepH W m₁ m₂) {o n : Nat} (hW : o + n ≤ whatO ∨ foldO + 256 ≤ o)
    (hn : o + n < 2 ^ 61) : Same m₁ m₂ (wd W o) n := fun j hj ↦ by
  rw [wd_wd]
  exact h.get (by omega) (by omega)

/-- A kernel's buffer inside `whatO .. foldO + 256`. -/
theorem KeepH.buf {t t' : QState} (h : KeepH W m t.mem) {o n : Nat}
    (hb : ∀ a, (∀ k < n, a ≠ wd (wd W o) k) → t'.mem a = t.mem a)
    (hw : whatO ≤ o ∧ o + n ≤ foldO + 256) : KeepH W m t'.mem := fun a ha ↦ by
  rw [hb a fun k hk e ↦ ha (o + k) (by omega) (by omega) (by rw [e, wd_wd])]
  exact h a ha

theorem KeepB.setMem {t : QState} (h : KeepB W m t.mem) {k : Nat} (hk : WB k) (v : UInt64) :
    KeepB W m (t.setMem (wd W k) v).mem := fun a ha ↦ by
  simp only [QState.setMem_mem, ha k hk, ite_false]
  exact h a ha

theorem DomEq.setMem {t : QState} (h : DomEq m t.mem) {a : UInt64} (ha : (t.mem a).isSome)
    (v : UInt64) : DomEq m (t.setMem a v).mem := fun b ↦ by
  rw [QState.setMem_mem]
  split
  · subst b; rw [← h a]; exact ha.symm ▸ rfl
  · exact h b

/-! ## Areas -/

theorem fitW {N : Nat} (hf : Fits W N) (hN : 85438 ≤ N) {o n : Nat} (ho : o < 85438)
    (h : o + n ≤ 85438) : Fits (wd W o) n :=
  NativeVm.Transcript.Fits.sub hf (by omega) (by omega)

theorem disjW {N : Nat} (hf : Fits W N) (hN : 85438 ≤ N) {o n o' n' : Nat} (ho : o < 85438)
    (ho' : o' < 85438) (hd : o + n ≤ o' ∨ o' + n' ≤ o) : Disj (wd W o) n (wd W o') n' := by
  unfold Disj
  rw [wd_toNat hf (by omega), wd_toNat hf (by omega)]
  omega

/-! ## Steps -/

variable {env : Env} {s : QState} {P E : QState → Prop} {rest : List Stmt}

/-- `base + 8 · index + 8 k`. -/
def ix (b i : Reg64) (k : Nat) : Addr := { base := b, idx := some (i, .W64), disp := wdisp k }

theorem ldW_wp (hrdi : s.reg .rdi = env.ctx) (hwp : s.mem (wd env.ctx ctxWork) = some env.work)
    (h : WP (blk rest) (s.setReg .rbp env.work) P E) : WP (blk (ldW :: rest)) s P E :=
  wp_load (NativeVm.Transcript.eval_cw hrdi ctxWork) hwp h

theorem leaw_wp {d : Reg64} {k : Nat} (hW : s.reg .rbp = env.work)
    (h : WP (blk rest) (s.setReg d (wd env.work k)) P E) : WP (blk (leaw d k :: rest)) s P E :=
  wp_reg (i := .lea d (at_ .rbp (wdisp k))) (by rw [QInstr.step, eval_w hW k]) h

theorem stwi0_wp {k : Nat} (hW : s.reg .rbp = env.work) (hk : (s.mem (wd env.work k)).isSome)
    (h : WP (blk rest) (s.setMem (wd env.work k) 0) P E) : WP (blk (stwi k 0 :: rest)) s P E :=
  wp_storei (eval_w hW k) hk h

theorem ldi_wp {d b r : Reg64} {p v : UInt64} {i k j : Nat} (hb : s.reg b = p)
    (hi : s.reg r = i.toUInt64) (hj : i + k = j) (hv : s.mem (wd p j) = some v)
    (h : WP (blk rest) (s.setReg d v) P E) : WP (blk (I (.load d (ix b r k)) :: rest)) s P E := by
  refine wp_load (NativeVm.Transcript.eval_idx64 (j := 0) (by rw [hb, wd_zero]) hi k) ?_ h
  rw [Nat.zero_add, hj]
  exact hv

theorem kernel_wp {c : Stmt} {Q : QState → Prop} (hc : c.writes .rdi = false) (h : WP c s Q E)
    (k : ∀ s₁, Q s₁ → DomEq s.mem s₁.mem → s₁.reg .rdi = s.reg .rdi → WP (blk rest) s₁ P E) :
    WP (blk (c :: rest)) s P E :=
  WP.blk_cons (WP.mono (NativeVm.Transcript.WP.frame h)
    (fun s₁ h₁ ↦ k s₁ h₁.1 h₁.2.1 (h₁.2.2 _ hc)) fun _ h ↦ h.1)

theorem eadd_k {a b : EW} (h9 : s.reg .r9 = a.c0) (h10 : s.reg .r10 = a.c1)
    (h11 : s.reg .r11 = b.c0) (h12 : s.reg .r12 = b.c1)
    (h : ∀ s₁ : QState, s₁.mem = s.mem → s₁.reg .r9 = (a + b).c0 → s₁.reg .r10 = (a + b).c1 →
      RegsFrame [.r9, .r10] s s₁ → WP (blk rest) s₁ P E) :
    WP (blk (Field.eadd :: rest)) s P E := by
  refine Field.WP.then (Field.eadd_spec _) fun s₁ ⟨e1, m1, f1⟩ ↦ ?_
  rw [h9, h10, h11, h12, eOf_eq_toE, eOf_eq_toE, ← Equiv.EW.toE_add] at e1
  obtain ⟨l0, l1⟩ := lanes_of_eOf e1
  exact h s₁ m1 l0 l1 f1

theorem emul_k {a b : EW} (h9 : s.reg .r9 = a.c0) (h10 : s.reg .r10 = a.c1)
    (h11 : s.reg .r11 = b.c0) (h12 : s.reg .r12 = b.c1)
    (h : ∀ s₁ : QState, s₁.mem = s.mem → s₁.reg .r9 = (a * b).c0 → s₁.reg .r10 = (a * b).c1 →
      RegsFrame Field.eRegs s s₁ → WP (blk rest) s₁ P E) :
    WP (blk (Field.emul :: rest)) s P E := by
  refine Field.WP.then (Field.emul_spec _) fun s₁ ⟨e1, m1, f1⟩ ↦ ?_
  rw [h9, h10, h11, h12, eOf_eq_toE, eOf_eq_toE, ← Equiv.EW.toE_mul] at e1
  obtain ⟨l0, l1⟩ := lanes_of_eOf e1
  exact h s₁ m1 l0 l1 f1

theorem escale_k {a : EW} {b : UInt64} (h9 : s.reg .r9 = a.c0) (h10 : s.reg .r10 = a.c1)
    (h11 : s.reg .r11 = b)
    (h : ∀ s₁ : QState, s₁.mem = s.mem → s₁.reg .r9 = (EW.scale b a).c0 →
      s₁.reg .r10 = (EW.scale b a).c1 → RegsFrame Field.sqRegs s s₁ → WP (blk rest) s₁ P E) :
    WP (blk (Field.escale :: rest)) s P E := by
  refine Field.WP.then (Field.escale_spec _) fun s₁ ⟨e1, m1, f1⟩ ↦ ?_
  rw [h9, h10, h11, eOf_eq_toE, mul_comm, ← Equiv.EW.toE_scale] at e1
  obtain ⟨l0, l1⟩ := lanes_of_eOf e1
  exact h s₁ m1 l0 l1 f1

theorem regs_of {l : List Reg64} {s₁ s₂ : QState} (h : RegsFrame l s₁ s₂) {r : Reg64}
    (hr : r ∉ l := by decide) : s₂.reg r = s₁.reg r := h r hr

/-! ## A query's novel evaluation -/

/-- The subspace values at `x`. -/
def whatW (mu : Nat) (x : UInt64) : Array UInt64 := subspaceAtTable (subspaceTable mu) x

theorem whatW_size (mu : Nat) (x : UInt64) : (whatW mu x).size = mu + 1 := by
  rw [whatW, subspaceAtTable_size, subspaceTable_size]

/-- `what` at `whatO`, then `(r9, r10) := novelEval cs what`, the query at word `cI`. -/
def qNovel : Stmt := blk [
  ldw .rcx cI, I (.load .rsi (ix .rbp .rcx (queriesR.off + 1))),
  leaw .r13 tabO, ldw .r15 cMu, I (.addi .r15 1), leaw .r14 whatO, subAtC,
  ldW, leaw .r13 hiO, ldw .r15 cJ, leaw .rsi whatO, ldw .rdx cMu, I (.addi .rdx 1),
  leaw .rbx novO, novelEvalC, ldW]

theorem qNovel_spec {t : QState} {F : QState → Prop} {N mu i : Nat} {x : UInt64} {cs : Array EW}
    (hrdi : t.reg .rdi = env.ctx) (hwp : t.mem (wd env.ctx ctxWork) = some env.work)
    (hne : ∀ k < N, wd env.ctx ctxWork ≠ wd env.work k)
    (hbp : t.reg .rbp = env.work) (hf : Fits env.work N) (hN : 85438 ≤ N)
    (hdom : ∀ k < N, (t.mem (wd env.work k)).isSome)
    (hi : t.mem (wd env.work cI) = some i.toUInt64)
    (hx : t.mem (wd env.work (queriesR.off + 1 + i)) = some x)
    (hmu : NatAt t.mem (wd env.work cMu) mu) (hmu30 : mu ≤ 30)
    (hT : TableAt t.mem (wd env.work tabO) (subspaceTable mu))
    (hcs : EWArr t.mem (wd env.work hiO) cs) (hcn : NatAt t.mem (wd env.work cJ) cs.size)
    (hcs64 : cs.size ≤ 64) :
    WP qNovel t (fun t' ↦ t'.reg .r9 = (novelEval cs (whatW mu x)).c0 ∧
      t'.reg .r10 = (novelEval cs (whatW mu x)).c1 ∧ t'.reg .rbp = env.work ∧
      t'.reg .rdi = env.ctx ∧
      t'.mem (wd env.work (whatO + mu)) = some ((whatW mu x).getD mu 0) ∧
      KeepH env.work t.mem t'.mem ∧ DomEq t.mem t'.mem) F := by
  have hN61 : N ≤ 2 ^ 61 := by unfold Fits at hf; omega
  have hts := subspaceTable_size mu
  have hws := whatW_size mu x
  unfold qNovel
  refine ldw_wp hbp hi ?_
  refine ldi_wp (i := i) (k := queriesR.off + 1) (j := queriesR.off + 1 + i) (by rsimp; exact hbp)
    (by rsimp) (by omega)
    (by rsimp; exact hx) ?_
  refine leaw_wp (env := env) (by rsimp; exact hbp) ?_
  refine ldw_wp (env := env) (by rsimp; exact hbp) (by rsimp; exact hmu.2) ?_
  fstep
  refine leaw_wp (env := env) (by rsimp; exact hbp) ?_
  refine kernel_wp (by decide) (subAtC_spec (tb := subspaceTable mu) (T := wd env.work tabO)
    (D := wd env.work whatO) (x := x) hT (by rsimp)
    (by rsimp; rw [hts, NativeVm.Transcript.toUInt64_succ]) (by rsimp) (by rsimp) (by omega)
    (fun k hk ↦ by rw [wd_wd]; exact hdom _ (by rw [hts] at hk; bomega))
    (fitW hf hN (by bomega) (by rw [hts]; bomega)) (fitW hf hN (by bomega) (by rw [hts]; bomega))
    (disjW hf hN (by bomega) (by bomega) (by rw [hts]; bomega))) fun t₁ ⟨a1, a2, _⟩ d1 r1 ↦ ?_
  rsimp at a2 d1 r1
  have k1 : KeepH env.work t.mem t₁.mem := KeepH.buf (KeepH.refl _ _) a2 (by rw [hts]; bomega)
  have g1 : ∀ j, (j < whatO ∨ foldO + 256 ≤ j) → j < 2 ^ 61 →
      t₁.mem (wd env.work j) = t.mem (wd env.work j) := fun j hj hj' ↦ k1.get hj hj'
  refine ldW_wp (env := env) (r1.trans hrdi) (by
    rw [a2 _ fun k hk ↦ by rw [wd_wd]; exact hne _ (by rw [hts] at hk; bomega)]; exact hwp) ?_
  refine leaw_wp (env := env) (by rsimp) ?_
  refine ldw_wp (env := env) (by rsimp) (by rsimp; rw [g1 _ (by bomega) (by bomega)]; exact hcn.2) ?_
  refine leaw_wp (env := env) (by rsimp) ?_
  refine ldw_wp (env := env) (by rsimp) (by rsimp; rw [g1 _ (by bomega) (by bomega)]; exact hmu.2) ?_
  fstep
  refine leaw_wp (env := env) (by rsimp) ?_
  refine kernel_wp (by decide) (novelEvalC_spec (cs := cs) (what := whatW mu x)
    (C := wd env.work hiO) (Wp := wd env.work whatO) (B := wd env.work novO)
    (hcs.congr (k1.same (n := 128) (by bomega) (by bomega)) (by omega)) (by rsimp)
    (by rsimp) hcs64 (by rsimp; exact a1) (by rsimp)
    (by rsimp; rw [hws, NativeVm.Transcript.toUInt64_succ]) (by omega) (by rsimp)
    (fun k hk ↦ by
      rsimp; rw [wd_wd]; exact (d1 _).trans (hdom _ (by simp only [novelBufWords] at hk; bomega)))
    (fitW hf hN (by bomega) (by simp only [novelBufWords]; bomega))
    (fitW hf hN (by bomega) (by bomega)) (fitW hf hN (by bomega) (by rw [hws]; bomega))
    (disjW hf hN (by bomega) (by bomega) (by simp only [novelBufWords]; bomega))
    (disjW hf hN (by bomega) (by bomega) (by simp only [novelBufWords]; rw [hws]; bomega)))
    fun t₂ ⟨b1, b2, b3⟩ d2 r2 ↦ ?_
  rsimp at b3 d2 r2
  have k2 : KeepH env.work t.mem t₂.mem := KeepH.buf k1 b3 (by simp only [novelBufWords]; bomega)
  refine ldW_wp (env := env) (r2.trans (r1.trans hrdi)) (by
    rw [b3 _ fun k hk ↦ by rw [wd_wd]; exact hne _ (by simp only [novelBufWords] at hk; bomega),
      a2 _ fun k hk ↦ by rw [wd_wd]; exact hne _ (by rw [hts] at hk; bomega)]; exact hwp) ?_
  apply WP.blk_nil
  refine ⟨by rsimp; exact b1, by rsimp; exact b2, by rsimp, by rsimp; exact r2.trans (r1.trans hrdi),
    ?_, k2, d1.trans d2⟩
  rsimp
  rw [b3 _ fun k hk e ↦ by
      rw [wd_wd] at e
      have := (wd_inj (by bomega) (by simp only [novelBufWords] at hk; bomega)).mp e
      simp only [novelBufWords] at hk; bomega,
    ← wd_wd, a1 mu (by rw [subspaceAtTable_size]; omega)]
  rw [Array.getElem_eq_getD 0]
  rfl

/-! ## A query's fold -/

/-- `(r9, r10) := foldRow (lanesW index row) x rs`, the row at the address in `tmpO + 18`. -/
def qFold : Stmt := blk [
  ldw .rcx cI, I (.load .rsi (ix .rbp .rcx (queriesR.off + 1))),
  ldw .r13 (tmpO + 18), ldw .r15 (tmpO + 24), ldw .rdx cIdx, leaw .r14 roundsR.off,
  leaw .rbx foldO, foldRowC, ldW]

theorem qFold_spec {t : QState} {F : QState → Prop} {N index i ro : Nat} {x : UInt64}
    {row : Array UInt64} {rs : Array FoldRoundW}
    (hrdi : t.reg .rdi = env.ctx) (hwp : t.mem (wd env.ctx ctxWork) = some env.work)
    (hne : ∀ k < N, wd env.ctx ctxWork ≠ wd env.work k)
    (hbp : t.reg .rbp = env.work) (hf : Fits env.work N) (hN : 85438 ≤ N)
    (hdom : ∀ k < N, (t.mem (wd env.work k)).isSome)
    (hi : t.mem (wd env.work cI) = some i.toUInt64)
    (hx : t.mem (wd env.work (queriesR.off + 1 + i)) = some x)
    (hp : t.mem (wd env.work (tmpO + 18)) = some (wd env.work ro))
    (hrow : WordArr t.mem (wd env.work ro) row)
    (hro' : ro + row.size ≤ scratchR.off)
    (hw : t.mem (wd env.work (tmpO + 24)) = some row.size.toUInt64) (hrow64 : row.size ≤ 64)
    (hidx : NatAt t.mem (wd env.work cIdx) index)
    (hR : RoundsAt t.mem (wd env.work roundsR.off) rs) :
    WP qFold t (fun t' ↦ t'.reg .r9 = (foldRow (lanesW index row) x rs).c0 ∧
      t'.reg .r10 = (foldRow (lanesW index row) x rs).c1 ∧ t'.reg .rbp = env.work ∧
      t'.reg .rdi = env.ctx ∧ KeepH env.work t.mem t'.mem ∧ DomEq t.mem t'.mem) F := by
  have hN61 : N ≤ 2 ^ 61 := by unfold Fits at hf; omega
  unfold qFold
  refine ldw_wp hbp hi ?_
  refine ldi_wp (i := i) (k := queriesR.off + 1) (j := queriesR.off + 1 + i) (by rsimp; exact hbp)
    (by rsimp) (by omega) (by rsimp; exact hx) ?_
  refine ldw_wp (env := env) (by rsimp; exact hbp) (by rsimp; exact hp) ?_
  refine ldw_wp (env := env) (by rsimp; exact hbp) (by rsimp; exact hw) ?_
  refine ldw_wp (env := env) (by rsimp; exact hbp) (by rsimp; exact hidx.2) ?_
  refine leaw_wp (env := env) (by rsimp; exact hbp) ?_
  refine leaw_wp (env := env) (by rsimp; exact hbp) ?_
  refine kernel_wp (by decide) (foldRowC_spec (row := row) (rs := rs) (index := index)
    (R := wd env.work ro) (Rd := wd env.work roundsR.off) (A := wd env.work foldO) (x := x)
    hrow (by rsimp) (by rsimp) hrow64 (by rsimp) hidx.1 (by rsimp) hR (by rsimp) (by rsimp)
    (fun k hk ↦ by
      rsimp; rw [wd_wd]; exact hdom _ (by simp only [foldBufWords] at hk; bomega))
    (fitW hf hN (by bomega) (by simp only [foldBufWords]; bomega))
    (fitW hf hN (by bomega) (by bomega))
    (fitW hf hN (by bomega) (by simp only [roundsWords_val]; bomega))
    (disjW hf hN (by bomega) (by bomega) (by simp only [foldBufWords]; bomega))
    (disjW hf hN (by bomega) (by bomega) (by simp only [foldBufWords, roundsWords_val]; bomega)))
    fun t₁ ⟨a1, a2, a3⟩ d1 r1 ↦ ?_
  rsimp at a3 d1 r1
  refine ldW_wp (env := env) (r1.trans hrdi) (by
    rw [a3 _ fun k hk ↦ by rw [wd_wd]; exact hne _ (by simp only [foldBufWords] at hk; bomega)]
    exact hwp) ?_
  apply WP.blk_nil
  refine ⟨by rsimp; exact a1, by rsimp; exact a2, by rsimp, by rsimp; exact r1.trans hrdi,
    by rsimp; exact KeepH.buf (KeepH.refl _ _) a3 (by simp only [foldBufWords]; bomega), d1⟩

/-! ## The loop's state -/

/-- The next query: the row's address advanced by the width, the index by one; `rax` the index,
`rcx` the count. -/
def qNext : Stmt := blk [
  ldw .rax (tmpO + 24), I (.shli .rax 3), ldw .rbx (tmpO + 18), I (.add .rbx .rax),
  stw (tmpO + 18) .rbx, ldw .rax cI, I (.addi .rax 1), stw cI .rax, ldw .rcx queriesR.off]

/-- The loop's start: index `0`, the first row; `rax` the index, `rcx` the count. -/
def qInit : Stmt := blk [
  stwi cI 0, leaw .rax rowsR.off, stw (tmpO + 18) .rax, I (.movi .rax 0), ldw .rcx queriesR.off]

/-- What `qNext` and `qInit` leave. -/
structure Step (W : UInt64) (t t' : QState) (n i ro : Nat) : Prop where
  rax : t'.reg .rax = i.toUInt64
  rcx : t'.reg .rcx = n.toUInt64
  rbp : t'.reg .rbp = W
  rdi : t'.reg .rdi = t.reg .rdi
  idx : t'.mem (wd W cI) = some i.toUInt64
  row : t'.mem (wd W (tmpO + 18)) = some (wd W ro)
  keep : ∀ j, j ≠ cI → j ≠ tmpO + 18 → j < 2 ^ 61 → t'.mem (wd W j) = t.mem (wd W j)
  keepB : KeepB W t.mem t'.mem
  dom : DomEq t.mem t'.mem

theorem qNext_spec {t : QState} {F : QState → Prop} {n i ro w : Nat}
    (hbp : t.reg .rbp = env.work) (hd0 : (t.mem (wd env.work cI)).isSome)
    (hd1 : (t.mem (wd env.work (tmpO + 18))).isSome)
    (hi : t.mem (wd env.work cI) = some i.toUInt64)
    (hp : t.mem (wd env.work (tmpO + 18)) = some (wd env.work ro))
    (hw : t.mem (wd env.work (tmpO + 24)) = some w.toUInt64)
    (hn : t.mem (wd env.work queriesR.off) = some n.toUInt64) :
    WP qNext t (fun t' ↦ Step env.work t t' n (i + 1) (ro + w)) F := by
  have n18 : wd env.work cI ≠ wd env.work (tmpO + 18) := wd_ne (by bomega) (by bomega) (by bomega)
  have nq0 : wd env.work queriesR.off ≠ wd env.work cI := wd_ne (by bomega) (by bomega) (by bomega)
  have nq1 : wd env.work queriesR.off ≠ wd env.work (tmpO + 18) :=
    wd_ne (by bomega) (by bomega) (by bomega)
  unfold qNext
  refine ldw_wp hbp hw ?_
  fstep [FR.shl3]
  refine ldw_wp (env := env) (by rsimp; exact hbp) (by rsimp; exact hp) ?_
  fstep [NativeVm.Transcript.wd_add]
  refine stw_wp (env := env) (by rsimp; exact hbp) (by rsimp; exact hd1) ?_
  refine ldw_wp (env := env) (by rsimp; exact hbp)
    (by simp only [QState.setReg_mem, QState.setMem_mem, n18, ite_false]; exact hi) ?_
  fstep [NativeVm.Transcript.toUInt64_succ]
  refine stw_wp (env := env) (by rsimp; exact hbp)
    (by simp only [QState.setReg_mem, QState.setMem_mem, n18, ite_false]; exact hd0) ?_
  refine ldw_wp (env := env) (by rsimp; exact hbp)
    (by simp only [QState.setReg_mem, QState.setMem_mem, nq0, nq1, ite_false]; exact hn) ?_
  apply WP.blk_nil
  refine ⟨by rsimp, by rsimp, by rsimp; exact hbp, by rsimp, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [QState.setReg_mem, QState.setMem_mem, ite_true]
    rsimp
  · simp only [QState.setReg_mem, QState.setMem_mem, n18.symm, ite_false, ite_true]
  · intro j h1 h2 hj
    have m1 : wd env.work j ≠ wd env.work cI := wd_ne h1 hj (by bomega)
    have m2 : wd env.work j ≠ wd env.work (tmpO + 18) := wd_ne h2 hj (by bomega)
    simp only [QState.setReg_mem, QState.setMem_mem, m1, m2, ite_false]
  · intro a ha
    simp only [QState.setReg_mem, QState.setMem_mem, ha cI WB_cI, ha (tmpO + 18) WB_18, ite_false]
  · intro a
    simp only [QState.setReg_mem, QState.setMem_mem]
    by_cases e1 : a = wd env.work cI
    · subst e1; simp [hd0]
    · by_cases e2 : a = wd env.work (tmpO + 18)
      · subst e2; simp [hd1, n18.symm]
      · simp [e1, e2]

theorem qInit_spec {t : QState} {F : QState → Prop} {n : Nat}
    (hbp : t.reg .rbp = env.work) (hd0 : (t.mem (wd env.work cI)).isSome)
    (hd1 : (t.mem (wd env.work (tmpO + 18))).isSome)
    (hn : t.mem (wd env.work queriesR.off) = some n.toUInt64) :
    WP qInit t (fun t' ↦ Step env.work t t' n 0 rowsR.off) F := by
  have n18 : wd env.work cI ≠ wd env.work (tmpO + 18) := wd_ne (by bomega) (by bomega) (by bomega)
  have nq0 : wd env.work queriesR.off ≠ wd env.work cI := wd_ne (by bomega) (by bomega) (by bomega)
  have nq1 : wd env.work queriesR.off ≠ wd env.work (tmpO + 18) :=
    wd_ne (by bomega) (by bomega) (by bomega)
  unfold qInit
  refine stwi0_wp hbp hd0 ?_
  refine leaw_wp (env := env) (by rsimp; exact hbp) ?_
  refine stw_wp (env := env) (by rsimp; exact hbp)
    (by simp only [QState.setReg_mem, QState.setMem_mem, n18.symm, ite_false]; exact hd1) ?_
  fstep
  refine ldw_wp (env := env) (by rsimp; exact hbp)
    (by simp only [QState.setReg_mem, QState.setMem_mem, nq0, nq1, ite_false]; exact hn) ?_
  apply WP.blk_nil
  refine ⟨by rsimp; rfl, by rsimp, by rsimp; exact hbp, by rsimp, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [QState.setReg_mem, QState.setMem_mem, n18, ite_false, ite_true]; rfl
  · simp only [QState.setReg_mem, QState.setMem_mem, ite_true]
  · intro j h1 h2 hj
    have m1 : wd env.work j ≠ wd env.work cI := wd_ne h1 hj (by bomega)
    have m2 : wd env.work j ≠ wd env.work (tmpO + 18) := wd_ne h2 hj (by bomega)
    simp only [QState.setReg_mem, QState.setMem_mem, m1, m2, ite_false]
  · intro a ha
    simp only [QState.setReg_mem, QState.setMem_mem, ha cI WB_cI, ha (tmpO + 18) WB_18, ite_false]
  · intro a
    simp only [QState.setReg_mem, QState.setMem_mem]
    by_cases e1 : a = wd env.work cI
    · subst e1; simp [hd0, n18]
    · by_cases e2 : a = wd env.work (tmpO + 18)
      · subst e2; simp [hd1]
      · simp [e1, e2]

/-! ## Two stores, the frames -/

/-- `word k := r9`, `word k' := r10`. -/
theorem st2_wp {k k' : Nat} (hW : s.reg .rbp = env.work) (hkk : k ≠ k') (hk : k < 2 ^ 61)
    (hk' : k' < 2 ^ 61) (h0 : (s.mem (wd env.work k)).isSome)
    (h1 : (s.mem (wd env.work k')).isSome)
    (h : ∀ s₁ : QState, s₁.reg = s.reg →
      (∀ a, a ≠ wd env.work k → a ≠ wd env.work k' → s₁.mem a = s.mem a) →
      s₁.mem (wd env.work k) = some (s.reg .r9) → s₁.mem (wd env.work k') = some (s.reg .r10) →
      DomEq s.mem s₁.mem → WP (blk rest) s₁ P E) :
    WP (blk (stw k .r9 :: stw k' .r10 :: rest)) s P E := by
  have ne : wd env.work k ≠ wd env.work k' := wd_ne hkk hk hk'
  refine stw_wp hW h0 (stw_wp (by rsimp; exact hW) (by
    simp only [QState.setMem_mem, ne.symm, ite_false]; exact h1) ?_)
  have e0 : ((s.setMem (wd env.work k) (s.reg .r9)).setMem (wd env.work k') (s.reg .r10)).mem
      (wd env.work k') = some (s.reg .r10) := by
    simp only [QState.setMem_mem, ite_true]
  refine h _ rfl (fun a h1 h2 ↦ by simp only [QState.setMem_mem, h1, h2, ite_false])
    (by simp only [QState.setMem_mem, ne, ite_false, ite_true]) e0 fun a ↦ ?_
  simp only [QState.setMem_mem]
  by_cases e1 : a = wd env.work k'
  · subst e1; simp [h1]
  · by_cases e2 : a = wd env.work k
    · subst e2; simp [h0, e1]
    · simp [e1, e2]

theorem WB_mine {k : Nat} (h : WB k) : mineLo ≤ k ∧ k < dataEnd := by
  simp only [mineLo_val, dataEnd_val]; bomega

/-- The words kept and the words existing give the frame. -/
theorem KeepB.frM {s s' : QState} (hk : KeepB env.work s.mem s'.mem) (hd : DomEq s.mem s'.mem)
    (hr : s'.reg .rdi = s.reg .rdi) : FrM env s s' :=
  ⟨hr, hd, fun a ha ↦ hk a fun k hk e ↦ ha ⟨k, (WB_mine hk).1, (WB_mine hk).2, e⟩⟩

theorem KeepB.only (hk : KeepB env.work m₁ m₂) : Only env WB m₁ m₂ :=
  fun k _ h2 hk' ↦ hk.get hk' (by rw [dataEnd_val] at h2; omega)

/-! ## The inputs -/

theorem TableAt.congr' {tb : Array (UInt64 × UInt64)} {p : UInt64} (h : Same m₁ m₂ p (2 * tb.size))
    (ht : TableAt m₁ p tb) : TableAt m₂ p tb := fun i hi ↦
  ⟨h.word (by omega) (ht i hi).1, h.word (by omega) (ht i hi).2⟩

theorem rowsWords_val : rowsWords = 16384 := by decide

/-- What both loops read, in the state they start from. -/
structure Ctx (p : Par) (s : QState) (index mu width : Nat) (rs : Array FoldRoundW)
    (cs : Array EW) (qs : Array UInt64) (rows : Array (Array UInt64)) : Prop where
  rdi : s.reg .rdi = p.env.ctx
  inp : Inputs p.env p.inp s.mem
  wp : s.mem (wd p.env.ctx ctxWork) = some p.env.work
  hIdx : NatAt s.mem (wd p.env.work cIdx) index
  hMu : NatAt s.mem (wd p.env.work cMu) mu
  mu30 : mu ≤ 30
  hQ : WVec s.mem (wd p.env.work queriesR.off) queryCap qs
  hRows : RowsAt s.mem (wd p.env.work rowsR.off) width rows
  rsz : rows.size = qs.size
  wid : width ≤ 64
  widw : NatAt s.mem (wd p.env.work (tmpO + 24)) width
  hR : RoundsAt s.mem (wd p.env.work roundsR.off) rs
  hCs : EWArr s.mem (wd p.env.work hiO) cs
  csz : cs.size ≤ 64
  csn : NatAt s.mem (wd p.env.work cJ) cs.size
  hT : TableAt s.mem (wd p.env.work tabO) (subspaceTable mu)

/-- The loop's words at a state `u` from the start `s`, at query `i`. -/
structure Loop (p : Par) (s u : QState) (width i : Nat) : Prop where
  rbp : u.reg .rbp = p.env.work
  rdi : u.reg .rdi = p.env.ctx
  idx : u.mem (wd p.env.work cI) = some i.toUInt64
  row : u.mem (wd p.env.work (tmpO + 18)) = some (wd p.env.work (rowsR.off + width * i))
  keep : KeepB p.env.work s.mem u.mem
  dom : DomEq s.mem u.mem

variable {p : Par} {index mu width : Nat} {rs : Array FoldRoundW} {cs : Array EW}
  {qs : Array UInt64} {rows : Array (Array UInt64)}

theorem Ctx.N (_c : Ctx p s index mu width rs cs qs rows) :
    85438 ≤ workWords p.inp.bytecode.size := workWords_ge _

theorem Ctx.ne (c : Ctx p s index mu width rs cs qs rows) :
    ∀ k < workWords p.inp.bytecode.size, wd p.env.ctx ctxWork ≠ wd p.env.work k :=
  fun _ hk ↦ c.inp.ctx_ne_work (by decide) hk

theorem Ctx.ctxw (c : Ctx p s index mu width rs cs qs rows) {u : QState}
    (hk : KeepB p.env.work s.mem u.mem) : u.mem (wd p.env.ctx ctxWork) = some p.env.work := by
  rw [hk _ fun k hk' ↦ c.ne k (by have := c.N; have := WB_lt hk'; bomega)]
  exact c.wp

theorem Ctx.dom (c : Ctx p s index mu width rs cs qs rows) {u : QState}
    (hd : DomEq s.mem u.mem) : ∀ k < workWords p.inp.bytecode.size,
      (u.mem (wd p.env.work k)).isSome :=
  fun k hk ↦ (hd _).trans (c.inp.workSome k hk)

theorem Ctx.qsz (c : Ctx p s index mu width rs cs qs rows) : qs.size ≤ 230 := c.hQ.1

theorem Ctx.query (c : Ctx p s index mu width rs cs qs rows) {u : QState}
    (hk : KeepB p.env.work s.mem u.mem) {i : Nat} (hi : i < qs.size) :
    u.mem (wd p.env.work (queriesR.off + 1 + i)) = some (qs.getD i 0) := by
  have hq := c.qsz
  rw [hk.get (by bomega) (by bomega), ← wd_wd, ← wd_wd, c.hQ.2.2 i hi, Array.getElem_eq_getD 0]

theorem Ctx.count (c : Ctx p s index mu width rs cs qs rows) {u : QState}
    (hk : KeepB p.env.work s.mem u.mem) :
    u.mem (wd p.env.work queriesR.off) = some qs.size.toUInt64 := by
  rw [hk.get (by bomega) (by bomega)]
  exact c.hQ.2.1.2

/-- **A query's novel evaluation**, from the loop's state. -/
theorem Ctx.novel (c : Ctx p s index mu width rs cs qs rows) {u : QState} {F : QState → Prop}
    {i : Nat} (hl : Loop p s u width i) (hi : i < qs.size) :
    WP qNovel u (fun t' ↦ t'.reg .r9 = (novelEval cs (whatW mu (qs.getD i 0))).c0 ∧
      t'.reg .r10 = (novelEval cs (whatW mu (qs.getD i 0))).c1 ∧ t'.reg .rbp = p.env.work ∧
      t'.reg .rdi = p.env.ctx ∧
      t'.mem (wd p.env.work (whatO + mu)) = some ((whatW mu (qs.getD i 0)).getD mu 0) ∧
      KeepH p.env.work u.mem t'.mem ∧ DomEq u.mem t'.mem) F := by
  have hk := hl.keep
  have ts := subspaceTable_size mu
  have := c.mu30
  have := c.csz
  exact qNovel_spec hl.rdi (c.ctxw hk) c.ne hl.rbp c.inp.fitWork c.N (c.dom hl.dom) hl.idx
    (c.query hk hi) (c.hMu.congr (hk.get (by bomega) (by bomega)))
    c.mu30 (TableAt.congr' (hk.same (by intro j hj; rw [ts] at hj; bomega)
      (by rw [ts]; bomega)) c.hT)
    (c.hCs.congr (hk.same (n := 128) (by intro j hj; bomega) (by bomega)) (by omega))
    (c.csn.congr (hk.get (by bomega) (by bomega))) c.csz

/-- **A query's fold**, from a state keeping the start's words but `WB`. -/
theorem Ctx.fold (c : Ctx p s index mu width rs cs qs rows) {v : QState} {F : QState → Prop}
    {i : Nat} (hbp : v.reg .rbp = p.env.work) (hrdi : v.reg .rdi = p.env.ctx)
    (hk : KeepB p.env.work s.mem v.mem) (hd : DomEq s.mem v.mem)
    (hix : v.mem (wd p.env.work cI) = some i.toUInt64)
    (hrow : v.mem (wd p.env.work (tmpO + 18)) = some (wd p.env.work (rowsR.off + width * i)))
    (hi : i < qs.size) :
    WP qFold v (fun t' ↦
      t'.reg .r9 = (foldRow (lanesW index (rows.getD i #[])) (qs.getD i 0) rs).c0 ∧
      t'.reg .r10 = (foldRow (lanesW index (rows.getD i #[])) (qs.getD i 0) rs).c1 ∧
      t'.reg .rbp = p.env.work ∧ t'.reg .rdi = p.env.ctx ∧ KeepH p.env.work v.mem t'.mem ∧
      DomEq v.mem t'.mem) F := by
  have hir : i < rows.size := by rw [c.rsz]; exact hi
  obtain ⟨hsz, hwa⟩ := c.hRows.2 i hir
  have hg : rows.getD i #[] = rows[i] := (Array.getElem_eq_getD _).symm
  have hmul : width * i + width ≤ rows.size * width := by
    rw [Nat.mul_comm rows.size, ← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hir
  have hrw := c.hRows.1
  rw [rowsWords_val] at hrw
  have := c.wid
  rw [hg]
  refine qFold_spec (ro := rowsR.off + width * i) hrdi (c.ctxw hk) c.ne hbp c.inp.fitWork c.N
    (c.dom hd) hix (c.query hk hi) hrow ?_ (by rw [hsz]; bomega)
    (by rw [hsz, hk.get (by bomega) (by bomega)]; exact c.widw.2) (by omega)
    (c.hIdx.congr (hk.get (by bomega) (by bomega)))
    (c.hR.congr (hk.same (by intro j hj; simp only [roundsWords_val] at hj; bomega)
      (by simp only [roundsWords_val]; bomega)))
  rw [wd_wd] at hwa
  exact hwa.congr (hk.same (o := rowsR.off + width * i) (n := width) (by intro j hj; bomega)
    (by bomega)) (by omega)

/-! ## The model, query by query -/

/-- Query `i`'s term of `batchedW`. -/
def termB (index mu : Nat) (rs : Array FoldRoundW) (high : Array EW) (qs : Array UInt64)
    (rows : Array (Array UInt64)) (qw : Array EW) (i : Nat) : EW :=
  qw.getD i 0 * (foldRow (lanesW index (rows.getD i #[])) (qs.getD i 0) rs +
    EW.scale ((whatW mu (qs.getD i 0)).getD mu 0) (novelEval high (whatW mu (qs.getD i 0))))

/-- The first `n` terms' sum. -/
def accB (index mu : Nat) (rs : Array FoldRoundW) (high : Array EW) (qs : Array UInt64)
    (rows : Array (Array UInt64)) (qw : Array EW) (n : Nat) : EW :=
  ((List.range n).map (termB index mu rs high qs rows qw)).foldl (· + ·) 0

theorem accB_succ {high qw : Array EW} (n : Nat) :
    accB index mu rs high qs rows qw (n + 1) =
      accB index mu rs high qs rows qw n + termB index mu rs high qs rows qw n := by
  simp only [accB, List.range_succ, List.map_append, List.foldl_append, List.map_cons,
    List.map_nil, List.foldl_cons, List.foldl_nil]

theorem accB_zero {high qw : Array EW} : accB index mu rs high qs rows qw 0 = 0 := rfl

theorem batchedW_eq {high qw : Array EW} (h1 : rows.size = qs.size) (h2 : qw.size = qs.size) :
    batchedW index mu rs high qs rows qw = accB index mu rs high qs rows qw qs.size := by
  unfold batchedW accB sumE
  rw [← Array.foldl_toList]
  congr 1
  apply List.ext_getElem
  · simp [h1, h2]
  · intro j hj hj'
    simp only [List.length_map, List.length_range] at hj'
    simp [termB, whatW, Array.getD_eq_getD_getElem?, hj', h1 ▸ hj', h2 ▸ hj']

/-- Query `i`'s final check. -/
def okF (index mu : Nat) (rs : Array FoldRoundW) (folded : Array EW) (qs : Array UInt64)
    (rows : Array (Array UInt64)) (i : Nat) : Prop :=
  foldRow (lanesW index (rows.getD i #[])) (qs.getD i 0) rs =
    novelEval folded (whatW mu (qs.getD i 0))

theorem finalOkW_iff {folded : Array EW} (h1 : rows.size = qs.size) :
    finalOkW index mu rs folded qs rows = true ↔ ∀ i < qs.size, okF index mu rs folded qs rows i := by
  unfold finalOkW okF
  rw [Array.all_eq_true]
  constructor
  · intro h i hi
    have := h i (by simp [h1, hi])
    simpa [whatW, Array.getD_eq_getD_getElem?, hi, h1 ▸ hi] using this
  · intro h i hi
    simp only [Array.size_zip, h1, Nat.min_self] at hi
    have := h i hi
    simpa [whatW, Array.getD_eq_getD_getElem?, hi, h1 ▸ hi] using this

/-! ## The batched value -/

theorem KeepB.st2 {u u' : QState} (h : KeepB W m u.mem) {k k' : Nat} (hk : WB k) (hk' : WB k')
    (hm : ∀ a, a ≠ wd W k → a ≠ wd W k' → u'.mem a = u.mem a) : KeepB W m u'.mem :=
  fun a ha ↦ (hm a (ha k hk) (ha k' hk')).trans (h a ha)

theorem term_eq (f sc w acc : EW) : (f + sc) * w + acc = acc + w * (f + sc) := by
  apply Equiv.EW.toE_injective
  simp only [Equiv.EW.toE_add, Equiv.EW.toE_mul]
  ring

/-- One query of the batch: `w · (fold + what[μ] · novel)` added to `tmpO + 16`. -/
def batchBody : Stmt := blk [
  qNovel, ldw .rcx cMu, I (.load .r11 (ix .rbp .rcx whatO)), Field.escale,
  stw (tmpO + 20) .r9, stw (tmpO + 21) .r10, qFold,
  ldw .r11 (tmpO + 20), ldw .r12 (tmpO + 21), Field.eadd,
  ldw .rcx cI, I (.shli .rcx 1), ldw .r8 cK, I (.load .r11 (ix .r8 .rcx 0)),
  I (.load .r12 (ix .r8 .rcx 1)), Field.emul,
  ldw .r11 (tmpO + 16), ldw .r12 (tmpO + 17), Field.eadd,
  stw (tmpO + 16) .r9, stw (tmpO + 17) .r10, qNext]

theorem batchBody_spec {F : QState → Prop} {qw : Array EW} {qo i : Nat}
    (c : Ctx p s index mu width rs cs qs rows)
    (hqo : s.mem (wd p.env.work cK) = some (wd p.env.work qo)) (hqw : EWArr s.mem (wd p.env.work qo) qw)
    (hqws : qw.size = qs.size) (hqoR : whirR.off ≤ qo ∧ qo + 2 * qw.size ≤ whirR.off + whirWords)
    {u : QState} (hl : Loop p s u width i)
    (ha : EWAt u.mem (wd p.env.work (tmpO + 16)) (accB index mu rs cs qs rows qw i))
    (hi : i < qs.size) :
    WP batchBody u (fun u' ↦ Loop p s u' width (i + 1) ∧
      EWAt u'.mem (wd p.env.work (tmpO + 16)) (accB index mu rs cs qs rows qw (i + 1)) ∧
      u'.reg .rax = (i + 1).toUInt64 ∧ u'.reg .rcx = qs.size.toUInt64) F := by
  have hq := c.qsz
  have hm30 := c.mu30
  have hws := whatW_size mu (qs.getD i 0)
  unfold batchBody
  -- the novel evaluation
  refine Field.WP.then (c.novel hl hi) fun u₁ ⟨n9, n10, nbp, nrdi, nw, nk, nd⟩ ↦ ?_
  have k1 : KeepB p.env.work s.mem u₁.mem := hl.keep.trans nk.toB
  refine ldw_wp nbp (by rw [k1.get (by bomega) (by bomega)]; exact c.hMu.2) ?_
  refine ldi_wp (i := mu) (k := whatO) (j := whatO + mu) (by rsimp; exact nbp) (by rsimp)
    (Nat.add_comm _ _) (by rsimp; exact nw) ?_
  refine escale_k (a := novelEval cs (whatW mu (qs.getD i 0)))
    (b := (whatW mu (qs.getD i 0)).getD mu 0) (by rsimp; exact n9) (by rsimp; exact n10) (by rsimp)
    fun u₂ m2 e9 e10 f2 ↦ ?_
  rsimp at m2
  have b2 : u₂.reg .rbp = p.env.work := by rw [regs_of f2]; rsimp; exact nbp
  have i2 : u₂.reg .rdi = p.env.ctx := by rw [regs_of f2]; rsimp; exact nrdi
  have d2 : DomEq s.mem u₂.mem := fun a ↦ by rw [m2]; exact (nd a).trans (hl.dom a)
  refine st2_wp (k := tmpO + 20) (k' := tmpO + 21) b2 (by omega) (by bomega) (by bomega)
    (c.dom d2 _ (by have := c.N; bomega)) (c.dom d2 _ (by have := c.N; bomega))
    fun u₃ r3 m3 w20 w21 d3 ↦ ?_
  have k3 : KeepB p.env.work s.mem u₃.mem :=
    KeepB.st2 (fun a ha ↦ by rw [m2]; exact k1 a ha) (.inr (.inl ⟨by omega, by omega⟩))
      (.inr (.inl ⟨by omega, by omega⟩)) m3
  have g3 : ∀ j, (j < whatO ∨ foldO + 256 ≤ j) → j ≠ tmpO + 20 → j ≠ tmpO + 21 → j < 2 ^ 61 →
      u₃.mem (wd p.env.work j) = u.mem (wd p.env.work j) := fun j h1 h2 h3 h4 ↦ by
    rw [m3 _ (wd_ne h2 h4 (by bomega)) (wd_ne h3 h4 (by bomega)), m2, nk.get h1 h4]
  -- the fold
  refine Field.WP.then (c.fold (i := i) (by rw [r3]; exact b2) (by rw [r3]; exact i2) k3
    (d2.trans d3) (by rw [g3 _ (by bomega) (by bomega) (by bomega) (by bomega)]; exact hl.idx)
    (by rw [g3 _ (by bomega) (by bomega) (by bomega) (by bomega)]; exact hl.row) hi)
    fun u₄ ⟨f9, f10, fbp, frdi, fk, fd⟩ ↦ ?_
  have k4 : KeepB p.env.work s.mem u₄.mem := k3.trans fk.toB
  refine ldw_wp fbp (by rw [fk.get (by bomega) (by bomega)]; exact w20) ?_
  refine ldw_wp (env := p.env) (by rsimp; exact fbp)
    (by rsimp; rw [fk.get (by bomega) (by bomega)]; exact w21) ?_
  refine eadd_k (a := foldRow (lanesW index (rows.getD i #[])) (qs.getD i 0) rs)
    (b := EW.scale ((whatW mu (qs.getD i 0)).getD mu 0) (novelEval cs (whatW mu (qs.getD i 0))))
    (by rsimp; exact f9) (by rsimp; exact f10) (by rsimp; exact e9)
    (by rsimp; exact e10) fun u₅ m5 a9 a10 f5 ↦ ?_
  rsimp at m5
  have b5 : u₅.reg .rbp = p.env.work := by rw [regs_of f5]; rsimp; exact fbp
  -- the weight
  refine ldw_wp b5 (by
    rw [m5, fk.get (by bomega) (by bomega), g3 _ (by bomega) (by bomega) (by bomega) (by bomega)]
    exact hl.idx) ?_
  fstep [FR.shl1]
  refine ldw_wp (env := p.env) (by rsimp; exact b5)
    (by rsimp; rw [m5, k4.get (by bomega) (by bomega)]; exact hqo) ?_
  have hii : i < qw.size := by omega
  obtain ⟨w0, w1⟩ := hqw i hii
  rw [wd_wd] at w0 w1
  rw [wd_wd] at w1
  refine ldi_wp (p := wd p.env.work qo) (v := qw[i].c0) (i := 2 * i) (k := 0) (j := 2 * i)
    (by rsimp) (by rsimp) (Nat.add_zero _)
    (by rsimp; rw [m5, wd_wd, k4.get (by bomega) (by bomega)]; exact w0) ?_
  refine ldi_wp (p := wd p.env.work qo) (v := qw[i].c1) (i := 2 * i) (k := 1) (j := 2 * i + 1)
    (by rsimp) (by rsimp) rfl
    (by rsimp; rw [m5, wd_wd, k4.get (by bomega) (by bomega)]; exact w1) ?_
  refine emul_k (b := qw[i]) (by rsimp; exact a9) (by rsimp; exact a10) (by rsimp) (by rsimp)
    fun u₆ m6 c9 c10 f6 ↦ ?_
  rsimp at m6
  have b6 : u₆.reg .rbp = p.env.work := by rw [regs_of f6 (r := .rbp)]; rsimp; exact b5
  -- the sum
  have acc0 : u₆.mem (wd p.env.work (tmpO + 16)) = some (accB index mu rs cs qs rows qw i).c0 := by
    rw [m6, m5, fk.get (by bomega) (by bomega), g3 _ (by bomega) (by bomega) (by bomega) (by bomega)]
    exact ha.1
  have acc1 : u₆.mem (wd p.env.work (tmpO + 17)) = some (accB index mu rs cs qs rows qw i).c1 := by
    rw [m6, m5, fk.get (by bomega) (by bomega), g3 _ (by bomega) (by bomega) (by bomega) (by bomega)]
    have := ha.2
    rwa [wd_wd] at this
  refine ldw_wp b6 acc0 ?_
  refine ldw_wp (env := p.env) (by rsimp; exact b6) (by rsimp; exact acc1) ?_
  refine eadd_k (b := accB index mu rs cs qs rows qw i) (by rsimp; exact c9) (by rsimp; exact c10)
    (by rsimp) (by rsimp)
    fun u₇ m7 s9 s10 f7 ↦ ?_
  rsimp at m7
  have b7 : u₇.reg .rbp = p.env.work := by rw [regs_of f7]; rsimp; exact b6
  have d7 : DomEq s.mem u₇.mem := fun a ↦ by
    rw [m7, m6, m5]; exact (fd a).trans ((d3 a).trans (d2 a))
  refine st2_wp (k := tmpO + 16) (k' := tmpO + 17) b7 (by omega) (by bomega) (by bomega)
    (c.dom d7 _ (by have := c.N; bomega)) (c.dom d7 _ (by have := c.N; bomega))
    fun u₈ r8 m8 v16 v17 d8 ↦ ?_
  have k8 : KeepB p.env.work s.mem u₈.mem :=
    KeepB.st2 (fun a ha ↦ by rw [m7, m6, m5]; exact k4 a ha) (.inr (.inl ⟨by omega, by omega⟩))
      (.inr (.inl ⟨by omega, by omega⟩)) m8
  have g8 : ∀ j, (j < whatO ∨ foldO + 256 ≤ j) → j ≠ tmpO + 16 → j ≠ tmpO + 17 →
      j ≠ tmpO + 20 → j ≠ tmpO + 21 → j < 2 ^ 61 →
      u₈.mem (wd p.env.work j) = u.mem (wd p.env.work j) := fun j h1 h2 h3 h4 h5 h6 ↦ by
    rw [m8 _ (wd_ne h2 h6 (by bomega)) (wd_ne h3 h6 (by bomega)), m7, m6, m5, fk.get h1 h6,
      g3 j h1 h4 h5 h6]
  -- the next query
  refine Field.WP.then (qNext_spec (n := qs.size) (i := i) (ro := rowsR.off + width * i)
    (w := width) (by rw [r8]; exact b7) (c.dom (d7.trans d8) _ (by have := c.N; bomega))
    (c.dom (d7.trans d8) _ (by have := c.N; bomega))
    (by rw [g8 _ (by bomega) (by bomega) (by bomega) (by bomega) (by bomega) (by bomega)]
        exact hl.idx)
    (by rw [g8 _ (by bomega) (by bomega) (by bomega) (by bomega) (by bomega) (by bomega)]
        exact hl.row)
    (by rw [k8.get (by bomega) (by bomega)]; exact c.widw.2) (c.count k8))
    fun u₉ st ↦ ?_
  apply WP.blk_nil
  have rd8 : u₈.reg .rdi = p.env.ctx := by
    rw [r8, regs_of f7 (r := .rdi)]; rsimp; rw [regs_of f6 (r := .rdi)]; rsimp
    rw [regs_of f5 (r := .rdi)]; rsimp; exact frdi
  refine ⟨⟨st.rbp, st.rdi.trans rd8, st.idx, ?_, k8.trans st.keepB, (d7.trans d8).trans st.dom⟩,
    ?_, st.rax, st.rcx⟩
  · rw [st.row, Nat.mul_succ, Nat.add_assoc]
  · have e : accB index mu rs cs qs rows qw (i + 1) =
        (foldRow (lanesW index (rows.getD i #[])) (qs.getD i 0) rs +
          EW.scale ((whatW mu (qs.getD i 0)).getD mu 0) (novelEval cs (whatW mu (qs.getD i 0)))) *
          qw[i] + accB index mu rs cs qs rows qw i := by
      rw [term_eq, accB_succ, termB, Array.getElem_eq_getD 0]
    refine ⟨?_, ?_⟩
    · rw [st.keep _ (by bomega) (by bomega) (by bomega), v16, s9, e]
    · rw [wd_wd, st.keep _ (by bomega) (by bomega) (by bomega), v17, s10, e]

/-- The batch's loop over the queries. -/
def batchLoop : Stmt := .loop (.cmp .ltu .rax (.reg .rcx)) batchBody

/-- The start: the sum `0`, query `0`. -/
theorem start_wp {F : QState → Prop} {Q : QState → Prop} (c : Ctx p s index mu width rs cs qs rows)
    (h : ∀ s₀ : QState, s₀.reg .rbp = p.env.work → s₀.reg .rdi = p.env.ctx →
      s₀.mem (wd p.env.work (tmpO + 16)) = some 0 → s₀.mem (wd p.env.work (tmpO + 17)) = some 0 →
      KeepB p.env.work s.mem s₀.mem → DomEq s.mem s₀.mem → WP (blk rest) s₀ Q F) :
    WP (blk (ldW :: stwi (tmpO + 16) 0 :: stwi (tmpO + 17) 0 :: rest)) s Q F := by
  have n67 : wd p.env.work (tmpO + 16) ≠ wd p.env.work (tmpO + 17) :=
    wd_ne (by omega) (by bomega) (by bomega)
  have d16 := c.dom (DomEq.refl _) (tmpO + 16) (by have := c.N; bomega)
  have d17 := c.dom (DomEq.refl _) (tmpO + 17) (by have := c.N; bomega)
  refine ldW_wp c.rdi c.wp ?_
  refine stwi0_wp (env := p.env) (by rsimp) (by rsimp; exact d16) ?_
  refine stwi0_wp (env := p.env) (by rsimp) (by
    simp only [QState.setMem_mem, QState.setReg_mem, n67.symm, ite_false]; exact d17) ?_
  refine h _ (by rsimp) (by rsimp; exact c.rdi)
    (by simp only [QState.setMem_mem, QState.setReg_mem, n67, ite_false, ite_true])
    (by simp only [QState.setMem_mem, ite_true]) (fun a ha ↦ ?_) (fun a ↦ ?_)
  · simp only [QState.setMem_mem, QState.setReg_mem,
      ha (tmpO + 16) (.inr (.inl ⟨by omega, by omega⟩)),
      ha (tmpO + 17) (.inr (.inl ⟨by omega, by omega⟩)), ite_false]
  · simp only [QState.setMem_mem, QState.setReg_mem]
    by_cases e1 : a = wd p.env.work (tmpO + 17)
    · subst e1; simp [d17]
    · by_cases e2 : a = wd p.env.work (tmpO + 16)
      · subst e2; simp [d16]
      · simp [e1, e2]

/-- `qInit`, and the loop's state at query `0`. -/
theorem init_wp {F : QState → Prop} {Q : QState → Prop} (c : Ctx p s index mu width rs cs qs rows)
    {s₀ : QState} (hbp : s₀.reg .rbp = p.env.work) (hrdi : s₀.reg .rdi = p.env.ctx)
    (hk : KeepB p.env.work s.mem s₀.mem) (hd : DomEq s.mem s₀.mem)
    (h : ∀ u : QState, Loop p s u width 0 → u.reg .rax = (0 : Nat).toUInt64 →
      u.reg .rcx = qs.size.toUInt64 →
      (∀ j, j ≠ cI → j ≠ tmpO + 18 → j < 2 ^ 61 → u.mem (wd p.env.work j) = s₀.mem (wd p.env.work j)) →
      WP (blk rest) u Q F) :
    WP (blk (qInit :: rest)) s₀ Q F :=
  Field.WP.then (qInit_spec (n := qs.size) hbp (c.dom hd _ (by have := c.N; bomega))
    (c.dom hd _ (by have := c.N; bomega)) (c.count hk)) fun u st ↦
    h u ⟨st.rbp, st.rdi.trans hrdi, st.idx, by rw [Nat.mul_zero, Nat.add_zero]; exact st.row,
      hk.trans st.keepB, hd.trans st.dom⟩ st.rax st.rcx st.keep


/-! ## The final check -/

theorem ew_ext {a b : EW} (h0 : a.c0 = b.c0) (h1 : a.c1 = b.c1) : a = b := by
  cases a; cases b; simp_all

/-- One query of the final check: fail unless its fold is the novel evaluation. -/
def finalBody : Stmt := blk [
  qNovel, stw (tmpO + 20) .r9, stw (tmpO + 21) .r10, qFold,
  ldw .rax (tmpO + 20), failIf (.cmp .ne .r9 (.reg .rax)),
  ldw .rax (tmpO + 21), failIf (.cmp .ne .r10 (.reg .rax)), qNext]

theorem finalBody_spec {i : Nat} (c : Ctx p s index mu width rs cs qs rows) {u : QState}
    (hl : Loop p s u width i) (hi : i < qs.size) :
    WP finalBody u (fun u' ↦ Loop p s u' width (i + 1) ∧ u'.reg .rax = (i + 1).toUInt64 ∧
        u'.reg .rcx = qs.size.toUInt64 ∧ okF index mu rs cs qs rows i)
      (fun u' ↦ ¬ okF index mu rs cs qs rows i ∧ KeepB p.env.work s.mem u'.mem ∧
        DomEq s.mem u'.mem ∧ u'.reg .rdi = p.env.ctx) := by
  have hq := c.qsz
  unfold finalBody
  refine Field.WP.then (c.novel hl hi) fun u₁ ⟨n9, n10, nbp, nrdi, _, nk, nd⟩ ↦ ?_
  have k1 : KeepB p.env.work s.mem u₁.mem := hl.keep.trans nk.toB
  have d1 : DomEq s.mem u₁.mem := hl.dom.trans nd
  refine st2_wp (k := tmpO + 20) (k' := tmpO + 21) nbp (by omega) (by bomega) (by bomega)
    (c.dom d1 _ (by have := c.N; bomega)) (c.dom d1 _ (by have := c.N; bomega))
    fun u₃ r3 m3 w20 w21 d3 ↦ ?_
  have k3 : KeepB p.env.work s.mem u₃.mem :=
    KeepB.st2 k1 (.inr (.inl ⟨by omega, by omega⟩)) (.inr (.inl ⟨by omega, by omega⟩)) m3
  have g3 : ∀ j, (j < whatO ∨ foldO + 256 ≤ j) → j ≠ tmpO + 20 → j ≠ tmpO + 21 → j < 2 ^ 61 →
      u₃.mem (wd p.env.work j) = u.mem (wd p.env.work j) := fun j h1 h2 h3 h4 ↦ by
    rw [m3 _ (wd_ne h2 h4 (by bomega)) (wd_ne h3 h4 (by bomega)), nk.get h1 h4]
  refine Field.WP.then (c.fold (i := i) (by rw [r3]; exact nbp) (by rw [r3]; exact nrdi) k3
    (d1.trans d3) (by rw [g3 _ (by bomega) (by bomega) (by bomega) (by bomega)]; exact hl.idx)
    (by rw [g3 _ (by bomega) (by bomega) (by bomega) (by bomega)]; exact hl.row) hi)
    fun u₄ ⟨f9, f10, fbp, frdi, fk, fd⟩ ↦ ?_
  have k4 : KeepB p.env.work s.mem u₄.mem := k3.trans fk.toB
  have d4 : DomEq s.mem u₄.mem := (d1.trans d3).trans fd
  have v20 : u₄.mem (wd p.env.work (tmpO + 20)) =
      some (novelEval cs (whatW mu (qs.getD i 0))).c0 := by
    rw [fk.get (by bomega) (by bomega), w20, n9]
  have v21 : u₄.mem (wd p.env.work (tmpO + 21)) =
      some (novelEval cs (whatW mu (qs.getD i 0))).c1 := by
    rw [fk.get (by bomega) (by bomega), w21, n10]
  refine ldw_wp fbp v20 ?_
  by_cases e0 : (foldRow (lanesW index (rows.getD i #[])) (qs.getD i 0) rs).c0 =
      (novelEval cs (whatW mu (qs.getD i 0))).c0
  swap
  · refine NativeVm.Transcript.wp_failIf_fail (by
      simp only [Cond.eval, Rhs.eval, QState.setReg_reg, reduceCtorEq, ite_false, ite_true, f9]
      simpa using e0) ⟨fun h ↦ e0 (by rw [okF] at h; rw [h]), k4, d4, ?_⟩
    rsimp; exact frdi
  refine NativeVm.Transcript.wp_failIf (by
    simp only [Cond.eval, Rhs.eval, QState.setReg_reg, reduceCtorEq, ite_false, ite_true, f9]
    simpa using e0) ?_
  refine ldw_wp (env := p.env) (by rsimp; exact fbp) (by rsimp; exact v21) ?_
  by_cases e1 : (foldRow (lanesW index (rows.getD i #[])) (qs.getD i 0) rs).c1 =
      (novelEval cs (whatW mu (qs.getD i 0))).c1
  swap
  · refine NativeVm.Transcript.wp_failIf_fail (by
      simp only [Cond.eval, Rhs.eval, QState.setReg_reg, reduceCtorEq, ite_false, ite_true, f10]
      simpa using e1) ⟨fun h ↦ e1 (by rw [okF] at h; rw [h]), k4, d4, ?_⟩
    rsimp; exact frdi
  refine NativeVm.Transcript.wp_failIf (by
    simp only [Cond.eval, Rhs.eval, QState.setReg_reg, reduceCtorEq, ite_false, ite_true, f10]
    simpa using e1) ?_
  have g4 : ∀ j, (j < whatO ∨ foldO + 256 ≤ j) → j ≠ tmpO + 20 → j ≠ tmpO + 21 → j < 2 ^ 61 →
      u₄.mem (wd p.env.work j) = u.mem (wd p.env.work j) := fun j h1 h2 h3 h4 ↦ by
    rw [fk.get h1 h4, g3 j h1 h2 h3 h4]
  refine Field.WP.then (qNext_spec (n := qs.size) (i := i) (ro := rowsR.off + width * i)
    (w := width) (by rsimp; exact fbp) (by rsimp; exact c.dom d4 _ (by have := c.N; bomega))
    (by rsimp; exact c.dom d4 _ (by have := c.N; bomega))
    (by rsimp; rw [g4 _ (by bomega) (by bomega) (by bomega) (by bomega)]; exact hl.idx)
    (by rsimp; rw [g4 _ (by bomega) (by bomega) (by bomega) (by bomega)]; exact hl.row)
    (by rsimp; rw [k4.get (by bomega) (by bomega)]; exact c.widw.2) (by rsimp; exact c.count k4))
    fun u₉ st ↦ ?_
  apply WP.blk_nil
  refine ⟨⟨st.rbp, ?_, st.idx, ?_, k4.trans st.keepB, d4.trans st.dom⟩, st.rax, st.rcx,
    ew_ext e0 e1⟩
  · rw [st.rdi]; rsimp; exact frdi
  · rw [st.row, Nat.mul_succ, Nat.add_assoc]

/-- The final check's loop over the queries. -/
def finalLoop : Stmt := .loop (.cmp .ltu .rax (.reg .rcx)) finalBody

end BT

open BT

/-- **The batched value of a non-final level's queries**, at `tmpO + 16`. -/
def batchC : Stmt := blk [ldW, stwi (tmpO + 16) 0, stwi (tmpO + 17) 0, qInit, batchLoop]

theorem batchC_spec {p : Par} {s : QState} {F : QState → Prop} {index mu width : Nat}
    {rs : Array FoldRoundW} {high : Array EW} {qs : Array UInt64} {rows : Array (Array UInt64)}
    {qw : Array EW} {qo : Nat}
    (hrdi : s.reg .rdi = p.env.ctx) (hin : Inputs p.env p.inp s.mem)
    (hwp : s.mem (wd p.env.ctx ctxWork) = some p.env.work)
    (hidx : NatAt s.mem (wd p.env.work cIdx) index) (hmu : NatAt s.mem (wd p.env.work cMu) mu)
    (hmu30 : mu ≤ 30) (hq : WVec s.mem (wd p.env.work queriesR.off) queryCap qs)
    (hrows : RowsAt s.mem (wd p.env.work rowsR.off) width rows) (hrs : rows.size = qs.size)
    (hwid : width ≤ 64) (hwd : NatAt s.mem (wd p.env.work (tmpO + 24)) width)
    (hR : RoundsAt s.mem (wd p.env.work roundsR.off) rs)
    (hh : EWArr s.mem (wd p.env.work hiO) high) (hhs : high.size ≤ 6)
    (hcn : NatAt s.mem (wd p.env.work cJ) high.size)
    (hT : TableAt s.mem (wd p.env.work tabO) (subspaceTable mu))
    (hqo : s.mem (wd p.env.work cK) = some (wd p.env.work qo))
    (hqw : EWArr s.mem (wd p.env.work qo) qw) (hqws : qw.size = qs.size)
    (hqoR : whirR.off ≤ qo ∧ qo + 2 * qw.size ≤ whirR.off + whirWords) :
    WP batchC s (fun s' ↦
      EWAt s'.mem (wd p.env.work (tmpO + 16)) (batchedW index mu rs high qs rows qw) ∧
      FrM p.env s s' ∧ Only p.env WB s.mem s'.mem) F := by
  have c : Ctx p s index mu width rs high qs rows :=
    ⟨hrdi, hin, hwp, hidx, hmu, hmu30, hq, hrows, hrs, hwid, hwd, hR, hh, by omega, hcn, hT⟩
  have hn := c.qsz
  unfold batchC
  refine start_wp c fun s₀ b0 r0 z16 z17 k0 d0 ↦ ?_
  refine init_wp c b0 r0 k0 d0 fun u₀ l0 a0 c0 g0 ↦ ?_
  apply WP.loop (fun u ↦ ∃ i ≤ qs.size, Loop p s u width i ∧
      EWAt u.mem (wd p.env.work (tmpO + 16)) (accB index mu rs high qs rows qw i) ∧
      u.reg .rax = i.toUInt64 ∧ u.reg .rcx = qs.size.toUInt64)
    (fun u ↦ qs.size - (u.reg .rax).toNat)
  · refine ⟨0, Nat.zero_le _, l0, ⟨?_, ?_⟩, a0, c0⟩
    · rw [g0 _ (by bomega) (by bomega) (by bomega), z16]; rfl
    · rw [wd_wd, g0 _ (by bomega) (by bomega) (by bomega), z17]; rfl
  · intro u ⟨i, hi, hl, ha, hax, hcx⟩ hc
    have hlt : i < qs.size := by
      have := of_decide_eq_true hc
      rw [hax, NativeVm.Transcript.rhs_reg, hcx, toUInt64_lt (by omega) (by omega)] at this
      exact this
    refine WP.mono (batchBody_spec c hqo hqw hqws hqoR hl ha hlt) (fun u' ⟨l', a', x', c'⟩ ↦
      ⟨⟨i + 1, hlt, l', a', x', c'⟩, ?_⟩) fun _ h ↦ h
    rw [x', hax, toNat_toUInt64 (by omega), toNat_toUInt64 (by omega)]
    omega
  · intro u ⟨i, hi, hl, ha, hax, hcx⟩ hc
    have hge : ¬ i < qs.size := by
      have := of_decide_eq_false hc
      rwa [hax, NativeVm.Transcript.rhs_reg, hcx, toUInt64_lt (by omega) (by omega)] at this
    obtain rfl : i = qs.size := by omega
    refine ⟨by rw [batchedW_eq hrs hqws]; exact ha, KeepB.frM hl.keep hl.dom (hl.rdi.trans hrdi.symm),
      KeepB.only hl.keep⟩

/-- **The final level's check**: fails unless every query's fold is the novel evaluation of the
folded polynomial at it. -/
def finalCheckC : Stmt := blk [ldW, qInit, finalLoop]

theorem finalCheckC_spec {p : Par} {s : QState} {index mu width : Nat}
    {rs : Array FoldRoundW} {folded : Array EW} {qs : Array UInt64} {rows : Array (Array UInt64)}
    (hrdi : s.reg .rdi = p.env.ctx) (hin : Inputs p.env p.inp s.mem)
    (hwp : s.mem (wd p.env.ctx ctxWork) = some p.env.work)
    (hidx : NatAt s.mem (wd p.env.work cIdx) index) (hmu : NatAt s.mem (wd p.env.work cMu) mu)
    (hmu30 : mu ≤ 30) (hq : WVec s.mem (wd p.env.work queriesR.off) queryCap qs)
    (hrows : RowsAt s.mem (wd p.env.work rowsR.off) width rows) (hrs : rows.size = qs.size)
    (hwid : width ≤ 64) (hwd : NatAt s.mem (wd p.env.work (tmpO + 24)) width)
    (hR : RoundsAt s.mem (wd p.env.work roundsR.off) rs)
    (hf : EWArr s.mem (wd p.env.work hiO) folded) (hfs : folded.size ≤ 64)
    (hcn : NatAt s.mem (wd p.env.work cJ) folded.size)
    (hT : TableAt s.mem (wd p.env.work tabO) (subspaceTable mu)) :
    WP finalCheckC s
      (fun s' ↦ finalOkW index mu rs folded qs rows = true ∧ FrM p.env s s' ∧
        Only p.env WB s.mem s'.mem)
      (fun s' ↦ finalOkW index mu rs folded qs rows = false ∧ FrM p.env s s' ∧
        Only p.env WB s.mem s'.mem) := by
  have c : Ctx p s index mu width rs folded qs rows :=
    ⟨hrdi, hin, hwp, hidx, hmu, hmu30, hq, hrows, hrs, hwid, hwd, hR, hf, hfs, hcn, hT⟩
  have hn := c.qsz
  unfold finalCheckC
  refine ldW_wp hrdi hwp ?_
  refine init_wp c (by rsimp) (by rsimp; exact hrdi) (KeepB.refl _ _) (DomEq.refl _)
    fun u₀ l0 a0 c0 _ ↦ ?_
  apply WP.loop (fun u ↦ ∃ i ≤ qs.size, Loop p s u width i ∧
      u.reg .rax = i.toUInt64 ∧ u.reg .rcx = qs.size.toUInt64 ∧
      ∀ j < i, okF index mu rs folded qs rows j)
    (fun u ↦ qs.size - (u.reg .rax).toNat)
  · exact ⟨0, Nat.zero_le _, l0, a0, c0, fun j hj ↦ absurd hj (Nat.not_lt_zero _)⟩
  · intro u ⟨i, hi, hl, hax, hcx, hok⟩ hc
    have hlt : i < qs.size := by
      have := of_decide_eq_true hc
      rw [hax, NativeVm.Transcript.rhs_reg, hcx, toUInt64_lt (by omega) (by omega)] at this
      exact this
    refine WP.mono (finalBody_spec c hl hlt) (fun u' ⟨l', x', c', ok'⟩ ↦
      ⟨⟨i + 1, hlt, l', x', c', fun j hj ↦ ?_⟩, ?_⟩) fun u' ⟨nok, k', d', r'⟩ ↦ ?_
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · exact hok j hj
      · exact ok'
    · rw [x', hax, toNat_toUInt64 (by omega), toNat_toUInt64 (by omega)]
      omega
    · refine ⟨?_, KeepB.frM k' d' (r'.trans hrdi.symm), KeepB.only k'⟩
      cases h : finalOkW index mu rs folded qs rows
      · rfl
      · exact absurd ((finalOkW_iff hrs).mp h i hlt) nok
  · intro u ⟨i, hi, hl, hax, hcx, hok⟩ hc
    have hge : ¬ i < qs.size := by
      have := of_decide_eq_false hc
      rwa [hax, NativeVm.Transcript.rhs_reg, hcx, toUInt64_lt (by omega) (by omega)] at this
    obtain rfl : i = qs.size := by omega
    exact ⟨(finalOkW_iff hrs).mpr hok, KeepB.frM hl.keep hl.dom (hl.rdi.trans hrdi.symm),
      KeepB.only hl.keep⟩

end NativeVm.Code.P7
