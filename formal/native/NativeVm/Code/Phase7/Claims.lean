module

public import NativeVm.Code.Phase7.Rounds

/-!
# Phase 7: the stack claims' batching

`batchingC` refines the stacked opening's batching (`verifyStackedOpening`): it samples `λ`, then
one pass over the stack claims (`stackClaims`: the ring-switched claim, every column claim on the
stack, the out-of-domain claim) stores the scales `powers λ n` at `basisR` and the batched value
`dot (powers λ n) values` at WHIR's running claim (`bpushC`: the running power in a temporary).
-/

@[expose] public section

namespace NativeVm.Code.P7

open Native NativeVm.Model NativeVm.Field LeanVM.Parameters NativeVm.Equiv
open LeanVM.Protocol.Verifier (qkeccak)
open NativeVm.Transcript (wd Env wdisp ctxWork wd_inj wd_zero wp_load wp_store wp_storei wp_reg
  eval_cw eval_wd eval_idx64 setMem_wd_ne setMem_wd_eq toUInt64_add wp_ite_true wp_ite_false)

/-! ## The model -/

/-- The stack claims: the ring-switched claim, the column claims on the stack, the out-of-domain
claim. -/
def stackClaims (layout : LayoutW) (target : EW) (point coeffs : Array EW)
    (claims : Array ColumnClaimW) (ood : StackClaimW) : Array StackClaimW :=
  #[⟨.ring (layout.placement qkeccak) point coeffs, target⟩] ++
    claims.filterMap (·.onStack layout) ++ #[ood]

/-- `powers`' loop state after `k` steps: the powers so far, the next. -/
def pst (lam : EW) (k : Nat) : Array EW × EW :=
  (List.range k).foldl (fun (acc : Array EW × EW) _ ↦ (acc.1.push acc.2, acc.2 * lam)) (#[], 1)

theorem powers_eq (lam : EW) (k : Nat) : powers lam k = (pst lam k).1 := rfl

theorem pst_succ (lam : EW) (k : Nat) :
    pst lam (k + 1) = ((pst lam k).1.push (pst lam k).2, (pst lam k).2 * lam) := by
  simp only [pst, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem pst_size (lam : EW) : ∀ k, (pst lam k).1.size = k
  | 0 => rfl
  | k + 1 => by rw [pst_succ, Array.size_push, pst_size lam k]

theorem dot_push {xs ys : Array EW} (h : xs.size = ys.size) (x y : EW) :
    dot (xs.push x) (ys.push y) = dot xs ys + x * y := by
  unfold dot
  rw [← Array.foldl_toList, ← Array.foldl_toList, Array.toList_zipWith, Array.toList_zipWith,
    Array.toList_push, Array.toList_push, List.zipWith_append (by simpa using h)]
  simp

/-! ## The words a pass writes -/

/-- What a pass keeps from `s0`: `rdi`, which words exist, every word outside the area (`FrM`),
and the area's words outside `Wk`. -/
structure Wr (env : Env) (Wk : Nat → Prop) (s0 s : QState) : Prop where
  fr : FrM env s0 s
  only : Only env Wk s0.mem s.mem

namespace Wr

variable {env : Env} {Wk : Nat → Prop} {s0 s s' : QState}

theorem refl (s : QState) : Wr env Wk s s := ⟨FrM.refl s, Only.refl _ _⟩

theorem regs (h : Wr env Wk s0 s) (hm : s'.mem = s.mem) (hdi : s'.reg .rdi = s.reg .rdi) :
    Wr env Wk s0 s' :=
  ⟨⟨hdi.trans h.fr.rdi, fun a ↦ by rw [hm]; exact h.fr.dom a,
    fun a ha ↦ by rw [hm]; exact h.fr.mem a ha⟩, fun k h1 h2 hk ↦ by rw [hm]; exact h.only k h1 h2 hk⟩

theorem setReg (h : Wr env Wk s0 s) {r : Reg64} (hr : r ≠ .rdi) (v : UInt64) :
    Wr env Wk s0 (s.setReg r v) :=
  h.regs rfl (by rw [QState.setReg_reg, ite_no (Ne.symm hr)])

theorem store (h : Wr env Wk s0 s) {k : Nat} (hk : Wk k) (h1 : mineLo ≤ k) (h2 : k < dataEnd)
    (hs : (s.mem (wd env.work k)).isSome) (v : UInt64) :
    Wr env Wk s0 (s.setMem (wd env.work k) v) :=
  ⟨⟨h.fr.rdi, fun a ↦ by rw [NativeVm.Transcript.isSome_setMem _ _ hs]; exact h.fr.dom a,
    fun a ha ↦ by
      rw [QState.setMem_mem, ite_no (fun e ↦ ha (by rw [e]; exact inMine_wd h1 h2))]
      exact h.fr.mem a ha⟩,
    h.only.store hk (by rw [dataEnd_val] at h2; omega) v⟩

/-- The words below the area are kept. -/
theorem low (h : Wr env Wk s0 s) {o n : Nat} (ho : o + n ≤ mineLo) :
    Same s0.mem s.mem (wd env.work o) n := fun j hj ↦ by
  rw [wd_wd]
  refine h.fr.mem _ fun ⟨k, h1, h2, e⟩ ↦ ?_
  rw [dataEnd_val] at h2
  rw [mineLo_val] at ho h1
  exact absurd ((wd_inj (by omega) (by omega)).mp e) (by omega)

theorem some (h : Wr env Wk s0 s) (h0 : ∀ k < dataEnd, (s0.mem (wd env.work k)).isSome) :
    ∀ k < dataEnd, (s.mem (wd env.work k)).isSome := fun k hk ↦ by
  rw [h.fr.dom]; exact h0 k hk

theorem mono (h : Wr env Wk s0 s) {Wk' : Nat → Prop} (hW : ∀ k, Wk k → Wk' k) : Wr env Wk' s0 s :=
  ⟨h.fr, h.only.mono hW⟩

end Wr

/-- `Wr`, and every area word exists. -/
structure WrS (env : Env) (Wk : Nat → Prop) (s0 s : QState) : Prop where
  w : Wr env Wk s0 s
  sm : ∀ j < dataEnd, (s.mem (wd env.work j)).isSome

theorem Wr.ok {env : Env} {Wk : Nat → Prop} {s0 s : QState} (h : Wr env Wk s0 s)
    (hs : ∀ j < dataEnd, (s.mem (wd env.work j)).isSome) : WrS env Wk s0 s := ⟨h, hs⟩

theorem WrS.reg {env : Env} {Wk : Nat → Prop} {s0 s : QState} (h : WrS env Wk s0 s) {r : Reg64}
    (hr : r ≠ .rdi) (v : UInt64) : WrS env Wk s0 (s.setReg r v) := ⟨h.w.setReg hr v, h.sm⟩

theorem WrS.st {env : Env} {Wk : Nat → Prop} {s0 s : QState} (h : WrS env Wk s0 s) {k : Nat}
    (hk : Wk k ∧ mineLo ≤ k ∧ k < dataEnd) (v : UInt64) :
    WrS env Wk s0 (s.setMem (wd env.work k) v) :=
  ⟨h.w.store hk.1 hk.2.1 hk.2.2 (h.sm k hk.2.2) v, fun j hj ↦ by
    rw [NativeVm.Transcript.isSome_setMem _ _ (h.sm k hk.2.2)]; exact h.sm j hj⟩

theorem WrS.of_wr {env : Env} {Wk : Nat → Prop} {s0 s u : QState} (h : WrS env Wk s0 s)
    (h' : Wr env Wk s0 u) : WrS env Wk s0 u :=
  ⟨h', fun j hj ↦ by rw [h'.fr.dom, ← h.w.fr.dom]; exact h.sm j hj⟩

/-- The words below the area are as at the WHIR part's start. -/
theorem low_of_base {p : Par} {t : TState} {s : QState} (hb : Base p t s) {o n : Nat}
    (h1 : NativeVm.Transcript.workWords ≤ o) (ho : o + n ≤ mineLo) :
    Same p.s1.mem s.mem (wd p.env.work o) n := fun j hj ↦ by
  have hww := workWords_ge p.inp.bytecode.size
  rw [mineLo_val] at ho
  rw [wd_wd]
  refine hb.fr.mem _ (hb.inp.not_foot_work (by omega) (by omega)) fun ⟨k, h1', h2, e⟩ ↦ ?_
  rw [dataEnd_val] at h2
  rw [mineLo_val] at h1'
  exact absurd ((wd_inj (by omega) (by omega)).mp e) (by omega)

/-! ## The regions the claims are in -/

/-- The layout, the column claims, the out-of-domain claim, the ring switch, `q_keccak`'s point. -/
structure Regs (mem : UInt64 → Option UInt64) (W : UInt64) (bc : Array UInt64) (layout : LayoutW)
    (rate : Nat) (claims : Array ColumnClaimW) (ood : StackClaimW) (target : EW)
    (coeffs point slices : Array EW) : Prop where
  lay : LayoutAt mem (layoutR.at W) bc layout rate
  cl : ClaimsAt mem (claimsR.at W) claims
  ood : EqClaimAt mem (oodR.at W) ood
  ring : RingAt mem (ringR.at W) target coeffs
  kec : KeccakOutAt mem (keccakR.at W) point slices

/-- The regions' bounds: after the transcript's words, below the area. -/
theorem regs_low : NativeVm.Transcript.workWords ≤ layoutR.off ∧
    layoutR.off + layoutWords ≤ mineLo ∧ NativeVm.Transcript.workWords ≤ claimsR.off ∧
    claimsR.off + claimsWords ≤ mineLo ∧ NativeVm.Transcript.workWords ≤ oodR.off ∧
    oodR.off + eqClaimWords ≤ mineLo ∧ NativeVm.Transcript.workWords ≤ ringR.off ∧
    ringR.off + ringWords ≤ mineLo ∧ NativeVm.Transcript.workWords ≤ keccakR.off ∧
    keccakR.off + keccakWords ≤ mineLo ∧ ringWords = 2 + 2 * ringCoeffCount := by
  decide +kernel

theorem Regs.congr {mem mem' : UInt64 → Option UInt64} {W : UInt64} {bc : Array UInt64}
    {layout : LayoutW} {rate : Nat} {claims : Array ColumnClaimW} {ood : StackClaimW} {target : EW}
    {coeffs point slices : Array EW}
    (h : Regs mem W bc layout rate claims ood target coeffs point slices)
    (hs : ∀ o n, NativeVm.Transcript.workWords ≤ o → o + n ≤ mineLo → Same mem mem' (wd W o) n) :
    Regs mem' W bc layout rate claims ood target coeffs point slices := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩ := regs_low
  have hr := hs ringR.off ringWords b7 b8
  exact ⟨h.lay.congr (hs _ _ b1 b2), h.cl.congr (hs _ _ b3 b4), h.ood.congr (hs _ _ b5 b6),
    ⟨h.ring.1.congr (hs ringR.off 2 b7 (by omega)), h.ring.2.1,
      h.ring.2.2.congr (hr.sub (a := 2) (m := 2 * ringCoeffCount) (by omega))
        (by rw [h.ring.2.1])⟩,
    h.kec.congr (hs _ _ b9 b10)⟩

/-! ## One claim pushed -/

/-- The running power. -/
local notation "pW" => tmpO + 2
/-- The batched value, WHIR's running claim. -/
local notation "accW" => whirR.off
/-- The scales' count. -/
local notation "cntW" => basisR.off

theorem basisWords_val : basisWords = 325 := by decide
theorem stackClaimCap_val : stackClaimCap = 162 := by decide

/-- The words the batching writes. -/
def WBa (k : Nat) : Prop :=
  (basisR.off ≤ k ∧ k < basisR.off + basisWords) ∨ k = whirR.off ∨ k = whirR.off + 1 ∨
    (tmpO ≤ k ∧ k < tmpO + 32) ∨ (sc 5 ≤ k ∧ k < sc 8)

/-- The pass's state after the values `vals`: `λ`, the next power, the batched value, the scales. -/
structure PInv (W : UInt64) (lam : EW) (vals : Array EW) (mem : UInt64 → Option UInt64) : Prop where
  lw : EWAt mem (wd W tmpO) lam
  pow : EWAt mem (wd W pW) (pst lam vals.size).2
  acc : EWAt mem (wd W accW) (dot (pst lam vals.size).1 vals)
  cnt : NatAt mem (wd W cntW) vals.size
  scales : EWArr mem (wd W (cntW + 1)) (pst lam vals.size).1

/-- The scale's address, `rbx` twice the count. -/
def sidx (d : Nat) : Addr := { base := .rbp, idx := some (.rbx, .W64), disp := wdisp (cntW + d) }

/-- Push the value at `r14`: the scale, the batched value, the next power. -/
def bpushC : List Stmt := [
  ldw .r9 pW, ldw .r10 (pW + 1),
  I (.load .r11 (at_ .r14 (wdisp 0))), I (.load .r12 (at_ .r14 (wdisp 1))), emul,
  I (.mov .r11 .r9), I (.mov .r12 .r10), ldw .r9 accW, ldw .r10 (accW + 1), eadd,
  I (.mov .rsi .r9), I (.mov .r14 .r10),
  ldw .r9 pW, ldw .r10 (pW + 1), ldw .r11 tmpO, ldw .r12 (tmpO + 1), emul,
  ldw .r11 pW, ldw .r12 (pW + 1), ldw .rax cntW, I (.mov .rbx .rax), I (.add .rbx .rbx),
  I (.store (sidx 1) .r11), I (.store (sidx 2) .r12),
  I (.addi .rax 1), stw cntW .rax,
  stw accW .rsi, stw (accW + 1) .r14,
  stw pW .r9, stw (pW + 1) .r10]

variable {s : QState} {P E : QState → Prop} {rest : List Stmt}

theorem emul_r {a b : EW} (h9 : s.reg .r9 = a.c0) (h10 : s.reg .r10 = a.c1)
    (h11 : s.reg .r11 = b.c0) (h12 : s.reg .r12 = b.c1)
    (h : ∀ s₁ : QState, s₁.mem = s.mem → s₁.reg .r9 = (a * b).c0 → s₁.reg .r10 = (a * b).c1 →
      RegsFrame eRegs s s₁ → WP (blk rest) s₁ P E) :
    WP (blk (emul :: rest)) s P E := by
  refine WP.then (emul_spec _) fun s₁ ⟨e1, m1, f1⟩ ↦ ?_
  rw [h9, h10, h11, h12, eOf_eq_toE, eOf_eq_toE, ← EW.toE_mul] at e1
  obtain ⟨l0, l1⟩ := lanes_of_eOf e1
  exact h s₁ m1 l0 l1 f1

theorem eadd_r {a b : EW} (h9 : s.reg .r9 = a.c0) (h10 : s.reg .r10 = a.c1)
    (h11 : s.reg .r11 = b.c0) (h12 : s.reg .r12 = b.c1)
    (h : ∀ s₁ : QState, s₁.mem = s.mem → s₁.reg .r9 = (a + b).c0 → s₁.reg .r10 = (a + b).c1 →
      RegsFrame [.r9, .r10] s s₁ → WP (blk rest) s₁ P E) :
    WP (blk (eadd :: rest)) s P E := by
  refine WP.then (eadd_spec _) fun s₁ ⟨e1, m1, f1⟩ ↦ ?_
  rw [h9, h10, h11, h12, eOf_eq_toE, eOf_eq_toE, ← EW.toE_add] at e1
  obtain ⟨l0, l1⟩ := lanes_of_eOf e1
  exact h s₁ m1 l0 l1 f1

/-- `oomega`, with the regions below the area. -/
macro "aomega" : tactic => `(tactic| first
  | oomega
  | (simp only [ring_off, claims_off, ood_off, layout_off, keccak_off, sc, tmpO, xO, ringO, spO,
      mleO, ptO, cI, cJ, cK, scratch_off, whir_off, basis_off, mineLo_val, dataEnd_val] at *; omega))

/-- Read a word through stores to other words of the working area, indices compared by `aomega`. -/
macro "cwsimp" : tactic => `(tactic|
  simp (disch := aomega) only [QState.setReg_mem, setMem_wd_ne, setMem_wd_eq, QState.setReg_reg,
    QState.setMem_reg, reduceCtorEq, ↓reduceIte, int64Zero_toUInt64, int64One_toUInt64])

/-- An area word exists through stores to area words. -/
macro "wsome" h:term : tactic => `(tactic| (
  simp only [QState.setReg_mem, QState.setMem_mem]
  split_ifs <;> first | rfl | exact $h _ (by aomega)))

theorem bpushC_spec {env : Env} {s0 : QState} {lam v : EW} {vals : Array EW} {o : Nat}
    (hW : s.reg .rbp = env.work) (h14 : s.reg .r14 = wd env.work o)
    (hv : EWAt s.mem (wd env.work o) v) (hI : PInv env.work lam vals s.mem)
    (hw : Wr env WBa s0 s) (hsome : ∀ k < dataEnd, (s.mem (wd env.work k)).isSome)
    (hk : vals.size < stackClaimCap) :
    WP (blk bpushC) s (fun s' ↦ PInv env.work lam (vals.push v) s'.mem ∧ Wr env WBa s0 s' ∧
      s'.reg .rbp = env.work ∧ s'.reg .r13 = s.reg .r13 ∧ s'.reg .r15 = s.reg .r15) E := by
  have hkc := hk
  rw [stackClaimCap_val] at hkc
  obtain ⟨q0, q1⟩ := ewat_wd hI.pow
  obtain ⟨a0, a1⟩ := ewat_wd hI.acc
  obtain ⟨l0, l1⟩ := ewat_wd hI.lw
  obtain ⟨v0, v1⟩ := hv
  unfold bpushC
  refine ldw_wp hW q0 (ldw_wp (by rsimp; exact hW) (by rsimp; exact q1) ?_)
  refine wp_load (eval_wd (j := o) (by rsimp; exact h14) 0) (by rsimp; rw [Nat.add_zero]; exact v0) ?_
  refine wp_load (eval_wd (j := o) (by rsimp; exact h14) 1) (by rsimp; rw [← wd_wd]; exact v1) ?_
  refine emul_r (a := (pst lam vals.size).2) (b := v) (by rsimp) (by rsimp) (by rsimp) (by rsimp)
    fun s1 m1 h9 h10 f1 ↦ ?_
  rsimp at m1
  have g1 : ∀ r ∉ eRegs, s1.reg r = s.reg r ∨ r = .r11 ∨ r = .r12 := fun r hr ↦ by
    rw [f1 r hr]; rsimp; by_cases e11 : r = .r11 <;> by_cases e12 : r = .r12 <;> simp_all
  have k1 : ∀ r ∉ eRegs, r ≠ .r11 → r ≠ .r12 → s1.reg r = s.reg r := fun r hr h11 h12 ↦ by
    rcases g1 r hr with h | h | h
    · exact h
    · exact absurd h h11
    · exact absurd h h12
  have hW1 : s1.reg .rbp = env.work := by rw [k1 .rbp (by decide) (by decide) (by decide)]; exact hW
  refine wp_reg rfl (wp_reg rfl ?_)
  refine ldw_wp (by rsimp; exact hW1) (by rsimp; rw [m1]; exact a0) ?_
  refine ldw_wp (by rsimp; exact hW1) (by rsimp; rw [m1]; exact a1) ?_
  refine eadd_r (a := dot (pst lam vals.size).1 vals) (b := (pst lam vals.size).2 * v)
    (by rsimp) (by rsimp) (by rsimp; exact h9) (by rsimp; exact h10) fun s2 m2 h9' h10' f2 ↦ ?_
  rsimp at m2
  have k2 : ∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 → s2.reg r = s1.reg r :=
    fun r e9 e10 e11 e12 ↦ by rw [f2 r (by simp [e9, e10])]; rsimp; simp [e9, e10, e11, e12]
  have hW2 : s2.reg .rbp = env.work := by
    rw [k2 .rbp (by decide) (by decide) (by decide) (by decide)]; exact hW1
  refine wp_reg rfl (wp_reg rfl ?_)
  refine ldw_wp (by rsimp; exact hW2) (by rsimp; rw [m2, m1]; exact q0) ?_
  refine ldw_wp (by rsimp; exact hW2) (by rsimp; rw [m2, m1]; exact q1) ?_
  refine ldw_wp (by rsimp; exact hW2) (by rsimp; rw [m2, m1]; exact l0) ?_
  refine ldw_wp (by rsimp; exact hW2) (by rsimp; rw [m2, m1]; exact l1) ?_
  refine emul_r (a := (pst lam vals.size).2) (b := lam) (by rsimp) (by rsimp) (by rsimp)
    (by rsimp) fun s3 m3 h9'' h10'' f3 ↦ ?_
  rsimp at m3
  have hW3 : s3.reg .rbp = env.work := by rw [f3 .rbp (by decide)]; rsimp; exact hW2
  have hm3 : s3.mem = s.mem := by rw [m3, m2, m1]
  have hrdi3 : s3.reg .rdi = s.reg .rdi := by
    rw [f3 .rdi (by decide)]; rsimp
    rw [k2 .rdi (by decide) (by decide) (by decide) (by decide)]
    rw [k1 .rdi (by decide) (by decide) (by decide)]
  have g14 : s3.reg .r14 = (dot (pst lam vals.size).1 vals + (pst lam vals.size).2 * v).c1 := by
    rw [f3 .r14 (by decide)]; rsimp; exact h10'
  have gsi : s3.reg .rsi = (dot (pst lam vals.size).1 vals + (pst lam vals.size).2 * v).c0 := by
    rw [f3 .rsi (by decide)]; rsimp; exact h9'
  have g13 : s3.reg .r13 = s.reg .r13 := by
    rw [f3 .r13 (by decide)]; rsimp
    rw [k2 .r13 (by decide) (by decide) (by decide) (by decide)]
    rw [k1 .r13 (by decide) (by decide) (by decide)]
  have g15 : s3.reg .r15 = s.reg .r15 := by
    rw [f3 .r15 (by decide)]; rsimp
    rw [k2 .r15 (by decide) (by decide) (by decide) (by decide)]
    rw [k1 .r15 (by decide) (by decide) (by decide)]
  have hw3 : Wr env WBa s0 s3 := hw.regs hm3 hrdi3
  have hs3 : ∀ k < dataEnd, (s3.mem (wd env.work k)).isSome := by rw [hm3]; exact hsome
  refine ldw_wp hW3 (by rw [hm3]; exact q0) ?_
  refine ldw_wp (by rsimp; exact hW3) (by rsimp; rw [hm3]; exact q1) ?_
  refine ldw_wp (by rsimp; exact hW3) (by rsimp; rw [hm3]; exact hI.cnt.2) ?_
  refine wp_reg rfl (wp_reg rfl ?_)
  have hbx : ∀ t : QState, t.reg .rbx = (vals.size).toUInt64 + (vals.size).toUInt64 →
      t.reg .rbp = env.work → ∀ d, (sidx d).eval t = wd env.work (cntW + d + 2 * vals.size) :=
    fun t e1 e2 d ↦ by
      rw [sidx, eval_idx64 (j := 0) (i := vals.size + vals.size) (by rw [e2, wd_zero])
        (by rw [e1, toUInt64_add])]
      congr 1; omega
  refine wp_store (hbx _ (by rsimp) (by rsimp; exact hW3) 1) (by rsimp; exact hs3 _ (by oomega)) ?_
  refine wp_store (hbx _ (by rsimp) (by rsimp; exact hW3) 2)
    (by rw [NativeVm.Transcript.isSome_setMem _ _ (by rsimp; exact hs3 _ (by oomega))]; rsimp
        exact hs3 _ (by oomega)) ?_
  refine wp_reg rfl ?_
  refine stw_wp (by rsimp; exact hW3) (by
    simp only [QState.setReg_mem, QState.setMem_mem]; split_ifs <;> first | rfl | exact hs3 _ (by oomega)) ?_
  refine stw_wp (by rsimp; exact hW3) (by
    simp only [QState.setReg_mem, QState.setMem_mem]; split_ifs <;> first | rfl | exact hs3 _ (by oomega)) ?_
  refine stw_wp (by rsimp; exact hW3) (by
    simp only [QState.setReg_mem, QState.setMem_mem]; split_ifs <;> first | rfl | exact hs3 _ (by oomega)) ?_
  refine stw_wp (by rsimp; exact hW3) (by
    simp only [QState.setReg_mem, QState.setMem_mem]; split_ifs <;> first | rfl | exact hs3 _ (by oomega)) ?_
  refine stw_wp (by rsimp; exact hW3) (by
    simp only [QState.setReg_mem, QState.setMem_mem]; split_ifs <;> first | rfl | exact hs3 _ (by oomega)) ?_
  refine WP.blk_nil ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩ <;> (try rw [wd_wd]) <;> cwsimp <;> rw [hm3]
    · exact l0
    · exact l1
  · rw [Array.size_push, pst_succ]
    refine ⟨?_, ?_⟩ <;> (try rw [wd_wd]) <;> cwsimp
    · rw [h9'']
    · rw [h10'']
  · rw [Array.size_push, pst_succ, dot_push (by rw [pst_size]) _ _]
    refine ⟨?_, ?_⟩ <;> (try rw [wd_wd]) <;> cwsimp
    · rw [gsi]
    · rw [g14]
  · refine ⟨by rw [Array.size_push]; omega, ?_⟩
    cwsimp
    rw [Array.size_push, NativeVm.Transcript.toUInt64_succ]
  · rw [Array.size_push, pst_succ]
    show EWArr _ _ ((pst lam vals.size).1.push (pst lam vals.size).2)
    intro i hi
    rw [Array.size_push, pst_size] at hi
    rw [wd_wd]
    refine ⟨?_, ?_⟩ <;> (try rw [wd_wd]) <;> rw [Array.getElem_push]
    · split
      · rename_i hlt
        have := (hI.scales i hlt).1
        rw [pst_size] at hlt
        rw [wd_wd] at this
        cwsimp
        rw [hm3]; exact this
      · obtain rfl : i = vals.size := by rw [pst_size] at *; omega
        cwsimp
    · split
      · rename_i hlt
        have := (hI.scales i hlt).2
        rw [pst_size] at hlt
        rw [wd_wd, wd_wd] at this
        cwsimp
        rw [hm3]; exact this
      · obtain rfl : i = vals.size := by rw [pst_size] at *; omega
        cwsimp
  · refine WrS.w ?_
    refine WrS.st (k := tmpO + 2 + 1) ?_ ⟨.inr (.inr (.inr (.inl ⟨by oomega, by oomega⟩))),
      by oomega, by oomega⟩ _
    refine WrS.st (k := tmpO + 2) ?_ ⟨.inr (.inr (.inr (.inl ⟨by oomega, by oomega⟩))),
      by oomega, by oomega⟩ _
    refine WrS.st (k := whirR.off + 1) ?_ ⟨.inr (.inr (.inl rfl)), by oomega, by oomega⟩ _
    refine WrS.st (k := whirR.off) ?_ ⟨.inr (.inl rfl), by oomega, by oomega⟩ _
    refine WrS.st (k := basisR.off) ?_ ⟨.inl ⟨by omega, by rw [basisWords_val]; omega⟩,
      by oomega, by oomega⟩ _
    refine WrS.reg (r := .rax) ?_ (by decide) _
    refine WrS.st (k := basisR.off + 2 + 2 * vals.size) ?_
      ⟨by simp only [WBa, basisWords_val]; oomega, by oomega, by oomega⟩ _
    refine WrS.st (k := basisR.off + 1 + 2 * vals.size) ?_
      ⟨by simp only [WBa, basisWords_val]; oomega, by oomega, by oomega⟩ _
    refine WrS.reg (r := .rbx) (WrS.reg (r := .rbx) (WrS.reg (r := .rax) (WrS.reg (r := .r12)
      (WrS.reg (r := .r11) (Wr.ok hw3 hs3) (by decide) _) (by decide) _) (by decide) _)
      (by decide) _) (by decide) _
  · rsimp; exact hW3
  · rsimp; exact g13
  · rsimp; exact g15

/-! ## The column claims -/

/-- A column claim on the stack is pushed: its column below `columnCount`, its placement word `1`. -/
def colTest : Stmt :=
  .ite (.cmp .ltu .rax (.imm (Int64.ofNat columnCount))) (blk [
      I (.mov .rbx .rax), I (.add .rbx .rbx), I (.add .rbx .rax),
      I (.load .rcx { base := .rbp, idx := some (.rbx, .W64), disp := wdisp (layoutR.off + 16) }),
      .ite (.cmp .eq .rcx (.imm 1))
        (blk [I (.lea .r14 (at_ .r13 (wdisp (1 + vecWords pointCap)))), blk bpushC]) .skip]) .skip

/-- One column claim, at `r13`; `r15` claims left. -/
def colBody : Stmt := blk [I (.load .rax (at_ .r13 (wdisp 0))), colTest,
  I (.addi .r13 (Int64.ofNat (8 * claimWords))), I (.subi .r15 1)]

/-- The values pushed after `i` column claims. -/
def valsAt (layout : LayoutW) (target : EW) (claims : Array ColumnClaimW) (i : Nat) : List EW :=
  target :: ((claims.toList.take i).filterMap (·.onStack layout)).map (·.value)

theorem valsAt_succ (layout : LayoutW) (target : EW) (claims : Array ColumnClaimW) {i : Nat}
    (hi : i < claims.size) :
    valsAt layout target claims (i + 1) = valsAt layout target claims i ++
      (((layout.placements[claims[i].column]?).getD none).map fun _ ↦ claims[i].value).toList := by
  simp only [valsAt, List.take_add_one, List.filterMap_append, List.map_append, List.cons_append]
  rw [List.getElem?_eq_getElem (by simpa using hi), Array.getElem_toList]
  simp only [Option.toList_some, List.filterMap_cons, List.filterMap_nil, ColumnClaimW.onStack]
  cases (layout.placements[claims[i].column]?).getD none <;> simp

theorem placement_some {layout : LayoutW} {c : Nat} (h : c < layout.placements.size) :
    (layout.placements[c]?).getD none = layout.placements.getD c none := by
  rw [Array.getElem?_eq_getElem h, Option.getD_some, Array.getD_eq_getD_getElem?,
    Array.getElem?_eq_getElem h, Option.getD_some]

theorem cc_imm : (Int64.ofNat columnCount).toUInt64 = (158 : Nat).toUInt64 := by decide +kernel

theorem claimStep_imm : (Int64.ofNat (8 * claimWords)).toUInt64 = (8 * 76 : Nat).toUInt64 := by
  decide +kernel

theorem claim_sizes : claimWords = 76 ∧ vecWords pointCap = 73 ∧ claimCap = 160 ∧
    columnCount = 158 := by decide +kernel

theorem colTest_spec {env : Env} {s0 t : QState} {lam target : EW} {bc : Array UInt64}
    {layout : LayoutW} {rate : Nat} {claims : Array ColumnClaimW} {ood : StackClaimW}
    {coeffs point slices : Array EW} {i : Nat} {vals : Array EW} {F : QState → Prop}
    (hR : Regs t.mem env.work bc layout rate claims ood target coeffs point slices)
    (hi : i < claims.size) (hW : t.reg .rbp = env.work)
    (h13 : t.reg .r13 = wd env.work (claimsR.off + 1 + claimWords * i))
    (hv : vals.toList = valsAt layout target claims i) (hvs : vals.size ≤ 1 + i)
    (hI : PInv env.work lam vals t.mem) (hw : WrS env WBa s0 t)
    (hrax : t.reg .rax = claims[i].column.toUInt64) :
    WP colTest t (fun t' ↦ t'.reg .rbp = env.work ∧ t'.reg .r13 = t.reg .r13 ∧
      t'.reg .r15 = t.reg .r15 ∧ ∃ vals' : Array EW,
        vals'.toList = valsAt layout target claims (i + 1) ∧ vals'.size ≤ 1 + (i + 1) ∧
        PInv env.work lam vals' t'.mem ∧ WrS env WBa s0 t') F := by
  obtain ⟨cw76, vw73, cap160, cc158⟩ := claim_sizes
  have hcap := hR.cl.1
  rw [cap160] at hcap
  have hcl := hR.cl.2.2 i hi
  have e0 : wd (claimsR.at env.work) (1 + claimWords * i) =
      wd env.work (claimsR.off + 1 + claimWords * i) := by
    rw [Region.at, wd_wd, Nat.add_assoc]
  rw [e0] at hcl
  have hc64 := hcl.1.1
  have hpl := hR.lay.placementsSize
  unfold colTest
  by_cases hlt : claims[i].column < columnCount
  · rw [cc158] at hlt
    refine wp_ite_true (by
      rw [NativeVm.Transcript.cond_ltu, NativeVm.Transcript.rhs_imm, cc_imm, hrax,
        decide_eq_true_eq, NativeVm.Transcript.toUInt64_lt (by omega) (by omega)]
      exact hlt) ?_
    have hP := hR.lay.placements _ (by rw [cc158]; exact hlt)
    have e1 : wd (layoutR.at env.work) (16 + 3 * claims[i].column) =
        wd env.work (0 + (claims[i].column + claims[i].column + claims[i].column) +
          (layoutR.off + 16)) := by
      rw [Region.at, wd_wd]; congr 1; omega
    rw [e1] at hP
    have hg := placement_some (layout := layout) (c := claims[i].column) (by rw [hpl, cc158]; exact hlt)
    refine wp_reg rfl (wp_reg rfl (wp_reg rfl ?_))
    have ea : ∀ m : UInt64 → Option UInt64, ∀ v, m (wd env.work (0 + (claims[i].column +
        claims[i].column + claims[i].column) + (layoutR.off + 16))) = some v →
        True := fun _ _ _ ↦ trivial
    clear ea
    rcases hpe : layout.placements.getD claims[i].column none with _ | pl
    · rw [hpe] at hP
      refine wp_load (eval_idx64 (j := 0) (i := claims[i].column + claims[i].column +
        claims[i].column) (by rsimp; rw [hW, wd_zero]) (by rsimp; rw [hrax, toUInt64_add,
        toUInt64_add]) (layoutR.off + 16)) (by rsimp; exact hP) ?_
      refine wp_ite_false (by
        rw [NativeVm.Transcript.cond_eq, NativeVm.Transcript.rhs_imm]; simp [int64One_toUInt64])
        (WP.skip ⟨by rsimp; exact hW, by rsimp, by rsimp, vals, ?_, by omega, hI, ?_⟩)
      · rw [valsAt_succ _ _ _ hi, hg, hpe, hv]; simp
      · exact ((hw.reg (by decide) _).reg (by decide) _ |>.reg (by decide) _).reg (by decide) _
    · rw [hpe] at hP
      refine wp_load (eval_idx64 (j := 0) (i := claims[i].column + claims[i].column +
        claims[i].column) (by rsimp; rw [hW, wd_zero]) (by rsimp; rw [hrax, toUInt64_add,
        toUInt64_add]) (layoutR.off + 16)) (by rsimp; exact hP.1) ?_
      refine wp_ite_true (by
        rw [NativeVm.Transcript.cond_eq, NativeVm.Transcript.rhs_imm]; simp [int64One_toUInt64]) ?_
      refine wp_reg rfl ?_
      show WP (blk bpushC) _ _ _
      have hval := hcl.2.2
      rw [wd_wd] at hval
      refine WP.mono (bpushC_spec (s0 := s0) (v := claims[i].value) (vals := vals)
        (o := claimsR.off + 1 + claimWords * i + (1 + vecWords pointCap)) (by rsimp; exact hW)
        (by rsimp; exact eval_wd (by rsimp; exact h13) _) (by rsimp; exact hval)
        (by rsimp; exact hI) (hw.w.regs (by rsimp) (by rsimp)) (by rsimp; exact hw.sm)
        (by rw [stackClaimCap_val]; omega)) ?_ (fun _ h ↦ h)
      rintro u ⟨hI', hw', hW', h13', h15'⟩
      refine ⟨hW', by rw [h13']; rsimp, by rw [h15']; rsimp, vals.push claims[i].value, ?_,
        by rw [Array.size_push]; omega, hI', hw.of_wr hw'⟩
      rw [Array.toList_push, valsAt_succ _ _ _ hi, hg, hpe, hv]
      rfl
  · refine wp_ite_false (by
      rw [NativeVm.Transcript.cond_ltu, NativeVm.Transcript.rhs_imm, cc_imm, hrax,
        decide_eq_false_iff_not, NativeVm.Transcript.toUInt64_lt (by omega) (by omega)]
      omega) (WP.skip ⟨hW, rfl, rfl, vals, ?_, by omega, hI, hw⟩)
    rw [valsAt_succ _ _ _ hi, Array.getElem?_eq_none (by omega), hv]
    simp

theorem colLoop_spec {env : Env} {s0 s : QState} {lam target : EW} {bc : Array UInt64}
    {layout : LayoutW} {rate : Nat} {claims : Array ColumnClaimW} {ood : StackClaimW}
    {coeffs point slices : Array EW} {vals : Array EW} {F : QState → Prop}
    (hR : Regs s0.mem env.work bc layout rate claims ood target coeffs point slices)
    (hW : s.reg .rbp = env.work) (h13 : s.reg .r13 = wd env.work (claimsR.off + 1))
    (h15 : s.reg .r15 = claims.size.toUInt64) (hv : vals.toList = valsAt layout target claims 0)
    (hvs : vals.size ≤ 1) (hI : PInv env.work lam vals s.mem) (hw : WrS env WBa s0 s) :
    WP (.loop (.cmp .ne .r15 (.imm 0)) colBody) s (fun s' ↦ s'.reg .rbp = env.work ∧
      ∃ vals' : Array EW, vals'.toList = valsAt layout target claims claims.size ∧
        vals'.size ≤ 1 + claims.size ∧ PInv env.work lam vals' s'.mem ∧ WrS env WBa s0 s') F := by
  obtain ⟨cw76, vw73, cap160, cc158⟩ := claim_sizes
  have hcap := hR.cl.1
  rw [cap160] at hcap
  have hne : ∀ t : QState, ∀ i ≤ claims.size, t.reg .r15 = (claims.size - i).toUInt64 →
      ((Cond.cmp .ne .r15 (.imm 0)).eval t = true ↔ i < claims.size) := fun t i hi h ↦ by
    rw [NativeVm.Transcript.cond_ne, NativeVm.Transcript.rhs_imm, h, int64Zero_toUInt64,
      bne_iff_ne, ne_eq, show (0 : UInt64) = (0 : Nat).toUInt64 from rfl,
      NativeVm.Transcript.toUInt64_inj (by omega) (by omega)]
    omega
  refine WP.loop (fun t ↦ ∃ i ≤ claims.size, t.reg .rbp = env.work ∧
      t.reg .r13 = wd env.work (claimsR.off + 1 + claimWords * i) ∧
      t.reg .r15 = (claims.size - i).toUInt64 ∧ ∃ vals : Array EW,
        vals.toList = valsAt layout target claims i ∧ vals.size ≤ 1 + i ∧
        PInv env.work lam vals t.mem ∧ WrS env WBa s0 t)
    (fun t ↦ (t.reg .r15).toNat)
    ⟨0, by omega, hW, by rw [h13, Nat.mul_zero, Nat.add_zero], by rw [h15, Nat.sub_zero], vals, hv,
      by omega, hI, hw⟩ ?_ ?_
  · rintro t ⟨i, hi, tW, t13, t15, vals, hv, hvs, hI, hw⟩ hc
    have hin : i < claims.size := (hne t i hi t15).mp hc
    have hR' := hR.congr (fun _ _ _ h ↦ hw.w.low h)
    have hcl := hR'.cl.2.2 i hin
    have e0 : wd (claimsR.at env.work) (1 + claimWords * i) =
        wd env.work (claimsR.off + 1 + claimWords * i + 0) := by
      rw [Region.at, wd_wd, Nat.add_zero, Nat.add_assoc]
    rw [e0] at hcl
    unfold colBody
    refine wp_load (eval_wd t13 0) hcl.1.2 ?_
    refine WP.then (colTest_spec (vals := vals) hR' hin (by rsimp; exact tW) (by rsimp; exact t13)
      hv hvs hI (hw.reg (by decide) _) (by rsimp)) fun u ⟨uW, u13, u15, vals', hv', hvs', hI', hw'⟩ ↦ ?_
    refine wp_reg rfl (wp_reg rfl (WP.blk_nil ⟨⟨i + 1, by omega, ?_, ?_, ?_, vals', hv', hvs', ?_,
      ?_⟩, ?_⟩))
    · rsimp; exact uW
    · rsimp
      rw [u13]; rsimp
      rw [t13, claimStep_imm, NativeVm.Transcript.wd_add, cw76]
      congr 1
    · rsimp
      rw [u15]; rsimp
      rw [t15, show claims.size - i = claims.size - (i + 1) + 1 by omega,
        ← NativeVm.Transcript.toUInt64_succ, UInt64.add_sub_cancel]
    · rsimp; exact hI'
    · exact (hw'.reg (by decide) _).reg (by decide) _
    · rsimp
      rw [u15]; rsimp
      rw [t15, show claims.size - i = claims.size - (i + 1) + 1 by omega,
        ← NativeVm.Transcript.toUInt64_succ, UInt64.add_sub_cancel,
        NativeVm.Transcript.toUInt64_succ, NativeVm.Transcript.toNat_toUInt64 (by omega),
        NativeVm.Transcript.toNat_toUInt64 (by omega)]
      omega
  · rintro t ⟨i, hi, tW, -, t15, vals, hv, hvs, hI, hw⟩ hc
    have : ¬ i < claims.size := fun h ↦ by rw [(hne t i hi t15).mpr h] at hc; exact absurd hc (by decide)
    obtain rfl : i = claims.size := by omega
    exact ⟨tW, vals, hv, hvs, hI, hw⟩

/-! ## The pass -/

/-- The batching pass, `λ` in `A`: the state initialised, then the ring-switched claim's value, the
column claims on the stack, the out-of-domain claim's value pushed. -/
def passC : Stmt := blk [ldW,
  stw tmpO .r9, stw (tmpO + 1) .r10,
  stwi (tmpO + 2) 1, stwi (tmpO + 2 + 1) 0, stwi whirR.off 0, stwi (whirR.off + 1) 0,
  stwi basisR.off 0,
  leaw .r14 ringR.off, blk bpushC,
  leaw .r13 (claimsR.off + 1), ldw .r15 claimsR.off,
  .loop (.cmp .ne .r15 (.imm 0)) colBody,
  leaw .r14 (oodR.off + vecWords stackCap), blk bpushC]

theorem stwi_wp {env : Env} {k : Nat} {n : Int64} (hW : s.reg .rbp = env.work)
    (hk : (s.mem (wd env.work k)).isSome)
    (h : WP (blk rest) (s.setMem (wd env.work k) n.toUInt64) P E) :
    WP (blk (stwi k n :: rest)) s P E :=
  wp_storei (eval_w hW k) hk h

theorem bpushC_specS {env : Env} {s0 : QState} {lam v : EW} {vals : Array EW} {o : Nat}
    (hW : s.reg .rbp = env.work) (h14 : s.reg .r14 = wd env.work o)
    (hv : EWAt s.mem (wd env.work o) v) (hI : PInv env.work lam vals s.mem)
    (hw : WrS env WBa s0 s) (hk : vals.size < stackClaimCap) :
    WP (blk bpushC) s (fun s' ↦ PInv env.work lam (vals.push v) s'.mem ∧ WrS env WBa s0 s' ∧
      s'.reg .rbp = env.work ∧ s'.reg .r13 = s.reg .r13 ∧ s'.reg .r15 = s.reg .r15) E :=
  WP.mono (bpushC_spec hW h14 hv hI hw.w hw.sm hk)
    (fun _ ⟨a, b, c, d, e⟩ ↦ ⟨a, hw.of_wr b, c, d, e⟩) fun _ h ↦ h

theorem stackClaims_values (layout : LayoutW) (target : EW) (point coeffs : Array EW)
    (claims : Array ColumnClaimW) (ood : StackClaimW) :
    ((stackClaims layout target point coeffs claims ood).map (·.value)).toList =
      valsAt layout target claims claims.size ++ [ood.value] := by
  simp [stackClaims, valsAt, List.take_of_length_le]

theorem dot_empty : dot #[] #[] = 0 := by simp [dot]

/-- The pass's state before any value. -/
theorem pinv0 {W : UInt64} {lam : EW} {mem : UInt64 → Option UInt64}
    (a : mem (wd W tmpO) = some lam.c0) (b : mem (wd W (tmpO + 1)) = some lam.c1)
    (c : mem (wd W (tmpO + 2)) = some 1) (d : mem (wd W (tmpO + 2 + 1)) = some 0)
    (e : mem (wd W whirR.off) = some 0) (f : mem (wd W (whirR.off + 1)) = some 0)
    (g : mem (wd W basisR.off) = some 0) : PInv W lam #[] mem := by
  have hp : pst lam (#[] : Array EW).size = (#[], 1) := rfl
  refine ⟨⟨a, by rw [wd_wd]; exact b⟩, ⟨by rw [hp]; exact c, by rw [wd_wd, hp]; exact d⟩,
    ⟨by rw [hp, dot_empty]; exact e, by rw [wd_wd, hp, dot_empty]; exact f⟩, ⟨by decide, g⟩,
    fun i hi ↦ absurd hi (by rw [hp]; simp)⟩

theorem passC_spec {env : Env} {s : QState} {F : QState → Prop} {lam target : EW}
    {bc : Array UInt64} {layout : LayoutW} {rate : Nat} {claims : Array ColumnClaimW}
    {ood : StackClaimW} {coeffs point slices : Array EW}
    (hrdi : s.reg .rdi = env.ctx) (hwp : s.mem (wd env.ctx ctxWork) = some env.work)
    (hR : Regs s.mem env.work bc layout rate claims ood target coeffs point slices)
    (h0 : ∀ k < dataEnd, (s.mem (wd env.work k)).isSome)
    (h9 : s.reg .r9 = lam.c0) (h10 : s.reg .r10 = lam.c1) :
    WP passC s (fun s' ↦ PInv env.work lam
      ((stackClaims layout target point coeffs claims ood).map (·.value)) s'.mem ∧
      (stackClaims layout target point coeffs claims ood).size ≤ stackClaimCap ∧
      Wr env WBa s s') F := by
  obtain ⟨cw76, vw73, cap160, cc158⟩ := claim_sizes
  have hcap := hR.cl.1
  rw [cap160] at hcap
  unfold passC ldW
  refine wp_load (eval_cw hrdi ctxWork) hwp ?_
  have hW : (s.setReg .rbp env.work).reg .rbp = env.work := by rsimp
  refine stw_wp hW (h0 _ (by aomega)) ?_
  refine stw_wp (by rsimp; exact hW) (by wsome h0) ?_
  refine stwi_wp (by rsimp; exact hW) (by wsome h0) ?_
  refine stwi_wp (by rsimp; exact hW) (by wsome h0) ?_
  refine stwi_wp (by rsimp; exact hW) (by wsome h0) ?_
  refine stwi_wp (by rsimp; exact hW) (by wsome h0) ?_
  refine stwi_wp (by rsimp; exact hW) (by wsome h0) ?_
  refine wp_reg rfl ?_
  have hring := hR.ring.1
  rw [Region.at] at hring
  obtain ⟨r0, r1⟩ := ewat_wd hring
  refine WP.then (bpushC_specS (s0 := s) (vals := #[]) (v := target) (o := ringR.off) (by rsimp; exact hW)
    (by rsimp; exact eval_w (by rsimp) _) ⟨by cwsimp; exact r0, by rw [wd_wd]; cwsimp; exact r1⟩
    (pinv0 (by cwsimp; rw [h9]) (by cwsimp; rw [h10]) (by cwsimp) (by cwsimp) (by cwsimp) (by cwsimp)
      (by cwsimp)) ?_ (by rw [stackClaimCap_val]; decide)) ?_
  · refine WrS.reg (r := .r14) ?_ (by decide) _
    refine WrS.st (k := basisR.off) ?_ ⟨.inl ⟨by omega, by rw [basisWords_val]; omega⟩,
      by oomega, by oomega⟩ _
    refine WrS.st (k := whirR.off + 1) ?_ ⟨.inr (.inr (.inl rfl)), by oomega, by oomega⟩ _
    refine WrS.st (k := whirR.off) ?_ ⟨.inr (.inl rfl), by oomega, by oomega⟩ _
    refine WrS.st (k := tmpO + 2 + 1) ?_ ⟨.inr (.inr (.inr (.inl ⟨by oomega, by oomega⟩))),
      by oomega, by oomega⟩ _
    refine WrS.st (k := tmpO + 2) ?_ ⟨.inr (.inr (.inr (.inl ⟨by oomega, by oomega⟩))),
      by oomega, by oomega⟩ _
    refine WrS.st (k := tmpO + 1) ?_ ⟨.inr (.inr (.inr (.inl ⟨by oomega, by oomega⟩))),
      by oomega, by oomega⟩ _
    refine WrS.st (k := tmpO) ?_ ⟨.inr (.inr (.inr (.inl ⟨by oomega, by oomega⟩))),
      by oomega, by oomega⟩ _
    exact WrS.reg ⟨Wr.refl s, h0⟩ (by decide) _
  rintro u1 ⟨hI1, hw1, hW1, -, -⟩
  have hR1 := hR.congr (fun _ _ _ h ↦ hw1.w.low h)
  have hn := hR1.cl.2.1
  refine wp_reg rfl ?_
  refine ldw_wp (by rsimp; exact hW1) (by rsimp; exact hn.2) ?_
  refine WP.then (colLoop_spec (s0 := s) (vals := #[target]) hR (by rsimp; exact hW1)
    (by rsimp; exact eval_w hW1 _) (by rsimp) (by simp [valsAt]) (by simp) (by rsimp; exact hI1)
    ((hw1.reg (by decide) _).reg (by decide) _)) ?_
  rintro u2 ⟨hW2, vals, hv, hvs, hI2, hw2⟩
  have hR2 := hR.congr (fun _ _ _ h ↦ hw2.w.low h)
  obtain ⟨z, -, -, hoodv⟩ := hR2.ood
  rw [Region.at, wd_wd] at hoodv
  refine wp_reg rfl ?_
  refine WP.mono (bpushC_specS (vals := vals) (v := ood.value) (o := oodR.off + vecWords stackCap)
    (by rsimp; exact hW2) (by rsimp; exact eval_w hW2 _) (by rsimp; exact hoodv)
    (by rsimp; exact hI2) (hw2.reg (by decide) _) (by rw [stackClaimCap_val]; omega)) ?_
    (fun _ h ↦ h)
  rintro u3 ⟨hI3, hw3, -, -, -⟩
  have hvals : vals.push ood.value = (stackClaims layout target point coeffs claims ood).map
      (·.value) := by
    apply Array.ext'
    rw [Array.toList_push, hv, stackClaims_values]
  rw [hvals] at hI3
  refine ⟨hI3, ?_, hw3.w⟩
  rw [← Array.size_map (f := (·.value)), ← hvals, Array.size_push, stackClaimCap_val]
  omega

/-! ## Batching -/

/-- **The batching**: sample `λ`, then the pass. -/
def batchingC : Stmt := .seq Transcript.sampleChallenge passC

/-- **The batching**: the scales `powers λ n` at `basisR`, the batched value at WHIR's running
claim, for the stack claims `stackClaims`; it writes only the words `WBa`. -/
theorem batchingC_spec {p : Par} {m0 : UInt64 → Option UInt64} {bc : Array UInt64}
    {layout : LayoutW} {rate : Nat} {target : EW} {coeffs point slices : Array EW}
    {claims : Array ColumnClaimW} {ood : StackClaimW}
    (hlay : LayoutAt p.s1.mem (layoutR.at p.env.work) bc layout rate)
    (hcl : ClaimsAt p.s1.mem (claimsR.at p.env.work) claims)
    (hood : EqClaimAt p.s1.mem (oodR.at p.env.work) ood)
    (hring : RingAt p.s1.mem (ringR.at p.env.work) target coeffs)
    (hk : KeccakOutAt p.s1.mem (keccakR.at p.env.work) point slices) :
    Refines (fun t s ↦ Base p t s ∧ s.mem = m0) batchingC sampleChallenge
      (fun lam t s ↦ Base p t s ∧
        EVec s.mem (basisR.at p.env.work) stackClaimCap
          (powers lam (stackClaims layout target point coeffs claims ood).size) ∧
        EWAt s.mem (wd p.env.work whirR.off)
          (dot (powers lam (stackClaims layout target point coeffs claims ood).size)
            ((stackClaims layout target point coeffs claims ood).map (·.value))) ∧
        (stackClaims layout target point coeffs claims ood).size ≤ stackClaimCap ∧
        Only p.env WBa m0 s.mem) (Err p) := by
  have gok : GOk p.env p.inp (fun s ↦ Only p.env (fun _ ↦ False) m0 s.mem) :=
    GOk.of_mine fun _ _ hm h k h1 h2 hk ↦ (hm _ (inMine_wd h1 h2)).trans (h k h1 h2 hk)
  refine Refines.post (Refines.mono (sample_b gok) (fun t s ⟨hb, hm⟩ ↦ ⟨hb, by
    rw [hm]; exact Only.refl _ _⟩) (fun _ _ _ h ↦ h) (fun _ h ↦ h)) ?_
  rintro lam t s ⟨hb, hon, h9, h10⟩
  have hR : Regs s.mem p.env.work bc layout rate claims ood target coeffs point slices :=
    Regs.congr ⟨hlay, hcl, hood, hring, hk⟩ fun _ _ h1 h2 ↦ low_of_base hb h1 h2
  have hww := workWords_ge p.inp.bytecode.size
  refine WP.mono (passC_spec hb.rdi hb.workPtr hR
    (fun k hk ↦ hb.inp.workSome k (by rw [dataEnd_val] at hk; omega)) h9 h10) ?_ fun _ h ↦ h
  rintro s' ⟨hI, hsz, hw⟩
  have hc := hI.cnt
  have hs := hI.scales
  have ha := hI.acc
  rw [Array.size_map] at hc hs ha
  refine ⟨hb.frM hw.fr, ⟨by rw [powers_eq, pst_size]; exact hsz, by
      rw [powers_eq, pst_size]; exact hc, by
      rw [Region.at, wd_wd, powers_eq]; exact hs⟩, by rw [powers_eq]; exact ha, hsz,
    (hon.trans hw.only).mono fun k h ↦ h.elim (fun h ↦ h.elim) id⟩

end NativeVm.Code.P7
