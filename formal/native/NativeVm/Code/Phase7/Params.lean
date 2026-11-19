module

public import NativeVm.Code.Phase7.Push
public import NativeVm.Code.Phase7.QueryBits

/-!
# Phase 7: a level's parameters

`paramsC` copies level `k`'s fold, rate exponent and query count (`k` at `cIdx`) from the ladder
(`LevelsAt` at `levO`) to `cFold`, `cRate`, `cQ`, with the loop counters `cJ := fold`,
`cK := queries`; `nextC` copies level `k + 1`'s fold and rate exponent to `cNFold`, `cNRate`; `muC`
sets `cMu := logN - |α|` and `cDepth := cMu + rate`. Level `k`'s words sit at `levO + 1 + 3k`, read
by an index register (`ix`) holding `3k`. `commitC` reads the next commitment, its height
`mu - f + r` and width `2 · 2^f` computed from `cMu`, `cNFold`, `cNRate`.
-/

@[expose] public section

namespace NativeVm.Code.P7

open Native NativeVm.Model LeanVM.Parameters NativeVm.Code
open NativeVm.Transcript (wd Env wdisp wd_inj wd_zero eval_cw wp_load wp_store wp_reg
  isSome_setMem ctxWork toUInt64_shl toUInt64_add toNat_toUInt64)

/-! ## The model -/

/-- `readCommitment` adds one root. -/
theorem readCommitment_roots_size {h w : Nat} {t t' : TState} {x : Unit}
    (hr : (readCommitment h w).run t = some (x, t')) : t'.roots.size = t.roots.size + 1 := by
  unfold readCommitment at hr
  simp only [StateT.run_bind, Option.bind_eq_bind] at hr
  cases h1 : Model.readScalar.run t with
  | none => rw [h1] at hr; cases hr
  | some p1 =>
    rw [h1, Option.bind_some] at hr
    cases h2 : Model.readScalar.run p1.2 with
    | none => rw [h2] at hr; cases hr
    | some p2 =>
      rw [h2, Option.bind_some] at hr
      simp only [StateT.run_modify, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨-, rfl⟩ := hr
      rw [Array.size_push, KeepsRoots.readScalar.keeps _ _ _ h2,
        KeepsRoots.readScalar.keeps _ _ _ h1]

/-! ## Shared steps -/

variable {p : Par} {s : QState} {P E : QState → Prop} {rest : List Stmt}

/-- A piece writing only registers other than `rdi` keeps the frame. -/
theorem frM_regs {env : Env} {s s' : QState} (hm : s'.mem = s.mem) (hr : s'.reg .rdi = s.reg .rdi) :
    FrM env s s' :=
  ⟨hr, fun a ↦ by rw [hm], fun a _ ↦ by rw [hm]⟩

/-- A pure piece's frame: which words exist and `rdi` kept, the words outside `W'` unchanged. -/
theorem frM_only {s s' : QState} {W' : Nat → Prop} (hrdi : s'.reg .rdi = s.reg .rdi)
    (hd : ∀ a, (s'.mem a).isSome = (s.mem a).isSome)
    (hm : ∀ a, (∀ k, W' k → a ≠ wd p.env.work k) → s'.mem a = s.mem a)
    (hW : ∀ k, W' k → mineLo ≤ k ∧ k < dataEnd) : FrM p.env s s' ∧ Only p.env W' s.mem s'.mem :=
  ⟨frM_of hrdi hd hm hW, Only.frame (Only.refl W' s.mem) hm (fun _ h ↦ h)
    (fun k hk ↦ by have := (hW k hk).2; rw [dataEnd_val] at this; omega)⟩

theorem three_mul (k : Nat) : k.toUInt64 + k.toUInt64 <<< 1 = (3 * k).toUInt64 := by
  rw [show (1 : UInt64) = (1 : Nat).toUInt64 from rfl, toUInt64_shl k 1 (by omega), toUInt64_add]
  congr 1
  omega

/-- `rbp := work`, `rcx := 3 · word cIdx`. -/
abbrev idx3 : List Stmt :=
  [ldW, ldw .rcx cIdx, I (.mov .rax .rcx), I (.shli .rax 1), I (.add .rcx .rax)]

theorem idx3_wp {k : Nat} (hrdi : s.reg .rdi = p.env.ctx)
    (hwp : s.mem (wd p.env.ctx ctxWork) = some p.env.work)
    (hidx : NatAt s.mem (wd p.env.work cIdx) k)
    (h : ∀ s', s'.mem = s.mem → s'.reg .rbp = p.env.work → s'.reg .rcx = (3 * k).toUInt64 →
      (∀ r, r ∉ [.rax, .rcx, .rbp] → s'.reg r = s.reg r) → WP (blk rest) s' P E) :
    WP (blk (idx3 ++ rest)) s P E := by
  simp only [idx3, List.cons_append, List.nil_append, ldW]
  refine wp_load (eval_cw hrdi _) hwp ?_
  refine ldw_wp (env := p.env) (by rsimp) (by rsimp; exact hidx.2) ?_
  refine wp_reg rfl ?_
  refine wp_reg rfl ?_
  refine wp_reg rfl ?_
  refine h _ (by rsimp) (by rsimp) (by rsimp; exact three_mul k) fun r hr ↦ ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  rsimp
  simp only [hr.1, hr.2.1, hr.2.2, ↓reduceIte]

/-- Load the word `j` of a level `k` (`rcx = 3k`). -/
theorem ldix_wp {d : Reg64} {k j : Nat} {v : Nat}
    (hbp : s.reg .rbp = p.env.work) (hcx : s.reg .rcx = (3 * k).toUInt64)
    (hv : NatAt s.mem (wd (wd p.env.work levO) (j + 3 * k)) v)
    (h : WP (blk rest) (s.setReg d v.toUInt64) P E) :
    WP (blk (I (.load d (ix .rcx (levO + j))) :: rest)) s P E :=
  wp_load (eval_ix hbp hcx _) (by rw [wd_wd] at hv; rw [← hv.2]; congr 2; omega) h

/-! ## Level `k`'s parameters -/

/-- The words `paramsC` writes. -/
def paramsW (j : Nat) : Prop := j = cFold ∨ j = cRate ∨ j = cQ ∨ j = cK ∨ j = cJ

/-- Level `k`'s fold, rate exponent and queries (`k` at `cIdx`) to `cFold`, `cRate`, `cQ`, with
`cJ := fold`, `cK := queries`. -/
def paramsC : Stmt := blk (idx3 ++ [
  I (.load .rax (ix .rcx (levO + 1))), I (.load .rdx (ix .rcx (levO + 2))),
  I (.load .rsi (ix .rcx (levO + 3))),
  stw cFold .rax, stw cJ .rax, stw cRate .rdx, stw cQ .rsi, stw cK .rsi])

theorem paramsC_core {k : Nat} {L : List Whir.Level} (hrdi : s.reg .rdi = p.env.ctx)
    (hin : Inputs p.env p.inp s.mem) (hwp : s.mem (wd p.env.ctx ctxWork) = some p.env.work)
    (hidx : NatAt s.mem (wd p.env.work cIdx) k) (hL : LevelsAt s.mem (wd p.env.work levO) L)
    (hk : k < L.length) :
    WP paramsC s (fun s' ↦ NatAt s'.mem (wd p.env.work cFold) L[k].fold ∧
      NatAt s'.mem (wd p.env.work cRate) L[k].logInvRate ∧
      NatAt s'.mem (wd p.env.work cQ) L[k].queries ∧ NatAt s'.mem (wd p.env.work cK) L[k].queries ∧
      NatAt s'.mem (wd p.env.work cJ) L[k].fold ∧
      ∀ a, (∀ j, paramsW j → a ≠ wd p.env.work j) → s'.mem a = s.mem a) P := by
  obtain ⟨f0, r0, q0⟩ := hL.2 k hk
  have hww := workWords_ge p.inp.bytecode.size
  have hsome : ∀ j, mineLo ≤ j → j < dataEnd → (s.mem (wd p.env.work j)).isSome := fun j _ h2 ↦
    hin.workSome j (by rw [dataEnd_val] at h2; omega)
  unfold paramsC
  refine idx3_wp hrdi hwp hidx fun s1 m1 b1 c1 _ ↦ ?_
  refine ldix_wp b1 c1 (j := 1) (by rw [m1]; exact f0) ?_
  refine ldix_wp (by rsimp; exact b1) (by rsimp; exact c1) (j := 2) (by rsimp; rw [m1]; exact r0) ?_
  refine ldix_wp (by rsimp; exact b1) (by rsimp; exact c1) (j := 3) (by rsimp; rw [m1]; exact q0) ?_
  refine stw_wp (env := p.env) (by rsimp; exact b1)
    (by rsimp; rw [m1]; exact hsome _ (by oomega) (by oomega)) ?_
  refine stw_wp (env := p.env) (by rsimp; exact b1)
    (by wsimp; rw [m1]; exact hsome _ (by oomega) (by oomega)) ?_
  refine stw_wp (env := p.env) (by rsimp; exact b1)
    (by wsimp; rw [m1]; exact hsome _ (by oomega) (by oomega)) ?_
  refine stw_wp (env := p.env) (by rsimp; exact b1)
    (by wsimp; rw [m1]; exact hsome _ (by oomega) (by oomega)) ?_
  refine stw_wp (env := p.env) (by rsimp; exact b1)
    (by wsimp; rw [m1]; exact hsome _ (by oomega) (by oomega)) ?_
  refine NativeVm.Transcript.wp_done_gen fun s' hs' ↦ ?_
  refine ⟨⟨f0.1, ?_⟩, ⟨r0.1, ?_⟩, ⟨q0.1, ?_⟩, ⟨q0.1, ?_⟩, ⟨f0.1, ?_⟩, fun a ha ↦ ?_⟩
  · rw [← hs']; wsimp
  · rw [← hs']; wsimp
  · rw [← hs']; wsimp
  · rw [← hs']; wsimp
  · rw [← hs']; wsimp
  · rw [← hs', ← m1]
    repeat (first | rw [QState.setReg_mem] | rw [setMem_ne _ _ ?_])
    all_goals exact ha _ (by unfold paramsW; oomega)

/-- **Level `k`'s parameters.** -/
theorem paramsC_spec {k : Nat} {L : List Whir.Level} (hrdi : s.reg .rdi = p.env.ctx)
    (hin : Inputs p.env p.inp s.mem) (hwp : s.mem (wd p.env.ctx ctxWork) = some p.env.work)
    (hidx : NatAt s.mem (wd p.env.work cIdx) k) (hL : LevelsAt s.mem (wd p.env.work levO) L)
    (hk : k < L.length) :
    WP paramsC s (fun s' ↦ NatAt s'.mem (wd p.env.work cFold) L[k].fold ∧
      NatAt s'.mem (wd p.env.work cRate) L[k].logInvRate ∧
      NatAt s'.mem (wd p.env.work cQ) L[k].queries ∧ NatAt s'.mem (wd p.env.work cK) L[k].queries ∧
      NatAt s'.mem (wd p.env.work cJ) L[k].fold ∧
      FrM p.env s s' ∧ Only p.env paramsW s.mem s'.mem ∧
      ∀ r, r ∉ [.rax, .rcx, .rdx, .rsi, .rbp] → s'.reg r = s.reg r) P :=
  WP.mono (NativeVm.Transcript.WP.frame (paramsC_core hrdi hin hwp hidx hL hk))
    (fun _ ⟨⟨h1, h2, h3, h4, h5, hm⟩, hd, hreg⟩ ↦ ⟨h1, h2, h3, h4, h5,
      (frM_only (hreg .rdi (by decide)) hd hm (fun j hj ↦ by unfold paramsW at hj; oomega)).1,
      (frM_only (hreg .rdi (by decide)) hd hm (fun j hj ↦ by unfold paramsW at hj; oomega)).2,
      fun r hr ↦ hreg r (by revert hr; cases r <;> decide)⟩) fun _ h ↦ h.1

/-! ## Level `k + 1`'s fold and rate exponent -/

/-- The words `nextC` writes. -/
def nextW (j : Nat) : Prop := j = cNFold ∨ j = cNRate

/-- Level `k + 1`'s fold and rate exponent (`k` at `cIdx`) to `cNFold`, `cNRate`. -/
def nextC : Stmt := blk (idx3 ++ [
  I (.load .rax (ix .rcx (levO + 4))), I (.load .rdx (ix .rcx (levO + 5))),
  stw cNFold .rax, stw cNRate .rdx])

theorem nextC_core {k : Nat} {L : List Whir.Level} (hrdi : s.reg .rdi = p.env.ctx)
    (hin : Inputs p.env p.inp s.mem) (hwp : s.mem (wd p.env.ctx ctxWork) = some p.env.work)
    (hidx : NatAt s.mem (wd p.env.work cIdx) k) (hL : LevelsAt s.mem (wd p.env.work levO) L)
    (hk : k + 1 < L.length) :
    WP nextC s (fun s' ↦ NatAt s'.mem (wd p.env.work cNFold) L[k + 1].fold ∧
      NatAt s'.mem (wd p.env.work cNRate) L[k + 1].logInvRate ∧
      ∀ a, (∀ j, nextW j → a ≠ wd p.env.work j) → s'.mem a = s.mem a) P := by
  obtain ⟨f0, r0, -⟩ := hL.2 (k + 1) hk
  have hww := workWords_ge p.inp.bytecode.size
  have hsome : ∀ j, mineLo ≤ j → j < dataEnd → (s.mem (wd p.env.work j)).isSome := fun j _ h2 ↦
    hin.workSome j (by rw [dataEnd_val] at h2; omega)
  unfold nextC
  refine idx3_wp hrdi hwp hidx fun s1 m1 b1 c1 _ ↦ ?_
  refine ldix_wp b1 c1 (j := 4)
    (by rw [m1, show 4 + 3 * k = 1 + 3 * (k + 1) by omega]; exact f0) ?_
  refine ldix_wp (by rsimp; exact b1) (by rsimp; exact c1) (j := 5)
    (by rsimp; rw [m1, show 5 + 3 * k = 2 + 3 * (k + 1) by omega]; exact r0) ?_
  refine stw_wp (env := p.env) (by rsimp; exact b1)
    (by rsimp; rw [m1]; exact hsome _ (by oomega) (by oomega)) ?_
  refine stw_wp (env := p.env) (by rsimp; exact b1)
    (by wsimp; rw [m1]; exact hsome _ (by oomega) (by oomega)) ?_
  refine NativeVm.Transcript.wp_done_gen fun s' hs' ↦ ?_
  refine ⟨⟨f0.1, ?_⟩, ⟨r0.1, ?_⟩, fun a ha ↦ ?_⟩
  · rw [← hs']; wsimp
  · rw [← hs']; wsimp
  · rw [← hs', ← m1]
    repeat (first | rw [QState.setReg_mem] | rw [setMem_ne _ _ ?_])
    all_goals exact ha _ (by unfold nextW; oomega)

/-- **Level `k + 1`'s fold and rate exponent.** -/
theorem nextC_spec {k : Nat} {L : List Whir.Level} (hrdi : s.reg .rdi = p.env.ctx)
    (hin : Inputs p.env p.inp s.mem) (hwp : s.mem (wd p.env.ctx ctxWork) = some p.env.work)
    (hidx : NatAt s.mem (wd p.env.work cIdx) k) (hL : LevelsAt s.mem (wd p.env.work levO) L)
    (hk : k + 1 < L.length) :
    WP nextC s (fun s' ↦ NatAt s'.mem (wd p.env.work cNFold) L[k + 1].fold ∧
      NatAt s'.mem (wd p.env.work cNRate) L[k + 1].logInvRate ∧
      FrM p.env s s' ∧ Only p.env nextW s.mem s'.mem ∧
      ∀ r, r ∉ [.rax, .rcx, .rdx, .rbp] → s'.reg r = s.reg r) P :=
  WP.mono (NativeVm.Transcript.WP.frame (nextC_core hrdi hin hwp hidx hL hk))
    (fun _ ⟨⟨h1, h2, hm⟩, hd, hreg⟩ ↦ ⟨h1, h2,
      (frM_only (hreg .rdi (by decide)) hd hm (fun j hj ↦ by unfold nextW at hj; oomega)).1,
      (frM_only (hreg .rdi (by decide)) hd hm (fun j hj ↦ by unfold nextW at hj; oomega)).2,
      fun r hr ↦ hreg r (by revert hr; cases r <;> decide)⟩) fun _ h ↦ h.1

/-! ## The variables left and the queries' depth -/

/-- The words `muC` writes. -/
def muW (j : Nat) : Prop := j = cMu ∨ j = cDepth

/-- `cMu := logN - |α|`, `cDepth := cMu + rate`. -/
def muC : Stmt := blk [ldW, ldw .rax cLogN, ldw .rcx (whirR.off + 2), I (.sub .rax .rcx),
  stw cMu .rax, ldw .rcx cRate, I (.add .rax .rcx), stw cDepth .rax]

theorem muC_core {logN r : Nat} {sW : WhirStateW} (hrdi : s.reg .rdi = p.env.ctx)
    (hin : Inputs p.env p.inp s.mem) (hwp : s.mem (wd p.env.ctx ctxWork) = some p.env.work)
    (hlog : NatAt s.mem (wd p.env.work cLogN) logN) (hw : WhirAt s.mem (whirR.at p.env.work) sW)
    (hr : NatAt s.mem (wd p.env.work cRate) r) (ha : sW.alphas.size ≤ logN)
    (h64 : logN - sW.alphas.size + r < 64) :
    WP muC s (fun s' ↦ NatAt s'.mem (wd p.env.work cMu) (logN - sW.alphas.size) ∧
      NatAt s'.mem (wd p.env.work cDepth) (logN - sW.alphas.size + r) ∧
      ∀ a, (∀ j, muW j → a ≠ wd p.env.work j) → s'.mem a = s.mem a) P := by
  have hn := hw.2.1.2.1
  simp only [Region.at, wd_wd] at hn
  have hww := workWords_ge p.inp.bytecode.size
  have hsome : ∀ j, mineLo ≤ j → j < dataEnd → (s.mem (wd p.env.work j)).isSome := fun j _ h2 ↦
    hin.workSome j (by rw [dataEnd_val] at h2; omega)
  unfold muC ldW
  refine wp_load (eval_cw hrdi _) hwp ?_
  refine ldw_wp (env := p.env) (by rsimp) (by rsimp; exact hlog.2) ?_
  refine ldw_wp (env := p.env) (by rsimp) (by rsimp; exact hn.2) ?_
  refine wp_reg rfl ?_
  refine stw_wp (env := p.env) (by rsimp) (by rsimp; exact hsome _ (by oomega) (by oomega)) ?_
  refine ldw_wp (env := p.env) (by rsimp) (by wsimp; exact hr.2) ?_
  refine wp_reg rfl ?_
  refine stw_wp (env := p.env) (by rsimp)
    (by wsimp; exact hsome _ (by oomega) (by oomega)) ?_
  refine NativeVm.Transcript.wp_done_gen fun s' hs' ↦ ?_
  have e1 : logN.toUInt64 - sW.alphas.size.toUInt64 = (logN - sW.alphas.size).toUInt64 :=
    qToUInt64_sub ha
  refine ⟨⟨by omega, ?_⟩, ⟨by omega, ?_⟩, fun a ha' ↦ ?_⟩
  · rw [← hs']; wsimp; rw [e1]
  · rw [← hs']; wsimp; rw [e1, toUInt64_add]
  · rw [← hs']
    repeat (first | rw [QState.setReg_mem] | rw [setMem_ne _ _ ?_])
    all_goals exact ha' _ (by unfold muW; oomega)

/-- **`cMu` and `cDepth`.** -/
theorem muC_spec {logN r : Nat} {sW : WhirStateW} (hrdi : s.reg .rdi = p.env.ctx)
    (hin : Inputs p.env p.inp s.mem) (hwp : s.mem (wd p.env.ctx ctxWork) = some p.env.work)
    (hlog : NatAt s.mem (wd p.env.work cLogN) logN) (hw : WhirAt s.mem (whirR.at p.env.work) sW)
    (hr : NatAt s.mem (wd p.env.work cRate) r) (ha : sW.alphas.size ≤ logN)
    (h64 : logN - sW.alphas.size + r < 64) :
    WP muC s (fun s' ↦ NatAt s'.mem (wd p.env.work cMu) (logN - sW.alphas.size) ∧
      NatAt s'.mem (wd p.env.work cDepth) (logN - sW.alphas.size + r) ∧
      FrM p.env s s' ∧ Only p.env muW s.mem s'.mem ∧
      ∀ r, r ∉ [.rax, .rcx, .rbp] → s'.reg r = s.reg r) P :=
  WP.mono (NativeVm.Transcript.WP.frame (muC_core hrdi hin hwp hlog hw hr ha h64))
    (fun _ ⟨⟨h1, h2, hm⟩, hd, hreg⟩ ↦ ⟨h1, h2,
      (frM_only (hreg .rdi (by decide)) hd hm (fun j hj ↦ by unfold muW at hj; oomega)).1,
      (frM_only (hreg .rdi (by decide)) hd hm (fun j hj ↦ by unfold muW at hj; oomega)).2,
      fun r hr ↦ hreg r (by revert hr; cases r <;> decide)⟩) fun _ h ↦ h.1

/-! ## The next commitment -/

/-- `rsi := mu - f + r`, `rbx := 2 << f` (`mu`, `f`, `r` at `cMu`, `cNFold`, `cNRate`). -/
def commitSetup : Stmt := blk [ldW, ldw .rsi cMu, ldw .rax cNFold, I (.sub .rsi .rax),
  ldw .rax cNRate, I (.add .rsi .rax), ldw .rcx cNFold, I (.movi .rbx 2), I (.shlcl .rbx)]

/-- The next commitment: height `mu - f + r`, width `2 · 2^f`. -/
def commitC : Stmt := .seq commitSetup Transcript.commit

theorem mine_mineOnly (m0 : UInt64 → Option UInt64) :
    MineOnly p.env fun m ↦ ∀ a, InMine p.env a → m a = m0 a :=
  fun _ _ hm hx a ha ↦ (hm a ha).trans (hx a ha)

/-- **The next commitment**: the area unchanged, one root more. -/
theorem commitC_spec {m0 : UInt64 → Option UInt64} {mu f r n : Nat} (hf : f ≤ mu) (hf6 : f ≤ 6)
    (hmu : mu ≤ 30) (hr : r < 64) :
    Refines (fun t s ↦ Base p t s ∧ s.mem = m0 ∧ t.roots.size = n ∧ n < Transcript.maxRoots ∧
        NatAt s.mem (wd p.env.work cMu) mu ∧ NatAt s.mem (wd p.env.work cNFold) f ∧
        NatAt s.mem (wd p.env.work cNRate) r)
      commitC (readCommitment (mu - f + r) (2 * 2 ^ f))
      (fun _ t s ↦ Base p t s ∧ (∀ a, InMine p.env a → s.mem a = m0 a) ∧ t.roots.size = n + 1)
      (Err p) := by
  have hR : GOk p.env p.inp fun s ↦ ∀ a, InMine p.env a → s.mem a = m0 a :=
    GOk.of_mine (mine_mineOnly m0)
  refine Refines.pre (P' := fun t s ↦ (Base p t s ∧ (∀ a, InMine p.env a → s.mem a = m0 a) ∧
      t.roots.size < Transcript.maxRoots ∧ s.reg .rsi = (mu - f + r).toUInt64 ∧
      s.reg .rbx = (2 * 2 ^ f).toUInt64) ∧ t.roots.size = n) ?_ ?_
  · intro t s ⟨hb, hm0, hn, hmax, hmu', hf', hr'⟩
    unfold commitSetup ldW
    refine wp_load (eval_cw hb.rdi _) hb.workPtr ?_
    refine ldw_wp (env := p.env) (by rsimp) (by rsimp; exact hmu'.2) ?_
    refine ldw_wp (env := p.env) (by rsimp) (by rsimp; exact hf'.2) ?_
    refine wp_reg rfl ?_
    refine ldw_wp (env := p.env) (by rsimp) (by rsimp; exact hr'.2) ?_
    refine wp_reg rfl ?_
    refine ldw_wp (env := p.env) (by rsimp) (by rsimp; exact hf'.2) ?_
    refine wp_reg rfl ?_
    refine wp_reg rfl ?_
    refine NativeVm.Transcript.wp_done_gen fun s' hs' ↦ ⟨⟨hb.frM (frM_regs ?_ ?_), fun a _ ↦ ?_,
      by omega, ?_, ?_⟩, hn⟩
    · rw [← hs']; rfl
    · rw [← hs']; rsimp
    · rw [← hs', ← hm0]; rfl
    · rw [← hs']; rsimp
      rw [qToUInt64_sub hf, toUInt64_add]
    · rw [← hs']; rsimp
      rw [qAnd63 (by omega), show (2 : UInt64) = (2 : Nat).toUInt64 from rfl,
        toUInt64_shl 2 f (by omega), Nat.mul_comm]
  · refine (Refines.addT (fun t ↦ t.roots.size = n) (fun t ↦ t.roots.size = n + 1)
      (fun t _ t' hr hn ↦ by rw [readCommitment_roots_size hr, hn])
      (commit_b (by omega) (by have := Nat.pow_le_pow_right (show 0 < 2 by omega) hf6; omega)
        hR)).mono (fun _ _ h ↦ h) (fun _ _ _ ⟨⟨hb, hm⟩, hn⟩ ↦ ⟨hb, hm, hn⟩) (fun _ h ↦ h)

end NativeVm.Code.P7
