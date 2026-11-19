module

public import NativeVm.Code.Phase7.Code
public import NativeVm.Code.Phase7.Link
public import NativeVm.Code.Phase7.Bundles

/-!
# The final level's small pieces

`cntC` (`cJ := 2^μ + fold`) and `clmC` (WHIR's running claim to `tmpO + 14`), with their frames;
`m0_drop`, a transcript piece that keeps only a part of the fact it starts from; `dep_ewarrB`, an
array's words within a fixed run.
-/

@[expose] public section

namespace NativeVm.Code.P7

open Native NativeVm.Model LeanVM.Parameters
open NativeVm.Transcript (wd Env wdisp wd_inj wd_zero eval_cw wp_load wp_store wp_reg ctxWork
  toUInt64_shl toUInt64_add)

variable {p : Par} {s : QState} {P : QState → Prop}

theorem cntC_core {mu f : Nat} (hrdi : s.reg .rdi = p.env.ctx)
    (hin : Inputs p.env p.inp s.mem) (hwp : s.mem (wd p.env.ctx ctxWork) = some p.env.work)
    (hmu : NatAt s.mem (wd p.env.work cMu) mu) (hf : NatAt s.mem (wd p.env.work cFold) f)
    (h64 : mu < 64) (hs : 2 ^ mu + f < 2 ^ 64) :
    WP cntC s (fun s' ↦ NatAt s'.mem (wd p.env.work cJ) (2 ^ mu + f) ∧
      ∀ a, (∀ j, j = cJ → a ≠ wd p.env.work j) → s'.mem a = s.mem a) P := by
  have hww := workWords_ge p.inp.bytecode.size
  have hsome : ∀ j, mineLo ≤ j → j < dataEnd → (s.mem (wd p.env.work j)).isSome := fun j _ h2 ↦
    hin.workSome j (by rw [dataEnd_val] at h2; omega)
  unfold cntC ldW
  refine wp_load (eval_cw hrdi _) hwp ?_
  refine ldw_wp (env := p.env) (by rsimp) (by rsimp; exact hmu.2) ?_
  refine wp_reg rfl ?_
  refine wp_reg rfl ?_
  refine ldw_wp (env := p.env) (by rsimp) (by rsimp; exact hf.2) ?_
  refine wp_reg rfl ?_
  refine stw_wp (env := p.env) (by rsimp) (by rsimp; exact hsome _ (by oomega) (by oomega)) ?_
  refine NativeVm.Transcript.wp_done_gen fun s' hs' ↦ ?_
  refine ⟨⟨hs, ?_⟩, fun a ha ↦ ?_⟩
  · rw [← hs']
    wsimp
    rw [qAnd63 h64, show Int64.toUInt64 1 = (1 : Nat).toUInt64 from rfl, toUInt64_shl 1 mu h64,
      Nat.mul_one, toUInt64_add]
  · rw [← hs']
    repeat (first | rw [QState.setReg_mem] | rw [setMem_ne _ _ ?_])
    all_goals exact ha _ rfl

/-- **`cJ := 2^μ + fold`.** -/
theorem cntC_spec {mu f : Nat} (hrdi : s.reg .rdi = p.env.ctx)
    (hin : Inputs p.env p.inp s.mem) (hwp : s.mem (wd p.env.ctx ctxWork) = some p.env.work)
    (hmu : NatAt s.mem (wd p.env.work cMu) mu) (hf : NatAt s.mem (wd p.env.work cFold) f)
    (h64 : mu < 64) (hs : 2 ^ mu + f < 2 ^ 64) :
    WP cntC s (fun s' ↦ NatAt s'.mem (wd p.env.work cJ) (2 ^ mu + f) ∧
      FrM p.env s s' ∧ Only p.env (fun j ↦ j = cJ) s.mem s'.mem) P :=
  WP.mono (NativeVm.Transcript.WP.frame (cntC_core hrdi hin hwp hmu hf h64 hs))
    (fun _ ⟨⟨h1, hm⟩, hd, hreg⟩ ↦ ⟨h1,
      (frM_only (hreg .rdi (by decide)) hd hm (fun j hj ↦ by subst hj; oomega)).1,
      (frM_only (hreg .rdi (by decide)) hd hm (fun j hj ↦ by subst hj; oomega)).2⟩) fun _ h ↦ h.1

theorem clmC_core {x : EW} (hrdi : s.reg .rdi = p.env.ctx)
    (hin : Inputs p.env p.inp s.mem) (hwp : s.mem (wd p.env.ctx ctxWork) = some p.env.work)
    (hx : EWAt s.mem (wd p.env.work whirR.off) x) :
    WP clmC s (fun s' ↦ EWAt s'.mem (wd p.env.work (tmpO + 14)) x ∧
      ∀ a, (∀ j, (j = tmpO + 14 ∨ j = tmpO + 15) → a ≠ wd p.env.work j) → s'.mem a = s.mem a) P := by
  have hww := workWords_ge p.inp.bytecode.size
  have hsome : ∀ j, mineLo ≤ j → j < dataEnd → (s.mem (wd p.env.work j)).isSome := fun j _ h2 ↦
    hin.workSome j (by rw [dataEnd_val] at h2; omega)
  unfold clmC ldA stA
  simp only [List.cons_append, List.nil_append]
  unfold ldW
  refine wp_load (eval_cw hrdi _) hwp ?_
  refine ldA_wp (env := p.env) (by rsimp) (by rsimp; exact hx) fun s1 m1 h9 h10 f1 ↦ ?_
  have hb1 : s1.reg .rbp = p.env.work := by rw [f1 .rbp (by decide)]; rsimp
  refine stA_wp hb1 (by rw [m1]; rsimp; exact hsome _ (by oomega) (by oomega))
    (by rw [m1]; rsimp; exact hsome _ (by oomega) (by oomega)) ?_
  refine NativeVm.Transcript.wp_done_gen fun s' hs' ↦ ?_
  refine ⟨⟨?_, ?_⟩, fun a ha ↦ ?_⟩
  · rw [← hs']
    wsimp
    rw [h9]
  · rw [← hs', wd_wd]
    wsimp
    rw [h10]
  · rw [← hs']
    repeat rw [setMem_ne _ _ ?_]
    · rw [m1, QState.setReg_mem]
    all_goals exact ha _ (by omega)
/-- **WHIR's running claim to `tmpO + 14`.** -/
theorem clmC_spec {x : EW} (hrdi : s.reg .rdi = p.env.ctx)
    (hin : Inputs p.env p.inp s.mem) (hwp : s.mem (wd p.env.ctx ctxWork) = some p.env.work)
    (hx : EWAt s.mem (wd p.env.work whirR.off) x) :
    WP clmC s (fun s' ↦ EWAt s'.mem (wd p.env.work (tmpO + 14)) x ∧
      FrM p.env s s' ∧ Only p.env (fun j ↦ j = tmpO + 14 ∨ j = tmpO + 15) s.mem s'.mem) P :=
  WP.mono (NativeVm.Transcript.WP.frame (clmC_core hrdi hin hwp hx))
    (fun _ ⟨⟨h1, hm⟩, hd, hreg⟩ ↦ ⟨h1,
      (frM_only (hreg .rdi (by decide)) hd hm (fun j hj ↦ by oomega)).1,
      (frM_only (hreg .rdi (by decide)) hd hm (fun j hj ↦ by oomega)).2⟩) fun _ h ↦ h.1

variable {X X' : (UInt64 → Option UInt64) → Prop} {D : Nat → Prop}

/-- **A transcript piece adding `Y x`** (and `R x`), keeping only the part `X'` of the fact. -/
theorem m0_drop {α β : Type} {c : Stmt} {cs : List Stmt} {mc : VM α} {m₂ : α → VM β}
    {Q : β → TState → QState → Prop} {I : TState → Prop}
    {Y : α → (UInt64 → Option UInt64) → Prop} {R : α → Prop} {Wc : Nat → Prop}
    (hX : Dep p.env X' D) (hD : ∀ j, D j → mineLo ≤ j ∧ j < dataEnd) (hDW : ∀ j, D j → ¬ Wc j)
    (hXX : ∀ m, X m → X' m)
    (hc : ∀ m0, Refines (fun t s ↦ Base p t s ∧ s.mem = m0 ∧ X s.mem ∧ I t) c mc
      (fun x t s ↦ Base p t s ∧ (Y x s.mem ∧ R x) ∧ Only p.env Wc m0 s.mem) (Err p))
    (h : ∀ x, R x → Refines (fun t s ↦ Base p t s ∧ (X' s.mem ∧ Y x s.mem) ∧ True) (blk cs) (m₂ x)
      Q (Err p)) :
    Refines (fun t s ↦ Base p t s ∧ X s.mem ∧ I t) (blk (c :: cs)) (mc >>= m₂) Q (Err p) :=
  m0_then (X' := X') (Post := fun x _ s ↦ Y x s.mem ∧ R x) hX hD hDW hXX
    (fun m0 ↦ (hc m0).mono (fun _ _ h ↦ h) (fun _ _ _ ⟨hb, hy, ho⟩ ↦ ⟨hb, hy, ho⟩) (fun _ h ↦ h))
    fun x t s ⟨hb, hx, hy, hr⟩ ↦ h x hr t s ⟨hb, ⟨hx, hy⟩, trivial⟩

/-- An array of at most `cap` elements reads the run of `2 cap` words. -/
theorem dep_ewarrB (j cap : Nat) {xs : Array EW} (hs : xs.size ≤ cap) :
    Dep p.env (fun m ↦ EWArr m (wd p.env.work j) xs) (fun k ↦ j ≤ k ∧ k < j + 2 * cap) :=
  (dep_ewarr j xs).mono fun _ h ↦ ⟨h.1, by omega⟩

end NativeVm.Code.P7
