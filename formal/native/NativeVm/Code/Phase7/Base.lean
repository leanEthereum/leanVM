module

public import NativeVm.Code.Gadgets
public import NativeVm.Code.Contracts

/-!
# Phase 7's frame: what its code may write

Phase 7's WHIR part writes only the working area's words from `basisR` to the end of `scratchR`
(`InMine`), besides the transcript's (`Transcript.Foot`). `Fr env s s'` is what a piece of its code
keeps: `rdi`, which words exist, and every word outside both. A piece that writes no transcript word
(`FrM`) keeps `CodeRel` (`codeRel_frM`); a run that keeps `Fr` from the WHIR part's start keeps its
regions' complement (`kept_of_fr`). The code addresses the working area through `rbp`, loaded from
the context (`ldW`, `ldw`, `stw`, `leaw`).
-/

@[expose] public section

namespace NativeVm.Code.P7

open Native NativeVm.Model
open NativeVm.Transcript (wd Fits Disj Env Foot cw wdisp ctxWork ctxEnd Keeps clobbers wd_inj wd_ne_of_disj
  wd_toNat eval_wd)

/-! ## The ladder in words -/

/-- The levels at `p`: their count, then level k's fold, rate exponent, queries at words 1+3k, 2+3k,
3+3k. -/
def LevelsAt (mem : UInt64 → Option UInt64) (p : UInt64) (L : List LeanVM.Parameters.Whir.Level) :
    Prop :=
  NatAt mem p L.length ∧ ∀ k (h : k < L.length), NatAt mem (wd p (1 + 3 * k)) L[k].fold ∧
    NatAt mem (wd p (2 + 3 * k)) L[k].logInvRate ∧ NatAt mem (wd p (3 + 3 * k)) L[k].queries

/-- The words of `LevelsAt`. -/
def levelsWords : Nat := 19

/-! ## Code helpers -/

/-- `rbp := work`, the working area's address. -/
def ldW : Stmt := I (.load .rbp (cw ctxWork))

/-- `d := word k` of the working area. -/
def ldw (d : Reg64) (k : Nat) : Stmt := I (.load d (at_ .rbp (wdisp k)))

/-- `word k := r` of the working area. -/
def stw (k : Nat) (r : Reg64) : Stmt := I (.store (at_ .rbp (wdisp k)) r)

/-- `word k := n` of the working area. -/
def stwi (k : Nat) (n : Int64) : Stmt := I (.storei (at_ .rbp (wdisp k)) n)

/-- `d := address of word k` of the working area. -/
def leaw (d : Reg64) (k : Nat) : Stmt := I (.lea d (at_ .rbp (wdisp k)))

/-- The regions the WHIR part writes. -/
def whirRegs : List Region := [basisR, whirR, roundsR, queriesR, rowsR, scratchR]

/-! ## The area -/

/-- The first word of the WHIR part's area. -/
abbrev mineLo : Nat := basisR.off

theorem mineLo_val : mineLo = 28061 := by decide
theorem dataEnd_eq : dataEnd = 85438 := dataEnd_val

/-- A word of the WHIR part's area. -/
def InMine (env : Env) (a : UInt64) : Prop := ∃ k, mineLo ≤ k ∧ k < dataEnd ∧ a = wd env.work k

/-- **What a piece of phase 7's code keeps**: `rdi`, which words exist, and every word outside the
transcript's and the area. -/
structure Fr (env : Env) (s s' : QState) : Prop where
  rdi : s'.reg .rdi = s.reg .rdi
  dom : ∀ a, (s'.mem a).isSome = (s.mem a).isSome
  mem : ∀ a, ¬ Foot env a → ¬ InMine env a → s'.mem a = s.mem a

/-- **What a piece writing no transcript word keeps.** -/
structure FrM (env : Env) (s s' : QState) : Prop where
  rdi : s'.reg .rdi = s.reg .rdi
  dom : ∀ a, (s'.mem a).isSome = (s.mem a).isSome
  mem : ∀ a, ¬ InMine env a → s'.mem a = s.mem a

variable {env : Env} {inp : Input} {s s₁ s₂ s₃ : QState} {t : TState}

theorem Fr.refl (s : QState) : Fr env s s := ⟨rfl, fun _ ↦ rfl, fun _ _ _ ↦ rfl⟩

theorem Fr.trans (h₁ : Fr env s₁ s₂) (h₂ : Fr env s₂ s₃) : Fr env s₁ s₃ :=
  ⟨h₂.rdi.trans h₁.rdi, fun a ↦ (h₂.dom a).trans (h₁.dom a),
    fun a hf hm ↦ (h₂.mem a hf hm).trans (h₁.mem a hf hm)⟩

theorem FrM.refl (s : QState) : FrM env s s := ⟨rfl, fun _ ↦ rfl, fun _ _ ↦ rfl⟩

theorem FrM.trans (h₁ : FrM env s₁ s₂) (h₂ : FrM env s₂ s₃) : FrM env s₁ s₃ :=
  ⟨h₂.rdi.trans h₁.rdi, fun a ↦ (h₂.dom a).trans (h₁.dom a),
    fun a hm ↦ (h₂.mem a hm).trans (h₁.mem a hm)⟩

theorem FrM.fr (h : FrM env s₁ s₂) : Fr env s₁ s₂ := ⟨h.rdi, h.dom, fun a _ hm ↦ h.mem a hm⟩

/-- A gadget's frame, with which words exist. -/
theorem Fr.of_keeps {rs : List Reg64} (h : Keeps rs (Foot env) s₁ s₂)
    (hd : ∀ a, (s₂.mem a).isSome = (s₁.mem a).isSome) : Fr env s₁ s₂ :=
  ⟨h.rdi, hd, fun a hf _ ↦ h.mem a hf⟩

theorem workWords_ge (n : Nat) : 85438 ≤ workWords n := by
  have := dataEnd_le n; rwa [dataEnd_val] at this

/-- An area word is no transcript word. -/
theorem InMine.not_foot (hi : Inputs env inp s.mem) {a : UInt64} (ha : InMine env a) :
    ¬ Foot env a := by
  obtain ⟨k, h1, h2, rfl⟩ := ha
  have := workWords_ge inp.bytecode.size
  rw [mineLo_val] at h1; rw [dataEnd_val] at h2
  exact hi.not_foot_work (by rw [Transcript.workWords_val]; omega) (by omega)

/-- A gadget keeps every word of the area. -/
theorem keeps_mine {rs : List Reg64} (hi : Inputs env inp s₁.mem) (h : Keeps rs (Foot env) s₁ s₂)
    {a : UInt64} (ha : InMine env a) : s₂.mem a = s₁.mem a :=
  h.mem a (ha.not_foot hi)

/-- The working area's words from `k`, as an area word. -/
theorem inMine_wd {k : Nat} (h1 : mineLo ≤ k) (h2 : k < dataEnd) : InMine env (wd env.work k) :=
  ⟨k, h1, h2, rfl⟩

/-- **`CodeRel` through a piece writing only the area.** -/
theorem codeRel_frM (h : CodeRel env t s₁) (hi : Inputs env inp s₁.mem) (hf : FrM env s₁ s₂) :
    CodeRel env t s₂ := by
  obtain ⟨st, hr, hs, hstream, hop⟩ := h
  have hw := workWords_ge inp.bytecode.size
  have hfw := hi.fitWork
  have notMine_ctx : ∀ k < ctxEnd, ¬ InMine env (wd env.ctx k) := fun k hk ⟨j, h1, h2, e⟩ ↦
    hi.ctx_ne_work hk (by rw [dataEnd_val] at h2; omega) e
  refine ⟨st, hr, hs.congrW (hf.rdi.trans hs.rdi) hf.dom (fun k hk ↦ hf.mem _ (notMine_ctx k ?_))
    (fun k hk ↦ hf.mem _ ?_) (fun k hk ↦ hf.mem _ ?_), hstream, hop⟩
  · rcases hk with hk | ⟨-, hk⟩
    · rw [Transcript.scratchW_val] at hk; rw [Transcript.ctxEnd_val]; omega
    · rw [Transcript.groundW_val] at hk; rw [Transcript.ctxEnd_val]; omega
  · rintro ⟨j, h1, h2, e⟩
    exact wd_ne_of_disj hs.layout.fitDec hfw hi.disjDec hk
      (by rw [dataEnd_val] at h2; omega) e
  · rintro ⟨j, h1, h2, e⟩
    rw [Transcript.workWords_val] at hk; rw [mineLo_val] at h1; rw [dataEnd_val] at h2
    have := (wd_inj (by omega) (by omega)).mp e
    omega

/-- The area is the WHIR part's regions. -/
theorem inMine_of_in {a : UInt64} (ha : InMine env a) : ∃ r ∈ whirRegs, r.In env.work a := by
  obtain ⟨k, h1, h2, rfl⟩ := ha
  rw [mineLo_val] at h1; rw [dataEnd_val] at h2
  have e : ∀ r : Region, r.off ≤ k → k < r.off + r.size → r.In env.work (wd env.work k) :=
    fun r h1 h2 ↦ ⟨k - r.off, by omega, by rw [Nat.add_sub_cancel' h1]⟩
  simp only [whirRegs, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
  have hb : basisR.off = 28061 ∧ basisR.size = 325 := by decide
  have hw : whirR.off = 28386 ∧ whirR.size = 7644 := by decide
  have hr : roundsR.off = 36030 ∧ roundsR.size = 25 := by decide
  have hq : queriesR.off = 36055 ∧ queriesR.size = 231 := by decide
  have hro : rowsR.off = 36286 ∧ rowsR.size = 16384 := by decide
  have hs : scratchR.off = 52670 ∧ scratchR.size = 32768 := by decide
  by_cases k1 : k < 28386
  · exact .inl (e _ (by omega) (by omega))
  by_cases k2 : k < 36030
  · exact .inr (.inl (e _ (by omega) (by omega)))
  by_cases k3 : k < 36055
  · exact .inr (.inr (.inl (e _ (by omega) (by omega))))
  by_cases k4 : k < 36286
  · exact .inr (.inr (.inr (.inl (e _ (by omega) (by omega)))))
  by_cases k5 : k < 52670
  · exact .inr (.inr (.inr (.inr (.inl (e _ (by omega) (by omega))))))
  · exact .inr (.inr (.inr (.inr (.inr (e _ (by omega) (by omega))))))

/-- **A run keeping `Fr` keeps the WHIR part's regions' complement.** -/
theorem kept_of_fr (h : Fr env s₁ s₂) (hrdi : s₁.reg .rdi = env.ctx) : Kept env whirRegs s₁ s₂ :=
  ⟨h.rdi.trans hrdi, fun a hf hr ↦ h.mem a hf fun hm ↦ by
    obtain ⟨r, hr', hin⟩ := inMine_of_in hm
    exact hr r hr' hin⟩

/-- A region below the area survives a run keeping `Fr` (from a state with the inputs). -/
theorem same_of_fr (h : Fr env s₁ s₂) (hi : Inputs env inp s₁.mem) (hrdi : s₁.reg .rdi = env.ctx)
    {q : Region} (hq : q ∈ regions) (hlo : q.off + q.size ≤ mineLo) :
    Same s₁.mem s₂.mem (q.at env.work) q.size := by
  refine (kept_of_fr h hrdi).same hi (fun r hr ↦ ?_) hq fun r hr ↦ ?_
  · exact stop_le_of_mem (by simp only [whirRegs] at hr; simp only [regions]; simp_all) _
  · have : mineLo ≤ r.off := by
      simp only [whirRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact .inl (by unfold Region.stop; omega)

/-! ## The area's words in the code -/

theorem eval_w {s : QState} (h : s.reg .rbp = env.work) (k : Nat) :
    (at_ .rbp (wdisp k)).eval s = wd env.work k := by
  have := eval_wd (s := s) (r := .rbp) (b := env.work) (j := 0) (by rw [h, Transcript.wd_zero]) k
  rwa [Nat.zero_add] at this

end NativeVm.Code.P7
