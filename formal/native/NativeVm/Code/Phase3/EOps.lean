module

public import NativeVm.Code.Phase3.Common

/-!
# Elements of the working area

Phase 3's arithmetic on elements held in the working area, its address in `r14`: `opMul a b d`
(`d := a · b`), `opAdd a b d` (`d := a + b`), `opSet d x` (`d := x`), `opCopy a d`, word indices of
the working area. Each writes the two words of `d` and the registers of `opRegs`
(`opMul_spec`, ...), as `updE`.
-/

@[expose] public section

namespace NativeVm.Code.P3

open Native NativeVm.Model NativeVm.Code NativeVm.Transcript NativeVm.Field LeanVM.Parameters

/-- The memory with the element `x` at words `a`, `a + 1` of the working area `w`. -/
def updE (m : UInt64 → Option UInt64) (w : UInt64) (a : Nat) (x : EW) : UInt64 → Option UInt64 :=
  Function.update (Function.update m (wd w a) (some x.c0)) (wd w (a + 1)) (some x.c1)

theorem ew_of_eOf {a b : UInt64} {x : EW} (h : eOf a b = x.toE) : (⟨a, b⟩ : EW) = x :=
  (eOf_eq_toE.mp h).elim fun h1 h2 ↦ by rw [h1, h2]

theorem updE_ne {m : UInt64 → Option UInt64} {w : UInt64} {a k : Nat} {x : EW} (ha : a + 1 < 2 ^ 61)
    (hk : k < 2 ^ 61) (h : k ≠ a ∧ k ≠ a + 1) : updE m w a x (wd w k) = m (wd w k) := by
  unfold updE
  rw [Function.update_of_ne (fun e ↦ h.2 ((wd_inj hk ha).mp e)),
    Function.update_of_ne (fun e ↦ h.1 ((wd_inj hk (by omega)).mp e))]

theorem updE_ewat {m : UInt64 → Option UInt64} {w : UInt64} {a : Nat} {x : EW} (ha : a + 1 < 2 ^ 61) :
    EWAt (updE m w a x) (wd w a) x := by
  unfold updE EWAt
  rw [wd_wd, Function.update_self, Function.update_of_ne (fun e ↦ by
    rw [wd_inj (by omega) (by omega)] at e; omega), Function.update_self]
  exact ⟨rfl, rfl⟩

/-- An element elsewhere survives. -/
theorem updE_ewat_ne {m : UInt64 → Option UInt64} {w : UInt64} {a k : Nat} {x y : EW}
    (ha : a + 1 < 2 ^ 61) (hk : k + 1 < 2 ^ 61) (h : k + 2 ≤ a ∨ a + 2 ≤ k)
    (hy : EWAt m (wd w k) y) : EWAt (updE m w a x) (wd w k) y := by
  unfold EWAt at *
  rw [wd_wd] at *
  rw [updE_ne ha (by omega) (by omega), updE_ne ha (by omega) (by omega)]
  exact hy

theorem updE_isSome {m : UInt64 → Option UInt64} {w : UInt64} {a : Nat} {x : EW}
    (h0 : (m (wd w a)).isSome) (h1 : (m (wd w (a + 1))).isSome) (b : UInt64) :
    (updE m w a x b).isSome = (m b).isSome := by
  unfold updE
  rw [Function.update_apply, Function.update_apply]
  split
  · subst b; simpa using h1.symm
  · split
    · subst b; simpa using h0.symm
    · rfl

/-- The registers the operations write. -/
abbrev opRegs : List Reg64 := [.rax, .rbx, .rcx, .rdx, .r8, .r9, .r10, .r11, .r12]

variable {s : QState} {E : QState → Prop} {w : UInt64}

/-- Store `A` at words `d`, `d + 1`. -/
def stA (d : Nat) : List Stmt := [I (.store (at_ .r14 (wdisp d)) .r9), I (.store (at_ .r14 (wdisp (d + 1))) .r10)]

/-- `A` from words `a`, `a + 1`. -/
def ldA (a : Nat) : List Stmt := [I (.load .r9 (at_ .r14 (wdisp a))), I (.load .r10 (at_ .r14 (wdisp (a + 1))))]

/-- `B` from words `b`, `b + 1`. -/
def ldB (b : Nat) : List Stmt := [I (.load .r11 (at_ .r14 (wdisp b))), I (.load .r12 (at_ .r14 (wdisp (b + 1))))]

/-- `d := a · b`. -/
def opMul (a b d : Nat) : Stmt := blk (ldA a ++ ldB b ++ [emul] ++ stA d)

/-- `d := a + b`. -/
def opAdd (a b d : Nat) : Stmt := blk (ldA a ++ ldB b ++ [I (.xor .r9 .r11), I (.xor .r10 .r12)] ++ stA d)

/-- `d := x`. -/
def opSet (d : Nat) (x : EW) : Stmt :=
  blk ([I (.movi .r9 (Int64.ofUInt64 x.c0)), I (.movi .r10 (Int64.ofUInt64 x.c1))] ++ stA d)

/-- `d := a`. -/
def opCopy (a d : Nat) : Stmt := blk (ldA a ++ stA d)

theorem int64_ofUInt64_toUInt64 (x : UInt64) : (Int64.ofUInt64 x).toUInt64 = x := by
  simp

/-- The stores of `A` at `d`. -/
theorem stA_spec {d : Nat} {xs : List Stmt} {P : QState → Prop} (h14 : s.reg .r14 = w)
    (hd : d + 1 < 2 ^ 61) (h0 : (s.mem (wd w d)).isSome) (h1 : (s.mem (wd w (d + 1))).isSome)
    (k : WP (blk xs) ⟨s.reg, updE s.mem w d ⟨s.reg .r9, s.reg .r10⟩⟩ P E) :
    WP (blk (stA d ++ xs)) s P E := by
  unfold stA
  refine wp_store (by rw [Transcript.eval_at, h14, wdisp_toUInt64]; rfl) h0 ?_
  have hne : wd w (d + 1) ≠ wd w d := fun e ↦ by rw [wd_inj (by omega) (by omega)] at e; omega
  refine wp_store (x := wd w (d + 1)) (by rw [Transcript.eval_at, QState.setMem_reg, h14, wdisp_toUInt64]; rfl)
    (by rw [QState.setMem_mem]; simp only [hne, ↓reduceIte]; exact h1) ?_
  exact k

theorem ew_at {r : Reg64} {k : Nat} (h : s.reg r = w) : (at_ r (wdisp k)).eval s = wd w k := by
  rw [Transcript.eval_at, h, wdisp_toUInt64]; rfl

theorem ewat_hi {m : UInt64 → Option UInt64} {a : Nat} {x : EW} (h : EWAt m (wd w a) x) :
    m (wd w (a + 1)) = some x.c1 := by
  have := h.2; rwa [wd_wd] at this

/-- `A` from an element. -/
theorem ldA_spec {a : Nat} {x : EW} {xs : List Stmt} {P : QState → Prop} (h14 : s.reg .r14 = w)
    (ha : EWAt s.mem (wd w a) x) (k : WP (blk xs) ((s.setReg .r9 x.c0).setReg .r10 x.c1) P E) :
    WP (blk (ldA a ++ xs)) s P E := by
  unfold ldA
  refine wp_load (ew_at h14) ha.1 ?_
  refine wp_load (ew_at (by rsimp; exact h14)) (ewat_hi ha) k

/-- `B` from an element. -/
theorem ldB_spec {b : Nat} {x : EW} {xs : List Stmt} {P : QState → Prop} (h14 : s.reg .r14 = w)
    (hb : EWAt s.mem (wd w b) x) (k : WP (blk xs) ((s.setReg .r11 x.c0).setReg .r12 x.c1) P E) :
    WP (blk (ldB b ++ xs)) s P E := by
  unfold ldB
  refine wp_load (ew_at h14) hb.1 ?_
  refine wp_load (ew_at (by rsimp; exact h14)) (ewat_hi hb) k

/-- What an operation leaves: the element at `d`, the registers outside `opRegs`. -/
def OpPost (s : QState) (w : UInt64) (d : Nat) (x : EW) (s' : QState) : Prop :=
  s'.mem = updE s.mem w d x ∧ RegsFrame opRegs s s'

theorem opMul_spec {a b d : Nat} {x y : EW} (h14 : s.reg .r14 = w) (ha : EWAt s.mem (wd w a) x)
    (hb : EWAt s.mem (wd w b) y) (hd : d + 1 < 2 ^ 61) (h0 : (s.mem (wd w d)).isSome)
    (h1 : (s.mem (wd w (d + 1))).isSome) : WP (opMul a b d) s (OpPost s w d (x * y)) E := by
  unfold opMul
  rw [List.append_assoc, List.append_assoc]
  refine ldA_spec h14 ha (ldB_spec (by rsimp; exact h14) (by rsimp; exact hb) ?_)
  refine WP.then (emul_spec _) fun t ⟨e1, e2, e3⟩ ↦ ?_
  have h14' : t.reg .r14 = w := by rw [e3 .r14 (by decide)]; rsimp; exact h14
  refine stA_spec h14' hd (by rw [e2]; rsimp; exact h0) (by rw [e2]; rsimp; exact h1) (WP.blk_nil ⟨?_, ?_⟩)
  · rw [e2]; rsimp
    congr 1
    refine ew_of_eOf ?_
    rw [e1, Equiv.EW.toE_mul]
    rsimp
    rfl
  · intro r hr
    have hr' : r ∉ eRegs := fun m ↦ hr ((show eRegs ⊆ opRegs by decide) m)
    rw [show ({ reg := t.reg, mem := _ } : QState).reg r = t.reg r from rfl, e3 r hr']
    simp only [opRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨-, -, -, -, -, h9, h10, h11, h12⟩ := hr
    rsimp
    simp [h9, h10, h11, h12]

theorem rf_op {s t : QState} (h : ∀ r, r ∉ opRegs → t.reg r = s.reg r) : RegsFrame opRegs s t := h

theorem opAdd_spec {a b d : Nat} {x y : EW} (h14 : s.reg .r14 = w) (ha : EWAt s.mem (wd w a) x)
    (hb : EWAt s.mem (wd w b) y) (hd : d + 1 < 2 ^ 61) (h0 : (s.mem (wd w d)).isSome)
    (h1 : (s.mem (wd w (d + 1))).isSome) : WP (opAdd a b d) s (OpPost s w d (x + y)) E := by
  unfold opAdd
  rw [List.append_assoc, List.append_assoc]
  refine ldA_spec h14 ha (ldB_spec (by rsimp; exact h14) (by rsimp; exact hb) ?_)
  refine wp_reg rfl (wp_reg rfl ?_)
  refine stA_spec (by rsimp; exact h14) hd (by rsimp; exact h0) (by rsimp; exact h1) (WP.blk_nil ⟨?_, ?_⟩)
  · rsimp; rfl
  · intro r hr
    simp only [opRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨-, -, -, -, -, h9, h10, h11, h12⟩ := hr
    show (QState.reg _) r = _
    rsimp
    simp [h9, h10, h11, h12]

theorem opSet_spec {d : Nat} {x : EW} (h14 : s.reg .r14 = w) (hd : d + 1 < 2 ^ 61)
    (h0 : (s.mem (wd w d)).isSome) (h1 : (s.mem (wd w (d + 1))).isSome) :
    WP (opSet d x) s (OpPost s w d x) E := by
  unfold opSet
  rw [List.cons_append, List.cons_append]
  refine wp_reg rfl (wp_reg rfl ?_)
  refine stA_spec (by rsimp; exact h14) hd (by rsimp; exact h0) (by rsimp; exact h1) (WP.blk_nil ⟨?_, ?_⟩)
  · rsimp
  · intro r hr
    simp only [opRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨-, -, -, -, -, h9, h10, h11, h12⟩ := hr
    show (QState.reg _) r = _
    rsimp
    simp [h9, h10]

theorem opCopy_spec {a d : Nat} {x : EW} (h14 : s.reg .r14 = w) (ha : EWAt s.mem (wd w a) x)
    (hd : d + 1 < 2 ^ 61) (h0 : (s.mem (wd w d)).isSome) (h1 : (s.mem (wd w (d + 1))).isSome) :
    WP (opCopy a d) s (OpPost s w d x) E := by
  unfold opCopy
  refine ldA_spec h14 ha ?_
  refine stA_spec (by rsimp; exact h14) hd (by rsimp; exact h0) (by rsimp; exact h1) (WP.blk_nil ⟨?_, ?_⟩)
  · rsimp
  · intro r hr
    simp only [opRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨-, -, -, -, -, h9, h10, h11, h12⟩ := hr
    show (QState.reg _) r = _
    rsimp
    simp [h9, h10]

/-! ## Straight-line programs over slots -/

/-- An operation on slots (word indices of the working area). -/
inductive EOp
  | mul (a b d : Nat)
  | add (a b d : Nat)
  | set (d : Nat) (x : EW)
  | copy (a d : Nat)

/-- Its code. -/
def EOp.code : EOp → Stmt
  | .mul a b d => opMul a b d
  | .add a b d => opAdd a b d
  | .set d x => opSet d x
  | .copy a d => opCopy a d

/-- The slot it writes. -/
def EOp.dst : EOp → Nat
  | .mul _ _ d | .add _ _ d | .set d _ | .copy _ d => d

/-- The slots it reads. -/
def EOp.srcs : EOp → List Nat
  | .mul a b _ | .add a b _ => [a, b]
  | .set _ _ => []
  | .copy a _ => [a]

/-- The value it writes, the slots holding `v`. -/
def EOp.eval (v : Nat → EW) : EOp → EW
  | .mul a b _ => v a * v b
  | .add a b _ => v a + v b
  | .set _ x => x
  | .copy a _ => v a

/-- The slots after a program. -/
def opsRun : List EOp → (Nat → EW) → (Nat → EW)
  | [], v => v
  | o :: os, v => opsRun os (Function.update v o.dst (o.eval v))

/-- A program reads only slots of `S` or written before. -/
def opsValid : List EOp → List Nat → Bool
  | [], _ => true
  | o :: os, S => o.srcs.all (· ∈ S) && opsValid os (o.dst :: S)

/-- The slots a program writes. -/
def opsDsts (l : List EOp) : List Nat := l.map EOp.dst

/-- The program's code. -/
def opsCode (l : List EOp) : Stmt := blk (l.map EOp.code)

/-- The slots `S` hold `v`. -/
def Holds (m : UInt64 → Option UInt64) (w : UInt64) (S : List Nat) (v : Nat → EW) : Prop :=
  ∀ k ∈ S, EWAt m (wd w k) (v k)

theorem EOp.spec (o : EOp) {S : List Nat} {v : Nat → EW} (h14 : s.reg .r14 = w)
    (hS : Holds s.mem w S v) (hv : o.srcs.all (· ∈ S)) (hd : o.dst + 1 < 2 ^ 61)
    (h0 : (s.mem (wd w o.dst)).isSome) (h1 : (s.mem (wd w (o.dst + 1))).isSome) :
    WP o.code s (OpPost s w o.dst (o.eval v)) E := by
  cases o with
  | mul a b d =>
    simp only [EOp.srcs, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
      decide_eq_true_eq] at hv
    exact opMul_spec h14 (hS a hv.1) (hS b hv.2) hd h0 h1
  | add a b d =>
    simp only [EOp.srcs, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
      decide_eq_true_eq] at hv
    exact opAdd_spec h14 (hS a hv.1) (hS b hv.2) hd h0 h1
  | set d x => exact opSet_spec h14 hd h0 h1
  | copy a d =>
    simp only [EOp.srcs, List.all_cons, List.all_nil, Bool.and_true, decide_eq_true_eq] at hv
    exact opCopy_spec h14 (hS a hv) hd h0 h1

/-- **A straight-line program** over even slots below `lim`, each written word existing: the
slots `S` and the written ones hold the program's values, the memory changed only at the written
slots' words. -/
theorem ops_spec (l : List EOp) {S : List Nat} {v : Nat → EW} {lim : Nat} (hlim : lim < 2 ^ 61)
    (h14 : s.reg .r14 = w) (hS : Holds s.mem w S v) (hSe : ∀ k ∈ S, k % 2 = 0 ∧ k + 1 < lim)
    (hval : opsValid l S = true) (hde : ∀ d ∈ opsDsts l, d % 2 = 0 ∧ d + 1 < lim)
    (hdom : ∀ d ∈ opsDsts l, (s.mem (wd w d)).isSome ∧ (s.mem (wd w (d + 1))).isSome) :
    WP (opsCode l) s (fun s' ↦ Holds s'.mem w (opsDsts l ++ S) (opsRun l v) ∧
      (∀ k < lim, (∀ d ∈ opsDsts l, k ≠ d ∧ k ≠ d + 1) → s'.mem (wd w k) = s.mem (wd w k)) ∧
      (∀ a, (s'.mem a).isSome = (s.mem a).isSome) ∧
      (∀ a, (∀ k < lim, a ≠ wd w k) → s'.mem a = s.mem a) ∧ RegsFrame opRegs s s') E := by
  induction l generalizing s S v with
  | nil =>
    exact WP.blk_nil ⟨hS, fun _ _ _ ↦ rfl, fun _ ↦ rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩
  | cons o os ih =>
    simp only [opsValid, Bool.and_eq_true] at hval
    simp only [opsDsts, List.map_cons, List.mem_cons, forall_eq_or_imp] at hde hdom
    unfold opsCode
    rw [List.map_cons]
    refine WP.blk_cons (WP.mono (o.spec h14 hS hval.1 (by omega) hdom.1.1 hdom.1.2) ?_ fun _ h ↦ h)
    rintro s1 ⟨hm, hf⟩
    have hdo := hde.1
    have hS1 : Holds s1.mem w (o.dst :: S) (Function.update v o.dst (o.eval v)) := by
      intro k hk
      rw [hm]
      rcases List.mem_cons.mp hk with rfl | hk
      · rw [Function.update_self]; exact updE_ewat (by omega)
      · by_cases e : k = o.dst
        · subst e; rw [Function.update_self]; exact updE_ewat (by omega)
        · rw [Function.update_of_ne e]
          have := hSe k hk
          exact updE_ewat_ne (by omega) (by omega) (by omega) (hS k hk)
    have hiso : ∀ a, (s1.mem a).isSome = (s.mem a).isSome := fun a ↦ by
      rw [hm]; exact updE_isSome hdom.1.1 hdom.1.2 a
    refine WP.mono (ih (s := s1) (S := o.dst :: S) (by rw [hf .r14 (by decide)]; exact h14) hS1
      (by simp only [List.mem_cons, forall_eq_or_imp]; exact ⟨⟨hdo.1, hdo.2⟩, hSe⟩) hval.2 hde.2
      (fun d hd ↦ by rw [hiso, hiso]; exact hdom.2 d hd)) ?_ fun _ h ↦ h
    rintro s' ⟨hH, hk, hsome, hout, hr⟩
    refine ⟨?_, fun k hk' hne ↦ ?_, fun a ↦ (hsome a).trans (hiso a), fun a ha ↦ ?_, ?_⟩
    · intro k hk'
      refine hH k ?_
      simp only [opsDsts, List.map_cons, List.mem_append, List.mem_cons] at hk' ⊢
      tauto
    · rw [hk k hk' fun d hd ↦ hne d (by simp [opsDsts] at hd ⊢; tauto), hm]
      have := hne o.dst (by simp [opsDsts])
      exact updE_ne (by omega) (by omega) this
    · rw [hout a ha, hm]
      unfold updE
      rw [Function.update_of_ne (ha _ (by omega)), Function.update_of_ne (ha _ (by omega))]
    · exact RegsFrame.trans hf hr

end NativeVm.Code.P3
