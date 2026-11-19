module

public import Native.Keccak.Words
public import Native.Frame
public import Mathlib.Data.UInt
public import Mathlib.Tactic.Ring

/-!
# `Keccak.hash`'s proof: blocks, scratch words, steps and phases

Rules of `WP` for blocks built by `List.flatMap` over a range; the facts `Words`
that a run of scratch words holds given values, `ScrFrame` that a block wrote only scratch words of
a range, and `ScrOk` that every scratch word exists; one instruction at a time (`wp_load`,
`wp_store`, `addr_tac` for a scratch word's address); and a phase, a block whose piece `j` stores
one scratch word (`phase_run`).
-/

@[expose] public section

namespace Native.Keccak.Proof

open LeanVM.Semantics

variable {P E : QState → Prop} {s : QState}

/-! ## Blocks -/

theorem wp_skip_inv (h : WP .skip s P E) : P s := by
  obtain ⟨o, hx, ho⟩ := h
  cases hx
  exact ho

theorem wp_blk_cons_inv {x : Stmt} {xs : List Stmt} (h : WP (blk (x :: xs)) s P E) :
    WP x s (fun s₁ ↦ WP (blk xs) s₁ P E) E := by
  cases xs with
  | nil => exact WP.mono h (fun _ h₁ ↦ WP.skip h₁) (fun _ h ↦ h)
  | cons y ys =>
    obtain ⟨o, hx, ho⟩ := h
    cases hx with
    | seqOk h₁ h₂ => exact ⟨_, h₁, _, h₂, ho⟩
    | seqErr h₁ => exact ⟨_, h₁, ho⟩

theorem wp_blk_append {xs ys : List Stmt} (h : WP (blk xs) s (fun s₁ ↦ WP (blk ys) s₁ P E) E) :
    WP (blk (xs ++ ys)) s P E := by
  induction xs generalizing s with
  | nil => exact wp_skip_inv h
  | cons x xs ih =>
    apply WP.blk_cons
    exact WP.mono (wp_blk_cons_inv h) (fun _ h₁ ↦ ih h₁) (fun _ h ↦ h)

/-- A block `f 0 ++ … ++ f (n - 1)`, by an invariant indexed by the pieces run. -/
theorem wp_range_flatMap (f : Nat → List Stmt) (I : Nat → QState → Prop) (n : Nat)
    (hstep : ∀ i < n, ∀ s, I i s → WP (blk (f i)) s (I (i + 1)) E) (h0 : I 0 s) :
    WP (blk ((List.range n).flatMap f)) s (I n) E := by
  induction n with
  | zero => exact WP.skip h0
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact wp_blk_append (WP.mono (ih fun i hi ↦ hstep i (by omega))
      (fun s₁ h₁ ↦ hstep n (by omega) s₁ h₁) (fun _ h ↦ h))

/-! ## Registers -/

theorem RegsFrame.refl {rs : List Reg64} (s : QState) : RegsFrame rs s s := fun _ _ ↦ rfl

theorem RegsFrame.trans {rs : List Reg64} {s₁ s₂ s₃ : QState} (h₁ : RegsFrame rs s₁ s₂)
    (h₂ : RegsFrame rs s₂ s₃) : RegsFrame rs s₁ s₃ := fun r hr ↦ (h₂ r hr).trans (h₁ r hr)

theorem RegsFrame.mono {rs rs' : List Reg64} {s₁ s₂ : QState} (h : RegsFrame rs s₁ s₂)
    (hsub : ∀ r ∈ rs, r ∈ rs') : RegsFrame rs' s₁ s₂ := fun r hr ↦ h r fun h' ↦ hr (hsub r h')

/-- Setting a register of the list keeps the frame. -/
theorem RegsFrame.setReg {rs : List Reg64} {s₁ s₂ : QState} (h : RegsFrame rs s₁ s₂) {r : Reg64}
    (hr : r ∈ rs) (v : UInt64) : RegsFrame rs s₁ (s₂.setReg r v) := fun r' hr' ↦ by
  have : r' ≠ r := by rintro rfl; exact hr' hr
  simp only [QState.setReg_reg, this, ↓reduceIte]
  exact h r' hr'

/-! ## Scratch words -/

theorem scratchAddr_inj {base : UInt64} {k k' : Nat} (hk : k < 84) (hk' : k' < 84)
    (h : scratchAddr base k = scratchAddr base k') : k = k' := by
  have h' := congrArg UInt64.toNat ((UInt64.add_right_inj base).mp h)
  simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat'] at h'
  omega

theorem scratchAddr_ne {base : UInt64} {k k' : Nat} (hk : k < 84) (hk' : k' < 84) (h : k ≠ k') :
    scratchAddr base k ≠ scratchAddr base k' := fun e ↦ h (scratchAddr_inj hk hk' e)

/-- The address of `at_ r d`. -/
theorem eval_at (r : Reg64) (d : Int64) (s : QState) :
    (at_ r d).eval s = s.reg r + d.toUInt64 := by
  simp [Addr.eval, at_]

/-- Every scratch word exists. -/
def ScrOk (mem : UInt64 → Option UInt64) (base : UInt64) : Prop :=
  ∀ k < scratchWords, (mem (scratchAddr base k)).isSome

theorem ScrOk.isSome {mem : UInt64 → Option UInt64} {base : UInt64} (h : ScrOk mem base) {k : Nat}
    (hk : k < 84) : (mem (scratchAddr base k)).isSome := h k hk

theorem ScrOk.update {mem : UInt64 → Option UInt64} {base : UInt64} (h : ScrOk mem base)
    (a v : UInt64) : ScrOk (Function.update mem a (some v)) base := fun k hk ↦ by
  by_cases e : scratchAddr base k = a
  · rw [e, Function.update_self]; rfl
  · rw [Function.update_of_ne e]; exact h k hk

/-- The words `off, …, off + n - 1` hold `f 0, …, f (n - 1)`. -/
def Words (mem : UInt64 → Option UInt64) (base : UInt64) (off n : Nat) (f : Nat → UInt64) :
    Prop :=
  ∀ t < n, mem (scratchAddr base (off + t)) = some (f t)

/-- `m₁` is `m₀` but at the scratch words `lo, …, hi - 1`. -/
def ScrFrame (base : UInt64) (lo hi : Nat) (m₀ m₁ : UInt64 → Option UInt64) : Prop :=
  ∀ a, (∀ k, lo ≤ k → k < hi → a ≠ scratchAddr base k) → m₁ a = m₀ a

theorem ScrFrame.refl {base : UInt64} {lo hi : Nat} (m : UInt64 → Option UInt64) :
    ScrFrame base lo hi m m := fun _ _ ↦ rfl

theorem ScrFrame.trans {base : UInt64} {lo hi lo' hi' : Nat} {m₀ m₁ m₂ : UInt64 → Option UInt64}
    (h₁ : ScrFrame base lo hi m₀ m₁) (h₂ : ScrFrame base lo' hi' m₁ m₂) (hlo : lo ≤ lo')
    (hhi : hi' ≤ hi) : ScrFrame base lo hi m₀ m₂ := fun a ha ↦
  (h₂ a fun k h1 h2 ↦ ha k (by omega) (by omega)).trans (h₁ a ha)

theorem ScrFrame.widen {base : UInt64} {lo hi lo' hi' : Nat} {m₀ m₁ : UInt64 → Option UInt64}
    (h : ScrFrame base lo hi m₀ m₁) (hlo : lo' ≤ lo) (hhi : hi ≤ hi') :
    ScrFrame base lo' hi' m₀ m₁ := fun a ha ↦ h a fun k h1 h2 ↦ ha k (by omega) (by omega)

theorem ScrFrame.update {base : UInt64} {lo hi k : Nat} {m : UInt64 → Option UInt64}
    {v : Option UInt64} (h1 : lo ≤ k) (h2 : k < hi) :
    ScrFrame base lo hi m (Function.update m (scratchAddr base k) v) := fun _ ha ↦
  Function.update_of_ne (ha k h1 h2) _ _

/-- A scratch word outside the frame's range is unchanged. -/
theorem ScrFrame.word {base : UInt64} {lo hi k : Nat} {m₀ m₁ : UInt64 → Option UInt64}
    (h : ScrFrame base lo hi m₀ m₁) (hk : k < lo ∨ hi ≤ k) (hk' : k < 84) (hhi : hi ≤ 84) :
    m₁ (scratchAddr base k) = m₀ (scratchAddr base k) :=
  h _ fun k' h1 h2 e ↦ by have := scratchAddr_inj hk' (by omega) e; omega

theorem Words.frame {base : UInt64} {lo hi off n : Nat} {f : Nat → UInt64}
    {m₀ m₁ : UInt64 → Option UInt64} (hw : Words m₀ base off n f)
    (h : ScrFrame base lo hi m₀ m₁) (hd : off + n ≤ lo ∨ hi ≤ off) (hn : off + n ≤ 84)
    (hhi : hi ≤ 84) : Words m₁ base off n f := fun t ht ↦ by
  rw [h.word (by omega) (by omega) hhi]
  exact hw t ht

theorem Words.congr {base : UInt64} {off n : Nat} {f g : Nat → UInt64}
    {m : UInt64 → Option UInt64} (hw : Words m base off n f) (h : ∀ t < n, f t = g t) :
    Words m base off n g := fun t ht ↦ by rw [← h t ht]; exact hw t ht

/-! ## One instruction at a time -/

theorem i64_lit (n : Nat) : (no_index (OfNat.ofNat n) : Int64).toUInt64 = OfNat.ofNat n := (rfl)

/-- A displacement `d` from `rdi` names scratch word `k`: the offsets are sums of literals and
`Nat.toInt64` of indices. -/
macro "addr_tac" : tactic => `(tactic| (
  open scoped UInt64.CommRing in
  ((try simp only [scratchAddr, sA, sB, sC, sD, sRC, Int64.toUInt64_add, Int64.toUInt64_mul,
    Int64.toUInt64_ofNat', Nat.toUInt64_eq, UInt64.ofNat_add, UInt64.ofNat_mul,
    UInt64.reduceOfNat, i64_lit]) <;>
   ring)))

/-- A load from the word at `a`. -/
theorem wp_load {r : Reg64} {ad : Addr} {a w : UInt64} {rest : List Stmt}
    (ha : ad.eval s = a) (hm : s.mem a = some w) (h : WP (blk rest) (s.setReg r w) P E) :
    WP (blk (I (.load r ad) :: rest)) s P E := by
  apply WP.blk_cons
  apply WP.ins'
  simp only [QInstr.step, ha, hm, Option.map_some]
  exact h

/-- A store to the word at `a`. -/
theorem wp_store {r : Reg64} {ad : Addr} {a : UInt64} {rest : List Stmt}
    (ha : ad.eval s = a) (hm : (s.mem a).isSome)
    (h : WP (blk rest) (s.setMem a (s.reg r)) P E) :
    WP (blk (I (.store ad r) :: rest)) s P E := by
  apply WP.blk_cons
  apply WP.ins'
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hm
  simp only [QInstr.step, ha, hw, Option.map_some]
  exact h

/-- A load from scratch word `k`. -/
theorem wp_load_scr {r : Reg64} {d : Int64} {base w : UInt64} {k : Nat} {rest : List Stmt}
    (hrdi : s.reg .rdi = base) (hd : d.toUInt64 = (8 * k).toUInt64)
    (hm : s.mem (scratchAddr base k) = some w) (h : WP (blk rest) (s.setReg r w) P E) :
    WP (blk (I (.load r (at_ .rdi d)) :: rest)) s P E :=
  wp_load (by rw [eval_at, hrdi, hd]; rfl) hm h

/-- A store to scratch word `k`. -/
theorem wp_store_scr {r : Reg64} {d : Int64} {base : UInt64} {k : Nat} {rest : List Stmt}
    (hrdi : s.reg .rdi = base) (hd : d.toUInt64 = (8 * k).toUInt64)
    (hm : (s.mem (scratchAddr base k)).isSome)
    (h : WP (blk rest) (s.setMem (scratchAddr base k) (s.reg r)) P E) :
    WP (blk (I (.store (at_ .rdi d) r) :: rest)) s P E :=
  wp_store (by rw [eval_at, hrdi, hd]; rfl) hm h

/-- An instruction that does not touch memory. -/
theorem wp_op {i : QInstr} {s' : QState} {rest : List Stmt} (hi : i.step s = some s')
    (h : WP (blk rest) s' P E) : WP (blk (I i :: rest)) s P E := by
  apply WP.blk_cons
  apply WP.ins'
  rw [hi]
  exact h

/-- `roli` by `n < 64` is `Keccak.rot`. -/
theorem roli_eq_rot (x : UInt64) {n : Nat} (h : n < 64) :
    UInt64.ofBitVec (x.toBitVec.rotateLeft (n % 64)) = Keccak.rot x n := by
  unfold Keccak.rot
  split
  · subst_vars
    apply UInt64.toBitVec_inj.mp
    simp only [BitVec.rotateLeft_def, Nat.zero_mod, BitVec.shiftLeft_zero, Nat.sub_zero]
    rw [BitVec.ushiftRight_eq_zero (by omega), BitVec.or_zero]
  · apply UInt64.toBitVec_inj.mp
    simp only [BitVec.rotateLeft_mod_eq_rotateLeft, Nat.toUInt64_eq, UInt64.toBitVec_or,
      UInt64.toBitVec_shiftLeft, BitVec.ofNat_eq_ofNat, BitVec.shiftLeft_eq', BitVec.toNat_umod,
      UInt64.toNat_toBitVec, UInt64.toNat_ofNat', Nat.reducePow, BitVec.toNat_ofNat,
      Nat.reduceMod, Nat.reduceDvd, Nat.mod_mod_of_dvd, UInt64.toBitVec_shiftRight,
      BitVec.ushiftRight_eq']
    rw [BitVec.rotateLeft_def, Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (by omega : 64 - n < 64)]

/-- A rotation by `n < 64` is `Keccak.rot`. -/
theorem rotl_eq_rot (x : UInt64) {n : Nat} (h : n < 64) :
    UInt64.ofBitVec (x.toBitVec.rotateLeft n) = Keccak.rot x n := by
  rw [← roli_eq_rot x h, BitVec.rotateLeft_mod_eq_rotateLeft]

/-! ## Phases -/

/-- A phase of scratch writes: piece `j` stores `val j` at scratch word `off + j`, reading the
words of the phase's range it has not written yet as they were, and the registers outside `rs`
as they were. -/
theorem phase_run {base : UInt64} (f : Nat → List Stmt) (off n : Nat) (val : Nat → UInt64)
    (rs : List Reg64) (hn : off + n ≤ 84) (hrs : Reg64.rdi ∉ rs)
    (hbody : ∀ j < n, ∀ s', s'.reg .rdi = base → ScrFrame base off (off + j) s.mem s'.mem →
      ScrOk s'.mem base → RegsFrame rs s s' →
      WP (blk (f j)) s' (fun s'' ↦
        s''.mem = Function.update s'.mem (scratchAddr base (off + j)) (some (val j)) ∧
          RegsFrame rs s' s'') E)
    (hrdi : s.reg .rdi = base) (hok : ScrOk s.mem base) :
    WP (blk ((List.range n).flatMap f)) s (fun s' ↦ ScrOk s'.mem base ∧
      RegsFrame rs s s' ∧ ScrFrame base off (off + n) s.mem s'.mem ∧
      Words s'.mem base off n val) E := by
  refine wp_range_flatMap (s := s) f (fun j s' ↦ ScrOk s'.mem base ∧
      RegsFrame rs s s' ∧ ScrFrame base off (off + j) s.mem s'.mem ∧
      Words s'.mem base off j val) n ?_ ⟨hok, RegsFrame.refl _, ScrFrame.refl _, fun t ht ↦ by
        simp at ht⟩
  intro j hj s' ⟨hok', hR, hF, hW⟩
  refine WP.mono (hbody j hj s' ((hR _ hrs).trans hrdi) hF hok' hR)
    (fun s'' ⟨hm, hR'⟩ ↦ ⟨?_, RegsFrame.trans hR hR', ?_, ?_⟩) (fun _ h ↦ h)
  · rw [hm]; exact hok'.update _ _
  · rw [hm]
    exact (hF.widen le_rfl (show off + j ≤ off + (j + 1) by omega)).trans
      (ScrFrame.update (lo := off + j) (k := off + j) (by omega) (by omega)) (by omega) le_rfl
  · intro t ht
    rw [hm]
    by_cases e : t = j
    · subst e; simp
    · rw [Function.update_of_ne (scratchAddr_ne (by omega) (by omega) (by omega))]
      exact hW t (by omega)

end Native.Keccak.Proof
