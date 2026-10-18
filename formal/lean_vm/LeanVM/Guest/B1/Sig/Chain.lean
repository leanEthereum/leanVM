/-
  LeanVM.Guest.B1.Sig.Chain

  A WOTS+C chain step, the steps of a chain and a chain's walk (`chain_step`, `walk`, G:2307-2331),
  sound and complete for the cells they hash.
-/

module

public import LeanVM.Guest.B1.Sig.Frame
public import LeanVM.Guest.B1.Sig.Hashing

/-!
# Chains

A step of chain `i` leaving position `s` hashes `stepCells`: for leanXMSS `P | A_s | v | i`, its
address `A_s` precomputed, for leanSPHINCS `P | idx + A(i, s) | v`. `chainFrom m s v` is `m + 1`
steps from position `s`, `tipCell d x` the end of a chain revealed at digit `d` with value `x`.

Each template has a soundness lemma (its relation gives the chain's cells), a completeness lemma
(`Completes`: from a valuation with the inputs canonical and the outputs preset, one on the
template's own range under which it holds) and a `NumBelow` lemma.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-! ## The cells of a chain -/

/-- A step's metadata counter: 64 bytes with the chain index (leanXMSS), 48 without. -/
def stepCount (lx : Bool) : Nat := if lx then 64 else 48

/-- The cells a step of chain `i` leaving position `s` hashes. -/
def stepCells (lx : Bool) (pp : E) (adr : Nat → E) (idx : E) (i s : Nat) (v : E) : List E :=
  if lx then [pp, adr s, v, eOfNat i] else [pp, idx + eOfNat (tw 1 + i * hiMul + s * stepMul), v]

/-- `m + 1` steps of chain `i` from position `s`. -/
def chainFrom (lx : Bool) (pp : E) (adr : Nat → E) (idx : E) (i : Nat) : Nat → Nat → E → E × E
  | 0, s, v => hcell (stepCells lx pp adr idx i s v)
  | m + 1, s, v => chainFrom lx pp adr idx i m (s + 1) (hcell (stepCells lx pp adr idx i s v)).1

/-- The end of chain `i` revealed at digit `d < 4` with the value `x`, and the other half of its
last hash. -/
def tipPair (lx : Bool) (pp : E) (adr : Nat → E) (idx : E) (i d : Nat) (x : E) : E × E :=
  if d = 3 then (x, 0) else chainFrom lx pp adr idx i (2 - d) d x

/-- What a valuation gives a chain: its public parameter, step addresses and index. -/
def Wots.pp' (w : Wots) (σ : Val) : E := σ w.pp
def Wots.adr' (w : Wots) (σ : Val) : Nat → E := fun s => σ (w.adr s)
def Wots.idx' (w : Wots) (σ : Val) : E := σ w.idx

/-- `v` is numbered outside `lo ..< hi`. -/
def Out (lo hi : Nat) (v : V) : Prop := ∀ k, lo ≤ k → k < hi → v ≠ .n k

theorem out_of_lt {lo hi : Nat} {v : V} (h : ∃ k < lo, v = .n k) : Out lo hi v := by
  obtain ⟨k, hk, rfl⟩ := h
  intro j hj _ e
  simp only [V.mk.injEq] at e
  omega

theorem out_of_ge {lo hi : Nat} {v : V} (h : ∃ k, hi ≤ k ∧ v = .n k) : Out lo hi v := by
  obtain ⟨k, hk, rfl⟩ := h
  intro j _ hj e
  simp only [V.mk.injEq] at e
  omega

theorem Out.mono {lo hi lo' hi' : Nat} {v : V} (h : Out lo hi v) (hlo : lo ≤ lo') (hhi : hi' ≤ hi) :
    Out lo' hi' v := fun k h1 h2 => h k (by omega) (by omega)

theorem Ext.out {lo hi : Nat} {σ σ' : Val} {v : V} (h : Ext lo hi σ σ') (hv : Out lo hi v) :
    σ' v = σ v := h v hv

/-- The inputs of a chain are numbered outside `lo ..< hi`. -/
structure Wots.Out (w : Wots) (lo hi : Nat) : Prop where
  pp : B1.Sig.Out lo hi w.pp
  md : B1.Sig.Out lo hi w.md
  adr : ∀ s, B1.Sig.Out lo hi (w.adr s)
  idx : B1.Sig.Out lo hi w.idx

theorem Wots.Out.mono {w : Wots} {lo hi lo' hi' : Nat} (h : w.Out lo hi) (hlo : lo ≤ lo') (hhi : hi' ≤ hi) :
    w.Out lo' hi' :=
  ⟨h.pp.mono hlo hhi, h.md.mono hlo hhi, fun s => (h.adr s).mono hlo hhi, h.idx.mono hlo hhi⟩

/-- A chain's inputs are numbered below `hi`. -/
structure Wots.Below (w : Wots) (hi : Nat) : Prop where
  pp : ∃ k < hi, w.pp = .n k
  md : ∃ k < hi, w.md = .n k
  adr : ∀ s, ∃ k < hi, w.adr s = .n k
  idx : ∃ k < hi, w.idx = .n k

theorem Wots.Below.out {w : Wots} {lo hi : Nat} (h : w.Below lo) : w.Out lo hi :=
  ⟨out_of_lt h.pp, out_of_lt h.md, fun s => out_of_lt (h.adr s), out_of_lt h.idx⟩

theorem Wots.Below.mono {w : Wots} {hi hi' : Nat} (h : w.Below hi) (hle : hi ≤ hi') : w.Below hi' :=
  ⟨let ⟨k, hk, e⟩ := h.pp; ⟨k, by omega, e⟩, let ⟨k, hk, e⟩ := h.md; ⟨k, by omega, e⟩,
    fun s => let ⟨k, hk, e⟩ := h.adr s; ⟨k, by omega, e⟩, let ⟨k, hk, e⟩ := h.idx; ⟨k, by omega, e⟩⟩

/-- The valuation keeps a chain's inputs. -/
theorem Wots.Out.keep {w : Wots} {lo hi : Nat} {σ σ' : Val} (hw : w.Out lo hi) (he : Ext lo hi σ σ') :
    w.pp' σ' = w.pp' σ ∧ w.adr' σ' = w.adr' σ ∧ w.idx' σ' = w.idx' σ ∧ σ' w.md = σ w.md :=
  ⟨he.out hw.pp, funext fun s => he.out (hw.adr s), he.out hw.idx, he.out hw.md⟩

/-- The canonical inputs a chain's steps need. -/
def Wots.Canon (w : Wots) (σ : Val) : Prop :=
  IsCanonical128 (w.pp' σ) ∧ (w.lx → ∀ s, IsCanonical128 (w.adr' σ s)) ∧
    (w.lx = false → IsCanonical128 (w.idx' σ))

theorem word_zero : word 0 0 0 = 0 := by
  rw [zero_eq_ofLimbs]; rfl

theorem canonical_stepCells {w : Wots} {σ : Val} (hc : w.Canon σ) {i s : Nat} {v : E}
    (hv : IsCanonical128 v) : ∀ c ∈ stepCells w.lx (w.pp' σ) (w.adr' σ) (w.idx' σ) i s v, IsCanonical128 c := by
  unfold stepCells
  cases hlx : w.lx
  · simp only [Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.mem_nil_iff, or_false,
      forall_eq_or_imp, forall_eq]
    exact ⟨hc.1, isCanonical128_add (hc.2.2 hlx) (isCanonical128_eOfNat _), hv⟩
  · simp only [↓reduceIte, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hc.1, hc.2.1 hlx s, hv, isCanonical128_eOfNat _⟩

/-! ## A step -/

theorem cStep_holds_iff (w : Wots) (σ : Val) (i s b : Nat) (v o0 o1 : V)
    (hmd : σ w.md = mdw (stepCount w.lx) true) (next : Prop) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (cStep w i s b v o0 o1) next kret ↔
      (if w.lx then σ (.n b) = word i 0 0 ∧ σ (.n (b + 1)) = iv0 ∧ σ (.n (b + 2)) = iv1
        else σ (.n b) = word (tw 1 + i * hiMul + s * stepMul) 0 0 ∧
          σ (.n (b + 1)) = σ w.idx + σ (.n b) ∧ σ (.n (b + 2)) = 0 ∧ σ (.n (b + 3)) = iv0 ∧
          σ (.n (b + 4)) = iv1) ∧
      (∀ c ∈ stepCells w.lx (w.pp' σ) (w.adr' σ) (w.idx' σ) i s (σ v), IsCanonical128 c) ∧
      (σ o0, σ o1) = hcell (stepCells w.lx (w.pp' σ) (w.adr' σ) (w.idx' σ) i s (σ v)) ∧ next := by
  unfold cStep
  cases hlx : w.lx
  · rw [hlx] at hmd
    simp only [Bool.false_eq_true, ↓reduceIte, cst, addS, b2s, holdsList_cons_atom, holdsList_nil,
      Atom.Holds, stepCells, Wots.pp', Wots.idx', word_zero, stepCount] at hmd ⊢
    constructor
    · rintro ⟨h0, h1, h2, h3, h4, h5, hn⟩
      rw [h3, h4, hmd, h2, h1, h0, word_eq_eOfNat, compress3_iff] at h5
      refine ⟨⟨h0, h1, h2, h3, h4⟩, ?_, h5.2, hn⟩
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
      exact h5.1
    · rintro ⟨⟨h0, h1, h2, h3, h4⟩, hc, ho, hn⟩
      refine ⟨h0, h1, h2, h3, h4, ?_, hn⟩
      rw [h3, h4, hmd, h2, h1, h0, word_eq_eOfNat, compress3_iff]
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at hc
      exact ⟨hc, ho⟩
  · rw [hlx] at hmd
    simp only [↓reduceIte, cst, b2s, holdsList_cons_atom, holdsList_nil, Atom.Holds, stepCells,
      Wots.pp', Wots.adr', stepCount] at hmd ⊢
    constructor
    · rintro ⟨h0, h1, h2, h3, hn⟩
      rw [h1, h2, hmd, h0, word_eq_eOfNat, compress4_iff] at h3
      refine ⟨⟨h0, h1, h2⟩, ?_, h3.2, hn⟩
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
      exact h3.1
    · rintro ⟨⟨h0, h1, h2⟩, hc, ho, hn⟩
      refine ⟨h0, h1, h2, ?_, hn⟩
      rw [h1, h2, hmd, h0, word_eq_eOfNat, compress4_iff]
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at hc
      exact ⟨hc, ho⟩

theorem cStep_sound {w : Wots} {σ : Val} {i s b : Nat} {v o0 o1 : V}
    (hmd : σ w.md = mdw (stepCount w.lx) true) {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (cStep w i s b v o0 o1) next kret) :
    (σ o0, σ o1) = hcell (stepCells w.lx (w.pp' σ) (w.adr' σ) (w.idx' σ) i s (σ v)) ∧ next :=
  let h' := (cStep_holds_iff w σ i s b v o0 o1 hmd next kret).mp h; ⟨h'.2.2.1, h'.2.2.2⟩

/-- The valuation setting a step's constants. -/
def stepVal (w : Wots) (σ : Val) (i s b : Nat) : Val :=
  if w.lx then Function.update (Function.update (Function.update σ (.n b) (word i 0 0)) (.n (b + 1)) iv0)
      (.n (b + 2)) iv1
  else Function.update (Function.update (Function.update (Function.update (Function.update σ
      (.n b) (word (tw 1 + i * hiMul + s * stepMul) 0 0)) (.n (b + 1))
      (σ w.idx + word (tw 1 + i * hiMul + s * stepMul) 0 0)) (.n (b + 2)) 0) (.n (b + 3)) iv0)
      (.n (b + 4)) iv1

theorem stepVal_ext (w : Wots) (σ : Val) (i s b : Nat) :
    Ext b (b + stepSize w.lx) σ (stepVal w σ i s b) := by
  intro v hv
  unfold stepVal stepSize at *
  cases hlx : w.lx <;> simp only [hlx, Bool.false_eq_true, ↓reduceIte] at hv ⊢
  · rw [Function.update_of_ne (hv _ (by omega) (by omega)), Function.update_of_ne (hv _ (by omega) (by omega)),
      Function.update_of_ne (hv _ (by omega) (by omega)), Function.update_of_ne (hv _ (by omega) (by omega)),
      Function.update_of_ne (hv _ (by omega) (by omega))]
  · rw [Function.update_of_ne (hv _ (by omega) (by omega)), Function.update_of_ne (hv _ (by omega) (by omega)),
      Function.update_of_ne (hv _ (by omega) (by omega))]

theorem stepVal_at (w : Wots) (σ : Val) (i s b : Nat) :
    (if w.lx then stepVal w σ i s b (.n b) = word i 0 0 ∧ stepVal w σ i s b (.n (b + 1)) = iv0 ∧
        stepVal w σ i s b (.n (b + 2)) = iv1
      else stepVal w σ i s b (.n b) = word (tw 1 + i * hiMul + s * stepMul) 0 0 ∧
        stepVal w σ i s b (.n (b + 1)) = σ w.idx + stepVal w σ i s b (.n b) ∧
        stepVal w σ i s b (.n (b + 2)) = 0 ∧ stepVal w σ i s b (.n (b + 3)) = iv0 ∧
        stepVal w σ i s b (.n (b + 4)) = iv1) := by
  unfold stepVal
  cases w.lx <;> simp

/-- **A step is complete**: its inputs and outputs outside its constants, canonical inputs and
the outputs preset to the hash. -/
theorem cStep_complete {w : Wots} {σ : Val} {i s b : Nat} {v o0 o1 : V}
    (hw : w.Out b (b + stepSize w.lx)) (hv : Out b (b + stepSize w.lx) v)
    (ho0 : Out b (b + stepSize w.lx) o0) (ho1 : Out b (b + stepSize w.lx) o1)
    (hmd : σ w.md = mdw (stepCount w.lx) true) (hc : w.Canon σ) (hvc : IsCanonical128 (σ v))
    (ho : (σ o0, σ o1) = hcell (stepCells w.lx (w.pp' σ) (w.adr' σ) (w.idx' σ) i s (σ v))) :
    Completes C rd b (b + stepSize w.lx) (cStep w i s b v o0 o1) σ (fun _ => True) := by
  have he := stepVal_ext w σ i s b
  obtain ⟨hpp, hadr, hidx, hmd'⟩ := hw.keep he
  refine ⟨stepVal w σ i s b, he, trivial, fun next kret hn => ?_⟩
  have hc' : w.Canon (stepVal w σ i s b) := by rw [Wots.Canon, hpp, hadr, hidx]; exact hc
  rw [cStep_holds_iff w _ i s b v o0 o1 (by rw [hmd', hmd]), hpp, hadr, hidx, he.out hv, he.out ho0,
    he.out ho1]
  refine ⟨?_, canonical_stepCells hc hvc, ho, hn⟩
  rw [he.out hw.idx]
  exact stepVal_at w σ i s b

theorem cStep_below {w : Wots} {hi i s b : Nat} {v o0 o1 : V} (hw : w.Below hi)
    (hv : ∃ k < hi, v = .n k) (ho0 : ∃ k < hi, o0 = .n k) (ho1 : ∃ k < hi, o1 = .n k)
    (hb : b + stepSize w.lx ≤ hi) : NumBelow hi (Stmt.valsList (cStep w i s b v o0 o1)) := by
  unfold cStep stepSize at *
  cases hlx : w.lx <;> simp only [hlx, Bool.false_eq_true, ↓reduceIte] at hb ⊢ <;>
    simp only [cst, addS, b2s, valsList_cons, valsList_nil, Stmt.vals, Atom.vals, List.cons_append,
      List.nil_append, List.append_nil] <;>
    first
    | exact .cons ⟨b, by omega, rfl⟩ (.cons ⟨b + 1, by omega, rfl⟩ (.cons hw.idx (.cons ⟨b, by omega, rfl⟩
        (.cons ⟨b + 2, by omega, rfl⟩ (.cons ⟨b + 3, by omega, rfl⟩ (.cons ⟨b + 4, by omega, rfl⟩
        (.cons hw.pp (.cons ⟨b + 1, by omega, rfl⟩ (.cons hv (.cons ⟨b + 2, by omega, rfl⟩
        (.cons ⟨b + 3, by omega, rfl⟩ (.cons ⟨b + 4, by omega, rfl⟩ (.cons ho0 (.cons ho1
        (.cons hw.md (.nil hi))))))))))))))))
    | exact .cons ⟨b, by omega, rfl⟩ (.cons ⟨b + 1, by omega, rfl⟩ (.cons ⟨b + 2, by omega, rfl⟩
        (.cons hw.pp (.cons (hw.adr s) (.cons hv (.cons ⟨b, by omega, rfl⟩ (.cons ⟨b + 1, by omega, rfl⟩
        (.cons ⟨b + 2, by omega, rfl⟩ (.cons ho0 (.cons ho1 (.cons hw.md (.nil hi))))))))))))

end
end LeanVM.Guest.B1.Sig
