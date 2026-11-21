module

public import LeanVM.Guest.Mode.InvRule

/-!
# The residuals, on the reference

`Prem.res` asks each residual of the walk (`ResHolds`) of the executor's state. `RRes M fp r` states
it of the reference `M` alone, at frame `fp`: a base's word is `M`'s at its cell (`RBase`), an
exponent's value read off it (`RIdx`), a run's product likewise (`RMono`). `resHolds_of_ref`: once a
residual's cells are written (`ResIn`), the executor's words are `M`'s (`Fine`), so `RRes` gives
`ResHolds`; `prem_res`: `Prem.res` from `ResRef`, `RRes` at every state of every certificate's
function, wherever the residual's bases have words in `M` (`RIn`, from `ResIn`).

`ref_mul`: on the reference a `MUL` holds (from `OnRef`).
-/

namespace LeanVM.Guest.Mode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest
open LeanVM.Prover.Exec

@[expose] public section

/-! ## The residuals on the reference -/

/-- Base `b`'s word in the reference `M` at frame `fp`. -/
def RBase (M : ℕ → E) (fp : ℕ) : Base → E → Prop
  | .fr o, v => M (fp + o) = v
  | .hp q d, v => ∃ x, Names (M (fp + q) * ofK (g ^ d)) x ∧ M x = v

/-- A base list's product in `M`. -/
def RBs (M : ℕ → E) (fp : ℕ) : List (Base × ℕ) → E → Prop
  | [], v => v = 1
  | (b, e) :: bs, v => ∃ u w, RBase M fp b u ∧ RBs M fp bs w ∧ v = u ^ e * w

/-- A product's word in `M`. -/
def RMono (M : ℕ → E) (fp : ℕ) (m : Mono) (v : E) : Prop :=
  ∃ w, RBs M fp m.bs w ∧ v = ofK (g ^ fp) ^ m.fp * ofK (g ^ m.k) * w

/-- An exponent's value in `M`. -/
def RIdx (M : ℕ → E) (fp : ℕ) : Idx → ℕ → Prop
  | .num n, x => x = n
  | .ex b c, x => ∃ v e, RBase M fp b v ∧ v = ofK (g ^ e) ∧ e < 2 ^ 62 ∧ x = e + c

/-- `SubF` in `M`. -/
def RSub (M : ℕ → E) (fp : ℕ) (a : Rng) (bs : List Rng) : Prop :=
  ∃ xlo xhi, RIdx M fp a.lo xlo ∧ RIdx M fp a.hi xhi ∧ ∀ vq, RMono M fp a.q vq → ∀ j, xlo ≤ j → j < xhi →
    ∃ b ∈ bs, ∀ vb ylo yhi, RMono M fp b.q vb → RIdx M fp b.lo ylo → RIdx M fp b.hi yhi →
      ∃ j', ylo ≤ j' ∧ j' < yhi ∧ vq * ofK (g ^ (a.S * j + a.d)) = vb * ofK (g ^ (b.S * j' + b.d))

/-- **A residual on the reference** `M` at frame `fp`. -/
def RRes (M : ℕ → E) (fp : ℕ) : Res → Prop
  | .lt a b => ∃ xa xb, RIdx M fp a xa ∧ RIdx M fp b xb ∧ xa < xb
  | .nz o => M (fp + o) ≠ 0
  | .sub a bs => RSub M fp a bs
  | .name _ => True

section

variable {M : ℕ → E} {s : St}

theorem rbase_of (h : Agree s.mem M) : ∀ {b : Base} {v : E}, BaseVal s b v → RBase M s.fp b v
  | .fr _, _, hv => h.get _ _ hv
  | .hp _ _, _, ⟨_, x, hp, hx, hv⟩ => ⟨x, by rw [h.get _ _ hp]; exact hx, h.get _ _ hv⟩

theorem rbs_of (h : Agree s.mem M) : ∀ {bs : List (Base × ℕ)} {v : E}, BsVal s bs v → RBs M s.fp bs v
  | [], _, hv => hv
  | (_, _) :: _, _, ⟨u, w, hu, hw, hv⟩ => ⟨u, w, rbase_of h hu, rbs_of h hw, hv⟩

theorem rmono_of (h : Agree s.mem M) {m : Mono} {v : E} (hv : MonoVal s m v) : RMono M s.fp m v :=
  let ⟨w, hw, e⟩ := hv
  ⟨w, rbs_of h hw, e⟩

theorem ridx_of (h : Agree s.mem M) : ∀ {i : Idx} {x : ℕ}, IdxVal s i x → RIdx M s.fp i x
  | .num _, _, hx => hx
  | .ex _ _, _, ⟨v, e, hv, h1, h2, h3⟩ => ⟨v, e, rbase_of h hv, h1, h2, h3⟩

theorem names_uniq {u : E} {x y : ℕ} (hx : Names u x) (hy : Names u y) : x = y :=
  gpow_inj (by have := hx.2; unfold maxCells at this; omega)
    (by have := hy.2; unfold maxCells at this; omega) (hx.1.symm.trans hy.1)

theorem rbase_uniq {fp : ℕ} : ∀ {b : Base} {v v' : E}, RBase M fp b v → RBase M fp b v' → v = v'
  | .fr _, _, _, h1, h2 => h1.symm.trans h2
  | .hp _ _, _, _, ⟨_, hx, h1⟩, ⟨_, hy, h2⟩ => by rw [← h1, ← h2, names_uniq hx hy]

theorem idx_of_ref (h : Agree s.mem M) : ∀ {i : Idx} {x : ℕ}, IdxIn s i → RIdx M s.fp i x → IdxVal s i x
  | .num _, _, _, hx => hx
  | .ex _ _, _, ⟨v', hv'⟩, ⟨_, e, hv, h1, h2, h3⟩ =>
    ⟨v', e, hv', (rbase_uniq (rbase_of h hv') hv).trans h1, h2, h3⟩

/-- **A residual on the reference holds of the executor** once its cells are written. -/
theorem resHolds_of_ref (h : Agree s.mem M) : ∀ {r : Res}, ResIn s r → RRes M s.fp r → ResHolds s r
  | .lt _ _, ⟨ha, hb⟩, ⟨xa, xb, h1, h2, h3⟩ =>
    show LTF s _ _ from ⟨xa, xb, idx_of_ref h ha h1, idx_of_ref h hb h2, h3⟩
  | .nz _, hw, hne => by
    obtain ⟨u, hu⟩ := Mem.get_of_written hw
    exact ⟨u, hu, by rw [← h.get _ _ hu]; exact hne⟩
  | .sub _ _, ⟨hlo, hhi⟩, ⟨xlo, xhi, h1, h2, hk⟩ =>
    show SubF s _ _ from ⟨xlo, xhi, idx_of_ref h hlo h1, idx_of_ref h hhi h2, fun vq hq j hj1 hj2 ↦
      (hk vq (rmono_of h hq) j hj1 hj2).imp fun _ ⟨hb, hk'⟩ ↦
        ⟨hb, fun vb ylo yhi e1 e2 e3 ↦ hk' vb ylo yhi (rmono_of h e1) (ridx_of h e2) (ridx_of h e3)⟩⟩
  | .name _, _, _ => trivial

end

/-- An exponent's base has a word in `M`. -/
def RIdxIn (M : ℕ → E) (fp : ℕ) : Idx → Prop
  | .num _ => True
  | .ex b _ => ∃ v, RBase M fp b v

/-- A residual's bases have words in `M`. -/
def RIn (M : ℕ → E) (fp : ℕ) : Res → Prop
  | .lt a b => RIdxIn M fp a ∧ RIdxIn M fp b
  | .nz _ => True
  | .sub a _ => RIdxIn M fp a.lo ∧ RIdxIn M fp a.hi
  | .name _ => True

theorem rin_of {M : ℕ → E} {s : St} (h : Agree s.mem M) : ∀ {r : Res}, ResIn s r → RIn M s.fp r
  | .lt _ _, ⟨ha, hb⟩ => ⟨ridxIn_of h ha, ridxIn_of h hb⟩
  | .nz _, _ => trivial
  | .sub _ _, ⟨ha, hb⟩ => ⟨ridxIn_of h ha, ridxIn_of h hb⟩
  | .name _, _ => trivial
where
  ridxIn_of {M : ℕ → E} {s : St} (h : Agree s.mem M) : ∀ {i : Idx}, IdxIn s i → RIdxIn M s.fp i
    | .num _, _ => trivial
    | .ex _ _, ⟨v, hv⟩ => ⟨v, rbase_of h hv⟩

/-- **The residuals on the reference**: at each state of the run at an offset of a certificate's
function, each residual there whose bases have words holds of the reference at the state's frame. -/
def ResRef (prog : LeanIsaProgram) {κ : ℕ} (img : MemoryImage κ) (n : ℕ) (Ks : List Cert)
    (X : St → Prop) : Prop :=
  ∀ Kc ∈ Ks, ∀ s i, X s → Fine (refMem img) s → OnRef prog img n s → i < Kc.code.length →
    s.pc = Kc.F.entry + i → ∀ r ∈ (Kc.F.res.get i).getD [], RIn (refMem img) s.fp r →
      RRes (refMem img) s.fp r

/-- **`Prem.res` from the reference.** -/
theorem prem_res {prog : LeanIsaProgram} {κ : ℕ} {img : MemoryImage κ} {n : ℕ} {Ks : List Cert}
    {X : St → Prop} (h : ResRef prog img n Ks X) :
    ∀ Kc ∈ Ks, ∀ s i, X s → Fine (refMem img) s → OnRef prog img n s → i < Kc.code.length →
      s.pc = Kc.F.entry + i → ∀ s1, Moves (refMem img) s s1 → ∀ r ∈ (Kc.F.res.get i).getD [],
        ResIn s1 r → ResHolds s1 r :=
  fun Kc hK s i hX hs hon hi hpc s1 hm r hr hin ↦ by
    have hin' := rin_of hm.fine.agree hin
    rw [hm.fp] at hin'
    have h' := h Kc hK s i hX hs hon hi hpc r hr hin'
    rw [← hm.fp] at h'
    exact resHolds_of_ref hm.fine.agree hin h'

/-! ## Nonzero divisors -/

/-- **The reference's `MUL`**: at a state on the reference run whose instruction is `[c] = [a]·[b]`,
the reference's words satisfy it. -/
theorem ref_mul {prog : LeanIsaProgram} {adv : Advice} {κ n : ℕ} {img : MemoryImage κ} {C : Ctx}
    (hκ : κ ≤ 28) (hC : Ctx.of prog adv = .ok C) {s : St} (hs : Fine (refMem img) s)
    (hon : OnRef prog img n s) {a b c : ℕ} (hop : C.ops[s.pc]? = some (.mul a b c)) :
    refMem img (s.fp + c) = refMem img (s.fp + a) * refMem img (s.fp + b) := by
  obtain ⟨hsize, hdecC⟩ := ctx_of_spec hC
  obtain ⟨hlt, hrun⟩ := hon
  obtain ⟨hpc, hop'⟩ := Array.getElem?_eq_some_iff.mp hop
  have hsm := ctx_small hC s.pc hpc
  rw [hop'] at hsm
  have hpc2 : s.pc < 2 ^ prog.logSize := hsize ▸ hpc
  have hdec := hdecC s.pc hpc2 hpc
  rw [hop'] at hdec
  obtain ⟨k, hk⟩ : ∃ k, n - s.steps = k + 1 := ⟨n - s.steps - 1, by omega⟩
  rw [hk] at hrun
  have hne : (⟨g ^ s.pc, g ^ s.fp⟩ : Registers K) ≠ Registers.final prog := fun h ↦ by
    rw [run_succ, ite_eq_left h] at hrun; cases hrun
  rw [run_succ_of_ne_final hne, Option.bind_eq_bind, Option.bind_eq_some_iff] at hrun
  obtain ⟨r1, hstep, -⟩ := hrun
  rw [step_of_fetch_eq_some (prog.fetch_gpow ⟨s.pc, hpc2⟩), LeanVM.Semantics.execute] at hstep
  generalize prog.instructions ⟨s.pc, hpc2⟩ = ins at hstep hdec
  cases ins <;> simp only [OpOf] at hdec
  obtain ⟨rfl, rfl, rfl⟩ := hdec
  simp only [executeWith, Option.bind_eq_bind, Option.bind_eq_some_iff] at hstep
  obtain ⟨vA, hA, vB, hB, vC, hC', hg⟩ := hstep
  simp [guard] at hg
  obtain ⟨rfl, -⟩ := hg
  obtain ⟨ha, hb, hc⟩ := hsm
  rw [((refRd_img hκ img).at hs.fp ha hA).2, ((refRd_img hκ img).at hs.fp hb hB).2,
    ((refRd_img hκ img).at hs.fp hc hC').2]

end

end LeanVM.Guest.Mode
