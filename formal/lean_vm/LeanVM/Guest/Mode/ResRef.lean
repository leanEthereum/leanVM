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

The nonzero residuals all sit at a back-solved `MUL` `[c] = [a]·[o]`, `o` the divisor (`nzMul`, a
kernel check per function). On the reference that `MUL` holds (`ref_mul`, from `OnRef`), so the
divisor is nonzero where the product is (`nz_mul`): the residual moves from the divisor to the
product cell (`numAt`), and is discharged outright when the product cell holds a nonzero word the
frame fixes (`nz_read`, a `SET`'s constant: `FrameHolds.stat`). The order residuals of `walk_path`
are window bounds (`ltWin`), each holding where the reference's windows do (`RWins`, `lt_win`).
`resRef_mul`, `resRef_win`: one function's `ResRef` by these families.
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

/-- `ResRef` from each certificate's own. -/
theorem resRef_of {prog : LeanIsaProgram} {κ : ℕ} {img : MemoryImage κ} {n : ℕ} {Ks : List Cert}
    {X : St → Prop} (h : ∀ Kc ∈ Ks, ResRef prog img n [Kc] X) : ResRef prog img n Ks X :=
  fun Kc hK ↦ h Kc hK Kc (List.mem_singleton_self _)

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

/-- The product cell of the `MUL` at an offset. -/
def numAt (code : List OffsetInstruction) (i : ℕ) : ℕ :=
  match code[i]? with
  | some (.mul _ _ c) => c
  | _ => 0

/-- A residual sits at a `MUL` as its divisor, if nonzero. -/
def nzAt (ins : Option OffsetInstruction) : Res → Bool
  | .nz o => match ins with
    | some (.mul _ b _) => b == o
    | _ => false
  | _ => true

/-- **Every nonzero residual is a `MUL`'s divisor**, at its offset. -/
def nzMul (F : Fun) (code : List OffsetInstruction) : Bool :=
  (List.range code.length).all fun i ↦ ((F.res.get i).getD []).all (nzAt code[i]?)

/-- **A nonzero residual from its product**: at a state on the reference at a certificate's offset,
a nonzero residual there holds of the reference once the product cell of its `MUL` is nonzero. -/
theorem nz_mul {prog : LeanIsaProgram} {adv : Advice} {κ n : ℕ} {img : MemoryImage κ} {C : Ctx}
    (hκ : κ ≤ 28) (hC : Ctx.of prog adv = .ok C) {Kc : Cert} (hK : CertOk C Kc)
    (hm : nzMul Kc.F Kc.code = true) {s : St} (hs : Fine (refMem img) s) (hon : OnRef prog img n s)
    {i : ℕ} (hi : i < Kc.code.length) (hpc : s.pc = Kc.F.entry + i) {o : ℕ}
    (hr : Res.nz o ∈ (Kc.F.res.get i).getD []) (hnum : refMem img (s.fp + numAt Kc.code i) ≠ 0) :
    RRes (refMem img) s.fp (.nz o) := by
  have h1 := List.all_eq_true.mp (List.all_eq_true.mp hm i (List.mem_range.mpr hi)) _ hr
  rw [List.getElem?_eq_getElem hi] at h1
  have hop := hK.ops i hi
  rw [← hpc] at hop
  unfold numAt at hnum
  rw [List.getElem?_eq_getElem hi] at hnum
  generalize Kc.code[i] = ins at h1 hop hnum
  cases ins with
  | mul a b c =>
    simp only [nzAt, beq_iff_eq] at h1
    subst h1
    have e := ref_mul hκ hC hs hon (a := a) (b := b) (c := c) hop
    rw [e] at hnum
    exact right_ne_zero_of_mul hnum
  | _ => simp [nzAt] at h1

/-- A cell the reference image holds a nonzero word at is nonzero in `refMem`. -/
theorem nz_read {κ : ℕ} (hκ : κ ≤ 28) {img : MemoryImage κ} {c : ℕ} (hc : c < 2 ^ 62) {w : E}
    (h : img.read (addressOfIndex c) = some w) (hw : w ≠ 0) : refMem img c ≠ 0 := by
  rw [((refRd_img hκ img) c w hc h).2]
  exact hw


/-! ## Window bounds -/

/-- The reference's windows at frame cell `q`: each cell `k < n` past the cell `[q]` names holds
`g^e`, `e < N`. -/
def RWins (M : ℕ → E) (fp q n N : ℕ) : Prop :=
  ∀ k < n, ∀ x, Names (M (fp + q) * ofK (g ^ k)) x → ∃ e < N, M x = ofK (g ^ e)

/-- A residual, if an order, is a window's bound: `[[q]·g^k]`'s exponent below `N`, `k < n`. -/
def winAt (q n N : ℕ) : Res → Bool
  | .lt (.ex (.hp q' k) 0) (.num N') => q' == q && decide (k < n) && N' == N
  | .lt _ _ => false
  | _ => true

/-- **Every order residual is a window's bound.** -/
def ltWin (F : Fun) (len q n N : ℕ) : Bool :=
  (List.range len).all fun i ↦ ((F.res.get i).getD []).all (winAt q n N)

/-- **The order residuals from the windows**: at an offset of a function whose order residuals are
all window bounds, each holds of the reference wherever its windows do. -/
theorem lt_win {M : ℕ → E} {fp q n N : ℕ} (hN : N ≤ 2 ^ 62) (hw : RWins M fp q n N) {Kc : Cert}
    (hc : ltWin Kc.F Kc.code.length q n N = true) {i : ℕ} (hi : i < Kc.code.length) {a b : Idx}
    (hr : Res.lt a b ∈ (Kc.F.res.get i).getD []) (hin : RIn M fp (.lt a b)) : RRes M fp (.lt a b) := by
  have h1 := List.all_eq_true.mp (List.all_eq_true.mp hc i (List.mem_range.mpr hi)) _ hr
  match a, b, h1, hin with
  | .ex (.hp q' k) 0, .num N', h1, ⟨⟨_, x, hx, _⟩, _⟩ =>
    simp only [winAt, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h1
    obtain ⟨⟨rfl, hk⟩, rfl⟩ := h1
    obtain ⟨e, he, hxe⟩ := hw k hk x hx
    exact ⟨e, _, ⟨M x, e, ⟨x, hx, rfl⟩, hxe, by omega, rfl⟩, rfl, he⟩
  | .ex (.hp _ _) (_ + 1), _, h1, _ => simp [winAt] at h1
  | .ex (.hp _ _) 0, .ex _ _, h1, _ => simp [winAt] at h1
  | .ex (.fr _) _, _, h1, _ => simp [winAt] at h1
  | .num _, _, h1, _ => simp [winAt] at h1


/-! ## A function's residuals by family -/

/-- **A function's residuals, its nonzero ones from their products**: `ResRef` for one certificate
whose nonzero residuals are `MUL` divisors, given each product cell nonzero on the reference and the
other residuals on the reference. -/
theorem resRef_mul {prog : LeanIsaProgram} {adv : Advice} {κ n : ℕ} {img : MemoryImage κ} {C : Ctx}
    {X : St → Prop} {Kc : Cert} (hκ : κ ≤ 28) (hC : Ctx.of prog adv = .ok C) (hK : CertOk C Kc)
    (hm : nzMul Kc.F Kc.code = true)
    (hnum : ∀ s i, X s → Fine (refMem img) s → OnRef prog img n s → i < Kc.code.length →
      s.pc = Kc.F.entry + i → ∀ o, Res.nz o ∈ (Kc.F.res.get i).getD [] →
        refMem img (s.fp + numAt Kc.code i) ≠ 0)
    (hother : ∀ s i, X s → Fine (refMem img) s → OnRef prog img n s → i < Kc.code.length →
      s.pc = Kc.F.entry + i → ∀ r ∈ (Kc.F.res.get i).getD [], (∀ o, r ≠ .nz o) →
        RIn (refMem img) s.fp r → RRes (refMem img) s.fp r) :
    ResRef prog img n [Kc] X := by
  intro K' hK' s i hX hs hon hi hpc r hr hin
  rw [List.mem_singleton] at hK'
  subst hK'
  cases r with
  | nz o => exact nz_mul hκ hC hK hm hs hon hi hpc hr (hnum s i hX hs hon hi hpc o hr)
  | lt a b => exact hother s i hX hs hon hi hpc _ hr (fun _ h ↦ by cases h) hin
  | sub a bs => exact hother s i hX hs hon hi hpc _ hr (fun _ h ↦ by cases h) hin
  | name o => exact hother s i hX hs hon hi hpc _ hr (fun _ h ↦ by cases h) hin

/-- **A function's residuals, its orders from its windows**: `ResRef` for one certificate whose
order residuals are window bounds, given its windows on the reference at every state and the other
residuals on the reference. -/
theorem resRef_win {prog : LeanIsaProgram} {κ n : ℕ} {img : MemoryImage κ} {X : St → Prop} {Kc : Cert}
    {q w N : ℕ} (hN : N ≤ 2 ^ 62) (hc : ltWin Kc.F Kc.code.length q w N = true)
    (hw : ∀ s i, X s → Fine (refMem img) s → OnRef prog img n s → i < Kc.code.length →
      s.pc = Kc.F.entry + i → RWins (refMem img) s.fp q w N)
    (hother : ∀ s i, X s → Fine (refMem img) s → OnRef prog img n s → i < Kc.code.length →
      s.pc = Kc.F.entry + i → ∀ r ∈ (Kc.F.res.get i).getD [], (∀ a b, r ≠ .lt a b) →
        RIn (refMem img) s.fp r → RRes (refMem img) s.fp r) :
    ResRef prog img n [Kc] X := by
  intro K' hK' s i hX hs hon hi hpc r hr hin
  rw [List.mem_singleton] at hK'
  subst hK'
  cases r with
  | lt a b => exact lt_win hN (hw s i hX hs hon hi hpc) hc hi hr hin
  | nz o => exact hother s i hX hs hon hi hpc _ hr (fun _ _ h ↦ by cases h) hin
  | sub a bs => exact hother s i hX hs hon hi hpc _ hr (fun _ _ h ↦ by cases h) hin
  | name o => exact hother s i hX hs hon hi hpc _ hr (fun _ _ h ↦ by cases h) hin

end

end LeanVM.Guest.Mode
