module

public import Quantum.Xmss.Assembly.EndReads
public import Quantum.Xmss.Assembly.GameT
public import Quantum.Xmss.EncCost

@[expose] public section

/-!
# The winning runs of the canonical game, decomposed along the verification's reads

EndReads' `WinDecomp` for the canonical game `wGame A L` (Security's `gameR`), with the game itself
as the event-bound program, hence Security's `endReads` (`endReads_wGame`) from the prefix
invariant `PrefixWinFacts` (open).

* **The game's shape** (`wGame_eq`): the challenge prefix `wPrefix A L`, then the verification's
  read program `wReads L pre` (`readsProgram` of the verification, its reads returned), then the
  winning condition and the verification's verdict.
* **Read programs answer as functions of the decompressed register** (`SuppTo`, `suppTo_readCall`,
  `suppTo_readsProgram`): run lifted, realized and in the decompressed basis (EndReads' `decR`), a
  read keeps the register and returns the view's cell; the read program of a hash-query
  computation returns its honest evaluation against the register's functions `regFns`.
* **Runs on the trivial register** (`runSig`, `ofReal_trace_conj_runSig`): the final branch at
  `true` of `x >>= y >>= f` splits, through any Kraus operator, along the runs of `x` and `y`.
* **The decomposition** (`wDecomp`): one operator per prefix outcome `pre` and run `(true, reads)`
  of the verification, when the winning condition holds; the log is the run's reads. Recorded:
  no empty decompressed cell (`noBot_runtimeR`) and the reads are the honest verification's
  against the register's functions, hence held by the view. In the event: on the prefix's facts
  (`PreFacts`: public key, transcript signatures and records of a selection function, exempted
  slots public), at most `progCap` hardwired cells and an accepting honest verification held by
  the view, `mem_bad_of_agrees`.
-/

open Matrix OracleSpec
open scoped Kronecker ComplexOrder ENNReal

namespace Quantum.Xmss.Assembly

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss.Hybrid
open HashSig HashSig.OverPermutation LeanXmss Common Common.SufCma LeanXmss.RandomPermutationModel

/-! ## Support through a call -/

/-- **A call moves the support of the runtime register** as its port's step does. -/
theorem querySupportedOn_queryStep_imp {spec : QuantumOracleSpec.{0, 0}} (R : QuantumRuntime spec)
    {A : QReg} (i : spec.Port) (E : QReg) (ℓ : A ≃ spec.In i × E) (r : spec.Result i)
    (P P' : Set R.D)
    (hR : ∀ σ : Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ,
      QuerySupportedOn (fun m : spec.In i × R.D ↦ m.2) P σ →
        QuerySupportedOn (fun m : spec.Out i × R.D ↦ m.2) P' ((R.step i).branch r σ))
    {ρ : Matrix (A × R.D) (A × R.D) ℂ} (h : QuerySupportedOn (fun m : A × R.D ↦ m.2) P ρ) :
    QuerySupportedOn (fun m : (spec.Out i × E) × R.D ↦ m.2) P'
      ((R.queryStep i E ℓ).branch r ρ) := by
  rw [QuantumRuntime.queryStep_branch_apply, DSubInstrument.branch_frame_apply]
  have h₁ := (h.branch_relabel (QuantumRuntime.queryEquivIn ℓ R.D)).imp
    (q' := fun m : (spec.In i × R.D) × E ↦ m.1.2) (S' := P) fun m hm ↦ by
      obtain ⟨y, rfl⟩ := (QuantumRuntime.queryEquivIn ℓ R.D).surjective m
      rwa [Function.comp_apply, Equiv.symm_apply_apply] at hm
  have h₂ := QuerySupportedOn.amplify_fst (q := fun m : spec.In i × R.D ↦ m.2)
    (q' := fun m : spec.Out i × R.D ↦ m.2) (fun σ hσ ↦ hR σ hσ) h₁
  refine (h₂.branch_relabel (QuantumRuntime.queryEquivOut _ R.D E)).imp fun m hm ↦ ?_
  obtain ⟨y, rfl⟩ := (QuantumRuntime.queryEquivOut _ R.D E).surjective m
  rwa [Function.comp_apply, Equiv.symm_apply_apply] at hm

/-! ## A read in the decompressed basis -/

section decRead

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]

omit [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] in
/-- An entry of a decompressed classical Kraus operator of the register: the condition holds, the
classical part moves along `φ`, and the database factor's entry is nonzero. -/
theorem clsKraus_dec_ne_zero [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
    [AddCommGroup X] [AddCommGroup Z] {M' : Type} [Fintype M'] [DecidableEq M']
    (p : Hw X Z × M' → Prop) [DecidablePred p] (φ : Hw X Z × M' → Hw X Z × M')
    (R : Hw X Z × M' → Matrix (DbReg X Z) (DbReg X Z) ℂ) {m' m : Unit × HwReg X Z M'}
    (h : (((1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg X Z M') *
      ((1 : Matrix Unit Unit ℂ) ⊗ₖ clsKraus p φ R) *
      ((1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg X Z M')) m' m ≠ 0) :
    p m.2.2 ∧ m'.2.2 = φ m.2.2 ∧ (compressDbs X Z * R m.2.2 * compressDbs X Z) m'.2.1 m.2.1 ≠ 0 := by
  rw [← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul, Matrix.one_mul, compressReg,
    kron_one_mul_clsKraus_mul_kron_one] at h
  have h' := (one_kronecker_ne_zero (a := m.1) (a' := m'.1) (b := m.2) (b' := m'.2) h).2
  rw [clsKraus_apply] at h'
  split_ifs at h' with hc
  · exact ⟨hc.1, hc.2, h'⟩
  · exact absurd rfl h'

omit [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] in
/-- An entry of a decompressed operator on the three databases splits into the three factors. -/
theorem dbs_dec_ne_zero [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
    {N₁ : Matrix (Database Z X) (Database Z X) ℂ} {N₂ N₃ : Matrix (Database X Z) (Database X Z) ℂ}
    {D' D : DbReg X Z}
    (h : (compressDbs X Z * (N₁ ⊗ₖ (N₂ ⊗ₖ N₃)) * compressDbs X Z) D' D ≠ 0) :
    (compressAll Z X * N₁ * compressAll Z X) D'.1 D.1 ≠ 0 ∧
      (compressAll X Z * N₂ * compressAll X Z) D'.2.1 D.2.1 ≠ 0 ∧
        (compressAll X Z * N₃ * compressAll X Z) D'.2.2 D.2.2 ≠ 0 := by
  rw [compressDbs_mul_kron_mul_compressDbs, kroneckerMap_apply, kroneckerMap_apply] at h
  exact ⟨left_ne_zero_of_mul h, left_ne_zero_of_mul (right_ne_zero_of_mul h),
    right_ne_zero_of_mul (right_ne_zero_of_mul h)⟩

/-- A decompressed read entry: diagonal, and the cell (hardwired or in the database) is the
outcome. -/
theorem cellRead_dec_ne_zero {A Y : Type} [Fintype A] [DecidableEq A] [Fintype Y] [DecidableEq Y]
    [Nonempty Y] {w : Database A Y} {a : A} {o : Option Y} {D' D : Database A Y}
    (h : (compressAll A Y * cellRead w a o * compressAll A Y) D' D ≠ 0) :
    D' = D ∧ (w a).or (D a) = o := by
  rw [compressAll_mul_cellRead_mul_compressAll] at h
  by_cases hD : D' = D
  · subst hD
    rw [diagonal_apply_eq] at h
    split_ifs at h with hc
    · exact ⟨rfl, hc⟩
    · exact absurd rfl h
  · exact absurd (diagonal_apply_ne _ hD) h

/-- A decompressed identity entry is diagonal. -/
theorem one_dec_ne_zero {A Y : Type} [Fintype A] [DecidableEq A] [Fintype Y] [DecidableEq Y]
    [Nonempty Y] {D' D : Database A Y}
    (h : (compressAll A Y * (1 : Matrix (Database A Y) (Database A Y) ℂ) * compressAll A Y) D' D ≠ 0) :
    D' = D := by
  rw [Matrix.mul_one, compressAll_mul_self] at h
  by_contra hD
  exact h (Matrix.one_apply_ne hD)

variable [AddCommGroup X] [AddCommGroup Z] [Nonempty X] [Nonempty Z]
  {S : Type} [Fintype S] [DecidableEq S] {M : Type} [Fintype M] [DecidableEq M]

/-- The answer of a read of `c` (inner memory `M`) on the register `s`: the view's cell and the
inner memory. -/
def viewAns (s : HwReg X Z (Finset S × M)) : (c : HwRead X Z M) → c.Result
  | .readH z _ => ((hwView s.2.1 s.1).1 z, s.2.2.2)
  | .readK x _ => ((hwView s.2.1 s.1).2.1 x, s.2.2.2)
  | .readK' x _ => ((hwView s.2.1 s.1).2.2 x, s.2.2.2)

/-- The answer of the lifted read of `c` on the register `s`: the view's cell and the memory. -/
def liftAns (s : HwReg X Z (Finset S × M)) :
    (c : HwRead X Z M) → (recHwSpec X Z S M).Result (.inl (.inl (.inr (liftRead c))))
  | .readH z _ => ((hwView s.2.1 s.1).1 z, s.2.2)
  | .readK x _ => ((hwView s.2.1 s.1).2.1 x, s.2.2)
  | .readK' x _ => ((hwView s.2.1 s.1).2.2 x, s.2.2)

/-- The result of a lifted read, read back as the result of the read: the inner memory. -/
def lowerRes : (c : HwRead X Z M) → (recHwSpec X Z S M).Result (.inl (.inl (.inr (liftRead c)))) →
    c.Result
  | .readH _ _, r => (r.1, r.2.2)
  | .readK _ _, r => (r.1, r.2.2)
  | .readK' _ _, r => (r.1, r.2.2)

omit [AddCommGroup X] [AddCommGroup Z] [Nonempty X] [Nonempty Z] [Fintype S] [DecidableEq S]
  [Fintype M] [DecidableEq M] in
theorem lowerRes_liftAns (s : HwReg X Z (Finset S × M)) (c : HwRead X Z M) :
    lowerRes c (liftAns s c) = viewAns s c := by
  cases c <;> rfl

/-- **A read that keeps the memory, in the decompressed basis**: it keeps the register and returns
the view's cell with the memory. -/
theorem decR_read_supp (m₀ : Finset S × M) (c : HwRead X Z M) (hc : c.KeepsMem)
    (r : (recHwSpec X Z S M).Result (.inl (.inl (.inr (liftRead c)))))
    (U : Set (HwReg X Z (Finset S × M)))
    (σ : Matrix ((recHwSpec X Z S M).In (.inl (.inl (.inr (liftRead c)))) ×
      HwReg X Z (Finset S × M)) ((recHwSpec X Z S M).In (.inl (.inl (.inr (liftRead c)))) ×
      HwReg X Z (Finset S × M)) ℂ)
    (hσ : QuerySupportedOn (fun p : (recHwSpec X Z S M).In (.inl (.inl (.inr (liftRead c)))) ×
      HwReg X Z (Finset S × M) ↦ p.2) U σ) :
    QuerySupportedOn (fun p : (recHwSpec X Z S M).Out (.inl (.inl (.inr (liftRead c)))) ×
      HwReg X Z (Finset S × M) ↦ p.2) {s | s ∈ U ∧ r = liftAns s c}
      (((decR m₀).step (.inl (.inl (.inr (liftRead c))))).branch r σ) := by
  rw [decR_branch_apply m₀ (.inl (.inl (.inr (liftRead c)))) r _
    (runtime2_branch m₀ (.inl (.inr (liftRead c))) r)]
  refine QuerySupportedOn.conj hσ fun m' m hK hm ↦ ?_
  cases c with
  | readH z upd =>
    change upd = keepMem at hc
    subst hc
    obtain ⟨hp, hφ, hR⟩ := clsKraus_dec_ne_zero _ _ _ hK
    rw [show (cellRead m.2.2.1.1 z r.1 ⊗ₖ (1 : Matrix (Database X Z × Database X Z)
      (Database X Z × Database X Z) ℂ)) = cellRead m.2.2.1.1 z r.1 ⊗ₖ
        ((1 : Matrix (Database X Z) (Database X Z) ℂ) ⊗ₖ 1) by rw [one_kronecker_one]] at hR
    obtain ⟨h₁, h₂, h₃⟩ := dbs_dec_ne_zero hR
    obtain ⟨e₁, hr⟩ := cellRead_dec_ne_zero h₁
    have hD : m'.2.1 = m.2.1 := Prod.ext e₁ (Prod.ext (one_dec_ne_zero h₂) (one_dec_ne_zero h₃))
    have hb : m'.2.2 = m.2.2 := hφ.trans (Prod.ext rfl hp.symm)
    have hm' : m'.2 = m.2 := Prod.ext hD hb
    refine ⟨hm' ▸ hm, ?_⟩
    rw [hm']
    exact Prod.ext hr.symm hp.symm
  | readK x upd =>
    change upd = keepMem at hc
    subst hc
    obtain ⟨hp, hφ, hR⟩ := clsKraus_dec_ne_zero _ _ _ hK
    obtain ⟨h₁, h₂, h₃⟩ := dbs_dec_ne_zero hR
    obtain ⟨e₂, hr⟩ := cellRead_dec_ne_zero h₂
    have hD : m'.2.1 = m.2.1 := Prod.ext (one_dec_ne_zero h₁) (Prod.ext e₂ (one_dec_ne_zero h₃))
    have hb : m'.2.2 = m.2.2 := hφ.trans (Prod.ext rfl hp.symm)
    have hm' : m'.2 = m.2 := Prod.ext hD hb
    refine ⟨hm' ▸ hm, ?_⟩
    rw [hm']
    exact Prod.ext hr.symm hp.symm
  | readK' x upd =>
    change upd = keepMem at hc
    subst hc
    obtain ⟨hp, hφ, hR⟩ := clsKraus_dec_ne_zero _ _ _ hK
    obtain ⟨h₁, h₂, h₃⟩ := dbs_dec_ne_zero hR
    obtain ⟨e₃, hr⟩ := cellRead_dec_ne_zero h₃
    have hD : m'.2.1 = m.2.1 := Prod.ext (one_dec_ne_zero h₁) (Prod.ext (one_dec_ne_zero h₂) e₃)
    have hb : m'.2.2 = m.2.2 := hφ.trans (Prod.ext rfl hp.symm)
    have hm' : m'.2 = m.2 := Prod.ext hD hb
    refine ⟨hm' ▸ hm, ?_⟩
    rw [hm']
    exact Prod.ext hr.symm hp.symm

end decRead

/-! ## Read programs in the decompressed basis -/

section suppTo

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  [AddCommGroup X] [AddCommGroup Z] [Nonempty X] [Nonempty Z]
  {S : Type} [Fintype S] [DecidableEq S] {D : S → Type} [∀ s, Fintype (D s)]
  [∀ s, DecidableEq (D s)] {M : Type} [Fintype M] [DecidableEq M]
  (m₀ : Finset S × M) (v : (s : S) → D s) (good : LazyProg X Z S D → Prop)

omit [AddCommGroup X] [AddCommGroup Z] [Nonempty X] [Nonempty Z] [Fintype S] [DecidableEq S]
  [∀ s, Fintype (D s)] [∀ s, DecidableEq (D s)] [Fintype M] [DecidableEq M] in
/-- A read, lifted to the template and realized: the lifted read port, the relabelling back, and
the result read back. -/
theorem realizeT_readLift_readCall (c : HwRead X Z M) (B : QReg) :
    realizeT (M := M) v (readLiftQ good (readCall c B)) =
      QuantumComp₂.queryBind (L := LocalSig.instruments) (spec := recHwSpec X Z S M)
        (.inl (.inl (.inr (liftRead c)))) B (Equiv.uniqueProd B Unit).symm fun r ↦
          (QComp.act (A := QReg.of ((recHwSpec X Z S M).Out (.inl (.inl (.inr (liftRead c)))) ×
            B)) (B := B) (SubInstrument.relabel (Equiv.uniqueProd B Unit))).bind fun _ ↦
              QuantumComp₂.pure (lowerRes c r) := by
  cases c <;> rfl

/-- **A read program answers as a function of the decompressed register**: run lifted, realized
and in the decompressed basis, from any operator supported on registers in `U`, its branch at `a`
is supported on the registers of `U` (unchanged: the reads keep the register) whose answer is
`a`. -/
def SuppTo {B : QReg} {α : Type} (y : QComp (hwReadSpec X Z M) B B α)
    (a₀ : HwReg X Z (Finset S × M) → α) : Prop :=
  ∀ (U : Set (HwReg X Z (Finset S × M)))
    (σ : Matrix (B × HwReg X Z (Finset S × M)) (B × HwReg X Z (Finset S × M)) ℂ),
    QuerySupportedOn (fun p : B × HwReg X Z (Finset S × M) ↦ p.2) U σ → ∀ a,
      QuerySupportedOn (fun p : B × HwReg X Z (Finset S × M) ↦ p.2) {s | s ∈ U ∧ a = a₀ s}
        (((decR m₀).run₂ .instruments (realizeT v (readLiftQ good y))).branch a σ)

variable {m₀ v good}

omit [∀ s, Fintype (D s)] [∀ s, DecidableEq (D s)] in
theorem SuppTo.congr {B : QReg} {α : Type} {y : QComp (hwReadSpec X Z M) B B α}
    {a₀ a₁ : HwReg X Z (Finset S × M) → α} (h : SuppTo m₀ v good y a₀) (e : ∀ s, a₀ s = a₁ s) :
    SuppTo m₀ v good y a₁ := by
  rwa [← funext e]

omit [∀ s, Fintype (D s)] [∀ s, DecidableEq (D s)] in
theorem suppTo_pure {B : QReg} {α : Type} (a₀ : α) :
    SuppTo m₀ v good (QuantumComp₂.pure a₀ : QComp (hwReadSpec X Z M) B B α) fun _ ↦ a₀ := by
  intro U σ hσ a
  change QuerySupportedOn _ _ (((decR m₀).run₂ .instruments
    (QuantumComp₂.pure a₀ : QComp (recHwSpec X Z S M) B B α)).branch a σ)
  rw [QuantumRuntime.run₂_pure]
  by_cases ha : a = a₀
  · subst ha
    rw [SubInstrument.branch_pure_self]
    exact hσ.mono fun s hs ↦ ⟨hs, rfl⟩
  · rw [SubInstrument.branch_pure_of_ne ha]
    exact querySupportedOn_zero _ _

omit [∀ s, Fintype (D s)] [∀ s, DecidableEq (D s)] in
theorem SuppTo.bind {B : QReg} {α β : Type} {x : QComp (hwReadSpec X Z M) B B α}
    {a₀ : HwReg X Z (Finset S × M) → α} (hx : SuppTo m₀ v good x a₀)
    {k : α → QComp (hwReadSpec X Z M) B B β} {b₀ : α → HwReg X Z (Finset S × M) → β}
    (hk : ∀ a, SuppTo m₀ v good (k a) (b₀ a)) :
    SuppTo m₀ v good (x.bind k) fun s ↦ b₀ (a₀ s) s := by
  intro U σ hσ b
  rw [readLift_bind₂, realizeT_bind₂]
  erw [QuantumRuntime.run₂_bind, DSubInstrument.branch_bind_apply]
  refine QuerySupportedOn.tsum fun a ↦ ((hk a) _ _ (hx U σ hσ a) b).mono ?_
  rintro s ⟨⟨hU, ha⟩, hb⟩
  exact ⟨hU, by rw [hb, ha]⟩

omit [∀ s, Fintype (D s)] [∀ s, DecidableEq (D s)] in
theorem SuppTo.map {B : QReg} {α β : Type} {x : QComp (hwReadSpec X Z M) B B α}
    {a₀ : HwReg X Z (Finset S × M) → α} (hx : SuppTo m₀ v good x a₀) (f : α → β) :
    SuppTo m₀ v good (x.map f) fun s ↦ f (a₀ s) := by
  rw [QuantumComp₂.map_eq_bind_pure]
  exact hx.bind fun a ↦ suppTo_pure (f a)

omit [∀ s, Fintype (D s)] [∀ s, DecidableEq (D s)] in
/-- **A read that keeps the memory answers the view's cell.** -/
theorem suppTo_readCall (c : HwRead X Z M) (hc : c.KeepsMem) (B : QReg) :
    SuppTo m₀ v good (readCall c B) fun s ↦ viewAns s c := by
  intro U σ hσ a
  rw [realizeT_readLift_readCall]
  erw [QuantumRuntime.run₂_queryBind, DSubInstrument.branch_bind_apply]
  refine QuerySupportedOn.tsum fun r ↦ ?_
  have hq := querySupportedOn_queryStep_imp (decR m₀) (.inl (.inl (.inr (liftRead c)))) B
    (Equiv.uniqueProd B Unit).symm r U {s | s ∈ U ∧ r = liftAns s c}
    (fun τ hτ ↦ decR_read_supp m₀ c hc r U τ hτ) hσ
  rw [QuantumRuntime.run₂_act_bind]
  erw [DSubInstrument.branch_bind_apply]
  refine QuerySupportedOn.tsum fun u ↦ ?_
  rw [QuantumRuntime.run₂_pure]
  by_cases ha : a = lowerRes c r
  · subst ha
    rw [SubInstrument.branch_pure_self, LinearMap.id_apply, DSubInstrument.branch_frame_apply]
    refine (QuerySupportedOn.amplify_snd (q := fun s : HwReg X Z (Finset S × M) ↦ s) hq _).mono ?_
    rintro s ⟨hU, hr⟩
    exact ⟨hU, by rw [hr, lowerRes_liftAns]⟩
  · rw [SubInstrument.branch_pure_of_ne ha]
    exact querySupportedOn_zero _ _

/-- The functions a register answers: its view, `0` at the empty cells. -/
def regFns (s : HwReg X Z (Finset S × M)) : (Z → X) × (X → Z) × (X → Z) :=
  (union s.2.1 s.1).fill

variable (m₀ v good) in
/-- **A stateful read program answers as a function of the decompressed register** (`SuppTo` at
every starting log). -/
def SuppToS {B : QReg} {α : Type}
    (x : StateT (List (SpongeRead X Z)) (QComp (hwReadSpec X Z M) B B) α)
    (y : HwReg X Z (Finset S × M) → StateM (List (SpongeRead X Z)) α) : Prop :=
  ∀ l, SuppTo m₀ v good (x.run l) fun s ↦ (y s).run l

omit [∀ s, Fintype (D s)] [∀ s, DecidableEq (D s)] in
theorem SuppToS.congr {B : QReg} {α : Type}
    {x : StateT (List (SpongeRead X Z)) (QComp (hwReadSpec X Z M) B B) α}
    {y y' : HwReg X Z (Finset S × M) → StateM (List (SpongeRead X Z)) α}
    (h : SuppToS m₀ v good x y) (e : ∀ s, y s = y' s) : SuppToS m₀ v good x y' := by
  rwa [← funext e]

omit [∀ s, Fintype (D s)] [∀ s, DecidableEq (D s)] in
theorem suppToS_pure {B : QReg} {α : Type} (a : α) :
    SuppToS m₀ v good
      (pure a : StateT (List (SpongeRead X Z)) (QComp (hwReadSpec X Z M) B B) α)
      fun _ ↦ pure a :=
  fun l ↦ suppTo_pure (a, l)

omit [∀ s, Fintype (D s)] [∀ s, DecidableEq (D s)] in
theorem SuppToS.bind {B : QReg} {α β : Type}
    {x : StateT (List (SpongeRead X Z)) (QComp (hwReadSpec X Z M) B B) α}
    {y : HwReg X Z (Finset S × M) → StateM (List (SpongeRead X Z)) α}
    {f : α → StateT (List (SpongeRead X Z)) (QComp (hwReadSpec X Z M) B B) β}
    {g : α → HwReg X Z (Finset S × M) → StateM (List (SpongeRead X Z)) β}
    (hx : SuppToS m₀ v good x y) (hf : ∀ a, SuppToS m₀ v good (f a) (g a)) :
    SuppToS m₀ v good (x >>= f) fun s ↦ y s >>= fun a ↦ g a s := by
  intro l
  rw [StateT.run_bind]
  exact (hx l).bind fun p ↦ hf p.1 p.2

omit [∀ s, Fintype (D s)] [∀ s, DecidableEq (D s)] in
theorem SuppToS.map {B : QReg} {α β : Type}
    {x : StateT (List (SpongeRead X Z)) (QComp (hwReadSpec X Z M) B B) α}
    {y : HwReg X Z (Finset S × M) → StateM (List (SpongeRead X Z)) α}
    (hx : SuppToS m₀ v good x y) (f : α → β) :
    SuppToS m₀ v good (f <$> x) fun s ↦ f <$> y s := by
  rw [map_eq_bind_pure_comp]
  exact (hx.bind fun a ↦ suppToS_pure (f a)).congr fun s ↦ (map_eq_bind_pure_comp _ f (y s)).symm

omit [∀ s, Fintype (D s)] [∀ s, DecidableEq (D s)] in
/-- A read followed by a function of its result. -/
theorem suppTo_readCall_pure {α : Type} (c : HwRead X Z M) (hc : c.KeepsMem) (B : QReg)
    (f : c.Result → α) :
    SuppTo m₀ v good ((readCall c B).bind fun r ↦ QuantumComp₂.pure (f r)) fun s ↦
      f (viewAns s c) :=
  (suppTo_readCall c hc B).bind fun r ↦ suppTo_pure (f r)

omit [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [Nonempty X] [Nonempty Z]
  [Fintype S] [DecidableEq S] [∀ s, Fintype (D s)] [∀ s, DecidableEq (D s)] [Fintype M]
  [DecidableEq M] in
theorem run_readH_regFns (z : Z) (l : List (SpongeRead X Z)) (s : HwReg X Z (Finset S × M)) :
    (readH (regFns s).1 z).run l =
      (((viewAns s (.readH z (keepMem (M := M)))).1.getD 0 : X),
        l ++ [.h z ((viewAns s (.readH z (keepMem (M := M)))).1.getD 0)]) := rfl

omit [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [Nonempty X] [Nonempty Z]
  [Fintype S] [DecidableEq S] [∀ s, Fintype (D s)] [∀ s, DecidableEq (D s)] [Fintype M]
  [DecidableEq M] in
theorem run_readK_regFns (x : X) (l : List (SpongeRead X Z)) (s : HwReg X Z (Finset S × M)) :
    (readK (regFns s).2.1 x).run l =
      (((viewAns s (.readK x (keepMem (M := M)))).1.getD 0 : Z),
        l ++ [.k x ((viewAns s (.readK x (keepMem (M := M)))).1.getD 0)]) := rfl

omit [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [Nonempty X] [Nonempty Z]
  [Fintype S] [DecidableEq S] [∀ s, Fintype (D s)] [∀ s, DecidableEq (D s)] [Fintype M]
  [DecidableEq M] in
theorem run_readK'_regFns (x : X) (l : List (SpongeRead X Z)) (s : HwReg X Z (Finset S × M)) :
    (readK' (regFns s).2.2 x).run l =
      (((viewAns s (.readK' x (keepMem (M := M)))).1.getD 0 : Z),
        l ++ [.k' x ((viewAns s (.readK' x (keepMem (M := M)))).1.getD 0)]) := rfl

omit [∀ s, Fintype (D s)] [∀ s, DecidableEq (D s)] in
theorem suppTo_rdH (B : QReg) (z : Z) (l : List (SpongeRead X Z)) :
    SuppTo m₀ v good ((readCall (.readH z keepMem) B).bind
      fun r : Option X × M ↦ QuantumComp₂.pure (r.1.getD 0, l ++ [.h z (r.1.getD 0)]))
      fun s ↦ (readH (regFns s).1 z).run l := by
  have h0 :=
    suppTo_readCall_pure (m₀ := m₀) (v := v) (good := good) (.readH z keepMem) rfl B
      (fun r : Option X × M ↦ (r.1.getD 0, l ++ [.h z (r.1.getD 0)]))
  have h : SuppTo m₀ v good ((readCall (.readH z keepMem) B).bind
      fun r : Option X × M ↦ QuantumComp₂.pure (r.1.getD 0, l ++ [.h z (r.1.getD 0)]))
      fun s ↦ (((viewAns s (.readH z (keepMem (M := M)))).1.getD 0 : X),
        l ++ [.h z ((viewAns s (.readH z (keepMem (M := M)))).1.getD 0)]) := h0
  exact SuppTo.congr h fun s ↦ (run_readH_regFns z l s).symm

omit [∀ s, Fintype (D s)] [∀ s, DecidableEq (D s)] in
theorem suppToS_rdH (B : QReg) (z : Z) :
    SuppToS m₀ v good (rdH (M := M) B z) fun s ↦ readH (regFns s).1 z :=
  fun l ↦ suppTo_rdH B z l

omit [∀ s, Fintype (D s)] [∀ s, DecidableEq (D s)] in
theorem suppTo_rdK (B : QReg) (x : X) (l : List (SpongeRead X Z)) :
    SuppTo m₀ v good ((readCall (.readK x keepMem) B).bind
      fun r : Option Z × M ↦ QuantumComp₂.pure (r.1.getD 0, l ++ [.k x (r.1.getD 0)]))
      fun s ↦ (readK (regFns s).2.1 x).run l := by
  have h0 :=
    suppTo_readCall_pure (m₀ := m₀) (v := v) (good := good) (.readK x keepMem) rfl B
      (fun r : Option Z × M ↦ (r.1.getD 0, l ++ [.k x (r.1.getD 0)]))
  have h : SuppTo m₀ v good ((readCall (.readK x keepMem) B).bind
      fun r : Option Z × M ↦ QuantumComp₂.pure (r.1.getD 0, l ++ [.k x (r.1.getD 0)]))
      fun s ↦ (((viewAns s (.readK x (keepMem (M := M)))).1.getD 0 : Z),
        l ++ [.k x ((viewAns s (.readK x (keepMem (M := M)))).1.getD 0)]) := h0
  exact SuppTo.congr h fun s ↦ (run_readK_regFns x l s).symm

omit [∀ s, Fintype (D s)] [∀ s, DecidableEq (D s)] in
theorem suppToS_rdK (B : QReg) (x : X) :
    SuppToS m₀ v good (rdK (M := M) B x) fun s ↦ readK (regFns s).2.1 x :=
  fun l ↦ suppTo_rdK B x l

omit [∀ s, Fintype (D s)] [∀ s, DecidableEq (D s)] in
theorem suppTo_rdK' (B : QReg) (x : X) (l : List (SpongeRead X Z)) :
    SuppTo m₀ v good ((readCall (.readK' x keepMem) B).bind
      fun r : Option Z × M ↦ QuantumComp₂.pure (r.1.getD 0, l ++ [.k' x (r.1.getD 0)]))
      fun s ↦ (readK' (regFns s).2.2 x).run l := by
  have h0 :=
    suppTo_readCall_pure (m₀ := m₀) (v := v) (good := good) (.readK' x keepMem) rfl B
      (fun r : Option Z × M ↦ (r.1.getD 0, l ++ [.k' x (r.1.getD 0)]))
  have h : SuppTo m₀ v good ((readCall (.readK' x keepMem) B).bind
      fun r : Option Z × M ↦ QuantumComp₂.pure (r.1.getD 0, l ++ [.k' x (r.1.getD 0)]))
      fun s ↦ (((viewAns s (.readK' x (keepMem (M := M)))).1.getD 0 : Z),
        l ++ [.k' x ((viewAns s (.readK' x (keepMem (M := M)))).1.getD 0)]) := h0
  exact SuppTo.congr h fun s ↦ (run_readK'_regFns x l s).symm

omit [∀ s, Fintype (D s)] [∀ s, DecidableEq (D s)] in
theorem suppToS_rdK' (B : QReg) (x : X) :
    SuppToS m₀ v good (rdK' (M := M) B x) fun s ↦ readK' (regFns s).2.2 x :=
  fun l ↦ suppTo_rdK' B x l

variable (π : Equiv.Perm (X × Z))

omit [∀ s, Fintype (D s)] [∀ s, DecidableEq (D s)] in
theorem suppToS_rdRound (B : QReg) (st : X × Z) (b : X) :
    SuppToS m₀ v good (rdRound M π B st b) fun s ↦
      evalRoundM π (readH (regFns s).1) (readK (regFns s).2.1) (readK' (regFns s).2.2) st b := by
  unfold rdRound evalRoundM
  exact (suppToS_rdK _ _).bind fun _ ↦ (suppToS_rdK' _ _).bind fun _ ↦ (suppToS_rdH _ _).bind
    fun _ ↦ suppToS_pure _

omit [∀ s, Fintype (D s)] [∀ s, DecidableEq (D s)] in
theorem suppToS_foldlM (B : QReg) (msg : List X) (st : X × Z) :
    SuppToS m₀ v good (msg.foldlM (rdRound M π B) st) fun s ↦
      msg.foldlM (evalRoundM π (readH (regFns s).1) (readK (regFns s).2.1)
        (readK' (regFns s).2.2)) st := by
  induction msg generalizing st with
  | nil => exact suppToS_pure st
  | cons b msg ih =>
    rw [List.foldlM_cons]
    exact ((suppToS_rdRound π B st b).bind ih).congr fun s ↦ (List.foldlM_cons ..).symm


end suppTo

/-! ## The read program of a hash-query computation -/

section readsProgram

variable {S : Type} [Fintype S] [DecidableEq S] {D : S → Type} [∀ s, Fintype (D s)]
  [∀ s, DecidableEq (D s)] {M : Type} [Fintype M] [DecidableEq M]
  {m₀ : Finset S × M} {v : (s : S) → D s} {good : LazyProg X Z S D → Prop}
  (π : Equiv.Perm (X × Z))

omit [∀ s, Fintype (D s)] [∀ s, DecidableEq (D s)] in
theorem suppToS_readsImpl (B : QReg) (input : HashInput) :
    SuppToS m₀ v good (readsImpl M π B input) fun s ↦ readHash (regFns s) π input :=
  ((suppToS_foldlM π B (blocks input) (0, 0)).map fun st ↦ st.1).map out256

omit [∀ s, Fintype (D s)] [∀ s, DecidableEq (D s)] in
theorem suppToS_simulateQ (B : QReg) {α : Type} (x : OracleComp LeanXmss.HashSpec α) :
    SuppToS m₀ v good (simulateQ (readsImpl M π B) x) fun s ↦
      simulateQ (readHash (regFns s) π) x := by
  induction x using OracleComp.inductionOn with
  | pure a =>
    rw [simulateQ_pure]
    exact (suppToS_pure a).congr fun s ↦ (simulateQ_pure _ a).symm
  | query_bind input k ih =>
    rw [simulateQ_bind, simulateQ_spec_query]
    refine ((suppToS_readsImpl π B input).bind ih).congr fun s ↦ ?_
    rw [simulateQ_bind, simulateQ_spec_query]

omit [∀ s, Fintype (D s)] [∀ s, DecidableEq (D s)] in
/-- **The read program of a hash-query computation answers its honest evaluation** against the
functions of the decompressed register. -/
theorem suppTo_readsProgram (B : QReg) {α : Type} (x : OracleComp LeanXmss.HashSpec α) :
    SuppTo m₀ v good (readsProgram M π B x) fun s ↦ honestEval (regFns s) π x :=
  suppToS_simulateQ π B x []

end readsProgram

/-! ## Read logs, held reads, and supports through the decompression -/

section logs

variable {X Z : Type}

/-- A read as a log entry with its answer (the inverse of `toSpongeRead`). -/
def ofSpongeRead : SpongeRead X Z → (q : SpongeQuery X Z) × spongeOSpec X Z q
  | .h z a => ⟨.h z, a⟩
  | .k x a => ⟨.k x, a⟩
  | .k' x a => ⟨.k' x, a⟩

theorem toSpongeRead_ofSpongeRead (e : SpongeRead X Z) : toSpongeRead (ofSpongeRead e) = e := by
  cases e <;> rfl

theorem map_toSpongeRead_ofSpongeRead (l : List (SpongeRead X Z)) :
    (l.map ofSpongeRead).map toSpongeRead = l := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id l]
  exact List.map_congr_left fun e _ ↦ toSpongeRead_ofSpongeRead e

theorem readCount_map_ofSpongeRead (p : SpongePort) (l : List (SpongeRead X Z)) :
    readCount p (l.map ofSpongeRead) = l.countP fun e ↦ decide (e.port = p) := by
  rw [readCount, List.countP_map]
  refine List.countP_congr fun e _ ↦ ?_
  cases e <;> exact Iff.rfl

theorem eq_some_of_getD {α : Type} [Zero α] {o : Option α} (hs : o.isSome) {a : α}
    (h : o.getD 0 = a) : o = some a := by
  cases o with
  | none => simp at hs
  | some b =>
    simp only [Option.getD_some] at h
    rw [h]

theorem or_isSome {α : Type} (o : Option α) {o' : Option α} (h : o'.isSome) :
    (o.or o').isSome := by
  cases o <;> simp [h]

end logs

section heldConcrete

theorem answeredBy_fill {U : Dbs X Z} {e : SpongeRead X Z} (h : e.HeldBy U) :
    e.AnsweredBy U.fill := by
  cases e with
  | h z a => exact Dbs.fill_h h
  | k x a => exact Dbs.fill_k h
  | k' x a => exact Dbs.fill_k' h

/-- **On databases with no empty cell, a read answered by the view's functions is held by the
view.** -/
theorem heldBy_hwView_of_noBot {W : Hw X Z} {D : DbReg X Z} (hD : NoBotDb D)
    {e : SpongeRead X Z} (h : e.AnsweredBy (union W D).fill) : e.HeldBy (hwView W D).toDbs := by
  cases e with
  | h z a => exact eq_some_of_getD (or_isSome _ (hD.1 z)) h
  | k x a => exact eq_some_of_getD (or_isSome _ (hD.2.1 x)) h
  | k' x a => exact eq_some_of_getD (or_isSome _ (hD.2.2 x)) h

end heldConcrete

section transfer

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  [AddCommGroup X] [AddCommGroup Z] [Nonempty X] [Nonempty Z]
  {M' : Type} [Fintype M'] [DecidableEq M']

omit [AddCommGroup X] [AddCommGroup Z] [Nonempty X] [Nonempty Z] in
theorem querySupportedOn_inter {α β : Type*} {q : α → β} {S T : Set β} {σ : Matrix α α ℂ}
    (h₁ : QuerySupportedOn q S σ) (h₂ : QuerySupportedOn q T σ) :
    QuerySupportedOn q (S ∩ T) σ :=
  fun m m' h ↦ ⟨⟨(h₁ m m' h).1, (h₂ m m' h).1⟩, ⟨(h₁ m m' h).2, (h₂ m m' h).2⟩⟩

omit [AddCommGroup X] [AddCommGroup Z] [Nonempty X] [Nonempty Z] in
/-- **The decompression keeps the classical part**: a support condition on the hardwired cells and
the memory passes through the conjugation by the decompression. -/
theorem querySupportedOn_conj_compressReg {P : Hw X Z × M' → Prop}
    {σ : Matrix (Unit × HwReg X Z M') (Unit × HwReg X Z M') ℂ}
    (h : QuerySupportedOn (fun p : Unit × HwReg X Z M' ↦ p.2) {s | P s.2} σ) :
    QuerySupportedOn (fun p : Unit × HwReg X Z M' ↦ p.2) {s | P s.2}
      (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg X Z M') σ) :=
  QuerySupportedOn.conj h fun m' m hK hm ↦ by
    have h' := (one_kronecker_ne_zero (a := m.1) (a' := m'.1) (b := m.2) (b' := m'.2) hK).2
    rw [compressReg, kroneckerMap_apply] at h'
    have h₂ := right_ne_zero_of_mul h'
    rw [Matrix.one_apply] at h₂
    split_ifs at h₂ with he
    · show P m'.2.2
      rw [he]
      exact hm
    · exact absurd rfl h₂

omit [Nonempty X] [Nonempty Z] in
theorem conj_compressReg_conj (σ : Matrix (Unit × HwReg X Z M') (Unit × HwReg X Z M') ℂ) :
    MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg X Z M')
      (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg X Z M') σ) = σ := by
  rw [← LinearMap.comp_apply, ← MatrixMap.conj_mul, ← mul_kronecker_mul, Matrix.one_mul,
    compressReg_mul_self, one_kronecker_one, MatrixMap.conj_one]
  rfl

omit [AddCommGroup X] [AddCommGroup Z] [Nonempty X] [Nonempty Z] in
/-- A support condition on the classical part of the decompressed form holds for the operator. -/
theorem querySupportedOn_of_conj_compressReg [AddCommGroup X] [AddCommGroup Z]
    {P : Hw X Z × M' → Prop}
    {σ : Matrix (Unit × HwReg X Z M') (Unit × HwReg X Z M') ℂ}
    (h : QuerySupportedOn (fun p : Unit × HwReg X Z M' ↦ p.2) {s | P s.2}
      (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg X Z M') σ)) :
    QuerySupportedOn (fun p : Unit × HwReg X Z M' ↦ p.2) {s | P s.2} σ := by
  have h' := querySupportedOn_conj_compressReg h
  rwa [conj_compressReg_conj] at h'

end transfer

/-! ## Traces along a sequence -/

/-- **The weight of a branch of a sequence**, through any Kraus operator `K`, is the sum over the
first outcomes of the weights of the continuations. -/
theorem ofReal_trace_conj_bind_branch {A : Type*} [Fintype A] {ι κ : Type*} {B : ι → Type*}
    [∀ i, Fintype (B i)] {C : κ → Type*} [∀ c, Fintype (C c)] (p : DSubInstrument A ι B)
    (k : (i : ι) → DSubInstrument (B i) κ C) (c : κ) (K : Matrix (C c) (C c) ℂ)
    {ρ : Matrix A A ℂ} (hρ : ρ.PosSemidef) :
    ENNReal.ofReal (MatrixMap.conj K ((p.bind k).branch c ρ)).trace.re =
      ∑' i, ENNReal.ofReal (MatrixMap.conj K ((k i).branch c (p.branch i ρ))).trace.re := by
  have hs : Summable fun i ↦ (k i).branch c (p.branch i ρ) :=
    (p.isCPTNIFamily.comp_eval (fun i ↦ (k i).isCPTNIFamily) c).summable_apply ρ
  rw [DSubInstrument.branch_bind_apply, MatrixMap.map_tsum _ hs]
  refine ofReal_trace_re_tsum (MatrixMap.summable_comp _ hs) fun i ↦ ?_
  rw [MatrixMap.conj_apply]
  exact ((k i).posSemidef_branch_apply c (p.posSemidef_branch_apply i hρ)).mul_mul_conjTranspose_same K

/-- `ofReal_trace_conj_bind_branch` for subinstruments with constant output systems. -/
theorem ofReal_trace_conj_bind_branch₂ {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    {α β : Type*} (p : SubInstrument A B α) (k : α → SubInstrument B C β) (c : β)
    (K : Matrix C C ℂ) {ρ : Matrix A A ℂ} (hρ : ρ.PosSemidef) :
    ENNReal.ofReal (MatrixMap.conj K ((p.bind k).branch c ρ)).trace.re =
      ∑' a, ENNReal.ofReal (MatrixMap.conj K ((k a).branch c (p.branch a ρ))).trace.re :=
  ofReal_trace_conj_bind_branch p k c K hρ

/-! ## Runs of runtime 2 with record ports on the trivial register -/

section bridge

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  [AddCommGroup X] [AddCommGroup Z] [Nonempty X] [Nonempty Z]
  {S M' : Type} [Fintype S] [DecidableEq S] [Fintype M'] [DecidableEq M'] (m₀ : Finset S × M')

/-- The initial state of runtime 2 with record ports beside the trivial register. -/
noncomputable def initU :
    Matrix (Unit × HwReg X Z (Finset S × M')) (Unit × HwReg X Z (Finset S × M')) ℂ :=
  (SubState.basis ()).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix

theorem initU_posSemidef : (initU (X := X) (Z := Z) m₀).PosSemidef :=
  ((SubState.basis ()).prod (runtimeR (X := X) (Z := Z) m₀).init).posSemidef

omit [AddCommGroup X] [AddCommGroup Z] [Nonempty X] [Nonempty Z] in
/-- The hardwired cells keep their grade through a record port. -/
theorem gradeSupp_recStep (T : Finset S) (r : Finset S × M') (n : ℕ)
    (σ : Matrix (Unit × HwReg X Z (Finset S × M')) (Unit × HwReg X Z (Finset S × M')) ℂ)
    (hσ : QuerySupportedOn (fun q : Unit × HwReg X Z (Finset S × M') ↦ dbGrade q.2.2.1)
      (Set.Iic n) σ) :
    QuerySupportedOn (fun q : Unit × HwReg X Z (Finset S × M') ↦ dbGrade q.2.2.1)
      (Set.Iic n) ((recStep (X := X) (Z := Z) T).branch r σ) := by
  rw [recStep_branch]
  exact querySupportedOn_conj_of_hw_eq (fun _ _ _ _ h ↦ by rw [eq_of_recKraus_ne_zero h]) hσ

/-- The win weight of a Boolean program is the weight of its final branch at `true`. -/
theorem evalDistMap_winBit (x : QComp (recHwSpec X Z S M') (QReg.of Unit) (QReg.of Unit) Bool) :
    (runtimeR m₀).evalDistMap .instruments x (SubState.basis ()) winBit {true} =
      ENNReal.ofReal (((runtimeR m₀).run₂ .instruments x).branch true (initU m₀)).trace.re := by
  refine (QuantumRuntime.evalDistMap_apply _ _ _ _ _ (measurableSet_singleton true)).trans ?_
  rw [← (QuantumComp₂.leafEquiv (QReg.of Unit) Bool).tsum_eq, tsum_bool]
  simp [winBit, Set.indicator]
  rfl

/-- The event weight of a Boolean program is at least the weight of the event on its final
branch at `true`. -/
theorem trace_conj_branch_true_le_eventWeight
    (x : QComp (recHwSpec X Z S M') (QReg.of Unit) (QReg.of Unit) Bool)
    (Bad : Set (HwReg X Z (Finset S × M'))) [DecidablePred (· ∈ Bad)] :
    ENNReal.ofReal (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ hwProjector Bad)
      (((runtimeR m₀).run₂ .instruments x).branch true (initU m₀))).trace.re ≤
      (runtimeR m₀).eventWeight .instruments (hwProjector Bad) x (initU m₀) := by
  unfold QuantumRuntime.eventWeight
  refine le_trans (le_of_eq ?_) (ENNReal.le_tsum (QuantumComp₂.leafEquiv (QReg.of Unit) Bool true))
  rfl

/-- **No empty decompressed cell** (`noBot_runtimeR`) for a program on the trivial register. -/
theorem noBot_branch₂ {α : Type}
    (x : QComp (recHwSpec X Z S M') (QReg.of Unit) (QReg.of Unit) α) (a : α) :
    QuerySupportedOn (fun p : Unit × HwReg X Z (Finset S × M') ↦ p.2) {s | NoBot s}
      (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg X Z (Finset S × M'))
        (((runtimeR m₀).run₂ .instruments x).branch a (initU m₀))) :=
  noBot_runtimeR m₀ .instruments x (SubState.basis ()).matrix ⟨QReg.of Unit, rfl, a⟩

/-- **At most `progCap` hardwired cells** at the end of a program on the trivial register with at
most `progCap` program calls (`dbGrade_le_progCap_extend`). -/
theorem grade_branch₂ {α : Type}
    {x : QComp (recHwSpec X Z S M') (QReg.of Unit) (QReg.of Unit) α}
    (hx : IPFunctor.IFreeM.IsChargeBound x (portCharge (L := LocalSig.instruments.{0})
      (extProgCharge X Z (Finset S × M') (recSpec S M'))) progCap) (a : α) :
    QuerySupportedOn (fun p : Unit × HwReg X Z (Finset S × M') ↦ p.2)
      {s | dbGrade s.2.1 ≤ progCap} (((runtimeR m₀).run₂ .instruments x).branch a (initU m₀)) :=
  QuerySupportedOn.imp (q' := fun p : Unit × HwReg X Z (Finset S × M') ↦ p.2)
    (S' := {s | dbGrade s.2.1 ≤ progCap})
    (dbGrade_le_progCap_extend m₀ (recStep (X := X) (Z := Z) (S := S) (M := M'))
      (fun T r n σ hσ ↦ gradeSupp_recStep T r n σ hσ) .instruments hx le_rfl (SubState.basis ())
      ⟨QReg.of Unit, rfl, a⟩) fun _ h ↦ h

/-- **A run in the decompressed basis** (`run_conjReg`) for a program on the trivial
register. -/
theorem conj_branch₂ {α : Type}
    (x : QComp (recHwSpec X Z S M') (QReg.of Unit) (QReg.of Unit) α) (a : α)
    (ρ : Matrix (Unit × HwReg X Z (Finset S × M')) (Unit × HwReg X Z (Finset S × M')) ℂ) :
    MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg X Z (Finset S × M'))
        (((runtimeR m₀).run₂ .instruments x).branch a ρ) =
      ((decR m₀).run₂ .instruments x).branch a
        (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg X Z (Finset S × M')) ρ) :=
  (run_conjReg (runtimeRH m₀) (compressReg X Z (Finset S × M')) compressReg_mul_self
    conjTranspose_compressReg .instruments x ⟨QReg.of Unit, rfl, a⟩ ρ).symm

variable {α β : Type} (x : QComp (recHwSpec X Z S M') (QReg.of Unit) (QReg.of Unit) α)
  (y : α → QComp (recHwSpec X Z S M') (QReg.of Unit) (QReg.of Unit) β) (f : α → β → Bool)

/-- **A run of `x`, then `y`, with the condition `f`**: the branch of `y p.1` at `p.2` after the
branch of `x` at `p.1`, when `f p.1 p.2`; `0` otherwise. -/
noncomputable def runSig (p : α × β) :
    Matrix (Unit × HwReg X Z (Finset S × M')) (Unit × HwReg X Z (Finset S × M')) ℂ :=
  if f p.1 p.2 = true then
    ((runtimeR m₀).run₂ .instruments (y p.1)).branch p.2
      (((runtimeR m₀).run₂ .instruments x).branch p.1 (initU m₀))
  else 0

theorem runSig_of (p : α × β) (h : f p.1 p.2 = true) :
    runSig m₀ x y f p = ((runtimeR m₀).run₂ .instruments (y p.1)).branch p.2
      (((runtimeR m₀).run₂ .instruments x).branch p.1 (initU m₀)) :=
  ite_eq_left h

theorem runSig_of_not (p : α × β) (h : ¬f p.1 p.2 = true) : runSig m₀ x y f p = 0 :=
  ite_eq_right h

theorem runSig_posSemidef (p : α × β) : (runSig m₀ x y f p).PosSemidef := by
  by_cases h : f p.1 p.2 = true
  · rw [runSig_of m₀ x y f p h]
    exact ((runtimeR m₀).run₂ .instruments (y p.1)).posSemidef_branch_apply p.2
      (((runtimeR m₀).run₂ .instruments x).posSemidef_branch_apply p.1 (initU_posSemidef m₀))
  · rw [runSig_of_not m₀ x y f p h]
    exact Matrix.PosSemidef.zero

omit [Fintype S] [DecidableEq S] [Fintype M'] [DecidableEq M'] in
/-- `ofReal_trace_conj_bind_branch` for the runs of a sequence in runtime 2 with record ports. -/
theorem ofReal_trace_conj_run₂_bind [Fintype S] [DecidableEq S] [Fintype M'] [DecidableEq M']
    {γ δ : Type} (u : QComp (recHwSpec X Z S M') (QReg.of Unit) (QReg.of Unit) γ)
    (k : γ → QComp (recHwSpec X Z S M') (QReg.of Unit) (QReg.of Unit) δ) (c : δ)
    (K : Matrix ((QReg.of Unit) × (runtimeR (X := X) (Z := Z) m₀).D)
      ((QReg.of Unit) × (runtimeR (X := X) (Z := Z) m₀).D) ℂ)
    {ρ : Matrix ((QReg.of Unit) × (runtimeR (X := X) (Z := Z) m₀).D)
      ((QReg.of Unit) × (runtimeR (X := X) (Z := Z) m₀).D) ℂ} (hρ : ρ.PosSemidef) :
    ENNReal.ofReal (MatrixMap.conj K
      (((runtimeR m₀).run₂ .instruments (u.bind k)).branch c ρ)).trace.re =
      ∑' a, ENNReal.ofReal (MatrixMap.conj K (((runtimeR m₀).run₂ .instruments (k a)).branch c
        (((runtimeR m₀).run₂ .instruments u).branch a ρ))).trace.re := by
  rw [QuantumRuntime.run₂_bind]
  exact ofReal_trace_conj_bind_branch₂ _ _ c K hρ

/-- **The final branch at `true` splits along the runs of `x` and `y`**, through any Kraus
operator `K`. -/
theorem ofReal_trace_conj_runSig
    (K : Matrix (Unit × HwReg X Z (Finset S × M')) (Unit × HwReg X Z (Finset S × M')) ℂ) :
    ENNReal.ofReal (MatrixMap.conj K (((runtimeR m₀).run₂ .instruments
      (x.bind fun a ↦ (y a).bind fun b ↦ QuantumComp₂.pure (f a b))).branch true
        (initU m₀))).trace.re =
      ∑' p, ENNReal.ofReal (MatrixMap.conj K (runSig m₀ x y f p)).trace.re := by
  refine (ofReal_trace_conj_run₂_bind m₀ x (fun a ↦ (y a).bind fun b ↦ QuantumComp₂.pure (f a b))
    true K (initU_posSemidef m₀)).trans ?_
  rw [ENNReal.tsum_prod']
  refine tsum_congr fun a ↦ ?_
  refine (ofReal_trace_conj_run₂_bind m₀ (y a) (fun b ↦ QuantumComp₂.pure (f a b)) true K
    (((runtimeR m₀).run₂ .instruments x).posSemidef_branch_apply a (initU_posSemidef m₀))).trans ?_
  refine tsum_congr fun b ↦ ?_
  rw [QuantumRuntime.run₂_pure, branch_pure_eq_ite]
  by_cases h : f a b = true
  · rw [runSig_of m₀ x y f (a, b) h, ite_eq_left h.symm]
    rfl
  · rw [runSig_of_not m₀ x y f (a, b) h, ite_eq_right (fun h' ↦ h h'.symm)]
    have h0 : ∀ {n : Type} {_ : Fintype n}, ((0 : Matrix n n ℂ).trace).re = 0 := by
      intro n _
      simp
    rw [LinearMap.zero_apply, map_zero, map_zero, h0, h0]

/-- A run with the condition, in the decompressed basis (`conj_branch₂`). -/
theorem conj_runSig_of (p : α × β) (h : f p.1 p.2 = true) :
    MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg X Z (Finset S × M'))
        (runSig m₀ x y f p) =
      ((decR m₀).run₂ .instruments (y p.1)).branch p.2
        (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg X Z (Finset S × M'))
          (((runtimeR m₀).run₂ .instruments x).branch p.1 (initU m₀))) := by
  rw [runSig_of m₀ x y f p h]
  exact conj_branch₂ m₀ (y p.1) p.2 _

/-- A final branch from the initial state weighs at most `1`. -/
theorem ofReal_trace_branch_le_one {γ : Type}
    (z : QComp (recHwSpec X Z S M') (QReg.of Unit) (QReg.of Unit) γ) (c : γ) :
    ENNReal.ofReal (((runtimeR m₀).run₂ .instruments z).branch c (initU m₀)).trace.re ≤ 1 :=
  ENNReal.ofReal_le_one.mpr ((DSubInstrument.trace_re_branch_apply_le _ _
    (initU_posSemidef m₀)).trans
      ((SubState.basis ()).prod (runtimeR (X := X) (Z := Z) m₀).init).trace_re_le_one)

end bridge


/-! ## The canonical game -/

section game

/- Instance search for the memory `Finset HPos × Selections` exceeds the default size (as for
Security's `Mem`): found once here. -/
set_option synthInstance.maxSize 1000 in
instance winMemDecEq : DecidableEq (Finset HPos × Selections) := inferInstance

/-- The winning condition of a prefix outcome. -/
noncomputable def winCond (pre : PublicKey × (Forgery × SignLog)) : Bool :=
  sufCmaScheme.winningCondition pre.2.2 pre.2.1

/-- The canonical game at the table `L` (Security's `gameR`). -/
noncomputable def wGame (A : Adversary (X × Z)) (L : HonestTable) :
    QComp (recHwSpec X Z HPos Selections) (QReg.of Unit) (QReg.of Unit) Bool :=
  realizeT (valueAt L) (gameT Selections cwUpd (pubOf L) A)

/-- Its challenge prefix (Security's `prefixR`). -/
noncomputable def wPrefix (A : Adversary (X × Z)) (L : HonestTable) :
    QComp (recHwSpec X Z HPos Selections) (QReg.of Unit) (QReg.of Unit)
      (PublicKey × (Forgery × SignLog)) :=
  realizeT (valueAt L) (prefixT Selections cwUpd (pubOf L) A)

/-- The verification's read program, realized: the verification of the prefix outcome `pre`
through read ports, with its reads. -/
noncomputable def wReads (L : HonestTable) (pre : PublicKey × (Forgery × SignLog)) :
    QComp (recHwSpec X Z HPos Selections) (QReg.of Unit) (QReg.of Unit)
      (Bool × List (SpongeRead X Z)) :=
  realizeT (valueAt L) (readLiftQ goodAll
    (readsProgram Selections L.perm (QReg.of Unit) (schemeWithHashFromSeed.verify pre.1 pre.2.1)))

theorem realizeT_verifyT (L : HonestTable) (pre : PublicKey × (Forgery × SignLog)) :
    realizeT (valueAt L) (verifyT Selections (pubOf L) pre) =
      (wReads L pre).bind fun a ↦ QuantumComp₂.pure (winCond pre && a.1) := by
  rw [verifyT, QuantumComp₂.map_eq_bind_pure, readLift_bind₂, QuantumComp₂.bind_assoc,
    realizeT_bind₂]
  rfl

/-- **The game is its prefix, the verification's reads, and the winning condition.** -/
theorem wGame_eq (A : Adversary (X × Z)) (L : HonestTable) :
    wGame A L = (wPrefix A L).bind fun pre ↦
      (wReads L pre).bind fun a ↦ QuantumComp₂.pure (winCond pre && a.1) := by
  rw [wGame, gameT_eq_prefixT_bind, realizeT_bind₂]
  simp only [realizeT_verifyT]
  rfl

/-- **The facts of a winning prefix outcome** on the classical part `(W, (label, m))` of the
register: the public key is `L`'s, and some selection function `Sel` gives the transcript's
signatures, is recorded in the selections `m`, and makes the exempted slots of `W` public. -/
def PreFacts (L : HonestTable) (pre : PublicKey × (Forgery × SignLog))
    (b : Hw X Z × (Finset HPos × Selections)) : Prop :=
  pre.1 = L.publicKey ∧ ∃ Sel : SelFn, (∀ r ∈ pre.2.2, r.2 = L.selSignature Sel r.1) ∧
    (∀ r ∈ pre.2.2, b.2.2.toMemory.RecordsSel L Sel r.1) ∧
    exOf L b.1 ⊆ Public (L.selDisclosures Sel (pre.2.2.map Sigma.fst))

/-- **The prefix invariant** (open): on every branch of the challenge prefix in `runtimeR m₀` whose
outcome `pre` satisfies the winning condition, the register is supported on `PreFacts L pre`. -/
def PrefixWinFacts (m₀ : Finset HPos × Selections) (A : Adversary (X × Z)) (L : HonestTable) :
    Prop :=
  ∀ pre, winCond pre = true →
    QuerySupportedOn (fun p : Unit × HwReg X Z (Finset HPos × Selections) ↦ p.2)
      {s | PreFacts L pre s.2}
      (((runtimeR m₀).run₂ .instruments (wPrefix A L)).branch pre (initU m₀))

/-- The verification's reads of each port number at most `verifyBlocks`. -/
def CountsOK (l : List (SpongeRead X Z)) : Prop :=
  ∀ p, readCount p (l.map ofSpongeRead) ≤ verifyBlocks

/-- **The honest verification makes at most `verifyBlocks` reads of each port**: one per block. -/
theorem countsOK_honest (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (pk : PublicKey)
    (f : Forgery) : CountsOK (honestEval t π (schemeWithHashFromSeed.verify pk f)).2 := by
  intro p
  rw [readCount_map_ofSpongeRead, snd_honestEval, List.countP_flatMap]
  refine le_of_eq_of_le ?_ (sum_map_queries_le (spongeOut (spongePerm t π)) hashBlocks
    (verify_cost' pk f))
  congr 1
  refine List.map_congr_left fun inp _ ↦ ?_
  simp only [Function.comp_apply, inputReads, countP_port_spongeReads, hashBlocks_eq_length_blocks]

open scoped Classical in
/-- The log of a run of the verification's reads (empty if it exceeds the read counts). -/
noncomputable def wLog (i : (PublicKey × (Forgery × SignLog)) × (Bool × List (SpongeRead X Z))) :
    QueryLog (spongeOSpec X Z) :=
  if CountsOK i.2.2 then i.2.2.map ofSpongeRead else []

theorem wLog_of_countsOK {i : (PublicKey × (Forgery × SignLog)) × (Bool × List (SpongeRead X Z))}
    (h : CountsOK i.2.2) : wLog i = i.2.2.map ofSpongeRead := by
  classical
  unfold wLog
  rw [ite_eq_left h]

theorem readCount_wLog_le
    (i : (PublicKey × (Forgery × SignLog)) × (Bool × List (SpongeRead X Z))) (p : SpongePort) :
    readCount p (wLog i) ≤ verifyBlocks := by
  classical
  by_cases h : CountsOK i.2.2
  · rw [wLog_of_countsOK h]
    exact h p
  · unfold wLog
    rw [ite_eq_right h]
    exact Nat.zero_le _

end game

/-! ## The decomposition of the winning runs -/

section decomp

variable (m₀ : Finset HPos × Selections) (A : Adversary (X × Z)) (L : HonestTable)

/-- **The runs of the winning outcomes**: a winning prefix outcome `i.1` followed by a run `i.2` of
the verification's reads that accepts (`runSig`). -/
noncomputable def wSig (i : (PublicKey × (Forgery × SignLog)) × (Bool × List (SpongeRead X Z))) :
    Matrix (Unit × HwReg X Z (Finset HPos × Selections))
      (Unit × HwReg X Z (Finset HPos × Selections)) ℂ :=
  runSig m₀ (wPrefix A L) (wReads L) (fun pre a ↦ winCond pre && a.1) i

variable {m₀ A L}

/-- The prefix of a game with at most `progCap` program calls has at most `progCap` program
calls. -/
theorem isChargeBound_wPrefix
    (hprog : IPFunctor.IFreeM.IsChargeBound (wGame A L)
      (portCharge (L := LocalSig.instruments.{0})
        (extProgCharge X Z (Finset HPos × Selections) (recSpec HPos Selections))) progCap) :
    IPFunctor.IFreeM.IsChargeBound (wPrefix A L)
      (portCharge (L := LocalSig.instruments.{0})
        (extProgCharge X Z (Finset HPos × Selections) (recSpec HPos Selections))) progCap := by
  rw [wGame_eq] at hprog
  exact isChargeBound_of_bind₂ hprog

/-- **The prefix's branch in the decompressed basis**: no empty cell, at most `progCap`
hardwired cells, and the prefix facts. -/
theorem dec_wPre
    (hprog : IPFunctor.IFreeM.IsChargeBound (wGame A L)
      (portCharge (L := LocalSig.instruments.{0})
        (extProgCharge X Z (Finset HPos × Selections) (recSpec HPos Selections))) progCap)
    (hpre : PrefixWinFacts m₀ A L) (pre : PublicKey × (Forgery × SignLog))
    (hw : winCond pre = true) :
    QuerySupportedOn (fun p : Unit × HwReg X Z (Finset HPos × Selections) ↦ p.2)
      {s | NoBot s ∧ (dbGrade s.2.1 ≤ progCap ∧ PreFacts L pre s.2)}
      (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg X Z (Finset HPos × Selections))
        (((runtimeR m₀).run₂ .instruments (wPrefix A L)).branch pre (initU m₀))) :=
  querySupportedOn_inter (noBot_branch₂ m₀ (wPrefix A L) pre)
    (querySupportedOn_conj_compressReg (P := fun b ↦ dbGrade b.1 ≤ progCap ∧ PreFacts L pre b)
      (querySupportedOn_inter (grade_branch₂ m₀ (isChargeBound_wPrefix hprog) pre) (hpre pre hw)))

/-- **A winning run of the verification's reads in the decompressed basis**: the prefix's facts
kept, and the run's outcome the honest verification against the register's functions. -/
theorem dec_wSig
    (hprog : IPFunctor.IFreeM.IsChargeBound (wGame A L)
      (portCharge (L := LocalSig.instruments.{0})
        (extProgCharge X Z (Finset HPos × Selections) (recSpec HPos Selections))) progCap)
    (hpre : PrefixWinFacts m₀ A L)
    (i : (PublicKey × (Forgery × SignLog)) × (Bool × List (SpongeRead X Z))) :
    QuerySupportedOn (fun p : Unit × HwReg X Z (Finset HPos × Selections) ↦ p.2)
      {s | (winCond i.1 && i.2.1) = true ∧
        ((NoBot s ∧ (dbGrade s.2.1 ≤ progCap ∧ PreFacts L i.1 s.2)) ∧
          i.2 = honestEval (regFns s) L.perm (schemeWithHashFromSeed.verify i.1.1 i.1.2.1))}
      (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg X Z (Finset HPos × Selections))
        (wSig m₀ A L i)) := by
  by_cases h : (winCond i.1 && i.2.1) = true
  · rw [wSig, conj_runSig_of m₀ _ _ _ i h]
    have hw : winCond i.1 = true := ((Bool.and_eq_true _ _).mp h).1
    exact (suppTo_readsProgram (m₀ := m₀) (v := valueAt L) (good := goodAll) L.perm (QReg.of Unit)
      (schemeWithHashFromSeed.verify i.1.1 i.1.2.1) _ _ (dec_wPre hprog hpre i.1 hw) i.2).mono
        fun _ hs ↦ ⟨h, hs⟩
  · rw [wSig, runSig_of_not m₀ _ _ _ i h, map_zero]
    exact querySupportedOn_zero _ _

end decomp

/-! ## The decomposition and `endReads` -/

section final

variable {m₀ : Finset HPos × Selections} {A : Adversary (X × Z)} {L : HonestTable}

/-- **The winning runs of the canonical game, decomposed along the verification's reads**: the
runs `wSig` of a winning prefix outcome and an accepting run of the verification's reads, with
the reads' log, recorded in the decompressed basis (`noBot_runtimeR`, the read program's
`SuppTo`), in the event `BadRS L progCap` where their view holds the log (`mem_bad_of_agrees`
from the prefix facts and the honest verification), their event weights part of the game's. -/
noncomputable def wDecomp [DecidablePred (· ∈ BadRS (S := HPos) L progCap)]
    (hprog : IPFunctor.IFreeM.IsChargeBound (wGame A L)
      (portCharge (L := LocalSig.instruments.{0})
        (extProgCharge X Z (Finset HPos × Selections) (recSpec HPos Selections))) progCap)
    (hpre : PrefixWinFacts m₀ A L) :
    WinDecomp m₀ (wGame A L) (wGame A L) (BadRS (S := HPos) L progCap) verifyBlocks verifyBlocks
      verifyBlocks where
  ι := (PublicKey × (Forgery × SignLog)) × (Bool × List (SpongeRead X Z))
  σ := wSig m₀ A L
  log := wLog
  psd i := runSig_posSemidef m₀ _ _ _ i
  countH i := readCount_wLog_le i .h
  countK i := readCount_wLog_le i .k
  countK' i := readCount_wLog_le i .k'
  recorded i := (dec_wSig hprog hpre i).mono fun s hs ↦ by
    obtain ⟨-, ⟨hnb, -⟩, ha⟩ := hs
    have hc : CountsOK i.2.2 := by
      rw [ha]
      exact countsOK_honest _ _ _ _
    refine ⟨hnb, ?_⟩
    rw [wLog_of_countsOK hc, agrees_iff_forall_heldBy, map_toSpongeRead_ofSpongeRead]
    intro e he
    rw [ha] at he
    exact heldBy_hwView_of_noBot hnb (honestEval_answeredBy L.perm _ _ e he)
  bad i := by
    have hdec := (dec_wSig hprog hpre i).mono (T := {s | ∃ Sel : SelFn, WinFacts L progCap Sel
        (wLog i) i.1.2.2 i.1.2.1 s.2.1 s.2.2.2}) fun s hs ↦ by
      obtain ⟨hw, ⟨hnb, hgr, hpk, Sel, hsig, hrec, hex⟩, ha⟩ := hs
      obtain ⟨hwc, hver⟩ := (Bool.and_eq_true _ _).mp hw
      have hc : CountsOK i.2.2 := by
        rw [ha]
        exact countsOK_honest _ _ _ _
      rw [hpk] at ha
      have hwin := hwc
      simp only [winCond, sufCmaScheme, decide_eq_true_eq] at hwin
      refine ⟨Sel, hgr, hsig, hrec, hex, hwin, fun U hU ↦ ?_⟩
      rw [wLog_of_countsOK hc, map_toSpongeRead_ofSpongeRead, ha] at hU
      have hcg : honestEval U.fill L.perm (schemeWithHashFromSeed.verify L.publicKey i.1.2.1) =
          honestEval (regFns s) L.perm (schemeWithHashFromSeed.verify L.publicKey i.1.2.1) :=
        honestEval_congr L.perm _ fun e he ↦ answeredBy_fill (hU e he)
      rw [hcg]
      refine ⟨?_, hU⟩
      rw [← ha]
      exact hver
    exact (querySupportedOn_of_conj_compressReg
      (P := fun b ↦ ∃ Sel : SelFn, WinFacts L progCap Sel (wLog i) i.1.2.2 i.1.2.1 b.1 b.2.2)
        hdec).mono fun s hs hag ↦ by
      obtain ⟨Sel, hf⟩ := hs
      exact mem_bad_of_agrees L Sel (wLog i) i.1.2.2 i.1.2.1 hf.grade hf.sigs hf.records hf.exempt
        hf.win hf.verify hag
  win := by
    rw [evalDistMap_winBit, wGame_eq]
    have h := ofReal_trace_conj_runSig m₀ (wPrefix A L) (wReads L)
      (fun pre a ↦ winCond pre && a.1) 1
    simp only [MatrixMap.conj_one, LinearMap.id_apply] at h
    exact h.le
  event := by
    have h := ofReal_trace_conj_runSig m₀ (wPrefix A L) (wReads L)
      (fun pre a ↦ winCond pre && a.1) ((1 : Matrix Unit Unit ℂ) ⊗ₖ hwProjector (BadRS L progCap))
    rw [← wGame_eq] at h
    exact h.symm.le.trans (trace_conj_branch_true_le_eventWeight m₀ (wGame A L) _)
  mass := by
    have h := ofReal_trace_conj_runSig m₀ (wPrefix A L) (wReads L)
      (fun pre a ↦ winCond pre && a.1) 1
    simp only [MatrixMap.conj_one, LinearMap.id_apply] at h
    rw [← wGame_eq] at h
    exact h.symm.le.trans (ofReal_trace_branch_le_one m₀ (wGame A L) true)

/-- **`endReads` for the canonical game**: on runs with at most `progCap` program calls and given
the prefix invariant `PrefixWinFacts`, the win weight of the game in `runtimeR m₀` is at most the
event weight of `BadRS L progCap` at the end of the game plus the read error of the verification's
`verifyBlocks` reads of each function. -/
theorem endReads_wGame [DecidablePred (· ∈ BadRS (S := HPos) L progCap)]
    (hprog : IPFunctor.IFreeM.IsChargeBound (wGame A L)
      (portCharge (L := LocalSig.instruments.{0})
        (extProgCharge X Z (Finset HPos × Selections) (recSpec HPos Selections))) progCap)
    (hpre : PrefixWinFacts m₀ A L) :
    (runtimeR m₀).evalDistMap .instruments (wGame A L) (SubState.basis ()) winBit {true} ≤
      (runtimeR m₀).eventWeight .instruments (hwProjector (BadRS L progCap)) (wGame A L)
          ((SubState.basis ()).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) +
        ENNReal.ofReal (readError X Z verifyBlocks verifyBlocks verifyBlocks) :=
  endReads_of_winDecomp L m₀ (wGame A L) (wGame A L) (wDecomp hprog hpre)

end final

end Quantum.Xmss.Assembly

end
