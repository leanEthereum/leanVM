module

public import Quantum.Qrom.Sphincs.Costs.RegrindModes
public import Quantum.Xmss.Assembly.CwRev

@[expose] public section

/-!
# Re-grinds: the invariant of leanSPHINCS's challenge prefix in the decompressed basis

In the decompressed basis the databases have no empty cell, the adversary's hash calls and the
reads keep them, and a program changes only its own cell, never a trial cell. So the view's pairs
at the trial cells are fixed along the prefix, and the trial reads return them.

* **The invariant** (`GlobG`, `rgInvG`): no decompressed `⊥`, no hardwired trial cell
  (`HwFreeG`), the recorded trial outcomes are the view's (`RdG`), and every selection of a key
  is the first codeword trial of the key's own search: trial `j`, read, a codeword in the view,
  the earlier trials read and no codewords (`SelG`, `NoPreG`). Within a search, its earlier trials
  were read and are no codewords.
* **The steps** (`rgInvG_read`, `rgInvG_prog`, `rgInvG_step`): every allowed call keeps the
  invariant of its mode.
* **At the calls of the prefix** (`forallQueries_rgInvG`): every call of `prefixQ pol A θ` is
  presented an operator whose decompressed form is supported on the invariant of a mode allowing
  it.
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker
open HashSig hiding PublicKey
open Sphincs hiding HashDomain

namespace Quantum.Qrom.Sphincs

open Quantum QuantumRuntime Quantum.Sponge
open Quantum.Sphincs (Key keyOf msgPos)
open Quantum.Xmss.Assembly (recHwSpec runtimeR runtimeRH decR liftRead liftAns NoBot initU
  noBot_init querySupportedOn_conj_compressReg querySupportedOn_inter forallQueries_of_modedP
  conjReg_branch conj_one_kronecker_comp_self querySupportedOn_traceRight)

attribute [local irreducible] sphincsRom

/- Instance search for the run families over the register exceeds the default size. -/
set_option synthInstance.maxSize 2000

/-! ## The invariant -/

section inv

variable (θ : TVals)

/-- **The trials before `j`** of the search of `K`: read, and no codewords in the view. -/
def NoPreG (rd : Qrom.HashDomain → Option PairOut) (s : RegQ) (K : Key) (j : ℕ) : Prop :=
  ∀ i < j, rd (tcG θ K i) ≠ none ∧
    ¬Quantum.Sphincs.Codeword.Valid (pairDigest (hvwS s (tcG θ K i)))

/-- **A selection by the search of `K`**: trial `j`, read, a codeword in the view, the earlier
trials read and no codewords. -/
def SelG (rd : Qrom.HashDomain → Option PairOut) (s : RegQ) (K : Key)
    (sel : Qrom.HashDomain × Digest) : Prop :=
  ∃ j, sel.1 = tcG θ K j ∧ rd sel.1 ≠ none ∧ sel.2 = pairDigest (hvwS s sel.1) ∧
    Quantum.Sphincs.Codeword.Valid sel.2 ∧ NoPreG θ rd s K j

/-- The recorded trial outcomes are the view's pairs at trial cells. -/
def RdG (rd : Qrom.HashDomain → Option PairOut) (s : RegQ) : Prop :=
  ∀ z y, rd z = some y → (∃ K c, z = tcG θ K c) ∧ hvwS s z = y

/-- No trial cell is hardwired. -/
def HwFreeG (s : RegQ) : Prop :=
  ∀ K c, s.2.1.1 (tcG θ K c) = none

/-- **The invariant between searches.** -/
def GlobG (rd : Qrom.HashDomain → Option PairOut) (s : RegQ) : Prop :=
  NoBot s ∧ HwFreeG θ s ∧ RdG θ rd s ∧ ∀ K sel, s.2.2.2 K = some sel → SelG θ rd s K sel

/-- **The invariant of a mode** (stated through the mode's projections: a mode computed by a
read is never reduced). -/
def rgInvG (μ : RgModeG) : Set RegQ :=
  {s | GlobG θ μ.2 s ∧ ∀ K j, μ.1 = .srch K j → NoPreG θ μ.2 s K j}

variable {θ}

theorem globG_of_inv {μ : RgModeG} {s : RegQ} (h : s ∈ rgInvG θ μ) : GlobG θ μ.2 s :=
  h.1

/-- The invariant between searches is the global one. -/
theorem mem_rgInvG_free {rd : Qrom.HashDomain → Option PairOut} {s : RegQ}
    (h : GlobG θ rd s) : s ∈ rgInvG θ (.free, rd) :=
  ⟨h, fun _ _ h' ↦ by cases h'⟩

/-- **The trials before a read** of the mode's search are read and no codewords. -/
theorem noPreG_of_curG {μ : RgModeG} {s : RegQ} (h : s ∈ rgInvG θ μ) {z : Qrom.HashDomain}
    {K : Key} {j : ℕ} (hc : curG θ μ.1 z = some (K, j)) : NoPreG θ μ.2 s K j := by
  obtain ⟨σ, rd⟩ := μ
  cases σ with
  | free =>
    have h0 : j = 0 := by
      revert hc
      show (keyAtG θ z).map (fun K ↦ (K, 0)) = some (K, j) → j = 0
      rcases keyAtG θ z with _ | K'
      · intro hc
        cases hc
      · intro hc
        exact (congrArg Prod.snd (Option.some.inj hc)).symm
    subst h0
    exact fun i hi ↦ absurd hi (Nat.not_lt_zero _)
  | srch K' j' =>
    cases hc
    exact h.2 _ _ rfl

/-- More recorded trial reads. -/
def RdLeG (rd rd' : Qrom.HashDomain → Option PairOut) : Prop :=
  ∀ z, rd z ≠ none → rd' z ≠ none

theorem noPreG_congr {rd rd' : Qrom.HashDomain → Option PairOut} {s s' : RegQ} {K : Key}
    {j : ℕ} (hrd : RdLeG rd rd') (hH : ∀ i, hvwS s' (tcG θ K i) = hvwS s (tcG θ K i))
    (h : NoPreG θ rd s K j) : NoPreG θ rd' s' K j := fun i hi ↦ by
  obtain ⟨h1, h2⟩ := h i hi
  exact ⟨hrd _ h1, by rw [hH]; exact h2⟩

theorem selG_congr {rd rd' : Qrom.HashDomain → Option PairOut} {s s' : RegQ} {K : Key}
    {sel : Qrom.HashDomain × Digest} (hrd : RdLeG rd rd')
    (hH : ∀ i, hvwS s' (tcG θ K i) = hvwS s (tcG θ K i)) (h : SelG θ rd s K sel) :
    SelG θ rd' s' K sel := by
  obtain ⟨j, h1, h2, h3, h4, h5⟩ := h
  refine ⟨j, h1, hrd _ h2, ?_, h4, noPreG_congr hrd hH h5⟩
  rw [h1] at h3 ⊢
  rw [hH]
  exact h3

theorem globG_congr {rd rd' : Qrom.HashDomain → Option PairOut} {s s' : RegQ}
    (hrd : RdLeG rd rd') (hnb : NoBot s') (hhw : HwFreeG θ s') (hRd : RdG θ rd' s')
    (hH : ∀ K c, hvwS s' (tcG θ K c) = hvwS s (tcG θ K c)) (hm : s'.2.2.2 = s.2.2.2)
    (h : GlobG θ rd s) : GlobG θ rd' s' := by
  refine ⟨hnb, hhw, hRd, fun K sel hsel ↦ ?_⟩
  rw [hm] at hsel
  exact selG_congr hrd (hH K) (h.2.2.2 K sel hsel)

/-- **A trial read keeps the invariant**: the view's pair at the trial cell is recorded and the
selection updated; the search stops at a codeword. -/
theorem rgInvG_read {rd : Qrom.HashDomain → Option PairOut} {K : Key} {j : ℕ}
    {z : Qrom.HashDomain} (hz : z = tcG θ K j) {s s' : RegQ} (hg : GlobG θ rd s)
    (hpre : NoPreG θ rd s K j) (h1 : s'.1 = s.1) (h2 : s'.2.1 = s.2.1)
    (h4 : s'.2.2.2 = cwUpd K z s.2.2.2 (some (hvwS s z))) :
    s' ∈ rgInvG θ ((if Quantum.Sphincs.Codeword.Valid (pairDigest (hvwS s z)) then .free
      else .srch K (j + 1)), Function.update rd z (some (hvwS s z))) := by
  obtain ⟨hnb, hhw, hrd, hsel⟩ := hg
  have hH : ∀ x, hvwS s' x = hvwS s x := fun x ↦ hvwS_congr (by rw [h2]) (by rw [h1])
  have hHi : ∀ i, hvwS s' (tcG θ K i) = hvwS s (tcG θ K i) := fun i ↦ hH _
  have hle : RdLeG rd (Function.update rd z (some (hvwS s z))) := fun w hw ↦ by
    by_cases hwz : w = z
    · rw [hwz, Function.update_self]
      exact Option.some_ne_none _
    · rwa [Function.update_of_ne hwz]
  have hRd : RdG θ (Function.update rd z (some (hvwS s z))) s' := by
    intro w y' hw
    by_cases hwz : w = z
    · rw [hwz, Function.update_self] at hw
      rw [hwz, hH, ← Option.some.inj hw]
      exact ⟨⟨K, j, hz⟩, rfl⟩
    · rw [Function.update_of_ne hwz] at hw
      obtain ⟨hw1, hw2⟩ := hrd w y' hw
      exact ⟨hw1, by rw [hH]; exact hw2⟩
  have hnb' : NoBot s' := noBot_of_fst_eq h1 hnb
  have hhw' : HwFreeG θ s' := fun K' c ↦ by rw [h2]; exact hhw K' c
  have hglob : s'.2.2.2 = s.2.2.2 → GlobG θ (Function.update rd z (some (hvwS s z))) s' :=
    fun hm ↦ globG_congr hle hnb' hhw' hRd (fun _ _ ↦ hH _) hm ⟨hnb, hhw, hrd, hsel⟩
  by_cases hv : Quantum.Sphincs.Codeword.Valid (pairDigest (hvwS s z))
  · rw [ite_eq_left hv]
    refine mem_rgInvG_free ?_
    by_cases hm : s.2.2.2 K = none
    · have hm' : s'.2.2.2 = s.2.2.2.select K z (pairDigest (hvwS s z)) := by
        rw [h4, cwUpd_some_of_none K z hm, cwSel, ite_eq_left hv]
      refine ⟨hnb', hhw', hRd, fun K' sel hs' ↦ ?_⟩
      rw [hm'] at hs'
      by_cases hk : K' = K
      · subst hk
        rw [SelMem.select_self] at hs'
        cases hs'
        refine ⟨j, hz, ?_, by rw [hH], hv, noPreG_congr hle hHi hpre⟩
        show Function.update rd z (some (hvwS s z)) z ≠ none
        rw [Function.update_self]
        exact Option.some_ne_none _
      · rw [SelMem.select_of_ne _ _ _ hk] at hs'
        exact selG_congr hle (fun _ ↦ hH _) (hsel K' sel hs')
    · exact hglob (h4.trans (cwUpd_of_ne_none hm _))
  · rw [ite_eq_right hv]
    have hm' : s'.2.2.2 = s.2.2.2 := by
      rw [h4]
      by_cases hm : s.2.2.2 K = none
      · rw [cwUpd_some_of_none K z hm, cwSel, ite_eq_right hv]
      · exact cwUpd_of_ne_none hm _
    refine ⟨hglob hm', fun K' j' h ↦ ?_⟩
    cases h
    show NoPreG θ (Function.update rd z (some (hvwS s z))) s' K (j + 1)
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
    · exact noPreG_congr hle hHi hpre i hi
    · rw [hi, ← hz, hH]
      refine ⟨?_, hv⟩
      rw [Function.update_self]
      exact Option.some_ne_none _

/-- **A program off the trial cells keeps the invariant between searches.** -/
theorem rgInvG_prog {μ : RgModeG} {z : Qrom.HashDomain} {a : PairOut}
    (hz : ∀ K j, z ≠ tcG θ K j) {s s' : RegQ} (hs : s ∈ rgInvG θ μ) (hR : ProgRelS z a s s') :
    s' ∈ rgInvG θ (.free, μ.2) := by
  obtain ⟨hR1, hR2, hR3⟩ := hR
  have hg := globG_of_inv hs
  have hW : ∀ x, x ≠ z → s'.2.1.1 x = s.2.1.1 x := fun x hx ↦ by
    rw [show s'.2.1 = Quantum.Xmss.Hybrid.progUpdate (.programH z a) s.2.1 from
      congrArg Prod.fst hR1, progUpdate_programH_fst]
    exact Function.update_of_ne hx _ _
  have hne : ∀ K c, tcG θ K c ≠ z := fun K c h ↦ hz K c h.symm
  have hH : ∀ K c, hvwS s' (tcG θ K c) = hvwS s (tcG θ K c) := fun K c ↦
    hvwS_congr (hW _ (hne K c)) (hR3 _ (hne K c))
  have hm : s'.2.2.2 = s.2.2.2 := by
    rw [hR1]
  refine mem_rgInvG_free ?_
  refine globG_congr (fun _ h ↦ h) (hR2 hg.1) (fun K c ↦ by rw [hW _ (hne K c)]; exact hg.2.1 K c)
    (fun w y hw ↦ ?_) hH hm hg
  obtain ⟨⟨K, c, rfl⟩, hw2⟩ := hg.2.2.1 w y hw
  exact ⟨⟨K, c, rfl⟩, by rw [hH]; exact hw2⟩

theorem readFinS_fstG {M : Type} (s : RRegS M) (z : Qrom.HashDomain)
    (upd : M → Option PairOut → M) : (readFinS s z upd).1 = s.1 :=
  rfl

theorem readFinS_hwG {M : Type} (s : RRegS M) (z : Qrom.HashDomain)
    (upd : M → Option PairOut → M) : (readFinS s z upd).2.1 = s.2.1 :=
  rfl

theorem readFinS_memG {M : Type} (s : RRegS M) (z : Qrom.HashDomain)
    (upd : M → Option PairOut → M) :
    (readFinS s z upd).2.2.2 = upd s.2.2.2 ((hwView s.2.1 s.1).1 z) :=
  rfl

/-- **Every allowed call keeps the invariant of its mode.** -/
theorem rgInvG_step (μ : RgModeG) (i : (RSpecS SelMem).Port) (r : (RSpecS SelMem).Result i)
    (σ : Matrix ((RSpecS SelMem).In i × RegQ) ((RSpecS SelMem).In i × RegQ) ℂ)
    (hok : rgOkZG θ μ i)
    (hσ : QuerySupportedOn (fun m : (RSpecS SelMem).In i × RegQ ↦ m.2) (rgInvG θ μ) σ) :
    QuerySupportedOn (fun m : (RSpecS SelMem).Out i × RegQ ↦ m.2) (rgInvG θ (rgNxZG θ μ i r))
      (((decR (X := PairOut) (Z := Qrom.HashDomain) m0Q).step i).branch r σ) := by
  rcases i with ((p | c) | c) | T
  · exact (decR_sponge_suppS m0Q p r _ σ hσ).mono fun _ hs ↦ mem_rgInvG_free (globG_of_inv hs)
  · obtain ⟨K, j, hcur, rfl⟩ := hok
    refine (decR_readH_suppS m0Q (tcG θ K j) (cwUpd K (tcG θ K j)) r _ σ hσ).mono ?_
    rintro _ ⟨s, hs, rfl, rfl⟩
    have hv : (hwView s.2.1 s.1).1 (tcG θ K j) = some (hvwS s (tcG θ K j)) :=
      hwView_eq_some_hvwS (globG_of_inv hs).1 _
    have hmode : rgNxZG θ μ (.inl (.inl (.inr (trialRead (tcG θ K j) K))))
        (liftAns s (.readH (tcG θ K j) (cwUpd K (tcG θ K j)))) =
        ((if Quantum.Sphincs.Codeword.Valid (pairDigest (hvwS s (tcG θ K j))) then .free
          else .srch K (j + 1)), Function.update μ.2 (tcG θ K j) (some (hvwS s (tcG θ K j)))) := by
      show rgStepG θ μ (tcG θ K j) ((hwView s.2.1 s.1).1 (tcG θ K j)) = _
      rw [rgStepG_of hcur, hv, Option.getD_some]
    rw [hmode]
    exact rgInvG_read (rd := μ.2) (K := K) (j := j) (z := tcG θ K j) (s := s)
      (s' := readFinS s (tcG θ K j) (cwUpd K (tcG θ K j))) rfl (globG_of_inv hs)
      (noPreG_of_curG hs hcur) (readFinS_fstG _ _ _) (readFinS_hwG _ _ _)
      ((readFinS_memG s (tcG θ K j) (cwUpd K (tcG θ K j))).trans
        (congrArg (cwUpd K (tcG θ K j) s.2.2.2) hv))
  · obtain ⟨z, a, rfl, hz⟩ := hok
    refine (decR_progH_suppS m0Q z a r _ σ hσ).mono ?_
    rintro _ ⟨_, hs, hR⟩
    exact rgInvG_prog hz hs hR
  · refine (decR_rec_suppS m0Q T r _ σ hσ).mono ?_
    rintro _ ⟨s, hs, -, rfl⟩
    have hg := globG_of_inv hs
    have hH : ∀ x, hvwS (s.1, s.2.1, (s.2.2.1 ∪ T, s.2.2.2)) x = hvwS s x := fun _ ↦ rfl
    exact mem_rgInvG_free (globG_congr (fun _ h ↦ h) (noBot_of_fst_eq rfl hg.1)
      (fun K c ↦ hg.2.1 K c)
      (fun w y hw ↦ ⟨(hg.2.2.1 w y hw).1, (hH w).trans (hg.2.2.1 w y hw).2⟩)
      (fun _ _ ↦ hH _) rfl hg)

/-- **The initial operator in the decompressed basis**: no empty cell, no hardwired cell, memory
`m0Q`. -/
theorem init_decG :
    QuerySupportedOn (fun p : Unit × RegQ ↦ p.2)
      {s | NoBot s ∧ s.2 = (hwEmpty PairOut Qrom.HashDomain, m0Q)}
      (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ
        compressReg PairOut Qrom.HashDomain QMem) initQ) := by
  have h0 : QuerySupportedOn (fun p : Unit × RegQ ↦ p.2)
      {s | s.2 = (hwEmpty PairOut Qrom.HashDomain, m0Q)} initQ := by
    intro m m' hm
    change ((SubState.basis ()).matrix ⊗ₖ (SubState.basis (((Database.empty, Database.empty,
      Database.empty), hwEmpty PairOut Qrom.HashDomain, m0Q) : RegQ)).matrix) m m' ≠ 0 at hm
    simp only [SubState.matrix_basis] at hm
    have h := right_ne_zero_of_mul hm
    rw [Matrix.single_apply] at h
    split_ifs at h with he
    · exact ⟨congrArg Prod.snd he.1.symm, congrArg Prod.snd he.2.symm⟩
    · exact absurd rfl h
  exact querySupportedOn_inter (noBot_init m0Q (A := Unit) (SubState.basis ()).matrix)
    (querySupportedOn_conj_compressReg
      (P := fun b ↦ b = (hwEmpty PairOut Qrom.HashDomain, m0Q)) h0)

variable (θ)

theorem rgInvG_init :
    QuerySupportedOn (fun m : QReg.of Unit × RegQ ↦ m.2) (rgInvG θ (.free, fun _ ↦ none))
      (MatrixMap.conj ((1 : Matrix (QReg.of Unit) (QReg.of Unit) ℂ) ⊗ₖ
        compressReg PairOut Qrom.HashDomain QMem) initQ) := by
  refine init_decG.mono ?_
  rintro s ⟨hn, hs⟩
  have hW : s.2.1 = hwEmpty PairOut Qrom.HashDomain := congrArg Prod.fst hs
  have hM : s.2.2.2 = fun _ ↦ none := congrArg (·.2.2) hs
  refine mem_rgInvG_free ⟨hn, fun K c ↦ ?_, fun _ _ h ↦ by simp at h, fun K sel h ↦ ?_⟩
  · rw [hW]
    simp [hwEmpty, Database.empty]
  · change s.2.2.2 K = some sel at h
    rw [hM] at h
    cases h

end inv

/-! ## The invariant at the calls of the prefix -/

section calls

variable (θ : TVals)

/-- **The invariant at the calls of the prefix, in the decompressed basis.** -/
theorem forallQueries_rgInvG_dec (pol : DigestPolicy) (A : SAdversary) :
    (decR (X := PairOut) (Z := Qrom.HashDomain) m0Q).ForallQueries .instruments (fun i E σ ↦ ∃ μ,
      rgOkZG θ μ i ∧ QuerySupportedOn (fun m : ((RSpecS SelMem).In i × RegQ) × E ↦ m.1.2)
        (rgInvG θ μ) σ) (prefixQ pol A θ)
      (MatrixMap.conj ((1 : Matrix (QReg.of Unit) (QReg.of Unit) ℂ) ⊗ₖ
        compressReg PairOut Qrom.HashDomain QMem) initQ) :=
  forallQueries_of_modedP (decR (X := PairOut) (Z := Qrom.HashDomain) m0Q) .instruments
    (rgInvG θ) (fun μ i r σ hok hσ ↦ rgInvG_step μ i r σ hok hσ) (prefixQ pol A θ)
    (.free, fun _ ↦ none) (rgModed_prefixQG θ pol A _) (rgInvG_init θ)

/-- **The invariant at the calls of the prefix**: every call of `prefixQ pol A θ` is presented an
operator whose decompressed form is supported on the invariant of a mode allowing it. -/
theorem forallQueries_rgInvG (pol : DigestPolicy) (A : SAdversary) :
    (runtimeR m0Q).ForallQueries .instruments (fun i E τ ↦ ∃ μ, rgOkZG θ μ i ∧
      QuerySupportedOn (fun m : (RSpecS SelMem).In i × RegQ ↦ m.2) (rgInvG θ μ)
        (MatrixMap.conj ((1 : Matrix ((RSpecS SelMem).In i) ((RSpecS SelMem).In i) ℂ) ⊗ₖ
          compressReg PairOut Qrom.HashDomain QMem) (MatrixMap.traceRight _ E τ)))
      (prefixQ pol A θ) initQ := by
  have hC : compressReg PairOut Qrom.HashDomain QMem * compressReg PairOut Qrom.HashDomain QMem =
      1 :=
    compressReg_mul_self
  have hstep : ∀ i r, ((runtimeRH (X := PairOut) (Z := Qrom.HashDomain) m0Q).step i).branch r ∘ₗ
      (MatrixMap.conj (compressReg PairOut Qrom.HashDomain QMem)).amplifyLeft
        ((RSpecS SelMem).In i) =
      (MatrixMap.conj (compressReg PairOut Qrom.HashDomain QMem)).amplifyLeft
        ((RSpecS SelMem).Out i) ∘ₗ
        ((decR (X := PairOut) (Z := Qrom.HashDomain) m0Q).step i).branch r := fun i r ↦ by
    rw [conjReg_branch (runtimeRH m0Q) (compressReg PairOut Qrom.HashDomain QMem)
      compressReg_mul_self conjTranspose_compressReg i r]
    simp only [MatrixMap.amplifyLeft_conj]
    rw [← LinearMap.comp_assoc, conj_one_kronecker_comp_self (runtimeRH m0Q) _ hC,
      LinearMap.id_comp]
  have h2 := ForallQueries.of_simulation .instruments
    (R₁ := decR (X := PairOut) (Z := Qrom.HashDomain) m0Q)
    (R₂ := runtimeRH (X := PairOut) (Z := Qrom.HashDomain) m0Q)
    (V := MatrixMap.conj (compressReg PairOut Qrom.HashDomain QMem)) hstep
    (P₂ := fun i E τ ↦ ∃ μ, rgOkZG θ μ i ∧
      QuerySupportedOn (fun m : (RSpecS SelMem).In i × RegQ ↦ m.2) (rgInvG θ μ)
        (MatrixMap.conj ((1 : Matrix ((RSpecS SelMem).In i) ((RSpecS SelMem).In i) ℂ) ⊗ₖ
          compressReg PairOut Qrom.HashDomain QMem) (MatrixMap.traceRight _ E τ)))
    (fun i E τ ⟨μ, hok, hτ⟩ ↦ ⟨μ, hok, by
      rw [MatrixMap.amplifyLeft_conj,
        ← LinearMap.comp_apply (MatrixMap.conj _) (MatrixMap.traceRight _ E),
        ← MatrixMap.traceRight_comp_amplify, LinearMap.comp_apply,
        ← LinearMap.comp_apply (MatrixMap.amplify _ E) (MatrixMap.amplify _ E),
        ← MatrixMap.amplify_comp, conj_one_kronecker_comp_self (runtimeRH m0Q) _ hC,
        MatrixMap.amplify_id, LinearMap.id_apply]
      exact querySupportedOn_traceRight
        (q := fun m : (RSpecS SelMem).In i × RegQ ↦ m.2) hτ⟩)
    (forallQueries_rgInvG_dec θ pol A)
  have hρ' : (MatrixMap.conj (compressReg PairOut Qrom.HashDomain QMem)).amplifyLeft
      (QReg.of Unit)
      (MatrixMap.conj ((1 : Matrix (QReg.of Unit) (QReg.of Unit) ℂ) ⊗ₖ
        compressReg PairOut Qrom.HashDomain QMem) initQ) = initQ := by
    rw [MatrixMap.amplifyLeft_conj,
      ← LinearMap.comp_apply (MatrixMap.conj ((1 : Matrix (QReg.of Unit) (QReg.of Unit) ℂ) ⊗ₖ
        compressReg PairOut Qrom.HashDomain QMem)),
      conj_one_kronecker_comp_self (runtimeRH m0Q) _ hC, LinearMap.id_apply]
  rw [hρ'] at h2
  exact h2

end calls

end Quantum.Qrom.Sphincs

end
