/-
  LeanVM.Guest.B1.VsC.VkPJ

  `verify_keccak` placed: its callees one after the other (`KidsAtF`), on any valuation giving
  their honest words.
-/

module

public import LeanVM.Guest.B1.VsC.VkPI
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_keccak»

/-!
# The callees, one after the other

`PreI`: the caller's words. `LOut s`: layer `s`'s `Out` (its next claim's record, once its own
words are held). `HonestCalls σ cs`: the eighteen calls with their honest arguments and returns.
`vk_kids`: they complete one after the other from `c + τ + 412` (`KidsAtF`), and at the end the
memory holds `verify_keccak`'s own words and every layer's next claim; the data they claim
contains the layers' buffers.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.Memory LeanVM.Guest.B1.Fwd LeanVM.Guest.Complete
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr Finset LeanVM.Guest.B1.VerifySub.KL
open LeanVM.Prover.Exec (allocBase)

open LeanVM.Guest.B1.VsC (PostQuiet lpB clArgs plain60_placed plain41_placed)

@[expose] public section

namespace VkData

variable (D : VkData) (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) (k : ℕ)
variable (c curE chiE olE zvE slE tbE : ℕ)

/-- The caller's words. -/
def PreI (rd : Reader) : Prop :=
  WinTabs rd (VsC.ptrAtV tbE) ∧ ReadsAt rd (VsC.ptrAtV chiE) D.chis ∧ ReadsAt rd (VsC.ptrAtV olE) D.outs ∧
    ReadsAt rd (VsC.ptrAtV curE) D.xs ∧ ReadsAt rd (VsC.ptrAtV zvE) D.op ∧
    ReadsAt rd (VsC.ptrAtV zvE * gen ^ qkeccakVarsCap) D.point ∧ ReadsAt rd (VsC.ptrAtV slE) D.slices

/-- Layer `s`'s `Out`. -/
def LOut (s : ℕ) (rd : Reader) : Prop :=
  ReadsAt rd (VsC.ptrAtV (c + D.o201 + 22 * (s + 1)))
      (VsC.klOutW ((D.layer s).next (firstOf s)) (D.lsP fs al cert k c curE tbE s) (D.τ - 3)) →
    ClaimRec rd false (VsC.ptrAtV (c + D.o201 + 22 * (s + 1))) ((D.layer s).next (firstOf s)) (D.τ - 3)

/-- The own words, the layers at their positions. -/
noncomputable abbrev WoP : Words := D.Wo c (D.lsP fs al cert k c curE tbE)

/-- Where the callees end. -/
noncomputable def q12 : ℕ := (D.posP fs al cert k c curE tbE 12).1
noncomputable def eo : ℕ := allocBase (al "keccak_plain_rounds__L6_L0") (D.q12 fs al cert k c curE tbE) +
  fs "keccak_plain_rounds__L6_L0"
noncomputable def e1 : ℕ := allocBase (al name% «verify_keccak_loop1») (D.eo fs al cert k c curE tbE) +
  lpB fs name% «verify_keccak_loop1» (D.τ - 4) 0
noncomputable def ei : ℕ := allocBase (al "keccak_plain_rounds__L4_L1") (D.e1 fs al cert k c curE tbE) +
  fs "keccak_plain_rounds__L4_L1"
noncomputable def es : ℕ := allocBase (al "keccak_plain_rounds__L6_L0") (D.ei fs al cert k c curE tbE) +
  fs "keccak_plain_rounds__L6_L0"
noncomputable def eF : ℕ := allocBase (al name% «verify_keccak_loop2») (D.es fs al cert k c curE tbE) +
  lpB fs name% «verify_keccak_loop2» (D.τ - 4) 0

/-- **The calls carry their honest words.** -/
def HonestCalls (σ : Val) (cs : List Call) : Prop :=
  ∃ (a0 : List V) (as rs : ℕ → List V) (ao ro a1 ai ri as' rs' a2 : List V),
    cs = ⟨name% «verify_keccak_loop0», a0, [], true⟩ ::
      ((List.range 12).map fun s ↦ (⟨lname s, as s, rs s, true⟩ : Call)) ++
      [⟨"keccak_plain_rounds__L6_L0", ao, ro, true⟩, ⟨name% «verify_keccak_loop1», a1, [], true⟩,
        ⟨"keccak_plain_rounds__L4_L1", ai, ri, true⟩, ⟨"keccak_plain_rounds__L6_L0", as', rs', true⟩,
        ⟨name% «verify_keccak_loop2», a2, [], true⟩] ∧
    a0.map σ = clArgs 0 (D.τ - 4) c (chiE + 4) ∧
    (∀ s < 12, (as s).map σ = D.layArgs c curE tbE s ∧
      (rs s).map σ = (D.layer s).rets (firstOf s) (VsC.ptrAtV (curE + D.lcur s))) ∧
    ao.map σ = D.oArgs curE zvE tbE ∧ ro.map σ = D.oRets curE ∧
    a1.map σ = clArgs 0 (D.τ - 4) (zvE + 4) c ∧
    ai.map σ = D.iArgs curE zvE tbE ∧ ri.map σ = D.iRets curE ∧
    as'.map σ = D.sArgs curE zvE tbE ∧ rs'.map σ = D.sRets curE ∧
    a2.map σ = clArgs 0 (D.τ - 4) (zvE + 43) (D.lsP fs al cert k c curE tbE 11)

variable {D fs al cert k c curE chiE olE zvE slE tbE}

/-- A claim's record with its pointers' words. -/
theorem claimRecAt_of {rd : Reader} {first : Bool} {rec cpt clp clc cfl : E} {cl : KeccakClaim} {y : ℕ}
    (h : ClaimRec rd first rec cl y) (h2 : LoadHolds rd rec 2 cpt) (h3 : LoadHolds rd rec 3 clp)
    (h45 : first = false → LoadHolds rd rec 4 clc ∧ LoadHolds rd rec 5 cfl) :
    VsC.ClaimRecAt rd first rec cpt clp clc cfl cl y := by
  obtain ⟨a1, a2, a3, a4, a5, ⟨pp, hpp, hpt⟩, lp, lanes, hlp, hl, hla, hrest⟩ := h
  have e2 := loadHolds_unique hpp h2
  have e3 := loadHolds_unique hlp h3
  subst e2 e3
  refine ⟨a1, a2, a3, a4, a5, hpp, hpt, lanes, hlp, hl, hla, ?_⟩
  cases first
  · simp only [Bool.false_eq_true, ↓reduceIte] at hrest ⊢
    obtain ⟨lc, fl, loc, b1, b2, b3, b4, b5, b6⟩ := hrest
    obtain ⟨c4, c5⟩ := h45 rfl
    have e4 := loadHolds_unique b1 c4
    have e5 := loadHolds_unique b4 c5
    subst e4 e5
    exact ⟨loc, b1, b2, b3, b4, b5, b6⟩
  · simpa using hrest

theorem lsP_eq (s : ℕ) :
    D.lsP fs al cert k c curE tbE s = D.lfp fs al cert k c curE tbE s + fs (lname s) := rfl

/-- **Layer `s`'s `Pre`** on the caller's words, the own words and the previous layer's `Out`. -/
theorem layer_pre (h : D.Ok) {s : ℕ} (hs : s < 12) {rd : Reader} (hP : D.PreI curE chiE olE zvE slE tbE rd)
    (hW : HoldsWords rd (D.WoP fs al cert k c curE tbE))
    (hprev : ∀ j, s = j + 1 → D.LOut fs al cert k c curE tbE j rd) :
    WinTabs rd (VsC.ptrAtV tbE) ∧
      VsC.ClaimRecAt rd (firstOf s = 1) (VsC.ptrAtV (c + D.o201 + 22 * s))
        (D.recPtrs c s (D.posP fs al cert k c curE tbE s).2).1
        (D.recPtrs c s (D.posP fs al cert k c curE tbE s).2).2.1
        (D.recPtrs c s (D.posP fs al cert k c curE tbE s).2).2.2.1
        (D.recPtrs c s (D.posP fs al cert k c curE tbE s).2).2.2.2 (D.layer s).c (D.τ - 3) ∧
      ReadsAt rd (VsC.ptrAtV (curE + D.lcur s))
        (VsC.klXs (D.T s).1 (D.T s).2.1 (D.T s).2.2.1 (D.T s).2.2.2.1 (D.T s).2.2.2.2) ∧
      ReadsAt rd (VsC.ptrAtV (c + D.o201 + 22 * (s + 1)))
        (VsC.klOutW ((D.layer s).next (firstOf s))
          (D.lfp fs al cert k c curE tbE s + fs (lname s)) (D.τ - 3)) := by
  obtain ⟨htb, -, -, hcur, -⟩ := hP
  obtain ⟨-, -, mcw, -, mo, -⟩ := own_mem hW
  refine ⟨htb, ?_, (xs_reads h hcur).2.1 s hs, mo s hs⟩
  rcases s with _ | j
  · have hr := rec0 h hW
    have hcw : ∀ k < 4, LoadHolds rd (VsC.ptrAtV (c + D.o201)) k ((D.cw0 c).getD k 0) :=
      fun k hk ↦ readsAt_getD mcw (by simp [cw0]; omega)
    simp only [recPtrs, ↓reduceIte, firstOf, decide_true, Nat.mul_zero, Nat.add_zero]
    exact claimRecAt_of hr (by simpa [cw0] using hcw 2 (by norm_num))
      (by simpa [cw0] using hcw 3 (by norm_num)) (fun h ↦ absurd h (by simp))
  · have hc : (D.layer (j + 1)).c = (D.layer j).next (firstOf j) := by
      show (D.chain (j + 1)).1 = _
      rw [D.layer_succ h (by omega)]
    have hr := hprev j rfl (mo j (by omega))
    have hrec := mo j (by omega)
    have hk : ∀ m < 6, LoadHolds rd (VsC.ptrAtV (c + D.o201 + 22 * (j + 1))) m
        ((D.outWs (D.lsP fs al cert k c curE tbE) j).getD m 0) :=
      fun m hm ↦ readsAt_getD hrec (by rw [outWs_length]; omega)
    have hf : firstOf (j + 1) = 0 := rfl
    simp only [recPtrs, show j + 1 ≠ 0 by omega, ↓reduceIte, hf, posP_snd]
    rw [hc]
    exact claimRecAt_of hr (by simpa [outWs, VsC.klOutW] using hk 2 (by norm_num))
      (by simpa [outWs, VsC.klOutW] using hk 3 (by norm_num))
      (fun _ ↦ ⟨by simpa [outWs, VsC.klOutW] using hk 4 (by norm_num),
        by simpa [outWs, VsC.klOutW] using hk 5 (by norm_num)⟩)

/-- Layer `s`'s arguments, as the layer is stated. -/
theorem layArgs_eq (h : D.Ok) {s : ℕ} (hs : s < 12) :
    D.layArgs c curE tbE s =
      [(D.layer s).cap.getD 0 0, (D.layer s).cap.getD 1 0, (D.layer s).cap.getD 2 0,
        (D.layer s).cap.getD 3 0, (D.layer s).cap.getD 4 0, (D.cells s).1, (D.cells s).2,
        VsC.ptrAtV (curE + D.lcur s), gen ^ (D.τ - 3), gen ^ ((D.τ - 3) / krStep),
        gen ^ ((D.τ - 3) % krStep), VsC.ptrAtV (c + D.o201 + 22 * s),
        VsC.ptrAtV (c + D.o201 + 22 * (s + 1)), keccakIota D.τ s (D.layer s).c, VsC.ptrAtV tbE] := by
  rw [layArgs, layerArgs, cap_eq h hs, D.layer_y h hs.le]
  rfl

/-- Layer `s`'s returns, as the layer is stated. -/
theorem layRets_eq (h : D.Ok) {s : ℕ} (hs : s < 12) :
    (D.layer s).rets (firstOf s) (VsC.ptrAtV (curE + D.lcur s)) =
      (layerBeta (D.layer s).c (plainStart (firstOf s) [(D.layer s).cap.getD 0 0, (D.layer s).cap.getD 1 0,
          (D.layer s).cap.getD 2 0, (D.layer s).cap.getD 3 0, (D.layer s).cap.getD 4 0] D.committed)
          (D.T s).1 (D.T s).2.1 (D.T s).2.2.1 (D.T s).2.2.2.1 (D.T s).2.2.2.2).2.cap ++
        [VsC.ptrAtV (curE + D.lcur s) *
          gen ^ (VsC.klXs (D.T s).1 (D.T s).2.1 (D.T s).2.2.1 (D.T s).2.2.2.1 (D.T s).2.2.2.2).length] := by
  have hl : (VsC.klXs (D.T s).1 (D.T s).2.1 (D.T s).2.2.1 (D.T s).2.2.2.1 (D.T s).2.2.2.2).length =
      48 + 2 * (D.layer s).y + 36 := by rw [D.layer_y h hs.le]; exact ltXs_length h hs
  rw [hl, LayerData.rets, LayerData.beta, LayerData.s0, ← cap_eq h hs]
  rfl

variable {σ : Val} {RN : ℕ → Prop}

set_option maxHeartbeats 1000000 in
/-- **Layer `s`, then the rest.** -/
theorem kid_layer (hL : VsC.KeccakLayerCompleteA fs al cert k) (h : D.Ok)
    (hRN : ∀ i, ((c ≤ i ∧ i < c + D.τ + 412) ∨ D.LinR curE chiE olE zvE slE i ∨
      (tbE ≤ i ∧ i < tbE + 2 ^ winTabBits)) → RN i) {s : ℕ} (hs : s < 12)
    {O : Reader → Prop} {Dacc : ℕ → Prop} {Qs : List (Reader → Tree → Prop)} {cs : List Call} {e : ℕ}
    {Oend : Reader → Prop} {Dend : ℕ → Prop} {as rs : List V}
    (ha : as.map σ = D.layArgs c curE tbE s)
    (hr : rs.map σ = (D.layer s).rets (firstOf s) (VsC.ptrAtV (curE + D.lcur s)))
    (hW : ∀ rd, O rd → HoldsWords rd (D.WoP fs al cert k c curE tbE))
    (hprev : ∀ j, s = j + 1 → ∀ rd, O rd → D.LOut fs al cert k c curE tbE j rd)
    (hD : ∀ j, s = j + 1 → ∀ i, VsC.klOwn (D.lsP fs al cert k c curE tbE j) (D.τ - 3) i → Dacc i)
    (hrest : KidsAtF fs al cert k σ RN (D.PreI curE chiE olE zvE slE tbE)
      (fun rd => O rd ∧ D.LOut fs al cert k c curE tbE s rd)
      (fun i => Dacc i ∨ VsC.klOwn (D.lsP fs al cert k c curE tbE s) (D.τ - 3) i) Qs cs
      (D.posP fs al cert k c curE tbE (s + 1)).1 e Oend Dend) :
    KidsAtF fs al cert k σ RN (D.PreI curE chiE olE zvE slE tbE) O Dacc (PostQuiet :: Qs)
      (⟨lname s, as, rs, true⟩ :: cs) (D.posP fs al cert k c curE tbE s).1 e Oend Dend := by
  rw [KidsAtF]
  simp only [↓reduceIte]
  obtain ⟨-, -, hc⟩ := lp_spec (curE := curE) hL h hs
  refine ⟨fs (lname s), (D.posP fs al cert k c curE tbE (s + 1)).1,
    D.lR c curE tbE s (D.posP fs al cert k c curE tbE s).2,
    VsC.klOwn (D.lsP fs al cert k c curE tbE s) (D.τ - 3), D.LOut fs al cert k c curE tbE s,
    fun i hi ↦ ?_, ?_, hrest⟩
  · rcases hi with hi | hi | hi | ⟨h1, hi⟩
    · exact Or.inl (hRN i (Or.inl hi))
    · exact Or.inl (hRN i (Or.inr (Or.inl (Or.inl hi))))
    · exact Or.inl (hRN i (Or.inr (Or.inr hi)))
    · obtain ⟨j, rfl⟩ : ∃ j, s = j + 1 := ⟨s - 1, by omega⟩
      exact Or.inr (hD j rfl i (by rw [posP_snd] at hi; exact ⟨hi.1, by omega⟩))
  · rw [ha, hr, layArgs_eq h hs, layRets_eq h hs]
    refine hc.mono (fun _ h ↦ h) (fun _ h ↦ h) (fun _ h ↦ h) (fun rd ⟨hp, ho⟩ ↦ ?_)
      (fun _ _ _ h ↦ h)
    exact layer_pre h hs hp (hW rd ho) (fun j hj ↦ hprev j hj rd ho)

/-- **The layers from `12 - n`, then the rest.** -/
theorem kids_from (hL : VsC.KeccakLayerCompleteA fs al cert k) (h : D.Ok)
    (hRN : ∀ i, ((c ≤ i ∧ i < c + D.τ + 412) ∨ D.LinR curE chiE olE zvE slE i ∨
      (tbE ≤ i ∧ i < tbE + 2 ^ winTabBits)) → RN i) {as rs : ℕ → List V}
    (has : ∀ s < 12, (as s).map σ = D.layArgs c curE tbE s ∧
      (rs s).map σ = (D.layer s).rets (firstOf s) (VsC.ptrAtV (curE + D.lcur s)))
    {tail : List Call} {Qt : List (Reader → Tree → Prop)} {e : ℕ} {Oend : Reader → Prop} {Dend : ℕ → Prop}
    (htail : ∀ (O : Reader → Prop) (Dacc : ℕ → Prop), (∀ rd, O rd → HoldsWords rd (D.WoP fs al cert k c curE tbE)) →
      (∀ rd, O rd → ∀ j < 12, D.LOut fs al cert k c curE tbE j rd) →
      (∀ j < 12, ∀ i, VsC.klOwn (D.lsP fs al cert k c curE tbE j) (D.τ - 3) i → Dacc i) →
      KidsAtF fs al cert k σ RN (D.PreI curE chiE olE zvE slE tbE) O Dacc Qt tail
        (D.posP fs al cert k c curE tbE 12).1 e Oend Dend) :
    ∀ n, n ≤ 12 → ∀ (O : Reader → Prop) (Dacc : ℕ → Prop),
      (∀ rd, O rd → HoldsWords rd (D.WoP fs al cert k c curE tbE)) →
      (∀ rd, O rd → ∀ j < 12 - n, D.LOut fs al cert k c curE tbE j rd) →
      (∀ j < 12 - n, ∀ i, VsC.klOwn (D.lsP fs al cert k c curE tbE j) (D.τ - 3) i → Dacc i) →
      KidsAtF fs al cert k σ RN (D.PreI curE chiE olE zvE slE tbE) O Dacc
        (List.replicate n PostQuiet ++ Qt)
        (((List.range' (12 - n) n).map fun s ↦ (⟨lname s, as s, rs s, true⟩ : Call)) ++ tail)
        (D.posP fs al cert k c curE tbE (12 - n)).1 e Oend Dend
  | 0, _, O, Dacc, hW, hO, hD => by
    simpa using htail O Dacc hW hO hD
  | n + 1, hn, O, Dacc, hW, hO, hD => by
    have e1 : 12 - n = (12 - (n + 1)) + 1 := by omega
    have IH := kids_from hL h hRN has htail n (by omega)
      (fun rd => O rd ∧ D.LOut fs al cert k c curE tbE (12 - (n + 1)) rd)
      (fun i => Dacc i ∨ VsC.klOwn (D.lsP fs al cert k c curE tbE (12 - (n + 1))) (D.τ - 3) i)
      (fun rd ho ↦ hW rd ho.1)
      (fun rd ho j hj ↦ by
        rcases Nat.lt_or_ge j (12 - (n + 1)) with hj' | hj'
        · exact hO rd ho.1 j hj'
        · obtain rfl : j = 12 - (n + 1) := by omega
          exact ho.2)
      (fun j hj i hi ↦ by
        rcases Nat.lt_or_ge j (12 - (n + 1)) with hj' | hj'
        · exact Or.inl (hD j hj' i hi)
        · obtain rfl : j = 12 - (n + 1) := by omega
          exact Or.inr hi)
    rw [e1] at IH
    have hr : List.range' (12 - (n + 1)) (n + 1) = (12 - (n + 1)) :: List.range' (12 - (n + 1) + 1) n :=
      List.range'_succ ..
    rw [hr, List.replicate_succ, List.map_cons, List.cons_append, List.cons_append]
    exact kid_layer hL h hRN (by omega) (has _ (by omega)).1 (has _ (by omega)).2 hW
      (fun j hj rd ho ↦ hO rd ho j (by omega)) (fun j hj i hi ↦ hD j (by omega) i hi) IH

theorem inst_drop_length (h : D.Ok) : (D.inst.drop 4).length = D.τ - 4 := by
  rw [List.length_drop, inst_length h]

theorem readsAt_take {rd : Reader} {p : E} {l : List E} (h : ReadsAt rd p l) (n : ℕ) :
    ReadsAt rd p (l.take n) := fun j hj ↦ by
  rw [List.getElem_take]; exact h j (by simp at hj; omega)

variable (D fs al cert k c curE tbE) in
/-- The closing calls' end conditions. -/
def Oend (rd : Reader) : Prop :=
  HoldsWords rd (D.WoP fs al cert k c curE tbE) ∧ ∀ j < 12, D.LOut fs al cert k c curE tbE j rd

variable (D fs al cert k c curE tbE) in
def Dend (i : ℕ) : Prop := ∃ j < 12, VsC.klOwn (D.lsP fs al cert k c curE tbE j) (D.τ - 3) i

/-- A taken call, then the rest. -/
theorem kid_taken {RN : ℕ → Prop} {Pre O : Reader → Prop} {Dacc : ℕ → Prop}
    {Qs : List (Reader → Tree → Prop)} {cs : List Call} {cur e : ℕ} {Oend : Reader → Prop}
    {Dend : ℕ → Prop} {f : String} {args rets : List V} {Bc ec : ℕ} {Rc Dc : ℕ → Prop}
    {Oc : Reader → Prop} (hR : ∀ i, Rc i → RN i ∨ Dacc i)
    (hc : CallAtA fs al cert k f (args.map σ) (rets.map σ) Rc Dc Oc (fun rd => Pre rd ∧ O rd) PostQuiet Bc
      (allocBase (al f) cur) (allocBase (al f) cur + Bc) ec)
    (hrest : KidsAtF fs al cert k σ RN Pre (fun rd => O rd ∧ Oc rd) (fun i => Dacc i ∨ Dc i) Qs cs ec e
      Oend Dend) :
    KidsAtF fs al cert k σ RN Pre O Dacc (PostQuiet :: Qs) (⟨f, args, rets, true⟩ :: cs) cur e Oend Dend := by
  rw [KidsAtF]
  simp only [↓reduceIte, List.headD_cons, List.tail_cons]
  exact ⟨Bc, ec, Rc, Dc, Oc, hR, hc, hrest⟩

/-- A taken call claiming no data, then the rest. -/
theorem kid_taken0 {RN : ℕ → Prop} {Pre O : Reader → Prop} {Dacc : ℕ → Prop}
    {Qs : List (Reader → Tree → Prop)} {cs : List Call} {cur e : ℕ} {Oend : Reader → Prop}
    {Dend : ℕ → Prop} {f : String} {args rets : List V} {Bc ec : ℕ} {Rc : ℕ → Prop}
    {Oc : Reader → Prop} (hR : ∀ i, Rc i → RN i ∨ Dacc i)
    (hc : CallAtA fs al cert k f (args.map σ) (rets.map σ) Rc (fun _ => False) Oc (fun rd => Pre rd ∧ O rd)
      PostQuiet Bc (allocBase (al f) cur) (allocBase (al f) cur + Bc) ec)
    (hrest : KidsAtF fs al cert k σ RN Pre (fun rd => O rd ∧ Oc rd) Dacc Qs cs ec e Oend Dend) :
    KidsAtF fs al cert k σ RN Pre O Dacc (PostQuiet :: Qs) (⟨f, args, rets, true⟩ :: cs) cur e Oend Dend := by
  refine kid_taken hR hc ?_
  have e : (fun i => Dacc i ∨ False) = Dacc := funext fun i ↦ or_false _
  rw [e]
  exact hrest

theorem plainRegion_ptr {a b n : ℕ} {R : ℕ → Prop} (h1 : ∀ t < 2 * n, R (a + t)) (h2 : ∀ t < n, R (b + t)) :
    VsC.PlainRegion (VsC.ptrAtV a) (VsC.ptrAtV b) n R :=
  ⟨fun t ht ↦ ⟨a + t, ptr_addr a t, h1 t ht⟩, fun t ht ↦ ⟨b + t, ptr_addr b t, h2 t ht⟩⟩

set_option maxHeartbeats 4000000 in
/-- **The closing calls**: the committed outputs' rounds, `verify_keccak_loop1`, the inputs'
rounds, their opening's, `verify_keccak_loop2`. -/
theorem kids_tail (h : D.Ok)
    (hRN : ∀ i, ((c ≤ i ∧ i < c + D.τ + 412) ∨ D.LinR curE chiE olE zvE slE i ∨
      (tbE ≤ i ∧ i < tbE + 2 ^ winTabBits)) → RN i)
    {ao ro a1 ai ri as' rs' a2 : List V}
    (hao : ao.map σ = D.oArgs curE zvE tbE) (hro : ro.map σ = D.oRets curE)
    (ha1 : a1.map σ = clArgs 0 (D.τ - 4) (zvE + 4) c)
    (hai : ai.map σ = D.iArgs curE zvE tbE) (hri : ri.map σ = D.iRets curE)
    (has : as'.map σ = D.sArgs curE zvE tbE) (hrs : rs'.map σ = D.sRets curE)
    (ha2 : a2.map σ = clArgs 0 (D.τ - 4) (zvE + 43) (D.lsP fs al cert k c curE tbE 11))
    (O : Reader → Prop) (Dacc : ℕ → Prop) (hW : ∀ rd, O rd → HoldsWords rd (D.WoP fs al cert k c curE tbE))
    (hO : ∀ rd, O rd → ∀ j < 12, D.LOut fs al cert k c curE tbE j rd)
    (hD : ∀ j < 12, ∀ i, VsC.klOwn (D.lsP fs al cert k c curE tbE j) (D.τ - 3) i → Dacc i) :
    KidsAtF fs al cert k σ RN (D.PreI curE chiE olE zvE slE tbE) O Dacc (List.replicate 5 PostQuiet)
      [⟨"keccak_plain_rounds__L6_L0", ao, ro, true⟩, ⟨name% «verify_keccak_loop1», a1, [], true⟩,
        ⟨"keccak_plain_rounds__L4_L1", ai, ri, true⟩, ⟨"keccak_plain_rounds__L6_L0", as', rs', true⟩,
        ⟨name% «verify_keccak_loop2», a2, [], true⟩]
      (D.q12 fs al cert k c curE tbE) (D.eF fs al cert k c curE tbE)
      (D.Oend fs al cert k c curE tbE) (D.Dend fs al cert k c curE tbE) := by
  have hτ1 := h.1
  have hτ2 := h.2.1
  have hxL := xs_len h
  have hoL := op_length h
  have hpL := point_length h
  have hq39 : qkeccakVarsCap = 39 := rfl
  have hmO : D.mO.length = 6 := h.2.2.2.2.2.2.1
  have hmI : D.mI.length = 4 := h.2.2.2.2.2.2.2.1
  have hmS : D.mS.length = 6 := h.2.2.2.2.2.2.2.2.1
  obtain ⟨l0, l1, l2, l3, l4, hL5⟩ := five_of_length' (L_ok h).2
  obtain ⟨o0, o1, o2, o3, o4, hO5⟩ := five_of_length' (O_ok h).2
  obtain ⟨i0, i1, i2, i3, i4, hI5⟩ := five_of_length' (I_ok h).2
  have hlin : ∀ i, D.LinR curE chiE olE zvE slE i → RN i ∨ Dacc i :=
    fun i hi ↦ Or.inl (hRN i (Or.inr (Or.inl hi)))
  have hcur : ∀ t, D.lcur 12 + t < D.xs.length → D.LinR curE chiE olE zvE slE (curE + D.lcur 12 + t) :=
    fun t ht ↦ Or.inl ⟨by omega, by omega⟩
  have hpt : ∀ t, t < D.point.length →
      D.LinR curE chiE olE zvE slE (zvE + qkeccakVarsCap + t) :=
    fun t ht ↦ Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))
  have hop : ∀ t, t < D.op.length → D.LinR curE chiE olE zvE slE (zvE + t) :=
    fun t ht ↦ Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))
  have hlc : D.lcur 12 + 97 = D.xs.length := hxL.symm
  have lc : ∀ {x y : ℕ}, D.LinR curE chiE olE zvE slE x → x = y → D.LinR curE chiE olE zvE slE y :=
    fun h e ↦ e ▸ h
  -- the point's parts
  have hpt3 : ∀ rd, ReadsAt rd (VsC.ptrAtV zvE * gen ^ qkeccakVarsCap) D.point →
      ReadsAt rd (VsC.ptrAtV zvE * gen ^ 39) D.I.1 ∧
      ReadsAt rd (VsC.ptrAtV (zvE + 43)) (D.L.1.point.take (D.τ - 4)) ∧
      ReadsAt rd (VsC.ptrAtV zvE * gen ^ 39 * gen ^ D.τ) D.S.1 := by
    intro rd hr
    rw [point, readsAt_append, readsAt_append] at hr
    obtain ⟨⟨r1, r2⟩, r3⟩ := hr
    rw [hq39] at r1 r2 r3
    refine ⟨r1, ?_, ?_⟩
    · rwa [I1_length h, ptr_mul_gen, ptr_mul_gen] at r2
    · rw [List.length_append, I1_length h, List.length_take, L_point h,
        show min (D.τ - 4) (D.τ - 3) = D.τ - 4 by omega, ptr_mul_gen, ptr_mul_gen] at r3
      rwa [ptr_mul_gen, ptr_mul_gen, show zvE + 39 + D.τ = zvE + 39 + (4 + (D.τ - 4)) by omega]
  simp only [List.replicate_succ, List.replicate_zero]
  -- the committed outputs' rounds
  have hrunO := O_run h 0
  rw [hL5] at hrunO
  refine kid_taken0 (Bc := fs "keccak_plain_rounds__L6_L0") (ec := D.eo fs al cert k c curE tbE)
    (Rc := D.LinR curE chiE olE zvE slE) (Oc := fun _ => True) hlin ?_ ?_
  · rw [hao, hro, oArgs, oRets, hL5]
    have hc := plain60_placed (fs := fs) (al := al) (cert := cert) (k := k) (f0 := l0) (f1 := l1) (f2 := l2)
      (f3 := l3) (f4 := l4) (p0 := 0) (p1 := 0) (cur := D.cL curE) (value := D.committed)
      (pt := VsC.ptrAtV zvE * gen ^ D.τ) (tabs := VsC.ptrAtV tbE) (w := 0) hmO
      (R := D.LinR curE chiE olE zvE slE)
      (by rw [cL, ptr_mul_gen]
          exact plainRegion_ptr (fun t ht ↦ hcur t (by omega))
            (fun t ht ↦ lc (hop (D.τ + t) (by omega)) (by omega)))
      (allocBase (al "keccak_plain_rounds__L6_L0") (D.q12 fs al cert k c curE tbE))
      (allocBase (al "keccak_plain_rounds__L6_L0") (D.q12 fs al cert k c curE tbE) + fs "keccak_plain_rounds__L6_L0")
    rw [VsC.plainRetsW, hrunO] at hc
    refine hc.mono (fun _ h ↦ h) (fun _ h ↦ h) (fun _ h ↦ h) (fun rd hpo ↦ ?_) (fun _ _ _ h ↦ h)
    obtain ⟨-, -, -, hcr, hzv, -⟩ := hpo.1
    refine ⟨(xs_reads h hcr).2.2.1, ?_⟩
    rw [hrunO]
    rw [op_eq] at hzv
    have := (readsAt_append.1 hzv).2
    rwa [List.take_append_drop, inst_length h] at this
  -- `verify_keccak_loop1`
  refine kid_taken0 (Bc := lpB fs name% «verify_keccak_loop1» (D.τ - 4) 0) (ec := D.e1 fs al cert k c curE tbE)
    (Rc := fun i => D.LinR curE chiE olE zvE slE i ∨ (c ≤ i ∧ i < c + D.τ + 412))
    (Oc := fun _ => True)
    (fun i hi ↦ hi.elim (fun h ↦ hlin i h) (fun h ↦ Or.inl (hRN i (Or.inl h)))) ?_ ?_
  · rw [ha1]
    have hc := VsC.cl_placed (fs := fs) (al := al) (cert := cert) (k := k) (name := name% «verify_keccak_loop1»)
      (by decide) (id := zvE + 4) (is := c) (l := D.inst.drop 4) (inst_drop_length h) (by omega) (by omega)
      (R := fun i => D.LinR curE chiE olE zvE slE i ∨ (c ≤ i ∧ i < c + D.τ + 412))
      ⟨fun i hi ↦ Or.inr ⟨by omega, by omega⟩, fun i hi ↦ Or.inl (lc (hop (4 + i) (by omega)) (by omega))⟩
      (allocBase (al name% «verify_keccak_loop1») (D.eo fs al cert k c curE tbE))
      (allocBase (al name% «verify_keccak_loop1») (D.eo fs al cert k c curE tbE) +
        lpB fs name% «verify_keccak_loop1» (D.τ - 4) 0)
    refine hc.mono (fun _ h ↦ h) (fun _ h ↦ h) (fun _ h ↦ h) (fun rd hpo ↦ ?_) (fun _ _ _ h ↦ h)
    obtain ⟨hp, ho⟩ := hpo
    obtain ⟨-, -, -, -, hzv, -⟩ := hp
    obtain ⟨m0, -⟩ := own_mem (hW rd ho.1)
    refine ⟨?_, ?_⟩
    · have := (readsAt_append.1 (show ReadsAt rd (VsC.ptrAtV c) (D.inst.drop 4 ++ D.seg) from m0)).1
      exact this
    · rw [op_eq] at hzv
      have := (readsAt_append.1 (readsAt_append.1 hzv).1).2
      rwa [List.length_take, inst_length h, show min 4 D.τ = 4 by omega, ptr_mul_gen] at this
  -- the inputs' rounds
  have hrunI := I_run h
  rw [hO5] at hrunI
  refine kid_taken0 (Bc := fs "keccak_plain_rounds__L4_L1") (ec := D.ei fs al cert k c curE tbE)
    (Rc := D.LinR curE chiE olE zvE slE) (Oc := fun _ => True) hlin ?_ ?_
  · rw [hai, hri, iArgs, iRets, hO5]
    have hc := plain41_placed (fs := fs) (al := al) (cert := cert) (k := k) (f0 := o0) (f1 := o1) (f2 := o2)
      (f3 := o3) (f4 := o4) (p0 := (Keccak.scalarCells D.word dsObserve).1)
      (p1 := (Keccak.scalarCells D.word dsObserve).2) (cur := D.cL curE * gen ^ (2 * 6) * gen)
      (value := D.L.1.value) (pt := VsC.ptrAtV zvE * gen ^ 39) (tabs := VsC.ptrAtV tbE) (w := D.word) rfl hmI
      (R := D.LinR curE chiE olE zvE slE)
      (by rw [cL, ptr_mul_gen, ptr_mul_gen1, ptr_mul_gen]
          exact plainRegion_ptr (fun t ht ↦ lc (hcur (13 + t) (by omega)) (by omega))
            (fun t ht ↦ by have := hpt t (by omega); rw [hq39] at this; exact lc this (by omega)))
      (allocBase (al "keccak_plain_rounds__L4_L1") (D.e1 fs al cert k c curE tbE))
      (allocBase (al "keccak_plain_rounds__L4_L1") (D.e1 fs al cert k c curE tbE) + fs "keccak_plain_rounds__L4_L1")
    rw [VsC.plainRetsW, hrunI] at hc
    refine hc.mono (fun _ h ↦ h) (fun _ h ↦ h) (fun _ h ↦ h) (fun rd hpo ↦ ?_) (fun _ _ _ h ↦ h)
    obtain ⟨-, -, -, hcr, -, hpp, -⟩ := hpo.1
    refine ⟨?_, by rw [hrunI]; exact (hpt3 rd hpp).1⟩
    rw [cL, ptr_mul_gen, ptr_mul_gen1]
    exact (xs_reads h hcr).2.2.2.2.1
  -- the inputs' opening's rounds
  have hrunS := S_run h 0
  rw [hI5] at hrunS
  refine kid_taken0 (Bc := fs "keccak_plain_rounds__L6_L0") (ec := D.es fs al cert k c curE tbE)
    (Rc := D.LinR curE chiE olE zvE slE) (Oc := fun _ => True) hlin ?_ ?_
  · rw [has, hrs, sArgs, sRets, hI5]
    have hc := plain60_placed (fs := fs) (al := al) (cert := cert) (k := k) (f0 := i0) (f1 := i1) (f2 := i2)
      (f3 := i3) (f4 := i4) (p0 := 0) (p1 := 0) (cur := D.cL curE * gen ^ (2 * 6) * gen * gen ^ (2 * 4))
      (value := D.I.2.1) (pt := VsC.ptrAtV zvE * gen ^ 39 * gen ^ D.τ) (tabs := VsC.ptrAtV tbE) (w := 0) hmS
      (R := D.LinR curE chiE olE zvE slE)
      (by rw [cL, ptr_mul_gen, ptr_mul_gen1, ptr_mul_gen, ptr_mul_gen, ptr_mul_gen]
          exact plainRegion_ptr (fun t ht ↦ lc (hcur (21 + t) (by omega)) (by omega))
            (fun t ht ↦ by have := hpt (D.τ + t) (by omega); rw [hq39] at this; exact lc this (by omega)))
      (allocBase (al "keccak_plain_rounds__L6_L0") (D.ei fs al cert k c curE tbE))
      (allocBase (al "keccak_plain_rounds__L6_L0") (D.ei fs al cert k c curE tbE) + fs "keccak_plain_rounds__L6_L0")
    rw [VsC.plainRetsW, hrunS] at hc
    refine hc.mono (fun _ h ↦ h) (fun _ h ↦ h) (fun _ h ↦ h) (fun rd hpo ↦ ?_) (fun _ _ _ h ↦ h)
    obtain ⟨-, -, -, hcr, -, hpp, -⟩ := hpo.1
    refine ⟨?_, by rw [hrunS]; exact (hpt3 rd hpp).2.2⟩
    rw [cL, ptr_mul_gen, ptr_mul_gen1, ptr_mul_gen]
    exact (xs_reads h hcr).2.2.2.2.2.1
  -- `verify_keccak_loop2`
  refine kid_taken0 (Bc := lpB fs name% «verify_keccak_loop2» (D.τ - 4) 0) (ec := D.eF fs al cert k c curE tbE)
    (Rc := fun i => D.LinR curE chiE olE zvE slE i ∨
      VsC.klOwn (D.lsP fs al cert k c curE tbE 11) (D.τ - 3) i)
    (Oc := fun _ => True)
    (fun i hi ↦ hi.elim (fun h ↦ hlin i h) (fun h ↦ Or.inr (hD 11 (by norm_num) i h)))
    ?_ ?_
  · rw [ha2]
    have hc := VsC.cl_placed (fs := fs) (al := al) (cert := cert) (k := k) (name := name% «verify_keccak_loop2»)
      (by decide) (id := zvE + 43) (is := D.lsP fs al cert k c curE tbE 11) (m := D.τ - 4)
      (l := D.L.1.point.take (D.τ - 4))
      (by rw [List.length_take, L_point h]; omega) (by omega) (by omega)
      (R := fun i => D.LinR curE chiE olE zvE slE i ∨
        VsC.klOwn (D.lsP fs al cert k c curE tbE 11) (D.τ - 3) i)
      ⟨fun i hi ↦ Or.inr ⟨by omega, by omega⟩,
        fun i hi ↦ Or.inl (by have := hpt (4 + i) (by omega); rw [hq39] at this; exact lc this (by omega))⟩
      (allocBase (al name% «verify_keccak_loop2») (D.es fs al cert k c curE tbE))
      (allocBase (al name% «verify_keccak_loop2») (D.es fs al cert k c curE tbE) +
        lpB fs name% «verify_keccak_loop2» (D.τ - 4) 0)
    refine hc.mono (fun _ h ↦ h) (fun _ h ↦ h) (fun _ h ↦ h) (fun rd hpo ↦ ?_) (fun _ _ _ h ↦ h)
    obtain ⟨hp, ho⟩ := hpo
    obtain ⟨-, -, -, -, -, hpp, -⟩ := hp
    refine ⟨?_, (hpt3 rd hpp).2.1⟩
    have hW' := hW rd ho.1.1.1.1
    obtain ⟨-, -, -, -, mo, -⟩ := own_mem hW'
    have hrec := mo 11 (by norm_num)
    have hcr := hO rd ho.1.1.1.1 11 (by norm_num) hrec
    obtain ⟨-, -, -, -, -, ⟨pp, hpp2, hptr⟩, -⟩ := hcr
    have e2 : pp = VsC.ptrAtV (D.lsP fs al cert k c curE tbE 11) := by
      have := readsAt_getD hrec (k := 2) (by rw [outWs_length]; norm_num)
      exact loadHolds_unique hpp2 (by simpa [outWs, VsC.klOutW] using this)
    rw [e2, ← L_next h] at hptr
    exact readsAt_take hptr _
  -- the end
  rw [KidsAtF]
  refine ⟨rfl, fun rd ho ↦ ⟨hW rd ho.1.1.1.1.1, hO rd ho.1.1.1.1.1⟩, fun i ⟨j, hj, hi⟩ ↦ ?_⟩
  exact hD j hj i hi

end VkData

end
end LeanVM.Guest.B1.VerifySub
