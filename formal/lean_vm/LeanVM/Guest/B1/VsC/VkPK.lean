/-
  LeanVM.Guest.B1.VsC.VkPK

  `verify_keccak` placed: calls carrying the honest words exist (`honest_exists`); a memory holding
  the callees' end words holds the layout (`mem_of_oend`); a call no memory satisfies completes.
-/

module

public import LeanVM.Guest.B1.VsC.VkPJ
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_keccak»

/-!
# Honest calls, the layout's memory

`honest_exists`: some valuation and calls carry the callees' honest words (each list at its own
block of indices), so `vk_kids`' placement exists whatever `verify_keccak`'s memory holds.
`mem_of_oend`: the caller's words and the callees' end words are the layout's memory (`Mem`).
`callAtA_vacuous`: a call whose precondition no memory satisfies completes, with no words.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.Memory LeanVM.Guest.B1.Fwd LeanVM.Guest.Complete
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr Finset LeanVM.Guest.B1.VerifySub.KL
open LeanVM.Prover.Exec (allocBase)

open LeanVM.Guest.B1.VsC (PostQuiet lpB clArgs plain60_placed plain41_placed)

@[expose] public section

/-- **A call no memory satisfies completes**, with no words. -/
theorem callAtA_vacuous {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k : ℕ}
    {f : String} {args rets : List E} {R D : ℕ → Prop} {Pre : Reader → Prop}
    {Post : Reader → Tree → Prop} {B fp c : ℕ} (h : ∀ rd, ¬ Pre rd) :
    CallAtA fs al cert k f args rets R D (fun _ => True) Pre Post B fp c c :=
  ⟨[], ⟨by simp, List.Pairwise.nil⟩, le_rfl, fun _ _ ↦ trivial, fun rd _ _ hp ↦ (h rd hp).elim⟩

/-- Values at a block of indices: list `m` at `1000 m`. -/
noncomputable def blockVal (spec : ℕ → List E) : Val := fun v => (spec (v.idx / 1000)).getD (v.idx % 1000) 0

/-- The indices of list `m`. -/
def blockVs (spec : ℕ → List E) (m : ℕ) : List V := (List.range (spec m).length).map fun i ↦ .n (1000 * m + i)

theorem blockVs_map {spec : ℕ → List E} {m : ℕ} (h : (spec m).length < 1000) :
    (blockVs spec m).map (blockVal spec) = spec m := by
  apply List.ext_getElem (by simp [blockVs])
  intro i h1 h2
  simp only [blockVs, List.map_map, List.getElem_map, List.getElem_range, Function.comp, blockVal]
  have hi : i < (spec m).length := by simpa [blockVs] using h1
  rw [show (1000 * m + i) / 1000 = m by omega, show (1000 * m + i) % 1000 = i by omega,
    List.getD_eq_getElem _ _ hi]

namespace VkData

variable {D : VkData} {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k : ℕ}
variable {c curE chiE olE zvE slE tbE : ℕ}

/-- The honest words of the calls, list by list. -/
noncomputable def spec (D : VkData) (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) (k : ℕ)
    (c curE zvE tbE chiE : ℕ) (m : ℕ) : List E :=
  if m = 0 then clArgs 0 (D.τ - 4) c (chiE + 4)
  else if m ≤ 24 then
    (if m % 2 = 1 then D.layArgs c curE tbE ((m - 1) / 2)
      else (D.layer ((m - 1) / 2)).rets (firstOf ((m - 1) / 2)) (VsC.ptrAtV (curE + D.lcur ((m - 1) / 2))))
  else if m = 25 then D.oArgs curE zvE tbE
  else if m = 26 then D.oRets curE
  else if m = 27 then clArgs 0 (D.τ - 4) (zvE + 4) c
  else if m = 28 then D.iArgs curE zvE tbE
  else if m = 29 then D.iRets curE
  else if m = 30 then D.sArgs curE zvE tbE
  else if m = 31 then D.sRets curE
  else clArgs 0 (D.τ - 4) (zvE + 43) (D.lsP fs al cert k c curE tbE 11)

theorem spec_length (h : D.Ok) (m : ℕ) : (D.spec fs al cert k c curE zvE tbE chiE m).length < 1000 := by
  have hL := (L_ok h).2
  have hO := (O_ok h).2
  have hI := (I_ok h).2
  have hS := (S_ok h).2
  unfold spec
  by_cases h0 : m = 0
  · simp [h0, clArgs]
  by_cases h24 : m ≤ 24
  · have hs : (m - 1) / 2 < 12 := by omega
    have hc := D.layer_cap h hs
    by_cases h1 : m % 2 = 1
    · simp [h0, h24, h1, layArgs, layerArgs, hc]
    · simp [h0, h24, h1, LayerData.rets, beta_cap_length]
  simp only [h0, h24, ↓reduceIte]
  split_ifs <;> simp [clArgs, oArgs, oRets, iArgs, iRets, sArgs, sRets, hL, hO, hI, hS]

/-- **Calls carrying the honest words exist.** -/
theorem honest_exists (h : D.Ok) :
    ∃ σ cs, D.HonestCalls fs al cert k c curE chiE zvE tbE σ cs := by
  set sp := D.spec fs al cert k c curE zvE tbE chiE with hsp
  have hb : ∀ m, (blockVs sp m).map (blockVal sp) = sp m := fun m ↦ blockVs_map (spec_length h m)
  refine ⟨blockVal sp, _, blockVs sp 0, fun s ↦ blockVs sp (1 + 2 * s), fun s ↦ blockVs sp (2 + 2 * s),
    blockVs sp 25, blockVs sp 26, blockVs sp 27, blockVs sp 28, blockVs sp 29, blockVs sp 30,
    blockVs sp 31, blockVs sp 32, rfl, ?_, fun s hs ↦ ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rw [hb, hsp, spec]
  all_goals try simp only [↓reduceIte, OfNat.ofNat_ne_zero, Nat.reduceLeDiff, Nat.reduceEqDiff,
    show ¬ (32 : ℕ) ≤ 24 by decide]
  · simp only [show 1 + 2 * s ≠ 0 by omega, show 1 + 2 * s ≤ 24 by omega, show (1 + 2 * s) % 2 = 1 by omega,
      show (1 + 2 * s - 1) / 2 = s by omega, ↓reduceIte]
  · simp only [show 2 + 2 * s ≠ 0 by omega, show 2 + 2 * s ≤ 24 by omega, show ¬ ((2 + 2 * s) % 2 = 1) by omega,
      show (2 + 2 * s - 1) / 2 = s by omega, ↓reduceIte]

variable {σ : Val} {RN : ℕ → Prop}

set_option maxHeartbeats 2000000 in
/-- **The callees complete one after the other** from `c + τ + 412`, on calls carrying their honest
words. -/
theorem vk_kids (hL : VsC.KeccakLayerCompleteA fs al cert k) (h : D.Ok)
    (hRN : ∀ i, ((c ≤ i ∧ i < c + D.τ + 412) ∨ D.LinR curE chiE olE zvE slE i ∨
      (tbE ≤ i ∧ i < tbE + 2 ^ winTabBits)) → RN i) {cs : List Call}
    (hH : D.HonestCalls fs al cert k c curE chiE zvE tbE σ cs) :
    KidsAtF fs al cert k σ RN (D.PreI curE chiE olE zvE slE tbE)
      (fun rd => HoldsWords rd (D.WoP fs al cert k c curE tbE)) (fun _ => False)
      (List.replicate 18 PostQuiet) cs (c + D.τ + 412) (D.eF fs al cert k c curE tbE)
      (D.Oend fs al cert k c curE tbE) (D.Dend fs al cert k c curE tbE) := by
  obtain ⟨a0, as, rs, ao, ro, a1, ai, ri, as', rs', a2, rfl, ha0, has, hao, hro, ha1, hai, hri, has',
    hrs', ha2⟩ := hH
  have hτ1 := h.1
  have hτ2 := h.2.1
  have hchis := h.2.2.1
  have hrep : List.replicate 18 (PostQuiet : Reader → Tree → Prop) =
      PostQuiet :: (List.replicate 12 PostQuiet ++ List.replicate 5 PostQuiet) := by simp [List.replicate]
  rw [hrep]
  refine kid_taken (Bc := lpB fs name% «verify_keccak_loop0» (D.τ - 4) 0) (ec := D.l0end fs al c)
    (Rc := fun i => D.LinR curE chiE olE zvE slE i ∨ (c ≤ i ∧ i < c + D.τ + 412))
    (Dc := fun _ => False) (Oc := fun _ => True)
    (fun i hi ↦ Or.inl (hi.elim (fun h ↦ hRN i (Or.inr (Or.inl h))) (fun h ↦ hRN i (Or.inl h)))) ?_ ?_
  · rw [ha0]
    have hc := VsC.cl_placed (fs := fs) (al := al) (cert := cert) (k := k) (name := name% «verify_keccak_loop0»)
      (by decide) (id := c) (is := chiE + 4) (l := D.inst.drop 4) (inst_drop_length h) (by omega) (by omega)
      (R := fun i => D.LinR curE chiE olE zvE slE i ∨ (c ≤ i ∧ i < c + D.τ + 412))
      ⟨fun i hi ↦ Or.inl (Or.inr (Or.inl ⟨by omega, by omega⟩)), fun i hi ↦ Or.inr ⟨by omega, by omega⟩⟩
      (D.l0fp al c) (D.l0end fs al c)
    refine hc.mono (fun _ h ↦ h) (fun _ h ↦ h) (fun _ h ↦ h) (fun rd ⟨hp, ho⟩ ↦ ?_) (fun _ _ _ h ↦ h)
    obtain ⟨-, hchi, -⟩ := hp
    obtain ⟨m0, -⟩ := own_mem ho
    refine ⟨?_, (readsAt_append.1 (show ReadsAt rd (VsC.ptrAtV c) (D.inst.drop 4 ++ D.seg) from m0)).1⟩
    have := (readsAt_append.1 (show ReadsAt rd (VsC.ptrAtV chiE) (D.chis.take 4 ++ D.chis.drop 4) by
      rwa [List.take_append_drop])).2
    rw [List.length_take, show min 4 D.chis.length = 4 by omega, ptr_mul_gen] at this
    have hd : D.inst.drop 4 = (D.chis.drop 4).take (D.τ - 4) := by
      rw [inst, List.drop_take]
    rw [hd]
    exact readsAt_take this _
  · have := kids_from (σ := σ) (RN := RN) hL h hRN (as := as) (rs := rs) has
      (tail := [⟨"keccak_plain_rounds__L6_L0", ao, ro, true⟩, ⟨name% «verify_keccak_loop1», a1, [], true⟩,
        ⟨"keccak_plain_rounds__L4_L1", ai, ri, true⟩, ⟨"keccak_plain_rounds__L6_L0", as', rs', true⟩,
        ⟨name% «verify_keccak_loop2», a2, [], true⟩]) (Qt := List.replicate 5 PostQuiet)
      (fun O Dacc hW hO hD ↦ kids_tail h hRN hao hro ha1 hai hri has' hrs' ha2 O Dacc hW hO hD)
      12 le_rfl (fun rd => HoldsWords rd (D.WoP fs al cert k c curE tbE) ∧ True) (fun i => False ∨ False)
      (fun rd h ↦ h.1) (fun _ _ j hj ↦ absurd hj (by omega)) (fun j hj ↦ absurd hj (by omega))
    have e0 : (D.posP fs al cert k c curE tbE 0).1 = D.l0end fs al c := rfl
    rw [e0] at this
    simpa [List.range_eq_range'] using this

/-- **The layout's memory**: the caller's words and the callees' end words. -/
theorem mem_of_oend {rd : Reader} (hP : D.PreI curE chiE olE zvE slE tbE rd)
    (hO : D.Oend fs al cert k c curE tbE rd) :
    D.Mem rd c curE chiE olE zvE slE tbE (D.lsP fs al cert k c curE tbE) := by
  obtain ⟨htb, hchi, hol, hcur, hzv, hpt, hsl⟩ := hP
  obtain ⟨hW, hL⟩ := hO
  obtain ⟨-, -, -, -, mo, -⟩ := own_mem hW
  exact ⟨hW, htb, hchi, hol, hcur, hzv, hpt, hsl, fun s hs ↦ hL s hs (mo s hs)⟩

end VkData

end
end LeanVM.Guest.B1.VerifySub
