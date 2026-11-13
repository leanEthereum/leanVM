/-
  LeanVM.Guest.Lift.Sig

  The signature verifiers' completeness in the uniform placed form (`CompleteAtD`), from B1's
  `Rel`-level completeness: they place nothing and call nothing, and their loads read the caller's
  words.
-/

module

public import LeanVM.Guest.Lift.SpWotsLeaf
public import LeanVM.Guest.B1.Sig.Interface
public import LeanVM.Guest.B1.Sig.XmssSegData
public import LeanVM.Guest.Lift.XmssLeaf

/-!
# The signature verifiers, placed

**`verify_lean_xmss`** is inline in `main_loop2`: its statements `xSeg` are a leaf block whose only
loads are the claim's four words at the pointer `.n 65` (`segLoad`, by the kernel on the data:
`xSeg_leafOk`; `loads_seg`), for the placed form of `main_loop2`.

**`sp_wots`** is a leaf body loading nothing (`spWots_leafOk`): with B1's completeness
(`sp_wots_complete_Spec`), on a memory defined below `2^6`, every honest call of it holds in any
region (`sp_wots_relIn`).

**`verify_sig_lean_sphincs`** calls `sp_wots` three times and loads the byte table through computed
pointers, so its loads are B1's (`verify_sig_lean_sphincs_complete_loads_Spec`: the claim's four
words and the table's 256), its body holding under the call relation `RelIn` of the region, which
holds of every honest call of `sp_wots`: with the claim and the table among the caller's words, on
a memory defined below `2^8`, it holds by a tree loading from them (`verify_sig_lean_sphincs_relIn`).
-/

namespace LeanVM.Guest.Lift

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B1 (LowDef Within CompleteAtD Returns disj_nil relAtIn_dmono)
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-! ## `verify_lean_xmss`, inline in `main_loop2` -/

/-- `xSeg`, `main_loop2`'s statements `9` to `321`. -/
theorem xSeg_length : B1.Sig.xSeg.length = 313 := by
  have h := congrArg List.length B1.Sig.loop2_split
  rw [main_loop2_length, List.length_append, List.length_append] at h
  have h9 : B1.Sig.l2Pre.length = 9 := rfl
  have h7 : B1.Sig.l2Post.length = 7 := rfl
  omega

theorem xSeg_eq_data : B1.Sig.xSeg = ((fn% «main_loop2»).body.drop 9).take 313 := by
  rw [B1.Sig.loop2_split, List.drop_left' (show B1.Sig.l2Pre.length = 9 from rfl),
    List.take_left' xSeg_length]

/-- **The check loads only the claim**: atoms, branches and arms, its loads the claim's words at
`.n 65`. -/
theorem xSeg_leafOk : Stmt.leafOkList segLoad B1.Sig.xSeg = true := by
  rw [xSeg_eq_data]; exact loop2Seg_leafOk

theorem loads_seg {σ : Val} {es : List Ev} (h : ∀ e ∈ es, EvLeafOk segLoad e) :
    ∀ A ∈ loadAddrs σ es, ∃ off < 4, A = (σ (.n 65)).limb 0 * addressOfIndex off := by
  intro A hA
  obtain ⟨e, he, hea⟩ := List.mem_filterMap.mp hA
  have hok := h e he
  cases e with
  | atom a =>
    cases a with
    | load d p off =>
      simp only [Ev.loadAddr?, Option.some.injEq] at hea
      simp only [EvLeafOk, segLoad, Bool.and_eq_true, decide_eq_true_eq] at hok
      exact ⟨off, hok.2, by rw [← hea, hok.1]⟩
    | _ => simp [Ev.loadAddr?] at hea
  | _ => simp [Ev.loadAddr?] at hea

/-! ## `sp_wots` -/

set_option maxRecDepth 100000 in
/-- **An honest call of `sp_wots` loads nothing**, from B1's completeness, in any region. -/
theorem sp_wots_relIn (hc : B1.Sig.sp_wots_complete_Spec) {rd : Reader} (R : ℕ → Prop)
    (hrd : B1.Sig.MemOK rd 64) : B1.Sig.SpWotsCalls (coreProgram.RelIn rd R) := by
  intro publicSeed layer tree leaf digest values hv
  obtain ⟨σ, h0, h12, h3, hb⟩ := hc (coreProgram.Rel rd) rd publicSeed layer tree leaf digest values
    hrd hv
  have h1 := congrArg Prod.fst h12
  have h2 := congrArg Prod.snd h12
  refine relIn_of_leaf B1.Sig.find_sp_wots spWots_leafOk (fun σ' es vs _ hw A hA => ?_)
    ((B1.Sig.rel_iff_body B1.Sig.find_sp_wots _ _).mpr
      ⟨σ, by rw [B1.Sig.sp_wots_params]; simp only at h1 h2; simp [h0, h1, h2, h3], hb⟩)
  have hall : (Out.ret es vs).All (EvLeafOk noLoad) := by
    have := walk_leafOk (σ := σ') (fn% «sp_wots»).body spWots_leafOk
    exact (show walk σ' (fn% «sp_wots»).body = .ret es vs from hw) ▸ this
  obtain ⟨e, he, hea⟩ := List.mem_filterMap.mp hA
  have hok := hall e he
  cases e with
  | atom a =>
    cases a with
    | load => simp [EvLeafOk, noLoad] at hok
    | _ => simp [Ev.loadAddr?] at hea
  | _ => simp [Ev.loadAddr?] at hea

/-! ## `verify_sig_lean_sphincs` -/

set_option maxRecDepth 100000 in
/-- **`verify_sig_lean_sphincs` loads only the claim and the byte table**, its calls of `sp_wots`
loading nothing, from B1's completeness with its loads. -/
theorem verify_sig_lean_sphincs_relIn (hc : B1.Sig.SphincsCompleteSpecs)
    {rd : Reader} {R : ℕ → Prop} {p bb : E} {pk : Sphincs.PublicKey} {m : HashSig.Message}
    {sig : Sphincs.Signature} (hrd : B1.Sig.MemOK rd 256) (hbb : B1.Sig.ByteBits rd bb)
    (hat : B1.Sig.ClaimAt rd p (B1.Sig.cellOf128 pk.publicSeed) (B1.Sig.cellOf128 pk.root)
      (B1.Sig.cellOf128 (m.extractLsb' 0 128)) (B1.Sig.cellOf128 (m.extractLsb' 128 128)))
    (hv : Sphincs.verifyWithKeccak pk m sig = true)
    (hreg : ∀ k < 4, ∃ i, p.limb 0 * addressOfIndex k = addressOfIndex i ∧ R i)
    (hregb : ∀ v < 256, ∃ i, bb.limb 0 * addressOfIndex v = addressOfIndex i ∧ R i) :
    coreProgram.RelIn rd R "verify_sig_lean_sphincs" [p, bb] [] := by
  obtain ⟨σ, h0, h1, hb, hloads⟩ := hc.verify (coreProgram.RelIn rd R) rd p bb pk m sig
    (sp_wots_relIn hc.sp_wots R fun i hi => hrd i (by omega)) hrd hbb hat hv
  have hsat := walk_sat (P := coreProgram) (fn% «verify_sig_lean_sphincs»).body
    (coreProgram_wf _ (List.mem_of_find?_eq_some B1.Sig.find_verify_sig_lean_sphincs)) hb
  cases hw : walk σ (fn% «verify_sig_lean_sphincs»).body with
  | fall es => rw [hw] at hsat; exact hsat.2.elim
  | stuck => rw [hw] at hsat; exact hsat.elim
  | ret es vs =>
    rw [hw] at hsat
    obtain ⟨hok, hr⟩ := hsat
    refine relIn_of_walk coreProgram_wf B1.Sig.find_verify_sig_lean_sphincs
      (by rw [B1.Sig.verify_sig_lean_sphincs_params]; simp [h0, h1]) hw hr (fun e he ↦ (hok e he).1)
      (fun A hA ↦ ?_) (fun c hc ht ↦ ?_)
    · rcases hloads es vs hw A hA with ⟨k, hk, rfl⟩ | ⟨v, hv', rfl⟩
      · exact hreg k hk
      · exact hregb v hv'
    · obtain ⟨e, he, hec⟩ := List.mem_filterMap.mp hc
      cases e with
      | call f args rets =>
        simp only [Ev.call?, Option.some.injEq] at hec
        subst hec
        exact (hok _ he).2 f args rets rfl
      | skip f args =>
        simp only [Ev.call?, Option.some.injEq] at hec
        subst hec
        cases ht
      | _ => simp [Ev.call?] at hec

end
end LeanVM.Guest.Lift
