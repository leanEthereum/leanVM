/-
  LeanVM.Guest.CoreMode.Fn.ring_rows.SoundA

  `ring_rows`'s own family, sound at the honest instances of b2c's aligned tree (`OwnOkA`): its split.
-/

module

public import LeanVM.Guest.EndExecCoreResA
public import LeanVM.Guest.EndExecCoreSplit
public import LeanVM.Guest.B1.Eq.RingRows
public import LeanVM.Guest.CoreMode.Fn.ring_rows.Fam
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«ring_rows»

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.CoreMode (CRes CCond CCell CRun CIdx LtF rep_of capE idxC vw prodW SplitC powB splitRes)
open LeanVM.Protocol.Verifier (gen)

public section

/-- A block of atoms holding gives what follows it. -/
theorem holdsList_atoms {C : CallRel} {rd : Reader} {σ : Val} :
    ∀ (xs : List Stmt) {next : Prop} {kret : List E → Prop},
      xs.all (fun s ↦ match s with | .atom _ => true | _ => false) = true → Stmt.HoldsList C rd σ xs next kret → next
  | [], _, _, _, h => h
  | .atom _ :: xs, _, _, hx, h => holdsList_atoms xs (by simpa using hx) h.2
  | .ite .. :: _, _, _, hx, _ | .match_ .. :: _, _, _, hx, _ | .ret .. :: _, _, _, hx, _
  | .call .. :: _, _, _, hx, _ | .callIf .. :: _, _, _, hx, _ | .dispatch .. :: _, _, _, hx, _ => by simp at hx

/-- **`ring_rows`' split** (`spRg`): its count `q^8·r_g@3`, `q = q_g@1·q_g@2~3·q_g@3~3`,
`r_g@3 = r_g@1·r_g@2~3·r_g@3~3`. -/
theorem splitW_rg : SplitW (fn% «ring_rows»)
    ⟨[(val% «ring_rows» "q_g@1", 1), (val% «ring_rows» "q_g@2~3", 1), (val% «ring_rows» "q_g@3~3", 1)],
    [(val% «ring_rows» "r_g@1", 1), (val% «ring_rows» "r_g@2~3", 1), (val% «ring_rows» "r_g@3~3", 1)], val% «ring_rows» "r_g@3", val% «ring_rows» "count_g", 8, 8⟩ := by
  intro rd σ es vs hw hev
  obtain ⟨w3, w5, w17⟩ := B1.rs_consts
  have h : Stmt.HoldsList (fun _ _ _ => True) rd σ (fn% «ring_rows»).body False (fun _ => True) :=
    holdsList_of_walk _ (by rw [hw]; exact ⟨fun e he => ⟨hev e he, fun _ _ _ _ => trivial⟩, trivial⟩)
  rw [B1.ring_rows_body, B1.rgBody, holdsList_append] at h
  replace h := holdsList_atoms _ (by decide +kernel) h
  simp only [B1.rgA, List.cons_append, List.nil_append, Stmt.HoldsList, Stmt.Holds, Atom.Holds, true_and] at h
  obtain ⟨b0, h10, h11, h12, h13, b1, h14, h15, h16, h17, h18, b2, h19, h20, h21, h22, h23,
    b3, h24, h25, h26, h27, b4, h28, h29, h30, h31, h32, b5, h33, h34, h35, h36, h37, h38, h39,
    h40, h41, ha, -⟩ := h
  have hlo : ∀ j < 3, σ (.n (val% «ring_rows» "bits[0]" + j)) * σ (.n (val% «ring_rows» "bits[0]" + j)) = σ (.n (val% «ring_rows» "bits[0]" + j)) := by
    intro j hj; interval_cases j
    exacts [b0.symm, b1.symm, b2.symm]
  have hhi : ∀ j < 3, σ (.n (val% «ring_rows» "bits[3]" + j)) * σ (.n (val% «ring_rows» "bits[3]" + j)) = σ (.n (val% «ring_rows» "bits[3]" + j)) := by
    intro j hj; interval_cases j
    exacts [b3.symm, b4.symm, b5.symm]
  have rg : σ (.n (val% «ring_rows» "r_g@3")) = ∏ j ∈ Finset.range 3, (1 + σ (.n (val% «ring_rows» "bits[0]" + j)) * (gen ^ 2 ^ j + 1)) := by
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
    rw [h23, h18, h13, h17, h22, h12, h16, h21, h10, h14, h19, h11, h15, h20, w3, w5, w17, B1.word_one]
  have qg : σ (.n (val% «ring_rows» "q_g@3")) = ∏ j ∈ Finset.range 3, (1 + σ (.n (val% «ring_rows» "bits[3]" + j)) * (gen ^ 2 ^ j + 1)) := by
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
    rw [h37, h32, h27, h31, h36, h26, h30, h35, h24, h28, h33, h25, h29, h34, w3, w5, w17, B1.word_one]
  obtain ⟨bb, hbb, hb⟩ := split_bits_gpow (b := fun j ↦ σ (.n (val% «ring_rows» "bits[0]" + j))) hlo
  obtain ⟨aa, haa, hab⟩ := split_bits_gpow (b := fun j ↦ σ (.n (val% «ring_rows» "bits[3]" + j))) hhi
  replace rg := rg.trans hb
  replace qg := qg.trans hab
  have h3 : σ (.n (val% «ring_rows» "count_g")) = gen ^ (8 * aa + bb) := by
    rw [← Value.e_add_eq_zero_iff.mp ha, h41, h40, h39, h38, qg, rg, pow_add, pow_mul']
    ring
  have haa' : aa < 8 := by simpa using haa
  have hbb' : bb < 8 := by simpa using hbb
  refine ⟨aa, bb, ⟨haa', hbb', show 8 * aa + bb < capE by unfold capE; omega, ?_, ?_, rg, h3⟩⟩
  · simp only [CoreMode.prodW, vw, pow_one, mul_one]
    rw [← qg, h37, h32, mul_assoc]
  · simp only [CoreMode.prodW, vw, pow_one, mul_one]
    rw [← rg, h23, h18, mul_assoc]

end

end LeanVM.Guest.EndExec

namespace LeanVM.Guest.CoreMode.Own.ring_rows

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.EndExec
open LeanVM.Protocol.Verifier (gen)

public section

/-- **Its family**, aligned: its split's residuals (`splitRes_instA`, `splitW_rg`). -/
theorem fams_okA {al : String → Bool} {D : Ref → RefD} : ∀ c ∈ fams, OwnOkA al D c := by
  simp only [fams, List.mem_cons, List.not_mem_nil, or_false, forall_eq]
  intro r hR hr I hI σ bufs kids ht fn hf x h
  have hw : SplitW fn CoreMode.spRg := by
    rw [B1.find_ring_rows] at hf
    obtain rfl := Option.some.inj hf
    exact splitW_rg
  exact splitRes_instA hR hI ht hf hw h

end

end LeanVM.Guest.CoreMode.Own.ring_rows
