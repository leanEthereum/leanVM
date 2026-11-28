/-
  LeanVM.Guest.CoreMode.Fn.keccak_layer.SoundA

  `keccak_layer`'s own routing facts, sound at the honest instances of b2c's aligned tree: its two dispatches'
  returned cursors (`OwnOkA`, its family `retEqs`).
-/

module

public import LeanVM.Guest.CoreMode.Fn.keccak_layer.Fam
public import LeanVM.Guest.EndExecCoreResA
public import LeanVM.Guest.CoreMode.Fam.MonoChain
public import LeanVM.Guest.CoreMode.Fam.ProgOkG
public import LeanVM.Guest.B1.KeccakGkr.LayerHolds
public import LeanVM.Guest.B1.KeccakGkr.LayerRounds
public import LeanVM.Guest.CoreMode.Fn.keccak_layer.KlCarry

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.VerifySub
open LeanVM.Guest.Value (gen_pow_eq_ofK)
open LeanVM.Protocol.Verifier (gen)

public section

variable {al : String → Bool} {D : Ref → RefD} {r : Ref}

/-- **A `layer_rounds__L{n}` call's returned cursor** (`layer_rounds_sound`): its cursor argument `·g^(2n)`. -/
theorem lrCall_cur {rd : Reader} {n : ℕ} (hn : n ≤ 16) {σ : Val} {b : ℕ} {args : List E} (hl : args.length = 10)
    (h : coreProgram.Rel rd (lrNames.getD n "") args ((List.range 7).map fun k ↦ σ (.n (b + k)))) :
    σ (.n (b + 5)) = args.getD 5 0 * gen ^ (2 * n) := by
  match args, hl with
  | [f0, f1, f2, f3, f4, cur, v, pp, pt, tabs], _ =>
    have hm := layer_rounds_sound n hn rd _ _ h
    simp only [MeaningLayerRounds] at hm
    obtain ⟨rs, ms, -, -, -, -, -, -, hr⟩ := hm
    have hc : (packRunF rs ms v ⟨[f0, f1, f2, f3, f4], []⟩).2.cap.length = 5 := by
      have := congrArg List.length hr
      simp at this
      omega
    have h5 := congrArg (fun l ↦ l.getD 5 0) hr
    rw [List.getD_append_right _ _ _ _ (by omega), hc] at h5
    simpa using h5

set_option maxHeartbeats 4000000 in
/-- **`keccak_layer`'s returned cursors** at an honest instance: the dispatch on `step_g` returns
`cursor·step_g^32·g^48`, the one on `rem_g` that times `rem_g^2` (`packT_holds`, `lrCall_cur`). -/
theorem kl_retCur {first : ℕ} (hf : first < 2) (hR : RefH (layB al) (D r) r) {I : Inst} (hI : I ∈ instsR al D r)
    {σ : Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node (layerName first) σ bufs kids) :
    σ (.n (preOff first + 790)) = σ (.n 7) * σ (.n 9) ^ 32 * gen ^ 48 ∧
      σ (.n (preOff first + 803)) = σ (.n 7) * σ (.n 9) ^ 32 * σ (.n 10) ^ 2 * gen ^ 48 := by
  obtain ⟨args, rets, hvI⟩ := inst_validA hR hI ht
  have hfb : ∃ fn, coreProgram.find? (layerName first) = some fn ∧ fn.body = layerT first := by
    interval_cases first
    · exact ⟨_, find_layer265, layer_body265⟩
    · exact ⟨_, find_layer264, layer_body264⟩
  obtain ⟨fn, hfn, hbody⟩ := hfb
  obtain ⟨-, hb⟩ := Res.holds_of_valid Res.fs_pos hvI hfn
  rw [hbody, layerT] at hb
  rw [holdsList_append, holdsList_append, holdsList_append, holdsList_append, holdsList_append,
    holdsList_append, holdsList_append, holdsList_append] at hb
  replace hb := ((holdsList_atoms (allAtoms_of_all (by interval_cases first <;> decide +kernel)) _ _).1 hb).2
  replace hb := ((holdsList_atoms (allAtoms_of_all (rmfeBlock_atoms _)) _ _).1 hb).2
  replace hb := ((holdsList_atoms (allAtoms_of_all (by interval_cases first <;> decide +kernel)) _ _).1 hb).2
  obtain ⟨-, ⟨j1, hj1, hsg, hc1⟩, ⟨j2, hj2, hrg, hc2⟩, -, -⟩ := packT_holds hb
  generalize preOff first = o at hc1 hc2 ⊢
  have hn1 : stepNames.getD j1 "" = lrNames.getD (16 * j1) "" := by interval_cases j1 <;> rfl
  have hn2 : remNames.getD j2 "" = lrNames.getD j2 "" := by interval_cases j2 <;> rfl
  have h1 := hc1.rel
  rw [hn1] at h1
  have e1 := lrCall_cur (by omega) (by simp [cap5]) h1
  have h2 := hc2.rel
  rw [hn2] at h2
  have e2 := lrCall_cur (by omega) (by simp) h2
  simp only [cap5, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.getD_cons_succ,
    List.getD_cons_zero] at e1
  rw [List.getD_append _ _ _ _ (by simp), show (List.range 7).map (fun k ↦ σ (.n (o + 785 + k))) =
    [σ (.n (o + 785 + 0)), σ (.n (o + 785 + 1)), σ (.n (o + 785 + 2)), σ (.n (o + 785 + 3)), σ (.n (o + 785 + 4)),
      σ (.n (o + 785 + 5)), σ (.n (o + 785 + 6))] from rfl] at e2
  simp only [List.getD_cons_succ, List.getD_cons_zero] at e2
  rw [show o + 785 + 5 = o + 790 by omega] at e1 e2
  rw [show o + 798 + 5 = o + 803 by omega] at e2
  have hs : σ (.n 9) ^ 32 = gen ^ (2 * (16 * j1)) := by rw [hsg, ← pow_mul]; ring_nf
  have hr : σ (.n 10) ^ 2 = gen ^ (2 * j2) := by rw [hrg, ← pow_mul]; ring_nf
  refine ⟨?_, ?_⟩
  · rw [e1, hs]; ring
  · rw [e2, e1, hs, hr]; ring

end

end LeanVM.Guest.EndExec

namespace LeanVM.Guest.CoreMode.Own.keccak_layer

open LeanVM.Parameters LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.EndExec
open LeanVM.Guest.Value (gen_pow_eq_ofK)

public section

/-- **Its point length holds** at an honest instance (`klQ_allA`). -/
theorem ygFam_holds {al : String → Bool} {D : Ref → RefD} {r : Ref} (hR : RefH (layB al) (D r) r) (hr : r.Ok)
    {I : Memory.Inst} (hI : I ∈ instsR al D r) {f : String} {σ : Val} {bufs : List ℕ} {kids : List Memory.Tree}
    (ht : I.t = .node f σ bufs kids) (hf : f = name% «keccak_layer__L0» ∨ f = name% «keccak_layer__L1») {x : CRes}
    (hx : ygFam x = true) : x.Holds σ := by
  obtain ⟨y, s, hy, hs, h8, h9, heq⟩ := klQ_allA hR hr I hI f σ bufs kids ht hf
  have hof : ofK (1 : K) = 1 := map_one (algebraMap K E)
  simp only [ygFam, Bool.or_eq_true, decide_eq_true_eq] at hx
  rcases hx with rfl | hx
  · show CCell.valW _ _ = CCell.valW _ _
    simp only [CCell.valW, prodW, vw, pow_one, mul_one, pow_zero]
    rw [heq, hof]
  · split at hx
    · rename_i n
      simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hx
      exact ltF_of_pow (e := y) hx.2 (by omega) (by rw [h8, gen_pow_eq_ofK])
    · rename_i c n
      simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, decide_eq_true_eq] at hx
      obtain ⟨⟨rfl, h32⟩, hn⟩ := hx
      refine ⟨16 * s, n, ?_, CoreMode.rep_const hn, by omega⟩
      simp only [idxC, CCell.valW, prodW, vw, mul_one, pow_zero]
      rw [h9, hof, mul_one, ← pow_mul, show s * 16 = 16 * s by ring, gen_pow_eq_ofK]
      exact CoreMode.rep_of (by unfold CoreMode.capE; omega)
    · cases hx

/-- **Its family** (`kl_retCur`, `ygFam_holds`), aligned. -/
theorem fams_okA {al : String → Bool} {D : Ref → RefD} : ∀ c ∈ fams, OwnOkA al D c := by
  intro c hc r hR hr I hI σ bufs kids ht fn hf x hx
  have hof : ofK (1 : K) = 1 := map_one (algebraMap K E)
  simp only [fams, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · simp only [Bool.or_eq_true] at hx
    rcases hx with hx | hx
    swap
    · exact ygFam_holds hR hr hI ht (Or.inl rfl) hx
    obtain ⟨e1, e2⟩ := kl_retCur (first := 0) (by decide) hR hI ht
    simp only [decide_eq_true_eq, retEqs, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · show CCell.valW _ _ = CCell.valW _ _
      simp only [CCell.valW, prodW, vw, pow_one, mul_one, ← gen_pow_eq_ofK, pow_zero]
      rw [show (0 : ℕ) + 790 = B1.VerifySub.preOff 0 + 790 from rfl, e1, hof]
      ring
    · show CCell.valW _ _ = CCell.valW _ _
      simp only [CCell.valW, prodW, vw, pow_one, mul_one, ← gen_pow_eq_ofK, pow_zero]
      rw [show (0 : ℕ) + 803 = B1.VerifySub.preOff 0 + 803 from rfl, e2, hof]
      ring
  · simp only [Bool.or_eq_true] at hx
    rcases hx with hx | hx
    swap
    · exact ygFam_holds hR hr hI ht (Or.inr rfl) hx
    obtain ⟨e1, e2⟩ := kl_retCur (first := 1) (by decide) hR hI ht
    simp only [decide_eq_true_eq, retEqs, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · show CCell.valW _ _ = CCell.valW _ _
      simp only [CCell.valW, prodW, vw, pow_one, mul_one, ← gen_pow_eq_ofK, pow_zero]
      rw [show (20 : ℕ) + 790 = B1.VerifySub.preOff 1 + 790 from rfl, e1, hof]
      ring
    · show CCell.valW _ _ = CCell.valW _ _
      simp only [CCell.valW, prodW, vw, pow_one, mul_one, ← gen_pow_eq_ofK, pow_zero]
      rw [show (20 : ℕ) + 803 = B1.VerifySub.preOff 1 + 803 from rfl, e2, hof]
      ring

end

end LeanVM.Guest.CoreMode.Own.keccak_layer
