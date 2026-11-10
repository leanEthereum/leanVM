/-
  LeanVM.Guest.B1.KeccakGkr.VkCU

  `verify_keccak`'s frames match its callees as it places them.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.VkCT

/-!
# The frames

`calls_match`: on the layout, the eighteen frames the body sets up are the callees `D.kids` at
the frame pointers `fps`: their names, whether entered, their arguments, and their returns are
what the callees return.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.Memory LeanVM.Guest.B1.Fwd
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr Finset
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

namespace VkData

variable {D : VkData} {rd : Reader} {B curE chiE olE zvE slE tbE : ℕ} {fs : String → ℕ}
  {fps : List ℕ}

theorem gen_ne (h : D.Ok) : 1 + gen ^ (D.τ - 4) ≠ 0 :=
  gen_pow_ne_one (by have := h.1; omega) (by have := h.2.1; unfold ordG; omega)

/-- **Layer `s`'s frame matches its callee.** -/
theorem layer_match (h : D.Ok) (hm : D.Mem rd B curE chiE olE zvE slE tbE (D.lsOf fs fps)) {σ : Val}
    (hσd : σ = D.val rd B curE chiE olE zvE slE tbE) {s : ℕ} (hs : s < 12)
    {o : List E × Main.Layout}
    (ho : (D.layKid fs B curE tbE s).Out ([] ++ fps.take (s + 1 + 1)) o.1 o.2) :
    (Main.mkCall σ (stepCall s)).f = (D.layKid fs B curE tbE s).f ∧
      (Main.mkCall σ (stepCall s)).taken = (D.layKid fs B curE tbE s).taken ∧
      ((D.layKid fs B curE tbE s).taken = true →
        (Main.mkCall σ (stepCall s)).args.map σ =
          (D.layKid fs B curE tbE s).args ([] ++ fps.take (s + 1)) ∧
        (Main.mkCall σ (stepCall s)).rets.map σ = o.1) := by
  obtain ⟨hf, ha, hr⟩ := layer_call h hm hσd hs fs ([] ++ fps.take (s + 1))
  have hc : stepCall s = (none, (stepCall s).2.1, (stepCall s).2.2.1,
      (stepCall s).2.2.2) := by
    unfold stepCall; split <;> rfl
  rw [hc]
  refine ⟨hf, rfl, fun _ ↦ ⟨ha, ?_⟩⟩
  rw [ho.1]
  exact hr

set_option maxRecDepth 20000 in
/-- **The frames match the callees.** -/
theorem calls_match (h : D.Ok) (hm : D.Mem rd B curE chiE olE zvE slE tbE (D.lsOf fs fps))
    {σ : Val} (hσd : σ = D.val rd B curE chiE olE zvE slE tbE) (hfl : fps.length = 18)
    {outs : List (List E × Main.Layout)}
    (hout : OutsOk (atAllG [] (D.kids fs B curE chiE olE zvE slE tbE) fps) outs) :
    CallsMatch σ ((vkPre.filterMap (Stmt.callSF σ)).map (Main.mkCall σ))
      (atAllG [] (D.kids fs B curE chiE olE zvE slE tbE) fps) outs := by
  obtain ⟨-, -, p6, -, -, p9, p10, h17, -, -, a58, e60, e61, e63, -, -, -, -, e191, -, a201, -,
    a274, -, -⟩ := head_first h hm hσd
  obtain ⟨eL, e3690, e3691, e3692, e3693, eO, -, cellsW, e3971, e3972, e3974, -⟩ :=
    out_on h hm hσd p6 p9 h17 a58 a274
  have e3699 : σ (.n 929) = ptr (curE + D.lcur 12 + 12) := by
    have := eO 5 (by norm_num)
    rw [this, oRets, List.getD_append_right _ _ _ _ (by rw [(O_ok h).2]), (O_ok h).2]
    simp [cL, ptr_mul_gen]
  obtain ⟨e3976, e3977, e3979, eI, e4104, e4107, e4108, e4109, eS, -, -, -⟩ :=
    in_on h hm hσd p6 p9 p10 a201 e3699
  have e4116 : σ (.n 1339) = D.S.2.1 := by
    rw [show (1339 : ℕ) = 1333 + 6 from rfl, eS 6 (by norm_num), sRets,
      List.getD_append_right _ _ _ _ (by rw [(S_ok h).2]; norm_num), (S_ok h).2]
    rfl
  obtain ⟨e4977, e6580, e6581, e6583, -⟩ :=
    fin_on h hm hσd p9 p10 h17 a201 e4104 e4107 e4116 e3979
  have p11 : σ (.n 11) = ptr tbE := by rw [hσd]; exact val_tabs h
  rw [vkPre_callSF]
  obtain ⟨hol, hoi⟩ := outsOk_getElem hout
  have hk : (D.kids fs B curE chiE olE zvE slE tbE).length = 18 := kids_length
  have hlen : (atAllG [] (D.kids fs B curE chiE olE zvE slE tbE) fps).length = 18 := by
    rw [atAllG_length, hk, hfl]; rfl
  have hoi2 : ∀ i (hi : i < 18) (ho : i < outs.length),
      ((D.kids fs B curE chiE olE zvE slE tbE)[i]'(by omega)).taken = true →
      ((D.kids fs B curE chiE olE zvE slE tbE)[i]'(by omega)).Out ([] ++ fps.take (i + 1))
        (outs[i]'ho).1 (outs[i]'ho).2 := by
    intro i hi ho ht
    have := hoi i (by rw [atAllG_length, hk, hfl]; omega) ho (by rw [atAllG_getElem]; exact ht)
    rwa [atAllG_getElem] at this
  have mr : ∀ {b n : ℕ} {L : List E}, L.length = n → (∀ j < n, σ (.n (b + j)) = L.getD j 0) →
      ((List.range n).map fun j ↦ V.n (b + j)).map σ = L := by
    intro b n L hL hj
    apply List.ext_getElem (by simp [hL])
    intro j h1 h2
    simp only [List.length_map, List.length_range] at h1
    simp only [List.getElem_map, List.getElem_range]
    rw [hj j h1, List.getD_eq_getElem _ _ h2]
  have hoc : ∀ j < 5, σ (.n (924 + j)) = D.O.2.2.cap.getD j 0 := fun j hj ↦ by
    rw [eO j (by omega), oRets, List.getD_append _ _ _ _ (by rw [(O_ok h).2]; exact hj)]
  have hic : ∀ j < 5, σ (.n (1203 + j)) = D.I.2.2.cap.getD j 0 := fun j hj ↦ by
    rw [eI j (by omega), iRets, List.getD_append _ _ _ _ (by rw [(I_ok h).2]; exact hj)]
  apply callsMatch_ofI (by rw [hlen]; simp [vkCalls]) hol (fun i hi hc ho ↦ ?_)
  rw [hlen] at hi
  rw [List.getElem_map, atAllG_getElem]
  interval_cases i
  · refine ⟨rfl, ?_, fun _ ↦ ⟨?_, ?_⟩⟩
    · show decide (σ (.n 63) ≠ 0) = true
      rw [e60]; exact decide_eq_true (gen_ne h)
    · show [σ (.n 64), σ (.n 18), σ (.n 61), σ (.n 66)] = [1, gen ^ (D.τ - 4), ptr B, ptr chiE * gen ^ 4]
      rw [e61, h17, a58, e63]
    · exact ((hoi2 0 (by norm_num) ho rfl).1).symm
  · exact layer_match h hm hσd (s := 0) (by norm_num) (hoi2 1 (by omega) ho rfl)
  · exact layer_match h hm hσd (s := 1) (by norm_num) (hoi2 2 (by omega) ho rfl)
  · exact layer_match h hm hσd (s := 2) (by norm_num) (hoi2 3 (by omega) ho rfl)
  · exact layer_match h hm hσd (s := 3) (by norm_num) (hoi2 4 (by omega) ho rfl)
  · exact layer_match h hm hσd (s := 4) (by norm_num) (hoi2 5 (by omega) ho rfl)
  · exact layer_match h hm hσd (s := 5) (by norm_num) (hoi2 6 (by omega) ho rfl)
  · exact layer_match h hm hσd (s := 6) (by norm_num) (hoi2 7 (by omega) ho rfl)
  · exact layer_match h hm hσd (s := 7) (by norm_num) (hoi2 8 (by omega) ho rfl)
  · exact layer_match h hm hσd (s := 8) (by norm_num) (hoi2 9 (by omega) ho rfl)
  · exact layer_match h hm hσd (s := 9) (by norm_num) (hoi2 10 (by omega) ho rfl)
  · exact layer_match h hm hσd (s := 10) (by norm_num) (hoi2 11 (by omega) ho rfl)
  · exact layer_match h hm hσd (s := 11) (by norm_num) (hoi2 12 (by omega) ho rfl)
  · refine ⟨rfl, rfl, fun _ ↦ ⟨?_, ?_⟩⟩
    · show [σ (.n 915), σ (.n 916), σ (.n 917), σ (.n 918), σ (.n 919), σ (.n 922),
        σ (.n 923), σ (.n 920), σ (.n 158), σ (.n 921), σ (.n 11)] = D.oArgs curE zvE tbE
      rw [oArgs, ← eL, e3692, e3693, e3690, e191, e3691, p11]; rfl
    · rw [(hoi2 13 (by norm_num) ho rfl).1]
      exact mr (by simp [oRets, (O_ok h).2]) eO
  · refine ⟨rfl, ?_, fun _ ↦ ⟨?_, ?_⟩⟩
    · show decide (σ (.n 1194) ≠ 0) = true
      rw [e3971]; exact decide_eq_true (gen_ne h)
    · show [σ (.n 1195), σ (.n 18), σ (.n 1197), σ (.n 61)] =
        [1, gen ^ (D.τ - 4), ptr zvE * gen ^ 4, ptr B]
      rw [e3972, h17, e3974, a58]
    · exact ((hoi2 14 (by norm_num) ho rfl).1).symm
  · refine ⟨rfl, rfl, fun _ ↦ ⟨?_, ?_⟩⟩
    · show [σ (.n 924), σ (.n 925), σ (.n 926), σ (.n 927), σ (.n 928), σ (.n 932),
        σ (.n 933), σ (.n 1199), σ (.n 1200), σ (.n 1202), σ (.n 11)] = D.iArgs curE zvE tbE
      have hc5 : [σ (.n 924), σ (.n 925), σ (.n 926), σ (.n 927), σ (.n 928)] = D.O.2.2.cap :=
        mr (b := 924) (n := 5) (O_ok h).2 hoc
      rw [iArgs, ← hc5, ← cellsW, e3976, e3977, e3979, cL, p11]
      simp only [ptr_mul_gen, ptr_mul_gen1, List.cons_append, List.nil_append]
    · rw [(hoi2 15 (by norm_num) ho rfl).1]
      exact mr (by simp [iRets, (I_ok h).2]) eI
  · refine ⟨rfl, rfl, fun _ ↦ ⟨?_, ?_⟩⟩
    · show [σ (.n 1203), σ (.n 1204), σ (.n 1205), σ (.n 1206), σ (.n 1207), σ (.n 1331),
        σ (.n 1332), σ (.n 1208), σ (.n 1209), σ (.n 1330), σ (.n 11)] = D.sArgs curE zvE tbE
      have hc5 : [σ (.n 1203), σ (.n 1204), σ (.n 1205), σ (.n 1206), σ (.n 1207)] = D.I.2.2.cap :=
        mr (b := 1203) (n := 5) (I_ok h).2 hic
      have e5 := eI 5 (by norm_num)
      have e6 := eI 6 (by norm_num)
      rw [iRets, List.getD_append_right _ _ _ _ (by rw [(I_ok h).2]), (I_ok h).2] at e5
      rw [iRets, List.getD_append_right _ _ _ _ (by rw [(I_ok h).2]; omega), (I_ok h).2] at e6
      rw [sArgs, ← hc5, e4108, e4109, e4107, p11]
      simp only [Nat.reduceAdd] at e5 e6
      rw [e5, e6]
      rfl
    · rw [(hoi2 16 (by norm_num) ho rfl).1]
      exact mr (by simp [sRets, (S_ok h).2]) eS
  · refine ⟨rfl, ?_, fun _ ↦ ⟨?_, ?_⟩⟩
    · show decide (σ (.n 3360) ≠ 0) = true
      rw [e6580]; exact decide_eq_true (gen_ne h)
    · show [σ (.n 3361), σ (.n 18), σ (.n 3363), σ (.n 1745)] =
        [1, gen ^ (D.τ - 4), ptr zvE * gen ^ 43, ptr (D.lsOf fs ([] ++ fps.take 17) 11)]
      rw [e6581, h17, e6583, e4977, List.nil_append, lsOf_take fs fps (by norm_num)]
    · exact ((hoi2 17 (by norm_num) ho rfl).1).symm

end VkData

end
end LeanVM.Guest.B1.VerifySub
