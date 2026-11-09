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

variable {D : VkData} {rd : Reader} {B curE chiE olE zvE slE : ℕ} {fs : String → ℕ}
  {fps : List ℕ}

theorem gen_ne (h : D.Ok) : 1 + gen ^ (D.τ - 4) ≠ 0 :=
  gen_pow_ne_one (by have := h.1; omega) (by have := h.2.1; unfold ordG; omega)

/-- **Layer `s`'s frame matches its callee.** -/
theorem layer_match (h : D.Ok) (hm : D.Mem rd B curE chiE olE zvE slE (D.lsOf fs fps)) {σ : Val}
    (hσd : σ = D.val rd B curE chiE olE zvE slE) {s : ℕ} (hs : s < 12)
    {o : List E × Main.Layout}
    (ho : (D.layKid fs B curE s).Out ([] ++ fps.take (s + 1 + 1)) o.1 o.2) :
    (Main.mkCall σ (stepCall s)).f = (D.layKid fs B curE s).f ∧
      (Main.mkCall σ (stepCall s)).taken = (D.layKid fs B curE s).taken ∧
      ((D.layKid fs B curE s).taken = true →
        (Main.mkCall σ (stepCall s)).args.map σ =
          (D.layKid fs B curE s).args ([] ++ fps.take (s + 1)) ∧
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
theorem calls_match (h : D.Ok) (hm : D.Mem rd B curE chiE olE zvE slE (D.lsOf fs fps))
    {σ : Val} (hσd : σ = D.val rd B curE chiE olE zvE slE) (hfl : fps.length = 18)
    {outs : List (List E × Main.Layout)}
    (hout : OutsOk (atAllG [] (D.kids fs B curE chiE olE zvE slE) fps) outs) :
    CallsMatch σ ((vkPre.filterMap (Stmt.callSF σ)).map (Main.mkCall σ))
      (atAllG [] (D.kids fs B curE chiE olE zvE slE) fps) outs := by
  obtain ⟨-, -, p6, -, -, p9, p10, h17, -, -, a58, e60, e61, e63, -, -, -, -, e191, -, a201, -,
    a274, -, -⟩ := head_first h hm hσd
  obtain ⟨eL, e3690, e3691, e3692, e3693, eO, -, cellsW, e3971, e3972, e3974, -⟩ :=
    out_on h hm hσd p6 p9 h17 a58 a274
  have e3699 : σ (.n 971) = ptr (curE + D.lcur 12 + 12) := by
    have := eO 5 (by norm_num)
    rw [this, oRets, List.getD_append_right _ _ _ _ (by rw [(O_ok h).2.1]), (O_ok h).2.1]
    simp [cL, ptr_mul_gen]
  obtain ⟨e3976, e3977, e3979, eI, e4104, e4107, e4108, e4109, eS, -, -⟩ :=
    in_on h hm hσd p6 p9 p10 a201 e3699
  have e4116 : σ (.n 1388) = D.S.2.1 := by
    rw [show (1388 : ℕ) = 1382 + 6 from rfl, eS 6 (by norm_num), sRets,
      List.getD_append_right _ _ _ _ (by rw [(S_ok h).2.1]; norm_num), (S_ok h).2.1]
    rfl
  obtain ⟨e4977, e6580, e6581, e6583, -⟩ :=
    fin_on h hm hσd p9 p10 h17 a201 e4104 e4107 e4116 e3979
  rw [vkPre_callSF]
  obtain ⟨hol, hoi⟩ := outsOk_getElem hout
  have hk : (D.kids fs B curE chiE olE zvE slE).length = 18 := kids_length
  have hlen : (atAllG [] (D.kids fs B curE chiE olE zvE slE) fps).length = 18 := by
    rw [atAllG_length, hk, hfl]; rfl
  have hoi2 : ∀ i (hi : i < 18) (ho : i < outs.length),
      ((D.kids fs B curE chiE olE zvE slE)[i]'(by omega)).taken = true →
      ((D.kids fs B curE chiE olE zvE slE)[i]'(by omega)).Out ([] ++ fps.take (i + 1))
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
  have hoc : ∀ j < 5, σ (.n (966 + j)) = D.O.2.2.cap.getD j 0 := fun j hj ↦ by
    rw [eO j (by omega), oRets, List.getD_append _ _ _ _ (by rw [(O_ok h).2.1]; exact hj)]
  have hic : ∀ j < 5, σ (.n (1252 + j)) = D.I.2.2.cap.getD j 0 := fun j hj ↦ by
    rw [eI j (by omega), iRets, List.getD_append _ _ _ _ (by rw [(I_ok h).2.1]; exact hj)]
  apply callsMatch_ofI (by rw [hlen]; simp [vkCalls]) hol (fun i hi hc ho ↦ ?_)
  rw [hlen] at hi
  rw [List.getElem_map, atAllG_getElem]
  interval_cases i
  · refine ⟨rfl, ?_, fun _ ↦ ⟨?_, ?_⟩⟩
    · show decide (σ (.n 62) ≠ 0) = true
      rw [e60]; exact decide_eq_true (gen_ne h)
    · show [σ (.n 63), σ (.n 17), σ (.n 60), σ (.n 65)] = [1, gen ^ (D.τ - 4), ptr B, ptr chiE * gen ^ 4]
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
    · show [σ (.n 957), σ (.n 958), σ (.n 959), σ (.n 960), σ (.n 961), σ (.n 964),
        σ (.n 965), σ (.n 962), σ (.n 193), σ (.n 963)] = D.oArgs curE zvE
      rw [oArgs, ← eL, e3692, e3693, e3690, e191, e3691]; rfl
    · rw [(hoi2 13 (by norm_num) ho rfl).1]
      exact mr (by simp [oRets, (O_ok h).2.1]) eO
  · refine ⟨rfl, ?_, fun _ ↦ ⟨?_, ?_⟩⟩
    · show decide (σ (.n 1243) ≠ 0) = true
      rw [e3971]; exact decide_eq_true (gen_ne h)
    · show [σ (.n 1244), σ (.n 17), σ (.n 1246), σ (.n 60)] =
        [1, gen ^ (D.τ - 4), ptr zvE * gen ^ 4, ptr B]
      rw [e3972, h17, e3974, a58]
    · exact ((hoi2 14 (by norm_num) ho rfl).1).symm
  · refine ⟨rfl, rfl, fun _ ↦ ⟨?_, ?_⟩⟩
    · show [σ (.n 966), σ (.n 967), σ (.n 968), σ (.n 969), σ (.n 970), σ (.n 980),
        σ (.n 982), σ (.n 1248), σ (.n 1249), σ (.n 1251)] = D.iArgs curE zvE
      have hc5 : [σ (.n 966), σ (.n 967), σ (.n 968), σ (.n 969), σ (.n 970)] = D.O.2.2.cap :=
        mr (b := 966) (n := 5) (O_ok h).2.1 hoc
      rw [iArgs, ← hc5, ← cellsW, e3976, e3977, e3979, cL]
      simp only [ptr_mul_gen, ptr_mul_gen1, List.cons_append, List.nil_append]
    · rw [(hoi2 15 (by norm_num) ho rfl).1]
      exact mr (by simp [iRets, (I_ok h).2.1]) eI
  · refine ⟨rfl, rfl, fun _ ↦ ⟨?_, ?_⟩⟩
    · show [σ (.n 1252), σ (.n 1253), σ (.n 1254), σ (.n 1255), σ (.n 1256), σ (.n 1380),
        σ (.n 1381), σ (.n 1257), σ (.n 1258), σ (.n 1379)] = D.sArgs curE zvE
      have hc5 : [σ (.n 1252), σ (.n 1253), σ (.n 1254), σ (.n 1255), σ (.n 1256)] = D.I.2.2.cap :=
        mr (b := 1252) (n := 5) (I_ok h).2.1 hic
      have e5 := eI 5 (by norm_num)
      have e6 := eI 6 (by norm_num)
      rw [iRets, List.getD_append_right _ _ _ _ (by rw [(I_ok h).2.1]), (I_ok h).2.1] at e5
      rw [iRets, List.getD_append_right _ _ _ _ (by rw [(I_ok h).2.1]; omega), (I_ok h).2.1] at e6
      rw [sArgs, ← hc5, e4108, e4109, e4107]
      simp only [Nat.reduceAdd] at e5 e6
      rw [e5, e6]
      rfl
    · rw [(hoi2 16 (by norm_num) ho rfl).1]
      exact mr (by simp [sRets, (S_ok h).2.1]) eS
  · refine ⟨rfl, ?_, fun _ ↦ ⟨?_, ?_⟩⟩
    · show decide (σ (.n 3864) ≠ 0) = true
      rw [e6580]; exact decide_eq_true (gen_ne h)
    · show [σ (.n 3865), σ (.n 17), σ (.n 3867), σ (.n 2249)] =
        [1, gen ^ (D.τ - 4), ptr zvE * gen ^ 43, ptr (D.lsOf fs ([] ++ fps.take 17) 11)]
      rw [e6581, h17, e6583, e4977, List.nil_append, lsOf_take fs fps (by norm_num)]
    · exact ((hoi2 17 (by norm_num) ho rfl).1).symm

end VkData

end
end LeanVM.Guest.B1.VerifySub
