/-
  LeanVM.Guest.B1.KeccakGkr.VkChain

  `verify_keccak`'s twelve steps (G:2950-2980): the layers, one after the other, on the claim
  chain at `claims`.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.VkStep

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr

@[expose] public section

variable {rd : Reader} {σ : Val}

/-- The returns of a step, split: the capacity and the cursor. -/
theorem split6 {B : ℕ} (hB : 6 ≤ B) {cap : List E} {x : E}
    (h : ((List.range 6).map fun j ↦ σ (.n (B - 6 + j))) = cap ++ [x]) :
    cap = [σ (.n (B - 6)), σ (.n (B - 5)), σ (.n (B - 4)), σ (.n (B - 3)), σ (.n (B - 2))] ∧
      σ (.n (B - 1)) = x := by
  have e : ((List.range 6).map fun j ↦ σ (.n (B - 6 + j))) =
      [σ (.n (B - 6)), σ (.n (B - 5)), σ (.n (B - 4)), σ (.n (B - 3)), σ (.n (B - 2))] ++
        [σ (.n (B - 1))] := by
    simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
      List.cons_append]
    rw [show B - 6 + 0 = B - 6 by omega, show B - 6 + 1 = B - 5 by omega,
      show B - 6 + 2 = B - 4 by omega, show B - 6 + 3 = B - 3 by omega,
      show B - 6 + 4 = B - 2 by omega, show B - 6 + 5 = B - 1 by omega]
  rw [e] at h
  have := List.append_inj' h rfl
  simp only [List.cons.injEq, and_true] at this
  exact ⟨this.1.symm, this.2⟩

theorem stepEnd_0 : stepEnd 0 448 = 489 := by decide +kernel
theorem stepEnd_1 : stepEnd 1 489 = 524 := by decide +kernel
theorem stepEnd_2 : stepEnd 2 524 = 558 := by decide +kernel
theorem stepEnd_3 : stepEnd 3 558 = 601 := by decide +kernel
theorem stepEnd_4 : stepEnd 4 601 = 642 := by decide +kernel
theorem stepEnd_5 : stepEnd 5 642 = 685 := by decide +kernel
theorem stepEnd_6 : stepEnd 6 685 = 718 := by decide +kernel
theorem stepEnd_7 : stepEnd 7 718 = 759 := by decide +kernel
theorem stepEnd_8 : stepEnd 8 759 = 797 := by decide +kernel
theorem stepEnd_9 : stepEnd 9 797 = 840 := by decide +kernel
theorem stepEnd_10 : stepEnd 10 840 = 881 := by decide +kernel
theorem stepEnd_11 : stepEnd 11 881 = 921 := by decide +kernel

/-- **The twelve steps** (G:2950-2980): each layer reads the claim at `claims·g^(22 s)` and writes
the next one `KC_SIZE = 22` words on. -/
theorem vkStepsT_holds {τ : ℕ} (hτ1 : 9 ≤ τ) (hτ2 : τ ≤ 28) (h17 : σ (.n 18) = gen ^ (τ - 4))
    (h33 : σ (.n 34) = gen ^ ((τ - 3) / krStep)) (h47 : σ (.n 48) = gen ^ ((τ - 3) % krStep))
    {c : KeccakClaim} {L0 : E}
    (hcr : ClaimRec rd ((1 : ℕ) = 1) (σ (.n 161)) c (τ - 3))
    (hL0 : ∀ v, LoadHolds rd (σ (.n 234)) 30 v → v = L0)
    (hw0 : ∀ z < 64, c.weights.getD z 0 = L0 * gen ^ z)
    (hpk : FsPackOk σ (.n 158) (158 + 1) dsObserve)
    (hK : keccak_layer_Spec rd) (htabs : WinTabs rd (σ (.n 11)))
    {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList (coreProgram.Rel rd) rd σ vkStepsT next kret) :
    ∃ (xs : List E) (c' : KeccakClaim), ReadsAt rd (σ (.n 5) * gen) xs ∧
      RunsTo (keccakLayers τ (List.range keccakDepth) c)
        ⟨[σ (.n 152), σ (.n 153), σ (.n 154), σ (.n 155), σ (.n 156)], [(σ (.n 158), dsObserve)]⟩
        xs c' ⟨[σ (.n 915), σ (.n 916), σ (.n 917), σ (.n 918), σ (.n 919)], []⟩ ∧
      ClaimRec rd ((0 : ℕ) = 1) (σ (.n 161) * gen ^ (22 * 12)) c' (τ - 3) ∧
      σ (.n 920) = σ (.n 5) * gen * gen ^ xs.length ∧ next := by
  rw [vkStepsT] at h
  simp only [List.append_assoc] at h
  rw [holdsList_append] at h
  obtain ⟨xs0, c1, cap1, hx0, r0, hc1, o0, e0, h⟩ := stepT_holds0 hτ1 hτ2 h17 h33 h47 hcr hL0 hw0 hpk hK htabs h
  rw [stepEnd_0] at e0 o0
  obtain ⟨k1, u1⟩ := split6 (by norm_num) e0
  simp only [Nat.reduceSub] at k1 u1 o0
  rw [holdsList_append] at h
  obtain ⟨xs1, c2, cap2, hx1, r1, hc2, o1, e1, h⟩ := stepT_holdsL (s := 1) (b := 489)
    (by norm_num) (by norm_num) hτ1 hτ2 h17 h33 h47 (by simp) o0 hc1 hK htabs h
  rw [stepEnd_1] at e1 o1
  obtain ⟨k2, u2⟩ := split6 (by norm_num) e1
  simp only [Nat.reduceSub] at k2 u2 o1
  rw [← k1] at r1
  rw [holdsList_append] at h
  obtain ⟨xs2, c3, cap3, hx2, r2, hc3, o2, e2, h⟩ := stepT_holdsL (s := 2) (b := 524)
    (by norm_num) (by norm_num) hτ1 hτ2 h17 h33 h47 o0 o1 hc2 hK htabs h
  rw [stepEnd_2] at e2 o2
  obtain ⟨k3, u3⟩ := split6 (by norm_num) e2
  simp only [Nat.reduceSub] at k3 u3 o2
  rw [← k2] at r2
  rw [holdsList_append] at h
  obtain ⟨xs3, c4, cap4, hx3, r3, hc4, o3, e3, h⟩ := stepT_holdsL (s := 3) (b := 558)
    (by norm_num) (by norm_num) hτ1 hτ2 h17 h33 h47 o1 o2 hc3 hK htabs h
  rw [stepEnd_3] at e3 o3
  obtain ⟨k4, u4⟩ := split6 (by norm_num) e3
  simp only [Nat.reduceSub] at k4 u4 o3
  rw [← k3] at r3
  rw [holdsList_append] at h
  obtain ⟨xs4, c5, cap5, hx4, r4, hc5, o4, e4, h⟩ := stepT_holdsL (s := 4) (b := 601)
    (by norm_num) (by norm_num) hτ1 hτ2 h17 h33 h47 o2 o3 hc4 hK htabs h
  rw [stepEnd_4] at e4 o4
  obtain ⟨k5, u5⟩ := split6 (by norm_num) e4
  simp only [Nat.reduceSub] at k5 u5 o4
  rw [← k4] at r4
  rw [holdsList_append] at h
  obtain ⟨xs5, c6, cap6, hx5, r5, hc6, o5, e5, h⟩ := stepT_holdsL (s := 5) (b := 642)
    (by norm_num) (by norm_num) hτ1 hτ2 h17 h33 h47 o3 o4 hc5 hK htabs h
  rw [stepEnd_5] at e5 o5
  obtain ⟨k6, u6⟩ := split6 (by norm_num) e5
  simp only [Nat.reduceSub] at k6 u6 o5
  rw [← k5] at r5
  rw [holdsList_append] at h
  obtain ⟨xs6, c7, cap7, hx6, r6, hc7, o6, e6, h⟩ := stepT_holdsL (s := 6) (b := 685)
    (by norm_num) (by norm_num) hτ1 hτ2 h17 h33 h47 o4 o5 hc6 hK htabs h
  rw [stepEnd_6] at e6 o6
  obtain ⟨k7, u7⟩ := split6 (by norm_num) e6
  simp only [Nat.reduceSub] at k7 u7 o6
  rw [← k6] at r6
  rw [holdsList_append] at h
  obtain ⟨xs7, c8, cap8, hx7, r7, hc8, o7, e7, h⟩ := stepT_holdsL (s := 7) (b := 718)
    (by norm_num) (by norm_num) hτ1 hτ2 h17 h33 h47 o5 o6 hc7 hK htabs h
  rw [stepEnd_7] at e7 o7
  obtain ⟨k8, u8⟩ := split6 (by norm_num) e7
  simp only [Nat.reduceSub] at k8 u8 o7
  rw [← k7] at r7
  rw [holdsList_append] at h
  obtain ⟨xs8, c9, cap9, hx8, r8, hc9, o8, e8, h⟩ := stepT_holdsL (s := 8) (b := 759)
    (by norm_num) (by norm_num) hτ1 hτ2 h17 h33 h47 o6 o7 hc8 hK htabs h
  rw [stepEnd_8] at e8 o8
  obtain ⟨k9, u9⟩ := split6 (by norm_num) e8
  simp only [Nat.reduceSub] at k9 u9 o8
  rw [← k8] at r8
  rw [holdsList_append] at h
  obtain ⟨xs9, c10, cap10, hx9, r9, hc10, o9, e9, h⟩ := stepT_holdsL (s := 9) (b := 797)
    (by norm_num) (by norm_num) hτ1 hτ2 h17 h33 h47 o7 o8 hc9 hK htabs h
  rw [stepEnd_9] at e9 o9
  obtain ⟨k10, u10⟩ := split6 (by norm_num) e9
  simp only [Nat.reduceSub] at k10 u10 o9
  rw [← k9] at r9
  rw [holdsList_append] at h
  obtain ⟨xs10, c11, cap11, hx10, r10, hc11, o10, e10, h⟩ := stepT_holdsL (s := 10) (b := 840)
    (by norm_num) (by norm_num) hτ1 hτ2 h17 h33 h47 o8 o9 hc10 hK htabs h
  rw [stepEnd_10] at e10 o10
  obtain ⟨k11, u11⟩ := split6 (by norm_num) e10
  simp only [Nat.reduceSub] at k11 u11 o10
  rw [← k10] at r10
  obtain ⟨xs11, c12, cap12, hx11, r11, hc12, o11, e11, h⟩ := stepT_holdsL (s := 11) (b := 881)
    (by norm_num) (by norm_num) hτ1 hτ2 h17 h33 h47 o9 o10 hc11 hK htabs h
  rw [stepEnd_11] at e11 o11
  obtain ⟨k12, u12⟩ := split6 (by norm_num) e11
  simp only [Nat.reduceSub] at k12 u12 o11
  rw [← k11] at r11
  have run := runsTo_keccakLayers_cons r0 (runsTo_keccakLayers_cons r1 (runsTo_keccakLayers_cons r2
    (runsTo_keccakLayers_cons r3 (runsTo_keccakLayers_cons r4 (runsTo_keccakLayers_cons r5
    (runsTo_keccakLayers_cons r6 (runsTo_keccakLayers_cons r7 (runsTo_keccakLayers_cons r8
    (runsTo_keccakLayers_cons r9 (runsTo_keccakLayers_cons r10 (runsTo_keccakLayers_cons r11
    (runsTo_keccakLayers_nil τ c12 _))))))))))))
  have R11 : ReadsAt rd (σ (.n 880)) (xs11 ++ []) := by simpa using hx11
  have R10 : ReadsAt rd (σ (.n 839)) (xs10 ++ (xs11 ++ [])) :=
    readsAt_append.2 ⟨hx10, by rw [← u11]; exact R11⟩
  have R9 : ReadsAt rd (σ (.n 796)) (xs9 ++ (xs10 ++ (xs11 ++ []))) :=
    readsAt_append.2 ⟨hx9, by rw [← u10]; exact R10⟩
  have R8 : ReadsAt rd (σ (.n 758)) (xs8 ++ (xs9 ++ (xs10 ++ (xs11 ++ [])))) :=
    readsAt_append.2 ⟨hx8, by rw [← u9]; exact R9⟩
  have R7 : ReadsAt rd (σ (.n 717)) (xs7 ++ (xs8 ++ (xs9 ++ (xs10 ++ (xs11 ++ []))))) :=
    readsAt_append.2 ⟨hx7, by rw [← u8]; exact R8⟩
  have R6 : ReadsAt rd (σ (.n 684)) (xs6 ++ (xs7 ++ (xs8 ++ (xs9 ++ (xs10 ++ (xs11 ++ [])))))) :=
    readsAt_append.2 ⟨hx6, by rw [← u7]; exact R7⟩
  have R5 : ReadsAt rd (σ (.n 641)) (xs5 ++ (xs6 ++ (xs7 ++ (xs8 ++ (xs9 ++ (xs10 ++ (xs11 ++ []))))))) :=
    readsAt_append.2 ⟨hx5, by rw [← u6]; exact R6⟩
  have R4 : ReadsAt rd (σ (.n 600)) (xs4 ++ (xs5 ++ (xs6 ++ (xs7 ++ (xs8 ++ (xs9 ++ (xs10 ++ (xs11 ++ [])))))))) :=
    readsAt_append.2 ⟨hx4, by rw [← u5]; exact R5⟩
  have R3 : ReadsAt rd (σ (.n 557)) (xs3 ++ (xs4 ++ (xs5 ++ (xs6 ++ (xs7 ++ (xs8 ++ (xs9 ++ (xs10 ++ (xs11 ++ []))))))))) :=
    readsAt_append.2 ⟨hx3, by rw [← u4]; exact R4⟩
  have R2 : ReadsAt rd (σ (.n 523)) (xs2 ++ (xs3 ++ (xs4 ++ (xs5 ++ (xs6 ++ (xs7 ++ (xs8 ++ (xs9 ++ (xs10 ++ (xs11 ++ [])))))))))) :=
    readsAt_append.2 ⟨hx2, by rw [← u3]; exact R3⟩
  have R1 : ReadsAt rd (σ (.n 488)) (xs1 ++ (xs2 ++ (xs3 ++ (xs4 ++ (xs5 ++ (xs6 ++ (xs7 ++ (xs8 ++ (xs9 ++ (xs10 ++ (xs11 ++ []))))))))))) :=
    readsAt_append.2 ⟨hx1, by rw [← u2]; exact R2⟩
  have R0 : ReadsAt rd (σ (.n 5) * gen) (xs0 ++ (xs1 ++ (xs2 ++ (xs3 ++ (xs4 ++ (xs5 ++ (xs6 ++ (xs7 ++ (xs8 ++ (xs9 ++ (xs10 ++ (xs11 ++ [])))))))))))) :=
    readsAt_append.2 ⟨hx0, by rw [← u1]; exact R1⟩
  refine ⟨xs0 ++ (xs1 ++ (xs2 ++ (xs3 ++ (xs4 ++ (xs5 ++ (xs6 ++ (xs7 ++ (xs8 ++ (xs9 ++ (xs10 ++ (xs11 ++ []))))))))))), c12, R0, ?_, hc12, ?_, h⟩
  · rw [k12] at run
    exact run
  · rw [u12, u11, u10, u9, u8, u7, u6, u5, u4, u3, u2, u1]
    simp only [List.length_append, List.length_nil, Nat.add_zero, pow_add, mul_assoc]

end
end LeanVM.Guest.B1.VerifySub
