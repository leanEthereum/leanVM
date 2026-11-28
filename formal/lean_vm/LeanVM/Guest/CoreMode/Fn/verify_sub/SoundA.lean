/-
  LeanVM.Guest.CoreMode.Fn.verify_sub.SoundA

  `verify_sub`'s own residual families, sound at the honest instances of b2c's aligned tree (`OwnOkA`): its link width
  values' exponent bounds, from its range checks (`gw_of_shape`, `gn_of_shape`) and its certified sizes (`SizesOk`); the
  link's challenges (`chalFam`, `chalFacts_of`); the proof stream (`streamFam`, `streamFam_okA` at `vsStreamQ`).
-/

module

public import LeanVM.Guest.EndExecExpCA
public import LeanVM.Guest.CoreMode.Fn.verify_sub.Fam
public import LeanVM.Guest.CoreMode.Fn.verify_sub.VkCarry
public import LeanVM.Guest.CoreMode.Fn.verify_sub.ChalA
public import LeanVM.Guest.CoreMode.Fn.verify_sub.IxA
public import LeanVM.Guest.CoreMode.Fn.verify_sub.GwInvA
public import LeanVM.Guest.CoreMode.Fn.verify_sub.OsCur
public import LeanVM.Guest.B1.VerifySub.PhLinkShape
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_sub»

namespace LeanVM.Guest.CoreMode.Own.verify_sub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.EndExec
open LeanVM.Protocol.Verifier (gen)

public section

/-- **The link width's range check** (`vsShapeAT`'s `log(g_w·g^-19) < 6`): `g_w = g^(e + 19)`, `e ≤ 5`. -/
theorem gw_of_shape {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop} (hm : B1.Digest.MemOk rd)
    (hA : Stmt.HoldsList C rd σ B1.VerifySub.vsShapeAT True kret) : ∃ e ≤ 5, σ (.n 409) = gen ^ (e + 19) := by
  simp only [B1.VerifySub.vsShapeAT, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at hA
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    s35, s36, s37, s38, -⟩ := hA
  obtain ⟨e, he, x455⟩ := B1.Digest.rc_const hm (c := 5) (by norm_num)
    (s35.trans (B1.word_two_pow (a := 5) (by norm_num))) s38
  rw [s36] at s37
  exact ⟨e, he, by rw [B1.VerifySub.eq_mul_winv19 s37, x455, pow_add]⟩

/-- **The tallest height's range check** (`vsShapeAT`'s `log(g_n / kb[2]) < 24`): `g_n = g^e`, `e ≤ 48`, given the
first table's height word `kb[2] = g^h`, `h ≤ 24`. -/
theorem gn_of_shape {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop} (hm : B1.Digest.MemOk rd)
    (hA : Stmt.HoldsList C rd σ B1.VerifySub.vsShapeAT True kret) {h : ℕ} (hh : h ≤ 24)
    (h115 : σ (.n 115) = gen ^ h) : ∃ e ≤ 48, σ (.n 408) = gen ^ e := by
  simp only [B1.VerifySub.vsShapeAT, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at hA
  obtain ⟨-, -, -, -, s4, s5, s6, -⟩ := hA
  obtain ⟨f, hf, x412⟩ := B1.Digest.rc_const hm (c := 24) (by norm_num)
    (s4.trans (B1.word_two_pow (a := 24) (by norm_num))) s6
  exact ⟨f + h, by omega, by rw [s5, x412, h115, pow_add]⟩

/-- The first table's height word `kb[2]`: `g^h`, `h` its log height (`SizesOk.heights` at `0`). -/
theorem vsHeight0 {bytecode : List K} {rd : Reader} {σ : Val} (S : B1.VerifySub.SizesOk bytecode rd σ) :
    σ (.n 115) = gen ^ (B1.VerifySub.vsLayout bytecode σ).tableLogHeights.getD 0 0 := by
  have hlen : (B1.VerifySub.vsLayout bytecode σ).tableLogHeights.length = 6 := by
    obtain ⟨-, -, -, hth, -⟩ := B1.Stack.buildLayout_some S.build
    rw [hth, List.length_zipWith]
    simp [B1.VerifySub.vsRows, B1.VerifySub.vsAnnounced, Protocol.Verifier.tableLogFloors, Protocol.Verifier.nTables]
  have := congrArg (fun l ↦ l.getD 0 0) S.heights
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (show 0 < Protocol.Verifier.nTables by decide), Option.map_some, Option.getD_some] at this
  rw [this, List.getElem?_eq_getElem (by rw [hlen]; decide), List.getD_eq_getElem _ _ (by rw [hlen]; decide)]
  rfl

/-- **Its family** (`gwFam`), on its honest instances, aligned. -/
theorem fams_okA {al : String → Bool} {D : Ref → RefD} : ∀ c ∈ fams, OwnOkA al D c := by
  intro c hc r hR hr I hI σ bufs kids ht fn hf x hx
  simp only [fams, List.mem_singleton] at hc
  subst hc
  simp only [Bool.or_eq_true] at hx ht
  rcases hx with hx | hx
  swap
  · exact streamFam_okA vsStreamQ hR hr I hI σ bufs kids ht fn hf x hx
  obtain ⟨args, rets, hv⟩ := inst_validA hR hI ht
  obtain ⟨-, hb⟩ := Res.holds_of_valid Res.fs_pos hv find_vs
  rw [B1.VerifySub.vs_body_eq, Core.holdsList_append] at hb
  have hpre := ((Core.holdsList_noRet _ B1.VerifySub.vsPre_noRet _ _).mp hb).1
  have hκ28 : r.κ ≤ 28 := hr.log
  have hκ23 : 23 ≤ r.κ := by rw [hR.κ]; exact twentyThree_le_logMem _
  have hexp : B1.ExpTables r.img.read (σ (.n (val% «verify_sub» "g_squares"))) :=
    (csQ_allA hR hr I hI _ _ _ _ ht).2.1 rfl
  have hbl : (List.replicate (2 ^ (B1.Main.bytecodeLog + Protocol.Verifier.bytecodeSlotBits)) (0 : K)).length =
      2 ^ (B1.Main.bytecodeLog + Protocol.Verifier.bytecodeSlotBits) := List.length_replicate
  have S := B1.VerifySub.sizesOk (by omega) (by omega) r.img (fun _ _ _ h ↦ Res.KidRel.rel h) hbl hexp
    (vs_slice hpre B1.VerifySub.vsReadsT_eq) (vs_slice hpre B1.VerifySub.vsHeightsT_eq)
    (vs_slice hpre B1.VerifySub.vsStackT_eq)
  have hA := vs_slice hpre B1.VerifySub.vsShapeAT_eq
  rcases hx with hx | hx
  swap
  · obtain ⟨e, he, hσ⟩ := gw_of_shape (ref_memOkA hR hr) hA
    exact gwInvFam_holds he hσ (vs_gwInv_eqs hpre) hx
  rcases hx with hx | hx
  swap
  · obtain ⟨e, he, hσ⟩ := gw_of_shape (ref_memOkA hR hr) hA
    obtain ⟨n, hn, h408⟩ := gn_of_shape (ref_memOkA hR hr) hA (S.heights24 0 (by decide)) (vsHeight0 S)
    exact ixFam_holds (ixFacts_of (ref_memOkA hR hr) hpre hA S he hσ hn h408) hx
  rcases hx with hx | hx
  swap
  · obtain ⟨e, he, hσ⟩ := gw_of_shape (ref_memOkA hR hr) hA
    obtain ⟨n, hn, h408⟩ := gn_of_shape (ref_memOkA hR hr) hA (S.heights24 0 (by decide)) (vsHeight0 S)
    exact chalFam_holds (chalFacts_of hR hI ht hn he h408 hσ (vs_gn_split hA)) hx
  unfold gwFam at hx
  split at hx
  · rename_i y n
    rw [Bool.and_eq_true] at hx
    obtain ⟨hx, hcap⟩ := hx
    obtain ⟨⟨v, b⟩, hy, hvb⟩ := List.any_eq_true.mp hx
    simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at hvb
    simp only [Nat.blt_eq] at hcap
    obtain ⟨rfl, hbn⟩ := hvb
    obtain ⟨-, hlm30, -⟩ := B1.Stack.buildLayout_some S.build
    obtain ⟨hlm, -⟩ := B1.Stack.buildLayout_some S.build
    simp only [vsBounds, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hy
    rcases hy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · obtain ⟨e, he, hσ⟩ := gw_of_shape (ref_memOkA hR hr) hA
      exact ltF_of_pow hcap (by omega : e + 19 < n) (hσ.trans (Value.gen_pow_eq_ofK _))
    · obtain ⟨h, -, h2, he⟩ := B1.VerifySub.vsHeight5_range S
      exact ltF_of_pow hcap (by omega : h < n) (he.trans (Value.gen_pow_eq_ofK _))
    · obtain ⟨e, he, hσ⟩ := gn_of_shape (ref_memOkA hR hr) hA (S.heights24 0 (by decide)) (vsHeight0 S)
      exact ltF_of_pow hcap (by omega : e < n) (hσ.trans (Value.gen_pow_eq_ofK _))
    · exact ltF_of_pow hcap (by omega) (S.logMem.trans (Value.gen_pow_eq_ofK _))
    · exact ltF_of_pow hcap (by have := S.st2; omega) (S.placed.1.trans (Value.gen_pow_eq_ofK _))
  · cases hx

end

end LeanVM.Guest.CoreMode.Own.verify_sub
