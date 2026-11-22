/-
  LeanVM.Guest.CoreMode.Fn.verify_keccak.EndExecCoreVk

  `verify_keccak`'s family (`CoreMode.vkQC`) sound at its honest instances.
-/

module

public import LeanVM.Guest.CoreMode.Fn.verify_keccak.ResVk
public import LeanVM.Guest.CoreMode.CoreRes
public import LeanVM.Guest.CoreMode.Fn.verify_keccak.Fam
public import LeanVM.Guest.EndExecCoreFn
public import LeanVM.Guest.CoreMode.HeapCSound
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_keccak»

/-!
# `verify_keccak`'s family

`vk_factors`: the hinted bits of `y = τ - 3` give each factor of `step_g` and `rem_g`, and `INV_GEN^4` is `g⁻⁴`.
`vk_inst`: at an honest instance of `verify_keccak`, `τ ∈ [9, 28]`, each value `vkE τ` knows the word `g^(vkE τ v)`,
and step `s`'s layer returns its cursor `p + 1 + (s + 1)·(84 + 2(τ - 3))` words into its stream, with room for its
reads (`VkQ`, `vk_rets`). `vkEv_val`: a cell over known values is `g` to its `vkEv` (modulo the order of `g`).
`vkAt_sound`: a residual `vkAt τ` decides holds there; `vkQC_inst`, the family.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.VerifySub LeanVM.Guest.Value
open LeanVM.Guest.CoreMode (CRes CCell CRun CIdx LtF capE idxC vw prodW vkE vkEv vkU vkK vkAt vkQC vkCurs gOrd
  rep_of)
open LeanVM.Protocol.Verifier (gen)

public section

theorem gen_pow_mod_ord (n : ℕ) : gen ^ (n % gOrd) = gen ^ n := by
  rw [gen_pow_eq_ofK, gen_pow_eq_ofK]
  simp only [addressOfIndex, gOrd]
  rw [← orderOf_g, pow_mod_orderOf]

/-- A Boolean bit's factor `1 + b·(g^k + 1)` is `g^(k·b)`. -/
theorem bit_factor {b : E} (hb : b * b = b) (k : ℕ) :
    1 + b * (gen ^ k + 1) = gen ^ (k * (decide (b = 1)).toNat) := by
  rw [bitE_of_mul_self hb]
  cases hd : decide (b = 1) <;> simp [bitE]
  rw [add_comm, add_assoc, CharTwo.add_self_eq_zero, add_zero]

/-- **`y`'s bits' factors**: `step_g`'s and `rem_g`'s factors are `g` to `y`'s bits (times their weights), and
`INV_GEN^4` is `g⁻⁴` (`vkBits_holds`'s atoms). -/
theorem vk_factors {C : CallRel} {rd : Reader} {σ : Val} {τ : ℕ} (hτ1 : 9 ≤ τ) (hτ2 : τ ≤ 28)
    (htg : σ (.n (val% «verify_keccak» "tau_g")) = gen ^ τ) {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ vkBitsT next kret) :
    σ (.n (val% «verify_keccak» "pack_g~0")) * gen ^ 4 = 1 ∧ σ (.n (val% «verify_keccak» "step_g@1")) = gen ^ ((τ - 3) / 8 % 2) ∧ σ (.n (val% «verify_keccak» "step_g@2~3")) = gen ^ (2 * ((τ - 3) / 16 % 2)) ∧
      σ (.n (val% «verify_keccak» "rem_g@1")) = gen ^ ((τ - 3) % 2) ∧ σ (.n (val% «verify_keccak» "rem_g@2~3")) = gen ^ (2 * ((τ - 3) / 2 % 2)) ∧
      σ (.n (val% «verify_keccak» "rem_g@3~3")) = gen ^ (4 * ((τ - 3) / 4 % 2)) := by
  obtain ⟨-, -, h35, h49, -⟩ := vkBits_holds hτ1 hτ2 htg h
  simp only [vkBitsT, Stmt.HoldsList, Stmt.Holds, Atom.Holds] at h
  obtain ⟨e17, e18, e19, e20, -, b0, b1, b2, b3, b4, e26, e27, e28, e29, e30, e31, e32, e33, e34,
    e35, e36, e37, e38, e39, e40, e41, e42, e43, e44, e45, e46, e47, e48, -⟩ := h
  have f30 : σ (.n (val% «verify_keccak» "step_g@1")) = gen ^ (2 ^ 0 * (decide (σ (.n (val% «verify_keccak» "y_bits[3]")) = 1)).toNat) := by
    rw [← bit_factor b3.symm, e29, e28, e27, e26, word_one, word_3]
  have f34 : σ (.n (val% «verify_keccak» "step_g@2~3")) = gen ^ (2 ^ 1 * (decide (σ (.n (val% «verify_keccak» "y_bits[4]")) = 1)).toNat) := by
    rw [← bit_factor b4.symm, e33, e32, e31, e30, word_one, word_5]
  have f39 : σ (.n (val% «verify_keccak» "rem_g@1")) = gen ^ (2 ^ 0 * (decide (σ (.n (val% «verify_keccak» "y_bits[0]")) = 1)).toNat) := by
    rw [← bit_factor b0.symm, e38, e37, e36, e35, word_one, word_3]
  have f43 : σ (.n (val% «verify_keccak» "rem_g@2~3")) = gen ^ (2 ^ 1 * (decide (σ (.n (val% «verify_keccak» "y_bits[1]")) = 1)).toNat) := by
    rw [← bit_factor b1.symm, e42, e41, e40, e39, word_one, word_5]
  have f48 : σ (.n (val% «verify_keccak» "rem_g@3~3")) = gen ^ (2 ^ 2 * (decide (σ (.n (val% «verify_keccak» "y_bits[2]")) = 1)).toNat) := by
    rw [← bit_factor b2.symm, e47, e46, e45, e44, word_one, word_17]
  have hq : (decide (σ (.n (val% «verify_keccak» "y_bits[3]")) = 1)).toNat + 2 * (decide (σ (.n (val% «verify_keccak» "y_bits[4]")) = 1)).toNat = (τ - 3) / krStep := by
    have : σ (.n (val% «verify_keccak» "step_g@2")) = gen ^ ((decide (σ (.n (val% «verify_keccak» "y_bits[3]")) = 1)).toNat + 2 * (decide (σ (.n (val% «verify_keccak» "y_bits[4]")) = 1)).toNat) := by
      rw [e34, f30, f34, ← pow_add]; congr 1; simp
    rw [this] at h35
    have h1 := Bool.toNat_le (decide (σ (.n (val% «verify_keccak» "y_bits[3]")) = 1))
    have h2 := Bool.toNat_le (decide (σ (.n (val% «verify_keccak» "y_bits[4]")) = 1))
    exact gen_pow_inj (by omega) (by simp only [krStep]; omega) h35
  have hr : (decide (σ (.n (val% «verify_keccak» "y_bits[0]")) = 1)).toNat + 2 * (decide (σ (.n (val% «verify_keccak» "y_bits[1]")) = 1)).toNat +
      4 * (decide (σ (.n (val% «verify_keccak» "y_bits[2]")) = 1)).toNat = (τ - 3) % krStep := by
    have : σ (.n (val% «verify_keccak» "rem_g@3")) = gen ^ ((decide (σ (.n (val% «verify_keccak» "y_bits[0]")) = 1)).toNat + 2 * (decide (σ (.n (val% «verify_keccak» "y_bits[1]")) = 1)).toNat +
        4 * (decide (σ (.n (val% «verify_keccak» "y_bits[2]")) = 1)).toNat) := by
      rw [e48, e43, f39, f43, f48, ← pow_add, ← pow_add]; congr 1; simp
    rw [this] at h49
    have h1 := Bool.toNat_le (decide (σ (.n (val% «verify_keccak» "y_bits[0]")) = 1))
    have h2 := Bool.toNat_le (decide (σ (.n (val% «verify_keccak» "y_bits[1]")) = 1))
    have h3 := Bool.toNat_le (decide (σ (.n (val% «verify_keccak» "y_bits[2]")) = 1))
    exact gen_pow_inj (by omega) (by simp only [krStep]; omega) h49
  simp only [krStep] at hq hr
  have h1 := Bool.toNat_le (decide (σ (.n (val% «verify_keccak» "y_bits[3]")) = 1))
  have h2 := Bool.toNat_le (decide (σ (.n (val% «verify_keccak» "y_bits[4]")) = 1))
  have h3 := Bool.toNat_le (decide (σ (.n (val% «verify_keccak» "y_bits[0]")) = 1))
  have h4 := Bool.toNat_le (decide (σ (.n (val% «verify_keccak» "y_bits[1]")) = 1))
  have h5 := Bool.toNat_le (decide (σ (.n (val% «verify_keccak» "y_bits[2]")) = 1))
  refine ⟨by rw [e17]; exact word_ginv4_mul, ?_, ?_, ?_, ?_, ?_⟩
  · rw [f30]; congr 1; omega
  · rw [f34]; congr 1; omega
  · rw [f39]; congr 1; omega
  · rw [f43]; congr 1; omega
  · rw [f48]; congr 1; omega

/-- `INV_GEN^4`'s word is `g` to the order less four. -/
theorem ginv4_pow {x : E} (h : x * gen ^ 4 = 1) : x = gen ^ (gOrd - 4) := by
  have h1 : gen ^ (gOrd - 4) * gen ^ 4 = 1 := by
    rw [← pow_add, show gOrd - 4 + 4 = gOrd by decide, ← gen_pow_mod_ord, Nat.mod_self, pow_zero]
  exact mul_right_cancel₀ (gen_pow_ne_zero 4) (h.trans h1.symm)

/-- **`verify_keccak` at an honest instance**: `τ ∈ [9, 28]`, each value `vkE τ` knows the word `g^(vkE τ v)`, and
step `s`'s layer returns its cursor `p + 1 + (s + 1)·(84 + 2(τ - 3))` words into its stream, with room (`VkQ`). -/
theorem vk_inst {r : Ref} (hr : r.Ok) {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T)
    {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node f σ bufs kids) {fn : Fn}
    (hf : coreProgram.find? f = some fn) (hn : fn.name = name% «verify_keccak») :
    ∃ τ p, 9 ≤ τ ∧ τ ≤ 28 ∧ p + vkNeed τ ≤ 8192 ∧ (∀ v e, vkE τ v = some e → vw σ v = gen ^ e) ∧
      ∀ s < 12, vw σ (vkCurs.getD s 0) = vw σ 12 * gen ^ (p + 1 + (s + 1) * (84 + 2 * (τ - 3))) := by
  have hf' : f = name% «verify_keccak» := by rw [← find_name' hf, hn]
  subst hf'
  obtain rfl : fn = fn% «verify_keccak» := Option.some.inj (hf.symm.trans find_vk)
  obtain ⟨p, τ, e5, e6, hτ9, hτ28, hroom⟩ := vkQ_all hr I hI σ bufs kids ht
  obtain ⟨args, rets, hv⟩ := inst_valid' hr hI ht
  have hfs : ∀ f', 1 ≤ B2C.fs f' := Res.fs_pos
  obtain ⟨-, hb⟩ := Res.holds_of_valid hfs hv find_vk
  have hrets := vk_rets (fun _ _ _ h ↦ Res.KidRel.rel h) hτ9 hτ28 e6 vk_body hb
  have hb' := hb
  rw [vk_body, vkT, holdsList_append, holdsList_append, holdsList_append, holdsList_append,
    holdsList_append] at hb'
  obtain ⟨h19, h21, h35, h49, -⟩ := vkHeadT_holds hτ9 hτ28 e6 hb'
  have hbits := hb'
  rw [vkHeadT, holdsList_append, holdsList_append, holdsList_append, holdsList_append,
    holdsList_append, holdsList_map_atoms] at hbits
  obtain ⟨-, hbits⟩ := hbits
  obtain ⟨f18, f30, f34, f39, f43, f48⟩ := vk_factors hτ9 hτ28 e6 hbits
  refine ⟨τ, p, hτ9, hτ28, hroom, fun v e he ↦ ?_, fun s hs ↦ ?_⟩
  · have hm := CoreMode.lookup_memL he
    simp only [CoreMode.vkTab, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
    simp only [CoreMode.vw]
    simp only [krStep] at h35 h49
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact e6
    · exact ginv4_pow f18
    · exact h19
    · exact h21
    · exact h35
    · exact h49
    · exact f30
    · exact f34
    · exact f39
    · exact f43
    · exact f48
  · have := hrets s hs
    have hv : (vkCall s).2.2.getD 5 (.n (val% «verify_keccak» "fs0@1")) = V.n (vkCurs.getD s 0) :=
      beq_iff_eq.mp (List.all_eq_true.mp vkCall_rets s (List.mem_range.mpr hs))
    rw [hv, e5] at this
    simp only [CoreMode.vw]
    rw [this, mul_assoc, ← pow_add]
    congr 2
    omega

variable {τ : ℕ} {σ : Val}

/-- The known bases' product and offset, folded (`vkEv` before the order). -/
theorem vkFold_val (hE : ∀ v e, vkE τ v = some e → vw σ v = gen ^ e) (off : ℕ) :
    ∀ (bs : List (ℕ × ℕ)) {a : ℕ}, bs.foldr (fun b acc ↦ acc.bind fun a ↦ (vkE τ b.1).map fun e ↦ a + b.2 * e)
      (some off) = some a → prodW (vw σ) bs * gen ^ off = gen ^ a
  | [], a, h => by simp only [List.foldr_nil, Option.some.injEq] at h; subst h; simp [prodW]
  | b :: bs, a, h => by
    simp only [List.foldr_cons, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨a', ha', e, he, rfl⟩ := h
    have ih := vkFold_val hE off bs ha'
    simp only [prodW]
    rw [hE _ _ he, mul_assoc, ih, ← pow_mul, ← pow_add]
    congr 1; ring

/-- **A cell over known values** is `g` to its `vkEv`. -/
theorem vkEv_val (hE : ∀ v e, vkE τ v = some e → vw σ v = gen ^ e) {c : CCell} {n : ℕ} (h : vkEv τ c = some n) :
    c.valW (vw σ) = gen ^ n := by
  unfold vkEv at h
  obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
  rw [CoreMode.CCell.valW, ← gen_pow_eq_ofK, vkFold_val hE c.off c.bases ha, gen_pow_mod_ord]

theorem vkEv_lt {c : CCell} {n : ℕ} (h : vkEv τ c = some n) : n < gOrd := by
  unfold vkEv at h
  obtain ⟨a, -, rfl⟩ := Option.map_eq_some_iff.mp h
  exact Nat.mod_lt _ (by decide)

/-- A product split by a predicate on its bases. -/
theorem prodW_filter (w : ℕ → E) (p : ℕ × ℕ → Bool) : ∀ bs : List (ℕ × ℕ),
    prodW w bs = prodW w (bs.filter p) * prodW w (bs.filter fun b ↦ !p b)
  | [] => by simp [prodW]
  | b :: bs => by
    have ih := prodW_filter w p bs
    cases hb : p b <;> simp only [List.filter_cons, hb, Bool.not_false, Bool.not_true, ite_true, ite_false,
      Bool.false_eq_true, prodW, ih] <;> ring

/-- A cell is its unknown bases' product times its known part. -/
theorem vk_split_val (c : CCell) :
    c.valW (vw σ) = prodW (vw σ) (vkU τ c) * (vkK τ c).valW (vw σ) := by
  simp only [CoreMode.CCell.valW, vkU, vkK]
  rw [prodW_filter (vw σ) (fun b ↦ (vkE τ b.1).isSome) c.bases]
  have : (c.bases.filter fun b ↦ !(vkE τ b.1).isSome) = c.bases.filter fun b ↦ (vkE τ b.1).isNone := by
    congr 1; funext b; cases vkE τ b.1 <;> rfl
  rw [this]; ring

theorem rep_gen {n : ℕ} (hn : n < capE) : CoreMode.rep (gen ^ n) = some n := by
  rw [gen_pow_eq_ofK]; exact rep_of hn

theorem rep_gen_eq {n y : ℕ} (hn : n < gOrd) (h : CoreMode.rep (gen ^ n) = some y) : y = n := by
  obtain ⟨hlt, heq⟩ := CoreMode.rep_spec h
  rw [← gen_pow_eq_ofK] at heq
  exact gen_pow_inj (by rw [CoreMode.capE_eq] at hlt; omega) (by simpa [gOrd] using hn) heq.symm

/-- **A residual `vkAt τ` decides holds** where the known values are `g` to their `vkE`. -/
theorem vkAt_sound (hE : ∀ v e, vkE τ v = some e → vw σ v = gen ^ e) : ∀ r : CRes, vkAt τ r = true → r.Holds σ
  | .lt a b, h => by
    simp only [vkAt] at h
    cases hu : vkEv τ (idxC a) with
    | none => simp [hu] at h
    | some u =>
      cases hv : vkEv τ (idxC b) with
      | none => simp [hu, hv] at h
      | some v =>
        simp only [hu, hv, Option.bind_some, Option.map_some, Option.getD_some, Bool.and_eq_true,
          decide_eq_true_eq] at h
        exact ⟨u, v, by rw [vkEv_val hE hu]; exact rep_gen (by omega), by rw [vkEv_val hE hv]; exact rep_gen h.2, h.1⟩
  | .subR q r, h => by
    simp only [vkAt] at h
    cases hkq : vkEv τ (vkK τ q.base) with
    | none => simp [hkq] at h
    | some kq =>
    cases hkr : vkEv τ (vkK τ r.base) with
    | none => simp [hkq, hkr] at h
    | some kr =>
    cases hlq : vkEv τ (idxC q.lo) with
    | none => simp [hkq, hkr, hlq] at h
    | some lq =>
    cases hhq : vkEv τ (idxC q.hi) with
    | none => simp [hkq, hkr, hlq, hhq] at h
    | some hq =>
    cases hlr : vkEv τ (idxC r.lo) with
    | none => simp [hkq, hkr, hlq, hhq, hlr] at h
    | some lr =>
    cases hhr : vkEv τ (idxC r.hi) with
    | none => simp [hkq, hkr, hlq, hhq, hlr, hhr] at h
    | some hr =>
    simp only [hkq, hkr, hlq, hhq, hlr, hhr, Option.bind_some, Option.map_some, Option.getD_some, CoreMode.vkRun,
      Bool.and_eq_true, decide_eq_true_eq, Nat.blt_eq, List.all_eq_true, List.mem_range, Nat.beq_eq] at h
    obtain ⟨⟨⟨⟨⟨hU, hS⟩, hcq⟩, hcq'⟩, hcr⟩, hall⟩ := h
    intro x hx
    obtain ⟨ylo, yhi, j, h1, h2, h3, h4, rfl⟩ := hx
    rw [vkEv_val hE hlq] at h1
    rw [vkEv_val hE hhq] at h2
    have e1 := rep_gen_eq (vkEv_lt hlq) h1
    have e2 := rep_gen_eq (vkEv_lt hhq) h2
    subst e1 e2
    obtain ⟨⟨⟨hk, hd⟩, hl⟩, hh⟩ := hall (j - ylo) (by omega)
    rw [show ylo + (j - ylo) = j by omega] at hk hd hl hh
    have hm := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hd)
    refine ⟨lr, hr, (kq + q.stride * j - kr) / r.stride, by rw [vkEv_val hE hlr]; exact rep_gen (by omega),
      by rw [vkEv_val hE hhr]; exact rep_gen hcr, hl, hh, ?_⟩
    have key : q.base.valW (vw σ) * ofK (addressOfIndex (q.stride * j)) =
        r.base.valW (vw σ) * ofK (addressOfIndex (r.stride * ((kq + q.stride * j - kr) / r.stride))) := by
      rw [vk_split_val (τ := τ) q.base, vk_split_val (τ := τ) r.base, hU, vkEv_val hE hkq, vkEv_val hE hkr,
        mul_assoc, mul_assoc, ← gen_pow_eq_ofK, ← gen_pow_eq_ofK, ← pow_add, ← pow_add, hm,
        show kr + (kq + q.stride * j - kr) = kq + q.stride * j by omega]
    rw [key]
  | .under _ r, h => fun _ ↦ vkAt_sound hE r h
  | .nz _, h | .sub _ _, h | .subP _ _, h => by simp [vkAt] at h

/-- A residual `vkAt` decides at every `τ ∈ [9, 28]` holds at an honest instance of `verify_keccak`. -/
theorem vkAll_inst {r : Ref} (hr : r.Ok) {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T)
    {f : String} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node f σ bufs kids) {fn : Fn}
    (hf : coreProgram.find? f = some fn) {x : CRes}
    (h : (fn.name == name% «verify_keccak» && (List.range 20).all fun i ↦ vkAt (9 + i) x) = true) : x.Holds σ := by
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨τ, p, h9, h28, -, hE, -⟩ := vk_inst hr hI ht hf h.1
  have := h.2 (τ - 9) (by omega)
  rw [show 9 + (τ - 9) = τ by omega] at this
  exact vkAt_sound hE x this

/-- **`verify_keccak`'s family holds** at an honest instance (`vkQC`): its reads past its layers' returned cursors
inside its stream (`vk_inst`), and the residuals true at every `τ ∈ [9, 28]` (`vkAt_sound`). -/
theorem vkQC_inst {r : Ref} (hr : r.Ok) {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T)
    {f : String} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node f σ bufs kids) {fn : Fn}
    (hf : coreProgram.find? f = some fn) : ∀ x : CRes, vkQC fn x = true → x.Holds σ
  | .under gs r', h => fun _ ↦ vkQC_inst hr hI ht hf r' h
  | .sub c q, h => by
    simp only [vkQC, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨hn, rfl⟩, h⟩ := h
    obtain ⟨τ, p, h9, h28, hroom, -, hcur⟩ := vk_inst hr hI ht hf hn
    obtain ⟨cb, co⟩ := c
    simp only at h
    split at h
    · rename_i x hcb
      obtain ⟨s, hs, hsx⟩ := List.any_eq_true.mp h
      simp only [List.mem_range, Bool.and_eq_true, Nat.beq_eq, decide_eq_true_eq] at hs hsx
      obtain ⟨hx, hoff⟩ := hsx
      have hc := hcur s hs
      rw [hx] at hc
      have hcap : (8192 : ℕ) < capE := by rw [CoreMode.capE_eq]; norm_num
      have hroom' : p + 1 + (s + 1) * (84 + 2 * (τ - 3)) + co < 8192 := by
        unfold vkNeed at hroom
        interval_cases s <;> omega
      refine ⟨0, 8192, p + 1 + (s + 1) * (84 + 2 * (τ - 3)) + co,
        CoreMode.rep_const (by rw [CoreMode.capE_eq]; norm_num), CoreMode.rep_const hcap, Nat.zero_le _, hroom', ?_⟩
      subst hcb
      simp only [CoreMode.CCell.addrW, CoreMode.CCell.valW, CoreMode.prodW, pow_one, mul_one, one_mul, hc,
        ← Value.gen_pow_eq_ofK, addressOfIndex]
      rw [mul_assoc, ← pow_add]
      ring_nf
    · cases h
  | .lt a b, h => vkAll_inst hr hI ht hf h
  | .subR a b, h => vkAll_inst hr hI ht hf h
  | .nz a, h => vkAll_inst hr hI ht hf h
  | .subP a b, h => vkAll_inst hr hI ht hf h

end

end LeanVM.Guest.EndExec
