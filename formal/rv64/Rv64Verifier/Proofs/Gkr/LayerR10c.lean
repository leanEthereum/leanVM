import Rv64Verifier.Proofs.Gkr.LayerR10b

/-!
# `keccak::verify_layer`: `at_local`, the loop

`keccak.rs:166-169` at `0x8000f848..0x8000f888`: `eq_lane[k] * dot` into `f + 264`, added to the
sum in `s2`, `s4`, `s5` (`at_mul`); the loop (`at_loop`) and `at_local` from `J10` to `K10`
(`at_local`).
-/

namespace Rv64Verifier.Gkr.Layer
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Model.Gkr Rv64Verifier.Transcript Rv64Verifier.Contracts
  Rv64Verifier.Gkr Rv64Verifier.Blocks.F74
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

attribute [local rv_addr] vecPtr vecLen vecCap

theorem add1536_succ (b : Word) (k : Nat) :
    b + BitVec.ofNat 64 (1536 * k) + 1536 = b + BitVec.ofNat 64 (1536 * (k + 1)) := by
  apply BitVec.eq_of_toNat_eq
  have h : (1536 : Word).toNat = 1536 := rfl
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, h]
  omega

theorem add24_succ (b : Word) (k : Nat) :
    b + BitVec.ofNat 64 (24 * k) + 24 = b + BitVec.ofNat 64 (24 * (k + 1)) := by
  apply BitVec.eq_of_toNat_eq
  have h : (24 : Word).toNat = 24 := rfl
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, h]
  omega

theorem sub64 {n k : Nat} (h : 64 * (k + 1) ≤ n) :
    BitVec.ofNat 64 (n - 64 * k) - 64 = BitVec.ofNat 64 (n - 64 * (k + 1)) := by
  apply BitVec.eq_of_toNat_eq
  have h64 : (64 : Word).toNat = 64 := rfl
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, h64]
  omega

theorem sub1 {m k : Nat} (h : k < m) :
    BitVec.ofNat 64 (m - k) - 1 = BitVec.ofNat 64 (m - (k + 1)) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : (1 : Word).toNat = 1 := rfl
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, h1]
  omega

theorem eAt_of_same {u v : MachineState} (h : ∀ a, v.getMem a = u.getMem a) (p : Word) :
    eAt v p = eAt u p := by
  simp only [Rv64Verifier.eAt, h]

theorem mOf_lt (s : MachineState) (lp : List E) : mOf s lp < 2 ^ 64 := by
  have := (s.getMem (s.getReg .x15 + 64)).isLt
  have hwl : (wOf s).length = (s.getMem (s.getReg .x15 + 64)).toNat := by
    rw [claim_weights, eListAt_length]
  simp only [mOf]
  rw [hwl]
  omega

set_option maxHeartbeats 16000000 in
/-- `0x8000f848`: `eq_lane[k] * dot` into `f + 264`; `0x8000f85c`: the sum, the next lane or the
second check. -/
theorem at_mul (hM : MulSpec) {s v : MachineState} {ip : Word} {c : E} {point lp t : List E}
    {scale lv : E} {tp tn : Word} {k : Nat} (hpre : VerifyLayerPre s)
    (Q : QD s v ip c point scale lv lp t tp tn k) :
    ∃ u, Reaches Image.code v u ∧ (L10 s u ip c point scale lv lp t tp tn (k + 1) ∨
      K10 s u ip c point scale lv lp t tp tn ∨ Dead Image.code u) := by
  have hb := bounds hpre
  have B := Q.base
  have X := Q.fx
  have hab := hpre.stack.above
  have hlo := hpre.heap.lo
  have hHv := B.heap.hi
  simp only [stackLo] at hab
  unfold verifyLayerStack at hb hab
  have hlt := Q.lt
  have hL : k < (v.getMem (s.getReg .x2 - 1624)).toNat := by
    have : k < (eqKernelRust (lp.drop 6)).length := by simp only [mOf] at hlt; omega
    rw [← X.elE, eListAt_length] at this
    exact this
  have eB := X.elB
  have eb : heapNext s ≤ (v.getMem (s.getReg .x2 - 1600)).toNat ∧
      (v.getMem (s.getReg .x2 - 1600)).toNat + 24 * (v.getMem (s.getReg .x2 - 1624)).toNat ≤
        heapNext v := by
    rcases eB.2 with h0 | h
    · omega
    · exact h
  have ea := eB.1
  -- `0x8000f848`
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000f848_spec Q.pc trivial
  have k₁ := b8000f848_keeps h₁
  have hm₁ := b8000f848_mem_same h₁
  have x2₁ : t₁.getReg .x2 = s.getReg .x2 - 1712 := (k₁ .x2 (by decide)).trans B.x2
  have B₁ : Base s t₁ := B.same x2₁ hm₁
  have hN₁ : heapNext t₁ = heapNext v := by simp only [heapNext, hm₁]
  have x10₁ : t₁.getReg .x10 = s.getReg .x2 - 1448 := by rw [b8000f848_x10 h₁, B.x2]; rv_eval []
  have x11₁ : t₁.getReg .x11 = v.getMem (s.getReg .x2 - 1600) + BitVec.ofNat 64 (24 * k) := by
    rw [b8000f848_x11 h₁, Q.x25]
  have x12₁ : t₁.getReg .x12 = s.getReg .x2 - 752 := by rw [b8000f848_x12 h₁, B.x2]; rv_eval []
  obtain ⟨t₂, hr₂, ⟨hpc₂, hp₂, B₂, F₂, hN₂, V₂⟩ | hd⟩ := mulH hM hpre B₁ hr₁ (b8000f848_pc h₁) 1448
    x10₁ (by decide) (fun a h ↦ Or.inr (Or.inl (by addr_omega [h, hb])))
    (by
      rw [x11₁]
      exact heap_vmr (by addr_omega [eb, hlo, hL, hHv]) (by addr_omega [eb, hL, hHv])
        (by addr_omega [ea, eb, hL, hHv]))
    (by rw [x11₁]; addr_omega [eb, hL, hHv, hab, hb])
    (by rw [x11₁]; addr_omega [eb, hL, hHv, hab, hb])
    (by rw [x12₁]; exact slot_vmr hpre (by decide) (by decide) (by decide))
    (by rw [x12₁]; addr_omega [hb]) (by rw [x12₁]; addr_omega [hb])
  swap
  · exact ⟨t₂, hr₂, Or.inr (Or.inr hd)⟩
  have hG : eAt t₂ (s.getReg .x2 - 1448) = atL s lp k := by
    refine V₂.trans ?_
    rw [x11₁, x12₁, eAt_of_same hm₁, eAt_of_same hm₁]
    simp only [atL]
    rw [← Q.dot, ← X.elE, eListAt_getD_lt _ _ hL]
  have lG := limbs_eAt t₂ (s.getReg .x2 - 1448)
  rw [hG] at lG
  rv_eval [] at lG
  -- `0x8000f85c`
  have x2₂ : t₂.getReg .x2 = s.getReg .x2 - 1712 := B₂.x2
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000f85c_spec
    (by rw [hpc₂, returnAddress_eq, b8000f848_x1 h₁]; decide) (by
      rv_eval [x2₂]; and_intros <;> valid_access hpre.stack.valid [hb])
  have k₃ := b8000f85c_keeps h₃
  have hm₃ := b8000f85c_mem_same h₃
  have x2₃ : t₃.getReg .x2 = s.getReg .x2 - 1712 := (k₃ .x2 (by decide)).trans x2₂
  have B₃ : Base s t₃ := B₂.same x2₃ hm₃
  have hN₃ : heapNext t₃ = heapNext t₂ := by simp only [heapNext, hm₃]
  have X₃ : Fx s t₃ ip c point scale lv lp t tp tn :=
    ((X.keep hpre B.heap B₁.heap (le_of_eq hN₁.symm) (DFrame.of_same hm₁ _)).keep hpre B₁.heap
      B₂.heap (le_of_eq hN₂.symm) F₂).keep hpre B₂.heap B₃.heap (le_of_eq hN₃.symm)
      (DFrame.of_same hm₃ _)
  have R₃ : Rest s t₃ (rest10 s c point scale lv lp t) :=
    (((Q.rest.keep fun T hT ↦ transcriptAt_congr hm₁ hT).body hpre B₁ B₂
      (F₂.mono fun a h ↦ w10_body hpre h)).keep fun T hT ↦ transcriptAt_congr hm₃ hT)
  have rg (r : Reg) (hr : r ∈ [Reg.x8, .x22, .x24, .x26, .x27]) : t₃.getReg r = v.getReg r := by
    rw [k₃ r (reg_sub (by decide) hr), hp₂ r (reg_sub (by decide) hr), k₁ r (reg_sub (by decide) hr)]
  have rg2 (r : Reg) (hr : r ∈ [Reg.x9, .x18, .x19, .x20, .x21, .x23, .x25]) :
      t₂.getReg r = v.getReg r := by
    rw [hp₂ r (reg_sub (by decide) hr), k₁ r (reg_sub (by decide) hr)]
  have acc₃ : (t₃.getReg .x18, t₃.getReg .x20, t₃.getReg .x21) =
      limbs (sumE ((List.range (k + 1)).map (atL s lp))) := by
    rw [b8000f85c_x18 h₃, b8000f85c_x20 h₃, b8000f85c_x21 h₃, x2₂, rg2 .x18 (by decide),
      rg2 .x20 (by decide), rg2 .x21 (by decide), sumE_map_succ, limbs_add, ← Q.acc, lG]
    rv_eval []
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> exact BitVec.xor_comm _ _
  have x23₃ : t₃.getReg .x23 = BitVec.ofNat 64 (mOf s lp - (k + 1)) := by
    rw [b8000f85c_x23 h₃, rg2 .x23 (by decide), Q.x23, sub1 hlt]
  have x23₂ : t₂.getReg .x23 - 1 = BitVec.ofNat 64 (mOf s lp - (k + 1)) := by
    rw [rg2 .x23 (by decide), Q.x23, sub1 hlt]
  by_cases hk : k + 1 = mOf s lp
  · refine ⟨t₃, hr₂.trans hr₃, Or.inr (Or.inl {
      pc := b8000f85c_pc_taken h₃ (by rw [x23₂, ← hk, Nat.sub_self]; rfl)
      base := B₃
      fx := X₃
      x8 := by rw [rg .x8 (by decide), Q.x8]
      x22 := by rw [rg .x22 (by decide), Q.x22]
      x26 := by rw [rg .x26 (by decide), Q.x26]
      x27 := by rw [rg .x27 (by decide), Q.x27]
      x24 := by rw [rg .x24 (by decide), Q.x24]
      acc := by rw [acc₃, atLocal_wOf, ← hk]
      rest := R₃ })⟩
  have hk' : k + 1 < mOf s lp := by omega
  have hwl : (wOf s).length = (s.getMem (s.getReg .x15 + 64)).toNat := by
    rw [claim_weights, eListAt_length]
  have hn64 : 64 * (k + 1) < (wOf s).length := by simp only [mOf] at hk'; omega
  refine ⟨t₃, hr₂.trans hr₃, Or.inl {
    pc := b8000f85c_pc_not_taken h₃ (by
      rw [x23₂]
      intro h
      have := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat] at this
      change (mOf s lp - (k + 1)) % 2 ^ 64 = 0 at this
      have := mOf_lt s lp
      omega)
    base := B₃
    fx := X₃
    x8 := by rw [rg .x8 (by decide), Q.x8]
    x22 := by rw [rg .x22 (by decide), Q.x22]
    x26 := by rw [rg .x26 (by decide), Q.x26]
    x27 := by rw [rg .x27 (by decide), Q.x27]
    x24 := by rw [rg .x24 (by decide), Q.x24]
    x9 := by
      rw [b8000f85c_x9 h₃, rg2 .x9 (by decide), Q.x9,
        sub64 (by omega)]
    x19 := by rw [b8000f85c_x19 h₃, rg2 .x19 (by decide), Q.x19, add1536_succ]
    x25 := by
      rw [b8000f85c_x25 h₃, rg2 .x25 (by decide), Q.x25, add24_succ, hm₃,
        F₂ (s.getReg .x2 - 1600) (w10_low hpre (by addr_omega [hb]) (by addr_omega [hb])), hm₁]
    x23 := x23₃
    lt := hk'
    acc := acc₃
    rest := R₃ }⟩

/-- The loop from lane `k`, `j` lanes to go. -/
theorem at_loop (hDt : MultilinearContracts.DotSpec) (hM : MulSpec) {s : MachineState} {ip : Word}
    {c : E} {point lp t : List E} {scale lv : E} {tp tn : Word} (hpre : VerifyLayerPre s) :
    ∀ j k v, k + j = mOf s lp → L10 s v ip c point scale lv lp t tp tn k →
      ∃ u, Reaches Image.code v u ∧ (K10 s u ip c point scale lv lp t tp tn ∨ Dead Image.code u)
  | 0, _, _, hj, L => absurd L.lt (by omega)
  | j + 1, k, v, hj, L => by
    obtain ⟨u, hr, Q | hd⟩ := at_dot hDt hpre L
    · obtain ⟨w, hr', L' | K | hd⟩ := at_mul hM hpre Q
      · obtain ⟨x, hr'', hx⟩ := at_loop hDt hM hpre j (k + 1) w (by omega) L'
        exact ⟨x, hr.trans (hr'.trans hr''), hx⟩
      · exact ⟨w, hr.trans hr', Or.inl K⟩
      · exact ⟨w, hr.trans hr', Or.inr hd⟩
    · exact ⟨u, hr, Or.inr hd⟩

/-- `at_local`, from `J10` to the second check. -/
theorem at_local (hDt : MultilinearContracts.DotSpec) (hM : MulSpec) {s v : MachineState}
    {ip : Word} {c : E} {point lp t : List E} {scale lv : E} (hpre : VerifyLayerPre s)
    (J : J10 s v ip c point scale lp lv t) :
    ∃ u, Reaches Image.code v u ∧
      (K10 s u ip c point scale lv lp t (v.getReg .x24) (v.getReg .x19) ∨ Dead Image.code u) := by
  obtain ⟨u, hr, L | K | hd⟩ := at_start hpre J
  · obtain ⟨w, hr', hw⟩ := at_loop hDt hM hpre (mOf s lp) 0 u (Nat.zero_add _) L
    exact ⟨w, hr.trans hr', hw⟩
  · exact ⟨u, hr, Or.inl K⟩
  · exact ⟨u, hr, Or.inr hd⟩

end Rv64Verifier.Gkr.Layer
