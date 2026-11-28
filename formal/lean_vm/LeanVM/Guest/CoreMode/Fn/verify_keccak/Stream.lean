/-
  LeanVM.Guest.CoreMode.Fn.verify_keccak.Stream

  `verify_keccak`'s stream family (`Fam.lean`'s `stFam`) sound: at a valuation whose head's values are the powers
  `stEx h` gives (`StEx σ h`, `9 ≤ h ≤ 24`), each read and run it takes lies in the stream's run `stQ`
  (`stFam_holds`); at an honest instance the head's values are those powers (`vk_stEx`).
-/

module

public import LeanVM.Guest.CoreMode.Fn.verify_keccak.Runs
public import LeanVM.Guest.B1.Link.RoundsLoop
public import LeanVM.Guest.B1.Digest.Range

namespace LeanVM.Guest.CoreMode.Own.verify_keccak

open LeanVM.Parameters LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.EndExec LeanVM.Guest.B1.VerifySub
open LeanVM.Guest.Value (gen_pow_eq_ofK)
open LeanVM.Protocol.Verifier (gen)

public section

/-- **The head's values are their powers** at height `h`. -/
def StEx (σ : Val) (h : ℕ) : Prop := ∀ v e, stEx h v = some e → σ (.n v) = gen ^ e

theorem stSum_val {σ : Val} {h : ℕ} (hE : StEx σ h) :
    ∀ (bs : List (ℕ × ℕ)) {s : ℕ}, stSum h bs = some s → prodW (vw σ) bs = gen ^ s
  | [], s, hs => by
    simp only [stSum, Option.some.injEq] at hs
    subst hs
    simp [prodW]
  | (v, a) :: l, s, hs => by
    simp only [stSum] at hs
    cases he : stEx h v with
    | none => simp [he] at hs
    | some e =>
      cases hl : stSum h l with
      | none => simp [he, hl] at hs
      | some t =>
        simp only [he, hl, Option.some.injEq] at hs
        subst hs
        simp only [prodW, vw]
        rw [hE v e he, stSum_val hE l hl, ← pow_mul, ← pow_add, mul_comm e a]

theorem stIdx_val {σ : Val} {h : ℕ} (hE : StEx σ h) :
    ∀ {i : CIdx} {n : ℕ}, stIdx h i = some n → (idxC i).valW (vw σ) = gen ^ n
  | .num n, m, hn => by
    simp only [stIdx, Option.some.injEq] at hn
    subst hn
    simp [idxC, CCell.valW, prodW, gen_pow_eq_ofK]
  | .val v, m, hn => by
    simp only [stIdx] at hn
    show (baseC v).valW (vw σ) = _
    rw [valW_baseC, vw, hE v m hn]
  | .mono c, m, hn => by
    simp only [stIdx] at hn
    cases hs : stSum h c.bases with
    | none => simp [hs] at hn
    | some s =>
      simp only [hs, Option.map_some, Option.some.injEq] at hn
      subst hn
      show c.valW (vw σ) = _
      rw [CCell.valW, stSum_val hE c.bases hs, ← gen_pow_eq_ofK, ← pow_add]

theorem rep_genE {n : ℕ} (hn : n < 4294967296) : rep (gen ^ n) = some n := by
  rw [gen_pow_eq_ofK]; exact rep_of (by unfold capE; omega)

theorem stQ_hi {σ : Val} {h : ℕ} (h24 : h ≤ 24) (hE : StEx σ h) :
    rep ((idxC stQ.hi).valW (vw σ)) = some (24 * (h + 44)) := by
  have : stIdx h stQ.hi = some (24 * (h + 44)) := by
    simp [stQ, stIdx, stSum, stEx]; omega
  rw [stIdx_val hE this, rep_genE (by omega)]

/-- **A run `stRunOk` takes lies in the stream's run** at a valuation of height `h`. -/
theorem stRun_sub {σ : Val} {h : ℕ} (h9 : 9 ≤ h) (h24 : h ≤ 24) (hE : StEx σ h) {q : CRun}
    (hq : stRunOk q = true) : ∀ x, q.Set (vw σ) x → stQ.Set (vw σ) x := by
  have hq' : stRunAt q h = true := by
    have := List.all_eq_true.mp hq (h - 9) (List.mem_range.mpr (by omega))
    rwa [show 9 + (h - 9) = h by omega] at this
  unfold stRunAt at hq'
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hq'
  obtain ⟨hhd, hm⟩ := hq'
  have hb : q.base.bases = (5, 1) :: q.base.bases.tail := by
    cases hbs : q.base.bases with
    | nil => rw [hbs] at hhd; cases hhd
    | cons b l => rw [hbs] at hhd; cases hhd; rfl
  cases ht : stSum h q.base.bases.tail with
  | none => simp [ht] at hm
  | some t =>
  cases hl : stIdx h q.lo with
  | none => simp [ht, hl] at hm
  | some l =>
  cases hu : stIdx h q.hi with
  | none => simp [ht, hl, hu] at hm
  | some u =>
  simp only [ht, hl, hu, Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq, Nat.ble_eq] at hm
  obtain ⟨⟨hu32, hl32⟩, hlu⟩ := hm
  intro x hx
  obtain ⟨ylo, yhi, j, e1, e2, hj1, hj2, rfl⟩ := hx
  rw [stIdx_val hE hl, rep_genE hl32, Option.some.injEq] at e1
  rw [stIdx_val hE hu, rep_genE hu32, Option.some.injEq] at e2
  subst e1 e2
  have hlt : t + q.base.off + q.stride * j < 24 * (h + 44) := by
    rcases hlu with hlu | hlu
    · omega
    · have : q.stride * j ≤ q.stride * (u - 1) := Nat.mul_le_mul_left _ (by omega)
      omega
  refine ⟨0, 24 * (h + 44), t + q.base.off + q.stride * j, rep_const (by unfold capE; omega), stQ_hi h24 hE,
    Nat.zero_le _, hlt, ?_⟩
  have hv : q.base.valW (vw σ) = σ (.n 5) * gen ^ (t + q.base.off) := by
    rw [CCell.valW, hb]
    simp only [prodW, vw, pow_one]
    rw [stSum_val hE _ ht, ← gen_pow_eq_ofK, pow_add]
    ring
  have hq0 : stQ.base.valW (vw σ) = σ (.n 5) := by
    rw [CCell.valW, ← gen_pow_eq_ofK]
    simp [stQ, prodW, vw]
  refine congrArg (fun z : E ↦ z.limb 0) ?_
  rw [hv, hq0, ← gen_pow_eq_ofK, ← gen_pow_eq_ofK]
  simp only [stQ, one_mul]
  ring

/-- **A bound `stLt` holds** at a valuation of height `h`. -/
theorem stLt_holds {σ : Val} {h : ℕ} (h9 : 9 ≤ h) (h24 : h ≤ 24) (hE : StEx σ h) :
    ∀ {a b : CIdx}, stLt a b = true → (CRes.lt a b).Holds σ
  | .mono c, .num n, hx => by
    simp only [stLt, Bool.and_eq_true, Nat.blt_eq, List.all_eq_true, List.mem_range] at hx
    obtain ⟨hn, hall⟩ := hx
    have hh := hall (h - 9) (by omega)
    rw [show 9 + (h - 9) = h by omega] at hh
    cases ht : stIdx h (.mono c) with
    | none => rw [ht] at hh; cases hh
    | some t =>
      rw [ht] at hh
      have htn : t < n := Nat.blt_eq.mp hh
      refine ⟨t, n, ?_, rep_const (by unfold capE; omega), htn⟩
      rw [stIdx_val hE ht, gen_pow_eq_ofK]
      exact rep_of (by unfold capE; omega)
  | .num _, _, hx => by simp [stLt] at hx
  | .val _, _, hx => by simp [stLt] at hx
  | .mono _, .val _, hx => by simp [stLt] at hx
  | .mono _, .mono _, hx => by simp [stLt] at hx

/-- **The stream family holds** at a valuation of height `h`. -/
theorem stFam_holds {σ : Val} {h : ℕ} (h9 : 9 ≤ h) (h24 : h ≤ 24) (hE : StEx σ h) :
    ∀ {x : CRes}, stFam x = true → x.Holds σ
  | .sub c r, hx => by
    simp only [stFam, Bool.and_eq_true, decide_eq_true_eq] at hx
    obtain ⟨rfl, hq⟩ := hx
    refine stRun_sub h9 h24 hE hq _ ⟨0, 1, 0, rep_const (by unfold capE; omega),
      rep_const (by unfold capE; omega), le_refl _, zero_lt_one, ?_⟩
    rw [CCell.addrW, mul_zero, ← gen_pow_eq_ofK, pow_zero, mul_one]
  | .subR q r, hx => by
    simp only [stFam, Bool.and_eq_true, decide_eq_true_eq] at hx
    obtain ⟨rfl, hq⟩ := hx
    exact stRun_sub h9 h24 hE hq
  | .under _ r, hx => fun _ ↦ stFam_holds h9 h24 hE hx
  | .lt a b, hx => stLt_holds (a := a) (b := b) h9 h24 hE hx
  | .nz _, hx => by simp [stFam] at hx
  | .subP _ _, hx => by simp [stFam] at hx
  | .eq _ _, hx => by simp [stFam] at hx

/-! ## At an honest instance -/

variable {al : String → Bool} {D : Ref → RefD}

/-- A pinned bit's factor `1 + b·(1 + g^a)`, as `1 + b·(g^a + 1)`. -/
theorem word_bitF {a : ℕ} (ha : a < 64) : word (2 ^ a ^^^ 1) 0 = gen ^ a + 1 :=
  B1.Link.word_two_pow_xor_one ha

/-- **The head's values are their powers** at an honest instance with `tau_g = g^h`, `9 ≤ h ≤ 24`. -/
theorem vk_stEx {r : Ref} (hR : RefH (layB al) (D r) r) {I : Inst} (hI : I ∈ instsR al D r) {σ : Val}
    {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node "verify_keccak" σ bufs kids) {h : ℕ} (h1 : 9 ≤ h)
    (h2 : h ≤ 24) (htg : σ (.n 6) = gen ^ h) : StEx σ h := by
  obtain ⟨-, e29, e48⟩ := vk_exps hR hI ht h1 h2 htg
  rw [show krStep = 16 from rfl] at e29 e48
  obtain ⟨args, rets, fn', hf', -, es, vs, hw, -, hh, -⟩ := inst_validA hR hI ht
  obtain rfl : fn' = fn% «verify_keccak» := Option.some.inj (hf'.symm.trans EndExec.find_vk)
  have hall : ∀ a ∈ LeanVM.Guest.Res.topAtoms (fn% «verify_keccak»).body, a.Holds r.img.read σ :=
    fun a ha ↦ hh _ (LeanVM.Guest.EndExec.topAtoms_on_path hw ha)
  -- each bit factor `1 + b·(g^(2^j) + 1) = g^(2^j·[b = 1])`, `b = b·b`
  have bit : ∀ (b w c p d : ℕ) (k : ℕ), k < 4 →
      Atom.mul (.n b) (.n b) (.n b) ∈ LeanVM.Guest.Res.topAtoms (fn% «verify_keccak»).body →
      Atom.const (.n w) (word 1 0) ∈ LeanVM.Guest.Res.topAtoms (fn% «verify_keccak»).body →
      Atom.const (.n c) (word (2 ^ (2 ^ k) ^^^ 1) 0) ∈ LeanVM.Guest.Res.topAtoms (fn% «verify_keccak»).body →
      Atom.mul (.n p) (.n b) (.n c) ∈ LeanVM.Guest.Res.topAtoms (fn% «verify_keccak»).body →
      Atom.add (.n d) (.n w) (.n p) ∈ LeanVM.Guest.Res.topAtoms (fn% «verify_keccak»).body →
      ∃ β ≤ 1, σ (.n d) = gen ^ (2 ^ k * β) := by
    intro b w c p d k hk mb mw mc mp md
    have ab := hall _ mb
    have aw := hall _ mw
    have ac := hall _ mc
    have ap := hall _ mp
    have ad := hall _ md
    simp only [Atom.Holds] at ab aw ac ap ad
    refine ⟨if σ (.n b) = 1 then 1 else 0, by split_ifs <;> omega, ?_⟩
    rw [ad, aw, ap, ac, B1.word_one, word_bitF (by interval_cases k <;> norm_num)]
    exact B1.Link.bit_factor ab _
  obtain ⟨β0, hβ0, e33⟩ := bit 21 30 31 32 33 0 (by norm_num) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  obtain ⟨β1, hβ1, e37⟩ := bit 22 34 35 36 37 1 (by norm_num) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  obtain ⟨β2, hβ2, e42⟩ := bit 23 39 40 41 42 2 (by norm_num) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  obtain ⟨β3, hβ3, e47⟩ := bit 24 44 45 46 47 3 (by norm_num) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have m38 := hall (.mul (.n 38) (.n 33) (.n 37)) (by decide +kernel)
  have m43 := hall (.mul (.n 43) (.n 38) (.n 42)) (by decide +kernel)
  have m48 := hall (.mul (.n 48) (.n 43) (.n 47)) (by decide +kernel)
  simp only [Atom.Holds] at m38 m43 m48
  norm_num at e33 e37 e42 e47
  -- the bits are `y % 16`'s
  have hsum : β0 + 2 * β1 + 4 * β2 + 8 * β3 = (h - 3) % 16 := by
    refine B1.Digest.gen_pow_inj' (by omega) (by omega) ?_
    rw [← e48, m48, m43, m38, e33, e37, e42, e47, ← pow_add, ← pow_add, ← pow_add]
  have gp : ∀ {a b : ℕ}, a = b → gen ^ a = gen ^ b := fun h ↦ h ▸ rfl
  intro v e hv
  unfold stEx at hv
  split_ifs at hv with v6 v29 v48 v33 v37 v42 v47
  · cases hv; subst v6; exact htg
  · cases hv; subst v29; exact e29
  · cases hv; subst v48; exact e48
  · cases hv; subst v33; exact e33.trans (gp (by omega))
  · cases hv; subst v37; exact e37.trans (gp (by omega))
  · cases hv; subst v42; exact e42.trans (gp (by omega))
  · cases hv; subst v47; exact e47.trans (gp (by omega))

end

end LeanVM.Guest.CoreMode.Own.verify_keccak
