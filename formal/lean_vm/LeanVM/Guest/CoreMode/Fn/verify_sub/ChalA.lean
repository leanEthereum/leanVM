/-
  LeanVM.Guest.CoreMode.Fn.verify_sub.ChalA

  `verify_sub`'s residuals over the link's challenges (`chalFam`), sound at the honest instances of b2c's aligned tree:
  the packed count `g_p = g^p`, `p < 64`, from its `squeeze_packed` call's meaning, and `8p = 88 + n + w + d + j`,
  `j < 8`, from its `vanish` product, so the challenges read lie in the written ones.
-/

module

public import LeanVM.Guest.EndExecExpCA
public import LeanVM.Guest.CoreMode.Fn.verify_sub.Chal
public import LeanVM.Guest.CoreMode.Fn.column_selector.CsChain
public import LeanVM.Guest.B1.VerifySub.PhLinkSpine
public import LeanVM.Guest.B1.Link.SqueezePacked
import Mathlib.Tactic.IntervalCases

namespace LeanVM.Guest.CoreMode.Own.verify_sub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.EndExec
open LeanVM.Guest.CoreMode
open LeanVM.Protocol.Verifier (gen)

public section

set_option maxHeartbeats 1000000 in
/-- **The challenges' count** at an honest instance of `verify_sub`, from its body: `g_p = g^p`, `p < 64` (its
`squeeze_packed` call, `B1.Link.MeaningSP`), and `8p = 88 + n + w + d + j`, `j < 8` (the `vanish` product: `over =
g_p^8 / (g^LINK_FIXED·g_n·g_w·g_d)` one of `g^0, …, g^7`), given `g_n = g^n`, `g_w = g^w`, `g_d = g^d`. -/
theorem vs_chalCount {al : String → Bool} {D : Ref → RefD} {r : Ref} (hR : RefH (layB al) (D r) r) {I : Inst}
    (hI : I ∈ instsR al D r) {σ : Val} {bufs : List ℕ} {kids : List Tree}
    (ht : I.t = .node name% «verify_sub» σ bufs kids) {n w d : ℕ} (hn : n ≤ 48) (hw : w ≤ 24) (hd : d ≤ 9)
    (h408 : σ (.n 408) = gen ^ n) (h409 : σ (.n 409) = gen ^ w) (h484 : σ (.n 484) = gen ^ d) :
    ∃ p j, σ (.n 645) = gen ^ p ∧ p < 64 ∧ j < 8 ∧ 8 * p = 88 + n + w + d + j := by
  obtain ⟨args, rets, hv⟩ := inst_validA hR hI ht
  obtain ⟨-, hb⟩ := Res.holds_of_valid Res.fs_pos hv find_vs
  rw [B1.VerifySub.vs_body_eq, Core.holdsList_append] at hb
  have hpre := ((Core.holdsList_noRet _ B1.VerifySub.vsPre_noRet _ _).mp hb).1
  have hV := vs_slice hpre B1.VerifySub.vsLkVanishT_eq
  simp only [B1.VerifySub.vsLkVanishT, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at hV
  obtain ⟨-, v538, v539, v540, v541, v542, v543, v544, v545, v546, v547, v548, v549, v550, v551, v552,
    v553, v554, v555, v556, v557, v558, v559, v560, v561, v562, v563, v564, v565, v566, v567, v568, v569,
    v570, -, -, -, hsq, -⟩ := hV
  have M := B1.Link.squeeze_packed_sound _ _ _ (Res.KidRel.rel hsq)
  simp only [B1.Link.MeaningSP] at M
  obtain ⟨p, hp, hcg, -⟩ := M
  have hj : ∃ j < 8, σ (.n 653) = gen ^ j := by
    have h0 : σ (.n 676) = 0 := by rw [B1.VerifySub.eq_of_add_zero v570, v569, B1.word_zero]
    rw [v568, v565, v562, v559, v556, v553, v550] at h0
    refine B1.VerifySub.vanish_of (by rw [v547, v546, B1.word_one])
      (by rw [v549, v548, ← B1.VerifySub.word_pow2 (by norm_num)]; rfl)
      (by rw [v552, v551, ← B1.VerifySub.word_pow2 (by norm_num)]; rfl)
      (by rw [v555, v554, ← B1.VerifySub.word_pow2 (by norm_num)]; rfl)
      (by rw [v558, v557, ← B1.VerifySub.word_pow2 (by norm_num)]; rfl)
      (by rw [v561, v560, ← B1.VerifySub.word_pow2 (by norm_num)]; rfl)
      (by rw [v564, v563, ← B1.VerifySub.word_pow2 (by norm_num)]; rfl)
      (by rw [v567, v566, ← B1.VerifySub.word_pow2 (by norm_num)]; rfl) h0
  obtain ⟨j, hj8, x653⟩ := hj
  have h652 : σ (.n 652) = gen ^ (88 + n + w + d) := by
    rw [v544, v543, v542, v541, B1.Link.Arith.word_g88, h408, h409, h484, ← pow_add, ← pow_add, ← pow_add]
    congr 1; ring
  have h8 : gen ^ (8 * p) = gen ^ (j + (88 + n + w + d)) := by
    rw [← B1.VerifySub.pow8 _ p hcg, ← v538, ← v539, ← v540, v545, x653, h652, ← pow_add]
  have e8 := B1.Digest.gen_pow_inj' (by omega) (by omega) h8
  exact ⟨p, j, hcg, hp, hj8, by omega⟩

/-- **The link's chunk count** `g_d` (value `484`, `verify_sub`'s `chunk_d` dispatch on `g_w·g^-19`): `g^d`,
`6 ≤ d ≤ 9`, given `g_w = g^(e + 19)`, `e ≤ 5`. -/
theorem vs_gd {al : String → Bool} {D : Ref → RefD} {r : Ref} (hR : RefH (layB al) (D r) r) {I : Inst}
    (hI : I ∈ instsR al D r) {σ : Val} {bufs : List ℕ} {kids : List Tree}
    (ht : I.t = .node name% «verify_sub» σ bufs kids) {e : ℕ} (he : e ≤ 5) (h409 : σ (.n 409) = gen ^ (e + 19)) :
    ∃ d, 6 ≤ d ∧ d ≤ 9 ∧ σ (.n 484) = gen ^ d := by
  obtain ⟨args, rets, hv⟩ := inst_validA hR hI ht
  obtain ⟨-, hb⟩ := Res.holds_of_valid Res.fs_pos hv find_vs
  rw [B1.VerifySub.vs_body_eq, Core.holdsList_append] at hb
  have hpre := ((Core.holdsList_noRet _ B1.VerifySub.vsPre_noRet _ _).mp hb).1
  have hB := vs_slice hpre B1.VerifySub.vsShapeBT_eq
  simp only [B1.VerifySub.vsShapeBT, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at hB
  obtain ⟨u0, u1, ⟨j, hj, hsel, hcall⟩, -⟩ := hB
  have hj6 : j < 6 := by simpa using hj
  have hje : j = e := by
    refine B1.Digest.gen_pow_inj' (by omega) (by omega) ?_
    rw [Value.gen_pow_eq_ofK, ← hsel, u1, u0, h409, B1.VerifySub.pow_mul_winv19 (by omega)]
    congr 1
  subst hje
  obtain ⟨c, hc, hcd⟩ := B1.VerifySub.chunkD_of_dispatch (fun _ _ _ h ↦ Res.KidRel.rel h) hj6 hcall
  have hall : ∀ w, 19 ≤ w → w ≤ 24 →
      ((LeanVM.Protocol.Verifier.Chunks.new w).map LeanVM.Protocol.Verifier.Chunks.d).all
        (fun x ↦ decide (6 ≤ x ∧ x ≤ 9)) = true := by
    intro w h1 h2; interval_cases w <;> decide +kernel
  have := hall (j + 19) (by omega) (by omega)
  rw [hc] at this
  have h69 : 6 ≤ c.d ∧ c.d ≤ 9 := by simpa using this
  exact ⟨c.d, h69.1, h69.2, hcd⟩

/-- The chunk counts at the pointer widths `19 + e`, `e ≤ 5`: `nuLens`. -/
theorem chunks_nuLens {e : ℕ} (he : e ≤ 5) :
    (LeanVM.Protocol.Verifier.Chunks.new (e + 19)).map LeanVM.Protocol.Verifier.Chunks.d = some (nuLens.getD e 0) := by
  interval_cases e <;> decide +kernel

/-- **The link's chunk count** `g_d` (value `484`) at `g_w = g^(e + 19)`, `e ≤ 5`: `g^nuLens[e]`. -/
theorem vs_gd_nu {al : String → Bool} {D : Ref → RefD} {r : Ref} (hR : RefH (layB al) (D r) r) {I : Inst}
    (hI : I ∈ instsR al D r) {σ : Val} {bufs : List ℕ} {kids : List Tree}
    (ht : I.t = .node name% «verify_sub» σ bufs kids) {e : ℕ} (he : e ≤ 5) (h409 : σ (.n 409) = gen ^ (e + 19)) :
    σ (.n 484) = gen ^ nuLens.getD e 0 := by
  obtain ⟨args, rets, hv⟩ := inst_validA hR hI ht
  obtain ⟨-, hb⟩ := Res.holds_of_valid Res.fs_pos hv find_vs
  rw [B1.VerifySub.vs_body_eq, Core.holdsList_append] at hb
  have hpre := ((Core.holdsList_noRet _ B1.VerifySub.vsPre_noRet _ _).mp hb).1
  have hB := vs_slice hpre B1.VerifySub.vsShapeBT_eq
  simp only [B1.VerifySub.vsShapeBT, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at hB
  obtain ⟨u0, u1, ⟨j, hj, hsel, hcall⟩, -⟩ := hB
  have hj6 : j < 6 := by simpa using hj
  have hje : j = e := by
    refine B1.Digest.gen_pow_inj' (by omega) (by omega) ?_
    rw [Value.gen_pow_eq_ofK, ← hsel, u1, u0, h409, B1.VerifySub.pow_mul_winv19 (by omega)]
    congr 1
  subst hje
  obtain ⟨c, hc, hcd⟩ := B1.VerifySub.chunkD_of_dispatch (fun _ _ _ h ↦ Res.KidRel.rel h) hj6 hcall
  have := chunks_nuLens he
  rw [hc, Option.map_some, Option.some.injEq] at this
  rw [hcd, this]

/-- `verify_sub`'s statements `2903` and `2904`: `link_terminal`'s selector `g_w·g^-19`. -/
def vsNuSelT : List Stmt :=
  [.atom (.const (.n 2892) (word 10248187242686185485 0)), .atom (.mul (.n 2893) (.n 409) (.n 2892))]

theorem vsNuSelT_eq : (B1.VerifySub.vsPre.drop 2903).take 2 = vsNuSelT := B1.stmtsEqb_sound (by decide +kernel)

/-- `g_n`'s split (`vsShapeAT`): `g_n = [412]·kb[2]`. -/
theorem vs_gn_split {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}
    (hA : Stmt.HoldsList C rd σ B1.VerifySub.vsShapeAT True kret) : σ (.n 408) = σ (.n 412) * σ (.n 115) := by
  simp only [B1.VerifySub.vsShapeAT, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at hA
  obtain ⟨-, -, -, -, -, s5, -⟩ := hA
  exact s5

/-- **`nu`'s facts** at an instance, given `g_p = g^p`, `g_n = g^n`: `[108]·[460]·g = g_w = g^w`, `19 ≤ w ≤ 24`,
`link_terminal`'s selector `[2893] = g^(w - 19)`, `88 + n + w + d ≤ 8p` at the chunk count `d = nuLens[w - 19]`. -/
def NuFacts (σ : Val) (p n : ℕ) : Prop :=
  ∃ w, 19 ≤ w ∧ w ≤ 24 ∧ σ (.n 108) * σ (.n 460) * gen = gen ^ w ∧ σ (.n 2893) = gen ^ (w - 19) ∧
    88 + n + w + nuLens.getD (w - 19) 0 ≤ 8 * p

/-- **The challenges' facts** at an instance: `g_p = g^p`, `p < 64`, `kb[2]·[412] = g^n` (`g_n`), `113 + n ≤ 8p`, and
`nu`'s. -/
def ChalFacts (σ : Val) : Prop :=
  ∃ p n, σ (.n 645) = gen ^ p ∧ p < 64 ∧ σ (.n 115) * σ (.n 412) = gen ^ n ∧ n ≤ 48 ∧ 113 + n ≤ 8 * p ∧
    NuFacts σ p n

/-- **The challenges' facts at an honest instance** of `verify_sub`, from `g_n = g^n`, `n ≤ 48`, `g_w = g^(e + 19)`,
`e ≤ 5`, and `g_n`'s split. -/
theorem chalFacts_of {al : String → Bool} {D : Ref → RefD} {r : Ref} (hR : RefH (layB al) (D r) r) {I : Inst}
    (hI : I ∈ instsR al D r) {σ : Val} {bufs : List ℕ} {kids : List Tree}
    (ht : I.t = .node name% «verify_sub» σ bufs kids) {n e : ℕ} (hn : n ≤ 48) (he : e ≤ 5)
    (h408 : σ (.n 408) = gen ^ n) (h409 : σ (.n 409) = gen ^ (e + 19))
    (hsplit : σ (.n 408) = σ (.n 412) * σ (.n 115)) : ChalFacts σ := by
  obtain ⟨d, hd6, hd9, h484⟩ := vs_gd hR hI ht he h409
  obtain ⟨p, j, hp, hp64, hj, h8⟩ := vs_chalCount hR hI ht hn (by omega : e + 19 ≤ 24) hd9 h408 h409 h484
  have hdn : d = nuLens.getD e 0 :=
    B1.Digest.gen_pow_inj' (by omega) (by interval_cases e <;> decide)
      (h484.symm.trans (vs_gd_nu hR hI ht he h409))
  obtain ⟨args, rets, hv⟩ := inst_validA hR hI ht
  obtain ⟨-, hb⟩ := Res.holds_of_valid Res.fs_pos hv find_vs
  rw [B1.VerifySub.vs_body_eq, Core.holdsList_append] at hb
  have hpre := ((Core.holdsList_noRet _ B1.VerifySub.vsPre_noRet _ _).mp hb).1
  have hmem : σ (.n 101) = σ (.n 108) * gen := (B1.VerifySub.readsFacts (vs_slice hpre B1.VerifySub.vsReadsT_eq)).memMul
  have hA := vs_slice hpre B1.VerifySub.vsShapeAT_eq
  simp only [B1.VerifySub.vsShapeAT, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at hA
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, s40, -⟩ := hA
  have hS := vs_slice hpre vsNuSelT_eq
  simp only [vsNuSelT, Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hS
  obtain ⟨u0, u1, -⟩ := hS
  refine ⟨p, n, hp, hp64, by rw [mul_comm, ← hsplit, h408], hn, by omega, e + 19, by omega, by omega, ?_, ?_, ?_⟩
  · rw [← h409, s40, hmem]; ring
  · rw [u1, u0, h409, B1.VerifySub.pow_mul_winv19 (by omega)]
  · rw [show e + 19 - 19 = e by omega, ← hdn]; omega

/-- A cell of a run `⟨M·g^c, 1, lo, m⟩` over constants, `M` the bases' word: `x = M·g^(c + i)`, `i < m`. -/
theorem runSet_const1 {w : ℕ → E} {bs : List (ℕ × ℕ)} {c lo m : ℕ} (hm : m < capE) {x : K}
    (h : CRun.Set w ⟨⟨bs, c⟩, 1, .num lo, .num m⟩ x) :
    ∃ i < m, x = (prodW w bs * gen ^ (c + i)).limb 0 := by
  simp only [CRun.Set, RunSet] at h
  obtain ⟨ylo, yhi, i, -, hhi, -, him, rfl⟩ := h
  simp only [idxC] at hhi
  rw [rep_const hm, Option.some.injEq] at hhi
  subst hhi
  refine ⟨i, him, ?_⟩
  simp only [CCell.valW, ← Value.gen_pow_eq_ofK, mul_assoc, ← pow_add, one_mul]

/-- A cell's word: its bases' word times `g^off`. -/
theorem valW_gen {w : ℕ → E} {bs : List (ℕ × ℕ)} {c : ℕ} : CCell.valW w ⟨bs, c⟩ = prodW w bs * gen ^ c := by
  simp only [CCell.valW]
  rw [Value.gen_pow_eq_ofK]

/-- The written run's upper bound: `g_p^8 = g^(8p)`. -/
theorem chalRun_hi {σ : Val} {p : ℕ} (hp : σ (.n 645) = gen ^ p) (hp64 : p < 64) :
    rep ((idxC chalRun.hi).valW (vw σ)) = some (8 * p) := by
  have hw : (idxC chalRun.hi).valW (vw σ) = gen ^ (8 * p) := by
    rw [show idxC chalRun.hi = ⟨[(645, 8)], 0⟩ from rfl, valW_gen, pow_zero, mul_one]
    simp only [prodW, vw, mul_one, hp, ← pow_mul]
    rw [mul_comm]
  rw [hw, Value.gen_pow_eq_ofK]
  exact rep_of (by unfold capE; omega)

/-- **A run of challenges read lies in the written one** (`chalRead q`), given the challenges' facts. -/
theorem chalRead_sub {σ : Val} (F : ChalFacts σ) {q : CRun} (hq : chalRead q = true) :
    (CRes.subR q chalRun).Holds σ := by
  obtain ⟨p, n, hp, hp64, hn, hn48, h8, -⟩ := F
  obtain ⟨⟨bs, c⟩, S, lo, hi⟩ := q
  cases lo <;> cases hi <;> simp only [chalRead, Bool.false_eq_true] at hq
  rename_i lo m
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Nat.beq_eq, Nat.ble_eq] at hq
  obtain ⟨⟨⟨hbs, rfl⟩, hc⟩, hcm⟩ := hq
  intro x hx
  obtain ⟨i, him, rfl⟩ := runSet_const1 (by unfold capE; omega) hx
  -- the bases' word: `chal·g^b`, `b` zero or `n`
  obtain ⟨b, hb, hw⟩ : ∃ b ≤ n, prodW (vw σ) bs = σ (.n 10) * gen ^ b := by
    rcases hbs with rfl | rfl
    · exact ⟨0, Nat.zero_le _, by simp [prodW, vw]⟩
    · refine ⟨n, le_refl _, ?_⟩
      simp only [prodW, vw, pow_one, mul_one]
      rw [hn]
  have hcell : prodW (vw σ) bs * gen ^ (c + i) =
      chalRun.base.valW (vw σ) * ofK (addressOfIndex (chalRun.stride * (c - 1 + b + i))) := by
    have h10 : prodW (vw σ) [(10, 1)] = σ (.n 10) := by simp [prodW, vw]
    rw [hw, show chalRun.base = ⟨[(10, 1)], 1⟩ from rfl, show chalRun.stride = 1 from rfl, valW_gen,
      ← Value.gen_pow_eq_ofK, h10, mul_assoc, mul_assoc, ← pow_add, ← pow_add,
      show 1 + 1 * (c - 1 + b + i) = b + (c + i) by omega]
  rw [hcell]
  exact runSet_of (rep_const (by unfold capE; omega)) (chalRun_hi hp hp64) (Nat.zero_le _) (by omega)

/-- **A run of `nu` read under `link_terminal`'s arm lies in the written challenges** (`nuRead g q`), given the
challenges' facts and the branch conditions. -/
theorem nuRead_sub {σ : Val} (F : ChalFacts σ) {g : List CCond} (hg : ∀ c ∈ g, c.Holds σ) {q : CRun}
    (hq : nuRead g q = true) : (CRes.subR q chalRun).Holds σ := by
  obtain ⟨p, n, hp, hp64, hn, hn48, -, w, hw19, hw24, hw, hsel, h8⟩ := F
  obtain ⟨⟨bs, c⟩, S, lo, hi⟩ := q
  cases lo <;> cases hi <;> simp only [nuRead, Bool.false_eq_true] at hq
  rename_i lo m
  simp only [Bool.and_eq_true, beq_iff_eq, Nat.beq_eq, List.any_eq_true] at hq
  obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, a, ha, hm⟩ := hq
  obtain ⟨j, hj6, hmj, rfl⟩ : ∃ j, j < 6 ∧ m ≤ nuLens.getD j 0 ∧ a = .arm 2893 j := by
    cases a with
    | arm x j =>
      simp only [Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq, Nat.ble_eq] at hm
      obtain ⟨⟨rfl, h1⟩, h2⟩ := hm
      exact ⟨j, h1, h2, rfl⟩
    | zero _ => simp at hm
    | nonzero _ => simp at hm
  have harm : σ (.n 2893) = ofK (addressOfIndex j) := hg _ ha
  have hj : w - 19 = j :=
    B1.Digest.gen_pow_inj' (by omega) (by omega) (by rw [← hsel, harm, Value.gen_pow_eq_ofK])
  subst hj
  have hm9 : nuLens.getD (w - 19) 0 ≤ 9 := by interval_cases w <;> decide
  intro x hx
  obtain ⟨i, him, rfl⟩ := runSet_const1 (by unfold capE; omega) hx
  have hcell : prodW (vw σ) nuBases * gen ^ (90 + i) =
      chalRun.base.valW (vw σ) * ofK (addressOfIndex (chalRun.stride * (n + w + 88 + i))) := by
    rw [show chalRun.base = ⟨[(10, 1)], 1⟩ from rfl, show chalRun.stride = 1 from rfl, valW_gen,
      ← Value.gen_pow_eq_ofK]
    simp only [prodW, nuBases, vw, pow_one, mul_one, one_mul]
    have e1 : σ (.n 108) * (σ (.n 115) * (σ (.n 412) * σ (.n 460))) * gen = gen ^ (n + w) := by
      rw [pow_add, ← hn, ← hw]; ring
    calc σ (.n 10) * (σ (.n 108) * (σ (.n 115) * (σ (.n 412) * σ (.n 460)))) * gen ^ (90 + i)
        = σ (.n 10) * (σ (.n 108) * (σ (.n 115) * (σ (.n 412) * σ (.n 460))) * gen) * gen ^ (89 + i) := by
          rw [show 90 + i = 89 + i + 1 by omega, pow_succ]; ring
      _ = σ (.n 10) * gen ^ (n + w) * gen ^ (89 + i) := by rw [e1]
      _ = σ (.n 10) * gen * gen ^ (n + w + 88 + i) := by
          have : gen ^ (n + w) * gen ^ (89 + i) = gen * gen ^ (n + w + 88 + i) := by
            rw [← pow_add, ← pow_succ', show n + w + (89 + i) = n + w + 88 + i + 1 by omega]
          rw [mul_assoc, this, ← mul_assoc]
  rw [hcell]
  exact runSet_of (rep_const (by unfold capE; omega)) (chalRun_hi hp hp64) (Nat.zero_le _) (by omega)

/-- **`chalFam` holds** where the challenges' facts do. -/
theorem chalFam_holds {σ : Val} (F : ChalFacts σ) : ∀ {x : CRes}, chalFam x = true → x.Holds σ
  | .lt (.val y) (.num m), hx => by
    obtain ⟨p, -, hp, hp64, -⟩ := F
    have hy : (y, m) ∈ chalBounds := List.contains_iff_mem.mp hx
    simp only [chalBounds, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hy
    obtain ⟨rfl, rfl⟩ := hy
    exact ltF_of_pow (by decide) hp64 (hp.trans (Value.gen_pow_eq_ofK _))
  | .lt (.num k) (.val v), hx => by
    obtain ⟨p, n, hp, hp64, -, -, h8, -⟩ := F
    simp only [chalFam, Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at hx
    obtain ⟨rfl, hk⟩ := hx
    have hw : (idxC (.val 645)).valW (vw σ) = gen ^ p := by
      rw [show idxC (.val 645) = ⟨[(645, 1)], 0⟩ from rfl, valW_gen, pow_zero, mul_one]
      simp [prodW, vw, hp]
    refine ⟨k, p, rep_const (by unfold capE; omega), ?_, by omega⟩
    rw [hw, Value.gen_pow_eq_ofK]
    exact rep_of (by unfold capE; omega)
  | .subR q r, hx => by
    simp only [chalFam, Bool.and_eq_true, decide_eq_true_eq] at hx
    obtain ⟨hq, rfl⟩ := hx
    exact chalRead_sub F hq
  | .under g (.subR q r), hx => by
    simp only [chalFam, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hx
    obtain ⟨hq | hq, rfl⟩ := hx
    · exact fun _ ↦ chalRead_sub F hq
    · exact fun hg ↦ nuRead_sub F hg hq
  | .under _ (.lt _ _), hx | .under _ (.nz _), hx | .under _ (.sub _ _), hx | .under _ (.under _ _), hx
  | .under _ (.subP _ _), hx | .under _ (.eq _ _), hx => by
    simp only [chalFam] at hx
    exact fun _ ↦ chalFam_holds F hx
  | .lt (.num _) (.num _), hx | .lt (.num _) (.mono _), hx | .lt (.val _) (.val _), hx
  | .lt (.val _) (.mono _), hx | .lt (.mono _) _, hx | .nz _, hx | .sub _ _, hx | .subP _ _, hx
  | .eq _ _, hx => by simp [chalFam] at hx

end

end LeanVM.Guest.CoreMode.Own.verify_sub
