/-
  LeanVM.Guest.B1.Digest.MonoCLasts

  `child_claim_list_mono_last__L{k}`'s honest valuation, with where its loads read, and its
  placed completeness.
-/

module

public import LeanVM.Guest.B1.Digest.MonoCLast
public import LeanVM.Guest.B1.Digest.ChildListAt0

/-!
# The walk's last claims, completely

`mlc_core`: from the record at `rec = g^rP` (the state after whole blocks `pre`, the pointers at
`mStart o s`) and `k` honest claims, the body's evaluated valuation holds its atoms and returns
the digest of `pre` and their cells: the walk's end `region · g^(mStart o (s + k))` divided by the
region is `g^(mStart o (s + k))`, range-checked against `limit = g^L` (reading below `L + 1`).
`mlc_completeAtB`: a leaf within its frame.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Memory LeanVM.Guest.B1.Fwd
open LeanVM.Guest.B1 (CompleteAtD CompleteAtDTB Returns LowDef)
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Guest.B1.Da (limb0_gen_pow_mul relAtIn_atoms)

@[expose] public section

variable {rd : Reader}

/-- `child_claim_list_mono_last__L{k}`'s atoms. -/
noncomputable def mlAtoms (k : ℕ) : List Atom :=
  ((splitBody (coreProgram.getD (idx% «child_claim_list_mono_last__L0» + k) default).body).map
      (·.1)).getD []

set_option maxRecDepth 100000 in
theorem ml_shape_all : ∀ k < 17, ((mlAtoms k).all (fun a => !Memory.atomAllocB a &&
    (Memory.atomAddr? a).isNone) && ((coreProgram.getD (idx% «child_claim_list_mono_last__L0» + k)
        default).loop == false)) = true := by
  decide +kernel

theorem ml_name {k : ℕ} (hk : k < 17) :
    coreProgram.find? (mlNames.getD k "") = some (coreProgram.getD
        (idx% «child_claim_list_mono_last__L0» + k) default) :=
  find_of_idx (ml_idx k hk)

theorem ml_loop {k : ℕ} (hk : k < 17) : coreProgram.loop (mlNames.getD k "") = false := by
  rw [Program.loop_of_find? (ml_name hk)]
  have := ml_shape_all k hk
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  exact this.2

theorem ml_na {k : ℕ} (hk : k < 17) : (mlAtoms k).all (fun a => !Memory.atomAllocB a) = true := by
  have := ml_shape_all k hk
  simp only [Bool.and_eq_true, List.all_eq_true] at this
  exact List.all_eq_true.mpr fun a ha => (this.1 a ha).1

theorem ml_addr {k : ℕ} (hk : k < 17) : (mlAtoms k).filterMap Memory.atomAddr? = [] := by
  have := ml_shape_all k hk
  simp only [Bool.and_eq_true, List.all_eq_true, Option.isNone_iff_eq_none] at this
  exact List.filterMap_eq_nil_iff.mpr fun a ha => (this.1 a ha).2

theorem mlc_all {k : ℕ} (hk : k < 17) :
    mlcOk k (coreProgram.getD (idx% «child_claim_list_mono_last__L0» + k) default) = true := by
  rcases Nat.lt_or_ge k 9 with h | h
  · exact mlc_lo k h
  · have := mlc_hi (k - 9) (by omega)
    rwa [show 9 + (k - 9) = k by omega] at this

/-- **A range check of `x = g^a` against `kk = g^b`, `a ≤ b`, holds** on a memory defined below
`b + 1`. -/
theorem rc_holds {S : List Atom} {w : ℕ → E} {σ : Val} {x y t1 t2 kk : V} {a b : ℕ}
    (hg : Good rd S w σ (.rangeCheck x y t1 t2 kk)) (hky : kk.idx < y.idx)
    (hx : σ x = gen ^ a) (hk : σ kk = gen ^ b) (hab : a ≤ b) (hdef : BoundMem rd (b + 1)) :
    (Atom.rangeCheck x y t1 t2 kk).Holds rd σ := by
  simp only [Good] at hg
  rw [ite_pos' hky] at hg
  obtain ⟨h1, h2, h3⟩ := hg
  have hga : gen ^ a ≠ 0 := pow_ne_zero _ gen_ne_zero
  have hyv : σ y = gen ^ (b - a) := by
    rw [h3, hk, hx, show b = b - a + a by omega, pow_add, mul_assoc, mul_inv_cancel₀ hga,
      mul_one, Nat.add_sub_cancel]
  obtain ⟨t1', ht1⟩ := hdef a (by omega)
  obtain ⟨t2', ht2⟩ := hdef (b - a) (by omega)
  refine ⟨?_, ?_, ?_⟩
  · rw [h1, hx, rdAt_of_load ht1]; exact ht1
  · rw [hk, hx, hyv, ← pow_add, show a + (b - a) = b by omega]
  · rw [h2, hyv, rdAt_of_load ht2]; exact ht2

theorem endOf_mem {atoms : List Atom} {ce t : V} (h : endOf atoms ce = some t) :
    Atom.mul ce t (.n 1) ∈ atoms := by
  obtain ⟨a, ha, hs⟩ := List.exists_of_findSome?_eq_some h
  cases a <;> simp only [reduceCtorEq] at hs
  split at hs
  · rename_i hd
    obtain ⟨h1, h2⟩ := hd
    obtain rfl := Option.some.inj hs
    subst h1 h2
    exact ha
  · exact absurd hs (by simp)

/-- The quotient `t` of the walk's end by the region. -/
theorem endOf_val {S : List Atom} {w : ℕ → E} {σ : Val} {atoms : List Atom} {ce t : V}
    (h : endOf atoms ce = some t) (hg : ∀ a ∈ atoms, Good rd S w σ a) (h1 : σ (.n 1) ≠ 0) :
    σ t = σ ce * (σ (.n 1))⁻¹ := by
  have := hg _ (endOf_mem h)
  simp only [Good] at this
  split at this
  · rw [this, mul_assoc, mul_inv_cancel₀ h1, mul_one]
  · exact this

theorem mlcSide_load {k : ℕ} {t : Option V} {d p : V} {off : ℕ}
    (h : mlcSide k t (.load d p off) = true) : p = .n 0 ∧ off < 15 := by
  simpa [mlcSide] using h

set_option maxRecDepth 20000 in
/-- **The walk's last claims' honest valuation** (`[rec, region, mark, limit]`), with where its
loads read. -/
theorem mlc_core {k : ℕ} (hk : k < 17) {rec region mark limit entries : E} {rP eP rg L s : ℕ}
    {o : ℕ → ℕ} (hrc : rec = gen ^ rP) (hen : entries = gen ^ eP) (hrg : region = gen ^ rg)
    (hlim : limit = gen ^ L) {n : ℕ} {pre : List UInt8} (hpre : pre.length = rate * n)
    (hR : MonoRecAt rd rec n pre region entries (mStart o s)) {cells : List E}
    (hl : cells.length = 4 * k) (hinc : ∀ i < k, mStart o (s + i) ≤ o (s + i))
    (hrec : MRec rd region L entries mark k (fun i => o (s + i)) cells)
    (hend : mStart o (s + k) ≤ L) (hdef : BoundMem rd (L + 1)) :
    ∃ (vs : List V) (σ : Val),
      (coreProgram.getD (idx% «child_claim_list_mono_last__L0» + k) default).body =
          (mlAtoms k).map Stmt.atom ++ [.ret vs] ∧
      (coreProgram.getD (idx% «child_claim_list_mono_last__L0» + k) default).params.map σ =
          [rec, region, mark, limit] ∧
      (∀ a ∈ mlAtoms k, a.Holds rd σ) ∧
      vs.map σ = digestCells (keccak256 (pre ++ cellsBytes cells)) ∧
      ∀ q ∈ (mlAtoms k).filterMap Memory.atomLoad?,
        (∃ c < 15, (σ q.1).limb 0 * addressOfIndex q.2 = addressOfIndex (rP + c)) ∨
        (∃ i < k, (σ q.1).limb 0 * addressOfIndex q.2 = addressOfIndex (rg + o (s + i))) ∨
        (∃ i < k, ∃ c < 4,
          (σ q.1).limb 0 * addressOfIndex q.2 = addressOfIndex (eP + 4 * o (s + i) + c)) := by
  obtain ⟨hS, h13, h14⟩ := hR
  have hok := ml_all k hk
  have hcok := mlc_all hk
  set fn := coreProgram.getD (idx% «child_claim_list_mono_last__L0» + k) default
  simp only [mlOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hpar, hok⟩ := hok
  simp only [mlcOk, Bool.and_eq_true, Option.isSome_iff_exists] at hcok
  obtain ⟨⟨c', hchk⟩, hcok⟩ := hcok
  split at hok
  · rename_i atoms r0 r1 hsb
    rw [hsb] at hcok
    have hatoms : mlAtoms k = atoms := by
      show ((splitBody fn.body).map (·.1)).getD [] = atoms
      rw [hsb]; rfl
    rw [hatoms]
    simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hok hcok
    obtain ⟨⟨⟨⟨hck, hret⟩, hst⟩, hwalk⟩, hendC⟩ := hok
    obtain ⟨⟨⟨⟨hSt, hhd⟩, htl⟩, hrecs⟩, hout⟩ := hcok
    set S := storesOf 4 fn.body with hSdef
    let args : List E := [rec, region, mark, limit]
    let w : ℕ → E := fun i => gen ^ mGap o (s + (i - 6) / 10)
    obtain ⟨σ, hσ⟩ : ∃ σ : Val, σ = B1.Val.ofArgs (ev rd w args fn.body) := ⟨_, rfl⟩
    have hidx : ∀ v, σ v = σ (.n v.idx) := fun v => by rw [hσ]; rfl
    obtain ⟨-, -, hgs⟩ := ev_spec rd w fn.body args hchk
    rw [show args.length = 4 from rfl, ← hσ] at hgs
    have hbody := splitBody_eq hsb
    have hg : ∀ a ∈ atoms, Good rd S w σ a := fun a ha =>
      hgs (.atom a) (by rw [hbody]; exact List.mem_append_left _ (List.mem_map_of_mem ha))
    have par : ∀ i (hi : i < 4), σ (.n i) = args.getD i 0 := fun i hi => by
      rw [hσ]; exact ev_params rd _ (l := args) hchk (by simp [args]; omega)
    have e0 : σ (.n 0) = rec := par 0 (by omega)
    have e1 : σ (.n 1) = region := par 1 (by omega)
    have e2 : σ (.n 2) = mark := par 2 (by omega)
    have e3 : σ (.n 3) = limit := par 3 (by omega)
    have hF := pure_holds hg
    have hpv : ∀ {p : V}, p.idx = 0 → σ p = rec := fun hp => by rw [hidx, hp, e0]
    have hS4 : ∀ a ∈ S, mStoresOk 6 0 a = true := hSt
    have hnSl : ∀ {d p : V} {off : ℕ}, p.idx = 0 → off < 15 → Atom.load d p off ∉ S :=
      fun hp ho => notS_of_mStores hS4 (by rw [hp]; rfl) (Or.inr ho)
    have hreg0 : region ≠ 0 := by rw [hrg]; exact pow_ne_zero _ gen_ne_zero
    have hrecDef : ∀ off < 15, ∃ v, LoadHolds rd rec off v := by
      intro off ho
      rcases Nat.lt_or_ge off 13 with h | h
      · exact ⟨_, by simpa using hS ⟨off, h⟩⟩
      · rcases (show off = 13 ∨ off = 14 by omega) with rfl | rfl
        · exact ⟨_, h13⟩
        · exact ⟨_, h14⟩
    -- the claims
    have hclaims : (∀ j < k, σ (.n (6 + 10 * j + 2)) = region * gen ^ (o (s + j) - j)) ∧
        (∀ j < k, σ (.n (6 + 10 * j + 5)) = entries * gen ^ (4 * (o (s + j) - j))) ∧
        (∀ j < k, ∀ c < 4, σ (.n (6 + 10 * j + 6 + c)) = cells.getD (4 * j + c) 0) ∧
        ∀ j < k, ∀ a ∈ monoWin atoms 2 j, needsSide a = true → a.Holds rd σ := by
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · exact ⟨fun _ h => absurd h (by omega), fun _ h => absurd h (by omega),
          fun _ h => absurd h (by omega), fun _ h => absurd h (by omega)⟩
      simp only [Nat.ne_of_gt hk0, ↓reduceIte, Bool.and_eq_true] at hwalk
      obtain ⟨⟨⟨hl4, hl5⟩, -⟩, -⟩ := hwalk
      have v4 : σ (.n 4) = region * gen ^ mStart o s := by
        rw [load_val hl4 hg (hnSl rfl (by omega)), e0, rdAt_of_load h13]
      have v5 : σ (.n 5) = entries * gen ^ (4 * mStart o s) := by
        rw [load_val hl5 hg (hnSl rfl (by omega)), e0, rdAt_of_load h14]
      exact mRecs_core (A := atoms) (p0 := 2) (g0 := 6) (cov0 := 4) (ent0 := 5) (stp := 0)
        (K := k) (s := s) (fun i hi => mRecsC_at hrecs hi) hg hS4 (by norm_num)
        (fun i _ => by simp only [w]; congr 3; omega) v4 v5 hinc (by rw [e2]; exact hrec)
        (fun i hi => hdef i (by omega))
    obtain ⟨hcv, hev, vc, hside⟩ := hclaims
    -- the walk's end
    have vce : σ (.n (mlEnd k)) = region * gen ^ mStart o (s + k) := by
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · simp only [↓reduceIte] at hwalk
        rw [show mlEnd 0 = 27 from rfl, load_val hwalk hg (hnSl rfl (by omega)), e0,
          rdAt_of_load h13, Nat.add_zero]
      · simp only [Nat.ne_of_gt hk0, ↓reduceIte] at hout
        have hle := mStart_le hinc (k - 1) (by omega)
        rw [mOutOk_val hout hF, show mCov 6 4 k = 6 + 10 * (k - 1) + 2 by simp [mCov]; omega,
          hcv (k - 1) (by omega), word_two_pow (by omega), mul_assoc, ← pow_add,
          show s + k = s + (k - 1) + 1 by omega, mStart_succ]
        congr 2; omega
    obtain ⟨t, ht⟩ : ∃ t, endOf atoms (.n (mlEnd k)) = some t := by
      revert hendC; cases endOf atoms (.n (mlEnd k)) <;> simp
    have vt : σ t = gen ^ mStart o (s + k) := by
      rw [endOf_val ht hg (by rw [e1]; exact hreg0), vce, e1, mul_comm region, mul_assoc,
        mul_inv_cancel₀ hreg0, mul_one]
    have hedgeN : ∀ a ∈ atoms, needsSide a = true →
        mlcSide k (endOf atoms (.n (mlEnd k))) a = true → a ∉ S → a.Holds rd σ := by
      intro a ha hns hs haS
      rw [ht] at hs
      cases a with
      | load d p off =>
        obtain ⟨rfl, ho⟩ := mlcSide_load hs
        obtain ⟨v, hv⟩ := hrecDef off ho
        exact load_holds_of haS (hg _ ha) (by rw [e0]; exact hv)
      | mul d x y =>
        simp only [mlcSide, Bool.and_eq_true, decide_eq_true_eq, Option.some.injEq] at hs
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hs
        refine holds_of_good (hg _ ha) ?_
        simp only [Side]
        split
        · trivial
        · rw [e1]; exact hreg0
      | rangeCheck x y t1 t2 kk =>
        simp only [mlcSide, Bool.and_eq_true, decide_eq_true_eq, Option.some.injEq] at hs
        obtain ⟨⟨rfl, hky⟩, rfl⟩ := hs
        exact rc_holds (hg _ ha) hky vt (by rw [e3, hlim]) hend hdef
      | _ => simp [mlcSide] at hs
    have hat : ∀ a ∈ atoms, a.Holds rd σ := by
      refine atoms_holds_stores hg (fun a ha haS hns => Or.inl ?_) (fun _ a ha haS => ?_)
      · rcases mem_mParts (p0 := 2) (K := k) ha with h | ⟨i, hi, h⟩ | h
        · rcases hhd a h with h' | h'
          · rw [h'] at hns; exact absurd hns (by simp)
          · exact hedgeN a ha hns h' haS
        · exact hside i hi a h hns
        · rcases htl a h with h' | h'
          · rw [h'] at hns; exact absurd hns (by simp)
          · exact hedgeN a ha hns h' haS
      · obtain ⟨d, p, off, rfl⟩ := storesOf_load haS
        have hst4 := hS4 _ haS
        have hnot : mlcSide k (endOf atoms (.n (mlEnd k))) (.load d p off) = true → False := by
          intro hs
          obtain ⟨rfl, ho⟩ := mlcSide_load hs
          simp only [mStoresOk, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
            decide_eq_true_eq] at hst4
          rcases hst4 with ⟨-, h⟩ | h
          · omega
          · exact absurd h (by decide)
        rcases mem_mParts (p0 := 2) (K := k) ha with h | ⟨i, hi, h⟩ | h
        · rcases hhd _ h with h' | h'
          · exact absurd h' (by simp [needsSide])
          · exact (hnot h').elim
        · exact hside i hi _ h rfl
        · rcases htl _ h with h' | h'
          · exact absurd h' (by simp [needsSide])
          · exact (hnot h').elim
    have hd := chain_final hck rfl hat hpre
      (initCell_of_loads rfl hst hat (by rw [e0]; exact hS))
    have hv : ((mlSpec k atoms).vals σ).take ((mlSpec k atoms).len / 16) = cells := by
      have : (mlSpec k atoms).vals σ = cells := monoMsg_vals hl vc
      rw [this, List.take_of_length_le (by simp only [mlSpec]; omega)]
    rw [hv] at hd
    simp only [retOk, Bool.and_eq_true] at hret
    refine ⟨[r0, r1], σ, hbody, ?_, hat, ?_, fun q hq => ?_⟩
    · rw [hpar]
      simp only [List.map_cons, List.map_nil, e0, e1, e2, e3]
    · rw [List.map_cons, List.map_cons, List.map_nil, copy_sound hret.1 hat, copy_sound hret.2 hat,
        digestCells, ← hd]
    · obtain ⟨a, ha, haq⟩ := List.mem_filterMap.mp hq
      cases a with
      | load d p off =>
        simp only [Memory.atomLoad?, Option.some.injEq] at haq
        subst haq
        have hedgeA : mlcSide k (endOf atoms (.n (mlEnd k))) (.load d p off) = true →
            ∃ c < 15, (σ p).limb 0 * addressOfIndex off = addressOfIndex (rP + c) := by
          intro hs
          obtain ⟨rfl, ho⟩ := mlcSide_load hs
          exact ⟨off, ho, by rw [e0, hrc, limb0_gen_pow_mul]⟩
        rcases mem_mParts (p0 := 2) (K := k) ha with h | ⟨i, hi, h⟩ | h
        · rcases hhd _ h with h' | h'
          · exact absurd h' (by simp [needsSide])
          · exact Or.inl (hedgeA h')
        · have hs' := (mRecW_parts (mRecsC_at hrecs hi)).2.2.2 _ h rfl
          simp only [mSide, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
            decide_eq_true_eq] at hs'
          have hli := mStart_le hinc i hi
          rcases hs' with ⟨⟨rfl, rfl⟩, -⟩ | ⟨⟨rfl, h1⟩, h2⟩
          · refine Or.inr (Or.inl ⟨off, hi, ?_⟩)
            show (σ (.n (6 + 10 * off + 2))).limb 0 * addressOfIndex off = _
            rw [hcv off hi, hrg, ← pow_add, limb0_gen_pow_mul]
            congr 1; omega
          · refine Or.inr (Or.inr ⟨i, hi, off - 4 * i, by omega, ?_⟩)
            show (σ (.n (6 + 10 * i + 5))).limb 0 * addressOfIndex off = _
            rw [hev i hi, hen, ← pow_add, limb0_gen_pow_mul]
            congr 1; omega
        · rcases htl _ h with h' | h'
          · exact absurd h' (by simp [needsSide])
          · exact Or.inl (hedgeA h')
      | _ => simp [Memory.atomLoad?] at haq
  · exact absurd hok (by simp)

/-- **`child_claim_list_mono_last__L{k}` is complete, placed, within its frame**: the record at
`rec = g^rP`, the claims' marks at `region · g^(o (s + j))` and their cells among the caller's
words, the walk's end at most `L < 2^κ`. -/
theorem mlc_completeAtB (fs : String → ℕ) (cert : String → V → ℕ) {k : ℕ} (hk : k < 17) {κ : ℕ}
    {Lin : Main.Layout} {rec region mark limit entries : E} {rP eP rg L s n : ℕ} {o : ℕ → ℕ}
    {pre : List UInt8} {cells : List E} (hrc : rec = gen ^ rP) (hen : entries = gen ^ eP)
    (hrg : region = gen ^ rg) (hlim : limit = gen ^ L) (hpre : pre.length = rate * n)
    (hl : cells.length = 4 * k) (hinc : ∀ i < k, mStart o (s + i) ≤ o (s + i))
    (hend : mStart o (s + k) ≤ L) (hLκ : L < 2 ^ κ)
    (hmem : ∀ rd, MemL rd Lin → MonoRecAt rd rec n pre region entries (mStart o s) ∧
      MRec rd region L entries mark k (fun i => o (s + i)) cells)
    (hR1 : ∀ c < 15, RegionL Lin (rP + c)) (hR2 : ∀ j < k, RegionL Lin (rg + o (s + j)))
    (hR3 : ∀ j < k, ∀ c < 4, RegionL Lin (eP + 4 * o (s + j) + c)) :
    CompleteAtDTB fs cert κ (mlNames.getD k "") Lin [rec, region, mark, limit]
      (Returns (digestCells (keccak256 (pre ++ cellsBytes cells)))) (fun _ => True)
      (fs (mlNames.getD k "")) := by
  intro fp
  refine ⟨fs (mlNames.getD k ""), [], _, [], le_rfl, ⟨rfl, rfl⟩, fun q hq => by simp at hq,
    B1.disj_nil, fun rd hlow hm => ?_⟩
  simp only [List.append_nil, List.nil_append] at hm
  obtain ⟨hR, hrec⟩ := hmem rd hm
  obtain ⟨vs, σ, hb, hp, hat, hr, hload⟩ := mlc_core hk hrc hen hrg hlim hpre hR hl hinc hrec hend
    (boundMem_of_low hlow (by omega))
  refine RelAtIn.relAtInT (relAtIn_atoms (ml_name hk) hb (ml_loop hk) (ml_na hk) hp hat hr
    (fun q hq => by rw [ml_addr hk] at hq; exact absurd hq List.not_mem_nil) (fun q hq => ?_)
    (fun i hi => by obtain ⟨q, hq, -⟩ := hi; simp at hq))
  rcases hload q hq with ⟨c, hc, h⟩ | ⟨j, hj, h⟩ | ⟨j, hj, c, hc4, h⟩
  · exact ⟨_, h, Or.inl (hR1 c hc)⟩
  · exact ⟨_, h, Or.inl (hR2 j hj)⟩
  · exact ⟨_, h, Or.inl (hR3 j hj c hc4)⟩

end
end LeanVM.Guest.B1.Digest
