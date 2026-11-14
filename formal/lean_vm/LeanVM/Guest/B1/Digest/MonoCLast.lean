/-
  LeanVM.Guest.B1.Digest.MonoCLast

  `child_claim_list_mono`'s frame loops `child_claim_list_mono_loop0` and
  `child_claim_list_mono_loop1`: a block's honest valuation, with where its loads read, and the
  loops completely and placed.
-/

module

public import LeanVM.Guest.B1.Digest.MonoCRec
public import LeanVM.Guest.B1.Digest.MonoCW
public import LeanVM.Guest.B1.Digest.ChildMono
public import LeanVM.Guest.B1.Digest.ChildListComplete

/-!
# A frame of the gap walk, completely

`mono_core`: a frame loop's block at the counter `x = g^xj` (`child_claim_list_mono_loop0`, 136
claims, or `child_claim_list_mono_loop1`, 17), from the record at `chain · x^15` (the state after
whole blocks `pre`, the pointers at `mStart o s`), `m` honest claims (`MRec`, slots
`o (s + j)` strictly increasing) and the next record at offset `15` (the state after their cells,
the pointers at `mStart o (s + m)`): the body's evaluated valuation (`Fwd.ev`, the gaps
`mGap o` hinted) holds its atoms, and every load reads the record's thirty words, a claim's
coverage slot or a claim's cells. Soundness's `monoOk` gives the chain's check, `mcOk` the rest.
`monoLoop_completeAtB`: the loop over `M` frames is complete, placed, within `M + 1` frames.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd
open LeanVM.Guest.Memory (atomUnplaced)
open LeanVM.Guest.B1 (CompleteAtD CompleteAtDTB Returns LowDef)
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Guest.B1.Da (limb0_gen_pow_mul)

@[expose] public section

variable {rd : Reader}

/-- The walk's message is its cells. -/
theorem monoMsg_vals {σ : Val} {g0 K : ℕ} {cells : List E} (hl : cells.length = 4 * K)
    (hv : ∀ j < K, ∀ c < 4, σ (.n (g0 + 10 * j + 6 + c)) = cells.getD (4 * j + c) 0) :
    (monoMsg g0 K).map (srcVal σ) = cells := by
  refine List.ext_getElem (by simp [monoMsg, hl]) fun i h1 h2 => ?_
  have hi : i < 4 * K := by simpa [monoMsg] using h1
  simp only [monoMsg, List.getElem_map, List.getElem_range, srcVal]
  rw [hv (i / 4) (by omega) (i % 4) (by omega), show 4 * (i / 4) + i % 4 = i by omega,
    List.getD_eq_getElem _ _ h2]

theorem mOutOk_val {F : List Atom} {σ : Val} {o last w : ℕ} (h : mOutOk F o last w = true)
    (hF : ∀ a ∈ F, a.Holds rd σ) : σ (.n o) = σ (.n last) * word w 0 := by
  unfold mOutOk at h
  split at h
  · rename_i a c hac
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨rfl, hc⟩ := h
    rw [mulOf_sound hac hF, const_sound hc hF]
  · exact absurd h (by simp)

theorem mRecLd_parts {stp : ℕ} {outs : List V} {o28 o29 : ℕ} {d p : V} {off : ℕ}
    (h : mRecLd stp outs o28 o29 (.load d p off) = true) :
    p.idx = stp ∧ (off < 15 ∨ (off < 28 ∧ d = outs.getD (off - 15) default) ∨
      (off = 28 ∧ d = .n o28) ∨ (off = 29 ∧ d = .n o29)) := by
  simp only [mRecLd, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, ?_⟩
  rcases h2 with ((h | h) | h) | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

theorem mRecLd_load {stp : ℕ} {outs : List V} {o28 o29 : ℕ} {a : Atom}
    (h : mRecLd stp outs o28 o29 a = true) : ∃ d p off, a = .load d p off := by
  cases a <;> simp [mRecLd] at h
  exact ⟨_, _, _, rfl⟩

set_option maxRecDepth 20000 in
/-- **A frame of the gap walk's honest valuation** (a frame loop's block at `x = g^xj`), with
where its loads read: the record's thirty words at `chain · x^15`, a claim's coverage slot at
`region · g^(o (s + i))`, a claim's cells at `entries · g^(4 o (s + i))`. -/
theorem mono_core {j : ℕ} {f : String} {m p0 st0 cw ew nb : ℕ}
    (hok : monoOk (coreProgram.getD j default) f m p0 st0 cw ew = true)
    (hc : mcOk (coreProgram.getD j default) f m p0 st0 cw ew = true)
    (hcw : word cw 0 = gen ^ m) (hew : word ew 0 = gen ^ (4 * m))
    (hnb : (monoSpec m st0 (loopAtoms (coreProgram.getD j default))).nb = nb) (hm0 : 0 < m)
    {x N chain mark region entries : E} {xj chP eP rg L s : ℕ} {o : ℕ → ℕ}
    (hx : x = gen ^ xj) (hch : chain = gen ^ chP) (hen : entries = gen ^ eP)
    (hrg : region = gen ^ rg) {n : ℕ} {pre : List UInt8} (hpre : pre.length = rate * n)
    (hS : StateAt rd (chain * x ^ 15) 0 (absorbChunks n zeroState pre))
    (h13 : LoadHolds rd (chain * x ^ 15) 13 (region * gen ^ mStart o s))
    (h14 : LoadHolds rd (chain * x ^ 15) 14 (entries * gen ^ (4 * mStart o s)))
    {cells : List E} (hl : cells.length = 4 * m)
    (hinc : ∀ i < m, mStart o (s + i) ≤ o (s + i))
    (hrec : MRec rd region L entries mark m (fun i => o (s + i)) cells) (hdef : BoundMem rd L)
    (hS' : StateAt rd (chain * x ^ 15) 15
      (absorbChunks (n + nb) zeroState (pre ++ cellsBytes cells)))
    (h28 : LoadHolds rd (chain * x ^ 15) 28 (region * gen ^ mStart o (s + m)))
    (h29 : LoadHolds rd (chain * x ^ 15) 29 (entries * gen ^ (4 * mStart o (s + m)))) :
    ∃ σ : Val, (coreProgram.getD j default).params.map σ = [x, N, chain, mark] ∧
      (∀ a ∈ atomsIn (loopPre (coreProgram.getD j default)), a.Holds rd σ) ∧
      (∀ q ∈ (loopPre (coreProgram.getD j default)).filterMap B1.Stmt.loadS,
        (∃ c < 30, (σ q.1).limb 0 * addressOfIndex q.2 = addressOfIndex (chP + 15 * xj + c)) ∨
        (∃ i < m, (σ q.1).limb 0 * addressOfIndex q.2 = addressOfIndex (rg + o (s + i))) ∨
        (∃ i < m, ∃ c < 4,
          (σ q.1).limb 0 * addressOfIndex q.2 = addressOfIndex (eP + 4 * o (s + i) + c))) ∧
      ∀ a ∈ atomsIn (loopPre (coreProgram.getD j default)),
        Good rd (storesOf 4 (coreProgram.getD j default).body) (fun i => gen ^ mGap o (s + (i - 13) / 10)) σ a := by
  set fn := coreProgram.getD j default
  set A := loopAtoms fn with hAdef
  set S := storesOf 4 fn.body with hSdef
  simp only [monoOk, monoHead, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hlen4⟩, -⟩, hst⟩, -⟩, -⟩, hl11⟩, hl12⟩, -⟩, -⟩, hck⟩, -⟩ := hok
  simp only [mcOk, mcHead, mcEdge, Bool.and_eq_true, Option.isSome_iff_exists, List.all_eq_true,
    Bool.or_eq_true, Bool.not_eq_true'] at hc
  obtain ⟨⟨⟨⟨⟨⟨hshape, c', hchk⟩, hpreA⟩, heqA⟩, -⟩, ⟨⟨⟨⟨⟨hSt, hhd⟩, htl⟩, hm10⟩, ho28⟩, ho29⟩⟩,
    hrecs⟩ := hc
  have heqA' := atomsEqbL_sound heqA
  let args : List E := [x, N, chain, mark]
  let w : ℕ → E := fun i => gen ^ mGap o (s + (i - 13) / 10)
  obtain ⟨σ, hσ⟩ : ∃ σ : Val, σ = B1.Val.ofArgs (ev rd w args fn.body) := ⟨_, rfl⟩
  have hidx : ∀ v, σ v = σ (.n v.idx) := fun v => by rw [hσ]; rfl
  obtain ⟨-, -, hgs⟩ := ev_spec rd w fn.body args hchk
  rw [show args.length = 4 from rfl, ← hσ] at hgs
  have hg : ∀ a ∈ A, Good rd S w σ a := fun a ha =>
    hgs (.atom a) (cl_pre_mem (cl_atom_mem (by rw [heqA']; exact ha)))
  have hpar : fn.params = [.n 0, .n 1, .n 2, .n 3] := by
    have hs2 := hshape
    simp only [loopShapeF, Bool.and_eq_true, decide_eq_true_eq] at hs2
    rw [hs2.1.2, hlen4]; rfl
  have par : ∀ i (hi : i < 4), σ (.n i) = args.getD i 0 := fun i hi => by
    rw [hσ]; exact ev_params rd _ (l := args) hchk (by simp [args]; omega)
  have e0 : σ (.n 0) = x := par 0 (by omega)
  have e2 : σ (.n 2) = chain := par 2 (by omega)
  have e3 : σ (.n 3) = mark := par 3 (by omega)
  have hF := pure_holds hg
  have v10 : σ (.n 10) = chain * x ^ 15 := by rw [monoIs_sound hm10 hF, e2, e0]
  have hpv : ∀ {p : V}, p.idx = 10 → σ p = chain * x ^ 15 := fun hp => by rw [hidx, hp, v10]
  have hS4 : ∀ a ∈ S, mStoresOk 13 10 a = true := hSt
  have hnSl : ∀ {d p : V} {off : ℕ}, p.idx = 10 → off < 15 → Atom.load d p off ∉ S :=
    fun hp ho => notS_of_mStores hS4 (by rw [hp]; rfl) (Or.inr ho)
  have v11 : σ (.n 11) = region * gen ^ mStart o s := by
    rw [load_val hl11 hg (hnSl rfl (by omega)), v10, rdAt_of_load h13]
  have v12 : σ (.n 12) = entries * gen ^ (4 * mStart o s) := by
    rw [load_val hl12 hg (hnSl rfl (by omega)), v10, rdAt_of_load h14]
  have hw : ∀ i < m, w (13 + 10 * i) = gen ^ mGap o (s + i) := fun i _ => by
    simp only [w]; congr 3; omega
  have hrecM : MRec rd region L entries (σ (.n 3)) m (fun i => o (s + i)) cells := by
    rw [e3]; exact hrec
  obtain ⟨hcv, hev, vc, hside⟩ := mRecs_core (A := A) (p0 := p0) (g0 := 13) (cov0 := 11)
    (ent0 := 12) (stp := 10) (K := m) (s := s) (fun i hi => mRecsC_at hrecs hi) hg hS4
    (by norm_num) hw v11 v12 hinc hrecM hdef
  have hle := mStart_le hinc
  have hrecDef : ∀ off < 30, ∃ v, LoadHolds rd (chain * x ^ 15) off v := by
    intro off ho
    rcases Nat.lt_or_ge off 13 with h | h
    · exact ⟨_, by simpa using hS ⟨off, h⟩⟩
    rcases Nat.lt_or_ge off 15 with h' | h'
    · rcases (show off = 13 ∨ off = 14 by omega) with rfl | rfl
      · exact ⟨_, h13⟩
      · exact ⟨_, h14⟩
    rcases Nat.lt_or_ge off 28 with h'' | h''
    · exact ⟨_, by have := hS' ⟨off - 15, by omega⟩; rwa [show 15 + (off - 15) = off by omega] at this⟩
    · rcases (show off = 28 ∨ off = 29 by omega) with rfl | rfl
      · exact ⟨_, h28⟩
      · exact ⟨_, h29⟩
  have vst : ∀ c : Fin 13, σ ((anySt st0).getD c default) =
      cellsOfState (absorbChunks n zeroState pre) false c := by
    intro c
    simp only [stLoadsOk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hst
    rw [load_val (hst.2 c c.isLt) hg (hnSl rfl (by have := c.isLt; omega)), v10,
      rdAt_of_load (hS c)]
  have hedgeN : ∀ a ∈ A, a ∉ S → mRecLd 10 (mOuts m st0 A) (14 + 10 * m) (16 + 10 * m) a = true →
      a.Holds rd σ := by
    intro a ha haS hr
    obtain ⟨d, p, off, rfl⟩ := mRecLd_load hr
    obtain ⟨hp, hoff⟩ := mRecLd_parts hr
    have ho : off < 30 := by
      rcases hoff with h | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> omega
    obtain ⟨v, hv⟩ := hrecDef off ho
    exact load_holds_of haS (hg _ ha) (by rw [hpv hp]; exact hv)
  have hm1 : mCov 13 11 m = 13 + 10 * (m - 1) + 2 := by simp [mCov]; omega
  have hm2 : mEnt 13 12 m = 13 + 10 * (m - 1) + 5 := by simp [mEnt]; omega
  have hsm : mStart o (s + m) = o (s + (m - 1)) - (m - 1) + m := by
    rw [show s + m = s + (m - 1) + 1 by omega, mStart_succ]
    have := hle (m - 1) (by omega); omega
  have hedgeS : (∀ a ∈ A, a ∉ S → a.Holds rd σ) → ∀ a ∈ A, a ∈ S →
      mRecLd 10 (mOuts m st0 A) (14 + 10 * m) (16 + 10 * m) a = true → a.Holds rd σ := by
    intro h1 a ha haS hr
    obtain ⟨d, p, off, rfl⟩ := mRecLd_load hr
    obtain ⟨hp, hoff⟩ := mRecLd_parts hr
    have h15 : 15 ≤ off := by
      have := hS4 _ haS
      simp only [mStoresOk, hp, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
        decide_eq_true_eq] at this
      rcases this with ⟨-, h⟩ | h
      · exact h
      · exact absurd h (by decide)
    show LoadHolds rd (σ p) off (σ d)
    rw [hpv hp]
    rcases hoff with h | ⟨h, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · omega
    · have hG : ∀ b ∈ A.filter (fun a => decide (a ∉ S)), b.Holds rd σ :=
        fun b hb => h1 b (List.mem_filter.mp hb).1 (by simpa using (List.mem_filter.mp hb).2)
      have hq : ∀ a, isLoadB a = false → decide (a ∉ S) = true := by
        intro a ha'
        simp only [decide_eq_true_eq]
        intro hm
        obtain ⟨_, _, _, rfl⟩ := storesOf_load hm
        simp [isLoadB] at ha'
      have hchk' : (monoSpec m st0 A).check (A.filter (fun a => decide (a ∉ S))) = true := by
        rw [check_filter hq]; exact hck
      obtain ⟨hwo, -⟩ := chain_whole hchk' rfl hG hpre (fun c => vst c)
      have hv : (monoSpec m st0 A).vals σ = cells := monoMsg_vals hl vc
      obtain ⟨c, rfl⟩ : ∃ c, off = 15 + c := ⟨off - 15, by omega⟩
      have hc13 : c < 13 := by omega
      have hwc := hwo ⟨c, hc13⟩
      rw [hv, hnb] at hwc
      have hd' : (mOuts m st0 A).getD (15 + c - 15) default =
          (monoSpec m st0 A).outV ((monoSpec m st0 A).nb - 1) c := by
        rw [show 15 + c - 15 = c by omega]
        simp [mOuts, List.getD_eq_getElem?_getD, hc13]
      rw [hd', hnb]
      have := hS' ⟨c, hc13⟩
      rw [← hnb] at hwc
      rw [show ((⟨c, hc13⟩ : Fin 13) : ℕ) = c from rfl] at hwc this
      rw [hnb] at hwc
      rw [hwc]
      exact this
    · rw [mOutOk_val ho28 hF, hm1, hcv (m - 1) (by omega), hcw, mul_assoc, ← pow_add, ← hsm]
      exact h28
    · rw [mOutOk_val ho29 hF, hm2, hev (m - 1) (by omega), hew, mul_assoc, ← pow_add,
        show 4 * (o (s + (m - 1)) - (m - 1)) + 4 * m = 4 * mStart o (s + m) by rw [hsm]; ring]
      exact h29
  have hat : ∀ a ∈ A, a.Holds rd σ := by
    refine atoms_holds_stores hg (fun a ha haS hns => Or.inl ?_) (fun h1 a ha haS => ?_)
    · rcases mem_mParts (p0 := p0) (K := m) ha with h | ⟨i, hi, h⟩ | h
      · rcases hhd a h with h' | h'
        · rw [h'] at hns; exact absurd hns (by simp)
        · exact hedgeN a ha haS h'
      · exact hside i hi a h hns
      · rcases htl a h with h' | h'
        · rw [h'] at hns; exact absurd hns (by simp)
        · exact hedgeN a ha haS h'
    · obtain ⟨d, p, off, rfl⟩ := storesOf_load haS
      rcases mem_mParts (p0 := p0) (K := m) ha with h | ⟨i, hi, h⟩ | h
      · rcases hhd _ h with h' | h'
        · exact absurd h' (by simp [needsSide])
        · exact hedgeS h1 _ ha haS h'
      · exact hside i hi _ h rfl
      · rcases htl _ h with h' | h'
        · exact absurd h' (by simp [needsSide])
        · exact hedgeS h1 _ ha haS h'
  have h15g : chain * x ^ 15 = gen ^ (chP + 15 * xj) := by
    rw [hch, hx, ← pow_mul, ← pow_add, mul_comm xj 15]
  refine ⟨σ, ?_, fun a ha => hat a (by rwa [heqA'] at ha), fun q hq => ?_,
    fun a ha => hg a (by rwa [heqA'] at ha)⟩
  · rw [hpar]
    simp only [List.map_cons, List.map_nil]
    rw [e0, par 1 (by omega), e2, e3]
    rfl
  · obtain ⟨st, hs, hsq⟩ := List.mem_filterMap.mp hq
    have := hpreA st hs
    cases st <;> simp only [isAtomS, Bool.false_eq_true] at this
    rename_i a
    cases a with
    | load d p off =>
      simp only [B1.Stmt.loadS, Option.some.injEq] at hsq
      subst hsq
      have ha : Atom.load d p off ∈ A := by have := cl_mem_atoms hs; rwa [heqA'] at this
      have hedgeA : mRecLd 10 (mOuts m st0 A) (14 + 10 * m) (16 + 10 * m) (.load d p off) = true →
          ∃ c < 30, (σ p).limb 0 * addressOfIndex off = addressOfIndex (chP + 15 * xj + c) := by
        intro hr
        obtain ⟨hp, hoff⟩ := mRecLd_parts hr
        refine ⟨off, by rcases hoff with h | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> omega, ?_⟩
        rw [hpv hp, h15g, limb0_gen_pow_mul]
      rcases mem_mParts (p0 := p0) (K := m) ha with h | ⟨i, hi, h⟩ | h
      · rcases hhd _ h with h' | h'
        · exact absurd h' (by simp [needsSide])
        · exact Or.inl (hedgeA h')
      · have hs' := (mRecW_parts (mRecsC_at hrecs hi)).2.2.2 _ h rfl
        simp only [mSide, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hs'
        have hli := hle i hi
        rcases hs' with ⟨⟨rfl, rfl⟩, -⟩ | ⟨⟨rfl, h1⟩, h2⟩
        · refine Or.inr (Or.inl ⟨off, hi, ?_⟩)
          show (σ (.n (13 + 10 * off + 2))).limb 0 * addressOfIndex off = _
          rw [hcv off hi, hrg, ← pow_add, limb0_gen_pow_mul]
          congr 1; omega
        · refine Or.inr (Or.inr ⟨i, hi, off - 4 * i, by omega, ?_⟩)
          show (σ (.n (13 + 10 * i + 5))).limb 0 * addressOfIndex off = _
          rw [hev i hi, hen, ← pow_add, limb0_gen_pow_mul]
          congr 1; omega
      · rcases htl _ h with h' | h'
        · exact absurd h' (by simp [needsSide])
        · exact Or.inl (hedgeA h')
    | _ => simp [B1.Stmt.loadS] at hsq

/-! ## The two frame loops -/

/-- **A record of the walk** at `p`: the state after whole blocks `pre`, the coverage pointer
`region · g^O` at `13` and the table pointer `entries · g^(4O)` at `14`. -/
def MonoRecAt (rd : Reader) (p : E) (n : ℕ) (pre : List UInt8) (region entries : E) (O : ℕ) :
    Prop :=
  StateAt rd p 0 (absorbChunks n zeroState pre) ∧ LoadHolds rd p 13 (region * gen ^ O) ∧
    LoadHolds rd p 14 (entries * gen ^ (4 * O))

/-- The claims `s, …, s + k - 1` of honest claims. -/
theorem mRec_group {region entries mark : E} {L n : ℕ} {o : ℕ → ℕ} {cells : List E}
    (h : MRec rd region L entries mark n o cells) {s k : ℕ} (hsk : s + k ≤ n) :
    MRec rd region L entries mark k (fun j => o (s + j)) ((cells.drop (4 * s)).take (4 * k)) := by
  intro j hj
  obtain ⟨h1, h2, h3⟩ := h (s + j) (by omega)
  refine ⟨h1, h2, fun c hc => ?_⟩
  have e : ((cells.drop (4 * s)).take (4 * k)).getD (4 * j + c) 0 =
      cells.getD (4 * (s + j) + c) 0 := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop]
    rw [ite_pos' (by omega), show 4 * s + (4 * j + c) = 4 * (s + j) + c by ring]
  rw [e]
  exact h3 c hc

/-- The claims after the first `s`. -/
theorem mRec_drop {region entries mark : E} {L n : ℕ} {o : ℕ → ℕ} {cells : List E}
    (h : MRec rd region L entries mark n o cells) {s k : ℕ} (hsk : s + k ≤ n) :
    MRec rd region L entries mark k (fun j => o (s + j)) (cells.drop (4 * s)) := by
  intro j hj
  obtain ⟨h1, h2, h3⟩ := h (s + j) (by omega)
  refine ⟨h1, h2, fun c hc => ?_⟩
  have e : (cells.drop (4 * s)).getD (4 * j + c) 0 = cells.getD (4 * (s + j) + c) 0 := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]
    rw [show 4 * s + (4 * j + c) = 4 * (s + j) + c by ring]
  rw [e]
  exact h3 c hc

set_option maxRecDepth 100000 in
theorem mono136_unplaced :
    (atomsIn (loopPre (coreProgram.getD idx% «child_claim_list_mono_loop0» default))).all
        atomUnplaced = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem mono17_unplaced :
    (atomsIn (loopPre (coreProgram.getD idx% «child_claim_list_mono_loop1» default))).all
        atomUnplaced = true := by decide +kernel

theorem mc136_ok : mcOk (coreProgram.getD idx% «child_claim_list_mono_loop0» default)
    name% «child_claim_list_mono_loop0» 136 9 1377 83200 72058697844523035 = true := by
  have hw : ∀ i < 16, mcWin i = true := by
    intro i hi
    interval_cases i
    exacts [mcWin_0, mcWin_1, mcWin_2, mcWin_3, mcWin_4, mcWin_5, mcWin_6, mcWin_7, mcWin_8,
      mcWin_9, mcWin_10, mcWin_11, mcWin_12, mcWin_13, mcWin_14, mcWin_15]
  simp only [mcOk, mc136_head, mc136_edge, Bool.true_and]
  exact mRecs_of_wins (w := 9) (W := 16) (by norm_num) fun i hi => hw i hi

set_option maxRecDepth 20000 in
/-- **A frame loop of the gap walk, its frames**: at every frame `q < M`, the block's valuation
holds its atoms and reads the chain buffer's records and the claims among the caller's words. -/
theorem monoLoop_blocks {j : ℕ} {f : String} {m p0 st0 cw ew nb : ℕ}
    (hok : monoOk (coreProgram.getD j default) f m p0 st0 cw ew = true)
    (hc : mcOk (coreProgram.getD j default) f m p0 st0 cw ew = true)
    (hcw : word cw 0 = gen ^ m) (hew : word ew 0 = gen ^ (4 * m))
    (hnb : (monoSpec m st0 (loopAtoms (coreProgram.getD j default))).nb = nb)
    (h64 : 64 * m = 136 * nb) (hm0 : 0 < m) {κ : ℕ} {Lin : Main.Layout}
    {chain entries region mark : E} {chP eP rg L M n0 s0 : ℕ} {pre0 : List UInt8} {o : ℕ → ℕ}
    {cells : List E} (hch : chain = gen ^ chP) (hen : entries = gen ^ eP) (hrg : region = gen ^ rg)
    (hpre0 : pre0.length = rate * n0) (hl : 4 * m * M ≤ cells.length) (hLκ : L ≤ 2 ^ κ)
    (hinc : ∀ i < m * M, mStart o (s0 + i) ≤ o (s0 + i))
    (hmem : ∀ rd, MemL rd Lin → (∀ q ≤ M, MonoRecAt rd (chain * gen ^ (15 * q)) (n0 + nb * q)
        (pre0 ++ cellsBytes (cells.take (4 * m * q))) region entries (mStart o (s0 + m * q))) ∧
      MRec rd region L entries mark (m * M) (fun i => o (s0 + i)) cells)
    (hR1 : ∀ q < M, ∀ c < 30, RegionL Lin (chP + 15 * q + c))
    (hR2 : ∀ i < m * M, RegionL Lin (rg + o (s0 + i)))
    (hR3 : ∀ i < m * M, ∀ c < 4, RegionL Lin (eP + 4 * o (s0 + i) + c)) :
    ∀ q < M, LoopBlockIn κ (coreProgram.getD j default) Lin q (gen ^ M) [chain, mark] := by
  intro q hq rd hlow hLin
  obtain ⟨hR, hrec⟩ := hmem rd hLin
  have hmq : m * q + m ≤ m * M := by nlinarith
  have h1 : 4 * m * q ≤ cells.length := le_trans (by nlinarith) hl
  have h2 : 4 * m * q + 4 * m ≤ cells.length := le_trans (by nlinarith) hl
  have hpre : (pre0 ++ cellsBytes (cells.take (4 * m * q))).length = rate * (n0 + nb * q) := by
    rw [List.length_append, length_cellsBytes, List.length_take, Nat.min_eq_left h1, hpre0]
    show 136 * n0 + 16 * (4 * m * q) = 136 * (n0 + nb * q)
    have : 16 * (4 * m * q) = (64 * m) * q := by ring
    rw [this, h64]; ring
  obtain ⟨hS0, h13, h14⟩ := hR q (by omega)
  obtain ⟨hS1, h28, h29⟩ := hR (q + 1) (by omega)
  rw [show 4 * m * (q + 1) = 4 * m * q + 4 * m by ring, List.take_add, cellsBytes_append,
    ← List.append_assoc, show nb * (q + 1) = nb * q + nb by ring, ← Nat.add_assoc] at hS1
  have hr := mRec_group hrec (s := m * q) (k := m) hmq
  rw [show 4 * (m * q) = 4 * m * q by ring] at hr
  have e15 : chain * gen ^ (15 * (q + 1)) = chain * (gen ^ q) ^ 15 * gen ^ 15 := by
    rw [gen_pow_pow, mul_assoc, ← pow_add]; ring_nf
  rw [e15, loadHolds_mul_gen_pow] at h28 h29
  rw [show s0 + m * (q + 1) = s0 + m * q + m by ring] at h28 h29
  obtain ⟨σ, hp, hat, hload, -⟩ := mono_core hok hc hcw hew hnb hm0 (x := gen ^ q) (N := gen ^ M)
    (mark := mark) (s := s0 + m * q) (o := o) (L := L) rfl hch hen hrg hpre
    (by rw [gen_pow_pow]; exact hS0) (by rw [gen_pow_pow]; exact h13)
    (by rw [gen_pow_pow]; exact h14)
    (cells := (cells.drop (4 * m * q)).take (4 * m))
    (by simp only [List.length_take, List.length_drop]; omega)
    (fun i hi => by rw [Nat.add_assoc]; exact hinc (m * q + i) (by omega))
    (by intro i hi; have := hr i hi; simp only [Nat.add_assoc] at this ⊢; exact this)
    (boundMem_of_low hlow hLκ)
    (fun c => by
      have := hS1 c
      rw [e15, loadHolds_mul_gen_pow, show 15 + (0 + c.val) = 15 + c.val by ring] at this
      exact this) h28 h29
  refine ⟨σ, hp, hat, fun q' hq' => ?_⟩
  rcases hload q' hq' with ⟨c, hc30, h⟩ | ⟨i, hi, h⟩ | ⟨i, hi, c, hc4, h⟩
  · exact ⟨_, h, hR1 q hq c hc30⟩
  · rw [Nat.add_assoc s0] at h
    exact ⟨_, h, hR2 (m * q + i) (by omega)⟩
  · rw [Nat.add_assoc s0] at h
    exact ⟨_, h, hR3 (m * q + i) (by omega) c hc4⟩

/-- **A frame loop of the gap walk is complete, placed, within its frames**: `M` frames of `m`
claims from the counter `1`, the chain buffer's records at `g^chP`, the claims' marks and cells
among the caller's words; `M + 1` frames of words. -/
theorem monoLoop_completeAtB (fs : String → ℕ) (cert : String → V → ℕ) {j : ℕ} {f : String}
    {m p0 st0 cw ew nb : ℕ} (hf : coreProgram.find? f = some (coreProgram.getD j default))
    (hok : monoOk (coreProgram.getD j default) f m p0 st0 cw ew = true)
    (hc : mcOk (coreProgram.getD j default) f m p0 st0 cw ew = true)
    (hcw : word cw 0 = gen ^ m) (hew : word ew 0 = gen ^ (4 * m))
    (hnb : (monoSpec m st0 (loopAtoms (coreProgram.getD j default))).nb = nb)
    (hun : (atomsIn (loopPre (coreProgram.getD j default))).all atomUnplaced = true)
    (h64 : 64 * m = 136 * nb) (hm0 : 0 < m) {κ : ℕ} {Lin : Main.Layout}
    {chain entries region mark : E} {chP eP rg L M n0 s0 : ℕ} {pre0 : List UInt8} {o : ℕ → ℕ}
    {cells : List E} (hch : chain = gen ^ chP) (hen : entries = gen ^ eP) (hrg : region = gen ^ rg)
    (hpre0 : pre0.length = rate * n0) (hl : 4 * m * M ≤ cells.length) (hLκ : L ≤ 2 ^ κ)
    (hM : M < 2 ^ 34) (hM0 : 0 < M)
    (hinc : ∀ i < m * M, mStart o (s0 + i) ≤ o (s0 + i))
    (hmem : ∀ rd, MemL rd Lin → (∀ q ≤ M, MonoRecAt rd (chain * gen ^ (15 * q)) (n0 + nb * q)
        (pre0 ++ cellsBytes (cells.take (4 * m * q))) region entries (mStart o (s0 + m * q))) ∧
      MRec rd region L entries mark (m * M) (fun i => o (s0 + i)) cells)
    (hR1 : ∀ q < M, ∀ c < 30, RegionL Lin (chP + 15 * q + c))
    (hR2 : ∀ i < m * M, RegionL Lin (rg + o (s0 + i)))
    (hR3 : ∀ i < m * M, ∀ c < 4, RegionL Lin (eP + 4 * o (s0 + i) + c)) :
    CompleteAtDTB fs cert κ f Lin [1, gen ^ M, chain, mark] (Returns []) (fun _ => True)
      ((M + 1) * fs f) := by
  have hshape : loopShapeF (coreProgram.getD j default) f = true := by
    simp only [mcOk, mcHead, Bool.and_eq_true] at hc; exact hc.1.1.1.1.1.1
  have hAS : (loopPre (coreProgram.getD j default)).all isAtomS = true := by
    simp only [mcOk, mcHead, Bool.and_eq_true] at hc; exact hc.1.1.1.1.2
  have h := loopA_completeAtB fs cert hf hshape hAS hun (Lin := Lin) (κ := κ) (N := gen ^ M)
    (rest := [chain, mark]) (m := M) rfl hM
    (monoLoop_blocks hok hc hcw hew hnb h64 hm0 hch hen hrg hpre0 hl hLκ hinc hmem hR1 hR2 hR3)
  have := h 0 hM0
  rwa [pow_zero, Nat.sub_zero] at this

end
end LeanVM.Guest.B1.Digest
