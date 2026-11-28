module

public import LeanVM.Guest.B1.Digest.MonoCRec
public import LeanVM.Guest.B1.Digest.MonoCW
public import LeanVM.Guest.B1.Digest.ChildMono
public import LeanVM.Guest.Complete.Claims.AnyCore
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«child_claim_list_mono_last__L»

/-!
# `child_claim_list_mono`'s blocks and last group, their honest valuations

Restored from the archive's `B1/Digest/{MonoCLast, MonoCLasts}` (tag `formal-bus-archive`),
layout-free. `mono_core`: a frame loop's block at the counter `x = g^xj` (`child_claim_list_mono_loop0`,
136 claims, or `child_claim_list_mono_loop1`, 17), from the record at `chain · x^15` (the state after
whole blocks `pre`, the pointers at `mStart o s`), `m` honest claims (`MRec`, slots `o (s + j)`
strictly increasing) and the next record at offset `15`: the body's evaluated valuation (`Fwd.ev`, the
gaps `mGap o` hinted) holds its atoms, and every load reads the record's thirty words, a claim's
coverage slot or a claim's cells. `MonoRecAt`, `mRec_group`, `mRec_drop`: the records. `mlc_core`:
`child_claim_list_mono_last__L{k}`'s, from the last record and `k` honest claims, returning the digest.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd
open LeanVM.Guest.Memory (atomUnplaced)
open LeanVM.Guest.B1 (LowDef)

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

theorem mc136_ok : mcOk (coreProgram.getD idx% «child_claim_list_mono_loop0» default)
    name% «child_claim_list_mono_loop0» 136 9 1377 83200 72058697844523035 = true := by
  have hw : ∀ i < 16, mcWin i = true := by
    intro i hi
    interval_cases i
    exacts [mcWin_0, mcWin_1, mcWin_2, mcWin_3, mcWin_4, mcWin_5, mcWin_6, mcWin_7, mcWin_8,
      mcWin_9, mcWin_10, mcWin_11, mcWin_12, mcWin_13, mcWin_14, mcWin_15]
  simp only [mcOk, mc136_head, mc136_edge, Bool.true_and]
  exact mRecs_of_wins (w := 9) (W := 16) (by norm_num) fun i hi => hw i hi

/-! ## The last group -/

/-- `child_claim_list_mono_last__L{k}`'s atoms. -/
noncomputable def mlAtoms (k : ℕ) : List Atom :=
  ((splitBody (coreProgram.getD (idx% «child_claim_list_mono_last__L0» + k) default).body).map
      (·.1)).getD []

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
    Atom.mul ce t (.n (valf% «child_claim_list_mono_last» "region")) ∈ atoms := by
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
    (h : endOf atoms ce = some t) (hg : ∀ a ∈ atoms, Good rd S w σ a) (h1 : σ (.n (valf% «child_claim_list_mono_last» "region")) ≠ 0) :
    σ t = σ ce * (σ (.n (valf% «child_claim_list_mono_last» "region")))⁻¹ := by
  have := hg _ (endOf_mem h)
  simp only [Good] at this
  split at this
  · rw [this, mul_assoc, mul_inv_cancel₀ h1, mul_one]
  · exact this

theorem mlcSide_load {k : ℕ} {t : Option V} {d p : V} {off : ℕ}
    (h : mlcSide k t (.load d p off) = true) : p = .n (valf% «child_claim_list_mono_last» "rec") ∧ off < 15 := by
  simpa [mlcSide] using h

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
      (∀ q ∈ (mlAtoms k).filterMap Memory.atomLoad?,
        (∃ c < 15, (σ q.1).limb 0 * addressOfIndex q.2 = addressOfIndex (rP + c)) ∨
        (∃ i < k, (σ q.1).limb 0 * addressOfIndex q.2 = addressOfIndex (rg + o (s + i))) ∨
        (∃ i < k, ∃ c < 4,
          (σ q.1).limb 0 * addressOfIndex q.2 = addressOfIndex (eP + 4 * o (s + i) + c))) ∧
      ∀ a ∈ mlAtoms k, Good rd (storesOf 4 (coreProgram.getD (idx% «child_claim_list_mono_last__L0» + k) default).body)
        (fun i => gen ^ mGap o (s + (i - 6) / 10)) σ a := by
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
    have e0 : σ (.n (valf% «child_claim_list_mono_last» "rec")) = rec := par 0 (by omega)
    have e1 : σ (.n (valf% «child_claim_list_mono_last» "region")) = region := par 1 (by omega)
    have e2 : σ (.n (valf% «child_claim_list_mono_last» "mark")) = mark := par 2 (by omega)
    have e3 : σ (.n (valf% «child_claim_list_mono_last» "limit_g")) = limit := par 3 (by omega)
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
    refine ⟨[r0, r1], σ, hbody, ?_, hat, ?_, fun q hq => ?_, hg⟩
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

end
end LeanVM.Guest.B1.Digest
