/-
  LeanVM.Guest.B1.KeccakGkr.PackComplete

  The pack rounds' loop helpers, completely: an honest iteration's block holds on its evaluated
  valuation (the eight-round loop and the remainder loop).
-/

module

public import LeanVM.Guest.B1.KeccakGkr.PackLoop
public import LeanVM.Guest.B1.KeccakGkr.LayerCBlock

/-!
# The pack rounds' loops, completely

`packRound_complete`: a round (`packRoundT`) on a valuation satisfying its equations
(`Fwd.Good`), its coordinate and words in memory and its challenge's slot holding the honest
challenge, holds, and it is `eqRound` of them. `pack8Block_complete`: from an honest iteration of
the eight-round loop at `x` (`Pack8Hon`: `Pack8Step`), the honest valuation (`Fwd.ev` of
`pack8Pre` on `[x, N, rec, pp, pt, tabs]`) makes every atom of the block hold;
`packRemBlock_complete` likewise for the remainder loop (`PackRemHon`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

variable {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val}

/-! ## Small facts -/

theorem readsAt_pairs_get {p : E} {ms : List (E × E)} (h : ReadsAt rd p (ms.flatMap fun m ↦ [m.1, m.2]))
    {k : ℕ} (hk : k < ms.length) :
    LoadHolds rd p (2 * k) (ms.getD k (0, 0)).1 ∧ LoadHolds rd p (2 * k + 1) (ms.getD k (0, 0)).2 := by
  have hl : (ms.flatMap fun m ↦ [m.1, m.2]).length = 2 * ms.length := by
    induction ms with
    | nil => rfl
    | cons m ms ih => simp [List.flatMap_cons]; omega
  obtain ⟨e1, e2⟩ := flatPairs_get' ms k hk
  rw [List.getD_eq_getElem _ _ hk]
  refine ⟨?_, ?_⟩
  · have := h (2 * k) (by omega)
    rwa [← List.getD_eq_getElem _ 0, e1] at this
  · have := h (2 * k + 1) (by omega)
    rwa [← List.getD_eq_getElem _ 0, e2] at this
where
  flatPairs_get' : ∀ (ms : List (E × E)) (k : ℕ) (hk : k < ms.length),
      (ms.flatMap fun m ↦ [m.1, m.2]).getD (2 * k) 0 = ms[k].1 ∧
        (ms.flatMap fun m ↦ [m.1, m.2]).getD (2 * k + 1) 0 = ms[k].2
    | [], _, hk => absurd hk (by simp)
    | m :: ms, 0, _ => by simp
    | m :: ms, k + 1, hk => by
      have := flatPairs_get' ms k (by simpa using hk)
      simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.getElem_cons_succ]
      rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, List.getD_cons_succ, List.getD_cons_succ,
        List.getD_cons_succ, List.getD_cons_succ]
      exact this

/-! ## Chains, indexed -/

/-- **A chain, round by round**: its claims, scales and capacities, each round `eqRound` of the
previous. -/
theorem eqChain_idx : ∀ (rs : List E) (ms : List (E × E)) (cl sc : E) (cap chs : List E)
    (cl' sc' : E) (cap' : List E), EqChain rs ms cl sc cap chs cl' sc' cap' →
    ∃ (CL SC : ℕ → E) (CAP : ℕ → List E), CL 0 = cl ∧ SC 0 = sc ∧ CAP 0 = cap ∧
      CL rs.length = cl' ∧ SC rs.length = sc' ∧ CAP rs.length = cap' ∧
      ∀ q < rs.length, eqRound ⟨CAP q, []⟩ (ms.getD q (0, 0)).1 (ms.getD q (0, 0)).2 (rs.getD q 0)
        (CL q) (SC q) = (chs.getD q 0, CL (q + 1), SC (q + 1), ⟨CAP (q + 1), []⟩)
  | [], [], cl, sc, cap, chs, cl', sc', cap', h => by
    obtain ⟨-, h2, h3, h4⟩ := h
    exact ⟨fun _ ↦ cl, fun _ ↦ sc, fun _ ↦ cap, rfl, rfl, rfl, h2.symm, h3.symm, h4.symm,
      fun q hq ↦ absurd hq (Nat.not_lt_zero _)⟩
  | r :: rs, (g1, g2) :: ms, cl, sc, cap, chs, cl', sc', cap', h => by
    obtain ⟨ch, cl1, sc1, cap1, chs', he, hchs, hc⟩ := h
    subst hchs
    obtain ⟨CL, SC, CAP, h0, h1, h2, h3, h4, h5, hs⟩ := eqChain_idx rs ms cl1 sc1 cap1 chs' cl' sc'
      cap' hc
    refine ⟨fun q ↦ if q = 0 then cl else CL (q - 1), fun q ↦ if q = 0 then sc else SC (q - 1),
      fun q ↦ if q = 0 then cap else CAP (q - 1), rfl, rfl, rfl, by simpa using h3,
      by simpa using h4, by simpa using h5, ?_⟩
    intro q hq
    rcases q with _ | q
    · simp only [List.getD_cons_zero, ↓reduceIte, Nat.zero_add, Nat.add_one_sub_one, one_ne_zero]
      rw [he, h0, h1, h2]
    · simp only [List.getD_cons_succ, Nat.add_one_sub_one, Nat.add_eq_zero_iff, one_ne_zero,
        and_false, ↓reduceIte]
      exact hs q (by simpa using hq)
  | [], _ :: _, _, _, _, _, _, _, _, h => h.elim
  | _ :: _, [], _, _, _, _, _, _, _, h => h.elim

/-! ## A round, completely -/

theorem packRound_mem {pp cu pt : V} {q b c : ℕ} {pre : List Stmt} {zs cap : List V} {cl sc : V} :
    (∀ s ∈ fsNextT cu (2 * q) (b + 1), s ∈ packRoundT pp cu pt q b c pre zs cap cl sc) ∧
    (∀ s ∈ fsNextT cu (2 * q + 1) (b + 4), s ∈ packRoundT pp cu pt q b c pre zs cap cl sc) ∧
    (∀ s ∈ pre, s ∈ packRoundT pp cu pt q b c pre zs cap cl sc) ∧
    (∀ s ∈ challengeT (.n c) (c + 13), s ∈ packRoundT pp cu pt q b c pre zs cap cl sc) := by
  refine ⟨fun s hs ↦ ?_, fun s hs ↦ ?_, fun s hs ↦ ?_, fun s hs ↦ ?_⟩ <;>
    simp only [packRoundT, List.mem_append]
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hs)))))
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hs))))
  · exact Or.inl (Or.inl (Or.inl (Or.inr hs)))
  · exact Or.inl (Or.inr hs)

/-- **A round, completely**: on a valuation satisfying the round's equations, its coordinate and
two words in memory (not stores), its zero cells zero and its challenge's slot (a store) holding
the honest challenge, every atom of the round holds, and the round is `eqRound` of them. -/
theorem packRound_complete {pp cu pt : V} {q b c : ℕ} {pre : List Stmt} {zs cap : List V}
    {cl sc : V} (hbc : b + 7 ≤ c) (hsc : sc.idx < c + 24)
    (hg : ∀ s ∈ packRoundT pp cu pt q b c pre zs cap cl sc, GoodS rd S w σ s)
    (hpre : ∀ a, Stmt.atom a ∈ pre → a.Holds rd σ) (hz : zs.map σ = [0, 0, 0, 0])
    (s1 : Atom.load (.n b) pp q ∉ S) (s2 : Atom.load (.n (b + 1)) cu (2 * q) ∉ S)
    (s3 : Atom.load (.n (b + 4)) cu (2 * q + 1) ∉ S) (s4 : Atom.load (.n (c + 13)) pt q ∈ S)
    {r g1 g2 : E} (lr : LoadHolds rd (σ pp) q r) (lg1 : LoadHolds rd (σ cu) (2 * q) g1)
    (lg2 : LoadHolds rd (σ cu) (2 * q + 1) g2)
    (lch : LoadHolds rd (σ pt) q (eqRound ⟨cap.map σ, []⟩ g1 g2 r (σ cl) (σ sc)).1) :
    (∀ a, Stmt.atom a ∈ packRoundT pp cu pt q b c pre zs cap cl sc → a.Holds rd σ) ∧
      eqRound ⟨cap.map σ, []⟩ g1 g2 r (σ cl) (σ sc) =
        (σ (.n (c + 13)), σ (.n (c + 23)), σ (.n (c + 24)), ⟨(cap5 (c + 8)).map σ, []⟩) := by
  obtain ⟨m1, m2, m3, m4⟩ := packRound_mem (pp := pp) (cu := cu) (pt := pt) (q := q) (b := b)
    (c := c) (pre := pre) (zs := zs) (cap := cap) (cl := cl) (sc := sc)
  have g0 : Good rd S w σ (.load (.n b) pp q) := hg (.atom (.load (.n b) pp q)) (by simp [packRoundT])
  obtain ⟨e1, -, H1⟩ := fsNext_complete (C := fun _ _ _ ↦ True) (fun s hs ↦ hg s (m1 s hs)) s2 lg1
  obtain ⟨e2, -, H2⟩ := fsNext_complete (C := fun _ _ _ ↦ True) (fun s hs ↦ hg s (m2 s hs)) s3 lg2
  have H1' := ((holdsList_atoms (fsNextT_atoms cu (2 * q) (b + 1)) True (fun _ ↦ False)).1
    (H1 trivial)).1
  have H2' := ((holdsList_atoms (fsNextT_atoms cu (2 * q + 1) (b + 4)) True (fun _ ↦ False)).1
    (H2 trivial)).1
  -- the permutation
  have gk : Good rd S w σ (.keccak ([V.n (b + 2), .n (b + 3), .n (b + 5), .n (b + 6)] ++ zs ++ cap)
      ((List.range 13).map fun k ↦ .n (c + k)) false false) :=
    hg (.atom (.keccak ([V.n (b + 2), .n (b + 3), .n (b + 5), .n (b + 6)] ++ zs ++ cap)
      ((List.range 13).map fun k ↦ .n (c + k)) false false)) (by simp [packRoundT, keccakA])
  have hk := keccakA_complete gk
  obtain ⟨hch, H4⟩ := challenge_complete (C := fun _ _ _ ↦ True) (fun s hs ↦ hg s (m4 s hs))
  have H4' := ((holdsList_atoms (challengeT_atoms (.n c) (c + 13)) True
    (fun _ ↦ False)).1 (H4 trivial)).1
  -- the challenge's value
  have p1 : FsPackOk σ (.n (b + 1)) (b + 1 + 1) dsObserve :=
    (fsNextT_facts (rd := rd) (σ := σ) H1').2
  have p2 : FsPackOk σ (.n (b + 1 + 3)) (b + 1 + 3 + 1) dsObserve := by
    simpa [Nat.add_assoc] using (fsNextT_facts (rd := rd) (σ := σ) H2').2
  have q0 := sq2_atoms (rd := rd) (a := b + 1) (o := c) (zs := zs) (capV := cap)
    (cap := cap.map σ) p1 p2 (by simpa [Nat.add_assoc] using hk) hch hz rfl
  have e1' : σ (.n (b + 1)) = g1 := e1
  have e2' : σ (.n (b + 1 + 3)) = g2 := by simpa [Nat.add_assoc] using e2
  rw [e1', e2'] at q0
  have v13 : σ (.n (c + 13)) = (eqRound ⟨cap.map σ, []⟩ g1 g2 r (σ cl) (σ sc)).1 := by
    simp only [eqRound]; exact q0.1
  -- every atom
  have H : ∀ a, Stmt.atom a ∈ packRoundT pp cu pt q b c pre zs cap cl sc → a.Holds rd σ := by
    intro a ha
    simp only [packRoundT, List.mem_append] at ha
    rcases ha with ((((((ha | ha) | ha) | ha) | ha) | ha) | ha)
    · simp only [List.mem_singleton, Stmt.atom.injEq] at ha
      subst ha
      exact holds_read s1 g0 lr
    · exact H1' a ha
    · exact H2' a ha
    · exact hpre a ha
    · simp only [keccakA, List.mem_singleton, Stmt.atom.injEq] at ha
      subst ha
      exact hk
    · exact H4' a ha
    · have gt : ∀ x, Stmt.atom x ∈ [Stmt.atom (.load (.n (c + 13)) pt q),
          .atom (.add (.n (c + 14)) (.n b) (.n (c + 13))),
          .atom (.const (.n (c + 15)) (word 1 0)),
          .atom (.add (.n (c + 16)) (.n (c + 15)) (.n (c + 14))),
          .atom (.mul (.n (c + 17)) (.n (c + 14)) (.n (b + 1))),
          .atom (.add (.n (c + 18)) cl (.n (c + 17))),
          .atom (.mul (.n (c + 19)) (.n (c + 13)) (.n (c + 13))),
          .atom (.add (.n (c + 20)) (.n b) (.n (c + 19))),
          .atom (.mul (.n (c + 21)) (.n (c + 20)) (.n (b + 4))),
          .atom (.add (.n (c + 22)) (.n (c + 18)) (.n (c + 21))),
          .atom (.mul (.n (c + 23)) (.n (c + 16)) (.n (c + 22))),
          .atom (.mul (.n (c + 24)) sc (.n (c + 16)))] → Good rd S w σ x :=
        fun x hx ↦ hg (.atom x) (by simp only [packRoundT, List.mem_append]; exact Or.inr hx)
      simp only [List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact holds_store s4 (gt _ (by simp)) (by rw [v13]; exact lch)
      · exact holds_of_pure rfl (gt _ (by simp))
      · exact holds_of_pure rfl (gt _ (by simp))
      · exact holds_of_pure rfl (gt _ (by simp))
      · exact holds_mul ⟨idx_lt (by omega), idx_lt (by omega)⟩ (gt _ (by simp))
      · exact holds_of_pure rfl (gt _ (by simp))
      · exact holds_mul ⟨idx_lt (by omega), idx_lt (by omega)⟩ (gt _ (by simp))
      · exact holds_of_pure rfl (gt _ (by simp))
      · exact holds_mul ⟨idx_lt (by omega), idx_lt (by omega)⟩ (gt _ (by simp))
      · exact holds_of_pure rfl (gt _ (by simp))
      · exact holds_mul ⟨idx_lt (by omega), idx_lt (by omega)⟩ (gt _ (by simp))
      · exact holds_mul ⟨hsc, idx_lt (by omega)⟩ (gt _ (by simp))
  refine ⟨H, ?_⟩
  have F := packRound_facts H hz
  have er : σ (.n b) = r := loadHolds_unique F.1 lr
  rw [er, e1, show σ (.n (b + 4)) = g2 from by simpa [Nat.add_assoc] using e2] at F
  exact F.2.2.2.2

/-! ## The eight-round loop's block -/

theorem five_of_length {l : List E} (h : l.length = 5) :
    ∃ a b c d e, l = [a, b, c, d, e] := by
  match l, h with
  | [a, b, c, d, e], _ => exact ⟨a, b, c, d, e, rfl⟩

/-- **An honest iteration of the eight-round loop at `x`**: `Pack8Step`. -/
def Pack8Hon (rd : Reader) (rec pp pt x : E) : Prop :=
  ∃ (cap : List E) (cur claim scale : E) (rs : List E) (ms : List (E × E)) (chs : List E)
    (claim' scale' : E) (cap' : List E),
    RoundRec rd (rec * x) 0 cap cur claim scale ∧ rs.length = 8 ∧
      ReadsAt rd (pp * x ^ 8) rs ∧ ReadsAt rd cur (ms.flatMap fun m ↦ [m.1, m.2]) ∧
      EqChain rs ms claim scale cap chs claim' scale' cap' ∧ ReadsAt rd (pt * x ^ 8) chs ∧
      RoundRec rd (rec * x) 1 cap' (cur * gen ^ 16) claim' scale'

/-- The stores of the eight-round loop's block: the challenges' slots, the next record. -/
def pack8S : List Atom :=
  ((List.range 8).map fun q ↦ Atom.load (.n (48 + 32 * q)) (.n 14) q) ++
  [.load (.n 267) (.n 6) 1, .load (.n 268) (.n 6) 17, .load (.n 269) (.n 6) 33,
    .load (.n 270) (.n 6) 49, .load (.n 271) (.n 6) 65, .load (.n 285) (.n 6) 81,
    .load (.n 282) (.n 6) 97, .load (.n 283) (.n 6) 113]

theorem pack8_chk : Fwd.chk 6 pack8Pre = some 291 := by decide +kernel

theorem pack8_stores : storesOf 6 pack8Pre = pack8S := by decide +kernel

theorem pack8S_round : ∀ q < 8, Atom.load (.n (pkB q)) (.n 10) q ∉ pack8S ∧
    Atom.load (.n (pkB q + 1)) (.n 20) (2 * q) ∉ pack8S ∧
    Atom.load (.n (pkB q + 4)) (.n 20) (2 * q + 1) ∉ pack8S ∧
    Atom.load (.n (pkC q + 13)) (.n 14) q ∈ pack8S := by decide +kernel

theorem pk8_mem_roundS {q : ℕ} (hq : q < 8) : ∀ s ∈ pkRound q, s ∈ pack8Pre := fun _ ha ↦
  List.mem_append_left _ (List.mem_append_right _
    (List.mem_flatten.2 ⟨pkRound q, List.mem_map.2 ⟨q, List.mem_range.2 hq, rfl⟩, ha⟩))

set_option maxRecDepth 20000 in
/-- **The eight-round loop's block, completely**: an honest iteration at `x` makes every atom of
the block's honest valuation hold. -/
theorem pack8Block_complete {x N rec pp pt tb : E} (hs : Pack8Hon rd rec pp pt x) :
    ∃ σ : Val, [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5)] = [x, N, rec, pp, pt, tb] ∧
      (∀ a, Stmt.atom a ∈ pack8Pre → a.Holds rd σ) ∧
      σ (.n 6) = rec * x ∧ σ (.n 10) = pp * x ^ 8 ∧ σ (.n 14) = pt * x ^ 8 ∧
      LoadHolds rd (rec * x) 80 (σ (.n 20)) ∧ σ (.n 288) = x * gen + N ∧
      σ (.n 290) = x * gen := by
  obtain ⟨cap, cur, claim, scale, rs, ms, chs, claim', scale', cap', ⟨⟨hcl, hcap⟩, lcur, lclm, lsc⟩,
    hrl, hrs, hms, hch, hchs, ⟨⟨hcl', hcap'⟩, lcur', lclm', lsc'⟩⟩ := hs
  obtain ⟨c0, c1, c2, c3, c4, rfl⟩ := five_of_length hcl
  obtain ⟨d0, d1, d2, d3, d4, rfl⟩ := five_of_length hcl'
  obtain ⟨hml, hchl⟩ := packEqChain_length hch
  obtain ⟨CL, SC, CAP, h0, h1, h2, h3, h4, h5, hst⟩ := eqChain_idx _ _ _ _ _ _ _ _ _ hch
  rw [hrl] at h3 h4 h5 hst
  -- the honest valuation
  set l : List E := [x, N, rec, pp, pt, tb] with hl
  have g := (ev_spec rd (fun _ ↦ 0) pack8Pre l pack8_chk).2.2
  have pq : ∀ i (hi : i < 6), Val.ofArgs (ev rd (fun _ ↦ 0) l pack8Pre) (.n i) = l.getD i 0 :=
    fun i hi ↦ ev_params rd (fun _ ↦ 0) (l := l) pack8_chk (by simpa [hl] using hi)
  rw [show l.length = 6 from rfl, pack8_stores] at g
  generalize Val.ofArgs (ev rd (fun _ ↦ 0) l pack8Pre) = σ at g pq
  have p0 : σ (.n 0) = x := pq 0 (by norm_num)
  have p1 : σ (.n 1) = N := pq 1 (by norm_num)
  have p2 : σ (.n 2) = rec := pq 2 (by norm_num)
  have p3 : σ (.n 3) = pp := pq 3 (by norm_num)
  have p4 : σ (.n 4) = pt := pq 4 (by norm_num)
  have p5 : σ (.n 5) = tb := pq 5 (by norm_num)
  have gH : ∀ a, Stmt.atom a ∈ pk8Head → Good rd pack8S (fun _ ↦ 0) σ a := fun a ha ↦
    g _ (List.mem_append_left _ (List.mem_append_left _ ha))
  have gT : ∀ a, Stmt.atom a ∈ pk8Tail → Good rd pack8S (fun _ ↦ 0) σ a := fun a ha ↦
    g _ (List.mem_append_right _ ha)
  -- the head
  have e6 : σ (.n 6) = σ (.n 2) * σ (.n 0) := good_mul (by decide) (gH _ (by simp [pk8Head]))
  have e7 : σ (.n 7) = σ (.n 0) * σ (.n 0) := good_mul (by decide) (gH _ (by simp [pk8Head]))
  have e8 : σ (.n 8) = σ (.n 7) * σ (.n 7) := good_mul (by decide) (gH _ (by simp [pk8Head]))
  have e9 : σ (.n 9) = σ (.n 8) * σ (.n 8) := good_mul (by decide) (gH _ (by simp [pk8Head]))
  have e10 : σ (.n 10) = σ (.n 3) * σ (.n 9) := good_mul (by decide) (gH _ (by simp [pk8Head]))
  have e11 : σ (.n 11) = σ (.n 0) * σ (.n 0) := good_mul (by decide) (gH _ (by simp [pk8Head]))
  have e12 : σ (.n 12) = σ (.n 11) * σ (.n 11) := good_mul (by decide) (gH _ (by simp [pk8Head]))
  have e13 : σ (.n 13) = σ (.n 12) * σ (.n 12) := good_mul (by decide) (gH _ (by simp [pk8Head]))
  have e14 : σ (.n 14) = σ (.n 4) * σ (.n 13) := good_mul (by decide) (gH _ (by simp [pk8Head]))
  have v6 : σ (.n 6) = rec * x := by rw [e6, p2, p0]
  have v10 : σ (.n 10) = pp * x ^ 8 := by rw [e10, p3, gen_pow_eight_of _ _ _ _ e7 e8 e9, p0]
  have v14 : σ (.n 14) = pt * x ^ 8 := by rw [e14, p4, gen_pow_eight_of _ _ _ _ e11 e12 e13, p0]
  have L0 : LoadHolds rd (rec * x) 0 c0 := hcap 0 (by simp)
  have L16 : LoadHolds rd (rec * x) 16 c1 := hcap 1 (by simp)
  have L32 : LoadHolds rd (rec * x) 32 c2 := hcap 2 (by simp)
  have L48 : LoadHolds rd (rec * x) 48 c3 := hcap 3 (by simp)
  have L64 : LoadHolds rd (rec * x) 64 c4 := hcap 4 (by simp)
  have L80 : LoadHolds rd (rec * x) 80 cur := lcur
  have L96 : LoadHolds rd (rec * x) 96 claim := lclm
  have L112 : LoadHolds rd (rec * x) 112 scale := lsc
  have v15 : σ (.n 15) = c0 := load_val (gH (.load (.n 15) (.n 6) 0) (by simp [pk8Head])) (by decide) (by rw [v6]; exact L0)
  have v16 : σ (.n 16) = c1 := load_val (gH (.load (.n 16) (.n 6) 16) (by simp [pk8Head])) (by decide) (by rw [v6]; exact L16)
  have v17 : σ (.n 17) = c2 := load_val (gH (.load (.n 17) (.n 6) 32) (by simp [pk8Head])) (by decide) (by rw [v6]; exact L32)
  have v18 : σ (.n 18) = c3 := load_val (gH (.load (.n 18) (.n 6) 48) (by simp [pk8Head])) (by decide) (by rw [v6]; exact L48)
  have v19 : σ (.n 19) = c4 := load_val (gH (.load (.n 19) (.n 6) 64) (by simp [pk8Head])) (by decide) (by rw [v6]; exact L64)
  have v20 : σ (.n 20) = cur := load_val (gH (.load (.n 20) (.n 6) 80) (by simp [pk8Head])) (by decide) (by rw [v6]; exact L80)
  have v21 : σ (.n 21) = claim := load_val (gH (.load (.n 21) (.n 6) 96) (by simp [pk8Head])) (by decide) (by rw [v6]; exact L96)
  have v22 : σ (.n 22) = scale := load_val (gH (.load (.n 22) (.n 6) 112) (by simp [pk8Head])) (by decide) (by rw [v6]; exact L112)
  -- the rounds
  have hpre : ∀ k < 8, ∀ a, Stmt.atom a ∈ pkPre k → a.Holds rd σ := by
    intro k hk a ha
    have hp : pureB a = true := by
      unfold pkPre at ha
      split at ha
      · simp only [List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
        rcases ha with rfl | rfl | rfl | rfl | rfl <;> rfl
      · simp at ha
    exact holds_of_pure hp (show Good rd pack8S (fun _ ↦ 0) σ a from
      g _ (pk8_mem_roundS hk _ (packRound_mem.2.2.1 _ ha)))
  have z : ∀ v ∈ [31, 32, 33, 34], σ (.n v) = 0 := by
    intro v hv
    have := g (.atom (.const (.n v) (word 0 0))) (pk8_mem_roundS (q := 0) (by norm_num) _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl <;> simp [pkRound, packRoundT, pkPre]))
    simpa [GoodS, Good, word_zero] using this
  have hz : pkZs.map σ = [0, 0, 0, 0] := by
    simp [pkZs, z 31 (by simp), z 32 (by simp), z 33 (by simp), z 34 (by simp)]
  have key : ∀ k ≤ 8, (pkCap k).map σ = CAP k ∧ σ (.n (pkCl k)) = CL k ∧
      σ (.n (pkSc k)) = SC k ∧ ∀ q < k, ∀ a, Stmt.atom a ∈ pkRound q → a.Holds rd σ := by
    intro k hk
    induction k with
    | zero =>
      refine ⟨?_, ?_, ?_, fun q hq ↦ absurd hq (Nat.not_lt_zero _)⟩
      · rw [h2]; simp [pkCap, cap5, v15, v16, v17, v18, v19]
      · rw [h0]; exact v21
      · rw [h1]; exact v22
    | succ k ih =>
      obtain ⟨ec, el, es, hr⟩ := ih (by omega)
      have hk8 : k < 8 := by omega
      obtain ⟨n1, n2, n3, n4⟩ := pack8S_round k hk8
      obtain ⟨lg1, lg2⟩ := readsAt_pairs_get hms (by omega : k < ms.length)
      have lr : LoadHolds rd (σ (.n 10)) k (rs.getD k 0) := by
        rw [v10, List.getD_eq_getElem _ _ (by omega)]; exact hrs k (by omega)
      have e := hst k hk8
      have lch : LoadHolds rd (σ (.n 14)) k (eqRound ⟨(pkCap k).map σ, []⟩ (ms.getD k (0, 0)).1
          (ms.getD k (0, 0)).2 (rs.getD k 0) (σ (.n (pkCl k))) (σ (.n (pkSc k)))).1 := by
        rw [ec, el, es, e, v14, List.getD_eq_getElem _ _ (by omega)]; exact hchs k (by omega)
      obtain ⟨Hk, ek⟩ := packRound_complete (rd := rd) (S := pack8S) (w := fun _ ↦ 0) (σ := σ)
        (pp := .n 10) (cu := .n 20) (pt := .n 14) (q := k) (b := pkB k) (c := pkC k)
        (pre := pkPre k) (zs := pkZs) (cap := pkCap k) (cl := .n (pkCl k)) (sc := .n (pkSc k))
        (by unfold pkB pkC; split <;> omega) (by show pkSc k < pkC k + 24; unfold pkSc pkC; split <;> omega)
        (fun s hs ↦ g s (pk8_mem_roundS hk8 s hs)) (hpre k hk8) hz n1 n2 n3 n4 lr (by rw [v20]; exact lg1)
        (by rw [v20]; exact lg2) lch
      rw [ec, el, es, e] at ek
      simp only [Prod.mk.injEq, Fs.mk.injEq, and_true] at ek
      obtain ⟨-, ecl, esc, ecap⟩ := ek
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [pkCap, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_one_sub_one]; exact ecap.symm
      · simp only [pkCl, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_one_sub_one]; exact ecl.symm
      · simp only [pkSc, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_one_sub_one]; exact esc.symm
      · intro q hq a ha
        rcases Nat.lt_succ_iff_lt_or_eq.1 hq with hq | rfl
        · exact hr q hq a ha
        · exact Hk a ha
  obtain ⟨kc, kl, ks, kr⟩ := key 8 le_rfl
  rw [h5] at kc
  rw [h3, show pkCl 8 = 282 from rfl] at kl
  rw [h4, show pkSc 8 = 283 from rfl] at ks
  simp only [pkCap, pkC, cap5] at kc
  norm_num at kc
  obtain ⟨w267, w268, w269, w270, w271⟩ := kc
  -- the tail
  have e284 : σ (.n 284) = word 65536 0 := gT (.const (.n 284) (word 65536 0)) (by simp [pk8Tail])
  have e285 : σ (.n 285) = σ (.n 20) * σ (.n 284) := good_mul (by decide) (gT _ (by simp [pk8Tail]))
  have v285 : σ (.n 285) = cur * gen ^ 16 := by
    rw [e285, e284, v20, show (65536 : ℕ) = 2 ^ 16 from rfl, word_two_pow (by decide)]
  have e286 : σ (.n 286) = word 2 0 := gT (.const (.n 286) (word 2 0)) (by simp [pk8Tail])
  have e287 : σ (.n 287) = σ (.n 0) * σ (.n 286) := good_mul (by decide) (gT _ (by simp [pk8Tail]))
  have e288 : σ (.n 288) = σ (.n 287) + σ (.n 1) := gT (.add (.n 288) (.n 287) (.n 1)) (by simp [pk8Tail])
  have e289 : σ (.n 289) = word 2 0 := gT (.const (.n 289) (word 2 0)) (by simp [pk8Tail])
  have e290 : σ (.n 290) = σ (.n 0) * σ (.n 289) := good_mul (by decide) (gT _ (by simp [pk8Tail]))
  have hO : ∀ j (hj : j < 5), LoadHolds rd (rec * x) (1 + j * 16) ([d0, d1, d2, d3, d4][j]'(by simpa using hj)) :=
    fun j hj ↦ hcap' j (by simpa using hj)
  refine ⟨σ, by rw [p0, p1, p2, p3, p4, p5], ?_, v6, v10, v14, by rw [v20]; exact L80,
    by rw [e288, e287, e286, p0, p1, word_gen], by rw [e290, e289, p0, word_gen]⟩
  intro a ha
  rcases List.mem_append.1 ha with ha | ha
  · rcases List.mem_append.1 ha with ha | ha
    · simp only [pk8Head, List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl
      · exact holds_mul (by decide) (gH _ (by simp [pk8Head]))
      · exact holds_mul (by decide) (gH _ (by simp [pk8Head]))
      · exact holds_mul (by decide) (gH _ (by simp [pk8Head]))
      · exact holds_mul (by decide) (gH _ (by simp [pk8Head]))
      · exact holds_mul (by decide) (gH _ (by simp [pk8Head]))
      · exact holds_mul (by decide) (gH _ (by simp [pk8Head]))
      · exact holds_mul (by decide) (gH _ (by simp [pk8Head]))
      · exact holds_mul (by decide) (gH _ (by simp [pk8Head]))
      · exact holds_mul (by decide) (gH _ (by simp [pk8Head]))
      · exact holds_read (by decide) (gH _ (by simp [pk8Head])) (by rw [v6]; exact L0)
      · exact holds_read (by decide) (gH _ (by simp [pk8Head])) (by rw [v6]; exact L16)
      · exact holds_read (by decide) (gH _ (by simp [pk8Head])) (by rw [v6]; exact L32)
      · exact holds_read (by decide) (gH _ (by simp [pk8Head])) (by rw [v6]; exact L48)
      · exact holds_read (by decide) (gH _ (by simp [pk8Head])) (by rw [v6]; exact L64)
      · exact holds_read (by decide) (gH _ (by simp [pk8Head])) (by rw [v6]; exact L80)
      · exact holds_read (by decide) (gH _ (by simp [pk8Head])) (by rw [v6]; exact L96)
      · exact holds_read (by decide) (gH _ (by simp [pk8Head])) (by rw [v6]; exact L112)
    · obtain ⟨_, hm, ha⟩ := List.mem_flatten.1 ha
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hm
      exact kr q (List.mem_range.1 hq) a ha
  · simp only [pk8Tail, List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
    · exact holds_store (by decide) (gT _ (by simp [pk8Tail])) (by rw [v6, w267]; exact hO 0 (by norm_num))
    · exact holds_store (by decide) (gT _ (by simp [pk8Tail])) (by rw [v6, w268]; exact hO 1 (by norm_num))
    · exact holds_store (by decide) (gT _ (by simp [pk8Tail])) (by rw [v6, w269]; exact hO 2 (by norm_num))
    · exact holds_store (by decide) (gT _ (by simp [pk8Tail])) (by rw [v6, w270]; exact hO 3 (by norm_num))
    · exact holds_store (by decide) (gT _ (by simp [pk8Tail])) (by rw [v6, w271]; exact hO 4 (by norm_num))
    · exact e284
    · exact holds_mul (by decide) (gT _ (by simp [pk8Tail]))
    · exact holds_store (by decide) (gT _ (by simp [pk8Tail])) (by rw [v6, v285]; exact lcur')
    · exact holds_store (by decide) (gT _ (by simp [pk8Tail])) (by rw [v6, kl]; exact lclm')
    · exact holds_store (by decide) (gT _ (by simp [pk8Tail])) (by rw [v6, ks]; exact lsc')
    · exact e286
    · exact holds_mul (by decide) (gT _ (by simp [pk8Tail]))
    · exact e288
    · exact e289
    · exact holds_mul (by decide) (gT _ (by simp [pk8Tail]))

/-! ## The remainder loop's block -/

/-- **An honest iteration of the remainder loop at `x`**: `PackRemStep`. -/
def PackRemHon (rd : Reader) (rec pp pt x : E) : Prop :=
  ∃ (cap : List E) (cur claim scale r g1 g2 : E),
    RoundRec rd (rec * x) 0 cap cur claim scale ∧ LoadHolds rd (pp * x) 0 r ∧
      ReadsAt rd cur [g1, g2] ∧
      LoadHolds rd (pt * x) 0 (eqRound ⟨cap, []⟩ g1 g2 r claim scale).1 ∧
      RoundRec rd (rec * x) 1 (eqRound ⟨cap, []⟩ g1 g2 r claim scale).2.2.2.cap (cur * gen ^ 2)
        (eqRound ⟨cap, []⟩ g1 g2 r claim scale).2.1 (eqRound ⟨cap, []⟩ g1 g2 r claim scale).2.2.1

/-- The remainder block's head: the record and the coordinate read. -/
def remA : List Stmt :=
  [.atom (.mul (.n 6) (.n 2) (.n 0)), .atom (.mul (.n 7) (.n 3) (.n 0)),
    .atom (.load (.n 8) (.n 7) 0), .atom (.load (.n 9) (.n 6) 0), .atom (.load (.n 10) (.n 6) 16),
    .atom (.load (.n 11) (.n 6) 32), .atom (.load (.n 12) (.n 6) 48),
    .atom (.load (.n 13) (.n 6) 64), .atom (.load (.n 14) (.n 6) 80)]

/-- The remainder block's constants before the permutation. -/
def remZ : List Stmt :=
  [.atom (.const (.n 21) (word 1 0)), .atom (.const (.n 22) (word 0 0)),
    .atom (.const (.n 23) (word 0 0)), .atom (.const (.n 24) (word 0 0)),
    .atom (.const (.n 25) (word 0 0))]

/-- The remainder block's permutation. -/
def remK : Atom :=
  .keccak [.n 16, .n 17, .n 19, .n 20, .n 22, .n 23, .n 24, .n 25, .n 9, .n 10, .n 11, .n 12, .n 13]
    [.n 26, .n 27, .n 28, .n 29, .n 30, .n 31, .n 32, .n 33, .n 34, .n 35, .n 36, .n 37, .n 38]
    false false

/-- The remainder block's tail: the challenge stored, the claim and the scale, the next record. -/
def remT : List Stmt :=
  [.atom (.mul (.n 40) (.n 5) (.n 0)), .atom (.load (.n 39) (.n 40) 0),
    .atom (.add (.n 41) (.n 8) (.n 39)), .atom (.const (.n 42) (word 1 0)),
    .atom (.add (.n 43) (.n 42) (.n 41)), .atom (.load (.n 34) (.n 6) 1),
    .atom (.load (.n 35) (.n 6) 17), .atom (.load (.n 36) (.n 6) 33),
    .atom (.load (.n 37) (.n 6) 49), .atom (.load (.n 38) (.n 6) 65),
    .atom (.const (.n 44) (word 4 0)), .atom (.mul (.n 45) (.n 14) (.n 44)),
    .atom (.load (.n 45) (.n 6) 81), .atom (.load (.n 46) (.n 6) 96),
    .atom (.mul (.n 47) (.n 41) (.n 15)), .atom (.add (.n 48) (.n 46) (.n 47)),
    .atom (.mul (.n 49) (.n 39) (.n 39)), .atom (.add (.n 50) (.n 8) (.n 49)),
    .atom (.mul (.n 51) (.n 50) (.n 18)), .atom (.add (.n 52) (.n 48) (.n 51)),
    .atom (.mul (.n 53) (.n 43) (.n 52)), .atom (.load (.n 53) (.n 6) 97),
    .atom (.load (.n 54) (.n 6) 112), .atom (.mul (.n 55) (.n 54) (.n 43)),
    .atom (.load (.n 55) (.n 6) 113), .atom (.const (.n 56) (word 2 0)),
    .atom (.mul (.n 57) (.n 0) (.n 56)), .atom (.add (.n 58) (.n 57) (.n 1)),
    .atom (.const (.n 59) (word 2 0)), .atom (.mul (.n 60) (.n 0) (.n 59))]

theorem packRemPre_split : packRemPre = remA ++ fsNextT (.n 14) 0 15 ++ fsNextT (.n 14) 1 18 ++
    remZ ++ [.atom remK] ++ challengeT (.n 26) 39 ++ remT := rfl

/-- The remainder block's stores. -/
def packRemS : List Atom :=
  [.load (.n 39) (.n 40) 0, .load (.n 34) (.n 6) 1, .load (.n 35) (.n 6) 17,
    .load (.n 36) (.n 6) 33, .load (.n 37) (.n 6) 49, .load (.n 38) (.n 6) 65,
    .load (.n 45) (.n 6) 81, .load (.n 53) (.n 6) 97, .load (.n 55) (.n 6) 113]

theorem packRem_chk : Fwd.chk 6 packRemPre = some 61 := by decide +kernel

theorem packRem_stores : storesOf 6 packRemPre = packRemS := by decide +kernel

set_option maxRecDepth 20000 in
/-- **The remainder loop's block, completely**: an honest iteration at `x` makes every atom of
the block's honest valuation hold. -/
theorem packRemBlock_complete {x N rec pp tb pt : E} (hs : PackRemHon rd rec pp pt x) :
    ∃ σ : Val, [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5)] =
        [x, N, rec, pp, tb, pt] ∧
      (∀ a, Stmt.atom a ∈ packRemPre → a.Holds rd σ) ∧
      σ (.n 6) = rec * x ∧ σ (.n 7) = pp * x ∧ σ (.n 40) = pt * x ∧
      LoadHolds rd (rec * x) 80 (σ (.n 14)) ∧ σ (.n 58) = x * gen + N ∧
      σ (.n 60) = x * gen := by
  obtain ⟨cap, cur, claim, scale, r, g1, g2, ⟨⟨hcl, hcap⟩, lcur, lclm, lsc⟩, lr, hxs, lch,
    ⟨⟨hcl', hcap'⟩, lcur', lclm', lsc'⟩⟩ := hs
  obtain ⟨c0, c1, c2, c3, c4, rfl⟩ := five_of_length hcl
  set o := eqRound ⟨[c0, c1, c2, c3, c4], []⟩ g1 g2 r claim scale with ho
  -- the honest valuation
  set l : List E := [x, N, rec, pp, tb, pt] with hl
  have g := (ev_spec rd (fun _ ↦ 0) packRemPre l packRem_chk).2.2
  have pq : ∀ i (hi : i < 6), Val.ofArgs (ev rd (fun _ ↦ 0) l packRemPre) (.n i) = l.getD i 0 :=
    fun i hi ↦ ev_params rd (fun _ ↦ 0) (l := l) packRem_chk (by simpa [hl] using hi)
  rw [show l.length = 6 from rfl, packRem_stores] at g
  generalize Val.ofArgs (ev rd (fun _ ↦ 0) l packRemPre) = σ at g pq
  have p0 : σ (.n 0) = x := pq 0 (by norm_num)
  have p1 : σ (.n 1) = N := pq 1 (by norm_num)
  have p2 : σ (.n 2) = rec := pq 2 (by norm_num)
  have p3 : σ (.n 3) = pp := pq 3 (by norm_num)
  have p4 : σ (.n 4) = tb := pq 4 (by norm_num)
  have p5 : σ (.n 5) = pt := pq 5 (by norm_num)
  rw [packRemPre_split] at g
  have gA : ∀ a, Stmt.atom a ∈ remA → Good rd packRemS (fun _ ↦ 0) σ a := fun a ha ↦
    g (.atom a) (by simp only [List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ha))))))
  have g1' : ∀ s ∈ fsNextT (.n 14) 0 15, GoodS rd packRemS (fun _ ↦ 0) σ s := fun s hs ↦
    g _ (by simp only [List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hs))))))
  have g2' : ∀ s ∈ fsNextT (.n 14) 1 18, GoodS rd packRemS (fun _ ↦ 0) σ s := fun s hs ↦
    g _ (by simp only [List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hs)))))
  have gZ : ∀ a, Stmt.atom a ∈ remZ → Good rd packRemS (fun _ ↦ 0) σ a := fun a ha ↦
    g (.atom a) (by simp only [List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inr ha))))
  have gK : Good rd packRemS (fun _ ↦ 0) σ remK :=
    g (.atom remK) (by simp only [List.mem_append]; exact Or.inl (Or.inl (Or.inr (List.mem_singleton_self _))))
  have gC : ∀ s ∈ challengeT (.n 26) 39, GoodS rd packRemS (fun _ ↦ 0) σ s := fun s hs ↦
    g _ (by simp only [List.mem_append]; exact Or.inl (Or.inr hs))
  have gT : ∀ a, Stmt.atom a ∈ remT → Good rd packRemS (fun _ ↦ 0) σ a := fun a ha ↦
    g (.atom a) (by simp only [List.mem_append]; exact Or.inr ha)
  -- the head
  have e6 : σ (.n 6) = σ (.n 2) * σ (.n 0) := good_mul (by decide) (gA _ (by simp [remA]))
  have e7 : σ (.n 7) = σ (.n 3) * σ (.n 0) := good_mul (by decide) (gA _ (by simp [remA]))
  have v6 : σ (.n 6) = rec * x := by rw [e6, p2, p0]
  have v7 : σ (.n 7) = pp * x := by rw [e7, p3, p0]
  have L0 : LoadHolds rd (rec * x) 0 c0 := hcap 0 (by simp)
  have L16 : LoadHolds rd (rec * x) 16 c1 := hcap 1 (by simp)
  have L32 : LoadHolds rd (rec * x) 32 c2 := hcap 2 (by simp)
  have L48 : LoadHolds rd (rec * x) 48 c3 := hcap 3 (by simp)
  have L64 : LoadHolds rd (rec * x) 64 c4 := hcap 4 (by simp)
  have L80 : LoadHolds rd (rec * x) 80 cur := lcur
  have L96 : LoadHolds rd (rec * x) 96 claim := lclm
  have L112 : LoadHolds rd (rec * x) 112 scale := lsc
  have v8 : σ (.n 8) = r := load_val (gA (.load (.n 8) (.n 7) 0) (by simp [remA])) (by decide)
    (by rw [v7]; exact lr)
  have v9 : σ (.n 9) = c0 := load_val (gA (.load (.n 9) (.n 6) 0) (by simp [remA])) (by decide)
    (by rw [v6]; exact L0)
  have v10 : σ (.n 10) = c1 := load_val (gA (.load (.n 10) (.n 6) 16) (by simp [remA])) (by decide)
    (by rw [v6]; exact L16)
  have v11 : σ (.n 11) = c2 := load_val (gA (.load (.n 11) (.n 6) 32) (by simp [remA])) (by decide)
    (by rw [v6]; exact L32)
  have v12 : σ (.n 12) = c3 := load_val (gA (.load (.n 12) (.n 6) 48) (by simp [remA])) (by decide)
    (by rw [v6]; exact L48)
  have v13 : σ (.n 13) = c4 := load_val (gA (.load (.n 13) (.n 6) 64) (by simp [remA])) (by decide)
    (by rw [v6]; exact L64)
  have v14 : σ (.n 14) = cur := load_val (gA (.load (.n 14) (.n 6) 80) (by simp [remA])) (by decide)
    (by rw [v6]; exact L80)
  -- the two words
  have lg1 : LoadHolds rd (σ (.n 14)) 0 g1 := by rw [v14]; exact hxs 0 (by simp)
  have lg2 : LoadHolds rd (σ (.n 14)) 1 g2 := by rw [v14]; exact hxs 1 (by simp)
  obtain ⟨e15, -, H1⟩ := fsNext_complete (C := fun _ _ _ ↦ True) g1' (by decide) lg1
  obtain ⟨e18, -, H2⟩ := fsNext_complete (C := fun _ _ _ ↦ True) g2' (by decide) lg2
  have H1' := ((holdsList_atoms (fsNextT_atoms (.n 14) 0 15) True (fun _ ↦ False)).1 (H1 trivial)).1
  have H2' := ((holdsList_atoms (fsNextT_atoms (.n 14) 1 18) True (fun _ ↦ False)).1 (H2 trivial)).1
  -- the permutation
  have z : ∀ v ∈ [22, 23, 24, 25], σ (.n v) = 0 := by
    intro v hv
    have := gZ (.const (.n v) (word 0 0)) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl <;> simp [remZ])
    simpa [Good, word_zero] using this
  have hz : [V.n 22, .n 23, .n 24, .n 25].map σ = [0, 0, 0, 0] := by
    simp [z 22 (by simp), z 23 (by simp), z 24 (by simp), z 25 (by simp)]
  have hk : remK.Holds rd σ := keccakA_complete gK
  obtain ⟨hch, H4⟩ := challenge_complete (C := fun _ _ _ ↦ True) gC
  have H4' := ((holdsList_atoms (challengeT_atoms (.n 26) 39) True
    (fun _ ↦ False)).1 (H4 trivial)).1
  have q0 := sq2_atoms (rd := rd) (a := 15) (o := 26) (zs := [.n 22, .n 23, .n 24, .n 25])
    (capV := [.n 9, .n 10, .n 11, .n 12, .n 13]) (cap := [c0, c1, c2, c3, c4])
    (fsNextT_facts (rd := rd) (σ := σ) H1').2 (fsNextT_facts (rd := rd) (σ := σ) H2').2 hk hch hz
    (by simp [v9, v10, v11, v12, v13])
  simp only [Nat.reduceAdd] at q0
  rw [e15, e18] at q0
  have v39 : σ (.n 39) = o.1 := q0.1
  have vcap : [σ (.n 34), σ (.n 35), σ (.n 36), σ (.n 37), σ (.n 38)] = o.2.2.2.cap := q0.2
  -- the tail
  have e40 : σ (.n 40) = σ (.n 5) * σ (.n 0) := good_mul (by decide) (gT _ (by simp [remT]))
  have v40 : σ (.n 40) = pt * x := by rw [e40, p5, p0]
  have e41 : σ (.n 41) = σ (.n 8) + σ (.n 39) := gT (.add (.n 41) (.n 8) (.n 39)) (by simp [remT])
  have e42 : σ (.n 42) = word 1 0 := gT (.const (.n 42) (word 1 0)) (by simp [remT])
  have e43 : σ (.n 43) = σ (.n 42) + σ (.n 41) := gT (.add (.n 43) (.n 42) (.n 41)) (by simp [remT])
  have e44 : σ (.n 44) = word 4 0 := gT (.const (.n 44) (word 4 0)) (by simp [remT])
  have e45 : σ (.n 45) = σ (.n 14) * σ (.n 44) := good_mul (by decide) (gT _ (by simp [remT]))
  have v46 : σ (.n 46) = claim := load_val (gT (.load (.n 46) (.n 6) 96) (by simp [remT]))
    (by decide) (by rw [v6]; exact L96)
  have e47 : σ (.n 47) = σ (.n 41) * σ (.n 15) := good_mul (by decide) (gT _ (by simp [remT]))
  have e48 : σ (.n 48) = σ (.n 46) + σ (.n 47) := gT (.add (.n 48) (.n 46) (.n 47)) (by simp [remT])
  have e49 : σ (.n 49) = σ (.n 39) * σ (.n 39) := good_mul (by decide) (gT _ (by simp [remT]))
  have e50 : σ (.n 50) = σ (.n 8) + σ (.n 49) := gT (.add (.n 50) (.n 8) (.n 49)) (by simp [remT])
  have e51 : σ (.n 51) = σ (.n 50) * σ (.n 18) := good_mul (by decide) (gT _ (by simp [remT]))
  have e52 : σ (.n 52) = σ (.n 48) + σ (.n 51) := gT (.add (.n 52) (.n 48) (.n 51)) (by simp [remT])
  have e53 : σ (.n 53) = σ (.n 43) * σ (.n 52) := good_mul (by decide) (gT _ (by simp [remT]))
  have v54 : σ (.n 54) = scale := load_val (gT (.load (.n 54) (.n 6) 112) (by simp [remT]))
    (by decide) (by rw [v6]; exact L112)
  have e55 : σ (.n 55) = σ (.n 54) * σ (.n 43) := good_mul (by decide) (gT _ (by simp [remT]))
  have e56 : σ (.n 56) = word 2 0 := gT (.const (.n 56) (word 2 0)) (by simp [remT])
  have e57 : σ (.n 57) = σ (.n 0) * σ (.n 56) := good_mul (by decide) (gT _ (by simp [remT]))
  have e58 : σ (.n 58) = σ (.n 57) + σ (.n 1) := gT (.add (.n 58) (.n 57) (.n 1)) (by simp [remT])
  have e59 : σ (.n 59) = word 2 0 := gT (.const (.n 59) (word 2 0)) (by simp [remT])
  have e60 : σ (.n 60) = σ (.n 0) * σ (.n 59) := good_mul (by decide) (gT _ (by simp [remT]))
  have v45 : σ (.n 45) = cur * gen ^ 2 := by
    rw [e45, e44, v14, show (4 : ℕ) = 2 ^ 2 from rfl, word_two_pow (by decide)]
  have v53 : σ (.n 53) = o.2.1 := by
    rw [e53, e52, e51, e50, e49, e48, e47, e43, e42, e41, v46, v8, v39, e15, e18, word_one, ho]
    simp only [eqRound]
  have v55 : σ (.n 55) = o.2.2.1 := by
    rw [e55, e43, e42, e41, v54, v8, v39, word_one, ho]
    simp only [eqRound]
  have hcl'' : o.2.2.2.cap.length = 5 := hcl'
  have hO : ∀ j (hj : j < 5), LoadHolds rd (rec * x) (1 + j * 16)
      ([σ (.n 34), σ (.n 35), σ (.n 36), σ (.n 37), σ (.n 38)][j]'(by simpa using hj)) := by
    intro j hj
    have := hcap' j (by omega)
    simp only [krCap] at this
    convert this using 2
  refine ⟨σ, by rw [p0, p1, p2, p3, p4, p5], ?_, v6, v7, v40, by rw [v14]; exact L80,
    by rw [e58, e57, e56, p0, p1, word_gen], by rw [e60, e59, p0, word_gen]⟩
  rw [packRemPre_split]
  intro a ha
  simp only [List.mem_append] at ha
  rcases ha with ((((((ha | ha) | ha) | ha) | ha) | ha) | ha)
  · simp only [remA, List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact holds_mul (by decide) (gA _ (by simp [remA]))
    · exact holds_mul (by decide) (gA _ (by simp [remA]))
    · exact holds_read (by decide) (gA _ (by simp [remA])) (by rw [v7]; exact lr)
    · exact holds_read (by decide) (gA _ (by simp [remA])) (by rw [v6]; exact L0)
    · exact holds_read (by decide) (gA _ (by simp [remA])) (by rw [v6]; exact L16)
    · exact holds_read (by decide) (gA _ (by simp [remA])) (by rw [v6]; exact L32)
    · exact holds_read (by decide) (gA _ (by simp [remA])) (by rw [v6]; exact L48)
    · exact holds_read (by decide) (gA _ (by simp [remA])) (by rw [v6]; exact L64)
    · exact holds_read (by decide) (gA _ (by simp [remA])) (by rw [v6]; exact L80)
  · exact H1' a ha
  · exact H2' a ha
  · simp only [remZ, List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> exact holds_of_pure rfl (gZ _ (by simp [remZ]))
  · simp only [List.mem_singleton, Stmt.atom.injEq] at ha
    subst ha
    exact hk
  · exact H4' a ha
  · simp only [remT, List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
    · exact holds_mul (by decide) (gT _ (by simp [remT]))
    · exact holds_store (by decide) (gT _ (by simp [remT])) (by rw [v40, v39]; exact lch)
    · exact e41
    · exact e42
    · exact e43
    · exact holds_store (by decide) (gT _ (by simp [remT])) (by rw [v6]; exact hO 0 (by norm_num))
    · exact holds_store (by decide) (gT _ (by simp [remT])) (by rw [v6]; exact hO 1 (by norm_num))
    · exact holds_store (by decide) (gT _ (by simp [remT])) (by rw [v6]; exact hO 2 (by norm_num))
    · exact holds_store (by decide) (gT _ (by simp [remT])) (by rw [v6]; exact hO 3 (by norm_num))
    · exact holds_store (by decide) (gT _ (by simp [remT])) (by rw [v6]; exact hO 4 (by norm_num))
    · exact e44
    · exact holds_mul (by decide) (gT _ (by simp [remT]))
    · exact holds_store (by decide) (gT _ (by simp [remT])) (by rw [v6, v45]; exact lcur')
    · exact holds_read (by decide) (gT _ (by simp [remT])) (by rw [v6]; exact L96)
    · exact holds_mul (by decide) (gT _ (by simp [remT]))
    · exact e48
    · exact holds_mul (by decide) (gT _ (by simp [remT]))
    · exact e50
    · exact holds_mul (by decide) (gT _ (by simp [remT]))
    · exact e52
    · exact holds_mul (by decide) (gT _ (by simp [remT]))
    · exact holds_store (by decide) (gT _ (by simp [remT])) (by rw [v6, v53]; exact lclm')
    · exact holds_read (by decide) (gT _ (by simp [remT])) (by rw [v6]; exact L112)
    · exact holds_mul (by decide) (gT _ (by simp [remT]))
    · exact holds_store (by decide) (gT _ (by simp [remT])) (by rw [v6, v55]; exact lsc')
    · exact e56
    · exact holds_mul (by decide) (gT _ (by simp [remT]))
    · exact e58
    · exact e59
    · exact holds_mul (by decide) (gT _ (by simp [remT]))

end
end LeanVM.Guest.B1.VerifySub
