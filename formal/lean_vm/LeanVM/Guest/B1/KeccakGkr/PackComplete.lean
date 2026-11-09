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
the eight-round loop at `x` (`Pack8Hon`: `Pack8Step` with a canonical capacity), the honest
valuation (`Fwd.ev` of `pack8Pre` on `[x, N, rec, pp, pt]`) makes every atom of the block hold;
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
previous, every capacity after a round canonical. -/
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

theorem eqRound_cap_canonical {s : Fs} {g1 g2 r cl sc ch cl' sc' : E} {cap' : List E}
    (h : eqRound s g1 g2 r cl sc = (ch, cl', sc', ⟨cap', []⟩)) : AllCanonical cap' := by
  have := congrArg (fun o ↦ o.2.2.2.cap) h
  simp only [eqRound] at this
  rw [← this]
  exact squeeze_cap_canonical _

/-! ## A round, completely -/

theorem packRound_mem {pp cu pt : V} {q b c : ℕ} {pre : List Stmt} {zs cap : List V} {cl sc : V} :
    (∀ s ∈ fsNextT cu (2 * q) (b + 1), s ∈ packRoundT pp cu pt q b c pre zs cap cl sc) ∧
    (∀ s ∈ fsNextT cu (2 * q + 1) (b + 11), s ∈ packRoundT pp cu pt q b c pre zs cap cl sc) ∧
    (∀ s ∈ pre, s ∈ packRoundT pp cu pt q b c pre zs cap cl sc) ∧
    (∀ s ∈ challengeT (.n c) (.n (c + 1)) (c + 13), s ∈ packRoundT pp cu pt q b c pre zs cap cl sc) := by
  refine ⟨fun s hs ↦ ?_, fun s hs ↦ ?_, fun s hs ↦ ?_, fun s hs ↦ ?_⟩ <;>
    simp only [packRoundT, List.mem_append]
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hs)))))
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hs))))
  · exact Or.inl (Or.inl (Or.inl (Or.inr hs)))
  · exact Or.inl (Or.inr hs)

/-- **A round, completely**: on a valuation satisfying the round's equations, its coordinate and
two words in memory (not stores), its zero cells zero, its capacity canonical and its challenge's
slot (a store) holding the honest challenge, every atom of the round holds, and the round is
`eqRound` of them. -/
theorem packRound_complete {pp cu pt : V} {q b c : ℕ} {pre : List Stmt} {zs cap : List V}
    {cl sc : V} (hbc : b + 21 ≤ c) (hsc : sc.idx < c + 30)
    (hg : ∀ s ∈ packRoundT pp cu pt q b c pre zs cap cl sc, GoodS rd S w σ s)
    (hpre : ∀ a, Stmt.atom a ∈ pre → a.Holds rd σ) (hz : zs.map σ = [0, 0, 0, 0])
    (hcap : AllCanonical (cap.map σ))
    (s1 : Atom.load (.n b) pp q ∉ S) (s2 : Atom.load (.n (b + 1)) cu (2 * q) ∉ S)
    (s3 : Atom.load (.n (b + 11)) cu (2 * q + 1) ∉ S) (s4 : Atom.load (.n (c + 19)) pt q ∈ S)
    {r g1 g2 : E} (lr : LoadHolds rd (σ pp) q r) (lg1 : LoadHolds rd (σ cu) (2 * q) g1)
    (lg2 : LoadHolds rd (σ cu) (2 * q + 1) g2)
    (lch : LoadHolds rd (σ pt) q (eqRound ⟨cap.map σ, []⟩ g1 g2 r (σ cl) (σ sc)).1) :
    (∀ a, Stmt.atom a ∈ packRoundT pp cu pt q b c pre zs cap cl sc → a.Holds rd σ) ∧
      eqRound ⟨cap.map σ, []⟩ g1 g2 r (σ cl) (σ sc) =
        (σ (.n (c + 19)), σ (.n (c + 29)), σ (.n (c + 30)), ⟨(cap5 (c + 8)).map σ, []⟩) := by
  obtain ⟨m1, m2, m3, m4⟩ := packRound_mem (pp := pp) (cu := cu) (pt := pt) (q := q) (b := b)
    (c := c) (pre := pre) (zs := zs) (cap := cap) (cl := cl) (sc := sc)
  have g0 : Good rd S w σ (.load (.n b) pp q) := hg (.atom (.load (.n b) pp q)) (by simp [packRoundT])
  obtain ⟨e1, c1a, c1b, -, H1⟩ := fsNext_complete (C := fun _ _ _ ↦ True) (fun s hs ↦ hg s (m1 s hs))
    s2 lg1
  obtain ⟨e2, c2a, c2b, -, H2⟩ := fsNext_complete (C := fun _ _ _ ↦ True) (fun s hs ↦ hg s (m2 s hs))
    s3 lg2
  have H1' := ((holdsList_atoms (fsNextT_atoms cu (2 * q) (b + 1)) True (fun _ ↦ False)).1
    (H1 trivial)).1
  have H2' := ((holdsList_atoms (fsNextT_atoms cu (2 * q + 1) (b + 11)) True (fun _ ↦ False)).1
    (H2 trivial)).1
  -- the permutation
  have gk : Good rd S w σ (.keccak ([V.n (b + 8), .n (b + 10), .n (b + 18), .n (b + 20)] ++ zs ++ cap)
      ((List.range 13).map fun k ↦ .n (c + k)) false false) :=
    hg (.atom (.keccak ([V.n (b + 8), .n (b + 10), .n (b + 18), .n (b + 20)] ++ zs ++ cap)
      ((List.range 13).map fun k ↦ .n (c + k)) false false)) (by simp [packRoundT, keccakA])
  have hk := keccakA_complete gk (by
    intro x hx
    simp only [List.map_append, List.mem_append, List.map_cons, List.map_nil, hz,
      List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (((rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl)) | hx)
    · simpa [Nat.add_assoc] using c1a
    · simpa [Nat.add_assoc] using c1b
    · simpa [Nat.add_assoc] using c2a
    · simpa [Nat.add_assoc] using c2b
    all_goals first | exact canon_zero | exact hcap _ hx)
  obtain ⟨-, -, -, hout⟩ := keccak_outs hk
  have hc1 : IsCanonical128 (σ (.n (c + 1))) := by
    have := hout 1 (by norm_num)
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by norm_num : 1 < 13),
      Option.map_some, Option.getD_some] at this
    rw [this]; exact cellsOfState_canonical _ _ _
  obtain ⟨hch, H4⟩ := challenge_complete (C := fun _ _ _ ↦ True) (fun s hs ↦ hg s (m4 s hs)) hc1
  have H4' := ((holdsList_atoms (challengeT_atoms (.n c) (.n (c + 1)) (c + 13)) True
    (fun _ ↦ False)).1 (H4 trivial)).1
  -- the challenge's value
  have p1 : FsPackOk σ (.n (b + 1)) (b + 1 + 1) dsObserve :=
    (fsNextT_facts (rd := rd) (σ := σ) H1').2
  have p2 : FsPackOk σ (.n (b + 1 + 10)) (b + 1 + 10 + 1) dsObserve := by
    simpa [Nat.add_assoc] using (fsNextT_facts (rd := rd) (σ := σ) H2').2
  have q0 := sq2_atoms (rd := rd) (a := b + 1) (o := c) (zs := zs) (capV := cap)
    (cap := cap.map σ) p1 p2 (by simpa [Nat.add_assoc] using hk) hch hz rfl
  have e1' : σ (.n (b + 1)) = g1 := e1
  have e2' : σ (.n (b + 1 + 10)) = g2 := by simpa [Nat.add_assoc] using e2
  rw [e1', e2'] at q0
  have v19 : σ (.n (c + 19)) = (eqRound ⟨cap.map σ, []⟩ g1 g2 r (σ cl) (σ sc)).1 := by
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
    · have gt : ∀ x, Stmt.atom x ∈ [Stmt.atom (.load (.n (c + 19)) pt q),
          .atom (.add (.n (c + 20)) (.n b) (.n (c + 19))),
          .atom (.const (.n (c + 21)) (word 1 0 0)),
          .atom (.add (.n (c + 22)) (.n (c + 21)) (.n (c + 20))),
          .atom (.mul (.n (c + 23)) (.n (c + 20)) (.n (b + 1))),
          .atom (.add (.n (c + 24)) cl (.n (c + 23))),
          .atom (.mul (.n (c + 25)) (.n (c + 19)) (.n (c + 19))),
          .atom (.add (.n (c + 26)) (.n b) (.n (c + 25))),
          .atom (.mul (.n (c + 27)) (.n (c + 26)) (.n (b + 11))),
          .atom (.add (.n (c + 28)) (.n (c + 24)) (.n (c + 27))),
          .atom (.mul (.n (c + 29)) (.n (c + 22)) (.n (c + 28))),
          .atom (.mul (.n (c + 30)) sc (.n (c + 22)))] → Good rd S w σ x :=
        fun x hx ↦ hg (.atom x) (by simp only [packRoundT, List.mem_append]; exact Or.inr hx)
      simp only [List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact holds_store s4 (gt _ (by simp)) (by rw [v19]; exact lch)
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
  rw [er, e1, show σ (.n (b + 11)) = g2 from by simpa [Nat.add_assoc] using e2] at F
  exact F.2.2.2.2

/-! ## The eight-round loop's block -/

theorem five_of_length {l : List E} (h : l.length = 5) :
    ∃ a b c d e, l = [a, b, c, d, e] := by
  match l, h with
  | [a, b, c, d, e], _ => exact ⟨a, b, c, d, e, rfl⟩

/-- **An honest iteration of the eight-round loop at `x`**: `Pack8Step` with a canonical
capacity. -/
def Pack8Hon (rd : Reader) (rec pp pt x : E) : Prop :=
  ∃ (cap : List E) (cur claim scale : E) (rs : List E) (ms : List (E × E)) (chs : List E)
    (claim' scale' : E) (cap' : List E),
    RoundRec rd (rec * x) 0 cap cur claim scale ∧ AllCanonical cap ∧ rs.length = 8 ∧
      ReadsAt rd (pp * x ^ 8) rs ∧ ReadsAt rd cur (ms.flatMap fun m ↦ [m.1, m.2]) ∧
      EqChain rs ms claim scale cap chs claim' scale' cap' ∧ ReadsAt rd (pt * x ^ 8) chs ∧
      RoundRec rd (rec * x) 1 cap' (cur * gen ^ 16) claim' scale'

/-- The stores of the eight-round loop's block: the challenges' slots, the next record. -/
def pack8S : List Atom :=
  ((List.range 8).map fun q ↦ Atom.load (.n (67 + 52 * q)) (.n 13) q) ++
  [.load (.n 420) (.n 5) 1, .load (.n 421) (.n 5) 17, .load (.n 422) (.n 5) 33,
    .load (.n 423) (.n 5) 49, .load (.n 424) (.n 5) 65, .load (.n 444) (.n 5) 81,
    .load (.n 441) (.n 5) 97, .load (.n 442) (.n 5) 113]

theorem pack8_chk : Fwd.chk 5 pack8Pre = some 450 := by decide +kernel

theorem pack8_stores : storesOf 5 pack8Pre = pack8S := by decide +kernel

theorem pack8S_round : ∀ q < 8, Atom.load (.n (pkB q)) (.n 9) q ∉ pack8S ∧
    Atom.load (.n (pkB q + 1)) (.n 19) (2 * q) ∉ pack8S ∧
    Atom.load (.n (pkB q + 11)) (.n 19) (2 * q + 1) ∉ pack8S ∧
    Atom.load (.n (pkC q + 19)) (.n 13) q ∈ pack8S := by decide +kernel

theorem pk8_mem_roundS {q : ℕ} (hq : q < 8) : ∀ s ∈ pkRound q, s ∈ pack8Pre := fun _ ha ↦
  List.mem_append_left _ (List.mem_append_right _
    (List.mem_flatten.2 ⟨pkRound q, List.mem_map.2 ⟨q, List.mem_range.2 hq, rfl⟩, ha⟩))

set_option maxRecDepth 20000 in
/-- **The eight-round loop's block, completely**: an honest iteration at `x` makes every atom of
the block's honest valuation hold. -/
theorem pack8Block_complete {x N rec pp pt : E} (hs : Pack8Hon rd rec pp pt x) :
    ∃ σ : Val, [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)] = [x, N, rec, pp, pt] ∧
      (∀ a, Stmt.atom a ∈ pack8Pre → a.Holds rd σ) ∧
      σ (.n 5) = rec * x ∧ σ (.n 9) = pp * x ^ 8 ∧ σ (.n 13) = pt * x ^ 8 ∧
      LoadHolds rd (rec * x) 80 (σ (.n 19)) ∧ σ (.n 447) = x * gen + N ∧
      σ (.n 449) = x * gen := by
  obtain ⟨cap, cur, claim, scale, rs, ms, chs, claim', scale', cap', ⟨⟨hcl, hcap⟩, lcur, lclm, lsc⟩,
    hcan, hrl, hrs, hms, hch, hchs, ⟨⟨hcl', hcap'⟩, lcur', lclm', lsc'⟩⟩ := hs
  obtain ⟨c0, c1, c2, c3, c4, rfl⟩ := five_of_length hcl
  obtain ⟨d0, d1, d2, d3, d4, rfl⟩ := five_of_length hcl'
  obtain ⟨hml, hchl⟩ := packEqChain_length hch
  obtain ⟨CL, SC, CAP, h0, h1, h2, h3, h4, h5, hst⟩ := eqChain_idx _ _ _ _ _ _ _ _ _ hch
  rw [hrl] at h3 h4 h5 hst
  have hcanC : ∀ q ≤ 8, AllCanonical (CAP q) := by
    intro q hq
    rcases q with _ | q
    · rw [h2]; exact hcan
    · exact eqRound_cap_canonical (hst q (by omega))
  -- the honest valuation
  set l : List E := [x, N, rec, pp, pt] with hl
  have g := (ev_spec rd (fun _ ↦ 0) pack8Pre l pack8_chk).2.2
  have pq : ∀ i (hi : i < 5), Val.ofArgs (ev rd (fun _ ↦ 0) l pack8Pre) (.n i) = l.getD i 0 :=
    fun i hi ↦ ev_params rd (fun _ ↦ 0) (l := l) pack8_chk (by simpa [hl] using hi)
  rw [show l.length = 5 from rfl, pack8_stores] at g
  generalize Val.ofArgs (ev rd (fun _ ↦ 0) l pack8Pre) = σ at g pq
  have p0 : σ (.n 0) = x := pq 0 (by norm_num)
  have p1 : σ (.n 1) = N := pq 1 (by norm_num)
  have p2 : σ (.n 2) = rec := pq 2 (by norm_num)
  have p3 : σ (.n 3) = pp := pq 3 (by norm_num)
  have p4 : σ (.n 4) = pt := pq 4 (by norm_num)
  have gH : ∀ a, Stmt.atom a ∈ pk8Head → Good rd pack8S (fun _ ↦ 0) σ a := fun a ha ↦
    g _ (List.mem_append_left _ (List.mem_append_left _ ha))
  have gT : ∀ a, Stmt.atom a ∈ pk8Tail → Good rd pack8S (fun _ ↦ 0) σ a := fun a ha ↦
    g _ (List.mem_append_right _ ha)
  -- the head
  have e5 : σ (.n 5) = σ (.n 2) * σ (.n 0) := good_mul (by decide) (gH _ (by simp [pk8Head]))
  have e6 : σ (.n 6) = σ (.n 0) * σ (.n 0) := good_mul (by decide) (gH _ (by simp [pk8Head]))
  have e7 : σ (.n 7) = σ (.n 6) * σ (.n 6) := good_mul (by decide) (gH _ (by simp [pk8Head]))
  have e8 : σ (.n 8) = σ (.n 7) * σ (.n 7) := good_mul (by decide) (gH _ (by simp [pk8Head]))
  have e9 : σ (.n 9) = σ (.n 3) * σ (.n 8) := good_mul (by decide) (gH _ (by simp [pk8Head]))
  have e10 : σ (.n 10) = σ (.n 0) * σ (.n 0) := good_mul (by decide) (gH _ (by simp [pk8Head]))
  have e11 : σ (.n 11) = σ (.n 10) * σ (.n 10) := good_mul (by decide) (gH _ (by simp [pk8Head]))
  have e12 : σ (.n 12) = σ (.n 11) * σ (.n 11) := good_mul (by decide) (gH _ (by simp [pk8Head]))
  have e13 : σ (.n 13) = σ (.n 4) * σ (.n 12) := good_mul (by decide) (gH _ (by simp [pk8Head]))
  have v5 : σ (.n 5) = rec * x := by rw [e5, p2, p0]
  have v9 : σ (.n 9) = pp * x ^ 8 := by rw [e9, p3, gen_pow_eight_of _ _ _ _ e6 e7 e8, p0]
  have v13 : σ (.n 13) = pt * x ^ 8 := by rw [e13, p4, gen_pow_eight_of _ _ _ _ e10 e11 e12, p0]
  have L0 : LoadHolds rd (rec * x) 0 c0 := hcap 0 (by simp)
  have L16 : LoadHolds rd (rec * x) 16 c1 := hcap 1 (by simp)
  have L32 : LoadHolds rd (rec * x) 32 c2 := hcap 2 (by simp)
  have L48 : LoadHolds rd (rec * x) 48 c3 := hcap 3 (by simp)
  have L64 : LoadHolds rd (rec * x) 64 c4 := hcap 4 (by simp)
  have L80 : LoadHolds rd (rec * x) 80 cur := lcur
  have L96 : LoadHolds rd (rec * x) 96 claim := lclm
  have L112 : LoadHolds rd (rec * x) 112 scale := lsc
  have v14 : σ (.n 14) = c0 := load_val (gH (.load (.n 14) (.n 5) 0) (by simp [pk8Head])) (by decide) (by rw [v5]; exact L0)
  have v15 : σ (.n 15) = c1 := load_val (gH (.load (.n 15) (.n 5) 16) (by simp [pk8Head])) (by decide) (by rw [v5]; exact L16)
  have v16 : σ (.n 16) = c2 := load_val (gH (.load (.n 16) (.n 5) 32) (by simp [pk8Head])) (by decide) (by rw [v5]; exact L32)
  have v17 : σ (.n 17) = c3 := load_val (gH (.load (.n 17) (.n 5) 48) (by simp [pk8Head])) (by decide) (by rw [v5]; exact L48)
  have v18 : σ (.n 18) = c4 := load_val (gH (.load (.n 18) (.n 5) 64) (by simp [pk8Head])) (by decide) (by rw [v5]; exact L64)
  have v19 : σ (.n 19) = cur := load_val (gH (.load (.n 19) (.n 5) 80) (by simp [pk8Head])) (by decide) (by rw [v5]; exact L80)
  have v20 : σ (.n 20) = claim := load_val (gH (.load (.n 20) (.n 5) 96) (by simp [pk8Head])) (by decide) (by rw [v5]; exact L96)
  have v21 : σ (.n 21) = scale := load_val (gH (.load (.n 21) (.n 5) 112) (by simp [pk8Head])) (by decide) (by rw [v5]; exact L112)
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
  have z : ∀ v ∈ [44, 45, 46, 47], σ (.n v) = 0 := by
    intro v hv
    have := g (.atom (.const (.n v) (word 0 0 0))) (pk8_mem_roundS (q := 0) (by norm_num) _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl <;> simp [pkRound, packRoundT, pkPre]))
    simpa [GoodS, Good, word_zero] using this
  have hz : pkZs.map σ = [0, 0, 0, 0] := by
    simp [pkZs, z 44 (by simp), z 45 (by simp), z 46 (by simp), z 47 (by simp)]
  have key : ∀ k ≤ 8, (pkCap k).map σ = CAP k ∧ σ (.n (pkCl k)) = CL k ∧
      σ (.n (pkSc k)) = SC k ∧ ∀ q < k, ∀ a, Stmt.atom a ∈ pkRound q → a.Holds rd σ := by
    intro k hk
    induction k with
    | zero =>
      refine ⟨?_, ?_, ?_, fun q hq ↦ absurd hq (Nat.not_lt_zero _)⟩
      · rw [h2]; simp [pkCap, cap5, v14, v15, v16, v17, v18]
      · rw [h0]; exact v20
      · rw [h1]; exact v21
    | succ k ih =>
      obtain ⟨ec, el, es, hr⟩ := ih (by omega)
      have hk8 : k < 8 := by omega
      obtain ⟨n1, n2, n3, n4⟩ := pack8S_round k hk8
      obtain ⟨lg1, lg2⟩ := readsAt_pairs_get hms (by omega : k < ms.length)
      have lr : LoadHolds rd (σ (.n 9)) k (rs.getD k 0) := by
        rw [v9, List.getD_eq_getElem _ _ (by omega)]; exact hrs k (by omega)
      have e := hst k hk8
      have lch : LoadHolds rd (σ (.n 13)) k (eqRound ⟨(pkCap k).map σ, []⟩ (ms.getD k (0, 0)).1
          (ms.getD k (0, 0)).2 (rs.getD k 0) (σ (.n (pkCl k))) (σ (.n (pkSc k)))).1 := by
        rw [ec, el, es, e, v13, List.getD_eq_getElem _ _ (by omega)]; exact hchs k (by omega)
      obtain ⟨Hk, ek⟩ := packRound_complete (rd := rd) (S := pack8S) (w := fun _ ↦ 0) (σ := σ)
        (pp := .n 9) (cu := .n 19) (pt := .n 13) (q := k) (b := pkB k) (c := pkC k)
        (pre := pkPre k) (zs := pkZs) (cap := pkCap k) (cl := .n (pkCl k)) (sc := .n (pkSc k))
        (by unfold pkB pkC; split <;> omega) (by show pkSc k < pkC k + 30; unfold pkSc pkC; split <;> omega)
        (fun s hs ↦ g s (pk8_mem_roundS hk8 s hs)) (hpre k hk8) hz
        (by rw [ec]; exact hcanC k (by omega)) n1 n2 n3 n4 lr (by rw [v19]; exact lg1)
        (by rw [v19]; exact lg2) lch
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
  rw [h3, show pkCl 8 = 441 from rfl] at kl
  rw [h4, show pkSc 8 = 442 from rfl] at ks
  simp only [pkCap, pkC, cap5] at kc
  norm_num at kc
  obtain ⟨w420, w421, w422, w423, w424⟩ := kc
  -- the tail
  have e443 : σ (.n 443) = word 65536 0 0 := gT (.const (.n 443) (word 65536 0 0)) (by simp [pk8Tail])
  have e444 : σ (.n 444) = σ (.n 19) * σ (.n 443) := good_mul (by decide) (gT _ (by simp [pk8Tail]))
  have v444 : σ (.n 444) = cur * gen ^ 16 := by
    rw [e444, e443, v19, show (65536 : ℕ) = 2 ^ 16 from rfl, word_two_pow (by decide)]
  have e445 : σ (.n 445) = word 2 0 0 := gT (.const (.n 445) (word 2 0 0)) (by simp [pk8Tail])
  have e446 : σ (.n 446) = σ (.n 0) * σ (.n 445) := good_mul (by decide) (gT _ (by simp [pk8Tail]))
  have e447 : σ (.n 447) = σ (.n 446) + σ (.n 1) := gT (.add (.n 447) (.n 446) (.n 1)) (by simp [pk8Tail])
  have e448 : σ (.n 448) = word 2 0 0 := gT (.const (.n 448) (word 2 0 0)) (by simp [pk8Tail])
  have e449 : σ (.n 449) = σ (.n 0) * σ (.n 448) := good_mul (by decide) (gT _ (by simp [pk8Tail]))
  have hO : ∀ j (hj : j < 5), LoadHolds rd (rec * x) (1 + j * 16) ([d0, d1, d2, d3, d4][j]'(by simpa using hj)) :=
    fun j hj ↦ hcap' j (by simpa using hj)
  refine ⟨σ, by rw [p0, p1, p2, p3, p4], ?_, v5, v9, v13, by rw [v19]; exact L80,
    by rw [e447, e446, e445, p0, p1, word_gen], by rw [e449, e448, p0, word_gen]⟩
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
      · exact holds_read (by decide) (gH _ (by simp [pk8Head])) (by rw [v5]; exact L0)
      · exact holds_read (by decide) (gH _ (by simp [pk8Head])) (by rw [v5]; exact L16)
      · exact holds_read (by decide) (gH _ (by simp [pk8Head])) (by rw [v5]; exact L32)
      · exact holds_read (by decide) (gH _ (by simp [pk8Head])) (by rw [v5]; exact L48)
      · exact holds_read (by decide) (gH _ (by simp [pk8Head])) (by rw [v5]; exact L64)
      · exact holds_read (by decide) (gH _ (by simp [pk8Head])) (by rw [v5]; exact L80)
      · exact holds_read (by decide) (gH _ (by simp [pk8Head])) (by rw [v5]; exact L96)
      · exact holds_read (by decide) (gH _ (by simp [pk8Head])) (by rw [v5]; exact L112)
    · obtain ⟨_, hm, ha⟩ := List.mem_flatten.1 ha
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hm
      exact kr q (List.mem_range.1 hq) a ha
  · simp only [pk8Tail, List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
    · exact holds_store (by decide) (gT _ (by simp [pk8Tail])) (by rw [v5, w420]; exact hO 0 (by norm_num))
    · exact holds_store (by decide) (gT _ (by simp [pk8Tail])) (by rw [v5, w421]; exact hO 1 (by norm_num))
    · exact holds_store (by decide) (gT _ (by simp [pk8Tail])) (by rw [v5, w422]; exact hO 2 (by norm_num))
    · exact holds_store (by decide) (gT _ (by simp [pk8Tail])) (by rw [v5, w423]; exact hO 3 (by norm_num))
    · exact holds_store (by decide) (gT _ (by simp [pk8Tail])) (by rw [v5, w424]; exact hO 4 (by norm_num))
    · exact e443
    · exact holds_mul (by decide) (gT _ (by simp [pk8Tail]))
    · exact holds_store (by decide) (gT _ (by simp [pk8Tail])) (by rw [v5, v444]; exact lcur')
    · exact holds_store (by decide) (gT _ (by simp [pk8Tail])) (by rw [v5, kl]; exact lclm')
    · exact holds_store (by decide) (gT _ (by simp [pk8Tail])) (by rw [v5, ks]; exact lsc')
    · exact e445
    · exact holds_mul (by decide) (gT _ (by simp [pk8Tail]))
    · exact e447
    · exact e448
    · exact holds_mul (by decide) (gT _ (by simp [pk8Tail]))

/-! ## The remainder loop's block -/

/-- **An honest iteration of the remainder loop at `x`**: `PackRemStep` with a canonical
capacity. -/
def PackRemHon (rd : Reader) (rec pp pt x : E) : Prop :=
  ∃ (cap : List E) (cur claim scale r g1 g2 : E),
    RoundRec rd (rec * x) 0 cap cur claim scale ∧ AllCanonical cap ∧ LoadHolds rd (pp * x) 0 r ∧
      ReadsAt rd cur [g1, g2] ∧
      LoadHolds rd (pt * x) 0 (eqRound ⟨cap, []⟩ g1 g2 r claim scale).1 ∧
      RoundRec rd (rec * x) 1 (eqRound ⟨cap, []⟩ g1 g2 r claim scale).2.2.2.cap (cur * gen ^ 2)
        (eqRound ⟨cap, []⟩ g1 g2 r claim scale).2.1 (eqRound ⟨cap, []⟩ g1 g2 r claim scale).2.2.1

/-- The remainder block's head: the record and the coordinate read. -/
def remA : List Stmt :=
  [.atom (.mul (.n 5) (.n 2) (.n 0)), .atom (.mul (.n 6) (.n 3) (.n 0)),
    .atom (.load (.n 7) (.n 6) 0), .atom (.load (.n 8) (.n 5) 0), .atom (.load (.n 9) (.n 5) 16),
    .atom (.load (.n 10) (.n 5) 32), .atom (.load (.n 11) (.n 5) 48),
    .atom (.load (.n 12) (.n 5) 64), .atom (.load (.n 13) (.n 5) 80)]

/-- The remainder block's constants before the permutation. -/
def remZ : List Stmt :=
  [.atom (.const (.n 34) (word 1 0 0)), .atom (.const (.n 35) (word 0 0 0)),
    .atom (.const (.n 36) (word 0 0 0)), .atom (.const (.n 37) (word 0 0 0)),
    .atom (.const (.n 38) (word 0 0 0))]

/-- The remainder block's permutation. -/
def remK : Atom :=
  .keccak [.n 21, .n 23, .n 31, .n 33, .n 35, .n 36, .n 37, .n 38, .n 8, .n 9, .n 10, .n 11, .n 12]
    [.n 39, .n 40, .n 41, .n 42, .n 43, .n 44, .n 45, .n 46, .n 47, .n 48, .n 49, .n 50, .n 51]
    false false

/-- The remainder block's tail: the challenge stored, the claim and the scale, the next record. -/
def remT : List Stmt :=
  [.atom (.mul (.n 59) (.n 4) (.n 0)), .atom (.load (.n 58) (.n 59) 0),
    .atom (.add (.n 60) (.n 7) (.n 58)), .atom (.const (.n 61) (word 1 0 0)),
    .atom (.add (.n 62) (.n 61) (.n 60)), .atom (.load (.n 47) (.n 5) 1),
    .atom (.load (.n 48) (.n 5) 17), .atom (.load (.n 49) (.n 5) 33),
    .atom (.load (.n 50) (.n 5) 49), .atom (.load (.n 51) (.n 5) 65),
    .atom (.const (.n 63) (word 4 0 0)), .atom (.mul (.n 64) (.n 13) (.n 63)),
    .atom (.load (.n 64) (.n 5) 81), .atom (.load (.n 65) (.n 5) 96),
    .atom (.mul (.n 66) (.n 60) (.n 14)), .atom (.add (.n 67) (.n 65) (.n 66)),
    .atom (.mul (.n 68) (.n 58) (.n 58)), .atom (.add (.n 69) (.n 7) (.n 68)),
    .atom (.mul (.n 70) (.n 69) (.n 24)), .atom (.add (.n 71) (.n 67) (.n 70)),
    .atom (.mul (.n 72) (.n 62) (.n 71)), .atom (.load (.n 72) (.n 5) 97),
    .atom (.load (.n 73) (.n 5) 112), .atom (.mul (.n 74) (.n 73) (.n 62)),
    .atom (.load (.n 74) (.n 5) 113), .atom (.const (.n 75) (word 2 0 0)),
    .atom (.mul (.n 76) (.n 0) (.n 75)), .atom (.add (.n 77) (.n 76) (.n 1)),
    .atom (.const (.n 78) (word 2 0 0)), .atom (.mul (.n 79) (.n 0) (.n 78))]

theorem packRemPre_split : packRemPre = remA ++ fsNextT (.n 13) 0 14 ++ fsNextT (.n 13) 1 24 ++
    remZ ++ [.atom remK] ++ challengeT (.n 39) (.n 40) 52 ++ remT := rfl

/-- The remainder block's stores. -/
def packRemS : List Atom :=
  [.load (.n 58) (.n 59) 0, .load (.n 47) (.n 5) 1, .load (.n 48) (.n 5) 17,
    .load (.n 49) (.n 5) 33, .load (.n 50) (.n 5) 49, .load (.n 51) (.n 5) 65,
    .load (.n 64) (.n 5) 81, .load (.n 72) (.n 5) 97, .load (.n 74) (.n 5) 113]

theorem packRem_chk : Fwd.chk 5 packRemPre = some 80 := by decide +kernel

theorem packRem_stores : storesOf 5 packRemPre = packRemS := by decide +kernel

set_option maxRecDepth 20000 in
/-- **The remainder loop's block, completely**: an honest iteration at `x` makes every atom of
the block's honest valuation hold. -/
theorem packRemBlock_complete {x N rec pp pt : E} (hs : PackRemHon rd rec pp pt x) :
    ∃ σ : Val, [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)] = [x, N, rec, pp, pt] ∧
      (∀ a, Stmt.atom a ∈ packRemPre → a.Holds rd σ) ∧
      σ (.n 5) = rec * x ∧ σ (.n 6) = pp * x ∧ σ (.n 59) = pt * x ∧
      LoadHolds rd (rec * x) 80 (σ (.n 13)) ∧ σ (.n 77) = x * gen + N ∧
      σ (.n 79) = x * gen := by
  obtain ⟨cap, cur, claim, scale, r, g1, g2, ⟨⟨hcl, hcap⟩, lcur, lclm, lsc⟩, hcan, lr, hxs, lch,
    ⟨⟨hcl', hcap'⟩, lcur', lclm', lsc'⟩⟩ := hs
  obtain ⟨c0, c1, c2, c3, c4, rfl⟩ := five_of_length hcl
  set o := eqRound ⟨[c0, c1, c2, c3, c4], []⟩ g1 g2 r claim scale with ho
  -- the honest valuation
  set l : List E := [x, N, rec, pp, pt] with hl
  have g := (ev_spec rd (fun _ ↦ 0) packRemPre l packRem_chk).2.2
  have pq : ∀ i (hi : i < 5), Val.ofArgs (ev rd (fun _ ↦ 0) l packRemPre) (.n i) = l.getD i 0 :=
    fun i hi ↦ ev_params rd (fun _ ↦ 0) (l := l) packRem_chk (by simpa [hl] using hi)
  rw [show l.length = 5 from rfl, packRem_stores] at g
  generalize Val.ofArgs (ev rd (fun _ ↦ 0) l packRemPre) = σ at g pq
  have p0 : σ (.n 0) = x := pq 0 (by norm_num)
  have p1 : σ (.n 1) = N := pq 1 (by norm_num)
  have p2 : σ (.n 2) = rec := pq 2 (by norm_num)
  have p3 : σ (.n 3) = pp := pq 3 (by norm_num)
  have p4 : σ (.n 4) = pt := pq 4 (by norm_num)
  rw [packRemPre_split] at g
  have gA : ∀ a, Stmt.atom a ∈ remA → Good rd packRemS (fun _ ↦ 0) σ a := fun a ha ↦
    g (.atom a) (by simp only [List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ha))))))
  have g1' : ∀ s ∈ fsNextT (.n 13) 0 14, GoodS rd packRemS (fun _ ↦ 0) σ s := fun s hs ↦
    g _ (by simp only [List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hs))))))
  have g2' : ∀ s ∈ fsNextT (.n 13) 1 24, GoodS rd packRemS (fun _ ↦ 0) σ s := fun s hs ↦
    g _ (by simp only [List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hs)))))
  have gZ : ∀ a, Stmt.atom a ∈ remZ → Good rd packRemS (fun _ ↦ 0) σ a := fun a ha ↦
    g (.atom a) (by simp only [List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inr ha))))
  have gK : Good rd packRemS (fun _ ↦ 0) σ remK :=
    g (.atom remK) (by simp only [List.mem_append]; exact Or.inl (Or.inl (Or.inr (List.mem_singleton_self _))))
  have gC : ∀ s ∈ challengeT (.n 39) (.n 40) 52, GoodS rd packRemS (fun _ ↦ 0) σ s := fun s hs ↦
    g _ (by simp only [List.mem_append]; exact Or.inl (Or.inr hs))
  have gT : ∀ a, Stmt.atom a ∈ remT → Good rd packRemS (fun _ ↦ 0) σ a := fun a ha ↦
    g (.atom a) (by simp only [List.mem_append]; exact Or.inr ha)
  -- the head
  have e5 : σ (.n 5) = σ (.n 2) * σ (.n 0) := good_mul (by decide) (gA _ (by simp [remA]))
  have e6 : σ (.n 6) = σ (.n 3) * σ (.n 0) := good_mul (by decide) (gA _ (by simp [remA]))
  have v5 : σ (.n 5) = rec * x := by rw [e5, p2, p0]
  have v6 : σ (.n 6) = pp * x := by rw [e6, p3, p0]
  have L0 : LoadHolds rd (rec * x) 0 c0 := hcap 0 (by simp)
  have L16 : LoadHolds rd (rec * x) 16 c1 := hcap 1 (by simp)
  have L32 : LoadHolds rd (rec * x) 32 c2 := hcap 2 (by simp)
  have L48 : LoadHolds rd (rec * x) 48 c3 := hcap 3 (by simp)
  have L64 : LoadHolds rd (rec * x) 64 c4 := hcap 4 (by simp)
  have L80 : LoadHolds rd (rec * x) 80 cur := lcur
  have L96 : LoadHolds rd (rec * x) 96 claim := lclm
  have L112 : LoadHolds rd (rec * x) 112 scale := lsc
  have v7 : σ (.n 7) = r := load_val (gA (.load (.n 7) (.n 6) 0) (by simp [remA])) (by decide)
    (by rw [v6]; exact lr)
  have v8 : σ (.n 8) = c0 := load_val (gA (.load (.n 8) (.n 5) 0) (by simp [remA])) (by decide)
    (by rw [v5]; exact L0)
  have v9 : σ (.n 9) = c1 := load_val (gA (.load (.n 9) (.n 5) 16) (by simp [remA])) (by decide)
    (by rw [v5]; exact L16)
  have v10 : σ (.n 10) = c2 := load_val (gA (.load (.n 10) (.n 5) 32) (by simp [remA])) (by decide)
    (by rw [v5]; exact L32)
  have v11 : σ (.n 11) = c3 := load_val (gA (.load (.n 11) (.n 5) 48) (by simp [remA])) (by decide)
    (by rw [v5]; exact L48)
  have v12 : σ (.n 12) = c4 := load_val (gA (.load (.n 12) (.n 5) 64) (by simp [remA])) (by decide)
    (by rw [v5]; exact L64)
  have v13 : σ (.n 13) = cur := load_val (gA (.load (.n 13) (.n 5) 80) (by simp [remA])) (by decide)
    (by rw [v5]; exact L80)
  -- the two words
  have lg1 : LoadHolds rd (σ (.n 13)) 0 g1 := by rw [v13]; exact hxs 0 (by simp)
  have lg2 : LoadHolds rd (σ (.n 13)) 1 g2 := by rw [v13]; exact hxs 1 (by simp)
  obtain ⟨e14, c21, c23, -, H1⟩ := fsNext_complete (C := fun _ _ _ ↦ True) g1' (by decide) lg1
  obtain ⟨e24, c31, c33, -, H2⟩ := fsNext_complete (C := fun _ _ _ ↦ True) g2' (by decide) lg2
  have H1' := ((holdsList_atoms (fsNextT_atoms (.n 13) 0 14) True (fun _ ↦ False)).1 (H1 trivial)).1
  have H2' := ((holdsList_atoms (fsNextT_atoms (.n 13) 1 24) True (fun _ ↦ False)).1 (H2 trivial)).1
  -- the permutation
  have z : ∀ v ∈ [35, 36, 37, 38], σ (.n v) = 0 := by
    intro v hv
    have := gZ (.const (.n v) (word 0 0 0)) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl <;> simp [remZ])
    simpa [Good, word_zero] using this
  have hz : [V.n 35, .n 36, .n 37, .n 38].map σ = [0, 0, 0, 0] := by
    simp [z 35 (by simp), z 36 (by simp), z 37 (by simp), z 38 (by simp)]
  have hk : remK.Holds rd σ := keccakA_complete gK (by
    intro y hy
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact c21
    · exact c23
    · exact c31
    · exact c33
    · rw [z 35 (by simp)]; exact canon_zero
    · rw [z 36 (by simp)]; exact canon_zero
    · rw [z 37 (by simp)]; exact canon_zero
    · rw [z 38 (by simp)]; exact canon_zero
    · rw [v8]; exact hcan _ (by simp)
    · rw [v9]; exact hcan _ (by simp)
    · rw [v10]; exact hcan _ (by simp)
    · rw [v11]; exact hcan _ (by simp)
    · rw [v12]; exact hcan _ (by simp))
  obtain ⟨-, -, -, hout⟩ := keccak_outs hk
  have hc40 : IsCanonical128 (σ (.n 40)) := by
    have := hout 1 (by norm_num)
    simp only [List.getD_cons_succ, List.getD_cons_zero] at this
    rw [this]; exact cellsOfState_canonical _ _ _
  obtain ⟨hch, H4⟩ := challenge_complete (C := fun _ _ _ ↦ True) gC hc40
  have H4' := ((holdsList_atoms (challengeT_atoms (.n 39) (.n 40) 52) True
    (fun _ ↦ False)).1 (H4 trivial)).1
  have q0 := sq2_atoms (rd := rd) (a := 14) (o := 39) (zs := [.n 35, .n 36, .n 37, .n 38])
    (capV := [.n 8, .n 9, .n 10, .n 11, .n 12]) (cap := [c0, c1, c2, c3, c4])
    (fsNextT_facts (rd := rd) (σ := σ) H1').2 (fsNextT_facts (rd := rd) (σ := σ) H2').2 hk hch hz
    (by simp [v8, v9, v10, v11, v12])
  simp only [Nat.reduceAdd] at q0
  rw [e14, e24] at q0
  have v58 : σ (.n 58) = o.1 := q0.1
  have vcap : [σ (.n 47), σ (.n 48), σ (.n 49), σ (.n 50), σ (.n 51)] = o.2.2.2.cap := q0.2
  -- the tail
  have e59 : σ (.n 59) = σ (.n 4) * σ (.n 0) := good_mul (by decide) (gT _ (by simp [remT]))
  have v59 : σ (.n 59) = pt * x := by rw [e59, p4, p0]
  have e60 : σ (.n 60) = σ (.n 7) + σ (.n 58) := gT (.add (.n 60) (.n 7) (.n 58)) (by simp [remT])
  have e61 : σ (.n 61) = word 1 0 0 := gT (.const (.n 61) (word 1 0 0)) (by simp [remT])
  have e62 : σ (.n 62) = σ (.n 61) + σ (.n 60) := gT (.add (.n 62) (.n 61) (.n 60)) (by simp [remT])
  have e63 : σ (.n 63) = word 4 0 0 := gT (.const (.n 63) (word 4 0 0)) (by simp [remT])
  have e64 : σ (.n 64) = σ (.n 13) * σ (.n 63) := good_mul (by decide) (gT _ (by simp [remT]))
  have v65 : σ (.n 65) = claim := load_val (gT (.load (.n 65) (.n 5) 96) (by simp [remT]))
    (by decide) (by rw [v5]; exact L96)
  have e66 : σ (.n 66) = σ (.n 60) * σ (.n 14) := good_mul (by decide) (gT _ (by simp [remT]))
  have e67 : σ (.n 67) = σ (.n 65) + σ (.n 66) := gT (.add (.n 67) (.n 65) (.n 66)) (by simp [remT])
  have e68 : σ (.n 68) = σ (.n 58) * σ (.n 58) := good_mul (by decide) (gT _ (by simp [remT]))
  have e69 : σ (.n 69) = σ (.n 7) + σ (.n 68) := gT (.add (.n 69) (.n 7) (.n 68)) (by simp [remT])
  have e70 : σ (.n 70) = σ (.n 69) * σ (.n 24) := good_mul (by decide) (gT _ (by simp [remT]))
  have e71 : σ (.n 71) = σ (.n 67) + σ (.n 70) := gT (.add (.n 71) (.n 67) (.n 70)) (by simp [remT])
  have e72 : σ (.n 72) = σ (.n 62) * σ (.n 71) := good_mul (by decide) (gT _ (by simp [remT]))
  have v73 : σ (.n 73) = scale := load_val (gT (.load (.n 73) (.n 5) 112) (by simp [remT]))
    (by decide) (by rw [v5]; exact L112)
  have e74 : σ (.n 74) = σ (.n 73) * σ (.n 62) := good_mul (by decide) (gT _ (by simp [remT]))
  have e75 : σ (.n 75) = word 2 0 0 := gT (.const (.n 75) (word 2 0 0)) (by simp [remT])
  have e76 : σ (.n 76) = σ (.n 0) * σ (.n 75) := good_mul (by decide) (gT _ (by simp [remT]))
  have e77 : σ (.n 77) = σ (.n 76) + σ (.n 1) := gT (.add (.n 77) (.n 76) (.n 1)) (by simp [remT])
  have e78 : σ (.n 78) = word 2 0 0 := gT (.const (.n 78) (word 2 0 0)) (by simp [remT])
  have e79 : σ (.n 79) = σ (.n 0) * σ (.n 78) := good_mul (by decide) (gT _ (by simp [remT]))
  have v64 : σ (.n 64) = cur * gen ^ 2 := by
    rw [e64, e63, v13, show (4 : ℕ) = 2 ^ 2 from rfl, word_two_pow (by decide)]
  have v72 : σ (.n 72) = o.2.1 := by
    rw [e72, e71, e70, e69, e68, e67, e66, e62, e61, e60, v65, v7, v58, e14, e24, word_one, ho]
    simp only [eqRound]
  have v74 : σ (.n 74) = o.2.2.1 := by
    rw [e74, e62, e61, e60, v73, v7, v58, word_one, ho]
    simp only [eqRound]
  have hcl'' : o.2.2.2.cap.length = 5 := hcl'
  have hO : ∀ j (hj : j < 5), LoadHolds rd (rec * x) (1 + j * 16)
      ([σ (.n 47), σ (.n 48), σ (.n 49), σ (.n 50), σ (.n 51)][j]'(by simpa using hj)) := by
    intro j hj
    have := hcap' j (by omega)
    simp only [krCap] at this
    convert this using 2
  refine ⟨σ, by rw [p0, p1, p2, p3, p4], ?_, v5, v6, v59, by rw [v13]; exact L80,
    by rw [e77, e76, e75, p0, p1, word_gen], by rw [e79, e78, p0, word_gen]⟩
  rw [packRemPre_split]
  intro a ha
  simp only [List.mem_append] at ha
  rcases ha with ((((((ha | ha) | ha) | ha) | ha) | ha) | ha)
  · simp only [remA, List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact holds_mul (by decide) (gA _ (by simp [remA]))
    · exact holds_mul (by decide) (gA _ (by simp [remA]))
    · exact holds_read (by decide) (gA _ (by simp [remA])) (by rw [v6]; exact lr)
    · exact holds_read (by decide) (gA _ (by simp [remA])) (by rw [v5]; exact L0)
    · exact holds_read (by decide) (gA _ (by simp [remA])) (by rw [v5]; exact L16)
    · exact holds_read (by decide) (gA _ (by simp [remA])) (by rw [v5]; exact L32)
    · exact holds_read (by decide) (gA _ (by simp [remA])) (by rw [v5]; exact L48)
    · exact holds_read (by decide) (gA _ (by simp [remA])) (by rw [v5]; exact L64)
    · exact holds_read (by decide) (gA _ (by simp [remA])) (by rw [v5]; exact L80)
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
    · exact holds_store (by decide) (gT _ (by simp [remT])) (by rw [v59, v58]; exact lch)
    · exact e60
    · exact e61
    · exact e62
    · exact holds_store (by decide) (gT _ (by simp [remT])) (by rw [v5]; exact hO 0 (by norm_num))
    · exact holds_store (by decide) (gT _ (by simp [remT])) (by rw [v5]; exact hO 1 (by norm_num))
    · exact holds_store (by decide) (gT _ (by simp [remT])) (by rw [v5]; exact hO 2 (by norm_num))
    · exact holds_store (by decide) (gT _ (by simp [remT])) (by rw [v5]; exact hO 3 (by norm_num))
    · exact holds_store (by decide) (gT _ (by simp [remT])) (by rw [v5]; exact hO 4 (by norm_num))
    · exact e63
    · exact holds_mul (by decide) (gT _ (by simp [remT]))
    · exact holds_store (by decide) (gT _ (by simp [remT])) (by rw [v5, v64]; exact lcur')
    · exact holds_read (by decide) (gT _ (by simp [remT])) (by rw [v5]; exact L96)
    · exact holds_mul (by decide) (gT _ (by simp [remT]))
    · exact e67
    · exact holds_mul (by decide) (gT _ (by simp [remT]))
    · exact e69
    · exact holds_mul (by decide) (gT _ (by simp [remT]))
    · exact e71
    · exact holds_mul (by decide) (gT _ (by simp [remT]))
    · exact holds_store (by decide) (gT _ (by simp [remT])) (by rw [v5, v72]; exact lclm')
    · exact holds_read (by decide) (gT _ (by simp [remT])) (by rw [v5]; exact L112)
    · exact holds_mul (by decide) (gT _ (by simp [remT]))
    · exact holds_store (by decide) (gT _ (by simp [remT])) (by rw [v5, v74]; exact lsc')
    · exact e75
    · exact holds_mul (by decide) (gT _ (by simp [remT]))
    · exact e77
    · exact e78
    · exact holds_mul (by decide) (gT _ (by simp [remT]))

end
end LeanVM.Guest.B1.VerifySub
