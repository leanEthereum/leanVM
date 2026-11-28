/-
  LeanVM.Guest.B1.VsC.KRoundsA

  `layer_rounds__L{n}` completes placed, storing its challenges into its caller's `point`.
-/

module

public import LeanVM.Guest.B1.VsC.RsRowsAllA
public import LeanVM.Guest.B1.KeccakGkr.LayerRounds
public import LeanVM.Guest.B1.KeccakGkr.PackChain
import LeanVM.Guest.CoreRef

/-!
# `layer_rounds`, placed

`layer_rounds__L{n}(fs0..fs4, cursor, run, prev_point, point, tabs)`, `n ≤ 16` (the guest stream's
template `lrBody n`, `KeccakGkr/LayerRounds.lean`), has no words of its own and no grind (`tabs` is
never read): it reads the `n` coordinates at `prev_point` and the `2n` messages at the cursor, and
stores round `q`'s challenge at `point[q]`, in its caller's buffer. On every memory holding these and
the honest challenges (`packRunF`'s) at `point`, its forward evaluation (`callAtA_fwd`) holds every
atom: the rounds other than their stores chain by `eqRound` (`packRound_factsNS`, `lr_chainNS`), so
the stored words are `packRunF`'s; the returns are then the guest stream's meaning (`lr_sound`). The
template's shape facts are one kernel decision per specialization (`lrOkA`).
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Guest.Value LeanVM.Guest
open LeanVM.Guest.B1.VerifySub
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The template's stores -/

/-- Round `q`'s store: its challenge at `point[q]`. -/
def lrStore (q : ℕ) : Atom := .load (.n (lrC q)) (.n 8) q

/-- The stores of `lrBody n`. -/
def lrStores (n : ℕ) : List Atom := (List.range n).map lrStore

/-- What the kernel checks of `layer_rounds__L{n}`'s template: a straight leaf, its loads through
`prev_point`, the cursor and `point`, no allocation, its stores the challenges', its returns
`lrRets n`, and a round's only store its own. -/
def lrOkA (n : ℕ) : Bool :=
  leafChecks 10 (lrBody n) &&
    (atomsOf (lrBody n)).all (loadOkB [(7, n), (5, 2 * n), (8, n)]) &&
    (atomsOf (lrBody n)).all (fun a => !atomAllocB a) &&
    storesOf 10 (lrBody n) == lrStores n && retOf (lrBody n) == some (lrRets n) &&
    (List.range n).all fun q => (atomsOf (lrRound q)).all fun a => !((lrStores n).contains a) || a == lrStore q

/-! ## A round without its store -/

section NS

variable {rd : Reader} {σ : Val}

/-- **A round's facts without its store**: `packRound_facts` from every atom of the round but the
store of its challenge. -/
theorem packRound_factsNS {pp cu pt : V} {q b c : ℕ} {pre : List Stmt} {zs cap : List V} {cl : V}
    (hbc : b + 4 < c)
    (H : ∀ a, Stmt.atom a ∈ packRoundT pp cu pt q b c pre zs cap cl → a ≠ .load (.n c) pt q → a.Holds rd σ)
    (hz : zs.map σ = [0, 0, 0, 0]) :
    LoadHolds rd (σ pp) q (σ (.n b)) ∧ LoadHolds rd (σ cu) (2 * q) (σ (.n (b + 1))) ∧
      LoadHolds rd (σ cu) (2 * q + 1) (σ (.n (b + 4))) ∧
      eqRound ⟨cap.map σ, []⟩ (σ (.n (b + 1))) (σ (.n (b + 4))) (σ (.n b)) (σ cl) =
        (σ (.n c), σ (.n (c + 19)), ⟨(cap5 (c + 8)).map σ, []⟩) := by
  have m1 : ∀ a, Stmt.atom a ∈ fsNextT cu (2 * q) (b + 1) → a.Holds rd σ := fun a ha ↦ by
    refine H a (by simp only [packRoundT, List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inl
      (Or.inr ha))))) ?_
    rintro rfl
    simp [fsNextT, fsPackT] at ha; omega
  have m2 : ∀ a, Stmt.atom a ∈ fsNextT cu (2 * q + 1) (b + 4) → a.Holds rd σ := fun a ha ↦ by
    refine H a (by simp only [packRoundT, List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inr ha)))) ?_
    rintro rfl
    simp [fsNextT, fsPackT] at ha; omega
  have hk : (Atom.keccak ([V.n (b + 2), .n (b + 3), .n (b + 5), .n (b + 6)] ++ zs ++ cap)
      ((List.range 13).map fun k ↦ .n (c + k)) false false).Holds rd σ :=
    H _ (by simp [packRoundT, keccakA]) (by simp)
  have l0 : LoadHolds rd (σ pp) q (σ (.n b)) :=
    H (.load (.n b) pp q) (by simp [packRoundT]) (by simp; omega)
  obtain ⟨l1, p1⟩ := fsNextT_facts m1
  obtain ⟨l2, p2⟩ := fsNextT_facts m2
  have q0 := sq2_atoms (a := b + 1) (o := c) (zs := zs) (capV := cap) (cap := cap.map σ) p1 p2
    (by simpa [Nat.add_assoc] using hk) hz rfl
  have e14 : σ (.n (c + 13)) = σ (.n b) + σ (.n c) :=
    H (.add (.n (c + 13)) (.n b) (.n c)) (by simp [packRoundT]) (by simp)
  have e17 : σ (.n (c + 14)) = σ (.n (c + 13)) * σ (.n (b + 1)) :=
    H (.mul (.n (c + 14)) (.n (c + 13)) (.n (b + 1))) (by simp [packRoundT]) (by simp)
  have e18 : σ (.n (c + 15)) = σ cl + σ (.n (c + 14)) :=
    H (.add (.n (c + 15)) cl (.n (c + 14))) (by simp [packRoundT]) (by simp)
  have e19 : σ (.n (c + 16)) = σ (.n c) * σ (.n c) :=
    H (.mul (.n (c + 16)) (.n c) (.n c)) (by simp [packRoundT]) (by simp)
  have e20 : σ (.n (c + 17)) = σ (.n b) + σ (.n (c + 16)) :=
    H (.add (.n (c + 17)) (.n b) (.n (c + 16))) (by simp [packRoundT]) (by simp)
  have e21 : σ (.n (c + 18)) = σ (.n (c + 17)) * σ (.n (b + 4)) :=
    H (.mul (.n (c + 18)) (.n (c + 17)) (.n (b + 4))) (by simp [packRoundT]) (by simp)
  have e22 : σ (.n (c + 19)) = σ (.n (c + 15)) + σ (.n (c + 18)) :=
    H (.add (.n (c + 19)) (.n (c + 15)) (.n (c + 18))) (by simp [packRoundT]) (by simp)
  have hsq : ((⟨cap.map σ, []⟩ : Fs).absorbAll [σ (.n (b + 1)), σ (.n (b + 4))] dsObserve).squeeze =
      (σ (.n c), ⟨(cap5 (c + 8)).map σ, []⟩) := by
    refine Prod.ext q0.1.symm ?_
    have h2 := q0.2
    simp only [cap5, List.map_cons, List.map_nil, Nat.add_assoc, Nat.reduceAdd] at h2 ⊢
    rw [h2]
    rfl
  refine ⟨l0, l1, l2, ?_⟩
  simp only [eqRound]
  rw [hsq]
  simp only [Prod.mk.injEq, true_and]
  refine ⟨?_, trivial⟩
  rw [e22, e21, e20, e19, e18, e17, e14]

theorem lrB_lt (q : ℕ) : lrB q + 4 < lrC q := by
  unfold lrB lrC; split <;> omega

/-- `lr_chain` from every atom of the rounds but their stores. -/
theorem lr_chainNS {N : ℕ} (hz : lrZs.map σ = [0, 0, 0, 0])
    (H : ∀ q < N, ∀ a, Stmt.atom a ∈ lrRound q → a ≠ lrStore q → a.Holds rd σ) : ∀ m k : ℕ, k + m ≤ N →
    EqChain ((List.range' k m).map fun q ↦ σ (.n (lrB q)))
      ((List.range' k m).map fun q ↦ (σ (.n (lrB q + 1)), σ (.n (lrB q + 4))))
      (σ (lrCl k)) ((lrCap k).map σ) ((List.range' k m).map fun q ↦ σ (.n (lrC q)))
      (σ (lrCl (k + m))) ((lrCap (k + m)).map σ)
  | 0, k, _ => ⟨rfl, rfl, rfl⟩
  | m + 1, k, hle => by
    have hf := packRound_factsNS (lrB_lt k) (H k (by omega)) hz
    simp only [List.range'_succ, List.map_cons]
    refine ⟨_, _, _, _, hf.2.2.2, rfl, ?_⟩
    have := lr_chainNS hz H m (k + 1) (by omega)
    rw [lrCap_succ, lrCl_succ, show k + 1 + m = k + (m + 1) by omega] at this
    exact this

end NS

/-! ## Lists of pairs -/

theorem flatMap_pairs_inj : ∀ (l1 l2 : List (E × E)),
    (l1.flatMap fun m ↦ [m.1, m.2]) = (l2.flatMap fun m ↦ [m.1, m.2]) → l1 = l2
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: l1, b :: l2, h => by
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.cons.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    rw [Prod.ext h1 h2, flatMap_pairs_inj l1 l2 h3]

theorem mem_lrBody_round {n q : ℕ} (hq : q < n) {a : Atom} (h : Stmt.atom a ∈ lrRound q) :
    Stmt.atom a ∈ lrBody n := by
  simp only [lrBody, lrPreBody, List.mem_append, List.mem_flatten, List.mem_map, List.mem_range]
  exact Or.inl (Or.inl (Or.inr ⟨_, ⟨q, hq, rfl⟩, h⟩))

theorem mem_lrBody_head {n : ℕ} {a : Atom} (h : Stmt.atom a ∈ lrHead) : Stmt.atom a ∈ lrBody n := by
  simp only [lrBody, lrPreBody, List.mem_append]
  exact Or.inl (Or.inl (Or.inl h))

/-! ## Placed -/

/-- A function whose body returns some values last is no loop helper. -/
theorem loop_false_of_ret {name : String} {fn : Fn} {hfind : coreProgram.find? name = some fn} {ss : List Stmt}
    {vs : List V} (hb : fn.body = ss ++ [.ret vs]) (hv : vs ≠ []) : coreProgram.loop name = false := by
  rw [Program.loop_of_find? hfind, Fn.loop, hb, List.reverse_append]
  cases vs with
  | nil => exact absurd rfl hv
  | cons v vs' => rfl

variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}

/-- `layer_rounds`' returns on the honest run: the capacity, the cursor past the `2n` words and the
claim. -/
noncomputable def lrRetsW (rs : List E) (ms : List (E × E)) (v cur : E) (f : List E) (n : ℕ) : List E :=
  (packRunF rs ms v ⟨f, []⟩).2.cap ++ [cur * gen ^ (2 * n), (packRunF rs ms v ⟨f, []⟩).1.1]

/-- What `layer_rounds` needs of the memory: the coordinates, the messages and the honest
challenges at `point`. -/
def KrPre (pp cur pt v : E) (f rs : List E) (ms : List (E × E)) (rd : Reader) : Prop :=
  ReadsAt rd pp rs ∧ ReadsAt rd cur (ms.flatMap fun m ↦ [m.1, m.2]) ∧
    ReadsAt rd pt (packRunF rs ms v ⟨f, []⟩).1.2

/-- The words `layer_rounds` reads and writes lie in the region `R`. -/
def KrRegion (pp cur pt : E) (n : ℕ) (R : ℕ → Prop) : Prop :=
  (∀ t < n, ∃ m, pp.limb 0 * addressOfIndex t = addressOfIndex m ∧ R m) ∧
    (∀ t < 2 * n, ∃ m, cur.limb 0 * addressOfIndex t = addressOfIndex m ∧ R m) ∧
    ∀ t < n, ∃ m, pt.limb 0 * addressOfIndex t = addressOfIndex m ∧ R m

set_option maxHeartbeats 1000000 in
/-- **`layer_rounds__L{n}` completes placed**, from its template. -/
theorem lr_placed {k : ℕ} {name : String} {fn : Fn} {n : ℕ} (hn : n ≤ 16)
    (hfind : coreProgram.find? name = some fn) (hparams : fn.params = lrParams)
    (hbody : fn.body = lrBody n) (hok : lrOkA n = true) {f0 f1 f2 f3 f4 cur v pp pt tabs : E}
    {rs : List E} {ms : List (E × E)} (hrs : rs.length = n) (hms : ms.length = n) {R : ℕ → Prop}
    (hR : KrRegion pp cur pt n R) (fp c0 : ℕ) :
    CallAtA fs al cert k name [f0, f1, f2, f3, f4, cur, v, pp, pt, tabs]
      (lrRetsW rs ms v cur [f0, f1, f2, f3, f4] n) R (fun _ => False) (fun _ => True)
      (KrPre pp cur pt v [f0, f1, f2, f3, f4] rs ms) PostQuiet (fs name) fp c0 c0 := by
  simp only [lrOkA, Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨⟨⟨⟨hck, hld⟩, hna⟩, hSeq⟩, hret⟩, hone⟩ := hok
  have hlp : coreProgram.loop name = false :=
    loop_false_of_ret (hfind := hfind) (by rw [hbody, lrBody]) (by unfold lrRets; split <;> simp)
  set args : List E := [f0, f1, f2, f3, f4, cur, v, pp, pt, tabs] with hargs
  have hck' : leafChecks args.length fn.body = true := by rw [hbody]; exact hck
  obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp (by
    simp only [leafChecks, Bool.and_eq_true] at hck'; exact hck'.1.1)
  have e := callAtA_fwd (fs := fs) (al := al) (cert := cert) (k := k) (R := R) (D := fun _ => False)
    (Out := fun _ => True) (fp := fp) (c := c0) (rets := lrRetsW rs ms v cur [f0, f1, f2, f3, f4] n)
    (fun _ => 0) [] [] hfind hlp (by rw [hparams]; rfl) hck'
    ⟨by simp, List.Pairwise.nil⟩ (fun _ _ => trivial) (fun _ h => h.elim)
    (Pre := KrPre pp cur pt v [f0, f1, f2, f3, f4] rs ms)
    fun rd _ _ ⟨hpp, hcur, hpt⟩ σ hσ => ?_
  · simpa using e
  set S := storesOf args.length fn.body with hS
  have hSr : S = lrStores n := by rw [hS, hbody]; exact hSeq
  have hG : ∀ a, Stmt.atom a ∈ fn.body → Good rd S (fun _ => 0) σ a := fun a ha => hσ ▸ fwd_good hc' a ha
  have hσp : ∀ i (hi : i < 10), σ (.n i) = args.getD i 0 := fun i hi => by
    rw [hσ]; exact fwd_param hc' (by simpa [hargs] using hi)
  have hσ5 : σ (.n 5) = cur := hσp 5 (by omega)
  have hσ7 : σ (.n 7) = pp := hσp 7 (by omega)
  have hσ8 : σ (.n 8) = pt := hσp 8 (by omega)
  have hok' : ∀ a, Stmt.atom a ∈ fn.body → loadOkB [(7, n), (5, 2 * n), (8, n)] a = true :=
    fun a ha => List.all_eq_true.mp hld a (mem_atomsOf' (hbody ▸ ha))
  have hload : ∀ d q off, Stmt.atom (.load d q off) ∈ fn.body →
      (q = .n 7 ∧ off < n) ∨ (q = .n 5 ∧ off < 2 * n) ∨ (q = .n 8 ∧ off < n) := fun d q off ha => by
    have h := hok' _ ha
    simpa only [loadOkB, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true, Bool.and_eq_true,
      beq_iff_eq, decide_eq_true_eq] using h
  have hchl : (packRunF rs ms v ⟨[f0, f1, f2, f3, f4], []⟩).1.2.length = n := by
    rw [packRunF_chs_length _ _ _ _ (by rw [hrs, hms]), hrs]
  have hcurl : (ms.flatMap fun m ↦ [m.1, m.2]).length = 2 * n := by rw [length_flatMap_pairs, hms]
  -- Every atom but the stores holds.
  have hside : ∀ a, Stmt.atom a ∈ fn.body → a ∉ S → needsSide a = true → Side rd S σ a := fun a ha haS hn => by
    cases a with
    | load d q off =>
      simp only [Side, haS, ↓reduceIte]
      rcases hload d q off ha with ⟨rfl, ho⟩ | ⟨rfl, ho⟩ | ⟨rfl, ho⟩
      · rw [hσ7]; exact ⟨(hpp off (by omega)).1, by rw [(hpp off (by omega)).2]; rfl⟩
      · rw [hσ5]; exact ⟨(hcur off (by omega)).1, by rw [(hcur off (by omega)).2]; rfl⟩
      · rw [hσ8]; exact ⟨(hpt off (by omega)).1, by rw [(hpt off (by omega)).2]; rfl⟩
    | hint => have := hok' _ ha; simp [loadOkB] at this
    | _ =>
      have := hok' _ ha
      simp only [loadOkB, hn, Bool.not_true, Bool.false_eq_true] at this
  have hns : ∀ a, Stmt.atom a ∈ fn.body → a ∉ S → a.Holds rd σ := fun a ha haS => by
    have := atoms_holds (S := S) (w := fun _ => 0) (rd := rd) (σ := σ) (atoms := [a])
      (fun b hb => by rw [List.mem_singleton] at hb; subst hb; exact hG b ha)
      (fun b hb hn => by rw [List.mem_singleton] at hb; subst hb; exact Or.inr (hside b ha haS hn))
    exact this a List.mem_cons_self
  -- The stores: the rounds chain without them.
  have hst : ∀ a ∈ S, a.Holds rd σ := by
    have Hr : ∀ q < n, ∀ a, Stmt.atom a ∈ lrRound q → a ≠ lrStore q → a.Holds rd σ := fun q hq a ha hne => by
      refine hns a (hbody ▸ mem_lrBody_round hq ha) ?_
      have h1 := List.all_eq_true.mp (List.all_eq_true.mp hone q (List.mem_range.mpr hq)) a (mem_atomsOf' ha)
      rw [hSr]
      intro hm
      simp only [Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at h1
      rcases h1 with h1 | h1
      · simp [hm] at h1
      · exact hne h1
    intro a ha
    rw [hSr] at ha
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
    have hq : q < n := List.mem_range.mp hq
    have hpos : 0 < n := by omega
    have hz : lrZs.map σ = [0, 0, 0, 0] := by
      have Z : ∀ k, 31 ≤ k → k < 35 → σ (.n k) = 0 := fun k h1 h2 ↦ by
        have := Hr 0 hpos (.const (.n k) (word 0 0)) (by
          simp only [lrRound, packRoundT, lrPre, ↓reduceIte, List.mem_append, List.mem_cons]
          interval_cases k <;> simp) (by simp [lrStore])
        simpa [Atom.Holds, Tables.tb_word_zero] using this
      simp only [lrZs, List.map_cons, List.map_nil]
      rw [Z 31 (by omega) (by omega), Z 32 (by omega) (by omega), Z 33 (by omega) (by omega),
        Z 34 (by omega) (by omega)]
    have hch := lr_chainNS hz Hr n 0 (by omega)
    have hrun := packRunF_of_chain _ _ _ _ _ _ _ hch
    have hcopy : ∀ k < 5, σ (.n (18 + k)) = σ (.n k) := fun k hk ↦
      hns (.copy (.n (18 + k)) (.n k)) (hbody ▸ mem_lrBody_head (by
        simp only [lrHead, List.mem_append, List.mem_map, List.mem_range]
        exact Or.inr ⟨k, hk, rfl⟩)) (by rw [hSr]; simp [lrStores, lrStore])
    have hcap0 : (lrCap 0).map σ = [f0, f1, f2, f3, f4] := by
      simp only [lrCap, ↓reduceIte, cap5, List.map_cons, List.map_nil]
      rw [hcopy 0 (by omega), hcopy 1 (by omega), hcopy 2 (by omega), hcopy 3 (by omega),
        hcopy 4 (by omega), hσp 0 (by omega), hσp 1 (by omega), hσp 2 (by omega), hσp 3 (by omega),
        hσp 4 (by omega)]
      rfl
    have hcl0 : σ (lrCl 0) = v := by rw [show lrCl 0 = .n 6 by simp [lrCl]]; exact hσp 6 (by omega)
    -- The coordinates and messages the rounds read are `rs` and `ms`.
    have pf : ∀ q < n, _ := fun q hq ↦ packRound_factsNS (lrB_lt q) (Hr q hq) hz
    have hrsσ : ((List.range' 0 n).map fun q ↦ σ (.n (lrB q))) = rs := by
      rw [← List.range_eq_range']
      refine readsAt_eq (p := pp) (rd := rd) ?_ hpp (by simp [hrs])
      rw [← hσ7]; exact readsAt_map_range fun q hq ↦ (pf q hq).1
    have hmsσ : ((List.range' 0 n).map fun q ↦ (σ (.n (lrB q + 1)), σ (.n (lrB q + 4)))) = ms := by
      rw [← List.range_eq_range']
      refine flatMap_pairs_inj _ _ (readsAt_eq (p := cur) (rd := rd) ?_ hcur (by
        rw [length_flatMap_pairs, length_flatMap_pairs, hms]; simp))
      rw [← hσ5]; exact readsAt_pairs n fun q hq ↦ ⟨(pf q hq).2.1, (pf q hq).2.2.1⟩
    rw [hrsσ, hmsσ, Nat.zero_add, hcl0, hcap0] at hrun
    have hchs : (packRunF rs ms v ⟨[f0, f1, f2, f3, f4], []⟩).1.2 =
        (List.range' 0 n).map fun q ↦ σ (.n (lrC q)) := by rw [hrun]
    have := hpt q (by rw [hchl]; exact hq)
    show LoadHolds rd (σ (.n 8)) q (σ (.n (lrC q)))
    rw [hσ8]
    simp only [hchs, List.getElem_map, List.getElem_range', Nat.zero_add, one_mul] at this
    exact this
  have hall : ∀ a, Stmt.atom a ∈ fn.body → a.Holds rd σ := fun a ha => by
    by_cases haS : a ∈ S
    · exact hst a haS
    · exact hns a ha haS
  refine ⟨fun a ha haS hn => hside a ha haS hn, fun _ => hst, fun a ha => ?_, fun vs hvs => ?_, ?_, ?_,
    fun A hA => ?_⟩
  · have := hok' a ha
    cases a with
    | hint hh => simp [loadOkB] at this
    | _ => trivial
  · -- the returns, by the guest stream's meaning
    rw [hbody, hret, Option.some.injEq] at hvs
    subst hvs
    have hrel : coreProgram.Rel rd name args ((lrRets n).map σ) := by
      rw [rel_iff_sem hfind, hbody, lrBody]
      refine ⟨σ, by rw [hparams, hσ]; exact fwd_params hc', ?_⟩
      rw [holdsList_append, holdsList_atoms (lrPreBody_atoms n)]
      refine ⟨fun a ha => hall a (by rw [hbody, lrBody]; exact List.mem_append_left _ ha), ?_⟩
      simp only [Stmt.HoldsList, Stmt.Holds]
    obtain ⟨rs', ms', hrs', hms', hpp', hcur', -, -, hrets⟩ := lr_sound hfind hparams hn hbody hrel
    obtain rfl : rs' = rs := readsAt_eq hpp' hpp (by rw [hrs', hrs])
    obtain rfl : ms' = ms := flatMap_pairs_inj _ _ (readsAt_eq hcur' hcur (by
      rw [length_flatMap_pairs, length_flatMap_pairs, hms', hms]))
    rw [hrets]; rfl
  · rw [hbody]; exact allocs_atoms _ hna
  · rw [hbody, allocDsts_atoms hna]; rfl
  · obtain ⟨d, q, off, hm, rfl⟩ := mem_loadAddrs hA
    have hm' : Stmt.atom (.load d q off) ∈ fn.body := mem_of_mem_atomsOf hm
    rcases hload d q off hm' with ⟨rfl, ho⟩ | ⟨rfl, ho⟩ | ⟨rfl, ho⟩
    · obtain ⟨m, he, hRm⟩ := hR.1 off ho; exact ⟨m, by rw [hσ7, he], Or.inr hRm⟩
    · obtain ⟨m, he, hRm⟩ := hR.2.1 off ho; exact ⟨m, by rw [hσ5, he], Or.inr hRm⟩
    · obtain ⟨m, he, hRm⟩ := hR.2.2 off ho; exact ⟨m, by rw [hσ8, he], Or.inr hRm⟩

end
end LeanVM.Guest.B1.VsC
