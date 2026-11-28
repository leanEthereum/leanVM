/-
  LeanVM.Guest.B1.VsC.PlainA

  `keccak_plain_rounds`' two specializations complete placed, storing their challenges into their
  caller's `point`.
-/

module

public import LeanVM.Guest.B1.VsC.KRoundsA
public import LeanVM.Guest.B1.KeccakGkr.Plain

/-!
# `keccak_plain_rounds`, placed

`keccak_plain_rounds__L6_L0` and `__L4_L1` (the guest stream's templates `plain60T`, `plain41T`)
have no words of their own and no grind: they read the `2n` stream words at the cursor and store
round `i`'s challenge at `point[i]`, in their caller's array. On every memory holding the stream
words and the honest challenges (`plainRun`'s) at `point`, the forward evaluation (`callAtA_fwd`)
holds every atom: the rounds other than their stores give the run (`PlainRoundNS`, the squeezes
`plain_round_sq0NS`, `plain_round_sq1NS`), so the stored words are `plainRun`'s; the returns are then
the guest stream's meaning (`plain60_sound`, `plain41_sound`).
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Guest.Value LeanVM.Guest
open LeanVM.Guest.B1.VerifySub
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## A round without its store -/

section NS

variable {rd : Reader} {σ : Val}

/-- What a plain round's statements but its store ask of a valuation. -/
structure PlainRoundNS (rd : Reader) (σ : Val) (cur vIn : V) (ins : List V) (i a o : ℕ) : Prop where
  ld0 : LoadHolds rd (σ cur) (2 * i) (σ (.n a))
  pk0 : FsPackOk σ (.n a) (a + 1) dsObserve
  ld2 : LoadHolds rd (σ cur) (2 * i + 1) (σ (.n (a + 3)))
  pk2 : FsPackOk σ (.n (a + 3)) (a + 3 + 1) dsObserve
  kc : (Atom.keccak ins ((List.range 13).map fun k ↦ .n (o + k)) false false).Holds rd σ
  v : σ (.n (o + 17)) =
    σ (.n a) + σ (.n o) * ((σ vIn + σ (.n (a + 3))) + σ (.n o) * σ (.n (a + 3)))

/-- **A round's facts from its atoms but the loads through `pt`.** -/
theorem plainNS_of {cur pt vIn : V} {ins : List V} {mid : List Stmt} {i a o : ℕ} (hcp : cur ≠ pt)
    (H : ∀ x, Stmt.atom x ∈ plainRoundT cur pt vIn ins mid i a o → (∀ d off, x ≠ .load d pt off) →
      x.Holds rd σ) : PlainRoundNS rd σ cur vIn ins i a o := by
  have nl : ∀ {x : Atom}, (∀ d p off, x ≠ .load d p off) → ∀ d off, x ≠ .load d pt off :=
    fun h d off => h d pt off
  have ld : ∀ d off, Stmt.atom (.load d cur off) ∈ plainRoundT cur pt vIn ins mid i a o →
      (Atom.load d cur off).Holds rd σ := fun d off hm =>
    H _ hm fun d' off' he => hcp (by simp only [Atom.load.injEq] at he; exact he.2.1)
  have l0 := ld (.n a) (2 * i) (by simp [plainRoundT, fsNextT])
  have l2 := ld (.n (a + 3)) (2 * i + 1) (by simp [plainRoundT, fsNextT])
  have c1 : σ (.n (a + 1)) = σ (.n a) := H (.copy (.n (a + 1)) (.n a)) (by simp [plainRoundT, fsNextT, fsPackT])
    (nl (by simp))
  have c2 : σ (.n (a + 2)) = word 0 dsObserve := H (.const (.n (a + 1 + 1)) (word 0 dsObserve))
    (by simp [plainRoundT, fsNextT, fsPackT]) (nl (by simp))
  have c4 : σ (.n (a + 3 + 1)) = σ (.n (a + 3)) := H (.copy (.n (a + 3 + 1)) (.n (a + 3)))
    (by simp [plainRoundT, fsNextT, fsPackT]) (nl (by simp))
  have c5 : σ (.n (a + 3 + 1 + 1)) = word 0 dsObserve := H (.const (.n (a + 3 + 1 + 1)) (word 0 dsObserve))
    (by simp [plainRoundT, fsNextT, fsPackT]) (nl (by simp))
  have kc := H (.keccak ins ((List.range 13).map fun k ↦ .n (o + k)) false false)
    (by simp [plainRoundT, keccakA]) (nl (by simp))
  have e20 : σ (.n (o + 13)) = σ vIn + σ (.n (a + 3)) :=
    H (.add (.n (o + 13)) vIn (.n (a + 3))) (by simp [plainRoundT]) (nl (by simp))
  have e21 : σ (.n (o + 14)) = σ (.n o) * σ (.n (a + 3)) :=
    H (.mul (.n (o + 14)) (.n o) (.n (a + 3))) (by simp [plainRoundT]) (nl (by simp))
  have e22 : σ (.n (o + 15)) = σ (.n (o + 13)) + σ (.n (o + 14)) :=
    H (.add (.n (o + 15)) (.n (o + 13)) (.n (o + 14))) (by simp [plainRoundT]) (nl (by simp))
  have e23 : σ (.n (o + 16)) = σ (.n o) * σ (.n (o + 15)) :=
    H (.mul (.n (o + 16)) (.n o) (.n (o + 15))) (by simp [plainRoundT]) (nl (by simp))
  have e24 : σ (.n (o + 17)) = σ (.n a) + σ (.n (o + 16)) :=
    H (.add (.n (o + 17)) (.n a) (.n (o + 16))) (by simp [plainRoundT]) (nl (by simp))
  exact ⟨l0, ⟨c1, c2⟩, l2, ⟨c4, c5⟩, kc, by rw [e24, e23, e22, e21, e20]⟩

/-- `plain_round_sq0` from the facts but the store. -/
theorem plain_round_sq0NS {cur vIn : V} {zs capV : List V} {i a o : ℕ} {cap : List E}
    (h : PlainRoundNS rd σ cur vIn ([.n (a + 1), .n (a + 2), .n (a + 4), .n (a + 5)] ++ zs ++ capV) i a o)
    (hz : zs.map σ = [0, 0, 0, 0]) (hc : capV.map σ = cap) :
    σ (.n o) = (plainSq ⟨cap, []⟩ (σ (.n a)) (σ (.n (a + 3)))).1 ∧
      [σ (.n (o + 8)), σ (.n (o + 9)), σ (.n (o + 10)), σ (.n (o + 11)), σ (.n (o + 12))] =
        (plainSq ⟨cap, []⟩ (σ (.n a)) (σ (.n (a + 3)))).2.cap := by
  have s0 := fsNext_scalar h.pk0
  have s2 := fsNext_scalar h.pk2
  have habs : ((⟨cap, []⟩ : Fs).absorb (σ (.n a)) dsObserve).absorb (σ (.n (a + 3))) dsObserve =
      ⟨cap, [(σ (.n a), dsObserve), (σ (.n (a + 3)), dsObserve)]⟩ := rfl
  have hin : ([V.n (a + 1), .n (a + 2), .n (a + 4), .n (a + 5)] ++ zs ++ capV).map σ =
      rateOf [(σ (.n a), dsObserve), (σ (.n (a + 3)), dsObserve)] ++ cap := by
    rw [rateOf_two, ← s0, ← s2, List.map_append, List.map_append, hz, hc]
    rfl
  have := squeeze_atom (s := ⟨cap, [(σ (.n a), dsObserve), (σ (.n (a + 3)), dsObserve)]⟩) h.kc hin
    (b := o) rfl
  simp only [range13_map, List.drop, List.map_cons, List.map_nil] at this
  rw [plainSq, habs]
  exact ⟨this.1, this.2⟩

/-- `plain_round_sq1` from the facts but the store. -/
theorem plain_round_sq1NS {cur vIn p0 p1 : V} {zs capV : List V} {i a o : ℕ} {cap : List E} {w : E}
    (h : PlainRoundNS rd σ cur vIn ([p0, p1, .n (a + 1), .n (a + 2), .n (a + 4), .n (a + 5)] ++ zs ++ capV) i a o)
    (hp : (σ p0, σ p1) = Keccak.scalarCells w dsObserve)
    (hz : zs.map σ = [0, 0]) (hc : capV.map σ = cap) :
    σ (.n o) = (plainSq ⟨cap, [(w, dsObserve)]⟩ (σ (.n a)) (σ (.n (a + 3)))).1 ∧
      [σ (.n (o + 8)), σ (.n (o + 9)), σ (.n (o + 10)), σ (.n (o + 11)), σ (.n (o + 12))] =
        (plainSq ⟨cap, [(w, dsObserve)]⟩ (σ (.n a)) (σ (.n (a + 3)))).2.cap := by
  have s0 := fsNext_scalar h.pk0
  have s2 := fsNext_scalar h.pk2
  have habs : ((⟨cap, [(w, dsObserve)]⟩ : Fs).absorb (σ (.n a)) dsObserve).absorb
      (σ (.n (a + 3))) dsObserve =
      ⟨cap, [(w, dsObserve), (σ (.n a), dsObserve), (σ (.n (a + 3)), dsObserve)]⟩ := rfl
  have hin : ([p0, p1, .n (a + 1), .n (a + 2), .n (a + 4), .n (a + 5)] ++ zs ++ capV).map σ =
      rateOf [(w, dsObserve), (σ (.n a), dsObserve), (σ (.n (a + 3)), dsObserve)] ++ cap := by
    rw [rateOf_three, ← hp, ← s0, ← s2, List.map_append, List.map_append, hz, hc]
    rfl
  have := squeeze_atom (s := ⟨cap, [(w, dsObserve), (σ (.n a), dsObserve),
    (σ (.n (a + 3)), dsObserve)]⟩) h.kc hin (b := o) rfl
  simp only [range13_map, List.drop, List.map_cons, List.map_nil] at this
  rw [plainSq, habs]
  exact ⟨this.1, this.2⟩

end NS

/-! ## The generic placement -/

variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}

/-- `keccak_plain_rounds`' returns on the honest run. -/
noncomputable def plainRetsW (k0 n : ℕ) (rounds : List (E × E)) (value cur w : E) (f : List E) : List E :=
  (plainRun rounds value (plainStart k0 f w)).2.2.cap ++
    [cur * gen ^ (2 * n), (plainRun rounds value (plainStart k0 f w)).2.1]

/-- What `keccak_plain_rounds` needs of the memory: the stream words and the honest challenges. -/
def PlainPre (k0 : ℕ) (cur pt value w : E) (f : List E) (rounds : List (E × E)) (rd : Reader) : Prop :=
  ReadsAt rd cur (rounds.flatMap fun c ↦ [c.1, c.2]) ∧
    ReadsAt rd pt (plainRun rounds value (plainStart k0 f w)).1

/-- The words `keccak_plain_rounds` reads and writes lie in the region `R`. -/
def PlainRegion (cur pt : E) (n : ℕ) (R : ℕ → Prop) : Prop :=
  (∀ t < 2 * n, ∃ m, cur.limb 0 * addressOfIndex t = addressOfIndex m ∧ R m) ∧
    ∀ t < n, ∃ m, pt.limb 0 * addressOfIndex t = addressOfIndex m ∧ R m

theorem plainRun_len : ∀ (rounds : List (E × E)) (v : E) (s : Fs),
    (plainRun rounds v s).1.length = rounds.length
  | [], _, _ => rfl
  | (_, _) :: rest, v, s => by simp only [plainRun, List.length_cons, plainRun_len rest]

/-- What the kernel checks of a plain template on its `n` rounds, its stores `S`. -/
def plainOkA (n : ℕ) (S : List Atom) (B : List Stmt) : Bool :=
  leafChecks 11 B && (atomsOf B).all (loadOkB [(7, 2 * n), (9, n)]) &&
    (atomsOf B).all (fun a => !atomAllocB a) && storesOf 11 B == S &&
    S.all (fun a => match a with | .load _ p _ => p == .n 9 | _ => false) &&
    (match retOf B with | some (_ :: _) => true | _ => false)

set_option maxHeartbeats 1000000 in
/-- **A plain template completes placed**, given that on every memory holding the stream words and
the honest challenges, its atoms but the stores give the stores. -/
theorem plain_core {k : ℕ} {name : String} {fn : Fn} {n k0 : ℕ} {S : List Atom}
    (hfind : coreProgram.find? name = some fn) (hparams : fn.params = (List.range 11).map V.n)
    (hok : plainOkA n S fn.body = true)
    (hsound : ∀ rd args rets, coreProgram.Rel rd name args rets → MeaningPlainRounds n k0 rd args rets)
    {f0 f1 f2 f3 f4 p0 p1 cur value pt tabs w : E} {rounds : List (E × E)} (hw : k0 = 1 → (p0, p1) = Keccak.scalarCells w dsObserve)
    (hrl : rounds.length = n) {R : ℕ → Prop} (hR : PlainRegion cur pt n R)
    (hst : ∀ rd, PlainPre k0 cur pt value w [f0, f1, f2, f3, f4] rounds rd →
      ∀ σ : Val, (∀ i < 11, σ (.n i) = [f0, f1, f2, f3, f4, p0, p1, cur, value, pt, tabs].getD i 0) →
      (∀ a, Stmt.atom a ∈ fn.body → a ∉ S → a.Holds rd σ) → ∀ a ∈ S, a.Holds rd σ)
    (fp c0 : ℕ) :
    CallAtA fs al cert k name [f0, f1, f2, f3, f4, p0, p1, cur, value, pt, tabs]
      (plainRetsW k0 n rounds value cur w [f0, f1, f2, f3, f4]) R (fun _ => False) (fun _ => True)
      (PlainPre k0 cur pt value w [f0, f1, f2, f3, f4] rounds) PostQuiet (fs name) fp c0 c0 := by
  simp only [plainOkA, Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨⟨⟨⟨hck, hld⟩, hna⟩, hSeq⟩, hSp⟩, hrn⟩ := hok
  obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp (by
    simp only [leafChecks, Bool.and_eq_true] at hck; exact hck.1.1)
  obtain ⟨vs0, hr0⟩ := Option.isSome_iff_exists.mp (by
    simp only [leafChecks, Bool.and_eq_true] at hck; exact hck.1.2)
  have hlp : coreProgram.loop name = false := by
    obtain ⟨ss, hb, -⟩ := retOf_spec hr0
    refine loop_false_of_ret (hfind := hfind) hb ?_
    rintro rfl
    simp [hr0] at hrn
  set args : List E := [f0, f1, f2, f3, f4, p0, p1, cur, value, pt, tabs] with hargs
  have e := callAtA_fwd (fs := fs) (al := al) (cert := cert) (k := k) (R := R) (D := fun _ => False)
    (Out := fun _ => True) (fp := fp) (c := c0) (args := args)
    (rets := plainRetsW k0 n rounds value cur w [f0, f1, f2, f3, f4])
    (fun _ => 0) [] [] hfind hlp (by rw [hparams]; rfl) hck
    ⟨by simp, List.Pairwise.nil⟩ (fun _ _ => trivial) (fun _ h => h.elim)
    (Pre := PlainPre k0 cur pt value w [f0, f1, f2, f3, f4] rounds)
    fun rd _ _ hP σ hσ => ?_
  · simpa using e
  obtain ⟨hcur, hpt⟩ := hP
  have hc'' : chk args.length fn.body = some c' := hc'
  set S' := storesOf args.length fn.body with hS
  have hSr : S' = S := hSeq
  have hG : ∀ a, Stmt.atom a ∈ fn.body → Good rd S' (fun _ => 0) σ a := fun a ha => hσ ▸ fwd_good hc'' a ha
  have hσp : ∀ i < 11, σ (.n i) = args.getD i 0 := fun i hi => by
    rw [hσ]; exact fwd_param hc'' (by simpa [hargs] using hi)
  have hσ7 : σ (.n 7) = cur := hσp 7 (by omega)
  have hσ9 : σ (.n 9) = pt := hσp 9 (by omega)
  have hok' : ∀ a, Stmt.atom a ∈ fn.body → loadOkB [(7, 2 * n), (9, n)] a = true :=
    fun a ha => List.all_eq_true.mp hld a (mem_atomsOf' ha)
  have hload : ∀ d q off, Stmt.atom (.load d q off) ∈ fn.body →
      (q = .n 7 ∧ off < 2 * n) ∨ (q = .n 9 ∧ off < n) := fun d q off ha => by
    have h := hok' _ ha
    simpa only [loadOkB, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true, Bool.and_eq_true,
      beq_iff_eq, decide_eq_true_eq] using h
  have hchl : (plainRun rounds value (plainStart k0 [f0, f1, f2, f3, f4] w)).1.length = n := by
    rw [plainRun_len, hrl]
  have hcurl : (rounds.flatMap fun c ↦ [c.1, c.2]).length = 2 * n := by rw [length_flatMap_pairs, hrl]
  have hside : ∀ a, Stmt.atom a ∈ fn.body → a ∉ S' → needsSide a = true → Side rd S' σ a := fun a ha haS hn => by
    cases a with
    | load d q off =>
      simp only [Side, haS, ↓reduceIte]
      rcases hload d q off ha with ⟨rfl, ho⟩ | ⟨rfl, ho⟩
      · rw [hσ7]; exact ⟨(hcur off (by omega)).1, by rw [(hcur off (by omega)).2]; rfl⟩
      · rw [hσ9]; exact ⟨(hpt off (by omega)).1, by rw [(hpt off (by omega)).2]; rfl⟩
    | hint => have := hok' _ ha; simp [loadOkB] at this
    | _ =>
      have := hok' _ ha
      simp only [loadOkB, hn, Bool.not_true, Bool.false_eq_true] at this
  have hns : ∀ a, Stmt.atom a ∈ fn.body → a ∉ S' → a.Holds rd σ := fun a ha haS => by
    have := atoms_holds (S := S') (w := fun _ => 0) (rd := rd) (σ := σ) (atoms := [a])
      (fun b hb => by rw [List.mem_singleton] at hb; subst hb; exact hG b ha)
      (fun b hb hn => by rw [List.mem_singleton] at hb; subst hb; exact Or.inr (hside b ha haS hn))
    exact this a List.mem_cons_self
  have hst' : ∀ a ∈ S', a.Holds rd σ := by
    rw [hSr]; exact hst rd ⟨hcur, hpt⟩ σ hσp (fun a ha haS => hns a ha (by rw [hSr]; exact haS))
  have hall : ∀ a, Stmt.atom a ∈ fn.body → a.Holds rd σ := fun a ha => by
    by_cases haS : a ∈ S'
    · exact hst' a haS
    · exact hns a ha haS
  refine ⟨fun a ha haS hn => hside a ha haS hn, fun _ => hst', fun a ha => ?_, fun vs hvs => ?_, ?_, ?_,
    fun A hA => ?_⟩
  · have := hok' a ha
    cases a with
    | hint hh => simp [loadOkB] at this
    | _ => trivial
  · -- the returns, by the guest stream's meaning
    obtain ⟨ss, hb, hss⟩ := retOf_spec hvs
    have hrel : coreProgram.Rel rd name args (vs.map σ) := by
      rw [rel_iff_sem hfind]
      refine ⟨σ, by rw [hparams, hσ]; exact fwd_params hc'', ?_⟩
      rw [hb, holdsList_append, holdsList_atoms hss]
      refine ⟨fun a ha => hall a (by rw [hb]; exact List.mem_append_left _ ha), ?_⟩
      simp only [Stmt.HoldsList, Stmt.Holds]
    have hm := hsound rd args _ hrel
    simp only [hargs, MeaningPlainRounds] at hm
    obtain ⟨rounds', hrl', hcur', hrun⟩ := hm
    obtain rfl : rounds' = rounds := flatMap_pairs_inj _ _ (readsAt_eq hcur' hcur (by
      rw [length_flatMap_pairs, length_flatMap_pairs, hrl', hrl]))
    rw [(hrun w hw).2]; rfl
  · exact allocs_atoms _ hna
  · rw [allocDsts_atoms hna]; rfl
  · obtain ⟨d, q, off, hm, rfl⟩ := mem_loadAddrs hA
    have hm' : Stmt.atom (.load d q off) ∈ fn.body := mem_of_mem_atomsOf hm
    rcases hload d q off hm' with ⟨rfl, ho⟩ | ⟨rfl, ho⟩
    · obtain ⟨m, he, hRm⟩ := hR.1 off ho; exact ⟨m, by rw [hσ7, he], Or.inr hRm⟩
    · obtain ⟨m, he, hRm⟩ := hR.2 off ho; exact ⟨m, by rw [hσ9, he], Or.inr hRm⟩

/-- `keccak_plain_rounds__L6_L0`'s stores: round `i`'s challenge at `point[i]`. -/
def p60S : List Atom := [.load (.n 27) (.n 9) 0, .load (.n 51) (.n 9) 1, .load (.n 75) (.n 9) 2, .load (.n 99) (.n 9) 3, .load (.n 123) (.n 9) 4, .load (.n 147) (.n 9) 5]

set_option maxRecDepth 100000 in
theorem p60_ok : plainOkA 6 p60S plain60T = true := by decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `keccak_plain_rounds__L6_L0`'s stores hold, from its other atoms. -/
theorem p60_hst {rd : Reader} {f0 f1 f2 f3 f4 p0 p1 cur value pt tabs w : E} {rounds : List (E × E)}
    (hrl : rounds.length = 6)
    (hP : PlainPre 0 cur pt value w [f0, f1, f2, f3, f4] rounds rd) (σ : Val)
    (hσp : ∀ i < 11, σ (.n i) = [f0, f1, f2, f3, f4, p0, p1, cur, value, pt, tabs].getD i 0)
    (hns : ∀ a, Stmt.atom a ∈ plain60T → a ∉ p60S → a.Holds rd σ) : ∀ a ∈ p60S, a.Holds rd σ := by
  obtain ⟨hcur, hpt⟩ := hP
  have notS : ∀ x : Atom, (∀ d off, x ≠ .load d (.n 9) off) → x ∉ p60S := fun x h hx => by
    simp only [p60S, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> exact h _ _ rfl
  have hcp : (V.n 7) ≠ V.n 9 := by decide
  have H : ∀ {B : List Stmt}, (∀ x, Stmt.atom x ∈ B → Stmt.atom x ∈ plain60T) →
      ∀ x, Stmt.atom x ∈ B → (∀ d off, x ≠ .load d (.n 9) off) → x.Holds rd σ :=
    fun hm x hx hn => hns x (hm x hx) (notS x hn)
  have m0 : ∀ x, Stmt.atom x ∈ plainRoundT (.n 7) (.n 9) (.n 8) (plainIns0 16 [.n 23, .n 24, .n 25, .n 26] 11) plainMid60 0 16 27 → Stmt.atom x ∈ plain60T := fun x h => by
    unfold plain60T; exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))))))
  have r0 := plainNS_of hcp (H m0)
  have v0 := r0.v
  have m1 : ∀ x, Stmt.atom x ∈ plainRoundT (.n 7) (.n 9) (.n 44) (plainIns0 45 [.n 23, .n 24, .n 25, .n 26] 35) [] 1 45 51 → Stmt.atom x ∈ plain60T := fun x h => by
    unfold plain60T; exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h)))))
  have r1 := plainNS_of hcp (H m1)
  have v1 := r1.v
  have m2 : ∀ x, Stmt.atom x ∈ plainRoundT (.n 7) (.n 9) (.n 68) (plainIns0 69 [.n 23, .n 24, .n 25, .n 26] 59) [] 2 69 75 → Stmt.atom x ∈ plain60T := fun x h => by
    unfold plain60T; exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))))
  have r2 := plainNS_of hcp (H m2)
  have v2 := r2.v
  have m3 : ∀ x, Stmt.atom x ∈ plainRoundT (.n 7) (.n 9) (.n 92) (plainIns0 93 [.n 23, .n 24, .n 25, .n 26] 83) [] 3 93 99 → Stmt.atom x ∈ plain60T := fun x h => by
    unfold plain60T; exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h)))
  have r3 := plainNS_of hcp (H m3)
  have v3 := r3.v
  have m4 : ∀ x, Stmt.atom x ∈ plainRoundT (.n 7) (.n 9) (.n 116) (plainIns0 117 [.n 23, .n 24, .n 25, .n 26] 107) [] 4 117 123 → Stmt.atom x ∈ plain60T := fun x h => by
    unfold plain60T; exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))
  have r4 := plainNS_of hcp (H m4)
  have v4 := r4.v
  have m5 : ∀ x, Stmt.atom x ∈ plainRoundT (.n 7) (.n 9) (.n 140) (plainIns0 141 [.n 23, .n 24, .n 25, .n 26] 131) [] 5 141 147 → Stmt.atom x ∈ plain60T := fun x h => by
    unfold plain60T; exact List.mem_append_left _ (List.mem_append_right _ h)
  have r5 := plainNS_of hcp (H m5)
  have v5 := r5.v
  have hd0 : σ (.n 11) = σ (.n 0) :=
    hns (.copy (.n 11) (.n 0)) (by unfold plain60T; exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_self)))))))) (notS _ (by simp))
  have hd1 : σ (.n 12) = σ (.n 1) :=
    hns (.copy (.n 12) (.n 1)) (by unfold plain60T; exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))) (notS _ (by simp))
  have hd2 : σ (.n 13) = σ (.n 2) :=
    hns (.copy (.n 13) (.n 2)) (by unfold plain60T; exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))) (notS _ (by simp))
  have hd3 : σ (.n 14) = σ (.n 3) :=
    hns (.copy (.n 14) (.n 3)) (by unfold plain60T; exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))) (notS _ (by simp))
  have hd4 : σ (.n 15) = σ (.n 4) :=
    hns (.copy (.n 15) (.n 4)) (by unfold plain60T; exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))) (notS _ (by simp))
  have z23 : σ (.n 23) = 0 := by
    have h := hns (.const (.n 23) (word 0 0)) (m0 _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))) (notS _ (by simp))
    simpa [Atom.Holds, word_zero] using h
  have z24 : σ (.n 24) = 0 := by
    have h := hns (.const (.n 24) (word 0 0)) (m0 _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))) (notS _ (by simp))
    simpa [Atom.Holds, word_zero] using h
  have z25 : σ (.n 25) = 0 := by
    have h := hns (.const (.n 25) (word 0 0)) (m0 _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))) (notS _ (by simp))
    simpa [Atom.Holds, word_zero] using h
  have z26 : σ (.n 26) = 0 := by
    have h := hns (.const (.n 26) (word 0 0)) (m0 _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))) (notS _ (by simp))
    simpa [Atom.Holds, word_zero] using h
  simp only [Nat.reduceAdd] at v0
  simp only [Nat.reduceAdd] at v1
  simp only [Nat.reduceAdd] at v2
  simp only [Nat.reduceAdd] at v3
  simp only [Nat.reduceAdd] at v4
  simp only [Nat.reduceAdd] at v5
  have hz : [V.n 23, .n 24, .n 25, .n 26].map σ = [0, 0, 0, 0] := by simp [z23, z24, z25, z26]
  have hσ : ∀ i < 11, σ (.n i) = [f0, f1, f2, f3, f4, p0, p1, cur, value, pt, tabs].getD i 0 := hσp
  have hc0 : (capV 11).map σ = [f0, f1, f2, f3, f4] := by
    simp only [capV, List.map_cons, List.map_nil, Nat.reduceAdd]
    rw [hd0, hd1, hd2, hd3, hd4, hσ 0 (by omega), hσ 1 (by omega), hσ 2 (by omega), hσ 3 (by omega),
      hσ 4 (by omega)]
    rfl
  have q0 := plain_round_sq0NS (cap := [f0, f1, f2, f3, f4]) r0 hz hc0
  have q1 := plain_round_sq0NS (cap := [σ (.n 35), σ (.n 36), σ (.n 37), σ (.n 38), σ (.n 39)]) r1 hz
    (by simp only [capV, List.map_cons, List.map_nil, Nat.reduceAdd])
  have q2 := plain_round_sq0NS (cap := [σ (.n 59), σ (.n 60), σ (.n 61), σ (.n 62), σ (.n 63)]) r2 hz
    (by simp only [capV, List.map_cons, List.map_nil, Nat.reduceAdd])
  have q3 := plain_round_sq0NS (cap := [σ (.n 83), σ (.n 84), σ (.n 85), σ (.n 86), σ (.n 87)]) r3 hz
    (by simp only [capV, List.map_cons, List.map_nil, Nat.reduceAdd])
  have q4 := plain_round_sq0NS (cap := [σ (.n 107), σ (.n 108), σ (.n 109), σ (.n 110), σ (.n 111)]) r4 hz
    (by simp only [capV, List.map_cons, List.map_nil, Nat.reduceAdd])
  have q5 := plain_round_sq0NS (cap := [σ (.n 131), σ (.n 132), σ (.n 133), σ (.n 134), σ (.n 135)]) r5 hz
    (by simp only [capV, List.map_cons, List.map_nil, Nat.reduceAdd])
  simp only [Nat.reduceAdd] at q0 q1 q2 q3 q4 q5
  have hrun : plainRun [(σ (.n 16), σ (.n 19)), (σ (.n 45), σ (.n 48)), (σ (.n 69), σ (.n 72)), (σ (.n 93), σ (.n 96)),
      (σ (.n 117), σ (.n 120)), (σ (.n 141), σ (.n 144))] (σ (.n 8)) ⟨[f0, f1, f2, f3, f4], []⟩ =
      ([σ (.n 27), σ (.n 51), σ (.n 75), σ (.n 99), σ (.n 123), σ (.n 147)], σ (.n 164),
        ⟨[σ (.n 155), σ (.n 156), σ (.n 157), σ (.n 158), σ (.n 159)], []⟩) := by
    rw [plainRun_step q0.1.symm q0.2.symm v0.symm, plainRun_step q1.1.symm q1.2.symm v1.symm,
      plainRun_step q2.1.symm q2.2.symm v2.symm, plainRun_step q3.1.symm q3.2.symm v3.symm,
      plainRun_step q4.1.symm q4.2.symm v4.symm, plainRun_step q5.1.symm q5.2.symm v5.symm]
    rfl
  have h7 : σ (.n 7) = cur := hσ 7 (by omega)
  have h8 : σ (.n 8) = value := hσ 8 (by omega)
  have h9 : σ (.n 9) = pt := hσ 9 (by omega)
  have hr : [(σ (.n 16), σ (.n 19)), (σ (.n 45), σ (.n 48)), (σ (.n 69), σ (.n 72)), (σ (.n 93), σ (.n 96)),
      (σ (.n 117), σ (.n 120)), (σ (.n 141), σ (.n 144))] = rounds := by
    refine flatMap_pairs_inj _ _ (readsAt_eq ?_ hcur (by rw [length_flatMap_pairs, length_flatMap_pairs, hrl]; rfl))
    intro k hk
    simp only [List.flatMap_cons, List.flatMap_nil, List.cons_append, List.nil_append, List.append_nil,
      List.length_cons, List.length_nil] at hk
    rw [← h7]
    interval_cases k
    · exact r0.ld0
    · exact r0.ld2
    · exact r1.ld0
    · exact r1.ld2
    · exact r2.ld0
    · exact r2.ld2
    · exact r3.ld0
    · exact r3.ld2
    · exact r4.ld0
    · exact r4.ld2
    · exact r5.ld0
    · exact r5.ld2
  have hch : (plainRun rounds value (plainStart 0 [f0, f1, f2, f3, f4] w)).1 =
      [σ (.n 27), σ (.n 51), σ (.n 75), σ (.n 99), σ (.n 123), σ (.n 147)] := by
    rw [← hr, ← h8, show plainStart 0 [f0, f1, f2, f3, f4] w = ⟨[f0, f1, f2, f3, f4], []⟩ from rfl, hrun]
  rw [hch] at hpt
  intro a ha
  simp only [p60S, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> (show LoadHolds rd (σ (.n 9)) _ _; rw [h9])
  · exact hpt 0 (by simp)
  · exact hpt 1 (by simp)
  · exact hpt 2 (by simp)
  · exact hpt 3 (by simp)
  · exact hpt 4 (by simp)
  · exact hpt 5 (by simp)

/-- `keccak_plain_rounds__L4_L1`'s stores: round `i`'s challenge at `point[i]`. -/
def p41S : List Atom := [.load (.n 26) (.n 9) 0, .load (.n 55) (.n 9) 1, .load (.n 79) (.n 9) 2, .load (.n 103) (.n 9) 3]

set_option maxRecDepth 100000 in
theorem p41_ok : plainOkA 4 p41S plain41T = true := by decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `keccak_plain_rounds__L4_L1`'s stores hold, from its other atoms. -/
theorem p41_hst {rd : Reader} {f0 f1 f2 f3 f4 p0 p1 cur value pt tabs w : E} {rounds : List (E × E)}
    (hrl : rounds.length = 4) (hw : 1 = 1 → (p0, p1) = Keccak.scalarCells w dsObserve)
    (hP : PlainPre 1 cur pt value w [f0, f1, f2, f3, f4] rounds rd) (σ : Val)
    (hσp : ∀ i < 11, σ (.n i) = [f0, f1, f2, f3, f4, p0, p1, cur, value, pt, tabs].getD i 0)
    (hns : ∀ a, Stmt.atom a ∈ plain41T → a ∉ p41S → a.Holds rd σ) : ∀ a ∈ p41S, a.Holds rd σ := by
  obtain ⟨hcur, hpt⟩ := hP
  have notS : ∀ x : Atom, (∀ d off, x ≠ .load d (.n 9) off) → x ∉ p41S := fun x h hx => by
    simp only [p41S, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> exact h _ _ rfl
  have hcp : (V.n 7) ≠ V.n 9 := by decide
  have H : ∀ {B : List Stmt}, (∀ x, Stmt.atom x ∈ B → Stmt.atom x ∈ plain41T) →
      ∀ x, Stmt.atom x ∈ B → (∀ d off, x ≠ .load d (.n 9) off) → x.Holds rd σ :=
    fun hm x hx hn => hns x (hm x hx) (notS x hn)
  have m0 : ∀ x, Stmt.atom x ∈ plainRoundT (.n 7) (.n 9) (.n 8) ([.n 16, .n 17, .n 19, .n 20, .n 22, .n 23] ++ [.n 24, .n 25] ++ capV 11) plainMid41a 0 18 26 → Stmt.atom x ∈ plain41T := fun x h => by
    unfold plain41T; exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))))
  have r0 := plainNS_of hcp (H m0)
  have v0 := r0.v
  have m1 : ∀ x, Stmt.atom x ∈ plainRoundT (.n 7) (.n 9) (.n 43) (plainIns0 44 [.n 51, .n 52, .n 53, .n 54] 34) plainMid41b 1 44 55 → Stmt.atom x ∈ plain41T := fun x h => by
    unfold plain41T; exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h)))
  have r1 := plainNS_of hcp (H m1)
  have v1 := r1.v
  have m2 : ∀ x, Stmt.atom x ∈ plainRoundT (.n 7) (.n 9) (.n 72) (plainIns0 73 [.n 51, .n 52, .n 53, .n 54] 63) [] 2 73 79 → Stmt.atom x ∈ plain41T := fun x h => by
    unfold plain41T; exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))
  have r2 := plainNS_of hcp (H m2)
  have v2 := r2.v
  have m3 : ∀ x, Stmt.atom x ∈ plainRoundT (.n 7) (.n 9) (.n 96) (plainIns0 97 [.n 51, .n 52, .n 53, .n 54] 87) [] 3 97 103 → Stmt.atom x ∈ plain41T := fun x h => by
    unfold plain41T; exact List.mem_append_left _ (List.mem_append_right _ h)
  have r3 := plainNS_of hcp (H m3)
  have v3 := r3.v
  have hd0 : σ (.n 11) = σ (.n 0) :=
    hns (.copy (.n 11) (.n 0)) (by unfold plain41T; exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_self)))))) (notS _ (by simp))
  have hd1 : σ (.n 12) = σ (.n 1) :=
    hns (.copy (.n 12) (.n 1)) (by unfold plain41T; exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))) (notS _ (by simp))
  have hd2 : σ (.n 13) = σ (.n 2) :=
    hns (.copy (.n 13) (.n 2)) (by unfold plain41T; exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))) (notS _ (by simp))
  have hd3 : σ (.n 14) = σ (.n 3) :=
    hns (.copy (.n 14) (.n 3)) (by unfold plain41T; exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))) (notS _ (by simp))
  have hd4 : σ (.n 15) = σ (.n 4) :=
    hns (.copy (.n 15) (.n 4)) (by unfold plain41T; exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))) (notS _ (by simp))
  have hd5 : σ (.n 16) = σ (.n 5) :=
    hns (.copy (.n 16) (.n 5)) (by unfold plain41T; exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))) (notS _ (by simp))
  have hd6 : σ (.n 17) = σ (.n 6) :=
    hns (.copy (.n 17) (.n 6)) (by unfold plain41T; exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))) (notS _ (by simp))
  have z24 : σ (.n 24) = 0 := by
    have h := hns (.const (.n 24) (word 0 0)) (m0 _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_self))))) (notS _ (by simp))
    simpa [Atom.Holds, word_zero] using h
  have z25 : σ (.n 25) = 0 := by
    have h := hns (.const (.n 25) (word 0 0)) (m0 _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))) (notS _ (by simp))
    simpa [Atom.Holds, word_zero] using h
  have z51 : σ (.n 51) = 0 := by
    have h := hns (.const (.n 51) (word 0 0)) (m1 _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))) (notS _ (by simp))
    simpa [Atom.Holds, word_zero] using h
  have z52 : σ (.n 52) = 0 := by
    have h := hns (.const (.n 52) (word 0 0)) (m1 _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))) (notS _ (by simp))
    simpa [Atom.Holds, word_zero] using h
  have z53 : σ (.n 53) = 0 := by
    have h := hns (.const (.n 53) (word 0 0)) (m1 _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))) (notS _ (by simp))
    simpa [Atom.Holds, word_zero] using h
  have z54 : σ (.n 54) = 0 := by
    have h := hns (.const (.n 54) (word 0 0)) (m1 _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))) (notS _ (by simp))
    simpa [Atom.Holds, word_zero] using h
  simp only [Nat.reduceAdd] at v0
  simp only [Nat.reduceAdd] at v1
  simp only [Nat.reduceAdd] at v2
  simp only [Nat.reduceAdd] at v3
  have hz0 : [V.n 24, .n 25].map σ = [0, 0] := by simp [z24, z25]
  have hz : [V.n 51, .n 52, .n 53, .n 54].map σ = [0, 0, 0, 0] := by simp [z51, z52, z53, z54]
  have hσ : ∀ i < 11, σ (.n i) = [f0, f1, f2, f3, f4, p0, p1, cur, value, pt, tabs].getD i 0 := hσp
  have hc0 : (capV 11).map σ = [f0, f1, f2, f3, f4] := by
    simp only [capV, List.map_cons, List.map_nil, Nat.reduceAdd]
    rw [hd0, hd1, hd2, hd3, hd4, hσ 0 (by omega), hσ 1 (by omega), hσ 2 (by omega), hσ 3 (by omega),
      hσ 4 (by omega)]
    rfl
  have hp : (σ (.n 16), σ (.n 17)) = Keccak.scalarCells w dsObserve := by
    rw [hd5, hd6, hσ 5 (by omega), hσ 6 (by omega)]; exact hw rfl
  have q0 := plain_round_sq1NS (cap := [f0, f1, f2, f3, f4]) r0 hp hz0 hc0
  have q1 := plain_round_sq0NS (cap := [σ (.n 34), σ (.n 35), σ (.n 36), σ (.n 37), σ (.n 38)]) r1 hz
    (by simp only [capV, List.map_cons, List.map_nil, Nat.reduceAdd])
  have q2 := plain_round_sq0NS (cap := [σ (.n 63), σ (.n 64), σ (.n 65), σ (.n 66), σ (.n 67)]) r2 hz
    (by simp only [capV, List.map_cons, List.map_nil, Nat.reduceAdd])
  have q3 := plain_round_sq0NS (cap := [σ (.n 87), σ (.n 88), σ (.n 89), σ (.n 90), σ (.n 91)]) r3 hz
    (by simp only [capV, List.map_cons, List.map_nil, Nat.reduceAdd])
  simp only [Nat.reduceAdd] at q0 q1 q2 q3
  have hrun : plainRun [(σ (.n 18), σ (.n 21)), (σ (.n 44), σ (.n 47)), (σ (.n 73), σ (.n 76)), (σ (.n 97), σ (.n 100))]
      (σ (.n 8)) ⟨[f0, f1, f2, f3, f4], [(w, dsObserve)]⟩ =
      ([σ (.n 26), σ (.n 55), σ (.n 79), σ (.n 103)], σ (.n 120),
        ⟨[σ (.n 111), σ (.n 112), σ (.n 113), σ (.n 114), σ (.n 115)], []⟩) := by
    rw [plainRun_step q0.1.symm q0.2.symm v0.symm, plainRun_step q1.1.symm q1.2.symm v1.symm,
      plainRun_step q2.1.symm q2.2.symm v2.symm, plainRun_step q3.1.symm q3.2.symm v3.symm]
    rfl
  have h7 : σ (.n 7) = cur := hσ 7 (by omega)
  have h8 : σ (.n 8) = value := hσ 8 (by omega)
  have h9 : σ (.n 9) = pt := hσ 9 (by omega)
  have hr : [(σ (.n 18), σ (.n 21)), (σ (.n 44), σ (.n 47)), (σ (.n 73), σ (.n 76)), (σ (.n 97), σ (.n 100))] =
      rounds := by
    refine flatMap_pairs_inj _ _ (readsAt_eq ?_ hcur (by rw [length_flatMap_pairs, length_flatMap_pairs, hrl]; rfl))
    intro k hk
    simp only [List.flatMap_cons, List.flatMap_nil, List.cons_append, List.nil_append, List.append_nil,
      List.length_cons, List.length_nil] at hk
    rw [← h7]
    interval_cases k
    · exact r0.ld0
    · exact r0.ld2
    · exact r1.ld0
    · exact r1.ld2
    · exact r2.ld0
    · exact r2.ld2
    · exact r3.ld0
    · exact r3.ld2
  have hch : (plainRun rounds value (plainStart 1 [f0, f1, f2, f3, f4] w)).1 =
      [σ (.n 26), σ (.n 55), σ (.n 79), σ (.n 103)] := by
    rw [← hr, ← h8, show plainStart 1 [f0, f1, f2, f3, f4] w = ⟨[f0, f1, f2, f3, f4], [(w, dsObserve)]⟩ from rfl,
      hrun]
  rw [hch] at hpt
  intro a ha
  simp only [p41S, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl <;> (show LoadHolds rd (σ (.n 9)) _ _; rw [h9])
  · exact hpt 0 (by simp)
  · exact hpt 1 (by simp)
  · exact hpt 2 (by simp)
  · exact hpt 3 (by simp)

/-- **`keccak_plain_rounds__L6_L0` completes placed**: on the six rounds' words at the cursor and the
honest challenges at `point`, it returns `plainRun`'s capacity, the cursor past the `12` words and
the claim, with no words of its own. -/
theorem plain60_placed {k : ℕ} {f0 f1 f2 f3 f4 p0 p1 cur value pt tabs w : E} {rounds : List (E × E)}
    (hrl : rounds.length = 6) {R : ℕ → Prop} (hR : PlainRegion cur pt 6 R) (fp c0 : ℕ) :
    CallAtA fs al cert k "keccak_plain_rounds__L6_L0" [f0, f1, f2, f3, f4, p0, p1, cur, value, pt, tabs]
      (plainRetsW 0 6 rounds value cur w [f0, f1, f2, f3, f4]) R (fun _ => False) (fun _ => True)
      (PlainPre 0 cur pt value w [f0, f1, f2, f3, f4] rounds) PostQuiet (fs "keccak_plain_rounds__L6_L0") fp c0 c0 :=
  plain_core find_plain60 rfl (by rw [body60]; exact p60_ok) plain60_sound (fun h => absurd h (by decide)) hrl hR
    (fun rd hP σ hσp hns => p60_hst hrl hP σ hσp
      (fun a ha haS => hns a (by rw [body60]; exact ha) haS)) fp c0

/-- **`keccak_plain_rounds__L4_L1` completes placed**, its cells `p0`, `p1` the waiting scalar `w`'s. -/
theorem plain41_placed {k : ℕ} {f0 f1 f2 f3 f4 p0 p1 cur value pt tabs w : E} {rounds : List (E × E)}
    (hw : (p0, p1) = Keccak.scalarCells w dsObserve)
    (hrl : rounds.length = 4) {R : ℕ → Prop} (hR : PlainRegion cur pt 4 R) (fp c0 : ℕ) :
    CallAtA fs al cert k "keccak_plain_rounds__L4_L1" [f0, f1, f2, f3, f4, p0, p1, cur, value, pt, tabs]
      (plainRetsW 1 4 rounds value cur w [f0, f1, f2, f3, f4]) R (fun _ => False) (fun _ => True)
      (PlainPre 1 cur pt value w [f0, f1, f2, f3, f4] rounds) PostQuiet (fs "keccak_plain_rounds__L4_L1") fp c0 c0 :=
  plain_core find_plain41 rfl (by rw [body41]; exact p41_ok) plain41_sound (fun _ => hw) hrl hR
    (fun rd hP σ hσp hns => p41_hst hrl (fun _ => hw) hP σ hσp
      (fun a ha haS => hns a (by rw [body41]; exact ha) haS)) fp c0

end
end LeanVM.Guest.B1.VsC
