/-
  LeanVM.Guest.B1.VsC.SqueezePackedA

  `squeeze_packed` completes placed.
-/

module

public import LeanVM.Guest.B1.VsC.SqueezeLoopA
public import LeanVM.Guest.Complete.SegA
public import LeanVM.Guest.B1.VsC.CalleesB
import LeanVM.Guest.CoreRef

/-!
# `squeeze_packed`, placed

`squeeze_packed(fs0..fs4, out, g^p)`, `p < 64`, placed at frame `fp`, its cursor `c` right after:
the count split `p = 4 q + r` from six hinted bits, its records buffer of `5 (q + 2)` words at `c`
(its own words `spWords`: the capacity after `4 j` permutations, `j ≤ q`, then after all `p`), the
loop over the `q` records from `c` (`spL_callAtA`, entered when `q ≠ 0`), the last arm on the `r`
left (`splA`), the capacity after them read back. One valuation fixed before the memory (`spVals`):
every value is a function of the capacity, `out`, `p` and `c`, by `callAtA_node`.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Link LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Protocol.Verifier
open LeanVM.Guest.Value
open LeanVM.Prover.Exec (allocBase bitWord)

@[expose] public section

/-! ## The template -/

/-- `squeeze_packed`'s statements before its dispatch. -/
def spMPre : List Stmt :=
  [.atom (.hint (.bitsExp (.n 6) 6 (.stack [.n 7, .n 8, .n 9, .n 10, .n 11, .n 12]))),
    .atom (.mul (.n 7) (.n 7) (.n 7)),
    .atom (.const (.n 13) (word 1 0)),
    .atom (.const (.n 14) (word 3 0)),
    .atom (.mul (.n 15) (.n 7) (.n 14)),
    .atom (.add (.n 16) (.n 13) (.n 15)),
    .atom (.mul (.n 8) (.n 8) (.n 8)),
    .atom (.const (.n 17) (word 1 0)),
    .atom (.const (.n 18) (word 5 0)),
    .atom (.mul (.n 19) (.n 8) (.n 18)),
    .atom (.add (.n 20) (.n 17) (.n 19)),
    .atom (.mul (.n 21) (.n 16) (.n 20)),
    .atom (.mul (.n 9) (.n 9) (.n 9)),
    .atom (.const (.n 22) (word 1 0)),
    .atom (.const (.n 23) (word 3 0)),
    .atom (.mul (.n 24) (.n 9) (.n 23)),
    .atom (.add (.n 25) (.n 22) (.n 24)),
    .atom (.mul (.n 10) (.n 10) (.n 10)),
    .atom (.const (.n 26) (word 1 0)),
    .atom (.const (.n 27) (word 5 0)),
    .atom (.mul (.n 28) (.n 10) (.n 27)),
    .atom (.add (.n 29) (.n 26) (.n 28)),
    .atom (.mul (.n 30) (.n 25) (.n 29)),
    .atom (.mul (.n 11) (.n 11) (.n 11)),
    .atom (.const (.n 31) (word 1 0)),
    .atom (.const (.n 32) (word 17 0)),
    .atom (.mul (.n 33) (.n 11) (.n 32)),
    .atom (.add (.n 34) (.n 31) (.n 33)),
    .atom (.mul (.n 35) (.n 30) (.n 34)),
    .atom (.mul (.n 12) (.n 12) (.n 12)),
    .atom (.const (.n 36) (word 1 0)),
    .atom (.const (.n 37) (word 257 0)),
    .atom (.mul (.n 38) (.n 12) (.n 37)),
    .atom (.add (.n 39) (.n 36) (.n 38)),
    .atom (.mul (.n 40) (.n 35) (.n 39)),
    .atom (.mul (.n 41) (.n 40) (.n 40)),
    .atom (.mul (.n 42) (.n 41) (.n 41)),
    .atom (.mul (.n 43) (.n 42) (.n 21)),
    .atom (.assertEq (.n 43) (.n 6)),
    .atom (.const (.n 44) (word 4 0)),
    .atom (.mul (.n 45) (.n 40) (.n 44)),
    .atom (.mul (.n 46) (.n 45) (.n 45)),
    .atom (.mul (.n 47) (.n 46) (.n 46)),
    .atom (.mul (.n 48) (.n 47) (.n 45)),
    .atom (.hint (.allocDyn (.n 49) (.n 48))),
    .atom (.load (.n 0) (.n 49) 0),
    .atom (.load (.n 1) (.n 49) 1),
    .atom (.load (.n 2) (.n 49) 2),
    .atom (.load (.n 3) (.n 49) 3),
    .atom (.load (.n 4) (.n 49) 4),
    .atom (.const (.n 50) (word 1 0)),
    .atom (.add (.n 51) (.n 50) (.n 40)),
    .atom (.const (.n 52) (word 1 0)),
    .callIf (.n 51) spLName [.n 52, .n 40, .n 49, .n 5],
    .atom (.mul (.n 53) (.n 40) (.n 40)),
    .atom (.mul (.n 54) (.n 53) (.n 53)),
    .atom (.mul (.n 55) (.n 54) (.n 40)),
    .atom (.mul (.n 56) (.n 49) (.n 55)),
    .atom (.const (.n 57) (word 32 0)),
    .atom (.mul (.n 58) (.n 56) (.n 57)),
    .atom (.mul (.n 59) (.n 40) (.n 40)),
    .atom (.mul (.n 60) (.n 59) (.n 59)),
    .atom (.mul (.n 61) (.n 60) (.n 60)),
    .atom (.mul (.n 62) (.n 61) (.n 61)),
    .atom (.mul (.n 63) (.n 62) (.n 62)),
    .atom (.mul (.n 64) (.n 5) (.n 63))]

/-- After the dispatch: the capacity after the draw read back. -/
def spMPost : List Stmt :=
  [.atom (.load (.n 66) (.n 56) 5), .atom (.load (.n 67) (.n 56) 6), .atom (.load (.n 68) (.n 56) 7),
    .atom (.load (.n 69) (.n 56) 8), .atom (.load (.n 70) (.n 56) 9)]

theorem spMain_eq : (fn% «squeeze_packed»).body =
    spMPre ++ .dispatch (.n 21) splNames [.n 56, .n 58, .n 64] [.n 65] ::
      (spMPost ++ [.ret [.n 66, .n 67, .n 68, .n 69, .n 70]]) := by
  rw [spMain_body]; rfl

theorem find_sp : coreProgram.find? "squeeze_packed" = some fn% «squeeze_packed» :=
  coreProgram_find?_at (j := idx% «squeeze_packed») rfl

theorem sp_not_loop : coreProgram.loop "squeeze_packed" = false := by decide +kernel

theorem sp_params : (fn% «squeeze_packed»).params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6] := rfl

theorem spMPre_straight : spMPre.all Stmt.straight = true := by decide
theorem spMPost_straight : spMPost.all Stmt.straight = true := by decide

theorem spMPre_allocSz : spMPre.filterMap Stmt.allocSz = [(.n 49, .inr (.n 48))] := rfl
theorem spMPre_addrS : spMPre.filterMap Stmt.addrS = [] := rfl
theorem spMPre_callS : spMPre.filterMap Stmt.callS = [(some (.n 51), spLName, [.n 52, .n 40, .n 49, .n 5], [])] := rfl
theorem spMPost_allocSz : spMPost.filterMap Stmt.allocSz = [] := rfl
theorem spMPost_addrS : spMPost.filterMap Stmt.addrS = [] := rfl
theorem spMPost_callS : spMPost.filterMap Stmt.callS = [] := rfl

/-! ## The valuation -/

theorem bitWord_sq (t : Bool) : bitWord t = bitWord t * bitWord t := by cases t <;> simp [bitWord]

theorem bitf (t : Bool) (a : ℕ) : word 1 0 + bitWord t * (gen ^ a + 1) = gen ^ (a * t.toNat) := by
  cases t
  · simp [bitWord, word_one]
  · simp only [bitWord, ↓reduceIte, one_mul, word_one, Bool.toNat_true, mul_one]
    rw [add_comm (gen ^ a) 1, ← add_assoc, add_self_E, zero_add]

theorem bits64 : ∀ p < 64, (p.testBit 0).toNat + 2 * (p.testBit 1).toNat = p % 4 ∧
    (p.testBit 2).toNat + 2 * (p.testBit 3).toNat + 4 * (p.testBit 4).toNat + 8 * (p.testBit 5).toNat = p / 4 := by
  decide

/-- `squeeze_packed`'s valuation: the capacity `cap`, `out`, the count `p`, the records at `c`. -/
def spVals (cap : List E) (out : E) (p c : ℕ) : List E :=
  let b : ℕ → E := fun i => bitWord (p.testBit i)
  let v16 := word 1 0 + b 0 * word 3 0
  let v20 := word 1 0 + b 1 * word 5 0
  let v21 := v16 * v20
  let v25 := word 1 0 + b 2 * word 3 0
  let v29 := word 1 0 + b 3 * word 5 0
  let v30 := v25 * v29
  let v34 := word 1 0 + b 4 * word 17 0
  let v35 := v30 * v34
  let v39 := word 1 0 + b 5 * word 257 0
  let v40 := v35 * v39
  let v41 := v40 * v40
  let v42 := v41 * v41
  let v45 := v40 * word 4 0
  let v46 := v45 * v45
  let v47 := v46 * v46
  let v49 := ofK (addressOfIndex c)
  let v53 := v40 * v40
  let v54 := v53 * v53
  let v55 := v54 * v40
  let v56 := v49 * v55
  let v59 := v40 * v40
  let v60 := v59 * v59
  let v61 := v60 * v60
  let v62 := v61 * v61
  let v63 := v62 * v62
  cap ++ [out, gen ^ p, b 0, b 1, b 2, b 3, b 4, b 5, word 1 0, word 3 0, b 0 * word 3 0, v16, word 1 0, word 5 0,
    b 1 * word 5 0, v20, v21, word 1 0, word 3 0, b 2 * word 3 0, v25, word 1 0, word 5 0, b 3 * word 5 0, v29,
    v30, word 1 0, word 17 0, b 4 * word 17 0, v34, v35, word 1 0, word 257 0, b 5 * word 257 0, v39, v40, v41,
    v42, v42 * v21, word 4 0, v45, v46, v47, v47 * v45, v49, word 1 0, word 1 0 + v40, word 1 0, v53, v54, v55,
    v56, word 32 0, v56 * word 32 0, v59, v60, v61, v62, v63, out * v63, 0] ++ (pkSqueeze p cap).2

/-- `squeeze_packed`'s own words: record `j ≤ q` the capacity after `4 j` permutations, then the
capacity after all `p`. -/
def spWords (cap : List E) (p : ℕ) : List E :=
  (List.range (5 * (p / 4 + 2))).map fun o =>
    if o / 5 ≤ p / 4 then (spRec cap (o / 5)).getD (o % 5) 0 else (pkSqueeze p cap).2.getD (o % 5) 0

theorem readsAt_shift {rd : Reader} {c m : ℕ} {xs : List E}
    (h : ∀ i < xs.length, LoadHolds rd (ptrAt c) (m + i) (xs.getD i 0)) : ReadsAt rd (ptrAt (c + m)) xs := by
  rw [← ptrAt_mul_gen_pow']; exact readsAt_of_getD h

/-- **The buffer holds the records.** -/
theorem spWords_recs {rd : Reader} {cap : List E} (hcap : cap.length = 5) {p c : ℕ}
    (h : ReadsAt rd (ptrAt c) (spWords cap p)) :
    (∀ j ≤ p / 4, ReadsAt rd (ptrAt (c + 5 * j)) (spRec cap j)) ∧
      ReadsAt rd (ptrAt (c + 5 * (p / 4 + 1))) (pkSqueeze p cap).2 := by
  refine ⟨fun j hj => readsAt_shift fun i hi => ?_, readsAt_shift fun i hi => ?_⟩
  · rw [spRec_length hcap] at hi
    have := h (5 * j + i) (by simp [spWords]; omega)
    simp only [spWords, List.getElem_map, List.getElem_range] at this
    rwa [show (5 * j + i) / 5 = j by omega, show (5 * j + i) % 5 = i by omega, ite_eq_left hj] at this
  · rw [pkSqueeze_cap_length _ _ hcap] at hi
    have := h (5 * (p / 4 + 1) + i) (by simp [spWords]; omega)
    simp only [spWords, List.getElem_map, List.getElem_range] at this
    rwa [show (5 * (p / 4 + 1) + i) / 5 = p / 4 + 1 by omega, show (5 * (p / 4 + 1) + i) % 5 = i by omega,
      ite_eq_right (show ¬p / 4 + 1 ≤ p / 4 by omega)] at this


/-! ## Straight runs: events, quiet atoms, exact hints -/

/-- What a straight statement's events ask: an atom's relation, a conditional call's condition in `K`. -/
def SOkV (rd : Reader) (σ : Val) : Stmt → Prop
  | .atom a => a.Holds rd σ
  | .callIf c _ _ => IsInK (σ c)
  | _ => True

theorem events_sokV {rd : Reader} {σ : Val} {s : Stmt} (h : SOkV rd σ s) {e : Ev} (he : e ∈ slEvs σ s) :
    e.Holds rd σ := by
  cases s with
  | atom a =>
    simp only [slEvs, List.mem_cons, List.not_mem_nil, or_false] at he
    subst he; exact h
  | call f args rets =>
    simp only [slEvs, List.mem_cons, List.not_mem_nil, or_false] at he
    subst he; trivial
  | callIf c f args =>
    simp only [slEvs, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact h
    · split <;> trivial
  | _ => simp [slEvs] at he

/-- A statement hinting nothing to the heap. -/
def noHeapHintB : Stmt → Bool
  | .atom a => (atomHeapDest? a).isNone
  | _ => true

theorem heapHintAddrs_nil_of {σ σ' : Val} : ∀ pre : List Stmt, pre.all noHeapHintB = true →
    heapHintAddrs σ (pre.flatMap (slEvs σ')) = []
  | [], _ => rfl
  | s :: pre, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    rw [List.flatMap_cons, heapHintAddrs_append, heapHintAddrs_nil_of pre h.2, List.append_nil]
    cases s with
    | atom a =>
      simp only [slEvs, heapHintAddrs, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      cases a with
      | hint hh =>
        simp only [noHeapHintB, atomHeapDest?, Option.isNone_iff_eq_none] at h
        simp [Ev.hintAddrs, h.1]
      | _ => rfl
    | call => rfl
    | callIf c f args => simp only [slEvs, heapHintAddrs]; split <;> rfl
    | _ => rfl

/-- A statement with no witness hint. -/
def stmtQuietB : Stmt → Bool
  | .atom a => atomQuiet a
  | _ => true

theorem quiet_of_slEvs {σ : Val} {s : Stmt} (h : stmtQuietB s = true) {a : Atom} (ha : Ev.atom a ∈ slEvs σ s) :
    atomQuiet a = true := by
  cases s with
  | atom b =>
    simp only [slEvs, List.mem_singleton, Ev.atom.injEq] at ha
    subst ha; exact h
  | callIf c f args =>
    simp only [slEvs, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with h' | h'
    · cases h'
    · split at h' <;> cases h'
  | call => simp [slEvs] at ha
  | _ => simp [slEvs] at ha

/-- A statement whose hints are `HeapBuf`s only, exact on any valuation. -/
def noComputedB : Stmt → Bool
  | .atom (.hint (.alloc ..)) | .atom (.hint (.allocDyn ..)) => true
  | .atom (.hint _) => false
  | _ => true

theorem exact_of_slEvs {rd : Reader} {σ : Val} {s : Stmt} (h : noComputedB s = true) {e : Ev}
    (he : e ∈ slEvs σ s) : e.Exact rd σ := by
  cases s with
  | atom a =>
    simp only [slEvs, List.mem_singleton] at he
    subst he
    cases a with
    | hint hh => cases hh <;> simp_all [noComputedB, Ev.Exact, Atom.Exact, Hint.Exact]
    | _ => trivial
  | callIf c f args =>
    simp only [slEvs, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · trivial
    · split <;> trivial
  | call => simp only [slEvs, List.mem_singleton] at he; subst he; trivial
  | _ => simp [slEvs] at he

theorem spMPre_quiet : spMPre.all stmtQuietB = true := by decide
theorem spMPost_quiet : spMPost.all stmtQuietB = true := by decide
theorem spMPre_noComputed : spMPre.tail.all noComputedB = true := by decide
theorem spMPost_noComputed : spMPost.all noComputedB = true := by decide

/-! ## Placed -/

variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}

theorem splNames_get {r : ℕ} (hr : r < 4) : splNames[r]! = splNames.getD r "" := by
  interval_cases r <;> rfl

set_option maxHeartbeats 2000000 in
/-- **`squeeze_packed` completes placed**, its end within `2^21` of its cursor when every frame is below
`2^16`. -/
theorem squeeze_packed_completeA (k : ℕ) :
    SqueezePackedCompleteAE fs al cert k (fun c e => FsSmall fs → e ≤ c + 2 ^ 21) := by
  intro f0 f1 f2 f3 f4 out p fp hp hpb
  set cap : List E := [f0, f1, f2, f3, f4] with hcapd
  have hcap : cap.length = 5 := rfl
  rw [pkSqueeze_length] at hpb ⊢
  set c := fp + fs "squeeze_packed" with hc
  set q := p / 4 with hq
  set r := p % 4 with hr
  have hpqr : p = 4 * q + r := by omega
  have hq16 : q < 16 := by omega
  have hr4 : r < 4 := by omega
  obtain ⟨hb1, hb2⟩ := bits64 p hp
  set σ : Val := fun v => (spVals cap out p c).getD v.idx 0 with hσ
  -- the values
  have w3 : word 3 0 = gen ^ 1 + 1 := word_two_pow_xor_one (a := 1) (by norm_num)
  have w5 : word 5 0 = gen ^ 2 + 1 := word_two_pow_xor_one (a := 2) (by norm_num)
  have w17 : word 17 0 = gen ^ 4 + 1 := word_two_pow_xor_one (a := 4) (by norm_num)
  have w257 : word 257 0 = gen ^ 8 + 1 := word_two_pow_xor_one (a := 8) (by norm_num)
  have h21 : σ (.n 21) = gen ^ r := by
    show (word 1 0 + bitWord (p.testBit 0) * word 3 0) * (word 1 0 + bitWord (p.testBit 1) * word 5 0) = _
    rw [w3, w5, bitf, bitf, ← pow_add]; congr 1; omega
  have h40 : σ (.n 40) = gen ^ q := by
    show (((word 1 0 + bitWord (p.testBit 2) * word 3 0) * (word 1 0 + bitWord (p.testBit 3) * word 5 0)) *
      (word 1 0 + bitWord (p.testBit 4) * word 17 0)) * (word 1 0 + bitWord (p.testBit 5) * word 257 0) = _
    rw [w3, w5, w17, w257, bitf, bitf, bitf, bitf, ← pow_add, ← pow_add, ← pow_add]; congr 1; omega
  have e43 : σ (.n 43) = σ (.n 40) * σ (.n 40) * (σ (.n 40) * σ (.n 40)) * σ (.n 21) := rfl
  have hassert : σ (.n 43) + σ (.n 6) = 0 := by
    rw [e43, h40, h21, show σ (.n 6) = gen ^ p from rfl, hpqr]
    rw [show gen ^ q * gen ^ q * (gen ^ q * gen ^ q) * gen ^ r = gen ^ (4 * q + r) by ring]
    exact add_self_E _
  have e48 : σ (.n 48) = (σ (.n 40) * word 4 0) * (σ (.n 40) * word 4 0) * ((σ (.n 40) * word 4 0) *
      (σ (.n 40) * word 4 0)) * (σ (.n 40) * word 4 0) := rfl
  have w4 : word 4 0 = gen ^ 2 := word_two_pow (a := 2) (by norm_num)
  have h48 : σ (.n 48) = gen ^ (5 * (q + 2)) := by rw [e48, h40, w4]; ring
  have h49 : σ (.n 49) = ptrAt c := rfl
  have h51 : σ (.n 51) = word 1 0 + σ (.n 40) := rfl
  have e56 : σ (.n 56) = σ (.n 49) * (σ (.n 40) * σ (.n 40) * (σ (.n 40) * σ (.n 40)) * σ (.n 40)) := rfl
  have h56 : σ (.n 56) = ptrAt (c + 5 * q) := by
    rw [e56, h49, h40, ← ptrAt_mul_gen_pow' c (5 * q)]; ring
  have h58 : σ (.n 58) = ptrAt (c + 5 * q + 5) := by
    rw [show σ (.n 58) = σ (.n 56) * word 32 0 from rfl, h56, show (32 : ℕ) = 2 ^ 5 from rfl,
      word_two_pow (by norm_num), ptrAt_mul_gen_pow']
  have e64 : σ (.n 64) = out * ((((σ (.n 40) * σ (.n 40)) * (σ (.n 40) * σ (.n 40))) *
      ((σ (.n 40) * σ (.n 40)) * (σ (.n 40) * σ (.n 40)))) * (((σ (.n 40) * σ (.n 40)) * (σ (.n 40) * σ (.n 40))) *
      ((σ (.n 40) * σ (.n 40)) * (σ (.n 40) * σ (.n 40)))) * ((((σ (.n 40) * σ (.n 40)) * (σ (.n 40) * σ (.n 40))) *
      ((σ (.n 40) * σ (.n 40)) * (σ (.n 40) * σ (.n 40)))) * (((σ (.n 40) * σ (.n 40)) * (σ (.n 40) * σ (.n 40))) *
      ((σ (.n 40) * σ (.n 40)) * (σ (.n 40) * σ (.n 40)))))) := rfl
  have h64 : σ (.n 64) = out * gen ^ (32 * q) := by rw [e64, h40]; ring
  have hrets : [V.n 66, .n 67, .n 68, .n 69, .n 70].map σ = (pkSqueeze p cap).2 := by
    obtain ⟨x0, x1, x2, x3, x4, he⟩ : ∃ x0 x1 x2 x3 x4, (pkSqueeze p cap).2 = [x0, x1, x2, x3, x4] := by
      have hl := pkSqueeze_cap_length p cap hcap
      match (pkSqueeze p cap).2, hl with | [x0, x1, x2, x3, x4], _ => exact ⟨x0, x1, x2, x3, x4, rfl⟩
    simp only [hσ, spVals, he]; rfl
  -- the path
  set es := spMPre.flatMap (slEvs σ) ++ .call splNames[r]! [.n 56, .n 58, .n 64] [.n 65] ::
    spMPost.flatMap (slEvs σ) with hes
  have hw : walk σ (fn% «squeeze_packed»).body = .ret es [.n 66, .n 67, .n 68, .n 69, .n 70] := by
    rw [spMain_eq]
    exact walk_dispatch σ spMPre spMPost spMPre_straight spMPost_straight (.n 21) splNames _ _ _ (i := r)
      (by simp [splNames]; omega) (by simp [splNames]) (by rw [h21, gen_pow_eq_ofK])
  have hpre := straight_parts σ spMPre spMPre_straight
  have hpost := straight_parts σ spMPost spMPost_straight
  have hallocs : allocs σ es = [5 * (q + 2)] := by
    rw [hes, allocs_append, hpre.2.1, allocs, List.filterMap_cons, ← allocs, hpost.2.1]
    simp [spMPre_allocSz, spMPost_allocSz, Ev.alloc?, h48, logG_gen_pow (show 5 * (q + 2) < 2 ^ 64 - 1 by omega)]
  have hdsts : allocDsts es = [.n 49] := by
    rw [hes, allocDsts_append, hpre.1, allocDsts, List.filterMap_cons, ← allocDsts, hpost.1]
    simp [spMPre_allocSz, spMPost_allocSz, Ev.allocDst?]
  have haddrs : addrs es = [] := by
    rw [hes, addrs_append, hpre.2.2.1, addrs, List.filterMap_cons, ← addrs, hpost.2.2.1]
    simp [spMPre_addrS, spMPost_addrS, Ev.addr?]
  have hcalls : calls es = [⟨spLName, [.n 52, .n 40, .n 49, .n 5], [], decide (σ (.n 51) ≠ 0)⟩,
      ⟨splNames[r]!, [.n 56, .n 58, .n 64], [.n 65], true⟩] := by
    rw [hes, calls_append, hpre.2.2.2, calls, List.filterMap_cons, ← calls, hpost.2.2.2]
    simp [spMPre_callS, spMPost_callS, mkCall, Ev.call?]
  have htk : decide (σ (.n 51) ≠ 0) = decide (q ≠ 0) := by
    rw [h51, h40, word_one]
    refine decide_eq_decide.mpr ⟨fun h he => h (by rw [he, pow_zero]; exact add_self_E _), fun h he => h ?_⟩
    have := e_add_eq_zero_iff.mp he
    rw [← pow_zero gen] at this
    exact (gen_pow_inj (by omega) (by omega) this).symm
  rw [splNames_get hr4] at hcalls hes
  -- the records and the cells the callees read
  have hrecs : ∀ rd, HoldsWords rd [(c, spWords cap p)] →
      (∀ j ≤ q, ReadsAt rd (ptrAt (c + 5 * j)) (spRec cap j)) ∧ ReadsAt rd (ptrAt (c + 5 * (q + 1))) (pkSqueeze p cap).2 :=
    fun rd hw => spWords_recs hcap (hw _ List.mem_cons_self)
  have hlast : (pkSqueeze r (spRec cap q)).2 = (pkSqueeze p cap).2 := by
    rw [hpqr, pkSqueeze_add]; rfl
  have hlastPre : ∀ rd, ReadsAt rd out (pkSqueeze p cap).1 → HoldsWords rd [(c, spWords cap p)] →
      ReadsAt rd (σ (.n 56)) (spRec cap q) ∧ ReadsAt rd (σ (.n 64)) (pkSqueeze r (spRec cap q)).1 ∧
        ReadsAt rd (σ (.n 58)) (pkSqueeze r (spRec cap q)).2 := by
    intro rd hout hw
    obtain ⟨hr1, hr2⟩ := hrecs rd hw
    refine ⟨by rw [h56]; exact hr1 q le_rfl, ?_, by rw [h58, hlast, show c + 5 * q + 5 = c + 5 * (q + 1) by ring]; exact hr2⟩
    rw [h64]
    refine readsAt_of_getD fun i hi => ?_
    rw [pkSqueeze_length] at hi
    have := readsAt_getD hout (i := 32 * q + i) (by rw [pkSqueeze_length]; omega)
    rwa [hpqr, pkSqueeze_add, List.getD_append_right _ _ _ _ (by rw [pkSqueeze_length]; omega), pkSqueeze_length,
      show 32 * q + i - 8 * (4 * q) = i by omega] at this
  -- the regions
  have hown : ∀ i, c ≤ i → i < c + 5 * (q + 2) →
      ownData cert fp c "squeeze_packed" [5 * (q + 2)] es i := fun i h1 h2 =>
    Or.inl ⟨(5 * (q + 2), c), by simp [bases], h1, by omega⟩
  have hptr : ∀ q' ∈ [(0, 5), (1, 5), (2, 8 * r)], ∀ off < q'.2,
      ∃ i, ([σ (.n 56), σ (.n 58), σ (.n 64)].getD q'.1 0).limb 0 * addressOfIndex off = addressOfIndex i ∧
        (ptrRegion [(out, 8 * p)] i ∨ (c ≤ i ∧ i < c + 5 * (q + 2))) := by
    intro q' hq' off hoff
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq'
    rcases hq' with rfl | rfl | rfl
    · refine ⟨c + 5 * q + off, ?_, Or.inr ⟨by omega, by simp at hoff; omega⟩⟩
      rw [show [σ (.n 56), σ (.n 58), σ (.n 64)].getD 0 0 = σ (.n 56) from rfl, h56]
      exact Main.addr_ofK _ _
    · refine ⟨c + 5 * q + 5 + off, ?_, Or.inr ⟨by omega, by simp at hoff; omega⟩⟩
      rw [show [σ (.n 56), σ (.n 58), σ (.n 64)].getD 1 0 = σ (.n 58) from rfl, h58]
      exact Main.addr_ofK _ _
    · simp only at hoff
      obtain ⟨i, -, hi⟩ := hpb (out, 8 * p) List.mem_cons_self (32 * q + off) (by omega)
      refine ⟨i, ?_, Or.inl ⟨_, List.mem_cons_self, 32 * q + off, by omega, hi⟩⟩
      rw [show [σ (.n 56), σ (.n 58), σ (.n 64)].getD 2 0 = σ (.n 64) from rfl, h64, ← hi, gen_pow_eq_ofK,
        limb0_mul_ofK, mul_assoc, addressOfIndex, addressOfIndex, addressOfIndex, ← pow_add]
  have hst0 : ∀ rd, HoldsWords rd [(c, spWords cap p)] → ∀ i < 5, LoadHolds rd (σ (.n 49)) i (cap.getD i 0) := by
    intro rd hw i hi
    have := (hrecs rd hw).1 0 (Nat.zero_le _)
    simp only [Nat.mul_zero, Nat.add_zero, spRec, pkSqueeze] at this
    exact readsAt_getD this (by rw [hcap]; exact hi)
  set cur := c + 5 * (q + 2) with hcur
  set c2 := allocBase (al spLName) cur + spBlock fs q with hc2
  have hub : FsSmall fs → allocBase (al (splNames.getD r "")) c2 + fs (splNames.getD r "") ≤ c + 2 ^ 21 := by
    intro hfs
    have := allocBase_le (al spLName) cur
    have := step_le hfs (al (splNames.getD r "")) (splNames.getD r "") c2
    have : spBlock fs q ≤ (q + 1) * 2 ^ 16 := by
      have h := lpB_le hfs spLName q 0
      simp only [lpB, Nat.sub_zero] at h
      unfold spBlock; exact h
    omega
  refine ⟨allocBase (al (splNames.getD r "")) c2 + fs (splNames.getD r ""), hub, callAtA_node sp_not_loop le_rfl
    ⟨σ, fn% «squeeze_packed», es, [.n 66, .n 67, .n 68, .n 69, .n 70], [(c, spWords cap p)], [PostQuiet, PostQuiet],
      fun rd => HoldsWords rd [(c, spWords cap p)], fun _ => False, find_sp, by rw [sp_params]; rfl, hw, hrets,
      ?_, ?_, ?_, ?_, fun _ h => h.elim, ?_, fun _ _ => trivial, ?_, ?_⟩⟩
  · -- placed
    rw [hallocs]
    exact ⟨by rw [hdsts]; simp [bases, h49], by rw [haddrs]; simp⟩
  · rw [hallocs]
    exact ⟨fun q' hq' => by
      rw [List.mem_singleton] at hq'; subst hq'
      exact Or.inr ⟨le_rfl, by simp [spWords]; omega⟩, List.pairwise_singleton _ _⟩
  · -- the loads
    intro A hA
    rw [hallocs]
    rw [hes, loadAddrs_append, LeanVM.Guest.Memory.loadAddrs_straight _ _ spMPre_straight, loadAddrs, List.filterMap_cons,
      ← loadAddrs, LeanVM.Guest.Memory.loadAddrs_straight _ _ spMPost_straight] at hA
    simp only [Ev.loadAddr?, List.mem_append, List.mem_map] at hA
    rcases hA with ⟨⟨x, off⟩, hq', rfl⟩ | ⟨⟨x, off⟩, hq', rfl⟩
    · have h49' : ∀ off < 5, ∃ i, (σ (.n 49)).limb 0 * addressOfIndex off = addressOfIndex i ∧
          (ownData cert fp c "squeeze_packed" [5 * (q + 2)] es i ∨ ptrRegion [(out, 8 * p)] i ∨ False) :=
        fun off hoff => ⟨c + off, by rw [h49]; exact Main.addr_ofK _ _, Or.inl (hown _ (by omega) (by omega))⟩
      rw [show spMPre.filterMap stmtLoad? = [(.n 49, 0), (.n 49, 1), (.n 49, 2), (.n 49, 3), (.n 49, 4)] from rfl] at hq'
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hq'
      rcases hq' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact h49' _ (by norm_num)
    · have h56' : ∀ off, 5 ≤ off → off < 10 → ∃ i, (σ (.n 56)).limb 0 * addressOfIndex off = addressOfIndex i ∧
          (ownData cert fp c "squeeze_packed" [5 * (q + 2)] es i ∨ ptrRegion [(out, 8 * p)] i ∨ False) :=
        fun off h1 h2 => ⟨c + 5 * q + off, by rw [h56]; exact Main.addr_ofK _ _, Or.inl (hown _ (by omega) (by omega))⟩
      rw [show spMPost.filterMap stmtLoad? = [(.n 56, 5), (.n 56, 6), (.n 56, 7), (.n 56, 8), (.n 56, 9)] from rfl] at hq'
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hq'
      rcases hq' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        exact h56' _ (by norm_num) (by norm_num)
  · -- no heap hint
    intro A hA
    rw [hes, heapHintAddrs_append, heapHintAddrs_nil_of spMPre (by decide), heapHintAddrs, List.flatMap_cons,
      ← heapHintAddrs, heapHintAddrs_nil_of spMPost (by decide)] at hA
    simp [Ev.hintAddrs] at hA
  · -- the callees
    rw [hcalls, hallocs, htk]
    by_cases hq0 : q = 0
    · have hd : decide (q ≠ 0) = false := decide_eq_false (by omega)
      simp only [KidsAtF, hd, Bool.false_eq_true, ↓reduceIte, List.headD_cons, List.tail_cons]
      refine ⟨⟨fun v => ([V.n 52, .n 40, .n 49, .n 5].map σ).getD v.idx 0, fn% «squeeze_packed_loop0», find_spL,
        by rw [spL_params]; rfl⟩, fs (splNames.getD r ""), allocBase (al (splNames.getD r "")) c2 + fs (splNames.getD r ""),
        fun i => ptrRegion [(out, 8 * p)] i ∨ (c ≤ i ∧ i < c + 5 * (q + 2)), fun _ => False, fun _ => True,
        fun i hi => ?_, ?_, rfl, fun _ h => h.1, fun _ h => h.elim⟩
      · rcases hi with hi | hi
        · exact Or.inl (Or.inl hi)
        · exact Or.inl (Or.inr (hown i hi.1 hi.2))
      · have e : allocBase (al spLName) (c + [5 * (q + 2)].sum) + fs (tailKey spLName) = c2 := by
          simp only [hc2, hcur, spBlock, List.sum_cons, List.sum_nil, Nat.add_zero, hq0, zero_mul, zero_add]
        rw [e]
        exact (splA k hr4 (spRec_length hcap q) hptr _ _).mono (fun _ h => h) (fun _ h => h) (fun _ _ => trivial)
          (fun rd h => hlastPre rd h.1 h.2) (fun _ _ _ h => h)
    · have hd : decide (q ≠ 0) = true := decide_eq_true hq0
      simp only [KidsAtF, hd, ↓reduceIte, List.headD_cons, List.tail_cons]
      refine ⟨spBlock fs q, c2, spLR p q c out, fun _ => False, fun _ => True, fun i hi => ?_, ?_,
        fs (splNames.getD r ""), allocBase (al (splNames.getD r "")) c2 + fs (splNames.getD r ""),
        fun i => ptrRegion [(out, 8 * p)] i ∨ (c ≤ i ∧ i < c + 5 * (q + 2)), fun _ => False, fun _ => True,
        fun i hi => ?_, ?_, rfl, fun _ h => h.1.1, fun _ h => h.elim⟩
      · rcases hi with hi | hi
        · exact Or.inl (Or.inl hi)
        · exact Or.inl (Or.inr (hown i hi.1 hi.2))
      · have h0 : [V.n 52, .n 40, .n 49, .n 5].map σ = [gen ^ 0, gen ^ q, ptrAt c, out] := by
          simp only [List.map_cons, List.map_nil, h40, h49, pow_zero]
          rfl
        rw [h0]
        have := spL_callAtA (fs := fs) (al := al) (cert := cert) (cm := c) k hcap (show 4 * q ≤ p by omega) hq16 hpb 0
          (by omega) (allocBase (al spLName) cur) (allocBase (al spLName) cur + spBlock fs q) (by simp)
        rw [Nat.sub_zero] at this
        exact this.mono (fun _ h => h) (fun _ h => h) (fun _ _ => trivial)
          (fun rd h => ⟨(hrecs rd h.2).1, h.1⟩) (fun _ _ _ h => h)
      · rcases hi with hi | hi
        · exact Or.inl (Or.inl hi)
        · exact Or.inl (Or.inr (hown i hi.1 hi.2))
      · exact (splA k hr4 (spRec_length hcap q) hptr _ _).mono (fun _ h => h) (fun _ h => h) (fun _ _ => trivial)
          (fun rd h => hlastPre rd h.1 h.2.1) (fun _ _ _ h => h)
  · -- the events
    intro rd _ hout hw ev hev
    rw [hes] at hev
    simp only [List.mem_append, List.mem_cons] at hev
    rcases hev with hev | rfl | hev
    · obtain ⟨s, hs, hev⟩ := List.mem_flatMap.mp hev
      have hK51 : IsInK (σ (.n 51)) := by
        rw [h51, h40, word_one, ← pow_zero gen]; exact isInK_add (gen_pow_isInK _) (gen_pow_isInK _)
      have hst := hst0 rd hw
      have hs' : SOkV rd σ s := by
        simp only [spMPre, List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        exacts [trivial, bitWord_sq _, rfl, rfl, rfl, rfl, bitWord_sq _, rfl, rfl, rfl, rfl, rfl, bitWord_sq _, rfl, rfl, rfl, rfl, bitWord_sq _, rfl, rfl, rfl, rfl, rfl, bitWord_sq _, rfl, rfl, rfl, rfl, rfl, bitWord_sq _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hassert, rfl, rfl, rfl, rfl, rfl, trivial, hst 0 (by norm_num), hst 1 (by norm_num), hst 2 (by norm_num), hst 3 (by norm_num), hst 4 (by norm_num), rfl, rfl, rfl, hK51, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl]
      exact events_sokV hs' hev
    · trivial
    · obtain ⟨s, hs, hev⟩ := List.mem_flatMap.mp hev
      have hr2 := (hrecs rd hw).2
      simp only [spMPost, List.mem_cons, List.not_mem_nil, or_false] at hs
      have hpost : ∀ i < 5, LoadHolds rd (σ (.n 56)) (5 + i) ((pkSqueeze p cap).2.getD i 0) := fun i hi => by
        rw [h56, ← loadHolds_mul_gen_pow, ptrAt_mul_gen_pow', show c + 5 * q + 5 = c + 5 * (q + 1) by ring]
        exact readsAt_getD hr2 (by rw [pkSqueeze_cap_length _ _ hcap]; exact hi)
      rcases hs with rfl | rfl | rfl | rfl | rfl <;> simp only [slEvs, List.mem_singleton] at hev <;> subst hev
      exacts [hpost 0 (by norm_num), hpost 1 (by norm_num), hpost 2 (by norm_num), hpost 3 (by norm_num),
        hpost 4 (by norm_num)]
  · -- the post
    intro rd ts _ _ _ hv hp'
    refine postQuiet_node find_sp hw (fun a ha => ?_) (fun ev hev => ?_) hv (by rw [hcalls] at hp' ⊢; exact hp') _
    · rw [hes] at ha
      simp only [List.mem_append, List.mem_cons, reduceCtorEq, false_or] at ha
      rcases ha with ha | ha
      · obtain ⟨s, hs, ha⟩ := List.mem_flatMap.mp ha
        exact quiet_of_slEvs (List.all_eq_true.mp spMPre_quiet s hs) ha
      · obtain ⟨s, hs, ha⟩ := List.mem_flatMap.mp ha
        exact quiet_of_slEvs (List.all_eq_true.mp spMPost_quiet s hs) ha
    · rw [hes] at hev
      simp only [List.mem_append, List.mem_cons] at hev
      rcases hev with hev | rfl | hev
      · obtain ⟨s, hs, hev⟩ := List.mem_flatMap.mp hev
        rw [spMPre] at hs
        rcases List.mem_cons.mp hs with rfl | hs
        · simp only [slEvs, List.mem_singleton] at hev
          subst hev
          exact ⟨p, by omega, by rw [show σ (.n 6) = gen ^ p from rfl, gen_pow_eq_ofK], rfl⟩
        · exact exact_of_slEvs (List.all_eq_true.mp spMPre_noComputed s hs) hev
      · trivial
      · obtain ⟨s, hs, hev⟩ := List.mem_flatMap.mp hev
        exact exact_of_slEvs (List.all_eq_true.mp spMPost_noComputed s hs) hev

end
end LeanVM.Guest.B1.VsC
