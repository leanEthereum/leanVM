/-
  LeanVM.Guest.B1.Ring.Loop14Complete

  `__loop13`, completely: on the honest chain, every iteration's block holds on its evaluated
  valuation, so the loop runs from `g^j` to its end `g^8`.
-/

module

public import LeanVM.Guest.B1.Ring.Target
public import LeanVM.Guest.B1.Fwd.Canon
public import LeanVM.Guest.Memory.Uniform

/-!
# `__loop13`, completely

The honest memory of `ring_switch_target(slices, map_challenges)`: the 64 slices `s` at `sl`,
the six challenges `chs` at `mc`, and its chain at `ch`, row `j ≤ 8` holding `(g^(8j), runL j)`
(`chainWords`), `runL` the partial sums `Σ_{t<j} g^(8t)·chunk t` of the chunks
`Σ_i g^i Φ(s_(8t+i))`.

`l14_block`: at `x = g^j`, `j < 8`, the evaluated valuation `l14σ` of the loop's body (`Fwd.ev`)
satisfies every atom of the block: its loads read the slices, the challenges and the chain's row
`j`, and its two stores write row `j + 1`, which the honest chain holds (`Φ` of the loaded slices
by the soundness lemmas `holds_rmapT`, `holds_ltRow`, on the evaluated atoms). `l14_rel`: the loop
holds from `g^j`, `j ≤ 7`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd LeanVM.Guest.Memory

@[expose] public section

/-! ## The honest chain -/

/-- Chunk `t` of the slices: `Σ_i g^i Φ(s_(8t+i))`. -/
def chunkOf (s chs : List E) (t : ℕ) : E := rsChunk ((s.drop (8 * t)).take 8) chs

/-- The chain's running sums. -/
def runL (s chs : List E) : ℕ → E
  | 0 => 0
  | j + 1 => runL s chs j + gen ^ (8 * j) * chunkOf s chs j

/-- **The honest chain**: row `j ≤ 8` holds `(g^(8j), runL j)`. -/
def chainWords (s chs : List E) : List E :=
  (List.range 18).map fun k ↦ if k % 2 = 0 then gen ^ (8 * (k / 2)) else runL s chs (k / 2)

theorem chainWords_length (s chs : List E) : (chainWords s chs).length = 18 := by
  simp [chainWords]

theorem chainWords_get (s chs : List E) {k : ℕ} (hk : k < (chainWords s chs).length) :
    (chainWords s chs)[k] = if k % 2 = 0 then gen ^ (8 * (k / 2)) else runL s chs (k / 2) := by
  simp [chainWords]

/-! ## Helpers -/

theorem rt_rdAt_of_load {rd : Reader} {p : E} {k : ℕ} {v : E} (h : LoadHolds rd p k v) :
    rdAt rd p k = v := by
  rw [rdAt, h.2]; rfl

theorem rt_side_of_load {rd : Reader} {p : E} {k : ℕ} {v : E} (h : LoadHolds rd p k v) :
    IsInK p ∧ (rd (p.limb 0 * Parameters.addressOfIndex k)).isSome := ⟨h.1, by rw [h.2]; rfl⟩

/-- A block of atoms that hold holds. -/
theorem holdsList_of_atoms {C : CallRel} {rd : Reader} {σ : Val} :
    ∀ (ss : List Stmt), (∀ s ∈ ss, ∃ a, s = .atom a ∧ a.Holds rd σ) →
      ∀ {next : Prop} {kret : List E → Prop}, next → Stmt.HoldsList C rd σ ss next kret
  | [], _, _, _, hn => hn
  | s :: ss, h, _, _, hn => by
    obtain ⟨a, rfl, ha⟩ := h s List.mem_cons_self
    exact ⟨ha, holdsList_of_atoms ss (fun t ht ↦ h t (List.mem_cons_of_mem _ ht)) hn⟩

/-! ## The block -/

/-- `__loop13`'s first atoms, `Φ` of the last slice and the seven rows: no store. -/
def l14Main : List Stmt :=
  [.atom (.mul (.n 4) (.n 0) (.n 0)), .atom (.mul (.n 5) (.n 4) (.n 4)),
    .atom (.mul (.n 6) (.n 5) (.n 5)), .atom (.mul (.n 7) (.n 1) (.n 6)),
    .atom (.load (.n 8) (.n 7) 7)] ++ rmapT (.n 8) 9 ++
  ((List.range 7).map fun r ↦ ltRow (r + 1)).flatten

/-- `__loop13`'s last atoms: the chain's next row, and the guard's values. -/
def l14Tail : List Stmt :=
  [.atom (.mul (.n 685) (.n 0) (.n 0)), .atom (.mul (.n 686) (.n 3) (.n 685)),
    .atom (.load (.n 687) (.n 686) 0), .atom (.const (.n 688) (word 256 0 0)),
    .atom (.mul (.n 689) (.n 687) (.n 688)), .atom (.load (.n 689) (.n 686) 2),
    .atom (.load (.n 690) (.n 686) 1), .atom (.mul (.n 691) (.n 687) (.n 684)),
    .atom (.add (.n 692) (.n 690) (.n 691)), .atom (.load (.n 692) (.n 686) 3),
    .atom (.const (.n 693) (word 2 0 0)), .atom (.mul (.n 694) (.n 0) (.n 693)),
    .atom (.const (.n 695) (word 256 0 0)), .atom (.add (.n 696) (.n 694) (.n 695)),
    .atom (.const (.n 697) (word 2 0 0)), .atom (.mul (.n 698) (.n 0) (.n 697))]

theorem loop14T_split : loop14T = (l14Main ++ l14Tail) ++
    [.callIf (.n 696) "__loop13" [.n 698, .n 1, .n 2, .n 3], .ret []] := by
  simp [loop14T, l14Main, l14Tail]

/-- The atoms of a block. -/
def rtAtoms (ss : List Stmt) : List Atom := ss.filterMap fun s => match s with
  | .atom a => some a
  | _ => none

theorem rt_mem_atoms {ss : List Stmt} {a : Atom} (h : a ∈ rtAtoms ss) : Stmt.atom a ∈ ss := by
  obtain ⟨s, hs, hsa⟩ := List.mem_filterMap.mp h
  cases s <;> simp only [reduceCtorEq, Option.some.injEq] at hsa
  subst hsa
  exact hs

theorem rt_atoms_mem {ss : List Stmt} {a : Atom} (h : Stmt.atom a ∈ ss) : a ∈ rtAtoms ss :=
  List.mem_filterMap.mpr ⟨_, h, rfl⟩

theorem l14_allAtoms : (l14Main ++ l14Tail).all (fun s => match s with
    | .atom _ => true | _ => false) = true := by decide +kernel

theorem l14_chk : chk 4 loop14T = some 699 := by decide +kernel

theorem l14_stores : storesOf 4 loop14T =
    [.load (.n 689) (.n 686) 2, .load (.n 692) (.n 686) 3] := by decide +kernel

/-- The loads `__loop13` needs a word for: the slices (`7`), the challenges (`2`), the chain's
row (`686`). -/
def l14LoadOk : Atom → Bool
  | .load _ (.n 7) off => decide (off < 8)
  | .load _ (.n 2) off => decide (off < 6)
  | .load _ (.n 686) off => decide (off < 2)
  | _ => false

theorem l14_needs : (rtAtoms (l14Main ++ l14Tail)).all (fun a => decide (a ∈ storesOf 4 loop14T) ||
    !needsSide a || l14LoadOk a) = true := by decide +kernel

theorem l14_canon : canonChk [] ((rtAtoms (l14Main ++ l14Tail)).filter
    (fun a => decide (a ∉ storesOf 4 loop14T))) = true := by decide +kernel

theorem l14_main_noStore : ∀ a ∈ rtAtoms l14Main, a ∉ storesOf 4 loop14T := by
  rw [l14_stores]; decide +kernel

/-- The evaluated valuation of `__loop13`'s body. -/
noncomputable def l14σ (rd : Reader) (x sl mc ch : E) : Val :=
  B1.Val.ofArgs (ev rd (fun _ => 0) [x, sl, mc, ch] loop14T)

set_option maxRecDepth 10000 in
/-- **`__loop13`'s block holds** on its evaluated valuation, at `x = g^j` over the honest row. -/
theorem l14_block {rd : Reader} {x sl mc ch : E} {vs chs : List E} {xp run : E}
    (hvl : vs.length = 8) (hcl : chs.length = 6) (hvs : ReadsAt rd (sl * x ^ 8) vs)
    (hmc : ReadsAt rd mc chs) (h0 : LoadHolds rd (ch * x ^ 2) 0 xp)
    (h1 : LoadHolds rd (ch * x ^ 2) 1 run) (h2 : LoadHolds rd (ch * x ^ 2) 2 (xp * gen ^ 8))
    (h3 : LoadHolds rd (ch * x ^ 2) 3 (run + xp * rsChunk vs chs)) :
    (∀ a ∈ rtAtoms (l14Main ++ l14Tail), a.Holds rd (l14σ rd x sl mc ch)) ∧
      l14σ rd x sl mc ch (.n 0) = x ∧ l14σ rd x sl mc ch (.n 1) = sl ∧
      l14σ rd x sl mc ch (.n 2) = mc ∧ l14σ rd x sl mc ch (.n 3) = ch ∧
      l14σ rd x sl mc ch (.n 696) = x * gen + gen ^ 8 ∧
      l14σ rd x sl mc ch (.n 698) = x * gen ∧ l14σ rd x sl mc ch (.n 7) = sl * x ^ 8 ∧
      l14σ rd x sl mc ch (.n 686) = ch * x ^ 2 := by
  obtain ⟨σ, hσdef⟩ : ∃ σ, σ = l14σ rd x sl mc ch := ⟨_, rfl⟩
  rw [← hσdef]
  set S : List Atom := [.load (.n 689) (.n 686) 2, .load (.n 692) (.n 686) 3] with hS
  obtain ⟨A, hA⟩ : ∃ A, A = rtAtoms (l14Main ++ l14Tail) := ⟨_, rfl⟩
  rw [← hA]
  obtain ⟨-, -, hgs⟩ := ev_spec rd (fun _ => 0) loop14T [x, sl, mc, ch] l14_chk
  rw [show [x, sl, mc, ch].length = 4 from rfl, l14_stores, ← hS, ← l14σ, ← hσdef] at hgs
  have hg : ∀ a ∈ A, Good rd S (fun _ => 0) σ a := fun a ha =>
    hgs (.atom a) (by rw [loop14T_split]; exact List.mem_append_left _ (rt_mem_atoms (hA ▸ ha)))
  have e0 : σ (.n 0) = x := by
    rw [hσdef]; exact ev_params rd _ (l := [x, sl, mc, ch]) l14_chk (by simp)
  have e1 : σ (.n 1) = sl := by
    rw [hσdef]; exact ev_params rd _ (l := [x, sl, mc, ch]) l14_chk (by simp)
  have e2 : σ (.n 2) = mc := by
    rw [hσdef]; exact ev_params rd _ (l := [x, sl, mc, ch]) l14_chk (by simp)
  have e3 : σ (.n 3) = ch := by
    rw [hσdef]; exact ev_params rd _ (l := [x, sl, mc, ch]) l14_chk (by simp)
  have hpure := pure_holds hg
  have gA : ∀ a, a ∈ A → Good rd S (fun _ => 0) σ a := hg
  -- the pure atoms' equations
  have mulE : ∀ d u v : ℕ, u < d → v < d → Atom.mul (.n d) (.n u) (.n v) ∈ A →
      σ (.n d) = σ (.n u) * σ (.n v) := by
    intro d u v hu hv hm
    have := gA _ hm
    simp only [Good] at this
    rwa [ite_pos' ⟨hu, hv⟩] at this
  have mA : ∀ a, Stmt.atom a ∈ l14Main ++ l14Tail → a ∈ A := fun a h ↦ hA ▸ rt_atoms_mem h
  have e4 := mulE 4 0 0 (by omega) (by omega) (mA _ (by simp [l14Main]))
  have e5 := mulE 5 4 4 (by omega) (by omega) (mA _ (by simp [l14Main]))
  have e6 := mulE 6 5 5 (by omega) (by omega) (mA _ (by simp [l14Main]))
  have e7 := mulE 7 1 6 (by omega) (by omega) (mA _ (by simp [l14Main]))
  have e685 := mulE 685 0 0 (by omega) (by omega) (mA _ (by simp [l14Tail]))
  have e686 := mulE 686 3 685 (by omega) (by omega) (mA _ (by simp [l14Tail]))
  have hσ7 : σ (.n 7) = sl * x ^ 8 := by rw [e7, e6, e5, e4, e1, e0]; ring
  have hσ686 : σ (.n 686) = ch * x ^ 2 := by rw [e686, e685, e3, e0]; ring
  -- the loads' side conditions
  have hside : ∀ a ∈ A, a ∉ S → needsSide a = true → a.Holds rd σ ∨ Side rd S σ a := by
    intro a ha haS hns
    right
    have hok := List.all_eq_true.mp l14_needs a (hA ▸ ha)
    rw [l14_stores, ← hS] at hok
    simp only [hns, Bool.not_true, Bool.or_false, Bool.or_eq_true, decide_eq_true_eq] at hok
    rcases hok with h | h
    · exact absurd h haS
    · match a, h with
      | .load d (.n 7) off, h =>
        simp only [l14LoadOk, decide_eq_true_eq] at h
        simp only [Side, ite_neg' haS, hσ7]
        exact rt_side_of_load (hvs off (by omega))
      | .load d (.n 2) off, h =>
        simp only [l14LoadOk, decide_eq_true_eq] at h
        simp only [Side, ite_neg' haS, e2]
        exact rt_side_of_load (hmc off (by omega))
      | .load d (.n 686) off, h =>
        simp only [l14LoadOk, decide_eq_true_eq] at h
        simp only [Side, ite_neg' haS, hσ686]
        interval_cases off
        · exact rt_side_of_load h0
        · exact rt_side_of_load h1
  -- the non-store atoms
  have hnon : ∀ a ∈ A, a ∉ S → a.Holds rd σ := by
    have hk : canonChk [] (A.filter fun a => decide (a ∉ S)) = true := by
      have := l14_canon; rw [l14_stores, ← hS, ← hA] at this; exact this
    have hσv : ∀ v, σ v = σ (.n v.idx) := fun v => by rw [hσdef]; rfl
    have := atoms_holds (S := S) (w := fun _ => 0) hσv hk
      (fun a ha => hg a (List.mem_filter.mp ha).1) (by simp)
      (fun a ha hns => hside a (List.mem_filter.mp ha).1 (by simpa using (List.mem_filter.mp ha).2) hns)
    exact fun a ha haS => this a (List.mem_filter.mpr ⟨ha, by simpa using haS⟩)
  -- `Φ` of the loaded slices, by the soundness lemmas on the evaluated atoms
  have hmain : Stmt.HoldsList (coreProgram.Rel rd) rd σ l14Main True (fun _ => True) := by
    refine holdsList_of_atoms l14Main (fun s hs => ?_) trivial
    have := List.all_eq_true.mp l14_allAtoms s (List.mem_append_left _ hs)
    cases s <;> simp only [Bool.false_eq_true] at this
    rename_i a
    have haA : a ∈ A := mA a (List.mem_append_left _ hs)
    have haS : a ∉ S := by
      have := l14_main_noStore a (rt_atoms_mem hs)
      rwa [l14_stores, ← hS] at this
    exact ⟨a, rfl, hnon a haA haS⟩
  simp only [l14Main, holdsList_append] at hmain
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hmain
  obtain ⟨-, -, -, -, l8, hmain⟩ := hmain
  obtain ⟨⟨rl0, rv0⟩, hmain⟩ := holds_rmapT hmain
  obtain ⟨hrows, -⟩ := (holdsList_range_flatten 7 (fun r ↦ ltRow (r + 1))
    (fun r ↦ ltRow_noRet (r + 1)) _ _).mp hmain
  have w1 := holds_ltRow (hrows 0 (by decide))
  have w2 := holds_ltRow (hrows 1 (by decide))
  have w3 := holds_ltRow (hrows 2 (by decide))
  have w4 := holds_ltRow (hrows 3 (by decide))
  have w5 := holds_ltRow (hrows 4 (by decide))
  have w6 := holds_ltRow (hrows 5 (by decide))
  have w7 := holds_ltRow (hrows 6 (by decide))
  simp only [ltBase, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, ↓reduceIte,
    show ¬ (2 : ℕ) = 1 by decide, show ¬ (3 : ℕ) = 1 by decide, show ¬ (4 : ℕ) = 1 by decide,
    show ¬ (5 : ℕ) = 1 by decide, show ¬ (6 : ℕ) = 1 by decide, show ¬ (7 : ℕ) = 1 by decide]
    at w1 w2 w3 w4 w5 w6 w7
  simp only [Nat.reduceAdd] at rl0 rv0
  have hmc' : ReadsAt rd (σ (.n 2)) chs := by rw [e2]; exact hmc
  have hvs' : [σ (.n 602), σ (.n 517), σ (.n 432), σ (.n 347), σ (.n 262), σ (.n 177), σ (.n 92),
      σ (.n 8)] = vs := by
    have hv : ReadsAt rd (σ (.n 7)) vs := by rw [hσ7]; exact hvs
    apply List.ext_getElem (by simp [hvl])
    intro k hk _
    simp only [List.length_cons, List.length_nil] at hk
    interval_cases k
    · exact loadHolds_unique w7.2.1 (hv 0 (by omega))
    · exact loadHolds_unique w6.2.1 (hv 1 (by omega))
    · exact loadHolds_unique w5.2.1 (hv 2 (by omega))
    · exact loadHolds_unique w4.2.1 (hv 3 (by omega))
    · exact loadHolds_unique w3.2.1 (hv 4 (by omega))
    · exact loadHolds_unique w2.2.1 (hv 5 (by omega))
    · exact loadHolds_unique w1.2.1 (hv 6 (by omega))
    · exact loadHolds_unique l8 (hv 7 (by omega))
  have hchunk : σ (.n 684) = rsChunk vs chs := by
    rw [readsAt_six_unique hcl hmc' rl0] at rv0
    rw [readsAt_six_unique hcl hmc' w1.2.2.1] at w1
    rw [readsAt_six_unique hcl hmc' w2.2.2.1] at w2
    rw [readsAt_six_unique hcl hmc' w3.2.2.1] at w3
    rw [readsAt_six_unique hcl hmc' w4.2.2.1] at w4
    rw [readsAt_six_unique hcl hmc' w5.2.2.1] at w5
    rw [readsAt_six_unique hcl hmc' w6.2.2.1] at w6
    rw [readsAt_six_unique hcl hmc' w7.2.2.1] at w7
    rw [w7.2.2.2, w7.1, w6.2.2.2, w6.1, w5.2.2.2, w5.1, w4.2.2.2, w4.1, w3.2.2.2, w3.1, w2.2.2.2,
      w2.1, w1.2.2.2, w1.1, rv0, ← hvs']
    simp only [rsChunk, Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_zero,
      List.getD_cons_succ, pow_zero, pow_one, one_mul, zero_add]
    ring
  -- the tail's values
  have constE : ∀ d : ℕ, ∀ c : E, Atom.const (.n d) c ∈ A → σ (.n d) = c := fun d c h ↦ gA _ h
  have loadE : ∀ d p off : ℕ, Atom.load (.n d) (.n p) off ∈ A → Atom.load (.n d) (.n p) off ∉ S →
      σ (.n d) = rdAt rd (σ (.n p)) off := by
    intro d p off h hS'
    rcases (gA _ h : Good rd S _ σ _) with h' | h'
    · exact absurd h' hS'
    · exact h'
  have addE : ∀ d u v : ℕ, Atom.add (.n d) (.n u) (.n v) ∈ A → σ (.n d) = σ (.n u) + σ (.n v) :=
    fun d u v h ↦ gA _ h
  have e687 : σ (.n 687) = xp := by
    rw [loadE 687 686 0 (mA _ (by simp [l14Tail])) (by rw [hS]; decide), hσ686]
    exact rt_rdAt_of_load h0
  have e690 : σ (.n 690) = run := by
    rw [loadE 690 686 1 (mA _ (by simp [l14Tail])) (by rw [hS]; decide), hσ686]
    exact rt_rdAt_of_load h1
  have e688 := constE 688 (word 256 0 0) (mA _ (by simp [l14Tail]))
  have e689 := mulE 689 687 688 (by omega) (by omega) (mA _ (by simp [l14Tail]))
  have e691 := mulE 691 687 684 (by omega) (by omega) (mA _ (by simp [l14Tail]))
  have e692 := addE 692 690 691 (mA _ (by simp [l14Tail]))
  have e693 := constE 693 (word 2 0 0) (mA _ (by simp [l14Tail]))
  have e694 := mulE 694 0 693 (by omega) (by omega) (mA _ (by simp [l14Tail]))
  have e695 := constE 695 (word 256 0 0) (mA _ (by simp [l14Tail]))
  have e696 := addE 696 694 695 (mA _ (by simp [l14Tail]))
  have e697 := constE 697 (word 2 0 0) (mA _ (by simp [l14Tail]))
  have e698 := mulE 698 0 697 (by omega) (by omega) (mA _ (by simp [l14Tail]))
  have w256 : word 256 0 0 = gen ^ 8 := word_two_pow (a := 8) (by decide)
  refine ⟨fun a ha => ?_, e0, e1, e2, e3, ?_, ?_, hσ7, hσ686⟩
  · by_cases haS : a ∈ S
    · rw [hS] at haS
      simp only [List.mem_cons, List.not_mem_nil, or_false] at haS
      rcases haS with rfl | rfl
      · show LoadHolds rd (σ (.n 686)) 2 (σ (.n 689))
        rw [hσ686, e689, e687, e688, w256]
        exact h2
      · show LoadHolds rd (σ (.n 686)) 3 (σ (.n 692))
        rw [hσ686, e692, e690, e691, e687, hchunk]
        exact h3
    · exact hnon a ha haS
  · rw [e696, e694, e695, e693, e0, word_gen, w256]
  · rw [e698, e697, e0, word_gen]

/-! ## The loop, loading the slices, the challenges and the chain -/

/-- The loads of `__loop13`'s block: the slices' eight (`7`), the six challenges (`2`), the
chain's row and the next (`686`). -/
def l14LoadIn : Atom → Bool
  | .load _ (.n 7) off => decide (off < 8)
  | .load _ (.n 2) off => decide (off < 6)
  | .load _ (.n 686) off => decide (off < 4)
  | .load .. => false
  | _ => true

theorem l14LoadIn_load {d p : V} {off : ℕ} (h : l14LoadIn (.load d p off) = true) :
    (p = .n 7 ∧ off < 8) ∨ (p = .n 2 ∧ off < 6) ∨ (p = .n 686 ∧ off < 4) := by
  unfold l14LoadIn at h
  split at h <;> simp_all

theorem l14_loadIn : (rtAtoms (l14Main ++ l14Tail)).all l14LoadIn = true := by decide +kernel

/-- `__loop13`'s statements before its `ret`. -/
def l14Pre : List Stmt :=
  (l14Main ++ l14Tail) ++ [Stmt.callIf (.n 696) "__loop13" [.n 698, .n 1, .n 2, .n 3]]

theorem l14_body_pre : Data.core269.body = l14Pre ++ [.ret []] := by
  simp only [loop14_body, loop14T_split, l14Pre, List.append_assoc, List.cons_append,
    List.nil_append]

theorem l14_straight : l14Pre.all Main.Stmt.straight = true := by
  decide +kernel

theorem l14_callS : l14Pre.filterMap Main.Stmt.callS =
    [(some (.n 696), "__loop13", [.n 698, .n 1, .n 2, .n 3], [])] := by decide +kernel

theorem rt_addr_mul (b c k : ℕ) : (ofK (Parameters.addressOfIndex b) * gen ^ c).limb 0 *
    Parameters.addressOfIndex k =
    Parameters.addressOfIndex (b + c + k) := by
  have e : ofK (Parameters.addressOfIndex b) * gen ^ c = ofK (Parameters.addressOfIndex (b +
      c)) := by
    rw [gen_pow_eq_ofK, ← ofK_mul, Parameters.addressOfIndex, Parameters.addressOfIndex,
        Parameters.addressOfIndex, pow_add]
  rw [e, Main.addr_ofK]

/-- **One iteration of `__loop13`, loading its regions**: at `g^j`, `j < 8`, over the honest
chain, the next iteration's relation (while `j < 7`) gives this one's. -/
theorem l14_iter {rd : Reader} {bs bm bc : ℕ} {s chs : List E} (hs : s.length = 64)
    (hc : chs.length = 6) (hsl : ReadsAt rd (ofK (Parameters.addressOfIndex bs)) s)
    (hmc : ReadsAt rd (ofK (Parameters.addressOfIndex bm)) chs)
    (hch : ReadsAt rd (ofK (Parameters.addressOfIndex bc)) (chainWords s chs)) {R : ℕ → Prop}
    (hR : ∀ i, (bs ≤ i ∧ i < bs + 64) ∨ (bm ≤ i ∧ i < bm + 6) ∨ (bc ≤ i ∧ i < bc + 18) → R i)
    {j : ℕ} (hj : j < 8)
    (hnext : j < 7 → coreProgram.RelIn rd R "__loop13" [gen ^ (j + 1), ofK
        (Parameters.addressOfIndex bs),
      ofK (Parameters.addressOfIndex bm), ofK (Parameters.addressOfIndex bc)] []) :
    coreProgram.RelIn rd R "__loop13" [gen ^ j, ofK (Parameters.addressOfIndex bs), ofK
        (Parameters.addressOfIndex bm),
      ofK (Parameters.addressOfIndex bc)] [] := by
  -- the row's facts
  have hvl : ((s.drop (8 * j)).take 8).length = 8 := by simp [hs]; omega
  have hvs : ReadsAt rd (ofK (Parameters.addressOfIndex bs) * (gen ^ j) ^ 8) ((s.drop (8 * j)).take
      8) := by
    intro k hk
    rw [← pow_mul, show j * 8 = 8 * j by ring, loadHolds_mul_gen_pow]
    simp only [List.getElem_take, List.getElem_drop]
    exact hsl _ (by rw [hs]; rw [hvl] at hk; omega)
  have hrow : ∀ k, (hk : 2 * j + k < 18) → LoadHolds rd (ofK (Parameters.addressOfIndex bc) * (gen ^
      j) ^ 2) k
      ((chainWords s chs)[2 * j + k]'(by rw [chainWords_length]; exact hk)) := by
    intro k hk
    rw [← pow_mul, show j * 2 = 2 * j by ring, loadHolds_mul_gen_pow]
    exact hch _ _
  have h0 := hrow 0 (by omega)
  have h1 := hrow 1 (by omega)
  have h2 := hrow 2 (by omega)
  have h3 := hrow 3 (by omega)
  simp only [chainWords_get, Nat.add_zero, show 2 * j % 2 = 0 by omega, show 2 * j / 2 = j by omega,
    ↓reduceIte] at h0
  simp only [chainWords_get, show (2 * j + 1) % 2 = 1 by omega, show (2 * j + 1) / 2 = j by omega,
    one_ne_zero, ↓reduceIte] at h1
  simp only [chainWords_get, show (2 * j + 2) % 2 = 0 by omega,
    show (2 * j + 2) / 2 = j + 1 by omega, ↓reduceIte, show 8 * (j + 1) = 8 * j + 8 by ring,
    pow_add] at h2
  simp only [chainWords_get, show (2 * j + 3) % 2 = 1 by omega,
    show (2 * j + 3) / 2 = j + 1 by omega, one_ne_zero, ↓reduceIte, runL] at h3
  obtain ⟨hat, e0, e1, e2, e3, e696, e698, e7, e686⟩ := l14_block hvl hc hvs hmc h0 h1 h2 h3
  obtain ⟨σ, hσdef⟩ : ∃ σ, σ = l14σ rd (gen ^ j) (ofK (Parameters.addressOfIndex bs))
      (ofK (Parameters.addressOfIndex bm)) (ofK (Parameters.addressOfIndex bc)) := ⟨_, rfl⟩
  rw [← hσdef] at hat e0 e1 e2 e3 e696 e698 e7 e686
  have hw := Main.walk_straight σ [] l14Pre l14_straight
  rw [← l14_body_pre] at hw
  -- the events of the block and the guard
  have hev : ∀ e ∈ l14Pre.flatMap (Main.slEvs σ), (∃ a ∈ rtAtoms (l14Main ++ l14Tail), e = .atom a) ∨
      e = .inK (.n 696) ∨ e = .skip "__loop13" [.n 698, .n 1, .n 2, .n 3] ∨
      e = .call "__loop13" [.n 698, .n 1, .n 2, .n 3] [] := by
    intro e he
    obtain ⟨st, hst, he⟩ := List.mem_flatMap.mp he
    rw [l14Pre, List.mem_append] at hst
    rcases hst with hst | hst
    · have := List.all_eq_true.mp l14_allAtoms st hst
      cases st <;> simp only [Bool.false_eq_true] at this
      rename_i a
      simp only [Main.slEvs, List.mem_singleton] at he
      exact Or.inl ⟨a, rt_atoms_mem hst, he⟩
    · simp only [List.mem_singleton] at hst
      subst hst
      simp only [Main.slEvs, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | he
      · exact Or.inr (Or.inl rfl)
      · split at he <;> subst he <;> simp
  refine relIn_of_walk coreProgram_wf find_loop14 ?_ hw rfl ?_ ?_ ?_
  · show [Core.V.n 0, .n 1, .n 2, .n 3].map σ = _
    simp only [List.map_cons, List.map_nil, e0, e1, e2, e3]
  · intro e he
    rcases hev e he with ⟨a, ha, rfl⟩ | rfl | rfl | rfl
    · exact hat a ha
    · show IsInK (σ (.n 696))
      rw [e696]
      exact isInK_add (isInK_mul (gen_pow_isInK j) (by simpa using gen_pow_isInK 1))
        (gen_pow_isInK 8)
    · trivial
    · trivial
  · intro A hA
    obtain ⟨e, he, hea⟩ := List.mem_filterMap.mp hA
    rcases hev e he with ⟨a, ha, rfl⟩ | rfl | rfl | rfl
    · have hok := List.all_eq_true.mp l14_loadIn a ha
      cases a with
      | load d p off =>
        simp only [Ev.loadAddr?, Option.some.injEq] at hea
        subst hea
        rcases l14LoadIn_load hok with ⟨rfl, ho⟩ | ⟨rfl, ho⟩ | ⟨rfl, ho⟩
        · rw [e7, ← pow_mul, rt_addr_mul]
          exact ⟨_, rfl, hR _ (Or.inl ⟨by omega, by omega⟩)⟩
        · rw [e2, Main.addr_ofK]
          exact ⟨_, rfl, hR _ (Or.inr (Or.inl ⟨by omega, by omega⟩))⟩
        · rw [e686, ← pow_mul, rt_addr_mul]
          exact ⟨_, rfl, hR _ (Or.inr (Or.inr ⟨by omega, by omega⟩))⟩
      | _ => simp [Ev.loadAddr?] at hea
    · simp [Ev.loadAddr?] at hea
    · simp [Ev.loadAddr?] at hea
    · simp [Ev.loadAddr?] at hea
  · intro c hc htaken
    rw [(Main.straight_parts σ l14Pre l14_straight).2.2.2, l14_callS] at hc
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hc
    subst hc
    simp only [Main.mkCall, decide_eq_true_eq] at htaken ⊢
    have hj7 : j < 7 := by
      by_contra hj7
      have : j = 7 := by omega
      subst this
      exact htaken (by rw [e696, gen_pow_mul_gen]; exact e_add_self _)
    simp only [List.map_cons, List.map_nil, e698, e1, e2, e3, gen_pow_mul_gen]
    exact hnext hj7

/-- **`__loop13`, completely, loading its regions**: over the honest chain, from `g^j`, `j ≤ 7`. -/
theorem l14_relIn {rd : Reader} {bs bm bc : ℕ} {s chs : List E} (hs : s.length = 64)
    (hc : chs.length = 6) (hsl : ReadsAt rd (ofK (Parameters.addressOfIndex bs)) s)
    (hmc : ReadsAt rd (ofK (Parameters.addressOfIndex bm)) chs)
    (hch : ReadsAt rd (ofK (Parameters.addressOfIndex bc)) (chainWords s chs)) {R : ℕ → Prop}
    (hR : ∀ i, (bs ≤ i ∧ i < bs + 64) ∨ (bm ≤ i ∧ i < bm + 6) ∨ (bc ≤ i ∧ i < bc + 18) → R i) :
    ∀ t j, j + t = 7 → coreProgram.RelIn rd R "__loop13"
      [gen ^ j, ofK (Parameters.addressOfIndex bs), ofK (Parameters.addressOfIndex bm), ofK (Parameters.addressOfIndex bc)] [] := by
  intro t
  induction t with
  | zero => exact fun j hj ↦ l14_iter hs hc hsl hmc hch hR (by omega) fun h ↦ absurd h (by omega)
  | succ t ih => exact fun j hj ↦ l14_iter hs hc hsl hmc hch hR (by omega) fun _ ↦ ih (j + 1) (by omega)

end
end LeanVM.Guest.B1.VerifySub
