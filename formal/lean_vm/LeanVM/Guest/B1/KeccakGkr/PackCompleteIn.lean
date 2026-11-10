/-
  LeanVM.Guest.B1.KeccakGkr.PackCompleteIn

  The pack rounds' loop helpers, completely and with their loads placed.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.PackComplete
public import LeanVM.Guest.B1.KeccakGkr.RecIn

/-!
# The pack rounds' loops, their loads placed

An iteration of the eight-round loop at `x` loads the record `rec·x` (the offsets
`roundRecOffs`), the coordinates at `pp·x⁸`, the challenges' slots at `pt·x⁸` and sixteen stream
words at the record's cursor (`Pack8Regions`); one of the remainder loop loads the record, the
coordinate at `pp·x`, the challenge's slot at `pt·x` and two stream words (`PackRemRegions`).
With those words in a region `R` at every counter, each loop's relation loads from `R`
(`pack8Loop_relIn`, `packRemLoop_relIn`): one tree per iteration (`Memory.relIn_of_walk`,
`loop6_relIn_step`), its only callee the next iteration.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.Memory LeanVM.Guest.Lift
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## A loop of six parameters, one iteration -/

/-- **One iteration on its loads' region**, the next one (if any) given: a body of atoms `pre`
then the self-call guarded by `c` with the counter `nx`, its atoms holding on `σ`. -/
theorem loop6_relIn_step {name : String} {fn : Fn} (hf : coreProgram.find? name = some fn)
    {pre : List Stmt} {c nx : ℕ}
    (hb : fn.body = pre ++ [.callIf (.n c) name [.n nx, .n 1, .n 2, .n 3, .n 4, .n 5], .ret []])
    (hpar : fn.params = loopParams) (hat : pre.all isAtom = true)
    {rd : Reader} {R : ℕ → Prop} {a2 a3 a4 a5 : E} {m k : ℕ} (hk : k < m) {σ : Val}
    (hp : [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5)] =
      [gen ^ k, gen ^ m, a2, a3, a4, a5])
    (hblk : ∀ a, Stmt.atom a ∈ pre → a.Holds rd σ) (hc : σ (.n c) = gen ^ k * gen + gen ^ m)
    (hn : σ (.n nx) = gen ^ k * gen)
    (hL : ∀ q ∈ pre.filterMap Stmt.loadS, InR R (σ q.1) q.2)
    (hnext : k + 1 < m → coreProgram.RelIn rd R name [gen ^ (k + 1), gen ^ m, a2, a3, a4, a5] []) :
    coreProgram.RelIn rd R name [gen ^ k, gen ^ m, a2, a3, a4, a5] [] := by
  have hpreS : pre.all Stmt.straight = true := List.all_eq_true.2 fun s hs ↦ by
    have := List.all_eq_true.1 hat s hs
    cases s with
    | atom a => rfl
    | _ => simp [isAtom] at this
  have hst : (pre ++ [Stmt.callIf (.n c) name [.n nx, .n 1, .n 2, .n 3, .n 4, .n 5]]).all
      Stmt.straight = true := by
    rw [List.all_append]
    simp only [Bool.and_eq_true]
    exact ⟨hpreS, rfl⟩
  have hw : walk σ fn.body = .ret ((pre ++ [Stmt.callIf (.n c) name
      [.n nx, .n 1, .n 2, .n 3, .n 4, .n 5]]).flatMap (slEvs σ)) [] := by
    rw [hb, show pre ++ [Stmt.callIf (.n c) name [.n nx, .n 1, .n 2, .n 3, .n 4, .n 5], .ret []] =
      (pre ++ [Stmt.callIf (.n c) name [.n nx, .n 1, .n 2, .n 3, .n 4, .n 5]]) ++ [.ret []] by simp]
    exact walk_straight σ [] _ hst
  have hcalls : pre.filterMap Stmt.callS = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro s hs
    have := List.all_eq_true.1 hat s hs
    cases s with
    | atom a => rfl
    | _ => simp [isAtom] at this
  refine relIn_of_walk coreProgram_wf hf (by rw [hpar, loopParams]; exact hp) hw rfl
    (fun e he ↦ ?_) (fun A hA ↦ ?_) (fun c' hc' ht ↦ ?_)
  · rw [List.flatMap_append, List.mem_append] at he
    rcases he with he | he
    · obtain ⟨s, hs', hes⟩ := List.mem_flatMap.1 he
      have hat' := List.all_eq_true.1 hat s hs'
      cases s with
      | atom a =>
        simp only [slEvs, List.mem_singleton] at hes
        subst hes
        exact hblk a hs'
      | _ => simp [isAtom] at hat'
    · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, slEvs,
        List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · show IsInK (σ (.n c))
        rw [hc, ← pow_succ]
        exact isInK_add (gen_pow_isInK _) (gen_pow_isInK _)
      · split <;> trivial
  · rw [loadAddrs_straight σ _ hst, List.filterMap_append] at hA
    simp only [Stmt.loadS, List.filterMap_cons, List.filterMap_nil, List.append_nil,
      List.mem_map] at hA
    obtain ⟨q, hq, rfl⟩ := hA
    exact hL q hq
  · rw [(straight_parts σ _ hst).2.2.2, List.filterMap_append, hcalls] at hc'
    simp only [List.nil_append, Stmt.callS, List.filterMap_cons, List.filterMap_nil,
      List.map_cons, List.map_nil, List.mem_singleton] at hc'
    subst hc'
    simp only [mkCall, decide_eq_true_eq] at ht
    simp only [List.cons.injEq, and_true] at hp
    obtain ⟨-, h1, h2, h3, h4, h5⟩ := hp
    have hk1 : k + 1 < m := by
      by_contra hge
      apply ht
      rw [hc, ← pow_succ, show k + 1 = m by omega]
      exact e_add_eq_zero_iff.mpr rfl
    show coreProgram.RelIn rd R name [σ (.n nx), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5)] []
    rw [hn, h1, h2, h3, h4, h5, ← pow_succ]
    exact hnext hk1

/-- **A loop of six parameters runs from `1`**, every iteration given its successor. -/
theorem loop6_relIn_guard {name : String} {rd : Reader} {R : ℕ → Prop} {a2 a3 a4 a5 : E} {m : ℕ}
    (hstep : ∀ k < m, (k + 1 < m → coreProgram.RelIn rd R name
      [gen ^ (k + 1), gen ^ m, a2, a3, a4, a5] []) →
        coreProgram.RelIn rd R name [gen ^ k, gen ^ m, a2, a3, a4, a5] []) :
    IsInK (1 + gen ^ m) ∧
      (1 + gen ^ m ≠ 0 → coreProgram.RelIn rd R name [1, gen ^ m, a2, a3, a4, a5] []) := by
  refine ⟨by rw [← pow_zero gen]; exact isInK_add (gen_pow_isInK _) (gen_pow_isInK _),
    fun hne ↦ ?_⟩
  have key : ∀ t k, k + 1 + t = m →
      coreProgram.RelIn rd R name [gen ^ k, gen ^ m, a2, a3, a4, a5] [] := by
    intro t
    induction t with
    | zero =>
      intro k hk
      exact hstep k (by omega) (fun h ↦ absurd h (by omega))
    | succ t ih =>
      intro k hk
      exact hstep k (by omega) (fun _ ↦ ih (k + 1) (by omega))
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · exact absurd (e_add_eq_zero_iff.mpr (pow_zero gen).symm) hne
  · have := key (m - 1) 0 (by omega)
    rwa [pow_zero] at this

/-! ## The eight-round loop -/

/-- The words an iteration of the eight-round loop at `x` loads lie in `R`. -/
def Pack8Regions (R : ℕ → Prop) (rd : Reader) (rec pp pt x : E) : Prop :=
  (∀ k ∈ roundRecOffs, InR R (rec * x) k) ∧ (∀ q < 8, InR R (pp * x ^ 8) q) ∧
    (∀ q < 8, InR R (pt * x ^ 8) q) ∧
    ∀ cur, LoadHolds rd (rec * x) 80 cur → ∀ k < 16, InR R cur k

/-- The eight-round loop's loads: the record, the coordinates, the stream words, the slots. -/
def pack8LoadOk (q : V × ℕ) : Bool :=
  (decide (q.1 = .n 6) && roundRecOffs.contains q.2) || (decide (q.1 = .n 10) && decide (q.2 < 8)) ||
    (decide (q.1 = .n 20) && decide (q.2 < 16)) || (decide (q.1 = .n 14) && decide (q.2 < 8))

theorem pack8_loads : (pack8Pre.filterMap Stmt.loadS).all pack8LoadOk = true := by decide +kernel

/-- **The eight-round loop is complete, its loads placed**: an honest iteration at every `g^j`,
`j < m`, its words in `R`, gives the guard and the loop run of `keccak_layer`'s call loading from
`R`. -/
theorem pack8Loop_relIn {first : ℕ} (hfirst : first < 2) {rd : Reader} {R : ℕ → Prop}
    {rec pp pt tb : E} {m : ℕ} (hs : ∀ j < m, Pack8Hon rd rec pp pt (gen ^ j))
    (hR : ∀ j < m, Pack8Regions R rd rec pp pt (gen ^ j)) :
    IsInK (1 + gen ^ m) ∧ (1 + gen ^ m ≠ 0 →
      coreProgram.RelIn rd R (packLoopName first) [1, gen ^ m, rec, pp, pt, tb] []) := by
  obtain ⟨fn, hf, hb, hpar⟩ := find_pack8 hfirst
  refine loop6_relIn_guard fun k hk hnext ↦ ?_
  obtain ⟨σ, hp, hblk, v5, v9, v13, l19, v447, v449⟩ :=
    pack8Block_complete (N := gen ^ m) (tb := tb) (hs k hk)
  obtain ⟨r5, r9, r13, r19⟩ := hR k hk
  refine loop6_relIn_step hf (hb.trans rfl) hpar pack8Pre_atoms hk hp hblk v447 v449 (fun q hq ↦ ?_)
    hnext
  have := List.all_eq_true.1 pack8_loads q hq
  simp only [pack8LoadOk, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    List.contains_iff_mem] at this
  rcases this with (((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩)
  · rw [h1, v5]; exact r5 _ h2
  · rw [h1, v9]; exact r9 _ h2
  · rw [h1]; exact r19 _ l19 _ h2
  · rw [h1, v13]; exact r13 _ h2

/-! ## The remainder loop -/

/-- The words an iteration of the remainder loop at `x` loads lie in `R`. -/
def PackRemRegions (R : ℕ → Prop) (rd : Reader) (rec pp pt x : E) : Prop :=
  (∀ k ∈ roundRecOffs, InR R (rec * x) k) ∧ InR R (pp * x) 0 ∧ InR R (pt * x) 0 ∧
    ∀ cur, LoadHolds rd (rec * x) 80 cur → ∀ k < 2, InR R cur k

/-- The remainder loop's loads. -/
def packRemLoadOk (q : V × ℕ) : Bool :=
  (decide (q.1 = .n 6) && roundRecOffs.contains q.2) || (decide (q.1 = .n 7) && decide (q.2 = 0)) ||
    (decide (q.1 = .n 14) && decide (q.2 < 2)) || (decide (q.1 = .n 40) && decide (q.2 = 0))

theorem packRem_loads : (packRemPre.filterMap Stmt.loadS).all packRemLoadOk = true := by
  decide +kernel

/-- **The remainder loop is complete, its loads placed.** -/
theorem packRemLoop_relIn {first : ℕ} (hfirst : first < 2) {rd : Reader} {R : ℕ → Prop}
    {rec pp tb pt : E} {m : ℕ} (hs : ∀ j < m, PackRemHon rd rec pp pt (gen ^ j))
    (hR : ∀ j < m, PackRemRegions R rd rec pp pt (gen ^ j)) :
    IsInK (1 + gen ^ m) ∧ (1 + gen ^ m ≠ 0 →
      coreProgram.RelIn rd R (remLoopName first) [1, gen ^ m, rec, pp, tb, pt] []) := by
  obtain ⟨fn, hf, hb, hpar⟩ := find_packRem hfirst
  refine loop6_relIn_guard fun k hk hnext ↦ ?_
  obtain ⟨σ, hp, hblk, v5, v6, v59, l13, v77, v79⟩ :=
    packRemBlock_complete (N := gen ^ m) (tb := tb) (hs k hk)
  obtain ⟨r5, r6, r59, r13⟩ := hR k hk
  refine loop6_relIn_step hf (hb.trans rfl) hpar packRemPre_atoms hk hp hblk v77 v79 (fun q hq ↦ ?_)
    hnext
  have := List.all_eq_true.1 packRem_loads q hq
  simp only [packRemLoadOk, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    List.contains_iff_mem] at this
  rcases this with (((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩)
  · rw [h1, v5]; exact r5 _ h2
  · rw [h1, v6, h2]; exact r6
  · rw [h1]; exact r13 _ l13 _ h2
  · rw [h1, v59, h2]; exact r59

end
end LeanVM.Guest.B1.VerifySub
