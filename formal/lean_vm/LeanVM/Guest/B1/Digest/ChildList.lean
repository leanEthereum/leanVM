/-
  LeanVM.Guest.B1.Digest.ChildList

  B1 for `child_claim_list_any` (G:4169-4231, 4305-4320; TRIAGE #89): a child's claim list
  rebuilt from this node's table through hinted slots, each marked in the coverage table, and its
  digest.
-/

module

public import LeanVM.Guest.B1.Digest.ClaimList
public import LeanVM.Guest.B1.Digest.ChildListAny0
public import LeanVM.Guest.B1.Digest.ChildListAny1
public import LeanVM.Guest.B1.Digest.ChildListAny2
public import LeanVM.Guest.B1.Digest.ChildListAny3
public import LeanVM.Guest.B1.Digest.ChildListLasts

/-!
# `child_claim_list_any`

As `claim_list_digest`, but claim `j` of a frame is read at a hinted slot `o` of the table
(`child_claims`, G:4169-4183): `o` passes a range check against `last = limit · g⁻¹`, the region's
coverage slot `region · g^o` holds the mark `marks · g^j` (the marks stepped by `g`), and the four
cells are read at `entries · g^(4o)`. `claimOk` checks one such record in a list of atoms, by
evaluation, and `claimOk_sound` gives it on a memory image. The records sit at fixed value offsets
in the 17 specializations `child_claim_list_last__L{k}` and in the frame loops `__loop17` (136
claims) and `__loop18` (17) (`ccOV`, `ccMark`, `ccCell`).
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## One claim record -/

theorem rcOf_sound {rd : Reader} {σ : Val} {atoms : List Atom} {x k : V}
    (h : rcOf atoms x = some k) (hat : ∀ a ∈ atoms, a.Holds rd σ) :
    ∃ y t1 t2 : E, LoadHolds rd (σ x) 0 t1 ∧ σ k = σ x * y ∧ LoadHolds rd y 0 t2 := by
  obtain ⟨a, ha, hs⟩ := List.exists_of_findSome?_eq_some h
  have := hat a ha
  cases a <;> simp only [reduceCtorEq] at hs
  rename_i x' y t1 t2 k'
  split at hs
  · rename_i hd
    obtain rfl := Option.some.inj hs
    subst hd
    exact ⟨σ y, σ t1, σ t2, this⟩
  · exact absurd hs (by simp)

theorem loadOf_sound {rd : Reader} {σ : Val} {atoms : List Atom} {x p : V} {off : ℕ}
    (h : loadOf atoms x = some (p, off)) (hat : ∀ a ∈ atoms, a.Holds rd σ) :
    LoadHolds rd (σ p) off (σ x) := by
  obtain ⟨a, ha, hs⟩ := List.exists_of_findSome?_eq_some h
  have := hat a ha
  cases a <;> simp only [reduceCtorEq] at hs
  split at hs
  · rename_i hd
    obtain ⟨rfl, rfl⟩ := Option.some.inj hs
    subst hd
    exact this
  · exact absurd hs (by simp)

theorem monoPerm_sound {rd : Reader} {σ : Val} {atoms : List Atom} {x : V} {l : List V}
    (h : (monoOf atoms 40 x).isPerm l = true) (hat : ∀ a ∈ atoms, a.Holds rd σ) :
    σ x = (l.map σ).prod := by
  rw [mono_sound hat 40 x, (List.isPerm_iff.mp h).map σ |>.prod_eq]

/-- What a claim record establishes: the slot `e` below the log of `last · g`, the mark
`marks · g^j` at `region · g^e`, the four cells at `entries · g^(4e)`. -/
def ClaimAtSlot (rd : Reader) (region limit entries marks : E) (j e : ℕ) (cells : List E) : Prop :=
  SlotBelow limit e ∧ LoadHolds rd region e (marks * gen ^ j) ∧
    ∀ c < 4, LoadHolds rd entries (4 * e + c) (cells.getD c 0)

/-- A range check against `last` bounds the slot below the log of `last · g`. -/
theorem rc_last {rd : Reader} (hm : MemOk rd) {x y t1 t2 last : E}
    (h : LoadHolds rd x 0 t1 ∧ last = x * y ∧ LoadHolds rd y 0 t2) :
    ∃ e, x = gen ^ e ∧ SlotBelow (last * gen) e := by
  obtain ⟨e, e', he, he', hx, hk⟩ := rc_sound hm h
  exact ⟨e, hx, e + e' + 1, by omega, by rw [hk, ← pow_succ], by omega⟩

theorem claimOk_sound {rd : Reader} (hm : MemOk rd) {σ : Val} {atoms : List Atom} {P : ClaimVs}
    {j : ℕ} {o mark prev : V} {cells : List V} (h : claimOk atoms P j o mark prev cells = true)
    (hat : ∀ a ∈ atoms, a.Holds rd σ) (hprev : j ≠ 0 → σ prev = σ P.marks * gen ^ (j - 1)) :
    σ mark = σ P.marks * gen ^ j ∧ ∃ e, σ o = gen ^ e ∧
      ClaimAtSlot rd (σ P.region) (σ P.last * gen) (σ P.entries) (σ P.marks) j e (cells.map σ) := by
  simp only [claimOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hrc, hmk⟩, hld⟩, hlen⟩, hcells⟩ := h
  obtain ⟨y, t1, t2, h1, h2, h3⟩ := rcOf_sound hrc hat
  obtain ⟨e, he, hbl⟩ := rc_last hm ⟨h1, h2, h3⟩
  have hmark : σ mark = σ P.marks * gen ^ j := by
    by_cases h0 : j = 0
    · subst h0
      simp only [↓reduceIte, decide_eq_true_eq] at hmk
      rw [hmk, pow_zero, mul_one]
    · rw [ite_neg' h0] at hmk
      split at hmk
      · rename_i m c hmc
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hmk
        obtain ⟨rfl, hc⟩ := hmk
        rw [mulOf_sound hmc hat, const_sound hc hat, hprev h0, word_gen, mul_assoc, ← pow_succ,
          Nat.sub_add_cancel (by omega)]
      · exact absurd hmk (by simp)
  refine ⟨hmark, e, he, hbl, ?_, fun c hc => ?_⟩
  · split at hld
    · rename_i b off hb
      simp only [Bool.and_eq_true, beq_iff_eq] at hld
      obtain ⟨rfl, hperm⟩ := hld
      have := loadOf_sound hb hat
      rw [monoPerm_sound hperm hat, hmark] at this
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, he] at this
      rw [loadHolds_mul_gen_pow, Nat.add_zero] at this
      exact this
    · exact absurd hld (by simp)
  · have hc' := hcells c hc
    split at hc'
    · rename_i p off hp
      simp only [Bool.and_eq_true, beq_iff_eq] at hc'
      obtain ⟨rfl, hperm⟩ := hc'
      have := loadOf_sound hp hat
      rw [monoPerm_sound hperm hat] at this
      simp only [List.map_cons, List.map_replicate, List.prod_cons, List.prod_replicate] at this
      rw [he, ← pow_mul, mul_comm e 4] at this
      have := (loadHolds_mul_gen_pow rd _ _ _ _).mp this
      rw [List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem (by omega)]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)] at this
      exact this
    · exact absurd hc' (by simp)

/-! ## The records' layout -/

theorem ccWin_holds {rd : Reader} {σ : Val} {atoms : List Atom} (hat : ∀ a ∈ atoms, a.Holds rd σ)
    (p0 j : ℕ) : ∀ a ∈ ccWin atoms p0 j, a.Holds rd σ :=
  fun a ha => hat a (List.mem_of_mem_drop (List.mem_of_mem_take ha))

theorem records_marks {rd : Reader} (hm : MemOk rd) {σ : Val} {atoms : List Atom} {P : ClaimVs}
    {o0 p0 n : ℕ} (h : recordsOk atoms P o0 p0 n = true) (hat : ∀ a ∈ atoms, a.Holds rd σ) :
    ∀ j < n, σ (ccMark o0 P.marks j) = σ P.marks * gen ^ j := by
  simp only [recordsOk, List.all_eq_true, List.mem_range] at h
  intro j
  induction j with
  | zero => intro _; simp [ccMark]
  | succ j ih =>
    intro hj
    exact (claimOk_sound hm (h (j + 1) hj) (ccWin_holds hat _ _) (fun _ => by
      simpa using ih (by omega))).1

/-- **The records of `n` claims**: slots `o j`, the message's cells. -/
theorem records_sound {rd : Reader} (hm : MemOk rd) {σ : Val} {atoms : List Atom} {P : ClaimVs}
    {o0 p0 n : ℕ} (h : recordsOk atoms P o0 p0 n = true) (hat : ∀ a ∈ atoms, a.Holds rd σ) :
    ∃ os : List ℕ, os.length = n ∧ ∀ j < n,
      ClaimAtSlot rd (σ P.region) (σ P.last * gen) (σ P.entries) (σ P.marks) j
        (os.getD j 0) (((ccMsg o0 n).map (srcVal σ)).drop (4 * j)) := by
  have hmk := records_marks hm h hat
  simp only [recordsOk, List.all_eq_true, List.mem_range] at h
  have hex : ∀ j < n, ∃ e, ClaimAtSlot rd (σ P.region) (σ P.last * gen) (σ P.entries)
      (σ P.marks) j e ((ccCells o0 j).map σ) := fun j hj => by
    obtain ⟨-, e, -, he⟩ := claimOk_sound hm (h j hj) (ccWin_holds hat _ _) (fun h0 => by
      simpa using hmk (j - 1) (by omega))
    exact ⟨e, he⟩
  classical
  refine ⟨(List.range n).map fun j => if hj : j < n then Classical.choose (hex j hj) else 0,
    by simp, fun j hj => ?_⟩
  have hs := Classical.choose_spec (hex j hj)
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
  simp only [Option.map_some, Option.getD_some, hj, ↓reduceDIte]
  refine ⟨hs.1, hs.2.1, fun c hc => ?_⟩
  have := hs.2.2 c hc
  have e1 : (((ccMsg o0 n).map (srcVal σ)).drop (4 * j)).getD c 0 = σ (.n (ccCell o0 j c)) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_drop, List.getElem?_map, ccMsg, List.getElem?_map,
      List.getElem?_range (by omega)]
    simp only [Option.map_some, Option.getD_some, srcVal]
    rw [show (4 * j + c) / 4 = j by omega, show (4 * j + c) % 4 = c by omega]
  have e2 : ((ccCells o0 j).map σ).getD c 0 = σ (.n (ccCell o0 j c)) := by
    simp [ccCells, List.getD_eq_getElem?_getD, hc]
  rw [e1, ← e2]
  exact this

end
end LeanVM.Guest.B1.Digest

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Records over several claims -/

/-- The records of `n` claims: slot `o j`, the mark `marks · g^j`, four cells each. -/
def ClaimsAt (rd : Reader) (region limit entries marks : E) (n : ℕ) (os : List ℕ)
    (cells : List E) : Prop :=
  os.length = n ∧ cells.length = 4 * n ∧
    ∀ j < n, ClaimAtSlot rd region limit entries marks j (os.getD j 0) (cells.drop (4 * j))

theorem getD_drop' {α : Type} (l : List α) (a c : ℕ) (d : α) :
    (l.drop a).getD c d = l.getD (a + c) d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_drop, ← List.getD_eq_getElem?_getD]

theorem getD_append_left'' {α : Type} (l l' : List α) {i : ℕ} (d : α) (h : i < l.length) :
    (l ++ l').getD i d = l.getD i d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h, ← List.getD_eq_getElem?_getD]

theorem getD_append_right'' {α : Type} (l l' : List α) {i : ℕ} (d : α) (h : l.length ≤ i) :
    (l ++ l').getD i d = l'.getD (i - l.length) d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right h, ← List.getD_eq_getElem?_getD]

theorem claimsAt_append {rd : Reader} {region limit entries base : E} {m k : ℕ}
    {os os' : List ℕ} {cs cs' : List E} (h : ClaimsAt rd region limit entries base m os cs)
    (h' : ClaimsAt rd region limit entries (base * gen ^ m) k os' cs') :
    ClaimsAt rd region limit entries base (m + k) (os ++ os') (cs ++ cs') := by
  obtain ⟨hl, hcl, hc⟩ := h
  obtain ⟨hl', hcl', hc'⟩ := h'
  refine ⟨by rw [List.length_append, hl, hl'], by rw [List.length_append, hcl, hcl']; ring,
    fun j hj => ?_⟩
  by_cases hjm : j < m
  · obtain ⟨h1, h2, h3⟩ := hc j hjm
    have hos : (os ++ os').getD j 0 = os.getD j 0 := getD_append_left'' _ _ _ (by omega)
    refine ⟨by rw [hos]; exact h1, by rw [hos]; exact h2, fun c hcc => ?_⟩
    rw [hos, getD_drop', getD_append_left'' _ _ _ (by omega)]
    have := h3 c hcc
    rwa [getD_drop'] at this
  · obtain ⟨h1, h2, h3⟩ := hc' (j - m) (by omega)
    have hos : (os ++ os').getD j 0 = os'.getD (j - m) 0 := by
      rw [getD_append_right'' _ _ _ (by omega), hl]
    refine ⟨by rw [hos]; exact h1, ?_, fun c hcc => ?_⟩
    · have hb : base * gen ^ j = base * gen ^ m * gen ^ (j - m) := by
        rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' (by omega)]
      rw [hos, hb]
      exact h2
    · rw [hos, getD_drop', getD_append_right'' _ _ _ (by omega), hcl,
        show 4 * j + c - 4 * m = 4 * (j - m) + c by omega]
      have := h3 c hcc
      rwa [getD_drop'] at this

theorem length_ccMsg (o0 n : ℕ) : (ccMsg o0 n).length = 4 * n := by simp [ccMsg]

theorem getD_map_range {α : Type} (f : ℕ → α) {n c : ℕ} (h : c < n) (d : α) :
    ((List.range n).map f).getD c d = f c := by
  simp [List.getD_eq_getElem?_getD, h]

/-! ## `child_claim_list_last__L{k}` -/


set_option maxRecDepth 100000 in
theorem ccl_idx : ∀ k < 17, coreProgram.indexOf? (cclNames.getD k "") = some (344 + k) := by
  decide +kernel

/-- **`child_claim_list_last__L{k}`**: from a state at its first argument after whole blocks
`pre`, `k` claims read at hinted slots and marked, and the digest of `pre ++` their cells. -/
theorem childLast_sound {rd : Reader} (hm : MemOk rd) {k : ℕ} (hk : k < 17) {args rets : List E}
    (h : coreProgram.Rel rd (cclNames.getD k "") args rets) :
    ∃ sp entries region marks last, args = [sp, entries, region, marks, last] ∧
      ∀ (n : ℕ) (pre : List UInt8), pre.length = rate * n →
      StateAt rd sp 0 (absorbChunks n zeroState pre) →
      ∃ (os : List ℕ) (cells : List E), ClaimsAt rd region (last * gen) entries marks k os cells ∧
        AllCanonical cells ∧ rets = digestCells (keccak256 (pre ++ cellsBytes cells)) := by
  have hf := find_of_idx (ccl_idx k hk) (by rw [coreProgram_length]; omega)
  obtain ⟨σ, hp, hb⟩ := (rel_iff_sem hf args rets).mp h
  have hok := ccl_all k hk
  set f := coreProgram.getD (344 + k) default
  simp only [cclOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hpar, hok⟩ := hok
  rw [hpar] at hp
  refine ⟨σ (V.n 0), σ (V.n 1), σ (V.n 2), σ (V.n 3), σ (V.n 4), by rw [← hp]; rfl,
    fun n pre hpre hS => ?_⟩
  split at hok
  · rename_i atoms r0 r1 hsb
    simp only [Bool.and_eq_true] at hok
    obtain ⟨⟨⟨hc, hr⟩, hrec⟩, hst⟩ := hok
    rw [splitBody_eq hsb, holdsList_atoms_ret] at hb
    obtain ⟨hat, hret⟩ := hb
    obtain ⟨hd, hcan⟩ := chain_final hc rfl hat hpre (initCell_of_loads rfl hst hat hS)
    obtain ⟨os, hos, hcl⟩ := records_sound hm hrec hat
    have hlen : ((cclSpec k atoms).vals σ).length = 4 * k := by
      simp [ChainSpec.vals, cclSpec, length_ccMsg]
    have htake : ((cclSpec k atoms).vals σ).take ((cclSpec k atoms).len / 16) =
        (cclSpec k atoms).vals σ := by
      rw [List.take_of_length_le]
      rw [hlen]; simp only [cclSpec]; omega
    rw [htake] at hd hcan
    simp only [retOk, Bool.and_eq_true] at hr
    refine ⟨os, (cclSpec k atoms).vals σ, ⟨hos, hlen, hcl⟩, hcan, ?_⟩
    rw [← hret, List.map_cons, List.map_cons, List.map_nil, copy_sound hr.1 hat,
      copy_sound hr.2 hat, digestCells, ← hd]
  · exact absurd hok (by simp)

/-! ## The frame loops of child claims: `m` claims a frame -/

-- `__loop17`: 136 claims a frame, 64 blocks.
set_option maxRecDepth 100000 in
theorem any136_nb : (anySpec 136 22 1924 (loopAtoms (coreProgram.getD 342 default))).nb = 64 := by
  decide +kernel

-- its head here, its sixteen windows in `ChildListAny{q}`.
set_option maxRecDepth 100000 in
theorem any136_head : anyHead (coreProgram.getD 342 default) "__loop17" 136 22 21 1924 = true := by
  decide +kernel

theorem any136_ok : anyOk (coreProgram.getD 342 default) "__loop17" 136 22 15 21 1924 = true := by
  have hw : ∀ i < 16, anyWin i = true := by
    intro i hi
    interval_cases i
    exacts [anyWin_0, anyWin_1, anyWin_2, anyWin_3, anyWin_4, anyWin_5, anyWin_6, anyWin_7,
      anyWin_8, anyWin_9, anyWin_10, anyWin_11, anyWin_12, anyWin_13, anyWin_14, anyWin_15]
  simp only [anyWin, any136Spec, any136Atoms, Bool.and_eq_true] at hw
  exact anyOk_of_parts (w := 4) (W := 16) (v := 9) (U := 16) any136_head (by rw [any136_nb])
    (fun i hi => (hw i hi).1) (by norm_num) (fun i hi => (hw i hi).2)

set_option maxRecDepth 100000 in
theorem any136_idx : coreProgram.indexOf? "__loop17" = some 342 := by decide +kernel


-- `__loop18`: 17 claims a frame, 8 blocks.
set_option maxRecDepth 100000 in
theorem any17_ok : anyOk (coreProgram.getD 343 default) "__loop18" 17 19 12 18 255 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem any17_idx : coreProgram.indexOf? "__loop18" = some 343 := by decide +kernel

set_option maxRecDepth 100000 in
theorem any17_nb : (anySpec 17 19 255 (loopAtoms (coreProgram.getD 343 default))).nb = 8 := by
  decide +kernel

/-- **One frame of `m` child claims, `nb` blocks**: from the state at `chain · x^13` after whole
blocks `pre`, `m` claims read at hinted slots and marked `base · x^m · g^j`, absorbed, the state
written at `chain · x^13 · g^13`. -/
def ChildGroupStep (rd : Reader) (m nb : ℕ) (chain entries region base limit x : E) : Prop :=
  ∀ (n : ℕ) (pre : List UInt8), pre.length = rate * n →
    StateAt rd (chain * x ^ 13) 0 (absorbChunks n zeroState pre) →
    ∃ (os : List ℕ) (cells : List E),
      ClaimsAt rd region limit entries (base * x ^ m) m os cells ∧ AllCanonical cells ∧
      StateAt rd (chain * x ^ 13) 13 (absorbChunks (n + nb) zeroState (pre ++ cellsBytes cells))

theorem any_step {rd : Reader} (hm : MemOk rd) {f : String} {j m o0 p0 mk st0 nb : ℕ}
    (hidx : coreProgram.indexOf? f = some j) (hj : j < 1752)
    (hok : anyOk (coreProgram.getD j default) f m o0 p0 mk st0 = true)
    (hnb : (anySpec m o0 st0 (loopAtoms (coreProgram.getD j default))).nb = nb)
    {x : E} {ps : List E} (h : coreProgram.Rel rd f (x :: ps) []) :
    (∀ N chain entries region base last, ps = [N, chain, entries, region, base, last] →
      ChildGroupStep rd m nb chain entries region base (last * gen) x) ∧
      (x * gen + ps.headD 0 ≠ 0 → coreProgram.Rel rd f (x * gen :: ps) []) := by
  have hf := find_of_idx hidx (by rw [coreProgram_length]; omega)
  simp only [anyOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨hshape, hlen7⟩, hc⟩, hst⟩, hrec⟩, hout⟩, hm12⟩, hmk⟩ := hok
  obtain ⟨σ, hx, hps, hat, hnext⟩ := loop_step hf hshape h
  refine ⟨fun N chain entries region base last hN n pre hpre hS => ?_, hnext⟩
  have hpar : (coreProgram.getD j default).params =
      [V.n 0, V.n 1, V.n 2, V.n 3, V.n 4, V.n 5, V.n 6] := by
    have hs := hshape
    simp only [loopShape, Bool.and_eq_true, decide_eq_true_eq] at hs
    rw [hs.1.2, hlen7]; rfl
  rw [hpar, hN] at hps
  simp only [List.tail_cons, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hps
  obtain ⟨-, hchain, hentries, hregion, hbase, hlast⟩ := hps
  have h12 : σ (V.n 12) = chain * x ^ 13 := by rw [monoIs_sound hm12 hat, hchain, hx]
  have hmkv : σ (V.n mk) = base * x ^ m := by rw [monoIs_sound hmk hat, hbase, hx]
  rw [← h12] at hS
  obtain ⟨hw, -, hcan⟩ := chain_whole hc rfl hat hpre (initCell_of_loads rfl hst hat hS)
  obtain ⟨os, hos, hcl⟩ := records_sound hm hrec hat
  have hlen : ((anySpec m o0 st0 (loopAtoms (coreProgram.getD j default))).vals σ).length =
      4 * m := by
    simp [ChainSpec.vals, anySpec, length_ccMsg]
  refine ⟨os, _, ⟨hos, hlen, ?_⟩, hcan, fun c => ?_⟩
  · intro i hi
    have := hcl i hi
    simp only [anyP] at this
    rwa [hregion, hlast, hentries, hmkv] at this
  · have hout' := stLoads_sound hout hat c
    have hw' := hw c
    rw [hnb] at hw' hout'
    rw [getD_map_range _ c.isLt, hw', h12] at hout'
    exact hout'

end
end LeanVM.Guest.B1.Digest

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The frames of child claims, by induction -/

/-- **The frames**: after `q ≤ a` frames of `m` child claims (`nb` blocks each), the state at
`chain · g^(13q)` is the sponge after their `4mq` cells, read at the slots of `ClaimsAt`. -/
theorem childGroups_sound {rd : Reader} {m nb : ℕ} (hmn : 64 * m = 136 * nb)
    {chain entries region base limit : E} {a n0 : ℕ} {pre : List UInt8}
    (hpre0 : pre.length = rate * n0) (h0 : StateAt rd chain 0 (absorbChunks n0 zeroState pre))
    (hstep : ∀ q < a, ChildGroupStep rd m nb chain entries region base limit (gen ^ q)) :
    ∀ q ≤ a, ∃ (os : List ℕ) (cells : List E),
      ClaimsAt rd region limit entries base (m * q) os cells ∧ AllCanonical cells ∧
      StateAt rd (chain * gen ^ (13 * q)) 0
        (absorbChunks (n0 + nb * q) zeroState (pre ++ cellsBytes cells)) := by
  intro q
  induction q with
  | zero =>
    intro _
    refine ⟨[], [], ⟨rfl, rfl, fun j hj => absurd hj (by omega)⟩, fun _ h => absurd h (by simp), ?_⟩
    simpa using h0
  | succ q ih =>
    intro hq
    obtain ⟨os, cells, hcl, hcan, hS⟩ := ih (by omega)
    have hpre : (pre ++ cellsBytes cells).length = rate * (n0 + nb * q) := by
      rw [List.length_append, length_cellsBytes, hcl.2.1, hpre0]
      show 136 * n0 + 16 * (4 * (m * q)) = 136 * (n0 + nb * q)
      have : 16 * (4 * (m * q)) = (64 * m) * q := by ring
      rw [this, hmn]; ring
    rw [show chain * gen ^ (13 * q) = chain * (gen ^ q) ^ 13 by rw [gen_pow_pow]] at hS
    obtain ⟨os2, c2, hcl2, hcan2, hS2⟩ := hstep q (by omega) _ _ hpre hS
    rw [gen_pow_pow] at hcl2
    refine ⟨os ++ os2, cells ++ c2, ?_, ?_, ?_⟩
    · rw [show m * (q + 1) = m * q + m by ring]
      exact claimsAt_append hcl (by rwa [show m * q = m * q from rfl])
    · intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · exact hcan c hc
      · exact hcan2 c hc
    · intro c
      have := hS2 c
      rw [gen_pow_pow, loadHolds_mul_gen_pow] at this
      rw [loadHolds_mul_gen_pow, cellsBytes_append, ← List.append_assoc,
        show 13 * (q + 1) + (0 + c.val) = 13 * q + (13 + c.val) by ring,
        show n0 + nb * (q + 1) = n0 + nb * q + nb by ring]
      exact this

/-- **A loop of frames of `m` child claims**, called as
`callIf (1 + N) f [1, N, chain, entries, region, base, last]` with `N = g^a`, `a < 2^34`. -/
theorem childFrames_of_loop {rd : Reader} (hm : MemOk rd) {f : String} {j m o0 p0 mk st0 nb : ℕ}
    (hidx : coreProgram.indexOf? f = some j) (hj : j < 1752)
    (hok : anyOk (coreProgram.getD j default) f m o0 p0 mk st0 = true)
    (hnb : (anySpec m o0 st0 (loopAtoms (coreProgram.getD j default))).nb = nb)
    {N chain entries region base last : E} {a : ℕ} (ha : a < 2 ^ 34) (hN : N = gen ^ a)
    (hloop : 1 + N ≠ 0 → coreProgram.Rel rd f [1, N, chain, entries, region, base, last] []) :
    ∀ q < a, ChildGroupStep rd m nb chain entries region base (last * gen) (gen ^ q) :=
  loop_sound (f := f) (ps := [N, chain, entries, region, base, last]) (N := N)
    (B := ChildGroupStep rd m nb chain entries region base (last * gen)) (by unfold ordG; omega) hN
    (fun x hx => by
      obtain ⟨h1, h2⟩ := any_step hm hidx hj hok hnb hx
      exact ⟨h1 _ _ _ _ _ _ rfl, h2⟩)
    hloop

/-! ## `child_claim_list_any` -/

/-- `child_claim_list_any`'s body before its `ret`. -/
noncomputable def anyFlat : List Stmt := (Fn.body Data.core25).dropLast

set_option maxRecDepth 100000 in
theorem core25_shape : Fn.body Data.core25 = anyFlat ++ [.ret [.n 66, .n 67]] :=
  stmtsEqb_sound (by decide +kernel)

/-- The body: `limit = last · g`, the zero state at `chain = .n 17`, the big frames' loop,
`mid = chain · bigs^13`, `mid_base = base · bigs^136`, the groups' loop, `last = mid · groups^13`,
the marks `mid_base · groups^17`, the dispatch on the rest. -/
noncomputable def anyBodyOk : Bool :=
  anyFlat.all Stmt.flat &&
  anyFlat.any (stmtEqb · (.callIf (.n 32) "__loop17" [.n 33, .n 4, .n 17, .n 0, .n 1, .n 2, .n 8])) &&
  anyFlat.any (stmtEqb · (.callIf (.n 50) "__loop18" [.n 51, .n 5, .n 39, .n 0, .n 1, .n 48, .n 8])) &&
  anyFlat.any (stmtEqb · (.dispatch (.n 6) cclNames [.n 57, .n 0, .n 1, .n 63, .n 8] [.n 64, .n 65])) &&
  genMulOk (atomsIn anyFlat) (.n 3) (.n 8) &&
  (atomsIn anyFlat).any (isConstAt (.n 33) 1 0) &&
  (atomsIn anyFlat).any (isAddAt (.n 32) (.n 31) (.n 4)) &&
  (atomsIn anyFlat).any (isConstAt (.n 31) 1 0) &&
  (atomsIn anyFlat).any (isConstAt (.n 51) 1 0) &&
  (atomsIn anyFlat).any (isAddAt (.n 50) (.n 49) (.n 5)) &&
  (atomsIn anyFlat).any (isConstAt (.n 49) 1 0) &&
  (List.range 13).all (fun c => (atomsIn anyFlat).any (isLoadAt (.n (18 + c)) (.n 17) c) &&
    (atomsIn anyFlat).any (isConstAt (.n (18 + c)) 0 0)) &&
  monoIs (atomsIn anyFlat) (.n 39) (.n 17) (.n 4) 13 &&
  monoIs (atomsIn anyFlat) (.n 48) (.n 2) (.n 4) 136 &&
  mono2Is (atomsIn anyFlat) (.n 57) (.n 17) (.n 4) 13 (.n 5) 13 &&
  mono2Is (atomsIn anyFlat) (.n 63) (.n 2) (.n 4) 136 (.n 5) 17 &&
  (atomsIn anyFlat).any (isCopyAt (.n 66) (.n 64)) &&
  (atomsIn anyFlat).any (isCopyAt (.n 67) (.n 65))

set_option maxRecDepth 100000 in
theorem anyBody_ok : anyBodyOk = true := by decide +kernel

theorem find_child_claim_list_any :
    coreProgram.find? "child_claim_list_any" = some Data.core25 :=
  Program.find?_of_indexOf? (j := 25) (by decide +kernel) rfl

/-- **`child_claim_list_any`** (G:4210-4230): on `bigs = g^a`, `groups = g^b`, `rest = g^c`, the
`136a + 17b + c` claims read at hinted slots of the region below the log of `limit`, marked
`base · g^j`, and their digest. -/
theorem child_claim_list_any_sound {rd : Reader} (hm : MemOk rd) {args rets : List E}
    (h : coreProgram.Rel rd "child_claim_list_any" args rets) :
    ∃ entries region base limit bigs groups rest,
      args = [entries, region, base, limit, bigs, groups, rest] ∧
      ∀ a b c, a < 2 ^ 32 → b < 8 → c < 17 → bigs = gen ^ a → groups = gen ^ b → rest = gen ^ c →
        ∃ (os : List ℕ) (cells : List E),
          ClaimsAt rd region limit entries base (136 * a + 17 * b + c) os cells ∧
          AllCanonical cells ∧ rets = digestCells (keccak256 (cellsBytes cells)) := by
  obtain ⟨σ, hp, hb⟩ := (rel_iff_sem find_child_claim_list_any args rets).mp h
  refine ⟨σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 6),
    by rw [← hp]; rfl, fun a b c ha hb' hc h4 h5 h6 => ?_⟩
  rw [core25_shape, holdsList_append] at hb
  have hok := anyBody_ok
  simp only [anyBodyOk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hfl, hl17⟩, hl18⟩, hdis⟩, h3⟩, h33⟩, h32⟩, h31⟩, h51⟩, h50⟩, h49⟩,
    hzs⟩, hm39⟩, hm48⟩, hm57⟩, hm63⟩, hc66⟩, hc67⟩ := hok
  obtain ⟨hall, hret⟩ := holdsList_flat _ (List.all_eq_true.mpr hfl) _ _ hb
  simp only [Stmt.HoldsList, Stmt.Holds, List.map_cons, List.map_nil] at hret
  have hat := atoms_of_flat hall
  have hlim : σ (.n 3) = σ (.n 8) * gen := genMul_sound h3 hat
  -- the zero state
  have h0 : StateAt rd (σ (.n 17)) 0 (absorbChunks 0 zeroState []) := by
    intro c
    have hl := load_sound (hzs c c.isLt).1 hat
    rw [const_sound (hzs c c.isLt).2 hat, word_zero] at hl
    rw [Nat.zero_add, absorbChunks, cellsOfState_zero]
    exact hl
  -- the big frames
  have hbig := childFrames_of_loop hm any136_idx (by norm_num) any136_ok any136_nb
    (chain := σ (.n 17)) (entries := σ (.n 0)) (region := σ (.n 1)) (base := σ (.n 2))
    (last := σ (.n 8)) (by omega) h4 (fun hne => by
      have := (callIf_of_flat hall hl17).2
        (by rw [add_sound h32 hat, const_sound h31 hat, word_one]; exact hne)
      simpa [const_sound h33 hat, word_one] using this)
  obtain ⟨osa, ca, hcla, hcana, hSa⟩ := childGroups_sound (by norm_num) (n0 := 0) (pre := []) rfl h0
    hbig a le_rfl
  -- the groups
  have h39 : σ (.n 39) = σ (.n 17) * gen ^ (13 * a) := by
    rw [monoIs_sound hm39 hat, h4, gen_pow_pow]
  have h48 : σ (.n 48) = σ (.n 2) * gen ^ (136 * a) := by
    rw [monoIs_sound hm48 hat, h4, gen_pow_pow]
  have hgrp := childFrames_of_loop hm any17_idx (by norm_num) any17_ok any17_nb
    (chain := σ (.n 39)) (entries := σ (.n 0)) (region := σ (.n 1)) (base := σ (.n 48))
    (last := σ (.n 8)) (by omega) h5 (fun hne => by
      have := (callIf_of_flat hall hl18).2
        (by rw [add_sound h50 hat, const_sound h49 hat, word_one]; exact hne)
      simpa [const_sound h51 hat, word_one] using this)
  have hpa : ([] ++ cellsBytes ca).length = rate * (0 + 64 * a) := by
    rw [List.nil_append, length_cellsBytes, hcla.2.1]; show 16 * (4 * (136 * a)) = 136 * (0 + 64 * a)
    ring
  obtain ⟨osb, cb, hclb, hcanb, hSb⟩ := childGroups_sound (by norm_num) hpa
    (by rw [h39]; exact hSa) hgrp b le_rfl
  -- the rest
  obtain ⟨j, hj, hsel, hcall⟩ := dispatch_of_flat hall hdis
  have hj17 : j < 17 := hj
  have hjc : j = c := by
    rw [h6, gen_pow_eq_ofK] at hsel
    exact (gpow_injOn (by simp only [Set.mem_Iio]; omega) (by simp only [Set.mem_Iio]; omega)
      (ofK_injective hsel)).symm
  subst hjc
  rw [show cclNames[j] = cclNames.getD j "" by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl] at hcall
  obtain ⟨sp, ent, reg, mk, lst, hargs, hlast⟩ := childLast_sound hm hj17 hcall
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hargs
  obtain ⟨hsp, hent, hreg, hmk, hlst⟩ := hargs
  have h57 : σ (.n 57) = σ (.n 39) * gen ^ (13 * b) := by
    rw [mono2Is_sound hm57 hat, h39, h4, h5]; simp only [gen_pow_pow]
  have h63 : σ (.n 63) = σ (.n 48) * gen ^ (17 * b) := by
    rw [mono2Is_sound hm63 hat, h48, h4, h5]; simp only [gen_pow_pow]
  have hpre : ([] ++ cellsBytes ca ++ cellsBytes cb).length = rate * (0 + 64 * a + 8 * b) := by
    rw [List.length_append, List.nil_append, length_cellsBytes, length_cellsBytes, hcla.2.1,
      hclb.2.1]
    show 16 * (4 * (136 * a)) + 16 * (4 * (17 * b)) = 136 * (0 + 64 * a + 8 * b)
    ring
  obtain ⟨osc, cc, hclc, hcanc, hd⟩ := hlast _ _ hpre (by rw [← hsp, h57]; exact hSb)
  rw [← hent, ← hreg, ← hmk, ← hlst, h63, h48, mul_assoc, ← pow_add] at hclc
  rw [h48] at hclb
  rw [← hlim] at hcla hclb hclc
  refine ⟨osa ++ osb ++ osc, ca ++ cb ++ cc, ?_, ?_, ?_⟩
  · exact claimsAt_append (claimsAt_append hcla hclb) hclc
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · rcases List.mem_append.mp hx with hx | hx
      · exact hcana x hx
      · exact hcanb x hx
    · exact hcanc x hx
  · simp only [List.map_cons, List.map_nil] at hd
    rw [← hret, copy_sound hc66 hat, copy_sound hc67 hat, hd, cellsBytes_append,
      cellsBytes_append]
    simp

end
end LeanVM.Guest.B1.Digest
