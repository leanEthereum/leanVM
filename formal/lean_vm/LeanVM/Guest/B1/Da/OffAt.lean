/-
  LeanVM.Guest.B1.Da.OffAt

  `da_column_offsets` placed (G:4445-4460): its `HeapBuf`s (the offsets, each bit's steps), its
  seven doubling loops, the offsets returned, within its frame, its buffers and its loops' static
  bounds.
-/

module

public import LeanVM.Guest.B1.Da.OffCChk
public import LeanVM.Guest.B1.Da.OffLoopsComplete
public import LeanVM.Guest.B1.Da.HonestDefs
public import LeanVM.Guest.B1.Da.KidsMap
public import LeanVM.Guest.B1.Da.AtTB
public import LeanVM.Guest.B1.Tables.FlatAtT

/-!
# `da_column_offsets`, placed

The buffers at `b0 = fp + fs f`: the offsets (`offCells Z`, `1024` words), then bit `b`'s steps
(`stepCells Z b`) at `b0 + 1024 + 8 b`. `offLoop_rel`: bit `b`'s loop runs to its end on them
(`off_block`, `wK_two_pow_add`). The body is evaluated (`Fwd.ev`); its loads read `zs`, its stores
find the zeros and the steps. `off_completeAtB`: complete, placed, within its frame, its buffers
and `offKB fs SK`, its loops' `2^b` iterations each and their runs' phantom frames, returning
the offsets (`offOut`).
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen eOfNat)
open LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Digest
open LeanVM.Guest.B1 (CompleteAtDTB completeAt_flatOutDTB flatCalls flatMap_loadsEv Kid Returns)
open LeanVM.Guest.B1.Main (Layout MemL RegionL iterK)

@[expose] public section

/-- `da_column_offsets`' `HeapBuf`s' sizes. -/
def offSizes : List ℕ := [1024, 8, 8, 8, 8, 8, 8, 8]

/-- Their honest words: the offsets, each bit's steps. -/
def offOwn (Z : ℕ → E) : List (List E) := offCells Z :: (List.range 7).map (stepCells Z)

/-- Bit `b`'s loop, on the offsets at `b0` and its steps after them. -/
def offKid (Z : ℕ → E) (b0 b : ℕ) : Kid :=
  ⟨offLoopName b, true, [1, gen ^ 2 ^ b, gen ^ b0, gen ^ (b0 + 1024 + 8 * b)],
    [(b0, offCells Z), (b0 + 1024 + 8 * b, stepCells Z b)], Returns []⟩

/-- **The loops' words bound**: bit `b`'s `2^b` iterations and its run's phantom frame. -/
def offKB (fs SK : String → ℕ) : ℕ :=
  ((List.range 7).map fun b => 2 ^ b * iterK fs SK (offLoopName b) + fs (offLoopName b)).sum

theorem bufL_off (Z : ℕ → E) (b0 : ℕ) : bufL b0 offSizes (offOwn Z) =
    (b0, offCells Z) :: (List.range 7).map fun b => (b0 + 1024 + 8 * b, stepCells Z b) := by
  simp [bufL, bases, offSizes, offOwn, List.range_succ, Nat.add_assoc]

theorem offCells_get {Z : ℕ → E} {k : ℕ} (hk : k < 1024) :
    (offCells Z)[k]'(by simp [offCells]; exact hk) = Z (k % 8) * ofK (wK (k % 8) (256 * (k / 8))) := by
  simp [offCells]

theorem stepCells_get {Z : ℕ → E} {b j : ℕ} (hj : j < 8) :
    (stepCells Z b)[j]'(by simp [stepCells]; exact hj) = Z j * ofK (wK j (2 ^ (8 + b))) := by
  simp [stepCells]

theorem pow8_eq (j : ℕ) : gen ^ j * gen ^ j * (gen ^ j * gen ^ j) * (gen ^ j * gen ^ j * (gen ^ j * gen ^ j)) =
    gen ^ (8 * j) := by
  rw [show 8 * j = j + j + (j + j) + (j + j + (j + j)) by ring]
  simp only [pow_add]

variable {rd : Reader}

/-- **Bit `b`'s loop runs to its end** on the honest offsets and steps. -/
theorem offLoop_rel {b : ℕ} (hb : b < 7) {Z : ℕ → E} {b0 bs : ℕ}
    (h1 : ReadsAt rd (gen ^ b0) (offCells Z)) (h2 : ReadsAt rd (gen ^ bs) (stepCells Z b)) :
    coreProgram.Rel rd (offLoopName b) [1, gen ^ 2 ^ b, gen ^ b0, gen ^ bs] [] := by
  have hok := offLoop_ok b hb
  simp only [offLoopOk, Bool.and_eq_true] at hok
  have hb64 : 2 ^ b ≤ 64 :=
    le_trans (Nat.pow_le_pow_right (n := 2) (by norm_num) (show b ≤ 6 by omega)) (by norm_num)
  have hblk : ∀ j < 2 ^ b, Digest.LoopBlock rd (coreProgram.getD (423 + b) default) (gen ^ j)
      (gen ^ 2 ^ b) [gen ^ b0, gen ^ bs] := by
    intro j hj
    have hl : ∀ i < 8, 8 * j + i < 1024 := fun i hi => by omega
    have hl' : ∀ i < 8, 8 * j + (8 * 2 ^ b + i) < 1024 := fun i hi => by omega
    refine off_block hb (fun i => Z i * ofK (wK i (256 * j)))
      (fun i => Z i * ofK (wK i (2 ^ (8 + b)))) (fun i hi => ?_) (fun i hi => ?_) (fun i hi => ?_)
    · rw [pow8_eq, loadHolds_mul_gen_pow]
      have := h1 (8 * j + i) (by simp [offCells]; exact hl i hi)
      rwa [offCells_get (hl i hi), show (8 * j + i) % 8 = i by omega,
        show (8 * j + i) / 8 = j by omega] at this
    · have := h2 i (by simp [stepCells]; exact hi)
      rwa [stepCells_get hi] at this
    · rw [pow8_eq, loadHolds_mul_gen_pow]
      have := h1 (8 * j + (8 * 2 ^ b + i)) (by simp [offCells]; exact hl' i hi)
      rw [offCells_get (hl' i hi), show (8 * j + (8 * 2 ^ b + i)) % 8 = i by omega,
        show (8 * j + (8 * 2 ^ b + i)) / 8 = j + 2 ^ b by omega] at this
      have hw : wK i (256 * (j + 2 ^ b)) = wK i (256 * j) + wK i (2 ^ (8 + b)) := by
        rw [show 256 * (j + 2 ^ b) = 2 ^ (8 + b) + 256 * j by rw [pow_add]; ring]
        exact wK_two_pow_add i (by rw [pow_add]; omega)
      rwa [hw, ofK_add, mul_add] at this
  have := loopF_complete (find_off hb) hok.1.1 (N := gen ^ 2 ^ b) (rest := [gen ^ b0, gen ^ bs])
    (m := 2 ^ b) rfl hblk 0 (Nat.two_pow_pos b)
  rwa [pow_zero] at this

theorem isOffLoad_spec {d p : V} {off : ℕ} (h : isOffLoad d p off = true) :
    off < 8 ∧ ((p = .n 1 ∧ d = .n (2 + off)) ∨ (p = .n 0 ∧ ∃ b < 7, d = .n (offB b + 1 + 3 * off)) ∨
      ∃ b < 7, p = .n (offB b) ∧ d = .n (offB b + 1 + 3 * off + 2)) := by
  simp only [isOffLoad, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true,
    List.mem_range] at h
  obtain ⟨h0, (h | h) | h⟩ := h
  · exact ⟨h0, Or.inl h⟩
  · exact ⟨h0, Or.inr (Or.inl h)⟩
  · obtain ⟨b, hb, h1, h2⟩ := h
    exact ⟨h0, Or.inr (Or.inr ⟨b, hb, h1, h2⟩)⟩

theorem isOffStmt_spec {s : Stmt} (h : isOffStmt s = true) :
    (∃ a, s = .atom a) ∨ ∃ b < 7, s = offCallS b := by
  cases s with
  | atom a => exact Or.inl ⟨a, rfl⟩
  | _ =>
    simp only [isOffStmt, List.any_eq_true, List.mem_range] at h
    obtain ⟨b, hb, h⟩ := h
    have := stmtsEqb_sound h
    simp only [List.cons.injEq, and_true] at this
    exact Or.inr ⟨b, hb, this⟩

variable (fs : String → ℕ) (cert : String → V → ℕ)

set_option maxRecDepth 4000 in
/-- **`da_column_offsets` is complete, placed, within its frame, its buffers and `offKB fs SK`**,
returning its offsets, the powers `Z` read at `g^c`. -/
theorem off_completeAtB {Lin : Layout} {c : ℕ} {Z : ℕ → E}
    (hzs : ∀ rd, MemL rd Lin → ∀ j < 8, LoadHolds rd (gen ^ c) j (Z j))
    (hzr : ∀ j < 8, RegionL Lin (c + j)) {SK : String → ℕ}
    (hT : ∀ b < 7, TotalLeOn coreProgram fs (offLoopName b) LoopPre
      (fun a => logG (a.getD 1 0) * iterK fs SK (offLoopName b) + fs (offLoopName b))) :
    CompleteAtDTB fs cert 16 "da_column_offsets" Lin [gen ^ c] (offOut Z) (fun _ => True)
      (fs "da_column_offsets" + 1080 + offKB fs SK) := by
  have hok := off_ok
  unfold offOk at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hok
  obtain ⟨⟨⟨hparams, hbody⟩, -⟩, hN⟩ := hok
  have hb := stmtsEqb_sound hbody
  have hcok := off_cok
  unfold offCOk at hcok
  simp only [Bool.and_eq_true, decide_eq_true_eq, Option.isSome_iff_exists] at hcok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c', hchk⟩, hst⟩, hside⟩, hloads⟩, hstmts⟩, hflat⟩, haddr⟩, halloc⟩,
    hcalls⟩, hnli⟩ := hcok
  have hS := atomsEqb_sound hst
  have hNb : ∀ b < 7, word (offN b) 0 = gen ^ 2 ^ b := fun b hb' => by
    rw [word_eOfNat, eOfNat, hN b hb', gen_pow_eq_ofK]
  have hKB : ((List.range 7).map fun b => 2 ^ b * iterK fs SK (offLoopName b) +
      fs (offLoopName b)).sum = offKB fs SK := rfl
  rw [show 1080 = offSizes.sum from rfl, ← hKB]
  refine (completeAt_flatOutDTB (fs := fs) (cert := cert) find_da_column_offsets
    (by rw [Program.loop_of_find? find_da_column_offsets]; decide +kernel) 16 Lin [gen ^ c]
    (fun fp ↦ [ofK (addressOfIndex (fp + fs "da_column_offsets"))]) (offOut Z) hb hflat haddr
    offSizes (fun _ ↦ offOwn Z) (fun _ ↦ .cons (by simp [offCells]) (by simp [stepCells, List.range_succ]))
    (fun fp ↦ ⟨fp + fs "da_column_offsets", by rw [gen_pow_eq_ofK], by
      rw [bufL_off]; exact List.mem_cons_self ..⟩)
    (fun fp ↦ (List.range 7).map (offKid Z (fp + fs "da_column_offsets")))
    (fun _ ↦ True) ((List.range 7).map fun _ => fun _ => True)
    ((List.range 7).map fun b => 2 ^ b * iterK fs SK (offLoopName b) + fs (offLoopName b)) _
    (fun fp ↦ kidsDTB_map _ _ _ fun b hb' _ => ?_)
    (fun fp ↦ le_of_eq (kidsBoundL_map _ _ _ fun _ _ => rfl)) (fun _ ↦ by simp)
    (fun fp k hk _ i hi => ?_) (fun fp rd hB _ k hk => ?_) ?_).mono (by simp) fun _ _ ↦ trivial
  · -- each loop
    have hb7 := List.mem_range.mp hb'
    refine pureB_loop daPure (by interval_cases b <;> simp [daPureSet, offKid, offLoopName])
      (fun rd hm => offLoop_rel hb7 (reads_of_memL hm List.mem_cons_self)
        (reads_of_memL hm (List.mem_cons_of_mem _ List.mem_cons_self))) (hT b hb7)
      (Nat.two_pow_pos b) (by
        have : 2 ^ b ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega)
  · -- what the loops read is the buffers
    obtain ⟨b, hb', rfl⟩ := List.mem_map.mp hk
    obtain ⟨q, hq, h1, h2⟩ := hi
    refine Or.inr ⟨q, ?_, h1, h2⟩
    rw [bufL_off]
    simp only [offKid, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨b, hb', rfl⟩)
  · obtain ⟨b, hb', rfl⟩ := List.mem_map.mp hk
    intro q hq
    simp only [offKid, List.mem_cons, List.not_mem_nil, or_false] at hq
    rw [bufL_off] at hB
    rcases hq with rfl | rfl
    · exact hB _ List.mem_cons_self
    · exact hB _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨b, hb', rfl⟩))
  -- the valuation
  intro fp outs ho rd _ hB hLin
  set b0 := fp + fs "da_column_offsets" with hb0
  rw [bufL_off] at hB
  have hRo : ReadsAt rd (gen ^ b0) (offCells Z) := reads_of_memL hB List.mem_cons_self
  have hRs : ∀ b < 7, ReadsAt rd (gen ^ (b0 + 1024 + 8 * b)) (stepCells Z b) := fun b hb' =>
    reads_of_memL hB (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨b, List.mem_range.mpr hb', rfl⟩))
  let w : ℕ → E := fun i => if i = 1 then gen ^ b0 else gen ^ (b0 + 1024 + 8 * ((i - 10) / 30))
  obtain ⟨σ, hσ⟩ : ∃ σ : Val, σ = B1.Val.ofArgs (ev rd w [gen ^ c] offP) := ⟨_, rfl⟩
  obtain ⟨-, -, hgs⟩ := ev_spec rd w offP [gen ^ c] hchk
  rw [show [gen ^ c].length = 1 from rfl, hS, ← hσ] at hgs
  have hgA : ∀ a, Stmt.atom a ∈ offP → Good rd offStores w σ a := fun a h => hgs (.atom a) h
  have e0 : σ (.n 0) = gen ^ c := by rw [hσ]; exact ev_params rd w (l := [gen ^ c]) hchk (by simp)
  -- the buffers' pointers
  have e1 : σ (.n 1) = gen ^ b0 := by
    have := hgA (.hint (.alloc (.n 1) 1024)) (List.mem_append_left _ (List.mem_append_left _
      List.mem_cons_self))
    simpa [Good, w] using this
  have eB : ∀ b < 7, σ (.n (offB b)) = gen ^ (b0 + 1024 + 8 * b) := by
    intro b hb'
    have := hgA (.hint (.alloc (.n (offB b)) 8)) (mem_offP_block hb' List.mem_cons_self)
    simp only [Good] at this
    rw [this]
    simp only [w, offB, show 10 + 30 * b ≠ 1 by omega, ↓reduceIte,
      show (10 + 30 * b - 10) / 30 = b by omega]
  -- the steps' words
  have hstep : ∀ b < 7, ∀ j < 8, σ (.n (offB b + 1 + 3 * j)) = Z j ∧
      σ (.n (offB b + 1 + 3 * j + 2)) = Z j * ofK (wK j (2 ^ (8 + b))) := by
    intro b hb' j hj
    have e := fun a (ha : a ∈ offStepA b j) => hgA a (mem_offP_block hb' (mem_offBlock_step hj ha))
    have l1 := e (.load (.n (offB b + 1 + 3 * j)) (.n 0) j) (by simp [offStepA])
    have c1 := e (.const (.n (offB b + 1 + 3 * j + 1)) (word (offC b j) 0)) (by simp [offStepA])
    have m1 := e (.mul (.n (offB b + 1 + 3 * j + 2)) (.n (offB b + 1 + 3 * j))
      (.n (offB b + 1 + 3 * j + 1))) (by simp [offStepA])
    simp only [Good] at l1 c1 m1
    rw [ite_pos' (show offB b + 1 + 3 * j < offB b + 1 + 3 * j + 2 ∧
      offB b + 1 + 3 * j + 1 < offB b + 1 + 3 * j + 2 by constructor <;> omega)] at m1
    have hz : σ (.n (offB b + 1 + 3 * j)) = Z j := by
      rcases l1 with h | h
      · simp [offStores, offB] at h
      · rw [h, e0]
        unfold rdAt
        rw [(hzs rd hLin j hj).2]
        rfl
    exact ⟨hz, by rw [m1, c1, hz, offC_word]⟩
  -- the guards
  have hguard : ∀ b < 7, σ (.n (offB b + 27)) = 1 + gen ^ 2 ^ b ∧ σ (.n (offB b + 28)) = 1 ∧
      σ (.n (offB b + 29)) = gen ^ 2 ^ b := by
    intro b hb'
    have e := fun a (ha : Stmt.atom a ∈ offBlockS b) => hgA a (mem_offP_block hb' ha)
    have c25 := e (.const (.n (offB b + 25)) (word 1 0)) (by simp [offBlockS])
    have c26 := e (.const (.n (offB b + 26)) (word (offN b) 0)) (by simp [offBlockS])
    have a27 := e (.add (.n (offB b + 27)) (.n (offB b + 25)) (.n (offB b + 26))) (by simp [offBlockS])
    have c28 := e (.const (.n (offB b + 28)) (word 1 0)) (by simp [offBlockS])
    have c29 := e (.const (.n (offB b + 29)) (word (offN b) 0)) (by simp [offBlockS])
    simp only [Good] at c25 c26 a27 c28 c29
    rw [hNb b hb', word_one] at *
    exact ⟨by rw [a27, c25, c26], c28, c29⟩
  have hcopy : σ (.n 220) = σ (.n 1) :=
    hgA (.copy (.n 220) (.n 1)) (List.mem_append_right _ (List.mem_singleton_self _))
  -- the atoms
  have hat : ∀ a ∈ offAtoms, a.Holds rd σ := by
    refine atoms_holds (S := offStores) (w := w) (fun a ha => ?_) fun a ha hns => Or.inl ?_
    · obtain ⟨s, hs, hsa⟩ := List.mem_filterMap.mp ha
      cases s <;> simp only [atomOfS, Option.some.injEq, reduceCtorEq] at hsa
      subst hsa
      exact hgA _ hs
    have hld := List.all_eq_true.mp hside a ha
    rw [hns] at hld
    have hsh := List.all_eq_true.mp hloads a ha
    cases a with
    | load d p off =>
      obtain ⟨ho8, ⟨rfl, rfl⟩ | ⟨rfl, b, hb', rfl⟩ | ⟨b, hb', rfl, rfl⟩⟩ := isOffLoad_spec hsh
      · -- a zero
        have hc := hgA (.const (.n (2 + off)) (word 0 0)) (mem_offP_zero ho8 (by simp [offZeroA]))
        simp only [Good] at hc
        show LoadHolds rd (σ (.n 1)) off (σ (.n (2 + off)))
        rw [e1, hc, word_zero]
        have := hRo off (by simp [offCells]; omega)
        rwa [offCells_get (by omega), show off / 8 = 0 by omega, Nat.mul_zero, wK_zero, ofK_zero,
          mul_zero] at this
      · show LoadHolds rd (σ (.n 0)) off (σ (.n (offB b + 1 + 3 * off)))
        rw [e0, (hstep b hb' off ho8).1]
        exact hzs rd hLin off ho8
      · show LoadHolds rd (σ (.n (offB b))) off (σ (.n (offB b + 1 + 3 * off + 2)))
        rw [eB b hb', (hstep b hb' off ho8).2]
        have := hRs b hb' off (by simp [stepCells]; exact ho8)
        rwa [stepCells_get ho8] at this
    | _ => simp [atomLoad?] at hld
  -- the loops
  have hrel : ∀ b < 7, coreProgram.Rel rd (offLoopName b)
      [1, gen ^ 2 ^ b, gen ^ b0, gen ^ (b0 + 1024 + 8 * b)] [] := fun b hb' =>
    offLoop_rel hb' hRo (hRs b hb')
  have hne : ∀ b < 7, (1 : E) + gen ^ 2 ^ b ≠ 0 := fun b hb' =>
    one_add_gen_pow_ne_zero (Nat.two_pow_pos b) (by
      have : 2 ^ b ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) (by omega)
      unfold ordG; omega)
  have hsh : ∀ s ∈ offP, SHolds (coreProgram.Rel rd) rd σ s := by
    intro s hs
    rcases isOffStmt_spec (List.all_eq_true.mp hstmts s hs) with ⟨a, rfl⟩ | ⟨b, hb', rfl⟩
    · exact hat a (List.mem_filterMap.mpr ⟨_, hs, rfl⟩)
    · obtain ⟨g27, g28, g29⟩ := hguard b hb'
      refine ⟨by rw [g27, ← pow_zero gen]; exact gen_pow_add_isInK _ _, fun _ => ?_⟩
      simp only [List.map_cons, List.map_nil, g28, g29, e1, eB b hb']
      exact hrel b hb'
  have hcallsS : offP.filterMap (Stmt.callSF σ) = offCalls := by
    rw [← hcalls]
    refine List.filterMap_congr fun s hs => ?_
    rcases isOffStmt_spec (List.all_eq_true.mp hstmts s hs) with ⟨a, rfl⟩ | ⟨b, hb', rfl⟩ <;> rfl
  refine ⟨σ, by rw [hparams]; simp [e0], fun s _ => ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  · rcases isOffStmt_spec (List.all_eq_true.mp hstmts s (by assumption)) with ⟨a, rfl⟩ | ⟨b, _, rfl⟩
      <;> trivial
  · rw [hb]
    refine holdsList_straight _ _ _ _ hsh ?_
    simp [hcopy, e1, gen_pow_eq_ofK]
  · rw [halloc]; rfl
  · rw [halloc]
    simp only [offAllocs, List.map_cons, List.map_map, e1, bases, offSizes]
    simp [gen_pow_eq_ofK, eB, List.range_succ, Nat.add_assoc]
  · simp only [flatCalls, hcallsS, offCalls, List.map_map]
    refine callsMatch_map _ _ _ outs (outsOk_length _ _ _ ho) ho fun b hb' => ?_
    have hb7 := List.mem_range.mp hb'
    obtain ⟨g27, g28, g29⟩ := hguard b hb7
    refine ⟨rfl, ?_, rfl, rfl, fun _ => ?_⟩
    · simp only [Function.comp, Main.mkCall, offKid, g27, ne_eq, hne b hb7, not_false_eq_true,
        decide_true]
    · simp only [Function.comp, Main.mkCall, offKid, List.map_cons, List.map_nil, g28, g29, e1,
        eB b hb7]
  · rw [flatMap_loadsEv _ _ hnli]
    intro q hq
    obtain ⟨s, hs, hq⟩ := List.mem_filterMap.mp hq
    rcases isOffStmt_spec (List.all_eq_true.mp hstmts s hs) with ⟨a, rfl⟩ | ⟨b, _, rfl⟩
    · cases a with
      | load d p off =>
        simp only [Stmt.loadS, Option.some.injEq] at hq
        subst hq
        have ha : Atom.load d p off ∈ offAtoms := List.mem_filterMap.mpr ⟨_, hs, rfl⟩
        obtain ⟨ho8, ⟨rfl, rfl⟩ | ⟨rfl, b, hb', rfl⟩ | ⟨b, hb', rfl, rfl⟩⟩ :=
          isOffLoad_spec (List.all_eq_true.mp hloads _ ha)
        · exact ⟨b0 + off, by rw [e1, limb0_gen_pow_mul], Or.inr (by
            rw [bufL_off]
            exact regionL_of_mem List.mem_cons_self (by simp [offCells]; omega))⟩
        · exact ⟨c + off, by rw [e0, limb0_gen_pow_mul], Or.inl (hzr off ho8)⟩
        · exact ⟨b0 + 1024 + 8 * b + off, by rw [eB b hb', limb0_gen_pow_mul], Or.inr (by
            rw [bufL_off]
            exact regionL_of_mem (List.mem_cons_of_mem _ (List.mem_map.mpr
              ⟨b, List.mem_range.mpr hb', rfl⟩)) (by simp [stepCells]; omega))⟩
      | _ => simp [Stmt.loadS] at hq
    · simp [offCallS, Stmt.loadS] at hq

end
end LeanVM.Guest.B1.Da
