module

public import LeanVM.Guest.Complete.DaFacA
public import LeanVM.Guest.Complete.LoopFA
public import LeanVM.Guest.B1.Da.OffsetsChk
import LeanVM.Guest.CoreRef
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«da_column_offsets»

/-!
# `da_column_offsets`, placed

`da_column_offsets(zs)` at frame `fp` and cursor `c`: its `HeapBuf`s `offsets` (`896` words, at
`c`) and bit `b`'s `steps` (`7` words, at `c + 896 + 7b`) its own words (`offCells Z`,
`stepCells Z b`); its seven loops from `c + 945`, each by `loopF_callAtA` on the explicit valuation
of its block at counter `g^h` (`offLoop_callAtA`): it reads `offsets[7h + j]` and `steps[j]` and
writes their sum at `offsets[7(h + 2^b) + j]`, which `offCells` has since `Ŵ_j` is additive over the
bits of its point (`wK_two_pow_add`). The node's valuation is explicit (`offVals`); `off_callAtA`.
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Da LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd
open LeanVM.Protocol.Verifier (gen eOfNat)
open LeanVM.Guest.Value
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

/-! ## Lists of fixed-size chunks -/

theorem getD_flatMap_range {α : Type} {d : α} (g : ℕ → List α) {m : ℕ} (hg : ∀ i, (g i).length = m) :
    ∀ n j r, j < n → r < m → ((List.range n).flatMap g).getD (m * j + r) d = (g j).getD r d
  | 0, _, _, hj, _ => absurd hj (by omega)
  | n + 1, j, r, hj, hr => by
    have hlen : ((List.range n).flatMap g).length = m * n := by
      rw [List.length_flatMap]
      simp only [hg, List.map_const', List.length_range, List.sum_replicate, smul_eq_mul]
      ring
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    rcases Nat.lt_or_ge j n with h | h
    · have : m * j + r < m * n := by
        calc m * j + r < m * j + m := by omega
          _ = m * (j + 1) := by ring
          _ ≤ m * n := Nat.mul_le_mul_left _ h
      rw [List.getD_append _ _ _ _ (by omega)]
      exact getD_flatMap_range g hg n j r h hr
    · obtain rfl : j = n := by omega
      rw [List.getD_append_right _ _ _ _ (by omega), hlen, Nat.add_sub_cancel_left]

theorem getD_mid {α : Type} {d : α} (L T : List α) (g : ℕ → List α) {m : ℕ} (hg : ∀ i, (g i).length = m)
    {n j r : ℕ} (hj : j < n) (hr : r < m) :
    (L ++ (List.range n).flatMap g ++ T).getD (L.length + (m * j + r)) d = (g j).getD r d := by
  have hlen : ((List.range n).flatMap g).length = m * n := by
    rw [List.length_flatMap]
    simp only [hg, List.map_const', List.length_range, List.sum_replicate, smul_eq_mul]
    ring
  have : m * j + r < m * n := by
    calc m * j + r < m * j + m := by omega
      _ = m * (j + 1) := by ring
      _ ≤ m * n := Nat.mul_le_mul_left _ hj
  rw [List.append_assoc, List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left,
    List.getD_append _ _ _ _ (by omega)]
  exact getD_flatMap_range g hg n j r hj hr

/-! ## The words -/

/-- Bit `b`'s `steps`: `zs[j] · Ŵ_j(e_(7 + b))`. -/
def stepCells (Z : ℕ → E) (b : ℕ) : List E := (List.range 7).map fun j => Z j * word (offC b j) 0

@[simp] theorem length_stepCells (Z : ℕ → E) (b : ℕ) : (stepCells Z b).length = 7 := by simp [stepCells]

theorem offCells_getElem (Z : ℕ → E) {h j : ℕ} (hj : j < 7) (hi : 7 * h + j < 896) :
    (offCells Z)[7 * h + j]'(by simp; exact hi) = Z j * ofK (wK j (128 * h)) := by
  simp only [offCells, List.getElem_map, List.getElem_range]
  rw [show (7 * h + j) % 7 = j by omega, show (7 * h + j) / 7 = h by omega]

/-- **Bit `b`'s doubling**: word `7(h + 2^b) + j` of `offCells` is word `7h + j` plus `steps[j]`. -/
theorem offCells_step (Z : ℕ → E) {b h j : ℕ} (hh : h < 2 ^ b) :
    Z j * ofK (wK j (128 * (h + 2 ^ b))) = Z j * ofK (wK j (128 * h)) + Z j * word (offC b j) 0 := by
  have h128 : 128 * 2 ^ b = 2 ^ (7 + b) := by rw [pow_add]; rfl
  have hx : 128 * h < 2 ^ (7 + b) := by rw [← h128]; omega
  rw [show 128 * (h + 2 ^ b) = 2 ^ (7 + b) + 128 * h by rw [← h128]; ring, wK_two_pow_add j hx, Da.ofK_add,
    offC_word, mul_add]

/-! ## The loops -/

/-- The region of bit `b`'s loop: `offsets` at `c` and its `steps` at `st`. -/
def offLR (c st : ℕ) (i : ℕ) : Prop := (c ≤ i ∧ i < c + 896) ∨ (st ≤ i ∧ i < st + 7)

/-- The valuation of a loop's block at counter `x`: the words read `A`, the steps `S`. -/
def offLoopVals (x N off st : E) (A S : ℕ → E) : List E :=
  [x, N, off, st, x * x, x * x * x, x * x * x * (x * x * x), x * x * x * (x * x * x) * x,
    off * (x * x * x * (x * x * x) * x)] ++ (List.range 7).flatMap (fun j => [A j, S j, A j + S j]) ++
  [word 2 0, x * word 2 0, x * word 2 0 + N, word 2 0, x * word 2 0]

theorem offLoop_mid (x N off st : E) (A S : ℕ → E) {j r : ℕ} (hj : j < 7) (hr : r < 3) :
    Val.ofArgs (offLoopVals x N off st A S) (.n (9 + (3 * j + r))) = [A j, S j, A j + S j].getD r 0 :=
  getD_mid (L := [x, N, off, st, x * x, x * x * x, x * x * x * (x * x * x), x * x * x * (x * x * x) * x,
    off * (x * x * x * (x * x * x) * x)]) _ (fun j => [A j, S j, A j + S j]) (fun _ => rfl) hj hr

/-- Bit `b`'s loop helper. -/
noncomputable def offLoopFn (b : ℕ) : Fn := coreProgram.getD (idx% «da_column_offsets_loop0» + b) default

set_option maxRecDepth 100000 in
theorem offLoop_cok : ∀ b < 7, coreProgram.loop (offLoopName b) = true ∧
    (loopPre (offLoopFn b)).all loopPlainB = true := by
  decide +kernel

theorem offLoop_atoms {b : ℕ} (hb : b < 7) {s : Stmt} (hs : s ∈ loopPre (offLoopFn b)) :
    ∃ a, s = .atom a ∧ a ∈ offLoopA b := by
  have hpl := List.all_eq_true.mp (offLoop_cok b hb).2 s hs
  have hok := offLoop_ok b hb
  simp only [offLoopOk, Bool.and_eq_true] at hok
  cases s with
  | atom a =>
    refine ⟨a, rfl, ?_⟩
    rw [← atomsEqb_sound hok.2]
    exact mem_atomsIn hs
  | _ => simp [loopPlainB] at hpl

/-- What bit `b`'s loop reads: `offsets` and its `steps`. -/
def OffLoopPre (Z : ℕ → E) (b c st : ℕ) (rd : Reader) : Prop :=
  ReadsAt rd (gen ^ c) (offCells Z) ∧ ReadsAt rd (gen ^ st) (stepCells Z b)

variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}

set_option maxRecDepth 10000 in
/-- **Bit `b`'s loop completes placed** from its first counter. -/
theorem offLoop_callAtA {b : ℕ} (hb : b < 7) (k : ℕ) (Z : ℕ → E) (c st fp cur : ℕ)
    (hfc : fp + lpBlk fs (offLoopName b) (2 ^ b - 0) ≤ cur) :
    CallAtA fs al cert k (offLoopName b) [gen ^ 0, gen ^ 2 ^ b, gen ^ c, gen ^ st] [] (offLR c st)
      (fun _ => False) (fun _ => True) (OffLoopPre Z b c st) (fun _ _ => True)
      (lpBlk fs (offLoopName b) (2 ^ b - 0)) fp cur cur := by
  have hok := offLoop_ok b hb
  simp only [offLoopOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨hshape, hlen⟩, -⟩ := hok
  have hf := find_of_idx (offLoop_idx b hb)
  have hpar := loop_params hshape hlen
  have hm : 2 ^ b < 2 ^ 34 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hb64 : 2 ^ b ≤ 64 := le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) (by norm_num : 2 ^ 6 ≤ 64)
  refine loopF_callAtA hf hshape (offLoop_cok b hb).1 (offLoop_cok b hb).2 hm (rest := [gen ^ c, gen ^ st])
    ?_ 0 (Nat.two_pow_pos b) fp cur hfc
  intro h hh rd _ hp
  obtain ⟨hoff, hst⟩ := hp
  set A : ℕ → E := fun j => Z j * ofK (wK j (128 * h)) with hA
  set S : ℕ → E := fun j => Z j * word (offC b j) 0 with hS
  set σ := Val.ofArgs (offLoopVals (gen ^ h) (gen ^ 2 ^ b) (gen ^ c) (gen ^ st) A S) with hσ
  have h8 : σ (.n 8) = gen ^ c * gen ^ (7 * h) := by
    show gen ^ c * (gen ^ h * gen ^ h * gen ^ h * (gen ^ h * gen ^ h * gen ^ h) * gen ^ h) = _
    ring
  have hmid : ∀ j < 7, ∀ r < 3, σ (.n (9 + (3 * j + r))) = [A j, S j, A j + S j].getD r 0 :=
    fun j hj r hr => offLoop_mid _ _ _ _ A S hj hr
  have hsrc : ∀ j < 7, ∀ i, h ≤ i → 7 * i + j < 896 →
      LoadHolds rd (gen ^ c * gen ^ (7 * h)) (7 * (i - h) + j) (Z j * ofK (wK j (128 * i))) := by
    intro j hj i hi hin
    rw [loadHolds_mul_gen_pow, show 7 * h + (7 * (i - h) + j) = 7 * i + j by omega,
      ← offCells_getElem Z hj hin]
    exact hoff _ _
  have hholds : ∀ a ∈ offLoopA b, a.Holds rd σ := by
    intro a ha
    simp only [offLoopA, List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_range,
      List.not_mem_nil, or_false] at ha
    rcases ha with ((rfl | rfl | rfl | rfl | rfl) | ⟨j, hj, rfl | rfl | rfl | rfl⟩) |
      (rfl | rfl | rfl | rfl | rfl)
    all_goals try rfl
    · show LoadHolds rd (σ (.n 8)) j (σ (.n (9 + 3 * j)))
      rw [h8, show 9 + 3 * j = 9 + (3 * j + 0) by rfl, hmid j hj 0 (by norm_num)]
      have := hsrc j hj h le_rfl (by omega)
      rwa [Nat.sub_self, Nat.mul_zero, Nat.zero_add] at this
    · show LoadHolds rd (gen ^ st) j (σ (.n (10 + 3 * j)))
      rw [show 10 + 3 * j = 9 + (3 * j + 1) by omega, hmid j hj 1 (by norm_num)]
      have := hst j (by simp; exact hj)
      simpa [stepCells, hS] using this
    · show σ (.n (11 + 3 * j)) = σ (.n (9 + 3 * j)) + σ (.n (10 + 3 * j))
      rw [show 11 + 3 * j = 9 + (3 * j + 2) by omega, show 10 + 3 * j = 9 + (3 * j + 1) by omega,
        show 9 + 3 * j = 9 + (3 * j + 0) by rfl, hmid j hj 2 (by norm_num), hmid j hj 1 (by norm_num),
        hmid j hj 0 (by norm_num)]
      rfl
    · show LoadHolds rd (σ (.n 8)) (7 * 2 ^ b + j) (σ (.n (11 + 3 * j)))
      rw [h8, show 11 + 3 * j = 9 + (3 * j + 2) by omega, hmid j hj 2 (by norm_num)]
      have := hsrc j hj (h + 2 ^ b) (by omega) (by omega)
      rw [show 7 * (h + 2 ^ b - h) + j = 7 * 2 ^ b + j by rw [Nat.add_sub_cancel_left], offCells_step Z hh] at this
      exact this
  refine ⟨σ, by rw [hpar]; rfl, fun s hs => ?_, fun q hq => ?_⟩
  · obtain ⟨a, rfl, ha⟩ := offLoop_atoms hb hs
    exact hholds a ha
  · obtain ⟨s, hs, hq⟩ := List.mem_filterMap.mp hq
    obtain ⟨a, rfl, ha⟩ := offLoop_atoms hb hs
    simp only [offLoopA, List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_range,
      List.not_mem_nil, or_false] at ha
    rcases ha with ((rfl | rfl | rfl | rfl | rfl) | ⟨j, hj, rfl | rfl | rfl | rfl⟩) |
      (rfl | rfl | rfl | rfl | rfl)
    all_goals simp only [stmtLoad?, reduceCtorEq, Option.some.injEq] at hq
    all_goals subst hq
    · refine ⟨c + 7 * h + j, ?_, Or.inl ⟨by omega, by omega⟩⟩
      show (σ (.n 8)).limb 0 * _ = _
      rw [h8, ← pow_add, gen_pow_eq_ofK, Main.addr_ofK]
    · exact ⟨st + j, by show (gen ^ st).limb 0 * _ = _; rw [gen_pow_eq_ofK, Main.addr_ofK],
        Or.inr ⟨by omega, by omega⟩⟩
    · refine ⟨c + 7 * h + (7 * 2 ^ b + j), ?_, Or.inl ⟨by omega, by omega⟩⟩
      show (σ (.n 8)).limb 0 * _ = _
      rw [h8, ← pow_add, gen_pow_eq_ofK, Main.addr_ofK]

/-! ## The node -/

/-- A statement with no hint into the heap. -/
def noHeapHintS : Stmt → Bool
  | .atom (.hint h) => ((hintDest? h).bind destHeap?).isNone
  | _ => true

theorem heapHintAddrs_straight_nil {σ : Val} {pre : List Stmt} (h : pre.all noHeapHintS = true) :
    heapHintAddrs σ (pre.flatMap (slEvs σ)) = [] := by
  refine List.eq_nil_iff_forall_not_mem.mpr fun A hA => ?_
  obtain ⟨e, he, hA⟩ := List.mem_flatMap.mp hA
  obtain ⟨s, hs, he⟩ := List.mem_flatMap.mp he
  have hn := List.all_eq_true.mp h s hs
  cases s with
  | atom a =>
    simp only [slEvs, List.mem_singleton] at he
    subst he
    cases a with
    | hint hh =>
      simp only [noHeapHintS, Option.isNone_iff_eq_none] at hn
      simp [Ev.hintAddrs, hn] at hA
    | _ => simp [Ev.hintAddrs] at hA
  | call f args rets =>
    simp only [slEvs, List.mem_singleton] at he
    subst he
    simp [Ev.hintAddrs] at hA
  | callIf c f args =>
    simp only [slEvs, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · simp [Ev.hintAddrs] at hA
    · split at hA <;> simp [Ev.hintAddrs] at hA
  | _ => simp [slEvs] at he

theorem length_flatMap_range {α : Type} (g : ℕ → List α) {m : ℕ} (hg : ∀ i, (g i).length = m) (n : ℕ) :
    ((List.range n).flatMap g).length = m * n := by
  rw [List.length_flatMap]
  simp only [hg, List.map_const', List.length_range, List.sum_replicate, smul_eq_mul]
  ring

theorem bases_replicate (m : ℕ) : ∀ (n b : ℕ), bases b (List.replicate n m) = (List.range n).map fun i => b + m * i
  | 0, _ => rfl
  | n + 1, b => by
    rw [List.replicate_succ, bases, bases_replicate m n (b + m), List.range_succ_eq_map, List.map_cons,
      List.map_map, Nat.mul_zero, Nat.add_zero]
    refine List.cons_eq_cons.mpr ⟨rfl, List.map_congr_left fun i _ => ?_⟩
    simp only [Function.comp, Nat.succ_eq_add_one]
    ring

/-- Bit `b`'s part of the node's valuation (`27` values from `.n (offB b)`). -/
def offBVals (c : ℕ) (Z : ℕ → E) (b : ℕ) : List E :=
  [gen ^ (c + 896 + 7 * b)] ++ (List.range 7).flatMap (fun j => [Z j, word (offC b j) 0, Z j * word (offC b j) 0]) ++
    [word 1 0, word (offN b) 0, word 1 0 + word (offN b) 0, word 1 0, word (offN b) 0]

theorem length_offMid (c : ℕ) (Z : ℕ → E) (b : ℕ) :
    ([gen ^ (c + 896 + 7 * b)] ++ (List.range 7).flatMap (fun j => [Z j, word (offC b j) 0,
      Z j * word (offC b j) 0])).length = 22 := by
  rw [List.length_append, length_flatMap_range (m := 3)
    (fun j => [Z j, word (offC b j) 0, Z j * word (offC b j) 0]) (fun _ => rfl)]; rfl

theorem length_offBVals (c : ℕ) (Z : ℕ → E) (b : ℕ) : (offBVals c Z b).length = 27 := by
  rw [offBVals, List.length_append, length_offMid]; rfl

/-- `da_column_offsets`' valuation: `zs`, `offsets`, the zeros, each bit's, the returned copy. -/
def offVals (bz c : ℕ) (Z : ℕ → E) : List E :=
  [gen ^ bz, gen ^ c, 0, 0, 0, 0, 0, 0, 0] ++ (List.range 7).flatMap (offBVals c Z) ++ [gen ^ c]

/-- The node's own words: `offsets` and each bit's `steps`. -/
def offWo (Z : ℕ → E) (c : ℕ) : Words :=
  (c, offCells Z) :: (List.range 7).map fun b => (c + 896 + 7 * b, stepCells Z b)

/-- Bit `b`'s loop call. -/
def offCallS (b : ℕ) : Option V × String × List V × List V :=
  (some (.n (offB b + 24)), offLoopName b, [.n (offB b + 25), .n (offB b + 26), .n 1, .n (offB b)], [])

set_option maxRecDepth 100000 in
theorem offP_cok : offP.all Stmt.straight = true ∧ offP.all noHeapHintS = true ∧
    offP.filterMap Stmt.allocSz = (.n 1, .inl 896) :: (List.range 7).map (fun b => (.n (offB b), .inl 7)) ∧
    offP.filterMap Stmt.callS = (List.range 7).map offCallS ∧ offP.filterMap Stmt.addrS = [] ∧
    coreProgram.loop "da_column_offsets" = false := by
  decide +kernel

theorem off_facts : (fn% «da_column_offsets»).params = [.n 0] ∧
    (fn% «da_column_offsets»).body = offP ++ [.ret [.n 198]] ∧
    ∀ b < 7, K.ofBits (offN b) = addressOfIndex (2 ^ b) := by
  have h := off_ok
  simp only [offOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨hp, hb⟩, -⟩, hN⟩ := h
  exact ⟨hp, stmtsEqb_sound hb, hN⟩

/-- The loops' cursors: each loop's frame at the aligned base, ending at its cursor. -/
def offFold (fs : String → ℕ) (al : String → Bool) : List ℕ → ℕ → ℕ
  | [], cur => cur
  | b :: bs, cur => offFold fs al bs (allocBase (al (offLoopName b)) cur + lpBlk fs (offLoopName b) (2 ^ b - 0))

/-- **The loops' end**: each loop's block over at most `2^6` iterations. -/
theorem offFold_le (hfs : ∀ g, fs g < 2 ^ 16) :
    ∀ (bs : List ℕ) (cur : ℕ), (∀ b ∈ bs, b ≤ 6) → offFold fs al bs cur ≤ cur + bs.length * 2 ^ 23
  | [], cur, _ => by simp [offFold]
  | b :: bs, cur, h => by
    rw [offFold]
    have h1 := offFold_le hfs bs (allocBase (al (offLoopName b)) cur + lpBlk fs (offLoopName b) (2 ^ b - 0))
      fun b' hb' => h b' (List.mem_cons_of_mem _ hb')
    have h2 := allocBase_le (al (offLoopName b)) cur
    have h3 := lpBlk_le16' hfs (offLoopName b) (2 ^ b - 0)
    have h4 : 2 ^ b - 0 ≤ 2 ^ 6 :=
      (Nat.sub_le _ _).trans (Nat.pow_le_pow_right (by norm_num) (h b List.mem_cons_self))
    have h5 : (2 ^ b - 0) * 2 ^ 16 ≤ 2 ^ 6 * 2 ^ 16 := Nat.mul_le_mul_right _ h4
    rw [List.length_cons, Nat.succ_mul]
    omega

/-- **The loops complete placed**, one after another from the cursor. -/
theorem off_kids {k : ℕ} {σ : Val} {R : ℕ → Prop} {Pre : Reader → Prop} {Z : ℕ → E} {c : ℕ}
    (hσ : ∀ b < 7, [V.n (offB b + 25), .n (offB b + 26), .n 1, .n (offB b)].map σ =
      [gen ^ 0, gen ^ 2 ^ b, gen ^ c, gen ^ (c + 896 + 7 * b)] ∧ σ (.n (offB b + 24)) ≠ 0)
    (hR : ∀ b < 7, ∀ i, offLR c (c + 896 + 7 * b) i → R i) :
    ∀ (bs : List ℕ), (∀ b ∈ bs, b < 7) → ∀ (O : Reader → Prop) (Dacc : ℕ → Prop) (cur : ℕ) (Oend : Reader → Prop),
      (∀ rd, O rd → ∀ b < 7, OffLoopPre Z b c (c + 896 + 7 * b) rd) → (∀ rd, O rd → Oend rd) →
      KidsAtF fs al cert k σ R Pre O Dacc [] (bs.map (mkCall σ ∘ offCallS)) cur (offFold fs al bs cur) Oend
        (fun _ => False)
  | [], _, O, Dacc, cur, Oend, _, hOe => by
    rw [List.map_nil, KidsAtF]; exact ⟨rfl, hOe, fun _ h => h.elim⟩
  | b :: bs, hbs, O, Dacc, cur, Oend, hO, hOe => by
    have hb := hbs b List.mem_cons_self
    obtain ⟨hargs, hg⟩ := hσ b hb
    rw [List.map_cons, KidsAtF]
    have ht : (mkCall σ (offCallS b)).taken = true := by simp [mkCall, offCallS, hg]
    simp only [Function.comp, ht, ↓reduceIte]
    refine ⟨lpBlk fs (offLoopName b) (2 ^ b - 0),
      allocBase (al (offLoopName b)) cur + lpBlk fs (offLoopName b) (2 ^ b - 0), offLR c (c + 896 + 7 * b), fun _ => False, fun _ => True,
      fun i hi => Or.inl (hR b hb i hi), ?_, ?_⟩
    · show CallAtA fs al cert k (offLoopName b) ([V.n (offB b + 25), .n (offB b + 26), .n 1, .n (offB b)].map σ)
        [] _ _ _ _ _ _ _ _ _
      rw [hargs]
      exact (offLoop_callAtA hb k Z c (c + 896 + 7 * b) _ _ le_rfl).mono (fun _ h => h) (fun _ h => h)
        (fun _ h => h) (fun rd h => hO rd h.2 b hb) (fun _ _ _ h => h)
    · exact off_kids hσ hR bs (fun b' h => hbs b' (List.mem_cons_of_mem _ h)) _ _ _ Oend
        (fun rd h => hO rd h.1) (fun rd h => hOe rd h.1)

theorem offZeroA_cells (Z : ℕ → E) {j : ℕ} (hj : j < 7) : (offCells Z)[j]'(by simp; omega) = 0 := by
  have := offCells_getElem Z (h := 0) hj (by omega)
  simp only [Nat.mul_zero, Nat.zero_add] at this
  rw [this, wK_zero, show ofK (0 : K) = 0 from map_zero (algebraMap K E), mul_zero]

set_option maxRecDepth 10000 in
/-- **`da_column_offsets` completes placed** at frame `fp` and cursor `c`, its offsets at `c`. -/
theorem off_callAtA (k : ℕ) (Z : ℕ → E) (bz : ℕ) {R : ℕ → Prop} (hR : ∀ j < 7, R (bz + j)) {fp c : ℕ}
    (hfc : fp + fs "da_column_offsets" ≤ c) :
    CallAtA fs al cert k "da_column_offsets" [gen ^ bz] [gen ^ c] R (fun i => c ≤ i ∧ i < c + 896)
      (fun rd => HoldsWords rd [(c, offCells Z)]) (fun rd => ∀ j < 7, LoadHolds rd (gen ^ bz) j (Z j))
      (fun _ _ => True) (fs "da_column_offsets") fp c (offFold fs al (List.range 7) (c + 945)) := by
  obtain ⟨hstr, hnh, halloc, hcalls, haddr, hlp⟩ := offP_cok
  obtain ⟨hparams, hbody, hN⟩ := off_facts
  set σ := Val.ofArgs (offVals bz c Z) with hσ
  have hparts := straight_parts σ offP hstr
  have hal : allocs σ (offP.flatMap (slEvs σ)) = 896 :: List.replicate 7 7 := by
    rw [hparts.2.1, halloc]; rfl
  have hwN : ∀ b < 7, word (offN b) 0 = gen ^ 2 ^ b := fun b hb => by
    rw [word_eOfNat, eOfNat, hN b hb, gen_pow_eq_ofK]
  -- the valuation
  have hB : ∀ b < 7, ∀ r < 27, σ (.n (offB b + r)) = (offBVals c Z b).getD r 0 := by
    intro b hb r hr
    rw [show offB b + r = [gen ^ bz, gen ^ c, (0 : E), 0, 0, 0, 0, 0, 0].length + (27 * b + r) by
      unfold offB; simp; omega]
    exact getD_mid _ _ (offBVals c Z) (length_offBVals c Z) hb hr
  have hS : ∀ b < 7, ∀ j < 7, ∀ s < 3, ∀ i, i = offB b + 1 + 3 * j + s →
      σ (.n i) = [Z j, word (offC b j) 0, Z j * word (offC b j) 0].getD s 0 := by
    intro b hb j hj s hs i hi
    rw [hi, show offB b + 1 + 3 * j + s = offB b + (1 + (3 * j + s)) by omega, hB b hb _ (by omega), offBVals]
    exact getD_mid [gen ^ (c + 896 + 7 * b)] _ (fun j => [Z j, word (offC b j) 0, Z j * word (offC b j) 0])
      (fun _ => rfl) hj hs
  have hG : ∀ b < 7, ∀ t < 5, ∀ i, i = offB b + 22 + t →
      σ (.n i) = [word 1 0, word (offN b) 0, word 1 0 + word (offN b) 0, word 1 0, word (offN b) 0].getD t 0 := by
    intro b hb t ht i hi
    rw [hi, show offB b + 22 + t = offB b + (22 + t) by omega, hB b hb _ (by omega), offBVals,
      List.getD_append_right _ _ _ _ (by rw [length_offMid]; omega), length_offMid, Nat.add_sub_cancel_left]
  have hP : ∀ b < 7, σ (.n (offB b)) = gen ^ (c + 896 + 7 * b) := fun b hb => by
    have := hB b hb 0 (by norm_num); rw [Nat.add_zero] at this; rw [this]; rfl
  have h198 : σ (.n 198) = gen ^ c := by
    show (offVals bz c Z).getD 198 0 = _
    have hl : ([gen ^ bz, gen ^ c, (0 : E), 0, 0, 0, 0, 0, 0] ++ (List.range 7).flatMap (offBVals c Z)).length =
        198 := by
      rw [List.length_append, length_flatMap_range (offBVals c Z) (length_offBVals c Z)]; rfl
    rw [offVals, List.getD_append_right _ _ _ _ (by rw [hl]), hl]; rfl
  have hZ0 : ∀ j < 7, σ (.n (2 + j)) = 0 := fun j hj => by interval_cases j <;> rfl
  -- the calls
  have hcl : calls (offP.flatMap (slEvs σ)) = (List.range 7).map (mkCall σ ∘ offCallS) := by
    rw [hparts.2.2.2, hcalls, List.map_map]
  have hguard : ∀ b < 7, σ (.n (offB b + 24)) = word 1 0 + gen ^ 2 ^ b := fun b hb => by
    rw [hG b hb 2 (by norm_num) _ rfl, hwN b hb]; rfl
  have hown : ∀ i, c ≤ i → i < c + 945 → ownData cert fp c "da_column_offsets" (allocs σ (offP.flatMap (slEvs σ)))
      (offP.flatMap (slEvs σ)) i := fun i h1 h2 => by
    rw [hal]
    left
    refine VsC.bufs_cover _ c i h1 (by simp; omega)
  refine callAtA_node hlp hfc ⟨σ, fn% «da_column_offsets», offP.flatMap (slEvs σ), [.n 198], offWo Z c, [],
    fun rd => HoldsWords rd (offWo Z c), fun _ => False, find_da_column_offsets, by rw [hparams]; rfl,
    by rw [hbody]; exact walk_straight σ _ offP hstr, by simp [h198], ?_, ?_, ?_, ?_, ?_, ?_,
    fun rd h => ?_, ?_, fun _ _ _ _ _ _ _ => trivial⟩
  · -- placed
    rw [hal]
    refine ⟨?_, fun q hq => by rw [hparts.2.2.1, haddr] at hq; simp at hq⟩
    rw [hparts.1, halloc, bases, bases_replicate]
    simp only [List.map_cons, List.map_map]
    refine List.cons_eq_cons.mpr ⟨by show gen ^ c = _; rw [gen_pow_eq_ofK], List.map_congr_left fun b hb => ?_⟩
    simp only [Function.comp]
    rw [hP b (List.mem_range.mp hb), gen_pow_eq_ofK]
  · -- the own words
    rw [hal]
    refine ⟨fun q hq => Or.inr ?_, ?_⟩
    · simp only [offWo, List.mem_cons, List.mem_map, List.mem_range] at hq
      rcases hq with rfl | ⟨b, hb, rfl⟩
      · simp
      · simp; omega
    · simp only [offWo, List.pairwise_cons, List.mem_map, List.mem_range, forall_exists_index, and_imp]
      refine ⟨fun q b hb hq => by subst hq; simp, ?_⟩
      refine List.pairwise_map.mpr (List.Pairwise.imp_of_mem ?_ (List.pairwise_lt_range (n := 7)))
      intro a b' _ _ h
      simp; omega
  · -- the loads
    intro A hA
    rw [loadAddrs_straight σ offP hstr] at hA
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hA
    obtain ⟨s, hs, hq⟩ := List.mem_filterMap.mp hq
    simp only [offP, offBlockS, List.mem_append, List.mem_cons, List.mem_map, List.mem_flatMap,
      List.mem_range, List.not_mem_nil, or_false] at hs
    rcases hs with ((rfl | ⟨a, ⟨j, hj, ha⟩, rfl⟩) | ⟨b, hb, (rfl | ⟨a, ⟨j, hj, ha⟩, rfl⟩) |
      (rfl | rfl | rfl | rfl | rfl | rfl)⟩) | rfl
    all_goals try (simp [stmtLoad?] at hq; done)
    · simp only [offZeroA, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl <;> simp only [stmtLoad?, reduceCtorEq, Option.some.injEq] at hq
      subst hq
      exact ⟨c + j, by show (gen ^ c).limb 0 * _ = _; rw [gen_pow_eq_ofK, Main.addr_ofK],
        Or.inl (hown _ (by omega) (by omega))⟩
    · simp only [offStepA, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl <;> simp only [stmtLoad?, reduceCtorEq, Option.some.injEq] at hq
      · subst hq
        exact ⟨bz + j, by show (gen ^ bz).limb 0 * _ = _; rw [gen_pow_eq_ofK, Main.addr_ofK],
          Or.inr (Or.inl (hR j hj))⟩
      · subst hq
        exact ⟨c + 896 + 7 * b + j, by show (σ (.n (offB b))).limb 0 * _ = _; rw [hP b hb, gen_pow_eq_ofK,
          Main.addr_ofK], Or.inl (hown _ (by omega) (by omega))⟩
  · intro A hA
    rw [heapHintAddrs_straight_nil hnh] at hA
    simp at hA
  · intro i hi
    exact Or.inl (hown i hi.1 (by omega))
  · -- the loops
    rw [hcl, hal]
    simp only [List.sum_cons, List.sum_replicate, smul_eq_mul]
    refine off_kids (Z := Z) (c := c) (fun b hb => ⟨?_, ?_⟩) (fun b hb i hi => Or.inr (hown i ?_ ?_)) _
      (fun b h => List.mem_range.mp h) _ _ _ _ (fun rd h b hb => ⟨?_, ?_⟩) (fun _ h => h)
    · show [σ (.n (offB b + 22 + 3)), σ (.n (offB b + 22 + 4)), σ (.n 1), σ (.n (offB b))] = _
      rw [hG b hb 3 (by norm_num) _ rfl, hG b hb 4 (by norm_num) _ rfl, hP b hb, hwN b hb,
        show σ (.n 1) = gen ^ c from rfl]
      simp [word_one]
    · rw [hguard b hb]
      have := one_add_gen_pow_ne (d := 2 ^ b) (Nat.pow_lt_pow_right (by norm_num) (by omega))
      simpa [Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos b)] using this
    · rcases hi with hi | hi <;> omega
    · rcases hi with hi | hi <;> omega
    · have := h (c, offCells Z) List.mem_cons_self
      rwa [← gen_pow_eq_ofK] at this
    · have := h (c + 896 + 7 * b, stepCells Z b) (List.mem_cons_of_mem _ (List.mem_map.mpr
        ⟨b, List.mem_range.mpr hb, rfl⟩))
      rwa [← gen_pow_eq_ofK] at this
  · exact fun q hq => by simp only [List.mem_singleton] at hq; subst hq; exact h _ List.mem_cons_self
  · -- the atoms
    intro rd _ hp hO ev hev
    have hoff : ReadsAt rd (gen ^ c) (offCells Z) := by
      have := hO (c, offCells Z) List.mem_cons_self; rwa [← gen_pow_eq_ofK] at this
    have hst : ∀ b < 7, ReadsAt rd (gen ^ (c + 896 + 7 * b)) (stepCells Z b) := fun b hb => by
      have := hO (c + 896 + 7 * b, stepCells Z b) (List.mem_cons_of_mem _ (List.mem_map.mpr
        ⟨b, List.mem_range.mpr hb, rfl⟩))
      rwa [← gen_pow_eq_ofK] at this
    refine events_straight (fun s hs => ?_) ev hev
    simp only [offP, offBlockS, List.mem_append, List.mem_cons, List.mem_map, List.mem_flatMap,
      List.mem_range, List.not_mem_nil, or_false] at hs
    rcases hs with ((rfl | ⟨a, ⟨j, hj, ha⟩, rfl⟩) | ⟨b, hb, (rfl | ⟨a, ⟨j, hj, ha⟩, rfl⟩) |
      (rfl | rfl | rfl | rfl | rfl | rfl)⟩) | rfl
    · trivial
    · simp only [offZeroA, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · show σ (.n (2 + j)) = word 0 0
        rw [hZ0 j hj, word_zero]
      · show LoadHolds rd (σ (.n 1)) j (σ (.n (2 + j)))
        rw [hZ0 j hj, ← offZeroA_cells Z hj]
        exact hoff j _
    · trivial
    · simp only [offStepA, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl
      · show LoadHolds rd (gen ^ bz) j (σ (.n (offB b + 1 + 3 * j)))
        rw [hS b hb j hj 0 (by norm_num) (offB b + 1 + 3 * j) (by omega)]
        exact hp j hj
      · show σ (.n (offB b + 1 + 3 * j + 1)) = word (offC b j) 0
        rw [hS b hb j hj 1 (by norm_num) _ rfl]; rfl
      · show σ (.n (offB b + 1 + 3 * j + 2)) = σ (.n (offB b + 1 + 3 * j)) * σ (.n (offB b + 1 + 3 * j + 1))
        rw [hS b hb j hj 2 (by norm_num) _ rfl, hS b hb j hj 0 (by norm_num) (offB b + 1 + 3 * j) (by omega),
          hS b hb j hj 1 (by norm_num) _ rfl]; rfl
      · show LoadHolds rd (σ (.n (offB b))) j (σ (.n (offB b + 1 + 3 * j + 2)))
        rw [hS b hb j hj 2 (by norm_num) _ rfl, hP b hb]
        have := hst b hb j (by simp; exact hj)
        simpa [stepCells] using this
    · show σ (.n (offB b + 22)) = word 1 0
      rw [hG b hb 0 (by norm_num) _ rfl]; rfl
    · show σ (.n (offB b + 23)) = word (offN b) 0
      rw [hG b hb 1 (by norm_num) _ rfl]; rfl
    · show σ (.n (offB b + 24)) = σ (.n (offB b + 22)) + σ (.n (offB b + 23))
      rw [hG b hb 2 (by norm_num) _ rfl, hG b hb 0 (by norm_num) _ rfl, hG b hb 1 (by norm_num) _ rfl]; rfl
    · show σ (.n (offB b + 25)) = word 1 0
      rw [hG b hb 3 (by norm_num) _ rfl]; rfl
    · show σ (.n (offB b + 26)) = word (offN b) 0
      rw [hG b hb 4 (by norm_num) _ rfl]; rfl
    · show IsInK (σ (.n (offB b + 24)))
      rw [hguard b hb, word_one, ← pow_zero gen]
      exact gen_pow_add_isInK _ _
    · show σ (.n 198) = σ (.n 1)
      rw [h198]; rfl

end
end LeanVM.Guest.Complete
