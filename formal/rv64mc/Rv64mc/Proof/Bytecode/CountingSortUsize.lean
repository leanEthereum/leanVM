/-
  Rv64mc.Proof.Bytecode.CountingSortUsize

  `counting_sort::<usize, block_members::{closure#0}>`, in progress: the counting loop (`loop1`, from its head at
  instruction 66 to the prefix sums') and the prefix-sum loop (`loop2`, from 102 to the allocation of the sorted
  copy at 114) are proved, each over the model's pass (`counts`, `prefixes`) on the `starts` block the call
  allocated. Every store into that block keeps what a loop head states of memory (`fresh_store`). The entry, the
  copy (`alloc`, `memcpy`) and the placing loop are not proved yet.
-/

import Rv64mc.Spec.Bytecode.CountingSortUsize
import Rv64mc.Spec.Runtime.TryAllocateIn
import Rv64mc.Spec.Runtime.Alloc
import Rv64mc.Spec.Runtime.Mem
import Rv64mc.Spec.Runtime.Panic
import Rv64mc.Gen.Tmpl.Verifier.Bytecode.CountingSortUsizeBlockMembersClosure0
import Rv64mc.Tactic.Sym

namespace Rv64mc.Proof.Bytecode.CountingSortUsize

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime Rv64mc.Spec.Bytecode.CountingSortUsize
open Rv64mc.Gen.Verifier.Bytecode.CountingSortUsizeBlockMembersClosure0 (Link tmpl)

/-! ## Words and addresses -/

theorem LensAt.keep {m m' : MachineState} {base : Word} {lens : List Nat} (h : LensAt m base lens)
    (hk : Keeps m m' base (Layouts.KVecU16.byteSize * lens.length)) : LensAt m' base lens := by
  refine ⟨h.1, fun i hi => ?_⟩
  have h1 := h.1
  simp only [Layouts.KVecU16.byteSize] at h1 hk
  have hb : (lenAt base i).toNat = base.toNat + (32 * i + 24) := by
    unfold lenAt
    simp only [Layouts.KVecU16.byteSize, Layouts.KVecU16.f1, Layouts.Vec.len]
    exact toNat_add_ofNat (by omega)
  rw [hk _ ⟨by rw [hb]; omega, by rw [hb]; omega⟩]
  exact h.2 i hi

/-- Word `i` of a list of numbers, read. -/
theorem words_get {M : MachineState} {a : Word} {xs : List Nat} (h : WordsAt M a (xs.map (BitVec.ofNat 64))) {i : Nat}
    (hi : i < xs.length) : M.getMem (a + BitVec.ofNat 64 (8 * i)) = BitVec.ofNat 64 xs[i] := by
  rw [h.2 i (by simpa using hi), List.getElem_map]

/-- Word `i` of a list of numbers, written. -/
theorem words_set {M : MachineState} {a : Word} {xs : List Nat} (h : WordsAt M a (xs.map (BitVec.ofNat 64)))
    {i : Nat} (hi : i < xs.length) (v : Nat) :
    WordsAt (M.setMem (a + BitVec.ofNat 64 (8 * i)) (BitVec.ofNat 64 v)) a ((xs.set i v).map (BitVec.ofNat 64)) := by
  have h1 := h.1
  simp only [List.length_map] at h1
  refine ⟨by simpa using h1, fun k hk => ?_⟩
  simp only [List.length_map, List.length_set] at hk
  by_cases e : k = i
  · subst e; simp
  · have hne : a + BitVec.ofNat 64 (8 * k) ≠ a + BitVec.ofNat 64 (8 * i) := fun he => e (by
      have := congrArg BitVec.toNat he
      rw [toNat_add_ofNat (by omega), toNat_add_ofNat (by omega)] at this; omega)
    rw [MachineState.getMem_setMem_ne hne, h.2 k (by simpa using hk)]
    simp [Ne.symm e]

theorem addr_shl3 (s a : Word) : s + (a + 1#64) <<< 3 = s + BitVec.ofNat 64 (8 * (a.toNat + 1) % 2 ^ 64) := by
  congr 1; apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.shiftLeft_eq]; omega

theorem addr_shl5 (x a : Word) : x + a <<< 5 + 24#64 = lenAt x a.toNat := by
  rw [lenAt, BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Layouts.KVecU16.byteSize,
    Layouts.KVecU16.f1, Layouts.Vec.len]; omega

theorem addr_len (x : Word) {a : Nat} (ha : a < 2 ^ 64) : x + BitVec.ofNat 64 a <<< 5 + 24#64 = lenAt x a := by
  rw [addr_shl5, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]

theorem addr_start (s : Word) {a : Nat} (ha : 8 * (a + 1) < 2 ^ 64) :
    s + (BitVec.ofNat 64 a + 1#64) <<< 3 = s + BitVec.ofNat 64 (8 * (a + 1)) := by
  rw [addr_shl3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem succ_word (a : Nat) : BitVec.ofNat 64 a + 1#64 = BitVec.ofNat 64 (a + 1) := (BitVec.ofNat_add a 1).symm

theorem zero_off (s : Word) : s + 8#64 = s + 8#64 + BitVec.ofNat 64 (8 * 0) := by simp

theorem step_ptr (x : Word) (j : Nat) : x + BitVec.ofNat 64 (8 * j) + 8#64 = x + BitVec.ofNat 64 (8 * (j + 1)) := by
  rw [BitVec.add_assoc]; congr 1; rw [Nat.mul_succ, BitVec.ofNat_add]

theorem step_rem {n j : Nat} (hj : j < n) :
    BitVec.ofNat 64 (8 * (n - j)) + 18446744073709551608#64 = BitVec.ofNat 64 (8 * (n - (j + 1))) := by
  rw [show 8 * (n - j) = 8 * (n - (j + 1)) + 8 by omega, BitVec.ofNat_add, BitVec.add_assoc,
    show BitVec.ofNat 64 8 + 18446744073709551608#64 = 0#64 by decide, BitVec.add_zero]

theorem rem_zero {n j : Nat} (hj : j < n) (hn : 8 * n < 2 ^ 64) :
    BitVec.ofNat 64 (8 * (n - j)) + 18446744073709551608#64 = 0#64 ↔ j + 1 = n := by
  rw [step_rem hj, ← BitVec.toNat_inj, BitVec.toNat_ofNat, show (0#64).toNat = 0 from rfl]
  constructor <;> intro h <;> omega

theorem lt_word {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) : BitVec.ofNat 64 a < BitVec.ofNat 64 b ↔ a < b := by
  rw [BitVec.lt_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

/-- **A store into a block the call allocated** keeps everything a loop head states of memory: the frame, the
    static data, the saved slots, the items, the members' counts and `NEXT`. -/
theorem fresh_store {env : Env} {top a v x11 x14 : Word} {out : Word → Prop} {m M S : MachineState}
    {items lens : List Nat} (hstk : env.stackLimit.toNat + 112 ≤ top.toNat) (hF : env.Frame top out m M)
    (hst : env.Static M) (hsl : ∀ b, top + 0xffffffffffffffa8#64 ≤ b → M.getMem b = S.getMem b)
    (hW : WordsAt M x11 (items.map (BitVec.ofNat 64))) (hli : env.Live m x11 (8 * items.length))
    (hLn : LensAt M x14 lens) (hll : env.Live m x14 (Layouts.KVecU16.byteSize * lens.length))
    (hlo : (env.next m).toNat ≤ a.toNat) (hhi : a.toNat < (env.next M).toNat) :
    env.Frame top out m (M.setMem a v) ∧ env.Static (M.setMem a v) ∧
      (∀ b, top + 0xffffffffffffffa8#64 ≤ b → (M.setMem a v).getMem b = S.getMem b) ∧
      WordsAt (M.setMem a v) x11 (items.map (BitVec.ofNat 64)) ∧ LensAt (M.setMem a v) x14 lens ∧
      env.next (M.setMem a v) = env.next M := by
  have hl := env.layout
  have h2 := hF.2.1
  have hne : a ≠ env.nextAddr := fun e => by rw [e] at hhi; omega
  have ha88 : (top + 0xffffffffffffffa8#64).toNat = top.toNat - 88 := by
    rw [BitVec.toNat_add, show (0xffffffffffffffa8#64).toNat = 2 ^ 64 - 88 from rfl]; omega
  unfold Env.Live at hli hll
  refine ⟨Tactic.frame_fresh hF rfl hlo hhi, Tactic.static_store hst (by omega), fun b hb => ?_, ?_, ?_,
    Tactic.next_setMem hne⟩
  · have : b ≠ a := fun e => by rw [BitVec.le_def, ha88, e] at hb; omega
    rw [MachineState.getMem_setMem_ne this, hsl b hb]
  · refine hW.keep (Keeps.setMem fun h => ?_)
    obtain ⟨h1, h2'⟩ := h; simp only [List.length_map] at h2'; omega
  · refine LensAt.keep hLn (Keeps.setMem fun h => ?_)
    obtain ⟨h1, h2'⟩ := h; omega

/-! ## The model's three passes -/

/-- The counts after the first `j` items: `starts[key + 1] += 1`. -/
def counts (items : List Nat) (keys : Nat) (lens : List Nat) (j : Nat) : List Nat :=
  (items.take j).foldl (fun starts item ↦
    starts.set (key lens item + 1) (starts.getD (key lens item + 1) 0 + 1)) (List.replicate (keys + 1) 0)

theorem counts_length (items : List Nat) (keys : Nat) (lens : List Nat) (j : Nat) :
    (counts items keys lens j).length = keys + 1 := by
  unfold counts
  suffices ∀ (l init : List Nat), (l.foldl (fun starts item ↦
      starts.set (key lens item + 1) (starts.getD (key lens item + 1) 0 + 1)) init).length = init.length by
    rw [this]; simp
  intro l
  induction l with
  | nil => intro init; rfl
  | cons x l ih => intro init; rw [List.foldl_cons, ih, List.length_set]

theorem counts_succ {items : List Nat} {keys : Nat} {lens : List Nat} {j : Nat} (h : j < items.length) :
    counts items keys lens (j + 1) = (counts items keys lens j).set (key lens items[j] + 1)
      ((counts items keys lens j).getD (key lens items[j] + 1) 0 + 1) := by
  rw [counts, List.take_add_one, List.getElem?_eq_getElem h, Option.toList_some, List.foldl_append]; rfl

/-- The prologue's stores: `ra` and `s0`..`s9` below `top`. -/
def saved (m : MachineState) (ret top : Word) (regs : Reg → Word) : MachineState :=
  ((((((((((m.setMem (top + 0xfffffffffffffff8#64) ret).setMem (top + 0xfffffffffffffff0#64) (regs .x8)).setMem
    (top + 0xffffffffffffffe8#64) (regs .x9)).setMem (top + 0xffffffffffffffe0#64) (regs .x18)).setMem
    (top + 0xffffffffffffffd8#64) (regs .x19)).setMem (top + 0xffffffffffffffd0#64) (regs .x20)).setMem
    (top + 0xffffffffffffffc8#64) (regs .x21)).setMem (top + 0xffffffffffffffc0#64) (regs .x22)).setMem
    (top + 0xffffffffffffffb8#64) (regs .x23)).setMem (top + 0xffffffffffffffb0#64) (regs .x24)).setMem
    (top + 0xffffffffffffffa8#64) (regs .x25)

/-- What every loop head keeps: the registers set at entry, the frame, the saved slots, the items, the members'
    counts and the `starts` block allocated by the call. -/
def Ctx (env : Env) (items : List Nat) (keys : Nat) (lens : List Nat) (ret top : Word) (regs : Reg → Word)
    (m : MachineState) (s : Word) (R : Reg → Word) (M : MachineState) : Prop :=
  R .x2 = top + 0xffffffffffffff90#64 ∧ R .x8 = BitVec.ofNat 64 lens.length ∧ R .x9 = BitVec.ofNat 64 keys + 1#64 ∧
    R .x18 = BitVec.ofNat 64 (items.map (BitVec.ofNat 64)).length ∧ R .x19 = regs .x14 ∧
    R .x20 = BitVec.ofNat 64 keys ∧ R .x21 = regs .x11 ∧
    R .x22 = BitVec.ofNat 64 (items.map (BitVec.ofNat 64)).length <<< 3 ∧ R .x23 = regs .x10 ∧
    R .x24 = regs .x24 ∧ R .x25 = s ∧ R .x26 = regs .x26 ∧ R .x27 = regs .x27 ∧
    env.Frame top (Spec.Whir.SretOut Layouts.Vec.byteSize regs m) m M ∧ env.Static M ∧
    (∀ a, top + 0xffffffffffffffa8#64 ≤ a → M.getMem a = (saved m ret top regs).getMem a) ∧
    WordsAt M (regs .x11) (items.map (BitVec.ofNat 64)) ∧ LensAt M (regs .x14) lens ∧
    (env.next m).toNat ≤ s.toNat ∧ s.toNat + 8 * (keys + 1) ≤ (env.next M).toNat

/-- The counting loop's invariant after `j` items. -/
def Inv1 (env : Env) (items : List Nat) (keys : Nat) (lens : List Nat) (ret top : Word) (regs : Reg → Word)
    (m : MachineState) (s : Word) (j : Nat) (R : Reg → Word) (M : MachineState) : Prop :=
  Ctx env items keys lens ret top regs m s R M ∧
    R .x12 = regs .x11 + BitVec.ofNat 64 (8 * j) ∧ R .x11 = BitVec.ofNat 64 (8 * (items.length - j)) ∧
    WordsAt M s ((counts items keys lens j).map (BitVec.ofNat 64)) ∧ ∀ x ∈ items.take j, key lens x < keys

/-- The starts after the prefix sums over `1..k`. -/
def prefixes (items : List Nat) (keys : Nat) (lens : List Nat) (k : Nat) : List Nat :=
  (List.range' 1 k).foldl (fun st k ↦ st.set k (st.getD k 0 + st.getD (k - 1) 0))
    (counts items keys lens items.length)

/-- The prefix-sum loop's invariant after `k` passes. -/
def Inv2 (env : Env) (items : List Nat) (keys : Nat) (lens : List Nat) (ret top : Word) (regs : Reg → Word)
    (m : MachineState) (s : Word) (k : Nat) (R : Reg → Word) (M : MachineState) : Prop :=
  Ctx env items keys lens ret top regs m s R M ∧
    R .x10 = s + 8#64 + BitVec.ofNat 64 (8 * k) ∧ R .x11 = s + 8#64 + BitVec.ofNat 64 keys <<< 3 ∧
    WordsAt M s ((prefixes items keys lens k).map (BitVec.ofNat 64)) ∧ ∀ x ∈ items, key lens x < keys

set_option hygiene false in
/-- One pass of the counting loop's body: its loads as the model's values. -/
local macro "body1" : tactic => `(tactic| (
  rw [hit] at hc_1 hc_2 ⊢
  have hb := hitems _ (List.getElem_mem hj')
  have hlt := (lt_word hb (by have := hLn.1; simp only [Layouts.KVecU16.byteSize] at this; omega)).1 hc_1
  have hL2 := hLn.2 _ hlt
  rw [addr_len _ hb, hL2.1] at hc_2 ⊢
  have hk := (lt_word hL2.2 (by omega)).1 hc_2
  have hkey : key lens items[j] = lens[items[j]] := List.getD_eq_getElem _ _ hlt
  have hcl := counts_length items keys lens j
  rw [addr_start _ (by omega), words_get hC (by omega)] at ⊢))

set_option hygiene false in
/-- The counting store keeps the loop head's memory facts. -/
local macro "store1" : term => `(fresh_store hstk hinv_14 hinv_15 hinv_16 hW hli hLn hll
  (a := s + BitVec.ofNat 64 (8 * (lens[items[j]] + 1)))
  (v := BitVec.ofNat 64 (counts items keys lens j)[lens[items[j]] + 1] + 1#64)
  (by rw [toNat_add_ofNat (by omega)]; omega) (by rw [toNat_add_ofNat (by omega)]; omega))

set_option rv_sym.heap true in
theorem loop1 (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    (hpanic : NoReturn env p L.panicBoundsCheck.idx 0)
    (items : List Nat) (keys : Nat) (lens : List Nat)
    {G : State rvIsa → Prop} {n : Nat} {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame}
    {regs : Reg → Word} {m : MachineState} {s : Word}
    (hstk : env.stackLimit.toNat + 112 ≤ top.toNat) (hal : top.toNat % 16 = 0) (hitems : ∀ x ∈ items, x < 2 ^ 64) (hkeys : keys < 2 ^ 59)
    (hli : env.Live m (regs .x11) (8 * items.length))
    (hll : env.Live m (regs .x14) (Layouts.KVecU16.byteSize * lens.length))
    (hnext : ∀ R M, Inv2 env items keys lens ret top regs m s 0 R M →
      rvIsa.SafeN p sp1Ctx G n Q ⟨⟨i, 102, ret, top⟩ :: rest, R, M⟩) :
    ∀ k j R M, j + k + 1 = items.length → Inv1 env items keys lens ret top regs m s j R M →
      rvIsa.SafeN p sp1Ctx G n Q ⟨⟨i, 66, ret, top⟩ :: rest, R, M⟩ := by
  intro k
  induction k with
  | zero =>
    intro j R M hj hinv
    unfold Inv1 Ctx saved at hinv
    have hj' : j < items.length := by omega
    obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hW, hLn, hs1, hs2⟩, -, -, hC, hK⟩ := id hinv
    have hit := words_get hW hj'
    rv_intro hinv
    rv_sym hp with [hL] using [hpanic]
    all_goals body1
    · exact absurd ((rem_zero hj' (by have := hW.1; simp at this; omega)).2 (by omega)) hc
    · apply hnext
      obtain ⟨f1, f2, f3, f4, f5, f6⟩ := store1
      have hjl : items.length = j + 1 := by omega
      refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, f1, f2, f3, f4, f5, hs1, by rw [f6]; exact hs2⟩,
        zero_off s, rfl, ?_, ?_⟩
      · rw [prefixes, List.range'_zero, List.foldl_nil, hjl, counts_succ hj']
        simp only [hkey]
        rw [List.getD_eq_getElem _ _ (by omega), succ_word]
        exact words_set hC (i := lens[items[j]] + 1) (by omega) _
      · intro x hx
        have hx' : x ∈ items.take (j + 1) := by rw [← hjl, List.take_length]; exact hx
        rw [List.take_add_one, List.getElem?_eq_getElem hj', Option.toList_some, List.mem_append,
          List.mem_singleton] at hx'
        rcases hx' with hx' | rfl
        · exact hK x hx'
        · rw [hkey]; exact hk
  | succ k ih =>
    intro j R M hj hinv
    unfold Inv1 Ctx saved at hinv
    have hj' : j < items.length := by omega
    obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hW, hLn, hs1, hs2⟩, -, -, hC, hK⟩ := id hinv
    have hit := words_get hW hj'
    rv_intro hinv
    rv_sym hp with [hL] using [hpanic]
    all_goals body1
    · apply ih (j + 1) _ _ (by omega)
      obtain ⟨f1, f2, f3, f4, f5, f6⟩ := store1
      refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, f1, f2, f3, f4, f5, hs1, by rw [f6]; exact hs2⟩,
        step_ptr _ _, step_rem hj', ?_, ?_⟩
      · rw [counts_succ hj']
        simp only [hkey]
        rw [List.getD_eq_getElem _ _ (by omega), succ_word]
        exact words_set hC (i := lens[items[j]] + 1) (by omega) _
      · intro x hx
        rw [List.take_add_one, List.getElem?_eq_getElem hj', Option.toList_some, List.mem_append,
          List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact hK x hx
        · rw [hkey]; exact hk
    · exact absurd ((rem_zero hj' (by have := hW.1; simp at this; omega)).1 hc) (by omega)

theorem off_hi (s : Word) (j : Nat) : s + 8#64 + BitVec.ofNat 64 (8 * j) = s + BitVec.ofNat 64 (8 * (j + 1)) := by
  rw [BitVec.add_assoc, show 8 * (j + 1) = 8 + 8 * j by omega, BitVec.ofNat_add]

theorem off_lo (s : Word) (j : Nat) :
    s + 8#64 + BitVec.ofNat 64 (8 * j) + 18446744073709551608#64 = s + BitVec.ofNat 64 (8 * j) := by
  rw [BitVec.add_assoc, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 (8 * j)), ← BitVec.add_assoc 8#64,
    show 8#64 + 18446744073709551608#64 = 0#64 by decide, BitVec.zero_add]

theorem off_step (s : Word) (j : Nat) :
    s + BitVec.ofNat 64 (8 * (j + 1)) + 8#64 = s + 8#64 + BitVec.ofNat 64 (8 * (j + 1)) := by
  rw [BitVec.add_assoc, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 (8 * (j + 1)))]

theorem exit2 {s : Word} {j keys : Nat} (hk : keys < 2 ^ 59) (hj : j < keys) :
    s + 8#64 + BitVec.ofNat 64 (8 * j) + 8#64 = s + 8#64 + BitVec.ofNat 64 keys <<< 3 ↔ j + 1 = keys := by
  rw [off_hi, off_step, BitVec.add_right_inj, ← BitVec.toNat_inj, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, Nat.shiftLeft_eq]; omega

theorem add_words (a b : Nat) : BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) :=
  (BitVec.ofNat_add a b).symm

theorem prefixes_succ (items : List Nat) (keys : Nat) (lens : List Nat) (k : Nat) :
    prefixes items keys lens (k + 1) = (prefixes items keys lens k).set (k + 1)
      ((prefixes items keys lens k).getD (k + 1) 0 + (prefixes items keys lens k).getD k 0) := by
  rw [prefixes, List.range'_concat, List.foldl_append]; simp [prefixes, Nat.add_comm]

theorem prefixes_length (items : List Nat) (keys : Nat) (lens : List Nat) (k : Nat) :
    (prefixes items keys lens k).length = keys + 1 := by
  induction k with
  | zero => exact counts_length items keys lens _
  | succ k ih => rw [prefixes_succ, List.length_set, ih]

set_option hygiene false in
/-- One pass of the prefix-sum loop's body: its loads as the model's values. -/
local macro "body2" : tactic => `(tactic| (
  have hpl := prefixes_length items keys lens j
  rw [off_lo, off_hi, words_get hC (i := j) (by omega), words_get hC (i := j + 1) (by omega)] at ⊢))

set_option hygiene false in
/-- The prefix-sum store keeps the loop head's memory facts. -/
local macro "store2" : term => `(fresh_store hstk hinv_14 hinv_15 hinv_16 hW hli hLn hll
  (a := s + BitVec.ofNat 64 (8 * (j + 1)))
  (v := BitVec.ofNat 64 (prefixes items keys lens j)[j + 1] + BitVec.ofNat 64 (prefixes items keys lens j)[j])
  (by rw [toNat_add_ofNat (by omega)]; omega) (by rw [toNat_add_ofNat (by omega)]; omega))

set_option rv_sym.heap true in
/-- **The prefix-sum loop**, from its head with `k + 1` passes to go. -/
theorem loop2 (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (items : List Nat) (keys : Nat) (lens : List Nat)
    {G : State rvIsa → Prop} {n : Nat} {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame}
    {regs : Reg → Word} {m : MachineState} {s : Word}
    (hstk : env.stackLimit.toNat + 112 ≤ top.toNat) (hkeys : keys < 2 ^ 59)
    (hli : env.Live m (regs .x11) (8 * items.length))
    (hll : env.Live m (regs .x14) (Layouts.KVecU16.byteSize * lens.length))
    (hnext : ∀ R M, Inv2 env items keys lens ret top regs m s keys R M →
      rvIsa.SafeN p sp1Ctx G n Q ⟨⟨i, 114, ret, top⟩ :: rest, R, M⟩) :
    ∀ k j R M, j + k + 1 = keys → Inv2 env items keys lens ret top regs m s j R M →
      rvIsa.SafeN p sp1Ctx G n Q ⟨⟨i, 102, ret, top⟩ :: rest, R, M⟩ := by
  intro k
  induction k with
  | zero =>
    intro j R M hj hinv
    unfold Inv2 Ctx saved at hinv
    obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hW, hLn, hs1, hs2⟩, -, -, hC, hK⟩ := id hinv
    rv_intro hinv
    rv_sym hp stop [114]
    all_goals body2
    · exact absurd ((exit2 hkeys (by omega)).2 (by omega)) hc
    · apply hnext
      obtain ⟨f1, f2, f3, f4, f5, f6⟩ := store2
      refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, f1, f2, f3, f4, f5, hs1,
        by rw [f6]; exact hs2⟩, ?_, rfl, ?_, hK⟩
      · have e : keys = j + 1 := by omega
        subst e
        exact off_step s j
      · have e : keys = j + 1 := by omega
        subst e
        rw [prefixes_succ, List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega), add_words]
        exact words_set hC (i := j + 1) (by omega) _
  | succ k ih =>
    intro j R M hj hinv
    unfold Inv2 Ctx saved at hinv
    obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hW, hLn, hs1, hs2⟩, -, -, hC, hK⟩ := id hinv
    rv_intro hinv
    rv_sym hp stop [114]
    all_goals body2
    · apply ih (j + 1) _ _ (by omega)
      obtain ⟨f1, f2, f3, f4, f5, f6⟩ := store2
      refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, f1, f2, f3, f4, f5, hs1,
        by rw [f6]; exact hs2⟩, off_step s j, rfl, ?_, hK⟩
      rw [prefixes_succ, List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega), add_words]
      exact words_set hC (i := j + 1) (by omega) _
    · exact absurd ((exit2 hkeys (by omega)).1 hc) (by omega)

end Rv64mc.Proof.Bytecode.CountingSortUsize
