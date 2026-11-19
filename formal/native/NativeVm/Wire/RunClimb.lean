module

public import NativeVm.Wire.Tables
public import NativeVm.Wire.ModelSpec

/-!
# The climb on the QM machine

`climb` runs `level` for each level below the height (`climb_ok`). A level stores its node count
and points `wSP` at its sibling table (`sibBase`); `pass1` writes each node's key and sibling there,
the level's node beside it (`find`) or else a digest read from the wire, as `sibsM` reads them, and
a flag in `wFL`; `pass2` hashes the parent of each first child into `wPar` (`parent`, as
`parentOf`); `nextLevel` makes the parents the level's nodes. Keys stay below `2^32`, so a lookup on
words is the model's lookup on numbers (`climb_lookup`).
-/

@[expose] public section

namespace NativeVm.Wire

open Native Native.Keccak Native.Keccak.Proof LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Wire
open Native.SphincsVerifier (toNat_toUInt64' toUInt64_add toUInt64_sub toUInt64_shl toUInt64_shr
  imm_nat cond_ltu_reg)

/-! ## Numbers -/

theorem climb_words : wN = 2 ∧ wK = 3 ∧ wSP = 4 ∧ wX = 5 ∧ wH = 8 ∧ wQ = 16 ∧ wFL = 528 ∧
    wNode = 784 ∧ wPar = 2064 ∧ wSibN = 3344 ∧ wSib = 3376 ∧ wLeaf = 44336 ∧ workWords = 60720 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The model's lookup of a key below `2^64` is the first entry whose key has its word. -/
theorem climb_lookup (a : Nat) (ha : a < 2 ^ 64) : ∀ (l : List (Nat × Digest)),
    (∀ x ∈ l, x.1 < 2 ^ 64) →
    (∀ h : (l.map fun x ↦ x.1.toUInt64).idxOf a.toUInt64 < l.length,
      l.lookup a = some (l[(l.map fun x ↦ x.1.toUInt64).idxOf a.toUInt64]'h).2) ∧
    (l.length ≤ (l.map fun x ↦ x.1.toUInt64).idxOf a.toUInt64 → l.lookup a = none)
  | [], _ => ⟨fun h ↦ absurd h (by simp), fun _ ↦ rfl⟩
  | (k, d) :: l, hl => by
    have hk : k < 2 ^ 64 := hl _ List.mem_cons_self
    obtain ⟨ih1, ih2⟩ := climb_lookup a ha l fun x hx ↦ hl x (List.mem_cons_of_mem _ hx)
    by_cases hka : k = a
    · subst hka
      simp
    · have hne : (k.toUInt64 == a.toUInt64) = false := by
        rw [beq_eq_false_iff_ne]
        exact fun h ↦ hka (Native.SphincsVerifier.toUInt64_inj hk ha h)
      have hl' : ((k, d) :: l).lookup a = l.lookup a := by
        rw [List.lookup_cons, beq_eq_false_iff_ne.2 (Ne.symm hka)]
      simp only [List.map_cons, List.idxOf_cons, hne, hl', List.length_cons]
      refine ⟨fun h ↦ ?_, fun h ↦ ih2 (by simp at h; omega)⟩
      rw [ih1 (by simpa using h)]
      simp

theorem climb_put4_out {W : Nat → UInt64} {J k : Nat} {v : Nat → UInt64} (h : k < J ∨ J + 4 ≤ k) :
    put4 W J v k = W k := by
  unfold put4; rw [ite_no (by omega)]

theorem climb_put4_in {W : Nat → UInt64} {J l : Nat} {v : Nat → UInt64} (h : l < 4) :
    put4 W J v (J + l) = v l := by
  unfold put4; rw [ite_yes (by omega), Nat.add_sub_cancel_left]

theorem climb_nodeTab_same {W W' : Nat → UInt64} {b : Nat} {l : List (Nat × Digest)}
    (h : NodeTab W b l) (hW : ∀ k, b ≤ k → k < b + 5 * l.length → W' k = W k) :
    NodeTab W' b l := fun j hj ↦
  ⟨by rw [hW _ (by omega) (by omega)]; exact (h j hj).1,
    fun k hk ↦ by rw [hW _ (by omega) (by omega)]; exact (h j hj).2 k hk⟩

theorem climb_nodeTab_snoc {W W' : Nat → UInt64} {b n : Nat} {l : List (Nat × Digest)}
    {x : Nat × Digest} (h : NodeTab W b l) (hn : l.length = n)
    (hold : ∀ j < n, ∀ k < 5, W' (b + 5 * j + k) = W (b + 5 * j + k))
    (h0 : W' (b + 5 * n) = x.1.toUInt64) (h1 : ∀ k < 4, W' (b + 5 * n + 1 + k) = dw x.2 k) :
    NodeTab W' b (l ++ [x]) := by
  intro j hj
  rw [List.length_append, List.length_singleton] at hj
  rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
  · rw [List.getElem_append_left (by omega)]
    refine ⟨by rw [← Nat.add_zero (b + 5 * j), hold j (by omega) 0 (by omega)]; exact (h j hj).1,
      fun k hk ↦ ?_⟩
    rw [Nat.add_assoc, hold j (by omega) (1 + k) (by omega), ← Nat.add_assoc]
    exact (h j hj).2 k hk
  · rw [List.getElem_append_right (by omega)]
    simp only [hn, Nat.sub_self, List.getElem_singleton]
    exact ⟨h0, h1⟩

theorem climb_xor (a : Nat) (ha : a < 2 ^ 64) :
    a.toUInt64 ^^^ (1 : Int64).toUInt64 = (a ^^^ 1).toUInt64 := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_xor, toNat_toUInt64 ha, show (1 : Int64).toUInt64.toNat = 1 from rfl,
    toNat_toUInt64 (Nat.xor_lt_two_pow ha (by norm_num))]

theorem climb_sibsM_found {B : List UInt8} {nodes : List (Nat × Digest)} {x : Nat × Digest}
    {l : List (Nat × Digest)} {c : Nat} {d : Digest} (h : nodes.lookup (x.1 ^^^ 1) = some d) :
    sibsM B nodes (x :: l) c = (sibsM B nodes l c).map fun p ↦ ((x.1, d, true) :: p.1, p.2) := by
  obtain ⟨v, d0⟩ := x
  rw [sibsM]
  simp only at h
  rw [h]
  cases sibsM B nodes l c <;> rfl

theorem climb_dw (d : Digest) {l : Nat} (hl : l < 4) :
    d.toList[l]'(by simpa using hl) = dw d l := by
  rw [dw, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hl)]
  rfl

/-- Two digests in eight words hold the bytes of the one, then the other's. -/
theorem climb_hashWords {W : Nat → UInt64} {b : Nat} {d1 d2 : Digest}
    (h1 : ∀ l < 4, W (b + l) = dw d1 l) (h2 : ∀ l < 4, W (b + 4 + l) = dw d2 l) :
    (wordsBytes (wordsOf W b ((64 + 7) / 8))).take 64 = digestBytes d1 ++ digestBytes d2 ∧
      HoldsBytes (wordsOf W b ((64 + 7) / 8)) 64 := by
  have hw : wordsOf W b ((64 + 7) / 8) = d1.toList ++ d2.toList := by
    apply List.ext_getElem (by simp [wordsOf])
    intro j hj _
    simp only [wordsOf, List.length_map, List.length_range] at hj
    simp only [wordsOf, List.getElem_map, List.getElem_range]
    by_cases hj4 : j < 4
    · rw [List.getElem_append_left (by simpa using hj4), climb_dw d1 hj4, h1 j hj4]
    · rw [List.getElem_append_right (by simpa using hj4)]
      simp only [Vector.length_toList]
      rw [climb_dw d2 (by omega), ← h2 (j - 4) (by omega)]
      congr 1
      omega
  have hlen : (wordsBytes (d1.toList ++ d2.toList)).length = 64 := by
    rw [length_wordsBytes]; simp
  rw [hw]
  refine ⟨?_, by simp, ?_⟩
  · rw [List.take_of_length_le (by omega)]
    simp [wordsBytes, digestBytes, List.flatMap_append]
  · rw [List.drop_eq_nil_of_le (by omega)]
    simp

theorem climb_sibsM_carried {B : List UInt8} {nodes : List (Nat × Digest)} {x : Nat × Digest}
    {l : List (Nat × Digest)} {c : Nat} (h : nodes.lookup (x.1 ^^^ 1) = none) :
    sibsM B nodes (x :: l) c = if c + 32 ≤ B.length then
      (sibsM B nodes l (c + 32)).map fun p ↦ ((x.1, #v[leAt B c 8, leAt B (c + 8) 8,
        leAt B (c + 16) 8, leAt B (c + 24) 8], false) :: p.1, p.2) else none := by
  obtain ⟨v, d0⟩ := x
  rw [sibsM]
  simp only at h
  rw [h]
  unfold rdDigest
  by_cases hc : c + 32 ≤ B.length
  · rw [ite_yes hc, ite_yes hc]
    simp only [Option.bind_eq_bind, Option.bind_some]
    cases sibsM B nodes l (c + 32) <;> rfl
  · rw [ite_no hc, ite_no hc]
    rfl

theorem climbM_succ {B : List UInt8} {h : Nat} {nodes : List (Nat × Digest)} {c : Nat} :
    climbM B (h + 1) nodes c = (sibsM B nodes nodes c).bind fun p ↦
      (climbM B h (parentsOf nodes p.1) p.2).map fun q ↦
        (p.1.map (fun s ↦ (s.1, s.2.1)) :: q.1, q.2) := by
  rw [climbM]
  simp only [Option.bind_eq_bind]
  cases sibsM B nodes nodes c with
  | none => rfl
  | some p =>
    simp only [Option.bind_some]
    cases climbM B h (parentsOf nodes p.1) p.2 <;> rfl

theorem climb_parentsOf_length : ∀ (l : List (Nat × Digest)) (m : List (Nat × Digest × Bool)),
    (parentsOf l m).length ≤ l.length
  | [], _ => by simp [parentsOf]
  | _ :: _, [] => by simp [parentsOf]
  | a :: l, b :: m => by
    have := climb_parentsOf_length l m
    have h1 : (parentOf a b).length ≤ 1 := by unfold parentOf; split <;> simp
    simp only [parentsOf, List.zip_cons_cons, List.flatMap_cons, List.length_append,
      List.length_cons] at this ⊢
    omega

theorem climb_parentsOf_lt {l : List (Nat × Digest)} (m : List (Nat × Digest × Bool))
    (hl : ∀ y ∈ l, y.1 < 2 ^ 32) : ∀ x ∈ parentsOf l m, x.1 < 2 ^ 32 := by
  intro x hx
  simp only [parentsOf, List.mem_flatMap] at hx
  obtain ⟨a, ha, hx⟩ := hx
  have := hl _ (List.of_mem_zip ha).1
  unfold parentOf at hx
  split at hx
  · simp only [List.mem_singleton] at hx
    rw [hx]
    exact lt_of_le_of_lt (Nat.shiftRight_le _ _) this
  · simp at hx

theorem climb_parentsOf_take {nodes : List (Nat × Digest)} {sibs : List (Nat × Digest × Bool)}
    {i : Nat} (hi : i < nodes.length) (hs : i < sibs.length) :
    parentsOf (nodes.take (i + 1)) (sibs.take (i + 1)) =
      parentsOf (nodes.take i) (sibs.take i) ++ parentOf nodes[i] sibs[i] := by
  rw [List.take_add_one, List.take_add_one, List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem hs]
  simp only [parentsOf, Option.toList_some]
  rw [List.zip_append (by simp; omega), List.flatMap_append]
  simp

/-- The flag test of `pass2`: the node is a first child. -/
theorem climb_flagTest {v : Nat} (hv : v < 2 ^ 64) (fl : Bool) :
    ((v.toUInt64 &&& Int64.toUInt64 1 &&& (if fl then (1 : UInt64) else 0)) == 0) =
      decide (v % 2 = 0 ∨ fl = false) := by
  rw [show Int64.toUInt64 1 = (2 ^ 1 - 1 : Nat).toUInt64 from rfl,
    Native.SphincsVerifier.toUInt64_and_mask (by norm_num) hv]
  cases fl
  · simp
  · rw [ite_yes rfl, show (1 : UInt64) = (2 ^ 1 - 1 : Nat).toUInt64 from rfl,
      Native.SphincsVerifier.toUInt64_and_mask (by norm_num) (by omega)]
    by_cases h : v % 2 = 0
    · simp [h]
    · have h1 : v % 2 = 1 := by omega
      simp [h1]

/-! ## Pieces -/

section Pieces

variable {e : Env} (P : Pre e)
include P

variable {s : QState} {D W : Nat → UInt64} {Q F : QState → Prop} {rest : List Stmt}

omit P in
theorem Inv.climbRegs (hI : Inv e s D W) {t : QState} (hm : t.mem = s.mem)
    (hr : t.reg .rdi = s.reg .rdi) : Inv e t D W :=
  ⟨hr.trans hI.rdi, fun a ha ↦ hm ▸ hI.out a ha, fun k hk ↦ hm ▸ hI.scr k hk,
    fun k hk ↦ hm ▸ hI.dec k hk, fun k hk ↦ hm ▸ hI.work k hk⟩

omit P in
theorem climb_mem_rax_rcx {r : Reg64} {l : List Reg64} (ha : .rax ∈ l) (hc : .rcx ∈ l)
    (h : r ∈ [Reg64.rax, .rcx]) : r ∈ l := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl <;> assumption

theorem climb_nodeAddr (hI : Inv e s D W) {i : Nat} (hi : i < 256)
    (hbp : s.reg .rbp = i.toUInt64) :
    WP nodeAddr s (fun s' ↦ Inv e s' D W ∧ s'.reg .rsi = adr e.wk (wNode + 5 * i) ∧
      RegsFrame [.rax, .rsi] s s') F := by
  unfold nodeAddr
  refine blk_load_ctx P hI (eval_cw s hI.rdi cWork) (by decide) P.c10 ?_
  step; step; step; step
  apply WP.blk_nil
  refine ⟨hI.climbRegs (by simp) (by simp), ?_, ?_⟩
  · simp only [QState.setReg_reg, ite_true]
    rw [eval_ix _ _ _ (a := e.wk) (j := 0) (n := 5 * i) (by simp [adr_zero])]
    · congr 1; omega
    · simp only [QState.setReg_reg, reduceCtorEq, ite_true, ite_false, hbp]
      rw [toUInt64_shl (by omega) (by omega), toUInt64_add]
      congr 1; omega
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [hr.1, hr.2]

omit P in
theorem climb_rw {t : QState} {r : Reg64} (k : Nat) (hr : t.reg r = e.wk) :
    (rw r k).eval t = adr e.wk k := by
  rw [eval_rw', hr]; rfl

omit P in
theorem climb_ix {t : QState} {b i : Reg64} {n : Nat} (k : Nat) (hb : t.reg b = e.wk)
    (hi : t.reg i = n.toUInt64) : (ix b i k).eval t = adr e.wk (n + k) := by
  rw [eval_ix t b i (a := e.wk) (j := 0) (by rw [hb, adr_zero]) hi, Nat.zero_add]

omit P in
theorem climb_sibBase {lv : Nat} (hlv : lv < 32) (hr11 : s.reg .r11 = lv.toUInt64)
    (hrcx : s.reg .rcx = e.wk) :
    WP sibBase s (fun s' ↦ s'.mem = s.mem ∧ s'.reg .rax = adr e.wk (wSib + 1280 * lv) ∧
      RegsFrame [.rax, .rdx] s s') F := by
  unfold sibBase
  step; step; step; step; step; step; step
  apply WP.blk_nil
  refine ⟨by simp, ?_, ?_⟩
  · simp only [QState.setReg_reg, reduceCtorEq, ite_true, ite_false, hr11, hrcx]
    rw [toUInt64_shl (by omega) (by omega), toUInt64_shl (by omega) (by omega), toUInt64_add,
      wd_toUInt64, adr, UInt64.add_comm _ e.wk, UInt64.add_assoc, toUInt64_add]
    congr 2
    unfold wSib wSibN wPar wNode wFL wP wQ
    omega
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [hr.1, hr.2]

theorem climb_nextSP (hI : Inv e s D W) {m : Nat} (hm : W wSP = adr e.wk m) :
    WP nextSP s (fun s' ↦ Inv e s' D (Function.update W wSP (adr e.wk (m + 5))) ∧
      RegsFrame [.rax, .rcx] s s') F := by
  unfold nextSP
  refine blk_load_ctx P hI (eval_cw s hI.rdi cWork) (by decide) P.c10 ?_
  have h1 := hI.setReg (d := .rcx) (by decide) e.wk
  refine blk_load_work h1 (k := wSP) (climb_rw _ (by simp)) (by decide) ?_
  step
  refine blk_store_work P (h1.setReg (d := .rax) (by decide) _) (k := wSP)
    (climb_rw (r := .rcx) _ (by simp)) (by decide) fun s' hs' hr ↦ ?_
  apply WP.blk_nil
  refine ⟨?_, ?_⟩
  · convert hs' using 2
    simp only [QState.setReg_reg, ite_true, hm]
    rw [show Int64.toUInt64 40 = (8 * 5 : Nat).toUInt64 from rfl, adr_add]
  · intro r hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
    simp [hr, hr'.1, hr'.2]

/-- A word read from the wire into the entry at `rsi`. -/
theorem climb_rdStore (hI : Inv e s D W) {p J k : Nat} (hp : s.reg .r15 = p.toUInt64)
    (hpL : p + 8 ≤ e.L) (hrsi : s.reg .rsi = adr e.wk J) (hk : J + k < workWords)
    (h : ∀ s', Inv e s' D (Function.update W (J + k) (leAt e.B p 8)) →
      s'.reg .r15 = (p + 8).toUInt64 → RegsFrame [.rax, .rbx, .rcx, .rdx, .r15] s s' →
      WP (blk rest) s' Q F) :
    WP (blk (rdLE 8 :: I (.store (rw .rsi k) .rbx) :: rest)) s Q F := by
  apply WP.blk_cons
  refine WP.mono (rdLE_ok P hI (by norm_num) le_rfl hp hpL) (fun s1 ⟨h1, hb, hr, hf⟩ ↦ ?_)
    (fun _ h ↦ h)
  have hsi : s1.reg .rsi = adr e.wk J := by rw [hf .rsi (by simp), hrsi]
  refine blk_store_work P h1 (eval_rw s1 .rsi hsi k) hk fun s2 h2 hr2 ↦ ?_
  rw [hb] at h2
  exact h s2 h2 (by rw [hr2, hr]) fun r hr' ↦ by rw [hr2]; exact hf r hr'

/-- **A node's sibling**: the level's node beside it, found by `find`, or else the next digest of
the wire; the flag says which. -/
theorem climb_sib (hI : Inv e s D W) {nodes : List (Nat × Digest)} {x : Nat × Digest}
    {l : List (Nat × Digest)} {i J c : Nat} (hn : nodes.length ≤ 256)
    (hk : ∀ y ∈ nodes, y.1 < 2 ^ 32) (hx : x.1 < 2 ^ 32) (hN : NodeTab W wNode nodes)
    (hi : i < 256) (hJ : wSib ≤ J) (hJ' : J + 5 ≤ wLeaf) (hsp : W wSP = adr e.wk J)
    (hrcx : s.reg .rcx = ((nodes.map fun y ↦ y.1.toUInt64).idxOf (x.1 ^^^ 1).toUInt64).toUInt64)
    (hr9 : s.reg .r9 = nodes.length.toUInt64)
    (hr8 : s.reg .r8 =
      adr e.wk (wNode + 5 * (nodes.map fun y ↦ y.1.toUInt64).idxOf (x.1 ^^^ 1).toUInt64))
    (hbp : s.reg .rbp = i.toUInt64) (hp : s.reg .r15 = c.toUInt64) (hc : c ≤ e.L) :
    WP (.ite (.cmp .ltu .rcx (.reg .r9))
      (blk [I (.load .rsi (cw cWork)), I (.load .rsi (rw .rsi wSP)), copy4 .r8 1 .rsi 1,
        I (.load .rax (cw cWork)), I (.storei (ix .rax .rbp wFL) 1)])
      (blk [needI 32, I (.load .rsi (cw cWork)), I (.load .rsi (rw .rsi wSP)),
        rdLE 8, I (.store (rw .rsi 1) .rbx), rdLE 8, I (.store (rw .rsi 2) .rbx),
        rdLE 8, I (.store (rw .rsi 3) .rbx), rdLE 8, I (.store (rw .rsi 4) .rbx),
        I (.load .rax (cw cWork)), I (.storei (ix .rax .rbp wFL) 0)])) s
      (fun s' ↦ ∃ dg fl c', sibsM e.B nodes (x :: l) c =
        (sibsM e.B nodes l c').map (fun p ↦ ((x.1, dg, fl) :: p.1, p.2)) ∧ c' ≤ e.L ∧
        Inv e s' D (Function.update (put4 W (J + 1) (dw dg)) (wFL + i) (if fl then 1 else 0)) ∧
        s'.reg .r15 = c'.toUInt64 ∧ RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r15] s s')
      (fun s' ↦ sibsM e.B nodes (x :: l) c = none ∧ Kept e s') := by
  obtain ⟨hw1, hw2, hw3, hw4, hw5, hw6, hw7, hw8, hw9, hw10, hw11, hw12, hw13⟩ := climb_words
  have hL := P.L32
  have hx1 : x.1 ^^^ 1 < 2 ^ 64 := lt_of_lt_of_le (Nat.xor_lt_two_pow hx (by norm_num))
    (by norm_num)
  obtain ⟨hfound, hnone⟩ := climb_lookup (x.1 ^^^ 1) hx1 nodes
    fun y hy ↦ lt_of_lt_of_le (hk y hy) (by norm_num)
  set idx := (nodes.map fun y ↦ y.1.toUInt64).idxOf (x.1 ^^^ 1).toUInt64 with hidx
  have hidxn : idx ≤ nodes.length := by
    have := List.idxOf_le_length (l := nodes.map fun y ↦ y.1.toUInt64) (a := (x.1 ^^^ 1).toUInt64)
    rwa [List.length_map] at this
  apply WP.ite
  rw [cond_ltu_reg hrcx hr9 (by omega) (by omega)]
  by_cases hlt : idx < nodes.length
  · rw [decide_eq_true hlt]
    simp only [ite_true]
    have hlk := hfound hlt
    refine blk_load_ctx P hI (eval_cw s hI.rdi cWork) (by decide) P.c10 ?_
    have h1 := hI.setReg (d := .rsi) (by decide) e.wk
    refine blk_load_work h1 (k := wSP) (climb_rw (r := .rsi) _ (by simp)) (by omega) ?_
    rw [QState.setReg_setReg_same]
    have h2 := hI.setReg (d := .rsi) (by decide) (W wSP)
    apply WP.blk_cons
    refine WP.mono (copy4_work P (D := D) (W := W) h2 (src := .r8) (dst := .rsi) (i := 1)
      (j := 1) (J := J) (A := adr e.wk (wNode + 5 * idx)) (v := dw (nodes[idx]'(by
        simpa using hlt)).2) (by decide) (by decide) (by simp [hr8]) (by simp [hsp]) (by omega)
      (fun l hl ↦ ?_) (fun l hl l' hl' he ↦ ?_)) (fun s1 ⟨h3, hf3, _⟩ ↦ ?_) (fun _ h ↦ h)
    · rw [adr_add, ← Nat.add_assoc, h2.work (wNode + 5 * idx + 1 + l) (by omega),
        (hN idx hlt).2 l hl]
    · rw [adr_add] at he
      have := adr_inj P.fk (k := wNode + 5 * idx + (1 + l)) (j := J + 1 + l') (by omega)
        (by omega) he
      omega
    have hf3' : ∀ r, r ≠ .rax → r ≠ .rsi → s1.reg r = s.reg r := fun r h h' ↦ by
      rw [hf3 r (by simp [h])]; simp [h']
    refine blk_load_ctx P h3 (eval_cw s1 h3.rdi cWork) (by decide) P.c10 ?_
    have h4 := h3.setReg (d := .rax) (by decide) e.wk
    refine blk_storei_work P h4 (k := wFL + i) (by
        rw [climb_ix (e := e) (b := .rax) (i := .rbp) (n := i) _ (by simp) (by
          simp [hf3' .rbp (by decide) (by decide), hbp]), Nat.add_comm]) (by omega)
      fun s5 h5 hr5 ↦ WP.blk_nil ⟨nodes[idx].2, true, c, ?_, hc, h5, ?_, ?_⟩
    · rw [climb_sibsM_found hlk]
    · rw [hr5]; simp [hf3' .r15 (by decide) (by decide), hp]
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [hr5]
      simp only [QState.setReg_reg, hr.1, ite_false]
      exact hf3' r hr.1 hr.2.2.2.2.1
  · rw [decide_eq_false hlt]
    simp only [Bool.false_eq_true, ite_false]
    have hlk := hnone (by omega)
    apply WP.blk_cons
    refine WP.mono (needI_ok P hI (p := c) hp hc (n := 32) (by norm_num))
      (fun s1 ⟨hn1, h1, hf1⟩ ↦ ?_) (fun s1 ⟨hn1, hk1⟩ ↦ ⟨?_, hk1⟩)
    swap
    · rw [climb_sibsM_carried hlk, B_length P, ite_no (by omega)]
    have hf1' : ∀ r, r ≠ .rax → s1.reg r = s.reg r := fun r h ↦ hf1 r (by simp [h])
    refine blk_load_ctx P h1 (eval_cw s1 h1.rdi cWork) (by decide) P.c10 ?_
    have h2 := h1.setReg (d := .rsi) (by decide) e.wk
    refine blk_load_work h2 (k := wSP) (climb_rw (e := e) (r := .rsi) _ (by simp)) (by omega) ?_
    rw [QState.setReg_setReg_same]
    have h3 := h1.setReg (d := .rsi) (by decide) (W wSP)
    refine climb_rdStore P h3 (p := c) (J := J) (k := 1)
      (by simp [hf1' .r15 (by decide), hp]) (by omega) (by simp [hsp]) (by omega)
      fun s4 h4 hp4 hf4 ↦ ?_
    have hs4 : s4.reg .rsi = adr e.wk J := by rw [hf4 .rsi (by simp)]; simp [hsp]
    refine climb_rdStore P h4 (p := c + 8) (J := J) (k := 2) hp4 (by omega) hs4 (by omega)
      fun s5 h5 hp5 hf5 ↦ ?_
    have hs5 : s5.reg .rsi = adr e.wk J := by rw [hf5 .rsi (by simp), hs4]
    refine climb_rdStore P h5 (p := c + 8 + 8) (J := J) (k := 3) hp5 (by omega) hs5 (by omega)
      fun s6 h6 hp6 hf6 ↦ ?_
    have hs6 : s6.reg .rsi = adr e.wk J := by rw [hf6 .rsi (by simp), hs5]
    refine climb_rdStore P h6 (p := c + 8 + 8 + 8) (J := J) (k := 4) hp6 (by omega) hs6
      (by omega) fun s7 h7 hp7 hf7 ↦ ?_
    have hf7' : ∀ r, r ∉ [.rax, .rbx, .rcx, .rdx, .rsi, .r15] → s7.reg r = s.reg r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      have hr' : r ∉ [Reg64.rax, .rbx, .rcx, .rdx, .r15] := by simp [hr.1, hr.2.1, hr.2.2.1,
        hr.2.2.2.1, hr.2.2.2.2.2]
      rw [hf7 r hr', hf6 r hr', hf5 r hr', hf4 r hr']
      simp only [QState.setReg_reg, hr.2.2.2.2.1, ite_false]
      exact hf1' r hr.1
    refine blk_load_ctx P h7 (eval_cw s7 h7.rdi cWork) (by decide) P.c10 ?_
    refine blk_storei_work P (h7.setReg (d := .rax) (by decide) e.wk) (k := wFL + i) (by
        rw [climb_ix (e := e) (b := .rax) (i := .rbp) (n := i) _ (by simp) (by
          simp [hf7' .rbp (by simp), hbp]), Nat.add_comm]) (by omega)
      fun s8 h8 hr8 ↦ WP.blk_nil ⟨#v[leAt e.B c 8, leAt e.B (c + 8) 8, leAt e.B (c + 16) 8,
        leAt e.B (c + 24) 8], false, c + 32, ?_, by omega, ?_, ?_, ?_⟩
    · rw [climb_sibsM_carried hlk, B_length P, ite_yes (by omega)]
    · rw [← put4_eq]
      exact h8
    · rw [hr8]
      simp only [QState.setReg_reg, reduceCtorEq, ite_false, hp7]
    · intro r hr
      rw [hr8]
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [QState.setReg_reg, hr.1, ite_false]
      exact hf7' r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2])

omit P in
/-- `pass1` after `i` nodes, from `s` and the working area `W`: the siblings `pre` read so far, the
wire at `ci`. -/
def climbP1 (e : Env) (D W : Nat → UInt64) (nodes : List (Nat × Digest)) (SB c : Nat)
    (s t : QState) (i : Nat) : Prop :=
  ∃ pre ci Wt, i ≤ nodes.length ∧ pre.length = i ∧ ci ≤ e.L ∧ Inv e t D Wt ∧
    sibsM e.B nodes nodes c =
      (sibsM e.B nodes (nodes.drop i) ci).map (fun p ↦ (pre ++ p.1, p.2)) ∧
    pre.map (·.1) = (nodes.take i).map (·.1) ∧
    NodeTab Wt SB (pre.map fun x ↦ (x.1, x.2.1)) ∧
    (∀ j (hj : j < pre.length), Wt (wFL + j) = if pre[j].2.2 then 1 else 0) ∧
    Wt wSP = adr e.wk (SB + 5 * i) ∧
    Same (fun k ↦ k = wSP ∨ (SB ≤ k ∧ k < SB + 1280) ∨ (wFL ≤ k ∧ k < wNode)) W Wt ∧
    t.reg .rbp = i.toUInt64 ∧ t.reg .r9 = nodes.length.toUInt64 ∧ t.reg .r15 = ci.toUInt64 ∧
    RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r9, .rbp, .r15] s t

theorem climb_pass1_body {nodes : List (Nat × Digest)} {SB c i : Nat} {t : QState}
    (hn : nodes.length ≤ 256) (hk : ∀ y ∈ nodes, y.1 < 2 ^ 32) (hN : NodeTab W wNode nodes)
    (hSB : wSib ≤ SB) (hSB' : SB + 1280 ≤ wLeaf) (hinv : climbP1 e D W nodes SB c s t i)
    (hi : i < nodes.length) :
    WP (blk [nodeAddr, I (.load .rax (rw .rsi 0)),
      I (.load .r8 (cw cWork)), I (.load .r8 (rw .r8 wSP)), I (.store (rw .r8 0) .rax),
      I (.xori .rax 1), I (.load .rsi (cw cWork)), I (.addi .rsi (wd wNode)), I (.mov .rdx .r9),
      find 5,
      .ite (.cmp .ltu .rcx (.reg .r9))
        (blk [I (.load .rsi (cw cWork)), I (.load .rsi (rw .rsi wSP)), copy4 .r8 1 .rsi 1,
          I (.load .rax (cw cWork)), I (.storei (ix .rax .rbp wFL) 1)])
        (blk [needI 32, I (.load .rsi (cw cWork)), I (.load .rsi (rw .rsi wSP)),
          rdLE 8, I (.store (rw .rsi 1) .rbx), rdLE 8, I (.store (rw .rsi 2) .rbx),
          rdLE 8, I (.store (rw .rsi 3) .rbx), rdLE 8, I (.store (rw .rsi 4) .rbx),
          I (.load .rax (cw cWork)), I (.storei (ix .rax .rbp wFL) 0)]),
      nextSP, I (.addi .rbp 1)]) t
      (fun t' ↦ climbP1 e D W nodes SB c s t' (i + 1))
      (fun t' ↦ sibsM e.B nodes nodes c = none ∧ Kept e t') := by
  obtain ⟨hw1, hw2, hw3, hw4, hw5, hw6, hw7, hw8, hw9, hw10, hw11, hw12, hw13⟩ := climb_words
  obtain ⟨pre, ci, Wt, hin, hpre, hci, hIt, hmod, hkeys, htab, hfl, hsp, hSame, hbp, hr9, hp, hf⟩ :=
    hinv
  have hL := P.L32
  have hNt : NodeTab Wt wNode nodes := fun j hj ↦ ⟨by rw [hSame _ (by omega)]; exact (hN j hj).1,
    fun k hk ↦ by rw [hSame _ (by omega)]; exact (hN j hj).2 k hk⟩
  have hx : nodes[i].1 < 2 ^ 32 := hk _ (List.getElem_mem _)
  apply WP.blk_cons
  refine WP.mono (climb_nodeAddr P hIt (i := i) (by omega) hbp) (fun t1 ⟨h1, hrsi1, hf1⟩ ↦ ?_)
    (fun _ h ↦ h)
  refine blk_load_work h1 (k := wNode + 5 * i) (by rw [eval_rw t1 .rsi hrsi1 0, Nat.add_zero])
    (by omega) ?_
  rw [(hNt i hi).1]
  refine blk_load_ctx P (h1.setReg (d := .rax) (by decide) _) (eval_cw _ (by simp [h1.rdi]) cWork)
    (by decide) P.c10 ?_
  refine blk_load_work ((h1.setReg (d := .rax) (by decide) _).setReg (d := .r8) (by decide) e.wk)
    (k := wSP) (climb_rw (e := e) (r := .r8) _ (by simp)) (by omega) ?_
  rw [QState.setReg_setReg_same, hsp]
  have h2 := (h1.setReg (d := .rax) (by decide) nodes[i].1.toUInt64).setReg (d := .r8)
    (by decide) (adr e.wk (SB + 5 * i))
  refine blk_store_work P h2 (k := SB + 5 * i)
    (by rw [eval_rw _ .r8 (a := e.wk) (j := SB + 5 * i) (by simp) 0, Nat.add_zero]) (by omega)
    fun t2 h2' hr2 ↦ ?_
  simp only [QState.setReg_reg, reduceCtorEq, ite_true, ite_false] at h2'
  have ht2 : ∀ r, r ≠ .rax → r ≠ .rsi → r ≠ .r8 → t2.reg r = t.reg r := fun r ha hs h8 ↦ by
    rw [hr2]; simp only [QState.setReg_reg, h8, ha, ite_false]; exact hf1 r (by simp [ha, hs])
  have hra2 : t2.reg .rax = nodes[i].1.toUInt64 := by rw [hr2]; simp
  step
  rw [hra2, climb_xor _ (by omega)]
  refine blk_load_ctx P (h2'.setReg (d := .rax) (by decide) _)
    (eval_cw _ (by simp [h2'.rdi]) cWork) (by decide) P.c10 ?_
  step; step
  have h3 := ((h2'.setReg (d := .rax) (by decide) ((nodes[i].1 ^^^ 1).toUInt64)).setReg (d := .rsi)
    (by decide) (e.wk + (wd wNode).toUInt64)).setReg (d := .rdx) (by decide) (t2.reg .r9)
  have hr92 : t2.reg .r9 = nodes.length.toUInt64 := by
    rw [ht2 .r9 (by decide) (by decide) (by decide), hr9]
  apply WP.blk_cons
  refine WP.mono (find_ok h3 (S := 5) (b := wNode) (n := nodes.length)
    (ks := nodes.map fun y ↦ y.1.toUInt64) (key := (nodes[i].1 ^^^ 1).toUInt64) (by norm_num)
    (by simp [wd_toUInt64, adr]) (by simp [hr92]) (by simp) (by simp) (by omega) (fun j hj ↦ ?_))
    (fun t3 ⟨h3', hm3, hrcx3, hrdx3, hr83, hf3⟩ ↦ ?_) (fun _ h ↦ h)
  · simp only [List.length_map] at hj
    rw [Function.update_of_ne (by omega), (hNt j hj).1]
    simp
  have ht3 : ∀ r, r ≠ .rax → r ≠ .rsi → r ≠ .r8 → r ≠ .rbx → r ≠ .rcx → r ≠ .rdx →
      t3.reg r = t.reg r := fun r ha hs h8 hb hc hd ↦ by
    rw [hf3 r (by simp [h8, hb, hc, hd])]
    simp only [QState.setReg_reg, ha, hs, hd, ite_false]
    exact ht2 r ha hs h8
  apply WP.blk_cons
  refine WP.mono (climb_sib P h3' (x := nodes[i]) (l := nodes.drop (i + 1)) (i := i)
    (J := SB + 5 * i) (c := ci) hn hk hx (fun j hj ↦ ?_) (by omega) (by omega) (by omega)
    (by rw [Function.update_of_ne (by omega), hsp]) hrcx3 ?_ hr83 ?_ ?_ hci)
    (fun t4 ⟨dg, fl, c', hmod', hc', h4, hp4, hf4⟩ ↦ ?_)
    (fun t4 ⟨hnone, hk4⟩ ↦ ⟨by rw [hmod, List.drop_eq_getElem_cons hi, hnone]; rfl, hk4⟩)
  · exact ⟨by rw [Function.update_of_ne (by omega)]; exact (hNt j hj).1, fun k hk' ↦ by
      rw [Function.update_of_ne (by omega)]; exact (hNt j hj).2 k hk'⟩
  · rw [ht3 .r9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr9]
  · rw [ht3 .rbp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hbp]
  · rw [ht3 .r15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hp]
  have ht4 : ∀ r, r ∉ [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r15] → t4.reg r = t.reg r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [hf4 r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.2])]
    exact ht3 r hr.1 hr.2.2.2.2.1 hr.2.2.2.2.2.1 hr.2.1 hr.2.2.1 hr.2.2.2.1
  apply WP.blk_cons
  refine WP.mono (climb_nextSP P h4 (m := SB + 5 * i) ?_) (fun t5 ⟨h5, hf5⟩ ↦ ?_) (fun _ h ↦ h)
  · rw [Function.update_of_ne (by omega), climb_put4_out (by omega),
      Function.update_of_ne (by omega), hsp]
  have ht5 : ∀ r, r ∉ [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r15] → t5.reg r = t.reg r := by
    intro r hr
    rw [hf5 r (fun h ↦ hr (climb_mem_rax_rcx (by simp) (by simp) h)), ht4 r hr]
  step
  apply WP.blk_nil
  refine ⟨pre ++ [(nodes[i].1, dg, fl)], c', _, by omega, by simp [hpre], hc',
    h5.setReg (by decide) _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hmod, List.drop_eq_getElem_cons hi, hmod', Option.map_map]
    cases sibsM e.B nodes (List.drop (i + 1) nodes) c' <;> simp
  · rw [List.map_append, hkeys, List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some,
      List.map_append]
    rfl
  · rw [List.map_append]
    refine climb_nodeTab_snoc (n := i) htab (by simp [hpre]) (fun j hj k hk ↦ ?_) ?_
      (fun k hk ↦ ?_)
    · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        climb_put4_out (by omega), Function.update_of_ne (by omega)]
    · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        climb_put4_out (by omega), Function.update_self]
    · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        climb_put4_in hk]
  · intro j hj
    rw [List.length_append, List.length_singleton] at hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · rw [List.getElem_append_left hj, Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), climb_put4_out (by omega),
        Function.update_of_ne (by omega)]
      exact hfl j hj
    · rw [Function.update_of_ne (by omega)]
      simp [List.getElem_append_right, hpre]
  · rw [Function.update_self]
    congr 1
  · intro k hk
    rw [← hSame k hk]
    simp only [Function.update_apply, put4]
    split_ifs <;> first | rfl | (exfalso; omega)
  · simp only [QState.setReg_reg, ite_true]
    rw [ht5 .rbp (by simp), hbp, show Int64.toUInt64 1 = (1 : Nat).toUInt64 from rfl, toUInt64_add]
  · simp only [QState.setReg_reg, reduceCtorEq, ite_false]
    rw [ht5 .r9 (by simp), hr9]
  · simp only [QState.setReg_reg, reduceCtorEq, ite_false]
    rw [hf5 .r15 (by simp), hp4]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [QState.setReg_reg, hr.2.2.2.2.2.2.2.1, ite_false]
    rw [ht5 r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.2])]
    exact hf r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2])

/-- **`pass1`**: each node's key and sibling into the sibling table at `SB`, each flag into `wFL`,
the carried siblings read as `sibsM` reads them. -/
theorem climb_pass1 (hI : Inv e s D W) {nodes : List (Nat × Digest)} {SB c : Nat}
    (hn : nodes.length ≤ 256) (hk : ∀ y ∈ nodes, y.1 < 2 ^ 32) (hN : NodeTab W wNode nodes)
    (hWN : W wN = nodes.length.toUInt64) (hSB : wSib ≤ SB) (hSB' : SB + 1280 ≤ wLeaf)
    (hsp : W wSP = adr e.wk SB) (hp : s.reg .r15 = c.toUInt64) (hc : c ≤ e.L) :
    WP pass1 s (fun s' ↦ ∃ sibs c' W', sibsM e.B nodes nodes c = some (sibs, c') ∧ c' ≤ e.L ∧
      Inv e s' D W' ∧ sibs.map (·.1) = nodes.map (·.1) ∧
      NodeTab W' SB (sibs.map fun x ↦ (x.1, x.2.1)) ∧
      (∀ j (hj : j < sibs.length), W' (wFL + j) = if sibs[j].2.2 then 1 else 0) ∧
      Same (fun k ↦ k = wSP ∨ (SB ≤ k ∧ k < SB + 1280) ∨ (wFL ≤ k ∧ k < wNode)) W W' ∧
      s'.reg .r15 = c'.toUInt64 ∧ s'.reg .r9 = nodes.length.toUInt64 ∧
      RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r9, .rbp, .r15] s s')
      (fun s' ↦ sibsM e.B nodes nodes c = none ∧ Kept e s') := by
  unfold pass1
  step
  refine blk_load_ctx P (hI.setReg (d := .rbp) (by decide) _)
    (eval_cw _ (by simp [hI.rdi]) cWork) (by decide) P.c10 ?_
  refine blk_load_work ((hI.setReg (d := .rbp) (by decide) _).setReg (d := .rcx) (by decide) e.wk)
    (k := wN) (climb_rw (e := e) (r := .rcx) _ (by simp)) (by decide) ?_
  rw [hWN]
  apply WP.blk_cons
  refine WP.mono (WP.loop (fun t ↦ ∃ i, climbP1 e D W nodes SB c s t i)
    (fun t ↦ (t.reg .r9).toNat - (t.reg .rbp).toNat)
    ⟨0, [], c, W, by omega, rfl, hc, ?_, ?_, by simp, fun j hj ↦ absurd hj (by simp),
      fun j hj ↦ absurd hj (by simp), by simp [hsp], Same.refl _ _, by simp; rfl, by simp,
      by simp [hp], ?_⟩ ?_ ?_) (fun _ h ↦ WP.blk_nil h) (fun _ h ↦ h)
  · exact ((hI.setReg (by decide) _).setReg (by decide) _).setReg (by decide) _
  · rw [List.drop_zero]
    cases sibsM e.B nodes nodes c <;> rfl
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [hr.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1]
  · intro t ⟨i, hinv⟩ hcnd
    obtain ⟨_, _, _, hin, _, _, _, _, _, _, _, _, _, hbp, hr9, _, _⟩ := id hinv
    rw [cond_ltu_reg hbp hr9 (by omega) (by omega), decide_eq_true_eq] at hcnd
    refine WP.mono (climb_pass1_body P hn hk hN hSB hSB' hinv hcnd) (fun t' h' ↦ ⟨⟨i + 1, h'⟩, ?_⟩)
      (fun _ h ↦ h)
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hbp', hr9', _, _⟩ := id h'
    rw [hbp, hr9, hbp', hr9', toNat_toUInt64 (by omega), toNat_toUInt64 (by omega),
      toNat_toUInt64 (by omega)]
    omega
  · intro t ⟨i, pre, ci, Wt, hin, hpre, hci, hIt, hmod, hkeys, htab, hfl, hsp, hSame, hbp, hr9,
      hp', hf⟩ hcnd
    rw [cond_ltu_reg hbp hr9 (by omega) (by omega), decide_eq_false_iff_not] at hcnd
    have hin' : i = nodes.length := by omega
    subst hin'
    refine ⟨pre, ci, Wt, ?_, hci, hIt, ?_, htab, hfl, hSame, hp', hr9, hf⟩
    · rw [hmod, List.drop_length]
      simp [sibsM]
    · rw [hkeys, List.take_length]

/-- Two digests of entries at `a` and `b` into the words `wH` a parent hashes. -/
theorem climb_copy8 (hI : Inv e s D W) {A B : Reg64} (hA : A ≠ .rax) (hB : B ≠ .rax) {a b : Nat}
    {da db : Digest} (hra : s.reg A = adr e.wk a) (hrb : s.reg B = adr e.wk b)
    (hrcx : s.reg .rcx = e.wk) (ha : a + 5 ≤ workWords) (hb : b + 5 ≤ workWords) (ha' : wQ ≤ a)
    (hb' : wQ ≤ b) (hda : ∀ l < 4, W (a + 1 + l) = dw da l)
    (hdb : ∀ l < 4, W (b + 1 + l) = dw db l) :
    WP (blk [copy4 A 1 .rcx wH, copy4 B 1 .rcx (wH + 4)]) s
      (fun s' ↦ ∃ W', Inv e s' D W' ∧ (∀ l < 4, W' (wH + l) = dw da l) ∧
        (∀ l < 4, W' (wH + 4 + l) = dw db l) ∧ Same (fun k ↦ wH ≤ k ∧ k < wQ) W W' ∧
        RegsFrame [.rax] s s') F := by
  obtain ⟨hw1, hw2, hw3, hw4, hw5, hw6, hw7, hw8, hw9, hw10, hw11, hw12, hw13⟩ := climb_words
  have hrcx' : s.reg .rcx = adr e.wk 0 := by rw [hrcx, adr_zero]
  apply WP.blk_cons
  refine WP.mono (copy4_work P hI (src := A) (dst := .rcx) (i := 1) (j := wH) (J := 0)
    (A := adr e.wk a) (v := dw da) hA (by decide) hra hrcx' (by omega) (fun l hl ↦ ?_)
    (fun l hl l' hl' he ↦ ?_)) (fun s1 ⟨h1, hf1, _⟩ ↦ ?_) (fun _ h ↦ h)
  · rw [adr_add, ← Nat.add_assoc, hI.work (a + 1 + l) (by omega), hda l hl]
  · rw [adr_add] at he
    have := adr_inj P.fk (k := a + (1 + l)) (j := 0 + wH + l') (by omega) (by omega) he
    omega
  apply WP.blk_cons
  refine WP.mono (copy4_work P h1 (src := B) (dst := .rcx) (i := 1) (j := wH + 4) (J := 0)
    (A := adr e.wk b) (v := dw db) hB (by decide) (by rw [hf1 B (by simp [hB]), hrb])
    (by rw [hf1 .rcx (by simp), hrcx']) (by omega) (fun l hl ↦ ?_)
    (fun l hl l' hl' he ↦ ?_)) (fun s2 ⟨h2, hf2, _⟩ ↦ ?_) (fun _ h ↦ h)
  · rw [adr_add, ← Nat.add_assoc, h1.work (b + 1 + l) (by omega), climb_put4_out (by omega),
      hdb l hl]
  · rw [adr_add] at he
    have := adr_inj P.fk (k := b + (1 + l)) (j := 0 + (wH + 4) + l') (by omega) (by omega) he
    omega
  apply WP.blk_nil
  refine ⟨_, h2, fun l hl ↦ ?_, fun l hl ↦ ?_, fun k hk ↦ ?_, RegsFrame.trans hf1 hf2⟩
  · simp only [Nat.zero_add]
    rw [climb_put4_out (by omega), climb_put4_in hl]
  · simp only [Nat.zero_add]
    rw [climb_put4_in hl]
  · rw [climb_put4_out (by omega), climb_put4_out (by omega)]

omit P in
/-- `rbx :=` the next parents entry, `wK` its index. -/
theorem climb_parAddr (hI : Inv e s D W) {K : Nat} (hrcx : s.reg .rcx = e.wk)
    (hK : W wK = K.toUInt64) (hK' : K < 256)
    (h : ∀ t, Inv e t D W → t.mem = s.mem → t.reg .rbx = adr e.wk (wPar + 5 * K) →
      (∀ r, r ≠ .rax → r ≠ .rbx → t.reg r = s.reg r) → WP (blk rest) t Q F) :
    WP (blk (I (.load .rax (rw .rcx wK)) :: I (.mov .rbx .rax) :: I (.shli .rbx 2) ::
      I (.add .rbx .rax) :: I (.lea .rbx (ix .rcx .rbx wPar)) :: rest)) s Q F := by
  refine blk_load_work hI (k := wK) (climb_rw (e := e) (r := .rcx) _ hrcx) (by decide) ?_
  rw [hK]
  step; step; step; step
  refine h _ (hI.climbRegs (by simp) (by simp)) (by simp) ?_ fun r ha hb ↦ by simp [ha, hb]
  simp only [QState.setReg_reg, ite_true]
  rw [climb_ix (e := e) (b := .rcx) (i := .rbx) (n := 5 * K) _ (by simp [hrcx]) (by
    simp only [QState.setReg_reg, reduceCtorEq, ite_true, ite_false]
    rw [toUInt64_shl (by omega) (by omega), toUInt64_add]
    congr 1; omega)]
  congr 1; omega

/-- **`parent`**: the parent of the node at `rsi` (key `v`, digest `dn`) and its sibling (digest
`ds`, at `wSP`), the left child's digest first, into the next parents entry, `wK` advanced. -/
theorem climb_parent (hI : Inv e s D W) {NB J K v : Nat} {dn ds : Digest}
    (hrsi : s.reg .rsi = adr e.wk NB) (hrdx : s.reg .rdx = v.toUInt64) (hv : v < 2 ^ 32)
    (hsp : W wSP = adr e.wk J) (hK : W wK = K.toUInt64) (hK' : K < 256) (hNB : wQ ≤ NB)
    (hNB' : NB + 5 ≤ wPar) (hJ : wSib ≤ J) (hJ' : J + 5 ≤ wLeaf)
    (hdn : ∀ l < 4, W (NB + 1 + l) = dw dn l) (hds : ∀ l < 4, W (J + 1 + l) = dw ds l) :
    WP parent s (fun s' ↦ ∃ W', Inv e s' D W' ∧ W' wK = (K + 1).toUInt64 ∧
      W' (wPar + 5 * K) = (v >>> 1).toUInt64 ∧
      (∀ l < 4, W' (wPar + 5 * K + 1 + l) = dw (keccak256 (if v % 2 = 0 then
        digestBytes dn ++ digestBytes ds else digestBytes ds ++ digestBytes dn)) l) ∧
      Same (fun k ↦ k = wK ∨ (wH ≤ k ∧ k < wQ) ∨ (wPar + 5 * K ≤ k ∧ k < wPar + 5 * K + 5)) W W' ∧
      RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8] s s') F := by
  obtain ⟨hw1, hw2, hw3, hw4, hw5, hw6, hw7, hw8, hw9, hw10, hw11, hw12, hw13⟩ := climb_words
  unfold parent
  refine blk_load_ctx P hI (eval_cw s hI.rdi cWork) (by decide) P.c10 ?_
  refine blk_load_work (hI.setReg (d := .r8) (by decide) e.wk) (k := wSP)
    (climb_rw (e := e) (r := .r8) _ (by simp)) (by omega) ?_
  rw [QState.setReg_setReg_same, hsp]
  refine blk_load_ctx P (hI.setReg (d := .r8) (by decide) _) (eval_cw _ (by simp [hI.rdi]) cWork)
    (by decide) P.c10 ?_
  have h0 := (hI.setReg (d := .r8) (by decide) (adr e.wk J)).setReg (d := .rcx) (by decide) e.wk
  apply WP.blk_cons
  refine WP.mono (P := fun s1 ↦ ∃ W2, Inv e s1 D W2 ∧
      (∀ l < 4, W2 (wH + l) = dw (if v % 2 = 0 then dn else ds) l) ∧
      (∀ l < 4, W2 (wH + 4 + l) = dw (if v % 2 = 0 then ds else dn) l) ∧
      Same (fun k ↦ wH ≤ k ∧ k < wQ) W W2 ∧
      RegsFrame [.rax] ((s.setReg .r8 (adr e.wk J)).setReg .rcx e.wk) s1) ?_
    (fun s1 ⟨W2, h1, hw1', hw2', hS2, hf1⟩ ↦ ?_) (fun _ h ↦ h)
  · apply WP.ite
    have hc : (Cond.test true .rdx (.imm 1)).eval ((s.setReg .r8 (adr e.wk J)).setReg .rcx e.wk) =
        decide (v % 2 = 0) := by
      simp only [Cond.eval, Rhs.eval, QState.setReg_reg, reduceCtorEq, ite_false, hrdx]
      rw [show Int64.toUInt64 1 = (2 ^ 1 - 1 : Nat).toUInt64 from rfl,
        Native.SphincsVerifier.toUInt64_and_mask (by norm_num) (by omega)]
      by_cases h : v % 2 = 0
      · simp [h]
      · have h1 : v % 2 = 1 := by omega
        simp [h1]
    rw [hc]
    by_cases hev : v % 2 = 0
    · rw [decide_eq_true hev, ite_yes rfl]
      refine WP.mono (climb_copy8 P h0 (A := .rsi) (B := .r8) (by decide) (by decide)
        (by simp [hrsi]) (by simp) (by simp) (by omega) (by omega) (by omega) (by omega) hdn hds)
        (fun s1 ⟨W2, h1, hw1', hw2', hS2, hf1⟩ ↦ ⟨W2, h1, ?_, ?_, hS2, hf1⟩) (fun _ h ↦ h)
      · rw [ite_yes hev]; exact hw1'
      · rw [ite_yes hev]; exact hw2'
    · rw [decide_eq_false hev]
      simp only [Bool.false_eq_true, ite_false]
      refine WP.mono (climb_copy8 P h0 (A := .r8) (B := .rsi) (by decide) (by decide)
        (by simp) (by simp [hrsi]) (by simp) (by omega) (by omega) (by omega) (by omega) hds hdn)
        (fun s1 ⟨W2, h1, hw1', hw2', hS2, hf1⟩ ↦ ⟨W2, h1, ?_, ?_, hS2, hf1⟩) (fun _ h ↦ h)
      · rw [ite_no hev]; exact hw1'
      · rw [ite_no hev]; exact hw2'
  have hs1 : ∀ r, r ≠ .rax → s1.reg r = ((s.setReg .r8 (adr e.wk J)).setReg .rcx e.wk).reg r :=
    fun r h ↦ hf1 r (by simp [h])
  have hrcx1 : s1.reg .rcx = e.wk := by rw [hs1 .rcx (by decide)]; simp
  have hrdx1 : s1.reg .rdx = v.toUInt64 := by rw [hs1 .rdx (by decide)]; simp [hrdx]
  have hK2 : W2 wK = K.toUInt64 := by rw [hS2 wK (by omega), hK]
  step
  rw [hrdx1, toUInt64_shr (by omega) (by omega), show v / 2 ^ 1 = v >>> 1 from
    (Nat.shiftRight_eq_div_pow v 1).symm]
  refine climb_parAddr (h1.setReg (d := .rdx) (by decide) _) (by simp [hrcx1]) hK2 hK'
    fun t2 h2 hm2 hrbx2 hf2 ↦ ?_
  refine blk_store_work P h2 (k := wPar + 5 * K) (by rw [eval_rw t2 .rbx hrbx2 0, Nat.add_zero])
    (by omega) fun s3 h3 hr3 ↦ ?_
  rw [hf2 .rdx (by decide) (by decide)] at h3
  simp only [QState.setReg_reg, ite_true] at h3
  have hrcx3 : s3.reg .rcx = e.wk := by
    rw [hr3, hf2 .rcx (by decide) (by decide)]; simp [hrcx1]
  step; step
  obtain ⟨hhash, hz⟩ := climb_hashWords (W := Function.update W2 (wPar + 5 * K)
    (v >>> 1).toUInt64) (b := wH) (d1 := if v % 2 = 0 then dn else ds)
    (d2 := if v % 2 = 0 then ds else dn)
    (fun l hl ↦ by rw [Function.update_of_ne (by omega), hw1' l hl])
    (fun l hl ↦ by rw [Function.update_of_ne (by omega), hw2' l hl])
  apply WP.blk_cons
  refine WP.mono (hashCall_ok P ((h3.setReg (d := .rsi) (by decide) _).setReg (d := .rbx)
    (by decide) _) (b := wH) (len := 64) (by simp [climb_rw (e := e) (r := .rcx) _ hrcx3])
    (by simp; rfl) (by norm_num) (by omega) hz) (fun s4 ⟨h4, hscr, hf4⟩ ↦ ?_) (fun _ h ↦ h)
  rw [hhash] at hscr
  have hK4 : Function.update W2 (wPar + 5 * K) (v >>> 1).toUInt64 wK = K.toUInt64 := by
    rw [Function.update_of_ne (by omega), hK2]
  refine blk_load_ctx P h4 (eval_cw s4 h4.rdi cWork) (by decide) P.c10 ?_
  refine climb_parAddr (h4.setReg (d := .rcx) (by decide) e.wk) (by simp) hK4 hK'
    fun t5 h5 hm5 hrbx5 hf5 ↦ ?_
  apply WP.blk_cons
  refine WP.mono (copy4_work P h5 (src := .rdi) (dst := .rbx) (i := cScr) (j := 1)
    (J := wPar + 5 * K) (A := e.x) (v := dw (keccak256 (digestBytes (if v % 2 = 0 then dn else ds)
      ++ digestBytes (if v % 2 = 0 then ds else dn)))) (by decide) (by decide) h5.rdi hrbx5
    (by omega) (fun l hl ↦ ?_) (fun l hl l' hl' ↦ ?_)) (fun s6 ⟨h6, hf6, _⟩ ↦ ?_) (fun _ h ↦ h)
  · rw [hm5]
    simp only [QState.setReg_mem]
    rw [show e.x + (8 * (cScr + l)).toUInt64 = adr e.x (cScr + l) from rfl, hscr l hl,
      ← climb_dw _ hl, Vector.getElem_toList]
  · exact P.scr_ne_work (by unfold scratchWords; omega) (by omega)
  refine blk_load_ctx P h6 (eval_cw s6 h6.rdi cWork) (by decide) P.c10 ?_
  refine blk_load_work (h6.setReg (d := .rcx) (by decide) e.wk) (k := wK)
    (climb_rw (e := e) (r := .rcx) _ (by simp)) (by omega) ?_
  step
  refine blk_store_work P ((h6.setReg (d := .rcx) (by decide) e.wk).setReg (d := .rax)
    (by decide) _)
    (k := wK) (climb_rw (e := e) (r := .rcx) _ (by simp)) (by omega) fun s7 h7 hr7 ↦ ?_
  apply WP.blk_nil
  refine ⟨_, h7, ?_, ?_, fun l hl ↦ ?_, fun k hk ↦ ?_, ?_⟩
  · rw [Function.update_self]
    simp only [QState.setReg_reg, ite_true]
    rw [climb_put4_out (by omega), hK4, show Int64.toUInt64 1 = (1 : Nat).toUInt64 from rfl,
      toUInt64_add]
  · rw [Function.update_of_ne (by omega), climb_put4_out (by omega), Function.update_self]
  · rw [Function.update_of_ne (by omega), climb_put4_in hl]
    by_cases hev : v % 2 = 0
    · simp only [hev, ite_true]
    · simp only [hev, ite_false]
  · rw [Function.update_of_ne (by omega), climb_put4_out (by omega),
      Function.update_of_ne (by omega), hS2 k (by omega)]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨ha, hb, hc, hd, hsi, h8⟩ := hr
    rw [hr7]
    simp only [QState.setReg_reg, ha, hc, ite_false]
    rw [hf6 r (by simp [ha]), hf5 r ha hb]
    simp only [QState.setReg_reg, hc, ite_false]
    rw [hf4 r (by simp [ha, hb, hc, hd, hsi, h8])]
    simp only [QState.setReg_reg, hb, hsi, ite_false]
    rw [hr3, hf2 r ha hb]
    simp only [QState.setReg_reg, hd, ite_false]
    rw [hs1 r ha]
    simp [hc, h8]

omit P in
/-- `pass2` after `i` nodes, from `s` and the working area `W`. -/
def climbP2 (e : Env) (D W : Nat → UInt64) (nodes : List (Nat × Digest))
    (sibs : List (Nat × Digest × Bool)) (SB : Nat) (s t : QState) (i : Nat) : Prop :=
  ∃ Wt, i ≤ nodes.length ∧ Inv e t D Wt ∧
    NodeTab Wt wPar (parentsOf (nodes.take i) (sibs.take i)) ∧
    Wt wK = (parentsOf (nodes.take i) (sibs.take i)).length.toUInt64 ∧
    Wt wSP = adr e.wk (SB + 5 * i) ∧
    Same (fun k ↦ k = wK ∨ k = wSP ∨ (wH ≤ k ∧ k < wQ) ∨ (wPar ≤ k ∧ k < wSibN)) W Wt ∧
    t.reg .rbp = i.toUInt64 ∧ t.reg .r9 = nodes.length.toUInt64 ∧
    RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .rbp] s t

theorem climb_pass2_body {nodes : List (Nat × Digest)} {sibs : List (Nat × Digest × Bool)}
    {SB i : Nat} {t : QState} (hn : nodes.length ≤ 256) (hk : ∀ y ∈ nodes, y.1 < 2 ^ 32)
    (hlen : sibs.length = nodes.length) (hSB : wSib ≤ SB) (hSB' : SB + 1280 ≤ wLeaf)
    (hN : NodeTab W wNode nodes) (hS : NodeTab W SB (sibs.map fun x ↦ (x.1, x.2.1)))
    (hfl : ∀ j (hj : j < sibs.length), W (wFL + j) = if sibs[j].2.2 then 1 else 0)
    (hinv : climbP2 e D W nodes sibs SB s t i) (hi : i < nodes.length) :
    WP (blk [nodeAddr, I (.load .rdx (rw .rsi 0)),
      I (.load .rcx (cw cWork)), I (.load .rax (ix .rcx .rbp wFL)),
      I (.mov .rbx .rdx), I (.andi .rbx 1), I (.and .rbx .rax),
      .ite (.test true .rbx (.reg .rbx)) parent .skip,
      nextSP, I (.addi .rbp 1)]) t (fun t' ↦ climbP2 e D W nodes sibs SB s t' (i + 1)) F := by
  obtain ⟨hw1, hw2, hw3, hw4, hw5, hw6, hw7, hw8, hw9, hw10, hw11, hw12, hw13⟩ := climb_words
  obtain ⟨Wt, hin, hIt, htab, hK, hsp, hSame, hbp, hr9, hf⟩ := hinv
  have hpl : (parentsOf (nodes.take i) (sibs.take i)).length ≤ i :=
    le_trans (climb_parentsOf_length _ _) (by simp)
  have hsi : i < sibs.length := by omega
  have hWt : ∀ k, (wFL ≤ k ∧ k < wPar) ∨ (wSib ≤ k ∧ k < wLeaf) → Wt k = W k :=
    fun k hk ↦ hSame k (by omega)
  have hv : nodes[i].1 < 2 ^ 32 := hk _ (List.getElem_mem _)
  apply WP.blk_cons
  refine WP.mono (climb_nodeAddr P hIt (i := i) (by omega) hbp) (fun t1 ⟨h1, hrsi1, hf1⟩ ↦ ?_)
    (fun _ h ↦ h)
  refine blk_load_work h1 (k := wNode + 5 * i) (by rw [eval_rw t1 .rsi hrsi1 0, Nat.add_zero])
    (by omega) ?_
  rw [hWt _ (by omega), (hN i hi).1]
  refine blk_load_ctx P (h1.setReg (d := .rdx) (by decide) _)
    (eval_cw _ (by simp [h1.rdi]) cWork) (by decide) P.c10 ?_
  refine blk_load_work ((h1.setReg (d := .rdx) (by decide) _).setReg (d := .rcx) (by decide) e.wk)
    (k := wFL + i) (by
      rw [climb_ix (e := e) (b := .rcx) (i := .rbp) (n := i) _ (by simp) (by
        simp [hf1 .rbp (by simp), hbp]), Nat.add_comm]) (by omega) ?_
  rw [hWt _ (by omega), hfl i hsi]
  step; step; step
  have hI2 := (((h1.setReg (d := .rdx) (by decide) nodes[i].1.toUInt64).setReg (d := .rcx)
    (by decide) e.wk).setReg (d := .rax) (by decide) (if sibs[i].2.2 then 1 else 0)).setReg
    (d := .rbx) (by decide) (nodes[i].1.toUInt64 &&& Int64.toUInt64 1 &&&
      (if sibs[i].2.2 then 1 else 0))
  apply WP.blk_cons
  refine WP.mono (P := fun t2 ↦ ∃ W2, Inv e t2 D W2 ∧
      NodeTab W2 wPar (parentsOf (nodes.take i) (sibs.take i) ++ parentOf nodes[i] sibs[i]) ∧
      W2 wK =
        (parentsOf (nodes.take i) (sibs.take i) ++ parentOf nodes[i] sibs[i]).length.toUInt64 ∧
      W2 wSP = Wt wSP ∧
      Same (fun k ↦ k = wK ∨ (wH ≤ k ∧ k < wQ) ∨ (wPar ≤ k ∧ k < wSibN)) Wt W2 ∧
      ∀ r, r ∉ [.rax, .rbx, .rcx, .rdx, .rsi, .r8] → t2.reg r = t.reg r) ?_
    (fun t2 ⟨W2, h2, htab2, hK2, hsp2, hS2, hf2⟩ ↦ ?_) (fun _ h ↦ h)
  · apply WP.ite
    have hc : ∀ t' : QState, t'.reg .rbx = (nodes[i].1.toUInt64 &&& Int64.toUInt64 1 &&&
        (if sibs[i].2.2 then 1 else 0)) → (Cond.test true .rbx (.reg .rbx)).eval t' =
        decide (nodes[i].1 % 2 = 0 ∨ sibs[i].2.2 = false) := fun t' h ↦ by
      simp only [Cond.eval, Rhs.eval, h, UInt64.and_self]
      rw [climb_flagTest (by omega)]
      simp
    rw [hc _ (by simp)]
    have hreg : ∀ r, r ∉ [.rax, .rbx, .rcx, .rdx, .rsi, .r8] →
        ((((t1.setReg .rdx nodes[i].1.toUInt64).setReg .rcx e.wk).setReg .rax
          (if sibs[i].2.2 then 1 else 0)).setReg .rbx (nodes[i].1.toUInt64 &&& Int64.toUInt64 1 &&&
          (if sibs[i].2.2 then 1 else 0))).reg r = t.reg r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [QState.setReg_reg, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, ite_false]
      exact hf1 r (by simp [hr.1, hr.2.2.2.2.1])
    by_cases hpc : nodes[i].1 % 2 = 0 ∨ sibs[i].2.2 = false
    · rw [decide_eq_true hpc, ite_yes rfl]
      have hpo : parentOf nodes[i] sibs[i] = [(nodes[i].1 >>> 1, keccak256
          (if nodes[i].1 % 2 = 0 then digestBytes nodes[i].2 ++ digestBytes sibs[i].2.1
          else digestBytes sibs[i].2.1 ++ digestBytes nodes[i].2))] := by
        unfold parentOf; rw [ite_yes hpc]
      rw [hpo]
      refine WP.mono (climb_parent P hI2 (NB := wNode + 5 * i) (J := SB + 5 * i)
        (K := (parentsOf (nodes.take i) (sibs.take i)).length) (v := nodes[i].1)
        (dn := nodes[i].2) (ds := sibs[i].2.1) (by simp [hrsi1]) (by simp) hv hsp hK (by omega)
        (by omega) (by omega) (by omega) (by omega)
        (fun l hl ↦ by rw [hWt _ (by omega), (hN i hi).2 l hl]) (fun l hl ↦ ?_))
        (fun t2 ⟨W', h2, hK2, hP0, hP1, hS2, hf2⟩ ↦ ⟨W', h2, ?_, ?_, ?_, ?_, ?_⟩) (fun _ h ↦ h)
      · rw [hWt _ (by omega)]
        have := (hS i (by simpa using hsi)).2 l hl
        simpa using this
      · exact climb_nodeTab_snoc htab rfl (fun j hj k hk ↦ hS2 _ (by omega)) hP0 hP1
      · simp [hK2]
      · exact hS2 wSP (by omega)
      · exact Same.mono hS2 fun k hk ↦ by omega
      · intro r hr
        rw [hf2 r hr, hreg r hr]
    · rw [decide_eq_false hpc]
      simp only [Bool.false_eq_true, ite_false]
      have hpo : parentOf nodes[i] sibs[i] = [] := by unfold parentOf; rw [ite_no hpc]
      rw [hpo, List.append_nil]
      exact WP.skip ⟨Wt, hI2, htab, hK, rfl, Same.refl _ _, hreg⟩
  apply WP.blk_cons
  refine WP.mono (climb_nextSP P h2 (m := SB + 5 * i) (by rw [hsp2, hsp]))
    (fun t3 ⟨h3, hf3⟩ ↦ ?_) (fun _ h ↦ h)
  have ht3 : ∀ r, r ∉ [.rax, .rbx, .rcx, .rdx, .rsi, .r8] → t3.reg r = t.reg r := fun r hr ↦ by
    rw [hf3 r (fun h ↦ hr (climb_mem_rax_rcx (by simp) (by simp) h)), hf2 r hr]
  step
  apply WP.blk_nil
  refine ⟨_, by omega, h3.setReg (by decide) _, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [climb_parentsOf_take hi hsi]
    exact climb_nodeTab_same htab2 fun k hk _ ↦ Function.update_of_ne (by omega) _ _
  · rw [Function.update_of_ne (by omega), climb_parentsOf_take hi hsi, hK2]
  · rw [Function.update_self]
    congr 1
  · refine Same.update (Same.trans hSame (Same.mono hS2 fun k hk ↦ by omega)) (by simp) _
  · simp only [QState.setReg_reg, ite_true]
    rw [ht3 .rbp (by simp), hbp, show Int64.toUInt64 1 = (1 : Nat).toUInt64 from rfl, toUInt64_add]
  · simp only [QState.setReg_reg, reduceCtorEq, ite_false]
    rw [ht3 .r9 (by simp), hr9]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨ha, hb, hc, hd, hsi', h8, hbp'⟩ := hr
    simp only [QState.setReg_reg, hbp', ite_false]
    rw [ht3 r (by simp [ha, hb, hc, hd, hsi', h8])]
    exact hf r (by simp [ha, hb, hc, hd, hsi', h8, hbp'])

/-- **`pass2`**: the parents of the level's first children into `wPar`, as `parentsOf`, their count
in `wK`. -/
theorem climb_pass2 (hI : Inv e s D W) {nodes : List (Nat × Digest)}
    {sibs : List (Nat × Digest × Bool)} {lv : Nat} (hn : nodes.length ≤ 256)
    (hk : ∀ y ∈ nodes, y.1 < 2 ^ 32) (hlen : sibs.length = nodes.length) (hlv : lv < 32)
    (hr11 : s.reg .r11 = lv.toUInt64) (hr9 : s.reg .r9 = nodes.length.toUInt64)
    (hN : NodeTab W wNode nodes)
    (hS : NodeTab W (wSib + 1280 * lv) (sibs.map fun x ↦ (x.1, x.2.1)))
    (hfl : ∀ j (hj : j < sibs.length), W (wFL + j) = if sibs[j].2.2 then 1 else 0) :
    WP pass2 s (fun s' ↦ ∃ W', Inv e s' D W' ∧ NodeTab W' wPar (parentsOf nodes sibs) ∧
      W' wK = (parentsOf nodes sibs).length.toUInt64 ∧
      Same (fun k ↦ k = wK ∨ k = wSP ∨ (wH ≤ k ∧ k < wQ) ∨ (wPar ≤ k ∧ k < wSibN)) W W' ∧
      RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .rbp] s s') F := by
  obtain ⟨hw1, hw2, hw3, hw4, hw5, hw6, hw7, hw8, hw9, hw10, hw11, hw12, hw13⟩ := climb_words
  unfold pass2
  step
  refine blk_load_ctx P (hI.setReg (d := .rbp) (by decide) _)
    (eval_cw _ (by simp [hI.rdi]) cWork) (by decide) P.c10 ?_
  refine blk_storei_work P ((hI.setReg (d := .rbp) (by decide) _).setReg (d := .rcx) (by decide)
    e.wk) (k := wK) (climb_rw (e := e) (r := .rcx) _ (by simp)) (by decide) fun s1 h1 hr1 ↦ ?_
  apply WP.blk_cons
  refine WP.mono (climb_sibBase (e := e) (lv := lv) hlv (by rw [hr1]; simp [hr11])
    (by rw [hr1]; simp)) (fun s2 ⟨hm2, hrax2, hf2⟩ ↦ ?_) (fun _ h ↦ h)
  have h2 := h1.climbRegs hm2 (hf2 .rdi (by simp))
  refine blk_store_work P h2 (k := wSP) (climb_rw (e := e) (r := .rcx) _ (by
    rw [hf2 .rcx (by simp), hr1]; simp)) (by decide) fun s3 h3 hr3 ↦ ?_
  rw [hrax2] at h3
  have hs3 : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rbp → r ≠ .rcx → s3.reg r = s.reg r :=
    fun r ha hd hb hc ↦ by
      rw [hr3, hf2 r (by simp [ha, hd]), hr1]; simp [hb, hc]
  apply WP.blk_cons
  refine WP.mono (WP.loop (fun t ↦ ∃ i, climbP2 e D W nodes sibs (wSib + 1280 * lv) s t i)
    (fun t ↦ (t.reg .r9).toNat - (t.reg .rbp).toNat)
    ⟨0, _, by omega, h3, by simp [parentsOf, NodeTab], ?_, ?_, ?_, ?_, ?_, ?_⟩ ?_ ?_)
    (fun _ h ↦ WP.blk_nil h) (fun _ h ↦ h)
  · rw [Function.update_of_ne (by omega), Function.update_self]
    rfl
  · rw [Function.update_self]
    simp
  · exact Same.update (Same.update (Same.refl _ _) (by simp) _) (by simp) _
  · rw [hr3, hf2 .rbp (by simp), hr1]; simp; rfl
  · rw [hs3 .r9 (by decide) (by decide) (by decide) (by decide), hr9]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    exact hs3 r hr.1 hr.2.2.2.1 hr.2.2.2.2.2.2 hr.2.2.1
  · intro t ⟨i, hinv⟩ hcnd
    obtain ⟨_, hin, _, _, _, _, _, hbp, hr9', _⟩ := id hinv
    rw [cond_ltu_reg hbp hr9' (by omega) (by omega), decide_eq_true_eq] at hcnd
    refine WP.mono (climb_pass2_body P hn hk hlen (by omega) (by omega) hN hS hfl hinv hcnd)
      (fun t' h' ↦ ⟨⟨i + 1, h'⟩, ?_⟩) (fun _ h ↦ h)
    obtain ⟨_, _, _, _, _, _, _, hbp', hr9'', _⟩ := id h'
    rw [hbp, hr9', hbp', hr9'', toNat_toUInt64 (by omega), toNat_toUInt64 (by omega),
      toNat_toUInt64 (by omega)]
    omega
  · intro t ⟨i, Wt, hin, hIt, htab, hK, _, hSame, hbp, hr9', hf⟩ hcnd
    rw [cond_ltu_reg hbp hr9' (by omega) (by omega), decide_eq_false_iff_not] at hcnd
    have hin' : i = nodes.length := by omega
    subst hin'
    rw [List.take_length, ← hlen, List.take_length] at htab hK
    exact ⟨Wt, hIt, htab, hK, hSame, hf⟩

/-- **`nextLevel`**: the parents become the level's nodes. -/
theorem climb_nextLevel (hI : Inv e s D W) {ps : List (Nat × Digest)}
    (hK : W wK = ps.length.toUInt64) (hn : ps.length ≤ 256) (hP : NodeTab W wPar ps) :
    WP nextLevel s (fun s' ↦ ∃ W', Inv e s' D W' ∧ W' wN = ps.length.toUInt64 ∧
      NodeTab W' wNode ps ∧ Same (fun k ↦ k = wN ∨ (wNode ≤ k ∧ k < wPar)) W W' ∧
      RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi] s s') F := by
  obtain ⟨hw1, hw2, hw3, hw4, hw5, hw6, hw7, hw8, hw9, hw10, hw11, hw12, hw13⟩ := climb_words
  unfold nextLevel
  refine blk_load_ctx P hI (eval_cw s hI.rdi cWork) (by decide) P.c10 ?_
  refine blk_load_work (hI.setReg (d := .rcx) (by decide) e.wk) (k := wK)
    (climb_rw (e := e) (r := .rcx) _ (by simp)) (by decide) ?_
  rw [hK]
  refine blk_store_work P ((hI.setReg (d := .rcx) (by decide) e.wk).setReg (d := .rdx) (by decide)
    _) (k := wN) (climb_rw (e := e) (r := .rcx) _ (by simp)) (by decide) fun s1 h1 hr1 ↦ ?_
  simp only [QState.setReg_reg, ite_true] at h1
  step; step; step; step; step
  apply WP.blk_cons
  refine WP.mono (copyWords_work P (h1.climbRegs (by simp) (by simp)) (a := wPar) (d := wNode)
    (n := 5 * ps.length) ?_ ?_ ?_ (by omega) (by omega) (by omega))
    (fun s2 ⟨h2, hf2⟩ ↦ WP.blk_nil ⟨_, h2, ?_, ?_, ?_, ?_⟩) (fun _ h ↦ h)
  · simp only [QState.setReg_reg, reduceCtorEq, ite_true, ite_false]
    exact climb_rw (e := e) _ (by simp [hr1])
  · simp only [QState.setReg_reg, reduceCtorEq, ite_true, ite_false]
    exact climb_rw (e := e) _ (by simp [hr1])
  · simp only [QState.setReg_reg, reduceCtorEq, ite_true, ite_false, hr1]
    rw [toUInt64_shl (by omega) (by omega), toUInt64_add]
    congr 1; omega
  · unfold copied
    rw [ite_no (by omega), Function.update_self]
  · intro j hj
    unfold copied
    refine ⟨?_, fun k hk ↦ ?_⟩
    · rw [ite_yes (by omega), Function.update_of_ne (by omega),
        show wPar + (wNode + 5 * j - wNode) = wPar + 5 * j by omega]
      exact (hP j hj).1
    · rw [ite_yes (by omega), Function.update_of_ne (by omega),
        show wPar + (wNode + 5 * j + 1 + k - wNode) = wPar + 5 * j + 1 + k by omega]
      exact (hP j hj).2 k hk
  · intro k hk
    unfold copied
    rw [ite_no (by omega), Function.update_of_ne (by omega)]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [hf2 r (by simp [hr.1, hr.2.1, hr.2.2.2.1, hr.2.2.2.2])]
    simp only [QState.setReg_reg, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false, hr1]

/-- **A level**: its node count and its nodes with their siblings kept, read as `sibsM` reads
them; its parents become the level's nodes. -/
theorem climb_level (hI : Inv e s D W) {nodes : List (Nat × Digest)} {lv c : Nat}
    (hn : nodes.length ≤ 256) (hk : ∀ y ∈ nodes, y.1 < 2 ^ 32) (hN : NodeTab W wNode nodes)
    (hWN : W wN = nodes.length.toUInt64) (hlv : lv < 32) (hr11 : s.reg .r11 = lv.toUInt64)
    (hp : s.reg .r15 = c.toUInt64) (hc : c ≤ e.L) :
    WP level s (fun s' ↦ ∃ sibs c' W', sibsM e.B nodes nodes c = some (sibs, c') ∧ c' ≤ e.L ∧
      Inv e s' D W' ∧ sibs.map (·.1) = nodes.map (·.1) ∧
      W' (wSibN + lv) = nodes.length.toUInt64 ∧
      NodeTab W' (wSib + 1280 * lv) (sibs.map fun x ↦ (x.1, x.2.1)) ∧
      W' wN = (parentsOf nodes sibs).length.toUInt64 ∧ NodeTab W' wNode (parentsOf nodes sibs) ∧
      Same (fun k ↦ (wN ≤ k ∧ k < wX) ∨ (wH ≤ k ∧ k < wQ) ∨ (wFL ≤ k ∧ k < wSibN) ∨
        k = wSibN + lv ∨ (wSib + 1280 * lv ≤ k ∧ k < wSib + 1280 * lv + 1280)) W W' ∧
      s'.reg .r15 = c'.toUInt64 ∧
      RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r9, .rbp, .r15] s s')
      (fun s' ↦ sibsM e.B nodes nodes c = none ∧ Kept e s') := by
  obtain ⟨hw1, hw2, hw3, hw4, hw5, hw6, hw7, hw8, hw9, hw10, hw11, hw12, hw13⟩ := climb_words
  unfold level
  refine blk_load_ctx P hI (eval_cw s hI.rdi cWork) (by decide) P.c10 ?_
  refine blk_load_work (hI.setReg (d := .rcx) (by decide) e.wk) (k := wN)
    (climb_rw (e := e) (r := .rcx) _ (by simp)) (by decide) ?_
  rw [hWN]
  refine blk_store_work P ((hI.setReg (d := .rcx) (by decide) e.wk).setReg (d := .rax) (by decide)
    _) (k := wSibN + lv) (by
      rw [climb_ix (e := e) (b := .rcx) (i := .r11) (n := lv) _ (by simp) (by simp [hr11]),
        Nat.add_comm]) (by omega) fun s1 h1 hr1 ↦ ?_
  simp only [QState.setReg_reg, ite_true] at h1
  have hs1 : ∀ r, r ≠ .rax → r ≠ .rcx → s1.reg r = s.reg r := fun r ha hc ↦ by
    rw [hr1]; simp [ha, hc]
  apply WP.blk_cons
  refine WP.mono (climb_sibBase (e := e) (lv := lv) hlv
    (by rw [hs1 .r11 (by decide) (by decide), hr11]) (by rw [hr1]; simp))
    (fun s2 ⟨hm2, hrax2, hf2⟩ ↦ ?_) (fun _ h ↦ h)
  have h2 := h1.climbRegs hm2 (hf2 .rdi (by simp))
  refine blk_store_work P h2 (k := wSP) (climb_rw (e := e) (r := .rcx) _ (by
    rw [hf2 .rcx (by simp), hr1]; simp)) (by decide) fun s3 h3 hr3 ↦ ?_
  rw [hrax2] at h3
  have hs3 : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → s3.reg r = s.reg r := fun r ha hc hd ↦ by
    rw [hr3, hf2 r (by simp [ha, hd]), hs1 r ha hc]
  have hN2 : NodeTab (Function.update (Function.update W (wSibN + lv) nodes.length.toUInt64) wSP
      (adr e.wk (wSib + 1280 * lv))) wNode nodes := climb_nodeTab_same hN fun k hk hk' ↦ by
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  apply WP.blk_cons
  refine WP.mono (climb_pass1 P h3 (SB := wSib + 1280 * lv) (c := c) hn hk hN2
    (by rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hWN]) (by omega)
    (by omega) (Function.update_self ..) (by rw [hs3 .r15 (by decide) (by decide) (by decide), hp])
    hc) (fun s4 ⟨sibs, c', W3, hm, hc', h4, hkeys, htab, hfl, hS3, hp4, hr94, hf4⟩ ↦ ?_)
    (fun _ h ↦ h)
  have hlen : sibs.length = nodes.length := by
    simpa using congrArg List.length hkeys
  have hN3 : NodeTab W3 wNode nodes := climb_nodeTab_same hN2 fun k hk hk' ↦ hS3 _ (by omega)
  apply WP.blk_cons
  refine WP.mono (climb_pass2 P h4 (lv := lv) hn hk hlen hlv
    (by rw [hf4 .r11 (by simp), hs3 .r11 (by decide) (by decide) (by decide), hr11]) hr94 hN3 htab
    hfl) (fun s5 ⟨W4, h5, hP, hK, hS4, hf5⟩ ↦ ?_) (fun _ h ↦ h)
  have hpl : (parentsOf nodes sibs).length ≤ 256 :=
    le_trans (climb_parentsOf_length _ _) hn
  apply WP.blk_cons
  refine WP.mono (climb_nextLevel P h5 hK hpl hP)
    (fun s6 ⟨W5, h6, hN5, hNT, hS5, hf6⟩ ↦ WP.blk_nil ⟨sibs, c', W5, hm, hc', h6, hkeys, ?_, ?_,
      hN5, hNT, ?_, ?_, ?_⟩) (fun _ h ↦ h)
  · rw [hS5 _ (by omega), hS4 _ (by omega), hS3 _ (by omega), Function.update_of_ne (by omega),
      Function.update_self]
  · exact climb_nodeTab_same htab fun k hk hk' ↦ by
      simp only [List.length_map, hlen] at hk'
      rw [hS5 _ (by omega), hS4 _ (by omega)]
  · intro k hk
    rw [hS5 _ (by omega), hS4 _ (by omega), hS3 _ (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega)]
  · rw [hf6 .r15 (by simp), hf5 .r15 (by simp), hp4]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨ha, hb, hc, hd, hsi, h8, h9, hbp, h15⟩ := hr
    rw [hf6 r (by simp [ha, hb, hc, hd, hsi]), hf5 r (by simp [ha, hb, hc, hd, hsi, h8, hbp]),
      hf4 r (by simp [ha, hb, hc, hd, hsi, h8, h9, hbp, h15]), hs3 r ha hc hd]

end Pieces

section

variable {e : Env} (P : Pre e)
include P
variable {s : QState} {D W : Nat → UInt64} {F : QState → Prop}

theorem climb_ok (hI : Inv e s D W) {c h : Nat} {ps : List Nat} {nodes : List (Nat × Digest)}
    (hp : s.reg .r15 = c.toUInt64) (hc : c ≤ e.L) (hr13 : s.reg .r13 = h.toUInt64)
    (hh : h ≤ wireMaxHeight) (hpos : ps.Pairwise (· < ·)) (hn : ps.length ≤ wireMaxQueries)
    (hlt : ∀ p ∈ ps, p < 2 ^ 32) (hkeys : keys nodes = levelNodes ps 0)
    (hN : W wN = nodes.length.toUInt64) (hnodes : NodeTab W wNode nodes) :
    WP climb s (fun s' ↦ ∃ sibs c', climbM e.B h nodes c = some (sibs, c') ∧ ∃ W',
      Inv e s' D W' ∧ (∀ lv < h, W' (wSibN + lv) = (sibs.getD lv []).length.toUInt64 ∧
        (sibs.getD lv []).length ≤ wireMaxQueries ∧ (∀ x ∈ sibs.getD lv [], x.1 < 2 ^ 32) ∧
        NodeTab W' (wSib + 1280 * lv) (sibs.getD lv [])) ∧
      Same (fun k ↦ (wN ≤ k ∧ k < wX) ∨ (wH ≤ k ∧ k < wQ) ∨ (wFL ≤ k ∧ k < wLeaf)) W W' ∧
      s'.reg .r15 = c'.toUInt64 ∧
      RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r9, .r11, .rbp, .r15] s s')
      (fun s' ↦ climbM e.B h nodes c = none ∧ Kept e s') := by
  obtain ⟨hw1, hw2, hw3, hw4, hw5, hw6, hw7, hw8, hw9, hw10, hw11, hw12, hw13⟩ := climb_words
  have hQ : wireMaxQueries = 256 := rfl
  have hH : wireMaxHeight = 32 := rfl
  have hps : levelNodes ps 0 = ps := levelNodes_zero hpos
  have hn0 : nodes.length ≤ 256 := by
    have := congrArg List.length hkeys
    rw [hps, List.length_map] at this
    omega
  have hk0 : ∀ y ∈ nodes, y.1 < 2 ^ 32 := fun y hy ↦ by
    have : y.1 ∈ keys nodes := List.mem_map_of_mem hy
    rw [hkeys, hps] at this
    exact hlt _ this
  unfold climb
  step
  apply WP.blk_cons
  refine WP.mono (WP.loop (fun t ↦ ∃ lv pre nd c' W', lv ≤ h ∧ pre.length = lv ∧ c' ≤ e.L ∧
      Inv e t D W' ∧
      climbM e.B h nodes c = (climbM e.B (h - lv) nd c').map (fun q ↦ (pre ++ q.1, q.2)) ∧
      nd.length ≤ 256 ∧ (∀ y ∈ nd, y.1 < 2 ^ 32) ∧ NodeTab W' wNode nd ∧
      W' wN = nd.length.toUInt64 ∧
      (∀ l < lv, W' (wSibN + l) = (pre.getD l []).length.toUInt64 ∧
        (pre.getD l []).length ≤ wireMaxQueries ∧ (∀ x ∈ pre.getD l [], x.1 < 2 ^ 32) ∧
        NodeTab W' (wSib + 1280 * l) (pre.getD l [])) ∧
      Same (fun k ↦ (wN ≤ k ∧ k < wX) ∨ (wH ≤ k ∧ k < wQ) ∨ (wFL ≤ k ∧ k < wLeaf)) W W' ∧
      t.reg .r11 = lv.toUInt64 ∧ t.reg .r13 = h.toUInt64 ∧ t.reg .r15 = c'.toUInt64 ∧
      RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r9, .r11, .rbp, .r15] s t)
    (fun t ↦ (t.reg .r13).toNat - (t.reg .r11).toNat)
    ⟨0, [], nodes, c, W, by omega, rfl, hc, hI.setReg (by decide) _, ?_, hn0, hk0, hnodes, hN,
      fun l hl ↦ absurd hl (by omega), Same.refl _ _, by simp; rfl, by simp [hr13],
      by simp [hp], ?_⟩ ?_ ?_) (fun _ h ↦ WP.blk_nil h) (fun _ h ↦ h)
  · rw [Nat.sub_zero]
    cases climbM e.B h nodes c <;> rfl
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [hr.2.2.2.2.2.2.2.1]
  · intro t ⟨lv, pre, nd, c', W', hlv, hpre, hc', hIt, hmod, hn', hk', hN', hWN', htabs, hSame,
      hr11, hr13', hp', hf⟩ hcnd
    rw [cond_ltu_reg hr11 hr13' (by omega) (by omega), decide_eq_true_eq] at hcnd
    apply WP.blk_cons
    refine WP.mono (climb_level P hIt hn' hk' hN' hWN' (by omega) hr11 hp' hc')
      (fun t1 ⟨sibs, c'', W'', hm, hc'', h1, hkeys1, hsn, htab, hWN1, hN1, hS1, hp1, hf1⟩ ↦ ?_)
      (fun t1 ⟨hnone, hk1⟩ ↦ ⟨?_, hk1⟩)
    rotate_left
    · rw [hmod, show h - lv = h - (lv + 1) + 1 by omega, climbM_succ, hnone]
      rfl
    have hlen1 : sibs.length = nd.length := by simpa using congrArg List.length hkeys1
    step
    apply WP.blk_nil
    refine ⟨⟨lv + 1, pre ++ [sibs.map fun x ↦ (x.1, x.2.1)], parentsOf nd sibs, c'', W'',
      by omega, by simp [hpre], hc'', h1.setReg (by decide) _, ?_,
      le_trans (climb_parentsOf_length _ _) hn', climb_parentsOf_lt _ hk', hN1, hWN1,
      fun l hl ↦ ?_, Same.trans hSame (Same.mono hS1 fun k hk ↦ by omega), ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [hmod, show h - lv = h - (lv + 1) + 1 by omega, climbM_succ, hm]
      simp only [Option.bind_some, Option.map_map]
      cases climbM e.B (h - (lv + 1)) (parentsOf nd sibs) c'' <;> simp
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hl | rfl
      · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
          ← List.getD_eq_getElem?_getD]
        obtain ⟨h1', h2', h3', h4'⟩ := htabs l hl
        refine ⟨by rw [hS1 _ (by omega), h1'], h2', h3', climb_nodeTab_same h4' fun k hk hk' ↦ ?_⟩
        have : (pre.getD l []).length ≤ 256 := h2'
        exact hS1 _ (by omega)
      · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hpre, Nat.sub_self]
        simp only [List.getElem?_cons_zero, Option.getD_some]
        refine ⟨by rw [hsn, List.length_map, hlen1], by rw [List.length_map, hlen1, hQ]; exact hn',
          fun x hx ↦ ?_, htab⟩
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
        have : y.1 ∈ sibs.map (·.1) := List.mem_map_of_mem hy
        rw [hkeys1] at this
        obtain ⟨z, hz, hzy⟩ := List.mem_map.1 this
        rw [← hzy]
        exact hk' z hz
    · simp only [QState.setReg_reg, ite_true]
      rw [hf1 .r11 (by simp), hr11, show Int64.toUInt64 1 = (1 : Nat).toUInt64 from rfl,
        toUInt64_add]
    · simp only [QState.setReg_reg, reduceCtorEq, ite_false]
      rw [hf1 .r13 (by simp), hr13']
    · simp only [QState.setReg_reg, reduceCtorEq, ite_false]
      exact hp1
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [QState.setReg_reg, hr.2.2.2.2.2.2.2.1, ite_false]
      rw [hf1 r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
        hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2])]
      exact hf r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
        hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2])
    · simp only [QState.setReg_reg, reduceCtorEq, ite_true, ite_false]
      rw [hf1 .r11 (by simp), hf1 .r13 (by simp), hr11, hr13', toNat_toUInt64 (by omega),
        show Int64.toUInt64 1 = (1 : Nat).toUInt64 from rfl, toUInt64_add,
        toNat_toUInt64 (by omega), toNat_toUInt64 (by omega)]
      omega
  · intro t ⟨lv, pre, nd, c', W', hlv, hpre, hc', hIt, hmod, _, _, _, _, htabs, hSame, hr11,
      hr13', hp', hf⟩ hcnd
    rw [cond_ltu_reg hr11 hr13' (by omega) (by omega), decide_eq_false_iff_not] at hcnd
    have hlv' : lv = h := by omega
    subst hlv'
    refine ⟨pre, c', ?_, W', hIt, htabs, hSame, hp', hf⟩
    rw [hmod, Nat.sub_self]
    simp [climbM]

end

end NativeVm.Wire
