module

public import NativeVm.Wire.Tables
public import NativeVm.Wire.ModelSpec

/-!
# The openings

`output_ok`: `output` writes each query's opening to the phase's area of the decoded area, as
`openingOf` gives it: the query, the leaf at its position among the distinct positions (`find 1`,
then `copyWords_dec`), and at each level the sibling of the node it is under, looked up in the
level's table (`output_pathStep_ok`, `output_path_ok`), zeros if none. `find` returns the first
entry with the key as `List.lookup` does (`lookup_found`, `lookup_none`), keys below `2^32`.
-/

@[expose] public section

namespace NativeVm.Wire

open Native Native.Keccak Native.Keccak.Proof LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Wire
open Native.SphincsVerifier (toNat_toUInt64' toUInt64_add toUInt64_shl toUInt64_shr toUInt64_inj
  cond_ltu_reg)

/-! ## Lookups -/

private theorem key_ne {a k : Nat} (ha : a < 2 ^ 32) (hk : k < 2 ^ 32) (h : a ≠ k) :
    (a.toUInt64 == k.toUInt64) = false := by
  simpa using fun h' ↦ h (toUInt64_inj (by omega) (by omega) h')

private theorem lookup_found {β : Type} {k : Nat} (hk : k < 2 ^ 32) :
    ∀ (l : List (Nat × β)), (∀ x ∈ l, x.1 < 2 ^ 32) → ∀ i (hi : i < l.length),
      (l.map fun x ↦ x.1.toUInt64).idxOf k.toUInt64 = i → l.lookup k = some l[i].2
  | [], _, _, hi, _ => absurd hi (by simp)
  | (a, b) :: l, hl, i, hi, hidx => by
    rw [List.map_cons, List.idxOf_cons] at hidx
    by_cases hab : a = k
    · subst hab
      simp only [BEq.rfl, ite_true] at hidx
      subst hidx
      simp
    · rw [key_ne (hl _ (by simp)) hk hab] at hidx
      simp only [Bool.false_eq_true, ite_false] at hidx
      subst hidx
      rw [List.lookup_cons, show (k == a) = false by simpa using Ne.symm hab]
      exact lookup_found hk l (fun x hx ↦ hl x (by simp [hx])) _ (by simp at hi; omega) rfl

private theorem lookup_none {β : Type} {k : Nat} (hk : k < 2 ^ 32) :
    ∀ (l : List (Nat × β)), (∀ x ∈ l, x.1 < 2 ^ 32) →
      l.length ≤ (l.map fun x ↦ x.1.toUInt64).idxOf k.toUInt64 → l.lookup k = none
  | [], _, _ => rfl
  | (a, b) :: l, hl, hidx => by
    rw [List.map_cons, List.idxOf_cons] at hidx
    by_cases hab : a = k
    · subst hab
      simp at hidx
    · rw [key_ne (hl _ (by simp)) hk hab] at hidx
      simp only [Bool.false_eq_true, ite_false, List.length_cons] at hidx
      rw [List.lookup_cons, show (k == a) = false by simpa using Ne.symm hab]
      exact lookup_none hk l (fun x hx ↦ hl x (by simp [hx])) (by omega)

private theorem dw_default (l : Nat) : dw default l = 0 := by
  unfold dw
  rw [show (default : Digest).toList = [0, 0, 0, 0] from rfl]
  rcases l with _ | _ | _ | _ | l <;> simp

/-! ## Addresses and states -/

private theorem ev_rw {t : QState} {r : Reg64} {a : UInt64} {j k K : Nat} (hr : t.reg r = adr a j)
    (hK : j + k = K) : (rw r k).eval t = adr a K := by
  rw [eval_rw t r hr, hK]

private theorem ev_ix {t : QState} {b i : Reg64} {a : UInt64} {j n k K : Nat}
    (hb : t.reg b = adr a j) (hi : t.reg i = n.toUInt64) (hK : j + n + k = K) :
    (ix b i k).eval t = adr a K := by
  rw [eval_ix t b i hb hi, hK]

private theorem sib_adr (wk : UInt64) {d : Nat} (hd : d < 32) :
    d.toUInt64 <<< Nat.toUInt64 13 + d.toUInt64 <<< Nat.toUInt64 11 + wk + (wd wSib).toUInt64 =
      adr wk (wSib + 1280 * d) := by
  rw [toUInt64_shl (by omega) (by omega), toUInt64_shl (by omega) (by omega), toUInt64_add,
    wd_toUInt64, adr, UInt64.add_comm _ wk, UInt64.add_assoc, toUInt64_add]
  rw [show d * 2 ^ 13 + d * 2 ^ 11 + 8 * wSib = 8 * (wSib + 1280 * d) by omega]

private theorem inv_of {e : Env} {s t : QState} {D W : Nat → UInt64} (hI : Inv e s D W)
    (hm : t.mem = s.mem) (hr : t.reg .rdi = e.x) : Inv e t D W :=
  ⟨hr, fun a ha ↦ hm ▸ hI.out a ha, fun k hk ↦ hm ▸ hI.scr k hk, hm ▸ hI.dec, hm ▸ hI.work⟩

private theorem ldw {e : Env} {s0 s : QState} {D W : Nat → UInt64} {Q F : QState → Prop}
    {rest : List Stmt} {d : Reg64} {ad : Addr} {k : Nat} (hI : Inv e s0 D W)
    (hm : s.mem = s0.mem) (hr : s.reg .rdi = e.x) (ha : ad.eval s = adr e.wk k)
    (hk : k < workWords) (h : WP (blk rest) (s.setReg d (W k)) Q F) :
    WP (blk (I (.load d ad) :: rest)) s Q F :=
  blk_load_work (inv_of hI hm hr) ha hk h

private theorem wp_gen {c : Stmt} {s : QState} {Q F : QState → Prop}
    (h : ∀ t, t = s → WP c t Q F) : WP c s Q F :=
  h s rfl

private theorem consts : wX = 5 ∧ wQ = 16 ∧ wP = 272 ∧ wFL = 528 ∧ wNode = 784 ∧ wPar = 2064 ∧
    wSibN = 3344 ∧ wSib = 3376 ∧ wLeaf = 44336 ∧ workWords = 60720 ∧ openingWords = 193 ∧
    wireMaxLeafWords = 64 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The openings -/

/-- Opening `j` of the phase at `base` holds the model's opening of the query `q`. -/
private def OpenOk (ps : List Nat) (leaves : List (List K)) (sibs : List (List (Nat × Digest)))
    (h lw base : Nat) (D : Nat → UInt64) (j q : Nat) : Prop :=
  let o := openingOf ps leaves sibs h q
  let ob := base + 3 + j * openingWords
  D ob = o.leafIndex.toUInt64 ∧ (∀ t < lw, D (ob + 1 + t) = (o.leaf.getD t 0).lane) ∧
    ∀ d < h, ∀ l < 4, D (ob + 1 + wireMaxLeafWords + 4 * d + l) = dw (o.path.getD d default) l

/-- An opening is kept by changes to a later opening's words. -/
private theorem openOk_same {ps : List Nat} {leaves : List (List K)}
    {sibs : List (List (Nat × Digest))} {h lw base j j' q : Nat} {D D' : Nat → UInt64}
    (hlw : lw ≤ wireMaxLeafWords) (hh : h ≤ wireMaxHeight) (hj : j' < j)
    (hS : Same (fun k ↦ base + 3 + j * openingWords ≤ k ∧
      k < base + 3 + j * openingWords + openingWords) D D')
    (hO : OpenOk ps leaves sibs h lw base D j' q) : OpenOk ps leaves sibs h lw base D' j' q := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, cOW, cLW⟩ := consts
  have hMH : wireMaxHeight = 32 := rfl
  have hm : j' * openingWords + openingWords ≤ j * openingWords := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hj
  obtain ⟨h1, h2, h3⟩ := hO
  refine ⟨by rw [hS _ (by omega)]; exact h1, fun t ht ↦ by rw [hS _ (by omega)]; exact h2 t ht,
    fun d hd l hl ↦ by rw [hS _ (by omega)]; exact h3 d hd l hl⟩

private theorem path_getD {ps : List Nat} {leaves : List (List K)}
    {sibs : List (List (Nat × Digest))} {h q d : Nat} (hd : d < h) :
    (openingOf ps leaves sibs h q).path.getD d default =
      ((sibs.getD d []).lookup (q >>> d)).getD default := by
  simp [openingOf, List.getD_eq_getElem?_getD, hd]

variable {e : Env} (P : Pre e)
include P
variable {s : QState} {D W : Nat → UInt64} {F : QState → Prop}

private theorem blk_storei_dec {Q : QState → Prop} {rest : List Stmt} (hI : Inv e s D W)
    {c : Int64} {ad : Addr} {k : Nat} (ha : ad.eval s = adr e.da k) (hk : k < e.dn)
    (h : ∀ s', Inv e s' (Function.update D k c.toUInt64) W → s'.reg = s.reg →
      WP (blk rest) s' Q F) : WP (blk (I (.storei ad c) :: rest)) s Q F := by
  apply WP.blk_cons
  apply WP.ins'
  simp only [QInstr.step, ha, hI.dec k hk, Option.map_some]
  exact h _ (hI.storeDec P hk _) rfl

private theorem stw {s0 : QState} {Q : QState → Prop} {rest : List Stmt} {r : Reg64} {ad : Addr}
    {k : Nat} (hI : Inv e s0 D W) (hm : s.mem = s0.mem) (hr : s.reg .rdi = e.x)
    (ha : ad.eval s = adr e.wk k) (hk : k < workWords)
    (h : ∀ s', Inv e s' D (Function.update W k (s.reg r)) → s'.reg = s.reg →
      WP (blk rest) s' Q F) : WP (blk (I (.store ad r) :: rest)) s Q F :=
  blk_store_work P (inv_of hI hm hr) ha hk h

private theorem std {s0 : QState} {Q : QState → Prop} {rest : List Stmt} {r : Reg64} {ad : Addr}
    {k : Nat} (hI : Inv e s0 D W) (hm : s.mem = s0.mem) (hr : s.reg .rdi = e.x)
    (ha : ad.eval s = adr e.da k) (hk : k < e.dn)
    (h : ∀ s', Inv e s' (Function.update D k (s.reg r)) W → s'.reg = s.reg →
      WP (blk rest) s' Q F) : WP (blk (I (.store ad r) :: rest)) s Q F :=
  blk_store_dec P (inv_of hI hm hr) ha hk h

/-- **`pathStep`**: the sibling of the query's node `q >>> d` at level `d`, from the level's table
`sl`, into the opening's path digest `d`, zeros if none; the node then `q >>> (d + 1)`. -/
theorem output_pathStep_ok (hI : Inv e s D W) {d ob q : Nat} {sl : List (Nat × Digest)}
    {W0 : Nat → UInt64} (hr11 : s.reg .r11 = d.toUInt64) (hr9 : s.reg .r9 = adr e.da ob)
    (hd : d < 32) (hob : ob + openingWords ≤ e.dn) (hq : q < 2 ^ 32)
    (hx : W wX = (q >>> d).toUInt64) (hW : Same (· = wX) W0 W)
    (hN : W0 (wSibN + d) = sl.length.toUInt64) (hsl : sl.length ≤ 256)
    (hk : ∀ x ∈ sl, x.1 < 2 ^ 32) (hT : NodeTab W0 (wSib + 1280 * d) sl) :
    WP pathStep s (fun s' ↦ Inv e s' (put4 D (ob + 1 + wireMaxLeafWords + 4 * d)
        (dw ((sl.lookup (q >>> d)).getD default)))
      (Function.update W wX (q >>> (d + 1)).toUInt64) ∧ s'.reg .r11 = (d + 1).toUInt64 ∧
      RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r11] s s') F := by
  obtain ⟨cX, cQ, cP, cFL, cNode, cPar, cSibN, cSib, cLeaf, cWW, cOW, cLW⟩ := consts
  have hNd : W (wSibN + d) = sl.length.toUInt64 := by rw [hW _ (by omega)]; exact hN
  have hqd : q >>> d < 2 ^ 32 := lt_of_le_of_lt (Nat.shiftRight_le q d) hq
  unfold pathStep
  refine blk_load_ctx P hI (eval_cw s hI.rdi _) (by decide) P.c10 ?_
  apply WP.blk_cons
  unfold sibBase
  step; step; step; step; step; step; step
  apply WP.blk_nil
  step
  refine ldw hI (k := wSibN + d) ?_ ?_ ?_ (by omega) ?_
  · rfl
  · simp [hI.rdi]
  · exact ev_ix (j := 0) (n := d) (by simp [adr_zero]) (by simp [hr11]) (by omega)
  refine ldw hI (k := wX) ?_ ?_ ?_ (by omega) ?_
  · rfl
  · simp [hI.rdi]
  · exact ev_rw (j := 0) (by simp [adr_zero]) (by omega)
  apply WP.blk_cons
  refine WP.mono (find_ok (e := e) (D := D) (W := W) (S := 5) (b := wSib + 1280 * d)
    (n := sl.length) (key := (q >>> d).toUInt64) (ks := sl.map fun x ↦ x.1.toUInt64)
    ?_ (by decide) ?_ ?_ ?_ (by simp) (by omega) (fun i hi ↦ ?_))
    (fun t1 ⟨h1, _, hc1, _, h81, hf1⟩ ↦ ?_) (fun _ h ↦ h)
  · exact inv_of hI rfl (by simp [hI.rdi])
  · simp only [QState.setReg_reg, reduceCtorEq, ite_true, ite_false, hr11]
    exact sib_adr _ hd
  · simp [hNd]
  · simp [hx]
  · rw [List.length_map] at hi
    rw [hW _ (by omega), (hT i hi).1, List.getElem_map]
  set i := (sl.map fun x ↦ x.1.toUInt64).idxOf (q >>> d).toUInt64 with hi
  have hil : i ≤ sl.length := by simpa using List.idxOf_le_length (l := sl.map fun x ↦ x.1.toUInt64)
  have r11' : t1.reg .r11 = d.toUInt64 := by rw [hf1 .r11 (by simp)]; simp [hr11]
  have r9' : t1.reg .r9 = adr e.da ob := by rw [hf1 .r9 (by simp)]; simp [hr9]
  set J := ob + 1 + wireMaxLeafWords + 4 * d with hJ
  refine blk_load_ctx P h1 (eval_cw t1 h1.rdi _) (by decide) P.c10 ?_
  refine ldw h1 (k := wSibN + d) ?_ ?_ ?_ (by omega) ?_
  · rfl
  · simp [h1.rdi]
  · exact ev_ix (j := 0) (n := d) (by simp [adr_zero]) (by simp [r11']) (by omega)
  step; step; step
  have h4 : t1.reg .r11 <<< Nat.toUInt64 2 = (4 * d).toUInt64 := by
    rw [r11', toUInt64_shl (by omega) (by omega), Nat.mul_comm]; rfl
  refine wp_gen fun u hu ↦ ?_
  have hIu : Inv e u D W := inv_of h1 (by rw [hu]; rfl) (by rw [hu]; simp [h1.rdi])
  have ubx : u.reg .rbx = adr e.da J := by
    rw [hu]
    simp only [QState.setReg_reg, reduceCtorEq, ite_true, ite_false]
    refine ev_ix (j := ob) (n := 4 * d) ?_ ?_ (by omega)
    · simp [r9']
    · simp only [QState.setReg_reg, reduceCtorEq, ite_true, ite_false]; exact h4
  have ucx : u.reg .rcx = i.toUInt64 := by rw [hu]; simp [hc1]
  have udx : u.reg .rdx = sl.length.toUInt64 := by rw [hu]; simp [hNd]
  have u8 : u.reg .r8 = adr e.wk (wSib + 1280 * d + 5 * i) := by rw [hu]; simp [h81]
  have uf : RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8] s u := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨n1, n2, n3, n4, n5, n6⟩ := hr
    rw [hu]
    simp only [QState.setReg_reg, n1, n2, n4, ite_false]
    rw [hf1 r (by simp [n2, n3, n4, n6])]
    simp [n1, n3, n4, n5]
  clear hu
  apply WP.blk_cons
  refine WP.mono (P := fun t2 ↦ Inv e t2 (put4 D J (dw ((sl.lookup (q >>> d)).getD default))) W ∧
    RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8] s t2) ?_ (fun t2 ⟨h2, hf2⟩ ↦ ?_) (fun _ h ↦ h)
  · apply WP.ite
    rw [cond_ltu_reg ucx udx (by omega) (by omega)]
    by_cases hf : i < sl.length
    · simp only [hf, decide_true, ite_true]
      refine WP.mono (copy4_dec P hIu (src := .r8) (dst := .rbx) (by decide) (by decide) (i := 1)
        (j := 0) (v := dw sl[i].2) u8 ubx (by omega) (fun l hl ↦ ?_) (fun l hl l' hl' ↦ ?_))
        (fun t2 ⟨h2, hf2, _⟩ ↦ ⟨?_, RegsFrame.trans uf (RegsFrame.mono hf2 (by simp))⟩)
        (fun _ h ↦ h)
      · rw [adr_add, hIu.work _ (by omega), ← Nat.add_assoc, hW _ (by omega), (hT i hf).2 l hl]
      · rw [adr_add]
        exact (P.dec_ne_work (by omega) (by omega)).symm
      · rw [lookup_found hqd sl hk i hf hi.symm, Option.getD_some]
        simpa using h2
    · simp only [hf, decide_false, Bool.false_eq_true, ite_false]
      refine blk_storei_dec P hIu (k := J + 0) (ev_rw ubx rfl) (by omega) fun u1 g1 e1 ↦ ?_
      refine blk_storei_dec P g1 (k := J + 1) (ev_rw (by rw [e1, ubx]) rfl) (by omega)
        fun u2 g2 e2 ↦ ?_
      refine blk_storei_dec P g2 (k := J + 2) (ev_rw (by rw [e2, e1, ubx]) rfl) (by omega)
        fun u3 g3 e3 ↦ ?_
      refine blk_storei_dec P g3 (k := J + 3) (ev_rw (by rw [e3, e2, e1, ubx]) rfl) (by omega)
        fun u4 g4 e4 ↦ ?_
      apply WP.blk_nil
      refine ⟨?_, fun r hr ↦ by rw [e4, e3, e2, e1]; exact uf r hr⟩
      rw [lookup_none hqd sl hk (by omega), Option.getD_none]
      convert g4 using 2
      rw [← put4_eq]
      simp only [dw_default, Nat.add_zero]
      rfl
  · refine blk_load_ctx P h2 (eval_cw t2 h2.rdi _) (by decide) P.c10 ?_
    refine ldw h2 (k := wX) ?_ ?_ ?_ (by omega) ?_
    · rfl
    · simp [h2.rdi]
    · exact ev_rw (j := 0) (by simp [adr_zero]) (by omega)
    step
    refine stw P h2 (k := wX) ?_ ?_ ?_ (by omega) fun t3 h3 r3 ↦ ?_
    · rfl
    · simp [h2.rdi]
    · exact ev_rw (j := 0) (by simp [adr_zero]) (by omega)
    step
    apply WP.blk_nil
    have hv : W wX >>> Nat.toUInt64 1 = (q >>> (d + 1)).toUInt64 := by
      rw [hx, toUInt64_shr (by omega) (by omega), Nat.shiftRight_succ, pow_one]
    simp only [QState.setReg_reg, reduceCtorEq, ite_true, ite_false, hv] at h3
    refine ⟨inv_of h3 rfl (by simp [r3, h2.rdi]), ?_, ?_⟩
    · simp [r3, hf2 .r11 (by simp), hr11]
      rfl
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      obtain ⟨n1, n2, n3, n4, n5, n6, n7⟩ := hr
      simp only [QState.setReg_reg, n7, ite_false, r3, n1, n3]
      exact hf2 r (by simp [n1, n2, n3, n4, n5, n6])

/-- **The path loop**: the `h` levels' siblings of the query `q` into the opening's path, the
query's node at level `h` left in `wX`. -/
theorem output_path_ok (hI : Inv e s D W) {h ob q : Nat} {sibs : List (List (Nat × Digest))}
    {W0 : Nat → UInt64} (hr11 : s.reg .r11 = 0) (hr13 : s.reg .r13 = h.toUInt64)
    (hr9 : s.reg .r9 = adr e.da ob) (hh : h ≤ 32) (hob : ob + openingWords ≤ e.dn)
    (hq : q < 2 ^ 32) (hx : W wX = q.toUInt64) (hW : Same (· = wX) W0 W)
    (hsib : ∀ lv < h, W0 (wSibN + lv) = (sibs.getD lv []).length.toUInt64 ∧
      (sibs.getD lv []).length ≤ wireMaxQueries ∧ (∀ x ∈ sibs.getD lv [], x.1 < 2 ^ 32) ∧
      NodeTab W0 (wSib + 1280 * lv) (sibs.getD lv [])) :
    WP (.loop (.cmp .ltu .r11 (.reg .r13)) pathStep) s (fun s' ↦ ∃ D',
      Inv e s' D' (Function.update W wX (q >>> h).toUInt64) ∧
      (∀ d < h, ∀ l < 4, D' (ob + 1 + wireMaxLeafWords + 4 * d + l) =
        dw (((sibs.getD d []).lookup (q >>> d)).getD default) l) ∧
      Same (fun k ↦ ob + 1 + wireMaxLeafWords ≤ k ∧ k < ob + 1 + wireMaxLeafWords + 4 * h) D D' ∧
      RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r11] s s') F := by
  obtain ⟨cX, cQ, cP, cFL, cNode, cPar, cSibN, cSib, cLeaf, cWW, cOW, cLW⟩ := consts
  have hMQ : wireMaxQueries = 256 := rfl
  refine WP.loop (fun v ↦ ∃ d D', d ≤ h ∧ Inv e v D' (Function.update W wX (q >>> d).toUInt64) ∧
      (∀ d' < d, ∀ l < 4, D' (ob + 1 + wireMaxLeafWords + 4 * d' + l) =
        dw (((sibs.getD d' []).lookup (q >>> d')).getD default) l) ∧
      Same (fun k ↦ ob + 1 + wireMaxLeafWords ≤ k ∧ k < ob + 1 + wireMaxLeafWords + 4 * d) D D' ∧
      v.reg .r11 = d.toUInt64 ∧ RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r11] s v)
    (fun v ↦ h - (v.reg .r11).toNat) ⟨0, D, by omega, ?_, fun _ h ↦ absurd h (by omega),
      Same.refl _ _, by rw [hr11]; rfl, RegsFrame.refl s⟩ ?_ ?_
  · rw [Nat.shiftRight_zero, ← hx, Function.update_eq_self]
    exact hI
  · intro v ⟨d, D', hdh, hIv, hP, hS, h11, hfv⟩ hc
    have h13 : v.reg .r13 = h.toUInt64 := by rw [hfv .r13 (by simp), hr13]
    rw [cond_ltu_reg h11 h13 (by omega) (by omega), decide_eq_true_eq] at hc
    obtain ⟨hN, hsl, hk, hT⟩ := hsib d hc
    refine WP.mono (output_pathStep_ok P hIv (W0 := W0) h11 (by rw [hfv .r9 (by simp), hr9])
      (by omega) hob hq (by simp) (fun k hk ↦ ?_) hN (by omega) hk hT)
      (fun v' ⟨hI', h11', hf'⟩ ↦ ⟨⟨d + 1, _, by omega, by rwa [Function.update_idem] at hI',
        fun d' hd' l hl ↦ ?_, fun k hk ↦ ?_, h11', RegsFrame.trans hfv hf'⟩, ?_⟩) (fun _ h ↦ h)
    · rw [Function.update_of_ne hk]
      exact hW k hk
    · unfold put4
      rcases Nat.lt_succ_iff_lt_or_eq.1 hd' with hd' | rfl
      · rw [ite_no (by omega)]
        exact hP d' hd' l hl
      · rw [ite_yes (by omega)]
        congr 1
        omega
    · unfold put4
      rw [ite_no (by omega)]
      exact hS k (by omega)
    · rw [h11', h11, toNat_toUInt64' (by omega), toNat_toUInt64' (by omega)]
      omega
  · intro v ⟨d, D', hdh, hIv, hP, hS, h11, hfv⟩ hc
    have h13 : v.reg .r13 = h.toUInt64 := by rw [hfv .r13 (by simp), hr13]
    rw [cond_ltu_reg h11 h13 (by omega) (by omega), decide_eq_false_iff_not] at hc
    obtain rfl : d = h := by omega
    exact ⟨D', hIv, hP, hS, hfv⟩

theorem output_ok (hI : Inv e s D W) {base lw h : Nat} {qs ps : List Nat}
    {leaves : List (List K)} {sibs : List (List (Nat × Digest))}
    (hr14 : s.reg .r14 = qs.length.toUInt64) (hr13 : s.reg .r13 = h.toUInt64)
    (hr12 : s.reg .r12 = lw.toUInt64) (hr10 : s.reg .r10 = ps.length.toUInt64)
    (hqn : qs.length ≤ wireMaxQueries) (hpn : ps.length ≤ wireMaxQueries)
    (hh : h ≤ wireMaxHeight) (hlw : lw ≤ wireMaxLeafWords)
    (hqlt : ∀ q ∈ qs, q < 2 ^ 32) (hplt : ∀ p ∈ ps, p < 2 ^ 32) (hqp : ∀ q ∈ qs, q ∈ ps)
    (hq : Tab W wQ (qs.map Nat.toUInt64)) (hps : Tab W wP (ps.map Nat.toUInt64))
    (hl : leaves.length = ps.length) (hleaf : LeafTab W leaves lw)
    (hsib : ∀ lv < h, W (wSibN + lv) = (sibs.getD lv []).length.toUInt64 ∧
      (sibs.getD lv []).length ≤ wireMaxQueries ∧ (∀ x ∈ sibs.getD lv [], x.1 < 2 ^ 32) ∧
      NodeTab W (wSib + 1280 * lv) (sibs.getD lv []))
    (hpb : W wPB = adr e.da base) (hbase : base + phaseWords ≤ e.dn) :
    WP output s (fun s' ↦ ∃ D' W', Inv e s' D' W' ∧
      (∀ j (hj : j < qs.length),
        let o := openingOf ps leaves sibs h qs[j]
        let ob := base + 3 + j * openingWords
        D' ob = o.leafIndex.toUInt64 ∧ (∀ t < lw, D' (ob + 1 + t) = (o.leaf.getD t 0).lane) ∧
        ∀ d < h, ∀ l < 4,
          D' (ob + 1 + wireMaxLeafWords + 4 * d + l) = dw (o.path.getD d default) l) ∧
      Same (fun k ↦ base + 3 ≤ k ∧ k < base + phaseWords) D D' ∧
      Same (fun k ↦ k = wX) W W' ∧
      RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r9, .r11, .rbp] s s') F := by
  obtain ⟨cX, cQ, cP, cFL, cNode, cPar, cSibN, cSib, cLeaf, cWW, cOW, cLW⟩ := consts
  have hMQ : wireMaxQueries = 256 := rfl
  have hMH : wireMaxHeight = 32 := rfl
  have hPW : phaseWords = 3 + 256 * openingWords := rfl
  unfold output
  refine blk_load_ctx P hI (eval_cw s hI.rdi _) (by decide) P.c10 ?_
  refine ldw hI (k := wPB) ?_ ?_ ?_ (by decide) ?_
  · rfl
  · simp [hI.rdi]
  · exact ev_rw (j := 0) (by simp [adr_zero]) (by decide)
  step; step
  refine wp_gen fun u hu ↦ ?_
  have hIu : Inv e u D W := inv_of hI (by rw [hu]; rfl) (by rw [hu]; simp [hI.rdi])
  have u9 : u.reg .r9 = adr e.da (base + 3 + 0 * openingWords) := by
    rw [hu]
    simp only [QState.setReg_reg, reduceCtorEq, ite_true, ite_false, hpb]
    rw [show (24 : Int64).toUInt64 = (8 * 3 : Nat).toUInt64 from rfl, adr_add]
    simp
  have ubp : u.reg .rbp = (0 : Nat).toUInt64 := by rw [hu]; simp; rfl
  have uf : RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r9, .r11, .rbp] s u := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [hu]
    simp [hr.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2]
  clear hu
  refine WP.loop (fun v ↦ ∃ j D1 W1, j ≤ qs.length ∧ Inv e v D1 W1 ∧ Same (· = wX) W W1 ∧
      Same (fun k ↦ base + 3 ≤ k ∧ k < base + phaseWords) D D1 ∧
      (∀ j' (hj' : j' < qs.length), j' < j → OpenOk ps leaves sibs h lw base D1 j' qs[j']) ∧
      v.reg .rbp = j.toUInt64 ∧ v.reg .r9 = adr e.da (base + 3 + j * openingWords) ∧
      RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r9, .r11, .rbp] s v)
    (fun v ↦ qs.length - (v.reg .rbp).toNat) ⟨0, D, W, by omega, hIu, Same.refl _ _,
      Same.refl _ _, fun _ _ h ↦ absurd h (by omega), ubp, u9, uf⟩ ?_ ?_
  · intro v ⟨j, D1, W1, hjl, hI1, hW1, hD1, hG, hbp, hr9v, hfv⟩ hc
    have h14 : v.reg .r14 = qs.length.toUInt64 := by rw [hfv .r14 (by simp), hr14]
    rw [cond_ltu_reg hbp h14 (by omega) (by omega), decide_eq_true_eq] at hc
    have hqm : qs[j] ∈ qs := List.getElem_mem hc
    have hq32 : qs[j] < 2 ^ 32 := hqlt _ hqm
    have hjm : j * openingWords + openingWords ≤ 256 * openingWords := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
    set ob := base + 3 + j * openingWords with hob
    have hobd : ob + openingWords ≤ e.dn := by omega
    have hqv : W1 (wQ + j) = qs[j].toUInt64 := by
      rw [hW1 _ (by omega), hq j (by simpa using hc), List.getElem_map]
    refine blk_load_ctx P hI1 (eval_cw v hI1.rdi _) (by decide) P.c10 ?_
    refine ldw hI1 (k := wQ + j) ?_ ?_ ?_ (by omega) ?_
    · rfl
    · simp [hI1.rdi]
    · exact ev_ix (j := 0) (n := j) (by simp [adr_zero]) (by simp [hbp]) (by omega)
    refine std P hI1 (k := ob) ?_ ?_ ?_ (by omega) fun t2 g2 e2 ↦ ?_
    · rfl
    · simp [hI1.rdi]
    · exact ev_rw (j := ob) (by simp [hr9v]) (by omega)
    simp only [QState.setReg_reg, reduceCtorEq, ite_true, ite_false, hqv] at g2
    refine stw P g2 (k := wX) ?_ ?_ ?_ (by omega) fun t3 g3 e3 ↦ ?_
    · rfl
    · rw [e2]; simp [hI1.rdi]
    · exact ev_rw (j := 0) (by rw [e2]; simp [adr_zero]) (by omega)
    simp only [e2, QState.setReg_reg, reduceCtorEq, ite_true, ite_false, hqv] at g3
    step; step
    refine wp_gen fun u4 hu4 ↦ ?_
    have hI4 := inv_of g3 (t := u4) (by rw [hu4]; rfl) (by rw [hu4]; simp [e3, e2, hI1.rdi])
    have u4si : u4.reg .rsi = adr e.wk wP := by
      rw [hu4]
      simp only [QState.setReg_reg, reduceCtorEq, ite_true, ite_false]
      exact ev_rw (j := 0) (by simp [e3, e2, adr_zero]) (by omega)
    have u4dx : u4.reg .rdx = ps.length.toUInt64 := by
      rw [hu4]; simp [e3, e2, hfv .r10 (by simp), hr10]
    have u4ax : u4.reg .rax = qs[j].toUInt64 := by rw [hu4]; simp [e3, e2, hqv]
    have uf4 : RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r11] v u4 := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      obtain ⟨n1, n2, n3, n4, n5, n6, n7⟩ := hr
      rw [hu4]
      simp [n1, n3, n4, n5, e3, e2]
    clear hu4
    apply WP.blk_cons
    refine WP.mono (find_ok hI4 (S := 1) (b := wP) (ks := ps.map Nat.toUInt64) (by decide) u4si
      u4dx u4ax (by simp) (by omega) (fun i hi ↦ ?_)) (fun t5 ⟨g5, _, c5, _, _, f5⟩ ↦ ?_)
      (fun _ h ↦ h)
    · rw [List.length_map] at hi
      rw [Nat.one_mul, Function.update_of_ne (by omega), hW1 _ (by omega)]
      exact hps i (by simpa using hi)
    set idx := (ps.map Nat.toUInt64).idxOf qs[j].toUInt64 with hidx
    have hil : idx < ps.length := by
      simpa using List.idxOf_lt_length_of_mem (List.mem_map_of_mem (f := Nat.toUInt64) (hqp _ hqm))
    have uf5 : RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r11] v t5 :=
      RegsFrame.trans uf4 (RegsFrame.mono f5 (by simp))
    refine blk_load_ctx P g5 (eval_cw t5 g5.rdi _) (by decide) P.c10 ?_
    step; step; step; step
    refine wp_gen fun u6 hu6 ↦ ?_
    have hI6 := inv_of g5 (t := u6) (by rw [hu6]; rfl) (by rw [hu6]; simp [g5.rdi])
    have u6si : u6.reg .rsi = adr e.wk (wLeaf + 64 * idx) := by
      rw [hu6]
      simp only [QState.setReg_reg, reduceCtorEq, ite_true, ite_false]
      refine ev_ix (j := 0) (n := idx * 2 ^ 6) (by simp [adr_zero]) ?_ (by omega)
      simp only [QState.setReg_reg, reduceCtorEq, ite_true, ite_false]
      rw [c5, toUInt64_shl (by omega) (by omega)]
    have u6bx : u6.reg .rbx = adr e.da (ob + 1) := by
      rw [hu6]
      simp only [QState.setReg_reg, reduceCtorEq, ite_true, ite_false]
      exact ev_rw (by simp [uf5 .r9 (by simp), hr9v]) rfl
    have u6dx : u6.reg .rdx = lw.toUInt64 := by
      rw [hu6]; simp [uf5 .r12 (by simp), hfv .r12 (by simp), hr12]
    have uf6 : RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r11] v u6 := by
      intro r hr
      have hr' := hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
      obtain ⟨n1, n2, n3, n4, n5, n6, n7⟩ := hr'
      rw [hu6]
      simp only [QState.setReg_reg, n2, n3, n4, n5, ite_false]
      exact uf5 r hr
    clear hu6
    apply WP.blk_cons
    refine WP.mono (copyWords_dec P hI6 u6si u6bx u6dx (by omega) (by omega))
      (fun t7 ⟨g7, f7⟩ ↦ ?_) (fun _ h ↦ h)
    have uf7 : RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r11] v t7 :=
      RegsFrame.trans uf6 (RegsFrame.mono f7 (by simp))
    step
    refine wp_gen fun u8 hu8 ↦ ?_
    have hI8 := inv_of g7 (t := u8) (by rw [hu8]; rfl) (by rw [hu8]; simp [g7.rdi])
    have u8r11 : u8.reg .r11 = 0 := by rw [hu8]; simp; rfl
    have u8r13 : u8.reg .r13 = h.toUInt64 := by
      rw [hu8]; simp [uf7 .r13 (by simp), hfv .r13 (by simp), hr13]
    have u8r9 : u8.reg .r9 = adr e.da ob := by
      rw [hu8]; simp [uf7 .r9 (by simp), hr9v]
    have uf8 : RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r11] v u8 := by
      intro r hr
      have hr' := hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
      rw [hu8]
      simp only [QState.setReg_reg, hr'.2.2.2.2.2.2, ite_false]
      exact uf7 r hr
    clear hu8
    apply WP.blk_cons
    refine WP.mono (output_path_ok P hI8 (W0 := W) (sibs := sibs) u8r11 u8r13 u8r9 (by omega)
      hobd hq32 (by simp) (fun k hk ↦ ?_) hsib) (fun t9 ⟨D3, g9, hP9, hS9, f9⟩ ↦ ?_)
      (fun _ h ↦ h)
    · rw [Function.update_of_ne hk]
      exact hW1 k hk
    have uf9 : RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r11] v t9 := RegsFrame.trans uf8 f9
    step; step
    apply WP.blk_nil
    have hSJ : Same (fun k ↦ ob ≤ k ∧ k < ob + openingWords) D1 D3 := fun k hk ↦ by
      rw [hS9 k (by omega)]
      unfold copied
      rw [ite_no (by omega), Function.update_of_ne (by omega)]
    have hkz : ∀ x ∈ ps.zip leaves, x.1 < 2 ^ 32 := fun x hx ↦ hplt _ (List.of_mem_zip hx).1
    have hmz : (ps.zip leaves).map (fun x ↦ x.1.toUInt64) = ps.map Nat.toUInt64 := by
      rw [show (fun x : Nat × List K ↦ x.1.toUInt64) = Nat.toUInt64 ∘ Prod.fst from rfl,
        ← List.map_map, List.map_fst_zip (by omega)]
    have hlk : (openingOf ps leaves sibs h qs[j]).leaf = leaves[idx] := by
      show ((ps.zip leaves).lookup qs[j]).getD [] = _
      rw [lookup_found hq32 (ps.zip leaves) hkz idx (by simp; omega) (by rw [hmz]),
        Option.getD_some, List.getElem_zip]
    refine ⟨⟨j + 1, D3, _, by omega, inv_of g9 rfl (by simp [g9.rdi]), fun k hk ↦ ?_,
      fun k hk ↦ ?_, fun j' hj' hj'1 ↦ ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [Function.update_of_ne hk, Function.update_of_ne hk]
      exact hW1 k hk
    · rw [hSJ k (by omega)]
      exact hD1 k hk
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hj'1 with hlt | rfl
      · exact openOk_same hlw hh hlt hSJ (hG j' hj' hlt)
      · refine ⟨?_, fun t ht ↦ ?_, fun d hd l hl ↦ ?_⟩
        · rw [hS9 _ (by omega)]
          unfold copied
          rw [ite_no (by omega)]
          simp [openingOf, hob]
        · rw [hS9 _ (by omega)]
          unfold copied
          rw [ite_yes (by omega), Nat.add_sub_cancel_left, Function.update_of_ne (by omega),
            hW1 _ (by omega), hleaf idx (by omega) t ht, hlk]
        · rw [path_getD hd]
          exact hP9 d hd l hl
    · simp [uf9 .rbp (by simp), hbp]
      rfl
    · simp only [QState.setReg_reg, reduceCtorEq, ite_true, ite_false]
      rw [uf9 .r9 (by simp), hr9v, wd_toUInt64, adr_add]
      exact congrArg (adr e.da) (by rw [Nat.succ_mul]; omega)
    · intro r hr
      have hr' := hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
      obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ := hr'
      simp only [QState.setReg_reg, n7, n9, ite_false]
      rw [uf9 r (by simp [n1, n2, n3, n4, n5, n6, n8])]
      exact hfv r hr
    · simp only [QState.setReg_reg, ite_true]
      rw [uf9 .rbp (by simp), hbp, show (1 : Int64).toUInt64 = (1 : Nat).toUInt64 from rfl,
        toUInt64_add, toNat_toUInt64' (by omega), toNat_toUInt64' (by omega)]
      omega
  · intro v ⟨j, D1, W1, hjl, hI1, hW1, hD1, hG, hbp, _, hfv⟩ hc
    have h14 : v.reg .r14 = qs.length.toUInt64 := by rw [hfv .r14 (by simp), hr14]
    rw [cond_ltu_reg hbp h14 (by omega) (by omega), decide_eq_false_iff_not] at hc
    obtain rfl : j = qs.length := by omega
    exact ⟨D1, W1, hI1, fun j hj ↦ hG j hj hj, hD1, hW1, hfv⟩

end NativeVm.Wire
