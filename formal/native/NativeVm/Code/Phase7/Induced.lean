module

public import NativeVm.Code.Phase7.Subspace

/-!
# The induced weight

`inducedC` computes `inducedWeight μ qs ws pt` into `(r9, r10)`. Per query `q_j` (weight
`w_j`): `subAtC` writes `what = subspaceAt μ q_j` into the scratch from word `16`, then `prodC`
multiplies `w_j` by `1 + scale (1 ^^^ what_k) pt_k` for `k < min |pt| (μ + 1)` (the `zip`'s
length), and the product is added to the total. `subAtC` and `prodC` clobber almost every
register, so the loop's state lives in the scratch's first words (`QInv`), its address in `rbp`:
the total (words `0`, `1`), the next query's and weight's addresses (`2`, `3`), the queries left
(`4`), `pt`'s address (`5`), the product's length (`6`), the table's address (`7`) and `μ + 1`
(`8`).
-/

@[expose] public section

namespace NativeVm.Code.P7

open Native NativeVm.Model LeanVM.Parameters
open NativeVm.Transcript (wd Fits Disj wd_add wd_zero wd_inj wd_ne_of_disj toNat_toUInt64
  toUInt64_inj)

/-- The scratch words `inducedC` uses: its state, then `what` from word `16`. -/
def inducedScratchWords : Nat := 80

namespace Ind

open Sp

/-! ## The model, step by step -/

/-- A factor of the product. -/
def prodStep (p : EW) (cv : EW × UInt64) : EW := p * (1 + EW.scale (1 ^^^ cv.2) cv.1)

/-- A query's term added to the total. -/
def totStep (mu : Nat) (pt : Array EW) (total : EW) (wq : EW × UInt64) : EW :=
  total + (pt.zip (subspaceAt mu wq.2)).foldl prodStep wq.1

/-- The total after the first `j` queries. -/
def tot (mu : Nat) (pt ws : Array EW) (qs : Array UInt64) (j : Nat) : EW :=
  ((ws.zip qs).toList.take j).foldl (totStep mu pt) 0

theorem tot_full (mu : Nat) (qs : Array UInt64) (ws pt : Array EW) (hl : ws.size = qs.size) :
    tot mu pt ws qs qs.size = inducedWeight mu qs ws pt := by
  rw [tot, List.take_of_length_le (by simp [hl]), Array.foldl_toList]
  rfl

theorem tot_succ (mu : Nat) {qs : Array UInt64} {ws : Array EW} (pt : Array EW) {j : Nat}
    (hj : j < qs.size) (hw : j < ws.size) :
    tot mu pt ws qs (j + 1) = tot mu pt ws qs j +
      (pt.zip (subspaceAtTable (subspaceTable mu) qs[j])).foldl prodStep ws[j] := by
  have key : (ws.zip qs).toList[j]? = some (ws[j], qs[j]) := by simp [Array.toList_zip, hj, hw]
  rw [tot, tot, List.take_add_one, List.foldl_append, key]
  rfl

theorem prod_succ {cs : Array EW} {vs : Array UInt64} {i : Nat} (hc : i < cs.size)
    (hv : i < vs.size) (w : EW) :
    ((cs.zip vs).toList.take (i + 1)).foldl prodStep w =
      prodStep (((cs.zip vs).toList.take i).foldl prodStep w) (cs[i], vs[i]) := by
  rw [List.take_add_one, List.foldl_append]
  simp [Array.toList_zip, hc, hv]

theorem factor_c0 (v : UInt64) (c : EW) :
    (1 + EW.scale (1 ^^^ v) c).c0 = kmul (v ^^^ 1) c.c0 ^^^ 1 := by
  show (1 : UInt64) ^^^ kmul (1 ^^^ v) c.c0 = _
  rw [UInt64.xor_comm 1 v, UInt64.xor_comm]

theorem factor_c1 (v : UInt64) (c : EW) : (1 + EW.scale (1 ^^^ v) c).c1 = kmul (v ^^^ 1) c.c1 := by
  show (0 : UInt64) ^^^ kmul (1 ^^^ v) c.c1 = _
  rw [UInt64.zero_xor, UInt64.xor_comm 1 v]

theorem emul_words {a0 a1 b0 b1 r0 r1 : UInt64} {x y : EW} (hx0 : a0 = x.c0) (hx1 : a1 = x.c1)
    (hy0 : b0 = y.c0) (hy1 : b1 = y.c1)
    (h : Field.eOf r0 r1 = Field.eOf a0 a1 * Field.eOf b0 b1) :
    r0 = (x * y).c0 ∧ r1 = (x * y).c1 := by
  subst hx0 hx1 hy0 hy1
  apply Field.eOf_inj.mp
  rw [h]
  exact (Equiv.EW.toE_mul x y).symm

theorem add_c0 (a b : EW) : (a + b).c0 = b.c0 ^^^ a.c0 := UInt64.xor_comm _ _

theorem add_c1 (a b : EW) : (a + b).c1 = b.c1 ^^^ a.c1 := UInt64.xor_comm _ _

/-! ## Areas and steps -/

theorem fits_sub {b : UInt64} {N k m : Nat} (h : Fits b N) (hk : k < N) (hkm : k + m ≤ N) :
    Fits (wd b k) m := by
  have := NativeVm.Transcript.wd_toNat h hk
  unfold Fits at *
  omega

theorem disj_sub {b c : UInt64} {N M k m : Nat} (hb : Fits b N) (h : Disj b N c M) (hk : k < N)
    (hkm : k + m ≤ N) : Disj (wd b k) m c M := by
  have := NativeVm.Transcript.wd_toNat hb hk
  unfold Disj at *
  omega

theorem TableAt.congr {m m' : UInt64 → Option UInt64} {p : UInt64} {tb : Array (UInt64 × UInt64)}
    (h : ∀ k < 2 * tb.size, m' (wd p k) = m (wd p k)) (ht : TableAt m p tb) : TableAt m' p tb :=
  fun i hi ↦ ⟨(h _ (by omega)).trans (ht i hi).1, (h _ (by omega)).trans (ht i hi).2⟩

variable {s : QState} {P F : QState → Prop} {xs : List Stmt}

theorem wp_ld {d r : Reg64} {disp : Int64} {b : UInt64} (k : Nat) {v : UInt64}
    (hr : s.reg r = b) (hd : disp.toUInt64 = (8 * k).toUInt64) (h : s.mem (wd b k) = some v)
    (kk : WP (blk xs) (s.setReg d v) P F) : WP (blk (I (.load d (at_ r disp)) :: xs)) s P F :=
  Field.WP.load_at (by rw [hr, hd]; exact h) kk

theorem wp_st {r src : Reg64} {disp : Int64} {b : UInt64} (k : Nat)
    (hr : s.reg r = b) (hd : disp.toUInt64 = (8 * k).toUInt64) (h : (s.mem (wd b k)).isSome)
    (kk : WP (blk xs) (s.setMem (wd b k) (s.reg src)) P F) :
    WP (blk (I (.store (at_ r disp) src) :: xs)) s P F := by
  have e : s.reg r + disp.toUInt64 = wd b k := by rw [hr, hd]; rfl
  exact Field.WP.store_at (by rw [e]; exact h) (by rw [e]; exact kk)

theorem wp_sti {r : Reg64} {disp n : Int64} {b : UInt64} (k : Nat)
    (hr : s.reg r = b) (hd : disp.toUInt64 = (8 * k).toUInt64) (h : (s.mem (wd b k)).isSome)
    (kk : WP (blk xs) (s.setMem (wd b k) n.toUInt64) P F) :
    WP (blk (I (.storei (at_ r disp) n) :: xs)) s P F := by
  have e : s.reg r + disp.toUInt64 = wd b k := by rw [hr, hd]; rfl
  exact Sp.WP.storei_at (by rw [e]; exact h) (by rw [e]; exact kk)

theorem wp_lea {d r : Reg64} {disp : Int64} {b : UInt64} (k : Nat)
    (hr : s.reg r = b) (hd : disp.toUInt64 = (8 * k).toUInt64)
    (kk : WP (blk xs) (s.setReg d (wd b k)) P F) :
    WP (blk (I (.lea d (at_ r disp)) :: xs)) s P F := by
  have e : (at_ r disp).eval s = wd b k := by rw [Field.eval_at, hr, hd]; rfl
  exact WP.blk_cons (WP.ins (by simp only [QInstr.step, e]) kk)

/-- Which words exist, through register updates and stores. -/
macro "sp_some" : tactic => `(tactic| (
  repeat (first
    | rw [QState.setReg_mem]
    | refine NativeVm.Field.isSome_setMem ?_ _ _)))

/-! ## The product -/

/-- `A := A · Π_k (1 + scale (1 ^^^ v_k) c_k)`, `c` at `r13` (two words each), `v` at `r14`,
`r15` factors. -/
def prodC : Stmt := .loop (.test false .r15 (.reg .r15)) (blk [
  I (.load .rsi (at_ .r14 0)), I (.xori .rsi 1),
  I (.mov .rax .rsi), I (.load .rbx (at_ .r13 0)), Field.kmul, I (.mov .r11 .rax), I (.xori .r11 1),
  I (.mov .rax .rsi), I (.load .rbx (at_ .r13 8)), Field.kmul, I (.mov .r12 .rax),
  Field.emul,
  I (.addi .r13 16), I (.addi .r14 8), I (.subi .r15 1)])

/-- The registers `prodC` writes. -/
abbrev prodRegs : List Reg64 :=
  [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

theorem prodC_writes : ∀ r, r ∉ prodRegs → prodC.writes r = false := by
  intro r hr
  cases r <;> first | rfl | exact absurd (by simp) hr

theorem prodC_spec {cs : Array EW} {vs : Array UInt64} {m : Nat} {Pp V : UInt64} {w : EW}
    (hm : m ≤ cs.size) (hm' : m ≤ vs.size) (hm64 : m ≤ 64)
    (hP : EWArr s.mem Pp cs) (hV : WordArr s.mem V vs)
    (h13 : s.reg .r13 = Pp) (h14 : s.reg .r14 = V) (h15 : s.reg .r15 = m.toUInt64)
    (h9 : s.reg .r9 = w.c0) (h10 : s.reg .r10 = w.c1) :
    WP prodC s (fun s' ↦ s'.reg .r9 = (((cs.zip vs).toList.take m).foldl prodStep w).c0 ∧
      s'.reg .r10 = (((cs.zip vs).toList.take m).foldl prodStep w).c1 ∧ s'.mem = s.mem) F := by
  unfold prodC
  apply WP.loop (fun t ↦ ∃ i ≤ m, t.reg .r13 = wd Pp (2 * i) ∧ t.reg .r14 = wd V i ∧
      t.reg .r15 = (m - i).toUInt64 ∧
      t.reg .r9 = (((cs.zip vs).toList.take i).foldl prodStep w).c0 ∧
      t.reg .r10 = (((cs.zip vs).toList.take i).foldl prodStep w).c1 ∧ t.mem = s.mem)
    (fun t ↦ (t.reg .r15).toNat)
  · exact ⟨0, Nat.zero_le _, by rw [h13, Nat.mul_zero, wd_zero], by rw [h14, wd_zero],
      by rw [h15, Nat.sub_zero], h9, h10, rfl⟩
  · intro t ⟨i, hi, t13, t14, t15, t9, t10, hm1⟩ hc
    have hin : i < m := cnt_lt (t15 ▸ cond_true hc)
    have hic : i < cs.size := by omega
    have hiv : i < vs.size := by omega
    obtain ⟨c0, c1⟩ := hP i hic
    have hv := hV i hiv
    refine wp_ld 0 t14 (by decide) (by rw [wd_zero, hm1]; exact hv) ?_
    fstep; fstep
    refine wp_ld 0 (by rsimp; exact t13) (by decide) (by rsimp; rw [hm1, wd_zero]; exact c0) ?_
    refine Field.WP.then (Field.kmul_spec _) fun t1 ⟨e1, m1, f1⟩ ↦ ?_
    rsimp at e1 m1
    have q1 : ∀ r ∉ Field.kRegs, r ≠ .rsi → t1.reg r = t.reg r := fun r hr hs ↦ by
      rw [f1 r hr]
      simp [notMem hr .rax (by decide), notMem hr .rbx (by decide), hs]
    have qsi : t1.reg .rsi = vs[i] ^^^ 1 := by rw [f1 .rsi (by decide)]; rsimp
    fstep; fstep; fstep
    refine wp_ld 1 (b := wd Pp (2 * i)) (by rsimp; rw [q1 .r13 (by decide) (by decide), t13])
      (by decide) (by rsimp; rw [m1, hm1]; exact c1) ?_
    refine Field.WP.then (Field.kmul_spec _) fun t2 ⟨e2, m2, f2⟩ ↦ ?_
    rsimp at e2 m2
    rw [qsi] at e2
    have q2 : ∀ r ∉ Field.kRegs, r ≠ .r11 → t2.reg r = t1.reg r := fun r hr h11 ↦ by
      rw [f2 r hr]
      simp [notMem hr .rax (by decide), notMem hr .rbx (by decide), h11]
    have r11 : t2.reg .r11 = t1.reg .rax ^^^ 1 := by rw [f2 .r11 (by decide)]; rsimp
    fstep
    refine Field.WP.then (Field.emul_spec _) fun t3 ⟨e3, m3, f3⟩ ↦ ?_
    rsimp at e3 m3
    have q3 : ∀ r ∉ Field.eRegs, r ≠ .r11 → r ≠ .r12 → t3.reg r = t2.reg r := fun r hr h11 h12 ↦ by
      rw [f3 r hr]
      simp [h12]
    fstep; fstep; fstep; fdone
    have hp := prod_succ hic hiv w
    obtain ⟨o0, o1⟩ := emul_words (x := ((cs.zip vs).toList.take i).foldl prodStep w)
      (y := 1 + EW.scale (1 ^^^ vs[i]) cs[i])
      (by rw [q2 .r9 (by decide) (by decide), q1 .r9 (by decide) (by decide), t9])
      (by rw [q2 .r10 (by decide) (by decide), q1 .r10 (by decide) (by decide), t10])
      (by rw [r11, kmul_word e1, factor_c0])
      (by rw [kmul_word e2, factor_c1]) e3
    refine ⟨⟨i + 1, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [q3 .r13 (by decide) (by decide) (by decide), q2 .r13 (by decide) (by decide),
        q1 .r13 (by decide) (by decide), t13, wd16, show 2 * i + 2 = 2 * (i + 1) by omega]
    · rw [q3 .r14 (by decide) (by decide) (by decide), q2 .r14 (by decide) (by decide),
        q1 .r14 (by decide) (by decide), t14, wd8]
    · rw [q3 .r15 (by decide) (by decide) (by decide), q2 .r15 (by decide) (by decide),
        q1 .r15 (by decide) (by decide), t15, cnt_succ hin]
    · rw [hp, o0]; rfl
    · rw [hp, o1]; rfl
    · rw [m3, m2, m1, hm1]
    · rw [q3 .r15 (by decide) (by decide) (by decide), q2 .r15 (by decide) (by decide),
        q1 .r15 (by decide) (by decide), t15, cnt_succ hin]
      exact cnt_dec (by omega) hin
  · intro t ⟨i, hi, _, _, t15, t9, t10, hm1⟩ hc
    have : i = m := cnt_eq (by omega) hi (t15 ▸ cond_false hc)
    subst this
    exact ⟨t9, t10, hm1⟩

/-! ## The loop over the queries -/

/-- The loop's state after `j` queries. -/
structure QInv (mu : Nat) (qs : Array UInt64) (ws pt : Array EW) (Q Wt Pt T S : UInt64)
    (s : QState) (j : Nat) (t : QState) : Prop where
  le : j ≤ qs.size
  bp : t.reg .rbp = S
  ax : t.reg .rax = (qs.size - j).toUInt64
  w0 : t.mem (wd S 0) = some (tot mu pt ws qs j).c0
  w1 : t.mem (wd S 1) = some (tot mu pt ws qs j).c1
  w2 : t.mem (wd S 2) = some (wd Q j)
  w3 : t.mem (wd S 3) = some (wd Wt (2 * j))
  w4 : t.mem (wd S 4) = some (qs.size - j).toUInt64
  w5 : t.mem (wd S 5) = some Pt
  w6 : t.mem (wd S 6) = some (min pt.size (mu + 1)).toUInt64
  w7 : t.mem (wd S 7) = some T
  w8 : t.mem (wd S 8) = some (mu + 1).toUInt64
  out : ∀ a, (∀ k < inducedScratchWords, a ≠ wd S k) → t.mem a = s.mem a
  dom : ∀ k < inducedScratchWords, (t.mem (wd S k)).isSome

/-- One query: `what` by `subAtC`, the product by `prodC`, added to the total. -/
def bodyC : Stmt := blk [
  I (.load .rax (at_ .rbp 16)), I (.load .rsi (at_ .rax 0)), I (.load .r13 (at_ .rbp 56)),
  I (.load .r15 (at_ .rbp 64)), I (.lea .r14 (at_ .rbp 128)),
  subAtC,
  I (.load .rax (at_ .rbp 24)), I (.load .r9 (at_ .rax 0)), I (.load .r10 (at_ .rax 8)),
  I (.load .r13 (at_ .rbp 40)), I (.lea .r14 (at_ .rbp 128)), I (.load .r15 (at_ .rbp 48)),
  prodC,
  I (.load .r11 (at_ .rbp 0)), I (.load .r12 (at_ .rbp 8)), I (.xor .r9 .r11), I (.xor .r10 .r12),
  I (.store (at_ .rbp 0) .r9), I (.store (at_ .rbp 8) .r10),
  I (.load .rax (at_ .rbp 16)), I (.addi .rax 8), I (.store (at_ .rbp 16) .rax),
  I (.load .rax (at_ .rbp 24)), I (.addi .rax 16), I (.store (at_ .rbp 24) .rax),
  I (.load .rax (at_ .rbp 32)), I (.subi .rax 1), I (.store (at_ .rbp 32) .rax)]

theorem bodyC_spec {mu : Nat} {qs : Array UInt64} {ws pt : Array EW} {Q Wt Pt T S : UInt64}
    {j : Nat} {t : QState}
    (hmu : mu ≤ 30) (hT : TableAt s.mem T (subspaceTable mu)) (hQ : WordArr s.mem Q qs)
    (hW : EWArr s.mem Wt ws) (hP : EWArr s.mem Pt pt) (hl : ws.size = qs.size)
    (hpt : pt.size ≤ 64) (hfS : Fits S inducedScratchWords) (hfQ : Fits Q qs.size)
    (hfW : Fits Wt (2 * ws.size)) (hfP : Fits Pt (2 * pt.size)) (hfT : Fits T (2 * (mu + 1)))
    (hSQ : Disj S inducedScratchWords Q qs.size)
    (hSW : Disj S inducedScratchWords Wt (2 * ws.size))
    (hSP : Disj S inducedScratchWords Pt (2 * pt.size))
    (hST : Disj S inducedScratchWords T (2 * (mu + 1)))
    (hI : QInv mu qs ws pt Q Wt Pt T S s j t) (hj : j < qs.size) :
    WP bodyC t (fun t' ↦ QInv mu qs ws pt Q Wt Pt T S s (j + 1) t') F := by
  have hsw : inducedScratchWords = 80 := rfl
  have hjw : j < ws.size := hl ▸ hj
  have hts : (subspaceTable mu).size = mu + 1 := subspaceTable_size mu
  have hwhat : (subspaceAtTable (subspaceTable mu) qs[j]).size = mu + 1 := by
    rw [subspaceAtTable_size, hts]
  have qv : t.mem (wd Q j) = some qs[j] := by
    rw [hI.out _ (fun k hk ↦ (wd_ne_of_disj hfS hfQ hSQ hk hj).symm)]
    exact hQ j hj
  have wv0 : t.mem (wd Wt (2 * j)) = some ws[j].c0 := by
    rw [hI.out _ (fun k hk ↦ (wd_ne_of_disj hfS hfW hSW hk (by omega)).symm)]
    exact (hW j hjw).1
  have wv1 : t.mem (wd (wd Wt (2 * j)) 1) = some ws[j].c1 := by
    rw [wd_wd, hI.out _ (fun k hk ↦ (wd_ne_of_disj hfS hfW hSW hk (by omega)).symm)]
    have := (hW j hjw).2
    rwa [wd_wd] at this
  have hTt : TableAt t.mem T (subspaceTable mu) := TableAt.congr (fun k hk ↦
    hI.out _ (fun k' hk' ↦ (wd_ne_of_disj hfS hfT hST hk' (by omega)).symm)) hT
  have hPt : EWArr t.mem Pt pt := EWArr.congr (n := 2 * pt.size) (fun k hk ↦
    hI.out _ (fun k' hk' ↦ (wd_ne_of_disj hfS hfP hSP hk' hk).symm)) le_rfl hP
  unfold bodyC
  refine wp_ld 2 hI.bp (by decide) hI.w2 ?_
  refine wp_ld 0 (b := wd Q j) (by rsimp) (by decide) (by rsimp; rw [wd_zero]; exact qv) ?_
  refine wp_ld 7 (by rsimp; exact hI.bp) (by decide) (by rsimp; exact hI.w7) ?_
  refine wp_ld 8 (by rsimp; exact hI.bp) (by decide) (by rsimp; exact hI.w8) ?_
  refine wp_lea 16 (by rsimp; exact hI.bp) (by decide) ?_
  refine NativeVm.Transcript.wp_then' (subAtC_spec (tb := subspaceTable mu) (T := T)
    (D := wd S 16) (x := qs[j]) hTt (by rsimp) (by rsimp; rw [hts]) (by rsimp) (by rsimp)
    (by omega) (fun k hk ↦ by rw [wd_wd]; exact hI.dom _ (by omega))
    (fits_sub hfS (by rw [hsw]; omega) (by omega)) (by rw [hts]; exact hfT)
    (by rw [hts]; exact disj_sub hfS hST (by rw [hsw]; omega) (by omega)))
    fun t6 ⟨a6, f6, r6⟩ d6 ↦ ?_
  simp only [QState.setReg_mem] at f6 d6
  have sl6 : ∀ k < 16, t6.mem (wd S k) = t.mem (wd S k) := fun k hk ↦
    f6 _ (fun k' hk' ↦ by rw [wd_wd]; exact wd_ne (by omega) (by omega) (by omega))
  have out6 : ∀ a, (∀ k < inducedScratchWords, a ≠ wd S k) → t6.mem a = t.mem a := fun a ha ↦
    f6 a (fun k' hk' ↦ by rw [wd_wd]; exact ha _ (by omega))
  have bp6 : t6.reg .rbp = S := by rw [r6 .rbp (by decide)]; rsimp; exact hI.bp
  have dom6 : ∀ k < inducedScratchWords, (t6.mem (wd S k)).isSome := fun k hk ↦ by
    rw [d6]; exact hI.dom k hk
  refine wp_ld 3 bp6 (by decide) (by rw [sl6 3 (by omega)]; exact hI.w3) ?_
  refine wp_ld 0 (b := wd Wt (2 * j)) (by rsimp) (by decide) (by
    rsimp
    rw [wd_zero, out6 _ (fun k hk ↦ (wd_ne_of_disj hfS hfW hSW hk (by omega)).symm)]
    exact wv0) ?_
  refine wp_ld 1 (b := wd Wt (2 * j)) (by rsimp) (by decide) (by
    rsimp
    rw [out6 _ (fun k hk ↦ by
      rw [wd_wd]; exact (wd_ne_of_disj hfS hfW hSW hk (by omega)).symm)]
    exact wv1) ?_
  refine wp_ld 5 (by rsimp; exact bp6) (by decide) (by rsimp; rw [sl6 5 (by omega)]; exact hI.w5) ?_
  refine wp_lea 16 (by rsimp; exact bp6) (by decide) ?_
  refine wp_ld 6 (by rsimp; exact bp6) (by decide) (by rsimp; rw [sl6 6 (by omega)]; exact hI.w6) ?_
  refine Field.WP.then (wp_regs prodRegs prodC_writes (prodC_spec (cs := pt)
    (vs := subspaceAtTable (subspaceTable mu) qs[j]) (m := min pt.size (mu + 1)) (Pp := Pt)
    (V := wd S 16) (w := ws[j]) (by omega) (by rw [hwhat]; omega) (by omega)
    (EWArr.congr (n := 2 * pt.size) (fun k hk ↦ out6 _
      (fun k' hk' ↦ (wd_ne_of_disj hfS hfP hSP hk' hk).symm)) le_rfl hPt)
    a6 (by rsimp) (by rsimp) (by rsimp) (by rsimp) (by rsimp)))
    fun t7 ⟨⟨p9, p10, pm⟩, r7⟩ ↦ ?_
  rsimp at pm
  have bp7 : t7.reg .rbp = S := by rw [r7 .rbp (by decide)]; rsimp; exact bp6
  have sl7 : ∀ k < 16, t7.mem (wd S k) = t.mem (wd S k) := fun k hk ↦ by rw [pm, sl6 k hk]
  have dom7 : ∀ k < inducedScratchWords, (t7.mem (wd S k)).isSome := fun k hk ↦ by
    rw [pm]; exact dom6 k hk
  rw [List.take_of_length_le (by simp [hwhat]), Array.foldl_toList] at p9 p10
  have ht := tot_succ mu pt hj hjw
  refine wp_ld 0 bp7 (by decide) (by rw [sl7 0 (by omega)]; exact hI.w0) ?_
  refine wp_ld 1 (by rsimp; exact bp7) (by decide) (by rsimp; rw [sl7 1 (by omega)]; exact hI.w1) ?_
  fstep; fstep
  refine wp_st 0 (by rsimp; exact bp7) (by decide) (by rsimp; exact dom7 0 (by decide)) ?_
  refine wp_st 1 (by rsimp; exact bp7) (by decide) (by sp_some; exact dom7 1 (by decide)) ?_
  refine wp_ld 2 (by rsimp; exact bp7) (by decide) (by
    rsimp; mem_simp; rw [sl7 2 (by omega)]; exact hI.w2) ?_
  fstep
  refine wp_st 2 (by rsimp; exact bp7) (by decide) (by sp_some; exact dom7 2 (by decide)) ?_
  refine wp_ld 3 (by rsimp; exact bp7) (by decide) (by
    rsimp; mem_simp; rw [sl7 3 (by omega)]; exact hI.w3) ?_
  fstep
  refine wp_st 3 (by rsimp; exact bp7) (by decide) (by sp_some; exact dom7 3 (by decide)) ?_
  refine wp_ld 4 (by rsimp; exact bp7) (by decide) (by
    rsimp; mem_simp; rw [sl7 4 (by omega)]; exact hI.w4) ?_
  fstep
  refine wp_st 4 (by rsimp; exact bp7) (by decide) (by sp_some; exact dom7 4 (by decide)) ?_
  apply WP.blk_nil
  refine ⟨by omega, by rsimp; exact bp7, by rsimp; exact cnt_succ hj, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · mem_simp; rw [ht, add_c0, p9]
  · mem_simp; rw [ht, add_c1, p10]
  · mem_simp; rw [wd8]
  · mem_simp; rw [wd16, show 2 * j + 2 = 2 * (j + 1) by omega]
  · mem_simp; rw [cnt_succ hj]
  · mem_simp; rw [sl7 5 (by omega)]; exact hI.w5
  · mem_simp; rw [sl7 6 (by omega)]; exact hI.w6
  · mem_simp; rw [sl7 7 (by omega)]; exact hI.w7
  · mem_simp; rw [sl7 8 (by omega)]; exact hI.w8
  · intro a ha
    simp only [QState.setReg_mem, QState.setMem_mem, ha 0 (by decide), ha 1 (by decide),
      ha 2 (by decide), ha 3 (by decide), ha 4 (by decide), ↓reduceIte]
    rw [pm, out6 a ha]
    exact hI.out a ha
  · intro k hk
    sp_some
    exact dom7 k hk

/-- The loop over the queries, their count in `rax`. -/
def queryLoopC : Stmt := .loop (.test false .rax (.reg .rax)) bodyC

/-- `rax := min rdx rax`. -/
def minC : Stmt := .ite (.cmp .ltu .rdx (.reg .rax)) (I (.mov .rax .rdx)) .skip

theorem minC_spec {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (hdx : s.reg .rdx = a.toUInt64)
    (hax : s.reg .rax = b.toUInt64) :
    WP minC s (fun s' ↦ s'.reg .rax = (min a b).toUInt64 ∧ s'.mem = s.mem ∧
      RegsFrame [.rax] s s') F := by
  unfold minC
  apply WP.ite
  have hc : (Cond.cmp .ltu .rdx (.reg .rax)).eval s = decide (a < b) := by
    rw [NativeVm.Transcript.cond_ltu, NativeVm.Transcript.rhs_reg, hdx, hax]
    exact decide_eq_decide.mpr (NativeVm.Transcript.toUInt64_lt ha hb)
  rw [hc]
  by_cases h : a < b
  · rw [decide_eq_true h]
    exact WP.ins' (by
      simp only [QInstr.step]
      exact ⟨by rsimp; rw [hdx, Nat.min_eq_left h.le], rfl, by rf_tac⟩)
  · rw [decide_eq_false h]
    exact WP.skip ⟨by rw [hax, Nat.min_eq_right (by omega)], rfl, fun _ _ ↦ rfl⟩

end Ind

open Ind Sp

/-- **The induced weight** `inducedWeight μ qs ws pt` in `(r9, r10)`: the queries at `r13`, the
weights at `r14`, the point at `rsi` (`rdx` elements), `r15` queries, the table
`subspaceTable μ` at `rcx`, `μ` in `rbp`, `inducedScratchWords` words of scratch at `rbx`. -/
def inducedC : Stmt := blk [
  I (.mov .rax .rbp), I (.addi .rax 1), minC, I (.store (at_ .rbx 48) .rax),
  I (.mov .rax .rbp), I (.addi .rax 1), I (.store (at_ .rbx 64) .rax),
  I (.storei (at_ .rbx 0) 0), I (.storei (at_ .rbx 8) 0),
  I (.store (at_ .rbx 16) .r13), I (.store (at_ .rbx 24) .r14), I (.store (at_ .rbx 32) .r15),
  I (.store (at_ .rbx 40) .rsi), I (.store (at_ .rbx 56) .rcx),
  I (.mov .rbp .rbx), I (.mov .rax .r15),
  queryLoopC,
  I (.load .r9 (at_ .rbp 0)), I (.load .r10 (at_ .rbp 8))]

/-- **`inducedC` computes `inducedWeight`.** -/
theorem inducedC_spec {s : QState} {F : QState → Prop} {mu : Nat} {qs : Array UInt64}
    {ws pt : Array EW} {Q Wt Pt T S : UInt64}
    (hmu : mu ≤ 30) (hT : TableAt s.mem T (subspaceTable mu)) (hQ : WordArr s.mem Q qs)
    (hW : EWArr s.mem Wt ws) (hP : EWArr s.mem Pt pt) (hl : ws.size = qs.size)
    (hq : qs.size ≤ 256) (hpt : pt.size ≤ 64)
    (h13 : s.reg .r13 = Q) (h14 : s.reg .r14 = Wt) (hsi : s.reg .rsi = Pt)
    (hdx : s.reg .rdx = pt.size.toUInt64) (h15 : s.reg .r15 = qs.size.toUInt64)
    (hcx : s.reg .rcx = T) (hbp : s.reg .rbp = mu.toUInt64) (hbx : s.reg .rbx = S)
    (hS : ∀ k < inducedScratchWords, (s.mem (wd S k)).isSome) (hfS : Fits S inducedScratchWords)
    (hfQ : Fits Q qs.size) (hfW : Fits Wt (2 * ws.size)) (hfP : Fits Pt (2 * pt.size))
    (hfT : Fits T (2 * (mu + 1)))
    (hSQ : Disj S inducedScratchWords Q qs.size)
    (hSW : Disj S inducedScratchWords Wt (2 * ws.size))
    (hSP : Disj S inducedScratchWords Pt (2 * pt.size))
    (hST : Disj S inducedScratchWords T (2 * (mu + 1))) :
    WP inducedC s (fun s' ↦ s'.reg .r9 = (inducedWeight mu qs ws pt).c0 ∧
      s'.reg .r10 = (inducedWeight mu qs ws pt).c1 ∧
      ∀ a, (∀ k < inducedScratchWords, a ≠ wd S k) → s'.mem a = s.mem a) F := by
  unfold inducedC
  fstep; fstep
  refine Field.WP.then (minC_spec (a := pt.size) (b := mu + 1) (by omega) (by omega)
    (by rsimp; exact hdx) (by rsimp; rw [hbp, NativeVm.Transcript.toUInt64_succ]))
    fun t1 ⟨x1, m1, f1⟩ ↦ ?_
  rsimp at m1
  have g1 : ∀ r, r ≠ .rax → t1.reg r = s.reg r := fun r hr ↦ by
    rw [f1 r (by simp [hr])]
    simp [hr]
  have d1 : ∀ k < inducedScratchWords, (t1.mem (wd S k)).isSome := fun k hk ↦ by
    rw [m1]; exact hS k hk
  have b1 : t1.reg .rbx = S := by rw [g1 .rbx (by decide), hbx]
  refine wp_st 6 b1 (by decide) (d1 6 (by decide)) ?_
  fstep; fstep
  refine wp_st 8 (by rsimp; exact b1) (by decide) (by sp_some; exact d1 8 (by decide)) ?_
  refine wp_sti 0 (by rsimp; exact b1) (by decide) (by sp_some; exact d1 0 (by decide)) ?_
  refine wp_sti 1 (by rsimp; exact b1) (by decide) (by sp_some; exact d1 1 (by decide)) ?_
  refine wp_st 2 (by rsimp; exact b1) (by decide) (by sp_some; exact d1 2 (by decide)) ?_
  refine wp_st 3 (by rsimp; exact b1) (by decide) (by sp_some; exact d1 3 (by decide)) ?_
  refine wp_st 4 (by rsimp; exact b1) (by decide) (by sp_some; exact d1 4 (by decide)) ?_
  refine wp_st 5 (by rsimp; exact b1) (by decide) (by sp_some; exact d1 5 (by decide)) ?_
  refine wp_st 7 (by rsimp; exact b1) (by decide) (by sp_some; exact d1 7 (by decide)) ?_
  fstep; fstep
  apply WP.blk_cons
  apply WP.loop (fun t ↦ ∃ j, QInv mu qs ws pt Q Wt Pt T S s j t)
    (fun t ↦ (t.reg .rax).toNat)
  · refine ⟨0, ⟨Nat.zero_le _, by rsimp; exact b1, by
      rsimp; rw [g1 .r15 (by decide), h15, Nat.sub_zero], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_⟩⟩
    · mem_simp; rfl
    · mem_simp; rfl
    · mem_simp; rw [g1 .r13 (by decide), h13, wd_zero]
    · mem_simp; rw [g1 .r14 (by decide), h14, Nat.mul_zero, wd_zero]
    · mem_simp; rw [g1 .r15 (by decide), h15, Nat.sub_zero]
    · mem_simp; rw [g1 .rsi (by decide), hsi]
    · mem_simp; rw [x1]
    · mem_simp; rw [g1 .rcx (by decide), hcx]
    · mem_simp; rw [g1 .rbp (by decide), hbp, NativeVm.Transcript.toUInt64_succ]
    · intro a ha
      simp only [QState.setReg_mem, QState.setMem_mem, ha 0 (by decide), ha 1 (by decide),
        ha 2 (by decide), ha 3 (by decide), ha 4 (by decide), ha 5 (by decide), ha 6 (by decide),
        ha 7 (by decide), ha 8 (by decide), ↓reduceIte]
      rw [m1]
    · intro k hk
      sp_some
      exact d1 k hk
  · intro t ⟨j, hI⟩ hc
    have hj : j < qs.size := cnt_lt (hI.ax ▸ cond_true hc)
    refine WP.mono (bodyC_spec hmu hT hQ hW hP hl hpt hfS hfQ hfW hfP hfT hSQ hSW hSP hST hI hj)
      (fun t' h' ↦ ⟨⟨j + 1, h'⟩, ?_⟩) (fun _ h ↦ h)
    rw [h'.ax, hI.ax]
    exact cnt_dec (by omega) hj
  · intro t ⟨j, hI⟩ hc
    have hj : j = qs.size := cnt_eq (by omega) hI.le (hI.ax ▸ cond_false hc)
    subst hj
    refine wp_ld 0 hI.bp (by decide) hI.w0 ?_
    refine wp_ld 1 (by rsimp; exact hI.bp) (by decide) (by rsimp; exact hI.w1) ?_
    apply WP.blk_nil
    refine ⟨by rsimp; rw [tot_full mu qs ws pt hl], by rsimp; rw [tot_full mu qs ws pt hl],
      fun a ha ↦ ?_⟩
    rsimp
    exact hI.out a ha

end NativeVm.Code.P7
