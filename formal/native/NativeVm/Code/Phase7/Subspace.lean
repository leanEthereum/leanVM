module

public import NativeVm.Code.Data
public import NativeVm.Field.KInv
public import NativeVm.Field.Arrays
public import NativeVm.Equiv.Field

/-!
# The subspace polynomials: their table and their values

`subTableC` writes `subspaceTable μ` (each root of `subspaceRoots μ`, then its inverse: two words
an entry, `TableAt`) at `r14`, from `μ` in `r15`, with `μ` words of scratch at `rbx` for the
layer. The layer starts `L[i] = 2^(i+1)`; step `j` maps `L[j..μ)` in place by
`v ↦ v·(v + last)` (`lstep`, the model's `v² + last·v`) and takes `L[j]` as root `j + 1`; then
`Field.kinv` inverts every root.

`subAtC` writes `subspaceAtTable tb x` at `r14`, the table at `r13` (`r15` entries), `x` in `rsi`:
per entry `(root, inverse)` the word `W·inverse`, then `W := W·(W + root)`.
-/

@[expose] public section

namespace NativeVm.Code.P7

open Native NativeVm.Model LeanVM.Parameters
open NativeVm.Transcript (wd Fits Disj wd_add wd_zero wd_inj wd_ne_of_disj toNat_toUInt64
  toUInt64_inj)

/-- The table `tb` at `p`: entry `i` in the words `2 i` and `2 i + 1`. -/
def TableAt (mem : UInt64 → Option UInt64) (p : UInt64) (tb : Array (UInt64 × UInt64)) : Prop :=
  ∀ i (h : i < tb.size), mem (wd p (2 * i)) = some tb[i].1 ∧ mem (wd p (2 * i + 1)) = some tb[i].2

namespace Sp

/-! ## Counters, addresses, stores -/

variable {s : QState} {P F : QState → Prop} {xs : List Stmt}

theorem cond_true {r : Reg64} {t : QState} (h : (Cond.test false r (.reg r)).eval t = true) :
    t.reg r ≠ 0 := by simpa [Cond.eval, Rhs.eval] using h

theorem cond_false {r : Reg64} {t : QState} (h : (Cond.test false r (.reg r)).eval t = false) :
    t.reg r = 0 := by simpa [Cond.eval, Rhs.eval] using h

theorem cnt_lt {n i : Nat} (h : (n - i).toUInt64 ≠ 0) : i < n := by
  by_contra hc
  exact h (by rw [show n - i = 0 by omega]; rfl)

theorem cnt_eq {n i : Nat} (hn : n < 2 ^ 64) (hi : i ≤ n) (h : (n - i).toUInt64 = 0) : i = n := by
  have := (toUInt64_inj (a := n - i) (b := 0) (by omega) (by norm_num)).mp h
  omega

theorem cnt_succ {n i : Nat} (hi : i < n) : (n - i).toUInt64 - 1 = (n - (i + 1)).toUInt64 := by
  rw [show n - i = n - (i + 1) + 1 by omega, Field.toUInt64_succ_sub]

theorem cnt_dec {n i : Nat} (hn : n < 2 ^ 64) (hi : i < n) :
    (n - (i + 1)).toUInt64.toNat < (n - i).toUInt64.toNat := by
  rw [toNat_toUInt64 (by omega), toNat_toUInt64 (by omega)]
  omega

theorem wd8 (b : UInt64) (k : Nat) : wd b k + 8 = wd b (k + 1) := wd_add b k 1

theorem wd16 (b : UInt64) (k : Nat) : wd b k + 16 = wd b (k + 2) := wd_add b k 2

theorem wd_ne {b : UInt64} {k k' : Nat} (hk : k < 2 ^ 61) (hk' : k' < 2 ^ 61) (h : k ≠ k') :
    wd b k ≠ wd b k' := fun e ↦ h ((wd_inj hk hk').mp e)

theorem setMem_ne {t : QState} {x a v : UInt64} (h : a ≠ x) : (t.setMem x v).mem a = t.mem a := by
  simp only [QState.setMem_mem, h, ↓reduceIte]

theorem setMem_same (t : QState) (x v : UInt64) : (t.setMem x v).mem x = some v := by
  simp only [QState.setMem_mem, ↓reduceIte]

theorem isSome_set {t : QState} {x : UInt64} (hx : (t.mem x).isSome) (v a : UInt64) :
    ((t.setMem x v).mem a).isSome = (t.mem a).isSome :=
  NativeVm.Transcript.isSome_setMem t v hx a

theorem WP.storei_at {r : Reg64} {disp k : Int64} (h : (s.mem (s.reg r + disp.toUInt64)).isSome)
    (k' : WP (blk xs) (s.setMem (s.reg r + disp.toUInt64) k.toUInt64) P F) :
    WP (blk (I (.storei (at_ r disp) k) :: xs)) s P F := by
  refine WP.blk_cons (WP.ins ?_ k')
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h
  simp [QInstr.step, Field.eval_at, hv]

/-- A register a kernel does not write, read back through the moves before it. -/
theorem notMem {r : Reg64} {l : List Reg64} (h : r ∉ l) (q : Reg64) (hq : q ∈ l) : r ≠ q :=
  fun e ↦ h (e ▸ hq)

/-! ## `K` words -/

theorem kmul_word {r a b : UInt64} (h : K.ofLane r = K.ofLane a * K.ofLane b) : r = kmul a b :=
  Field.ofLane_injective (h.trans (Equiv.K_ofLane_kmul a b).symm)

theorem kinv_word {r a : UInt64} (h : K.ofLane r = (K.ofLane a)⁻¹) : r = kinv a :=
  Field.ofLane_injective (h.trans (Equiv.K_ofLane_kinv a).symm)

/-! ## The roots -/

/-- The map of a layer step, `v ↦ v² + last·v`. -/
def lstep (last v : UInt64) : UInt64 := kmul v v ^^^ kmul last v

theorem lstep_word {r v last : UInt64} (h : K.ofLane r = K.ofLane v * K.ofLane (v ^^^ last)) :
    r = lstep last v := by
  apply Field.ofLane_injective
  rw [h, lstep, Equiv.K_ofLane_xor, Equiv.K_ofLane_xor, Equiv.K_ofLane_kmul, Equiv.K_ofLane_kmul]
  ring

/-- A step of `subspaceRoots`' fold. -/
def rootsStep (acc : Array UInt64 × UInt64 × Array UInt64) (_ : Nat) :
    Array UInt64 × UInt64 × Array UInt64 :=
  let (roots, last, layer) := acc
  match (layer.map fun v ↦ kmul v v ^^^ kmul last v).toList with
  | [] => (roots, last, #[])
  | root :: rest => (roots.push root, root, rest.toArray)

/-- The first layer, `2^(i+1)`. -/
def layer0 (mu : Nat) : Array UInt64 := (Array.range mu).map fun i ↦ (2 ^ (i + 1) : Nat).toUInt64

/-- The roots, the last root and the layer after `j` steps. -/
def rootsAfter (mu j : Nat) : Array UInt64 × UInt64 × Array UInt64 :=
  (List.range j).foldl rootsStep (#[1], 1, layer0 mu)

theorem subspaceRoots_eq (mu : Nat) : subspaceRoots mu = (rootsAfter mu mu).1 := (rfl)

theorem rootsAfter_succ (mu j : Nat) : rootsAfter mu (j + 1) = rootsStep (rootsAfter mu j) j := by
  rw [rootsAfter, rootsAfter, List.range_succ, List.foldl_append]
  rfl

theorem rootsStep_eq (roots : Array UInt64) (last : UInt64) (layer : Array UInt64)
    (h : 0 < layer.size) (x : Nat) :
    rootsStep (roots, last, layer) x = (roots.push (lstep last (layer.getD 0 0)),
      lstep last (layer.getD 0 0), (layer.toList.tail.map (lstep last)).toArray) := by
  rcases layer with ⟨_ | ⟨a, l⟩⟩
  · simp at h
  · simp [rootsStep, lstep]

theorem tail_getD (l : Array UInt64) (f : UInt64 → UInt64) {i : Nat} (h : i + 1 < l.size) :
    ((l.toList.tail.map f).toArray).getD i 0 = f (l.getD (i + 1) 0) := by
  rcases l with ⟨l⟩
  simp at h
  simp [Array.getD_eq_getD_getElem?, h]

theorem getD_push_lt {a : Array UInt64} (v : UInt64) {k : Nat} (h : k < a.size) :
    (a.push v).getD k 0 = a.getD k 0 := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_push, h, Nat.ne_of_lt h]

theorem getD_push_size (a : Array UInt64) (v : UInt64) : (a.push v).getD a.size 0 = v := by
  simp [Array.getD_eq_getD_getElem?]

theorem layer0_getD {mu k : Nat} (h : k < mu) :
    (layer0 mu).getD k 0 = (2 ^ (k + 1) : Nat).toUInt64 := by
  simp [layer0, Array.getD_eq_getD_getElem?, h]

theorem rootsAfter_size (mu : Nat) : ∀ j ≤ mu,
    (rootsAfter mu j).1.size = j + 1 ∧ (rootsAfter mu j).2.2.size = mu - j
  | 0, _ => by simp [rootsAfter, layer0]
  | j + 1, h => by
    obtain ⟨h1, h2⟩ := rootsAfter_size mu j (by omega)
    rw [rootsAfter_succ]
    rcases hr : rootsAfter mu j with ⟨R, last, Ly⟩
    rw [hr] at h1 h2
    rw [rootsStep_eq _ _ _ (by simp only at h2; omega)]
    simp only at h1 h2 ⊢
    simp [h1, h2]
    omega

/-- One step of the roots, as the code takes it. -/
theorem rootsAfter_step {mu j : Nat} (hj : j < mu) :
    (rootsAfter mu (j + 1)).1 = (rootsAfter mu j).1.push
      (lstep (rootsAfter mu j).2.1 ((rootsAfter mu j).2.2.getD 0 0)) ∧
    (rootsAfter mu (j + 1)).2.1 = lstep (rootsAfter mu j).2.1 ((rootsAfter mu j).2.2.getD 0 0) ∧
    ∀ i < mu - (j + 1), (rootsAfter mu (j + 1)).2.2.getD i 0 =
      lstep (rootsAfter mu j).2.1 ((rootsAfter mu j).2.2.getD (i + 1) 0) := by
  have h2 := (rootsAfter_size mu j hj.le).2
  rw [rootsAfter_succ]
  rcases hr : rootsAfter mu j with ⟨R, last, Ly⟩
  rw [hr] at h2
  simp only at h2
  rw [rootsStep_eq _ _ _ (by omega)]
  exact ⟨rfl, rfl, fun i hi ↦ tail_getD Ly _ (by omega)⟩

/-! ## The values -/

/-- A step of `subspaceAtTable`'s fold. -/
def atStep (acc : Array UInt64 × UInt64) (e : UInt64 × UInt64) : Array UInt64 × UInt64 :=
  (acc.1.push (kmul acc.2 e.2), kmul acc.2 acc.2 ^^^ kmul e.1 acc.2)

/-- The fold after the table's first `i` entries. -/
def atAfter (tb : Array (UInt64 × UInt64)) (x : UInt64) (i : Nat) : Array UInt64 × UInt64 :=
  (tb.toList.take i).foldl atStep (#[], x)

theorem atAfter_succ (tb : Array (UInt64 × UInt64)) (x : UInt64) {i : Nat} (h : i < tb.size) :
    atAfter tb x (i + 1) = atStep (atAfter tb x i) tb[i] := by
  rw [atAfter, atAfter, List.take_add_one, List.foldl_append]
  simp [h]

theorem atAfter_size (tb : Array (UInt64 × UInt64)) (x : UInt64) :
    ∀ i ≤ tb.size, (atAfter tb x i).1.size = i
  | 0, _ => rfl
  | i + 1, h => by
    rw [atAfter_succ tb x (by omega), atStep, Array.size_push, atAfter_size tb x i (by omega)]

theorem subspaceAtTable_eq (tb : Array (UInt64 × UInt64)) (x : UInt64) :
    subspaceAtTable tb x = (atAfter tb x tb.size).1 := by
  rw [atAfter, List.take_of_length_le (by simp), Array.foldl_toList]
  rfl

theorem atWord {r a b : UInt64} (h : K.ofLane r = K.ofLane a * K.ofLane (b ^^^ a)) :
    r = kmul a a ^^^ kmul b a := by
  apply Field.ofLane_injective
  rw [h, Equiv.K_ofLane_xor, Equiv.K_ofLane_xor, Equiv.K_ofLane_kmul, Equiv.K_ofLane_kmul]
  ring

end Sp

open Sp

theorem subspaceTable_size (mu : Nat) : (subspaceTable mu).size = mu + 1 := by
  rw [subspaceTable, Array.size_map, subspaceRoots_eq, (rootsAfter_size mu mu le_rfl).1]

theorem subspaceAtTable_size (tb : Array (UInt64 × UInt64)) (x : UInt64) :
    (subspaceAtTable tb x).size = tb.size := by
  rw [subspaceAtTable_eq, atAfter_size _ _ _ le_rfl]

/-! ## `subAtC` -/

/-- The registers `subAtC` writes. -/
abbrev atRegs : List Reg64 := [.rax, .rbx, .rcx, .r8, .rsi, .r13, .r14, .r15]

/-- `subspaceAtTable tb x` at `r14`: the table at `r13`, `r15` entries, `x` in `rsi`. -/
def subAtC : Stmt := .loop (.test false .r15 (.reg .r15)) (blk [
  I (.mov .rax .rsi), I (.load .rbx (at_ .r13 8)), Field.kmul, I (.store (at_ .r14 0) .rax),
  I (.load .rbx (at_ .r13 0)), I (.xor .rbx .rsi), I (.mov .rax .rsi), Field.kmul,
  I (.mov .rsi .rax), I (.addi .r13 16), I (.addi .r14 8), I (.subi .r15 1)])

/-- **`subAtC` writes `subspaceAtTable tb x`.** -/
theorem subAtC_spec {s : QState} {F : QState → Prop} {tb : Array (UInt64 × UInt64)}
    {T D x : UInt64} (hT : TableAt s.mem T tb) (h13 : s.reg .r13 = T)
    (h15 : s.reg .r15 = tb.size.toUInt64) (hsi : s.reg .rsi = x) (h14 : s.reg .r14 = D)
    (hn : tb.size ≤ 64) (hD : ∀ k < tb.size, (s.mem (wd D k)).isSome) (hfD : Fits D tb.size)
    (hfT : Fits T (2 * tb.size)) (hDT : Disj D tb.size T (2 * tb.size)) :
    WP subAtC s (fun s' ↦ WordArr s'.mem D (subspaceAtTable tb x) ∧
      (∀ a, (∀ k < tb.size, a ≠ wd D k) → s'.mem a = s.mem a) ∧ RegsFrame atRegs s s') F := by
  have hn64 : tb.size < 2 ^ 64 := by omega
  unfold subAtC
  apply WP.loop (fun t ↦ ∃ i ≤ tb.size, t.reg .r13 = wd T (2 * i) ∧ t.reg .r14 = wd D i ∧
      t.reg .r15 = (tb.size - i).toUInt64 ∧ t.reg .rsi = (atAfter tb x i).2 ∧
      (∀ k < i, t.mem (wd D k) = some ((atAfter tb x i).1.getD k 0)) ∧
      (∀ a, (∀ k < tb.size, a ≠ wd D k) → t.mem a = s.mem a) ∧
      (∀ a, (t.mem a).isSome = (s.mem a).isSome) ∧ RegsFrame atRegs s t)
    (fun t ↦ (t.reg .r15).toNat)
  · exact ⟨0, Nat.zero_le _, by rw [h13, Nat.mul_zero, wd_zero], by rw [h14, wd_zero],
      by rw [h15, Nat.sub_zero], hsi, fun k hk ↦ absurd hk (Nat.not_lt_zero _),
      fun _ _ ↦ rfl, fun _ ↦ rfl, Field.RegsFrame.refl _ _⟩
  · intro t ⟨i, hi, t13, t14, t15, tsi, hW, hF, hS, hf⟩ hc
    have hin : i < tb.size := cnt_lt (t15 ▸ cond_true hc)
    have hTw : ∀ m < 2 * tb.size, t.mem (wd T m) = s.mem (wd T m) := fun m hm ↦
      hF _ fun k hk ↦ (wd_ne_of_disj hfD hfT hDT hk hm).symm
    have hT0 : t.mem (wd T (2 * i)) = some tb[i].1 := by
      rw [hTw _ (by omega)]; exact (hT i hin).1
    have hT1 : t.mem (wd T (2 * i + 1)) = some tb[i].2 := by
      rw [hTw _ (by omega)]; exact (hT i hin).2
    have hDs : (t.mem (wd D i)).isSome := by rw [hS]; exact hD i hin
    fstep
    refine Field.WP.load_at (by rsimp; rw [t13, wd8]; exact hT1) ?_
    refine Field.WP.then (Field.kmul_spec _) fun t1 ⟨e1, m1, f1⟩ ↦ ?_
    rsimp at e1 m1
    rw [tsi] at e1
    have k1 : ∀ r ∉ Field.kRegs, t1.reg r = t.reg r := fun r hr ↦ by
      rw [f1 r hr]
      simp [notMem hr .rax (by decide), notMem hr .rbx (by decide)]
    have a1 : t1.reg .r14 + (0 : Int64).toUInt64 = wd D i := by
      rw [k1 .r14 (by decide), t14, Field.int64Zero_toUInt64, UInt64.add_zero]
    refine Field.WP.store_at (by rw [a1, m1]; exact hDs) ?_
    rw [a1]
    refine Field.WP.load_at (v := tb[i].1) (by
      rw [QState.setMem_reg, k1 .r13 (by decide), t13, Field.int64Zero_toUInt64, UInt64.add_zero,
        setMem_ne (wd_ne_of_disj hfT hfD hDT.symm (by omega) hin), m1]
      exact hT0) ?_
    fstep; fstep
    refine Field.WP.then (Field.kmul_spec _) fun t2 ⟨e2, m2, f2⟩ ↦ ?_
    rsimp at e2 m2
    rw [k1 .rsi (by decide), tsi] at e2
    have k2 : ∀ r ∉ Field.kRegs, t2.reg r = t1.reg r := fun r hr ↦ by
      rw [f2 r hr]
      simp [notMem hr .rax (by decide), notMem hr .rbx (by decide)]
    fstep; fstep; fstep; fstep; fdone
    have hstep := atAfter_succ tb x hin
    have hsz := atAfter_size tb x i hi
    refine ⟨⟨i + 1, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [k2 .r13 (by decide), k1 .r13 (by decide), t13, wd16]
      congr 1
    · rw [k2 .r14 (by decide), k1 .r14 (by decide), t14, wd8]
    · rw [k2 .r15 (by decide), k1 .r15 (by decide), t15, cnt_succ hin]
    · rw [hstep, atStep, atWord e2]
    · intro k hk
      rw [m2, hstep, atStep]
      rcases Nat.lt_or_ge k i with hk' | hk'
      · rw [setMem_ne (wd_ne (by omega) (by omega) (by omega)), m1, hW k hk',
          getD_push_lt _ (by omega)]
      · rw [show k = i by omega, setMem_same]
        have hp := getD_push_size (atAfter tb x i).1 (kmul (atAfter tb x i).2 tb[i].2)
        rw [hsz] at hp
        rw [hp, kmul_word e1]
    · intro a ha
      rw [m2, setMem_ne (ha i hin), m1]
      exact hF a ha
    · intro a
      rw [m2, isSome_set (by rw [m1]; exact hDs), m1]
      exact hS a
    · intro r hr
      have hr' := hr
      simp only [atRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
      obtain ⟨_, _, _, _, hsi', h13', h14', h15'⟩ := hr'
      have hk : r ∉ Field.kRegs := by simp [Field.kRegs, *]
      simp only [QState.setReg_reg, hsi', h13', h14', h15', ↓reduceIte, k2 r hk, k1 r hk]
      exact hf r hr
    · rw [k2 .r15 (by decide), k1 .r15 (by decide), t15, cnt_succ hin]
      exact cnt_dec hn64 hin
  · intro t ⟨i, hi, _, _, t15, _, hW, hF, _, hf⟩ hc
    have hin : i = tb.size := cnt_eq hn64 hi (t15 ▸ cond_false hc)
    subst hin
    refine ⟨fun k hk ↦ ?_, hF, hf⟩
    rw [subspaceAtTable_size] at hk
    rw [Array.getElem_eq_getD 0, subspaceAtTable_eq]
    exact hW k hk

namespace Sp

/-- The registers a statement writes are among `l`. -/
theorem wp_regs {c : Stmt} {s : QState} {P F : QState → Prop} (l : List Reg64)
    (hl : ∀ r, r ∉ l → c.writes r = false) (h : WP c s P F) :
    WP c s (fun s' ↦ P s' ∧ RegsFrame l s s') F :=
  WP.mono (NativeVm.Transcript.WP.frame h) (fun _ h' ↦ ⟨h'.1, fun r hr ↦ h'.2.2 r (hl r hr)⟩)
    fun _ h' ↦ h'.1

/-! ## The layer, the roots, the inverses -/

/-- `L[i] := 2^(i+1)` for `i < r15`, `L` at `r12`. -/
def initLayerC : Stmt := blk [
  I (.mov .r9 .r12), I (.mov .rdx .r15), I (.movi .rax 2),
  .loop (.test false .rdx (.reg .rdx)) (blk [
    I (.store (at_ .r9 0) .rax), I (.add .rax .rax), I (.addi .r9 8), I (.subi .rdx 1)])]

theorem initLayerC_spec {s : QState} {F : QState → Prop} {mu : Nat} {L : UInt64} (hmu : mu ≤ 30)
    (h12 : s.reg .r12 = L) (h15 : s.reg .r15 = mu.toUInt64)
    (hL : ∀ k < mu, (s.mem (wd L k)).isSome) :
    WP initLayerC s (fun s' ↦ (∀ k < mu, s'.mem (wd L k) = some ((layer0 mu).getD k 0)) ∧
      (∀ a, (∀ k < mu, a ≠ wd L k) → s'.mem a = s.mem a) ∧
      (∀ a, (s'.mem a).isSome = (s.mem a).isSome)) F := by
  unfold initLayerC
  fstep; fstep; fstep
  apply WP.blk_cons
  apply WP.loop (fun t ↦ ∃ i ≤ mu, t.reg .r9 = wd L i ∧ t.reg .rdx = (mu - i).toUInt64 ∧
      t.reg .rax = (2 ^ (i + 1) : Nat).toUInt64 ∧
      (∀ k < i, t.mem (wd L k) = some ((layer0 mu).getD k 0)) ∧
      (∀ a, (∀ k < mu, a ≠ wd L k) → t.mem a = s.mem a) ∧
      (∀ a, (t.mem a).isSome = (s.mem a).isSome))
    (fun t ↦ (t.reg .rdx).toNat)
  · refine ⟨0, Nat.zero_le _, ?_, ?_, ?_, fun k hk ↦ absurd hk (Nat.not_lt_zero _),
      fun _ _ ↦ rfl, fun _ ↦ rfl⟩ <;> rsimp
    · rw [h12, wd_zero]
    · rw [h15, Nat.sub_zero]
    · rfl
  · intro t ⟨i, hi, t9, tdx, tax, hW, hF, hS⟩ hc
    have hin : i < mu := cnt_lt (tdx ▸ cond_true hc)
    have hs : (t.mem (wd L i)).isSome := by rw [hS]; exact hL i hin
    have a0 : t.reg .r9 + (0 : Int64).toUInt64 = wd L i := by
      rw [t9, Field.int64Zero_toUInt64, UInt64.add_zero]
    refine Field.WP.store_at (by rw [a0]; exact hs) ?_
    rw [a0]
    fstep; fstep; fstep; fdone
    refine ⟨⟨i + 1, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [t9, wd8]
    · rw [tdx, cnt_succ hin]
    · rw [tax, NativeVm.Transcript.toUInt64_add]
      congr 1
      rw [pow_succ 2 (i + 1)]
      omega
    · intro k hk
      rcases Nat.lt_or_ge k i with hk' | hk'
      · rw [setMem_ne (wd_ne (by omega) (by omega) (by omega)), hW k hk']
      · rw [show k = i by omega, setMem_same, tax, layer0_getD hin]
    · intro a ha
      rw [setMem_ne (ha i hin)]
      exact hF a ha
    · intro a
      rw [isSome_set hs]
      exact hS a
    · rw [tdx, cnt_succ hin]
      exact cnt_dec (by omega) hin
  · intro t ⟨i, hi, _, tdx, _, hW, hF, hS⟩ hc
    have hin : i = mu := cnt_eq (by omega) hi (tdx ▸ cond_false hc)
    subst hin
    exact WP.blk_nil ⟨hW, hF, hS⟩

/-- `L[k] := v·(v + r10)` for the `rdx` words `v = L[k]` from `r9`. -/
def layerC : Stmt := .loop (.test false .rdx (.reg .rdx)) (blk [
  I (.load .rax (at_ .r9 0)), I (.mov .rbx .rax), I (.xor .rbx .r10), Field.kmul,
  I (.store (at_ .r9 0) .rax), I (.addi .r9 8), I (.subi .rdx 1)])

theorem layerC_spec {s : QState} {F : QState → Prop} {p : UInt64} {c : Nat} {vs : Nat → UInt64}
    (hc : c ≤ 64) (h9 : s.reg .r9 = p) (hdx : s.reg .rdx = c.toUInt64)
    (hv : ∀ k < c, s.mem (wd p k) = some (vs k)) :
    WP layerC s (fun s' ↦ (∀ k < c, s'.mem (wd p k) = some (lstep (s.reg .r10) (vs k))) ∧
      (∀ a, (∀ k < c, a ≠ wd p k) → s'.mem a = s.mem a) ∧
      (∀ a, (s'.mem a).isSome = (s.mem a).isSome)) F := by
  unfold layerC
  apply WP.loop (fun t ↦ ∃ i ≤ c, t.reg .r9 = wd p i ∧ t.reg .rdx = (c - i).toUInt64 ∧
      t.reg .r10 = s.reg .r10 ∧
      (∀ k < c, t.mem (wd p k) = some (if k < i then lstep (s.reg .r10) (vs k) else vs k)) ∧
      (∀ a, (∀ k < c, a ≠ wd p k) → t.mem a = s.mem a) ∧
      (∀ a, (t.mem a).isSome = (s.mem a).isSome))
    (fun t ↦ (t.reg .rdx).toNat)
  · refine ⟨0, Nat.zero_le _, by rw [h9, wd_zero], by rw [hdx, Nat.sub_zero], rfl,
      fun k hk ↦ ?_, fun _ _ ↦ rfl, fun _ ↦ rfl⟩
    rw [ite_eq_right (Nat.not_lt_zero k)]
    exact hv k hk
  · intro t ⟨i, hi, t9, tdx, t10, hW, hF, hS⟩ hc'
    have hin : i < c := cnt_lt (tdx ▸ cond_true hc')
    have hs : (t.mem (wd p i)).isSome := by rw [hW i hin]; rfl
    have a0 : t.reg .r9 + (0 : Int64).toUInt64 = wd p i := by
      rw [t9, Field.int64Zero_toUInt64, UInt64.add_zero]
    have hvi : t.mem (wd p i) = some (vs i) := by rw [hW i hin, ite_eq_right (Nat.lt_irrefl i)]
    refine Field.WP.load_at (by rw [a0]; exact hvi) ?_
    fstep; fstep
    refine Field.WP.then (Field.kmul_spec _) fun t1 ⟨e1, m1, f1⟩ ↦ ?_
    rsimp at e1 m1
    have k1 : ∀ r ∉ Field.kRegs, t1.reg r = t.reg r := fun r hr ↦ by
      rw [f1 r hr]
      simp [notMem hr .rax (by decide), notMem hr .rbx (by decide)]
    have a1 : t1.reg .r9 + (0 : Int64).toUInt64 = wd p i := by rw [k1 .r9 (by decide), a0]
    refine Field.WP.store_at (by rw [a1, m1]; exact hs) ?_
    rw [a1]
    fstep; fstep; fdone
    rw [t10] at e1
    refine ⟨⟨i + 1, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [k1 .r9 (by decide), t9, wd8]
    · rw [k1 .rdx (by decide), tdx, cnt_succ hin]
    · rw [k1 .r10 (by decide), t10]
    · intro k hk
      rcases Nat.lt_or_ge k i with hk' | hk'
      · rw [setMem_ne (wd_ne (by omega) (by omega) (by omega)), m1, hW k hk, ite_eq_left hk',
          ite_eq_left (by omega)]
      · rcases Nat.lt_or_ge i k with hk'' | hk''
        · rw [setMem_ne (wd_ne (by omega) (by omega) (by omega)), m1, hW k hk,
            ite_eq_right (by omega), ite_eq_right (by omega)]
        · rw [show k = i by omega, setMem_same, ite_eq_left (by omega), lstep_word e1]
    · intro a ha
      rw [setMem_ne (ha i hin), m1]
      exact hF a ha
    · intro a
      rw [isSome_set (by rw [m1]; exact hs), m1]
      exact hS a
    · rw [k1 .rdx (by decide), tdx, cnt_succ hin]
      exact cnt_dec (by omega) hin
  · intro t ⟨i, hi, _, tdx, _, hW, hF, hS⟩ hc'
    have hin : i = c := cnt_eq (by omega) hi (tdx ▸ cond_false hc')
    subst hin
    refine ⟨fun k hk ↦ ?_, hF, hS⟩
    rw [hW k hk, ite_eq_left hk]

theorem layerC_writes : ∀ r, r ∉ [Reg64.rax, .rbx, .rcx, .rdx, .r8, .r9] →
    layerC.writes r = false := by
  intro r hr
  cases r <;> first | rfl | exact absurd (by simp) hr

/-- The roots: step `j` maps `L[j..μ)` (`r12 = L + 8 j`, `r11 = μ - j` words) by `layerC` with
the last root in `r10`, and stores `L[j]` as root `j + 1` at `r14`. -/
def rootsC : Stmt := .loop (.test false .r11 (.reg .r11)) (blk [
  I (.mov .r9 .r12), I (.mov .rdx .r11), layerC,
  I (.load .r10 (at_ .r12 0)), I (.store (at_ .r14 0) .r10),
  I (.addi .r14 16), I (.addi .r12 8), I (.subi .r11 1)])

theorem rootsC_spec {s : QState} {F : QState → Prop} {mu : Nat} {T L : UInt64} (hmu : mu ≤ 30)
    (h12 : s.reg .r12 = L) (h11 : s.reg .r11 = mu.toUInt64) (h14 : s.reg .r14 = wd T 2)
    (h10 : s.reg .r10 = 1) (hT0 : s.mem (wd T 0) = some 1)
    (hL0 : ∀ k < mu, s.mem (wd L k) = some ((layer0 mu).getD k 0))
    (hT : ∀ k < 2 * (mu + 1), (s.mem (wd T k)).isSome)
    (hfT : Fits T (2 * (mu + 1))) (hfL : Fits L mu) (hTL : Disj T (2 * (mu + 1)) L mu) :
    WP rootsC s (fun s' ↦
      (∀ k ≤ mu, s'.mem (wd T (2 * k)) = some ((subspaceRoots mu).getD k 0)) ∧
      (∀ a, (∀ k < 2 * (mu + 1), a ≠ wd T k) → (∀ k < mu, a ≠ wd L k) → s'.mem a = s.mem a) ∧
      (∀ a, (s'.mem a).isSome = (s.mem a).isSome)) F := by
  have hTL' : ∀ {k m}, k < 2 * (mu + 1) → m < mu → wd T k ≠ wd L m :=
    fun hk hm ↦ wd_ne_of_disj hfT hfL hTL hk hm
  unfold rootsC
  apply WP.loop (fun t ↦ ∃ j ≤ mu, t.reg .r12 = wd L j ∧ t.reg .r11 = (mu - j).toUInt64 ∧
      t.reg .r14 = wd T (2 * (j + 1)) ∧ t.reg .r10 = (rootsAfter mu j).2.1 ∧
      (∀ k ≤ j, t.mem (wd T (2 * k)) = some ((rootsAfter mu j).1.getD k 0)) ∧
      (∀ i < mu - j, t.mem (wd L (j + i)) = some ((rootsAfter mu j).2.2.getD i 0)) ∧
      (∀ a, (∀ k < 2 * (mu + 1), a ≠ wd T k) → (∀ k < mu, a ≠ wd L k) → t.mem a = s.mem a) ∧
      (∀ a, (t.mem a).isSome = (s.mem a).isSome))
    (fun t ↦ (t.reg .r11).toNat)
  · refine ⟨0, Nat.zero_le _, by rw [h12, wd_zero], by rw [h11, Nat.sub_zero], h14, h10,
      fun k hk ↦ ?_, fun i hi ↦ ?_, fun _ _ _ ↦ rfl, fun _ ↦ rfl⟩
    · rw [show k = 0 by omega]
      exact hT0
    · rw [Nat.zero_add]
      exact hL0 i (by omega)
  · intro t ⟨j, hj, t12, t11, t14, t10, hR, hLy, hF, hS⟩ hc
    have hjn : j < mu := cnt_lt (t11 ▸ cond_true hc)
    obtain ⟨sR, sL⟩ := rootsAfter_size mu j hj
    obtain ⟨stR, stl, stL⟩ := rootsAfter_step hjn
    fstep; fstep
    refine Field.WP.then (wp_regs _ layerC_writes (layerC_spec (p := wd L j) (c := mu - j)
      (vs := fun i ↦ (rootsAfter mu j).2.2.getD i 0) (by omega) (by rsimp; exact t12)
      (by rsimp; exact t11) (fun k hk ↦ by rsimp; rw [wd_wd]; exact hLy k hk)))
      fun t1 ⟨⟨l1, lf1, ls1⟩, rf1⟩ ↦ ?_
    simp only [QState.setReg_reg, reduceCtorEq, ↓reduceIte, t10] at l1
    simp only [QState.setReg_mem] at lf1 ls1
    have g1 : ∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → r ≠ .rdx → r ≠ .r8 → r ≠ .r9 →
        t1.reg r = t.reg r := fun r ha hb hc hd h8 h9 ↦ by
      rw [rf1 r (by simp [ha, hb, hc, hd, h8, h9])]
      simp [hd, h9]
    have e12 : t1.reg .r12 = wd L j := by
      rw [g1 .r12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), t12]
    have e14 : t1.reg .r14 = wd T (2 * (j + 1)) := by
      rw [g1 .r14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), t14]
    have e11 : t1.reg .r11 = (mu - j).toUInt64 := by
      rw [g1 .r11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), t11]
    have v0 : t1.mem (wd L j) =
        some (lstep (rootsAfter mu j).2.1 ((rootsAfter mu j).2.2.getD 0 0)) := by
      have := l1 0 (by omega)
      rwa [wd_zero] at this
    refine Field.WP.load_at (by rw [e12, Field.int64Zero_toUInt64, UInt64.add_zero]; exact v0) ?_
    have hTs : (t1.mem (wd T (2 * (j + 1)))).isSome := by rw [ls1, hS]; exact hT _ (by omega)
    have a1 : (t1.setReg .r10 (lstep (rootsAfter mu j).2.1 ((rootsAfter mu j).2.2.getD 0 0))).reg
        .r14 + (0 : Int64).toUInt64 = wd T (2 * (j + 1)) := by
      rsimp
      rw [e14, UInt64.add_zero]
    refine Field.WP.store_at (by rw [a1, QState.setReg_mem]; exact hTs) ?_
    rw [a1]
    fstep; fstep; fstep; fdone
    refine ⟨⟨j + 1, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [e12, wd8]
    · rw [e11, cnt_succ hjn]
    · rw [e14, wd16, show 2 * (j + 1) + 2 = 2 * (j + 1 + 1) by omega]
    · rw [stl]
    · intro k hk
      rw [stR]
      rcases Nat.lt_or_ge k (j + 1) with hk' | hk'
      · rw [setMem_ne (wd_ne (by omega) (by omega) (by omega)), QState.setReg_mem,
          lf1 _ (fun m hm ↦ by rw [wd_wd]; exact hTL' (by omega) (by omega)), hR k (by omega),
          getD_push_lt _ (by omega)]
      · have hp := getD_push_size (rootsAfter mu j).1
          (lstep (rootsAfter mu j).2.1 ((rootsAfter mu j).2.2.getD 0 0))
        rw [sR] at hp
        rw [show k = j + 1 by omega, setMem_same, hp]
    · intro i hi
      rw [stL i hi, setMem_ne (hTL' (by omega) (by omega)).symm, QState.setReg_mem]
      have := l1 (i + 1) (by omega)
      rwa [wd_wd, show j + (i + 1) = j + 1 + i by omega] at this
    · intro a haT haL
      rw [setMem_ne (haT _ (by omega)), QState.setReg_mem,
        lf1 a (fun m hm ↦ by rw [wd_wd]; exact haL _ (by omega))]
      exact hF a haT haL
    · intro a
      rw [isSome_set (by rw [QState.setReg_mem]; exact hTs), QState.setReg_mem, ls1]
      exact hS a
    · rw [e11, cnt_succ hjn, t11]
      exact cnt_dec (by omega) hjn
  · intro t ⟨j, hj, _, t11, _, _, hR, _, hF, hS⟩ hc
    have hjn : j = mu := cnt_eq (by omega) hj (t11 ▸ cond_false hc)
    subst hjn
    exact ⟨fun k hk ↦ by rw [subspaceRoots_eq]; exact hR k hk, hF, hS⟩

/-- The registers `rootsC` writes. -/
abbrev rootsRegs : List Reg64 := [.rax, .rbx, .rcx, .rdx, .r8, .r9, .r10, .r11, .r12, .r14]

theorem rootsC_writes : ∀ r, r ∉ rootsRegs → rootsC.writes r = false := by
  intro r hr
  cases r <;> first | rfl | exact absurd (by simp) hr

theorem initLayerC_writes : ∀ r, r ∉ [Reg64.rax, .rdx, .r9] → initLayerC.writes r = false := by
  intro r hr
  cases r <;> first | rfl | exact absurd (by simp) hr

/-- Each entry's second word, the inverse of its first: `r14` at the table, `r11` entries. -/
def invC : Stmt := .loop (.test false .r11 (.reg .r11)) (blk [
  I (.load .rax (at_ .r14 0)), Field.kinv, I (.store (at_ .r14 8) .rax),
  I (.addi .r14 16), I (.subi .r11 1)])

theorem invC_spec {s : QState} {F : QState → Prop} {n : Nat} {p : UInt64} {R : Nat → UInt64}
    (hn : n ≤ 64) (h14 : s.reg .r14 = p) (h11 : s.reg .r11 = n.toUInt64)
    (hR : ∀ k < n, s.mem (wd p (2 * k)) = some (R k))
    (hS : ∀ k < 2 * n, (s.mem (wd p k)).isSome) :
    WP invC s (fun s' ↦ (∀ k < n, s'.mem (wd p (2 * k)) = some (R k) ∧
      s'.mem (wd p (2 * k + 1)) = some (kinv (R k))) ∧
      (∀ a, (∀ k < 2 * n, a ≠ wd p k) → s'.mem a = s.mem a)) F := by
  unfold invC
  apply WP.loop (fun t ↦ ∃ i ≤ n, t.reg .r14 = wd p (2 * i) ∧ t.reg .r11 = (n - i).toUInt64 ∧
      (∀ k < n, t.mem (wd p (2 * k)) = some (R k)) ∧
      (∀ k < i, t.mem (wd p (2 * k + 1)) = some (kinv (R k))) ∧
      (∀ a, (∀ k < 2 * n, a ≠ wd p k) → t.mem a = s.mem a) ∧
      (∀ k < 2 * n, (t.mem (wd p k)).isSome))
    (fun t ↦ (t.reg .r11).toNat)
  · exact ⟨0, Nat.zero_le _, by rw [h14, Nat.mul_zero, wd_zero], by rw [h11, Nat.sub_zero], hR,
      fun k hk ↦ absurd hk (Nat.not_lt_zero _), fun _ _ ↦ rfl, hS⟩
  · intro t ⟨i, hi, t14, t11, hE, hO, hF, hS'⟩ hc
    have hin : i < n := cnt_lt (t11 ▸ cond_true hc)
    refine Field.WP.load_at
      (by rw [t14, Field.int64Zero_toUInt64, UInt64.add_zero]; exact hE i hin) ?_
    refine Field.WP.then (Field.kinv_spec _) fun t1 ⟨e1, m1, f1⟩ ↦ ?_
    rsimp at e1 m1
    have k1 : ∀ r ∉ Field.kinvRegs, t1.reg r = t.reg r := fun r hr ↦ by
      rw [f1 r hr]
      simp [notMem hr .rax (by decide)]
    have a1 : t1.reg .r14 + (8 : Int64).toUInt64 = wd p (2 * i + 1) := by
      simp only [Field.int64Lit_toUInt64]
      rw [k1 .r14 (by decide), t14, wd8]
    have hs1 : (t1.mem (wd p (2 * i + 1))).isSome := by rw [m1]; exact hS' _ (by omega)
    refine Field.WP.store_at (by rw [a1]; exact hs1) ?_
    rw [a1]
    fstep; fstep; fdone
    refine ⟨⟨i + 1, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [k1 .r14 (by decide), t14, wd16, show 2 * i + 2 = 2 * (i + 1) by omega]
    · rw [k1 .r11 (by decide), t11, cnt_succ hin]
    · intro k hk
      rw [setMem_ne (wd_ne (by omega) (by omega) (by omega)), m1]
      exact hE k hk
    · intro k hk
      rcases Nat.lt_or_ge k i with hk' | hk'
      · rw [setMem_ne (wd_ne (by omega) (by omega) (by omega)), m1]
        exact hO k hk'
      · rw [show k = i by omega, setMem_same, kinv_word e1]
    · intro a ha
      rw [setMem_ne (ha _ (by omega)), m1]
      exact hF a ha
    · intro k hk
      rw [isSome_set hs1, m1]
      exact hS' k hk
    · rw [k1 .r11 (by decide), t11, cnt_succ hin]
      exact cnt_dec (by omega) hin
  · intro t ⟨i, hi, _, t11, hE, hO, hF, _⟩ hc
    have : i = n := cnt_eq (by omega) hi (t11 ▸ cond_false hc)
    subst this
    exact ⟨fun k hk ↦ ⟨hE k hk, hO k hk⟩, hF⟩

end Sp

/-! ## `subTableC` -/

/-- `subspaceTable μ` at `r14`, `μ` in `r15`, `μ` words of scratch at `rbx`. -/
def subTableC : Stmt := blk [
  I (.mov .r12 .rbx), I (.mov .r13 .r14),
  initLayerC,
  I (.storei (at_ .r14 0) 1), I (.movi .r10 1), I (.addi .r14 16), I (.mov .r11 .r15),
  rootsC,
  I (.mov .r14 .r13), I (.mov .r11 .r15), I (.addi .r11 1),
  invC]

/-- **`subTableC` writes `subspaceTable μ`.** -/
theorem subTableC_spec {s : QState} {F : QState → Prop} {mu : Nat} {T L : UInt64} (hmu : mu ≤ 30)
    (h15 : s.reg .r15 = mu.toUInt64) (h14 : s.reg .r14 = T) (hbx : s.reg .rbx = L)
    (hT : ∀ k < 2 * (mu + 1), (s.mem (wd T k)).isSome) (hL : ∀ k < mu, (s.mem (wd L k)).isSome)
    (hfT : Fits T (2 * (mu + 1))) (hfL : Fits L mu) (hTL : Disj T (2 * (mu + 1)) L mu) :
    WP subTableC s (fun s' ↦ TableAt s'.mem T (subspaceTable mu) ∧
      ∀ a, (∀ k < 2 * (mu + 1), a ≠ wd T k) → (∀ k < mu, a ≠ wd L k) → s'.mem a = s.mem a) F := by
  have hTL' : ∀ {k m}, k < 2 * (mu + 1) → m < mu → wd T k ≠ wd L m :=
    fun hk hm ↦ wd_ne_of_disj hfT hfL hTL hk hm
  unfold subTableC
  fstep; fstep
  refine Field.WP.then (wp_regs _ initLayerC_writes
    (initLayerC_spec hmu (L := L) (by rsimp; exact hbx) (by rsimp; exact h15)
      (by rsimp; exact hL)))
    fun t1 ⟨⟨l1, lf1, ls1⟩, rf1⟩ ↦ ?_
  simp only [QState.setReg_mem] at lf1 ls1
  have e14 : t1.reg .r14 = T := by rw [rf1 .r14 (by decide)]; rsimp; exact h14
  have e13 : t1.reg .r13 = T := by rw [rf1 .r13 (by decide)]; rsimp; exact h14
  have e12 : t1.reg .r12 = L := by rw [rf1 .r12 (by decide)]; rsimp; exact hbx
  have e15 : t1.reg .r15 = mu.toUInt64 := by rw [rf1 .r15 (by decide)]; rsimp; exact h15
  have hT0 : (t1.mem (wd T 0)).isSome := by rw [ls1]; exact hT 0 (by omega)
  have a0 : t1.reg .r14 + (0 : Int64).toUInt64 = wd T 0 := by
    rw [e14, Field.int64Zero_toUInt64, UInt64.add_zero, wd_zero]
  refine Sp.WP.storei_at (by rw [a0]; exact hT0) ?_
  rw [a0]
  fstep; fstep; fstep
  refine Field.WP.then (wp_regs _ rootsC_writes (rootsC_spec hmu (L := L) (by rsimp; exact e12)
    (by rsimp; exact e15) (by rsimp; rw [e14, ← wd16, wd_zero]) (by rsimp)
    (by rsimp; exact setMem_same _ _ _)
    (fun k hk ↦ by rsimp; rw [setMem_ne (hTL' (by omega) hk).symm]; exact l1 k hk)
    (fun k hk ↦ by rsimp; rw [isSome_set hT0, ls1]; exact hT k hk) hfT hfL hTL))
    fun t2 ⟨⟨r2, f2, s2⟩, rf2⟩ ↦ ?_
  simp only [QState.setReg_mem] at f2 s2
  have e13' : t2.reg .r13 = T := by rw [rf2 .r13 (by decide)]; rsimp; exact e13
  have e15' : t2.reg .r15 = mu.toUInt64 := by rw [rf2 .r15 (by decide)]; rsimp; exact e15
  fstep; fstep; fstep
  refine Field.WP.then (invC_spec (n := mu + 1) (p := T)
    (R := fun k ↦ (subspaceRoots mu).getD k 0) (by omega) (by rsimp; exact e13')
    (by rsimp; rw [e15', NativeVm.Transcript.toUInt64_succ])
    (fun k hk ↦ by rsimp; exact r2 k (by omega))
    (fun k hk ↦ by rsimp; rw [s2, isSome_set hT0, ls1]; exact hT k hk))
    fun t3 ⟨i3, f3⟩ ↦ ?_
  simp only [QState.setReg_mem] at f3
  refine WP.blk_nil ⟨fun i hi ↦ ?_, fun a haT haL ↦ ?_⟩
  · have hi' : i < mu + 1 := by rwa [subspaceTable_size] at hi
    simp only [subspaceTable, Array.getElem_map]
    rw [Array.getElem_eq_getD 0]
    exact i3 i hi'
  · rw [f3 a haT, f2 a haT haL, setMem_ne (haT 0 (by omega)), lf1 a haL]

end NativeVm.Code.P7
