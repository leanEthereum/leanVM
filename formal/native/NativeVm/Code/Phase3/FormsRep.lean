module

public import NativeVm.Code.Phase3.FormsCode
public import NativeVm.Code.Phase3.FormsModel

/-!
# The bus forms of a side: forms in words

Every address is a word of the working area (`wd w k`). A monomial's key (`KeyAt`): its degree and
two columns, zero past the degree; a term (`TZ`): the key, then the coefficient (`EAtI`); a form
(`FZ`): the term count, then term `i` at word `1 + 5 i`: `FormAt` with the unused column words zero
(`FZ.formAt`). `KeepS w S` says a run wrote only words `wd w k` with `S k`. The steps `ldw`, `stw`,
`ldx` run a load or store at a word given by a register.
-/

@[expose] public section

namespace NativeVm.Code.P3

open Native NativeVm.Model NativeVm.Code NativeVm.Transcript

variable {mem mem' : UInt64 → Option UInt64} {w : UInt64}

/-! ## The scratch's offsets -/

theorem ftOff_val : ftOff = 60862 := by
  show scratchR.off + 8192 = _
  rw [scratchR_off]

theorem padOff_val : padOff = 60862 := by unfold padOff; rw [ftOff_val]
theorem fOff_val : fOff = 60990 := by unfold fOff; rw [ftOff_val]
theorem wvOff_val : wvOff = 61182 := by unfold wvOff; rw [ftOff_val]
theorem bvOff_val : bvOff = 61214 := by unfold bvOff; rw [ftOff_val]
theorem vCur_val : vCur = 61162 := by unfold vCur; rw [ftOff_val]
theorem vSel_val : vSel = 61163 := by unfold vSel; rw [ftOff_val]
theorem vRem_val : vRem = 61164 := by unfold vRem; rw [ftOff_val]
theorem vG_val : vG = 61165 := by unfold vG; rw [ftOff_val]
theorem dOff_val : dOff = 61374 := by unfold dOff; rw [ftOff_val]
theorem fCap_val : fCap = 32 := rfl

/-- The block form's words. -/
def SF (k : Nat) : Prop := fOff ≤ k ∧ k < fOff + 1 + 5 * fCap

/-- Unfold the scratch's offsets, then `omega`. -/
scoped macro "oo" : tactic => `(tactic| (
  (try (set_option simprocs false in simp only [fOff_val, padOff_val, wvOff_val, bvOff_val, vCur_val,
    vSel_val, vRem_val, vG_val, dOff_val, fCap_val, ftOff_val, dataEnd_eq, SF] at *)) <;>
  first | omega | simp))

/-! ## Forms in words -/

/-- The key of `m` from word `q`: degree, columns `0` and `1` (zero past the degree). -/
def KeyAt (mem : UInt64 → Option UInt64) (w : UInt64) (q : Nat) (m : Array Nat) : Prop :=
  m.size ≤ 2 ∧ (∀ i (h : i < m.size), m[i] < 2 ^ 64) ∧ mem (wd w q) = some m.size.toUInt64 ∧
    mem (wd w (q + 1)) = some (m.getD 0 0).toUInt64 ∧ mem (wd w (q + 2)) = some (m.getD 1 0).toUInt64

/-- The element `x` in words `q`, `q + 1`. -/
def EAtI (mem : UInt64 → Option UInt64) (w : UInt64) (q : Nat) (x : EW) : Prop :=
  mem (wd w q) = some x.c0 ∧ mem (wd w (q + 1)) = some x.c1

/-- A term from word `q`: its key, then its coefficient. -/
def TZ (mem : UInt64 → Option UInt64) (w : UInt64) (q : Nat) (t : TermW) : Prop :=
  KeyAt mem w q t.cols ∧ EAtI mem w (q + 3) t.coeff

/-- A form of at most `cap` terms from word `p`: the count, then term `i` at word `p + 1 + 5 i`. -/
def FZ (mem : UInt64 → Option UInt64) (w : UInt64) (p cap : Nat) (f : FormW) : Prop :=
  f.size ≤ cap ∧ mem (wd w p) = some f.size.toUInt64 ∧
    ∀ i (h : i < f.size), TZ mem w (p + 1 + 5 * i) f[i]

theorem KeyAt.congr {q : Nat} {m : Array Nat} (h : ∀ k < 3, mem' (wd w (q + k)) = mem (wd w (q + k)))
    (hk : KeyAt mem w q m) : KeyAt mem' w q m :=
  ⟨hk.1, hk.2.1, by rw [← Nat.add_zero q, h 0 (by omega)]; exact hk.2.2.1,
    by rw [h 1 (by omega)]; exact hk.2.2.2.1, by rw [h 2 (by omega)]; exact hk.2.2.2.2⟩

theorem EAtI.congr {q : Nat} {x : EW} (h : ∀ k < 2, mem' (wd w (q + k)) = mem (wd w (q + k)))
    (hx : EAtI mem w q x) : EAtI mem' w q x :=
  ⟨by rw [← Nat.add_zero q, h 0 (by omega)]; exact hx.1, by rw [h 1 (by omega)]; exact hx.2⟩

theorem TZ.congr {q : Nat} {t : TermW} (h : ∀ k < 5, mem' (wd w (q + k)) = mem (wd w (q + k)))
    (ht : TZ mem w q t) : TZ mem' w q t :=
  ⟨ht.1.congr fun k hk ↦ h k (by omega),
    ht.2.congr fun k hk ↦ by rw [Nat.add_assoc]; exact h (3 + k) (by omega)⟩

theorem FZ.congr {p cap : Nat} {f : FormW}
    (h : ∀ k < 1 + 5 * cap, mem' (wd w (p + k)) = mem (wd w (p + k))) (hf : FZ mem w p cap f) :
    FZ mem' w p cap f := by
  refine ⟨hf.1, by rw [← Nat.add_zero p, h 0 (by omega)]; exact hf.2.1, fun i hi ↦ ?_⟩
  refine (hf.2.2 i hi).congr fun k hk ↦ ?_
  have := hf.1
  rw [show p + 1 + 5 * i + k = p + (1 + 5 * i + k) by omega]
  exact h _ (by omega)

/-- `FZ` is `FormAt` with zero column words. -/
theorem FZ.formAt {p cap : Nat} {f : FormW} (hf : FZ mem w p cap f) (hcap : cap ≤ formCap) :
    FormAt mem (wd w p) f := by
  refine ⟨by have := hf.1; omega, ⟨by have := hf.1; unfold formCap at hcap; omega, hf.2.1⟩,
    fun i hi ↦ ?_⟩
  obtain ⟨⟨hs, hb, h0, h1, h2⟩, c0, c1⟩ := hf.2.2 i hi
  have ix : ∀ a b, a = b → mem (wd w a) = mem (wd w b) := fun a b e ↦ by rw [e]
  refine ⟨hs, ⟨by omega, by rw [wd_wd, ix _ (p + 1 + 5 * i) (by unfold termWords monoCap; omega)]; exact h0⟩,
    fun j hj ↦ ⟨hb j hj, ?_⟩,
    by rw [wd_wd, wd_wd, ix _ (p + 1 + 5 * i + 3) (by unfold termWords monoCap; omega)]; exact c0,
    by rw [wd_wd, wd_wd, wd_wd, ix _ (p + 1 + 5 * i + 3 + 1) (by unfold termWords monoCap; omega)]
       exact c1⟩
  rw [wd_wd, wd_wd, ix _ (p + 1 + 5 * i + (1 + j)) (by unfold termWords monoCap; omega)]
  rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
  · rw [h1]; congr 2; rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj]; rfl
  · rw [h2]; congr 2; rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj]; rfl

/-! ## What a run wrote -/

/-- `mem'` is `mem` but at the words `wd w k` with `S k`. -/
def KeepS (w : UInt64) (S : Nat → Prop) (mem mem' : UInt64 → Option UInt64) : Prop :=
  ∀ a, (∀ k, S k → a ≠ wd w k) → mem' a = mem a

theorem KeepS.refl (S : Nat → Prop) (mem : UInt64 → Option UInt64) : KeepS w S mem mem :=
  fun _ _ ↦ rfl

theorem KeepS.trans {S T : Nat → Prop} {m₁ m₂ m₃ : UInt64 → Option UInt64} (h₁ : KeepS w S m₁ m₂)
    (h₂ : KeepS w T m₂ m₃) {U : Nat → Prop} (hS : ∀ k, S k → U k) (hT : ∀ k, T k → U k) :
    KeepS w U m₁ m₃ :=
  fun a ha ↦ (h₂ a fun k hk ↦ ha k (hT k hk)).trans (h₁ a fun k hk ↦ ha k (hS k hk))

theorem KeepS.mono {S T : Nat → Prop} (h : KeepS w S mem mem') (hST : ∀ k, S k → T k) :
    KeepS w T mem mem' :=
  fun a ha ↦ h a fun k hk ↦ ha k (hST k hk)

theorem KeepS.setMem {S : Nat → Prop} {s s' : QState} (h : KeepS w S s.mem s'.mem) {k : Nat}
    (hk : S k) (v : UInt64) : KeepS w S s.mem (s'.setMem (wd w k) v).mem := fun a ha ↦ by
  rw [QState.setMem_mem, ite_eq_right_of_eq_false _ _ (eq_false (ha k hk))]
  exact h a ha

theorem KeepS.setReg' {S : Nat → Prop} {s' : QState} (h : KeepS w S mem s'.mem) {r : Reg64}
    {v : UInt64} : KeepS w S mem (s'.setReg r v).mem := h

/-- Peel register updates and stores to words of `S` off a `KeepS` goal. -/
scoped macro "keep_tac" : tactic => `(tactic| (repeat (first
  | with_reducible refine NativeVm.Code.P3.KeepS.setReg' ?_
  | (refine NativeVm.Code.P3.KeepS.setMem ?_ ?_ _; on_goal 2 => oo)
  | exact NativeVm.Code.P3.KeepS.refl _ _)))

/-- A word outside the written ones is kept. -/
theorem KeepS.word {S : Nat → Prop} (h : KeepS w S mem mem') {k : Nat} (hk : k < 2 ^ 61)
    (hS : ∀ j, S j → j < 2 ^ 61 ∧ j ≠ k) : mem' (wd w k) = mem (wd w k) :=
  h _ fun j hj e ↦ (hS j hj).2 ((wd_inj (hS j hj).1 hk).mp e.symm)

/-- Peel register and memory updates off a `RegsFrame` goal, each register written in the list. -/
scoped macro "rfx" : tactic => `(tactic| (repeat (first
  | with_reducible refine NativeVm.Transcript.rf_setMem ?_ _ _
  | with_reducible refine NativeVm.Transcript.rf_setReg ?_ (by simp) _)))

/-! ## Steps -/

variable {s : QState} {P E : QState → Prop} {xs : List Stmt}

theorem ldw {d b : Reg64} {j k : Nat} {v : UInt64} (hr : s.reg b = wd w j)
    (hv : s.mem (wd w (j + k)) = some v) (h : WP (blk xs) (s.setReg d v) P E) :
    WP (blk (I (.load d (at_ b (wdisp k))) :: xs)) s P E :=
  wp_load (eval_wd hr k) hv h

theorem stw {r b : Reg64} {j k : Nat} (hr : s.reg b = wd w j) (hd : (s.mem (wd w (j + k))).isSome)
    (h : WP (blk xs) (s.setMem (wd w (j + k)) (s.reg r)) P E) :
    WP (blk (I (.store (at_ b (wdisp k)) r) :: xs)) s P E :=
  wp_store (eval_wd hr k) hd h

theorem stiw {b : Reg64} {j k : Nat} {n : Int64} (hr : s.reg b = wd w j)
    (hd : (s.mem (wd w (j + k))).isSome)
    (h : WP (blk xs) (s.setMem (wd w (j + k)) n.toUInt64) P E) :
    WP (blk (I (.storei (at_ b (wdisp k)) n) :: xs)) s P E :=
  wp_storei (eval_wd hr k) hd h

theorem ldx {d b : Reg64} {j i k : Nat} {v : UInt64} (hr : s.reg b = wd w j)
    (hi : s.reg .rax = i.toUInt64) (hv : s.mem (wd w (j + i + k)) = some v)
    (h : WP (blk xs) (s.setReg d v) P E) : WP (blk (I (.load d (aix b k)) :: xs)) s P E :=
  wp_load (eval_idx64 hr hi k) hv h

theorem lea_wd {d b : Reg64} {j k : Nat} (hr : s.reg b = wd w j)
    (h : WP (blk xs) (s.setReg d (wd w (j + k))) P E) :
    WP (blk (I (.lea d (at_ b (wdisp k))) :: xs)) s P E :=
  wp_reg (by rw [QInstr.step, eval_wd hr k]) h

theorem wd_add40 (j : Nat) : wd w j + 40 = wd w (j + 5) := wd_add w j 5

theorem wd_add16 (j : Nat) : wd w j + 16 = wd w (j + 2) := wd_add w j 2

theorem wd_add8 (j : Nat) : wd w j + 8 = wd w (j + 1) := wd_add w j 1

/-- `40 n` as a word, from the shifts the code uses. -/
theorem times40 (n : Nat) :
    n.toUInt64 <<< 5 + n.toUInt64 <<< 3 = (8 * (5 * n)).toUInt64 := by
  show n.toUInt64 <<< (5 : Nat).toUInt64 + n.toUInt64 <<< (3 : Nat).toUInt64 = _
  rw [toUInt64_shl n 5 (by omega), toUInt64_shl n 3 (by omega), toUInt64_add]
  congr 1
  simp only [Nat.reducePow]
  omega

/-- `8 n` as a word. -/
theorem times8 (n : Nat) : n.toUInt64 <<< 3 = (8 * n).toUInt64 := by
  show n.toUInt64 <<< (3 : Nat).toUInt64 = _
  rw [toUInt64_shl n 3 (by omega)]
  rfl

theorem wd_eq_add (j n : Nat) : wd w j + (8 * n).toUInt64 = wd w (j + n) := wd_add w j n

/-- The distance between two words of the working area, in bytes. -/
theorem wd_sub_toNat {a b : Nat} (h : a ≤ b) (hb : b < 2 ^ 61) :
    (wd w b - wd w a).toNat = 8 * (b - a) := by
  unfold wd
  rw [add_sub_add_left_eq_sub, UInt64.toNat_sub_of_le _ _ ((toUInt64_le (by omega) (by omega)).mpr
    (by omega)), toNat_toUInt64 (by omega), toNat_toUInt64 (by omega)]
  omega

/-- Steps at a word of the working area, the area's address in a register. -/
theorem ldw0 {d b : Reg64} {k : Nat} {v : UInt64} (hr : s.reg b = w)
    (hv : s.mem (wd w k) = some v) (h : WP (blk xs) (s.setReg d v) P E) :
    WP (blk (I (.load d (at_ b (wdisp k))) :: xs)) s P E :=
  ldw (j := 0) (by rw [hr, wd_zero]) (by rw [Nat.zero_add]; exact hv) h

theorem stw0 {r b : Reg64} {k : Nat} (hr : s.reg b = w) (hd : (s.mem (wd w k)).isSome)
    (h : WP (blk xs) (s.setMem (wd w k) (s.reg r)) P E) :
    WP (blk (I (.store (at_ b (wdisp k)) r) :: xs)) s P E :=
  stw (j := 0) (by rw [hr, wd_zero]) (by rw [Nat.zero_add]; exact hd) (by rw [Nat.zero_add]; exact h)

theorem stiw0 {b : Reg64} {k : Nat} {n : Int64} (hr : s.reg b = w) (hd : (s.mem (wd w k)).isSome)
    (h : WP (blk xs) (s.setMem (wd w k) n.toUInt64) P E) :
    WP (blk (I (.storei (at_ b (wdisp k)) n) :: xs)) s P E :=
  stiw (j := 0) (by rw [hr, wd_zero]) (by rw [Nat.zero_add]; exact hd) (by rw [Nat.zero_add]; exact h)

theorem lea0 {d b : Reg64} {k : Nat} (hr : s.reg b = w) (h : WP (blk xs) (s.setReg d (wd w k)) P E) :
    WP (blk (I (.lea d (at_ b (wdisp k))) :: xs)) s P E :=
  lea_wd (j := 0) (by rw [hr, wd_zero]) (by rw [Nat.zero_add]; exact h)

/-- `wk`: `r11 :=` the working area. -/
theorem wk_wp {ctx : UInt64} (hrdi : s.reg .rdi = ctx) (hwp : s.mem (wd ctx ctxWork) = some w)
    (h : WP (blk xs) (s.setReg .r11 w) P E) : WP (blk (wk :: xs)) s P E :=
  wp_load (eval_cw hrdi ctxWork) hwp h

/-! ## The data in words -/

/-- An entry from word `q`: degree, two columns, slot, coefficient. -/
def EntAt (mem : UInt64 → Option UInt64) (w : UInt64) (q : Nat) (e : DEnt) : Prop :=
  mem (wd w q) = some e.2.1.length.toUInt64 ∧ mem (wd w (q + 1)) = some (e.2.1.getD 0 0).toUInt64 ∧
    mem (wd w (q + 2)) = some (e.2.1.getD 1 0).toUInt64 ∧ mem (wd w (q + 3)) = some e.1.toUInt64 ∧
    mem (wd w (q + 4)) = some e.2.2.toUInt64

/-- A block from word `q`: the owner's form's word, the entry count, the entries. -/
def BlkAt (mem : UInt64 → Option UInt64) (w : UInt64) (q side : Nat) (b : DBlk) : Prop :=
  mem (wd w q) = some (busR.off + formOff b.1 side).toUInt64 ∧
    mem (wd w (q + 1)) = some b.2.length.toUInt64 ∧
    ∀ j (h : j < b.2.length), EntAt mem w (q + 2 + 5 * j) b.2[j]

/-- The blocks from word `q`. -/
def DataAt (mem : UInt64 → Option UInt64) (w : UInt64) (side : Nat) : Nat → List DBlk → Prop
  | _, [] => True
  | q, b :: bs => BlkAt mem w q side b ∧ DataAt mem w side (q + (encBlk side b).length) bs

theorem encEnts_length (es : List DEnt) : (es.flatMap encEnt).length = 5 * es.length := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [List.flatMap_cons, encEnt, ih]; omega

theorem encBlk_length (side : Nat) (b : DBlk) : (encBlk side b).length = 2 + 5 * b.2.length := by
  rw [encBlk, List.length_cons, List.length_cons, encEnts_length]; omega

theorem encode_take_succ (side : Nat) (D : List DBlk) {i : Nat} (hi : i < D.length) :
    (encode side (D.take (i + 1))).length =
      (encode side (D.take i)).length + (encBlk side D[i]).length := by
  unfold encode
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, List.flatMap_append,
    List.length_append, List.flatMap_singleton]

/-- A monomial's key from an entry's words. -/
theorem EntAt.key {q : Nat} {e : DEnt} (h : EntAt mem w q e) (h2 : e.2.1.length ≤ 2)
    (hb : ∀ a ∈ e.2.1, a < 2 ^ 64) : KeyAt mem w q e.2.1.toArray := by
  refine ⟨by simpa using h2, fun i hi ↦ hb _ (by simp), by simpa using h.1, ?_, ?_⟩
  · rw [h.2.1]; congr 2; simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
  · rw [h.2.2.1]; congr 2; simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

end NativeVm.Code.P3
