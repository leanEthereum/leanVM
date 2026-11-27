module

public import LeanVM.Guest.CoreMode.FrameSem
public import LeanVM.Guest.Mode.SoundStep
public import LeanVM.Prover.ExecuteComplete

/-!
# One instruction of the frame walk

A non-`JUMP` the frame walk accepts (`stepF_val`, `stepF_wr`, `stepF_reads`, `stepF_deref`), at a state where the path's state holds and
whose instruction holds of the reference image (the reference executes it there), reads written
cells (`Mode.Reads`: a back-solve's divisor nonzero by `divOk_sound`); after it the new state's
value facts hold of the image (`Exec`'s step by `Exec.nonJump_holds`) and, after the executor's
step, its written facts of the executor's memory. A `DEREF` at an offset of the oracle needs its
heap cell written (`HeapRd`).
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest
open LeanVM.Prover.Exec (Mem maxCells gpow_inj Mem.le_trans Mem.get_of_written Fine refMem refRd_img runOp
  Agree)
open LeanVM.Guest.Mode (Names written_of_get written_mono names_inj Reads ZNz opOfOff)

@[expose] public section

variable {κ : ℕ} {img : MemoryImage κ}

/-! ## Words of the reference -/

theorem symNz_val {o : Option Exec.Sym} (h : FSt.symNz o = true) (fp : K) (hfp : fp ≠ 0) :
    ∃ v, o = some v ∧ v.val fp ≠ 0 := by
  rcases o with _ | (_ | e | e) <;> simp [FSt.symNz] at h
  · exact ⟨_, rfl, fun h0 ↦ gpow_ne_zero e (ofK_injective (by rw [LeanVM.Parameters.ofK_zero]; exact h0))⟩
  · refine ⟨_, rfl, fun h0 ↦ ?_⟩
    have := ofK_injective (show ofK (fp * addressOfIndex e) = ofK 0 by rw [LeanVM.Parameters.ofK_zero]; exact h0)
    exact mul_ne_zero hfp (gpow_ne_zero e) this

theorem gpow_ne_zero' (n : ℕ) : (g : K) ^ n ≠ 0 := pow_ne_zero _ g_ne_zero

/-- A cell the state knows nonzero is, in the reference. -/
theorem nzOf_sound {fp : ℕ} {A : FSt} (hv : FVal img fp A) {o : ℕ} (h : A.nzOf o = true) :
    ∃ v, Rd img fp o = some v ∧ v ≠ 0 := by
  unfold FSt.nzOf at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · exact hv.nz o h
  · obtain ⟨v, hv', hne⟩ := symNz_val h _ (gpow_ne_zero' fp)
    exact ⟨_, hv.st.1 o v hv', hne⟩

/-- `[b] = 0` makes `[x] = 0`, in the reference. -/
theorem zImp_sound {fp : ℕ} {A : FSt} (hv : FVal img fp A) {b x : ℕ} (h : A.zImp b x = true)
    {vb vx : E} (hb : Rd img fp b = some vb) (hx : Rd img fp x = some vx) (h0 : vb = 0) : vx = 0 := by
  unfold FSt.zImp at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · obtain rfl := beq_iff_eq.mp h
    rw [hx] at hb; cases hb; exact h0
  · rcases hprev : A.st.prev with _ | ⟨⟨pc, ins⟩, rest⟩
    · rw [hprev] at h; cases h
    · rw [hprev] at h
      cases ins with
      | mul p q r =>
        simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
        obtain ⟨hrb, hpq⟩ := h
        have hh := hv.st.2.2 _ (by rw [hprev]; exact List.mem_cons_self ..)
        obtain ⟨vP, vQ, hP, hQ, hR⟩ := hh
        rw [hrb] at hR
        have hR' : Rd img fp b = some (vP * vQ) := hR
        rw [hb] at hR'; cases hR'
        rcases hpq with ⟨hpx, hq⟩ | ⟨hqx, hp⟩
        · rw [hpx] at hP
          have hP' : Rd img fp x = some vP := hP
          rw [hx] at hP'; cases hP'
          obtain ⟨u, hu, hne⟩ := nzOf_sound hv hq
          have hQ' : Rd img fp q = some vQ := hQ
          rw [hu] at hQ'; cases hQ'
          exact (mul_eq_zero.mp h0).resolve_right hne
        · rw [hqx] at hQ
          have hQ' : Rd img fp x = some vQ := hQ
          rw [hx] at hQ'; cases hQ'
          obtain ⟨u, hu, hne⟩ := nzOf_sound hv hp
          have hP' : Rd img fp p = some vP := hP
          rw [hu] at hP'; cases hP'
          exact (mul_eq_zero.mp h0).resolve_left hne
      | _ => cases h

/-- **A back-solve's divisor** the state accepts is nonzero in the reference, where its product
with the other operand is `[c]`. -/
theorem divOk_sound {fp : ℕ} {A : FSt} (hv : FVal img fp A) {b c : ℕ} (h : A.divOk b c = true)
    {vb vc : E} (hb : Rd img fp b = some vb) (hc : Rd img fp c = some vc) (hp : vb = 0 → vc = 0) :
    vb ≠ 0 := by
  intro h0
  unfold FSt.divOk at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · rcases Bool.or_eq_true_iff.mp h with h | h
    · obtain ⟨u, hu, hne⟩ := nzOf_sound hv h
      rw [hb] at hu; cases hu; exact hne h0
    · obtain ⟨u, hu, hne⟩ := nzOf_sound hv h
      rw [hc] at hu; cases hu; exact hne (hp h0)
  · rcases hx : A.one.get c with _ | x
    · rw [hx] at h; cases h
    · rw [hx] at h
      obtain ⟨u, hu, hcu⟩ := hv.one c x hx
      have := zImp_sound hv h hb hu h0
      rw [hc, this, add_zero] at hcu
      cases hcu
      exact one_ne_zero (hp h0)

/-- The executor's word at a written frame cell is the reference's. -/
theorem rd_get (hκ : κ ≤ 28) {s : Prover.Exec.St} (hs : Fine (refMem img) s) {o : ℕ} (ho : o < 2 ^ 28)
    {u v : E} (hr : Rd img s.fp o = some v) (hg : s.mem.get (s.fp + o) = some u) : u = v := by
  have h1 := hs.agree.get _ _ hg
  have hfp := hs.fp
  unfold maxCells at hfp
  have h2 := (refRd_img hκ img (s.fp + o) v (by omega) (by rw [pow_add]; exact hr)).2
  rw [← h1, h2]

/-- A pointer the reference dereferences is nonzero. -/
theorem deref_ptr_nz {fp : K} {o1 o2 o3 pc : ℕ} {mode : DerefMode}
    (hh : Guest.Holds img pc fp (.deref o1 o2 o3 mode)) :
    ∃ v, img.read (fp * addressOfIndex o1) = some v ∧ v ≠ 0 := by
  obtain ⟨p, v3, hp, -, -, hr⟩ := hh
  refine ⟨p, hp, fun h0 ↦ ?_⟩
  rw [h0, limb_zero, zero_mul, MemoryImage.read_zero] at hr
  cases hr

/-! ## What the oracle says -/

/-- What an offset of the oracle needs: a `DEREF`'s heap cell written. -/
def HeapRd (s : Prover.Exec.St) : OffsetInstruction → Prop
  | .deref a o _ .cell => ∀ p x, s.mem.get (s.fp + a) = some p → Names (p * ofK (g ^ o)) x →
      s.mem.written x = true
  | _ => True


/-! ## Value facts after an instruction -/

theorem stepF_deref {O : ℕ} {S : Exec.Trie Unit} {i : ℕ} {A A' : FSt} {a o c : ℕ} {mode : DerefMode}
    (h : stepF O S i A (.deref a o c mode) = some A') :
    A.hasW a = true ∧ (has S i = true → A.hasW c = true) ∧ A' = derefF O i A a o c mode := by
  replace h : (if (A.hasW a && (!has S i || A.hasW c)) = true then some (derefF O i A a o c mode)
    else none) = some A' := h
  split_ifs at h with hw
  simp only [Bool.and_eq_true] at hw
  obtain ⟨hw1, hw2⟩ := hw
  refine ⟨hw1, fun hs ↦ ?_, (Option.some.inj h).symm⟩
  rw [hs] at hw2
  simpa using hw2

/-- A copy into frame cell `t` of `c`'s word. -/
theorem FVal.setCp {fp : ℕ} {B : FSt} (hB : FVal img fp B) {t c : ℕ}
    (h : ∃ v, Rd img fp t = some v ∧ Rd img fp c = some v) :
    FVal img fp { B with cp := B.cp.set c Exec.envDepth t } := by
  refine ⟨hB.st, hB.nz, hB.hs, fun t' c' ht ↦ ?_, hB.one⟩
  replace ht : (B.cp.set c Exec.envDepth t).get t' = some c' := ht
  rcases Exec.Trie.get_set ht with ⟨rfl, rfl⟩ | ht
  · exact h
  · exact hB.cp t' c' ht

/-- A `DEREF` of mode `cell` through a next frame's pointer: the own cell it names holds `[c]`. -/
theorem fval_nextF {fp pc : ℕ} {A B : FSt} {a o c : ℕ} (hv : FVal img fp A) (hB : FVal img fp B)
    (hh : Guest.Holds img pc (g ^ fp) (.deref a o c .cell)) : FVal img fp (nextF A B a o c) := by
  unfold nextF
  rcases he : A.st.env.get a with _ | (_ | _ | e)
  · exact hB
  · exact hB
  · exact hB
  obtain ⟨p, v3, hp, -, hv3, hr⟩ := hh
  have hpe := hv.st.1 a _ he
  rw [hp] at hpe
  cases hpe
  have hcp : ∃ v, Rd img fp (e + o) = some v ∧ Rd img fp c = some v := by
    refine ⟨v3, ?_, hv3⟩
    have hr' : img.read ((Exec.Sym.val (g ^ fp) (.fpg e)).limb 0 * addressOfIndex o) = some v3 := hr
    show img.read (g ^ fp * addressOfIndex (e + o)) = some v3
    rw [show g ^ fp * addressOfIndex (e + o) = (Exec.Sym.val (g ^ fp) (.fpg e)).limb 0 * addressOfIndex o by
      rw [show (Exec.Sym.val (g ^ fp) (.fpg e)).limb 0 = g ^ fp * addressOfIndex e by simp [Exec.Sym.val]]
      simp only [addressOfIndex, pow_add, mul_assoc]]
    exact hr'
  dsimp only
  split_ifs
  · exact (hB.addW _).setCp hcp
  · exact hB.setCp hcp
  · exact hB

theorem names_gpow {p : E} {o x n : ℕ} (hn : p.limb 0 = g ^ n) (hx : Names (p * ofK (g ^ o)) x)
    (hb : n + o < 2 ^ 63) : x = n + o := by
  have h1 := hx.1
  rw [Mode.limb_mul_ofK, hn, ← pow_add] at h1
  have := hx.2
  unfold maxCells at this
  exact gpow_inj (by omega) hb h1.symm

/-- The written cells after `nextF`: the own cell `e + o` is the heap cell, written once `c` is. -/
theorem fwr_nextF {s : Prover.Exec.St} {A B : FSt} {a o c : ℕ} (hB : FWr s B)
    (hx : ∀ e, A.st.env.get a = some (.fpg e) → e + o < pcLim → B.hasW c = true →
      s.mem.written (s.fp + (e + o)) = true) : FWr s (nextF A B a o c) := by
  unfold nextF
  rcases he : A.st.env.get a with _ | (_ | _ | e)
  · exact hB
  · exact hB
  · exact hB
  dsimp only
  split_ifs with hl hc
  · exact ⟨(hB.addW (hx e he hl hc)).w, hB.hq⟩
  · exact ⟨hB.w, hB.hq⟩
  · exact hB

theorem isOne_eq' {o : Option Exec.Sym} (h : Exec.isOne o = true) : o = some (.gp 0) := by
  rcases o with _ | (_ | (_ | _) | _) <;> simp_all [Exec.isOne]

theorem fval_one {fp : ℕ} {A : FSt} (hv : FVal img fp A) {a b c pc : ℕ}
    (hh : Guest.Holds img pc (g ^ fp) (.xor a b c)) : FVal img fp { A.addW c with one := oneOf A a b c } := by
  refine ⟨hv.st, hv.nz, hv.hs, hv.cp, fun c' x hx ↦ ?_⟩
  obtain ⟨vA, vB, hA, hB, hC⟩ := hh
  replace hA : Rd img fp a = some vA := hA
  replace hB : Rd img fp b = some vB := hB
  replace hC : Rd img fp c = some (vA + vB) := hC
  replace hx : (oneOf A a b c).get c' = some x := hx
  by_cases ha : Exec.isOne (A.st.env.get a) = true
  · have he : oneOf A a b c = A.one.set b Exec.envDepth c := by unfold oneOf; simp [ha]
    rw [he] at hx
    rcases Exec.Trie.get_set hx with ⟨rfl, rfl⟩ | hx
    · have h1 := hv.st.1 a _ (isOne_eq' ha)
      replace h1 : Rd img fp a = some _ := h1
      rw [hA] at h1; cases h1
      simp only [Exec.Sym.val, addressOfIndex, pow_zero, LeanVM.Parameters.ofK_one] at hC
      exact ⟨vB, hB, hC⟩
    · exact hv.one c' x hx
  by_cases hb : Exec.isOne (A.st.env.get b) = true
  · have he : oneOf A a b c = A.one.set a Exec.envDepth c := by unfold oneOf; simp [ha, hb]
    rw [he] at hx
    rcases Exec.Trie.get_set hx with ⟨rfl, rfl⟩ | hx
    · have h1 := hv.st.1 b _ (isOne_eq' hb)
      replace h1 : Rd img fp b = some _ := h1
      rw [hB] at h1; cases h1
      simp only [Exec.Sym.val, addressOfIndex, pow_zero, LeanVM.Parameters.ofK_one] at hC
      exact ⟨vA, hA, by rw [hC, add_comm]⟩
    · exact hv.one c' x hx
  · have he : oneOf A a b c = A.one := by unfold oneOf; simp [ha, hb]
    rw [he] at hx
    exact hv.one c' x hx

theorem has_keccakMask {m0 m1 m2 m3 tail b8 cap j : ℕ} (hj : j ∈ keccakIns m0 m1 m2 m3 tail b8 cap) :
    Bits.has (keccakMask m0 m1 m2 m3 tail b8 cap) j = true := by
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hj
  have hc : c < 13 := List.mem_range.mp hc
  have h15 : ∀ k < 4, Nat.testBit 15 k = true := by decide
  interval_cases c <;>
    simp [keccakInOff, keccakMask, Bits.has, Nat.testBit_or, Nat.testBit_two_pow, Nat.testBit_shiftLeft, h15]

/-- **The value facts after a non-`JUMP`** the frame rule accepts, the instruction holding of the
reference. -/
theorem stepF_val {O : ℕ} {S : Exec.Trie Unit} {i pc fp : ℕ} {A A' : FSt} {ins : OffsetInstruction}
    (hv : FVal img fp A) (hh : Guest.Holds img pc (g ^ fp) ins) (h : stepF O S i A ins = some A') :
    FVal img fp A' := by
  cases ins with
  | xor a b c =>
    simp only [stepF] at h
    split_ifs at h
    cases h
    exact fval_one hv hh
  | mul a b c =>
    obtain ⟨vA, vB, hA, hB, hC⟩ := hh
    replace hA : Rd img fp a = some vA := hA
    replace hB : Rd img fp b = some vB := hB
    replace hC : Rd img fp c = some (vA * vB) := hC
    simp only [stepF] at h
    split_ifs at h with h1 h2 h3 h4
    · cases h
      simp only [Bool.and_eq_true] at h2
      obtain ⟨ua, hua, hna⟩ := nzOf_sound hv h2.1
      obtain ⟨ub, hub, hnb⟩ := nzOf_sound hv h2.2
      rw [hA] at hua; cases hua
      rw [hB] at hub; cases hub
      exact (hv.addW c).addNz ⟨_, hC, mul_ne_zero hna hnb⟩
    · cases h; exact hv.addW c
    · cases h
      simp only [Bool.and_eq_true] at h3
      exact (hv.addW b).addNz ⟨vA, hA, divOk_sound hv h3.2 hA hC fun h0 ↦ by rw [h0, zero_mul]⟩
    · cases h
      simp only [Bool.and_eq_true] at h4
      exact (hv.addW a).addNz ⟨vB, hB, divOk_sound hv h4.2 hB hC fun h0 ↦ by rw [h0, mul_zero]⟩
  | set o k0 k1 =>
    simp only [stepF] at h
    cases h
    split_ifs with hi
    · exact (hv.addW o).addNz ⟨_, hh, Mode.immNz_ne hi⟩
    · exact hv.addW o
  | deref a o c mode =>
    have hnz := deref_ptr_nz hh
    obtain ⟨-, -, rfl⟩ := stepF_deref h
    have hB : FVal img fp (cellF O i A a o c) := by
      unfold cellF
      split_ifs
      · exact (hv.addNz hnz).addQ a o
      · exact (hv.addNz hnz).addW c
      · exact ((hv.addNz hnz).addW c).addQ a o
      · exact hv.addNz hnz
    cases mode with
    | cell =>
      refine fval_nextF hv ?_ hh
      split_ifs with hca
      · have hca' : c = a := beq_iff_eq.mp hca
        refine hB.addS fun _ ↦ ?_
        obtain ⟨p, v3, hp, hpK, hv3, hr⟩ := hh
        rw [hca', hp] at hv3; cases hv3
        exact ⟨p, hp, hpK, hr⟩
      · exact hB
    | pc => exact (hv.addNz hnz).addQ a o
    | fp => exact (hv.addNz hnz).addQ a o
  | keccak m0 m1 m2 m3 tail b8 cap out inOdd outOdd outCells =>
    simp only [stepF] at h
    split_ifs at h
    cases h
    exact ⟨hv.st, hv.nz, hv.hs, hv.cp, hv.one⟩
  | jump => simp [stepF] at h

theorem fval_addCopies {fp : ℕ} : ∀ {A : FSt} {fs : List Exec.Atom}, FVal img fp A →
    (∀ x ∈ fs, x.Holds img (g ^ fp)) → FVal img fp (addCopies A fs)
  | _, [], hv, _ => hv
  | A, x :: fs, hv, hf => by
    have hf' : ∀ y ∈ fs, y.Holds img (g ^ fp) := fun y hy ↦ hf y (List.mem_cons_of_mem _ hy)
    cases x with
    | copy d src =>
      show FVal img fp (addCopies { A with cp := A.cp.set src Exec.envDepth d } fs)
      refine fval_addCopies ⟨hv.st, hv.nz, hv.hs, fun t c ht ↦ ?_, hv.one⟩ hf'
      replace ht : (A.cp.set src Exec.envDepth d).get t = some c := ht
      rcases Exec.Trie.get_set ht with ⟨rfl, rfl⟩ | ht
      · obtain ⟨v, h1, h2⟩ := hf _ List.mem_cons_self
        exact ⟨v, h2, h1⟩
      · exact hv.cp t c ht
    | instr | jump | eq | nz | ne | bool | range | powPair =>
      show FVal img fp (addCopies A fs)
      exact fval_addCopies hv hf'

/-- **`Exec`'s step** keeps the value facts, the instruction holding of the reference. -/
theorem execF_val (hκ : κ ≤ 32) {F : Exec.Facts} (hp : F.pows.Ok) {fp pc : ℕ} {A : FSt}
    {ins : OffsetInstruction} (hv : FVal img fp A) (hh : Guest.Holds img pc (g ^ fp) ins) :
    FVal img fp (execF F pc A ins) := by
  unfold execF
  obtain ⟨hfs, he, hm⟩ := Exec.nonJump_holds hκ hp hv.st hh
  exact fval_addCopies ⟨hv.st.push he hm hh, hv.nz, hv.hs, hv.cp, hv.one⟩ hfs

theorem addCopies_w : ∀ (A : FSt) (fs : List Exec.Atom), (addCopies A fs).w = A.w ∧ (addCopies A fs).hq = A.hq
  | _, [] => ⟨rfl, rfl⟩
  | A, x :: fs => by
    cases x with
    | copy d src => exact addCopies_w { A with cp := A.cp.set src Exec.envDepth d } fs
    | instr | jump | eq | nz | ne | bool | range | powPair =>
      show (addCopies A fs).w = A.w ∧ (addCopies A fs).hq = A.hq
      exact addCopies_w A fs

theorem execF_wr {F : Exec.Facts} {pc : ℕ} {s : Prover.Exec.St} {A : FSt} {ins : OffsetInstruction}
    (h : FWr s A) : FWr s (execF F pc A ins) := by
  unfold execF
  split
  rename_i fs env mem _
  obtain ⟨h1, h2⟩ := addCopies_w { A with st := A.st.push env mem pc ins } fs
  exact ⟨fun o ho ↦ h.w o (by rw [h1] at ho; exact ho), fun q o hl ho ↦ h.hq q o hl (by rw [h2] at ho; exact ho)⟩

/-! ## Written cells after an instruction -/

theorem fwr_addRun {s : Prover.Exec.St} {A : FSt} (hw : FWr s A) {out n : ℕ}
    (hn : ∀ j < n, s.mem.written (s.fp + (out + j)) = true) : FWr s { A with w := Bits.addRun A.w out n } where
  w o ho := (Bits.has_addRun ho).elim (hw.w o) fun ⟨h1, h2, _⟩ ↦
    Nat.add_sub_cancel' h1 ▸ hn (o - out) (by omega)
  hq := hw.hq

/-- **The written cells after a non-`JUMP`** the frame rule accepts. -/
theorem stepF_wr {C : Prover.Exec.Ctx} {O : ℕ} {S : Exec.Trie Unit} {i : ℕ} {s s' : Prover.Exec.St} {A A' : FSt}
    {ins : OffsetInstruction} (hs : s.Good) (hfp : s.fp < maxCells) (hpc : s.pc < C.ops.size)
    (hw : FWr s A) (hO : Bits.has O i = true → HeapRd s ins) (h : stepF O S i A ins = some A')
    (hfpg : ∀ a o c mode e p, ins = .deref a o c mode → A.st.env.get a = some (.fpg e) →
      s.mem.get (s.fp + a) = some p → p.limb 0 = g ^ (s.fp + e))
    (e : runOp C s (opOfOff ins) = .ok s') :
    FWr s' A' ∧ s'.fp = s.fp ∧ s'.pc = s.pc + 1 ∧ s.mem ≤ s'.mem := by
  cases ins with
  | jump => simp [stepF] at h
  | keccak m0 m1 m2 m3 tail b8 cap out inOdd outOdd outCells =>
    simp only [stepF] at h
    split_ifs at h
    cases h
    obtain ⟨hle, hf, hp, hk⟩ := Mode.keccak_writes hs e
    refine ⟨fwr_addRun (hw.mono hle hf) fun j hj ↦ ?_, hf, hp, hle⟩
    rw [hf]; exact hk j hj
  | xor a b c =>
    obtain ⟨h1, h2, h3⟩ := Mode.runOp_next hs hfp hpc e (fun _ _ _ ↦ nofun) (fun _ _ _ _ _ ↦ nofun)
    simp only [stepF] at h
    split_ifs at h
    cases h
    have hc := Mode.runOp_writes (k := 0) hs (Or.inl rfl) e
    exact ⟨⟨((hw.mono h3 h2).addW (by rw [h2]; exact hc)).w, (hw.mono h3 h2).hq⟩, h2, h1, h3⟩
  | mul a b c =>
    obtain ⟨h1, h2, h3⟩ := Mode.runOp_next hs hfp hpc e (fun _ _ _ ↦ nofun) (fun _ _ _ _ _ ↦ nofun)
    obtain ⟨va, vb, ha, hb, hc⟩ := Mode.mul_vals hs e
    rw [← h2] at ha hb hc
    have hm := hw.mono h3 h2
    refine ⟨?_, h2, h1, h3⟩
    simp only [stepF] at h
    split_ifs at h
    · cases h; exact (hm.addW (written_of_get hc)).addNz c
    · cases h; exact hm.addW (written_of_get hc)
    · cases h; exact (hm.addW (written_of_get hb)).addNz a
    · cases h; exact (hm.addW (written_of_get ha)).addNz b
  | set o k0 k1 =>
    obtain ⟨h1, h2, h3⟩ := Mode.runOp_next hs hfp hpc e (fun _ _ _ ↦ nofun) (fun _ _ _ _ _ ↦ nofun)
    have hv := Mode.set_vals hs e
    rw [← h2] at hv
    have hm := (hw.mono h3 h2).addW (written_of_get hv)
    refine ⟨?_, h2, h1, h3⟩
    simp only [stepF] at h
    cases h
    split_ifs
    · exact hm.addNz o
    · exact hm
  | deref a o c mode =>
    obtain ⟨h1, h2, h3⟩ := Mode.runOp_next hs hfp hpc e (fun _ _ _ ↦ nofun) (fun _ _ _ _ _ ↦ nofun)
    obtain ⟨p, x, hp, -, hx, hpcm, hfpm, hcell⟩ := Mode.deref_vals hs e
    have hm := hw.mono h3 h2
    have hp' : s'.mem.get (s'.fp + a) = some p := by rw [h2]; exact h3.get _ _ hp
    refine ⟨?_, h2, h1, h3⟩
    obtain ⟨-, -, rfl⟩ := stepF_deref h
    cases mode with
    | pc => exact (hm.addNz a).addQ fun _ ↦ ⟨p, x, hp', hx, written_of_get (hpcm rfl)⟩
    | fp => exact (hm.addNz a).addQ fun _ ↦ ⟨p, x, hp', hx, written_of_get (hfpm rfl)⟩
    | cell =>
      obtain ⟨hld, hst⟩ := hcell rfl
      have hB : FWr s' (cellF O i A a o c) ∧ ((cellF O i A a o c).hasW c = true → s'.mem.written x = true) := by
        unfold cellF
        split_ifs with hc hq ho
        · obtain ⟨v, hv⟩ := Mem.get_of_written (hw.w c hc)
          exact ⟨(hm.addNz a).addQ fun _ ↦ ⟨p, x, hp', hx, written_of_get (hst v hv)⟩,
            fun _ ↦ written_of_get (hst v hv)⟩
        · unfold FSt.hasQ at hq
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hq
          obtain ⟨p', x', hp1, hx1, hw1⟩ := hw.hq a o hq.1 (has_iff.mp hq.2)
          rw [hp] at hp1; cases hp1
          obtain rfl := names_inj hx hx1
          obtain ⟨v, hv⟩ := Mem.get_of_written hw1
          exact ⟨(hm.addNz a).addW (by rw [h2]; exact written_of_get (hld v hv)), fun _ ↦ written_mono h3 hw1⟩
        · have hxw := hO ho p x hp hx
          obtain ⟨v, hv⟩ := Mem.get_of_written hxw
          exact ⟨((hm.addNz a).addW (by rw [h2]; exact written_of_get (hld v hv))).addQ
            fun _ ↦ ⟨p, x, hp', hx, written_mono h3 hxw⟩, fun _ ↦ written_mono h3 hxw⟩
        · exact ⟨hm.addNz a, fun h' ↦ absurd h' hc⟩
      have hB' : FWr s' (if c == a then (cellF O i A a o c).addS a o else cellF O i A a o c) ∧
          ((if c == a then (cellF O i A a o c).addS a o else cellF O i A a o c).hasW c = true →
            s'.mem.written x = true) := by
        split_ifs
        · refine ⟨hB.1.addS a o, fun h' ↦ hB.2 ?_⟩
          unfold FSt.addS at h'
          split_ifs at h' <;> exact h'
        · exact hB
      refine fwr_nextF hB'.1 fun e' he hl hc ↦ ?_
      have hn := names_gpow (hfpg a o c .cell e' p rfl he hp) hx (by unfold pcLim at hl; unfold maxCells at hfp; omega)
      rw [h2, ← Nat.add_assoc, ← hn]
      exact hB'.2 hc

/-- **What a non-`JUMP` the frame rule accepts reads is written**, a back-solve's divisor nonzero. -/
theorem stepF_reads (hκ : κ ≤ 28) {O : ℕ} {S : Exec.Trie Unit} {i pc : ℕ} {s : Prover.Exec.St} {A A' : FSt}
    {ins : OffsetInstruction} (hs : Fine (refMem img) s) (hA : FHolds img s A)
    (hh : Guest.Holds img pc (g ^ s.fp) ins)
    (hsm : ∀ a b c, ins = .mul a b c → a < 2 ^ 28 ∧ b < 2 ^ 28 ∧ c < 2 ^ 28)
    (h : stepF O S i A ins = some A') : Reads s (opOfOff ins) := by
  have hW : ∀ o, A.hasW o = true → s.mem.written (s.fp + o) = true := fun o ho ↦ hA.2.w o ho
  cases ins with
  | jump => simp [stepF] at h
  | set => trivial
  | xor a b c =>
    simp only [stepF] at h
    split_ifs at h with hc
    simp only [Bool.and_eq_true] at hc
    exact ⟨hW a hc.1, hW b hc.2⟩
  | deref a o c mode => exact hW a (stepF_deref h).1
  | keccak m0 m1 m2 m3 tail b8 cap out inOdd outOdd outCells =>
    simp only [stepF] at h
    split_ifs at h with hall
    intro j hj
    have hj' : j ∈ keccakIns m0 m1 m2 m3 tail b8 cap := by simpa using hj
    exact hW j (Bits.has_of_sub hall (has_keccakMask hj'))
  | mul a b c =>
    obtain ⟨sa, sb, sc⟩ := hsm a b c rfl
    obtain ⟨vA, vB, hA', hB', hC'⟩ := hh
    have hA'' : Rd img s.fp a = some vA := hA'
    have hB'' : Rd img s.fp b = some vB := hB'
    have hC'' : Rd img s.fp c = some (vA * vB) := hC'
    simp only [stepF] at h
    split_ifs at h with h1 h2 h3 h4
    · simp only [Bool.and_eq_true] at h1
      exact Or.inl ⟨hW a h1.1, hW b h1.2⟩
    · simp only [Bool.and_eq_true] at h1
      exact Or.inl ⟨hW a h1.1, hW b h1.2⟩
    · simp only [Bool.and_eq_true] at h3
      have hne := divOk_sound hA.1 h3.2 hA' hC' fun h0 ↦ by rw [h0, zero_mul]
      obtain ⟨u, hu⟩ := Mem.get_of_written (hW a h3.1.2)
      obtain ⟨v, hv⟩ := Mem.get_of_written (hW c h3.1.1)
      exact Or.inr (Or.inl ⟨hW c h3.1.1, hW a h3.1.2, u, v, hu, hv, fun hu0 ↦
        absurd (rd_get hκ hs sa hA' hu ▸ hu0) hne⟩)
    · simp only [Bool.and_eq_true] at h4
      have hne := divOk_sound hA.1 h4.2 hB' hC' fun h0 ↦ by rw [h0, mul_zero]
      obtain ⟨u, hu⟩ := Mem.get_of_written (hW b h4.1.2)
      obtain ⟨v, hv⟩ := Mem.get_of_written (hW c h4.1.1)
      exact Or.inr (Or.inr ⟨hW c h4.1.1, hW b h4.1.2, u, v, hu, hv, fun hu0 ↦
        absurd (rd_get hκ hs sb hB' hu ▸ hu0) hne⟩)

end

end LeanVM.Guest.CoreMode
