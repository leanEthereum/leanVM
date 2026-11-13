/-
  LeanVM.Guest.B1.Sig.KeccakMsg

  What the compiler's lowering of a Keccak message (`kMsg`) computes: its output's first cells
  are the Keccak-256 digest's halves of the message bytes.
-/

module

public import LeanVM.Guest.B1.Sig.Shapes
public import LeanVM.Guest.CoreLemmas
public import LeanVM.Guest.Value.Keccak

/-!
# The Keccak message, sound

`kMsg_sound_cells`: when the statements of `kMsg pad cells len tailRun out b n` hold, the padding
run holding `[0x01, 0, 0, 0, 0]` (`PadOK`), the output run's first cells, as many of the two as the
last block writes (`n`), are `digestHalves (keccak256 m)` for `m` the first `len` bytes of the
message cells' words (`KC.val`), provided the bytes past `len` are zero (`kMsg_sound`: the first,
`kMsg_sound2`: both). The proof reads off each block's `KECCAK` inputs: from the
zero state the message cells (`kCell_sound`, `kRun_sound`), after it the previous output XORed with
them (`kXor_sound`, `kTailXor_sound`), the padding bytes XORed in first (`kXorByte_sound`); and
applies `keccak_final_digest`.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.KeccakHash LeanVM.Guest LeanVM.Guest.Core
open LeanVM.Guest.Value.Keccak

@[expose] public section

/-- A message cell's word under a valuation. -/
def KC.val (σ : Val) : KC → E
  | .zero => 0
  | .const c => c
  | .cell v => σ v

/-- The padding run holds `[0x01, 0, 0, 0, 0]`. -/
def PadOK (σ : Val) (pad : Nat) : Prop :=
  σ (.n pad) = word 1 0 ∧ σ (.n (pad + 1)) = 0 ∧ σ (.n (pad + 2)) = 0 ∧ σ (.n (pad + 3)) = 0 ∧
    σ (.n (pad + 4)) = 0

/-! ## Blocks of atoms -/

/-- All statements are atoms. -/
def atomsOnly : List Stmt → Bool
  | [] => true
  | .atom _ :: ss => atomsOnly ss
  | _ :: _ => false

theorem noRetList_of_atomsOnly : ∀ {ss : List Stmt}, atomsOnly ss = true → Stmt.noRetList ss = true
  | [], _ => rfl
  | .atom _ :: ss, h => by
      simp only [atomsOnly] at h
      simp only [Stmt.noRetList, Stmt.noRet, noRetList_of_atomsOnly h, Bool.and_self]
  | .ite .. :: _, h | .match_ .. :: _, h | .call .. :: _, h | .callIf .. :: _, h
  | .dispatch .. :: _, h | .ret _ :: _, h => by simp [atomsOnly] at h

theorem atomsOnly_append : ∀ (xs ys : List Stmt), atomsOnly (xs ++ ys) = (atomsOnly xs && atomsOnly ys)
  | [], _ => by simp [atomsOnly]
  | .atom _ :: xs, ys => by simp only [List.cons_append, atomsOnly, atomsOnly_append xs ys]
  | .ite .. :: _, _ | .match_ .. :: _, _ | .call .. :: _, _ | .callIf .. :: _, _
  | .dispatch .. :: _, _ | .ret _ :: _, _ => by simp [atomsOnly]

variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

/-- A return-free block followed by another: both hold. -/
theorem holdsList_split {xs ys : List Stmt} (hx : Stmt.noRetList xs = true) {next : Prop}
    (h : Stmt.HoldsList C rd σ (xs ++ ys) next kret) :
    Stmt.HoldsList C rd σ xs True kret ∧ Stmt.HoldsList C rd σ ys next kret := by
  rw [holdsList_append] at h
  exact (holdsList_noRet xs hx _ kret).mp h

theorem holdsList_split_atoms {xs ys : List Stmt} (hx : atomsOnly xs = true) {next : Prop}
    (h : Stmt.HoldsList C rd σ (xs ++ ys) next kret) :
    Stmt.HoldsList C rd σ xs True kret ∧ Stmt.HoldsList C rd σ ys next kret :=
  holdsList_split (noRetList_of_atomsOnly hx) h

/-- Every atom of a block holds. -/
def AtomsHold (rd : Reader) (σ : Val) (ss : List Stmt) : Prop := ∀ a, Stmt.atom a ∈ ss → a.Holds rd σ

theorem atomsHold_of_holdsList : ∀ {ss : List Stmt} {next : Prop}, atomsOnly ss = true →
    Stmt.HoldsList C rd σ ss next kret → AtomsHold rd σ ss
  | [], _, _, _ => fun _ h => absurd h (by simp)
  | .atom a :: ss, next, hs, h => by
      simp only [atomsOnly] at hs
      intro b hb
      rcases List.mem_cons.mp hb with e | hb
      · cases e; exact h.1
      · exact atomsHold_of_holdsList hs h.2 b hb
  | .ite .. :: _, _, hs, _ | .match_ .. :: _, _, hs, _ | .call .. :: _, _, hs, _
  | .callIf .. :: _, _, hs, _ | .dispatch .. :: _, _, hs, _ | .ret _ :: _, _, hs, _ => by
      simp [atomsOnly] at hs

theorem AtomsHold.sub {ss ss' : List Stmt} (h : AtomsHold rd σ ss) (hs : ∀ x ∈ ss', x ∈ ss) :
    AtomsHold rd σ ss' := fun a ha => h a (hs _ ha)

theorem AtomsHold.left {xs ys : List Stmt} (h : AtomsHold rd σ (xs ++ ys)) : AtomsHold rd σ xs :=
  h.sub fun _ hx => List.mem_append_left _ hx

theorem AtomsHold.right {xs ys : List Stmt} (h : AtomsHold rd σ (xs ++ ys)) : AtomsHold rd σ ys :=
  h.sub fun _ hx => List.mem_append_right _ hx

theorem AtomsHold.atom {ss : List Stmt} {a : Atom} (h : AtomsHold rd σ ss) (ha : Stmt.atom a ∈ ss) :
    a.Holds rd σ := h a ha

/-! ## Cells -/

theorem kCell_const (pad : Nat) (c : E) (b : Nat) :
    kCell pad (.const c) b = if isPadOne c then ([], .n pad, b) else ([cst b c], .n b, b + 1) := rfl

theorem isPadOne_eq {c : E} (h : isPadOne c = true) : c = word 1 0 :=
  @of_decide_eq_true _ (Dec.eDecEq _ _) h

theorem kCell_atoms (pad : Nat) (k : KC) (b : Nat) : atomsOnly (kCell pad k b).1 = true := by
  cases k with
  | zero => rfl
  | const c => rw [kCell_const]; split <;> rfl
  | cell v => rfl

theorem kCell_sound {pad : Nat} (hp : PadOK σ pad) {k : KC} {b : Nat}
    (h : AtomsHold rd σ (kCell pad k b).1) : σ (kCell pad k b).2.1 = k.val σ := by
  cases k with
  | zero => exact hp.2.1
  | const c =>
      rw [kCell_const] at h ⊢
      by_cases hc : isPadOne c = true
      · simp only [hc, ↓reduceIte, KC.val]
        rw [isPadOne_eq hc]
        exact hp.1
      · simp only [hc, Bool.false_eq_true, ↓reduceIte, KC.val] at h ⊢
        exact h.atom (List.mem_singleton_self _)
  | cell v => rfl

theorem kXor_sound {pad : Nat} (hp : PadOK σ pad) {st : V} {k : KC} {b : Nat}
    (h : AtomsHold rd σ (kXor pad st k b).1) :
    σ (kXor pad st k b).2.1 = σ st + k.val σ := by
  cases k with
  | zero => simp [kXor, KC.val]
  | const c =>
      have h' : AtomsHold rd σ ((kCell pad (.const c) b).1 ++
          [addS (.n (kCell pad (.const c) b).2.2) st (kCell pad (.const c) b).2.1]) := h
      have e := kCell_sound hp h'.left
      have hadd := h'.right.atom (List.mem_singleton_self _)
      simp only [Atom.Holds] at hadd
      show σ (V.n (kCell pad (.const c) b).2.2) = _
      rw [hadd, e]
  | cell v =>
      exact (show AtomsHold rd σ [.atom (.add (.n b) st v)] from h).atom (List.mem_singleton_self _)

theorem kRunFresh_sound : ∀ {ks : List KC} {b : Nat},
    AtomsHold rd σ (kRunFresh ks b) → ∀ j < ks.length, σ (.n (b + j)) = (ks.getD j .zero).val σ
  | [], _, _, j, hj => absurd hj (by simp)
  | k :: ks, b, h, j, hj => by
      have h1 : (match k with
          | .zero => σ (.n b) = 0
          | .const c => σ (.n b) = c
          | .cell o => σ (.n b) = σ o) ∧ AtomsHold rd σ (kRunFresh ks (b + 1)) := by
        cases k with
        | zero =>
            refine ⟨?_, h.sub fun _ hx => List.mem_cons_of_mem _ hx⟩
            have h0 : σ (.n b) = word 0 0 := h.atom (List.mem_cons_self ..)
            rw [h0]
            simp only [word, Value.ofBits_zero]
            exact Value.zero_eq_ofLimbs.symm
        | const c => exact ⟨h.atom (List.mem_cons_self ..), h.sub fun _ hx => List.mem_cons_of_mem _ hx⟩
        | cell o => exact ⟨h.atom (List.mem_cons_self ..), h.sub fun _ hx => List.mem_cons_of_mem _ hx⟩
      rcases j with _ | j
      · cases k <;> simpa [KC.val] using h1.1
      · have := kRunFresh_sound h1.2 j (by simpa using hj)
        rw [show b + (j + 1) = b + 1 + j by omega, this]
        simp

theorem kVals_getD : ∀ {ks : List KC}, (∀ k ∈ ks, ∃ v, k = .cell v) → ∀ j < ks.length,
    σ ((kVals ks).getD j default) = (ks.getD j .zero).val σ
  | [], _, j, hj => absurd hj (by simp)
  | k :: ks, h, j, hj => by
      obtain ⟨v, rfl⟩ := h k (by simp)
      rcases j with _ | j
      · rfl
      · simp only [kVals, List.getD_cons_succ]
        exact kVals_getD (fun k hk => h k (by simp [hk])) j (by simpa using hj)

theorem runV_getD (o n j : Nat) (hj : j < n) : (runV o n).getD j default = .n (o + j) := by
  simp [runV, List.getD_eq_getElem?_getD, hj]

theorem runV_length (o n : Nat) : (runV o n).length = n := by simp [runV]

theorem val_of_isZero {k : KC} (h : k.isZero = true) : k.val σ = 0 := by
  cases k <;> simp_all [KC.isZero, KC.val]

theorem kRun_eq (pad : Nat) (k0 k1 k2 k3 : KC) (tailRun : Bool) (b : Nat) :
    kRun pad [k0, k1, k2, k3] tailRun b =
      if tailRun then ([], kVals [k0, k1, k2, k3], b)
      else if [k0, k1, k2, k3].all KC.isZero then ([], runV (pad + 1) 4, b)
      else if (match k0 with | .const c => isPadOne c | _ => false) && [k1, k2, k3].all KC.isZero
        then ([], runV pad 4, b)
      else (kRunFresh [k0, k1, k2, k3] b, runV b 4, b + 4) := by
  unfold kRun
  cases k0 <;> simp

theorem PadOK.zero {pad : Nat} (hp : PadOK σ pad) : ∀ j < 4, σ ((runV (pad + 1) 4).getD j default) = 0 := by
  intro j hj
  rw [runV_getD _ _ _ hj]
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl
  · exact hp.2.1
  · exact hp.2.2.1
  · exact hp.2.2.2.1
  · exact hp.2.2.2.2

theorem kRun_length (pad : Nat) (k0 k1 k2 k3 : KC) (tailRun : Bool)
    (htr : tailRun = true → ∀ k ∈ [k0, k1, k2, k3], ∃ v, k = .cell v) (b : Nat) :
    (kRun pad [k0, k1, k2, k3] tailRun b).2.1.length = 4 := by
  rw [kRun_eq]
  split_ifs with ht
  · have := htr ht
    obtain ⟨v0, rfl⟩ := this k0 (by simp)
    obtain ⟨v1, rfl⟩ := this k1 (by simp)
    obtain ⟨v2, rfl⟩ := this k2 (by simp)
    obtain ⟨v3, rfl⟩ := this k3 (by simp)
    rfl
  all_goals exact runV_length _ _

theorem kRun_sound {pad : Nat} (hp : PadOK σ pad) {k0 k1 k2 k3 : KC}
    {tailRun : Bool} (htr : tailRun = true → ∀ k ∈ [k0, k1, k2, k3], ∃ v, k = .cell v) {b : Nat}
    (h : AtomsHold rd σ (kRun pad [k0, k1, k2, k3] tailRun b).1) :
    ∀ j < 4, σ ((kRun pad [k0, k1, k2, k3] tailRun b).2.1.getD j default) =
      ([k0, k1, k2, k3].getD j .zero).val σ := by
  intro j hj
  rw [kRun_eq] at h ⊢
  split_ifs at h ⊢ with ht hz h1
  · exact kVals_getD (htr ht) j (by simp; omega)
  · rw [hp.zero j hj, val_of_isZero]
    rw [List.getD_eq_getElem _ _ (by simp; omega)]
    exact List.all_eq_true.mp hz _ (List.getElem_mem _)
  · have h1' := Bool.and_eq_true_iff.mp h1
    rcases j with _ | j
    · rw [runV_getD _ _ _ hj]
      cases k0 with
      | const c =>
          simp only [KC.val, List.getD_cons_zero, Nat.add_zero, isPadOne_eq h1'.1]
          exact hp.1
      | zero => simp at h1'
      | cell v => simp at h1'
    · have hz' : ([k1, k2, k3].getD j .zero).isZero = true := by
        rw [List.getD_eq_getElem _ _ (by simp; omega)]
        exact List.all_eq_true.mp h1'.2 _ (List.getElem_mem _)
      rw [List.getD_cons_succ, val_of_isZero hz', runV_getD _ _ _ hj]
      rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl
      · exact hp.2.1
      · exact hp.2.2.1
      · exact hp.2.2.2.1
  · rw [runV_getD _ _ _ hj]
    exact kRunFresh_sound h j (by simp; omega)

theorem kTailXor_sound {pad : Nat} (hp : PadOK σ pad) : ∀ {sts : List V} {ks : List KC} {b : Nat},
    AtomsHold rd σ (kTailXor pad sts ks b).1 → ∀ j < ks.length, j < sts.length →
      σ ((kTailXor pad sts ks b).2.1.getD j default) = σ (sts.getD j default) + (ks.getD j .zero).val σ
  | [], _, _, _, j, _, hj => absurd hj (by simp)
  | _ :: _, [], _, _, j, hj, _ => absurd hj (by simp)
  | st :: sts, k :: ks, b, h, j, hjk, hjs => by
      cases k with
      | zero =>
          have h' : AtomsHold rd σ ([copyS (.n b) st] ++ (kTailXor pad sts ks (b + 1)).1) := h
          rcases j with _ | j
          · have := h'.left.atom (List.mem_singleton_self _)
            simpa [KC.val, kTailXor, Atom.Holds] using this
          · simpa [kTailXor] using kTailXor_sound hp h'.right j (by simpa using hjk) (by simpa using hjs)
      | const c =>
          have h' : AtomsHold rd σ ((kXor pad st (.const c) b).1 ++
              (kTailXor pad sts ks (kXor pad st (.const c) b).2.2).1) := h
          rcases j with _ | j
          · simpa [kTailXor] using kXor_sound hp h'.left
          · simpa [kTailXor] using kTailXor_sound hp h'.right j (by simpa using hjk) (by simpa using hjs)
      | cell v =>
          have h' : AtomsHold rd σ ((kXor pad st (.cell v) b).1 ++
              (kTailXor pad sts ks (kXor pad st (.cell v) b).2.2).1) := h
          rcases j with _ | j
          · simpa [kTailXor] using kXor_sound hp h'.left
          · simpa [kTailXor] using kTailXor_sound hp h'.right j (by simpa using hjk) (by simpa using hjs)

/-! ## A block's inputs -/

/-- The thirteen inputs of a block, read cell by cell. -/
theorem getD_ins13 {a0 a1 a2 a3 a8 : V} {T R : List V} (hT : T.length = 4)
    (c : Nat) (hc : c < 13) :
    (([a0, a1, a2, a3] ++ T ++ [a8] ++ R).getD c default) =
      if c = 0 then a0 else if c = 1 then a1 else if c = 2 then a2 else if c = 3 then a3
      else if c < 8 then T.getD (c - 4) default else if c = 8 then a8 else R.getD (c - 9) default := by
  interval_cases c <;> simp [List.getD_eq_getElem?_getD, hT, List.getElem?_append_right]

theorem getD_ins13' {a0 a1 a2 a3 a8 r9 r10 r11 r12 : V} {T : List V} (hT : T.length = 4)
    (c : Nat) (hc : c < 13) :
    (([a0, a1, a2, a3] ++ T ++ [a8, r9, r10, r11, r12]).getD c default) =
      if c = 0 then a0 else if c = 1 then a1 else if c = 2 then a2 else if c = 3 then a3
      else if c < 8 then T.getD (c - 4) default else if c = 8 then a8 else if c = 9 then r9
      else if c = 10 then r10 else if c = 11 then r11 else r12 := by
  interval_cases c <;> simp [List.getD_eq_getElem?_getD, hT]

theorem ins13_length {a0 a1 a2 a3 a8 : V} {T R : List V} (hT : T.length = 4) (hR : R.length = 4) :
    ([a0, a1, a2, a3] ++ T ++ [a8] ++ R).length = 13 := by
  simp [hT, hR]

theorem kTailXor_length (pad : Nat) : ∀ (sts : List V) (ks : List KC) (b : Nat),
    (kTailXor pad sts ks b).2.1.length = min sts.length ks.length
  | [], _, _ => by simp [kTailXor]
  | _ :: _, [], _ => by simp [kTailXor]
  | st :: sts, k :: ks, b => by
      cases k <;> simp [kTailXor, kTailXor_length pad sts ks, Nat.succ_min_succ]

/-- The value a block's input adds the cells to: the previous output's, zero at first. -/
def prevVal (σ : Val) : Option (List V) → Nat → E
  | none, _ => 0
  | some st, c => σ (st.getD c default)

/-- The tail of a block is cells. -/
def TailCells (blk : List KC) : Prop :=
  ∀ k ∈ [blk.getD 4 .zero, blk.getD 5 .zero, blk.getD 6 .zero, blk.getD 7 .zero], ∃ v, k = .cell v

theorem kIns_length {pad : Nat} {blk : List KC} {tailRun : Bool} {st : Option (List V)}
    (htr : st = none → tailRun = true → TailCells blk) (b : Nat) :
    (kIns pad blk tailRun st b).2.1.length = 13 := by
  cases st with
  | none => exact ins13_length (kRun_length _ _ _ _ _ _ (htr rfl) _) (runV_length _ _)
  | some st =>
      simp only [kIns]
      split
      · simp
      · simp [kTailXor_length]

/-- **A block's inputs**: the previous output (zero at first) plus the block's cells, its capacity
cells the previous output's (the padding run's zeros at first). -/
theorem kIns_sound {pad : Nat} (hp : PadOK σ pad) {blk : List KC} {tailRun : Bool}
    {st : Option (List V)} (htr : st = none → tailRun = true → TailCells blk) {b : Nat}
    (h : AtomsHold rd σ (kIns pad blk tailRun st b).1) :
    ∀ c < 13, σ ((kIns pad blk tailRun st b).2.1.getD c default) =
      prevVal σ st c + if c < 9 then (blk.getD c .zero).val σ else 0 := by
  intro c hc
  cases st with
  | none =>
      have htr := htr rfl
      have hT := kRun_length pad (blk.getD 4 .zero) (blk.getD 5 .zero) (blk.getD 6 .zero)
        (blk.getD 7 .zero) tailRun htr
      simp only [kIns] at h ⊢
      rw [getD_ins13 (hT _) c hc]
      simp only [prevVal, zero_add]
      have e0 := kCell_sound (k := blk.getD 0 .zero) (b := b) hp (h.sub fun x hx => by simp only [List.mem_append]; tauto)
      have e1 := kCell_sound (k := blk.getD 1 .zero) (b := (kCell pad (blk.getD 0 .zero) b).2.2) hp
        (h.sub fun x hx => by simp only [List.mem_append]; tauto)
      have e2 := kCell_sound (k := blk.getD 2 .zero) hp (h.sub fun x hx => by simp only [List.mem_append]; tauto)
      have e3 := kCell_sound (k := blk.getD 3 .zero) hp (h.sub fun x hx => by simp only [List.mem_append]; tauto)
      have et := kRun_sound (k0 := blk.getD 4 .zero) (k1 := blk.getD 5 .zero) (k2 := blk.getD 6 .zero)
        (k3 := blk.getD 7 .zero) hp htr (h.sub fun x hx => by simp only [List.mem_append]; tauto)
      have e8 := kCell_sound (k := blk.getD 8 .zero) hp (h.sub fun x hx => by simp only [List.mem_append]; tauto)
      interval_cases c
      · simpa using e0
      · simpa using e1
      · simpa using e2
      · simpa using e3
      · simpa using et 0 (by omega)
      · simpa using et 1 (by omega)
      · simpa using et 2 (by omega)
      · simpa using et 3 (by omega)
      · simpa using e8
      · simpa using hp.zero 0 (by omega)
      · simpa using hp.zero 1 (by omega)
      · simpa using hp.zero 2 (by omega)
      · simpa using hp.zero 3 (by omega)
  | some st =>
      simp only [kIns] at h ⊢
      have e0 := kXor_sound (st := st.getD 0 default) (k := blk.getD 0 .zero) (b := b) hp
        (h.sub fun x hx => by simp only [List.mem_append]; tauto)
      have e1 := kXor_sound (st := st.getD 1 default) (k := blk.getD 1 .zero)
        (b := (kXor pad (st.getD 0 default) (blk.getD 0 .zero) b).2.2) hp
        (h.sub fun x hx => by simp only [List.mem_append]; tauto)
      have e2 := kXor_sound (st := st.getD 2 default) (k := blk.getD 2 .zero) hp
        (h.sub fun x hx => by simp only [List.mem_append]; tauto)
      have e3 := kXor_sound (st := st.getD 3 default) (k := blk.getD 3 .zero) hp
        (h.sub fun x hx => by simp only [List.mem_append]; tauto)
      have e8 := kXor_sound (st := st.getD 8 default) (k := blk.getD 8 .zero) hp
        (h.sub fun x hx => by simp only [List.mem_append]; tauto)
      by_cases hz : [blk.getD 4 .zero, blk.getD 5 .zero, blk.getD 6 .zero, blk.getD 7 .zero].all
          KC.isZero = true
      · simp only [hz, ↓reduceIte] at h e8 ⊢
        have hz4 : ∀ j < 4, ([blk.getD 4 .zero, blk.getD 5 .zero, blk.getD 6 .zero,
            blk.getD 7 .zero].getD j .zero).val σ = 0 := fun j hj => by
          apply val_of_isZero
          rw [List.getD_eq_getElem _ _ (by simp; omega)]
          exact List.all_eq_true.mp hz _ (List.getElem_mem _)
        have z4 := hz4 0 (by omega); have z5 := hz4 1 (by omega)
        have z6 := hz4 2 (by omega); have z7 := hz4 3 (by omega)
        simp only [List.getD_cons_zero, List.getD_cons_succ] at z4 z5 z6 z7
        interval_cases c <;> simp_all [prevVal]
      · simp only [hz, Bool.false_eq_true, ↓reduceIte] at h e8 ⊢
        have et := kTailXor_sound (sts := [st.getD 4 default, st.getD 5 default, st.getD 6 default,
          st.getD 7 default]) (ks := [blk.getD 4 .zero, blk.getD 5 .zero, blk.getD 6 .zero,
          blk.getD 7 .zero]) hp (h.sub fun x hx => by simp only [List.mem_append]; tauto)
        have t4 := et 0 (by simp) (by simp); have t5 := et 1 (by simp) (by simp)
        have t6 := et 2 (by simp) (by simp); have t7 := et 3 (by simp) (by simp)
        simp only [List.getD_cons_zero, List.getD_cons_succ] at t4 t5 t6 t7
        rw [getD_ins13' (by simp [kTailXor_length]) c hc]
        interval_cases c
        · simpa [prevVal] using e0
        · simpa [prevVal] using e1
        · simpa [prevVal] using e2
        · simpa [prevVal] using e3
        · simpa [prevVal] using t4
        · simpa [prevVal] using t5
        · simpa [prevVal] using t6
        · simpa [prevVal] using t7
        · simpa [prevVal] using e8
        · simp [prevVal]
        · simp [prevVal]
        · simp [prevVal]
        · simp [prevVal]

/-! ## The blocks -/

/-- The inputs and the output base of each block, as `kBlocks` emits them. -/
def kTrace (pad : Nat) (cs : List KC) (B : Nat) (tailRun : Bool) (out : Option Nat) (n : Nat) :
    Nat → Nat → Option (List V) → Nat → List (List V × Nat)
  | 0, _, _, _ => []
  | m + 1, k, st, b =>
      let blk := (cs.drop (17 * k / 2)).take 9
      let ins := kIns pad blk tailRun st b
      let last := k + 1 == B
      let o := if last then out.getD ins.2.2 else ins.2.2
      let b' := if last && out.isSome then ins.2.2 else ins.2.2 + kOutN B n k
      (ins.2.1, o) :: kTrace pad cs B tailRun out n m (k + 1) (some (runV o 13)) b'

/-- The block `k` read from the cells `cs`. -/
def blockOf (cs : List KC) (k : Nat) : List KC := (cs.drop (17 * k / 2)).take 9

/-- Block `k`, entry `e` of the trace, from the previous state `st`: thirteen inputs, the previous
output (zero at first) plus the block's cells, and its `KECCAK`, writing the first `kOutN B n k`
cells of its output `O`. -/
def BlockOK (σ : Val) (cs : List KC) (B n k : Nat) (st : Option (List V)) (e : List V × Nat) :
    Prop :=
  e.1.length = 13 ∧
    (∀ c < 13, σ (e.1.getD c default) =
      prevVal σ st c + if c < 9 then ((blockOf cs k).getD c .zero).val σ else 0) ∧
    ∃ O : Fin 13 → E, KeccakCellsRelation (cells13 (e.1.map σ)) (k % 2 == 1) O
      (!(k + 1 == B) && k % 2 == 0) .all ∧ ∀ c : Fin 13, c.val < kOutN B n k → σ (.n (e.2 + c)) = O c

/-- The state block `j` of a trace starts from. -/
def stAt (tr : List (List V × Nat)) (st : Option (List V)) : Nat → Option (List V)
  | 0 => st
  | j + 1 => some (runV (tr.getD j ([], 0)).2 13)

theorem stAt_cons (e : List V × Nat) (tr : List (List V × Nat)) (st : Option (List V)) (j : Nat) :
    stAt (e :: tr) st (j + 1) = stAt tr (some (runV e.2 13)) j := by
  cases j <;> rfl

theorem kBlocks_sound {pad : Nat} (hp : PadOK σ pad) {cs : List KC} {B : Nat} {tailRun : Bool}
    {out : Option Nat} {n : Nat} : ∀ (m k : Nat) (st : Option (List V)) (b : Nat),
    (st = none → tailRun = true → TailCells (blockOf cs k)) →
    AtomsHold rd σ (kBlocks pad cs B tailRun out n m k st b).1 →
    ∀ j < m, BlockOK σ cs B n (k + j) (stAt (kTrace pad cs B tailRun out n m k st b) st j)
      ((kTrace pad cs B tailRun out n m k st b).getD j ([], 0))
  | 0, _, _, _, _, _, j, hj => absurd hj (by omega)
  | m + 1, k, st, b, htr, h, j, hj => by
      simp only [kBlocks] at h
      have hins := h.left.left
      have hkec := h.left.right.atom (List.mem_singleton_self _)
      have hrest := h.right
      rcases j with _ | j
      · simp only [kTrace, stAt, List.getD_cons_zero, Nat.add_zero]
        refine ⟨kIns_length htr _, kIns_sound hp htr hins, ?_⟩
        obtain ⟨-, -, O, hk, hw⟩ := keccak_holds_full hkec
        refine ⟨O, hk, fun c hc => ?_⟩
        have := hw c (by rw [runV_length]; exact hc)
        simpa [runV] using this
      · have ih := kBlocks_sound hp m (k + 1) _ _ (fun h => by simp at h) hrest j (by omega)
        simp only [kTrace, List.getD_cons_succ]
        rw [show k + (j + 1) = k + 1 + j by omega, stAt_cons]
        exact ih

/-- The last block writes the output run `kBlocks` returns. -/
theorem kBlocks_out {pad : Nat} {cs : List KC} {B : Nat} {tailRun : Bool} {out : Option Nat}
    {n : Nat} : ∀ (m k : Nat) (st : Option (List V)) (b : Nat), k + m = B → 0 < m →
    (kBlocks pad cs B tailRun out n m k st b).2.2 =
      ((kTrace pad cs B tailRun out n m k st b).getD (m - 1) ([], 0)).2
  | 0, _, _, _, _, hm => absurd hm (by omega)
  | 1, k, st, b, hB, _ => by
      subst hB
      simp [kBlocks, kTrace]
  | m + 2, k, st, b, hB, _ => by
      have hl : (k + 1 == B) = false := by simp; omega
      simp only [kBlocks, kTrace, hl, Bool.false_eq_true, ↓reduceIte, kOutN]
      exact kBlocks_out (m + 1) (k + 1) _ _ (by omega) (by omega)

/-! ## The padding bytes -/

theorem byteWord_eq_byteCell (pos v : Nat) : byteWord pos v = byteCell pos v := by
  simp only [byteWord, byteCell]
  by_cases h : pos % 16 < 8
  · simp [h, Nat.mod_eq_of_lt h]
  · simp [h, show pos % 16 % 8 = pos % 16 - 8 by omega]

theorem kXorByte_sound {cs : List KC} {pos v b : Nat} (h : AtomsHold rd σ (kXorByte cs pos v b).1) :
    (kXorByte cs pos v b).2.1.map (KC.val σ) = xorByte (cs.map (KC.val σ)) pos v := by
  simp only [kXorByte] at h ⊢
  rw [xorByte]
  by_cases hi : pos / 16 < cs.length
  · rw [List.modify_eq_set, List.getElem?_map, List.getElem?_eq_getElem hi]
    simp only [Option.map_some, Option.getD_some]
    have hk : cs.getD (pos / 16) .zero = cs[pos / 16] := List.getD_eq_getElem _ _ hi
    rw [hk] at h ⊢
    generalize hk' : cs[pos / 16] = k at h ⊢
    cases k with
    | zero => simp [List.map_set, KC.val, byteWord_eq_byteCell]
    | const c => simp [List.map_set, KC.val, byteWord_eq_byteCell]
    | cell o =>
        have h1 := h.atom (List.mem_cons_self ..)
        have h2 := h.atom (List.mem_cons_of_mem _ (List.mem_singleton_self _))
        simp only [Atom.Holds] at h1 h2
        simp only [List.map_set, KC.val, h2, h1, byteWord_eq_byteCell]
  · rw [List.modify_eq_self (by simp; omega)]
    have hk : cs.getD (pos / 16) .zero = .zero := by
      rw [List.getD_eq_default _ _ (by omega)]
    rw [hk]
    simp only
    rw [List.set_eq_of_length_le (by omega)]

/-! ## The message -/

/-- The message cells `kMsg` absorbs: the cells zero-extended to the last block's read, the two
padding bytes XORed in. -/
def kMsgCells (cells : List KC) (len b : Nat) : List KC :=
  let B := kBlocksOf len
  let cs0 := cells ++ List.replicate (17 * (B - 1) / 2 + 9 - cells.length) KC.zero
  (kXorByte (kXorByte cs0 len 1 b).2.1 (136 * B - 1) 0x80 (kXorByte cs0 len 1 b).2.2).2.1

theorem cells13_map (l : List V) (c : Fin 13) (hc : c.val < l.length) :
    cells13 (l.map σ) c = σ (l.getD c default) := by
  simp [cells13, List.getD_eq_getElem?_getD, hc]

theorem val_getD (cs : List KC) (j : Nat) : (cs.getD j .zero).val σ = (cs.map (KC.val σ)).getD j 0 := by
  by_cases hj : j < cs.length
  · simp [hj]
  · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by simp; omega)]
    rfl

theorem blockOf_getD (cs : List KC) (k c : Nat) (hc : c < 9) :
    ((blockOf cs k).getD c .zero).val σ = (cs.map (KC.val σ)).getD (17 * k / 2 + c) 0 := by
  rw [val_getD, blockOf, List.map_take, List.map_drop, List.getD_eq_getElem?_getD,
    List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hc, List.getElem?_drop]

/-- **The lowered Keccak message computes Keccak-256**: when the statements of `kMsg` hold, the
padding run holding `[0x01, 0, 0, 0, 0]`, the cells the last block writes, one or two of the output
run's first two, are the digest's halves of the message cells' first `len` bytes, the bytes past
`len` being zero. -/
theorem kMsg_sound_cells {pad : Nat} (hp : PadOK σ pad) {cells : List KC} {len : Nat}
    {tailRun : Bool} {out : Option Nat} {b n : Nat}
    (htr : tailRun = true → TailCells (blockOf (kMsgCells cells len b) 0))
    (h : AtomsHold rd σ (kMsg pad cells len tailRun out b n).1)
    (hlen : len ≤ 16 * cells.length)
    (hz : ∀ j, len ≤ j → (cellsBytes (cells.map (KC.val σ))).getD j 0 = 0) :
    (1 ≤ n → σ (.n (kMsg pad cells len tailRun out b n).2.2) =
        (digestHalves (keccak256 ((cellsBytes (cells.map (KC.val σ))).take len))).1) ∧
      (2 ≤ n → σ (.n ((kMsg pad cells len tailRun out b n).2.2 + 1)) =
        (digestHalves (keccak256 ((cellsBytes (cells.map (KC.val σ))).take len))).2) := by
  simp only [kMsg] at h ⊢
  simp only [kMsgCells] at htr
  set B := kBlocksOf len with hB
  set cs0 := cells ++ List.replicate (17 * (B - 1) / 2 + 9 - cells.length) KC.zero with hcs0
  set x1 := kXorByte cs0 len 1 b with hx1
  set x2 := kXorByte x1.2.1 (136 * B - 1) 0x80 x1.2.2 with hx2
  set cs := x2.2.1 with hcs
  have e1 := kXorByte_sound (h.left.left : AtomsHold rd σ x1.1)
  have e2 := kXorByte_sound (h.left.right : AtomsHold rd σ x2.1)
  have hP : cs.map (KC.val σ) = padCells (cells.map (KC.val σ)) len := by
    rw [hcs, e2, e1, hcs0, List.map_append, List.map_replicate]
    simp only [padCells, padRead, hB, kBlocksOf, rate, KC.val, List.length_map, Nat.add_sub_cancel]
  set tr := kTrace pad cs B tailRun out n B 0 none x2.2.2 with htr'
  have hbl := kBlocks_sound (rd := rd) hp B 0 none x2.2.2 (fun _ => htr) h.right
  have hB1 : 0 < B := by simp [hB, kBlocksOf]
  have hlenB : len / rate + 1 = B := by simp [hB, kBlocksOf, rate]
  let I : Nat → Fin 13 → E := fun j => cells13 ((tr.getD j ([], 0)).1.map σ)
  let O : Nat → Fin 13 → E := fun j => match j with
    | 0 => cellsOfState zeroState false
    | j + 1 => cellsOfState (keccakF1600 (stateOfCells (I j) (j % 2 == 1)))
        (!(j + 1 == B) && j % 2 == 0)
  have hblk : ∀ k < B, ∃ O' : Fin 13 → E, KeccakCellsRelation (I k) (k % 2 == 1) O'
      (!(k + 1 == B) && k % 2 == 0) .all ∧
      ∀ c : Fin 13, c.val < kOutN B n k → σ (.n ((tr.getD k ([], 0)).2 + c)) = O (k + 1) c := by
    intro k hk
    obtain ⟨-, -, O', hk', hw⟩ := hbl k hk
    rw [Nat.zero_add] at hk' hw
    exact ⟨O', hk', fun c hc => (hw c hc).trans (hk' c c.isLt)⟩
  have hprev : ∀ k < B, ∀ c : Fin 13, prevVal σ (stAt tr none k) c = O k c := by
    intro k hk c
    cases k with
    | zero => simp [prevVal, stAt, O, cellsOfState_zero]
    | succ k =>
        obtain ⟨-, -, hw⟩ := hblk k (by omega)
        have hl : (k + 1 == B) = false := by simp; omega
        have := hw c (by simp only [kOutN, hl, Bool.false_eq_true, ↓reduceIte]; exact c.isLt)
        simp only [prevVal, stAt]
        rw [runV_getD _ _ _ c.isLt]
        exact this
  have hin : ∀ k < B, ∀ c : Fin 13, I k c = O k c +
      if c.val < 9 then (padCells (cells.map (KC.val σ)) len).getD (17 * k / 2 + c) 0 else 0 := by
    intro k hk c
    have hb := hbl k hk
    rw [Nat.zero_add] at hb
    show cells13 ((tr.getD k ([], 0)).1.map σ) c = _
    rw [cells13_map _ _ (by rw [hb.1]; exact c.isLt), hb.2.1 c c.isLt, hprev k hk c]
    split
    · rename_i hc; rw [blockOf_getD _ _ _ hc, hP]
    · rfl
  have hfinal := keccak_final_digest (pre := []) (n := 0) (I := I) (O := O) (by simp)
    (by simpa using hlen) hz (by simp [O, absorbChunks])
    (fun k hk c hc => by rw [hlenB] at hk; rw [hin k hk c]; simp [hc])
    (fun k hk c hc => by
      rw [hlenB] at hk
      rw [hin k hk c]
      simp [show ¬ c.val < 9 by omega])
    (fun k _ c _ => rfl)
  rw [List.nil_append, hlenB] at hfinal
  rw [← hfinal]
  obtain ⟨B', hB'⟩ : ∃ B', B = B' + 1 := ⟨B - 1, by omega⟩
  have hout := kBlocks_out (pad := pad) (cs := cs) (B := B) (tailRun := tailRun) (out := out)
    (n := n) B 0 none x2.2.2 (by omega) hB1
  rw [hout]
  obtain ⟨-, -, hw⟩ := hblk B' (by omega)
  have hl : (B' + 1 == B) = true := by simp [hB']
  simp only [kOutN, hl, ↓reduceIte] at hw
  rw [show B - 1 = B' by omega, ← htr', hB']
  refine ⟨fun hn => ?_, fun hn => ?_⟩
  · have := hw 0 (by simp; omega)
    simpa [hB'] using this
  · have := hw 1 (by simp; omega)
    simpa [hB'] using this

/-- **The lowered Keccak message's first cell is the digest's first half** (`kMsg_sound_cells`). -/
theorem kMsg_sound {pad : Nat} (hp : PadOK σ pad) {cells : List KC} {len : Nat} {tailRun : Bool}
    {out : Option Nat} {b n : Nat}
    (htr : tailRun = true → TailCells (blockOf (kMsgCells cells len b) 0))
    (h : AtomsHold rd σ (kMsg pad cells len tailRun out b n).1)
    (hlen : len ≤ 16 * cells.length)
    (hz : ∀ j, len ≤ j → (cellsBytes (cells.map (KC.val σ))).getD j 0 = 0)
    (hn : 1 ≤ n := by decide) :
    σ (.n (kMsg pad cells len tailRun out b n).2.2) =
      (digestHalves (keccak256 ((cellsBytes (cells.map (KC.val σ))).take len))).1 :=
  (kMsg_sound_cells hp htr h hlen hz).1 hn

/-- **A lowered Keccak message into two cells or more computes the Keccak-256 digest**
(`kMsg_sound_cells`). -/
theorem kMsg_sound2 {pad : Nat} (hp : PadOK σ pad) {cells : List KC} {len : Nat} {tailRun : Bool}
    {out : Option Nat} {b n : Nat}
    (htr : tailRun = true → TailCells (blockOf (kMsgCells cells len b) 0))
    (h : AtomsHold rd σ (kMsg pad cells len tailRun out b n).1)
    (hlen : len ≤ 16 * cells.length)
    (hz : ∀ j, len ≤ j → (cellsBytes (cells.map (KC.val σ))).getD j 0 = 0)
    (hn : 2 ≤ n := by decide) :
    (σ (.n (kMsg pad cells len tailRun out b n).2.2),
        σ (.n ((kMsg pad cells len tailRun out b n).2.2 + 1))) =
      digestHalves (keccak256 ((cellsBytes (cells.map (KC.val σ))).take len)) := by
  have h2 := kMsg_sound_cells hp htr h hlen hz
  rw [h2.1 (by omega), h2.2 hn]

/-! ## Atoms only -/

theorem kRunFresh_atoms : ∀ (ks : List KC) (b : Nat), atomsOnly (kRunFresh ks b) = true
  | [], _ => rfl
  | .zero :: ks, b => kRunFresh_atoms ks (b + 1)
  | .const _ :: ks, b => kRunFresh_atoms ks (b + 1)
  | .cell _ :: ks, b => kRunFresh_atoms ks (b + 1)

theorem kRun_atoms' (pad : Nat) (ks : List KC) (tailRun : Bool) (b : Nat) :
    atomsOnly (kRun pad ks tailRun b).1 = true := by
  unfold kRun
  split_ifs
  · rfl
  · rfl
  · split
    · split_ifs
      · rfl
      · exact kRunFresh_atoms _ _
    · exact kRunFresh_atoms _ _

theorem kXor_atoms (pad : Nat) (st : V) (k : KC) (b : Nat) : atomsOnly (kXor pad st k b).1 = true := by
  cases k with
  | zero => rfl
  | const c =>
      show atomsOnly ((kCell pad _ b).1 ++ _) = true
      rw [atomsOnly_append, kCell_atoms]; rfl
  | cell v => rfl

theorem kTailXor_atoms (pad : Nat) : ∀ (sts : List V) (ks : List KC) (b : Nat),
    atomsOnly (kTailXor pad sts ks b).1 = true
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | st :: sts, k :: ks, b => by
      cases k with
      | zero =>
          show atomsOnly ([copyS (.n b) st] ++ _) = true
          rw [atomsOnly_append, kTailXor_atoms pad sts ks]; rfl
      | const c =>
          show atomsOnly ((kXor pad st (.const c) b).1 ++ _) = true
          rw [atomsOnly_append, kXor_atoms, kTailXor_atoms pad sts ks]; rfl
      | cell v =>
          show atomsOnly ((kXor pad st (.cell v) b).1 ++ _) = true
          rw [atomsOnly_append, kXor_atoms, kTailXor_atoms pad sts ks]; rfl

theorem kIns_atoms (pad : Nat) (blk : List KC) (tailRun : Bool) (st : Option (List V)) (b : Nat) :
    atomsOnly (kIns pad blk tailRun st b).1 = true := by
  cases st with
  | none => simp [kIns, atomsOnly_append, kCell_atoms, kRun_atoms']
  | some st =>
      simp only [kIns]
      split <;> simp [atomsOnly_append, kXor_atoms, kTailXor_atoms]

theorem kBlocks_atoms (pad : Nat) (cs : List KC) (B : Nat) (tailRun : Bool) (out : Option Nat)
    (n : Nat) : ∀ m k st b, atomsOnly (kBlocks pad cs B tailRun out n m k st b).1 = true
  | 0, _, _, _ => rfl
  | m + 1, k, st, b => by
      simp only [kBlocks, atomsOnly_append, kIns_atoms, kBlocks_atoms pad cs B tailRun out n m]
      rfl

theorem kXorByte_atoms (cs : List KC) (pos v b : Nat) : atomsOnly (kXorByte cs pos v b).1 = true := by
  simp only [kXorByte]
  split <;> rfl

theorem kMsg_atoms (pad : Nat) (cells : List KC) (len : Nat) (tailRun : Bool) (out : Option Nat)
    (b n : Nat) : atomsOnly (kMsg pad cells len tailRun out b n).1 = true := by
  simp only [kMsg, atomsOnly_append, kXorByte_atoms, kBlocks_atoms, Bool.and_self]

end
end LeanVM.Guest.B1.Sig
