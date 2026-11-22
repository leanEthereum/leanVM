module

public import LeanVM.Guest.CoreMode.FrameOp
public import LeanVM.Guest.Mode.Hints

/-!
# The frame walk's pass, offset by offset

The pass reads a function's hints through a cursor (`advC`, `hintsC`); with the hints by pc
(`Mode.hintsAt`) instead it is `frameRunH`, the same (`frameRun_eq`) wherever the cursor holds
every entry from the offset's pc on (`CurOk`). What the walk knows at offset `i`: the live path and
pending groups before it (`preF`, the pass over the code's first `i` instructions), and a state of
the executor is at the offset when the live path holds there or a pending group into the offset
does (`AtF`). `atF_zero`: the entry. `atF_step`: at an offset the walk accepts, the joined path holds
and its step (`offF`) goes through; what falls through holds at the next offset, and a group it adds
into a later offset `j` holds at `j` (`covF_forward`).
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest
open LeanVM.Prover.Exec (Hint)

@[expose] public section

/-! ## The hints by pc -/

/-- One offset of the pass with the hints by pc, `run` walking the rest. -/
noncomputable def passH (Fn : FFun) (ins : OffsetInstruction)
    (run : ℕ → Option FSt → FPend → Option (Option FSt × FPend))
    (i : ℕ) (cur : Option FSt) (pend : FPend) : Option (Option FSt × FPend) :=
  match cutF Fn i cur pend with
  | none => none
  | some (cur, pend) =>
    match joinF i cur pend with
    | (none, pend) => run (i + 1) none pend
    | (some A, pend) =>
      match offF Fn i (Mode.hintsAt Fn.hints (Fn.entry + i)) A ins pend with
      | some (cur, pend) => run (i + 1) cur pend
      | none => none

/-- The pass with the hints by pc. -/
noncomputable def frameRunH (Fn : FFun) : List OffsetInstruction → ℕ → Option FSt → FPend →
    Option (Option FSt × FPend)
  | [], _, cur, pend => some (cur, pend)
  | ins :: code, i, cur, pend => passH Fn ins (frameRunH Fn code) i cur pend

/-- The cursor `c` holds the entries of `d` from pc `P` on, in order. -/
def CurOk (d : List (ℕ × List Hint)) (P : ℕ) (c : List (ℕ × List Hint)) : Prop :=
  Mode.pcsIncr c = true ∧ (∀ x ∈ c, x ∈ d) ∧ ∀ x ∈ d, P ≤ x.1 → x ∈ c

theorem pcsIncr_cons_lt {a : ℕ × List Hint} {l : List (ℕ × List Hint)}
    (h : Mode.pcsIncr (a :: l) = true) : ∀ x ∈ l, a.1 < x.1 := by
  induction l generalizing a with
  | nil => intro x hx; cases hx
  | cons b l ih =>
    simp only [Mode.pcsIncr, Bool.and_eq_true, decide_eq_true_eq] at h
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · exact lt_trans h.1 (ih h.2 x hx)

theorem pcsIncr_tail' {a : ℕ × List Hint} {l : List (ℕ × List Hint)} (h : Mode.pcsIncr (a :: l) = true) :
    Mode.pcsIncr l = true := by
  cases l with
  | nil => rfl
  | cons b l => simp only [Mode.pcsIncr, Bool.and_eq_true] at h; exact h.2

theorem pcsIncr_dropWhile {p : ℕ × List Hint → Bool} :
    ∀ {l : List (ℕ × List Hint)}, Mode.pcsIncr l = true → Mode.pcsIncr (l.dropWhile p) = true
  | [], _ => rfl
  | a :: l, h => by
    rw [List.dropWhile_cons]
    split_ifs
    · exact pcsIncr_dropWhile (pcsIncr_tail' h)
    · exact h

theorem mem_dropWhile_of {p : ℕ × List Hint → Bool} {x : ℕ × List Hint} (hx : p x = false) :
    ∀ {l : List (ℕ × List Hint)}, x ∈ l → x ∈ l.dropWhile p
  | [], h => absurd h List.not_mem_nil
  | a :: l, h => by
    rw [List.dropWhile_cons]
    split_ifs with ha
    · rcases List.mem_cons.mp h with rfl | h
      · rw [hx] at ha; cases ha
      · exact mem_dropWhile_of hx h
    · exact h

theorem hintsAt_of_mem {d : List (ℕ × List Hint)} (hd : Mode.pcsIncr d = true) {P : ℕ}
    {h : List Hint} (hm : (P, h) ∈ d) : Mode.hintsAt d P = h := by
  induction d with
  | nil => cases hm
  | cons a d ih =>
    unfold Mode.hintsAt
    rw [List.find?_cons]
    rcases List.mem_cons.mp hm with rfl | hm
    · simp
    · have hlt := pcsIncr_cons_lt hd _ hm
      have hne : (a.1 == P) = false := by simp only [beq_eq_false_iff_ne]; simp at hlt; omega
      rw [hne]
      exact ih (pcsIncr_tail' hd) hm

theorem hintsAt_of_not {d : List (ℕ × List Hint)} {P : ℕ} (h : ∀ x ∈ d, x.1 ≠ P) :
    Mode.hintsAt d P = [] := by
  unfold Mode.hintsAt
  rw [List.find?_eq_none.mpr fun x hx ↦ by simpa using h x hx]

/-- **The cursor reads the hints by pc.** -/
theorem hintsC_advC {d c : List (ℕ × List Hint)} (hd : Mode.pcsIncr d = true) {P : ℕ}
    (h : CurOk d P c) : hintsC (advC c P) P = Mode.hintsAt d P := by
  obtain ⟨hc, hsub, hall⟩ := h
  have hinc := pcsIncr_dropWhile (p := fun p ↦ decide (p.1 < P)) hc
  have hkeep : ∀ x ∈ d, P ≤ x.1 → x ∈ advC c P := fun x hx hP ↦
    mem_dropWhile_of (by simp; omega) (hall x hx hP)
  unfold advC at hkeep hinc ⊢
  rcases e : c.dropWhile (fun p ↦ decide (p.1 < P)) with _ | ⟨⟨p, hs⟩, r⟩
  · rw [e, hintsAt_of_not fun x hx hx1 ↦ by
      have := hkeep x hx (by omega); rw [e] at this; cases this]
    rfl
  · have hhd : P ≤ p := by simpa [e] using List.head?_dropWhile_not (fun p ↦ decide (p.1 < P)) c
    rw [e]
    simp only [hintsC]
    split_ifs with hp
    · subst hp
      exact (hintsAt_of_mem hd
        (hsub _ ((List.dropWhile_sublist _).subset (by rw [e]; exact List.mem_cons_self ..)))).symm
    · rw [hintsAt_of_not fun x hx hx1 ↦ by
        have hm := hkeep x hx (by omega)
        rw [e] at hm hinc
        rcases List.mem_cons.mp hm with rfl | hm
        · exact hp hx1
        · have := pcsIncr_cons_lt hinc x hm; simp at this; omega]

theorem curOk_adv {d c : List (ℕ × List Hint)} {P : ℕ} (h : CurOk d P c) :
    CurOk d (P + 1) (advC c P) := by
  obtain ⟨hc, hsub, hall⟩ := h
  exact ⟨pcsIncr_dropWhile hc, fun x hx ↦ hsub x ((List.dropWhile_sublist _).subset hx),
    fun x hx hP ↦ mem_dropWhile_of (by simp; omega) (hall x hx (by omega))⟩

theorem optFSeq_eq {β : Type} (o : Option FSt) (k : Option FSt → β) : optFSeq o k = k o := by
  cases o with
  | none => rfl
  | some A => obtain ⟨st, w, nz, hq, hs, cp, one⟩ := A; simp only [optFSeq, FSt.force,
      Exec.St.seq_eq, Exec.Trie.seq_eq]

theorem FSt.force_eq {β : Type} (A : FSt) (k : FSt → β) : A.force k = k A := by
  obtain ⟨st, w, nz, hq, hs, cp, one⟩ := A
  simp only [FSt.force, Exec.St.seq_eq, Exec.Trie.seq_eq]

/-- **The pass reads the hints by pc** through its cursor. -/
theorem frameRun_eq {Fn : FFun} (hd : Mode.pcsIncr Fn.hints = true) :
    ∀ (code : List OffsetInstruction) (i : ℕ) (c : List (ℕ × List Hint)) (cur : Option FSt) (pend : FPend),
      CurOk Fn.hints (Fn.entry + i) c → frameRun Fn code i c cur pend = frameRunH Fn code i cur pend
  | [], _, _, _, _, _ => rfl
  | ins :: code, i, c, cur, pend, hc => by
    have hc' : CurOk Fn.hints (Fn.entry + (i + 1)) (advC c (Fn.entry + i)) := by
      have h := curOk_adv hc; rw [Nat.add_assoc] at h; exact h
    have ih := fun cur pend ↦ frameRun_eq hd code (i + 1) (advC c (Fn.entry + i)) cur pend hc'
    show passF Fn ins (frameRun Fn code) i c cur pend = passH Fn ins (frameRunH Fn code) i cur pend
    unfold passF passH
    rw [Exec.headSeq_eq, hintsC_advC hd hc]
    rcases cutF Fn i cur pend with _ | ⟨cur', pend'⟩
    · rfl
    · dsimp only
      rcases joinF i cur' pend' with ⟨_ | A, p⟩
      · dsimp only; rw [Exec.natSeq_eq, ih]
      · dsimp only
        rcases offF Fn i (Mode.hintsAt Fn.hints (Fn.entry + i)) A ins p with _ | ⟨cur'', p''⟩
        · rfl
        · dsimp only; rw [optFSeq_eq, Exec.headSeq_eq, Exec.natSeq_eq, ih]

theorem frameRunH_append (Fn : FFun) : ∀ (l₁ l₂ : List OffsetInstruction) (i : ℕ) (cur : Option FSt)
    (pend : FPend), frameRunH Fn (l₁ ++ l₂) i cur pend =
      (frameRunH Fn l₁ i cur pend).bind fun p ↦ frameRunH Fn l₂ (i + l₁.length) p.1 p.2
  | [], _, _, _, _ => rfl
  | ins :: l₁, l₂, i, cur, pend => by
    show passH Fn ins (frameRunH Fn (l₁ ++ l₂)) i cur pend = (passH Fn ins (frameRunH Fn l₁) i cur pend).bind _
    unfold passH
    rcases cutF Fn i cur pend with _ | ⟨cur', pend'⟩
    · rfl
    · dsimp only
      rcases joinF i cur' pend' with ⟨_ | A, p⟩
      · dsimp only; rw [frameRunH_append Fn l₁ l₂ (i + 1)]; simp [Nat.add_assoc, Nat.add_comm 1]
      · dsimp only
        rcases offF Fn i (Mode.hintsAt Fn.hints (Fn.entry + i)) A ins p with _ | ⟨cur'', p''⟩
        · rfl
        · dsimp only; rw [frameRunH_append Fn l₁ l₂ (i + 1)]; simp [Nat.add_assoc, Nat.add_comm 1]


/-! ## Pending groups -/

section Pend

variable {κ : ℕ} (img : MemoryImage κ)

/-- Some group of `P` enters offset `j` with a state that holds at `s`. -/
def CovF (s : Prover.Exec.St) (P : FPend) (j : ℕ) : Prop := ∃ g ∈ P, j ∈ g.2.1 ∧ FHolds img s g.2.2

/-- Every group's targets increase, from `k` on, a tagged group's those of its table in `ar`. -/
def PendOkF (ar : Exec.Trie (List ℕ)) (P : FPend) (k : ℕ) : Prop :=
  ∀ g ∈ P, incrF g.2.1 = true ∧ (∀ t ∈ g.2.1, k ≤ t) ∧ (g.1 ≠ 0 → ar.get (g.1 - 1) = some g.2.1)

/-- Every edge of `P` is one of `Q`'s. -/
def PendLeF (P Q : FPend) : Prop := ∀ s j, CovF img s P j → CovF img s Q j

variable {img}

theorem incrF_lt : ∀ {t : ℕ} {ts : List ℕ}, incrF (t :: ts) = true → ∀ u ∈ ts, t < u
  | _, [], _, _, hu => absurd hu List.not_mem_nil
  | t, b :: l, h, u, hu => by
    simp only [incrF, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases List.mem_cons.mp hu with rfl | hu
    · exact h.1
    · exact lt_trans h.1 (incrF_lt h.2 u hu)

theorem incrF_tail {t : ℕ} {ts : List ℕ} (h : incrF (t :: ts) = true) : incrF ts = true := by
  cases ts with
  | nil => rfl
  | cons b l => simp only [incrF, Bool.and_eq_true] at h; exact h.2

theorem PendOkF.cons {ar : Exec.Trie (List ℕ)} {g : ℕ × List ℕ × FSt} {P : FPend} {k : ℕ}
    (h : PendOkF ar (g :: P) k) : PendOkF ar P k :=
  fun g' hg' ↦ h g' (List.mem_cons_of_mem _ hg')

theorem popF_cons (i k : ℕ) (ts : List ℕ) (B : FSt) (gs : FPend) :
    popF i ((k, ts, B) :: gs) = match ts with
      | t :: ts' =>
        if t = i then (some (meetOpt B (popF i gs).1),
          if ts' = [] then (popF i gs).2 else (0, ts', B) :: (popF i gs).2)
        else ((popF i gs).1, (k, t :: ts', B) :: (popF i gs).2)
      | [] => ((popF i gs).1, (popF i gs).2) := by
  conv_lhs => unfold popF
  rcases popF i gs with ⟨o, ps⟩
  rfl

theorem meetOpt_left {s : Prover.Exec.St} {B : FSt} (h : FHolds img s B) :
    ∀ o, FHolds img s (meetOpt B o)
  | none => h.reset
  | some _ => h.meet_right

theorem meetOpt_right {s : Prover.Exec.St} {B A : FSt} (h : FHolds img s A) :
    FHolds img s (meetOpt B (some A)) := h.meet_left

/-- A state that holds where one of the groups into `i` does. -/
def PopHolds (s : Prover.Exec.St) (o : Option FSt) : Prop := ∃ A, o = some A ∧ FHolds img s A

theorem popF_cov {ar : Exec.Trie (List ℕ)} {s : Prover.Exec.St} {i : ℕ} :
    ∀ {P : FPend}, PendOkF ar P i → CovF img s P i → PopHolds (img := img) s (popF i P).1
  | [], _, ⟨_, hG, _⟩ => absurd hG List.not_mem_nil
  | (k, ts, B) :: gs, hP, ⟨G, hG, hj, hH⟩ => by
    rw [popF_cons]
    rcases List.mem_cons.mp hG with rfl | hG
    · obtain ⟨hinc, hge, -⟩ := hP _ (List.mem_cons_self ..)
      rcases ts with _ | ⟨t, ts⟩
      · exact absurd hj List.not_mem_nil
      · have hti : t = i := by
          rcases List.mem_cons.mp hj with h | h
          · exact h.symm
          · have := incrF_lt hinc i h; have := hge t (List.mem_cons_self ..); omega
        dsimp only
        rw [ite_eq_left hti]
        exact ⟨_, rfl, meetOpt_left hH _⟩
    · obtain ⟨A, hA, hHA⟩ := popF_cov hP.cons ⟨G, hG, hj, hH⟩
      rcases ts with _ | ⟨t, ts⟩
      · exact ⟨A, hA, hHA⟩
      · dsimp only
        split_ifs
        · exact ⟨_, rfl, by rw [hA]; exact meetOpt_right hHA⟩
        · exact ⟨_, rfl, by rw [hA]; exact meetOpt_right hHA⟩
        · exact ⟨A, hA, hHA⟩

theorem popF_sub (i : ℕ) (g : ℕ × List ℕ × FSt) (gs : FPend) :
    ∀ X ∈ (popF i gs).2, X ∈ (popF i (g :: gs)).2 := fun X hX ↦ by
  obtain ⟨k, ts, B⟩ := g
  rw [popF_cons]
  rcases ts with _ | ⟨t, ts⟩
  · exact hX
  · dsimp only
    split_ifs
    · exact hX
    · exact List.mem_cons_of_mem _ hX
    · exact List.mem_cons_of_mem _ hX

theorem popF_keep {s : Prover.Exec.St} {i j : ℕ} (hji : j ≠ i) : ∀ {P : FPend}, CovF img s P j →
    CovF img s (popF i P).2 j
  | [], ⟨_, hG, _⟩ => absurd hG List.not_mem_nil
  | (k, ts, B) :: gs, ⟨G, hG, hj, hH⟩ => by
    rcases List.mem_cons.mp hG with rfl | hG
    · rw [popF_cons]
      rcases ts with _ | ⟨t, ts⟩
      · exact absurd hj List.not_mem_nil
      · dsimp only
        split_ifs with ht hts
        · have hj' : j ∈ ts := by
            rcases List.mem_cons.mp hj with h | h
            · omega
            · exact h
          rw [hts] at hj'; exact absurd hj' List.not_mem_nil
        · have hj' : j ∈ ts := by
            rcases List.mem_cons.mp hj with h | h
            · omega
            · exact h
          exact ⟨_, List.mem_cons_self .., hj', hH⟩
        · exact ⟨_, List.mem_cons_self .., hj, hH⟩
    · obtain ⟨G', hG', hj', hH'⟩ := popF_keep hji ⟨G, hG, hj, hH⟩
      exact ⟨G', popF_sub i _ gs G' hG', hj', hH'⟩

theorem popF_ok {ar : Exec.Trie (List ℕ)} {i : ℕ} : ∀ {P : FPend}, PendOkF ar P i →
    PendOkF ar (popF i P).2 (i + 1)
  | [], _ => fun _ h ↦ absurd h List.not_mem_nil
  | (k, ts, B) :: gs, hP => by
    have ih := popF_ok hP.cons
    obtain ⟨hinc, hge, htag⟩ := hP _ (List.mem_cons_self ..)
    rw [popF_cons]
    rcases ts with _ | ⟨t, ts⟩
    · exact ih
    · dsimp only
      split_ifs with ht hts
      · exact ih
      · intro G hG
        rcases List.mem_cons.mp hG with rfl | hG
        · exact ⟨incrF_tail hinc, fun u hu ↦ by have := incrF_lt hinc u hu; omega, fun h ↦ absurd rfl h⟩
        · exact ih G hG
      · intro G hG
        rcases List.mem_cons.mp hG with rfl | hG
        · refine ⟨hinc, fun u hu ↦ ?_, htag⟩
          have h0 := hge t (List.mem_cons_self ..)
          rcases List.mem_cons.mp hu with rfl | hu
          · omega
          · have := incrF_lt hinc u hu; omega
        · exact ih G hG

/-- **The join**: where the live path or a group into `i` holds, the joined path does. -/
theorem joinF_holds {ar : Exec.Trie (List ℕ)} {s : Prover.Exec.St} {i : ℕ} {cur : Option FSt}
    {pend : FPend} (hP : PendOkF ar pend i)
    (h : (∃ A, cur = some A ∧ FHolds img s A) ∨ CovF img s pend i) :
    ∃ A, (joinF i cur pend).1 = some A ∧ FHolds img s A := by
  unfold joinF
  rcases e : popF i pend with ⟨_ | P, ps⟩
  · dsimp only
    rcases h with h | h
    · exact h
    · obtain ⟨A, hA, -⟩ := popF_cov hP h
      rw [e] at hA; cases hA
  · dsimp only
    rcases h with ⟨A, rfl, hA⟩ | h
    · exact ⟨_, rfl, hA.meet_left⟩
    · obtain ⟨A, hA, hHA⟩ := popF_cov hP h
      rw [e] at hA; cases hA
      rcases cur with _ | A'
      · exact ⟨_, rfl, hHA⟩
      · exact ⟨_, rfl, hHA.meet_right⟩

theorem joinF_pend (i : ℕ) (cur : Option FSt) (pend : FPend) : (joinF i cur pend).2 = (popF i pend).2 := by
  unfold joinF
  rcases popF i pend with ⟨_ | P, ps⟩ <;> rfl

/-! ### Adding a group -/

/-- Where the tags agree, the targets do: untagged, equal; tagged, the same table's. -/
def SameTargets (ar : Exec.Trie (List ℕ)) (k : ℕ) (ts : List ℕ) : Prop :=
  k ≠ 0 → ar.get (k - 1) = some ts

theorem addGrpF_cons (k : ℕ) (ts : List ℕ) (A : FSt) (k' : ℕ) (us : List ℕ) (B : FSt) (gs : FPend) :
    addGrpF k ts A ((k', us, B) :: gs) =
      if (bif k == 0 then ts == us else k == k') then (k', us, B.meet A) :: gs
      else (k', us, B) :: addGrpF k ts A gs := by
  conv_lhs => unfold addGrpF
  split_ifs
  · rw [FSt.force_eq]
  · rw [Exec.headSeq_eq]

theorem addGrpF_keep (k : ℕ) (ts : List ℕ) (A : FSt) : ∀ (P : FPend), PendLeF img P (addGrpF k ts A P)
  | [] => fun _ _ h ↦ by obtain ⟨_, hG, _⟩ := h; exact absurd hG List.not_mem_nil
  | (k', us, B) :: gs => fun s j ⟨G, hG, hj, hH⟩ ↦ by
    rw [addGrpF_cons]
    split_ifs
    · rcases List.mem_cons.mp hG with rfl | hG
      · exact ⟨_, List.mem_cons_self .., hj, hH.meet_left⟩
      · exact ⟨G, List.mem_cons_of_mem _ hG, hj, hH⟩
    · rcases List.mem_cons.mp hG with rfl | hG
      · exact ⟨_, List.mem_cons_self .., hj, hH⟩
      · obtain ⟨G', hG', hj', hH'⟩ := addGrpF_keep k ts A gs s j ⟨G, hG, hj, hH⟩
        exact ⟨G', List.mem_cons_of_mem _ hG', hj', hH'⟩

theorem addGrpF_new {ar : Exec.Trie (List ℕ)} {s : Prover.Exec.St} {k : ℕ} {ts : List ℕ} {A : FSt}
    (hA : FHolds img s A) (hk : SameTargets ar k ts) {j : ℕ} (hj : j ∈ ts) {m : ℕ} :
    ∀ {P : FPend}, PendOkF ar P m → CovF img s (addGrpF k ts A P) j
  | [], _ => ⟨_, List.mem_singleton_self _, hj, hA⟩
  | (k', us, B) :: gs, hP => by
    rw [addGrpF_cons]
    split_ifs with he
    · have hus : ts = us := by
        by_cases hk0 : k = 0
        · rw [hk0] at he; simpa using he
        · have hkk : k = k' := by simpa [hk0] using he
          obtain ⟨-, -, htag⟩ := hP _ (List.mem_cons_self ..)
          have h1 := hk hk0
          rw [hkk, htag (hkk ▸ hk0)] at h1
          exact (Option.some.inj h1).symm
      subst hus
      exact ⟨_, List.mem_cons_self .., hj, hA.meet_right⟩
    · obtain ⟨G', hG', hj', hH'⟩ := addGrpF_new hA hk hj hP.cons
      exact ⟨G', List.mem_cons_of_mem _ hG', hj', hH'⟩

theorem addGrpF_ok {ar : Exec.Trie (List ℕ)} {k : ℕ} {ts : List ℕ} {A : FSt} {m : ℕ}
    (hinc : incrF ts = true) (hge : ∀ t ∈ ts, m ≤ t) (hk : SameTargets ar k ts) :
    ∀ {P : FPend}, PendOkF ar P m → PendOkF ar (addGrpF k ts A P) m
  | [], _ => fun G hG ↦ by rcases List.mem_singleton.mp hG with rfl; exact ⟨hinc, hge, hk⟩
  | (k', us, B) :: gs, hP => by
    rw [addGrpF_cons]
    split_ifs
    · intro G hG
      rcases List.mem_cons.mp hG with rfl | hG
      · exact hP (k', us, B) List.mem_cons_self
      · exact hP G (List.mem_cons_of_mem _ hG)
    · intro G hG
      rcases List.mem_cons.mp hG with rfl | hG
      · exact hP (k', us, B) List.mem_cons_self
      · exact addGrpF_ok hinc hge hk hP.cons G hG

theorem tagF_arms {Fn : FFun} {i : ℕ} {A : FSt} {x : Exec.Exit} {ts : List ℕ} {B : FSt}
    (e : exitF Fn i A x = some (ts, B)) (hk : tagF Fn i x ≠ 0) : Fn.arms.get (tagF Fn i x - 1) = some ts := by
  unfold tagF at hk ⊢
  rcases hx : x.kind with t | _ | ⟨pt, q, r⟩ | ⟨pt, ft⟩
  · simp [hx] at hk
  · simp [hx] at hk
  · simp [hx] at hk
  · rcases pt with e' | e' | o
    · simp [hx] at hk
    · simp [hx] at hk
    · simp only [hx] at hk ⊢
      by_cases hself : Fn.F.self ft = true
      · rcases hk' : Fn.tgt.get i with _ | k
        · simp [hself, hk'] at hk
        · simp only [hself, Nat.add_sub_cancel, ite_true]
          have e' : jumpExF Fn i A (.cell o) ft = some (ts, B) := by unfold exitF at e; rw [hx] at e; exact e
          unfold jumpExF at e'
          simp only [hself, ite_true, hk'] at e'
          obtain ⟨ts', hts', he⟩ := Option.map_eq_some_iff.mp e'
          cases he
          exact hts'
      · simp [hself] at hk

/-- **A taken jump's edges**: the exit the walk accepts, its groups added. -/
theorem jumpF_spec {Fn : FFun} (har : armsOk Fn = true) {i : ℕ} {A : FSt} {x : Exec.Exit}
    {pend pend' : FPend} (h : jumpF Fn i A x pend = some pend') :
    ∃ ts B, exitF Fn i A x = some (ts, B) ∧ PendLeF img pend pend' ∧
      (PendOkF Fn.arms pend (i + 1) →
        (∀ s j, j ∈ ts → FHolds img s B → CovF img s pend' j) ∧ PendOkF Fn.arms pend' (i + 1)) := by
  unfold jumpF at h
  rcases e : exitF Fn i A x with _ | ⟨_ | ⟨t, ts⟩, B⟩
  · rw [e] at h; cases h
  · rw [e] at h; cases h
    exact ⟨[], B, rfl, fun _ _ h ↦ h, fun hP ↦ ⟨fun _ _ hj ↦ absurd hj List.not_mem_nil, hP⟩⟩
  · rw [e] at h
    dsimp only at h
    split_ifs at h with hc
    cases h
    rw [FSt.force_eq]
    have hst : SameTargets Fn.arms (tagF Fn i x) (t :: ts) := fun hk ↦ tagF_arms e hk
    have hti : incrF (t :: ts) = true ∧ ∀ u ∈ t :: ts, i + 1 ≤ u := by
      by_cases hk : tagF Fn i x = 0
      · rw [hk] at hc
        simp only [beq_self_eq_true, Bool.cond_true, Bool.and_eq_true] at hc
        exact ⟨hc.2, fun u hu ↦ by have := List.all_eq_true.mp hc.1 u hu; simp at this; omega⟩
      · have hkk : (tagF Fn i x == 0) = false := by simpa using hk
        rw [hkk] at hc
        simp only [Bool.cond_false, decide_eq_true_eq] at hc
        have hinc := (Bool.and_eq_true _ _ ▸ Exec.trieAll_get har (hst hk)).1
        exact ⟨hinc, fun u hu ↦ by
          rcases List.mem_cons.mp hu with rfl | hu
          · omega
          · have := incrF_lt hinc u hu; omega⟩
    exact ⟨t :: ts, B, rfl, addGrpF_keep _ (t :: ts) B pend, fun hP ↦
      ⟨fun s j hj hB ↦ addGrpF_new hB hst hj hP, addGrpF_ok hti.1 hti.2 hst hP⟩⟩

end Pend

/-! ## Offset by offset -/

section Off

variable {κ : ℕ} (img : MemoryImage κ)

/-- The live path and pending groups before offset `i`. -/
noncomputable def preF (Fn : FFun) (code : List OffsetInstruction) (i : ℕ) : Option (Option FSt × FPend) :=
  frameRunH Fn (code.take i) 0 (some (entryF Fn)) []

/-- **A state at offset `i`**: the live path the walk has there holds, or a pending group into it
does. -/
def AtF (Fn : FFun) (code : List OffsetInstruction) (i : ℕ) (s : Prover.Exec.St) : Prop :=
  ∃ cur pend, preF Fn code i = some (cur, pend) ∧
    ((∃ A, cur = some A ∧ FHolds img s A) ∨ CovF img s pend i)

variable {img}

/-- The walk's pass from its entry state: `frameOk`'s, with the hints by pc. -/
def FrameAcc (Fn : FFun) (code : List OffsetInstruction) : Prop :=
  frameRunH Fn code 0 (some (entryF Fn)) [] = some (none, [])

theorem frameAcc_of {Fn : FFun} {code : List OffsetInstruction} (hd : Mode.pcsIncr Fn.hints = true)
    (h : frameOk Fn code = true) : envOk Fn = true ∧ armsOk Fn = true ∧ FrameAcc Fn code := by
  unfold frameOk at h
  simp only [Bool.and_eq_true] at h
  refine ⟨h.1.1, h.1.2, ?_⟩
  unfold FrameAcc
  rw [← frameRun_eq hd code 0 Fn.hints _ _ ⟨hd, fun _ hx ↦ hx, fun _ hx _ ↦ hx⟩]
  split at h
  · rename_i e; exact e
  · cases h.2

theorem preF_succ {Fn : FFun} {code : List OffsetInstruction} {i : ℕ} (hi : i < code.length) :
    preF Fn code (i + 1) = (preF Fn code i).bind fun S ↦ frameRunH Fn [code[i]] i S.1 S.2 := by
  unfold preF
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, frameRunH_append,
    List.length_take, Nat.zero_add, Nat.min_eq_left hi.le]

theorem preF_isSome {Fn : FFun} {code : List OffsetInstruction} (hw : FrameAcc Fn code) (i : ℕ) :
    ∃ S, preF Fn code i = some S := by
  unfold FrameAcc at hw
  rw [← List.take_append_drop i code, frameRunH_append] at hw
  obtain ⟨S, hS, -⟩ := Option.bind_eq_some_iff.mp hw
  exact ⟨S, hS⟩

theorem preF_end {Fn : FFun} {code : List OffsetInstruction} (hw : FrameAcc Fn code)
    {i : ℕ} (hi : code.length ≤ i) {cur : Option FSt} {pend : FPend}
    (h : preF Fn code i = some (cur, pend)) : cur = none ∧ pend = [] := by
  unfold FrameAcc at hw
  unfold preF at h
  rw [List.take_of_length_le hi] at h
  rw [h] at hw
  cases hw
  exact ⟨rfl, rfl⟩

theorem frameRunH_one (Fn : FFun) (ins : OffsetInstruction) (i : ℕ) (cur : Option FSt) (pend : FPend) :
    frameRunH Fn [ins] i cur pend = passH Fn ins (fun _ cur pend ↦ some (cur, pend)) i cur pend := rfl

/-- What one offset of the pass does: the cut, the join, the step. -/
theorem passH_cases {Fn : FFun} {ins : OffsetInstruction} {i : ℕ} {cur : Option FSt} {pend : FPend}
    {cur' : Option FSt} {pend' : FPend}
    (h : passH Fn ins (fun _ cur pend ↦ some (cur, pend)) i cur pend = some (cur', pend')) :
    ∃ c1 p1, cutF Fn i cur pend = some (c1, p1) ∧
      (((joinF i c1 p1).1 = none ∧ cur' = none ∧ pend' = (joinF i c1 p1).2) ∨
       ∃ A, (joinF i c1 p1).1 = some A ∧
         offF Fn i (Mode.hintsAt Fn.hints (Fn.entry + i)) A ins (joinF i c1 p1).2 = some (cur', pend')) := by
  unfold passH at h
  rcases e : cutF Fn i cur pend with _ | ⟨c1, p1⟩
  · rw [e] at h; cases h
  · rw [e] at h
    dsimp only at h
    refine ⟨c1, p1, rfl, ?_⟩
    rcases ej : joinF i c1 p1 with ⟨_ | A, p⟩
    · rw [ej] at h
      cases h
      exact Or.inl ⟨rfl, rfl, rfl⟩
    · rw [ej] at h
      dsimp only at h
      rcases eo : offF Fn i (Mode.hintsAt Fn.hints (Fn.entry + i)) A ins p with _ | ⟨c2, p2⟩
      · rw [eo] at h; cases h
      · rw [eo] at h; cases h
        exact Or.inr ⟨A, rfl, eo⟩

theorem pendSub_cov {s : Prover.Exec.St} {j : ℕ} : ∀ {S P : FPend}, pendSub S P = true →
    CovF img s P j → CovF img s (S.map fun g ↦ (g.1, g.2.1, g.2.2.reset)) j
  | [], [], _, ⟨_, hG, _⟩ => absurd hG List.not_mem_nil
  | [], _ :: _, h, _ => by cases h
  | _ :: _, [], h, _ => by cases h
  | (k, ts, S) :: ss, (k', us, T) :: tt, h, ⟨G, hG, hj, hH⟩ => by
    simp only [pendSub, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨rfl, rfl⟩, hst⟩, hrest⟩ := h
    rcases List.mem_cons.mp hG with rfl | hG
    · exact ⟨_, List.mem_cons_self .., hj, hH.sub hst⟩
    · obtain ⟨G', hG', hj', hH'⟩ := pendSub_cov hrest ⟨G, hG, hj, hH⟩
      exact ⟨G', List.mem_cons_of_mem _ hG', hj', hH'⟩

theorem pendSub_ok {ar : Exec.Trie (List ℕ)} {m : ℕ} : ∀ {S P : FPend}, pendSub S P = true →
    PendOkF ar P m → PendOkF ar (S.map fun g ↦ (g.1, g.2.1, g.2.2.reset)) m
  | [], _, _, _ => fun _ h ↦ absurd h List.not_mem_nil
  | _ :: _, [], h, _ => by cases h
  | (k, ts, S) :: ss, (k', us, T) :: tt, h, hP => by
    simp only [pendSub, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨rfl, rfl⟩, -⟩, hrest⟩ := h
    intro G hG
    rcases List.mem_cons.mp hG with rfl | hG
    · exact hP (k, ts, T) List.mem_cons_self
    · exact pendSub_ok hrest hP.cons G hG

/-- A cut keeps what holds. -/
theorem cutF_spec {Fn : FFun} {i : ℕ} {cur c1 : Option FSt} {pend p1 : FPend}
    (h : cutF Fn i cur pend = some (c1, p1)) :
    (∀ s, ((∃ A, cur = some A ∧ FHolds img s A) ∨ CovF img s pend i) →
      ((∃ A, c1 = some A ∧ FHolds img s A) ∨ CovF img s p1 i)) ∧
    PendLeF img pend p1 ∧ (∀ ar k, PendOkF ar pend k → PendOkF ar p1 k) := by
  unfold cutF at h
  split at h
  · rename_i c hc
    split_ifs at h with hsub
    cases h
    simp only [Bool.and_eq_true] at hsub
    obtain ⟨hcur, hpend⟩ := hsub
    refine ⟨fun s hs ↦ ?_, fun s j hc ↦ pendSub_cov hpend hc, fun ar k hk ↦ pendSub_ok hpend hk⟩
    rcases hs with ⟨A, rfl, hH⟩ | hc
    · left
      rcases c with ⟨_ | S, sp⟩
      · cases hcur
      · exact ⟨_, rfl, hH.sub hcur⟩
    · exact Or.inr (pendSub_cov hpend hc)
  · cases h
    exact ⟨fun _ h ↦ h, fun _ _ h ↦ h, fun _ _ h ↦ h⟩

/-- What one path's step does to the pending groups. -/
theorem offF_pend {Fn : FFun} (har : armsOk Fn = true) {i : ℕ} {hs : List Hint} {A : FSt}
    {ins : OffsetInstruction} {pend pend' : FPend} {cur' : Option FSt}
    (h : offF Fn i hs A ins pend = some (cur', pend')) :
    PendLeF img pend pend' ∧ (PendOkF Fn.arms pend (i + 1) → PendOkF Fn.arms pend' (i + 1)) := by
  unfold offF at h
  split at h
  · cases h
  · rename_i A1 _
    dsimp only at h
    split at h
    · rename_i c d f
      split_ifs at h
      rw [Exec.optSeq_eq] at h
      split_ifs at h
      · cases h; exact ⟨fun _ _ h ↦ h, id⟩
      · obtain ⟨p, hp, he⟩ := Option.map_eq_some_iff.mp h
        cases he
        obtain ⟨_, _, _, h1, h2⟩ := jumpF_spec (img := img) har hp
        exact ⟨h1, fun hP ↦ (h2 hP).2⟩
      · obtain ⟨p, hp, he⟩ := Option.map_eq_some_iff.mp h
        cases he
        obtain ⟨_, _, _, h1, h2⟩ := jumpF_spec (img := img) har hp
        exact ⟨h1, fun hP ↦ (h2 hP).2⟩
    · obtain ⟨B, -, he⟩ := Option.map_eq_some_iff.mp h
      cases he
      exact ⟨fun _ _ h ↦ h, id⟩

theorem preF_ok (img : MemoryImage κ) {Fn : FFun} (har : armsOk Fn = true) {code : List OffsetInstruction} :
    ∀ {i : ℕ} {cur : Option FSt} {pend : FPend}, i ≤ code.length → preF Fn code i = some (cur, pend) →
      PendOkF Fn.arms pend i
  | 0, cur, pend, _, h => by
    simp only [preF, List.take_zero, frameRunH, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact fun _ h ↦ absurd h List.not_mem_nil
  | i + 1, cur, pend, hi, h => by
    rw [preF_succ (by omega)] at h
    obtain ⟨⟨c0, p0⟩, h0, h⟩ := Option.bind_eq_some_iff.mp h
    have hP0 := preF_ok img har (by omega) h0
    rw [frameRunH_one] at h
    obtain ⟨c1, p1, hc, hj⟩ := passH_cases h
    have hP1 := (cutF_spec (img := img) hc).2.2 _ i hP0
    have hJ : PendOkF Fn.arms (joinF i c1 p1).2 (i + 1) := by rw [joinF_pend]; exact popF_ok hP1
    rcases hj with ⟨-, -, rfl⟩ | ⟨A, -, ho⟩
    · exact hJ
    · exact (offF_pend (img := img) har ho).2 hJ

/-- **A pending group survives** to its target. -/
theorem covF_forward {Fn : FFun} {code : List OffsetInstruction} (har : armsOk Fn = true)
    (hw : FrameAcc Fn code) {s : Prover.Exec.St} {j : ℕ} : ∀ (d i : ℕ) {cur : Option FSt} {pend : FPend},
      i + d = j → preF Fn code i = some (cur, pend) → CovF img s pend j → AtF img Fn code j s
  | 0, i, cur, pend, hd, h, hc => by
    rw [Nat.add_zero] at hd; subst hd
    exact ⟨cur, pend, h, Or.inr hc⟩
  | d + 1, i, cur, pend, hd, h, hc => by
    by_cases hi : i < code.length
    · obtain ⟨⟨c2, p2⟩, h2⟩ := preF_isSome hw (i + 1)
      have h2' := h2
      rw [preF_succ hi, h, Option.bind_some, frameRunH_one] at h2'
      obtain ⟨c1, p1, hcut, hj⟩ := passH_cases h2'
      have hc1 := (cutF_spec (img := img) hcut).2.1 s j hc
      have hc2 : CovF img s (joinF i c1 p1).2 j := by rw [joinF_pend]; exact popF_keep (by omega) hc1
      have hc3 : CovF img s p2 j := by
        rcases hj with ⟨-, -, rfl⟩ | ⟨A, -, ho⟩
        · exact hc2
        · exact (offF_pend (img := img) har ho).1 s j hc2
      exact covF_forward har hw d (i + 1) (by omega) h2 hc3
    · obtain ⟨G, hG, -⟩ := hc
      rw [(preF_end hw (by omega) h).2] at hG
      exact absurd hG List.not_mem_nil

/-- **The entry**: the entry state holds at offset `0`. -/
theorem atF_zero {Fn : FFun} {code : List OffsetInstruction} {s : Prover.Exec.St}
    (h : FHolds img s (entryF Fn)) : AtF img Fn code 0 s :=
  ⟨some (entryF Fn), [], by simp [preF, frameRunH], Or.inl ⟨_, rfl, h⟩⟩

/-- **One offset**: at an offset the walk accepts, the joined path holds and its step goes
through; what falls through holds at the next offset, and a group the step adds holds at its
targets. -/
theorem atF_step {Fn : FFun} {code : List OffsetInstruction} (har : armsOk Fn = true)
    (hw : FrameAcc Fn code) {i : ℕ} (hi : i < code.length) {s : Prover.Exec.St}
    (h : AtF img Fn code i s) :
    ∃ A, FHolds img s A ∧ ∃ pa cur' pb,
      offF Fn i (Mode.hintsAt Fn.hints (Fn.entry + i)) A code[i] pa = some (cur', pb) ∧
      PendOkF Fn.arms pa (i + 1) ∧
      (∀ s', (∃ X, cur' = some X ∧ FHolds img s' X) → AtF img Fn code (i + 1) s') ∧
      ∀ s' j, CovF img s' pb j → AtF img Fn code j s' := by
  obtain ⟨cur, pend, h0, hh⟩ := h
  obtain ⟨⟨c2, p2⟩, h2⟩ := preF_isSome hw (i + 1)
  have h2' := h2
  rw [preF_succ hi, h0, Option.bind_some, frameRunH_one] at h2'
  obtain ⟨c1, p1, hcut, hj⟩ := passH_cases h2'
  have hP := preF_ok img har (by omega) h0
  obtain ⟨hc1, -, hc3⟩ := cutF_spec (img := img) hcut
  have hP1 := hc3 _ i hP
  obtain ⟨A, hA, hH⟩ := joinF_holds hP1 (hc1 s hh)
  have hJ : PendOkF Fn.arms (joinF i c1 p1).2 (i + 1) := by rw [joinF_pend]; exact popF_ok hP1
  have hP2 := preF_ok img har (by omega) h2
  rcases hj with ⟨hn, -, -⟩ | ⟨A', hA', ho⟩
  · rw [hA] at hn; cases hn
  rw [hA] at hA'; cases hA'
  refine ⟨A, hH, _, c2, p2, ho, hJ, fun s' hX ↦ ⟨c2, p2, h2, Or.inl hX⟩, fun s' j hc ↦ ?_⟩
  obtain ⟨G, hG, hjG, -⟩ := id hc
  have hij := (hP2 G hG).2.1 j hjG
  exact covF_forward har hw (j - (i + 1)) (i + 1) (by omega) h2 hc

/-- **The walk's state at offset `i`**: the live path and the groups into `i`, cut and joined (`atF_step`'s). -/
noncomputable def retSt (Fn : FFun) (code : List OffsetInstruction) (i : ℕ) : Option FSt :=
  match preF Fn code i with
  | some (cur, pend) => match cutF Fn i cur pend with
    | some (c1, p1) => (joinF i c1 p1).1
    | none => none
  | none => none

/-- **The state at an offset holds** (`retSt`), at a state the walk reaches there. -/
theorem atF_ret {Fn : FFun} {code : List OffsetInstruction} (har : armsOk Fn = true)
    (hw : FrameAcc Fn code) {i : ℕ} (hi : i < code.length) {s : Prover.Exec.St}
    (h : AtF img Fn code i s) : ∃ A, retSt Fn code i = some A ∧ FHolds img s A := by
  obtain ⟨cur, pend, h0, hh⟩ := h
  obtain ⟨⟨c2, p2⟩, h2⟩ := preF_isSome hw (i + 1)
  rw [preF_succ hi, h0, Option.bind_some, frameRunH_one] at h2
  obtain ⟨c1, p1, hcut, -⟩ := passH_cases h2
  have hP := preF_ok img har (by omega) h0
  obtain ⟨hc1, -, hc3⟩ := cutF_spec (img := img) hcut
  obtain ⟨A, hA, hH⟩ := joinF_holds (hc3 _ i hP) (hc1 s hh)
  refine ⟨A, ?_, hH⟩
  unfold retSt
  rw [h0]
  dsimp only
  rw [hcut]
  exact hA

end Off

end

end LeanVM.Guest.CoreMode
