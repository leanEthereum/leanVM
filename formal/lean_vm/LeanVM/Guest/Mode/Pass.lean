module

public import LeanVM.Guest.Mode.SoundJoin
public import LeanVM.Guest.Mode.Win

/-!
# The pass, offset by offset

What the walk's pass has before offset `i` of a function (`preAt`, the run of the code's first `i`
instructions), and a state of the executor at the offset when one of its paths holds there or a
pending edge into the offset does (`AtOff`, `Cov`); `PendOk`, a pending edge's groups' targets
increasing.
-/

namespace LeanVM.Guest.Mode

open LeanVM.Guest
open LeanVM.Prover.Exec (St)

@[expose] public section

/-- Some group of `P` enters offset `j` with a state that holds at `s`. -/
def Cov (s : St) (P : Pend) (j : ℕ) : Prop := ∃ G ∈ P, j ∈ G.ts ∧ ∃ B ∈ G.Bs, Holds s B

/-- Every group's targets increase, from `k` on. -/
def PendOk (P : Pend) (k : ℕ) : Prop := ∀ G ∈ P, incr G.ts = true ∧ ∀ t ∈ G.ts, k ≤ t

/-- Every edge of `P` is one of `Q`'s. -/
def PendLe (P Q : Pend) : Prop := ∀ s j, Cov s P j → Cov s Q j

theorem PendLe.refl (P : Pend) : PendLe P P := fun _ _ h ↦ h

theorem PendLe.trans {P Q R : Pend} (h1 : PendLe P Q) (h2 : PendLe Q R) : PendLe P R :=
  fun s j h ↦ h2 s j (h1 s j h)

/-- The paths and pending edges before offset `i`. -/
noncomputable def preAt (E : Env) (F : Fun) (code : List OffsetInstruction) (i : ℕ) :
    Option (List Abs × Pend) :=
  runCode E F (code.take i) 0 [entryAbs E F.sig] []

/-- **A state at offset `i`**: a path the walk has there holds, or a pending edge into it does. -/
def AtOff (E : Env) (F : Fun) (code : List OffsetInstruction) (i : ℕ) (s : St) : Prop :=
  ∃ cur pend, preAt E F code i = some (cur, pend) ∧ ((∃ A ∈ cur, Holds s A) ∨ Cov s pend i)

/-! ## Increasing targets -/

theorem PendOk.cons {G : Grp} {P : Pend} {k : ℕ} (h : PendOk (G :: P) k) : PendOk P k :=
  fun G' hG' ↦ h G' (List.mem_cons_of_mem _ hG')

/-! ## Cuts -/

theorem pendSub_ok {k : ℕ} : ∀ {S P : Pend}, pendSub S P = true → PendOk P k → PendOk S k
  | [], [], _, _ => fun _ h ↦ absurd h List.not_mem_nil
  | S :: Ss, G :: Gs, h, hP => by
    simp only [pendSub, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨hts, -⟩, -⟩, hrest⟩ := h
    intro X hX
    rcases List.mem_cons.mp hX with rfl | hX
    · rw [hts]; exact hP G (List.mem_cons_self ..)
    · exact pendSub_ok hrest hP.cons X hX
  | [], _ :: _, h, _ => by simp [pendSub] at h
  | _ :: _, [], h, _ => by simp [pendSub] at h

end

end LeanVM.Guest.Mode
