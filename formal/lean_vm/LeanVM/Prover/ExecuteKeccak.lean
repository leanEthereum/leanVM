module

public import LeanVM.Prover.ExecuteOp
import Mathlib.Data.List.Forall2

/-!
# The executor's `KECCAK` is a step

`keccak_spec`: the thirteen cells the executor reads are the instruction's input cells
(`readCells`), the cells it writes its first output cells (`readFirstCells`), and what it writes
there is the permutation of what it read, so `KeccakCellsRelation` holds. The permutation's value is
generalized away at once, never evaluated.
-/

namespace LeanVM.Prover.Exec

open LeanVM.Parameters LeanVM.Semantics

@[expose] public section

theorem exMapM_ok {ε α β : Type} (f : α → Except ε β) :
    ∀ (l : List α) (l' : List β), l.mapM f = .ok l' → List.Forall₂ (fun a b ↦ f a = .ok b) l l'
  | [], l', h => by simp only [List.mapM_nil, pure_ok] at h; subst h; exact .nil
  | a :: l, l', h => by
    simp only [List.mapM_cons, bind_ok, pure_ok] at h
    obtain ⟨b, hb, bs, hbs, rfl⟩ := h
    exact .cons hb (exMapM_ok f l bs hbs)

theorem forall₂_getElem {α β : Type} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) {i : ℕ} (h₁ : i < l₁.length) (h₂ : i < l₂.length) :
    R l₁[i] l₂[i] := by
  have := (List.forall₂_iff_get.mp h).2 i h₁ h₂
  simp only [List.get_eq_getElem] at this
  exact this

theorem guard_some {p : Prop} [Decidable p] (hp : p) : guard p = some () := by
  simp [guard, hp]

theorem keccak_spec {C : Ctx} {s s' : St} {om : Fin 4 → K} {otail ob8 ocap : K}
    {outCells : KeccakOutputCells} {L : List ℕ} {out : ℕ} {inOdd outOdd : Bool} (hs : s.Good)
    (hfp : s.fp < maxCells) (hpc : s.pc < C.ops.size)
    (hL : List.Forall₂ (fun c k ↦ g ^ k = keccakInputCellOffset om otail ob8 ocap c)
      (List.finRange 13) L)
    (e : runOp C s (.keccak L.toArray out inOdd outOdd outCells.cellCount) = .ok s') :
    OpSpec (.keccak om otail ob8 ocap (g ^ out) inOdd outOdd outCells) C.ops.size s s' := by
  simp only [runOp, bind_ok] at e
  obtain ⟨cells, hcells, input, hinput, outs, houts, s1, hs1, e⟩ := e
  simp only [pure_ok] at e; subst e
  generalize hO : cellsOfState (keccakF1600 (stateOfCells (fun c : Fin 13 ↦ input.getD c.val 0)
    inOdd)) outOdd = O at hs1
  obtain ⟨m, hm, rfl⟩ := St.withMem_ok hs1
  rw [bind_ok] at hm
  obtain ⟨m1, hm1, hm⟩ := hm
  simp only [pure_ok] at hm; subst hm
  obtain ⟨hle1, hwf1, hputs⟩ := Mem.foldlM_ok _
    (fun (x : ℕ × ℕ) (m : Mem) ↦ m.get x.1 = some (O ⟨x.2 % 13, Nat.mod_lt x.2 (by decide)⟩))
    (fun _ _ _ h hle ↦ hle.get _ _ h) (fun _ _ _ hm h ↦ Mem.put_ok hm h) outs.zipIdx s.mem m1
    hs.wf hm1
  obtain ⟨hle2, hwf2⟩ := Mem.foldl_ensure (cells ++ outs) m1 hwf1
  refine ⟨⟨hwf2, hs.dl⟩, Mem.le_trans hle1 hle2, rfl, hpc, hfp, ?_⟩
  intro M rd hM hF
  have hc := exMapM_ok _ _ _ hcells
  have hi := exMapM_ok _ _ _ hinput
  have ho := exMapM_ok _ _ _ houts
  have hlL : L.length = 13 := by rw [← hL.length_eq, List.length_finRange]
  have hlc : cells.length = 13 := by rw [← hc.length_eq, hlL]
  have hli : input.length = 13 := by rw [← hi.length_eq, hlc]
  have hlo : outs.length = outCells.cellCount := by rw [← ho.length_eq, List.length_range]
  have hrin : ∀ c : Fin 13,
      rd (g ^ s.fp * keccakInputCellOffset om otail ob8 ocap c) = some (input.getD c.val 0) := by
    intro c
    have h1 := forall₂_getElem hL (i := c.val) (by simp) (by rw [hlL]; exact c.isLt)
    have h2 := forall₂_getElem hc (i := c.val) (by rw [hlL]; exact c.isLt)
      (by rw [hlc]; exact c.isLt)
    have h3 := forall₂_getElem hi (i := c.val) (by rw [hlc]; exact c.isLt)
      (by rw [hli]; exact c.isLt)
    simp only [List.getElem_finRange, Fin.cast_mk] at h1
    rw [← h1, ← pow_add, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by rw [hli]; exact c.isLt), Option.getD_some]
    obtain ⟨h4, -⟩ := cellAt_ok h2
    rw [h4] at h3
    exact hF.get (Mem.le_trans hle1 (Mem.le_trans hle2 hM)) (Mem.read_ok h3)
  have hrout : ∀ c : Fin 13, c.val < outCells.cellCount →
      rd (g ^ s.fp * (g ^ c.val * g ^ out)) = some (O c) := by
    intro c hcc
    have h2 := forall₂_getElem ho (i := c.val) (by rw [List.length_range]; exact hcc)
      (by rw [hlo]; exact hcc)
    simp only [List.getElem_range] at h2
    obtain ⟨h4, -⟩ := cellAt_ok h2
    have hmem : (outs[c.val]'(by rw [hlo]; exact hcc), c.val) ∈ outs.zipIdx :=
      List.mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem _)
    have h5 := hputs _ hmem
    have hfin : (⟨c.val % 13, Nat.mod_lt _ (by decide)⟩ : Fin 13) = c :=
      Fin.ext (Nat.mod_eq_of_lt c.isLt)
    dsimp only at h5
    rw [hfin, h4] at h5
    rw [← pow_add, ← pow_add, Nat.add_comm c.val out]
    exact hF.get (Mem.le_trans hle2 hM) h5
  obtain ⟨inp, hrc, hinp⟩ : ∃ inp,
      readCells rd (g ^ s.fp) (keccakInputCellOffset om otail ob8 ocap) = some inp ∧
        inp = fun c : Fin 13 ↦ input.getD c.val 0 :=
    ⟨_, (readCells_eq_some_iff _ _ _ _).mpr hrin, rfl⟩
  obtain ⟨f, hrf, hf⟩ : ∃ f, readFirstCells rd (g ^ s.fp) (fun c ↦ g ^ c.val * g ^ out)
      outCells.cellCount = some f ∧ ∀ c : Fin 13, c.val < outCells.cellCount → f c = O c := by
    refine ⟨fun c ↦ if c.val < outCells.cellCount then O c else 0,
      (readFirstCells_eq_some_iff _ _ _ _ _).mpr ⟨fun c hcc ↦ ?_, fun c hcc ↦ ?_⟩,
      fun c hcc ↦ ite_eq_left hcc⟩
    · rw [ite_eq_left hcc]; exact hrout c hcc
    · exact ite_eq_right (by omega)
  have hrel : KeccakCellsRelation inp inOdd f outOdd outCells := by
    intro c hcc
    rw [hf c hcc, hinp, hO]
  simp only [executeWith, hrc, hrf, guard_some hrel, Option.pure_def, next_gpow,
    Option.bind_eq_bind, Option.bind_some]

end

end LeanVM.Prover.Exec
