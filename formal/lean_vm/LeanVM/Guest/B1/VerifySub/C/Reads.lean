/-
  LeanVM.Guest.B1.VerifySub.C.Reads

  `verify_sub`'s announced words (G:3344-3356), honestly: the eight words read from the stream and
  packed, the six row counts stored in `table_rows`, the first four absorbed.
-/

module

public import LeanVM.Guest.B1.VerifySub.C.Head
public import LeanVM.Guest.B1.VerifySub.Front
public import LeanVM.Guest.B1.KeccakGkr.FsComplete

/-!
# The announced words, honestly

`vsReadsT_complete`: with the stream's first eight words `ws` in memory at `stream` (`27`), the
row counts `ws[1 .. 6]` at `table_rows` (`28`, the stores), and the seed's capacity cells
(`22 .. 26`) canonical, the honest valuation reads `ws` into the words `vsX i`, and `vsReadsT`
holds.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Tables

@[expose] public section

/-- A statement other than an `assertNe`. -/
def noNeB : Stmt → Bool
  | .atom (.assertNe _ _ _) => false
  | _ => true

theorem fixNe_of_noNe {s : Stmt} (h : noNeB s = true) : fixNe s = s := by
  cases s with
  | atom a => cases a <;> simp_all [noNeB, fixNe]
  | _ => rfl

theorem vsReadsT_noNe : vsReadsT.all noNeB = true := by decide +kernel

variable {rd : Reader} {w : ℕ → E} {args : List E}

theorem vsReadsT_good (hl : args.length = 6) :
    ∀ s ∈ vsReadsT, GoodS rd vsSL w (vsσ rd w args) s := by
  intro s hs
  have h := vs_goodS (rd := rd) (w := w) hl (vs_mem_slice (n := 10) (blk := vsReadsT)
    (by decide +kernel) hs)
  rwa [fixNe_of_noNe (List.all_eq_true.mp vsReadsT_noNe s hs)] at h

theorem vsReadsT_notS : ∀ i < 8, Atom.load (.n (vsX i)) (.n 25) i ∉ vsSL := by decide +kernel

theorem vsReadsT_sub : ∀ i < 8, ∀ s ∈ fsNextT (.n 25) i (vsX i), s ∈ vsReadsT := by
  intro i hi s hs
  interval_cases i <;>
    simp only [vsX, List.getD_cons_zero, List.getD_cons_succ] at hs <;>
    simp only [vsReadsT, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] <;> tauto

/-- One announced word, honestly: read, packed canonically, its template holding. -/
theorem vs_word (hl : args.length = 6) {ws : List E}
    (hws : ∀ i < 8, LoadHolds rd (vsσ rd w args (.n 25)) i (ws.getD i 0)) {i : ℕ} (hi : i < 8) :
    vsσ rd w args (.n (vsX i)) = ws.getD i 0 ∧
      IsCanonical128 (vsσ rd w args (.n (vsX i + 7))) ∧
      IsCanonical128 (vsσ rd w args (.n (vsX i + 9))) ∧
      ∀ {C : CallRel} {next : Prop} {kret : List E → Prop}, next →
        Stmt.HoldsList C rd (vsσ rd w args) (fsNextT (.n 25) i (vsX i)) next kret := by
  have hG := vsReadsT_good (rd := rd) (w := w) hl
  have hgs : ∀ s ∈ fsNextT (.n 25) i (vsX i), GoodS rd vsSL w (vsσ rd w args) s :=
    fun s hs ↦ hG s (vsReadsT_sub i hi s hs)
  obtain ⟨e, c1, c2, -, -⟩ := fsNext_complete (C := fun _ _ _ ↦ True)
    hgs (vsReadsT_notS i hi) (hws i hi)
  exact ⟨e, c1, c2, fun {C next kret} hn ↦
    (fsNext_complete (C := C) hgs (vsReadsT_notS i hi)
      (hws i hi)).2.2.2.2 hn⟩

set_option maxRecDepth 100000 in
/-- **The announced words, honestly.** -/
theorem vsReadsT_complete (hl : args.length = 6) {ws : List E}
    (hws : ∀ i < 8, LoadHolds rd (vsσ rd w args (.n 25)) i (ws.getD i 0))
    (hrows : ∀ i < 6, LoadHolds rd (vsσ rd w args (.n 26)) i (ws.getD (i + 1) 0))
    (hcap : ∀ i ∈ [20, 21, 22, 23, 24], IsCanonical128 (vsσ rd w args (.n i)))
    {C : CallRel} {next : Prop} {kret : List E → Prop} (hn : next) :
    (∀ i < 8, vsσ rd w args (.n (vsX i)) = ws.getD i 0) ∧
      Stmt.HoldsList C rd (vsσ rd w args) vsReadsT next kret := by
  have W := fun i (hi : i < 8) ↦ vs_word (rd := rd) (w := w) hl hws hi
  have hG := vsReadsT_good (rd := rd) (w := w) hl
  refine ⟨fun i hi ↦ (W i hi).1, ?_⟩
  have st : ∀ j < 6, (Atom.load (.n (vsX (j + 1))) (.n 26) j).Holds rd (vsσ rd w args) := by
    intro j hj
    show LoadHolds rd _ _ _
    rw [(W (j + 1) (by omega)).1]
    exact hrows j hj
  have hk : vsAtom50.Holds rd (vsσ rd w args) := by
    have hm : keccakA [.n 34, .n 36, .n 44, .n 46, .n 54, .n 56, .n 64, .n 66, .n 20, .n 21,
        .n 22, .n 23, .n 24] (vsRun 67 13) ∈ vsReadsT := by
      simp only [vsReadsT, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]; tauto
    have hg := hG _ hm
    simp only [keccakA, GoodS] at hg
    refine keccakA_complete hg ?_
    intro x hx
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (W 0 (by norm_num)).2.1
    · exact (W 0 (by norm_num)).2.2.1
    · exact (W 1 (by norm_num)).2.1
    · exact (W 1 (by norm_num)).2.2.1
    · exact (W 2 (by norm_num)).2.1
    · exact (W 2 (by norm_num)).2.2.1
    · exact (W 3 (by norm_num)).2.1
    · exact (W 3 (by norm_num)).2.2.1
    · exact hcap 20 (by simp)
    · exact hcap 21 (by simp)
    · exact hcap 22 (by simp)
    · exact hcap 23 (by simp)
    · exact hcap 24 (by simp)
  rw [vsReadsT]
  simp only [List.append_assoc, holdsList_append]
  refine (W 0 (by norm_num)).2.2.2 ?_
  refine (W 1 (by norm_num)).2.2.2 ?_
  refine ⟨st 0 (by norm_num), ?_⟩
  refine (W 2 (by norm_num)).2.2.2 ?_
  refine ⟨st 1 (by norm_num), ?_⟩
  refine (W 3 (by norm_num)).2.2.2 ?_
  refine ⟨st 2 (by norm_num), ?_⟩
  refine ⟨hk, ?_⟩
  refine (W 4 (by norm_num)).2.2.2 ?_
  refine ⟨st 3 (by norm_num), ?_⟩
  refine (W 5 (by norm_num)).2.2.2 ?_
  refine ⟨st 4 (by norm_num), ?_⟩
  refine (W 6 (by norm_num)).2.2.2 ?_
  refine ⟨st 5 (by norm_num), ?_⟩
  exact (W 7 (by norm_num)).2.2.2 hn

end
end LeanVM.Guest.B1.VerifySub
