/-
  LeanVM.Guest.B1.Place.LrBufs

  `level_residual`'s chain buffers as a layout, its body placed on them, its loops honestly on
  them, and a loop's guarded size.
-/

module

public import LeanVM.Guest.B1.Place.LrCore

/-!
# `level_residual`'s buffers

`lrBufL … fp`: the batches' chain (`lrCH`) at `fp + fs name` and, when `8 ∤ q`, the rest's chain
(`lrRS`) after it, the honest words `level_residual` reads back. `lr_relAtIn`: on a memory holding
them, the function placed (`lr_relAtIn0`, `lr_relAtIn1`). `lr_loop1_rel`, `lr_loop2_rel`: its loops
hold there honestly. `guarded_relAtIn`, `guarded_uniform`: a loop's call, entered or skipped, at
one size.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Guest.B1.Whir
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

/-- The batches' chain: the chain over the first `8j` positions, `j ≤ q / 8`. -/
def lrCH (D : ℕ → E) (cols : ℕ) (M : E) (p : ℕ → E) (q : ℕ) : List E :=
  (List.range (q / resBatch + 1)).map fun j ↦ lrAcc D cols M p (resBatch * j)

/-- The rest's chain: the chain over the first `8·(q / 8) + j` positions, `j ≤ q % 8`. -/
def lrRS (D : ℕ → E) (cols : ℕ) (M : E) (p : ℕ → E) (q : ℕ) : List E :=
  (List.range (q % resBatch + 1)).map fun j ↦ lrAcc D cols M p (resBatch * (q / resBatch) + j)

/-- The chains' words, one list a buffer. -/
def lrWords (D : ℕ → E) (cols : ℕ) (M : E) (p : ℕ → E) (q : ℕ) : List (List E) :=
  if q % resBatch = 0 then [lrCH D cols M p q] else [lrCH D cols M p q, lrRS D cols M p q]

/-- **`level_residual`'s buffers at `fp`**, holding the honest chains. -/
def lrBufL (fs : String → ℕ) (name : String) (q cols : ℕ) (D : ℕ → E) (M : E) (p : ℕ → E)
    (fp : ℕ) : Layout :=
  bufL (fp + fs name) (lrSizes q) (lrWords D cols M p q)

theorem lrWords_forall₂ (D : ℕ → E) (cols : ℕ) (M : E) (p : ℕ → E) (q : ℕ) :
    List.Forall₂ (fun c s ↦ c.length ≤ s) (lrWords D cols M p q) (lrSizes q) := by
  unfold lrWords lrSizes
  split <;> simp [lrCH, lrRS]

theorem lrBufL_eq (fs : String → ℕ) (name : String) (q cols : ℕ) (D : ℕ → E) (M : E) (p : ℕ → E)
    (fp : ℕ) : lrBufL fs name q cols D M p fp = if q % resBatch = 0 then
      [(fp + fs name, lrCH D cols M p q)] else
      [(fp + fs name, lrCH D cols M p q), (fp + fs name + (q / resBatch + 1), lrRS D cols M p q)] := by
  unfold lrBufL lrWords lrSizes bufL
  split <;> simp [bases]

theorem lrCH_of_mem {rd : Reader} {fs : String → ℕ} {name : String} {q cols : ℕ} {D : ℕ → E}
    {M : E} {p : ℕ → E} {fp : ℕ} (h : MemL rd (lrBufL fs name q cols D M p fp)) :
    ∀ j ≤ q / resBatch, LoadHolds rd (ofK (addressOfIndex (fp + fs name))) j
      (lrAcc D cols M p (resBatch * j)) := by
  intro j hj
  have hm : (fp + fs name, lrCH D cols M p q) ∈ lrBufL fs name q cols D M p fp := by
    rw [lrBufL_eq]; split <;> simp
  have := h _ hm j (by simp [lrCH]; omega)
  simpa [lrCH] using this

theorem lrRS_of_mem {rd : Reader} {fs : String → ℕ} {name : String} {q cols : ℕ} {D : ℕ → E}
    {M : E} {p : ℕ → E} {fp : ℕ} (h : MemL rd (lrBufL fs name q cols D M p fp))
    (h0 : q % resBatch ≠ 0) :
    ∀ j ≤ q % resBatch, LoadHolds rd (ofK (addressOfIndex (fp + fs name + (q / resBatch + 1)))) j
      (lrAcc D cols M p (resBatch * (q / resBatch) + j)) := by
  intro j hj
  have hm : (fp + fs name + (q / resBatch + 1), lrRS D cols M p q) ∈ lrBufL fs name q cols D M p fp := by
    rw [lrBufL_eq]; simp [h0]
  have := h _ hm j (by simp [lrRS]; omega)
  simpa [lrRS] using this

/-- **`level_residual` placed on its buffers**, its loops' trees given after them. -/
theorem lr_relAtIn {name loop1 loop2 : String} {q cols : ℕ}
    (hlr : FnIs name (osParams 3) (lrBody q loop1 loop2)) (hq : q + 2 < 2 ^ 64 - 1)
    (fs : String → ℕ) (cert : String → V → ℕ) {rd : Reader} {R Rk : ℕ → Prop} {fp m1 m2 : ℕ}
    {P BD M : E} {D p : ℕ → E} (hbuf : MemL rd (lrBufL fs name q cols D M p fp))
    (hL1 : if 1 + gen ^ (q / resBatch) ≠ 0 then
      RelAtIn coreProgram fs cert rd Rk (fun _ ↦ False) (fp + fs name + (lrSizes q).sum) m1 loop1
        [1, gen ^ (q / resBatch), ofK (addressOfIndex (fp + fs name)), P, BD, M] []
      else m1 = fs loop1)
    (hL2 : q % resBatch ≠ 0 → if 1 + gen ^ (q % resBatch) ≠ 0 then
      RelAtIn coreProgram fs cert rd Rk (fun _ ↦ False) (fp + fs name + (lrSizes q).sum + m1) m2
        loop2 [1, gen ^ (q % resBatch), ofK (addressOfIndex (fp + fs name + (q / resBatch + 1))),
          P * gen ^ (resBatch * (q / resBatch)), BD, M] []
      else m2 = fs loop2)
    (hm2 : q % resBatch = 0 → m2 = 0)
    (hRk : ∀ i, Rk i → R i ∨ (fp + fs name ≤ i ∧ i < fp + fs name + (lrSizes q).sum)) :
    RelAtIn coreProgram fs cert rd R (fun _ ↦ False) fp (fs name + (lrSizes q).sum + (m1 + m2))
      name [P, BD, M] [lrAcc D cols M p q] := by
  by_cases h0 : q % resBatch = 0
  · rw [hm2 h0, Nat.add_zero]
    exact lr_relAtIn0 hlr hq h0 fs cert (lrCH_of_mem hbuf) hL1 hRk
  · exact lr_relAtIn1 hlr hq h0 fs cert (lrCH_of_mem hbuf) (lrRS_of_mem hbuf h0) hL1 (hL2 h0) hRk hRk

/-- **The batches' loop, honestly, on the buffers.** -/
theorem lr_loop1_rel {loop1 : String} {q cols : ℕ}
    (hl1 : FnIs loop1 (osParams 6) (lrLoop1Body cols loop1))
    (hrb : FnIs (rbName cols) (osParams 4) (rbBody cols)) (hn : 1 ≤ cols) (hq8 : 0 < q / resBatch)
    {fs : String → ℕ} {name : String} {rd : Reader} {fp : ℕ} {P BD M : E} {D p : ℕ → E}
    (hP : ∀ i < q, LoadHolds rd P i (p i)) (hD : ∀ s < cols, LoadHolds rd BD s (D s))
    (hbuf : MemL rd (lrBufL fs name q cols D M p fp)) :
    1 + gen ^ (q / resBatch) ≠ 0 → coreProgram.Rel rd loop1
      [1, gen ^ (q / resBatch), ofK (addressOfIndex (fp + fs name)), P, BD, M] [] :=
  (lrLoop1_complete hl1 hrb hn hq8
    (fun i hi ↦ hP i (lt_of_lt_of_le hi (Nat.mul_div_le q resBatch))) hD (lrCH_of_mem hbuf)).2

/-- **The rest's loop, honestly, on the buffers.** -/
theorem lr_loop2_rel {loop2 : String} {q cols : ℕ}
    (hl2 : FnIs loop2 (osParams 6) (lrLoop2Body cols loop2)) (hn : 1 ≤ cols)
    (h0 : q % resBatch ≠ 0)
    {fs : String → ℕ} {name : String} {rd : Reader} {fp : ℕ} {P BD M : E} {D p : ℕ → E}
    (hP : ∀ i < q, LoadHolds rd P i (p i)) (hD : ∀ s < cols, LoadHolds rd BD s (D s))
    (hbuf : MemL rd (lrBufL fs name q cols D M p fp)) :
    1 + gen ^ (q % resBatch) ≠ 0 → coreProgram.Rel rd loop2
      [1, gen ^ (q % resBatch), ofK (addressOfIndex (fp + fs name + (q / resBatch + 1))),
        P * gen ^ (resBatch * (q / resBatch)), BD, M] [] := by
  have hqd := Nat.div_add_mod q resBatch
  exact (lrLoop2_complete (b := resBatch * (q / resBatch)) hl2 hn (Nat.pos_of_ne_zero h0)
    (fun i hi ↦ hP _ (by omega)) hD (lrRS_of_mem hbuf h0)).2

/-! ## A loop's call, entered or skipped -/

/-- **A guarded pure call on one memory**, placed at `fp'`: its size, whether it is entered. -/
theorem guarded_relAtIn {S : List String} (hS : coreProgram.PureIn S) {g : String} (hg : g ∈ S)
    (fs : String → ℕ) (cert : String → V → ℕ) {rd : Reader} {Rk : ℕ → Prop} {args : List E}
    {G : Prop} [Decidable G] (hsupp : ∀ A v, rd A = some v → ∃ i, A = addressOfIndex i ∧ Rk i)
    (h : G → coreProgram.Rel rd g args []) (fp' : ℕ) :
    ∃ m, if G then RelAtIn coreProgram fs cert rd Rk (fun _ ↦ False) fp' m g args [] else m = fs g := by
  by_cases hG : G
  · obtain ⟨n, hn⟩ := relAtIn_uniform_pure (fs := fs) (cert := cert) coreProgram_fresh hS hg
      (Main.relIn_of_rel_supp coreProgram_wf hsupp (h hG))
    exact ⟨n, by rw [ite_eq_left hG]; exact hn fp' rd (fun _ _ ↦ rfl) (fun _ h ↦ h)⟩
  · exact ⟨fs g, by rw [ite_eq_right hG]⟩

/-- **A guarded pure call on the words `Lk`**, one size on every memory defined below `2^κ`
holding them. -/
theorem guarded_uniform {S : List String} (hS : coreProgram.PureIn S) {g : String} (hg : g ∈ S)
    (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ} {Lk : Layout} {args : List E}
    {G : Prop} [Decidable G]
    (h : G → ∀ rd, LowDef κ rd → MemL rd Lk →
      coreProgram.Rel (Main.restrict rd (RegionL Lk)) g args []) :
    ∃ m, ∀ fp' rd, LowDef κ rd → MemL rd Lk → if G then
      RelAtIn coreProgram fs cert rd (RegionL Lk) (fun _ ↦ False) fp' m g args [] else m = fs g := by
  by_cases hG : G
  · obtain ⟨n, hn⟩ := relAtIn_pure_uniform hS hg fs cert (h hG)
    exact ⟨n, fun fp' rd hl hL ↦ by rw [ite_eq_left hG]; exact hn fp' rd hl hL⟩
  · exact ⟨fs g, fun _ _ _ _ ↦ by rw [ite_eq_right hG]⟩

end
end LeanVM.Guest.B1
