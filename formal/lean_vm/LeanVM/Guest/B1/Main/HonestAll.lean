/-
  LeanVM.Guest.B1.Main.HonestAll

  `main`'s honest words satisfy `MainWordsOk` (from a witness of `NodeRel` within the deployed
  limits), and `main` is complete, placed: TRIAGE #76's completeness.
-/

module

public import LeanVM.Guest.B1.Main.HonestChild

/-!
# `main` is complete

`honest_wordsOk`: the honest words (`honestWords`) of a witness of `NodeRel` within `Limits`
satisfy `MainWordsOk`, every child's proof run by a run in `VsGood` and its fresh claims of the
guest's shape. `main_complete`: at every `fp` one size and one layout serve every memory holding
`main`'s words, defined below `2^κ`, with the statement's digest at words `0` and `1`.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.Hints (direct)
open LeanVM.Guest.End (Limits coverage)
open LeanVM.Guest.B1 (LowDef Within)

@[expose] public section

/-- A batching's rounds are the deferred claim's points. -/
theorem batch_lengths {cs : List ChildClaims} {h : BatchHints} {d : DeferredClaim}
    (hb : batch cs h = some d) :
    d.bytecodePoint.length = h.bytecodeRounds.length ∧ d.matrixPoint.length = h.matrixRounds.length := by
  rw [batch_spec] at hb
  simp only at hb
  split_ifs at hb
  injection hb with hd
  subst hd
  exact ⟨batchRounds_length _ _ _, batchRounds_length _ _ _⟩

variable (fs : String → ℕ) {fp : ℕ} {seed : Digest} {s : NodeStatement} {w : NodeWitness}

theorem honest_lens {bytecode : List K} (hb : bytecode.length = 2 ^ 22) (hN : NodeRel bytecode seed s w)
    (hfr : ∀ c ∈ w.children, FreshShaped c.fresh) :
    (honestWords seed s w).bufs.map List.length = (honestWords seed s w).sizes := by
  simp only [MainWords.bufs, MainWords.sizes, List.map_cons, List.map_nil, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, rfl, hon_cov_length, ?_, ?_, ?_, ?_, defer_cells_length hb hN.1⟩
  · simp only [honestWords]
    rw [length_flatMap_const _ 4 _ fun c _ => daCellsOf_length c, List.length_append]
  · simp only [honestWords]
    rw [length_flatMap_const _ 4 _ fun c _ => xCellsOf_length c, List.length_append]
  · simp only [honestWords]
    rw [length_flatMap_const _ 4 _ fun c _ => sCellsOf_length c, List.length_append]
  · simp only [honestWords]
    rw [length_flatMap_const _ 2 _ fun c _ => rfl]
  · simp only [honestWords]
    rw [length_flatMap_const _ 106 _ fun c hc => fixedCells_length (hfr c hc)]
  · simp only [honestWords]
    rw [length_flatMap_const _ 53 _ fun c hc => defer_cells_length hb (hN.2.1 c hc).1]
  · simp [honestWords]

/-- **`main`'s honest words are what its callees need.** -/
theorem honest_wordsOk {κ : ℕ} {VsGood : VerifySub.VsData → Prop} {bytecode : List K}
    (hb : bytecode.length = 2 ^ 22) (hN : NodeRel bytecode seed s w) (hlim : Limits s w)
    (hfr : ∀ c ∈ w.children, FreshShaped c.fresh)
    (hvs : ∀ c ∈ w.children, ∃ D : VerifySub.VsData, VsGood D ∧ D.pi = statementDigest seed c.statement ∧
      D.seed = seed ∧ D.fresh = c.fresh) :
    MainWordsOk fs κ VsGood fp (honestWords seed s w) := by
  obtain ⟨hsh, hch, hX, hS, hD, hfin⟩ := hN
  have ht := honest_total (seed := seed) hlim
  have hrxl := honest_rx_le hlim
  have hrsl := honest_rs_le hlim
  have hdau := honest_dau hlim
  have hrdl : hrd s w ≤ 1 := hlim.directDa
  simp only [MainWords.total, honestWords] at ht
  refine
    { total := by simp only [MainWords.total, honestWords]; omega
      nc := hlim.children
      rd1 := hrdl
      da := hlim.daRoots.1
      ud := by simp only [honestWords]; omega
      dau := hdau
      rx := by simp only [honestWords]; omega
      rs := by simp only [honestWords]; omega
      decl := hlim.nonempty
      lens := honest_lens hb ⟨hsh, hch, hX, hS, hD, hfin⟩ hfr
      daList := ⟨_, rfl, fun rd _ hL => hon_daList fs hlim hL⟩
      xList := ⟨_, length_flatMap_const _ 4 _ fun c _ => xCellsOf_length c, fun rd _ hL => hon_xList fs hlim hL⟩
      sList := ⟨_, length_flatMap_const _ 4 _ fun c _ => sCellsOf_length c, fun rd _ hL => hon_sList fs hlim hL⟩
      sig := hon_sig _ _
      xSlot := fun c hc => (hon_markX fs (seed := seed) (fp := fp)
        (show c < (writersX s w).length by rw [writersX_len]; simp only [honestWords] at hc; omega)).1
      xMark := fun c hc => by
        have := (hon_markX fs (seed := seed) (fp := fp)
          (show c < (writersX s w).length by rw [writersX_len]; simp only [honestWords] at hc; omega)).2
        rw [gX_raw hc] at this
        exact this
      xSig := fun c hc rd _ hL => hon_xSig fs hX hL hc
      sSlot := fun c hc => (hon_markS fs (seed := seed) (fp := fp)
        (show c < (writersS s w).length by rw [writersS_len]; simp only [honestWords] at hc; omega)).1
      sMark := fun c hc => by
        have := (hon_markS fs (seed := seed) (fp := fp)
          (show c < (writersS s w).length by rw [writersS_len]; simp only [honestWords] at hc; omega)).2
        rw [gS_raw hc, pow_add] at this
        exact this
      sSig := fun c hc rd _ hL => hon_sSig fs hS hL hc
      daVerify := fun h1 => by
        obtain ⟨wt, root, vd, ho, hr, h⟩ := hon_daVerify fs (fp := fp) (seed := seed) hD h1
        exact ⟨wt, root, vd, ho, hr, fun rd _ hL => h rd hL⟩
      daCover := fun h1 => ⟨_, fun rd _ hL => hon_daCover fs hlim h1 hL⟩
      written0 := by
        have := hon_written fs (fp := fp) (seed := seed) (s := s) (w := w) 0 (by omega)
        rw [show hbase s w 0 = hrx s w + hrs s w + hrd s w by simp [hbase], pow_add, pow_add] at this
        exact this
      writtenN := by
        have := hon_written fs (fp := fp) (seed := seed) (s := s) (w := w) w.children.length le_rfl
        rw [hbase_children (seed := seed) hlim] at this
        simp only [MainWords.total, honestWords, pow_add] at this
        exact this
      children := fun c hc => hon_child fs hb hlim (fun x hx => (hch x hx).1) hfr hvs hc
      leaf := fun h0 => by
        have he : w.children = [] := List.length_eq_zero_iff.mp h0
        simp only [he, ↓reduceIte] at hfin
        obtain ⟨h1, h2⟩ := hfin
        rw [hb, Nat.log2_two_pow] at h1
        simp [honestWords, DeferredClaim.cells, h1, h2, blake2sR1csLogSize]
      agg := fun h0 => by
        have he : w.children ≠ [] := fun h => h0 (by simp [honestWords, h])
        simp only [he, ↓reduceIte] at hfin
        obtain ⟨l1, l2⟩ := batch_lengths hfin
        obtain ⟨b1, b2⟩ := hsh
        rw [hb, Nat.log2_two_pow] at b1
        refine ⟨_, w.hints, s.defer, by simp [honestWords], hfin, by omega,
          by rw [← l2, b2]; rfl, fun c hc => ?_, by simp [honestWords, List.flatMap_map],
          by simp [honestWords, List.flatMap_map], by simp [honestWords, List.flatMap_map], rfl⟩
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc
        obtain ⟨c1, c2⟩ := (hch x hx).1
        rw [hb, Nat.log2_two_pow] at c1
        exact ⟨hfr x hx, c1, by rw [c2]; rfl⟩
      stmt := ⟨_, _, fun rd _ hL => hon_stmt fs hb hsh hL⟩ }

/-- **`main` is complete, placed** (G:3119-3316; TRIAGE #76): for a witness of `NodeRel` within
the deployed limits, every child's proof run by a run in `VsGood` and of the guest's fresh shape,
and `main`'s callees complete within `Bd` (`CalleesAt`), at every `fp` one size, within
`mainBound`, and one layout of `main`'s words serve every memory holding them, defined below
`2^κ`, with the statement's digest at words `0` and `1`: `main` holds by a tree placed at `fp`,
loading from its own data or its header, within `mainWeight` at the honest words at every
`ωs θ` its callees' weights `Wt θ` are given at. -/
theorem main_completeW {cert : String → V → ℕ} {κ : ℕ} {VsGood : VerifySub.VsData → Prop}
    {Bd : CalleeBounds} {bytecode : List K} (H : CalleesAt fs cert κ VsGood Bd)
    {Θ : Type} {ωs : Θ → String → ℕ} (Wt : ∀ θ, MainWeightHyps fs (ωs θ)) (hκ : 16 ≤ κ)
    (hb : bytecode.length = 2 ^ 22) (hN : NodeRel bytecode seed s w) (hlim : Limits s w)
    (hfr : ∀ c ∈ w.children, FreshShaped c.fresh)
    (hvs : ∀ c ∈ w.children, ∃ D : VerifySub.VsData, VsGood D ∧ D.pi = statementDigest seed c.statement ∧
      D.seed = seed ∧ D.fresh = c.fresh) (fp : ℕ) :
    ∃ (m : ℕ) (L : Layout), Within L (fp + fs "main") m ∧ LeanVM.Guest.B1.DisjL L ∧
      fs "main" + m ≤ mainBound fs Bd (honestWords seed s w) ∧
      ∀ rd, LowDef κ rd → MemL rd L →
        rd 1 = some (digestScalars (statementDigest seed s)).1 →
        rd g = some (digestScalars (statementDigest seed s)).2 →
        RelAtInW fs cert ωs rd (fun i => i < 2) (fun _ => False) fp (fs "main" + m)
          "main" [] [] fun θ => mainWeight (ωs θ) Bd (Wt θ) (honestWords seed s w) :=
  let ⟨m, _, hW, hD, hB, h⟩ := main_relAtInW Wt H hκ (honest_wordsOk fs (fp := fp) hb hN hlim hfr hvs)
  ⟨m, _, hW, hD, by unfold mainBound; omega, h⟩

/-- **`main` is complete, placed**, by a bounded tree. -/
theorem main_complete {cert : String → V → ℕ} {κ : ℕ} {VsGood : VerifySub.VsData → Prop}
    {Bd : CalleeBounds} {bytecode : List K} (H : CalleesAt fs cert κ VsGood Bd) (hκ : 16 ≤ κ)
    (hb : bytecode.length = 2 ^ 22) (hN : NodeRel bytecode seed s w) (hlim : Limits s w)
    (hfr : ∀ c ∈ w.children, FreshShaped c.fresh)
    (hvs : ∀ c ∈ w.children, ∃ D : VerifySub.VsData, VsGood D ∧ D.pi = statementDigest seed c.statement ∧
      D.seed = seed ∧ D.fresh = c.fresh) (fp : ℕ) :
    ∃ (m : ℕ) (L : Layout), Within L (fp + fs "main") m ∧ LeanVM.Guest.B1.DisjL L ∧
      fs "main" + m ≤ mainBound fs Bd (honestWords seed s w) ∧
      ∀ rd, LowDef κ rd → MemL rd L →
        rd 1 = some (digestScalars (statementDigest seed s)).1 →
        rd g = some (digestScalars (statementDigest seed s)).2 →
        RelAtIn coreProgram fs cert rd (fun i => i < 2) (fun _ => False) fp (fs "main" + m)
          "main" [] [] :=
  let ⟨m, L, hW, hD, hB, h⟩ := main_completeW fs H (ωs := fun (θ : Empty) => θ.elim) (fun θ => θ.elim) hκ hb hN
    hlim hfr hvs fp
  ⟨m, L, hW, hD, hB, fun rd hl hL h0 h1 => (h rd hl hL h0 h1).toRelAtIn⟩

end
end LeanVM.Guest.B1.Main
