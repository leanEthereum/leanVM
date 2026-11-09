/-
  LeanVM.Guest.B1.VerifySub.H.Keccak

  An honest child's Keccak reduction as `verify_keccak` takes it: from `verify_tables`' capacity,
  on `chi` cut to the `KECCAK` table's height and the output lanes' values, one committed outputs'
  claim on `q_keccak` and the ring switch's point, `τ + 6` coordinates each, and `64` slices.
-/

module

public import LeanVM.Guest.B1.VerifySub.H.Data
public import LeanVM.Protocol.EndToEnd.Front.KeccakBridge

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node
open LeanVM.Protocol.EndToEnd.Sound (RetOK)

@[expose] public section

/-- **A value a program may return satisfies what every return does.** -/
theorem retOK_returns {α : Type} {Q : α → Prop} {p : VerifierProgram α} {a : α} (hr :
    VerifierProgram.Returns p a)
    (h : RetOK Q p) : Q a := by
  induction hr with
  | ret a => exact h [] a rfl
  | read x _ ih => exact ih fun l b hl ↦ h (Ev.read x :: l) b (by simpa [VerifierProgram.after] using hl)
  | sample x _ ih => exact ih fun l b hl ↦ h (Ev.sample x :: l) b (by simpa [VerifierProgram.after] using hl)
  | grind bits _ ih => exact ih fun l b hl ↦ h (Ev.grind bits :: l) b (by simpa [VerifierProgram.after] using hl)
  | commit ht w _ ih =>
    exact ih fun l b hl ↦ h (Ev.commit ht w (fun _ ↦ []) :: l) b
        (by simpa [VerifierProgram.after] using hl)
  | query i ps rows _ ih =>
    exact ih fun l b hl ↦ h (Ev.query rows :: l) b (by simpa [VerifierProgram.after] using hl)

/-- **`keccakSeg`'s outputs**: one committed outputs' claim on `q_keccak` at `τ + 6` coordinates,
the ring switch's point of `τ + 6` coordinates and `64` slices. -/
theorem keccakSeg_out {τ : ℕ} {inst out : List E} {s t : Fs} {xs : List E}
    {km : (List ColumnClaim × List E × List E) × E}
    (h : RunsTo (keccakSeg τ inst out) s xs km t) (hc : ∃ sp, s.Carries sp)
    (hi : 4 ≤ inst.length) (hl : inst.length = τ) :
    ∃ op word, km.1.1 = [⟨qkeccak, op, word⟩] ∧ op.length = τ + 6 ∧ km.1.2.1.length = τ + 6 ∧
      km.1.2.2.length = 64 := by
  obtain ⟨op, word, hk⟩ := keccakSeg_shape h hc
  obtain ⟨sp, hsp⟩ := hc
  obtain ⟨sp', -, e⟩ := h sp hsp [] [] []
  have hr := VerifierProgram.returns_of_run keccak256 keccakF1600 e
  unfold keccakSeg at hr
  obtain ⟨r, hr1, hr2⟩ := VerifierProgram.returns_bind hr
  obtain ⟨m, -, hr2⟩ := VerifierProgram.returns_bind hr2
  have ek := VerifierProgram.returns_ret hr2
  subst ek
  have h1 := retOK_returns hr1 (LeanVM.Protocol.EndToEnd.Front.retOK_verifyKeccak τ inst out hi)
  have h2 := retOK_returns hr1
    (LeanVM.Protocol.EndToEnd.Front.retOK_verifyKeccak_point τ inst out hi hl)
  refine ⟨op, word, hk, ?_, by rw [← hl]; exact h2.1, h2.2⟩
  have := (h1 ⟨qkeccak, op, word⟩ (by rw [show (r, m).1.1 = r.1 from rfl] at hk; rw [hk]; simp)).2
  rw [← hl]; exact this

namespace ChildSegs

variable {bytecode : List K} {seed : Digest} {c : Child} (S : ChildSegs bytecode seed c)

/-- The output lanes' values. -/
noncomputable def outs : List E := (S.H.poolW.drop 112).take 25

/-- `chi`'s words: the table sumcheck's challenges, last first. -/
noncomputable def chis : List E := S.H.chiW

/-- The committed outputs' claim's point. -/
def op : List E := (S.km.1.1.headD default).point

/-- The committed outputs' word. -/
def word : E := (S.km.1.1.headD default).value

/-- The ring switch's point. -/
def kpt : List E := S.km.1.2.1

/-- The slices. -/
def slices : List E := S.km.1.2.2

/-- The ring map's first challenge. -/
def m0 : E := S.km.2

theorem chis_length : S.chis.length = S.H.n := by
  simp [ChildSegs.chis, Tables.VtHonest.chiW, Tables.zcChis]

theorem τ_bounds (hbl : bytecode.length = 2 ^ 23) : 9 ≤ S.τ ∧ S.τ < 29 ∧ S.τ ≤ S.H.n := by
  have hsl := S.hs_length
  refine ⟨tau_ge S.hrowsL, S.hh29 hbl _ ?_, ?_⟩
  · rw [ChildSegs.τ, List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
  · show S.hs.getD 5 0 ≤ (Tables.tableHeightsOf S.rowsN).foldl max 0
    exact mem_le_foldl_max 0 (getD_mem' (by have := hsl; unfold ChildSegs.hs at this; omega))

/-- **The lanes, honestly**: their point is `chi` cut to the `KECCAK` table's height. -/
theorem lanes (hbl : bytecode.length = 2 ^ 23) :
    ((lanesOf S.claims).headD default).point = S.chis.take S.τ ∧
      (lanesOf S.claims).map (·.value) = S.outs ∧ S.outs.length = 25 := by
  obtain ⟨hok, -, -, -⟩ := S.H_run hbl
  obtain ⟨hv, hl, -, hp⟩ := vtH_lanes hok S.hrowsL hbl
  rw [S.H_claims] at hv hl hp
  obtain ⟨c0, cs, hcs⟩ := List.exists_cons_of_ne_nil (show lanesOf S.claims ≠ [] by
    intro h; rw [h] at hl; simp at hl)
  refine ⟨?_, hv, ?_⟩
  · rw [hcs]; exact hp c0 (by rw [hcs]; exact List.mem_cons_self)
  · rw [ChildSegs.outs, ← hv, List.length_map, hl]

/-- **The Keccak reduction's run from `verify_tables`' capacity**, its outputs. -/
theorem runK' (hbl : bytecode.length = 2 ^ 23) :
    RunsTo (keccakSeg S.τ (S.chis.take S.τ) S.outs) ⟨S.s6.cap, []⟩ S.xsK
      (([⟨qkeccak, S.op, S.word⟩], S.kpt, S.slices), S.m0) ⟨S.s7.cap, []⟩ ∧
      S.op.length = S.τ + 6 ∧ S.kpt.length = S.τ + 6 ∧ S.slices.length = 64 ∧
      (∃ sp, (⟨S.s6.cap, []⟩ : Fs).Carries sp) := by
  obtain ⟨-, -, h6, -⟩ := S.H_run hbl
  obtain ⟨hpt, hvals, -⟩ := S.lanes hbl
  have h := S.runK
  rw [S.hlayout, hpt, hvals, h6] at h
  have hc6 : ∃ sp, (⟨S.s6.cap, []⟩ : Fs).Carries sp := by
    have := Tables.RunsTo.carries S.runT (by rw [(S.runG' hbl).2.1]; exact S.s5_carries hbl)
    rwa [h6] at this
  have h7 := keccakSeg_end h hc6
  have hτ := S.τ_bounds hbl
  have hil : (S.chis.take S.τ).length = S.τ := by simp [S.chis_length]; omega
  obtain ⟨op', word', hk, hop, hpt', hsl⟩ := keccakSeg_out h hc6 (by rw [hil]; omega) hil
  have ekm : S.km = (([⟨qkeccak, S.op, S.word⟩], S.kpt, S.slices), S.m0) := by
    refine Prod.ext (Prod.ext ?_ rfl) rfl
    show S.km.1.1 = [⟨qkeccak, (S.km.1.1.headD default).point, (S.km.1.1.headD default).value⟩]
    rw [hk]; rfl
  rw [h7, ekm] at h
  refine ⟨h, ?_, hpt', hsl, hc6⟩
  simp only [ChildSegs.op, hk]
  exact hop

theorem s7_capOf (hbl : bytecode.length = 2 ^ 23) : ∃ K, S.s7.cap = capOf K := by
  obtain ⟨h, -, -, -, hc6⟩ := S.runK' hbl
  obtain ⟨K, hK⟩ := keccakSeg_capOf h hc6
  exact ⟨K, by rw [show S.s7.cap = (⟨S.s7.cap, []⟩ : Fs).cap from rfl, hK]⟩

end ChildSegs

end
end LeanVM.Guest.B1.VerifySub
