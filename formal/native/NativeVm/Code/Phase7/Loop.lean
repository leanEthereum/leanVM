module

public import NativeVm.Code.Phase7.Level

/-!
# The non-final levels

The loop `while r15 ≠ 0: levelC` refines the fold of `levelAt` over the non-final levels
(`levelsC_b`), its invariant `LInv k`: the level's context at index `k` with `r15` the levels
left, WHIR's state, `WOk`, and at most `1 + k` roots read (one commitment a level, the stack's
before them: `levelM_roots`).
-/

@[expose] public section

namespace NativeVm.Code.P7

open Native NativeVm.Model LeanVM.Parameters

variable {p : Par}

theorem queryOpenings_keeps (i : Nat) (ps : Array UInt64) : KeepsRoots (queryOpenings i ps) :=
  ⟨fun _ _ _ h ↦ qy_roots h⟩

/-- **A non-final level reads one root.** -/
theorem levelM_roots (logN index : Nat) (level next : Whir.Level) (s : WhirStateW) :
    GrowsRoots 1 (levelM logN index level next s) := by
  unfold levelM
  refine (GrowsRoots.bind (b := 1) (foldRounds_roots _ _).grows fun x ↦ ?_).mono (by omega)
  obtain ⟨s', rounds⟩ := x
  dsimp only [levelShape]
  refine (GrowsRoots.bind (b := 0) (readCommitment_roots _ _) fun _ ↦ KeepsRoots.grows ?_).mono
    (by omega)
  refine (KeepsRoots.readScalars _).bind fun _ ↦ (KeepsRoots.grind _).bind fun _ ↦
    (KeepsRoots.sampleChallenges _).bind fun _ ↦ KeepsRoots.readScalar.bind fun _ ↦
    (KeepsRoots.grind _).bind fun _ ↦ (sampleQueries_keepsRoots _ _).bind fun _ ↦
    KeepsRoots.sampleChallenge.bind fun _ ↦ (queryOpenings_keeps _ _).bind fun _ ↦
    KeepsRoots.pure _

/-- The loop's invariant after `k` non-final levels. -/
def LInv (p : Par) (L : List Whir.Level) (logN : Nat) (scales : Array EW) (k : Nat)
    (sW : WhirStateW) (t : TState) (s : QState) : Prop :=
  (Base p t s ∧ (LvB p L logN k scales s.mem ∧ WhirAt s.mem (whirR.at p.env.work) sW) ∧
    s.reg .r15 = (L.length - 1 - k).toUInt64) ∧ WOk L k sW ∧ t.roots.size ≤ 1 + k

/-- **The non-final levels.** -/
theorem levelsC_b {L : List Whir.Level} {logN : Nat} {scales : Array EW} {sW : WhirStateW}
    (hok : LadderOk logN L) (hlog : logN ≤ 30) (hq : ∀ lv ∈ L, 1 ≤ lv.queries) :
    Refines (LInv p L logN scales 0 sW) (.loop (.cmp .ne .r15 (.imm 0)) levelC)
      ((List.range (L.length - 1)).foldlM (levelAt logN L) sW)
      (fun sW' t s ↦ LInv p L logN scales (L.length - 1) sW' t s) (Err p) := by
  have hl6 : L.length ≤ 6 := hok.len.2
  refine (Refines.foldlM (Inv := LInv p L logN scales) ?_ ?_).mono (fun _ _ h ↦ h)
    (fun x t s h ↦ by rwa [List.length_range] at h) (fun _ h ↦ h)
  · rintro k acc t s ⟨⟨-, -, h15⟩, -⟩
    rw [List.length_range, NativeVm.Transcript.cond_ne, h15, NativeVm.Transcript.rhs_imm]
    simp only [bne_iff_ne, ne_eq]
    rw [show ((0 : Int64).toUInt64) = (0 : UInt64) from rfl, ← ne_eq,
      toUInt64_ne_zero (by omega)]
    omega
  · intro k hk acc
    rw [List.length_range] at hk
    rw [List.getElem_range]
    intro t s ⟨⟨hb, hx, _⟩, hw, hr⟩
    have hmax : Transcript.maxRoots = 8 := rfl
    exact (Refines.addT (fun t ↦ t.roots.size ≤ 1 + k) (fun t ↦ t.roots.size ≤ 1 + (k + 1))
      (fun t x t' hr hi ↦ by
        have := (levelM_roots _ _ _ _ _).grows t x t' hr
        omega)
      (levelC_b (p := p) (scales := scales) hok hlog hq (by omega) hw)).mono (fun _ _ h ↦ h)
      (fun x t s ⟨⟨h, hw⟩, hr⟩ ↦ ⟨h, hw, hr⟩) (fun _ h ↦ h) t s ⟨⟨hb, hx, by omega⟩, hr⟩

end NativeVm.Code.P7
