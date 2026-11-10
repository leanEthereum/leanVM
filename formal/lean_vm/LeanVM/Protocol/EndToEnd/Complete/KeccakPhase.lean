/-
  LeanVM.Protocol.EndToEnd.Complete.KeccakPhase

  The honest run of the Keccak phase of the verifier program: the check on the output lanes'
  claims passes, and the Keccak reduction, run by its honest prover on the honest stack's
  `q_keccak`, returns true claims on `q_keccak` and its true slices.
-/

module

public import LeanVM.Protocol.Verifier.Claims
public import LeanVM.Protocol.EndToEnd.Complete.Table
public import LeanVM.Protocol.EndToEnd.Front.KeccakBridge
public import LeanVM.Protocol.Keccak.Complete
public import LeanVM.Protocol.EndToEnd.Front.RingFidelity

/-!
# Completeness of the Keccak phase

Step 6 of `verify_execution` (`keccakPhase`, `crates/verifier/src/lib.rs:283-300` at leanVM
`40f877dc`): the claims on the 25 output lanes of `KECCAK` leave
the batch, the program checks that they are the 25 lanes in order at one point, and they become
the claim of the Keccak reduction (`verifyKeccak`), whose column claims on `q_keccak` join the
batch and whose point and slices go to ring switching.

Against the honest prover the claims on the output lanes are the table phase's honest claims
(`honestLanes`, from `follows_tablePhase`): the bus and the public input claim no output lane
(`lanesOf_honest`). So the check passes (`lanesOk_honestLanes`), and on the honest stack:

* the output lanes' claims are the reduction's `outClaimsTrueMid` (`outClaimsTrueMid_honest`):
  an output lane is derived, the second segment of the committed middle state
  (`Front.laneHolds_iff`);
* the middle state agrees with twelve rounds of the input at the lanes' point
  (`midAgree_honest`): the honest stack satisfies the instance's Keccak predicate (`M3Holds`), and
  `Front.auxAt_iff_midAgree` reads it at any point;
* the reduction's column claims (`colTrue`) are true claims on `QKECCAK`
  (`trueClaim_of_colTrue`).

`follows_keccakPhase`: the honest prover (`hKeccakPhase`) follows `keccakPhase`, and the claims
it returns are true claims on no output lane, its slices the true slices of `q_keccak`. The
honest stack is read on the verifier's layout by `fromI` (`toI_fromI`).
-/

namespace LeanVM.Protocol.EndToEnd.Complete

open LeanVM.Prover (Script)

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.Whir.Complete
open LeanVM.Protocol.KeccakGkr Finset

@[expose] public section

/-- A column read on equal variables and back is itself. -/
theorem castColumn_symm {a b : ℕ} (h : a = b) (q : Column b) :
    castColumn h (castColumn h.symm q) = q := by
  subst h
  simp [castColumn]

/-! ## What the program returns, in a simulation -/

open LeanVM.Protocol.EndToEnd.Sound (RetOK RetOK.ret RetOK.bind_true) in
/-- **A simulation returns what the program returns**: a property of every return of the
program holds of the simulation's results. -/
theorem follows_retOK {α β : Type} {R : Commits → α → β → Prop} {Q : β → Prop} :
    ∀ (H : Script α) (P : VerifierProgram β) (cs : Commits), Follows R H P cs → RetOK Q P →
      Follows (fun cs a b ↦ R cs a b ∧ Q b) H P cs := by
  intro H
  induction H with
  | ret a =>
    intro P cs h hq
    cases P <;> simp only [Follows] at h ⊢
    exact ⟨h, hq [] _ rfl⟩
  | send x k ih =>
    intro P cs h hq
    cases P <;> simp only [Follows] at h ⊢
    exact ih _ _ h fun l a hl ↦ hq (Ev.read x :: l) a (by simpa [VerifierProgram.after] using hl)
  | sample k ih =>
    intro P cs h hq
    cases P <;> simp only [Follows] at h ⊢
    exact fun c ↦ ih c _ _ (h c) fun l a hl ↦ hq (Ev.sample c :: l) a
      (by simpa [VerifierProgram.after] using hl)
  | grind k ih =>
    intro P cs h hq
    cases P with
    | grind b k' =>
      simp only [Follows] at h ⊢
      exact ih _ _ h fun l a hl ↦ hq (Ev.grind b :: l) a (by simpa [VerifierProgram.after] using hl)
    | _ => simp only [Follows] at h
  | commit W k ih =>
    intro P cs h hq
    cases P with
    | commit ht w k' =>
      simp only [Follows] at h ⊢
      exact ⟨h.1, ih _ _ h.2 fun l a hl ↦ hq (Ev.commit ht w W :: l) a
        (by simpa [VerifierProgram.after] using hl)⟩
    | _ => simp only [Follows] at h
  | query k ih =>
    intro P cs h hq
    cases P with
    | query i ps k' =>
      simp only [Follows] at h ⊢
      obtain ⟨rows, h1, h2⟩ := h
      exact ⟨rows, h1, ih rows _ _ h2 fun l a hl ↦ hq (Ev.query rows :: l) a
        (by simpa [VerifierProgram.after] using hl)⟩
    | _ => simp only [Follows] at h

open LeanVM.Protocol.EndToEnd.Sound (RetOK RetOK.ret RetOK.bind_true) in
/-- The bus phase claims the framework's columns only. -/
theorem retOK_busColumns (layout : Verifier.Layout) :
    RetOK (fun bus : BusResult ↦ ∀ c ∈ bus.claims, c.column < 6)
      (verifyBusBalance computedBytecodeValue layout) := by
  unfold verifyBusBalance
  refine RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦ RetOK.bind_true fun r ↦ ?_
  obtain ⟨countRoot, point, treeValues⟩ := r
  refine RetOK.bind_true fun _ ↦ RetOK.bind_true fun memory ↦ RetOK.bind_true fun _ ↦
    RetOK.bind_true fun _ ↦ RetOK.ret ?_
  intro c hc
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with hc | rfl | rfl
  · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hc
    simp only [List.getElem_zipWith, List.length_zipWith] at hi ⊢
    have : i < 3 := by simp at hi; omega
    interval_cases i <;> simp [memory0, memory1, memory2]
  · show memoryFinalCounters < 6; decide
  · show bytecodeFinalCounters < 6; decide

open LeanVM.Protocol.EndToEnd.Sound (RetOK RetOK.ret RetOK.bind_true) in
/-- The public-input phase claims the memory columns only. -/
theorem retOK_publicColumns (layout : Verifier.Layout) (publicInput : Digest) :
    RetOK (fun claims : List Verifier.ColumnClaim ↦ ∀ c ∈ claims, c.column < 6)
      (publicInputPhase layout publicInput) := by
  unfold publicInputPhase
  refine RetOK.bind_true fun _ ↦ RetOK.ret ?_
  intro c hc
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hc
  simp only [List.getElem_zipWith, List.length_zipWith] at hi ⊢
  have : i < 3 := by simp at hi; omega
  interval_cases i <;> simp [memory0, memory1, memory2]

variable (prog : LeanIsaProgram) (s : Sizes) (q : Column (leanIsaμ prog s))

/-- The honest stack read on the verifier's layout. -/
def fromI : Column (verifierLayout prog s).stackLog :=
  castColumn (stackLog_verifierLayout prog s).symm q

theorem toI_fromI : toI prog s (fromI prog s q) = q :=
  castColumn_symm _ q

/-- `q_keccak`'s words on the honest stack: its cells past `QKECCAK`'s offset. -/
abbrev qkH : ℕ → K := Front.qkAt ((blocks prog s).offset (keccakBlock prog s)) q

theorem qkOf_fromI : qkOf (verifierLayout prog s) (fromI prog s q) = qkH prog s q := by
  funext n
  rw [qkOf_eq, toI_fromI]
  rfl

/-! ## The reduction's statement on the honest stack -/

/-- **The honest output lanes' claims are the reduction's output claims.** -/
theorem outClaimsTrueMid_honest (z : Vector E (s.τ 5)) :
    outClaimsTrueMid (s.τ 5) (qkH prog s q) z.toList
      ((honestLanes prog s q z).map (·.value)) := by
  intro l hl
  have hget : ((honestLanes prog s q z).map (·.value)).getD l 0 =
      colEval prog s q (outCol ⟨l, hl⟩) z := by
    simp [honestLanes, List.getD_eq_getElem?_getD, hl]
  rw [hget]
  have hw : WireHolds prog s ⟨refCol (outCol ⟨l, hl⟩), z.toList,
      colEval prog s q (outCol ⟨l, hl⟩) z⟩ (fromI prog s q) := by
    refine (wireHolds_iff prog s (outCol ⟨l, hl⟩) z _ (fromI prog s q)).mpr ?_
    rw [toI_fromI]
    rfl
  rw [refCol_outCol] at hw
  have h := (laneHolds_iff prog s (fromI prog s q) ⟨l, hl⟩ z.toList (by simp) _).mp hw
  rwa [qkOf_fromI] at h

/-- **On a stack satisfying `M3Holds`, the middle state agrees** with twelve rounds of the input,
at every point of the `KECCAK` table's coordinates. -/
theorem midAgree_honest {input : PublicInput} (hq : M3Holds (inst prog s) input q)
    (z : Vector E (s.τ 5)) : midAgree (s.τ 5) (qkH prog s q) z.toList := by
  have hτ : s.τ 5 ≤ (leanIsaInstance prog s).τmax :=
    (leanIsaInstance prog s).τ_le_τmax ⟨opIdx 5, keccak_sumcheckTable prog s⟩
  have h := (auxAt_iff_midAgree prog s (fromI prog s q) z.toList (by simp) hτ).mp
    (by rw [toI_fromI]; exact (leanIsaInstance prog s).auxAt_of_aux hq.2.2.2.2 _)
  rwa [qkOf_fromI, List.take_of_length_le (by simp)] at h

/-- **A true claim of the reduction on `q_keccak` is a true claim** on `QKECCAK`. -/
theorem trueClaim_of_colTrue {c : Verifier.ColumnClaim} (hc : colTrue (s.τ 5) (qkH prog s q) c) :
    TrueClaim prog s q c := by
  obtain ⟨col, pt, v⟩ := c
  obtain ⟨hcol, hlen, hv⟩ := hc
  simp only at hcol hlen hv
  subst hcol
  let z : Vector E (s.τ 5 + 6) := ⟨pt.toArray, by simpa using hlen⟩
  refine ⟨keccakCol, z, ?_⟩
  have hz : z.toList = pt := by simp [z]
  have heval : colEval prog s q keccakCol z = v := by
    refine (eval₂Mle_eq_sum_eqAt _ z).trans ?_
    rw [hz, hv]
    refine Finset.sum_congr rfl fun n hn ↦ ?_
    have h := keccakCol_getD prog s (fromI prog s q) (Finset.mem_range.1 hn)
    rw [toI_fromI, qkOf_fromI] at h
    exact congrArg (fun x ↦ eqAt pt n * ofK x) h
  rw [heval, refCol_keccakCol]
  exact congrArg (fun p ↦ (⟨qkeccak, p, v⟩ : Verifier.ColumnClaim)) hz.symm

/-! ## The claims on the output lanes -/

/-- The honest lanes' columns are the output lanes', in order. -/
theorem honestLanes_columns (z : Vector E (s.τ 5)) :
    (honestLanes prog s q z).map (·.column) = keccakOutputColumns := by
  rw [keccakOutputColumns_eq, honestLanes, List.map_map]
  show (List.finRange 25).map (fun l : Fin 25 ↦ 106 + l.val) = _
  decide +kernel

/-- **The check on the honest lanes passes.** -/
theorem lanesOk_honestLanes (z : Vector E (s.τ 5)) {claims : List Verifier.ColumnClaim}
    (hl : lanesOf claims = honestLanes prog s q z) : LanesOk claims := by
  refine ⟨by rw [hl, honestLanes_columns], fun c hc ↦ ?_⟩
  rw [hl] at hc ⊢
  obtain ⟨l, -, rfl⟩ := List.mem_map.mp hc
  have h0 : (List.finRange 25).head? = some 0 := rfl
  simp [honestLanes, h0]

/-- Claims on columns below `6` hold no output lane. -/
theorem filter_out_of_lt {l : List Verifier.ColumnClaim} (h : ∀ c ∈ l, c.column < 6) :
    l.filter (fun c ↦ c.column ∈ keccakOutputColumns) = [] := by
  refine List.filter_eq_nil_iff.mpr fun c hc ↦ ?_
  have := h c hc
  simp only [keccakOutputColumns_eq, List.mem_map, List.mem_range, decide_eq_true_eq, not_exists,
    not_and]
  intro l _ he
  omega

/-- **The honest run's lanes**: the bus's and the public input's claims, on the framework's
columns, hold no output lane, so the lanes are the table's. -/
theorem lanesOf_honest {bc tc pc : List Verifier.ColumnClaim} (hb : ∀ c ∈ bc, c.column < 6)
    (hp : ∀ c ∈ pc, c.column < 6) (z : Vector E (s.τ 5))
    (ht : tc.filter (fun c ↦ c.column ∈ keccakOutputColumns) = honestLanes prog s q z) :
    lanesOf (bc ++ tc ++ pc) = honestLanes prog s q z := by
  simp only [lanesOf, List.filter_append, filter_out_of_lt hb, filter_out_of_lt hp, ht,
    List.nil_append, List.append_nil]

/-! ## The phase -/

/-- **The honest prover of the Keccak phase**: nothing for the check, then the reduction's honest
prover on the honest stack's `q_keccak` at the lanes' point and values; it returns what the
program returns. -/
noncomputable def hKeccakPhase (claims : List Verifier.ColumnClaim) :
    Script (List Verifier.ColumnClaim × List E × List E) :=
  (Script.ret ()).bind fun _ ↦
    (hKeccak (s.τ 5 - 4) (qkH prog s q) ((lanesOf claims).headD default).point
        ((lanesOf claims).map (·.value))).bind fun r ↦
      Script.ret (claims.filter (fun c ↦ c.column ∉ keccakOutputColumns) ++ r.1, r.2.1, r.2.2)

/-- **Completeness of the Keccak phase.** On a stack satisfying `M3Holds`, from true claims whose
output lanes are the honest table lanes, the honest prover follows `keccakPhase` at the verifier's
layout: the check passes, the claims returned are true and on no output lane, and the slices are
the true slices of the honest stack's `q_keccak`. -/
theorem follows_keccakPhase {input : PublicInput} (hq : M3Holds (inst prog s) input q)
    {claims : List Verifier.ColumnClaim} (htrue : TrueClaims prog s q claims)
    (z : Vector E (s.τ 5)) (hl : lanesOf claims = honestLanes prog s q z) (cs : Commits) :
    Follows (fun cs' a b ↦ cs' = cs ∧ a = b ∧
        (∀ c ∈ b.1, TrueClaim prog s q c ∧ c.column ∉ keccakOutputColumns) ∧
        slicesTrue (s.τ 5) (qkH prog s q) b.2.1 b.2.2 ∧ b.1.length ≤ claims.length + 1)
      (hKeccakPhase prog s q claims) (keccakPhaseClaims (verifierLayout prog s) claims) cs := by
  have hP : s.τ 5 - 4 + 4 = s.τ 5 := by
    have := s.minSteps_le
    simp only [keccakMinStepsLog] at this
    omega
  have hok := lanesOk_honestLanes prog s q z hl
  have hinst : ((lanesOf claims).headD default).point = z.toList := by
    have h0 : (List.finRange 25).head? = some 0 := rfl
    rw [hl]; simp [honestLanes, h0]
  have hout : (lanesOf claims).map (·.value) = (honestLanes prog s q z).map (·.value) := by
    rw [hl]
  rw [keccakPhase_eq, tableLogHeights_keccak]
  unfold hKeccakPhase
  refine Follows.bind (fun cs₁ _ _ h₁ ↦ ?_) _ _ _
    (Follows.ret_require (R := fun cs' _ _ ↦ cs' = cs) hok rfl)
  subst h₁
  have e : verifyKeccak (s.τ 5) ((lanesOf claims).headD default).point
      ((lanesOf claims).map (·.value)) = verifyKeccak (s.τ 5 - 4 + 4)
        ((lanesOf claims).headD default).point ((lanesOf claims).map (·.value)) := by
    rw [hP]
  rw [e]
  have hi : ((lanesOf claims).headD default).point.length = s.τ 5 - 4 + 4 := by
    rw [hinst, hP]; simp
  have ho : ((lanesOf claims).map (·.value)).length = 25 := by
    rw [hout]; simp [honestLanes]
  have hmid : outClaimsTrueMid (s.τ 5 - 4 + 4) (qkH prog s q) ((lanesOf claims).headD default).point
      ((lanesOf claims).map (·.value)) := by
    rw [hP, hinst, hout]; exact outClaimsTrueMid_honest prog s q z
  have hagree : midAgree (s.τ 5 - 4 + 4) (qkH prog s q) ((lanesOf claims).headD default).point := by
    rw [hP, hinst]; exact midAgree_honest prog s q hq z
  refine Follows.bind (fun cs₂ a b h₂ ↦ ?_) _ _ _
    (follows_keccak (s.τ 5 - 4) (qkH prog s q) hi ho hmid hagree cs₁)
  obtain ⟨rfl, rfl, hcol, hsl, hlen1⟩ := h₂
  refine ⟨rfl, rfl, fun c hc ↦ ?_, by rw [hP] at hsl; exact hsl, ?_⟩
  swap
  · rw [List.length_append, hlen1]
    exact Nat.add_le_add_right (List.length_filter_le _ _) 1
  rcases List.mem_append.mp hc with hc | hc
  · obtain ⟨hmem, hnot⟩ := List.mem_filter.mp hc
    exact ⟨htrue c hmem, by simpa using hnot⟩
  · have hct := hcol c hc
    rw [hP] at hct
    refine ⟨trueClaim_of_colTrue prog s q hct, ?_⟩
    rw [hct.1]
    decide +kernel

end
end LeanVM.Protocol.EndToEnd.Complete
