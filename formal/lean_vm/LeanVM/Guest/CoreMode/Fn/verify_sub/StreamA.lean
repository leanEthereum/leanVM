/-
  LeanVM.Guest.CoreMode.Fn.verify_sub.StreamA

  `verify_sub`'s proof stream family, sound at the honest instances of b2c's aligned tree, given that every listed
  read lies before its end cursor (`VsStreamQ`): its end check `assert log(cursor / stream) <
  log(stream_chunks^STREAM_CHUNK·g)` bounds the end cursor by the stream's `256·e(stream_chunks)` words.
-/

module

public import LeanVM.Guest.EndExecExpCA
public import LeanVM.Guest.CoreMode.Fn.verify_sub.Stream
public import LeanVM.Guest.CoreMode.Fn.column_selector.CsChain

/-!
# The proof stream's reads

At an honest instance of `verify_sub`, its range check of `stream_chunks` (value `42`) gives `g^n`, `n ≤ 32`; its end
check, the atoms `4004 = 42^256` (eight squarings), `4006 = 4004·g`, `4008 = 4006·g⁻¹` and `rangeCheck 4009 … 4008`
(`cursor@5 = 3996 = 4009·stream`), gives `4009 = g^E`, `E ≤ 256·n` (`vs_end`). So a cell `stream·g^j`, `j < E`, is a
cell of `streamQ` (`streamQ_set`).

`VsStreamQ` (proved in `OsCur.lean`): every read the family places in the stream (`streamCell`) and every cell of every run
it places there (`streamRun`), under the site's branch conditions, is `stream·g^j` with `j` below the end cursor's
`E`, by the cursor's advances (each by a nonnegative exponent) between the read and the end. `streamFam_okA`: the
family from it.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.CoreMode (CCond CRes CRun)
open LeanVM.Guest.CoreMode.Own.verify_sub (streamQ streamFam)

@[expose] public section

/-- **The stream family's reads before the end**: at every honest instance of `verify_sub` whose end cursor's quotient by
the stream (value `4009`, `cursor@5 = 4009·stream`) is `g^E`, where branch conditions `g` hold, each read the family
places in the stream (`streamCell g`) is `stream·g^j`, and so is each cell of each run it places there (`streamRun g`),
`j < E`: the cursor only advances (each callee's returned cursor its argument times `g^k`, `k ≥ 0`) from the read to
the end. -/
def VsStreamQ (al : String → Bool) (D : Ref → RefD) : Prop :=
  ∀ {r : Ref}, RefH (layB al) (D r) r → r.Ok → ∀ I ∈ instsR al D r, ∀ σ bufs kids,
    I.t = .node name% «verify_sub» σ bufs kids → ∀ E, σ (.n 4009) = gen ^ E → ∀ g : List CCond, (∀ x ∈ g, x.Holds σ) →
      (∀ c, CoreMode.Own.verify_sub.streamCell g c = true →
        ∃ j < E, c.addrW (CoreMode.vw σ) = (σ (.n 55) * gen ^ j).limb 0) ∧
      ∀ q, CoreMode.Own.verify_sub.streamRun g q = true → ∀ x, q.Set (CoreMode.vw σ) x →
        ∃ j < E, x = (σ (.n 55) * gen ^ j).limb 0

end

public section

/-- `verify_sub`'s range check of `stream_chunks` and its end check's atoms. -/
def vsEndAtoms : List Atom :=
  [.rangeCheck (.n 42) (.n 44) (.n 45) (.n 46) (.n 43), .const (.n 43) (word (2 ^ 32) 0),
    .mul (.n 3997) (.n 42) (.n 42), .mul (.n 3998) (.n 3997) (.n 3997), .mul (.n 3999) (.n 3998) (.n 3998),
    .mul (.n 4000) (.n 3999) (.n 3999), .mul (.n 4001) (.n 4000) (.n 4000), .mul (.n 4002) (.n 4001) (.n 4001),
    .mul (.n 4003) (.n 4002) (.n 4002), .mul (.n 4004) (.n 4003) (.n 4003), .const (.n 4005) (word 2 0),
    .mul (.n 4006) (.n 4004) (.n 4005), .const (.n 4007) (word 9223372036854775821 0),
    .mul (.n 4008) (.n 4006) (.n 4007), .rangeCheck (.n 4009) (.n 4010) (.n 4011) (.n 4012) (.n 4008)]

theorem vs_end_atoms : vsEndAtoms.all (fun a ↦ (Res.topAtoms (fn% «verify_sub»).body).contains a) = true := by
  decide +kernel

/-- **The stream's length and the end cursor** at a valuation holding `verify_sub`'s atoms: `stream_chunks = g^n`,
`n ≤ 32`, and the end cursor's quotient `4009 = g^E`, `E ≤ 256·n`. -/
theorem vs_end {rd : Reader} (hm : B1.Digest.MemOk rd) {σ : Val}
    (hall : ∀ a ∈ Res.topAtoms (fn% «verify_sub»).body, a.Holds rd σ) :
    ∃ n E, n ≤ 32 ∧ σ (.n 42) = gen ^ n ∧ σ (.n 4009) = gen ^ E ∧ E ≤ 256 * n := by
  have H : ∀ a ∈ vsEndAtoms, a.Holds rd σ := fun a ha ↦
    hall a (List.contains_iff_mem.mp (List.all_eq_true.mp vs_end_atoms a ha))
  have a0 : (Atom.rangeCheck (.n 42) (.n 44) (.n 45) (.n 46) (.n 43)).Holds rd σ := H _ (by simp [vsEndAtoms])
  have a1 : (Atom.const (.n 43) (word (2 ^ 32) 0)).Holds rd σ := H _ (by simp [vsEndAtoms])
  have a2 : (Atom.mul (.n 3997) (.n 42) (.n 42)).Holds rd σ := H _ (by simp [vsEndAtoms])
  have a3 : (Atom.mul (.n 3998) (.n 3997) (.n 3997)).Holds rd σ := H _ (by simp [vsEndAtoms])
  have a4 : (Atom.mul (.n 3999) (.n 3998) (.n 3998)).Holds rd σ := H _ (by simp [vsEndAtoms])
  have a5 : (Atom.mul (.n 4000) (.n 3999) (.n 3999)).Holds rd σ := H _ (by simp [vsEndAtoms])
  have a6 : (Atom.mul (.n 4001) (.n 4000) (.n 4000)).Holds rd σ := H _ (by simp [vsEndAtoms])
  have a7 : (Atom.mul (.n 4002) (.n 4001) (.n 4001)).Holds rd σ := H _ (by simp [vsEndAtoms])
  have a8 : (Atom.mul (.n 4003) (.n 4002) (.n 4002)).Holds rd σ := H _ (by simp [vsEndAtoms])
  have a9 : (Atom.mul (.n 4004) (.n 4003) (.n 4003)).Holds rd σ := H _ (by simp [vsEndAtoms])
  have a10 : (Atom.const (.n 4005) (word 2 0)).Holds rd σ := H _ (by simp [vsEndAtoms])
  have a11 : (Atom.mul (.n 4006) (.n 4004) (.n 4005)).Holds rd σ := H _ (by simp [vsEndAtoms])
  have a12 : (Atom.const (.n 4007) (word 9223372036854775821 0)).Holds rd σ := H _ (by simp [vsEndAtoms])
  have a13 : (Atom.mul (.n 4008) (.n 4006) (.n 4007)).Holds rd σ := H _ (by simp [vsEndAtoms])
  have a14 : (Atom.rangeCheck (.n 4009) (.n 4010) (.n 4011) (.n 4012) (.n 4008)).Holds rd σ :=
    H _ (by simp [vsEndAtoms])
  simp only [Atom.Holds] at a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
  obtain ⟨n, hn, h42⟩ := B1.Digest.rc_const hm (c := 32) (by norm_num)
    (a1.trans (B1.word_two_pow (a := 32) (by norm_num))) a0
  have hg : word 2 0 = gen := by
    have := B1.word_two_pow (a := 1) (by norm_num); simpa using this
  have h4004 : σ (.n 4004) = σ (.n 42) ^ 256 := by
    rw [a9, a8, a7, a6, a5, a4, a3, a2]; ring
  have h4006 : σ (.n 4006) = gen ^ (256 * n + 1) := by
    rw [a11, h4004, a10, hg, h42]; ring
  obtain ⟨E, hE, hb⟩ := B1.Digest.rc_below hm (b := σ (.n 4006)) (by rw [a13, a12]) a14
  exact ⟨n, E, hn, h42, hE, by have := B1.Digest.belowLog_lt (by omega) h4006 hb; omega⟩

/-- **A cell `stream·g^j` before the end is a cell of the stream's run.** -/
theorem streamQ_set {σ : Val} {n M j : ℕ} (hn : n ≤ 32) (h42 : σ (.n 42) = gen ^ n) (hM : M ≤ 256 * n) (hj : j < M) :
    streamQ.Set (CoreMode.vw σ) ((σ (.n 55) * gen ^ j).limb 0) := by
  refine ⟨0, 256 * n, j, CoreMode.rep_const (by unfold CoreMode.capE; norm_num), ?_, Nat.zero_le _, by omega, ?_⟩
  · have e1 : CoreMode.CCell.valW (CoreMode.vw σ) ⟨[(42, 256)], 0⟩ = ofK (addressOfIndex (256 * n)) := by
      simp only [CoreMode.CCell.valW, CoreMode.prodW, CoreMode.vw, h42, mul_one, addressOfIndex, pow_zero]
      rw [← Value.gen_pow_eq_ofK, ← pow_mul, mul_comm n 256, show ofK (1 : Parameters.K) = 1 from map_one (algebraMap Parameters.K Parameters.E), mul_one]
    show CoreMode.rep (CoreMode.idxC (.mono ⟨[(42, 256)], 0⟩) |>.valW (CoreMode.vw σ)) = some (256 * n)
    simp only [CoreMode.idxC]
    rw [e1]
    exact CoreMode.rep_of (by unfold CoreMode.capE; omega)
  · simp only [streamQ, CoreMode.CCell.valW, CoreMode.prodW, CoreMode.vw, pow_one, mul_one, addressOfIndex,
      pow_zero, one_mul, Value.gen_pow_eq_ofK, show ofK (1 : Parameters.K) = 1 from map_one (algebraMap Parameters.K Parameters.E)]

/-- **The family under branch conditions**, at a valuation whose stream reads lie before the end. -/
theorem streamFamU_holds {σ : Val} {n E : ℕ} (hn : n ≤ 32) (h42 : σ (.n 42) = gen ^ n) (hEn : E ≤ 256 * n)
    (hQ : ∀ g : List CCond, (∀ x ∈ g, x.Holds σ) →
      (∀ c, CoreMode.Own.verify_sub.streamCell g c = true →
        ∃ j < E, c.addrW (CoreMode.vw σ) = (σ (.n 55) * gen ^ j).limb 0) ∧
      ∀ q, CoreMode.Own.verify_sub.streamRun g q = true → ∀ x, q.Set (CoreMode.vw σ) x →
        ∃ j < E, x = (σ (.n 55) * gen ^ j).limb 0) :
    ∀ (x : CRes) (g : List CCond), CoreMode.Own.verify_sub.streamFamU g x = true → (∀ y ∈ g, y.Holds σ) →
      x.Holds σ := by
  intro x
  induction x with
  | sub c q =>
    intro g hx hg
    simp only [CoreMode.Own.verify_sub.streamFamU, Bool.and_eq_true, decide_eq_true_eq] at hx
    obtain ⟨rfl, hm⟩ := hx
    obtain ⟨j, hj, he⟩ := (hQ g hg).1 c hm
    show streamQ.Set _ (c.addrW _)
    rw [he]
    exact streamQ_set hn h42 hEn hj
  | subR q q' =>
    intro g hx hg
    simp only [CoreMode.Own.verify_sub.streamFamU, Bool.and_eq_true, decide_eq_true_eq] at hx
    obtain ⟨rfl, hm⟩ := hx
    intro y hy
    obtain ⟨j, hj, rfl⟩ := (hQ g hg).2 q hm y hy
    exact streamQ_set hn h42 hEn hj
  | under g' r' ih =>
    intro g hx hg hg'
    exact ih (g ++ g') hx fun y hy ↦ (List.mem_append.mp hy).elim (hg y) (hg' y)
  | lt a b =>
    intro g hx hg
    have ha : a = .num 0 ∧ b = .val 42 := by
      simpa [CoreMode.Own.verify_sub.streamFamU] using hx
    obtain ⟨rfl, rfl⟩ := ha
    obtain ⟨j, hj, -⟩ := (hQ [] (by simp)).1 ⟨[(1076, 1)], 0⟩ (by decide)
    exact ⟨0, n, CoreMode.rep_const (by unfold CoreMode.capE; norm_num),
      rep_val_gen h42 (by unfold CoreMode.capE; omega), by omega⟩
  | nz _ | subP _ _ | eq _ _ => intro g hx; simp [CoreMode.Own.verify_sub.streamFamU] at hx

/-- **The stream family, given `VsStreamQ`**, on `verify_sub`'s honest instances, aligned. -/
theorem streamFam_okA {al : String → Bool} {D : Ref → RefD} (hQ : VsStreamQ al D) :
    OwnOkA al D (name% «verify_sub», fun _ r ↦ streamFam r) := by
  intro r hR hr I hI σ bufs kids ht fn hf x hx
  obtain rfl : fn = fn% «verify_sub» := Option.some.inj (hf.symm.trans find_vs)
  obtain ⟨args, rets, hv⟩ := inst_validA hR hI ht
  obtain ⟨fn', hf', -, es, vs, hw, -, hh, -⟩ := hv
  obtain rfl : fn% «verify_sub» = fn' := Option.some.inj (find_vs.symm.trans hf')
  have hall : ∀ a ∈ Res.topAtoms (fn% «verify_sub»).body, a.Holds r.img.read σ :=
    fun a ha ↦ hh _ (topAtoms_on_path hw ha)
  obtain ⟨n, E, hn, h42, hE, hEn⟩ := vs_end (ref_memOkA hR hr) hall
  exact streamFamU_holds hn h42 hEn (hQ hR hr I hI σ bufs kids ht E hE) x [] hx (by simp)

end

end LeanVM.Guest.EndExec
