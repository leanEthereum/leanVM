module

public import NativeVm.Code.Phase7.Frame
public import NativeVm.Code.Phase7.QueryBits

/-!
# Phase 7: the query positions

`sampleQueriesC` runs `sampleQueries depth count` (`NativeVm.Model.Whir`): the depth and the count
in the scratch words `cDepth`, `cK`, the positions stored as a `WVec` in `queriesR` (the count word,
then the positions). The count goes to the count word first; then, while positions remain (`r15`),
a challenge is sampled and `qchunkC` stores its positions at `r14`, both registers kept by the
sample gadget. The loop's invariant (`SqInv`) says the whole run is the prefix stored so far
followed by the run of `sampleQueriesAux` on what remains; each pass takes at least one position,
so the fuel `count` is enough.
-/

@[expose] public section

namespace NativeVm.Code.P7

open Native NativeVm.Model LeanVM.Parameters NativeVm.Code
open NativeVm.Transcript (wd Fits Env ctxWork wd_inj eval_cw wp_load wp_store wp_reg isSome_setMem
  toUInt64_inj toNat_toUInt64 clobbers wp_then)

/-! ## The model -/

theorem sampleQueriesAux_keepsRoots (depth : Nat) :
    ∀ fuel rem, KeepsRoots (sampleQueriesAux depth fuel rem)
  | 0, _ => KeepsRoots.pure _
  | fuel + 1, rem => by
    unfold sampleQueriesAux
    split
    · exact KeepsRoots.pure _
    · exact KeepsRoots.bind KeepsRoots.sampleChallenge fun _ ↦
        KeepsRoots.bind (sampleQueriesAux_keepsRoots depth fuel _) fun _ ↦ KeepsRoots.pure _

theorem sampleQueries_keepsRoots (depth count : Nat) : KeepsRoots (sampleQueries depth count) :=
  sampleQueriesAux_keepsRoots depth count count

theorem sqAux_zero (depth fuel : Nat) (t : TState) :
    (sampleQueriesAux depth fuel 0).run t = some (#[], t) := by
  cases fuel <;> rfl

/-- One pass of `sampleQueriesAux`, the challenge sampled. -/
theorem sqAux_succ {depth fuel rem : Nat} (hr : rem ≠ 0) {t t1 : TState} {c : EW}
    (hs : Model.sampleChallenge.run t = some (c, t1)) :
    (sampleQueriesAux depth (fuel + 1) rem).run t =
      ((sampleQueriesAux depth fuel (rem - min (128 / depth) rem)).run t1).map fun q ↦
        ((Array.range (min (128 / depth) rem)).map (fun i ↦ queryBits c (i * depth) depth) ++ q.1,
          q.2) := by
  rw [sampleQueriesAux, ite_eq_right hr]
  simp only [StateT.run_bind, hs]
  cases h : (sampleQueriesAux depth fuel (rem - min (128 / depth) rem)).run t1 <;> simp [h]

theorem sq_sample_some (t : TState) : Model.sampleChallenge.run t ≠ none := by
  simp [Model.sampleChallenge]

/-! ## The code -/

/-- **The query positions**: `sampleQueries depth count`, `depth` at `cDepth`, `count` at `cK`, as
a `WVec` at `queriesR`. -/
def sampleQueriesC : Stmt := blk [
  ldW, ldw .r15 cK, stw queriesR.off .r15, leaw .r14 (queriesR.off + 1),
  .loop (.test false .r15 (.reg .r15)) (blk [Transcript.sampleChallenge, ldw .rcx cDepth, qchunkC])]

/-- The words `sampleQueriesC` writes: the queries' `WVec`. -/
abbrev qW : Nat → Prop := fun k ↦ queriesR.off ≤ k ∧ k < queriesR.off + wvecWords queryCap

/-- The words the loop keeps: the depth, the count, the positions so far, the frame. -/
def SqMem (p : Par) (m0 : UInt64 → Option UInt64) (depth count : Nat) (acc : Array UInt64)
    (mem : UInt64 → Option UInt64) : Prop :=
  NatAt mem (wd p.env.work cDepth) depth ∧ NatAt mem (wd p.env.work queriesR.off) count ∧
    (∀ k (h : k < acc.size), mem (wd p.env.work (queriesR.off + 1 + k)) = some acc[k]) ∧
    Only p.env qW m0 mem

/-- The loop's invariant: the prefix `acc` stored, `rem` positions left, the whole run the prefix
then `sampleQueriesAux`'s on what is left. -/
def SqInv (p : Par) (m0 : UInt64 → Option UInt64) (depth count : Nat) (t0 : TState) (s : QState) :
    Prop :=
  ∃ (acc : Array UInt64) (rem f : Nat) (t : TState), rem ≤ f ∧ acc.size + rem = count ∧
    (sampleQueries depth count).run t0 =
      ((sampleQueriesAux depth f rem).run t).map (fun q ↦ (acc ++ q.1, q.2)) ∧
    Base p t s ∧ s.reg .rbp = p.env.work ∧ s.reg .r15 = rem.toUInt64 ∧
    s.reg .r14 = wd p.env.work (queriesR.off + 1 + acc.size) ∧ SqMem p m0 depth count acc s.mem

variable {env : Env} {p : Par}

theorem sqMem_mine {m0 : UInt64 → Option UInt64} {depth count : Nat} {acc : Array UInt64}
    (hacc : acc.size ≤ queryCap) : MineOnly p.env (SqMem p m0 depth count acc) := by
  intro m m' hm ⟨d, c, ps, on⟩
  have e : ∀ k, mineLo ≤ k → k < dataEnd → m' (wd p.env.work k) = m (wd p.env.work k) :=
    fun k h1 h2 ↦ hm _ (inMine_wd h1 h2)
  have qo := queries_off; have so := scratch_off; have ml := mineLo_val; have de := dataEnd_eq
  have qc : queryCap = 230 := rfl
  have cd : cDepth = scratchR.off + 4 := rfl
  refine ⟨⟨d.1, by rw [e _ (by omega) (by omega)]; exact d.2⟩,
    ⟨c.1, by rw [e _ (by omega) (by omega)]; exact c.2⟩,
    fun k hk ↦ by rw [e _ (by omega) (by omega)]; exact ps k hk,
    fun k h1 h2 hk ↦ by rw [e k h1 h2]; exact on k h1 h2 hk⟩

/-- **`sampleQueriesC` runs `sampleQueries`.** -/
theorem sampleQueriesC_spec {p : Par} {m0 : UInt64 → Option UInt64} {depth count : Nat}
    (hd1 : 1 ≤ depth) (hd : depth < 64) (hc : count ≤ queryCap) :
    Refines (fun t s ↦ Base p t s ∧ s.mem = m0 ∧ NatAt s.mem (wd p.env.work cDepth) depth ∧
        NatAt s.mem (wd p.env.work cK) count)
      sampleQueriesC (sampleQueries depth count)
      (fun qs t s ↦ Base p t s ∧ WVec s.mem (wd p.env.work queriesR.off) queryCap qs ∧
        qs.size = count ∧
        Only p.env (fun k ↦ queriesR.off ≤ k ∧ k < queriesR.off + wvecWords queryCap) m0 s.mem)
      (Err p) := by
  intro t0 s ⟨hb, hm0, hdep, hcnt⟩
  subst hm0
  have qo := queries_off; have so := scratch_off; have ml := mineLo_val; have de := dataEnd_eq
  have qc : queryCap = 230 := rfl
  have hww := workWords_ge p.inp.bytecode.size
  have wv : wvecWords queryCap = 231 := rfl
  have cd : cDepth = scratchR.off + 4 := rfl
  have ck : cK = scratchR.off + 7 := rfl
  unfold sampleQueriesC ldW ldw stw leaw
  refine wp_load (eval_cw hb.rdi ctxWork) hb.workPtr ?_
  have b1 : (s.setReg .rbp p.env.work).reg .rbp = p.env.work := by rsimp
  refine wp_load (eval_w b1 cK) hcnt.2 ?_
  have b2 : ((s.setReg .rbp p.env.work).setReg .r15 count.toUInt64).reg .rbp = p.env.work := by
    rsimp
  have hs0 : (s.mem (wd p.env.work queriesR.off)).isSome :=
    hb.inp.workSome _ (by omega)
  refine wp_store (eval_w b2 queriesR.off) hs0 ?_
  refine wp_reg rfl ?_
  rw [eval_w (env := p.env) (by rsimp) (queriesR.off + 1)]
  refine WP.loop (SqInv p s.mem depth count t0) (fun s ↦ (s.reg .r15).toNat) ?_ ?_ ?_
  · -- the start
    refine ⟨#[], count, count, t0, le_rfl, by simp, ?_, ?_, by rsimp, by rsimp, by rsimp; rfl, ?_⟩
    · unfold sampleQueries
      cases (sampleQueriesAux depth count count).run t0 <;> simp
    · exact hb.frM ((((frM_setReg (r := .rbp) (by decide) _).trans
        (frM_setReg (r := .r15) (by decide) _)).trans (frM_store (s := (s.setReg .rbp p.env.work).setReg .r15 count.toUInt64)
        (by omega) (by omega) hs0 _)).trans
        (frM_setReg (r := .r14) (by decide) _))
    · refine ⟨⟨hdep.1, ?_⟩, ⟨hcnt.1, ?_⟩, fun k hk ↦ absurd hk (by simp), ?_⟩
      · rsimp
        rw [QState.setMem_mem, ite_eq_right (fun e ↦ by
          have := (wd_inj (by omega) (by omega)).mp e; omega)]
        exact hdep.2
      · rsimp
        rw [QState.setMem_mem, ite_eq_left rfl]
      · have := Only.store (env := p.env) (Only.refl qW s.mem) (k := queriesR.off)
          ⟨le_rfl, by rw [wv]; omega⟩ (by omega) count.toUInt64
        rsimp
        exact this
  · -- a pass
    intro u ⟨acc, rem, f, t, hf, hsz, hrun, hb, hbp, h15, h14, hM⟩ hcond
    have hne : u.reg .r15 ≠ 0 := fun h0 ↦ by simp [Cond.eval, Rhs.eval, h0] at hcond
    have hrem0 : rem ≠ 0 := fun h ↦ hne (by rw [h15, h]; rfl)
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    have hacc : acc.size ≤ queryCap := by omega
    have hR : GOk p.env p.inp fun v ↦ v.reg .rbp = p.env.work ∧ v.reg .r15 = rem.toUInt64 ∧
        v.reg .r14 = wd p.env.work (queriesR.off + 1 + acc.size) ∧
        SqMem p s.mem depth count acc v.mem :=
      (GOk.reg (by decide) _).and ((GOk.reg (by decide) _).and
        ((GOk.reg (by decide) _).and (GOk.of_mine (sqMem_mine hacc))))
    refine wp_then (WP.mono (sample_b hR t u ⟨hb, hbp, h15, h14, hM⟩) (fun _ h ↦ h)
      (fun _ ⟨hr, _⟩ ↦ absurd hr (sq_sample_some t)))
      fun u1 ⟨c, t1, hsr, hb1, ⟨b1, r1, q1, hM1⟩, h9, h10⟩ ↦ ?_
    refine wp_load (eval_w b1 cDepth) hM1.1.2 ?_
    have hn1 : 1 ≤ min (128 / depth) rem :=
      le_min ((Nat.le_div_iff_mul_le hd1).mpr (by omega)) (by omega)
    have hnr : min (128 / depth) rem ≤ rem := min_le_right _ _
    have hDk : ∀ k, wd (wd p.env.work (queriesR.off + 1 + acc.size)) k =
        wd p.env.work (queriesR.off + 1 + acc.size + k) := fun k ↦ wd_wd _ _ _
    refine WP.mono (qchunkC_spec (s := u1.setReg .rcx depth.toUInt64) (c := c)
      (D := wd p.env.work (queriesR.off + 1 + acc.size))
      (by rsimp; exact h9) (by rsimp; exact h10) (by rsimp) hd1 hd (by rsimp; exact r1) (by omega)
      (by rsimp; exact q1)
      (fun k hk ↦ by rw [hDk]; exact hb1.inp.workSome _ (by omega))
      (Transcript.Fits.sub hb1.inp.fitWork (by omega) (by omega))) ?_ (fun _ h ↦ h)
    rintro u3 ⟨hW, h14', h15', hf3, -, hmem3⟩
    have hkeep : ∀ j, (j < queriesR.off + 1 + acc.size ∨
        queriesR.off + 1 + acc.size + min (128 / depth) rem ≤ j) → j < 2 ^ 61 →
        u3.mem (wd p.env.work j) = u1.mem (wd p.env.work j) := fun j hj hj' ↦
      hmem3 _ fun k hk e ↦ by
        rw [hDk, wd_inj hj' (by omega)] at e
        omega
    have hfrm : FrM p.env u1 u3 := by
      refine ⟨by rw [hf3 .rdi (by decide)]; rsimp, fun a ↦ ?_, fun a ha ↦ hmem3 a fun k hk e ↦
        ha (by rw [e, hDk]; exact inMine_wd (by omega) (by omega))⟩
      by_cases hin : ∃ k < min (128 / depth) rem, 
          a = wd (wd p.env.work (queriesR.off + 1 + acc.size)) k
      · obtain ⟨k, hk, rfl⟩ := hin
        rw [hW k (by simpa using hk), hDk]
        exact (hb1.inp.workSome _ (by omega)).symm
      · rw [hmem3 a fun k hk e ↦ hin ⟨k, hk, e⟩]
        rfl
    refine ⟨⟨acc ++ (Array.range (min (128 / depth) rem)).map
        (fun i ↦ queryBits c (i * depth) depth), rem - min (128 / depth) rem, f', t1, by omega,
        by simp only [Array.size_append, Array.size_map, Array.size_range]; omega, ?_, hb1.frM hfrm,
        by rw [hf3 .rbp (by decide)]; rsimp; exact b1, h15', ?_, ?_⟩, ?_⟩
    · rw [hrun, sqAux_succ hrem0 hsr, Option.map_map]
      congr 1
      funext q
      simp [Array.append_assoc]
    · rw [h14', hDk]
      congr 1
      simp only [Array.size_append, Array.size_map, Array.size_range]
      omega
    · refine ⟨⟨hM1.1.1, by rw [hkeep _ (by omega) (by omega)]; exact hM1.1.2⟩,
        ⟨hM1.2.1.1, by rw [hkeep _ (by omega) (by omega)]; exact hM1.2.1.2⟩, fun k hk ↦ ?_,
        fun j h1 h2 hj ↦ ?_⟩
      · simp only [Array.size_append, Array.size_map, Array.size_range] at hk
        by_cases hka : k < acc.size
        · rw [Array.getElem_append_left hka, hkeep _ (by omega) (by omega)]
          exact hM1.2.2.1 k hka
        · have := hW (k - acc.size) (by simp; omega)
          rw [hDk, show queriesR.off + 1 + acc.size + (k - acc.size) = queriesR.off + 1 + k by omega]
            at this
          rw [this, Array.getElem_append_right (by omega)]
      · have hj' : ¬ (queriesR.off ≤ j ∧ j < queriesR.off + 231) := by rw [← wv]; exact hj
        rw [hkeep j (by omega) (by omega)]
        exact hM1.2.2.2 j h1 h2 hj
    · rw [h15', h15, toNat_toUInt64 (by omega), toNat_toUInt64 (by omega)]
      omega
  · -- the end
    intro s ⟨acc, rem, f, t, hf, hsz, hrun, hb, hbp, h15, h14, hM⟩ hcond
    have hrem0 : rem = 0 := by
      have : s.reg .r15 = 0 := by simpa [Cond.eval, Rhs.eval] using hcond
      rw [h15] at this
      exact (toUInt64_inj (b := 0) (by omega) (by omega)).mp this
    subst hrem0
    rw [sqAux_zero, Option.map_some, Array.append_empty] at hrun
    refine ⟨acc, t, hrun, hb, ⟨by omega, ⟨by omega, ?_⟩, fun k hk ↦ ?_⟩, by omega, hM.2.2.2⟩
    · rw [show acc.size = count by omega]; exact hM.2.1.2
    · rw [wd_wd, wd_wd, ← Nat.add_assoc]
      exact hM.2.2.1 k hk

end NativeVm.Code.P7
