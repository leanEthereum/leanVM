/-
  LeanVM.Guest.B1.VsC.VkInvOs

  `VkInv` in the run world of `VsC/Os/RunF` (the native chain's): `verifyKeccak`'s accepting run read
  back, and the shape of its result.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.LayerSpec
public import LeanVM.Guest.B1.KeccakGkr.VkSpec
public import LeanVM.Guest.B1.VsC.VsNatTail
public import LeanVM.Guest.B1.KeccakGkr.LocalRounds

/-!
# Runs read back, in the native chain's run world

`Tables/RunF.lean` and `VsC/Os/RunF.lean` declare the same names, so no module imports both, and
`VkInv` (the first) cannot serve `natTail` (the second). This is `VkInv` over the second, its proofs
unchanged but `runsTo_toT` (from `NoPacked`), with `vi_vkRes` (`vi_vk` at any result) and `vk_shape`
(an accepting run's result is one output claim, a point and `64` slices, its end sponge's queue full).


An accepting run from a carried sponge is the carried run (`runsTo_toT`, `Tables.runT`), which is
deterministic: the reads, samples and `require`s read back from it (`vi_readE`, `vi_readN`,
`vi_require`), the pack rounds (`vi_pack`: `packRunF`), the position rounds (`vi_local`:
`localRunF`), the plain rounds (`vi_plain`: `plainRun`), and a layer (`vi_layer`): its product,
its nonce, its messages, `t`, its two checks, the claim it returns (`layerClaim`) and the sponge
after it; and `verifyKeccak` (`vi_vk`).
-/

namespace LeanVM.Guest.B1.VsC.VkOs

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr LeanVM.Guest.B1.Tables LeanVM.Guest.B1.VerifySub

@[expose] public section

/-! ## The carried run -/

/-- **An accepting run is the carried run.** -/
theorem runsTo_toT {α : Type} {p : VerifierProgram α} {s s' : Fs} {xs : List E} {a : α}
    (hpf : NoPacked p) (h : RunsTo p s xs a s') {sp : Sponge} (hc : s.Carries sp) :
    runT p ⟨s, none, xs, [], []⟩ = some (a, ⟨s', none, [], [], []⟩) := by
  obtain ⟨sp', hc', he⟩ := h sp hc [] [] []
  simp only [List.append_nil] at he
  rw [runT_of_runId p hpf ⟨s, none, xs, [], []⟩ sp (tcar_none.mpr hc) a _ he]
  obtain ⟨e1, e2⟩ := eq_fsOfT (tcar_none.mpr hc')
  rw [← e1, ← e2]

theorem vi_bind {α β : Type} {p : VerifierProgram α} {f : α → VerifierProgram β} {st st'' : TSt}
    {b : β}
    (h : runT (p >>= f) st = some (b, st'')) :
    ∃ a st', runT p st = some (a, st') ∧ runT (f a) st' = some (b, st'') := by
  rw [prog_bind_eq, runT_bind] at h
  obtain ⟨⟨a, st'⟩, h1, h2⟩ := Option.bind_eq_some_iff.mp h
  exact ⟨a, st', h1, h2⟩

theorem vi_pure {α : Type} {a b : α} {st st' : TSt}
    (h : runT (pure a : VerifierProgram α) st = some (b, st')) : b = a ∧ st' = st := by
  change runT (VerifierProgram.ret a) st = some (b, st') at h
  simp only [runT, Option.some.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.symm⟩

theorem vi_ret {α : Type} {a b : α} {st st' : TSt}
    (h : runT (VerifierProgram.ret a) st = some (b, st')) : b = a ∧ st' = st := vi_pure h

theorem vi_readE {s : Fs} {zs : List E} {os : List (List Opening)} {R : List (Digest × ℕ × ℕ)}
    {x : E} {st' : TSt} (h : runT VerifierProgram.readScalar ⟨s, none, zs, os, R⟩ = some (x, st')) :
    ∃ zs', zs = x :: zs' ∧ st' = ⟨s.absorb x dsObserve, none, zs', os, R⟩ := by
  cases zs with
  | nil => simp [VerifierProgram.readScalar, runT] at h
  | cons z zs' =>
    simp only [VerifierProgram.readScalar, runT, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨zs', rfl, rfl⟩

theorem vi_sampleE (s : Fs) (zs : List E) (os : List (List Opening)) (R : List (Digest × ℕ × ℕ)) :
    runT VerifierProgram.sampleChallenge ⟨s, none, zs, os, R⟩ =
      some (s.squeeze.1, ⟨s.squeeze.2, none, zs, os, R⟩) :=
  rfl

theorem vi_sampleE' {s : Fs} {zs : List E} {os : List (List Opening)} {R : List (Digest × ℕ × ℕ)}
    {st' : TSt} {x : E} (h : runT VerifierProgram.sampleChallenge ⟨s, none, zs, os, R⟩ = some (x, st')) :
    x = s.squeeze.1 ∧ st' = ⟨s.squeeze.2, none, zs, os, R⟩ := by
  rw [vi_sampleE] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.symm⟩

/-- `n` reads take the next `n` words, absorbed. -/
theorem vi_readN : ∀ (n : ℕ) (s : Fs) (zs : List E) (os : List (List Opening))
    (R : List (Digest × ℕ × ℕ)) (xs : List E) (st' : TSt),
    runT (VerifierProgram.readScalars n) ⟨s, none, zs, os, R⟩ = some (xs, st') →
      ∃ rest, xs.length = n ∧ zs = xs ++ rest ∧ st' = ⟨s.absorbAll xs dsObserve, none, rest, os, R⟩
  | 0, s, zs, os, R, xs, st', h => by
    obtain ⟨rfl, rfl⟩ := vi_ret (a := ([] : List E)) h
    exact ⟨zs, rfl, rfl, rfl⟩
  | n + 1, s, zs, os, R, xs, st', h => by
    simp only [VerifierProgram.readScalars] at h
    obtain ⟨x, st1, h1, h2⟩ := vi_bind h
    obtain ⟨zs1, rfl, rfl⟩ := vi_readE h1
    obtain ⟨ys, st2, h3, h4⟩ := vi_bind h2
    obtain ⟨rest, hl, hz, hst⟩ := vi_readN n _ _ _ _ _ _ h3
    obtain ⟨rfl, rfl⟩ := vi_pure h4
    exact ⟨rest, by simp [hl], by rw [hz]; rfl, hst⟩

/-- `n` samples squeeze `n` challenges. -/
theorem vi_sampleN : ∀ (n : ℕ) (s : Fs) (zs : List E) (os : List (List Opening))
    (R : List (Digest × ℕ × ℕ)),
    runT (VerifierProgram.sampleChallenges n) ⟨s, none, zs, os, R⟩ =
      some ((s.squeezeN n).1, ⟨(s.squeezeN n).2, none, zs, os, R⟩)
  | 0, s, zs, os, R => rfl
  | n + 1, s, zs, os, R => by
    simp only [VerifierProgram.sampleChallenges, prog_bind_eq, runT_bind, vi_sampleE,
        Option.bind_some]
    rw [vi_sampleN n]
    rfl

theorem vi_sampleN' {n : ℕ} {s : Fs} {zs : List E} {os : List (List Opening)}
    {R : List (Digest × ℕ × ℕ)} {st' : TSt} {xs : List E}
    (h : runT (VerifierProgram.sampleChallenges n) ⟨s, none, zs, os, R⟩ = some (xs, st')) :
    xs = (s.squeezeN n).1 ∧ st' = ⟨(s.squeezeN n).2, none, zs, os, R⟩ := by
  rw [vi_sampleN] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.symm⟩

/-- **A grind of `bits ≠ 0` bits, then a sample, read back**: the nonce read, its proof of work,
and the sample is the grind's challenge (`grindSqueeze`). -/
theorem vi_grindSample {β : Type} {bits : ℕ} (hb : bits ≠ 0) {k : E → VerifierProgram β} {s : Fs}
    {zs : List E} {os : List (List Opening)} {R : List (Digest × ℕ × ℕ)} {b : β} {st' : TSt}
    (h : runT (VerifierProgram.grindProofOfWork bits >>= fun _ ↦
      VerifierProgram.sampleChallenge >>= k) ⟨s, none, zs, os, R⟩ = some (b, st')) :
    ∃ n zs', zs = n :: zs' ∧ s.GrindOk bits n ∧
      runT (k (s.grindSqueeze bits n).1) ⟨(s.grindSqueeze bits n).2, none, zs', os, R⟩ =
        some (b, st') := by
  obtain ⟨u, st1, h1, h2⟩ := vi_bind h
  unfold VerifierProgram.grindProofOfWork at h1
  simp only [hb, ↓reduceIte] at h1
  cases zs with
  | nil => simp [runT] at h1
  | cons n zs' =>
    simp only [runT] at h1
    split at h1
    · rename_i hp
      simp only [Option.some.injEq, Prod.mk.injEq] at h1
      obtain ⟨-, rfl⟩ := h1
      obtain ⟨c, st2, h3, h4⟩ := vi_bind h2
      simp only [VerifierProgram.sampleChallenge, runT, Option.some.injEq, Prod.mk.injEq] at h3
      obtain ⟨rfl, rfl⟩ := h3
      refine ⟨n, zs', rfl, Or.inr hp, ?_⟩
      rw [Fs.grindSqueeze_pos _ hb]
      exact h4
    · simp at h1

theorem vi_require {c : Prop} [Decidable c] {st st' : TSt} {u : Unit}
    (h : runT (VerifierProgram.require c) st = some (u, st')) : c ∧ st' = st := by
  unfold VerifierProgram.require at h
  split at h
  · rename_i hc
    simp only [runT, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨hc, h.2.symm⟩
  · simp [runT] at h

/-! ## Sumchecks -/

/-- **The pack rounds, read back.** -/
theorem vi_pack : ∀ (rs : List E) (v : E) (s : Fs) (zs : List E) (os : List (List Opening))
    (R : List (Digest × ℕ × ℕ)) (res : E × List E) (st' : TSt),
    runT (keccakPackRounds rs v) ⟨s, none, zs, os, R⟩ = some (res, st') →
      ∃ (ms : List (E × E)) (rest : List E), ms.length = rs.length ∧
        zs = ms.flatMap (fun m ↦ [m.1, m.2]) ++ rest ∧ res = (packRunF rs ms v s).1 ∧
        st' = ⟨(packRunF rs ms v s).2, none, rest, os, R⟩
  | [], v, s, zs, os, R, res, st', h => by
    obtain ⟨rfl, rfl⟩ := vi_pure (a := ((v, []) : E × List E)) h
    exact ⟨[], zs, rfl, rfl, rfl, rfl⟩
  | r :: rs, v, s, zs, os, R, res, st', h => by
    have key : keccakPackRounds (r :: rs) v = (sumcheckRoundPoly 3 v (some r) >>= fun message ↦
        VerifierProgram.sampleChallenge >>= fun challenge ↦
          keccakPackRounds rs (polyEval message challenge) >>= fun x ↦
            (pure (x.1, challenge :: x.2) : VerifierProgram (E × List E))) := rfl
    rw [key] at h
    obtain ⟨msg, st1, h1, h2⟩ := vi_bind h
    simp only [sumcheckRoundPoly] at h1
    obtain ⟨tail, st0, h3, h4⟩ := vi_bind h1
    obtain ⟨rest0, hl, hz, rfl⟩ := vi_readN _ _ _ _ _ _ _ h3
    obtain ⟨rfl, rfl⟩ := vi_pure h4
    obtain ⟨ch, st2, h5, h6⟩ := vi_bind h2
    obtain ⟨rfl, rfl⟩ := vi_sampleE' h5
    obtain ⟨r', st3, h7, h8⟩ := vi_bind h6
    obtain ⟨ms, rest, hml, hz', hr, hst⟩ := vi_pack rs _ _ _ _ _ _ _ h7
    obtain ⟨rfl, rfl⟩ := vi_pure h8
    have hl2 : tail.length = 2 := by simpa using hl
    obtain ⟨g1, g2, rfl⟩ := List.length_eq_two.mp hl2
    · refine ⟨(g1, g2) :: ms, rest, by simp [hml], ?_, ?_, ?_⟩
      · simp [hz, hz']
      · simp only [packRunF, hr]
      · simp only [packRunF]; exact hst

/-- **The position rounds, read back.** -/
theorem vi_local : ∀ (n : ℕ) (v : E) (s : Fs) (zs : List E) (os : List (List Opening))
    (R : List (Digest × ℕ × ℕ)) (res : List E × E) (st' : TSt),
    runT (sumcheck v 4 (List.replicate n none)) ⟨s, none, zs, os, R⟩ = some (res, st') →
      ∃ (ms : List (E × E × E)) (rest : List E), ms.length = n ∧
        zs = ms.flatMap (fun m ↦ [m.1, m.2.1, m.2.2]) ++ rest ∧ res = (localRunF ms v s).1 ∧
        st' = ⟨(localRunF ms v s).2, none, rest, os, R⟩
  | 0, v, s, zs, os, R, res, st', h => by
    obtain ⟨rfl, rfl⟩ := vi_pure (a := (([] : List E), v)) h
    exact ⟨[], zs, rfl, rfl, rfl, rfl⟩
  | n + 1, v, s, zs, os, R, res, st', h => by
    have key : sumcheck v 4 (List.replicate (n + 1) none) =
        (sumcheckRoundPoly 4 v none >>= fun message ↦ VerifierProgram.sampleChallenge >>=
            fun challenge ↦
          sumcheck (polyEval message challenge) 4 (List.replicate n none) >>= fun x ↦
            (pure (challenge :: x.1, x.2) : VerifierProgram (List E × E))) := rfl
    rw [key] at h
    obtain ⟨msg, st1, h1, h2⟩ := vi_bind h
    simp only [sumcheckRoundPoly] at h1
    obtain ⟨c0, st0, h3, h4⟩ := vi_bind h1
    obtain ⟨zs0, rfl, rfl⟩ := vi_readE h3
    obtain ⟨tail, st5, h9, h10⟩ := vi_bind h4
    obtain ⟨rest0, hl, hz, rfl⟩ := vi_readN _ _ _ _ _ _ _ h9
    obtain ⟨rfl, rfl⟩ := vi_pure h10
    obtain ⟨ch, st2, h5, h6⟩ := vi_bind h2
    obtain ⟨rfl, rfl⟩ := vi_sampleE' h5
    obtain ⟨r', st3, h7, h8⟩ := vi_bind h6
    obtain ⟨ms, rest, hml, hz', hr, hst⟩ := vi_local n _ _ _ _ _ _ _ h7
    obtain ⟨rfl, rfl⟩ := vi_pure h8
    have hl2 : tail.length = 2 := by simpa using hl
    obtain ⟨c2, c3, rfl⟩ := List.length_eq_two.mp hl2
    · refine ⟨(c0, c2, c3) :: ms, rest, by simp [hml], ?_, ?_, ?_⟩
      · simp [hz, hz']
      · rw [localRunF_cons, hr]
        rfl
      · rw [localRunF_cons]; exact hst

/-- **The plain rounds, read back.** -/
theorem vi_plain : ∀ (n : ℕ) (v : E) (s : Fs) (zs : List E) (os : List (List Opening))
    (R : List (Digest × ℕ × ℕ)) (res : List E × E) (st' : TSt),
    runT (sumcheck v 3 (List.replicate n none)) ⟨s, none, zs, os, R⟩ = some (res, st') →
      ∃ (ms : List (E × E)) (rest : List E), ms.length = n ∧
        zs = ms.flatMap (fun m ↦ [m.1, m.2]) ++ rest ∧
        res = ((plainRun ms v s).1, (plainRun ms v s).2.1) ∧
        st' = ⟨(plainRun ms v s).2.2, none, rest, os, R⟩
  | 0, v, s, zs, os, R, res, st', h => by
    obtain ⟨rfl, rfl⟩ := vi_pure (a := (([] : List E), v)) h
    exact ⟨[], zs, rfl, rfl, rfl, rfl⟩
  | n + 1, v, s, zs, os, R, res, st', h => by
    have key : sumcheck v 3 (List.replicate (n + 1) none) =
        (sumcheckRoundPoly 3 v none >>= fun message ↦ VerifierProgram.sampleChallenge >>=
            fun challenge ↦
          sumcheck (polyEval message challenge) 3 (List.replicate n none) >>= fun x ↦
            (pure (challenge :: x.1, x.2) : VerifierProgram (List E × E))) := rfl
    rw [key] at h
    obtain ⟨msg, st1, h1, h2⟩ := vi_bind h
    simp only [sumcheckRoundPoly] at h1
    obtain ⟨c0, st0, h3, h4⟩ := vi_bind h1
    obtain ⟨zs0, rfl, rfl⟩ := vi_readE h3
    obtain ⟨tail, st5, h9, h10⟩ := vi_bind h4
    obtain ⟨rest0, hl, hz, rfl⟩ := vi_readN _ _ _ _ _ _ _ h9
    obtain ⟨rfl, rfl⟩ := vi_pure h10
    obtain ⟨ch, st2, h5, h6⟩ := vi_bind h2
    obtain ⟨rfl, rfl⟩ := vi_sampleE' h5
    obtain ⟨r', st3, h7, h8⟩ := vi_bind h6
    obtain ⟨ms, rest, hml, hz', hr, hst⟩ := vi_plain n _ _ _ _ _ _ _ h7
    obtain ⟨rfl, rfl⟩ := vi_pure h8
    have hl2 : tail.length = 1 := by simpa using hl
    obtain ⟨c2, rfl⟩ := List.length_eq_one_iff.mp hl2
    · have hev : ∀ q : E, polyEval [c0, v + sumE [c2], c2] q = c0 + q * ((v + c2) + q * c2) := by
        intro q; simp [polyEval, sumE]; ring
      refine ⟨(c0, c2) :: ms, rest, by simp [hml], ?_, ?_, ?_⟩
      · simp [hz, hz']
      · simp only [plainRun, hr, hev]
        rfl
      · simp only [plainRun, hev] at hst ⊢; exact hst

/-! ## A layer -/

theorem grindPow_two : VerifierProgram.grindProofOfWork (grindingBits 2) = VerifierProgram.ret () := by
  simp [VerifierProgram.grindProofOfWork, show grindingBits 2 = 0 by decide]

/-- **A layer, read back**: its product, the nonce of the grind before `s`, its pack and position
rounds' messages, `t`, its two checks, the claim it returns and the sponge after it. -/
theorem vi_layer {L step : ℕ} {c c' : KeccakClaim} {s : Fs} {zs : List E} {os : List (List Opening)}
    {R : List (Digest × ℕ × ℕ)} {st' : TSt}
    (h : runT (verifyKeccakLayer L step c) ⟨s, none, zs, os, R⟩ = some (c', st')) :
    ∃ (product : List E) (n : E) (packMsgs : List (E × E)) (localMsgs : List (E × E × E))
      (t : E × E × E) (rest : List E), product.length = productBits ∧
      (s.absorbAll product dsObserve).GrindOk sGrindBits n ∧ packMsgs.length = c.point.length ∧
      localMsgs.length = keccakLocalBits ∧
      zs = product ++ [n] ++ packMsgs.flatMap (fun m ↦ [m.1, m.2]) ++
        localMsgs.flatMap (fun m ↦ [m.1, m.2.1, m.2.2]) ++ [t.1, t.2.1, t.2.2] ++ rest ∧
      projectedOf c product + keccakIota L step c * sumE c.mu = c.value ∧
      LayerFinal c s product n packMsgs localMsgs t ∧
      c' = layerClaim c s product n packMsgs localMsgs t ∧
      st' = ⟨(layerBeta c s product n packMsgs localMsgs t).2, none, rest, os, R⟩ := by
  rw [verifyKeccakLayer_packed] at h
  unfold verifyKeccakLayerPacked at h
  obtain ⟨product, st1, h1, h2⟩ := vi_bind h
  obtain ⟨rest1, hpl, hz1, rfl⟩ := vi_readN _ _ _ _ _ _ _ h1
  obtain ⟨u, st2, h3, h4⟩ := vi_bind h2
  obtain ⟨hproj, rfl⟩ := vi_require h3
  obtain ⟨n, rest2, rfl, hgr, h6⟩ := vi_grindSample
    (by rw [show grindingBits (productBits - 1) = 3 from sGrindBits_eq]; decide) h4
  obtain ⟨res, st4, h7, h8⟩ := vi_bind h6
  obtain ⟨packMsgs, rest3, hpm, hz2, hr, rfl⟩ := vi_pack _ _ _ _ _ _ _ _ h7
  obtain ⟨vL, chs⟩ := res
  obtain ⟨res2, st5, h9, h10⟩ := vi_bind h8
  obtain ⟨localMsgs, rest4, hlm, hz3, hr2, rfl⟩ := vi_local _ _ _ _ _ _ _ _ h9
  obtain ⟨locPt, vR⟩ := res2
  obtain ⟨tl, st6, h11, h12⟩ := vi_bind h10
  obtain ⟨rest5, htl, hz4, rfl⟩ := vi_readN _ _ _ _ _ _ _ h11
  obtain ⟨t0, t1, t2, rfl⟩ := List.length_eq_three.mp htl
  obtain ⟨u2, st7, h13, h14⟩ := vi_bind h12
  obtain ⟨hfin, rfl⟩ := vi_require h13
  obtain ⟨u3, st7', h14a, h14b⟩ := vi_bind h14
  rw [grindPow_two] at h14a
  obtain ⟨-, rfl⟩ := vi_ret h14a
  obtain ⟨beta, st8, h15, h16⟩ := vi_bind h14b
  obtain ⟨rfl, rfl⟩ := vi_sampleE' h15
  obtain ⟨rfl, rfl⟩ := vi_pure h16
  simp only [Prod.ext_iff] at hr hr2
  obtain ⟨rfl, rfl⟩ := hr
  obtain ⟨rfl, rfl⟩ := hr2
  refine ⟨product, n, packMsgs, localMsgs, (t0, t1, t2), rest5, hpl, hgr, hpm, hlm, ?_, hproj,
    hfin, rfl, rfl⟩
  rw [hz1, hz2, hz3, hz4]; simp

/-! ## The layers -/

/-- A layer's words: the product, the nonce, the pack and position rounds' messages, `t`. -/
abbrev LT : Type := List E × E × List (E × E) × List (E × E × E) × (E × E × E)

/-- The words a layer reads. -/
def ltXs (T : LT) : List E :=
  T.1 ++ [T.2.1] ++ T.2.2.1.flatMap (fun m ↦ [m.1, m.2]) ++
    T.2.2.2.1.flatMap (fun m ↦ [m.1, m.2.1, m.2.2]) ++
    [T.2.2.2.2.1, T.2.2.2.2.2.1, T.2.2.2.2.2.2]

/-- The claim and the sponge after the layers. -/
def chainEnd : List ℕ → KeccakClaim → Fs → List LT → KeccakClaim × Fs
  | _ :: steps, c, s, T :: Ts =>
    chainEnd steps (layerClaim c s T.1 T.2.1 T.2.2.1 T.2.2.2.1 T.2.2.2.2)
      (layerBeta c s T.1 T.2.1 T.2.2.1 T.2.2.2.1 T.2.2.2.2).2 Ts
  | _, c, s, _ => (c, s)

/-- What the layers' words satisfy: their lengths, each grind's proof of work and each layer's two
checks. -/
def ChainOk (L : ℕ) : List ℕ → KeccakClaim → Fs → List LT → Prop
  | a :: steps, c, s, T :: Ts =>
    T.1.length = productBits ∧ (s.absorbAll T.1 dsObserve).GrindOk sGrindBits T.2.1 ∧
      T.2.2.1.length = c.point.length ∧ T.2.2.2.1.length = keccakLocalBits ∧
      projectedOf c T.1 + keccakIota L a c * sumE c.mu = c.value ∧
      LayerFinal c s T.1 T.2.1 T.2.2.1 T.2.2.2.1 T.2.2.2.2 ∧
      ChainOk L steps (layerClaim c s T.1 T.2.1 T.2.2.1 T.2.2.2.1 T.2.2.2.2)
        (layerBeta c s T.1 T.2.1 T.2.2.1 T.2.2.2.1 T.2.2.2.2).2 Ts
  | [], _, _, [] => True
  | _, _, _, _ => False

/-- **The layers, read back.** -/
theorem vi_layers {L : ℕ} : ∀ (steps : List ℕ) (c : KeccakClaim) (s : Fs) (zs : List E)
    (os : List (List Opening)) (R : List (Digest × ℕ × ℕ)) (c' : KeccakClaim) (st' : TSt),
    runT (keccakLayers L steps c) ⟨s, none, zs, os, R⟩ = some (c', st') →
      ∃ (Ts : List LT) (rest : List E), ChainOk L steps c s Ts ∧
        zs = Ts.flatMap ltXs ++ rest ∧ c' = (chainEnd steps c s Ts).1 ∧
        st' = ⟨(chainEnd steps c s Ts).2, none, rest, os, R⟩
  | [], c, s, zs, os, R, c', st', h => by
    obtain ⟨rfl, rfl⟩ := vi_pure (a := c) h
    exact ⟨[], zs, trivial, rfl, rfl, rfl⟩
  | a :: steps, c, s, zs, os, R, c', st', h => by
    obtain ⟨c1, st1, h1, h2⟩ := vi_bind h
    obtain ⟨product, n, packMsgs, localMsgs, t, rest1, hpl, hgr, hpm, hlm, hz, hproj, hfin, rfl,
      rfl⟩ := vi_layer h1
    obtain ⟨Ts, rest, hok, hz', rfl, rfl⟩ := vi_layers steps _ _ _ _ _ _ _ h2
    refine ⟨(product, n, packMsgs, localMsgs, t) :: Ts, rest,
      ⟨hpl, hgr, hpm, hlm, hproj, hfin, hok⟩, ?_, rfl, rfl⟩
    rw [hz, hz']
    simp [ltXs]

/-! ## `verifyKeccak` -/

set_option maxRecDepth 20000 in
/-- **`verifyKeccak`, read back**: the committed word, the layers' words, the openings' rounds,
the word, the slices; the two opening checks; the results and the sponge after the slices. -/
theorem vi_vk {τ : ℕ} {inst outs : List E} {f xs op point slices : List E} {word : E} {S' : Fs}
    (hshape : inst.length = τ ∧ outs.length = keccakStateLanes ∧ 4 ≤ τ)
    (h : runT (verifyKeccak τ inst outs) ⟨⟨f, []⟩, none, xs, [], []⟩ =
      some (([⟨qkeccak, op, word⟩], point, slices), ⟨S', none, [], [], []⟩)) :
    ∃ (committed : E) (Ts : List LT) (mO mI mS : List (E × E)),
      let s1 := (⟨f, []⟩ : Fs).squeezeN keccakSegmentBits
      let s2 := s1.2.squeezeN keccakLaneBits
      let c0 := vkFirst inst outs committed s1.1 s2.1
      let L := chainEnd (List.range keccakDepth) c0 (s2.2.absorb committed dsObserve) Ts
      let O := plainRun mO committed L.2
      let I := plainRun mI L.1.value (O.2.2.absorb word dsObserve)
      let S := plainRun mS I.2.1 I.2.2
      ChainOk τ (List.range keccakDepth) c0 (s2.2.absorb committed dsObserve) Ts ∧
      mO.length = 6 ∧ mI.length = 4 ∧ mS.length = 6 ∧ slices.length = 64 ∧
      ((foldAll O.1 (keccakSlotWeights τ c0 1 1)).headD []).headD 0 * word = O.2.1 ∧
      multilinearEval L.1.mu I.1 * dot ((foldAll S.1 (keccakSlotWeights τ L.1 0 2)).headD [])
        slices = S.2.1 ∧
      S' = S.2.2.absorbAll slices dsObserve ∧
      xs = [committed] ++ Ts.flatMap ltXs ++ mO.flatMap (fun m ↦ [m.1, m.2]) ++ [word] ++
        mI.flatMap (fun m ↦ [m.1, m.2]) ++ mS.flatMap (fun m ↦ [m.1, m.2]) ++ slices ∧
      op = inst.take 4 ++ inst.drop 4 ++ O.1 ∧
      point = I.1 ++ L.1.point.take (τ - 4) ++ S.1 := by
  rw [verifyKeccak_body τ inst outs hshape] at h
  obtain ⟨seg, sA, a1, a2⟩ := vi_bind h
  obtain ⟨rfl, rfl⟩ := vi_sampleN' a1
  obtain ⟨rl, sB, a3, a4⟩ := vi_bind a2
  obtain ⟨rfl, rfl⟩ := vi_sampleN' a3
  obtain ⟨committed, sC, a5, a6⟩ := vi_bind a4
  obtain ⟨zs1, hz1, rfl⟩ := vi_readE a5
  obtain ⟨claim, sD, a7, a8⟩ := vi_bind a6
  obtain ⟨Ts, rest1, hok, hz2, rfl, rfl⟩ := vi_layers _ _ _ _ _ _ _ _ a7
  obtain ⟨o, sE, a9, a10⟩ := vi_bind a8
  rw [keccakOpen_eq] at a9
  obtain ⟨x, sF, a11, a12⟩ := vi_bind a9
  obtain ⟨mO, rest2, hmO, hz3, rfl, rfl⟩ := vi_plain _ _ _ _ _ _ _ _ a11
  obtain ⟨rfl, rfl⟩ := vi_ret a12
  obtain ⟨wd, sG, a13, a14⟩ := vi_bind a10
  obtain ⟨zs2, hz4, rfl⟩ := vi_readE a13
  obtain ⟨u, sH, a15, a16⟩ := vi_bind a14
  obtain ⟨hchkO, rfl⟩ := vi_require a15
  obtain ⟨y, sI, a17, a18⟩ := vi_bind a16
  obtain ⟨mI, rest3, hmI, hz5, rfl, rfl⟩ := vi_plain _ _ _ _ _ _ _ _ a17
  obtain ⟨o2, sJ, a19, a20⟩ := vi_bind a18
  rw [keccakOpen_eq] at a19
  obtain ⟨x2, sK, a21, a22⟩ := vi_bind a19
  obtain ⟨mS, rest4, hmS, hz6, rfl, rfl⟩ := vi_plain _ _ _ _ _ _ _ _ a21
  obtain ⟨rfl, rfl⟩ := vi_ret a22
  obtain ⟨sl, sL, a23, a24⟩ := vi_bind a20
  obtain ⟨rest5, hsl, hz7, rfl⟩ := vi_readN _ _ _ _ _ _ _ a23
  obtain ⟨u2, sM, a25, a26⟩ := vi_bind a24
  obtain ⟨hchkI, rfl⟩ := vi_require a25
  obtain ⟨hr, hst⟩ := vi_pure a26
  simp only [qkeccakSlotBits_eq'] at hmO hmS
  simp only [Prod.mk.injEq, List.cons.injEq, ColumnClaim.mk.injEq, and_true, true_and] at hr
  simp only [TSt.mk.injEq] at hst
  simp only [and_assoc] at hr
  simp only at hchkO hchkI hok
  obtain ⟨hop, rfl, hpt, rfl⟩ := hr
  obtain ⟨hS, -, rfl, -, -⟩ := hst
  refine ⟨committed, Ts, mO, mI, mS, hok, hmO, hmI, hmS, hsl, hchkO, hchkI, hS, ?_, hop, hpt⟩
  rw [hz1, hz2, hz3, hz4, hz5, hz6, hz7]
  simp

/-! ## The result's shape -/

set_option maxRecDepth 20000 in
/-- **`verifyKeccak`'s result, at any accepting carried run**: one output claim on `q_keccak`, a point,
the slices. -/
theorem vi_vkRes {τ : ℕ} {inst outs : List E} {f xs : List E} {res : List ColumnClaim × List E × List E}
    {st : TSt} (hshape : inst.length = τ ∧ outs.length = keccakStateLanes ∧ 4 ≤ τ)
    (h : runT (verifyKeccak τ inst outs) ⟨⟨f, []⟩, none, xs, [], []⟩ = some (res, st)) :
    ∃ (op point slices : List E) (word : E), res = ([⟨qkeccak, op, word⟩], point, slices) := by
  rw [verifyKeccak_body τ inst outs hshape] at h
  obtain ⟨_, _, -, a2⟩ := vi_bind h
  obtain ⟨_, _, -, a4⟩ := vi_bind a2
  obtain ⟨_, _, -, a6⟩ := vi_bind a4
  obtain ⟨_, _, -, a8⟩ := vi_bind a6
  obtain ⟨_, _, -, a10⟩ := vi_bind a8
  obtain ⟨_, _, -, a14⟩ := vi_bind a10
  obtain ⟨_, _, -, a16⟩ := vi_bind a14
  obtain ⟨_, _, -, a18⟩ := vi_bind a16
  obtain ⟨_, _, -, a20⟩ := vi_bind a18
  obtain ⟨_, _, -, a24⟩ := vi_bind a20
  obtain ⟨_, _, -, a26⟩ := vi_bind a24
  obtain ⟨hr, -⟩ := vi_pure a26
  exact ⟨_, _, _, _, hr⟩

theorem plainRun_len' : ∀ (ms : List (E × E)) (v : E) (s : Fs), (plainRun ms v s).1.length = ms.length
  | [], _, _ => rfl
  | m :: ms, v, s => by simp [plainRun, plainRun_len' ms]

theorem plainRun_cons_snd' (c0 c2 : E) (rest : List (E × E)) (v : E) (s : Fs) :
    (plainRun ((c0, c2) :: rest) v s).2.2 =
      (plainRun rest (c0 + ((s.absorb c0 dsObserve).absorb c2 dsObserve).squeeze.1 *
        ((v + c2) + ((s.absorb c0 dsObserve).absorb c2 dsObserve).squeeze.1 * c2))
        ((s.absorb c0 dsObserve).absorb c2 dsObserve).squeeze.2).2.2 := rfl

theorem plainRun_pend' (ms : List (E × E)) : ∀ (v : E) (s : Fs), ms ≠ [] → (plainRun ms v s).2.2.pend = [] := by
  induction ms with
  | nil => intro _ _ h; exact absurd rfl h
  | cons m ms ih =>
    intro v s _
    obtain ⟨c0, c2⟩ := m
    rw [plainRun_cons_snd']
    rcases ms with _ | ⟨m', ms'⟩
    · simp only [plainRun]
      rfl
    · exact ih _ _ (by simp)

theorem pend_absorbAll' : ∀ (xs : List E) (s : Fs) (t : ℕ), 1 ≤ s.pend.length →
    s.pend.length ≤ 4 → (s.absorbAll xs t).pend.length = (s.pend.length - 1 + xs.length) % 4 + 1
  | [], s, t, h1, h4 => by
    show s.pend.length = _
    simp only [List.length_nil]
    omega
  | x :: xs, s, t, h1, h4 => by
    show ((s.absorb x t).absorbAll xs t).pend.length = _
    by_cases hf : s.pend.length = 4
    · have e : s.absorb x t = ⟨capOf s.perm, [(x, t)]⟩ := by simp [Fs.absorb, hf, rateScalars]
      rw [e, pend_absorbAll' xs _ t (by simp) (by simp)]
      simp only [List.length_cons, List.length_nil]
      omega
    · have e : s.absorb x t = ⟨s.cap, s.pend ++ [(x, t)]⟩ := by
        simp [Fs.absorb, hf, rateScalars]
      rw [e, pend_absorbAll' xs _ t (by simp) (by simp; omega)]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega

/-- Sixty-four words absorbed from an empty queue fill it. -/
theorem absorbAll64_pend {s : Fs} (hs : s.pend = []) {xs : List E} (hl : xs.length = 64) (t : ℕ) :
    (s.absorbAll xs t).pend.length = rateScalars := by
  obtain ⟨x, xs', rfl⟩ : ∃ x xs', xs = x :: xs' := by
    cases xs with
    | nil => simp at hl
    | cons x xs' => exact ⟨x, xs', rfl⟩
  have e : s.absorb x t = ⟨s.cap, [(x, t)]⟩ := by simp [Fs.absorb, hs, rateScalars]
  show ((s.absorb x t).absorbAll xs' t).pend.length = _
  rw [e, pend_absorbAll' xs' _ t (by simp) (by simp)]
  simp only [List.length_cons] at hl
  dsimp only
  simp only [List.length_cons, List.length_nil, rateScalars]
  omega

set_option maxRecDepth 20000 in
/-- **An accepting run of `verifyKeccak` from a squeezed sponge**: one output claim on `q_keccak` at a point
of `τ + 6` words, an input point of at most `τ + 6`, `64` slices, its end sponge's queue full. -/
theorem vk_shape {τ : ℕ} {inst outs : List E} {S : KeccakState} {xs : List E}
    {res : List ColumnClaim × List E × List E} {s' : Fs}
    (hshape : inst.length = τ ∧ outs.length = keccakStateLanes ∧ 4 ≤ τ)
    (h : RunsTo (verifyKeccak τ inst outs) ⟨capOf S, []⟩ xs res s') :
    ∃ (op point slices : List E) (word : E), res = ([⟨qkeccak, op, word⟩], point, slices) ∧
      slices.length = 64 ∧ s'.pend.length = rateScalars ∧ op.length = τ + 6 ∧ point.length ≤ τ + 6 := by
  have hT := runsTo_toT (plain_verifyKeccak hshape).noPacked h (sp := ⟨S, [], none⟩) ⟨rfl, rfl, rfl⟩
  obtain ⟨op, point, slices, word, rfl⟩ := vi_vkRes hshape hT
  obtain ⟨committed, Ts, mO, mI, mS, -, hmO, hmI, hmS, hsl, -, -, hS, -, hop, hpt⟩ := vi_vk hshape hT
  refine ⟨op, point, slices, word, rfl, hsl, ?_, ?_, ?_⟩
  · rw [hS]
    exact absorbAll64_pend (plainRun_pend' _ _ _ (by rintro rfl; simp at hmS)) hsl _
  · have h4 := hshape.2.2
    rw [hop]
    simp only [List.length_append, plainRun_len', hmO, List.length_take, List.length_drop, hshape.1]
    omega
  · have h4 := hshape.2.2
    rw [hpt]
    simp only [List.length_append, plainRun_len', hmI, hmS, List.length_take]
    omega

end
end LeanVM.Guest.B1.VsC.VkOs
