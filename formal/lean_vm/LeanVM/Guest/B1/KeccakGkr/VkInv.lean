/-
  LeanVM.Guest.B1.KeccakGkr.VkInv

  `verify_keccak`'s honest run read back: the sumchecks' rounds and a layer's words from an
  accepting carried run.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.LayerSpec
public import LeanVM.Guest.B1.KeccakGkr.VkSpec
public import LeanVM.Guest.B1.Tables.RunF
public import LeanVM.Guest.B1.KeccakGkr.LocalRounds

/-!
# Runs read back

An accepting run from a carried sponge is the carried run (`runsTo_toT`, `Tables.runT`), which is
deterministic: the reads, samples and `require`s read back from it (`vi_readE`, `vi_readN`,
`vi_require`), the pack rounds (`vi_pack`: `packRunF`), the position rounds (`vi_local`:
`localRunF`), the plain rounds (`vi_plain`: `plainRun`), and a layer (`vi_layer`): its product,
its messages, `t`, its two checks, the claim it returns (`layerClaim`) and the sponge after it.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr LeanVM.Guest.B1.Tables

@[expose] public section

/-! ## The carried run -/

/-- **An accepting run is the carried run.** -/
theorem runsTo_toT {α : Type} {p : VerifierProgram α} {s s' : Fs} {xs : List E} {a : α}
    (h : RunsTo p s xs a s') {sp : Sponge} (hc : s.Carries sp) :
    runT p ⟨s, xs, [], []⟩ = some (a, ⟨s', [], [], []⟩) := by
  obtain ⟨sp', hc', he⟩ := h sp hc [] [] []
  simp only [List.append_nil] at he
  rw [runT_of_runId p ⟨s, xs, [], []⟩ sp hc a _ he, ← eq_fsOfT hc']

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
    {x : E} {st' : TSt} (h : runT VerifierProgram.readScalar ⟨s, zs, os, R⟩ = some (x, st')) :
    ∃ zs', zs = x :: zs' ∧ st' = ⟨s.absorb x dsObserve, zs', os, R⟩ := by
  cases zs with
  | nil => simp [VerifierProgram.readScalar, runT] at h
  | cons z zs' =>
    simp only [VerifierProgram.readScalar, runT, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨zs', rfl, rfl⟩

theorem vi_sampleE (st : TSt) :
    runT VerifierProgram.sampleChallenge st = some (st.sponge.squeeze.1, { st with sponge := st.sponge.squeeze.2 }) :=
  rfl

theorem vi_sampleE' {st st' : TSt} {x : E} (h : runT VerifierProgram.sampleChallenge st = some (x,
    st')) :
    x = st.sponge.squeeze.1 ∧ st' = { st with sponge := st.sponge.squeeze.2 } := by
  rw [vi_sampleE] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.symm⟩

/-- `n` reads take the next `n` words, absorbed. -/
theorem vi_readN : ∀ (n : ℕ) (s : Fs) (zs : List E) (os : List (List Opening))
    (R : List (Digest × ℕ × ℕ)) (xs : List E) (st' : TSt),
    runT (VerifierProgram.readScalars n) ⟨s, zs, os, R⟩ = some (xs, st') →
      ∃ rest, xs.length = n ∧ zs = xs ++ rest ∧ st' = ⟨s.absorbAll xs dsObserve, rest, os, R⟩
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
theorem vi_sampleN : ∀ (n : ℕ) (st : TSt),
    runT (VerifierProgram.sampleChallenges n) st = some ((st.sponge.squeezeN n).1,
      { st with sponge := (st.sponge.squeezeN n).2 })
  | 0, ⟨s, zs, os, R⟩ => rfl
  | n + 1, st => by
    simp only [VerifierProgram.sampleChallenges, prog_bind_eq, runT_bind, vi_sampleE,
        Option.bind_some]
    rw [vi_sampleN n]
    rfl

theorem vi_sampleN' {n : ℕ} {st st' : TSt} {xs : List E}
    (h : runT (VerifierProgram.sampleChallenges n) st = some (xs, st')) :
    xs = (st.sponge.squeezeN n).1 ∧ st' = { st with sponge := (st.sponge.squeezeN n).2 } := by
  rw [vi_sampleN] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.symm⟩

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
theorem vi_pack : ∀ (rs : List E) (v sc : E) (s : Fs) (zs : List E) (os : List (List Opening))
    (R : List (Digest × ℕ × ℕ)) (res : E × E × List E) (st' : TSt),
    runT (keccakPackRounds rs v sc) ⟨s, zs, os, R⟩ = some (res, st') →
      ∃ (ms : List (E × E)) (rest : List E), ms.length = rs.length ∧
        zs = ms.flatMap (fun m ↦ [m.1, m.2]) ++ rest ∧ res = (packRunF rs ms v sc s).1 ∧
        st' = ⟨(packRunF rs ms v sc s).2, rest, os, R⟩
  | [], v, sc, s, zs, os, R, res, st', h => by
    obtain ⟨rfl, rfl⟩ := vi_pure (a := ((v, sc, []) : E × E × List E)) h
    exact ⟨[], zs, rfl, rfl, rfl, rfl⟩
  | r :: rs, v, sc, s, zs, os, R, res, st', h => by
    have key : keccakPackRounds (r :: rs) v sc = (sumcheckRoundPoly 3 v (some r) >>= fun message ↦
        VerifierProgram.sampleChallenge >>= fun challenge ↦
          keccakPackRounds rs ((1 + r + challenge) * polyEval message challenge)
            (sc * (1 + r + challenge)) >>= fun x ↦
            (pure (x.1, x.2.1, challenge :: x.2.2) : VerifierProgram (E × E × List E))) := rfl
    rw [key] at h
    obtain ⟨msg, st1, h1, h2⟩ := vi_bind h
    simp only [sumcheckRoundPoly] at h1
    obtain ⟨tail, st0, h3, h4⟩ := vi_bind h1
    obtain ⟨rest0, hl, hz, rfl⟩ := vi_readN _ _ _ _ _ _ _ h3
    obtain ⟨rfl, rfl⟩ := vi_pure h4
    obtain ⟨ch, st2, h5, h6⟩ := vi_bind h2
    obtain ⟨rfl, rfl⟩ := vi_sampleE' h5
    obtain ⟨r', st3, h7, h8⟩ := vi_bind h6
    obtain ⟨ms, rest, hml, hz', hr, hst⟩ := vi_pack rs _ _ _ _ _ _ _ _ h7
    obtain ⟨rfl, rfl⟩ := vi_pure h8
    have hl2 : tail.length = 2 := by simpa using hl
    obtain ⟨g1, g2, rfl⟩ := List.length_eq_two.mp hl2
    · refine ⟨(g1, g2) :: ms, rest, by simp [hml], ?_, ?_, ?_⟩
      · simp only at hz'
        simp [hz, hz']
      · simp only [packRunF, hr]
      · simp only [packRunF]; exact hst

/-- **The position rounds, read back.** -/
theorem vi_local : ∀ (n : ℕ) (v : E) (s : Fs) (zs : List E) (os : List (List Opening))
    (R : List (Digest × ℕ × ℕ)) (res : List E × E) (st' : TSt),
    runT (sumcheck v 4 (List.replicate n none)) ⟨s, zs, os, R⟩ = some (res, st') →
      ∃ (ms : List (E × E × E)) (rest : List E), ms.length = n ∧
        zs = ms.flatMap (fun m ↦ [m.1, m.2.1, m.2.2]) ++ rest ∧ res = (localRunF ms v s).1 ∧
        st' = ⟨(localRunF ms v s).2, rest, os, R⟩
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
      · simp only at hz'
        simp [hz, hz']
      · rw [localRunF_cons, hr]
        rfl
      · rw [localRunF_cons]; exact hst

/-- **The plain rounds, read back.** -/
theorem vi_plain : ∀ (n : ℕ) (v : E) (s : Fs) (zs : List E) (os : List (List Opening))
    (R : List (Digest × ℕ × ℕ)) (res : List E × E) (st' : TSt),
    runT (sumcheck v 3 (List.replicate n none)) ⟨s, zs, os, R⟩ = some (res, st') →
      ∃ (ms : List (E × E)) (rest : List E), ms.length = n ∧
        zs = ms.flatMap (fun m ↦ [m.1, m.2]) ++ rest ∧
        res = ((plainRun ms v s).1, (plainRun ms v s).2.1) ∧
        st' = ⟨(plainRun ms v s).2.2, rest, os, R⟩
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
      · simp only at hz'
        simp [hz, hz']
      · simp only [plainRun, hr, hev]
        rfl
      · simp only [plainRun, hev] at hst ⊢; exact hst

/-! ## A layer -/

/-- **A layer, read back**: its product, its pack and position rounds' messages, `t`, its two
checks, the claim it returns and the sponge after it. -/
theorem vi_layer {L step : ℕ} {c c' : KeccakClaim} {s : Fs} {zs : List E} {os : List (List Opening)}
    {R : List (Digest × ℕ × ℕ)} {st' : TSt}
    (h : runT (verifyKeccakLayer L step c) ⟨s, zs, os, R⟩ = some (c', st')) :
    ∃ (product : List E) (packMsgs : List (E × E)) (localMsgs : List (E × E × E)) (t : E × E × E)
      (rest : List E), product.length = productBits ∧ packMsgs.length = c.point.length ∧
      localMsgs.length = keccakLocalBits ∧
      zs = product ++ packMsgs.flatMap (fun m ↦ [m.1, m.2]) ++
        localMsgs.flatMap (fun m ↦ [m.1, m.2.1, m.2.2]) ++ [t.1, t.2.1, t.2.2] ++ rest ∧
      projectedOf c product + keccakIota L step c * sumE c.mu = c.value ∧
      LayerFinal c s product packMsgs localMsgs t ∧
      c' = layerClaim c s product packMsgs localMsgs t ∧
      st' = ⟨(layerBeta c s product packMsgs localMsgs t).2, rest, os, R⟩ := by
  unfold verifyKeccakLayer at h
  obtain ⟨product, st1, h1, h2⟩ := vi_bind h
  obtain ⟨rest1, hpl, hz1, rfl⟩ := vi_readN _ _ _ _ _ _ _ h1
  obtain ⟨u, st2, h3, h4⟩ := vi_bind h2
  obtain ⟨hproj, rfl⟩ := vi_require h3
  obtain ⟨sv, st3, h5, h6⟩ := vi_bind h4
  obtain ⟨rfl, rfl⟩ := vi_sampleE' h5
  obtain ⟨res, st4, h7, h8⟩ := vi_bind h6
  obtain ⟨packMsgs, rest2, hpm, hz2, hr, rfl⟩ := vi_pack _ _ _ _ _ _ _ _ _ h7
  obtain ⟨vL, scL, chs⟩ := res
  obtain ⟨res2, st5, h9, h10⟩ := vi_bind h8
  obtain ⟨localMsgs, rest3, hlm, hz3, hr2, rfl⟩ := vi_local _ _ _ _ _ _ _ _ h9
  obtain ⟨locPt, vR⟩ := res2
  obtain ⟨tl, st6, h11, h12⟩ := vi_bind h10
  obtain ⟨rest4, htl, hz4, rfl⟩ := vi_readN _ _ _ _ _ _ _ h11
  obtain ⟨t0, t1, t2, rfl⟩ := List.length_eq_three.mp htl
  obtain ⟨u2, st7, h13, h14⟩ := vi_bind h12
  obtain ⟨hfin, rfl⟩ := vi_require h13
  obtain ⟨beta, st8, h15, h16⟩ := vi_bind h14
  obtain ⟨rfl, rfl⟩ := vi_sampleE' h15
  obtain ⟨rfl, rfl⟩ := vi_pure h16
  simp only at hr hr2 hz2 hz3 hz4 hfin
  simp only [Prod.ext_iff] at hr hr2
  obtain ⟨rfl, rfl, rfl⟩ := hr
  obtain ⟨rfl, rfl⟩ := hr2
  refine ⟨product, packMsgs, localMsgs, (t0, t1, t2), rest4, hpl, hpm, hlm, ?_, hproj, hfin, rfl,
    rfl⟩
  rw [hz1, hz2, hz3, hz4]; simp

/-! ## The layers -/

/-- A layer's words: the product, the pack and position rounds' messages, `t`. -/
abbrev LT : Type := List E × List (E × E) × List (E × E × E) × (E × E × E)

/-- The words a layer reads. -/
def ltXs (T : LT) : List E :=
  T.1 ++ T.2.1.flatMap (fun m ↦ [m.1, m.2]) ++ T.2.2.1.flatMap (fun m ↦ [m.1, m.2.1, m.2.2]) ++
    [T.2.2.2.1, T.2.2.2.2.1, T.2.2.2.2.2]

/-- The claim and the sponge after the layers. -/
def chainEnd : List ℕ → KeccakClaim → Fs → List LT → KeccakClaim × Fs
  | _ :: steps, c, s, T :: Ts =>
    chainEnd steps (layerClaim c s T.1 T.2.1 T.2.2.1 T.2.2.2)
      (layerBeta c s T.1 T.2.1 T.2.2.1 T.2.2.2).2 Ts
  | _, c, s, _ => (c, s)

/-- What the layers' words satisfy: their lengths and each layer's two checks. -/
def ChainOk (L : ℕ) : List ℕ → KeccakClaim → Fs → List LT → Prop
  | a :: steps, c, s, T :: Ts =>
    T.1.length = productBits ∧ T.2.1.length = c.point.length ∧
      T.2.2.1.length = keccakLocalBits ∧
      projectedOf c T.1 + keccakIota L a c * sumE c.mu = c.value ∧
      LayerFinal c s T.1 T.2.1 T.2.2.1 T.2.2.2 ∧
      ChainOk L steps (layerClaim c s T.1 T.2.1 T.2.2.1 T.2.2.2)
        (layerBeta c s T.1 T.2.1 T.2.2.1 T.2.2.2).2 Ts
  | [], _, _, [] => True
  | _, _, _, _ => False

/-- **The layers, read back.** -/
theorem vi_layers {L : ℕ} : ∀ (steps : List ℕ) (c : KeccakClaim) (s : Fs) (zs : List E)
    (os : List (List Opening)) (R : List (Digest × ℕ × ℕ)) (c' : KeccakClaim) (st' : TSt),
    runT (keccakLayers L steps c) ⟨s, zs, os, R⟩ = some (c', st') →
      ∃ (Ts : List LT) (rest : List E), ChainOk L steps c s Ts ∧
        zs = Ts.flatMap ltXs ++ rest ∧ c' = (chainEnd steps c s Ts).1 ∧
        st' = ⟨(chainEnd steps c s Ts).2, rest, os, R⟩
  | [], c, s, zs, os, R, c', st', h => by
    obtain ⟨rfl, rfl⟩ := vi_pure (a := c) h
    exact ⟨[], zs, trivial, rfl, rfl, rfl⟩
  | a :: steps, c, s, zs, os, R, c', st', h => by
    obtain ⟨c1, st1, h1, h2⟩ := vi_bind h
    obtain ⟨product, packMsgs, localMsgs, t, rest1, hpl, hpm, hlm, hz, hproj, hfin, rfl, rfl⟩ :=
      vi_layer h1
    obtain ⟨Ts, rest, hok, hz', rfl, rfl⟩ := vi_layers steps _ _ _ _ _ _ _ h2
    refine ⟨(product, packMsgs, localMsgs, t) :: Ts, rest, ⟨hpl, hpm, hlm, hproj, hfin, hok⟩, ?_,
      rfl, rfl⟩
    rw [hz, hz']
    simp [ltXs]

/-! ## `keccakSeg` -/

set_option maxRecDepth 20000 in
/-- **`keccakSeg`, read back**: the committed word, the layers' words, the openings' rounds, the
word, the slices; the two opening checks; the results. -/
theorem vi_seg {τ : ℕ} {inst outs : List E} {f xs op point slices cap' : List E} {word m0 : E}
    (h : runT (keccakSeg τ inst outs) ⟨⟨f, []⟩, xs, [], []⟩ =
      some ((([⟨qkeccak, op, word⟩], point, slices), m0), ⟨⟨cap', []⟩, [], [], []⟩)) :
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
      (S.2.2.absorbAll slices dsObserve).squeeze = (m0, ⟨cap', []⟩) ∧
      xs = [committed] ++ Ts.flatMap ltXs ++ mO.flatMap (fun m ↦ [m.1, m.2]) ++ [word] ++
        mI.flatMap (fun m ↦ [m.1, m.2]) ++ mS.flatMap (fun m ↦ [m.1, m.2]) ++ slices ∧
      op = inst.take 4 ++ inst.drop 4 ++ O.1 ∧
      point = I.1 ++ L.1.point.take (τ - 4) ++ S.1 := by
  unfold keccakSeg at h
  obtain ⟨r, st1, h1, h2⟩ := vi_bind h
  obtain ⟨m, st2, h3, h4⟩ := vi_bind h2
  obtain ⟨rfl, rfl⟩ := vi_sampleE' h3
  obtain ⟨hr, hst⟩ := vi_pure h4
  rw [verifyKeccak_eq] at h1
  obtain ⟨seg, sA, a1, a2⟩ := vi_bind h1
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
  obtain ⟨rfl, rfl⟩ := vi_pure a26
  simp only [qkeccakSlotBits_eq'] at hmO hmS
  simp only [Prod.mk.injEq, List.cons.injEq, ColumnClaim.mk.injEq, and_true, true_and] at hr
  simp only [TSt.mk.injEq] at hst
  simp only [and_assoc] at hr
  simp only at hchkO hchkI hok
  obtain ⟨hop, rfl, hpt, rfl, hm0⟩ := hr
  obtain ⟨hcap, rfl, -, -⟩ := hst
  refine ⟨committed, Ts, mO, mI, mS, hok, hmO, hmI, hmS, hsl, hchkO, hchkI, ?_, ?_, hop, hpt⟩
  · rw [hm0, hcap]
  · simp only at hz1 hz3 hz4 hz5 hz6 hz7
    rw [hz1, hz2, hz3, hz4, hz5, hz6, hz7]
    simp

end
end LeanVM.Guest.B1.VerifySub
