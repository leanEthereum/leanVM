module

public import Quantum.Xmss.Assembly.GameCongr
public import Quantum.Sphincs.Assembly.FullTable

@[expose] public section

/-!
# leanSPHINCS's template game at congruent public data and hidden values

`gameT M upd pol pub A` reads the public data `pub` only through `PK.seed`, the permutation and the
program ports of the slots and `H_msg` calls it makes public. `realizeT_gameT_congr`: realized at
`v` and `v'`, the games at `pub` and `pub'` are equal when the seeds and permutations are, `v` and
`v'` agree on every coordinate the game may reveal (the tabulated positions `FullPos`, the
randomizers, the digest policy's coordinates), and the realized ports agree on every in-table slot
and every `H_msg` call. Along the way: the congruences of `progPorts`, `progSlots`, `forsOpenT`,
`signLayerT` (in-range keys, `KeyIn`), `signT`, `challengeT`, `challengedT`, `prefixT`, `verifyT`;
`grindK_pub` (the counter search reads `pub` only through `PK.seed` and `π`); `pathCells_congr`.
The combinators are leanXMSS's (`Quantum.Xmss.Assembly.GameCongr`).
-/

open Quantum.SufCma

open Quantum QuantumRuntime Quantum.Sponge Sphincs
open HashSig (Digest Message)
open Quantum.Xmss (X Z)
open Quantum.Xmss.Hybrid (LazyProg Agree)
open Quantum.Xmss.Assembly (realizeT realizeT_bind₂_congr realizeT_bind_congr
  realizeT_revealThen_congr progR realizeT_readLift_indep realizeT_substitute)

namespace Quantum.Sphincs.Assembly

/-! ## The realized cells -/

/-- **Absorptions with agreeing cells** realize alike. -/
theorem pathCells_congr {pub pub' : Pub} {b b' : ℕ → X} {cor cor' : X → X → X} {n : ℕ}
    (h : ∀ j < n, cellK pub b j = cellK pub' b' j ∧ cellK' pub b j = cellK' pub' b' j ∧
      cellH pub b (n - 1) cor j = cellH pub' b' (n - 1) cor' j) :
    pathCells pub b cor n = pathCells pub' b' cor' n := by
  rw [pathCells, pathCells]
  refine List.flatMap_congr fun j hj ↦ ?_
  obtain ⟨e1, e2, e3⟩ := h j (List.mem_range.mp hj)
  rw [e1, e2, e3]

/-! ## The congruence -/

section congr

variable (M : Type) (upd : TrialUpd M)

/-- **The counter search reads `pub` only through `PK.seed` and `π`.** -/
theorem grindK_pub {pub pub' : Pub} (hP : pub.seed = pub'.seed) (hπ : pub.perm = pub'.perm)
    (B : QReg) (K : Key) (m : Digest) :
    ∀ n c, grindK M upd pub B K m n c = grindK M upd pub' B K m n c
  | 0, _ => rfl
  | n + 1, c => by
    rw [grindK, grindK]
    simp only [grindK_pub hP hπ B K m n, trialInput, hP, hπ]

theorem realizeT_progPorts_congr {v v' : (s : HPos) → XD s} (B : QReg) :
    ∀ {ps ps' : List (LazyProg X Z HPos XD)},
      ps.map (LazyProg.realize v) = ps'.map (LazyProg.realize v') →
        realizeT v (progPorts M B ps) = realizeT v' (progPorts M B ps')
  | [], [], _ => rfl
  | [], _ :: _, h => (List.cons_ne_nil _ _ h.symm).elim
  | _ :: _, [], h => (List.cons_ne_nil _ _ h).elim
  | p :: ps, p' :: ps', h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [progPorts, progPorts]
    exact congrArg₂ (progR B) h.1 (realizeT_progPorts_congr B h.2)

theorem realizeT_progSlots_congr {pub pub' : Pub} {v v' : (s : HPos) → XD s} (B : QReg) :
    ∀ ss : List Slot,
      (∀ s ∈ ss, (slotPorts pub s).map (LazyProg.realize v) =
        (slotPorts pub' s).map (LazyProg.realize v')) →
        realizeT v (progSlots M pub B ss) = realizeT v' (progSlots M pub' B ss)
  | [], _ => rfl
  | s :: ss, h => by
    rw [progSlots, progSlots]
    exact realizeT_bind₂_congr (realizeT_progPorts_congr M B (h s List.mem_cons_self)) fun _ ↦
      realizeT_progSlots_congr B ss fun s' hs' ↦ h s' (List.mem_cons_of_mem _ hs')

/-- Values agreeing on the tabulated positions agree on a set of tabulated positions. -/
theorem agree_valSet {v v' : (s : HPos) → XD s}
    (hval : ∀ q, FullPos q → v (.val q) = v' (.val q)) {T : Finset ValPos}
    (hT : ∀ q ∈ T, FullPos q) : Agree (valSet T) v v' := fun s hs ↦ by
  obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hs
  exact hval q (hT q hq)

/-- **A FORS opening** at agreeing tabulated values and in-table slot ports. -/
theorem realizeT_forsOpenT_congr {pub pub' : Pub} {v v' : (s : HPos) → XD s}
    (hval : ∀ q, FullPos q → v (.val q) = v' (.val q))
    (hslot : ∀ s, InTable s →
      (slotPorts pub s).map (LazyProg.realize v) = (slotPorts pub' s).map (LazyProg.realize v'))
    (B : QReg) (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex) :
    realizeT v (forsOpenT M pub B idx lv) = realizeT v' (forsOpenT M pub' B idx lv) := by
  rw [forsOpenT, forsOpenT]
  refine realizeT_revealThen_congr _ (agree_valSet hval fullPos_forsNeed) fun r ↦ ?_
  exact realizeT_bind₂_congr (realizeT_progSlots_congr M B _ fun s hs ↦
    hslot s (inTable_of_mem_forsSlots hs)) fun _ ↦ rfl

/-- **A layer signature by an in-range key** at agreeing tabulated values and in-table slot
ports. -/
theorem realizeT_signLayerT_congr {pub pub' : Pub} {v v' : (s : HPos) → XD s}
    (hP : pub.seed = pub'.seed) (hπ : pub.perm = pub'.perm)
    (hval : ∀ q, FullPos q → v (.val q) = v' (.val q))
    (hslot : ∀ s, InTable s →
      (slotPorts pub s).map (LazyProg.realize v) = (slotPorts pub' s).map (LazyProg.realize v'))
    (B : QReg) {K : Key} (hK : KeyIn K) :
    realizeT v (signLayerT M upd pub B K) = realizeT v' (signLayerT M upd pub' B K) := by
  rw [signLayerT, signLayerT]
  refine realizeT_revealThen_congr _ (fun s hs ↦ by
    rw [Finset.mem_singleton.mp hs]
    exact hval _ (fullPos_msgPos hK)) fun r₀ ↦ ?_
  rw [grindK_pub M upd hP hπ]
  refine realizeT_bind₂_congr (realizeT_readLift_indep v v' _) fun g ↦ ?_
  rcases g with _ | ⟨c, x⟩
  · rfl
  · refine realizeT_revealThen_congr _
      (agree_valSet hval fun _ hq ↦ fullPos_layerNeed hK hq) fun r ↦ ?_
    exact realizeT_bind₂_congr (realizeT_progSlots_congr M B _ fun s hs ↦
      hslot s (inTable_of_mem_layerSlots hK hs)) fun _ ↦ rfl

/-- **A signature** at agreeing revealed values and agreeing slot and `H_msg` ports. -/
theorem realizeT_signT_congr (pol : DigestPolicy) {pub pub' : Pub} {v v' : (s : HPos) → XD s}
    (hP : pub.seed = pub'.seed) (hπ : pub.perm = pub'.perm)
    (hval : ∀ q, FullPos q → v (.val q) = v' (.val q))
    (hrnd : ∀ msg, v (.rnd msg) = v' (.rnd msg))
    (hneed : ∀ T msg, Agree (pol.need T msg) v v')
    (hslot : ∀ s, InTable s →
      (slotPorts pub s).map (LazyProg.realize v) = (slotPorts pub' s).map (LazyProg.realize v'))
    (hhmsg : ∀ T msg i, (hmsgPorts pub pol T msg i).map (LazyProg.realize v) =
      (hmsgPorts pub' pol T msg i).map (LazyProg.realize v'))
    (B : QReg) (msg : Message) :
    realizeT v (signT M upd pol pub B msg) = realizeT v' (signT M upd pol pub' B msg) := by
  rw [signT, signT]
  refine realizeT_revealThen_congr _ (fun s hs ↦ ?_) fun r₁ ↦ ?_
  · rcases Finset.mem_insert.mp hs with rfl | hs
    · exact hval _ fullPos_rootPos
    · rw [Finset.mem_singleton.mp hs]
      exact hrnd msg
  refine realizeT_revealThen_congr _ (hneed _ _) fun r₂ ↦ ?_
  refine realizeT_bind₂_congr (realizeT_progPorts_congr M B ?_) fun _ ↦ ?_
  · rw [digestPorts, digestPorts, List.map_append, List.map_append, hhmsg, hhmsg]
  refine realizeT_bind₂_congr (realizeT_forsOpenT_congr M hval hslot B _ _) fun _ ↦ ?_
  refine realizeT_bind₂_congr
    (realizeT_signLayerT_congr M upd hP hπ hval hslot B (keyIn_keyOf 0 _)) fun s₀ ↦ ?_
  rcases s₀ with _ | bottom
  · rfl
  refine realizeT_bind₂_congr
    (realizeT_signLayerT_congr M upd hP hπ hval hslot B (keyIn_keyOf 1 _)) fun s₁ ↦ ?_
  rcases s₁ with _ | middle
  · rfl
  exact realizeT_bind₂_congr
    (realizeT_signLayerT_congr M upd hP hπ hval hslot B (keyIn_keyOf 2 _)) fun s₂ ↦ by
      rcases s₂ with _ | top <;> rfl

theorem realizeT_challengeT_congr (pol : DigestPolicy) {pub pub' : Pub}
    {v v' : (s : HPos) → XD s} (hP : pub.seed = pub'.seed) (hπ : pub.perm = pub'.perm)
    (hval : ∀ q, FullPos q → v (.val q) = v' (.val q))
    (hrnd : ∀ msg, v (.rnd msg) = v' (.rnd msg))
    (hneed : ∀ T msg, Agree (pol.need T msg) v v')
    (hslot : ∀ s, InTable s →
      (slotPorts pub s).map (LazyProg.realize v) = (slotPorts pub' s).map (LazyProg.realize v'))
    (hhmsg : ∀ T msg i, (hmsgPorts pub pol T msg i).map (LazyProg.realize v) =
      (hmsgPorts pub' pol T msg i).map (LazyProg.realize v'))
    (A : QReg) (c : (QuantumComp.toIPFunctor LocalSig.instruments.{0} sAdvSpec).A A) :
    realizeT v (challengeT M upd pol pub A c) = realizeT v' (challengeT M upd pol pub' A c) := by
  obtain ⟨P, π, t⟩ := pub
  obtain ⟨P', π', t'⟩ := pub'
  obtain rfl : P = P' := hP
  obtain rfl : π = π' := hπ
  rcases c with o | ⟨p | msg, E, ℓ⟩
  · exact realizeT_readLift_indep v v' _
  · exact realizeT_readLift_indep v v' _
  · refine realizeT_bind_congr ?_ fun _ _ ↦ rfl
    rw [signAt, signAt]
    refine realizeT_bind₂_congr rfl fun _ ↦ ?_
    exact realizeT_signT_congr M upd pol (pub := ⟨P, π, t⟩) (pub' := ⟨P, π, t'⟩) rfl rfl hval hrnd
      hneed hslot hhmsg _ msg

theorem realizeT_challengedT_congr (pol : DigestPolicy) {pub pub' : Pub}
    {v v' : (s : HPos) → XD s} (hP : pub.seed = pub'.seed) (hπ : pub.perm = pub'.perm)
    (hval : ∀ q, FullPos q → v (.val q) = v' (.val q))
    (hrnd : ∀ msg, v (.rnd msg) = v' (.rnd msg))
    (hneed : ∀ T msg, Agree (pol.need T msg) v v')
    (hslot : ∀ s, InTable s →
      (slotPorts pub s).map (LazyProg.realize v) = (slotPorts pub' s).map (LazyProg.realize v'))
    (hhmsg : ∀ T msg i, (hmsgPorts pub pol T msg i).map (LazyProg.realize v) =
      (hmsgPorts pub' pol T msg i).map (LazyProg.realize v'))
    {A B : QReg} {α : Type} (x : QComp sAdvSpec A B α) :
    realizeT v (challengedT M upd pol pub x) = realizeT v' (challengedT M upd pol pub' x) := by
  have h₁ := realizeT_substitute (M := M) (good := goodAll) v (challengeT M upd pol pub) x
  have h₂ := realizeT_substitute (M := M) (good := goodAll) v' (challengeT M upd pol pub') x
  refine (h₁.trans ?_).trans h₂.symm
  exact congrArg (fun σ ↦ IPFunctor.IFreeM.substitute σ x) (funext fun A ↦ funext fun c ↦
    realizeT_challengeT_congr M upd pol hP hπ hval hrnd hneed hslot hhmsg A c)

/-- **The challenge prefix congruence.** -/
theorem realizeT_prefixT_congr (pol : DigestPolicy) (A : SAdversary) {pub pub' : Pub}
    {v v' : (s : HPos) → XD s} (hP : pub.seed = pub'.seed) (hπ : pub.perm = pub'.perm)
    (hval : ∀ q, FullPos q → v (.val q) = v' (.val q))
    (hrnd : ∀ msg, v (.rnd msg) = v' (.rnd msg))
    (hneed : ∀ T msg, Agree (pol.need T msg) v v')
    (hslot : ∀ s, InTable s →
      (slotPorts pub s).map (LazyProg.realize v) = (slotPorts pub' s).map (LazyProg.realize v'))
    (hhmsg : ∀ T msg i, (hmsgPorts pub pol T msg i).map (LazyProg.realize v) =
      (hmsgPorts pub' pol T msg i).map (LazyProg.realize v')) :
    realizeT v (prefixT M upd pol pub A) = realizeT v' (prefixT M upd pol pub' A) := by
  obtain ⟨P, π, t⟩ := pub
  obtain ⟨P', π', t'⟩ := pub'
  obtain rfl : P = P' := hP
  obtain rfl : π = π' := hπ
  refine realizeT_revealThen_congr _ (fun s hs ↦ by
    rw [Finset.mem_singleton.mp hs]
    exact hval _ fullPos_rootPos) fun r₀ ↦ ?_
  exact realizeT_bind₂_congr
    (realizeT_challengedT_congr M upd pol (pub := ⟨P, π, t⟩) (pub' := ⟨P, π, t'⟩) rfl rfl hval
      hrnd hneed hslot hhmsg _) fun _ ↦ rfl

omit upd in
/-- **The verification** reads `pub` only through `π`. -/
theorem realizeT_verifyT_congr {pub pub' : Pub} {v v' : (s : HPos) → XD s}
    (hπ : pub.perm = pub'.perm)
    (x : PublicKey × (Forgery × SignLog Message (Option Signature))) :
    realizeT v (verifyT M pub x) = realizeT v' (verifyT M pub' x) := by
  obtain ⟨P, π, t⟩ := pub
  obtain ⟨P', π', t'⟩ := pub'
  obtain rfl : π = π' := hπ
  exact realizeT_bind₂_congr (realizeT_readLift_indep v v' _) fun _ ↦ rfl

/-- **The game congruence.** Realized at `v` and `v'`, the template games at `pub` and `pub'` are
equal when the seeds and permutations are, the values agree on the tabulated positions, the
randomizers and the digest policy's coordinates, and the realized ports of the in-table slots and
the `H_msg` calls agree. -/
theorem realizeT_gameT_congr (pol : DigestPolicy) (A : SAdversary) {pub pub' : Pub}
    {v v' : (s : HPos) → XD s} (hP : pub.seed = pub'.seed) (hπ : pub.perm = pub'.perm)
    (hval : ∀ q, FullPos q → v (.val q) = v' (.val q))
    (hrnd : ∀ msg, v (.rnd msg) = v' (.rnd msg))
    (hneed : ∀ T msg, Agree (pol.need T msg) v v')
    (hslot : ∀ s, InTable s →
      (slotPorts pub s).map (LazyProg.realize v) = (slotPorts pub' s).map (LazyProg.realize v'))
    (hhmsg : ∀ T msg i, (hmsgPorts pub pol T msg i).map (LazyProg.realize v) =
      (hmsgPorts pub' pol T msg i).map (LazyProg.realize v')) :
    realizeT v (gameT M upd pol pub A) = realizeT v' (gameT M upd pol pub' A) := by
  obtain ⟨P, π, t⟩ := pub
  obtain ⟨P', π', t'⟩ := pub'
  obtain rfl : P = P' := hP
  obtain rfl : π = π' := hπ
  refine realizeT_revealThen_congr _ (fun s hs ↦ by
    rw [Finset.mem_singleton.mp hs]
    exact hval _ fullPos_rootPos) fun r₀ ↦ ?_
  exact realizeT_bind₂_congr
    (realizeT_challengedT_congr M upd pol (pub := ⟨P, π, t⟩) (pub' := ⟨P, π, t'⟩) rfl rfl hval
      hrnd hneed hslot hhmsg _) fun _ ↦
      realizeT_bind₂_congr (realizeT_readLift_indep v v' _) fun _ ↦ rfl

end congr

end Quantum.Sphincs.Assembly

end
