module

public import NativeVm.Equiv.Basic
public import NativeVm.Equiv.Field

/-!
# The model's transcript is the statement's

The sponge first: `SpongeW.Rel` is kept by `absorb`, `duplex`, `squeeze` and `absorbNonce` over
Keccak-f[1600] (`duplexInput_eq`: the waiting scalars' lanes are the statement's `pendingLanes`).
Then each operation of the model simulates its constructor of the verifier language (`Sim`):
`readScalar(s)`, `sampleChallenge(s)`, `grind` (`powOkW` is `powOk`), `readCommitment`,
`queryOpenings` (the model's `openPhase` is the statement's: the leaf hash and the Merkle climb are
Keccak-256 of the same bytes), and the sumcheck rounds.
-/

@[expose] public section

namespace NativeVm.Equiv

open NativeVm.Model LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.KeccakHash

/-! ## The sponge -/

/-- Lane `i` of the waiting scalars, as the model reads it. -/
def pendingLane (pending : List (EW × UInt64)) (i : ℕ) : UInt64 :=
  match pending[i / 4]? with
  | some (x, tag) =>
    if i % 4 = 0 then x.c0 else if i % 4 = 1 then x.c1 else if i % 4 = 2 then 0 else tag
  | none => 0

/-! Keccak-f is never unfolded here: every fact holds of the permutation as a black box. -/

attribute [local irreducible] keccakF1600

theorem pendingLanes_getD : ∀ (pending : List (EW × UInt64)) (i : ℕ),
    (pendingLanes (pending.map fun p ↦ (p.1.toE, p.2.toNat))).getD i 0 = pendingLane pending i
  | [], i => by simp [pendingLanes, pendingLane]
  | p :: pending, i => by
    rw [List.map_cons, pendingLanes, List.flatMap_cons, ← pendingLanes, List.getD_eq_getElem?_getD]
    by_cases hi : i < 4
    · rw [List.getElem?_append_left (by simpa using hi)]
      interval_cases i <;> simp [pendingLane]
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 4 := ⟨i - 4, by omega⟩
      rw [List.getElem?_append_right (by simp), ← List.getD_eq_getElem?_getD]
      simp only [List.length_cons, List.length_nil, Nat.add_sub_cancel]
      rw [pendingLanes_getD pending]
      simp [pendingLane, Nat.add_div_right, Nat.add_mod_right]

theorem lane_eq (v : KeccakState) {i : ℕ} (hi : i < 25) : Keccak.lane v i = v[i] := by
  simp only [Keccak.lane, Array.getD_eq_getD_getElem?, Vector.getElem?_toArray,
    Vector.getElem?_eq_getElem hi, Option.getD_some]

theorem _root_.NativeVm.Model.SpongeW.Rel.duplexInput_eq {w : SpongeW} {s : Sponge}
    (h : w.Rel s) : w.duplexInput = duplexInput s := by
  apply Vector.ext
  intro i hi
  simp only [SpongeW.duplexInput, duplexInput, Vector.getElem_ofFn]
  split
  · rw [← h.pending, pendingE, pendingLanes_getD]
    simp only [pendingLane, Array.getElem?_toList]
    rfl
  · exact (congrArg (fun v : KeccakState ↦ v[i]) h.state).trans (lane_eq _ hi).symm

/-! The statement's sponge steps over any permutation, by their definitions. -/

section Steps

variable (π : KeccakState → KeccakState)

theorem duplex_id (s : Sponge) :
    Id.run (Compile.duplex (m := Id) π s) = ⟨π (duplexInput s), [], s.ground⟩ := rfl

theorem absorb_id (s : Sponge) (x : E) (tag : ℕ) :
    Id.run (Compile.absorb (m := Id) π s x tag) =
      let sp := if s.pending.length = rateScalars then Id.run (Compile.duplex (m := Id) π s) else s
      { sp with pending := sp.pending ++ [(x, tag)] } := by
  simp only [Compile.absorb]
  split <;> rfl

theorem squeeze_id_some (s : Sponge) {c : E} (h : s.ground = some c) :
    Id.run (Compile.squeeze (m := Id) π s) = (c, { s with ground := none }) := by
  simp only [Compile.squeeze, h]
  rfl

theorem squeeze_id_none (s : Sponge) (h : s.ground = none) :
    Id.run (Compile.squeeze (m := Id) π s) =
      (challengeOf (π (duplexInput s)), ⟨π (duplexInput s), [], none⟩) := by
  obtain ⟨st, p, g⟩ := s
  obtain rfl : g = none := h
  rfl

theorem absorbNonce_id (s : Sponge) (n : E) :
    Id.run (Compile.absorbNonce (m := Id) π s n) =
      let sp := Id.run (Compile.duplex (m := Id) π (Id.run (Compile.absorb (m := Id) π s n dsPowNonce)))
      (Keccak.lane sp.state 2, { sp with ground := some (challengeOf sp.state) }) := rfl

end Steps

theorem _root_.NativeVm.Model.SpongeW.Rel.duplex {w : SpongeW} {s : Sponge} (h : w.Rel s) :
    w.duplex.Rel ⟨keccakF1600 (duplexInput s), [], s.ground⟩ :=
  ⟨congrArg keccakF1600 h.duplexInput_eq, rfl, h.ground⟩

theorem _root_.NativeVm.Model.SpongeW.Rel.absorb {w : SpongeW} {s : Sponge} (h : w.Rel s)
    (x : EW) (tag : UInt64) :
    (w.absorb x tag).Rel (Id.run (Compile.absorb (m := Id) keccakF1600 s x.toE tag.toNat)) := by
  have hlen : w.pending.size = s.pending.length := by rw [← h.pending, pendingE]; simp
  rw [absorb_id, duplex_id]
  by_cases hc : s.pending.length = rateScalars
  · simp only [SpongeW.absorb, hlen, hc, ↓reduceIte]
    have hd := h.duplex
    exact ⟨hd.state, by simp [pendingE, SpongeW.duplex], hd.ground⟩
  · simp only [SpongeW.absorb, hlen, hc, ↓reduceIte]
    exact ⟨h.state, by simp [pendingE, ← h.pending], h.ground⟩

theorem toE_challengeOf (state : KeccakState) :
    (SpongeW.challengeOf state).toE = challengeOf state := by
  simp [SpongeW.challengeOf, challengeOf, EW.toE, lane_eq]

theorem _root_.NativeVm.Model.SpongeW.Rel.squeeze {w : SpongeW} {s : Sponge} (h : w.Rel s) :
    w.squeeze.1.toE = (Id.run (Compile.squeeze (m := Id) keccakF1600 s)).1 ∧
      w.squeeze.2.Rel (Id.run (Compile.squeeze (m := Id) keccakF1600 s)).2 := by
  have hg := h.ground
  rcases hw : w.ground with _ | c
  · rw [hw] at hg
    have hs : s.ground = none := hg.symm
    rw [squeeze_id_none _ _ hs]
    simp only [SpongeW.squeeze, hw]
    have hd := h.duplex
    rw [hs] at hd
    exact ⟨by rw [toE_challengeOf, hd.state], hd⟩
  · rw [hw] at hg
    rw [squeeze_id_some _ _ hg.symm]
    simp only [SpongeW.squeeze, hw]
    exact ⟨by simp, h.state, h.pending, rfl⟩

theorem _root_.NativeVm.Model.SpongeW.Rel.absorbNonce {w : SpongeW} {s : Sponge} (h : w.Rel s)
    (nonce : EW) :
    (w.absorbNonce nonce).1 = (Id.run (Compile.absorbNonce (m := Id) keccakF1600 s nonce.toE)).1 ∧
      (w.absorbNonce nonce).2.Rel
        (Id.run (Compile.absorbNonce (m := Id) keccakF1600 s nonce.toE)).2 := by
  have ha := h.absorb nonce dsPowNonce.toUInt64
  rw [show dsPowNonce.toUInt64.toNat = dsPowNonce from rfl] at ha
  have hd := ha.duplex
  rw [absorbNonce_id, duplex_id]
  constructor
  · show (w.absorb nonce dsPowNonce.toUInt64).duplex.state[2] =
      Keccak.lane (keccakF1600 (duplexInput
        (Id.run (Compile.absorb (m := Id) keccakF1600 s nonce.toE dsPowNonce)))) 2
    rw [hd.state, lane_eq _ (by decide : 2 < 25)]
  · refine ⟨hd.state, hd.pending, ?_⟩
    show some (SpongeW.challengeOf (w.absorb nonce dsPowNonce.toUInt64).duplex.state).toE = _
    rw [toE_challengeOf, hd.state]

/-! ## The states -/

theorem powOkW_eq (bits : ℕ) (pow : UInt64) : powOkW bits pow = powOk bits pow := by
  unfold powOkW powOk
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  split
  · rename_i hb
    rw [beq_iff_eq, ← UInt64.toNat_inj, Nat.mod_eq_of_lt (lt_of_lt_of_le pow.toNat_lt
      (Nat.pow_le_pow_right (by decide) hb))]
    rfl
  · rename_i hb
    have h1 : ((1 : UInt64) <<< bits.toUInt64).toNat = 2 ^ bits := by
      have hb64 : bits < 64 := by omega
      rw [UInt64.toNat_shiftLeft, Nat.toUInt64_eq, UInt64.toNat_ofNat',
        Nat.mod_eq_of_lt (lt_trans hb64 (by decide) : bits < 2 ^ 64), Nat.mod_eq_of_lt hb64,
        UInt64.toNat_one, Nat.one_shiftLeft]
      exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide : 1 < 2) hb64)
    have h2 : (((1 : UInt64) <<< bits.toUInt64) - 1).toNat = 2 ^ bits - 1 := by
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, h1]; exact Nat.one_le_two_pow),
        h1]
      rfl
    rw [beq_iff_eq, ← UInt64.toNat_inj, UInt64.toNat_and, h2, Nat.and_two_pow_sub_one_eq_mod]
    rfl

theorem _root_.NativeVm.Model.TState.Rel.stream_some {t : TState} {s : VerifierProgramState}
    (h : t.Rel s) {x : EW} (hx : t.stream[t.cursor]? = some x) :
    s.stream = x.toE :: (t.stream.toList.drop (t.cursor + 1)).map EW.toE := by
  obtain ⟨hlt, rfl⟩ := Array.getElem?_eq_some_iff.mp hx
  rw [← h.stream, List.drop_eq_getElem_cons (by simpa using hlt)]
  simp

theorem _root_.NativeVm.Model.TState.Rel.stream_none {t : TState} {s : VerifierProgramState}
    (h : t.Rel s) (hx : t.stream[t.cursor]? = none) : s.stream = [] := by
  rw [← h.stream, List.drop_eq_nil_of_le (by simpa using Array.getElem?_eq_none_iff.mp hx)]
  rfl

/-- Reading the scalar at the cursor keeps the states related. -/
theorem _root_.NativeVm.Model.TState.Rel.advance {t : TState} {s : VerifierProgramState}
    (h : t.Rel s) {x : EW} (hx : t.stream[t.cursor]? = some x) {sp : SpongeW} {sp' : Sponge}
    (hsp : sp.Rel sp') :
    TState.Rel { t with cursor := t.cursor + 1, sponge := sp }
      { s with stream := (t.stream.toList.drop (t.cursor + 1)).map EW.toE, sponge := sp' } :=
  ⟨hsp, (Array.getElem?_eq_some_iff.mp hx).1, rfl, h.phase_le, h.openings, h.roots⟩

theorem _root_.NativeVm.Model.TState.Rel.withSponge {t : TState} {s : VerifierProgramState}
    (h : t.Rel s) {sp : SpongeW} {sp' : Sponge} (hsp : sp.Rel sp') :
    TState.Rel { t with sponge := sp } { s with sponge := sp' } :=
  ⟨hsp, h.cursor_le, h.stream, h.phase_le, h.openings, h.roots⟩

/-! ## The statement's steps -/

section Steps

variable {β : Type}

theorem runSpec_read_cons (k : E → VerifierProgram β) {s : VerifierProgramState} {x : E}
    {xs : List E} (hs : s.stream = x :: xs) (hg : s.sponge.ground = none) :
    runSpec (.read k) s =
      runSpec (k x)
        { s with
          sponge := Id.run (absorb (m := Id) keccakF1600 s.sponge x dsObserve)
          stream := xs } := by
  obtain ⟨⟨st, p, g⟩, stream, os, rs⟩ := s
  obtain rfl : stream = x :: xs := hs
  obtain rfl : g = none := hg
  rfl

theorem runSpec_read_nil (k : E → VerifierProgram β) {s : VerifierProgramState}
    (hs : s.stream = []) : runSpec (.read k) s = none := by
  obtain ⟨sp, stream, os, rs⟩ := s
  obtain rfl : stream = [] := hs
  rfl

theorem runSpec_read_ground (k : E → VerifierProgram β) {s : VerifierProgramState} {c : E}
    (hg : s.sponge.ground = some c) : runSpec (.read k) s = none := by
  obtain ⟨⟨st, p, g⟩, _ | ⟨x, xs⟩, os, rs⟩ := s
  · rfl
  · obtain rfl : g = some c := hg
    rfl

theorem runSpec_sample (k : E → VerifierProgram β) (s : VerifierProgramState) :
    runSpec (.sample k) s =
      runSpec (k (Id.run (squeeze (m := Id) keccakF1600 s.sponge)).1)
        { s with sponge := (Id.run (squeeze (m := Id) keccakF1600 s.sponge)).2 } := rfl

theorem runSpec_grind_cons (bits : ℕ) (k : VerifierProgram β) {s : VerifierProgramState} {x : E}
    {xs : List E} (hs : s.stream = x :: xs) (hg : s.sponge.ground = none) :
    runSpec (.grind bits k) s =
      if powOk bits (Id.run (absorbNonce (m := Id) keccakF1600 s.sponge x)).1 then
        runSpec k
          { s with
            sponge := (Id.run (absorbNonce (m := Id) keccakF1600 s.sponge x)).2
            stream := xs }
      else none := by
  obtain ⟨⟨st, p, g⟩, stream, os, rs⟩ := s
  obtain rfl : stream = x :: xs := hs
  obtain rfl : g = none := hg
  rfl

theorem runSpec_grind_nil (bits : ℕ) (k : VerifierProgram β) {s : VerifierProgramState}
    (hs : s.stream = []) : runSpec (.grind bits k) s = none := by
  obtain ⟨sp, stream, os, rs⟩ := s
  obtain rfl : stream = [] := hs
  rfl

theorem runSpec_grind_ground (bits : ℕ) (k : VerifierProgram β) {s : VerifierProgramState}
    {c : E} (hg : s.sponge.ground = some c) : runSpec (.grind bits k) s = none := by
  obtain ⟨⟨st, p, g⟩, _ | ⟨x, xs⟩, os, rs⟩ := s
  · rfl
  · obtain rfl : g = some c := hg
    rfl

end Steps

/-! ## The model's steps -/

theorem nextScalar_run (t : TState) :
    nextScalar.run t =
      if t.sponge.ground.isSome then none
      else (t.stream[t.cursor]?).map fun x ↦ (x, { t with cursor := t.cursor + 1 }) := by
  unfold nextScalar
  show (if t.sponge.ground.isSome then reject else _) t = _
  split
  · rfl
  · rcases t.stream[t.cursor]? <;> rfl

theorem readScalar_run (t : TState) :
    readScalar.run t = (nextScalar.run t).map fun p ↦
      (p.1, { p.2 with sponge := p.2.sponge.absorb p.1 dsObserve.toUInt64 }) := by
  rw [Model.readScalar, StateT.run_bind]
  rcases nextScalar.run t with _ | ⟨x, t'⟩ <;> rfl

theorem sampleChallenge_run (t : TState) :
    sampleChallenge.run t = some (t.sponge.squeeze.1, { t with sponge := t.sponge.squeeze.2 }) :=
  rfl

theorem grind_run {bits : ℕ} (hb : bits ≠ 0) (t : TState) :
    (grind bits).run t = (nextScalar.run t).bind fun p ↦
      if powOkW bits (p.2.sponge.absorbNonce p.1).1 then
        some ((), { p.2 with sponge := (p.2.sponge.absorbNonce p.1).2 })
      else none := by
  simp only [Model.grind, hb, ↓reduceIte]
  rw [StateT.run_bind]
  rcases nextScalar.run t with _ | ⟨x, t'⟩
  · rfl
  · show (Model.require _).run _ = _
    unfold Model.require
    by_cases hc : powOkW bits (t'.sponge.absorbNonce x).1 = true <;>
      simp only [hc, ↓reduceIte, Option.bind_some] <;> rfl

/-! ## Reads and samples -/

namespace Sim

theorem readScalar : Sim Model.readScalar VerifierProgram.readScalar fun a b ↦ a.toE = b := by
  intro t s h
  rw [readScalar_run, nextScalar_run]
  have hg := h.sponge.ground
  rcases hw : t.sponge.ground with _ | c
  · rw [hw] at hg
    rcases hx : t.stream[t.cursor]? with _ | x
    · simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Option.map_none]
      rw [VerifierProgram.readScalar, runSpec_read_nil _ (h.stream_none hx)]
      exact .none
    · simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Option.map_some]
      rw [VerifierProgram.readScalar, runSpec_read_cons _ (h.stream_some hx) hg.symm, runSpec_ret]
      exact .some ⟨rfl, h.advance hx (h.sponge.absorb x dsObserve.toUInt64)⟩
  · rw [hw] at hg
    simp only [Option.isSome_some, ↓reduceIte, Option.map_none]
    rw [VerifierProgram.readScalar, runSpec_read_ground _ hg.symm]
    exact .none

theorem sampleChallenge :
    Sim Model.sampleChallenge VerifierProgram.sampleChallenge fun a b ↦ a.toE = b := by
  intro t s h
  rw [sampleChallenge_run, VerifierProgram.sampleChallenge, runSpec_sample, runSpec_ret]
  have hs := h.sponge.squeeze
  exact .some ⟨hs.1, h.withSponge hs.2⟩

/-- A loop pushing what `m` returns, against a program reading a list by `p` one at a time. -/
theorem pushLoop {m : VM EW} {p : VerifierProgram E} {X : ℕ → VerifierProgram (List E)}
    (hm : Sim m p fun a b ↦ a.toE = b) (h0 : X 0 = Pure.pure [])
    (hs : ∀ n, X (n + 1) = do let x ← p; let xs ← X n; Pure.pure (x :: xs)) :
    ∀ (l : List ℕ) (acc : Array EW) (pre : List E), acc.toList.map EW.toE = pre →
      Sim (l.foldlM (fun acc _ ↦ do Pure.pure (acc.push (← m))) acc)
        (do let xs ← X l.length; Pure.pure (pre ++ xs))
        fun a b ↦ a.toList.map EW.toE = b ∧ b.length = pre.length + l.length
  | [], acc, pre, hacc => by
    rw [List.foldlM_nil, List.length_nil, h0, pure_bind, List.append_nil]
    exact Sim.pure ⟨hacc, rfl⟩
  | _ :: l, acc, pre, hacc => by
    simp only [List.foldlM_cons, bind_assoc, pure_bind, List.length_cons, hs]
    refine Sim.bind hm fun y x hyx ↦ ?_
    have := pushLoop hm h0 hs l (acc.push y) (pre ++ [x]) (by simp [hacc, hyx])
    simp only [List.append_assoc, List.cons_append, List.nil_append, List.length_append,
      List.length_cons, List.length_nil] at this
    exact this.mono fun _ _ hab ↦ ⟨hab.1, by omega⟩

theorem readScalars (n : ℕ) :
    Sim (Model.readScalars n) (VerifierProgram.readScalars n)
      fun a b ↦ a.toList.map EW.toE = b ∧ b.length = n := by
  have := pushLoop (X := VerifierProgram.readScalars) readScalar rfl (fun _ ↦ rfl) (List.range n)
    #[] [] rfl
  simp only [List.length_range, List.nil_append, bind_pure, List.length_nil, Nat.zero_add]
    at this
  exact this

theorem sampleChallenges (n : ℕ) :
    Sim (Model.sampleChallenges n) (VerifierProgram.sampleChallenges n)
      fun a b ↦ a.toList.map EW.toE = b ∧ b.length = n := by
  have := pushLoop (X := VerifierProgram.sampleChallenges) sampleChallenge rfl (fun _ ↦ rfl)
    (List.range n) #[] [] rfl
  simp only [List.length_range, List.nil_append, bind_pure, List.length_nil, Nat.zero_add]
    at this
  exact this

theorem grind (bits : ℕ) :
    Sim (Model.grind bits) (VerifierProgram.grindProofOfWork bits) fun _ _ ↦ True := by
  by_cases hb : bits = 0
  · subst hb
    exact Sim.ret trivial
  intro t s h
  simp only [VerifierProgram.grindProofOfWork, hb, ↓reduceIte]
  rw [grind_run hb, nextScalar_run]
  have hg := h.sponge.ground
  rcases hw : t.sponge.ground with _ | c
  · rw [hw] at hg
    rcases hx : t.stream[t.cursor]? with _ | x
    · simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Option.map_none,
        Option.bind_none]
      rw [runSpec_grind_nil _ _ (h.stream_none hx)]
      exact .none
    · simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Option.map_some,
        Option.bind_some]
      rw [runSpec_grind_cons _ _ (h.stream_some hx) hg.symm]
      have ha := h.sponge.absorbNonce x
      rw [powOkW_eq, ha.1]
      split
      · rw [runSpec_ret]
        exact .some ⟨trivial, h.advance hx ha.2⟩
      · exact .none
  · rw [hw] at hg
    simp only [Option.isSome_some, ↓reduceIte, Option.bind_none]
    rw [runSpec_grind_ground _ _ hg.symm]
    exact .none

/-! ## Sumcheck rounds -/

theorem sumcheckRoundPoly (count : ℕ) {c : EW} {c' : E} (hc : c.toE = c') {e : Option EW}
    {e' : Option E} (he : e.map EW.toE = e') :
    Sim (Model.sumcheckRoundPoly count c e) (Verifier.sumcheckRoundPoly count c' e')
      fun a b ↦ a.toList.map EW.toE = b := by
  subst hc he
  cases e with
  | none =>
    simp only [Model.sumcheckRoundPoly, Verifier.sumcheckRoundPoly, Option.map_none]
    refine Sim.bind readScalar fun x x' hx ↦ Sim.bind (readScalars _) fun xs xs' hxs ↦
      Sim.bind (grind _) fun _ _ _ ↦ Sim.pure ?_
    simp [← hx, ← hxs.1, toE_sumE]
  | some f =>
    simp only [Model.sumcheckRoundPoly, Verifier.sumcheckRoundPoly, Option.map_some]
    refine Sim.bind (readScalars _) fun xs xs' hxs ↦ Sim.bind (grind _) fun _ _ _ ↦ Sim.pure ?_
    simp [← hxs.1, toE_sumE]

/-- The rounds from an accumulator: the challenges after `pre`, and the claim. -/
theorem sumcheck_loop (count : ℕ) : ∀ (l : List (Option EW)) (l' : List (Option E)),
    l.map (Option.map EW.toE) = l' → ∀ (acc : Array EW × EW) (pre : List E),
      acc.1.toList.map EW.toE = pre →
      Sim (l.foldlM (fun (acc : Array EW × EW) equality ↦ do
          let message ← Model.sumcheckRoundPoly count acc.2 equality
          let challenge ← Model.sampleChallenge
          Pure.pure (acc.1.push challenge, polyEval message challenge)) acc)
        (Verifier.sumcheck acc.2.toE count l')
        fun a b ↦ a.1.toList.map EW.toE = pre ++ b.1 ∧ a.2.toE = b.2
  | [], _, rfl, acc, pre, hacc => Sim.pure ⟨by simp [hacc], rfl⟩
  | e :: l, _, rfl, acc, pre, hacc => by
    simp only [List.foldlM_cons, List.map_cons, Verifier.sumcheck, bind_assoc, pure_bind]
    refine Sim.bind (sumcheckRoundPoly count rfl rfl) fun msg msg' hmsg ↦
      Sim.bind sampleChallenge fun ch ch' hch ↦ ?_
    rw [← bind_pure (List.foldlM _ _ l),
      show Verifier.polyEval msg' ch' = (polyEval msg ch).toE by rw [toE_polyEval, hmsg, hch]]
    refine Sim.bind (sumcheck_loop count l _ rfl (acc.1.push ch, polyEval msg ch) (pre ++ [ch'])
      (by simp [hacc, hch])) fun a b hab ↦ Sim.pure ⟨by simpa using hab.1, hab.2⟩

theorem sumcheck {c : EW} {c' : E} (hc : c.toE = c') (count : ℕ) {eqs : Array (Option EW)}
    {eqs' : List (Option E)} (heqs : eqs.toList.map (Option.map EW.toE) = eqs') :
    Sim (Model.sumcheck c count eqs) (Verifier.sumcheck c' count eqs')
      fun a b ↦ a.1.toList.map EW.toE = b.1 ∧ a.2.toE = b.2 := by
  subst hc
  rw [Model.sumcheck, ← Array.foldlM_toList]
  exact (sumcheck_loop count _ _ heqs (#[], c) [] rfl).mono fun _ _ h ↦ by simpa using h

theorem sumcheckPlain {c : EW} {c' : E} (hc : c.toE = c') (count rounds : ℕ) :
    Sim (Model.sumcheckPlain c count rounds) (Verifier.sumcheck c' count (List.replicate rounds none))
      fun a b ↦ a.1.toList.map EW.toE = b.1 ∧ a.2.toE = b.2 :=
  sumcheck hc count (by simp)

end Sim

/-! ## Commitments and openings: the states -/

theorem _root_.NativeVm.Model.TState.Rel.pushRoot {t : TState} {s : VerifierProgramState}
    (h : t.Rel s) (r : RootW) :
    TState.Rel { t with roots := t.roots.push r } { s with roots := s.roots ++ [r.toRoot] } :=
  ⟨h.sponge, h.cursor_le, h.stream, h.phase_le, h.openings, by simp [← h.roots]⟩

theorem _root_.NativeVm.Model.TState.Rel.roots_getElem? {t : TState} {s : VerifierProgramState}
    (h : t.Rel s) (i : ℕ) : s.roots[i]? = t.roots[i]?.map RootW.toRoot := by
  simp [← h.roots]

theorem _root_.NativeVm.Model.TState.Rel.openings_some {t : TState} {s : VerifierProgramState}
    (h : t.Rel s) {ph : Array OpeningW} (hx : t.openings[t.phase]? = some ph) :
    s.openings = phaseOpenings ph :: (t.openings.toList.drop (t.phase + 1)).map phaseOpenings := by
  obtain ⟨hlt, rfl⟩ := Array.getElem?_eq_some_iff.mp hx
  rw [← h.openings, List.drop_eq_getElem_cons (by simpa using hlt)]
  simp

theorem _root_.NativeVm.Model.TState.Rel.openings_none {t : TState} {s : VerifierProgramState}
    (h : t.Rel s) (hx : t.openings[t.phase]? = none) : s.openings = [] := by
  rw [← h.openings, List.drop_eq_nil_of_le (by simpa using Array.getElem?_eq_none_iff.mp hx)]
  rfl

theorem _root_.NativeVm.Model.TState.Rel.nextPhase {t : TState} {s : VerifierProgramState}
    (h : t.Rel s) {ph : Array OpeningW} (hx : t.openings[t.phase]? = some ph) :
    TState.Rel { t with phase := t.phase + 1 }
      { s with openings := (t.openings.toList.drop (t.phase + 1)).map phaseOpenings } :=
  ⟨h.sponge, h.cursor_le, h.stream, (Array.getElem?_eq_some_iff.mp hx).1, rfl, h.roots⟩

theorem SpongeW.absorb_ground (sp : SpongeW) (x : EW) (tag : UInt64) :
    (sp.absorb x tag).ground = sp.ground := by
  unfold SpongeW.absorb
  split <;> rfl

/-! ## Commitments and openings: the steps -/

section Steps

variable {β : Type}

theorem runSpec_commit_cons (height width : ℕ) (k : VerifierProgram β) {s : VerifierProgramState}
    {x0 x1 : E} {xs : List E} (hs : s.stream = x0 :: x1 :: xs) (hg : s.sponge.ground = none) :
    runSpec (.commit height width k) s =
      runSpec k
        { s with
          sponge := Id.run (absorb (m := Id) keccakF1600
            (Id.run (absorb (m := Id) keccakF1600 s.sponge x0 dsObserve)) x1 dsObserve)
          stream := xs
          roots := s.roots ++ [(digestFromHalves (x0, x1), height, width)] } := by
  obtain ⟨⟨st, p, g⟩, stream, os, rs⟩ := s
  obtain rfl : stream = x0 :: x1 :: xs := hs
  obtain rfl : g = none := hg
  rfl

theorem runSpec_commit_short (height width : ℕ) (k : VerifierProgram β)
    {s : VerifierProgramState} (hs : s.stream.length < 2) :
    runSpec (.commit height width k) s = none := by
  obtain ⟨⟨st, p, g⟩, _ | ⟨x0, _ | ⟨x1, xs⟩⟩, os, rs⟩ := s
  · rfl
  · rcases g <;> rfl
  · simp at hs

theorem runSpec_commit_ground (height width : ℕ) (k : VerifierProgram β)
    {s : VerifierProgramState} {c : E} (hg : s.sponge.ground = some c) :
    runSpec (.commit height width k) s = none := by
  obtain ⟨⟨st, p, g⟩, _ | ⟨x0, _ | ⟨x1, xs⟩⟩, os, rs⟩ := s <;> obtain rfl : g = some c := hg <;> rfl

theorem runSpec_query_cons (i : ℕ) (ps : List ℕ) (k : List (List K) → VerifierProgram β)
    {s : VerifierProgramState} {root : Digest} {height width : ℕ} {phase : List Opening}
    {rest : List (List Opening)} (hr : s.roots[i]? = some (root, height, width))
    (ho : s.openings = phase :: rest) :
    runSpec (.query i ps k) s =
      match Id.run (openPhase (m := Id) keccakF1600 root height width ps phase) with
      | some rows => runSpec (k rows) { s with openings := rest }
      | none => none := by
  obtain ⟨sp, stream, os, rs⟩ := s
  obtain rfl : os = phase :: rest := ho
  simp only at hr
  simp only [runSpec, Compile.run, hr]
  rfl

theorem runSpec_query_root (i : ℕ) (ps : List ℕ) (k : List (List K) → VerifierProgram β)
    {s : VerifierProgramState} (hr : s.roots[i]? = none) : runSpec (.query i ps k) s = none := by
  obtain ⟨sp, stream, os, rs⟩ := s
  simp only at hr
  simp only [runSpec, Compile.run, hr]
  rfl

theorem runSpec_query_nil (i : ℕ) (ps : List ℕ) (k : List (List K) → VerifierProgram β)
    {s : VerifierProgramState} (ho : s.openings = []) : runSpec (.query i ps k) s = none := by
  obtain ⟨sp, stream, os, rs⟩ := s
  obtain rfl : os = [] := ho
  rcases hr : rs[i]? with _ | ⟨root, height, width⟩ <;> simp only [runSpec, Compile.run, hr] <;> rfl

end Steps

theorem readCommitment_run (height width : ℕ) (t : TState) :
    (readCommitment height width).run t = (readScalar.run t).bind fun p ↦
      (readScalar.run p.2).bind fun q ↦
        some ((), { q.2 with roots := q.2.roots.push ⟨#v[p.1.c0, p.1.c1, q.1.c0, q.1.c1], height, width⟩ }) := by
  simp only [Model.readCommitment, StateT.run_bind, StateT.run_modify, Option.bind_eq_bind]
  rfl

theorem queryOpenings_run (i : ℕ) (ps : Array UInt64) (t : TState) :
    (queryOpenings i ps).run t =
      match t.roots[i]?, t.openings[t.phase]? with
      | some r, some ph => (openPhase r.digest r.height r.width ps ph).map fun rows ↦
          (rows, { t with phase := t.phase + 1 })
      | _, _ => none := by
  simp only [Model.queryOpenings, StateT.run_bind, StateT.run_get, pure_bind]
  rcases t.roots[i]? with _ | r <;> rcases t.openings[t.phase]? with _ | ph
  · rfl
  · rfl
  · rfl
  · simp only
    rcases openPhase r.digest r.height r.width ps ph <;> rfl

/-! ## Merkle paths -/

theorem hashWords_eq (ws : Array UInt64) :
    keccak256With (m := Id) keccakF1600 ((ws.toList.map K.ofLane).flatMap K.toBytes) =
      pure (hashWords ws) := by
  simp only [hashWords, keccak256, Native.Keccak.wordsBytes, List.flatMap_map]
  rfl

theorem hashPair_eq (l r : Digest) :
    keccak256With (m := Id) keccakF1600 (digestBytes l ++ digestBytes r) = pure (hashPair l r) := by
  simp only [hashPair, hashWords, keccak256, Native.Keccak.wordsBytes, digestBytes,
    Array.toList_append, List.flatMap_append, Vector.toList]
  rfl

theorem climb_list : ∀ (path : List Digest) (node : Digest) (q : UInt64),
    Compile.climb (m := Id) keccakF1600 node q.toNat path =
      pure (path.foldl (fun (acc : Digest × UInt64) s ↦
        (if acc.2 % 2 = 0 then hashPair acc.1 s else hashPair s acc.1, acc.2 / 2)) (node, q)).1
  | [], _, _ => rfl
  | s :: ss, node, q => by
    have hq : q % 2 = 0 ↔ q.toNat % 2 = 0 := by
      rw [← UInt64.toNat_inj, UInt64.toNat_mod]
      rfl
    have hd : q.toNat / 2 = (q / 2).toNat := (UInt64.toNat_div q 2).symm
    rw [List.foldl_cons, Compile.climb]
    by_cases h : q.toNat % 2 = 0
    · simp only [h, hq.mpr h, ↓reduceIte, hashPair_eq, pure_bind, hd]
      exact climb_list ss _ _
    · simp only [h, mt hq.mp h, ↓reduceIte, hashPair_eq, pure_bind, hd]
      exact climb_list ss _ _

theorem climb_eq (node : Digest) (q : UInt64) (path : Array Digest) :
    Compile.climb (m := Id) keccakF1600 node q.toNat path.toList = pure (Model.climb node q path) := by
  rw [climb_list, Model.climb, Array.foldl_toList]

theorem openOne_eq (root : Digest) {height width : ℕ} (o : OpeningW) (hw : o.leaf.size = width)
    (hh : o.path.size = height) :
    openOne (m := Id) keccakF1600 root height width o.leafIndex.toNat o.toOpening =
      pure (Model.climb (hashWords o.leaf) o.leafIndex o.path == root) := by
  have hs : o.toOpening.leaf.length = width ∧ o.toOpening.path.length = height := by
    simp [OpeningW.toOpening, hw, hh]
  unfold openOne
  split
  · simp only [OpeningW.toOpening, hashWords_eq, pure_bind, climb_eq]
    congr 1
    rw [Bool.eq_iff_iff, decide_eq_true_iff, beq_iff_eq, Vector.toList_inj]
  · contradiction

theorem openAll_eq (root : Digest) (height width : ℕ) : ∀ (L : List OpeningW),
    (∀ o ∈ L, o.leaf.size = width ∧ o.path.size = height) →
    (openAll (m := Id) keccakF1600 root height width (L.map fun o ↦ o.leafIndex.toNat)
      (L.map OpeningW.toOpening) : Id _) =
      if L.all fun o ↦ Model.climb (hashWords o.leaf) o.leafIndex o.path == root then
        some (L.map fun o ↦ o.leaf.toList.map K.ofLane, [])
      else none
  | [], _ => rfl
  | o :: L, hL => by
    have ho := hL o (by simp)
    simp only [List.map_cons, openAll, openOne_eq root o ho.1 ho.2, pure_bind]
    by_cases hc : (Model.climb (hashWords o.leaf) o.leafIndex o.path == root) = true
    · simp only [hc, ↓reduceIte, List.all_cons, Bool.true_and,
        openAll_eq root height width L fun o' h' ↦ hL o' (by simp [h'])]
      split <;> rfl
    · simp only [hc, Bool.false_eq_true, ↓reduceIte, List.all_cons, Bool.false_and]
      rfl

theorem openPhase_eq (root : Digest) (height width : ℕ) (ps : Array UInt64)
    (ph : Array OpeningW) :
    Id.run (Compile.openPhase (m := Id) keccakF1600 root height width (ps.toList.map UInt64.toNat)
      (phaseOpenings ph)) =
      (Model.openPhase root height width ps ph).map fun rows ↦ rows.toList.map (·.toList.map K.ofLane) := by
  have hshape : ((∀ o ∈ phaseOpenings ph, o.leaf.length = width ∧ o.path.length = height) ∧
      (phaseOpenings ph).map Opening.leafIndex = ps.toList.map UInt64.toNat) ↔
      (ph.all (fun o ↦ o.leaf.size == width && o.path.size == height) &&
        ph.map (·.leafIndex) == ps) = true := by
    rw [Bool.and_eq_true, Array.all_eq_true_iff_forall_mem, beq_iff_eq, ← Array.toList_inj,
      Array.toList_map,
      ← (List.map_injective_iff.mpr fun a b h ↦ UInt64.toNat_inj.mp h).eq_iff]
    simp [phaseOpenings, OpeningW.toOpening, Function.comp_def]
  unfold Compile.openPhase Model.openPhase
  by_cases hc : (ph.all (fun o ↦ o.leaf.size == width && o.path.size == height) &&
      ph.map (·.leafIndex) == ps) = true
  · have hcond := hshape.mpr hc
    have hL : ∀ o ∈ ph.toList, o.leaf.size = width ∧ o.path.size = height := by
      intro o ho
      have := hcond.1 o.toOpening (by
        simp only [phaseOpenings, List.mem_map]
        exact ⟨o, ho, rfl⟩)
      simpa [OpeningW.toOpening] using this
    have hidx : ps.toList.map UInt64.toNat = ph.toList.map fun o ↦ o.leafIndex.toNat := by
      rw [← hcond.2]
      simp [phaseOpenings, OpeningW.toOpening]
    simp only [hc, ↓reduceIte]
    split
    · rw [hidx, phaseOpenings, openAll_eq root height width ph.toList hL, Array.all_toList]
      split <;> simp only [Option.map_some, Option.map_none, Array.toList_map, List.map_map,
        Function.comp_def] <;> rfl
    · contradiction
  · simp only [hc, Bool.false_eq_true, ↓reduceIte, Option.map_none]
    split
    · exact absurd (hshape.mp ‹_›) hc
    · rfl

namespace Sim

theorem readCommitment (height width : ℕ) :
    Sim (Model.readCommitment height width) (VerifierProgram.readCommitment height width)
      fun _ _ ↦ True := by
  intro t s h
  rw [readCommitment_run, readScalar_run, nextScalar_run, VerifierProgram.readCommitment]
  have hg := h.sponge.ground
  rcases hw : t.sponge.ground with _ | c
  · rw [hw] at hg
    rcases hx0 : t.stream[t.cursor]? with _ | x0
    · simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Option.map_none,
        Option.bind_none]
      rw [runSpec_commit_short _ _ _ (by simp [h.stream_none hx0])]
      exact .none
    simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Option.map_some,
      Option.bind_some, readScalar_run, nextScalar_run, SpongeW.absorb_ground, hw]
    have h1 := h.advance hx0 (h.sponge.absorb x0 dsObserve.toUInt64)
    rcases hx1 : t.stream[t.cursor + 1]? with _ | x1
    · simp only [Option.map_none, Option.bind_none]
      have h2 := h1.stream_none hx1
      simp only at h2
      rw [runSpec_commit_short _ _ _ (by rw [h.stream_some hx0, h2]; simp)]
      exact .none
    · simp only [Option.map_some, Option.bind_some]
      have hs : s.stream = x0.toE :: x1.toE ::
          (t.stream.toList.drop (t.cursor + 1 + 1)).map EW.toE := by
        rw [h.stream_some hx0]
        exact congrArg _ (h1.stream_some hx1)
      rw [runSpec_commit_cons _ _ _ hs hg.symm, runSpec_ret]
      have h2 := (h1.advance hx1 (h1.sponge.absorb x1 dsObserve.toUInt64)).pushRoot
        ⟨#v[x0.c0, x0.c1, x1.c0, x1.c1], height, width⟩
      have hd : digestFromHalves (x0.toE, x1.toE) = #v[x0.c0, x0.c1, x1.c0, x1.c1] := by
        simp [digestFromHalves]
      refine .some ⟨trivial, ?_⟩
      rw [hd]
      exact h2
  · rw [hw] at hg
    simp only [Option.isSome_some, ↓reduceIte, Option.map_none, Option.bind_none]
    rw [runSpec_commit_ground _ _ _ hg.symm]
    exact .none

theorem queryOpenings (i : ℕ) {ps : Array UInt64} {ps' : List ℕ}
    (hps : ps.toList.map UInt64.toNat = ps') :
    Sim (Model.queryOpenings i ps) (VerifierProgram.queryOpenings i ps')
      fun a b ↦ a.toList.map (·.toList.map K.ofLane) = b := by
  subst hps
  intro t s h
  rw [queryOpenings_run, VerifierProgram.queryOpenings]
  rcases hr : t.roots[i]? with _ | r
  · rw [runSpec_query_root _ _ _ (by rw [h.roots_getElem?, hr]; rfl)]
    exact .none
  rcases hx : t.openings[t.phase]? with _ | ph
  · rw [runSpec_query_nil _ _ _ (h.openings_none hx)]
    exact .none
  simp only
  rw [runSpec_query_cons _ _ _ (by rw [h.roots_getElem?, hr]; rfl) (h.openings_some hx),
    openPhase_eq]
  rcases Model.openPhase r.digest r.height r.width ps ph with _ | rows
  · exact .none
  · exact .some ⟨rfl, h.nextPhase hx⟩

end Sim

end NativeVm.Equiv
