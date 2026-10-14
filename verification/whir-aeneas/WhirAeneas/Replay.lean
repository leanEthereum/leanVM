import WhirAeneas.Query

namespace WhirAeneas.Replay
open Aeneas Aeneas.Std ReplaySource Whir Whir.Concrete WhirAeneas.Fold WhirAeneas.Query

theorem range_next_some (r : core.ops.range.Range Usize) (h : r.start.val < r.end.val) :
    ∃ r', core.iter.range.IteratorRange.next core.iter.range.StepUsize r = .ok (some r.start, r') ∧
      r'.start.val = r.start.val + 1 ∧ r'.end = r.end := by
  have hl : core.cmp.impls.PartialOrdUsize.lt r.start r.end = true := by
    simp [core.cmp.impls.PartialOrdUsize.lt, h]
  have hm : r.start.val < UScalar.max .Usize := by scalar_tac
  simp only [core.iter.range.IteratorRange.next, core.iter.range.UScalarStep,
    core.iter.range.UScalarStep.forward_checked, bind_tc_ok]
  simp only [hl, ↓reduceIte]
  simp [hm, UScalar.ofNatCore_val_eq]

theorem range_next_none (r : core.ops.range.Range Usize) (h : r.end.val ≤ r.start.val) :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize r = .ok (none, r) := by
  have hl : core.cmp.impls.PartialOrdUsize.lt r.start r.end = false := by
    simp [core.cmp.impls.PartialOrdUsize.lt]; omega
  simp only [core.iter.range.IteratorRange.next, core.iter.range.UScalarStep]
  simp [hl]

theorem list_clone_id {α : Type} (c : α → Result α) (hc : ∀ x, c x = .ok x) (l : List α) :
    List.clone c l = .ok ⟨l, rfl⟩ := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.clone, List.mapM_with_length] at ih ⊢
    simp only [ih, hc, bind_tc_ok]
    rfl

theorem extend_ok {α : Type} (c : core.clone.Clone α) (hc : ∀ x, c.clone x = .ok x)
    (v : alloc.vec.Vec α) (s : Slice α) (h : v.val.length + s.val.length ≤ Usize.max) :
    ∃ w, alloc.vec.Vec.extend_from_slice c v s = .ok w ∧ w.val = v.val ++ s.val := by
  have h' : v.length + s.length ≤ Usize.max := by simpa using h
  simp only [alloc.vec.Vec.extend_from_slice, h', ↓reduceDIte, list_clone_id c.clone hc, bind_tc_ok]
  exact ⟨_, rfl, alloc.vec.Vec.from_val _ _⟩

theorem to_vec_ok {α : Type} (c : core.clone.Clone α) (hc : ∀ x, c.clone x = .ok x) (s : Slice α) :
    ∃ w, alloc.slice.Slice.to_vec c s = .ok w ∧ w.val = s.val := by
  simp only [alloc.slice.Slice.to_vec, Slice.clone, list_clone_id c.clone hc, bind_tc_ok]
  exact ⟨_, rfl, by simp [alloc.vec.Vec.val]⟩

theorem clone_vec_ok {α : Type} (c : core.clone.Clone α) (hc : ∀ x, c.clone x = .ok x)
    (v : alloc.vec.Vec α) : ∃ w, alloc.vec.CloneVec.clone c v = .ok w ∧ w.val = v.val := by
  simp only [alloc.vec.CloneVec.clone, Slice.clone, list_clone_id c.clone hc, bind_tc_ok]
  exact ⟨_, rfl, by simp⟩

theorem vec_index_usize {α : Type} (v : alloc.vec.Vec α) (i : Usize) (hi : i.val < v.val.length) :
    v.index_usize i = .ok v.val[i.val] := by
  simp [alloc.vec.Vec.index_usize, hi]

theorem slice_range {α : Type} (s : Slice α) (a b : Usize) (hab : a.val ≤ b.val)
    (hb : b.val ≤ s.val.length) :
    ∃ t, core.slice.index.SliceIndexRangeUsizeSlice.index { start := a, «end» := b } s = .ok t ∧
      t.val = (s.val.drop a.val).take (b.val - a.val) := by
  have h : a ≤ b ∧ b ≤ s.length := ⟨by scalar_tac, by simpa using hb⟩
  simp only [core.slice.index.SliceIndexRangeUsizeSlice.index, h, and_self, ↓reduceIte]
  exact ⟨_, rfl, by simp [List.slice]⟩

/-! ## The transcript interface

`tape v evs` says the opening verifier in state `v` answers the events `evs` next, as source
values, in the replay's read order. It is a relation rather than a function of the state: a
read that changes nothing observable (a proof of work of zero bits, an empty batch) leaves the
state as it was while consuming its event. It is stated against the spongefish transcript of
PR 607: a verifier message (`sample`, `sampleVec`, the batch challenge, the query positions) is
drawn from the BLAKE2s duplex and takes no proof bytes; a prover message is read off the NARG
string and absorbed (`scalar`, `scalars`: 24 bytes per element, three little-endian limbs
lowest first; `root`: the raw 32-byte digest); a round polynomial is two prover messages, its
constant and quadratic coefficients, from which the default `Verifier::read_round` fixes the
linear one; `grind bits` is the proof-of-work check of `bits` bits (a 32-byte challenge drawn,
then an 8-byte little-endian nonce read and absorbed; zero bits is no step); `queries depth qs`
are positions of `depth` bits; `rows` is one length-prefixed hint, not absorbed, authenticated
by the opening verifier against the root, depth, query positions and row and leaf widths the
replay passes, which the event records. The interface assumes nothing about how the duplex
derives the draws or how the hint is authenticated; those are separate contracts of the
concrete verifier. -/

inductive Event (E Q R K : Type) where
  | sample (e : E)
  | sampleVec (zs : List E)
  | scalar (y : E)
  | scalars (ys : List E)
  | poly (u0 u2 : E)
  | root (r : R)
  | grind (bits : Nat)
  | queries (depth : Nat) (qs : List Q)
  | rows (root : R) (depth : Nat) (qs : List Q) (rowWords leafWords : Nat) (ws : List (List K))

/-- Every read but the Merkle rows: each answers the tape's next event and leaves the rest; a
round polynomial is read as its two transmitted coefficients by the trait's default
`Verifier::read_round`; scopes change nothing. -/
structure Reads {V R K Q E : Type} (inst : verifier.OpeningVerifier V R K Q E)
    (encode : E → Concrete.E) (tape : V → List (Event E Q R K) → Prop) : Prop where
  sample : ∀ v e rest, tape v (.sample e :: rest) →
    ∃ v', inst.fiat_shamirarithVerifierInst.verifier_message v = .ok (e, v') ∧ tape v' rest
  sample_vec : ∀ v (n : Usize) zs rest, tape v (.sampleVec zs :: rest) → zs.length = n.val →
    ∃ w v', inst.fiat_shamirarithVerifierInst.verifier_messages v n = .ok (w, v') ∧ w.val = zs ∧
      tape v' rest
  scalar : ∀ v y rest, tape v (.scalar y :: rest) →
    ∃ v', inst.fiat_shamirarithVerifierInst.prover_message v = .ok (.Ok y, v') ∧ tape v' rest
  scalars : ∀ v (n : Usize) ys rest, tape v (.scalars ys :: rest) → ys.length = n.val →
    ∃ w v', inst.fiat_shamirarithVerifierInst.prover_messages v n = .ok (.Ok w, v') ∧ w.val = ys ∧
      tape v' rest
  poly : ∀ v (n : Usize) u0 u2 rest, tape v (.poly u0 u2 :: rest) → n.val = 2 →
    ∃ w v', inst.fiat_shamirarithVerifierInst.prover_messages v n = .ok (.Ok w, v') ∧ w.val = [u0, u2] ∧
      tape v' rest
  read_round : inst.fiat_shamirarithVerifierInst.read_round =
    fiat_shamir.arith.Verifier.read_round.default inst.fiat_shamirarithVerifierInst
  root : ∀ v r rest, tape v (.root r :: rest) →
    ∃ v', inst.next_root v = .ok (.Ok r, v') ∧ tape v' rest
  grind : ∀ v (bits : U32) rest, tape v (.grind bits.val :: rest) →
    ∃ v', inst.fiat_shamirarithVerifierInst.check_pow v bits = .ok (.Ok (), v') ∧ tape v' rest
  queries : ∀ v (depth count : Usize) qs rest, tape v (.queries depth.val qs :: rest) → qs.length = count.val →
    ∃ w v', inst.sample_queries v depth count = .ok (w, v') ∧ w.val = qs ∧ tape v' rest
  begin_scope : ∀ v stage, inst.fiat_shamirarithVerifierInst.begin_scope v stage = .ok v
  end_scope : ∀ v, inst.fiat_shamirarithVerifierInst.end_scope v = .ok v

/-- The reads, and the rows read answering the arguments its event records. -/
structure Transcript {V R K Q E : Type} (inst : verifier.OpeningVerifier V R K Q E)
    (encode : E → Concrete.E) (tape : V → List (Event E Q R K) → Prop) : Prop extends Reads inst encode tape where
  rows : ∀ v root (depth : Usize) (queries : Slice Q) (a b : Usize) ws rest,
    tape v (.rows root depth.val queries.val a.val b.val ws :: rest) →
    ∃ w v', inst.open_rows v root depth queries a b = .ok (.Ok w, v') ∧
      w.val.map (·.val) = ws ∧ tape v' rest

section Steps
open AccumulatedTerminalRefinement WHIRNativeArithmetic
variable {V R K Q E : Type} (inst : verifier.OpeningVerifier V R K Q E)
  (encode : E → Concrete.E) (const : primitives.field.gf2_64x3.F192 → Concrete.E) (index : Q → Nat)
  (tape : V → List (Event E Q R K) → Prop)

/-- The generated default `Verifier::read_round` of a quadratic with the linear coefficient
fixed: the two transmitted coefficients with `claim + u2` inserted between them. -/
theorem read_eq (h : ArithModel inst.fiat_shamirarithVerifierInst.ArithInst encode const)
    (v v1 : V) (claim u0 u2 : E) (w : alloc.vec.Vec E) (hw : w.val = [u0, u2])
    (hpm : inst.fiat_shamirarithVerifierInst.prover_messages v (Std.Usize.wrapping_sub 3#usize 1#usize) =
      .ok (.Ok w, v1)) :
    ∃ coeffs b, fiat_shamir.arith.Verifier.read_round.default inst.fiat_shamirarithVerifierInst v 3#usize
        claim none = .ok (.Ok coeffs, v1) ∧ coeffs.val = [u0, b, u2] ∧
      encode b = encode claim + encode u2 := by
  obtain ⟨z, hz, ez⟩ := h.zero v1
  obtain ⟨t, ht, et⟩ := h.add v1 z u2
  obtain ⟨t2, ht2, et2⟩ := h.add v1 claim t
  have hm : 4 ≤ Usize.max := by clear * -; scalar_tac
  obtain ⟨w3, hins, ew3⟩ : ∃ w3, alloc.vec.Vec.insert w 1#usize claim = .ok w3 ∧ w3.val = [u0, claim, u2] := by
    simp [alloc.vec.Vec.insert, hw, show 2 < Usize.max by omega]
  have h11 : Std.Usize.wrapping_add 1#usize 1#usize = 2#usize :=
    UScalar.eq_of_val_eq (by rw [succ_val 1#usize 2 (by simp) (by omega)]; simp)
  have h21 : (Std.Usize.wrapping_add 2#usize 1#usize).val = 3 := by
    rw [succ_val 2#usize 3 (by simp) (by omega)]; simp
  have hloop : fiat_shamir.arith.Verifier.read_round.default_loop inst.fiat_shamirarithVerifierInst v1
      w3 z 2#usize = .ok (v1, t) := by
    unfold fiat_shamir.arith.Verifier.read_round.default_loop
    have hb1 : fiat_shamir.arith.Verifier.read_round.default_loop.body inst.fiat_shamirarithVerifierInst
        w3 v1 z 2#usize = .ok (.cont (v1, t, Std.Usize.wrapping_add 2#usize 1#usize)) := by
      have h2 : (2#usize : Usize) < alloc.vec.Vec.len w3 := by simp [UScalar.lt_equiv, ew3]
      simp only [fiat_shamir.arith.Verifier.read_round.default_loop.body, h2, ↓reduceIte,
        alloc.vec.Vec.index_slice_index, vec_index_usize w3 2#usize (by simp [ew3]), Std.bind_ok, lift]
      simp [ew3, ht]
    rw [loop_cont hb1]
    apply loop_done
    have h3 : ¬ (Std.Usize.wrapping_add 2#usize 1#usize < alloc.vec.Vec.len w3) := by
      simp [UScalar.lt_equiv, ew3, h21]
    simp [fiat_shamir.arith.Verifier.read_round.default_loop.body, h3]
  refine ⟨alloc.vec.Vec.set w3 1#usize t2, t2, ?_, by simp [ew3], ?_⟩
  · simp [fiat_shamir.arith.Verifier.read_round.default, massert, hpm,
      core.result.Result.Insts.CoreOpsTry.branch, core.option.Option.map_or,
      fiat_shamir.arith.RoundWeight.fixed_index, hins, hz, lift, h11, hloop, ht2,
      alloc.vec.Vec.index_mut_usize, vec_index_usize w3 1#usize (by simp [ew3])]
  · rw [et2, et, ez, zero_add]

/-- `RoundQuad::read` reads the next round polynomial: the transmitted `u0` and `u2`, with the
linear coefficient `claim + u2`. -/
theorem recv_eq (h : ArithModel inst.fiat_shamirarithVerifierInst.ArithInst encode const)
    (ht : Transcript inst encode tape) (copy : core.marker.Copy E) (v : V)
    (claim u0 u2 : E) (rest : List (Event E Q R K)) (hv : tape v (.poly u0 u2 :: rest)) :
    ∃ q v', whir.sumcheck.RoundQuad.read copy inst.fiat_shamirarithVerifierInst v claim = .ok (.Ok q, v') ∧
      q.c = u0 ∧ q.a = u2 ∧ encode q.b = encode claim + encode u2 ∧ tape v' rest := by
  obtain ⟨w, v', hpm, hw, hrest⟩ := ht.poly v (Std.Usize.wrapping_sub 3#usize 1#usize) u0 u2 rest hv
    (by rw [Fold.sub_val _ _ (by simp)]; simp)
  obtain ⟨coeffs, b, hread, hc, hb⟩ := read_eq inst encode const h v v' claim u0 u2 w hw hpm
  refine ⟨{ c := u0, b := b, a := u2 }, v', ?_, rfl, rfl, hb, hrest⟩
  simp [whir.sumcheck.RoundQuad.read, ht.read_round, hread, core.result.Result.Insts.CoreOpsTry.branch,
    alloc.vec.Vec.index_usize, hc]

/-- The tape of fold rounds: each samples its challenge, then reads its polynomial. -/
def foldTape (rounds : List (E × E × E)) : List (Event E Q R K) :=
  rounds.flatMap fun (r, u0, u2) => [.sample r, .poly u0 u2]

/-- The model's fold rounds over the interpreted challenges and messages. -/
def foldModel (rounds : List (E × E × E)) (st : State) : State :=
  rounds.foldl (fun s (r, u0, u2) => foldScalar s (encode r) ⟨encode u0, encode u2⟩) st

theorem fold_loop_eq (h : ArithModel inst.fiat_shamirarithVerifierInst.ArithInst encode const)
    (ht : Transcript inst encode tape) :
    ∀ (rounds : List (E × E × E)) (iter : core.ops.range.Range Std.Usize)
      (self : whir.verify.WhirReplay V R K Q E) (v : V) (rs : alloc.vec.Vec E) (st : State)
      (rest : List (Event E Q R K)),
      iter.start.val + rounds.length = iter.end.val →
      tape v (foldTape rounds ++ rest) →
      encode self.t_r = st.claim →
      (⟨encode self.quad.c, encode self.quad.a⟩ : Protocol.Message Concrete.E) = st.message →
      encode self.quad.b = st.claim + encode self.quad.a →
      self.ris.val.map encode = st.source.ris →
      self.ris.val.length + rounds.length ≤ Usize.max →
      rs.val.length + rounds.length ≤ Usize.max →
      ∃ rs' self' v',
        whir.verify.WhirReplay.fold_rounds_loop inst iter self v rs = .ok (.Ok rs', self', v') ∧
        tape v' rest ∧ rs'.val = rs.val ++ rounds.map (·.1) ∧
        self'.ris.val = self.ris.val ++ rounds.map (·.1) ∧
        self'.levels = self.levels ∧ self'.oods = self.oods ∧
        encode self'.t_r = (foldModel encode rounds st).claim ∧
        (⟨encode self'.quad.c, encode self'.quad.a⟩ : Protocol.Message Concrete.E) =
          (foldModel encode rounds st).message ∧
        encode self'.quad.b = (foldModel encode rounds st).claim + encode self'.quad.a ∧
        self'.ris.val.map encode = (foldModel encode rounds st).source.ris ∧
        (foldModel encode rounds st).source.saved = st.source.saved ∧
        (foldModel encode rounds st).n = st.n - rounds.length := by
  intro rounds
  induction rounds with
  | nil =>
    intro iter self v rs st rest hlen hv hc hm hb hris _ _
    refine ⟨rs, self, v, ?_, by simpa [foldTape] using hv, by simp, by simp, rfl, rfl, hc, hm, hb,
      by simpa [foldModel] using hris, rfl, by simp [foldModel]⟩
    unfold whir.verify.WhirReplay.fold_rounds_loop
    apply loop_done
    simp [whir.verify.WhirReplay.fold_rounds_loop.body, range_next_none iter (by simp at hlen; omega)]
  | cons rd rounds ih =>
    intro iter self v rs st rest hlen hv hc hm hb hris hcap hcaprs
    obtain ⟨r, u0, u2⟩ := rd
    obtain ⟨iter1, hnext, hs1, he1⟩ := range_next_some iter (by simp at hlen; omega)
    obtain ⟨v1, hsample, hv1⟩ := ht.sample v r (.poly u0 u2 :: (foldTape rounds ++ rest))
      (by simpa [foldTape] using hv)
    obtain ⟨t, het, et⟩ := quad_eval inst.fiat_shamirarithVerifierInst.ArithInst.coremarkerCopyInst inst
      encode const h self.quad v1 r st.claim hb
    obtain ⟨ris1, hpris, eris1⟩ := push_ok self.ris r (by simp at hcap; omega)
    obtain ⟨q, v3, hrecv, hqc, hqa, hqb, hv3⟩ := recv_eq inst encode const tape h ht
      inst.fiat_shamirarithVerifierInst.ArithInst.coremarkerCopyInst v1 t u0 u2
      (foldTape rounds ++ rest) hv1
    obtain ⟨rs1, hpush, ers1⟩ := push_ok rs r (by simp at hcaprs; omega)
    have hfc : whir.verify.WhirReplay.fold_challenge inst self v =
        .ok (r, { self with t_r := t, ris := ris1 }, v1) := by
      simp [whir.verify.WhirReplay.fold_challenge, hsample, het, hpris]
    have hbody : whir.verify.WhirReplay.fold_rounds_loop.body inst iter self v rs =
        .ok (.cont (iter1, { self with t_r := t, ris := ris1, quad := q }, v3, rs1)) := by
      simp [whir.verify.WhirReplay.fold_rounds_loop.body, hnext, hfc, hrecv,
        core.result.Result.Insts.CoreOpsTry.branch, hpush]
    let st1 := foldScalar st (encode r) ⟨encode u0, encode u2⟩
    obtain ⟨rs', self', v', hloop, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩ :=
      ih iter1 { self with t_r := t, ris := ris1, quad := q } v3 rs1 st1 rest
        (by simp at hlen; rw [hs1, he1]; omega) hv3
        (by rw [et, hm]; rfl)
        (by simp only [st1, foldScalar, hqc, hqa])
        (by rw [hqb, hqa, et, hm]; rfl)
        (by simp only [eris1, st1, foldScalar, SourceState.step, ← hris]; simp)
        (by simp only [eris1]; simp at hcap ⊢; omega)
        (by simp only [ers1]; simp at hcaprs ⊢; omega)
    refine ⟨rs', self', v', ?_, e1, by rw [e2, ers1]; simp, by rw [e3, eris1]; simp, e4, e5, e6, e7,
      e8, e9, e10, ?_⟩
    · unfold whir.verify.WhirReplay.fold_rounds_loop
      rw [loop_cont hbody]
      unfold whir.verify.WhirReplay.fold_rounds_loop at hloop
      exact hloop
    · change (foldModel encode rounds st1).n = _
      rw [e11]; simp only [st1, foldScalar, List.length_cons]; omega

/-- `fold_rounds` reads `k` rounds, folds the running claim and quadratic exactly as the
model's `foldScalar`, and appends the challenges to the transcript's fold point. -/
theorem fold_rounds_eq (h : ArithModel inst.fiat_shamirarithVerifierInst.ArithInst encode const)
    (ht : Transcript inst encode tape)
    (self : whir.verify.WhirReplay V R K Q E) (st : State) (hrel : StateRel encode index self st)
    (v : V) (k : Usize) (rounds : List (E × E × E)) (rest : List (Event E Q R K))
    (hk : rounds.length = k.val) (hv : tape v (foldTape rounds ++ rest))
    (hcap : self.ris.val.length + rounds.length ≤ Usize.max) :
    ∃ rs self' v', whir.verify.WhirReplay.fold_rounds inst self v k = .ok (.Ok rs, self', v') ∧
      tape v' rest ∧ rs.val = rounds.map (·.1) ∧ self'.ris.val = self.ris.val ++ rs.val ∧
      self'.levels = self.levels ∧ self'.oods = self.oods ∧
      StateRel encode index self' (foldModel encode rounds st) ∧
      (foldModel encode rounds st).n = st.n - k.val := by
  obtain ⟨rs', self', v', hloop, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩ :=
    fold_loop_eq inst encode const tape h ht rounds { start := 0#usize, «end» := k } self v
      (alloc.vec.Vec.with_capacity E k) st rest (by simp [hk]) hv hrel.claim hrel.message hrel.linear
      hrel.ris hcap (by simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new]; omega)
  have hrs : rs'.val = rounds.map (·.1) := by
    simpa [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new] using e2
  refine ⟨rs', self', v', ?_, e1, hrs, by rw [e3, hrs], e4, e5,
    ⟨e6, e7, e8, e9, by simpa [e4, e5, e10] using hrel.oods, by simpa [e4, e5, e10] using hrel.levels⟩,
    by rw [e11, hk]⟩
  simp [whir.verify.WhirReplay.fold_rounds, hloop]

/-- The tape of a level's out-of-domain claims: each point, its value, its intro round. -/
def oodTape (oods : List (List E × E × E × E)) : List (Event E Q R K) :=
  oods.flatMap fun (z, y, u0, u2) => [.sampleVec z, .scalar y, .poly u0 u2]

/-- A replayed out-of-domain claim is the tape's, with the intro's linear coefficient
fixed by the claimed value. -/
def OodIs (o : whir.verify.Ood E) (d : List E × E × E × E) : Prop :=
  o.z.val = d.1 ∧ o.y = d.2.1 ∧ o.intro.c = d.2.2.1 ∧ o.intro.a = d.2.2.2 ∧
    encode o.intro.b = encode d.2.1 + encode d.2.2.2

theorem ood_replay_eq (h : ArithModel inst.fiat_shamirarithVerifierInst.ArithInst encode const)
    (ht : Transcript inst encode tape) (copy : core.marker.Copy E) (v : V)
    (n : Usize) (z : List E) (y u0 u2 : E) (rest : List (Event E Q R K)) (hz : z.length = n.val)
    (hv : tape v (.sampleVec z :: .scalar y :: .poly u0 u2 :: rest)) :
    ∃ o v', whir.verify.Ood.replay copy inst v n = .ok (.Ok o, v') ∧ OodIs encode o (z, y, u0, u2) ∧
      tape v' rest := by
  obtain ⟨w, v1, h1, ew, hv1⟩ := ht.sample_vec v n z _ hv hz
  obtain ⟨v2, h2, hv2⟩ := ht.scalar v1 y _ hv1
  obtain ⟨q, v3, h3, hqc, hqa, hqb, hv3⟩ := recv_eq inst encode const tape h ht copy v2 y u0 u2 rest hv2
  refine ⟨{ z := w, y := y, intro := q }, v3, ?_, ⟨ew, rfl, hqc, hqa, by rw [hqb, ← hqa]⟩, hv3⟩
  simp [whir.verify.Ood.replay, h1, h2, h3, core.result.Result.Insts.CoreOpsTry.branch]

theorem replay_all_loop_eq (h : ArithModel inst.fiat_shamirarithVerifierInst.ArithInst encode const)
    (ht : Transcript inst encode tape) (copy : core.marker.Copy E)
    (count n : Usize) :
    ∀ (l : List (List E × E × E × E)) (i : Usize) (oods : alloc.vec.Vec (whir.verify.Ood E)) (v : V)
      (rest : List (Event E Q R K)),
      i.val + l.length = count.val → (∀ d ∈ l, d.1.length = n.val) → tape v (oodTape l ++ rest) →
      oods.val.length + l.length ≤ Usize.max →
      ∃ w v', whir.verify.Ood.replay_all_loop copy inst v count n oods i = .ok (.Ok w, v') ∧
        tape v' rest ∧ ∃ ws, w.val = oods.val ++ ws ∧ List.Forall₂ (OodIs encode) ws l := by
  intro l
  induction l with
  | nil =>
    intro i oods v rest hi _ hv _
    refine ⟨oods, v, ?_, by simpa [oodTape] using hv, [], by simp, List.Forall₂.nil⟩
    unfold whir.verify.Ood.replay_all_loop
    apply loop_done
    have : ¬ (i < count) := by simp at hi; scalar_tac
    simp [whir.verify.Ood.replay_all_loop.body, this]
  | cons d l ih =>
    intro i oods v rest hi hz hv hcap
    obtain ⟨z, y, u0, u2⟩ := d
    obtain ⟨o, v1, h1, eo, hv1⟩ := ood_replay_eq inst encode const tape h ht copy v n z y u0 u2
      (oodTape l ++ rest) (hz (z, y, u0, u2) (by simp)) (by simpa [oodTape] using hv)
    obtain ⟨oods1, hpush, eoods1⟩ := push_ok oods o (by simp at hcap; omega)
    have hlt : i.val < count.val := by simp at hi; omega
    have hsucc := succ_val i count.val hlt (by scalar_tac)
    have hbody : whir.verify.Ood.replay_all_loop.body copy inst count n v oods i =
        .ok (.cont (v1, oods1, Std.Usize.wrapping_add i 1#usize)) := by
      have : i < count := by scalar_tac
      simp [whir.verify.Ood.replay_all_loop.body, this, h1, hpush,
        core.result.Result.Insts.CoreOpsTry.branch, lift]
    obtain ⟨w, v', hloop, hv', ws, ew, hws⟩ := ih (Std.Usize.wrapping_add i 1#usize) oods1 v1 rest
      (by rw [hsucc]; simp at hi; omega) (fun d hd => hz d (by simp [hd])) hv1
      (by rw [eoods1]; simp at hcap ⊢; omega)
    refine ⟨w, v', ?_, hv', o :: ws, by rw [ew, eoods1]; simp, List.Forall₂.cons eo hws⟩
    unfold whir.verify.Ood.replay_all_loop
    rw [loop_cont hbody]
    unfold whir.verify.Ood.replay_all_loop at hloop
    exact hloop

theorem replay_all_eq (h : ArithModel inst.fiat_shamirarithVerifierInst.ArithInst encode const)
    (ht : Transcript inst encode tape) (copy : core.marker.Copy E)
    (v : V) (count n : Usize) (l : List (List E × E × E × E)) (rest : List (Event E Q R K))
    (hl : l.length = count.val) (hz : ∀ d ∈ l, d.1.length = n.val) (hv : tape v (oodTape l ++ rest)) :
    ∃ w v', whir.verify.Ood.replay_all copy inst v count n = .ok (.Ok w, v') ∧ tape v' rest ∧
      List.Forall₂ (OodIs encode) w.val l := by
  obtain ⟨w, v', hloop, hv', ws, ew, hws⟩ := replay_all_loop_eq inst encode const tape h ht copy count n l
    0#usize (alloc.vec.Vec.new _) v rest (by simp [hl]) hz hv (by simp [alloc.vec.Vec.new]; scalar_tac)
  refine ⟨w, v', hloop, hv', ?_⟩
  simpa [ew, alloc.vec.Vec.new] using hws

/-- `begin_query` checks grinding, reads the batch's queries, draws its challenge and
takes the challenge's powers as the query weights. -/
theorem begin_query_eq (h : ArithModel inst.fiat_shamirarithVerifierInst.ArithInst encode const)
    (ht : Transcript inst encode tape) (v : V) (phase : whir.verify.QueryPhase) (qs : List Q) (lam : E)
    (rest : List (Event E Q R K)) (hq : qs.length = phase.count.val)
    (hv : tape v (.grind phase.grinding.val :: .queries phase.depth.val qs :: .sample lam :: rest)) :
    ∃ b v', whir.verify.WhirReplay.begin_query inst v phase = .ok (.Ok b, v') ∧ tape v' rest ∧
      b.queries.val = qs ∧ b.lambda = lam ∧
      b.weights.val.map encode = (Concrete.powers (encode lam) qs.length).toList := by
  obtain ⟨v1, h1, hv1⟩ := ht.grind v phase.grinding _ hv
  obtain ⟨w, v2, h2, ew, hv2⟩ := ht.queries v1 phase.depth phase.count qs _ hv1 hq
  obtain ⟨v3, h3, hv3⟩ := ht.sample v2 lam _ hv2
  obtain ⟨ws, h4, ews⟩ := h.powers v3 lam phase.count
  refine ⟨{ queries := w, weights := ws, lambda := lam }, v3, ?_, hv3, ew, rfl, by rw [ews, hq]⟩
  simp [whir.verify.WhirReplay.begin_query, h1, h2, h3, h4, whir.verify.QueryPhase.sample,
    core.result.Result.Insts.CoreOpsTry.branch, ht.begin_scope]

end Steps

/-! ## Opened rows of elements -/

section Rows
variable {V R K Q E : Type} (inst : verifier.OpeningVerifier V R K Q E)
  (encode : E → Concrete.E) (encodeK : K → Concrete.K)
  (ofLimbs : Concrete.K → Concrete.K → Concrete.K → Concrete.E) (index : Q → Nat)
  (tape : V → List (Event E Q R K) → Prop)

/-- A row of words read as elements, three limbs each, lowest first. -/
def eRow (ws : List K) : List Concrete.E :=
  (List.range (ws.length / 3)).map fun i =>
    ofLimbs (ws.map encodeK)[3 * i]! (ws.map encodeK)[3 * i + 1]! (ws.map encodeK)[3 * i + 2]!

theorem e_row_loop_eq (hr : RowModel inst encode encodeK ofLimbs index) (words : Slice K) (n : Usize)
    (hn : 3 * n.val ≤ words.val.length) :
    ∀ (m : Nat) (i : Usize) (row : alloc.vec.Vec E) (v : V), n.val - i.val = m → i.val ≤ n.val →
      row.val.map encode = (List.range i.val).map (fun j =>
        ofLimbs (words.val.map encodeK)[3 * j]! (words.val.map encodeK)[3 * j + 1]!
          (words.val.map encodeK)[3 * j + 2]!) →
      ∃ row', whir.verify.e_row_loop inst v words n row i = .ok (row', v) ∧
        row'.val.map encode = (List.range n.val).map (fun j =>
          ofLimbs (words.val.map encodeK)[3 * j]! (words.val.map encodeK)[3 * j + 1]!
            (words.val.map encodeK)[3 * j + 2]!) := by
  intro m
  induction m with
  | zero =>
    intro i row v hm hi hrow
    refine ⟨row, ?_, by rw [show n.val = i.val by omega]; exact hrow⟩
    unfold whir.verify.e_row_loop
    apply loop_done
    have : ¬ (i < n) := by scalar_tac
    simp [whir.verify.e_row_loop.body, this]
  | succ m ih =>
    intro i row v hm hi hrow
    have hin : i.val < n.val := by omega
    have hat : (Std.Usize.wrapping_mul 3#usize i).val = 3 * i.val := by
      rw [Std.Usize.wrapping_mul_val_eq]
      apply Nat.mod_eq_of_lt
      have := words.property
      have := Usize.max_def
      simp only [UScalar.size] at *
      scalar_tac
    have h1 : (Std.Usize.wrapping_add (Std.Usize.wrapping_mul 3#usize i) 1#usize).val = 3 * i.val + 1 := by
      rw [succ_val _ words.val.length (by rw [hat]; omega) (by have := words.property; scalar_tac), hat]
    have h2 : (Std.Usize.wrapping_add (Std.Usize.wrapping_mul 3#usize i) 2#usize).val = 3 * i.val + 2 := by
      rw [Std.Usize.wrapping_add_val_eq, hat]
      apply Nat.mod_eq_of_lt
      have := words.property
      have := Usize.max_def
      simp only [UScalar.size] at *
      scalar_tac
    have i0 : 3 * i.val < words.val.length := by omega
    have i1 : 3 * i.val + 1 < words.val.length := by omega
    have i2 : 3 * i.val + 2 < words.val.length := by omega
    obtain ⟨y, hy, ey⟩ := hr.e_of_limbs v (Array.make 3#usize [words.val[3 * i.val],
      words.val[3 * i.val + 1], words.val[3 * i.val + 2]]) _ _ _ rfl
    obtain ⟨row1, hpush, erow1⟩ := push_ok row y (by
      have : row.val.length = i.val := by simpa using congrArg List.length hrow
      have := words.property
      scalar_tac)
    have hbody : whir.verify.e_row_loop.body inst words n v row i =
        .ok (.cont (v, row1, Std.Usize.wrapping_add i 1#usize)) := by
      have hlt : i < n := by scalar_tac
      simp only [whir.verify.e_row_loop.body, hlt, ↓reduceIte, lift, Std.bind_ok,
        slice_index words _ (by rw [hat]; omega), slice_index words _ (by rw [h1]; omega),
        slice_index words _ (by rw [h2]; omega)]
      simp only [hat, h1, h2]
      simp [hy, hpush]
    have hsucc := succ_val i n.val hin (by scalar_tac)
    obtain ⟨row', hloop, erow'⟩ := ih (Std.Usize.wrapping_add i 1#usize) row1 v (by omega) (by omega) (by
      rw [erow1, hsucc, List.range_succ]
      simp [hrow, ey, List.getElem?_eq_getElem i0, List.getElem?_eq_getElem i1,
        List.getElem?_eq_getElem i2])
    refine ⟨row', ?_, erow'⟩
    unfold whir.verify.e_row_loop
    rw [loop_cont hbody]
    unfold whir.verify.e_row_loop at hloop
    exact hloop

/-- `e_row` on a row of a multiple of three words is the row's elements. -/
theorem e_row_eq (hr : RowModel inst encode encodeK ofLimbs index) (copyK : core.marker.Copy K)
    (v : V) (words : Slice K) (h3 : words.val.length % 3 = 0) :
    ∃ row, whir.verify.e_row copyK inst v words = .ok (row, v) ∧
      row.val.map encode = eRow encodeK ofLimbs words.val := by
  have h3ne : ¬ ((3#usize : Usize).val = 0) := by simp
  simp only [whir.verify.e_row, core.num.Usize.div_ceil, h3ne, ↓reduceIte, Std.bind_ok]
  generalize hn : (⟨BitVec.ofNat _ (((Slice.len words).val + (3#usize : Usize).val - 1) /
    (3#usize : Usize).val)⟩ : Usize) = n
  have hd : n.val = words.val.length / 3 := by
    have := words.property
    have hl : (Slice.len words).bv.toNat = words.val.length := by
      exact Slice.len_val words
    rw [← hn]
    simp only [UScalar.val, BitVec.toNat_ofNat, hl]
    have h3v : (3#usize : Usize).val = 3 := by simp
    simp only [UScalar.val] at h3v
    rw [h3v, Nat.mod_eq_of_lt]
    · omega
    · have := Usize.max_def
      simp only [Usize.max, Usize.numBits] at *
      have : 0 < 2 ^ UScalarTy.Usize.numBits := by positivity
      omega
  obtain ⟨row, hloop, erow⟩ := e_row_loop_eq inst encode encodeK ofLimbs index hr words n
    (by rw [hd]; omega) _ 0#usize (alloc.vec.Vec.with_capacity E n) v rfl (by simp)
    (by simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new])
  exact ⟨row, hloop, by rw [erow, hd]; rfl⟩

theorem open_e_rows_loop_eq (hr : RowModel inst encode encodeK ofLimbs index)
    (words : alloc.vec.Vec (alloc.vec.Vec K)) (h3 : ∀ w ∈ words.val, w.val.length % 3 = 0) :
    ∀ (m : Nat) (q : Usize) (rows : alloc.vec.Vec (alloc.vec.Vec E)) (v : V),
      words.val.length - q.val = m → q.val ≤ words.val.length →
      rows.val.map (fun r => r.val.map encode) = (words.val.take q.val).map (fun w => eRow encodeK ofLimbs w.val) →
      ∃ rows', whir.verify.Oracle.open_e_rows_loop inst v words rows q = .ok (v, rows') ∧
        rows'.val.map (fun r => r.val.map encode) = words.val.map (fun w => eRow encodeK ofLimbs w.val) := by
  intro m
  induction m with
  | zero =>
    intro q rows v hm hq hrows
    refine ⟨rows, ?_, by rw [hrows, show q.val = words.val.length by omega, List.take_length]⟩
    unfold whir.verify.Oracle.open_e_rows_loop
    apply loop_done
    have : ¬ (q < alloc.vec.Vec.len words) := by simp; omega
    simp [whir.verify.Oracle.open_e_rows_loop.body, this]
  | succ m ih =>
    intro q rows v hm hq hrows
    have hlt : q.val < words.val.length := by omega
    obtain ⟨row, hrow, erow⟩ := e_row_eq inst encode encodeK ofLimbs index hr inst.coremarkerCopyInst1 v
      (alloc.vec.Vec.deref words.val[q.val]) (by simpa [alloc.vec.Vec.deref] using h3 _ (List.getElem_mem hlt))
    obtain ⟨rows1, hpush, erows1⟩ := push_ok rows row (by
      have : rows.val.length = q.val := by
        simpa [List.length_take, show min q.val words.val.length = q.val by omega] using congrArg List.length hrows
      have := words.property
      scalar_tac)
    have hbody : whir.verify.Oracle.open_e_rows_loop.body inst words v rows q =
        .ok (.cont (v, rows1, Std.Usize.wrapping_add q 1#usize)) := by
      have : q < alloc.vec.Vec.len words := by simp; omega
      simp [whir.verify.Oracle.open_e_rows_loop.body, this, vec_index words q hlt, hrow, hpush, lift]
    have hsucc := succ_val q words.val.length hlt (by have := words.property; scalar_tac)
    obtain ⟨rows', hloop, erows'⟩ := ih (Std.Usize.wrapping_add q 1#usize) rows1 v (by omega) (by omega) (by
      rw [erows1, hsucc, List.map_append, hrows, List.take_succ_eq_append_getElem hlt, List.map_append]
      simp [erow, alloc.vec.Vec.deref])
    refine ⟨rows', ?_, erows'⟩
    unfold whir.verify.Oracle.open_e_rows_loop
    rw [loop_cont hbody]
    unfold whir.verify.Oracle.open_e_rows_loop at hloop
    exact hloop

/-- `open_e_rows` returns the transcript's opened rows, each read as elements, when the rows
event records the oracle's root, depth and leaf width and the queried positions. -/
theorem open_e_rows_eq (hr : RowModel inst encode encodeK ofLimbs index) (ht : Transcript inst encode tape)
    (oracle : whir.verify.Oracle R) (v : V) (queries : Slice Q) (root : R) (depth : Nat) (qs : List Q)
    (words : Nat) (ws : List (List K)) (rest : List (Event E Q R K)) (h3 : ∀ w ∈ ws, w.length % 3 = 0)
    (hroot : oracle.root = root)
    (hdepth : (Std.Usize.wrapping_add oracle.log_msg_cols oracle.log_inv_rate).val = depth)
    (hq : queries.val = qs) (hwords : (Std.Usize.wrapping_shl 3#usize oracle.log_num_interleaved).val = words)
    (hv : tape v (.rows root depth qs words words ws :: rest)) :
    ∃ rows v', whir.verify.Oracle.open_e_rows inst oracle v queries = .ok (.Ok rows, v') ∧ tape v' rest ∧
      rows.val.map (fun r => r.val.map encode) = ws.map (eRow encodeK ofLimbs) := by
  subst hroot hdepth hq hwords
  obtain ⟨w, v1, h1, ew, hv1⟩ := ht.rows v oracle.root
    (Std.Usize.wrapping_add oracle.log_msg_cols oracle.log_inv_rate) queries
    (Std.Usize.wrapping_shl 3#usize oracle.log_num_interleaved)
    (Std.Usize.wrapping_shl 3#usize oracle.log_num_interleaved) ws rest hv
  have h3' : ∀ x ∈ w.val, x.val.length % 3 = 0 := by
    intro x hx
    exact h3 _ (by rw [← ew]; exact List.mem_map_of_mem hx)
  obtain ⟨rows, hloop, erows⟩ := open_e_rows_loop_eq inst encode encodeK ofLimbs index hr w h3' _ 0#usize
    (alloc.vec.Vec.with_capacity _ (alloc.vec.Vec.len w)) v1 rfl (by simp)
    (by simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new])
  refine ⟨rows, v1, ?_, hv1, by rw [erows, ← ew]; simp⟩
  simp [whir.verify.Oracle.open_e_rows, whir.verify.Oracle.depth, h1, lift,
    core.result.Result.Insts.CoreOpsTry.branch, hloop]

end Rows

section Config
variable {V R K Q E : Type} (inst : verifier.OpeningVerifier V R K Q E)

theorem cast_u32_val (x : Usize) (hx : x ≤ U32.max) : (UScalar.cast .U32 x).val = x.val := by
  rw [UScalar.cast_val_eq]; apply Nat.mod_eq_of_lt; scalar_tac

theorem phase_eq (config : whir.config.Config) (level depth : Usize)
    (hl : level.val < config.grinding_bits.val.length) (hq : level.val < config.queries.val.length)
    (hg : config.grinding_bits.val[level.val] ≤ U32.max) :
    whir.verify.WhirReplay.phase inst config level depth =
      .ok (whir.verify.QueryPhase.mk (UScalar.cast .U32 config.grinding_bits.val[level.val]) depth
        config.queries.val[level.val]) := by
  simp only [whir.verify.WhirReplay.phase, whir.config.Config.impl.grinding_bits,
    whir.config.Config.impl.queries, Std.bind_ok]
  rw [slice_index _ level (by simpa [alloc.vec.Vec.deref] using hl)]
  simp only [Std.bind_ok, core.convert.num.ptr_try_from_impls.TryFromU32Usize.try_from,
    core.num.tryFromUScalar]
  simp only [alloc.vec.Vec.deref, Slice.from_val] at hg ⊢
  rw [if_pos (by simpa using hg)]
  simp only [Std.bind_ok]
  rw [slice_index _ level (by simpa using hq)]
  simp

theorem oracle_eq (config : whir.config.Config) (root : R) (level n : Usize)
    (hl : level.val < config.level_ks.val.length) (hk : config.level_ks.val[level.val] ≤ n.val)
    (hr : level.val + 1 < config.log_inv_rates.val.length) :
    ∃ o : whir.verify.Oracle R, whir.verify.WhirReplay.oracle inst config root level n = .ok (.Ok o) ∧
      o.root = root ∧ o.log_num_interleaved = config.level_ks.val[level.val] ∧
      o.log_msg_cols.val = n.val - (config.level_ks.val[level.val]).val ∧
      o.log_inv_rate = config.log_inv_rates.val[level.val + 1] := by
  have hspec := Usize.checked_sub_bv_spec n config.level_ks.val[level.val]
  cases hcs : Usize.checked_sub n config.level_ks.val[level.val] with
  | none => simp only [hcs] at hspec; omega
  | some z =>
    simp only [hcs] at hspec
    have hsucc := succ_val level config.log_inv_rates.val.length (by omega)
      (by have := config.log_inv_rates.property; scalar_tac)
    refine ⟨whir.verify.Oracle.mk root config.level_ks.val[level.val] z
      config.log_inv_rates.val[level.val + 1], ?_, rfl, rfl, hspec.2.1, rfl⟩
    simp only [whir.verify.WhirReplay.oracle, whir.config.Config.impl.level_ks,
      whir.config.Config.impl.log_inv_rates, Std.bind_ok]
    rw [slice_index _ level (by simpa [alloc.vec.Vec.deref] using hl)]
    simp only [Std.bind_ok, lift, alloc.vec.Vec.deref, Slice.from_val, hcs]
    simp only [core.option.Option.ok_or_some, Std.bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
    rw [slice_index _ _ (by simpa [hsucc] using hr)]
    simp [hsucc]

end Config

/-! ## A level's induced basis at the terminal point -/

/-- The normalizers' interpretation: `NovelBasis::new n` holds the model's subspace roots
`s_k(v_k)` as its normalizers and their inverses (zero at zero), read as `F192` constants
through `const`, and `const` reads the constant one as one. -/
structure NormalizerModel (const : primitives.field.gf2_64x3.F192 → Concrete.E) : Prop where
  new : ∀ n : Usize, n.val < 64 → ∃ nb, ntt.basis.NovelBasis.new n = .ok nb ∧
    n.val ≤ nb.normalizers.val.length ∧ n.val ≤ nb.inverses.val.length ∧
    (∀ i (hi : i < nb.normalizers.val.length) f,
      primitives.field.gf2_64x3.F192.Insts.CoreConvertFromF64.from nb.normalizers.val[i] = .ok f →
        const f = Concrete.E.ofK (subspaceRoots n.val)[i]!) ∧
    (∀ i (hi : i < nb.inverses.val.length) f,
      primitives.field.gf2_64x3.F192.Insts.CoreConvertFromF64.from nb.inverses.val[i] = .ok f →
        const f = Concrete.E.ofK (InducedTerminalRefinement.nativeInverse (subspaceRoots n.val)[i]!))
  one : const primitives.field.gf2_64x3.F192.ONE = 1

section Basis
variable {S E : Type} (copy : core.marker.Copy E) (A : fiat_shamir.arith.Arith S E)
  (encode : E → Concrete.E) (const : primitives.field.gf2_64x3.F192 → Concrete.E)

/-- The model's affine factors of a point, as a list. -/
def linList (n : Nat) (pt : List Concrete.E) (k : Nat) : List (Concrete.E × Concrete.E) :=
  (List.range k).map fun j =>
    (pt[j]! + 1, pt[j]! * Concrete.E.ofK (InducedTerminalRefinement.nativeInverse (subspaceRoots n)[j]!))

theorem affine_loop_eq (h : ArithModel A encode const) (hone : const primitives.field.gf2_64x3.F192.ONE = 1)
    (n : Nat) (point : Slice E) (inverses : Slice primitives.field.gf2_64.F64)
    (hlen : point.val.length ≤ inverses.val.length)
    (hinv : ∀ i (hi : i < inverses.val.length) f,
      primitives.field.gf2_64x3.F192.Insts.CoreConvertFromF64.from inverses.val[i] = .ok f →
        const f = Concrete.E.ofK (InducedTerminalRefinement.nativeInverse (subspaceRoots n)[i]!)) :
    ∀ (m : Nat) (k : Usize) (lin : alloc.vec.Vec (E × E)) (a : S), point.val.length - k.val = m →
      k.val ≤ point.val.length →
      lin.val.map (fun p => (encode p.1, encode p.2)) = linList n (point.val.map encode) k.val →
      ∃ lin', whir.verify.affine_factors_loop A a point inverses lin k = .ok (lin', a) ∧
        lin'.val.map (fun p => (encode p.1, encode p.2)) =
          linList n (point.val.map encode) point.val.length := by
  intro m
  induction m with
  | zero =>
    intro k lin a hm hk hlin
    refine ⟨lin, ?_, by rw [hlin, show k.val = point.val.length by omega]⟩
    unfold whir.verify.affine_factors_loop
    apply loop_done
    have : ¬ (k < Slice.len point) := by simp; omega
    simp [whir.verify.affine_factors_loop.body, this]
  | succ m ih =>
    intro k lin a hm hk hlin
    have hkp : k.val < point.val.length := by omega
    have hki : k.val < inverses.val.length := by omega
    obtain ⟨one_plus, h1, e1⟩ := h.add_const a point.val[k.val] primitives.field.gf2_64x3.F192.ONE
    obtain ⟨c, h2, e2⟩ := h.mul_const a point.val[k.val]
      { c0 := inverses.val[k.val], c1 := 0#u64, c2 := 0#u64 }
    obtain ⟨lin1, hpush, elin1⟩ := push_ok lin (one_plus, c) (by
      have : lin.val.length = k.val := by simpa [linList] using congrArg List.length hlin
      have := point.property
      scalar_tac)
    have hbody : whir.verify.affine_factors_loop.body A point inverses a lin k =
        .ok (.cont (a, lin1, Std.Usize.wrapping_add k 1#usize)) := by
      have : k < Slice.len point := by simp; omega
      simp [whir.verify.affine_factors_loop.body, this, slice_index point k hkp,
        slice_index inverses k hki, h1, primitives.field.gf2_64x3.F192.Insts.CoreConvertFromF64.from, h2,
        hpush, lift]
    have hsucc := succ_val k point.val.length hkp (by have := point.property; scalar_tac)
    obtain ⟨lin', hloop, elin'⟩ := ih (Std.Usize.wrapping_add k 1#usize) lin1 a (by omega) (by omega) (by
      rw [elin1, hsucc, List.map_append, hlin]
      simp only [linList, List.range_succ, List.map_append, List.map_cons, List.map_nil]
      rw [e1, e2, hone, hinv k.val hki _ rfl, map_getElem! _ _ _ hkp])
    refine ⟨lin', ?_, elin'⟩
    unfold whir.verify.affine_factors_loop
    rw [loop_cont hbody]
    unfold whir.verify.affine_factors_loop at hloop
    exact hloop

theorem linList_eq (n : Nat) (pt : List Concrete.E) :
    (linList n pt pt.length).toArray = InducedTerminalRefinement.nativeLinear n pt.toArray := by
  apply Array.ext
  · simp [linList, InducedTerminalRefinement.nativeLinear]
  · intro i h1 h2
    simp only [linList, List.size_toArray, List.length_map, List.length_range] at h1
    simp [linList, InducedTerminalRefinement.nativeLinear, getElem!_pos, h1, add_comm]

/-- `affine_factors` is the model's `nativeLinear` on the interpreted point. -/
theorem affine_factors_eq (h : ArithModel A encode const) (hone : const primitives.field.gf2_64x3.F192.ONE = 1)
    (n : Nat) (a : S) (point : Slice E) (inverses : Slice primitives.field.gf2_64.F64)
    (hlen : point.val.length ≤ inverses.val.length)
    (hinv : ∀ i (hi : i < inverses.val.length) f,
      primitives.field.gf2_64x3.F192.Insts.CoreConvertFromF64.from inverses.val[i] = .ok f →
        const f = Concrete.E.ofK (InducedTerminalRefinement.nativeInverse (subspaceRoots n)[i]!)) :
    ∃ lin, whir.verify.affine_factors copy A a point inverses = .ok (lin, a) ∧
      lin.val.length = point.val.length ∧
      factors encode (alloc.vec.Vec.deref lin) =
        InducedTerminalRefinement.nativeLinear n (point.val.map encode).toArray := by
  obtain ⟨lin, hloop, elin⟩ := affine_loop_eq A encode const h hone n point inverses hlen hinv _ 0#usize
    (alloc.vec.Vec.with_capacity _ (Slice.len point)) a rfl (by simp)
    (by simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new, linList])
  refine ⟨lin, by simpa [whir.verify.affine_factors] using hloop, ?_, ?_⟩
  · simpa [linList] using congrArg List.length elin
  · rw [factors, ← linList_eq]
    simp only [alloc.vec.Vec.deref, Slice.from_val, List.length_map] at elin ⊢
    rw [elin]

end Basis

section BasisAt
variable {V R K Q E : Type} (inst : verifier.OpeningVerifier V R K Q E)
  (encode : E → Concrete.E) (const : primitives.field.gf2_64x3.F192 → Concrete.E)
  (encodeK : K → Concrete.K) (ofLimbs : Concrete.K → Concrete.K → Concrete.K → Concrete.E)
  (index : Q → Nat)

/-- One query's term of `nativeBasisAt`. -/
def queryProduct (n : Nat) (pt : Array Concrete.E) (q : Nat) : Concrete.E :=
  ((List.range pt.size).foldl (InducedTerminalRefinement.nativeStep (subspaceRoots n)
    (InducedTerminalRefinement.nativeLinear n pt)) (Concrete.E.ofK (UInt64.ofNat q), 1)).2

theorem basis_at_loop_eq (h : ArithModel inst.fiat_shamirarithVerifierInst.ArithInst encode const)
    (hr : RowModel inst encode encodeK ofLimbs index) (copy : core.marker.Copy E) (n : Nat)
    (queries : alloc.vec.Vec Q) (weights : alloc.vec.Vec E) (nb : ntt.basis.NovelBasis)
    (lin : alloc.vec.Vec (E × E)) (pt : Array Concrete.E) (stop : Usize)
    (hstop : stop.val = min queries.val.length weights.val.length)
    (hlin : factors encode (alloc.vec.Vec.deref lin) = InducedTerminalRefinement.nativeLinear n pt)
    (hsize : lin.val.length = pt.size) (hsks : lin.val.length ≤ nb.normalizers.val.length + 1)
    (hroots : ∀ i (hi : i < nb.normalizers.val.length) f,
      primitives.field.gf2_64x3.F192.Insts.CoreConvertFromF64.from nb.normalizers.val[i] = .ok f →
        const f = Concrete.E.ofK (subspaceRoots n)[i]!) :
    ∀ (m : Nat) (i : Usize) (acc : E) (v : V), stop.val - i.val = m → i.val ≤ stop.val →
      encode acc = (List.range i.val).foldl (fun acc j =>
        (weights.val.map encode)[j]! * queryProduct n pt (queries.val.map index)[j]! + acc) 0 →
      ∃ y, whir.verify.LevelCtx.basis_at_loop copy inst { start := i, «end» := stop } queries weights v nb
          lin acc = .ok (y, v) ∧
        encode y = (List.range stop.val).foldl (fun acc j =>
          (weights.val.map encode)[j]! * queryProduct n pt (queries.val.map index)[j]! + acc) 0 := by
  intro m
  induction m with
  | zero =>
    intro i acc v hm hi hacc
    refine ⟨acc, ?_, by rw [show stop.val = i.val by omega]; exact hacc⟩
    unfold whir.verify.LevelCtx.basis_at_loop
    apply loop_done
    simp [whir.verify.LevelCtx.basis_at_loop.body,
      range_next_none { start := i, «end» := stop } (show stop.val ≤ i.val by omega)]
  | succ m ih =>
    intro i acc v hm hi hacc
    have hlt : i.val < stop.val := by omega
    have hq : i.val < queries.val.length := by omega
    have hw : i.val < weights.val.length := by omega
    obtain ⟨iter1, hnext, hs1, he1⟩ := range_next_some { start := i, «end» := stop } hlt
    obtain ⟨s, hs, es⟩ := hr.query_point v queries.val[i.val]
    obtain ⟨prod, hprod, eprod⟩ := basis_product_eq copy inst.fiat_shamirarithVerifierInst.ArithInst encode
      const h v (alloc.vec.Vec.deref lin) nb (subspaceRoots n) s
      (by simpa [alloc.vec.Vec.deref] using hsks) hroots
    obtain ⟨acc1, hacc1, eacc1⟩ := h.mul_add v weights.val[i.val] prod acc
    have hbody : whir.verify.LevelCtx.basis_at_loop.body copy inst queries weights nb lin
        { start := i, «end» := stop } v acc = .ok (.cont (iter1, v, acc1)) := by
      simp [whir.verify.LevelCtx.basis_at_loop.body, hnext, vec_index_usize queries i hq, hs,
        hprod, vec_index_usize weights i hw, hacc1]
    have hiter : iter1 = { start := Std.Usize.wrapping_add i 1#usize, «end» := stop } := by
      have hsucc := succ_val i stop.val hlt (by scalar_tac)
      cases iter1
      simp only at hs1 he1
      subst he1
      congr 1
      apply UScalar.eq_of_val_eq
      rw [hs1, hsucc]
    have hsucc := succ_val i stop.val hlt (by scalar_tac)
    obtain ⟨y, hy, ey⟩ := ih (Std.Usize.wrapping_add i 1#usize) acc1 v (by omega) (by omega) (by
      rw [hsucc, List.range_succ, List.foldl_append, ← hacc]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [eacc1, eprod, map_getElem! _ _ _ hw, map_getElem! _ _ _ hq, es, queryProduct]
      congr 2
      simp only [factors, alloc.vec.Vec.deref, Slice.from_val] at hlin ⊢
      rw [show (List.map (fun p => (encode p.1, encode p.2)) lin.val).toArray =
        InducedTerminalRefinement.nativeLinear n pt from hlin, hsize])
    refine ⟨y, ?_, ey⟩
    unfold whir.verify.LevelCtx.basis_at_loop
    rw [loop_cont hbody, hiter]
    unfold whir.verify.LevelCtx.basis_at_loop at hy
    exact hy

/-- `LevelCtx::basis_at` at a point of the level's cube is the model's `nativeBasisAt`. -/
theorem basis_at_eq (h : ArithModel inst.fiat_shamirarithVerifierInst.ArithInst encode const)
    (hr : RowModel inst encode encodeK ofLimbs index) (hn : NormalizerModel const)
    (copy : core.marker.Copy E) (ctx : whir.verify.LevelCtx Q E) (v : V) (point : Slice E)
    (hp : point.val.length = ctx.log_msg_cols.val) (h64 : ctx.log_msg_cols.val < 64) :
    ∃ y, whir.verify.LevelCtx.basis_at copy inst ctx v point = .ok (y, v) ∧
      encode y = InducedTerminalRefinement.nativeBasisAt ctx.log_msg_cols.val
        (ctx.queries.val.map index).toArray (ctx.weights.val.map encode).toArray
        (point.val.map encode).toArray := by
  obtain ⟨nb, hnb, hroots_len, hinv_len, hroots, hinv⟩ := hn.new ctx.log_msg_cols h64
  obtain ⟨lin, hlin, hlen, elin⟩ := affine_factors_eq copy
    inst.fiat_shamirarithVerifierInst.ArithInst encode const h hn.one ctx.log_msg_cols.val v point
    (alloc.vec.Vec.deref nb.inverses) (by simp [alloc.vec.Vec.deref]; omega)
    (by simpa [alloc.vec.Vec.deref] using hinv)
  obtain ⟨zero, hzero, ezero⟩ := h.zero v
  have hmin : (core.cmp.impls.OrdUsize.min (alloc.vec.Vec.len ctx.queries) (alloc.vec.Vec.len ctx.weights)).val =
      min ctx.queries.val.length ctx.weights.val.length := by
    simp [core.cmp.impls.OrdUsize.min_val]
  obtain ⟨y, hy, ey⟩ := basis_at_loop_eq inst encode const encodeK ofLimbs index h hr copy ctx.log_msg_cols.val
    ctx.queries ctx.weights nb lin (point.val.map encode).toArray _ hmin elin (by simp [hlen])
    (by omega) hroots _ 0#usize zero v rfl (by simp) (by simp [ezero])
  refine ⟨y, ?_, ?_⟩
  · have hpl : Slice.len point = ctx.log_msg_cols := by
      apply UScalar.eq_of_val_eq; simp [hp]
    simp only [whir.verify.LevelCtx.basis_at, hpl, ↓reduceIte, hnb, Std.bind_ok,
      ntt.basis.NovelBasis.impl.inverses, hlin, lift]
    generalize core.cmp.impls.OrdUsize.min ctx.queries.len ctx.weights.len = stop at hy ⊢
    simp [hzero, hy]
  · rw [ey, InducedTerminalRefinement.nativeBasisAt, hmin]
    simp only [List.size_toArray, List.length_map]
    congr 1
    funext acc j
    rw [queryProduct, Query.toArray_getElem!, Query.toArray_getElem!]
    simp

end BasisAt

theorem vec_range {α : Type} (v : alloc.vec.Vec α) (a b : Usize) (hab : a.val ≤ b.val)
    (hb : b.val ≤ v.val.length) :
    ∃ t, alloc.vec.Vec.index (core.slice.index.SliceIndexRangeUsizeSlice α) v { start := a, «end» := b } =
      .ok t ∧ t.val = (v.val.drop a.val).take (b.val - a.val) := by
  simp only [alloc.vec.Vec.index]
  exact slice_range v.slice a b hab hb

/-! ## The terminal weight -/

section Terminal
open AccumulatedTerminalRefinement
variable {V R K Q E : Type} (inst : verifier.OpeningVerifier V R K Q E)
  (encode : E → Concrete.E) (const : primitives.field.gf2_64x3.F192 → Concrete.E)
  (encodeK : K → Concrete.K) (ofLimbs : Concrete.K → Concrete.K → Concrete.K → Concrete.E)
  (index : Q → Nat)

/-- A level context's term at the terminal point: its induced basis at its suffix of the
fold challenges followed by the residual challenges, at its power. -/
def levelTerm (c : whir.verify.LevelCtx Q E) (ris tail : List Concrete.E) : Concrete.E :=
  encode c.beta * InducedTerminalRefinement.nativeBasisAt c.log_msg_cols.val
    (c.queries.val.map index).toArray (c.weights.val.map encode).toArray
    ((ris.drop c.ris_start.val).take (c.log_msg_cols.val - tail.length) ++ tail).toArray

/-- An out-of-domain context's term at the terminal point. -/
def oodTerm (c : whir.verify.OodCtx E) (ris tail : List Concrete.E) : Concrete.E :=
  encode c.beta * AccumulatedTerminalAlgebra.equalityProduct (c.z.val.map encode)
    ((ris.drop c.ris_start.val).take (c.z.val.length - tail.length) ++ tail)

/-- What the terminal reads of a saved level context: it fits the transcript's fold point. -/
def LevelFits (ris tail : Nat) (c : whir.verify.LevelCtx Q E) : Prop :=
  tail ≤ c.log_msg_cols.val ∧ c.ris_start.val + (c.log_msg_cols.val - tail) ≤ ris ∧ c.log_msg_cols.val < 64

def OodFits (ris tail : Nat) (c : whir.verify.OodCtx E) : Prop :=
  tail ≤ c.z.val.length ∧ c.ris_start.val + (c.z.val.length - tail) ≤ ris

theorem terminal_loop_eq (h : ArithModel inst.fiat_shamirarithVerifierInst.ArithInst encode const)
    (hr : RowModel inst encode encodeK ofLimbs index) (hn : NormalizerModel const)
    (hclone : ∀ x, inst.fiat_shamirarithVerifierInst.ArithInst.coremarkerCopyInst.cloneInst.clone x = .ok x)
    (ris : alloc.vec.Vec E) (levels : alloc.vec.Vec (whir.verify.LevelCtx Q E)) (ris_tail : Slice E)
    (hfit : ∀ c ∈ levels.val, LevelFits ris.val.length ris_tail.val.length c) :
    ∀ (m : Nat) (i : Usize) (weight : E) (v : V), levels.val.length - i.val = m → i.val ≤ levels.val.length →
      encode weight = ((levels.val.take i.val).map fun c =>
        levelTerm encode index c (ris.val.map encode) (ris_tail.val.map encode)).sum →
      ∃ w, whir.verify.WhirReplay.terminal_loop inst { start := i, «end» := alloc.vec.Vec.len levels }
          ris levels v ris_tail (Slice.len ris_tail) weight = .ok (v, w) ∧
        encode w = (levels.val.map fun c =>
          levelTerm encode index c (ris.val.map encode) (ris_tail.val.map encode)).sum := by
  intro m
  induction m with
  | zero =>
    intro i weight v hm hi hw
    refine ⟨weight, ?_, by rw [hw, show i.val = levels.val.length by omega, List.take_length]⟩
    unfold whir.verify.WhirReplay.terminal_loop
    apply loop_done
    simp [whir.verify.WhirReplay.terminal_loop.body,
      range_next_none { start := i, «end» := alloc.vec.Vec.len levels } (by simp; omega)]
  | succ m ih =>
    intro i weight v hm hi hw
    have hlt : i.val < levels.val.length := by omega
    set c := levels.val[i.val] with hc
    obtain ⟨ht, hs, h64⟩ := hfit c (List.getElem_mem hlt)
    obtain ⟨iter1, hnext, hs1, he1⟩ := range_next_some { start := i, «end» := alloc.vec.Vec.len levels }
      (by simpa using hlt)
    have hfold : (Std.Usize.wrapping_sub c.log_msg_cols (Slice.len ris_tail)).val =
        c.log_msg_cols.val - ris_tail.val.length :=
      Fold.sub_val _ _ (by simpa using ht)
    have hend : (Std.Usize.wrapping_add c.ris_start (Std.Usize.wrapping_sub c.log_msg_cols
        (Slice.len ris_tail))).val = c.ris_start.val + (c.log_msg_cols.val - ris_tail.val.length) := by
      rw [Std.Usize.wrapping_add_val_eq, hfold]
      apply Nat.mod_eq_of_lt
      have := ris.property
      have := Usize.max_def
      simp only [UScalar.size] at *
      scalar_tac
    obtain ⟨s, hsl, es⟩ := vec_range ris c.ris_start _ (by rw [hend]; omega) (by rw [hend]; omega)
    obtain ⟨pt, hpt, ept⟩ := to_vec_ok _ hclone s
    obtain ⟨pt1, hpt1, ept1⟩ := extend_ok _ hclone pt ris_tail (by
      rw [ept, es]; simp only [List.length_take, List.length_drop]
      have := ris_tail.property; scalar_tac)
    have hptv : (alloc.vec.Vec.deref pt1).val =
        (ris.val.drop c.ris_start.val).take (c.log_msg_cols.val - ris_tail.val.length) ++ ris_tail.val := by
      simp only [alloc.vec.Vec.deref, Slice.from_val, ept1, ept, es, hend]
      congr 2
      omega
    have hlen : (alloc.vec.Vec.deref pt1).val.length = c.log_msg_cols.val := by
      rw [hptv]
      simp only [List.length_append, List.length_take, List.length_drop]
      omega
    obtain ⟨at_, hat, eat⟩ := basis_at_eq inst encode const encodeK ofLimbs index h hr hn
      inst.fiat_shamirarithVerifierInst.ArithInst.coremarkerCopyInst c v (alloc.vec.Vec.deref pt1) hlen h64
    rw [hptv] at eat
    obtain ⟨w1, hw1, ew1⟩ := h.mul_add v c.beta at_ weight
    have hbody : whir.verify.WhirReplay.terminal_loop.body inst ris levels ris_tail (Slice.len ris_tail)
        { start := i, «end» := alloc.vec.Vec.len levels } v weight = .ok (.cont (iter1, v, w1)) := by
      simp [whir.verify.WhirReplay.terminal_loop.body, hnext, vec_index_usize levels i hlt, ← hc, lift,
        hsl, hpt, hpt1, hat, hw1]
    have hiter : iter1 = { start := Std.Usize.wrapping_add i 1#usize, «end» := alloc.vec.Vec.len levels } := by
      have hsucc := succ_val i levels.val.length hlt (by have := levels.property; scalar_tac)
      cases iter1
      simp only at hs1 he1
      subst he1
      congr 1
      apply UScalar.eq_of_val_eq
      rw [hs1, hsucc]
    have hsucc := succ_val i levels.val.length hlt (by have := levels.property; scalar_tac)
    obtain ⟨y, hy, ey⟩ := ih (Std.Usize.wrapping_add i 1#usize) w1 v (by omega) (by omega) (by
      rw [hsucc, List.take_succ_eq_append_getElem hlt, List.map_append, List.sum_append, ew1, eat, hw]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, ← hc]
      rw [add_comm]
      simp [levelTerm, List.map_take, List.map_drop])
    refine ⟨y, ?_, ey⟩
    unfold whir.verify.WhirReplay.terminal_loop
    rw [loop_cont hbody, hiter]
    unfold whir.verify.WhirReplay.terminal_loop at hy
    exact hy

theorem add_ood_loop_eq (h : ArithModel inst.fiat_shamirarithVerifierInst.ArithInst encode const)
    (copy : core.marker.Copy E) (oods : Slice (whir.verify.OodCtx E)) (ris ris_tail : Slice E)
    (weight0 : E) (hfit : ∀ c ∈ oods.val, OodFits ris.val.length ris_tail.val.length c) :
    ∀ (m : Nat) (i : Usize) (weight : E) (v : V), oods.val.length - i.val = m → i.val ≤ oods.val.length →
      encode weight = encode weight0 + ((oods.val.take i.val).map fun c =>
        oodTerm encode c (ris.val.map encode) (ris_tail.val.map encode)).sum →
      ∃ w, whir.verify.add_ood_terms_loop copy inst.fiat_shamirarithVerifierInst.ArithInst v oods ris ris_tail
          weight (Slice.len ris_tail) i = .ok (w, v) ∧
        encode w = encode weight0 + (oods.val.map fun c =>
          oodTerm encode c (ris.val.map encode) (ris_tail.val.map encode)).sum := by
  intro m
  induction m with
  | zero =>
    intro i weight v hm hi hw
    refine ⟨weight, ?_, by rw [hw, show i.val = oods.val.length by omega, List.take_length]⟩
    unfold whir.verify.add_ood_terms_loop
    apply loop_done
    have : ¬ (i < Slice.len oods) := by simp; omega
    simp [whir.verify.add_ood_terms_loop.body, this]
  | succ m ih =>
    intro i weight v hm hi hw
    have hlt : i.val < oods.val.length := by omega
    set c := oods.val[i.val] with hc
    obtain ⟨ht, hs⟩ := hfit c (List.getElem_mem hlt)
    have hfold : (Std.Usize.wrapping_sub (alloc.vec.Vec.len c.z) (Slice.len ris_tail)).val =
        c.z.val.length - ris_tail.val.length := by
      rw [Fold.sub_val _ _ (by simpa using ht)]; simp
    have hend : (Std.Usize.wrapping_add c.ris_start (Std.Usize.wrapping_sub (alloc.vec.Vec.len c.z)
        (Slice.len ris_tail))).val = c.ris_start.val + (c.z.val.length - ris_tail.val.length) := by
      rw [Std.Usize.wrapping_add_val_eq, hfold]
      apply Nat.mod_eq_of_lt
      have := ris.property
      have := Usize.max_def
      simp only [UScalar.size] at *
      scalar_tac
    obtain ⟨s, hsl, es⟩ := slice_range ris c.ris_start _ (by rw [hend]; omega) (by rw [hend]; omega)
    have hsv : s.val = (ris.val.drop c.ris_start.val).take (c.z.val.length - ris_tail.val.length) := by
      rw [es, hend]
      congr 1
      omega
    obtain ⟨t, ht', et⟩ := Fold.term_eq copy inst.fiat_shamirarithVerifierInst.ArithInst encode const h c v s
      ris_tail (by
        rw [hsv]; simp only [List.length_take, List.length_drop]
        have := ris_tail.property; scalar_tac)
    obtain ⟨w1, hw1, ew1⟩ := h.add v weight t
    have hbody : whir.verify.add_ood_terms_loop.body copy inst.fiat_shamirarithVerifierInst.ArithInst oods ris
        ris_tail (Slice.len ris_tail) v weight i = .ok (.cont (v, w1, Std.Usize.wrapping_add i 1#usize)) := by
      have : i < Slice.len oods := by simp; omega
      simp only [whir.verify.add_ood_terms_loop.body, this, ↓reduceIte, slice_index oods i hlt, ← hc, lift,
        Std.bind_ok, Slice.index_SliceIndexRangeUsizeSliceInst, hsl, ht']
      simp [hw1]
    have hsucc := succ_val i oods.val.length hlt (by have := oods.property; scalar_tac)
    obtain ⟨y, hy, ey⟩ := ih (Std.Usize.wrapping_add i 1#usize) w1 v (by omega) (by omega) (by
      rw [hsucc, List.take_succ_eq_append_getElem hlt, List.map_append, List.sum_append, ew1, et, hw, hsv]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, ← hc, add_assoc]
      simp [oodTerm, List.map_take, List.map_drop])
    refine ⟨y, ?_, ey⟩
    unfold whir.verify.add_ood_terms_loop
    rw [loop_cont hbody]
    unfold whir.verify.add_ood_terms_loop at hy
    exact hy

theorem rotate_toArray (k : Nat) (l : List Concrete.E) :
    (l.drop k ++ l.take k).toArray = rotatePoint k l.toArray := by
  apply Array.toList_inj.mp
  simp [rotatePoint, List.take_of_length_le]

/-- The equality check the terminal ends with returns `Ok` exactly when the interpreted
operands are equal, for an error closure that succeeds (the terminal's returns its error). -/
def EnsureModel (inst : verifier.OpeningVerifier V R K Q E) (encode : E → Concrete.E) : Prop :=
  ∀ {Er T2 : Type} (f : core.ops.function.FnOnce T2 Unit Er) (v : V) (a b : E) (c : T2),
    (∃ e, f.call_once c () = .ok e) →
    ∃ r v', inst.fiat_shamirarithVerifierInst.ensure_eq f v a b c = .ok (r, v') ∧
      (r = .Ok () ↔ encode a = encode b)

/-- The caller's weight is `callerAt` of the interpreted point it is given. -/
def CallerModel {T1 : Type} (W : whir.verify.WeightAt T1 E V R K Q) (weight_at : T1)
    (encode : E → Concrete.E) (callerAt : Array Concrete.E → Concrete.E) : Prop :=
  ∀ v (pt : Slice E), ∃ y v', W.call weight_at v pt = .ok (y, v') ∧
    encode y = callerAt (pt.val.map encode).toArray

/-- The terminal check accepts exactly when the running claim equals the level terms, the
out-of-domain terms and the caller's weight at the rotated point, times the residual's
multilinear extension at the residual challenges. -/
theorem terminal_eq {T1 : Type} (h : ArithModel inst.fiat_shamirarithVerifierInst.ArithInst encode const)
    (hr : RowModel inst encode encodeK ofLimbs index) (hn : NormalizerModel const)
    (hclone : ∀ x, inst.fiat_shamirarithVerifierInst.ArithInst.coremarkerCopyInst.cloneInst.clone x = .ok x)
    (hens : EnsureModel inst encode) (W : whir.verify.WeightAt T1 E V R K Q) (weight_at : T1)
    (callerAt : Array Concrete.E → Concrete.E) (hcall : CallerModel W weight_at encode callerAt)
    (self : whir.verify.WhirReplay V R K Q E) (v : V) (config : whir.config.Config)
    (yr ris_tail : Slice E)
    (hlev : ∀ c ∈ self.levels.val, LevelFits self.ris.val.length ris_tail.val.length c)
    (hood : ∀ c ∈ self.oods.val, OodFits self.ris.val.length ris_tail.val.length c)
    (hk : config.initial_k.val ≤ self.ris.val.length + ris_tail.val.length)
    (hcap : self.ris.val.length + ris_tail.val.length ≤ Usize.max)
    (h64 : ris_tail.val.length < 64) (hyr : yr.val.length = 2 ^ ris_tail.val.length) :
    ∃ r v', whir.verify.WhirReplay.terminal inst W self v config yr ris_tail weight_at = .ok (r, v') ∧
      (r = .Ok () ↔
        ((self.levels.val.map fun c => levelTerm encode index c (self.ris.val.map encode)
            (ris_tail.val.map encode)).sum +
          (self.oods.val.map fun c => oodTerm encode c (self.ris.val.map encode)
            (ris_tail.val.map encode)).sum +
          callerAt (rotatePoint config.initial_k.val
            ((self.ris.val ++ ris_tail.val).map encode).toArray)) *
          Concrete.mle (yr.val.map encode).toArray (ris_tail.val.map encode).toArray =
        encode self.t_r) := by
  obtain ⟨zero, hzero, ezero⟩ := h.zero v
  obtain ⟨w, hw, ew⟩ := terminal_loop_eq inst encode const encodeK ofLimbs index h hr hn hclone self.ris
    self.levels ris_tail hlev _ 0#usize zero v rfl (by simp) (by simp [ezero])
  obtain ⟨w1, hw1, ew1⟩ := add_ood_loop_eq inst encode const h
    inst.fiat_shamirarithVerifierInst.ArithInst.coremarkerCopyInst (alloc.vec.Vec.deref self.oods)
    (alloc.vec.Vec.deref self.ris) ris_tail w (by simpa [alloc.vec.Vec.deref] using hood) _ 0#usize w v rfl
    (by simp) (by simp)
  obtain ⟨fp, hfp, efp⟩ := clone_vec_ok _ hclone self.ris
  obtain ⟨fp1, hfp1, efp1⟩ := extend_ok _ hclone fp ris_tail (by rw [efp]; exact hcap)
  have hrot : config.initial_k.val ≤ fp1.slice.val.length := by
    have : fp1.slice.val = fp1.val := rfl
    rw [this, efp1, efp]; simpa using hk
  let rot : Slice E := Slice.from (fp1.slice.val.drop config.initial_k.val ++ fp1.slice.val.take config.initial_k.val)
    (by have := fp1.slice.property; simp; omega)
  have hrl : core.slice.Slice.rotate_left fp1.slice config.initial_k = .ok rot := by
    simp [core.slice.Slice.rotate_left, hrot, rot]
  obtain ⟨caller, v4, hc4, ec4⟩ := hcall v (alloc.vec.Vec.deref { slice := rot })
  simp only [alloc.vec.Vec.deref] at hc4
  obtain ⟨w2, hw2, ew2⟩ := h.add v4 w1 caller
  obtain ⟨fy, hfy, efy⟩ := h.mle v4 yr ris_tail h64 hyr
  obtain ⟨lhs, hlhs, elhs⟩ := h.mul v4 w2 fy
  obtain ⟨r, v', hens', er⟩ := hens
    (whir.verify.WhirReplay.terminal.closure.Insts.CoreOpsFunctionFnOnceTupleWhirError inst W) v4 lhs self.t_r ()
    ⟨_, rfl⟩
  refine ⟨r, v', ?_, ?_⟩
  · simp only [whir.verify.WhirReplay.terminal, hzero, Std.bind_ok, alloc.vec.Vec.deref]
    simp [hw, whir.verify.add_ood_terms, alloc.vec.Vec.deref] at hw1 ⊢
    simp [hw1, hfp, hfp1, lift, alloc.vec.Vec.deref_mut, whir.config.Config.impl.initial_k, hrl, hc4, hw2,
      hfy, hlhs, hens']
  · rw [er, elhs, ew2, ew1, ew, efy, ec4]
    have hpt : ((alloc.vec.Vec.deref ({ slice := rot } : alloc.vec.Vec E)).val.map encode).toArray =
        rotatePoint config.initial_k.val ((self.ris.val ++ ris_tail.val).map encode).toArray := by
      rw [← rotate_toArray]
      have hv : (alloc.vec.Vec.deref ({ slice := rot } : alloc.vec.Vec E)).val =
          fp1.val.drop config.initial_k.val ++ fp1.val.take config.initial_k.val := by
        simp only [alloc.vec.Vec.deref, rot, Slice.from_val]
        simp [alloc.vec.Vec.val]
      rw [hv, efp1, efp]
      simp [List.map_drop, List.map_take]
    rw [hpt]
    simp [alloc.vec.Vec.deref]

end Terminal

/-! ## Model-side iteration -/

theorem runSteps_foldl {S : Type} (f : Nat → S → S) (n start : Nat) (s : S) :
    Protocol.runSteps f n start s = (List.range' start n).foldl (fun s j => f j s) s := by
  induction n generalizing start s with
  | zero => rfl
  | succ n ih => simp [Protocol.runSteps, ih, List.range'_succ]

theorem runSteps_succ {S : Type} (f : Nat → S → S) (n : Nat) (s : S) :
    Protocol.runSteps f (n + 1) 0 s = f n (Protocol.runSteps f n 0 s) := by
  rw [runSteps_foldl, runSteps_foldl, List.range'_concat]
  simp

/-! ## The residual rounds -/

section Tail
open AccumulatedTerminalRefinement WHIRNativeArithmetic
variable {V R K Q E : Type} (inst : verifier.OpeningVerifier V R K Q E)
  (encode : E → Concrete.E) (const : primitives.field.gf2_64x3.F192 → Concrete.E)
  (encodeK : K → Concrete.K) (ofLimbs : Concrete.K → Concrete.K → Concrete.K → Concrete.E)
  (index : Q → Nat) (tape : V → List (Event E Q R K) → Prop)

/-- A residual round's reads: its challenge, then its polynomial unless it is the last. -/
def tailEvents : E × Option (E × E) → List (Event E Q R K)
  | (r, some (u0, u2)) => [.sample r, .poly u0 u2]
  | (r, none) => [.sample r]

def tailPairs (tail : List E) (msgs : List (E × E)) : List (E × Option (E × E)) :=
  tail.zip (msgs.map some ++ [none])

/-- The tape of the residual rounds. -/
def tailTape (tail : List E) (msgs : List (E × E)) : List (Event E Q R K) :=
  (tailPairs tail msgs).flatMap tailEvents

theorem tailPairs_drop (tail : List E) (msgs : List (E × E)) (hlen : msgs.length + 1 = tail.length)
    (j : Nat) (hj : j < tail.length) :
    (tailPairs tail msgs).drop j =
      (tail[j], if h : j + 1 < tail.length then some msgs[j] else none) :: (tailPairs tail msgs).drop (j + 1) := by
  have hl : j < (tailPairs tail msgs).length := by simp [tailPairs]; omega
  rw [List.drop_eq_getElem_cons hl]
  congr 1
  simp only [tailPairs, List.getElem_zip]
  congr 1
  by_cases h : j + 1 < tail.length
  · simp only [h, ↓reduceDIte]
    rw [List.getElem_append_left (by simp; omega)]
    simp
  · simp only [h, ↓reduceDIte]
    rw [List.getElem_append_right (by simp; omega)]
    simp

/-- The terminal formula of `terminal_eq`. -/
def terminalValue (callerAt : Array Concrete.E → Concrete.E) (initialK : Nat)
    (ris : List E) (levels : List (whir.verify.LevelCtx Q E)) (oods : List (whir.verify.OodCtx E))
    (yr tail : List E) : Concrete.E :=
  ((levels.map fun c => levelTerm encode index c (ris.map encode) (tail.map encode)).sum +
    (oods.map fun c => oodTerm encode c (ris.map encode) (tail.map encode)).sum +
    callerAt (rotatePoint initialK ((ris ++ tail).map encode).toArray)) *
    Concrete.mle (yr.map encode).toArray (tail.map encode).toArray

theorem tail_loop_eq {T1 : Type} (h : ArithModel inst.fiat_shamirarithVerifierInst.ArithInst encode const)
    (hr : RowModel inst encode encodeK ofLimbs index) (hn : NormalizerModel const)
    (ht : Transcript inst encode tape)
    (hclone : ∀ x, inst.fiat_shamirarithVerifierInst.ArithInst.coremarkerCopyInst.cloneInst.clone x = .ok x)
    (hens : EnsureModel inst encode) (W : whir.verify.WeightAt T1 E V R K Q) (weight_at : T1)
    (callerAt : Array Concrete.E → Concrete.E) (hcall : CallerModel W weight_at encode callerAt)
    (config : whir.config.Config) (nc : Usize) (yr : alloc.vec.Vec E)
    (ris0 : alloc.vec.Vec E) (levels0 : alloc.vec.Vec (whir.verify.LevelCtx Q E))
    (oods0 : alloc.vec.Vec (whir.verify.OodCtx E))
    (tail : List E) (msgs : List (E × E)) (rest : List (Event E Q R K))
    (ch : Protocol.Challenges) (pf : Protocol.Opening) (st0 : State)
    (hch : ch.tail = (tail.map encode).toArray)
    (hpf : pf.tailMessages = (msgs.map fun m => (⟨encode m.1, encode m.2⟩ : Protocol.Message Concrete.E)).toArray)
    (hlen : msgs.length + 1 = tail.length) (hnc : nc.val = tail.length)
    (hlev : ∀ c ∈ levels0.val, LevelFits ris0.val.length tail.length c)
    (hood : ∀ c ∈ oods0.val, OodFits ris0.val.length tail.length c)
    (hk : config.initial_k.val ≤ ris0.val.length + tail.length)
    (hcap : ris0.val.length + tail.length ≤ Usize.max)
    (h64 : tail.length < 64) (hyr : yr.val.length = 2 ^ tail.length) :
    ∀ (m j : Nat) (iter : core.ops.range.Range Usize) (self : whir.verify.WhirReplay V R K Q E) (v : V)
      (rt : alloc.vec.Vec E),
      iter.start.val = j → iter.end = nc → tail.length - j = m → j ≤ tail.length →
      tape v (((tailPairs tail msgs).drop j).flatMap tailEvents ++ rest) →
      self.ris = ris0 → self.levels = levels0 → self.oods = oods0 → rt.val = tail.take j →
      encode self.t_r = (Protocol.runSteps (tailStep ch pf) j 0 st0).claim →
      (⟨encode self.quad.c, encode self.quad.a⟩ : Protocol.Message Concrete.E) =
        (Protocol.runSteps (tailStep ch pf) j 0 st0).message →
      (j < tail.length → encode self.quad.b =
        (Protocol.runSteps (tailStep ch pf) j 0 st0).claim + encode self.quad.a) →
      ∃ r v', whir.verify.WhirReplay.last_level_loop inst W iter self v config nc weight_at yr rt =
          .ok (r, v') ∧
        (r = .Ok () ↔ terminalValue encode index callerAt config.initial_k.val ris0.val levels0.val oods0.val
          yr.val tail = (Protocol.runSteps (tailStep ch pf) tail.length 0 st0).claim) := by
  intro m
  induction m with
  | zero =>
    intro j iter self v rt hs he hm hj hv hris hlevs hoods hrt hc hmsg hb
    have hjn : j = tail.length := by omega
    subst hjn
    have hnone : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter = .ok (none, iter) :=
      range_next_none iter (by rw [he, hnc, hs])
    have hrt' : rt.val = tail := by rw [hrt, List.take_length]
    obtain ⟨r, v', hterm, er⟩ := terminal_eq inst encode const encodeK ofLimbs index h hr hn hclone hens W
      weight_at callerAt hcall self v config (alloc.vec.Vec.deref yr) (alloc.vec.Vec.deref rt)
      (by simpa [hris, hlevs, alloc.vec.Vec.deref, hrt'] using hlev)
      (by simpa [hris, hoods, alloc.vec.Vec.deref, hrt'] using hood)
      (by simpa [hris, alloc.vec.Vec.deref, hrt'] using hk)
      (by simpa [hris, alloc.vec.Vec.deref, hrt'] using hcap)
      (by simpa [alloc.vec.Vec.deref, hrt'] using h64)
      (by simpa [alloc.vec.Vec.deref, hrt'] using hyr)
    refine ⟨r, v', ?_, ?_⟩
    · unfold whir.verify.WhirReplay.last_level_loop
      apply loop_done
      simp [whir.verify.WhirReplay.last_level_loop.body, hnone, ht.begin_scope, hterm, ht.end_scope]
    · rw [er, ← hc]
      simp only [terminalValue, alloc.vec.Vec.deref, Slice.from_val, hrt', hris, hlevs, hoods]
  | succ m ih =>
    intro j iter self v rt hs he hm hj hv hris hlevs hoods hrt hc hmsg hb
    have hjt : j < tail.length := by omega
    have hjn : j < nc.val := by omega
    obtain ⟨iter1, hnext, hs1, he1⟩ := range_next_some iter (by rw [he, hs]; exact hjn)
    rw [tailPairs_drop tail msgs hlen j hjt] at hv
    set sj := Protocol.runSteps (tailStep ch pf) j 0 st0 with hsj
    have hstep : Protocol.runSteps (tailStep ch pf) (j + 1) 0 st0 = tailStep ch pf j sj := runSteps_succ _ _ _
    have htj : ch.tail[j]! = encode tail[j] := by rw [hch]; simp [getElem!_pos, hjt]
    have hsize : ch.tail.size = tail.length := by rw [hch]; simp
    have hmod : (iter.start.val + 1) % Usize.size = j + 1 := by
      rw [hs]; apply Nat.mod_eq_of_lt
      have := Usize.max_def; have := nc.hBounds
      simp only [Usize.size, Usize.max] at *
      omega
    obtain ⟨rt1, hpush, ert1⟩ := push_ok rt tail[j] (by
      rw [hrt]; simp only [List.length_take]; have := Usize.max_def; scalar_tac)
    have hrt1 : rt1.val = tail.take (j + 1) := by rw [ert1, hrt, List.take_succ_eq_append_getElem hjt]
    by_cases hl : j + 1 < tail.length
    · have hmj : j < msgs.length := by omega
      simp only [hl, ↓reduceDIte, tailEvents, List.flatMap_cons, List.cons_append, List.nil_append] at hv
      obtain ⟨v1, hsample, hv1⟩ := ht.sample v tail[j] _ hv
      obtain ⟨t, het, et⟩ := quad_eval inst.fiat_shamirarithVerifierInst.ArithInst.coremarkerCopyInst inst
        encode const h self.quad v1 tail[j] sj.claim (hb hjt)
      obtain ⟨q, v3, hrecv, hqc, hqa, hqb, hv3⟩ := recv_eq inst encode const tape h ht
        inst.fiat_shamirarithVerifierInst.ArithInst.coremarkerCopyInst v1 t msgs[j].1 msgs[j].2 _ hv1
      have hbody : whir.verify.WhirReplay.last_level_loop.body inst W config nc weight_at yr iter self v rt =
          .ok (.cont (iter1, { self with t_r := t, quad := q }, v3, rt1)) := by
        simp [whir.verify.WhirReplay.last_level_loop.body, hnext, hsample, het, hpush, lift, hmod, hnc, hl,
          hrecv, core.result.Result.Insts.CoreOpsTry.branch]
      obtain ⟨r, v', hloop, er⟩ := ih (j + 1) iter1 { self with t_r := t, quad := q } v3 rt1
        (by rw [hs1, hs]) (by rw [he1, he]) (by omega) (by omega) hv3 hris hlevs hoods hrt1
        (by rw [hstep, et, hmsg]; simp [tailStep, htj])
        (by rw [hstep]; simp [tailStep, hsize, hl, hpf, getElem!_pos, hmj, hqc, hqa])
        (fun _ => by rw [hstep, hqb, hqa, et, hmsg]; simp [tailStep, htj])
      refine ⟨r, v', ?_, er⟩
      unfold whir.verify.WhirReplay.last_level_loop
      rw [loop_cont hbody]
      unfold whir.verify.WhirReplay.last_level_loop at hloop
      exact hloop
    · simp only [hl, ↓reduceDIte, tailEvents, List.flatMap_cons, List.cons_append, List.nil_append] at hv
      obtain ⟨v1, hsample, hv1⟩ := ht.sample v tail[j] _ hv
      obtain ⟨t, het, et⟩ := quad_eval inst.fiat_shamirarithVerifierInst.ArithInst.coremarkerCopyInst inst
        encode const h self.quad v1 tail[j] sj.claim (hb hjt)
      have hbody : whir.verify.WhirReplay.last_level_loop.body inst W config nc weight_at yr iter self v rt =
          .ok (.cont (iter1, { self with t_r := t }, v1, rt1)) := by
        simp [whir.verify.WhirReplay.last_level_loop.body, hnext, hsample, het, hpush, lift, hmod, hnc, hl]
      obtain ⟨r, v', hloop, er⟩ := ih (j + 1) iter1 { self with t_r := t } v1 rt1
        (by rw [hs1, hs]) (by rw [he1, he]) (by omega) (by omega) hv1 hris hlevs hoods hrt1
        (by rw [hstep, et, hmsg]; simp [tailStep, htj])
        (by rw [hstep]; simp [tailStep, hsize, hl, hmsg])
        (fun h' => absurd h' (by omega))
      refine ⟨r, v', ?_, er⟩
      unfold whir.verify.WhirReplay.last_level_loop
      rw [loop_cont hbody]
      unfold whir.verify.WhirReplay.last_level_loop at hloop
      exact hloop

end Tail

/-! ## The model's level steps on interpreted data -/

section ModelSteps
open AccumulatedTerminalRefinement WHIRNativeArithmetic

theorem foldl_range'_eq {α β : Type} (g : β → α → β) (F : Nat → α) (l : List α) (k : Nat)
    (hF : ∀ j (hj : j < l.length), F (k + j) = l[j]) (b : β) :
    (List.range' k l.length).foldl (fun b j => g b (F j)) b = l.foldl g b := by
  induction l generalizing k b with
  | nil => rfl
  | cons x t ih =>
    simp only [List.length_cons, List.range'_succ, List.foldl_cons]
    have h0 := hF 0 (by simp)
    rw [Nat.add_zero, List.getElem_cons_zero] at h0
    rw [h0]
    exact ih (k + 1) (fun j hj => by
      rw [show k + 1 + j = k + (j + 1) by omega, hF (j + 1) (by simp; omega)]
      simp) _

variable {E : Type} (encode : E → Concrete.E)

theorem foldBlock_eq (rounds : List (E × E × E)) (cs : Protocol.LevelChallenges) (p : Protocol.LevelProof)
    (st : State) (hf : cs.folds = (rounds.map fun x => encode x.1).toArray)
    (ha : p.afterFold = (rounds.map fun x =>
      (⟨encode x.2.1, encode x.2.2⟩ : Protocol.Message Concrete.E)).toArray) :
    foldBlock cs p st = foldModel encode rounds st := by
  have key := foldl_range'_eq (fun s (x : Concrete.E × Protocol.Message Concrete.E) => foldScalar s x.1 x.2)
    (fun j => (cs.folds[j]!, p.afterFold[j]!))
    (rounds.map fun x => (encode x.1, (⟨encode x.2.1, encode x.2.2⟩ : Protocol.Message Concrete.E))) 0
    (fun j hj => by
      simp only [List.length_map] at hj
      simp [hf, ha, getElem!_pos, hj]) st
  simp only [foldBlock, runSteps_foldl, foldStep]
  rw [show cs.folds.size = (rounds.map fun x => (encode x.1,
    (⟨encode x.2.1, encode x.2.2⟩ : Protocol.Message Concrete.E))).length by simp [hf]]
  rw [key, foldModel, List.foldl_map]

theorem oodFold_foldl (lam : Concrete.E) (l : List (Array Concrete.E × Concrete.E × Protocol.Message Concrete.E))
    (acc : State × Concrete.E) :
    Query.oodFold lam l acc = l.foldl (fun (acc : State × Concrete.E) x =>
      (batchScalar acc.1 (.ood x.1) x.2.1 (acc.2 * lam) x.2.2, acc.2 * lam)) acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons x l ih => obtain ⟨st, b⟩ := acc; simp [Query.oodFold, ih]

theorem oodBatch_eq (data : List (Array Concrete.E × Concrete.E × Protocol.Message Concrete.E))
    (cs : Protocol.LevelChallenges) (p : Protocol.LevelProof) (st : State)
    (hz : cs.oodPoints = (data.map (·.1)).toArray)
    (ho : p.oods = (data.map fun x => (⟨x.2.1, x.2.2⟩ : Protocol.OodClaim)).toArray) :
    oodBatch cs p st = Query.oodFold cs.lambda data (st, 1) := by
  have key := foldl_range'_eq (fun (acc : State × Concrete.E) (x : Array Concrete.E × Concrete.E ×
      Protocol.Message Concrete.E) => (batchScalar acc.1 (.ood x.1) x.2.1 (acc.2 * cs.lambda) x.2.2,
      acc.2 * cs.lambda))
    (fun j => (cs.oodPoints[j]!, p.oods[j]!.value, p.oods[j]!.intro)) data 0
    (fun j hj => by simp [hz, ho, getElem!_pos, hj]) (st, 1)
  rw [oodFold_foldl, ← key]
  simp only [oodBatch, runSteps_foldl, oodStep]
  rw [show p.oods.size = data.length by simp [ho]]
  rfl

theorem enforced_base (rows : Array (Array Concrete.E)) (rs ws : Array Concrete.E) :
    Protocol.enforced rows rs ws true = Protocol.enforced (rows.map (·.reverse)) rs ws false := by
  simp only [Protocol.enforced, ↓reduceIte, Array.size_map, Bool.false_eq_true]
  have hf : (fun i : Nat => ws[i]! * Concrete.dot (rows[i]! : Array Concrete.E).reverse (Concrete.eqTable rs)) =
      (fun i : Nat => ws[i]! * Concrete.dot (rows.map (·.reverse))[i]! (Concrete.eqTable rs)) := by
    funext i
    by_cases hi : i < rows.size
    · simp [getElem!_pos, hi]
    · simp only [getElem!_neg rows i hi, getElem!_neg (rows.map (·.reverse)) i (by simpa using hi)]
      rfl
  rw [hf]

private theorem except_bind_ok' {S T : Type} (s : S) (f : S → Except String T) :
    ((Except.ok s : Except String S) >>= f) = f s := rfl

/-- A model level passes every check and returns its batched state when the proof has the
level's shapes and the query challenges derive positions. -/
theorem verifyLevel_ok (c : Protocol.Config) (ch : Protocol.Challenges) (pf : Protocol.Opening) (j : Nat)
    (s : State) (qs : Array Nat)
    (hround : pf.levels[j]!.afterFold.size = ch.levels[j]!.folds.size)
    (hood : pf.levels[j]!.oods.size = ch.levels[j]!.oodPoints.size)
    (hnext : if j + 1 < c.folds.size then pf.levels[j]!.nextOracle.isSome = true
      else pf.levels[j]!.nextOracle.isSome = false ∧
        pf.residual.size = 2 ^ (foldBlock ch.levels[j]! pf.levels[j]! s).n)
    (hq : deriveQueries ((foldBlock ch.levels[j]! pf.levels[j]! s).n + c.rates[j]!) c.queries[j]!
      ch.levels[j]!.querySqueezes = some qs)
    (hrows : pf.levels[j]!.rows.size = qs.size) :
    verifyLevel c ch pf j s = .ok (queryBatch (foldBlock ch.levels[j]! pf.levels[j]! s).n j ch.levels[j]!
      pf.levels[j]! qs (oodBatch ch.levels[j]! pf.levels[j]! (foldBlock ch.levels[j]! pf.levels[j]! s))) := by
  unfold verifyLevel
  by_cases hm : j + 1 < c.folds.size
  · rw [if_pos hm] at hnext
    simp [hround, hood, hm, hnext, hq, hrows, Option.elim]
    rfl
  · rw [if_neg hm] at hnext
    simp [hround, hood, hm, hnext, hq, hrows, Option.elim]
    rfl

/-- Every saved context sits on the transcript's fold point and spans the variables left. -/
def ModelFits (s : State) : Prop :=
  ∀ sv ∈ s.source.saved, sv.risStart ≤ s.source.ris.length ∧
    sv.basis.dimension = s.source.ris.length + s.n - sv.risStart ∧ sv.basis.dimension < 64

theorem ModelFits.fold (s : State) (h : ModelFits s) (hn : 0 < s.n) (r : Concrete.E) (m : Protocol.Message Concrete.E) :
    ModelFits (foldScalar s r m) := by
  intro sv hsv
  obtain ⟨h1, h2, h3⟩ := h sv hsv
  simp only [foldScalar, SourceState.step, List.length_append, List.length_singleton]
  exact ⟨by omega, by omega, h3⟩

theorem ModelFits.batch (s : State) (h : ModelFits s) (basis : Basis) (hb : basis.dimension = s.n)
    (h64 : s.n < 64) (value beta : Concrete.E) (m : Protocol.Message Concrete.E) :
    ModelFits (batchScalar s basis value beta m) := by
  intro sv hsv
  simp only [batchScalar, SourceState.step, List.mem_append, List.mem_singleton] at hsv
  rcases hsv with hsv | rfl
  · exact h sv hsv
  · refine ⟨?_, ?_, ?_⟩ <;> simp [batchScalar, SourceState.step] <;> omega

theorem ModelFits.ofFold (rounds : List (E × E × E)) (s : State) (h : ModelFits s)
    (hn : rounds.length ≤ s.n) : ModelFits (foldModel encode rounds s) := by
  induction rounds generalizing s with
  | nil => exact h
  | cons x rounds ih =>
    simp only [foldModel, List.foldl_cons] at ih ⊢
    apply ih
    · exact h.fold s (by simp at hn; omega) _ _
    · simp only [foldScalar]; simp at hn; omega

theorem ModelFits.ofOodFold (lam : Concrete.E)
    (data : List (Array Concrete.E × Concrete.E × Protocol.Message Concrete.E))
    (acc : State × Concrete.E) (h : ModelFits acc.1) (hz : ∀ d ∈ data, d.1.size = acc.1.n) (h64 : acc.1.n < 64) :
    ModelFits (Query.oodFold lam data acc).1 ∧ (Query.oodFold lam data acc).1.n = acc.1.n := by
  induction data generalizing acc with
  | nil => exact ⟨h, rfl⟩
  | cons d data ih =>
    obtain ⟨st, b⟩ := acc
    obtain ⟨z, y, m⟩ := d
    simp only [Query.oodFold]
    have hb := ModelFits.batch st h (Basis.ood z) (hz (z, y, m) (by simp)) h64 y (b * lam) m
    obtain ⟨e1, e2⟩ := ih (batchScalar st (Basis.ood z) y (b * lam) m, b * lam) hb
      (fun d hd => by simpa [batchScalar] using hz d (by simp [hd])) (by simpa [batchScalar] using h64)
    exact ⟨e1, by rw [e2]; rfl⟩

end ModelSteps

/-! ## The terminal formula is the model's source terminal -/

section Link
open AccumulatedTerminalRefinement WHIRNativeArithmetic
variable {V R K Q E : Type} (encode : E → Concrete.E) (index : Q → Nat)

theorem sum_filter_zero {α : Type} (l : List α) (p : α → Bool) (f : α → Concrete.E)
    (hz : ∀ x ∈ l, p x = true → f x = 0) :
    (l.map f).sum = ((l.filter fun x => !p x).map f).sum := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    have ih' := ih (fun y hy => hz y (by simp [hy]))
    by_cases hp : p x = true
    · simp [hp, hz x (by simp) hp, ih']
    · simp [hp, ih']

theorem levels_sum (levels : List (whir.verify.LevelCtx Q E)) (svs : List Saved)
    (hrel : List.Forall₂ (Query.LevelMatch encode index) levels svs) (ris tail : List Concrete.E) :
    (levels.map fun c => levelTerm encode index c ris tail).sum = (svs.map fun s => s.queryTerm ris tail).sum := by
  induction hrel with
  | nil => rfl
  | @cons c sv cs svs' hm _ ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    congr 1
    obtain ⟨hstart, hbeta, lam, hbasis, hw⟩ := hm
    have hws : (c.weights.val.map encode).toArray = Concrete.powers lam c.queries.val.length := by
      rw [hw]
    simp only [levelTerm, Saved.queryTerm, hbasis, Saved.sourcePoint, Basis.dimension, hstart, hbeta, hws,
      List.size_toArray, List.length_map]

theorem oods_sum (oods : List (whir.verify.OodCtx E)) (svs : List Saved)
    (hrel : List.Forall₂ (Query.OodMatch encode) oods svs) (ris tail : List Concrete.E) :
    (oods.map fun c => oodTerm encode c ris tail).sum = (svs.map fun s => s.oodTerm ris tail).sum := by
  induction hrel with
  | nil => rfl
  | @cons c sv cs svs' hm _ ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    congr 1
    obtain ⟨hstart, hbasis, hbeta⟩ := hm
    simp [oodTerm, Saved.oodTerm, hbasis, Saved.sourcePoint, Basis.dimension, hstart, hbeta]

/-- The source's terminal value, over the source's two context lists, is the model's
`sourceTerminal` over its interleaved saved contexts. -/
theorem terminal_link (w : whir.verify.WhirReplay V R K Q E) (s : State) (hrel : Query.StateRel encode index w s)
    (callerAt : Array Concrete.E → Concrete.E) (k : Nat) (yr tail : List E) :
    terminalValue encode index callerAt k w.ris.val w.levels.val w.oods.val yr tail =
      sourceTerminal (callerAt (rotatePoint k (s.source.ris ++ tail.map encode).toArray)) s.source.saved
        s.source.ris (tail.map encode) (yr.map encode).toArray := by
  have hq : (s.source.saved.map fun sv => sv.queryTerm s.source.ris (tail.map encode)).sum =
      ((s.source.saved.filter fun sv => !Query.isOod sv).map fun sv =>
        sv.queryTerm s.source.ris (tail.map encode)).sum :=
    sum_filter_zero _ Query.isOod _ (fun sv _ h => by
      cases hb : sv.basis with
      | ood z => simp [Saved.queryTerm, hb]
      | query n qs l => simp [Query.isOod, hb] at h)
  have ho : (s.source.saved.map fun sv => sv.oodTerm s.source.ris (tail.map encode)).sum =
      ((s.source.saved.filter fun sv => !!Query.isOod sv).map fun sv =>
        sv.oodTerm s.source.ris (tail.map encode)).sum :=
    sum_filter_zero _ (fun sv => !Query.isOod sv) _ (fun sv _ h => by
      cases hb : sv.basis with
      | ood z => simp [Query.isOod, hb] at h
      | query n qs l => simp [Saved.oodTerm, hb])
  simp only [Bool.not_not] at ho
  rw [terminalValue, sourceTerminal, hq, ho, ← levels_sum encode index _ _ hrel.levels,
    ← oods_sum encode _ _ hrel.oods, ← hrel.ris, List.map_append]

theorem forall₂_mem {α β : Type} {Rel : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ Rel l₁ l₂) : ∀ a ∈ l₁, ∃ b ∈ l₂, Rel a b := by
  induction h with
  | nil => intro a ha; simp at ha
  | @cons a b _ _ hab _ ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨b, by simp, hab⟩
    · obtain ⟨y, hy, hxy⟩ := ih x hx
      exact ⟨y, by simp [hy], hxy⟩

/-- The model's context invariant gives what the terminal reads of each source context. -/
theorem fits_of_model (w : whir.verify.WhirReplay V R K Q E) (s : State) (hrel : Query.StateRel encode index w s)
    (hf : ModelFits s) :
    (∀ c ∈ w.levels.val, LevelFits w.ris.val.length s.n c) ∧ (∀ c ∈ w.oods.val, OodFits w.ris.val.length s.n c) := by
  have hlen : w.ris.val.length = s.source.ris.length := by rw [← hrel.ris]; simp
  constructor
  · intro c hc
    obtain ⟨sv, hsv, hm⟩ := forall₂_mem hrel.levels c hc
    obtain ⟨hstart, _, lam, hbasis, _⟩ := hm
    obtain ⟨h1, h2, h3⟩ := hf sv (List.mem_of_mem_filter hsv)
    rw [hbasis] at h2 h3
    simp only [Basis.dimension] at h2 h3
    refine ⟨by omega, by omega, h3⟩
  · intro c hc
    obtain ⟨sv, hsv, hm⟩ := forall₂_mem hrel.oods c hc
    obtain ⟨hstart, hbasis, _⟩ := hm
    obtain ⟨h1, h2, _⟩ := hf sv (List.mem_of_mem_filter hsv)
    rw [hbasis] at h2
    simp only [Basis.dimension, List.size_toArray, List.length_map] at h2
    refine ⟨by omega, by omega⟩

end Link

theorem shl_one_val (hw : System.Platform.numBits = 64) (n : Usize) (h : n.val < 64) :
    (Std.Usize.wrapping_shl 1#usize n).val = 2 ^ n.val := by
  simp only [Std.Usize.wrapping_shl, UScalar.wrapping_shl_rhs, WrappingShiftRhs.amount_unsigned]
  have hn : UScalarTy.Usize.numBits = 64 := by simp [hw]
  have h1 : (1#usize : Usize).val = 1 := by simp
  have hv : n.val % UScalarTy.Usize.numBits = n.val := by rw [hn]; exact Nat.mod_eq_of_lt h
  rw [hv]
  show ((1#usize : Usize).bv <<< n.val).toNat = 2 ^ n.val
  rw [BitVec.toNat_shiftLeft]
  change (1#usize : Usize).val <<< n.val % 2 ^ UScalarTy.Usize.numBits = 2 ^ n.val
  rw [h1, Nat.one_shiftLeft, hn]
  exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) h)

theorem shl_three_val (hw : System.Platform.numBits = 64) (k : Usize) (h : k.val < 62) :
    (Std.Usize.wrapping_shl 3#usize k).val = 3 * 2 ^ k.val := by
  simp only [Std.Usize.wrapping_shl, UScalar.wrapping_shl_rhs, WrappingShiftRhs.amount_unsigned]
  have hn : UScalarTy.Usize.numBits = 64 := by simp [hw]
  have h3 : (3#usize : Usize).val = 3 := by simp
  have hv : k.val % UScalarTy.Usize.numBits = k.val := by rw [hn]; exact Nat.mod_eq_of_lt (by omega)
  rw [hv]
  show ((3#usize : Usize).bv <<< k.val).toNat = 3 * 2 ^ k.val
  rw [BitVec.toNat_shiftLeft]
  change (3#usize : Usize).val <<< k.val % 2 ^ UScalarTy.Usize.numBits = 3 * 2 ^ k.val
  rw [h3, Nat.shiftLeft_eq, hn]
  apply Nat.mod_eq_of_lt
  have : 2 ^ k.val ≤ 2 ^ 61 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h64 : (2 : Nat) ^ 64 = 8 * 2 ^ 61 := by norm_num
  omega

theorem add_val_lt (x y : Usize) (h : x.val + y.val < 64) :
    (Std.Usize.wrapping_add x y).val = x.val + y.val := by
  rw [Std.Usize.wrapping_add_val_eq]
  have : x.val + y.val < UScalar.size .Usize := by
    have := Usize.max_def; simp only [UScalar.size] at *; scalar_tac
  exact Nat.mod_eq_of_lt this

/-! ## The last level -/

section Last
open AccumulatedTerminalRefinement WHIRNativeArithmetic
variable {V R K Q E : Type} (inst : verifier.OpeningVerifier V R K Q E)
  (encode : E → Concrete.E) (const : primitives.field.gf2_64x3.F192 → Concrete.E)
  (encodeK : K → Concrete.K) (ofLimbs : Concrete.K → Concrete.K → Concrete.K → Concrete.E)
  (index : Q → Nat) (tape : V → List (Event E Q R K) → Prop)

/-- The model's state after a later level's query batch with no out-of-domain claims. -/
def lastState (st : State) (n : Nat) (qs : List Q) (lam : E) (rows : List (List K)) (point : List E)
    (i0 i2 : E) : State :=
  batchScalar st (.query n (qs.map index).toArray (encode lam))
    (Protocol.enforced (rows.map fun w => (eRow encodeK ofLimbs w).toArray).toArray (point.map encode).toArray
      (Concrete.powers (encode lam) qs.length) false) (1 * encode lam) ⟨encode i0, encode i2⟩

theorem last_level_eq {T1 : Type} (hw : System.Platform.numBits = 64)
    (h : ArithModel inst.fiat_shamirarithVerifierInst.ArithInst encode const)
    (hr : RowModel inst encode encodeK ofLimbs index) (hn : NormalizerModel const)
    (ht : Transcript inst encode tape)
    (hclone : ∀ x, inst.fiat_shamirarithVerifierInst.ArithInst.coremarkerCopyInst.cloneInst.clone x = .ok x)
    (hens : EnsureModel inst encode) (W : whir.verify.WeightAt T1 E V R K Q) (weight_at : T1)
    (callerAt : Array Concrete.E → Concrete.E) (hcall : CallerModel W weight_at encode callerAt)
    (config : whir.config.Config) (oracle : whir.verify.Oracle R) (root : R) (depth words bits : Nat)
    (horoot : oracle.root = root)
    (hodepth : (Std.Usize.wrapping_add oracle.log_msg_cols oracle.log_inv_rate).val = depth)
    (howords : (Std.Usize.wrapping_shl 3#usize oracle.log_num_interleaved).val = words)
    (level_rs : Slice E)
    (w : whir.verify.WhirReplay V R K Q E) (st : State) (hrel : Query.StateRel encode index w st)
    (hfits : ModelFits st) (v : V) (n : Usize) (hst : st.n = n.val) (hn64 : n.val < 64)
    (ys : List E) (qs : List Q) (lam : E) (rows : List (List K)) (i0 i2 : E) (tail : List E)
    (msgs : List (E × E)) (rest : List (Event E Q R K))
    (hv : tape v ([.scalars ys, .grind bits, .queries depth qs, .sample lam, .rows root depth qs words words rows,
      .poly i0 i2] ++ (tailTape tail msgs ++ rest)))
    (hys : ys.length = 2 ^ n.val)
    (hgl : (alloc.vec.Vec.len config.level_ks).val < config.grinding_bits.val.length)
    (hql : (alloc.vec.Vec.len config.level_ks).val < config.queries.val.length)
    (hg : config.grinding_bits.val[(alloc.vec.Vec.len config.level_ks).val] ≤ U32.max)
    (hbits : (config.grinding_bits.val[(alloc.vec.Vec.len config.level_ks).val]).val = bits)
    (hcount : qs.length = (config.queries.val[(alloc.vec.Vec.len config.level_ks).val]).val)
    (hrows : rows.length = qs.length) (hne : rows ≠ [])
    (hwidth : ∀ r ∈ rows, r.length = 3 * 2 ^ level_rs.val.length) (hpt : level_rs.val.length < 64)
    (htail : tail.length = n.val) (hmsgs : msgs.length + 1 = tail.length)
    (hk : config.initial_k.val ≤ w.ris.val.length + tail.length)
    (hcap : w.ris.val.length + tail.length + 1 ≤ Usize.max)
    (hcapo : w.oods.val.length < Usize.max) (hcapl : w.levels.val.length < Usize.max)
    (ch : Protocol.Challenges) (pf : Protocol.Opening) (hch : ch.tail = (tail.map encode).toArray)
    (hpf : pf.tailMessages = (msgs.map fun m => (⟨encode m.1, encode m.2⟩ : Protocol.Message Concrete.E)).toArray) :
    ∃ r v', ∃ wF : whir.verify.WhirReplay V R K Q E,
      whir.verify.WhirReplay.last_level inst W w v config oracle level_rs n weight_at = .ok (r, v') ∧
      Query.StateRel encode index wF
        (lastState encode encodeK ofLimbs index st n.val qs lam rows level_rs.val i0 i2) ∧
      wF.ris = w.ris ∧
      (r = .Ok () ↔ terminalValue encode index callerAt config.initial_k.val wF.ris.val wF.levels.val wF.oods.val
        ys tail = (closeTail ch pf (lastState encode encodeK ofLimbs index st n.val qs lam rows level_rs.val
          i0 i2)).claim) := by
  have hshl := shl_one_val hw n hn64
  obtain ⟨yr, v1, h1, eyr, hv1⟩ := ht.scalars v (Std.Usize.wrapping_shl 1#usize n) ys _ hv (by rw [hshl, hys])
  have hgv : (UScalar.cast .U32 config.grinding_bits.val[(alloc.vec.Vec.len config.level_ks).val]).val = bits := by
    rw [cast_u32_val _ hg, hbits]
  obtain ⟨b, v2, h2, hv2, ebq, ebl, ebw⟩ := begin_query_eq inst encode const tape h ht v1
    (whir.verify.QueryPhase.mk (UScalar.cast .U32 config.grinding_bits.val[(alloc.vec.Vec.len config.level_ks).val])
      (Std.Usize.wrapping_add oracle.log_msg_cols oracle.log_inv_rate)
      config.queries.val[(alloc.vec.Vec.len config.level_ks).val]) qs lam _ hcount (by
        show tape v1 (.grind (UScalar.cast .U32 _).val :: .queries (Std.Usize.wrapping_add _ _).val qs :: _)
        rw [hgv, hodepth]; exact hv1)
  obtain ⟨rowsV, v3, h3, hv3, erows⟩ := open_e_rows_eq inst encode encodeK ofLimbs index tape hr ht oracle v2
    (alloc.vec.Vec.deref b.queries) root depth qs words rows _ (fun r hr' => by rw [hwidth r hr']; omega)
    horoot hodepth (by simpa [alloc.vec.Vec.deref] using ebq) howords hv2
  have hrows_ne : rowsV.val ≠ [] := by
    intro hnil; apply hne
    have := congrArg List.length erows
    simp [hnil] at this
    exact this
  have hlenrows : rowsV.val.length = rows.length := by simpa using congrArg List.length erows
  have hwidthV : ∀ r ∈ rowsV.val, r.val.length = 2 ^ level_rs.val.length := by
    intro r hr'
    have hmem : r.val.map encode ∈ rows.map (eRow encodeK ofLimbs) := by
      rw [← erows]; exact List.mem_map_of_mem hr'
    obtain ⟨wd, hwd, hwe⟩ := List.mem_map.mp hmem
    have := congrArg List.length hwe
    simp only [eRow, List.length_map, List.length_range] at this
    rw [hwidth wd hwd] at this
    simp at this
    omega
  obtain ⟨sum, h4, esum⟩ := Query.ext_enforced_eq inst.fiat_shamirarithVerifierInst.ArithInst.coremarkerCopyInst
    inst encode const h v3 rowsV level_rs (alloc.vec.Vec.deref b.weights) (2 ^ level_rs.val.length) hrows_ne
    hwidthV hpt le_rfl (by
      have := congrArg List.length ebw
      simp only [List.length_map, Array.length_toList, BatchingRefinement.size_powers] at this
      simp [alloc.vec.Vec.deref, this, hlenrows, hrows])
  obtain ⟨intro, v5, hrecv, hic, hia, hib, hv5⟩ := recv_eq inst encode const tape h ht
    inst.fiat_shamirarithVerifierInst.ArithInst.coremarkerCopyInst v3 sum i0 i2 _ hv3
  obtain ⟨w2, hfin, hris2, hrel2⟩ := Query.finish_query_eq inst encode const index h w st hrel v3 v3 v5 b
    (alloc.vec.Vec.new _) n sum intro (ht.end_scope v3) hrecv (by rw [hib, hia]) (by simp [alloc.vec.Vec.new])
    (by rw [ebw, ebq, ebl]) (by simpa [alloc.vec.Vec.new] using hcapo) hcapl
  have hsF : batchScalar (Query.oodFold (encode b.lambda) (Query.oodData encode (alloc.vec.Vec.new
      (whir.verify.Ood E)).val) (st, 1)).1 (.query n.val (b.queries.val.map index).toArray (encode b.lambda))
      (encode sum) ((Query.oodFold (encode b.lambda) (Query.oodData encode (alloc.vec.Vec.new
        (whir.verify.Ood E)).val) (st, 1)).2 * encode b.lambda) ⟨encode intro.c, encode intro.a⟩ =
      lastState encode encodeK ofLimbs index st n.val qs lam rows level_rs.val i0 i2 := by
    simp only [alloc.vec.Vec.new, Query.oodData, List.map_nil, Query.oodFold, lastState, ebq, ebl, hic, hia]
    congr 2
    rw [esum]
    have hw' : ((alloc.vec.Vec.deref b.weights).val.map encode).toArray = Concrete.powers (encode lam) qs.length := by
      simp only [alloc.vec.Vec.deref, Slice.from_val]; rw [ebw]
    have hrw : rowsV.val.map (fun r => (r.val.map encode).toArray) = (rows.map (eRow encodeK ofLimbs)).map
        List.toArray := by rw [← erows]; simp
    rw [hw', hrw]
    simp only [List.map_map]
    rfl
  rw [hsF] at hrel2
  set sF := lastState encode encodeK ofLimbs index st n.val qs lam rows level_rs.val i0 i2 with hsFdef
  have hfitsF : ModelFits sF := by
    rw [hsFdef, lastState]
    exact ModelFits.batch st hfits _ (by simp [Basis.dimension, hst]) (by omega) _ _ _
  have hnF : sF.n = n.val := by rw [hsFdef]; simp [lastState, batchScalar, hst]
  obtain ⟨hlevF, hoodF⟩ := fits_of_model encode index w2 sF hrel2 hfitsF
  obtain ⟨r, v', hloop, er⟩ := tail_loop_eq inst encode const encodeK ofLimbs index tape h hr hn ht hclone hens W
    weight_at callerAt hcall config n yr w2.ris w2.levels w2.oods tail msgs rest ch pf sF hch hpf hmsgs
    htail.symm (by rw [hnF, ← htail] at hlevF; exact hlevF) (by rw [hnF, ← htail] at hoodF; exact hoodF)
    (by rw [hris2]; exact hk) (by rw [hris2]; omega) (by omega) (by rw [eyr, hys, htail])
    tail.length 0 { start := 0#usize, «end» := n } w2 v5 (alloc.vec.Vec.with_capacity E n) (by simp) rfl
    (by simp) (by simp) (by simpa [tailTape] using hv5) rfl rfl rfl (by simp [alloc.vec.Vec.with_capacity,
      alloc.vec.Vec.new]) hrel2.claim hrel2.message (fun _ => hrel2.linear)
  refine ⟨r, v', w2, ?_, hrel2, hris2, ?_⟩
  · have hph := phase_eq inst config (alloc.vec.Vec.len config.level_ks)
      (Std.Usize.wrapping_add oracle.log_msg_cols oracle.log_inv_rate) hgl hql hg
    simp only [whir.verify.WhirReplay.last_level, lift, Std.bind_ok, h1, core.result.Result.Insts.CoreOpsTry.branch,
      whir.config.Config.level_steps, whir.verify.Oracle.depth, hph]
    generalize (whir.verify.QueryPhase.mk (UScalar.cast .U32
      config.grinding_bits.val[(alloc.vec.Vec.len config.level_ks).val])
      (Std.Usize.wrapping_add oracle.log_msg_cols oracle.log_inv_rate)
      config.queries.val[(alloc.vec.Vec.len config.level_ks).val]) = ph at h2 ⊢
    simp [h2, h3, h4, hfin, hloop]
  · rw [er, eyr]
    simp only [closeTail, hch, List.size_toArray, List.length_map]

end Last

/-! ## The configuration -/

/-- The source configuration is the model's: the lane fold then the level folds, the rates,
query counts and out-of-domain counts per level, at most 32 grinding bits per level, a
witness of fewer than 64 variables, level folds below 62 (the source's guard on a row of three
words per element), and no zero-knowledge padding of the lanes (the model has no padding, so
`verify` never takes its reveal branch). -/
structure ConfigRel (config : whir.config.Config) (c : Protocol.Config) (log_n : Usize) : Prop where
  logN : c.logN = log_n.val
  folds : c.folds.toList = (config.initial_k :: config.level_ks.val).map (·.val)
  rates : c.rates.toList = config.log_inv_rates.val.map (·.val)
  queries : c.queries.toList = config.queries.val.map (·.val)
  oods : c.oodCounts.toList = config.ood_samples.val.map (·.val)
  grinding_len : config.grinding_bits.val.length = c.folds.size
  grinding : ∀ g ∈ config.grinding_bits.val, g.val ≤ U32.max
  log64 : log_n.val < 64
  ks : ∀ k ∈ config.level_ks.val, k.val < 62
  padding : config.padding.val = 0

theorem arr_get (a : Array Nat) (l : List Nat) (h : a.toList = l) (j : Nat) : a[j]! = l[j]! := by
  cases a; simp_all

theorem runChecked_last {S : Type} (f : Nat → S → Except String S) (n start : Nat) (s : S) :
    Protocol.runChecked f (n + 1) start s = (Protocol.runChecked f n start s) >>= f (start + n) := by
  induction n generalizing start s with
  | zero =>
    show (f start s >>= fun next => Protocol.runChecked f 0 (start + 1) next) = f start s
    cases f start s <;> rfl
  | succ n ih =>
    rw [Protocol.runChecked, Protocol.runChecked]
    cases hf : f start s with
    | error e => rfl
    | ok x =>
      show Protocol.runChecked f (n + 1) (start + 1) x =
        Protocol.runChecked f n (start + 1) x >>= f (start + (n + 1))
      rw [ih, show start + 1 + n = start + (n + 1) by omega]

theorem checked_add_some (x y : Usize) (h : x.val + y.val ≤ Usize.max) :
    ∃ z, Usize.checked_add x y = some z ∧ z.val = x.val + y.val := by
  have hs := Usize.checked_add_bv_spec x y
  cases hc : Usize.checked_add x y with
  | none => simp only [hc] at hs; omega
  | some z => simp only [hc] at hs; exact ⟨z, rfl, hs.2.1⟩

theorem checked_sub_some (x y : Usize) (h : y.val ≤ x.val) :
    ∃ z, Usize.checked_sub x y = some z ∧ z.val = x.val - y.val := by
  have hs := Usize.checked_sub_bv_spec x y
  cases hc : Usize.checked_sub x y with
  | none => simp only [hc] at hs; omega
  | some z => simp only [hc] at hs; exact ⟨z, rfl, hs.2.1⟩

section ConfigFacts
variable {config : whir.config.Config} {c : Protocol.Config} {log_n : Usize} (hcfg : ConfigRel config c log_n)
include hcfg

theorem ConfigRel.folds_size : c.folds.size = config.level_ks.val.length + 1 := by
  rw [← Array.length_toList, hcfg.folds]; simp

theorem ConfigRel.fold0 : c.folds[0]! = config.initial_k.val := by
  rw [arr_get _ _ hcfg.folds]; simp

theorem ConfigRel.foldk (j : Nat) (hj : j < config.level_ks.val.length) :
    c.folds[j + 1]! = (config.level_ks.val[j]).val := by
  rw [arr_get _ _ hcfg.folds]; simp [getElem!_pos, hj]

theorem ConfigRel.rate (j : Nat) (hj : j < config.log_inv_rates.val.length) :
    c.rates[j]! = (config.log_inv_rates.val[j]).val := by
  rw [arr_get _ _ hcfg.rates]; simp [getElem!_pos, hj]

theorem ConfigRel.query (j : Nat) (hj : j < config.queries.val.length) :
    c.queries[j]! = (config.queries.val[j]).val := by
  rw [arr_get _ _ hcfg.queries]; simp [getElem!_pos, hj]

theorem ConfigRel.ood (j : Nat) (hj : j < config.ood_samples.val.length) :
    c.oodCounts[j]! = (config.ood_samples.val[j]).val := by
  rw [arr_get _ _ hcfg.oods]; simp [getElem!_pos, hj]

theorem ConfigRel.lengths (hv : c.valid = true) :
    config.log_inv_rates.val.length = c.folds.size ∧ config.queries.val.length = c.folds.size ∧
      config.ood_samples.val.length = c.folds.size := by
  have h := WHIRNativeGuards.config_header c hv
  have hr : c.rates.toList.length = _ := congrArg List.length hcfg.rates
  have hq : c.queries.toList.length = _ := congrArg List.length hcfg.queries
  have ho : c.oodCounts.toList.length = _ := congrArg List.length hcfg.oods
  simp only [Array.length_toList, List.length_map] at hr hq ho
  omega

omit hcfg in
theorem deref_length {α : Type} (v : alloc.vec.Vec α) : (alloc.vec.Vec.deref v).length = v.val.length := by
  simp only [alloc.vec.Vec.deref, Slice.length, Slice.from_val]

theorem ConfigRel.lengths' (hv : c.valid = true) :
    config.grinding_bits.val.length = c.folds.size := hcfg.grinding_len

theorem check_shape_loop (hv : c.valid = true) (bits : Usize) (hbits : bits.val = 64) :
    ∀ (m : Nat) (level remaining : Usize), config.level_ks.val.length - level.val = m →
      level.val ≤ config.level_ks.val.length → remaining.val = CausalGame.remaining c level.val →
      whir.verify.check_config_shape_loop config bits remaining level (.Ok ()) = .ok (.Ok ()) := by
  have hsz := hcfg.folds_size
  obtain ⟨hrl, -, -⟩ := hcfg.lengths hv
  intro m
  induction m with
  | zero =>
    intro level remaining hm hl hr
    unfold whir.verify.check_config_shape_loop
    apply loop_done
    have : ¬ (level < Slice.len (alloc.vec.Vec.deref config.level_ks)) := by
      simp only [UScalar.lt_equiv, Slice.len_val, deref_length]; omega
    simp only [whir.verify.check_config_shape_loop.body, whir.config.Config.impl.level_ks, Std.bind_ok, this,
      ↓reduceIte]
  | succ m ih =>
    intro level remaining hm hl hr
    have hlt : level.val < config.level_ks.val.length := by omega
    have hcl := WHIRNativeGuards.config_level c hv (level.val + 1) (by omega)
    obtain ⟨_, hkb, hrate, _, h64⟩ := hcl
    have hk : c.folds[level.val + 1]! = (config.level_ks.val[level.val]).val := hcfg.foldk level.val hlt
    have hk62 : (config.level_ks.val[level.val]).val < 62 := hcfg.ks _ (List.getElem_mem hlt)
    have hbefore : WHIRNativeGuards.before c (level.val + 1) = CausalGame.remaining c level.val := rfl
    have hstep := WHIRNativeGuards.before_step c (level.val + 1) (by omega)
    have hrate' : c.rates[level.val + 1]! = (config.log_inv_rates.val[level.val + 1]).val :=
      hcfg.rate (level.val + 1) (by omega)
    obtain ⟨nxt, hsub, enxt⟩ := checked_sub_some remaining config.level_ks.val[level.val] (by omega)
    have hsum : nxt.val + (config.log_inv_rates.val[level.val + 1]).val < 64 := by
      rw [enxt, hr, ← hbefore, ← hk, hstep, ← hrate']; exact h64
    obtain ⟨sm, hadd, esm⟩ := checked_add_some nxt config.log_inv_rates.val[level.val + 1] (by scalar_tac)
    have hsucc := succ_val level config.level_ks.val.length hlt (by have := config.level_ks.property; scalar_tac)
    have hi1 : (Std.Usize.wrapping_sub bits 2#usize).val = 62 := by rw [Fold.sub_val _ _ (by simp [hbits])]; simp [hbits]
    have hrl1 : (Std.Usize.wrapping_add level 1#usize).val < config.log_inv_rates.val.length := by
      rw [hsucc]; omega
    have hbody : whir.verify.check_config_shape_loop.body config bits remaining level (.Ok ()) =
        .ok (.cont (nxt, Std.Usize.wrapping_add level 1#usize, .Ok ())) := by
      have hlt' : level < Slice.len (alloc.vec.Vec.deref config.level_ks) := by
        simp only [UScalar.lt_equiv, Slice.len_val, deref_length]; exact hlt
      have hge : ¬ (Std.Usize.wrapping_sub bits 2#usize ≤ config.level_ks.val[level.val]) := by
        simp only [UScalar.le_equiv, hi1]; omega
      have hcl1 : whir.verify.check_config_shape.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeBool.call_once
          bits sm = .ok true := by
        simp only [whir.verify.check_config_shape.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeBool.call_once]
        have h0 : sm > 0#usize := by simp only [gt_iff_lt, UScalar.lt_equiv, esm]; simp; omega
        have h1 : sm < bits := by simp only [UScalar.lt_equiv, esm, hbits]; omega
        simp [h0, h1]
      have hidx : Slice.index_usize (alloc.vec.Vec.deref config.level_ks) level = .ok config.level_ks.val[level.val] := by
        rw [slice_index _ level (by simp only [alloc.vec.Vec.deref, Slice.from_val]; exact hlt)]
        simp [alloc.vec.Vec.deref]
      have hidx2 : Slice.index_usize (alloc.vec.Vec.deref config.log_inv_rates) (Std.Usize.wrapping_add level 1#usize) =
          .ok config.log_inv_rates.val[(Std.Usize.wrapping_add level 1#usize).val] := by
        rw [slice_index _ _ (by simp only [alloc.vec.Vec.deref, Slice.from_val]; exact hrl1)]
        simp [alloc.vec.Vec.deref]
      have hadd' : Usize.checked_add nxt config.log_inv_rates.val[(Std.Usize.wrapping_add level 1#usize).val] = some sm := by
        simp only [hsucc]; exact hadd
      simp only [whir.verify.check_config_shape_loop.body, whir.config.Config.impl.level_ks, Std.bind_ok, hlt',
        ↓reduceIte, core.result.Result.is_ok, hidx, lift, ge_iff_le, hge, hsub,
        whir.config.Config.impl.log_inv_rates, hidx2, hadd', core.option.Option.is_some_and,
        whir.verify.check_config_shape.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeBool, hcl1]
      simp
    unfold whir.verify.check_config_shape_loop
    rw [loop_cont hbody]
    exact ih _ _ (by omega) (by omega) (by rw [hsucc, enxt, hr, ← hbefore, ← hk, hstep])

omit hcfg in
theorem bits_val (hw : System.Platform.numBits = 64) :
    (UScalar.cast .Usize core.num.Usize.BITS : Usize).val = 64 := by
  rw [UScalar.cast_val_eq]
  have h1 : core.num.Usize.BITS.val = UScalarTy.Usize.numBits := by
    simp [core.num.Usize.BITS]
  rw [h1]
  simp [hw]

/-- `check_config_shape` accepts a valid model configuration whose witness has fewer than 64
variables and whose level folds are below 62. -/
theorem check_config_shape_ok (hw : System.Platform.numBits = 64) (hv : c.valid = true) :
    whir.verify.check_config_shape config log_n = .ok (.Ok ()) := by
  have hsz := hcfg.folds_size
  obtain ⟨hrl, -, -⟩ := hcfg.lengths hv
  have hb := bits_val hw
  have h0 := WHIRNativeGuards.config_level c hv 0 (by omega)
  obtain ⟨_, hk0, hr0, _, h64⟩ := h0
  have hf0 := hcfg.fold0
  have hlog := hcfg.logN
  have hbefore0 : WHIRNativeGuards.before c 0 = c.logN := by simp [WHIRNativeGuards.before]
  have hstep0 := WHIRNativeGuards.before_step c 0 (by omega)
  have hrate0 : c.rates[0]! = (config.log_inv_rates.val[0]'(by omega)).val := hcfg.rate 0 (by omega)
  have hrem : (Std.Usize.wrapping_sub log_n config.initial_k).val = CausalGame.remaining c 0 := by
    rw [Fold.sub_val _ _ (by omega), ← hstep0, hbefore0, hf0, hlog]
  obtain ⟨sm, hadd, esm⟩ := checked_add_some (Std.Usize.wrapping_sub log_n config.initial_k)
    (config.log_inv_rates.val[0]'(by omega)) (by
      have : (Std.Usize.wrapping_sub log_n config.initial_k).val + (config.log_inv_rates.val[0]'(by omega)).val < 64 := by
        rw [hrem, ← hrate0]; exact h64
      scalar_tac)
  have hidx : Slice.index_usize (alloc.vec.Vec.deref config.log_inv_rates) 0#usize =
      .ok (config.log_inv_rates.val[0]'(by omega)) := by
    rw [slice_index _ _ (by simp only [alloc.vec.Vec.deref, Slice.from_val]; simp; omega)]
    simp [alloc.vec.Vec.deref]
  have hge : ¬ (UScalar.cast .Usize core.num.Usize.BITS ≤ log_n) := by
    simp only [UScalar.le_equiv, hb]; have := hcfg.log64; omega
  have hle : ¬ (log_n ≤ config.initial_k) := by
    simp only [UScalar.le_equiv]; rw [← hf0, ← hlog, ← hbefore0]; omega
  have hcl : whir.verify.check_config_shape.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeBool.call_once
      (UScalar.cast .Usize core.num.Usize.BITS) sm = .ok true := by
    simp only [whir.verify.check_config_shape.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeBool.call_once]
    have : sm < UScalar.cast .Usize core.num.Usize.BITS := by
      simp only [UScalar.lt_equiv, esm, hb, hrem]; rw [← hrate0]; omega
    simp [this]
  have hloop := check_shape_loop hcfg hv _ hb _ 0#usize (Std.Usize.wrapping_sub log_n config.initial_k) rfl
    (by simp) (by simpa using hrem)
  simp only [whir.verify.check_config_shape, lift, Std.bind_ok, whir.config.Config.impl.initial_k, ge_iff_le, hge,
    ↓reduceIte, hle, whir.config.Config.impl.log_inv_rates, hidx, hadd, core.option.Option.is_some_and,
    whir.verify.check_config_shape.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeBool, hcl, hloop]

end ConfigFacts

/-! ## The transcript's answers as the model's challenges and opening -/

section Script
open AccumulatedTerminalRefinement WHIRNativeArithmetic

/-- One level's answers, as source values: the fold rounds `(r, u0, u2)`, the next oracle's
root or (at the last level) the residual polynomial, the out-of-domain claims
`(z, y, u0, u2)`, the batch's proof-of-work bits, the query positions and the model's squeezes
behind them, the batch challenge, the arguments the replay passes to the rows read (the level
oracle's root and depth, the row and leaf widths in words), the opened rows and the batch's
intro round. -/
structure SLevel (E Q R K : Type) where
  folds : List (E × E × E)
  head : R ⊕ List E
  oods : List (List E × E × E × E)
  bits : Nat
  squeezes : Array Concrete.E
  queries : List Q
  lambda : E
  root : R
  depth : Nat
  rowWords : Nat
  leafWords : Nat
  rows : List (List K)
  intro : E × E

structure Script (E Q R K : Type) where
  initial : E × E
  levels : List (SLevel E Q R K)
  tail : List E
  tailMsgs : List (E × E)

variable {V R K Q E : Type}

def headTape : R ⊕ List E → List (Event E Q R K)
  | .inl r => [.root r]
  | .inr ys => [.scalars ys]

def batchTape (l : SLevel E Q R K) : List (Event E Q R K) :=
  [.grind l.bits, .queries l.depth l.queries, .sample l.lambda, .rows l.root l.depth l.queries l.rowWords l.leafWords l.rows,
    .poly l.intro.1 l.intro.2]

def levelTape (l : SLevel E Q R K) : List (Event E Q R K) :=
  foldTape l.folds ++ (headTape l.head ++ (oodTape l.oods ++ batchTape l))

/-- The replay's reads, in order. -/
def Script.tape (s : Script E Q R K) : List (Event E Q R K) :=
  .poly s.initial.1 s.initial.2 :: (s.levels.flatMap levelTape ++ tailTape s.tail s.tailMsgs)

def residualOf : R ⊕ List E → List E
  | .inl _ => []
  | .inr ys => ys

variable (encode : E → Concrete.E) (encodeK : K → Concrete.K)
  (ofLimbs : Concrete.K → Concrete.K → Concrete.K → Concrete.E) (index : Q → Nat)

def SLevel.chal (l : SLevel E Q R K) : Protocol.LevelChallenges :=
  ⟨(l.folds.map fun x => encode x.1).toArray, (l.oods.map fun o => (o.1.map encode).toArray).toArray,
    l.squeezes, encode l.lambda⟩

/-- A level's proof: level 0 rows are words read as base elements, later rows are elements
of three words each. The next oracle is only a presence marker in the native verifier. -/
def SLevel.prf (base : Bool) (l : SLevel E Q R K) : Protocol.LevelProof :=
  ⟨(l.folds.map fun x => (⟨encode x.2.1, encode x.2.2⟩ : Protocol.Message Concrete.E)).toArray,
    (match l.head with | .inl _ => some #[] | .inr _ => none),
    (l.oods.map fun o => (⟨encode o.2.1, ⟨encode o.2.2.1, encode o.2.2.2⟩⟩ : Protocol.OodClaim)).toArray,
    (if base then l.rows.map (fun w => (w.map fun k => Concrete.E.ofK (encodeK k)).toArray)
      else l.rows.map fun w => (eRow encodeK ofLimbs w).toArray).toArray,
    ⟨encode l.intro.1, encode l.intro.2⟩⟩

/-- The model's challenges the transcript answered. -/
def Script.chal (s : Script E Q R K) : Protocol.Challenges :=
  ⟨(s.levels.map (SLevel.chal encode)).toArray, (s.tail.map encode).toArray⟩

/-- The model's opening the transcript answered. -/
def Script.prf (s : Script E Q R K) : Protocol.Opening :=
  ⟨⟨encode s.initial.1, encode s.initial.2⟩,
    (s.levels.mapIdx fun i l => SLevel.prf encode encodeK ofLimbs (i == 0) l).toArray,
    (((s.levels.getLast?.map fun l => residualOf l.head).getD []).map encode).toArray,
    (s.tailMsgs.map fun m => (⟨encode m.1, encode m.2⟩ : Protocol.Message Concrete.E)).toArray⟩

/-- The shapes the opening must have for the source's fixed read schedule: every level but
the last carries the next level's root, the last the residual of the remaining cube; query
positions are derived from the squeezes; one row per query of the committed width; one
round polynomial per residual round but the last; the source keeps all out-of-domain
contexts in one vector, so their total count is below `usize::MAX`. The rows read gets the
level's depth, and at level 0 the lane count and the lane fold's leaf width, at later levels
the interleaved row of three words per element as both widths. -/
structure ScriptShape (c : Protocol.Config) (s : Script E Q R K) (lanes : Nat) : Prop where
  len : s.levels.length = c.folds.size
  roots : ∀ i (hi : i + 1 < s.levels.length), (s.levels[i]'(by omega)).head = .inl (s.levels[i + 1]'hi).root
  last : ∀ (hl : 0 < s.levels.length), ∃ ys, (s.levels[s.levels.length - 1]'(by omega)).head = .inr ys ∧
    ys.length = 2 ^ CausalGame.remaining c (c.folds.size - 1)
  queries : ∀ i (hi : i < s.levels.length),
    (deriveQueries (CausalGame.remaining c i + c.rates[i]!) c.queries[i]! s.levels[i].squeezes).map
      Array.toList = some (s.levels[i].queries.map index)
  depth : ∀ i (hi : i < s.levels.length), s.levels[i].depth = CausalGame.remaining c i + c.rates[i]!
  rows : ∀ i (hi : i < s.levels.length), s.levels[i].rows.length = s.levels[i].queries.length
  base : ∀ (hl : 0 < s.levels.length), ∀ w ∈ (s.levels[0]'hl).rows, w.length = lanes
  baseWords : ∀ (hl : 0 < s.levels.length),
    (s.levels[0]'hl).rowWords = lanes ∧ (s.levels[0]'hl).leafWords = 2 ^ c.folds[0]!
  ext : ∀ i (hi : i < s.levels.length), 0 < i → ∀ w ∈ s.levels[i].rows, w.length = 3 * 2 ^ c.folds[i]!
  extWords : ∀ i (hi : i < s.levels.length), 0 < i →
    s.levels[i].rowWords = 3 * 2 ^ c.folds[i]! ∧ s.levels[i].leafWords = 3 * 2 ^ c.folds[i]!
  tail : s.tailMsgs.length + 1 = s.tail.length
  small : (s.levels.map fun l => l.oods.length).sum < Usize.max

/-- Every level but the last carries a root. -/
theorem ScriptShape.head {idx : Q → Nat} {c : Protocol.Config} {s : Script E Q R K} {lanes : Nat}
    (hS : ScriptShape idx c s lanes) (i : Nat) (hi : i + 1 < s.levels.length) :
    ∃ r, (s.levels[i]'(by omega)).head = .inl r :=
  ⟨_, hS.roots i hi⟩

theorem chal_get (s : Script E Q R K) (j : Nat) (hj : j < s.levels.length) :
    (s.chal encode).levels[j]! = s.levels[j].chal encode := by
  simp [Script.chal, getElem!_pos, hj]

theorem prf_get (s : Script E Q R K) (j : Nat) (hj : j < s.levels.length) :
    (s.prf encode encodeK ofLimbs).levels[j]! = s.levels[j].prf encode encodeK ofLimbs (j == 0) := by
  simp [Script.prf, getElem!_pos, hj]

theorem deriveQueries_size (d n : Nat) (sq : Array Concrete.E) (qs : Array Nat)
    (h : deriveQueries d n sq = some qs) : qs.size = n := by
  unfold deriveQueries at h
  split_ifs at h <;> simp at h
  rw [← h.2]; simp [tab]

/-- What the challenge validator and the shape premise give at one level. -/
theorem level_facts (c : Protocol.Config) (s : Script E Q R K) (lanes : Nat)
    (hc : (s.chal encode).valid c = true) (hS : ScriptShape index c s lanes) (j : Nat) (hj : j < c.folds.size) :
    (s.levels[j]'(by rw [hS.len]; exact hj)).folds.length = c.folds[j]! ∧
    (s.levels[j]'(by rw [hS.len]; exact hj)).oods.length = CausalGame.oodCount c j ∧
    (∀ o ∈ (s.levels[j]'(by rw [hS.len]; exact hj)).oods, o.1.length = CausalGame.remaining c j) ∧
    ∃ qsA, deriveQueries (CausalGame.remaining c j + c.rates[j]!) c.queries[j]!
        (s.levels[j]'(by rw [hS.len]; exact hj)).squeezes = some qsA ∧
      qsA.toList = (s.levels[j]'(by rw [hS.len]; exact hj)).queries.map index ∧
      (s.levels[j]'(by rw [hS.len]; exact hj)).queries.length = c.queries[j]! := by
  have hjl : j < s.levels.length := by rw [hS.len]; exact hj
  have hf := WHIRNativeGuards.challenges_folds c _ hc j hj
  have ho := WHIRNativeGuards.challenges_ood_count c _ hc j hj
  have hp := WHIRNativeGuards.challenges_ood_point c _ hc j hj
  rw [chal_get encode s j hjl] at hf ho hp
  simp only [SLevel.chal, List.size_toArray, List.length_map] at hf ho
  refine ⟨hf, ho, fun o ho' => ?_, ?_⟩
  · have := hp (o.1.map encode).toArray (by
      rw [SLevel.chal]; exact List.mem_toArray.mpr (List.mem_map.mpr ⟨o, ho', rfl⟩))
    simpa using this
  · have hq := hS.queries j hjl
    cases hd : deriveQueries (CausalGame.remaining c j + c.rates[j]!) c.queries[j]! s.levels[j].squeezes with
    | none => simp [hd] at hq
    | some qsA =>
      simp only [hd, Option.map_some, Option.some.injEq] at hq
      refine ⟨qsA, rfl, hq, ?_⟩
      have := deriveQueries_size _ _ _ _ hd
      have h1 := congrArg List.length hq
      simp only [Array.length_toList, List.length_map] at h1
      omega

end Script

end WhirAeneas.Replay
