import WhirAeneas.MerkleRows
import WhirAeneas.Sampling

/-! The native transcript reads. The generated `VerifierState` answers the replay's reads by
reading prover messages off the NARG string (`FromNarg`: an `F192` is 24 little-endian bytes, a
root 32 raw bytes, a nonce 8 little-endian bytes; each read consumes exactly its bytes and
absorbs them), drawing verifier messages from the BLAKE2s duplex (`FromUniform`), checking proof
of work (`ProofOfWork::verify`) and sampling query positions through the same draws. The duplex
and the proof-of-work hash are opaque, with content contracts: `Duplex` (an absorb extends the
logical transcript by its bytes, a squeeze returns the duplex's output for the transcript so
far) and `PowHash`. `Answers` states what a proof must hold for the native state to answer a list
of events: the draws are the duplex's outputs, the prover messages are the proof's bytes, each
proof of work clears its bits, and each rows event is the next length-prefixed hint, opening
its rows. -/
namespace WhirAeneas.NativeReads
open Aeneas Aeneas.Std ReplaySource WhirAeneas.Merkle WhirAeneas.MerkleNative WhirAeneas.Replay

/-- The native element. -/
abbrev F192 := primitives.field.gf2_64x3.F192

/-! ## Contracts of the opaque duplex and proof-of-work hash -/

/-- One step of the duplex's logical transcript: bytes absorbed, or a number of bytes squeezed. -/
inductive DOp where
  | absorb (bytes : List U8)
  | squeeze (n : Nat)

/-- Bytes one squeeze run may take (`MAX_SQUEEZE`). -/
def maxSqueeze : Nat := 2 ^ 49 - 1

/-- The bytes squeezed since the last nonempty absorb, read from the end. -/
def runRev : List DOp → Nat
  | [] => 0
  | .squeeze n :: t => n + runRev t
  | .absorb [] :: t => runRev t
  | .absorb (_ :: _) :: _ => 0

/-- The current squeeze run of a transcript. -/
def runOf (h : List DOp) : Nat := runRev h.reverse

/-- The content contract of the opaque BLAKE2s duplex. `R s h` says the sponge `s` holds the
logical transcript `h`, and `out h n` is the `n` bytes the duplex squeezes after `h`: an absorb
extends the transcript by its bytes, and a squeeze within the run budget returns `out` of the
transcript so far and extends it by its length. -/
structure Duplex (out : List DOp → Nat → List U8)
    (R : fiat_shamir.duplex.Blake2sDuplex → List DOp → Prop) : Prop where
  out_length : ∀ h n, (out h n).length = n
  absorb : ∀ s h (b : Slice U8), R s h →
    ∃ s', fiat_shamir.duplex.Blake2sDuplex.absorb s b = .ok s' ∧ R s' (h ++ [.absorb b.val])
  squeeze : ∀ s h (o : Slice U8), R s h → runOf h + o.val.length ≤ maxSqueeze →
    ∃ s' o', fiat_shamir.duplex.Blake2sDuplex.squeeze s o = .ok (s', o') ∧
      o'.val = out h o.val.length ∧ R s' (h ++ [.squeeze o.val.length])

/-- The content contract of the opaque one-block hash: `H` of the input bytes (BLAKE2s-256). -/
def PowHash (H : List U8 → Merkle.Digest) : Prop :=
  ∀ s : Slice U8, primitives.hash.hash s = .ok (H s.val)

/-! ## Decoding -/

/-- The little-endian word of the first eight bytes (padded with zeros). -/
def u64Of (bs : List U8) : U64 :=
  core.num.U64.from_le_bytes (Aeneas.Std.Array.make 8#usize ((bs ++ List.replicate 8 0#u8).take 8) (by simp))

/-- The element of the first 24 bytes: three little-endian limbs, lowest first. -/
def f192Of (bs : List U8) : F192 :=
  { c0 := u64Of bs, c1 := u64Of (bs.drop 8), c2 := u64Of (bs.drop 16) }

/-- `n` elements read off `bs`, 24 bytes each. -/
def readsE : List U8 → Nat → List F192
  | _, 0 => []
  | bs, n + 1 => f192Of bs :: readsE (bs.drop 24) n

/-- The transcript steps of reading `n` elements off `bs`: each absorbs its 24 bytes. -/
def absorbsE : List U8 → Nat → List DOp
  | _, 0 => []
  | bs, n + 1 => .absorb (bs.take 24) :: absorbsE (bs.drop 24) n

/-- `n` squeezes of 24 bytes. -/
def sqs (n : Nat) : List DOp := List.replicate n (.squeeze 24)

/-- `n` elements drawn from the duplex after `h`. -/
def draws (out : List DOp → Nat → List U8) : List DOp → Nat → List F192
  | _, 0 => []
  | h, n + 1 => f192Of (out h 24) :: draws out (h ++ [.squeeze 24]) n

/-- The proof-of-work trial block: challenge, little-endian nonce, sixteen zeros, the tag. -/
def powBlock (challenge nonce : List U8) : List U8 :=
  challenge ++ nonce ++ List.replicate 16 0#u8 ++ (core.num.U64.to_le_bytes fiat_shamir.pow.ProofOfWork.TRIAL_TAG).val

/-- A nonce clears `bits` of work on `challenge`: the first word of its trial's hash, little-endian,
has at least `bits` leading zeros. -/
def Works (H : List U8 → Merkle.Digest) (challenge : List U8) (nonce : U64) (bits : Nat) : Prop :=
  bits ≤ (core.num.U64.leading_zeros (u64Of (H (powBlock challenge (core.num.U64.to_le_bytes nonce).val)).val)).val

/-! ## The generated decoders -/

theorem take_some (N : Usize) (narg : Slice U8) (h : N.val ≤ narg.val.length) :
    ∃ a rest, fiat_shamir.codec.take N narg = .ok (some a, rest) ∧ a.val = narg.val.take N.val ∧
      rest.val = narg.val.drop N.val := by
  refine ⟨Aeneas.Std.Array.make N (narg.val.take N.val) (by simp; omega),
    Slice.from (narg.val.drop N.val) (by have := narg.property; simp; omega), ?_, by simp, by simp⟩
  simp [fiat_shamir.codec.take, core.slice.Slice.split_first_chunk, h,
    core.option.Option.Insts.CoreOpsTry_traitTry.branch]

theorem take_none (N : Usize) (narg : Slice U8) (h : narg.val.length < N.val) :
    fiat_shamir.codec.take N narg = .ok (none, narg) := by
  simp [fiat_shamir.codec.take, core.slice.Slice.split_first_chunk, show ¬ N.val ≤ narg.val.length by omega,
    core.option.Option.Insts.CoreOpsTry_traitTry.branch,
    core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual]

theorem u64Of_eq (a : Aeneas.Std.Array U8 8#usize) : core.num.U64.from_le_bytes a = u64Of a.val := by
  unfold u64Of
  congr 1
  rw [Aeneas.Std.Array.eq_iff]
  simp

theorem u64Of_take (l : List U8) : u64Of (l.take 8) = u64Of l := by
  unfold u64Of
  congr 2
  simp only [List.take_append, List.take_take, List.length_take]
  congr 2
  omega

theorem usize_ofNat_val (k : Nat) (hk : k < 2 ^ 32) :
    (⟨BitVec.ofNat System.Platform.numBits k⟩ : Usize).val = k := by
  show (BitVec.ofNat System.Platform.numBits k).toNat = k
  rw [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have : 2 ^ 32 ≤ 2 ^ System.Platform.numBits := by
    apply Nat.pow_le_pow_right (by omega)
    rcases System.Platform.numBits_eq with h | h <;> simp [h]
  omega

theorem chunks_cons {T : Type} (N : Usize) (l : List T) (h : 0 < N.val ∧ N.val ≤ l.length) :
    core.slice.Slice.as_chunks.chunks N l =
      Aeneas.Std.Array.make N (l.take N.val) (by simp; omega) :: core.slice.Slice.as_chunks.chunks N (l.drop N.val) := by
  rw [core.slice.Slice.as_chunks.chunks]; simp only [h, and_self, ↓reduceDIte]

theorem chunks_nil {T : Type} (N : Usize) (l : List T) (h : l.length < N.val) :
    core.slice.Slice.as_chunks.chunks N l = [] := by
  rw [core.slice.Slice.as_chunks.chunks]; simp only [show ¬ (0 < N.val ∧ N.val ≤ l.length) by omega, ↓reduceDIte]

theorem chunks_24 (l : List U8) (hl : l.length = 24) :
    (core.slice.Slice.as_chunks.chunks 8#usize l).map (·.val) = [l.take 8, (l.drop 8).take 8, (l.drop 16).take 8] := by
  rw [chunks_cons _ _ (by simp; omega), chunks_cons _ _ (by simp; omega), chunks_cons _ _ (by simp; omega),
    chunks_nil _ _ (by simp; omega)]
  simp [List.drop_drop]

/-- `F192::from_le_bytes`: three little-endian limbs, lowest first. -/
theorem from_le_bytes_eq (bytes : Aeneas.Std.Array U8 24#usize) :
    primitives.field.gf2_64x3.F192.from_le_bytes bytes = .ok (f192Of bytes.val) := by
  have hl : bytes.val.length = 24 := by simp
  have hc := chunks_24 bytes.val hl
  obtain ⟨A0, A1, A2, hcs⟩ : ∃ A0 A1 A2, core.slice.Slice.as_chunks.chunks 8#usize bytes.val = [A0, A1, A2] := by
    have hlen := congrArg List.length hc
    simp only [List.length_map, List.length_cons, List.length_nil] at hlen
    match hm : core.slice.Slice.as_chunks.chunks 8#usize bytes.val, hlen with
    | [A0, A1, A2], _ => exact ⟨A0, A1, A2, rfl⟩
  rw [hcs] at hc
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at hc
  obtain ⟨h0, h1, h2, -⟩ := hc
  have hs : (Aeneas.Std.Array.to_slice bytes).val = bytes.val := by simp [Aeneas.Std.Array.to_slice]
  have h3 : (3 : Nat) ≤ Usize.max := by scalar_tac
  have e0 : core.num.U64.from_le_bytes A0 = u64Of bytes.val := by rw [u64Of_eq, h0, u64Of_take]
  have e1 : core.num.U64.from_le_bytes A1 = u64Of (bytes.val.drop 8) := by rw [u64Of_eq, h1, u64Of_take]
  have e2 : core.num.U64.from_le_bytes A2 = u64Of (bytes.val.drop 16) := by rw [u64Of_eq, h2, u64Of_take]
  simp [primitives.field.gf2_64x3.F192.from_le_bytes, core.slice.Slice.as_chunks, hs, hcs, lift, h3,
    Slice.index_usize, Slice.from_val, e0, e1, e2, primitives.field.gf2_64x3.F192.new, f192Of]

theorem f192Of_take (l : List U8) : f192Of (l.take 24) = f192Of l := by
  have e1 : u64Of ((l.take 24).drop 8) = u64Of (l.drop 8) := by
    rw [← u64Of_take, List.drop_take, List.take_take, ← u64Of_take (l.drop 8)]; simp
  have e2 : u64Of ((l.take 24).drop 16) = u64Of (l.drop 16) := by
    rw [← u64Of_take, List.drop_take, List.take_take, ← u64Of_take (l.drop 16)]; simp
  have e0 : u64Of (l.take 24) = u64Of l := by
    rw [← u64Of_take, List.take_take, ← u64Of_take l]; simp
  simp only [f192Of, e0, e1, e2]

theorem from_uniform_eq (repr : Aeneas.Std.Array U8 24#usize) :
    primitives.field.gf2_64x3.F192.Insts.Fiat_shamirCodecFromUniformArrayU824.from_uniform repr =
      .ok (f192Of repr.val) := by
  simp [primitives.field.gf2_64x3.F192.Insts.Fiat_shamirCodecFromUniformArrayU824.from_uniform,
    from_le_bytes_eq]

theorem from_narg_f192 (narg : Slice U8) (h : 24 ≤ narg.val.length) :
    ∃ rest, primitives.field.gf2_64x3.F192.Insts.Fiat_shamirCodecFromNargArrayU824.from_narg narg =
      .ok (some (f192Of narg.val), rest) ∧ rest.val = narg.val.drop 24 := by
  obtain ⟨a, rest, ht, ea, er⟩ := take_some 24#usize narg (by simpa using h)
  refine ⟨rest, ?_, by simpa using er⟩
  have hf : f192Of a.val = f192Of narg.val := by rw [ea]; simpa using f192Of_take narg.val
  rw [← hf]
  simp [primitives.field.gf2_64x3.F192.Insts.Fiat_shamirCodecFromNargArrayU824.from_narg, ht, core.option.Option.map,
    fiat_shamir.codec.FromNargF192ArrayU824.from_narg.closure.Insts.CoreOpsFunctionFnOnceTupleShared0ArrayU824F192,
    fiat_shamir.codec.FromNargF192ArrayU824.from_narg.closure.Insts.CoreOpsFunctionFnOnceTupleShared0ArrayU824F192.call_once,
    from_le_bytes_eq]

theorem from_narg_digest (narg : Slice U8) (h : 32 ≤ narg.val.length) :
    ∃ (a : Aeneas.Std.Array U8 32#usize) (rest : Slice U8), ArrayU8N.Insts.Fiat_shamirCodecFromNargArrayU8N.from_narg 32#usize narg =
      .ok (some a, rest) ∧ a.val = narg.val.take 32 ∧ rest.val = narg.val.drop 32 := by
  obtain ⟨a, rest, ht, ea, er⟩ := take_some 32#usize narg (by simpa using h)
  refine ⟨a, rest, ?_, by simpa using ea, by simpa using er⟩
  simp [ArrayU8N.Insts.Fiat_shamirCodecFromNargArrayU8N.from_narg, ht, core.option.OptionShared0T.copied]

theorem from_narg_u64 (narg : Slice U8) (h : 8 ≤ narg.val.length) :
    ∃ rest, U64.Insts.Fiat_shamirCodecFromNargArrayU88.from_narg narg =
      .ok (some (u64Of narg.val), rest) ∧ rest.val = narg.val.drop 8 := by
  obtain ⟨a, rest, ht, ea, er⟩ := take_some 8#usize narg (by simpa using h)
  refine ⟨rest, ?_, by simpa using er⟩
  have hu : u64Of narg.val = core.num.U64.from_le_bytes a := by
    rw [u64Of_eq, ea, ← u64Of_take]; simp
  rw [hu]
  simp [U64.Insts.Fiat_shamirCodecFromNargArrayU88.from_narg, ht, core.option.Option.map,
    fiat_shamir.codec.FromNargU64ArrayU88.from_narg.closure.Insts.CoreOpsFunctionFnOnceTupleShared0ArrayU88U64,
    fiat_shamir.codec.FromNargU64ArrayU88.from_narg.closure.Insts.CoreOpsFunctionFnOnceTupleShared0ArrayU88U64.call_once]

theorem index_to (s : Slice U8) (e : Usize) (he : e.val ≤ s.val.length) :
    core.slice.index.SliceIndexRangeToUsizeSlice.index { «end» := e } s =
      .ok (Slice.from (s.val.take e.val) (by have := s.property; simp only [List.length_take]; omega)) := by
  have he' : e ≤ s.length := by simpa using he
  simp [core.slice.index.SliceIndexRangeToUsizeSlice.index, he', List.slice]

/-! ## Reads of the generated `VerifierState` -/

section State
variable {out : List DOp → Nat → List U8} {R : fiat_shamir.duplex.Blake2sDuplex → List DOp → Prop}

/-- A prover message whose decoder takes the first `k` bytes: the value, with those bytes
consumed and absorbed. -/
theorem prover_message_ok (hD : Duplex out R) {T B : Type} (inst : fiat_shamir.codec.FromNarg T B) (v : VS)
    (hp : v.poison = none) (x : T) (cursor : Slice U8) (k : Nat) (hk : k ≤ v.narg.val.length)
    (hfrom : inst.from_narg v.narg = .ok (some x, cursor)) (hc : cursor.val = v.narg.val.drop k)
    (h : List DOp) (hR : R v.sponge h) :
    ∃ v', fiat_shamir.verifier.VerifierState.prover_message inst v = .ok (.Ok x, v') ∧
      v'.poison = none ∧ v'.narg.val = v.narg.val.drop k ∧ v'.hints = v.hints ∧
      R v'.sponge (h ++ [.absorb (v.narg.val.take k)]) := by
  have hsub : (Std.Usize.wrapping_sub (Slice.len v.narg) (Slice.len cursor)).val = k := by
    rw [Fold.sub_val _ _ (by simp [hc])]; simp [hc]; omega
  have hidx : core.slice.index.SliceIndexRangeToUsizeSlice.index
      { «end» := Std.Usize.wrapping_sub (Slice.len v.narg) (Slice.len cursor) } v.narg =
      .ok (Slice.from (v.narg.val.take k) (by have := v.narg.property; simp only [List.length_take]; omega)) := by
    rw [index_to _ _ (by rw [hsub]; exact hk)]
    congr 1; apply Slice.ext; simp [hsub]
  obtain ⟨s', habs, hR'⟩ := hD.absorb v.sponge h (Slice.from (v.narg.val.take k) (by
      have := v.narg.property; simp only [List.length_take]; omega)) hR
  refine ⟨{ v with sponge := s', narg := cursor, messages_read := Std.Usize.wrapping_add v.messages_read 1#usize },
    ?_, hp, hc, rfl, by simpa using hR'⟩
  simp [fiat_shamir.verifier.VerifierState.prover_message, hp, hfrom,
    core.option.Option.ok_or, fiat_shamir.verifier.VerifierState.guard,
    core.result.Result.Insts.CoreOpsTry.branch, lift, hidx, habs]

/-- A verifier message drawn as `n` squeezed bytes, within the run budget. -/
theorem verifier_message_ok (hD : Duplex out R) {T : Type} (n : Usize) (inst : fiat_shamir.codec.FromUniform T
    (Aeneas.Std.Array U8 n)) (hdef : inst.coredefaultDefaultInst = core.default.DefaultArray n core.default.DefaultU8)
    (has : inst.coreconvertAsMutSelf_ReprSliceU8Inst = Aeneas.Std.Array.Insts.CoreConvertAsMutSlice U8 n)
    (v : VS) (h : List DOp) (hR : R v.sponge h) (hb : runOf h + n.val ≤ maxSqueeze)
    (y : T) (hy : ∀ a : Aeneas.Std.Array U8 n, a.val = out h n.val → inst.from_uniform a = .ok y) :
    ∃ v', fiat_shamir.verifier.VerifierState.verifier_message inst v = .ok (y, v') ∧
      v'.poison = v.poison ∧ v'.narg = v.narg ∧ v'.hints = v.hints ∧ R v'.sponge (h ++ [.squeeze n.val]) := by
  have hz : (List.replicate n.val (0#u8 : U8)).length ≤ Usize.max := by simp; scalar_tac
  obtain ⟨s', o', hsq, ho, hR'⟩ := hD.squeeze v.sponge h (Slice.from (List.replicate n.val 0#u8) hz) hR
    (by simpa using hb)
  have hlen : o'.val.length = n.val := by rw [ho, hD.out_length]; simp
  have hback : (if hh : o'.length = n then (Aeneas.Std.Array.from o'.val (by simpa using hlen) : Aeneas.Std.Array U8 n)
      else Aeneas.Std.Array.repeat n 0#u8).val = out h n.val := by
    rw [dif_pos (by simpa using hlen)]; simpa using ho
  refine ⟨{ v with sponge := s' }, ?_, rfl, rfl, rfl, by simpa using hR'⟩
  have hrep : (Slice.from (Aeneas.Std.Array.repeat n 0#u8).val (by simp; scalar_tac) : Slice U8) =
      Slice.from (List.replicate n.val 0#u8) hz := by apply Slice.ext; simp
  have hfu := hy _ hback
  have hd0 : (core.default.DefaultU8.default : U8) = 0#u8 := rfl
  simp only [fiat_shamir.verifier.VerifierState.verifier_message, fiat_shamir.duplex.Blake2sDuplex.draw, hdef, has,
    core.default.DefaultArray,
    core.default.DefaultArray.default, Aeneas.Std.Array.Insts.CoreConvertAsMutSlice,
    Aeneas.Std.Array.Insts.CoreConvertAsMutSlice.as_mut, Std.bind_ok, hd0]
  simp [hrep, hsq, hfu]

/-- The generated opening verifier for the native state. -/
abbrev nativeInst :=
  fiat_shamir.verifier.VerifierState.Insts.PcsVerifierOpeningVerifierArrayU832F64UsizeF192

/-- The arithmetic verifier of the native state. -/
abbrev nativeV := nativeInst.fiat_shamirarithVerifierInst

theorem sample_ok (hD : Duplex out R) (v : VS) (h : List DOp) (hR : R v.sponge h)
    (hb : runOf h + 24 ≤ maxSqueeze) :
    ∃ v', nativeV.verifier_message v = .ok (f192Of (out h 24), v') ∧
      v'.poison = v.poison ∧ v'.narg = v.narg ∧ v'.hints = v.hints ∧ R v'.sponge (h ++ [.squeeze 24]) := by
  obtain ⟨v', h1, e1, e2, e3, e4⟩ := verifier_message_ok hD 24#usize
    primitives.field.gf2_64x3.F192.Insts.Fiat_shamirCodecFromUniformArrayU824 rfl rfl v h hR (by simpa using hb)
    (f192Of (out h 24)) (fun a ha => by
      have e : a.val = out h 24 := by simpa using ha
      exact (from_uniform_eq a).trans (by rw [e]))
  exact ⟨v', h1, e1, e2, e3, by simpa using e4⟩

theorem scalar_ok (hD : Duplex out R) (v : VS) (hp : v.poison = none) (h : List DOp) (hR : R v.sponge h)
    (hn : 24 ≤ v.narg.val.length) :
    ∃ v', nativeV.prover_message v = .ok (.Ok (f192Of v.narg.val), v') ∧ v'.poison = none ∧
      v'.narg.val = v.narg.val.drop 24 ∧ v'.hints = v.hints ∧ R v'.sponge (h ++ [.absorb (v.narg.val.take 24)]) := by
  obtain ⟨rest, hf, er⟩ := from_narg_f192 v.narg hn
  exact prover_message_ok hD _ v hp _ rest 24 hn hf er h hR

theorem root_ok (hD : Duplex out R) (v : VS) (hp : v.poison = none) (h : List DOp) (hR : R v.sponge h)
    (hn : 32 ≤ v.narg.val.length) :
    ∃ (r : Merkle.Digest) (v' : VS), nativeInst.next_root v = .ok (.Ok r, v') ∧ r.val = v.narg.val.take 32 ∧
      v'.poison = none ∧ v'.narg.val = v.narg.val.drop 32 ∧ v'.hints = v.hints ∧
      R v'.sponge (h ++ [.absorb (v.narg.val.take 32)]) := by
  obtain ⟨a, rest, hf, ea, er⟩ := from_narg_digest v.narg hn
  obtain ⟨v', h1, e1, e2, e3, e4⟩ := prover_message_ok hD (ArrayU8N.Insts.Fiat_shamirCodecFromNargArrayU8N 32#usize)
    v hp _ rest 32 hn hf er h hR
  exact ⟨a, v', h1, ea, e1, e2, e3, e4⟩

theorem prover_messages_loop (hD : Duplex out R) (n : Usize) :
    ∀ (m : Nat) (i : Usize) (v : VS) (acc : alloc.vec.Vec F192) (h : List DOp), n.val - i.val = m →
      i.val ≤ n.val → acc.val.length = i.val → v.poison = none → R v.sponge h → 24 * m ≤ v.narg.val.length →
      ∃ w v', fiat_shamir.arith.Verifier.prover_messages.default_loop nativeV v n acc i = .ok (.Ok w, v') ∧
        w.val = acc.val ++ readsE v.narg.val m ∧ v'.poison = none ∧ v'.narg.val = v.narg.val.drop (24 * m) ∧
        v'.hints = v.hints ∧ R v'.sponge (h ++ absorbsE v.narg.val m) := by
  intro m
  induction m with
  | zero =>
    intro i v acc h hm hi hacc hp hR _
    refine ⟨acc, v, ?_, by simp [readsE], hp, by simp, rfl, by simpa [absorbsE] using hR⟩
    unfold fiat_shamir.arith.Verifier.prover_messages.default_loop
    apply Fold.loop_done
    have : ¬ (i < n) := by simp [UScalar.lt_equiv]; omega
    simp [fiat_shamir.arith.Verifier.prover_messages.default_loop.body, this]
  | succ m ih =>
    intro i v acc h hm hi hacc hp hR hn
    have hlt : i < n := by simp [UScalar.lt_equiv]; omega
    obtain ⟨v1, h1, p1, n1, s1, r1⟩ := scalar_ok hD v hp h hR (by omega)
    have h1' : fiat_shamir.verifier.VerifierState.Insts.Fiat_shamirArithVerifierF192.prover_message v =
        .ok (.Ok (f192Of v.narg.val), v1) := h1
    obtain ⟨acc1, hpush, eacc1⟩ := Query.push_ok acc (f192Of v.narg.val) (by
      have := n.hBounds; simp [Usize.max] at *; scalar_tac)
    have hsucc := Fold.succ_val i n.val (by omega) (by scalar_tac)
    obtain ⟨w, v', hl, ew, p', n', s', r'⟩ := ih (Std.Usize.wrapping_add i 1#usize) v1 acc1
      (h ++ [.absorb (v.narg.val.take 24)]) (by rw [hsucc]; omega) (by rw [hsucc]; omega)
      (by rw [eacc1, hsucc]; simp [hacc]) p1 r1 (by rw [n1]; simp; omega)
    refine ⟨w, v', ?_, ?_, p', ?_, by rw [s', s1], ?_⟩
    · unfold fiat_shamir.arith.Verifier.prover_messages.default_loop
      rw [Fold.loop_cont (x' := (v1, acc1, Std.Usize.wrapping_add i 1#usize)) (by
        simp [fiat_shamir.arith.Verifier.prover_messages.default_loop.body, hlt, h1',
          core.result.Result.Insts.CoreOpsTry.branch, hpush, lift])]
      unfold fiat_shamir.arith.Verifier.prover_messages.default_loop at hl
      exact hl
    · rw [ew, eacc1, n1]; simp [readsE]
    · rw [n', n1]; simp [List.drop_drop]; ring_nf
    · rw [n1] at r'; simpa [absorbsE] using r'

theorem runOf_squeeze (h : List DOp) (n : Nat) : runOf (h ++ [.squeeze n]) = runOf h + n := by
  simp [runOf, runRev]; omega

theorem verifier_messages_loop (hD : Duplex out R) (n : Usize) :
    ∀ (m : Nat) (i : Usize) (v : VS) (acc : alloc.vec.Vec F192) (h : List DOp), n.val - i.val = m →
      i.val ≤ n.val → acc.val.length = i.val → R v.sponge h → runOf h + 24 * m ≤ maxSqueeze →
      ∃ w v', fiat_shamir.arith.Verifier.verifier_messages.default_loop nativeV v n acc i = .ok (w, v') ∧
        w.val = acc.val ++ draws out h m ∧ v'.poison = v.poison ∧ v'.narg = v.narg ∧
        v'.hints = v.hints ∧ R v'.sponge (h ++ sqs m) := by
  intro m
  induction m with
  | zero =>
    intro i v acc h hm hi hacc hR _
    refine ⟨acc, v, ?_, by simp [draws], rfl, rfl, rfl, by simpa [sqs] using hR⟩
    unfold fiat_shamir.arith.Verifier.verifier_messages.default_loop
    apply Fold.loop_done
    have : ¬ (i < n) := by simp [UScalar.lt_equiv]; omega
    simp [fiat_shamir.arith.Verifier.verifier_messages.default_loop.body, this]
  | succ m ih =>
    intro i v acc h hm hi hacc hR hb
    have hlt : i < n := by simp [UScalar.lt_equiv]; omega
    obtain ⟨v1, h1, p1, n1, s1, r1⟩ := sample_ok hD v h hR (by omega)
    have h1' : fiat_shamir.verifier.VerifierState.Insts.Fiat_shamirArithVerifierF192.verifier_message v =
        .ok (f192Of (out h 24), v1) := h1
    obtain ⟨acc1, hpush, eacc1⟩ := Query.push_ok acc (f192Of (out h 24)) (by
      have := n.hBounds; simp [Usize.max] at *; scalar_tac)
    have hsucc := Fold.succ_val i n.val (by omega) (by scalar_tac)
    obtain ⟨w, v', hl, ew, p', n', s', r'⟩ := ih (Std.Usize.wrapping_add i 1#usize) v1 acc1
      (h ++ [.squeeze 24]) (by rw [hsucc]; omega) (by rw [hsucc]; omega)
      (by rw [eacc1, hsucc]; simp [hacc]) r1 (by rw [runOf_squeeze]; omega)
    refine ⟨w, v', ?_, ?_, by rw [p', p1], by rw [n', n1], by rw [s', s1], ?_⟩
    · unfold fiat_shamir.arith.Verifier.verifier_messages.default_loop
      rw [Fold.loop_cont (x' := (v1, acc1, Std.Usize.wrapping_add i 1#usize)) (by
        simp [fiat_shamir.arith.Verifier.verifier_messages.default_loop.body, hlt, h1', hpush, lift])]
      unfold fiat_shamir.arith.Verifier.verifier_messages.default_loop at hl
      exact hl
    · rw [ew, eacc1]; simp [draws]
    · simpa [sqs, List.replicate_succ] using r'

theorem slice_len_eq {α : Type} (a b : Slice α) : Slice.len a = Slice.len b ↔ a.val.length = b.val.length := by
  constructor
  · intro h; have := congrArg UScalar.val h; simpa [Slice.len_val] using this
  · intro h; exact UScalar.eq_of_val_eq (by simp [Slice.len_val, h])

theorem block_eq (challenge : Aeneas.Std.Array U8 32#usize) (nonce : U64) :
    ∃ b, fiat_shamir.pow.block challenge nonce = .ok b ∧
      b.val = powBlock challenge.val (core.num.U64.to_le_bytes nonce).val := by
  have hc : challenge.val.length = 32 := by simp
  have hn : (core.num.U64.to_le_bytes nonce).val.length = 8 := by simp [core.num.U64.to_le_bytes]
  have ht : (core.num.U64.to_le_bytes fiat_shamir.pow.ProofOfWork.TRIAL_TAG).val.length = 8 := by
    simp [core.num.U64.to_le_bytes]
  have h64 : (64 : Nat) ≤ Usize.max := by scalar_tac
  refine ⟨Aeneas.Std.Array.make 64#usize (powBlock challenge.val (core.num.U64.to_le_bytes nonce).val)
    (by simp [powBlock, hc, hn, ht]), ?_, by simp⟩
  simp [fiat_shamir.pow.block, core.array.Array.index_mut, core.ops.index.IndexMutSlice,
    core.slice.index.Slice.index_mut, core.slice.index.SliceIndexRangeToUsizeSlice,
    core.slice.index.SliceIndexRangeToUsizeSlice.index_mut, core.slice.index.SliceIndexRangeUsizeSlice,
    core.slice.index.SliceIndexRangeUsizeSlice.index_mut, core.slice.index.SliceIndexRangeFromUsizeSlice,
    core.slice.index.SliceIndexRangeFromUsizeSlice.index_mut, core.slice.Slice.copy_from_slice,
    Aeneas.Std.Array.from_slice, lift, Aeneas.Std.Array.to_slice, hc, hn, ht, slice_len_eq, List.slice,
    List.setSlice!, Slice.drop]
  rw [Aeneas.Std.Array.eq_iff]
  have e1 : challenge.val.take 32 = challenge.val := List.take_of_length_le (by omega)
  have e2 : (core.num.U64.to_le_bytes nonce).val.take 8 = (core.num.U64.to_le_bytes nonce).val :=
    List.take_of_length_le (by omega)
  have e3 : (core.num.U64.to_le_bytes fiat_shamir.pow.ProofOfWork.TRIAL_TAG).val.take 8 =
      (core.num.U64.to_le_bytes fiat_shamir.pow.ProofOfWork.TRIAL_TAG).val := List.take_of_length_le (by omega)
  have e4 : challenge.val.take 56 = challenge.val := List.take_of_length_le (by omega)
  have e5 : (core.num.U64.to_le_bytes nonce).val.take 24 = (core.num.U64.to_le_bytes nonce).val :=
    List.take_of_length_le (by omega)
  simp [e1, e2, e3, powBlock, List.take_append, List.drop_append, hc, hn]
  rw [e4, e5]

theorem accepts_eq (digest : Aeneas.Std.Array U8 32#usize) (bits : U32) :
    fiat_shamir.pow.ProofOfWork.accepts { bits := bits } digest =
      .ok (decide (bits.val ≤ (core.num.U64.leading_zeros (u64Of digest.val)).val)) := by
  have hd : digest.val.length = 32 := by simp
  have hs : core.slice.Slice.split_first_chunk 8#usize (Aeneas.Std.Array.to_slice digest) =
      .ok (some (Aeneas.Std.Array.make 8#usize (digest.val.take 8) (by simp),
        Slice.from (digest.val.drop 8) (by simp; scalar_tac))) := by
    simp [core.slice.Slice.split_first_chunk, Aeneas.Std.Array.to_slice, hd]
  have hw : core.num.U64.from_le_bytes (Aeneas.Std.Array.make 8#usize (digest.val.take 8) (by simp)) =
      u64Of digest.val := by rw [u64Of_eq]; simp [u64Of_take]
  simp [fiat_shamir.pow.ProofOfWork.accepts, lift, hs, core.option.Option.expect, Result.ofOption, hw,
    UScalar.le_equiv]

theorem pow_verify_eq {H : List U8 → Merkle.Digest} (hH : PowHash H) (bits : U32)
    (challenge : Aeneas.Std.Array U8 32#usize) (nonce : U64) :
    ∃ b, fiat_shamir.pow.ProofOfWork.verify { bits := bits } challenge nonce = .ok b ∧
      (b = true ↔ Works H challenge.val nonce bits.val) := by
  obtain ⟨b, hb, eb⟩ := block_eq challenge nonce
  have hh : primitives.hash.hash (Aeneas.Std.Array.to_slice b) = .ok (H (powBlock challenge.val
      (core.num.U64.to_le_bytes nonce).val)) := by
    rw [hH]; congr 2; simpa [Aeneas.Std.Array.to_slice] using eb
  refine ⟨decide (bits.val ≤ (core.num.U64.leading_zeros (u64Of (H (powBlock challenge.val
    (core.num.U64.to_le_bytes nonce).val)).val)).val), ?_, by simp [Works]⟩
  simp [fiat_shamir.pow.ProofOfWork.verify, fiat_shamir.pow.trial, hb, lift, hh, accepts_eq]

theorem pow_new (bits : U32) (h : bits.val ≤ 63) : fiat_shamir.pow.ProofOfWork.new bits = .ok { bits := bits } := by
  have : bits ≤ fiat_shamir.pow.ProofOfWork.MAX_BITS := by
    simp [fiat_shamir.pow.ProofOfWork.MAX_BITS, UScalar.le_equiv]; omega
  simp [fiat_shamir.pow.ProofOfWork.new, massert, this]

theorem check_pow_zero (v : VS) (bits : U32) (h0 : bits.val = 0) :
    nativeV.check_pow v bits = .ok (.Ok (), v) := by
  have hb : bits = 0#u32 := UScalar.eq_of_val_eq (by simp [h0])
  subst hb
  simp [nativeV, nativeInst, fiat_shamir.verifier.VerifierState.Insts.Fiat_shamirArithVerifierF192,
    fiat_shamir.verifier.VerifierState.Insts.Fiat_shamirArithVerifierF192.check_pow,
    fiat_shamir.verifier.VerifierState.check_pow, pow_new 0#u32 (by simp)]

theorem check_pow_ok (hD : Duplex out R) {H : List U8 → Merkle.Digest} (hH : PowHash H) (v : VS)
    (hp : v.poison = none) (h : List DOp) (hR : R v.sponge h) (bits : U32) (h0 : bits.val ≠ 0)
    (h63 : bits.val ≤ 63) (hb : runOf h + 32 ≤ maxSqueeze) (hn : 8 ≤ v.narg.val.length)
    (hw : Works H (out h 32) (u64Of v.narg.val) bits.val) :
    ∃ v', nativeV.check_pow v bits = .ok (.Ok (), v') ∧ v'.poison = none ∧
      v'.narg.val = v.narg.val.drop 8 ∧ v'.hints = v.hints ∧
      R v'.sponge (h ++ [.squeeze 32, .absorb (v.narg.val.take 8)]) := by
  have hl32 : (out h 32).length = 32 := hD.out_length h 32
  let ch : Aeneas.Std.Array U8 32#usize := Aeneas.Std.Array.make 32#usize (out h 32) (by simpa using hl32)
  obtain ⟨v1, h1, p1, n1, s1, r1⟩ := verifier_message_ok hD 32#usize
    (ArrayU8N.Insts.Fiat_shamirCodecFromUniformArrayU8N (core.default.DefaultArray 32#usize core.default.DefaultU8))
    rfl rfl v h hR (by simpa using hb) ch (fun a ha => by
      have : a = ch := by rw [Aeneas.Std.Array.eq_iff]; simpa [ch] using ha
      simp [ArrayU8N.Insts.Fiat_shamirCodecFromUniformArrayU8N,
        ArrayU8N.Insts.Fiat_shamirCodecFromUniformArrayU8N.from_uniform, this])
  obtain ⟨rest, hf, er⟩ := from_narg_u64 v1.narg (by rw [n1]; exact hn)
  obtain ⟨v2, h2, p2, n2, s2, r2⟩ := prover_message_ok hD U64.Insts.Fiat_shamirCodecFromNargArrayU88 v1
    (by rw [p1, hp]) _ rest 8 (by rw [n1]; exact hn) hf er _ r1
  obtain ⟨b, hv, eb⟩ := pow_verify_eq hH bits ch (u64Of v1.narg.val)
  have hbt : b = true := eb.mpr (by simpa [ch, n1] using hw)
  subst hbt
  refine ⟨v2, ?_, p2, by rw [n2, n1], by rw [s2, s1], by simpa [n1, List.append_assoc] using r2⟩
  have hne : ¬ (bits = 0#u32) := by intro he; apply h0; simp [he]
  simp [nativeV, nativeInst, fiat_shamir.verifier.VerifierState.Insts.Fiat_shamirArithVerifierF192,
    fiat_shamir.verifier.VerifierState.Insts.Fiat_shamirArithVerifierF192.check_pow,
    fiat_shamir.verifier.VerifierState.check_pow, pow_new bits h63, hne, h1, h2,
    core.result.Result.Insts.CoreOpsTry.branch, hv, core.bool.Bool.then_some, core.option.Option.ok_or,
    fiat_shamir.verifier.VerifierState.guard]

theorem runOf_sqs (h : List DOp) (k : Nat) : runOf (h ++ sqs k) = runOf h + 24 * k := by
  induction k with
  | zero => simp [sqs]
  | succ k ih =>
    rw [show sqs (k + 1) = sqs k ++ [.squeeze 24] by simp [sqs, List.replicate_succ']]
    rw [← List.append_assoc, runOf_squeeze, ih]; ring

theorem draws_length (h : List DOp) (m : Nat) : (draws out h m).length = m := by
  induction m generalizing h with
  | zero => rfl
  | succ m ih => simp [draws, ih]

theorem draws_drop (h : List DOp) : ∀ (m k : Nat), k ≤ m →
    (draws out h m).drop k = draws out (h ++ sqs k) (m - k) := by
  intro m k
  induction k generalizing h m with
  | zero => intro _; simp [sqs]
  | succ k ih =>
    intro hk
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    simp only [draws, List.drop_succ_cons]
    rw [ih (h ++ [DOp.squeeze (24 : Nat)]) m' (by omega)]
    simp [sqs, List.replicate_succ, show m' + 1 - (k + 1) = m' - k by omega]

/-- The native challenger's squeezes: the next `xs` are the remaining draws of a run of `m`
after `h0`, the rest of the state unchanged. -/
def SqueezeRel (out : List DOp → Nat → List U8) (R : fiat_shamir.duplex.Blake2sDuplex → List DOp → Prop)
    (v0 : VS) (h0 : List DOp) (m : Nat) (ch : VS) (xs : List F192) : Prop :=
  ch.poison = v0.poison ∧ ch.narg = v0.narg ∧ ch.hints = v0.hints ∧
    ∃ k ≤ m, R ch.sponge (h0 ++ sqs k) ∧ xs = (draws out h0 m).drop k

theorem squeeze_tape (hD : Duplex out R) (v0 : VS) (h0 : List DOp) (m : Nat)
    (hb : runOf h0 + 24 * m ≤ maxSqueeze) :
    Sampling.SqueezeTape fiat_shamir.verifier.VerifierState.Insts.Fiat_shamirChallenger
      (SqueezeRel out R v0 h0 m) := by
  constructor
  intro ch x rest ⟨p, n, s, k, hk, hR, hx⟩
  rw [draws_drop h0 m k hk] at hx
  obtain ⟨m', hm'⟩ : ∃ m', m - k = m' + 1 := by
    rcases hmk : m - k with _ | m'
    · rw [hmk] at hx; simp [draws] at hx
    · exact ⟨m', rfl⟩
  rw [hm'] at hx
  simp only [draws, List.cons.injEq] at hx
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨v1, h1, p1, n1, s1, r1⟩ := sample_ok hD ch (h0 ++ sqs k) hR (by rw [runOf_sqs]; omega)
  refine ⟨v1, ?_, ⟨by rw [p1, p], by rw [n1, n], by rw [s1, s], k + 1, by omega, ?_, ?_⟩⟩
  · rw [hx1]; exact h1
  · simpa [sqs, List.replicate_succ', List.append_assoc] using r1
  · rw [hx2, draws_drop h0 m (k + 1) (by omega)]
    congr 1
    · simp [sqs, List.replicate_succ', List.append_assoc]
    · omega

theorem queries_ok (hw : System.Platform.numBits = 64) (hD : Duplex out R) (v : VS) (h : List DOp)
    (hR : R v.sponge h) (depth count : Usize) (hd0 : 0 < depth.val) (hd64 : depth.val < 64)
    (hb : runOf h + 24 * ((count.val + 192 / depth.val - 1) / (192 / depth.val)) ≤ maxSqueeze) :
    ∃ (qs : alloc.vec.Vec Usize) (v' : VS), nativeInst.sample_queries v depth count = .ok (qs, v') ∧
      Whir.Concrete.deriveQueries depth.val count.val
        ((draws out h ((count.val + 192 / depth.val - 1) / (192 / depth.val))).map Sampling.toE).toArray =
          some (qs.val.map (·.val)).toArray ∧
      v'.poison = v.poison ∧ v'.narg = v.narg ∧ v'.hints = v.hints ∧
      R v'.sponge (h ++ sqs ((count.val + 192 / depth.val - 1) / (192 / depth.val))) := by
  set m := (count.val + 192 / depth.val - 1) / (192 / depth.val) with hm
  obtain ⟨qs, v', hs, hrel, hq⟩ := Sampling.sample_queries_eq hw
    fiat_shamir.verifier.VerifierState.Insts.Fiat_shamirChallenger (SqueezeRel out R v h m)
    (squeeze_tape hD v h m hb) v depth count hd0 hd64 (draws out h m) (by rw [draws_length]) []
    ⟨rfl, rfl, rfl, 0, by omega, by simpa [sqs] using hR, by simp⟩
  obtain ⟨p, n, s, k, hk, hR', hx⟩ := hrel
  have hkm : k = m := by
    have := congrArg List.length hx
    simp [draws_length] at this; omega
  subst hkm
  refine ⟨qs, v', ?_, hq, p, n, s, hR'⟩
  simp only [nativeInst,
    fiat_shamir.verifier.VerifierState.Insts.PcsVerifierOpeningVerifierArrayU832F64UsizeF192.sample_queries]
  exact hs
end State

/-! ## What a proof must hold for the native state to answer the replay's reads -/

/-- The native events: elements `F192`, queries `usize`, roots digests, words `u64`. -/
abbrev NEvent := Event F192 Usize Merkle.Digest primitives.field.gf2_64.F64

/-- The squeezes a query batch of `count` positions of `d` bits draws. -/
def qDraws (d count : Nat) : Nat := (count + 192 / d - 1) / (192 / d)

/-- The native state with transcript `h`, remaining NARG bytes `narg` and hints `hints` answers
`evs`: every draw is the duplex's output for the transcript so far, within the squeeze budget;
every prover message is the next bytes of the NARG string (24 per element, read as three
little-endian limbs; a root its 32 bytes); every proof of work of nonzero bits has its challenge
drawn and a nonce (8 little-endian bytes) that clears the bits; the query positions are the
model's `deriveQueries` of their draws; and every rows event is the next length-prefixed hint,
whose content opens the event's rows (`HintOpens`). -/
def Answers (out : List DOp → Nat → List U8) (H : List U8 → Merkle.Digest) (leaf : List U64 → Merkle.Digest)
    (node : Merkle.Digest → Merkle.Digest → Merkle.Digest) :
    List DOp → List U8 → List U8 → List NEvent → Prop
  | _, _, _, [] => True
  | h, n, hs, .sample e :: rest =>
    runOf h + 24 ≤ maxSqueeze ∧ e = f192Of (out h 24) ∧ Answers out H leaf node (h ++ [.squeeze 24]) n hs rest
  | h, n, hs, .sampleVec zs :: rest =>
    runOf h + 24 * zs.length ≤ maxSqueeze ∧ zs = draws out h zs.length ∧
      Answers out H leaf node (h ++ sqs zs.length) n hs rest
  | h, n, hs, .scalar y :: rest =>
    24 ≤ n.length ∧ y = f192Of n ∧ Answers out H leaf node (h ++ [.absorb (n.take 24)]) (n.drop 24) hs rest
  | h, n, hs, .scalars ys :: rest =>
    24 * ys.length ≤ n.length ∧ ys = readsE n ys.length ∧
      Answers out H leaf node (h ++ absorbsE n ys.length) (n.drop (24 * ys.length)) hs rest
  | h, n, hs, .poly u0 u2 :: rest =>
    48 ≤ n.length ∧ [u0, u2] = readsE n 2 ∧ Answers out H leaf node (h ++ absorbsE n 2) (n.drop 48) hs rest
  | h, n, hs, .root r :: rest =>
    32 ≤ n.length ∧ r.val = n.take 32 ∧ Answers out H leaf node (h ++ [.absorb (n.take 32)]) (n.drop 32) hs rest
  | h, n, hs, .grind bits :: rest =>
    bits ≤ 63 ∧ (bits = 0 → Answers out H leaf node h n hs rest) ∧
      (bits ≠ 0 → runOf h + 32 ≤ maxSqueeze ∧ 8 ≤ n.length ∧ Works H (out h 32) (u64Of n) bits ∧
        Answers out H leaf node (h ++ [.squeeze 32, .absorb (n.take 8)]) (n.drop 8) hs rest)
  | h, n, hs, .queries d qs :: rest =>
    0 < d ∧ d < 64 ∧ runOf h + 24 * qDraws d qs.length ≤ maxSqueeze ∧
      Whir.Concrete.deriveQueries d qs.length ((draws out h (qDraws d qs.length)).map Sampling.toE).toArray =
        some (qs.map (·.val)).toArray ∧
      Answers out H leaf node (h ++ sqs (qDraws d qs.length)) n hs rest
  | h, n, hs, .rows root depth qs rw lw ws :: rest =>
    ∃ (L : U32) (hint more : List U8), L.val = hint.length ∧
      hs = (core.num.U32.to_le_bytes L).val ++ hint ++ more ∧
      HintOpens leaf node root depth (qs.map (·.val)) rw lw ws hint ∧ Answers out H leaf node h n more rest

/-- The native state answers `evs`: unpoisoned, its sponge holds some transcript `h`, and its
remaining proof answers `evs` after `h`. -/
def NativeAnswers (out : List DOp → Nat → List U8) (R : fiat_shamir.duplex.Blake2sDuplex → List DOp → Prop)
    (H : List U8 → Merkle.Digest) (leaf : List U64 → Merkle.Digest)
    (node : Merkle.Digest → Merkle.Digest → Merkle.Digest) (v : VS) (evs : List NEvent) : Prop :=
  v.poison = none ∧ ∃ h, R v.sponge h ∧ Answers out H leaf node h v.narg.val v.hints.rest.val evs

theorem vec_val_inj (a b : List Usize) (h : a.map (·.val) = b.map (·.val)) : a = b := by
  apply List.map_injective_iff.mpr _ h
  intro x y hxy; exact UScalar.eq_of_val_eq hxy

/-- The native state's reads: the generated opening verifier over `VerifierState` answers every
read of `Transcript` on the tape `NativeAnswers`, given the duplex, proof-of-work hash and Merkle
hash content contracts. -/
theorem native_transcript (hw : System.Platform.numBits = 64) {out : List DOp → Nat → List U8}
    {R : fiat_shamir.duplex.Blake2sDuplex → List DOp → Prop} (hD : Duplex out R)
    {H : List U8 → Merkle.Digest} (hH : PowHash H) {leaf : List U64 → Merkle.Digest}
    {node : Merkle.Digest → Merkle.Digest → Merkle.Digest} (hRow : RowHash leaf) (hPair : PairHash node)
    (encode : F192 → Whir.Concrete.E) :
    Transcript nativeInst encode (NativeAnswers out R H leaf node) where
  sample := by
    intro v e rest ⟨hp, h, hR, hA⟩
    simp only [Answers] at hA
    obtain ⟨hb, he, hrest⟩ := hA
    obtain ⟨v', h1, p1, n1, s1, r1⟩ := sample_ok hD v h hR hb
    exact ⟨v', by rw [he]; exact h1, by rw [p1]; exact hp, _, r1, by rw [n1, s1]; exact hrest⟩
  sample_vec := by
    intro v n zs rest ⟨hp, h, hR, hA⟩ hlen
    simp only [Answers] at hA
    obtain ⟨hb, hz, hrest⟩ := hA
    obtain ⟨w, v', hl, ew, p, nn, s, r⟩ := verifier_messages_loop hD n n.val 0#usize v
      (alloc.vec.Vec.with_capacity F192 n) h (by simp) (by simp)
      (by simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new]) hR (by rw [← hlen]; exact hb)
    refine ⟨w, v', ?_, ?_, by rw [p]; exact hp, _, r, ?_⟩
    · show fiat_shamir.arith.Verifier.verifier_messages.default nativeV v n = _
      simp [fiat_shamir.arith.Verifier.verifier_messages.default, hl]
    · rw [ew, hz, hlen]; simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new]
    · rw [nn, s, ← hlen]; exact hrest
  scalar := by
    intro v y rest ⟨hp, h, hR, hA⟩
    simp only [Answers] at hA
    obtain ⟨hn, hy, hrest⟩ := hA
    obtain ⟨v', h1, p1, n1, s1, r1⟩ := scalar_ok hD v hp h hR hn
    exact ⟨v', by rw [hy]; exact h1, p1, _, r1, by rw [n1, s1]; exact hrest⟩
  scalars := by
    intro v n ys rest ⟨hp, h, hR, hA⟩ hlen
    simp only [Answers] at hA
    obtain ⟨hn, hy, hrest⟩ := hA
    obtain ⟨w, v', hl, ew, p, nn, s, r⟩ := prover_messages_loop hD n n.val 0#usize v
      (alloc.vec.Vec.with_capacity F192 n) h (by simp) (by simp)
      (by simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new]) hp hR (by rw [← hlen]; exact hn)
    refine ⟨w, v', ?_, ?_, p, h ++ absorbsE v.narg.val ys.length, by rw [hlen]; exact r, ?_⟩
    · show fiat_shamir.arith.Verifier.prover_messages.default nativeV v n = _
      simp [fiat_shamir.arith.Verifier.prover_messages.default, hl]
    · rw [ew, hy, hlen]; simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new]
    · rw [nn, s, ← hlen]; exact hrest
  poly := by
    intro v n u0 u2 rest ⟨hp, h, hR, hA⟩ h2
    simp only [Answers] at hA
    obtain ⟨hn, hy, hrest⟩ := hA
    obtain ⟨w, v', hl, ew, p, nn, s, r⟩ := prover_messages_loop hD n n.val 0#usize v
      (alloc.vec.Vec.with_capacity F192 n) h (by simp) (by simp)
      (by simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new]) hp hR (by rw [h2]; omega)
    refine ⟨w, v', ?_, ?_, p, h ++ absorbsE v.narg.val 2, by rw [h2] at r; exact r, ?_⟩
    · show fiat_shamir.arith.Verifier.prover_messages.default nativeV v n = _
      simp [fiat_shamir.arith.Verifier.prover_messages.default, hl]
    · rw [ew, h2, hy]; simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new]
    · rw [nn, s, h2]; exact hrest
  read_round := rfl
  root := by
    intro v r rest ⟨hp, h, hR, hA⟩
    simp only [Answers] at hA
    obtain ⟨hn, hr, hrest⟩ := hA
    obtain ⟨a, v', h1, ea, p1, n1, s1, r1⟩ := root_ok hD v hp h hR hn
    have : a = r := by rw [Aeneas.Std.Array.eq_iff, ea, hr]
    exact ⟨v', by rw [← this]; exact h1, p1, _, r1, by rw [n1, s1]; exact hrest⟩
  grind := by
    intro v bits rest ⟨hp, h, hR, hA⟩
    simp only [Answers] at hA
    obtain ⟨h63, hz, hnz⟩ := hA
    by_cases h0 : bits.val = 0
    · exact ⟨v, check_pow_zero v bits h0, hp, h, hR, hz h0⟩
    · obtain ⟨hb, hn, hwk, hrest⟩ := hnz h0
      obtain ⟨v', h1, p1, n1, s1, r1⟩ := check_pow_ok hD hH v hp h hR bits h0 h63 hb hn hwk
      exact ⟨v', h1, p1, _, r1, by rw [n1, s1]; exact hrest⟩
  queries := by
    intro v depth count qs rest ⟨hp, h, hR, hA⟩ hlen
    simp only [Answers] at hA
    obtain ⟨hd0, hd64, hb, hq, hrest⟩ := hA
    rw [hlen] at hb hq hrest
    obtain ⟨w, v', h1, hw', p1, n1, s1, r1⟩ := queries_ok hw hD v h hR depth count hd0 hd64 hb
    refine ⟨w, v', h1, ?_, by rw [p1]; exact hp, _, r1, by rw [n1, s1]; exact hrest⟩
    have e := hw'.symm.trans hq
    have e' : w.val.map (·.val) = qs.map (·.val) := by simpa using e
    exact vec_val_inj _ _ e'
  begin_scope := by intro v stage; rfl
  end_scope := by intro v; rfl
  rows := by
    intro v root depth queries a b ws rest ⟨hp, h, hR, hA⟩
    simp only [Answers] at hA
    obtain ⟨L, hint, more, hL, hb, hh, hrest⟩ := hA
    have hbound := v.hints.rest.property
    have hlen : v.hints.rest.val.length = 4 + hint.length + more.length := by
      rw [hb]; simp [core.num.U32.to_le_bytes]; omega
    have hword : UScalarTy.Usize.numBits = 64 := by simp only [UScalarTy.numBits]; exact hw
    obtain ⟨rows, hrun, erows⟩ := open_rows_ok hword hRow hPair v hp root depth queries a b L
      (Slice.from hint (by omega)) (Slice.from more (by omega)) (by simpa using hL) (by simpa using hb) ws
      (by simpa using hh)
    exact ⟨rows, _, hrun, erows, hp, h, hR, by simpa using hrest⟩

end WhirAeneas.NativeReads
