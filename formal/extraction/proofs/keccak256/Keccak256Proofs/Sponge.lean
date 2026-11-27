import Keccak256Proofs.Hasher

/-!
# The sponge step and the digest

`keccak256::absorb` XORs a rate block into the state and permutes it, and `digest_of` reads the
digest off the state: what `SpongeSpec` (`Hasher.lean`) asks, proved here from their extracted
bodies, given what the permutation `keccak_f` computes.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM Std.Do
open LeanVM.Semantics (KeccakState)
open LeanVM.Semantics.Keccak (lane)
open LeanVM.Protocol.KeccakHash

namespace Keccak256Proofs

namespace Sponge

open Hasher

theorem lane64_xor (x y : Std.U64) : lane64 (x ^^^ y) = lane64 x ^^^ lane64 y := by
  simp only [lane64, UScalar.bv_xor]
  rfl

/-- Lane `i` of a Rust state, read as the statement's. -/
theorem lane_toState (a : Array Std.U64 25#usize) (i : ℕ) (h : i < 25) :
    lane (toState a) i = lane64 a.val[i]! := by
  simp [lane, toState, h]

theorem rate_lanes : keccak256.RATE_LANES = ok 17#usize := by
  have h := ok_of_triple (x := keccak256.RATE_LANES) (P := fun r => r.val = 17) (by
    hax_mvcgen [keccak256.RATE_LANES, keccak256.RATE])
  obtain ⟨r, hr, hv⟩ := h
  rw [hr]
  congr 1
  scalar_tac

/-- One turn of `absorb`'s loop: lane `i` of the block XORed into lane `i` of the state. -/
theorem absorb_body (block : Array Std.U64 17#usize) (i e : Std.Usize) (he : e.val = 17)
    (hi : i.val < e.val) (st : Array Std.U64 25#usize) :
    ∃ (s : Std.Usize) (st' : Array Std.U64 25#usize),
      keccak256.absorb_loop.body block { start := i, «end» := e } st =
        ok (.cont ({ start := s, «end» := e }, st')) ∧ s.val = i.val + 1 ∧
      st'.val = st.val.set i.val (st.val[i.val]! ^^^ block.val[i.val]!) := by
  obtain ⟨s, hs, hnext⟩ := range_next_lt i e hi
  obtain ⟨st', hu, hst'⟩ := array_update st i (st.val[i.val]! ^^^ block.val[i.val]!)
    (by scalar_tac)
  refine ⟨s, st', ?_, hs, hst'⟩
  have hb : block.index_usize i = ok block.val[i.val]! := array_index_usize block i (by scalar_tac)
  have hsx : st.index_usize i = ok st.val[i.val]! := array_index_usize st i (by scalar_tac)
  simp [keccak256.absorb_loop.body, hnext]
  rw [hb, Aeneas.Std.bind_ok, hsx, Aeneas.Std.bind_ok]
  simp only [lift, Aeneas.Std.bind_ok, hu]

/-- **`absorb`'s loop**: the block's 17 lanes XORed into the first 17 of the state. -/
theorem absorb_loop_eq (st0 : Array Std.U64 25#usize) (block : Array Std.U64 17#usize) :
    ∃ st, keccak256.absorb_loop { start := 0#usize, «end» := 17#usize } st0 block = ok st ∧
      ∀ k < 25, st.val[k]! = if k < 17 then st0.val[k]! ^^^ block.val[k]! else st0.val[k]! := by
  unfold keccak256.absorb_loop
  have h17 : (17#usize).val = 17 := by decide
  obtain ⟨st, hst, hQ⟩ := loop_induct
    (fun x : core.ops.range.Range Std.Usize × Array Std.U64 25#usize =>
      keccak256.absorb_loop.body block x.1 x.2)
    (fun x => x.1.«end» = 17#usize ∧ x.1.start.val ≤ 17 ∧
      ∀ k < 25, x.2.val[k]! =
        if k < x.1.start.val then st0.val[k]! ^^^ block.val[k]! else st0.val[k]!)
    (fun st => ∀ k < 25, st.val[k]! =
      if k < 17 then st0.val[k]! ^^^ block.val[k]! else st0.val[k]!)
    (fun x => 17 - x.1.start.val)
    (by
      rintro ⟨⟨i, e⟩, st⟩ ⟨he, hi17, hinv⟩
      simp only at he hi17 hinv
      subst he
      by_cases hlt : i.val < 17
      · obtain ⟨s, st', hbody, hs, hst'⟩ := absorb_body block i 17#usize h17 (by omega) st
        refine ⟨_, hbody, ⟨rfl, by simp only [hs]; omega, ?_⟩, by simp only [hs]; omega⟩
        intro k hk
        have hlen : st.val.length = 25 := by simp
        simp only [hs, hst']
        by_cases hki : k = i.val
        · subst hki
          rw [getElem!_pos _ _ (by simp [hlen]; omega), List.getElem_set_self, hinv _ hk]
          simp only [lt_self_iff_false, ↓reduceIte, Nat.lt_add_one]
        · rw [getElem!_pos _ k (by simp [hlen]; omega), List.getElem_set_ne (by omega),
            ← getElem!_pos st.val k (by omega), hinv k hk]
          split_ifs <;> first | rfl | omega
      · refine ⟨.done st, ?_, ?_⟩
        · simp [keccak256.absorb_loop.body, range_next_ge i 17#usize (by omega)]
        · intro k hk
          rw [hinv k hk]
          have : i.val = 17 := by omega
          rw [this])
    ({ start := 0#usize, «end» := 17#usize }, st0) ⟨rfl, by simp, by simp⟩
  exact ⟨st, hst, hQ⟩

/-! ## The digest -/

/-- Byte `n` of a lane, least significant first. -/
def leByte (x : Std.U64) (n : ℕ) : Std.U8 := ⟨BitVec.ofNat 8 (x.val >>> (8 * n))⟩

theorem leByte_val (x : Std.U64) (n : ℕ) : (leByte x n).val = x.val >>> (8 * n) % 256 := by
  simp only [leByte, UScalar.val]
  rfl

/-- The closure of `u64::to_le_bytes`: byte `n`, and itself. -/
theorem to_le_bytes_closure (x : Std.U64) (n : Std.Usize) (hn : n.val < 8) :
    core.num.U64.to_le_bytes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut x n =
      ok (leByte x n.val, x) := by
  have h : core.num.U64.to_le_bytes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut x n
      ⦃ r => r = (leByte x n.val, x) ⦄ := by
    unfold core.num.U64.to_le_bytes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut
    step*
    have hiv : i.val = n.val := by
      rw [i_post, UScalar.cast_val_eq]
      exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hn (by decide))
    have h4 : i4 = leByte x n.val := by
      rw [UScalar.eq_equiv, leByte_val, i4_post, UScalar.cast_val_eq, i3_post, i2_post, i1_post,
        hiv, Nat.mod_eq_of_lt (by omega : 8 * n.val < 64)]
      rfl
    rw [h4]
  obtain ⟨r, hr, rfl⟩ := WP.spec_imp_exists h
  exact hr

/-- `u64::to_le_bytes`: the lane's eight bytes, the statement's `wordBytes`. -/
theorem to_le_bytes_eq (x : Std.U64) :
    ∃ a, core.num.U64.to_le_bytes x = ok a ∧ bytes a.val = wordBytes (lane64 x) := by
  obtain ⟨a, ha, hav⟩ := array_from_fn_eq 8#usize
    core.num.U64.to_le_bytes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8 x (leByte x)
    (fun i hi ↦ to_le_bytes_closure x i hi)
  refine ⟨a, ha, ?_⟩
  rw [hav]
  simp only [bytes, wordBytes, List.map_map]
  apply List.map_congr_left
  intro k hk
  have hk8 : k < 8 := by simpa using hk
  apply UInt8.toNat_inj.mp
  have hl : (b8 (leByte x k)).toNat = x.val >>> (8 * k) % 256 := by
    rw [← leByte_val]
    rfl
  have hx : (lane64 x).toNat = x.val := rfl
  have h8 : (8 * k).toUInt64.toNat = 8 * k := by
    simp only [Nat.toUInt64, UInt64.toNat_ofNat']
    omega
  rw [Function.comp_apply, hl, UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, hx, h8,
    Nat.mod_eq_of_lt (by omega : 8 * k < 64)]

/-- The digest's bytes from lane `k` of a state. -/
def laneBytes (state : Array Std.U64 25#usize) (k : ℕ) : List UInt8 :=
  wordBytes (lane64 state.val[k]!)

theorem laneBytes_length (state : Array Std.U64 25#usize) (k : ℕ) :
    (laneBytes state k).length = 8 := by
  simp [laneBytes, wordBytes]

theorem mul8 (i : Std.Usize) (hi : i.val ≤ 4) : ∃ r, 8#usize * i = ok r ∧ r.val = 8 * i.val := by
  apply ok_of_triple
  hax_mvcgen
  scalar_tac

theorem add8 (i : Std.Usize) (hi : i.val ≤ 32) : ∃ r, i + 8#usize = ok r ∧ r.val = i.val + 8 := by
  apply ok_of_triple
  hax_mvcgen
  scalar_tac

/-- One turn of `digest_of`'s loop: lane `i`'s bytes written at `8 i`. -/
theorem digest_body (state : Array Std.U64 25#usize) (i e : Std.Usize) (hi : i.val < e.val)
    (he : e.val = 4) (out : Array Std.U8 32#usize) :
    ∃ (s' : Std.Usize) (out' : Array Std.U8 32#usize),
      keccak256.digest_of_loop.body state { start := i, «end» := e } out =
        ok (.cont ({ start := s', «end» := e }, out')) ∧ s'.val = i.val + 1 ∧
      bytes out'.val = (bytes out.val).take (8 * i.val) ++ laneBytes state i.val ++
        (bytes out.val).drop (8 * (i.val + 1)) := by
  obtain ⟨s', hs', hnext⟩ := range_next_lt i e hi
  obtain ⟨i1, hi1, hi1v⟩ := mul8 i (by omega)
  obtain ⟨i2, hi2, hi2v⟩ := add8 i1 (by omega)
  obtain ⟨s1, wb, hidx, hs1, hwb⟩ := array_index_mut_range out i1 i2 (by omega)
    (by have : (32#usize).val = 32 := by decide
        omega)
  have hst : state.index_usize i = ok state.val[i.val]! :=
    array_index_usize state i (by scalar_tac)
  obtain ⟨a, ha, hab⟩ := to_le_bytes_eq state.val[i.val]!
  have hcopy := copy_from_slice_u8 s1 a.to_slice (by
    simp [Slice.length, hs1, List.slice]
    omega)
  refine ⟨s', wb a.to_slice, ?_, hs', ?_⟩
  · have ha' : core.num.U64.to_le_bytes (state.val[i.val]?.getD default) = ok a := by
      simpa using ha
    simp [keccak256.digest_of_loop.body, hnext, hi1, hi2, hidx, hst, core.array.Array.as_slice,
      rust_primitives.slice.array_as_slice]
    rw [ha', Aeneas.Std.bind_ok, hcopy, Aeneas.Std.bind_ok]
  · rw [hwb, laneBytes, ← hab]
    simp [bytes, List.setSlice!, hi1v]
    have hm : min 8 (32 - 8 * i.val) = 8 := by omega
    rw [hm, List.take_of_length_le (by simp), show 8 * i.val + 8 = 8 * (i.val + 1) by omega]

/-- **`digest_of`'s loop**: the first four lanes' bytes. -/
theorem digest_loop_eq (state : Array Std.U64 25#usize) (e : Std.Usize) (he : e.val = 4)
    (out0 : Array Std.U8 32#usize) :
    ∃ out, keccak256.digest_of_loop { start := 0#usize, «end» := e } state out0 = ok out ∧
      bytes out.val = (List.range 4).flatMap (laneBytes state) := by
  unfold keccak256.digest_of_loop
  obtain ⟨out, hout, hb⟩ := loop_induct
    (fun x : core.ops.range.Range Std.Usize × Array Std.U8 32#usize =>
      keccak256.digest_of_loop.body state x.1 x.2)
    (fun x => x.1.«end» = e ∧ x.1.start.val ≤ 4 ∧
      (bytes x.2.val).take (8 * x.1.start.val) =
        (List.range x.1.start.val).flatMap (laneBytes state))
    (fun out => bytes out.val = (List.range 4).flatMap (laneBytes state))
    (fun x => 4 - x.1.start.val)
    (by
      rintro ⟨⟨i, e'⟩, out⟩ ⟨hee, hi4, hb⟩
      simp only at hee hi4 hb
      subst hee
      by_cases hlt : i.val < 4
      · obtain ⟨s', out', hbody, hs', hb'⟩ := digest_body state i e' (by omega) he out
        refine ⟨_, hbody, ⟨rfl, by simp only [hs']; omega, ?_⟩, by simp only [hs']; omega⟩
        simp only [hs', hb', List.range_succ, List.flatMap_append, List.flatMap_singleton,
          ← hb]
        apply List.take_left'
        have : (bytes out.val).length = 32 := by simp [bytes]
        simp [laneBytes_length]
        omega
      · have hi : i.val = 4 := by omega
        refine ⟨.done out, ?_, ?_⟩
        · simp [keccak256.digest_of_loop.body, range_next_ge i e' (by omega)]
        · rw [← hi, ← hb, List.take_of_length_le (by simp [bytes, hi])])
    ({ start := 0#usize, «end» := e }, out0) ⟨rfl, by simp, by simp⟩
  exact ⟨out, hout, hb⟩

end Sponge

open Sponge in
/-- **The sponge step and the digest**, given what the permutation `keccak_f` computes. -/
theorem spongeSpec_of_keccak_f {π : KeccakState → KeccakState}
    (hf : ∀ a, ∃ a', keccak256.keccak_f a = ok a' ∧ toState a' = π (toState a)) :
    SpongeSpec π where
  absorb state block := by
    obtain ⟨st, hst, hQ⟩ := absorb_loop_eq state block
    obtain ⟨st', hst', hπ⟩ := hf st
    refine ⟨st', by simp only [keccak256.absorb, rate_lanes, Aeneas.Std.bind_ok, hst, hst'], ?_⟩
    rw [hπ]
    refine congrArg π (congrArg Vector.ofFn (funext fun i ↦ ?_))
    rw [hQ i.val i.isLt, lane_toState state i.val i.isLt]
    split_ifs
    · exact lane64_xor _ _
    · rfl
  digest_of state := by
    obtain ⟨out0, hout0, -⟩ := array_repeat 32#usize core.U8.Insts.CoreCloneClone (fun _ ↦ rfl) 0#u8
    have h4 : keccak256.OUT_LEN / 8#usize = ok 4#usize := by
      obtain ⟨r, hr, hv⟩ := ok_of_triple (x := keccak256.OUT_LEN / 8#usize)
        (P := fun r => r.val = 4) (by
          hax_mvcgen
          rename_i r hr
          rw [hr]
          simp [keccak256.OUT_LEN])
      rw [hr]
      congr 1
      scalar_tac
    obtain ⟨out, hout, hb⟩ := digest_loop_eq state 4#usize (by decide) out0
    refine ⟨out, by simp only [keccak256.digest_of, hout0, Aeneas.Std.bind_ok, h4, hout], ?_⟩
    rw [hb]
    simp [digestBytes, laneBytes, lane_toState, List.range_succ]

end Keccak256Proofs
