import WhirAeneas.Hash.Portable

namespace WhirAeneas.Hash
open Aeneas Aeneas.Std
open LeanVMCircuits.Blake2s.Rfc7693

/-- The source representation of a valid message schedule. -/
def encodeSchedule (s : Vector (Fin 16) 16) : Aeneas.Std.Array Usize 16#usize :=
  .from (s.toList.map (fun i => Usize.ofNatCore i.val (by scalar_tac))) (by simp)

/-- A position in the actual source's enumerated G_LANES slice. -/
def portableLanes (i : Fin 9) :
    core.iter.adapters.enumerate.Enumerate
      (core.slice.iter.Iter (Aeneas.Std.Array Usize 4#usize)) :=
  { iter := { slice := PortableSource.hash.G_LANES.to_slice, i := i.val },
    count := Usize.ofNatCore i.val (by scalar_tac) }

private theorem index_schedule (s : Vector (Fin 16) 16) (i : Usize) (hi : i.val < 16) :
    Aeneas.Std.Array.index_usize (encodeSchedule s) i =
      .ok (Usize.ofNatCore s[i.val].val (by scalar_tac)) := by
  simp [encodeSchedule, Aeneas.Std.Array.index_usize, hi]

private theorem index_fin (v : Vector Word 16) (i : Fin 16) :
    Aeneas.Std.Array.index_usize (encodeMessage v) (Usize.ofNatCore i.val (by scalar_tac)) =
      .ok (⟨v[i]⟩ : U32) := by
  exact index_encodeMessage v (Usize.ofNatCore i.val (by scalar_tac)) (by simp)

private theorem update_fin (v : Vector Word 16) (i : Fin 16) (w : Word) :
    Aeneas.Std.Array.update (encodeMessage v) (Usize.ofNatCore i.val (by scalar_tac)) ⟨w⟩ =
      .ok (encodeMessage (v.set i.val w)) := by
  exact update_encodeMessage v (Usize.ofNatCore i.val (by scalar_tac)) (by simp) w

private theorem word_add (a b : Word) :
    core.num.U32.wrapping_add (⟨a⟩ : U32) ⟨b⟩ = ⟨a + b⟩ := rfl

private theorem word_xor (a b : Word) :
    ((⟨a⟩ : U32) ^^^ (⟨b⟩ : U32)) = (⟨a ^^^ b⟩ : U32) := rfl

private theorem word_rotate (a : Word) (n : U32) :
    core.num.U32.rotate_right (⟨a⟩ : U32) n =
      ⟨a.rotateRight n.val⟩ := rfl

private theorem usize_mul_val (a b : Usize) (h : a.val * b.val < 2 ^ UScalarTy.Usize.numBits) :
    (Usize.wrapping_mul a b).val = a.val * b.val := by
  simp only [Usize.wrapping_mul_val_eq, UScalar.size_def, Nat.mod_eq_of_lt h]

private theorem usize_add_val (a b : Usize) (h : a.val + b.val < 2 ^ UScalarTy.Usize.numBits) :
    (Usize.wrapping_add a b).val = a.val + b.val := by
  simp only [Usize.wrapping_add_val_eq, UScalar.size_def, Nat.mod_eq_of_lt h]

private theorem body_of_next
    (v m : Vector Word 16) (s : Vector (Fin 16) 16)
    (iter iter' : core.iter.adapters.enumerate.Enumerate
      (core.slice.iter.Iter (Aeneas.Std.Array Usize 4#usize)))
    (g : Usize) (hg : g.val < 8) (lane : Aeneas.Std.Array Usize 4#usize)
    (a b c d : Fin 16)
    (hn : core.iter.adapters.enumerate.IteratorEnumerate.next
      (core.iter.traits.iterator.IteratorSliceIter (Aeneas.Std.Array Usize 4#usize)) iter =
      .ok (some (g, lane), iter'))
    (ha : Aeneas.Std.Array.index_usize lane 0#usize = .ok (Usize.ofNatCore a.val (by scalar_tac)))
    (hb : Aeneas.Std.Array.index_usize lane 1#usize = .ok (Usize.ofNatCore b.val (by scalar_tac)))
    (hc : Aeneas.Std.Array.index_usize lane 2#usize = .ok (Usize.ofNatCore c.val (by scalar_tac)))
    (hd : Aeneas.Std.Array.index_usize lane 3#usize = .ok (Usize.ofNatCore d.val (by scalar_tac))) :
    PortableSource.hash.compress_portable_loop0_loop0.body
      (encodeMessage m) (encodeSchedule s) iter (encodeMessage v) =
      .ok (.cont (iter', encodeMessage
        (G v a b c d m[s[2 * g.val]] m[s[2 * g.val + 1]]))) := by
  have hm : (Usize.wrapping_mul 2#usize g).val = 2 * g.val :=
    usize_mul_val _ _ (by scalar_tac)
  have hp : (Usize.wrapping_add (Usize.wrapping_mul 2#usize g) 1#usize).val =
      2 * g.val + 1 := by
    rw [usize_add_val _ _ (by rw [hm]; scalar_tac), hm]
    rfl
  simp (config := { autoUnfold := true }) only
    [PortableSource.hash.compress_portable_loop0_loop0.body, hn,
    bind_ok, ha, hb, hc, hd, lift, hm, hp,
    index_schedule s _ (by rw [hm]; omega),
    index_schedule s _ (by rw [hp]; omega),
    index_fin, update_fin, word_add, word_xor, word_rotate]
  rfl

private theorem portable_lanes_get (i : Fin 8) :
    PortableSource.hash.G_LANES.to_slice[i.val] = PortableSource.hash.G_LANES.val[i.val] := by
  change PortableSource.hash.G_LANES.to_slice.val[i.val] = PortableSource.hash.G_LANES.val[i.val]
  have h := congrArg
    (fun xs : List (Aeneas.Std.Array Usize 4#usize) => xs[i.val]?)
    (Aeneas.Std.Array.val_to_slice PortableSource.hash.G_LANES)
  have hr : i.val < PortableSource.hash.G_LANES.val.length := by
    simp
  obtain ⟨_, he⟩ := List.getElem_of_getElem?
    (h.trans (getElem?_pos PortableSource.hash.G_LANES.val i.val hr))
  exact he

private theorem portable_lanes_next (i : Fin 8) :
    core.iter.adapters.enumerate.IteratorEnumerate.next
      (core.iter.traits.iterator.IteratorSliceIter (Aeneas.Std.Array Usize 4#usize))
      (portableLanes ⟨i.val, by omega⟩) =
    .ok (some (Usize.ofNatCore i.val (by scalar_tac),
      PortableSource.hash.G_LANES.val[i.val]), portableLanes ⟨i.val + 1, by omega⟩) := by
  have hlen : PortableSource.hash.G_LANES.to_slice.len.val = 8 := by
    simp [PortableSource.hash.G_LANES, Aeneas.Std.Array.to_slice, Slice.len]
  have hlt : i.val < PortableSource.hash.G_LANES.to_slice.len := by
    simpa only [hlen] using i.isLt
  have hcount : ((Usize.ofNatCore i.val (by scalar_tac)) + 1#usize : Result Usize) =
      .ok (Usize.ofNatCore (i.val + 1) (by scalar_tac)) := by
    exact scalar_add_ofNatCore i.val 1 (by scalar_tac) (by scalar_tac) (by scalar_tac)
  simp (config := { autoUnfold := true }) only
    [portableLanes, core.iter.adapters.enumerate.IteratorEnumerate.next,
    core.slice.iter.IteratorSliceIter.next, hlt, _root_.dite_true,
    bind_tc_ok, hcount]
  exact congrArg
    (fun lane : Aeneas.Std.Array Usize 4#usize =>
      Result.ok (some (Usize.ofNatCore i.val (by scalar_tac), lane),
        portableLanes ⟨i.val + 1, by omega⟩))
    (portable_lanes_get i)

theorem portable_g_body_0 (v m : Vector Word 16) (s : Vector (Fin 16) 16) :
    PortableSource.hash.compress_portable_loop0_loop0.body
      (encodeMessage m) (encodeSchedule s) (portableLanes 0) (encodeMessage v) =
      .ok (.cont (portableLanes 1, encodeMessage (G v 0 4 8 12 m[s[0]] m[s[1]]))) := by
  apply body_of_next v m s (portableLanes 0) (portableLanes 1)
    (Usize.ofNatCore 0 (by scalar_tac)) (by simp)
    PortableSource.hash.G_LANES.val[0] 0 4 8 12 (portable_lanes_next 0) <;>
    simp [PortableSource.hash.G_LANES, Aeneas.Std.Array.index_usize] <;> rfl

theorem portable_g_body_1 (v m : Vector Word 16) (s : Vector (Fin 16) 16) :
    PortableSource.hash.compress_portable_loop0_loop0.body
      (encodeMessage m) (encodeSchedule s) (portableLanes 1) (encodeMessage v) =
      .ok (.cont (portableLanes 2, encodeMessage (G v 1 5 9 13 m[s[2]] m[s[3]]))) := by
  apply body_of_next v m s (portableLanes 1) (portableLanes 2)
    (Usize.ofNatCore 1 (by scalar_tac)) (by simp)
    PortableSource.hash.G_LANES.val[1] 1 5 9 13 (portable_lanes_next 1) <;>
    simp [PortableSource.hash.G_LANES, Aeneas.Std.Array.index_usize] <;> rfl

theorem portable_g_body_2 (v m : Vector Word 16) (s : Vector (Fin 16) 16) :
    PortableSource.hash.compress_portable_loop0_loop0.body
      (encodeMessage m) (encodeSchedule s) (portableLanes 2) (encodeMessage v) =
      .ok (.cont (portableLanes 3, encodeMessage (G v 2 6 10 14 m[s[4]] m[s[5]]))) := by
  apply body_of_next v m s (portableLanes 2) (portableLanes 3)
    (Usize.ofNatCore 2 (by scalar_tac)) (by simp)
    PortableSource.hash.G_LANES.val[2] 2 6 10 14 (portable_lanes_next 2) <;>
    simp [PortableSource.hash.G_LANES, Aeneas.Std.Array.index_usize] <;> rfl

theorem portable_g_body_3 (v m : Vector Word 16) (s : Vector (Fin 16) 16) :
    PortableSource.hash.compress_portable_loop0_loop0.body
      (encodeMessage m) (encodeSchedule s) (portableLanes 3) (encodeMessage v) =
      .ok (.cont (portableLanes 4, encodeMessage (G v 3 7 11 15 m[s[6]] m[s[7]]))) := by
  apply body_of_next v m s (portableLanes 3) (portableLanes 4)
    (Usize.ofNatCore 3 (by scalar_tac)) (by simp)
    PortableSource.hash.G_LANES.val[3] 3 7 11 15 (portable_lanes_next 3) <;>
    simp [PortableSource.hash.G_LANES, Aeneas.Std.Array.index_usize] <;> rfl

theorem portable_g_body_4 (v m : Vector Word 16) (s : Vector (Fin 16) 16) :
    PortableSource.hash.compress_portable_loop0_loop0.body
      (encodeMessage m) (encodeSchedule s) (portableLanes 4) (encodeMessage v) =
      .ok (.cont (portableLanes 5, encodeMessage (G v 0 5 10 15 m[s[8]] m[s[9]]))) := by
  apply body_of_next v m s (portableLanes 4) (portableLanes 5)
    (Usize.ofNatCore 4 (by scalar_tac)) (by simp)
    PortableSource.hash.G_LANES.val[4] 0 5 10 15 (portable_lanes_next 4) <;>
    simp [PortableSource.hash.G_LANES, Aeneas.Std.Array.index_usize] <;> rfl

theorem portable_g_body_5 (v m : Vector Word 16) (s : Vector (Fin 16) 16) :
    PortableSource.hash.compress_portable_loop0_loop0.body
      (encodeMessage m) (encodeSchedule s) (portableLanes 5) (encodeMessage v) =
      .ok (.cont (portableLanes 6, encodeMessage (G v 1 6 11 12 m[s[10]] m[s[11]]))) := by
  apply body_of_next v m s (portableLanes 5) (portableLanes 6)
    (Usize.ofNatCore 5 (by scalar_tac)) (by simp)
    PortableSource.hash.G_LANES.val[5] 1 6 11 12 (portable_lanes_next 5) <;>
    simp [PortableSource.hash.G_LANES, Aeneas.Std.Array.index_usize] <;> rfl

theorem portable_g_body_6 (v m : Vector Word 16) (s : Vector (Fin 16) 16) :
    PortableSource.hash.compress_portable_loop0_loop0.body
      (encodeMessage m) (encodeSchedule s) (portableLanes 6) (encodeMessage v) =
      .ok (.cont (portableLanes 7, encodeMessage (G v 2 7 8 13 m[s[12]] m[s[13]]))) := by
  apply body_of_next v m s (portableLanes 6) (portableLanes 7)
    (Usize.ofNatCore 6 (by scalar_tac)) (by simp)
    PortableSource.hash.G_LANES.val[6] 2 7 8 13 (portable_lanes_next 6) <;>
    simp [PortableSource.hash.G_LANES, Aeneas.Std.Array.index_usize] <;> rfl

theorem portable_g_body_7 (v m : Vector Word 16) (s : Vector (Fin 16) 16) :
    PortableSource.hash.compress_portable_loop0_loop0.body
      (encodeMessage m) (encodeSchedule s) (portableLanes 7) (encodeMessage v) =
      .ok (.cont (portableLanes 8, encodeMessage (G v 3 4 9 14 m[s[14]] m[s[15]]))) := by
  apply body_of_next v m s (portableLanes 7) (portableLanes 8)
    (Usize.ofNatCore 7 (by scalar_tac)) (by simp)
    PortableSource.hash.G_LANES.val[7] 3 4 9 14 (portable_lanes_next 7) <;>
    simp [PortableSource.hash.G_LANES, Aeneas.Std.Array.index_usize] <;> rfl

theorem portable_g_body_done (v m : Vector Word 16) (s : Vector (Fin 16) 16) :
    PortableSource.hash.compress_portable_loop0_loop0.body
      (encodeMessage m) (encodeSchedule s) (portableLanes 8) (encodeMessage v) =
      .ok (.done (encodeMessage v)) := by
  simp [PortableSource.hash.compress_portable_loop0_loop0.body,
    portableLanes, core.iter.adapters.enumerate.IteratorEnumerate.next,
    core.slice.iter.IteratorSliceIter.next,
    PortableSource.hash.G_LANES, Aeneas.Std.Array.to_slice, Slice.len]

/-- The source loop terminates after the eight actual G lanes and computes the
shared RFC round, for arbitrary words and every valid schedule. -/
theorem portable_g_round (v m : Vector Word 16) (s : Vector (Fin 16) 16) :
    PortableSource.hash.compress_portable_loop0_loop0
      (portableLanes 0) (encodeMessage m) (encodeMessage v) (encodeSchedule s) =
      .ok (encodeMessage (round v m s)) := by
  unfold PortableSource.hash.compress_portable_loop0_loop0
  rw [loop.eq_def]
  simp (config := { dsimp := true }) only [portable_g_body_0, bind_ok]
  rw [loop.eq_def]
  simp (config := { dsimp := true }) only [portable_g_body_1, bind_ok]
  rw [loop.eq_def]
  simp (config := { dsimp := true }) only [portable_g_body_2, bind_ok]
  rw [loop.eq_def]
  simp (config := { dsimp := true }) only [portable_g_body_3, bind_ok]
  rw [loop.eq_def]
  simp (config := { dsimp := true }) only [portable_g_body_4, bind_ok]
  rw [loop.eq_def]
  simp (config := { dsimp := true }) only [portable_g_body_5, bind_ok]
  rw [loop.eq_def]
  simp (config := { dsimp := true }) only [portable_g_body_6, bind_ok]
  rw [loop.eq_def]
  simp (config := { dsimp := true }) only [portable_g_body_7, bind_ok]
  rw [loop.eq_def]
  simp (config := { dsimp := true }) only [portable_g_body_done, bind_ok]
  unfold LeanVMCircuits.Blake2s.Rfc7693.round
  rfl

/-- The iterator initialization used by the actual outer round-loop body. -/
theorem portable_lanes_init :
    (do
      let slice ← lift (Aeneas.Std.Array.to_slice PortableSource.hash.G_LANES)
      let iter ← core.slice.Slice.iter slice
      core.iter.traits.iterator.Iterator.enumerate.trait_default
        (core.iter.traits.iterator.IteratorSliceIter (Aeneas.Std.Array Usize 4#usize)) iter) =
      .ok (portableLanes 0) := by
  simp only [lift, core.slice.Slice.iter, bind_tc_ok,
    core.iter.traits.iterator.Iterator.enumerate.trait_default,
    core.iter.traits.iterator.Iterator.enumerate.default]
  rfl

#check portable_g_body_0
#check portable_g_round
#print axioms portable_g_body_0
#print axioms portable_g_body_1
#print axioms portable_g_body_2
#print axioms portable_g_body_3
#print axioms portable_g_body_4
#print axioms portable_g_body_5
#print axioms portable_g_body_6
#print axioms portable_g_body_7
#print axioms portable_g_body_done
#print axioms portable_g_round
#print axioms portable_lanes_init

end WhirAeneas.Hash
