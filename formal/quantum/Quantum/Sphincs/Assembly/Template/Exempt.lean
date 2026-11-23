module

public import Quantum.Sphincs.Assembly.Template
public import Quantum.Sphincs.Assembly.PathsDisjoint

@[expose] public section

/-!
# The template's programs and the event's exemptions

The two facts the event (contract C3, `Quantum.Sphincs.Events`) needs from the template's program
ports, as statements about the cells the ports hardwire. At the template data `(pub, v)` the
event's data is `evData pub v`.

* **Realized ports** (`realize_slotPorts`, `realize_hmsgPorts`): at the hidden values `v`, the
  ports of a structural slot `s` (`InTable s`) hardwire the cells `pathCells` of its honest path
  at the values `v ∘ .val` (Events' `blocksOf`), the last `h` value corrected to the value at its
  output position; the ports of `H_msg` call `i` on `M` (label `T`) those of the call's one block at
  `R = v (.rnd M)`, the output corrected to `v (pol.out T M i)`.
* **Exempted slots** (`heldIn_of_cells`, `mem_exS_of_cells`): if a database `U` holds every cell
  of a structural slot's path with its programmed value (`RoundHeld`), and the final `h`-cell is
  none of the earlier rounds' `h`-cells (`FinalSep`, a property of good data:
  `finalSep_of_pathsAvoid`, from PathBad's `PathsAvoid` at `pub.xw`, `h`, `valsOf v`), the slot's
  honest path is held (`HeldIn`, with `h' = update h zfin wcorr`: the public `h` with the
  corrected final value; `held_update_final` for any absorption); with `U` the hardwired cells,
  the slot is in `exS`. The digest is the value at the output (`trunc128_cor128`).
* **Head-tails** (`isHeadTail_hmsg`, `isHeadTail_slot`): if a database holds the `k`- and
  `k'`-cells of an `H_msg` call's round (programmed by the batch's first two ports), the call's
  honest tail heads to its `h`-cell, with the rate after `π`: the hypothesis of Events'
  `mem_covEx_programH` and `not_mem_bad_programH_hmsg` before a call-0 `h` program. The same for a
  structural slot's final `h`-cell (`not_mem_bad_programH_honest`); `isHeadTail_take_succ_rn`:
  round `j` of any absorption (the earlier `h`-cells of multi-block paths).

What stays with the run invariants (SP-GTC, SP-PS1): that at a port's call the batch's earlier
ports are hardwired (`RoundHeld` for the rounds before, from `realize_slotPorts`,
`realize_hmsgPorts`), and `PathsAvoid` on the good data (SP-PB's fraction, moved to `(p, v)`).
-/

open Quantum Quantum.Sponge Sphincs
open HashSig (Digest HashOutput Message Randomizer PublicParameter)
open Quantum.Xmss (X Z blocks trunc128 length_blocks)
open Quantum.Xmss.Hybrid (LazyProg restrictTo)
open Quantum.Xmss.Assembly (rnSt rnK rnR rnZ rnMid RnAgree rnSt_congr rnK_congr rnR_congr
  rnZ_congr rnSt_succ exists_round_of_mem_spongeReads trunc128_add_embed128 xor_xor_cancel_left
  XW)

namespace Quantum.Sphincs.Assembly

/-! ## Absorptions with a changed final `h` value -/

section rounds

variable (π : Equiv.Perm (X × Z)) (h : Z → X) (k k' : X → Z)

/-- **A round of an absorption is a head-tail.** If `D` holds the `k`, `k'` cells of rounds
`0, …, j` with their key values, the tail of the first `j + 1` blocks heads to the `h`-cell of
round `j`, with the rate after `π`. -/
theorem isHeadTail_take_succ_rn {D : Dbs X Z} {msg : List X} {j : ℕ} (hj : j < msg.length)
    (hD : ∀ i ≤ j, D.k (rnK π h k k' (fun i ↦ msg.getD i 0) i) =
        some (k (rnK π h k k' (fun i ↦ msg.getD i 0) i)) ∧
      D.k' (rnR π h k k' (fun i ↦ msg.getD i 0) i) =
        some (k' (rnR π h k k' (fun i ↦ msg.getD i 0) i))) :
    IsHeadTail π D (absorbTail (spongePerm (h, k, k') π) (msg.take (j + 1)))
      (rnZ π h k k' (fun i ↦ msg.getD i 0) j) (rnR π h k k' (fun i ↦ msg.getD i 0) j) := by
  have hA : AgreesRounds π h k k' D (msg.take j) := by
    intro i hi
    have hij : i < j := by
      rw [List.length_take] at hi
      omega
    have ht : (msg.take j).take i = msg.take i := by
      rw [List.take_take, Nat.min_eq_left hij.le]
    have hg : (msg.take j)[i] = msg.getD i 0 := by
      rw [List.getElem_take, List.getD_eq_getElem _ _ (by omega)]
    dsimp only
    rw [ht, hg, absorb_take_eq_rnSt π h k k' msg i (by omega)]
    exact hD i hij.le
  have hm : msg.take (j + 1) = msg.take j ++ [msg.getD j 0] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some,
      List.getD_eq_getElem _ _ hj]
  have hs := absorb_take_eq_rnSt π h k k' msg j hj.le
  rw [hm, absorbTail_append_singleton]
  refine ⟨_, _, _, k ((absorb (spongePerm (h, k, k') π) (msg.take j)).1 + msg.getD j 0),
    (rnMid π h k k' (fun i ↦ msg.getD i 0) j).2, k' (rnR π h k k' (fun i ↦ msg.getD i 0) j), rfl,
    isTail_absorbTail π h k k' hA, ?_, ?_, (hD j le_rfl).2, rfl⟩
  · rw [hs]
    exact (hD j le_rfl).1
  · rw [hs]
    rfl

/-- The tails of two absorptions agree up to `n` blocks if their states do before. -/
theorem absorbTail_take_congr (h' : Z → X) {msg : List X} :
    ∀ {n : ℕ}, n ≤ msg.length → (∀ j < n, absorb (spongePerm (h', k, k') π) (msg.take j) =
      absorb (spongePerm (h, k, k') π) (msg.take j)) →
    absorbTail (spongePerm (h', k, k') π) (msg.take n) =
      absorbTail (spongePerm (h, k, k') π) (msg.take n)
  | 0, _, _ => rfl
  | n + 1, hn, hA => by
    rw [List.take_add_one, List.getElem?_eq_getElem (by omega), Option.toList_some,
      absorbTail_append_singleton, absorbTail_append_singleton,
      absorbTail_take_congr h' (by omega) fun j hj ↦ hA j (by omega), hA n (Nat.lt_succ_self n)]

/-- **An absorption with its final `h` value changed.** Let `h'` agree with `h` at the `h`-cells
of the rounds before the last, and hold `cor r (h zfin)` at the final `h`-cell `zfin` (`r` the
final rate after `π`). If `U` holds every `k`, `k'` cell with its key value and every `h`-cell
with its `h'` value, then `U` holds every read of the absorption under `h'`, its tail is the one
under `h`, and its hash is `r + cor r (h zfin)`. -/
theorem held_update_final {msg : List X} (hne : msg ≠ []) (cor : X → X → X) (h' : Z → X)
    (hfin : h' (rnZ π h k k' (fun i ↦ msg.getD i 0) (msg.length - 1)) =
      cor (rnR π h k k' (fun i ↦ msg.getD i 0) (msg.length - 1))
        (h (rnZ π h k k' (fun i ↦ msg.getD i 0) (msg.length - 1))))
    (hoth : ∀ j < msg.length - 1, h' (rnZ π h k k' (fun i ↦ msg.getD i 0) j) =
      h (rnZ π h k k' (fun i ↦ msg.getD i 0) j))
    {U : Dbs X Z}
    (hU : ∀ j < msg.length,
      U.k (rnK π h k k' (fun i ↦ msg.getD i 0) j) =
          some (k (rnK π h k k' (fun i ↦ msg.getD i 0) j)) ∧
        U.k' (rnR π h k k' (fun i ↦ msg.getD i 0) j) =
          some (k' (rnR π h k k' (fun i ↦ msg.getD i 0) j)) ∧
        U.h (rnZ π h k k' (fun i ↦ msg.getD i 0) j) = some (if j = msg.length - 1 then
          cor (rnR π h k k' (fun i ↦ msg.getD i 0) j) (h (rnZ π h k k' (fun i ↦ msg.getD i 0) j))
          else h (rnZ π h k k' (fun i ↦ msg.getD i 0) j))) :
    (∀ e ∈ spongeReads π h' k k' msg, e.HeldBy U) ∧
      absorbTail (spongePerm (h', k, k') π) msg = absorbTail (spongePerm (h, k, k') π) msg ∧
      spongeHash (spongePerm (h', k, k') π) msg =
        rnR π h k k' (fun i ↦ msg.getD i 0) (msg.length - 1) +
          cor (rnR π h k k' (fun i ↦ msg.getD i 0) (msg.length - 1))
            (h (rnZ π h k k' (fun i ↦ msg.getD i 0) (msg.length - 1))) := by
  have hlen : 1 ≤ msg.length := List.length_pos_iff.mpr hne
  have hag : ∀ j, j ≤ msg.length - 1 →
      RnAgree π h k k' h' k k' (fun i ↦ msg.getD i 0) j := fun j hj i hi ↦
    ⟨rfl, rfl, hoth i (by omega)⟩
  have hst : ∀ j ≤ msg.length - 1, absorb (spongePerm (h', k, k') π) (msg.take j) =
      absorb (spongePerm (h, k, k') π) (msg.take j) := fun j hj ↦ by
    rw [absorb_take_eq_rnSt π h' k k' msg j (by omega), absorb_take_eq_rnSt π h k k' msg j
      (by omega), rnSt_congr (hag j hj)]
  refine ⟨fun e he ↦ ?_, ?_, ?_⟩
  · obtain ⟨j, hj, hje⟩ := exists_round_of_mem_spongeReads π h' k k' msg he
    rw [absorb_take_eq_rnSt π h' k k' msg j hj.le] at hje
    have h3 := (congrArg (e ∈ ·) (Quantum.Sphincs.Assembly.roundReads_rnSt π h' k k'
      (fun i ↦ msg.getD i 0) j)).mp hje
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h3
    have hA := hag j (by omega)
    obtain ⟨u1, u2, u3⟩ := hU j hj
    rcases h3 with rfl | rfl | rfl
    · show U.k _ = some _
      rw [rnK_congr hA]
      exact u1
    · show U.k' _ = some _
      rw [rnR_congr hA rfl]
      exact u2
    · show U.h _ = some _
      rw [rnZ_congr hA rfl rfl]
      by_cases hjl : j = msg.length - 1
      · subst hjl
        rw [u3, ite_eq_left rfl, hfin]
      · rw [u3, ite_eq_right hjl, hoth j (by omega)]
  · have ht := absorbTail_take_congr π h k k' h' (n := msg.length) le_rfl
      fun j hj ↦ hst j (by omega)
    rwa [List.take_length] at ht
  · obtain ⟨m, hm⟩ : ∃ m, msg.length = m + 1 := ⟨msg.length - 1, by omega⟩
    have e : msg.length - 1 = m := by omega
    rw [e] at hfin ⊢
    have hA := hag m (by omega)
    have hmsg : absorb (spongePerm (h', k, k') π) msg =
        absorb (spongePerm (h', k, k') π) (msg.take msg.length) := by
      rw [List.take_length]
    show (absorb (spongePerm (h', k, k') π) msg).1 = _
    rw [hmsg, absorb_take_eq_rnSt π h' k k' msg _ le_rfl, hm, rnSt_succ, rnR_congr hA rfl,
      rnZ_congr hA rfl rfl, hfin]

end rounds

/-! ## The digest correction -/

theorem trunc128_cor128 (d : Digest) (r w : X) : trunc128 (r + cor128 d r w) = d := by
  rw [cor128, ← add_assoc, trunc128_add_embed128, BitVec.xor_comm d, xor_xor_cancel_left]

/-! ## The realized ports -/

variable (pub : Pub)

theorem slotBlk_restrictTo (s : Slot) (v : (s : HPos) → XD s) :
    slotBlk pub.seed s (extendVals (restrictTo (valSet (slotNeed s)) v)) =
      slotBlk pub.seed s (valsOf v) := by
  funext j
  unfold slotBlk
  rw [slotInput_congr pub.seed fun p hp ↦ extendVals_restrictTo (val_mem_valSet.mpr hp) v]
  rfl

/-- **The realized ports of a structural slot** are its honest path's cells at the values, the
last `h` value corrected to the value at its output position. -/
theorem realize_slotPorts {s : Slot} (hs : InTable s) (v : (s : HPos) → XD s) :
    (slotPorts pub s).map (LazyProg.realize v) =
      pathCells pub (slotBlk pub.seed s (valsOf v)) (cor128 (valsOf v (slotOutPos s)))
        (nBlk pub.seed s) := by
  rw [slotPorts, realize_pathPorts, slotBlk_restrictTo,
    extendVals_restrictTo (val_mem_valSet.mpr (slotOutPos_mem_slotNeed hs)) v]
  rfl

/-- **The realized ports of `H_msg` call `i`** on `M` at the label `T`: its one block at the
randomizer `v (.rnd M)`, the output corrected to the policy's coordinate. -/
theorem realize_hmsgPorts (pol : DigestPolicy) (T : Finset HPos) (msg : Message) (i : DigestCall)
    (v : (s : HPos) → XD s) :
    (hmsgPorts pub pol T msg i).map (LazyProg.realize v) =
      pathCells pub (slotBlk pub.seed (.hmsg (v (.rnd msg)) msg i) (valsOf v))
        (cor256 (hashOut _ (v (pol.out T msg i)))) 1 := by
  have h0 : HPos.val rootPos ∈ hmsgNeed pol T msg i := by simp [hmsgNeed]
  have h1 : HPos.rnd msg ∈ hmsgNeed pol T msg i := by simp [hmsgNeed]
  have h2 : pol.out T msg i ∈ hmsgNeed pol T msg i := by simp [hmsgNeed]
  rw [hmsgPorts, realize_pathPorts, extendRnd_restrictTo h1, extendOut_restrictTo h2]
  have hb : slotBlk pub.seed (.hmsg (v (.rnd msg)) msg i)
      (extendVals (restrictTo (hmsgNeed pol T msg i) v)) =
        slotBlk pub.seed (.hmsg (v (.rnd msg)) msg i) (valsOf v) := by
    funext j
    unfold slotBlk
    rw [slotInput_congr pub.seed (g := valsOf v) fun p hp ↦ by
      simp only [slotNeed, Finset.mem_singleton] at hp
      subst hp
      exact extendVals_restrictTo h0 v]
  rw [hb]

/-! ## Exempted structural slots -/

/-- `U` holds the cells of round `j` of the blocks `b` with their programmed values. -/
def RoundHeld (U : Dbs X Z) (b : ℕ → X) (last : ℕ) (cor : X → X → X) (j : ℕ) : Prop :=
  U.k (cellK pub b j).1 = some (cellK pub b j).2 ∧
    U.k' (cellK' pub b j).1 = some (cellK' pub b j).2 ∧
    U.h (cellH pub b last cor j).1 = some (cellH pub b last cor j).2

/-- The final `h`-cell of slot `s`'s path at the values is none of its earlier `h`-cells. -/
def FinalSep (v : (s : HPos) → XD s) (s : Slot) : Prop :=
  ∀ j < nBlk pub.seed s - 1,
    rnZ pub.perm pub.keys.1 pub.keys.2.1 pub.keys.2.2 (slotBlk pub.seed s (valsOf v)) j ≠
      rnZ pub.perm pub.keys.1 pub.keys.2.1 pub.keys.2.2 (slotBlk pub.seed s (valsOf v))
        (nBlk pub.seed s - 1)

/-- The public data of the path events (`Quantum.Sphincs.Assembly.PathBad`): `PK.seed`, `π`, `k`,
`k'`. -/
def Pub.xw : XW :=
  (pub.seed, pub.perm, pub.keys.2.1, pub.keys.2.2)

/-- **Paths avoiding the output cells separate the final cell**: off PathBad's event at the template
data, every structural slot has `FinalSep`. -/
theorem finalSep_of_pathsAvoid (v : (s : HPos) → XD s) {s : Slot} (hs : InTable s)
    (h : PathsAvoid pub.xw pub.keys.1 (valsOf v)) : FinalSep pub v s := by
  intro j hj
  have hp := mem_xI.mpr (inPos_slotOutPos hs)
  have hj' := h _ hp _ hp j (by
    rw [xLen, outSlot_slotOutPos hs]
    show j + 1 < nBlk pub.seed s
    omega)
  rw [outSlot_slotOutPos hs] at hj'
  exact hj'

/-- **A structural slot's honest path is held** by a database holding every cell its ports
program, if its final `h`-cell is none of its earlier `h`-cells: the witness is the public `h`
with the corrected final value. -/
theorem heldIn_of_cells (v : (s : HPos) → XD s) (s : Slot) {U : Dbs X Z}
    (hU : ∀ j < nBlk pub.seed s, RoundHeld pub U (slotBlk pub.seed s (valsOf v))
      (nBlk pub.seed s - 1) (cor128 (valsOf v (slotOutPos s))) j)
    (hsep : FinalSep pub v s) : (evData pub v).HeldIn U s := by
  have hlen := length_blocks_slotInput pub.seed s (valsOf v)
  have hne : blocks (slotInput pub.seed s (valsOf v)) ≠ [] := by
    rw [← List.length_pos_iff, hlen]
    exact nBlk_pos _ _
  have hsep' : ∀ j < (blocks (slotInput pub.seed s (valsOf v))).length - 1,
      rnZ pub.perm pub.keys.1 pub.keys.2.1 pub.keys.2.2
          (fun i ↦ (blocks (slotInput pub.seed s (valsOf v))).getD i 0) j ≠
        rnZ pub.perm pub.keys.1 pub.keys.2.1 pub.keys.2.2
          (fun i ↦ (blocks (slotInput pub.seed s (valsOf v))).getD i 0)
          ((blocks (slotInput pub.seed s (valsOf v))).length - 1) := fun j hj ↦ by
    rw [hlen] at hj ⊢
    exact hsep j hj
  obtain ⟨hr, ht, hh⟩ := held_update_final pub.perm pub.keys.1 pub.keys.2.1 pub.keys.2.2 hne
    (cor128 (valsOf v (slotOutPos s))) (Function.update pub.keys.1 _ _)
    (Function.update_self _ _ _) (fun j hj ↦ Function.update_of_ne (hsep' j hj) _ _) (U := U)
    (fun j hj ↦ by
      rw [hlen] at hj ⊢
      obtain ⟨u1, u2, u3⟩ := hU j hj
      exact ⟨u1, u2, (congrArg U.h (cellH_fst pub _ _ _ j)).symm.trans
        (u3.trans (congrArg some (cellH_snd pub _ _ _ j)))⟩)
  refine ⟨_, hr, ht, ?_⟩
  exact (congrArg trunc128 hh).trans (trunc128_cor128 _ _ _)

/-- **A programmed structural slot is exempted** (Events' `exS`): obligation (1) of the event. -/
theorem mem_exS_of_cells (v : (s : HPos) → XD s) {s : Slot} (hs : InTable s) {W : Hw X Z}
    (hU : ∀ j < nBlk pub.seed s, RoundHeld pub W.toDbs (slotBlk pub.seed s (valsOf v))
      (nBlk pub.seed s - 1) (cor128 (valsOf v (slotOutPos s))) j)
    (hsep : FinalSep pub v s) : s ∈ (evData pub v).exS W :=
  ⟨hs, heldIn_of_cells pub v s hU hsep⟩

/-- **The head-tail of a structural slot's final `h`-cell**: with the `k`- and `k'`-cells of every
round held with their key values, the slot's honest tail heads to its final `h`-cell (Events'
`not_mem_bad_programH_honest`); earlier rounds by `isHeadTail_take_succ_rn`. -/
theorem isHeadTail_slot (v : (s : HPos) → XD s) (s : Slot) (cor : X → X → X) {D : Dbs X Z}
    (hD : ∀ j < nBlk pub.seed s,
      D.k (cellK pub (slotBlk pub.seed s (valsOf v)) j).1 =
          some (cellK pub (slotBlk pub.seed s (valsOf v)) j).2 ∧
        D.k' (cellK' pub (slotBlk pub.seed s (valsOf v)) j).1 =
          some (cellK' pub (slotBlk pub.seed s (valsOf v)) j).2) :
    IsHeadTail pub.perm D ((evData pub v).honTail s)
      (cellH pub (slotBlk pub.seed s (valsOf v)) (nBlk pub.seed s - 1) cor
        (nBlk pub.seed s - 1)).1
      (cellK' pub (slotBlk pub.seed s (valsOf v)) (nBlk pub.seed s - 1)).1 := by
  have hl := length_blocks_slotInput pub.seed s (valsOf v)
  have hp := nBlk_pos pub.seed s
  have h := isHeadTail_take_succ_rn pub.perm pub.keys.1 pub.keys.2.1 pub.keys.2.2
    (msg := blocks (slotInput pub.seed s (valsOf v))) (j := nBlk pub.seed s - 1) (by omega)
    fun j hj ↦ hD j (by omega)
  rw [List.take_of_length_le (by omega)] at h
  rw [cellH_fst]
  exact h

/-! ## `H_msg` head-tails -/

theorem length_blocks_hmsg (seed : PublicParameter) (R : Randomizer) (msg : Message)
    (i : DigestCall) (f : ValPos → Digest) :
    (blocks (slotInput seed (.hmsg R msg i) f)).length = 1 := by
  rw [length_blocks]
  show (messageDigestInput _ _ _ _ _).length / 136 + 1 = 1
  rw [length_messageDigestInput]

/-- **The head-tail of an `H_msg` call's `h`-cell**: with the `k`- and `k'`-cells of its round held
with their key values, the call's honest tail heads to the `h`-cell its ports program, with the
rate after `π`. Obligation (2) of the event, before a call-0 `h` program. -/
theorem isHeadTail_hmsg (v : (s : HPos) → XD s) (R : Randomizer) (msg : Message)
    (i : DigestCall) (cor : X → X → X) {D : Dbs X Z}
    (hk : D.k (cellK pub (slotBlk pub.seed (.hmsg R msg i) (valsOf v)) 0).1 =
      some (cellK pub (slotBlk pub.seed (.hmsg R msg i) (valsOf v)) 0).2)
    (hk' : D.k' (cellK' pub (slotBlk pub.seed (.hmsg R msg i) (valsOf v)) 0).1 =
      some (cellK' pub (slotBlk pub.seed (.hmsg R msg i) (valsOf v)) 0).2) :
    IsHeadTail pub.perm D ((evData pub v).honTail (.hmsg R msg i))
      (cellH pub (slotBlk pub.seed (.hmsg R msg i) (valsOf v)) 0 cor 0).1
      (cellK' pub (slotBlk pub.seed (.hmsg R msg i) (valsOf v)) 0).1 := by
  have hl := length_blocks_hmsg pub.seed R msg i (valsOf v)
  have h := isHeadTail_take_succ_rn pub.perm pub.keys.1 pub.keys.2.1 pub.keys.2.2
    (msg := blocks (slotInput pub.seed (.hmsg R msg i) (valsOf v))) (j := 0) (by omega)
    fun j hj ↦ by
      obtain rfl : j = 0 := Nat.le_zero.mp hj
      exact ⟨hk, hk'⟩
  rw [List.take_of_length_le (by omega)] at h
  rw [cellH_fst]
  exact h

end Quantum.Sphincs.Assembly

end
