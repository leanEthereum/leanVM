/-
  LeanVM.Guest.B1.Digest.ClaimListComplete

  `claim_list_digest`, completely: its meaning's claims, and the memory an honest run leaves at
  its chain buffer, give its core IR relation.
-/

module

public import LeanVM.Guest.B1.Digest.ClaimListCLast
public import LeanVM.Guest.B1.Digest.ClaimListCBig
public import LeanVM.Guest.B1.Digest.CompleteSmall

/-!
# `claim_list_digest`, completely

`ClaimChainMem rd chain entries n`: the memory an honest run leaves at its chain buffer `chain`,
the sponge state after each frame (`136` claims, then `17`) at `chain · g^(13t)`. From it,
`cl_bigBlocks` and `cl_grpBlocks` give the frame loops' blocks (`frame_block`, `grp_block`) that
`guard_complete` runs.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

variable {rd : Reader}

/-- The claims hashed after `t` frames of a list with `a` big frames, in groups of `17`: eight a
big frame, one a group frame. -/
def clU (a t : ℕ) : ℕ := 8 * min t a + (t - a)

/-- **The memory an honest run of `claim_list_digest` leaves** at its chain buffer `chain`: after
`t ≤ a + b` frames (`n = 136a + 17b + c`, the big frames first), the sponge state after the first
`68 · clU a t` cells at `entries`, at `chain · g^(13t)`. -/
def ClaimChainMem (rd : Reader) (chain entries : E) (n : ℕ) : Prop :=
  ∀ t ≤ n / 136 + n % 136 / 17, StateAt rd (chain * gen ^ (13 * t)) 0
    (absorbChunks (8 * clU (n / 136) t) zeroState
      (cellsBytes (memRun rd entries (68 * clU (n / 136) t))))

theorem readsAt_take' {p : E} {cells : List E} (hr : ReadsAt rd p cells) (k : ℕ) :
    ReadsAt rd p (cells.take k) := fun i hi => by
  rw [List.getElem_take]; exact hr i (by simp at hi; omega)

theorem readsAt_drop' {p : E} {cells : List E} (hr : ReadsAt rd p cells) (k : ℕ) :
    ReadsAt rd (p * gen ^ k) (cells.drop k) := fun i hi => by
  rw [loadHolds_mul_gen_pow, List.getElem_drop]; exact hr _ (by simp at hi; omega)

theorem memRun_take {p : E} {cells : List E} (hr : ReadsAt rd p cells) {k : ℕ}
    (hk : k ≤ cells.length) : memRun rd p k = cells.take k := by
  rw [readsAt_memRun (readsAt_take' hr k), List.length_take, Nat.min_eq_left hk]

theorem canon_take {cells : List E} (hc : AllCanonical cells) (k : ℕ) : AllCanonical (cells.take k) :=
  fun c h => hc c (List.mem_of_mem_take h)

theorem canon_drop {cells : List E} (hc : AllCanonical cells) (k : ℕ) : AllCanonical (cells.drop k) :=
  fun c h => hc c (List.mem_of_mem_drop h)

theorem grpc_shapeF {j : ℕ} {f : String} {m c0 st0 ep : ℕ}
    (h : grpcOk (coreProgram.getD j default) f m c0 st0 ep = true) :
    loopShapeF (coreProgram.getD j default) f = true := by
  simp only [grpcOk, Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1.1.1

/-- **A frame from the chain's memory**: the states before and after `d` units of `68` cells
(units `u` to `u + d`) give a frame loop's block (`grp_block`) at the counter `x`. -/
theorem frame_block {j : ℕ} {f : String} {m c0 st0 ep nb d : ℕ}
    (hok : grpOk (coreProgram.getD j default) f m c0 st0 ep = true)
    (hcok : grpcOk (coreProgram.getD j default) f m c0 st0 ep = true)
    (hnb : (grpSpec m c0 st0 (loopAtoms (coreProgram.getD j default))).nb = nb) (hep : ep ≠ 9)
    (hm : 4 * m = 68 * d) (hnbd : nb = 8 * d) {N chain' entries' entries x : E} {u : ℕ}
    {cells : List E} (hr : ReadsAt rd entries cells) (hc : AllCanonical cells)
    (hu : 68 * (u + d) ≤ cells.length)
    (hS : StateAt rd (chain' * x ^ 13) 0
      (absorbChunks (8 * u) zeroState (cellsBytes (cells.take (68 * u)))))
    (hS1 : StateAt rd (chain' * x ^ 13) 13
      (absorbChunks (8 * (u + d)) zeroState (cellsBytes (cells.take (68 * (u + d))))))
    (hE : entries' * x ^ (4 * m) = entries * gen ^ (68 * u)) :
    LoopBlock rd (coreProgram.getD j default) x N [chain', entries'] := by
  have hpre : (cellsBytes (cells.take (68 * u))).length = rate * (8 * u) := by
    rw [length_cellsBytes, List.length_take, Nat.min_eq_left (by omega)]
    show 16 * (68 * u) = 136 * (8 * u); omega
  refine grp_block hok hcok hnb hep hpre hS (cells := (cells.drop (68 * u)).take (4 * m))
    (by simp; omega) ?_ (canon_take (canon_drop hc _) _) ?_
  · rw [hE]; exact readsAt_take' (readsAt_drop' hr _) _
  · rw [show 68 * (u + d) = 68 * u + 4 * m by omega, List.take_add, cellsBytes_append,
      show 8 * (u + d) = 8 * u + nb by omega] at hS1
    exact hS1

/-- The big frames: `__loop15`'s block at every big frame below `a = n / 136`. -/
theorem cl_bigBlocks {chain entries : E} {n : ℕ} {cells : List E} (hl : cells.length = 4 * n)
    (hr : ReadsAt rd entries cells) (hc : AllCanonical cells) (hmem : ClaimChainMem rd chain entries n) :
    ∀ q < n / 136, LoopBlock rd (coreProgram.getD 359 default) (gen ^ q) (gen ^ (n / 136))
      [chain, entries] := by
  intro q hq
  have hS := hmem q (by omega)
  have hS1 := hmem (q + 1) (by omega)
  have hu0 : clU (n / 136) q = 8 * q := by unfold clU; rw [Nat.min_eq_left (by omega)]; omega
  have hu1 : clU (n / 136) (q + 1) = 8 * q + 8 := by
    unfold clU; rw [Nat.min_eq_left (by omega)]; omega
  rw [hu0, memRun_take hr (by omega)] at hS
  rw [hu1, memRun_take hr (by omega)] at hS1
  refine frame_block big_ok grpc_big big_nb (by decide) (d := 8) (by norm_num) rfl hr hc (u := 8 * q)
    (by omega) (by rw [gen_pow_pow]; exact hS) (fun c => ?_) (by rw [gen_pow_pow]; congr 2; ring)
  have := hS1 c
  rw [gen_pow_pow, loadHolds_mul_gen_pow]
  rw [loadHolds_mul_gen_pow, show 13 * (q + 1) + (0 + c.val) = 13 * q + (13 + c.val) by ring] at this
  exact this

/-- The groups: `__loop16`'s block at every group below `b = n % 136 / 17`, from
`chain · g^(13a)` and `entries · g^(544a)`. -/
theorem cl_grpBlocks {chain entries : E} {n : ℕ} {cells : List E} (hl : cells.length = 4 * n)
    (hr : ReadsAt rd entries cells) (hc : AllCanonical cells) (hmem : ClaimChainMem rd chain entries n) :
    ∀ q < n % 136 / 17, LoopBlock rd (coreProgram.getD 360 default) (gen ^ q) (gen ^ (n % 136 / 17))
      [chain * gen ^ (13 * (n / 136)), entries * gen ^ (544 * (n / 136))] := by
  intro q hq
  set a := n / 136 with ha
  have hn : n = 136 * a + n % 136 := (Nat.div_add_mod n 136).symm
  have hS := hmem (a + q) (by omega)
  have hS1 := hmem (a + q + 1) (by omega)
  have hu0 : clU a (a + q) = 8 * a + q := by unfold clU; rw [Nat.min_eq_right (by omega)]; omega
  have hu1 : clU a (a + q + 1) = 8 * a + q + 1 := by
    unfold clU; rw [Nat.min_eq_right (by omega)]; omega
  rw [hu0, memRun_take hr (by omega)] at hS
  rw [hu1, memRun_take hr (by omega)] at hS1
  refine frame_block grp_ok grpc_ok grp_nb (by decide) (d := 1) (by norm_num) rfl hr hc
    (u := 8 * a + q) (by omega) ?_ (fun c => ?_) ?_
  · rw [gen_pow_pow, mul_assoc, ← pow_add, show 13 * a + 13 * q = 13 * (a + q) by ring]; exact hS
  · have := hS1 c
    rw [gen_pow_pow, mul_assoc, ← pow_add, loadHolds_mul_gen_pow]
    rw [loadHolds_mul_gen_pow,
      show 13 * (a + q + 1) + (0 + c.val) = 13 * a + 13 * q + (13 + c.val) by ring] at this
    exact this
  · rw [gen_pow_pow, mul_assoc, ← pow_add]; congr 2; ring

theorem cl_param (σ : Val) : (Fn.params Data.core23).map σ = [σ (.n 0), σ (.n 1)] := rfl

end
end LeanVM.Guest.B1.Digest
