/-
  LeanVM.Guest.EndExecLoop

  A loop helper's tail call in the honest tree: its next frame through the next-frame cell of its
  `JUMP`, its header copied, its arguments.
-/

module

public import LeanVM.Guest.Bridge.JumpCells
public import LeanVM.Guest.Bridge.JumpCells.All
public import LeanVM.Guest.CoreMode.Core
public import LeanVM.Guest.ExecDecodable

/-!
# A loop's tail call, of the honest tree

`tailF_of`: for function `j`'s frame `fp` holding what its check reads (`FrameHolds`), whose path's
last call is entered, and a `JUMP` of its code through a next-frame cell `q` (`nextAt`): `j` is a loop
(`jcData`'s next-frame clause), the last call's frame is right after this one (`FrameHolds.tail`),
which cell `q` names; its header is this frame's and its arguments are the call's
(`FrameHolds.kid`). `jump_of_fetch`: a small `JUMP` fetched at an offset of a guest function is its
instruction there.
-/

namespace LeanVM.Guest.Bridge

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B2C
open LeanVM.Guest.Check (getF)

public section

/-- **A loop's tail call**, of a frame holding what its check reads. -/
theorem tailF_of {κ : ℕ} {L : MemoryImage κ} {j fp : ℕ} {σ : Val} {es : List Ev} {vs : List V} {kfps : List ℕ}
    {hdr : E × E} (hj1 : 1 ≤ j) (hj2 : j < nFns) (hF : FrameHolds L j fp σ es vs kfps hdr) {i : ℕ} {c : Call}
    (hc : (calls es)[i]? = some c) (hi : i + 1 = (calls es).length) {off oc od q S : ℕ}
    (hcode : (fnOf j).code[off]? = some (.jump oc od q)) (hso : (ctxOf j).statOf q = some (.fpg S)) (hS : S ≠ 0) :
    CoreMode.Rd L fp q = some (ofK (Parameters.g ^ (fp + S))) ∧ CoreMode.Rd L (fp + S) 0 = CoreMode.Rd L fp 0 ∧
      CoreMode.Rd L (fp + S) 1 = CoreMode.Rd L fp 1 ∧
      ∀ k (hk : k < c.args.length), CoreMode.Rd L (fp + S) (2 + k) = some (σ c.args[k]) := by
  have hrd : ∀ x o, CoreMode.Rd L x o = cellAt L x o := fun x o ↦ by
    simp [CoreMode.Rd, cellAt, addressOfIndex, pow_add]
  have hd := JumpCells.jcData_all j hj1 (by have : nFns = fn_count% := rfl; omega)
  unfold jcData jcDataD at hd
  simp only [Bool.and_eq_true] at hd
  obtain ⟨⟨⟨⟨⟨⟨⟨hstat, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hnext⟩ := hd
  have hm : (q, PC.fpg S) ∈ (plumbOf j).stat := statOf_ofData hso
  have hls : (coreOf j).loop = true ∧ S = fsN j := by
    rcases Bool.or_eq_true _ _ |>.mp hnext with hn | hn
    · have := List.all_eq_true.mp hn _ hm
      simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at this
      rcases this with h0 | h0
      · exact absurd h0 hS
      · exact h0
    · have hmem : OffsetInstruction.jump oc od q ∈ (fnOf j).code := List.mem_of_getElem? hcode
      have := List.all_eq_true.mp (List.all_eq_true.mp hn _ hmem) _ hm
      simp only [beq_self_eq_true, Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq,
        Bool.and_eq_true] at this
      rcases this with h0 | h0
      · exact absurd h0 hS
      · exact h0
  have hi' : i < (calls es).length := (List.getElem?_eq_some_iff.mp hc).1
  obtain ⟨kfp, hkfp⟩ : ∃ kfp, kfps[i]? = some kfp :=
    ⟨_, List.getElem?_eq_getElem (by rw [hF.len]; exact hi')⟩
  have hlast : kfps.getLast? = some kfp := by
    rw [List.getLast?_eq_getElem?, hF.len, ← hi, Nat.add_sub_cancel]; exact hkfp
  have hkv := hF.tail hls.1 kfp hlast
  obtain ⟨hk0, hk1, hka, -⟩ := hF.kid i c kfp hc hkfp
  have hkh : kidHdr j fp hdr es i = hdr := by
    unfold kidHdr
    rw [hc]
    dsimp only
    rw [ite_eq_left ⟨hls.1, hi⟩]
  have hb := List.all_eq_true.mp hstat _ hm
  simp only [cellIn, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hb
  rw [hls.2, ← hkv]
  refine ⟨?_, ?_, ?_, fun k hk ↦ ?_⟩
  · rw [hrd, cellAt, hF.stat _ hm hb.1.1 hb.1.2, hkv, ← hls.2]
    simp [PC.word, addressOfIndex, hls.2]
  · rw [hrd, hrd, cellAt, cellAt, hk0, hkh, hF.hdr0]
  · rw [hrd, hrd, cellAt, cellAt, hk1, hkh, hF.hdr1]
  · rw [hrd, cellAt, ← hka k hk]

/-- **A small `JUMP` fetched at an offset of a guest function** is its instruction there. -/
theorem jump_of_fetch {f : CompiledFunction} (hf : f ∈ Data.functions) {off oc od q : ℕ}
    (hoff : off < f.code.length) (hoc : oc < 2 ^ 28) (hod : od < 2 ^ 28) (hq : q < 2 ^ 28)
    (h : guestProgram.fetch (addressOfIndex (f.entryPc + off)) =
      some (OffsetInstruction.jump oc od q).toLeanIsaInstruction) :
    f.code[off]? = some (.jump oc od q) := by
  have hget := List.getElem?_eq_getElem hoff
  have hfe := (Exec.guest_fetches hf off _ hget).1
  rw [h, Option.some.injEq] at hfe
  have hsm : Mode.offSmall f.code[off] = true := by
    have := List.all_eq_true.mp Mode.functions_offSmall f hf
    have hm : f.code[off] ∈ f.chunks.flatten := List.getElem_mem hoff
    obtain ⟨l, hl, hx⟩ := List.mem_flatten.mp hm
    exact List.all_eq_true.mp (List.all_eq_true.mp this l hl) _ hx
  rw [hget, Option.some.injEq]
  generalize f.code[off] = ins at hfe hsm
  cases ins with
  | jump a b c =>
    simp only [OffsetInstruction.toLeanIsaInstruction, LeanIsaInstruction.jump.injEq] at hfe
    simp only [Mode.offSmall, Bool.and_eq_true, decide_eq_true_eq] at hsm
    obtain ⟨h1, h2, h3⟩ := hfe
    have e : ∀ x y : ℕ, x < 2 ^ 28 → y < 2 ^ 28 → addressOfIndex x = addressOfIndex y → x = y :=
      fun x y hx hy hxy ↦ Prover.Exec.gpow_inj (by omega) (by omega) hxy
    rw [e _ _ hoc hsm.1.1 h1, e _ _ hod hsm.1.2 h2, e _ _ hq hsm.2 h3]
  | _ => simp [OffsetInstruction.toLeanIsaInstruction] at hfe

end

end LeanVM.Guest.Bridge
