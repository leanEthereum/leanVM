/-
  LeanVM.Guest.B1.Sig.SphincsLayersComplete

  A layer of `verify_sig_lean_sphincs` (`sp_layer`, `lean_ethereum.py:3936-3948` at leanVM main 40f877dc,
  after its counter) is complete: its encoding hashed, the key's leaf by the call of `sp_wots`, the
  path to the root.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsForsComplete
public import LeanVM.Guest.B1.Sig.SphincsSoundLayer

/-!
# A layer, complete

* `encOf`: the encoding digest of `P`, `A0`, `key + WOTS_ENC`, the value signed and the counter
  `N`'s four bytes (`sLayerEnc_sound`'s);
* `call_complete`: a call returning one word, the call relation holding;
* `sHtLayer_complete`: the layer, the call returning `leaf` at the encoding: its root is
  `pFold (pNodeE …)` from `leaf`.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier (eOfNat)

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-- A layer's encoding digest (`sLayerEnc_sound`). -/
def encOf (pp a0 key signed : E) (N : Nat) : E :=
  (digestHalves (keccak256 (cellsBytes [pp, a0, key + lit (7 * 2 ^ 24), signed] ++
    leBytes N 4))).1

/-- **A call returning one word completes** when the call relation holds of its arguments. -/
theorem call_complete {f : String} {args : List V} {d : Nat} (σ : Val) (w : E)
    (hargs : NumBelow d args) (hC : C f (args.map σ) [w]) :
    Completes C rd d (d + 1) [.call f args [.n d]] σ (fun σ' => σ' (.n d) = w) := by
  refine ⟨Function.update σ (.n d) w, fun v hv => Function.update_of_ne (hv d le_rfl (by omega)) _ _,
    Function.update_self .., fun next kret hn => ⟨?_, hn⟩⟩
  have : args.map (Function.update σ (.n d) w) = args.map σ := List.map_congr_left fun v hv => by
    obtain ⟨j, hj, rfl⟩ := hargs v hv
    exact Function.update_of_ne (by simp; omega) _ _
  rw [this]
  simpa using hC

/-- **A layer completes** from base `b`, its counter `ctr` the word `N < 2^32`, the call of
`sp_wots` at the encoding returning `leaf`: its root is `pFold` of `pNodeE` from `leaf`, the
siblings `sib`. -/
theorem sHtLayer_complete {pad : Nat} {pp a0 key signed ctr : V} {bit val : Nat → V}
    {off e height b N : Nat} (hh : height ≤ 16) (he : e < 2 ^ height) {sib : Nat → E}
    (σ : Val) (hpb : pad + 5 ≤ b) (hpp : NBv b pp)
    (ha0 : NBv b a0) (hkey : NBv b key) (hsg : NBv b signed) (hct : NBv b ctr)
    (hbn : ∀ j < height, NBv b (bit (off + j))) (hvn : ∀ j < height, NBv b (val (off + j)))
    (hp : PadOK σ pad) (hN : N < 2 ^ 32)
    (hctr : σ ctr = eOfNat N)
    (hbit : ∀ j < height, σ (bit (off + j)) = if e.testBit j then 1 else 0)
    (hval : ∀ j < height, σ (val (off + j)) = eOfNat (e >>> j)) {leaf : E}
    (hcall : C "sp_wots" [σ pp, σ a0, σ key, encOf (σ pp) (σ a0) (σ key) (σ signed) N] [leaf]) :
    Completes C rd b (sHtLayer pad pp a0 key signed ctr bit val off height b).2.1
      (sHtLayer pad pp a0 key signed ctr bit val off height b).1 σ
      (fun σ' => AgreeBelow b σ σ' ∧
        σ' (sHtLayer pad pp a0 key signed ctr bit val off height b).2.2 =
          pFold (pNodeE (σ pp) (σ a0) e sib) height leaf) := by
  rw [sHtLayer_split]
  simp only [List.append_assoc]
  have hcells : ∀ c ∈ [KC.cell pp, .cell a0, .cell (.n (b + 1)), .cell signed, .cell ctr],
      KCb (b + 2) c := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro c (rfl | rfl | rfl | rfl | rfl)
    · exact hpp.mono' (by omega)
    · exact ha0.mono' (by omega)
    · exact ⟨b + 1, by omega, rfl⟩
    · exact hsg.mono' (by omega)
    · exact hct.mono' (by omega)
  have hkn := (kMsg_nb (pad := pad) (len := 68) (tailRun := false) (by omega) hcells).1
  rw [(kEnc_shape ..).1] at hkn
  have hs1 : SeqOK b [cst b (lit (7 * 2 ^ 24)), addS (.n (b + 1)) key (.n b)] (b + 2) :=
    ⟨rfl, ⟨rfl, hkey.mono' (by omega), ⟨b, by omega, rfl⟩⟩, rfl⟩
  have hpre_nb : NumBelow (b + 10) (Stmt.valsList (layerPre pad pp a0 key signed ctr b)) := by
    simp only [layerPre, valsList_append]
    exact (hs1.numBelow.mono (by omega)).append hkn
  have hpath_le := sPath_le pad pp a0 bit val off height 0 (.n (b + 10)) (b + 11)
  -- the encoding
  have hpre : Completes C rd b (b + 10) (layerPre pad pp a0 key signed ctr b) σ
      (fun σ' => AgreeBelow b σ σ' ∧ σ' (.n (b + 9)) = encOf (σ pp) (σ a0) (σ key) (σ signed) N) := by
    have h := Completes.seqThen (C := C) (rd := rd) (Q := fun _ => True) hs1 (hi := b + 10)
      (by omega) (fun σ1 he1 _ => by
        have hag1 : AgreeBelow b σ σ1 := he1.agree
        have hk := (kMsg_complete (C := C) (rd := rd) σ1 (hp.congr hpb hag1) (by omega)
          (len := 68) (tailRun := false) hcells (fun h => by simp at h)).1
        rw [(kEnc_shape ..).1] at hk
        exact hk)
    refine (h.withAtoms (by simp only [atomsOnly_append, kMsg_atoms]; rfl)).withExt.mono le_rfl
      le_rfl (fun σ' ⟨⟨_, hA⟩, he'⟩ => ⟨he'.agree, ?_⟩)
    have t : ∀ v, NBv b v → σ' v = σ v := fun v hv => he'.agree.apply hv
    rw [sLayerEnc_sound (hp.congr hpb he'.agree) hN (by rw [t _ hct]; exact hctr) hA, t _ hpp,
      t _ ha0, t _ hkey, t _ hsg, encOf]
  refine Completes.append (m := b + 10) (by omega) (by omega) hpre_nb hpre
    (fun σ1 he1 ⟨hag1, henc⟩ => ?_)
  have t1 : ∀ v, NBv b v → σ1 v = σ v := fun v hv => hag1.apply hv
  refine Completes.append (m := b + 11) (by omega) (by omega)
    (by simp only [valsList_cons, valsList_nil, Stmt.vals, List.append_nil]
        intro v hv
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with (rfl | rfl | rfl | rfl) | rfl
        · exact hpp.mono' (by omega)
        · exact ha0.mono' (by omega)
        · exact hkey.mono' (by omega)
        · exact ⟨b + 9, by omega, rfl⟩
        · exact ⟨b + 10, by omega, rfl⟩)
    (call_complete σ1 leaf (by
        intro v hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl
        · exact hpp.mono' (by omega)
        · exact ha0.mono' (by omega)
        · exact hkey.mono' (by omega)
        · exact ⟨b + 9, by omega, rfl⟩)
      (by simp only [List.map_cons, List.map_nil, t1 _ hpp, t1 _ ha0, t1 _ hkey, henc]; exact hcall))
    (fun σ2 he2 hl2 => ?_)
  have hag2 : AgreeBelow (b + 10) σ1 σ2 := he2.agree
  have t2 : ∀ v, NBv b v → σ2 v = σ v := fun v hv =>
    (hag2.apply (hv.mono' (by omega))).trans (t1 v hv)
  have hpv := sPath_complete_val (C := C) (rd := rd) (pad := pad) (pp := pp) (a0 := a0) (bit := bit)
    (val := val) (off := off) (sib := sib) hh he (cur := .n (b + 10)) (x := b + 11) σ2 (by omega)
    (hpp.mono' (by omega)) (ha0.mono' (by omega)) (fun j hj => (hbn j hj).mono' (by omega))
    (fun j hj => (hvn j hj).mono' (by omega)) ⟨b + 10, by omega, rfl⟩
    (hp.congr hpb fun j hj => by rw [t2 (.n j) ⟨j, hj, rfl⟩])
    (fun j hj => by rw [t2 _ (hbn j hj)]; exact hbit j hj)
    (fun j hj => by rw [t2 _ (hvn j hj)]; exact hval j hj)
  refine hpv.mono le_rfl le_rfl (fun σ' ⟨hag', hr'⟩ => ⟨?_, ?_⟩)
  · exact fun j hj => (t2 (.n j) ⟨j, hj, rfl⟩).symm.trans (hag' j (by omega))
  · rw [hr', t2 _ hpp, t2 _ ha0, hl2]

end
end LeanVM.Guest.B1.Sig
