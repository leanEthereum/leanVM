/-
  LeanVM.Guest.Backend.Complete.FrameOp

  The walk's instance gives its straight-line instructions' words (`OpOK`): an instruction's
  relation on the frame words `Ψ` is its `HW`/`JW` on every memory holding `Ψ` patched at the
  temporaries' cells.
-/

module

public import LeanVM.Guest.Backend.Complete.FrameBlock
public import LeanVM.Guest.Backend.Complete.FrameHW
public import LeanVM.Guest.Memory.Retemp

/-!
# A straight-line instruction's relation gives its words

For the walk's instance `I = instOf W tf pf fp hdr σ es` and a valuation `σ'` agreeing with it off
the temporaries, the memories `AgOf … ⟨patchT I Ψ σ', kh⟩` hold `Ψ` at every cell but the
temporaries' (`FrameRd`) and are readers of the instance (`I.Rd`: the path's events name no
temporary but a range check's own, so their relations without those agree under `σ'` and `I.σ`).
An instruction of the placement names no temporary's cell but a temporary's `DEREF` into it
(`Inst.Ok.tops`), whose pointer cell is no temporary's (`tptr`); that `DEREF` reads the
temporary's word, which the patched cell holds (`tinj`: the cell is that temporary's only).
-/

namespace LeanVM.Guest.Backend.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- An atom with no temporaries holds under a valuation agreeing on the values it names. -/
theorem atom_holds_of {rd : Reader} {σ σ' : Val} {a : Atom} (hT : atomTmps a = [])
    (h : ∀ v ∈ atomUses a, σ' v = σ v) (he : a.Holds rd σ') : a.Holds rd σ :=
  (atom_holds_congr a fun v hv => h v (by simpa [hT] using hv)).mp he

/-- **An event's relation without its temporaries' loads**, from its relation under a valuation
agreeing on the values it names. -/
theorem evNT_of_holds {rd : Reader} {σ σ' : Val} {e : Ev} (h : ∀ v ∈ e.uses, σ' v = σ v)
    (he : e.Holds rd σ') : evNT rd σ e := by
  cases e with
  | atom a =>
      cases a with
      | rangeCheck x y t1 t2 k =>
          obtain ⟨h1, h2, h3⟩ := he
          simp only [Ev.uses, atomUses, List.mem_cons, List.not_mem_nil, or_false,
            forall_eq_or_imp, forall_eq] at h
          refine ⟨?_, ?_, ?_⟩
          · rw [← h.1]; exact h1.1
          · rw [← h.1, ← h.2.1, ← h.2.2]; exact h2
          · rw [← h.2.1]; exact h3.1
      | touch t p =>
          have hp : σ' p = σ p := h p (by simp [Ev.uses, atomUses])
          show IsInK (σ p)
          rw [← hp]
          exact he.1
      | _ =>
          simp only [Ev.Holds] at he
          simp only [Ev.uses] at h
          simp only [evNT, holdsNT]
          exact atom_holds_of rfl h he
  | inK c =>
      show IsInK (σ c)
      rw [← h c (by simp [Ev.uses])]
      exact he
  | call _ _ _ => trivial
  | skip _ _ => trivial

/-- The frame words patched at the temporaries' cells are `Ψ`'s at every other cell. -/
theorem fwd_patch {I : Inst} {Ψ : ℕ → E} {σ' : Val} {kh : ℕ → E × E} {n : ℕ} (hn : ¬ I.tc n) :
    fwd I.hdr ⟨patchT I Ψ σ', kh⟩ n = fw I Ψ n := by
  simp [fwd, fw, patchT, hn]

/-- **The walk's instance gives its straight-line instructions' words.** -/
theorem opOK_instOf {κ₀ : ℕ} {W : World κ₀} {tf : TracedFn} {pf : Placed} {fp : ℕ} {hdr : E × E}
    {σ : Val} {es : List Ev} {vs : List V} (kfps : List ℕ)
    (hok : (instOf W tf pf fp hdr σ es).Ok) (hta : TmpsApart tf pf)
    (hw : walk σ tf.core.body = .ret es vs)
    (hbelow : OpsBelow pf.fn.frameSize (blockOps pf.fn.body 0))
    (hin : ∀ v n, cellP pf.locs v = some n → 2 ≤ n)
    (tptr : ∀ o ∈ blockOps pf.fn.body 0, ∀ p off d, o = .deref p off d .cell →
      (instOf W tf pf fp hdr σ es).tc d → ¬ (instOf W tf pf fp hdr σ es).tc p)
    (tinj : ∀ t ∈ Stmt.tmpsList tf.core.body, ∀ t' ∈ Stmt.tmpsList tf.core.body, ∀ n,
      cellP pf.locs t = some n → cellP pf.locs t' = some n → t = t') :
    OpOK (World.cplSite W tf.core.name) (instOf W tf pf fp hdr σ es)
      (fun σ' Ψ kh => AgOf W tf fp σ' es kfps hdr ⟨patchT (instOf W tf pf fp hdr σ es) Ψ σ', kh⟩
        pf.fn.frameSize) (calls es) := by
  set I := instOf W tf pf fp hdr σ es with hI
  intro Ψ σ' hS kh h o pos cs ks next kj kret khalt ho hwo hn
  set FS : FrameSpec := ⟨patchT I Ψ σ', kh⟩ with hFS
  set Ag := AgOf W tf fp σ' es kfps hdr FS pf.fn.frameSize with hAg
  have hfresh := hta.fresh
  have hR : Rds Ag fp pf.fn.frameSize (fwd hdr FS) := fun κ L hA => hA.1
  have huses : ∀ e ∈ es, ∀ v ∈ e.uses, σ' v = I.σ v := by
    have hwi := walk_within (σ := σ) tf.core.body
    rw [hw] at hwi
    intro e he v hv
    exact hS v fun ht => (hfresh.2 v ht).1 (hwi.1 e he v hv)
  have hRd : ∀ (κ : ℕ) (L : MemoryImage κ), Ag κ L → FrameRd I Ψ L.read ∧ I.Rd L.read :=
    fun κ L hA => ⟨⟨hA.2.1.hdr0, hA.2.1.hdr1, fun n h2 hs ht => by
      have h0 : n ≠ 0 := by omega
      have h1 : n ≠ 1 := by omega
      have hfw : fw I Ψ n = Ψ n := by simp [fw, h0, h1]
      show L.read (addressOfIndex (fp + n)) = some (Ψ n)
      rw [hA.1 n hs]
      exact congrArg some ((fwd_patch ht).trans hfw)⟩,
      fun e he => evNT_of_holds (huses e he) (hA.2.2.2.1 e he)⟩
  have hlt : ∀ c ∈ opCells o, c < pf.fn.frameSize := hbelow o ho
  have hnt : ∀ c ∈ opCells o, I.tc c → ∃ p, o = .deref p 0 c .cell :=
    fun c hc ht => (hok.tops c ht o ho hc).imp fun _ h => h.1
  have hw' : ∀ c ∈ opCells o, ¬ I.tc c → fwd hdr FS c = fw I Ψ c := fun _ _ ht => fwd_patch ht
  cases o with
  | set c k =>
      have hc : ¬ I.tc c := fun ht => by
        obtain ⟨p, hp⟩ := hnt c (by simp [opCells]) ht
        cases hp
      simp only [wS]
      refine ⟨set_hw hR (hlt c (by simp [opCells])) ?_, hn⟩
      rw [hw' c (by simp [opCells]) hc]
      exact hwo
  | xor a b c =>
      have hc : ∀ x ∈ opCells (.xor a b c), ¬ I.tc x := fun x hx ht => by
        obtain ⟨p, hp⟩ := hnt x hx ht
        cases hp
      simp only [wS]
      refine ⟨xor_hw hR (hlt a (by simp [opCells])) (hlt b (by simp [opCells]))
        (hlt c (by simp [opCells])) ?_, hn⟩
      rw [hw' a (by simp [opCells]) (hc a (by simp [opCells])),
        hw' b (by simp [opCells]) (hc b (by simp [opCells])),
        hw' c (by simp [opCells]) (hc c (by simp [opCells]))]
      exact hwo
  | mul a b c =>
      have hc : ∀ x ∈ opCells (.mul a b c), ¬ I.tc x := fun x hx ht => by
        obtain ⟨p, hp⟩ := hnt x hx ht
        cases hp
      simp only [wS]
      refine ⟨mul_hw hR (hlt a (by simp [opCells])) (hlt b (by simp [opCells]))
        (hlt c (by simp [opCells])) ?_, hn⟩
      rw [hw' a (by simp [opCells]) (hc a (by simp [opCells])),
        hw' b (by simp [opCells]) (hc b (by simp [opCells])),
        hw' c (by simp [opCells]) (hc c (by simp [opCells]))]
      exact hwo
  | deref p off d mode =>
      have hpl := hlt p (by simp [opCells])
      have hdl := hlt d (by simp [opCells])
      cases mode with
      | cell =>
          have hp : ¬ I.tc p := fun ht => by
            obtain ⟨q, hq⟩ := hnt p (by simp [opCells]) ht
            cases hq
            exact tptr _ ho _ _ _ rfl ht ht
          simp only [wS]
          refine ⟨?_, hn⟩
          by_cases hd : I.tc d
          · obtain ⟨t, ht, hcell, rfl, hK, hrd⟩ := hwo.2.1 hd
            refine deref_hw hR hpl hdl (by rw [hw' p (by simp [opCells]) hp]; exact hK)
              fun κ L hA => ?_
            rw [hw' p (by simp [opCells]) hp, hrd σ' L.read hS hA.2.2.2.1]
            have h2 : 2 ≤ d := hin t d hcell
            have htm : t ∈ Stmt.tmpsList tf.core.body := by
              have hwi := walk_within (σ := σ) tf.core.body
              rw [hw] at hwi
              exact hwi.2.1.subset ht
            have hch := Classical.choose_spec hd
            have heq : Classical.choose hd = t := tinj _ hch.1 t htm d hch.2 hcell
            have h0 : d ≠ 0 := by simp only [Cell] at *; omega
            have h1 : d ≠ 1 := by simp only [Cell] at *; omega
            show some (σ' t) = some (fwd hdr FS d)
            simp [hFS, fwd, h0, h1, patchT, hd, heq]
          · refine deref_hw hR hpl hdl (by rw [hw' p (by simp [opCells]) hp]; exact hwo.1)
              fun κ L hA => ?_
            rw [hw' p (by simp [opCells]) hp, hw' d (by simp [opCells]) hd]
            exact hwo.2.2 hd L.read (hRd κ L hA).1 (hRd κ L hA).2
      | fp =>
          have hp : ¬ I.tc p := fun ht => by
            obtain ⟨q, hq⟩ := hnt p (by simp [opCells]) ht
            cases hq
          simp only [wS]
          refine ⟨deref_hw hR hpl hdl (by rw [hw' p (by simp [opCells]) hp]; exact hwo.1)
            fun κ L hA => ?_, hn⟩
          rw [hw' p (by simp [opCells]) hp]
          exact hwo.2 L.read (hRd κ L hA).1 (hRd κ L hA).2
      | pc => exact hwo.elim
  | jump oc od of =>
      have hc : ∀ x ∈ opCells (.jump oc od of), ¬ I.tc x := fun x hx ht => by
        obtain ⟨p, hp⟩ := hnt x hx ht
        cases hp
      simp only [wS]
      obtain ⟨h0, hd, hf⟩ := hwo
      have h0' : fwd hdr FS oc = 0 :=
        (hw' oc (by simp [opCells]) (hc oc (by simp [opCells]))).trans h0
      have hd' : IsInK (fwd hdr FS od) := by
        rw [hw' od (by simp [opCells]) (hc od (by simp [opCells]))]; exact hd
      have hf' : IsInK (fwd hdr FS of) := by
        rw [hw' of (by simp [opCells]) (hc of (by simp [opCells]))]; exact hf
      exact jw_of hR (hlt oc (by simp [opCells])) (hlt od (by simp [opCells]))
        (hlt of (by simp [opCells])) (by rw [h0']; exact (isInK_iff _).mpr ⟨0, by simp⟩) hd' hf'
        (fun _ => hn) (fun h' => absurd h0' h')
  | keccak m0 m1 m2 m3 tail b8 cap out inOdd outOdd oc =>
      have hc : ∀ x ∈ opCells (.keccak m0 m1 m2 m3 tail b8 cap out inOdd outOdd oc), ¬ I.tc x :=
        fun x hx ht => by
          obtain ⟨p, hp⟩ := hnt x hx ht
          cases hp
      have e1 : (fun c : Fin 13 => fwd hdr FS (keccakInOff m0 m1 m2 m3 tail b8 cap c.val)) =
          fun c : Fin 13 => fw I Ψ (keccakInOff m0 m1 m2 m3 tail b8 cap c.val) :=
        funext fun c => hw' _ (keccakIn_mem c) (hc _ (keccakIn_mem c))
      simp only [wS]
      refine ⟨keccak_hw (output := fun c : Fin 13 => fw I Ψ (out + c.val)) hR
        (fun c => hlt _ (keccakIn_mem c)) (fun c hc' => ⟨hlt _ (keccakOut_mem c hc'),
          (hw' _ (keccakOut_mem c hc') (hc _ (keccakOut_mem c hc'))).symm⟩) ?_, hn⟩
      rw [e1]
      exact hwo
  | slot => exact hwo.elim
  | mulNextFrame => exact hwo.elim

end
end LeanVM.Guest.Backend.Complete
