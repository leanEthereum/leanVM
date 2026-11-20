/-
  LeanVM.Guest.B1.KeccakGkr.VkOut

  `verify_keccak`'s committed outputs' opening.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.VkOpen
public import LeanVM.Guest.B1.KeccakGkr.VkHead
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_keccak»

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr Finset

@[expose] public section

variable {rd : Reader} {σ : Val}

theorem plainRun_cons_snd (c0 c2 : E) (rest : List (E × E)) (v : E) (s : Fs) :
    (plainRun ((c0, c2) :: rest) v s).2.2 =
      (plainRun rest (c0 + ((s.absorb c0 dsObserve).absorb c2 dsObserve).squeeze.1 *
        ((v + c2) + ((s.absorb c0 dsObserve).absorb c2 dsObserve).squeeze.1 * c2))
        ((s.absorb c0 dsObserve).absorb c2 dsObserve).squeeze.2).2.2 := rfl

theorem squeeze_pend (s : Fs) : s.squeeze.2.pend = [] := rfl

theorem plainRun_pend (ms : List (E × E)) : ∀ (v : E) (s : Fs), ms ≠ [] →
    (plainRun ms v s).2.2.pend = [] := by
  induction ms with
  | nil => intro _ _ h; exact absurd rfl h
  | cons m ms ih =>
    intro v s _
    obtain ⟨c0, c2⟩ := m
    rw [plainRun_cons_snd]
    rcases ms with _ | ⟨m', ms'⟩
    · simp only [plainRun]
      exact squeeze_pend _
    · exact ih _ _ (by simp)

theorem plainRun_length : ∀ (ms : List (E × E)) (v : E) (s : Fs), (plainRun ms v s).1.length = ms.length
  | [], _, _ => rfl
  | m :: ms, v, s => by simp [plainRun, plainRun_length ms]

/-- Plain rounds through their call: the rounds' messages, the run, the challenges stored, the
returns. -/
theorem plain_call {n k0 : ℕ} (hk : k0 < 2) (hn : n = plainCount k0) {cap : List E}
    (hcap : cap.length = 5) {p0 p1 cur v pt tb : E} {rets : List E}
    (h : coreProgram.Rel rd (plainName k0) (cap ++ [p0, p1, cur, v, pt, tb]) rets) :
    ∃ ms : List (E × E), ms.length = n ∧ ReadsAt rd cur (ms.flatMap fun c ↦ [c.1, c.2]) ∧
      ∀ w : E, (k0 = 1 → (p0, p1) = Keccak.scalarCells w dsObserve) →
        ReadsAt rd pt (plainRun ms v (plainStart k0 cap w)).1 ∧
        rets = (plainRun ms v (plainStart k0 cap w)).2.2.cap ++
          [cur * gen ^ (2 * n), (plainRun ms v (plainStart k0 cap w)).2.1] := by
  have hm := keccak_plain_rounds_holds k0 hk rd _ rets h
  match cap, hcap with
  | [f0, f1, f2, f3, f4], _ =>
    simp only [List.cons_append, List.nil_append, MeaningPlainRounds] at hm
    obtain ⟨ms, hl, hr, hall⟩ := hm
    subst hn
    exact ⟨ms, hl, hr, fun w hw ↦ hall w hw⟩

/-- **The committed outputs' opening**. -/
theorem vkOutT_holds {τ : ℕ} (hτ1 : 9 ≤ τ) (hτ2 : τ ≤ 28) (h6 : σ (.n (val% «verify_keccak» "tau_g")) = gen ^ τ)
    (h17 : σ (.n (val% «verify_keccak» "pack_g")) = gen ^ (τ - 4)) {L : ℕ → E}
    (hL : ∀ lane < 25, ∀ v, LoadHolds rd (σ (.n (val% «verify_keccak» "lane_tree"))) (30 + lane) v → v = L lane)
    (h64 : σ (.n (val% «verify_keccak» "segment")) = σ (.n (val% «verify_keccak» "point")) * σ (.n (val% «verify_keccak» "pack_g"))) (h89 : LoadHolds rd (σ (.n (val% «verify_keccak» "segment"))) 0 (σ (.n (val% «verify_keccak» "nxt[0]@1"))))
    {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList (coreProgram.Rel rd) rd σ vkOutT next kret) :
    ∃ (mO : List (E × E)) (slotO : List E), mO.length = 6 ∧
      ReadsAt rd (σ (.n (val% «verify_keccak» "cursor@13"))) (mO.flatMap fun c ↦ [c.1, c.2]) ∧
      plainRun mO (σ (.n (val% «verify_keccak» "x@1")))
        ⟨[σ (.n (val% «verify_keccak» "fs0@13")), σ (.n (val% «verify_keccak» "fs1@13")), σ (.n (val% «verify_keccak» "fs2@13")), σ (.n (val% «verify_keccak» "fs3@13")), σ (.n (val% «verify_keccak» "fs4@13"))], []⟩ =
        (slotO, σ (.n (val% «verify_keccak» "out_value")),
          ⟨[σ (.n (val% «verify_keccak» "fs0@14")), σ (.n (val% «verify_keccak» "fs1@14")), σ (.n (val% «verify_keccak» "fs2@14")), σ (.n (val% «verify_keccak» "fs3@14")), σ (.n (val% «verify_keccak» "fs4@14"))], []⟩) ∧
      ReadsAt rd (σ (.n (val% «verify_keccak» "z_vals")) * gen ^ τ) slotO ∧
      σ (.n (val% «verify_keccak» "cursor@14")) = σ (.n (val% «verify_keccak» "cursor@13")) * gen ^ 12 ∧
      (LoadHolds rd (σ (.n (val% «verify_keccak» "cursor@14"))) 0 (σ (.n (val% «verify_keccak» "x@2"))) ∧ FsPackOk σ (.n (val% «verify_keccak» "x@2")) (926 + 1) dsObserve) ∧
      (∑ lane ∈ range 25, (∑ m ∈ range 1, eqAt [σ (.n (val% «verify_keccak» "nxt[0]@1"))] m * eqAt slotO (25 * (1 + m) + lane)) *
        L lane) * σ (.n (val% «verify_keccak» "x@2")) = σ (.n (val% «verify_keccak» "out_value")) ∧
      (∀ j < τ - 4, ∃ v, LoadHolds rd (σ (.n (val% «verify_keccak» "point"))) j v ∧ LoadHolds rd (σ (.n (val% «verify_keccak» "z_vals")) * gen ^ 4) j v) ∧
      next := by
  rw [vkOutT] at h
  simp only [holdsList_append, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons,
    List.map_nil] at h
  obtain ⟨e3691, z0, z1, hcall, h⟩ := h
  -- the slot's rounds
  obtain ⟨mO, hmL, hmR, hrun⟩ := plain_call (k0 := 0) (n := 6) (by omega) rfl
    (cap := [σ (.n (val% «verify_keccak» "fs0@13")), σ (.n (val% «verify_keccak» "fs1@13")), σ (.n (val% «verify_keccak» "fs2@13")), σ (.n (val% «verify_keccak» "fs3@13")), σ (.n (val% «verify_keccak» "fs4@13"))]) rfl
    (by simpa [List.range_succ, plainName] using hcall)
  obtain ⟨hpt, hrets⟩ := hrun 0 (fun h ↦ absurd h (by decide))
  simp only [plainStart, show ¬ ((0 : ℕ) = 1) by decide, ↓reduceIte] at hpt hrets
  have hpend := plainRun_pend mO (σ (.n (val% «verify_keccak» "x@1")))
    ⟨[σ (.n (val% «verify_keccak» "fs0@13")), σ (.n (val% «verify_keccak» "fs1@13")), σ (.n (val% «verify_keccak» "fs2@13")), σ (.n (val% «verify_keccak» "fs3@13")), σ (.n (val% «verify_keccak» "fs4@13"))], []⟩
    (by rintro rfl; simp at hmL)
  set R := plainRun mO (σ (.n (val% «verify_keccak» "x@1")))
    ⟨[σ (.n (val% «verify_keccak» "fs0@13")), σ (.n (val% «verify_keccak» "fs1@13")), σ (.n (val% «verify_keccak» "fs2@13")), σ (.n (val% «verify_keccak» "fs3@13")), σ (.n (val% «verify_keccak» "fs4@13"))], []⟩ with hR
  rw [show [σ (.n (val% «verify_keccak» "fs0@14")), σ (.n (val% «verify_keccak» "fs1@14")), σ (.n (val% «verify_keccak» "fs2@14")), σ (.n (val% «verify_keccak» "fs3@14")), σ (.n (val% «verify_keccak» "fs4@14")), σ (.n (val% «verify_keccak» "cursor@14")),
      σ (.n (val% «verify_keccak» "out_value"))] = [σ (.n (val% «verify_keccak» "fs0@14")), σ (.n (val% «verify_keccak» "fs1@14")), σ (.n (val% «verify_keccak» "fs2@14")), σ (.n (val% «verify_keccak» "fs3@14")), σ (.n (val% «verify_keccak» "fs4@14"))] ++
      [σ (.n (val% «verify_keccak» "cursor@14")), σ (.n (val% «verify_keccak» "out_value"))] from rfl] at hrets
  obtain ⟨hcapR, hlast⟩ := List.append_inj' hrets rfl
  simp only [List.cons.injEq, and_true] at hlast
  obtain ⟨h3699, h3700⟩ := hlast
  have hRs : R = (R.1, σ (.n (val% «verify_keccak» "out_value")),
      ⟨[σ (.n (val% «verify_keccak» "fs0@14")), σ (.n (val% «verify_keccak» "fs1@14")), σ (.n (val% «verify_keccak» "fs2@14")), σ (.n (val% «verify_keccak» "fs3@14")), σ (.n (val% «verify_keccak» "fs4@14"))], []⟩) := by
    rw [h3700, hcapR, ← hpend]
  have hslotL : R.1.length = 6 := by rw [hR, plainRun_length, hmL]
  -- the word
  obtain ⟨⟨lw, pw⟩, h⟩ := (holds_fsNextT _ _ _ _ _).1 h
  obtain ⟨e3711, h⟩ := h
  -- the slot's lane weights
  obtain ⟨rs, hrsL, hrs, r, hr, hlanes, h⟩ := slotLanesT_holds (Or.inl rfl) (by norm_num) h
  have hrs' : rs = R.1 := by
    apply List.ext_getElem (by rw [hrsL, hslotL])
    intro k h1 h2
    have := hpt k h2
    rw [e3691, h6] at hrs
    exact loadHolds_unique (hrs k h1) (by rw [e3691, h6] at this; exact this)
  have hr' : r = σ (.n (val% «verify_keccak» "nxt[0]@1")) := by
    rw [e3711, ← h64] at hr
    exact loadHolds_unique hr h89
  obtain ⟨hdot, h⟩ := dotLoadsT_holds (xs := (List.range 25).map (slotLaneV 930 1)) (P := L)
    (fun k hk v hv ↦ hL k (by simpa using hk) v hv) (by simp) h
  obtain ⟨e3969, heq, c70, e71, c72, c73, e74, -, hcall12, hn⟩ := h
  simp only [List.length_map, List.length_range] at hdot
  refine ⟨mO, R.1, hmL, hmR, hRs, by rw [← h6]; rw [e3691] at hpt; exact hpt,
    h3699.trans (by norm_num), ⟨lw, pw⟩, ?_, ?_, hn⟩
  · rw [← eq_of_add_eq_zero' heq, e3969]
    have hd : σ (.n (val% «verify_keccak» "lanes_sum@25")) = ∑ lane ∈ range 25,
        (∑ m ∈ range 1, eqAt [σ (.n (val% «verify_keccak» "nxt[0]@1"))] m * eqAt R.1 (25 * (1 + m) + lane)) * L lane := by
      rw [show (1186 : ℕ) = dotLoadsV 1113 25 from rfl, hdot]
      refine Finset.sum_congr rfl fun lane hl ↦ ?_
      rw [List.getD_eq_getElem _ _ (by simpa using hl), List.getElem_map, List.getElem_range,
        hlanes lane (Finset.mem_range.1 hl), hrs', hr']
    rw [hd]
  · have hne : 1 + σ (.n (val% «verify_keccak» "pack_g")) ≠ 0 := by rw [h17]; exact gen_pow_ne_one (by omega) (by unfold ordG; omega)
    have hc := hcall12 (by rw [e71, c70, word_one]; exact hne)
    simp only [c72, e74, c73, word_one, word_16] at hc
    exact copyLoop_sound find_copyLoop12 copyLoop_body12 rfl h17 (by unfold ordG; omega) hc

end
end LeanVM.Guest.B1.VerifySub
