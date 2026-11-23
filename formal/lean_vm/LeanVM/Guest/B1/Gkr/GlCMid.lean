/-
  LeanVM.Guest.B1.Gkr.GlCMid

  A radix-four layer's middle, completely: the head record stored, the loop called, the last
  record read and the row's zero cell, on their equations.
-/

module

public import LeanVM.Guest.B1.Gkr.GlCHead
public import LeanVM.Guest.B1.Gkr.GlCLoop
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«gkr_layer__L»
import LeanVM.Guest.Data.ValNames.«gkr_layer__L0_L0»

/-!
# A radix-four layer's middle, completely

The rounds' states are `gkSt Cf ef claim s a` (round `q` on the words `Cf q` and the eq factor
`ef q`); `GlRecK rd rec cur … a`: the record at `rec` holds the state after `a` rounds and the
cursor `4a` words on.

* `glc_hstore`: the head record (after `2p` rounds) stored at `head`;
* `glc_lcall`: the loop called on `head`, `qrow = row·g^(2p)` and `qrow·g^42`;
* `glc_tsetup`: the last record `head·x_m` read (its state after `2p + 8m` rounds), the rows
  `tpt = row·g^(2p + 8m)` and `ntpt = tpt·g^42`;
* `glc_pad`: at an odd depth, the zero at `ntpt[1]`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1 LeanVM.Guest.B1.Fwd

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop} {S : List Atom}
  {w : ℕ → E}

/-- **A round record** after `a` rounds of `gkSt`: the capacity, the cursor `4a` words on and the
claim. -/
def GlRecK (rd : Reader) (rec cur : E) (Cf : ℕ → List E) (ef : ℕ → E) (claim : E) (s : Fs)
    (a : ℕ) : Prop :=
  TbCapAt rd rec 0 gkCap (gkSt Cf ef claim s a).2.cap ∧
    LoadHolds rd rec (5 * gkCap) (cur * gen ^ (4 * a)) ∧
    LoadHolds rd rec (6 * gkCap) (gkSt Cf ef claim s a).1

theorem gkCap_eq : gkCap = 862 := by decide

theorem glc_cap_load {rd : Reader} {rec : E} {cap : List E} (h : TbCapAt rd rec 0 gkCap cap)
    {k : ℕ} (hk : k < 5) : LoadHolds rd rec (862 * k) (cap.getD k 0) := by
  obtain ⟨hl, h⟩ := h
  have := h k (by omega)
  rw [gkCap_eq, Nat.zero_add, mul_comm] at this
  rwa [List.getD_eq_getElem _ _ (by omega)]

/-- **The head record stored.** -/
theorem glc_hstore {p : ℕ} (hp : p < 4) (hG : ∀ s ∈ glHeadStore p, GoodS rd S w σ s)
    {head cur : E} (e21 : σ (.n (valf% «gkr_layer» "s4#0")) = cur) (e54 : σ (.n (valf% «gkr_layer» "head")) = head) {cap : List E} {claim : E}
    (hcap : (glCap (if p = 0 then 35 else 39 + 78 * p)).map σ = cap)
    (hcl : σ (.n (if p = 0 then 57 else 57 + 78 * p)) = claim)
    (hR1 : TbCapAt rd head 0 gkCap cap) (hR2 : LoadHolds rd head (5 * gkCap) (cur * gen ^ (8 * p)))
    (hR3 : LoadHolds rd head (6 * gkCap) claim) :
    Stmt.HoldsList C rd σ (glHeadStore p) True kret := by
  have hc : ∀ k < 5, LoadHolds rd (σ (.n (valf% «gkr_layer» "head"))) (862 * k)
      (σ (.n ((if p = 0 then 35 else 39 + 78 * p) + k))) := by
    intro k hk
    have := glc_cap_load hR1 hk
    rw [← hcap] at this
    rw [e54]
    simpa [glCap, List.getD_eq_getElem?_getD, hk] using this
  rw [gkCap_eq] at hR2 hR3
  rcases Nat.eq_zero_or_pos p with h0 | h0
  · subst h0
    simp only [glHeadStore, ↓reduceIte, glHeadStore0, List.range_succ, List.range_zero,
      List.map_cons, List.map_nil, List.nil_append, List.cons_append, Stmt.HoldsList, Stmt.Holds,
      Atom.Holds, and_true] at hc hcl ⊢
    refine ⟨hc 0 (by omega), hc 1 (by omega), hc 2 (by omega), hc 3 (by omega), hc 4 (by omega),
      ?_, ?_⟩
    · rw [e54, e21]; simpa using hR2
    · rw [e54, hcl]; exact hR3
  · have hp0 : p ≠ 0 := by omega
    have g : ∀ a, Stmt.atom a ∈ glHeadStore p → Good rd S w σ a := fun a ha ↦ hG _ ha
    have c59 : σ (.n (58 + 78 * p)) = word (2 ^ (8 * p)) 0 :=
      g (.const (.n (58 + 78 * p)) (word (2 ^ (8 * p)) 0)) (by simp [glHeadStore, hp0, glHeadStoreP])
    have m60 := good_mul (g (.mul (.n (59 + 78 * p)) (.n (valf% «gkr_layer» "s4#0")) (.n (58 + 78 * p)))
      (by simp [glHeadStore, hp0, glHeadStoreP])) (by omega) (by omega)
    simp only [glHeadStore, hp0, ↓reduceIte, glHeadStoreP, List.range_succ, List.range_zero,
      List.map_cons, List.map_nil, List.nil_append, List.cons_append, Stmt.HoldsList, Stmt.Holds,
      Atom.Holds, and_true] at hc hcl ⊢
    refine ⟨hc 0 (by omega), hc 1 (by omega), hc 2 (by omega), hc 3 (by omega), hc 4 (by omega),
      c59, m60, ?_, ?_⟩
    · rw [m60, c59, tb_word_two_pow (by omega), e54, e21]; exact hR2
    · rw [e54, hcl]; exact hR3

/-- **The loop's call** on the head, `qrow = row·g^(2p)` and `qrow·g^42`, entered iff `m ≠ 0`. -/
theorem glc_lcall {p : ℕ} (hp : p < 4) {nm : String}
    (hG : ∀ s ∈ glLoopCall p nm, GoodS rd S w σ s) {m : ℕ} (e3 : σ (.n (valf% «gkr_layer» "x_m")) = gen ^ m)
    {row : E} (e53 : σ (.n (valf% «gkr_layer» "point_row")) = row)
    (hloop : 0 < m → coreProgram.Rel rd nm [1, gen ^ m, σ (.n (valf% «gkr_layer» "head")), row * gen ^ (2 * p),
      row * gen ^ (2 * p) * gen ^ 42, σ (.n (valf% «gkr_layer» "tabs"))] []) :
    Stmt.HoldsList (coreProgram.Rel rd) rd σ (glLoopCall p nm) True kret := by
  have g : ∀ a, Stmt.atom a ∈ glLoopCall p nm → Good rd S w σ a := fun a ha ↦ hG _ ha
  have hK : IsInK (1 + gen ^ m) := tb_isInK_add (by simpa using tb_gen_pow_isInK 0) (tb_gen_pow_isInK _)
  have hm0 : 1 + gen ^ m ≠ 0 → 0 < m := fun hne ↦ by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, pow_zero, e_add_self] at hne; exact absurd rfl hne
    · exact h0
  rcases Nat.eq_zero_or_pos p with h0 | h0
  · subst h0
    have c59 : σ (.n (val% «gkr_layer__L0_L0» "s20#0")) = word 1 0 := g (.const (.n (val% «gkr_layer__L0_L0» "s20#0")) (word 1 0)) (by simp [glLoopCall, glLoopCall0])
    have a60 : σ (.n (val% «gkr_layer__L0_L0» "s20#1")) = σ (.n (val% «gkr_layer__L0_L0» "s20#0")) + σ (.n (valf% «gkr_layer» "x_m")) := g (.add (.n (val% «gkr_layer__L0_L0» "s20#1")) (.n (val% «gkr_layer__L0_L0» "s20#0")) (.n (valf% «gkr_layer» "x_m")))
      (by simp [glLoopCall, glLoopCall0])
    have c61 : σ (.n (val% «gkr_layer__L0_L0» "s20#2")) = word 1 0 := g (.const (.n (val% «gkr_layer__L0_L0» "s20#2")) (word 1 0)) (by simp [glLoopCall, glLoopCall0])
    have c62 : σ (.n (val% «gkr_layer__L0_L0» "s20#3")) = word (2 ^ 42) 0 := g (.const (.n (val% «gkr_layer__L0_L0» "s20#3")) (word (2 ^ 42) 0))
      (by simp [glLoopCall, glLoopCall0])
    have m63 := good_mul (g (.mul (.n (val% «gkr_layer__L0_L0» "s20#4")) (.n (valf% «gkr_layer» "point_row")) (.n (val% «gkr_layer__L0_L0» "s20#3"))) (by simp [glLoopCall, glLoopCall0]))
      (by omega) (by omega)
    have e60 : σ (.n (val% «gkr_layer__L0_L0» "s20#1")) = 1 + gen ^ m := by rw [a60, c59, tb_word_one, e3]
    simp only [glLoopCall, ↓reduceIte, glLoopCall0, Stmt.HoldsList, Stmt.Holds, Atom.Holds,
      List.map_cons, List.map_nil, and_true]
    refine ⟨c59, a60, c61, c62, m63, by rw [e60]; exact hK, fun hne ↦ ?_⟩
    rw [e60] at hne
    have := hloop (hm0 hne)
    rw [m63, c62, c61, tb_word_one, tb_word_two_pow (by omega), e3, e53]
    simpa using this
  · have hp0 : p ≠ 0 := by omega
    have mem : ∀ a, Stmt.atom a ∈ glLoopCallP p nm → Stmt.atom a ∈ glLoopCall p nm := fun a ha ↦ by
      simpa [glLoopCall, hp0] using ha
    have c1 : σ (.n (60 + 78 * p)) = word 1 0 :=
      g (.const (.n (60 + 78 * p)) (word 1 0)) (mem _ (by simp [glLoopCallP]))
    have a2 : σ (.n (61 + 78 * p)) = σ (.n (60 + 78 * p)) + σ (.n (valf% «gkr_layer» "x_m")) :=
      g (.add (.n (61 + 78 * p)) (.n (60 + 78 * p)) (.n (valf% «gkr_layer» "x_m"))) (mem _ (by simp [glLoopCallP]))
    have c3 : σ (.n (62 + 78 * p)) = word 1 0 :=
      g (.const (.n (62 + 78 * p)) (word 1 0)) (mem _ (by simp [glLoopCallP]))
    have c4 : σ (.n (63 + 78 * p)) = word (2 ^ (2 * p)) 0 :=
      g (.const (.n (63 + 78 * p)) (word (2 ^ (2 * p)) 0)) (mem _ (by simp [glLoopCallP]))
    have m5 := good_mul (g (.mul (.n (64 + 78 * p)) (.n (valf% «gkr_layer» "point_row")) (.n (63 + 78 * p)))
      (mem _ (by simp [glLoopCallP]))) (by omega) (by omega)
    have c6 : σ (.n (65 + 78 * p)) = word (2 ^ (42 + 2 * p)) 0 :=
      g (.const (.n (65 + 78 * p)) (word (2 ^ (42 + 2 * p)) 0)) (mem _ (by simp [glLoopCallP]))
    have m7 := good_mul (g (.mul (.n (66 + 78 * p)) (.n (valf% «gkr_layer» "point_row")) (.n (65 + 78 * p)))
      (mem _ (by simp [glLoopCallP]))) (by omega) (by omega)
    have e2 : σ (.n (61 + 78 * p)) = 1 + gen ^ m := by rw [a2, c1, tb_word_one, e3]
    simp only [glLoopCall, hp0, ↓reduceIte, glLoopCallP, Stmt.HoldsList, Stmt.Holds, Atom.Holds,
      List.map_cons, List.map_nil, and_true]
    refine ⟨c1, a2, c3, c4, m5, c6, m7, by rw [e2]; exact hK, fun hne ↦ ?_⟩
    rw [e2] at hne
    have := hloop (hm0 hne)
    rw [m7, m5, c6, c4, c3, tb_word_one, tb_word_two_pow (by omega), tb_word_two_pow (by omega), e3,
      e53, show row * gen ^ (42 + 2 * p) = row * gen ^ (2 * p) * gen ^ 42 by ring]
    simpa using this

/-- Where the tail reads the last record. -/
def glW (p : ℕ) : ℕ := if p = 0 then 63 else 67 + 78 * p

/-- The last record's reads. -/
def glTailKeys (p : ℕ) : List (ℕ × ℕ × ℕ) :=
  (List.range 5).map (fun k ↦ (71 + glD p + k, glW p, 862 * k)) ++
    [(76 + glD p, glW p, 4310), (77 + glD p, glW p, 5172)]

/-- **The last record read.** -/
theorem glc_tloads {p : ℕ} (hG : ∀ s ∈ glTailLoads p (glW p), GoodS rd S w σ s)
    (hk : ∀ k ∈ glTailKeys p, some k ∉ S.map loadKey) {rec cur : E} {Cf : ℕ → List E}
    {ef : ℕ → E} {claim : E} {s : Fs} {a : ℕ} (ew : σ (.n (glW p)) = rec)
    (hR : GlRecK rd rec cur Cf ef claim s a) :
    Stmt.HoldsList C rd σ (glTailLoads p (glW p)) True kret ∧
      (glCap (71 + glD p)).map σ = (gkSt Cf ef claim s a).2.cap ∧
      σ (.n (76 + glD p)) = cur * gen ^ (4 * a) ∧ σ (.n (77 + glD p)) = (gkSt Cf ef claim s a).1 := by
  obtain ⟨h1, h2, h3⟩ := hR
  rw [gkCap_eq] at h2 h3
  have g : ∀ a, Stmt.atom a ∈ glTailLoads p (glW p) → Good rd S w σ a := fun a ha ↦ hG _ ha
  have rc : ∀ k < 5, σ (.n (71 + glD p + k)) = (gkSt Cf ef claim s a).2.cap.getD k 0 ∧
      LoadHolds rd (σ (.n (glW p))) (862 * k) (σ (.n (71 + glD p + k))) := fun k hk' ↦
    good_read (g (.load (.n (71 + glD p + k)) (.n (glW p)) (862 * k))
      (by simp only [glTailLoads, List.mem_append, List.mem_map, List.mem_range]
          exact .inl ⟨k, hk', rfl⟩))
      (hk _ (by simp only [glTailKeys, List.mem_append, List.mem_map, List.mem_range]
                exact .inl ⟨k, hk', rfl⟩))
      (by rw [ew]; exact glc_cap_load h1 hk')
  obtain ⟨e77, l77⟩ := good_read (g (.load (.n (76 + glD p)) (.n (glW p)) 4310)
    (by simp [glTailLoads])) (hk _ (by simp [glTailKeys])) (by rw [ew]; exact h2)
  obtain ⟨e78, l78⟩ := good_read (g (.load (.n (77 + glD p)) (.n (glW p)) 5172)
    (by simp [glTailLoads])) (hk _ (by simp [glTailKeys])) (by rw [ew]; exact h3)
  have hcl : (gkSt Cf ef claim s a).2.cap.length = 5 := h1.1
  refine ⟨?_, ?_, e77, e78⟩
  · simp only [glTailLoads, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
      List.nil_append, List.cons_append, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
    exact ⟨(rc 0 (by omega)).2, (rc 1 (by omega)).2, (rc 2 (by omega)).2, (rc 3 (by omega)).2,
      (rc 4 (by omega)).2, l77, l78⟩
  · rw [tb_eq_map_getD hcl]
    simp only [glCap, List.map_map]
    exact List.map_congr_left fun k hk' ↦ (rc k (List.mem_range.mp hk')).1

/-- **The tail's pointers and the last record**: `head·x_m`, `tpt = row·g^(2p)·x_m^8`,
`ntpt = row·g^(2p)·g^42·x_m^8`. -/
theorem glc_tsetup {p : ℕ} (hp : p < 4) (hG : ∀ s ∈ glTailSetup p, GoodS rd S w σ s)
    (hk : ∀ k ∈ glTailKeys p, some k ∉ S.map loadKey) {head row : E} {m : ℕ}
    (e54 : σ (.n (valf% «gkr_layer» "head")) = head) (e3 : σ (.n (valf% «gkr_layer» "x_m")) = gen ^ m) (e53 : σ (.n (valf% «gkr_layer» "point_row")) = row)
    {cur : E} {Cf : ℕ → List E} {ef : ℕ → E} {claim : E} {s : Fs} {a : ℕ}
    (hR : GlRecK rd (head * gen ^ m) cur Cf ef claim s a) :
    Stmt.HoldsList C rd σ (glTailSetup p) True kret ∧
      σ (.n (67 + glD p)) = row * gen ^ (2 * p) * gen ^ (8 * m) ∧
      σ (.n (70 + glD p)) = row * gen ^ (2 * p) * gen ^ 42 * gen ^ (8 * m) ∧
      (glCap (71 + glD p)).map σ = (gkSt Cf ef claim s a).2.cap ∧
      σ (.n (76 + glD p)) = cur * gen ^ (4 * a) ∧ σ (.n (77 + glD p)) = (gkSt Cf ef claim s a).1 := by
  have g : ∀ a, Stmt.atom a ∈ glTailSetup p → Good rd S w σ a := fun a ha ↦ hG _ ha
  have m8 : ∀ x : E, x = gen ^ m → x * x * (x * x) * (x * x * (x * x)) = gen ^ (8 * m) := by
    intro x hx; rw [hx]; ring
  rcases Nat.eq_zero_or_pos p with h0 | h0
  · subst h0
    have mem : ∀ a, Stmt.atom a ∈ glTailSetup0 → Stmt.atom a ∈ glTailSetup 0 := fun a ha ↦ by
      simpa [glTailSetup] using ha
    have m64 := good_mul (g (.mul (.n (val% «gkr_layer__L0_L0» "rd_last")) (.n (valf% «gkr_layer» "head")) (.n (valf% «gkr_layer» "x_m"))) (mem _ (by simp [glTailSetup0])))
      (by omega) (by omega)
    have m65 := good_mul (g (.mul (.n (val% «gkr_layer__L0_L0» "m2")) (.n (valf% «gkr_layer» "x_m")) (.n (valf% «gkr_layer» "x_m"))) (mem _ (by simp [glTailSetup0])))
      (by omega) (by omega)
    have m66 := good_mul (g (.mul (.n (val% «gkr_layer__L0_L0» "m4")) (.n (val% «gkr_layer__L0_L0» "m2")) (.n (val% «gkr_layer__L0_L0» "m2"))) (mem _ (by simp [glTailSetup0])))
      (by omega) (by omega)
    have m67 := good_mul (g (.mul (.n (val% «gkr_layer__L0_L0» "m8")) (.n (val% «gkr_layer__L0_L0» "m4")) (.n (val% «gkr_layer__L0_L0» "m4"))) (mem _ (by simp [glTailSetup0])))
      (by omega) (by omega)
    have m68 := good_mul (g (.mul (.n (val% «gkr_layer__L0_L0» "tpt")) (.n (valf% «gkr_layer» "point_row")) (.n (val% «gkr_layer__L0_L0» "m8"))) (mem _ (by simp [glTailSetup0])))
      (by omega) (by omega)
    have c69 : σ (.n (val% «gkr_layer__L0_L0» "ntpt~0")) = word (2 ^ 42) 0 :=
      g (.const (.n (val% «gkr_layer__L0_L0» "ntpt~0")) (word (2 ^ 42) 0)) (mem _ (by simp [glTailSetup0]))
    have m70 := good_mul (g (.mul (.n (val% «gkr_layer__L0_L0» "ntpt~1")) (.n (valf% «gkr_layer» "point_row")) (.n (val% «gkr_layer__L0_L0» "ntpt~0"))) (mem _ (by simp [glTailSetup0])))
      (by omega) (by omega)
    have m71 := good_mul (g (.mul (.n (val% «gkr_layer__L0_L0» "ntpt")) (.n (val% «gkr_layer__L0_L0» "ntpt~1")) (.n (val% «gkr_layer__L0_L0» "m8"))) (mem _ (by simp [glTailSetup0])))
      (by omega) (by omega)
    have e67 : σ (.n (val% «gkr_layer__L0_L0» "m8")) = gen ^ (8 * m) := by rw [m67, m66, m65]; exact m8 _ e3
    have hT0 : ∀ s ∈ glTailLoads 0 (glW 0), s ∈ glTailSetup 0 := fun s hs ↦ by
      simp only [glTailSetup, ↓reduceIte, glTailSetup0]
      exact List.mem_append_right _ (by simpa [glW] using hs)
    obtain ⟨L1, L2, L3, L4⟩ := glc_tloads (C := C) (kret := kret) (p := 0)
      (fun s hs ↦ hG s (hT0 s hs)) hk (rec := head * gen ^ m)
      (by simp only [glW, ↓reduceIte]; rw [m64, e54, e3]) hR
    refine ⟨?_, by simp only [glD, ↓reduceIte, Nat.add_zero]; rw [m68, e53, e67]; ring,
      by simp only [glD, ↓reduceIte, Nat.add_zero]; rw [m71, m70, c69, e67, e53,
        tb_word_two_pow (by omega)]; ring, L2, L3, L4⟩
    simp only [glTailSetup, ↓reduceIte, glTailSetup0]
    rw [tb_holdsList_append_noRet (by rfl)]
    refine ⟨?_, by simpa [glW] using L1⟩
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
    exact ⟨m64, m65, m66, m67, m68, c69, m70, m71⟩
  · have hp0 : p ≠ 0 := by omega
    have mem : ∀ a, Stmt.atom a ∈ glTailSetupP p → Stmt.atom a ∈ glTailSetup p := fun a ha ↦ by
      simpa [glTailSetup, hp0] using ha
    have m1 := good_mul (g (.mul (.n (67 + 78 * p)) (.n (valf% «gkr_layer» "head")) (.n (valf% «gkr_layer» "x_m"))) (mem _ (by simp [glTailSetupP])))
      (by omega) (by omega)
    have m2 := good_mul (g (.mul (.n (68 + 78 * p)) (.n (valf% «gkr_layer» "x_m")) (.n (valf% «gkr_layer» "x_m"))) (mem _ (by simp [glTailSetupP])))
      (by omega) (by omega)
    have m3 := good_mul (g (.mul (.n (69 + 78 * p)) (.n (68 + 78 * p)) (.n (68 + 78 * p)))
      (mem _ (by simp [glTailSetupP]))) (by omega) (by omega)
    have m4 := good_mul (g (.mul (.n (70 + 78 * p)) (.n (69 + 78 * p)) (.n (69 + 78 * p)))
      (mem _ (by simp [glTailSetupP]))) (by omega) (by omega)
    have c5 : σ (.n (71 + 78 * p)) = word (2 ^ (2 * p)) 0 :=
      g (.const (.n (71 + 78 * p)) (word (2 ^ (2 * p)) 0)) (mem _ (by simp [glTailSetupP]))
    have m6 := good_mul (g (.mul (.n (72 + 78 * p)) (.n (valf% «gkr_layer» "point_row")) (.n (71 + 78 * p)))
      (mem _ (by simp [glTailSetupP]))) (by omega) (by omega)
    have m7 := good_mul (g (.mul (.n (73 + 78 * p)) (.n (72 + 78 * p)) (.n (70 + 78 * p)))
      (mem _ (by simp [glTailSetupP]))) (by omega) (by omega)
    have c8 : σ (.n (74 + 78 * p)) = word (2 ^ (42 + 2 * p)) 0 :=
      g (.const (.n (74 + 78 * p)) (word (2 ^ (42 + 2 * p)) 0)) (mem _ (by simp [glTailSetupP]))
    have m9 := good_mul (g (.mul (.n (75 + 78 * p)) (.n (valf% «gkr_layer» "point_row")) (.n (74 + 78 * p)))
      (mem _ (by simp [glTailSetupP]))) (by omega) (by omega)
    have m10 := good_mul (g (.mul (.n (76 + 78 * p)) (.n (75 + 78 * p)) (.n (70 + 78 * p)))
      (mem _ (by simp [glTailSetupP]))) (by omega) (by omega)
    have e71 : σ (.n (70 + 78 * p)) = gen ^ (8 * m) := by rw [m4, m3, m2]; exact m8 _ e3
    have hD : glD p = 78 * p + 6 := by simp [glD, hp0]
    have hTP : ∀ s ∈ glTailLoads p (glW p), s ∈ glTailSetup p := fun s hs ↦ by
      simp only [glTailSetup, hp0, ↓reduceIte, glTailSetupP]
      exact List.mem_append_right _ (by simpa [glW, hp0] using hs)
    obtain ⟨L1, L2, L3, L4⟩ := glc_tloads (C := C) (kret := kret) (p := p)
      (fun s hs ↦ hG s (hTP s hs)) hk (rec := head * gen ^ m)
      (by simp only [glW, hp0, ↓reduceIte]; rw [m1, e54, e3]) hR
    refine ⟨?_, ?_, ?_, L2, L3, L4⟩
    · simp only [glTailSetup, hp0, ↓reduceIte, glTailSetupP]
      rw [tb_holdsList_append_noRet (by rfl)]
      refine ⟨?_, by simpa [glW, hp0] using L1⟩
      simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
      exact ⟨m1, m2, m3, m4, c5, m6, m7, c8, m9, m10⟩
    · rw [hD, show 67 + (78 * p + 6) = 73 + 78 * p by ring, m7, m6, c5, e71, e53,
        tb_word_two_pow (by omega)]
    · rw [hD, show 70 + (78 * p + 6) = 76 + 78 * p by ring, m10, m9, c8, e71, e53,
        tb_word_two_pow (by omega), show 42 + 2 * p = 2 * p + 42 by ring, pow_add]
      ring

/-- **The row's zero cell** at an odd depth, `ntpt[1]`. -/
theorem glc_pad {p o : ℕ} (hG : ∀ s ∈ glPad p o, GoodS rd S w σ s)
    (hz : o = 1 → LoadHolds rd (σ (.n (70 + glD p))) 1 0) :
    Stmt.HoldsList C rd σ (glPad p o) True kret := by
  unfold glPad at hG ⊢
  split
  · rename_i h1
    have c : σ (.n (117 + glD p)) = word 0 0 := hG (.atom (.const (.n (117 + glD p)) (word 0 0)))
      (by simp [h1])
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
    refine ⟨c, ?_⟩
    rw [c, tb_word_zero]; exact hz h1
  · trivial

end
end LeanVM.Guest.B1.Tables
