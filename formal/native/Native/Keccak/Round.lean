module

public import Native.Keccak.Base
public import Statement.Fast.Keccak

/-!
# `Keccak.hash`'s proof: one round

`Keccak.round` runs θ's parities (`thetaC`), θ's effects (`thetaD`), ρ and π (`rhoPiP`), χ
(`chiP`), each a phase of scratch writes, then ι (`iotaP`); it leaves the lanes of `roundLanes`
at `sA` and changes no word outside `sA, …, sB`.
-/

@[expose] public section

namespace Native.Keccak.Proof

open LeanVM.Semantics LeanVM.Fast.Keccak

variable {E : QState → Prop}

/-! ## θ -/

/-- θ's parity of column `x`. -/
def cv (A : KeccakState) (x : Nat) : UInt64 :=
  Keccak.lane A x ^^^ Keccak.lane A (x + 5) ^^^ Keccak.lane A (x + 10) ^^^
    Keccak.lane A (x + 15) ^^^ Keccak.lane A (x + 20)

/-- The round's first phase, column `x`. -/
def thetaC (x : Nat) : List Stmt :=
  [I (.load .rax (atDi (sA + 8 * x.toInt64)))] ++
    ((List.range 4).flatMap fun y ↦
      [I (.load .r8 (atDi (sA + 8 * (x + 5 * (y + 1)).toInt64))), I (.xor .rax .r8)]) ++
    [I (.store (atDi (sC + 8 * x.toInt64)) .rax)]

theorem regs_rax_r8 {s s' : QState} {r : Reg64} (hr : r ∉ [Reg64.rax, .r8])
    (h : ∀ r, r ≠ .rax → r ≠ .r8 → s'.reg r = s.reg r) : s'.reg r = s.reg r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  exact h r hr.1 hr.2

theorem thetaC_spec {A : KeccakState} {base : UInt64} {x : Nat} (hx : x < 5) {s : QState}
    (hrdi : s.reg .rdi = base) (hA : Words s.mem base 0 25 (Keccak.lane A))
    (hS : (s.mem (scratchAddr base (25 + x))).isSome) :
    WP (blk (thetaC x)) s (fun s' ↦
      s'.mem = Function.update s.mem (scratchAddr base (25 + x)) (some (cv A x)) ∧
      RegsFrame [.rax, .r8] s s') E := by
  simp only [thetaC, List.range_succ, List.range_zero, List.nil_append, List.flatMap_cons,
    List.flatMap_nil, List.cons_append, List.append_nil]
  refine wp_load_scr (k := 0 + x) hrdi (by addr_tac) (hA x (by omega)) ?_
  refine wp_load_scr (k := 0 + (x + 5 * (0 + 1))) (by simp [hrdi]) (by addr_tac)
    (hA _ (by omega)) ?_
  refine wp_op rfl ?_
  refine wp_load_scr (k := 0 + (x + 5 * (1 + 1))) (by simp [hrdi]) (by addr_tac)
    (hA _ (by omega)) ?_
  refine wp_op rfl ?_
  refine wp_load_scr (k := 0 + (x + 5 * (2 + 1))) (by simp [hrdi]) (by addr_tac)
    (hA _ (by omega)) ?_
  refine wp_op rfl ?_
  refine wp_load_scr (k := 0 + (x + 5 * (3 + 1))) (by simp [hrdi]) (by addr_tac)
    (hA _ (by omega)) ?_
  refine wp_op rfl ?_
  refine wp_store_scr (k := 25 + x) (by simp [hrdi]) (by addr_tac) hS ?_
  refine WP.blk_nil ⟨?_, fun r hr ↦ regs_rax_r8 hr fun r h1 h2 ↦ by simp [h1, h2]⟩
  simp [QState.setMem, cv]

/-- θ's effect on column `x`. -/
def dv (A : KeccakState) (x : Nat) : UInt64 :=
  cv A ((x + 4) % 5) ^^^ Keccak.rot (cv A ((x + 1) % 5)) 1

/-- The round's second phase, column `x`. -/
def thetaD (x : Nat) : List Stmt :=
  [I (.load .rax (atDi (sC + 8 * ((x + 4) % 5).toInt64))),
    I (.load .r8 (atDi (sC + 8 * ((x + 1) % 5).toInt64))),
    I (.roli .r8 1), I (.xor .rax .r8),
    I (.store (atDi (sD + 8 * x.toInt64)) .rax)]

theorem thetaD_spec {A : KeccakState} {base : UInt64} {x : Nat} {s : QState}
    (hrdi : s.reg .rdi = base) (hC : Words s.mem base 25 5 (cv A))
    (hS : (s.mem (scratchAddr base (30 + x))).isSome) :
    WP (blk (thetaD x)) s (fun s' ↦
      s'.mem = Function.update s.mem (scratchAddr base (30 + x)) (some (dv A x)) ∧
      RegsFrame [.rax, .r8] s s') E := by
  refine wp_load_scr (k := 25 + (x + 4) % 5) hrdi (by addr_tac) (hC _ (by omega)) ?_
  refine wp_load_scr (k := 25 + (x + 1) % 5) (by simp [hrdi]) (by addr_tac) (hC _ (by omega)) ?_
  refine wp_op rfl ?_
  refine wp_op rfl ?_
  refine wp_store_scr (k := 30 + x) (by simp [hrdi]) (by addr_tac) hS ?_
  refine WP.blk_nil ⟨?_, fun r hr ↦ regs_rax_r8 hr fun r h1 h2 ↦ by simp [h1, h2]⟩
  simp [QState.setMem, dv, rotl_eq_rot]

/-! ## ρ and π -/

/-- Lane `j` after ρ and π. -/
def bv (A : KeccakState) (j : Nat) : UInt64 :=
  Keccak.rot (Keccak.lane A (rhoPi.getD j (0, 0)).1 ^^^ dv A ((rhoPi.getD j (0, 0)).1 % 5))
    (rhoPi.getD j (0, 0)).2

/-- The round's third phase, lane `j`. -/
def rhoPiP (j : Nat) : List Stmt :=
  let (i, r) := rhoPi.getD j (0, 0)
  [I (.load .rax (atDi (sA + 8 * i.toInt64))),
    I (.load .r8 (atDi (sD + 8 * (i % 5).toInt64))),
    I (.xor .rax .r8), I (.roli .rax r),
    I (.store (atDi (sB + 8 * j.toInt64)) .rax)]

theorem rhoPi_bounds : ∀ j < 25, (rhoPi.getD j (0, 0)).1 < 25 ∧ (rhoPi.getD j (0, 0)).2 < 64 := by
  decide

theorem rhoPiP_spec {A : KeccakState} {base : UInt64} {j : Nat} (hj : j < 25) {s : QState}
    (hrdi : s.reg .rdi = base) (hA : Words s.mem base 0 25 (Keccak.lane A))
    (hD : Words s.mem base 30 5 (dv A)) (hS : (s.mem (scratchAddr base (35 + j))).isSome) :
    WP (blk (rhoPiP j)) s (fun s' ↦
      s'.mem = Function.update s.mem (scratchAddr base (35 + j)) (some (bv A j)) ∧
      RegsFrame [.rax, .r8] s s') E := by
  have hb := rhoPi_bounds j hj
  unfold rhoPiP bv
  generalize rhoPi.getD j (0, 0) = p at hb ⊢
  obtain ⟨i, r⟩ := p
  obtain ⟨hi, hr⟩ := hb
  simp only at hi hr
  refine wp_load_scr (k := 0 + i) hrdi (by addr_tac) (hA _ hi) ?_
  refine wp_load_scr (k := 30 + i % 5) (by simp [hrdi]) (by addr_tac) (hD _ (by omega)) ?_
  refine wp_op rfl ?_
  refine wp_op rfl ?_
  refine wp_store_scr (k := 35 + j) (by simp [hrdi]) (by addr_tac) hS ?_
  refine WP.blk_nil ⟨?_, fun r hr ↦ regs_rax_r8 hr fun r h1 h2 ↦ by simp [h1, h2]⟩
  simp [QState.setMem, rotl_eq_rot _ hr]

/-! ## χ and ι -/

/-- Lane `j` after χ. -/
def chiv (A : KeccakState) (j : Nat) : UInt64 :=
  bv A j ^^^ (~~~ bv A (j - j % 5 + (j + 1) % 5) &&& bv A (j - j % 5 + (j + 2) % 5))

/-- The round's fourth phase, lane `j`. -/
def chiP (j : Nat) : List Stmt :=
  let row := j - j % 5
  [I (.load .rax (atDi (sB + 8 * (row + (j + 1) % 5).toInt64))), I (.not .rax),
    I (.load .r8 (atDi (sB + 8 * (row + (j + 2) % 5).toInt64))), I (.and .rax .r8),
    I (.load .r8 (atDi (sB + 8 * j.toInt64))), I (.xor .r8 .rax),
    I (.store (atDi (sA + 8 * j.toInt64)) .r8)]

theorem chiP_spec {A : KeccakState} {base : UInt64} {j : Nat} (hj : j < 25) {s : QState}
    (hrdi : s.reg .rdi = base) (hB : Words s.mem base 35 25 (bv A))
    (hS : (s.mem (scratchAddr base (0 + j))).isSome) :
    WP (blk (chiP j)) s (fun s' ↦
      s'.mem = Function.update s.mem (scratchAddr base (0 + j)) (some (chiv A j)) ∧
      RegsFrame [.rax, .r8] s s') E := by
  unfold chiP
  refine wp_load_scr (k := 35 + (j - j % 5 + (j + 1) % 5)) hrdi (by addr_tac)
    (hB _ (by omega)) ?_
  refine wp_op rfl ?_
  refine wp_load_scr (k := 35 + (j - j % 5 + (j + 2) % 5)) (by simp [hrdi]) (by addr_tac)
    (hB _ (by omega)) ?_
  refine wp_op rfl ?_
  refine wp_load_scr (k := 35 + j) (by simp [hrdi]) (by addr_tac) (hB _ hj) ?_
  refine wp_op rfl ?_
  refine wp_store_scr (k := 0 + j) (by simp [hrdi]) (by addr_tac) hS ?_
  refine WP.blk_nil ⟨?_, fun r hr ↦ regs_rax_r8 hr fun r h1 h2 ↦ by simp [h1, h2]⟩
  simp [QState.setMem, chiv]

/-- ι. -/
def iotaP : List Stmt :=
  [I (.load .rax { base := .rdi, idx := some (.rcx, .W64), disp := sRC }),
    I (.load .r8 (atDi sA)), I (.xor .r8 .rax), I (.store (atDi sA) .r8)]

theorem iotaP_spec {base : UInt64} {i : Nat} {s : QState} {l rc : UInt64}
    (hrdi : s.reg .rdi = base) (hrcx : s.reg .rcx = i.toUInt64)
    (hRC : s.mem (scratchAddr base (60 + i)) = some rc) (hl : s.mem (scratchAddr base 0) = some l) :
    WP (blk iotaP) s (fun s' ↦
      s'.mem = Function.update s.mem (scratchAddr base 0) (some (l ^^^ rc)) ∧
      RegsFrame [.rax, .r8] s s') E := by
  refine wp_load (a := scratchAddr base (60 + i)) ?_ hRC ?_
  · open scoped UInt64.CommRing in
    simp only [Addr.eval, hrdi, hrcx, scratchAddr, Width.bytes, sRC, Nat.toUInt64_eq,
      UInt64.ofNat_add, UInt64.ofNat_mul, UInt64.reduceOfNat, i64_lit]
    ring
  refine wp_load_scr (k := 0) (by simp [hrdi]) (by decide) hl ?_
  refine wp_op rfl ?_
  refine wp_store_scr (base := base) (k := 0) (by simp [hrdi]) (by decide)
    (by simp only [QState.setReg_mem, hl]; rfl) ?_
  refine WP.blk_nil ⟨?_, fun r hr ↦ regs_rax_r8 hr fun r h1 h2 ↦ by simp [h1, h2]⟩
  simp [QState.setMem]

theorem roundLanes_lane (A : KeccakState) (rc : UInt64) :
    ∀ t < 25, Keccak.lane (roundLanes A rc) t = if t = 0 then chiv A 0 ^^^ rc else chiv A t := by
  intro t ht
  interval_cases t <;> rfl

/-! ## The round -/

theorem round_eq : round = blk ((List.range 5).flatMap thetaC ++
    (List.range 5).flatMap thetaD ++ (List.range 25).flatMap rhoPiP ++
    (List.range 25).flatMap chiP ++ iotaP) := (rfl)

/-- **One round**: the lanes at `sA` become `roundLanes`', the round constant `rc` read at
`sRC + 8 · i` for `rcx = i`. -/
theorem round_spec {base : UInt64} {A : KeccakState} {i : Nat} {rc : UInt64} {s : QState}
    (hrdi : s.reg .rdi = base) (hok : ScrOk s.mem base)
    (hA : Words s.mem base 0 25 (Keccak.lane A)) (hrcx : s.reg .rcx = i.toUInt64)
    (hRC : s.mem (scratchAddr base (60 + i)) = some rc) (hi : 60 + i < 84) :
    WP round s (fun s' ↦ ScrOk s'.mem base ∧ RegsFrame [.rax, .r8] s s' ∧
      ScrFrame base 0 60 s.mem s'.mem ∧ Words s'.mem base 0 25 (Keccak.lane (roundLanes A rc)))
      E := by
  rw [round_eq]
  refine wp_blk_append (wp_blk_append (wp_blk_append (wp_blk_append ?_)))
  refine WP.mono (phase_run thetaC 25 5 (cv A) [.rax, .r8] (by omega) (by simp)
    (fun j hj s' h1 h2 h3 _ ↦ thetaC_spec hj h1 (hA.frame h2 (by omega) (by omega) (by omega))
      (h3.isSome (by omega))) hrdi hok) ?_ (fun _ h ↦ h)
  rintro s1 ⟨hok1, hR1, hF1, hC1⟩
  have hrdi1 : s1.reg .rdi = base := (hR1 _ (by simp)).trans hrdi
  refine WP.mono (phase_run thetaD 30 5 (dv A) [.rax, .r8] (by omega) (by simp)
    (fun j hj s' h1 h2 h3 _ ↦ thetaD_spec h1 (hC1.frame h2 (by omega) (by omega) (by omega))
      (h3.isSome (by omega))) hrdi1 hok1) ?_ (fun _ h ↦ h)
  rintro s2 ⟨hok2, hR2, hF2, hD2⟩
  have hrdi2 : s2.reg .rdi = base := (hR2 _ (by simp)).trans hrdi1
  have hA2 := (hA.frame hF1 (by omega) (by omega) (by omega)).frame hF2 (by omega) (by omega)
    (by omega)
  refine WP.mono (phase_run rhoPiP 35 25 (bv A) [.rax, .r8] (by omega) (by simp)
    (fun j hj s' h1 h2 h3 _ ↦ rhoPiP_spec hj h1 (hA2.frame h2 (by omega) (by omega) (by omega))
      (hD2.frame h2 (by omega) (by omega) (by omega)) (h3.isSome (by omega))) hrdi2 hok2) ?_
    (fun _ h ↦ h)
  rintro s3 ⟨hok3, hR3, hF3, hB3⟩
  have hrdi3 : s3.reg .rdi = base := (hR3 _ (by simp)).trans hrdi2
  refine WP.mono (phase_run chiP 0 25 (chiv A) [.rax, .r8] (by omega) (by simp)
    (fun j hj s' h1 h2 h3 _ ↦ chiP_spec hj h1 (hB3.frame h2 (by omega) (by omega) (by omega))
      (h3.isSome (by omega))) hrdi3 hok3) ?_ (fun _ h ↦ h)
  rintro s4 ⟨hok4, hR4, hF4, hX4⟩
  have hrdi4 : s4.reg .rdi = base := (hR4 _ (by simp)).trans hrdi3
  have hF : ScrFrame base 0 60 s.mem s4.mem :=
    ((((hF1.widen (lo' := 0) (hi' := 60) (by omega) (by omega)).trans hF2 (by omega)
      (by omega)).trans hF3 (by omega) (by omega)).trans hF4 (by omega) (by omega))
  have hrcx4 : s4.reg .rcx = i.toUInt64 := by
    rw [hR4 _ (by simp), hR3 _ (by simp), hR2 _ (by simp), hR1 _ (by simp), hrcx]
  have hRC4 : s4.mem (scratchAddr base (60 + i)) = some rc := by
    rw [hF.word (by omega) hi (by omega)]
    exact hRC
  refine WP.mono (iotaP_spec hrdi4 hrcx4 hRC4 (by simpa using hX4 0 (by omega))) ?_ (fun _ h ↦ h)
  rintro s5 ⟨hm5, hR5⟩
  have hR : RegsFrame [.rax, .r8] s s4 :=
    RegsFrame.trans (RegsFrame.trans (RegsFrame.trans hR1 hR2) hR3) hR4
  refine ⟨?_, RegsFrame.trans hR hR5, ?_, ?_⟩
  · rw [hm5]
    exact hok4.update _ _
  · rw [hm5]
    exact hF.trans (ScrFrame.update (lo := 0) (hi := 1) (k := 0) (by omega) (by omega)) le_rfl
      (by omega)
  · intro t ht
    rw [roundLanes_lane A rc t ht, hm5]
    by_cases h0 : t = 0
    · subst h0
      simp
    · rw [Function.update_of_ne (scratchAddr_ne (by omega) (by omega) (by omega))]
      simp only [h0, ↓reduceIte]
      simpa using hX4 t ht

end Native.Keccak.Proof
