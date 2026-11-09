/-
  LeanVM.Guest.B1.VerifySub.H.Mid

  An honest child's runs between the bus challenges and the ring map: the bus's GKR, the tables,
  the Keccak reduction, each ending with nothing waiting, the claimed bytecode point, and the
  committed outputs' claim.
-/

module

public import LeanVM.Guest.B1.VerifySub.H.Front
public import LeanVM.Guest.B1.VerifySub.H.Vt
public import LeanVM.Guest.B1.VerifySub.Lanes
public import LeanVM.Guest.B1.Gkr.VbgAt

/-!
# The middle runs

* `squeezeN_pend`: after a squeeze nothing waits.
* `gkr_end`: a run of `gkrPhase depth` (`1 ≤ depth`) ends with nothing waiting.
* `claimed_point`: a run of `tablesSeg` on the claimed evaluator `c` asks the bytecode at `c`'s
  point: `c.bytecodePoint = point.take logBytecode ++ alphas`.
* `keccakSeg_shape`, `keccakSeg_end`: `keccakSeg` returns one committed outputs' claim on
  `q_keccak`, and ends with a squeeze.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

theorem squeezeN_pend_of : ∀ (n : ℕ) (s : Fs), s.pend = [] → (s.squeezeN n).2.pend = []
  | 0, _, h => h
  | n + 1, s, _ => squeezeN_pend_of n s.squeeze.2 rfl

theorem squeezeN_capOf (n : ℕ) : ∀ (s : Fs), ∃ K, (s.squeezeN (n + 1)).2 = ⟨capOf K, []⟩ := by
  induction n with
  | zero => intro s; exact ⟨s.perm, by simp only [Fs.squeezeN, Fs.squeeze]⟩
  | succ n ih =>
    intro s
    obtain ⟨K, hK⟩ := ih s.squeeze.2
    exact ⟨K, by rw [← hK, Fs.squeezeN]⟩

/-- **A run of the bus's GKR ends on a permutation's capacity**, nothing waiting. -/
theorem gkr_capOf {depth : ℕ} (hd : 1 ≤ depth) {cap0 xs : List E} {r : E × List E × List E}
    {sF : Fs} (h : RunsTo (Tables.gkrPhase depth) ⟨cap0, []⟩ xs r sF)
    (hc : ∃ sp, (⟨cap0, []⟩ : Fs).Carries sp) : ∃ K, sF = ⟨capOf K, []⟩ := by
  obtain ⟨-, -, -, -, -, hsF, -, -⟩ := Tables.gk_walk h hc
  rw [hsF]
  rcases h2 : depth / 2 with _ | k
  · have h1 : depth % 2 = 1 := by omega
    rw [h1]
    simp only [Tables.gkSl, Tables.gkSl0, ↓reduceIte, Tables.GkStepD.s']
    exact squeezeN_capOf 0 _
  · simp only [Tables.gkSl, Tables.GkStepD.s']
    exact squeezeN_capOf 1 _

/-- A property of nothing a program returns, after a step that ensures it. -/
theorem always_const {α β : Type} {Q : Prop} {p : VerifierProgram α} {f : α → VerifierProgram β}
    (hp : Always p fun _ ↦ Q) : Always (p.bind f) fun _ ↦ Q :=
  Always.bind (fun _ hq ↦ Always.mono (fun _ _ ↦ hq) _ (always_true _)) p hp

/-- **The claimed evaluator is asked at its point.** -/
theorem claimed_point {c : BytecodeClaim} {L : Layout} {pi : Digest} {alphas : List E} {beta : E}
    {point values : List E} {s s' : Fs} {xs : List E} {bc : BusResult × List ColumnClaim}
    (h : RunsTo (Tables.tablesSeg (claimedBytecodeValue c) L pi alphas beta point values) s
        xs bc s')
    (hc : ∃ sp, s.Carries sp) : c.bytecodePoint = point.take L.logBytecode ++ alphas := by
  obtain ⟨sp, hsp⟩ := hc
  refine (RunsTo.always (P := fun _ ↦ point.take L.logBytecode ++ alphas = c.bytecodePoint) h hsp
    ?_).symm
  unfold Tables.tablesSeg
  simp only [VerifierProgram.bind_eq]
  refine always_const ?_
  unfold Tables.busRest
  simp only [VerifierProgram.bind_eq]
  refine Always.bind (fun _ _ ↦ ?_) _ (always_true _)
  refine Always.bind (fun _ _ ↦ ?_) _ (always_true _)
  refine Always.bind (fun _ _ ↦ ?_) _ (always_true _)
  refine always_const ?_
  simp only [claimedBytecodeValue, VerifierProgram.bind_eq]
  exact Always.bind (fun _ hq ↦ by show _ = _; exact hq) _ (always_require _)

/-- **`keccakSeg` returns one committed outputs' claim, on `q_keccak`.** -/
theorem keccakSeg_shape {τ : ℕ} {inst out : List E} {s t : Fs} {xs : List E}
    {km : (List ColumnClaim × List E × List E) × E}
    (h : RunsTo (keccakSeg τ inst out) s xs km t) (hc : ∃ sp, s.Carries sp) :
    ∃ op word, km.1.1 = [⟨qkeccak, op, word⟩] := by
  obtain ⟨sp, hsp⟩ := hc
  obtain ⟨sp', -, e⟩ := h sp hsp [] [] []
  have hr := VerifierProgram.returns_of_run keccak256 keccakF1600 e
  unfold keccakSeg at hr
  obtain ⟨r, hr1, hr2⟩ := VerifierProgram.returns_bind hr
  obtain ⟨m, -, hr2⟩ := VerifierProgram.returns_bind hr2
  rw [VerifierProgram.returns_ret hr2]
  unfold verifyKeccak at hr1
  obtain ⟨_, -, hr1⟩ := VerifierProgram.returns_bind hr1
  obtain ⟨_, -, hr1⟩ := VerifierProgram.returns_bind hr1
  obtain ⟨_, -, hr1⟩ := VerifierProgram.returns_bind hr1
  obtain ⟨_, -, hr1⟩ := VerifierProgram.returns_bind hr1
  obtain ⟨⟨slot, weights, value⟩, -, hr1⟩ := VerifierProgram.returns_bind hr1
  dsimp only at hr1
  obtain ⟨word, -, hr1⟩ := VerifierProgram.returns_bind hr1
  obtain ⟨_, -, hr1⟩ := VerifierProgram.returns_bind hr1
  obtain ⟨outs, ho, hr1⟩ := VerifierProgram.returns_bind hr1
  cases ho
  obtain ⟨⟨low, value'⟩, -, hr1⟩ := VerifierProgram.returns_bind hr1
  dsimp only at hr1
  obtain ⟨⟨slot', weights', value''⟩, -, hr1⟩ := VerifierProgram.returns_bind hr1
  dsimp only at hr1
  obtain ⟨_, -, hr1⟩ := VerifierProgram.returns_bind hr1
  obtain ⟨_, -, hr1⟩ := VerifierProgram.returns_bind hr1
  cases hr1
  exact ⟨_, _, rfl⟩

/-- **`keccakSeg` ends with a squeeze**: nothing waits. -/
theorem keccakSeg_end {τ : ℕ} {inst out : List E} {s t : Fs} {xs : List E}
    {km : (List ColumnClaim × List E × List E) × E}
    (h : RunsTo (keccakSeg τ inst out) s xs km t) (hc : ∃ sp, s.Carries sp) :
    t = ⟨t.cap, []⟩ := by
  unfold keccakSeg at h
  simp only [VerifierProgram.bind_eq] at h
  obtain ⟨r, xs1, xs2, t1, -, h1, h2⟩ := Tables.RunsTo.unbind h hc
  have c1 := Tables.RunsTo.carries h1 hc
  obtain ⟨m, ys1, ys2, u1, hy, q1, q2⟩ := Tables.RunsTo.unbind h2 c1
  obtain ⟨-, eu1, -⟩ := Tables.runsTo_det q1 (runsTo_sampleE _) c1 (r1 := ys2) (r2 := ys1 ++ ys2)
    (by simp)
  obtain ⟨-, et, -⟩ := Tables.runsTo_ret_inv q2 (Tables.RunsTo.carries q1 c1)
  rw [et, eu1]
  rfl

/-- **`keccakSeg` ends on a permutation's capacity**, nothing waiting. -/
theorem keccakSeg_capOf {τ : ℕ} {inst out : List E} {s t : Fs} {xs : List E}
    {km : (List ColumnClaim × List E × List E) × E}
    (h : RunsTo (keccakSeg τ inst out) s xs km t) (hc : ∃ sp, s.Carries sp) :
    ∃ K, t = ⟨capOf K, []⟩ := by
  unfold keccakSeg at h
  simp only [VerifierProgram.bind_eq] at h
  obtain ⟨r, xs1, xs2, t1, -, h1, h2⟩ := Tables.RunsTo.unbind h hc
  have c1 := Tables.RunsTo.carries h1 hc
  obtain ⟨m, ys1, ys2, u1, hy, q1, q2⟩ := Tables.RunsTo.unbind h2 c1
  obtain ⟨-, eu1, -⟩ := Tables.runsTo_det q1 (runsTo_sampleE _) c1 (r1 := ys2) (r2 := ys1 ++ ys2)
    (by simp)
  obtain ⟨-, et, -⟩ := Tables.runsTo_ret_inv q2 (Tables.RunsTo.carries q1 c1)
  exact ⟨t1.perm, by rw [et, eu1]; rfl⟩

end
end LeanVM.Guest.B1.VerifySub
