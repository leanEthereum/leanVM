module

public import NativeRustcX64.Sym.Sound.Data

/-!
# Shifts and rotations are sound

`OpOk` for `SHL`, `SHR`, `SAR`, `ROL`, `ROR`, `SHLD` and `SHRD`: a count of zero writes the
destination back and keeps the flags (`all_ite_beq`); otherwise the value is Kraken's and the
flags `shiftFlags` keeps are Kraken's, whatever Kraken chooses for the flags it leaves undefined
(`all_choice`).
-/

namespace NativeRustcX64.Sym

public section

theorem all_ite_beq {n : Nat} {A B : Effects} {post : MachineState → Prop}
    (hA : n = 0 → A.All post) (hB : n ≠ 0 → B.All post) : (if n == 0 then A else B).All post := by
  by_cases h : n = 0
  · rw [ite_pos (by simp [h])]
    exact hA h
  · rw [ite_neg (by simp [h])]
    exact hB h

theorem shiftCount_lt {w : Width} (hw : w = .W32 ∨ w = .W64) (y : BitVec 64) :
    shiftCount w y < w.bits := by
  have := Nat.and_le_right (n := (low .W8 y).toNat) (m := shiftMask w)
  unfold shiftCount
  rcases hw with rfl | rfl <;> simp only [shiftMask, Width.bits] at this ⊢ <;> omega

variable [Labels] {env : Env} {w : Width}

omit [Labels] in
theorem msb_shiftLeft_sub {n : Nat} (A : BitVec n) {k : Nat} (h0 : 0 < k) (hk : k < n) :
    (A <<< (n - k)).msb = A.getLsbD (k - 1) := by
  rw [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_shiftLeft, show n - 1 - (n - k) = k - 1 by omega]
  have h1 : n - 1 < n := by omega
  have h2 : ¬n - 1 < n - k := by omega
  simp [h1, h2]

theorem eval_msb_shl (a : Sym) {j : Nat} (hj : j < w.bits) :
    (SBool.msb w (.bin .shl w a (.lit j))).eval env = (low w (a.eval env) <<< j).msb := by
  simp only [SBool.eval, Sym.eval, BinOp.apply, low_ext, shiftCount_lit w j hj]

/-- CF by `shiftCF`, of a nonzero count: the last bit `SHL` shifts out. -/
theorem shiftCF_shl {a : Sym} {k : Nat} {b : SBool} (h : shiftCF .shl w a k = some b) :
    k < w.bits ∧ b.eval env = (low w (a.eval env) <<< (k - 1)).msb := by
  unfold shiftCF at h
  split at h
  · rename_i hk
    cases h
    exact ⟨hk, eval_msb_shl a (by omega)⟩
  · cases h

/-- CF by `shiftCF`, of a nonzero count: the last bit `SHR` or `SAR` shifts out. -/
theorem shiftCF_shr {op : BinOp} (hop : op = .shr ∨ op = .sar) {a : Sym} {k : Nat} {b : SBool}
    (h0 : k ≠ 0) (h : shiftCF op w a k = some b) :
    k < w.bits ∧ b.eval env = (low w (a.eval env)).getLsbD (k - 1) := by
  unfold shiftCF at h
  split at h
  · rename_i hk
    have hb : b = .msb w (.bin .shl w a (.lit (w.bits - k))) := by
      rcases hop with rfl | rfl <;> (cases h; rfl)
    subst hb
    exact ⟨hk, (eval_msb_shl a (by omega)).trans (msb_shiftLeft_sub _ (by omega) hk)⟩
  · cases h

omit [Labels] in
theorem getLsbD_sshiftRight_zero {n : Nat} (A : BitVec n) {s : Nat} (hs : s < n) :
    (A.sshiftRight s).getLsbD 0 = A.getLsbD s := by
  have h1 : ¬n ≤ 0 := by omega
  rw [BitVec.getLsbD_sshiftRight, ite_pos (by omega), Nat.add_zero]
  simp [h1]

omit [Labels] in
/-- A choice that, under `c`, is `b`. -/
theorem all_choice_eq {c : Prop} [Decidable c] {b : Bool} {k : Bool → Effects}
    {post : MachineState → Prop} (h : ∀ v, (c → v = b) → (k v).All post) :
    (if c then k b else undefined k).All post := by
  split
  · rename_i hc
    exact h b fun _ => rfl
  · rename_i hc
    exact fun v => h v fun h' => absurd h' hc

theorem shiftFlags_zero {f : SFlags} {st : StatusFlags} (hf : FlagsOk env f st) (op : BinOp)
    (rot : Bool) {a v n : Sym} (h0 : shiftCount w (n.eval env) = 0) :
    FlagsOk env (shiftFlags f op rot w a v n) st := by
  unfold shiftFlags
  split
  · rename_i k hk
    rw [asLit_eq hk] at h0
    simp only [Sym.eval] at h0
    rw [ite_pos (by simp [h0])]
    exact hf
  · exact flagsOk_unknown st

theorem shiftFlags_shift {f : SFlags} {op : BinOp} {a v n : Sym} {vv : w.type}
    (hv : v.eval env = ext w vv) (h0 : shiftCount w (n.eval env) ≠ 0)
    {rem : StatusFlags.from_result.Remaining}
    (hcf : ∀ b, shiftCF op w a (shiftCount w (n.eval env)) = some b → rem.cf = b.eval env) :
    FlagsOk env (shiftFlags f op false w a v n) (StatusFlags.from_result vv rem) := by
  unfold shiftFlags
  split
  · rename_i k hk
    rw [asLit_eq hk] at h0 hcf
    simp only [Sym.eval] at h0 hcf
    rw [ite_neg (by simp [h0]), ite_neg Bool.false_ne_true]
    exact flagsOk_result env hv hcf nofun
  · exact flagsOk_unknown _

theorem shiftFlags_rot {f : SFlags} {st : StatusFlags} (hf : FlagsOk env f st) {op : BinOp}
    {a v n : Sym} (h0 : shiftCount w (n.eval env) ≠ 0) (cf of : Bool) :
    FlagsOk env (shiftFlags f op true w a v n) { st with cf, of } := by
  unfold shiftFlags
  split
  · rename_i k hk
    rw [asLit_eq hk] at h0
    simp only [Sym.eval] at h0
    rw [ite_neg (by simp [h0]), ite_pos rfl]
    exact ⟨nofun, hf.2.1, hf.2.2.1, nofun⟩
  · exact flagsOk_unknown _

/-- A register operand read. -/
theorem Match.readReg {S : SState} {m : MachineData} (hm : Match env S m) {r : Reg w} {v : Sym}
    (h : S.getR r = some v) (p : Std.Rco Int64) {ret : w.type → MachineData → Effects}
    {post : MachineState → Prop} (hret : (ret (low w (v.eval env)) m).All post) :
    (r.interp m p ret).All post := by
  show (ret (m.regs.get r) m).All post
  rw [hm.getR h]
  exact hret

omit [Labels] in
theorem rotateLeft_zero' {n : Nat} (x : BitVec n) : x.rotateLeft 0 = x := by
  ext i hi
  simp [BitVec.getElem_rotateLeft]

omit [Labels] in
theorem rotateRight_zero' {n : Nat} (x : BitVec n) : x.rotateRight 0 = x := by
  ext i hi
  simp [BitVec.getElem_rotateRight, hi]

omit [Labels] in
/-- The shifts and rotations by a count of zero. -/
theorem apply_count_zero (op : BinOp) (hop : op = .shl ∨ op = .shr ∨ op = .sar ∨ op = .rol ∨
    op = .ror) (x y : BitVec 64) (h0 : shiftCount w y = 0) :
    op.apply w x y = ext w (low w x) := by
  rcases hop with rfl | rfl | rfl | rfl | rfl <;> simp only [BinOp.apply, h0]
  · rw [BitVec.shiftLeft_zero]
  · rw [show (low w x).ushiftRight 0 = low w x from BitVec.ushiftRight_zero _]
  · rw [BitVec.sshiftRight_zero]
  · rw [rotateLeft_zero']
  · rw [rotateRight_zero']

omit [Labels] in
/-- The step of a shift or rotation, unpacked. -/
theorem shift_step {op : BinOp} {rot : Bool} {dst : Dst w} {c : ShiftCountExpr} {S S' : SState}
    {x : Exit} (h : Step.shift op rot dst c S = some (S', x)) :
    ∃ a n, S.readRM dst = some a ∧ S.count c = some n ∧
      (S.setFlags (shiftFlags S.flags op rot w a (mkBin op w a n) n)).writeDst dst
        (mkBin op w a n) =
        some S' ∧ x = .fall := by
  simp only [Step.shift, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨a, ha, n, hn, h⟩ := h
  obtain ⟨hS, rfl⟩ := step_write h
  exact ⟨a, n, ha, hn, hS, rfl⟩

theorem ok_shl (dst : Dst w) (c : ShiftCountExpr) : OpOk env (.shl dst c) := by
  intro S S' x m p hwf hm h _
  obtain ⟨a, n, ha, hn, hS, rfl⟩ := shift_step (rot := false) (op := .shl) h
  unfold Operation.interp
  refine hm.readRM hwf ha p ?_
  refine all_ite_beq (fun h0 => ?_) (fun h0 => ?_) <;> rw [hm.count hn p w] at h0
  · exact (hm.setFlags _ (shiftFlags_zero hm.flags _ false h0)).writeDst hwf hS
      (by rw [eval_mkBin, apply_count_zero _ (by simp) _ _ h0]) p fun _ hm' => done_fall hm'
  · have hv : (mkBin .shl w a n).eval env =
        ext w (low w (a.eval env) <<< c.interpMasked m p w) := by
      rw [eval_mkBin, hm.count hn p w]
      rfl
    intro af
    refine all_choice_eq fun cf hcf => ?_
    refine all_choice fun of => ?_
    refine (hm.setFlags _ (shiftFlags_shift hv h0 fun b hb => ?_)).writeDst hwf hS hv p
      fun _ hm' => done_fall hm'
    obtain ⟨hk, hb⟩ := shiftCF_shl hb
    rw [hm.count hn p w] at hcf
    exact (hcf hk).trans hb.symm

theorem ok_shr (dst : Dst w) (c : ShiftCountExpr) : OpOk env (.shr dst c) := by
  intro S S' x m p hwf hm h _
  obtain ⟨a, n, ha, hn, hS, rfl⟩ := shift_step (rot := false) (op := .shr) h
  unfold Operation.interp
  refine hm.readRM hwf ha p ?_
  refine all_ite_beq (fun h0 => ?_) (fun h0 => ?_) <;> rw [hm.count hn p w] at h0
  · exact (hm.setFlags _ (shiftFlags_zero hm.flags _ false h0)).writeDst hwf hS
      (by rw [eval_mkBin, apply_count_zero _ (by simp) _ _ h0]) p fun _ hm' => done_fall hm'
  · have hv : (mkBin .shr w a n).eval env =
        ext w ((low w (a.eval env)).ushiftRight (c.interpMasked m p w)) := by
      rw [eval_mkBin, hm.count hn p w]
      rfl
    intro af
    refine all_choice_eq fun cf hcf => ?_
    refine all_choice fun of => ?_
    refine (hm.setFlags _ (shiftFlags_shift hv h0 fun b hb => ?_)).writeDst hwf hS hv p
      fun _ hm' => done_fall hm'
    obtain ⟨hk, hb⟩ := shiftCF_shr (.inl rfl) h0 hb
    rw [hm.count hn p w] at hcf
    exact (hcf hk).trans hb.symm

theorem ok_sar (dst : Dst w) (c : ShiftCountExpr) : OpOk env (.sar dst c) := by
  intro S S' x m p hwf hm h _
  obtain ⟨a, n, ha, hn, hS, rfl⟩ := shift_step (rot := false) (op := .sar) h
  unfold Operation.interp
  refine hm.readRM hwf ha p ?_
  refine all_ite_beq (fun h0 => ?_) (fun h0 => ?_) <;> rw [hm.count hn p w] at h0
  · exact (hm.setFlags _ (shiftFlags_zero hm.flags _ false h0)).writeDst hwf hS
      (by rw [eval_mkBin, apply_count_zero _ (by simp) _ _ h0]) p fun _ hm' => done_fall hm'
  · have hv : (mkBin .sar w a n).eval env =
        ext w ((low w (a.eval env)).sshiftRight (c.interpMasked m p w)) := by
      rw [eval_mkBin, hm.count hn p w]
      rfl
    intro af
    refine all_choice fun of => ?_
    refine (hm.setFlags _ (shiftFlags_shift hv h0 fun b hb => ?_)).writeDst hwf hS hv p
      fun _ hm' => done_fall hm'
    obtain ⟨hk, hb⟩ := shiftCF_shr (.inr rfl) h0 hb
    show ((low w (a.eval env)).sshiftRight (c.interpMasked m p w - 1)).getLsbD 0 = _
    rw [hm.count hn p w, hb]
    exact getLsbD_sshiftRight_zero _ (by omega)

theorem ok_rol (dst : Dst w) (c : ShiftCountExpr) : OpOk env (.rol dst c) := by
  intro S S' x m p hwf hm h _
  obtain ⟨a, n, ha, hn, hS, rfl⟩ := shift_step (rot := true) (op := .rol) h
  unfold Operation.interp
  refine hm.readRM hwf ha p ?_
  refine all_ite_beq (fun h0 => ?_) (fun h0 => ?_) <;> rw [hm.count hn p w] at h0
  · exact (hm.setFlags _ (shiftFlags_zero hm.flags _ true h0)).writeDst hwf hS
      (by rw [eval_mkBin, apply_count_zero _ (by simp) _ _ h0]) p fun _ hm' => done_fall hm'
  · have hv : (mkBin .rol w a n).eval env =
        ext w ((low w (a.eval env)).rotateLeft (c.interpMasked m p w)) := by
      rw [eval_mkBin, hm.count hn p w]
      rfl
    refine all_choice fun of => ?_
    exact (hm.setFlags _ (shiftFlags_rot hm.flags h0 _ _)).writeDst hwf hS hv p
      fun _ hm' => done_fall hm'

theorem ok_ror (dst : Dst w) (c : ShiftCountExpr) : OpOk env (.ror dst c) := by
  intro S S' x m p hwf hm h _
  obtain ⟨a, n, ha, hn, hS, rfl⟩ := shift_step (rot := true) (op := .ror) h
  unfold Operation.interp
  refine hm.readRM hwf ha p ?_
  refine all_ite_beq (fun h0 => ?_) (fun h0 => ?_) <;> rw [hm.count hn p w] at h0
  · exact (hm.setFlags _ (shiftFlags_zero hm.flags _ true h0)).writeDst hwf hS
      (by rw [eval_mkBin, apply_count_zero _ (by simp) _ _ h0]) p fun _ hm' => done_fall hm'
  · have hv : (mkBin .ror w a n).eval env =
        ext w ((low w (a.eval env)).rotateRight (c.interpMasked m p w)) := by
      rw [eval_mkBin, hm.count hn p w]
      rfl
    refine all_choice fun of => ?_
    exact (hm.setFlags _ (shiftFlags_rot hm.flags h0 _ _)).writeDst hwf hS hv p
      fun _ hm' => done_fall hm'

omit [Labels] in
/-- The step of a double-precision shift, unpacked. -/
theorem shiftD_step {op : TernOp} {dst : Dst w} {src : Reg w} {c : ShiftCountExpr}
    {S S' : SState} {x : Exit} (h : Step.shiftD op dst src c S = some (S', x)) :
    (w = .W32 ∨ w = .W64) ∧ ∃ a b n, S.readRM dst = some a ∧ S.getR src = some b ∧
      S.count c = some n ∧ (S.setFlags unknownFlags).writeDst dst (.tern op w a b n) = some S' ∧
      x = .fall := by
  cases w with
  | W32 | W64 =>
    simp only [Step.shiftD, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨a, ha, b, hb, n, hn, h⟩ := h
    obtain ⟨hS, rfl⟩ := step_write h
    exact ⟨by simp, a, b, n, ha, hb, hn, hS, rfl⟩
  | W8 | W16 => cases h

theorem shiftD_ok (op : TernOp) {dst : Dst w} {src : Reg w} {c : ShiftCountExpr}
    (hop : op = .shld ∨ op = .shrd) : OpOk env (match op with
      | .shld => Operation.shld dst src c
      | .shrd => Operation.shrd dst src c) := by
  intro S S' x m p hwf hm h _
  have h' : Step.shiftD op dst src c S = some (S', x) := by
    rcases hop with rfl | rfl <;> exact h
  obtain ⟨hw, a, b, n, ha, hb, hn, hS, rfl⟩ := shiftD_step h'
  have hu0 : ∀ y, shiftCount w y = 0 → TernOp.apply op w (a.eval env) (b.eval env) y =
      ext w (low w (a.eval env)) := by
    intro y h0
    rcases hop with rfl | rfl <;> simp [TernOp.apply, h0]
  rcases hop with rfl | rfl <;> unfold Operation.interp <;>
    refine hm.readRM hwf ha p (hm.readReg hb p ?_) <;>
    refine all_ite_beq (fun h0 => ?_) (fun h0 => ?_) <;> rw [hm.count hn p w] at h0 <;>
    first
    | exact (hm.setFlags _ (flagsOk_unknown m.status)).writeDst hwf hS (hu0 _ h0) p
        fun _ hm' => done_fall hm'
    | have hle : ¬c.interpMasked m p w > w.bits := by
        rw [hm.count hn p w]
        have := shiftCount_lt hw (n.eval env)
        omega
      dsimp only
      simp only [hle, ↓reduceIte]
      intro af
      split
      all_goals first | intro _ | skip
      all_goals
        refine (hm.setFlags _ (flagsOk_unknown _)).writeDst hwf hS ?_ p fun _ hm' => done_fall hm'
        show TernOp.apply _ w (a.eval env) (b.eval env) (n.eval env) = _
        rw [hm.count hn p w]
        simp only [TernOp.apply]
        rw [ite_neg (by simpa using h0)]

theorem ok_shld (dst : Dst w) (src : Reg w) (c : ShiftCountExpr) : OpOk env (.shld dst src c) :=
  shiftD_ok .shld (.inl rfl)

theorem ok_shrd (dst : Dst w) (src : Reg w) (c : ShiftCountExpr) : OpOk env (.shrd dst src c) :=
  shiftD_ok .shrd (.inr rfl)

end

end NativeRustcX64.Sym
