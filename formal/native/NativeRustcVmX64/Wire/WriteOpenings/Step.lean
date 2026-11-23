module

public import NativeRustcVmX64.Wire.WriteOpenings.Entry

/-!
# `write_openings`' steps: shared helpers (x86-64)

The queries' end (`Run.qe`), a frame-word set kept by a block (`FwK`, `fwK_of`), the aliases of a
block's chunks (`al0`, `alN`, `ix_eval`), the comparisons the blocks branch on (`beq_ofNat`,
`beq_qa`), chunks inside the input regions and the phase (`Geo.q_in`, `Geo.p_in`, `Geo.l_in`,
`Geo.o_in`), and what a block keeps of the phase (`Geo.keepF`).
-/

namespace NativeRustcVmX64.Wire.WriteOpenings

open NativeRustcX64 hiding InRange SameOutside
open NativeRustcX64.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmX64.Vm.WriteOpenings
open NativeRustcVmX64.Transcript (Frame MidOk)
open NativeRustcVm (WordAt WordsAt wordOf InRange SameOutside)

@[expose] public section

/-- `x` rounded down to a multiple of four. -/
abbrev q4 (x : Nat) : Nat := x / 4 * 4

/-- The queries' end. -/
abbrev Run.qe (R : Run) : BitVec 64 := R.qa + BitVec.ofNat 64 (8 * R.nq)

/-- The frame words at the offsets `os` kept from `d` to `d'`. -/
def FwK (R : Run) (d d' : Mem 64) (os : List Nat) : Prop :=
  ∀ o ∈ os, ∀ v, R.FW d o v → R.FW d' o v

/-- Registers holding values. -/
def Regs (m : MachineData) (l : List (Reg64 × BitVec 64)) : Prop := ∀ p ∈ l, reg m p.1 = p.2

/-- Frame words holding values. -/
def FWs (R : Run) (d : Mem 64) (l : List (Nat × BitVec 64)) : Prop := ∀ p ∈ l, R.FW d p.1 p.2

/-- The registers `rs` a block keeps. -/
def keepAll (rs : List Reg64) (S : SState) : Bool := rs.all fun r ↦ S.reg r == some (.reg r)

/-- Decides a `keepAll` over a list of register-value pairs. -/
macro "kdec" : tactic => `(tactic| (simp only [List.map_cons, List.map_nil]; decide +kernel))

/-- `b + s i`. -/
abbrev ixs (b i : BitVec 64) (s : Nat) : BitVec 64 := b + i * BitVec.ofNat 64 s

end

public section

variable {R : Run}

theorem FwK.of_eq {d d' : Mem 64} (h : d' = d) (os : List Nat) : FwK R d d' os :=
  fun _ _ _ hw ↦ h ▸ hw

theorem FwK.trans {d d' d'' : Mem 64} {os : List Nat} (h : FwK R d d' os) (h' : FwK R d' d'' os) :
    FwK R d d'' os := fun o ho v hw ↦ h' o ho v (h o ho v hw)

theorem FwK.sub {d d' : Mem 64} {os os' : List Nat} (h : FwK R d d' os) (hs : ∀ o ∈ os', o ∈ os) :
    FwK R d d' os' := fun o ho v hw ↦ h o (hs o ho) v hw

section
variable [Labels]

/-- **The frame words a block keeps**: those no write of it covers. -/
theorem fwK_of {m d' : MachineData} {cs : List (BitVec 64 × Nat)} {ret : BitVec 64} {S : SState}
    (hwf : (envOf R m cs ret).WF) (hm : Match (envOf R m cs ret) S d') {o' : Nat}
    (hok : MidOk 160 o' slots S = true) {os : List Nat} (hmiss : missAll os S = true)
    (hle : os.all (fun o ↦ decide (o + 8 ≤ 168)) = true) : FwK R m.dmem d'.dmem os :=
  fun o ho _ hw ↦ fw_keepAll hwf hm hok hmiss ho (by
    rw [List.all_eq_true] at hle; simpa using hle o ho) hw

end

/-! ## Registers and frame words -/

theorem Regs.get {m : MachineData} {l : List (Reg64 × BitVec 64)} (h : Regs m l) {r : Reg64}
    {v : BitVec 64} (hp : (r, v) ∈ l) : reg m r = v := h _ hp

theorem Regs.keep [Labels] {m m' : MachineData} {l : List (Reg64 × BitVec 64)} (h : Regs m l)
    {rs : List (BitVec 64 × Nat)} {vs : Nat → BitVec 64} {ret : BitVec 64} {S' : SState}
    (hm' : Match (Env.ofMachine m rs vs ret) S' m') (hk : keepAll (l.map Prod.fst) S' = true) :
    Regs m' l := fun p hp ↦ by
  unfold keepAll at hk
  rw [List.all_eq_true] at hk
  have := hk p.1 (List.mem_map_of_mem hp)
  rw [beq_iff_eq] at this
  exact (hm'.regs p.1 _ this).trans (h p hp)

theorem Regs.append {m : MachineData} {l l' : List (Reg64 × BitVec 64)} (h : Regs m l)
    (h' : Regs m l') : Regs m (l ++ l') := fun p hp ↦ by
  rcases List.mem_append.mp hp with hp | hp
  · exact h p hp
  · exact h' p hp

theorem Regs.left {m : MachineData} {l l' : List (Reg64 × BitVec 64)} (h : Regs m (l ++ l')) :
    Regs m l := fun p hp ↦ h p (List.mem_append_left _ hp)

theorem Regs.right {m : MachineData} {l l' : List (Reg64 × BitVec 64)} (h : Regs m (l ++ l')) :
    Regs m l' := fun p hp ↦ h p (List.mem_append_right _ hp)

theorem Regs.nil (m : MachineData) : Regs m [] := fun _ h ↦ absurd h (List.not_mem_nil)

theorem Regs.cons {m : MachineData} {r : Reg64} {v : BitVec 64} {l : List (Reg64 × BitVec 64)}
    (h : reg m r = v) (h' : Regs m l) : Regs m ((r, v) :: l) := fun p hp ↦ by
  rcases List.mem_cons.mp hp with rfl | hp
  · exact h
  · exact h' p hp

theorem FWs.get {d : Mem 64} {l : List (Nat × BitVec 64)} (h : FWs R d l) {o : Nat}
    {v : BitVec 64} (hp : (o, v) ∈ l) : R.FW d o v := by
  have := h (o, v) hp
  dsimp only at this
  exact this

theorem FWs.keep {d d' : Mem 64} {l : List (Nat × BitVec 64)} (h : FWs R d l)
    (hk : FwK R d d' (l.map Prod.fst)) : FWs R d' l :=
  fun p hp ↦ hk p.1 (List.mem_map_of_mem hp) p.2 (h p hp)

theorem FWs.append {d : Mem 64} {l l' : List (Nat × BitVec 64)} (h : FWs R d l) (h' : FWs R d l') :
    FWs R d (l ++ l') := fun p hp ↦ by
  rcases List.mem_append.mp hp with hp | hp
  · exact h p hp
  · exact h' p hp

theorem FWs.left {d : Mem 64} {l l' : List (Nat × BitVec 64)} (h : FWs R d (l ++ l')) :
    FWs R d l := fun p hp ↦ h p (List.mem_append_left _ hp)

theorem FWs.nil (d : Mem 64) : FWs R d [] := fun _ h ↦ absurd h (List.not_mem_nil)

theorem FWs.cons {d : Mem 64} {o : Nat} {v : BitVec 64} {l : List (Nat × BitVec 64)}
    (h : R.FW d o v) (h' : FWs R d l) : FWs R d ((o, v) :: l) := fun p hp ↦ by
  rcases List.mem_cons.mp hp with rfl | hp
  · exact h
  · exact h' p hp

/-- Rebuilds a list of registers from a block's result: each entry the block keeps from `old`,
the others left as goals. -/
macro "keep_regs " hm:term:max old:term:max : tactic => `(tactic| (
  repeat' (first | apply Regs.nil | apply Regs.cons)
  all_goals try exact kreg $hm rfl (Regs.get $old (by simp))))

/-- **A word loaded and stored** by a block: region `r`'s word at `o` is the load's. -/
theorem stored_load [Labels] {env : Env} {S : SState} {m : MachineData} (hm : Match env S m)
    {r o sz : Nat} {b : BitVec 64} (hb : env.regions[r]? = some (b, sz)) (ho : o + 8 ≤ sz)
    {r' o' : Nat} (hw : ∀ i < 8, findWrite r (o + i) S.mem = some (.load r' o' 8, i)) {w : UInt64}
    (hl : env.load r' o' 8 = w.toBitVec) : WordAt m.dmem (b + BitVec.ofNat 64 o) w := by
  have := stored hm hb ho hw
  simp only [Sym.eval] at this
  rw [hl] at this
  exact this

/-- **A register stored** by a block. -/
theorem stored_reg [Labels] {m0 : MachineData} {rs : List (BitVec 64 × Nat)}
    {vs : Nat → BitVec 64} {ret : BitVec 64} {S : SState} {m : MachineData}
    (hm : Match (Env.ofMachine m0 rs vs ret) S m) {r o sz : Nat} {b : BitVec 64}
    (hb : (Env.ofMachine m0 rs vs ret).regions[r]? = some (b, sz)) (ho : o + 8 ≤ sz) {x : Reg64}
    (hw : ∀ i < 8, findWrite r (o + i) S.mem = some (.reg x, i)) {w : UInt64}
    (hl : reg m0 x = w.toBitVec) : WordAt m.dmem (b + BitVec.ofNat 64 o) w := by
  have := stored hm hb ho hw
  simp only [Sym.eval, envRegs] at this
  rw [hl] at this
  exact this

/-- An alias at a region's base. -/
theorem al0 [Labels] {env : Env} {x : Sym} {r : Nat} (h : x.eval env = env.base r) :
    x.eval env = env.base r + BitVec.ofInt 64 0 := by
  rw [NativeRustcVmX64.Transcript.ofInt_zero64, BitVec.add_zero]; exact h

/-- An alias `o` bytes into a region. -/
theorem alN [Labels] {env : Env} {x : Sym} {r o : Nat}
    (h : x.eval env = env.base r + BitVec.ofNat 64 o) :
    x.eval env = env.base r + BitVec.ofInt 64 (o : Int) := by
  rw [BitVec.ofInt_natCast]; exact h

theorem ix_eval [Labels] {m : MachineData} {rs : List (BitVec 64 × Nat)} {vs : Nat → BitVec 64}
    {ret : BitVec 64} (b i : Reg64) (s : Nat) :
    (ix b i s).eval (Env.ofMachine m rs vs ret) = ixs (reg m b) (reg m i) s := by
  simp [ix, Sym.eval, add_eval, mul_eval]

theorem ixs_ofNat (b : BitVec 64) (i s : Nat) :
    ixs b (BitVec.ofNat 64 i) s = b + BitVec.ofNat 64 (s * i) := by
  rw [ixs, ofNat_mul, Nat.mul_comm]

/-- Two numbers below `2 ^ 64` as words: equal iff equal. -/
theorem beq_ofNat {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    (BitVec.ofNat 64 x == BitVec.ofNat 64 y) = (x == y) := by
  by_cases h : x = y
  · subst h; simp
  · rw [beq_eq_false_iff_ne.mpr h, beq_eq_false_iff_ne]
    intro he
    apply h
    have := congrArg BitVec.toNat he
    rwa [toNat_ofNat hx, toNat_ofNat hy] at this

/-- Two offsets of one address: equal iff equal. -/
theorem beq_add {a : BitVec 64} {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    (a + BitVec.ofNat 64 x == a + BitVec.ofNat 64 y) = (x == y) := by
  by_cases h : x = y
  · subst h; simp
  · rw [beq_eq_false_iff_ne.mpr h, beq_eq_false_iff_ne]
    intro he
    apply h
    have := congrArg BitVec.toNat ((BitVec.add_right_inj a).mp he)
    rwa [toNat_ofNat hx, toNat_ofNat hy] at this

/-- A word and a word: equal iff equal. -/
theorem beq_word (a b : UInt64) : (a.toBitVec == b.toBitVec) = decide (a = b) := by
  by_cases h : a = b
  · subst h; simp
  · rw [decide_eq_false h, beq_eq_false_iff_ne]
    exact fun he ↦ h (UInt64.toBitVec_inj.mp he)

/-- A conditional exit, its condition evaluated. -/
theorem pc_cond [Labels] {env : Env} {c : SBool} {l : Label} {next : Int64} {st : MachineState}
    (h : PcOk env (.cond c l) next st) {b : Bool} (hb : c.eval env = b) :
    st.pc = if b then Labels.label l else next := by
  rw [← hb]; exact h

/-- A jump's exit. -/
theorem pc_jump [Labels] {env : Env} {l : Label} {next : Int64} {st : MachineState}
    (h : PcOk env (.jump l) next st) : st.pc = Labels.label l := h

/-- A fall-through's exit. -/
theorem pc_fall [Labels] {env : Env} {next : Int64} {st : MachineState}
    (h : PcOk env .fall next st) : st.pc = next := h

/-- A count of words down by one: `-8 + 8 (k + 1) = 8 k`. -/
theorem dec8 (k : Nat) :
    BitVec.ofNat 64 18446744073709551608 + BitVec.ofNat 64 (8 * (k + 1)) =
      BitVec.ofNat 64 (8 * k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem not_beq_decide (a b : Nat) : (!(a == b)) = decide (a ≠ b) := by
  by_cases h : a = b <;> simp [h]

theorem beq_decide (a b : Nat) : (a == b) = decide (a = b) := by
  by_cases h : a = b <;> simp [h]

theorem oa_add (o x : Nat) : R.oa o + BitVec.ofNat 64 x = R.oa (o + x) :=
  NativeRustcVm.addr_add_add _ _ _

/-- A word of the phase, its offset rewritten. -/
theorem word_at {d : Mem 64} {o x y : Nat} {w : UInt64}
    (h : WordAt d (R.oa o + BitVec.ofNat 64 x) w) (e : o + x = y) : WordAt d (R.oa y) w := by
  rw [oa_add, e] at h; exact h

/-! ## Chunks -/

theorem Geo.q_in (G : Geo R) {j : Nat} (hj : j < R.nq) :
    Inside (R.qa + BitVec.ofNat 64 (8 * j)) 8 (R.big 2) :=
  inside_off (A := R.big 2) (G.noWrap (by omega)) (by show 8 * j + 8 ≤ 8 * R.nq; omega)
    (by omega)

theorem Geo.p_in (G : Geo R) {i : Nat} (hi : i < R.np) :
    Inside (R.pa + BitVec.ofNat 64 (8 * i)) 8 (R.big 3) :=
  inside_off (A := R.big 3) (G.noWrap (by omega)) (by show 8 * i + 8 ≤ 8 * R.np; omega)
    (by omega)

/-- Leaf `i`'s `n` bytes from word `t`. -/
theorem Geo.l_in (G : Geo R) {i t n : Nat} (hi : i < R.np) (htn : 8 * t + n ≤ 512) (hn : 0 < n) :
    Inside (R.lv + BitVec.ofNat 64 (512 * i + 8 * t)) n (R.big 4) :=
  inside_off (A := R.big 4) (G.noWrap (by omega)) (by show _ ≤ 512 * R.np; omega) hn

/-- The phase's `n` bytes from byte `o`. -/
theorem Geo.o_in (G : Geo R) {o n : Nat} (h : o + n ≤ phaseBytes) (hn : 0 < n) :
    Inside (R.oa o) n (R.big 7) :=
  inside_off (A := R.big 7) G.outNw h hn

/-- **Leaf `i`'s word `t + u`**, loaded from a chunk at its word `t`. -/
theorem Geo.lfw_load (G : Geo R) {m : MachineData} (hc : R.Chg m.dmem)
    {rest : List (BitVec 64 × Nat)} {ret : BitVec 64} {i t n u : Nat} (hi : i < R.np)
    (htu : t + u < 64) :
    (envOf R m ((R.lv + BitVec.ofNat 64 (512 * i + 8 * t), n) :: rest) ret).load 2 (8 * u) 8 =
      (R.lfw i (t + u)).toBitVec := by
  have := G.in_load (m := m) (cs := (R.lv + BitVec.ofNat 64 (512 * i + 8 * t), n) :: rest)
    (ret := ret) hc (r := 2) rfl (by omega) (o := 8 * u) (i := 4) (by omega) (by omega) (by
      rw [NativeRustcVm.addr_add_add]
      rw [show 512 * i + 8 * t + 8 * u = 512 * i + 8 * (t + u) by omega]
      exact G.l_in hi (t := t + u) (n := 8) (by omega) (by omega))
  rw [this, NativeRustcVm.addr_add_add, show 512 * i + 8 * t + 8 * u = 512 * i + 8 * (t + u) by omega]
  rfl

/-- The phase's bytes around opening `j`. -/
theorem ob_lt {j : Nat} (hj : j < 256) {o : Nat} (ho : o ≤ 1544) : ob j + o ≤ phaseBytes := by
  have := ob_le hj; omega

end

end NativeRustcVmX64.Wire.WriteOpenings
