import LeanVM.Guest.Exec

/-!
# The symbolic executor on guest functions

`exec` evaluated by the kernel on compiled functions of different shapes, with the facts each
needs (generated from the bytecode: the powers of `g` its `SET`s name, a loop's self frame
pointer cell, `main`'s frame `1`):

* `assert_canonical`, straight code: its one segment, its atoms, and its contract by
  `exec_sound`, the run returning in fewer steps;
* `__loop0`, a loop helper: the tail call to the next frame `fp·g^16` on a branch, then the
  return;
* `da_vector_dispatch`, a forward branch and its join, through a self frame pointer bounced
  through a hinted cell;
* `da_list_digest`, a fused table dispatch: a call into the callee frame `fp[9]` whose return
  pc is the join at offset `7`;
* `main` and `grind_check`, linked.
-/

namespace LeanVMTests.Guest.Exec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Exec

/-! ## `assert_canonical` -/

def F2 : Facts := {}

/-- Its atoms: the instructions it executes, the not-taken `JUMP` reading its cells in `K`, and
the return. -/
def canonicalAtoms : List Atom :=
  [.instr 4783 (.xor 2 4 5), .instr 4784 (.set 6 1 0 1), .instr 4785 (.mul 5 6 7),
    .instr 4786 (.set 8 0 0 0), .jump 8 4 7, .instr 4788 (.set 3 0 0 0),
    .instr 4789 (.set 9 1 0 0), .jump 9 0 1]

theorem canonical_shape : (exec F2 Data.f2).segs.map (fun s ↦ (s.start, s.env.sub Sym.beq .nil,
    (branchExits s.items).isEmpty, s.items.filterMap Item.atom?, s.exit.kind)) =
      [(0, true, true, canonicalAtoms, .ret)] := by
  decide +kernel

/-- **`assert_canonical`'s contract**, from the executor: a halting run entering it returns, in
fewer steps, with every atom holding. -/
theorem canonical_spec {κ : ℕ} {L : MemImage κ} (hκ : κ ≤ 32) :
    FunSpec guest L 4783 (fun _ ↦ True) (fun fp ↦ ∀ a ∈ canonicalAtoms, a.Holds L fp) := by
  intro fp k _ h
  obtain ⟨s, hs, he⟩ := List.mem_map.mp (canonical_shape ▸ List.mem_singleton_self _)
  simp only [Prod.mk.injEq] at he
  obtain ⟨h0, henv, hb, hatoms, hkind⟩ := he
  have hctx : Ctx F2 κ fp := ⟨trivial, fun h ↦ absurd h (by decide), hκ⟩
  have hentry : Data.f2.entry + s.start = 4783 := by rw [h0]; rfl
  have hrun := exec_sound hctx (guest_fetches (mem_functions (j := 2) rfl)) hs
    (EnvHolds.nil.sub henv) (hentry ▸ h)
  obtain ⟨hall, k', -, hlt, -, -, r, hr, hsafe⟩ :=
    RunK.straight (List.isEmpty_iff.mp hb) hrun
  rw [hkind] at hr
  exact ⟨k', hlt, r, hr, hatoms ▸ hall, hsafe⟩

/-! ## Other shapes -/

def F31 : Facts where
  env := [(5, .fpg 0)]
  scaled := [5]
  pows := (.node 65536 16 (.node 2 1 .leaf .leaf) (.node 6562775826835341521 78895 .leaf .leaf))

def F27 : Facts where
  pows := (.node 9223372036854775983 127 (.node 6647501145143662796 176798 (.node 6069848660758997429 179222 .leaf .leaf) .leaf) (.node 12060818041379662471 78104 (.node 9463924850925913143 78090 .leaf .leaf) .leaf))

def F28 : Facts where
  pows := (.node 365034048459132197 78115 .leaf .leaf)

def F1 : Facts where
  fpOne := true
  pows := (.node 7167479045172100979 4657 (.node 2742287972818379206 4791 (.node 139298 257 (.node 65536 16 (.node 2 1 .leaf .leaf) .leaf) (.node 2100987625415436551 4755 (.node 156645908148787 262143 .leaf .leaf) .leaf)) (.node 6490334292723863085 78953 (.node 5794507937549519934 4764 (.node 3916432595873351572 74683 .leaf .leaf) .leaf) (.node 6562775826835341521 78895 .leaf .leaf))) (.node 11681089550692230304 78120 (.node 9272771591053052074 65535 (.node 9262365267281685472 76295 (.node 8505647924979083422 78108 .leaf .leaf) .leaf) (.node 10683087727989742573 75492 (.node 10452479293323663173 78136 .leaf .leaf) .leaf)) (.node 16669948859450948282 78985 (.node 14024268205854977662 78933 (.node 12060547623566316098 78913 .leaf .leaf) .leaf) (.node 17872441827613743139 79021 .leaf .leaf))))

def F4 : Facts where
  pows := (.node 8589934592 33 (.node 131072 17 (.node 512 9 (.node 32 5 (.node 8 3 (.node 4 2 (.node 2 1 .leaf .leaf) .leaf) (.node 16 4 .leaf .leaf)) (.node 128 7 (.node 64 6 .leaf .leaf) (.node 256 8 .leaf .leaf))) (.node 8192 13 (.node 2048 11 (.node 1024 10 .leaf .leaf) (.node 4096 12 .leaf .leaf)) (.node 32768 15 (.node 16384 14 .leaf .leaf) (.node 65536 16 .leaf .leaf)))) (.node 33554432 25 (.node 2097152 21 (.node 524288 19 (.node 262144 18 .leaf .leaf) (.node 1048576 20 .leaf .leaf)) (.node 8388608 23 (.node 4194304 22 .leaf .leaf) (.node 16777216 24 .leaf .leaf))) (.node 536870912 29 (.node 134217728 27 (.node 67108864 26 .leaf .leaf) (.node 268435456 28 .leaf .leaf)) (.node 2147483648 31 (.node 1073741824 30 .leaf .leaf) (.node 4294967296 32 .leaf .leaf))))) (.node 1125899906842624 50 (.node 4398046511104 42 (.node 274877906944 38 (.node 68719476736 36 (.node 34359738368 35 (.node 17179869184 34 .leaf .leaf) .leaf) (.node 137438953472 37 .leaf .leaf)) (.node 1099511627776 40 (.node 549755813888 39 .leaf .leaf) (.node 2199023255552 41 .leaf .leaf))) (.node 70368744177664 46 (.node 17592186044416 44 (.node 8796093022208 43 .leaf .leaf) (.node 35184372088832 45 .leaf .leaf)) (.node 281474976710656 48 (.node 140737488355328 47 .leaf .leaf) (.node 562949953421312 49 .leaf .leaf)))) (.node 288230376151711744 58 (.node 18014398509481984 54 (.node 4503599627370496 52 (.node 2251799813685248 51 .leaf .leaf) (.node 9007199254740992 53 .leaf .leaf)) (.node 72057594037927936 56 (.node 36028797018963968 55 .leaf .leaf) (.node 144115188075855872 57 .leaf .leaf))) (.node 2092093120342337205 79162 (.node 1152921504606846976 60 (.node 576460752303423488 59 .leaf .leaf) (.node 1516574801963302816 4932 .leaf .leaf)) (.node 4611686018427387904 62 (.node 2305843009213693952 61 .leaf .leaf) (.node 9223372036854775808 63 .leaf .leaf))))))


/-- `__loop0`: one segment, the return at its end and, on the branch, the tail call to its own
entry at the next frame `fp·g^16`. -/
example : (exec F31 Data.f31).segs.map (fun s ↦ (s.start, s.exits.map (·.kind))) =
    [(0, [.ret, .jump (.gp 78895) (.fpg 16)])] ∧ (exec F31 Data.f31).linked = true := by
  decide +kernel

/-- `da_list_digest`: the fused dispatch enters the callee frame `fp[9]` at the pc read from the
table into `fp[11]`, its return pc `g^78115` the join at offset `7`. -/
example : (exec F28 Data.f28).segs.map (fun s ↦ (s.start, s.exits.map (·.kind),
    s.exits.map (·.succ))) =
      [(7, [.ret], [[]]), (0, [.call (.cell 11) 9 78115], [[7]])] ∧
    (exec F28 Data.f28).linked = true := by
  decide +kernel

theorem dispatch_linked : (exec F27 Data.f27).linked = true := by decide +kernel
theorem main_linked : (exec F1 Data.f1).linked = true := by decide +kernel
theorem grind_linked : (exec F4 Data.f4).linked = true := by decide +kernel

end LeanVMTests.Guest.Exec
