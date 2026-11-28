import Statement.Verifier.Lib

/-!
# The link's functions on the Rust's values

`crates/verifier/src/link.rs`'s functions, as the statement transcribes them
(`Statement/Verifier/Link.lean`), on values the Rust computes: `Chunks::new` at every
width from `0` to `25`; `eq_at`, `shift_eq`, `less_than`, `prefix_sum`, `omega_at` and
`window_shift` at fixed points; `round_coefficients`; `Functionals`' mirrors, values and summand
on fixed bit-slices at widths `1`, `3`, `10`, `17` and `24`; `pointer_width`; and `Links::pointers`,
`Links::max_shift` and `packed_challenges` on tables shaped as `tables()`'s links are (their
state and program pointers, and their accesses' pointers and shifts). The points are the Rust's
test points, `point(seed, n)[h] = E::new(31·seed + 7h + 3, seed ^ h)`; the slices are
`E::new(i² + 1, i ^ 5)`. Each check is a `#guard`, evaluated as the module builds.
-/

namespace LeanVMTests.Protocol.Link

open LeanVM.Parameters LeanVM.Protocol.Verifier

/-- `E::new(a, b)`. -/
def e (a b : ℕ) : E := E.ofLimbs (K.ofBits a) (K.ofBits b)

/-- The Rust's test point `point(seed, n)`. -/
def point (seed n : ℕ) : List E :=
  (List.range n).map fun h ↦ e (seed * 31 + h * 7 + 3) (seed ^^^ h)

/-- The bit-slices `E::new(i² + 1, i ^ 5)`. -/
def slicesOf : List E := (List.range 64).map fun i ↦ e (i * i + 1) (i ^^^ 5)

/-- A table whose links have the cycle pointer `cycle`, the program pointer `bc`, and an access
per pointer and shift. -/
def shapeTable (cycle bc : ℕ) (pointers shifts : List ℕ) : Table :=
  { opcode := 0, columns := [], padding := []
    links :=
      { state := some { cycle, pc := 0, fp := 0, next := ({}, {}) }
        bytecode := some { pointer := bc, pc := 0, opcode := 0, operands := [] }
        memory := (pointers.zip shifts).map fun (p, s) ↦
          { pointer := p, shift := s, gate := none, address := {}, frame := none, value := {},
            reads := [] } } }

/-- The chunks of a `width`-bit pointer. -/
def chunksOf (width : ℕ) : Chunks := (Chunks.new width).getD default

/-- The functionals at `point(4, width)`, up to shift `3`. -/
def functionalsAt (width : ℕ) : Functionals := Functionals.new (chunksOf width) (point 4 width) 3

/-- Their values on the slices. -/
def valuesAt (width : ℕ) : List E := (functionalsAt width).values (chunksOf width) slicesOf

/-- The summand at `c = E::new(11, 12)`, `c_s = E::new(12 + s, s)` and the certificates
`point(5, d)`. -/
def summandAt (width : ℕ) : E :=
  (functionalsAt width).summand (e 11 12) [e 13 1, e 14 2, e 15 3] (valuesAt width)
    (point 5 (chunksOf width).d)

/-- `tables()`'s links' shapes, in opcode order. -/
def shapes : List Table :=
  [shapeTable 6 5 [2, 3, 4] [0, 0, 0], shapeTable 8 7 [4, 5, 6] [0, 0, 0], shapeTable 4 3 [2] [0],
    shapeTable 9 8 [5, 6, 7] [0, 0, 0], shapeTable 13 12 [9, 10, 11] [0, 0, 0],
    shapeTable 67 66 [58, 59, 60, 61, 62, 62, 62, 62, 63, 64, 64, 64, 64, 65, 65, 65, 65, 65, 65,
    65, 65, 65, 65, 65, 65, 65] [0, 0, 0, 0, 0, 1, 2, 3, 0, 0, 1, 2, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8,
    9, 10, 11, 12]]

/-! The Rust forms the Hotwire bridges state (`LeanVM/Facts/Hotwire.lean`: `linkEqAt_eq`,
`linkShiftEq_eq_shiftSum`, `linkWindowShift_eq`, `one_add_paddingWeight_eq_mle`) are the
statement's definitions, by unfolding. -/

example (pt : List E) (j : ℕ) : linkEqAt pt j =
    pt.zipIdx.foldl (fun acc p ↦ acc * if j >>> p.2 % 2 = 1 then p.1 else 1 + p.1) 1 := rfl

example (ζ r : List E) : linkShiftEq ζ r =
    ((ζ.zip r).foldl (fun acc zx ↦ (acc.1 * (1 + zx.1 + zx.2) + acc.2 * (1 + zx.2) * zx.1,
      acc.2 * (zx.2 * (1 + zx.1)))) (0, 1)).1 := rfl

example (r0 : List E) (s : ℕ) : linkWindowShift (eqKernel r0) s =
    (List.range (eqKernel r0).length).map fun v ↦ (eqKernel r0).getD (v + s) 0 := rfl

example (pt : List E) (n : ℕ) : lessThan pt n = 1 + paddingWeight pt n := rfl

#guard Chunks.new 0 == none
#guard Chunks.new 1 == some ⟨1, [1], [0], [0]⟩
#guard Chunks.new 2 == some ⟨2, [2], [0], [0]⟩
#guard Chunks.new 3 == some ⟨3, [3], [0], [0]⟩
#guard Chunks.new 4 == some ⟨4, [4], [0], [0]⟩
#guard Chunks.new 5 == some ⟨5, [4, 1], [0, 4], [0, 16]⟩
#guard Chunks.new 6 == some ⟨6, [4, 2], [0, 4], [0, 16]⟩
#guard Chunks.new 7 == some ⟨7, [4, 3], [0, 4], [0, 16]⟩
#guard Chunks.new 8 == some ⟨8, [4, 4], [0, 4], [0, 16]⟩
#guard Chunks.new 9 == some ⟨9, [4, 5], [0, 4], [0, 16]⟩
#guard Chunks.new 10 == some ⟨10, [4, 3, 3], [0, 4, 7], [0, 16, 24]⟩
#guard Chunks.new 11 == some ⟨11, [4, 4, 3], [0, 4, 8], [0, 16, 32]⟩
#guard Chunks.new 12 == some ⟨12, [4, 4, 4], [0, 4, 8], [0, 16, 32]⟩
#guard Chunks.new 13 == some ⟨13, [4, 5, 4], [0, 4, 9], [0, 16, 48]⟩
#guard Chunks.new 14 == some ⟨14, [4, 4, 3, 3], [0, 4, 8, 11], [0, 16, 32, 40]⟩
#guard Chunks.new 15 == some ⟨15, [4, 4, 4, 3], [0, 4, 8, 12], [0, 16, 32, 48]⟩
#guard Chunks.new 16 == some ⟨16, [4, 4, 4, 4], [0, 4, 8, 12], [0, 16, 32, 48]⟩
#guard Chunks.new 17 == some ⟨17, [4, 4, 3, 3, 3], [0, 4, 8, 11, 14], [0, 16, 32, 40, 48]⟩
#guard Chunks.new 18 == some ⟨18, [4, 4, 4, 3, 3], [0, 4, 8, 12, 15], [0, 16, 32, 48, 56]⟩
#guard Chunks.new 19 == some ⟨19, [4, 3, 3, 3, 3, 3], [0, 4, 7, 10, 13, 16], [0, 16, 24, 32, 40,
    48]⟩
#guard Chunks.new 20 == some ⟨20, [4, 4, 3, 3, 3, 3], [0, 4, 8, 11, 14, 17], [0, 16, 32, 40, 48,
    56]⟩
#guard Chunks.new 21 == some ⟨21, [4, 3, 3, 3, 3, 3, 2], [0, 4, 7, 10, 13, 16, 19], [0, 16, 24, 32,
    40, 48, 56]⟩
#guard Chunks.new 22 == some ⟨22, [4, 3, 3, 3, 3, 3, 3], [0, 4, 7, 10, 13, 16, 19], [0, 16, 24, 32,
    40, 48, 56]⟩
#guard Chunks.new 23 == some ⟨23, [4, 3, 3, 3, 3, 3, 2, 2], [0, 4, 7, 10, 13, 16, 19, 21], [0, 16,
    24, 32, 40, 48, 56, 60]⟩
#guard Chunks.new 24 == some ⟨24, [4, 3, 3, 3, 3, 2, 2, 2, 2], [0, 4, 7, 10, 13, 16, 18, 20, 22],
    [0, 16, 24, 32, 40, 48, 52, 56, 60]⟩
#guard Chunks.new 25 == none
#guard linkEqAt (point 1 5) 0 == (e 0x384bf40 0x524300)
#guard linkEqAt (point 1 5) 5 == (e 0x38e3240 0x5209e0)
#guard linkEqAt (point 1 5) 19 == (e 0x391b908 0x5252a4)
#guard linkEqAt (point 1 5) 31 == (e 0x3930140 0x52c14d)
#guard linkShiftEq (point 1 0) (point 2 0) == (e 0x0 0x0)
#guard linkShiftEq (point 1 1) (point 2 1) == (e 0x882 0x0)
#guard linkShiftEq (point 1 2) (point 2 2) == (e 0x5c0f8c 0x3f1a4)
#guard linkShiftEq (point 1 3) (point 2 3) == (e 0x3dc123334 0x2d8e25c4)
#guard linkShiftEq (point 1 4) (point 2 4) == (e 0x16ffa7dc7bbc 0x66ccaf7594)
#guard linkShiftEq (point 1 5) (point 2 5) == (e 0xfb88bc05716584 0x1ee569fd7e3fd4)
#guard linkShiftEq (point 1 6) (point 2 6) == (e 0x19ee1ff02b945764 0x30bb20f72b2e872f)
#guard lessThan (point 3 5) 0 == (e 0x0 0x0)
#guard lessThan (point 3 5) 1 == (e 0x624df260 0x6eedb00)
#guard lessThan (point 3 5) 7 == (e 0x637f45b8 0x6ffa618)
#guard lessThan (point 3 5) 17 == (e 0x630dd1cd 0x6ee2617)
#guard lessThan (point 3 5) 31 == (e 0x63468a13 0x6ea0e0f)
#guard lessThan (point 3 5) 32 == (e 0x1 0x0)
#guard prefixSum (point 6 4) (point 7 4) 0 == (e 0x0 0x0)
#guard prefixSum (point 6 4) (point 7 4) 3 == (e 0x15a77067 0x26cbac)
#guard prefixSum (point 6 4) (point 7 4) 9 == (e 0x1c949324 0x43b213)
#guard prefixSum (point 6 4) (point 7 4) 15 == (e 0x17c3b749 0x3ba022)
#guard prefixSum (point 6 4) (point 7 4) 16 == (e 0x37438c 0x10188)
#guard omegaAt (e 9 9) (point 8 5) (point 9 5) 0 == (e 0x0 0x0)
#guard omegaAt (e 9 9) (point 8 5) (point 9 5) 13 == (e 0xef5cca3765a03491 0xf9083de828638037)
#guard omegaAt (e 9 9) (point 8 5) (point 9 5) 32 == (e 0xb8e163ed 0xbc78860f)
#guard linkWindowShift (eqKernel (point 10 3)) 0 == [(e 0x12d8c44 0x9a494), (e 0x12c9ada 0x9a7d6),
    (e 0x12cfc84 0x9a548), (e 0x12deb5c 0x9a602), (e 0x12cfb32 0x9a60a), (e 0x12deced 0x9a543),
    (e 0x12d8aca 0x9a7dc), (e 0x12c9c52 0x9a49d)]
#guard linkWindowShift (eqKernel (point 10 3)) 1 == [(e 0x12c9ada 0x9a7d6), (e 0x12cfc84 0x9a548),
    (e 0x12deb5c 0x9a602), (e 0x12cfb32 0x9a60a), (e 0x12deced 0x9a543), (e 0x12d8aca 0x9a7dc),
    (e 0x12c9c52 0x9a49d), (e 0x0 0x0)]
#guard linkWindowShift (eqKernel (point 10 3)) 2 == [(e 0x12cfc84 0x9a548), (e 0x12deb5c 0x9a602),
    (e 0x12cfb32 0x9a60a), (e 0x12deced 0x9a543), (e 0x12d8aca 0x9a7dc), (e 0x12c9c52 0x9a49d),
    (e 0x0 0x0), (e 0x0 0x0)]
#guard linkWindowShift (eqKernel (point 10 3)) 3 == [(e 0x12deb5c 0x9a602), (e 0x12cfb32 0x9a60a),
    (e 0x12deced 0x9a543), (e 0x12d8aca 0x9a7dc), (e 0x12c9c52 0x9a49d), (e 0x0 0x0), (e 0x0 0x0),
    (e 0x0 0x0)]
#guard roundCoefficients 1 == (5, 4)
#guard roundCoefficients 2 == (5, 4)
#guard roundCoefficients 3 == (6, 5)
#guard roundCoefficients 4 == (7, 6)
#guard roundCoefficients 5 == (8, 7)
#guard roundCoefficients 6 == (9, 8)
#guard roundCoefficients 7 == (10, 9)
#guard roundCoefficients 8 == (11, 10)
#guard roundCoefficients 9 == (12, 11)
#guard roundCoefficients 10 == (13, 12)
#guard (functionalsAt 1).mirrors == [(e 0x153a 0x24)]
#guard valuesAt 1 == [(e 0x84 0x7e), (e 0x87 0x7f), (e 0x6b 0x1af), (e 0x0 0x0), (e 0x0 0x0)]
#guard summandAt 1 == (e 0x27d0b2 0x167a08)
#guard (functionalsAt 3).mirrors == [(e 0x152d1abacec 0x26dd8a494)]
#guard valuesAt 3 == [(e 0x1eb2bee 0x15f732), (e 0x1ef42a1 0x15e549), (e 0x3f610cd 0x10d16b),
    (e 0x5e142a 0x1a9934), (e 0x170f7c9 0x7c54d)]
#guard summandAt 3 == (e 0xb1b3b759d76dc8 0x504f63fcd1e88)
#guard (functionalsAt 10).mirrors == [(e 0x555bf9513b78c8 0xbc769c7bd7a0),
    (e 0x41d03cd36ac 0x9bae4594), (e 0x45bdae56f28 0x8b0ac7ec)]
#guard valuesAt 10 == [(e 0xb8af536 0x77bb12), (e 0x7340272e 0x16d94da), (e 0x9ddd13a 0x31ddec),
    (e 0xb979879 0x77b671), (e 0x73b884c1 0x16d6ba1), (e 0x9c8ff5d 0x31e3ef),
    (e 0x52a4c3405 0x3692cbdb), (e 0x1ee871e1a 0x1139e1ac), (e 0x71174b1f9 0x4168a49)]
#guard summandAt 10 == (e 0xf7620799e8e24f1d 0x2afc1234d23d9e40)
#guard (functionalsAt 17).mirrors == [(e 0x555bf9513b78c8 0xbc769c7bd7a0),
    (e 0x111f1635d8c7068 0xb6fb33e7a0), (e 0x508a0ce432c 0xa7d541194),
    (e 0x558c2246530 0xaec921ac4), (e 0x50e9ba3ba54 0x216853878c)]
#guard valuesAt 17 == [(e 0xb8af536 0x77bb12), (e 0x34a3d31096 0x1cf615da), (e 0x31e7c6e 0x3abc82),
    (e 0x23d5481a 0x2a548b4), (e 0x5264d2ee 0xde40546), (e 0xb979879 0x77b671),
    (e 0x34bee27f39 0x1cfe1979), (e 0x31a1021 0x3ab079), (e 0x23a9e2fd 0x2a5b917),
    (e 0x5289f1c1 0xde4cc7d), (e 0x52a4c3405 0x3692cbdb), (e 0x1ee871e1a 0x1139e1ac),
    (e 0x71174b1f9 0x4168a49)]
#guard summandAt 17 == (e 0xf375234cc5f6da4e 0x2c1dd6f56186d4a)
#guard (functionalsAt 24).mirrors == [(e 0x555bf9513b78c8 0xbc769c7bd7a0),
    (e 0x41d03cd36ac 0x9bae4594), (e 0x45bdae56f28 0x8b0ac7ec), (e 0x54c39f117b4 0x81319d48c),
    (e 0x54da02b57ec 0x82bf06a20), (e 0x115225d2 0xa71b2), (e 0x54bc57ae 0x2930b0a),
    (e 0x1015d4c3a 0x9a922), (e 0x1057858c6 0x1899a)]
#guard valuesAt 24 == [(e 0xb8af536 0x77bb12), (e 0x7340272e 0x16d94da), (e 0x9ddd13a 0x31ddec),
    (e 0x3b9b18e 0x2b684e), (e 0x27d311f2 0x393fa38), (e 0xc9bb1e 0x4a136), (e 0x4a26fe 0xbc646),
    (e 0x4b039e 0xaa96), (e 0x1f285e 0x1166), (e 0xb979879 0x77b671), (e 0x73b884c1 0x16d6ba1),
    (e 0x9c8ff5d 0x31e3ef), (e 0x3bcb141 0x2b6035), (e 0x27a9d565 0x393086b), (e 0xc99f19 0x4a2b9),
    (e 0x4ab2c1 0xbc699), (e 0x4b04a9 0xaad9), (e 0x1f2b71 0x1179), (e 0x52a4c3405 0x3692cbdb),
    (e 0x1ee871e1a 0x1139e1ac), (e 0x71174b1f9 0x4168a49)]
#guard summandAt 24 == (e 0xd2f3ddd615dd3175 0x6ed0dd27f0748c7d)
#guard pointerWidth 0 0 0 == 1
#guard pointerWidth 10 3 5 == 10
#guard pointerWidth 16 18 1048576 == 21
#guard pointerWidth 12 5 4194303 == 22
#guard pointerWidth 20 9 8388608 == 24
#guard (shapes.getD 0 default).links.pointers == [6, 5, 2, 3, 4]
#guard (shapes.getD 0 default).links.maxShift == 0
#guard (shapes.getD 1 default).links.pointers == [8, 7, 4, 5, 6]
#guard (shapes.getD 1 default).links.maxShift == 0
#guard (shapes.getD 2 default).links.pointers == [4, 3, 2]
#guard (shapes.getD 2 default).links.maxShift == 0
#guard (shapes.getD 3 default).links.pointers == [9, 8, 5, 6, 7]
#guard (shapes.getD 3 default).links.maxShift == 0
#guard (shapes.getD 4 default).links.pointers == [13, 12, 9, 10, 11]
#guard (shapes.getD 4 default).links.maxShift == 0
#guard (shapes.getD 5 default).links.pointers == [67, 66, 58, 59, 60, 61, 62, 63, 64, 65]
#guard (shapes.getD 5 default).links.maxShift == 12
#guard packedChallenges shapes 0 1 == 90
#guard packedChallenges shapes 5 10 == 106
#guard packedChallenges shapes 20 24 == 141
#guard packedChallenges shapes 9 25 == 122

end LeanVMTests.Protocol.Link
