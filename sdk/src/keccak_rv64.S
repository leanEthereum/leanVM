// Keccak-f[1600] on rv64im with the whole state in registers, the shape of the scalar
// AArch64 permutation in s2n-bignum (sha3_keccak_f1600.S): 25 lanes in 25 registers for all
// 24 rounds, pi a renaming of registers rather than a move, memory touched once each way.
//
// The round is the one in keccak.rs: lane complementing, theta, then rho, pi and chi plane by
// plane. Five more registers hold the column parities and then take each plane's chi outputs,
// whose inputs become the next plane's spare registers. So the lanes move between registers from
// round to round, and the rounds are unrolled with the registers renamed. rv64im has no rotate:
// theta needs a sixth spare register, so lane aso waits on the stack while the parities are
// combined, and C4 is summed twice rather than kept.
//
// leanvm_keccak_f1600(state: *mut [u64; 25]), lane x + 5y at byte 8(x + 5y).

.equ KECCAK_SAVED, 15 * 8
.equ KECCAK_STATE, KECCAK_SAVED
.equ KECCAK_SPILL, KECCAK_SAVED + 8
.equ KECCAK_FRAME, KECCAK_SAVED + 24 // the two slots, sp kept 16-byte aligned

// The register of lane `lane` rotated left by `r`.
.macro keccak_rot lane, tmp, r
    srli \tmp, \lane, 64 - \r
    slli \lane, \lane, \r
    or \lane, \lane, \tmp
.endm

// acc ^= rot(src, 1): acc holding C[x-1] becomes D[x] for src = C[x+1].
.macro keccak_d acc, src, tmp
    slli \tmp, \src, 1
    xor \acc, \acc, \tmp
    srli \tmp, \src, 63
    xor \acc, \acc, \tmp
.endm

.macro keccak_column c, l0, l1, l2, l3, l4
    xor \c, \l0, \l1
    xor \c, \c, \l2
    xor \c, \c, \l3
    xor \c, \c, \l4
.endm

.macro keccak_apply d, l0, l1, l2, l3, l4
    xor \l0, \l0, \d
    xor \l1, \l1, \d
    xor \l2, \l2, \d
    xor \l3, \l3, \d
    xor \l4, \l4, \d
.endm

// Round `n`. Its outputs, as the next round's arguments: `keccak_next`.
.macro keccak_round n, aba, abe, abi, abo, abu, aga, age, agi, ago, agu, aka, ake, aki, ako, aku, ama, ame, ami, amo, amu, asa, ase, asi, aso, asu, c0, c1, c2, c3, c4
    // Theta: C[x], then D[x] = C[x-1] ^ rot(C[x+1], 1) in the register of a parity no longer needed.
    keccak_column \c0, \aba, \aga, \aka, \ama, \asa
    keccak_column \c1, \abe, \age, \ake, \ame, \ase
    keccak_column \c2, \abi, \agi, \aki, \ami, \asi
    keccak_column \c3, \abo, \ago, \ako, \amo, \aso
    keccak_column \c4, \abu, \agu, \aku, \amu, \asu
    sd \aso, KECCAK_SPILL(sp)
    keccak_d \c4, \c1, \aso
    keccak_apply \c4, \aba, \aga, \aka, \ama, \asa
    keccak_d \c1, \c3, \aso
    keccak_apply \c1, \abi, \agi, \aki, \ami, \asi
    keccak_d \c3, \c0, \aso
    keccak_d \c0, \c2, \aso
    keccak_apply \c0, \abe, \age, \ake, \ame, \ase
    keccak_column \c4, \abu, \agu, \aku, \amu, \asu
    keccak_d \c2, \c4, \aso
    xor \abo, \abo, \c2
    xor \ago, \ago, \c2
    xor \ako, \ako, \c2
    xor \amo, \amo, \c2
    ld \aso, KECCAK_SPILL(sp)
    xor \aso, \aso, \c2
    keccak_apply \c3, \abu, \agu, \aku, \amu, \asu

    // Plane 0 of (a, e, i, o, u) = (aba, age, aki, amo, asu), into c0..c4.
    keccak_rot \age, \c0, 44
    keccak_rot \aki, \c0, 43
    keccak_rot \amo, \c0, 21
    keccak_rot \asu, \c0, 14
    not \c0, \aki
    or \c0, \c0, \amo
    xor \c0, \c0, \age
    and \c1, \amo, \asu
    xor \c1, \c1, \aki
    or \c2, \asu, \aba
    xor \c2, \c2, \amo
    and \c3, \aba, \age
    xor \c3, \c3, \asu
    or \c4, \age, \aki
    xor \c4, \c4, \aba
    lui \aba, %hi({rc} + 8 * (\n))
    ld \aba, %lo({rc} + 8 * (\n))(\aba)
    xor \c4, \c4, \aba

    // Plane 1 of (abo, agu, aka, ame, asi), into plane 0's inputs.
    keccak_rot \abo, \aba, 28
    keccak_rot \agu, \aba, 20
    keccak_rot \aka, \aba, 3
    keccak_rot \ame, \aba, 45
    keccak_rot \asi, \aba, 61
    or \aba, \agu, \aka
    xor \aba, \aba, \abo
    and \age, \aka, \ame
    xor \age, \age, \agu
    not \aki, \asi
    or \aki, \aki, \ame
    xor \aki, \aki, \aka
    or \amo, \asi, \abo
    xor \amo, \amo, \ame
    and \asu, \abo, \agu
    xor \asu, \asu, \asi

    // Plane 2 of (abe, agi, ako, amu, asa), into plane 1's inputs.
    keccak_rot \abe, \abo, 1
    keccak_rot \agi, \abo, 6
    keccak_rot \ako, \abo, 25
    keccak_rot \amu, \abo, 8
    keccak_rot \asa, \abo, 18
    or \abo, \agi, \ako
    xor \abo, \abo, \abe
    and \agu, \ako, \amu
    xor \agu, \agu, \agi
    and \aka, \abe, \agi
    xor \aka, \aka, \asa
    not \amu, \amu
    and \ame, \amu, \asa
    xor \ame, \ame, \ako
    or \asi, \asa, \abe
    xor \asi, \asi, \amu

    // Plane 3 of (abu, aga, ake, ami, aso), into plane 2's inputs.
    keccak_rot \abu, \abe, 27
    keccak_rot \aga, \abe, 36
    keccak_rot \ake, \abe, 10
    keccak_rot \ami, \abe, 15
    keccak_rot \aso, \abe, 56
    and \abe, \aga, \ake
    xor \abe, \abe, \abu
    or \agi, \ake, \ami
    xor \agi, \agi, \aga
    or \ako, \abu, \aga
    xor \ako, \ako, \aso
    not \ami, \ami
    or \amu, \ami, \aso
    xor \amu, \amu, \ake
    and \asa, \aso, \abu
    xor \asa, \asa, \ami

    // Plane 4 of (abi, ago, aku, ama, ase), into plane 3's inputs.
    keccak_rot \abi, \abu, 62
    keccak_rot \ago, \abu, 55
    keccak_rot \aku, \abu, 39
    keccak_rot \ama, \abu, 41
    keccak_rot \ase, \abu, 2
    and \abu, \ama, \ase
    xor \abu, \abu, \aku
    or \aga, \ase, \abi
    xor \aga, \aga, \ama
    and \ake, \abi, \ago
    xor \ake, \ake, \ase
    not \ago, \ago
    and \ami, \ago, \aku
    xor \ami, \ami, \abi
    or \aso, \aku, \ama
    xor \aso, \aso, \ago
.endm

// Rounds n.. two at a time, then the state stored and the caller's registers restored. The
// second round's arguments are where the first left the lanes; the next pair's, where the second did.
.macro keccak_rounds n, aba, abe, abi, abo, abu, aga, age, agi, ago, agu, aka, ake, aki, ako, aku, ama, ame, ami, amo, amu, asa, ase, asi, aso, asu, c0, c1, c2, c3, c4
.if \n < 24
    keccak_round \n, \aba, \abe, \abi, \abo, \abu, \aga, \age, \agi, \ago, \agu, \aka, \ake, \aki, \ako, \aku, \ama, \ame, \ami, \amo, \amu, \asa, \ase, \asi, \aso, \asu, \c0, \c1, \c2, \c3, \c4
    keccak_round (\n + 1), \c4, \c0, \c1, \c2, \c3, \aba, \age, \aki, \amo, \asu, \abo, \agu, \ame, \asi, \aka, \abe, \agi, \amu, \asa, \ako, \ami, \aso, \abu, \aga, \ake, \abi, \ago, \aku, \ama, \ase
    keccak_rounds (\n + 2), \ase, \abi, \ago, \aku, \ama, \c4, \age, \ame, \asa, \ake, \c2, \asu, \agi, \abu, \abo, \c0, \aki, \ako, \ami, \asi, \amu, \aga, \c3, \aba, \agu, \c1, \amo, \aka, \abe, \aso
.else
    ld \c0, KECCAK_STATE(sp)
    not \abe, \abe
    not \abi, \abi
    not \ago, \ago
    not \aki, \aki
    not \ami, \ami
    not \asa, \asa
    sd \aba, 0(\c0)
    sd \abe, 8(\c0)
    sd \abi, 16(\c0)
    sd \abo, 24(\c0)
    sd \abu, 32(\c0)
    sd \aga, 40(\c0)
    sd \age, 48(\c0)
    sd \agi, 56(\c0)
    sd \ago, 64(\c0)
    sd \agu, 72(\c0)
    sd \aka, 80(\c0)
    sd \ake, 88(\c0)
    sd \aki, 96(\c0)
    sd \ako, 104(\c0)
    sd \aku, 112(\c0)
    sd \ama, 120(\c0)
    sd \ame, 128(\c0)
    sd \ami, 136(\c0)
    sd \amo, 144(\c0)
    sd \amu, 152(\c0)
    sd \asa, 160(\c0)
    sd \ase, 168(\c0)
    sd \asi, 176(\c0)
    sd \aso, 184(\c0)
    sd \asu, 192(\c0)
.endif
.endm

.pushsection .text.leanvm_keccak_f1600, "ax", @progbits
.globl leanvm_keccak_f1600
.p2align 2
leanvm_keccak_f1600:
    addi sp, sp, -KECCAK_FRAME
    sd ra, 0(sp)
    sd gp, 8(sp)
    sd tp, 16(sp)
    sd s0, 24(sp)
    sd s1, 32(sp)
    sd s2, 40(sp)
    sd s3, 48(sp)
    sd s4, 56(sp)
    sd s5, 64(sp)
    sd s6, 72(sp)
    sd s7, 80(sp)
    sd s8, 88(sp)
    sd s9, 96(sp)
    sd s10, 104(sp)
    sd s11, 112(sp)
    sd a0, KECCAK_STATE(sp)
    ld s0, 0(a0)
    ld s1, 8(a0)
    ld s2, 16(a0)
    ld s3, 24(a0)
    ld s4, 32(a0)
    ld s5, 40(a0)
    ld s6, 48(a0)
    ld s7, 56(a0)
    ld s8, 64(a0)
    ld s9, 72(a0)
    ld s10, 80(a0)
    ld s11, 88(a0)
    ld a1, 96(a0)
    ld a2, 104(a0)
    ld a3, 112(a0)
    ld a4, 120(a0)
    ld a5, 128(a0)
    ld a6, 136(a0)
    ld a7, 144(a0)
    ld t0, 152(a0)
    ld t1, 160(a0)
    ld t2, 168(a0)
    ld ra, 176(a0)
    ld gp, 184(a0)
    ld tp, 192(a0)
    // Lane complementing: be bi go ki mi sa.
    not s1, s1
    not s2, s2
    not s8, s8
    not a1, a1
    not a6, a6
    not t1, t1
    keccak_rounds 0, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, a1, a2, a3, a4, a5, a6, a7, t0, t1, t2, ra, gp, tp, t3, t4, t5, t6, a0
    ld ra, 0(sp)
    ld gp, 8(sp)
    ld tp, 16(sp)
    ld s0, 24(sp)
    ld s1, 32(sp)
    ld s2, 40(sp)
    ld s3, 48(sp)
    ld s4, 56(sp)
    ld s5, 64(sp)
    ld s6, 72(sp)
    ld s7, 80(sp)
    ld s8, 88(sp)
    ld s9, 96(sp)
    ld s10, 104(sp)
    ld s11, 112(sp)
    addi sp, sp, KECCAK_FRAME
    ret
.popsection
