import Rv64Verifier.Proofs.Runtime.CopyBlocks

/-! # The forward copy's blocks in `memcpy` and in `memmove`, checked -/

namespace Rv64Verifier.Runtime.Forward
open RiscvZkvm.Rv64 Rv64Verifier.Sym Rv64Verifier.Runtime.Memcpy

def memcpyCode : FwdCode where
  size := 0x80011ffc
  small := 0x8001212c
  jmp := 0x80012138
  bytes := 0x80012168
  ret := 0x80012180
  head := 0x80012004
  headPre := 0x80012014
  headLoop := 0x80012020
  setup := 0x80012038
  co := 0x8001213c
  coPre := 0x80012140
  coLoop := 0x80012144
  tail := 0x80012158
  sh0 := 0x80012050
  pt2 := 0x80012070
  pt4 := 0x80012078
  pw := 0x80012080
  pe := 0x80012090
  lpre := 0x800120a4
  loop := 0x800120ac
  after := 0x800120d4
  qt2 := 0x800120e8
  qt1 := 0x800120f0
  qb := 0x800120f8
  fin := 0x8001210c
  pb := 0x80012188
  ph := 0x8001219c
  pj := 0x800121b8
  qw := 0x800121bc
  qh := 0x800121d0
  qj := 0x800121f0

theorem memcpy_size : Spec 0x80011ffc (sizeE 0x8001212c 0x80012004) :=
  spec_ofA 18431 2 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem memcpy_small : Spec 0x8001212c (smallE 0x80012168 0x80012138) :=
  spec_ofA 18507 3 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem memcpy_jmp : Spec 0x80012138 (jmpE 0x80012180) :=
  spec_ofA 18510 1 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem memcpy_head : Spec 0x80012004 (headE 0x80012038 0x80012014) :=
  spec_ofA 18433 4 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem memcpy_headPre : Spec 0x80012014 (headPreE 0x80012020) :=
  spec_ofA 18437 3 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem memcpy_setup : Spec 0x80012038 (setupE 0x8001213c 0x80012050) :=
  spec_ofA 18446 6 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem memcpy_co : Spec 0x8001213c (coE 0x80012158 0x80012140) :=
  spec_ofA 18511 1 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem memcpy_coPre : Spec 0x80012140 (coPreE 0x80012144) :=
  spec_ofA 18512 1 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem memcpy_coLoop : Spec 0x80012144 (coLoopE 0x80012144 0x80012158) :=
  spec_ofA 18513 5 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem memcpy_tail : Spec 0x80012158 (tailBE 0x80012180 0x80012168) :=
  spec_ofA 18518 4 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem memcpy_sh0 : Spec 0x80012050 (sh0E 0x80012188 0x80012070) :=
  spec_ofA 18452 8 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem memcpy_pt2 : Spec 0x80012070 (pt2E 0x8001219c 0x80012078) :=
  spec_ofA 18460 2 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem memcpy_pt4 : Spec 0x80012078 (pt4E 0x80012090 0x80012080) :=
  spec_ofA 18462 2 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem memcpy_pw : Spec 0x80012080 (pwE 0x80012090) :=
  spec_ofA 18464 4 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem memcpy_pe : Spec 0x80012090 (peE 0x800120d4 0x800120a4) :=
  spec_ofA 18468 5 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem memcpy_lpre : Spec 0x800120a4 (lpreE 0x800120ac) :=
  spec_ofA 18473 2 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem memcpy_loop : Spec 0x800120ac (loopE 0x800120ac 0x800120d4) :=
  spec_ofA 18475 10 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem memcpy_after : Spec 0x800120d4 (afterE 0x800121bc 0x800120e8) :=
  spec_ofA 18485 5 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem memcpy_qt2 : Spec 0x800120e8 (qt2E 0x800121d0 0x800120f0) :=
  spec_ofA 18490 2 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem memcpy_qt1 : Spec 0x800120f0 (qt1E 0x8001210c 0x800120f8) :=
  spec_ofA 18492 2 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem memcpy_qb : Spec 0x800120f8 (qbE 0x8001210c) :=
  spec_ofA 18494 5 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem memcpy_fin : Spec 0x8001210c (finE 0x80012158) :=
  spec_ofA 18499 8 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem memcpy_pb : Spec 0x80012188 (pbE 0x80012078 0x8001219c) :=
  spec_ofA 18530 5 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem memcpy_ph : Spec 0x8001219c (phE 0x80012080 0x800121b8) :=
  spec_ofA 18535 7 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem memcpy_pj : Spec 0x800121b8 (jmpE 0x80012090) :=
  spec_ofA 18542 1 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem memcpy_qw : Spec 0x800121bc (qwE 0x800120f0 0x800121d0) :=
  spec_ofA 18543 5 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem memcpy_qh : Spec 0x800121d0 (qhE 0x800120f8 0x800121f0) :=
  spec_ofA 18548 8 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem memcpy_qj : Spec 0x800121f0 (jmpE 0x8001210c) :=
  spec_ofA 18556 1 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem memcpy_ret : Spec 0x80012180 (retE ) :=
  spec_ofA 18528 2 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem memcpy_dec1 : Spec 0x80012024 (decE 0x80012020 .x15) :=
  spec_ofA 18441 1 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem memcpy_tail1 : Spec 0x8001202c (tailCE 0x80012020 .x15 .x16 .x17) :=
  spec_ofA 18443 3 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem memcpy_dec2 : Spec 0x8001216c (decE 0x80012168 .x12) :=
  spec_ofA 18523 1 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem memcpy_tail2 : Spec 0x80012174 (tailCE 0x80012168 .x12 .x13 .x11) :=
  spec_ofA 18525 3 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem memcpyCode_ok : memcpyCode.Ok where
  size := memcpy_size
  small := memcpy_small
  jmp := memcpy_jmp
  head := memcpy_head
  headPre := memcpy_headPre
  setup := memcpy_setup
  co := memcpy_co
  coPre := memcpy_coPre
  coLoop := memcpy_coLoop
  tail := memcpy_tail
  sh0 := memcpy_sh0
  pt2 := memcpy_pt2
  pt4 := memcpy_pt4
  pw := memcpy_pw
  pe := memcpy_pe
  lpre := memcpy_lpre
  loop := memcpy_loop
  after := memcpy_after
  qt2 := memcpy_qt2
  qt1 := memcpy_qt1
  qb := memcpy_qb
  fin := memcpy_fin
  pb := memcpy_pb
  ph := memcpy_ph
  pj := memcpy_pj
  qw := memcpy_qw
  qh := memcpy_qh
  qj := memcpy_qj
  ret := memcpy_ret
  lbu1 := fetch_of (by decide +kernel)
  dec1 := memcpy_dec1
  sb1 := fetch_of (by decide +kernel)
  tail1 := memcpy_tail1
  lbu2 := fetch_of (by decide +kernel)
  dec2 := memcpy_dec2
  sb2 := fetch_of (by decide +kernel)
  tail2 := memcpy_tail2
  bytesExit := .inl (by decide)
  headLoop := by decide

def memmoveCode : FwdCode where
  size := 0x80012388
  small := 0x800124b8
  jmp := 0x800124c4
  bytes := 0x80012520
  ret := 0x8001260c
  head := 0x80012390
  headPre := 0x800123a0
  headLoop := 0x800123ac
  setup := 0x800123c4
  co := 0x800124f4
  coPre := 0x800124f8
  coLoop := 0x800124fc
  tail := 0x80012510
  sh0 := 0x800123dc
  pt2 := 0x800123fc
  pt4 := 0x80012404
  pw := 0x8001240c
  pe := 0x8001241c
  lpre := 0x80012430
  loop := 0x80012438
  after := 0x80012460
  qt2 := 0x80012474
  qt1 := 0x8001247c
  qb := 0x80012484
  fin := 0x80012498
  pb := 0x80012614
  ph := 0x80012628
  pj := 0x80012644
  qw := 0x80012648
  qh := 0x8001265c
  qj := 0x8001267c

theorem memmove_size : Spec 0x80012388 (sizeE 0x800124b8 0x80012390) :=
  spec_ofA 18658 2 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem memmove_small : Spec 0x800124b8 (smallE 0x80012520 0x800124c4) :=
  spec_ofA 18734 3 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem memmove_jmp : Spec 0x800124c4 (jmpE 0x8001260c) :=
  spec_ofA 18737 1 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem memmove_head : Spec 0x80012390 (headE 0x800123c4 0x800123a0) :=
  spec_ofA 18660 4 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem memmove_headPre : Spec 0x800123a0 (headPreE 0x800123ac) :=
  spec_ofA 18664 3 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem memmove_setup : Spec 0x800123c4 (setupE 0x800124f4 0x800123dc) :=
  spec_ofA 18673 6 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem memmove_co : Spec 0x800124f4 (coE 0x80012510 0x800124f8) :=
  spec_ofA 18749 1 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem memmove_coPre : Spec 0x800124f8 (coPreE 0x800124fc) :=
  spec_ofA 18750 1 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem memmove_coLoop : Spec 0x800124fc (coLoopE 0x800124fc 0x80012510) :=
  spec_ofA 18751 5 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem memmove_tail : Spec 0x80012510 (tailBE 0x8001260c 0x80012520) :=
  spec_ofA 18756 4 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem memmove_sh0 : Spec 0x800123dc (sh0E 0x80012614 0x800123fc) :=
  spec_ofA 18679 8 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem memmove_pt2 : Spec 0x800123fc (pt2E 0x80012628 0x80012404) :=
  spec_ofA 18687 2 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem memmove_pt4 : Spec 0x80012404 (pt4E 0x8001241c 0x8001240c) :=
  spec_ofA 18689 2 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem memmove_pw : Spec 0x8001240c (pwE 0x8001241c) :=
  spec_ofA 18691 4 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem memmove_pe : Spec 0x8001241c (peE 0x80012460 0x80012430) :=
  spec_ofA 18695 5 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem memmove_lpre : Spec 0x80012430 (lpreE 0x80012438) :=
  spec_ofA 18700 2 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem memmove_loop : Spec 0x80012438 (loopE 0x80012438 0x80012460) :=
  spec_ofA 18702 10 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem memmove_after : Spec 0x80012460 (afterE 0x80012648 0x80012474) :=
  spec_ofA 18712 5 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem memmove_qt2 : Spec 0x80012474 (qt2E 0x8001265c 0x8001247c) :=
  spec_ofA 18717 2 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem memmove_qt1 : Spec 0x8001247c (qt1E 0x80012498 0x80012484) :=
  spec_ofA 18719 2 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem memmove_qb : Spec 0x80012484 (qbE 0x80012498) :=
  spec_ofA 18721 5 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem memmove_fin : Spec 0x80012498 (finE 0x80012510) :=
  spec_ofA 18726 8 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem memmove_pb : Spec 0x80012614 (pbE 0x80012404 0x80012628) :=
  spec_ofA 18821 5 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem memmove_ph : Spec 0x80012628 (phE 0x8001240c 0x80012644) :=
  spec_ofA 18826 7 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem memmove_pj : Spec 0x80012644 (jmpE 0x8001241c) :=
  spec_ofA 18833 1 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem memmove_qw : Spec 0x80012648 (qwE 0x8001247c 0x8001265c) :=
  spec_ofA 18834 5 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem memmove_qh : Spec 0x8001265c (qhE 0x80012484 0x8001267c) :=
  spec_ofA 18839 8 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem memmove_qj : Spec 0x8001267c (jmpE 0x80012498) :=
  spec_ofA 18847 1 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem memmove_ret : Spec 0x8001260c (retE ) :=
  spec_ofA 18819 2 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem memmove_dec1 : Spec 0x800123b0 (decE 0x800123ac .x15) :=
  spec_ofA 18668 1 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem memmove_tail1 : Spec 0x800123b8 (tailCE 0x800123ac .x15 .x16 .x17) :=
  spec_ofA 18670 3 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem memmove_dec2 : Spec 0x80012524 (decE 0x80012520 .x12) :=
  spec_ofA 18761 1 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem memmove_tail2 : Spec 0x8001252c (tailCE 0x80012520 .x12 .x13 .x11) :=
  spec_ofA 18763 3 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem memmove_exit : Spec 0x80012538 (jmpE 0x8001260c) :=
  spec_ofA 18766 1 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem memmoveCode_ok : memmoveCode.Ok where
  size := memmove_size
  small := memmove_small
  jmp := memmove_jmp
  head := memmove_head
  headPre := memmove_headPre
  setup := memmove_setup
  co := memmove_co
  coPre := memmove_coPre
  coLoop := memmove_coLoop
  tail := memmove_tail
  sh0 := memmove_sh0
  pt2 := memmove_pt2
  pt4 := memmove_pt4
  pw := memmove_pw
  pe := memmove_pe
  lpre := memmove_lpre
  loop := memmove_loop
  after := memmove_after
  qt2 := memmove_qt2
  qt1 := memmove_qt1
  qb := memmove_qb
  fin := memmove_fin
  pb := memmove_pb
  ph := memmove_ph
  pj := memmove_pj
  qw := memmove_qw
  qh := memmove_qh
  qj := memmove_qj
  ret := memmove_ret
  lbu1 := fetch_of (by decide +kernel)
  dec1 := memmove_dec1
  sb1 := fetch_of (by decide +kernel)
  tail1 := memmove_tail1
  lbu2 := fetch_of (by decide +kernel)
  dec2 := memmove_dec2
  sb2 := fetch_of (by decide +kernel)
  tail2 := memmove_tail2
  bytesExit := .inr memmove_exit
  headLoop := by decide

theorem memcpy_sp : Spec 0x80011ff8 (spE 0x80011ffc) :=
  spec_ofA 18430 1 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

end Rv64Verifier.Runtime.Forward
