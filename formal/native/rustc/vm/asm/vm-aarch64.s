	.file	"native_vm.a73d193de09a3cff-cgu.0"
	.section	.text._RINvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB6_6TState8sumcheckNCNvB2_14sumcheck_plain0EB8_,"ax",@progbits
	.p2align	2
	.type	_RINvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB6_6TState8sumcheckNCNvB2_14sumcheck_plain0EB8_,@function
_RINvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB6_6TState8sumcheckNCNvB2_14sumcheck_plain0EB8_:
.Lfunc_begin0:
	.cfi_startproc
	sub	sp, sp, #160
	.cfi_def_cfa_offset 160
	stp	x30, x23, [sp, #112]
	stp	x22, x21, [sp, #128]
	stp	x20, x19, [sp, #144]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w30, -48
	.cfi_remember_state
	mov	x19, x0
	stp	xzr, xzr, [sp, #8]
	stp	xzr, xzr, [sp, #24]
	stp	xzr, xzr, [sp, #40]
	stp	xzr, xzr, [sp, #56]
	stp	xzr, xzr, [sp, #72]
	cbz	x6, .LBB0_4
	add	x23, x5, x6, lsl #4
	mov	x20, x5
	mov	x21, x4
	mov	x22, x1
.LBB0_2:
	add	x4, sp, #88
	add	x5, sp, #8
	mov	x0, x22
	mov	x1, x21
	str	xzr, [sp, #88]
	bl	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState19sumcheck_round_poly
	tbz	w0, #0, .LBB0_5
	mov	x0, x22
	bl	_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW7squeeze
	mov	x2, x0
	mov	x3, x1
	stp	x0, x1, [x20], #16
	add	x0, sp, #8
	mov	x1, x21
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field9poly_eval
	mov	x2, x0
	cmp	x20, x23
	mov	x3, x1
	b.ne	.LBB0_2
.LBB0_4:
	mov	w8, #1
	stp	x2, x3, [x19, #8]
	str	x8, [x19]
	ldp	x20, x19, [sp, #144]
	ldp	x22, x21, [sp, #128]
	ldp	x30, x23, [sp, #112]
	add	sp, sp, #160
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w30
	ret
.LBB0_5:
	.cfi_restore_state
	str	xzr, [x19]
	ldp	x20, x19, [sp, #144]
	ldp	x22, x21, [sp, #128]
	ldp	x30, x23, [sp, #112]
	add	sp, sp, #160
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w30
	ret
.Lfunc_end0:
	.size	_RINvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB6_6TState8sumcheckNCNvB2_14sumcheck_plain0EB8_, .Lfunc_end0-_RINvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB6_6TState8sumcheckNCNvB2_14sumcheck_plain0EB8_
	.cfi_endproc

	.section	.text._RINvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB6_6TState8sumcheckNCNvNtB8_10keccak_gkr12verify_layers1_0EB8_,"ax",@progbits
	.p2align	2
	.type	_RINvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB6_6TState8sumcheckNCNvNtB8_10keccak_gkr12verify_layers1_0EB8_,@function
_RINvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB6_6TState8sumcheckNCNvNtB8_10keccak_gkr12verify_layers1_0EB8_:
.Lfunc_begin1:
	.cfi_startproc
	sub	sp, sp, #176
	.cfi_def_cfa_offset 176
	stp	x30, x25, [sp, #112]
	stp	x24, x23, [sp, #128]
	stp	x22, x21, [sp, #144]
	stp	x20, x19, [sp, #160]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w24, -48
	.cfi_offset w25, -56
	.cfi_offset w30, -64
	mov	x19, x0
	stp	xzr, xzr, [sp, #8]
	stp	xzr, xzr, [sp, #24]
	stp	xzr, xzr, [sp, #40]
	stp	xzr, xzr, [sp, #56]
	stp	xzr, xzr, [sp, #72]
	cbz	x7, .LBB1_7
	add	x24, x6, x7, lsl #4
	mov	x20, x6
	mov	x21, x5
	mov	x22, x1
	mov	x23, xzr
	add	x25, x4, #8
.LBB1_2:
	cmp	x23, x21
	b.hs	.LBB1_4
	ldp	x8, x9, [x25, #-8]
	stp	x8, x9, [sp, #96]
	mov	w8, #1
	b	.LBB1_5
.LBB1_4:
	mov	x8, xzr
.LBB1_5:
	add	x4, sp, #88
	add	x5, sp, #8
	mov	x0, x22
	mov	w1, #3
	str	x8, [sp, #88]
	bl	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState19sumcheck_round_poly
	tbz	w0, #0, .LBB1_8
	mov	x0, x22
	bl	_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW7squeeze
	mov	x2, x0
	mov	x3, x1
	stp	x0, x1, [x20], #16
	add	x0, sp, #8
	mov	w1, #3
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field9poly_eval
	mov	x2, x0
	mov	x3, x1
	cmp	x20, x24
	add	x25, x25, #16
	add	x23, x23, #1
	b.ne	.LBB1_2
.LBB1_7:
	mov	w8, #1
	stp	x2, x3, [x19, #8]
	b	.LBB1_9
.LBB1_8:
	mov	x8, xzr
.LBB1_9:
	str	x8, [x19]
	ldp	x20, x19, [sp, #160]
	ldp	x22, x21, [sp, #144]
	ldp	x24, x23, [sp, #128]
	ldp	x30, x25, [sp, #112]
	add	sp, sp, #176
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w25
	.cfi_restore w30
	ret
.Lfunc_end1:
	.size	_RINvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB6_6TState8sumcheckNCNvNtB8_10keccak_gkr12verify_layers1_0EB8_, .Lfunc_end1-_RINvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB6_6TState8sumcheckNCNvNtB8_10keccak_gkr12verify_layers1_0EB8_
	.cfi_endproc

	.section	.text._RINvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB6_6TState8sumcheckNCNvNtB8_3gkr8gkr_step0EB8_,"ax",@progbits
	.p2align	2
	.type	_RINvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB6_6TState8sumcheckNCNvNtB8_3gkr8gkr_step0EB8_,@function
_RINvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB6_6TState8sumcheckNCNvNtB8_3gkr8gkr_step0EB8_:
.Lfunc_begin2:
	.cfi_startproc
	sub	sp, sp, #192
	.cfi_def_cfa_offset 192
	str	x30, [sp, #112]
	stp	x26, x25, [sp, #128]
	stp	x24, x23, [sp, #144]
	stp	x22, x21, [sp, #160]
	stp	x20, x19, [sp, #176]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w24, -48
	.cfi_offset w25, -56
	.cfi_offset w26, -64
	.cfi_offset w30, -80
	ldr	x8, [sp, #192]
	mov	x19, x0
	stp	xzr, xzr, [sp, #8]
	stp	xzr, xzr, [sp, #24]
	stp	xzr, xzr, [sp, #40]
	stp	xzr, xzr, [sp, #56]
	stp	xzr, xzr, [sp, #72]
	cbz	x8, .LBB2_7
	add	x25, x7, x8, lsl #4
	mov	x20, x7
	mov	x21, x6
	mov	x22, x4
	mov	x23, x1
	mov	x24, xzr
	add	x26, x5, #8
.LBB2_2:
	cmp	x24, x21
	b.hs	.LBB2_4
	ldp	x8, x9, [x26, #-8]
	stp	x8, x9, [sp, #96]
	mov	w8, #1
	b	.LBB2_5
.LBB2_4:
	mov	x8, xzr
.LBB2_5:
	add	x4, sp, #88
	add	x5, sp, #8
	mov	x0, x23
	mov	x1, x22
	str	x8, [sp, #88]
	bl	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState19sumcheck_round_poly
	tbz	w0, #0, .LBB2_8
	mov	x0, x23
	bl	_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW7squeeze
	mov	x2, x0
	mov	x3, x1
	stp	x0, x1, [x20], #16
	add	x0, sp, #8
	mov	x1, x22
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field9poly_eval
	mov	x2, x0
	mov	x3, x1
	cmp	x20, x25
	add	x26, x26, #16
	add	x24, x24, #1
	b.ne	.LBB2_2
.LBB2_7:
	mov	w8, #1
	stp	x2, x3, [x19, #8]
	b	.LBB2_9
.LBB2_8:
	mov	x8, xzr
.LBB2_9:
	str	x8, [x19]
	ldp	x20, x19, [sp, #176]
	ldp	x22, x21, [sp, #160]
	ldr	x30, [sp, #112]
	ldp	x24, x23, [sp, #144]
	ldp	x26, x25, [sp, #128]
	add	sp, sp, #192
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w25
	.cfi_restore w26
	.cfi_restore w30
	ret
.Lfunc_end2:
	.size	_RINvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB6_6TState8sumcheckNCNvNtB8_3gkr8gkr_step0EB8_, .Lfunc_end2-_RINvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB6_6TState8sumcheckNCNvNtB8_3gkr8gkr_step0EB8_
	.cfi_endproc

	.section	.text._RINvNtCsemcRClSg8DH_9native_vm4whir8each_rowNCNvB2_10next_level0EB4_,"ax",@progbits
	.p2align	2
	.type	_RINvNtCsemcRClSg8DH_9native_vm4whir8each_rowNCNvB2_10next_level0EB4_,@function
_RINvNtCsemcRClSg8DH_9native_vm4whir8each_rowNCNvB2_10next_level0EB4_:
.Lfunc_begin3:
	.cfi_startproc
	stp	x29, x30, [sp, #-96]!
	.cfi_def_cfa_offset 96
	stp	x28, x27, [sp, #16]
	stp	x26, x25, [sp, #32]
	stp	x24, x23, [sp, #48]
	stp	x22, x21, [sp, #64]
	stp	x20, x19, [sp, #80]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w24, -48
	.cfi_offset w25, -56
	.cfi_offset w26, -64
	.cfi_offset w27, -72
	.cfi_offset w28, -80
	.cfi_offset w30, -88
	.cfi_offset w29, -96
	sub	sp, sp, #1904
	.cfi_def_cfa_offset 2000
	ldr	xzr, [sp]
	stp	x0, x1, [sp, #80]
	add	x0, sp, #600
	mov	x1, x4
	mov	x25, x7
	stp	x5, x6, [sp, #64]
	mov	x21, x3
	mov	x28, x2
	add	x19, sp, #600
	bl	_RNvNtCsemcRClSg8DH_9native_vm4whir14subspace_table
	ldr	x8, [sp, #600]
	cbz	x8, .LBB3_12
	add	x8, sp, #96
	ldr	x23, [sp, #608]
	add	x1, x19, #16
	add	x26, x8, #8
	mov	w2, #496
	mov	x0, x26
	bl	memcpy
	ldr	x19, [x21, #16]
	str	x23, [sp, #96]
	cbz	x19, .LBB3_13
	cmp	x23, #32
	mov	w9, #8
	add	x8, sp, #1624
	csel	x10, x26, x9, lo
	ldp	x11, x9, [x25]
	lsl	x22, x28, #3
	mov	x24, xzr
	add	x8, x8, #8
	stp	x11, x10, [sp, #48]
	ldp	x11, x20, [x25, #16]
	str	x9, [sp, #40]
	ldp	x9, x10, [x25, #32]
	stp	x10, x8, [sp, #8]
	csel	x10, x23, xzr, lo
	add	x23, x9, #8
	stp	x10, x11, [sp, #24]
	b	.LBB3_5
.LBB3_3:
	ldp	x8, x1, [x23, #-8]
.LBB3_4:
	ldp	x27, x28, [x20]
	eor	x2, x26, x29
	eor	x3, x0, x25
	mov	x0, x8
	add	x24, x24, #1
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	cmp	x19, x24
	eor	x8, x0, x27
	eor	x9, x1, x28
	sub	x22, x22, #8
	add	x23, x23, #16
	stp	x8, x9, [x20]
	b.eq	.LBB3_13
.LBB3_5:
	cbz	x22, .LBB3_13
	ldr	x8, [sp, #88]
	mov	x0, x21
	mov	x1, x24
	str	xzr, [sp, #600]
	ldr	x26, [x8, x24, lsl #3]
	str	xzr, [sp, #608]
	str	xzr, [sp, #616]
	str	xzr, [sp, #624]
	str	xzr, [sp, #632]
	str	xzr, [sp, #640]
	str	xzr, [sp, #648]
	str	xzr, [sp, #656]
	str	xzr, [sp, #664]
	str	xzr, [sp, #672]
	str	xzr, [sp, #680]
	str	xzr, [sp, #688]
	str	xzr, [sp, #696]
	str	xzr, [sp, #704]
	str	xzr, [sp, #712]
	str	xzr, [sp, #720]
	str	xzr, [sp, #728]
	str	xzr, [sp, #736]
	str	xzr, [sp, #744]
	str	xzr, [sp, #752]
	str	xzr, [sp, #760]
	str	xzr, [sp, #768]
	str	xzr, [sp, #776]
	str	xzr, [sp, #784]
	str	xzr, [sp, #792]
	str	xzr, [sp, #800]
	str	xzr, [sp, #808]
	str	xzr, [sp, #816]
	str	xzr, [sp, #824]
	str	xzr, [sp, #832]
	str	xzr, [sp, #840]
	str	xzr, [sp, #848]
	str	xzr, [sp, #856]
	str	xzr, [sp, #864]
	str	xzr, [sp, #872]
	str	xzr, [sp, #880]
	str	xzr, [sp, #888]
	str	xzr, [sp, #896]
	str	xzr, [sp, #904]
	str	xzr, [sp, #912]
	str	xzr, [sp, #920]
	str	xzr, [sp, #928]
	str	xzr, [sp, #936]
	str	xzr, [sp, #944]
	str	xzr, [sp, #952]
	str	xzr, [sp, #960]
	str	xzr, [sp, #968]
	str	xzr, [sp, #976]
	str	xzr, [sp, #984]
	str	xzr, [sp, #992]
	str	xzr, [sp, #1000]
	str	xzr, [sp, #1008]
	str	xzr, [sp, #1016]
	str	xzr, [sp, #1024]
	str	xzr, [sp, #1032]
	str	xzr, [sp, #1040]
	str	xzr, [sp, #1048]
	str	xzr, [sp, #1056]
	str	xzr, [sp, #1064]
	str	xzr, [sp, #1072]
	str	xzr, [sp, #1080]
	str	xzr, [sp, #1088]
	str	xzr, [sp, #1096]
	str	xzr, [sp, #1104]
	str	xzr, [sp, #1112]
	str	xzr, [sp, #1120]
	str	xzr, [sp, #1128]
	str	xzr, [sp, #1136]
	str	xzr, [sp, #1144]
	str	xzr, [sp, #1152]
	str	xzr, [sp, #1160]
	str	xzr, [sp, #1168]
	str	xzr, [sp, #1176]
	str	xzr, [sp, #1184]
	str	xzr, [sp, #1192]
	str	xzr, [sp, #1200]
	str	xzr, [sp, #1208]
	str	xzr, [sp, #1216]
	str	xzr, [sp, #1224]
	str	xzr, [sp, #1232]
	str	xzr, [sp, #1240]
	str	xzr, [sp, #1248]
	str	xzr, [sp, #1256]
	str	xzr, [sp, #1264]
	str	xzr, [sp, #1272]
	str	xzr, [sp, #1280]
	str	xzr, [sp, #1288]
	str	xzr, [sp, #1296]
	str	xzr, [sp, #1304]
	str	xzr, [sp, #1312]
	str	xzr, [sp, #1320]
	str	xzr, [sp, #1328]
	str	xzr, [sp, #1336]
	str	xzr, [sp, #1344]
	str	xzr, [sp, #1352]
	str	xzr, [sp, #1360]
	str	xzr, [sp, #1368]
	str	xzr, [sp, #1376]
	str	xzr, [sp, #1384]
	str	xzr, [sp, #1392]
	str	xzr, [sp, #1400]
	str	xzr, [sp, #1408]
	str	xzr, [sp, #1416]
	str	xzr, [sp, #1424]
	str	xzr, [sp, #1432]
	str	xzr, [sp, #1440]
	str	xzr, [sp, #1448]
	str	xzr, [sp, #1456]
	str	xzr, [sp, #1464]
	str	xzr, [sp, #1472]
	str	xzr, [sp, #1480]
	str	xzr, [sp, #1488]
	str	xzr, [sp, #1496]
	str	xzr, [sp, #1504]
	str	xzr, [sp, #1512]
	str	xzr, [sp, #1520]
	str	xzr, [sp, #1528]
	str	xzr, [sp, #1536]
	str	xzr, [sp, #1544]
	str	xzr, [sp, #1552]
	str	xzr, [sp, #1560]
	str	xzr, [sp, #1568]
	str	xzr, [sp, #1576]
	str	xzr, [sp, #1584]
	str	xzr, [sp, #1592]
	str	xzr, [sp, #1600]
	str	xzr, [sp, #1608]
	str	xzr, [sp, #1616]
	bl	_RNvMs_NtCsemcRClSg8DH_9native_vm10transcriptNtB4_4Rows3row
	mov	x2, x0
	mov	x4, x1
	ldr	x0, [sp, #80]
	add	x3, sp, #600
	mov	x1, x2
	mov	x2, x4
	bl	_RNvNtCsemcRClSg8DH_9native_vm4whir8lanes_of
	cmp	x0, #1
	b.ne	.LBB3_12
	ldp	x3, x4, [sp, #64]
	add	x0, sp, #600
	mov	x2, x26
	bl	_RNvNtCsemcRClSg8DH_9native_vm4whir8fold_row
	mov	x25, x1
	ldr	x1, [sp, #56]
	ldr	x2, [sp, #24]
	mov	x29, x0
	add	x0, sp, #1624
	mov	x3, x26
	bl	_RNvNtCsemcRClSg8DH_9native_vm4whir17subspace_at_table
	ldr	x9, [sp, #1624]
	ldr	x8, [sp, #48]
	mov	x27, xzr
	ldr	x10, [sp, #16]
	cmp	x9, #32
	ldr	x8, [x8]
	csel	x4, x9, xzr, lo
	mov	w9, #8
	csel	x3, x10, x9, lo
	cmp	x8, x4
	b.hs	.LBB3_9
	ldr	x27, [x3, x8, lsl #3]
.LBB3_9:
	ldp	x2, x1, [sp, #32]
	add	x0, sp, #1880
	bl	_RNvNtCsemcRClSg8DH_9native_vm4whir10novel_eval
	ldr	x8, [sp, #1880]
	cbz	x8, .LBB3_12
	ldr	x1, [sp, #1888]
	ldr	x28, [sp, #1896]
	mov	x0, x27
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field4kmul
	mov	x26, x0
	mov	x0, x27
	mov	x1, x28
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field4kmul
	ldr	x8, [sp, #8]
	cmp	x24, x8
	b.lo	.LBB3_3
	mov	x8, xzr
	mov	x1, xzr
	b	.LBB3_4
.LBB3_12:
	mov	w0, wzr
	b	.LBB3_14
.LBB3_13:
	mov	w0, #1
.LBB3_14:
	add	sp, sp, #1904
	.cfi_def_cfa_offset 96
	ldp	x20, x19, [sp, #80]
	ldp	x22, x21, [sp, #64]
	ldp	x24, x23, [sp, #48]
	ldp	x26, x25, [sp, #32]
	ldp	x28, x27, [sp, #16]
	ldp	x29, x30, [sp], #96
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w25
	.cfi_restore w26
	.cfi_restore w27
	.cfi_restore w28
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end3:
	.size	_RINvNtCsemcRClSg8DH_9native_vm4whir8each_rowNCNvB2_10next_level0EB4_, .Lfunc_end3-_RINvNtCsemcRClSg8DH_9native_vm4whir8each_rowNCNvB2_10next_level0EB4_
	.cfi_endproc

	.section	.text._RINvNtCsemcRClSg8DH_9native_vm4whir8each_rowNCNvB2_11final_level0EB4_,"ax",@progbits
	.p2align	2
	.type	_RINvNtCsemcRClSg8DH_9native_vm4whir8each_rowNCNvB2_11final_level0EB4_,@function
_RINvNtCsemcRClSg8DH_9native_vm4whir8each_rowNCNvB2_11final_level0EB4_:
.Lfunc_begin4:
	.cfi_startproc
	stp	x29, x30, [sp, #-96]!
	.cfi_def_cfa_offset 96
	stp	x28, x27, [sp, #16]
	stp	x26, x25, [sp, #32]
	stp	x24, x23, [sp, #48]
	stp	x22, x21, [sp, #64]
	stp	x20, x19, [sp, #80]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w24, -48
	.cfi_offset w25, -56
	.cfi_offset w26, -64
	.cfi_offset w27, -72
	.cfi_offset w28, -80
	.cfi_offset w30, -88
	.cfi_offset w29, -96
	sub	sp, sp, #1856
	.cfi_def_cfa_offset 1952
	ldr	xzr, [sp]
	mov	x23, x1
	mov	x24, x0
	add	x0, sp, #552
	mov	x1, x4
	str	x7, [sp, #40]
	mov	x20, x6
	mov	x21, x5
	mov	x22, x3
	mov	x27, x2
	add	x19, sp, #552
	bl	_RNvNtCsemcRClSg8DH_9native_vm4whir14subspace_table
	ldr	x8, [sp, #552]
	cbz	x8, .LBB4_10
	add	x8, sp, #48
	ldr	x29, [sp, #560]
	add	x1, x19, #16
	add	x26, x8, #8
	mov	w2, #496
	mov	x0, x26
	bl	memcpy
	ldr	x28, [x22, #16]
	str	x29, [sp, #48]
	cbz	x28, .LBB4_9
	ldr	x10, [sp, #1952]
	cmp	x29, #32
	mov	w9, #8
	add	x8, sp, #1576
	lsl	x19, x27, #3
	csel	x9, x26, x9, lo
	mov	x25, xzr
	stp	x9, x10, [sp, #24]
	csel	x9, x29, xzr, lo
	add	x8, x8, #8
	stp	x8, x9, [sp, #8]
.LBB4_3:
	cbz	x19, .LBB4_9
	ldr	x29, [x23, x25, lsl #3]
	mov	x0, x22
	mov	x1, x25
	str	xzr, [sp, #552]
	str	xzr, [sp, #560]
	str	xzr, [sp, #568]
	str	xzr, [sp, #576]
	str	xzr, [sp, #584]
	str	xzr, [sp, #592]
	str	xzr, [sp, #600]
	str	xzr, [sp, #608]
	str	xzr, [sp, #616]
	str	xzr, [sp, #624]
	str	xzr, [sp, #632]
	str	xzr, [sp, #640]
	str	xzr, [sp, #648]
	str	xzr, [sp, #656]
	str	xzr, [sp, #664]
	str	xzr, [sp, #672]
	str	xzr, [sp, #680]
	str	xzr, [sp, #688]
	str	xzr, [sp, #696]
	str	xzr, [sp, #704]
	str	xzr, [sp, #712]
	str	xzr, [sp, #720]
	str	xzr, [sp, #728]
	str	xzr, [sp, #736]
	str	xzr, [sp, #744]
	str	xzr, [sp, #752]
	str	xzr, [sp, #760]
	str	xzr, [sp, #768]
	str	xzr, [sp, #776]
	str	xzr, [sp, #784]
	str	xzr, [sp, #792]
	str	xzr, [sp, #800]
	str	xzr, [sp, #808]
	str	xzr, [sp, #816]
	str	xzr, [sp, #824]
	str	xzr, [sp, #832]
	str	xzr, [sp, #840]
	str	xzr, [sp, #848]
	str	xzr, [sp, #856]
	str	xzr, [sp, #864]
	str	xzr, [sp, #872]
	str	xzr, [sp, #880]
	str	xzr, [sp, #888]
	str	xzr, [sp, #896]
	str	xzr, [sp, #904]
	str	xzr, [sp, #912]
	str	xzr, [sp, #920]
	str	xzr, [sp, #928]
	str	xzr, [sp, #936]
	str	xzr, [sp, #944]
	str	xzr, [sp, #952]
	str	xzr, [sp, #960]
	str	xzr, [sp, #968]
	str	xzr, [sp, #976]
	str	xzr, [sp, #984]
	str	xzr, [sp, #992]
	str	xzr, [sp, #1000]
	str	xzr, [sp, #1008]
	str	xzr, [sp, #1016]
	str	xzr, [sp, #1024]
	str	xzr, [sp, #1032]
	str	xzr, [sp, #1040]
	str	xzr, [sp, #1048]
	str	xzr, [sp, #1056]
	str	xzr, [sp, #1064]
	str	xzr, [sp, #1072]
	str	xzr, [sp, #1080]
	str	xzr, [sp, #1088]
	str	xzr, [sp, #1096]
	str	xzr, [sp, #1104]
	str	xzr, [sp, #1112]
	str	xzr, [sp, #1120]
	str	xzr, [sp, #1128]
	str	xzr, [sp, #1136]
	str	xzr, [sp, #1144]
	str	xzr, [sp, #1152]
	str	xzr, [sp, #1160]
	str	xzr, [sp, #1168]
	str	xzr, [sp, #1176]
	str	xzr, [sp, #1184]
	str	xzr, [sp, #1192]
	str	xzr, [sp, #1200]
	str	xzr, [sp, #1208]
	str	xzr, [sp, #1216]
	str	xzr, [sp, #1224]
	str	xzr, [sp, #1232]
	str	xzr, [sp, #1240]
	str	xzr, [sp, #1248]
	str	xzr, [sp, #1256]
	str	xzr, [sp, #1264]
	str	xzr, [sp, #1272]
	str	xzr, [sp, #1280]
	str	xzr, [sp, #1288]
	str	xzr, [sp, #1296]
	str	xzr, [sp, #1304]
	str	xzr, [sp, #1312]
	str	xzr, [sp, #1320]
	str	xzr, [sp, #1328]
	str	xzr, [sp, #1336]
	str	xzr, [sp, #1344]
	str	xzr, [sp, #1352]
	str	xzr, [sp, #1360]
	str	xzr, [sp, #1368]
	str	xzr, [sp, #1376]
	str	xzr, [sp, #1384]
	str	xzr, [sp, #1392]
	str	xzr, [sp, #1400]
	str	xzr, [sp, #1408]
	str	xzr, [sp, #1416]
	str	xzr, [sp, #1424]
	str	xzr, [sp, #1432]
	str	xzr, [sp, #1440]
	str	xzr, [sp, #1448]
	str	xzr, [sp, #1456]
	str	xzr, [sp, #1464]
	str	xzr, [sp, #1472]
	str	xzr, [sp, #1480]
	str	xzr, [sp, #1488]
	str	xzr, [sp, #1496]
	str	xzr, [sp, #1504]
	str	xzr, [sp, #1512]
	str	xzr, [sp, #1520]
	str	xzr, [sp, #1528]
	str	xzr, [sp, #1536]
	str	xzr, [sp, #1544]
	str	xzr, [sp, #1552]
	str	xzr, [sp, #1560]
	str	xzr, [sp, #1568]
	bl	_RNvMs_NtCsemcRClSg8DH_9native_vm10transcriptNtB4_4Rows3row
	mov	x2, x0
	mov	x4, x1
	add	x3, sp, #552
	mov	x0, x24
	mov	x1, x2
	mov	x2, x4
	bl	_RNvNtCsemcRClSg8DH_9native_vm4whir8lanes_of
	cmp	x0, #1
	b.ne	.LBB4_10
	add	x0, sp, #552
	mov	x2, x29
	mov	x3, x21
	mov	x4, x20
	bl	_RNvNtCsemcRClSg8DH_9native_vm4whir8fold_row
	mov	x26, x1
	ldp	x2, x1, [sp, #16]
	mov	x27, x0
	add	x0, sp, #1576
	mov	x3, x29
	bl	_RNvNtCsemcRClSg8DH_9native_vm4whir17subspace_at_table
	ldr	x8, [sp, #1576]
	ldr	x10, [sp, #8]
	mov	w9, #8
	ldp	x2, x1, [sp, #32]
	add	x0, sp, #1832
	cmp	x8, #32
	csel	x3, x10, x9, lo
	csel	x4, x8, xzr, lo
	bl	_RNvNtCsemcRClSg8DH_9native_vm4whir10novel_eval
	ldr	w8, [sp, #1832]
	tbz	w8, #0, .LBB4_10
	ldr	x8, [sp, #1840]
	cmp	x27, x8
	b.ne	.LBB4_10
	ldr	x8, [sp, #1848]
	cmp	x26, x8
	b.ne	.LBB4_10
	add	x25, x25, #1
	sub	x19, x19, #8
	cmp	x28, x25
	b.ne	.LBB4_3
.LBB4_9:
	mov	w0, #1
	b	.LBB4_11
.LBB4_10:
	mov	w0, wzr
.LBB4_11:
	add	sp, sp, #1856
	.cfi_def_cfa_offset 96
	ldp	x20, x19, [sp, #80]
	ldp	x22, x21, [sp, #64]
	ldp	x24, x23, [sp, #48]
	ldp	x26, x25, [sp, #32]
	ldp	x28, x27, [sp, #16]
	ldp	x29, x30, [sp], #96
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w25
	.cfi_restore w26
	.cfi_restore w27
	.cfi_restore w28
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end4:
	.size	_RINvNtCsemcRClSg8DH_9native_vm4whir8each_rowNCNvB2_11final_level0EB4_, .Lfunc_end4-_RINvNtCsemcRClSg8DH_9native_vm4whir8each_rowNCNvB2_11final_level0EB4_
	.cfi_endproc

	.section	.text._RINvNtCsemcRClSg8DH_9native_vm5field10eq_eval_fnNCNvNtB4_6layout8eq_above0EB4_,"ax",@progbits
	.p2align	2
	.type	_RINvNtCsemcRClSg8DH_9native_vm5field10eq_eval_fnNCNvNtB4_6layout8eq_above0EB4_,@function
_RINvNtCsemcRClSg8DH_9native_vm5field10eq_eval_fnNCNvNtB4_6layout8eq_above0EB4_:
.Lfunc_begin5:
	.cfi_startproc
	str	x30, [sp, #-48]!
	.cfi_def_cfa_offset 48
	stp	x22, x21, [sp, #16]
	stp	x20, x19, [sp, #32]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w30, -48
	.cfi_remember_state
	cmp	x3, x0
	csel	x20, x3, x0, lo
	cbz	x20, .LBB5_4
	mov	x19, x1
	mov	x1, xzr
	mov	x22, xzr
	add	x21, x2, #8
	mov	w0, #1
.LBB5_2:
	lsr	x8, x19, x22
	ldp	x9, x3, [x21, #-8]
	add	x22, x22, #1
	and	x8, x8, #0x1
	eor	x8, x9, x8
	eor	x2, x8, #0x1
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	cmp	x20, x22
	add	x21, x21, #16
	b.ne	.LBB5_2
	ldp	x20, x19, [sp, #32]
	ldp	x22, x21, [sp, #16]
	ldr	x30, [sp], #48
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w30
	ret
.LBB5_4:
	.cfi_restore_state
	mov	x1, xzr
	mov	w0, #1
	ldp	x20, x19, [sp, #32]
	ldp	x22, x21, [sp, #16]
	ldr	x30, [sp], #48
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w30
	ret
.Lfunc_end5:
	.size	_RINvNtCsemcRClSg8DH_9native_vm5field10eq_eval_fnNCNvNtB4_6layout8eq_above0EB4_, .Lfunc_end5-_RINvNtCsemcRClSg8DH_9native_vm5field10eq_eval_fnNCNvNtB4_6layout8eq_above0EB4_
	.cfi_endproc

	.section	.text._RINvNtCsemcRClSg8DH_9native_vm5field19multilinear_eval_byNCNvB2_16multilinear_eval0EB4_,"ax",@progbits
	.p2align	2
	.type	_RINvNtCsemcRClSg8DH_9native_vm5field19multilinear_eval_byNCNvB2_16multilinear_eval0EB4_,@function
_RINvNtCsemcRClSg8DH_9native_vm5field19multilinear_eval_byNCNvB2_16multilinear_eval0EB4_:
.Lfunc_begin6:
	.cfi_startproc
	stp	x29, x30, [sp, #-96]!
	.cfi_def_cfa_offset 96
	stp	x28, x27, [sp, #16]
	stp	x26, x25, [sp, #32]
	stp	x24, x23, [sp, #48]
	stp	x22, x21, [sp, #64]
	stp	x20, x19, [sp, #80]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w24, -48
	.cfi_offset w25, -56
	.cfi_offset w26, -64
	.cfi_offset w27, -72
	.cfi_offset w28, -80
	.cfi_offset w30, -88
	.cfi_offset w29, -96
	sub	sp, sp, #1136
	.cfi_def_cfa_offset 1232
	ldr	xzr, [sp]
	stp	xzr, xzr, [sp, #48]
	stp	xzr, xzr, [sp, #64]
	stp	xzr, xzr, [sp, #80]
	stp	xzr, xzr, [sp, #96]
	stp	xzr, xzr, [sp, #112]
	stp	xzr, xzr, [sp, #128]
	stp	xzr, xzr, [sp, #144]
	stp	xzr, xzr, [sp, #160]
	stp	xzr, xzr, [sp, #176]
	stp	xzr, xzr, [sp, #192]
	stp	xzr, xzr, [sp, #208]
	stp	xzr, xzr, [sp, #224]
	stp	xzr, xzr, [sp, #240]
	stp	xzr, xzr, [sp, #256]
	stp	xzr, xzr, [sp, #272]
	stp	xzr, xzr, [sp, #288]
	stp	xzr, xzr, [sp, #304]
	stp	xzr, xzr, [sp, #320]
	stp	xzr, xzr, [sp, #336]
	stp	xzr, xzr, [sp, #352]
	stp	xzr, xzr, [sp, #368]
	stp	xzr, xzr, [sp, #384]
	stp	xzr, xzr, [sp, #400]
	stp	xzr, xzr, [sp, #416]
	stp	xzr, xzr, [sp, #432]
	stp	xzr, xzr, [sp, #448]
	stp	xzr, xzr, [sp, #464]
	stp	xzr, xzr, [sp, #480]
	stp	xzr, xzr, [sp, #496]
	str	xzr, [sp, #512]
	str	xzr, [sp, #520]
	str	xzr, [sp, #528]
	str	xzr, [sp, #536]
	str	xzr, [sp, #544]
	str	xzr, [sp, #552]
	str	xzr, [sp, #560]
	str	xzr, [sp, #568]
	str	xzr, [sp, #576]
	str	xzr, [sp, #584]
	str	xzr, [sp, #592]
	str	xzr, [sp, #600]
	str	xzr, [sp, #608]
	str	xzr, [sp, #616]
	str	xzr, [sp, #624]
	str	xzr, [sp, #632]
	str	xzr, [sp, #640]
	str	xzr, [sp, #648]
	str	xzr, [sp, #656]
	str	xzr, [sp, #664]
	str	xzr, [sp, #672]
	str	xzr, [sp, #680]
	str	xzr, [sp, #688]
	str	xzr, [sp, #696]
	str	xzr, [sp, #704]
	str	xzr, [sp, #712]
	str	xzr, [sp, #720]
	str	xzr, [sp, #728]
	str	xzr, [sp, #736]
	str	xzr, [sp, #744]
	str	xzr, [sp, #752]
	str	xzr, [sp, #760]
	str	xzr, [sp, #768]
	str	xzr, [sp, #776]
	str	xzr, [sp, #784]
	str	xzr, [sp, #792]
	str	xzr, [sp, #800]
	str	xzr, [sp, #808]
	str	xzr, [sp, #816]
	str	xzr, [sp, #824]
	str	xzr, [sp, #832]
	str	xzr, [sp, #840]
	str	xzr, [sp, #848]
	str	xzr, [sp, #856]
	str	xzr, [sp, #864]
	str	xzr, [sp, #872]
	str	xzr, [sp, #880]
	str	xzr, [sp, #888]
	str	xzr, [sp, #896]
	str	xzr, [sp, #904]
	str	xzr, [sp, #912]
	str	xzr, [sp, #920]
	str	xzr, [sp, #928]
	str	xzr, [sp, #936]
	str	xzr, [sp, #944]
	str	xzr, [sp, #952]
	str	xzr, [sp, #960]
	str	xzr, [sp, #968]
	str	xzr, [sp, #976]
	str	xzr, [sp, #984]
	str	xzr, [sp, #992]
	str	xzr, [sp, #1000]
	str	xzr, [sp, #1008]
	str	xzr, [sp, #1016]
	str	xzr, [sp, #1024]
	str	xzr, [sp, #1032]
	str	xzr, [sp, #1040]
	str	xzr, [sp, #1048]
	str	xzr, [sp, #1056]
	str	xzr, [sp, #1064]
	str	xzr, [sp, #1128]
	str	xzr, [sp, #1120]
	str	xzr, [sp, #1112]
	str	xzr, [sp, #1104]
	str	xzr, [sp, #1096]
	str	xzr, [sp, #1088]
	str	xzr, [sp, #1080]
	str	xzr, [sp, #1072]
	cbz	x0, .LBB6_12
	cbz	x4, .LBB6_10
	mov	x29, xzr
	add	x8, x3, #8
	stp	x1, x0, [sp, #8]
	stp	x2, x4, [sp, #32]
	str	x8, [sp, #24]
.LBB6_3:
	ldr	x8, [sp, #32]
	cmp	x29, x8
	b.hs	.LBB6_5
	ldr	x8, [sp, #8]
	add	x8, x8, x29, lsl #4
	ldp	x23, x24, [x8]
	b	.LBB6_6
.LBB6_5:
	mov	x23, xzr
	mov	x24, xzr
.LBB6_6:
	ldr	x22, [sp, #40]
	ldr	x19, [sp, #24]
	add	x29, x29, #1
	add	x21, sp, #48
	add	x20, sp, #1072
.LBB6_7:
	ldrb	w8, [x20]
	tbz	w8, #0, .LBB6_9
	ldp	x25, x26, [x19, #-8]
	ldp	x0, x1, [x21], #16
	strb	wzr, [x20], #1
	eor	x2, x25, #0x1
	mov	x3, x26
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	mov	x27, x0
	mov	x28, x1
	mov	x0, x23
	mov	x1, x24
	mov	x2, x25
	mov	x3, x26
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	subs	x22, x22, #1
	eor	x23, x0, x27
	eor	x24, x1, x28
	add	x19, x19, #16
	b.ne	.LBB6_7
	b	.LBB6_13
.LBB6_9:
	mov	w8, #1
	stp	x23, x24, [x21]
	mov	x24, xzr
	strb	w8, [x20]
	ldr	x8, [sp, #16]
	mov	x23, xzr
	cmp	x29, x8
	b.ne	.LBB6_3
	b	.LBB6_13
.LBB6_10:
	cbz	x2, .LBB6_12
	ldp	x23, x24, [x1]
	b	.LBB6_13
.LBB6_12:
	mov	x24, xzr
	mov	x23, xzr
.LBB6_13:
	mov	x0, x23
	mov	x1, x24
	add	sp, sp, #1136
	.cfi_def_cfa_offset 96
	ldp	x20, x19, [sp, #80]
	ldp	x22, x21, [sp, #64]
	ldp	x24, x23, [sp, #48]
	ldp	x26, x25, [sp, #32]
	ldp	x28, x27, [sp, #16]
	ldp	x29, x30, [sp], #96
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w25
	.cfi_restore w26
	.cfi_restore w27
	.cfi_restore w28
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end6:
	.size	_RINvNtCsemcRClSg8DH_9native_vm5field19multilinear_eval_byNCNvB2_16multilinear_eval0EB4_, .Lfunc_end6-_RINvNtCsemcRClSg8DH_9native_vm5field19multilinear_eval_byNCNvB2_16multilinear_eval0EB4_
	.cfi_endproc

	.section	.text._RINvNtCsemcRClSg8DH_9native_vm5field19multilinear_eval_byNCNvNtB4_3bus23computed_bytecode_value0EB4_,"ax",@progbits
	.p2align	2
	.type	_RINvNtCsemcRClSg8DH_9native_vm5field19multilinear_eval_byNCNvNtB4_3bus23computed_bytecode_value0EB4_,@function
_RINvNtCsemcRClSg8DH_9native_vm5field19multilinear_eval_byNCNvNtB4_3bus23computed_bytecode_value0EB4_:
.Lfunc_begin7:
	.cfi_startproc
	stp	x29, x30, [sp, #-96]!
	.cfi_def_cfa_offset 96
	stp	x28, x27, [sp, #16]
	stp	x26, x25, [sp, #32]
	stp	x24, x23, [sp, #48]
	stp	x22, x21, [sp, #64]
	stp	x20, x19, [sp, #80]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w24, -48
	.cfi_offset w25, -56
	.cfi_offset w26, -64
	.cfi_offset w27, -72
	.cfi_offset w28, -80
	.cfi_offset w30, -88
	.cfi_offset w29, -96
	sub	sp, sp, #1136
	.cfi_def_cfa_offset 1232
	ldr	xzr, [sp]
	cmp	x4, #63
	b.hi	.LBB7_13
	stp	xzr, xzr, [sp, #48]
	stp	xzr, xzr, [sp, #64]
	stp	xzr, xzr, [sp, #80]
	stp	xzr, xzr, [sp, #96]
	stp	xzr, xzr, [sp, #112]
	stp	xzr, xzr, [sp, #128]
	stp	xzr, xzr, [sp, #144]
	stp	xzr, xzr, [sp, #160]
	stp	xzr, xzr, [sp, #176]
	stp	xzr, xzr, [sp, #192]
	stp	xzr, xzr, [sp, #208]
	stp	xzr, xzr, [sp, #224]
	stp	xzr, xzr, [sp, #240]
	stp	xzr, xzr, [sp, #256]
	stp	xzr, xzr, [sp, #272]
	stp	xzr, xzr, [sp, #288]
	stp	xzr, xzr, [sp, #304]
	stp	xzr, xzr, [sp, #320]
	stp	xzr, xzr, [sp, #336]
	stp	xzr, xzr, [sp, #352]
	stp	xzr, xzr, [sp, #368]
	stp	xzr, xzr, [sp, #384]
	stp	xzr, xzr, [sp, #400]
	stp	xzr, xzr, [sp, #416]
	stp	xzr, xzr, [sp, #432]
	stp	xzr, xzr, [sp, #448]
	stp	xzr, xzr, [sp, #464]
	stp	xzr, xzr, [sp, #480]
	stp	xzr, xzr, [sp, #496]
	str	xzr, [sp, #512]
	str	xzr, [sp, #520]
	str	xzr, [sp, #528]
	str	xzr, [sp, #536]
	str	xzr, [sp, #544]
	str	xzr, [sp, #552]
	str	xzr, [sp, #560]
	str	xzr, [sp, #568]
	str	xzr, [sp, #576]
	str	xzr, [sp, #584]
	str	xzr, [sp, #592]
	str	xzr, [sp, #600]
	str	xzr, [sp, #608]
	str	xzr, [sp, #616]
	str	xzr, [sp, #624]
	str	xzr, [sp, #632]
	str	xzr, [sp, #640]
	str	xzr, [sp, #648]
	str	xzr, [sp, #656]
	str	xzr, [sp, #664]
	str	xzr, [sp, #672]
	str	xzr, [sp, #680]
	str	xzr, [sp, #688]
	str	xzr, [sp, #696]
	str	xzr, [sp, #704]
	str	xzr, [sp, #712]
	str	xzr, [sp, #720]
	str	xzr, [sp, #728]
	str	xzr, [sp, #736]
	str	xzr, [sp, #744]
	str	xzr, [sp, #752]
	str	xzr, [sp, #760]
	str	xzr, [sp, #768]
	str	xzr, [sp, #776]
	str	xzr, [sp, #784]
	str	xzr, [sp, #792]
	str	xzr, [sp, #800]
	str	xzr, [sp, #808]
	str	xzr, [sp, #816]
	str	xzr, [sp, #824]
	str	xzr, [sp, #832]
	str	xzr, [sp, #840]
	str	xzr, [sp, #848]
	str	xzr, [sp, #856]
	str	xzr, [sp, #864]
	str	xzr, [sp, #872]
	str	xzr, [sp, #880]
	str	xzr, [sp, #888]
	str	xzr, [sp, #896]
	str	xzr, [sp, #904]
	str	xzr, [sp, #912]
	str	xzr, [sp, #920]
	str	xzr, [sp, #928]
	str	xzr, [sp, #936]
	str	xzr, [sp, #944]
	str	xzr, [sp, #952]
	str	xzr, [sp, #960]
	str	xzr, [sp, #968]
	str	xzr, [sp, #976]
	str	xzr, [sp, #984]
	str	xzr, [sp, #992]
	str	xzr, [sp, #1000]
	str	xzr, [sp, #1008]
	str	xzr, [sp, #1016]
	str	xzr, [sp, #1024]
	str	xzr, [sp, #1032]
	str	xzr, [sp, #1040]
	str	xzr, [sp, #1048]
	str	xzr, [sp, #1056]
	str	xzr, [sp, #1064]
	str	xzr, [sp, #1128]
	str	xzr, [sp, #1120]
	str	xzr, [sp, #1112]
	str	xzr, [sp, #1104]
	str	xzr, [sp, #1096]
	str	xzr, [sp, #1088]
	str	xzr, [sp, #1080]
	str	xzr, [sp, #1072]
	cbz	x0, .LBB7_13
	cbz	x4, .LBB7_11
	mov	x29, xzr
	add	x8, x3, #8
	stp	x1, x0, [sp, #8]
	stp	x2, x4, [sp, #32]
	str	x8, [sp, #24]
.LBB7_4:
	ldr	x8, [sp, #32]
	cmp	x29, x8
	b.hs	.LBB7_6
	ldr	x8, [sp, #8]
	ldr	x22, [x8, x29, lsl #3]
	b	.LBB7_7
.LBB7_6:
	mov	x22, xzr
.LBB7_7:
	ldr	x19, [sp, #40]
	ldr	x21, [sp, #24]
	mov	x23, xzr
	add	x29, x29, #1
	add	x28, sp, #48
	add	x20, sp, #1072
.LBB7_8:
	ldrb	w8, [x20]
	tbz	w8, #0, .LBB7_10
	ldp	x24, x25, [x21, #-8]
	ldp	x0, x1, [x28], #16
	strb	wzr, [x20], #1
	eor	x2, x24, #0x1
	mov	x3, x25
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	mov	x26, x0
	mov	x27, x1
	mov	x0, x22
	mov	x1, x23
	mov	x2, x24
	mov	x3, x25
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	subs	x19, x19, #1
	eor	x22, x0, x26
	eor	x23, x1, x27
	add	x21, x21, #16
	b.ne	.LBB7_8
	b	.LBB7_14
.LBB7_10:
	mov	w8, #1
	stp	x22, x23, [x28]
	mov	x23, xzr
	strb	w8, [x20]
	ldr	x8, [sp, #16]
	mov	x22, xzr
	cmp	x29, x8
	b.ne	.LBB7_4
	b	.LBB7_14
.LBB7_11:
	cbz	x2, .LBB7_13
	ldr	x22, [x1]
	mov	x23, xzr
	b	.LBB7_14
.LBB7_13:
	mov	x23, xzr
	mov	x22, xzr
.LBB7_14:
	mov	x0, x22
	mov	x1, x23
	add	sp, sp, #1136
	.cfi_def_cfa_offset 96
	ldp	x20, x19, [sp, #80]
	ldp	x22, x21, [sp, #64]
	ldp	x24, x23, [sp, #48]
	ldp	x26, x25, [sp, #32]
	ldp	x28, x27, [sp, #16]
	ldp	x29, x30, [sp], #96
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w25
	.cfi_restore w26
	.cfi_restore w27
	.cfi_restore w28
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end7:
	.size	_RINvNtCsemcRClSg8DH_9native_vm5field19multilinear_eval_byNCNvNtB4_3bus23computed_bytecode_value0EB4_, .Lfunc_end7-_RINvNtCsemcRClSg8DH_9native_vm5field19multilinear_eval_byNCNvNtB4_3bus23computed_bytecode_value0EB4_
	.cfi_endproc

	.section	.text._RINvNtCsemcRClSg8DH_9native_vm6keccak15keccak256_wordsNCNvB2_10hash_words0EB4_,"ax",@progbits
	.p2align	2
	.type	_RINvNtCsemcRClSg8DH_9native_vm6keccak15keccak256_wordsNCNvB2_10hash_words0EB4_,@function
_RINvNtCsemcRClSg8DH_9native_vm6keccak15keccak256_wordsNCNvB2_10hash_words0EB4_:
.Lfunc_begin8:
	.cfi_startproc
	sub	sp, sp, #288
	.cfi_def_cfa_offset 288
	stp	x29, x30, [sp, #208]
	stp	x26, x25, [sp, #224]
	stp	x24, x23, [sp, #240]
	stp	x22, x21, [sp, #256]
	stp	x20, x19, [sp, #272]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w24, -48
	.cfi_offset w25, -56
	.cfi_offset w26, -64
	.cfi_offset w30, -72
	.cfi_offset w29, -80
	mov	x20, x2
	mov	x23, x1
	mov	x19, x0
	add	x0, sp, #8
	mov	w1, wzr
	mov	w2, #200
	mov	x22, x4
	mov	x21, x3
	bl	memset
	mov	x8, #-1085102592571150096
	cmp	x23, x22
	movk	x8, #61681
	csel	x22, x23, x22, lo
	cmp	x20, #136
	umulh	x8, x20, x8
	lsr	x24, x8, #7
	add	x23, x24, x24, lsl #4
	b.hs	.LBB8_19
.LBB8_1:
	cmp	x23, x22
	b.hs	.LBB8_56
	ldr	x8, [x21, x23, lsl #3]
	ldr	x10, [sp, #8]
	add	x9, x23, #1
	cmp	x9, x22
	eor	x8, x10, x8
	str	x8, [sp, #8]
	b.lo	.LBB8_57
.LBB8_3:
	ldr	x10, [sp, #16]
	add	x9, x23, #2
	cmp	x9, x22
	eor	x8, x10, xzr
	str	x8, [sp, #16]
	b.lo	.LBB8_58
.LBB8_4:
	ldr	x10, [sp, #24]
	add	x9, x23, #3
	cmp	x9, x22
	eor	x8, x10, xzr
	str	x8, [sp, #24]
	b.lo	.LBB8_59
.LBB8_5:
	ldr	x10, [sp, #32]
	add	x9, x23, #4
	cmp	x9, x22
	eor	x8, x10, xzr
	str	x8, [sp, #32]
	b.lo	.LBB8_60
.LBB8_6:
	ldr	x10, [sp, #40]
	add	x9, x23, #5
	cmp	x9, x22
	eor	x8, x10, xzr
	str	x8, [sp, #40]
	b.lo	.LBB8_61
.LBB8_7:
	ldr	x10, [sp, #48]
	add	x9, x23, #6
	cmp	x9, x22
	eor	x8, x10, xzr
	str	x8, [sp, #48]
	b.lo	.LBB8_62
.LBB8_8:
	ldr	x10, [sp, #56]
	add	x9, x23, #7
	cmp	x9, x22
	eor	x8, x10, xzr
	str	x8, [sp, #56]
	b.lo	.LBB8_63
.LBB8_9:
	ldr	x10, [sp, #64]
	add	x9, x23, #8
	cmp	x9, x22
	eor	x8, x10, xzr
	str	x8, [sp, #64]
	b.lo	.LBB8_64
.LBB8_10:
	ldr	x10, [sp, #72]
	add	x9, x23, #9
	cmp	x9, x22
	eor	x8, x10, xzr
	str	x8, [sp, #72]
	b.lo	.LBB8_65
.LBB8_11:
	ldr	x10, [sp, #80]
	add	x9, x23, #10
	cmp	x9, x22
	eor	x8, x10, xzr
	str	x8, [sp, #80]
	b.lo	.LBB8_66
.LBB8_12:
	ldr	x10, [sp, #88]
	add	x9, x23, #11
	cmp	x9, x22
	eor	x8, x10, xzr
	str	x8, [sp, #88]
	b.lo	.LBB8_67
.LBB8_13:
	ldr	x10, [sp, #96]
	add	x9, x23, #12
	cmp	x9, x22
	eor	x8, x10, xzr
	str	x8, [sp, #96]
	b.lo	.LBB8_68
.LBB8_14:
	ldr	x10, [sp, #104]
	add	x9, x23, #13
	cmp	x9, x22
	eor	x8, x10, xzr
	str	x8, [sp, #104]
	b.lo	.LBB8_69
.LBB8_15:
	ldr	x10, [sp, #112]
	add	x9, x23, #14
	cmp	x9, x22
	eor	x8, x10, xzr
	str	x8, [sp, #112]
	b.lo	.LBB8_70
.LBB8_16:
	ldr	x10, [sp, #120]
	add	x9, x23, #15
	cmp	x9, x22
	eor	x8, x10, xzr
	str	x8, [sp, #120]
	b.lo	.LBB8_71
.LBB8_17:
	ldr	x10, [sp, #128]
	add	x9, x23, #16
	cmp	x9, x22
	eor	x8, x10, xzr
	str	x8, [sp, #128]
	b.lo	.LBB8_72
.LBB8_18:
	mov	x8, xzr
	b	.LBB8_73
.LBB8_19:
	mov	x25, xzr
	add	x26, x21, #64
	b	.LBB8_22
.LBB8_20:
	ldr	x8, [x26, #64]
.LBB8_21:
	ldr	x9, [sp, #136]
	add	x0, sp, #8
	eor	x8, x9, x8
	str	x8, [sp, #136]
	bl	_RNvNtCsemcRClSg8DH_9native_vm6keccak8keccak_f
	add	x25, x25, #17
	add	x26, x26, #136
	cmp	x23, x25
	b.eq	.LBB8_1
.LBB8_22:
	cmp	x25, x22
	b.hs	.LBB8_39
	ldur	x8, [x26, #-64]
	ldr	x9, [sp, #8]
	add	x10, x25, #1
	cmp	x10, x22
	eor	x8, x9, x8
	str	x8, [sp, #8]
	b.lo	.LBB8_40
.LBB8_24:
	ldr	x9, [sp, #16]
	add	x10, x25, #2
	cmp	x10, x22
	eor	x8, x9, xzr
	str	x8, [sp, #16]
	b.lo	.LBB8_41
.LBB8_25:
	ldr	x9, [sp, #24]
	add	x10, x25, #3
	cmp	x10, x22
	eor	x8, x9, xzr
	str	x8, [sp, #24]
	b.lo	.LBB8_42
.LBB8_26:
	ldr	x9, [sp, #32]
	add	x10, x25, #4
	cmp	x10, x22
	eor	x8, x9, xzr
	str	x8, [sp, #32]
	b.lo	.LBB8_43
.LBB8_27:
	ldr	x9, [sp, #40]
	add	x10, x25, #5
	cmp	x10, x22
	eor	x8, x9, xzr
	str	x8, [sp, #40]
	b.lo	.LBB8_44
.LBB8_28:
	ldr	x9, [sp, #48]
	add	x10, x25, #6
	cmp	x10, x22
	eor	x8, x9, xzr
	str	x8, [sp, #48]
	b.lo	.LBB8_45
.LBB8_29:
	ldr	x9, [sp, #56]
	add	x10, x25, #7
	cmp	x10, x22
	eor	x8, x9, xzr
	str	x8, [sp, #56]
	b.lo	.LBB8_46
.LBB8_30:
	ldr	x9, [sp, #64]
	add	x10, x25, #8
	cmp	x10, x22
	eor	x8, x9, xzr
	str	x8, [sp, #64]
	b.lo	.LBB8_47
.LBB8_31:
	ldr	x9, [sp, #72]
	add	x10, x25, #9
	cmp	x10, x22
	eor	x8, x9, xzr
	str	x8, [sp, #72]
	b.lo	.LBB8_48
.LBB8_32:
	ldr	x9, [sp, #80]
	add	x10, x25, #10
	cmp	x10, x22
	eor	x8, x9, xzr
	str	x8, [sp, #80]
	b.lo	.LBB8_49
.LBB8_33:
	ldr	x9, [sp, #88]
	add	x10, x25, #11
	cmp	x10, x22
	eor	x8, x9, xzr
	str	x8, [sp, #88]
	b.lo	.LBB8_50
.LBB8_34:
	ldr	x9, [sp, #96]
	add	x10, x25, #12
	cmp	x10, x22
	eor	x8, x9, xzr
	str	x8, [sp, #96]
	b.lo	.LBB8_51
.LBB8_35:
	ldr	x9, [sp, #104]
	add	x10, x25, #13
	cmp	x10, x22
	eor	x8, x9, xzr
	str	x8, [sp, #104]
	b.lo	.LBB8_52
.LBB8_36:
	ldr	x9, [sp, #112]
	add	x10, x25, #14
	cmp	x10, x22
	eor	x8, x9, xzr
	str	x8, [sp, #112]
	b.lo	.LBB8_53
.LBB8_37:
	ldr	x9, [sp, #120]
	add	x10, x25, #15
	cmp	x10, x22
	eor	x8, x9, xzr
	str	x8, [sp, #120]
	b.lo	.LBB8_54
.LBB8_38:
	ldr	x9, [sp, #128]
	add	x10, x25, #16
	cmp	x10, x22
	eor	x8, x9, xzr
	str	x8, [sp, #128]
	b.lo	.LBB8_20
	b	.LBB8_55
.LBB8_39:
	ldr	x9, [sp, #8]
	add	x10, x25, #1
	cmp	x10, x22
	eor	x8, x9, xzr
	str	x8, [sp, #8]
	b.hs	.LBB8_24
.LBB8_40:
	ldur	x8, [x26, #-56]
	ldr	x9, [sp, #16]
	add	x10, x25, #2
	cmp	x10, x22
	eor	x8, x9, x8
	str	x8, [sp, #16]
	b.hs	.LBB8_25
.LBB8_41:
	ldur	x8, [x26, #-48]
	ldr	x9, [sp, #24]
	add	x10, x25, #3
	cmp	x10, x22
	eor	x8, x9, x8
	str	x8, [sp, #24]
	b.hs	.LBB8_26
.LBB8_42:
	ldur	x8, [x26, #-40]
	ldr	x9, [sp, #32]
	add	x10, x25, #4
	cmp	x10, x22
	eor	x8, x9, x8
	str	x8, [sp, #32]
	b.hs	.LBB8_27
.LBB8_43:
	ldur	x8, [x26, #-32]
	ldr	x9, [sp, #40]
	add	x10, x25, #5
	cmp	x10, x22
	eor	x8, x9, x8
	str	x8, [sp, #40]
	b.hs	.LBB8_28
.LBB8_44:
	ldur	x8, [x26, #-24]
	ldr	x9, [sp, #48]
	add	x10, x25, #6
	cmp	x10, x22
	eor	x8, x9, x8
	str	x8, [sp, #48]
	b.hs	.LBB8_29
.LBB8_45:
	ldur	x8, [x26, #-16]
	ldr	x9, [sp, #56]
	add	x10, x25, #7
	cmp	x10, x22
	eor	x8, x9, x8
	str	x8, [sp, #56]
	b.hs	.LBB8_30
.LBB8_46:
	ldur	x8, [x26, #-8]
	ldr	x9, [sp, #64]
	add	x10, x25, #8
	cmp	x10, x22
	eor	x8, x9, x8
	str	x8, [sp, #64]
	b.hs	.LBB8_31
.LBB8_47:
	ldr	x8, [x26]
	ldr	x9, [sp, #72]
	add	x10, x25, #9
	cmp	x10, x22
	eor	x8, x9, x8
	str	x8, [sp, #72]
	b.hs	.LBB8_32
.LBB8_48:
	ldr	x8, [x26, #8]
	ldr	x9, [sp, #80]
	add	x10, x25, #10
	cmp	x10, x22
	eor	x8, x9, x8
	str	x8, [sp, #80]
	b.hs	.LBB8_33
.LBB8_49:
	ldr	x8, [x26, #16]
	ldr	x9, [sp, #88]
	add	x10, x25, #11
	cmp	x10, x22
	eor	x8, x9, x8
	str	x8, [sp, #88]
	b.hs	.LBB8_34
.LBB8_50:
	ldr	x8, [x26, #24]
	ldr	x9, [sp, #96]
	add	x10, x25, #12
	cmp	x10, x22
	eor	x8, x9, x8
	str	x8, [sp, #96]
	b.hs	.LBB8_35
.LBB8_51:
	ldr	x8, [x26, #32]
	ldr	x9, [sp, #104]
	add	x10, x25, #13
	cmp	x10, x22
	eor	x8, x9, x8
	str	x8, [sp, #104]
	b.hs	.LBB8_36
.LBB8_52:
	ldr	x8, [x26, #40]
	ldr	x9, [sp, #112]
	add	x10, x25, #14
	cmp	x10, x22
	eor	x8, x9, x8
	str	x8, [sp, #112]
	b.hs	.LBB8_37
.LBB8_53:
	ldr	x8, [x26, #48]
	ldr	x9, [sp, #120]
	add	x10, x25, #15
	cmp	x10, x22
	eor	x8, x9, x8
	str	x8, [sp, #120]
	b.hs	.LBB8_38
.LBB8_54:
	ldr	x8, [x26, #56]
	ldr	x9, [sp, #128]
	add	x10, x25, #16
	cmp	x10, x22
	eor	x8, x9, x8
	str	x8, [sp, #128]
	b.lo	.LBB8_20
.LBB8_55:
	mov	x8, xzr
	b	.LBB8_21
.LBB8_56:
	ldr	x10, [sp, #8]
	add	x9, x23, #1
	cmp	x9, x22
	eor	x8, x10, xzr
	str	x8, [sp, #8]
	b.hs	.LBB8_3
.LBB8_57:
	ldr	x8, [x21, x9, lsl #3]
	ldr	x10, [sp, #16]
	add	x9, x23, #2
	cmp	x9, x22
	eor	x8, x10, x8
	str	x8, [sp, #16]
	b.hs	.LBB8_4
.LBB8_58:
	ldr	x8, [x21, x9, lsl #3]
	ldr	x10, [sp, #24]
	add	x9, x23, #3
	cmp	x9, x22
	eor	x8, x10, x8
	str	x8, [sp, #24]
	b.hs	.LBB8_5
.LBB8_59:
	ldr	x8, [x21, x9, lsl #3]
	ldr	x10, [sp, #32]
	add	x9, x23, #4
	cmp	x9, x22
	eor	x8, x10, x8
	str	x8, [sp, #32]
	b.hs	.LBB8_6
.LBB8_60:
	ldr	x8, [x21, x9, lsl #3]
	ldr	x10, [sp, #40]
	add	x9, x23, #5
	cmp	x9, x22
	eor	x8, x10, x8
	str	x8, [sp, #40]
	b.hs	.LBB8_7
.LBB8_61:
	ldr	x8, [x21, x9, lsl #3]
	ldr	x10, [sp, #48]
	add	x9, x23, #6
	cmp	x9, x22
	eor	x8, x10, x8
	str	x8, [sp, #48]
	b.hs	.LBB8_8
.LBB8_62:
	ldr	x8, [x21, x9, lsl #3]
	ldr	x10, [sp, #56]
	add	x9, x23, #7
	cmp	x9, x22
	eor	x8, x10, x8
	str	x8, [sp, #56]
	b.hs	.LBB8_9
.LBB8_63:
	ldr	x8, [x21, x9, lsl #3]
	ldr	x10, [sp, #64]
	add	x9, x23, #8
	cmp	x9, x22
	eor	x8, x10, x8
	str	x8, [sp, #64]
	b.hs	.LBB8_10
.LBB8_64:
	ldr	x8, [x21, x9, lsl #3]
	ldr	x10, [sp, #72]
	add	x9, x23, #9
	cmp	x9, x22
	eor	x8, x10, x8
	str	x8, [sp, #72]
	b.hs	.LBB8_11
.LBB8_65:
	ldr	x8, [x21, x9, lsl #3]
	ldr	x10, [sp, #80]
	add	x9, x23, #10
	cmp	x9, x22
	eor	x8, x10, x8
	str	x8, [sp, #80]
	b.hs	.LBB8_12
.LBB8_66:
	ldr	x8, [x21, x9, lsl #3]
	ldr	x10, [sp, #88]
	add	x9, x23, #11
	cmp	x9, x22
	eor	x8, x10, x8
	str	x8, [sp, #88]
	b.hs	.LBB8_13
.LBB8_67:
	ldr	x8, [x21, x9, lsl #3]
	ldr	x10, [sp, #96]
	add	x9, x23, #12
	cmp	x9, x22
	eor	x8, x10, x8
	str	x8, [sp, #96]
	b.hs	.LBB8_14
.LBB8_68:
	ldr	x8, [x21, x9, lsl #3]
	ldr	x10, [sp, #104]
	add	x9, x23, #13
	cmp	x9, x22
	eor	x8, x10, x8
	str	x8, [sp, #104]
	b.hs	.LBB8_15
.LBB8_69:
	ldr	x8, [x21, x9, lsl #3]
	ldr	x10, [sp, #112]
	add	x9, x23, #14
	cmp	x9, x22
	eor	x8, x10, x8
	str	x8, [sp, #112]
	b.hs	.LBB8_16
.LBB8_70:
	ldr	x8, [x21, x9, lsl #3]
	ldr	x10, [sp, #120]
	add	x9, x23, #15
	cmp	x9, x22
	eor	x8, x10, x8
	str	x8, [sp, #120]
	b.hs	.LBB8_17
.LBB8_71:
	ldr	x8, [x21, x9, lsl #3]
	ldr	x10, [sp, #128]
	add	x9, x23, #16
	cmp	x9, x22
	eor	x8, x10, x8
	str	x8, [sp, #128]
	b.hs	.LBB8_18
.LBB8_72:
	ldr	x8, [x21, x9, lsl #3]
.LBB8_73:
	mov	w9, #136
	ldr	x10, [sp, #136]
	add	x11, sp, #8
	msub	x9, x24, x9, x20
	add	x0, sp, #8
	eor	x8, x10, x8
	mov	w10, #1
	str	x8, [sp, #136]
	ubfiz	x8, x9, #3, #3
	and	x9, x9, #0xfffffffffffffff8
	lsl	x8, x10, x8
	ldr	x10, [x11, x9]
	eor	x8, x10, x8
	str	x8, [x11, x9]
	ldr	x8, [sp, #136]
	eor	x8, x8, #0x8000000000000000
	str	x8, [sp, #136]
	bl	_RNvNtCsemcRClSg8DH_9native_vm6keccak8keccak_f
	ldp	x8, x9, [sp, #8]
	ldp	x22, x21, [sp, #256]
	ldp	x24, x23, [sp, #240]
	stp	x8, x9, [x19]
	ldp	x8, x10, [sp, #24]
	ldp	x26, x25, [sp, #224]
	ldp	x29, x30, [sp, #208]
	stp	x8, x10, [x19, #16]
	ldp	x20, x19, [sp, #272]
	add	sp, sp, #288
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w25
	.cfi_restore w26
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end8:
	.size	_RINvNtCsemcRClSg8DH_9native_vm6keccak15keccak256_wordsNCNvB2_10hash_words0EB4_, .Lfunc_end8-_RINvNtCsemcRClSg8DH_9native_vm6keccak15keccak256_wordsNCNvB2_10hash_words0EB4_
	.cfi_endproc

	.section	.text._RINvNtCsemcRClSg8DH_9native_vm6keccak15keccak256_wordsNCNvNtB4_6verify14fiat_shamir_iv0EB4_,"ax",@progbits
	.p2align	2
	.type	_RINvNtCsemcRClSg8DH_9native_vm6keccak15keccak256_wordsNCNvNtB4_6verify14fiat_shamir_iv0EB4_,@function
_RINvNtCsemcRClSg8DH_9native_vm6keccak15keccak256_wordsNCNvNtB4_6verify14fiat_shamir_iv0EB4_:
.Lfunc_begin9:
	.cfi_startproc
	sub	sp, sp, #288
	.cfi_def_cfa_offset 288
	str	x29, [sp, #208]
	stp	x30, x25, [sp, #224]
	stp	x24, x23, [sp, #240]
	stp	x22, x21, [sp, #256]
	stp	x20, x19, [sp, #272]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w24, -48
	.cfi_offset w25, -56
	.cfi_offset w30, -64
	.cfi_offset w29, -80
	mov	x20, x2
	mov	x23, x1
	mov	x19, x0
	add	x0, sp, #8
	mov	w1, wzr
	mov	w2, #200
	mov	x21, x4
	mov	x22, x3
	bl	memset
	mov	w8, #61681
	cmp	x20, #136
	movk	w8, #61680, lsl #16
	umull	x8, w20, w8
	lsr	x8, x8, #39
	add	x24, x8, x8, lsl #4
	b.hs	.LBB9_19
.LBB9_1:
	cmp	x24, x23
	b.hs	.LBB9_56
	mov	x0, x22
	mov	x1, x21
	mov	x2, x24
	bl	_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word
	ldr	x8, [sp, #8]
	add	x9, x24, #1
	cmp	x9, x23
	eor	x8, x8, x0
	str	x8, [sp, #8]
	b.lo	.LBB9_57
.LBB9_3:
	ldr	x8, [sp, #16]
	add	x9, x24, #2
	cmp	x9, x23
	eor	x8, x8, xzr
	str	x8, [sp, #16]
	b.lo	.LBB9_58
.LBB9_4:
	ldr	x8, [sp, #24]
	add	x9, x24, #3
	cmp	x9, x23
	eor	x8, x8, xzr
	str	x8, [sp, #24]
	b.lo	.LBB9_59
.LBB9_5:
	ldr	x8, [sp, #32]
	add	x9, x24, #4
	cmp	x9, x23
	eor	x8, x8, xzr
	str	x8, [sp, #32]
	b.lo	.LBB9_60
.LBB9_6:
	ldr	x8, [sp, #40]
	add	x9, x24, #5
	cmp	x9, x23
	eor	x8, x8, xzr
	str	x8, [sp, #40]
	b.lo	.LBB9_61
.LBB9_7:
	ldr	x8, [sp, #48]
	add	x9, x24, #6
	cmp	x9, x23
	eor	x8, x8, xzr
	str	x8, [sp, #48]
	b.lo	.LBB9_62
.LBB9_8:
	ldr	x8, [sp, #56]
	add	x9, x24, #7
	cmp	x9, x23
	eor	x8, x8, xzr
	str	x8, [sp, #56]
	b.lo	.LBB9_63
.LBB9_9:
	ldr	x8, [sp, #64]
	add	x9, x24, #8
	cmp	x9, x23
	eor	x8, x8, xzr
	str	x8, [sp, #64]
	b.lo	.LBB9_64
.LBB9_10:
	ldr	x8, [sp, #72]
	add	x9, x24, #9
	cmp	x9, x23
	eor	x8, x8, xzr
	str	x8, [sp, #72]
	b.lo	.LBB9_65
.LBB9_11:
	ldr	x8, [sp, #80]
	add	x9, x24, #10
	cmp	x9, x23
	eor	x8, x8, xzr
	str	x8, [sp, #80]
	b.lo	.LBB9_66
.LBB9_12:
	ldr	x8, [sp, #88]
	add	x9, x24, #11
	cmp	x9, x23
	eor	x8, x8, xzr
	str	x8, [sp, #88]
	b.lo	.LBB9_67
.LBB9_13:
	ldr	x8, [sp, #96]
	add	x9, x24, #12
	cmp	x9, x23
	eor	x8, x8, xzr
	str	x8, [sp, #96]
	b.lo	.LBB9_68
.LBB9_14:
	ldr	x8, [sp, #104]
	add	x9, x24, #13
	cmp	x9, x23
	eor	x8, x8, xzr
	str	x8, [sp, #104]
	b.lo	.LBB9_69
.LBB9_15:
	ldr	x8, [sp, #112]
	add	x9, x24, #14
	cmp	x9, x23
	eor	x8, x8, xzr
	str	x8, [sp, #112]
	b.lo	.LBB9_70
.LBB9_16:
	ldr	x8, [sp, #120]
	add	x9, x24, #15
	cmp	x9, x23
	eor	x8, x8, xzr
	str	x8, [sp, #120]
	b.lo	.LBB9_71
.LBB9_17:
	ldr	x8, [sp, #128]
	add	x2, x24, #16
	cmp	x2, x23
	eor	x8, x8, xzr
	str	x8, [sp, #128]
	b.lo	.LBB9_72
.LBB9_18:
	mov	x0, xzr
	b	.LBB9_73
.LBB9_19:
	mov	x25, xzr
	b	.LBB9_22
.LBB9_20:
	add	x2, x25, #16
	mov	x0, x22
	mov	x1, x21
	bl	_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word
.LBB9_21:
	ldr	x8, [sp, #136]
	eor	x8, x8, x0
	add	x0, sp, #8
	str	x8, [sp, #136]
	bl	_RNvNtCsemcRClSg8DH_9native_vm6keccak8keccak_f
	add	x25, x25, #17
	cmp	x24, x25
	b.eq	.LBB9_1
.LBB9_22:
	cmp	x25, x23
	b.hs	.LBB9_39
	mov	x0, x22
	mov	x1, x21
	mov	x2, x25
	bl	_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word
	ldr	x8, [sp, #8]
	add	x9, x25, #1
	cmp	x9, x23
	eor	x8, x8, x0
	str	x8, [sp, #8]
	b.lo	.LBB9_40
.LBB9_24:
	ldr	x8, [sp, #16]
	add	x9, x25, #2
	cmp	x9, x23
	eor	x8, x8, xzr
	str	x8, [sp, #16]
	b.lo	.LBB9_41
.LBB9_25:
	ldr	x8, [sp, #24]
	add	x9, x25, #3
	cmp	x9, x23
	eor	x8, x8, xzr
	str	x8, [sp, #24]
	b.lo	.LBB9_42
.LBB9_26:
	ldr	x8, [sp, #32]
	add	x9, x25, #4
	cmp	x9, x23
	eor	x8, x8, xzr
	str	x8, [sp, #32]
	b.lo	.LBB9_43
.LBB9_27:
	ldr	x8, [sp, #40]
	add	x9, x25, #5
	cmp	x9, x23
	eor	x8, x8, xzr
	str	x8, [sp, #40]
	b.lo	.LBB9_44
.LBB9_28:
	ldr	x8, [sp, #48]
	add	x9, x25, #6
	cmp	x9, x23
	eor	x8, x8, xzr
	str	x8, [sp, #48]
	b.lo	.LBB9_45
.LBB9_29:
	ldr	x8, [sp, #56]
	add	x9, x25, #7
	cmp	x9, x23
	eor	x8, x8, xzr
	str	x8, [sp, #56]
	b.lo	.LBB9_46
.LBB9_30:
	ldr	x8, [sp, #64]
	add	x9, x25, #8
	cmp	x9, x23
	eor	x8, x8, xzr
	str	x8, [sp, #64]
	b.lo	.LBB9_47
.LBB9_31:
	ldr	x8, [sp, #72]
	add	x9, x25, #9
	cmp	x9, x23
	eor	x8, x8, xzr
	str	x8, [sp, #72]
	b.lo	.LBB9_48
.LBB9_32:
	ldr	x8, [sp, #80]
	add	x9, x25, #10
	cmp	x9, x23
	eor	x8, x8, xzr
	str	x8, [sp, #80]
	b.lo	.LBB9_49
.LBB9_33:
	ldr	x8, [sp, #88]
	add	x9, x25, #11
	cmp	x9, x23
	eor	x8, x8, xzr
	str	x8, [sp, #88]
	b.lo	.LBB9_50
.LBB9_34:
	ldr	x8, [sp, #96]
	add	x9, x25, #12
	cmp	x9, x23
	eor	x8, x8, xzr
	str	x8, [sp, #96]
	b.lo	.LBB9_51
.LBB9_35:
	ldr	x8, [sp, #104]
	add	x9, x25, #13
	cmp	x9, x23
	eor	x8, x8, xzr
	str	x8, [sp, #104]
	b.lo	.LBB9_52
.LBB9_36:
	ldr	x8, [sp, #112]
	add	x9, x25, #14
	cmp	x9, x23
	eor	x8, x8, xzr
	str	x8, [sp, #112]
	b.lo	.LBB9_53
.LBB9_37:
	ldr	x8, [sp, #120]
	add	x9, x25, #15
	cmp	x9, x23
	eor	x8, x8, xzr
	str	x8, [sp, #120]
	b.lo	.LBB9_54
.LBB9_38:
	ldr	x8, [sp, #128]
	add	x9, x25, #16
	cmp	x9, x23
	eor	x8, x8, xzr
	str	x8, [sp, #128]
	b.lo	.LBB9_20
	b	.LBB9_55
.LBB9_39:
	ldr	x8, [sp, #8]
	add	x9, x25, #1
	cmp	x9, x23
	eor	x8, x8, xzr
	str	x8, [sp, #8]
	b.hs	.LBB9_24
.LBB9_40:
	add	x2, x25, #1
	mov	x0, x22
	mov	x1, x21
	bl	_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word
	ldr	x8, [sp, #16]
	add	x9, x25, #2
	cmp	x9, x23
	eor	x8, x8, x0
	str	x8, [sp, #16]
	b.hs	.LBB9_25
.LBB9_41:
	add	x2, x25, #2
	mov	x0, x22
	mov	x1, x21
	bl	_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word
	ldr	x8, [sp, #24]
	add	x9, x25, #3
	cmp	x9, x23
	eor	x8, x8, x0
	str	x8, [sp, #24]
	b.hs	.LBB9_26
.LBB9_42:
	add	x2, x25, #3
	mov	x0, x22
	mov	x1, x21
	bl	_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word
	ldr	x8, [sp, #32]
	add	x9, x25, #4
	cmp	x9, x23
	eor	x8, x8, x0
	str	x8, [sp, #32]
	b.hs	.LBB9_27
.LBB9_43:
	add	x2, x25, #4
	mov	x0, x22
	mov	x1, x21
	bl	_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word
	ldr	x8, [sp, #40]
	add	x9, x25, #5
	cmp	x9, x23
	eor	x8, x8, x0
	str	x8, [sp, #40]
	b.hs	.LBB9_28
.LBB9_44:
	add	x2, x25, #5
	mov	x0, x22
	mov	x1, x21
	bl	_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word
	ldr	x8, [sp, #48]
	add	x9, x25, #6
	cmp	x9, x23
	eor	x8, x8, x0
	str	x8, [sp, #48]
	b.hs	.LBB9_29
.LBB9_45:
	add	x2, x25, #6
	mov	x0, x22
	mov	x1, x21
	bl	_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word
	ldr	x8, [sp, #56]
	add	x9, x25, #7
	cmp	x9, x23
	eor	x8, x8, x0
	str	x8, [sp, #56]
	b.hs	.LBB9_30
.LBB9_46:
	add	x2, x25, #7
	mov	x0, x22
	mov	x1, x21
	bl	_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word
	ldr	x8, [sp, #64]
	add	x9, x25, #8
	cmp	x9, x23
	eor	x8, x8, x0
	str	x8, [sp, #64]
	b.hs	.LBB9_31
.LBB9_47:
	add	x2, x25, #8
	mov	x0, x22
	mov	x1, x21
	bl	_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word
	ldr	x8, [sp, #72]
	add	x9, x25, #9
	cmp	x9, x23
	eor	x8, x8, x0
	str	x8, [sp, #72]
	b.hs	.LBB9_32
.LBB9_48:
	add	x2, x25, #9
	mov	x0, x22
	mov	x1, x21
	bl	_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word
	ldr	x8, [sp, #80]
	add	x9, x25, #10
	cmp	x9, x23
	eor	x8, x8, x0
	str	x8, [sp, #80]
	b.hs	.LBB9_33
.LBB9_49:
	add	x2, x25, #10
	mov	x0, x22
	mov	x1, x21
	bl	_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word
	ldr	x8, [sp, #88]
	add	x9, x25, #11
	cmp	x9, x23
	eor	x8, x8, x0
	str	x8, [sp, #88]
	b.hs	.LBB9_34
.LBB9_50:
	add	x2, x25, #11
	mov	x0, x22
	mov	x1, x21
	bl	_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word
	ldr	x8, [sp, #96]
	add	x9, x25, #12
	cmp	x9, x23
	eor	x8, x8, x0
	str	x8, [sp, #96]
	b.hs	.LBB9_35
.LBB9_51:
	add	x2, x25, #12
	mov	x0, x22
	mov	x1, x21
	bl	_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word
	ldr	x8, [sp, #104]
	add	x9, x25, #13
	cmp	x9, x23
	eor	x8, x8, x0
	str	x8, [sp, #104]
	b.hs	.LBB9_36
.LBB9_52:
	add	x2, x25, #13
	mov	x0, x22
	mov	x1, x21
	bl	_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word
	ldr	x8, [sp, #112]
	add	x9, x25, #14
	cmp	x9, x23
	eor	x8, x8, x0
	str	x8, [sp, #112]
	b.hs	.LBB9_37
.LBB9_53:
	add	x2, x25, #14
	mov	x0, x22
	mov	x1, x21
	bl	_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word
	ldr	x8, [sp, #120]
	add	x9, x25, #15
	cmp	x9, x23
	eor	x8, x8, x0
	str	x8, [sp, #120]
	b.hs	.LBB9_38
.LBB9_54:
	add	x2, x25, #15
	mov	x0, x22
	mov	x1, x21
	bl	_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word
	ldr	x8, [sp, #128]
	add	x9, x25, #16
	cmp	x9, x23
	eor	x8, x8, x0
	str	x8, [sp, #128]
	b.lo	.LBB9_20
.LBB9_55:
	mov	x0, xzr
	b	.LBB9_21
.LBB9_56:
	ldr	x8, [sp, #8]
	add	x9, x24, #1
	cmp	x9, x23
	eor	x8, x8, xzr
	str	x8, [sp, #8]
	b.hs	.LBB9_3
.LBB9_57:
	add	x2, x24, #1
	mov	x0, x22
	mov	x1, x21
	bl	_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word
	ldr	x8, [sp, #16]
	add	x9, x24, #2
	cmp	x9, x23
	eor	x8, x8, x0
	str	x8, [sp, #16]
	b.hs	.LBB9_4
.LBB9_58:
	add	x2, x24, #2
	mov	x0, x22
	mov	x1, x21
	bl	_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word
	ldr	x8, [sp, #24]
	add	x9, x24, #3
	cmp	x9, x23
	eor	x8, x8, x0
	str	x8, [sp, #24]
	b.hs	.LBB9_5
.LBB9_59:
	add	x2, x24, #3
	mov	x0, x22
	mov	x1, x21
	bl	_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word
	ldr	x8, [sp, #32]
	add	x9, x24, #4
	cmp	x9, x23
	eor	x8, x8, x0
	str	x8, [sp, #32]
	b.hs	.LBB9_6
.LBB9_60:
	add	x2, x24, #4
	mov	x0, x22
	mov	x1, x21
	bl	_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word
	ldr	x8, [sp, #40]
	add	x9, x24, #5
	cmp	x9, x23
	eor	x8, x8, x0
	str	x8, [sp, #40]
	b.hs	.LBB9_7
.LBB9_61:
	add	x2, x24, #5
	mov	x0, x22
	mov	x1, x21
	bl	_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word
	ldr	x8, [sp, #48]
	add	x9, x24, #6
	cmp	x9, x23
	eor	x8, x8, x0
	str	x8, [sp, #48]
	b.hs	.LBB9_8
.LBB9_62:
	add	x2, x24, #6
	mov	x0, x22
	mov	x1, x21
	bl	_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word
	ldr	x8, [sp, #56]
	add	x9, x24, #7
	cmp	x9, x23
	eor	x8, x8, x0
	str	x8, [sp, #56]
	b.hs	.LBB9_9
.LBB9_63:
	add	x2, x24, #7
	mov	x0, x22
	mov	x1, x21
	bl	_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word
	ldr	x8, [sp, #64]
	add	x9, x24, #8
	cmp	x9, x23
	eor	x8, x8, x0
	str	x8, [sp, #64]
	b.hs	.LBB9_10
.LBB9_64:
	add	x2, x24, #8
	mov	x0, x22
	mov	x1, x21
	bl	_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word
	ldr	x8, [sp, #72]
	add	x9, x24, #9
	cmp	x9, x23
	eor	x8, x8, x0
	str	x8, [sp, #72]
	b.hs	.LBB9_11
.LBB9_65:
	add	x2, x24, #9
	mov	x0, x22
	mov	x1, x21
	bl	_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word
	ldr	x8, [sp, #80]
	add	x9, x24, #10
	cmp	x9, x23
	eor	x8, x8, x0
	str	x8, [sp, #80]
	b.hs	.LBB9_12
.LBB9_66:
	add	x2, x24, #10
	mov	x0, x22
	mov	x1, x21
	bl	_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word
	ldr	x8, [sp, #88]
	add	x9, x24, #11
	cmp	x9, x23
	eor	x8, x8, x0
	str	x8, [sp, #88]
	b.hs	.LBB9_13
.LBB9_67:
	add	x2, x24, #11
	mov	x0, x22
	mov	x1, x21
	bl	_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word
	ldr	x8, [sp, #96]
	add	x9, x24, #12
	cmp	x9, x23
	eor	x8, x8, x0
	str	x8, [sp, #96]
	b.hs	.LBB9_14
.LBB9_68:
	add	x2, x24, #12
	mov	x0, x22
	mov	x1, x21
	bl	_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word
	ldr	x8, [sp, #104]
	add	x9, x24, #13
	cmp	x9, x23
	eor	x8, x8, x0
	str	x8, [sp, #104]
	b.hs	.LBB9_15
.LBB9_69:
	add	x2, x24, #13
	mov	x0, x22
	mov	x1, x21
	bl	_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word
	ldr	x8, [sp, #112]
	add	x9, x24, #14
	cmp	x9, x23
	eor	x8, x8, x0
	str	x8, [sp, #112]
	b.hs	.LBB9_16
.LBB9_70:
	add	x2, x24, #14
	mov	x0, x22
	mov	x1, x21
	bl	_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word
	ldr	x8, [sp, #120]
	add	x9, x24, #15
	cmp	x9, x23
	eor	x8, x8, x0
	str	x8, [sp, #120]
	b.hs	.LBB9_17
.LBB9_71:
	add	x2, x24, #15
	mov	x0, x22
	mov	x1, x21
	bl	_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word
	ldr	x8, [sp, #128]
	add	x2, x24, #16
	cmp	x2, x23
	eor	x8, x8, x0
	str	x8, [sp, #128]
	b.hs	.LBB9_18
.LBB9_72:
	mov	x0, x22
	mov	x1, x21
	bl	_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word
.LBB9_73:
	mov	x8, #-1085102592571150096
	mov	w9, #136
	mov	w10, #1
	movk	x8, #61681
	add	x11, sp, #8
	umulh	x8, x20, x8
	lsr	x8, x8, #7
	msub	x8, x8, x9, x20
	ldr	x9, [sp, #136]
	eor	x9, x9, x0
	add	x0, sp, #8
	str	x9, [sp, #136]
	ubfiz	x9, x8, #3, #3
	and	x8, x8, #0xf8
	lsl	x9, x10, x9
	ldr	x10, [x11, x8]
	eor	x9, x10, x9
	str	x9, [x11, x8]
	ldr	x8, [sp, #136]
	eor	x8, x8, #0x8000000000000000
	str	x8, [sp, #136]
	bl	_RNvNtCsemcRClSg8DH_9native_vm6keccak8keccak_f
	ldp	x8, x9, [sp, #8]
	ldr	x29, [sp, #208]
	ldp	x22, x21, [sp, #256]
	ldp	x24, x23, [sp, #240]
	stp	x8, x9, [x19]
	ldp	x8, x10, [sp, #24]
	ldp	x30, x25, [sp, #224]
	stp	x8, x10, [x19, #16]
	ldp	x20, x19, [sp, #272]
	add	sp, sp, #288
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w25
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end9:
	.size	_RINvNtCsemcRClSg8DH_9native_vm6keccak15keccak256_wordsNCNvNtB4_6verify14fiat_shamir_iv0EB4_, .Lfunc_end9-_RINvNtCsemcRClSg8DH_9native_vm6keccak15keccak256_wordsNCNvNtB4_6verify14fiat_shamir_iv0EB4_
	.cfi_endproc

	.section	.text._RINvNtCsemcRClSg8DH_9native_vm6layout14insertion_sortNCNvB2_13stack_offsetss_0EB4_,"ax",@progbits
	.p2align	2
	.type	_RINvNtCsemcRClSg8DH_9native_vm6layout14insertion_sortNCNvB2_13stack_offsetss_0EB4_,@function
_RINvNtCsemcRClSg8DH_9native_vm6layout14insertion_sortNCNvB2_13stack_offsetss_0EB4_:
.Lfunc_begin10:
	.cfi_startproc
	cbz	x1, .LBB10_16
	mov	x8, xzr
	b	.LBB10_3
.LBB10_2:
	add	x8, x8, #1
	cmp	x8, x1
	b.eq	.LBB10_16
.LBB10_3:
	cbz	x8, .LBB10_2
	ldr	x9, [x0, x8, lsl #3]
	mov	x10, x8
.LBB10_5:
	add	x11, x0, x10, lsl #3
	ldur	x12, [x11, #-8]
	cmp	x12, x3
	b.hs	.LBB10_8
	ldr	x14, [x2, x12, lsl #3]
	cmp	x9, x3
	b.lo	.LBB10_9
.LBB10_7:
	mov	x13, xzr
	b	.LBB10_10
.LBB10_8:
	mov	x14, xzr
	cmp	x9, x3
	b.hs	.LBB10_7
.LBB10_9:
	ldr	x13, [x2, x9, lsl #3]
	cmp	x14, x13
	b.lo	.LBB10_14
.LBB10_10:
	cmp	x12, x3
	b.hs	.LBB10_12
	ldr	x14, [x2, x12, lsl #3]
	cmp	x9, x12
	b.lo	.LBB10_13
	b	.LBB10_2
.LBB10_12:
	mov	x14, xzr
	cmp	x9, x12
	b.hs	.LBB10_2
.LBB10_13:
	cmp	x13, x14
	b.ne	.LBB10_2
.LBB10_14:
	str	x12, [x0, x10, lsl #3]
	subs	x12, x10, #1
	stur	x9, [x11, #-8]
	b.eq	.LBB10_2
	sub	x10, x10, #1
	cmp	x10, x1
	mov	x10, x12
	b.lo	.LBB10_5
	b	.LBB10_2
.LBB10_16:
	ret
.Lfunc_end10:
	.size	_RINvNtCsemcRClSg8DH_9native_vm6layout14insertion_sortNCNvB2_13stack_offsetss_0EB4_, .Lfunc_end10-_RINvNtCsemcRClSg8DH_9native_vm6layout14insertion_sortNCNvB2_13stack_offsetss_0EB4_
	.cfi_endproc

	.section	.text._RNCNvNtCsemcRClSg8DH_9native_vm3bus18verify_bus_balance0B5_,"ax",@progbits
	.p2align	2
	.type	_RNCNvNtCsemcRClSg8DH_9native_vm3bus18verify_bus_balance0B5_,@function
_RNCNvNtCsemcRClSg8DH_9native_vm3bus18verify_bus_balance0B5_:
.Lfunc_begin11:
	.cfi_startproc
	sub	sp, sp, #64
	.cfi_def_cfa_offset 64
	.cfi_offset w30, -16
	ldp	x13, x14, [x1, #40]
	ldr	x12, [x1, #32]
	ldp	x8, x9, [x1]
	ldp	x10, x11, [x1, #16]
	ldp	x7, x14, [x14]
	stp	x6, x30, [sp, #40]
	mov	x1, x8
	mov	x6, x13
	stp	x4, x5, [sp, #24]
	stp	x2, x3, [sp, #8]
	mov	x2, x9
	mov	x3, x10
	mov	x4, x11
	mov	x5, x12
	str	x14, [sp]
	bl	_RNvNtCsemcRClSg8DH_9native_vm3bus12fingerprints
	ldr	x30, [sp, #48]
	add	sp, sp, #64
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	ret
.Lfunc_end11:
	.size	_RNCNvNtCsemcRClSg8DH_9native_vm3bus18verify_bus_balance0B5_, .Lfunc_end11-_RNCNvNtCsemcRClSg8DH_9native_vm3bus18verify_bus_balance0B5_
	.cfi_endproc

	.section	.text._RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW12absorb_nonce,"ax",@progbits
	.p2align	2
	.type	_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW12absorb_nonce,@function
_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW12absorb_nonce:
.Lfunc_begin12:
	.cfi_startproc
	stp	x30, x19, [sp, #-16]!
	.cfi_def_cfa_offset 16
	.cfi_offset w19, -8
	.cfi_offset w30, -16
	mov	w3, #4
	mov	x19, x0
	bl	_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW6absorb
	mov	x0, x19
	bl	_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW6duplex
	ldp	x10, x0, [x19, #8]
	mov	w8, #1
	ldr	x9, [x19]
	stp	x8, x9, [x19, #304]
	str	x10, [x19, #320]
	ldp	x30, x19, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w30
	ret
.Lfunc_end12:
	.size	_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW12absorb_nonce, .Lfunc_end12-_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW12absorb_nonce
	.cfi_endproc

	.section	.text._RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW12duplex_input,"ax",@progbits
	.p2align	2
	.type	_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW12duplex_input,@function
_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW12duplex_input:
.Lfunc_begin13:
	.cfi_startproc
	ldr	x8, [x0, #296]
	cbz	x8, .LBB13_6
	ldp	x9, x10, [x0, #200]
	cmp	x8, #1
	stp	x9, x10, [x0]
	ldr	x9, [x0, #216]
	stp	xzr, x9, [x0, #16]
	b.eq	.LBB13_7
	ldp	x9, x10, [x0, #224]
	cmp	x8, #2
	stp	x9, x10, [x0, #32]
	ldr	x9, [x0, #240]
	stp	xzr, x9, [x0, #48]
	b.ls	.LBB13_8
	ldp	x12, x13, [x0, #248]
	mov	x9, xzr
	mov	x10, xzr
	mov	x11, xzr
	cmp	x8, #3
	stp	x12, x13, [x0, #64]
	ldr	x12, [x0, #264]
	stp	xzr, x12, [x0, #80]
	b.eq	.LBB13_5
	ldp	x11, x10, [x0, #272]
	ldr	x9, [x0, #288]
.LBB13_5:
	stp	x11, x10, [x0, #96]
	stp	xzr, x9, [x0, #112]
	ret
.LBB13_6:
	stp	xzr, xzr, [x0]
	stp	xzr, xzr, [x0, #16]
.LBB13_7:
	stp	xzr, xzr, [x0, #32]
	stp	xzr, xzr, [x0, #48]
.LBB13_8:
	stp	xzr, xzr, [x0, #64]
	stp	xzr, xzr, [x0, #80]
	stp	xzr, xzr, [x0, #96]
	stp	xzr, xzr, [x0, #112]
	ret
.Lfunc_end13:
	.size	_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW12duplex_input, .Lfunc_end13-_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW12duplex_input
	.cfi_endproc

	.section	.text._RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW6absorb,"ax",@progbits
	.p2align	2
	.type	_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW6absorb,@function
_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW6absorb:
.Lfunc_begin14:
	.cfi_startproc
	str	x30, [sp, #-48]!
	.cfi_def_cfa_offset 48
	stp	x22, x21, [sp, #16]
	stp	x20, x19, [sp, #32]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w30, -48
	ldr	x8, [x0, #296]
	mov	x19, x3
	mov	x21, x2
	mov	x20, x0
	mov	x22, x1
	cmp	x8, #4
	b.lo	.LBB14_2
	mov	x0, x20
	bl	_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW6duplex
	ldr	x8, [x20, #296]
	cmp	x8, #3
	b.hi	.LBB14_3
.LBB14_2:
	mov	w9, #24
	madd	x9, x8, x9, x20
	add	x8, x8, #1
	str	x8, [x20, #296]
	stp	x22, x21, [x9, #200]
	str	x19, [x9, #216]
.LBB14_3:
	ldp	x20, x19, [sp, #32]
	ldp	x22, x21, [sp, #16]
	ldr	x30, [sp], #48
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w30
	ret
.Lfunc_end14:
	.size	_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW6absorb, .Lfunc_end14-_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW6absorb
	.cfi_endproc

	.section	.text._RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW6duplex,"ax",@progbits
	.p2align	2
	.type	_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW6duplex,@function
_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW6duplex:
.Lfunc_begin15:
	.cfi_startproc
	stp	x30, x19, [sp, #-16]!
	.cfi_def_cfa_offset 16
	.cfi_offset w19, -8
	.cfi_offset w30, -16
	mov	x19, x0
	bl	_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW12duplex_input
	mov	x0, x19
	bl	_RNvNtCsemcRClSg8DH_9native_vm6keccak8keccak_f
	str	xzr, [x19, #296]
	ldp	x30, x19, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w30
	ret
.Lfunc_end15:
	.size	_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW6duplex, .Lfunc_end15-_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW6duplex
	.cfi_endproc

	.section	.text._RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW7squeeze,"ax",@progbits
	.p2align	2
	.type	_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW7squeeze,@function
_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW7squeeze:
.Lfunc_begin16:
	.cfi_startproc
	stp	x30, x19, [sp, #-16]!
	.cfi_def_cfa_offset 16
	.cfi_offset w19, -8
	.cfi_offset w30, -16
	mov	x19, x0
	ldr	w8, [x0, #304]
	ldr	x0, [x0, #312]
	ldr	x1, [x19, #320]
	str	xzr, [x19, #304]
	tbnz	w8, #0, .LBB16_2
	mov	x0, x19
	bl	_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW6duplex
	ldp	x0, x1, [x19]
.LBB16_2:
	ldp	x30, x19, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w30
	ret
.Lfunc_end16:
	.size	_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW7squeeze, .Lfunc_end16-_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW7squeeze
	.cfi_endproc

	.section	.text._RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKj1e_E6extendB4_,"ax",@progbits
	.p2align	2
	.type	_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKj1e_E6extendB4_,@function
_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKj1e_E6extendB4_:
.Lfunc_begin17:
	.cfi_startproc
	cbz	x2, .LBB17_4
	ldr	x10, [x0]
	mov	w9, #30
	lsl	x8, x2, #4
	cmp	x10, #30
	add	x12, x0, x10, lsl #4
	csel	x11, x10, x9, hi
	add	x9, x1, #8
	add	x10, x10, #1
	neg	x11, x11
	add	x12, x12, #16
.LBB17_2:
	add	x13, x11, x10
	cmp	x13, #1
	b.eq	.LBB17_5
	ldp	x13, x14, [x9, #-8]
	subs	x8, x8, #16
	add	x9, x9, #16
	stp	x13, x14, [x12, #-8]
	add	x12, x12, #16
	str	x10, [x0]
	add	x10, x10, #1
	b.ne	.LBB17_2
.LBB17_4:
	mov	w0, #1
	ret
.LBB17_5:
	mov	w0, wzr
	ret
.Lfunc_end17:
	.size	_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKj1e_E6extendB4_, .Lfunc_end17-_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKj1e_E6extendB4_
	.cfi_endproc

	.section	.text._RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKj24_E6extendB4_,"ax",@progbits
	.p2align	2
	.type	_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKj24_E6extendB4_,@function
_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKj24_E6extendB4_:
.Lfunc_begin18:
	.cfi_startproc
	cbz	x2, .LBB18_4
	ldr	x10, [x0]
	mov	w9, #36
	lsl	x8, x2, #4
	cmp	x10, #36
	add	x12, x0, x10, lsl #4
	csel	x11, x10, x9, hi
	add	x9, x1, #8
	add	x10, x10, #1
	neg	x11, x11
	add	x12, x12, #16
.LBB18_2:
	add	x13, x11, x10
	cmp	x13, #1
	b.eq	.LBB18_5
	ldp	x13, x14, [x9, #-8]
	subs	x8, x8, #16
	add	x9, x9, #16
	stp	x13, x14, [x12, #-8]
	add	x12, x12, #16
	str	x10, [x0]
	add	x10, x10, #1
	b.ne	.LBB18_2
.LBB18_4:
	mov	w0, #1
	ret
.LBB18_5:
	mov	w0, wzr
	ret
.Lfunc_end18:
	.size	_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKj24_E6extendB4_, .Lfunc_end18-_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKj24_E6extendB4_
	.cfi_endproc

	.section	.text._RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKj3f_E6extendB4_,"ax",@progbits
	.p2align	2
	.type	_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKj3f_E6extendB4_,@function
_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKj3f_E6extendB4_:
.Lfunc_begin19:
	.cfi_startproc
	cbz	x2, .LBB19_4
	ldr	x10, [x0]
	mov	w9, #63
	lsl	x8, x2, #4
	cmp	x10, #63
	add	x12, x0, x10, lsl #4
	csel	x11, x10, x9, hi
	add	x9, x1, #8
	add	x10, x10, #1
	neg	x11, x11
	add	x12, x12, #16
.LBB19_2:
	add	x13, x11, x10
	cmp	x13, #1
	b.eq	.LBB19_5
	ldp	x13, x14, [x9, #-8]
	subs	x8, x8, #16
	add	x9, x9, #16
	stp	x13, x14, [x12, #-8]
	add	x12, x12, #16
	str	x10, [x0]
	add	x10, x10, #1
	b.ne	.LBB19_2
.LBB19_4:
	mov	w0, #1
	ret
.LBB19_5:
	mov	w0, wzr
	ret
.Lfunc_end19:
	.size	_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKj3f_E6extendB4_, .Lfunc_end19-_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKj3f_E6extendB4_
	.cfi_endproc

	.section	.text._RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKje6_E6extendB4_,"ax",@progbits
	.p2align	2
	.type	_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKje6_E6extendB4_,@function
_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKje6_E6extendB4_:
.Lfunc_begin20:
	.cfi_startproc
	cbz	x2, .LBB20_4
	ldr	x10, [x0]
	mov	w9, #230
	lsl	x8, x2, #4
	cmp	x10, #230
	add	x12, x0, x10, lsl #4
	csel	x11, x10, x9, hi
	add	x9, x1, #8
	add	x10, x10, #1
	neg	x11, x11
	add	x12, x12, #16
.LBB20_2:
	add	x13, x11, x10
	cmp	x13, #1
	b.eq	.LBB20_5
	ldp	x13, x14, [x9, #-8]
	subs	x8, x8, #16
	add	x9, x9, #16
	stp	x13, x14, [x12, #-8]
	add	x12, x12, #16
	str	x10, [x0]
	add	x10, x10, #1
	b.ne	.LBB20_2
.LBB20_4:
	mov	w0, #1
	ret
.LBB20_5:
	mov	w0, wzr
	ret
.Lfunc_end20:
	.size	_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKje6_E6extendB4_, .Lfunc_end20-_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKje6_E6extendB4_
	.cfi_endproc

	.section	.text._RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufyKje6_E6extendB4_,"ax",@progbits
	.p2align	2
	.type	_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufyKje6_E6extendB4_,@function
_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufyKje6_E6extendB4_:
.Lfunc_begin21:
	.cfi_startproc
	cbz	x2, .LBB21_4
	ldr	x9, [x0]
	mov	w10, #230
	lsl	x8, x2, #3
	cmp	x9, #230
	csel	x10, x9, x10, hi
	add	x9, x9, #1
	neg	x10, x10
.LBB21_2:
	add	x11, x10, x9
	cmp	x11, #1
	b.eq	.LBB21_5
	ldr	x11, [x1], #8
	subs	x8, x8, #8
	str	x11, [x0, x9, lsl #3]
	str	x9, [x0]
	add	x9, x9, #1
	b.ne	.LBB21_2
.LBB21_4:
	mov	w0, #1
	ret
.LBB21_5:
	mov	w0, wzr
	ret
.Lfunc_end21:
	.size	_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufyKje6_E6extendB4_, .Lfunc_end21-_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufyKje6_E6extendB4_
	.cfi_endproc

	.section	.text._RNvMNtCsemcRClSg8DH_9native_vm4whirNtB2_6BasisW4eval,"ax",@progbits
	.p2align	2
	.type	_RNvMNtCsemcRClSg8DH_9native_vm4whirNtB2_6BasisW4eval,@function
_RNvMNtCsemcRClSg8DH_9native_vm4whirNtB2_6BasisW4eval:
.Lfunc_begin22:
	.cfi_startproc
	sub	sp, sp, #144
	.cfi_def_cfa_offset 144
	stp	x29, x30, [sp, #48]
	stp	x28, x27, [sp, #64]
	stp	x26, x25, [sp, #80]
	stp	x24, x23, [sp, #96]
	stp	x22, x21, [sp, #112]
	stp	x20, x19, [sp, #128]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w24, -48
	.cfi_offset w25, -56
	.cfi_offset w26, -64
	.cfi_offset w27, -72
	.cfi_offset w28, -80
	.cfi_offset w30, -88
	.cfi_offset w29, -96
	.cfi_remember_state
	ldr	x23, [x1, #16]
	ldp	x19, x20, [x1]
	mov	x22, x1
	mov	x27, x0
	mov	w1, #4
	mov	x0, x23
	str	x3, [sp, #16]
	mov	x21, x2
	bl	_RNvMs2_NtCsemcRClSg8DH_9native_vm6layoutNtB5_7LayoutW9placement
	mov	x2, x0
	mov	x6, x1
	cbz	x20, .LBB22_2
	ldp	x25, x24, [x19]
	add	x28, x19, #16
	b	.LBB22_3
.LBB22_2:
	mov	x24, xzr
	mov	x25, xzr
	mov	x28, x19
.LBB22_3:
	ldp	x9, x8, [x22, #24]
	mov	w11, #8
	ldr	x7, [sp, #16]
	add	x0, sp, #24
	mov	x1, x2
	mov	x2, x6
	mov	x6, x21
	ldr	x10, [x8], #8
	add	x5, x9, #16
	cmp	x10, #37
	csel	x3, x8, x11, lo
	csel	x4, x10, xzr, lo
	bl	_RNvNtCsemcRClSg8DH_9native_vm5stack17ring_claim_weight
	ldr	x8, [sp, #24]
	cbz	x8, .LBB22_18
	ldp	x2, x3, [sp, #32]
	mov	x0, x25
	mov	x1, x24
	str	x27, [sp, #8]
	add	x29, x19, x20, lsl #4
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	ldr	x8, [x22, #40]
	mov	w10, #608
	mov	x24, x0
	mov	x25, x1
	ldr	x9, [x8], #8
	mul	x10, x9, x10
	cmp	x9, #161
	mov	w9, #8
	csel	x8, x8, x9, lo
	csel	x19, x10, xzr, lo
	cbz	x19, .LBB22_14
	add	x20, x8, #16
	b	.LBB22_7
.LBB22_6:
	subs	x19, x19, #608
	add	x20, x20, #608
	b.eq	.LBB22_14
.LBB22_7:
	ldur	x8, [x20, #-16]
	cmp	x8, #158
	b.hs	.LBB22_6
	mov	w10, #24
	add	x9, x23, #120
	madd	x8, x8, x10, x9
	ldr	x9, [x8]
	cbz	x9, .LBB22_6
	cmp	x28, x29
	b.eq	.LBB22_11
	ldp	x26, x27, [x28], #16
	b	.LBB22_12
.LBB22_11:
	mov	x26, xzr
	mov	x27, xzr
	mov	x28, x29
.LBB22_12:
	ldur	x9, [x20, #-8]
	ldp	x1, x2, [x8, #8]
	ldr	x5, [x23, #16]
	mov	w8, #8
	add	x0, sp, #24
	cmp	x9, #37
	ldr	x7, [sp, #16]
	mov	x6, x21
	csel	x3, x20, x8, lo
	csel	x4, x9, xzr, lo
	bl	_RNvNtCsemcRClSg8DH_9native_vm5stack13column_weight
	ldr	x8, [sp, #24]
	cbz	x8, .LBB22_19
	ldp	x2, x3, [sp, #32]
	mov	x0, x26
	mov	x1, x27
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	eor	x24, x0, x24
	eor	x25, x1, x25
	b	.LBB22_6
.LBB22_14:
	cmp	x28, x29
	b.eq	.LBB22_16
	ldp	x23, x26, [x28]
	b	.LBB22_17
.LBB22_16:
	mov	x23, xzr
	mov	x26, xzr
.LBB22_17:
	ldr	x8, [x22, #48]
	ldp	x27, x3, [sp, #8]
	mov	w10, #8
	mov	x2, x21
	ldr	x9, [x8], #8
	cmp	x9, #31
	csel	x0, x8, x10, lo
	csel	x1, x9, xzr, lo
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field7eq_eval
	mov	x2, x0
	mov	x3, x1
	mov	x0, x23
	mov	x1, x26
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	eor	x9, x0, x24
	eor	x10, x1, x25
	mov	w8, #1
	stp	x9, x10, [x27, #8]
.LBB22_18:
	str	x8, [x27]
	ldp	x20, x19, [sp, #128]
	ldp	x22, x21, [sp, #112]
	ldp	x24, x23, [sp, #96]
	ldp	x26, x25, [sp, #80]
	ldp	x28, x27, [sp, #64]
	ldp	x29, x30, [sp, #48]
	add	sp, sp, #144
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w25
	.cfi_restore w26
	.cfi_restore w27
	.cfi_restore w28
	.cfi_restore w30
	.cfi_restore w29
	ret
.LBB22_19:
	.cfi_restore_state
	ldr	x27, [sp, #8]
	b	.LBB22_18
.Lfunc_end22:
	.size	_RNvMNtCsemcRClSg8DH_9native_vm4whirNtB2_6BasisW4eval, .Lfunc_end22-_RNvMNtCsemcRClSg8DH_9native_vm4whirNtB2_6BasisW4eval
	.cfi_endproc

	.section	.text._RNvMNtCsemcRClSg8DH_9native_vm4wireNtB2_6Reader2le,"ax",@progbits
	.p2align	2
	.type	_RNvMNtCsemcRClSg8DH_9native_vm4wireNtB2_6Reader2le,@function
_RNvMNtCsemcRClSg8DH_9native_vm4wireNtB2_6Reader2le:
.Lfunc_begin23:
	.cfi_startproc
	ldp	x11, x9, [x0, #8]
	adds	x10, x9, x1
	cset	w12, hs
	cmp	x10, x11
	csinc	w11, w12, wzr, ls
	tbz	w11, #0, .LBB23_2
	mov	x0, xzr
	ret
.LBB23_2:
	ldr	x11, [x0]
	mov	x8, x1
	str	x10, [x0, #16]
	cmp	x1, #4
	add	x9, x11, x9
	add	x9, x9, x1
	ldurb	w11, [x9, #-2]
	ldurb	w12, [x9, #-1]
	ldurb	w13, [x9, #-4]
	lsl	x11, x11, #8
	orr	x11, x11, x12, lsl #16
	ldurb	w12, [x9, #-3]
	orr	x11, x11, x12
	orr	x1, x13, x11, lsl #8
	b.ne	.LBB23_4
	mov	w0, #1
	ret
.LBB23_4:
	ldurb	w10, [x9, #-5]
	cmp	x8, #5
	orr	x1, x10, x1, lsl #8
	b.ne	.LBB23_6
	mov	w0, #1
	ret
.LBB23_6:
	ldurb	w10, [x9, #-6]
	cmp	x8, #6
	orr	x1, x10, x1, lsl #8
	b.ne	.LBB23_8
	mov	w0, #1
	ret
.LBB23_8:
	ldurb	w10, [x9, #-7]
	cmp	x8, #7
	orr	x1, x10, x1, lsl #8
	b.ne	.LBB23_10
	mov	w0, #1
	ret
.LBB23_10:
	ldurb	w8, [x9, #-8]
	mov	w0, #1
	orr	x1, x8, x1, lsl #8
	ret
.Lfunc_end23:
	.size	_RNvMNtCsemcRClSg8DH_9native_vm4wireNtB2_6Reader2le, .Lfunc_end23-_RNvMNtCsemcRClSg8DH_9native_vm4wireNtB2_6Reader2le
	.cfi_endproc

	.section	.text._RNvMNtCsemcRClSg8DH_9native_vm4wireNtB2_6Reader5words,"ax",@progbits
	.p2align	2
	.type	_RNvMNtCsemcRClSg8DH_9native_vm4wireNtB2_6Reader5words,@function
_RNvMNtCsemcRClSg8DH_9native_vm4wireNtB2_6Reader5words:
.Lfunc_begin24:
	.cfi_startproc
	stp	x30, x21, [sp, #-32]!
	.cfi_def_cfa_offset 32
	stp	x20, x19, [sp, #16]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w30, -32
	.cfi_remember_state
	ldp	x9, x8, [x0, #8]
	lsl	x21, x2, #3
	adds	x8, x8, x21
	cset	w10, hs
	cmp	x8, x9
	csinc	w8, w10, wzr, ls
	tbz	w8, #0, .LBB24_2
.LBB24_1:
	mov	w0, wzr
	ldp	x20, x19, [sp, #16]
	ldp	x30, x21, [sp], #32
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w30
	ret
.LBB24_2:
	.cfi_restore_state
	cbz	x2, .LBB24_6
	mov	x19, x0
	mov	x20, x1
.LBB24_4:
	mov	x0, x19
	mov	w1, #8
	bl	_RNvMNtCsemcRClSg8DH_9native_vm4wireNtB2_6Reader2le
	cmp	x0, #1
	b.ne	.LBB24_1
	subs	x21, x21, #8
	str	x1, [x20], #8
	b.ne	.LBB24_4
.LBB24_6:
	mov	w0, #1
	ldp	x20, x19, [sp, #16]
	ldp	x30, x21, [sp], #32
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w30
	ret
.Lfunc_end24:
	.size	_RNvMNtCsemcRClSg8DH_9native_vm4wireNtB2_6Reader5words, .Lfunc_end24-_RNvMNtCsemcRClSg8DH_9native_vm4wireNtB2_6Reader5words
	.cfi_endproc

	.section	.text._RNvMNtCsemcRClSg8DH_9native_vm4wireNtB2_6Reader6digest,"ax",@progbits
	.p2align	2
	.type	_RNvMNtCsemcRClSg8DH_9native_vm4wireNtB2_6Reader6digest,@function
_RNvMNtCsemcRClSg8DH_9native_vm4wireNtB2_6Reader6digest:
.Lfunc_begin25:
	.cfi_startproc
	stp	x30, x23, [sp, #-48]!
	.cfi_def_cfa_offset 48
	stp	x22, x21, [sp, #16]
	stp	x20, x19, [sp, #32]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w30, -48
	.cfi_remember_state
	mov	x20, x1
	mov	x19, x0
	mov	x0, x1
	mov	w1, #8
	bl	_RNvMNtCsemcRClSg8DH_9native_vm4wireNtB2_6Reader2le
	cmp	x0, #1
	b.ne	.LBB25_5
	mov	x22, x1
	mov	x0, x20
	mov	w1, #8
	bl	_RNvMNtCsemcRClSg8DH_9native_vm4wireNtB2_6Reader2le
	cmp	x0, #1
	b.ne	.LBB25_5
	mov	x23, x1
	mov	x0, x20
	mov	w1, #8
	bl	_RNvMNtCsemcRClSg8DH_9native_vm4wireNtB2_6Reader2le
	cmp	x0, #1
	b.ne	.LBB25_5
	mov	x21, x1
	mov	x0, x20
	mov	w1, #8
	bl	_RNvMNtCsemcRClSg8DH_9native_vm4wireNtB2_6Reader2le
	cmp	x0, #1
	b.ne	.LBB25_5
	mov	w8, #1
	stp	x22, x23, [x19, #8]
	stp	x21, x1, [x19, #24]
	str	x8, [x19]
	ldp	x20, x19, [sp, #32]
	ldp	x22, x21, [sp, #16]
	ldp	x30, x23, [sp], #48
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w30
	ret
.LBB25_5:
	.cfi_restore_state
	str	xzr, [x19]
	ldp	x20, x19, [sp, #32]
	ldp	x22, x21, [sp, #16]
	ldp	x30, x23, [sp], #48
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w30
	ret
.Lfunc_end25:
	.size	_RNvMNtCsemcRClSg8DH_9native_vm4wireNtB2_6Reader6digest, .Lfunc_end25-_RNvMNtCsemcRClSg8DH_9native_vm4wireNtB2_6Reader6digest
	.cfi_endproc

	.section	.text._RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul,"ax",@progbits
	.p2align	2
	.type	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul,@function
_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul:
.Lfunc_begin26:
	.cfi_startproc
	stp	x29, x30, [sp, #-96]!
	.cfi_def_cfa_offset 96
	stp	x28, x27, [sp, #16]
	stp	x26, x25, [sp, #32]
	stp	x24, x23, [sp, #48]
	stp	x22, x21, [sp, #64]
	stp	x20, x19, [sp, #80]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w24, -48
	.cfi_offset w25, -56
	.cfi_offset w26, -64
	.cfi_offset w27, -72
	.cfi_offset w28, -80
	.cfi_offset w30, -88
	.cfi_offset w29, -96
	sub	sp, sp, #496
	.cfi_def_cfa_offset 592
	and	x8, x2, #0x1111111111111111
	and	x9, x0, #0x1111111111111111
	and	x11, x2, #0x8888888888888888
	and	x13, x2, #0x4444444444444444
	and	x15, x2, #0x2222222222222222
	mul	x17, x8, x9
	and	x10, x0, #0x2222222222222222
	and	x12, x0, #0x4444444444444444
	and	x14, x0, #0x8888888888888888
	mul	x6, x15, x9
	mul	x21, x13, x9
	mul	x9, x11, x9
	mul	x18, x11, x10
	mul	x19, x11, x12
	str	x9, [sp, #488]
	mul	x26, x11, x14
	mul	x11, x13, x10
	mul	x9, x15, x12
	mul	x7, x8, x10
	mul	x25, x8, x12
	stp	x9, x11, [sp, #472]
	rbit	x9, x0
	mul	x8, x8, x14
	mul	x22, x15, x10
	rbit	x10, x2
	eor	x2, x3, x2
	eor	x30, x25, x26
	mul	x4, x13, x12
	and	x11, x10, #0x8888888888888888
	and	x12, x9, #0x4444444444444444
	str	x8, [sp, #464]
	and	x8, x9, #0x2222222222222222
	mul	x20, x13, x14
	and	x13, x10, #0x4444444444444444
	eor	x28, x21, x22
	mul	x5, x15, x14
	mul	x15, x11, x8
	mul	x14, x13, x12
	stp	x14, x15, [sp, #448]
	and	x14, x10, #0x1111111111111111
	and	x10, x10, #0x2222222222222222
	mul	x15, x14, x8
	str	x15, [sp, #440]
	and	x15, x9, #0x8888888888888888
	and	x9, x9, #0x1111111111111111
	mul	x16, x13, x15
	str	x16, [sp, #432]
	mul	x16, x13, x9
	mul	x13, x13, x8
	mul	x8, x10, x8
	stp	x13, x16, [sp, #416]
	mul	x16, x14, x9
	and	x13, x3, #0x1111111111111111
	str	x8, [sp, #400]
	mul	x8, x10, x15
	str	x8, [sp, #320]
	mul	x8, x10, x9
	str	x8, [sp, #368]
	mul	x8, x10, x12
	mul	x10, x11, x12
	str	x8, [sp, #408]
	mul	x8, x14, x12
	str	x8, [sp, #392]
	mul	x8, x11, x9
	and	x9, x3, #0x4444444444444444
	str	x8, [sp, #384]
	mul	x8, x11, x15
	stp	x8, x10, [sp, #352]
	mul	x8, x14, x15
	str	x8, [sp, #376]
	and	x8, x1, #0x4444444444444444
	mul	x10, x9, x8
	str	x10, [sp, #336]
	and	x10, x1, #0x8888888888888888
	mul	x11, x9, x10
	str	x11, [sp, #344]
	and	x11, x1, #0x1111111111111111
	mul	x12, x9, x11
	str	x12, [sp, #328]
	and	x12, x1, #0x2222222222222222
	mul	x9, x9, x12
	mul	x14, x13, x12
	str	x9, [sp, #312]
	and	x9, x3, #0x8888888888888888
	mul	x15, x9, x12
	str	x14, [sp, #288]
	and	x14, x3, #0x2222222222222222
	mul	x12, x14, x12
	str	x12, [sp, #296]
	mul	x12, x14, x10
	stp	x12, x15, [sp, #232]
	mul	x12, x14, x8
	mul	x15, x14, x11
	str	x12, [sp, #304]
	mul	x12, x9, x8
	mul	x8, x13, x8
	stp	x12, x15, [sp, #256]
	str	x8, [sp, #280]
	mul	x8, x13, x11
	str	x8, [sp, #216]
	mul	x8, x9, x11
	rbit	x11, x3
	and	x3, x2, #0x1111111111111111
	and	x12, x11, #0x4444444444444444
	str	x8, [sp, #272]
	mul	x8, x9, x10
	rbit	x9, x1
	eor	x1, x1, x0
	str	x8, [sp, #248]
	mul	x8, x13, x10
	and	x10, x9, #0x4444444444444444
	and	x13, x9, #0x1111111111111111
	mul	x14, x12, x13
	str	x8, [sp, #224]
	mul	x8, x12, x10
	str	x8, [sp, #208]
	and	x8, x9, #0x8888888888888888
	mul	x15, x12, x8
	stp	x15, x14, [sp, #192]
	and	x14, x9, #0x2222222222222222
	mul	x9, x12, x14
	and	x12, x11, #0x8888888888888888
	mul	x27, x12, x8
	str	x9, [sp, #184]
	mul	x9, x12, x14
	str	x9, [sp, #160]
	and	x9, x11, #0x1111111111111111
	and	x11, x11, #0x2222222222222222
	mul	x15, x9, x14
	mul	x14, x11, x14
	mul	x24, x9, x8
	str	x14, [sp, #168]
	mul	x14, x11, x8
	str	x14, [sp, #128]
	mul	x14, x11, x13
	mul	x11, x11, x10
	str	x11, [sp, #176]
	mul	x11, x12, x10
	mul	x10, x9, x10
	stp	x11, x14, [sp, #112]
	rbit	x11, x2
	str	x10, [sp, #136]
	mul	x10, x9, x13
	and	x9, x11, #0x4444444444444444
	str	x10, [sp, #104]
	mul	x10, x12, x13
	stp	x10, x15, [sp, #144]
	rbit	x10, x1
	and	x15, x11, #0x1111111111111111
	and	x8, x10, #0x4444444444444444
	and	x12, x10, #0x8888888888888888
	mul	x14, x9, x8
	mul	x13, x9, x12
	mul	x29, x15, x8
	mul	x22, x15, x12
	stp	x13, x14, [sp, #88]
	and	x13, x10, #0x1111111111111111
	and	x10, x10, #0x2222222222222222
	mul	x14, x9, x13
	mul	x9, x9, x10
	mul	x23, x15, x13
	stp	x9, x14, [sp, #72]
	and	x9, x11, #0x8888888888888888
	and	x11, x11, #0x2222222222222222
	mul	x14, x9, x10
	mul	x26, x9, x13
	mul	x21, x9, x12
	str	x14, [sp, #40]
	mul	x14, x15, x10
	mul	x10, x11, x10
	stp	x10, x14, [sp, #48]
	mul	x10, x11, x12
	ldr	x12, [sp, #376]
	str	x10, [sp, #32]
	mul	x10, x11, x13
	eor	x13, x28, x30
	and	x30, x2, #0x2222222222222222
	str	x10, [sp, #24]
	mul	x10, x11, x8
	eor	x11, x4, x5
	str	x10, [sp, #64]
	mul	x10, x9, x8
	eor	x8, x6, x7
	str	x10, [sp, #16]
	eor	x10, x17, x18
	and	x17, x2, #0x8888888888888888
	eor	x4, x10, x11
	eor	x10, x19, x20
	and	x18, x1, #0x1111111111111111
	eor	x0, x8, x10
	ldp	x10, x8, [sp, #480]
	and	x0, x0, #0x2222222222222222
	mul	x19, x3, x18
	eor	x11, x8, x10
	ldp	x10, x8, [sp, #464]
	eor	x14, x8, x10
	ldp	x8, x9, [sp, #448]
	eor	x11, x11, x14
	eor	x10, x16, x9
	ldr	x16, [sp, #320]
	stp	x13, x11, [sp, #480]
	and	x13, x1, #0x2222222222222222
	eor	x8, x8, x16
	and	x16, x1, #0x4444444444444444
	and	x1, x1, #0x8888888888888888
	eor	x14, x10, x8
	ldp	x8, x11, [sp, #432]
	ldr	x10, [sp, #368]
	and	x14, x14, #0x1111111111111111
	mul	x7, x17, x13
	eor	x10, x10, x11
	ldr	x11, [sp, #360]
	mul	x5, x30, x1
	eor	x11, x11, x8
	ldr	x8, [sp, #424]
	eor	x9, x10, x11
	ldr	x10, [sp, #400]
	ldr	x11, [sp, #352]
	and	x9, x9, #0x2222222222222222
	eor	x10, x8, x10
	ldr	x8, [sp, #392]
	orr	x14, x14, x9
	eor	x11, x8, x11
	ldr	x8, [sp, #416]
	eor	x11, x10, x11
	ldr	x10, [sp, #384]
	and	x9, x11, #0x4444444444444444
	ldr	x11, [sp, #216]
	eor	x10, x10, x8
	ldr	x8, [sp, #408]
	eor	x8, x8, x12
	eor	x10, x10, x8
	and	x8, x2, #0x4444444444444444
	and	x2, x4, #0x1111111111111111
	and	x10, x10, #0x8888888888888888
	mul	x4, x30, x18
	orr	x10, x9, x10
	ldr	x9, [sp, #240]
	orr	x20, x14, x10
	mul	x6, x8, x16
	eor	x12, x11, x9
	ldr	x9, [sp, #336]
	ldr	x11, [sp, #232]
	eor	x9, x9, x11
	orr	x11, x2, x0
	mul	x0, x3, x13
	str	x11, [sp, #472]
	ldp	x11, x10, [sp, #256]
	eor	x28, x12, x9
	ldr	x9, [sp, #288]
	eor	x9, x10, x9
	ldr	x10, [sp, #344]
	eor	x12, x11, x10
	ldr	x10, [sp, #296]
	ldr	x11, [sp, #248]
	eor	x25, x9, x12
	ldr	x9, [sp, #328]
	eor	x9, x9, x10
	ldr	x10, [sp, #280]
	eor	x2, x10, x11
	ldr	x10, [sp, #272]
	eor	x9, x9, x2
	str	x9, [sp, #464]
	ldp	x9, x11, [sp, #304]
	eor	x15, x10, x11
	ldr	x10, [sp, #224]
	eor	x12, x9, x10
	ldp	x10, x2, [sp, #104]
	ldr	x9, [sp, #160]
	eor	x12, x15, x12
	eor	x14, x10, x9
	ldr	x9, [sp, #208]
	ldr	x10, [sp, #128]
	eor	x11, x9, x10
	ldr	x9, [sp, #152]
	ldr	x10, [sp, #120]
	eor	x11, x14, x11
	ldr	x14, [sp, #168]
	eor	x10, x10, x9
	ldr	x9, [sp, #192]
	and	x11, x11, #0x1111111111111111
	eor	x9, x2, x9
	mul	x2, x8, x1
	eor	x9, x10, x9
	ldr	x10, [sp, #200]
	eor	x10, x10, x14
	ldp	x14, x15, [sp, #136]
	eor	x14, x14, x27
	mul	x27, x8, x18
	eor	x10, x10, x14
	ldr	x14, [sp, #184]
	mul	x18, x17, x18
	eor	x14, x15, x14
	ldr	x15, [sp, #176]
	eor	x15, x15, x24
	mul	x24, x8, x13
	and	x8, x9, #0x2222222222222222
	eor	x14, x14, x15
	and	x9, x10, #0x4444444444444444
	orr	x8, x11, x8
	and	x10, x14, #0x8888888888888888
	eor	x11, x6, x5
	mul	x15, x17, x16
	orr	x9, x9, x10
	ldp	x6, x5, [sp, #16]
	mul	x10, x30, x13
	eor	x13, x4, x0
	ldr	x0, [sp, #96]
	ldp	x4, x14, [sp, #32]
	orr	x8, x8, x9
	eor	x9, x19, x7
	mul	x19, x30, x16
	rbit	x8, x8
	eor	x15, x15, x2
	rbit	x2, x20
	eor	x9, x9, x11
	eor	x0, x0, x4
	ldp	x7, x4, [sp, #48]
	eor	x14, x23, x14
	mul	x16, x3, x16
	eor	x11, x13, x15
	eor	x14, x14, x0
	eor	x10, x27, x10
	and	x9, x9, #0x1111111111111111
	eor	x4, x5, x4
	ldr	x5, [sp, #88]
	and	x14, x14, #0x1111111111111111
	mul	x17, x17, x1
	and	x11, x11, #0x2222222222222222
	eor	x5, x6, x5
	ldr	x6, [sp, #80]
	orr	x9, x9, x11
	eor	x0, x4, x5
	mul	x15, x3, x1
	lsr	x1, x8, #63
	eor	x6, x6, x7
	eor	x7, x29, x21
	and	x0, x0, #0x2222222222222222
	eor	x4, x6, x7
	ldp	x6, x5, [sp, #64]
	and	x4, x4, #0x4444444444444444
	orr	x14, x14, x0
	eor	x16, x16, x17
	eor	x10, x10, x16
	and	x3, x28, #0x1111111111111111
	eor	x5, x26, x5
	eor	x6, x6, x22
	eor	x15, x19, x15
	eor	x5, x5, x6
	and	x10, x10, #0x4444444444444444
	and	x5, x5, #0x8888888888888888
	orr	x0, x4, x5
	and	x4, x25, #0x2222222222222222
	orr	x13, x14, x0
	eor	x14, x2, x8
	eor	x0, x8, x2
	rbit	x13, x13
	bfxil	x8, x12, #63, #1
	lsr	x17, x0, #62
	eor	x13, x14, x13
	eor	x16, x17, x0, lsr #61
	eor	x8, x8, x13, lsr #1
	eor	x13, x18, x24
	eor	x13, x13, x15
	ldp	x14, x2, [sp, #480]
	eor	x15, x1, x8, lsr #61
	and	x13, x13, #0x8888888888888888
	eor	x11, x16, x0, lsr #1
	orr	x10, x10, x13
	ldr	x13, [sp, #464]
	eor	x15, x15, x8, lsr #60
	orr	x9, x9, x10
	and	x10, x12, #0x8888888888888888
	and	x13, x13, #0x4444444444444444
	lsl	x12, x11, #3
	and	x14, x14, #0x4444444444444444
	eor	x8, x15, x8
	and	x2, x2, #0x8888888888888888
	orr	x15, x3, x4
	eor	x9, x9, x8, lsl #3
	orr	x10, x13, x10
	ldr	x13, [sp, #472]
	orr	x14, x14, x2
	orr	x10, x15, x10
	eor	x12, x12, x11, lsl #1
	eor	x9, x9, x8, lsl #4
	orr	x13, x13, x14
	eor	x14, x8, x10
	eor	x12, x12, x11, lsl #4
	eor	x10, x13, x10
	eor	x9, x9, x14, lsl #1
	eor	x11, x10, x11
	eor	x8, x10, x8
	eor	x0, x12, x11
	eor	x1, x9, x8
	add	sp, sp, #496
	.cfi_def_cfa_offset 96
	ldp	x20, x19, [sp, #80]
	ldp	x22, x21, [sp, #64]
	ldp	x24, x23, [sp, #48]
	ldp	x26, x25, [sp, #32]
	ldp	x28, x27, [sp, #16]
	ldp	x29, x30, [sp], #96
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w25
	.cfi_restore w26
	.cfi_restore w27
	.cfi_restore w28
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end26:
	.size	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul, .Lfunc_end26-_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	.cfi_endproc

	.section	.text._RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW7sq_iter,"ax",@progbits
	.p2align	2
	.type	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW7sq_iter,@function
_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW7sq_iter:
.Lfunc_begin27:
	.cfi_startproc
	stp	x30, x19, [sp, #-16]!
	.cfi_def_cfa_offset 16
	.cfi_offset w19, -8
	.cfi_offset w30, -16
	mov	x3, x2
	mov	x19, x0
	mov	x0, x1
	cbz	x19, .LBB27_2
.LBB27_1:
	mov	x1, x3
	mov	x2, x0
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	subs	x19, x19, #1
	mov	x3, x1
	b.ne	.LBB27_1
.LBB27_2:
	mov	x1, x3
	ldp	x30, x19, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w30
	ret
.Lfunc_end27:
	.size	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW7sq_iter, .Lfunc_end27-_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW7sq_iter
	.cfi_endproc

	.section	.text._RNvMNtCsemcRClSg8DH_9native_vm5inputNtB2_7Decoded11phase_count,"ax",@progbits
	.p2align	2
	.type	_RNvMNtCsemcRClSg8DH_9native_vm5inputNtB2_7Decoded11phase_count,@function
_RNvMNtCsemcRClSg8DH_9native_vm5inputNtB2_7Decoded11phase_count:
.Lfunc_begin28:
	.cfi_startproc
	ldp	x9, x8, [x0, #8]
	lsr	x8, x8, #3
	orr	x8, x8, #0x1
	cmp	x8, x9
	b.hs	.LBB28_2
	ldr	x9, [x0]
	ldr	x0, [x9, x8, lsl #3]
	ret
.LBB28_2:
	mov	x0, xzr
	ret
.Lfunc_end28:
	.size	_RNvMNtCsemcRClSg8DH_9native_vm5inputNtB2_7Decoded11phase_count, .Lfunc_end28-_RNvMNtCsemcRClSg8DH_9native_vm5inputNtB2_7Decoded11phase_count
	.cfi_endproc

	.section	.text._RNvMNtCsemcRClSg8DH_9native_vm5inputNtB2_7Decoded14stream_element,"ax",@progbits
	.p2align	2
	.type	_RNvMNtCsemcRClSg8DH_9native_vm5inputNtB2_7Decoded14stream_element,@function
_RNvMNtCsemcRClSg8DH_9native_vm5inputNtB2_7Decoded14stream_element:
.Lfunc_begin29:
	.cfi_startproc
	cbz	x2, .LBB29_3
	ldr	x8, [x1]
	cmp	x3, x8
	b.hs	.LBB29_3
	lsl	x8, x3, #1
	add	x9, x8, #3
	cmp	x9, x2
	ccmn	x8, #4, #2, ls
	b.ls	.LBB29_4
.LBB29_3:
	str	xzr, [x0]
	ret
.LBB29_4:
	add	x8, x1, x8, lsl #3
	ldp	x9, x8, [x8, #8]
	stp	x9, x8, [x0, #8]
	mov	w8, #1
	str	x8, [x0]
	ret
.Lfunc_end29:
	.size	_RNvMNtCsemcRClSg8DH_9native_vm5inputNtB2_7Decoded14stream_element, .Lfunc_end29-_RNvMNtCsemcRClSg8DH_9native_vm5inputNtB2_7Decoded14stream_element
	.cfi_endproc

	.section	.text._RNvMNtCsemcRClSg8DH_9native_vm5inputNtB2_7Decoded5phase,"ax",@progbits
	.p2align	2
	.type	_RNvMNtCsemcRClSg8DH_9native_vm5inputNtB2_7Decoded5phase,@function
_RNvMNtCsemcRClSg8DH_9native_vm5inputNtB2_7Decoded5phase:
.Lfunc_begin30:
	.cfi_startproc
	str	x30, [sp, #-32]!
	.cfi_def_cfa_offset 32
	stp	x20, x19, [sp, #16]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w30, -32
	.cfi_remember_state
	mov	x20, x1
	mov	x19, x0
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5inputNtB2_7Decoded11phase_count
	cmp	x20, x0
	ccmp	x20, #7, #2, lo
	b.ls	.LBB30_2
	mov	x0, xzr
	ldp	x20, x19, [sp, #16]
	ldr	x30, [sp], #32
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w30
	ret
.LBB30_2:
	.cfi_restore_state
	.cfi_remember_state
	ldp	x9, x8, [x19, #8]
	mov	w10, #49411
	lsr	x8, x8, #3
	orr	x8, x8, #0x1
	madd	x8, x20, x10, x8
	mov	w10, #49412
	add	x10, x8, x10
	cmp	x10, x9
	b.ls	.LBB30_4
	mov	x0, xzr
	ldp	x20, x19, [sp, #16]
	ldr	x30, [sp], #32
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w30
	ret
.LBB30_4:
	.cfi_restore_state
	ldr	x9, [x19]
	add	x8, x8, #1
	add	x0, x9, x8, lsl #3
	ldp	x20, x19, [sp, #16]
	ldr	x30, [sp], #32
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w30
	ret
.Lfunc_end30:
	.size	_RNvMNtCsemcRClSg8DH_9native_vm5inputNtB2_7Decoded5phase, .Lfunc_end30-_RNvMNtCsemcRClSg8DH_9native_vm5inputNtB2_7Decoded5phase
	.cfi_endproc

	.section	.text._RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState11next_scalar,"ax",@progbits
	.p2align	2
	.type	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState11next_scalar,@function
_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState11next_scalar:
.Lfunc_begin31:
	.cfi_startproc
	sub	sp, sp, #64
	.cfi_def_cfa_offset 64
	stp	x30, x21, [sp, #32]
	stp	x20, x19, [sp, #48]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w30, -32
	.cfi_remember_state
	ldr	x8, [x1, #304]
	mov	x19, x0
	cbz	x8, .LBB31_3
	mov	x8, xzr
.LBB31_2:
	str	x8, [x19]
	ldp	x20, x19, [sp, #48]
	ldp	x30, x21, [sp, #32]
	add	sp, sp, #64
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w30
	ret
.LBB31_3:
	.cfi_restore_state
	ldp	x8, x2, [x1, #328]
	mov	x21, x1
	ldr	x20, [x1, #352]
	add	x0, sp, #8
	mov	x1, x8
	mov	x3, x20
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5inputNtB2_7Decoded14stream_element
	ldr	x8, [sp, #8]
	cbz	x8, .LBB31_2
	ldp	x9, x10, [sp, #16]
	add	x8, x20, #1
	str	x8, [x21, #352]
	mov	w8, #1
	stp	x9, x10, [x19, #8]
	str	x8, [x19]
	ldp	x20, x19, [sp, #48]
	ldp	x30, x21, [sp, #32]
	add	sp, sp, #64
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w30
	ret
.Lfunc_end31:
	.size	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState11next_scalar, .Lfunc_end31-_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState11next_scalar
	.cfi_endproc

	.section	.text._RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState11read_scalar,"ax",@progbits
	.p2align	2
	.type	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState11read_scalar,@function
_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState11read_scalar:
.Lfunc_begin32:
	.cfi_startproc
	sub	sp, sp, #80
	.cfi_def_cfa_offset 80
	str	x30, [sp, #32]
	stp	x22, x21, [sp, #48]
	stp	x20, x19, [sp, #64]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w30, -48
	.cfi_remember_state
	mov	x19, x0
	add	x0, sp, #8
	mov	x20, x1
	bl	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState11next_scalar
	ldr	x8, [sp, #8]
	cbz	x8, .LBB32_2
	ldp	x21, x22, [sp, #16]
	mov	x0, x20
	mov	w3, #1
	mov	w20, #1
	mov	x1, x21
	mov	x2, x22
	bl	_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW6absorb
	stp	x21, x22, [x19, #8]
	str	x20, [x19]
	ldp	x20, x19, [sp, #64]
	ldp	x22, x21, [sp, #48]
	ldr	x30, [sp, #32]
	add	sp, sp, #80
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w30
	ret
.LBB32_2:
	.cfi_restore_state
	str	xzr, [x19]
	ldp	x20, x19, [sp, #64]
	ldp	x22, x21, [sp, #48]
	ldr	x30, [sp, #32]
	add	sp, sp, #80
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w30
	ret
.Lfunc_end32:
	.size	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState11read_scalar, .Lfunc_end32-_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState11read_scalar
	.cfi_endproc

	.section	.text._RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState12read_scalars,"ax",@progbits
	.p2align	2
	.type	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState12read_scalars,@function
_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState12read_scalars:
.Lfunc_begin33:
	.cfi_startproc
	cbz	x2, .LBB33_5
	sub	sp, sp, #64
	.cfi_def_cfa_offset 64
	stp	x30, x21, [sp, #32]
	stp	x20, x19, [sp, #48]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w30, -32
	.cfi_remember_state
	add	x21, x1, x2, lsl #4
	mov	x19, x1
	mov	x20, x0
.LBB33_2:
	add	x0, sp, #8
	mov	x1, x20
	bl	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState11read_scalar
	ldr	x8, [sp, #8]
	cbz	x8, .LBB33_6
	ldp	x8, x9, [sp, #16]
	stp	x8, x9, [x19], #16
	cmp	x19, x21
	b.ne	.LBB33_2
	mov	w0, #1
	ldp	x20, x19, [sp, #48]
	ldp	x30, x21, [sp, #32]
	add	sp, sp, #64
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w30
	ret
.LBB33_5:
	mov	w0, #1
	ret
.LBB33_6:
	.cfi_restore_state
	mov	w0, wzr
	ldp	x20, x19, [sp, #48]
	ldp	x30, x21, [sp, #32]
	add	sp, sp, #64
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w30
	ret
.Lfunc_end33:
	.size	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState12read_scalars, .Lfunc_end33-_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState12read_scalars
	.cfi_endproc

	.section	.text._RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState14query_openings,"ax",@progbits
	.p2align	2
	.type	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState14query_openings,@function
_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState14query_openings:
.Lfunc_begin34:
	.cfi_startproc
	sub	sp, sp, #96
	.cfi_def_cfa_offset 96
	str	x30, [sp, #32]
	stp	x24, x23, [sp, #48]
	stp	x22, x21, [sp, #64]
	stp	x20, x19, [sp, #80]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w24, -48
	.cfi_offset w30, -64
	.cfi_remember_state
	ldr	x8, [x1, #752]
	mov	x19, x0
	cmp	x8, #8
	b.hi	.LBB34_5
	mov	x24, x2
	cmp	x2, x8
	b.hs	.LBB34_5
	ldr	x21, [x1, #360]
	mov	x20, x1
	add	x0, x1, #328
	mov	x22, x4
	mov	x23, x3
	mov	x1, x21
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5inputNtB2_7Decoded5phase
	cbz	x0, .LBB34_5
	mov	w8, #48
	mov	x6, x0
	mov	x0, sp
	madd	x8, x24, x8, x20
	mov	x4, x23
	mov	x5, x22
	ldp	x2, x3, [x8, #400]
	add	x1, x8, #368
	bl	_RNvNtCsemcRClSg8DH_9native_vm10transcript10open_phase
	ldr	x8, [sp]
	cbz	x8, .LBB34_5
	ldp	x8, x9, [sp]
	stp	x8, x9, [x19]
	ldp	x8, x10, [sp, #16]
	stp	x8, x10, [x19, #16]
	add	x8, x21, #1
	str	x8, [x20, #360]
	ldp	x20, x19, [sp, #80]
	ldr	x30, [sp, #32]
	ldp	x22, x21, [sp, #64]
	ldp	x24, x23, [sp, #48]
	add	sp, sp, #96
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w30
	ret
.LBB34_5:
	.cfi_restore_state
	str	xzr, [x19]
	ldp	x20, x19, [sp, #80]
	ldr	x30, [sp, #32]
	ldp	x22, x21, [sp, #64]
	ldp	x24, x23, [sp, #48]
	add	sp, sp, #96
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w30
	ret
.Lfunc_end34:
	.size	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState14query_openings, .Lfunc_end34-_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState14query_openings
	.cfi_endproc

	.section	.text._RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState15read_commitment,"ax",@progbits
	.p2align	2
	.type	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState15read_commitment,@function
_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState15read_commitment:
.Lfunc_begin35:
	.cfi_startproc
	sub	sp, sp, #80
	.cfi_def_cfa_offset 80
	stp	x30, x23, [sp, #32]
	stp	x22, x21, [sp, #48]
	stp	x20, x19, [sp, #64]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w30, -48
	.cfi_remember_state
	mov	x19, x0
	mov	x21, x1
	add	x0, sp, #8
	mov	x1, x19
	mov	x20, x2
	bl	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState11read_scalar
	ldr	x8, [sp, #8]
	cbz	x8, .LBB35_4
	ldp	x23, x22, [sp, #16]
	add	x0, sp, #8
	mov	x1, x19
	bl	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState11read_scalar
	ldr	w8, [sp, #8]
	tbz	w8, #0, .LBB35_4
	ldr	x8, [x19, #752]
	cmp	x8, #8
	b.hs	.LBB35_4
	mov	w9, #48
	mov	w0, #1
	madd	x8, x8, x9, x19
	ldp	x9, x10, [sp, #16]
	stp	x23, x22, [x8, #368]
	stp	x9, x10, [x8, #384]
	ldr	x9, [x19, #752]
	stp	x21, x20, [x8, #400]
	add	x8, x9, #1
	str	x8, [x19, #752]
	ldp	x20, x19, [sp, #64]
	ldp	x22, x21, [sp, #48]
	ldp	x30, x23, [sp, #32]
	add	sp, sp, #80
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w30
	ret
.LBB35_4:
	.cfi_restore_state
	mov	w0, wzr
	ldp	x20, x19, [sp, #64]
	ldp	x22, x21, [sp, #48]
	ldp	x30, x23, [sp, #32]
	add	sp, sp, #80
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w30
	ret
.Lfunc_end35:
	.size	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState15read_commitment, .Lfunc_end35-_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState15read_commitment
	.cfi_endproc

	.section	.text._RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState17sample_challenges,"ax",@progbits
	.p2align	2
	.type	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState17sample_challenges,@function
_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState17sample_challenges:
.Lfunc_begin36:
	.cfi_startproc
	cbz	x2, .LBB36_4
	stp	x30, x21, [sp, #-32]!
	.cfi_def_cfa_offset 32
	stp	x20, x19, [sp, #16]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w30, -32
	add	x21, x1, x2, lsl #4
	mov	x19, x1
	mov	x20, x0
.LBB36_2:
	mov	x0, x20
	bl	_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW7squeeze
	stp	x0, x1, [x19], #16
	cmp	x19, x21
	b.ne	.LBB36_2
	ldp	x20, x19, [sp, #16]
	ldp	x30, x21, [sp], #32
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w30
.LBB36_4:
	ret
.Lfunc_end36:
	.size	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState17sample_challenges, .Lfunc_end36-_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState17sample_challenges
	.cfi_endproc

	.section	.text._RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState19sumcheck_round_poly,"ax",@progbits
	.p2align	2
	.type	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState19sumcheck_round_poly,@function
_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState19sumcheck_round_poly:
.Lfunc_begin37:
	.cfi_startproc
	sub	sp, sp, #112
	.cfi_def_cfa_offset 112
	stp	x30, x27, [sp, #32]
	stp	x26, x25, [sp, #48]
	stp	x24, x23, [sp, #64]
	stp	x22, x21, [sp, #80]
	stp	x20, x19, [sp, #96]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w24, -48
	.cfi_offset w25, -56
	.cfi_offset w26, -64
	.cfi_offset w27, -72
	.cfi_offset w30, -80
	ldr	w8, [x4]
	mov	x19, x5
	mov	x20, x3
	mov	x21, x2
	mov	x25, x1
	mov	x22, x0
	tbz	w8, #0, .LBB37_4
	ldp	x23, x24, [x4, #8]
	sub	x27, x25, #1
	add	x1, x19, #16
	mov	x0, x22
	mov	x2, x27
	bl	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState12read_scalars
	tbz	w0, #0, .LBB37_8
	add	x0, x19, #16
	mov	x1, x27
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field5sum_e
	mov	x25, x0
	mov	x0, x27
	mov	x26, x1
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field10bit_length
	subs	w8, w0, #3
	mov	x0, x22
	csel	w1, wzr, w8, lo
	bl	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState5grind
	cbz	w0, .LBB37_9
	mov	x0, x23
	mov	x1, x24
	mov	x2, x25
	mov	x3, x26
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	mov	x8, x0
	eor	x9, x1, x20
	mov	w0, #1
	eor	x8, x8, x21
	stp	x8, x9, [x19]
	b	.LBB37_9
.LBB37_4:
	add	x0, sp, #8
	mov	x1, x22
	bl	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState11read_scalar
	ldr	x8, [sp, #8]
	cbz	x8, .LBB37_8
	ldp	x8, x9, [sp, #16]
	sub	x23, x25, #2
	add	x1, x19, #32
	mov	x0, x22
	mov	x2, x23
	stp	x8, x9, [x19]
	bl	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState12read_scalars
	tbz	w0, #0, .LBB37_8
	add	x0, x19, #32
	mov	x1, x23
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field5sum_e
	mov	x24, x0
	mov	x0, x23
	mov	x25, x1
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field10bit_length
	subs	w8, w0, #3
	mov	x0, x22
	csel	w1, wzr, w8, lo
	bl	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState5grind
	cbz	w0, .LBB37_9
	eor	x8, x24, x21
	eor	x9, x25, x20
	mov	w0, #1
	stp	x8, x9, [x19, #16]
	b	.LBB37_9
.LBB37_8:
	mov	w0, wzr
.LBB37_9:
	ldp	x20, x19, [sp, #96]
	ldp	x22, x21, [sp, #80]
	ldp	x24, x23, [sp, #64]
	ldp	x26, x25, [sp, #48]
	ldp	x30, x27, [sp, #32]
	add	sp, sp, #112
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w25
	.cfi_restore w26
	.cfi_restore w27
	.cfi_restore w30
	ret
.Lfunc_end37:
	.size	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState19sumcheck_round_poly, .Lfunc_end37-_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState19sumcheck_round_poly
	.cfi_endproc

	.section	.text._RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState5grind,"ax",@progbits
	.p2align	2
	.type	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState5grind,@function
_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState5grind:
.Lfunc_begin38:
	.cfi_startproc
	cbz	w1, .LBB38_3
	sub	sp, sp, #64
	.cfi_def_cfa_offset 64
	str	x30, [sp, #32]
	stp	x20, x19, [sp, #48]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w30, -32
	.cfi_remember_state
	mov	x20, x0
	mov	w19, w1
	add	x0, sp, #8
	mov	x1, x20
	bl	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState11next_scalar
	ldr	w8, [sp, #8]
	tbz	w8, #0, .LBB38_4
	ldp	x1, x2, [sp, #16]
	mov	x0, x20
	bl	_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW12absorb_nonce
	mov	x8, #-1
	lsl	x8, x8, x19
	bics	xzr, x0, x8
	cset	w0, eq
	ldp	x20, x19, [sp, #48]
	ldr	x30, [sp, #32]
	add	sp, sp, #64
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w30
	ret
.LBB38_3:
	mov	w0, #1
	ret
.LBB38_4:
	.cfi_restore_state
	mov	w0, wzr
	ldp	x20, x19, [sp, #48]
	ldr	x30, [sp, #32]
	add	sp, sp, #64
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w30
	ret
.Lfunc_end38:
	.size	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState5grind, .Lfunc_end38-_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState5grind
	.cfi_endproc

	.section	.text._RNvMs0_NtCsemcRClSg8DH_9native_vm6layoutNtB5_7FormBuf10add_scaled,"ax",@progbits
	.p2align	2
	.type	_RNvMs0_NtCsemcRClSg8DH_9native_vm6layoutNtB5_7FormBuf10add_scaled,@function
_RNvMs0_NtCsemcRClSg8DH_9native_vm6layoutNtB5_7FormBuf10add_scaled:
.Lfunc_begin39:
	.cfi_startproc
	cbz	x2, .LBB39_5
	stp	x30, x23, [sp, #-48]!
	.cfi_def_cfa_offset 48
	stp	x22, x21, [sp, #16]
	stp	x20, x19, [sp, #32]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w30, -48
	add	x8, x2, x2, lsl #2
	mov	x19, x4
	mov	x20, x3
	mov	x21, x1
	mov	x22, x0
	lsl	x8, x8, #3
	sub	x8, x8, #40
.LBB39_2:
	ldp	x2, x3, [x21, #24]
	mov	x0, x20
	mov	x1, x19
	mov	x23, x8
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	mov	x2, x0
	mov	x3, x1
	mov	x0, x22
	mov	x1, x21
	bl	_RNvMs0_NtCsemcRClSg8DH_9native_vm6layoutNtB5_7FormBuf8add_term
	cbz	w0, .LBB39_4
	add	x21, x21, #40
	sub	x8, x23, #40
	cbnz	x23, .LBB39_2
.LBB39_4:
	ldp	x20, x19, [sp, #32]
	ldp	x22, x21, [sp, #16]
	ldp	x30, x23, [sp], #48
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w30
	ret
.LBB39_5:
	mov	w0, #1
	ret
.Lfunc_end39:
	.size	_RNvMs0_NtCsemcRClSg8DH_9native_vm6layoutNtB5_7FormBuf10add_scaled, .Lfunc_end39-_RNvMs0_NtCsemcRClSg8DH_9native_vm6layoutNtB5_7FormBuf10add_scaled
	.cfi_endproc

	.section	.text._RNvMs0_NtCsemcRClSg8DH_9native_vm6layoutNtB5_7FormBuf8add_term,"ax",@progbits
	.p2align	2
	.type	_RNvMs0_NtCsemcRClSg8DH_9native_vm6layoutNtB5_7FormBuf8add_term,@function
_RNvMs0_NtCsemcRClSg8DH_9native_vm6layoutNtB5_7FormBuf8add_term:
.Lfunc_begin40:
	.cfi_startproc
	ldr	x8, [x0]
	cmp	x8, #148
	b.hi	.LBB40_10
	mov	w9, #40
	add	x11, x0, #8
	ldr	x10, [x1]
	madd	x9, x8, x9, x11
	cbz	x8, .LBB40_11
	add	x13, x1, #8
	cmp	x10, #3
	mov	w12, #8
	csel	x13, x13, x12, lo
	csel	x14, x10, xzr, lo
	mov	x15, x11
	b	.LBB40_4
.LBB40_3:
	cmp	x15, x9
	mov	x11, x15
	b.eq	.LBB40_9
.LBB40_4:
	ldr	x16, [x15], #40
	cmp	x16, x10
	b.ne	.LBB40_3
	add	x16, x11, #8
	cmp	x10, #3
	mov	x17, x14
	csel	x16, x16, x12, lo
	mov	x18, x13
.LBB40_6:
	cbz	x17, .LBB40_8
	ldr	x4, [x16], #8
	sub	x17, x17, #1
	ldr	x5, [x18], #8
	cmp	x4, x5
	b.eq	.LBB40_6
	b	.LBB40_3
.LBB40_8:
	ldp	x8, x9, [x11, #24]
	mov	w0, #1
	eor	x8, x8, x2
	eor	x9, x9, x3
	stp	x8, x9, [x11, #24]
	ret
.LBB40_9:
	cmp	x8, #148
	b.ne	.LBB40_11
.LBB40_10:
	mov	w0, wzr
	ret
.LBB40_11:
	ldp	x11, x12, [x1, #8]
	add	x8, x8, #1
	str	x8, [x0]
	mov	w0, #1
	str	x3, [x9, #32]
	stp	x10, x11, [x9]
	stp	x12, x2, [x9, #16]
	ret
.Lfunc_end40:
	.size	_RNvMs0_NtCsemcRClSg8DH_9native_vm6layoutNtB5_7FormBuf8add_term, .Lfunc_end40-_RNvMs0_NtCsemcRClSg8DH_9native_vm6layoutNtB5_7FormBuf8add_term
	.cfi_endproc

	.section	.text._RNvMs2_NtCsemcRClSg8DH_9native_vm6layoutNtB5_7LayoutW9placement,"ax",@progbits
	.p2align	2
	.type	_RNvMs2_NtCsemcRClSg8DH_9native_vm6layoutNtB5_7LayoutW9placement,@function
_RNvMs2_NtCsemcRClSg8DH_9native_vm6layoutNtB5_7LayoutW9placement:
.Lfunc_begin41:
	.cfi_startproc
	mov	w8, #24
	madd	x8, x1, x8, x0
	ldr	x9, [x8, #120]!
	cbz	x9, .LBB41_2
	ldp	x0, x1, [x8, #8]
	ret
.LBB41_2:
	mov	x1, xzr
	mov	x0, xzr
	ret
.Lfunc_end41:
	.size	_RNvMs2_NtCsemcRClSg8DH_9native_vm6layoutNtB5_7LayoutW9placement, .Lfunc_end41-_RNvMs2_NtCsemcRClSg8DH_9native_vm6layoutNtB5_7LayoutW9placement
	.cfi_endproc

	.section	.text._RNvMs_NtCsemcRClSg8DH_9native_vm10transcriptNtB4_4Rows3row,"ax",@progbits
	.p2align	2
	.type	_RNvMs_NtCsemcRClSg8DH_9native_vm10transcriptNtB4_4Rows3row,@function
_RNvMs_NtCsemcRClSg8DH_9native_vm10transcriptNtB4_4Rows3row:
.Lfunc_begin42:
	.cfi_startproc
	mov	w8, #193
	mov	x9, #1
	madd	x8, x1, x8, x9
	ldr	x9, [x0, #24]
	ldp	x11, x10, [x0]
	adds	x12, x9, x8
	add	x8, x11, x8, lsl #3
	cset	w13, hs
	cmp	x12, x10
	csinc	w10, w13, wzr, ls
	cmp	w10, #0
	mov	w10, #8
	csel	x1, xzr, x9, ne
	csel	x0, x10, x8, ne
	ret
.Lfunc_end42:
	.size	_RNvMs_NtCsemcRClSg8DH_9native_vm10transcriptNtB4_4Rows3row, .Lfunc_end42-_RNvMs_NtCsemcRClSg8DH_9native_vm10transcriptNtB4_4Rows3row
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr11first_claim,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr11first_claim,@function
_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr11first_claim:
.Lfunc_begin43:
	.cfi_startproc
	stp	x29, x30, [sp, #-96]!
	.cfi_def_cfa_offset 96
	stp	x28, x27, [sp, #16]
	stp	x26, x25, [sp, #32]
	stp	x24, x23, [sp, #48]
	stp	x22, x21, [sp, #64]
	stp	x20, x19, [sp, #80]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w24, -48
	.cfi_offset w25, -56
	.cfi_offset w26, -64
	.cfi_offset w27, -72
	.cfi_offset w28, -80
	.cfi_offset w30, -88
	.cfi_offset w29, -96
	sub	sp, sp, #1312
	.cfi_def_cfa_offset 1408
	ldr	xzr, [sp]
	mov	x22, x3
	mov	x23, x2
	mov	x24, x1
	mov	x19, x0
	add	x2, sp, #16
	mov	x0, x4
	mov	w1, #5
	mov	w3, #32
	mov	x20, x7
	mov	x21, x6
	mov	x25, x5
	stp	xzr, xzr, [sp, #16]
	add	x26, sp, #16
	stp	xzr, xzr, [sp, #32]
	stp	xzr, xzr, [sp, #48]
	stp	xzr, xzr, [sp, #64]
	stp	xzr, xzr, [sp, #80]
	stp	xzr, xzr, [sp, #96]
	stp	xzr, xzr, [sp, #112]
	stp	xzr, xzr, [sp, #128]
	stp	xzr, xzr, [sp, #144]
	stp	xzr, xzr, [sp, #160]
	stp	xzr, xzr, [sp, #176]
	stp	xzr, xzr, [sp, #192]
	stp	xzr, xzr, [sp, #208]
	stp	xzr, xzr, [sp, #224]
	stp	xzr, xzr, [sp, #240]
	stp	xzr, xzr, [sp, #256]
	stp	xzr, xzr, [sp, #272]
	stp	xzr, xzr, [sp, #288]
	stp	xzr, xzr, [sp, #304]
	stp	xzr, xzr, [sp, #320]
	stp	xzr, xzr, [sp, #336]
	stp	xzr, xzr, [sp, #352]
	stp	xzr, xzr, [sp, #368]
	stp	xzr, xzr, [sp, #384]
	stp	xzr, xzr, [sp, #400]
	stp	xzr, xzr, [sp, #416]
	stp	xzr, xzr, [sp, #432]
	stp	xzr, xzr, [sp, #448]
	stp	xzr, xzr, [sp, #464]
	stp	xzr, xzr, [sp, #480]
	stp	xzr, xzr, [sp, #496]
	str	xzr, [sp, #512]
	str	xzr, [sp, #520]
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field9eq_kernel
	cmp	x0, #1
	b.ne	.LBB43_8
	ldr	x8, [sp, #1408]
	str	x20, [sp, #8]
	mov	x20, xzr
	mov	w28, #25600
	mov	w29, #1
	add	x27, x8, #8
.LBB43_2:
	ubfx	x8, x20, #6, #5
	lsl	x2, x29, x20
	mov	x3, xzr
	add	x20, x20, #1
	add	x8, x26, x8, lsl #4
	ldp	x0, x1, [x8]
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	subs	x28, x28, #16
	stp	x0, x1, [x27, #-8]
	add	x27, x27, #16
	b.ne	.LBB43_2
	add	x2, sp, #528
	mov	x0, x22
	mov	w1, #1
	mov	w3, #2
	str	xzr, [sp, #528]
	str	xzr, [sp, #536]
	str	xzr, [sp, #544]
	str	xzr, [sp, #552]
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field9eq_kernel
	tbz	w0, #0, .LBB43_8
	ldr	x26, [sp, #544]
	ldr	x27, [sp, #552]
	add	x0, sp, #16
	mov	w1, #25
	mov	x2, x25
	mov	w3, #25
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field3dot
	mov	x2, x0
	mov	x3, x1
	mov	x0, x26
	mov	x1, x27
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	cmp	x23, #4
	mov	w8, #4
	add	x9, sp, #560
	mov	x25, x0
	mov	x26, x1
	csel	x1, x23, x8, lo
	add	x2, x9, #8
	mov	x0, x24
	mov	w3, #16
	str	xzr, [sp, #560]
	str	xzr, [sp, #568]
	str	xzr, [sp, #576]
	str	xzr, [sp, #584]
	str	xzr, [sp, #592]
	str	xzr, [sp, #600]
	str	xzr, [sp, #608]
	str	xzr, [sp, #616]
	str	xzr, [sp, #624]
	str	xzr, [sp, #632]
	str	xzr, [sp, #640]
	str	xzr, [sp, #648]
	str	xzr, [sp, #656]
	str	xzr, [sp, #664]
	str	xzr, [sp, #672]
	str	xzr, [sp, #680]
	str	xzr, [sp, #688]
	str	xzr, [sp, #696]
	str	xzr, [sp, #704]
	str	xzr, [sp, #712]
	str	xzr, [sp, #720]
	str	xzr, [sp, #728]
	str	xzr, [sp, #736]
	str	xzr, [sp, #744]
	str	xzr, [sp, #752]
	str	xzr, [sp, #760]
	str	xzr, [sp, #768]
	str	xzr, [sp, #776]
	str	xzr, [sp, #784]
	str	xzr, [sp, #792]
	str	xzr, [sp, #800]
	str	xzr, [sp, #808]
	str	xzr, [sp, #816]
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field9eq_kernel
	tbz	w0, #0, .LBB43_8
	add	x8, x24, #64
	subs	x9, x23, #4
	mov	w10, #8
	str	x1, [sp, #560]
	csel	x1, x10, x8, lo
	csel	x2, xzr, x9, lo
	add	x0, sp, #824
	str	xzr, [sp, #832]
	str	xzr, [sp, #840]
	str	xzr, [sp, #848]
	str	xzr, [sp, #856]
	str	xzr, [sp, #864]
	str	xzr, [sp, #872]
	str	xzr, [sp, #880]
	str	xzr, [sp, #888]
	str	xzr, [sp, #896]
	str	xzr, [sp, #904]
	str	xzr, [sp, #912]
	str	xzr, [sp, #920]
	str	xzr, [sp, #928]
	str	xzr, [sp, #936]
	str	xzr, [sp, #944]
	str	xzr, [sp, #952]
	str	xzr, [sp, #960]
	str	xzr, [sp, #968]
	str	xzr, [sp, #976]
	str	xzr, [sp, #984]
	str	xzr, [sp, #992]
	str	xzr, [sp, #1000]
	str	xzr, [sp, #1008]
	str	xzr, [sp, #1016]
	str	xzr, [sp, #1024]
	str	xzr, [sp, #1032]
	str	xzr, [sp, #1040]
	str	xzr, [sp, #1048]
	str	xzr, [sp, #1056]
	str	xzr, [sp, #1064]
	str	xzr, [sp, #1072]
	str	xzr, [sp, #1080]
	str	xzr, [sp, #1088]
	str	xzr, [sp, #1096]
	str	xzr, [sp, #1104]
	str	xzr, [sp, #1112]
	str	xzr, [sp, #1120]
	str	xzr, [sp, #1128]
	str	xzr, [sp, #1136]
	str	xzr, [sp, #1144]
	str	xzr, [sp, #1152]
	str	xzr, [sp, #1160]
	str	xzr, [sp, #1168]
	str	xzr, [sp, #1176]
	str	xzr, [sp, #1184]
	str	xzr, [sp, #1192]
	str	xzr, [sp, #1200]
	str	xzr, [sp, #1208]
	str	xzr, [sp, #1216]
	str	xzr, [sp, #1224]
	str	xzr, [sp, #1232]
	str	xzr, [sp, #1240]
	str	xzr, [sp, #1248]
	str	xzr, [sp, #1256]
	str	xzr, [sp, #1264]
	str	xzr, [sp, #1272]
	str	xzr, [sp, #1280]
	str	xzr, [sp, #1288]
	str	xzr, [sp, #1296]
	str	xzr, [sp, #1304]
	str	xzr, [sp, #824]
	bl	_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKj1e_E6extendB4_
	tbz	w0, #0, .LBB43_8
	add	x0, sp, #824
	mov	x1, x22
	mov	w2, #1
	bl	_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKj1e_E6extendB4_
	tbz	w0, #0, .LBB43_8
	ldr	x8, [sp, #8]
	add	x0, x19, #24
	add	x1, sp, #560
	mov	w2, #264
	eor	x20, x25, x21
	eor	x21, x26, x8
	bl	memcpy
	add	x0, x19, #288
	add	x1, sp, #824
	mov	w2, #488
	bl	memcpy
	mov	w8, #1
	stp	x20, x21, [x19, #8]
	str	x8, [x19]
	b	.LBB43_9
.LBB43_8:
	str	xzr, [x19]
.LBB43_9:
	add	sp, sp, #1312
	.cfi_def_cfa_offset 96
	ldp	x20, x19, [sp, #80]
	ldp	x22, x21, [sp, #64]
	ldp	x24, x23, [sp, #48]
	ldp	x26, x25, [sp, #32]
	ldp	x28, x27, [sp, #16]
	ldp	x29, x30, [sp], #96
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w25
	.cfi_restore w26
	.cfi_restore w27
	.cfi_restore w28
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end43:
	.size	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr11first_claim, .Lfunc_end43-_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr11first_claim
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr11keccak_open,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr11keccak_open,@function
_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr11keccak_open:
.Lfunc_begin44:
	.cfi_startproc
	stp	x29, x30, [sp, #-96]!
	.cfi_def_cfa_offset 96
	stp	x28, x27, [sp, #16]
	stp	x26, x25, [sp, #32]
	stp	x24, x23, [sp, #48]
	stp	x22, x21, [sp, #64]
	stp	x20, x19, [sp, #80]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w24, -48
	.cfi_offset w25, -56
	.cfi_offset w26, -64
	.cfi_offset w27, -72
	.cfi_offset w28, -80
	.cfi_offset w30, -88
	.cfi_offset w29, -96
	sub	sp, sp, #2128
	.cfi_def_cfa_offset 2224
	ldr	x28, [sp, #2240]
	mov	x26, x3
	mov	x27, x2
	ldr	x2, [sp, #2224]
	ldr	x3, [sp, #2232]
	ldr	xzr, [sp]
	mov	x23, x6
	mov	x24, x5
	mov	x25, x4
	mov	x19, x0
	add	x0, sp, #56
	mov	w4, #3
	mov	x5, x28
	mov	w6, #6
	mov	x22, x7
	bl	_RINvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB6_6TState8sumcheckNCNvB2_14sumcheck_plain0EB8_
	ldr	x8, [sp, #56]
	cbz	x8, .LBB44_42
	ldr	x29, [sp, #2248]
	ldp	x21, x20, [sp, #64]
	mov	x0, x27
	mov	x1, x26
	mov	x2, x25
	mov	x3, x24
	mov	x4, x23
	mov	x5, x22
	mov	x6, x29
	bl	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr12slot_weights
	tbz	w0, #0, .LBB44_41
	ldp	x22, x23, [x28]
	mov	x25, xzr
	stp	x21, x20, [sp, #16]
	mov	x26, xzr
	add	x27, sp, #80
	stp	x19, x28, [sp, #32]
	add	x28, sp, #1104
	str	x29, [sp, #48]
.LBB44_3:
	add	x24, x29, x26, lsl #11
	add	x0, sp, #80
	mov	w2, #1024
	mov	x1, x24
	bl	memcpy
	add	x0, sp, #1104
	add	x1, x24, #1024
	mov	w2, #1024
	bl	memcpy
	mov	x8, x29
	mov	x29, xzr
	add	x24, x8, x25
.LBB44_4:
	add	x8, x27, x29
	add	x9, x28, x29
	mov	x0, x22
	ldp	x20, x21, [x8]
	mov	x1, x23
	ldp	x8, x9, [x9]
	mov	x19, x29
	add	x29, x29, #16
	eor	x2, x8, x20
	eor	x3, x9, x21
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	add	x8, x24, x19
	eor	x10, x1, x21
	cmp	x29, #1024
	eor	x9, x0, x20
	str	x9, [x24, x19]
	str	x10, [x8, #8]
	b.ne	.LBB44_4
	add	x26, x26, #1
	ldr	x29, [sp, #48]
	add	x25, x25, #1024
	cmp	x26, #32
	b.ne	.LBB44_3
	ldr	x8, [sp, #40]
	mov	x25, xzr
	mov	x26, xzr
	add	x27, sp, #80
	add	x28, sp, #1104
	ldp	x22, x23, [x8, #16]
.LBB44_7:
	add	x24, x29, x26, lsl #11
	add	x0, sp, #80
	mov	w2, #1024
	mov	x1, x24
	bl	memcpy
	add	x0, sp, #1104
	add	x1, x24, #1024
	mov	w2, #1024
	bl	memcpy
	mov	x19, xzr
	add	x24, x29, x25
.LBB44_8:
	add	x8, x27, x19
	add	x9, x28, x19
	mov	x0, x22
	ldp	x20, x21, [x8]
	mov	x1, x23
	ldp	x8, x9, [x9]
	mov	x29, x19
	add	x19, x19, #16
	eor	x2, x8, x20
	eor	x3, x9, x21
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	add	x8, x24, x29
	eor	x10, x1, x21
	cmp	x19, #1024
	eor	x9, x0, x20
	str	x9, [x24, x29]
	str	x10, [x8, #8]
	b.ne	.LBB44_8
	add	x26, x26, #1
	ldr	x29, [sp, #48]
	add	x25, x25, #1024
	cmp	x26, #16
	b.ne	.LBB44_7
	ldr	x8, [sp, #40]
	add	x0, sp, #80
	mov	x1, x29
	mov	w2, #1024
	add	x24, sp, #80
	ldp	x22, x23, [x8, #32]
	bl	memcpy
	add	x0, sp, #1104
	add	x1, x29, #1024
	mov	w2, #1024
	add	x25, sp, #1104
	bl	memcpy
	mov	x26, xzr
.LBB44_11:
	add	x8, x24, x26
	add	x9, x25, x26
	mov	x0, x22
	ldp	x19, x20, [x8]
	mov	x1, x23
	ldp	x8, x9, [x9]
	add	x21, x29, x26
	add	x26, x26, #16
	eor	x2, x8, x19
	eor	x3, x9, x20
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	cmp	x26, #1024
	eor	x8, x0, x19
	eor	x9, x1, x20
	stp	x8, x9, [x21]
	b.ne	.LBB44_11
	add	x0, sp, #80
	add	x1, x29, #2048
	mov	w2, #1024
	add	x24, sp, #80
	bl	memcpy
	add	x0, sp, #1104
	add	x1, x29, #3072
	mov	w2, #1024
	add	x25, sp, #1104
	bl	memcpy
	mov	x26, xzr
.LBB44_13:
	add	x8, x24, x26
	add	x9, x25, x26
	mov	x0, x22
	ldp	x19, x20, [x8]
	mov	x1, x23
	ldp	x8, x9, [x9]
	add	x21, x29, x26
	add	x26, x26, #16
	eor	x2, x8, x19
	eor	x3, x9, x20
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	cmp	x26, #1024
	eor	x8, x0, x19
	eor	x9, x1, x20
	str	x8, [x21, #1024]
	str	x9, [x21, #1032]
	b.ne	.LBB44_13
	add	x0, sp, #80
	add	x1, x29, #1, lsl #12
	mov	w2, #1024
	add	x25, sp, #80
	bl	memcpy
	mov	w24, #5120
	add	x0, sp, #1104
	mov	w2, #1024
	add	x1, x29, x24
	add	x26, sp, #1104
	bl	memcpy
	mov	x27, xzr
.LBB44_15:
	add	x8, x25, x27
	add	x9, x26, x27
	mov	x0, x22
	ldp	x19, x20, [x8]
	mov	x1, x23
	ldp	x8, x9, [x9]
	add	x21, x29, x27
	add	x27, x27, #16
	eor	x2, x8, x19
	eor	x3, x9, x20
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	cmp	x27, #1024
	eor	x8, x0, x19
	eor	x9, x1, x20
	str	x8, [x21, #2048]
	str	x9, [x21, #2056]
	b.ne	.LBB44_15
	mov	w8, #6144
	add	x0, sp, #80
	mov	w2, #1024
	add	x1, x29, x8
	add	x27, sp, #80
	bl	memcpy
	mov	w26, #7168
	add	x0, sp, #1104
	mov	w2, #1024
	add	x1, x29, x26
	add	x28, sp, #1104
	bl	memcpy
	mov	x25, x29
	mov	x29, xzr
.LBB44_17:
	add	x8, x27, x29
	add	x9, x28, x29
	mov	x0, x22
	ldp	x19, x20, [x8]
	mov	x1, x23
	ldp	x8, x9, [x9]
	add	x21, x25, x29
	add	x29, x29, #16
	eor	x2, x8, x19
	eor	x3, x9, x20
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	cmp	x29, #1024
	eor	x8, x0, x19
	eor	x9, x1, x20
	str	x8, [x21, #3072]
	str	x9, [x21, #3080]
	b.ne	.LBB44_17
	add	x0, sp, #80
	add	x1, x25, #2, lsl #12
	mov	w2, #1024
	add	x27, sp, #80
	bl	memcpy
	mov	w8, #9216
	add	x0, sp, #1104
	mov	w2, #1024
	add	x1, x25, x8
	add	x28, sp, #1104
	bl	memcpy
	mov	x29, xzr
.LBB44_19:
	add	x8, x27, x29
	add	x9, x28, x29
	mov	x0, x22
	ldp	x19, x20, [x8]
	mov	x1, x23
	ldp	x8, x9, [x9]
	add	x21, x25, x29
	add	x29, x29, #16
	eor	x2, x8, x19
	eor	x3, x9, x20
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	cmp	x29, #1024
	eor	x8, x0, x19
	eor	x9, x1, x20
	str	x8, [x21, #4096]
	str	x9, [x21, #4104]
	b.ne	.LBB44_19
	mov	w8, #10240
	add	x0, sp, #80
	mov	w2, #1024
	add	x1, x25, x8
	add	x27, sp, #80
	bl	memcpy
	mov	w8, #11264
	add	x0, sp, #1104
	mov	w2, #1024
	add	x1, x25, x8
	add	x28, sp, #1104
	bl	memcpy
	mov	x29, xzr
.LBB44_21:
	add	x8, x27, x29
	add	x9, x28, x29
	mov	x0, x22
	ldp	x19, x20, [x8]
	mov	x1, x23
	ldp	x8, x9, [x9]
	add	x21, x25, x29
	add	x29, x29, #16
	eor	x2, x8, x19
	eor	x3, x9, x20
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	cmp	x29, #1024
	eor	x8, x0, x19
	eor	x9, x1, x20
	str	x8, [x21, #5120]
	str	x9, [x21, #5128]
	b.ne	.LBB44_21
	add	x0, sp, #80
	add	x1, x25, #3, lsl #12
	mov	w2, #1024
	add	x27, sp, #80
	bl	memcpy
	mov	w8, #13312
	add	x0, sp, #1104
	mov	w2, #1024
	add	x1, x25, x8
	add	x28, sp, #1104
	bl	memcpy
	mov	x29, xzr
.LBB44_23:
	add	x8, x27, x29
	add	x9, x28, x29
	mov	x0, x22
	ldp	x19, x20, [x8]
	mov	x1, x23
	ldp	x8, x9, [x9]
	add	x21, x25, x29
	add	x29, x29, #16
	eor	x2, x8, x19
	eor	x3, x9, x20
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	cmp	x29, #1024
	eor	x8, x0, x19
	eor	x9, x1, x20
	str	x8, [x21, #6144]
	str	x9, [x21, #6152]
	b.ne	.LBB44_23
	mov	w8, #14336
	add	x0, sp, #80
	mov	w2, #1024
	add	x1, x25, x8
	add	x27, sp, #80
	bl	memcpy
	mov	w8, #15360
	add	x0, sp, #1104
	mov	w2, #1024
	add	x1, x25, x8
	add	x28, sp, #1104
	bl	memcpy
	mov	x29, xzr
.LBB44_25:
	add	x8, x27, x29
	add	x9, x28, x29
	mov	x0, x22
	ldp	x19, x20, [x8]
	mov	x1, x23
	ldp	x8, x9, [x9]
	add	x21, x25, x29
	add	x29, x29, #16
	eor	x2, x8, x19
	eor	x3, x9, x20
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	cmp	x29, #1024
	eor	x8, x0, x19
	eor	x9, x1, x20
	str	x8, [x21, #7168]
	str	x9, [x21, #7176]
	b.ne	.LBB44_25
	ldr	x8, [sp, #40]
	add	x0, sp, #80
	mov	x1, x25
	mov	w2, #1024
	add	x27, sp, #80
	ldp	x22, x23, [x8, #48]
	bl	memcpy
	add	x0, sp, #1104
	add	x1, x25, #1024
	mov	w2, #1024
	add	x28, sp, #1104
	bl	memcpy
	mov	x29, xzr
.LBB44_27:
	add	x8, x27, x29
	add	x9, x28, x29
	mov	x0, x22
	ldp	x19, x20, [x8]
	mov	x1, x23
	ldp	x8, x9, [x9]
	add	x21, x25, x29
	add	x29, x29, #16
	eor	x2, x8, x19
	eor	x3, x9, x20
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	cmp	x29, #1024
	eor	x8, x0, x19
	eor	x9, x1, x20
	stp	x8, x9, [x21]
	b.ne	.LBB44_27
	add	x0, sp, #80
	add	x1, x25, #2048
	mov	w2, #1024
	add	x27, sp, #80
	bl	memcpy
	add	x0, sp, #1104
	add	x1, x25, #3072
	mov	w2, #1024
	add	x28, sp, #1104
	bl	memcpy
	mov	x29, xzr
.LBB44_29:
	add	x8, x27, x29
	add	x9, x28, x29
	mov	x0, x22
	ldp	x19, x20, [x8]
	mov	x1, x23
	ldp	x8, x9, [x9]
	add	x21, x25, x29
	add	x29, x29, #16
	eor	x2, x8, x19
	eor	x3, x9, x20
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	cmp	x29, #1024
	eor	x8, x0, x19
	eor	x9, x1, x20
	str	x8, [x21, #1024]
	str	x9, [x21, #1032]
	b.ne	.LBB44_29
	add	x0, sp, #80
	add	x1, x25, #1, lsl #12
	mov	w2, #1024
	add	x27, sp, #80
	bl	memcpy
	add	x0, sp, #1104
	add	x1, x25, x24
	mov	w2, #1024
	add	x24, sp, #1104
	bl	memcpy
	mov	x28, xzr
	mov	x29, x25
.LBB44_31:
	add	x8, x27, x28
	add	x9, x24, x28
	mov	x0, x22
	ldp	x19, x20, [x8]
	mov	x1, x23
	ldp	x8, x9, [x9]
	add	x21, x29, x28
	add	x28, x28, #16
	eor	x2, x8, x19
	eor	x3, x9, x20
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	cmp	x28, #1024
	eor	x8, x0, x19
	eor	x9, x1, x20
	str	x8, [x21, #2048]
	str	x9, [x21, #2056]
	b.ne	.LBB44_31
	mov	w8, #6144
	add	x0, sp, #80
	mov	w2, #1024
	add	x1, x29, x8
	add	x24, sp, #80
	bl	memcpy
	add	x0, sp, #1104
	add	x1, x29, x26
	mov	w2, #1024
	add	x25, sp, #1104
	bl	memcpy
	mov	x26, xzr
.LBB44_33:
	add	x8, x24, x26
	add	x9, x25, x26
	mov	x0, x22
	ldp	x19, x20, [x8]
	mov	x1, x23
	ldp	x8, x9, [x9]
	add	x21, x29, x26
	add	x26, x26, #16
	eor	x2, x8, x19
	eor	x3, x9, x20
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	cmp	x26, #1024
	eor	x8, x0, x19
	eor	x9, x1, x20
	str	x8, [x21, #3072]
	str	x9, [x21, #3080]
	b.ne	.LBB44_33
	ldr	x27, [sp, #40]
	add	x0, sp, #80
	mov	x1, x29
	mov	w2, #1024
	add	x24, sp, #80
	ldp	x22, x23, [x27, #64]
	bl	memcpy
	add	x0, sp, #1104
	add	x1, x29, #1024
	mov	w2, #1024
	add	x25, sp, #1104
	bl	memcpy
	mov	x26, xzr
.LBB44_35:
	add	x8, x24, x26
	add	x9, x25, x26
	mov	x0, x22
	ldp	x19, x20, [x8]
	mov	x1, x23
	ldp	x8, x9, [x9]
	add	x21, x29, x26
	add	x26, x26, #16
	eor	x2, x8, x19
	eor	x3, x9, x20
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	cmp	x26, #1024
	eor	x8, x0, x19
	eor	x9, x1, x20
	stp	x8, x9, [x21]
	b.ne	.LBB44_35
	add	x0, sp, #80
	add	x1, x29, #2048
	mov	w2, #1024
	add	x24, sp, #80
	bl	memcpy
	add	x0, sp, #1104
	add	x1, x29, #3072
	mov	w2, #1024
	add	x25, sp, #1104
	bl	memcpy
	mov	x26, xzr
.LBB44_37:
	add	x8, x24, x26
	add	x9, x25, x26
	mov	x0, x22
	ldp	x19, x20, [x8]
	mov	x1, x23
	ldp	x8, x9, [x9]
	add	x21, x29, x26
	add	x26, x26, #16
	eor	x2, x8, x19
	eor	x3, x9, x20
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	cmp	x26, #1024
	eor	x8, x0, x19
	eor	x9, x1, x20
	str	x8, [x21, #1024]
	str	x9, [x21, #1032]
	b.ne	.LBB44_37
	ldp	x22, x20, [x27, #80]
	add	x0, sp, #80
	mov	x1, x29
	mov	w2, #1024
	mov	w23, #1024
	add	x19, sp, #80
	bl	memcpy
	add	x0, sp, #1104
	add	x1, x29, #1024
	mov	w2, #1024
	add	x24, sp, #1104
	bl	memcpy
	add	x21, x29, #8
	add	x24, x24, #8
	add	x25, x19, #8
.LBB44_39:
	ldp	x19, x26, [x25, #-8]
	mov	x0, x22
	ldp	x8, x9, [x24, #-8]
	mov	x1, x20
	eor	x2, x8, x19
	eor	x3, x9, x26
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	eor	x8, x0, x19
	eor	x9, x1, x26
	subs	x23, x23, #16
	stp	x8, x9, [x21, #-8]
	add	x21, x21, #16
	add	x24, x24, #16
	add	x25, x25, #16
	b.ne	.LBB44_39
	ldp	x9, x19, [sp, #24]
	ldr	x8, [sp, #16]
	stp	x8, x9, [x19, #8]
	mov	w8, #1
	b	.LBB44_42
.LBB44_41:
	mov	x8, xzr
.LBB44_42:
	str	x8, [x19]
	add	sp, sp, #2128
	.cfi_def_cfa_offset 96
	ldp	x20, x19, [sp, #80]
	ldp	x22, x21, [sp, #64]
	ldp	x24, x23, [sp, #48]
	ldp	x26, x25, [sp, #32]
	ldp	x28, x27, [sp, #16]
	ldp	x29, x30, [sp], #96
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w25
	.cfi_restore w26
	.cfi_restore w27
	.cfi_restore w28
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end44:
	.size	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr11keccak_open, .Lfunc_end44-_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr11keccak_open
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr12keccak_phase,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr12keccak_phase,@function
_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr12keccak_phase:
.Lfunc_begin45:
	.cfi_startproc
	sub	sp, sp, #480
	.cfi_def_cfa_offset 480
	str	x29, [sp, #400]
	stp	x30, x25, [sp, #416]
	stp	x24, x23, [sp, #432]
	stp	x22, x21, [sp, #448]
	stp	x20, x19, [sp, #464]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w24, -48
	.cfi_offset w25, -56
	.cfi_offset w30, -64
	.cfi_offset w29, -80
	ldr	x8, [x2, #10328]
	mov	w11, #25
	stp	xzr, xzr, [sp]
	stp	xzr, xzr, [sp, #16]
	cmp	x8, #93
	stp	xzr, xzr, [sp, #32]
	csel	x10, x8, xzr, lo
	stp	xzr, xzr, [sp, #48]
	subs	x9, x10, #40
	stp	xzr, xzr, [sp, #64]
	csel	x9, xzr, x9, lo
	stp	xzr, xzr, [sp, #80]
	cmp	x9, #25
	stp	xzr, xzr, [sp, #96]
	csel	x9, x9, x11, lo
	stp	xzr, xzr, [sp, #112]
	add	x11, x9, #40
	stp	xzr, xzr, [sp, #128]
	cmp	x11, x10
	stp	xzr, xzr, [sp, #144]
	stp	xzr, xzr, [sp, #160]
	stp	xzr, xzr, [sp, #176]
	stp	xzr, xzr, [sp, #192]
	stp	xzr, xzr, [sp, #208]
	stp	xzr, xzr, [sp, #224]
	stp	xzr, xzr, [sp, #240]
	stp	xzr, xzr, [sp, #256]
	stp	xzr, xzr, [sp, #272]
	stp	xzr, xzr, [sp, #288]
	stp	xzr, xzr, [sp, #304]
	stp	xzr, xzr, [sp, #320]
	stp	xzr, xzr, [sp, #336]
	stp	xzr, xzr, [sp, #352]
	stp	xzr, xzr, [sp, #368]
	stp	xzr, xzr, [sp, #384]
	b.ls	.LBB45_2
	mov	w0, wzr
	b	.LBB45_3
.LBB45_2:
	mov	w10, #10336
	cmp	x8, #93
	mov	w24, #8
	add	x10, x2, x10
	lsl	x8, x9, #4
	mov	x22, x0
	csel	x9, x10, x24, lo
	mov	x0, sp
	mov	x23, x1
	add	x1, x9, #640
	mov	x25, x2
	mov	x2, x8
	mov	x19, x5
	mov	x20, x4
	mov	x21, x3
	bl	memcpy
	ldr	x8, [x25, #9840]
	mov	w9, #9848
	mov	x4, sp
	add	x9, x25, x9
	mov	x0, x22
	mov	x1, x23
	cmp	x8, #31
	mov	x5, x21
	mov	x6, x20
	csel	x2, x9, x24, lo
	csel	x3, x8, xzr, lo
	mov	x7, x19
	bl	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr13verify_keccak
.LBB45_3:
	ldp	x20, x19, [sp, #464]
	ldr	x29, [sp, #400]
	ldp	x22, x21, [sp, #448]
	ldp	x24, x23, [sp, #432]
	ldp	x30, x25, [sp, #416]
	add	sp, sp, #480
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w25
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end45:
	.size	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr12keccak_phase, .Lfunc_end45-_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr12keccak_phase
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr12slot_weights,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr12slot_weights,@function
_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr12slot_weights:
.Lfunc_begin46:
	.cfi_startproc
	sub	sp, sp, #176
	.cfi_def_cfa_offset 176
	stp	x29, x30, [sp, #80]
	stp	x28, x27, [sp, #96]
	stp	x26, x25, [sp, #112]
	stp	x24, x23, [sp, #128]
	stp	x22, x21, [sp, #144]
	stp	x20, x19, [sp, #160]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w24, -48
	.cfi_offset w25, -56
	.cfi_offset w26, -64
	.cfi_offset w27, -72
	.cfi_offset w28, -80
	.cfi_offset w30, -88
	.cfi_offset w29, -96
	.cfi_remember_state
	subs	x8, x0, #4
	mov	w10, #8
	mov	x21, x3
	csel	x8, xzr, x8, lo
	mov	w3, #4
	mov	x19, x6
	add	x9, x1, x8, lsl #4
	subs	x8, x2, x8
	add	x2, sp, #16
	csel	x1, xzr, x8, lo
	mov	x23, x5
	mov	x22, x4
	csel	x0, x10, x9, lo
	stp	xzr, xzr, [sp, #16]
	stp	xzr, xzr, [sp, #32]
	stp	xzr, xzr, [sp, #48]
	stp	xzr, xzr, [sp, #64]
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field9eq_kernel
	mov	x20, x0
	cmp	x0, #1
	b.ne	.LBB46_8
	mov	w8, #65536
	mov	x9, x19
	str	x23, [sp, #8]
.LBB46_2:
	stp	xzr, xzr, [x9]
	subs	x8, x8, #1024
	stp	xzr, xzr, [x9, #16]
	stp	xzr, xzr, [x9, #32]
	stp	xzr, xzr, [x9, #48]
	stp	xzr, xzr, [x9, #64]
	stp	xzr, xzr, [x9, #80]
	stp	xzr, xzr, [x9, #96]
	stp	xzr, xzr, [x9, #112]
	stp	xzr, xzr, [x9, #128]
	stp	xzr, xzr, [x9, #144]
	stp	xzr, xzr, [x9, #160]
	stp	xzr, xzr, [x9, #176]
	stp	xzr, xzr, [x9, #192]
	stp	xzr, xzr, [x9, #208]
	stp	xzr, xzr, [x9, #224]
	stp	xzr, xzr, [x9, #240]
	stp	xzr, xzr, [x9, #256]
	stp	xzr, xzr, [x9, #272]
	stp	xzr, xzr, [x9, #288]
	stp	xzr, xzr, [x9, #304]
	stp	xzr, xzr, [x9, #320]
	stp	xzr, xzr, [x9, #336]
	stp	xzr, xzr, [x9, #352]
	stp	xzr, xzr, [x9, #368]
	stp	xzr, xzr, [x9, #384]
	stp	xzr, xzr, [x9, #400]
	stp	xzr, xzr, [x9, #416]
	stp	xzr, xzr, [x9, #432]
	stp	xzr, xzr, [x9, #448]
	stp	xzr, xzr, [x9, #464]
	stp	xzr, xzr, [x9, #480]
	stp	xzr, xzr, [x9, #496]
	str	xzr, [x9, #512]
	str	xzr, [x9, #520]
	str	xzr, [x9, #528]
	str	xzr, [x9, #536]
	str	xzr, [x9, #544]
	str	xzr, [x9, #552]
	str	xzr, [x9, #560]
	str	xzr, [x9, #568]
	str	xzr, [x9, #576]
	str	xzr, [x9, #584]
	str	xzr, [x9, #592]
	str	xzr, [x9, #600]
	str	xzr, [x9, #608]
	str	xzr, [x9, #616]
	str	xzr, [x9, #624]
	str	xzr, [x9, #632]
	str	xzr, [x9, #640]
	str	xzr, [x9, #648]
	str	xzr, [x9, #656]
	str	xzr, [x9, #664]
	str	xzr, [x9, #672]
	str	xzr, [x9, #680]
	str	xzr, [x9, #688]
	str	xzr, [x9, #696]
	str	xzr, [x9, #704]
	str	xzr, [x9, #712]
	str	xzr, [x9, #720]
	str	xzr, [x9, #728]
	str	xzr, [x9, #736]
	str	xzr, [x9, #744]
	str	xzr, [x9, #752]
	str	xzr, [x9, #760]
	str	xzr, [x9, #768]
	str	xzr, [x9, #776]
	str	xzr, [x9, #784]
	str	xzr, [x9, #792]
	str	xzr, [x9, #800]
	str	xzr, [x9, #808]
	str	xzr, [x9, #816]
	str	xzr, [x9, #824]
	str	xzr, [x9, #832]
	str	xzr, [x9, #840]
	str	xzr, [x9, #848]
	str	xzr, [x9, #856]
	str	xzr, [x9, #864]
	str	xzr, [x9, #872]
	str	xzr, [x9, #880]
	str	xzr, [x9, #888]
	str	xzr, [x9, #896]
	str	xzr, [x9, #904]
	str	xzr, [x9, #912]
	str	xzr, [x9, #920]
	str	xzr, [x9, #928]
	str	xzr, [x9, #936]
	str	xzr, [x9, #944]
	str	xzr, [x9, #952]
	str	xzr, [x9, #960]
	str	xzr, [x9, #968]
	str	xzr, [x9, #976]
	str	xzr, [x9, #984]
	str	xzr, [x9, #992]
	str	xzr, [x9, #1000]
	str	xzr, [x9, #1008]
	str	xzr, [x9, #1016]
	add	x9, x9, #1024
	b.ne	.LBB46_2
	mov	w8, #25
	ldp	x24, x25, [sp, #16]
	mul	x27, x22, x8
	mov	x26, xzr
	add	x28, x21, #8
	mov	w29, #25600
	b	.LBB46_5
.LBB46_4:
	subs	x29, x29, #16
	add	x28, x28, #16
	add	x26, x26, #1
	b.eq	.LBB46_7
.LBB46_5:
	add	x23, x27, x26, lsr #6
	cmp	x23, #63
	b.hi	.LBB46_4
	ldp	x2, x3, [x28, #-8]
	mov	x0, x24
	mov	x1, x25
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	add	x8, x19, x23, lsl #10
	and	x9, x26, #0x3f
	add	x8, x8, x9, lsl #4
	stp	x0, x1, [x8]
	b	.LBB46_4
.LBB46_7:
	ldr	x8, [sp, #8]
	cmp	x8, #1
	b.ne	.LBB46_9
.LBB46_8:
	and	w0, w20, #0x1
	ldp	x20, x19, [sp, #160]
	ldp	x22, x21, [sp, #144]
	ldp	x24, x23, [sp, #128]
	ldp	x26, x25, [sp, #112]
	ldp	x28, x27, [sp, #96]
	ldp	x29, x30, [sp, #80]
	add	sp, sp, #176
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w25
	.cfi_restore w26
	.cfi_restore w27
	.cfi_restore w28
	.cfi_restore w30
	.cfi_restore w29
	ret
.LBB46_9:
	.cfi_restore_state
	mov	w8, #25
	mov	x9, #25
	mov	x24, xzr
	madd	x25, x22, x8, x9
	ldp	x22, x23, [sp, #32]
	add	x21, x21, #8
	mov	w26, #25600
	b	.LBB46_11
.LBB46_10:
	subs	x26, x26, #16
	add	x21, x21, #16
	add	x24, x24, #1
	b.eq	.LBB46_8
.LBB46_11:
	add	x27, x25, x24, lsr #6
	cmp	x27, #63
	b.hi	.LBB46_10
	ldp	x2, x3, [x21, #-8]
	mov	x0, x22
	mov	x1, x23
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	add	x8, x19, x27, lsl #10
	and	x9, x24, #0x3f
	add	x8, x8, x9, lsl #4
	stp	x0, x1, [x8]
	b	.LBB46_10
.Lfunc_end46:
	.size	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr12slot_weights, .Lfunc_end46-_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr12slot_weights
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr12verify_layer,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr12verify_layer,@function
_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr12verify_layer:
.Lfunc_begin47:
	.cfi_startproc
	stp	x29, x30, [sp, #-96]!
	.cfi_def_cfa_offset 96
	stp	x28, x27, [sp, #16]
	stp	x26, x25, [sp, #32]
	stp	x24, x23, [sp, #48]
	stp	x22, x21, [sp, #64]
	stp	x20, x19, [sp, #80]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w24, -48
	.cfi_offset w25, -56
	.cfi_offset w26, -64
	.cfi_offset w27, -72
	.cfi_offset w28, -80
	.cfi_offset w30, -88
	.cfi_offset w29, -96
	sub	sp, sp, #1936
	.cfi_def_cfa_offset 2032
	ldr	xzr, [sp]
	str	x2, [sp, #128]
	subs	x8, x1, #4
	add	x1, sp, #152
	mov	w2, #47
	mov	x23, x4
	mov	x19, x3
	mov	x20, x0
	stp	xzr, xzr, [sp, #152]
	stp	xzr, xzr, [sp, #168]
	csel	x21, xzr, x8, lo
	add	x28, sp, #152
	stp	xzr, xzr, [sp, #184]
	stp	xzr, xzr, [sp, #200]
	stp	xzr, xzr, [sp, #216]
	stp	xzr, xzr, [sp, #232]
	stp	xzr, xzr, [sp, #248]
	stp	xzr, xzr, [sp, #264]
	stp	xzr, xzr, [sp, #280]
	stp	xzr, xzr, [sp, #296]
	stp	xzr, xzr, [sp, #312]
	stp	xzr, xzr, [sp, #328]
	stp	xzr, xzr, [sp, #344]
	stp	xzr, xzr, [sp, #360]
	stp	xzr, xzr, [sp, #376]
	stp	xzr, xzr, [sp, #392]
	stp	xzr, xzr, [sp, #408]
	stp	xzr, xzr, [sp, #424]
	stp	xzr, xzr, [sp, #440]
	stp	xzr, xzr, [sp, #456]
	stp	xzr, xzr, [sp, #472]
	stp	xzr, xzr, [sp, #488]
	stp	xzr, xzr, [sp, #504]
	str	xzr, [sp, #520]
	str	xzr, [sp, #528]
	str	xzr, [sp, #536]
	str	xzr, [sp, #544]
	str	xzr, [sp, #552]
	str	xzr, [sp, #560]
	str	xzr, [sp, #568]
	str	xzr, [sp, #576]
	str	xzr, [sp, #584]
	str	xzr, [sp, #592]
	str	xzr, [sp, #600]
	str	xzr, [sp, #608]
	str	xzr, [sp, #616]
	str	xzr, [sp, #624]
	str	xzr, [sp, #632]
	str	xzr, [sp, #640]
	str	xzr, [sp, #648]
	str	xzr, [sp, #656]
	str	xzr, [sp, #664]
	str	xzr, [sp, #672]
	str	xzr, [sp, #680]
	str	xzr, [sp, #688]
	str	xzr, [sp, #696]
	str	xzr, [sp, #704]
	str	xzr, [sp, #712]
	str	xzr, [sp, #720]
	str	xzr, [sp, #728]
	str	xzr, [sp, #736]
	str	xzr, [sp, #744]
	str	xzr, [sp, #752]
	str	xzr, [sp, #760]
	str	xzr, [sp, #768]
	str	xzr, [sp, #776]
	str	xzr, [sp, #784]
	str	xzr, [sp, #792]
	str	xzr, [sp, #800]
	str	xzr, [sp, #808]
	str	xzr, [sp, #816]
	str	xzr, [sp, #824]
	str	xzr, [sp, #832]
	str	xzr, [sp, #840]
	str	xzr, [sp, #848]
	str	xzr, [sp, #856]
	str	xzr, [sp, #864]
	str	xzr, [sp, #872]
	str	xzr, [sp, #880]
	str	xzr, [sp, #888]
	str	xzr, [sp, #896]
	bl	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState12read_scalars
	cbz	w0, .LBB47_38
	str	x19, [sp, #136]
	ldr	x8, [x19, #16]!
	add	x9, x23, #26, lsl #12
	mov	w10, #51200
	mov	w11, #8
	cmp	x8, #17
	add	x9, x9, #1032
	stp	x20, x21, [sp, #104]
	str	x9, [sp, #96]
	add	x9, x19, #8
	csel	x25, x8, xzr, lo
	add	x8, x23, x10
	mov	x29, xzr
	mov	x22, xzr
	stp	x19, x8, [sp, #80]
	csel	x8, x9, x11, lo
	mov	x20, xzr
	mov	x21, xzr
	str	x23, [sp, #120]
	and	x23, x25, #0x1e
	add	x19, x8, #8
	adrp	x24, .Lanon.a75d6d9e6a8990b4224ef13f18552af8.0
	add	x24, x24, :lo12:.Lanon.a75d6d9e6a8990b4224ef13f18552af8.0
	mov	w27, #1
	adrp	x26, .Lanon.a75d6d9e6a8990b4224ef13f18552af8.0+8
	add	x26, x26, :lo12:.Lanon.a75d6d9e6a8990b4224ef13f18552af8.0+8
	str	x8, [sp, #144]
	b	.LBB47_4
.LBB47_2:
	mov	x1, xzr
	mov	x0, xzr
.LBB47_3:
	add	x8, x28, x29
	add	x29, x29, #16
	add	x20, x20, #1
	ldp	x2, x3, [x8]
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	cmp	x29, #752
	eor	x21, x0, x21
	eor	x22, x1, x22
	b.eq	.LBB47_12
.LBB47_4:
	cbz	x25, .LBB47_2
	lsl	x8, x27, x20
	cmp	x25, #1
	b.ne	.LBB47_7
	mov	x0, xzr
	mov	x1, xzr
	mov	x11, xzr
	b	.LBB47_10
.LBB47_7:
	ldr	x13, [sp, #144]
	mov	x9, xzr
	mov	x10, xzr
	mov	x11, xzr
	mov	x12, xzr
	mov	x14, x26
	add	x13, x13, #16
	and	x15, x25, #0x1e
.LBB47_8:
	ldp	x16, x0, [x14, #-8]
	add	x14, x14, #16
	ldp	x17, x18, [x13, #-16]
	ldp	x1, x2, [x13], #32
	tst	x16, x8
	csel	x16, xzr, x18, eq
	csel	x17, xzr, x17, eq
	tst	x0, x8
	csel	x18, xzr, x2, eq
	eor	x11, x11, x16
	csel	x16, xzr, x1, eq
	eor	x9, x9, x17
	subs	x15, x15, #2
	eor	x12, x12, x18
	eor	x10, x10, x16
	b.ne	.LBB47_8
	cmp	x25, x23
	eor	x0, x10, x9
	eor	x1, x12, x11
	and	x11, x25, #0x1e
	b.eq	.LBB47_3
.LBB47_10:
	add	x9, x24, x11, lsl #3
	add	x10, x19, x11, lsl #4
	sub	x11, x25, x11
.LBB47_11:
	ldr	x12, [x9], #8
	ldp	x13, x14, [x10, #-8]
	add	x10, x10, #16
	tst	x12, x8
	csel	x12, xzr, x14, eq
	csel	x13, xzr, x13, eq
	subs	x11, x11, #1
	eor	x1, x1, x12
	eor	x0, x0, x13
	b.ne	.LBB47_11
	b	.LBB47_3
.LBB47_12:
	ldr	x9, [sp, #136]
	ldr	x11, [sp, #112]
	add	x2, sp, #904
	mov	w3, #4
	str	xzr, [sp, #904]
	ldr	x8, [x9, #280]
	add	x19, x9, #288
	mov	w9, #8
	str	xzr, [sp, #912]
	cmp	x8, #31
	str	xzr, [sp, #920]
	csel	x10, x19, x9, lo
	csel	x8, x8, xzr, lo
	str	xzr, [sp, #928]
	add	x10, x10, x11, lsl #4
	subs	x8, x8, x11
	str	xzr, [sp, #936]
	csel	x1, xzr, x8, lo
	str	xzr, [sp, #944]
	csel	x0, x9, x10, lo
	str	xzr, [sp, #952]
	str	xzr, [sp, #960]
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field9eq_kernel
	cmp	x0, #1
	b.ne	.LBB47_37
	ldr	x18, [sp, #904]
	ldr	x1, [sp, #128]
	mov	w15, #11
	adrp	x0, .Lanon.a75d6d9e6a8990b4224ef13f18552af8.1
	add	x0, x0, :lo12:.Lanon.a75d6d9e6a8990b4224ef13f18552af8.1
	mov	w2, #25656
	str	x18, [sp, #112]
	ldr	x18, [sp, #912]
	mov	x17, xzr
	mov	x8, xzr
	mov	x9, xzr
	mov	x10, xzr
	str	x18, [sp, #72]
	sub	x18, x15, x1
	ldr	x15, [sp, #120]
	ldr	x18, [x0, x18, lsl #3]
	mov	x11, xzr
	mov	x12, xzr
	mov	x13, xzr
	mov	x14, xzr
	mov	x16, xzr
	add	x2, x15, x2
	mov	w3, #1
	mov	w4, #2
	mov	w5, #4
	mov	w6, #8
	str	x19, [sp, #32]
.LBB47_14:
	ldp	x7, x19, [x2, #-56]
	lsl	x20, x3, x17
	ldp	x23, x24, [x2, #-40]
	lsl	x26, x4, x17
	ldp	x27, x28, [x2, #-24]
	lsl	x29, x5, x17
	tst	x20, x18
	lsl	x15, x6, x17
	add	x17, x17, #4
	csel	x19, xzr, x19, eq
	csel	x7, xzr, x7, eq
	tst	x26, x18
	csel	x20, xzr, x24, eq
	csel	x23, xzr, x23, eq
	tst	x29, x18
	csel	x24, xzr, x28, eq
	csel	x26, xzr, x27, eq
	tst	x15, x18
	ldp	x15, x30, [x2, #-8]
	eor	x8, x8, x19
	eor	x9, x9, x20
	eor	x10, x10, x24
	eor	x12, x12, x7
	eor	x13, x13, x23
	eor	x14, x14, x26
	add	x2, x2, #64
	csel	x27, xzr, x30, eq
	csel	x15, xzr, x15, eq
	cmp	x17, #64
	eor	x11, x11, x27
	eor	x16, x16, x15
	b.ne	.LBB47_14
	eor	x8, x9, x8
	ldr	x9, [sp, #920]
	mov	x4, xzr
	str	x8, [sp, #48]
	eor	x8, x11, x10
	eor	x10, x13, x12
	str	x8, [sp, #40]
	ldr	x8, [sp, #928]
	mov	w12, #23
	sub	x12, x12, x1
	mov	w13, #25656
	mov	x17, xzr
	stp	x8, x9, [sp, #56]
	ldr	x8, [sp, #120]
	ldr	x12, [x0, x12, lsl #3]
	mov	x18, xzr
	mov	x2, xzr
	mov	x3, xzr
	mov	x5, xzr
	mov	x6, xzr
	mov	x7, xzr
	mov	x19, xzr
	eor	x11, x16, x14
	add	x13, x8, x13
	mov	w14, #1
	mov	w15, #2
	mov	w16, #4
	mov	w20, #8
.LBB47_16:
	ldp	x0, x23, [x13, #-56]
	lsl	x24, x14, x4
	ldp	x26, x29, [x13, #-40]
	lsl	x30, x15, x4
	ldp	x27, x28, [x13, #-24]
	lsl	x8, x16, x4
	tst	x24, x12
	lsl	x9, x20, x4
	add	x4, x4, #4
	csel	x23, xzr, x23, eq
	csel	x0, xzr, x0, eq
	tst	x30, x12
	csel	x24, xzr, x29, eq
	csel	x26, xzr, x26, eq
	tst	x8, x12
	csel	x8, xzr, x28, eq
	csel	x27, xzr, x27, eq
	tst	x9, x12
	ldp	x9, x1, [x13, #-8]
	eor	x2, x2, x8
	eor	x17, x17, x23
	eor	x18, x18, x24
	eor	x5, x5, x0
	eor	x6, x6, x26
	eor	x7, x7, x27
	add	x13, x13, #64
	csel	x1, xzr, x1, eq
	csel	x8, xzr, x9, eq
	cmp	x4, #64
	eor	x3, x3, x1
	eor	x19, x19, x8
	b.ne	.LBB47_16
	ldp	x9, x8, [sp, #40]
	eor	x26, x3, x2
	ldr	x0, [sp, #112]
	ldr	x1, [sp, #72]
	eor	x2, x11, x10
	eor	x20, x6, x5
	eor	x19, x19, x7
	eor	x23, x18, x17
	eor	x3, x9, x8
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	mov	x24, x0
	mov	x29, x1
	eor	x2, x19, x20
	ldp	x1, x0, [sp, #56]
	eor	x3, x26, x23
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	mov	x27, x0
	ldr	x0, [sp, #144]
	mov	x28, x1
	mov	x1, x25
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field5sum_e
	mov	x2, x0
	mov	x3, x1
	eor	x0, x27, x24
	eor	x1, x28, x29
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	ldr	x20, [sp, #136]
	eor	x9, x0, x21
	mov	w0, wzr
	ldr	x8, [x20]
	cmp	x9, x8
	b.ne	.LBB47_38
	ldr	x8, [x20, #8]
	eor	x9, x1, x22
	cmp	x9, x8
	b.ne	.LBB47_38
	mov	w0, #45
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field10bit_length
	ldr	x22, [sp, #104]
	subs	w8, w0, #3
	csel	w1, wzr, w8, lo
	mov	x0, x22
	bl	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState5grind
	cbz	w0, .LBB47_38
	mov	x0, x22
	bl	_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW7squeeze
	mov	x27, x0
	mov	x28, x1
	add	x0, sp, #968
	mov	x1, x27
	mov	x2, x28
	add	x19, sp, #968
	bl	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr16instance_weights
	ldr	x8, [sp, #968]
	add	x9, x19, #8
	mov	w19, #8
	cmp	x8, #17
	csel	x0, x9, x19, lo
	csel	x1, x8, xzr, lo
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field5sum_e
	ldr	x8, [x20, #280]
	ldr	x9, [sp, #32]
	mov	x25, x0
	mov	x26, x1
	add	x0, sp, #152
	mov	w1, #47
	cmp	x8, #31
	mov	x2, x27
	mov	x3, x28
	str	xzr, [sp, #1232]
	csel	x29, x9, x19, lo
	csel	x24, x8, xzr, lo
	str	xzr, [sp, #1240]
	str	xzr, [sp, #1248]
	str	xzr, [sp, #1256]
	str	xzr, [sp, #1264]
	str	xzr, [sp, #1272]
	str	xzr, [sp, #1280]
	str	xzr, [sp, #1288]
	str	xzr, [sp, #1296]
	str	xzr, [sp, #1304]
	str	xzr, [sp, #1312]
	str	xzr, [sp, #1320]
	str	xzr, [sp, #1328]
	str	xzr, [sp, #1336]
	str	xzr, [sp, #1344]
	str	xzr, [sp, #1352]
	str	xzr, [sp, #1360]
	str	xzr, [sp, #1368]
	str	xzr, [sp, #1376]
	str	xzr, [sp, #1384]
	str	xzr, [sp, #1392]
	str	xzr, [sp, #1400]
	str	xzr, [sp, #1408]
	str	xzr, [sp, #1416]
	str	xzr, [sp, #1424]
	str	xzr, [sp, #1432]
	str	xzr, [sp, #1440]
	str	xzr, [sp, #1448]
	str	xzr, [sp, #1456]
	str	xzr, [sp, #1464]
	str	xzr, [sp, #1472]
	str	xzr, [sp, #1480]
	str	xzr, [sp, #1488]
	str	xzr, [sp, #1496]
	str	xzr, [sp, #1504]
	str	xzr, [sp, #1512]
	str	xzr, [sp, #1520]
	str	xzr, [sp, #1528]
	str	xzr, [sp, #1536]
	str	xzr, [sp, #1544]
	str	xzr, [sp, #1552]
	str	xzr, [sp, #1560]
	str	xzr, [sp, #1568]
	str	xzr, [sp, #1576]
	str	xzr, [sp, #1584]
	str	xzr, [sp, #1592]
	str	xzr, [sp, #1600]
	str	xzr, [sp, #1608]
	str	xzr, [sp, #1616]
	str	xzr, [sp, #1624]
	str	xzr, [sp, #1632]
	str	xzr, [sp, #1640]
	str	xzr, [sp, #1648]
	str	xzr, [sp, #1656]
	str	xzr, [sp, #1664]
	str	xzr, [sp, #1672]
	str	xzr, [sp, #1680]
	str	xzr, [sp, #1688]
	str	xzr, [sp, #1696]
	str	xzr, [sp, #1704]
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field9poly_eval
	mov	x2, x0
	mov	x3, x1
	add	x0, sp, #1712
	add	x6, sp, #1232
	mov	x1, x22
	mov	x4, x29
	mov	x5, x24
	mov	x7, x24
	bl	_RINvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB6_6TState8sumcheckNCNvNtB8_10keccak_gkr12verify_layers1_0EB8_
	ldr	x8, [sp, #1712]
	cbz	x8, .LBB47_37
	ldr	x2, [sp, #1720]
	ldr	x3, [sp, #1728]
	add	x0, sp, #1888
	add	x5, sp, #1712
	mov	x1, x22
	mov	w4, #4
	mov	w6, #11
	str	xzr, [sp, #1712]
	str	xzr, [sp, #1720]
	str	xzr, [sp, #1728]
	str	xzr, [sp, #1736]
	str	xzr, [sp, #1744]
	str	xzr, [sp, #1752]
	str	xzr, [sp, #1760]
	str	xzr, [sp, #1768]
	str	xzr, [sp, #1776]
	str	xzr, [sp, #1784]
	str	xzr, [sp, #1792]
	str	xzr, [sp, #1800]
	str	xzr, [sp, #1808]
	str	xzr, [sp, #1816]
	str	xzr, [sp, #1824]
	str	xzr, [sp, #1832]
	str	xzr, [sp, #1840]
	str	xzr, [sp, #1848]
	str	xzr, [sp, #1856]
	str	xzr, [sp, #1864]
	str	xzr, [sp, #1872]
	str	xzr, [sp, #1880]
	bl	_RINvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB6_6TState8sumcheckNCNvB2_14sumcheck_plain0EB8_
	ldr	w8, [sp, #1888]
	tbz	w8, #0, .LBB47_37
	ldr	x20, [sp, #1896]
	ldr	x19, [sp, #1904]
	add	x1, sp, #1888
	mov	x0, x22
	mov	w2, #3
	str	xzr, [sp, #1888]
	str	xzr, [sp, #1896]
	str	xzr, [sp, #1904]
	str	xzr, [sp, #1912]
	str	xzr, [sp, #1920]
	str	xzr, [sp, #1928]
	bl	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState12read_scalars
	ldr	x21, [sp, #120]
	tbz	w0, #0, .LBB47_37
	add	x8, x21, #26, lsl #12
	add	x0, sp, #1712
	mov	w1, #11
	add	x2, x8, #1024
	mov	w3, #2048
	str	x2, [sp, #144]
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field9eq_kernel
	tbz	w0, #0, .LBB47_37
	mov	w8, #25600
	ldr	x0, [sp, #144]
	ldr	x29, [sp, #1888]
	ldr	x27, [sp, #1896]
	ldr	x23, [sp, #1904]
	add	x2, x21, x8
	str	x19, [sp, #128]
	ldr	x19, [sp, #1912]
	mov	w1, #1600
	str	x20, [sp, #112]
	ldr	x20, [sp, #1920]
	mov	w3, #1600
	ldr	x28, [sp, #1928]
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field3dot
	stp	x1, x0, [sp, #64]
	mov	x0, x25
	mov	x1, x26
	mov	x2, x29
	mov	x3, x27
	stp	x27, x29, [sp, #48]
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	mov	x21, x0
	mov	x29, x1
	stp	x19, x23, [sp, #32]
	eor	x0, x23, x25
	eor	x1, x19, x26
	ldr	x19, [sp, #128]
	mov	x2, x20
	mov	x3, x28
	stp	x28, x20, [sp, #16]
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	eor	x2, x0, x21
	eor	x3, x1, x29
	ldp	x1, x0, [sp, #64]
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	ldr	x8, [sp, #112]
	cmp	x0, x8
	b.ne	.LBB47_37
	cmp	x1, x19
	b.ne	.LBB47_37
	mov	w0, #1
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field10bit_length
	subs	w8, w0, #3
	mov	x0, x22
	csel	w1, wzr, w8, lo
	bl	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState5grind
	cbz	w0, .LBB47_37
	mov	x0, x22
	bl	_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW7squeeze
	ldr	x29, [sp, #88]
	mov	x23, x0
	mov	x25, x1
	mov	x19, xzr
	mov	w26, #25600
	add	x20, x29, #8
	b	.LBB47_30
.LBB47_28:
	ldr	x10, [sp, #144]
	add	x9, x10, x9, lsl #4
	add	x8, x9, x8, lsl #4
	ldp	x2, x3, [x8]
.LBB47_29:
	ldr	x8, [sp, #96]
	mov	x0, x23
	mov	x1, x25
	ldp	x28, x27, [x8, #-8]
	add	x8, x8, #16
	str	x8, [sp, #96]
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	eor	x2, x0, x21
	eor	x3, x1, x22
	mov	x0, x23
	mov	x1, x25
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	subs	x26, x26, #16
	eor	x8, x0, x28
	eor	x9, x1, x27
	add	x19, x19, #1
	str	x8, [x29], #16
	str	x9, [x20], #16
	b.eq	.LBB47_35
.LBB47_30:
	lsr	x8, x19, #6
	mov	x9, #3689348814741910323
	mov	x10, #-3689348814741910324
	movk	x9, #13108
	movk	x10, #52429
	mov	w11, #4
	umulh	x9, x8, x9
	umulh	x10, x19, x10
	add	x9, x9, x9, lsl #2
	lsr	x10, x10, #8
	subs	x9, x8, x9
	sub	x8, x9, #1
	add	x10, x10, x10, lsl #2
	csel	x8, x11, x8, eq
	add	x8, x8, x10
	lsl	x11, x8, #6
	and	x8, x19, #0x3f
	cmp	x11, #2047
	b.hi	.LBB47_32
	ldr	x12, [sp, #144]
	add	x11, x12, x11, lsl #4
	add	x11, x11, x8, lsl #4
	ldp	x21, x22, [x11]
	b	.LBB47_33
.LBB47_32:
	mov	x21, xzr
	mov	x22, xzr
.LBB47_33:
	cmp	x9, #2
	mov	w11, #3
	mov	x12, #288230376151711742
	csel	x11, x11, x12, lo
	add	x9, x10, x9
	add	x9, x9, x11
	lsl	x9, x9, #6
	cmp	x9, #2047
	b.ls	.LBB47_28
	mov	x2, xzr
	mov	x3, xzr
	b	.LBB47_29
.LBB47_35:
	ldr	x9, [sp, #120]
	ldr	x0, [sp, #88]
	add	x8, x9, #18, lsl #12
	add	x2, x9, #25, lsl #12
	add	x1, x8, #3072
	mov	w8, #25600
	add	x3, x9, x8
	bl	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr16linear_transpose
	ldp	x3, x2, [sp, #16]
	mov	x0, x23
	mov	x1, x25
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	ldp	x8, x9, [sp, #32]
	eor	x2, x0, x9
	eor	x3, x1, x8
	mov	x0, x23
	mov	x1, x25
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	ldp	x9, x8, [sp, #48]
	mov	w2, #264
	ldr	x19, [sp, #136]
	eor	x8, x0, x8
	ldr	x0, [sp, #80]
	eor	x9, x1, x9
	add	x1, sp, #968
	stp	x8, x9, [x19]
	bl	memcpy
	add	x0, x19, #280
	add	x1, sp, #1232
	mov	x2, x24
	str	xzr, [x19, #280]
	bl	_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKj1e_E6extendB4_
	tbz	w0, #0, .LBB47_37
	mov	w0, #1
	b	.LBB47_38
.LBB47_37:
	mov	w0, wzr
.LBB47_38:
	add	sp, sp, #1936
	.cfi_def_cfa_offset 96
	ldp	x20, x19, [sp, #80]
	ldp	x22, x21, [sp, #64]
	ldp	x24, x23, [sp, #48]
	ldp	x26, x25, [sp, #32]
	ldp	x28, x27, [sp, #16]
	ldp	x29, x30, [sp], #96
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w25
	.cfi_restore w26
	.cfi_restore w27
	.cfi_restore w28
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end47:
	.size	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr12verify_layer, .Lfunc_end47-_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr12verify_layer
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr13verify_keccak,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr13verify_keccak,@function
_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr13verify_keccak:
.Lfunc_begin48:
	.cfi_startproc
	stp	x29, x30, [sp, #-96]!
	.cfi_def_cfa_offset 96
	stp	x28, x27, [sp, #16]
	stp	x26, x25, [sp, #32]
	stp	x24, x23, [sp, #48]
	stp	x22, x21, [sp, #64]
	stp	x20, x19, [sp, #80]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w24, -48
	.cfi_offset w25, -56
	.cfi_offset w26, -64
	.cfi_offset w27, -72
	.cfi_offset w28, -80
	.cfi_offset w30, -88
	.cfi_offset w29, -96
	sub	sp, sp, #3264
	.cfi_def_cfa_offset 3360
	subs	x8, x1, #4
	ldr	xzr, [sp]
	mov	x20, x0
	csel	x8, xzr, x8, lo
	mov	w9, #4
	add	x10, x2, #64
	str	x8, [sp, #88]
	subs	x8, x3, #4
	mov	w11, #8
	mov	w0, #5
	mov	x29, x7
	mov	x23, x6
	mov	x22, x5
	mov	x19, x4
	mov	x28, x3
	mov	x21, x1
	mov	x24, x2
	csel	x27, x3, x9, lo
	csel	x25, xzr, x8, lo
	csel	x26, x11, x10, lo
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field10bit_length
	subs	w8, w0, #3
	mov	x0, x20
	csel	w1, wzr, w8, lo
	bl	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState5grind
	mov	w8, w0
	mov	w0, wzr
	cbz	w8, .LBB48_32
	add	x1, sp, #96
	mov	x0, x20
	mov	w2, #1
	stp	xzr, xzr, [sp, #96]
	bl	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState17sample_challenges
	add	x1, sp, #112
	mov	x0, x20
	mov	w2, #5
	stp	xzr, xzr, [sp, #112]
	stp	xzr, xzr, [sp, #128]
	stp	xzr, xzr, [sp, #144]
	stp	xzr, xzr, [sp, #160]
	stp	xzr, xzr, [sp, #176]
	bl	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState17sample_challenges
	add	x0, sp, #960
	mov	x1, x20
	bl	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState11read_scalar
	ldr	x8, [sp, #960]
	cbz	x8, .LBB48_31
	str	x29, [sp, #72]
	ldr	x29, [sp, #976]
	ldr	x6, [sp, #968]
	add	x0, sp, #960
	add	x3, sp, #96
	add	x4, sp, #112
	mov	x1, x24
	mov	x2, x28
	mov	x5, x19
	mov	x7, x29
	str	x6, [sp, #80]
	add	x28, sp, #960
	str	x22, [sp]
	bl	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr11first_claim
	ldr	w8, [sp, #960]
	tbz	w8, #0, .LBB48_31
	add	x0, sp, #2216
	add	x1, x28, #8
	mov	w2, #280
	str	x29, [sp, #56]
	bl	memcpy
	ldr	x29, [sp, #1248]
	add	x0, sp, #1736
	add	x1, x28, #296
	mov	w2, #480
	bl	memcpy
	add	x0, sp, #192
	add	x1, sp, #2216
	mov	w2, #280
	add	x19, sp, #192
	bl	memcpy
	add	x0, x19, #288
	add	x1, sp, #1736
	mov	w2, #480
	str	x29, [sp, #472]
	str	x0, [sp, #48]
	bl	memcpy
	add	x0, sp, #960
	add	x1, sp, #2216
	mov	w2, #280
	bl	memcpy
	add	x0, x28, #288
	add	x1, sp, #1736
	mov	w2, #480
	str	x29, [sp, #64]
	add	x19, x28, #288
	str	x29, [sp, #1240]
	bl	memcpy
	mov	w8, #25600
	mov	x1, x22
	mov	w2, #25600
	add	x0, x22, x8
	bl	memcpy
	add	x3, sp, #960
	mov	x0, x20
	mov	x1, x21
	mov	x2, xzr
	mov	x4, x22
	bl	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr12verify_layer
	tbz	w0, #0, .LBB48_31
	add	x3, sp, #960
	mov	x0, x20
	mov	x1, x21
	mov	w2, #1
	mov	x4, x22
	bl	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr12verify_layer
	cbz	w0, .LBB48_31
	add	x3, sp, #960
	mov	x0, x20
	mov	x1, x21
	mov	w2, #2
	mov	x4, x22
	bl	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr12verify_layer
	cbz	w0, .LBB48_31
	add	x3, sp, #960
	mov	x0, x20
	mov	x1, x21
	mov	w2, #3
	mov	x4, x22
	bl	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr12verify_layer
	cbz	w0, .LBB48_31
	add	x3, sp, #960
	mov	x0, x20
	mov	x1, x21
	mov	w2, #4
	mov	x4, x22
	bl	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr12verify_layer
	cbz	w0, .LBB48_31
	add	x3, sp, #960
	mov	x0, x20
	mov	x1, x21
	mov	w2, #5
	mov	x4, x22
	bl	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr12verify_layer
	cbz	w0, .LBB48_31
	add	x3, sp, #960
	mov	x0, x20
	mov	x1, x21
	mov	w2, #6
	mov	x4, x22
	bl	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr12verify_layer
	cbz	w0, .LBB48_31
	add	x3, sp, #960
	mov	x0, x20
	mov	x1, x21
	mov	w2, #7
	mov	x4, x22
	bl	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr12verify_layer
	cbz	w0, .LBB48_31
	add	x3, sp, #960
	mov	x0, x20
	mov	x1, x21
	mov	w2, #8
	mov	x4, x22
	bl	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr12verify_layer
	cbz	w0, .LBB48_31
	add	x3, sp, #960
	mov	x0, x20
	mov	x1, x21
	mov	w2, #9
	mov	x4, x22
	bl	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr12verify_layer
	cbz	w0, .LBB48_31
	add	x3, sp, #960
	mov	x0, x20
	mov	x1, x21
	mov	w2, #10
	mov	x4, x22
	bl	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr12verify_layer
	cbz	w0, .LBB48_31
	add	x3, sp, #960
	mov	x0, x20
	mov	x1, x21
	mov	w2, #11
	mov	x4, x22
	bl	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr12verify_layer
	cbz	w0, .LBB48_31
	ldr	x9, [sp, #64]
	ldr	x10, [sp, #48]
	mov	w8, #8
	add	x28, x22, #34, lsl #12
	add	x0, sp, #2592
	mov	x1, x20
	cmp	x9, #31
	mov	x2, x21
	mov	x5, x22
	csel	x3, x10, x8, lo
	csel	x4, x9, xzr, lo
	add	x10, x28, #1024
	add	x8, sp, #2496
	add	x9, x28, #1024
	mov	w6, #1
	str	x9, [sp, #64]
	ldr	x9, [sp, #56]
	mov	w7, #1
	stp	x8, x10, [sp, #16]
	ldr	x8, [sp, #80]
	str	x19, [sp, #40]
	str	xzr, [sp, #2496]
	str	xzr, [sp, #2504]
	str	xzr, [sp, #2512]
	str	xzr, [sp, #2520]
	str	xzr, [sp, #2528]
	str	xzr, [sp, #2536]
	str	xzr, [sp, #2544]
	str	xzr, [sp, #2552]
	str	xzr, [sp, #2560]
	str	xzr, [sp, #2568]
	str	xzr, [sp, #2576]
	str	xzr, [sp, #2584]
	stp	x8, x9, [sp]
	bl	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr11keccak_open
	ldr	x8, [sp, #2592]
	cbz	x8, .LBB48_31
	ldr	x29, [sp, #2600]
	ldr	x19, [sp, #2608]
	add	x0, sp, #2592
	mov	x1, x20
	bl	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState11read_scalar
	ldr	w8, [sp, #2592]
	tbz	w8, #0, .LBB48_31
	ldr	x2, [sp, #2600]
	ldr	x3, [sp, #2608]
	ldr	x0, [x28, #1024]
	ldr	x1, [x28, #1032]
	mov	x28, x2
	str	x3, [sp, #80]
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	cmp	x0, x29
	b.ne	.LBB48_31
	cmp	x1, x19
	b.ne	.LBB48_31
	add	x0, sp, #2592
	mov	x1, x24
	mov	x2, x27
	str	xzr, [sp, #2600]
	add	x19, sp, #2592
	str	xzr, [sp, #2608]
	str	xzr, [sp, #2616]
	str	xzr, [sp, #2624]
	str	xzr, [sp, #2632]
	str	xzr, [sp, #2640]
	str	xzr, [sp, #2648]
	str	xzr, [sp, #2656]
	str	xzr, [sp, #2664]
	str	xzr, [sp, #2672]
	str	xzr, [sp, #2680]
	str	xzr, [sp, #2688]
	str	xzr, [sp, #2696]
	str	xzr, [sp, #2704]
	str	xzr, [sp, #2712]
	str	xzr, [sp, #2720]
	str	xzr, [sp, #2728]
	str	xzr, [sp, #2736]
	str	xzr, [sp, #2744]
	str	xzr, [sp, #2752]
	str	xzr, [sp, #2760]
	str	xzr, [sp, #2768]
	str	xzr, [sp, #2776]
	str	xzr, [sp, #2784]
	str	xzr, [sp, #2792]
	str	xzr, [sp, #2800]
	str	xzr, [sp, #2808]
	str	xzr, [sp, #2816]
	str	xzr, [sp, #2824]
	str	xzr, [sp, #2832]
	str	xzr, [sp, #2840]
	str	xzr, [sp, #2848]
	str	xzr, [sp, #2856]
	str	xzr, [sp, #2864]
	str	xzr, [sp, #2872]
	str	xzr, [sp, #2880]
	str	xzr, [sp, #2888]
	str	xzr, [sp, #2896]
	str	xzr, [sp, #2904]
	str	xzr, [sp, #2912]
	str	xzr, [sp, #2920]
	str	xzr, [sp, #2928]
	str	xzr, [sp, #2936]
	str	xzr, [sp, #2944]
	str	xzr, [sp, #2952]
	str	xzr, [sp, #2960]
	str	xzr, [sp, #2968]
	str	xzr, [sp, #2976]
	str	xzr, [sp, #2984]
	str	xzr, [sp, #2992]
	str	xzr, [sp, #3000]
	str	xzr, [sp, #3008]
	str	xzr, [sp, #3016]
	str	xzr, [sp, #3024]
	str	xzr, [sp, #3032]
	str	xzr, [sp, #3040]
	str	xzr, [sp, #3048]
	str	xzr, [sp, #3056]
	str	xzr, [sp, #3064]
	str	xzr, [sp, #3072]
	str	xzr, [sp, #3080]
	str	xzr, [sp, #3088]
	str	xzr, [sp, #3096]
	str	xzr, [sp, #3104]
	str	xzr, [sp, #3112]
	str	xzr, [sp, #3120]
	str	xzr, [sp, #3128]
	str	xzr, [sp, #3136]
	str	xzr, [sp, #3144]
	str	xzr, [sp, #3152]
	str	xzr, [sp, #3160]
	str	xzr, [sp, #3168]
	str	xzr, [sp, #2592]
	bl	_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKj24_E6extendB4_
	cbz	w0, .LBB48_31
	add	x0, sp, #2592
	mov	x1, x26
	mov	x2, x25
	bl	_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKj24_E6extendB4_
	tbz	w0, #0, .LBB48_31
	add	x0, sp, #2592
	add	x1, sp, #2496
	mov	w2, #6
	bl	_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKj24_E6extendB4_
	cbz	w0, .LBB48_31
	ldr	x8, [sp, #2592]
	add	x9, x19, #8
	mov	w10, #8
	ldr	x5, [sp, #80]
	mov	x0, x23
	mov	w1, #4
	cmp	x8, #37
	mov	x4, x28
	csel	x2, x9, x10, lo
	csel	x3, x8, xzr, lo
	bl	_RNvNtCsemcRClSg8DH_9native_vm5stack10push_claim
	cbz	w0, .LBB48_31
	ldr	x2, [sp, #960]
	ldr	x3, [sp, #968]
	add	x0, sp, #3240
	add	x5, sp, #3176
	mov	x1, x20
	mov	w4, #3
	mov	w6, #4
	str	xzr, [sp, #3176]
	str	xzr, [sp, #3184]
	str	xzr, [sp, #3192]
	str	xzr, [sp, #3200]
	str	xzr, [sp, #3208]
	str	xzr, [sp, #3216]
	str	xzr, [sp, #3224]
	str	xzr, [sp, #3232]
	bl	_RINvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB6_6TState8sumcheckNCNvB2_14sumcheck_plain0EB8_
	ldr	x8, [sp, #3240]
	cbz	x8, .LBB48_31
	ldr	x8, [sp, #1240]
	ldr	x12, [sp, #40]
	mov	w11, #8
	ldr	x9, [sp, #3248]
	ldr	x10, [sp, #3256]
	mov	x6, xzr
	cmp	x8, #31
	add	x0, sp, #3240
	mov	x1, x20
	csel	x23, x12, x11, lo
	ldr	x11, [sp, #64]
	csel	x24, x8, xzr, lo
	add	x8, sp, #2496
	mov	x2, x21
	mov	x3, x23
	stp	x8, x11, [sp, #16]
	mov	w11, #25600
	mov	x4, x24
	add	x5, x22, x11
	mov	w7, #2
	stp	x9, x10, [sp]
	bl	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr11keccak_open
	ldr	w8, [sp, #3240]
	tbz	w8, #0, .LBB48_31
	ldr	x8, [sp, #72]
	ldr	x22, [sp, #3248]
	mov	x0, x20
	ldr	x21, [sp, #3256]
	mov	w2, #64
	add	x1, x8, #584
	bl	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState12read_scalars
	tbz	w0, #0, .LBB48_31
	ldr	x8, [sp, #976]
	add	x9, sp, #960
	mov	w10, #8
	add	x9, x9, #24
	add	x3, sp, #3176
	mov	w4, #4
	cmp	x8, #17
	csel	x0, x8, xzr, lo
	csel	x1, x9, x10, lo
	mov	x2, x0
	bl	_RINvNtCsemcRClSg8DH_9native_vm5field19multilinear_eval_byNCNvB2_16multilinear_eval0EB4_
	mov	x19, x0
	ldp	x0, x8, [sp, #64]
	mov	x20, x1
	mov	w1, #64
	mov	w3, #64
	add	x2, x8, #584
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field3dot
	mov	x2, x0
	mov	x3, x1
	mov	x0, x19
	mov	x1, x20
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	cmp	x0, x22
	b.ne	.LBB48_31
	cmp	x1, x21
	b.ne	.LBB48_31
	ldr	x0, [sp, #72]
	add	x1, sp, #3176
	mov	w2, #4
	str	xzr, [x0]
	bl	_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKj24_E6extendB4_
	cbz	w0, .LBB48_31
	ldr	x8, [sp, #88]
	ldr	x0, [sp, #72]
	mov	x1, x23
	cmp	x8, x24
	csel	x2, x8, x24, lo
	bl	_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKj24_E6extendB4_
	cbz	w0, .LBB48_31
	ldr	x0, [sp, #72]
	add	x1, sp, #2496
	mov	w2, #6
	bl	_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKj24_E6extendB4_
	b	.LBB48_32
.LBB48_31:
	mov	w0, wzr
.LBB48_32:
	add	sp, sp, #3264
	.cfi_def_cfa_offset 96
	ldp	x20, x19, [sp, #80]
	ldp	x22, x21, [sp, #64]
	ldp	x24, x23, [sp, #48]
	ldp	x26, x25, [sp, #32]
	ldp	x28, x27, [sp, #16]
	ldp	x29, x30, [sp], #96
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w25
	.cfi_restore w26
	.cfi_restore w27
	.cfi_restore w28
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end48:
	.size	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr13verify_keccak, .Lfunc_end48-_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr13verify_keccak
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr16instance_weights,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr16instance_weights,@function
_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr16instance_weights:
.Lfunc_begin49:
	.cfi_startproc
	stp	x29, x30, [sp, #-96]!
	.cfi_def_cfa_offset 96
	stp	x28, x27, [sp, #16]
	stp	x26, x25, [sp, #32]
	stp	x24, x23, [sp, #48]
	stp	x22, x21, [sp, #64]
	stp	x20, x19, [sp, #80]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w24, -48
	.cfi_offset w25, -56
	.cfi_offset w26, -64
	.cfi_offset w27, -72
	.cfi_offset w28, -80
	.cfi_offset w30, -88
	.cfi_offset w29, -96
	sub	sp, sp, #880
	.cfi_def_cfa_offset 976
	mov	x8, x2
	str	x0, [sp, #24]
	add	x2, sp, #232
	mov	x0, x1
	mov	x1, x8
	mov	w3, #24
	stp	xzr, xzr, [sp, #232]
	stp	xzr, xzr, [sp, #248]
	stp	xzr, xzr, [sp, #264]
	stp	xzr, xzr, [sp, #280]
	stp	xzr, xzr, [sp, #296]
	stp	xzr, xzr, [sp, #312]
	stp	xzr, xzr, [sp, #328]
	stp	xzr, xzr, [sp, #344]
	stp	xzr, xzr, [sp, #360]
	stp	xzr, xzr, [sp, #376]
	stp	xzr, xzr, [sp, #392]
	stp	xzr, xzr, [sp, #408]
	stp	xzr, xzr, [sp, #424]
	stp	xzr, xzr, [sp, #440]
	stp	xzr, xzr, [sp, #456]
	stp	xzr, xzr, [sp, #472]
	stp	xzr, xzr, [sp, #488]
	stp	xzr, xzr, [sp, #504]
	str	xzr, [sp, #520]
	str	xzr, [sp, #528]
	str	xzr, [sp, #536]
	str	xzr, [sp, #544]
	str	xzr, [sp, #552]
	str	xzr, [sp, #560]
	str	xzr, [sp, #568]
	str	xzr, [sp, #576]
	str	xzr, [sp, #584]
	str	xzr, [sp, #592]
	str	xzr, [sp, #600]
	str	xzr, [sp, #608]
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field6powers
	ldp	x10, x8, [sp, #232]
	mov	w9, #16
	ldp	x11, x12, [sp, #248]
	str	x9, [sp, #616]
	ldp	x13, x15, [sp, #280]
	str	xzr, [sp, #624]
	str	xzr, [sp, #632]
	ldr	x4, [sp, #600]
	ldr	x3, [sp, #608]
	eor	x10, x10, x11
	eor	x8, x8, x12
	stp	x12, x11, [sp, #216]
	ldr	x1, [sp, #568]
	ldr	x2, [sp, #576]
	str	x15, [sp, #128]
	ldp	x14, x16, [sp, #360]
	stp	x3, x4, [sp, #8]
	mov	w3, #1
	str	xzr, [sp, #648]
	ldp	x17, x0, [sp, #456]
	eor	x11, x13, x14
	stp	x14, x13, [sp, #136]
	eor	x10, x10, x11
	str	xzr, [sp, #656]
	str	x0, [sp, #80]
	ldp	x14, x18, [sp, #392]
	str	xzr, [sp, #664]
	ldp	x28, x29, [sp, #408]
	str	xzr, [sp, #672]
	ldp	x30, x19, [sp, #424]
	eor	x11, x14, x17
	stp	x17, x14, [sp, #112]
	ldr	x17, [sp, #592]
	stp	x18, x16, [sp, #96]
	ldp	x13, x14, [sp, #472]
	mov	x22, x17
	str	xzr, [sp, #680]
	str	xzr, [sp, #688]
	eor	x11, x11, x13
	stp	x14, x13, [sp, #200]
	ldr	x13, [sp, #584]
	eor	x9, x10, x11
	add	x10, sp, #616
	add	x6, x10, #32
	eor	x9, x9, x13
	str	x13, [sp, #88]
	str	x9, [sp, #624]
	ldp	x11, x10, [sp, #264]
	str	xzr, [sp, #696]
	ldp	x13, x12, [sp, #376]
	str	xzr, [sp, #704]
	stp	x10, x11, [sp, #168]
	ldp	x11, x10, [sp, #296]
	stp	x12, x13, [sp, #152]
	ldr	x12, [sp, #520]
	ldr	x13, [sp, #544]
	str	xzr, [sp, #712]
	stp	x11, x10, [sp, #184]
	ldp	x11, x10, [sp, #312]
	str	xzr, [sp, #720]
	str	xzr, [sp, #728]
	stp	x10, x11, [sp, #64]
	ldp	x11, x10, [sp, #328]
	str	xzr, [sp, #736]
	str	xzr, [sp, #744]
	stp	x10, x11, [sp, #48]
	ldp	x11, x10, [sp, #344]
	str	xzr, [sp, #752]
	str	xzr, [sp, #760]
	stp	x10, x11, [sp, #32]
	eor	x10, x15, x16
	eor	x11, x18, x0
	eor	x8, x8, x10
	eor	x10, x11, x14
	ldr	x16, [sp, #528]
	eor	x8, x8, x10
	ldp	x11, x10, [sp, #488]
	eor	x8, x8, x17
	ldp	x14, x15, [sp, #504]
	str	x8, [sp, #632]
	ldp	x8, x9, [sp, #440]
	ldr	x17, [sp, #536]
	ldr	x18, [sp, #552]
	ldr	x0, [sp, #560]
	str	xzr, [sp, #768]
	str	xzr, [sp, #776]
	str	xzr, [sp, #784]
	str	xzr, [sp, #792]
	str	xzr, [sp, #800]
	str	xzr, [sp, #808]
	str	xzr, [sp, #816]
	str	xzr, [sp, #824]
	str	xzr, [sp, #832]
	str	xzr, [sp, #840]
	str	xzr, [sp, #848]
	str	xzr, [sp, #856]
	str	xzr, [sp, #864]
	str	xzr, [sp, #640]
	str	xzr, [sp, #872]
.LBB49_1:
	mov	w4, #1
	mov	w5, #15624
	mov	w23, #58498
	lsl	x4, x4, x3
	mov	w24, #20685
	mov	w25, #54717
	mov	w26, #25753
	mov	w27, #53088
	add	x3, x3, #1
	tst	x4, x5
	ldp	x5, x7, [sp, #216]
	csel	x20, x7, xzr, eq
	mov	w7, #12311
	csel	x5, x5, xzr, eq
	tst	x4, x7
	ldr	x7, [sp, #168]
	csel	x21, x7, xzr, eq
	ldr	x7, [sp, #176]
	eor	x5, x5, x21
	ldr	x21, [sp, #128]
	csel	x7, x7, xzr, eq
	tst	x4, x23
	ldr	x23, [sp, #144]
	csel	x21, x21, xzr, eq
	eor	x7, x20, x7
	csel	x23, x23, xzr, eq
	tst	x4, x24
	ldp	x24, x20, [sp, #184]
	csel	x20, x20, xzr, eq
	csel	x24, x24, xzr, eq
	tst	x4, x25
	eor	x20, x21, x20
	eor	x21, x23, x24
	mov	w25, #49197
	ldp	x23, x24, [sp, #64]
	eor	x5, x5, x20
	eor	x7, x7, x21
	ldp	x20, x21, [sp, #48]
	csel	x23, x23, xzr, eq
	csel	x24, x24, xzr, eq
	tst	x4, x25
	csel	x20, x20, xzr, eq
	csel	x21, x21, xzr, eq
	mov	w25, #42701
	eor	x20, x23, x20
	eor	x21, x24, x21
	tst	x4, x25
	ldp	x23, x24, [sp, #32]
	mov	w25, #7467
	csel	x23, x23, xzr, eq
	csel	x24, x24, xzr, eq
	eor	x20, x20, x23
	eor	x21, x21, x24
	mov	w23, #40940
	tst	x4, x23
	ldr	x23, [sp, #104]
	ldr	x24, [sp, #136]
	eor	x5, x5, x20
	eor	x7, x7, x21
	ldp	x20, x21, [sp, #152]
	csel	x23, x23, xzr, eq
	csel	x24, x24, xzr, eq
	tst	x4, x25
	ldr	x25, [sp, #120]
	csel	x20, x20, xzr, eq
	csel	x21, x21, xzr, eq
	eor	x20, x23, x20
	mov	w23, #49282
	eor	x21, x24, x21
	tst	x4, x23
	ldr	x23, [sp, #96]
	mov	w24, #42677
	csel	x25, x25, xzr, eq
	csel	x23, x23, xzr, eq
	tst	x4, x26
	eor	x21, x21, x25
	eor	x20, x20, x23
	csel	x23, x29, xzr, eq
	mov	w25, #28094
	eor	x20, x20, x23
	csel	x23, x28, xzr, eq
	mov	w26, #39237
	eor	x5, x5, x20
	eor	x20, x21, x23
	mov	w21, #32773
	tst	x4, x21
	eor	x7, x7, x20
	csel	x21, x19, xzr, eq
	csel	x23, x30, xzr, eq
	tst	x4, x24
	csel	x20, x9, xzr, eq
	csel	x24, x8, xzr, eq
	eor	x20, x21, x20
	eor	x21, x23, x24
	mov	w23, #36448
	tst	x4, x23
	ldr	x23, [sp, #80]
	ldr	x24, [sp, #112]
	csel	x23, x23, xzr, eq
	csel	x24, x24, xzr, eq
	tst	x4, x25
	eor	x20, x20, x23
	ldr	x23, [sp, #200]
	eor	x21, x21, x24
	mov	w24, #21193
	mov	w25, #52125
	csel	x23, x23, xzr, eq
	eor	x20, x20, x23
	ldr	x23, [sp, #208]
	csel	x23, x23, xzr, eq
	tst	x4, x24
	eor	x21, x21, x23
	csel	x23, x10, xzr, eq
	csel	x24, x11, xzr, eq
	eor	x20, x20, x23
	mov	w23, #56289
	eor	x21, x21, x24
	tst	x4, x23
	eor	x7, x7, x21
	eor	x5, x5, x20
	csel	x23, x15, xzr, eq
	csel	x24, x14, xzr, eq
	tst	x4, x25
	csel	x21, x16, xzr, eq
	csel	x25, x12, xzr, eq
	eor	x21, x23, x21
	eor	x23, x24, x25
	mov	w24, #43609
	tst	x4, x24
	csel	x24, x13, xzr, eq
	csel	x25, x17, xzr, eq
	tst	x4, x26
	eor	x21, x21, x24
	eor	x23, x23, x25
	csel	x24, x18, xzr, eq
	eor	x23, x23, x24
	mov	w24, #55157
	csel	x25, x0, xzr, eq
	tst	x4, x24
	csel	x26, x1, xzr, eq
	csel	x24, x2, xzr, eq
	tst	x4, x27
	eor	x4, x21, x25
	eor	x21, x23, x26
	ldr	x23, [sp, #88]
	eor	x4, x4, x24
	csel	x23, x23, xzr, eq
	eor	x21, x21, x23
	csel	x23, x22, xzr, eq
	cmp	x3, #15
	eor	x4, x4, x23
	eor	x7, x7, x21
	eor	x4, x5, x4
	stp	x7, x4, [x6, #-8]
	add	x6, x6, #16
	b.ne	.LBB49_1
	ldp	x8, x12, [sp, #168]
	add	x1, sp, #616
	ldp	x9, x13, [sp, #8]
	mov	w2, #264
	ldp	x15, x14, [sp, #216]
	ldr	x0, [sp, #24]
	eor	x8, x8, x9
	eor	x12, x12, x13
	ldp	x9, x13, [sp, #152]
	eor	x8, x8, x15
	eor	x12, x12, x14
	ldp	x14, x15, [sp, #200]
	eor	x13, x13, x28
	eor	x9, x9, x29
	eor	x13, x13, x15
	eor	x9, x9, x14
	eor	x11, x13, x11
	ldp	x14, x13, [sp, #184]
	eor	x9, x9, x10
	eor	x12, x12, x14
	eor	x8, x8, x13
	eor	x10, x12, x11
	eor	x8, x8, x9
	str	x10, [sp, #864]
	str	x8, [sp, #872]
	bl	memcpy
	add	sp, sp, #880
	.cfi_def_cfa_offset 96
	ldp	x20, x19, [sp, #80]
	ldp	x22, x21, [sp, #64]
	ldp	x24, x23, [sp, #48]
	ldp	x26, x25, [sp, #32]
	ldp	x28, x27, [sp, #16]
	ldp	x29, x30, [sp], #96
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w25
	.cfi_restore w26
	.cfi_restore w27
	.cfi_restore w28
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end49:
	.size	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr16instance_weights, .Lfunc_end49-_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr16instance_weights
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr16linear_transpose,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr16linear_transpose,@function
_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr16linear_transpose:
.Lfunc_begin50:
	.cfi_startproc
	str	x30, [sp, #-80]!
	.cfi_def_cfa_offset 80
	stp	x26, x25, [sp, #16]
	stp	x24, x23, [sp, #32]
	stp	x22, x21, [sp, #48]
	stp	x20, x19, [sp, #64]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w24, -48
	.cfi_offset w25, -56
	.cfi_offset w26, -64
	.cfi_offset w30, -80
	mov	x21, x3
	mov	x19, x2
	mov	x20, x1
	mov	x22, x0
	mov	x23, xzr
	add	x24, x1, #8
	add	x25, x1, #16
	adrp	x26, .Lanon.a75d6d9e6a8990b4224ef13f18552af8.2
	add	x26, x26, :lo12:.Lanon.a75d6d9e6a8990b4224ef13f18552af8.2
	b	.LBB50_2
.LBB50_1:
	add	x23, x23, #1
	add	x24, x24, #1024
	add	x25, x25, #1024
	cmp	x23, #25
	b.eq	.LBB50_7
.LBB50_2:
	mov	x0, x23
	bl	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr9keccak_pi
	ldr	w8, [x26, x23, lsl #2]
	add	x9, x22, x0, lsl #10
	cbz	x23, .LBB50_5
	mov	w10, #64
	mov	x11, x24
.LBB50_4:
	and	x12, x8, #0x3f
	subs	x10, x10, #1
	add	x8, x8, #1
	add	x12, x9, x12, lsl #4
	ldp	x13, x12, [x12]
	stp	x13, x12, [x11, #-8]
	add	x11, x11, #16
	b.ne	.LBB50_4
	b	.LBB50_1
.LBB50_5:
	mov	x10, x25
	mov	w11, #64
.LBB50_6:
	and	x12, x8, #0x3f
	add	w13, w8, #1
	subs	x11, x11, #2
	add	x12, x9, x12, lsl #4
	and	x13, x13, #0x3f
	add	x8, x8, #2
	add	x13, x9, x13, lsl #4
	ldp	x14, x12, [x12]
	stp	x14, x12, [x10, #-16]
	ldp	x14, x13, [x13]
	stp	x14, x13, [x10], #32
	b.ne	.LBB50_6
	b	.LBB50_1
.LBB50_7:
	add	x8, x19, #8
	mov	w9, #64
	mov	x10, x20
.LBB50_8:
	ldp	x11, x12, [x10]
	subs	x9, x9, #1
	ldr	x13, [x10, #5120]
	ldr	x14, [x10, #5128]
	ldr	x15, [x10, #10240]
	ldr	x16, [x10, #15360]
	ldr	x17, [x10, #15368]
	eor	x11, x13, x11
	ldr	x13, [x10, #10248]
	eor	x12, x14, x12
	eor	x14, x16, x15
	ldr	x15, [x10, #20480]
	eor	x11, x14, x11
	eor	x13, x17, x13
	ldr	x14, [x10, #20488]
	eor	x12, x13, x12
	eor	x11, x15, x11
	add	x10, x10, #16
	eor	x12, x14, x12
	stp	x11, x12, [x8, #-8]
	add	x8, x8, #16
	b.ne	.LBB50_8
	add	x8, x19, #1032
	mov	w9, #64
	mov	x10, x20
.LBB50_10:
	ldr	x11, [x10, #1024]
	ldr	x13, [x10, #6144]
	subs	x9, x9, #1
	ldr	x12, [x10, #1032]
	ldr	x14, [x10, #6152]
	ldr	x15, [x10, #11264]
	ldr	x16, [x10, #16384]
	eor	x11, x13, x11
	ldr	x13, [x10, #11272]
	ldr	x17, [x10, #16392]
	eor	x12, x14, x12
	eor	x14, x16, x15
	ldr	x15, [x10, #21504]
	eor	x11, x14, x11
	eor	x13, x17, x13
	ldr	x14, [x10, #21512]
	eor	x12, x13, x12
	eor	x11, x15, x11
	add	x10, x10, #16
	eor	x12, x14, x12
	stp	x11, x12, [x8, #-8]
	add	x8, x8, #16
	b.ne	.LBB50_10
	add	x8, x19, #2048
	mov	x9, #-1024
.LBB50_12:
	add	x10, x20, x9
	ldr	x11, [x10, #3072]
	ldr	x13, [x10, #8192]
	ldr	x12, [x10, #3080]
	ldr	x14, [x10, #8200]
	ldr	x15, [x10, #13312]
	ldr	x16, [x10, #18432]
	ldr	x17, [x10, #13320]
	eor	x11, x13, x11
	ldr	x13, [x10, #18440]
	eor	x12, x14, x12
	eor	x14, x16, x15
	ldr	x15, [x10, #23552]
	eor	x13, x13, x17
	ldr	x10, [x10, #23560]
	eor	x11, x14, x11
	eor	x12, x13, x12
	eor	x11, x15, x11
	add	x13, x8, x9
	eor	x10, x10, x12
	adds	x9, x9, #16
	str	x11, [x13, #1024]
	str	x10, [x13, #1032]
	b.ne	.LBB50_12
	add	x8, x19, #3080
	mov	w9, #64
	mov	x10, x20
.LBB50_14:
	ldr	x11, [x10, #3072]
	ldr	x13, [x10, #8192]
	subs	x9, x9, #1
	ldr	x12, [x10, #3080]
	ldr	x14, [x10, #8200]
	ldr	x15, [x10, #13312]
	ldr	x16, [x10, #18432]
	eor	x11, x13, x11
	ldr	x13, [x10, #13320]
	ldr	x17, [x10, #18440]
	eor	x12, x14, x12
	eor	x14, x16, x15
	ldr	x15, [x10, #23552]
	eor	x11, x14, x11
	eor	x13, x17, x13
	ldr	x14, [x10, #23560]
	eor	x12, x13, x12
	eor	x11, x15, x11
	add	x10, x10, #16
	eor	x12, x14, x12
	stp	x11, x12, [x8, #-8]
	add	x8, x8, #16
	b.ne	.LBB50_14
	mov	w8, #4104
	mov	w9, #64
	mov	x10, x20
	add	x8, x19, x8
.LBB50_16:
	ldr	x11, [x10, #4096]
	ldr	x13, [x10, #9216]
	subs	x9, x9, #1
	ldr	x12, [x10, #4104]
	ldr	x14, [x10, #9224]
	ldr	x15, [x10, #14336]
	ldr	x16, [x10, #19456]
	eor	x11, x13, x11
	ldr	x13, [x10, #14344]
	ldr	x17, [x10, #19464]
	eor	x12, x14, x12
	eor	x14, x16, x15
	ldr	x15, [x10, #24576]
	eor	x11, x14, x11
	eor	x13, x17, x13
	ldr	x14, [x10, #24584]
	eor	x12, x13, x12
	eor	x11, x15, x11
	add	x10, x10, #16
	eor	x12, x14, x12
	stp	x11, x12, [x8, #-8]
	add	x8, x8, #16
	b.ne	.LBB50_16
	mov	x12, #-3689348814741910324
	mov	x8, xzr
	add	x9, x19, #8
	add	x10, x21, #8
	add	x11, x20, #8
	movk	x12, #52429
	mov	w13, #4096
.LBB50_18:
	umulh	x14, x8, x12
	mov	w18, #1
	lsr	x14, x14, #2
	add	x14, x14, x14, lsl #2
	sub	x14, x8, x14
	add	x15, x14, #1
	lsl	x16, x14, #10
	lsl	x17, x15, #6
	cmp	x15, #5
	sub	x15, x16, #1024
	csel	x16, xzr, x17, eq
	cmp	x14, #0
	mov	x17, x10
	csel	x15, x13, x15, eq
	add	x14, x9, x16, lsl #4
	mov	x16, x11
	add	x15, x19, x15
.LBB50_19:
	and	x0, x18, #0x3f
	ldp	x1, x4, [x14, #-8]
	add	x0, x15, x0, lsl #4
	ldp	x2, x3, [x16, #-8]
	add	x18, x18, #1
	add	x14, x14, #16
	add	x16, x16, #16
	ldp	x5, x0, [x0]
	cmp	x18, #65
	eor	x1, x1, x2
	eor	x2, x4, x3
	eor	x1, x1, x5
	eor	x0, x2, x0
	stp	x1, x0, [x17, #-8]
	add	x17, x17, #16
	b.ne	.LBB50_19
	add	x8, x8, #1
	add	x10, x10, #1024
	add	x11, x11, #1024
	cmp	x8, #25
	b.ne	.LBB50_18
	ldp	x20, x19, [sp, #64]
	ldp	x22, x21, [sp, #48]
	ldp	x24, x23, [sp, #32]
	ldp	x26, x25, [sp, #16]
	ldr	x30, [sp], #80
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w25
	.cfi_restore w26
	.cfi_restore w30
	ret
.Lfunc_end50:
	.size	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr16linear_transpose, .Lfunc_end50-_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr16linear_transpose
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr9keccak_pi,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr9keccak_pi,@function
_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr9keccak_pi:
.Lfunc_begin51:
	.cfi_startproc
	mov	w8, #205
	mov	x10, #-3689348814741910324
	mul	w8, w0, w8
	movk	x10, #52429
	ubfx	x8, x8, #10, #6
	sub	x9, x8, x8, lsl #3
	add	x9, x9, x0, lsl #1
	umulh	x10, x9, x10
	lsr	x10, x10, #2
	add	x10, x10, x10, lsl #2
	sub	x9, x9, x10
	add	x9, x9, x9, lsl #2
	add	x0, x9, x8
	ret
.Lfunc_end51:
	.size	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr9keccak_pi, .Lfunc_end51-_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr9keccak_pi
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm10transcript10open_phase,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm10transcript10open_phase,@function
_RNvNtCsemcRClSg8DH_9native_vm10transcript10open_phase:
.Lfunc_begin52:
	.cfi_startproc
	sub	sp, sp, #176
	.cfi_def_cfa_offset 176
	stp	x29, x30, [sp, #80]
	stp	x28, x27, [sp, #96]
	stp	x26, x25, [sp, #112]
	stp	x24, x23, [sp, #128]
	stp	x22, x21, [sp, #144]
	stp	x20, x19, [sp, #160]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w24, -48
	.cfi_offset w25, -56
	.cfi_offset w26, -64
	.cfi_offset w27, -72
	.cfi_offset w28, -80
	.cfi_offset w30, -88
	.cfi_offset w29, -96
	ldp	x23, x22, [x6]
	mov	x20, x6
	ldr	x21, [x6, #16]
	mov	x19, x0
	cbz	x23, .LBB52_4
	cmp	x21, x3
	b.ne	.LBB52_18
	cmp	x23, x5
	b.ne	.LBB52_18
	cmp	x22, x2
	b.eq	.LBB52_5
	b	.LBB52_18
.LBB52_4:
	cbnz	x5, .LBB52_18
.LBB52_5:
	lsl	x8, x5, #3
	add	x9, x20, #24
.LBB52_6:
	cbz	x8, .LBB52_8
	ldr	x10, [x4], #8
	ldr	x11, [x9]
	sub	x8, x8, #8
	add	x9, x9, #1544
	cmp	x11, x10
	b.eq	.LBB52_6
	b	.LBB52_18
.LBB52_8:
	add	x8, x20, #24
	str	x8, [sp]
	cbz	x23, .LBB52_17
	cmp	x21, #192
	b.hi	.LBB52_18
	ldp	x26, x27, [x1]
	lsl	x8, x21, #3
	ldp	x28, x29, [x1, #16]
	mov	w25, #2048
	movk	w25, #6, lsl #16
	mov	x24, x23
	str	x8, [sp, #8]
.LBB52_11:
	cbz	x25, .LBB52_18
	ldr	x2, [sp, #8]
	add	x0, sp, #48
	add	x3, x20, #32
	mov	x1, x21
	mov	x4, x21
	bl	_RINvNtCsemcRClSg8DH_9native_vm6keccak15keccak256_wordsNCNvB2_10hash_words0EB4_
	ldr	x2, [x20, #24]
	add	x0, sp, #16
	add	x1, sp, #48
	add	x3, x20, #544
	mov	x4, x22
	bl	_RNvNtCsemcRClSg8DH_9native_vm10transcript5climb
	ldr	x8, [sp, #16]
	cmp	x8, x26
	b.ne	.LBB52_18
	ldr	x8, [sp, #24]
	cmp	x8, x27
	b.ne	.LBB52_18
	ldr	x8, [sp, #32]
	cmp	x8, x28
	b.ne	.LBB52_18
	ldr	x8, [sp, #40]
	cmp	x8, x29
	b.ne	.LBB52_18
	subs	x24, x24, #1
	add	x20, x20, #1544
	sub	x25, x25, #1544
	b.ne	.LBB52_11
.LBB52_17:
	ldr	x9, [sp]
	mov	w8, #49408
	stp	x23, x21, [x19, #16]
	stp	x9, x8, [x19]
	b	.LBB52_19
.LBB52_18:
	str	xzr, [x19]
.LBB52_19:
	ldp	x20, x19, [sp, #160]
	ldp	x22, x21, [sp, #144]
	ldp	x24, x23, [sp, #128]
	ldp	x26, x25, [sp, #112]
	ldp	x28, x27, [sp, #96]
	ldp	x29, x30, [sp, #80]
	add	sp, sp, #176
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w25
	.cfi_restore w26
	.cfi_restore w27
	.cfi_restore w28
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end52:
	.size	_RNvNtCsemcRClSg8DH_9native_vm10transcript10open_phase, .Lfunc_end52-_RNvNtCsemcRClSg8DH_9native_vm10transcript10open_phase
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm10transcript5climb,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm10transcript5climb,@function
_RNvNtCsemcRClSg8DH_9native_vm10transcript5climb:
.Lfunc_begin53:
	.cfi_startproc
	sub	sp, sp, #144
	.cfi_def_cfa_offset 144
	stp	x30, x23, [sp, #96]
	stp	x22, x21, [sp, #112]
	stp	x20, x19, [sp, #128]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w30, -48
	ldp	x8, x9, [x1]
	mov	x19, x0
	stp	x8, x9, [sp]
	ldp	x8, x10, [x1, #16]
	stp	x8, x10, [sp, #16]
	cbz	x4, .LBB53_8
	mov	x20, x4
	mov	x21, x2
	mov	x22, xzr
	add	x23, x3, #16
	b	.LBB53_4
.LBB53_2:
	mov	x1, sp
	add	x2, sp, #32
.LBB53_3:
	bl	_RNvNtCsemcRClSg8DH_9native_vm6keccak9hash_pair
	ldp	x8, x9, [sp, #64]
	lsr	x21, x21, #1
	subs	x20, x20, #1
	add	x23, x23, #32
	add	x22, x22, #4
	stp	x8, x9, [sp]
	ldp	x8, x10, [sp, #80]
	stp	x8, x10, [sp, #16]
	b.eq	.LBB53_8
.LBB53_4:
	cmp	x22, #124
	b.hi	.LBB53_6
	ldp	x8, x9, [x23, #-16]
	stp	x8, x9, [sp, #32]
	ldp	x8, x10, [x23]
	stp	x8, x10, [sp, #48]
	add	x0, sp, #64
	tbz	w21, #0, .LBB53_2
	b	.LBB53_7
.LBB53_6:
	stp	xzr, xzr, [sp, #48]
	stp	xzr, xzr, [sp, #32]
	add	x0, sp, #64
	tbz	w21, #0, .LBB53_2
.LBB53_7:
	add	x1, sp, #32
	mov	x2, sp
	b	.LBB53_3
.LBB53_8:
	ldp	x8, x9, [sp]
	ldp	x22, x21, [sp, #112]
	ldp	x30, x23, [sp, #96]
	stp	x8, x9, [x19]
	ldp	x8, x10, [sp, #16]
	stp	x8, x10, [x19, #16]
	ldp	x20, x19, [sp, #128]
	add	sp, sp, #144
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w30
	ret
.Lfunc_end53:
	.size	_RNvNtCsemcRClSg8DH_9native_vm10transcript5climb, .Lfunc_end53-_RNvNtCsemcRClSg8DH_9native_vm10transcript5climb
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm11ring_switch11ring_switch,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm11ring_switch11ring_switch,@function
_RNvNtCsemcRClSg8DH_9native_vm11ring_switch11ring_switch:
.Lfunc_begin54:
	.cfi_startproc
	sub	sp, sp, #432
	.cfi_def_cfa_offset 432
	stp	x29, x30, [sp, #384]
	stp	x22, x21, [sp, #400]
	stp	x20, x19, [sp, #416]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w30, -40
	.cfi_offset w29, -48
	mov	x20, x1
	mov	w1, #13
	mov	x19, x2
	mov	x21, x0
	bl	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState5grind
	tbz	w0, #0, .LBB54_2
	mov	x1, sp
	mov	w22, w0
	mov	x0, x21
	mov	w2, #16
	stp	xzr, xzr, [sp]
	stp	xzr, xzr, [sp, #16]
	stp	xzr, xzr, [sp, #32]
	stp	xzr, xzr, [sp, #48]
	stp	xzr, xzr, [sp, #64]
	stp	xzr, xzr, [sp, #80]
	stp	xzr, xzr, [sp, #96]
	stp	xzr, xzr, [sp, #112]
	stp	xzr, xzr, [sp, #128]
	stp	xzr, xzr, [sp, #144]
	stp	xzr, xzr, [sp, #160]
	stp	xzr, xzr, [sp, #176]
	stp	xzr, xzr, [sp, #192]
	stp	xzr, xzr, [sp, #208]
	stp	xzr, xzr, [sp, #224]
	stp	xzr, xzr, [sp, #240]
	bl	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState17sample_challenges
	ldp	x8, x9, [sp, #128]
	mov	x0, sp
	add	x1, sp, #256
	add	x2, x19, #16
	stp	x8, x9, [sp, #256]
	ldp	x8, x10, [sp, #144]
	stp	x8, x10, [sp, #272]
	ldp	x8, x9, [sp, #160]
	stp	x8, x9, [sp, #288]
	ldp	x8, x10, [sp, #176]
	stp	x8, x10, [sp, #304]
	ldp	x8, x9, [sp, #192]
	stp	x8, x9, [sp, #320]
	ldp	x8, x10, [sp, #208]
	stp	x8, x10, [sp, #336]
	ldp	x8, x9, [sp, #224]
	stp	x8, x9, [sp, #352]
	ldp	x8, x10, [sp, #240]
	stp	x8, x10, [sp, #368]
	bl	_RNvNtCsemcRClSg8DH_9native_vm11ring_switch17ring_coefficients
	mov	x1, sp
	add	x2, sp, #256
	mov	x0, x20
	bl	_RNvNtCsemcRClSg8DH_9native_vm11ring_switch11ring_target
	mov	x8, x0
	mov	w0, w22
	stp	x8, x1, [x19]
.LBB54_2:
	ldp	x20, x19, [sp, #416]
	ldp	x22, x21, [sp, #400]
	ldp	x29, x30, [sp, #384]
	add	sp, sp, #432
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end54:
	.size	_RNvNtCsemcRClSg8DH_9native_vm11ring_switch11ring_switch, .Lfunc_end54-_RNvNtCsemcRClSg8DH_9native_vm11ring_switch11ring_switch
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm11ring_switch11ring_target,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm11ring_switch11ring_target,@function
_RNvNtCsemcRClSg8DH_9native_vm11ring_switch11ring_target:
.Lfunc_begin55:
	.cfi_startproc
	stp	x29, x30, [sp, #-96]!
	.cfi_def_cfa_offset 96
	stp	x28, x27, [sp, #16]
	stp	x26, x25, [sp, #32]
	stp	x24, x23, [sp, #48]
	stp	x22, x21, [sp, #64]
	stp	x20, x19, [sp, #80]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w24, -48
	.cfi_offset w25, -56
	.cfi_offset w26, -64
	.cfi_offset w27, -72
	.cfi_offset w28, -80
	.cfi_offset w30, -88
	.cfi_offset w29, -96
	sub	sp, sp, #2256
	.cfi_def_cfa_offset 2352
	ldr	xzr, [sp]
	mov	x19, x2
	mov	x21, x1
	mov	x20, x0
	mov	x22, xzr
	add	x23, sp, #1232
.LBB55_1:
	add	x8, x20, x22
	mov	x2, x19
	ldp	x0, x1, [x8]
	bl	_RNvNtCsemcRClSg8DH_9native_vm11ring_switch8ring_psi
	add	x8, x23, x22
	add	x22, x22, #16
	cmp	x22, #1024
	stp	x0, x1, [x8]
	b.ne	.LBB55_1
	add	x0, sp, #208
	add	x1, sp, #1232
	mov	w2, #1024
	bl	memcpy
	mov	w0, #8
	mov	w1, #2
	mov	x2, xzr
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW7sq_iter
	ldp	x9, x8, [x21, #112]
	mov	x19, x0
	mov	x20, x1
	add	x0, sp, #208
	mov	w1, #64
	mov	x2, x19
	mov	x3, x20
	stp	x8, x9, [sp, #192]
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field9poly_eval
	mov	x2, x0
	mov	x3, x1
	mov	w0, #56
	mov	x1, x2
	mov	x2, x3
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW7sq_iter
	stp	x1, x0, [sp, #176]
	mov	w0, #8
	mov	x1, x19
	mov	x2, x20
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW7sq_iter
	ldp	x9, x8, [x21, #96]
	mov	x19, x0
	mov	x20, x1
	add	x0, sp, #208
	mov	w1, #64
	mov	x2, x19
	mov	x3, x20
	stp	x8, x9, [sp, #160]
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field9poly_eval
	mov	x2, x0
	mov	x3, x1
	mov	w0, #48
	mov	x1, x2
	mov	x2, x3
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW7sq_iter
	stp	x1, x0, [sp, #144]
	mov	w0, #8
	mov	x1, x19
	mov	x2, x20
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW7sq_iter
	ldp	x9, x8, [x21, #80]
	mov	x19, x0
	mov	x20, x1
	add	x0, sp, #208
	mov	w1, #64
	mov	x2, x19
	mov	x3, x20
	stp	x8, x9, [sp, #128]
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field9poly_eval
	mov	x2, x0
	mov	x3, x1
	mov	w0, #40
	mov	x1, x2
	mov	x2, x3
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW7sq_iter
	stp	x1, x0, [sp, #112]
	mov	w0, #8
	mov	x1, x19
	mov	x2, x20
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW7sq_iter
	ldp	x9, x8, [x21, #64]
	mov	x19, x0
	mov	x20, x1
	add	x0, sp, #208
	mov	w1, #64
	mov	x2, x19
	mov	x3, x20
	stp	x8, x9, [sp, #96]
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field9poly_eval
	mov	x2, x0
	mov	x3, x1
	mov	w0, #32
	mov	x1, x2
	mov	x2, x3
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW7sq_iter
	stp	x1, x0, [sp, #80]
	mov	w0, #8
	mov	x1, x19
	mov	x2, x20
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW7sq_iter
	ldp	x9, x8, [x21, #48]
	mov	x20, x0
	mov	x22, x1
	add	x0, sp, #208
	mov	w1, #64
	mov	x2, x20
	mov	x3, x22
	stp	x8, x9, [sp, #64]
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field9poly_eval
	mov	x2, x0
	mov	x3, x1
	mov	w0, #24
	mov	x1, x2
	mov	x2, x3
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW7sq_iter
	stp	x1, x0, [sp, #32]
	mov	w0, #8
	mov	x1, x20
	mov	x2, x22
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW7sq_iter
	mov	x20, x0
	ldp	x24, x25, [x21, #32]
	mov	x22, x1
	add	x0, sp, #208
	mov	w1, #64
	mov	x2, x20
	mov	x3, x22
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field9poly_eval
	mov	x2, x0
	mov	x3, x1
	mov	w0, #16
	mov	x1, x2
	mov	x2, x3
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW7sq_iter
	mov	x27, x0
	mov	x28, x1
	mov	w0, #8
	mov	x1, x20
	mov	x2, x22
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW7sq_iter
	mov	x20, x0
	ldp	x23, x26, [x21, #16]
	mov	x22, x1
	add	x0, sp, #208
	mov	w1, #64
	mov	x2, x20
	mov	x3, x22
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field9poly_eval
	mov	x2, x0
	mov	x3, x1
	mov	w0, #8
	mov	x1, x2
	mov	x2, x3
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW7sq_iter
	mov	x19, x0
	mov	x29, x1
	mov	w0, #8
	mov	x1, x20
	mov	x2, x22
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW7sq_iter
	ldp	x8, x9, [x21]
	mov	x2, x19
	stp	x1, x0, [sp, #16]
	mov	x0, x23
	mov	x1, x26
	mov	x3, x29
	stp	x8, x9, [sp, #48]
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	str	x0, [sp, #8]
	mov	x26, x1
	mov	x0, x24
	mov	x1, x25
	mov	x2, x27
	mov	x3, x28
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	mov	x19, x0
	mov	x24, x1
	ldp	x1, x0, [sp, #64]
	ldp	x3, x2, [sp, #32]
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	mov	x25, x0
	mov	x27, x1
	ldp	x1, x0, [sp, #96]
	ldp	x3, x2, [sp, #80]
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	mov	x28, x0
	mov	x29, x1
	ldp	x1, x0, [sp, #128]
	ldp	x3, x2, [sp, #112]
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	mov	x21, x0
	mov	x20, x1
	ldp	x1, x0, [sp, #160]
	ldp	x3, x2, [sp, #144]
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	mov	x22, x0
	mov	x23, x1
	ldp	x1, x0, [sp, #192]
	ldp	x3, x2, [sp, #176]
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	eor	x8, x23, x1
	eor	x9, x22, x0
	ldr	x2, [sp, #24]
	eor	x8, x20, x8
	eor	x9, x21, x9
	add	x0, sp, #208
	eor	x8, x29, x8
	eor	x9, x28, x9
	mov	w1, #64
	eor	x8, x27, x8
	eor	x9, x25, x9
	eor	x8, x24, x8
	eor	x9, x19, x9
	eor	x19, x26, x8
	ldp	x8, x3, [sp, #8]
	eor	x20, x8, x9
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field9poly_eval
	mov	x2, x0
	mov	x3, x1
	mov	x0, xzr
	mov	x1, x2
	mov	x2, x3
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW7sq_iter
	mov	x2, x0
	mov	x3, x1
	ldp	x0, x1, [sp, #48]
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	eor	x0, x0, x20
	eor	x1, x1, x19
	add	sp, sp, #2256
	.cfi_def_cfa_offset 96
	ldp	x20, x19, [sp, #80]
	ldp	x22, x21, [sp, #64]
	ldp	x24, x23, [sp, #48]
	ldp	x26, x25, [sp, #32]
	ldp	x28, x27, [sp, #16]
	ldp	x29, x30, [sp], #96
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w25
	.cfi_restore w26
	.cfi_restore w27
	.cfi_restore w28
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end55:
	.size	_RNvNtCsemcRClSg8DH_9native_vm11ring_switch11ring_target, .Lfunc_end55-_RNvNtCsemcRClSg8DH_9native_vm11ring_switch11ring_target
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm11ring_switch17ring_coefficients,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm11ring_switch17ring_coefficients,@function
_RNvNtCsemcRClSg8DH_9native_vm11ring_switch17ring_coefficients:
.Lfunc_begin56:
	.cfi_startproc
	sub	sp, sp, #176
	.cfi_def_cfa_offset 176
	stp	x29, x30, [sp, #80]
	stp	x28, x27, [sp, #96]
	stp	x26, x25, [sp, #112]
	stp	x24, x23, [sp, #128]
	stp	x22, x21, [sp, #144]
	stp	x20, x19, [sp, #160]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w24, -48
	.cfi_offset w25, -56
	.cfi_offset w26, -64
	.cfi_offset w27, -72
	.cfi_offset w28, -80
	.cfi_offset w30, -88
	.cfi_offset w29, -96
	ldp	x21, x8, [x1, #64]
	add	x26, x2, #64
	ldp	x10, x9, [x1, #48]
	add	x27, x0, #8
	ldp	x22, x28, [x1, #112]
	ldp	x20, x23, [x1, #96]
	stp	x8, x10, [sp, #8]
	ldp	x10, x8, [x1, #32]
	ldp	x19, x29, [x1, #80]
	stp	x9, x10, [sp, #24]
	ldp	x11, x9, [x1, #16]
	stp	x9, x8, [sp, #64]
	ldp	x10, x8, [x1]
	str	x10, [sp, #40]
	mov	w10, #8
	stp	x8, x11, [sp, #48]
.LBB56_1:
	ldp	x24, x25, [x27, #-8]
	str	x10, [sp]
	ldp	x2, x3, [sp, #40]
	mov	x0, x24
	mov	x1, x25
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	ldp	x2, x3, [sp, #56]
	stp	x0, x1, [x26, #-64]
	mov	x0, x24
	mov	x1, x25
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	ldr	x2, [sp, #32]
	ldr	x3, [sp, #72]
	stp	x0, x1, [x26, #-48]
	mov	x0, x24
	mov	x1, x25
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	ldp	x2, x3, [sp, #16]
	stp	x0, x1, [x26, #-32]
	mov	x0, x24
	mov	x1, x25
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	ldr	x3, [sp, #8]
	stp	x0, x1, [x26, #-16]
	mov	x0, x24
	mov	x1, x25
	mov	x2, x21
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	stp	x0, x1, [x26]
	mov	x0, x24
	mov	x1, x25
	mov	x2, x19
	mov	x3, x29
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	stp	x0, x1, [x26, #16]
	mov	x0, x24
	mov	x1, x25
	mov	x2, x20
	mov	x3, x23
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	stp	x0, x1, [x26, #32]
	mov	x0, x24
	mov	x1, x25
	mov	x2, x22
	mov	x3, x28
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	stp	x0, x1, [x26, #48]
	ldp	x1, x2, [sp, #40]
	mov	w0, #8
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW7sq_iter
	stp	x0, x1, [sp, #40]
	ldp	x1, x2, [sp, #56]
	mov	w0, #8
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW7sq_iter
	stp	x0, x1, [sp, #56]
	ldr	x1, [sp, #32]
	ldr	x2, [sp, #72]
	mov	w0, #8
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW7sq_iter
	str	x1, [sp, #72]
	ldp	x1, x2, [sp, #16]
	str	x0, [sp, #32]
	mov	w0, #8
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW7sq_iter
	ldr	x2, [sp, #8]
	stp	x0, x1, [sp, #16]
	mov	w0, #8
	mov	x1, x21
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW7sq_iter
	mov	x21, x0
	str	x1, [sp, #8]
	mov	w0, #8
	mov	x1, x19
	mov	x2, x29
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW7sq_iter
	mov	x19, x0
	mov	x29, x1
	mov	w0, #8
	mov	x1, x20
	mov	x2, x23
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW7sq_iter
	mov	x20, x0
	mov	x23, x1
	mov	w0, #8
	mov	x1, x22
	mov	x2, x28
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW7sq_iter
	ldr	x10, [sp]
	mov	x22, x0
	mov	x28, x1
	add	x26, x26, #128
	add	x27, x27, #16
	subs	x10, x10, #1
	b.ne	.LBB56_1
	ldp	x20, x19, [sp, #160]
	ldp	x22, x21, [sp, #144]
	ldp	x24, x23, [sp, #128]
	ldp	x26, x25, [sp, #112]
	ldp	x28, x27, [sp, #96]
	ldp	x29, x30, [sp, #80]
	add	sp, sp, #176
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w25
	.cfi_restore w26
	.cfi_restore w27
	.cfi_restore w28
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end56:
	.size	_RNvNtCsemcRClSg8DH_9native_vm11ring_switch17ring_coefficients, .Lfunc_end56-_RNvNtCsemcRClSg8DH_9native_vm11ring_switch17ring_coefficients
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm11ring_switch8ring_psi,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm11ring_switch8ring_psi,@function
_RNvNtCsemcRClSg8DH_9native_vm11ring_switch8ring_psi:
.Lfunc_begin57:
	.cfi_startproc
	stp	x30, x23, [sp, #-48]!
	.cfi_def_cfa_offset 48
	stp	x22, x21, [sp, #16]
	stp	x20, x19, [sp, #32]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w30, -48
	mov	x20, x1
	ldp	x8, x1, [x2]
	mov	x21, x0
	mov	x19, x2
	mov	x3, x20
	mov	x2, x21
	mov	x0, x8
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	mov	x22, x0
	mov	x23, x1
	mov	x0, x21
	mov	x1, x20
	mov	x2, x21
	mov	x3, x20
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	mov	x20, x0
	ldp	x0, x8, [x19, #16]
	mov	x21, x1
	mov	x2, x20
	mov	x3, x21
	mov	x1, x8
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	eor	x22, x0, x22
	eor	x23, x1, x23
	mov	x0, x20
	mov	x1, x21
	mov	x2, x20
	mov	x3, x21
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	mov	x20, x0
	ldp	x0, x8, [x19, #32]
	mov	x21, x1
	mov	x2, x20
	mov	x3, x21
	mov	x1, x8
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	eor	x22, x0, x22
	eor	x23, x1, x23
	mov	x0, x20
	mov	x1, x21
	mov	x2, x20
	mov	x3, x21
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	mov	x20, x0
	ldp	x0, x8, [x19, #48]
	mov	x21, x1
	mov	x2, x20
	mov	x3, x21
	mov	x1, x8
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	eor	x22, x0, x22
	eor	x23, x1, x23
	mov	x0, x20
	mov	x1, x21
	mov	x2, x20
	mov	x3, x21
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	mov	x20, x0
	ldp	x0, x8, [x19, #64]
	mov	x21, x1
	mov	x2, x20
	mov	x3, x21
	mov	x1, x8
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	eor	x22, x0, x22
	eor	x23, x1, x23
	mov	x0, x20
	mov	x1, x21
	mov	x2, x20
	mov	x3, x21
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	mov	x20, x0
	ldp	x0, x8, [x19, #80]
	mov	x21, x1
	mov	x2, x20
	mov	x3, x21
	mov	x1, x8
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	eor	x22, x0, x22
	eor	x23, x1, x23
	mov	x0, x20
	mov	x1, x21
	mov	x2, x20
	mov	x3, x21
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	mov	x20, x0
	ldp	x0, x8, [x19, #96]
	mov	x21, x1
	mov	x2, x20
	mov	x3, x21
	mov	x1, x8
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	eor	x22, x0, x22
	eor	x23, x1, x23
	mov	x0, x20
	mov	x1, x21
	mov	x2, x20
	mov	x3, x21
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	mov	x2, x0
	ldp	x0, x8, [x19, #112]
	mov	x3, x1
	mov	x1, x8
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	eor	x0, x0, x22
	ldp	x20, x19, [sp, #32]
	ldp	x22, x21, [sp, #16]
	eor	x1, x1, x23
	ldp	x30, x23, [sp], #48
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w30
	ret
.Lfunc_end57:
	.size	_RNvNtCsemcRClSg8DH_9native_vm11ring_switch8ring_psi, .Lfunc_end57-_RNvNtCsemcRClSg8DH_9native_vm11ring_switch8ring_psi
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm3bus10block_form,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm3bus10block_form,@function
_RNvNtCsemcRClSg8DH_9native_vm3bus10block_form:
.Lfunc_begin58:
	.cfi_startproc
	stp	x30, x25, [sp, #-64]!
	.cfi_def_cfa_offset 64
	stp	x24, x23, [sp, #16]
	stp	x22, x21, [sp, #32]
	stp	x20, x19, [sp, #48]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w24, -48
	.cfi_offset w25, -56
	.cfi_offset w30, -64
	mov	x19, x5
	mov	x20, x2
	mov	x22, xzr
	mov	x8, xzr
	mov	w9, #1
	cmp	x0, #146
	stp	x3, x4, [x5, #32]
	stp	x9, xzr, [x5]
	stp	xzr, xzr, [x5, #16]
	b.hi	.LBB58_2
	adrp	x8, .Lanon.a75d6d9e6a8990b4224ef13f18552af8.3
	add	x8, x8, :lo12:.Lanon.a75d6d9e6a8990b4224ef13f18552af8.3
	add	x9, x8, x0, lsl #4
	ldp	x8, x9, [x9]
	add	x22, x9, x8
.LBB58_2:
	subs	x9, x22, x8
	mov	x23, xzr
	add	x25, x1, #8
	csel	x24, xzr, x9, lo
	b	.LBB58_5
.LBB58_3:
	ldp	x3, x4, [x25, #-8]
.LBB58_4:
	mov	x0, x19
	mov	x1, x2
	mov	x2, x5
	bl	_RNvMs0_NtCsemcRClSg8DH_9native_vm6layoutNtB5_7FormBuf10add_scaled
	add	x25, x25, #16
	add	x8, x21, #1
	add	x23, x23, #1
	tbz	w0, #0, .LBB58_8
.LBB58_5:
	cmp	x24, x23
	mov	x21, x8
	b.eq	.LBB58_8
	mov	x0, x21
	bl	_RNvNtCsemcRClSg8DH_9native_vm6layout10form_terms
	mov	x2, x0
	cmp	x23, x20
	mov	x5, x1
	b.lo	.LBB58_3
	mov	x4, xzr
	mov	x3, xzr
	b	.LBB58_4
.LBB58_8:
	cmp	x21, x22
	ldp	x20, x19, [sp, #48]
	ldp	x22, x21, [sp, #32]
	cset	w0, hs
	ldp	x24, x23, [sp, #16]
	ldp	x30, x25, [sp], #64
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w25
	.cfi_restore w30
	ret
.Lfunc_end58:
	.size	_RNvNtCsemcRClSg8DH_9native_vm3bus10block_form, .Lfunc_end58-_RNvNtCsemcRClSg8DH_9native_vm3bus10block_form
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm3bus10bus_layout,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm3bus10bus_layout,@function
_RNvNtCsemcRClSg8DH_9native_vm3bus10bus_layout:
.Lfunc_begin59:
	.cfi_startproc
	stp	x29, x30, [sp, #-80]!
	.cfi_def_cfa_offset 80
	stp	x26, x25, [sp, #16]
	stp	x24, x23, [sp, #32]
	stp	x22, x21, [sp, #48]
	stp	x20, x19, [sp, #64]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w24, -48
	.cfi_offset w25, -56
	.cfi_offset w26, -64
	.cfi_offset w30, -72
	.cfi_offset w29, -80
	sub	sp, sp, #1760
	.cfi_def_cfa_offset 1840
	ldr	xzr, [sp]
	mov	x20, x2
	mov	x25, x1
	mov	x19, x0
	add	x0, sp, #8
	mov	w1, wzr
	mov	w2, #432
	mov	x24, x5
	mov	x22, x4
	mov	x23, x3
	add	x26, sp, #8
	bl	memset
	add	x21, x22, x20
	cbz	x20, .LBB59_4
	ldr	x8, [x25]
	cmp	x20, #1
	str	x8, [sp, #8]
	b.eq	.LBB59_4
	ldr	x8, [x25, #8]
	cmp	x20, #2
	str	x8, [sp, #16]
	b.eq	.LBB59_4
	ldr	x8, [x25, #16]
	str	x8, [sp, #24]
.LBB59_4:
	lsl	x8, x20, #3
	add	x9, x24, #24
	b	.LBB59_6
.LBB59_5:
	ldr	x10, [x9, x10, lsl #3]
	subs	x22, x22, #1
	str	x10, [x26, x8]
	add	x8, x8, #8
	b.eq	.LBB59_8
.LBB59_6:
	ldr	x10, [x23], #16
	cmp	x10, #5
	b.ls	.LBB59_5
	subs	x22, x22, #1
	str	xzr, [x26, x8]
	add	x8, x8, #8
	b.ne	.LBB59_6
.LBB59_8:
	add	x0, sp, #440
	mov	w1, wzr
	mov	w2, #432
	add	x22, sp, #440
	bl	memset
	add	x0, sp, #8
	add	x2, sp, #440
	mov	x1, x21
	mov	w3, #54
	add	x23, sp, #8
	bl	_RNvNtCsemcRClSg8DH_9native_vm6layout13stack_offsets
	cmp	x0, #1
	b.ne	.LBB59_16
	str	xzr, [sp, #880]
	add	x11, sp, #872
	mov	x8, xzr
	mov	x9, xzr
	add	x10, x11, #16
	add	x11, x11, #72
	str	x1, [sp, #872]
	str	xzr, [sp, #888]
	str	xzr, [sp, #896]
	str	xzr, [sp, #904]
	str	xzr, [sp, #912]
	str	xzr, [sp, #920]
	str	xzr, [sp, #928]
	str	xzr, [sp, #936]
	str	xzr, [sp, #944]
	str	xzr, [sp, #952]
	str	xzr, [sp, #960]
	str	xzr, [sp, #968]
	str	xzr, [sp, #976]
	str	xzr, [sp, #984]
	str	xzr, [sp, #992]
	str	xzr, [sp, #1000]
	str	xzr, [sp, #1008]
	str	xzr, [sp, #1016]
	str	xzr, [sp, #1024]
	str	xzr, [sp, #1032]
	str	xzr, [sp, #1040]
	str	xzr, [sp, #1048]
	str	xzr, [sp, #1056]
	str	xzr, [sp, #1064]
	str	xzr, [sp, #1072]
	str	xzr, [sp, #1080]
	str	xzr, [sp, #1088]
	str	xzr, [sp, #1096]
	str	xzr, [sp, #1104]
	str	xzr, [sp, #1112]
	str	xzr, [sp, #1120]
	str	xzr, [sp, #1128]
	str	xzr, [sp, #1136]
	str	xzr, [sp, #1144]
	str	xzr, [sp, #1152]
	str	xzr, [sp, #1160]
	str	xzr, [sp, #1168]
	str	xzr, [sp, #1176]
	str	xzr, [sp, #1184]
	str	xzr, [sp, #1192]
	str	xzr, [sp, #1200]
	str	xzr, [sp, #1208]
	str	xzr, [sp, #1216]
	str	xzr, [sp, #1224]
	str	xzr, [sp, #1232]
	str	xzr, [sp, #1240]
	str	xzr, [sp, #1248]
	str	xzr, [sp, #1256]
	str	xzr, [sp, #1264]
	str	xzr, [sp, #1272]
	str	xzr, [sp, #1280]
	str	xzr, [sp, #1288]
	str	xzr, [sp, #1296]
	str	xzr, [sp, #1304]
	str	xzr, [sp, #1312]
	str	xzr, [sp, #1320]
	str	xzr, [sp, #1328]
	str	xzr, [sp, #1336]
	str	xzr, [sp, #1344]
	str	xzr, [sp, #1352]
	str	xzr, [sp, #1360]
	str	xzr, [sp, #1368]
	str	xzr, [sp, #1376]
	str	xzr, [sp, #1384]
	str	xzr, [sp, #1392]
	str	xzr, [sp, #1400]
	str	xzr, [sp, #1408]
	str	xzr, [sp, #1416]
	str	xzr, [sp, #1424]
	str	xzr, [sp, #1432]
	str	xzr, [sp, #1440]
	str	xzr, [sp, #1448]
	str	xzr, [sp, #1456]
	str	xzr, [sp, #1464]
	str	xzr, [sp, #1472]
	str	xzr, [sp, #1480]
	str	xzr, [sp, #1488]
	str	xzr, [sp, #1496]
	str	xzr, [sp, #1504]
	str	xzr, [sp, #1512]
	str	xzr, [sp, #1520]
	str	xzr, [sp, #1528]
	str	xzr, [sp, #1536]
	str	xzr, [sp, #1544]
	str	xzr, [sp, #1552]
	str	xzr, [sp, #1560]
	str	xzr, [sp, #1568]
	str	xzr, [sp, #1576]
	str	xzr, [sp, #1584]
	str	xzr, [sp, #1592]
	str	xzr, [sp, #1600]
	str	xzr, [sp, #1608]
	str	xzr, [sp, #1616]
	str	xzr, [sp, #1624]
	str	xzr, [sp, #1632]
	str	xzr, [sp, #1640]
	str	xzr, [sp, #1648]
	str	xzr, [sp, #1656]
	str	xzr, [sp, #1664]
	str	xzr, [sp, #1672]
	str	xzr, [sp, #1680]
	str	xzr, [sp, #1688]
	str	xzr, [sp, #1696]
	str	xzr, [sp, #1704]
	str	xzr, [sp, #1712]
	str	xzr, [sp, #1720]
	str	xzr, [sp, #1728]
	str	xzr, [sp, #1736]
	str	xzr, [sp, #1744]
	str	xzr, [sp, #1752]
	b	.LBB59_11
.LBB59_10:
	add	x8, x8, #1
	cmp	x21, x8
	b.eq	.LBB59_17
.LBB59_11:
	ldr	x13, [x23, x8, lsl #3]
	ldr	x12, [x22, x8, lsl #3]
	cmp	x8, x20
	b.hs	.LBB59_14
	cmp	x9, #3
	b.hs	.LBB59_16
	add	x14, x10, x9, lsl #4
	add	x9, x9, #1
	stp	x13, x12, [x14]
	b	.LBB59_10
.LBB59_14:
	ldr	x14, [sp, #936]
	cmp	x14, #51
	b.hs	.LBB59_16
	add	x15, x11, x14, lsl #4
	stp	x13, x12, [x15]
	add	x13, x14, #1
	str	x13, [sp, #936]
	b	.LBB59_10
.LBB59_16:
	str	xzr, [x19]
	b	.LBB59_18
.LBB59_17:
	add	x0, x19, #8
	add	x1, sp, #872
	mov	w2, #888
	str	x9, [sp, #880]
	bl	memcpy
	mov	w8, #1
	str	x8, [x19]
.LBB59_18:
	add	sp, sp, #1760
	.cfi_def_cfa_offset 80
	ldp	x20, x19, [sp, #64]
	ldp	x22, x21, [sp, #48]
	ldp	x24, x23, [sp, #32]
	ldp	x26, x25, [sp, #16]
	ldp	x29, x30, [sp], #80
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w25
	.cfi_restore w26
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end59:
	.size	_RNvNtCsemcRClSg8DH_9native_vm3bus10bus_layout, .Lfunc_end59-_RNvNtCsemcRClSg8DH_9native_vm3bus10bus_layout
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm3bus12fingerprints,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm3bus12fingerprints,@function
_RNvNtCsemcRClSg8DH_9native_vm3bus12fingerprints:
.Lfunc_begin60:
	.cfi_startproc
	sub	sp, sp, #320
	.cfi_def_cfa_offset 320
	stp	x29, x30, [sp, #224]
	stp	x28, x27, [sp, #240]
	stp	x26, x25, [sp, #256]
	stp	x24, x23, [sp, #272]
	stp	x22, x21, [sp, #288]
	stp	x20, x19, [sp, #304]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w24, -48
	.cfi_offset w25, -56
	.cfi_offset w26, -64
	.cfi_offset w27, -72
	.cfi_offset w28, -80
	.cfi_offset w30, -88
	.cfi_offset w29, -96
	ldp	x8, x9, [sp, #352]
	mov	x20, x0
	ldp	x29, x19, [sp, #336]
	mov	x0, xzr
	mov	x22, x6
	mov	x23, x5
	mov	x26, x4
	stp	x8, x9, [sp, #16]
	ldp	x8, x24, [sp, #320]
	mov	x27, x3
	mov	x28, x2
	mov	x21, x1
	stp	x8, x7, [sp, #32]
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field4kpow
	mov	w8, #1
	stp	x0, xzr, [sp, #80]
	add	x2, sp, #48
	mov	x0, x21
	mov	w1, #3
	mov	w3, #3
	stp	x8, xzr, [sp, #48]
	stp	x24, xzr, [sp, #64]
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field3dot
	mov	x24, x0
	mov	x25, x1
	mov	x0, x27
	mov	x1, x26
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field14index_mle_from
	mov	w8, #2
	stp	x0, x1, [sp, #112]
	add	x2, sp, #96
	stp	x8, xzr, [sp, #96]
	ldp	x8, x9, [x28]
	mov	x0, x21
	mov	w1, #5
	mov	w3, #5
	stp	x29, x19, [sp, #128]
	stp	x8, x9, [sp, #144]
	ldp	x8, x10, [x28, #16]
	stp	x8, x10, [sp, #160]
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field3dot
	mov	x26, x0
	mov	w0, #2
	mov	x27, x1
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field4kpow
	mov	x28, x0
	mov	x0, x23
	mov	x1, x22
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field14index_mle_from
	ldp	x9, x8, [sp, #16]
	add	x2, sp, #176
	stp	x0, x1, [sp, #192]
	mov	x0, x21
	mov	w1, #3
	mov	w3, #3
	stp	x28, xzr, [sp, #176]
	stp	x9, x8, [sp, #208]
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field3dot
	ldp	x9, x8, [sp, #32]
	stp	x24, x25, [x20]
	stp	x26, x27, [x20, #16]
	ldp	x22, x21, [sp, #288]
	ldp	x24, x23, [sp, #272]
	eor	x8, x0, x8
	eor	x9, x1, x9
	stp	x8, x9, [x20, #32]
	ldp	x20, x19, [sp, #304]
	ldp	x26, x25, [sp, #256]
	ldp	x28, x27, [sp, #240]
	ldp	x29, x30, [sp, #224]
	add	sp, sp, #320
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w25
	.cfi_restore w26
	.cfi_restore w27
	.cfi_restore w28
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end60:
	.size	_RNvNtCsemcRClSg8DH_9native_vm3bus12fingerprints, .Lfunc_end60-_RNvNtCsemcRClSg8DH_9native_vm3bus12fingerprints
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm3bus14bytecode_share,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm3bus14bytecode_share,@function
_RNvNtCsemcRClSg8DH_9native_vm3bus14bytecode_share:
.Lfunc_begin61:
	.cfi_startproc
	sub	sp, sp, #432
	.cfi_def_cfa_offset 432
	stp	x29, x30, [sp, #336]
	stp	x28, x27, [sp, #352]
	stp	x26, x25, [sp, #368]
	stp	x24, x23, [sp, #384]
	stp	x22, x21, [sp, #400]
	stp	x20, x19, [sp, #416]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w24, -48
	.cfi_offset w25, -56
	.cfi_offset w26, -64
	.cfi_offset w27, -72
	.cfi_offset w28, -80
	.cfi_offset w30, -88
	.cfi_offset w29, -96
	.cfi_remember_state
	mov	x19, x0
	add	x0, sp, #80
	mov	x23, x5
	mov	x22, x4
	mov	x24, x3
	mov	x27, x2
	mov	x25, x1
	bl	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState11read_scalar
	ldr	x8, [sp, #80]
	cbz	x8, .LBB61_9
	ldp	x20, x21, [sp, #88]
	add	x0, sp, #80
	add	x5, sp, #16
	mov	x1, x25
	mov	w4, #3
	mov	w6, #4
	stp	xzr, xzr, [sp, #16]
	mov	x2, x20
	mov	x3, x21
	stp	xzr, xzr, [sp, #32]
	stp	xzr, xzr, [sp, #48]
	stp	xzr, xzr, [sp, #64]
	bl	_RINvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB6_6TState8sumcheckNCNvB2_14sumcheck_plain0EB8_
	ldr	w8, [sp, #80]
	tbz	w8, #0, .LBB61_9
	ldp	x29, x28, [sp, #88]
	add	x0, sp, #80
	mov	x1, x25
	bl	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState11read_scalar
	ldr	w8, [sp, #80]
	tbz	w8, #0, .LBB61_9
	ldp	x25, x26, [sp, #88]
	add	x0, sp, #16
	add	x2, sp, #80
	mov	w1, #4
	mov	w3, #16
	stp	xzr, xzr, [sp, #80]
	stp	xzr, xzr, [sp, #96]
	stp	xzr, xzr, [sp, #112]
	stp	xzr, xzr, [sp, #128]
	stp	xzr, xzr, [sp, #144]
	stp	xzr, xzr, [sp, #160]
	stp	xzr, xzr, [sp, #176]
	stp	xzr, xzr, [sp, #192]
	stp	xzr, xzr, [sp, #208]
	stp	xzr, xzr, [sp, #224]
	stp	xzr, xzr, [sp, #240]
	stp	xzr, xzr, [sp, #256]
	stp	xzr, xzr, [sp, #272]
	stp	xzr, xzr, [sp, #288]
	stp	xzr, xzr, [sp, #304]
	stp	xzr, xzr, [sp, #320]
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field9eq_kernel
	tbz	w0, #0, .LBB61_9
	add	x0, sp, #80
	mov	w1, #16
	mov	x2, x27
	mov	w3, #16
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field3dot
	mov	x2, x25
	mov	x3, x26
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	cmp	x29, x0
	b.ne	.LBB61_9
	cmp	x28, x1
	b.ne	.LBB61_9
	add	x9, x23, x22, lsl #4
	add	x8, x22, #4
	cbz	x22, .LBB61_16
	cmp	x22, #1
	b.ne	.LBB61_11
	mov	x10, xzr
	b	.LBB61_14
.LBB61_9:
	str	xzr, [x19]
.LBB61_10:
	ldp	x20, x19, [sp, #416]
	ldp	x22, x21, [sp, #400]
	ldp	x24, x23, [sp, #384]
	ldp	x26, x25, [sp, #368]
	ldp	x28, x27, [sp, #352]
	ldp	x29, x30, [sp, #336]
	add	sp, sp, #432
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w25
	.cfi_restore w26
	.cfi_restore w27
	.cfi_restore w28
	.cfi_restore w30
	.cfi_restore w29
	ret
.LBB61_11:
	.cfi_restore_state
	and	x10, x22, #0x3e
	add	x11, x24, #16
	add	x12, x23, #16
	and	x13, x22, #0x3e
.LBB61_12:
	ldp	x14, x16, [x11, #-16]
	subs	x13, x13, #2
	stp	x14, x16, [x12, #-16]
	ldp	x15, x14, [x11], #32
	stp	x15, x14, [x12], #32
	b.ne	.LBB61_12
	cmp	x22, x10
	b.eq	.LBB61_16
.LBB61_14:
	mov	w11, #8
	orr	x12, x11, x10, lsl #4
	sub	x10, x22, x10
	add	x11, x24, x12
	add	x12, x23, x12
.LBB61_15:
	ldp	x13, x14, [x11, #-8]
	subs	x10, x10, #1
	add	x11, x11, #16
	stp	x13, x14, [x12, #-8]
	add	x12, x12, #16
	b.ne	.LBB61_15
.LBB61_16:
	ldp	x10, x11, [sp, #16]
	stp	x21, x8, [x19, #16]
	mov	w8, #1
	stp	x25, x26, [x19, #32]
	stp	x8, x20, [x19]
	stp	x10, x11, [x9]
	ldp	x10, x12, [sp, #32]
	stp	x10, x12, [x9, #16]
	ldp	x11, x10, [sp, #48]
	stp	x11, x10, [x9, #32]
	ldp	x12, x10, [sp, #64]
	stp	x12, x10, [x9, #48]
	b	.LBB61_10
.Lfunc_end61:
	.size	_RNvNtCsemcRClSg8DH_9native_vm3bus14bytecode_share, .Lfunc_end61-_RNvNtCsemcRClSg8DH_9native_vm3bus14bytecode_share
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm3bus15accumulate_side,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm3bus15accumulate_side,@function
_RNvNtCsemcRClSg8DH_9native_vm3bus15accumulate_side:
.Lfunc_begin62:
	.cfi_startproc
	stp	x29, x30, [sp, #-96]!
	.cfi_def_cfa_offset 96
	stp	x28, x27, [sp, #16]
	stp	x26, x25, [sp, #32]
	stp	x24, x23, [sp, #48]
	stp	x22, x21, [sp, #64]
	stp	x20, x19, [sp, #80]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w24, -48
	.cfi_offset w25, -56
	.cfi_offset w26, -64
	.cfi_offset w27, -72
	.cfi_offset w28, -80
	.cfi_offset w30, -88
	.cfi_offset w29, -96
	sub	sp, sp, #1, lsl #12
	.cfi_def_cfa_offset 4192
	ldr	xzr, [sp]
	sub	sp, sp, #1, lsl #12
	.cfi_def_cfa_offset 8288
	ldr	xzr, [sp]
	sub	sp, sp, #3808
	.cfi_def_cfa_offset 12096
	ldr	xzr, [sp]
	ldr	x8, [x6, #8]
	add	x10, x6, #16
	ldr	x9, [sp, #12152]
	mov	w11, #8
	ldr	x29, [sp, #12160]
	cmp	x8, #4
	ldr	x25, [sp, #12144]
	ldr	x28, [sp, #12136]
	str	x9, [sp, #32]
	ldr	x9, [sp, #12096]
	csel	x22, x8, xzr, lo
	csel	x21, x10, x11, lo
	ldr	x24, [sp, #12128]
	ldr	x23, [sp, #12120]
	cmp	x9, x22
	mov	x19, x6
	mov	x27, x4
	csel	x20, x9, x22, lo
	stp	x5, x3, [sp, #120]
	stp	x1, x2, [sp, #48]
	str	x0, [sp, #16]
	stp	x28, x25, [sp, #104]
	cbz	x20, .LBB62_3
	ldp	x8, x9, [x21]
	mov	w12, #8
	stp	x27, x19, [sp, #136]
	ldp	x19, x27, [x7]
	mov	x26, x7
	add	x10, x28, x8, lsl #4
	subs	x11, x25, x8
	lsr	x9, x9, x8
	csel	x0, xzr, x11, lo
	csel	x2, x12, x10, lo
	cmp	x8, #63
	mov	x3, x0
	csel	x1, xzr, x9, hi
	bl	_RINvNtCsemcRClSg8DH_9native_vm5field10eq_eval_fnNCNvNtB4_6layout8eq_above0EB4_
	eor	x2, x19, x23
	eor	x3, x27, x24
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	mov	x19, x0
	cmp	x20, #1
	mov	x27, x24
	mov	x24, x28
	mov	x28, x1
	b.ne	.LBB62_5
	mov	x25, x23
	b	.LBB62_9
.LBB62_3:
	mov	x26, x25
	ldr	x9, [sp, #12112]
	ldr	x8, [sp, #12104]
	stp	x8, x9, [sp, #88]
	cbnz	x22, .LBB62_10
.LBB62_4:
	mov	x20, xzr
	mov	w25, #1
	b	.LBB62_13
.LBB62_5:
	str	x29, [sp, #24]
	ldp	x8, x9, [x21, #16]
	ldp	x10, x29, [x26, #16]
	mov	w12, #8
	subs	x11, x25, x8
	lsr	x9, x9, x8
	str	x10, [sp, #96]
	add	x10, x24, x8, lsl #4
	csel	x0, xzr, x11, lo
	mov	x3, x0
	csel	x2, x12, x10, lo
	cmp	x8, #63
	csel	x1, xzr, x9, hi
	bl	_RINvNtCsemcRClSg8DH_9native_vm5field10eq_eval_fnNCNvNtB4_6layout8eq_above0EB4_
	ldr	x8, [sp, #96]
	eor	x3, x29, x27
	eor	x2, x8, x23
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	cmp	x20, #2
	eor	x19, x0, x19
	eor	x28, x1, x28
	b.ne	.LBB62_7
	mov	x25, x23
	b	.LBB62_8
.LBB62_7:
	ldp	x8, x9, [x21, #32]
	mov	w12, #8
	ldp	x20, x26, [x26, #32]
	add	x10, x24, x8, lsl #4
	subs	x11, x25, x8
	lsr	x9, x9, x8
	csel	x0, xzr, x11, lo
	csel	x2, x12, x10, lo
	cmp	x8, #63
	mov	x3, x0
	csel	x1, xzr, x9, hi
	bl	_RINvNtCsemcRClSg8DH_9native_vm5field10eq_eval_fnNCNvNtB4_6layout8eq_above0EB4_
	eor	x2, x20, x23
	eor	x3, x26, x27
	mov	x25, x23
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	eor	x19, x0, x19
	eor	x28, x1, x28
.LBB62_8:
	ldr	x29, [sp, #24]
.LBB62_9:
	mov	x24, x27
	ldr	x8, [sp, #32]
	eor	x29, x28, x29
	mov	x23, x25
	ldp	x28, x26, [sp, #104]
	eor	x8, x19, x8
	ldp	x27, x19, [sp, #136]
	str	x8, [sp, #32]
	ldr	x9, [sp, #12112]
	ldr	x8, [sp, #12104]
	stp	x8, x9, [sp, #88]
	cbz	x22, .LBB62_4
.LBB62_10:
	ldp	x8, x9, [x21]
	mov	w12, #8
	add	x10, x28, x8, lsl #4
	subs	x11, x26, x8
	lsr	x9, x9, x8
	csel	x0, xzr, x11, lo
	csel	x2, x12, x10, lo
	cmp	x8, #63
	mov	x3, x0
	csel	x1, xzr, x9, hi
	bl	_RINvNtCsemcRClSg8DH_9native_vm5field10eq_eval_fnNCNvNtB4_6layout8eq_above0EB4_
	mov	x20, x1
	cmp	x22, #1
	eor	x25, x0, #0x1
	b.eq	.LBB62_13
	ldp	x8, x9, [x21, #16]
	mov	w12, #8
	add	x10, x28, x8, lsl #4
	subs	x11, x26, x8
	lsr	x9, x9, x8
	csel	x0, xzr, x11, lo
	csel	x2, x12, x10, lo
	cmp	x8, #63
	mov	x3, x0
	csel	x1, xzr, x9, hi
	bl	_RINvNtCsemcRClSg8DH_9native_vm5field10eq_eval_fnNCNvNtB4_6layout8eq_above0EB4_
	cmp	x22, #2
	eor	x25, x0, x25
	eor	x20, x1, x20
	b.eq	.LBB62_13
	ldp	x8, x9, [x21, #32]
	mov	w12, #8
	add	x10, x28, x8, lsl #4
	subs	x11, x26, x8
	lsr	x9, x9, x8
	csel	x0, xzr, x11, lo
	csel	x2, x12, x10, lo
	cmp	x8, #63
	mov	x3, x0
	csel	x1, xzr, x9, hi
	bl	_RINvNtCsemcRClSg8DH_9native_vm5field10eq_eval_fnNCNvNtB4_6layout8eq_above0EB4_
	eor	x25, x0, x25
	eor	x20, x1, x20
.LBB62_13:
	add	x9, sp, #1, lsl #12
	mov	x8, #-5920
	add	x9, x9, #1984
.LBB62_14:
	add	x10, x9, x8
	adds	x8, x8, #160
	str	xzr, [x10, #5920]
	str	xzr, [x10, #5960]
	str	xzr, [x10, #6000]
	str	xzr, [x10, #6040]
	str	xzr, [x10, #5928]
	str	xzr, [x10, #5968]
	str	xzr, [x10, #6008]
	str	xzr, [x10, #6048]
	str	xzr, [x10, #5936]
	str	xzr, [x10, #5976]
	str	xzr, [x10, #6016]
	str	xzr, [x10, #6056]
	str	xzr, [x10, #5944]
	str	xzr, [x10, #5984]
	str	xzr, [x10, #6024]
	str	xzr, [x10, #6064]
	str	xzr, [x10, #5952]
	str	xzr, [x10, #5992]
	str	xzr, [x10, #6032]
	str	xzr, [x10, #6072]
	b.ne	.LBB62_14
	add	x8, sp, #152
	add	x1, sp, #1, lsl #12
	mov	w2, #5920
	add	x0, x8, #8
	add	x1, x1, #1984
	stp	x25, x20, [sp, #136]
	str	x29, [sp, #24]
	str	x0, [sp, #80]
	bl	memcpy
	ldr	x8, [x19, #64]
	cmp	x27, x8
	sub	x9, x8, #1
	csel	x29, x27, x8, lo
	cmp	x9, #50
	b.hi	.LBB62_21
	ldp	x10, x9, [sp, #48]
	mov	w8, #5928
	mov	x21, xzr
	mov	x22, xzr
	mov	x20, x28
	add	x27, x19, #80
	mov	w12, #8
	stp	x23, x24, [sp, #64]
	madd	x11, x9, x8, x10
	ldr	x8, [sp, #120]
	add	x9, x8, #24
	add	x8, x8, #72
	str	x8, [sp, #40]
	ldr	x8, [sp, #128]
	add	x28, x8, #8
	stp	x9, x11, [sp, #48]
.LBB62_17:
	ldp	x8, x9, [x27, #-8]
	add	x10, x20, x8, lsl #4
	subs	x11, x26, x8
	lsr	x9, x9, x8
	csel	x0, xzr, x11, lo
	csel	x2, x12, x10, lo
	cmp	x8, #63
	mov	x3, x0
	csel	x1, xzr, x9, hi
	bl	_RINvNtCsemcRClSg8DH_9native_vm5field10eq_eval_fnNCNvNtB4_6layout8eq_above0EB4_
	mov	x24, x1
	ldp	x1, x2, [sp, #88]
	ldp	x3, x4, [sp, #64]
	mov	x23, x0
	ldr	x0, [x28]
	add	x5, sp, #152
	bl	_RNvNtCsemcRClSg8DH_9native_vm3bus10block_form
	mov	w26, #8
	tbz	w0, #0, .LBB62_23
	ldur	x20, [x28, #-8]
	cmp	x20, #5
	b.hi	.LBB62_23
	mov	w8, #40
	adrp	x9, .Lanon.a75d6d9e6a8990b4224ef13f18552af8.4
	add	x9, x9, :lo12:.Lanon.a75d6d9e6a8990b4224ef13f18552af8.4
	madd	x8, x20, x8, x9
	ldr	x9, [sp, #56]
	mov	w10, #17784
	stp	x22, x21, [sp, #120]
	mov	x3, x23
	mov	x4, x24
	madd	x0, x20, x10, x9
	ldr	x9, [sp, #152]
	cmp	x9, #149
	ldp	x22, x21, [x8, #24]
	ldr	x8, [sp, #80]
	csel	x19, x9, xzr, lo
	csel	x25, x8, x26, lo
	mov	x2, x19
	mov	x1, x25
	bl	_RNvMs0_NtCsemcRClSg8DH_9native_vm6layoutNtB5_7FormBuf10add_scaled
	cbz	w0, .LBB62_23
	add	x8, x21, x22
	mov	w11, #154
	adrp	x9, .Lanon.a75d6d9e6a8990b4224ef13f18552af8.5
	add	x9, x9, :lo12:.Lanon.a75d6d9e6a8990b4224ef13f18552af8.5
	cmp	x8, x22
	ldr	x10, [sp, #48]
	ccmp	x8, x11, #2, hs
	ldr	x8, [sp, #136]
	add	x9, x9, x22, lsl #4
	ldr	x10, [x10, x20, lsl #3]
	csel	x21, x21, xzr, lo
	add	x27, x27, #16
	eor	x8, x23, x8
	csel	x22, x9, x26, lo
	add	x28, x28, #16
	str	x8, [sp, #136]
	ldr	x8, [sp, #144]
	eor	x8, x24, x8
	str	x8, [sp, #144]
	ldr	x8, [sp, #40]
	ldr	x2, [x8, x20, lsl #3]
	ldp	x20, x26, [sp, #104]
	cmp	x10, x26
	mov	x0, x20
	csel	x1, x10, x26, lo
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field14padding_weight
	mov	x2, x0
	mov	x3, x1
	mov	x0, x23
	mov	x1, x24
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	mov	x23, x0
	mov	x24, x1
	mov	x0, x25
	mov	x1, x19
	mov	x2, x22
	mov	x3, x21
	bl	_RNvNtCsemcRClSg8DH_9native_vm6layout8evaluate
	mov	x3, x1
	eor	x2, x0, #0x1
	mov	x0, x23
	mov	x1, x24
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	ldp	x22, x21, [sp, #120]
	mov	w12, #8
	subs	x29, x29, #1
	eor	x22, x0, x22
	eor	x21, x1, x21
	b.ne	.LBB62_17
	b	.LBB62_22
.LBB62_21:
	mov	x22, xzr
	mov	x21, xzr
.LBB62_22:
	ldp	x9, x10, [sp, #136]
	ldr	x8, [sp, #32]
	eor	x8, x8, x9
	ldr	x9, [sp, #24]
	eor	x8, x8, x22
	eor	x9, x9, x10
	ldr	x10, [sp, #16]
	eor	x9, x9, x21
	stp	x8, x9, [x10, #8]
	mov	w8, #1
	b	.LBB62_24
.LBB62_23:
	ldr	x10, [sp, #16]
	mov	x8, xzr
.LBB62_24:
	str	x8, [x10]
	add	sp, sp, #2, lsl #12
	.cfi_def_cfa_offset 3904
	add	sp, sp, #3808
	.cfi_def_cfa_offset 96
	ldp	x20, x19, [sp, #80]
	ldp	x22, x21, [sp, #64]
	ldp	x24, x23, [sp, #48]
	ldp	x26, x25, [sp, #32]
	ldp	x28, x27, [sp, #16]
	ldp	x29, x30, [sp], #96
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w25
	.cfi_restore w26
	.cfi_restore w27
	.cfi_restore w28
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end62:
	.size	_RNvNtCsemcRClSg8DH_9native_vm3bus15accumulate_side, .Lfunc_end62-_RNvNtCsemcRClSg8DH_9native_vm3bus15accumulate_side
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm3bus18verify_bus_balance,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm3bus18verify_bus_balance,@function
_RNvNtCsemcRClSg8DH_9native_vm3bus18verify_bus_balance:
.Lfunc_begin63:
	.cfi_startproc
	stp	x29, x30, [sp, #-96]!
	.cfi_def_cfa_offset 96
	stp	x28, x27, [sp, #16]
	stp	x26, x25, [sp, #32]
	stp	x24, x23, [sp, #48]
	stp	x22, x21, [sp, #64]
	stp	x20, x19, [sp, #80]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w24, -48
	.cfi_offset w25, -56
	.cfi_offset w26, -64
	.cfi_offset w27, -72
	.cfi_offset w28, -80
	.cfi_offset w30, -88
	.cfi_offset w29, -96
	sub	sp, sp, #1, lsl #12
	.cfi_def_cfa_offset 4192
	ldr	xzr, [sp]
	sub	sp, sp, #1296
	.cfi_def_cfa_offset 5488
	ldr	xzr, [sp]
	ldp	x27, x29, [x1]
	mov	x20, x1
	mov	x25, x0
	add	x0, sp, #1, lsl #12
	mov	x28, x5
	mov	x19, x4
	mov	x23, x3
	mov	x24, x2
	adrp	x3, .Lanon.a75d6d9e6a8990b4224ef13f18552af8.6
	add	x3, x3, :lo12:.Lanon.a75d6d9e6a8990b4224ef13f18552af8.6
	add	x0, x0, #80
	add	x1, sp, #136
	mov	w2, #3
	mov	w4, #51
	mov	x5, x20
	add	x21, sp, #1, lsl #12
	stp	xzr, x27, [sp, #136]
	add	x21, x21, #80
	str	x29, [sp, #152]
	bl	_RNvNtCsemcRClSg8DH_9native_vm3bus10bus_layout
	ldr	x8, [sp, #4176]
	cbz	x8, .LBB63_22
	add	x8, sp, #160
	ldr	x26, [sp, #4184]
	add	x1, x21, #16
	add	x0, x8, #8
	mov	w2, #880
	bl	memcpy
	add	x0, sp, #1, lsl #12
	adrp	x3, .Lanon.a75d6d9e6a8990b4224ef13f18552af8.7
	add	x3, x3, :lo12:.Lanon.a75d6d9e6a8990b4224ef13f18552af8.7
	add	x0, x0, #80
	add	x1, sp, #136
	mov	w2, #3
	mov	w4, #51
	mov	x5, x20
	add	x21, sp, #1, lsl #12
	str	x26, [sp, #160]
	add	x21, x21, #80
	bl	_RNvNtCsemcRClSg8DH_9native_vm3bus10bus_layout
	ldr	w8, [sp, #4176]
	tbz	w8, #0, .LBB63_22
	add	x0, sp, #1048
	add	x1, x21, #8
	mov	w2, #888
	bl	memcpy
	add	x0, sp, #1, lsl #12
	adrp	x3, .Lanon.a75d6d9e6a8990b4224ef13f18552af8.8
	add	x3, x3, :lo12:.Lanon.a75d6d9e6a8990b4224ef13f18552af8.8
	add	x0, x0, #80
	mov	w1, #8
	mov	x2, xzr
	mov	w4, #45
	mov	x5, x20
	add	x21, sp, #1, lsl #12
	add	x21, x21, #80
	bl	_RNvNtCsemcRClSg8DH_9native_vm3bus10bus_layout
	ldr	w8, [sp, #4176]
	tbz	w8, #0, .LBB63_22
	add	x0, sp, #1936
	add	x1, x21, #8
	mov	w2, #888
	bl	memcpy
	cmp	x26, #64
	b.hs	.LBB63_22
	mov	x8, #-1
	lsl	x8, x8, x26
	mvn	x0, x8
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field10bit_length
	subs	w8, w0, #3
	mov	x0, x25
	csel	w1, wzr, w8, lo
	bl	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState5grind
	cbz	w0, .LBB63_22
	add	x1, sp, #2824
	mov	x0, x25
	mov	w2, #16
	str	xzr, [sp, #2824]
	str	xzr, [sp, #2832]
	str	xzr, [sp, #2840]
	str	xzr, [sp, #2848]
	str	xzr, [sp, #2856]
	str	xzr, [sp, #2864]
	str	xzr, [sp, #2872]
	str	xzr, [sp, #2880]
	str	xzr, [sp, #2888]
	str	xzr, [sp, #2896]
	str	xzr, [sp, #2904]
	str	xzr, [sp, #2912]
	str	xzr, [sp, #2920]
	str	xzr, [sp, #2928]
	str	xzr, [sp, #2936]
	str	xzr, [sp, #2944]
	str	xzr, [sp, #2952]
	str	xzr, [sp, #2960]
	str	xzr, [sp, #2968]
	str	xzr, [sp, #2976]
	str	xzr, [sp, #2984]
	str	xzr, [sp, #2992]
	str	xzr, [sp, #3000]
	str	xzr, [sp, #3008]
	str	xzr, [sp, #3016]
	str	xzr, [sp, #3024]
	str	xzr, [sp, #3032]
	str	xzr, [sp, #3040]
	str	xzr, [sp, #3048]
	str	xzr, [sp, #3056]
	str	xzr, [sp, #3064]
	str	xzr, [sp, #3072]
	bl	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState17sample_challenges
	mov	x0, x25
	bl	_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW7squeeze
	str	x0, [sp, #128]
	add	x0, sp, #1, lsl #12
	mov	x22, x1
	add	x0, x0, #80
	add	x3, sp, #3080
	mov	x1, x25
	mov	x2, x26
	str	xzr, [sp, #3080]
	add	x21, sp, #3080
	str	xzr, [sp, #3088]
	str	xzr, [sp, #3096]
	str	xzr, [sp, #3104]
	str	xzr, [sp, #3112]
	str	xzr, [sp, #3120]
	str	xzr, [sp, #3128]
	str	xzr, [sp, #3136]
	str	xzr, [sp, #3144]
	str	xzr, [sp, #3152]
	str	xzr, [sp, #3160]
	str	xzr, [sp, #3168]
	str	xzr, [sp, #3176]
	str	xzr, [sp, #3184]
	str	xzr, [sp, #3192]
	str	xzr, [sp, #3200]
	str	xzr, [sp, #3208]
	str	xzr, [sp, #3216]
	str	xzr, [sp, #3224]
	str	xzr, [sp, #3232]
	str	xzr, [sp, #3240]
	str	xzr, [sp, #3248]
	str	xzr, [sp, #3256]
	str	xzr, [sp, #3264]
	str	xzr, [sp, #3272]
	str	xzr, [sp, #3280]
	str	xzr, [sp, #3288]
	str	xzr, [sp, #3296]
	str	xzr, [sp, #3304]
	str	xzr, [sp, #3312]
	str	xzr, [sp, #3320]
	str	xzr, [sp, #3328]
	str	xzr, [sp, #3336]
	str	xzr, [sp, #3344]
	str	xzr, [sp, #3352]
	str	xzr, [sp, #3360]
	str	xzr, [sp, #3368]
	str	xzr, [sp, #3376]
	str	xzr, [sp, #3384]
	str	xzr, [sp, #3392]
	str	xzr, [sp, #3400]
	str	xzr, [sp, #3408]
	str	xzr, [sp, #3416]
	str	xzr, [sp, #3424]
	str	xzr, [sp, #3432]
	str	xzr, [sp, #3440]
	str	xzr, [sp, #3448]
	str	xzr, [sp, #3456]
	str	xzr, [sp, #3464]
	str	xzr, [sp, #3472]
	str	xzr, [sp, #3480]
	str	xzr, [sp, #3488]
	str	xzr, [sp, #3496]
	str	xzr, [sp, #3504]
	str	xzr, [sp, #3512]
	str	xzr, [sp, #3520]
	str	xzr, [sp, #3528]
	str	xzr, [sp, #3536]
	str	xzr, [sp, #3544]
	str	xzr, [sp, #3552]
	str	xzr, [sp, #3560]
	str	xzr, [sp, #3568]
	str	xzr, [sp, #3576]
	str	xzr, [sp, #3584]
	str	xzr, [sp, #3592]
	str	xzr, [sp, #3600]
	str	xzr, [sp, #3608]
	str	xzr, [sp, #3616]
	str	xzr, [sp, #3624]
	str	xzr, [sp, #3632]
	str	xzr, [sp, #3640]
	str	xzr, [sp, #3648]
	str	xzr, [sp, #3656]
	str	xzr, [sp, #3664]
	str	xzr, [sp, #3672]
	str	xzr, [sp, #3680]
	str	xzr, [sp, #3688]
	str	xzr, [sp, #3696]
	str	xzr, [sp, #3704]
	str	xzr, [sp, #3712]
	str	xzr, [sp, #3720]
	str	xzr, [sp, #3728]
	str	xzr, [sp, #3736]
	str	xzr, [sp, #3744]
	str	xzr, [sp, #3752]
	str	xzr, [sp, #3760]
	str	xzr, [sp, #3768]
	str	xzr, [sp, #3776]
	str	xzr, [sp, #3784]
	str	xzr, [sp, #3792]
	str	xzr, [sp, #3800]
	str	xzr, [sp, #3808]
	str	xzr, [sp, #3816]
	str	xzr, [sp, #3824]
	str	xzr, [sp, #3832]
	str	xzr, [sp, #3840]
	str	xzr, [sp, #3848]
	str	xzr, [sp, #3856]
	str	xzr, [sp, #3864]
	str	xzr, [sp, #3872]
	str	xzr, [sp, #3880]
	str	xzr, [sp, #3888]
	str	xzr, [sp, #3896]
	str	xzr, [sp, #3904]
	str	xzr, [sp, #3912]
	str	xzr, [sp, #3920]
	str	xzr, [sp, #3928]
	str	xzr, [sp, #3936]
	str	xzr, [sp, #3944]
	str	xzr, [sp, #3952]
	str	xzr, [sp, #3960]
	str	xzr, [sp, #3968]
	str	xzr, [sp, #3976]
	str	xzr, [sp, #3984]
	str	xzr, [sp, #3992]
	str	xzr, [sp, #4000]
	str	xzr, [sp, #4008]
	str	xzr, [sp, #4016]
	str	xzr, [sp, #4024]
	str	xzr, [sp, #4032]
	str	xzr, [sp, #4040]
	str	xzr, [sp, #4048]
	str	xzr, [sp, #4056]
	str	xzr, [sp, #4064]
	str	xzr, [sp, #4072]
	str	xzr, [sp, #4080]
	str	xzr, [sp, #4088]
	str	xzr, [sp, #4096]
	str	xzr, [sp, #4104]
	str	xzr, [sp, #4112]
	str	xzr, [sp, #4120]
	str	xzr, [sp, #4128]
	str	xzr, [sp, #4136]
	bl	_RNvNtCsemcRClSg8DH_9native_vm3gkr25verify_gkr_grand_products
	ldr	x8, [sp, #4176]
	cbz	x8, .LBB63_22
	ldr	x8, [sp, #4184]
	ldr	x9, [sp, #4192]
	orr	x8, x9, x8
	cbz	x8, .LBB63_22
	ldr	x8, [sp, #3128]
	add	x9, x21, #56
	add	x1, sp, #1, lsl #12
	add	x1, x1, #48
	mov	x0, x25
	mov	w2, #2
	cmp	x8, #64
	str	xzr, [sp, #4144]
	csel	x26, x8, xzr, lo
	mov	w8, #8
	str	xzr, [sp, #4152]
	csel	x21, x9, x8, lo
	cmp	x27, x26
	str	xzr, [sp, #4160]
	csel	x27, x27, x26, lo
	cmp	x29, x26
	str	xzr, [sp, #4168]
	csel	x8, x29, x26, lo
	str	x8, [sp, #120]
	bl	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState12read_scalars
	cbz	w0, .LBB63_22
	add	x0, sp, #1, lsl #12
	mov	x1, x25
	add	x0, x0, #80
	bl	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState11read_scalar
	ldr	w8, [sp, #4176]
	tbz	w8, #0, .LBB63_22
	ldr	x9, [sp, #4184]
	ldr	x8, [sp, #4192]
	add	x0, sp, #1, lsl #12
	add	x0, x0, #80
	mov	x1, x25
	stp	x8, x9, [sp, #104]
	bl	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState11read_scalar
	ldr	w8, [sp, #4176]
	tbz	w8, #0, .LBB63_22
	ldr	x9, [sp, #4184]
	ldr	x8, [sp, #4192]
	mov	x0, x28
	ldr	x4, [sp, #4144]
	ldr	x5, [sp, #4152]
	mov	x1, xzr
	mov	x2, x21
	mov	x3, x27
	stp	x8, x9, [sp, #88]
	str	xzr, [x28]
	bl	_RNvNtCsemcRClSg8DH_9native_vm5stack10push_claim
	tbz	w0, #0, .LBB63_22
	ldr	x4, [sp, #4160]
	ldr	x5, [sp, #4168]
	mov	x0, x28
	mov	w1, #1
	mov	x2, x21
	mov	x3, x27
	bl	_RNvNtCsemcRClSg8DH_9native_vm5stack10push_claim
	cbz	w0, .LBB63_22
	ldp	x5, x4, [sp, #104]
	mov	x0, x28
	mov	w1, #2
	mov	x2, x21
	mov	x3, x27
	bl	_RNvNtCsemcRClSg8DH_9native_vm5stack10push_claim
	cbz	w0, .LBB63_22
	ldp	x5, x4, [sp, #88]
	mov	x0, x28
	ldr	x3, [sp, #120]
	mov	w1, #3
	mov	x2, x21
	bl	_RNvNtCsemcRClSg8DH_9native_vm5stack10push_claim
	cbz	w0, .LBB63_22
	add	x0, sp, #1, lsl #12
	add	x5, sp, #1, lsl #12
	ldr	x4, [sp, #120]
	add	x0, x0, #1168
	add	x2, sp, #2824
	add	x5, x5, #80
	mov	x1, x25
	mov	x3, x21
	str	xzr, [sp, #4176]
	str	xzr, [sp, #4184]
	mov	x25, x21
	str	xzr, [sp, #4192]
	str	xzr, [sp, #4200]
	str	xzr, [sp, #4208]
	str	xzr, [sp, #4216]
	str	xzr, [sp, #4224]
	str	xzr, [sp, #4232]
	str	xzr, [sp, #4240]
	str	xzr, [sp, #4248]
	str	xzr, [sp, #4256]
	str	xzr, [sp, #4264]
	str	xzr, [sp, #4272]
	str	xzr, [sp, #4280]
	str	xzr, [sp, #4288]
	str	xzr, [sp, #4296]
	str	xzr, [sp, #4304]
	str	xzr, [sp, #4312]
	str	xzr, [sp, #4320]
	str	xzr, [sp, #4328]
	str	xzr, [sp, #4336]
	str	xzr, [sp, #4344]
	str	xzr, [sp, #4352]
	str	xzr, [sp, #4360]
	str	xzr, [sp, #4368]
	str	xzr, [sp, #4376]
	str	xzr, [sp, #4384]
	str	xzr, [sp, #4392]
	str	xzr, [sp, #4400]
	str	xzr, [sp, #4408]
	str	xzr, [sp, #4416]
	str	xzr, [sp, #4424]
	str	xzr, [sp, #4432]
	str	xzr, [sp, #4440]
	str	xzr, [sp, #4448]
	str	xzr, [sp, #4456]
	str	xzr, [sp, #4464]
	str	xzr, [sp, #4472]
	str	xzr, [sp, #4480]
	str	xzr, [sp, #4488]
	str	xzr, [sp, #4496]
	str	xzr, [sp, #4504]
	str	xzr, [sp, #4512]
	str	xzr, [sp, #4520]
	str	xzr, [sp, #4528]
	str	xzr, [sp, #4536]
	str	xzr, [sp, #4544]
	str	xzr, [sp, #4552]
	str	xzr, [sp, #4560]
	str	xzr, [sp, #4568]
	str	xzr, [sp, #4576]
	str	xzr, [sp, #4584]
	str	xzr, [sp, #4592]
	str	xzr, [sp, #4600]
	str	xzr, [sp, #4608]
	str	xzr, [sp, #4616]
	str	xzr, [sp, #4624]
	str	xzr, [sp, #4632]
	str	xzr, [sp, #4640]
	str	xzr, [sp, #4648]
	str	xzr, [sp, #4656]
	str	xzr, [sp, #4664]
	str	xzr, [sp, #4672]
	str	xzr, [sp, #4680]
	str	xzr, [sp, #4688]
	str	xzr, [sp, #4696]
	str	xzr, [sp, #4704]
	str	xzr, [sp, #4712]
	str	xzr, [sp, #4720]
	str	xzr, [sp, #4728]
	str	xzr, [sp, #4736]
	str	xzr, [sp, #4744]
	str	xzr, [sp, #4752]
	str	xzr, [sp, #4760]
	str	xzr, [sp, #4768]
	str	xzr, [sp, #4776]
	str	xzr, [sp, #4784]
	str	xzr, [sp, #4792]
	str	xzr, [sp, #4800]
	str	xzr, [sp, #4808]
	str	xzr, [sp, #4816]
	str	xzr, [sp, #4824]
	str	xzr, [sp, #4832]
	str	xzr, [sp, #4840]
	str	xzr, [sp, #4848]
	str	xzr, [sp, #4856]
	str	xzr, [sp, #4864]
	str	xzr, [sp, #4872]
	str	xzr, [sp, #4880]
	str	xzr, [sp, #4888]
	str	xzr, [sp, #4896]
	str	xzr, [sp, #4904]
	str	xzr, [sp, #4912]
	str	xzr, [sp, #4920]
	str	xzr, [sp, #4928]
	str	xzr, [sp, #4936]
	str	xzr, [sp, #4944]
	str	xzr, [sp, #4952]
	str	xzr, [sp, #4960]
	str	xzr, [sp, #4968]
	str	xzr, [sp, #4976]
	str	xzr, [sp, #4984]
	str	xzr, [sp, #4992]
	str	xzr, [sp, #5000]
	str	xzr, [sp, #5008]
	str	xzr, [sp, #5016]
	str	xzr, [sp, #5024]
	str	xzr, [sp, #5032]
	str	xzr, [sp, #5040]
	str	xzr, [sp, #5048]
	str	xzr, [sp, #5056]
	str	xzr, [sp, #5064]
	str	xzr, [sp, #5072]
	str	xzr, [sp, #5080]
	str	xzr, [sp, #5088]
	str	xzr, [sp, #5096]
	str	xzr, [sp, #5104]
	str	xzr, [sp, #5112]
	str	xzr, [sp, #5120]
	str	xzr, [sp, #5128]
	str	xzr, [sp, #5136]
	str	xzr, [sp, #5144]
	str	xzr, [sp, #5152]
	str	xzr, [sp, #5160]
	str	xzr, [sp, #5168]
	str	xzr, [sp, #5176]
	str	xzr, [sp, #5184]
	str	xzr, [sp, #5192]
	str	xzr, [sp, #5200]
	str	xzr, [sp, #5208]
	str	xzr, [sp, #5216]
	str	xzr, [sp, #5224]
	str	xzr, [sp, #5232]
	str	xzr, [sp, #5240]
	bl	_RNvNtCsemcRClSg8DH_9native_vm3bus14bytecode_share
	ldr	x8, [sp, #5264]
	cbz	x8, .LBB63_22
	ldr	x3, [sp, #5288]
	ldr	x8, [sp, #5272]
	ldr	x9, [sp, #5280]
	ldr	x4, [sp, #5296]
	ldr	x5, [sp, #5304]
	cmp	x3, #68
	str	x8, [sp, #5248]
	str	x9, [sp, #5256]
	b.hs	.LBB63_22
	add	x2, sp, #1, lsl #12
	mov	x0, x24
	mov	x1, x23
	add	x2, x2, #80
	bl	_RNvNtCsemcRClSg8DH_9native_vm3bus23computed_bytecode_value
	cbz	w0, .LBB63_22
	add	x8, sp, #1, lsl #12
	add	x9, sp, #2824
	str	x25, [sp, #5280]
	add	x8, x8, #48
	str	x9, [sp, #5264]
	ldr	x9, [sp, #120]
	str	x8, [sp, #5272]
	mov	x8, #-1
	mov	w21, #59280
	lsl	x8, x8, x29
	str	x9, [sp, #5304]
	add	x9, sp, #1, lsl #12
	add	x9, x9, #1152
	mov	w24, #53352
	str	x27, [sp, #5288]
	mvn	x0, x8
	mov	w27, #47424
	str	x25, [sp, #5296]
	mov	w29, #41496
	mov	w23, #35568
	str	x9, [sp, #5312]
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field4kpow
	mov	w8, #65208
	str	x0, [sp, #120]
	mov	x0, xzr
	str	xzr, [x19, x8]
	mov	w8, #5600
	movk	w8, #1, lsl #16
	str	xzr, [x19, x23]
	ldr	x23, [sp, #3120]
	str	xzr, [x19, x8]
	mov	w8, #11528
	movk	w8, #1, lsl #16
	str	xzr, [x19, x29]
	ldr	x29, [sp, #3104]
	str	xzr, [x19, x8]
	mov	w8, #17456
	movk	w8, #1, lsl #16
	str	xzr, [x19, x27]
	ldr	x27, [sp, #3096]
	str	xzr, [x19, x8]
	mov	w8, #23384
	movk	w8, #1, lsl #16
	str	xzr, [x19, x24]
	ldr	x24, [sp, #3088]
	str	xzr, [x19, x8]
	mov	w8, #29312
	movk	w8, #1, lsl #16
	str	xzr, [x19, x21]
	ldr	x21, [sp, #3080]
	str	xzr, [x19, x8]
	ldr	x8, [sp, #3112]
	str	xzr, [x19]
	str	x8, [sp, #80]
	mov	w8, #35240
	movk	w8, #1, lsl #16
	str	xzr, [x19, #5928]
	str	xzr, [x19, #11856]
	str	xzr, [x19, #17784]
	str	xzr, [x19, #23712]
	str	xzr, [x19, #29640]
	str	xzr, [x19, x8]
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field4kpow
	mov	x2, x0
	add	x0, sp, #1, lsl #12
	add	x1, sp, #1, lsl #12
	add	x0, x0, #1248
	add	x1, x1, #1168
	mov	w3, #1
	mov	x4, xzr
	mov	w5, #1
	mov	x6, xzr
	bl	_RNCNvNtCsemcRClSg8DH_9native_vm3bus18verify_bus_balance0B5_
	ldr	x9, [sp, #128]
	mov	w8, #16
	add	x0, sp, #1, lsl #12
	add	x7, sp, #1, lsl #12
	mov	x2, xzr
	adrp	x3, .Lanon.a75d6d9e6a8990b4224ef13f18552af8.6
	add	x3, x3, :lo12:.Lanon.a75d6d9e6a8990b4224ef13f18552af8.6
	stp	x8, x9, [sp, #16]
	mov	w9, #3
	add	x8, sp, #2824
	add	x0, x0, #1224
	add	x6, sp, #160
	add	x7, x7, #1248
	mov	x1, x19
	mov	w4, #51
	mov	x5, x20
	stp	x21, x24, [sp, #56]
	add	x21, sp, #2824
	stp	x25, x26, [sp, #40]
	stp	x9, x8, [sp]
	str	x22, [sp, #32]
	bl	_RNvNtCsemcRClSg8DH_9native_vm3bus15accumulate_side
	ldr	x8, [sp, #5320]
	cbz	x8, .LBB63_22
	ldp	x3, x2, [sp, #112]
	add	x0, sp, #1, lsl #12
	ldp	x5, x4, [sp, #96]
	add	x1, sp, #1, lsl #12
	ldr	x6, [sp, #88]
	ldr	x28, [sp, #5328]
	add	x0, x0, #1248
	ldr	x24, [sp, #5336]
	add	x1, x1, #1168
	bl	_RNCNvNtCsemcRClSg8DH_9native_vm3bus18verify_bus_balance0B5_
	ldr	x9, [sp, #128]
	mov	w8, #16
	add	x0, sp, #1, lsl #12
	add	x7, sp, #1, lsl #12
	adrp	x3, .Lanon.a75d6d9e6a8990b4224ef13f18552af8.7
	add	x3, x3, :lo12:.Lanon.a75d6d9e6a8990b4224ef13f18552af8.7
	stp	x8, x9, [sp, #16]
	mov	w9, #3
	add	x0, x0, #1224
	add	x6, sp, #1048
	add	x7, x7, #1248
	mov	x1, x19
	mov	w2, #1
	mov	w4, #51
	mov	x5, x20
	stp	x27, x29, [sp, #56]
	stp	x22, x25, [sp, #32]
	stp	x9, x21, [sp]
	str	x26, [sp, #48]
	bl	_RNvNtCsemcRClSg8DH_9native_vm3bus15accumulate_side
	ldr	w8, [sp, #5320]
	tbz	w8, #0, .LBB63_22
	ldr	x8, [sp, #80]
	add	x0, sp, #1, lsl #12
	ldr	x21, [sp, #5328]
	ldr	x22, [sp, #5336]
	adrp	x9, .Lanon.a75d6d9e6a8990b4224ef13f18552af8.9
	add	x9, x9, :lo12:.Lanon.a75d6d9e6a8990b4224ef13f18552af8.9
	stp	x8, x23, [sp, #56]
	mov	w8, #1
	adrp	x3, .Lanon.a75d6d9e6a8990b4224ef13f18552af8.8
	add	x3, x3, :lo12:.Lanon.a75d6d9e6a8990b4224ef13f18552af8.8
	add	x0, x0, #1248
	add	x6, sp, #1936
	mov	x1, x19
	mov	w2, #2
	mov	w4, #45
	mov	x5, x20
	mov	w7, #8
	stp	x25, x26, [sp, #40]
	stp	xzr, xzr, [sp, #24]
	stp	x9, x8, [sp, #8]
	str	xzr, [sp]
	bl	_RNvNtCsemcRClSg8DH_9native_vm3bus15accumulate_side
	ldr	w8, [sp, #5344]
	tbz	w8, #0, .LBB63_22
	add	x8, x19, #26, lsl #12
	ldr	x23, [sp, #5352]
	ldr	x20, [sp, #5360]
	add	x19, x8, #208
	mov	x1, x25
	mov	x2, x26
	mov	x0, x19
	str	xzr, [x19]
	bl	_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKj3f_E6extendB4_
	tbz	w0, #0, .LBB63_22
	str	x28, [x19, #1016]
	mov	w0, #1
	str	x24, [x19, #1024]
	str	x21, [x19, #1032]
	str	x22, [x19, #1040]
	str	x23, [x19, #1048]
	str	x20, [x19, #1056]
	b	.LBB63_23
.LBB63_22:
	mov	w0, wzr
.LBB63_23:
	add	sp, sp, #1, lsl #12
	.cfi_def_cfa_offset 1392
	add	sp, sp, #1296
	.cfi_def_cfa_offset 96
	ldp	x20, x19, [sp, #80]
	ldp	x22, x21, [sp, #64]
	ldp	x24, x23, [sp, #48]
	ldp	x26, x25, [sp, #32]
	ldp	x28, x27, [sp, #16]
	ldp	x29, x30, [sp], #96
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w25
	.cfi_restore w26
	.cfi_restore w27
	.cfi_restore w28
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end63:
	.size	_RNvNtCsemcRClSg8DH_9native_vm3bus18verify_bus_balance, .Lfunc_end63-_RNvNtCsemcRClSg8DH_9native_vm3bus18verify_bus_balance
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm3bus23computed_bytecode_value,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm3bus23computed_bytecode_value,@function
_RNvNtCsemcRClSg8DH_9native_vm3bus23computed_bytecode_value:
.Lfunc_begin64:
	.cfi_startproc
	str	x30, [sp, #-32]!
	.cfi_def_cfa_offset 32
	stp	x20, x19, [sp, #16]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w30, -32
	mov	x20, x4
	mov	x4, x3
	mov	x3, x2
	mov	x2, x1
	mov	x1, x0
	mov	x19, x5
	mov	x0, x2
	bl	_RINvNtCsemcRClSg8DH_9native_vm5field19multilinear_eval_byNCNvNtB4_3bus23computed_bytecode_value0EB4_
	cmp	x0, x20
	ccmp	x1, x19, #0, eq
	ldp	x20, x19, [sp, #16]
	cset	w0, eq
	ldr	x30, [sp], #32
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w30
	ret
.Lfunc_end64:
	.size	_RNvNtCsemcRClSg8DH_9native_vm3bus23computed_bytecode_value, .Lfunc_end64-_RNvNtCsemcRClSg8DH_9native_vm3bus23computed_bytecode_value
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm3gkr10gkr_layers,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm3gkr10gkr_layers,@function
_RNvNtCsemcRClSg8DH_9native_vm3gkr10gkr_layers:
.Lfunc_begin65:
	.cfi_startproc
	str	x30, [sp, #-48]!
	.cfi_def_cfa_offset 48
	stp	x22, x21, [sp, #16]
	stp	x20, x19, [sp, #32]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w30, -48
	.cfi_remember_state
	mov	x19, x2
	mov	x21, x1
	mov	x20, x0
	subs	x22, x1, #1
	b.ne	.LBB65_3
.LBB65_1:
	mov	x0, x20
	mov	w1, #1
	mov	w2, #1
	mov	x3, x19
	bl	_RNvNtCsemcRClSg8DH_9native_vm3gkr8gkr_step
	mov	x21, xzr
	tbz	w0, #0, .LBB65_8
.LBB65_2:
	subs	x22, x21, #1
	b.eq	.LBB65_1
.LBB65_3:
	cbz	x21, .LBB65_9
	tbnz	w21, #0, .LBB65_6
	subs	x21, x21, #2
	mov	x0, x20
	mov	w1, #2
	cset	w2, eq
	mov	x3, x19
	bl	_RNvNtCsemcRClSg8DH_9native_vm3gkr8gkr_step
	tbnz	w0, #0, .LBB65_2
	b	.LBB65_8
.LBB65_6:
	mov	x0, x20
	mov	w1, #1
	mov	w2, wzr
	mov	x3, x19
	bl	_RNvNtCsemcRClSg8DH_9native_vm3gkr8gkr_step
	tbz	w0, #0, .LBB65_8
	mov	x21, x22
	subs	x22, x22, #1
	b.ne	.LBB65_3
	b	.LBB65_1
.LBB65_8:
	mov	w0, wzr
	ldp	x20, x19, [sp, #32]
	ldp	x22, x21, [sp, #16]
	ldr	x30, [sp], #48
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w30
	ret
.LBB65_9:
	.cfi_restore_state
	mov	w0, #1
	ldp	x20, x19, [sp, #32]
	ldp	x22, x21, [sp, #16]
	ldr	x30, [sp], #48
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w30
	ret
.Lfunc_end65:
	.size	_RNvNtCsemcRClSg8DH_9native_vm3gkr10gkr_layers, .Lfunc_end65-_RNvNtCsemcRClSg8DH_9native_vm3gkr10gkr_layers
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm3gkr25verify_gkr_grand_products,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm3gkr25verify_gkr_grand_products,@function
_RNvNtCsemcRClSg8DH_9native_vm3gkr25verify_gkr_grand_products:
.Lfunc_begin66:
	.cfi_startproc
	sub	sp, sp, #96
	.cfi_def_cfa_offset 96
	stp	x30, x25, [sp, #32]
	stp	x24, x23, [sp, #48]
	stp	x22, x21, [sp, #64]
	stp	x20, x19, [sp, #80]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w24, -48
	.cfi_offset w25, -56
	.cfi_offset w30, -64
	mov	x19, x0
	add	x0, sp, #8
	mov	x20, x3
	mov	x21, x2
	mov	x22, x1
	bl	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState11read_scalar
	ldr	x8, [sp, #8]
	cbz	x8, .LBB66_5
	ldp	x23, x25, [sp, #16]
	add	x0, sp, #8
	mov	x1, x22
	bl	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState11read_scalar
	ldr	w8, [sp, #8]
	tbz	w8, #0, .LBB66_4
	stp	x23, x25, [x20]
	mov	x0, x22
	mov	x1, x21
	stp	x23, x25, [x20, #16]
	ldp	x24, x23, [sp, #16]
	mov	x2, x20
	str	xzr, [x20, #48]
	stp	x24, x23, [x20, #32]
	bl	_RNvNtCsemcRClSg8DH_9native_vm3gkr10gkr_layers
	mov	x8, xzr
	tbz	w0, #0, .LBB66_5
	mov	w8, #1
	stp	x24, x23, [x19, #8]
	b	.LBB66_5
.LBB66_4:
	mov	x8, xzr
.LBB66_5:
	str	x8, [x19]
	ldp	x20, x19, [sp, #80]
	ldp	x22, x21, [sp, #64]
	ldp	x24, x23, [sp, #48]
	ldp	x30, x25, [sp, #32]
	add	sp, sp, #96
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w25
	.cfi_restore w30
	ret
.Lfunc_end66:
	.size	_RNvNtCsemcRClSg8DH_9native_vm3gkr25verify_gkr_grand_products, .Lfunc_end66-_RNvNtCsemcRClSg8DH_9native_vm3gkr25verify_gkr_grand_products
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm3gkr8gkr_step,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm3gkr8gkr_step,@function
_RNvNtCsemcRClSg8DH_9native_vm3gkr8gkr_step:
.Lfunc_begin67:
	.cfi_startproc
	stp	x29, x30, [sp, #-96]!
	.cfi_def_cfa_offset 96
	stp	x28, x27, [sp, #16]
	stp	x26, x25, [sp, #32]
	stp	x24, x23, [sp, #48]
	stp	x22, x21, [sp, #64]
	stp	x20, x19, [sp, #80]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w24, -48
	.cfi_offset w25, -56
	.cfi_offset w26, -64
	.cfi_offset w27, -72
	.cfi_offset w28, -80
	.cfi_offset w30, -88
	.cfi_offset w29, -96
	sub	sp, sp, #1296
	.cfi_def_cfa_offset 1392
	.cfi_remember_state
	ldr	xzr, [sp]
	mov	x21, x0
	mov	w0, #1
	mov	x19, x3
	mov	w22, w2
	mov	x20, x1
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field10bit_length
	subs	w8, w0, #3
	mov	x0, x21
	csel	w1, wzr, w8, lo
	bl	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState5grind
	mov	w8, w0
	mov	w0, wzr
	cbz	w8, .LBB67_15
	mov	x0, x21
	bl	_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW7squeeze
	mov	x24, x0
	mov	x25, x1
	mov	x0, x19
	mov	w1, #3
	mov	x2, x24
	mov	x3, x25
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field9poly_eval
	ldr	x8, [x19, #48]
	mov	w10, #1
	add	x9, x19, #56
	lsl	x26, x10, x20
	mov	w11, #8
	mov	x2, x0
	cmp	x8, #64
	mov	x3, x1
	add	x0, sp, #1024
	csel	x23, x8, xzr, lo
	csel	x5, x9, x11, lo
	orr	x4, x26, #0x1
	add	x7, sp, #16
	mov	x1, x21
	mov	x6, x23
	stp	xzr, xzr, [sp, #16]
	add	x27, sp, #1024
	stp	xzr, xzr, [sp, #32]
	stp	xzr, xzr, [sp, #48]
	stp	xzr, xzr, [sp, #64]
	stp	xzr, xzr, [sp, #80]
	stp	xzr, xzr, [sp, #96]
	stp	xzr, xzr, [sp, #112]
	stp	xzr, xzr, [sp, #128]
	stp	xzr, xzr, [sp, #144]
	stp	xzr, xzr, [sp, #160]
	stp	xzr, xzr, [sp, #176]
	stp	xzr, xzr, [sp, #192]
	stp	xzr, xzr, [sp, #208]
	stp	xzr, xzr, [sp, #224]
	stp	xzr, xzr, [sp, #240]
	stp	xzr, xzr, [sp, #256]
	stp	xzr, xzr, [sp, #272]
	stp	xzr, xzr, [sp, #288]
	stp	xzr, xzr, [sp, #304]
	stp	xzr, xzr, [sp, #320]
	stp	xzr, xzr, [sp, #336]
	stp	xzr, xzr, [sp, #352]
	stp	xzr, xzr, [sp, #368]
	stp	xzr, xzr, [sp, #384]
	stp	xzr, xzr, [sp, #400]
	stp	xzr, xzr, [sp, #416]
	stp	xzr, xzr, [sp, #432]
	stp	xzr, xzr, [sp, #448]
	stp	xzr, xzr, [sp, #464]
	stp	xzr, xzr, [sp, #480]
	stp	xzr, xzr, [sp, #496]
	str	xzr, [sp, #512]
	str	xzr, [sp, #520]
	str	xzr, [sp, #528]
	str	xzr, [sp, #536]
	str	xzr, [sp, #544]
	str	xzr, [sp, #552]
	str	xzr, [sp, #560]
	str	xzr, [sp, #568]
	str	xzr, [sp, #576]
	str	xzr, [sp, #584]
	str	xzr, [sp, #592]
	str	xzr, [sp, #600]
	str	xzr, [sp, #608]
	str	xzr, [sp, #616]
	str	xzr, [sp, #624]
	str	xzr, [sp, #632]
	str	xzr, [sp, #640]
	str	xzr, [sp, #648]
	str	xzr, [sp, #656]
	str	xzr, [sp, #664]
	str	xzr, [sp, #672]
	str	xzr, [sp, #680]
	str	xzr, [sp, #688]
	str	xzr, [sp, #696]
	str	xzr, [sp, #704]
	str	xzr, [sp, #712]
	str	xzr, [sp, #720]
	str	xzr, [sp, #728]
	str	xzr, [sp, #736]
	str	xzr, [sp, #744]
	str	xzr, [sp, #752]
	str	xzr, [sp, #760]
	str	xzr, [sp, #768]
	str	xzr, [sp, #776]
	str	xzr, [sp, #784]
	str	xzr, [sp, #792]
	str	xzr, [sp, #800]
	str	xzr, [sp, #808]
	str	xzr, [sp, #816]
	str	xzr, [sp, #824]
	str	xzr, [sp, #832]
	str	xzr, [sp, #840]
	str	xzr, [sp, #848]
	str	xzr, [sp, #856]
	str	xzr, [sp, #864]
	str	xzr, [sp, #872]
	str	xzr, [sp, #880]
	str	xzr, [sp, #888]
	str	xzr, [sp, #896]
	str	xzr, [sp, #904]
	str	xzr, [sp, #912]
	str	xzr, [sp, #920]
	str	xzr, [sp, #928]
	str	xzr, [sp, #936]
	str	xzr, [sp, #944]
	str	xzr, [sp, #952]
	str	xzr, [sp, #960]
	str	xzr, [sp, #968]
	str	xzr, [sp, #976]
	str	xzr, [sp, #984]
	str	xzr, [sp, #992]
	str	xzr, [sp, #1000]
	str	xzr, [sp, #1008]
	str	xzr, [sp, #1016]
	str	x23, [sp]
	bl	_RINvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB6_6TState8sumcheckNCNvNtB8_3gkr8gkr_step0EB8_
	ldr	w8, [sp, #1024]
	tbz	w8, #0, .LBB67_14
	ldr	x29, [sp, #1032]
	ldr	x28, [sp, #1040]
	add	x1, sp, #1024
	mov	x0, x21
	mov	x2, x26
	str	xzr, [sp, #1024]
	str	xzr, [sp, #1032]
	str	xzr, [sp, #1040]
	str	xzr, [sp, #1048]
	str	xzr, [sp, #1056]
	str	xzr, [sp, #1064]
	str	xzr, [sp, #1072]
	str	xzr, [sp, #1080]
	str	xzr, [sp, #1088]
	str	xzr, [sp, #1096]
	str	xzr, [sp, #1104]
	str	xzr, [sp, #1112]
	str	xzr, [sp, #1120]
	str	xzr, [sp, #1128]
	str	xzr, [sp, #1136]
	str	xzr, [sp, #1144]
	str	xzr, [sp, #1152]
	str	xzr, [sp, #1160]
	str	xzr, [sp, #1168]
	str	xzr, [sp, #1176]
	str	xzr, [sp, #1184]
	str	xzr, [sp, #1192]
	str	xzr, [sp, #1200]
	str	xzr, [sp, #1208]
	bl	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState12read_scalars
	tbz	w0, #0, .LBB67_14
	add	x1, x27, #64
	mov	x0, x21
	mov	x2, x26
	bl	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState12read_scalars
	cbz	w0, .LBB67_14
	add	x1, x27, #128
	mov	x0, x21
	mov	x2, x26
	bl	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState12read_scalars
	cbz	w0, .LBB67_14
	add	x0, sp, #1024
	mov	x1, x26
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field6prod_e
	str	x0, [sp, #1216]
	add	x0, x27, #64
	str	x1, [sp, #1224]
	mov	x1, x26
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field6prod_e
	str	x0, [sp, #1232]
	add	x0, x27, #128
	str	x1, [sp, #1240]
	mov	x1, x26
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field6prod_e
	str	x0, [sp, #1248]
	add	x0, sp, #1216
	mov	x2, x24
	str	x1, [sp, #1256]
	mov	w1, #3
	mov	x3, x25
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field9poly_eval
	cmp	x29, x0
	b.ne	.LBB67_14
	cmp	x28, x1
	b.ne	.LBB67_14
	lsl	x8, x20, x22
	sub	x0, x8, #1
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field10bit_length
	subs	w8, w0, #3
	mov	x0, x21
	csel	w1, wzr, w8, lo
	bl	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState5grind
	tbz	w0, #0, .LBB67_14
	add	x1, sp, #1264
	mov	x0, x21
	mov	x2, x20
	str	xzr, [sp, #1264]
	str	xzr, [sp, #1272]
	str	xzr, [sp, #1280]
	str	xzr, [sp, #1288]
	bl	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState17sample_challenges
	add	x1, sp, #1024
	add	x3, sp, #1264
	mov	x0, x26
	mov	x2, x26
	mov	x4, x20
	bl	_RINvNtCsemcRClSg8DH_9native_vm5field19multilinear_eval_byNCNvB2_16multilinear_eval0EB4_
	stp	x0, x1, [x19]
	add	x1, x27, #64
	add	x3, sp, #1264
	mov	x0, x26
	mov	x2, x26
	mov	x4, x20
	bl	_RINvNtCsemcRClSg8DH_9native_vm5field19multilinear_eval_byNCNvB2_16multilinear_eval0EB4_
	stp	x0, x1, [x19, #16]
	add	x1, x27, #128
	add	x3, sp, #1264
	mov	x0, x26
	mov	x2, x26
	mov	x4, x20
	bl	_RINvNtCsemcRClSg8DH_9native_vm5field19multilinear_eval_byNCNvB2_16multilinear_eval0EB4_
	add	x8, x23, x20
	stp	x0, x1, [x19, #32]
	cmp	x8, #63
	b.hi	.LBB67_14
	ldr	x9, [sp, #1264]
	ldr	x10, [sp, #1272]
	cmp	x20, #1
	stp	x8, x9, [x19, #48]
	str	x10, [x19, #64]
	b.eq	.LBB67_11
	ldr	x8, [sp, #1280]
	ldr	x9, [sp, #1288]
	stp	x8, x9, [x19, #72]
.LBB67_11:
	cbz	x23, .LBB67_21
	cmp	x23, #1
	b.ne	.LBB67_16
	mov	x8, xzr
	b	.LBB67_19
.LBB67_14:
	mov	w0, wzr
.LBB67_15:
	add	sp, sp, #1296
	.cfi_def_cfa_offset 96
	ldp	x20, x19, [sp, #80]
	ldp	x22, x21, [sp, #64]
	ldp	x24, x23, [sp, #48]
	ldp	x26, x25, [sp, #32]
	ldp	x28, x27, [sp, #16]
	ldp	x29, x30, [sp], #96
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w25
	.cfi_restore w26
	.cfi_restore w27
	.cfi_restore w28
	.cfi_restore w30
	.cfi_restore w29
	ret
.LBB67_16:
	.cfi_restore_state
	add	x10, x19, x20, lsl #4
	add	x9, sp, #16
	and	x8, x23, #0x3e
	add	x9, x9, #16
	and	x11, x23, #0x3e
	add	x10, x10, #80
.LBB67_17:
	ldp	x12, x14, [x9, #-16]
	subs	x11, x11, #2
	stp	x12, x14, [x10, #-24]
	ldp	x13, x12, [x9], #32
	stp	x13, x12, [x10, #-8]
	add	x10, x10, #32
	b.ne	.LBB67_17
	cmp	x23, x8
	b.eq	.LBB67_21
.LBB67_19:
	lsl	x9, x8, #4
	add	x11, sp, #16
	sub	x8, x23, x8
	add	x10, x9, x20, lsl #4
	add	x9, x9, x11
	add	x9, x9, #8
	add	x10, x10, x19
	add	x10, x10, #64
.LBB67_20:
	ldp	x11, x12, [x9, #-8]
	subs	x8, x8, #1
	add	x9, x9, #16
	stp	x11, x12, [x10, #-8]
	add	x10, x10, #16
	b.ne	.LBB67_20
.LBB67_21:
	mov	w0, #1
	b	.LBB67_15
.Lfunc_end67:
	.size	_RNvNtCsemcRClSg8DH_9native_vm3gkr8gkr_step, .Lfunc_end67-_RNvNtCsemcRClSg8DH_9native_vm3gkr8gkr_step
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm4whir10fold_round,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm4whir10fold_round,@function
_RNvNtCsemcRClSg8DH_9native_vm4whir10fold_round:
.Lfunc_begin68:
	.cfi_startproc
	sub	sp, sp, #208
	.cfi_def_cfa_offset 208
	stp	x29, x30, [sp, #112]
	stp	x28, x27, [sp, #128]
	stp	x26, x25, [sp, #144]
	stp	x24, x23, [sp, #160]
	stp	x22, x21, [sp, #176]
	stp	x20, x19, [sp, #192]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w24, -48
	.cfi_offset w25, -56
	.cfi_offset w26, -64
	.cfi_offset w27, -72
	.cfi_offset w28, -80
	.cfi_offset w30, -88
	.cfi_offset w29, -96
	mov	x19, x0
	add	x0, sp, #88
	mov	x20, x2
	mov	x23, x1
	bl	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState11read_scalar
	ldr	x8, [sp, #88]
	cbz	x8, .LBB68_8
	ldp	x29, x24, [sp, #96]
	add	x0, sp, #88
	mov	x1, x23
	bl	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState11read_scalar
	ldr	w8, [sp, #88]
	tbz	w8, #0, .LBB68_7
	ldp	x27, x28, [sp, #96]
	add	x0, sp, #88
	mov	x1, x23
	bl	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState11read_scalar
	ldr	w8, [sp, #88]
	tbz	w8, #0, .LBB68_7
	ldp	x25, x26, [sp, #96]
	add	x0, sp, #88
	mov	x1, x23
	bl	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState11read_scalar
	ldr	w8, [sp, #88]
	tbz	w8, #0, .LBB68_7
	ldp	x21, x22, [sp, #96]
	mov	x0, x23
	mov	w1, #7
	bl	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState5grind
	tbz	w0, #0, .LBB68_7
	mov	x0, x23
	bl	_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW7squeeze
	str	x25, [sp, #48]
	mov	x25, x0
	mov	x0, x23
	stp	x22, x21, [sp, #72]
	mov	x22, x1
	bl	_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW7squeeze
	ldp	x8, x9, [x20]
	mov	x21, x0
	mov	x23, x1
	mov	x0, x25
	mov	x1, x22
	eor	x2, x8, x29
	eor	x3, x9, x24
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	stp	x0, x1, [sp, #56]
	mov	x0, x25
	mov	x1, x22
	mov	x2, x25
	mov	x3, x22
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	mov	x2, x27
	mov	x3, x28
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	ldr	x27, [sp, #48]
	stp	x0, x1, [sp, #32]
	mov	x0, x21
	mov	x1, x23
	mov	x3, x26
	mov	x2, x27
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	mov	x28, x0
	stp	x21, x1, [sp, #16]
	mov	x0, x25
	mov	x1, x22
	mov	x2, x21
	mov	x3, x23
	str	x25, [sp, #8]
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	ldp	x8, x9, [sp, #72]
	eor	x2, x9, x27
	eor	x3, x8, x26
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	ldp	x8, x9, [sp, #32]
	eor	x11, x0, x29
	ldr	x10, [sp, #24]
	eor	x9, x9, x10
	ldp	x10, x12, [sp, #56]
	eor	x8, x8, x28
	eor	x10, x10, x8
	ldr	x8, [x20, #16]
	eor	x9, x12, x9
	eor	x10, x10, x11
	eor	x11, x1, x24
	eor	x9, x9, x11
	cmp	x8, #29
	stp	x10, x9, [x20]
	b.hi	.LBB68_7
	add	x9, x20, x8, lsl #4
	add	x8, x8, #1
	str	x8, [x20, #16]
	ldp	x10, x8, [sp, #8]
	stp	x8, x23, [x19, #24]
	mov	w8, #1
	stp	x10, x22, [x9, #24]
	stp	x10, x22, [x19, #8]
	b	.LBB68_8
.LBB68_7:
	mov	x8, xzr
.LBB68_8:
	str	x8, [x19]
	ldp	x20, x19, [sp, #192]
	ldp	x22, x21, [sp, #176]
	ldp	x24, x23, [sp, #160]
	ldp	x26, x25, [sp, #144]
	ldp	x28, x27, [sp, #128]
	ldp	x29, x30, [sp, #112]
	add	sp, sp, #208
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w25
	.cfi_restore w26
	.cfi_restore w27
	.cfi_restore w28
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end68:
	.size	_RNvNtCsemcRClSg8DH_9native_vm4whir10fold_round, .Lfunc_end68-_RNvNtCsemcRClSg8DH_9native_vm4whir10fold_round
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm4whir10glue_level,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm4whir10glue_level,@function
_RNvNtCsemcRClSg8DH_9native_vm4whir10glue_level:
.Lfunc_begin69:
	.cfi_startproc
	sub	sp, sp, #112
	.cfi_def_cfa_offset 112
	stp	x29, x30, [sp, #16]
	stp	x28, x27, [sp, #32]
	stp	x26, x25, [sp, #48]
	stp	x24, x23, [sp, #64]
	stp	x22, x21, [sp, #80]
	stp	x20, x19, [sp, #96]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w24, -48
	.cfi_offset w25, -56
	.cfi_offset w26, -64
	.cfi_offset w27, -72
	.cfi_offset w28, -80
	.cfi_offset w30, -88
	.cfi_offset w29, -96
	ldp	x27, x28, [sp, #144]
	mov	x19, x0
	ldp	x23, x24, [x0]
	mov	x25, x2
	str	x3, [sp, #8]
	mov	x26, x1
	mov	x0, x1
	mov	x1, x2
	mov	x2, x6
	mov	x3, x7
	mov	x21, x5
	mov	x22, x4
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	eor	x29, x0, x23
	eor	x20, x1, x24
	mov	x0, x26
	mov	x1, x25
	mov	x2, x26
	mov	x3, x25
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	mov	x2, x27
	mov	x3, x28
	mov	x23, x0
	mov	x24, x1
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	ldr	x8, [x19, #504]
	eor	x9, x29, x0
	eor	x10, x20, x1
	stp	x9, x10, [x19]
	cmp	x8, #9
	b.hi	.LBB69_6
	mov	w9, #6064
	add	x28, x19, #512
	ldr	x27, [x19, #16]
	madd	x0, x8, x9, x28
	mov	x1, x22
	mov	x2, x21
	stp	x26, x25, [x0]
	stp	x27, xzr, [x0, #16]
	str	xzr, [x0, #40]!
	bl	_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKj1e_E6extendB4_
	cbz	w0, .LBB69_7
	ldr	x8, [x19, #504]
	add	x8, x8, #1
	cmp	x8, #9
	str	x8, [x19, #504]
	b.hi	.LBB69_6
	mov	w9, #6064
	ldp	x1, x2, [sp, #112]
	madd	x21, x8, x9, x28
	mov	w8, #1
	stp	x27, x8, [x21, #16]
	ldr	x8, [sp, #8]
	add	x0, x21, #528
	stp	x23, x24, [x21]
	str	x8, [x21, #32]
	str	xzr, [x21, #528]
	bl	_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufyKje6_E6extendB4_
	cbz	w0, .LBB69_7
	ldp	x1, x2, [sp, #128]
	add	x0, x21, #2376
	str	xzr, [x21, #2376]
	bl	_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKje6_E6extendB4_
	cbz	w0, .LBB69_7
	ldr	x8, [x19, #504]
	mov	w0, #1
	add	x8, x8, #1
	str	x8, [x19, #504]
	b	.LBB69_7
.LBB69_6:
	mov	w0, wzr
.LBB69_7:
	ldp	x20, x19, [sp, #96]
	ldp	x22, x21, [sp, #80]
	ldp	x24, x23, [sp, #64]
	ldp	x26, x25, [sp, #48]
	ldp	x28, x27, [sp, #32]
	ldp	x29, x30, [sp, #16]
	add	sp, sp, #112
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w25
	.cfi_restore w26
	.cfi_restore w27
	.cfi_restore w28
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end69:
	.size	_RNvNtCsemcRClSg8DH_9native_vm4whir10glue_level, .Lfunc_end69-_RNvNtCsemcRClSg8DH_9native_vm4whir10glue_level
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm4whir10glued_eval,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm4whir10glued_eval,@function
_RNvNtCsemcRClSg8DH_9native_vm4whir10glued_eval:
.Lfunc_begin70:
	.cfi_startproc
	ldr	x8, [x1, #24]
	mov	x7, x3
	mov	x6, x2
	cbz	x8, .LBB70_2
	ldr	x9, [x1, #528]
	ldr	x10, [x1, #2376]
	add	x11, x1, #536
	ldr	x8, [x1, #32]
	mov	w12, #8
	cmp	x9, #231
	csel	x3, x9, xzr, lo
	csel	x2, x11, x12, lo
	cmp	x10, #231
	add	x9, x1, #2384
	csel	x5, x10, xzr, lo
	mov	x1, x8
	csel	x4, x9, x12, lo
	b	_RNvNtCsemcRClSg8DH_9native_vm4whir14induced_weight
.LBB70_2:
	stp	x30, x19, [sp, #-16]!
	.cfi_def_cfa_offset 16
	.cfi_offset w19, -8
	.cfi_offset w30, -16
	ldr	x8, [x1, #40]
	add	x9, x1, #48
	mov	w10, #8
	mov	x19, x0
	mov	x2, x6
	mov	x3, x7
	cmp	x8, #31
	csel	x1, x8, xzr, lo
	csel	x8, x9, x10, lo
	mov	x0, x8
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field7eq_eval
	mov	w8, #1
	stp	x0, x1, [x19, #8]
	str	x8, [x19]
	ldp	x30, x19, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w30
	ret
.Lfunc_end70:
	.size	_RNvNtCsemcRClSg8DH_9native_vm4whir10glued_eval, .Lfunc_end70-_RNvNtCsemcRClSg8DH_9native_vm4whir10glued_eval
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm4whir10next_level,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm4whir10next_level,@function
_RNvNtCsemcRClSg8DH_9native_vm4whir10next_level:
.Lfunc_begin71:
	.cfi_startproc
	stp	x29, x30, [sp, #-96]!
	.cfi_def_cfa_offset 96
	stp	x28, x27, [sp, #16]
	stp	x26, x25, [sp, #32]
	stp	x24, x23, [sp, #48]
	stp	x22, x21, [sp, #64]
	stp	x20, x19, [sp, #80]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w24, -48
	.cfi_offset w25, -56
	.cfi_offset w26, -64
	.cfi_offset w27, -72
	.cfi_offset w28, -80
	.cfi_offset w30, -88
	.cfi_offset w29, -96
	sub	sp, sp, #1, lsl #12
	.cfi_def_cfa_offset 4192
	ldr	xzr, [sp]
	sub	sp, sp, #4000
	.cfi_def_cfa_offset 8192
	mov	w8, #2
	ldr	xzr, [sp]
	mov	x28, x2
	ldr	x29, [x2, #8]
	lsl	x2, x8, x3
	subs	x8, x5, x3
	csel	x8, xzr, x8, lo
	mov	x20, x1
	mov	x19, x6
	add	x1, x8, x4
	mov	x27, x5
	mov	x22, x0
	str	x5, [sp, #88]
	bl	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState15read_commitment
	cbz	w0, .LBB71_14
	ldr	x21, [x28]
	stp	xzr, xzr, [sp, #96]
	stp	xzr, xzr, [sp, #112]
	cmp	x21, #6
	stp	xzr, xzr, [sp, #128]
	stp	xzr, xzr, [sp, #144]
	stp	xzr, xzr, [sp, #160]
	stp	xzr, xzr, [sp, #176]
	b.hi	.LBB71_13
	add	x1, sp, #96
	mov	x0, x22
	mov	x2, x21
	bl	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState12read_scalars
	cbz	w0, .LBB71_14
	mov	x0, x22
	mov	w1, #15
	bl	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState5grind
	cbz	w0, .LBB71_14
	ldr	x26, [sp, #88]
	stp	xzr, xzr, [sp, #192]
	stp	xzr, xzr, [sp, #208]
	cmp	x26, #30
	stp	xzr, xzr, [sp, #224]
	stp	xzr, xzr, [sp, #240]
	stp	xzr, xzr, [sp, #256]
	stp	xzr, xzr, [sp, #272]
	stp	xzr, xzr, [sp, #288]
	stp	xzr, xzr, [sp, #304]
	stp	xzr, xzr, [sp, #320]
	stp	xzr, xzr, [sp, #336]
	stp	xzr, xzr, [sp, #352]
	stp	xzr, xzr, [sp, #368]
	stp	xzr, xzr, [sp, #384]
	stp	xzr, xzr, [sp, #400]
	stp	xzr, xzr, [sp, #416]
	stp	xzr, xzr, [sp, #432]
	stp	xzr, xzr, [sp, #448]
	stp	xzr, xzr, [sp, #464]
	stp	xzr, xzr, [sp, #480]
	stp	xzr, xzr, [sp, #496]
	str	xzr, [sp, #512]
	str	xzr, [sp, #520]
	str	xzr, [sp, #528]
	str	xzr, [sp, #536]
	str	xzr, [sp, #544]
	str	xzr, [sp, #552]
	str	xzr, [sp, #560]
	str	xzr, [sp, #568]
	str	xzr, [sp, #576]
	str	xzr, [sp, #584]
	str	xzr, [sp, #592]
	str	xzr, [sp, #600]
	str	xzr, [sp, #608]
	str	xzr, [sp, #616]
	str	xzr, [sp, #624]
	str	xzr, [sp, #632]
	str	xzr, [sp, #640]
	str	xzr, [sp, #648]
	str	xzr, [sp, #656]
	str	xzr, [sp, #664]
	str	xzr, [sp, #672]
	b.hi	.LBB71_13
	add	x8, sp, #192
	mov	x0, x22
	mov	x2, x26
	add	x23, x8, #8
	str	x26, [sp, #192]
	mov	x1, x23
	bl	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState17sample_challenges
	add	x0, sp, #680
	mov	x1, x22
	bl	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState11read_scalar
	ldr	x8, [sp, #680]
	cbz	x8, .LBB71_13
	ldr	x24, [sp, #688]
	ldr	x25, [sp, #696]
	mov	x0, x22
	mov	w1, #17
	bl	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState5grind
	tbz	w0, #0, .LBB71_13
	str	x24, [sp, #80]
	add	x24, x19, #14, lsl #12
	ldr	x2, [x28, #16]
	add	x1, x29, x27
	add	x3, x24, #4008
	mov	x0, x22
	add	x28, x24, #4008
	bl	_RNvNtCsemcRClSg8DH_9native_vm4whir14sample_queries
	cbz	w0, .LBB71_14
	mov	x0, x22
	bl	_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW7squeeze
	ldr	x8, [x28]
	add	x10, sp, #1, lsl #12
	mov	x9, xzr
	add	x10, x10, #272
	stp	x1, x0, [sp, #64]
.LBB71_9:
	add	x11, x10, x9
	add	x9, x9, #64
	cmp	x9, #3648
	stp	xzr, xzr, [x11]
	stp	xzr, xzr, [x11, #16]
	stp	xzr, xzr, [x11, #32]
	stp	xzr, xzr, [x11, #48]
	b.ne	.LBB71_9
	add	x11, sp, #680
	mov	w9, #61360
	add	x1, sp, #1, lsl #12
	add	x28, x11, #8
	cmp	x8, #231
	mov	w10, #8
	add	x9, x19, x9
	add	x1, x1, #272
	mov	x0, x28
	mov	w2, #3680
	str	xzr, [sp, #8016]
	csel	x29, x9, x10, lo
	str	xzr, [sp, #8024]
	csel	x27, x8, xzr, lo
	str	xzr, [sp, #8032]
	str	xzr, [sp, #8040]
	bl	memcpy
	ldp	x1, x0, [sp, #64]
	mov	x2, x28
	mov	x3, x27
	str	x27, [sp, #680]
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field6powers
	add	x0, sp, #1, lsl #12
	mov	x1, x22
	mov	x2, x20
	add	x0, x0, #272
	mov	x3, x29
	mov	x4, x27
	bl	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState14query_openings
	ldr	x8, [sp, #4368]
	cbz	x8, .LBB71_13
	ldr	x8, [sp, #4368]
	ldr	x9, [sp, #4376]
	add	x11, sp, #1, lsl #12
	ldr	x10, [sp, #4392]
	add	x3, sp, #1, lsl #12
	add	x7, sp, #1, lsl #12
	str	x8, [sp, #8048]
	ldr	x8, [sp, #4384]
	add	x11, x11, #3984
	str	x9, [sp, #8056]
	ldr	x9, [sp, #680]
	add	x3, x3, #3952
	str	x10, [sp, #8072]
	add	x10, sp, #96
	add	x7, x7, #272
	str	x8, [sp, #8064]
	add	x8, sp, #88
	cmp	x9, #231
	str	x10, [sp, #4376]
	ldr	x10, [x24, #3808]
	mov	x0, x20
	str	x8, [sp, #4368]
	mov	w8, #8
	mov	x1, x29
	str	x21, [sp, #4384]
	csel	x21, x9, xzr, lo
	mov	w9, #61160
	csel	x22, x28, x8, lo
	add	x9, x19, x9
	cmp	x10, #7
	csel	x5, x9, x8, lo
	csel	x6, x10, xzr, lo
	mov	x2, x27
	mov	x4, x26
	str	xzr, [sp, #8080]
	str	xzr, [sp, #8088]
	str	x11, [sp, #4392]
	str	x22, [sp, #4400]
	str	x21, [sp, #4408]
	bl	_RINvNtCsemcRClSg8DH_9native_vm4whir8each_rowNCNvB2_10next_level0EB4_
	tbz	w0, #0, .LBB71_13
	ldr	x8, [sp, #192]
	ldp	x6, x3, [sp, #80]
	ldp	x2, x1, [sp, #64]
	mov	w9, #8
	cmp	x8, #31
	ldr	x10, [sp, #8080]
	mov	x0, x19
	ldr	x11, [sp, #8088]
	csel	x4, x23, x9, lo
	csel	x5, x8, xzr, lo
	mov	x7, x25
	stp	x22, x21, [sp, #16]
	stp	x10, x11, [sp, #32]
	stp	x29, x27, [sp]
	bl	_RNvNtCsemcRClSg8DH_9native_vm4whir10glue_level
	b	.LBB71_14
.LBB71_13:
	mov	w0, wzr
.LBB71_14:
	add	sp, sp, #1, lsl #12
	.cfi_def_cfa_offset 4096
	add	sp, sp, #4000
	.cfi_def_cfa_offset 96
	ldp	x20, x19, [sp, #80]
	ldp	x22, x21, [sp, #64]
	ldp	x24, x23, [sp, #48]
	ldp	x26, x25, [sp, #32]
	ldp	x28, x27, [sp, #16]
	ldp	x29, x30, [sp], #96
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w25
	.cfi_restore w26
	.cfi_restore w27
	.cfi_restore w28
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end71:
	.size	_RNvNtCsemcRClSg8DH_9native_vm4whir10next_level, .Lfunc_end71-_RNvNtCsemcRClSg8DH_9native_vm4whir10next_level
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm4whir10novel_eval,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm4whir10novel_eval,@function
_RNvNtCsemcRClSg8DH_9native_vm4whir10novel_eval:
.Lfunc_begin72:
	.cfi_startproc
	str	x29, [sp, #-96]!
	.cfi_def_cfa_offset 96
	stp	x30, x27, [sp, #16]
	stp	x26, x25, [sp, #32]
	stp	x24, x23, [sp, #48]
	stp	x22, x21, [sp, #64]
	stp	x20, x19, [sp, #80]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w24, -48
	.cfi_offset w25, -56
	.cfi_offset w26, -64
	.cfi_offset w27, -72
	.cfi_offset w30, -80
	.cfi_offset w29, -96
	sub	sp, sp, #1024
	.cfi_def_cfa_offset 1120
	mov	x8, sp
	mov	x21, x2
	mov	x20, x1
	mov	x19, x0
	add	x0, x8, #8
	mov	w1, wzr
	mov	w2, #1016
	mov	x23, x4
	mov	x22, x3
	bl	memset
	cmp	x21, #64
	b.hi	.LBB72_10
	mov	w24, #1
	cmp	x21, #2
	str	x24, [sp]
	b.lo	.LBB72_7
	add	x25, x22, x23, lsl #3
	mov	w24, #1
.LBB72_3:
	cmp	x22, x25
	b.eq	.LBB72_7
	ldr	x23, [x22]
	mov	x26, sp
	mov	x27, x24
.LBB72_5:
	ldr	x0, [x26]
	mov	x1, x23
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field4kmul
	subs	x27, x27, #1
	str	x0, [x26, x24, lsl #3]
	add	x26, x26, #8
	b.ne	.LBB72_5
	lsl	x24, x24, #1
	add	x22, x22, #8
	cmp	x21, x24
	b.hi	.LBB72_3
.LBB72_7:
	cmp	x24, x21
	csel	x25, x24, x21, lo
	cbz	x25, .LBB72_11
	mov	x24, xzr
	mov	x23, xzr
	add	x26, x20, #8
	mov	x27, sp
.LBB72_9:
	ldp	x1, x20, [x26, #-8]
	ldr	x21, [x27], #8
	mov	x0, x21
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field4kmul
	mov	x22, x0
	mov	x0, x21
	mov	x1, x20
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field4kmul
	subs	x25, x25, #1
	eor	x24, x22, x24
	eor	x23, x0, x23
	add	x26, x26, #16
	b.ne	.LBB72_9
	b	.LBB72_12
.LBB72_10:
	mov	x8, xzr
	b	.LBB72_13
.LBB72_11:
	mov	x23, xzr
	mov	x24, xzr
.LBB72_12:
	mov	w8, #1
	stp	x24, x23, [x19, #8]
.LBB72_13:
	str	x8, [x19]
	add	sp, sp, #1024
	.cfi_def_cfa_offset 96
	ldp	x20, x19, [sp, #80]
	ldp	x22, x21, [sp, #64]
	ldp	x24, x23, [sp, #48]
	ldp	x26, x25, [sp, #32]
	ldp	x30, x27, [sp, #16]
	ldr	x29, [sp], #96
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w25
	.cfi_restore w26
	.cfi_restore w27
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end72:
	.size	_RNvNtCsemcRClSg8DH_9native_vm4whir10novel_eval, .Lfunc_end72-_RNvNtCsemcRClSg8DH_9native_vm4whir10novel_eval
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm4whir10query_bits,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm4whir10query_bits,@function
_RNvNtCsemcRClSg8DH_9native_vm4whir10query_bits:
.Lfunc_begin73:
	.cfi_startproc
	cbz	x2, .LBB73_3
	cmp	x2, #64
	b.hs	.LBB73_4
	lsl	x8, x1, #1
	mvn	w9, w2
	lsr	x10, x0, x2
	lsl	x8, x8, x9
	orr	x0, x8, x10
.LBB73_3:
	mov	x8, #-1
	cmp	x3, #63
	lsl	x9, x8, x3
	csinv	x8, x8, x9, hi
	and	x0, x0, x8
	ret
.LBB73_4:
	cmp	x2, #128
	b.hs	.LBB73_6
	lsr	x0, x1, x2
	mov	x8, #-1
	cmp	x3, #63
	lsl	x9, x8, x3
	csinv	x8, x8, x9, hi
	and	x0, x0, x8
	ret
.LBB73_6:
	mov	x8, #-1
	cmp	x3, #63
	lsl	x9, x8, x3
	csinv	x8, x8, x9, hi
	and	x0, xzr, x8
	ret
.Lfunc_end73:
	.size	_RNvNtCsemcRClSg8DH_9native_vm4whir10query_bits, .Lfunc_end73-_RNvNtCsemcRClSg8DH_9native_vm4whir10query_bits
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm4whir11final_level,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm4whir11final_level,@function
_RNvNtCsemcRClSg8DH_9native_vm4whir11final_level:
.Lfunc_begin74:
	.cfi_startproc
	stp	x29, x30, [sp, #-96]!
	.cfi_def_cfa_offset 96
	stp	x28, x27, [sp, #16]
	stp	x26, x25, [sp, #32]
	stp	x24, x23, [sp, #48]
	stp	x22, x21, [sp, #64]
	stp	x20, x19, [sp, #80]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w24, -48
	.cfi_offset w25, -56
	.cfi_offset w26, -64
	.cfi_offset w27, -72
	.cfi_offset w28, -80
	.cfi_offset w30, -88
	.cfi_offset w29, -96
	sub	sp, sp, #2576
	.cfi_def_cfa_offset 2672
	.cfi_remember_state
	ldr	xzr, [sp]
	ldr	x25, [x2, #8]
	cmp	x3, #63
	stp	xzr, xzr, [sp, #40]
	stp	xzr, xzr, [sp, #56]
	stp	xzr, xzr, [sp, #72]
	stp	xzr, xzr, [sp, #88]
	stp	xzr, xzr, [sp, #104]
	stp	xzr, xzr, [sp, #120]
	stp	xzr, xzr, [sp, #136]
	stp	xzr, xzr, [sp, #152]
	stp	xzr, xzr, [sp, #168]
	stp	xzr, xzr, [sp, #184]
	stp	xzr, xzr, [sp, #200]
	stp	xzr, xzr, [sp, #216]
	stp	xzr, xzr, [sp, #232]
	stp	xzr, xzr, [sp, #248]
	stp	xzr, xzr, [sp, #264]
	stp	xzr, xzr, [sp, #280]
	stp	xzr, xzr, [sp, #296]
	stp	xzr, xzr, [sp, #312]
	stp	xzr, xzr, [sp, #328]
	stp	xzr, xzr, [sp, #344]
	stp	xzr, xzr, [sp, #360]
	stp	xzr, xzr, [sp, #376]
	stp	xzr, xzr, [sp, #392]
	stp	xzr, xzr, [sp, #408]
	stp	xzr, xzr, [sp, #424]
	stp	xzr, xzr, [sp, #440]
	stp	xzr, xzr, [sp, #456]
	stp	xzr, xzr, [sp, #472]
	stp	xzr, xzr, [sp, #488]
	stp	xzr, xzr, [sp, #504]
	str	xzr, [sp, #520]
	str	xzr, [sp, #528]
	str	xzr, [sp, #536]
	str	xzr, [sp, #544]
	str	xzr, [sp, #552]
	str	xzr, [sp, #560]
	str	xzr, [sp, #568]
	str	xzr, [sp, #576]
	str	xzr, [sp, #584]
	str	xzr, [sp, #592]
	str	xzr, [sp, #600]
	str	xzr, [sp, #608]
	str	xzr, [sp, #616]
	str	xzr, [sp, #624]
	str	xzr, [sp, #632]
	str	xzr, [sp, #640]
	str	xzr, [sp, #648]
	str	xzr, [sp, #656]
	str	xzr, [sp, #664]
	str	xzr, [sp, #672]
	str	xzr, [sp, #680]
	str	xzr, [sp, #688]
	str	xzr, [sp, #696]
	str	xzr, [sp, #704]
	str	xzr, [sp, #712]
	str	xzr, [sp, #720]
	str	xzr, [sp, #728]
	str	xzr, [sp, #736]
	str	xzr, [sp, #744]
	str	xzr, [sp, #752]
	str	xzr, [sp, #760]
	str	xzr, [sp, #768]
	str	xzr, [sp, #776]
	str	xzr, [sp, #784]
	str	xzr, [sp, #792]
	str	xzr, [sp, #800]
	str	xzr, [sp, #808]
	str	xzr, [sp, #816]
	str	xzr, [sp, #824]
	str	xzr, [sp, #832]
	str	xzr, [sp, #840]
	str	xzr, [sp, #848]
	str	xzr, [sp, #856]
	str	xzr, [sp, #864]
	str	xzr, [sp, #872]
	str	xzr, [sp, #880]
	str	xzr, [sp, #888]
	str	xzr, [sp, #896]
	str	xzr, [sp, #904]
	str	xzr, [sp, #912]
	str	xzr, [sp, #920]
	str	xzr, [sp, #928]
	str	xzr, [sp, #936]
	str	xzr, [sp, #944]
	str	xzr, [sp, #952]
	str	xzr, [sp, #960]
	str	xzr, [sp, #968]
	str	xzr, [sp, #976]
	str	xzr, [sp, #984]
	str	xzr, [sp, #992]
	str	xzr, [sp, #1000]
	str	xzr, [sp, #1008]
	str	xzr, [sp, #1016]
	str	xzr, [sp, #1024]
	str	xzr, [sp, #1032]
	str	xzr, [sp, #1040]
	str	xzr, [sp, #1048]
	str	xzr, [sp, #1056]
	b.hi	.LBB74_2
	mov	w8, #1
	lsl	x19, x8, x3
	ldr	x8, [x2]
	add	x23, x8, x19
	cmp	x23, #64
	ccmp	x23, x19, #0, ls
	b.hs	.LBB74_4
.LBB74_2:
	mov	w0, wzr
.LBB74_3:
	add	sp, sp, #2576
	.cfi_def_cfa_offset 96
	ldp	x20, x19, [sp, #80]
	ldp	x22, x21, [sp, #64]
	ldp	x24, x23, [sp, #48]
	ldp	x26, x25, [sp, #32]
	ldp	x28, x27, [sp, #16]
	ldp	x29, x30, [sp], #96
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w25
	.cfi_restore w26
	.cfi_restore w27
	.cfi_restore w28
	.cfi_restore w30
	.cfi_restore w29
	ret
.LBB74_4:
	.cfi_restore_state
	mov	x26, x2
	mov	x24, x1
	add	x1, sp, #40
	mov	x2, x23
	mov	x28, x4
	mov	x21, x5
	mov	x27, x6
	mov	x20, x3
	mov	x22, x0
	bl	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState12read_scalars
	cbz	w0, .LBB74_3
	mov	x0, x22
	mov	w1, #17
	bl	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState5grind
	cbz	w0, .LBB74_3
	add	x29, x27, #14, lsl #12
	ldr	x2, [x26, #16]
	add	x1, x25, x20
	add	x3, x29, #4008
	mov	x0, x22
	add	x26, x29, #4008
	bl	_RNvNtCsemcRClSg8DH_9native_vm4whir14sample_queries
	cbz	w0, .LBB74_3
	ldr	x8, [x26]
	mov	w9, #61360
	mov	w10, #8
	add	x9, x27, x9
	add	x0, sp, #2064
	mov	x1, x22
	cmp	x8, #231
	mov	x2, x24
	csel	x25, x8, xzr, lo
	csel	x26, x9, x10, lo
	mov	x3, x26
	mov	x4, x25
	bl	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState14query_openings
	ldr	x8, [sp, #2064]
	cbz	x8, .LBB74_2
	ldr	x8, [sp, #2064]
	ldr	x9, [sp, #2072]
	mov	w12, #61160
	ldr	x11, [x29, #3808]
	ldr	x10, [sp, #2080]
	add	x3, sp, #1064
	str	x8, [sp, #1064]
	add	x8, x27, x12
	mov	w12, #8
	str	x9, [sp, #1072]
	ldr	x9, [sp, #2088]
	cmp	x11, #7
	csel	x6, x11, xzr, lo
	csel	x5, x8, x12, lo
	add	x7, sp, #40
	mov	x0, x24
	mov	x1, x26
	mov	x2, x25
	mov	x4, x20
	str	x10, [sp, #1080]
	str	x9, [sp, #1088]
	str	x23, [sp]
	bl	_RINvNtCsemcRClSg8DH_9native_vm4whir8each_rowNCNvB2_11final_level0EB4_
	tbz	w0, #0, .LBB74_2
	cmp	x20, #30
	str	xzr, [sp, #1096]
	str	xzr, [sp, #1104]
	str	xzr, [sp, #1112]
	str	xzr, [sp, #1120]
	str	xzr, [sp, #1128]
	str	xzr, [sp, #1136]
	str	xzr, [sp, #1144]
	str	xzr, [sp, #1152]
	str	xzr, [sp, #1160]
	str	xzr, [sp, #1168]
	str	xzr, [sp, #1176]
	str	xzr, [sp, #1184]
	str	xzr, [sp, #1192]
	str	xzr, [sp, #1200]
	str	xzr, [sp, #1208]
	str	xzr, [sp, #1216]
	str	xzr, [sp, #1224]
	str	xzr, [sp, #1232]
	str	xzr, [sp, #1240]
	str	xzr, [sp, #1248]
	str	xzr, [sp, #1256]
	str	xzr, [sp, #1264]
	str	xzr, [sp, #1272]
	str	xzr, [sp, #1280]
	str	xzr, [sp, #1288]
	str	xzr, [sp, #1296]
	str	xzr, [sp, #1304]
	str	xzr, [sp, #1312]
	str	xzr, [sp, #1320]
	str	xzr, [sp, #1328]
	str	xzr, [sp, #1336]
	str	xzr, [sp, #1344]
	str	xzr, [sp, #1352]
	str	xzr, [sp, #1360]
	str	xzr, [sp, #1368]
	str	xzr, [sp, #1376]
	str	xzr, [sp, #1384]
	str	xzr, [sp, #1392]
	str	xzr, [sp, #1400]
	str	xzr, [sp, #1408]
	str	xzr, [sp, #1416]
	str	xzr, [sp, #1424]
	str	xzr, [sp, #1432]
	str	xzr, [sp, #1440]
	str	xzr, [sp, #1448]
	str	xzr, [sp, #1456]
	str	xzr, [sp, #1464]
	str	xzr, [sp, #1472]
	str	xzr, [sp, #1480]
	str	xzr, [sp, #1488]
	str	xzr, [sp, #1496]
	str	xzr, [sp, #1504]
	str	xzr, [sp, #1512]
	str	xzr, [sp, #1520]
	str	xzr, [sp, #1528]
	str	xzr, [sp, #1536]
	str	xzr, [sp, #1544]
	str	xzr, [sp, #1552]
	str	xzr, [sp, #1560]
	str	xzr, [sp, #1568]
	b.hi	.LBB74_2
	ldp	x2, x3, [x27]
	mov	x6, x20
	add	x0, sp, #2064
	add	x5, sp, #1096
	mov	x1, x22
	mov	w4, #3
	bl	_RINvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB6_6TState8sumcheckNCNvB2_14sumcheck_plain0EB8_
	ldr	x8, [sp, #2064]
	cbz	x8, .LBB74_2
	ldr	x9, [x27, #16]
	add	x8, x27, #24
	mov	w10, #8
	ldr	x23, [sp, #2072]
	ldr	x24, [sp, #2080]
	add	x0, sp, #1576
	cmp	x9, #31
	str	xzr, [sp, #1584]
	add	x22, sp, #1576
	csel	x2, x9, xzr, lo
	csel	x1, x8, x10, lo
	str	xzr, [sp, #1592]
	str	xzr, [sp, #1600]
	str	xzr, [sp, #1608]
	str	xzr, [sp, #1616]
	str	xzr, [sp, #1624]
	str	xzr, [sp, #1632]
	str	xzr, [sp, #1640]
	str	xzr, [sp, #1648]
	str	xzr, [sp, #1656]
	str	xzr, [sp, #1664]
	str	xzr, [sp, #1672]
	str	xzr, [sp, #1680]
	str	xzr, [sp, #1688]
	str	xzr, [sp, #1696]
	str	xzr, [sp, #1704]
	str	xzr, [sp, #1712]
	str	xzr, [sp, #1720]
	str	xzr, [sp, #1728]
	str	xzr, [sp, #1736]
	str	xzr, [sp, #1744]
	str	xzr, [sp, #1752]
	str	xzr, [sp, #1760]
	str	xzr, [sp, #1768]
	str	xzr, [sp, #1776]
	str	xzr, [sp, #1784]
	str	xzr, [sp, #1792]
	str	xzr, [sp, #1800]
	str	xzr, [sp, #1808]
	str	xzr, [sp, #1816]
	str	xzr, [sp, #1824]
	str	xzr, [sp, #1832]
	str	xzr, [sp, #1840]
	str	xzr, [sp, #1848]
	str	xzr, [sp, #1856]
	str	xzr, [sp, #1864]
	str	xzr, [sp, #1872]
	str	xzr, [sp, #1880]
	str	xzr, [sp, #1888]
	str	xzr, [sp, #1896]
	str	xzr, [sp, #1904]
	str	xzr, [sp, #1912]
	str	xzr, [sp, #1920]
	str	xzr, [sp, #1928]
	str	xzr, [sp, #1936]
	str	xzr, [sp, #1944]
	str	xzr, [sp, #1952]
	str	xzr, [sp, #1960]
	str	xzr, [sp, #1968]
	str	xzr, [sp, #1976]
	str	xzr, [sp, #1984]
	str	xzr, [sp, #1992]
	str	xzr, [sp, #2000]
	str	xzr, [sp, #2008]
	str	xzr, [sp, #2016]
	str	xzr, [sp, #2024]
	str	xzr, [sp, #2032]
	str	xzr, [sp, #2040]
	str	xzr, [sp, #2048]
	str	xzr, [sp, #2056]
	str	xzr, [sp, #1576]
	bl	_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKj1e_E6extendB4_
	tbz	w0, #0, .LBB74_2
	add	x0, sp, #1576
	add	x1, sp, #1096
	mov	x2, x20
	bl	_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKj1e_E6extendB4_
	tbz	w0, #0, .LBB74_2
	ldr	x8, [sp, #1576]
	add	x9, x22, #8
	mov	w10, #8
	add	x0, sp, #2064
	str	xzr, [sp, #2072]
	add	x25, sp, #2064
	cmp	x8, #31
	str	xzr, [sp, #2080]
	csel	x22, x9, x10, lo
	csel	x29, x8, xzr, lo
	str	xzr, [sp, #2088]
	add	x9, x22, x28, lsl #4
	subs	x8, x29, x28
	str	xzr, [sp, #2096]
	csel	x2, xzr, x8, lo
	str	xzr, [sp, #2104]
	csel	x1, x10, x9, lo
	str	xzr, [sp, #2112]
	str	xzr, [sp, #2120]
	str	xzr, [sp, #2128]
	str	xzr, [sp, #2136]
	str	xzr, [sp, #2144]
	str	xzr, [sp, #2152]
	str	xzr, [sp, #2160]
	str	xzr, [sp, #2168]
	str	xzr, [sp, #2176]
	str	xzr, [sp, #2184]
	str	xzr, [sp, #2192]
	str	xzr, [sp, #2200]
	str	xzr, [sp, #2208]
	str	xzr, [sp, #2216]
	str	xzr, [sp, #2224]
	str	xzr, [sp, #2232]
	str	xzr, [sp, #2240]
	str	xzr, [sp, #2248]
	str	xzr, [sp, #2256]
	str	xzr, [sp, #2264]
	str	xzr, [sp, #2272]
	str	xzr, [sp, #2280]
	str	xzr, [sp, #2288]
	str	xzr, [sp, #2296]
	str	xzr, [sp, #2304]
	str	xzr, [sp, #2312]
	str	xzr, [sp, #2320]
	str	xzr, [sp, #2328]
	str	xzr, [sp, #2336]
	str	xzr, [sp, #2344]
	str	xzr, [sp, #2352]
	str	xzr, [sp, #2360]
	str	xzr, [sp, #2368]
	str	xzr, [sp, #2376]
	str	xzr, [sp, #2384]
	str	xzr, [sp, #2392]
	str	xzr, [sp, #2400]
	str	xzr, [sp, #2408]
	str	xzr, [sp, #2416]
	str	xzr, [sp, #2424]
	str	xzr, [sp, #2432]
	str	xzr, [sp, #2440]
	str	xzr, [sp, #2448]
	str	xzr, [sp, #2456]
	str	xzr, [sp, #2464]
	str	xzr, [sp, #2472]
	str	xzr, [sp, #2480]
	str	xzr, [sp, #2488]
	str	xzr, [sp, #2496]
	str	xzr, [sp, #2504]
	str	xzr, [sp, #2512]
	str	xzr, [sp, #2520]
	str	xzr, [sp, #2528]
	str	xzr, [sp, #2536]
	str	xzr, [sp, #2544]
	str	xzr, [sp, #2064]
	bl	_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKj1e_E6extendB4_
	cbz	w0, .LBB74_2
	cmp	x29, x28
	add	x0, sp, #2064
	mov	x1, x22
	csel	x2, x29, x28, lo
	bl	_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKj1e_E6extendB4_
	tbz	w0, #0, .LBB74_2
	ldr	x8, [sp, #2064]
	add	x9, x25, #8
	mov	w10, #8
	add	x0, sp, #2552
	mov	x1, x21
	cmp	x8, #31
	csel	x3, x8, xzr, lo
	csel	x2, x9, x10, lo
	bl	_RNvMNtCsemcRClSg8DH_9native_vm4whirNtB2_6BasisW4eval
	ldr	x8, [sp, #2552]
	cbz	x8, .LBB74_2
	ldr	x8, [x27, #504]
	mov	w9, #6064
	stp	x23, x24, [sp, #24]
	ldr	x21, [sp, #2560]
	ldr	x23, [sp, #2568]
	add	x10, x27, #512
	mul	x9, x8, x9
	cmp	x8, #11
	mov	w11, #8
	csel	x24, x10, x11, lo
	csel	x8, x9, xzr, lo
	cbz	x8, .LBB74_20
	add	x27, x24, x8
	mov	w28, #6064
.LBB74_18:
	ldp	x26, x8, [x24, #8]
	mov	w10, #8
	ldr	x25, [x24]
	add	x0, sp, #2552
	mov	x1, x24
	add	x9, x22, x8, lsl #4
	subs	x8, x29, x8
	csel	x3, xzr, x8, lo
	csel	x2, x10, x9, lo
	bl	_RNvNtCsemcRClSg8DH_9native_vm4whir10glued_eval
	ldr	x8, [sp, #2552]
	cbz	x8, .LBB74_2
	ldr	x2, [sp, #2560]
	ldr	x3, [sp, #2568]
	mov	x0, x25
	mov	x1, x26
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	add	x24, x24, x28
	eor	x21, x0, x21
	eor	x23, x1, x23
	cmp	x24, x27
	b.ne	.LBB74_18
.LBB74_20:
	add	x1, sp, #40
	add	x3, sp, #1096
	mov	x0, x19
	mov	x2, x19
	mov	x4, x20
	bl	_RINvNtCsemcRClSg8DH_9native_vm5field19multilinear_eval_byNCNvB2_16multilinear_eval0EB4_
	mov	x2, x0
	mov	x3, x1
	mov	x0, x21
	mov	x1, x23
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	ldp	x9, x8, [sp, #24]
	cmp	x0, x9
	ccmp	x1, x8, #0, eq
	cset	w0, eq
	b	.LBB74_3
.Lfunc_end74:
	.size	_RNvNtCsemcRClSg8DH_9native_vm4whir11final_level, .Lfunc_end74-_RNvNtCsemcRClSg8DH_9native_vm4whir11final_level
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm4whir11fold_rounds,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm4whir11fold_rounds,@function
_RNvNtCsemcRClSg8DH_9native_vm4whir11fold_rounds:
.Lfunc_begin75:
	.cfi_startproc
	str	xzr, [x3]
	cbz	x1, .LBB75_7
	sub	sp, sp, #160
	.cfi_def_cfa_offset 160
	stp	x30, x23, [sp, #112]
	stp	x22, x21, [sp, #128]
	stp	x20, x19, [sp, #144]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w30, -48
	.cfi_remember_state
	mov	x20, x0
	mov	x22, x1
	add	x0, sp, #40
	mov	x1, x20
	mov	x21, x3
	mov	x19, x2
	add	x23, sp, #40
	bl	_RNvNtCsemcRClSg8DH_9native_vm4whir10fold_round
	ldr	w8, [sp, #40]
	tbz	w8, #0, .LBB75_17
	ldp	x10, x8, [x23, #16]
	mov	w0, #1
	ldur	x9, [x23, #8]
	ldur	x11, [x23, #32]
	cmp	x22, #1
	str	x8, [sp, #24]
	stp	x9, x10, [sp, #80]
	stp	x8, x11, [sp, #96]
	stp	x10, x8, [x21, #16]
	str	x11, [x21, #32]
	stp	x0, x9, [x21]
	b.eq	.LBB75_6
	add	x0, sp, #40
	mov	x1, x20
	mov	x2, x19
	bl	_RNvNtCsemcRClSg8DH_9native_vm4whir10fold_round
	ldr	x8, [sp, #40]
	cbz	x8, .LBB75_17
	ldp	x10, x8, [x23, #16]
	cmp	x22, #2
	ldur	x11, [x23, #32]
	ldur	x9, [x23, #8]
	str	x8, [sp, #24]
	stp	x8, x11, [sp, #96]
	stp	x8, x11, [x21, #56]
	mov	w8, #2
	stp	x9, x10, [sp, #80]
	stp	x9, x10, [x21, #40]
	str	x8, [x21]
	b.ne	.LBB75_8
.LBB75_5:
	mov	w0, #1
.LBB75_6:
	ldp	x20, x19, [sp, #144]
	ldp	x22, x21, [sp, #128]
	ldp	x30, x23, [sp, #112]
	add	sp, sp, #160
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w30
	ret
.LBB75_7:
	mov	w0, #1
	ret
.LBB75_8:
	.cfi_restore_state
	add	x0, sp, #40
	mov	x1, x20
	mov	x2, x19
	bl	_RNvNtCsemcRClSg8DH_9native_vm4whir10fold_round
	ldr	x8, [sp, #40]
	cbz	x8, .LBB75_17
	ldp	x10, x8, [x23, #16]
	cmp	x22, #3
	ldur	x11, [x23, #32]
	ldur	x9, [x23, #8]
	str	x8, [sp, #24]
	stp	x8, x11, [sp, #96]
	stp	x8, x11, [x21, #88]
	mov	w8, #3
	stp	x9, x10, [sp, #80]
	stp	x9, x10, [x21, #72]
	str	x8, [x21]
	b.eq	.LBB75_5
	add	x0, sp, #40
	mov	x1, x20
	mov	x2, x19
	bl	_RNvNtCsemcRClSg8DH_9native_vm4whir10fold_round
	ldr	x8, [sp, #40]
	cbz	x8, .LBB75_17
	ldp	x10, x8, [x23, #16]
	cmp	x22, #4
	ldur	x11, [x23, #32]
	ldur	x9, [x23, #8]
	str	x8, [sp, #24]
	stp	x8, x11, [sp, #96]
	stp	x8, x11, [x21, #120]
	mov	w8, #4
	stp	x9, x10, [sp, #80]
	stp	x9, x10, [x21, #104]
	str	x8, [x21]
	b.eq	.LBB75_5
	add	x0, sp, #40
	mov	x1, x20
	mov	x2, x19
	bl	_RNvNtCsemcRClSg8DH_9native_vm4whir10fold_round
	ldr	x8, [sp, #40]
	cbz	x8, .LBB75_17
	ldp	x10, x8, [x23, #16]
	cmp	x22, #5
	ldur	x11, [x23, #32]
	ldur	x9, [x23, #8]
	str	x8, [sp, #24]
	stp	x8, x11, [sp, #96]
	stp	x8, x11, [x21, #152]
	mov	w8, #5
	stp	x9, x10, [sp, #80]
	stp	x9, x10, [x21, #136]
	str	x8, [x21]
	b.eq	.LBB75_5
	add	x0, sp, #40
	mov	x1, x20
	mov	x2, x19
	bl	_RNvNtCsemcRClSg8DH_9native_vm4whir10fold_round
	ldr	x8, [sp, #40]
	cbz	x8, .LBB75_17
	ldp	x10, x8, [x23, #16]
	cmp	x22, #6
	ldur	x11, [x23, #32]
	ldur	x9, [x23, #8]
	str	x8, [sp, #24]
	stp	x8, x11, [sp, #96]
	stp	x8, x11, [x21, #184]
	mov	w8, #6
	stp	x9, x10, [sp, #80]
	stp	x9, x10, [x21, #168]
	str	x8, [x21]
	b.eq	.LBB75_5
	add	x0, sp, #40
	mov	x1, x20
	mov	x2, x19
	bl	_RNvNtCsemcRClSg8DH_9native_vm4whir10fold_round
.LBB75_17:
	mov	w0, wzr
	ldp	x20, x19, [sp, #144]
	ldp	x22, x21, [sp, #128]
	ldp	x30, x23, [sp, #112]
	add	sp, sp, #160
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w30
	ret
.Lfunc_end75:
	.size	_RNvNtCsemcRClSg8DH_9native_vm4whir11fold_rounds, .Lfunc_end75-_RNvNtCsemcRClSg8DH_9native_vm4whir11fold_rounds
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm4whir11whir_levels,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm4whir11whir_levels,@function
_RNvNtCsemcRClSg8DH_9native_vm4whir11whir_levels:
.Lfunc_begin76:
	.cfi_startproc
	str	x30, [sp, #-96]!
	.cfi_def_cfa_offset 96
	stp	x28, x27, [sp, #16]
	stp	x26, x25, [sp, #32]
	stp	x24, x23, [sp, #48]
	stp	x22, x21, [sp, #64]
	stp	x20, x19, [sp, #80]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w24, -48
	.cfi_offset w25, -56
	.cfi_offset w26, -64
	.cfi_offset w27, -72
	.cfi_offset w28, -80
	.cfi_offset w30, -96
	.cfi_remember_state
	subs	x8, x5, #1
	csel	x24, xzr, x8, lo
	cbz	x5, .LBB76_27
	mov	x27, x4
	mov	x25, x1
	mov	w28, #61152
	ldr	x1, [x27], #24
	mov	x20, x3
	mov	x22, x2
	add	x3, x6, x28
	mov	x2, x6
	mov	x19, x6
	mov	x26, x5
	mov	x23, x4
	mov	x21, x0
	bl	_RNvNtCsemcRClSg8DH_9native_vm4whir11fold_rounds
	cbz	w0, .LBB76_27
	ldr	x8, [x19, #16]
	subs	x8, x25, x8
	csel	x5, xzr, x8, lo
	cmp	x26, #1
	b.ne	.LBB76_4
.LBB76_3:
	mov	x0, x21
	mov	x1, x24
	mov	x2, x23
	mov	x3, x5
	mov	x4, x22
	mov	x5, x20
	mov	x6, x19
	ldp	x20, x19, [sp, #80]
	ldp	x22, x21, [sp, #64]
	ldp	x24, x23, [sp, #48]
	ldp	x26, x25, [sp, #32]
	ldp	x28, x27, [sp, #16]
	ldr	x30, [sp], #96
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w25
	.cfi_restore w26
	.cfi_restore w27
	.cfi_restore w28
	.cfi_restore w30
	b	_RNvNtCsemcRClSg8DH_9native_vm4whir11final_level
.LBB76_4:
	.cfi_restore_state
	ldp	x3, x4, [x23, #24]
	mov	x0, x21
	mov	x1, xzr
	mov	x2, x23
	mov	x6, x19
	bl	_RNvNtCsemcRClSg8DH_9native_vm4whir10next_level
	cbz	w0, .LBB76_27
	ldr	x1, [x23, #24]
	add	x3, x19, x28
	mov	x0, x21
	mov	x2, x19
	bl	_RNvNtCsemcRClSg8DH_9native_vm4whir11fold_rounds
	cbz	w0, .LBB76_27
	ldr	x8, [x19, #16]
	subs	x8, x25, x8
	csel	x5, xzr, x8, lo
	cmp	x24, #1
	b.ne	.LBB76_8
	mov	x23, x27
	b	.LBB76_3
.LBB76_8:
	ldp	x3, x4, [x23, #48]
	mov	x0, x21
	mov	w1, #1
	mov	x2, x27
	mov	x6, x19
	bl	_RNvNtCsemcRClSg8DH_9native_vm4whir10next_level
	cmp	x26, #2
	b.eq	.LBB76_27
	cbz	w0, .LBB76_27
	ldr	x1, [x23, #48]
	add	x3, x19, x28
	mov	x0, x21
	mov	x2, x19
	bl	_RNvNtCsemcRClSg8DH_9native_vm4whir11fold_rounds
	cbz	w0, .LBB76_27
	ldr	x8, [x19, #16]
	subs	x8, x25, x8
	csel	x5, xzr, x8, lo
	cmp	x24, #2
	add	x8, x23, #48
	b.ne	.LBB76_13
.LBB76_12:
	mov	x23, x8
	b	.LBB76_3
.LBB76_13:
	ldp	x3, x4, [x23, #72]
	add	x2, x23, #48
	mov	x0, x21
	mov	w1, #2
	mov	x6, x19
	bl	_RNvNtCsemcRClSg8DH_9native_vm4whir10next_level
	cmp	x26, #3
	b.eq	.LBB76_27
	cbz	w0, .LBB76_27
	ldr	x1, [x23, #72]
	add	x3, x19, x28
	mov	x0, x21
	mov	x2, x19
	bl	_RNvNtCsemcRClSg8DH_9native_vm4whir11fold_rounds
	cbz	w0, .LBB76_27
	ldr	x8, [x19, #16]
	subs	x8, x25, x8
	csel	x5, xzr, x8, lo
	cmp	x24, #3
	add	x8, x23, #72
	b.eq	.LBB76_12
	ldp	x3, x4, [x23, #96]
	add	x2, x23, #72
	mov	x0, x21
	mov	w1, #3
	mov	x6, x19
	bl	_RNvNtCsemcRClSg8DH_9native_vm4whir10next_level
	cmp	x26, #4
	b.eq	.LBB76_27
	cbz	w0, .LBB76_27
	ldr	x1, [x23, #96]
	add	x3, x19, x28
	mov	x0, x21
	mov	x2, x19
	bl	_RNvNtCsemcRClSg8DH_9native_vm4whir11fold_rounds
	cbz	w0, .LBB76_27
	ldr	x8, [x19, #16]
	subs	x8, x25, x8
	csel	x5, xzr, x8, lo
	cmp	x24, #4
	add	x8, x23, #96
	b.eq	.LBB76_12
	ldp	x3, x4, [x23, #120]
	add	x2, x23, #96
	mov	x0, x21
	mov	w1, #4
	mov	x6, x19
	bl	_RNvNtCsemcRClSg8DH_9native_vm4whir10next_level
	cmp	x26, #5
	b.eq	.LBB76_27
	cbz	w0, .LBB76_27
	add	x26, x23, #120
	add	x3, x19, x28
	mov	x0, x21
	ldr	x1, [x26]
	mov	x2, x19
	bl	_RNvNtCsemcRClSg8DH_9native_vm4whir11fold_rounds
	cbz	w0, .LBB76_27
	ldr	x8, [x19, #16]
	subs	x8, x25, x8
	csel	x5, xzr, x8, lo
	cmp	x24, #5
	b.ne	.LBB76_26
	mov	x23, x26
	b	.LBB76_3
.LBB76_26:
	ldp	x3, x4, [x23, #144]
	mov	x0, x21
	mov	w1, #5
	mov	x2, x26
	mov	x6, x19
	bl	_RNvNtCsemcRClSg8DH_9native_vm4whir10next_level
.LBB76_27:
	ldp	x20, x19, [sp, #80]
	mov	w0, wzr
	ldp	x22, x21, [sp, #64]
	ldp	x24, x23, [sp, #48]
	ldp	x26, x25, [sp, #32]
	ldp	x28, x27, [sp, #16]
	ldr	x30, [sp], #96
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w25
	.cfi_restore w26
	.cfi_restore w27
	.cfi_restore w28
	.cfi_restore w30
	ret
.Lfunc_end76:
	.size	_RNvNtCsemcRClSg8DH_9native_vm4whir11whir_levels, .Lfunc_end76-_RNvNtCsemcRClSg8DH_9native_vm4whir11whir_levels
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm4whir14induced_weight,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm4whir14induced_weight,@function
_RNvNtCsemcRClSg8DH_9native_vm4whir14induced_weight:
.Lfunc_begin77:
	.cfi_startproc
	stp	x29, x30, [sp, #-96]!
	.cfi_def_cfa_offset 96
	stp	x28, x27, [sp, #16]
	stp	x26, x25, [sp, #32]
	stp	x24, x23, [sp, #48]
	stp	x22, x21, [sp, #64]
	stp	x20, x19, [sp, #80]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w24, -48
	.cfi_offset w25, -56
	.cfi_offset w26, -64
	.cfi_offset w27, -72
	.cfi_offset w28, -80
	.cfi_offset w30, -88
	.cfi_offset w29, -96
	sub	sp, sp, #1104
	.cfi_def_cfa_offset 1200
	ldr	xzr, [sp]
	mov	x20, x0
	add	x0, sp, #592
	stp	x4, x7, [sp, #72]
	mov	x25, x6
	mov	x23, x5
	mov	x24, x3
	str	x2, [sp, #64]
	add	x19, sp, #592
	bl	_RNvNtCsemcRClSg8DH_9native_vm4whir14subspace_table
	ldr	x8, [sp, #592]
	cbz	x8, .LBB77_9
	add	x8, sp, #88
	ldr	x21, [sp, #600]
	add	x1, x19, #16
	add	x26, x8, #8
	mov	w2, #496
	str	x20, [sp, #16]
	mov	x0, x26
	bl	memcpy
	cmp	x24, x23
	str	x21, [sp, #88]
	csel	x8, x24, x23, lo
	str	x8, [sp, #56]
	cbz	x8, .LBB77_7
	cmp	x21, #32
	mov	w8, #8
	mov	x29, xzr
	csel	x10, x26, x8, lo
	add	x8, sp, #592
	csel	x9, x21, xzr, lo
	mov	x19, xzr
	mov	x22, xzr
	stp	x9, x10, [sp, #40]
	add	x9, x8, #8
	add	x8, x25, #8
	stp	x8, x9, [sp, #24]
	b	.LBB77_4
.LBB77_3:
	ldr	x8, [sp, #56]
	add	x22, x22, #1
	eor	x19, x25, x19
	eor	x29, x26, x29
	cmp	x22, x8
	b.eq	.LBB77_8
.LBB77_4:
	ldr	x8, [sp, #72]
	ldp	x2, x1, [sp, #40]
	add	x0, sp, #592
	add	x8, x8, x22, lsl #4
	ldp	x25, x26, [x8]
	ldr	x8, [sp, #64]
	ldr	x3, [x8, x22, lsl #3]
	bl	_RNvNtCsemcRClSg8DH_9native_vm4whir17subspace_at_table
	ldr	x8, [sp, #592]
	ldr	x9, [sp, #80]
	cmp	x8, x9
	csel	x21, x8, x9, lo
	cmp	x21, #0
	ccmp	x8, #31, #2, ne
	b.hi	.LBB77_3
	ldp	x23, x24, [sp, #24]
.LBB77_6:
	ldp	x1, x27, [x23, #-8]
	ldr	x20, [x24], #8
	eor	x0, x20, #0x1
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field4kmul
	mov	x28, x0
	eor	x0, x20, #0x1
	mov	x1, x27
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field4kmul
	mov	x3, x0
	eor	x2, x28, #0x1
	mov	x0, x25
	mov	x1, x26
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	mov	x25, x0
	mov	x26, x1
	subs	x21, x21, #1
	add	x23, x23, #16
	b.ne	.LBB77_6
	b	.LBB77_3
.LBB77_7:
	mov	x19, xzr
	mov	x29, xzr
.LBB77_8:
	ldr	x20, [sp, #16]
	mov	w8, #1
	stp	x19, x29, [x20, #8]
.LBB77_9:
	str	x8, [x20]
	add	sp, sp, #1104
	.cfi_def_cfa_offset 96
	ldp	x20, x19, [sp, #80]
	ldp	x22, x21, [sp, #64]
	ldp	x24, x23, [sp, #48]
	ldp	x26, x25, [sp, #32]
	ldp	x28, x27, [sp, #16]
	ldp	x29, x30, [sp], #96
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w25
	.cfi_restore w26
	.cfi_restore w27
	.cfi_restore w28
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end77:
	.size	_RNvNtCsemcRClSg8DH_9native_vm4whir14induced_weight, .Lfunc_end77-_RNvNtCsemcRClSg8DH_9native_vm4whir14induced_weight
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm4whir14sample_queries,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm4whir14sample_queries,@function
_RNvNtCsemcRClSg8DH_9native_vm4whir14sample_queries:
.Lfunc_begin78:
	.cfi_startproc
	str	xzr, [x3]
	cbz	x2, .LBB78_5
	sub	sp, sp, #112
	.cfi_def_cfa_offset 112
	stp	x29, x30, [sp, #16]
	stp	x28, x27, [sp, #32]
	stp	x26, x25, [sp, #48]
	stp	x24, x23, [sp, #64]
	stp	x22, x21, [sp, #80]
	stp	x20, x19, [sp, #96]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w24, -48
	.cfi_offset w25, -56
	.cfi_offset w26, -64
	.cfi_offset w27, -72
	.cfi_offset w28, -80
	.cfi_offset w30, -88
	.cfi_offset w29, -96
	.cfi_remember_state
	mov	x19, x2
	mov	x22, x1
	mov	x20, x0
	cmp	x1, #129
	b.hs	.LBB78_3
	mov	x21, x3
	mov	x25, xzr
	mov	x28, xzr
	mov	w26, #230
	adrp	x27, .Lanon.a75d6d9e6a8990b4224ef13f18552af8.10
	add	x27, x27, :lo12:.Lanon.a75d6d9e6a8990b4224ef13f18552af8.10
	mov	x29, x19
	b	.LBB78_8
.LBB78_3:
	mov	x0, x20
	bl	_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW7squeeze
	subs	x19, x19, #1
	b.ne	.LBB78_3
.LBB78_4:
	mov	w0, #1
	b	.LBB78_14
.LBB78_5:
	.cfi_def_cfa wsp, 0
	.cfi_same_value w19
	.cfi_same_value w20
	.cfi_same_value w21
	.cfi_same_value w22
	.cfi_same_value w23
	.cfi_same_value w24
	.cfi_same_value w25
	.cfi_same_value w26
	.cfi_same_value w27
	.cfi_same_value w28
	.cfi_same_value w30
	.cfi_same_value w29
	mov	w0, #1
	ret
.LBB78_6:
	.cfi_restore_state
	ldp	x8, x25, [sp]
	sub	x28, x26, #1
	mov	w26, #230
	adrp	x27, .Lanon.a75d6d9e6a8990b4224ef13f18552af8.10
	add	x27, x27, :lo12:.Lanon.a75d6d9e6a8990b4224ef13f18552af8.10
.LBB78_7:
	add	x25, x25, #1
	sub	x29, x29, x8
	mov	w0, #1
	cmp	x25, x19
	b.eq	.LBB78_14
.LBB78_8:
	cbz	x29, .LBB78_4
	mov	x0, x20
	bl	_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW7squeeze
	ldrb	w8, [x27, x22]
	cmp	x29, x8
	csel	x8, x29, x8, lo
	cbz	x22, .LBB78_7
	cmp	x8, #1
	mov	x9, x28
	stp	x8, x25, [sp]
	csinc	x28, x8, xzr, hi
	cmp	x9, #230
	mov	x23, x0
	csel	x8, x9, x26, lo
	mov	x24, x1
	mov	x25, xzr
	sub	x27, x8, #230
	add	x26, x9, #1
.LBB78_11:
	cbz	x27, .LBB78_13
	mov	x0, x23
	mov	x1, x24
	mov	x2, x25
	mov	x3, x22
	bl	_RNvNtCsemcRClSg8DH_9native_vm4whir10query_bits
	str	x0, [x21, x26, lsl #3]
	subs	x28, x28, #1
	add	x25, x25, x22
	str	x26, [x21]
	add	x27, x27, #1
	add	x26, x26, #1
	b.ne	.LBB78_11
	b	.LBB78_6
.LBB78_13:
	mov	w0, wzr
.LBB78_14:
	ldp	x20, x19, [sp, #96]
	ldp	x22, x21, [sp, #80]
	ldp	x24, x23, [sp, #64]
	ldp	x26, x25, [sp, #48]
	ldp	x28, x27, [sp, #32]
	ldp	x29, x30, [sp, #16]
	add	sp, sp, #112
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w25
	.cfi_restore w26
	.cfi_restore w27
	.cfi_restore w28
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end78:
	.size	_RNvNtCsemcRClSg8DH_9native_vm4whir14sample_queries, .Lfunc_end78-_RNvNtCsemcRClSg8DH_9native_vm4whir14sample_queries
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm4whir14subspace_table,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm4whir14subspace_table,@function
_RNvNtCsemcRClSg8DH_9native_vm4whir14subspace_table:
.Lfunc_begin79:
	.cfi_startproc
	stp	x29, x30, [sp, #-96]!
	.cfi_def_cfa_offset 96
	stp	x28, x27, [sp, #16]
	stp	x26, x25, [sp, #32]
	stp	x24, x23, [sp, #48]
	stp	x22, x21, [sp, #64]
	stp	x20, x19, [sp, #80]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w24, -48
	.cfi_offset w25, -56
	.cfi_offset w26, -64
	.cfi_offset w27, -72
	.cfi_offset w28, -80
	.cfi_offset w30, -88
	.cfi_offset w29, -96
	sub	sp, sp, #768
	.cfi_def_cfa_offset 864
	mov	x20, x1
	mov	x19, x0
	add	x0, sp, #16
	mov	w1, wzr
	mov	w2, #248
	add	x21, sp, #16
	bl	memset
	cmp	x20, #32
	b.hs	.LBB79_4
	lsl	x24, x20, #3
	str	x19, [sp, #8]
	cbz	x20, .LBB79_10
	sub	x8, x24, #8
	add	x9, sp, #16
	cmp	x8, #24
	b.hs	.LBB79_5
	mov	x8, xzr
	b	.LBB79_8
.LBB79_4:
	str	xzr, [x19]
	b	.LBB79_18
.LBB79_5:
	lsr	x8, x8, #3
	add	x11, x9, #16
	mov	w12, #1
	mov	w13, #2
	mov	w14, #4
	mov	w15, #8
	add	x10, x8, #1
	mov	w16, #16
	and	x8, x10, #0x3ffffffffffffffc
	and	x17, x10, #0x3ffffffffffffffc
	add	x9, x9, x8, lsl #3
.LBB79_6:
	sub	x18, x12, #1
	subs	x17, x17, #4
	add	x12, x12, #4
	lsl	x0, x13, x18
	lsl	x1, x14, x18
	lsl	x2, x15, x18
	lsl	x18, x16, x18
	stp	x0, x1, [x11, #-16]
	stp	x2, x18, [x11], #32
	b.ne	.LBB79_6
	cmp	x10, x8
	b.eq	.LBB79_10
.LBB79_8:
	add	x10, x21, x24
	mov	w11, #2
.LBB79_9:
	lsl	x12, x11, x8
	add	x8, x8, #1
	str	x12, [x9], #8
	cmp	x9, x10
	b.ne	.LBB79_9
.LBB79_10:
	mov	w0, #1
	str	xzr, [sp, #264]
	mov	w25, #1
	stp	xzr, xzr, [sp, #288]
	stp	xzr, xzr, [sp, #304]
	stp	xzr, xzr, [sp, #320]
	stp	xzr, xzr, [sp, #336]
	stp	xzr, xzr, [sp, #352]
	stp	xzr, xzr, [sp, #368]
	stp	xzr, xzr, [sp, #384]
	stp	xzr, xzr, [sp, #400]
	stp	xzr, xzr, [sp, #416]
	stp	xzr, xzr, [sp, #432]
	stp	xzr, xzr, [sp, #448]
	stp	xzr, xzr, [sp, #464]
	stp	xzr, xzr, [sp, #480]
	stp	xzr, xzr, [sp, #496]
	str	xzr, [sp, #512]
	str	xzr, [sp, #520]
	str	xzr, [sp, #528]
	str	xzr, [sp, #536]
	str	xzr, [sp, #544]
	str	xzr, [sp, #552]
	str	xzr, [sp, #560]
	str	xzr, [sp, #568]
	str	xzr, [sp, #576]
	str	xzr, [sp, #584]
	str	xzr, [sp, #592]
	str	xzr, [sp, #600]
	str	xzr, [sp, #608]
	str	xzr, [sp, #616]
	str	xzr, [sp, #624]
	str	xzr, [sp, #632]
	str	xzr, [sp, #640]
	str	xzr, [sp, #648]
	str	xzr, [sp, #656]
	str	xzr, [sp, #664]
	str	xzr, [sp, #672]
	str	xzr, [sp, #680]
	str	xzr, [sp, #688]
	str	xzr, [sp, #696]
	str	xzr, [sp, #704]
	str	xzr, [sp, #712]
	str	xzr, [sp, #720]
	str	xzr, [sp, #728]
	str	xzr, [sp, #736]
	str	xzr, [sp, #744]
	str	xzr, [sp, #752]
	str	xzr, [sp, #760]
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field4kinv
	stp	x25, x0, [sp, #272]
	cbz	x20, .LBB79_16
	add	x8, sp, #264
	mov	x26, xzr
	mov	w21, #1
	add	x27, x8, #8
	add	x28, sp, #16
	mov	w25, #1
.LBB79_12:
	cmp	x20, x26
	add	x19, x28, x26, lsl #3
	csel	x8, x20, x26, lo
	sub	x29, x24, x8, lsl #3
.LBB79_13:
	ldr	x22, [x19]
	mov	x0, x22
	mov	x1, x22
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field4kmul
	mov	x23, x0
	mov	x0, x21
	mov	x1, x22
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field4kmul
	subs	x29, x29, #8
	eor	x8, x0, x23
	str	x8, [x19], #8
	b.ne	.LBB79_13
	ldr	x21, [x28, x26, lsl #3]
	mov	x0, x21
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field4kinv
	cmp	x26, #30
	b.eq	.LBB79_17
	add	x8, x27, x25, lsl #4
	add	x26, x26, #1
	add	x25, x25, #1
	cmp	x26, x20
	stp	x21, x0, [x8]
	b.ne	.LBB79_12
.LBB79_16:
	ldr	x19, [sp, #8]
	add	x1, sp, #264
	mov	w2, #504
	str	x25, [sp, #264]
	add	x0, x19, #8
	bl	memcpy
	mov	w8, #1
	str	x8, [x19]
	b	.LBB79_18
.LBB79_17:
	ldr	x8, [sp, #8]
	str	xzr, [x8]
.LBB79_18:
	add	sp, sp, #768
	.cfi_def_cfa_offset 96
	ldp	x20, x19, [sp, #80]
	ldp	x22, x21, [sp, #64]
	ldp	x24, x23, [sp, #48]
	ldp	x26, x25, [sp, #32]
	ldp	x28, x27, [sp, #16]
	ldp	x29, x30, [sp], #96
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w25
	.cfi_restore w26
	.cfi_restore w27
	.cfi_restore w28
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end79:
	.size	_RNvNtCsemcRClSg8DH_9native_vm4whir14subspace_table, .Lfunc_end79-_RNvNtCsemcRClSg8DH_9native_vm4whir14subspace_table
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm4whir17subspace_at_table,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm4whir17subspace_at_table,@function
_RNvNtCsemcRClSg8DH_9native_vm4whir17subspace_at_table:
.Lfunc_begin80:
	.cfi_startproc
	sub	sp, sp, #336
	.cfi_def_cfa_offset 336
	stp	x29, x30, [sp, #256]
	stp	x26, x25, [sp, #272]
	stp	x24, x23, [sp, #288]
	stp	x22, x21, [sp, #304]
	stp	x20, x19, [sp, #320]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w24, -48
	.cfi_offset w25, -56
	.cfi_offset w26, -64
	.cfi_offset w30, -72
	.cfi_offset w29, -80
	mov	x8, sp
	mov	x20, x2
	mov	x23, x1
	add	x21, x8, #8
	mov	x19, x0
	mov	w1, wzr
	mov	x0, x21
	mov	w2, #248
	mov	x22, x3
	bl	memset
	cbz	x20, .LBB80_3
	add	x25, x23, #8
	mov	x26, x20
.LBB80_2:
	ldp	x23, x1, [x25, #-8]
	mov	x0, x22
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field4kmul
	str	x0, [x21], #8
	mov	x0, x22
	mov	x1, x22
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field4kmul
	mov	x24, x0
	mov	x0, x23
	mov	x1, x22
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field4kmul
	subs	x26, x26, #1
	eor	x22, x0, x24
	add	x25, x25, #16
	b.ne	.LBB80_2
.LBB80_3:
	mov	x1, sp
	mov	x0, x19
	mov	w2, #256
	str	x20, [sp]
	bl	memcpy
	ldp	x20, x19, [sp, #320]
	ldp	x22, x21, [sp, #304]
	ldp	x24, x23, [sp, #288]
	ldp	x26, x25, [sp, #272]
	ldp	x29, x30, [sp, #256]
	add	sp, sp, #336
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w25
	.cfi_restore w26
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end80:
	.size	_RNvNtCsemcRClSg8DH_9native_vm4whir17subspace_at_table, .Lfunc_end80-_RNvNtCsemcRClSg8DH_9native_vm4whir17subspace_at_table
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm4whir22verify_stacked_opening,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm4whir22verify_stacked_opening,@function
_RNvNtCsemcRClSg8DH_9native_vm4whir22verify_stacked_opening:
.Lfunc_begin81:
	.cfi_startproc
	stp	x29, x30, [sp, #-96]!
	.cfi_def_cfa_offset 96
	stp	x28, x27, [sp, #16]
	stp	x26, x25, [sp, #32]
	stp	x24, x23, [sp, #48]
	stp	x22, x21, [sp, #64]
	stp	x20, x19, [sp, #80]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w24, -48
	.cfi_offset w25, -56
	.cfi_offset w26, -64
	.cfi_offset w27, -72
	.cfi_offset w28, -80
	.cfi_offset w30, -88
	.cfi_offset w29, -96
	sub	sp, sp, #416
	.cfi_def_cfa_offset 512
	mov	x8, x5
	mov	x26, x7
	mov	x20, x6
	ldr	x9, [x8], #8
	mov	x21, x5
	mov	x24, x3
	mov	x22, x1
	cmp	x9, #161
	csel	x29, x9, xzr, lo
	mov	w9, #8
	csel	x28, x8, x9, lo
	cbz	x29, .LBB81_8
	mov	x8, xzr
	add	x9, x22, #120
	mov	x10, x28
	mov	x11, x29
	b	.LBB81_3
.LBB81_2:
	add	x12, x12, x12, lsl #1
	ldr	x12, [x9, x12, lsl #3]
	cmp	x12, #0
	cset	w12, ne
	subs	x11, x11, #1
	add	x10, x10, #608
	add	x8, x12, x8
	b.eq	.LBB81_5
.LBB81_3:
	ldr	x12, [x10]
	cmp	x12, #157
	b.ls	.LBB81_2
	subs	x11, x11, #1
	add	x10, x10, #608
	add	x8, xzr, x8
	b.ne	.LBB81_3
.LBB81_5:
	add	x27, x8, #2
	cmp	x27, #512
	b.hi	.LBB81_27
	mov	x23, x4
	mov	x19, x2
	str	x0, [sp, #16]
	bl	_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW7squeeze
	cmp	x27, #162
	b.hi	.LBB81_27
	str	x23, [sp, #24]
	str	x19, [sp, #48]
	b	.LBB81_9
.LBB81_8:
	stp	x0, x4, [sp, #16]
	str	x2, [sp, #48]
	bl	_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW7squeeze
	mov	w27, #2
.LBB81_9:
	add	x2, x26, #8
	mov	x3, x27
	add	x19, x26, #8
	str	x27, [x26]
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field6powers
	ldr	x8, [x26]
	str	x21, [sp, #32]
	cmp	x8, #163
	csel	x25, x8, xzr, lo
	mov	w8, #8
	csel	x23, x19, x8, lo
	cbz	x25, .LBB81_11
	ldp	x0, x1, [x23]
	add	x19, x23, #16
	b	.LBB81_12
.LBB81_11:
	mov	x1, xzr
	mov	x0, xzr
	mov	x19, x23
.LBB81_12:
	ldp	x2, x3, [x24]
	add	x21, x23, x25, lsl #4
	str	x20, [sp, #40]
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	mov	x27, x0
	mov	x26, x1
	cbz	x29, .LBB81_21
	mov	w8, #608
	add	x20, x22, #120
	mul	x29, x29, x8
	b	.LBB81_17
.LBB81_14:
	ldp	x0, x1, [x19], #16
.LBB81_15:
	ldr	x2, [x28, #592]
	ldr	x3, [x28, #600]
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	eor	x27, x0, x27
	eor	x26, x1, x26
.LBB81_16:
	subs	x29, x29, #608
	add	x28, x28, #608
	b.eq	.LBB81_21
.LBB81_17:
	ldr	x8, [x28]
	cmp	x8, #157
	b.hi	.LBB81_16
	add	x8, x8, x8, lsl #1
	ldr	x8, [x20, x8, lsl #3]
	cbz	x8, .LBB81_16
	cmp	x19, x21
	b.ne	.LBB81_14
	mov	x1, xzr
	mov	x0, xzr
	b	.LBB81_15
.LBB81_21:
	cmp	x19, x21
	b.eq	.LBB81_23
	ldp	x0, x1, [x19]
	b	.LBB81_24
.LBB81_23:
	mov	x1, xzr
	mov	x0, xzr
.LBB81_24:
	ldp	x20, x19, [sp, #32]
	ldp	x2, x3, [x19, #488]
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	ldr	x21, [x22, #16]
	ldr	x8, [sp, #24]
	mov	x28, x0
	ldr	x2, [sp, #48]
	mov	x29, x1
	add	x0, sp, #256
	mov	x1, x21
	stp	x23, x25, [sp, #56]
	stp	x22, x24, [sp, #72]
	stp	x8, x20, [sp, #88]
	str	x19, [sp, #104]
	add	x19, sp, #256
	bl	_RNvNtCsemcRClSg8DH_9native_vm4whir6ladder
	ldr	w8, [sp, #256]
	tbz	w8, #0, .LBB81_27
	add	x0, sp, #112
	add	x1, x19, #8
	mov	w2, #144
	bl	memcpy
	ldr	x5, [sp, #408]
	cmp	x5, #7
	b.hs	.LBB81_27
	ldr	x6, [sp, #512]
	eor	x8, x28, x27
	eor	x9, x29, x26
	cmp	x5, #0
	ldr	x0, [sp, #16]
	add	x3, sp, #56
	stp	x8, x9, [x6]
	ldr	x8, [sp, #112]
	add	x4, sp, #112
	mov	x1, x21
	str	xzr, [x6, #16]
	csel	x2, xzr, x8, eq
	str	xzr, [x6, #504]
	bl	_RNvNtCsemcRClSg8DH_9native_vm4whir11whir_levels
	b	.LBB81_28
.LBB81_27:
	mov	w0, wzr
.LBB81_28:
	add	sp, sp, #416
	.cfi_def_cfa_offset 96
	ldp	x20, x19, [sp, #80]
	ldp	x22, x21, [sp, #64]
	ldp	x24, x23, [sp, #48]
	ldp	x26, x25, [sp, #32]
	ldp	x28, x27, [sp, #16]
	ldp	x29, x30, [sp], #96
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w25
	.cfi_restore w26
	.cfi_restore w27
	.cfi_restore w28
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end81:
	.size	_RNvNtCsemcRClSg8DH_9native_vm4whir22verify_stacked_opening, .Lfunc_end81-_RNvNtCsemcRClSg8DH_9native_vm4whir22verify_stacked_opening
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm4whir6ladder,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm4whir6ladder,@function
_RNvNtCsemcRClSg8DH_9native_vm4whir6ladder:
.Lfunc_begin82:
	.cfi_startproc
	sub	x16, x2, #1
	sub	x15, x1, #16
	cmp	x16, #4
	ccmp	x15, #15, #2, lo
	b.hs	.LBB82_11
	cmp	x1, #20
	b.ge	.LBB82_3
	mov	x8, xzr
	mov	x12, xzr
	mov	x14, xzr
	mov	x9, xzr
	mov	x11, xzr
	mov	x10, xzr
	mov	w13, #3
	b	.LBB82_8
.LBB82_3:
	cmp	x1, #24
	add	x8, x2, #9
	b.ge	.LBB82_5
	mov	x14, xzr
	mov	x9, xzr
	mov	x11, xzr
	mov	x10, xzr
	mov	w12, #4
	mov	w13, #4
	b	.LBB82_8
.LBB82_5:
	cmp	x1, #28
	add	x9, x2, #12
	b.ge	.LBB82_7
	mov	x11, xzr
	mov	x10, xzr
	mov	w13, #5
	mov	w12, #4
	mov	w14, #4
	b	.LBB82_8
.LBB82_7:
	add	x10, x2, #15
	mov	w13, #6
	mov	w12, #4
	mov	w14, #4
	mov	w11, #4
.LBB82_8:
	mov	w17, #120
	adrp	x18, .Lanon.a75d6d9e6a8990b4224ef13f18552af8.12
	add	x18, x18, :lo12:.Lanon.a75d6d9e6a8990b4224ef13f18552af8.12
	madd	x17, x16, x17, x18
	ldr	x17, [x17, x15, lsl #3]
	cmp	x17, x13
	b.ne	.LBB82_11
	mov	w17, #720
	adrp	x18, .Lanon.a75d6d9e6a8990b4224ef13f18552af8.11
	add	x18, x18, :lo12:.Lanon.a75d6d9e6a8990b4224ef13f18552af8.11
	madd	x16, x16, x17, x18
	mov	w17, #48
	sub	x6, x13, #1
	cmp	x6, #2
	add	x1, x2, #3
	madd	x5, x15, x17, x16
	add	x17, x2, #6
	ldp	x18, x16, [x5]
	ldr	x15, [x5, #16]
	b.ne	.LBB82_12
	mov	x3, xzr
	b	.LBB82_13
.LBB82_11:
	str	xzr, [x0]
	ret
.LBB82_12:
	ldr	x3, [x5, #24]
	cmp	x6, #3
	b.ne	.LBB82_16
.LBB82_13:
	mov	x4, xzr
.LBB82_14:
	mov	x5, xzr
.LBB82_15:
	mov	w6, #6
	stp	x8, x3, [x0, #88]
	mov	w8, #1
	stp	x6, x2, [x0, #8]
	mov	w2, #4
	stp	x18, x2, [x0, #24]
	stp	x1, x16, [x0, #40]
	stp	x2, x17, [x0, #56]
	stp	x15, x12, [x0, #72]
	stp	x14, x9, [x0, #104]
	stp	x4, x11, [x0, #120]
	stp	x10, x5, [x0, #136]
	str	x13, [x0, #152]
	str	x8, [x0]
	ret
.LBB82_16:
	ldr	x4, [x5, #32]
	cmp	x6, #4
	b.eq	.LBB82_14
	ldr	x5, [x5, #40]
	b	.LBB82_15
.Lfunc_end82:
	.size	_RNvNtCsemcRClSg8DH_9native_vm4whir6ladder, .Lfunc_end82-_RNvNtCsemcRClSg8DH_9native_vm4whir6ladder
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm4whir8fold_row,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm4whir8fold_row,@function
_RNvNtCsemcRClSg8DH_9native_vm4whir8fold_row:
.Lfunc_begin83:
	.cfi_startproc
	sub	sp, sp, #128
	.cfi_def_cfa_offset 128
	stp	x29, x30, [sp, #32]
	stp	x28, x27, [sp, #48]
	stp	x26, x25, [sp, #64]
	stp	x24, x23, [sp, #80]
	stp	x22, x21, [sp, #96]
	stp	x20, x19, [sp, #112]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w24, -48
	.cfi_offset w25, -56
	.cfi_offset w26, -64
	.cfi_offset w27, -72
	.cfi_offset w28, -80
	.cfi_offset w30, -88
	.cfi_offset w29, -96
	mov	x26, x1
	stp	x4, x0, [sp, #16]
	cbz	x4, .LBB83_37
	ldp	x1, x25, [x3, #16]
	mov	x0, x2
	ldp	x27, x28, [x3]
	mov	x22, x3
	mov	x19, x2
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field4kmul
	mov	x24, x0
	mov	x0, x19
	mov	x1, x25
	str	x19, [sp]
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field4kmul
	str	x26, [sp, #8]
	lsr	x26, x26, #1
	cbz	x26, .LBB83_6
	ldr	x8, [sp, #24]
	mov	x25, x0
	mov	x29, xzr
	add	x20, x8, #8
	add	x23, x8, #16
	b	.LBB83_4
.LBB83_3:
	add	x29, x29, #1
	add	x20, x20, #16
	add	x23, x23, #32
	cmp	x26, x29
	b.eq	.LBB83_6
.LBB83_4:
	cmp	x29, #31
	b.hi	.LBB83_3
	ldp	x2, x3, [x23, #-16]
	eor	x0, x24, x27
	ldp	x19, x21, [x23]
	eor	x1, x25, x28
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	eor	x8, x0, x19
	eor	x9, x1, x21
	stp	x8, x9, [x20, #-8]
	b	.LBB83_3
.LBB83_6:
	ldr	x8, [sp, #16]
	cmp	x8, #1
	b.eq	.LBB83_37
	ldp	x1, x25, [x22, #48]
	ldr	x19, [sp]
	ldp	x27, x28, [x22, #32]
	mov	x0, x19
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field4kmul
	mov	x24, x0
	mov	x0, x19
	mov	x1, x25
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field4kmul
	ldr	x8, [sp, #8]
	lsr	x26, x8, #2
	cbz	x26, .LBB83_12
	ldr	x8, [sp, #24]
	mov	x25, x0
	mov	x29, xzr
	add	x20, x8, #8
	add	x23, x8, #16
	b	.LBB83_10
.LBB83_9:
	add	x29, x29, #1
	add	x20, x20, #16
	add	x23, x23, #32
	cmp	x26, x29
	b.eq	.LBB83_12
.LBB83_10:
	cmp	x29, #31
	b.hi	.LBB83_9
	ldp	x2, x3, [x23, #-16]
	eor	x0, x24, x27
	ldp	x21, x19, [x23]
	eor	x1, x25, x28
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	eor	x8, x0, x21
	eor	x9, x1, x19
	stp	x8, x9, [x20, #-8]
	b	.LBB83_9
.LBB83_12:
	ldr	x8, [sp, #16]
	cmp	x8, #2
	b.eq	.LBB83_37
	ldp	x1, x25, [x22, #80]
	ldr	x19, [sp]
	ldp	x27, x28, [x22, #64]
	mov	x0, x19
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field4kmul
	mov	x24, x0
	mov	x0, x19
	mov	x1, x25
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field4kmul
	ldr	x8, [sp, #8]
	lsr	x26, x8, #3
	cbz	x26, .LBB83_18
	ldr	x8, [sp, #24]
	mov	x25, x0
	mov	x29, xzr
	add	x20, x8, #8
	add	x23, x8, #16
	b	.LBB83_16
.LBB83_15:
	add	x29, x29, #1
	add	x20, x20, #16
	add	x23, x23, #32
	cmp	x26, x29
	b.eq	.LBB83_18
.LBB83_16:
	cmp	x29, #31
	b.hi	.LBB83_15
	ldp	x2, x3, [x23, #-16]
	eor	x0, x24, x27
	ldp	x19, x21, [x23]
	eor	x1, x25, x28
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	eor	x8, x0, x19
	eor	x9, x1, x21
	stp	x8, x9, [x20, #-8]
	b	.LBB83_15
.LBB83_18:
	ldr	x8, [sp, #16]
	cmp	x8, #3
	b.eq	.LBB83_37
	ldp	x1, x25, [x22, #112]
	ldr	x19, [sp]
	ldp	x27, x28, [x22, #96]
	mov	x0, x19
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field4kmul
	mov	x24, x0
	mov	x0, x19
	mov	x1, x25
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field4kmul
	ldr	x8, [sp, #8]
	lsr	x26, x8, #4
	cbz	x26, .LBB83_24
	ldr	x8, [sp, #24]
	mov	x25, x0
	mov	x29, xzr
	add	x20, x8, #8
	add	x23, x8, #16
	b	.LBB83_22
.LBB83_21:
	add	x29, x29, #1
	add	x20, x20, #16
	add	x23, x23, #32
	cmp	x26, x29
	b.eq	.LBB83_24
.LBB83_22:
	cmp	x29, #31
	b.hi	.LBB83_21
	ldp	x2, x3, [x23, #-16]
	eor	x0, x24, x27
	ldp	x19, x21, [x23]
	eor	x1, x25, x28
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	eor	x8, x0, x19
	eor	x9, x1, x21
	stp	x8, x9, [x20, #-8]
	b	.LBB83_21
.LBB83_24:
	ldr	x8, [sp, #16]
	cmp	x8, #4
	b.eq	.LBB83_37
	ldp	x1, x25, [x22, #144]
	ldr	x19, [sp]
	ldp	x27, x28, [x22, #128]
	mov	x0, x19
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field4kmul
	mov	x24, x0
	mov	x0, x19
	mov	x1, x25
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field4kmul
	ldr	x8, [sp, #8]
	lsr	x26, x8, #5
	cbz	x26, .LBB83_30
	ldr	x8, [sp, #24]
	mov	x25, x0
	mov	x29, xzr
	add	x20, x8, #8
	add	x23, x8, #16
	b	.LBB83_28
.LBB83_27:
	add	x29, x29, #1
	add	x20, x20, #16
	add	x23, x23, #32
	cmp	x26, x29
	b.eq	.LBB83_30
.LBB83_28:
	cmp	x29, #31
	b.hi	.LBB83_27
	ldp	x2, x3, [x23, #-16]
	eor	x0, x24, x27
	ldp	x19, x21, [x23]
	eor	x1, x25, x28
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	eor	x8, x0, x19
	eor	x9, x1, x21
	stp	x8, x9, [x20, #-8]
	b	.LBB83_27
.LBB83_30:
	ldr	x8, [sp, #16]
	cmp	x8, #5
	b.eq	.LBB83_37
	ldp	x1, x23, [x22, #176]
	ldr	x19, [sp]
	ldp	x24, x25, [x22, #160]
	mov	x0, x19
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field4kmul
	mov	x22, x0
	mov	x0, x19
	mov	x1, x23
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field4kmul
	ldr	x8, [sp, #8]
	lsr	x21, x8, #6
	cbz	x21, .LBB83_36
	ldr	x8, [sp, #24]
	mov	x20, x0
	mov	x23, xzr
	mov	w26, #1
	add	x27, x8, #8
	add	x28, x8, #16
	b	.LBB83_34
.LBB83_33:
	add	x23, x23, #1
	add	x27, x27, #16
	add	x28, x28, #32
	cmp	x21, x23
	b.eq	.LBB83_37
.LBB83_34:
	cmp	x23, #31
	b.hi	.LBB83_33
	ldp	x2, x3, [x28, #-16]
	eor	x0, x22, x24
	ldp	x19, x29, [x28]
	eor	x1, x20, x25
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	eor	x8, x0, x19
	eor	x9, x1, x29
	stp	x8, x9, [x27, #-8]
	b	.LBB83_33
.LBB83_36:
	mov	x26, xzr
.LBB83_37:
	ldr	x9, [sp, #24]
	cmp	x26, #0
	ldp	x20, x19, [sp, #112]
	ldp	x8, x9, [x9]
	ldp	x22, x21, [sp, #96]
	ldp	x24, x23, [sp, #80]
	ldp	x26, x25, [sp, #64]
	csel	x1, xzr, x9, eq
	ldp	x28, x27, [sp, #48]
	csel	x0, xzr, x8, eq
	ldp	x29, x30, [sp, #32]
	add	sp, sp, #128
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w25
	.cfi_restore w26
	.cfi_restore w27
	.cfi_restore w28
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end83:
	.size	_RNvNtCsemcRClSg8DH_9native_vm4whir8fold_row, .Lfunc_end83-_RNvNtCsemcRClSg8DH_9native_vm4whir8fold_row
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm4whir8lanes_of,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm4whir8lanes_of,@function
_RNvNtCsemcRClSg8DH_9native_vm4whir8lanes_of:
.Lfunc_begin84:
	.cfi_startproc
	cbz	x0, .LBB84_5
	cmp	x2, #130
	b.hs	.LBB84_15
	lsr	x2, x2, #1
	cbz	x2, .LBB84_19
	cmp	x2, #1
	b.ne	.LBB84_16
	mov	x8, xzr
	b	.LBB84_20
.LBB84_5:
	cmp	x2, #65
	b.hs	.LBB84_15
	cbz	x2, .LBB84_19
	lsl	x9, x2, #4
	lsl	x13, x2, #3
	sub	x8, x13, #8
	sub	x10, x9, #16
	lsr	x8, x8, #3
	lsr	x10, x10, #4
	cmp	x8, x10
	csel	x11, x8, x10, lo
	add	x10, x1, x13
	mov	x8, x3
	cmp	x11, #3
	b.lo	.LBB84_11
	add	x11, x11, #1
	add	x14, x13, x1
	add	x13, x3, #32
	and	x12, x11, #0x1ffffffffffffffc
	sub	x14, x14, #16
	and	x15, x11, #0x1ffffffffffffffc
	add	x8, x3, x12, lsl #4
	sub	x10, x10, x12, lsl #3
.LBB84_9:
	ldp	x17, x16, [x14]
	sub	x15, x15, #4
	stp	x16, xzr, [x13, #-32]
	stp	x17, xzr, [x13, #-16]
	ldp	x17, x16, [x14, #-16]
	sub	x14, x14, #32
	stp	x16, xzr, [x13]
	stp	x17, xzr, [x13, #16]
	add	x13, x13, #64
	cbnz	x15, .LBB84_9
	cmp	x11, x12
	b.eq	.LBB84_19
.LBB84_11:
	sub	x10, x10, #8
	add	x9, x3, x9
	mov	w0, #1
	mov	x11, x10
.LBB84_12:
	ldr	x13, [x11], #-8
	add	x12, x8, #16
	cmp	x12, x9
	stp	x13, xzr, [x8]
	b.eq	.LBB84_14
	cmp	x10, x1
	mov	x10, x11
	mov	x8, x12
	b.ne	.LBB84_12
.LBB84_14:
	mov	x1, x2
	ret
.LBB84_15:
	mov	x0, xzr
	mov	x1, x2
	ret
.LBB84_16:
	and	x8, x2, #0x7e
	add	x9, x3, #16
	add	x10, x1, #16
	and	x11, x2, #0x7e
.LBB84_17:
	ldp	x12, x13, [x10, #-16]
	subs	x11, x11, #2
	stp	x12, x13, [x9, #-16]
	ldp	x12, x14, [x10], #32
	stp	x12, x14, [x9], #32
	b.ne	.LBB84_17
	cmp	x2, x8
	b.ne	.LBB84_20
.LBB84_19:
	mov	w0, #1
	mov	x1, x2
	ret
.LBB84_20:
	mov	w9, #8
	mov	w0, #1
	orr	x10, x9, x8, lsl #4
	sub	x8, x2, x8
	add	x9, x1, x10
	add	x10, x3, x10
.LBB84_21:
	ldp	x11, x12, [x9, #-8]
	subs	x8, x8, #1
	add	x9, x9, #16
	stp	x11, x12, [x10, #-8]
	add	x10, x10, #16
	b.ne	.LBB84_21
	b	.LBB84_14
.Lfunc_end84:
	.size	_RNvNtCsemcRClSg8DH_9native_vm4whir8lanes_of, .Lfunc_end84-_RNvNtCsemcRClSg8DH_9native_vm4whir8lanes_of
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm4wire11climb_level,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm4wire11climb_level,@function
_RNvNtCsemcRClSg8DH_9native_vm4wire11climb_level:
.Lfunc_begin85:
	.cfi_startproc
	sub	sp, sp, #224
	.cfi_def_cfa_offset 224
	stp	x29, x30, [sp, #128]
	stp	x28, x27, [sp, #144]
	stp	x26, x25, [sp, #160]
	stp	x24, x23, [sp, #176]
	stp	x22, x21, [sp, #192]
	stp	x20, x19, [sp, #208]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w24, -48
	.cfi_offset w25, -56
	.cfi_offset w26, -64
	.cfi_offset w27, -72
	.cfi_offset w28, -80
	.cfi_offset w30, -88
	.cfi_offset w29, -96
	stp	x0, x4, [sp, #8]
	cbz	x2, .LBB85_13
	add	x8, x2, x2, lsl #2
	mov	x22, x3
	mov	x23, x1
	mov	x19, xzr
	mov	x20, xzr
	add	x27, sp, #24
	lsl	x25, x8, #3
	sub	x29, x1, #40
	add	x28, x1, x25
	b	.LBB85_5
.LBB85_2:
	add	x0, sp, #96
	add	x1, sp, #64
	add	x2, x24, #8
	bl	_RNvNtCsemcRClSg8DH_9native_vm6keccak9hash_pair
	cmp	x19, #256
	b.hs	.LBB85_12
.LBB85_3:
	ldr	x8, [sp, #16]
	mov	w9, #40
	madd	x8, x19, x9, x8
	ldp	x10, x11, [sp, #96]
	lsr	x9, x21, #1
	add	x19, x19, #1
	stp	x9, x10, [x8]
	ldp	x9, x10, [sp, #112]
	stp	x11, x9, [x8, #16]
	str	x10, [x8, #32]
.LBB85_4:
	cmp	x23, x28
	b.eq	.LBB85_14
.LBB85_5:
	mov	x24, x23
	mov	x26, x20
	add	x23, x23, #40
	add	x20, x20, #1
	mov	x9, x25
	mov	x8, x29
.LBB85_6:
	cbz	x9, .LBB85_9
	ldr	x10, [x8, #40]!
	ldr	x21, [x24]
	sub	x9, x9, #40
	eor	x10, x21, x10
	cmp	x10, #1
	b.ne	.LBB85_6
	mov	w11, #40
	ldp	x9, x10, [x8, #8]
	madd	x11, x26, x11, x22
	ldp	x12, x8, [x8, #24]
	stp	x9, x10, [sp, #64]
	stp	x12, x8, [sp, #80]
	stp	x21, x9, [x11]
	stp	x10, x12, [x11, #16]
	str	x8, [x11, #32]
	tbnz	w21, #0, .LBB85_4
	b	.LBB85_11
.LBB85_9:
	ldr	x1, [sp, #8]
	add	x0, sp, #24
	bl	_RNvMNtCsemcRClSg8DH_9native_vm4wireNtB2_6Reader6digest
	ldr	w8, [sp, #24]
	tbz	w8, #0, .LBB85_12
	mov	w10, #40
	ldp	x8, x9, [x27, #8]
	madd	x10, x26, x10, x22
	ldp	x11, x12, [x27, #24]
	ldr	x21, [x24]
	stp	x8, x9, [sp, #64]
	stp	x11, x12, [sp, #80]
	stp	x21, x8, [x10]
	stp	x9, x11, [x10, #16]
	str	x12, [x10, #32]
	tbnz	w21, #0, .LBB85_2
.LBB85_11:
	add	x0, sp, #96
	add	x1, x24, #8
	add	x2, sp, #64
	bl	_RNvNtCsemcRClSg8DH_9native_vm6keccak9hash_pair
	cmp	x19, #256
	b.lo	.LBB85_3
.LBB85_12:
	mov	x0, xzr
	b	.LBB85_15
.LBB85_13:
	mov	x19, xzr
.LBB85_14:
	mov	w0, #1
.LBB85_15:
	mov	x1, x19
	ldp	x20, x19, [sp, #208]
	ldp	x22, x21, [sp, #192]
	ldp	x24, x23, [sp, #176]
	ldp	x26, x25, [sp, #160]
	ldp	x28, x27, [sp, #144]
	ldp	x29, x30, [sp, #128]
	add	sp, sp, #224
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w25
	.cfi_restore w26
	.cfi_restore w27
	.cfi_restore w28
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end85:
	.size	_RNvNtCsemcRClSg8DH_9native_vm4wire11climb_level, .Lfunc_end85-_RNvNtCsemcRClSg8DH_9native_vm4wire11climb_level
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm4wire14write_openings,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm4wire14write_openings,@function
_RNvNtCsemcRClSg8DH_9native_vm4wire14write_openings:
.Lfunc_begin86:
	.cfi_startproc
	sub	sp, sp, #176
	.cfi_def_cfa_offset 176
	stp	x29, x30, [sp, #80]
	stp	x28, x27, [sp, #96]
	stp	x26, x25, [sp, #112]
	stp	x24, x23, [sp, #128]
	stp	x22, x21, [sp, #144]
	stp	x20, x19, [sp, #160]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w24, -48
	.cfi_offset w25, -56
	.cfi_offset w26, -64
	.cfi_offset w27, -72
	.cfi_offset w28, -80
	.cfi_offset w30, -88
	.cfi_offset w29, -96
	ldr	x10, [sp, #184]
	mov	x21, x5
	add	x5, x0, x1, lsl #3
	mov	x19, x2
	mov	x2, x0
	stp	x1, x6, [x10]
	lsl	x1, x3, #3
	add	x3, x10, #24
	str	x21, [x10, #16]
	cbz	x6, .LBB86_20
	add	x8, x6, x6, lsl #2
	ldr	x29, [sp, #176]
	mov	x23, x7
	mov	x9, xzr
	and	x15, x21, #0x7c
	add	x16, x10, #56
	lsl	x26, x8, #11
	add	x17, x10, #32
	add	x20, x10, #568
	mov	w11, #1544
	mov	w22, #10240
.LBB86_2:
	mov	x8, x9
	mul	x9, x9, x11
	mov	x10, xzr
	ldr	x25, [x2], #8
	add	x13, x8, #1
	mov	x8, x4
	mov	x11, x1
	str	x25, [x3, x9]
	add	x9, x4, #16
.LBB86_3:
	ldr	x12, [x19, x10, lsl #3]
	cmp	x12, x25
	b.eq	.LBB86_5
	subs	x11, x11, #8
	add	x10, x10, #1
	add	x9, x9, #512
	add	x8, x8, #512
	b.ne	.LBB86_3
	b	.LBB86_38
.LBB86_5:
	stp	x13, x4, [sp, #32]
	stp	x3, x1, [sp, #48]
	stp	x5, x2, [sp, #64]
	cbz	x21, .LBB86_12
	cmp	x21, #4
	mov	x10, x16
	and	x11, x21, #0x7c
	b.hs	.LBB86_8
	mov	x10, xzr
	b	.LBB86_10
.LBB86_8:
	ldp	x12, x13, [x9, #-16]
	subs	x11, x11, #4
	stp	x12, x13, [x10, #-24]
	ldp	x12, x14, [x9], #32
	stp	x12, x14, [x10, #-8]
	add	x10, x10, #32
	b.ne	.LBB86_8
	cmp	x21, x15
	and	x10, x21, #0x7c
	b.eq	.LBB86_12
.LBB86_10:
	lsl	x9, x10, #3
	sub	x10, x21, x10
	add	x8, x8, x9
	add	x9, x17, x9
.LBB86_11:
	ldr	x11, [x8], #8
	subs	x10, x10, #1
	str	x11, [x9], #8
	b.ne	.LBB86_11
.LBB86_12:
	mov	x28, xzr
	mov	x27, xzr
	stp	x17, x16, [sp, #16]
	str	x20, [sp, #8]
	b	.LBB86_15
.LBB86_13:
	mov	x9, x8
	mov	x10, x8
	mov	x11, x8
.LBB86_14:
	add	x28, x28, x22
	stp	x11, x10, [x20, #-24]
	add	x27, x27, #1
	cmp	x26, x28
	stp	x9, x8, [x20, #-8]
	add	x20, x20, #32
	b.eq	.LBB86_19
.LBB86_15:
	ldr	x24, [x29, x27, lsl #3]
	cmp	x24, #256
	b.hi	.LBB86_38
	lsr	x2, x25, x27
	add	x0, x23, x28
	mov	x1, x24
	bl	_RNvNtCsemcRClSg8DH_9native_vm4wire4find
	cmp	x0, #1
	mov	x8, xzr
	b.ne	.LBB86_13
	cmp	x1, x24
	mov	x9, x8
	mov	x10, x8
	mov	x11, x8
	b.hs	.LBB86_14
	mov	w8, #40
	madd	x8, x1, x8, x23
	add	x8, x8, x28
	ldp	x11, x10, [x8, #8]
	ldp	x9, x8, [x8, #24]
	b	.LBB86_14
.LBB86_19:
	ldp	x17, x16, [sp, #16]
	mov	w0, #1
	ldp	x5, x2, [sp, #64]
	and	x15, x21, #0x7c
	ldr	x20, [sp, #8]
	ldp	x3, x1, [sp, #48]
	ldp	x9, x4, [sp, #32]
	add	x16, x16, #1544
	cmp	x2, x5
	add	x17, x17, #1544
	add	x20, x20, #1544
	mov	w11, #1544
	b.ne	.LBB86_2
	b	.LBB86_39
.LBB86_20:
	cbz	x21, .LBB86_33
	mov	x11, xzr
	and	x8, x21, #0x7c
	add	x9, x10, #56
	add	x10, x10, #32
	mov	w12, #1544
.LBB86_22:
	mul	x13, x11, x12
	ldr	x16, [x2], #8
	mov	x15, xzr
	add	x11, x11, #1
	add	x14, x4, #16
	mov	x17, x1
	str	x16, [x3, x13]
	mov	x13, x4
.LBB86_23:
	ldr	x18, [x19, x15, lsl #3]
	cmp	x18, x16
	b.eq	.LBB86_25
	subs	x17, x17, #8
	add	x15, x15, #1
	add	x14, x14, #512
	add	x13, x13, #512
	b.ne	.LBB86_23
	b	.LBB86_38
.LBB86_25:
	cmp	x21, #4
	b.hs	.LBB86_27
	mov	x15, xzr
	b	.LBB86_30
.LBB86_27:
	mov	x15, x9
	and	x16, x21, #0x7c
.LBB86_28:
	ldp	x17, x18, [x14, #-16]
	subs	x16, x16, #4
	stp	x17, x18, [x15, #-24]
	ldp	x17, x0, [x14], #32
	stp	x17, x0, [x15, #-8]
	add	x15, x15, #32
	b.ne	.LBB86_28
	cmp	x21, x8
	and	x15, x21, #0x7c
	b.eq	.LBB86_32
.LBB86_30:
	lsl	x14, x15, #3
	sub	x15, x21, x15
	add	x13, x13, x14
	add	x14, x10, x14
.LBB86_31:
	ldr	x16, [x13], #8
	subs	x15, x15, #1
	str	x16, [x14], #8
	b.ne	.LBB86_31
.LBB86_32:
	cmp	x2, x5
	add	x9, x9, #1544
	add	x10, x10, #1544
	mov	w0, #1
	b.ne	.LBB86_22
	b	.LBB86_39
.LBB86_33:
	mov	x9, xzr
	mov	w8, #1544
	mov	w0, #1
.LBB86_34:
	mul	x12, x9, x8
	ldr	x11, [x2], #8
	mov	x10, xzr
	add	x9, x9, #1
	str	x11, [x3, x12]
	mov	x12, x1
.LBB86_35:
	ldr	x13, [x19, x10, lsl #3]
	cmp	x13, x11
	b.eq	.LBB86_37
	subs	x12, x12, #8
	add	x10, x10, #1
	b.ne	.LBB86_35
	b	.LBB86_38
.LBB86_37:
	cmp	x2, x5
	b.ne	.LBB86_34
	b	.LBB86_39
.LBB86_38:
	mov	w0, wzr
.LBB86_39:
	ldp	x20, x19, [sp, #160]
	ldp	x22, x21, [sp, #144]
	ldp	x24, x23, [sp, #128]
	ldp	x26, x25, [sp, #112]
	ldp	x28, x27, [sp, #96]
	ldp	x29, x30, [sp, #80]
	add	sp, sp, #176
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w25
	.cfi_restore w26
	.cfi_restore w27
	.cfi_restore w28
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end86:
	.size	_RNvNtCsemcRClSg8DH_9native_vm4wire14write_openings, .Lfunc_end86-_RNvNtCsemcRClSg8DH_9native_vm4wire14write_openings
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm4wire4find,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm4wire4find,@function
_RNvNtCsemcRClSg8DH_9native_vm4wire4find:
.Lfunc_begin87:
	.cfi_startproc
	cbz	x1, .LBB87_4
	mov	x9, x1
	mov	x8, x0
	mov	x1, xzr
	add	x9, x9, x9, lsl #2
	mov	w0, #1
	lsl	x9, x9, #3
.LBB87_2:
	ldr	x10, [x8], #40
	cmp	x10, x2
	b.eq	.LBB87_5
	subs	x9, x9, #40
	add	x1, x1, #1
	b.ne	.LBB87_2
.LBB87_4:
	mov	x0, xzr
.LBB87_5:
	ret
.Lfunc_end87:
	.size	_RNvNtCsemcRClSg8DH_9native_vm4wire4find, .Lfunc_end87-_RNvNtCsemcRClSg8DH_9native_vm4wire4find
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm4wire5ins_d,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm4wire5ins_d,@function
_RNvNtCsemcRClSg8DH_9native_vm4wire5ins_d:
.Lfunc_begin88:
	.cfi_startproc
	mov	x8, xzr
	cbz	x1, .LBB88_6
.LBB88_1:
	and	x9, x8, #0xff
	ldr	x9, [x0, x9, lsl #3]
	cmp	x9, x2
	b.hs	.LBB88_4
	add	x8, x8, #1
	cmp	x1, x8
	b.ne	.LBB88_1
	and	x8, x1, #0xff
	str	x2, [x0, x8, lsl #3]
	add	x0, x1, #1
	ret
.LBB88_4:
	b.ne	.LBB88_6
	mov	x0, x1
	ret
.LBB88_6:
	cmp	x1, #255
	mov	w9, #255
	csel	x9, x1, x9, lo
	cmp	x9, x8
	b.ls	.LBB88_8
.LBB88_7:
	mov	x10, x9
	sub	x9, x9, #1
	and	x11, x9, #0xff
	and	x10, x10, #0xff
	cmp	x9, x8
	ldr	x11, [x0, x11, lsl #3]
	str	x11, [x0, x10, lsl #3]
	b.hi	.LBB88_7
.LBB88_8:
	and	x8, x8, #0xff
	str	x2, [x0, x8, lsl #3]
	add	x0, x1, #1
	ret
.Lfunc_end88:
	.size	_RNvNtCsemcRClSg8DH_9native_vm4wire5ins_d, .Lfunc_end88-_RNvNtCsemcRClSg8DH_9native_vm4wire5ins_d
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm4wire6decode,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm4wire6decode,@function
_RNvNtCsemcRClSg8DH_9native_vm4wire6decode:
.Lfunc_begin89:
	.cfi_startproc
	sub	sp, sp, #96
	.cfi_def_cfa_offset 96
	stp	xzr, x30, [sp, #24]
	stp	x24, x23, [sp, #48]
	stp	x22, x21, [sp, #64]
	stp	x20, x19, [sp, #80]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w24, -48
	.cfi_offset w30, -64
	.cfi_remember_state
	mov	x20, x1
	stp	x0, x1, [sp, #8]
	add	x0, sp, #8
	mov	w1, #4
	mov	x19, x4
	mov	x22, x3
	mov	x21, x2
	bl	_RNvMNtCsemcRClSg8DH_9native_vm4wireNtB2_6Reader2le
	cmp	x0, #1
	b.ne	.LBB89_9
	lsl	x2, x1, #1
	cmp	x2, x22
	b.hs	.LBB89_9
	mov	x23, x1
	add	x0, sp, #8
	add	x1, x21, #8
	bl	_RNvMNtCsemcRClSg8DH_9native_vm4wireNtB2_6Reader5words
	cbz	w0, .LBB89_10
	add	x0, sp, #8
	mov	w1, #4
	str	x23, [x21]
	bl	_RNvMNtCsemcRClSg8DH_9native_vm4wireNtB2_6Reader2le
	cmp	x1, #9
	cset	w8, lo
	tst	w0, w8
	b.eq	.LBB89_9
	lsr	x8, x20, #3
	orr	x8, x8, #0x1
	cmp	x8, x22
	b.hs	.LBB89_9
	mov	x10, #6553
	mvn	x9, x8
	add	x8, x21, x8, lsl #3
	movk	x10, #36924, lsl #16
	add	x9, x22, x9
	mov	w24, #2072
	movk	x10, #19819, lsl #32
	str	x1, [x8]
	sub	x8, x8, #96, lsl #12
	movk	x10, #21387, lsl #48
	mov	x23, x1
	sub	x21, x8, #2064
	umulh	x10, x9, x10
	movk	w24, #6, lsl #16
	sub	x9, x9, x10
	add	x9, x10, x9, lsr #1
	lsr	x9, x9, #15
	add	x22, x9, #1
.LBB89_6:
	cbz	x23, .LBB89_11
	sub	x22, x22, #1
	cbz	x22, .LBB89_9
	add	x21, x21, x24
	add	x0, sp, #8
	mov	x2, x19
	mov	x1, x21
	sub	x23, x23, #1
	bl	_RNvNtCsemcRClSg8DH_9native_vm4wire7phase_m
	mov	w8, w0
	mov	w0, wzr
	tbnz	w8, #0, .LBB89_6
	b	.LBB89_10
.LBB89_9:
	mov	w0, wzr
.LBB89_10:
	ldp	x20, x19, [sp, #80]
	ldr	x30, [sp, #32]
	ldp	x22, x21, [sp, #64]
	ldp	x24, x23, [sp, #48]
	add	sp, sp, #96
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w30
	ret
.LBB89_11:
	.cfi_restore_state
	ldp	x8, x30, [sp, #24]
	cmp	x8, x20
	cset	w0, eq
	ldp	x20, x19, [sp, #80]
	ldp	x22, x21, [sp, #64]
	ldp	x24, x23, [sp, #48]
	add	sp, sp, #96
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w30
	ret
.Lfunc_end89:
	.size	_RNvNtCsemcRClSg8DH_9native_vm4wire6decode, .Lfunc_end89-_RNvNtCsemcRClSg8DH_9native_vm4wire6decode
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm4wire7phase_m,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm4wire7phase_m,@function
_RNvNtCsemcRClSg8DH_9native_vm4wire7phase_m:
.Lfunc_begin90:
	.cfi_startproc
	sub	sp, sp, #192
	.cfi_def_cfa_offset 192
	stp	x29, x30, [sp, #96]
	stp	x28, x27, [sp, #112]
	stp	x26, x25, [sp, #128]
	stp	x24, x23, [sp, #144]
	stp	x22, x21, [sp, #160]
	stp	x20, x19, [sp, #176]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w24, -48
	.cfi_offset w25, -56
	.cfi_offset w26, -64
	.cfi_offset w27, -72
	.cfi_offset w28, -80
	.cfi_offset w30, -88
	.cfi_offset w29, -96
	.cfi_remember_state
	mov	x20, x1
	mov	w1, #4
	mov	x19, x2
	mov	x22, x0
	bl	_RNvMNtCsemcRClSg8DH_9native_vm4wireNtB2_6Reader2le
	cmp	x1, #257
	cset	w8, lo
	tst	w0, w8
	b.eq	.LBB90_12
	lsl	x27, x1, #3
	mov	x21, x1
	cbz	x1, .LBB90_5
	mov	x23, x27
	mov	x24, x19
.LBB90_3:
	mov	x0, x22
	mov	w1, #4
	bl	_RNvMNtCsemcRClSg8DH_9native_vm4wireNtB2_6Reader2le
	tbz	w0, #0, .LBB90_12
	subs	x23, x23, #8
	str	x1, [x24], #8
	b.ne	.LBB90_3
.LBB90_5:
	mov	x0, x22
	mov	w1, #4
	bl	_RNvMNtCsemcRClSg8DH_9native_vm4wireNtB2_6Reader2le
	tbz	w0, #0, .LBB90_12
	mov	x24, x1
	mov	x0, x22
	mov	w1, #4
	bl	_RNvMNtCsemcRClSg8DH_9native_vm4wireNtB2_6Reader2le
	cmp	x0, #1
	str	x1, [sp, #56]
	b.ne	.LBB90_12
	mov	x0, x22
	mov	w1, #4
	bl	_RNvMNtCsemcRClSg8DH_9native_vm4wireNtB2_6Reader2le
	cbz	x21, .LBB90_12
	tbz	w0, #0, .LBB90_12
	mov	x28, x1
	mov	x23, xzr
	mov	x26, xzr
	add	x8, x19, #2048
	str	x8, [sp, #48]
.LBB90_10:
	ldr	x2, [x19, x23]
	add	x0, x19, #2048
	mov	x1, x26
	bl	_RNvNtCsemcRClSg8DH_9native_vm4wire5ins_d
	add	x23, x23, #8
	mov	x26, x0
	cmp	x27, x23
	b.ne	.LBB90_10
	sub	x8, x26, #257
	cmn	x8, #256
	b.hs	.LBB90_14
.LBB90_12:
	mov	w0, wzr
.LBB90_13:
	ldp	x20, x19, [sp, #176]
	ldp	x22, x21, [sp, #160]
	ldp	x24, x23, [sp, #144]
	ldp	x26, x25, [sp, #128]
	ldp	x28, x27, [sp, #112]
	ldp	x29, x30, [sp, #96]
	add	sp, sp, #192
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w25
	.cfi_restore w26
	.cfi_restore w27
	.cfi_restore w28
	.cfi_restore w30
	.cfi_restore w29
	ret
.LBB90_14:
	.cfi_restore_state
	cmp	x24, #32
	b.hi	.LBB90_12
	ldr	x8, [sp, #56]
	cmp	x8, #64
	b.hi	.LBB90_12
	ldr	x8, [sp, #56]
	cmp	x28, x8
	b.hi	.LBB90_12
	add	x8, x19, #2048
	add	x8, x8, x26, lsl #3
	ldur	x8, [x8, #-8]
	lsr	x8, x8, x24
	cbnz	x8, .LBB90_12
	add	x8, x19, #86, lsl #12
	ldr	x2, [sp, #56]
	mov	x0, x22
	add	x4, x8, #256
	mov	x1, x26
	mov	x3, x28
	str	x4, [sp, #40]
	bl	_RNvNtCsemcRClSg8DH_9native_vm4wire7rd_rows
	cmp	x28, #0
	and	w8, w0, #0xff
	and	w9, w8, #0xff
	cset	w10, ne
	cmp	w9, #2
	and	w8, w10, w8
	csinc	w8, w8, wzr, ne
	tbnz	w8, #0, .LBB90_12
	ldr	x5, [sp, #56]
	mov	w8, #4104
	ldr	x29, [sp, #40]
	add	x25, x19, x8
	mov	x27, x26
	add	x23, x19, #2048
	lsl	x28, x5, #3
	str	x24, [sp, #32]
.LBB90_20:
	ldr	x24, [x23], #8
	add	x0, sp, #64
	mov	x1, x5
	mov	x2, x28
	mov	x3, x29
	mov	x4, x5
	bl	_RINvNtCsemcRClSg8DH_9native_vm6keccak15keccak256_wordsNCNvB2_10hash_words0EB4_
	ldp	x5, x8, [sp, #56]
	subs	x27, x27, #1
	ldr	x10, [sp, #88]
	add	x29, x29, #512
	stp	x24, x8, [x25, #-8]
	ldp	x9, x8, [sp, #72]
	str	x10, [x25, #24]
	stp	x9, x8, [x25, #8]
	add	x25, x25, #40
	b.ne	.LBB90_20
	mov	w8, #24832
	ldr	x24, [sp, #32]
	add	x29, x19, x8
	add	x8, x19, #6, lsl #12
	cbz	x24, .LBB90_27
	mov	w8, #14336
	mov	x25, xzr
	add	x23, x19, #6, lsl #12
	add	x27, x19, x8
	mov	x28, x26
	str	x29, [sp, #24]
.LBB90_23:
	cmp	x28, #257
	b.hs	.LBB90_12
	tst	x25, #0x1
	add	x8, x19, #1, lsl #12
	mov	x0, x22
	csel	x1, x8, x27, eq
	csel	x4, x27, x8, eq
	mov	x2, x28
	mov	x3, x29
	bl	_RNvNtCsemcRClSg8DH_9native_vm4wire11climb_level
	cmp	x0, #1
	b.ne	.LBB90_12
	add	x25, x25, #1
	mov	w8, #10240
	str	x28, [x23], #8
	cmp	x24, x25
	add	x29, x29, x8
	mov	x28, x1
	b.ne	.LBB90_23
	ldr	x5, [sp, #56]
	ldr	x29, [sp, #24]
	add	x8, x19, #6, lsl #12
.LBB90_27:
	ldp	x4, x2, [sp, #40]
	mov	x0, x19
	mov	x1, x21
	mov	x3, x26
	mov	x6, x24
	mov	x7, x29
	stp	x8, x20, [sp]
	bl	_RNvNtCsemcRClSg8DH_9native_vm4wire14write_openings
	b	.LBB90_13
.Lfunc_end90:
	.size	_RNvNtCsemcRClSg8DH_9native_vm4wire7phase_m, .Lfunc_end90-_RNvNtCsemcRClSg8DH_9native_vm4wire7phase_m
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm4wire7rd_rows,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm4wire7rd_rows,@function
_RNvNtCsemcRClSg8DH_9native_vm4wire7rd_rows:
.Lfunc_begin91:
	.cfi_startproc
	sub	sp, sp, #112
	.cfi_def_cfa_offset 112
	stp	x29, x30, [sp, #16]
	stp	x28, x27, [sp, #32]
	stp	x26, x25, [sp, #48]
	stp	x24, x23, [sp, #64]
	stp	x22, x21, [sp, #80]
	stp	x20, x19, [sp, #96]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w24, -48
	.cfi_offset w25, -56
	.cfi_offset w26, -64
	.cfi_offset w27, -72
	.cfi_offset w28, -80
	.cfi_offset w30, -88
	.cfi_offset w29, -96
	.cfi_remember_state
	subs	x8, x2, x3
	b.hs	.LBB91_3
.LBB91_1:
	mov	w23, #2
.LBB91_2:
	mov	w0, w23
	ldp	x20, x19, [sp, #96]
	ldp	x22, x21, [sp, #80]
	ldp	x24, x23, [sp, #64]
	ldp	x26, x25, [sp, #48]
	ldp	x28, x27, [sp, #32]
	ldp	x29, x30, [sp, #16]
	add	sp, sp, #112
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w25
	.cfi_restore w26
	.cfi_restore w27
	.cfi_restore w28
	.cfi_restore w30
	.cfi_restore w29
	ret
.LBB91_3:
	.cfi_restore_state
	add	x24, x4, x1, lsl #9
	mov	x19, x4
	mov	x22, x3
	mov	x20, x2
	mov	x21, x0
	cbz	x3, .LBB91_13
	sub	x9, x22, x20
	mov	x10, #2305843009213693951
	lsl	x28, x8, #3
	bic	x25, x10, x9
	add	x27, x19, #16
	mov	w23, #1
	add	x9, x25, #1
	and	x9, x9, #0x3ffffffffffffffc
	lsl	x29, x9, #3
	str	x9, [sp, #8]
.LBB91_5:
	cmp	x20, x22
	add	x26, x19, x28
	b.eq	.LBB91_11
	cmp	x25, #3
	mov	x8, x19
	b.lo	.LBB91_10
	add	x10, x25, #1
	add	x8, x19, x29
	mov	x9, x27
	and	x10, x10, #0x3ffffffffffffffc
.LBB91_8:
	subs	x10, x10, #4
	stp	xzr, xzr, [x9, #-16]
	stp	xzr, xzr, [x9], #32
	b.ne	.LBB91_8
	ldr	x10, [sp, #8]
	add	x9, x25, #1
	cmp	x9, x10
	b.eq	.LBB91_11
.LBB91_10:
	str	xzr, [x8], #8
	cmp	x8, x26
	b.ne	.LBB91_10
.LBB91_11:
	add	x1, x19, x28
	mov	x0, x21
	mov	x2, x22
	bl	_RNvMNtCsemcRClSg8DH_9native_vm4wireNtB2_6Reader5words
	cbz	w0, .LBB91_1
	ldr	x8, [x26]
	add	x19, x19, #512
	add	x27, x27, #512
	cmp	x8, #0
	csel	w23, w23, wzr, eq
	cmp	x19, x24
	b.ne	.LBB91_5
	b	.LBB91_2
.LBB91_13:
	lsl	x22, x20, #3
	add	x28, x19, #16
	sub	x23, x22, #8
	lsr	x8, x23, #3
	add	x25, x8, #1
	and	x26, x25, #0x3ffffffffffffffc
	lsl	x27, x26, #3
.LBB91_14:
	add	x8, x19, x22
	cbz	x20, .LBB91_20
	cmp	x23, #24
	mov	x9, x19
	b.lo	.LBB91_19
	add	x9, x19, x27
	mov	x10, x28
	and	x11, x25, #0x3ffffffffffffffc
.LBB91_17:
	subs	x11, x11, #4
	stp	xzr, xzr, [x10, #-16]
	stp	xzr, xzr, [x10], #32
	b.ne	.LBB91_17
	cmp	x25, x26
	b.eq	.LBB91_20
.LBB91_19:
	str	xzr, [x9], #8
	cmp	x9, x8
	b.ne	.LBB91_19
.LBB91_20:
	add	x1, x19, x22
	mov	x0, x21
	mov	x2, xzr
	bl	_RNvMNtCsemcRClSg8DH_9native_vm4wireNtB2_6Reader5words
	cbz	w0, .LBB91_1
	add	x19, x19, #512
	add	x28, x28, #512
	cmp	x19, x24
	b.ne	.LBB91_14
	mov	w23, #1
	b	.LBB91_2
.Lfunc_end91:
	.size	_RNvNtCsemcRClSg8DH_9native_vm4wire7rd_rows, .Lfunc_end91-_RNvNtCsemcRClSg8DH_9native_vm4wire7rd_rows
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm5field10bit_length,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm5field10bit_length,@function
_RNvNtCsemcRClSg8DH_9native_vm5field10bit_length:
.Lfunc_begin92:
	.cfi_startproc
	lsr	x8, x0, #32
	mov	w10, #32
	mov	w11, #16
	mov	w12, #8
	cmp	x8, #0
	csel	x8, x0, x8, eq
	csel	x10, xzr, x10, eq
	lsr	x9, x8, #16
	cmp	x9, #0
	csel	x8, x8, x9, eq
	csel	x11, xzr, x11, eq
	lsr	x9, x8, #8
	cmp	x9, #0
	csel	x8, x8, x9, eq
	csel	x12, xzr, x12, eq
	lsr	x9, x8, #4
	cmp	x9, #0
	csel	x8, x8, x9, eq
	orr	x9, x11, x10
	mov	w11, #4
	lsr	x10, x8, #2
	orr	x9, x12, x9
	csel	x11, xzr, x11, eq
	mov	w12, #2
	orr	x9, x11, x9
	cmp	x10, #0
	csel	x11, xzr, x12, eq
	csel	x8, x8, x10, eq
	orr	x9, x11, x9
	cmp	x8, #1
	cinc	x9, x9, hi
	cmp	x8, #0
	cinc	x0, x9, ne
	ret
.Lfunc_end92:
	.size	_RNvNtCsemcRClSg8DH_9native_vm5field10bit_length, .Lfunc_end92-_RNvNtCsemcRClSg8DH_9native_vm5field10bit_length
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm5field14index_mle_from,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm5field14index_mle_from,@function
_RNvNtCsemcRClSg8DH_9native_vm5field14index_mle_from:
.Lfunc_begin93:
	.cfi_startproc
	str	x30, [sp, #-64]!
	.cfi_def_cfa_offset 64
	stp	x24, x23, [sp, #16]
	stp	x22, x21, [sp, #32]
	stp	x20, x19, [sp, #48]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w24, -48
	.cfi_offset w30, -64
	cbz	x1, .LBB93_3
	add	x24, x0, x1, lsl #4
	mov	x20, x0
	mov	x22, xzr
	mov	x19, xzr
	mov	w21, #1
	mov	w23, #2
.LBB93_2:
	ldp	x0, x1, [x20], #16
	eor	x2, x23, #0x1
	mov	x3, x22
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	mov	x3, x1
	eor	x2, x0, #0x1
	mov	x0, x21
	mov	x1, x19
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	mov	x21, x0
	mov	x19, x1
	mov	x0, x23
	mov	x1, x22
	mov	x2, x23
	mov	x3, x22
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	mov	x23, x0
	cmp	x20, x24
	mov	x22, x1
	b.ne	.LBB93_2
	b	.LBB93_4
.LBB93_3:
	mov	x19, xzr
	mov	w21, #1
.LBB93_4:
	mov	x0, x21
	mov	x1, x19
	ldp	x20, x19, [sp, #48]
	ldp	x22, x21, [sp, #32]
	ldp	x24, x23, [sp, #16]
	ldr	x30, [sp], #64
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w30
	ret
.Lfunc_end93:
	.size	_RNvNtCsemcRClSg8DH_9native_vm5field14index_mle_from, .Lfunc_end93-_RNvNtCsemcRClSg8DH_9native_vm5field14index_mle_from
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm5field14padding_weight,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm5field14padding_weight,@function
_RNvNtCsemcRClSg8DH_9native_vm5field14padding_weight:
.Lfunc_begin94:
	.cfi_startproc
	sub	sp, sp, #112
	.cfi_def_cfa_offset 112
	stp	x29, x30, [sp, #16]
	stp	x28, x27, [sp, #32]
	stp	x26, x25, [sp, #48]
	stp	x24, x23, [sp, #64]
	stp	x22, x21, [sp, #80]
	stp	x20, x19, [sp, #96]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w24, -48
	.cfi_offset w25, -56
	.cfi_offset w26, -64
	.cfi_offset w27, -72
	.cfi_offset w28, -80
	.cfi_offset w30, -88
	.cfi_offset w29, -96
	mov	x19, x2
	str	x1, [sp, #8]
	cbz	x1, .LBB94_3
	add	x29, x0, x1, lsl #4
	mov	x22, x0
	mov	x20, xzr
	mov	x21, xzr
	mov	w23, #1
.LBB94_2:
	lsr	x8, x19, x20
	mov	x1, xzr
	add	x20, x20, #1
	ldp	x24, x25, [x22], #16
	mvn	w8, w8
	and	x26, x8, #0x1
	mov	x0, x26
	mov	x2, x24
	mov	x3, x25
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	mov	x27, x0
	mov	x28, x1
	eor	x0, x24, x26
	mov	x1, x25
	mov	x2, x23
	mov	x3, x21
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	cmp	x22, x29
	eor	x23, x0, x27
	eor	x21, x1, x28
	b.ne	.LBB94_2
	b	.LBB94_4
.LBB94_3:
	mov	x21, xzr
	mov	w23, #1
.LBB94_4:
	ldr	x8, [sp, #8]
	mov	x2, x23
	mov	x3, x21
	ldp	x22, x21, [sp, #80]
	mov	x1, xzr
	lsr	x8, x19, x8
	ldp	x20, x19, [sp, #96]
	ldp	x24, x23, [sp, #64]
	ldp	x26, x25, [sp, #48]
	mvn	w8, w8
	ldp	x28, x27, [sp, #32]
	and	x0, x8, #0x1
	ldp	x29, x30, [sp, #16]
	add	sp, sp, #112
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w25
	.cfi_restore w26
	.cfi_restore w27
	.cfi_restore w28
	.cfi_restore w30
	.cfi_restore w29
	b	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
.Lfunc_end94:
	.size	_RNvNtCsemcRClSg8DH_9native_vm5field14padding_weight, .Lfunc_end94-_RNvNtCsemcRClSg8DH_9native_vm5field14padding_weight
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm5field14selector_point,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm5field14selector_point,@function
_RNvNtCsemcRClSg8DH_9native_vm5field14selector_point:
.Lfunc_begin95:
	.cfi_startproc
	cbz	x2, .LBB95_8
	lsl	x10, x2, #4
	sub	x8, x10, #16
	cmp	x8, #48
	b.hs	.LBB95_3
	mov	x9, xzr
	mov	x8, x1
	b	.LBB95_6
.LBB95_3:
	lsr	x8, x8, #4
	mov	x11, xzr
	add	x13, x1, #32
	add	x12, x8, #1
	and	x9, x12, #0x1ffffffffffffffc
	add	x8, x1, x9, lsl #4
.LBB95_4:
	lsr	x14, x0, x11
	add	x16, x11, #2
	cmp	x11, #63
	lsr	x16, x0, x16
	add	x15, x11, #1
	add	x17, x11, #3
	and	x14, x14, #0x1
	lsr	x15, x0, x15
	add	x11, x11, #4
	csel	x14, xzr, x14, hi
	stp	x14, xzr, [x13, #-32]
	and	x14, x16, #0x1
	lsr	x16, x0, x17
	csel	x14, xzr, x14, hi
	and	x15, x15, #0x1
	stp	x14, xzr, [x13]
	and	x14, x16, #0x1
	csel	x15, xzr, x15, hi
	csel	x14, xzr, x14, hi
	stp	x15, xzr, [x13, #-16]
	cmp	x11, x9
	stp	x14, xzr, [x13, #16]
	add	x13, x13, #64
	b.ne	.LBB95_4
	cmp	x12, x9
	b.eq	.LBB95_8
.LBB95_6:
	add	x10, x1, x10
.LBB95_7:
	lsr	x11, x0, x9
	cmp	x9, #63
	add	x9, x9, #1
	and	x11, x11, #0x1
	csel	x11, xzr, x11, hi
	stp	x11, xzr, [x8], #16
	cmp	x8, x10
	b.ne	.LBB95_7
.LBB95_8:
	ret
.Lfunc_end95:
	.size	_RNvNtCsemcRClSg8DH_9native_vm5field14selector_point, .Lfunc_end95-_RNvNtCsemcRClSg8DH_9native_vm5field14selector_point
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm5field3dot,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm5field3dot,@function
_RNvNtCsemcRClSg8DH_9native_vm5field3dot:
.Lfunc_begin96:
	.cfi_startproc
	stp	x30, x23, [sp, #-48]!
	.cfi_def_cfa_offset 48
	stp	x22, x21, [sp, #16]
	stp	x20, x19, [sp, #32]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w30, -48
	.cfi_remember_state
	cmp	x3, x1
	csel	x21, x3, x1, lo
	cbz	x21, .LBB96_4
	mov	x20, xzr
	mov	x19, xzr
	add	x22, x2, #8
	add	x23, x0, #8
.LBB96_2:
	ldp	x0, x1, [x23, #-8]
	ldp	x2, x3, [x22, #-8]
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	subs	x21, x21, #1
	eor	x20, x0, x20
	eor	x19, x1, x19
	add	x22, x22, #16
	add	x23, x23, #16
	b.ne	.LBB96_2
	mov	x0, x20
	mov	x1, x19
	ldp	x20, x19, [sp, #32]
	ldp	x22, x21, [sp, #16]
	ldp	x30, x23, [sp], #48
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w30
	ret
.LBB96_4:
	.cfi_restore_state
	mov	x19, xzr
	mov	x20, xzr
	mov	x0, x20
	mov	x1, x19
	ldp	x20, x19, [sp, #32]
	ldp	x22, x21, [sp, #16]
	ldp	x30, x23, [sp], #48
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w30
	ret
.Lfunc_end96:
	.size	_RNvNtCsemcRClSg8DH_9native_vm5field3dot, .Lfunc_end96-_RNvNtCsemcRClSg8DH_9native_vm5field3dot
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm5field4kinv,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm5field4kinv,@function
_RNvNtCsemcRClSg8DH_9native_vm5field4kinv:
.Lfunc_begin97:
	.cfi_startproc
	stp	x30, x21, [sp, #-32]!
	.cfi_def_cfa_offset 32
	stp	x20, x19, [sp, #16]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w30, -32
	mov	w1, #1
	mov	x19, x0
	bl	_RNvNvNtCsemcRClSg8DH_9native_vm5field4kinv2sq
	mov	x1, x19
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field4kmul
	mov	w1, #1
	bl	_RNvNvNtCsemcRClSg8DH_9native_vm5field4kinv2sq
	mov	x1, x19
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field4kmul
	mov	w1, #3
	mov	x19, x0
	bl	_RNvNvNtCsemcRClSg8DH_9native_vm5field4kinv2sq
	mov	x1, x19
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field4kmul
	mov	w1, #6
	mov	x20, x0
	bl	_RNvNvNtCsemcRClSg8DH_9native_vm5field4kinv2sq
	mov	x1, x20
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field4kmul
	mov	w1, #12
	mov	x20, x0
	bl	_RNvNvNtCsemcRClSg8DH_9native_vm5field4kinv2sq
	mov	x1, x20
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field4kmul
	mov	w1, #24
	mov	x21, x0
	bl	_RNvNvNtCsemcRClSg8DH_9native_vm5field4kinv2sq
	mov	x1, x21
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field4kmul
	mov	w1, #12
	bl	_RNvNvNtCsemcRClSg8DH_9native_vm5field4kinv2sq
	mov	x1, x20
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field4kmul
	mov	w1, #3
	bl	_RNvNvNtCsemcRClSg8DH_9native_vm5field4kinv2sq
	mov	x1, x19
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field4kmul
	ldp	x20, x19, [sp, #16]
	mov	w1, #1
	ldp	x30, x21, [sp], #32
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w30
	b	_RNvNvNtCsemcRClSg8DH_9native_vm5field4kinv2sq
.Lfunc_end97:
	.size	_RNvNtCsemcRClSg8DH_9native_vm5field4kinv, .Lfunc_end97-_RNvNtCsemcRClSg8DH_9native_vm5field4kinv
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm5field4kmul,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm5field4kmul,@function
_RNvNtCsemcRClSg8DH_9native_vm5field4kmul:
.Lfunc_begin98:
	.cfi_startproc
	sub	sp, sp, #112
	.cfi_def_cfa_offset 112
	stp	x29, x30, [sp, #16]
	stp	x28, x27, [sp, #32]
	stp	x26, x25, [sp, #48]
	stp	x24, x23, [sp, #64]
	stp	x22, x21, [sp, #80]
	stp	x20, x19, [sp, #96]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w24, -48
	.cfi_offset w25, -56
	.cfi_offset w26, -64
	.cfi_offset w27, -72
	.cfi_offset w28, -80
	.cfi_offset w30, -88
	.cfi_offset w29, -96
	and	x11, x0, #0x1111111111111111
	and	x10, x1, #0x1111111111111111
	and	x3, x0, #0x2222222222222222
	and	x15, x1, #0x8888888888888888
	mul	x9, x10, x11
	and	x4, x1, #0x4444444444444444
	and	x5, x1, #0x2222222222222222
	rbit	x6, x0
	rbit	x1, x1
	mul	x8, x15, x3
	and	x2, x0, #0x4444444444444444
	and	x13, x0, #0x8888888888888888
	and	x7, x6, #0x1111111111111111
	and	x19, x1, #0x1111111111111111
	and	x21, x6, #0x2222222222222222
	and	x22, x1, #0x8888888888888888
	and	x24, x6, #0x4444444444444444
	and	x25, x1, #0x4444444444444444
	and	x6, x6, #0x8888888888888888
	and	x1, x1, #0x2222222222222222
	mul	x20, x19, x7
	stp	x8, x9, [sp]
	mul	x23, x22, x21
	mul	x26, x25, x24
	mul	x27, x1, x6
	eor	x20, x20, x23
	mul	x28, x1, x7
	mul	x29, x19, x21
	eor	x23, x26, x27
	mul	x30, x22, x24
	eor	x20, x20, x23
	mul	x8, x25, x6
	eor	x26, x28, x29
	ldp	x28, x27, [sp, #32]
	mul	x9, x25, x7
	mul	x25, x25, x21
	eor	x8, x30, x8
	ldp	x29, x30, [sp, #16]
	mul	x21, x1, x21
	eor	x8, x26, x8
	and	x8, x8, #0x2222222222222222
	mul	x1, x1, x24
	mul	x24, x19, x24
	eor	x9, x9, x21
	mul	x7, x22, x7
	mul	x22, x22, x6
	mul	x6, x19, x6
	eor	x7, x7, x25
	ldp	x26, x25, [sp, #48]
	mul	x12, x4, x2
	eor	x21, x24, x22
	ldp	x24, x23, [sp, #64]
	mul	x14, x5, x13
	eor	x9, x9, x21
	eor	x1, x1, x6
	and	x6, x20, #0x1111111111111111
	and	x9, x9, #0x4444444444444444
	mul	x16, x5, x11
	eor	x1, x7, x1
	orr	x8, x6, x8
	and	x1, x1, #0x8888888888888888
	ldp	x22, x21, [sp, #80]
	mul	x17, x10, x3
	orr	x9, x9, x1
	orr	x8, x8, x9
	eor	x12, x12, x14
	mul	x18, x15, x2
	rbit	x8, x8
	mul	x0, x4, x13
	eor	x9, x16, x17
	mul	x19, x4, x11
	mul	x4, x4, x3
	eor	x14, x18, x0
	mul	x3, x5, x3
	eor	x9, x9, x14
	and	x9, x9, #0x2222222222222222
	mul	x5, x5, x2
	mul	x2, x10, x2
	mul	x11, x15, x11
	mul	x15, x15, x13
	mul	x10, x10, x13
	ldp	x1, x13, [sp]
	eor	x11, x11, x4
	eor	x13, x13, x1
	eor	x14, x2, x15
	lsr	x15, x8, #62
	eor	x12, x13, x12
	eor	x13, x19, x3
	eor	x10, x5, x10
	eor	x13, x13, x14
	eor	x10, x11, x10
	and	x11, x12, #0x1111111111111111
	eor	x12, x15, x8, lsr #61
	and	x13, x13, #0x4444444444444444
	and	x10, x10, #0x8888888888888888
	orr	x9, x11, x9
	orr	x10, x13, x10
	eor	x8, x12, x8, lsr #1
	orr	x9, x9, x10
	ldp	x20, x19, [sp, #96]
	eor	x9, x9, x8, lsl #1
	eor	x9, x9, x8, lsl #3
	eor	x9, x9, x8, lsl #4
	eor	x0, x9, x8
	add	sp, sp, #112
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w25
	.cfi_restore w26
	.cfi_restore w27
	.cfi_restore w28
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end98:
	.size	_RNvNtCsemcRClSg8DH_9native_vm5field4kmul, .Lfunc_end98-_RNvNtCsemcRClSg8DH_9native_vm5field4kmul
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm5field4kpow,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm5field4kpow,@function
_RNvNtCsemcRClSg8DH_9native_vm5field4kpow:
.Lfunc_begin99:
	.cfi_startproc
	stp	x30, x21, [sp, #-32]!
	.cfi_def_cfa_offset 32
	stp	x20, x19, [sp, #16]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w30, -32
	cbz	x0, .LBB99_5
	mov	x19, x0
	mov	w20, #1
	mov	w21, #2
	b	.LBB99_3
.LBB99_2:
	mov	x0, x21
	mov	x1, x21
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field4kmul
	lsr	x19, x19, #1
	mov	x21, x0
	cbz	x19, .LBB99_6
.LBB99_3:
	tbz	w19, #0, .LBB99_2
	mov	x0, x20
	mov	x1, x21
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field4kmul
	mov	x20, x0
	b	.LBB99_2
.LBB99_5:
	mov	w20, #1
.LBB99_6:
	mov	x0, x20
	ldp	x20, x19, [sp, #16]
	ldp	x30, x21, [sp], #32
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w30
	ret
.Lfunc_end99:
	.size	_RNvNtCsemcRClSg8DH_9native_vm5field4kpow, .Lfunc_end99-_RNvNtCsemcRClSg8DH_9native_vm5field4kpow
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm5field5sum_e,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm5field5sum_e,@function
_RNvNtCsemcRClSg8DH_9native_vm5field5sum_e:
.Lfunc_begin100:
	.cfi_startproc
	cbz	x1, .LBB100_3
	cmp	x1, #4
	b.hs	.LBB100_4
	mov	x10, xzr
	mov	x8, xzr
	mov	x9, xzr
	b	.LBB100_9
.LBB100_3:
	mov	x8, xzr
	mov	x9, xzr
	mov	x0, x9
	mov	x1, x8
	ret
.LBB100_4:
	ldp	x8, x12, [x0]
	and	x10, x1, #0x1c
	ldp	x9, x14, [x0, #16]
	cmp	x10, #4
	ldp	x11, x15, [x0, #32]
	ldp	x13, x16, [x0, #48]
	b.eq	.LBB100_8
	ldp	x17, x4, [x0, #64]
	cmp	x10, #8
	ldp	x18, x5, [x0, #80]
	eor	x8, x17, x8
	ldp	x2, x17, [x0, #96]
	eor	x9, x18, x9
	ldp	x3, x18, [x0, #112]
	eor	x12, x4, x12
	eor	x14, x5, x14
	eor	x11, x2, x11
	eor	x15, x17, x15
	eor	x13, x3, x13
	eor	x16, x18, x16
	b.eq	.LBB100_8
	ldp	x17, x4, [x0, #128]
	cmp	x10, #12
	ldp	x18, x5, [x0, #144]
	eor	x8, x17, x8
	ldp	x2, x17, [x0, #160]
	eor	x9, x18, x9
	ldp	x3, x18, [x0, #176]
	eor	x12, x4, x12
	eor	x14, x5, x14
	eor	x11, x2, x11
	eor	x15, x17, x15
	eor	x13, x3, x13
	eor	x16, x18, x16
	b.eq	.LBB100_8
	ldp	x17, x4, [x0, #192]
	ldp	x18, x5, [x0, #208]
	eor	x8, x17, x8
	ldp	x2, x17, [x0, #224]
	eor	x9, x18, x9
	ldp	x3, x18, [x0, #240]
	eor	x12, x4, x12
	eor	x14, x5, x14
	eor	x11, x2, x11
	eor	x15, x17, x15
	eor	x13, x3, x13
	eor	x16, x18, x16
.LBB100_8:
	eor	x12, x14, x12
	eor	x14, x16, x15
	eor	x9, x9, x8
	eor	x11, x13, x11
	cmp	x1, x10
	eor	x8, x14, x12
	eor	x9, x11, x9
	b.eq	.LBB100_11
.LBB100_9:
	add	x11, x0, x10, lsl #4
	sub	x10, x1, x10
	add	x11, x11, #8
.LBB100_10:
	ldp	x12, x13, [x11, #-8]
	subs	x10, x10, #1
	add	x11, x11, #16
	eor	x9, x12, x9
	eor	x8, x13, x8
	b.ne	.LBB100_10
.LBB100_11:
	mov	x0, x9
	mov	x1, x8
	ret
.Lfunc_end100:
	.size	_RNvNtCsemcRClSg8DH_9native_vm5field5sum_e, .Lfunc_end100-_RNvNtCsemcRClSg8DH_9native_vm5field5sum_e
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm5field6powers,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm5field6powers,@function
_RNvNtCsemcRClSg8DH_9native_vm5field6powers:
.Lfunc_begin101:
	.cfi_startproc
	cbz	x3, .LBB101_4
	str	x30, [sp, #-48]!
	.cfi_def_cfa_offset 48
	stp	x22, x21, [sp, #16]
	stp	x20, x19, [sp, #32]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w30, -48
	add	x22, x2, x3, lsl #4
	mov	x19, x2
	mov	x20, x1
	mov	x21, x0
	mov	x1, xzr
	mov	w0, #1
.LBB101_2:
	mov	x2, x21
	mov	x3, x20
	stp	x0, x1, [x19], #16
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	cmp	x19, x22
	b.ne	.LBB101_2
	ldp	x20, x19, [sp, #32]
	ldp	x22, x21, [sp, #16]
	ldr	x30, [sp], #48
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w30
.LBB101_4:
	ret
.Lfunc_end101:
	.size	_RNvNtCsemcRClSg8DH_9native_vm5field6powers, .Lfunc_end101-_RNvNtCsemcRClSg8DH_9native_vm5field6powers
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm5field6prod_e,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm5field6prod_e,@function
_RNvNtCsemcRClSg8DH_9native_vm5field6prod_e:
.Lfunc_begin102:
	.cfi_startproc
	str	x30, [sp, #-32]!
	.cfi_def_cfa_offset 32
	stp	x20, x19, [sp, #16]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w30, -32
	.cfi_remember_state
	ldp	x2, x3, [x0]
	mov	x19, x0
	mov	x20, x1
	mov	w0, #1
	mov	x1, xzr
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	ldp	x2, x3, [x19, #16]
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	cmp	x20, #2
	b.eq	.LBB102_2
	ldp	x2, x3, [x19, #32]
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	cmp	x20, #3
	b.ne	.LBB102_3
.LBB102_2:
	ldp	x20, x19, [sp, #16]
	ldr	x30, [sp], #32
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w30
	ret
.LBB102_3:
	.cfi_restore_state
	ldp	x2, x3, [x19, #48]
	ldp	x20, x19, [sp, #16]
	ldr	x30, [sp], #32
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w30
	b	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
.Lfunc_end102:
	.size	_RNvNtCsemcRClSg8DH_9native_vm5field6prod_e, .Lfunc_end102-_RNvNtCsemcRClSg8DH_9native_vm5field6prod_e
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm5field7eq_eval,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm5field7eq_eval,@function
_RNvNtCsemcRClSg8DH_9native_vm5field7eq_eval:
.Lfunc_begin103:
	.cfi_startproc
	stp	x30, x21, [sp, #-32]!
	.cfi_def_cfa_offset 32
	stp	x20, x19, [sp, #16]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w30, -32
	.cfi_remember_state
	cmp	x3, x1
	csel	x19, x3, x1, lo
	cbz	x19, .LBB103_4
	mov	x1, xzr
	add	x20, x2, #8
	add	x21, x0, #8
	mov	w0, #1
.LBB103_2:
	ldp	x8, x11, [x20, #-8]
	ldp	x9, x10, [x21, #-8]
	eor	x8, x9, x8
	eor	x3, x11, x10
	eor	x2, x8, #0x1
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	subs	x19, x19, #1
	add	x20, x20, #16
	add	x21, x21, #16
	b.ne	.LBB103_2
	ldp	x20, x19, [sp, #16]
	ldp	x30, x21, [sp], #32
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w30
	ret
.LBB103_4:
	.cfi_restore_state
	mov	x1, xzr
	mov	w0, #1
	ldp	x20, x19, [sp, #16]
	ldp	x30, x21, [sp], #32
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w30
	ret
.Lfunc_end103:
	.size	_RNvNtCsemcRClSg8DH_9native_vm5field7eq_eval, .Lfunc_end103-_RNvNtCsemcRClSg8DH_9native_vm5field7eq_eval
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm5field9eq_kernel,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm5field9eq_kernel,@function
_RNvNtCsemcRClSg8DH_9native_vm5field9eq_kernel:
.Lfunc_begin104:
	.cfi_startproc
	mov	w8, #1
	lsl	x8, x8, x1
	cmp	x3, x8
	b.hs	.LBB104_2
	mov	x0, xzr
	mov	x1, x8
	ret
.LBB104_2:
	sub	sp, sp, #112
	.cfi_def_cfa_offset 112
	stp	x29, x30, [sp, #16]
	stp	x28, x27, [sp, #32]
	stp	x26, x25, [sp, #48]
	stp	x24, x23, [sp, #64]
	stp	x22, x21, [sp, #80]
	stp	x20, x19, [sp, #96]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w24, -48
	.cfi_offset w25, -56
	.cfi_offset w26, -64
	.cfi_offset w27, -72
	.cfi_offset w28, -80
	.cfi_offset w30, -88
	.cfi_offset w29, -96
	mov	x22, x0
	mov	w0, #1
	stp	x0, xzr, [x2]
	cbz	x1, .LBB104_11
	str	x8, [sp]
	add	x8, x22, x1, lsl #4
	mov	x20, x3
	add	x27, x2, #8
	mov	w29, #1
	str	x8, [sp, #8]
	b	.LBB104_5
.LBB104_4:
	ldr	x8, [sp, #8]
	add	x22, x22, #16
	lsl	x29, x29, #1
	cmp	x22, x8
	b.eq	.LBB104_10
.LBB104_5:
	subs	x8, x20, x29
	b.lo	.LBB104_9
	cmp	x8, x29
	csel	x19, x8, x29, lo
	cmp	x20, x29
	b.eq	.LBB104_4
	lsl	x8, x29, #4
	ldp	x23, x24, [x22]
	mov	x28, x27
	add	x21, x27, x8
.LBB104_8:
	ldp	x25, x26, [x28, #-8]
	mov	x2, x23
	mov	x3, x24
	mov	x0, x25
	mov	x1, x26
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	eor	x8, x25, x0
	eor	x9, x26, x1
	subs	x19, x19, #1
	stp	x0, x1, [x21, #-8]
	add	x21, x21, #16
	stp	x8, x9, [x28, #-8]
	add	x28, x28, #16
	b.ne	.LBB104_8
	b	.LBB104_4
.LBB104_9:
	ldr	x8, [sp]
	mov	x0, xzr
	b	.LBB104_11
.LBB104_10:
	ldr	x8, [sp]
	mov	w0, #1
.LBB104_11:
	ldp	x20, x19, [sp, #96]
	ldp	x22, x21, [sp, #80]
	ldp	x24, x23, [sp, #64]
	ldp	x26, x25, [sp, #48]
	ldp	x28, x27, [sp, #32]
	ldp	x29, x30, [sp, #16]
	add	sp, sp, #112
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w25
	.cfi_restore w26
	.cfi_restore w27
	.cfi_restore w28
	.cfi_restore w30
	.cfi_restore w29
	mov	x1, x8
	ret
.Lfunc_end104:
	.size	_RNvNtCsemcRClSg8DH_9native_vm5field9eq_kernel, .Lfunc_end104-_RNvNtCsemcRClSg8DH_9native_vm5field9eq_kernel
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm5field9poly_eval,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm5field9poly_eval,@function
_RNvNtCsemcRClSg8DH_9native_vm5field9poly_eval:
.Lfunc_begin105:
	.cfi_startproc
	str	x30, [sp, #-64]!
	.cfi_def_cfa_offset 64
	stp	x24, x23, [sp, #16]
	stp	x22, x21, [sp, #32]
	stp	x20, x19, [sp, #48]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w24, -48
	.cfi_offset w30, -64
	mov	x9, x0
	mov	x19, x3
	lsl	x8, x1, #4
	mov	x20, x2
	mov	x0, xzr
	mov	x1, xzr
	add	x9, x8, x9
	neg	x22, x8
	sub	x21, x9, #8
.LBB105_1:
	ldp	x23, x24, [x21, #-8]
	mov	x2, x20
	mov	x3, x19
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	adds	x22, x22, #16
	eor	x0, x0, x23
	eor	x1, x1, x24
	sub	x21, x21, #16
	b.ne	.LBB105_1
	ldp	x20, x19, [sp, #48]
	ldp	x22, x21, [sp, #32]
	ldp	x24, x23, [sp, #16]
	ldr	x30, [sp], #64
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w30
	ret
.Lfunc_end105:
	.size	_RNvNtCsemcRClSg8DH_9native_vm5field9poly_eval, .Lfunc_end105-_RNvNtCsemcRClSg8DH_9native_vm5field9poly_eval
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm5stack10push_claim,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm5stack10push_claim,@function
_RNvNtCsemcRClSg8DH_9native_vm5stack10push_claim:
.Lfunc_begin106:
	.cfi_startproc
	ldr	x8, [x0]
	cmp	x8, #159
	b.hi	.LBB106_3
	str	x30, [sp, #-48]!
	.cfi_def_cfa_offset 48
	stp	x22, x21, [sp, #16]
	stp	x20, x19, [sp, #32]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w30, -48
	.cfi_remember_state
	mov	w9, #608
	mov	x20, x0
	mov	x19, x5
	madd	x22, x8, x9, x0
	mov	x21, x4
	str	x1, [x22, #8]!
	mov	x0, x22
	mov	x1, x2
	mov	x2, x3
	str	xzr, [x0, #8]!
	bl	_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKj24_E6extendB4_
	tbz	w0, #0, .LBB106_4
	ldr	x8, [x20]
	mov	w0, #1
	str	x21, [x22, #592]
	str	x19, [x22, #600]
	add	x8, x8, #1
	str	x8, [x20]
	ldp	x20, x19, [sp, #32]
	ldp	x22, x21, [sp, #16]
	ldr	x30, [sp], #48
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w30
	ret
.LBB106_3:
	mov	w0, wzr
	ret
.LBB106_4:
	.cfi_restore_state
	mov	w0, wzr
	ldp	x20, x19, [sp, #32]
	ldp	x22, x21, [sp, #16]
	ldr	x30, [sp], #48
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w30
	ret
.Lfunc_end106:
	.size	_RNvNtCsemcRClSg8DH_9native_vm5stack10push_claim, .Lfunc_end106-_RNvNtCsemcRClSg8DH_9native_vm5stack10push_claim
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm5stack11ring_weight,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm5stack11ring_weight,@function
_RNvNtCsemcRClSg8DH_9native_vm5stack11ring_weight:
.Lfunc_begin107:
	.cfi_startproc
	stp	x29, x30, [sp, #-96]!
	.cfi_def_cfa_offset 96
	stp	x28, x27, [sp, #16]
	stp	x26, x25, [sp, #32]
	stp	x24, x23, [sp, #48]
	stp	x22, x21, [sp, #64]
	stp	x20, x19, [sp, #80]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w24, -48
	.cfi_offset w25, -56
	.cfi_offset w26, -64
	.cfi_offset w27, -72
	.cfi_offset w28, -80
	.cfi_offset w30, -88
	.cfi_offset w29, -96
	sub	sp, sp, #592
	.cfi_def_cfa_offset 688
	lsl	x8, x2, #4
	mov	x20, x5
	cmp	x2, #1
	add	x9, sp, #16
	stp	xzr, xzr, [sp, #16]
	stp	xzr, xzr, [sp, #32]
	stp	xzr, xzr, [sp, #48]
	stp	xzr, xzr, [sp, #64]
	stp	xzr, xzr, [sp, #80]
	stp	xzr, xzr, [sp, #96]
	stp	xzr, xzr, [sp, #112]
	stp	xzr, xzr, [sp, #128]
	stp	xzr, xzr, [sp, #144]
	stp	xzr, xzr, [sp, #160]
	stp	xzr, xzr, [sp, #176]
	stp	xzr, xzr, [sp, #192]
	stp	xzr, xzr, [sp, #208]
	stp	xzr, xzr, [sp, #224]
	stp	xzr, xzr, [sp, #240]
	stp	xzr, xzr, [sp, #256]
	stp	xzr, xzr, [sp, #272]
	stp	xzr, xzr, [sp, #288]
	stp	xzr, xzr, [sp, #304]
	stp	xzr, xzr, [sp, #320]
	stp	xzr, xzr, [sp, #336]
	stp	xzr, xzr, [sp, #352]
	stp	xzr, xzr, [sp, #368]
	stp	xzr, xzr, [sp, #384]
	stp	xzr, xzr, [sp, #400]
	stp	xzr, xzr, [sp, #416]
	stp	xzr, xzr, [sp, #432]
	stp	xzr, xzr, [sp, #448]
	stp	xzr, xzr, [sp, #464]
	stp	xzr, xzr, [sp, #480]
	stp	xzr, xzr, [sp, #496]
	str	xzr, [sp, #512]
	str	xzr, [sp, #520]
	str	xzr, [sp, #528]
	str	xzr, [sp, #536]
	str	xzr, [sp, #544]
	str	xzr, [sp, #552]
	str	xzr, [sp, #560]
	str	xzr, [sp, #568]
	str	xzr, [sp, #576]
	str	xzr, [sp, #584]
	str	x0, [sp, #8]
	b.eq	.LBB107_5
	cbnz	x2, .LBB107_6
	add	x12, x8, x20
	sub	x9, x2, #64
	mov	x8, x2
	mov	x10, x2
	mov	x11, x2
	add	x13, x12, #32
	mov	x12, x2
	mov	x14, x2
	mov	x15, x2
	mov	x16, x2
.LBB107_3:
	ldp	x17, x3, [x13, #-32]
	adds	x9, x9, #4
	ldp	x18, x4, [x13, #-16]
	eor	x12, x17, x12
	ldp	x0, x17, [x13]
	eor	x14, x18, x14
	ldp	x1, x18, [x13, #16]
	eor	x2, x3, x2
	eor	x8, x4, x8
	add	x13, x13, #64
	eor	x15, x0, x15
	eor	x10, x17, x10
	eor	x16, x1, x16
	eor	x11, x18, x11
	b.ne	.LBB107_3
	eor	x9, x14, x12
	eor	x12, x16, x15
	eor	x8, x8, x2
	eor	x10, x11, x10
	eor	x21, x12, x9
	eor	x23, x10, x8
	b	.LBB107_22
.LBB107_5:
	mov	x10, xzr
	b	.LBB107_9
.LBB107_6:
	add	x12, sp, #16
	and	x10, x2, #0x3e
	add	x11, x1, #16
	add	x12, x12, #16
	and	x13, x2, #0x3e
.LBB107_7:
	ldp	x14, x16, [x11, #-16]
	subs	x13, x13, #2
	stp	x14, x16, [x12, #-16]
	ldp	x15, x14, [x11], #32
	stp	x15, x14, [x12], #32
	b.ne	.LBB107_7
	cmp	x2, x10
	b.eq	.LBB107_11
.LBB107_9:
	mov	w11, #8
	orr	x12, x11, x10, lsl #4
	sub	x10, x2, x10
	add	x11, x1, x12
	add	x12, x9, x12
.LBB107_10:
	ldp	x13, x14, [x11, #-8]
	subs	x10, x10, #1
	add	x11, x11, #16
	stp	x13, x14, [x12, #-8]
	add	x12, x12, #16
	b.ne	.LBB107_10
.LBB107_11:
	cmp	x4, x2
	add	x22, x9, x8
	mov	x23, xzr
	csel	x24, x4, x2, lo
	mov	x21, xzr
	cbz	x4, .LBB107_18
	add	x8, sp, #16
	mov	x25, xzr
	add	x19, x3, #8
	add	x27, x8, #8
.LBB107_13:
	add	x8, x20, x25
	mov	x28, x24
	mov	x29, x27
	ldp	x0, x1, [x8]
	mov	x26, x19
.LBB107_14:
	ldp	x8, x11, [x26, #-8]
	ldp	x9, x10, [x29, #-8]
	eor	x8, x9, x8
	eor	x3, x11, x10
	eor	x2, x8, #0x1
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	subs	x28, x28, #1
	add	x26, x26, #16
	add	x29, x29, #16
	b.ne	.LBB107_14
	mov	x26, x1
	mov	x28, x0
	add	x29, sp, #16
.LBB107_16:
	ldp	x0, x1, [x29]
	mov	x2, x0
	mov	x3, x1
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	stp	x0, x1, [x29], #16
	cmp	x29, x22
	b.ne	.LBB107_16
	add	x25, x25, #16
	eor	x21, x28, x21
	eor	x23, x26, x23
	cmp	x25, #1024
	b.ne	.LBB107_13
	b	.LBB107_22
.LBB107_18:
	mov	x24, xzr
.LBB107_19:
	add	x8, x20, x24
	add	x26, sp, #16
	ldp	x19, x25, [x8]
.LBB107_20:
	ldp	x0, x1, [x26]
	mov	x2, x0
	mov	x3, x1
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	stp	x0, x1, [x26], #16
	cmp	x26, x22
	b.ne	.LBB107_20
	add	x24, x24, #16
	eor	x21, x19, x21
	eor	x23, x25, x23
	cmp	x24, #1024
	b.ne	.LBB107_19
.LBB107_22:
	ldr	x9, [sp, #8]
	mov	w8, #1
	stp	x21, x23, [x9, #8]
	str	x8, [x9]
	add	sp, sp, #592
	.cfi_def_cfa_offset 96
	ldp	x20, x19, [sp, #80]
	ldp	x22, x21, [sp, #64]
	ldp	x24, x23, [sp, #48]
	ldp	x26, x25, [sp, #32]
	ldp	x28, x27, [sp, #16]
	ldp	x29, x30, [sp], #96
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w25
	.cfi_restore w26
	.cfi_restore w27
	.cfi_restore w28
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end107:
	.size	_RNvNtCsemcRClSg8DH_9native_vm5stack11ring_weight, .Lfunc_end107-_RNvNtCsemcRClSg8DH_9native_vm5stack11ring_weight
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm5stack12commit_stack,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm5stack12commit_stack,@function
_RNvNtCsemcRClSg8DH_9native_vm5stack12commit_stack:
.Lfunc_begin108:
	.cfi_startproc
	sub	sp, sp, #192
	.cfi_def_cfa_offset 192
	str	x30, [sp, #160]
	stp	x20, x19, [sp, #176]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w30, -32
	.cfi_remember_state
	mov	x19, x0
	mov	x0, sp
	mov	x20, x1
	bl	_RNvNtCsemcRClSg8DH_9native_vm4whir6ladder
	ldr	x8, [sp]
	cbz	x8, .LBB108_2
	ldr	x8, [sp, #152]
	sub	x8, x8, #7
	cmn	x8, #6
	b.hs	.LBB108_3
.LBB108_2:
	ldp	x20, x19, [sp, #176]
	mov	w0, wzr
	ldr	x30, [sp, #160]
	add	sp, sp, #192
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w30
	ret
.LBB108_3:
	.cfi_restore_state
	ldp	x8, x10, [sp, #8]
	mov	w9, #1
	mov	x0, x19
	ldr	x30, [sp, #160]
	lsl	x2, x9, x8
	subs	x8, x20, x8
	ldp	x20, x19, [sp, #176]
	csel	x8, xzr, x8, lo
	add	x1, x8, x10
	add	sp, sp, #192
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w30
	b	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState15read_commitment
.Lfunc_end108:
	.size	_RNvNtCsemcRClSg8DH_9native_vm5stack12commit_stack, .Lfunc_end108-_RNvNtCsemcRClSg8DH_9native_vm5stack12commit_stack
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm5stack13column_weight,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm5stack13column_weight,@function
_RNvNtCsemcRClSg8DH_9native_vm5stack13column_weight:
.Lfunc_begin109:
	.cfi_startproc
	str	x29, [sp, #-48]!
	.cfi_def_cfa_offset 48
	stp	x30, x21, [sp, #16]
	stp	x20, x19, [sp, #32]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w30, -32
	.cfi_offset w29, -48
	sub	sp, sp, #1056
	.cfi_def_cfa_offset 1104
	mov	x8, x5
	ldr	xzr, [sp]
	mov	x19, x0
	mov	x5, sp
	mov	x0, x1
	mov	x1, x2
	mov	x2, x3
	mov	x3, x4
	mov	x4, x8
	mov	x20, x7
	mov	x21, x6
	stp	xzr, xzr, [sp]
	stp	xzr, xzr, [sp, #16]
	stp	xzr, xzr, [sp, #32]
	stp	xzr, xzr, [sp, #48]
	stp	xzr, xzr, [sp, #64]
	stp	xzr, xzr, [sp, #80]
	stp	xzr, xzr, [sp, #96]
	stp	xzr, xzr, [sp, #112]
	stp	xzr, xzr, [sp, #128]
	stp	xzr, xzr, [sp, #144]
	stp	xzr, xzr, [sp, #160]
	stp	xzr, xzr, [sp, #176]
	stp	xzr, xzr, [sp, #192]
	stp	xzr, xzr, [sp, #208]
	stp	xzr, xzr, [sp, #224]
	stp	xzr, xzr, [sp, #240]
	stp	xzr, xzr, [sp, #256]
	stp	xzr, xzr, [sp, #272]
	stp	xzr, xzr, [sp, #288]
	stp	xzr, xzr, [sp, #304]
	stp	xzr, xzr, [sp, #320]
	stp	xzr, xzr, [sp, #336]
	stp	xzr, xzr, [sp, #352]
	stp	xzr, xzr, [sp, #368]
	stp	xzr, xzr, [sp, #384]
	stp	xzr, xzr, [sp, #400]
	stp	xzr, xzr, [sp, #416]
	stp	xzr, xzr, [sp, #432]
	stp	xzr, xzr, [sp, #448]
	stp	xzr, xzr, [sp, #464]
	stp	xzr, xzr, [sp, #480]
	stp	xzr, xzr, [sp, #496]
	str	xzr, [sp, #512]
	str	xzr, [sp, #520]
	str	xzr, [sp, #528]
	str	xzr, [sp, #536]
	str	xzr, [sp, #544]
	str	xzr, [sp, #552]
	str	xzr, [sp, #560]
	str	xzr, [sp, #568]
	str	xzr, [sp, #576]
	str	xzr, [sp, #584]
	str	xzr, [sp, #592]
	str	xzr, [sp, #600]
	str	xzr, [sp, #608]
	str	xzr, [sp, #616]
	str	xzr, [sp, #624]
	str	xzr, [sp, #632]
	str	xzr, [sp, #640]
	str	xzr, [sp, #648]
	str	xzr, [sp, #656]
	str	xzr, [sp, #664]
	str	xzr, [sp, #672]
	str	xzr, [sp, #680]
	str	xzr, [sp, #688]
	str	xzr, [sp, #696]
	str	xzr, [sp, #704]
	str	xzr, [sp, #712]
	str	xzr, [sp, #720]
	str	xzr, [sp, #728]
	str	xzr, [sp, #736]
	str	xzr, [sp, #744]
	str	xzr, [sp, #752]
	str	xzr, [sp, #760]
	str	xzr, [sp, #768]
	str	xzr, [sp, #776]
	str	xzr, [sp, #784]
	str	xzr, [sp, #792]
	str	xzr, [sp, #800]
	str	xzr, [sp, #808]
	str	xzr, [sp, #816]
	str	xzr, [sp, #824]
	str	xzr, [sp, #832]
	str	xzr, [sp, #840]
	str	xzr, [sp, #848]
	str	xzr, [sp, #856]
	str	xzr, [sp, #864]
	str	xzr, [sp, #872]
	str	xzr, [sp, #880]
	str	xzr, [sp, #888]
	str	xzr, [sp, #896]
	str	xzr, [sp, #904]
	str	xzr, [sp, #912]
	str	xzr, [sp, #920]
	str	xzr, [sp, #928]
	str	xzr, [sp, #936]
	str	xzr, [sp, #944]
	str	xzr, [sp, #952]
	str	xzr, [sp, #960]
	str	xzr, [sp, #968]
	str	xzr, [sp, #976]
	str	xzr, [sp, #984]
	str	xzr, [sp, #992]
	str	xzr, [sp, #1000]
	str	xzr, [sp, #1008]
	str	xzr, [sp, #1016]
	str	xzr, [sp, #1024]
	str	xzr, [sp, #1032]
	str	xzr, [sp, #1040]
	str	xzr, [sp, #1048]
	bl	_RNvNtCsemcRClSg8DH_9native_vm6layout11stack_point
	cmp	x0, #1
	mov	x8, xzr
	b.ne	.LBB109_2
	mov	x0, sp
	mov	x2, x21
	mov	x3, x20
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field7eq_eval
	mov	w8, #1
	stp	x0, x1, [x19, #8]
.LBB109_2:
	str	x8, [x19]
	add	sp, sp, #1056
	.cfi_def_cfa_offset 48
	ldp	x20, x19, [sp, #32]
	ldp	x30, x21, [sp, #16]
	ldr	x29, [sp], #48
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end109:
	.size	_RNvNtCsemcRClSg8DH_9native_vm5stack13column_weight, .Lfunc_end109-_RNvNtCsemcRClSg8DH_9native_vm5stack13column_weight
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm5stack17ring_claim_weight,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm5stack17ring_claim_weight,@function
_RNvNtCsemcRClSg8DH_9native_vm5stack17ring_claim_weight:
.Lfunc_begin110:
	.cfi_startproc
	sub	sp, sp, #112
	.cfi_def_cfa_offset 112
	str	x30, [sp, #32]
	stp	x26, x25, [sp, #48]
	stp	x24, x23, [sp, #64]
	stp	x22, x21, [sp, #80]
	stp	x20, x19, [sp, #96]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w24, -48
	.cfi_offset w25, -56
	.cfi_offset w26, -64
	.cfi_offset w30, -80
	add	x8, x6, x1, lsl #4
	cmp	x1, x7
	mov	w9, #8
	csel	x26, x1, x7, lo
	lsr	x10, x2, x1
	mov	x19, x0
	csel	x8, x9, x8, hi
	subs	x9, x7, x1
	mov	x25, x3
	csel	x0, xzr, x9, lo
	cmp	x1, #63
	mov	x2, x8
	csel	x1, xzr, x10, hi
	mov	x3, x0
	mov	x22, x6
	mov	x23, x5
	mov	x24, x4
	bl	_RINvNtCsemcRClSg8DH_9native_vm5field10eq_eval_fnNCNvNtB4_6layout8eq_above0EB4_
	mov	x20, x0
	mov	x21, x1
	add	x0, sp, #8
	mov	x1, x25
	mov	x2, x24
	mov	x3, x22
	mov	x4, x26
	mov	x5, x23
	bl	_RNvNtCsemcRClSg8DH_9native_vm5stack11ring_weight
	ldr	x8, [sp, #8]
	cbz	x8, .LBB110_2
	ldp	x2, x3, [sp, #16]
	mov	x0, x20
	mov	x1, x21
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	mov	w8, #1
	stp	x0, x1, [x19, #8]
.LBB110_2:
	str	x8, [x19]
	ldp	x20, x19, [sp, #96]
	ldp	x22, x21, [sp, #80]
	ldr	x30, [sp, #32]
	ldp	x24, x23, [sp, #64]
	ldp	x26, x25, [sp, #48]
	add	sp, sp, #112
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w25
	.cfi_restore w26
	.cfi_restore w30
	ret
.Lfunc_end110:
	.size	_RNvNtCsemcRClSg8DH_9native_vm5stack17ring_claim_weight, .Lfunc_end110-_RNvNtCsemcRClSg8DH_9native_vm5stack17ring_claim_weight
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm5stack8read_ood,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm5stack8read_ood,@function
_RNvNtCsemcRClSg8DH_9native_vm5stack8read_ood:
.Lfunc_begin111:
	.cfi_startproc
	sub	sp, sp, #64
	.cfi_def_cfa_offset 64
	stp	x30, x21, [sp, #32]
	stp	x20, x19, [sp, #48]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w30, -32
	.cfi_remember_state
	mov	x21, x1
	mov	w1, #15
	mov	x19, x2
	mov	x20, x0
	bl	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState5grind
	cmp	x21, #31
	csel	w8, wzr, w0, hs
	tbz	w8, #0, .LBB111_3
	mov	x1, x19
	mov	x0, x20
	mov	x2, x21
	str	x21, [x1], #8
	bl	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState17sample_challenges
	add	x0, sp, #8
	mov	x1, x20
	bl	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState11read_scalar
	ldr	x8, [sp, #8]
	cbz	x8, .LBB111_3
	ldp	x8, x9, [sp, #16]
	mov	w0, #1
	stp	x8, x9, [x19, #488]
	ldp	x20, x19, [sp, #48]
	ldp	x30, x21, [sp, #32]
	add	sp, sp, #64
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w30
	ret
.LBB111_3:
	.cfi_restore_state
	mov	w0, wzr
	ldp	x20, x19, [sp, #48]
	ldp	x30, x21, [sp, #32]
	add	sp, sp, #64
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w30
	ret
.Lfunc_end111:
	.size	_RNvNtCsemcRClSg8DH_9native_vm5stack8read_ood, .Lfunc_end111-_RNvNtCsemcRClSg8DH_9native_vm5stack8read_ood
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm6keccak8keccak_f,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm6keccak8keccak_f,@function
_RNvNtCsemcRClSg8DH_9native_vm6keccak8keccak_f:
.Lfunc_begin112:
	.cfi_startproc
	sub	sp, sp, #400
	.cfi_def_cfa_offset 400
	stp	x29, x30, [sp, #304]
	stp	x28, x27, [sp, #320]
	stp	x26, x25, [sp, #336]
	stp	x24, x23, [sp, #352]
	stp	x22, x21, [sp, #368]
	stp	x20, x19, [sp, #384]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w24, -48
	.cfi_offset w25, -56
	.cfi_offset w26, -64
	.cfi_offset w27, -72
	.cfi_offset w28, -80
	.cfi_offset w30, -88
	.cfi_offset w29, -96
	add	x8, sp, #96
	mov	x19, x0
	adrp	x1, .Lanon.a75d6d9e6a8990b4224ef13f18552af8.1
	add	x1, x1, :lo12:.Lanon.a75d6d9e6a8990b4224ef13f18552af8.1
	add	x0, x8, #16
	mov	w2, #192
	bl	memcpy
	ldp	x17, x11, [x19, #96]
	ldr	x23, [x19, #192]
	ldp	x12, x9, [x19, #48]
	str	x19, [sp, #16]
	ldp	x10, x0, [x19, #80]
	ldp	x16, x8, [x19, #64]
	ldp	x3, x21, [x19, #160]
	ldp	x2, x1, [x19, #128]
	stp	x9, x8, [sp, #56]
	ldp	x9, x8, [x19, #16]
	ldp	x7, x26, [x19, #176]
	ldp	x6, x25, [x19, #112]
	stp	x11, x9, [sp, #80]
	mov	w9, #16
	str	x8, [sp, #72]
	ldp	x4, x22, [x19, #144]
	ldp	x27, x11, [x19]
	ldp	x18, x5, [x19, #32]
.LBB112_1:
	eor	x20, x10, x25
	eor	x28, x3, x27
	eor	x29, x0, x2
	eor	x30, x21, x11
	str	x17, [sp, #24]
	eor	x20, x20, x28
	eor	x28, x29, x30
	eor	x29, x17, x1
	mov	x17, x16
	mov	x14, x2
	ldp	x2, x16, [sp, #64]
	ldr	x15, [sp, #88]
	mov	x13, x0
	eor	x8, x22, x23
	mov	x0, x23
	mov	x23, x7
	mov	x24, x22
	eor	x30, x7, x15
	eor	x19, x2, x6
	mov	x7, x1
	ldr	x1, [sp, #80]
	mov	x22, x21
	ldr	x21, [sp, #56]
	eor	x29, x29, x30
	eor	x8, x19, x8
	eor	x28, x28, x12
	eor	x19, x17, x1
	eor	x30, x4, x26
	eor	x8, x8, x18
	eor	x29, x29, x21
	eor	x20, x20, x5
	eor	x19, x19, x30
	eor	x30, x8, x28, ror #63
	eor	x8, x29, x8, ror #63
	eor	x19, x19, x16
	eor	x29, x20, x29, ror #63
	eor	x28, x28, x19, ror #63
	eor	x20, x19, x20, ror #63
	eor	x19, x25, x30
	eor	x25, x3, x30
	eor	x3, x16, x8
	ldr	x16, [sp, #24]
	str	x19, [sp, #48]
	eor	x19, x13, x29
	eor	x13, x14, x29
	eor	x14, x22, x29
	eor	x27, x27, x30
	eor	x5, x5, x30
	eor	x10, x10, x30
	str	x14, [sp, #32]
	eor	x14, x15, x28
	eor	x15, x18, x20
	eor	x2, x2, x20
	eor	x16, x16, x28
	eor	x18, x1, x8
	eor	x30, x6, x20
	eor	x4, x4, x8
	eor	x6, x24, x20
	eor	x20, x0, x20
	eor	x12, x12, x29
	str	x14, [sp, #40]
	eor	x14, x21, x28
	eor	x21, x17, x8
	eor	x22, x7, x28
	eor	x8, x26, x8
	ror	x7, x15, #37
	ror	x15, x16, #21
	ror	x26, x18, #39
	ror	x16, x4, #43
	ror	x18, x20, #50
	eor	x11, x11, x29
	eor	x28, x23, x28
	ror	x12, x12, #20
	ror	x1, x11, #63
	ror	x24, x3, #36
	ror	x23, x5, #28
	ror	x3, x14, #58
	ror	x14, x2, #44
	ror	x13, x13, #19
	ror	x2, x28, #3
	bic	x11, x16, x15
	bic	x5, x18, x16
	ror	x10, x10, #61
	bic	x29, x15, x12
	eor	x20, x11, x12
	eor	x11, x5, x15
	bic	x15, x27, x18
	bic	x12, x12, x27
	str	x11, [sp, #88]
	eor	x11, x15, x16
	bic	x16, x24, x2
	eor	x18, x12, x18
	bic	x12, x2, x13
	str	x11, [sp, #72]
	eor	x16, x16, x13
	bic	x13, x13, x10
	eor	x11, x12, x10
	bic	x10, x10, x14
	ror	x4, x25, #46
	ror	x12, x6, #56
	eor	x5, x10, x24
	bic	x10, x14, x24
	str	x11, [sp, #56]
	eor	x11, x13, x14
	eor	x10, x10, x2
	bic	x13, x1, x4
	ror	x8, x8, #8
	str	x10, [sp, #64]
	bic	x10, x4, x12
	eor	x13, x13, x12
	eor	x17, x10, x26
	bic	x10, x26, x3
	ror	x14, x22, #49
	str	x13, [sp, #80]
	bic	x12, x12, x26
	ror	x13, x19, #54
	eor	x15, x10, x1
	bic	x10, x3, x1
	eor	x0, x12, x3
	bic	x12, x7, x8
	eor	x6, x10, x4
	bic	x10, x8, x14
	eor	x4, x12, x14
	bic	x12, x14, x13
	eor	x1, x10, x13
	bic	x10, x13, x23
	ldp	x3, x13, [sp, #40]
	ldr	x14, [sp, #32]
	eor	x2, x12, x23
	add	x12, sp, #96
	eor	x25, x10, x7
	bic	x10, x23, x7
	ldr	x12, [x12, x9]
	ror	x13, x13, #23
	ror	x14, x14, #62
	ror	x24, x21, #9
	ror	x21, x30, #25
	ror	x19, x3, #2
	eor	x22, x10, x8
	bic	x8, x14, x13
	eor	x10, x12, x27
	add	x9, x9, #8
	bic	x12, x21, x24
	eor	x7, x8, x21
	bic	x8, x13, x21
	eor	x3, x12, x19
	eor	x21, x8, x24
	bic	x8, x24, x19
	bic	x12, x19, x14
	cmp	x9, #208
	eor	x23, x8, x14
	eor	x26, x12, x13
	mov	x12, x11
	mov	x11, x20
	eor	x27, x29, x10
	mov	x10, x15
	b.ne	.LBB112_1
	ldr	x8, [sp, #16]
	ldr	x9, [sp, #64]
	ldp	x20, x19, [sp, #384]
	stp	x16, x9, [x8, #64]
	ldp	x29, x30, [sp, #304]
	stp	x10, x0, [x8, #80]
	ldp	x10, x9, [sp, #80]
	stp	x6, x25, [x8, #112]
	stp	x4, x22, [x8, #144]
	stp	x11, x9, [x8, #8]
	ldr	x9, [sp, #72]
	stp	x3, x21, [x8, #160]
	ldp	x22, x21, [sp, #368]
	stp	x7, x26, [x8, #176]
	ldp	x26, x25, [sp, #336]
	str	x23, [x8, #192]
	ldp	x24, x23, [sp, #352]
	stp	x9, x18, [x8, #24]
	ldr	x9, [sp, #56]
	str	x27, [x8]
	ldp	x28, x27, [sp, #320]
	stp	x17, x10, [x8, #96]
	stp	x2, x1, [x8, #128]
	stp	x5, x12, [x8, #40]
	str	x9, [x8, #56]
	add	sp, sp, #400
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w25
	.cfi_restore w26
	.cfi_restore w27
	.cfi_restore w28
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end112:
	.size	_RNvNtCsemcRClSg8DH_9native_vm6keccak8keccak_f, .Lfunc_end112-_RNvNtCsemcRClSg8DH_9native_vm6keccak8keccak_f
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm6keccak9hash_pair,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm6keccak9hash_pair,@function
_RNvNtCsemcRClSg8DH_9native_vm6keccak9hash_pair:
.Lfunc_begin113:
	.cfi_startproc
	sub	sp, sp, #80
	.cfi_def_cfa_offset 80
	.cfi_offset w30, -16
	ldp	x8, x9, [x1]
	mov	x3, sp
	mov	w4, #8
	stp	x8, x9, [sp]
	ldp	x8, x10, [x1, #16]
	mov	w1, #8
	stp	x8, x10, [sp, #16]
	ldp	x8, x9, [x2]
	stp	x8, x9, [sp, #32]
	ldp	x8, x10, [x2, #16]
	mov	w2, #64
	str	x8, [sp, #48]
	stp	x10, x30, [sp, #56]
	bl	_RINvNtCsemcRClSg8DH_9native_vm6keccak15keccak256_wordsNCNvB2_10hash_words0EB4_
	ldr	x30, [sp, #64]
	add	sp, sp, #80
	.cfi_def_cfa_offset 0
	.cfi_restore w30
	ret
.Lfunc_end113:
	.size	_RNvNtCsemcRClSg8DH_9native_vm6keccak9hash_pair, .Lfunc_end113-_RNvNtCsemcRClSg8DH_9native_vm6keccak9hash_pair
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm6layout10form_terms,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm6layout10form_terms,@function
_RNvNtCsemcRClSg8DH_9native_vm6layout10form_terms:
.Lfunc_begin114:
	.cfi_startproc
	cmp	x0, #592
	b.hi	.LBB114_2
	adrp	x8, .Lanon.a75d6d9e6a8990b4224ef13f18552af8.13
	add	x8, x8, :lo12:.Lanon.a75d6d9e6a8990b4224ef13f18552af8.13
	mov	w10, #40
	add	x8, x8, x0, lsl #4
	adrp	x11, .Lanon.a75d6d9e6a8990b4224ef13f18552af8.14
	add	x11, x11, :lo12:.Lanon.a75d6d9e6a8990b4224ef13f18552af8.14
	ldp	x9, x8, [x8]
	madd	x10, x9, x10, x11
	add	x11, x8, x9
	cmp	x11, x9
	mov	w9, #770
	ccmp	x11, x9, #2, hs
	mov	w9, #8
	csel	x1, x8, xzr, lo
	csel	x0, x10, x9, lo
	ret
.LBB114_2:
	mov	x1, xzr
	mov	w0, #8
	ret
.Lfunc_end114:
	.size	_RNvNtCsemcRClSg8DH_9native_vm6layout10form_terms, .Lfunc_end114-_RNvNtCsemcRClSg8DH_9native_vm6layout10form_terms
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm6layout11stack_point,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm6layout11stack_point,@function
_RNvNtCsemcRClSg8DH_9native_vm6layout11stack_point:
.Lfunc_begin115:
	.cfi_startproc
	stp	x30, x19, [sp, #-16]!
	.cfi_def_cfa_offset 16
	.cfi_offset w19, -8
	.cfi_offset w30, -16
	subs	x8, x4, x0
	mov	x9, x2
	csel	x2, xzr, x8, lo
	mov	x8, xzr
	add	x19, x2, x3
	cmp	x19, #66
	ccmp	x19, x3, #0, ls
	b.lo	.LBB115_10
	add	x8, x5, x3, lsl #4
	cbz	x3, .LBB115_9
	cmp	x3, #1
	b.ne	.LBB115_4
	mov	x10, xzr
	b	.LBB115_7
.LBB115_4:
	and	x10, x3, #0x3e
	add	x11, x9, #16
	add	x12, x5, #16
	and	x13, x3, #0x3e
.LBB115_5:
	ldp	x14, x16, [x11, #-16]
	subs	x13, x13, #2
	stp	x14, x16, [x12, #-16]
	ldp	x15, x14, [x11], #32
	stp	x15, x14, [x12], #32
	b.ne	.LBB115_5
	cmp	x3, x10
	b.eq	.LBB115_9
.LBB115_7:
	mov	w11, #8
	orr	x11, x11, x10, lsl #4
	sub	x10, x3, x10
	add	x9, x9, x11
	add	x11, x5, x11
.LBB115_8:
	ldp	x12, x13, [x9, #-8]
	subs	x10, x10, #1
	add	x9, x9, #16
	stp	x12, x13, [x11, #-8]
	add	x11, x11, #16
	b.ne	.LBB115_8
.LBB115_9:
	lsr	x9, x1, x0
	cmp	x0, #63
	mov	x1, x8
	csel	x0, xzr, x9, hi
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field14selector_point
	mov	w8, #1
.LBB115_10:
	mov	x0, x8
	mov	x1, x19
	ldp	x30, x19, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w30
	ret
.Lfunc_end115:
	.size	_RNvNtCsemcRClSg8DH_9native_vm6layout11stack_point, .Lfunc_end115-_RNvNtCsemcRClSg8DH_9native_vm6layout11stack_point
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm6layout12build_layout,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm6layout12build_layout,@function
_RNvNtCsemcRClSg8DH_9native_vm6layout12build_layout:
.Lfunc_begin116:
	.cfi_startproc
	sub	x8, x0, #1
	eor	x9, x0, x8
	cmp	x9, x8
	b.ls	.LBB116_10
	stp	x29, x30, [sp, #-96]!
	.cfi_def_cfa_offset 96
	stp	x28, x27, [sp, #16]
	stp	x26, x25, [sp, #32]
	stp	x24, x23, [sp, #48]
	stp	x22, x21, [sp, #64]
	stp	x20, x19, [sp, #80]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w24, -48
	.cfi_offset w25, -56
	.cfi_offset w26, -64
	.cfi_offset w27, -72
	.cfi_offset w28, -80
	.cfi_offset w30, -88
	.cfi_offset w29, -96
	sub	sp, sp, #1264
	.cfi_def_cfa_offset 1360
	.cfi_remember_state
	ldr	xzr, [sp]
	mov	x21, x2
	mov	x19, x1
	mov	x22, x3
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field10bit_length
	sub	x20, x0, #5
	sub	x8, x19, #1
	cmn	x20, #5
	ccmp	x8, #29, #2, ls
	b.hi	.LBB116_11
	ldr	x28, [x21]
	mov	w8, #1073741824
	cmp	x28, x8
	b.hi	.LBB116_11
	ldr	x27, [x21, #8]
	mov	w8, #1
	movk	w8, #16384, lsl #16
	cmp	x27, x8
	b.hs	.LBB116_11
	ldr	x26, [x21, #16]
	cmp	x26, x8
	b.hs	.LBB116_11
	ldr	x25, [x21, #24]
	cmp	x25, x8
	b.hs	.LBB116_11
	ldr	x24, [x21, #32]
	cmp	x24, x8
	b.hs	.LBB116_11
	ldr	x23, [x21, #40]
	cmp	x20, #30
	ccmp	x23, x8, #2, ls
	b.hs	.LBB116_11
	subs	x8, x28, #1
	mov	x21, x22
	stp	x19, x20, [x22]
	csel	x0, xzr, x8, lo
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field10bit_length
	subs	x8, x27, #1
	str	x0, [x21, #24]!
	csel	x0, xzr, x8, lo
	str	x28, [x21, #48]
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field10bit_length
	subs	x8, x26, #1
	str	x0, [x21, #8]
	csel	x0, xzr, x8, lo
	str	x27, [x21, #56]
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field10bit_length
	subs	x8, x25, #1
	str	x0, [x21, #16]
	csel	x0, xzr, x8, lo
	str	x26, [x21, #64]
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field10bit_length
	subs	x8, x24, #1
	str	x0, [x21, #24]
	csel	x0, xzr, x8, lo
	str	x25, [x21, #72]
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field10bit_length
	subs	x8, x23, #1
	str	x0, [x21, #32]
	csel	x0, xzr, x8, lo
	str	x24, [x21, #80]
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field10bit_length
	mov	w8, #9
	cmp	x0, #9
	mov	x1, x19
	csel	x8, x0, x8, hi
	mov	x0, sp
	mov	x2, x20
	mov	x3, x21
	str	x8, [x21, #40]
	str	x23, [x21, #88]
	bl	_RNvNtCsemcRClSg8DH_9native_vm6layout13column_kappas
	mov	x0, sp
	add	x1, x21, #96
	bl	_RNvNtCsemcRClSg8DH_9native_vm6layout13placements_of
	cmp	x0, #1
	b.ne	.LBB116_12
	str	x1, [x22, #16]
	b	.LBB116_12
.LBB116_10:
	.cfi_def_cfa wsp, 0
	.cfi_same_value w19
	.cfi_same_value w20
	.cfi_same_value w21
	.cfi_same_value w22
	.cfi_same_value w23
	.cfi_same_value w24
	.cfi_same_value w25
	.cfi_same_value w26
	.cfi_same_value w27
	.cfi_same_value w28
	.cfi_same_value w30
	.cfi_same_value w29
	mov	w0, wzr
	and	w0, w0, #0x1
	ret
.LBB116_11:
	.cfi_restore_state
	mov	w0, wzr
.LBB116_12:
	add	sp, sp, #1264
	.cfi_def_cfa_offset 96
	ldp	x20, x19, [sp, #80]
	ldp	x22, x21, [sp, #64]
	ldp	x24, x23, [sp, #48]
	ldp	x26, x25, [sp, #32]
	ldp	x28, x27, [sp, #16]
	ldp	x29, x30, [sp], #96
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w25
	.cfi_restore w26
	.cfi_restore w27
	.cfi_restore w28
	.cfi_restore w30
	.cfi_restore w29
	and	w0, w0, #0x1
	ret
.Lfunc_end116:
	.size	_RNvNtCsemcRClSg8DH_9native_vm6layout12build_layout, .Lfunc_end116-_RNvNtCsemcRClSg8DH_9native_vm6layout12build_layout
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm6layout13column_kappas,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm6layout13column_kappas,@function
_RNvNtCsemcRClSg8DH_9native_vm6layout13column_kappas:
.Lfunc_begin117:
	.cfi_startproc
	ldp	x9, x8, [x3, #32]
	ldr	x10, [x3]
	stp	x1, x1, [x0]
	stp	x10, x10, [x0, #48]
	add	x11, x8, #6
	stp	x10, x10, [x0, #64]
	stp	x11, x10, [x0, #32]
	stp	x10, x10, [x0, #80]
	stp	x10, x10, [x0, #96]
	stp	x10, x10, [x0, #112]
	stp	x10, x10, [x0, #128]
	ldp	x11, x10, [x3, #8]
	stp	x11, x11, [x0, #144]
	stp	x11, x11, [x0, #160]
	stp	x11, x11, [x0, #176]
	stp	x11, x11, [x0, #192]
	stp	x11, x11, [x0, #208]
	stp	x11, x11, [x0, #224]
	stp	x11, x10, [x0, #240]
	ldr	x11, [x3, #24]
	stp	x1, x2, [x0, #16]
	stp	x10, x10, [x0, #256]
	stp	x10, x10, [x0, #272]
	stp	x10, x10, [x0, #288]
	stp	x11, x11, [x0, #304]
	stp	x11, x11, [x0, #320]
	stp	x11, x11, [x0, #336]
	stp	x11, x11, [x0, #352]
	stp	x11, x11, [x0, #368]
	stp	x11, x11, [x0, #384]
	stp	x11, x11, [x0, #400]
	stp	x9, x9, [x0, #416]
	stp	x9, x9, [x0, #432]
	stp	x9, x9, [x0, #448]
	stp	x9, x9, [x0, #464]
	stp	x9, x9, [x0, #480]
	stp	x9, x9, [x0, #496]
	str	x9, [x0, #512]
	str	x9, [x0, #520]
	str	x8, [x0, #528]
	str	x8, [x0, #536]
	str	x8, [x0, #544]
	str	x8, [x0, #552]
	str	x8, [x0, #560]
	str	x8, [x0, #568]
	str	x8, [x0, #576]
	str	x8, [x0, #584]
	str	x8, [x0, #592]
	str	x8, [x0, #600]
	str	x8, [x0, #608]
	str	x8, [x0, #616]
	str	x8, [x0, #624]
	str	x8, [x0, #632]
	str	x8, [x0, #640]
	str	x8, [x0, #648]
	str	x8, [x0, #656]
	str	x8, [x0, #664]
	str	x8, [x0, #672]
	str	x8, [x0, #680]
	str	x8, [x0, #688]
	str	x8, [x0, #696]
	str	x8, [x0, #704]
	str	x8, [x0, #712]
	str	x8, [x0, #720]
	str	x8, [x0, #728]
	str	x8, [x0, #736]
	str	x8, [x0, #744]
	str	x8, [x0, #752]
	str	x8, [x0, #760]
	str	x8, [x0, #768]
	str	x8, [x0, #776]
	str	x8, [x0, #784]
	str	x8, [x0, #792]
	str	x8, [x0, #800]
	str	x8, [x0, #808]
	str	x8, [x0, #816]
	str	x8, [x0, #824]
	str	x8, [x0, #832]
	str	x8, [x0, #840]
	str	x8, [x0, #848]
	str	x8, [x0, #856]
	str	x8, [x0, #864]
	str	x8, [x0, #872]
	str	x8, [x0, #880]
	str	x8, [x0, #888]
	str	x8, [x0, #896]
	str	x8, [x0, #904]
	str	x8, [x0, #912]
	str	x8, [x0, #920]
	str	x8, [x0, #928]
	str	x8, [x0, #936]
	str	x8, [x0, #944]
	str	x8, [x0, #952]
	str	x8, [x0, #960]
	str	x8, [x0, #968]
	str	x8, [x0, #976]
	str	x8, [x0, #984]
	str	x8, [x0, #992]
	str	x8, [x0, #1000]
	str	x8, [x0, #1008]
	str	x8, [x0, #1016]
	str	x8, [x0, #1024]
	str	x8, [x0, #1032]
	str	x8, [x0, #1040]
	str	x8, [x0, #1048]
	str	x8, [x0, #1056]
	str	x8, [x0, #1064]
	str	x8, [x0, #1072]
	str	x8, [x0, #1080]
	str	x8, [x0, #1088]
	str	x8, [x0, #1096]
	str	x8, [x0, #1104]
	str	x8, [x0, #1112]
	str	x8, [x0, #1120]
	str	x8, [x0, #1128]
	str	x8, [x0, #1136]
	str	x8, [x0, #1144]
	str	x8, [x0, #1152]
	str	x8, [x0, #1160]
	str	x8, [x0, #1168]
	str	x8, [x0, #1176]
	str	x8, [x0, #1184]
	str	x8, [x0, #1192]
	str	x8, [x0, #1200]
	str	x8, [x0, #1208]
	str	x8, [x0, #1216]
	str	x8, [x0, #1224]
	str	x8, [x0, #1232]
	str	x8, [x0, #1240]
	str	x8, [x0, #1248]
	str	x8, [x0, #1256]
	ret
.Lfunc_end117:
	.size	_RNvNtCsemcRClSg8DH_9native_vm6layout13column_kappas, .Lfunc_end117-_RNvNtCsemcRClSg8DH_9native_vm6layout13column_kappas
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm6layout13constraints_w,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm6layout13constraints_w,@function
_RNvNtCsemcRClSg8DH_9native_vm6layout13constraints_w:
.Lfunc_begin118:
	.cfi_startproc
	cmp	x0, #4
	b.ne	.LBB118_5
	stp	x30, x23, [sp, #-48]!
	.cfi_def_cfa_offset 48
	stp	x22, x21, [sp, #16]
	stp	x20, x19, [sp, #32]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w30, -48
	.cfi_remember_state
	mov	x19, x3
	cmp	x2, #6
	b.lo	.LBB118_6
	ldp	x21, x20, [x1, #80]
	cmp	x2, #13
	b.lo	.LBB118_7
	mov	x8, x2
	ldp	x2, x3, [x1, #192]
	cmp	x8, #13
	b.eq	.LBB118_8
	ldp	x23, x22, [x1, #208]
	b	.LBB118_9
.LBB118_5:
	.cfi_def_cfa wsp, 0
	.cfi_same_value w19
	.cfi_same_value w20
	.cfi_same_value w21
	.cfi_same_value w22
	.cfi_same_value w23
	.cfi_same_value w30
	mov	x0, xzr
	ret
.LBB118_6:
	.cfi_restore_state
	mov	x2, xzr
	mov	x3, xzr
	mov	x20, xzr
	mov	x21, xzr
	b	.LBB118_8
.LBB118_7:
	mov	x2, xzr
	mov	x3, xzr
.LBB118_8:
	mov	x22, xzr
	mov	x23, xzr
.LBB118_9:
	mov	x0, x21
	mov	x1, x20
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	eor	x8, x0, x23
	eor	x9, x1, x22
	eor	x2, x23, #0x1
	mov	x0, x21
	mov	x1, x20
	mov	x3, x22
	stp	x8, x9, [x19]
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	ldp	x22, x21, [sp, #16]
	stp	x0, x1, [x19, #16]
	ldp	x20, x19, [sp, #32]
	mov	w0, #2
	ldp	x30, x23, [sp], #48
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w30
	ret
.Lfunc_end118:
	.size	_RNvNtCsemcRClSg8DH_9native_vm6layout13constraints_w, .Lfunc_end118-_RNvNtCsemcRClSg8DH_9native_vm6layout13constraints_w
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm6layout13placements_of,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm6layout13placements_of,@function
_RNvNtCsemcRClSg8DH_9native_vm6layout13placements_of:
.Lfunc_begin119:
	.cfi_startproc
	stp	x29, x30, [sp, #-80]!
	.cfi_def_cfa_offset 80
	stp	x26, x25, [sp, #16]
	stp	x24, x23, [sp, #32]
	stp	x22, x21, [sp, #48]
	stp	x20, x19, [sp, #64]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w24, -48
	.cfi_offset w25, -56
	.cfi_offset w26, -64
	.cfi_offset w30, -72
	.cfi_offset w29, -80
	sub	sp, sp, #1, lsl #12
	.cfi_def_cfa_offset 4176
	ldr	xzr, [sp]
	sub	sp, sp, #960
	.cfi_def_cfa_offset 5136
	mov	x20, x1
	mov	x19, x0
	mov	w1, wzr
	mov	x0, sp
	mov	w2, #1264
	mov	w21, #1264
	mov	x25, sp
	bl	memset
	add	x0, sp, #1264
	mov	w1, wzr
	mov	w2, #1264
	add	x26, sp, #1264
	bl	memset
	mov	x22, xzr
	mov	x8, xzr
	adrp	x23, .Lanon.a75d6d9e6a8990b4224ef13f18552af8.15
	add	x23, x23, :lo12:.Lanon.a75d6d9e6a8990b4224ef13f18552af8.15
	adrp	x24, .Lanon.a75d6d9e6a8990b4224ef13f18552af8.16
	add	x24, x24, :lo12:.Lanon.a75d6d9e6a8990b4224ef13f18552af8.16
	b	.LBB119_2
.LBB119_1:
	subs	x21, x21, #8
	add	x8, x8, #1
	b.eq	.LBB119_6
.LBB119_2:
	ldrb	w9, [x23, x8]
	cmp	w9, #255
	b.ne	.LBB119_1
	ldrb	w9, [x24, x8]
	cbnz	w9, .LBB119_1
	cmp	x22, #158
	b.hs	.LBB119_23
	ldr	x9, [x19, x8, lsl #3]
	str	x8, [x25, x22, lsl #3]
	str	x9, [x26, x22, lsl #3]
	add	x22, x22, #1
	b	.LBB119_1
.LBB119_6:
	add	x0, sp, #2528
	mov	w1, wzr
	mov	w2, #1264
	bl	memset
	cmp	x22, #159
	b.hs	.LBB119_23
	add	x0, sp, #1264
	add	x2, sp, #2528
	mov	x1, x22
	mov	w3, #158
	bl	_RNvNtCsemcRClSg8DH_9native_vm6layout13stack_offsets
	cmp	x0, #1
	b.ne	.LBB119_23
	mov	x21, x1
	add	x0, sp, #3792
	mov	w1, wzr
	mov	w2, #1264
	add	x25, sp, #3792
	bl	memset
	cbz	x22, .LBB119_13
	add	x8, sp, #2528
	mov	x9, sp
.LBB119_10:
	ldr	x10, [x9], #8
	cmp	x10, #158
	b.hs	.LBB119_23
	ldr	x11, [x8], #8
	subs	x22, x22, #1
	str	x11, [x25, x10, lsl #3]
	b.ne	.LBB119_10
	ldr	x8, [sp, #3824]
	b	.LBB119_14
.LBB119_13:
	mov	x8, xzr
.LBB119_14:
	mov	x9, xzr
	add	x10, x20, #16
	b	.LBB119_17
.LBB119_15:
	ldr	x12, [x25, x9, lsl #3]
.LBB119_16:
	mov	w13, #1
	add	x9, x9, #1
	stp	x13, x11, [x10, #-16]
	cmp	x9, #158
	str	x12, [x10], #24
	b.eq	.LBB119_22
.LBB119_17:
	ldrb	w12, [x23, x9]
	ldr	x11, [x19, x9, lsl #3]
	cmp	x12, #255
	b.eq	.LBB119_20
	cmp	x11, #64
	b.hs	.LBB119_23
	lsl	x12, x12, x11
	adds	x12, x8, x12
	b.lo	.LBB119_16
	b	.LBB119_23
.LBB119_20:
	ldrb	w12, [x24, x9]
	tbz	w12, #0, .LBB119_15
	add	x9, x9, #1
	stp	xzr, xzr, [x10, #-16]
	cmp	x9, #158
	str	xzr, [x10], #24
	b.ne	.LBB119_17
.LBB119_22:
	cmp	x21, #16
	mov	w8, #16
	mov	w0, #1
	csel	x1, x21, x8, hi
	b	.LBB119_24
.LBB119_23:
	mov	x0, xzr
.LBB119_24:
	add	sp, sp, #1, lsl #12
	.cfi_def_cfa_offset 1040
	add	sp, sp, #960
	.cfi_def_cfa_offset 80
	ldp	x20, x19, [sp, #64]
	ldp	x22, x21, [sp, #48]
	ldp	x24, x23, [sp, #32]
	ldp	x26, x25, [sp, #16]
	ldp	x29, x30, [sp], #80
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w25
	.cfi_restore w26
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end119:
	.size	_RNvNtCsemcRClSg8DH_9native_vm6layout13placements_of, .Lfunc_end119-_RNvNtCsemcRClSg8DH_9native_vm6layout13placements_of
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm6layout13stack_offsets,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm6layout13stack_offsets,@function
_RNvNtCsemcRClSg8DH_9native_vm6layout13stack_offsets:
.Lfunc_begin120:
	.cfi_startproc
	cmp	x3, x1
	b.hs	.LBB120_2
	mov	x0, xzr
	ret
.LBB120_2:
	stp	x29, x30, [sp, #-64]!
	.cfi_def_cfa_offset 64
	stp	x24, x23, [sp, #16]
	stp	x22, x21, [sp, #32]
	stp	x20, x19, [sp, #48]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w24, -48
	.cfi_offset w30, -56
	.cfi_offset w29, -64
	sub	sp, sp, #1264
	.cfi_def_cfa_offset 1328
	.cfi_remember_state
	ldr	xzr, [sp]
	mov	x20, x2
	mov	x21, x1
	mov	x22, x0
	mov	x0, sp
	mov	w1, wzr
	mov	w2, #1264
	mov	x19, x3
	mov	x24, sp
	bl	memset
	lsl	x23, x21, #3
	cbz	x21, .LBB120_5
	sub	x8, x23, #8
	mov	x11, sp
	cmp	x8, #23
	b.hi	.LBB120_6
	mov	x8, xzr
	mov	x9, sp
	b	.LBB120_9
.LBB120_5:
	mov	x0, sp
	mov	x1, xzr
	mov	x2, x22
	mov	x3, xzr
	b	.LBB120_12
.LBB120_6:
	lsr	x8, x8, #3
	mov	w12, #1
	add	x10, x8, #1
	and	x8, x10, #0x3ffffffffffffffc
	add	x9, x11, x8, lsl #3
	add	x11, x11, #16
.LBB120_7:
	sub	x13, x12, #1
	add	x14, x12, #3
	add	x15, x12, #2
	stp	x13, x12, [x11, #-16]
	add	x13, x12, #1
	cmp	x14, x8
	add	x12, x12, #4
	stp	x13, x15, [x11], #32
	b.ne	.LBB120_7
	cmp	x10, x8
	b.eq	.LBB120_11
.LBB120_9:
	add	x10, x24, x23
.LBB120_10:
	str	x8, [x9], #8
	cmp	x9, x10
	add	x8, x8, #1
	b.ne	.LBB120_10
.LBB120_11:
	mov	x0, sp
	mov	x1, x21
	mov	x2, x22
	mov	x3, x21
.LBB120_12:
	bl	_RINvNtCsemcRClSg8DH_9native_vm6layout14insertion_sortNCNvB2_13stack_offsetss_0EB4_
	mov	x8, xzr
	mov	x9, sp
	mov	w10, #1
	b	.LBB120_15
.LBB120_13:
	mov	x11, xzr
.LBB120_14:
	lsl	x11, x10, x11
	sub	x23, x23, #8
	adds	x8, x11, x8
	b.hs	.LBB120_19
.LBB120_15:
	cbz	x23, .LBB120_20
	ldr	x11, [x9], #8
	cmp	x11, x19
	b.hs	.LBB120_19
	cmp	x11, x21
	str	x8, [x20, x11, lsl #3]
	b.hs	.LBB120_13
	ldr	x11, [x22, x11, lsl #3]
	cmp	x11, #63
	b.ls	.LBB120_14
.LBB120_19:
	mov	x0, xzr
	add	sp, sp, #1264
	.cfi_def_cfa_offset 64
	ldp	x20, x19, [sp, #48]
	ldp	x22, x21, [sp, #32]
	ldp	x24, x23, [sp, #16]
	ldp	x29, x30, [sp], #64
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w30
	.cfi_restore w29
	ret
.LBB120_20:
	.cfi_restore_state
	subs	x8, x8, #1
	csel	x0, xzr, x8, lo
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field10bit_length
	mov	x1, x0
	mov	w0, #1
	add	sp, sp, #1264
	.cfi_def_cfa_offset 64
	ldp	x20, x19, [sp, #48]
	ldp	x22, x21, [sp, #32]
	ldp	x24, x23, [sp, #16]
	ldp	x29, x30, [sp], #64
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end120:
	.size	_RNvNtCsemcRClSg8DH_9native_vm6layout13stack_offsets, .Lfunc_end120-_RNvNtCsemcRClSg8DH_9native_vm6layout13stack_offsets
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm6layout20read_announced_sizes,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm6layout20read_announced_sizes,@function
_RNvNtCsemcRClSg8DH_9native_vm6layout20read_announced_sizes:
.Lfunc_begin121:
	.cfi_startproc
	sub	sp, sp, #208
	.cfi_def_cfa_offset 208
	stp	x30, x21, [sp, #176]
	stp	x20, x19, [sp, #192]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w30, -32
	.cfi_remember_state
	mov	x19, x2
	mov	x20, x1
	mov	x1, sp
	mov	w2, #8
	stp	xzr, xzr, [sp]
	stp	xzr, xzr, [sp, #16]
	stp	xzr, xzr, [sp, #32]
	stp	xzr, xzr, [sp, #48]
	stp	xzr, xzr, [sp, #64]
	stp	xzr, xzr, [sp, #80]
	stp	xzr, xzr, [sp, #96]
	stp	xzr, xzr, [sp, #112]
	bl	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState12read_scalars
	mov	w8, w0
	mov	x0, xzr
	cbz	w8, .LBB121_14
	ldr	x8, [sp, #8]
	cbnz	x8, .LBB121_14
	ldr	x8, [sp, #24]
	cbnz	x8, .LBB121_14
	ldr	x8, [sp, #40]
	cbnz	x8, .LBB121_14
	ldr	x8, [sp, #56]
	cbnz	x8, .LBB121_14
	ldr	x8, [sp, #72]
	cbnz	x8, .LBB121_14
	ldr	x8, [sp, #88]
	cbnz	x8, .LBB121_14
	ldr	x8, [sp, #104]
	cbnz	x8, .LBB121_14
	ldr	x8, [sp, #120]
	cbnz	x8, .LBB121_12
	ldr	x8, [sp, #16]
	ldr	x9, [sp, #32]
	ldr	x10, [sp, #48]
	ldr	x21, [sp, #112]
	ldr	x1, [sp]
	stp	x8, x9, [sp, #128]
	ldr	x8, [sp, #64]
	ldr	x9, [sp, #80]
	sub	x11, x21, #1
	stp	x10, x8, [sp, #144]
	ldr	x10, [sp, #96]
	cmp	x11, #3
	stp	x9, x10, [sp, #160]
	b.hi	.LBB121_13
	add	x2, sp, #128
	mov	x0, x20
	mov	x3, x19
	bl	_RNvNtCsemcRClSg8DH_9native_vm6layout12build_layout
	cbz	w0, .LBB121_13
	ldr	x8, [x19, #16]
	sub	x8, x8, #16
	cmp	x8, #15
	cset	w0, lo
.LBB121_12:
	mov	x1, x21
	ldp	x20, x19, [sp, #192]
	ldp	x30, x21, [sp, #176]
	add	sp, sp, #208
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w30
	ret
.LBB121_13:
	.cfi_restore_state
	.cfi_remember_state
	mov	x0, xzr
	mov	x1, x21
	ldp	x20, x19, [sp, #192]
	ldp	x30, x21, [sp, #176]
	add	sp, sp, #208
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w30
	ret
.LBB121_14:
	.cfi_restore_state
	mov	x1, x21
	ldp	x20, x19, [sp, #192]
	ldp	x30, x21, [sp, #176]
	add	sp, sp, #208
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w30
	ret
.Lfunc_end121:
	.size	_RNvNtCsemcRClSg8DH_9native_vm6layout20read_announced_sizes, .Lfunc_end121-_RNvNtCsemcRClSg8DH_9native_vm6layout20read_announced_sizes
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm6layout8evaluate,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm6layout8evaluate,@function
_RNvNtCsemcRClSg8DH_9native_vm6layout8evaluate:
.Lfunc_begin122:
	.cfi_startproc
	stp	x30, x27, [sp, #-80]!
	.cfi_def_cfa_offset 80
	stp	x26, x25, [sp, #16]
	stp	x24, x23, [sp, #32]
	stp	x22, x21, [sp, #48]
	stp	x20, x19, [sp, #64]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w24, -48
	.cfi_offset w25, -56
	.cfi_offset w26, -64
	.cfi_offset w27, -72
	.cfi_offset w30, -80
	cbz	x1, .LBB122_11
	mov	x20, x3
	mov	x21, x2
	mov	x22, x1
	mov	x19, xzr
	mov	x23, xzr
	add	x24, x0, #32
	mov	w25, #8
	b	.LBB122_5
.LBB122_2:
	add	x8, x21, x8, lsl #4
	ldp	x2, x3, [x8]
.LBB122_3:
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
.LBB122_4:
	subs	x22, x22, #1
	add	x24, x24, #40
	eor	x23, x0, x23
	eor	x19, x1, x19
	b.eq	.LBB122_12
.LBB122_5:
	ldur	x26, [x24, #-32]
	ldp	x0, x1, [x24, #-8]
	sub	x8, x24, #24
	cmp	x26, #2
	sub	x9, x26, #3
	csel	x27, x25, x8, hi
	cmn	x9, #2
	b.lo	.LBB122_4
	ldr	x8, [x27]
	cmp	x8, x20
	b.hs	.LBB122_8
	add	x8, x21, x8, lsl #4
	ldp	x2, x3, [x8]
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	cmp	x26, #1
	b.eq	.LBB122_4
	b	.LBB122_9
.LBB122_8:
	mov	x3, xzr
	mov	x2, xzr
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	cmp	x26, #1
	b.eq	.LBB122_4
.LBB122_9:
	ldr	x8, [x27, #8]
	cmp	x8, x20
	b.lo	.LBB122_2
	mov	x3, xzr
	mov	x2, xzr
	b	.LBB122_3
.LBB122_11:
	mov	x19, xzr
	mov	x23, xzr
.LBB122_12:
	mov	x0, x23
	mov	x1, x19
	ldp	x20, x19, [sp, #64]
	ldp	x22, x21, [sp, #48]
	ldp	x24, x23, [sp, #32]
	ldp	x26, x25, [sp, #16]
	ldp	x30, x27, [sp], #80
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w25
	.cfi_restore w26
	.cfi_restore w27
	.cfi_restore w30
	ret
.Lfunc_end122:
	.size	_RNvNtCsemcRClSg8DH_9native_vm6layout8evaluate, .Lfunc_end122-_RNvNtCsemcRClSg8DH_9native_vm6layout8evaluate
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm6tables11table_phase,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm6tables11table_phase,@function
_RNvNtCsemcRClSg8DH_9native_vm6tables11table_phase:
.Lfunc_begin123:
	.cfi_startproc
	sub	sp, sp, #128
	.cfi_def_cfa_offset 128
	stp	x30, x23, [sp, #80]
	stp	x22, x21, [sp, #96]
	stp	x20, x19, [sp, #112]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w30, -48
	mov	x21, x0
	mov	w0, #3
	mov	x19, x3
	mov	x20, x2
	mov	x22, x1
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field10bit_length
	subs	w8, w0, #3
	mov	x0, x21
	csel	w1, wzr, w8, lo
	bl	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState5grind
	mov	w8, w0
	mov	w0, wzr
	cbz	w8, .LBB123_2
	mov	x0, x21
	bl	_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW7squeeze
	mov	x2, sp
	mov	w3, #5
	stp	xzr, xzr, [sp]
	stp	xzr, xzr, [sp, #16]
	mov	x23, sp
	stp	xzr, xzr, [sp, #32]
	stp	xzr, xzr, [sp, #48]
	stp	xzr, xzr, [sp, #64]
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field6powers
	add	x8, x20, #26, lsl #12
	add	x0, x23, #32
	mov	w1, #3
	add	x2, x8, #1224
	mov	w3, #3
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field3dot
	mov	x5, x0
	mov	x6, x1
	add	x1, x22, #24
	mov	x3, sp
	add	x4, x23, #32
	mov	x0, x21
	mov	x2, x20
	mov	x7, x19
	bl	_RNvNtCsemcRClSg8DH_9native_vm6tables14table_sumcheck
.LBB123_2:
	ldp	x20, x19, [sp, #112]
	ldp	x22, x21, [sp, #96]
	ldp	x30, x23, [sp, #80]
	add	sp, sp, #128
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w30
	ret
.Lfunc_end123:
	.size	_RNvNtCsemcRClSg8DH_9native_vm6tables11table_phase, .Lfunc_end123-_RNvNtCsemcRClSg8DH_9native_vm6tables11table_phase
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm6tables11table_terms,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm6tables11table_terms,@function
_RNvNtCsemcRClSg8DH_9native_vm6tables11table_terms:
.Lfunc_begin124:
	.cfi_startproc
	sub	sp, sp, #288
	.cfi_def_cfa_offset 288
	stp	x29, x30, [sp, #192]
	stp	x28, x27, [sp, #208]
	stp	x26, x25, [sp, #224]
	stp	x24, x23, [sp, #240]
	stp	x22, x21, [sp, #256]
	stp	x20, x19, [sp, #272]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w24, -48
	.cfi_offset w25, -56
	.cfi_offset w26, -64
	.cfi_offset w27, -72
	.cfi_offset w28, -80
	.cfi_offset w30, -88
	.cfi_offset w29, -96
	ldp	x8, x27, [sp, #288]
	adrp	x19, .Lanon.a75d6d9e6a8990b4224ef13f18552af8.4+8
	add	x19, x19, :lo12:.Lanon.a75d6d9e6a8990b4224ef13f18552af8.4+8
	mov	x20, x7
	mov	x26, xzr
	mov	x23, xzr
	mov	x22, xzr
	mov	w29, #240
	add	x8, x8, #8
	mov	x21, x19
	stp	x4, x5, [sp, #40]
	stp	x2, x3, [sp, #24]
	str	x1, [sp, #56]
	str	x0, [sp, #16]
	stp	x8, x6, [sp, #96]
.LBB124_1:
	ldr	x28, [x21], #40
	cmp	x28, #93
	b.hs	.LBB124_6
	ldr	x0, [sp, #56]
	add	x1, x27, #496
	mov	x2, x28
	str	x28, [x27, #488]
	bl	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState12read_scalars
	cbz	w0, .LBB124_6
	ldur	x0, [x19, #-8]
	add	x1, x27, #496
	add	x3, sp, #112
	mov	x2, x28
	stp	x23, x22, [sp, #80]
	stp	xzr, xzr, [sp, #112]
	stp	xzr, xzr, [sp, #128]
	bl	_RNvNtCsemcRClSg8DH_9native_vm6layout13constraints_w
	ldr	x8, [sp, #24]
	cmp	x26, #2
	mov	w23, #8
	mov	x3, x0
	ldr	x22, [x19, #8]
	add	x2, sp, #112
	add	x8, x8, x26, lsl #4
	csel	x0, x23, x8, hi
	mov	w8, #2
	subs	x8, x8, x26
	csel	x8, xzr, x8, lo
	cmp	x22, x8
	csel	x1, x22, x8, lo
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field3dot
	ldr	x8, [x20]
	add	x9, x20, #8
	stp	x1, x0, [sp, #64]
	add	x2, x27, #496
	mov	x3, x28
	cmp	x8, #149
	csel	x0, x9, x23, lo
	csel	x1, x8, xzr, lo
	bl	_RNvNtCsemcRClSg8DH_9native_vm6layout8evaluate
	ldr	x8, [x20, #5928]
	mov	w9, #5936
	stp	x0, x1, [sp, #144]
	add	x9, x20, x9
	add	x2, x27, #496
	mov	x3, x28
	cmp	x8, #149
	csel	x0, x9, x23, lo
	csel	x1, x8, xzr, lo
	bl	_RNvNtCsemcRClSg8DH_9native_vm6layout8evaluate
	ldr	x8, [x20, #11856]
	mov	w9, #11864
	stp	x0, x1, [sp, #160]
	add	x9, x20, x9
	add	x2, x27, #496
	mov	x3, x28
	cmp	x8, #149
	csel	x0, x9, x23, lo
	csel	x1, x8, xzr, lo
	bl	_RNvNtCsemcRClSg8DH_9native_vm6layout8evaluate
	ldr	x19, [sp, #96]
	stp	x0, x1, [sp, #176]
	add	x2, sp, #144
	ldr	x0, [sp, #32]
	mov	w1, #3
	mov	w3, #3
	ldp	x28, x23, [x19, #-8]
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field3dot
	ldr	x9, [sp, #104]
	mov	x25, x1
	mov	x24, x0
	mov	x0, x27
	str	xzr, [x27]
	ldr	x8, [x9], #8
	str	x9, [sp, #104]
	ldp	x1, x9, [sp, #40]
	cmp	x8, x9
	csel	x2, x8, x9, lo
	bl	_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKj1e_E6extendB4_
	tbz	w0, #0, .LBB124_6
	ldp	x8, x9, [sp, #64]
	add	x19, x19, #16
	mov	x0, x28
	mov	x1, x23
	str	x19, [sp, #96]
	eor	x2, x24, x9
	eor	x3, x25, x8
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	add	x26, x22, x26
	ldp	x23, x22, [sp, #80]
	mov	w8, #17784
	subs	x29, x29, #40
	add	x27, x27, #1968
	add	x20, x20, x8
	mov	x19, x21
	eor	x23, x1, x23
	eor	x22, x0, x22
	b.ne	.LBB124_1
	ldr	x9, [sp, #16]
	mov	w8, #1
	stp	x22, x23, [x9, #8]
	str	x8, [x9]
	b	.LBB124_7
.LBB124_6:
	ldr	x8, [sp, #16]
	str	xzr, [x8]
.LBB124_7:
	ldp	x20, x19, [sp, #272]
	ldp	x22, x21, [sp, #256]
	ldp	x24, x23, [sp, #240]
	ldp	x26, x25, [sp, #224]
	ldp	x28, x27, [sp, #208]
	ldp	x29, x30, [sp, #192]
	add	sp, sp, #288
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w25
	.cfi_restore w26
	.cfi_restore w27
	.cfi_restore w28
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end124:
	.size	_RNvNtCsemcRClSg8DH_9native_vm6tables11table_terms, .Lfunc_end124-_RNvNtCsemcRClSg8DH_9native_vm6tables11table_terms
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm6tables13table_weights,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm6tables13table_weights,@function
_RNvNtCsemcRClSg8DH_9native_vm6tables13table_weights:
.Lfunc_begin125:
	.cfi_startproc
	sub	sp, sp, #240
	.cfi_def_cfa_offset 240
	stp	x29, x30, [sp, #144]
	stp	x28, x27, [sp, #160]
	stp	x26, x25, [sp, #176]
	stp	x24, x23, [sp, #192]
	stp	x22, x21, [sp, #208]
	stp	x20, x19, [sp, #224]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w24, -48
	.cfi_offset w25, -56
	.cfi_offset w26, -64
	.cfi_offset w27, -72
	.cfi_offset w28, -80
	.cfi_offset w30, -88
	.cfi_offset w29, -96
	str	x3, [sp, #72]
	str	x0, [sp, #8]
	cbz	x5, .LBB125_6
	ldp	x11, x8, [x1]
	add	x10, x4, x5, lsl #4
	mov	x27, x4
	mov	x9, xzr
	mov	x22, xzr
	add	x23, x2, #8
	mov	w0, #1
	mov	w19, #1
	stp	x11, x10, [sp, #56]
	mov	w28, #1
	mov	w20, #1
	str	x8, [sp, #48]
	ldp	x10, x8, [x1, #16]
	mov	w21, #1
	stp	xzr, xzr, [sp, #128]
	stp	xzr, xzr, [sp, #112]
	stp	x8, x10, [sp, #32]
	ldp	x10, x8, [x1, #32]
	stp	x8, x10, [sp, #16]
	mov	w8, #1
	stp	x8, xzr, [sp, #96]
	b	.LBB125_4
.LBB125_2:
	ldp	x8, x9, [x23, #-8]
	eor	x25, x8, #0x1
	eor	x26, x9, x24
.LBB125_3:
	ldr	x8, [sp, #56]
	ldr	x29, [x27], #16
	ldr	x1, [sp, #104]
	mov	x0, x21
	cmp	x22, x8
	csel	x8, x25, xzr, lo
	csel	x3, x26, x24, lo
	eor	x2, x8, x29
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	ldr	x8, [sp, #48]
	str	x1, [sp, #104]
	mov	x21, x0
	ldr	x1, [sp, #112]
	mov	x0, x20
	cmp	x22, x8
	csel	x8, x25, xzr, lo
	csel	x3, x26, x24, lo
	eor	x2, x8, x29
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	ldr	x8, [sp, #40]
	str	x1, [sp, #112]
	mov	x20, x0
	ldr	x1, [sp, #120]
	mov	x0, x28
	cmp	x22, x8
	csel	x8, x25, xzr, lo
	csel	x3, x26, x24, lo
	eor	x2, x8, x29
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	ldr	x8, [sp, #32]
	str	x1, [sp, #120]
	mov	x28, x0
	ldr	x1, [sp, #128]
	mov	x0, x19
	cmp	x22, x8
	csel	x8, x25, xzr, lo
	csel	x3, x26, x24, lo
	eor	x2, x8, x29
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	ldr	x8, [sp, #24]
	mov	x19, x0
	str	x1, [sp, #128]
	ldr	x0, [sp, #96]
	ldr	x1, [sp, #136]
	cmp	x22, x8
	csel	x8, x25, xzr, lo
	csel	x3, x26, x24, lo
	eor	x2, x8, x29
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	ldr	x8, [sp, #16]
	str	x0, [sp, #96]
	str	x1, [sp, #136]
	ldp	x0, x1, [sp, #80]
	cmp	x22, x8
	csel	x8, x25, xzr, lo
	csel	x3, x26, x24, lo
	eor	x2, x8, x29
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	ldr	x8, [sp, #64]
	mov	x9, x1
	add	x23, x23, #16
	add	x22, x22, #1
	cmp	x27, x8
	b.eq	.LBB125_7
.LBB125_4:
	ldr	x8, [sp, #72]
	ldr	x24, [x27, #8]
	stp	x0, x9, [sp, #80]
	cmp	x22, x8
	b.lo	.LBB125_2
	mov	w25, #1
	mov	x26, x24
	b	.LBB125_3
.LBB125_6:
	mov	w8, #1
	mov	x9, xzr
	stp	xzr, xzr, [sp, #128]
	stp	xzr, xzr, [sp, #112]
	mov	w0, #1
	mov	w19, #1
	stp	x8, xzr, [sp, #96]
	mov	w28, #1
	mov	w20, #1
	mov	w21, #1
.LBB125_7:
	ldp	x11, x10, [sp, #104]
	ldr	x8, [sp, #8]
	ldp	x24, x23, [sp, #192]
	ldp	x26, x25, [sp, #176]
	stp	x0, x9, [x8, #80]
	stp	x21, x11, [x8]
	ldp	x22, x21, [sp, #208]
	stp	x20, x10, [x8, #16]
	ldp	x11, x10, [sp, #120]
	ldp	x29, x30, [sp, #144]
	stp	x28, x11, [x8, #32]
	ldr	x11, [sp, #96]
	stp	x19, x10, [x8, #48]
	ldr	x10, [sp, #136]
	ldp	x20, x19, [sp, #224]
	stp	x11, x10, [x8, #64]
	ldp	x28, x27, [sp, #160]
	add	sp, sp, #240
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w25
	.cfi_restore w26
	.cfi_restore w27
	.cfi_restore w28
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end125:
	.size	_RNvNtCsemcRClSg8DH_9native_vm6tables13table_weights, .Lfunc_end125-_RNvNtCsemcRClSg8DH_9native_vm6tables13table_weights
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm6tables14table_sumcheck,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm6tables14table_sumcheck,@function
_RNvNtCsemcRClSg8DH_9native_vm6tables14table_sumcheck:
.Lfunc_begin126:
	.cfi_startproc
	stp	x29, x30, [sp, #-96]!
	.cfi_def_cfa_offset 96
	stp	x28, x27, [sp, #16]
	stp	x26, x25, [sp, #32]
	stp	x24, x23, [sp, #48]
	stp	x22, x21, [sp, #64]
	stp	x20, x19, [sp, #80]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w24, -48
	.cfi_offset w25, -56
	.cfi_offset w26, -64
	.cfi_offset w27, -72
	.cfi_offset w28, -80
	.cfi_offset w30, -88
	.cfi_offset w29, -96
	sub	sp, sp, #624
	.cfi_def_cfa_offset 720
	ldp	x9, x10, [x1]
	stp	xzr, xzr, [sp, #24]
	stp	xzr, xzr, [sp, #40]
	stp	xzr, xzr, [sp, #56]
	cmp	x10, x9
	stp	xzr, xzr, [sp, #72]
	csel	x9, x10, x9, hi
	ldp	x11, x10, [x1, #16]
	stp	xzr, xzr, [sp, #88]
	stp	xzr, xzr, [sp, #104]
	cmp	x11, x9
	stp	xzr, xzr, [sp, #120]
	csel	x9, x11, x9, hi
	stp	xzr, xzr, [sp, #136]
	cmp	x10, x9
	stp	xzr, xzr, [sp, #152]
	csel	x9, x10, x9, hi
	ldp	x11, x10, [x1, #32]
	stp	xzr, xzr, [sp, #168]
	stp	xzr, xzr, [sp, #184]
	cmp	x11, x9
	stp	xzr, xzr, [sp, #200]
	csel	x9, x11, x9, hi
	stp	xzr, xzr, [sp, #216]
	cmp	x10, x9
	stp	xzr, xzr, [sp, #232]
	csel	x25, x10, x9, hi
	stp	xzr, xzr, [sp, #248]
	cmp	x25, #30
	stp	xzr, xzr, [sp, #264]
	stp	xzr, xzr, [sp, #280]
	stp	xzr, xzr, [sp, #296]
	stp	xzr, xzr, [sp, #312]
	stp	xzr, xzr, [sp, #328]
	stp	xzr, xzr, [sp, #344]
	stp	xzr, xzr, [sp, #360]
	stp	xzr, xzr, [sp, #376]
	stp	xzr, xzr, [sp, #392]
	stp	xzr, xzr, [sp, #408]
	stp	xzr, xzr, [sp, #424]
	stp	xzr, xzr, [sp, #440]
	stp	xzr, xzr, [sp, #456]
	stp	xzr, xzr, [sp, #472]
	stp	xzr, xzr, [sp, #488]
	b.hi	.LBB126_7
	mov	x8, x5
	mov	x23, x0
	mov	x20, x4
	mov	x22, x3
	mov	x19, x2
	mov	x21, x1
	add	x0, sp, #504
	add	x5, sp, #24
	mov	x1, x23
	mov	x2, x8
	mov	x3, x6
	mov	w4, #4
	mov	x6, x25
	mov	x24, x7
	bl	_RINvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB6_6TState8sumcheckNCNvB2_14sumcheck_plain0EB8_
	ldr	x8, [sp, #504]
	cbz	x8, .LBB126_7
	lsr	x8, x25, #1
	cbz	x8, .LBB126_5
	add	x9, sp, #24
	add	x10, x9, x25, lsl #4
	sub	x10, x10, #16
.LBB126_4:
	ldp	x11, x12, [x10]
	sub	x8, x8, #1
	ldp	x13, x14, [x9]
	stp	x11, x12, [x9], #16
	stp	x13, x14, [x10], #-16
	cbnz	x8, .LBB126_4
.LBB126_5:
	add	x8, x19, #24, lsl #12
	add	x9, x19, #26, lsl #12
	mov	w10, #8
	ldr	x8, [x8, #8400]
	add	x9, x9, #216
	ldr	x26, [sp, #512]
	ldr	x27, [sp, #520]
	add	x0, sp, #504
	add	x4, sp, #24
	cmp	x8, #64
	mov	x1, x21
	mov	x5, x25
	csel	x2, x9, x10, lo
	csel	x3, x8, xzr, lo
	add	x28, sp, #504
	bl	_RNvNtCsemcRClSg8DH_9native_vm6tables13table_weights
	add	x0, sp, #600
	add	x4, sp, #24
	mov	x1, x23
	mov	x2, x22
	mov	x3, x20
	mov	x5, x25
	mov	x6, x21
	mov	x7, x19
	stp	x28, x24, [sp]
	bl	_RNvNtCsemcRClSg8DH_9native_vm6tables11table_terms
	ldr	w8, [sp, #600]
	tbz	w8, #0, .LBB126_7
	ldr	x8, [sp, #608]
	ldr	x9, [sp, #616]
	cmp	x8, x26
	ccmp	x9, x27, #0, eq
	cset	w0, eq
	b	.LBB126_8
.LBB126_7:
	mov	w0, wzr
.LBB126_8:
	add	sp, sp, #624
	.cfi_def_cfa_offset 96
	ldp	x20, x19, [sp, #80]
	ldp	x22, x21, [sp, #64]
	ldp	x24, x23, [sp, #48]
	ldp	x26, x25, [sp, #32]
	ldp	x28, x27, [sp, #16]
	ldp	x29, x30, [sp], #96
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w25
	.cfi_restore w26
	.cfi_restore w27
	.cfi_restore w28
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end126:
	.size	_RNvNtCsemcRClSg8DH_9native_vm6tables14table_sumcheck, .Lfunc_end126-_RNvNtCsemcRClSg8DH_9native_vm6tables14table_sumcheck
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm6tables18public_input_phase,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm6tables18public_input_phase,@function
_RNvNtCsemcRClSg8DH_9native_vm6tables18public_input_phase:
.Lfunc_begin127:
	.cfi_startproc
	str	x29, [sp, #-64]!
	.cfi_def_cfa_offset 64
	stp	x30, x23, [sp, #16]
	stp	x22, x21, [sp, #32]
	stp	x20, x19, [sp, #48]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w30, -48
	.cfi_offset w29, -64
	sub	sp, sp, #544
	.cfi_def_cfa_offset 608
	.cfi_remember_state
	mov	x19, x3
	mov	x20, x2
	mov	x23, x1
	bl	_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW7squeeze
	mov	x21, x0
	mov	x22, x1
	mov	x0, x23
	mov	x1, xzr
	stp	xzr, xzr, [sp]
	stp	xzr, xzr, [sp, #16]
	stp	xzr, xzr, [sp, #32]
	stp	xzr, xzr, [sp, #48]
	stp	xzr, xzr, [sp, #64]
	stp	xzr, xzr, [sp, #80]
	stp	xzr, xzr, [sp, #96]
	stp	xzr, xzr, [sp, #112]
	stp	xzr, xzr, [sp, #128]
	stp	xzr, xzr, [sp, #144]
	stp	xzr, xzr, [sp, #160]
	stp	xzr, xzr, [sp, #176]
	stp	xzr, xzr, [sp, #192]
	stp	xzr, xzr, [sp, #208]
	stp	xzr, xzr, [sp, #224]
	stp	xzr, xzr, [sp, #240]
	stp	xzr, xzr, [sp, #256]
	stp	xzr, xzr, [sp, #272]
	stp	xzr, xzr, [sp, #288]
	stp	xzr, xzr, [sp, #304]
	stp	xzr, xzr, [sp, #320]
	stp	xzr, xzr, [sp, #336]
	stp	xzr, xzr, [sp, #352]
	stp	xzr, xzr, [sp, #368]
	stp	xzr, xzr, [sp, #384]
	stp	xzr, xzr, [sp, #400]
	stp	xzr, xzr, [sp, #416]
	stp	xzr, xzr, [sp, #432]
	stp	xzr, xzr, [sp, #448]
	stp	xzr, xzr, [sp, #464]
	stp	xzr, xzr, [sp, #480]
	bl	_RNvMs2_NtCsemcRClSg8DH_9native_vm6layoutNtB5_7LayoutW9placement
	cmp	x0, #1
	csinc	x23, x0, xzr, hi
	cmp	x0, #31
	b.hi	.LBB127_4
	ldr	x8, [x20]
	ldr	x9, [x20, #16]
	add	x1, sp, #496
	add	x3, sp, #528
	mov	w0, #2
	mov	w2, #2
	mov	w4, #1
	stp	x21, x22, [sp]
	stp	x8, xzr, [sp, #496]
	str	x9, [sp, #512]
	str	xzr, [sp, #520]
	str	x21, [sp, #528]
	str	x22, [sp, #536]
	bl	_RINvNtCsemcRClSg8DH_9native_vm5field19multilinear_eval_byNCNvB2_16multilinear_eval0EB4_
	mov	x4, x0
	mov	x5, x1
	mov	x2, sp
	mov	x0, x19
	mov	x1, xzr
	mov	x3, x23
	bl	_RNvNtCsemcRClSg8DH_9native_vm5stack10push_claim
	cbz	w0, .LBB127_3
	ldr	x8, [x20, #8]
	ldr	x9, [x20, #24]
	add	x1, sp, #496
	add	x3, sp, #528
	mov	w0, #2
	mov	w2, #2
	mov	w4, #1
	stp	x8, xzr, [sp, #496]
	str	x9, [sp, #512]
	str	xzr, [sp, #520]
	str	x21, [sp, #528]
	str	x22, [sp, #536]
	bl	_RINvNtCsemcRClSg8DH_9native_vm5field19multilinear_eval_byNCNvB2_16multilinear_eval0EB4_
	mov	x4, x0
	mov	x5, x1
	mov	x2, sp
	mov	x0, x19
	mov	w1, #1
	mov	x3, x23
	bl	_RNvNtCsemcRClSg8DH_9native_vm5stack10push_claim
.LBB127_3:
	add	sp, sp, #544
	.cfi_def_cfa_offset 64
	ldp	x20, x19, [sp, #48]
	ldp	x22, x21, [sp, #32]
	ldp	x30, x23, [sp, #16]
	ldr	x29, [sp], #64
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w30
	.cfi_restore w29
	ret
.LBB127_4:
	.cfi_restore_state
	mov	w0, wzr
	add	sp, sp, #544
	.cfi_def_cfa_offset 64
	ldp	x20, x19, [sp, #48]
	ldp	x22, x21, [sp, #32]
	ldp	x30, x23, [sp, #16]
	ldr	x29, [sp], #64
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end127:
	.size	_RNvNtCsemcRClSg8DH_9native_vm6tables18public_input_phase, .Lfunc_end127-_RNvNtCsemcRClSg8DH_9native_vm6tables18public_input_phase
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm6tables19table_column_claims,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm6tables19table_column_claims,@function
_RNvNtCsemcRClSg8DH_9native_vm6tables19table_column_claims:
.Lfunc_begin128:
	.cfi_startproc
	stp	x30, x25, [sp, #-64]!
	.cfi_def_cfa_offset 64
	stp	x24, x23, [sp, #16]
	stp	x22, x21, [sp, #32]
	stp	x20, x19, [sp, #48]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w24, -48
	.cfi_offset w25, -56
	.cfi_offset w30, -64
	.cfi_remember_state
	ldr	x10, [x0, #488]
	ldr	x11, [x0]
	mov	w9, #8
	add	x8, x0, #496
	add	x12, x0, #8
	mov	x19, x1
	cmp	x10, #93
	mov	x20, x0
	mov	w23, #4
	csel	x10, x10, xzr, lo
	csel	x8, x8, x9, lo
	cmp	x11, #31
	lsl	x24, x10, #4
	csel	x21, x12, x9, lo
	csel	x22, x11, xzr, lo
.LBB128_1:
	cbz	x24, .LBB128_3
	ldp	x4, x5, [x8]
	add	x23, x23, #1
	mov	x0, x19
	mov	x1, x23
	mov	x2, x21
	mov	x3, x22
	add	x25, x8, #16
	sub	x24, x24, #16
	bl	_RNvNtCsemcRClSg8DH_9native_vm5stack10push_claim
	mov	x8, x25
	tbnz	w0, #0, .LBB128_1
	b	.LBB128_15
.LBB128_3:
	ldr	x9, [x20, #2456]
	ldr	x11, [x20, #1968]
	add	x8, x20, #2464
	mov	w10, #8
	add	x12, x20, #1976
	mov	w23, #17
	cmp	x9, #93
	csel	x9, x9, xzr, lo
	csel	x8, x8, x10, lo
	cmp	x11, #31
	lsl	x24, x9, #4
	csel	x21, x12, x10, lo
	csel	x22, x11, xzr, lo
.LBB128_4:
	cbz	x24, .LBB128_6
	ldp	x4, x5, [x8]
	add	x23, x23, #1
	mov	x0, x19
	mov	x1, x23
	mov	x2, x21
	mov	x3, x22
	add	x25, x8, #16
	sub	x24, x24, #16
	bl	_RNvNtCsemcRClSg8DH_9native_vm5stack10push_claim
	mov	x8, x25
	tbnz	w0, #0, .LBB128_4
	b	.LBB128_15
.LBB128_6:
	ldr	x9, [x20, #4424]
	mov	w8, #4432
	ldr	x11, [x20, #3936]
	add	x8, x20, x8
	mov	w10, #8
	add	x12, x20, #3944
	cmp	x9, #93
	mov	w23, #30
	csel	x9, x9, xzr, lo
	csel	x8, x8, x10, lo
	cmp	x11, #31
	lsl	x24, x9, #4
	csel	x21, x12, x10, lo
	csel	x22, x11, xzr, lo
.LBB128_7:
	cbz	x24, .LBB128_9
	ldp	x4, x5, [x8]
	add	x23, x23, #1
	mov	x0, x19
	mov	x1, x23
	mov	x2, x21
	mov	x3, x22
	add	x25, x8, #16
	sub	x24, x24, #16
	bl	_RNvNtCsemcRClSg8DH_9native_vm5stack10push_claim
	mov	x8, x25
	tbnz	w0, #0, .LBB128_7
	b	.LBB128_15
.LBB128_9:
	ldr	x9, [x20, #6392]
	mov	w8, #6400
	ldr	x11, [x20, #5904]
	add	x8, x20, x8
	mov	w10, #8
	mov	w12, #5912
	cmp	x9, #93
	add	x12, x20, x12
	mov	w23, #37
	csel	x9, x9, xzr, lo
	csel	x8, x8, x10, lo
	cmp	x11, #31
	lsl	x24, x9, #4
	csel	x21, x12, x10, lo
	csel	x22, x11, xzr, lo
.LBB128_10:
	cbz	x24, .LBB128_12
	ldp	x4, x5, [x8]
	add	x23, x23, #1
	mov	x0, x19
	mov	x1, x23
	mov	x2, x21
	mov	x3, x22
	add	x25, x8, #16
	sub	x24, x24, #16
	bl	_RNvNtCsemcRClSg8DH_9native_vm5stack10push_claim
	mov	x8, x25
	tbnz	w0, #0, .LBB128_10
	b	.LBB128_15
.LBB128_12:
	ldr	x9, [x20, #8360]
	mov	w8, #8368
	ldr	x11, [x20, #7872]
	add	x8, x20, x8
	mov	w10, #8
	mov	w12, #7880
	cmp	x9, #93
	add	x12, x20, x12
	mov	w23, #51
	csel	x9, x9, xzr, lo
	csel	x8, x8, x10, lo
	cmp	x11, #31
	lsl	x24, x9, #4
	csel	x21, x12, x10, lo
	csel	x22, x11, xzr, lo
.LBB128_13:
	cbz	x24, .LBB128_17
	ldp	x4, x5, [x8]
	add	x23, x23, #1
	mov	x0, x19
	mov	x1, x23
	mov	x2, x21
	mov	x3, x22
	add	x25, x8, #16
	sub	x24, x24, #16
	bl	_RNvNtCsemcRClSg8DH_9native_vm5stack10push_claim
	mov	x8, x25
	tbnz	w0, #0, .LBB128_13
.LBB128_15:
	mov	w0, wzr
.LBB128_16:
	ldp	x20, x19, [sp, #48]
	ldp	x22, x21, [sp, #32]
	ldp	x24, x23, [sp, #16]
	ldp	x30, x25, [sp], #64
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w25
	.cfi_restore w30
	ret
.LBB128_17:
	.cfi_restore_state
	ldr	x8, [x20, #10328]
	mov	w9, #10336
	ldr	x11, [x20, #9840]
	add	x9, x20, x9
	mov	w10, #8
	mov	w12, #9848
	cmp	x8, #93
	add	x12, x20, x12
	mov	w22, #65
	csel	x8, x8, xzr, lo
	csel	x9, x9, x10, lo
	cmp	x11, #31
	lsl	x23, x8, #4
	csel	x20, x12, x10, lo
	csel	x21, x11, xzr, lo
.LBB128_18:
	cbz	x23, .LBB128_20
	ldp	x4, x5, [x9]
	add	x22, x22, #1
	mov	x0, x19
	mov	x1, x22
	mov	x2, x20
	mov	x3, x21
	add	x24, x9, #16
	sub	x23, x23, #16
	bl	_RNvNtCsemcRClSg8DH_9native_vm5stack10push_claim
	mov	w8, w0
	mov	w0, wzr
	mov	x9, x24
	tbnz	w8, #0, .LBB128_18
	b	.LBB128_16
.LBB128_20:
	mov	w0, #1
	ldp	x20, x19, [sp, #48]
	ldp	x22, x21, [sp, #32]
	ldp	x24, x23, [sp, #16]
	ldp	x30, x25, [sp], #64
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w25
	.cfi_restore w30
	ret
.Lfunc_end128:
	.size	_RNvNtCsemcRClSg8DH_9native_vm6tables19table_column_claims, .Lfunc_end128-_RNvNtCsemcRClSg8DH_9native_vm6tables19table_column_claims
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm6verify16verify_execution,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm6verify16verify_execution,@function
_RNvNtCsemcRClSg8DH_9native_vm6verify16verify_execution:
.Lfunc_begin129:
	.cfi_startproc
	sub	sp, sp, #96
	.cfi_def_cfa_offset 96
	str	x30, [sp, #16]
	stp	x26, x25, [sp, #32]
	stp	x24, x23, [sp, #48]
	stp	x22, x21, [sp, #64]
	stp	x20, x19, [sp, #80]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w24, -48
	.cfi_offset w25, -56
	.cfi_offset w26, -64
	.cfi_offset w30, -80
	mov	x23, x2
	mov	x24, x1
	mov	x1, x2
	mov	x2, x4
	mov	x19, x4
	mov	x22, x3
	mov	x20, x0
	bl	_RNvNtCsemcRClSg8DH_9native_vm6layout20read_announced_sizes
	cmp	x0, #1
	b.ne	.LBB129_10
	ldr	x25, [x19, #16]
	mov	x21, x1
	mov	x0, x20
	mov	x2, x21
	mov	x1, x25
	bl	_RNvNtCsemcRClSg8DH_9native_vm5stack12commit_stack
	cbz	w0, .LBB129_10
	add	x2, x19, #3912
	mov	x0, x20
	mov	x1, x25
	bl	_RNvNtCsemcRClSg8DH_9native_vm5stack8read_ood
	cbz	w0, .LBB129_10
	mov	w25, #58456
	mov	w26, #4416
	mov	x0, x20
	movk	w25, #1, lsl #16
	add	x4, x19, x26
	mov	x1, x19
	add	x5, x19, x25
	mov	x2, x24
	mov	x3, x23
	bl	_RNvNtCsemcRClSg8DH_9native_vm3bus18verify_bus_balance
	cbz	w0, .LBB129_10
	mov	w23, #46648
	add	x2, x19, x26
	mov	x0, x20
	movk	w23, #1, lsl #16
	mov	x1, x19
	add	x3, x19, x23
	bl	_RNvNtCsemcRClSg8DH_9native_vm6tables11table_phase
	cbz	w0, .LBB129_10
	add	x0, x19, x23
	add	x1, x19, x25
	bl	_RNvNtCsemcRClSg8DH_9native_vm6tables19table_column_claims
	cbz	w0, .LBB129_10
	add	x3, x19, x25
	mov	x0, x20
	mov	x1, x19
	mov	x2, x22
	bl	_RNvNtCsemcRClSg8DH_9native_vm6tables18public_input_phase
	cbz	w0, .LBB129_10
	mov	w22, #24672
	ldr	x1, [x19, #64]
	add	x8, x19, #70, lsl #12
	movk	w22, #3, lsl #16
	add	x2, x19, x23
	add	x4, x19, x25
	add	x3, x8, #3008
	add	x5, x19, x22
	mov	x0, x20
	bl	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr12keccak_phase
	cbz	w0, .LBB129_10
	mov	w23, #26280
	add	x8, x19, #54, lsl #12
	mov	x0, x20
	movk	w23, #3, lsl #16
	add	x1, x8, #680
	add	x2, x19, x23
	bl	_RNvNtCsemcRClSg8DH_9native_vm11ring_switch11ring_switch
	cbz	w0, .LBB129_10
	add	x8, x19, #55, lsl #12
	add	x9, x19, #54, lsl #12
	add	x3, x19, x23
	add	x8, x8, #1248
	add	x4, x19, x22
	add	x5, x19, x25
	add	x6, x19, #3912
	add	x7, x9, #2744
	mov	x0, x20
	mov	x1, x19
	mov	x2, x21
	str	x8, [sp]
	bl	_RNvNtCsemcRClSg8DH_9native_vm4whir22verify_stacked_opening
	b	.LBB129_11
.LBB129_10:
	mov	w0, wzr
.LBB129_11:
	ldp	x20, x19, [sp, #80]
	ldr	x30, [sp, #16]
	ldp	x22, x21, [sp, #64]
	ldp	x24, x23, [sp, #48]
	ldp	x26, x25, [sp, #32]
	add	sp, sp, #96
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w25
	.cfi_restore w26
	.cfi_restore w30
	ret
.Lfunc_end129:
	.size	_RNvNtCsemcRClSg8DH_9native_vm6verify16verify_execution, .Lfunc_end129-_RNvNtCsemcRClSg8DH_9native_vm6verify16verify_execution
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm6verify4seed,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm6verify4seed,@function
_RNvNtCsemcRClSg8DH_9native_vm6verify4seed:
.Lfunc_begin130:
	.cfi_startproc
	sub	sp, sp, #240
	.cfi_def_cfa_offset 240
	stp	x30, x21, [sp, #208]
	stp	x20, x19, [sp, #224]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w30, -32
	lsl	x8, x2, #3
	mov	x19, x3
	mov	x4, x2
	mov	x3, x1
	mov	x20, x0
	add	x0, sp, #8
	add	x1, x2, #2
	add	x2, x8, #9
	add	x21, sp, #8
	bl	_RINvNtCsemcRClSg8DH_9native_vm6keccak15keccak256_wordsNCNvNtB4_6verify14fiat_shamir_iv0EB4_
	add	x0, x21, #64
	mov	w1, wzr
	mov	w2, #136
	bl	memset
	ldp	x8, x9, [x19]
	add	x0, sp, #8
	stp	x8, x9, [sp, #40]
	ldp	x8, x10, [x19, #16]
	stp	x8, x10, [sp, #56]
	bl	_RNvNtCsemcRClSg8DH_9native_vm6keccak8keccak_f
	add	x1, sp, #8
	mov	x0, x20
	mov	w2, #200
	bl	memcpy
	ldp	x20, x19, [sp, #224]
	ldp	x30, x21, [sp, #208]
	add	sp, sp, #240
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w30
	ret
.Lfunc_end130:
	.size	_RNvNtCsemcRClSg8DH_9native_vm6verify4seed, .Lfunc_end130-_RNvNtCsemcRClSg8DH_9native_vm6verify4seed
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm6verify6verify,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm6verify6verify,@function
_RNvNtCsemcRClSg8DH_9native_vm6verify6verify:
.Lfunc_begin131:
	.cfi_startproc
	str	x29, [sp, #-64]!
	.cfi_def_cfa_offset 64
	stp	x30, x23, [sp, #16]
	stp	x22, x21, [sp, #32]
	stp	x20, x19, [sp, #48]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w30, -48
	.cfi_offset w29, -64
	sub	sp, sp, #768
	.cfi_def_cfa_offset 832
	.cfi_remember_state
	mov	x21, x2
	mov	x22, x1
	mov	x23, x0
	mov	x19, x3
	add	x0, sp, #8
	mov	x1, x23
	mov	x2, x22
	mov	x3, x21
	mov	x20, x4
	bl	_RNvNtCsemcRClSg8DH_9native_vm6verify4seed
	ldp	x8, x9, [x19]
	add	x0, sp, #8
	mov	x1, x23
	mov	x2, x22
	mov	x3, x21
	mov	x4, x20
	stp	xzr, xzr, [sp, #208]
	stp	x8, x9, [sp, #336]
	ldr	x8, [x19, #16]
	stp	xzr, xzr, [sp, #224]
	stp	xzr, xzr, [sp, #240]
	stp	xzr, xzr, [sp, #256]
	stp	xzr, xzr, [sp, #272]
	stp	xzr, xzr, [sp, #288]
	stp	xzr, xzr, [sp, #304]
	stp	x8, xzr, [sp, #352]
	stp	xzr, xzr, [sp, #368]
	stp	xzr, xzr, [sp, #384]
	stp	xzr, xzr, [sp, #400]
	stp	xzr, xzr, [sp, #416]
	stp	xzr, xzr, [sp, #432]
	stp	xzr, xzr, [sp, #448]
	stp	xzr, xzr, [sp, #464]
	stp	xzr, xzr, [sp, #480]
	stp	xzr, xzr, [sp, #496]
	str	xzr, [sp, #512]
	str	xzr, [sp, #520]
	str	xzr, [sp, #528]
	str	xzr, [sp, #536]
	str	xzr, [sp, #544]
	str	xzr, [sp, #552]
	str	xzr, [sp, #560]
	str	xzr, [sp, #568]
	str	xzr, [sp, #576]
	str	xzr, [sp, #584]
	str	xzr, [sp, #592]
	str	xzr, [sp, #600]
	str	xzr, [sp, #608]
	str	xzr, [sp, #616]
	str	xzr, [sp, #624]
	str	xzr, [sp, #632]
	str	xzr, [sp, #640]
	str	xzr, [sp, #648]
	str	xzr, [sp, #656]
	str	xzr, [sp, #664]
	str	xzr, [sp, #672]
	str	xzr, [sp, #680]
	str	xzr, [sp, #688]
	str	xzr, [sp, #696]
	str	xzr, [sp, #704]
	str	xzr, [sp, #712]
	str	xzr, [sp, #720]
	str	xzr, [sp, #728]
	str	xzr, [sp, #736]
	str	xzr, [sp, #744]
	str	xzr, [sp, #752]
	str	xzr, [sp, #760]
	bl	_RNvNtCsemcRClSg8DH_9native_vm6verify16verify_execution
	cbz	w0, .LBB131_5
	ldr	x9, [x19, #8]
	ldr	x8, [sp, #360]
	cbz	x9, .LBB131_3
	ldr	x9, [x19]
	ldr	x9, [x9]
.LBB131_3:
	cmp	x8, x9
	b.ne	.LBB131_6
	ldr	x20, [sp, #368]
	mov	x0, x19
	bl	_RNvMNtCsemcRClSg8DH_9native_vm5inputNtB2_7Decoded11phase_count
	cmp	x20, x0
	cset	w0, eq
.LBB131_5:
	add	sp, sp, #768
	.cfi_def_cfa_offset 64
	ldp	x20, x19, [sp, #48]
	ldp	x22, x21, [sp, #32]
	ldp	x30, x23, [sp, #16]
	ldr	x29, [sp], #64
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w30
	.cfi_restore w29
	ret
.LBB131_6:
	.cfi_restore_state
	mov	w0, wzr
	add	sp, sp, #768
	.cfi_def_cfa_offset 64
	ldp	x20, x19, [sp, #48]
	ldp	x22, x21, [sp, #32]
	ldp	x30, x23, [sp, #16]
	ldr	x29, [sp], #64
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w30
	.cfi_restore w29
	ret
.Lfunc_end131:
	.size	_RNvNtCsemcRClSg8DH_9native_vm6verify6verify, .Lfunc_end131-_RNvNtCsemcRClSg8DH_9native_vm6verify6verify
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word,"ax",@progbits
	.p2align	2
	.type	_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word,@function
_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word:
.Lfunc_begin132:
	.cfi_startproc
	cbz	x2, .LBB132_4
	subs	x9, x2, #1
	b.eq	.LBB132_5
	sub	x8, x2, #2
	cmp	x8, x1
	b.hs	.LBB132_8
	add	x8, x0, x8, lsl #3
	ldrb	w8, [x8, #7]
	cmp	x9, x1
	b.lo	.LBB132_6
	b	.LBB132_7
.LBB132_4:
	mov	x0, #25964
	movk	x0, #28257, lsl #16
	movk	x0, #28022, lsl #32
	movk	x0, #30253, lsl #48
	ret
.LBB132_5:
	mov	w8, #49
	cmp	x9, x1
	b.hs	.LBB132_7
.LBB132_6:
	ldr	x9, [x0, x9, lsl #3]
	orr	x8, x8, x9, lsl #8
.LBB132_7:
	mov	x0, x8
	ret
.LBB132_8:
	mov	x8, xzr
	cmp	x9, x1
	b.lo	.LBB132_6
	b	.LBB132_7
.Lfunc_end132:
	.size	_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word, .Lfunc_end132-_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word
	.cfi_endproc

	.section	.text._RNvNvNtCsemcRClSg8DH_9native_vm5field4kinv2sq,"ax",@progbits
	.p2align	2
	.type	_RNvNvNtCsemcRClSg8DH_9native_vm5field4kinv2sq,@function
_RNvNvNtCsemcRClSg8DH_9native_vm5field4kinv2sq:
.Lfunc_begin133:
	.cfi_startproc
	stp	x30, x19, [sp, #-16]!
	.cfi_def_cfa_offset 16
	.cfi_offset w19, -8
	.cfi_offset w30, -16
	mov	w19, w1
.LBB133_1:
	mov	x1, x0
	bl	_RNvNtCsemcRClSg8DH_9native_vm5field4kmul
	subs	w19, w19, #1
	b.ne	.LBB133_1
	ldp	x30, x19, [sp], #16
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w30
	ret
.Lfunc_end133:
	.size	_RNvNvNtCsemcRClSg8DH_9native_vm5field4kinv2sq, .Lfunc_end133-_RNvNvNtCsemcRClSg8DH_9native_vm5field4kinv2sq
	.cfi_endproc

	.section	.text.leanvm_verify,"ax",@progbits
	.globl	leanvm_verify
	.p2align	2
	.type	leanvm_verify,@function
leanvm_verify:
.Lfunc_begin134:
	.cfi_startproc
	sub	sp, sp, #128
	.cfi_def_cfa_offset 128
	str	x30, [sp, #64]
	stp	x24, x23, [sp, #80]
	stp	x22, x21, [sp, #96]
	stp	x20, x19, [sp, #112]
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w24, -48
	.cfi_offset w30, -64
	.cfi_remember_state
	ldr	x19, [x0, #8]
	ldr	x10, [x0, #88]
	mov	w8, #61944
	ldr	x11, [x0, #72]
	ldr	x20, [x0, #24]
	lsr	x9, x19, #3
	cmp	x10, x8
	mov	w8, #536870910
	orr	x9, x9, #0x1
	add	x9, x9, #96, lsl #12
	add	x21, x9, #2073
	and	x9, x19, #0xffffffff00000000
	ccmp	x11, x21, #0, hs
	ccmp	x20, x8, #2, hs
	ccmp	x9, #0, #0, ls
	b.eq	.LBB134_3
.LBB134_1:
	mov	x8, xzr
.LBB134_2:
	ldp	x20, x19, [sp, #112]
	mov	x0, x8
	ldp	x22, x21, [sp, #96]
	ldr	x30, [sp, #64]
	ldp	x24, x23, [sp, #80]
	add	sp, sp, #128
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w30
	ret
.LBB134_3:
	.cfi_restore_state
	ldr	x23, [x0, #64]
	mov	x8, xzr
	cbz	x23, .LBB134_2
	and	x9, x23, #0x7
	cbnz	x9, .LBB134_2
	ldr	x22, [x0, #80]
	mov	x8, xzr
	cbz	x22, .LBB134_2
	and	x9, x22, #0x7
	cbnz	x9, .LBB134_2
	ldp	x13, x12, [x0, #32]
	ldr	x9, [x0]
	ldp	x11, x10, [x0, #48]
	ldr	x24, [x0, #16]
	cbz	x20, .LBB134_10
	mov	x8, xzr
	cbz	x24, .LBB134_2
	and	x14, x24, #0x7
	cbnz	x14, .LBB134_2
.LBB134_10:
	cbz	x19, .LBB134_13
	cbz	x9, .LBB134_1
	mov	x0, x9
	mov	x1, x19
	mov	x2, x23
	mov	x3, x21
	mov	x4, x22
	stp	x13, x12, [sp, #8]
	stp	x11, x10, [sp, #24]
	bl	_RNvNtCsemcRClSg8DH_9native_vm4wire6decode
	cbz	w0, .LBB134_1
	b	.LBB134_14
.LBB134_13:
	mov	w0, #1
	mov	x1, xzr
	mov	x2, x23
	mov	x3, x21
	mov	x4, x22
	stp	x13, x12, [sp, #8]
	stp	x11, x10, [sp, #24]
	bl	_RNvNtCsemcRClSg8DH_9native_vm4wire6decode
	tbz	w0, #0, .LBB134_1
.LBB134_14:
	cmp	x20, #0
	mov	w8, #8
	add	x2, sp, #8
	csel	x0, x8, x24, eq
	add	x3, sp, #40
	mov	x1, x20
	mov	x4, x22
	stp	x23, x21, [sp, #40]
	str	x19, [sp, #56]
	bl	_RNvNtCsemcRClSg8DH_9native_vm6verify6verify
	mov	w8, w0
	b	.LBB134_2
.Lfunc_end134:
	.size	leanvm_verify, .Lfunc_end134-leanvm_verify
	.cfi_endproc

	.section	.text.memcpy,"ax",@progbits
	.globl	memcpy
	.p2align	2
	.type	memcpy,@function
memcpy:
.Lfunc_begin135:
	.cfi_startproc
	orr	w8, w1, w0
	orr	w8, w8, w2
	tst	x8, #0x7
	b.eq	.LBB135_4
	cbz	x2, .LBB135_7
	mov	x8, x0
.LBB135_3:
	ldrb	w9, [x1], #1
	subs	x2, x2, #1
	strb	w9, [x8], #1
	//APP
	//NO_APP
	b.ne	.LBB135_3
	b	.LBB135_7
.LBB135_4:
	cbz	x2, .LBB135_7
	mov	x8, xzr
.LBB135_6:
	ldr	x9, [x1, x8]
	str	x9, [x0, x8]
	add	x8, x8, #8
	//APP
	//NO_APP
	cmp	x8, x2
	b.lo	.LBB135_6
.LBB135_7:
	ret
.Lfunc_end135:
	.size	memcpy, .Lfunc_end135-memcpy
	.cfi_endproc

	.section	.text.memset,"ax",@progbits
	.globl	memset
	.p2align	2
	.type	memset,@function
memset:
.Lfunc_begin136:
	.cfi_startproc
	orr	w8, w2, w0
	tst	x8, #0x7
	b.eq	.LBB136_4
	cbz	x2, .LBB136_7
	mov	x8, x0
.LBB136_3:
	subs	x2, x2, #1
	strb	w1, [x8], #1
	//APP
	//NO_APP
	b.ne	.LBB136_3
	b	.LBB136_7
.LBB136_4:
	cbz	x2, .LBB136_7
	and	w8, w1, #0xff
	mov	x9, #72340172838076673
	mul	x8, x8, x9
	mov	x9, xzr
.LBB136_6:
	str	x8, [x0, x9]
	add	x9, x9, #8
	//APP
	//NO_APP
	cmp	x9, x2
	b.lo	.LBB136_6
.LBB136_7:
	ret
.Lfunc_end136:
	.size	memset, .Lfunc_end136-memset
	.cfi_endproc

	.type	.Lanon.a75d6d9e6a8990b4224ef13f18552af8.0,@object
	.section	.rodata..Lanon.a75d6d9e6a8990b4224ef13f18552af8.0,"a",@progbits
	.p2align	3, 0x0
.Lanon.a75d6d9e6a8990b4224ef13f18552af8.0:
	.asciz	"\001\000\000\000\000\000\000\000\377\377\377\377\377\177\000\000\351t:\235N'\000\000\247\323\351t:\035\000\000\271\\.\227\313e\000\000\227\313\345r\271\\\000\000!\315\307\256\220f\000\000\037\273B\232\217]\000\000\220\346cWHs\000\000\241n|\226P7\000\000\237%\324\215\317\022\000\000P7>K\250\033\000\000\241\025\367\311\320\n\000\000\237\f\255\270O\006\000\000\320\212\373dhE\000\000\000\000\000\000\000@\000"
	.size	.Lanon.a75d6d9e6a8990b4224ef13f18552af8.0, 128

	.type	.Lanon.a75d6d9e6a8990b4224ef13f18552af8.1,@object
	.section	.rodata..Lanon.a75d6d9e6a8990b4224ef13f18552af8.1,"a",@progbits
	.p2align	3, 0x0
.Lanon.a75d6d9e6a8990b4224ef13f18552af8.1:
	.ascii	"\001\000\000\000\000\000\000\000\202\200\000\000\000\000\000\000\212\200\000\000\000\000\000\200\000\200\000\200\000\000\000\200\213\200\000\000\000\000\000\000\001\000\000\200\000\000\000\000\201\200\000\200\000\000\000\200\t\200\000\000\000\000\000\200\212\000\000\000\000\000\000\000\210\000\000\000\000\000\000\000\t\200\000\200\000\000\000\000\n\000\000\200\000\000\000\000\213\200\000\200\000\000\000\000\213\000\000\000\000\000\000\200\211\200\000\000\000\000\000\200\003\200\000\000\000\000\000\200\002\200\000\000\000\000\000\200\200\000\000\000\000\000\000\200\n\200\000\000\000\000\000\000\n\000\000\200\000\000\000\200\201\200\000\200\000\000\000\200\200\200\000\000\000\000\000\200\001\000\000\200\000\000\000\000\b\200\000\200\000\000\000\200"
	.size	.Lanon.a75d6d9e6a8990b4224ef13f18552af8.1, 192

	.type	.Lanon.a75d6d9e6a8990b4224ef13f18552af8.2,@object
	.section	.rodata..Lanon.a75d6d9e6a8990b4224ef13f18552af8.2,"a",@progbits
	.p2align	2, 0x0
.Lanon.a75d6d9e6a8990b4224ef13f18552af8.2:
	.asciz	"\000\000\000\000\001\000\000\000>\000\000\000\034\000\000\000\033\000\000\000$\000\000\000,\000\000\000\006\000\000\0007\000\000\000\024\000\000\000\003\000\000\000\n\000\000\000+\000\000\000\031\000\000\000'\000\000\000)\000\000\000-\000\000\000\017\000\000\000\025\000\000\000\b\000\000\000\022\000\000\000\002\000\000\000=\000\000\0008\000\000\000\016\000\000"
	.size	.Lanon.a75d6d9e6a8990b4224ef13f18552af8.2, 100

	.type	.Lanon.a75d6d9e6a8990b4224ef13f18552af8.3,@object
	.section	.rodata..Lanon.a75d6d9e6a8990b4224ef13f18552af8.3,"a",@progbits
	.p2align	3, 0x0
.Lanon.a75d6d9e6a8990b4224ef13f18552af8.3:
	.asciz	"\000\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000\t\000\000\000\000\000\000\000\f\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\021\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\026\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\033\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000\036\000\000\000\000\000\000\000\t\000\000\000\000\000\000\000'\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000,\000\000\000\000\000\000\000\005\000\000\000\000\000\000\0001\000\000\000\000\000\000\000\005\000\000\000\000\000\000\0006\000\000\000\000\000\000\000\001\000\000\000\000\000\000\0007\000\000\000\000\000\000\000\001\000\000\000\000\000\000\0008\000\000\000\000\000\000\000\001\000\000\000\000\000\000\0009\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000:\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000=\000\000\000\000\000\000\000\t\000\000\000\000\000\000\000F\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000K\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000P\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000U\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000X\000\000\000\000\000\000\000\t\000\000\000\000\000\000\000a\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000f\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000k\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000p\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000q\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000r\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000s\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000t\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000w\000\000\000\000\000\000\000\t\000\000\000\000\000\000\000\200\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\205\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000\210\000\000\000\000\000\000\000\t\000\000\000\000\000\000\000\221\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\226\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\227\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\230\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000\233\000\000\000\000\000\000\000\t\000\000\000\000\000\000\000\244\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\251\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\256\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\263\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000\266\000\000\000\000\000\000\000\t\000\000\000\000\000\000\000\277\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\304\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\311\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\316\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\317\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\320\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\321\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\322\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000\325\000\000\000\000\000\000\000\t\000\000\000\000\000\000\000\336\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\343\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\350\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\355\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000\360\000\000\000\000\000\000\000\t\000\000\000\000\000\000\000\371\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\376\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\003\001\000\000\000\000\000\000\005\000\000\000\000\000\000\000\b\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\t\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\n\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\013\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\f\001\000\000\000\000\000\000\003\000\000\000\000\000\000\000\017\001\000\000\000\000\000\000\020\000\000\000\000\000\000\000\037\001\000\000\000\000\000\000\005\000\000\000\000\000\000\000$\001\000\000\000\000\000\000\005\000\000\000\000\000\000\000)\001\000\000\000\000\000\000\005\000\000\000\000\000\000\000.\001\000\000\000\000\000\000\005\000\000\000\000\000\000\0003\001\000\000\000\000\000\000\005\000\000\000\000\000\000\0008\001\000\000\000\000\000\000\005\000\000\000\000\000\000\000=\001\000\000\000\000\000\000\005\000\000\000\000\000\000\000B\001\000\000\000\000\000\000\005\000\000\000\000\000\000\000G\001\000\000\000\000\000\000\005\000\000\000\000\000\000\000L\001\000\000\000\000\000\000\005\000\000\000\000\000\000\000Q\001\000\000\000\000\000\000\005\000\000\000\000\000\000\000V\001\000\000\000\000\000\000\005\000\000\000\000\000\000\000[\001\000\000\000\000\000\000\005\000\000\000\000\000\000\000`\001\000\000\000\000\000\000\005\000\000\000\000\000\000\000e\001\000\000\000\000\000\000\005\000\000\000\000\000\000\000j\001\000\000\000\000\000\000\005\000\000\000\000\000\000\000o\001\000\000\000\000\000\000\005\000\000\000\000\000\000\000t\001\000\000\000\000\000\000\005\000\000\000\000\000\000\000y\001\000\000\000\000\000\000\005\000\000\000\000\000\000\000~\001\000\000\000\000\000\000\005\000\000\000\000\000\000\000\203\001\000\000\000\000\000\000\005\000\000\000\000\000\000\000\210\001\000\000\000\000\000\000\005\000\000\000\000\000\000\000\215\001\000\000\000\000\000\000\005\000\000\000\000\000\000\000\222\001\000\000\000\000\000\000\005\000\000\000\000\000\000\000\227\001\000\000\000\000\000\000\005\000\000\000\000\000\000\000\234\001\000\000\000\000\000\000\005\000\000\000\000\000\000\000\241\001\000\000\000\000\000\000\003\000\000\000\000\000\000\000\244\001\000\000\000\000\000\000\020\000\000\000\000\000\000\000\264\001\000\000\000\000\000\000\005\000\000\000\000\000\000\000\271\001\000\000\000\000\000\000\005\000\000\000\000\000\000\000\276\001\000\000\000\000\000\000\005\000\000\000\000\000\000\000\303\001\000\000\000\000\000\000\005\000\000\000\000\000\000\000\310\001\000\000\000\000\000\000\005\000\000\000\000\000\000\000\315\001\000\000\000\000\000\000\005\000\000\000\000\000\000\000\322\001\000\000\000\000\000\000\005\000\000\000\000\000\000\000\327\001\000\000\000\000\000\000\005\000\000\000\000\000\000\000\334\001\000\000\000\000\000\000\005\000\000\000\000\000\000\000\341\001\000\000\000\000\000\000\005\000\000\000\000\000\000\000\346\001\000\000\000\000\000\000\005\000\000\000\000\000\000\000\353\001\000\000\000\000\000\000\005\000\000\000\000\000\000\000\360\001\000\000\000\000\000\000\005\000\000\000\000\000\000\000\365\001\000\000\000\000\000\000\005\000\000\000\000\000\000\000\372\001\000\000\000\000\000\000\005\000\000\000\000\000\000\000\377\001\000\000\000\000\000\000\005\000\000\000\000\000\000\000\004\002\000\000\000\000\000\000\005\000\000\000\000\000\000\000\t\002\000\000\000\000\000\000\005\000\000\000\000\000\000\000\016\002\000\000\000\000\000\000\005\000\000\000\000\000\000\000\023\002\000\000\000\000\000\000\005\000\000\000\000\000\000\000\030\002\000\000\000\000\000\000\005\000\000\000\000\000\000\000\035\002\000\000\000\000\000\000\005\000\000\000\000\000\000\000\"\002\000\000\000\000\000\000\005\000\000\000\000\000\000\000'\002\000\000\000\000\000\000\005\000\000\000\000\000\000\000,\002\000\000\000\000\000\000\005\000\000\000\000\000\000\0001\002\000\000\000\000\000\000\005\000\000\000\000\000\000\0006\002\000\000\000\000\000\000\001\000\000\000\000\000\000\0007\002\000\000\000\000\000\000\001\000\000\000\000\000\000\0008\002\000\000\000\000\000\000\001\000\000\000\000\000\000\0009\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000:\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000;\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000<\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000=\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000>\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000?\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000@\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000A\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000B\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000C\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000D\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000E\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000F\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000G\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000H\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000I\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000J\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000K\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000L\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000M\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000N\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000O\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000P\002\000\000\000\000\000\000\001\000\000\000\000\000\000"
	.size	.Lanon.a75d6d9e6a8990b4224ef13f18552af8.3, 2352

	.type	.Lanon.a75d6d9e6a8990b4224ef13f18552af8.4,@object
	.section	.rodata..Lanon.a75d6d9e6a8990b4224ef13f18552af8.4,"a",@progbits
	.p2align	3, 0x0
.Lanon.a75d6d9e6a8990b4224ef13f18552af8.4:
	.asciz	"\000\000\000\000\000\000\000\000\r\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\r\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\r\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\r\000\000\000\000\000\000\000\r\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\007\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\032\000\000\000\000\000\000\000\007\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000\016\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000!\000\000\000\000\000\000\000\016\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000\016\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000/\000\000\000\000\000\000\000\016\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000=\000\000\000\000\000\000\000\\\000\000\000\000\000\000"
	.size	.Lanon.a75d6d9e6a8990b4224ef13f18552af8.4, 240

	.type	.Lanon.a75d6d9e6a8990b4224ef13f18552af8.5,@object
	.section	.rodata..Lanon.a75d6d9e6a8990b4224ef13f18552af8.5,"a",@progbits
	.p2align	3, 0x0
.Lanon.a75d6d9e6a8990b4224ef13f18552af8.5:
	.asciz	"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\347\335\341@y\217%\361\000\000\000\000\000\000\000\000\212G\3003\371\314\325\204\000\000\000\000\000\000\000\000\356\251Z\246\036&\230\325\000\000\000\000\000\000\000\000MI\200o0G\025\275\000\000\000\000\000\000\000\000W\320Sb\005N(\213\000\000\000\000\000\000\000\000\324o\216\177-\244\227\377\000\000\000\000\000\000\000\000\304GF\244\240\345\376\220\000\000\000\000\000\000\000\000v.\031\326\f\332[\214\000\000\000\000\000\000\000\000\234\005\031\033\367\2460\255\000\000\000\000\000\000\000\000d\374\217\320\267Z\2230\000\000\000\000\000\000\000\0005\326\027#?\251Z\353\000\000\000\000\000\000\000\000\003!q\r&\346\246\251\000\000\000\000\000\000\000\000_U\317\333\026|\245\201\000\000\000\000\000\000\000\000&\310G\003\3151\270C\000\000\000\000\000\000\000\000\237V\245\021\032/\362\001\000\000\000\000\000\000\000\000a\256\331!Zc\345\005\000\000\000\000\000\000\000\000\362p\311\214\362\376\276d\000\000\000\000\000\000\000\000\021f\304{\225p6a\000\000\000\000\000\000\000\000\313\016\320OUZ|\270\000\000\000\000\000\000\000\000\3102\317\034\212\350>\214\000\000\000\000\000\000\000\000\024&:\256\"y\f\224\000\000\000\000\000\000\000\000\344\t\305\242$\371A\030\000\000\000\000\000\000\000\000\302e\004\347&5\365\026\000\000\000\000\000\000\000\000;\2410\177\351D\366u\000\000\000\000\000\000\000\000I\242\354\\{\377\361\352\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000"
	.size	.Lanon.a75d6d9e6a8990b4224ef13f18552af8.5, 2448

	.type	.Lanon.a75d6d9e6a8990b4224ef13f18552af8.6,@object
	.section	.rodata..Lanon.a75d6d9e6a8990b4224ef13f18552af8.6,"a",@progbits
	.p2align	3, 0x0
.Lanon.a75d6d9e6a8990b4224ef13f18552af8.6:
	.asciz	"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\016\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\017\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\020\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\021\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\022\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\034\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\035\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\036\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000$\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000%\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000&\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000'\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000(\000\000\000\000\000\000\000\004\000\000\000\000\000\000\0002\000\000\000\000\000\000\000\004\000\000\000\000\000\000\0003\000\000\000\000\000\000\000\004\000\000\000\000\000\000\0004\000\000\000\000\000\000\000\004\000\000\000\000\000\000\0005\000\000\000\000\000\000\000\004\000\000\000\000\000\000\0006\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000@\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000A\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000B\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000C\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000D\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000E\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000F\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000G\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000H\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000I\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000J\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000K\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000L\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000M\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000N\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000O\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000P\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000Q\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000R\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000S\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000T\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000U\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000V\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000W\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000X\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000Y\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000Z\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000[\000\000\000\000\000\000"
	.size	.Lanon.a75d6d9e6a8990b4224ef13f18552af8.6, 816

	.type	.Lanon.a75d6d9e6a8990b4224ef13f18552af8.7,@object
	.section	.rodata..Lanon.a75d6d9e6a8990b4224ef13f18552af8.7,"a",@progbits
	.p2align	3, 0x0
.Lanon.a75d6d9e6a8990b4224ef13f18552af8.7:
	.asciz	"\000\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\006\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\007\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\b\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\t\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\023\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\024\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\025\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\026\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\027\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\037\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000 \000\000\000\000\000\000\000\002\000\000\000\000\000\000\000!\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000)\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000*\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000+\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000,\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000-\000\000\000\000\000\000\000\004\000\000\000\000\000\000\0007\000\000\000\000\000\000\000\004\000\000\000\000\000\000\0008\000\000\000\000\000\000\000\004\000\000\000\000\000\000\0009\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000:\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000;\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\\\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000]\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000^\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000_\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000`\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000a\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000b\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000c\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000d\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000e\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000f\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000g\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000h\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000i\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000j\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000k\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000l\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000m\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000n\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000o\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000p\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000q\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000r\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000s\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000t\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000u\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000v\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000w\000\000\000\000\000\000"
	.size	.Lanon.a75d6d9e6a8990b4224ef13f18552af8.7, 816

	.type	.Lanon.a75d6d9e6a8990b4224ef13f18552af8.8,@object
	.section	.rodata..Lanon.a75d6d9e6a8990b4224ef13f18552af8.8,"a",@progbits
	.p2align	3, 0x0
.Lanon.a75d6d9e6a8990b4224ef13f18552af8.8:
	.asciz	"\000\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\013\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\f\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\r\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\030\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\031\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\032\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\033\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\"\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000#\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000.\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000/\000\000\000\000\000\000\000\003\000\000\000\000\000\000\0000\000\000\000\000\000\000\000\003\000\000\000\000\000\000\0001\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000<\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000=\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000>\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000?\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000x\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000y\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000z\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000{\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000|\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000}\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000~\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\177\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\200\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\201\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\202\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\203\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\204\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\205\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\206\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\207\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\210\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\211\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\212\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\213\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\214\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\215\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\216\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\217\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\220\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\221\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\222\000\000\000\000\000\000"
	.size	.Lanon.a75d6d9e6a8990b4224ef13f18552af8.8, 720

	.type	.Lanon.a75d6d9e6a8990b4224ef13f18552af8.9,@object
	.section	.rodata.cst16,"aM",@progbits,16
	.p2align	3, 0x0
.Lanon.a75d6d9e6a8990b4224ef13f18552af8.9:
	.asciz	"\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000"
	.size	.Lanon.a75d6d9e6a8990b4224ef13f18552af8.9, 16

	.type	.Lanon.a75d6d9e6a8990b4224ef13f18552af8.10,@object
	.section	.rodata..Lanon.a75d6d9e6a8990b4224ef13f18552af8.10,"a",@progbits
.Lanon.a75d6d9e6a8990b4224ef13f18552af8.10:
	.ascii	"\000\200@* \031\025\022\020\016\f\013\n\t\t\b\b\007\007\006\006\006\005\005\005\005\004\004\004\004\004\004\004\003\003\003\003\003\003\003\003\003\003\002\002\002\002\002\002\002\002\002\002\002\002\002\002\002\002\002\002\002\002\002\002\001\001\001\001\001\001\001\001\001\001\001\001\001\001\001\001\001\001\001\001\001\001\001\001\001\001\001\001\001\001\001\001\001\001\001\001\001\001\001\001\001\001\001\001\001\001\001\001\001\001\001\001\001\001\001\001\001\001\001\001\001\001\001\001"
	.size	.Lanon.a75d6d9e6a8990b4224ef13f18552af8.10, 129

	.type	.Lanon.a75d6d9e6a8990b4224ef13f18552af8.11,@object
	.section	.rodata..Lanon.a75d6d9e6a8990b4224ef13f18552af8.11,"a",@progbits
	.p2align	3, 0x0
.Lanon.a75d6d9e6a8990b4224ef13f18552af8.11:
	.asciz	"\346\000\000\000\000\000\000\000<\000\000\000\000\000\000\000*\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\341\000\000\000\000\000\000\000:\000\000\000\000\000\000\000&\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\336\000\000\000\000\000\000\0009\000\000\000\000\000\000\000#\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\334\000\000\000\000\000\000\0008\000\000\000\000\000\000\000\"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\333\000\000\000\000\000\000\0007\000\000\000\000\000\000\000!\000\000\000\000\000\000\000\033\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\332\000\000\000\000\000\000\0007\000\000\000\000\000\000\000 \000\000\000\000\000\000\000\031\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\332\000\000\000\000\000\000\0007\000\000\000\000\000\000\000 \000\000\000\000\000\000\000\030\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\332\000\000\000\000\000\000\0007\000\000\000\000\000\000\000 \000\000\000\000\000\000\000\027\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\332\000\000\000\000\000\000\0007\000\000\000\000\000\000\000 \000\000\000\000\000\000\000\027\000\000\000\000\000\000\000\024\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\332\000\000\000\000\000\000\0007\000\000\000\000\000\000\000 \000\000\000\000\000\000\000\027\000\000\000\000\000\000\000\023\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\332\000\000\000\000\000\000\0007\000\000\000\000\000\000\000 \000\000\000\000\000\000\000\027\000\000\000\000\000\000\000\022\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\332\000\000\000\000\000\000\0007\000\000\000\000\000\000\000 \000\000\000\000\000\000\000\027\000\000\000\000\000\000\000\022\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\332\000\000\000\000\000\000\0007\000\000\000\000\000\000\000 \000\000\000\000\000\000\000\027\000\000\000\000\000\000\000\022\000\000\000\000\000\000\000\020\000\000\000\000\000\000\000\332\000\000\000\000\000\000\0007\000\000\000\000\000\000\000 \000\000\000\000\000\000\000\027\000\000\000\000\000\000\000\022\000\000\000\000\000\000\000\017\000\000\000\000\000\000\000\332\000\000\000\000\000\000\0007\000\000\000\000\000\000\000 \000\000\000\000\000\000\000\027\000\000\000\000\000\000\000\022\000\000\000\000\000\000\000\017\000\000\000\000\000\000\000p\000\000\000\000\000\000\000/\000\000\000\000\000\000\000#\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000o\000\000\000\000\000\000\000.\000\000\000\000\000\000\000 \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000n\000\000\000\000\000\000\000-\000\000\000\000\000\000\000\037\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000n\000\000\000\000\000\000\000-\000\000\000\000\000\000\000\035\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000m\000\000\000\000\000\000\000,\000\000\000\000\000\000\000\035\000\000\000\000\000\000\000\030\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000m\000\000\000\000\000\000\000,\000\000\000\000\000\000\000\034\000\000\000\000\000\000\000\027\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000m\000\000\000\000\000\000\000,\000\000\000\000\000\000\000\034\000\000\000\000\000\000\000\026\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000m\000\000\000\000\000\000\000,\000\000\000\000\000\000\000\034\000\000\000\000\000\000\000\025\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000m\000\000\000\000\000\000\000,\000\000\000\000\000\000\000\034\000\000\000\000\000\000\000\025\000\000\000\000\000\000\000\022\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000m\000\000\000\000\000\000\000,\000\000\000\000\000\000\000\034\000\000\000\000\000\000\000\025\000\000\000\000\000\000\000\021\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000m\000\000\000\000\000\000\000,\000\000\000\000\000\000\000\034\000\000\000\000\000\000\000\025\000\000\000\000\000\000\000\021\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000m\000\000\000\000\000\000\000,\000\000\000\000\000\000\000\034\000\000\000\000\000\000\000\025\000\000\000\000\000\000\000\021\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000m\000\000\000\000\000\000\000,\000\000\000\000\000\000\000\034\000\000\000\000\000\000\000\025\000\000\000\000\000\000\000\021\000\000\000\000\000\000\000\017\000\000\000\000\000\000\000m\000\000\000\000\000\000\000,\000\000\000\000\000\000\000\034\000\000\000\000\000\000\000\025\000\000\000\000\000\000\000\021\000\000\000\000\000\000\000\017\000\000\000\000\000\000\000m\000\000\000\000\000\000\000,\000\000\000\000\000\000\000\034\000\000\000\000\000\000\000\025\000\000\000\000\000\000\000\021\000\000\000\000\000\000\000\017\000\000\000\000\000\000\000J\000\000\000\000\000\000\000'\000\000\000\000\000\000\000\036\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000J\000\000\000\000\000\000\000&\000\000\000\000\000\000\000\034\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000I\000\000\000\000\000\000\000%\000\000\000\000\000\000\000\033\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000I\000\000\000\000\000\000\000%\000\000\000\000\000\000\000\032\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000I\000\000\000\000\000\000\000%\000\000\000\000\000\000\000\031\000\000\000\000\000\000\000\026\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000I\000\000\000\000\000\000\000%\000\000\000\000\000\000\000\031\000\000\000\000\000\000\000\024\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000I\000\000\000\000\000\000\000%\000\000\000\000\000\000\000\031\000\000\000\000\000\000\000\024\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000I\000\000\000\000\000\000\000%\000\000\000\000\000\000\000\031\000\000\000\000\000\000\000\023\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000I\000\000\000\000\000\000\000%\000\000\000\000\000\000\000\031\000\000\000\000\000\000\000\023\000\000\000\000\000\000\000\021\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000I\000\000\000\000\000\000\000%\000\000\000\000\000\000\000\031\000\000\000\000\000\000\000\023\000\000\000\000\000\000\000\020\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000I\000\000\000\000\000\000\000%\000\000\000\000\000\000\000\031\000\000\000\000\000\000\000\023\000\000\000\000\000\000\000\020\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000I\000\000\000\000\000\000\000%\000\000\000\000\000\000\000\031\000\000\000\000\000\000\000\023\000\000\000\000\000\000\000\020\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000I\000\000\000\000\000\000\000%\000\000\000\000\000\000\000\031\000\000\000\000\000\000\000\023\000\000\000\000\000\000\000\020\000\000\000\000\000\000\000\017\000\000\000\000\000\000\000I\000\000\000\000\000\000\000%\000\000\000\000\000\000\000\031\000\000\000\000\000\000\000\023\000\000\000\000\000\000\000\020\000\000\000\000\000\000\000\016\000\000\000\000\000\000\000I\000\000\000\000\000\000\000%\000\000\000\000\000\000\000\031\000\000\000\000\000\000\000\023\000\000\000\000\000\000\000\020\000\000\000\000\000\000\000\017\000\000\000\000\000\000\0008\000\000\000\000\000\000\000!\000\000\000\000\000\000\000\033\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\0007\000\000\000\000\000\000\000 \000\000\000\000\000\000\000\031\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\0007\000\000\000\000\000\000\000 \000\000\000\000\000\000\000\030\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\0007\000\000\000\000\000\000\000 \000\000\000\000\000\000\000\027\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\0007\000\000\000\000\000\000\000 \000\000\000\000\000\000\000\027\000\000\000\000\000\000\000\024\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\0007\000\000\000\000\000\000\000 \000\000\000\000\000\000\000\027\000\000\000\000\000\000\000\023\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\0007\000\000\000\000\000\000\000 \000\000\000\000\000\000\000\027\000\000\000\000\000\000\000\022\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\0007\000\000\000\000\000\000\000 \000\000\000\000\000\000\000\027\000\000\000\000\000\000\000\022\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\0007\000\000\000\000\000\000\000 \000\000\000\000\000\000\000\027\000\000\000\000\000\000\000\022\000\000\000\000\000\000\000\020\000\000\000\000\000\000\000\000\000\000\000\000\000\000\0007\000\000\000\000\000\000\000 \000\000\000\000\000\000\000\027\000\000\000\000\000\000\000\022\000\000\000\000\000\000\000\017\000\000\000\000\000\000\000\000\000\000\000\000\000\000\0007\000\000\000\000\000\000\000 \000\000\000\000\000\000\000\027\000\000\000\000\000\000\000\022\000\000\000\000\000\000\000\017\000\000\000\000\000\000\000\000\000\000\000\000\000\000\0007\000\000\000\000\000\000\000 \000\000\000\000\000\000\000\027\000\000\000\000\000\000\000\022\000\000\000\000\000\000\000\017\000\000\000\000\000\000\000\000\000\000\000\000\000\000\0007\000\000\000\000\000\000\000 \000\000\000\000\000\000\000\027\000\000\000\000\000\000\000\022\000\000\000\000\000\000\000\017\000\000\000\000\000\000\000\016\000\000\000\000\000\000\0007\000\000\000\000\000\000\000 \000\000\000\000\000\000\000\027\000\000\000\000\000\000\000\022\000\000\000\000\000\000\000\020\000\000\000\000\000\000\000\016\000\000\000\000\000\000\0007\000\000\000\000\000\000\000 \000\000\000\000\000\000\000\027\000\000\000\000\000\000\000\022\000\000\000\000\000\000\000\020\000\000\000\000\000\000\000\016\000\000\000\000\000\000"
	.size	.Lanon.a75d6d9e6a8990b4224ef13f18552af8.11, 2880

	.type	.Lanon.a75d6d9e6a8990b4224ef13f18552af8.12,@object
	.section	.rodata..Lanon.a75d6d9e6a8990b4224ef13f18552af8.12,"a",@progbits
	.p2align	3, 0x0
.Lanon.a75d6d9e6a8990b4224ef13f18552af8.12:
	.asciz	"\003\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\006\000\000\000\000\000\000\000\006\000\000\000\000\000\000\000\006\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\006\000\000\000\000\000\000\000\006\000\000\000\000\000\000\000\006\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\006\000\000\000\000\000\000\000\006\000\000\000\000\000\000\000\006\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\006\000\000\000\000\000\000\000\006\000\000\000\000\000\000\000\006\000\000\000\000\000\000"
	.size	.Lanon.a75d6d9e6a8990b4224ef13f18552af8.12, 480

	.type	.Lanon.a75d6d9e6a8990b4224ef13f18552af8.13,@object
	.section	.rodata..Lanon.a75d6d9e6a8990b4224ef13f18552af8.13,"a",@progbits
	.p2align	3, 0x0
.Lanon.a75d6d9e6a8990b4224ef13f18552af8.13:
	.asciz	"\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\006\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\007\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\b\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\t\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\013\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\f\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\r\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\016\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\017\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\020\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\021\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\022\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\023\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\024\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\025\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\026\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\027\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\030\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\031\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\033\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\035\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\036\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\037\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000 \000\000\000\000\000\000\000\001\000\000\000\000\000\000\000!\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\"\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000#\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000$\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000%\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000&\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000'\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000(\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000)\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000*\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000+\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000,\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000-\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000.\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000/\000\000\000\000\000\000\000\001\000\000\000\000\000\000\0000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\0001\000\000\000\000\000\000\000\001\000\000\000\000\000\000\0002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\0003\000\000\000\000\000\000\000\001\000\000\000\000\000\000\0004\000\000\000\000\000\000\000\001\000\000\000\000\000\000\0005\000\000\000\000\000\000\000\001\000\000\000\000\000\000\0006\000\000\000\000\000\000\000\002\000\000\000\000\000\000\0008\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000:\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000;\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000<\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000=\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000>\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000?\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000@\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000A\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000B\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000C\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000D\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000E\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000F\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000G\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000H\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000I\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000J\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000K\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000L\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000M\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000N\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000O\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000P\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000Q\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000R\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000S\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000T\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000U\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000V\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000W\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000Y\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000\\\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000]\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000^\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000_\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000`\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000a\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000b\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000c\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000d\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000e\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000f\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000g\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000h\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000i\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000j\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000k\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000l\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000m\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000n\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000o\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000p\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000q\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000r\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000s\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000t\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000u\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000w\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000z\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000{\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000|\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000}\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000~\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\177\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\200\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\201\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\202\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\203\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\204\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\205\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\206\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\207\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\210\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\211\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\212\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\213\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\214\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\215\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\216\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\217\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\220\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\221\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\222\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\223\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\224\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\225\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\226\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\227\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\230\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\231\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\232\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\233\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\234\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\235\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\236\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\237\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\240\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\241\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\242\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\243\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\244\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\245\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\246\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\247\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\250\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\251\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\252\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\253\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\254\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\255\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\256\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\257\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\260\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\261\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\262\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\263\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\264\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\265\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\266\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\273\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000\276\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\277\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\300\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\301\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\302\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\303\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\304\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\305\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\306\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\307\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\310\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\311\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\312\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\313\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\314\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\315\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\316\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\317\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\320\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\321\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\322\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\323\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\324\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\325\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\326\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\327\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\334\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000\337\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\340\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\341\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\342\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\343\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\344\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\345\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\346\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\347\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\350\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\351\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000\354\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000\357\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\360\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\361\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\362\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\363\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\364\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\365\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\366\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\367\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\370\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\371\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\372\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\373\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\374\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\375\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\376\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\377\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\001\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\002\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\003\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\004\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\005\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\006\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\007\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\b\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\t\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\n\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\013\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\f\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\r\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\016\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\017\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\020\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\021\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\022\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\023\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\024\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\025\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\026\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\027\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\030\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\031\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\032\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\033\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\034\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\035\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\036\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\037\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000 \001\000\000\000\000\000\000\001\000\000\000\000\000\000\000!\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\"\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000#\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000$\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000%\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000&\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000'\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000(\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000)\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000*\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000+\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000,\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000-\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000.\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000/\001\000\000\000\000\000\000\001\000\000\000\000\000\000\0000\001\000\000\000\000\000\000\001\000\000\000\000\000\000\0001\001\000\000\000\000\000\000\001\000\000\000\000\000\000\0002\001\000\000\000\000\000\000\001\000\000\000\000\000\000\0003\001\000\000\000\000\000\000\001\000\000\000\000\000\000\0004\001\000\000\000\000\000\000\001\000\000\000\000\000\000\0005\001\000\000\000\000\000\000\001\000\000\000\000\000\000\0006\001\000\000\000\000\000\000\001\000\000\000\000\000\000\0007\001\000\000\000\000\000\000\001\000\000\000\000\000\000\0008\001\000\000\000\000\000\000\001\000\000\000\000\000\000\0009\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000:\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000;\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000<\001\000\000\000\000\000\000\003\000\000\000\000\000\000\000?\001\000\000\000\000\000\000\003\000\000\000\000\000\000\000B\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000C\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000D\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000E\001\000\000\000\000\000\000\003\000\000\000\000\000\000\000H\001\000\000\000\000\000\000\003\000\000\000\000\000\000\000K\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000L\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000M\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000N\001\000\000\000\000\000\000\003\000\000\000\000\000\000\000Q\001\000\000\000\000\000\000\003\000\000\000\000\000\000\000T\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000U\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000V\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000W\001\000\000\000\000\000\000\003\000\000\000\000\000\000\000Z\001\000\000\000\000\000\000\003\000\000\000\000\000\000\000]\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000^\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000_\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000`\001\000\000\000\000\000\000\003\000\000\000\000\000\000\000c\001\000\000\000\000\000\000\003\000\000\000\000\000\000\000f\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000g\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000h\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000i\001\000\000\000\000\000\000\003\000\000\000\000\000\000\000l\001\000\000\000\000\000\000\003\000\000\000\000\000\000\000o\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000p\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000q\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000r\001\000\000\000\000\000\000\003\000\000\000\000\000\000\000u\001\000\000\000\000\000\000\003\000\000\000\000\000\000\000x\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000y\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000z\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000{\001\000\000\000\000\000\000\003\000\000\000\000\000\000\000~\001\000\000\000\000\000\000\003\000\000\000\000\000\000\000\201\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\202\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\203\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\204\001\000\000\000\000\000\000\003\000\000\000\000\000\000\000\207\001\000\000\000\000\000\000\003\000\000\000\000\000\000\000\212\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\213\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\214\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\215\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\216\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\217\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\220\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\221\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\222\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\223\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\224\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\225\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\226\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\227\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\230\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\231\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\232\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\233\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\234\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\235\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\236\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\237\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\240\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\241\001\000\000\000\000\000\000\002\000\000\000\000\000\000\000\243\001\000\000\000\000\000\000\003\000\000\000\000\000\000\000\246\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\247\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\250\001\000\000\000\000\000\000\002\000\000\000\000\000\000\000\252\001\000\000\000\000\000\000\003\000\000\000\000\000\000\000\255\001\000\000\000\000\000\000\003\000\000\000\000\000\000\000\260\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\261\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\262\001\000\000\000\000\000\000\002\000\000\000\000\000\000\000\264\001\000\000\000\000\000\000\003\000\000\000\000\000\000\000\267\001\000\000\000\000\000\000\003\000\000\000\000\000\000\000\272\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\273\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\274\001\000\000\000\000\000\000\002\000\000\000\000\000\000\000\276\001\000\000\000\000\000\000\003\000\000\000\000\000\000\000\301\001\000\000\000\000\000\000\003\000\000\000\000\000\000\000\304\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\305\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\306\001\000\000\000\000\000\000\002\000\000\000\000\000\000\000\310\001\000\000\000\000\000\000\003\000\000\000\000\000\000\000\313\001\000\000\000\000\000\000\003\000\000\000\000\000\000\000\316\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\317\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\320\001\000\000\000\000\000\000\002\000\000\000\000\000\000\000\322\001\000\000\000\000\000\000\003\000\000\000\000\000\000\000\325\001\000\000\000\000\000\000\003\000\000\000\000\000\000\000\330\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\331\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\332\001\000\000\000\000\000\000\002\000\000\000\000\000\000\000\334\001\000\000\000\000\000\000\003\000\000\000\000\000\000\000\337\001\000\000\000\000\000\000\003\000\000\000\000\000\000\000\342\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\343\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\344\001\000\000\000\000\000\000\002\000\000\000\000\000\000\000\346\001\000\000\000\000\000\000\003\000\000\000\000\000\000\000\351\001\000\000\000\000\000\000\003\000\000\000\000\000\000\000\354\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\355\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\356\001\000\000\000\000\000\000\002\000\000\000\000\000\000\000\360\001\000\000\000\000\000\000\003\000\000\000\000\000\000\000\363\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\364\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\365\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\366\001\000\000\000\000\000\000\002\000\000\000\000\000\000\000\370\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\371\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\372\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\373\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\374\001\000\000\000\000\000\000\002\000\000\000\000\000\000\000\376\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\377\001\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\001\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\002\002\000\000\000\000\000\000\002\000\000\000\000\000\000\000\004\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\005\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\006\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\007\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\b\002\000\000\000\000\000\000\002\000\000\000\000\000\000\000\n\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\013\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\f\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\r\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\016\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\017\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\020\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\021\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\022\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\023\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\024\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\025\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\026\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\027\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\030\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\031\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\032\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\033\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\034\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\035\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\036\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\037\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000 \002\000\000\000\000\000\000\001\000\000\000\000\000\000\000!\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\"\002\000\000\000\000\000\000\003\000\000\000\000\000\000\000%\002\000\000\000\000\000\000\003\000\000\000\000\000\000\000(\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000)\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000*\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000+\002\000\000\000\000\000\000\003\000\000\000\000\000\000\000.\002\000\000\000\000\000\000\003\000\000\000\000\000\000\0001\002\000\000\000\000\000\000\001\000\000\000\000\000\000\0002\002\000\000\000\000\000\000\001\000\000\000\000\000\000\0003\002\000\000\000\000\000\000\001\000\000\000\000\000\000\0004\002\000\000\000\000\000\000\003\000\000\000\000\000\000\0007\002\000\000\000\000\000\000\003\000\000\000\000\000\000\000:\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000;\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000<\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000=\002\000\000\000\000\000\000\003\000\000\000\000\000\000\000@\002\000\000\000\000\000\000\003\000\000\000\000\000\000\000C\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000D\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000E\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000F\002\000\000\000\000\000\000\003\000\000\000\000\000\000\000I\002\000\000\000\000\000\000\003\000\000\000\000\000\000\000L\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000M\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000N\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000O\002\000\000\000\000\000\000\003\000\000\000\000\000\000\000R\002\000\000\000\000\000\000\003\000\000\000\000\000\000\000U\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000V\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000W\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000X\002\000\000\000\000\000\000\003\000\000\000\000\000\000\000[\002\000\000\000\000\000\000\003\000\000\000\000\000\000\000^\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000_\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000`\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000a\002\000\000\000\000\000\000\003\000\000\000\000\000\000\000d\002\000\000\000\000\000\000\003\000\000\000\000\000\000\000g\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000h\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000i\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000j\002\000\000\000\000\000\000\003\000\000\000\000\000\000\000m\002\000\000\000\000\000\000\003\000\000\000\000\000\000\000p\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000q\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000r\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000s\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000t\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000u\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000v\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000w\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000x\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000y\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000z\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000{\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000|\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000}\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000~\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\177\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\200\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\201\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\202\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\203\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\204\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\205\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\206\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\207\002\000\000\000\000\000\000\002\000\000\000\000\000\000\000\211\002\000\000\000\000\000\000\003\000\000\000\000\000\000\000\214\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\215\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\216\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\217\002\000\000\000\000\000\000\003\000\000\000\000\000\000\000\222\002\000\000\000\000\000\000\003\000\000\000\000\000\000\000\225\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\226\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\227\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\230\002\000\000\000\000\000\000\003\000\000\000\000\000\000\000\233\002\000\000\000\000\000\000\003\000\000\000\000\000\000\000\236\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\237\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\240\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\241\002\000\000\000\000\000\000\003\000\000\000\000\000\000\000\244\002\000\000\000\000\000\000\003\000\000\000\000\000\000\000\247\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\250\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\251\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\252\002\000\000\000\000\000\000\003\000\000\000\000\000\000\000\255\002\000\000\000\000\000\000\003\000\000\000\000\000\000\000\260\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\261\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\262\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\263\002\000\000\000\000\000\000\003\000\000\000\000\000\000\000\266\002\000\000\000\000\000\000\003\000\000\000\000\000\000\000\271\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\272\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\273\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\274\002\000\000\000\000\000\000\003\000\000\000\000\000\000\000\277\002\000\000\000\000\000\000\003\000\000\000\000\000\000\000\302\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\303\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\304\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\305\002\000\000\000\000\000\000\003\000\000\000\000\000\000\000\310\002\000\000\000\000\000\000\003\000\000\000\000\000\000\000\313\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\314\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\315\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\316\002\000\000\000\000\000\000\003\000\000\000\000\000\000\000\321\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\322\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\323\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\324\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\325\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\326\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\327\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\330\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\331\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\332\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\333\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\334\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\335\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\336\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\337\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\340\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\341\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\342\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\343\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\344\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\345\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\346\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\347\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\350\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\351\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\352\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\353\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\354\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\355\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\356\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\357\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\360\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\361\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\362\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\363\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\364\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\365\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\366\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\367\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\370\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\371\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\372\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\373\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\374\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\375\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\376\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\377\002\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\003\000\000\000\000\000\000\001\000\000\000\000\000\000"
	.size	.Lanon.a75d6d9e6a8990b4224ef13f18552af8.13, 9488

	.type	.Lanon.a75d6d9e6a8990b4224ef13f18552af8.14,@object
	.section	.rodata..Lanon.a75d6d9e6a8990b4224ef13f18552af8.14,"a",@progbits
	.p2align	3, 0x0
.Lanon.a75d6d9e6a8990b4224ef13f18552af8.14:
	.asciz	"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\f\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\t\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\006\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\007\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\b\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\013\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\007\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\006\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\b\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\f\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\t\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\006\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\007\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\b\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\013\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\007\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\006\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\b\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\t\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\013\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\f\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\f\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\t\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\006\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\007\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\b\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\013\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\007\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\006\000\000\000\000\000\000\000\b\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\b\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\006\000\000\000\000\000\000\000\007\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\006\000\000\000\000\000\000\000\b\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\f\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\t\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\006\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\007\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\b\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\013\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\007\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\006\000\000\000\000\000\000\000\b\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\b\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\006\000\000\000\000\000\000\000\007\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\006\000\000\000\000\000\000\000\b\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\t\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\013\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\f\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\006\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\006\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\006\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\r\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\b\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\006\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\007\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000\007\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\013\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\b\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\b\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\006\000\000\000\000\000\000\000\b\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\006\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\t\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\t\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\006\000\000\000\000\000\000\000\t\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\f\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\b\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\t\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\r\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\b\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\006\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\007\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000\007\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\013\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\b\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\b\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\006\000\000\000\000\000\000\000\b\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\006\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\t\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\t\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\006\000\000\000\000\000\000\000\t\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\f\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\b\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\t\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\013\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\f\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\r\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\006\000\000\000\000\000\000\000\r\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\r\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\007\000\000\000\000\000\000\000\r\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\r\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\013\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\020\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\b\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\t\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\006\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\007\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\013\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\020\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\b\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\t\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\006\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\007\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\b\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\t\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\013\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000[\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000 \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\006\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\007\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\b\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\t\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\013\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\f\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\r\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000A\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\017\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\017\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\016\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\020\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\020\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\017\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000B\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\021\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\021\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\020\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\022\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\022\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\021\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000C\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\023\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\023\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\022\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\024\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\024\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\023\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000D\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\025\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\025\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\024\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\026\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\026\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\025\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\006\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000E\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\027\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\027\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\026\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\030\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\030\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\027\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\006\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000F\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\031\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\031\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\030\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\032\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\032\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\031\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\006\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000G\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\033\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\033\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\032\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\034\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\034\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\033\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\006\000\000\000\000\000\000\000\b\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000H\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\035\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\035\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\034\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\036\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\036\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\035\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\007\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000I\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\037\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\037\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\036\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\016\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\016\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\037\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\b\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000J\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000 \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000!\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\b\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000K\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000#\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\b\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000L\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000$\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000%\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\b\000\000\000\000\000\000\000\b\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000M\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000&\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000'\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\t\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000N\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000(\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\013\000\000\000\000\000\000\000(\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000)\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\013\000\000\000\000\000\000\000)\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\013\000\000\000\000\000\000\000(\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\t\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000O\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\f\000\000\000\000\000\000\000O\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000*\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\013\000\000\000\000\000\000\000*\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\013\000\000\000\000\000\000\000)\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000+\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\013\000\000\000\000\000\000\000+\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\013\000\000\000\000\000\000\000*\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\t\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000P\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\r\000\000\000\000\000\000\000P\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000,\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\013\000\000\000\000\000\000\000,\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\013\000\000\000\000\000\000\000+\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000-\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\013\000\000\000\000\000\000\000-\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\013\000\000\000\000\000\000\000,\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\t\000\000\000\000\000\000\000\b\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000Q\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\r\000\000\000\000\000\000\000Q\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000.\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\013\000\000\000\000\000\000\000.\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\013\000\000\000\000\000\000\000-\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000/\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\013\000\000\000\000\000\000\000/\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\013\000\000\000\000\000\000\000.\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\t\000\000\000\000\000\000\000\020\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000R\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\r\000\000\000\000\000\000\000R\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\0000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\013\000\000\000\000\000\000\0000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\013\000\000\000\000\000\000\000/\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\0001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\013\000\000\000\000\000\000\0001\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\013\000\000\000\000\000\000\0000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\t\000\000\000\000\000\000\000 \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000S\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\r\000\000\000\000\000\000\000S\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\0002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\013\000\000\000\000\000\000\0002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\013\000\000\000\000\000\000\0001\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\0003\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\013\000\000\000\000\000\000\0003\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\013\000\000\000\000\000\000\0002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\t\000\000\000\000\000\000\000@\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000T\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\r\000\000\000\000\000\000\000T\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\0004\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\013\000\000\000\000\000\000\0004\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\013\000\000\000\000\000\000\0003\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\0005\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\013\000\000\000\000\000\000\0005\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\013\000\000\000\000\000\000\0004\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\t\000\000\000\000\000\000\000\200\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000U\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\r\000\000\000\000\000\000\000U\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\0006\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\013\000\000\000\000\000\000\0006\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\013\000\000\000\000\000\000\0005\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\0007\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\013\000\000\000\000\000\000\0007\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\013\000\000\000\000\000\000\0006\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\t\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000V\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\r\000\000\000\000\000\000\000V\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\0008\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\013\000\000\000\000\000\000\0008\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\013\000\000\000\000\000\000\0007\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\013\000\000\000\000\000\000\0008\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\t\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000W\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\r\000\000\000\000\000\000\000W\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\0009\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000:\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\t\000\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000X\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\r\000\000\000\000\000\000\000X\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000;\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000<\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\t\000\000\000\000\000\000\000\000\b\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000Y\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\r\000\000\000\000\000\000\000Y\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000=\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000>\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\t\000\000\000\000\000\000\000\000\020\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000Z\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\r\000\000\000\000\000\000\000Z\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000?\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000@\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000[\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000 \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\006\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\007\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\b\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\t\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\013\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\f\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\r\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000A\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\017\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\017\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\016\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\020\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\020\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\017\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\003\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000B\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\021\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\021\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\020\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\022\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\022\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\021\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000C\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\023\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\023\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\022\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\024\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\024\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\023\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000D\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\025\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\025\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\024\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\026\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\026\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\025\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\006\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000E\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\027\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\027\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\026\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\030\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\030\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\027\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\006\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000F\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\031\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\031\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\030\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\032\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\032\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\031\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\006\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000G\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\033\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\033\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\032\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\034\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\034\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\033\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\006\000\000\000\000\000\000\000\b\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000H\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\035\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\035\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\034\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\036\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\036\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\035\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\007\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000I\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\037\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\037\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\036\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\016\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\016\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\n\000\000\000\000\000\000\000\037\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\b\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000J\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000 \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000!\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\b\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000K\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000#\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\b\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000L\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000$\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000%\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\b\000\000\000\000\000\000\000\b\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000M\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000&\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000'\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\t\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000N\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000(\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\013\000\000\000\000\000\000\000(\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000)\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\013\000\000\000\000\000\000\000)\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\013\000\000\000\000\000\000\000(\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\t\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000O\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000*\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\013\000\000\000\000\000\000\000*\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\013\000\000\000\000\000\000\000)\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000+\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\013\000\000\000\000\000\000\000+\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\013\000\000\000\000\000\000\000*\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\t\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000P\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000,\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\013\000\000\000\000\000\000\000,\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\013\000\000\000\000\000\000\000+\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000-\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\013\000\000\000\000\000\000\000-\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\013\000\000\000\000\000\000\000,\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\t\000\000\000\000\000\000\000\b\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000Q\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000.\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\013\000\000\000\000\000\000\000.\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\013\000\000\000\000\000\000\000-\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000/\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\013\000\000\000\000\000\000\000/\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\013\000\000\000\000\000\000\000.\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\t\000\000\000\000\000\000\000\020\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000R\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\0000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\013\000\000\000\000\000\000\0000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\013\000\000\000\000\000\000\000/\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\0001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\013\000\000\000\000\000\000\0001\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\013\000\000\000\000\000\000\0000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\t\000\000\000\000\000\000\000 \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000S\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\0002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\013\000\000\000\000\000\000\0002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\013\000\000\000\000\000\000\0001\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\0003\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\013\000\000\000\000\000\000\0003\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\013\000\000\000\000\000\000\0002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\t\000\000\000\000\000\000\000@\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000T\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\0004\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\013\000\000\000\000\000\000\0004\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\013\000\000\000\000\000\000\0003\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\0005\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\013\000\000\000\000\000\000\0005\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\013\000\000\000\000\000\000\0004\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\t\000\000\000\000\000\000\000\200\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000U\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\0006\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\013\000\000\000\000\000\000\0006\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\013\000\000\000\000\000\000\0005\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\0007\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\013\000\000\000\000\000\000\0007\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\013\000\000\000\000\000\000\0006\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\t\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000V\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\0008\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\013\000\000\000\000\000\000\0008\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\013\000\000\000\000\000\000\0007\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\013\000\000\000\000\000\000\0008\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\t\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000W\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\0009\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000:\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\t\000\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000X\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000;\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000<\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\t\000\000\000\000\000\000\000\000\b\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000Y\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000=\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000>\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\t\000\000\000\000\000\000\000\000\020\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000Z\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000?\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000@\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000A\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000B\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000C\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000D\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000E\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000F\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000G\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000H\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000I\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000J\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000K\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000L\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000M\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000N\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000O\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000P\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000Q\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000R\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000S\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000T\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000U\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000V\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000W\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000X\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000Y\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000Z\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000[\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000"
	.size	.Lanon.a75d6d9e6a8990b4224ef13f18552af8.14, 30760

	.type	.Lanon.a75d6d9e6a8990b4224ef13f18552af8.15,@object
	.section	.rodata..Lanon.a75d6d9e6a8990b4224ef13f18552af8.15,"a",@progbits
.Lanon.a75d6d9e6a8990b4224ef13f18552af8.15:
	.ascii	"\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\37723456789:;<=>?\377\000\001\002\003\004\005\006\007\b\t\n\013\f\r\016\017\020\021\022\023\024\025\026\027\030\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377\377"
	.size	.Lanon.a75d6d9e6a8990b4224ef13f18552af8.15, 158

	.type	.Lanon.a75d6d9e6a8990b4224ef13f18552af8.16,@object
	.section	.rodata..Lanon.a75d6d9e6a8990b4224ef13f18552af8.16,"a",@progbits
.Lanon.a75d6d9e6a8990b4224ef13f18552af8.16:
	.asciz	"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\001\001\001\001\001\001\001\001\001\001\001\001\001\001\001\001\001\001\001\001\001\001\001\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000"
	.size	.Lanon.a75d6d9e6a8990b4224ef13f18552af8.16, 158

	.ident	"rustc version 1.99.1 (58cf8f9c3 2026-10-13)"
	.section	".note.GNU-stack","",@progbits
