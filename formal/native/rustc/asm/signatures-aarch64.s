	.file	"signatures.2a34a834e9d96c0-cgu.0"
	.section	.text._RNvCs5fGHjzWXRav_7___rustc17rust_begin_unwind,"ax",@progbits
	.p2align	2
	.type	_RNvCs5fGHjzWXRav_7___rustc17rust_begin_unwind,@function
_RNvCs5fGHjzWXRav_7___rustc17rust_begin_unwind:
.Lfunc_begin0:
	.cfi_startproc
	//APP
	udf	#0
	//NO_APP
	brk	#0x1
.Lfunc_end0:
	.size	_RNvCs5fGHjzWXRav_7___rustc17rust_begin_unwind, .Lfunc_end0-_RNvCs5fGHjzWXRav_7___rustc17rust_begin_unwind
	.cfi_endproc

	.section	.text.memcpy,"ax",@progbits
	.globl	memcpy
	.p2align	2
	.type	memcpy,@function
memcpy:
.Lfunc_begin1:
	.cfi_startproc
	orr	w8, w1, w0
	orr	w8, w8, w2
	tst	x8, #0x7
	b.eq	.LBB1_4
	cbz	x2, .LBB1_7
	mov	x8, x0
.LBB1_3:
	ldrb	w9, [x1], #1
	subs	x2, x2, #1
	strb	w9, [x8], #1
	//APP
	//NO_APP
	b.ne	.LBB1_3
	b	.LBB1_7
.LBB1_4:
	cbz	x2, .LBB1_7
	mov	x8, xzr
.LBB1_6:
	ldr	x9, [x1, x8]
	str	x9, [x0, x8]
	add	x8, x8, #8
	//APP
	//NO_APP
	cmp	x8, x2
	b.lo	.LBB1_6
.LBB1_7:
	ret
.Lfunc_end1:
	.size	memcpy, .Lfunc_end1-memcpy
	.cfi_endproc

	.section	.text.memset,"ax",@progbits
	.globl	memset
	.p2align	2
	.type	memset,@function
memset:
.Lfunc_begin2:
	.cfi_startproc
	orr	w8, w2, w0
	tst	x8, #0x7
	b.eq	.LBB2_4
	cbz	x2, .LBB2_7
	mov	x8, x0
.LBB2_3:
	subs	x2, x2, #1
	strb	w1, [x8], #1
	//APP
	//NO_APP
	b.ne	.LBB2_3
	b	.LBB2_7
.LBB2_4:
	cbz	x2, .LBB2_7
	and	w8, w1, #0xff
	mov	x9, #72340172838076673
	mul	x8, x8, x9
	mov	x9, xzr
.LBB2_6:
	str	x8, [x0, x9]
	add	x9, x9, #8
	//APP
	//NO_APP
	cmp	x9, x2
	b.lo	.LBB2_6
.LBB2_7:
	ret
.Lfunc_end2:
	.size	memset, .Lfunc_end2-memset
	.cfi_endproc

	.section	.text.sphincs_verify,"ax",@progbits
	.globl	sphincs_verify
	.p2align	2
	.type	sphincs_verify,@function
sphincs_verify:
.Lfunc_begin3:
	.cfi_startproc
	stp	x29, x30, [sp, #-96]!
	.cfi_def_cfa_offset 96
	stp	x28, x27, [sp, #16]
	stp	x26, x25, [sp, #32]
	stp	x24, x23, [sp, #48]
	stp	x22, x21, [sp, #64]
	stp	x20, x19, [sp, #80]
	mov	x29, sp
	.cfi_def_cfa w29, 96
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
	sub	x9, sp, #7, lsl #12
.LBB3_1:
	sub	sp, sp, #1, lsl #12
	ldr	xzr, [sp]
	cmp	sp, x9
	b.ne	.LBB3_1
	sub	sp, sp, #608
	ldr	x8, [x0, #1056]
	ldr	x9, [x0, #1064]
	mov	x19, x0
	ldr	x10, [x0, #1072]
	ldr	x21, [x0, #1024]
	add	x20, sp, #468
	stp	x8, x9, [sp, #432]
	ldr	x8, [x0, #1080]
	mov	w1, wzr
	ldr	x23, [x0, #1032]
	ldr	x24, [x0, #1040]
	mov	w2, #7740
	ldr	x22, [x0, #1048]
	add	x0, sp, #468
	stp	x10, x8, [sp, #448]
	add	x25, x20, #1, lsl #12
	bl	memset
	add	x8, x19, #1112
	mov	x9, #-4224
.LBB3_3:
	add	x10, x8, x9
	add	x12, x20, x9
	adds	x9, x9, #32
	ldr	x11, [x10, #4200]
	ldr	x13, [x10, #4208]
	ldr	x14, [x10, #4216]
	ldr	x10, [x10, #4224]
	str	x11, [x12, #4224]
	str	x13, [x12, #4232]
	str	x14, [x12, #4240]
	str	x10, [x12, #4248]
	b.ne	.LBB3_3
	ldr	x8, [x19, #5312]
	ldr	x9, [x19, #5320]
	add	x11, sp, #468
	ldr	w10, [x19, #5328]
	str	x8, [x20, #4224]
	mov	w8, #5360
	str	x9, [x20, #4232]
	rev	w9, w10
	add	x8, x19, x8
	str	w9, [sp, #4708]
	mov	w9, #140
	mov	w10, #4244
.LBB3_5:
	ldp	x12, x13, [x8, #-24]
	add	x14, x11, x10
	subs	x9, x9, #4
	add	x10, x10, #32
	stp	x12, x13, [x14]
	ldp	x12, x15, [x8, #-8]
	add	x8, x8, #32
	stp	x12, x15, [x14, #16]
	b.ne	.LBB3_5
	ldr	x9, [x19, #6456]
	add	x10, x25, #1268
	ldr	x11, [x19, #6464]
	add	x12, x25, #1276
	mov	x8, xzr
	str	x9, [x10]
	ldr	x9, [x19, #6472]
	add	x10, x25, #1284
	str	x11, [x12]
	ldr	x11, [x19, #6480]
	ldr	w12, [x19, #6488]
	str	x9, [x10]
	add	x9, x25, #1292
	mov	w10, #6520
	str	x11, [x9]
	rev	w9, w12
	str	w9, [sp, #5864]
	add	x9, x19, x10
	add	x10, sp, #468
.LBB3_7:
	add	x11, x9, x8
	add	x13, x10, x8
	add	x8, x8, #32
	ldp	x12, x14, [x11, #-24]
	cmp	x8, #1120
	ldp	x15, x11, [x11, #-8]
	str	x12, [x13, #5400]
	str	x14, [x13, #5408]
	str	x15, [x13, #5416]
	str	x11, [x13, #5424]
	b.ne	.LBB3_7
	ldr	x8, [x19, #7616]
	ldr	w11, [x19, #7648]
	ldr	x9, [x19, #7624]
	ldr	x10, [x19, #7632]
	ldr	x12, [x19, #7640]
	str	x8, [x20, #6520]
	rev	w11, w11
	mov	w8, #7680
	str	x9, [x20, #6528]
	add	x8, x19, x8
	mov	w9, #144
	str	x10, [x20, #6536]
	mov	w10, #6556
	str	w11, [sp, #7020]
	add	x11, sp, #468
	str	x12, [x20, #6544]
.LBB3_9:
	ldp	x12, x13, [x8, #-24]
	add	x14, x11, x10
	subs	x9, x9, #4
	add	x10, x10, #32
	stp	x12, x13, [x14]
	ldp	x12, x15, [x8, #-8]
	add	x8, x8, #32
	stp	x12, x15, [x14, #16]
	b.ne	.LBB3_9
	ldr	x8, [x19, #8808]
	add	x9, x25, #3612
	ldr	x10, [x19, #8816]
	str	x21, [sp, #8208]
	add	x21, sp, #6, lsl #12
	mov	w26, #4224
	str	x8, [x9]
	add	x8, x25, #3620
	ldr	x9, [x19, #8824]
	str	x10, [x8]
	add	x8, x25, #3628
	ldr	x10, [x19, #8832]
	str	x9, [x8]
	add	x8, x25, #3636
	add	x9, sp, #221
	str	x10, [x8]
	add	x8, sp, #213
	add	x19, sp, #2, lsl #12
	ldur	x8, [x8, #255]
	ldur	x9, [x9, #255]
	str	x22, [sp, #8232]
	add	x22, sp, #2, lsl #12
	add	x10, sp, #468
	add	x25, sp, #4, lsl #12
	str	x23, [sp, #8216]
	add	x19, x19, #16
	add	x21, x21, #2192
	str	x24, [sp, #8224]
	add	x22, x22, #52
	add	x23, x10, #96
	mov	x24, #-4224
	add	x25, x25, #16
	str	x8, [sp, #27808]
	str	x9, [sp, #27816]
.LBB3_11:
	add	x27, x23, x24
	add	x0, sp, #2, lsl #12
	add	x1, sp, #6, lsl #12
	ldr	x8, [x27, #4160]
	ldr	x9, [x27, #4168]
	ldr	x10, [x27, #4176]
	add	x0, x0, #52
	add	x1, x1, #2192
	mov	w2, #160
	str	x8, [sp, #26768]
	ldr	x8, [x27, #4184]
	str	x9, [sp, #26776]
	ldr	x9, [x27, #4192]
	stp	x10, x8, [x21, #16]
	ldr	x8, [x27, #4200]
	ldr	x10, [x27, #4216]
	stp	x9, x8, [x21, #32]
	ldr	x8, [x27, #4208]
	ldr	x9, [x27, #4232]
	stp	x8, x10, [x21, #48]
	ldr	x8, [x27, #4224]
	ldr	x10, [x27, #4248]
	stp	x8, x9, [x21, #64]
	ldr	x8, [x27, #4240]
	ldr	x9, [x27, #4264]
	stp	x8, x10, [x21, #80]
	ldr	x8, [x27, #4256]
	ldr	x10, [x27, #4280]
	stp	x8, x9, [x21, #96]
	ldr	x8, [x27, #4272]
	ldr	x9, [x27, #4296]
	stp	x8, x10, [x21, #112]
	ldr	x8, [x27, #4288]
	ldr	x10, [x27, #4312]
	stp	x8, x9, [x21, #128]
	ldr	x8, [x27, #4304]
	stp	x8, x10, [x21, #144]
	bl	memcpy
	ldr	x8, [x27, #4144]
	ldr	x9, [x27, #4152]
	add	x0, sp, #6, lsl #12
	add	x1, sp, #2, lsl #12
	add	x0, x0, #2192
	mov	w2, #176
	add	x1, x1, #52
	stp	x8, x9, [x22, #160]
	bl	memcpy
	add	x8, x25, x24
	add	x1, sp, #6, lsl #12
	mov	w2, #176
	add	x0, x8, x26
	add	x1, x1, #2192
	bl	memcpy
	adds	x24, x24, #176
	b.ne	.LBB3_11
	add	x23, sp, #3, lsl #12
	mov	w1, wzr
	mov	w2, #288
	add	x23, x23, #3696
	add	x0, x23, #128
	bl	memset
	mov	w9, #4244
	add	x10, sp, #468
	ldr	w21, [sp, #4708]
	add	x9, x10, x9
	add	x10, sp, #2, lsl #12
	mov	x8, xzr
	add	x10, x10, #52
.LBB3_13:
	add	x11, x9, x8
	add	x13, x10, x8
	add	x8, x8, #16
	ldp	x12, x11, [x11]
	cmp	x8, #1024
	stp	x12, x11, [x13]
	b.ne	.LBB3_13
	add	x0, sp, #6, lsl #12
	add	x1, sp, #2, lsl #12
	mov	w2, #1024
	add	x0, x0, #2192
	add	x1, x1, #52
	add	x24, sp, #2, lsl #12
	add	x24, x24, #52
	bl	memcpy
	mov	w8, #5268
	add	x25, sp, #468
	mov	w9, #5284
	add	x8, x25, x8
	add	x9, x25, x9
	mov	w11, #5300
	ldp	x10, x8, [x8]
	add	x0, sp, #6, lsl #12
	ldp	x12, x9, [x9]
	add	x1, sp, #6, lsl #12
	add	x0, x0, #144
	add	x1, x1, #2192
	mov	w2, #1024
	str	x8, [sp, #15992]
	mov	w8, #5316
	str	x10, [sp, #15984]
	add	x10, x25, x11
	add	x8, x25, x8
	str	x9, [sp, #16008]
	ldp	x11, x9, [x10]
	ldp	x8, x10, [x8]
	str	x12, [sp, #16000]
	mov	w12, #5332
	str	x9, [sp, #16024]
	add	x9, x25, x12
	mov	w12, #5364
	str	x10, [sp, #16040]
	mov	w10, #5348
	str	x11, [sp, #16016]
	ldp	x9, x11, [x9]
	str	x8, [sp, #16032]
	add	x8, x25, x10
	ldp	x8, x10, [x8]
	str	x9, [sp, #16048]
	add	x9, x25, x12
	mov	w12, #5380
	str	x11, [sp, #16056]
	str	x8, [sp, #16064]
	ldp	x8, x11, [x9]
	add	x9, x25, x12
	str	x10, [sp, #16072]
	str	x8, [sp, #16080]
	ldp	x8, x10, [x9]
	str	x11, [sp, #16088]
	str	x10, [sp, #16104]
	str	x8, [sp, #16096]
	bl	memcpy
	add	x0, sp, #5, lsl #12
	add	x1, sp, #6, lsl #12
	mov	w2, #1024
	add	x0, x0, #3216
	add	x1, x1, #144
	bl	memcpy
	add	x0, sp, #5, lsl #12
	add	x1, sp, #5, lsl #12
	mov	w2, #1024
	add	x0, x0, #2192
	add	x1, x1, #3216
	bl	memcpy
	add	x0, sp, #6, lsl #12
	add	x1, sp, #5, lsl #12
	mov	w2, #1024
	add	x0, x0, #1168
	add	x1, x1, #2192
	bl	memcpy
	add	x0, sp, #5, lsl #12
	add	x1, sp, #6, lsl #12
	mov	w2, #1024
	add	x0, x0, #1168
	add	x1, x1, #1168
	bl	memcpy
	ldr	w22, [sp, #5864]
	mov	w9, #5400
	mov	x8, xzr
	add	x9, x25, x9
.LBB3_15:
	add	x10, x9, x8
	add	x12, x24, x8
	add	x8, x8, #16
	ldp	x11, x10, [x10]
	cmp	x8, #1024
	stp	x11, x10, [x12]
	b.ne	.LBB3_15
	add	x0, sp, #6, lsl #12
	add	x1, sp, #2, lsl #12
	mov	w2, #1024
	add	x0, x0, #2192
	add	x1, x1, #52
	add	x25, sp, #2, lsl #12
	add	x25, x25, #52
	bl	memcpy
	ldr	x8, [x20, #6424]
	ldr	x9, [x20, #6432]
	add	x0, sp, #6, lsl #12
	ldr	x10, [x20, #6440]
	add	x1, sp, #6, lsl #12
	add	x0, x0, #144
	stp	x8, x9, [x23, #128]
	ldr	x8, [x20, #6448]
	ldr	x9, [x20, #6456]
	str	x10, [sp, #16128]
	ldr	x10, [x20, #6480]
	add	x1, x1, #2192
	str	x8, [sp, #16136]
	ldr	x8, [x20, #6464]
	mov	w2, #1024
	str	x9, [sp, #16144]
	ldr	x9, [x20, #6496]
	str	x8, [sp, #16152]
	ldr	x8, [x20, #6472]
	str	x10, [sp, #16168]
	ldr	x10, [x20, #6512]
	str	x8, [sp, #16160]
	ldr	x8, [x20, #6488]
	str	x9, [sp, #16184]
	ldr	x9, [x20, #6528]
	str	x8, [sp, #16176]
	ldr	x8, [x20, #6504]
	str	x10, [sp, #16200]
	ldr	x10, [x20, #6544]
	str	x8, [sp, #16192]
	ldr	x8, [x20, #6520]
	str	x9, [sp, #16216]
	str	x8, [sp, #16208]
	ldr	x8, [x20, #6536]
	str	x10, [sp, #16232]
	str	x8, [sp, #16224]
	bl	memcpy
	add	x0, sp, #5, lsl #12
	add	x1, sp, #6, lsl #12
	mov	w2, #1024
	add	x0, x0, #3216
	add	x1, x1, #144
	bl	memcpy
	add	x0, sp, #5, lsl #12
	add	x1, sp, #5, lsl #12
	mov	w2, #1024
	add	x0, x0, #2192
	add	x1, x1, #3216
	bl	memcpy
	add	x0, sp, #6, lsl #12
	add	x1, sp, #5, lsl #12
	mov	w2, #1024
	add	x0, x0, #1168
	add	x1, x1, #2192
	bl	memcpy
	add	x0, sp, #5, lsl #12
	add	x1, sp, #6, lsl #12
	mov	w2, #1024
	add	x0, x0, #144
	add	x1, x1, #1168
	bl	memcpy
	ldr	w24, [sp, #7020]
	mov	w9, #6556
	add	x10, sp, #468
	mov	x8, xzr
	add	x9, x10, x9
.LBB3_17:
	add	x10, x9, x8
	add	x12, x25, x8
	add	x8, x8, #16
	ldp	x11, x10, [x10]
	cmp	x8, #1024
	stp	x11, x10, [x12]
	b.ne	.LBB3_17
	add	x0, sp, #6, lsl #12
	add	x1, sp, #2, lsl #12
	mov	w2, #1024
	add	x0, x0, #2192
	add	x1, x1, #52
	add	x23, sp, #2, lsl #12
	add	x23, x23, #52
	bl	memcpy
	mov	w9, #7580
	add	x8, sp, #468
	mov	w10, #7596
	add	x9, x8, x9
	add	x10, x8, x10
	mov	w12, #7612
	ldp	x11, x9, [x9]
	add	x0, sp, #6, lsl #12
	ldp	x13, x10, [x10]
	add	x1, sp, #6, lsl #12
	rev	w26, w21
	add	x0, x0, #144
	add	x1, x1, #2192
	str	x9, [sp, #16248]
	mov	w9, #7628
	mov	w2, #1024
	str	x11, [sp, #16240]
	add	x11, x8, x12
	add	x9, x8, x9
	str	x10, [sp, #16264]
	ldp	x12, x10, [x11]
	ldp	x9, x11, [x9]
	str	x13, [sp, #16256]
	mov	w13, #7644
	add	x21, sp, #6, lsl #12
	rev	w25, w22
	str	x10, [sp, #16280]
	add	x10, x8, x13
	mov	w13, #7676
	str	x11, [sp, #16296]
	mov	w11, #7660
	rev	w22, w24
	str	x12, [sp, #16272]
	ldp	x10, x12, [x10]
	str	x9, [sp, #16288]
	add	x9, x8, x11
	add	x21, x21, #144
	ldp	x9, x11, [x9]
	str	x10, [sp, #16304]
	add	x10, x8, x13
	mov	w13, #7692
	str	x12, [sp, #16312]
	str	x9, [sp, #16320]
	ldp	x9, x12, [x10]
	add	x10, x8, x13
	str	x11, [sp, #16328]
	mov	w13, #7708
	str	x9, [sp, #16336]
	ldp	x9, x11, [x10]
	add	x10, x8, x13
	mov	w13, #7724
	str	x12, [sp, #16344]
	add	x8, x8, x13
	str	x9, [sp, #16352]
	ldp	x9, x12, [x10]
	ldp	x8, x10, [x8]
	str	x11, [sp, #16360]
	str	x12, [sp, #16376]
	str	x9, [sp, #16368]
	str	x10, [sp, #16392]
	str	x8, [sp, #16384]
	bl	memcpy
	add	x0, sp, #5, lsl #12
	add	x1, sp, #6, lsl #12
	mov	w2, #1024
	add	x0, x0, #3216
	add	x1, x1, #144
	bl	memcpy
	add	x0, sp, #5, lsl #12
	add	x1, sp, #5, lsl #12
	mov	w2, #1024
	add	x0, x0, #2192
	add	x1, x1, #3216
	bl	memcpy
	add	x0, sp, #6, lsl #12
	add	x1, sp, #5, lsl #12
	mov	w2, #1024
	add	x0, x0, #1168
	add	x1, x1, #2192
	bl	memcpy
	ldr	x8, [sp, #27808]
	ldr	x9, [sp, #27816]
	add	x0, sp, #2, lsl #12
	add	x1, sp, #4, lsl #12
	add	x0, x0, #52
	mov	w2, #4224
	add	x1, x1, #16
	str	x8, [x20, #12416]
	mov	w24, #4640
	str	x9, [x20, #12424]
	mov	w20, #4224
	bl	memcpy
	mov	w8, #4656
	add	x1, sp, #5, lsl #12
	mov	w2, #1024
	add	x0, x23, x8
	add	x1, x1, #1168
	str	x0, [sp, #392]
	bl	memcpy
	mov	w8, #5684
	add	x1, sp, #5, lsl #12
	mov	w2, #1024
	add	x0, x23, x8
	add	x1, x1, #144
	str	w26, [sp, #13924]
	bl	memcpy
	mov	w8, #6712
	add	x1, sp, #6, lsl #12
	mov	w2, #1024
	add	x0, x23, x8
	add	x1, x1, #1168
	str	w25, [sp, #14952]
	bl	memcpy
	add	x1, sp, #3, lsl #12
	add	x0, x23, x20
	mov	w2, #416
	add	x1, x1, #3696
	str	w22, [sp, #15980]
	str	x0, [sp, #376]
	bl	memcpy
	add	x0, sp, #6, lsl #12
	mov	w1, wzr
	mov	w2, #344
	add	x0, x0, #2192
	bl	memset
	add	x0, sp, #6, lsl #12
	add	x1, x23, x24
	mov	w2, #16
	add	x0, x0, #2192
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	add	x0, sp, #6, lsl #12
	add	x1, sp, #2, lsl #12
	mov	w2, #16
	add	x0, x0, #2192
	add	x1, x1, #16
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	add	x0, sp, #6, lsl #12
	add	x1, x19, #16
	mov	w2, #16
	add	x0, x0, #2192
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	add	x0, sp, #6, lsl #12
	add	x1, sp, #432
	mov	w2, #32
	add	x0, x0, #2192
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	add	x0, sp, #4, lsl #12
	add	x1, sp, #6, lsl #12
	mov	w2, #344
	add	x0, x0, #16
	add	x1, x1, #2192
	bl	memcpy
	add	x23, sp, #5, lsl #12
	add	x0, sp, #4, lsl #12
	add	x1, sp, #5, lsl #12
	add	x23, x23, #1168
	add	x0, x0, #16
	add	x1, x1, #3216
	mov	w2, #4
	str	wzr, [x23, #2048]
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	add	x0, sp, #6, lsl #12
	add	x1, sp, #4, lsl #12
	add	x0, x0, #1168
	add	x1, x1, #16
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher8finalize
	ldr	x8, [sp, #25744]
	ldr	x9, [sp, #25752]
	add	x0, sp, #4, lsl #12
	ldr	x10, [sp, #25768]
	add	x1, sp, #6, lsl #12
	add	x0, x0, #16
	str	x8, [sp, #24720]
	ldr	x8, [sp, #25760]
	add	x1, x1, #2192
	mov	w2, #344
	str	x9, [sp, #24728]
	str	x8, [sp, #24736]
	str	x10, [sp, #24744]
	bl	memcpy
	add	x0, sp, #4, lsl #12
	add	x1, sp, #5, lsl #12
	mov	w8, #16777216
	add	x0, x0, #16
	add	x1, x1, #3216
	mov	w2, #4
	str	w8, [x23, #2048]
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	add	x0, sp, #6, lsl #12
	add	x1, sp, #4, lsl #12
	add	x0, x0, #1168
	add	x1, x1, #16
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher8finalize
	ldr	x9, [sp, #25744]
	ldr	x10, [sp, #25752]
	mov	x8, xzr
	ldr	x11, [sp, #25768]
	str	x9, [sp, #24752]
	ldr	x9, [sp, #25760]
	str	x10, [sp, #24760]
	mov	w10, #6
	str	x9, [sp, #24768]
	add	x9, sp, #4, lsl #12
	add	x9, x9, #16
	str	x11, [sp, #24776]
.LBB3_19:
	lsr	x13, x8, #3
	add	x14, x8, #2
	and	x18, x8, #0x6
	lsr	x16, x14, #3
	eor	x11, x18, #0x7
	eor	w18, w18, #0x6
	ldrb	w13, [x21, x13]
	and	w14, w14, #0x6
	add	x0, x8, #3
	ldrb	w16, [x21, x16]
	add	x15, x8, #4
	eor	w14, w14, #0x7
	lsr	w18, w13, w18
	lsr	x1, x0, #3
	lsr	x17, x15, #3
	lsr	w13, w13, w11
	lsr	w14, w16, w14
	bic	w16, w10, w0
	ldrb	w0, [x21, x1]
	and	w18, w18, #0x1
	ldrb	w17, [x21, x17]
	bfi	w18, w13, #1, #1
	ubfiz	w13, w14, #1, #1
	and	w14, w15, #0x6
	add	x12, x8, #6
	eor	w14, w14, #0x7
	lsr	w15, w0, w16
	add	x16, x8, #5
	lsr	w14, w17, w14
	orr	w13, w13, w18, lsl #2
	lsr	x17, x16, #3
	lsr	x0, x12, #3
	and	w12, w12, #0x6
	ubfiz	w14, w14, #1, #1
	bfxil	w13, w15, #0, #1
	bic	w16, w10, w16
	ldrb	w17, [x21, x17]
	ldrb	w15, [x21, x0]
	add	x0, x8, #7
	eor	w12, w12, #0x7
	lsr	x1, x0, #3
	orr	w13, w14, w13, lsl #2
	lsr	w14, w17, w16
	lsr	w12, w15, w12
	add	x18, x8, #8
	ldrb	w17, [x21, x1]
	lsr	x15, x18, #3
	add	x16, x8, #9
	bfxil	w13, w14, #0, #1
	ubfiz	w12, w12, #2, #1
	bic	w14, w10, w0
	lsr	x18, x16, #3
	lsr	w14, w17, w14
	mvn	w16, w16
	orr	w12, w12, w13, lsl #3
	ldrb	w13, [x21, x15]
	add	x8, x8, #10
	ubfiz	w14, w14, #1, #1
	ldrb	w15, [x21, x18]
	cmp	x8, #240
	and	x12, x12, #0x3fc
	lsr	x11, x13, x11
	and	x13, x16, #0x6
	orr	x12, x12, x14
	lsr	x13, x15, x13
	bfxil	x12, x11, #0, #1
	and	x11, x13, #0x1
	orr	x11, x11, x12, lsl #1
	str	x11, [x9], #8
	b.ne	.LBB3_19
	ldrb	w8, [x23, #3103]
	ldrb	w9, [x23, #3102]
	add	x1, sp, #4, lsl #12
	ldrb	w10, [x23, #3104]
	ldrb	w20, [x23, #3105]
	add	x1, x1, #16
	lsl	w8, w8, #8
	mov	w2, #192
	add	x21, sp, #4, lsl #12
	and	x22, x20, #0xff
	add	x21, x21, #16
	orr	w8, w8, w9, lsl #16
	orr	w8, w8, w10
	bfi	x22, x8, #8, #18
	add	x8, sp, #6, lsl #12
	add	x8, x8, #1168
	add	x24, x8, #8
	str	x22, [sp, #25744]
	mov	x0, x24
	bl	memcpy
	add	x9, sp, #6, lsl #12
	rev	x8, x22
	str	x22, [sp, #384]
	add	x9, x9, #2192
	lsl	w26, w20, #24
	lsl	x27, x8, #8
	add	x22, x9, #200
	add	x9, sp, #2, lsl #12
	mov	x19, xzr
	add	x21, x21, #200
	mov	w8, #176
	add	x9, x9, #52
	mov	w25, #50331648
	mov	w20, #136
	stp	x24, x27, [sp, #400]
.LBB3_21:
	ldr	x10, [x24, x19, lsl #3]
	madd	x24, x19, x8, x9
	add	x0, sp, #4, lsl #12
	add	x0, x0, #16
	mov	w1, wzr
	mov	w2, #344
	add	w8, w10, w19, lsl #10
	str	xzr, [sp, #24720]
	str	x27, [sp, #24728]
	rev	w8, w8
	str	x10, [sp, #424]
	str	w25, [x23, #3088]
	str	w26, [x23, #3092]
	str	wzr, [x23, #3096]
	str	w8, [x23, #3100]
	bl	memset
	add	x0, sp, #4, lsl #12
	add	x1, sp, #2, lsl #12
	mov	w2, #16
	add	x0, x0, #16
	add	x1, x1, #16
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	add	x0, sp, #4, lsl #12
	add	x1, sp, #6, lsl #12
	mov	w2, #32
	add	x0, x0, #16
	add	x1, x1, #144
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	add	x0, sp, #6, lsl #12
	add	x1, sp, #4, lsl #12
	mov	w2, #344
	add	x0, x0, #2192
	add	x1, x1, #16
	bl	memcpy
	add	x0, sp, #6, lsl #12
	add	x1, x24, #160
	mov	w2, #16
	add	x0, x0, #2192
	str	x24, [sp, #416]
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	add	x0, sp, #5, lsl #12
	add	x1, sp, #6, lsl #12
	add	x0, x0, #144
	add	x1, x1, #2192
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher8finalize
	mov	x28, xzr
.LBB3_22:
	ldp	x11, x12, [sp, #416]
	mov	w8, #1
	ldr	x10, [sp, #20632]
	lsl	x8, x8, x28
	ldr	x9, [sp, #20624]
	add	x0, sp, #4, lsl #12
	mov	w1, wzr
	mov	w2, #344
	add	x11, x11, x28, lsl #4
	str	x10, [sp, #21656]
	add	x10, sp, #5, lsl #12
	tst	x8, x12
	add	x10, x10, #1168
	str	x9, [sp, #21648]
	csel	x8, x10, x11, eq
	csel	x10, x11, x10, eq
	add	x11, sp, #5, lsl #12
	ldp	x9, x8, [x8]
	add	x11, x11, #2192
	add	x0, x0, #16
	str	xzr, [sp, #23696]
	str	x27, [sp, #23704]
	str	x9, [sp, #22672]
	ldp	x9, x10, [x10]
	str	x8, [sp, #22680]
	mov	w8, #9
	sub	x8, x8, x28
	add	x28, x28, #1
	str	w25, [x23, #2064]
	stp	x9, x10, [x11, #16]
	lsr	x9, x12, x28
	lsl	w8, w19, w8
	rev	w10, w28
	str	w26, [x23, #2068]
	add	w8, w8, w9
	str	w10, [x23, #2072]
	rev	w8, w8
	str	w8, [x23, #2076]
	bl	memset
	ldr	x8, [sp, #16736]
	ldr	x9, [sp, #8208]
	ldr	x10, [sp, #8216]
	add	x0, x8, #16
	stp	x9, x10, [x21]
	cmp	x0, #136
	str	x0, [sp, #16736]
	b.ne	.LBB3_24
	ldr	x9, [sp, #16600]
	ldr	x14, [sp, #16400]
	ldr	x10, [sp, #16608]
	ldr	x15, [sp, #16408]
	ldr	x8, [sp, #16616]
	ldr	x16, [sp, #16624]
	eor	x9, x14, x9
	ldr	x14, [sp, #16424]
	ldr	x12, [sp, #16632]
	eor	x10, x15, x10
	str	x9, [sp, #16400]
	ldr	x9, [sp, #16416]
	str	x10, [sp, #16408]
	ldr	x10, [sp, #16432]
	ldr	x13, [sp, #16640]
	eor	x8, x9, x8
	eor	x9, x14, x16
	ldr	x11, [sp, #16648]
	str	x8, [sp, #16416]
	ldr	x8, [sp, #16440]
	ldr	x15, [sp, #16656]
	str	x9, [sp, #16424]
	eor	x9, x10, x12
	ldr	x10, [sp, #16448]
	eor	x8, x8, x13
	ldr	x18, [sp, #16664]
	ldr	x12, [sp, #16456]
	ldr	x13, [sp, #16464]
	ldr	x14, [sp, #16672]
	ldr	x0, [sp, #16472]
	str	x8, [sp, #16440]
	eor	x8, x10, x11
	ldr	x16, [sp, #16680]
	eor	x10, x13, x18
	eor	x11, x0, x14
	add	x0, sp, #4, lsl #12
	add	x0, x0, #16
	str	x9, [sp, #16432]
	eor	x9, x12, x15
	ldr	x13, [sp, #16688]
	str	x8, [sp, #16448]
	ldr	x8, [sp, #16488]
	ldr	x12, [sp, #16480]
	ldr	x14, [sp, #16696]
	str	x9, [sp, #16456]
	eor	x8, x8, x13
	ldr	x9, [sp, #16496]
	str	x10, [sp, #16464]
	eor	x12, x12, x16
	ldr	x10, [sp, #16704]
	str	x11, [sp, #16472]
	eor	x9, x9, x14
	ldr	x11, [sp, #16504]
	ldr	x13, [sp, #16712]
	str	x8, [sp, #16488]
	ldr	x8, [sp, #16512]
	ldr	x17, [sp, #16528]
	eor	x10, x11, x10
	str	x12, [sp, #16480]
	ldr	x11, [sp, #16720]
	eor	x8, x8, x13
	str	x9, [sp, #16496]
	ldr	x9, [sp, #16520]
	ldr	x12, [sp, #16728]
	str	x8, [sp, #16512]
	eor	x9, x9, x11
	str	x10, [sp, #16504]
	eor	x8, x17, x12
	str	x9, [sp, #16520]
	str	x8, [sp, #16528]
	bl	_RNvCsndc0WgnAaH_9keccak2568keccak_f
	mov	x0, xzr
	str	xzr, [sp, #16736]
.LBB3_24:
	add	x23, sp, #5, lsl #12
	mov	w25, #32
	add	x23, x23, #3216
	b	.LBB3_26
.LBB3_25:
	sub	x25, x25, x24
	add	x23, x23, x24
	cbz	x25, .LBB3_30
.LBB3_26:
	sub	x8, x20, x0
	cmp	x25, x8
	csel	x24, x25, x8, lo
	add	x1, x24, x0
	cmp	x1, x0
	b.lo	.LBB3_87
	cmp	x1, #137
	b.hs	.LBB3_87
	add	x0, x21, x0
	mov	x1, x23
	mov	x2, x24
	bl	memcpy
	ldr	x8, [sp, #16736]
	add	x0, x8, x24
	cmp	x0, #136
	str	x0, [sp, #16736]
	b.ne	.LBB3_25
	ldr	x9, [sp, #16600]
	ldr	x14, [sp, #16400]
	ldr	x10, [sp, #16608]
	ldr	x15, [sp, #16408]
	ldr	x8, [sp, #16616]
	ldr	x16, [sp, #16624]
	eor	x9, x14, x9
	ldr	x14, [sp, #16424]
	ldr	x12, [sp, #16632]
	eor	x10, x15, x10
	str	x9, [sp, #16400]
	ldr	x9, [sp, #16416]
	str	x10, [sp, #16408]
	ldr	x10, [sp, #16432]
	ldr	x13, [sp, #16640]
	eor	x8, x9, x8
	eor	x9, x14, x16
	ldr	x11, [sp, #16648]
	str	x8, [sp, #16416]
	ldr	x8, [sp, #16440]
	ldr	x15, [sp, #16656]
	str	x9, [sp, #16424]
	eor	x9, x10, x12
	ldr	x10, [sp, #16448]
	eor	x8, x8, x13
	ldr	x18, [sp, #16664]
	ldr	x12, [sp, #16456]
	ldr	x13, [sp, #16464]
	ldr	x14, [sp, #16672]
	ldr	x0, [sp, #16472]
	str	x8, [sp, #16440]
	eor	x8, x10, x11
	ldr	x16, [sp, #16680]
	eor	x10, x13, x18
	eor	x11, x0, x14
	add	x0, sp, #4, lsl #12
	add	x0, x0, #16
	str	x9, [sp, #16432]
	eor	x9, x12, x15
	ldr	x13, [sp, #16688]
	str	x8, [sp, #16448]
	ldr	x8, [sp, #16488]
	ldr	x12, [sp, #16480]
	ldr	x14, [sp, #16696]
	str	x9, [sp, #16456]
	eor	x8, x8, x13
	ldr	x9, [sp, #16496]
	str	x10, [sp, #16464]
	eor	x12, x12, x16
	ldr	x10, [sp, #16704]
	str	x11, [sp, #16472]
	eor	x9, x9, x14
	ldr	x11, [sp, #16504]
	ldr	x13, [sp, #16712]
	str	x8, [sp, #16488]
	ldr	x8, [sp, #16512]
	ldr	x17, [sp, #16528]
	eor	x10, x11, x10
	str	x12, [sp, #16480]
	ldr	x11, [sp, #16720]
	eor	x8, x8, x13
	str	x9, [sp, #16496]
	ldr	x9, [sp, #16520]
	ldr	x12, [sp, #16728]
	str	x8, [sp, #16512]
	eor	x9, x9, x11
	str	x10, [sp, #16504]
	eor	x8, x17, x12
	str	x9, [sp, #16520]
	str	x8, [sp, #16528]
	bl	_RNvCsndc0WgnAaH_9keccak2568keccak_f
	mov	x0, xzr
	str	xzr, [sp, #16736]
	b	.LBB3_25
.LBB3_30:
	add	x0, sp, #6, lsl #12
	add	x1, sp, #4, lsl #12
	mov	w2, #344
	add	x0, x0, #2192
	add	x1, x1, #16
	mov	x27, x19
	mov	w19, w26
	bl	memcpy
	ldr	x25, [sp, #27104]
	add	x23, sp, #5, lsl #12
	mov	w26, #32
	add	x23, x23, #2192
	b	.LBB3_32
.LBB3_31:
	sub	x26, x26, x24
	add	x23, x23, x24
	cbz	x26, .LBB3_36
.LBB3_32:
	sub	x8, x20, x25
	cmp	x26, x8
	csel	x24, x26, x8, lo
	add	x1, x24, x25
	cmp	x1, x25
	b.lo	.LBB3_88
	cmp	x1, #137
	b.hs	.LBB3_88
	add	x0, x22, x25
	mov	x1, x23
	mov	x2, x24
	bl	memcpy
	ldr	x8, [sp, #27104]
	add	x25, x8, x24
	cmp	x25, #136
	str	x25, [sp, #27104]
	b.ne	.LBB3_31
	ldr	x9, [sp, #26968]
	ldr	x14, [sp, #26768]
	ldr	x10, [sp, #26976]
	ldr	x15, [sp, #26776]
	ldr	x8, [sp, #26984]
	ldr	x16, [sp, #26992]
	eor	x9, x14, x9
	ldr	x14, [sp, #26792]
	ldr	x12, [sp, #27000]
	eor	x10, x15, x10
	str	x9, [sp, #26768]
	ldr	x9, [sp, #26784]
	str	x10, [sp, #26776]
	ldr	x10, [sp, #26800]
	ldr	x13, [sp, #27008]
	eor	x8, x9, x8
	eor	x9, x14, x16
	ldr	x11, [sp, #27016]
	str	x8, [sp, #26784]
	ldr	x8, [sp, #26808]
	ldr	x15, [sp, #27024]
	str	x9, [sp, #26792]
	eor	x9, x10, x12
	ldr	x10, [sp, #26816]
	eor	x8, x8, x13
	ldr	x18, [sp, #27032]
	ldr	x12, [sp, #26824]
	ldr	x13, [sp, #26832]
	ldr	x14, [sp, #27040]
	ldr	x0, [sp, #26840]
	str	x8, [sp, #26808]
	eor	x8, x10, x11
	ldr	x16, [sp, #27048]
	eor	x10, x13, x18
	eor	x11, x0, x14
	add	x0, sp, #6, lsl #12
	add	x0, x0, #2192
	str	x9, [sp, #26800]
	eor	x9, x12, x15
	ldr	x13, [sp, #27056]
	str	x8, [sp, #26816]
	ldr	x8, [sp, #26856]
	ldr	x12, [sp, #26848]
	ldr	x14, [sp, #27064]
	str	x9, [sp, #26824]
	eor	x8, x8, x13
	ldr	x9, [sp, #26864]
	str	x10, [sp, #26832]
	eor	x12, x12, x16
	ldr	x10, [sp, #27072]
	str	x11, [sp, #26840]
	eor	x9, x9, x14
	ldr	x11, [sp, #26872]
	ldr	x13, [sp, #27080]
	str	x8, [sp, #26856]
	ldr	x8, [sp, #26880]
	ldr	x17, [sp, #26896]
	eor	x10, x11, x10
	str	x12, [sp, #26848]
	ldr	x11, [sp, #27088]
	eor	x8, x8, x13
	str	x9, [sp, #26864]
	ldr	x9, [sp, #26888]
	ldr	x12, [sp, #27096]
	str	x8, [sp, #26880]
	eor	x9, x9, x11
	str	x10, [sp, #26872]
	eor	x8, x17, x12
	str	x9, [sp, #26888]
	str	x8, [sp, #26896]
	bl	_RNvCsndc0WgnAaH_9keccak2568keccak_f
	mov	x25, xzr
	str	xzr, [sp, #27104]
	b	.LBB3_31
.LBB3_36:
	add	x0, sp, #4, lsl #12
	add	x1, sp, #6, lsl #12
	mov	w2, #200
	add	x0, x0, #16
	add	x1, x1, #2192
	bl	memcpy
	cmp	x25, #137
	b.hs	.LBB3_89
	add	x0, sp, #6, lsl #12
	mov	x1, x22
	mov	x2, x25
	add	x0, x0, #144
	mov	w26, w19
	str	xzr, [sp, #24848]
	str	xzr, [sp, #24840]
	str	xzr, [sp, #24832]
	str	xzr, [sp, #24824]
	str	xzr, [sp, #24816]
	str	xzr, [sp, #24808]
	str	xzr, [sp, #24800]
	str	xzr, [sp, #24792]
	str	xzr, [sp, #24784]
	str	xzr, [sp, #24776]
	str	xzr, [sp, #24768]
	str	xzr, [sp, #24760]
	str	xzr, [sp, #24752]
	str	xzr, [sp, #24744]
	str	xzr, [sp, #24736]
	str	xzr, [sp, #24728]
	str	xzr, [sp, #24720]
	bl	memcpy
	add	x9, sp, #6, lsl #12
	add	x23, sp, #5, lsl #12
	ldr	x0, [sp, #16408]
	add	x9, x9, #144
	add	x23, x23, #1168
	ldrb	w8, [x9, x25]
	eor	w8, w8, #0x1
	strb	w8, [x9, x25]
	ldr	x8, [sp, #16400]
	ldr	x10, [sp, #24720]
	ldr	x11, [sp, #24728]
	ldr	x12, [sp, #24736]
	ldrb	w9, [x23, #3207]
	ldr	x13, [sp, #24744]
	eor	x8, x8, x10
	ldr	x10, [sp, #16416]
	eor	x11, x0, x11
	ldr	x0, [sp, #16424]
	ldr	x14, [sp, #24752]
	ldr	x15, [sp, #24760]
	str	x8, [sp, #16400]
	eor	x8, x10, x12
	ldr	x10, [sp, #16432]
	ldr	x12, [sp, #16440]
	eor	w9, w9, #0x80
	str	x11, [sp, #16408]
	eor	x11, x0, x13
	ldr	x16, [sp, #24768]
	ldr	x17, [sp, #24776]
	strb	w9, [x23, #3207]
	ldr	x9, [sp, #24784]
	ldr	x13, [sp, #16464]
	str	x8, [sp, #16416]
	eor	x8, x10, x14
	ldr	x10, [sp, #16448]
	str	x11, [sp, #16424]
	eor	x11, x12, x15
	ldr	x12, [sp, #16456]
	ldr	x14, [sp, #24808]
	str	x11, [sp, #16440]
	ldr	x11, [sp, #16488]
	str	x8, [sp, #16432]
	eor	x8, x10, x16
	eor	x12, x12, x17
	eor	x9, x13, x9
	ldr	x18, [sp, #24792]
	ldr	x1, [sp, #24800]
	ldr	x10, [sp, #16472]
	ldr	x13, [sp, #16480]
	str	x8, [sp, #16448]
	ldr	x8, [sp, #24816]
	str	x12, [sp, #16456]
	ldr	x12, [sp, #16496]
	eor	x11, x11, x14
	ldr	x14, [sp, #24824]
	str	x9, [sp, #16464]
	ldr	x9, [sp, #16504]
	eor	x10, x10, x18
	eor	x13, x13, x1
	eor	x8, x12, x8
	str	x10, [sp, #16472]
	ldr	x10, [sp, #24832]
	eor	x9, x9, x14
	str	x13, [sp, #16480]
	ldr	x12, [sp, #16512]
	ldr	x13, [sp, #24840]
	str	x11, [sp, #16488]
	ldr	x11, [sp, #16520]
	str	x8, [sp, #16496]
	ldr	x8, [sp, #24848]
	add	x0, sp, #4, lsl #12
	str	x9, [sp, #16504]
	ldr	x9, [sp, #16528]
	eor	x10, x12, x10
	eor	x11, x11, x13
	add	x0, x0, #16
	str	x10, [sp, #16512]
	eor	x8, x9, x8
	str	x11, [sp, #16520]
	str	x8, [sp, #16528]
	bl	_RNvCsndc0WgnAaH_9keccak2568keccak_f
	ldr	x8, [sp, #16408]
	ldr	x9, [sp, #16400]
	mov	x19, x27
	ldr	x27, [sp, #408]
	cmp	x28, #10
	mov	w25, #50331648
	str	x8, [sp, #24728]
	str	x9, [sp, #24720]
	str	x9, [sp, #20624]
	str	x8, [sp, #20632]
	b.ne	.LBB3_22
	add	x8, sp, #6, lsl #12
	ldr	x9, [sp, #20624]
	ldr	x10, [sp, #20632]
	add	x8, x8, #3248
	ldr	x24, [sp, #400]
	add	x8, x8, x19, lsl #4
	add	x19, x19, #1
	cmp	x19, #24
	stp	x9, x10, [x8]
	add	x9, sp, #2, lsl #12
	mov	w8, #176
	add	x9, x9, #52
	b.ne	.LBB3_21
	add	x0, sp, #4, lsl #12
	mov	w8, #67108864
	mov	w1, wzr
	add	x0, x0, #16
	mov	w2, #344
	str	xzr, [sp, #24720]
	str	x27, [sp, #24728]
	str	w8, [x23, #3088]
	str	w26, [x23, #3092]
	str	xzr, [sp, #24744]
	bl	memset
	add	x0, sp, #4, lsl #12
	add	x1, sp, #2, lsl #12
	mov	w2, #16
	add	x0, x0, #16
	add	x1, x1, #16
	mov	w22, #16
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	add	x0, sp, #4, lsl #12
	add	x1, sp, #6, lsl #12
	mov	w2, #32
	add	x0, x0, #16
	add	x1, x1, #144
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	add	x0, sp, #6, lsl #12
	add	x1, sp, #4, lsl #12
	mov	w2, #344
	add	x0, x0, #2192
	add	x1, x1, #16
	add	x19, sp, #6, lsl #12
	add	x19, x19, #2192
	bl	memcpy
	add	x0, sp, #6, lsl #12
	add	x1, sp, #6, lsl #12
	mov	w2, #384
	add	x0, x0, #2192
	add	x1, x1, #3248
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	add	x0, sp, #4, lsl #12
	add	x1, sp, #6, lsl #12
	add	x20, sp, #4, lsl #12
	add	x0, x0, #16
	add	x1, x1, #2192
	add	x20, x20, #16
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher8finalize
	ldr	x8, [sp, #16400]
	ldr	x9, [sp, #16408]
	add	x25, x20, #200
	add	x20, sp, #5, lsl #12
	ldr	x11, [sp, #392]
	mov	x10, xzr
	str	x8, [sp, #27792]
	add	x21, x19, #200
	orr	x23, x19, #0x1
	mov	w12, #4656
	adrp	x8, .Lanon.bee145f0cb2eac5728ff95be1b200579.2
	add	x8, x8, :lo12:.Lanon.bee145f0cb2eac5728ff95be1b200579.2
	mov	w13, #8
	mov	w14, #117440512
	add	x20, x20, #1168
	mov	w26, #136
	str	x9, [sp, #27800]
	str	x23, [sp]
.LBB3_40:
	cmp	x10, #1
	mov	x16, x10
	ldr	x15, [x8, x10, lsl #3]
	csel	x8, x13, x22, eq
	cmp	x10, #0
	ldr	x10, [sp, #384]
	csel	x8, xzr, x8, eq
	mov	x9, #-1
	add	x0, sp, #4, lsl #12
	lsr	x8, x10, x8
	lsl	x9, x9, x15
	rev	w13, w16
	ldr	w19, [x11, #1024]
	add	x12, x12, #1028
	add	x0, x0, #16
	lsr	x10, x8, x15
	bic	x8, x8, x9
	mov	w1, wzr
	stp	x8, x15, [sp, #32]
	rev	w9, w8
	mov	w2, #344
	rev	x8, x10
	str	wzr, [x20, #3076]
	str	x8, [sp, #424]
	str	x8, [sp, #24728]
	add	x8, x16, #1
	str	w14, [x20, #3088]
	str	w13, [sp, #416]
	str	w13, [x20, #3072]
	str	w9, [sp, #408]
	str	w9, [x20, #3092]
	str	x11, [sp, #392]
	stp	x12, x16, [sp, #16]
	str	x8, [sp, #8]
	str	xzr, [sp, #24744]
	bl	memset
	add	x0, sp, #4, lsl #12
	add	x1, sp, #2, lsl #12
	mov	w2, #16
	add	x0, x0, #16
	add	x1, x1, #16
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	add	x0, sp, #4, lsl #12
	add	x1, sp, #6, lsl #12
	mov	w2, #32
	add	x0, x0, #16
	add	x1, x1, #144
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	add	x0, sp, #6, lsl #12
	add	x1, sp, #4, lsl #12
	mov	w2, #344
	add	x0, x0, #2192
	add	x1, x1, #16
	bl	memcpy
	add	x0, sp, #6, lsl #12
	add	x1, sp, #6, lsl #12
	mov	w2, #16
	add	x0, x0, #2192
	add	x1, x1, #3216
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	add	x0, sp, #4, lsl #12
	add	x1, sp, #6, lsl #12
	mov	w2, #344
	add	x0, x0, #16
	add	x1, x1, #2192
	bl	memcpy
	add	x0, sp, #4, lsl #12
	add	x1, sp, #6, lsl #12
	rev	w8, w19
	add	x0, x0, #16
	add	x1, x1, #144
	mov	w2, #4
	str	w8, [x20, #3072]
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	add	x0, sp, #6, lsl #12
	add	x1, sp, #4, lsl #12
	add	x0, x0, #2192
	add	x1, x1, #16
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher8finalize
	ldr	x10, [sp, #26776]
	ldr	x9, [sp, #26768]
	mov	x8, xzr
	mov	x11, x23
	rev	x9, x9
	rev	x10, x10
.LBB3_41:
	add	x14, x8, #2
	eor	x12, x8, #0x7e
	lsl	x13, x9, #1
	eor	x14, x14, #0x7e
	mvn	w16, w12
	lsr	x17, x10, x12
	lsr	x18, x9, x12
	tst	x12, #0x40
	mvn	w12, w14
	add	x15, x8, #4
	lsl	x16, x13, x16
	lsr	x0, x10, x14
	lsl	x12, x13, x12
	eor	x15, x15, #0x7e
	orr	x16, x16, x17
	add	x17, x8, #6
	add	x8, x8, #8
	orr	x12, x12, x0
	mvn	w0, w15
	csel	x16, x18, x16, ne
	lsr	x18, x9, x14
	tst	x14, #0x40
	lsr	x14, x10, x15
	lsl	x0, x13, x0
	eor	x17, x17, #0x7e
	csel	x12, x18, x12, ne
	lsr	x18, x9, x15
	tst	x15, #0x40
	orr	x14, x0, x14
	mvn	w0, w17
	lsr	x15, x10, x17
	lsl	x13, x13, x0
	csel	x14, x18, x14, ne
	lsr	x18, x9, x17
	tst	x17, #0x40
	and	w12, w12, #0x3
	and	w14, w14, #0x3
	orr	x13, x13, x15
	and	w15, w16, #0x3
	strb	w12, [x11]
	csel	x13, x18, x13, ne
	sturb	w15, [x11, #-1]
	cmp	x8, #128
	and	w12, w13, #0x3
	strb	w14, [x11, #1]
	strb	w12, [x11, #2]
	add	x11, x11, #4
	b.ne	.LBB3_41
	add	x8, sp, #6, lsl #12
	add	x3, sp, #6, lsl #12
	add	x8, x8, #2192
	add	x3, x3, #2192
	ldrb	w8, [x8]
	ldrb	w9, [x3, #1]
	ldrb	w10, [x3, #2]
	ldrb	w11, [x3, #3]
	ldrb	w12, [x3, #4]
	ldrb	w13, [x3, #5]
	str	x8, [sp, #400]
	add	x8, x9, x8
	ldrb	w14, [x3, #7]
	stp	x10, x9, [sp, #360]
	add	x9, x10, x11
	add	x10, x12, x13
	stp	x12, x11, [sp, #344]
	ldrb	w11, [x3, #6]
	ldrb	w12, [x3, #8]
	add	x8, x8, x9
	ldrb	w15, [x3, #12]
	ldrb	w16, [x3, #13]
	stp	x11, x13, [sp, #328]
	ldrb	w13, [x3, #9]
	add	x9, x10, x11
	ldrb	w10, [x3, #10]
	add	x8, x8, x9
	add	x9, x14, x12
	ldrb	w11, [x3, #11]
	add	x9, x9, x13
	ldrb	w17, [x3, #17]
	stp	x10, x13, [sp, #296]
	ldrb	w13, [x3, #16]
	add	x9, x9, x10
	stp	x12, x14, [sp, #312]
	ldrb	w12, [x3, #14]
	ldrb	w18, [x3, #18]
	add	x8, x8, x9
	add	x9, x11, x15
	ldrb	w14, [x3, #15]
	ldrb	w0, [x3, #19]
	stp	x15, x11, [sp, #280]
	ldrb	w11, [x3, #22]
	ldrb	w15, [x3, #23]
	add	x9, x9, x16
	add	x10, x13, x17
	ldrb	w1, [x3, #20]
	stp	x12, x16, [sp, #264]
	ldrb	w16, [x3, #24]
	add	x9, x9, x12
	add	x10, x10, x18
	ldrb	w4, [x3, #25]
	add	x9, x9, x14
	add	x10, x10, x0
	stp	x15, x11, [sp, #192]
	add	x11, x11, x15
	ldrb	w2, [x3, #21]
	stp	x17, x13, [sp, #240]
	ldrb	w13, [x3, #26]
	ldrb	w17, [x3, #27]
	add	x8, x8, x9
	add	x9, x10, x1
	add	x10, x11, x16
	ldrb	w11, [x3, #28]
	add	x10, x10, x4
	add	x9, x9, x2
	stp	x17, x13, [sp, #160]
	add	x10, x10, x13
	ldrb	w12, [x3, #29]
	ldrb	w13, [x3, #30]
	str	x14, [sp, #256]
	add	x8, x8, x9
	add	x9, x10, x17
	ldrb	w14, [x3, #31]
	stp	x12, x11, [sp, #144]
	add	x9, x9, x11
	ldrb	w11, [x3, #32]
	add	x10, x12, x13
	add	x8, x8, x9
	add	x9, x10, x14
	ldrb	w12, [x3, #33]
	ldrb	w10, [x3, #37]
	stp	x10, x11, [sp, #112]
	add	x9, x9, x11
	ldrb	w11, [x3, #38]
	add	x9, x9, x12
	stp	x14, x13, [sp, #128]
	ldrb	w13, [x3, #40]
	stp	x12, x11, [sp, #96]
	ldrb	w12, [x3, #39]
	ldrb	w14, [x3, #34]
	add	x10, x10, x11
	ldrb	w11, [x3, #41]
	add	x10, x10, x12
	stp	x4, x16, [sp, #176]
	ldrb	w15, [x3, #35]
	stp	x13, x12, [sp, #80]
	add	x10, x10, x13
	ldrb	w12, [x3, #42]
	ldrb	w4, [x3, #46]
	ldrb	w5, [x3, #47]
	add	x9, x9, x14
	add	x10, x10, x11
	ldrb	w20, [x3, #36]
	ldrb	w6, [x3, #43]
	ldrb	w7, [x3, #48]
	add	x9, x9, x15
	stp	x12, x11, [sp, #48]
	add	x10, x10, x12
	ldrb	w22, [x3, #44]
	ldrb	w19, [x3, #49]
	add	x11, x4, x5
	add	x9, x9, x20
	add	x10, x10, x6
	add	x11, x11, x7
	ldrb	w28, [x3, #45]
	ldrb	w23, [x3, #50]
	stp	x0, x18, [sp, #224]
	add	x18, x8, x9
	add	x8, x10, x22
	add	x9, x11, x19
	ldrb	w30, [x3, #51]
	add	x0, x8, x28
	add	x8, x9, x23
	ldrb	w9, [x3, #52]
	ldrb	w24, [x3, #56]
	ldrb	w27, [x3, #57]
	add	x10, x8, x30
	ldrb	w11, [x3, #53]
	ldrb	w8, [x3, #58]
	add	x12, x10, x9
	ldrb	w10, [x3, #59]
	add	x13, x24, x27
	stp	x15, x14, [sp, #64]
	add	x15, x12, x11
	add	x13, x13, x8
	ldrb	w12, [x3, #60]
	ldrb	w16, [x3, #54]
	add	x14, x13, x10
	ldrb	w13, [x3, #61]
	stp	x2, x1, [sp, #208]
	add	x1, x14, x12
	ldrb	w17, [x3, #55]
	ldrb	w14, [x3, #62]
	add	x2, x15, x16
	add	x1, x1, x13
	ldrb	w15, [x3, #63]
	add	x18, x18, x0
	add	x0, x2, x17
	add	x1, x1, x14
	add	x18, x18, x0
	add	x0, x1, x15
	add	x18, x18, x0
	cmp	x18, #128
	b.ne	.LBB3_91
	add	x18, sp, #5, lsl #12
	ldr	x1, [sp, #400]
	mov	x0, xzr
	add	x18, x18, #1168
	strb	w1, [x18, #2048]
	ldp	x1, x2, [sp, #360]
	strb	w8, [x18, #2106]
	ldr	x8, [sp, #392]
	strb	w20, [x18, #2084]
	strb	w1, [x18, #2050]
	ldp	x1, x3, [sp, #344]
	strb	w2, [x18, #2049]
	strb	w6, [x18, #2091]
	strb	w1, [x18, #2052]
	ldr	x1, [sp, #336]
	strb	w3, [x18, #2051]
	strb	w1, [x18, #2053]
	ldr	x1, [sp, #328]
	strb	w22, [x18, #2092]
	strb	w1, [x18, #2054]
	ldr	x1, [sp, #320]
	strb	w28, [x18, #2093]
	strb	w1, [x18, #2055]
	ldr	x1, [sp, #312]
	strb	w4, [x18, #2094]
	strb	w1, [x18, #2056]
	ldr	x1, [sp, #304]
	strb	w5, [x18, #2095]
	strb	w1, [x18, #2057]
	ldr	x1, [sp, #296]
	strb	w7, [x18, #2096]
	strb	w1, [x18, #2058]
	ldr	x1, [sp, #288]
	strb	w19, [x18, #2097]
	strb	w1, [x18, #2059]
	ldr	x1, [sp, #280]
	strb	w23, [x18, #2098]
	strb	w1, [x18, #2060]
	ldr	x1, [sp, #272]
	strb	w30, [x18, #2099]
	strb	w1, [x18, #2061]
	ldr	x1, [sp, #264]
	strb	w9, [x18, #2100]
	strb	w1, [x18, #2062]
	ldr	x1, [sp, #256]
	strb	w11, [x18, #2101]
	strb	w1, [x18, #2063]
	ldr	x1, [sp, #248]
	strb	w16, [x18, #2102]
	strb	w1, [x18, #2064]
	ldr	x1, [sp, #240]
	strb	w17, [x18, #2103]
	strb	w1, [x18, #2065]
	ldr	x1, [sp, #232]
	strb	w24, [x18, #2104]
	strb	w1, [x18, #2066]
	ldr	x1, [sp, #224]
	strb	w27, [x18, #2105]
	strb	w1, [x18, #2067]
	ldr	x1, [sp, #216]
	strb	w10, [x18, #2107]
	strb	w1, [x18, #2068]
	ldr	x1, [sp, #208]
	strb	w12, [x18, #2108]
	strb	w1, [x18, #2069]
	ldr	x1, [sp, #200]
	strb	w13, [x18, #2109]
	strb	w1, [x18, #2070]
	ldr	x1, [sp, #192]
	strb	w14, [x18, #2110]
	strb	w1, [x18, #2071]
	ldr	x1, [sp, #184]
	strb	w15, [x18, #2111]
	strb	w1, [x18, #2072]
	ldr	x1, [sp, #176]
	strb	w1, [x18, #2073]
	ldr	x1, [sp, #168]
	strb	w1, [x18, #2074]
	ldr	x1, [sp, #160]
	strb	w1, [x18, #2075]
	ldr	x1, [sp, #152]
	strb	w1, [x18, #2076]
	ldr	x1, [sp, #144]
	strb	w1, [x18, #2077]
	ldr	x1, [sp, #136]
	strb	w1, [x18, #2078]
	ldr	x1, [sp, #128]
	strb	w1, [x18, #2079]
	ldr	x1, [sp, #120]
	strb	w1, [x18, #2080]
	ldr	x1, [sp, #96]
	strb	w1, [x18, #2081]
	ldr	x1, [sp, #72]
	strb	w1, [x18, #2082]
	ldr	x1, [sp, #64]
	strb	w1, [x18, #2083]
	ldr	x1, [sp, #112]
	strb	w1, [x18, #2085]
	ldr	x1, [sp, #104]
	strb	w1, [x18, #2086]
	ldr	x1, [sp, #88]
	strb	w1, [x18, #2087]
	ldr	x1, [sp, #80]
	strb	w1, [x18, #2088]
	ldr	x1, [sp, #56]
	strb	w1, [x18, #2089]
	ldr	x1, [sp, #48]
	strb	w1, [x18, #2090]
	b	.LBB3_45
.LBB3_44:
	add	x8, sp, #6, lsl #12
	ldr	x9, [sp, #15984]
	ldr	x10, [sp, #15992]
	add	x8, x8, #3648
	add	x0, x28, #1
	add	x8, x8, x28, lsl #4
	cmp	x0, #64
	stp	x9, x10, [x8]
	ldr	x8, [sp, #392]
	b.eq	.LBB3_63
.LBB3_45:
	add	x8, x8, x0, lsl #4
	add	x9, sp, #5, lsl #12
	add	x22, sp, #5, lsl #12
	add	x9, x9, #3216
	mov	x28, x0
	add	x22, x22, #1168
	ldrb	w19, [x9, x0]
	ldp	x9, x8, [x8]
	cmp	x19, #2
	str	x9, [sp, #15984]
	str	x8, [sp, #15992]
	b.hi	.LBB3_44
	lsl	w20, w28, #24
.LBB3_47:
	ldr	x8, [sp, #15984]
	ldr	x9, [sp, #15992]
	add	x0, sp, #4, lsl #12
	add	x0, x0, #16
	mov	w1, wzr
	mov	w2, #344
	str	x8, [sp, #20624]
	ldr	w8, [sp, #416]
	str	x19, [sp, #20640]
	stp	w8, wzr, [x22]
	ldr	x8, [sp, #424]
	str	x9, [sp, #20632]
	str	x8, [sp, #21656]
	ldr	w8, [sp, #408]
	stp	wzr, w8, [x22, #16]
	rev	w8, w19
	stp	w20, w8, [x22, #24]
	bl	memset
	ldr	x8, [sp, #16736]
	ldr	x9, [sp, #8208]
	ldr	x10, [sp, #8216]
	add	x0, x8, #16
	stp	x9, x10, [x25]
	cmp	x0, #136
	str	x0, [sp, #16736]
	b.ne	.LBB3_49
	ldr	x9, [sp, #16600]
	ldr	x14, [sp, #16400]
	ldr	x10, [sp, #16608]
	ldr	x15, [sp, #16408]
	ldr	x8, [sp, #16616]
	ldr	x16, [sp, #16624]
	eor	x9, x14, x9
	ldr	x14, [sp, #16424]
	ldr	x12, [sp, #16632]
	eor	x10, x15, x10
	str	x9, [sp, #16400]
	ldr	x9, [sp, #16416]
	str	x10, [sp, #16408]
	ldr	x10, [sp, #16432]
	ldr	x13, [sp, #16640]
	eor	x8, x9, x8
	eor	x9, x14, x16
	ldr	x11, [sp, #16648]
	str	x8, [sp, #16416]
	ldr	x8, [sp, #16440]
	ldr	x15, [sp, #16656]
	str	x9, [sp, #16424]
	eor	x9, x10, x12
	ldr	x10, [sp, #16448]
	eor	x8, x8, x13
	ldr	x18, [sp, #16664]
	ldr	x12, [sp, #16456]
	ldr	x13, [sp, #16464]
	ldr	x14, [sp, #16672]
	ldr	x0, [sp, #16472]
	str	x8, [sp, #16440]
	eor	x8, x10, x11
	ldr	x16, [sp, #16680]
	eor	x10, x13, x18
	eor	x11, x0, x14
	add	x0, sp, #4, lsl #12
	add	x0, x0, #16
	str	x9, [sp, #16432]
	eor	x9, x12, x15
	ldr	x13, [sp, #16688]
	str	x8, [sp, #16448]
	ldr	x8, [sp, #16488]
	ldr	x12, [sp, #16480]
	ldr	x14, [sp, #16696]
	str	x9, [sp, #16456]
	eor	x8, x8, x13
	ldr	x9, [sp, #16496]
	str	x10, [sp, #16464]
	eor	x12, x12, x16
	ldr	x10, [sp, #16704]
	str	x11, [sp, #16472]
	eor	x9, x9, x14
	ldr	x11, [sp, #16504]
	ldr	x13, [sp, #16712]
	str	x8, [sp, #16488]
	ldr	x8, [sp, #16512]
	ldr	x17, [sp, #16528]
	eor	x10, x11, x10
	str	x12, [sp, #16480]
	ldr	x11, [sp, #16720]
	eor	x8, x8, x13
	str	x9, [sp, #16496]
	ldr	x9, [sp, #16520]
	ldr	x12, [sp, #16728]
	str	x8, [sp, #16512]
	eor	x9, x9, x11
	str	x10, [sp, #16504]
	eor	x8, x17, x12
	str	x9, [sp, #16520]
	str	x8, [sp, #16528]
	bl	_RNvCsndc0WgnAaH_9keccak2568keccak_f
	mov	x0, xzr
	str	xzr, [sp, #16736]
.LBB3_49:
	add	x22, sp, #5, lsl #12
	add	x19, x19, #1
	mov	w24, #32
	add	x22, x22, #1168
	b	.LBB3_51
.LBB3_50:
	sub	x24, x24, x23
	add	x22, x22, x23
	cbz	x24, .LBB3_55
.LBB3_51:
	sub	x8, x26, x0
	cmp	x24, x8
	csel	x23, x24, x8, lo
	add	x1, x23, x0
	cmp	x1, x0
	b.lo	.LBB3_87
	cmp	x1, #137
	b.hs	.LBB3_87
	add	x0, x25, x0
	mov	x1, x22
	mov	x2, x23
	bl	memcpy
	ldr	x8, [sp, #16736]
	add	x0, x8, x23
	cmp	x0, #136
	str	x0, [sp, #16736]
	b.ne	.LBB3_50
	ldr	x9, [sp, #16600]
	ldr	x14, [sp, #16400]
	ldr	x10, [sp, #16608]
	ldr	x15, [sp, #16408]
	ldr	x8, [sp, #16616]
	ldr	x16, [sp, #16624]
	eor	x9, x14, x9
	ldr	x14, [sp, #16424]
	ldr	x12, [sp, #16632]
	eor	x10, x15, x10
	str	x9, [sp, #16400]
	ldr	x9, [sp, #16416]
	str	x10, [sp, #16408]
	ldr	x10, [sp, #16432]
	ldr	x13, [sp, #16640]
	eor	x8, x9, x8
	eor	x9, x14, x16
	ldr	x11, [sp, #16648]
	str	x8, [sp, #16416]
	ldr	x8, [sp, #16440]
	ldr	x15, [sp, #16656]
	str	x9, [sp, #16424]
	eor	x9, x10, x12
	ldr	x10, [sp, #16448]
	eor	x8, x8, x13
	ldr	x18, [sp, #16664]
	ldr	x12, [sp, #16456]
	ldr	x13, [sp, #16464]
	ldr	x14, [sp, #16672]
	ldr	x0, [sp, #16472]
	str	x8, [sp, #16440]
	eor	x8, x10, x11
	ldr	x16, [sp, #16680]
	eor	x10, x13, x18
	eor	x11, x0, x14
	add	x0, sp, #4, lsl #12
	add	x0, x0, #16
	str	x9, [sp, #16432]
	eor	x9, x12, x15
	ldr	x13, [sp, #16688]
	str	x8, [sp, #16448]
	ldr	x8, [sp, #16488]
	ldr	x12, [sp, #16480]
	ldr	x14, [sp, #16696]
	str	x9, [sp, #16456]
	eor	x8, x8, x13
	ldr	x9, [sp, #16496]
	str	x10, [sp, #16464]
	eor	x12, x12, x16
	ldr	x10, [sp, #16704]
	str	x11, [sp, #16472]
	eor	x9, x9, x14
	ldr	x11, [sp, #16504]
	ldr	x13, [sp, #16712]
	str	x8, [sp, #16488]
	ldr	x8, [sp, #16512]
	ldr	x17, [sp, #16528]
	eor	x10, x11, x10
	str	x12, [sp, #16480]
	ldr	x11, [sp, #16720]
	eor	x8, x8, x13
	str	x9, [sp, #16496]
	ldr	x9, [sp, #16520]
	ldr	x12, [sp, #16728]
	str	x8, [sp, #16512]
	eor	x9, x9, x11
	str	x10, [sp, #16504]
	eor	x8, x17, x12
	str	x9, [sp, #16520]
	str	x8, [sp, #16528]
	bl	_RNvCsndc0WgnAaH_9keccak2568keccak_f
	mov	x0, xzr
	str	xzr, [sp, #16736]
	b	.LBB3_50
.LBB3_55:
	add	x0, sp, #6, lsl #12
	add	x1, sp, #4, lsl #12
	mov	w2, #344
	add	x0, x0, #2192
	add	x1, x1, #16
	bl	memcpy
	ldr	x24, [sp, #27104]
	add	x22, sp, #5, lsl #12
	mov	w27, #16
	add	x22, x22, #144
	b	.LBB3_57
.LBB3_56:
	sub	x27, x27, x23
	add	x22, x22, x23
	cbz	x27, .LBB3_61
.LBB3_57:
	sub	x8, x26, x24
	cmp	x27, x8
	csel	x23, x27, x8, lo
	add	x1, x23, x24
	cmp	x1, x24
	b.lo	.LBB3_90
	cmp	x1, #137
	b.hs	.LBB3_90
	add	x0, x21, x24
	mov	x1, x22
	mov	x2, x23
	bl	memcpy
	ldr	x8, [sp, #27104]
	add	x24, x8, x23
	cmp	x24, #136
	str	x24, [sp, #27104]
	b.ne	.LBB3_56
	ldr	x9, [sp, #26968]
	ldr	x14, [sp, #26768]
	ldr	x10, [sp, #26976]
	ldr	x15, [sp, #26776]
	ldr	x8, [sp, #26984]
	ldr	x16, [sp, #26992]
	eor	x9, x14, x9
	ldr	x14, [sp, #26792]
	ldr	x12, [sp, #27000]
	eor	x10, x15, x10
	str	x9, [sp, #26768]
	ldr	x9, [sp, #26784]
	str	x10, [sp, #26776]
	ldr	x10, [sp, #26800]
	ldr	x13, [sp, #27008]
	eor	x8, x9, x8
	eor	x9, x14, x16
	ldr	x11, [sp, #27016]
	str	x8, [sp, #26784]
	ldr	x8, [sp, #26808]
	ldr	x15, [sp, #27024]
	str	x9, [sp, #26792]
	eor	x9, x10, x12
	ldr	x10, [sp, #26816]
	eor	x8, x8, x13
	ldr	x18, [sp, #27032]
	ldr	x12, [sp, #26824]
	ldr	x13, [sp, #26832]
	ldr	x14, [sp, #27040]
	ldr	x0, [sp, #26840]
	str	x8, [sp, #26808]
	eor	x8, x10, x11
	ldr	x16, [sp, #27048]
	eor	x10, x13, x18
	eor	x11, x0, x14
	add	x0, sp, #6, lsl #12
	add	x0, x0, #2192
	str	x9, [sp, #26800]
	eor	x9, x12, x15
	ldr	x13, [sp, #27056]
	str	x8, [sp, #26816]
	ldr	x8, [sp, #26856]
	ldr	x12, [sp, #26848]
	ldr	x14, [sp, #27064]
	str	x9, [sp, #26824]
	eor	x8, x8, x13
	ldr	x9, [sp, #26864]
	str	x10, [sp, #26832]
	eor	x12, x12, x16
	ldr	x10, [sp, #27072]
	str	x11, [sp, #26840]
	eor	x9, x9, x14
	ldr	x11, [sp, #26872]
	ldr	x13, [sp, #27080]
	str	x8, [sp, #26856]
	ldr	x8, [sp, #26880]
	ldr	x17, [sp, #26896]
	eor	x10, x11, x10
	str	x12, [sp, #26848]
	ldr	x11, [sp, #27088]
	eor	x8, x8, x13
	str	x9, [sp, #26864]
	ldr	x9, [sp, #26888]
	ldr	x12, [sp, #27096]
	str	x8, [sp, #26880]
	eor	x9, x9, x11
	str	x10, [sp, #26872]
	eor	x8, x17, x12
	str	x9, [sp, #26888]
	str	x8, [sp, #26896]
	bl	_RNvCsndc0WgnAaH_9keccak2568keccak_f
	mov	x24, xzr
	str	xzr, [sp, #27104]
	b	.LBB3_56
.LBB3_61:
	add	x0, sp, #4, lsl #12
	add	x1, sp, #6, lsl #12
	mov	w2, #200
	add	x0, x0, #16
	add	x1, x1, #2192
	bl	memcpy
	cmp	x24, #137
	b.hs	.LBB3_93
	add	x0, sp, #6, lsl #12
	mov	x1, x21
	mov	x2, x24
	add	x0, x0, #144
	str	xzr, [sp, #24848]
	str	xzr, [sp, #24840]
	str	xzr, [sp, #24832]
	str	xzr, [sp, #24824]
	str	xzr, [sp, #24816]
	str	xzr, [sp, #24808]
	str	xzr, [sp, #24800]
	str	xzr, [sp, #24792]
	str	xzr, [sp, #24784]
	str	xzr, [sp, #24776]
	str	xzr, [sp, #24768]
	str	xzr, [sp, #24760]
	str	xzr, [sp, #24752]
	str	xzr, [sp, #24744]
	str	xzr, [sp, #24736]
	str	xzr, [sp, #24728]
	str	xzr, [sp, #24720]
	bl	memcpy
	add	x9, sp, #6, lsl #12
	add	x22, sp, #5, lsl #12
	ldr	x0, [sp, #16408]
	add	x9, x9, #144
	add	x22, x22, #1168
	ldrb	w8, [x9, x24]
	eor	w8, w8, #0x1
	strb	w8, [x9, x24]
	ldr	x8, [sp, #16400]
	ldr	x10, [sp, #24720]
	ldr	x11, [sp, #24728]
	ldr	x12, [sp, #24736]
	ldrb	w9, [x22, #3207]
	ldr	x13, [sp, #24744]
	eor	x8, x8, x10
	ldr	x10, [sp, #16416]
	eor	x11, x0, x11
	ldr	x0, [sp, #16424]
	ldr	x14, [sp, #24752]
	ldr	x15, [sp, #24760]
	str	x8, [sp, #16400]
	eor	x8, x10, x12
	ldr	x10, [sp, #16432]
	ldr	x12, [sp, #16440]
	eor	w9, w9, #0x80
	str	x11, [sp, #16408]
	eor	x11, x0, x13
	ldr	x16, [sp, #24768]
	ldr	x17, [sp, #24776]
	strb	w9, [x22, #3207]
	ldr	x9, [sp, #24784]
	ldr	x13, [sp, #16464]
	str	x8, [sp, #16416]
	eor	x8, x10, x14
	ldr	x10, [sp, #16448]
	str	x11, [sp, #16424]
	eor	x11, x12, x15
	ldr	x12, [sp, #16456]
	ldr	x14, [sp, #24808]
	str	x11, [sp, #16440]
	ldr	x11, [sp, #16488]
	str	x8, [sp, #16432]
	eor	x8, x10, x16
	eor	x12, x12, x17
	eor	x9, x13, x9
	ldr	x18, [sp, #24792]
	ldr	x1, [sp, #24800]
	ldr	x10, [sp, #16472]
	ldr	x13, [sp, #16480]
	str	x8, [sp, #16448]
	ldr	x8, [sp, #24816]
	str	x12, [sp, #16456]
	ldr	x12, [sp, #16496]
	eor	x11, x11, x14
	ldr	x14, [sp, #24824]
	str	x9, [sp, #16464]
	ldr	x9, [sp, #16504]
	eor	x10, x10, x18
	eor	x13, x13, x1
	eor	x8, x12, x8
	str	x10, [sp, #16472]
	ldr	x10, [sp, #24832]
	eor	x9, x9, x14
	str	x13, [sp, #16480]
	ldr	x12, [sp, #16512]
	ldr	x13, [sp, #24840]
	str	x11, [sp, #16488]
	ldr	x11, [sp, #16520]
	str	x8, [sp, #16496]
	ldr	x8, [sp, #24848]
	add	x0, sp, #4, lsl #12
	str	x9, [sp, #16504]
	ldr	x9, [sp, #16528]
	eor	x10, x12, x10
	eor	x11, x11, x13
	add	x0, x0, #16
	str	x10, [sp, #16512]
	eor	x8, x9, x8
	str	x11, [sp, #16520]
	str	x8, [sp, #16528]
	bl	_RNvCsndc0WgnAaH_9keccak2568keccak_f
	ldr	x8, [sp, #16408]
	ldr	x9, [sp, #16400]
	cmp	x19, #3
	str	x8, [sp, #24728]
	str	x9, [sp, #24720]
	str	x9, [sp, #15984]
	str	x8, [sp, #15992]
	b.ne	.LBB3_47
	b	.LBB3_44
.LBB3_63:
	add	x8, sp, #5, lsl #12
	ldr	w9, [sp, #416]
	add	x0, sp, #4, lsl #12
	add	x8, x8, #1168
	add	x0, x0, #16
	mov	w1, wzr
	str	w9, [x8, #3072]
	mov	w9, #16777216
	mov	w2, #344
	str	w9, [x8, #3088]
	ldr	w9, [sp, #408]
	str	wzr, [x8, #3076]
	str	w9, [x8, #3092]
	ldr	x8, [sp, #424]
	str	xzr, [sp, #24744]
	str	x8, [sp, #24728]
	bl	memset
	add	x0, sp, #4, lsl #12
	add	x1, sp, #2, lsl #12
	mov	w2, #16
	add	x0, x0, #16
	add	x1, x1, #16
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	add	x0, sp, #4, lsl #12
	add	x1, sp, #6, lsl #12
	mov	w2, #32
	add	x0, x0, #16
	add	x1, x1, #144
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	add	x0, sp, #6, lsl #12
	add	x1, sp, #4, lsl #12
	mov	w2, #344
	add	x0, x0, #2192
	add	x1, x1, #16
	bl	memcpy
	add	x0, sp, #6, lsl #12
	add	x1, sp, #6, lsl #12
	mov	w2, #1024
	add	x0, x0, #2192
	add	x1, x1, #3648
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	add	x0, sp, #5, lsl #12
	add	x1, sp, #6, lsl #12
	add	x0, x0, #2192
	add	x1, x1, #2192
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher8finalize
	ldr	x11, [sp, #24]
	mov	w22, #16
	mov	w13, #8
	ldr	x8, [sp, #22680]
	ldr	x9, [sp, #22672]
	cmp	x11, #1
	csel	x10, x13, x22, eq
	cmp	x11, #0
	str	x8, [sp, #27816]
	csel	x0, xzr, x10, eq
	ldr	x10, [sp, #40]
	str	x9, [sp, #27808]
	str	x9, [sp, #15984]
	add	x1, x0, x10
	str	x8, [sp, #15992]
	cmp	x1, x0
	b.lo	.LBB3_96
	cmp	x1, #27
	b.hs	.LBB3_96
	ldr	x8, [sp, #40]
	cbz	x8, .LBB3_84
	ldr	x10, [sp, #376]
	ldr	x8, [sp, #15984]
	lsl	w27, w11, #24
	ldr	x9, [sp, #15992]
	add	x20, sp, #5, lsl #12
	mov	x19, xzr
	add	x24, x10, x0, lsl #4
	add	x20, x20, #1168
	str	x8, [sp, #20624]
	str	x9, [sp, #20632]
.LBB3_67:
	mov	w8, #1
	ldr	x10, [sp, #20632]
	ldr	x12, [sp, #32]
	lsl	x8, x8, x19
	ldr	x9, [sp, #20624]
	add	x11, x24, x19, lsl #4
	str	x10, [sp, #21656]
	add	x10, sp, #5, lsl #12
	add	x19, x19, #1
	tst	x8, x12
	add	x10, x10, #1168
	str	x9, [sp, #21648]
	csel	x8, x10, x11, eq
	csel	x10, x11, x10, eq
	add	x0, sp, #4, lsl #12
	ldp	x9, x8, [x8]
	add	x0, x0, #16
	mov	w1, wzr
	mov	w2, #344
	str	w27, [x20, #2048]
	str	wzr, [x20, #2052]
	str	x9, [sp, #22672]
	ldp	x9, x10, [x10]
	str	x8, [sp, #22680]
	add	x8, sp, #5, lsl #12
	add	x8, x8, #2192
	stp	x9, x10, [x8, #16]
	lsr	x8, x12, x19
	ldr	x9, [sp, #424]
	mov	w10, #33554432
	str	x9, [sp, #23704]
	rev	w9, w19
	rev	w8, w8
	str	x10, [sp, #23712]
	str	w9, [x20, #2072]
	str	w8, [x20, #2076]
	bl	memset
	ldr	x8, [sp, #16736]
	ldr	x9, [sp, #8208]
	ldr	x10, [sp, #8216]
	add	x0, x8, #16
	stp	x9, x10, [x25]
	cmp	x0, #136
	str	x0, [sp, #16736]
	b.ne	.LBB3_69
	ldr	x9, [sp, #16600]
	ldr	x14, [sp, #16400]
	ldr	x10, [sp, #16608]
	ldr	x15, [sp, #16408]
	ldr	x8, [sp, #16616]
	ldr	x16, [sp, #16624]
	eor	x9, x14, x9
	ldr	x14, [sp, #16424]
	ldr	x12, [sp, #16632]
	eor	x10, x15, x10
	str	x9, [sp, #16400]
	ldr	x9, [sp, #16416]
	str	x10, [sp, #16408]
	ldr	x10, [sp, #16432]
	ldr	x13, [sp, #16640]
	eor	x8, x9, x8
	eor	x9, x14, x16
	ldr	x11, [sp, #16648]
	str	x8, [sp, #16416]
	ldr	x8, [sp, #16440]
	ldr	x15, [sp, #16656]
	str	x9, [sp, #16424]
	eor	x9, x10, x12
	ldr	x10, [sp, #16448]
	eor	x8, x8, x13
	ldr	x18, [sp, #16664]
	ldr	x12, [sp, #16456]
	ldr	x13, [sp, #16464]
	ldr	x14, [sp, #16672]
	ldr	x0, [sp, #16472]
	str	x8, [sp, #16440]
	eor	x8, x10, x11
	ldr	x16, [sp, #16680]
	eor	x10, x13, x18
	eor	x11, x0, x14
	add	x0, sp, #4, lsl #12
	add	x0, x0, #16
	str	x9, [sp, #16432]
	eor	x9, x12, x15
	ldr	x13, [sp, #16688]
	str	x8, [sp, #16448]
	ldr	x8, [sp, #16488]
	ldr	x12, [sp, #16480]
	ldr	x14, [sp, #16696]
	str	x9, [sp, #16456]
	eor	x8, x8, x13
	ldr	x9, [sp, #16496]
	str	x10, [sp, #16464]
	eor	x12, x12, x16
	ldr	x10, [sp, #16704]
	str	x11, [sp, #16472]
	eor	x9, x9, x14
	ldr	x11, [sp, #16504]
	ldr	x13, [sp, #16712]
	str	x8, [sp, #16488]
	ldr	x8, [sp, #16512]
	ldr	x17, [sp, #16528]
	eor	x10, x11, x10
	str	x12, [sp, #16480]
	ldr	x11, [sp, #16720]
	eor	x8, x8, x13
	str	x9, [sp, #16496]
	ldr	x9, [sp, #16520]
	ldr	x12, [sp, #16728]
	str	x8, [sp, #16512]
	eor	x9, x9, x11
	str	x10, [sp, #16504]
	eor	x8, x17, x12
	str	x9, [sp, #16520]
	str	x8, [sp, #16528]
	bl	_RNvCsndc0WgnAaH_9keccak2568keccak_f
	mov	x0, xzr
	str	xzr, [sp, #16736]
.LBB3_69:
	add	x20, sp, #5, lsl #12
	mov	w23, #32
	add	x20, x20, #3216
	b	.LBB3_71
.LBB3_70:
	sub	x23, x23, x22
	add	x20, x20, x22
	cbz	x23, .LBB3_75
.LBB3_71:
	sub	x8, x26, x0
	cmp	x23, x8
	csel	x22, x23, x8, lo
	add	x1, x22, x0
	cmp	x1, x0
	b.lo	.LBB3_87
	cmp	x1, #137
	b.hs	.LBB3_87
	add	x0, x25, x0
	mov	x1, x20
	mov	x2, x22
	bl	memcpy
	ldr	x8, [sp, #16736]
	add	x0, x8, x22
	cmp	x0, #136
	str	x0, [sp, #16736]
	b.ne	.LBB3_70
	ldr	x9, [sp, #16600]
	ldr	x14, [sp, #16400]
	ldr	x10, [sp, #16608]
	ldr	x15, [sp, #16408]
	ldr	x8, [sp, #16616]
	ldr	x16, [sp, #16624]
	eor	x9, x14, x9
	ldr	x14, [sp, #16424]
	ldr	x12, [sp, #16632]
	eor	x10, x15, x10
	str	x9, [sp, #16400]
	ldr	x9, [sp, #16416]
	str	x10, [sp, #16408]
	ldr	x10, [sp, #16432]
	ldr	x13, [sp, #16640]
	eor	x8, x9, x8
	eor	x9, x14, x16
	ldr	x11, [sp, #16648]
	str	x8, [sp, #16416]
	ldr	x8, [sp, #16440]
	ldr	x15, [sp, #16656]
	str	x9, [sp, #16424]
	eor	x9, x10, x12
	ldr	x10, [sp, #16448]
	eor	x8, x8, x13
	ldr	x18, [sp, #16664]
	ldr	x12, [sp, #16456]
	ldr	x13, [sp, #16464]
	ldr	x14, [sp, #16672]
	ldr	x0, [sp, #16472]
	str	x8, [sp, #16440]
	eor	x8, x10, x11
	ldr	x16, [sp, #16680]
	eor	x10, x13, x18
	eor	x11, x0, x14
	add	x0, sp, #4, lsl #12
	add	x0, x0, #16
	str	x9, [sp, #16432]
	eor	x9, x12, x15
	ldr	x13, [sp, #16688]
	str	x8, [sp, #16448]
	ldr	x8, [sp, #16488]
	ldr	x12, [sp, #16480]
	ldr	x14, [sp, #16696]
	str	x9, [sp, #16456]
	eor	x8, x8, x13
	ldr	x9, [sp, #16496]
	str	x10, [sp, #16464]
	eor	x12, x12, x16
	ldr	x10, [sp, #16704]
	str	x11, [sp, #16472]
	eor	x9, x9, x14
	ldr	x11, [sp, #16504]
	ldr	x13, [sp, #16712]
	str	x8, [sp, #16488]
	ldr	x8, [sp, #16512]
	ldr	x17, [sp, #16528]
	eor	x10, x11, x10
	str	x12, [sp, #16480]
	ldr	x11, [sp, #16720]
	eor	x8, x8, x13
	str	x9, [sp, #16496]
	ldr	x9, [sp, #16520]
	ldr	x12, [sp, #16728]
	str	x8, [sp, #16512]
	eor	x9, x9, x11
	str	x10, [sp, #16504]
	eor	x8, x17, x12
	str	x9, [sp, #16520]
	str	x8, [sp, #16528]
	bl	_RNvCsndc0WgnAaH_9keccak2568keccak_f
	mov	x0, xzr
	str	xzr, [sp, #16736]
	b	.LBB3_70
.LBB3_75:
	add	x0, sp, #6, lsl #12
	add	x1, sp, #4, lsl #12
	mov	w2, #344
	add	x0, x0, #2192
	add	x1, x1, #16
	bl	memcpy
	ldr	x23, [sp, #27104]
	add	x20, sp, #5, lsl #12
	mov	w28, #32
	add	x20, x20, #2192
	b	.LBB3_77
.LBB3_76:
	sub	x28, x28, x22
	add	x20, x20, x22
	cbz	x28, .LBB3_81
.LBB3_77:
	sub	x8, x26, x23
	cmp	x28, x8
	csel	x22, x28, x8, lo
	add	x1, x22, x23
	cmp	x1, x23
	b.lo	.LBB3_94
	cmp	x1, #137
	b.hs	.LBB3_94
	add	x0, x21, x23
	mov	x1, x20
	mov	x2, x22
	bl	memcpy
	ldr	x8, [sp, #27104]
	add	x23, x8, x22
	cmp	x23, #136
	str	x23, [sp, #27104]
	b.ne	.LBB3_76
	ldr	x9, [sp, #26968]
	ldr	x14, [sp, #26768]
	ldr	x10, [sp, #26976]
	ldr	x15, [sp, #26776]
	ldr	x8, [sp, #26984]
	ldr	x16, [sp, #26992]
	eor	x9, x14, x9
	ldr	x14, [sp, #26792]
	ldr	x12, [sp, #27000]
	eor	x10, x15, x10
	str	x9, [sp, #26768]
	ldr	x9, [sp, #26784]
	str	x10, [sp, #26776]
	ldr	x10, [sp, #26800]
	ldr	x13, [sp, #27008]
	eor	x8, x9, x8
	eor	x9, x14, x16
	ldr	x11, [sp, #27016]
	str	x8, [sp, #26784]
	ldr	x8, [sp, #26808]
	ldr	x15, [sp, #27024]
	str	x9, [sp, #26792]
	eor	x9, x10, x12
	ldr	x10, [sp, #26816]
	eor	x8, x8, x13
	ldr	x18, [sp, #27032]
	ldr	x12, [sp, #26824]
	ldr	x13, [sp, #26832]
	ldr	x14, [sp, #27040]
	ldr	x0, [sp, #26840]
	str	x8, [sp, #26808]
	eor	x8, x10, x11
	ldr	x16, [sp, #27048]
	eor	x10, x13, x18
	eor	x11, x0, x14
	add	x0, sp, #6, lsl #12
	add	x0, x0, #2192
	str	x9, [sp, #26800]
	eor	x9, x12, x15
	ldr	x13, [sp, #27056]
	str	x8, [sp, #26816]
	ldr	x8, [sp, #26856]
	ldr	x12, [sp, #26848]
	ldr	x14, [sp, #27064]
	str	x9, [sp, #26824]
	eor	x8, x8, x13
	ldr	x9, [sp, #26864]
	str	x10, [sp, #26832]
	eor	x12, x12, x16
	ldr	x10, [sp, #27072]
	str	x11, [sp, #26840]
	eor	x9, x9, x14
	ldr	x11, [sp, #26872]
	ldr	x13, [sp, #27080]
	str	x8, [sp, #26856]
	ldr	x8, [sp, #26880]
	ldr	x17, [sp, #26896]
	eor	x10, x11, x10
	str	x12, [sp, #26848]
	ldr	x11, [sp, #27088]
	eor	x8, x8, x13
	str	x9, [sp, #26864]
	ldr	x9, [sp, #26888]
	ldr	x12, [sp, #27096]
	str	x8, [sp, #26880]
	eor	x9, x9, x11
	str	x10, [sp, #26872]
	eor	x8, x17, x12
	str	x9, [sp, #26888]
	str	x8, [sp, #26896]
	bl	_RNvCsndc0WgnAaH_9keccak2568keccak_f
	mov	x23, xzr
	str	xzr, [sp, #27104]
	b	.LBB3_76
.LBB3_81:
	add	x0, sp, #4, lsl #12
	add	x1, sp, #6, lsl #12
	mov	w2, #200
	add	x0, x0, #16
	add	x1, x1, #2192
	bl	memcpy
	cmp	x23, #137
	b.hs	.LBB3_95
	add	x0, sp, #6, lsl #12
	mov	x1, x21
	mov	x2, x23
	add	x0, x0, #144
	str	xzr, [sp, #24848]
	str	xzr, [sp, #24840]
	str	xzr, [sp, #24832]
	str	xzr, [sp, #24824]
	str	xzr, [sp, #24816]
	str	xzr, [sp, #24808]
	str	xzr, [sp, #24800]
	str	xzr, [sp, #24792]
	str	xzr, [sp, #24784]
	str	xzr, [sp, #24776]
	str	xzr, [sp, #24768]
	str	xzr, [sp, #24760]
	str	xzr, [sp, #24752]
	str	xzr, [sp, #24744]
	str	xzr, [sp, #24736]
	str	xzr, [sp, #24728]
	str	xzr, [sp, #24720]
	bl	memcpy
	add	x9, sp, #6, lsl #12
	add	x20, sp, #5, lsl #12
	ldr	x0, [sp, #16408]
	add	x9, x9, #144
	add	x20, x20, #1168
	ldrb	w8, [x9, x23]
	eor	w8, w8, #0x1
	strb	w8, [x9, x23]
	ldr	x8, [sp, #16400]
	ldr	x10, [sp, #24720]
	ldr	x11, [sp, #24728]
	ldr	x12, [sp, #24736]
	ldrb	w9, [x20, #3207]
	ldr	x13, [sp, #24744]
	eor	x8, x8, x10
	ldr	x10, [sp, #16416]
	eor	x11, x0, x11
	ldr	x0, [sp, #16424]
	ldr	x14, [sp, #24752]
	ldr	x15, [sp, #24760]
	str	x8, [sp, #16400]
	eor	x8, x10, x12
	ldr	x10, [sp, #16432]
	ldr	x12, [sp, #16440]
	eor	w9, w9, #0x80
	str	x11, [sp, #16408]
	eor	x11, x0, x13
	ldr	x16, [sp, #24768]
	ldr	x17, [sp, #24776]
	strb	w9, [x20, #3207]
	ldr	x9, [sp, #24784]
	ldr	x13, [sp, #16464]
	str	x8, [sp, #16416]
	eor	x8, x10, x14
	ldr	x10, [sp, #16448]
	str	x11, [sp, #16424]
	eor	x11, x12, x15
	ldr	x12, [sp, #16456]
	ldr	x14, [sp, #24808]
	str	x11, [sp, #16440]
	ldr	x11, [sp, #16488]
	str	x8, [sp, #16432]
	eor	x8, x10, x16
	eor	x12, x12, x17
	eor	x9, x13, x9
	ldr	x18, [sp, #24792]
	ldr	x1, [sp, #24800]
	ldr	x10, [sp, #16472]
	ldr	x13, [sp, #16480]
	str	x8, [sp, #16448]
	ldr	x8, [sp, #24816]
	str	x12, [sp, #16456]
	ldr	x12, [sp, #16496]
	eor	x11, x11, x14
	ldr	x14, [sp, #24824]
	str	x9, [sp, #16464]
	ldr	x9, [sp, #16504]
	eor	x10, x10, x18
	eor	x13, x13, x1
	eor	x8, x12, x8
	str	x10, [sp, #16472]
	ldr	x10, [sp, #24832]
	eor	x9, x9, x14
	str	x13, [sp, #16480]
	ldr	x12, [sp, #16512]
	ldr	x13, [sp, #24840]
	str	x11, [sp, #16488]
	ldr	x11, [sp, #16520]
	str	x8, [sp, #16496]
	ldr	x8, [sp, #24848]
	add	x0, sp, #4, lsl #12
	str	x9, [sp, #16504]
	ldr	x9, [sp, #16528]
	eor	x10, x12, x10
	eor	x11, x11, x13
	add	x0, x0, #16
	str	x10, [sp, #16512]
	eor	x8, x9, x8
	str	x11, [sp, #16520]
	str	x8, [sp, #16528]
	bl	_RNvCsndc0WgnAaH_9keccak2568keccak_f
	ldr	x10, [sp, #40]
	ldr	x8, [sp, #16408]
	ldr	x9, [sp, #16400]
	cmp	x19, x10
	str	x8, [sp, #24728]
	str	x9, [sp, #24720]
	str	x9, [sp, #20624]
	str	x8, [sp, #20632]
	b.ne	.LBB3_67
	ldr	x8, [sp, #20624]
	ldr	x9, [sp, #20632]
	mov	w22, #16
	mov	w13, #8
	b	.LBB3_85
.LBB3_84:
	ldr	x8, [sp, #15984]
	ldr	x9, [sp, #15992]
.LBB3_85:
	str	x8, [sp, #16400]
	str	x9, [sp, #16408]
	ldr	x12, [sp, #16]
	mov	w10, #7740
	add	x20, sp, #5, lsl #12
	mov	w14, #117440512
	cmp	x12, x10
	str	x8, [sp, #27792]
	add	x8, sp, #2, lsl #12
	ldp	x23, x10, [sp]
	add	x8, x8, #52
	add	x11, x8, x12
	add	x20, x20, #1168
	adrp	x8, .Lanon.bee145f0cb2eac5728ff95be1b200579.2
	add	x8, x8, :lo12:.Lanon.bee145f0cb2eac5728ff95be1b200579.2
	str	x9, [sp, #27800]
	b.ne	.LBB3_40
	ldr	x8, [sp, #8224]
	ldr	x9, [sp, #27792]
	ldr	x10, [sp, #27800]
	ldr	x11, [sp, #8232]
	cmp	x9, x8
	ccmp	x10, x11, #0, eq
	cset	w0, eq
	b	.LBB3_92
.LBB3_87:
	adrp	x3, .Lanon.47fac95803119c4a094797088418c9d4.11
	add	x3, x3, :lo12:.Lanon.47fac95803119c4a094797088418c9d4.11
	mov	w2, #136
	bl	_RNvNtNtCs8l20omZJ7ql_4core5slice5index16slice_index_fail
.LBB3_88:
	adrp	x3, .Lanon.47fac95803119c4a094797088418c9d4.11
	add	x3, x3, :lo12:.Lanon.47fac95803119c4a094797088418c9d4.11
	mov	x0, x25
	mov	w2, #136
	bl	_RNvNtNtCs8l20omZJ7ql_4core5slice5index16slice_index_fail
.LBB3_89:
	adrp	x3, .Lanon.47fac95803119c4a094797088418c9d4.12
	add	x3, x3, :lo12:.Lanon.47fac95803119c4a094797088418c9d4.12
	mov	x0, xzr
	mov	x1, x25
	mov	w2, #136
	bl	_RNvNtNtCs8l20omZJ7ql_4core5slice5index16slice_index_fail
.LBB3_90:
	adrp	x3, .Lanon.47fac95803119c4a094797088418c9d4.11
	add	x3, x3, :lo12:.Lanon.47fac95803119c4a094797088418c9d4.11
	mov	x0, x24
	mov	w2, #136
	bl	_RNvNtNtCs8l20omZJ7ql_4core5slice5index16slice_index_fail
.LBB3_91:
	mov	x0, xzr
.LBB3_92:
	add	sp, sp, #7, lsl #12
	add	sp, sp, #608
	.cfi_def_cfa wsp, 96
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
.LBB3_93:
	.cfi_restore_state
	adrp	x3, .Lanon.47fac95803119c4a094797088418c9d4.12
	add	x3, x3, :lo12:.Lanon.47fac95803119c4a094797088418c9d4.12
	mov	x0, xzr
	mov	x1, x24
	mov	w2, #136
	bl	_RNvNtNtCs8l20omZJ7ql_4core5slice5index16slice_index_fail
.LBB3_94:
	adrp	x3, .Lanon.47fac95803119c4a094797088418c9d4.11
	add	x3, x3, :lo12:.Lanon.47fac95803119c4a094797088418c9d4.11
	mov	x0, x23
	mov	w2, #136
	bl	_RNvNtNtCs8l20omZJ7ql_4core5slice5index16slice_index_fail
.LBB3_95:
	adrp	x3, .Lanon.47fac95803119c4a094797088418c9d4.12
	add	x3, x3, :lo12:.Lanon.47fac95803119c4a094797088418c9d4.12
	mov	x0, xzr
	mov	x1, x23
	mov	w2, #136
	bl	_RNvNtNtCs8l20omZJ7ql_4core5slice5index16slice_index_fail
.LBB3_96:
	adrp	x3, .Lanon.bee145f0cb2eac5728ff95be1b200579.4
	add	x3, x3, :lo12:.Lanon.bee145f0cb2eac5728ff95be1b200579.4
	mov	w2, #26
	bl	_RNvNtNtCs8l20omZJ7ql_4core5slice5index16slice_index_fail
.Lfunc_end3:
	.size	sphincs_verify, .Lfunc_end3-sphincs_verify
	.cfi_endproc

	.section	.text.xmss_verify,"ax",@progbits
	.globl	xmss_verify
	.p2align	2
	.type	xmss_verify,@function
xmss_verify:
.Lfunc_begin4:
	.cfi_startproc
	stp	x29, x30, [sp, #-96]!
	.cfi_def_cfa_offset 96
	stp	x28, x27, [sp, #16]
	stp	x26, x25, [sp, #32]
	stp	x24, x23, [sp, #48]
	stp	x22, x21, [sp, #64]
	stp	x20, x19, [sp, #80]
	mov	x29, sp
	.cfi_def_cfa w29, 96
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
	ldr	xzr, [sp]
	sub	sp, sp, #1680
	add	x22, sp, #44
	ldr	xzr, [sp]
	mov	x20, x0
	add	x21, sp, #1, lsl #12
	add	x0, x22, #4
	mov	w1, wzr
	mov	w2, #2400
	add	x21, x21, #1296
	add	x19, x22, #4
	bl	memset
	ldr	x8, [x20, #1056]
	ldr	x9, [x20, #1064]
	add	x12, x22, #20
	ldr	x10, [x20, #1072]
	ldr	x13, [x20, #1080]
	mov	w14, #300
	ldr	x24, [x20, #1088]
	stp	x8, x9, [sp, #8]
	ldr	x8, [x20, #1024]
	ldr	x9, [x20, #1032]
	stp	x10, x13, [sp, #24]
	add	x13, x20, #1120
	ldr	x10, [x20, #1040]
	mov	w23, w24
	ldr	x11, [x20, #1048]
	str	w24, [sp, #44]
.LBB4_1:
	ldp	x15, x16, [x13, #-24]
	subs	x14, x14, #4
	stp	x15, x16, [x12, #-16]
	ldp	x15, x17, [x13, #-8]
	add	x13, x13, #32
	stp	x15, x17, [x12], #32
	b.ne	.LBB4_1
	add	x1, sp, #1, lsl #12
	str	x8, [sp, #2448]
	mov	w8, #2400
	add	x0, sp, #2492
	add	x1, x1, #1312
	str	x9, [sp, #2456]
	str	x10, [sp, #2464]
	add	x20, sp, #2448
	str	x11, [sp, #2472]
	str	x19, [sp, #5408]
	add	x19, sp, #2492
	str	x8, [sp, #5416]
	bl	_RNvMs_NtCs7Pyp4CbMBld_9lean_xmss6schemeNtB4_14LayerSignature4read
	add	x1, sp, #1, lsl #12
	add	x0, x19, #1200
	add	x22, x19, #1200
	add	x1, x1, #1312
	bl	_RNvMs_NtCs7Pyp4CbMBld_9lean_xmss6schemeNtB4_14LayerSignature4read
	add	x0, sp, #1, lsl #12
	add	x1, x20, #16
	add	x4, sp, #8
	add	x0, x0, #1312
	add	x6, x19, #1184
	add	x7, x19, #256
	mov	x2, xzr
	mov	w3, w24
	mov	w5, #32
	str	w24, [sp, #4892]
	bl	_RNvNtCs7Pyp4CbMBld_9lean_xmss4wots9wots_leaf
	ldrb	w8, [x21, #16]
	cbz	w8, .LBB4_9
	ldur	x8, [x21, #81]
	ldurh	w9, [x21, #89]
	add	x25, sp, #1, lsl #12
	ldur	x10, [x21, #49]
	add	x26, sp, #1, lsl #12
	add	x19, sp, #1, lsl #12
	str	x8, [sp, #4960]
	ldur	x8, [x21, #57]
	add	x25, x25, #800
	strh	w9, [sp, #4968]
	ldur	x9, [x21, #65]
	add	x26, x26, #920
	str	x8, [sp, #4936]
	ldur	x8, [x21, #73]
	add	x27, sp, #2492
	str	x10, [sp, #4928]
	ldur	x10, [x21, #17]
	mov	w28, #1
	str	x8, [sp, #4952]
	ldur	x8, [x21, #25]
	add	x19, x19, #880
	str	x9, [sp, #4944]
	ldur	x9, [x21, #33]
	mov	w20, #3
	str	x8, [sp, #4904]
	ldur	x8, [x21, #41]
	str	x24, [sp]
	mov	x24, xzr
	str	x10, [sp, #4896]
	str	x9, [sp, #4912]
	str	x8, [sp, #4920]
.LBB4_4:
	lsl	x9, x28, x24
	ldur	x8, [x25, #58]
	ldur	x10, [x25, #66]
	add	x24, x24, #1
	add	x0, sp, #1, lsl #12
	mov	w1, wzr
	tst	x9, x23
	str	x8, [sp, #4976]
	lsr	x8, x23, x24
	str	x10, [sp, #4984]
	csel	x9, x19, x27, eq
	add	x0, x0, #1312
	ldp	x10, x9, [x9]
	str	w8, [sp, #5392]
	csel	x8, x27, x19, eq
	mov	w2, #344
	strh	w24, [sp, #5396]
	strb	w20, [x21, #7]
	str	x10, [sp, #5016]
	ldp	x10, x8, [x8]
	str	x9, [sp, #5024]
	lsr	w9, w24, #16
	str	xzr, [sp, #5400]
	stp	x10, x8, [x26, #16]
	strb	w9, [x21, #6]
	bl	memset
	add	x0, sp, #1, lsl #12
	add	x8, sp, #2448
	mov	w2, #16
	add	x0, x0, #1312
	add	x1, x8, #16
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	add	x0, sp, #1, lsl #12
	add	x1, sp, #1, lsl #12
	mov	w2, #16
	add	x0, x0, #1312
	add	x1, x1, #1296
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	add	x0, sp, #1, lsl #12
	add	x1, sp, #1, lsl #12
	mov	w2, #344
	add	x0, x0, #952
	add	x1, x1, #1312
	bl	memcpy
	add	x0, sp, #1, lsl #12
	add	x1, sp, #1, lsl #12
	mov	w2, #32
	add	x0, x0, #952
	add	x1, x1, #920
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	add	x0, sp, #1, lsl #12
	add	x1, sp, #1, lsl #12
	add	x0, x0, #1312
	add	x1, x1, #952
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher8finalize
	ldr	x8, [sp, #5408]
	ldr	x9, [sp, #5416]
	cmp	x24, #16
	add	x27, x27, #16
	stur	x8, [x25, #58]
	stur	x9, [x25, #66]
	b.ne	.LBB4_4
	ldr	x8, [sp]
	add	x0, sp, #1, lsl #12
	add	x9, sp, #2448
	add	x0, x0, #1312
	add	x1, x9, #16
	add	x4, x25, #58
	lsr	w19, w8, #16
	add	x8, sp, #2492
	mov	w2, #1
	add	x6, x8, #2384
	add	x7, x8, #1456
	mov	w5, #16
	mov	w3, w19
	bl	_RNvNtCs7Pyp4CbMBld_9lean_xmss4wots9wots_leaf
	ldrb	w8, [x21, #16]
	add	x27, sp, #2448
	cbz	w8, .LBB4_9
	ldur	x8, [x21, #83]
	ldur	x9, [x21, #75]
	add	x23, sp, #1, lsl #12
	add	x25, sp, #1, lsl #12
	add	x23, x23, #920
	mov	w24, #1
	add	x25, x25, #880
	mov	w26, #3
	mov	w20, #1
.LBB4_7:
	sub	x10, x20, #1
	str	x9, [sp, #4976]
	lsr	x11, x19, x20
	lsl	x10, x24, x10
	str	x8, [sp, #4984]
	add	x0, sp, #1, lsl #12
	add	x0, x0, #1312
	mov	w1, wzr
	mov	w2, #344
	tst	x10, x19
	orr	w10, w20, #0x800000
	str	w11, [sp, #5392]
	csel	x9, x25, x22, eq
	lsr	w8, w10, #16
	strh	w20, [sp, #5396]
	ldp	x10, x9, [x9]
	strb	w26, [x21, #7]
	strb	w8, [x21, #6]
	csel	x8, x22, x25, eq
	str	xzr, [sp, #5400]
	str	x10, [sp, #5016]
	ldp	x10, x8, [x8]
	str	x9, [sp, #5024]
	stp	x10, x8, [x23, #16]
	bl	memset
	add	x0, sp, #1, lsl #12
	add	x1, x27, #16
	mov	w2, #16
	add	x0, x0, #1312
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	add	x0, sp, #1, lsl #12
	add	x1, sp, #1, lsl #12
	mov	w2, #16
	add	x0, x0, #1312
	add	x1, x1, #1296
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	add	x0, sp, #1, lsl #12
	add	x1, sp, #1, lsl #12
	mov	w2, #344
	add	x0, x0, #952
	add	x1, x1, #1312
	bl	memcpy
	add	x0, sp, #1, lsl #12
	add	x1, sp, #1, lsl #12
	mov	w2, #32
	add	x0, x0, #952
	add	x1, x1, #920
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	add	x0, sp, #1, lsl #12
	add	x1, sp, #1, lsl #12
	add	x0, x0, #1312
	add	x1, x1, #952
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher8finalize
	add	x20, x20, #1
	ldr	x8, [sp, #5416]
	ldr	x9, [sp, #5408]
	cmp	x20, #17
	add	x22, x22, #16
	b.ne	.LBB4_7
	ldr	x10, [sp, #2448]
	ldr	x11, [sp, #2456]
	cmp	x9, x10
	ccmp	x8, x11, #0, eq
	cset	w0, eq
	b	.LBB4_10
.LBB4_9:
	mov	x0, xzr
.LBB4_10:
	add	sp, sp, #1, lsl #12
	add	sp, sp, #1680
	.cfi_def_cfa wsp, 96
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
	.size	xmss_verify, .Lfunc_end4-xmss_verify
	.cfi_endproc

	.section	.text.unlikely._RNvNtCs8l20omZJ7ql_4core9panicking9panic_fmt,"ax",@progbits
	.p2align	2
	.type	_RNvNtCs8l20omZJ7ql_4core9panicking9panic_fmt,@function
_RNvNtCs8l20omZJ7ql_4core9panicking9panic_fmt:
.Lfunc_begin5:
	.file	1 "/rustc/58cf8f9c35b355199727627d07ae34a4e2846d67" "library/core/src/panicking.rs"
	.loc	1 60 0
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
.Ltmp0:
	.loc	1 80 14 prologue_end
	bl	_RNvCs5fGHjzWXRav_7___rustc17rust_begin_unwind
.Ltmp1:
.Lfunc_end5:
	.size	_RNvNtCs8l20omZJ7ql_4core9panicking9panic_fmt, .Lfunc_end5-_RNvNtCs8l20omZJ7ql_4core9panicking9panic_fmt
	.cfi_endproc

	.section	.text.unlikely._RNvNtNtCs8l20omZJ7ql_4core5slice5index16slice_index_fail,"ax",@progbits
	.p2align	2
	.type	_RNvNtNtCs8l20omZJ7ql_4core5slice5index16slice_index_fail,@function
_RNvNtNtCs8l20omZJ7ql_4core5slice5index16slice_index_fail:
.Lfunc_begin6:
	.file	2 "/rustc/58cf8f9c35b355199727627d07ae34a4e2846d67" "library/core/src/slice/index.rs"
	.loc	2 39 0
	.cfi_startproc
	sub	sp, sp, #48
	.cfi_def_cfa_offset 48
	stp	x29, x30, [sp, #32]
	add	x29, sp, #32
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
.Ltmp2:
	.loc	2 40 8 prologue_end
	cmp	x0, x2
	b.ls	.LBB6_2
.Ltmp3:
	.file	3 "/rustc/58cf8f9c35b355199727627d07ae34a4e2846d67" "library/core/src/panic.rs"
	.loc	3 172 21
	adrp	x0, .Lanon.46a40f786ce4ddedc5d90764d599cb89.205
	add	x0, x0, :lo12:.Lanon.46a40f786ce4ddedc5d90764d599cb89.205
.Ltmp4:
	.loc	3 177 9
	mov	x1, sp
	mov	x2, x3
	bl	_RNvNtCs8l20omZJ7ql_4core9panicking9panic_fmt
.LBB6_2:
	.loc	2 49 8
	cmp	x1, x2
	b.hi	.LBB6_5
	.loc	2 58 8
	cmp	x0, x1
	b.ls	.LBB6_5
.Ltmp5:
	.loc	3 172 21
	adrp	x0, .Lanon.46a40f786ce4ddedc5d90764d599cb89.204
	add	x0, x0, :lo12:.Lanon.46a40f786ce4ddedc5d90764d599cb89.204
.Ltmp6:
	.loc	3 177 9
	mov	x1, sp
	mov	x2, x3
	bl	_RNvNtCs8l20omZJ7ql_4core9panicking9panic_fmt
.LBB6_5:
	.loc	3 177 9
	adrp	x0, .Lanon.46a40f786ce4ddedc5d90764d599cb89.203
	add	x0, x0, :lo12:.Lanon.46a40f786ce4ddedc5d90764d599cb89.203
	mov	x1, sp
	mov	x2, x3
	bl	_RNvNtCs8l20omZJ7ql_4core9panicking9panic_fmt
.Ltmp7:
.Lfunc_end6:
	.size	_RNvNtNtCs8l20omZJ7ql_4core5slice5index16slice_index_fail, .Lfunc_end6-_RNvNtNtCs8l20omZJ7ql_4core5slice5index16slice_index_fail
	.cfi_endproc
	.file	4 "/rustc/58cf8f9c35b355199727627d07ae34a4e2846d67" "library/core/src/intrinsics/mod.rs"

	.section	.text.unlikely._RNvNtCs8l20omZJ7ql_4core9panicking5panic,"ax",@progbits
	.p2align	2
	.type	_RNvNtCs8l20omZJ7ql_4core9panicking5panic,@function
_RNvNtCs8l20omZJ7ql_4core9panicking5panic:
.Lfunc_begin7:
	.loc	1 138 0
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
.Ltmp8:
	.loc	1 150 5 prologue_end
	adrp	x0, .Lanon.46a40f786ce4ddedc5d90764d599cb89.173
	add	x0, x0, :lo12:.Lanon.46a40f786ce4ddedc5d90764d599cb89.173
	adrp	x2, .Lanon.9dc208de841c72058cf8117eb5c1924c.1
	add	x2, x2, :lo12:.Lanon.9dc208de841c72058cf8117eb5c1924c.1
	mov	w1, #87
	bl	_RNvNtCs8l20omZJ7ql_4core9panicking9panic_fmt
.Ltmp9:
.Lfunc_end7:
	.size	_RNvNtCs8l20omZJ7ql_4core9panicking5panic, .Lfunc_end7-_RNvNtCs8l20omZJ7ql_4core9panicking5panic
	.cfi_endproc

	.section	.text.unlikely._RNvNtCs8l20omZJ7ql_4core6option13unwrap_failed,"ax",@progbits
	.p2align	2
	.type	_RNvNtCs8l20omZJ7ql_4core6option13unwrap_failed,@function
_RNvNtCs8l20omZJ7ql_4core6option13unwrap_failed:
.Lfunc_begin8:
	.file	5 "/rustc/58cf8f9c35b355199727627d07ae34a4e2846d67" "library/core/src/option.rs"
	.loc	5 2247 0
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	.cfi_def_cfa_offset 16
	mov	x29, sp
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
.Ltmp10:
	.loc	5 2248 5 prologue_end
	bl	_RNvNtCs8l20omZJ7ql_4core9panicking5panic
.Ltmp11:
.Lfunc_end8:
	.size	_RNvNtCs8l20omZJ7ql_4core6option13unwrap_failed, .Lfunc_end8-_RNvNtCs8l20omZJ7ql_4core6option13unwrap_failed
	.cfi_endproc

	.section	.text._RNvCsndc0WgnAaH_9keccak2568keccak_f,"ax",@progbits
	.p2align	2
	.type	_RNvCsndc0WgnAaH_9keccak2568keccak_f,@function
_RNvCsndc0WgnAaH_9keccak2568keccak_f:
.Lfunc_begin9:
	.cfi_startproc
	sub	sp, sp, #192
	.cfi_def_cfa_offset 192
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
	.cfi_offset w30, -96
	ldp	x15, x8, [x0, #32]
	mov	x27, xzr
	ldp	x5, x12, [x0, #112]
	str	x0, [sp, #8]
	ldp	x9, x10, [x0]
	ldp	x11, x2, [x0, #80]
	mov	x22, x15
	ldp	x4, x13, [x0, #48]
	str	x8, [sp, #80]
	eor	x8, x8, x9
	str	x12, [sp, #40]
	ldp	x19, x3, [x0, #128]
	stp	x11, x9, [sp, #48]
	eor	x9, x11, x12
	stp	x30, x10, [sp, #96]
	ldp	x11, x14, [x0, #16]
	eor	x8, x8, x9
	ldp	x1, x7, [x0, #96]
	eor	x9, x4, x10
	ldp	x25, x21, [x0, #144]
	eor	x10, x2, x19
	ldp	x12, x6, [x0, #64]
	eor	x9, x9, x10
	str	x11, [sp, #88]
	eor	x10, x13, x11
	eor	x11, x1, x3
	stp	x14, x13, [sp, #64]
	eor	x10, x10, x11
	eor	x13, x7, x25
	eor	x11, x12, x14
	ldp	x23, x18, [x0, #160]
	ldp	x16, x20, [x0, #176]
	eor	x11, x11, x13
	eor	x13, x6, x15
	eor	x14, x5, x21
	eor	x13, x13, x14
	ldr	x14, [x0, #192]
	eor	x28, x8, x23
	eor	x30, x9, x18
	eor	x8, x10, x16
	eor	x15, x11, x20
	eor	x0, x13, x14
.LBB9_1:
	str	x5, [sp, #32]
	mov	x24, x2
	eor	x2, x0, x30, ror #63
	mov	x26, x3
	eor	x3, x30, x15, ror #63
	eor	x30, x28, x8, ror #63
	eor	x5, x8, x0, ror #63
	ldr	x8, [sp, #56]
	stp	x12, x18, [sp, #16]
	eor	x15, x15, x28, ror #63
	eor	x9, x1, x3
	ldr	x13, [sp, #104]
	eor	x12, x8, x2
	eor	x8, x4, x30
	eor	x10, x25, x5
	ror	x4, x8, #20
	ror	x1, x10, #43
	ldr	x8, [sp, #64]
	ldr	x10, [sp, #48]
	eor	x11, x14, x15
	ror	x17, x9, #21
	eor	x9, x6, x15
	ror	x18, x11, #50
	eor	x8, x8, x5
	eor	x11, x10, x2
	ror	x10, x9, #44
	eor	x9, x16, x3
	ror	x6, x8, #36
	eor	x8, x19, x30
	eor	x16, x13, x30
	ror	x14, x9, #3
	eor	x9, x7, x5
	ror	x13, x8, #19
	ror	x19, x16, #63
	ldr	x8, [sp, #72]
	ror	x16, x9, #39
	ldp	x9, x7, [sp, #80]
	eor	x0, x21, x15
	eor	x8, x8, x3
	ror	x21, x0, #56
	eor	x0, x22, x15
	ror	x25, x8, #58
	eor	x8, x23, x2
	eor	x23, x26, x3
	eor	x3, x7, x3
	ldr	x7, [sp, #16]
	eor	x22, x9, x2
	ror	x9, x8, #46
	ror	x8, x0, #37
	ror	x0, x22, #28
	eor	x22, x24, x30
	eor	x24, x20, x5
	eor	x5, x7, x5
	ldr	x7, [sp, #32]
	ror	x26, x22, #54
	ror	x22, x23, #49
	ror	x23, x24, #8
	ror	x3, x3, #2
	ror	x24, x5, #9
	eor	x15, x7, x15
	bic	x5, x1, x17
	ror	x11, x11, #61
	ror	x20, x15, #25
	ldr	x15, [sp, #40]
	eor	x7, x5, x4
	adrp	x5, .Lanon.47fac95803119c4a094797088418c9d4.1
	add	x5, x5, :lo12:.Lanon.47fac95803119c4a094797088418c9d4.1
	str	x3, [sp, #32]
	eor	x2, x15, x2
	ldr	x15, [sp, #24]
	ldr	x5, [x5, x27]
	ror	x28, x2, #23
	bic	x2, x18, x1
	str	x7, [sp, #104]
	eor	x3, x15, x30
	eor	x2, x2, x17
	bic	x17, x17, x4
	ror	x30, x3, #62
	bic	x3, x12, x18
	add	x27, x27, #8
	eor	x3, x3, x1
	bic	x1, x4, x12
	eor	x12, x5, x12
	eor	x15, x18, x1
	eor	x5, x17, x12
	bic	x17, x11, x10
	bic	x18, x13, x11
	eor	x1, x17, x6
	bic	x17, x14, x13
	eor	x4, x18, x10
	bic	x10, x10, x6
	eor	x17, x17, x11
	bic	x11, x6, x14
	eor	x6, x14, x10
	bic	x14, x19, x9
	eor	x12, x11, x13
	eor	x11, x7, x4
	eor	x7, x14, x21
	bic	x14, x21, x16
	stp	x1, x2, [sp, #80]
	eor	x13, x2, x17
	eor	x2, x14, x25
	bic	x14, x25, x19
	stp	x5, x3, [sp, #56]
	eor	x10, x5, x1
	bic	x18, x9, x21
	eor	x5, x9, x14
	bic	x9, x26, x0
	eor	x1, x18, x16
	bic	x16, x16, x25
	eor	x18, x9, x8
	bic	x9, x22, x26
	eor	x16, x16, x19
	bic	x14, x23, x22
	eor	x19, x9, x0
	bic	x9, x0, x8
	bic	x8, x8, x23
	str	x17, [sp, #72]
	eor	x17, x3, x12
	eor	x3, x14, x26
	eor	x25, x8, x22
	eor	x8, x16, x18
	eor	x21, x23, x9
	eor	x8, x10, x8
	eor	x10, x1, x3
	eor	x10, x13, x10
	mov	x22, x15
	eor	x13, x15, x6
	eor	x14, x5, x21
	ldr	x15, [sp, #32]
	eor	x9, x2, x19
	eor	x13, x13, x14
	bic	x14, x20, x24
	eor	x9, x11, x9
	eor	x11, x7, x25
	eor	x23, x14, x15
	bic	x14, x28, x20
	stp	x18, x16, [sp, #40]
	eor	x11, x17, x11
	bic	x17, x30, x28
	eor	x18, x14, x24
	bic	x14, x24, x15
	bic	x15, x15, x30
	eor	x16, x17, x20
	eor	x20, x15, x28
	eor	x14, x30, x14
	eor	x28, x8, x23
	eor	x30, x9, x18
	cmp	x27, #192
	eor	x8, x10, x16
	eor	x15, x11, x20
	eor	x0, x13, x14
	b.ne	.LBB9_1
	ldr	x8, [sp, #8]
	ldr	x10, [sp, #56]
	ldp	x30, x9, [sp, #96]
	ldp	x28, x27, [sp, #112]
	stp	x10, x9, [x8]
	ldr	x10, [sp, #88]
	ldr	x9, [sp, #64]
	stp	x19, x3, [x8, #128]
	stp	x10, x9, [x8, #16]
	ldp	x9, x10, [sp, #72]
	stp	x25, x21, [x8, #144]
	ldp	x26, x25, [sp, #128]
	stp	x23, x18, [x8, #160]
	ldp	x24, x23, [sp, #144]
	stp	x22, x10, [x8, #32]
	ldp	x22, x21, [sp, #160]
	stp	x4, x9, [x8, #48]
	ldp	x9, x10, [sp, #40]
	stp	x16, x20, [x8, #176]
	ldp	x20, x19, [sp, #176]
	stp	x12, x6, [x8, #64]
	stp	x10, x2, [x8, #80]
	stp	x1, x7, [x8, #96]
	stp	x5, x9, [x8, #112]
	str	x14, [x8, #192]
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
	ret
.Lfunc_end9:
	.size	_RNvCsndc0WgnAaH_9keccak2568keccak_f, .Lfunc_end9-_RNvCsndc0WgnAaH_9keccak2568keccak_f
	.cfi_endproc

	.section	.text._RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update,"ax",@progbits
	.p2align	2
	.type	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update,@function
_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update:
.Lfunc_begin10:
	.cfi_startproc
	stp	x29, x30, [sp, #-64]!
	.cfi_def_cfa_offset 64
	stp	x24, x23, [sp, #16]
	stp	x22, x21, [sp, #32]
	stp	x20, x19, [sp, #48]
	mov	x29, sp
	.cfi_def_cfa w29, 64
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w24, -48
	.cfi_offset w30, -56
	.cfi_offset w29, -64
	.cfi_remember_state
	mov	x20, x0
	ldr	x0, [x0, #336]
	mov	x19, x2
	mov	x21, x1
	add	x23, x20, #200
	mov	w24, #136
	b	.LBB10_2
.LBB10_1:
	sub	x19, x19, x22
	add	x21, x21, x22
	cbz	x19, .LBB10_6
.LBB10_2:
	sub	x8, x24, x0
	cmp	x19, x8
	csel	x22, x19, x8, lo
	add	x1, x22, x0
	cmp	x1, x0
	b.lo	.LBB10_7
	cmp	x1, #137
	b.hs	.LBB10_7
	add	x0, x23, x0
	mov	x1, x21
	mov	x2, x22
	bl	memcpy
	ldr	x8, [x20, #336]
	add	x0, x8, x22
	cmp	x0, #136
	str	x0, [x20, #336]
	b.ne	.LBB10_1
	ldp	x8, x9, [x20, #200]
	ldr	x1, [x20, #280]
	ldp	x16, x0, [x20]
	ldp	x10, x11, [x20, #216]
	ldp	x12, x13, [x20, #232]
	eor	x8, x16, x8
	eor	x9, x0, x9
	ldp	x16, x0, [x20, #16]
	stp	x8, x9, [x20]
	ldp	x14, x15, [x20, #248]
	ldp	x17, x18, [x20, #264]
	eor	x8, x16, x10
	eor	x10, x0, x11
	mov	x0, x20
	ldp	x9, x11, [x20, #32]
	stp	x8, x10, [x20, #16]
	eor	x8, x9, x12
	eor	x10, x11, x13
	ldp	x9, x11, [x20, #48]
	stp	x8, x10, [x20, #32]
	ldp	x13, x10, [x20, #80]
	eor	x8, x9, x14
	ldp	x12, x9, [x20, #64]
	eor	x11, x11, x15
	eor	x13, x13, x1
	stp	x8, x11, [x20, #48]
	ldp	x14, x8, [x20, #288]
	eor	x12, x12, x17
	eor	x9, x9, x18
	stp	x12, x9, [x20, #64]
	ldp	x11, x12, [x20, #96]
	eor	x10, x10, x14
	ldp	x14, x9, [x20, #304]
	stp	x13, x10, [x20, #80]
	eor	x8, x11, x8
	ldp	x11, x10, [x20, #112]
	eor	x12, x12, x14
	stp	x8, x12, [x20, #96]
	ldp	x13, x8, [x20, #320]
	eor	x9, x11, x9
	ldr	x11, [x20, #128]
	eor	x10, x10, x13
	eor	x8, x11, x8
	stp	x9, x10, [x20, #112]
	str	x8, [x20, #128]
	bl	_RNvCsndc0WgnAaH_9keccak2568keccak_f
	mov	x0, xzr
	str	xzr, [x20, #336]
	b	.LBB10_1
.LBB10_6:
	mov	x0, x20
	.cfi_def_cfa wsp, 64
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
.LBB10_7:
	.cfi_restore_state
	adrp	x3, .Lanon.47fac95803119c4a094797088418c9d4.11
	add	x3, x3, :lo12:.Lanon.47fac95803119c4a094797088418c9d4.11
	mov	w2, #136
	bl	_RNvNtNtCs8l20omZJ7ql_4core5slice5index16slice_index_fail
.Lfunc_end10:
	.size	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update, .Lfunc_end10-_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	.cfi_endproc

	.section	.text._RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher8finalize,"ax",@progbits
	.p2align	2
	.type	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher8finalize,@function
_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher8finalize:
.Lfunc_begin11:
	.cfi_startproc
	sub	sp, sp, #384
	.cfi_def_cfa_offset 384
	stp	x29, x30, [sp, #336]
	stp	x28, x21, [sp, #352]
	stp	x20, x19, [sp, #368]
	add	x29, sp, #336
	.cfi_def_cfa w29, 48
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w28, -32
	.cfi_offset w30, -40
	.cfi_offset w29, -48
	.cfi_remember_state
	mov	x19, x0
	mov	x0, sp
	mov	w2, #200
	mov	x21, x1
	bl	memcpy
	ldr	x20, [x21, #336]
	cmp	x20, #137
	b.hs	.LBB11_3
	cmp	x20, #136
	b.eq	.LBB11_4
	sub	x0, x29, #136
	add	x1, x21, #200
	mov	x2, x20
	stp	xzr, xzr, [x29, #-16]
	sub	x21, x29, #136
	stp	xzr, xzr, [x29, #-32]
	stp	xzr, xzr, [x29, #-48]
	stp	xzr, xzr, [x29, #-64]
	stp	xzr, xzr, [x29, #-80]
	stp	xzr, xzr, [x29, #-96]
	stp	xzr, xzr, [x29, #-112]
	stp	xzr, xzr, [x29, #-128]
	stur	xzr, [x29, #-136]
	bl	memcpy
	ldrb	w8, [x21, x20]
	eor	w8, w8, #0x1
	strb	w8, [x21, x20]
	ldp	x8, x0, [sp]
	ldurb	w9, [x29, #-1]
	ldp	x10, x11, [x29, #-136]
	ldur	x1, [x29, #-56]
	ldp	x12, x13, [x29, #-120]
	eor	w9, w9, #0x80
	ldp	x14, x15, [x29, #-104]
	sturb	w9, [x29, #-1]
	eor	x8, x8, x10
	eor	x11, x0, x11
	ldp	x10, x0, [sp, #16]
	stp	x8, x11, [sp]
	ldp	x16, x17, [x29, #-88]
	ldp	x9, x18, [x29, #-72]
	eor	x8, x10, x12
	ldp	x10, x12, [sp, #32]
	eor	x11, x0, x13
	mov	x0, sp
	stp	x8, x11, [sp, #16]
	eor	x8, x10, x14
	eor	x11, x12, x15
	ldp	x10, x12, [sp, #48]
	stp	x8, x11, [sp, #32]
	eor	x8, x10, x16
	ldp	x13, x10, [sp, #64]
	eor	x12, x12, x17
	stp	x8, x12, [sp, #48]
	ldp	x14, x8, [x29, #-48]
	eor	x9, x13, x9
	ldp	x13, x11, [sp, #80]
	eor	x10, x10, x18
	stp	x9, x10, [sp, #64]
	ldp	x12, x9, [sp, #96]
	eor	x11, x11, x14
	ldp	x14, x10, [x29, #-32]
	eor	x13, x13, x1
	eor	x8, x12, x8
	stp	x13, x11, [sp, #80]
	eor	x9, x9, x14
	ldp	x12, x11, [sp, #112]
	stp	x8, x9, [sp, #96]
	ldp	x13, x8, [x29, #-16]
	ldr	x9, [sp, #128]
	eor	x10, x12, x10
	eor	x11, x11, x13
	eor	x8, x9, x8
	stp	x10, x11, [sp, #112]
	str	x8, [sp, #128]
	bl	_RNvCsndc0WgnAaH_9keccak2568keccak_f
	ldp	x8, x9, [sp]
	stp	x8, x9, [x19]
	ldp	x8, x10, [sp, #16]
	stp	x8, x10, [x19, #16]
	.cfi_def_cfa wsp, 384
	ldp	x20, x19, [sp, #368]
	ldp	x28, x21, [sp, #352]
	ldp	x29, x30, [sp, #336]
	add	sp, sp, #384
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w28
	.cfi_restore w30
	.cfi_restore w29
	ret
.LBB11_3:
	.cfi_restore_state
	adrp	x3, .Lanon.47fac95803119c4a094797088418c9d4.12
	add	x3, x3, :lo12:.Lanon.47fac95803119c4a094797088418c9d4.12
	mov	x0, xzr
	mov	x1, x20
	mov	w2, #136
	bl	_RNvNtNtCs8l20omZJ7ql_4core5slice5index16slice_index_fail
.LBB11_4:
	adrp	x0, .Lanon.47fac95803119c4a094797088418c9d4.8
	add	x0, x0, :lo12:.Lanon.47fac95803119c4a094797088418c9d4.8
	adrp	x2, .Lanon.47fac95803119c4a094797088418c9d4.9
	add	x2, x2, :lo12:.Lanon.47fac95803119c4a094797088418c9d4.9
	mov	w1, #99
	bl	_RNvNtCs8l20omZJ7ql_4core9panicking9panic_fmt
.Lfunc_end11:
	.size	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher8finalize, .Lfunc_end11-_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher8finalize
	.cfi_endproc

	.section	.text._RNvMs_NtCs7Pyp4CbMBld_9lean_xmss6schemeNtB4_14LayerSignature4read,"ax",@progbits
	.p2align	2
	.type	_RNvMs_NtCs7Pyp4CbMBld_9lean_xmss6schemeNtB4_14LayerSignature4read,@function
_RNvMs_NtCs7Pyp4CbMBld_9lean_xmss6schemeNtB4_14LayerSignature4read:
.Lfunc_begin12:
	.cfi_startproc
	stp	x29, x30, [sp, #-80]!
	.cfi_def_cfa_offset 80
	str	x28, [sp, #16]
	stp	x24, x23, [sp, #32]
	stp	x22, x21, [sp, #48]
	stp	x20, x19, [sp, #64]
	mov	x29, sp
	.cfi_def_cfa w29, 80
	.cfi_offset w19, -8
	.cfi_offset w20, -16
	.cfi_offset w21, -24
	.cfi_offset w22, -32
	.cfi_offset w23, -40
	.cfi_offset w24, -48
	.cfi_offset w28, -64
	.cfi_offset w30, -72
	.cfi_offset w29, -80
	.cfi_remember_state
	sub	sp, sp, #1856
	ldr	xzr, [sp]
	ldr	x22, [x1, #8]
	cmp	x22, #15
	b.ls	.LBB12_21
	sub	x8, x22, #16
	ldr	x21, [x1]
	mov	x20, x1
	lsr	x8, x8, #4
	mov	x19, x0
	mov	x23, xzr
	add	x9, sp, #928
.LBB12_2:
	cbz	x8, .LBB12_21
	add	x10, x21, x23
	add	x12, x9, x23
	add	x23, x23, #16
	add	x11, x10, #32
	ldp	x13, x10, [x10, #16]
	sub	x24, x22, #32
	cmp	x23, #928
	sub	x8, x8, #1
	sub	x22, x22, #16
	stp	x11, x24, [x20]
	stp	x13, x10, [x12]
	b.ne	.LBB12_2
	mov	x0, sp
	add	x1, sp, #928
	mov	w2, #928
	bl	memcpy
	cmp	x24, #15
	b.ls	.LBB12_21
	add	x8, x21, x23
	and	x9, x24, #0xfffffffffffffff0
	ldp	x10, x11, [x8, #16]
	cmp	x9, #16
	str	x10, [sp, #928]
	str	x11, [sp, #936]
	b.eq	.LBB12_21
	ldp	x10, x11, [x8, #32]
	cmp	x9, #32
	str	x10, [sp, #944]
	str	x11, [sp, #952]
	b.eq	.LBB12_21
	ldp	x10, x11, [x8, #48]
	cmp	x9, #48
	str	x10, [sp, #960]
	str	x11, [sp, #968]
	b.eq	.LBB12_21
	ldp	x10, x11, [x8, #64]
	cmp	x9, #64
	str	x10, [sp, #976]
	str	x11, [sp, #984]
	b.eq	.LBB12_21
	ldp	x10, x11, [x8, #80]
	cmp	x9, #80
	str	x10, [sp, #992]
	str	x11, [sp, #1000]
	b.eq	.LBB12_21
	ldp	x10, x11, [x8, #96]
	cmp	x9, #96
	str	x10, [sp, #1008]
	str	x11, [sp, #1016]
	b.eq	.LBB12_21
	ldp	x10, x11, [x8, #112]
	cmp	x9, #112
	str	x10, [sp, #1024]
	str	x11, [sp, #1032]
	b.eq	.LBB12_21
	ldp	x10, x11, [x8, #128]
	and	x12, x22, #0xfffffffffffffff0
	cmp	x12, #144
	str	x10, [sp, #1040]
	str	x11, [sp, #1048]
	b.eq	.LBB12_21
	ldp	x10, x11, [x8, #144]
	cmp	x9, #144
	str	x10, [sp, #1056]
	str	x11, [sp, #1064]
	b.eq	.LBB12_21
	ldp	x10, x11, [x8, #160]
	cmp	x9, #160
	str	x10, [sp, #1072]
	str	x11, [sp, #1080]
	b.eq	.LBB12_21
	ldp	x10, x11, [x8, #176]
	cmp	x9, #176
	str	x10, [sp, #1088]
	str	x11, [sp, #1096]
	b.eq	.LBB12_21
	ldp	x10, x11, [x8, #192]
	cmp	x9, #192
	str	x10, [sp, #1104]
	str	x11, [sp, #1112]
	b.eq	.LBB12_21
	ldp	x10, x11, [x8, #208]
	cmp	x9, #208
	str	x10, [sp, #1120]
	str	x11, [sp, #1128]
	b.eq	.LBB12_21
	ldp	x10, x11, [x8, #224]
	cmp	x9, #224
	str	x10, [sp, #1136]
	str	x11, [sp, #1144]
	b.eq	.LBB12_21
	ldp	x10, x11, [x8, #240]
	cmp	x9, #240
	str	x10, [sp, #1152]
	str	x11, [sp, #1160]
	b.eq	.LBB12_21
	add	x9, x8, #272
	sub	x10, x22, #272
	add	x1, sp, #928
	stp	x9, x10, [x20]
	ldp	x9, x8, [x8, #256]
	mov	x0, x19
	mov	w2, #256
	str	x9, [sp, #1168]
	str	x8, [sp, #1176]
	bl	memcpy
	ldp	x8, x9, [x21]
	add	x0, x19, #256
	mov	x1, sp
	mov	w2, #928
	str	x8, [x19, #1184]
	str	x9, [x19, #1192]
	bl	memcpy
	add	sp, sp, #1856
	.cfi_def_cfa wsp, 80
	ldp	x20, x19, [sp, #64]
	ldr	x28, [sp, #16]
	ldp	x22, x21, [sp, #48]
	ldp	x24, x23, [sp, #32]
	ldp	x29, x30, [sp], #80
	.cfi_def_cfa_offset 0
	.cfi_restore w19
	.cfi_restore w20
	.cfi_restore w21
	.cfi_restore w22
	.cfi_restore w23
	.cfi_restore w24
	.cfi_restore w28
	.cfi_restore w30
	.cfi_restore w29
	ret
.LBB12_21:
	.cfi_restore_state
	bl	_RNvNtCs8l20omZJ7ql_4core6option13unwrap_failed
.Lfunc_end12:
	.size	_RNvMs_NtCs7Pyp4CbMBld_9lean_xmss6schemeNtB4_14LayerSignature4read, .Lfunc_end12-_RNvMs_NtCs7Pyp4CbMBld_9lean_xmss6schemeNtB4_14LayerSignature4read
	.cfi_endproc

	.section	.text._RNvNtCs7Pyp4CbMBld_9lean_xmss4wots9wots_leaf,"ax",@progbits
	.p2align	2
	.type	_RNvNtCs7Pyp4CbMBld_9lean_xmss4wots9wots_leaf,@function
_RNvNtCs7Pyp4CbMBld_9lean_xmss4wots9wots_leaf:
.Lfunc_begin13:
	.cfi_startproc
	stp	x29, x30, [sp, #-96]!
	.cfi_def_cfa_offset 96
	stp	x28, x27, [sp, #16]
	stp	x26, x25, [sp, #32]
	stp	x24, x23, [sp, #48]
	stp	x22, x21, [sp, #64]
	stp	x20, x19, [sp, #80]
	mov	x29, sp
	.cfi_def_cfa w29, 96
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
	sub	sp, sp, #2656
	lsl	w8, w2, #7
	lsl	w9, w2, #23
	ldr	xzr, [sp]
	mov	x20, x1
	mov	x19, x0
	add	x0, sp, #32
	strb	w8, [sp, #1782]
	mov	w8, #12
	mov	w1, wzr
	mov	w2, #344
	mov	x22, x7
	mov	x23, x6
	mov	x24, x5
	mov	x25, x4
	stp	w3, w9, [sp, #24]
	str	w3, [sp, #1776]
	strh	w9, [sp, #1780]
	strb	w8, [sp, #1783]
	str	xzr, [sp, #1784]
	bl	memset
	add	x0, sp, #32
	mov	x1, x20
	mov	w2, #16
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	add	x0, sp, #32
	add	x1, sp, #1776
	mov	w2, #16
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	add	x0, sp, #32
	mov	x1, x25
	mov	x2, x24
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	add	x0, sp, #32
	mov	x1, x23
	mov	w2, #16
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	add	x0, sp, #1776
	add	x1, sp, #32
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher8finalize
	ldr	x8, [sp, #1784]
	tst	x8, #0xfff0000000000000
	b.ne	.LBB13_5
	mov	x10, #6148914691236517205
	ldr	x9, [sp, #1776]
	mov	x11, #-6148914691236517206
	movk	x10, #5, lsl #48
	movk	x11, #10, lsl #48
	and	x10, x8, x10
	lsr	x13, x9, #2
	and	x14, x9, #0xaaaaaaaaaaaaaaaa
	lsr	x12, x10, #2
	sub	x14, x14, x14, lsr #1
	and	x11, x8, x11
	and	x10, x10, #0x3333333333333333
	and	x15, x9, #0x1111111111111111
	and	x13, x13, #0x1111111111111111
	and	x12, x12, #0x3333333333333333
	sub	x11, x11, x11, lsr #1
	add	x10, x10, x12
	add	x12, x15, x13
	lsr	x13, x14, #2
	lsr	x16, x11, #2
	and	x14, x14, #0x3333333333333333
	add	x12, x12, x12, lsr #4
	and	x13, x13, #0x3333333333333333
	and	x11, x11, #0x3333333333333333
	add	x10, x10, x10, lsr #4
	add	x13, x14, x13
	and	x14, x16, #0x3333333333333333
	mov	x15, #72340172838076673
	add	x13, x13, x13, lsr #4
	add	x11, x11, x14
	and	x12, x12, #0xf0f0f0f0f0f0f0f
	add	x11, x11, x11, lsr #4
	mul	x12, x12, x15
	and	x10, x10, #0xf0f0f0f0f0f0f0f
	and	x13, x13, #0xf0f0f0f0f0f0f0f
	mul	x13, x13, x15
	and	x11, x11, #0xf0f0f0f0f0f0f0f
	mul	x10, x10, x15
	lsr	x12, x12, #56
	mul	x11, x11, x15
	lsr	x13, x13, #56
	add	x10, x12, x10, lsr #56
	add	x11, x13, x11, lsr #56
	add	w10, w10, w11, lsl #1
	cmp	w10, #106
	b.ne	.LBB13_5
	add	x11, sp, #380
	lsl	x10, x8, #1
	mov	w12, #6
	orr	x11, x11, #0x1
	str	x19, [sp]
.LBB13_3:
	sub	x13, x12, #6
	sub	x14, x12, #4
	sub	x15, x12, #2
	mvn	w17, w13
	mvn	w1, w14
	lsr	x16, x9, x13
	lsr	x0, x9, x14
	lsl	x17, x10, x17
	lsl	x1, x10, x1
	lsr	x18, x8, x13
	mvn	w2, w15
	tst	x13, #0x40
	orr	x16, x17, x16
	orr	x17, x1, x0
	lsr	x0, x8, x14
	lsr	x13, x9, x15
	lsl	x2, x10, x2
	csel	x16, x18, x16, ne
	tst	x14, #0x40
	mvn	w18, w12
	and	w16, w16, #0x3
	csel	x14, x0, x17, ne
	lsr	x17, x8, x15
	orr	x13, x2, x13
	tst	x15, #0x40
	lsr	x15, x9, x12
	lsl	x18, x10, x18
	csel	x13, x17, x13, ne
	lsr	x17, x8, x12
	tst	x12, #0x40
	orr	x15, x18, x15
	and	w14, w14, #0x3
	and	w13, w13, #0x3
	csel	x15, x17, x15, ne
	strb	w14, [x11]
	add	x12, x12, #8
	and	w14, w15, #0x3
	sturb	w16, [x11, #-1]
	cmp	x12, #118
	strb	w13, [x11, #1]
	strb	w14, [x11, #2]
	add	x11, x11, #4
	b.ne	.LBB13_3
	ubfx	x9, x8, #48, #2
	lsr	x8, x8, #50
	add	x10, sp, #1776
	add	x11, sp, #1432
	mov	x28, xzr
	add	x21, x10, #200
	strb	w8, [sp, #437]
	ldr	w8, [sp, #28]
	add	x23, x11, #200
	strb	w9, [sp, #436]
	add	x9, sp, #380
	mov	w19, #136
	lsr	w8, w8, #16
	str	x22, [sp, #8]
	str	w8, [sp, #20]
	b	.LBB13_8
.LBB13_5:
	strb	wzr, [x19]
.LBB13_6:
	add	sp, sp, #2656
	.cfi_def_cfa wsp, 96
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
.LBB13_7:
	.cfi_restore_state
	add	x8, sp, #440
	ldr	x9, [sp, #1384]
	ldr	x10, [sp, #1392]
	add	x8, x8, x28, lsl #4
	add	x28, x28, #1
	ldr	x22, [sp, #8]
	cmp	x28, #58
	stp	x9, x10, [x8]
	add	x9, sp, #380
	b.eq	.LBB13_27
.LBB13_8:
	add	x8, x22, x28, lsl #4
	ldrb	w22, [x9, x28]
	ldp	x9, x8, [x8]
	cmp	x22, #2
	str	x9, [sp, #1384]
	str	x8, [sp, #1392]
	b.hi	.LBB13_7
.LBB13_9:
	ldr	x8, [sp, #1384]
	ldr	x9, [sp, #1392]
	add	x0, sp, #1776
	mov	w1, wzr
	mov	w2, #344
	str	xzr, [sp, #1424]
	str	x8, [sp, #1400]
	str	x9, [sp, #1408]
	ldp	w9, w8, [sp, #20]
	str	x28, [sp, #1416]
	stur	xzr, [x29, #-144]
	stur	w8, [x29, #-152]
	mov	w8, #1
	orr	w8, w8, w22, lsl #5
	sturb	w9, [x29, #-146]
	ldr	w9, [sp, #28]
	sturh	w9, [x29, #-148]
	sturb	w8, [x29, #-145]
	bl	memset
	ldr	x8, [sp, #2112]
	ldp	x9, x10, [x20]
	add	x0, x8, #16
	cmp	x0, #136
	stp	x9, x10, [x21]
	str	x0, [sp, #2112]
	b.ne	.LBB13_11
	ldr	x9, [sp, #1976]
	ldr	x14, [sp, #1776]
	ldr	x10, [sp, #1984]
	ldr	x15, [sp, #1784]
	ldr	x8, [sp, #1992]
	ldr	x16, [sp, #2000]
	eor	x9, x14, x9
	ldr	x14, [sp, #1800]
	ldr	x12, [sp, #2008]
	eor	x10, x15, x10
	str	x9, [sp, #1776]
	ldr	x9, [sp, #1792]
	str	x10, [sp, #1784]
	ldr	x10, [sp, #1808]
	ldr	x13, [sp, #2016]
	eor	x8, x9, x8
	eor	x9, x14, x16
	ldr	x11, [sp, #2024]
	str	x8, [sp, #1792]
	ldr	x8, [sp, #1816]
	ldr	x15, [sp, #2032]
	str	x9, [sp, #1800]
	eor	x9, x10, x12
	ldr	x10, [sp, #1824]
	eor	x8, x8, x13
	ldr	x18, [sp, #2040]
	ldr	x12, [sp, #1832]
	ldr	x13, [sp, #1840]
	ldr	x14, [sp, #2048]
	ldr	x0, [sp, #1848]
	str	x8, [sp, #1816]
	eor	x8, x10, x11
	ldr	x16, [sp, #2056]
	eor	x10, x13, x18
	eor	x11, x0, x14
	add	x0, sp, #1776
	str	x9, [sp, #1808]
	eor	x9, x12, x15
	ldr	x13, [sp, #2064]
	str	x8, [sp, #1824]
	ldr	x8, [sp, #1864]
	ldr	x12, [sp, #1856]
	ldr	x14, [sp, #2072]
	str	x9, [sp, #1832]
	ldr	x9, [sp, #1872]
	eor	x8, x8, x13
	eor	x12, x12, x16
	str	x10, [sp, #1840]
	eor	x9, x9, x14
	ldr	x10, [sp, #2080]
	str	x11, [sp, #1848]
	ldr	x11, [sp, #1880]
	ldr	x13, [sp, #2088]
	str	x8, [sp, #1864]
	ldr	x8, [sp, #1888]
	ldr	x17, [sp, #1904]
	str	x12, [sp, #1856]
	eor	x10, x11, x10
	ldr	x11, [sp, #2096]
	str	x9, [sp, #1872]
	eor	x8, x8, x13
	ldr	x9, [sp, #1896]
	ldr	x12, [sp, #2104]
	str	x8, [sp, #1888]
	eor	x9, x9, x11
	eor	x8, x17, x12
	str	x10, [sp, #1880]
	str	x9, [sp, #1896]
	str	x8, [sp, #1904]
	bl	_RNvCsndc0WgnAaH_9keccak2568keccak_f
	mov	x0, xzr
	str	xzr, [sp, #2112]
.LBB13_11:
	add	x22, x22, #1
	sub	x24, x29, #152
	mov	w26, #16
	b	.LBB13_13
.LBB13_12:
	sub	x26, x26, x25
	add	x24, x24, x25
	cbz	x26, .LBB13_17
.LBB13_13:
	sub	x8, x19, x0
	cmp	x26, x8
	csel	x25, x26, x8, lo
	add	x1, x25, x0
	cmp	x1, x0
	b.lo	.LBB13_25
	cmp	x1, #137
	b.hs	.LBB13_25
	add	x0, x21, x0
	mov	x1, x24
	mov	x2, x25
	bl	memcpy
	ldr	x8, [sp, #2112]
	add	x0, x8, x25
	cmp	x0, #136
	str	x0, [sp, #2112]
	b.ne	.LBB13_12
	ldr	x9, [sp, #1976]
	ldr	x14, [sp, #1776]
	ldr	x10, [sp, #1984]
	ldr	x15, [sp, #1784]
	ldr	x8, [sp, #1992]
	ldr	x16, [sp, #2000]
	eor	x9, x14, x9
	ldr	x14, [sp, #1800]
	ldr	x12, [sp, #2008]
	eor	x10, x15, x10
	str	x9, [sp, #1776]
	ldr	x9, [sp, #1792]
	str	x10, [sp, #1784]
	ldr	x10, [sp, #1808]
	ldr	x13, [sp, #2016]
	eor	x8, x9, x8
	eor	x9, x14, x16
	ldr	x11, [sp, #2024]
	str	x8, [sp, #1792]
	ldr	x8, [sp, #1816]
	ldr	x15, [sp, #2032]
	str	x9, [sp, #1800]
	eor	x9, x10, x12
	ldr	x10, [sp, #1824]
	eor	x8, x8, x13
	ldr	x18, [sp, #2040]
	ldr	x12, [sp, #1832]
	ldr	x13, [sp, #1840]
	ldr	x14, [sp, #2048]
	ldr	x0, [sp, #1848]
	str	x8, [sp, #1816]
	eor	x8, x10, x11
	ldr	x16, [sp, #2056]
	eor	x10, x13, x18
	eor	x11, x0, x14
	add	x0, sp, #1776
	str	x9, [sp, #1808]
	eor	x9, x12, x15
	ldr	x13, [sp, #2064]
	str	x8, [sp, #1824]
	ldr	x8, [sp, #1864]
	ldr	x12, [sp, #1856]
	ldr	x14, [sp, #2072]
	str	x9, [sp, #1832]
	ldr	x9, [sp, #1872]
	eor	x8, x8, x13
	eor	x12, x12, x16
	str	x10, [sp, #1840]
	eor	x9, x9, x14
	ldr	x10, [sp, #2080]
	str	x11, [sp, #1848]
	ldr	x11, [sp, #1880]
	ldr	x13, [sp, #2088]
	str	x8, [sp, #1864]
	ldr	x8, [sp, #1888]
	ldr	x17, [sp, #1904]
	str	x12, [sp, #1856]
	eor	x10, x11, x10
	ldr	x11, [sp, #2096]
	str	x9, [sp, #1872]
	eor	x8, x8, x13
	ldr	x9, [sp, #1896]
	ldr	x12, [sp, #2104]
	str	x8, [sp, #1888]
	eor	x9, x9, x11
	eor	x8, x17, x12
	str	x10, [sp, #1880]
	str	x9, [sp, #1896]
	str	x8, [sp, #1904]
	bl	_RNvCsndc0WgnAaH_9keccak2568keccak_f
	mov	x0, xzr
	str	xzr, [sp, #2112]
	b	.LBB13_12
.LBB13_17:
	add	x0, sp, #1432
	add	x1, sp, #1776
	mov	w2, #344
	bl	memcpy
	ldr	x26, [sp, #1768]
	add	x24, sp, #1400
	mov	w27, #32
	b	.LBB13_19
.LBB13_18:
	sub	x27, x27, x25
	add	x24, x24, x25
	cbz	x27, .LBB13_23
.LBB13_19:
	sub	x8, x19, x26
	cmp	x27, x8
	csel	x25, x27, x8, lo
	add	x1, x25, x26
	cmp	x1, x26
	b.lo	.LBB13_26
	cmp	x1, #137
	b.hs	.LBB13_26
	add	x0, x23, x26
	mov	x1, x24
	mov	x2, x25
	bl	memcpy
	ldr	x8, [sp, #1768]
	add	x26, x8, x25
	cmp	x26, #136
	str	x26, [sp, #1768]
	b.ne	.LBB13_18
	ldr	x9, [sp, #1632]
	ldr	x14, [sp, #1432]
	ldr	x10, [sp, #1640]
	ldr	x15, [sp, #1440]
	ldr	x8, [sp, #1648]
	ldr	x16, [sp, #1656]
	eor	x9, x14, x9
	ldr	x14, [sp, #1456]
	ldr	x12, [sp, #1664]
	eor	x10, x15, x10
	str	x9, [sp, #1432]
	ldr	x9, [sp, #1448]
	str	x10, [sp, #1440]
	ldr	x10, [sp, #1464]
	ldr	x13, [sp, #1672]
	eor	x8, x9, x8
	eor	x9, x14, x16
	ldr	x11, [sp, #1680]
	str	x8, [sp, #1448]
	ldr	x8, [sp, #1472]
	ldr	x15, [sp, #1688]
	str	x9, [sp, #1456]
	eor	x9, x10, x12
	ldr	x10, [sp, #1480]
	eor	x8, x8, x13
	ldr	x18, [sp, #1696]
	ldr	x12, [sp, #1488]
	ldr	x13, [sp, #1496]
	ldr	x14, [sp, #1704]
	ldr	x0, [sp, #1504]
	str	x8, [sp, #1472]
	eor	x8, x10, x11
	ldr	x16, [sp, #1712]
	eor	x10, x13, x18
	eor	x11, x0, x14
	add	x0, sp, #1432
	str	x9, [sp, #1464]
	eor	x9, x12, x15
	ldr	x13, [sp, #1720]
	str	x8, [sp, #1480]
	ldr	x8, [sp, #1520]
	ldr	x12, [sp, #1512]
	ldr	x14, [sp, #1728]
	str	x9, [sp, #1488]
	ldr	x9, [sp, #1528]
	eor	x8, x8, x13
	eor	x12, x12, x16
	str	x10, [sp, #1496]
	eor	x9, x9, x14
	ldr	x10, [sp, #1736]
	str	x11, [sp, #1504]
	ldr	x11, [sp, #1536]
	ldr	x13, [sp, #1744]
	str	x8, [sp, #1520]
	ldr	x8, [sp, #1544]
	ldr	x17, [sp, #1560]
	str	x12, [sp, #1512]
	eor	x10, x11, x10
	ldr	x11, [sp, #1752]
	str	x9, [sp, #1528]
	eor	x8, x8, x13
	ldr	x9, [sp, #1552]
	ldr	x12, [sp, #1760]
	str	x8, [sp, #1544]
	eor	x9, x9, x11
	eor	x8, x17, x12
	str	x10, [sp, #1536]
	str	x9, [sp, #1552]
	str	x8, [sp, #1560]
	bl	_RNvCsndc0WgnAaH_9keccak2568keccak_f
	mov	x26, xzr
	str	xzr, [sp, #1768]
	b	.LBB13_18
.LBB13_23:
	add	x0, sp, #1776
	add	x1, sp, #1432
	mov	w2, #200
	bl	memcpy
	cmp	x26, #137
	b.hs	.LBB13_28
	sub	x0, x29, #152
	mov	x1, x23
	mov	x2, x26
	stp	xzr, xzr, [x29, #-32]
	stp	xzr, xzr, [x29, #-48]
	stp	xzr, xzr, [x29, #-64]
	stp	xzr, xzr, [x29, #-80]
	stp	xzr, xzr, [x29, #-96]
	stp	xzr, xzr, [x29, #-112]
	stp	xzr, xzr, [x29, #-128]
	stp	xzr, xzr, [x29, #-144]
	stur	xzr, [x29, #-152]
	bl	memcpy
	sub	x9, x29, #152
	ldr	x0, [sp, #1784]
	ldrb	w8, [x9, x26]
	eor	w8, w8, #0x1
	strb	w8, [x9, x26]
	ldp	x10, x11, [x29, #-152]
	ldr	x8, [sp, #1776]
	ldp	x12, x13, [x29, #-136]
	ldurb	w9, [x29, #-17]
	ldp	x14, x15, [x29, #-120]
	ldur	x1, [x29, #-72]
	eor	x8, x8, x10
	ldr	x10, [sp, #1792]
	eor	x11, x0, x11
	str	x8, [sp, #1776]
	ldp	x16, x17, [x29, #-104]
	eor	x8, x10, x12
	ldr	x10, [sp, #1808]
	ldr	x0, [sp, #1800]
	str	x8, [sp, #1792]
	eor	w9, w9, #0x80
	ldr	x12, [sp, #1816]
	eor	x8, x10, x14
	ldr	x10, [sp, #1824]
	sturb	w9, [x29, #-17]
	ldp	x9, x18, [x29, #-88]
	str	x11, [sp, #1784]
	eor	x11, x0, x13
	str	x8, [sp, #1808]
	eor	x8, x10, x16
	str	x11, [sp, #1800]
	eor	x11, x12, x15
	ldr	x12, [sp, #1832]
	ldr	x10, [sp, #1848]
	str	x8, [sp, #1824]
	ldr	x13, [sp, #1840]
	ldp	x14, x8, [x29, #-64]
	str	x11, [sp, #1816]
	ldr	x11, [sp, #1864]
	eor	x12, x12, x17
	eor	x10, x10, x18
	eor	x9, x13, x9
	ldr	x13, [sp, #1856]
	str	x12, [sp, #1832]
	ldr	x12, [sp, #1872]
	eor	x11, x11, x14
	str	x10, [sp, #1848]
	ldp	x14, x10, [x29, #-48]
	str	x9, [sp, #1840]
	ldr	x9, [sp, #1880]
	eor	x13, x13, x1
	eor	x8, x12, x8
	str	x13, [sp, #1856]
	ldr	x12, [sp, #1888]
	add	x0, sp, #1776
	eor	x9, x9, x14
	str	x8, [sp, #1872]
	ldp	x13, x8, [x29, #-32]
	str	x11, [sp, #1864]
	ldr	x11, [sp, #1896]
	str	x9, [sp, #1880]
	ldr	x9, [sp, #1904]
	eor	x10, x12, x10
	eor	x11, x11, x13
	eor	x8, x9, x8
	str	x10, [sp, #1888]
	str	x11, [sp, #1896]
	str	x8, [sp, #1904]
	bl	_RNvCsndc0WgnAaH_9keccak2568keccak_f
	ldr	x8, [sp, #1784]
	ldr	x9, [sp, #1776]
	cmp	x22, #3
	stp	x9, x8, [x29, #-152]
	str	x9, [sp, #1384]
	str	x8, [sp, #1392]
	b.ne	.LBB13_9
	b	.LBB13_7
.LBB13_25:
	adrp	x3, .Lanon.47fac95803119c4a094797088418c9d4.11
	add	x3, x3, :lo12:.Lanon.47fac95803119c4a094797088418c9d4.11
	mov	w2, #136
	bl	_RNvNtNtCs8l20omZJ7ql_4core5slice5index16slice_index_fail
.LBB13_26:
	adrp	x3, .Lanon.47fac95803119c4a094797088418c9d4.11
	add	x3, x3, :lo12:.Lanon.47fac95803119c4a094797088418c9d4.11
	mov	x0, x26
	mov	w2, #136
	bl	_RNvNtNtCs8l20omZJ7ql_4core5slice5index16slice_index_fail
.LBB13_27:
	ldp	w8, w9, [sp, #20]
	add	x0, sp, #2160
	mov	w1, wzr
	mov	w2, #344
	str	xzr, [sp, #1784]
	strb	w8, [sp, #1782]
	ldr	w8, [sp, #28]
	str	w9, [sp, #1776]
	strh	w8, [sp, #1780]
	mov	w8, #2
	strb	w8, [sp, #1783]
	bl	memset
	add	x0, sp, #2160
	mov	x1, x20
	mov	w2, #16
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	add	x0, sp, #2160
	add	x1, sp, #1776
	mov	w2, #16
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	add	x0, sp, #2160
	add	x1, sp, #440
	mov	w2, #928
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	add	x0, sp, #2128
	add	x1, sp, #2160
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher8finalize
	add	x11, sp, #380
	ldp	x8, x9, [x11, #32]
	ldr	x10, [x11, #48]
	str	x10, [sp, #1824]
	str	x8, [sp, #1808]
	ldrh	w8, [x11, #56]
	str	x9, [sp, #1816]
	strh	w8, [sp, #1832]
	ldp	x9, x8, [x11]
	str	x8, [sp, #1784]
	ldp	x10, x8, [x11, #16]
	str	x9, [sp, #1776]
	ldr	x9, [sp, #2136]
	add	x11, sp, #1776
	str	x10, [sp, #1792]
	ldr	x10, [sp, #2128]
	str	x8, [sp, #1800]
	ldr	x8, [sp, #1808]
	stur	x9, [x11, #66]
	ldr	x9, [sp, #1816]
	stur	x10, [x11, #58]
	ldr	x11, [sp]
	ldr	x10, [sp, #1832]
	stur	x8, [x11, #33]
	ldr	x8, [sp, #1824]
	stur	x9, [x11, #41]
	ldr	x9, [sp, #1776]
	stur	x8, [x11, #49]
	ldr	x8, [sp, #1784]
	stur	x9, [x11, #1]
	ldr	x9, [sp, #1792]
	stur	x8, [x11, #9]
	ldr	x8, [sp, #1800]
	stur	x9, [x11, #17]
	ldr	x9, [sp, #1840]
	stur	x8, [x11, #25]
	ldrh	w8, [sp, #1848]
	stur	x9, [x11, #65]
	sturh	w8, [x11, #73]
	mov	w8, #1
	stur	x10, [x11, #57]
	strb	w8, [x11]
	b	.LBB13_6
.LBB13_28:
	adrp	x3, .Lanon.47fac95803119c4a094797088418c9d4.12
	add	x3, x3, :lo12:.Lanon.47fac95803119c4a094797088418c9d4.12
	mov	x0, xzr
	mov	x1, x26
	mov	w2, #136
	bl	_RNvNtNtCs8l20omZJ7ql_4core5slice5index16slice_index_fail
.Lfunc_end13:
	.size	_RNvNtCs7Pyp4CbMBld_9lean_xmss4wots9wots_leaf, .Lfunc_end13-_RNvNtCs7Pyp4CbMBld_9lean_xmss4wots9wots_leaf
	.cfi_endproc

	.type	.Lanon.46a40f786ce4ddedc5d90764d599cb89.173,@object
	.section	.rodata..Lanon.46a40f786ce4ddedc5d90764d599cb89.173,"a",@progbits
.Lanon.46a40f786ce4ddedc5d90764d599cb89.173:
	.ascii	"called `Option::unwrap()` on a `None` value"
	.size	.Lanon.46a40f786ce4ddedc5d90764d599cb89.173, 43

	.type	.Lanon.46a40f786ce4ddedc5d90764d599cb89.203,@object
	.section	.rodata.str1.1,"aMS",@progbits,1
.Lanon.46a40f786ce4ddedc5d90764d599cb89.203:
	.asciz	"\020range end index \300\" out of range for slice of length \300"
	.size	.Lanon.46a40f786ce4ddedc5d90764d599cb89.203, 55

	.type	.Lanon.46a40f786ce4ddedc5d90764d599cb89.204,@object
.Lanon.46a40f786ce4ddedc5d90764d599cb89.204:
	.asciz	"\026slice index starts at \300\r but ends at \300"
	.size	.Lanon.46a40f786ce4ddedc5d90764d599cb89.204, 40

	.type	.Lanon.46a40f786ce4ddedc5d90764d599cb89.205,@object
.Lanon.46a40f786ce4ddedc5d90764d599cb89.205:
	.asciz	"\022range start index \300\" out of range for slice of length \300"
	.size	.Lanon.46a40f786ce4ddedc5d90764d599cb89.205, 57

	.type	.Lanon.47fac95803119c4a094797088418c9d4.1,@object
	.section	.rodata..Lanon.47fac95803119c4a094797088418c9d4.1,"a",@progbits
	.p2align	3, 0x0
.Lanon.47fac95803119c4a094797088418c9d4.1:
	.ascii	"\001\000\000\000\000\000\000\000\202\200\000\000\000\000\000\000\212\200\000\000\000\000\000\200\000\200\000\200\000\000\000\200\213\200\000\000\000\000\000\000\001\000\000\200\000\000\000\000\201\200\000\200\000\000\000\200\t\200\000\000\000\000\000\200\212\000\000\000\000\000\000\000\210\000\000\000\000\000\000\000\t\200\000\200\000\000\000\000\n\000\000\200\000\000\000\000\213\200\000\200\000\000\000\000\213\000\000\000\000\000\000\200\211\200\000\000\000\000\000\200\003\200\000\000\000\000\000\200\002\200\000\000\000\000\000\200\200\000\000\000\000\000\000\200\n\200\000\000\000\000\000\000\n\000\000\200\000\000\000\200\201\200\000\200\000\000\000\200\200\200\000\000\000\000\000\200\001\000\000\200\000\000\000\000\b\200\000\200\000\000\000\200"
	.size	.Lanon.47fac95803119c4a094797088418c9d4.1, 192

	.type	.Lanon.47fac95803119c4a094797088418c9d4.3,@object
	.section	.rodata.str1.1,"aMS",@progbits,1
.Lanon.47fac95803119c4a094797088418c9d4.3:
	.asciz	"crates/keccak256/src/lib.rs"
	.size	.Lanon.47fac95803119c4a094797088418c9d4.3, 28

	.type	.Lanon.47fac95803119c4a094797088418c9d4.8,@object
	.section	.rodata..Lanon.47fac95803119c4a094797088418c9d4.8,"a",@progbits
.Lanon.47fac95803119c4a094797088418c9d4.8:
	.ascii	"a final block holds fewer than RATE message bytes"
	.size	.Lanon.47fac95803119c4a094797088418c9d4.8, 49

	.type	.Lanon.47fac95803119c4a094797088418c9d4.9,@object
	.section	.data.rel.ro..Lanon.47fac95803119c4a094797088418c9d4.9,"aw",@progbits
	.p2align	3, 0x0
.Lanon.47fac95803119c4a094797088418c9d4.9:
	.xword	.Lanon.47fac95803119c4a094797088418c9d4.3
	.asciz	"\033\000\000\000\000\000\000\000\200\000\000\000\005\000\000"
	.size	.Lanon.47fac95803119c4a094797088418c9d4.9, 24

	.type	.Lanon.47fac95803119c4a094797088418c9d4.11,@object
	.section	.data.rel.ro..Lanon.47fac95803119c4a094797088418c9d4.11,"aw",@progbits
	.p2align	3, 0x0
.Lanon.47fac95803119c4a094797088418c9d4.11:
	.xword	.Lanon.47fac95803119c4a094797088418c9d4.3
	.asciz	"\033\000\000\000\000\000\000\000\247\000\000\000\025\000\000"
	.size	.Lanon.47fac95803119c4a094797088418c9d4.11, 24

	.type	.Lanon.47fac95803119c4a094797088418c9d4.12,@object
	.section	.data.rel.ro..Lanon.47fac95803119c4a094797088418c9d4.12,"aw",@progbits
	.p2align	3, 0x0
.Lanon.47fac95803119c4a094797088418c9d4.12:
	.xword	.Lanon.47fac95803119c4a094797088418c9d4.3
	.asciz	"\033\000\000\000\000\000\000\000\264\000\000\0002\000\000"
	.size	.Lanon.47fac95803119c4a094797088418c9d4.12, 24

	.type	.Lanon.bee145f0cb2eac5728ff95be1b200579.0,@object
	.section	.rodata.str1.1,"aMS",@progbits,1
.Lanon.bee145f0cb2eac5728ff95be1b200579.0:
	.asciz	"crates/lean_sphincs/src/scheme.rs"
	.size	.Lanon.bee145f0cb2eac5728ff95be1b200579.0, 34

	.type	.Lanon.bee145f0cb2eac5728ff95be1b200579.2,@object
	.section	.rodata..Lanon.bee145f0cb2eac5728ff95be1b200579.2,"a",@progbits
	.p2align	3, 0x0
.Lanon.bee145f0cb2eac5728ff95be1b200579.2:
	.asciz	"\b\000\000\000\000\000\000\000\b\000\000\000\000\000\000\000\n\000\000\000\000\000\000"
	.size	.Lanon.bee145f0cb2eac5728ff95be1b200579.2, 24

	.type	.Lanon.bee145f0cb2eac5728ff95be1b200579.4,@object
	.section	.data.rel.ro..Lanon.bee145f0cb2eac5728ff95be1b200579.4,"aw",@progbits
	.p2align	3, 0x0
.Lanon.bee145f0cb2eac5728ff95be1b200579.4:
	.xword	.Lanon.bee145f0cb2eac5728ff95be1b200579.0
	.asciz	"!\000\000\000\000\000\000\000c\000\000\000\024\000\000"
	.size	.Lanon.bee145f0cb2eac5728ff95be1b200579.4, 24

	.type	.Lanon.9dc208de841c72058cf8117eb5c1924c.0,@object
	.section	.rodata.str1.1,"aMS",@progbits,1
.Lanon.9dc208de841c72058cf8117eb5c1924c.0:
	.asciz	"crates/lean_xmss/src/scheme.rs"
	.size	.Lanon.9dc208de841c72058cf8117eb5c1924c.0, 31

	.type	.Lanon.9dc208de841c72058cf8117eb5c1924c.1,@object
	.section	.data.rel.ro..Lanon.9dc208de841c72058cf8117eb5c1924c.1,"aw",@progbits
	.p2align	3, 0x0
.Lanon.9dc208de841c72058cf8117eb5c1924c.1:
	.xword	.Lanon.9dc208de841c72058cf8117eb5c1924c.0
	.asciz	"\036\000\000\000\000\000\000\000J\000\000\0002\000\000"
	.size	.Lanon.9dc208de841c72058cf8117eb5c1924c.1, 24

	.section	.debug_abbrev,"",@progbits
	.byte	1
	.byte	17
	.byte	1
	.byte	37
	.byte	14
	.byte	19
	.byte	5
	.byte	3
	.byte	14
	.byte	16
	.byte	23
	.byte	27
	.byte	14
	.byte	17
	.byte	1
	.byte	85
	.byte	23
	.byte	0
	.byte	0
	.byte	2
	.byte	57
	.byte	1
	.byte	3
	.byte	14
	.byte	0
	.byte	0
	.byte	3
	.byte	46
	.byte	0
	.byte	17
	.byte	1
	.byte	18
	.byte	6
	.byte	64
	.byte	24
	.byte	110
	.byte	14
	.byte	3
	.byte	14
	.byte	58
	.byte	11
	.byte	59
	.byte	11
	.byte	63
	.byte	25
	.ascii	"\207\001"
	.byte	25
	.byte	0
	.byte	0
	.byte	4
	.byte	46
	.byte	0
	.byte	17
	.byte	1
	.byte	18
	.byte	6
	.byte	64
	.byte	24
	.byte	110
	.byte	14
	.byte	3
	.byte	14
	.byte	58
	.byte	11
	.byte	59
	.byte	11
	.byte	54
	.byte	11
	.byte	63
	.byte	25
	.ascii	"\207\001"
	.byte	25
	.byte	0
	.byte	0
	.byte	5
	.byte	46
	.byte	0
	.byte	110
	.byte	14
	.byte	3
	.byte	14
	.byte	58
	.byte	11
	.byte	59
	.byte	5
	.ascii	"\207\001"
	.byte	25
	.byte	32
	.byte	11
	.byte	0
	.byte	0
	.byte	6
	.byte	46
	.byte	0
	.byte	110
	.byte	14
	.byte	3
	.byte	14
	.byte	58
	.byte	11
	.byte	59
	.byte	11
	.ascii	"\207\001"
	.byte	25
	.byte	32
	.byte	11
	.byte	0
	.byte	0
	.byte	7
	.byte	46
	.byte	1
	.byte	17
	.byte	1
	.byte	18
	.byte	6
	.byte	64
	.byte	24
	.byte	110
	.byte	14
	.byte	3
	.byte	14
	.byte	58
	.byte	11
	.byte	59
	.byte	11
	.byte	63
	.byte	25
	.ascii	"\207\001"
	.byte	25
	.byte	0
	.byte	0
	.byte	8
	.byte	29
	.byte	1
	.byte	49
	.byte	19
	.byte	17
	.byte	1
	.byte	18
	.byte	6
	.byte	88
	.byte	11
	.byte	89
	.byte	11
	.byte	87
	.byte	11
	.byte	0
	.byte	0
	.byte	9
	.byte	29
	.byte	0
	.byte	49
	.byte	19
	.byte	17
	.byte	1
	.byte	18
	.byte	6
	.byte	88
	.byte	11
	.byte	89
	.byte	5
	.byte	87
	.byte	11
	.byte	0
	.byte	0
	.byte	10
	.byte	29
	.byte	1
	.byte	49
	.byte	19
	.byte	17
	.byte	1
	.byte	18
	.byte	6
	.byte	88
	.byte	11
	.byte	89
	.byte	11
	.byte	87
	.byte	11
	.ascii	"\266B"
	.byte	11
	.byte	0
	.byte	0
	.byte	11
	.byte	29
	.byte	0
	.byte	49
	.byte	19
	.byte	17
	.byte	1
	.byte	18
	.byte	6
	.byte	88
	.byte	11
	.byte	89
	.byte	5
	.byte	87
	.byte	11
	.ascii	"\266B"
	.byte	11
	.byte	0
	.byte	0
	.byte	12
	.byte	46
	.byte	0
	.byte	17
	.byte	1
	.byte	18
	.byte	6
	.byte	64
	.byte	24
	.byte	110
	.byte	14
	.byte	3
	.byte	14
	.byte	58
	.byte	11
	.byte	59
	.byte	5
	.byte	54
	.byte	11
	.byte	63
	.byte	25
	.ascii	"\207\001"
	.byte	25
	.byte	0
	.byte	0
	.byte	0
	.section	.debug_info,"",@progbits
.Lcu_begin0:
	.word	.Ldebug_info_end0-.Ldebug_info_start0
.Ldebug_info_start0:
	.hword	4
	.word	.debug_abbrev
	.byte	8
	.byte	1
	.word	.Linfo_string0
	.hword	28
	.word	.Linfo_string1
	.word	.Lline_table_start0
	.word	.Linfo_string2
	.xword	0
	.word	.Ldebug_ranges0
	.byte	2
	.word	.Linfo_string3
	.byte	2
	.word	.Linfo_string4
	.byte	3
	.xword	.Lfunc_begin5
	.word	.Lfunc_end5-.Lfunc_begin5
	.byte	1
	.byte	109
	.word	.Linfo_string15
	.word	.Linfo_string16
	.byte	1
	.byte	60


	.byte	4
	.xword	.Lfunc_begin7
	.word	.Lfunc_end7-.Lfunc_begin7
	.byte	1
	.byte	109
	.word	.Linfo_string18
	.word	.Linfo_string19
	.byte	1
	.byte	138
	.byte	3


	.byte	0
	.byte	2
	.word	.Linfo_string5
	.byte	2
	.word	.Linfo_string6
	.byte	2
	.word	.Linfo_string7
	.byte	2
	.word	.Linfo_string8
	.byte	5
	.word	.Linfo_string9
	.word	.Linfo_string10
	.byte	4
	.hword	2623

	.byte	1
	.byte	5
	.word	.Linfo_string12
	.word	.Linfo_string10
	.byte	4
	.hword	2623

	.byte	1
	.byte	0
	.byte	6
	.word	.Linfo_string11
	.word	.Linfo_string8
	.byte	3
	.byte	166

	.byte	1
	.byte	6
	.word	.Linfo_string13
	.word	.Linfo_string8
	.byte	3
	.byte	166

	.byte	1
	.byte	0
	.byte	7
	.xword	.Lfunc_begin6
	.word	.Lfunc_end6-.Lfunc_begin6
	.byte	1
	.byte	109
	.word	.Linfo_string17
	.word	.Linfo_string7
	.byte	2
	.byte	39


	.byte	8
	.word	151
	.xword	.Ltmp3
	.word	.Ltmp4-.Ltmp3
	.byte	3
	.byte	177
	.byte	9
	.byte	9
	.word	124
	.xword	.Ltmp3
	.word	.Ltmp4-.Ltmp3
	.byte	4
	.hword	2636
	.byte	9
	.byte	0
	.byte	10
	.word	163
	.xword	.Ltmp5
	.word	.Ltmp6-.Ltmp5
	.byte	3
	.byte	177
	.byte	9
	.byte	4
	.byte	11
	.word	137
	.xword	.Ltmp5
	.word	.Ltmp6-.Ltmp5
	.byte	4
	.hword	2636
	.byte	9
	.byte	4
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.byte	2
	.word	.Linfo_string14
	.byte	12
	.xword	.Lfunc_begin8
	.word	.Lfunc_end8-.Lfunc_begin8
	.byte	1
	.byte	109
	.word	.Linfo_string20
	.word	.Linfo_string21
	.byte	5
	.hword	2247
	.byte	3


	.byte	0
	.byte	0
	.byte	0
.Ldebug_info_end0:
	.section	.text.unlikely._RNvNtCs8l20omZJ7ql_4core9panicking9panic_fmt,"ax",@progbits
.Lsec_end0:
	.section	.text.unlikely._RNvNtNtCs8l20omZJ7ql_4core5slice5index16slice_index_fail,"ax",@progbits
.Lsec_end1:
	.section	.text.unlikely._RNvNtCs8l20omZJ7ql_4core9panicking5panic,"ax",@progbits
.Lsec_end2:
	.section	.text.unlikely._RNvNtCs8l20omZJ7ql_4core6option13unwrap_failed,"ax",@progbits
.Lsec_end3:
	.section	.debug_aranges,"",@progbits
	.word	92
	.hword	2
	.word	.Lcu_begin0
	.byte	8
	.byte	0
	.zero	4,255
	.xword	.Lfunc_begin5
	.xword	.Lsec_end0-.Lfunc_begin5
	.xword	.Lfunc_begin6
	.xword	.Lsec_end1-.Lfunc_begin6
	.xword	.Lfunc_begin7
	.xword	.Lsec_end2-.Lfunc_begin7
	.xword	.Lfunc_begin8
	.xword	.Lsec_end3-.Lfunc_begin8
	.xword	0
	.xword	0
	.section	.debug_ranges,"",@progbits
.Ldebug_ranges0:
	.xword	.Lfunc_begin5
	.xword	.Lfunc_end5
	.xword	.Lfunc_begin6
	.xword	.Lfunc_end6
	.xword	.Lfunc_begin7
	.xword	.Lfunc_end7
	.xword	.Lfunc_begin8
	.xword	.Lfunc_end8
	.xword	0
	.xword	0
	.section	.debug_str,"MS",@progbits,1
.Linfo_string0:
	.asciz	"clang LLVM (rustc version 1.99.1 (58cf8f9c3 2026-10-13))"
.Linfo_string1:
	.asciz	"/rustc/58cf8f9c35b355199727627d07ae34a4e2846d67/library/core/src/lib.rs/@/core.6121d71b78da2427-cgu.0"
.Linfo_string2:
	.asciz	"/rustc/58cf8f9c35b355199727627d07ae34a4e2846d67"
.Linfo_string3:
	.asciz	"core"
.Linfo_string4:
	.asciz	"panicking"
.Linfo_string5:
	.asciz	"slice"
.Linfo_string6:
	.asciz	"index"
.Linfo_string7:
	.asciz	"slice_index_fail"
.Linfo_string8:
	.asciz	"do_panic"
.Linfo_string9:
	.asciz	"_RNvNvNvNtNtCs8l20omZJ7ql_4core5slice5index16slice_index_fail8do_panic7runtime"
.Linfo_string10:
	.asciz	"runtime"
.Linfo_string11:
	.asciz	"_RNvNvNtNtCs8l20omZJ7ql_4core5slice5index16slice_index_fail8do_panic"
.Linfo_string12:
	.asciz	"_RNvNvNvNtNtCs8l20omZJ7ql_4core5slice5index16slice_index_fails0_8do_panic7runtime"
.Linfo_string13:
	.asciz	"_RNvNvNtNtCs8l20omZJ7ql_4core5slice5index16slice_index_fails0_8do_panic"
.Linfo_string14:
	.asciz	"option"
.Linfo_string15:
	.asciz	"_RNvNtCs8l20omZJ7ql_4core9panicking9panic_fmt"
.Linfo_string16:
	.asciz	"panic_fmt"
.Linfo_string17:
	.asciz	"_RNvNtNtCs8l20omZJ7ql_4core5slice5index16slice_index_fail"
.Linfo_string18:
	.asciz	"_RNvNtCs8l20omZJ7ql_4core9panicking5panic"
.Linfo_string19:
	.asciz	"panic"
.Linfo_string20:
	.asciz	"_RNvNtCs8l20omZJ7ql_4core6option13unwrap_failed"
.Linfo_string21:
	.asciz	"unwrap_failed"
	.ident	"rustc version 1.99.1 (58cf8f9c3 2026-10-13)"
	.section	".note.GNU-stack","",@progbits
	.section	.debug_line,"",@progbits
.Lline_table_start0:
