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
	sub	x9, sp, #5, lsl #12
.LBB3_1:
	sub	sp, sp, #1, lsl #12
	ldr	xzr, [sp]
	cmp	sp, x9
	b.ne	.LBB3_1
	sub	sp, sp, #1040
	ldr	xzr, [sp]
	ldp	x8, x9, [x0]
	add	x27, sp, #4, lsl #12
	add	x25, sp, #2, lsl #12
	mov	x19, x2
	mov	x21, x1
	add	x22, sp, #484
	add	x27, x27, #2624
	stp	x8, x9, [sp, #448]
	ldp	x8, x10, [x0, #16]
	add	x20, sp, #448
	add	x23, x2, #96
	mov	x24, #-4224
	add	x25, x25, #448
	mov	w26, #4224
	stp	x8, x10, [sp, #464]
	ldp	x9, x8, [x2]
	str	x9, [sp, #20048]
	str	x8, [sp, #20056]
.LBB3_3:
	add	x28, x23, x24
	add	x1, sp, #4, lsl #12
	add	x0, sp, #484
	ldr	x8, [x28, #4160]
	ldr	x9, [x28, #4168]
	ldr	x10, [x28, #4176]
	add	x1, x1, #2624
	mov	w2, #160
	str	x8, [sp, #19008]
	ldr	x8, [x28, #4184]
	str	x9, [sp, #19016]
	ldr	x9, [x28, #4192]
	stp	x10, x8, [x27, #16]
	ldr	x8, [x28, #4200]
	ldr	x10, [x28, #4216]
	stp	x9, x8, [x27, #32]
	ldr	x8, [x28, #4208]
	ldr	x9, [x28, #4232]
	stp	x8, x10, [x27, #48]
	ldr	x8, [x28, #4224]
	ldr	x10, [x28, #4248]
	stp	x8, x9, [x27, #64]
	ldr	x8, [x28, #4240]
	ldr	x9, [x28, #4264]
	stp	x8, x10, [x27, #80]
	ldr	x8, [x28, #4256]
	ldr	x10, [x28, #4280]
	stp	x8, x9, [x27, #96]
	ldr	x8, [x28, #4272]
	ldr	x9, [x28, #4296]
	stp	x8, x10, [x27, #112]
	ldr	x8, [x28, #4288]
	ldr	x10, [x28, #4312]
	stp	x8, x9, [x27, #128]
	ldr	x8, [x28, #4304]
	stp	x8, x10, [x27, #144]
	bl	memcpy
	ldr	x8, [x28, #4144]
	ldr	x9, [x28, #4152]
	add	x0, sp, #4, lsl #12
	add	x0, x0, #2624
	add	x1, sp, #484
	mov	w2, #176
	stp	x8, x9, [x22, #160]
	bl	memcpy
	add	x8, x25, x24
	add	x1, sp, #4, lsl #12
	mov	w2, #176
	add	x0, x8, x26
	add	x1, x1, #2624
	bl	memcpy
	adds	x24, x24, #176
	b.ne	.LBB3_3
	add	x25, sp, #2, lsl #12
	mov	w1, wzr
	mov	w2, #288
	add	x25, x25, #32
	add	x0, x25, #128
	bl	memset
	ldr	w23, [x19, #4240]
	mov	w9, #4244
	mov	x8, xzr
	add	x9, x19, x9
	add	x10, sp, #484
.LBB3_5:
	add	x11, x9, x8
	add	x13, x10, x8
	add	x8, x8, #16
	ldp	x12, x11, [x11]
	cmp	x8, #1024
	stp	x12, x11, [x13]
	b.ne	.LBB3_5
	add	x0, sp, #4, lsl #12
	add	x1, sp, #484
	mov	w2, #1024
	add	x0, x0, #2624
	add	x26, sp, #484
	bl	memcpy
	mov	w8, #5268
	mov	w9, #5284
	mov	w11, #5300
	add	x8, x19, x8
	add	x9, x19, x9
	add	x0, sp, #4, lsl #12
	ldp	x10, x8, [x8]
	add	x1, sp, #4, lsl #12
	ldp	x12, x9, [x9]
	add	x0, x0, #576
	add	x1, x1, #2624
	mov	w2, #1024
	str	x8, [sp, #8232]
	mov	w8, #5316
	str	x10, [sp, #8224]
	add	x10, x19, x11
	add	x8, x19, x8
	str	x9, [sp, #8248]
	ldp	x11, x9, [x10]
	ldp	x8, x10, [x8]
	str	x12, [sp, #8240]
	mov	w12, #5332
	str	x9, [sp, #8264]
	add	x9, x19, x12
	mov	w12, #5364
	str	x10, [sp, #8280]
	mov	w10, #5348
	str	x11, [sp, #8256]
	ldp	x9, x11, [x9]
	str	x8, [sp, #8272]
	add	x8, x19, x10
	ldp	x8, x10, [x8]
	str	x9, [sp, #8288]
	add	x9, x19, x12
	mov	w12, #5380
	str	x11, [sp, #8296]
	str	x8, [sp, #8304]
	ldp	x8, x11, [x9]
	add	x9, x19, x12
	str	x10, [sp, #8312]
	str	x8, [sp, #8320]
	ldp	x8, x10, [x9]
	str	x11, [sp, #8328]
	str	x10, [sp, #8344]
	str	x8, [sp, #8336]
	bl	memcpy
	add	x0, sp, #3, lsl #12
	add	x1, sp, #4, lsl #12
	mov	w2, #1024
	add	x0, x0, #3648
	add	x1, x1, #576
	bl	memcpy
	add	x0, sp, #3, lsl #12
	add	x1, sp, #3, lsl #12
	mov	w2, #1024
	add	x0, x0, #2624
	add	x1, x1, #3648
	bl	memcpy
	add	x0, sp, #4, lsl #12
	add	x1, sp, #3, lsl #12
	mov	w2, #1024
	add	x0, x0, #1600
	add	x1, x1, #2624
	bl	memcpy
	add	x0, sp, #3, lsl #12
	add	x1, sp, #4, lsl #12
	mov	w2, #1024
	add	x0, x0, #1600
	add	x1, x1, #1600
	bl	memcpy
	ldr	w24, [x19, #5396]
	mov	w9, #5400
	mov	x8, xzr
	add	x9, x19, x9
.LBB3_7:
	add	x10, x9, x8
	add	x12, x26, x8
	add	x8, x8, #16
	ldp	x11, x10, [x10]
	cmp	x8, #1024
	stp	x11, x10, [x12]
	b.ne	.LBB3_7
	add	x0, sp, #4, lsl #12
	add	x1, sp, #484
	mov	w2, #1024
	add	x0, x0, #2624
	add	x28, sp, #484
	bl	memcpy
	ldr	x8, [x19, #6424]
	ldr	x9, [x19, #6432]
	add	x0, sp, #4, lsl #12
	ldr	x10, [x19, #6440]
	add	x1, sp, #4, lsl #12
	add	x0, x0, #576
	stp	x8, x9, [x25, #128]
	ldr	x8, [x19, #6448]
	ldr	x9, [x19, #6456]
	str	x10, [sp, #8368]
	ldr	x10, [x19, #6480]
	add	x1, x1, #2624
	str	x8, [sp, #8376]
	ldr	x8, [x19, #6464]
	mov	w2, #1024
	str	x9, [sp, #8384]
	ldr	x9, [x19, #6496]
	str	x8, [sp, #8392]
	ldr	x8, [x19, #6472]
	str	x10, [sp, #8408]
	ldr	x10, [x19, #6512]
	str	x8, [sp, #8400]
	ldr	x8, [x19, #6488]
	str	x9, [sp, #8424]
	ldr	x9, [x19, #6528]
	str	x8, [sp, #8416]
	ldr	x8, [x19, #6504]
	str	x10, [sp, #8440]
	ldr	x10, [x19, #6544]
	str	x8, [sp, #8432]
	ldr	x8, [x19, #6520]
	str	x9, [sp, #8456]
	str	x8, [sp, #8448]
	ldr	x8, [x19, #6536]
	str	x10, [sp, #8472]
	str	x8, [sp, #8464]
	bl	memcpy
	add	x0, sp, #3, lsl #12
	add	x1, sp, #4, lsl #12
	mov	w2, #1024
	add	x0, x0, #3648
	add	x1, x1, #576
	bl	memcpy
	add	x0, sp, #3, lsl #12
	add	x1, sp, #3, lsl #12
	mov	w2, #1024
	add	x0, x0, #2624
	add	x1, x1, #3648
	bl	memcpy
	add	x0, sp, #4, lsl #12
	add	x1, sp, #3, lsl #12
	mov	w2, #1024
	add	x0, x0, #1600
	add	x1, x1, #2624
	bl	memcpy
	add	x0, sp, #3, lsl #12
	add	x1, sp, #4, lsl #12
	mov	w2, #1024
	add	x0, x0, #576
	add	x1, x1, #1600
	bl	memcpy
	ldr	w26, [x19, #6552]
	mov	w9, #6556
	mov	x8, xzr
	add	x9, x19, x9
.LBB3_9:
	add	x10, x9, x8
	add	x12, x28, x8
	add	x8, x8, #16
	ldp	x11, x10, [x10]
	cmp	x8, #1024
	stp	x11, x10, [x12]
	b.ne	.LBB3_9
	add	x0, sp, #4, lsl #12
	add	x1, sp, #484
	mov	w2, #1024
	add	x0, x0, #2624
	add	x25, sp, #484
	bl	memcpy
	mov	w8, #7580
	mov	w9, #7596
	mov	w11, #7612
	add	x8, x19, x8
	add	x9, x19, x9
	add	x0, sp, #4, lsl #12
	ldp	x10, x8, [x8]
	add	x1, sp, #4, lsl #12
	ldp	x12, x9, [x9]
	add	x0, x0, #576
	add	x1, x1, #2624
	mov	w2, #1024
	rev	w24, w24
	str	x8, [sp, #8488]
	mov	w8, #7628
	rev	w28, w23
	str	x10, [sp, #8480]
	add	x10, x19, x11
	add	x8, x19, x8
	str	x9, [sp, #8504]
	ldp	x11, x9, [x10]
	ldp	x8, x10, [x8]
	str	x12, [sp, #8496]
	mov	w12, #7644
	rev	w23, w26
	str	x9, [sp, #8520]
	add	x9, x19, x12
	mov	w12, #7676
	str	x10, [sp, #8536]
	mov	w10, #7660
	str	x11, [sp, #8512]
	ldp	x9, x11, [x9]
	str	x8, [sp, #8528]
	add	x8, x19, x10
	ldp	x8, x10, [x8]
	str	x9, [sp, #8544]
	add	x9, x19, x12
	mov	w12, #7692
	str	x11, [sp, #8552]
	str	x8, [sp, #8560]
	ldp	x8, x11, [x9]
	add	x9, x19, x12
	str	x10, [sp, #8568]
	mov	w12, #7708
	str	x8, [sp, #8576]
	ldp	x8, x10, [x9]
	add	x9, x19, x12
	mov	w12, #7724
	str	x11, [sp, #8584]
	ldp	x9, x11, [x9]
	str	x8, [sp, #8592]
	add	x8, x19, x12
	add	x19, sp, #4, lsl #12
	str	x10, [sp, #8600]
	ldp	x8, x10, [x8]
	str	x11, [sp, #8616]
	add	x19, x19, #576
	str	x9, [sp, #8608]
	str	x10, [sp, #8632]
	str	x8, [sp, #8624]
	bl	memcpy
	add	x0, sp, #3, lsl #12
	add	x1, sp, #4, lsl #12
	mov	w2, #1024
	add	x0, x0, #3648
	add	x1, x1, #576
	bl	memcpy
	add	x0, sp, #3, lsl #12
	add	x1, sp, #3, lsl #12
	mov	w2, #1024
	add	x0, x0, #2624
	add	x1, x1, #3648
	bl	memcpy
	add	x0, sp, #4, lsl #12
	add	x1, sp, #3, lsl #12
	mov	w2, #1024
	add	x0, x0, #1600
	add	x1, x1, #2624
	bl	memcpy
	ldr	x8, [sp, #20048]
	ldr	x9, [sp, #20056]
	add	x1, sp, #2, lsl #12
	add	x0, sp, #484
	add	x1, x1, #448
	mov	w2, #4224
	str	x8, [x22, #4640]
	mov	w26, #4640
	str	x9, [x22, #4648]
	mov	w22, #4224
	bl	memcpy
	mov	w8, #4656
	add	x1, sp, #3, lsl #12
	mov	w2, #1024
	add	x0, x25, x8
	add	x1, x1, #1600
	str	x0, [sp, #408]
	bl	memcpy
	mov	w8, #5684
	add	x1, sp, #3, lsl #12
	mov	w2, #1024
	add	x0, x25, x8
	add	x1, x1, #576
	str	w28, [sp, #6164]
	bl	memcpy
	mov	w8, #6712
	add	x1, sp, #4, lsl #12
	mov	w2, #1024
	add	x0, x25, x8
	add	x1, x1, #1600
	str	w24, [sp, #7192]
	bl	memcpy
	add	x1, sp, #2, lsl #12
	add	x0, x25, x22
	mov	w2, #416
	add	x1, x1, #32
	str	w23, [sp, #8220]
	str	x0, [sp, #392]
	bl	memcpy
	add	x0, sp, #4, lsl #12
	mov	w1, wzr
	mov	w2, #344
	add	x0, x0, #2624
	bl	memset
	add	x0, sp, #4, lsl #12
	add	x1, x25, x26
	mov	w2, #16
	add	x0, x0, #2624
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	add	x0, sp, #4, lsl #12
	add	x1, sp, #448
	mov	w2, #16
	add	x0, x0, #2624
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	add	x0, sp, #4, lsl #12
	add	x1, x20, #16
	mov	w2, #16
	add	x0, x0, #2624
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	add	x0, sp, #4, lsl #12
	mov	x1, x21
	mov	w2, #32
	add	x0, x0, #2624
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	add	x0, sp, #2, lsl #12
	add	x1, sp, #4, lsl #12
	mov	w2, #344
	add	x0, x0, #448
	add	x1, x1, #2624
	bl	memcpy
	add	x0, sp, #2, lsl #12
	add	x1, sp, #3, lsl #12
	mov	w2, #4
	add	x0, x0, #448
	add	x1, x1, #3648
	str	wzr, [sp, #15936]
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	add	x0, sp, #4, lsl #12
	add	x1, sp, #2, lsl #12
	add	x0, x0, #1600
	add	x1, x1, #448
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher8finalize
	ldr	x8, [sp, #17984]
	ldr	x9, [sp, #17992]
	add	x0, sp, #2, lsl #12
	ldr	x10, [sp, #18008]
	add	x1, sp, #4, lsl #12
	add	x0, x0, #448
	str	x8, [sp, #16960]
	ldr	x8, [sp, #18000]
	add	x1, x1, #2624
	mov	w2, #344
	str	x9, [sp, #16968]
	str	x8, [sp, #16976]
	str	x10, [sp, #16984]
	bl	memcpy
	add	x0, sp, #2, lsl #12
	add	x1, sp, #3, lsl #12
	mov	w8, #16777216
	add	x0, x0, #448
	add	x1, x1, #3648
	mov	w2, #4
	str	w8, [sp, #15936]
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	add	x0, sp, #4, lsl #12
	add	x1, sp, #2, lsl #12
	add	x0, x0, #1600
	add	x1, x1, #448
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher8finalize
	ldr	x9, [sp, #17984]
	ldr	x10, [sp, #17992]
	mov	x8, xzr
	ldr	x11, [sp, #18008]
	str	x9, [sp, #16992]
	ldr	x9, [sp, #18000]
	str	x10, [sp, #17000]
	mov	w10, #6
	str	x9, [sp, #17008]
	add	x9, sp, #2, lsl #12
	add	x9, x9, #448
	str	x11, [sp, #17016]
.LBB3_11:
	lsr	x13, x8, #3
	add	x14, x8, #2
	and	x18, x8, #0x6
	lsr	x16, x14, #3
	eor	x11, x18, #0x7
	eor	w18, w18, #0x6
	ldrb	w13, [x19, x13]
	and	w14, w14, #0x6
	add	x0, x8, #3
	ldrb	w16, [x19, x16]
	add	x15, x8, #4
	eor	w14, w14, #0x7
	lsr	w18, w13, w18
	lsr	x1, x0, #3
	lsr	x17, x15, #3
	lsr	w13, w13, w11
	lsr	w14, w16, w14
	bic	w16, w10, w0
	ldrb	w0, [x19, x1]
	and	w18, w18, #0x1
	ldrb	w17, [x19, x17]
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
	ldrb	w17, [x19, x17]
	ldrb	w15, [x19, x0]
	add	x0, x8, #7
	eor	w12, w12, #0x7
	lsr	x1, x0, #3
	orr	w13, w14, w13, lsl #2
	lsr	w14, w17, w16
	lsr	w12, w15, w12
	add	x18, x8, #8
	ldrb	w17, [x19, x1]
	lsr	x15, x18, #3
	add	x16, x8, #9
	bfxil	w13, w14, #0, #1
	ubfiz	w12, w12, #2, #1
	bic	w14, w10, w0
	lsr	x18, x16, #3
	lsr	w14, w17, w14
	mvn	w16, w16
	orr	w12, w12, w13, lsl #3
	ldrb	w13, [x19, x15]
	add	x8, x8, #10
	ubfiz	w14, w14, #1, #1
	ldrb	w15, [x19, x18]
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
	b.ne	.LBB3_11
	add	x23, sp, #3, lsl #12
	add	x1, sp, #2, lsl #12
	mov	w2, #192
	add	x23, x23, #3648
	add	x1, x1, #448
	add	x20, sp, #2, lsl #12
	ldrb	w8, [x23, #1055]
	ldrb	w9, [x23, #1054]
	ldrb	w10, [x23, #1056]
	ldrb	w19, [x23, #1057]
	add	x20, x20, #448
	lsl	w8, w8, #8
	and	x21, x19, #0xff
	orr	w8, w8, w9, lsl #16
	orr	w8, w8, w10
	bfi	x21, x8, #8, #18
	add	x8, sp, #4, lsl #12
	add	x8, x8, #1600
	add	x24, x8, #8
	str	x21, [sp, #17984]
	mov	x0, x24
	bl	memcpy
	rev	x8, x21
	add	x9, sp, #4, lsl #12
	lsl	w25, w19, #24
	lsl	x8, x8, #8
	add	x9, x9, #2624
	mov	x19, xzr
	add	x26, x20, #200
	add	x22, x9, #200
	add	x9, sp, #484
	mov	x20, x8
	mov	w8, #176
	mov	w10, #50331648
	mov	w28, #136
	str	x21, [sp, #400]
	stp	x24, x20, [sp, #416]
.LBB3_13:
	ldr	x11, [x24, x19, lsl #3]
	madd	x21, x19, x8, x9
	add	x0, sp, #2, lsl #12
	add	x0, x0, #448
	mov	w1, wzr
	mov	w2, #344
	add	w8, w11, w19, lsl #10
	str	xzr, [sp, #16960]
	str	x20, [sp, #16968]
	rev	w8, w8
	str	x11, [sp, #440]
	str	w10, [x23, #1040]
	str	w25, [x23, #1044]
	str	wzr, [x23, #1048]
	str	w8, [x23, #1052]
	bl	memset
	add	x0, sp, #2, lsl #12
	add	x1, sp, #448
	mov	w2, #16
	add	x0, x0, #448
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	add	x0, sp, #2, lsl #12
	add	x1, sp, #4, lsl #12
	mov	w2, #32
	add	x0, x0, #448
	add	x1, x1, #576
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	add	x0, sp, #4, lsl #12
	add	x1, sp, #2, lsl #12
	mov	w2, #344
	add	x0, x0, #2624
	add	x1, x1, #448
	bl	memcpy
	add	x0, sp, #4, lsl #12
	add	x1, x21, #160
	mov	w2, #16
	add	x0, x0, #2624
	str	x21, [sp, #432]
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	add	x0, sp, #3, lsl #12
	add	x1, sp, #4, lsl #12
	add	x0, x0, #576
	add	x1, x1, #2624
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher8finalize
	mov	x21, xzr
.LBB3_14:
	ldp	x11, x12, [sp, #432]
	mov	w8, #1
	ldr	x10, [sp, #12872]
	lsl	x8, x8, x21
	ldr	x9, [sp, #12864]
	add	x0, sp, #2, lsl #12
	mov	w1, wzr
	mov	w2, #344
	add	x11, x11, x21, lsl #4
	str	x10, [sp, #13896]
	add	x10, sp, #3, lsl #12
	tst	x8, x12
	add	x10, x10, #1600
	str	x9, [sp, #13888]
	csel	x8, x10, x11, eq
	csel	x10, x11, x10, eq
	add	x11, sp, #3, lsl #12
	ldp	x9, x8, [x8]
	add	x11, x11, #2624
	add	x0, x0, #448
	str	xzr, [sp, #15936]
	str	x20, [sp, #15944]
	str	x9, [sp, #14912]
	ldp	x9, x10, [x10]
	str	x8, [sp, #14920]
	mov	w8, #9
	sub	x8, x8, x21
	add	x21, x21, #1
	str	w25, [sp, #15956]
	stp	x9, x10, [x11, #16]
	lsr	x9, x12, x21
	lsl	w8, w19, w8
	mov	w10, #50331648
	add	w8, w8, w9
	str	w10, [sp, #15952]
	rev	w10, w21
	rev	w8, w8
	str	w10, [sp, #15960]
	str	w8, [sp, #15964]
	bl	memset
	ldr	x8, [sp, #8976]
	ldp	x9, x10, [sp, #448]
	add	x0, x8, #16
	cmp	x0, #136
	stp	x9, x10, [x26]
	str	x0, [sp, #8976]
	b.ne	.LBB3_16
	ldr	x9, [sp, #8840]
	ldr	x14, [sp, #8640]
	ldr	x10, [sp, #8848]
	ldr	x15, [sp, #8648]
	ldr	x8, [sp, #8856]
	ldr	x16, [sp, #8864]
	eor	x9, x14, x9
	ldr	x14, [sp, #8664]
	ldr	x12, [sp, #8872]
	eor	x10, x15, x10
	str	x9, [sp, #8640]
	ldr	x9, [sp, #8656]
	str	x10, [sp, #8648]
	ldr	x10, [sp, #8672]
	ldr	x13, [sp, #8880]
	eor	x8, x9, x8
	eor	x9, x14, x16
	ldr	x11, [sp, #8888]
	str	x8, [sp, #8656]
	ldr	x8, [sp, #8680]
	ldr	x15, [sp, #8896]
	str	x9, [sp, #8664]
	eor	x9, x10, x12
	ldr	x10, [sp, #8688]
	eor	x8, x8, x13
	ldr	x18, [sp, #8904]
	ldr	x12, [sp, #8696]
	ldr	x13, [sp, #8704]
	ldr	x14, [sp, #8912]
	ldr	x0, [sp, #8712]
	str	x8, [sp, #8680]
	eor	x8, x10, x11
	ldr	x16, [sp, #8920]
	eor	x10, x13, x18
	eor	x11, x0, x14
	add	x0, sp, #2, lsl #12
	add	x0, x0, #448
	str	x9, [sp, #8672]
	eor	x9, x12, x15
	ldr	x13, [sp, #8928]
	str	x8, [sp, #8688]
	ldr	x8, [sp, #8728]
	ldr	x12, [sp, #8720]
	ldr	x14, [sp, #8936]
	str	x9, [sp, #8696]
	eor	x8, x8, x13
	ldr	x9, [sp, #8736]
	str	x10, [sp, #8704]
	eor	x12, x12, x16
	ldr	x10, [sp, #8944]
	str	x11, [sp, #8712]
	eor	x9, x9, x14
	ldr	x11, [sp, #8744]
	ldr	x13, [sp, #8952]
	str	x8, [sp, #8728]
	ldr	x8, [sp, #8752]
	ldr	x17, [sp, #8768]
	eor	x10, x11, x10
	str	x12, [sp, #8720]
	ldr	x11, [sp, #8960]
	eor	x8, x8, x13
	str	x9, [sp, #8736]
	ldr	x9, [sp, #8760]
	ldr	x12, [sp, #8968]
	str	x8, [sp, #8752]
	eor	x9, x9, x11
	str	x10, [sp, #8744]
	eor	x8, x17, x12
	str	x9, [sp, #8760]
	str	x8, [sp, #8768]
	bl	_RNvCsndc0WgnAaH_9keccak2568keccak_f
	mov	x0, xzr
	str	xzr, [sp, #8976]
.LBB3_16:
	add	x23, sp, #3, lsl #12
	mov	w20, #32
	add	x23, x23, #3648
	b	.LBB3_18
.LBB3_17:
	sub	x20, x20, x24
	add	x23, x23, x24
	cbz	x20, .LBB3_22
.LBB3_18:
	sub	x8, x28, x0
	cmp	x20, x8
	csel	x24, x20, x8, lo
	add	x1, x24, x0
	cmp	x1, x0
	b.lo	.LBB3_79
	cmp	x1, #137
	b.hs	.LBB3_79
	add	x0, x26, x0
	mov	x1, x23
	mov	x2, x24
	bl	memcpy
	ldr	x8, [sp, #8976]
	add	x0, x8, x24
	cmp	x0, #136
	str	x0, [sp, #8976]
	b.ne	.LBB3_17
	ldr	x9, [sp, #8840]
	ldr	x14, [sp, #8640]
	ldr	x10, [sp, #8848]
	ldr	x15, [sp, #8648]
	ldr	x8, [sp, #8856]
	ldr	x16, [sp, #8864]
	eor	x9, x14, x9
	ldr	x14, [sp, #8664]
	ldr	x12, [sp, #8872]
	eor	x10, x15, x10
	str	x9, [sp, #8640]
	ldr	x9, [sp, #8656]
	str	x10, [sp, #8648]
	ldr	x10, [sp, #8672]
	ldr	x13, [sp, #8880]
	eor	x8, x9, x8
	eor	x9, x14, x16
	ldr	x11, [sp, #8888]
	str	x8, [sp, #8656]
	ldr	x8, [sp, #8680]
	ldr	x15, [sp, #8896]
	str	x9, [sp, #8664]
	eor	x9, x10, x12
	ldr	x10, [sp, #8688]
	eor	x8, x8, x13
	ldr	x18, [sp, #8904]
	ldr	x12, [sp, #8696]
	ldr	x13, [sp, #8704]
	ldr	x14, [sp, #8912]
	ldr	x0, [sp, #8712]
	str	x8, [sp, #8680]
	eor	x8, x10, x11
	ldr	x16, [sp, #8920]
	eor	x10, x13, x18
	eor	x11, x0, x14
	add	x0, sp, #2, lsl #12
	add	x0, x0, #448
	str	x9, [sp, #8672]
	eor	x9, x12, x15
	ldr	x13, [sp, #8928]
	str	x8, [sp, #8688]
	ldr	x8, [sp, #8728]
	ldr	x12, [sp, #8720]
	ldr	x14, [sp, #8936]
	str	x9, [sp, #8696]
	eor	x8, x8, x13
	ldr	x9, [sp, #8736]
	str	x10, [sp, #8704]
	eor	x12, x12, x16
	ldr	x10, [sp, #8944]
	str	x11, [sp, #8712]
	eor	x9, x9, x14
	ldr	x11, [sp, #8744]
	ldr	x13, [sp, #8952]
	str	x8, [sp, #8728]
	ldr	x8, [sp, #8752]
	ldr	x17, [sp, #8768]
	eor	x10, x11, x10
	str	x12, [sp, #8720]
	ldr	x11, [sp, #8960]
	eor	x8, x8, x13
	str	x9, [sp, #8736]
	ldr	x9, [sp, #8760]
	ldr	x12, [sp, #8968]
	str	x8, [sp, #8752]
	eor	x9, x9, x11
	str	x10, [sp, #8744]
	eor	x8, x17, x12
	str	x9, [sp, #8760]
	str	x8, [sp, #8768]
	bl	_RNvCsndc0WgnAaH_9keccak2568keccak_f
	mov	x0, xzr
	str	xzr, [sp, #8976]
	b	.LBB3_17
.LBB3_22:
	add	x0, sp, #4, lsl #12
	add	x1, sp, #2, lsl #12
	mov	w2, #344
	add	x0, x0, #2624
	add	x1, x1, #448
	mov	x27, x19
	mov	w19, w25
	bl	memcpy
	ldr	x25, [sp, #19344]
	add	x23, sp, #3, lsl #12
	mov	w20, #32
	add	x23, x23, #2624
	b	.LBB3_24
.LBB3_23:
	sub	x20, x20, x24
	add	x23, x23, x24
	cbz	x20, .LBB3_28
.LBB3_24:
	sub	x8, x28, x25
	cmp	x20, x8
	csel	x24, x20, x8, lo
	add	x1, x24, x25
	cmp	x1, x25
	b.lo	.LBB3_80
	cmp	x1, #137
	b.hs	.LBB3_80
	add	x0, x22, x25
	mov	x1, x23
	mov	x2, x24
	bl	memcpy
	ldr	x8, [sp, #19344]
	add	x25, x8, x24
	cmp	x25, #136
	str	x25, [sp, #19344]
	b.ne	.LBB3_23
	ldr	x9, [sp, #19208]
	ldr	x14, [sp, #19008]
	ldr	x10, [sp, #19216]
	ldr	x15, [sp, #19016]
	ldr	x8, [sp, #19224]
	ldr	x16, [sp, #19232]
	eor	x9, x14, x9
	ldr	x14, [sp, #19032]
	ldr	x12, [sp, #19240]
	eor	x10, x15, x10
	str	x9, [sp, #19008]
	ldr	x9, [sp, #19024]
	str	x10, [sp, #19016]
	ldr	x10, [sp, #19040]
	ldr	x13, [sp, #19248]
	eor	x8, x9, x8
	eor	x9, x14, x16
	ldr	x11, [sp, #19256]
	str	x8, [sp, #19024]
	ldr	x8, [sp, #19048]
	ldr	x15, [sp, #19264]
	str	x9, [sp, #19032]
	eor	x9, x10, x12
	ldr	x10, [sp, #19056]
	eor	x8, x8, x13
	ldr	x18, [sp, #19272]
	ldr	x12, [sp, #19064]
	ldr	x13, [sp, #19072]
	ldr	x14, [sp, #19280]
	ldr	x0, [sp, #19080]
	str	x8, [sp, #19048]
	eor	x8, x10, x11
	ldr	x16, [sp, #19288]
	eor	x10, x13, x18
	eor	x11, x0, x14
	add	x0, sp, #4, lsl #12
	add	x0, x0, #2624
	str	x9, [sp, #19040]
	eor	x9, x12, x15
	ldr	x13, [sp, #19296]
	str	x8, [sp, #19056]
	ldr	x8, [sp, #19096]
	ldr	x12, [sp, #19088]
	ldr	x14, [sp, #19304]
	str	x9, [sp, #19064]
	eor	x8, x8, x13
	ldr	x9, [sp, #19104]
	str	x10, [sp, #19072]
	eor	x12, x12, x16
	ldr	x10, [sp, #19312]
	str	x11, [sp, #19080]
	eor	x9, x9, x14
	ldr	x11, [sp, #19112]
	ldr	x13, [sp, #19320]
	str	x8, [sp, #19096]
	ldr	x8, [sp, #19120]
	ldr	x17, [sp, #19136]
	eor	x10, x11, x10
	str	x12, [sp, #19088]
	ldr	x11, [sp, #19328]
	eor	x8, x8, x13
	str	x9, [sp, #19104]
	ldr	x9, [sp, #19128]
	ldr	x12, [sp, #19336]
	str	x8, [sp, #19120]
	eor	x9, x9, x11
	str	x10, [sp, #19112]
	eor	x8, x17, x12
	str	x9, [sp, #19128]
	str	x8, [sp, #19136]
	bl	_RNvCsndc0WgnAaH_9keccak2568keccak_f
	mov	x25, xzr
	str	xzr, [sp, #19344]
	b	.LBB3_23
.LBB3_28:
	add	x0, sp, #2, lsl #12
	add	x1, sp, #4, lsl #12
	mov	w2, #200
	add	x0, x0, #448
	add	x1, x1, #2624
	bl	memcpy
	cmp	x25, #137
	b.hs	.LBB3_81
	add	x0, sp, #4, lsl #12
	mov	x1, x22
	mov	x2, x25
	add	x0, x0, #576
	str	xzr, [sp, #17088]
	str	xzr, [sp, #17080]
	str	xzr, [sp, #17072]
	str	xzr, [sp, #17064]
	str	xzr, [sp, #17056]
	str	xzr, [sp, #17048]
	str	xzr, [sp, #17040]
	str	xzr, [sp, #17032]
	str	xzr, [sp, #17024]
	str	xzr, [sp, #17016]
	str	xzr, [sp, #17008]
	str	xzr, [sp, #17000]
	str	xzr, [sp, #16992]
	str	xzr, [sp, #16984]
	str	xzr, [sp, #16976]
	str	xzr, [sp, #16968]
	str	xzr, [sp, #16960]
	bl	memcpy
	add	x9, sp, #4, lsl #12
	add	x23, sp, #3, lsl #12
	ldr	x0, [sp, #8648]
	add	x9, x9, #576
	add	x23, x23, #3648
	ldrb	w8, [x9, x25]
	eor	w8, w8, #0x1
	strb	w8, [x9, x25]
	ldr	x8, [sp, #8640]
	ldr	x10, [sp, #16960]
	ldr	x11, [sp, #16968]
	ldr	x12, [sp, #16976]
	ldrb	w9, [x23, #1159]
	ldr	x13, [sp, #16984]
	eor	x8, x8, x10
	ldr	x10, [sp, #8656]
	eor	x11, x0, x11
	ldr	x0, [sp, #8664]
	ldr	x14, [sp, #16992]
	ldr	x15, [sp, #17000]
	str	x8, [sp, #8640]
	eor	x8, x10, x12
	ldr	x10, [sp, #8672]
	ldr	x12, [sp, #8680]
	eor	w9, w9, #0x80
	str	x11, [sp, #8648]
	eor	x11, x0, x13
	ldr	x16, [sp, #17008]
	ldr	x17, [sp, #17016]
	strb	w9, [x23, #1159]
	ldr	x9, [sp, #17024]
	ldr	x13, [sp, #8704]
	str	x8, [sp, #8656]
	eor	x8, x10, x14
	ldr	x10, [sp, #8688]
	str	x11, [sp, #8664]
	eor	x11, x12, x15
	ldr	x12, [sp, #8696]
	ldr	x14, [sp, #17048]
	str	x11, [sp, #8680]
	ldr	x11, [sp, #8728]
	str	x8, [sp, #8672]
	eor	x8, x10, x16
	eor	x12, x12, x17
	eor	x9, x13, x9
	ldr	x18, [sp, #17032]
	ldr	x1, [sp, #17040]
	ldr	x10, [sp, #8712]
	ldr	x13, [sp, #8720]
	str	x8, [sp, #8688]
	ldr	x8, [sp, #17056]
	str	x12, [sp, #8696]
	ldr	x12, [sp, #8736]
	eor	x11, x11, x14
	ldr	x14, [sp, #17064]
	str	x9, [sp, #8704]
	ldr	x9, [sp, #8744]
	eor	x10, x10, x18
	eor	x13, x13, x1
	eor	x8, x12, x8
	str	x10, [sp, #8712]
	ldr	x10, [sp, #17072]
	eor	x9, x9, x14
	str	x13, [sp, #8720]
	ldr	x12, [sp, #8752]
	ldr	x13, [sp, #17080]
	str	x11, [sp, #8728]
	ldr	x11, [sp, #8760]
	str	x8, [sp, #8736]
	ldr	x8, [sp, #17088]
	add	x0, sp, #2, lsl #12
	str	x9, [sp, #8744]
	ldr	x9, [sp, #8768]
	eor	x10, x12, x10
	eor	x11, x11, x13
	add	x0, x0, #448
	str	x10, [sp, #8752]
	eor	x8, x9, x8
	str	x11, [sp, #8760]
	str	x8, [sp, #8768]
	bl	_RNvCsndc0WgnAaH_9keccak2568keccak_f
	ldr	x8, [sp, #8648]
	ldr	x9, [sp, #8640]
	mov	w25, w19
	mov	x19, x27
	add	x27, sp, #4, lsl #12
	ldr	x20, [sp, #424]
	cmp	x21, #10
	add	x27, x27, #2624
	str	x8, [sp, #16968]
	str	x9, [sp, #16960]
	str	x9, [sp, #12864]
	str	x8, [sp, #12872]
	b.ne	.LBB3_14
	add	x8, sp, #4, lsl #12
	ldr	x9, [sp, #12864]
	ldr	x10, [sp, #12872]
	add	x8, x8, #3680
	ldr	x24, [sp, #416]
	add	x8, x8, x19, lsl #4
	add	x19, x19, #1
	cmp	x19, #24
	stp	x9, x10, [x8]
	mov	w8, #176
	add	x9, sp, #484
	mov	w10, #50331648
	b.ne	.LBB3_13
	add	x0, sp, #2, lsl #12
	mov	w8, #67108864
	mov	w1, wzr
	add	x0, x0, #448
	mov	w2, #344
	str	xzr, [sp, #16960]
	str	x20, [sp, #16968]
	str	w8, [x23, #1040]
	str	w25, [x23, #1044]
	str	xzr, [sp, #16984]
	bl	memset
	add	x0, sp, #2, lsl #12
	add	x1, sp, #448
	mov	w2, #16
	add	x0, x0, #448
	mov	w23, #16
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	add	x0, sp, #2, lsl #12
	add	x1, sp, #4, lsl #12
	mov	w2, #32
	add	x0, x0, #448
	add	x1, x1, #576
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	add	x0, sp, #4, lsl #12
	add	x1, sp, #2, lsl #12
	mov	w2, #344
	add	x0, x0, #2624
	add	x1, x1, #448
	add	x19, sp, #4, lsl #12
	add	x19, x19, #2624
	bl	memcpy
	add	x0, sp, #4, lsl #12
	add	x1, sp, #4, lsl #12
	mov	w2, #384
	add	x0, x0, #2624
	add	x1, x1, #3680
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	add	x0, sp, #2, lsl #12
	add	x1, sp, #4, lsl #12
	add	x20, sp, #2, lsl #12
	add	x0, x0, #448
	add	x1, x1, #2624
	add	x20, x20, #448
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher8finalize
	ldr	x8, [sp, #8640]
	ldr	x9, [sp, #8648]
	add	x22, sp, #3, lsl #12
	mov	x10, xzr
	add	x22, x22, #3648
	add	x25, x20, #200
	str	x8, [sp, #20032]
	add	x21, x19, #200
	orr	x24, x19, #0x1
	mov	w11, #4656
	adrp	x8, .Lanon.bee145f0cb2eac5728ff95be1b200579.2
	add	x8, x8, :lo12:.Lanon.bee145f0cb2eac5728ff95be1b200579.2
	mov	w12, #8
	mov	w13, #117440512
	mov	w19, #136
	str	x9, [sp, #20040]
	str	x24, [sp, #8]
.LBB3_32:
	cmp	x10, #1
	mov	x15, x10
	ldr	x14, [x8, x10, lsl #3]
	csel	x8, x12, x23, eq
	cmp	x10, #0
	ldr	x10, [sp, #400]
	csel	x8, xzr, x8, eq
	mov	x9, #-1
	add	x0, sp, #2, lsl #12
	lsl	x9, x9, x14
	lsr	x8, x10, x8
	rev	w12, w15
	add	x11, x11, #1028
	add	x0, x0, #448
	mov	w1, wzr
	lsr	x10, x8, x14
	bic	x8, x8, x9
	mov	w2, #344
	stp	x8, x14, [sp, #40]
	rev	w8, w8
	str	w8, [sp, #424]
	rev	x9, x10
	str	w8, [x22, #1044]
	ldr	x8, [sp, #408]
	str	wzr, [x22, #1028]
	ldr	w20, [x8, #1024]
	add	x8, x15, #1
	str	w13, [x22, #1040]
	str	w12, [sp, #432]
	str	w12, [x22, #1024]
	str	x9, [sp, #440]
	str	x9, [sp, #16968]
	stp	x11, x15, [sp, #24]
	str	x8, [sp, #16]
	str	xzr, [sp, #16984]
	bl	memset
	add	x0, sp, #2, lsl #12
	add	x1, sp, #448
	mov	w2, #16
	add	x0, x0, #448
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	add	x0, sp, #2, lsl #12
	add	x1, sp, #4, lsl #12
	mov	w2, #32
	add	x0, x0, #448
	add	x1, x1, #576
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	add	x0, sp, #4, lsl #12
	add	x1, sp, #2, lsl #12
	mov	w2, #344
	add	x0, x0, #2624
	add	x1, x1, #448
	bl	memcpy
	add	x0, sp, #4, lsl #12
	add	x1, sp, #4, lsl #12
	mov	w2, #16
	add	x0, x0, #2624
	add	x1, x1, #3648
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	add	x0, sp, #2, lsl #12
	add	x1, sp, #4, lsl #12
	mov	w2, #344
	add	x0, x0, #448
	add	x1, x1, #2624
	bl	memcpy
	add	x0, sp, #2, lsl #12
	add	x1, sp, #4, lsl #12
	rev	w8, w20
	add	x0, x0, #448
	add	x1, x1, #576
	mov	w2, #4
	str	w8, [x22, #1024]
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	add	x0, sp, #4, lsl #12
	add	x1, sp, #2, lsl #12
	add	x0, x0, #2624
	add	x1, x1, #448
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher8finalize
	ldr	x10, [sp, #19016]
	ldr	x9, [sp, #19008]
	mov	x8, xzr
	mov	x11, x24
	rev	x9, x9
	rev	x10, x10
.LBB3_33:
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
	b.ne	.LBB3_33
	add	x5, sp, #3, lsl #12
	ldrb	w8, [x27]
	add	x5, x5, #3648
	ldrb	w9, [x5, #3073]
	ldrb	w10, [x5, #3074]
	ldrb	w11, [x5, #3075]
	ldrb	w12, [x5, #3076]
	ldrb	w13, [x5, #3077]
	str	x8, [sp, #416]
	stp	x10, x9, [sp, #376]
	add	x8, x9, x8
	add	x9, x10, x11
	stp	x12, x11, [sp, #360]
	ldrb	w11, [x5, #3078]
	ldrb	w14, [x5, #3079]
	add	x10, x12, x13
	ldrb	w12, [x5, #3080]
	add	x8, x8, x9
	stp	x11, x13, [sp, #344]
	ldrb	w13, [x5, #3081]
	add	x9, x10, x11
	ldrb	w10, [x5, #3082]
	add	x8, x8, x9
	add	x9, x14, x12
	ldrb	w11, [x5, #3083]
	ldrb	w15, [x5, #3084]
	add	x9, x9, x13
	ldrb	w16, [x5, #3085]
	stp	x10, x13, [sp, #312]
	ldrb	w13, [x5, #3088]
	ldrb	w17, [x5, #3089]
	add	x9, x9, x10
	stp	x12, x14, [sp, #328]
	ldrb	w12, [x5, #3086]
	ldrb	w18, [x5, #3090]
	add	x8, x8, x9
	add	x9, x11, x15
	ldrb	w14, [x5, #3087]
	ldrb	w0, [x5, #3091]
	stp	x15, x11, [sp, #296]
	ldrb	w11, [x5, #3094]
	ldrb	w15, [x5, #3095]
	add	x9, x9, x16
	add	x10, x13, x17
	ldrb	w1, [x5, #3092]
	stp	x12, x16, [sp, #280]
	ldrb	w16, [x5, #3096]
	add	x9, x9, x12
	add	x10, x10, x18
	ldrb	w3, [x5, #3097]
	add	x9, x9, x14
	add	x10, x10, x0
	stp	x15, x11, [sp, #208]
	add	x11, x11, x15
	ldrb	w2, [x5, #3093]
	stp	x17, x13, [sp, #256]
	ldrb	w13, [x5, #3098]
	ldrb	w17, [x5, #3099]
	add	x8, x8, x9
	add	x9, x10, x1
	add	x10, x11, x16
	ldrb	w11, [x5, #3100]
	add	x9, x9, x2
	add	x10, x10, x3
	stp	x17, x13, [sp, #176]
	ldrb	w12, [x5, #3101]
	add	x10, x10, x13
	ldrb	w13, [x5, #3102]
	str	x14, [sp, #272]
	add	x8, x8, x9
	add	x9, x10, x17
	ldrb	w14, [x5, #3103]
	stp	x12, x11, [sp, #160]
	add	x9, x9, x11
	ldrb	w11, [x5, #3104]
	add	x10, x12, x13
	add	x9, x8, x9
	ldrb	w12, [x5, #3105]
	add	x8, x10, x14
	str	x11, [sp, #136]
	ldrb	w10, [x5, #3109]
	add	x8, x8, x11
	ldrb	w11, [x5, #3110]
	stp	x14, x13, [sp, #144]
	add	x8, x8, x12
	ldrb	w13, [x5, #3112]
	str	x10, [sp, #128]
	stp	x12, x11, [sp, #112]
	ldrb	w12, [x5, #3111]
	add	x10, x10, x11
	ldrb	w11, [x5, #3113]
	ldrb	w14, [x5, #3106]
	ldrb	w15, [x5, #3107]
	add	x10, x10, x12
	stp	x13, x12, [sp, #96]
	ldrb	w12, [x5, #3114]
	add	x10, x10, x13
	add	x8, x8, x14
	ldrb	w23, [x5, #3108]
	add	x10, x10, x11
	stp	x12, x11, [sp, #64]
	ldrb	w6, [x5, #3119]
	add	x10, x10, x12
	ldrb	w12, [x5, #3118]
	add	x8, x8, x15
	ldrb	w7, [x5, #3115]
	ldrb	w20, [x5, #3120]
	add	x11, x8, x23
	ldrb	w24, [x5, #3116]
	ldrb	w22, [x5, #3121]
	add	x8, x12, x6
	add	x10, x10, x7
	str	x12, [sp, #56]
	add	x12, x8, x20
	ldrb	w8, [x5, #3117]
	ldrb	w26, [x5, #3122]
	stp	x2, x1, [sp, #224]
	add	x1, x9, x11
	add	x9, x10, x24
	add	x10, x12, x22
	add	x2, x9, x8
	add	x9, x10, x26
	ldrb	w10, [x5, #3123]
	ldrb	w11, [x5, #3124]
	ldrb	w28, [x5, #3128]
	ldrb	w30, [x5, #3129]
	add	x12, x9, x10
	ldrb	w13, [x5, #3125]
	ldrb	w9, [x5, #3130]
	stp	x15, x14, [sp, #80]
	add	x14, x12, x11
	ldrb	w12, [x5, #3131]
	add	x15, x28, x30
	add	x17, x14, x13
	ldrb	w14, [x5, #3132]
	add	x15, x15, x9
	stp	x0, x18, [sp, #240]
	ldrb	w18, [x5, #3126]
	stp	x3, x16, [sp, #192]
	add	x16, x15, x12
	ldrb	w15, [x5, #3133]
	add	x3, x16, x14
	ldrb	w0, [x5, #3127]
	ldrb	w16, [x5, #3134]
	add	x4, x17, x18
	add	x3, x3, x15
	ldrb	w17, [x5, #3135]
	add	x1, x1, x2
	add	x2, x4, x0
	add	x3, x3, x16
	add	x1, x1, x2
	add	x2, x3, x17
	add	x1, x1, x2
	cmp	x1, #128
	b.ne	.LBB3_83
	ldr	x2, [sp, #416]
	strb	w8, [x5, #45]
	mov	x1, xzr
	ldr	x8, [sp, #56]
	strb	w23, [x5, #36]
	strb	w2, [x5]
	ldp	x2, x3, [sp, #376]
	strb	w7, [x5, #43]
	strb	w24, [x5, #44]
	strb	w2, [x5, #2]
	ldp	x2, x4, [sp, #360]
	strb	w3, [x5, #1]
	strb	w8, [x5, #46]
	strb	w2, [x5, #4]
	ldr	x2, [sp, #352]
	strb	w4, [x5, #3]
	strb	w2, [x5, #5]
	ldr	x2, [sp, #344]
	strb	w6, [x5, #47]
	strb	w2, [x5, #6]
	ldr	x2, [sp, #336]
	strb	w20, [x5, #48]
	strb	w2, [x5, #7]
	ldr	x2, [sp, #328]
	strb	w22, [x5, #49]
	strb	w2, [x5, #8]
	ldr	x2, [sp, #320]
	strb	w26, [x5, #50]
	strb	w2, [x5, #9]
	ldr	x2, [sp, #312]
	strb	w10, [x5, #51]
	strb	w2, [x5, #10]
	ldr	x2, [sp, #304]
	strb	w11, [x5, #52]
	strb	w2, [x5, #11]
	ldr	x2, [sp, #296]
	strb	w13, [x5, #53]
	strb	w2, [x5, #12]
	ldr	x2, [sp, #288]
	strb	w18, [x5, #54]
	strb	w2, [x5, #13]
	ldr	x2, [sp, #280]
	strb	w0, [x5, #55]
	strb	w2, [x5, #14]
	ldr	x2, [sp, #272]
	strb	w28, [x5, #56]
	strb	w2, [x5, #15]
	ldr	x2, [sp, #264]
	strb	w30, [x5, #57]
	strb	w2, [x5, #16]
	ldr	x2, [sp, #256]
	strb	w9, [x5, #58]
	strb	w2, [x5, #17]
	ldr	x2, [sp, #248]
	strb	w12, [x5, #59]
	strb	w2, [x5, #18]
	ldr	x2, [sp, #240]
	strb	w14, [x5, #60]
	strb	w2, [x5, #19]
	ldr	x2, [sp, #232]
	strb	w15, [x5, #61]
	strb	w2, [x5, #20]
	ldr	x2, [sp, #224]
	strb	w16, [x5, #62]
	strb	w2, [x5, #21]
	ldr	x2, [sp, #216]
	strb	w17, [x5, #63]
	strb	w2, [x5, #22]
	ldr	x2, [sp, #208]
	strb	w2, [x5, #23]
	ldr	x2, [sp, #200]
	strb	w2, [x5, #24]
	ldr	x2, [sp, #192]
	strb	w2, [x5, #25]
	ldr	x2, [sp, #184]
	strb	w2, [x5, #26]
	ldr	x2, [sp, #176]
	strb	w2, [x5, #27]
	ldr	x2, [sp, #168]
	strb	w2, [x5, #28]
	ldr	x2, [sp, #160]
	strb	w2, [x5, #29]
	ldr	x2, [sp, #152]
	strb	w2, [x5, #30]
	ldr	x2, [sp, #144]
	strb	w2, [x5, #31]
	ldr	x2, [sp, #136]
	strb	w2, [x5, #32]
	ldr	x2, [sp, #112]
	strb	w2, [x5, #33]
	ldr	x2, [sp, #88]
	strb	w2, [x5, #34]
	ldr	x2, [sp, #80]
	strb	w2, [x5, #35]
	ldr	x2, [sp, #128]
	strb	w2, [x5, #37]
	ldr	x2, [sp, #120]
	strb	w2, [x5, #38]
	ldr	x2, [sp, #104]
	strb	w2, [x5, #39]
	ldr	x2, [sp, #96]
	strb	w2, [x5, #40]
	ldr	x2, [sp, #72]
	strb	w2, [x5, #41]
	ldr	x2, [sp, #64]
	strb	w2, [x5, #42]
	b	.LBB3_37
.LBB3_36:
	add	x8, sp, #4, lsl #12
	ldr	x1, [sp, #416]
	ldr	x9, [sp, #8224]
	add	x8, x8, #4080
	ldr	x10, [sp, #8232]
	add	x8, x8, x1, lsl #4
	add	x1, x1, #1
	cmp	x1, #64
	stp	x9, x10, [x8]
	b.eq	.LBB3_55
.LBB3_37:
	ldr	x8, [sp, #408]
	add	x9, sp, #3, lsl #12
	str	x1, [sp, #416]
	add	x9, x9, #3648
	add	x8, x8, x1, lsl #4
	ldrb	w20, [x9, x1]
	ldp	x9, x8, [x8]
	cmp	x20, #2
	str	x9, [sp, #8224]
	str	x8, [sp, #8232]
	b.hi	.LBB3_36
	ldr	x8, [sp, #416]
	lsl	w26, w8, #24
.LBB3_39:
	ldr	x8, [sp, #8224]
	ldr	x9, [sp, #8232]
	add	x0, sp, #2, lsl #12
	add	x0, x0, #448
	mov	w1, wzr
	mov	w2, #344
	str	x8, [sp, #12864]
	ldr	w8, [sp, #432]
	str	x20, [sp, #12880]
	str	w8, [sp, #13888]
	ldr	x8, [sp, #440]
	str	x9, [sp, #12872]
	str	x8, [sp, #13896]
	ldr	w8, [sp, #424]
	str	wzr, [sp, #13892]
	str	w8, [sp, #13908]
	rev	w8, w20
	str	wzr, [sp, #13904]
	str	w26, [sp, #13912]
	str	w8, [sp, #13916]
	bl	memset
	ldr	x8, [sp, #8976]
	ldp	x9, x10, [sp, #448]
	add	x0, x8, #16
	cmp	x0, #136
	stp	x9, x10, [x25]
	str	x0, [sp, #8976]
	b.ne	.LBB3_41
	ldr	x9, [sp, #8840]
	ldr	x14, [sp, #8640]
	ldr	x10, [sp, #8848]
	ldr	x15, [sp, #8648]
	ldr	x8, [sp, #8856]
	ldr	x16, [sp, #8864]
	eor	x9, x14, x9
	ldr	x14, [sp, #8664]
	ldr	x12, [sp, #8872]
	eor	x10, x15, x10
	str	x9, [sp, #8640]
	ldr	x9, [sp, #8656]
	str	x10, [sp, #8648]
	ldr	x10, [sp, #8672]
	ldr	x13, [sp, #8880]
	eor	x8, x9, x8
	eor	x9, x14, x16
	ldr	x11, [sp, #8888]
	str	x8, [sp, #8656]
	ldr	x8, [sp, #8680]
	ldr	x15, [sp, #8896]
	str	x9, [sp, #8664]
	eor	x9, x10, x12
	ldr	x10, [sp, #8688]
	eor	x8, x8, x13
	ldr	x18, [sp, #8904]
	ldr	x12, [sp, #8696]
	ldr	x13, [sp, #8704]
	ldr	x14, [sp, #8912]
	ldr	x0, [sp, #8712]
	str	x8, [sp, #8680]
	eor	x8, x10, x11
	ldr	x16, [sp, #8920]
	eor	x10, x13, x18
	eor	x11, x0, x14
	add	x0, sp, #2, lsl #12
	add	x0, x0, #448
	str	x9, [sp, #8672]
	eor	x9, x12, x15
	ldr	x13, [sp, #8928]
	str	x8, [sp, #8688]
	ldr	x8, [sp, #8728]
	ldr	x12, [sp, #8720]
	ldr	x14, [sp, #8936]
	str	x9, [sp, #8696]
	eor	x8, x8, x13
	ldr	x9, [sp, #8736]
	str	x10, [sp, #8704]
	eor	x12, x12, x16
	ldr	x10, [sp, #8944]
	str	x11, [sp, #8712]
	eor	x9, x9, x14
	ldr	x11, [sp, #8744]
	ldr	x13, [sp, #8952]
	str	x8, [sp, #8728]
	ldr	x8, [sp, #8752]
	ldr	x17, [sp, #8768]
	eor	x10, x11, x10
	str	x12, [sp, #8720]
	ldr	x11, [sp, #8960]
	eor	x8, x8, x13
	str	x9, [sp, #8736]
	ldr	x9, [sp, #8760]
	ldr	x12, [sp, #8968]
	str	x8, [sp, #8752]
	eor	x9, x9, x11
	str	x10, [sp, #8744]
	eor	x8, x17, x12
	str	x9, [sp, #8760]
	str	x8, [sp, #8768]
	bl	_RNvCsndc0WgnAaH_9keccak2568keccak_f
	mov	x0, xzr
	str	xzr, [sp, #8976]
.LBB3_41:
	add	x22, sp, #3, lsl #12
	add	x20, x20, #1
	mov	w24, #32
	add	x22, x22, #1600
	b	.LBB3_43
.LBB3_42:
	sub	x24, x24, x23
	add	x22, x22, x23
	cbz	x24, .LBB3_47
.LBB3_43:
	sub	x8, x19, x0
	cmp	x24, x8
	csel	x23, x24, x8, lo
	add	x1, x23, x0
	cmp	x1, x0
	b.lo	.LBB3_79
	cmp	x1, #137
	b.hs	.LBB3_79
	add	x0, x25, x0
	mov	x1, x22
	mov	x2, x23
	bl	memcpy
	ldr	x8, [sp, #8976]
	add	x0, x8, x23
	cmp	x0, #136
	str	x0, [sp, #8976]
	b.ne	.LBB3_42
	ldr	x9, [sp, #8840]
	ldr	x14, [sp, #8640]
	ldr	x10, [sp, #8848]
	ldr	x15, [sp, #8648]
	ldr	x8, [sp, #8856]
	ldr	x16, [sp, #8864]
	eor	x9, x14, x9
	ldr	x14, [sp, #8664]
	ldr	x12, [sp, #8872]
	eor	x10, x15, x10
	str	x9, [sp, #8640]
	ldr	x9, [sp, #8656]
	str	x10, [sp, #8648]
	ldr	x10, [sp, #8672]
	ldr	x13, [sp, #8880]
	eor	x8, x9, x8
	eor	x9, x14, x16
	ldr	x11, [sp, #8888]
	str	x8, [sp, #8656]
	ldr	x8, [sp, #8680]
	ldr	x15, [sp, #8896]
	str	x9, [sp, #8664]
	eor	x9, x10, x12
	ldr	x10, [sp, #8688]
	eor	x8, x8, x13
	ldr	x18, [sp, #8904]
	ldr	x12, [sp, #8696]
	ldr	x13, [sp, #8704]
	ldr	x14, [sp, #8912]
	ldr	x0, [sp, #8712]
	str	x8, [sp, #8680]
	eor	x8, x10, x11
	ldr	x16, [sp, #8920]
	eor	x10, x13, x18
	eor	x11, x0, x14
	add	x0, sp, #2, lsl #12
	add	x0, x0, #448
	str	x9, [sp, #8672]
	eor	x9, x12, x15
	ldr	x13, [sp, #8928]
	str	x8, [sp, #8688]
	ldr	x8, [sp, #8728]
	ldr	x12, [sp, #8720]
	ldr	x14, [sp, #8936]
	str	x9, [sp, #8696]
	eor	x8, x8, x13
	ldr	x9, [sp, #8736]
	str	x10, [sp, #8704]
	eor	x12, x12, x16
	ldr	x10, [sp, #8944]
	str	x11, [sp, #8712]
	eor	x9, x9, x14
	ldr	x11, [sp, #8744]
	ldr	x13, [sp, #8952]
	str	x8, [sp, #8728]
	ldr	x8, [sp, #8752]
	ldr	x17, [sp, #8768]
	eor	x10, x11, x10
	str	x12, [sp, #8720]
	ldr	x11, [sp, #8960]
	eor	x8, x8, x13
	str	x9, [sp, #8736]
	ldr	x9, [sp, #8760]
	ldr	x12, [sp, #8968]
	str	x8, [sp, #8752]
	eor	x9, x9, x11
	str	x10, [sp, #8744]
	eor	x8, x17, x12
	str	x9, [sp, #8760]
	str	x8, [sp, #8768]
	bl	_RNvCsndc0WgnAaH_9keccak2568keccak_f
	mov	x0, xzr
	str	xzr, [sp, #8976]
	b	.LBB3_42
.LBB3_47:
	add	x0, sp, #4, lsl #12
	add	x1, sp, #2, lsl #12
	mov	w2, #344
	add	x0, x0, #2624
	add	x1, x1, #448
	bl	memcpy
	ldr	x24, [sp, #19344]
	add	x22, sp, #3, lsl #12
	mov	w28, #16
	add	x22, x22, #576
	b	.LBB3_49
.LBB3_48:
	sub	x28, x28, x23
	add	x22, x22, x23
	cbz	x28, .LBB3_53
.LBB3_49:
	sub	x8, x19, x24
	cmp	x28, x8
	csel	x23, x28, x8, lo
	add	x1, x23, x24
	cmp	x1, x24
	b.lo	.LBB3_82
	cmp	x1, #137
	b.hs	.LBB3_82
	add	x0, x21, x24
	mov	x1, x22
	mov	x2, x23
	bl	memcpy
	ldr	x8, [sp, #19344]
	add	x24, x8, x23
	cmp	x24, #136
	str	x24, [sp, #19344]
	b.ne	.LBB3_48
	ldr	x9, [sp, #19208]
	ldr	x14, [sp, #19008]
	ldr	x10, [sp, #19216]
	ldr	x15, [sp, #19016]
	ldr	x8, [sp, #19224]
	ldr	x16, [sp, #19232]
	eor	x9, x14, x9
	ldr	x14, [sp, #19032]
	ldr	x12, [sp, #19240]
	eor	x10, x15, x10
	str	x9, [sp, #19008]
	ldr	x9, [sp, #19024]
	str	x10, [sp, #19016]
	ldr	x10, [sp, #19040]
	ldr	x13, [sp, #19248]
	eor	x8, x9, x8
	eor	x9, x14, x16
	ldr	x11, [sp, #19256]
	str	x8, [sp, #19024]
	ldr	x8, [sp, #19048]
	ldr	x15, [sp, #19264]
	str	x9, [sp, #19032]
	eor	x9, x10, x12
	ldr	x10, [sp, #19056]
	eor	x8, x8, x13
	ldr	x18, [sp, #19272]
	ldr	x12, [sp, #19064]
	ldr	x13, [sp, #19072]
	ldr	x14, [sp, #19280]
	ldr	x0, [sp, #19080]
	str	x8, [sp, #19048]
	eor	x8, x10, x11
	ldr	x16, [sp, #19288]
	eor	x10, x13, x18
	eor	x11, x0, x14
	add	x0, sp, #4, lsl #12
	add	x0, x0, #2624
	str	x9, [sp, #19040]
	eor	x9, x12, x15
	ldr	x13, [sp, #19296]
	str	x8, [sp, #19056]
	ldr	x8, [sp, #19096]
	ldr	x12, [sp, #19088]
	ldr	x14, [sp, #19304]
	str	x9, [sp, #19064]
	eor	x8, x8, x13
	ldr	x9, [sp, #19104]
	str	x10, [sp, #19072]
	eor	x12, x12, x16
	ldr	x10, [sp, #19312]
	str	x11, [sp, #19080]
	eor	x9, x9, x14
	ldr	x11, [sp, #19112]
	ldr	x13, [sp, #19320]
	str	x8, [sp, #19096]
	ldr	x8, [sp, #19120]
	ldr	x17, [sp, #19136]
	eor	x10, x11, x10
	str	x12, [sp, #19088]
	ldr	x11, [sp, #19328]
	eor	x8, x8, x13
	str	x9, [sp, #19104]
	ldr	x9, [sp, #19128]
	ldr	x12, [sp, #19336]
	str	x8, [sp, #19120]
	eor	x9, x9, x11
	str	x10, [sp, #19112]
	eor	x8, x17, x12
	str	x9, [sp, #19128]
	str	x8, [sp, #19136]
	bl	_RNvCsndc0WgnAaH_9keccak2568keccak_f
	mov	x24, xzr
	str	xzr, [sp, #19344]
	b	.LBB3_48
.LBB3_53:
	add	x0, sp, #2, lsl #12
	add	x1, sp, #4, lsl #12
	mov	w2, #200
	add	x0, x0, #448
	add	x1, x1, #2624
	bl	memcpy
	cmp	x24, #137
	b.hs	.LBB3_85
	add	x0, sp, #4, lsl #12
	mov	x1, x21
	mov	x2, x24
	add	x0, x0, #576
	str	xzr, [sp, #17088]
	str	xzr, [sp, #17080]
	str	xzr, [sp, #17072]
	str	xzr, [sp, #17064]
	str	xzr, [sp, #17056]
	str	xzr, [sp, #17048]
	str	xzr, [sp, #17040]
	str	xzr, [sp, #17032]
	str	xzr, [sp, #17024]
	str	xzr, [sp, #17016]
	str	xzr, [sp, #17008]
	str	xzr, [sp, #17000]
	str	xzr, [sp, #16992]
	str	xzr, [sp, #16984]
	str	xzr, [sp, #16976]
	str	xzr, [sp, #16968]
	str	xzr, [sp, #16960]
	bl	memcpy
	add	x9, sp, #4, lsl #12
	add	x18, sp, #3, lsl #12
	ldr	x0, [sp, #8648]
	add	x9, x9, #576
	add	x18, x18, #3648
	ldrb	w8, [x9, x24]
	eor	w8, w8, #0x1
	strb	w8, [x9, x24]
	ldr	x8, [sp, #8640]
	ldr	x10, [sp, #16960]
	ldr	x11, [sp, #16968]
	ldr	x12, [sp, #16976]
	ldrb	w9, [x18, #1159]
	ldr	x13, [sp, #16984]
	eor	x8, x8, x10
	ldr	x10, [sp, #8656]
	eor	x11, x0, x11
	ldr	x0, [sp, #8664]
	ldr	x14, [sp, #16992]
	ldr	x15, [sp, #17000]
	str	x8, [sp, #8640]
	eor	x8, x10, x12
	ldr	x10, [sp, #8672]
	ldr	x12, [sp, #8680]
	eor	w9, w9, #0x80
	str	x11, [sp, #8648]
	eor	x11, x0, x13
	ldr	x16, [sp, #17008]
	ldr	x17, [sp, #17016]
	strb	w9, [x18, #1159]
	ldr	x9, [sp, #17024]
	ldr	x13, [sp, #8704]
	str	x8, [sp, #8656]
	eor	x8, x10, x14
	ldr	x10, [sp, #8688]
	str	x11, [sp, #8664]
	eor	x11, x12, x15
	ldr	x12, [sp, #8696]
	ldr	x14, [sp, #17048]
	str	x11, [sp, #8680]
	ldr	x11, [sp, #8728]
	str	x8, [sp, #8672]
	eor	x8, x10, x16
	eor	x12, x12, x17
	eor	x9, x13, x9
	ldr	x18, [sp, #17032]
	ldr	x1, [sp, #17040]
	ldr	x10, [sp, #8712]
	ldr	x13, [sp, #8720]
	str	x8, [sp, #8688]
	ldr	x8, [sp, #17056]
	str	x12, [sp, #8696]
	ldr	x12, [sp, #8736]
	eor	x11, x11, x14
	ldr	x14, [sp, #17064]
	str	x9, [sp, #8704]
	ldr	x9, [sp, #8744]
	eor	x10, x10, x18
	eor	x13, x13, x1
	eor	x8, x12, x8
	str	x10, [sp, #8712]
	ldr	x10, [sp, #17072]
	eor	x9, x9, x14
	str	x13, [sp, #8720]
	ldr	x12, [sp, #8752]
	ldr	x13, [sp, #17080]
	str	x11, [sp, #8728]
	ldr	x11, [sp, #8760]
	str	x8, [sp, #8736]
	ldr	x8, [sp, #17088]
	add	x0, sp, #2, lsl #12
	str	x9, [sp, #8744]
	ldr	x9, [sp, #8768]
	eor	x10, x12, x10
	eor	x11, x11, x13
	add	x0, x0, #448
	str	x10, [sp, #8752]
	eor	x8, x9, x8
	str	x11, [sp, #8760]
	str	x8, [sp, #8768]
	bl	_RNvCsndc0WgnAaH_9keccak2568keccak_f
	ldr	x8, [sp, #8648]
	ldr	x9, [sp, #8640]
	cmp	x20, #3
	str	x8, [sp, #16968]
	str	x9, [sp, #16960]
	str	x9, [sp, #8224]
	str	x8, [sp, #8232]
	b.ne	.LBB3_39
	b	.LBB3_36
.LBB3_55:
	add	x8, sp, #3, lsl #12
	ldr	w9, [sp, #432]
	add	x0, sp, #2, lsl #12
	add	x8, x8, #3648
	add	x0, x0, #448
	mov	w1, wzr
	str	w9, [x8, #1024]
	mov	w9, #16777216
	mov	w2, #344
	str	w9, [x8, #1040]
	ldr	w9, [sp, #424]
	str	wzr, [x8, #1028]
	str	w9, [x8, #1044]
	ldr	x8, [sp, #440]
	str	xzr, [sp, #16984]
	str	x8, [sp, #16968]
	bl	memset
	add	x0, sp, #2, lsl #12
	add	x1, sp, #448
	mov	w2, #16
	add	x0, x0, #448
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	add	x0, sp, #2, lsl #12
	add	x1, sp, #4, lsl #12
	mov	w2, #32
	add	x0, x0, #448
	add	x1, x1, #576
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	add	x0, sp, #4, lsl #12
	add	x1, sp, #2, lsl #12
	mov	w2, #344
	add	x0, x0, #2624
	add	x1, x1, #448
	bl	memcpy
	add	x0, sp, #4, lsl #12
	add	x1, sp, #4, lsl #12
	mov	w2, #1024
	add	x0, x0, #2624
	add	x1, x1, #4080
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	add	x0, sp, #3, lsl #12
	add	x1, sp, #4, lsl #12
	add	x0, x0, #2624
	add	x1, x1, #2624
	bl	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher8finalize
	ldr	x11, [sp, #32]
	mov	w23, #16
	mov	w12, #8
	ldr	x8, [sp, #14920]
	ldr	x9, [sp, #14912]
	cmp	x11, #1
	csel	x10, x12, x23, eq
	cmp	x11, #0
	str	x8, [sp, #20056]
	csel	x0, xzr, x10, eq
	ldr	x10, [sp, #48]
	str	x9, [sp, #20048]
	str	x9, [sp, #8224]
	add	x1, x0, x10
	str	x8, [sp, #8232]
	cmp	x1, x0
	b.lo	.LBB3_88
	cmp	x1, #27
	b.hs	.LBB3_88
	ldr	x8, [sp, #48]
	cbz	x8, .LBB3_76
	ldr	x10, [sp, #392]
	ldr	x8, [sp, #8224]
	lsl	w28, w11, #24
	ldr	x9, [sp, #8232]
	mov	x24, xzr
	add	x10, x10, x0, lsl #4
	str	x8, [sp, #12864]
	str	x9, [sp, #12872]
	str	x10, [sp, #432]
.LBB3_59:
	mov	w8, #1
	ldr	x10, [sp, #12872]
	ldr	x11, [sp, #432]
	lsl	x8, x8, x24
	ldr	x12, [sp, #40]
	ldr	x9, [sp, #12864]
	add	x11, x11, x24, lsl #4
	str	x10, [sp, #13896]
	add	x10, sp, #3, lsl #12
	tst	x8, x12
	add	x10, x10, #1600
	str	x9, [sp, #13888]
	csel	x8, x10, x11, eq
	csel	x10, x11, x10, eq
	add	x24, x24, #1
	ldp	x9, x8, [x8]
	add	x0, sp, #2, lsl #12
	add	x0, x0, #448
	mov	w1, wzr
	mov	w2, #344
	str	w28, [sp, #15936]
	str	x9, [sp, #14912]
	ldp	x9, x10, [x10]
	str	x8, [sp, #14920]
	add	x8, sp, #3, lsl #12
	add	x8, x8, #2624
	str	wzr, [sp, #15940]
	stp	x9, x10, [x8, #16]
	lsr	x8, x12, x24
	ldr	x9, [sp, #440]
	mov	w10, #33554432
	str	x9, [sp, #15944]
	rev	w9, w24
	rev	w8, w8
	str	x10, [sp, #15952]
	str	w9, [sp, #15960]
	str	w8, [sp, #15964]
	bl	memset
	ldr	x8, [sp, #8976]
	ldp	x9, x10, [sp, #448]
	add	x0, x8, #16
	cmp	x0, #136
	stp	x9, x10, [x25]
	str	x0, [sp, #8976]
	b.ne	.LBB3_61
	ldr	x9, [sp, #8840]
	ldr	x14, [sp, #8640]
	ldr	x10, [sp, #8848]
	ldr	x15, [sp, #8648]
	ldr	x8, [sp, #8856]
	ldr	x16, [sp, #8864]
	eor	x9, x14, x9
	ldr	x14, [sp, #8664]
	ldr	x12, [sp, #8872]
	eor	x10, x15, x10
	str	x9, [sp, #8640]
	ldr	x9, [sp, #8656]
	str	x10, [sp, #8648]
	ldr	x10, [sp, #8672]
	ldr	x13, [sp, #8880]
	eor	x8, x9, x8
	eor	x9, x14, x16
	ldr	x11, [sp, #8888]
	str	x8, [sp, #8656]
	ldr	x8, [sp, #8680]
	ldr	x15, [sp, #8896]
	str	x9, [sp, #8664]
	eor	x9, x10, x12
	ldr	x10, [sp, #8688]
	eor	x8, x8, x13
	ldr	x18, [sp, #8904]
	ldr	x12, [sp, #8696]
	ldr	x13, [sp, #8704]
	ldr	x14, [sp, #8912]
	ldr	x0, [sp, #8712]
	str	x8, [sp, #8680]
	eor	x8, x10, x11
	ldr	x16, [sp, #8920]
	eor	x10, x13, x18
	eor	x11, x0, x14
	add	x0, sp, #2, lsl #12
	add	x0, x0, #448
	str	x9, [sp, #8672]
	eor	x9, x12, x15
	ldr	x13, [sp, #8928]
	str	x8, [sp, #8688]
	ldr	x8, [sp, #8728]
	ldr	x12, [sp, #8720]
	ldr	x14, [sp, #8936]
	str	x9, [sp, #8696]
	eor	x8, x8, x13
	ldr	x9, [sp, #8736]
	str	x10, [sp, #8704]
	eor	x12, x12, x16
	ldr	x10, [sp, #8944]
	str	x11, [sp, #8712]
	eor	x9, x9, x14
	ldr	x11, [sp, #8744]
	ldr	x13, [sp, #8952]
	str	x8, [sp, #8728]
	ldr	x8, [sp, #8752]
	ldr	x17, [sp, #8768]
	eor	x10, x11, x10
	str	x12, [sp, #8720]
	ldr	x11, [sp, #8960]
	eor	x8, x8, x13
	str	x9, [sp, #8736]
	ldr	x9, [sp, #8760]
	ldr	x12, [sp, #8968]
	str	x8, [sp, #8752]
	eor	x9, x9, x11
	str	x10, [sp, #8744]
	eor	x8, x17, x12
	str	x9, [sp, #8760]
	str	x8, [sp, #8768]
	bl	_RNvCsndc0WgnAaH_9keccak2568keccak_f
	mov	x0, xzr
	str	xzr, [sp, #8976]
.LBB3_61:
	add	x20, sp, #3, lsl #12
	mov	w23, #32
	add	x20, x20, #3648
	b	.LBB3_63
.LBB3_62:
	sub	x23, x23, x22
	add	x20, x20, x22
	cbz	x23, .LBB3_67
.LBB3_63:
	sub	x8, x19, x0
	cmp	x23, x8
	csel	x22, x23, x8, lo
	add	x1, x22, x0
	cmp	x1, x0
	b.lo	.LBB3_79
	cmp	x1, #137
	b.hs	.LBB3_79
	add	x0, x25, x0
	mov	x1, x20
	mov	x2, x22
	bl	memcpy
	ldr	x8, [sp, #8976]
	add	x0, x8, x22
	cmp	x0, #136
	str	x0, [sp, #8976]
	b.ne	.LBB3_62
	ldr	x9, [sp, #8840]
	ldr	x14, [sp, #8640]
	ldr	x10, [sp, #8848]
	ldr	x15, [sp, #8648]
	ldr	x8, [sp, #8856]
	ldr	x16, [sp, #8864]
	eor	x9, x14, x9
	ldr	x14, [sp, #8664]
	ldr	x12, [sp, #8872]
	eor	x10, x15, x10
	str	x9, [sp, #8640]
	ldr	x9, [sp, #8656]
	str	x10, [sp, #8648]
	ldr	x10, [sp, #8672]
	ldr	x13, [sp, #8880]
	eor	x8, x9, x8
	eor	x9, x14, x16
	ldr	x11, [sp, #8888]
	str	x8, [sp, #8656]
	ldr	x8, [sp, #8680]
	ldr	x15, [sp, #8896]
	str	x9, [sp, #8664]
	eor	x9, x10, x12
	ldr	x10, [sp, #8688]
	eor	x8, x8, x13
	ldr	x18, [sp, #8904]
	ldr	x12, [sp, #8696]
	ldr	x13, [sp, #8704]
	ldr	x14, [sp, #8912]
	ldr	x0, [sp, #8712]
	str	x8, [sp, #8680]
	eor	x8, x10, x11
	ldr	x16, [sp, #8920]
	eor	x10, x13, x18
	eor	x11, x0, x14
	add	x0, sp, #2, lsl #12
	add	x0, x0, #448
	str	x9, [sp, #8672]
	eor	x9, x12, x15
	ldr	x13, [sp, #8928]
	str	x8, [sp, #8688]
	ldr	x8, [sp, #8728]
	ldr	x12, [sp, #8720]
	ldr	x14, [sp, #8936]
	str	x9, [sp, #8696]
	eor	x8, x8, x13
	ldr	x9, [sp, #8736]
	str	x10, [sp, #8704]
	eor	x12, x12, x16
	ldr	x10, [sp, #8944]
	str	x11, [sp, #8712]
	eor	x9, x9, x14
	ldr	x11, [sp, #8744]
	ldr	x13, [sp, #8952]
	str	x8, [sp, #8728]
	ldr	x8, [sp, #8752]
	ldr	x17, [sp, #8768]
	eor	x10, x11, x10
	str	x12, [sp, #8720]
	ldr	x11, [sp, #8960]
	eor	x8, x8, x13
	str	x9, [sp, #8736]
	ldr	x9, [sp, #8760]
	ldr	x12, [sp, #8968]
	str	x8, [sp, #8752]
	eor	x9, x9, x11
	str	x10, [sp, #8744]
	eor	x8, x17, x12
	str	x9, [sp, #8760]
	str	x8, [sp, #8768]
	bl	_RNvCsndc0WgnAaH_9keccak2568keccak_f
	mov	x0, xzr
	str	xzr, [sp, #8976]
	b	.LBB3_62
.LBB3_67:
	add	x0, sp, #4, lsl #12
	add	x1, sp, #2, lsl #12
	mov	w2, #344
	add	x0, x0, #2624
	add	x1, x1, #448
	bl	memcpy
	ldr	x23, [sp, #19344]
	add	x20, sp, #3, lsl #12
	mov	w26, #32
	add	x20, x20, #2624
	b	.LBB3_69
.LBB3_68:
	sub	x26, x26, x22
	add	x20, x20, x22
	cbz	x26, .LBB3_73
.LBB3_69:
	sub	x8, x19, x23
	cmp	x26, x8
	csel	x22, x26, x8, lo
	add	x1, x22, x23
	cmp	x1, x23
	b.lo	.LBB3_86
	cmp	x1, #137
	b.hs	.LBB3_86
	add	x0, x21, x23
	mov	x1, x20
	mov	x2, x22
	bl	memcpy
	ldr	x8, [sp, #19344]
	add	x23, x8, x22
	cmp	x23, #136
	str	x23, [sp, #19344]
	b.ne	.LBB3_68
	ldr	x9, [sp, #19208]
	ldr	x14, [sp, #19008]
	ldr	x10, [sp, #19216]
	ldr	x15, [sp, #19016]
	ldr	x8, [sp, #19224]
	ldr	x16, [sp, #19232]
	eor	x9, x14, x9
	ldr	x14, [sp, #19032]
	ldr	x12, [sp, #19240]
	eor	x10, x15, x10
	str	x9, [sp, #19008]
	ldr	x9, [sp, #19024]
	str	x10, [sp, #19016]
	ldr	x10, [sp, #19040]
	ldr	x13, [sp, #19248]
	eor	x8, x9, x8
	eor	x9, x14, x16
	ldr	x11, [sp, #19256]
	str	x8, [sp, #19024]
	ldr	x8, [sp, #19048]
	ldr	x15, [sp, #19264]
	str	x9, [sp, #19032]
	eor	x9, x10, x12
	ldr	x10, [sp, #19056]
	eor	x8, x8, x13
	ldr	x18, [sp, #19272]
	ldr	x12, [sp, #19064]
	ldr	x13, [sp, #19072]
	ldr	x14, [sp, #19280]
	ldr	x0, [sp, #19080]
	str	x8, [sp, #19048]
	eor	x8, x10, x11
	ldr	x16, [sp, #19288]
	eor	x10, x13, x18
	eor	x11, x0, x14
	add	x0, sp, #4, lsl #12
	add	x0, x0, #2624
	str	x9, [sp, #19040]
	eor	x9, x12, x15
	ldr	x13, [sp, #19296]
	str	x8, [sp, #19056]
	ldr	x8, [sp, #19096]
	ldr	x12, [sp, #19088]
	ldr	x14, [sp, #19304]
	str	x9, [sp, #19064]
	eor	x8, x8, x13
	ldr	x9, [sp, #19104]
	str	x10, [sp, #19072]
	eor	x12, x12, x16
	ldr	x10, [sp, #19312]
	str	x11, [sp, #19080]
	eor	x9, x9, x14
	ldr	x11, [sp, #19112]
	ldr	x13, [sp, #19320]
	str	x8, [sp, #19096]
	ldr	x8, [sp, #19120]
	ldr	x17, [sp, #19136]
	eor	x10, x11, x10
	str	x12, [sp, #19088]
	ldr	x11, [sp, #19328]
	eor	x8, x8, x13
	str	x9, [sp, #19104]
	ldr	x9, [sp, #19128]
	ldr	x12, [sp, #19336]
	str	x8, [sp, #19120]
	eor	x9, x9, x11
	str	x10, [sp, #19112]
	eor	x8, x17, x12
	str	x9, [sp, #19128]
	str	x8, [sp, #19136]
	bl	_RNvCsndc0WgnAaH_9keccak2568keccak_f
	mov	x23, xzr
	str	xzr, [sp, #19344]
	b	.LBB3_68
.LBB3_73:
	add	x0, sp, #2, lsl #12
	add	x1, sp, #4, lsl #12
	mov	w2, #200
	add	x0, x0, #448
	add	x1, x1, #2624
	bl	memcpy
	cmp	x23, #137
	b.hs	.LBB3_87
	add	x0, sp, #4, lsl #12
	mov	x1, x21
	mov	x2, x23
	add	x0, x0, #576
	str	xzr, [sp, #17088]
	str	xzr, [sp, #17080]
	str	xzr, [sp, #17072]
	str	xzr, [sp, #17064]
	str	xzr, [sp, #17056]
	str	xzr, [sp, #17048]
	str	xzr, [sp, #17040]
	str	xzr, [sp, #17032]
	str	xzr, [sp, #17024]
	str	xzr, [sp, #17016]
	str	xzr, [sp, #17008]
	str	xzr, [sp, #17000]
	str	xzr, [sp, #16992]
	str	xzr, [sp, #16984]
	str	xzr, [sp, #16976]
	str	xzr, [sp, #16968]
	str	xzr, [sp, #16960]
	bl	memcpy
	add	x9, sp, #4, lsl #12
	add	x18, sp, #3, lsl #12
	ldr	x0, [sp, #8648]
	add	x9, x9, #576
	add	x18, x18, #3648
	ldrb	w8, [x9, x23]
	eor	w8, w8, #0x1
	strb	w8, [x9, x23]
	ldr	x8, [sp, #8640]
	ldr	x10, [sp, #16960]
	ldr	x11, [sp, #16968]
	ldr	x12, [sp, #16976]
	ldrb	w9, [x18, #1159]
	ldr	x13, [sp, #16984]
	eor	x8, x8, x10
	ldr	x10, [sp, #8656]
	eor	x11, x0, x11
	ldr	x0, [sp, #8664]
	ldr	x14, [sp, #16992]
	ldr	x15, [sp, #17000]
	str	x8, [sp, #8640]
	eor	x8, x10, x12
	ldr	x10, [sp, #8672]
	ldr	x12, [sp, #8680]
	eor	w9, w9, #0x80
	str	x11, [sp, #8648]
	eor	x11, x0, x13
	ldr	x16, [sp, #17008]
	ldr	x17, [sp, #17016]
	strb	w9, [x18, #1159]
	ldr	x9, [sp, #17024]
	ldr	x13, [sp, #8704]
	str	x8, [sp, #8656]
	eor	x8, x10, x14
	ldr	x10, [sp, #8688]
	str	x11, [sp, #8664]
	eor	x11, x12, x15
	ldr	x12, [sp, #8696]
	ldr	x14, [sp, #17048]
	str	x11, [sp, #8680]
	ldr	x11, [sp, #8728]
	str	x8, [sp, #8672]
	eor	x8, x10, x16
	eor	x12, x12, x17
	eor	x9, x13, x9
	ldr	x18, [sp, #17032]
	ldr	x1, [sp, #17040]
	ldr	x10, [sp, #8712]
	ldr	x13, [sp, #8720]
	str	x8, [sp, #8688]
	ldr	x8, [sp, #17056]
	str	x12, [sp, #8696]
	ldr	x12, [sp, #8736]
	eor	x11, x11, x14
	ldr	x14, [sp, #17064]
	str	x9, [sp, #8704]
	ldr	x9, [sp, #8744]
	eor	x10, x10, x18
	eor	x13, x13, x1
	eor	x8, x12, x8
	str	x10, [sp, #8712]
	ldr	x10, [sp, #17072]
	eor	x9, x9, x14
	str	x13, [sp, #8720]
	ldr	x12, [sp, #8752]
	ldr	x13, [sp, #17080]
	str	x11, [sp, #8728]
	ldr	x11, [sp, #8760]
	str	x8, [sp, #8736]
	ldr	x8, [sp, #17088]
	add	x0, sp, #2, lsl #12
	str	x9, [sp, #8744]
	ldr	x9, [sp, #8768]
	eor	x10, x12, x10
	eor	x11, x11, x13
	add	x0, x0, #448
	str	x10, [sp, #8752]
	eor	x8, x9, x8
	str	x11, [sp, #8760]
	str	x8, [sp, #8768]
	bl	_RNvCsndc0WgnAaH_9keccak2568keccak_f
	ldr	x10, [sp, #48]
	ldr	x8, [sp, #8648]
	ldr	x9, [sp, #8640]
	cmp	x24, x10
	str	x8, [sp, #16968]
	str	x9, [sp, #16960]
	str	x9, [sp, #12864]
	str	x8, [sp, #12872]
	b.ne	.LBB3_59
	ldr	x8, [sp, #12864]
	ldr	x9, [sp, #12872]
	mov	w23, #16
	mov	w12, #8
	b	.LBB3_77
.LBB3_76:
	ldr	x8, [sp, #8224]
	ldr	x9, [sp, #8232]
.LBB3_77:
	str	x8, [sp, #8640]
	str	x9, [sp, #8648]
	ldr	x11, [sp, #24]
	mov	w10, #7740
	add	x22, sp, #3, lsl #12
	mov	w13, #117440512
	cmp	x11, x10
	str	x8, [sp, #20032]
	add	x8, sp, #484
	ldp	x24, x10, [sp, #8]
	add	x8, x8, x11
	str	x8, [sp, #408]
	add	x22, x22, #3648
	adrp	x8, .Lanon.bee145f0cb2eac5728ff95be1b200579.2
	add	x8, x8, :lo12:.Lanon.bee145f0cb2eac5728ff95be1b200579.2
	str	x9, [sp, #20040]
	b.ne	.LBB3_32
	ldp	x8, x11, [sp, #464]
	ldr	x9, [sp, #20032]
	ldr	x10, [sp, #20040]
	cmp	x9, x8
	ccmp	x10, x11, #0, eq
	cset	w0, eq
	b	.LBB3_84
.LBB3_79:
	adrp	x3, .Lanon.47fac95803119c4a094797088418c9d4.15
	add	x3, x3, :lo12:.Lanon.47fac95803119c4a094797088418c9d4.15
	mov	w2, #136
	bl	_RNvNtNtCs8l20omZJ7ql_4core5slice5index16slice_index_fail
.LBB3_80:
	adrp	x3, .Lanon.47fac95803119c4a094797088418c9d4.15
	add	x3, x3, :lo12:.Lanon.47fac95803119c4a094797088418c9d4.15
	mov	x0, x25
	mov	w2, #136
	bl	_RNvNtNtCs8l20omZJ7ql_4core5slice5index16slice_index_fail
.LBB3_81:
	adrp	x3, .Lanon.47fac95803119c4a094797088418c9d4.16
	add	x3, x3, :lo12:.Lanon.47fac95803119c4a094797088418c9d4.16
	mov	x0, xzr
	mov	x1, x25
	mov	w2, #136
	bl	_RNvNtNtCs8l20omZJ7ql_4core5slice5index16slice_index_fail
.LBB3_82:
	adrp	x3, .Lanon.47fac95803119c4a094797088418c9d4.15
	add	x3, x3, :lo12:.Lanon.47fac95803119c4a094797088418c9d4.15
	mov	x0, x24
	mov	w2, #136
	bl	_RNvNtNtCs8l20omZJ7ql_4core5slice5index16slice_index_fail
.LBB3_83:
	mov	x0, xzr
.LBB3_84:
	add	sp, sp, #5, lsl #12
	add	sp, sp, #1040
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
.LBB3_85:
	.cfi_restore_state
	adrp	x3, .Lanon.47fac95803119c4a094797088418c9d4.16
	add	x3, x3, :lo12:.Lanon.47fac95803119c4a094797088418c9d4.16
	mov	x0, xzr
	mov	x1, x24
	mov	w2, #136
	bl	_RNvNtNtCs8l20omZJ7ql_4core5slice5index16slice_index_fail
.LBB3_86:
	adrp	x3, .Lanon.47fac95803119c4a094797088418c9d4.15
	add	x3, x3, :lo12:.Lanon.47fac95803119c4a094797088418c9d4.15
	mov	x0, x23
	mov	w2, #136
	bl	_RNvNtNtCs8l20omZJ7ql_4core5slice5index16slice_index_fail
.LBB3_87:
	adrp	x3, .Lanon.47fac95803119c4a094797088418c9d4.16
	add	x3, x3, :lo12:.Lanon.47fac95803119c4a094797088418c9d4.16
	mov	x0, xzr
	mov	x1, x23
	mov	w2, #136
	bl	_RNvNtNtCs8l20omZJ7ql_4core5slice5index16slice_index_fail
.LBB3_88:
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
	mov	x17, xzr
	ldp	x5, x18, [x0, #112]
	ldr	x27, [x0, #192]
	ldp	x9, x10, [x0]
	str	x0, [sp, #8]
	mov	x22, x15
	str	x8, [sp, #72]
	ldp	x11, x2, [x0, #80]
	ldp	x4, x13, [x0, #48]
	eor	x8, x8, x9
	ldp	x19, x3, [x0, #128]
	stp	x10, x30, [sp, #88]
	stp	x11, x9, [sp, #40]
	eor	x9, x11, x18
	ldp	x11, x14, [x0, #16]
	eor	x8, x8, x9
	ldp	x1, x7, [x0, #96]
	eor	x9, x4, x10
	ldp	x25, x20, [x0, #144]
	eor	x10, x2, x19
	ldp	x12, x6, [x0, #64]
	eor	x9, x9, x10
	str	x11, [sp, #80]
	eor	x10, x13, x11
	eor	x11, x1, x3
	ldp	x23, x21, [x0, #160]
	eor	x10, x10, x11
	stp	x14, x13, [sp, #56]
	ldp	x16, x24, [x0, #176]
	eor	x11, x12, x14
	eor	x13, x7, x25
	eor	x14, x5, x20
	eor	x11, x11, x13
	eor	x13, x6, x15
	eor	x28, x8, x23
	eor	x13, x13, x14
	eor	x30, x9, x21
	eor	x8, x10, x16
	eor	x15, x11, x24
	eor	x0, x13, x27
.LBB9_1:
	stp	x24, x5, [sp, #16]
	mov	x24, x2
	eor	x2, x0, x30, ror #63
	mov	x26, x3
	eor	x3, x30, x15, ror #63
	eor	x30, x28, x8, ror #63
	eor	x5, x8, x0, ror #63
	ldr	x8, [sp, #48]
	str	x21, [sp, #32]
	mov	x21, x12
	eor	x15, x15, x28, ror #63
	eor	x9, x1, x3
	eor	x12, x8, x2
	eor	x8, x4, x30
	eor	x10, x25, x5
	ror	x4, x8, #20
	ldr	x8, [sp, #56]
	ror	x1, x10, #43
	ldr	x10, [sp, #40]
	str	x17, [sp, #104]
	eor	x11, x27, x15
	ror	x17, x9, #21
	eor	x8, x8, x5
	eor	x9, x6, x15
	ldr	x13, [sp, #88]
	mov	x28, x18
	ror	x18, x11, #50
	eor	x11, x10, x2
	ror	x6, x8, #36
	ror	x10, x9, #44
	eor	x8, x19, x30
	eor	x9, x16, x3
	eor	x16, x13, x30
	ror	x13, x8, #19
	ror	x14, x9, #3
	eor	x9, x7, x5
	ror	x19, x16, #63
	eor	x0, x20, x15
	ror	x16, x9, #39
	ldp	x8, x9, [sp, #64]
	eor	x8, x8, x3
	ldr	x7, [sp, #16]
	ror	x25, x8, #58
	ror	x20, x0, #56
	eor	x8, x23, x2
	eor	x0, x22, x15
	eor	x22, x9, x2
	ror	x9, x8, #46
	ror	x8, x0, #37
	ror	x0, x22, #28
	eor	x22, x24, x30
	eor	x24, x7, x5
	ldr	x7, [sp, #80]
	eor	x23, x26, x3
	eor	x5, x21, x5
	ror	x26, x22, #54
	eor	x3, x7, x3
	ldr	x7, [sp, #24]
	ror	x22, x23, #49
	ror	x23, x24, #8
	ror	x24, x3, #2
	ror	x27, x5, #9
	eor	x15, x7, x15
	bic	x5, x1, x17
	eor	x2, x28, x2
	ror	x21, x15, #25
	ldr	x15, [sp, #32]
	eor	x7, x5, x4
	adrp	x5, .Lanon.47fac95803119c4a094797088418c9d4.6
	add	x5, x5, :lo12:.Lanon.47fac95803119c4a094797088418c9d4.6
	ror	x11, x11, #61
	eor	x3, x15, x30
	ldr	x15, [sp, #104]
	ror	x28, x2, #23
	ror	x30, x3, #62
	bic	x2, x18, x1
	bic	x3, x12, x18
	ldr	x5, [x5, x15]
	eor	x2, x2, x17
	eor	x3, x3, x1
	bic	x1, x4, x12
	bic	x17, x17, x4
	str	x7, [sp, #88]
	eor	x12, x5, x12
	eor	x15, x18, x1
	bic	x18, x13, x11
	eor	x5, x17, x12
	bic	x17, x11, x10
	eor	x4, x18, x10
	eor	x1, x17, x6
	bic	x17, x14, x13
	bic	x10, x10, x6
	eor	x17, x17, x11
	bic	x11, x6, x14
	eor	x6, x14, x10
	bic	x14, x19, x9
	eor	x12, x11, x13
	eor	x11, x7, x4
	eor	x7, x14, x20
	bic	x14, x20, x16
	stp	x1, x2, [sp, #72]
	eor	x13, x2, x17
	eor	x2, x14, x25
	bic	x14, x25, x19
	stp	x5, x3, [sp, #48]
	eor	x10, x5, x1
	bic	x18, x9, x20
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
	str	x17, [sp, #64]
	eor	x17, x3, x12
	eor	x3, x14, x26
	eor	x25, x8, x22
	eor	x8, x16, x18
	eor	x20, x23, x9
	eor	x9, x2, x19
	eor	x8, x10, x8
	eor	x10, x1, x3
	eor	x14, x5, x20
	eor	x10, x13, x10
	eor	x13, x15, x6
	eor	x9, x11, x9
	eor	x11, x7, x25
	eor	x13, x13, x14
	bic	x14, x21, x27
	eor	x11, x17, x11
	bic	x17, x30, x28
	eor	x23, x14, x24
	bic	x14, x28, x21
	str	x16, [sp, #40]
	eor	x16, x17, x21
	eor	x21, x14, x27
	bic	x14, x27, x24
	mov	x22, x15
	eor	x27, x30, x14
	ldr	x14, [sp, #104]
	bic	x15, x24, x30
	eor	x24, x15, x28
	eor	x28, x8, x23
	eor	x30, x9, x21
	add	x17, x14, #8
	eor	x8, x10, x16
	eor	x15, x11, x24
	cmp	x17, #192
	eor	x0, x13, x27
	b.ne	.LBB9_1
	ldp	x9, x11, [sp, #80]
	ldr	x8, [sp, #8]
	ldr	x30, [sp, #96]
	stp	x18, x19, [x8, #120]
	str	x9, [x8, #16]
	ldp	x10, x9, [sp, #48]
	stp	x10, x11, [x8]
	stp	x9, x22, [x8, #24]
	ldp	x9, x10, [sp, #64]
	stp	x3, x25, [x8, #136]
	ldp	x26, x25, [sp, #128]
	stp	x20, x23, [x8, #152]
	ldp	x20, x19, [sp, #176]
	stp	x9, x12, [x8, #56]
	ldr	x9, [sp, #40]
	stp	x21, x16, [x8, #168]
	ldp	x22, x21, [sp, #160]
	stp	x24, x27, [x8, #184]
	ldp	x24, x23, [sp, #144]
	stp	x10, x4, [x8, #40]
	ldp	x28, x27, [sp, #112]
	stp	x6, x9, [x8, #72]
	stp	x2, x1, [x8, #88]
	stp	x7, x5, [x8, #104]
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
	adrp	x3, .Lanon.47fac95803119c4a094797088418c9d4.15
	add	x3, x3, :lo12:.Lanon.47fac95803119c4a094797088418c9d4.15
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
	adrp	x3, .Lanon.47fac95803119c4a094797088418c9d4.16
	add	x3, x3, :lo12:.Lanon.47fac95803119c4a094797088418c9d4.16
	mov	x0, xzr
	mov	x1, x20
	mov	w2, #136
	bl	_RNvNtNtCs8l20omZJ7ql_4core5slice5index16slice_index_fail
.LBB11_4:
	adrp	x0, .Lanon.47fac95803119c4a094797088418c9d4.12
	add	x0, x0, :lo12:.Lanon.47fac95803119c4a094797088418c9d4.12
	adrp	x2, .Lanon.47fac95803119c4a094797088418c9d4.13
	add	x2, x2, :lo12:.Lanon.47fac95803119c4a094797088418c9d4.13
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
	adrp	x3, .Lanon.47fac95803119c4a094797088418c9d4.15
	add	x3, x3, :lo12:.Lanon.47fac95803119c4a094797088418c9d4.15
	mov	w2, #136
	bl	_RNvNtNtCs8l20omZJ7ql_4core5slice5index16slice_index_fail
.LBB13_26:
	adrp	x3, .Lanon.47fac95803119c4a094797088418c9d4.15
	add	x3, x3, :lo12:.Lanon.47fac95803119c4a094797088418c9d4.15
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
	adrp	x3, .Lanon.47fac95803119c4a094797088418c9d4.16
	add	x3, x3, :lo12:.Lanon.47fac95803119c4a094797088418c9d4.16
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

	.type	.Lanon.47fac95803119c4a094797088418c9d4.6,@object
	.section	.rodata..Lanon.47fac95803119c4a094797088418c9d4.6,"a",@progbits
	.p2align	3, 0x0
.Lanon.47fac95803119c4a094797088418c9d4.6:
	.ascii	"\001\000\000\000\000\000\000\000\202\200\000\000\000\000\000\000\212\200\000\000\000\000\000\200\000\200\000\200\000\000\000\200\213\200\000\000\000\000\000\000\001\000\000\200\000\000\000\000\201\200\000\200\000\000\000\200\t\200\000\000\000\000\000\200\212\000\000\000\000\000\000\000\210\000\000\000\000\000\000\000\t\200\000\200\000\000\000\000\n\000\000\200\000\000\000\000\213\200\000\200\000\000\000\000\213\000\000\000\000\000\000\200\211\200\000\000\000\000\000\200\003\200\000\000\000\000\000\200\002\200\000\000\000\000\000\200\200\000\000\000\000\000\000\200\n\200\000\000\000\000\000\000\n\000\000\200\000\000\000\200\201\200\000\200\000\000\000\200\200\200\000\000\000\000\000\200\001\000\000\200\000\000\000\000\b\200\000\200\000\000\000\200"
	.size	.Lanon.47fac95803119c4a094797088418c9d4.6, 192

	.type	.Lanon.47fac95803119c4a094797088418c9d4.9,@object
	.section	.rodata.str1.1,"aMS",@progbits,1
.Lanon.47fac95803119c4a094797088418c9d4.9:
	.asciz	"crates/keccak256/src/lib.rs"
	.size	.Lanon.47fac95803119c4a094797088418c9d4.9, 28

	.type	.Lanon.47fac95803119c4a094797088418c9d4.12,@object
	.section	.rodata..Lanon.47fac95803119c4a094797088418c9d4.12,"a",@progbits
.Lanon.47fac95803119c4a094797088418c9d4.12:
	.ascii	"a final block holds fewer than RATE message bytes"
	.size	.Lanon.47fac95803119c4a094797088418c9d4.12, 49

	.type	.Lanon.47fac95803119c4a094797088418c9d4.13,@object
	.section	.data.rel.ro..Lanon.47fac95803119c4a094797088418c9d4.13,"aw",@progbits
	.p2align	3, 0x0
.Lanon.47fac95803119c4a094797088418c9d4.13:
	.xword	.Lanon.47fac95803119c4a094797088418c9d4.9
	.asciz	"\033\000\000\000\000\000\000\000\200\000\000\000\005\000\000"
	.size	.Lanon.47fac95803119c4a094797088418c9d4.13, 24

	.type	.Lanon.47fac95803119c4a094797088418c9d4.15,@object
	.section	.data.rel.ro..Lanon.47fac95803119c4a094797088418c9d4.15,"aw",@progbits
	.p2align	3, 0x0
.Lanon.47fac95803119c4a094797088418c9d4.15:
	.xword	.Lanon.47fac95803119c4a094797088418c9d4.9
	.asciz	"\033\000\000\000\000\000\000\000\247\000\000\000\025\000\000"
	.size	.Lanon.47fac95803119c4a094797088418c9d4.15, 24

	.type	.Lanon.47fac95803119c4a094797088418c9d4.16,@object
	.section	.data.rel.ro..Lanon.47fac95803119c4a094797088418c9d4.16,"aw",@progbits
	.p2align	3, 0x0
.Lanon.47fac95803119c4a094797088418c9d4.16:
	.xword	.Lanon.47fac95803119c4a094797088418c9d4.9
	.asciz	"\033\000\000\000\000\000\000\000\264\000\000\0002\000\000"
	.size	.Lanon.47fac95803119c4a094797088418c9d4.16, 24

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
