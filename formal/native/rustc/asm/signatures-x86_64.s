	.att_syntax
	.file	"signatures.2a34a834e9d96c0-cgu.0"
	.section	.text._RNvCs5fGHjzWXRav_7___rustc17rust_begin_unwind,"ax",@progbits
	.p2align	4
	.type	_RNvCs5fGHjzWXRav_7___rustc17rust_begin_unwind,@function
_RNvCs5fGHjzWXRav_7___rustc17rust_begin_unwind:
.Lfunc_begin0:
	.cfi_startproc
	#APP

	ud2

	#NO_APP
	ud2
.Lfunc_end0:
	.size	_RNvCs5fGHjzWXRav_7___rustc17rust_begin_unwind, .Lfunc_end0-_RNvCs5fGHjzWXRav_7___rustc17rust_begin_unwind
	.cfi_endproc

	.section	.text.memcpy,"ax",@progbits
	.globl	memcpy
	.p2align	4
	.type	memcpy,@function
memcpy:
.Lfunc_begin1:
	.cfi_startproc
	movq	%rdi, %rax
	movl	%esi, %ecx
	orl	%eax, %ecx
	movl	%edx, %edi
	orl	%ecx, %edi
	testb	$7, %dil
	je	.LBB1_4
	testq	%rdx, %rdx
	je	.LBB1_7
	xorl	%ecx, %ecx
	.p2align	4
.LBB1_3:
	movzbl	(%rsi,%rcx), %edi
	movb	%dil, (%rax,%rcx)
	incq	%rcx
	#APP
	#NO_APP
	cmpq	%rcx, %rdx
	jne	.LBB1_3
	jmp	.LBB1_7
.LBB1_4:
	testq	%rdx, %rdx
	je	.LBB1_7
	xorl	%ecx, %ecx
	.p2align	4
.LBB1_6:
	movq	(%rsi,%rcx), %rdi
	movq	%rdi, (%rax,%rcx)
	addq	$8, %rcx
	#APP
	#NO_APP
	cmpq	%rdx, %rcx
	jb	.LBB1_6
.LBB1_7:
	retq
.Lfunc_end1:
	.size	memcpy, .Lfunc_end1-memcpy
	.cfi_endproc

	.section	.text.memset,"ax",@progbits
	.globl	memset
	.p2align	4
	.type	memset,@function
memset:
.Lfunc_begin2:
	.cfi_startproc
	movq	%rdi, %rax
	movl	%edx, %ecx
	orl	%eax, %ecx
	testb	$7, %cl
	je	.LBB2_4
	testq	%rdx, %rdx
	je	.LBB2_7
	xorl	%ecx, %ecx
	.p2align	4
.LBB2_3:
	movb	%sil, (%rax,%rcx)
	incq	%rcx
	#APP
	#NO_APP
	cmpq	%rcx, %rdx
	jne	.LBB2_3
	jmp	.LBB2_7
.LBB2_4:
	testq	%rdx, %rdx
	je	.LBB2_7
	movzbl	%sil, %esi
	movabsq	$72340172838076673, %rcx
	imulq	%rsi, %rcx
	xorl	%esi, %esi
	.p2align	4
.LBB2_6:
	movq	%rcx, (%rax,%rsi)
	addq	$8, %rsi
	#APP
	#NO_APP
	cmpq	%rdx, %rsi
	jb	.LBB2_6
.LBB2_7:
	retq
.Lfunc_end2:
	.size	memset, .Lfunc_end2-memset
	.cfi_endproc

	.section	.text.sphincs_verify,"ax",@progbits
	.globl	sphincs_verify
	.p2align	4
	.type	sphincs_verify,@function
sphincs_verify:
.Lfunc_begin3:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	pushq	%r15
	.cfi_def_cfa_offset 24
	pushq	%r14
	.cfi_def_cfa_offset 32
	pushq	%r13
	.cfi_def_cfa_offset 40
	pushq	%r12
	.cfi_def_cfa_offset 48
	pushq	%rbx
	.cfi_def_cfa_offset 56
	subq	$4096, %rsp
	.cfi_adjust_cfa_offset 4096
	movq	$0, (%rsp)
	subq	$4096, %rsp
	.cfi_adjust_cfa_offset 4096
	movq	$0, (%rsp)
	subq	$4096, %rsp
	.cfi_adjust_cfa_offset 4096
	movq	$0, (%rsp)
	subq	$4096, %rsp
	.cfi_adjust_cfa_offset 4096
	movq	$0, (%rsp)
	subq	$4096, %rsp
	.cfi_adjust_cfa_offset 4096
	movq	$0, (%rsp)
	subq	$4096, %rsp
	.cfi_adjust_cfa_offset 4096
	movq	$0, (%rsp)
	subq	$4096, %rsp
	.cfi_adjust_cfa_offset 4096
	movq	$0, (%rsp)
	subq	$664, %rsp
	.cfi_def_cfa_offset 29392
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	%rdi, %rbx
	movq	1024(%rdi), %r14
	movq	1032(%rdi), %r15
	movq	1040(%rdi), %r13
	movq	1048(%rdi), %rbp
	movq	1056(%rdi), %rax
	movq	%rax, 1600(%rsp)
	movq	1064(%rdi), %rax
	movq	%rax, 1608(%rsp)
	movq	1072(%rdi), %rax
	movq	%rax, 1616(%rsp)
	movq	1080(%rdi), %rax
	movq	%rax, 1624(%rsp)
	leaq	12416(%rsp), %rdi
	xorl	%r12d, %r12d
	movl	$7740, %edx
	xorl	%esi, %esi
	callq	*memset@GOTPCREL(%rip)
	.p2align	4
.LBB3_1:
	movq	1088(%rbx,%r12), %rax
	movq	%rax, 12416(%rsp,%r12)
	movq	1096(%rbx,%r12), %rax
	movq	%rax, 12424(%rsp,%r12)
	movq	1104(%rbx,%r12), %rax
	movq	%rax, 12432(%rsp,%r12)
	movq	1112(%rbx,%r12), %rax
	movq	%rax, 12440(%rsp,%r12)
	movq	1120(%rbx,%r12), %rax
	movq	%rax, 12448(%rsp,%r12)
	addq	$40, %r12
	cmpq	$4240, %r12
	jne	.LBB3_1
	movl	5328(%rbx), %eax
	bswapl	%eax
	movl	%eax, 16656(%rsp)
	movl	$5360, %eax
	.p2align	4
.LBB3_3:
	movq	-24(%rbx,%rax), %rcx
	movq	%rcx, 11300(%rsp,%rax)
	movq	-16(%rbx,%rax), %rcx
	movq	%rcx, 11308(%rsp,%rax)
	movq	-8(%rbx,%rax), %rcx
	movq	%rcx, 11316(%rsp,%rax)
	movq	(%rbx,%rax), %rcx
	movq	%rcx, 11324(%rsp,%rax)
	addq	$32, %rax
	cmpq	$6512, %rax
	jne	.LBB3_3
	movl	6488(%rbx), %eax
	bswapl	%eax
	movl	%eax, 17812(%rsp)
	movl	$6520, %eax
	.p2align	4
.LBB3_5:
	movq	-24(%rbx,%rax), %rcx
	movq	%rcx, 11296(%rsp,%rax)
	movq	-16(%rbx,%rax), %rcx
	movq	%rcx, 11304(%rsp,%rax)
	movq	-8(%rbx,%rax), %rcx
	movq	%rcx, 11312(%rsp,%rax)
	movq	(%rbx,%rax), %rcx
	movq	%rcx, 11320(%rsp,%rax)
	addq	$32, %rax
	cmpq	$7672, %rax
	jne	.LBB3_5
	movl	7648(%rbx), %eax
	bswapl	%eax
	movl	%eax, 18968(%rsp)
	movl	$7680, %eax
	.p2align	4
.LBB3_7:
	movq	-24(%rbx,%rax), %rcx
	movq	%rcx, 11292(%rsp,%rax)
	movq	-16(%rbx,%rax), %rcx
	movq	%rcx, 11300(%rsp,%rax)
	movq	-8(%rbx,%rax), %rcx
	movq	%rcx, 11308(%rsp,%rax)
	movq	(%rbx,%rax), %rcx
	movq	%rcx, 11316(%rsp,%rax)
	addq	$32, %rax
	cmpq	$8864, %rax
	jne	.LBB3_7
	movq	%r13, 128(%rsp)
	movq	%rbp, 136(%rsp)
	movq	%r14, 112(%rsp)
	movq	%r15, 120(%rsp)
	leaq	592(%rsp), %r15
	movl	$176, %r13d
	leaq	20700(%rsp), %rbp
	leaq	20540(%rsp), %rbx
	leaq	576(%rsp), %r14
	movq	memcpy@GOTPCREL(%rip), %r12
	.p2align	4
.LBB3_9:
	movq	12256(%rsp,%r13), %rax
	movq	12264(%rsp,%r13), %rcx
	movq	%rcx, 8(%rbp)
	movq	%rax, (%rbp)
	movq	12272(%rsp,%r13), %rax
	movq	12280(%rsp,%r13), %rcx
	movq	%rcx, 584(%rsp)
	movq	%rax, 576(%rsp)
	movq	12296(%rsp,%r13), %rax
	movq	%rax, 8(%r15)
	movq	12288(%rsp,%r13), %rax
	movq	%rax, (%r15)
	movq	12304(%rsp,%r13), %rax
	movq	12312(%rsp,%r13), %rcx
	movq	%rcx, 24(%r15)
	movq	%rax, 16(%r15)
	movq	12320(%rsp,%r13), %rax
	movq	12328(%rsp,%r13), %rcx
	movq	%rcx, 40(%r15)
	movq	%rax, 32(%r15)
	movq	12336(%rsp,%r13), %rax
	movq	12344(%rsp,%r13), %rcx
	movq	%rcx, 56(%r15)
	movq	%rax, 48(%r15)
	movq	12352(%rsp,%r13), %rax
	movq	12360(%rsp,%r13), %rcx
	movq	%rcx, 72(%r15)
	movq	%rax, 64(%r15)
	movq	12368(%rsp,%r13), %rax
	movq	12376(%rsp,%r13), %rcx
	movq	%rcx, 88(%r15)
	movq	%rax, 80(%r15)
	movq	12384(%rsp,%r13), %rax
	movq	12392(%rsp,%r13), %rcx
	movq	%rcx, 104(%r15)
	movq	%rax, 96(%r15)
	movq	12400(%rsp,%r13), %rax
	movq	12408(%rsp,%r13), %rcx
	movq	%rcx, 120(%r15)
	movq	%rax, 112(%r15)
	movq	12416(%rsp,%r13), %rax
	movq	12424(%rsp,%r13), %rcx
	movq	%rcx, 136(%r15)
	movq	%rax, 128(%r15)
	movl	$160, %edx
	movq	%rbx, %rdi
	movq	%r14, %rsi
	callq	*%r12
	movl	$176, %edx
	movq	%r14, %rdi
	movq	%rbx, %rsi
	callq	*%r12
	leaq	(%rsp,%r13), %rdi
	addq	$3920, %rdi
	movl	$176, %edx
	movq	%r14, %rsi
	callq	*%r12
	addq	$176, %r13
	cmpq	$4400, %r13
	jne	.LBB3_9
	leaq	1760(%rsp), %rbx
	xorl	%r14d, %r14d
	movl	$288, %edx
	movq	%rbx, %rdi
	xorl	%esi, %esi
	callq	*memset@GOTPCREL(%rip)
	movl	16656(%rsp), %ebp
	.p2align	4
.LBB3_11:
	movq	16660(%rsp,%r14), %rax
	movq	16668(%rsp,%r14), %rcx
	movq	%rcx, 20548(%rsp,%r14)
	movq	%rax, 20540(%rsp,%r14)
	movq	16676(%rsp,%r14), %rax
	movq	%rax, 20556(%rsp,%r14)
	movq	16684(%rsp,%r14), %rax
	movq	%rax, 20564(%rsp,%r14)
	addq	$32, %r14
	cmpq	$1024, %r14
	jne	.LBB3_11
	leaq	576(%rsp), %r14
	leaq	20540(%rsp), %rsi
	movl	$1024, %edx
	movq	%r14, %rdi
	movq	memcpy@GOTPCREL(%rip), %r12
	callq	*%r12
	movq	17684(%rsp), %rax
	movq	17692(%rsp), %rcx
	movq	%rax, 1632(%rsp)
	movq	%rcx, 1640(%rsp)
	movq	17700(%rsp), %rax
	movq	%rax, 1648(%rsp)
	movq	17708(%rsp), %rax
	movq	%rax, 1656(%rsp)
	movq	17716(%rsp), %rax
	movq	%rax, 1664(%rsp)
	movq	17724(%rsp), %rax
	movq	%rax, 1672(%rsp)
	movq	17732(%rsp), %rax
	movq	%rax, 1680(%rsp)
	movq	17740(%rsp), %rax
	movq	%rax, 1688(%rsp)
	movq	17756(%rsp), %rax
	movq	%rax, 1704(%rsp)
	movq	17748(%rsp), %rax
	movq	%rax, 1696(%rsp)
	movq	17764(%rsp), %rax
	movq	17772(%rsp), %rcx
	movq	%rcx, 1720(%rsp)
	movq	%rax, 1712(%rsp)
	movq	17788(%rsp), %rax
	movq	%rax, 1736(%rsp)
	movq	17780(%rsp), %rax
	movq	%rax, 1728(%rsp)
	movq	17804(%rsp), %rax
	movq	%rax, 1752(%rsp)
	movq	17796(%rsp), %rax
	movq	%rax, 1744(%rsp)
	leaq	2048(%rsp), %r15
	movl	$1024, %edx
	movq	%r15, %rdi
	movq	%r14, %rsi
	callq	*%r12
	leaq	9344(%rsp), %r14
	movl	$1024, %edx
	movq	%r14, %rdi
	movq	%r15, %rsi
	callq	*%r12
	leaq	3072(%rsp), %r15
	movl	$1024, %edx
	movq	%r15, %rdi
	movq	%r14, %rsi
	callq	*%r12
	leaq	11392(%rsp), %r14
	movl	$1024, %edx
	movq	%r14, %rdi
	movq	%r15, %rsi
	callq	*%r12
	leaq	8320(%rsp), %rdi
	movl	$1024, %edx
	movq	%r14, %rsi
	callq	*%r12
	movl	17812(%rsp), %r15d
	xorl	%eax, %eax
	.p2align	4
.LBB3_13:
	movq	17816(%rsp,%rax), %rcx
	movq	17824(%rsp,%rax), %rdx
	movq	%rdx, 20548(%rsp,%rax)
	movq	%rcx, 20540(%rsp,%rax)
	movq	17832(%rsp,%rax), %rcx
	movq	%rcx, 20556(%rsp,%rax)
	movq	17840(%rsp,%rax), %rcx
	movq	%rcx, 20564(%rsp,%rax)
	addq	$32, %rax
	cmpq	$1024, %rax
	jne	.LBB3_13
	leaq	576(%rsp), %r14
	leaq	20540(%rsp), %rsi
	movl	$1024, %edx
	movq	%r14, %rdi
	movq	memcpy@GOTPCREL(%rip), %r12
	callq	*%r12
	movq	18840(%rsp), %rax
	movq	18848(%rsp), %rcx
	movq	%rcx, 8(%rbx)
	movq	%rax, (%rbx)
	movq	18856(%rsp), %rax
	movq	18864(%rsp), %rcx
	movq	%rax, 1776(%rsp)
	movq	%rcx, 1784(%rsp)
	movq	18872(%rsp), %rax
	movq	%rax, 1792(%rsp)
	movq	18880(%rsp), %rax
	movq	%rax, 1800(%rsp)
	movq	18888(%rsp), %rax
	movq	%rax, 1808(%rsp)
	movq	18896(%rsp), %rax
	movq	%rax, 1816(%rsp)
	movq	18912(%rsp), %rax
	movq	%rax, 1832(%rsp)
	movq	18904(%rsp), %rax
	movq	%rax, 1824(%rsp)
	movq	18920(%rsp), %rax
	movq	18928(%rsp), %rcx
	movq	%rcx, 1848(%rsp)
	movq	%rax, 1840(%rsp)
	movq	18944(%rsp), %rax
	movq	%rax, 1864(%rsp)
	movq	18936(%rsp), %rax
	movq	%rax, 1856(%rsp)
	movq	18960(%rsp), %rax
	movq	%rax, 1880(%rsp)
	movq	18952(%rsp), %rax
	movq	%rax, 1872(%rsp)
	leaq	2048(%rsp), %rbx
	movl	$1024, %edx
	movq	%rbx, %rdi
	movq	%r14, %rsi
	callq	*%r12
	leaq	9344(%rsp), %r14
	movl	$1024, %edx
	movq	%r14, %rdi
	movq	%rbx, %rsi
	callq	*%r12
	leaq	3072(%rsp), %rbx
	movl	$1024, %edx
	movq	%rbx, %rdi
	movq	%r14, %rsi
	callq	*%r12
	leaq	11392(%rsp), %r14
	movl	$1024, %edx
	movq	%r14, %rdi
	movq	%rbx, %rsi
	callq	*%r12
	leaq	10368(%rsp), %rdi
	movl	$1024, %edx
	movq	%r14, %rsi
	callq	*%r12
	movl	18968(%rsp), %r13d
	xorl	%eax, %eax
	.p2align	4
.LBB3_15:
	movq	18972(%rsp,%rax), %rcx
	movq	18980(%rsp,%rax), %rdx
	movq	%rdx, 20548(%rsp,%rax)
	movq	%rcx, 20540(%rsp,%rax)
	movq	18988(%rsp,%rax), %rcx
	movq	%rcx, 20556(%rsp,%rax)
	movq	18996(%rsp,%rax), %rcx
	movq	%rcx, 20564(%rsp,%rax)
	addq	$32, %rax
	cmpq	$1024, %rax
	jne	.LBB3_15
	leaq	576(%rsp), %rbx
	leaq	20540(%rsp), %rsi
	movl	$1024, %edx
	movq	%rbx, %rdi
	callq	*%r12
	movq	19996(%rsp), %rax
	movq	20004(%rsp), %rcx
	movq	%rax, 1888(%rsp)
	movq	%rcx, 1896(%rsp)
	movq	20012(%rsp), %rax
	movq	%rax, 1904(%rsp)
	movq	20020(%rsp), %rax
	movq	%rax, 1912(%rsp)
	movq	20028(%rsp), %rax
	movq	%rax, 1920(%rsp)
	movq	20036(%rsp), %rax
	movq	%rax, 1928(%rsp)
	movq	20044(%rsp), %rax
	movq	%rax, 1936(%rsp)
	movq	20052(%rsp), %rax
	movq	%rax, 1944(%rsp)
	movq	20068(%rsp), %rax
	movq	%rax, 1960(%rsp)
	movq	20060(%rsp), %rax
	movq	%rax, 1952(%rsp)
	movq	20076(%rsp), %rax
	movq	20084(%rsp), %rcx
	movq	%rcx, 1976(%rsp)
	movq	%rax, 1968(%rsp)
	movq	20100(%rsp), %rax
	movq	%rax, 1992(%rsp)
	movq	20092(%rsp), %rax
	movq	%rax, 1984(%rsp)
	movq	20116(%rsp), %rax
	movq	%rax, 2008(%rsp)
	movq	20108(%rsp), %rax
	movq	%rax, 2000(%rsp)
	movq	20132(%rsp), %rax
	movq	%rax, 2024(%rsp)
	movq	20124(%rsp), %rax
	movq	%rax, 2016(%rsp)
	bswapl	%r15d
	bswapl	%ebp
	movq	20148(%rsp), %rax
	movq	%rax, 2040(%rsp)
	movq	20140(%rsp), %rax
	movq	%rax, 2032(%rsp)
	bswapl	%r13d
	leaq	2048(%rsp), %r14
	movl	$1024, %edx
	movq	%r14, %rdi
	movq	%rbx, %rsi
	callq	*%r12
	leaq	9344(%rsp), %rbx
	movl	$1024, %edx
	movq	%rbx, %rdi
	movq	%r14, %rsi
	callq	*%r12
	movl	%r15d, %r14d
	movl	%ebp, %r15d
	leaq	3072(%rsp), %rbp
	movl	$1024, %edx
	movq	%rbp, %rdi
	movq	%rbx, %rsi
	callq	*%r12
	leaq	11392(%rsp), %rbx
	movl	$1024, %edx
	movq	%rbx, %rdi
	movq	%rbp, %rsi
	callq	*%r12
	leaq	25180(%rsp), %rbp
	movq	12416(%rsp), %rax
	movq	12424(%rsp), %rcx
	movq	%rax, 25180(%rsp)
	movq	%rcx, 25188(%rsp)
	leaq	20540(%rsp), %rdi
	leaq	4096(%rsp), %rsi
	movl	$4224, %edx
	callq	*%r12
	leaq	25196(%rsp), %rdi
	leaq	8320(%rsp), %rsi
	movl	$1024, %edx
	movq	%rdi, 176(%rsp)
	callq	*%r12
	movl	%r15d, 26220(%rsp)
	leaq	26224(%rsp), %rdi
	leaq	10368(%rsp), %rsi
	movl	$1024, %edx
	callq	*%r12
	movl	%r14d, 27248(%rsp)
	leaq	27252(%rsp), %rdi
	movl	$1024, %edx
	movq	%rbx, %rsi
	callq	*%r12
	movl	%r13d, 28276(%rsp)
	leaq	24764(%rsp), %rdi
	leaq	1632(%rsp), %rsi
	movl	$416, %edx
	callq	*%r12
	leaq	576(%rsp), %r14
	xorl	%r13d, %r13d
	movl	$344, %edx
	movq	%r14, %rdi
	xorl	%esi, %esi
	callq	*memset@GOTPCREL(%rip)
	movl	$16, %edx
	movq	%r14, %rdi
	movq	%rbp, %rsi
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	leaq	112(%rsp), %rsi
	movl	$16, %edx
	movq	%r14, %rdi
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	movl	$16, %edx
	movq	%r14, %rdi
	leaq	128(%rsp), %rsi
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	leaq	1600(%rsp), %rsi
	movl	$32, %edx
	movq	%r14, %rdi
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	leaq	4096(%rsp), %rbp
	movl	$344, %edx
	movq	%rbp, %rdi
	movq	%r14, %rsi
	callq	*%r12
	movl	$0, 9344(%rsp)
	leaq	9344(%rsp), %rbx
	movl	$4, %edx
	movq	%rbp, %rdi
	movq	%rbx, %rsi
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	leaq	11392(%rsp), %r15
	movq	%r15, %rdi
	movq	%rbp, %rsi
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher8finalize
	movq	11416(%rsp), %rax
	movq	%rax, 2072(%rsp)
	movq	11408(%rsp), %rax
	movq	%rax, 2064(%rsp)
	movq	11392(%rsp), %rax
	movq	11400(%rsp), %rcx
	movq	%rcx, 2056(%rsp)
	movq	%rax, 2048(%rsp)
	movl	$344, %edx
	movq	%rbp, %rdi
	movq	%r14, %rsi
	callq	*%r12
	movl	$16777216, 9344(%rsp)
	movl	$4, %edx
	movq	%rbp, %rdi
	movq	%rbx, %rsi
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	movq	%r15, %rdi
	movq	%rbp, %rsi
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher8finalize
	movq	11416(%rsp), %rax
	movq	%rax, 2104(%rsp)
	movq	11408(%rsp), %rax
	movq	%rax, 2096(%rsp)
	movq	11392(%rsp), %rax
	movq	11400(%rsp), %rcx
	movq	%rcx, 2088(%rsp)
	movq	%rax, 2080(%rsp)
	.p2align	4
.LBB3_17:
	movq	%r13, %rax
	shrq	$3, %rax
	leaq	2(%r13), %rsi
	movq	%rsi, %r15
	shrq	$3, %r15
	leaq	4(%r13), %rdx
	movq	%rdx, %r14
	shrq	$3, %r14
	leaq	6(%r13), %r10
	movq	%r10, %r11
	shrq	$3, %r11
	leaq	8(%r13), %r9
	shrq	$3, %r9
	leaq	9(%r13), %rdi
	movq	%rdi, %rcx
	shrq	$3, %rcx
	movq	%rcx, 8(%rsp)
	movq	%rbp, %r8
	movzbl	2048(%rsp,%rax), %ebp
	movl	%r13d, %r12d
	andb	$6, %r12b
	movl	%r12d, %eax
	xorb	$7, %al
	movl	%ebp, %ebx
	movl	%eax, %ecx
	shrb	%cl, %bl
	addb	%bl, %bl
	andb	$2, %bl
	xorb	$6, %r12b
	movzbl	%r12b, %ecx
	btl	%ecx, %ebp
	setb	%bpl
	movzbl	2048(%rsp,%r15), %r15d
	andb	$6, %sil
	xorb	$7, %sil
	movl	%esi, %ecx
	shrb	%cl, %r15b
	orb	%bl, %bpl
	shlb	$2, %bpl
	addb	%r15b, %r15b
	andb	$2, %r15b
	orb	%bpl, %r15b
	movq	%r8, %rbp
	leaq	3(%r13), %rcx
	movq	%rcx, %rsi
	shrq	$3, %rsi
	notb	%cl
	movzbl	2048(%rsp,%rsi), %esi
	movzbl	%cl, %ecx
	andl	$6, %ecx
	btl	%ecx, %esi
	setb	%sil
	orb	%r15b, %sil
	shlb	$2, %sil
	movzbl	2048(%rsp,%r14), %ebx
	andb	$6, %dl
	xorb	$7, %dl
	movl	%edx, %ecx
	shrb	%cl, %bl
	addb	%bl, %bl
	andb	$2, %bl
	orb	%sil, %bl
	leaq	5(%r13), %rcx
	movq	%rcx, %rdx
	shrq	$3, %rdx
	notb	%cl
	movzbl	2048(%rsp,%rdx), %edx
	movzbl	%cl, %ecx
	andl	$6, %ecx
	btl	%ecx, %edx
	setb	%cl
	orb	%bl, %cl
	addb	%cl, %cl
	andb	$6, %r10b
	xorb	$7, %r10b
	movzbl	2048(%rsp,%r11), %edx
	movzbl	%r10b, %esi
	btl	%esi, %edx
	setb	%dl
	orb	%cl, %dl
	movzbl	%dl, %edx
	leaq	7(%r13), %rcx
	movq	%rcx, %rsi
	shrq	$3, %rsi
	movzbl	2048(%rsp,%rsi), %esi
	notb	%cl
	andb	$6, %cl
	shrq	%cl, %rsi
	andl	$1, %esi
	addl	%esi, %esi
	leal	(%rsi,%rdx,4), %ecx
	movzbl	2048(%rsp,%r9), %edx
	movzbl	%al, %eax
	xorl	%esi, %esi
	btl	%eax, %edx
	setb	%sil
	orl	%ecx, %esi
	movq	8(%rsp), %rax
	movzbl	2048(%rsp,%rax), %eax
	notb	%dil
	movzbl	%dil, %ecx
	andl	$6, %ecx
	xorl	%edx, %edx
	btl	%ecx, %eax
	setb	%dl
	leaq	(%rdx,%rsi,2), %rax
	movq	%rax, (%r8)
	addq	$10, %r13
	addq	$8, %rbp
	cmpq	$240, %r13
	jne	.LBB3_17
	leaq	11400(%rsp), %rdi
	movzbl	2078(%rsp), %eax
	movzbl	2079(%rsp), %ebx
	movzbl	2080(%rsp), %ecx
	shll	$16, %eax
	shll	$8, %ebx
	orl	%eax, %ebx
	orl	%ecx, %ebx
	shll	$8, %ebx
	andl	$67108608, %ebx
	movzbl	2081(%rsp), %ebp
	orl	%ebp, %ebx
	movq	%rbx, 11392(%rsp)
	leaq	4096(%rsp), %r12
	movl	$192, %edx
	movq	%r12, %rsi
	callq	*memcpy@GOTPCREL(%rip)
	movq	%rbx, 568(%rsp)
	movq	%rbx, %r15
	bswapq	%r15
	shlq	$8, %r15
	shll	$24, %ebp
	xorl	%r13d, %r13d
	movq	memset@GOTPCREL(%rip), %rbx
	leaq	112(%rsp), %r14
	movl	%ebp, 60(%rsp)
	movq	%r15, 80(%rsp)
.LBB3_19:
	movq	11400(%rsp,%r13,8), %rcx
	imulq	$176, %r13, %rax
	leaq	(%rsp,%rax), %rdx
	addq	$20540, %rdx
	movq	%rdx, 72(%rsp)
	addq	%rsp, %rax
	addq	$20700, %rax
	movq	%rax, 8(%rsp)
	movl	%r13d, %eax
	shll	$10, %eax
	movq	%rcx, 88(%rsp)
	addl	%ecx, %eax
	bswapl	%eax
	movq	$0, 2048(%rsp)
	movq	%r15, 2056(%rsp)
	movl	$50331648, 2064(%rsp)
	movl	%ebp, 2068(%rsp)
	movl	$0, 2072(%rsp)
	movl	%eax, 2076(%rsp)
	movl	$344, %edx
	movq	%r12, %rdi
	xorl	%esi, %esi
	callq	*%rbx
	movl	$16, %edx
	movq	%r12, %rdi
	movq	%r14, %rsi
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	movl	$32, %edx
	movq	%r12, %rdi
	leaq	2048(%rsp), %rsi
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	movl	$344, %edx
	leaq	576(%rsp), %r14
	movq	%r14, %rdi
	movq	%r12, %rsi
	movq	memcpy@GOTPCREL(%rip), %rbx
	callq	*%rbx
	movl	$16, %edx
	movq	%r14, %rdi
	movq	8(%rsp), %rsi
	movq	%rbx, %r14
	movq	memset@GOTPCREL(%rip), %rbx
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	leaq	10368(%rsp), %rdi
	leaq	576(%rsp), %rsi
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher8finalize
	xorl	%ecx, %ecx
	movq	%r13, 104(%rsp)
	.p2align	4
.LBB3_20:
	movq	10368(%rsp), %rax
	movq	10376(%rsp), %rdx
	movq	%rdx, 8328(%rsp)
	movq	%rax, 8320(%rsp)
	movq	%rcx, %rax
	shlq	$4, %rax
	addq	72(%rsp), %rax
	movq	88(%rsp), %rdi
	btq	%rcx, %rdi
	movq	%rax, %r8
	leaq	8320(%rsp), %rdx
	cmovaeq	%rdx, %r8
	cmovbq	%rdx, %rax
	movl	%ecx, %edx
	movq	(%r8), %rsi
	movq	8(%r8), %r8
	movq	%r8, 3080(%rsp)
	movq	%rsi, 3072(%rsp)
	movq	(%rax), %r8
	movq	8(%rax), %rax
	leaq	3088(%rsp), %rsi
	movq	%rax, 8(%rsi)
	movq	%r8, (%rsi)
	incq	%rcx
	movq	%rdi, %rax
	shrq	%cl, %rax
	movq	%rcx, 64(%rsp)
	movl	%ecx, %esi
	bswapl	%esi
	movb	$9, %cl
	subb	%dl, %cl
	movl	%r13d, %edx
	shll	%cl, %edx
	addl	%edx, %eax
	bswapl	%eax
	movq	$0, 9344(%rsp)
	movq	%r15, 9352(%rsp)
	movl	$50331648, 9360(%rsp)
	movl	%ebp, 9364(%rsp)
	movl	%esi, 9368(%rsp)
	movl	%eax, 9372(%rsp)
	movl	$344, %edx
	movq	%r12, %rdi
	xorl	%esi, %esi
	callq	*%rbx
	movq	112(%rsp), %rax
	movq	120(%rsp), %rcx
	leaq	4296(%rsp), %rdx
	movq	%rax, (%rdx)
	movq	%rcx, 8(%rdx)
	movq	4432(%rsp), %rdi
	addq	$16, %rdi
	movq	%rdi, 4432(%rsp)
	cmpq	$136, %rdi
	jne	.LBB3_22
	movq	4296(%rsp), %rax
	movq	%rax, 24(%rsp)
	movq	4304(%rsp), %rcx
	movq	4312(%rsp), %rdx
	movq	4320(%rsp), %rsi
	movq	4328(%rsp), %rdi
	movq	4336(%rsp), %r8
	movq	4344(%rsp), %r9
	movq	4352(%rsp), %r10
	movq	4360(%rsp), %r11
	movq	4368(%rsp), %rbx
	movq	4376(%rsp), %r12
	movq	4384(%rsp), %r13
	movq	4392(%rsp), %rbp
	movq	4400(%rsp), %r14
	movq	4408(%rsp), %r15
	movq	4416(%rsp), %rax
	movq	%rax, 8(%rsp)
	movq	4424(%rsp), %rax
	movq	%rax, 16(%rsp)
	movq	24(%rsp), %rax
	xorq	%rax, 4096(%rsp)
	xorq	%rcx, 4104(%rsp)
	xorq	%rdx, 4112(%rsp)
	xorq	%rsi, 4120(%rsp)
	xorq	%rdi, 4128(%rsp)
	xorq	%r8, 4136(%rsp)
	xorq	%r9, 4144(%rsp)
	xorq	%r10, 4152(%rsp)
	xorq	%r11, 4160(%rsp)
	xorq	%rbx, 4168(%rsp)
	xorq	%r12, 4176(%rsp)
	leaq	4096(%rsp), %r12
	xorq	%r13, 4184(%rsp)
	xorq	%rbp, 4192(%rsp)
	xorq	%r14, 4200(%rsp)
	movq	memcpy@GOTPCREL(%rip), %r14
	xorq	%r15, 4208(%rsp)
	movq	8(%rsp), %rax
	xorq	%rax, 4216(%rsp)
	movq	16(%rsp), %rax
	xorq	%rax, 4224(%rsp)
	movq	%r12, %rdi
	callq	_RNvCsndc0WgnAaH_9keccak2568keccak_f
	movq	$0, 4432(%rsp)
	xorl	%edi, %edi
.LBB3_22:
	movl	$32, %ebx
	leaq	9344(%rsp), %rbp
	leaq	2048(%rsp), %r15
	jmp	.LBB3_23
	.p2align	4
.LBB3_27:
	subq	%r13, %rbx
	addq	%r13, %rbp
	testq	%rbx, %rbx
	je	.LBB3_28
.LBB3_23:
	movl	$136, %r13d
	subq	%rdi, %r13
	cmpq	%r13, %rbx
	cmovbq	%rbx, %r13
	leaq	(%rdi,%r13), %rsi
	cmpq	%rdi, %rsi
	jb	.LBB3_86
	cmpq	$137, %rsi
	jae	.LBB3_86
	leaq	4296(%rsp), %rax
	addq	%rax, %rdi
	movq	%rbp, %rsi
	movq	%r13, %rdx
	callq	*%r14
	movq	4432(%rsp), %rdi
	addq	%r13, %rdi
	movq	%rdi, 4432(%rsp)
	cmpq	$136, %rdi
	jne	.LBB3_27
	movq	4296(%rsp), %rax
	movq	%rax, 24(%rsp)
	movq	4304(%rsp), %rcx
	movq	4312(%rsp), %rdx
	movq	4320(%rsp), %rsi
	movq	4328(%rsp), %rdi
	movq	4336(%rsp), %r8
	movq	4344(%rsp), %r9
	movq	4352(%rsp), %r10
	movq	4360(%rsp), %r11
	movq	4368(%rsp), %r14
	movq	4376(%rsp), %r15
	movq	4384(%rsp), %r12
	movq	4392(%rsp), %rax
	movq	%rax, 8(%rsp)
	movq	4400(%rsp), %rax
	movq	%rax, 16(%rsp)
	movq	4408(%rsp), %rax
	movq	%rax, 48(%rsp)
	movq	4416(%rsp), %rax
	movq	%rax, 40(%rsp)
	movq	4424(%rsp), %rax
	movq	%rax, 32(%rsp)
	movq	24(%rsp), %rax
	xorq	%rax, 4096(%rsp)
	xorq	%rcx, 4104(%rsp)
	xorq	%rdx, 4112(%rsp)
	xorq	%rsi, 4120(%rsp)
	xorq	%rdi, 4128(%rsp)
	xorq	%r8, 4136(%rsp)
	xorq	%r9, 4144(%rsp)
	xorq	%r10, 4152(%rsp)
	xorq	%r11, 4160(%rsp)
	xorq	%r14, 4168(%rsp)
	movq	memcpy@GOTPCREL(%rip), %r14
	xorq	%r15, 4176(%rsp)
	leaq	2048(%rsp), %r15
	xorq	%r12, 4184(%rsp)
	leaq	4096(%rsp), %r12
	movq	8(%rsp), %rax
	xorq	%rax, 4192(%rsp)
	movq	16(%rsp), %rax
	xorq	%rax, 4200(%rsp)
	movq	48(%rsp), %rax
	xorq	%rax, 4208(%rsp)
	movq	40(%rsp), %rax
	xorq	%rax, 4216(%rsp)
	movq	32(%rsp), %rax
	xorq	%rax, 4224(%rsp)
	movq	%r12, %rdi
	callq	_RNvCsndc0WgnAaH_9keccak2568keccak_f
	movq	$0, 4432(%rsp)
	xorl	%edi, %edi
	jmp	.LBB3_27
	.p2align	4
.LBB3_28:
	movl	$344, %edx
	leaq	576(%rsp), %rdi
	movq	%r12, %rsi
	callq	*%r14
	movl	$32, %ebx
	movq	912(%rsp), %r13
	leaq	3072(%rsp), %rbp
	jmp	.LBB3_29
	.p2align	4
.LBB3_33:
	subq	%r12, %rbx
	addq	%r12, %rbp
	testq	%rbx, %rbx
	je	.LBB3_34
.LBB3_29:
	movl	$136, %r12d
	subq	%r13, %r12
	cmpq	%r12, %rbx
	cmovbq	%rbx, %r12
	leaq	(%r12,%r13), %rsi
	cmpq	%r13, %rsi
	jb	.LBB3_87
	cmpq	$137, %rsi
	jae	.LBB3_87
	leaq	776(%rsp), %rax
	addq	%rax, %r13
	movq	%r13, %rdi
	movq	%rbp, %rsi
	movq	%r12, %rdx
	callq	*%r14
	movq	912(%rsp), %r13
	addq	%r12, %r13
	movq	%r13, 912(%rsp)
	cmpq	$136, %r13
	jne	.LBB3_33
	movq	776(%rsp), %rax
	movq	%rax, 24(%rsp)
	movq	784(%rsp), %rcx
	movq	792(%rsp), %rdx
	movq	800(%rsp), %rsi
	movq	808(%rsp), %rdi
	movq	816(%rsp), %r8
	movq	824(%rsp), %r9
	movq	832(%rsp), %r10
	movq	840(%rsp), %r11
	movq	848(%rsp), %r14
	movq	856(%rsp), %r15
	movq	864(%rsp), %r13
	movq	872(%rsp), %rax
	movq	%rax, 8(%rsp)
	movq	880(%rsp), %rax
	movq	%rax, 16(%rsp)
	movq	888(%rsp), %rax
	movq	%rax, 48(%rsp)
	movq	896(%rsp), %rax
	movq	%rax, 40(%rsp)
	movq	904(%rsp), %rax
	movq	%rax, 32(%rsp)
	movq	24(%rsp), %rax
	xorq	%rax, 576(%rsp)
	xorq	%rcx, 584(%rsp)
	xorq	%rdx, 592(%rsp)
	xorq	%rsi, 600(%rsp)
	xorq	%rdi, 608(%rsp)
	xorq	%r8, 616(%rsp)
	xorq	%r9, 624(%rsp)
	xorq	%r10, 632(%rsp)
	xorq	%r11, 640(%rsp)
	xorq	%r14, 648(%rsp)
	movq	memcpy@GOTPCREL(%rip), %r14
	xorq	%r15, 656(%rsp)
	leaq	2048(%rsp), %r15
	xorq	%r13, 664(%rsp)
	movq	8(%rsp), %rax
	xorq	%rax, 672(%rsp)
	movq	16(%rsp), %rax
	xorq	%rax, 680(%rsp)
	movq	48(%rsp), %rax
	xorq	%rax, 688(%rsp)
	movq	40(%rsp), %rax
	xorq	%rax, 696(%rsp)
	movq	32(%rsp), %rax
	xorq	%rax, 704(%rsp)
	leaq	576(%rsp), %rdi
	callq	_RNvCsndc0WgnAaH_9keccak2568keccak_f
	movq	$0, 912(%rsp)
	xorl	%r13d, %r13d
	jmp	.LBB3_33
	.p2align	4
.LBB3_34:
	movl	$200, %edx
	leaq	4096(%rsp), %r12
	movq	%r12, %rdi
	leaq	576(%rsp), %rsi
	callq	*%r14
	movl	$136, %edx
	cmpq	$137, %r13
	jae	.LBB3_88
	movq	%r15, %rdi
	xorl	%esi, %esi
	movq	memset@GOTPCREL(%rip), %rbx
	callq	*%rbx
	movq	%r15, %rdi
	leaq	776(%rsp), %rsi
	movq	%r13, %rdx
	callq	*%r14
	xorb	$1, 2048(%rsp,%r13)
	xorb	$-128, 2183(%rsp)
	movq	2048(%rsp), %rax
	xorq	%rax, 4096(%rsp)
	movq	2056(%rsp), %rax
	xorq	%rax, 4104(%rsp)
	movq	2064(%rsp), %rax
	xorq	%rax, 4112(%rsp)
	movq	2072(%rsp), %rax
	xorq	%rax, 4120(%rsp)
	movq	2080(%rsp), %rax
	xorq	%rax, 4128(%rsp)
	movq	2088(%rsp), %rax
	xorq	%rax, 4136(%rsp)
	movq	2096(%rsp), %rax
	xorq	%rax, 4144(%rsp)
	movq	2104(%rsp), %rax
	xorq	%rax, 4152(%rsp)
	movq	2112(%rsp), %rax
	xorq	%rax, 4160(%rsp)
	movq	2120(%rsp), %rax
	xorq	%rax, 4168(%rsp)
	movq	2128(%rsp), %rax
	xorq	%rax, 4176(%rsp)
	movq	2136(%rsp), %rax
	xorq	%rax, 4184(%rsp)
	movq	2144(%rsp), %rax
	xorq	%rax, 4192(%rsp)
	movq	2152(%rsp), %rax
	xorq	%rax, 4200(%rsp)
	movq	2160(%rsp), %rax
	xorq	%rax, 4208(%rsp)
	movq	2168(%rsp), %rax
	xorq	%rax, 4216(%rsp)
	movq	2176(%rsp), %rax
	xorq	%rax, 4224(%rsp)
	movq	%r12, %rdi
	callq	_RNvCsndc0WgnAaH_9keccak2568keccak_f
	movq	4096(%rsp), %rax
	movq	4104(%rsp), %rcx
	movq	%rcx, 2056(%rsp)
	movq	%rax, 2048(%rsp)
	movq	%rax, 10368(%rsp)
	movq	%rcx, 10376(%rsp)
	movq	64(%rsp), %rcx
	cmpq	$10, %rcx
	movl	60(%rsp), %ebp
	movq	80(%rsp), %r15
	movq	104(%rsp), %r13
	jne	.LBB3_20
	movq	10368(%rsp), %rax
	movq	10376(%rsp), %rcx
	movq	%r13, %rdx
	shlq	$4, %rdx
	movq	%rax, 20156(%rsp,%rdx)
	movq	%rcx, 20164(%rsp,%rdx)
	incq	%r13
	cmpq	$24, %r13
	leaq	112(%rsp), %r14
	jne	.LBB3_19
	movq	$0, 2048(%rsp)
	movq	%r15, 2056(%rsp)
	movl	$67108864, 2064(%rsp)
	movl	%ebp, 2068(%rsp)
	movq	$0, 2072(%rsp)
	leaq	4096(%rsp), %r12
	xorl	%ebx, %ebx
	movl	$344, %edx
	movq	%r12, %rdi
	xorl	%esi, %esi
	callq	*memset@GOTPCREL(%rip)
	leaq	112(%rsp), %rsi
	movl	$16, %edx
	movq	%r12, %rdi
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	leaq	2048(%rsp), %r13
	movl	$32, %edx
	movq	%r12, %rdi
	movq	%r13, %rsi
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	leaq	576(%rsp), %rbp
	movl	$344, %edx
	movq	%rbp, %rdi
	movq	%r12, %rsi
	callq	*memcpy@GOTPCREL(%rip)
	leaq	20156(%rsp), %rsi
	movl	$384, %edx
	movq	%rbp, %rdi
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	leaq	4096(%rsp), %rdi
	movq	%rbp, %rsi
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher8finalize
	movq	4096(%rsp), %rax
	movq	4104(%rsp), %rcx
	movq	%rcx, 152(%rsp)
	movq	%rax, 144(%rsp)
	movl	$4656, %ecx
	leaq	.Lanon.440213f1c62d8b61420e6860e9721951.8(%rip), %rdx
	leaq	144(%rsp), %r15
	xorl	%esi, %esi
	movq	memcpy@GOTPCREL(%rip), %r14
.LBB3_38:
	addq	$1028, %rcx
	movq	%rcx, 208(%rsp)
	cmpq	$1, %rsi
	setne	%al
	shlb	$3, %al
	addb	$8, %al
	testq	%rsi, %rsi
	movzbl	%al, %ecx
	cmovel	%ebx, %ecx
	movq	568(%rsp), %rdi
	shrq	%cl, %rdi
	movq	(%rdx,%rsi,8), %rcx
	movq	%rdi, %r8
	shrq	%cl, %r8
	movq	$-1, %rax
	movq	%rcx, 160(%rsp)
	shlq	%cl, %rax
	leaq	1(%rsi), %rcx
	movq	%rcx, 200(%rsp)
	notl	%eax
	andl	%eax, %edi
	movq	176(%rsp), %rax
	movl	1024(%rax), %ebx
	movq	%rsi, 96(%rsp)
	movl	%esi, %eax
	bswapl	%eax
	bswapq	%r8
	movq	%rdi, 216(%rsp)
	movl	%edi, %ecx
	bswapl	%ecx
	movl	%eax, 104(%rsp)
	movl	%eax, 2048(%rsp)
	movl	$0, 2052(%rsp)
	movq	%r8, 88(%rsp)
	movq	%r8, 2056(%rsp)
	movl	$117440512, 2064(%rsp)
	movl	%ecx, 60(%rsp)
	movl	%ecx, 2068(%rsp)
	movq	$0, 2072(%rsp)
	movl	$344, %edx
	movq	%r12, %rdi
	xorl	%esi, %esi
	callq	*memset@GOTPCREL(%rip)
	movl	$16, %edx
	movq	%r12, %rdi
	leaq	112(%rsp), %rsi
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	movl	$32, %edx
	movq	%r12, %rdi
	movq	%r13, %rsi
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	movl	$344, %edx
	movq	%rbp, %rdi
	movq	%r12, %rsi
	callq	*%r14
	movl	$16, %edx
	movq	%rbp, %rdi
	movq	%r15, %rsi
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	movl	$344, %edx
	movq	%r12, %rdi
	movq	%rbp, %rsi
	callq	*%r14
	bswapl	%ebx
	movl	%ebx, 2048(%rsp)
	movl	$4, %edx
	movq	%r12, %rdi
	movq	%r13, %rsi
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	movq	%rbp, %rdi
	movq	%r12, %rsi
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher8finalize
	movq	576(%rsp), %rax
	movq	584(%rsp), %rdx
	bswapq	%rax
	bswapq	%rdx
	leaq	577(%rsp), %rsi
	xorl	%edi, %edi
	.p2align	4
.LBB3_39:
	movl	%edi, %ecx
	xorb	$126, %cl
	movq	%rdx, %r8
	shrdq	%cl, %rax, %r8
	movq	%rax, %r9
	shrq	%cl, %r9
	testb	$64, %cl
	cmoveq	%r8, %r9
	leal	2(%rdi), %ecx
	xorb	$126, %cl
	movq	%rdx, %r8
	shrdq	%cl, %rax, %r8
	andb	$3, %r9b
	movb	%r9b, -1(%rsi)
	movq	%rax, %r9
	shrq	%cl, %r9
	testb	$64, %cl
	cmoveq	%r8, %r9
	andb	$3, %r9b
	movb	%r9b, (%rsi)
	addq	$4, %rdi
	addq	$2, %rsi
	cmpq	$128, %rdi
	jne	.LBB3_39
	movzbl	576(%rsp), %eax
	movzbl	577(%rsp), %ecx
	movzbl	578(%rsp), %edx
	movzbl	579(%rsp), %esi
	movzbl	580(%rsp), %edi
	movzbl	581(%rsp), %r8d
	movzbl	582(%rsp), %r9d
	movzbl	583(%rsp), %r10d
	movzbl	584(%rsp), %r11d
	movzbl	585(%rsp), %ebx
	movzbl	586(%rsp), %r15d
	movzbl	587(%rsp), %r12d
	movzbl	588(%rsp), %r13d
	movq	%rax, 8(%rsp)
	movq	%rcx, 24(%rsp)
	addq	%rcx, %rax
	movq	%rdx, 16(%rsp)
	movq	%rsi, 48(%rsp)
	leaq	(%rdx,%rsi), %rcx
	addq	%rax, %rcx
	movq	%rdi, 40(%rsp)
	movq	%r8, 32(%rsp)
	leaq	(%rdi,%r8), %rax
	movq	%r9, 64(%rsp)
	addq	%r9, %rax
	addq	%rcx, %rax
	movq	%r10, 72(%rsp)
	movq	%r11, 80(%rsp)
	leaq	(%r10,%r11), %rcx
	movq	%rbx, 168(%rsp)
	addq	%rbx, %rcx
	movq	%r15, 560(%rsp)
	addq	%r15, %rcx
	addq	%rax, %rcx
	movzbl	589(%rsp), %edx
	movq	%r12, 552(%rsp)
	movq	%r13, 544(%rsp)
	leaq	(%r12,%r13), %rax
	movq	%rdx, 536(%rsp)
	addq	%rdx, %rax
	movzbl	590(%rsp), %edx
	movq	%rdx, 528(%rsp)
	addq	%rdx, %rax
	movzbl	591(%rsp), %edx
	movq	%rdx, 520(%rsp)
	addq	%rdx, %rax
	addq	%rcx, %rax
	movzbl	592(%rsp), %ecx
	movzbl	593(%rsp), %edx
	movzbl	594(%rsp), %esi
	movq	%rcx, 512(%rsp)
	movq	%rdx, 504(%rsp)
	addq	%rdx, %rcx
	movq	%rsi, 496(%rsp)
	addq	%rsi, %rcx
	movzbl	595(%rsp), %edx
	movq	%rdx, 488(%rsp)
	addq	%rdx, %rcx
	movzbl	596(%rsp), %edx
	movq	%rdx, 480(%rsp)
	addq	%rdx, %rcx
	movzbl	597(%rsp), %edx
	movq	%rdx, 472(%rsp)
	addq	%rdx, %rcx
	addq	%rax, %rcx
	movzbl	598(%rsp), %eax
	movzbl	599(%rsp), %edx
	movzbl	600(%rsp), %esi
	movq	%rax, 464(%rsp)
	movq	%rdx, 456(%rsp)
	addq	%rdx, %rax
	movq	%rsi, 448(%rsp)
	addq	%rsi, %rax
	movzbl	601(%rsp), %edx
	movq	%rdx, 440(%rsp)
	addq	%rdx, %rax
	movzbl	602(%rsp), %edx
	movq	%rdx, 432(%rsp)
	addq	%rdx, %rax
	movzbl	603(%rsp), %edx
	movq	%rdx, 424(%rsp)
	addq	%rdx, %rax
	movzbl	604(%rsp), %edx
	movq	%rdx, 416(%rsp)
	addq	%rdx, %rax
	addq	%rcx, %rax
	movzbl	605(%rsp), %ecx
	movzbl	606(%rsp), %edx
	movzbl	607(%rsp), %esi
	movq	%rcx, 408(%rsp)
	movq	%rdx, 400(%rsp)
	addq	%rdx, %rcx
	movq	%rsi, 392(%rsp)
	addq	%rsi, %rcx
	movzbl	608(%rsp), %edx
	movq	%rdx, 384(%rsp)
	addq	%rdx, %rcx
	movzbl	609(%rsp), %edx
	movq	%rdx, 376(%rsp)
	addq	%rdx, %rcx
	movzbl	610(%rsp), %edx
	movq	%rdx, 368(%rsp)
	addq	%rdx, %rcx
	movzbl	611(%rsp), %edx
	movq	%rdx, 360(%rsp)
	addq	%rdx, %rcx
	movzbl	612(%rsp), %edx
	movq	%rdx, 352(%rsp)
	addq	%rdx, %rcx
	addq	%rax, %rcx
	movzbl	613(%rsp), %eax
	movzbl	614(%rsp), %edx
	movzbl	615(%rsp), %esi
	movq	%rax, 344(%rsp)
	movq	%rdx, 336(%rsp)
	addq	%rdx, %rax
	movq	%rsi, 328(%rsp)
	addq	%rsi, %rax
	movzbl	616(%rsp), %edx
	movq	%rdx, 320(%rsp)
	addq	%rdx, %rax
	movzbl	617(%rsp), %edx
	movq	%rdx, 312(%rsp)
	addq	%rdx, %rax
	movzbl	618(%rsp), %edx
	movq	%rdx, 304(%rsp)
	addq	%rdx, %rax
	movzbl	619(%rsp), %edx
	movq	%rdx, 296(%rsp)
	addq	%rdx, %rax
	movzbl	620(%rsp), %edx
	movq	%rdx, 288(%rsp)
	addq	%rdx, %rax
	movzbl	621(%rsp), %edx
	movq	%rdx, 280(%rsp)
	addq	%rdx, %rax
	addq	%rcx, %rax
	movzbl	622(%rsp), %ecx
	movzbl	623(%rsp), %edx
	movzbl	624(%rsp), %esi
	movq	%rcx, 272(%rsp)
	movq	%rdx, 264(%rsp)
	leaq	(%rcx,%rdx), %r12
	movq	%rsi, 256(%rsp)
	addq	%rsi, %r12
	movzbl	625(%rsp), %ecx
	movq	%rcx, 248(%rsp)
	addq	%rcx, %r12
	movzbl	626(%rsp), %ecx
	movq	%rcx, 240(%rsp)
	addq	%rcx, %r12
	movzbl	627(%rsp), %ecx
	movq	%rcx, 232(%rsp)
	addq	%rcx, %r12
	movzbl	628(%rsp), %ecx
	movq	%rcx, 224(%rsp)
	addq	%rcx, %r12
	movzbl	629(%rsp), %ecx
	addq	%rcx, %r12
	movzbl	630(%rsp), %edx
	addq	%rdx, %r12
	movzbl	631(%rsp), %esi
	addq	%rsi, %r12
	addq	%rax, %r12
	movzbl	632(%rsp), %edi
	movzbl	633(%rsp), %r8d
	movzbl	634(%rsp), %r9d
	leaq	(%rdi,%r8), %r13
	addq	%r9, %r13
	movzbl	635(%rsp), %r10d
	addq	%r10, %r13
	movzbl	636(%rsp), %r11d
	addq	%r11, %r13
	movzbl	637(%rsp), %ebx
	addq	%rbx, %r13
	movzbl	638(%rsp), %r15d
	addq	%r15, %r13
	movzbl	639(%rsp), %eax
	addq	%rax, %r13
	addq	%r12, %r13
	cmpq	$128, %r13
	jne	.LBB3_84
	movq	8(%rsp), %r12
	movb	%r12b, 3072(%rsp)
	movq	24(%rsp), %r12
	movb	%r12b, 3073(%rsp)
	movq	16(%rsp), %r12
	movb	%r12b, 3074(%rsp)
	movq	48(%rsp), %r12
	movb	%r12b, 3075(%rsp)
	movq	40(%rsp), %r12
	movb	%r12b, 3076(%rsp)
	movq	32(%rsp), %r12
	movb	%r12b, 3077(%rsp)
	movq	64(%rsp), %r12
	movb	%r12b, 3078(%rsp)
	movq	72(%rsp), %r12
	movb	%r12b, 3079(%rsp)
	movq	80(%rsp), %r12
	movb	%r12b, 3080(%rsp)
	movq	168(%rsp), %r12
	movb	%r12b, 3081(%rsp)
	movq	560(%rsp), %r12
	movb	%r12b, 3082(%rsp)
	movq	552(%rsp), %r12
	movb	%r12b, 3083(%rsp)
	movq	544(%rsp), %r12
	movb	%r12b, 3084(%rsp)
	movq	536(%rsp), %r12
	movb	%r12b, 3085(%rsp)
	movq	528(%rsp), %r12
	movb	%r12b, 3086(%rsp)
	movq	520(%rsp), %r12
	movb	%r12b, 3087(%rsp)
	movq	512(%rsp), %r12
	movb	%r12b, 3088(%rsp)
	movq	504(%rsp), %r12
	movb	%r12b, 3089(%rsp)
	movq	496(%rsp), %r12
	movb	%r12b, 3090(%rsp)
	movq	488(%rsp), %r12
	movb	%r12b, 3091(%rsp)
	movq	480(%rsp), %r12
	movb	%r12b, 3092(%rsp)
	movq	472(%rsp), %r12
	movb	%r12b, 3093(%rsp)
	movq	464(%rsp), %r12
	movb	%r12b, 3094(%rsp)
	movq	456(%rsp), %r12
	movb	%r12b, 3095(%rsp)
	movq	448(%rsp), %r12
	movb	%r12b, 3096(%rsp)
	movq	440(%rsp), %r12
	movb	%r12b, 3097(%rsp)
	movq	432(%rsp), %r12
	movb	%r12b, 3098(%rsp)
	movq	424(%rsp), %r12
	movb	%r12b, 3099(%rsp)
	movq	416(%rsp), %r12
	movb	%r12b, 3100(%rsp)
	movq	408(%rsp), %r12
	movb	%r12b, 3101(%rsp)
	movq	400(%rsp), %r12
	movb	%r12b, 3102(%rsp)
	movq	392(%rsp), %r12
	movb	%r12b, 3103(%rsp)
	movq	384(%rsp), %r12
	movb	%r12b, 3104(%rsp)
	movq	376(%rsp), %r12
	movb	%r12b, 3105(%rsp)
	movq	368(%rsp), %r12
	movb	%r12b, 3106(%rsp)
	movq	360(%rsp), %r12
	movb	%r12b, 3107(%rsp)
	movq	352(%rsp), %r12
	movb	%r12b, 3108(%rsp)
	movq	344(%rsp), %r12
	movb	%r12b, 3109(%rsp)
	movq	336(%rsp), %r12
	movb	%r12b, 3110(%rsp)
	movq	328(%rsp), %r12
	movb	%r12b, 3111(%rsp)
	movq	320(%rsp), %r12
	movb	%r12b, 3112(%rsp)
	movq	312(%rsp), %r12
	movb	%r12b, 3113(%rsp)
	movq	304(%rsp), %r12
	movb	%r12b, 3114(%rsp)
	movq	296(%rsp), %r12
	movb	%r12b, 3115(%rsp)
	movq	288(%rsp), %r12
	movb	%r12b, 3116(%rsp)
	movq	280(%rsp), %r12
	movb	%r12b, 3117(%rsp)
	movq	272(%rsp), %r12
	movb	%r12b, 3118(%rsp)
	movq	264(%rsp), %r12
	movb	%r12b, 3119(%rsp)
	movq	256(%rsp), %r12
	movb	%r12b, 3120(%rsp)
	movq	248(%rsp), %r12
	movb	%r12b, 3121(%rsp)
	movq	240(%rsp), %r12
	movb	%r12b, 3122(%rsp)
	movq	232(%rsp), %r12
	movb	%r12b, 3123(%rsp)
	movq	224(%rsp), %r12
	movb	%r12b, 3124(%rsp)
	movb	%cl, 3125(%rsp)
	movb	%dl, 3126(%rsp)
	movb	%sil, 3127(%rsp)
	movb	%dil, 3128(%rsp)
	movb	%r8b, 3129(%rsp)
	movb	%r9b, 3130(%rsp)
	movb	%r10b, 3131(%rsp)
	movb	%r11b, 3132(%rsp)
	movb	%bl, 3133(%rsp)
	movb	%r15b, 3134(%rsp)
	movb	%al, 3135(%rsp)
	xorl	%eax, %eax
	movq	memset@GOTPCREL(%rip), %rbx
	leaq	4096(%rsp), %r12
	leaq	2048(%rsp), %r13
	jmp	.LBB3_42
.LBB3_60:
	movq	184(%rsp), %rax
	movq	192(%rsp), %rcx
	movq	168(%rsp), %rdx
	movq	%rax, 28280(%rsp,%rdx)
	movq	%rcx, 28288(%rsp,%rdx)
	movq	80(%rsp), %rax
	incq	%rax
	cmpq	$64, %rax
	je	.LBB3_61
.LBB3_42:
	movzbl	3072(%rsp,%rax), %esi
	movq	%rax, 80(%rsp)
	movq	%rax, %rdx
	shlq	$4, %rdx
	movq	176(%rsp), %rcx
	movq	(%rcx,%rdx), %rax
	movq	%rdx, 168(%rsp)
	movq	8(%rcx,%rdx), %rcx
	movq	%rcx, 192(%rsp)
	movq	%rax, 184(%rsp)
	cmpq	$2, %rsi
	ja	.LBB3_60
	movq	80(%rsp), %rax
	shll	$24, %eax
	movl	%eax, 72(%rsp)
	.p2align	4
.LBB3_44:
	movq	184(%rsp), %rax
	movq	192(%rsp), %rcx
	movq	%rcx, 1640(%rsp)
	movq	%rax, 1632(%rsp)
	movq	%rsi, 1648(%rsp)
	movl	104(%rsp), %eax
	movl	%eax, 8320(%rsp)
	movl	$0, 8324(%rsp)
	movq	88(%rsp), %rax
	movq	%rax, 8328(%rsp)
	movl	$0, 8336(%rsp)
	movl	60(%rsp), %eax
	movl	%eax, 8340(%rsp)
	movl	72(%rsp), %eax
	movl	%eax, 8344(%rsp)
	movq	%rsi, 64(%rsp)
	movl	%esi, %eax
	bswapl	%eax
	movl	%eax, 8348(%rsp)
	movl	$344, %edx
	movq	%r12, %rdi
	xorl	%esi, %esi
	callq	*%rbx
	movq	112(%rsp), %rax
	movq	120(%rsp), %rcx
	leaq	4296(%rsp), %rdx
	movq	%rax, (%rdx)
	movq	%rcx, 8(%rdx)
	movq	4432(%rsp), %rdi
	addq	$16, %rdi
	movq	%rdi, 4432(%rsp)
	cmpq	$136, %rdi
	jne	.LBB3_46
	movq	4296(%rsp), %rax
	movq	%rax, 24(%rsp)
	movq	4304(%rsp), %rcx
	movq	4312(%rsp), %rdx
	movq	4320(%rsp), %rsi
	movq	4328(%rsp), %rdi
	movq	4336(%rsp), %r8
	movq	4344(%rsp), %r9
	movq	4352(%rsp), %r10
	movq	4360(%rsp), %r11
	movq	4368(%rsp), %rbx
	movq	4376(%rsp), %r15
	movq	4384(%rsp), %r12
	movq	4392(%rsp), %r14
	movq	4400(%rsp), %rbp
	movq	4408(%rsp), %r13
	movq	4416(%rsp), %rax
	movq	%rax, 8(%rsp)
	movq	4424(%rsp), %rax
	movq	%rax, 16(%rsp)
	movq	24(%rsp), %rax
	xorq	%rax, 4096(%rsp)
	xorq	%rcx, 4104(%rsp)
	xorq	%rdx, 4112(%rsp)
	xorq	%rsi, 4120(%rsp)
	xorq	%rdi, 4128(%rsp)
	xorq	%r8, 4136(%rsp)
	xorq	%r9, 4144(%rsp)
	xorq	%r10, 4152(%rsp)
	xorq	%r11, 4160(%rsp)
	xorq	%rbx, 4168(%rsp)
	xorq	%r15, 4176(%rsp)
	xorq	%r12, 4184(%rsp)
	xorq	%r14, 4192(%rsp)
	movq	memcpy@GOTPCREL(%rip), %r14
	xorq	%rbp, 4200(%rsp)
	leaq	576(%rsp), %rbp
	xorq	%r13, 4208(%rsp)
	leaq	2048(%rsp), %r13
	movq	8(%rsp), %rax
	xorq	%rax, 4216(%rsp)
	movq	16(%rsp), %rax
	xorq	%rax, 4224(%rsp)
	leaq	4096(%rsp), %rdi
	callq	_RNvCsndc0WgnAaH_9keccak2568keccak_f
	movq	$0, 4432(%rsp)
	xorl	%edi, %edi
.LBB3_46:
	incq	64(%rsp)
	movl	$32, %r12d
	leaq	8320(%rsp), %rbx
	jmp	.LBB3_47
	.p2align	4
.LBB3_51:
	subq	%r15, %r12
	addq	%r15, %rbx
	testq	%r12, %r12
	je	.LBB3_52
.LBB3_47:
	movl	$136, %r15d
	subq	%rdi, %r15
	cmpq	%r15, %r12
	cmovbq	%r12, %r15
	leaq	(%r15,%rdi), %rsi
	cmpq	%rdi, %rsi
	jb	.LBB3_86
	cmpq	$137, %rsi
	jae	.LBB3_86
	leaq	4296(%rsp), %rax
	addq	%rax, %rdi
	movq	%rbx, %rsi
	movq	%r15, %rdx
	callq	*%r14
	movq	4432(%rsp), %rdi
	addq	%r15, %rdi
	movq	%rdi, 4432(%rsp)
	cmpq	$136, %rdi
	jne	.LBB3_51
	movq	4296(%rsp), %rax
	movq	%rax, 24(%rsp)
	movq	4304(%rsp), %rcx
	movq	4312(%rsp), %rdx
	movq	4320(%rsp), %rsi
	movq	4328(%rsp), %rdi
	movq	4336(%rsp), %r8
	movq	4344(%rsp), %r9
	movq	4352(%rsp), %r10
	movq	4360(%rsp), %r11
	movq	4368(%rsp), %r14
	movq	4376(%rsp), %r13
	movq	4384(%rsp), %rbp
	movq	4392(%rsp), %rax
	movq	%rax, 8(%rsp)
	movq	4400(%rsp), %rax
	movq	%rax, 16(%rsp)
	movq	4408(%rsp), %rax
	movq	%rax, 48(%rsp)
	movq	4416(%rsp), %rax
	movq	%rax, 40(%rsp)
	movq	4424(%rsp), %rax
	movq	%rax, 32(%rsp)
	movq	24(%rsp), %rax
	xorq	%rax, 4096(%rsp)
	xorq	%rcx, 4104(%rsp)
	xorq	%rdx, 4112(%rsp)
	xorq	%rsi, 4120(%rsp)
	xorq	%rdi, 4128(%rsp)
	xorq	%r8, 4136(%rsp)
	xorq	%r9, 4144(%rsp)
	xorq	%r10, 4152(%rsp)
	xorq	%r11, 4160(%rsp)
	xorq	%r14, 4168(%rsp)
	movq	memcpy@GOTPCREL(%rip), %r14
	xorq	%r13, 4176(%rsp)
	leaq	2048(%rsp), %r13
	xorq	%rbp, 4184(%rsp)
	leaq	576(%rsp), %rbp
	movq	8(%rsp), %rax
	xorq	%rax, 4192(%rsp)
	movq	16(%rsp), %rax
	xorq	%rax, 4200(%rsp)
	movq	48(%rsp), %rax
	xorq	%rax, 4208(%rsp)
	movq	40(%rsp), %rax
	xorq	%rax, 4216(%rsp)
	movq	32(%rsp), %rax
	xorq	%rax, 4224(%rsp)
	leaq	4096(%rsp), %rdi
	callq	_RNvCsndc0WgnAaH_9keccak2568keccak_f
	movq	$0, 4432(%rsp)
	xorl	%edi, %edi
	jmp	.LBB3_51
	.p2align	4
.LBB3_52:
	movl	$344, %edx
	movq	%rbp, %rdi
	leaq	4096(%rsp), %rsi
	callq	*%r14
	movl	$16, %r12d
	movq	912(%rsp), %rdi
	leaq	1632(%rsp), %rbx
	jmp	.LBB3_53
	.p2align	4
.LBB3_57:
	subq	%r15, %r12
	addq	%r15, %rbx
	testq	%r12, %r12
	je	.LBB3_58
.LBB3_53:
	movl	$136, %r15d
	subq	%rdi, %r15
	cmpq	%r15, %r12
	cmovbq	%r12, %r15
	leaq	(%r15,%rdi), %rsi
	cmpq	%rdi, %rsi
	jb	.LBB3_86
	cmpq	$137, %rsi
	jae	.LBB3_86
	leaq	776(%rsp), %rax
	addq	%rax, %rdi
	movq	%rbx, %rsi
	movq	%r15, %rdx
	callq	*%r14
	movq	912(%rsp), %rdi
	addq	%r15, %rdi
	movq	%rdi, 912(%rsp)
	cmpq	$136, %rdi
	jne	.LBB3_57
	movq	776(%rsp), %rax
	movq	%rax, 24(%rsp)
	movq	784(%rsp), %rcx
	movq	792(%rsp), %rdx
	movq	800(%rsp), %rsi
	movq	808(%rsp), %rdi
	movq	816(%rsp), %r8
	movq	824(%rsp), %r9
	movq	832(%rsp), %r10
	movq	840(%rsp), %r11
	movq	848(%rsp), %r14
	movq	856(%rsp), %r13
	movq	864(%rsp), %rbp
	movq	872(%rsp), %rax
	movq	%rax, 8(%rsp)
	movq	880(%rsp), %rax
	movq	%rax, 16(%rsp)
	movq	888(%rsp), %rax
	movq	%rax, 48(%rsp)
	movq	896(%rsp), %rax
	movq	%rax, 40(%rsp)
	movq	904(%rsp), %rax
	movq	%rax, 32(%rsp)
	movq	24(%rsp), %rax
	xorq	%rax, 576(%rsp)
	xorq	%rcx, 584(%rsp)
	xorq	%rdx, 592(%rsp)
	xorq	%rsi, 600(%rsp)
	xorq	%rdi, 608(%rsp)
	xorq	%r8, 616(%rsp)
	xorq	%r9, 624(%rsp)
	xorq	%r10, 632(%rsp)
	xorq	%r11, 640(%rsp)
	xorq	%r14, 648(%rsp)
	movq	memcpy@GOTPCREL(%rip), %r14
	xorq	%r13, 656(%rsp)
	leaq	2048(%rsp), %r13
	xorq	%rbp, 664(%rsp)
	leaq	576(%rsp), %rbp
	movq	8(%rsp), %rax
	xorq	%rax, 672(%rsp)
	movq	16(%rsp), %rax
	xorq	%rax, 680(%rsp)
	movq	48(%rsp), %rax
	xorq	%rax, 688(%rsp)
	movq	40(%rsp), %rax
	xorq	%rax, 696(%rsp)
	movq	32(%rsp), %rax
	xorq	%rax, 704(%rsp)
	movq	%rbp, %rdi
	callq	_RNvCsndc0WgnAaH_9keccak2568keccak_f
	movq	$0, 912(%rsp)
	xorl	%edi, %edi
	jmp	.LBB3_57
	.p2align	4
.LBB3_58:
	movl	$200, %edx
	movq	%r14, %r15
	movq	%rdi, %r14
	leaq	4096(%rsp), %r12
	movq	%r12, %rdi
	movq	%rbp, %rsi
	callq	*%r15
	movq	%r14, %rbx
	cmpq	$137, %r14
	jae	.LBB3_89
	movl	$136, %edx
	movq	%r13, %rdi
	xorl	%esi, %esi
	movq	memset@GOTPCREL(%rip), %r14
	callq	*%r14
	movq	%r13, %rdi
	leaq	776(%rsp), %rsi
	movq	%rbx, %rdx
	callq	*%r15
	xorb	$1, 2048(%rsp,%rbx)
	movq	%r14, %rbx
	xorb	$-128, 2183(%rsp)
	movq	2048(%rsp), %rax
	xorq	%rax, 4096(%rsp)
	movq	2056(%rsp), %rax
	xorq	%rax, 4104(%rsp)
	movq	2064(%rsp), %rax
	xorq	%rax, 4112(%rsp)
	movq	2072(%rsp), %rax
	xorq	%rax, 4120(%rsp)
	movq	2080(%rsp), %rax
	xorq	%rax, 4128(%rsp)
	movq	2088(%rsp), %rax
	xorq	%rax, 4136(%rsp)
	movq	2096(%rsp), %rax
	xorq	%rax, 4144(%rsp)
	movq	2104(%rsp), %rax
	xorq	%rax, 4152(%rsp)
	movq	2112(%rsp), %rax
	xorq	%rax, 4160(%rsp)
	movq	2120(%rsp), %rax
	xorq	%rax, 4168(%rsp)
	movq	2128(%rsp), %rax
	xorq	%rax, 4176(%rsp)
	movq	2136(%rsp), %rax
	xorq	%rax, 4184(%rsp)
	movq	2144(%rsp), %rax
	xorq	%rax, 4192(%rsp)
	movq	2152(%rsp), %rax
	xorq	%rax, 4200(%rsp)
	movq	2160(%rsp), %rax
	xorq	%rax, 4208(%rsp)
	movq	2168(%rsp), %rax
	xorq	%rax, 4216(%rsp)
	movq	2176(%rsp), %rax
	xorq	%rax, 4224(%rsp)
	movq	%r12, %rdi
	callq	_RNvCsndc0WgnAaH_9keccak2568keccak_f
	movq	4120(%rsp), %rax
	movq	%rax, 2072(%rsp)
	movq	4096(%rsp), %rax
	movq	4104(%rsp), %rcx
	movq	%rax, 2048(%rsp)
	movq	%rax, 184(%rsp)
	movq	%rcx, 192(%rsp)
	movq	64(%rsp), %rsi
	cmpq	$3, %rsi
	movq	%r15, %r14
	jne	.LBB3_44
	jmp	.LBB3_60
.LBB3_61:
	movl	104(%rsp), %eax
	movl	%eax, 8320(%rsp)
	movl	$0, 8324(%rsp)
	movq	88(%rsp), %rax
	movq	%rax, 8328(%rsp)
	movl	$16777216, 8336(%rsp)
	movl	60(%rsp), %eax
	movl	%eax, 8340(%rsp)
	movq	$0, 8344(%rsp)
	movl	$344, %edx
	movq	%r12, %rdi
	xorl	%esi, %esi
	callq	*%rbx
	movl	$16, %edx
	movq	%r12, %rdi
	leaq	112(%rsp), %rsi
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	movl	$32, %edx
	movq	%r12, %rdi
	leaq	8320(%rsp), %rsi
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	movl	$344, %edx
	movq	%rbp, %rdi
	movq	%r12, %rsi
	callq	*%r14
	movl	$1024, %edx
	movq	%rbp, %rdi
	leaq	28280(%rsp), %rsi
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	leaq	10368(%rsp), %rdi
	movq	%rbp, %rsi
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher8finalize
	movq	3072(%rsp), %rax
	movq	3080(%rsp), %rcx
	movq	%rax, 2048(%rsp)
	movq	%rcx, 2056(%rsp)
	movq	3088(%rsp), %rax
	movq	%rax, 2064(%rsp)
	movq	3096(%rsp), %rax
	movq	%rax, 2072(%rsp)
	movq	3104(%rsp), %rax
	movq	%rax, 2080(%rsp)
	movq	3112(%rsp), %rax
	movq	%rax, 2088(%rsp)
	movq	3120(%rsp), %rax
	movq	%rax, 2096(%rsp)
	movq	3128(%rsp), %rax
	movq	%rax, 2104(%rsp)
	movq	10368(%rsp), %rax
	movq	10376(%rsp), %rcx
	movq	%rcx, 72(%r13)
	movq	%rax, 64(%r13)
	movl	$80, %edx
	leaq	9344(%rsp), %rdi
	movq	%r13, %rsi
	callq	*%r14
	xorl	%eax, %eax
	movq	96(%rsp), %rsi
	cmpq	$1, %rsi
	setne	%al
	testq	%rsi, %rsi
	leaq	9408(%rsp), %rdx
	movq	(%rdx), %rcx
	movq	8(%rdx), %rdx
	movq	%rdx, 1640(%rsp)
	movq	%rcx, 1632(%rsp)
	leaq	8(,%rax,8), %rcx
	cmoveq	%rsi, %rcx
	movq	160(%rsp), %rax
	leaq	(%rcx,%rax), %rsi
	movq	%rcx, %rdi
	cmpq	%rcx, %rsi
	jb	.LBB3_90
	cmpq	$27, %rsi
	jae	.LBB3_90
	cmpq	$0, 160(%rsp)
	je	.LBB3_91
	shlq	$4, %rdi
	leaq	24764(%rsp), %rax
	addq	%rax, %rdi
	movq	%rdi, 72(%rsp)
	movq	1632(%rsp), %rax
	movq	1640(%rsp), %rcx
	movq	%rcx, 10376(%rsp)
	movq	%rax, 10368(%rsp)
	movq	96(%rsp), %rax
	shll	$24, %eax
	movq	%rax, 96(%rsp)
	xorl	%ecx, %ecx
.LBB3_65:
	movq	10368(%rsp), %rax
	movq	10376(%rsp), %rdx
	movq	%rdx, 8328(%rsp)
	movq	%rcx, %rdx
	movl	$1, %esi
	shlq	%cl, %rsi
	shlq	$4, %rdx
	addq	72(%rsp), %rdx
	movq	216(%rsp), %rdi
	testl	%edi, %esi
	movq	%rdx, %r8
	leaq	8320(%rsp), %rsi
	cmoveq	%rsi, %r8
	cmovneq	%rsi, %rdx
	movq	%rax, 8320(%rsp)
	movq	(%r8), %rax
	movq	8(%r8), %rsi
	movq	%rsi, 3080(%rsp)
	movq	%rax, 3072(%rsp)
	movq	(%rdx), %rax
	movq	8(%rdx), %rsi
	leaq	3088(%rsp), %rdx
	movq	%rsi, 8(%rdx)
	movq	%rax, (%rdx)
	incq	%rcx
	movq	%rdi, %rax
	shrq	%cl, %rax
	movq	%rcx, 64(%rsp)
	bswapl	%ecx
	bswapl	%eax
	movq	96(%rsp), %rdx
	movl	%edx, 9344(%rsp)
	movl	$0, 9348(%rsp)
	movq	88(%rsp), %rdx
	movq	%rdx, 9352(%rsp)
	movq	$33554432, 9360(%rsp)
	movl	%ecx, 9368(%rsp)
	movl	%eax, 9372(%rsp)
	movl	$344, %edx
	movq	%r12, %rdi
	xorl	%esi, %esi
	callq	*%rbx
	movq	112(%rsp), %rax
	movq	120(%rsp), %rcx
	leaq	4296(%rsp), %rdx
	movq	%rax, (%rdx)
	movq	%rcx, 8(%rdx)
	movq	4432(%rsp), %rdi
	addq	$16, %rdi
	movq	%rdi, 4432(%rsp)
	cmpq	$136, %rdi
	jne	.LBB3_67
	movq	4296(%rsp), %rax
	movq	%rax, 24(%rsp)
	movq	4304(%rsp), %rcx
	movq	4312(%rsp), %rdx
	movq	4320(%rsp), %rsi
	movq	4328(%rsp), %rdi
	movq	4336(%rsp), %r8
	movq	4344(%rsp), %r9
	movq	4352(%rsp), %r10
	movq	4360(%rsp), %r11
	movq	4368(%rsp), %rbx
	movq	4376(%rsp), %r14
	movq	4384(%rsp), %r15
	movq	4392(%rsp), %r12
	movq	4400(%rsp), %r13
	movq	4408(%rsp), %rbp
	movq	4416(%rsp), %rax
	movq	%rax, 8(%rsp)
	movq	4424(%rsp), %rax
	movq	%rax, 16(%rsp)
	movq	24(%rsp), %rax
	xorq	%rax, 4096(%rsp)
	xorq	%rcx, 4104(%rsp)
	xorq	%rdx, 4112(%rsp)
	xorq	%rsi, 4120(%rsp)
	xorq	%rdi, 4128(%rsp)
	xorq	%r8, 4136(%rsp)
	xorq	%r9, 4144(%rsp)
	xorq	%r10, 4152(%rsp)
	xorq	%r11, 4160(%rsp)
	xorq	%rbx, 4168(%rsp)
	xorq	%r14, 4176(%rsp)
	movq	memcpy@GOTPCREL(%rip), %r14
	xorq	%r15, 4184(%rsp)
	xorq	%r12, 4192(%rsp)
	leaq	4096(%rsp), %r12
	xorq	%r13, 4200(%rsp)
	xorq	%rbp, 4208(%rsp)
	leaq	576(%rsp), %rbp
	movq	8(%rsp), %rax
	xorq	%rax, 4216(%rsp)
	movq	16(%rsp), %rax
	xorq	%rax, 4224(%rsp)
	movq	%r12, %rdi
	callq	_RNvCsndc0WgnAaH_9keccak2568keccak_f
	movq	$0, 4432(%rsp)
	xorl	%edi, %edi
.LBB3_67:
	movl	$32, %r15d
	leaq	9344(%rsp), %r13
	jmp	.LBB3_68
.LBB3_72:
	subq	%rbx, %r15
	addq	%rbx, %r13
	testq	%r15, %r15
	je	.LBB3_73
.LBB3_68:
	movl	$136, %ebx
	subq	%rdi, %rbx
	cmpq	%rbx, %r15
	cmovbq	%r15, %rbx
	leaq	(%rbx,%rdi), %rsi
	cmpq	%rdi, %rsi
	jb	.LBB3_86
	cmpq	$137, %rsi
	jae	.LBB3_86
	leaq	4296(%rsp), %rax
	addq	%rax, %rdi
	movq	%r13, %rsi
	movq	%rbx, %rdx
	callq	*%r14
	movq	4432(%rsp), %rdi
	addq	%rbx, %rdi
	movq	%rdi, 4432(%rsp)
	cmpq	$136, %rdi
	jne	.LBB3_72
	movq	4296(%rsp), %rax
	movq	%rax, 24(%rsp)
	movq	4304(%rsp), %rcx
	movq	4312(%rsp), %rdx
	movq	4320(%rsp), %rsi
	movq	4328(%rsp), %rdi
	movq	4336(%rsp), %r8
	movq	4344(%rsp), %r9
	movq	4352(%rsp), %r10
	movq	4360(%rsp), %r11
	movq	4368(%rsp), %r14
	movq	4376(%rsp), %r12
	movq	4384(%rsp), %rbp
	movq	4392(%rsp), %rax
	movq	%rax, 8(%rsp)
	movq	4400(%rsp), %rax
	movq	%rax, 16(%rsp)
	movq	4408(%rsp), %rax
	movq	%rax, 48(%rsp)
	movq	4416(%rsp), %rax
	movq	%rax, 40(%rsp)
	movq	4424(%rsp), %rax
	movq	%rax, 32(%rsp)
	movq	24(%rsp), %rax
	xorq	%rax, 4096(%rsp)
	xorq	%rcx, 4104(%rsp)
	xorq	%rdx, 4112(%rsp)
	xorq	%rsi, 4120(%rsp)
	xorq	%rdi, 4128(%rsp)
	xorq	%r8, 4136(%rsp)
	xorq	%r9, 4144(%rsp)
	xorq	%r10, 4152(%rsp)
	xorq	%r11, 4160(%rsp)
	xorq	%r14, 4168(%rsp)
	movq	memcpy@GOTPCREL(%rip), %r14
	xorq	%r12, 4176(%rsp)
	leaq	4096(%rsp), %r12
	xorq	%rbp, 4184(%rsp)
	leaq	576(%rsp), %rbp
	movq	8(%rsp), %rax
	xorq	%rax, 4192(%rsp)
	movq	16(%rsp), %rax
	xorq	%rax, 4200(%rsp)
	movq	48(%rsp), %rax
	xorq	%rax, 4208(%rsp)
	movq	40(%rsp), %rax
	xorq	%rax, 4216(%rsp)
	movq	32(%rsp), %rax
	xorq	%rax, 4224(%rsp)
	movq	%r12, %rdi
	callq	_RNvCsndc0WgnAaH_9keccak2568keccak_f
	movq	$0, 4432(%rsp)
	xorl	%edi, %edi
	jmp	.LBB3_72
.LBB3_73:
	movl	$344, %edx
	movq	%rbp, %rdi
	movq	%r12, %rsi
	callq	*%r14
	movl	$32, %r15d
	movq	912(%rsp), %rbx
	leaq	3072(%rsp), %r13
	jmp	.LBB3_74
.LBB3_78:
	subq	%r12, %r15
	addq	%r12, %r13
	testq	%r15, %r15
	je	.LBB3_79
.LBB3_74:
	movl	$136, %r12d
	subq	%rbx, %r12
	cmpq	%r12, %r15
	cmovbq	%r15, %r12
	leaq	(%r12,%rbx), %rsi
	cmpq	%rbx, %rsi
	jb	.LBB3_92
	cmpq	$137, %rsi
	jae	.LBB3_92
	leaq	776(%rsp), %rax
	addq	%rax, %rbx
	movq	%rbx, %rdi
	movq	%r13, %rsi
	movq	%r12, %rdx
	callq	*%r14
	movq	912(%rsp), %rbx
	addq	%r12, %rbx
	movq	%rbx, 912(%rsp)
	cmpq	$136, %rbx
	jne	.LBB3_78
	movq	776(%rsp), %rax
	movq	%rax, 24(%rsp)
	movq	784(%rsp), %rcx
	movq	792(%rsp), %rdx
	movq	800(%rsp), %rsi
	movq	808(%rsp), %rdi
	movq	816(%rsp), %r8
	movq	824(%rsp), %r9
	movq	832(%rsp), %r10
	movq	840(%rsp), %r11
	movq	848(%rsp), %rbx
	movq	856(%rsp), %r14
	movq	864(%rsp), %rbp
	movq	872(%rsp), %rax
	movq	%rax, 8(%rsp)
	movq	880(%rsp), %rax
	movq	%rax, 16(%rsp)
	movq	888(%rsp), %rax
	movq	%rax, 48(%rsp)
	movq	896(%rsp), %rax
	movq	%rax, 40(%rsp)
	movq	904(%rsp), %rax
	movq	%rax, 32(%rsp)
	movq	24(%rsp), %rax
	xorq	%rax, 576(%rsp)
	xorq	%rcx, 584(%rsp)
	xorq	%rdx, 592(%rsp)
	xorq	%rsi, 600(%rsp)
	xorq	%rdi, 608(%rsp)
	xorq	%r8, 616(%rsp)
	xorq	%r9, 624(%rsp)
	xorq	%r10, 632(%rsp)
	xorq	%r11, 640(%rsp)
	xorq	%rbx, 648(%rsp)
	xorq	%r14, 656(%rsp)
	movq	memcpy@GOTPCREL(%rip), %r14
	xorq	%rbp, 664(%rsp)
	leaq	576(%rsp), %rbp
	movq	8(%rsp), %rax
	xorq	%rax, 672(%rsp)
	movq	16(%rsp), %rax
	xorq	%rax, 680(%rsp)
	movq	48(%rsp), %rax
	xorq	%rax, 688(%rsp)
	movq	40(%rsp), %rax
	xorq	%rax, 696(%rsp)
	movq	32(%rsp), %rax
	xorq	%rax, 704(%rsp)
	movq	%rbp, %rdi
	callq	_RNvCsndc0WgnAaH_9keccak2568keccak_f
	movq	$0, 912(%rsp)
	xorl	%ebx, %ebx
	jmp	.LBB3_78
.LBB3_79:
	movl	$200, %edx
	leaq	4096(%rsp), %r12
	movq	%r12, %rdi
	movq	%rbp, %rsi
	callq	*%r14
	cmpq	$137, %rbx
	jae	.LBB3_89
	movl	$136, %edx
	leaq	2048(%rsp), %r13
	movq	%r13, %rdi
	xorl	%esi, %esi
	movq	memset@GOTPCREL(%rip), %r15
	callq	*%r15
	movq	%r13, %rdi
	leaq	776(%rsp), %rsi
	movq	%rbx, %rdx
	callq	*%r14
	xorb	$1, 2048(%rsp,%rbx)
	movq	%r15, %rbx
	xorb	$-128, 2183(%rsp)
	movq	2048(%rsp), %rax
	xorq	%rax, 4096(%rsp)
	movq	2056(%rsp), %rax
	xorq	%rax, 4104(%rsp)
	movq	2064(%rsp), %rax
	xorq	%rax, 4112(%rsp)
	movq	2072(%rsp), %rax
	xorq	%rax, 4120(%rsp)
	movq	2080(%rsp), %rax
	xorq	%rax, 4128(%rsp)
	movq	2088(%rsp), %rax
	xorq	%rax, 4136(%rsp)
	movq	2096(%rsp), %rax
	xorq	%rax, 4144(%rsp)
	movq	2104(%rsp), %rax
	xorq	%rax, 4152(%rsp)
	movq	2112(%rsp), %rax
	xorq	%rax, 4160(%rsp)
	movq	2120(%rsp), %rax
	xorq	%rax, 4168(%rsp)
	movq	2128(%rsp), %rax
	xorq	%rax, 4176(%rsp)
	movq	2136(%rsp), %rax
	xorq	%rax, 4184(%rsp)
	movq	2144(%rsp), %rax
	xorq	%rax, 4192(%rsp)
	movq	2152(%rsp), %rax
	xorq	%rax, 4200(%rsp)
	movq	2160(%rsp), %rax
	xorq	%rax, 4208(%rsp)
	movq	2168(%rsp), %rax
	xorq	%rax, 4216(%rsp)
	movq	2176(%rsp), %rax
	xorq	%rax, 4224(%rsp)
	movq	%r12, %rdi
	callq	_RNvCsndc0WgnAaH_9keccak2568keccak_f
	movq	4096(%rsp), %rax
	movq	4104(%rsp), %rcx
	movq	%rcx, 2056(%rsp)
	movq	%rax, 2048(%rsp)
	movq	%rax, 10368(%rsp)
	movq	%rcx, 10376(%rsp)
	movq	64(%rsp), %rcx
	cmpq	160(%rsp), %rcx
	jne	.LBB3_65
	movq	10368(%rsp), %rax
	movq	10376(%rsp), %rcx
	jmp	.LBB3_82
.LBB3_91:
	movq	1632(%rsp), %rax
	movq	1640(%rsp), %rcx
.LBB3_82:
	movq	%rcx, 4104(%rsp)
	movq	%rax, 4096(%rsp)
	movq	4096(%rsp), %rax
	movq	4104(%rsp), %rcx
	movq	%rcx, 152(%rsp)
	movq	%rax, 144(%rsp)
	movq	208(%rsp), %rcx
	leaq	(%rsp,%rcx), %rax
	addq	$20540, %rax
	movq	%rax, 176(%rsp)
	cmpq	$7740, %rcx
	movl	$0, %ebx
	leaq	.Lanon.440213f1c62d8b61420e6860e9721951.8(%rip), %rdx
	leaq	144(%rsp), %r15
	movq	200(%rsp), %rsi
	jne	.LBB3_38
	movq	144(%rsp), %rcx
	movq	152(%rsp), %rdx
	xorq	136(%rsp), %rdx
	xorq	128(%rsp), %rcx
	xorl	%eax, %eax
	orq	%rdx, %rcx
	sete	%al
	jmp	.LBB3_85
.LBB3_86:
	movl	$136, %edx
	callq	_RNvNtNtCs1gUZZmupoa8_4core5slice5index16slice_index_fail
.LBB3_87:
	movl	$136, %edx
	movq	%r13, %rdi
	callq	_RNvNtNtCs1gUZZmupoa8_4core5slice5index16slice_index_fail
.LBB3_88:
	xorl	%edi, %edi
	movq	%r13, %rsi
	callq	_RNvNtNtCs1gUZZmupoa8_4core5slice5index16slice_index_fail
.LBB3_84:
	xorl	%eax, %eax
.LBB3_85:
	addq	$29336, %rsp
	.cfi_def_cfa_offset 56
	popq	%rbx
	.cfi_def_cfa_offset 48
	popq	%r12
	.cfi_def_cfa_offset 40
	popq	%r13
	.cfi_def_cfa_offset 32
	popq	%r14
	.cfi_def_cfa_offset 24
	popq	%r15
	.cfi_def_cfa_offset 16
	popq	%rbp
	.cfi_def_cfa_offset 8
	retq
.LBB3_89:
	.cfi_def_cfa_offset 29392
	movl	$136, %edx
	xorl	%edi, %edi
	movq	%rbx, %rsi
	callq	_RNvNtNtCs1gUZZmupoa8_4core5slice5index16slice_index_fail
.LBB3_92:
	movl	$136, %edx
	movq	%rbx, %rdi
	callq	_RNvNtNtCs1gUZZmupoa8_4core5slice5index16slice_index_fail
.LBB3_90:
	movl	$26, %edx
	callq	_RNvNtNtCs1gUZZmupoa8_4core5slice5index16slice_index_fail
.Lfunc_end3:
	.size	sphincs_verify, .Lfunc_end3-sphincs_verify
	.cfi_endproc

	.section	.text.xmss_verify,"ax",@progbits
	.globl	xmss_verify
	.p2align	4
	.type	xmss_verify,@function
xmss_verify:
.Lfunc_begin4:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	pushq	%r15
	.cfi_def_cfa_offset 24
	pushq	%r14
	.cfi_def_cfa_offset 32
	pushq	%r13
	.cfi_def_cfa_offset 40
	pushq	%r12
	.cfi_def_cfa_offset 48
	pushq	%rbx
	.cfi_def_cfa_offset 56
	subq	$4096, %rsp
	.cfi_adjust_cfa_offset 4096
	movq	$0, (%rsp)
	subq	$1640, %rsp
	.cfi_def_cfa_offset 5792
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	%rdi, %r14
	leaq	932(%rsp), %rbx
	xorl	%r15d, %r15d
	movl	$2400, %edx
	movq	%rbx, %rdi
	xorl	%esi, %esi
	callq	*memset@GOTPCREL(%rip)
	movq	1024(%r14), %rax
	movq	1032(%r14), %rcx
	movq	1040(%r14), %rdx
	movq	1048(%r14), %rsi
	movq	1056(%r14), %rdi
	movq	%rdi, 128(%rsp)
	movq	1064(%r14), %rdi
	movq	%rdi, 136(%rsp)
	movq	1072(%r14), %rdi
	movq	%rdi, 144(%rsp)
	movq	1080(%r14), %rdi
	movq	%rdi, 152(%rsp)
	movq	1088(%r14), %r13
	movl	%r13d, %ebp
	movl	%r13d, 928(%rsp)
	.p2align	4
.LBB4_1:
	movq	1096(%r14,%r15,8), %rdi
	movq	%rdi, 932(%rsp,%r15,8)
	movq	1104(%r14,%r15,8), %rdi
	movq	%rdi, 940(%rsp,%r15,8)
	movq	1112(%r14,%r15,8), %rdi
	movq	%rdi, 948(%rsp,%r15,8)
	movq	1120(%r14,%r15,8), %rdi
	movq	%rdi, 956(%rsp,%r15,8)
	movq	1128(%r14,%r15,8), %rdi
	movq	%rdi, 964(%rsp,%r15,8)
	movq	1136(%r14,%r15,8), %rdi
	movq	%rdi, 972(%rsp,%r15,8)
	addq	$6, %r15
	cmpq	$300, %r15
	jne	.LBB4_1
	leaq	32(%rsp), %r15
	movq	%rdx, 32(%rsp)
	movq	%rsi, 40(%rsp)
	movq	%rax, 16(%rsp)
	movq	%rcx, 24(%rsp)
	movq	%rbx, 160(%rsp)
	movq	$2400, 168(%rsp)
	leaq	3332(%rsp), %r12
	leaq	160(%rsp), %rbx
	movq	%r12, %rdi
	movq	%rbx, %rsi
	callq	_RNvMs_NtCs7Pyp4CbMBld_9lean_xmss6schemeNtB4_14LayerSignature4read
	leaq	4532(%rsp), %rdi
	movq	%rbx, %rsi
	callq	_RNvMs_NtCs7Pyp4CbMBld_9lean_xmss6schemeNtB4_14LayerSignature4read
	movl	%r13d, 5732(%rsp)
	leaq	4516(%rsp), %rax
	leaq	3588(%rsp), %r10
	leaq	160(%rsp), %rdi
	leaq	128(%rsp), %r8
	movl	$32, %r9d
	movq	%r15, %rsi
	xorl	%edx, %edx
	movl	%r13d, %ecx
	pushq	%r10
	.cfi_adjust_cfa_offset 8
	pushq	%rax
	.cfi_adjust_cfa_offset 8
	callq	_RNvNtCs7Pyp4CbMBld_9lean_xmss4wots9wots_leaf
	addq	$16, %rsp
	.cfi_adjust_cfa_offset -16
	cmpb	$1, 160(%rsp)
	jne	.LBB4_10
	movq	%r13, 56(%rsp)
	leaq	161(%rsp), %rsi
	leaq	510(%rsp), %rdi
	movl	$74, %edx
	callq	*memcpy@GOTPCREL(%rip)
	movq	%rbp, %rbx
	xorl	%ebp, %ebp
	leaq	160(%rsp), %r15
	.p2align	4
.LBB4_4:
	leaq	568(%rsp), %r14
	movq	(%r14), %rax
	movq	8(%r14), %rcx
	movq	%rcx, 104(%rsp)
	movq	%rax, 96(%rsp)
	movl	$1, %eax
	movl	%ebp, %ecx
	shlq	%cl, %rax
	testl	%ebx, %eax
	movq	%r12, %rax
	leaq	96(%rsp), %rcx
	cmoveq	%rcx, %rax
	cmoveq	%r12, %rcx
	movq	(%rax), %rdx
	movq	8(%rax), %rax
	movq	%rax, 72(%rsp)
	movq	%rdx, 64(%rsp)
	movq	(%rcx), %rax
	movq	8(%rcx), %rcx
	leaq	80(%rsp), %rsi
	movq	%rcx, 8(%rsi)
	incq	%rbp
	movq	%rbx, %rdx
	movl	%ebp, %ecx
	shrq	%cl, %rdx
	movq	%rax, (%rsi)
	movl	%edx, (%rsp)
	movl	%ebp, %eax
	shrl	$16, %eax
	movb	%al, 6(%rsp)
	movw	%bp, 4(%rsp)
	movb	$3, 7(%rsp)
	movq	$0, 8(%rsp)
	movl	$344, %edx
	movq	%r15, %rdi
	xorl	%esi, %esi
	callq	*memset@GOTPCREL(%rip)
	movl	$16, %edx
	movq	%r15, %rdi
	leaq	32(%rsp), %rsi
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	movl	$16, %edx
	movq	%r15, %rdi
	movq	%rsp, %rsi
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	movl	$344, %edx
	leaq	584(%rsp), %r13
	movq	%r13, %rdi
	movq	%r15, %rsi
	callq	*memcpy@GOTPCREL(%rip)
	movl	$32, %edx
	movq	%r13, %rdi
	leaq	64(%rsp), %rsi
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	movq	%r15, %rdi
	movq	%r13, %rsi
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher8finalize
	movq	160(%rsp), %rax
	movq	168(%rsp), %rcx
	movq	%rcx, 8(%r14)
	movq	%rax, (%r14)
	addq	$16, %r12
	cmpq	$16, %rbp
	jne	.LBB4_4
	movq	56(%rsp), %rbx
	shrl	$16, %ebx
	leaq	5716(%rsp), %rax
	leaq	4788(%rsp), %r10
	leaq	160(%rsp), %rdi
	movl	$1, %r12d
	movl	$1, %edx
	movl	$16, %r9d
	leaq	32(%rsp), %rsi
	leaq	568(%rsp), %r8
	movl	%ebx, %ecx
	pushq	%r10
	.cfi_adjust_cfa_offset 8
	pushq	%rax
	.cfi_adjust_cfa_offset 8
	callq	_RNvNtCs7Pyp4CbMBld_9lean_xmss4wots9wots_leaf
	addq	$16, %rsp
	.cfi_adjust_cfa_offset -16
	cmpb	$1, 160(%rsp)
	jne	.LBB4_10
	movq	219(%rsp), %rcx
	movq	227(%rsp), %rdx
	movl	%ebx, %ebx
	leaq	160(%rsp), %r15
	leaq	584(%rsp), %rbp
	leaq	96(%rsp), %r13
	leaq	4532(%rsp), %r14
	.p2align	4
.LBB4_7:
	movq	%rcx, 96(%rsp)
	movq	%rdx, 104(%rsp)
	leal	-1(%r12), %ecx
	movl	$1, %eax
	shlq	%cl, %rax
	testl	%ebx, %eax
	movq	%r14, %rax
	cmoveq	%r13, %rax
	movq	%r13, %rcx
	cmoveq	%r14, %rcx
	movq	(%rax), %rdx
	movq	8(%rax), %rax
	movq	%rax, 72(%rsp)
	movq	%rdx, 64(%rsp)
	movq	(%rcx), %rax
	movq	8(%rcx), %rcx
	leaq	80(%rsp), %rdx
	movq	%rcx, 8(%rdx)
	movq	%rax, (%rdx)
	movq	%rbx, %rax
	movl	%r12d, %ecx
	shrq	%cl, %rax
	movl	%r12d, %ecx
	orl	$8388608, %ecx
	movl	%eax, (%rsp)
	shrl	$16, %ecx
	movb	%cl, 6(%rsp)
	movw	%r12w, 4(%rsp)
	movb	$3, 7(%rsp)
	movq	$0, 8(%rsp)
	movl	$344, %edx
	movq	%r15, %rdi
	xorl	%esi, %esi
	callq	*memset@GOTPCREL(%rip)
	movl	$16, %edx
	movq	%r15, %rdi
	leaq	32(%rsp), %rsi
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	movl	$16, %edx
	movq	%r15, %rdi
	movq	%rsp, %rsi
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	movl	$344, %edx
	movq	%rbp, %rdi
	movq	%r15, %rsi
	callq	*memcpy@GOTPCREL(%rip)
	movl	$32, %edx
	movq	%rbp, %rdi
	leaq	64(%rsp), %rsi
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	movq	%r15, %rdi
	movq	%rbp, %rsi
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher8finalize
	movq	160(%rsp), %rcx
	movq	168(%rsp), %rdx
	incq	%r12
	addq	$16, %r14
	cmpq	$17, %r12
	jne	.LBB4_7
	xorq	16(%rsp), %rcx
	xorq	24(%rsp), %rdx
	xorl	%eax, %eax
	orq	%rcx, %rdx
	sete	%al
	jmp	.LBB4_9
.LBB4_10:
	xorl	%eax, %eax
.LBB4_9:
	addq	$5736, %rsp
	.cfi_def_cfa_offset 56
	popq	%rbx
	.cfi_def_cfa_offset 48
	popq	%r12
	.cfi_def_cfa_offset 40
	popq	%r13
	.cfi_def_cfa_offset 32
	popq	%r14
	.cfi_def_cfa_offset 24
	popq	%r15
	.cfi_def_cfa_offset 16
	popq	%rbp
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end4:
	.size	xmss_verify, .Lfunc_end4-xmss_verify
	.cfi_endproc

	.section	.text.unlikely._RNvNtCs1gUZZmupoa8_4core9panicking9panic_fmt,"ax",@progbits
	.p2align	4
	.type	_RNvNtCs1gUZZmupoa8_4core9panicking9panic_fmt,@function
_RNvNtCs1gUZZmupoa8_4core9panicking9panic_fmt:
.Lfunc_begin5:
	.file	1 "/rustc/58cf8f9c35b355199727627d07ae34a4e2846d67" "library/core/src/panicking.rs"
	.loc	1 60 0
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset %rbp, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register %rbp
.Ltmp0:
	.loc	1 80 14 prologue_end
	callq	_RNvCs5fGHjzWXRav_7___rustc17rust_begin_unwind
.Ltmp1:
.Lfunc_end5:
	.size	_RNvNtCs1gUZZmupoa8_4core9panicking9panic_fmt, .Lfunc_end5-_RNvNtCs1gUZZmupoa8_4core9panicking9panic_fmt
	.cfi_endproc

	.section	.text.unlikely._RNvNtNtCs1gUZZmupoa8_4core5slice5index16slice_index_fail,"ax",@progbits
	.p2align	4
	.type	_RNvNtNtCs1gUZZmupoa8_4core5slice5index16slice_index_fail,@function
_RNvNtNtCs1gUZZmupoa8_4core5slice5index16slice_index_fail:
.Lfunc_begin6:
	.file	2 "/rustc/58cf8f9c35b355199727627d07ae34a4e2846d67" "library/core/src/slice/index.rs"
	.loc	2 39 0
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset %rbp, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register %rbp
.Ltmp2:
	.file	3 "/rustc/58cf8f9c35b355199727627d07ae34a4e2846d67" "library/core/src/panic.rs"
	.loc	3 177 9 prologue_end
	callq	_RNvNtCs1gUZZmupoa8_4core9panicking9panic_fmt
.Ltmp3:
.Lfunc_end6:
	.size	_RNvNtNtCs1gUZZmupoa8_4core5slice5index16slice_index_fail, .Lfunc_end6-_RNvNtNtCs1gUZZmupoa8_4core5slice5index16slice_index_fail
	.cfi_endproc

	.section	.text.unlikely._RNvNtCs1gUZZmupoa8_4core9panicking5panic,"ax",@progbits
	.p2align	4
	.type	_RNvNtCs1gUZZmupoa8_4core9panicking5panic,@function
_RNvNtCs1gUZZmupoa8_4core9panicking5panic:
.Lfunc_begin7:
	.loc	1 138 0
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset %rbp, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register %rbp
.Ltmp4:
	.loc	1 150 5 prologue_end
	callq	_RNvNtCs1gUZZmupoa8_4core9panicking9panic_fmt
.Ltmp5:
.Lfunc_end7:
	.size	_RNvNtCs1gUZZmupoa8_4core9panicking5panic, .Lfunc_end7-_RNvNtCs1gUZZmupoa8_4core9panicking5panic
	.cfi_endproc

	.section	.text.unlikely._RNvNtCs1gUZZmupoa8_4core6option13unwrap_failed,"ax",@progbits
	.p2align	4
	.type	_RNvNtCs1gUZZmupoa8_4core6option13unwrap_failed,@function
_RNvNtCs1gUZZmupoa8_4core6option13unwrap_failed:
.Lfunc_begin8:
	.file	4 "/rustc/58cf8f9c35b355199727627d07ae34a4e2846d67" "library/core/src/option.rs"
	.loc	4 2247 0
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset %rbp, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register %rbp
.Ltmp6:
	.loc	4 2248 5 prologue_end
	callq	_RNvNtCs1gUZZmupoa8_4core9panicking5panic
.Ltmp7:
.Lfunc_end8:
	.size	_RNvNtCs1gUZZmupoa8_4core6option13unwrap_failed, .Lfunc_end8-_RNvNtCs1gUZZmupoa8_4core6option13unwrap_failed
	.cfi_endproc

	.section	.text._RNvCsndc0WgnAaH_9keccak2568keccak_f,"ax",@progbits
	.p2align	4
	.type	_RNvCsndc0WgnAaH_9keccak2568keccak_f,@function
_RNvCsndc0WgnAaH_9keccak2568keccak_f:
.Lfunc_begin9:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	pushq	%r15
	.cfi_def_cfa_offset 24
	pushq	%r14
	.cfi_def_cfa_offset 32
	pushq	%r13
	.cfi_def_cfa_offset 40
	pushq	%r12
	.cfi_def_cfa_offset 48
	pushq	%rbx
	.cfi_def_cfa_offset 56
	subq	$112, %rsp
	.cfi_def_cfa_offset 168
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	(%rdi), %rdx
	movq	8(%rdi), %rsi
	movq	40(%rdi), %rax
	movq	80(%rdi), %r14
	movq	120(%rdi), %rcx
	movq	%rax, -88(%rsp)
	movq	%rdx, -40(%rsp)
	xorq	%rdx, %rax
	movq	%r14, -96(%rsp)
	movq	%rcx, 40(%rsp)
	xorq	%rcx, %r14
	xorq	%rax, %r14
	movq	48(%rdi), %rax
	movq	88(%rdi), %r9
	movq	128(%rdi), %rcx
	movq	%rax, -120(%rsp)
	movq	%rsi, 16(%rsp)
	xorq	%rsi, %rax
	movq	%r9, -72(%rsp)
	movq	%rcx, -48(%rsp)
	xorq	%rcx, %r9
	xorq	%rax, %r9
	movq	16(%rdi), %rcx
	movq	56(%rdi), %rax
	movq	96(%rdi), %rsi
	movq	%rax, -112(%rsp)
	movq	%rcx, 24(%rsp)
	xorq	%rcx, %rax
	movq	136(%rdi), %rcx
	movq	%rsi, %r13
	movq	%rcx, -56(%rsp)
	xorq	%rcx, %r13
	xorq	%rax, %r13
	movq	24(%rdi), %r11
	movq	64(%rdi), %rax
	movq	%rax, 32(%rsp)
	xorq	%r11, %rax
	movq	104(%rdi), %rbp
	movq	144(%rdi), %r8
	movq	%rbp, -64(%rsp)
	xorq	%r8, %rbp
	xorq	%rax, %rbp
	movq	32(%rdi), %rcx
	movq	72(%rdi), %rax
	movq	%rax, -80(%rsp)
	movq	%rcx, %r15
	xorq	%rcx, %rax
	movq	112(%rdi), %rcx
	movq	152(%rdi), %rdx
	movq	%rcx, -104(%rsp)
	movq	%rdx, -128(%rsp)
	xorq	%rdx, %rcx
	xorq	%rax, %rcx
	movq	160(%rdi), %r10
	xorq	%r10, %r14
	movq	168(%rdi), %rax
	movq	%rax, -16(%rsp)
	xorq	%rax, %r9
	movq	176(%rdi), %rax
	xorq	%rax, %r13
	movq	184(%rdi), %rdx
	movq	%rdx, -24(%rsp)
	xorq	%rdx, %rbp
	movq	%rdi, 88(%rsp)
	movq	192(%rdi), %rbx
	xorq	%rbx, %rcx
	movl	$8, %edi
	.p2align	4
.LBB9_1:
	movq	%rdi, 64(%rsp)
	movq	%rbp, %rdi
	rolq	%rdi
	xorq	%r9, %rdi
	movq	%rdi, %r12
	movq	%rdi, 48(%rsp)
	rolq	%r9
	xorq	%rcx, %r9
	movq	%r9, %rdx
	movq	%r13, %rdi
	rolq	%rdi
	xorq	%r14, %rdi
	movq	%rdi, -32(%rsp)
	rolq	%rcx
	rolq	%r14
	xorq	%r13, %rcx
	xorq	%rbp, %r14
	xorq	%r14, %rbx
	xorq	%r14, -80(%rsp)
	xorq	%r14, -128(%rsp)
	xorq	%r14, %r15
	movq	%r15, -8(%rsp)
	xorq	-104(%rsp), %r14
	xorq	%r12, %rsi
	rolq	$43, %rsi
	xorq	%rcx, %r8
	movq	-120(%rsp), %r13
	xorq	%rdi, %r13
	rolq	$21, %r8
	rolq	$44, %r13
	movq	-40(%rsp), %r9
	movq	%rdx, %r15
	xorq	%rdx, %r9
	rolq	$14, %rbx
	movq	%rsi, %rdi
	notq	%rdi
	andq	%r8, %rdi
	xorq	%r13, %rdi
	movq	%rdi, 80(%rsp)
	movq	%r9, %rbp
	notq	%rbp
	andq	%r13, %rbp
	notq	%r13
	andq	%rsi, %r13
	movq	%rbx, %r12
	notq	%r12
	andq	%r9, %r12
	xorq	%r8, %r12
	movq	%r12, 8(%rsp)
	notq	%r8
	andq	%rbx, %r8
	xorq	%rsi, %r8
	movq	%r8, 72(%rsp)
	xorq	%rbx, %rbp
	movq	%rbp, (%rsp)
	leaq	.Lanon.5ef9b7c546f4dc64388b910df55ec241.1(%rip), %rdx
	movq	64(%rsp), %rsi
	xorq	-8(%rsi,%rdx), %r13
	xorq	%r9, %r13
	movq	%r13, 104(%rsp)
	xorq	%rcx, %r11
	rolq	$28, %r11
	movq	-96(%rsp), %rbp
	xorq	%r15, %rbp
	rolq	$3, %rbp
	movq	-48(%rsp), %rdx
	movq	-32(%rsp), %r9
	xorq	%r9, %rdx
	rolq	$45, %rdx
	movq	-80(%rsp), %rsi
	rolq	$20, %rsi
	movq	48(%rsp), %r12
	xorq	%r12, %rax
	rolq	$61, %rax
	movq	%rsi, %r8
	movq	%rsi, %rbx
	movq	%rsi, -80(%rsp)
	notq	%r8
	movq	%rdx, %rsi
	notq	%rsi
	andq	%rbp, %r8
	andq	%rax, %rsi
	xorq	%rbp, %rsi
	movq	%rsi, -96(%rsp)
	notq	%rbp
	movq	%rax, %rsi
	notq	%rsi
	andq	%r11, %rsi
	andq	%rdx, %rbp
	movq	%rbp, 56(%rsp)
	xorq	%rdx, %rsi
	movq	%rsi, -104(%rsp)
	xorq	%r11, %r8
	movq	%r8, -48(%rsp)
	notq	%r11
	andq	%rbx, %r11
	movq	-112(%rsp), %rdx
	xorq	%r12, %rdx
	rolq	$6, %rdx
	xorq	%rax, %r11
	movq	%r11, -120(%rsp)
	movq	-64(%rsp), %r8
	xorq	%rcx, %r8
	rolq	$25, %r8
	movq	%r9, %rsi
	movq	16(%rsp), %rbx
	xorq	%r9, %rbx
	movq	%r15, 96(%rsp)
	xorq	%r15, %r10
	rolq	%rbx
	rolq	$18, %r10
	movq	-128(%rsp), %r13
	rolq	$8, %r13
	movq	%rdx, %rax
	notq	%rax
	andq	%r8, %rax
	xorq	%rbx, %rax
	movq	%rax, -64(%rsp)
	movq	%r13, %rax
	notq	%rax
	andq	%r10, %rax
	movq	%rax, -112(%rsp)
	movq	%r10, %rax
	notq	%rax
	andq	%rbx, %rax
	movq	%rax, -128(%rsp)
	notq	%rbx
	andq	%rdx, %rbx
	xorq	%r10, %rbx
	movq	%rbx, -40(%rsp)
	movq	-56(%rsp), %r9
	xorq	%r12, %r9
	movq	-88(%rsp), %rax
	xorq	%r15, %rax
	rolq	$15, %r9
	rolq	$36, %rax
	movq	-72(%rsp), %r10
	xorq	%rsi, %r10
	movq	-24(%rsp), %r11
	xorq	%rcx, %r11
	rolq	$10, %r10
	rolq	$56, %r11
	movq	-8(%rsp), %r15
	rolq	$27, %r15
	xorq	24(%rsp), %r12
	movq	%rax, %rsi
	notq	%rsi
	andq	%r10, %rsi
	movq	%r9, %rdi
	notq	%rdi
	andq	%r11, %rdi
	xorq	%r10, %rdi
	movq	%rdi, -24(%rsp)
	notq	%r10
	andq	%r9, %r10
	movq	%r11, %rbp
	notq	%rbp
	andq	%r15, %rbp
	xorq	%r9, %rbp
	movq	%rbp, -8(%rsp)
	xorq	%r15, %rsi
	movq	%rsi, -56(%rsp)
	xorq	%rax, %r10
	movq	%r10, -88(%rsp)
	notq	%r15
	andq	%rax, %r15
	xorq	%r11, %r15
	movq	%r15, %r9
	movq	%r15, -72(%rsp)
	movq	-112(%rsp), %r11
	xorq	%r8, %r11
	movq	%r11, -112(%rsp)
	movq	-96(%rsp), %rax
	xorq	72(%rsp), %rax
	xorq	%rdi, %r11
	xorq	%rax, %r11
	movq	56(%rsp), %rsi
	xorq	-80(%rsp), %rsi
	notq	%r8
	movq	-128(%rsp), %r15
	xorq	%r13, %r15
	movq	%r15, -128(%rsp)
	andq	%r13, %r8
	movq	%r8, %r13
	xorq	%rbp, %r15
	movq	-104(%rsp), %rax
	xorq	8(%rsp), %rax
	xorq	%rax, %r15
	movq	-120(%rsp), %rax
	xorq	(%rsp), %rax
	movq	%rbx, %r8
	xorq	%r9, %r8
	xorq	%rax, %r8
	xorq	32(%rsp), %rcx
	xorq	%rdx, %r13
	movq	%r13, 48(%rsp)
	movq	96(%rsp), %rax
	xorq	40(%rsp), %rax
	movq	-32(%rsp), %r9
	xorq	-16(%rsp), %r9
	rolq	$62, %r12
	rolq	$41, %rax
	rolq	$55, %rcx
	rolq	$2, %r9
	rolq	$39, %r14
	movq	%rcx, %r10
	notq	%r10
	andq	%r14, %r10
	movq	%rax, %rbp
	notq	%rbp
	andq	%r9, %rbp
	xorq	%r14, %rbp
	movq	%r14, %rbx
	notq	%rbx
	movq	%r9, %r14
	notq	%r14
	andq	%rax, %rbx
	andq	%r12, %r14
	xorq	%rax, %r14
	movq	%r14, -32(%rsp)
	xorq	%r12, %r10
	movq	%r10, 56(%rsp)
	xorq	%rcx, %rbx
	movq	%rbx, %rdi
	movq	%rbx, -16(%rsp)
	notq	%r12
	andq	%rcx, %r12
	xorq	%r9, %r12
	movq	%rsi, %rcx
	xorq	80(%rsp), %rcx
	xorq	-88(%rsp), %r13
	xorq	%rcx, %r13
	movq	-48(%rsp), %r9
	xorq	-64(%rsp), %r9
	xorq	-56(%rsp), %r9
	xorq	%r10, %r9
	movq	104(%rsp), %rdx
	xorq	%rdx, %r9
	xorq	%rbp, %r11
	xorq	%r14, %r15
	xorq	%r12, %r8
	movq	%r15, %rbx
	rolq	%rbx
	xorq	%rdi, %r13
	xorq	%r13, %rbx
	rolq	%r13
	xorq	%r8, %r13
	rolq	%r8
	xorq	%r11, %r8
	movq	%r11, %rdi
	rolq	%rdi
	xorq	%r9, %rdi
	rolq	%r9
	xorq	%r15, %r9
	xorq	%r9, %r12
	xorq	%r9, -120(%rsp)
	xorq	%r9, -72(%rsp)
	xorq	%r9, (%rsp)
	xorq	-40(%rsp), %r9
	movq	-112(%rsp), %r10
	xorq	%rbx, %r10
	rolq	$43, %r10
	xorq	%r13, %rdx
	xorq	%rdi, %rsi
	movq	-8(%rsp), %r15
	xorq	%r8, %r15
	rolq	$44, %rsi
	rolq	$21, %r15
	rolq	$14, %r12
	movq	%r10, %rcx
	notq	%rcx
	andq	%r15, %rcx
	xorq	%rsi, %rcx
	movq	%rcx, 16(%rsp)
	movq	%rdx, %rcx
	notq	%rcx
	andq	%rsi, %rcx
	movq	%rsi, %rax
	notq	%rax
	movq	%r12, %r11
	notq	%r11
	andq	%r10, %rax
	andq	%rdx, %r11
	xorq	%r15, %r11
	movq	%r15, %rsi
	movq	%rcx, %r15
	notq	%rsi
	andq	%r12, %rsi
	xorq	%r10, %rsi
	movq	%rsi, 24(%rsp)
	leaq	.Lanon.5ef9b7c546f4dc64388b910df55ec241.1(%rip), %rsi
	movq	64(%rsp), %rcx
	xorq	(%rcx,%rsi), %rax
	xorq	%r12, %r15
	movq	%r15, -8(%rsp)
	xorq	%rdx, %rax
	movq	%rax, -40(%rsp)
	movq	-64(%rsp), %r10
	xorq	%r13, %r10
	movq	%r13, %r15
	movq	8(%rsp), %rcx
	xorq	%r8, %rcx
	rolq	$3, %r10
	rolq	$28, %rcx
	movq	-88(%rsp), %r14
	movq	%rdi, %r13
	xorq	%rdi, %r14
	xorq	%rbx, %rbp
	rolq	$45, %r14
	rolq	$61, %rbp
	movq	-120(%rsp), %rsi
	rolq	$20, %rsi
	movq	%rsi, %rax
	notq	%rax
	andq	%r10, %rax
	movq	%rax, %rdx
	movq	%r14, %rax
	notq	%rax
	andq	%rbp, %rax
	xorq	%r10, %rax
	movq	%rax, -112(%rsp)
	notq	%r10
	movq	%rbp, %rax
	notq	%rax
	andq	%r14, %r10
	andq	%rcx, %rax
	xorq	%r14, %rax
	movq	%rax, 32(%rsp)
	xorq	%rcx, %rdx
	movq	%rdx, -88(%rsp)
	notq	%rcx
	andq	%rsi, %rcx
	xorq	%rbp, %rcx
	movq	%rcx, -80(%rsp)
	xorq	%rsi, %r10
	movq	%r10, -120(%rsp)
	movq	-96(%rsp), %rsi
	xorq	%rbx, %rsi
	movq	-24(%rsp), %rdi
	xorq	%rbx, %rdi
	xorq	72(%rsp), %rbx
	movq	-48(%rsp), %rcx
	xorq	%r15, %rcx
	movq	%r15, %rdx
	rolq	$15, %rdi
	rolq	$36, %rcx
	movq	48(%rsp), %r12
	movq	%r13, %r14
	xorq	%r13, %r12
	movq	-32(%rsp), %r10
	xorq	%r8, %r10
	movq	%r8, %rbp
	rolq	$10, %r12
	rolq	$56, %r10
	movq	%r10, -32(%rsp)
	movq	(%rsp), %rax
	rolq	$27, %rax
	movq	%rcx, %r8
	notq	%r8
	andq	%r12, %r8
	movq	%rdi, %r13
	notq	%r13
	andq	%r10, %r13
	xorq	%r12, %r13
	notq	%r12
	movq	%r10, %r15
	notq	%r15
	andq	%rdi, %r12
	andq	%rax, %r15
	xorq	%rdi, %r15
	movq	%r15, 8(%rsp)
	xorq	%rax, %r8
	movq	%r8, 40(%rsp)
	xorq	%rcx, %r12
	notq	%rax
	andq	%rcx, %rax
	movq	%rax, (%rsp)
	movq	%rsi, %rcx
	rolq	$6, %rcx
	movq	80(%rsp), %rsi
	xorq	%r14, %rsi
	movq	-128(%rsp), %r8
	movq	%rbp, %rdi
	xorq	%rbp, %r8
	rolq	%rsi
	rolq	$25, %r8
	movq	%r8, -128(%rsp)
	movq	-72(%rsp), %rax
	rolq	$8, %rax
	movq	56(%rsp), %rbp
	xorq	%rdx, %rbp
	rolq	$18, %rbp
	movq	%rcx, %r15
	movq	%rcx, %r10
	notq	%r15
	andq	%r8, %r15
	xorq	%rsi, %r15
	movq	%r15, -96(%rsp)
	movq	%r8, %rcx
	notq	%rcx
	movq	%rbp, %r15
	notq	%r15
	andq	%rax, %rcx
	andq	%rsi, %r15
	notq	%rsi
	andq	%r10, %rsi
	movq	%rsi, %r8
	xorq	%r10, %rcx
	xorq	-104(%rsp), %rdi
	xorq	-56(%rsp), %rdx
	xorq	%rax, %r15
	movq	%rax, %rsi
	notq	%rsi
	xorq	%rbp, %r8
	movq	%r8, -104(%rsp)
	andq	%rbp, %rsi
	rolq	$62, %rbx
	movq	%rdi, %rbp
	rolq	$55, %rbp
	rolq	$41, %rdx
	rolq	$39, %r9
	xorq	-16(%rsp), %r14
	rolq	$2, %r14
	movq	(%rsp), %rdi
	xorq	-32(%rsp), %rdi
	movq	%rbp, %r10
	notq	%r10
	andq	%r9, %r10
	movq	%rdx, %rax
	notq	%rax
	andq	%r14, %rax
	xorq	%r9, %rax
	notq	%r9
	andq	%rdx, %r9
	movq	%r14, %r8
	notq	%r8
	andq	%rbx, %r8
	xorq	%rdx, %r8
	xorq	%rbx, %r10
	xorq	%rbp, %r9
	notq	%rbx
	andq	%rbp, %rbx
	xorq	-128(%rsp), %rsi
	xorq	%r14, %rbx
	movq	%rcx, -72(%rsp)
	xorq	-120(%rsp), %rcx
	movq	%r9, -16(%rsp)
	xorq	%r9, %rcx
	movq	16(%rsp), %r9
	movq	%r12, -48(%rsp)
	xorq	%r12, %r9
	xorq	%rcx, %r9
	movq	24(%rsp), %rcx
	xorq	-112(%rsp), %rcx
	movq	%r13, -56(%rsp)
	xorq	%rax, %r13
	xorq	%rsi, %rcx
	xorq	%rcx, %r13
	movq	8(%rsp), %rdx
	movq	%rdx, %rcx
	xorq	32(%rsp), %rcx
	xorq	%r11, %rcx
	movq	%r15, -64(%rsp)
	movq	%r15, %rbp
	movq	%r8, -24(%rsp)
	xorq	%r8, %rbp
	movq	%rdx, %r8
	xorq	%rcx, %rbp
	movq	-80(%rsp), %r14
	movq	-8(%rsp), %rcx
	movq	%rcx, %r15
	xorq	%rcx, %r14
	movq	-104(%rsp), %rcx
	xorq	%rbx, %rcx
	movq	%rdi, -128(%rsp)
	xorq	%rdi, %r14
	xorq	%r14, %rcx
	movq	%r10, %r14
	xorq	-96(%rsp), %r14
	xorq	-88(%rsp), %r14
	xorq	40(%rsp), %r14
	xorq	-40(%rsp), %r14
	movq	64(%rsp), %rdx
	addq	$16, %rdx
	movq	%rdx, %rdi
	cmpq	$200, %rdx
	jne	.LBB9_1
	movq	88(%rsp), %rcx
	movq	-40(%rsp), %rdi
	movq	%rdi, (%rcx)
	movq	-120(%rsp), %rdi
	movq	%rdi, 48(%rcx)
	movq	%rsi, 96(%rcx)
	movq	%r8, 144(%rcx)
	movq	%rbx, 192(%rcx)
	movq	%r11, 24(%rcx)
	movq	-80(%rsp), %rdx
	movq	%rdx, 72(%rcx)
	movq	-96(%rsp), %rdx
	movq	%rdx, 80(%rcx)
	movq	-48(%rsp), %rdx
	movq	%rdx, 128(%rcx)
	movq	%rax, 176(%rcx)
	movq	16(%rsp), %rax
	movq	%rax, 8(%rcx)
	movq	-112(%rsp), %rax
	movq	%rax, 56(%rcx)
	movq	-64(%rsp), %rax
	movq	%rax, 104(%rcx)
	movq	-128(%rsp), %rax
	movq	%rax, 152(%rcx)
	movq	%r10, 160(%rcx)
	movq	%r15, 32(%rcx)
	movq	-88(%rsp), %rax
	movq	%rax, 40(%rcx)
	movq	-72(%rsp), %rax
	movq	%rax, 88(%rcx)
	movq	-56(%rsp), %rax
	movq	%rax, 136(%rcx)
	movq	-24(%rsp), %rax
	movq	%rax, 184(%rcx)
	movq	24(%rsp), %rax
	movq	%rax, 16(%rcx)
	movq	32(%rsp), %rax
	movq	%rax, 64(%rcx)
	movq	-104(%rsp), %rax
	movq	%rax, 112(%rcx)
	movq	40(%rsp), %rax
	movq	%rax, 120(%rcx)
	movq	-16(%rsp), %rax
	movq	%rax, 168(%rcx)
	addq	$112, %rsp
	.cfi_def_cfa_offset 56
	popq	%rbx
	.cfi_def_cfa_offset 48
	popq	%r12
	.cfi_def_cfa_offset 40
	popq	%r13
	.cfi_def_cfa_offset 32
	popq	%r14
	.cfi_def_cfa_offset 24
	popq	%r15
	.cfi_def_cfa_offset 16
	popq	%rbp
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end9:
	.size	_RNvCsndc0WgnAaH_9keccak2568keccak_f, .Lfunc_end9-_RNvCsndc0WgnAaH_9keccak2568keccak_f
	.cfi_endproc

	.section	.text._RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update,"ax",@progbits
	.p2align	4
	.type	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update,@function
_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update:
.Lfunc_begin10:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	pushq	%r15
	.cfi_def_cfa_offset 24
	pushq	%r14
	.cfi_def_cfa_offset 32
	pushq	%r13
	.cfi_def_cfa_offset 40
	pushq	%r12
	.cfi_def_cfa_offset 48
	pushq	%rbx
	.cfi_def_cfa_offset 56
	subq	$56, %rsp
	.cfi_def_cfa_offset 112
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	%rdx, %rbx
	movq	%rsi, %r15
	movq	%rdi, %r14
	leaq	200(%rdi), %r13
	movq	336(%rdi), %rdi
	movq	memcpy@GOTPCREL(%rip), %rbp
	jmp	.LBB10_1
	.p2align	4
.LBB10_5:
	subq	%r12, %rbx
	addq	%r12, %r15
	testq	%rbx, %rbx
	je	.LBB10_6
.LBB10_1:
	movl	$136, %r12d
	subq	%rdi, %r12
	cmpq	%r12, %rbx
	cmovbq	%rbx, %r12
	leaq	(%r12,%rdi), %rsi
	cmpq	%rdi, %rsi
	jb	.LBB10_7
	cmpq	$137, %rsi
	jae	.LBB10_7
	addq	%r13, %rdi
	movq	%r15, %rsi
	movq	%r12, %rdx
	callq	*%rbp
	movq	336(%r14), %rdi
	addq	%r12, %rdi
	movq	%rdi, 336(%r14)
	cmpq	$136, %rdi
	jne	.LBB10_5
	movq	200(%r14), %rax
	movq	%rax, 40(%rsp)
	movq	208(%r14), %rcx
	movq	216(%r14), %rdx
	movq	224(%r14), %rsi
	movq	232(%r14), %rdi
	movq	240(%r14), %r8
	movq	248(%r14), %r9
	movq	256(%r14), %r10
	movq	264(%r14), %r11
	movq	272(%r14), %r13
	movq	280(%r14), %rbp
	movq	288(%r14), %rax
	movq	%rax, 48(%rsp)
	movq	296(%r14), %rax
	movq	%rax, 32(%rsp)
	movq	304(%r14), %rax
	movq	%rax, 24(%rsp)
	movq	312(%r14), %rax
	movq	%rax, 16(%rsp)
	movq	320(%r14), %rax
	movq	%rax, 8(%rsp)
	movq	328(%r14), %rax
	movq	%rax, (%rsp)
	movq	40(%rsp), %rax
	xorq	%rax, (%r14)
	xorq	%rcx, 8(%r14)
	xorq	%rdx, 16(%r14)
	xorq	%rsi, 24(%r14)
	xorq	%rdi, 32(%r14)
	xorq	%r8, 40(%r14)
	xorq	%r9, 48(%r14)
	xorq	%r10, 56(%r14)
	xorq	%r11, 64(%r14)
	xorq	%r13, 72(%r14)
	leaq	200(%r14), %r13
	xorq	%rbp, 80(%r14)
	movq	memcpy@GOTPCREL(%rip), %rbp
	movq	48(%rsp), %rax
	xorq	%rax, 88(%r14)
	movq	32(%rsp), %rax
	xorq	%rax, 96(%r14)
	movq	24(%rsp), %rax
	xorq	%rax, 104(%r14)
	movq	16(%rsp), %rax
	xorq	%rax, 112(%r14)
	movq	8(%rsp), %rax
	xorq	%rax, 120(%r14)
	movq	(%rsp), %rax
	xorq	%rax, 128(%r14)
	movq	%r14, %rdi
	callq	_RNvCsndc0WgnAaH_9keccak2568keccak_f
	movq	$0, 336(%r14)
	xorl	%edi, %edi
	jmp	.LBB10_5
.LBB10_6:
	movq	%r14, %rax
	addq	$56, %rsp
	.cfi_def_cfa_offset 56
	popq	%rbx
	.cfi_def_cfa_offset 48
	popq	%r12
	.cfi_def_cfa_offset 40
	popq	%r13
	.cfi_def_cfa_offset 32
	popq	%r14
	.cfi_def_cfa_offset 24
	popq	%r15
	.cfi_def_cfa_offset 16
	popq	%rbp
	.cfi_def_cfa_offset 8
	retq
.LBB10_7:
	.cfi_def_cfa_offset 112
	movl	$136, %edx
	callq	_RNvNtNtCs1gUZZmupoa8_4core5slice5index16slice_index_fail
.Lfunc_end10:
	.size	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update, .Lfunc_end10-_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	.cfi_endproc

	.section	.text._RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher8finalize,"ax",@progbits
	.p2align	4
	.type	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher8finalize,@function
_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher8finalize:
.Lfunc_begin11:
	.cfi_startproc
	pushq	%r15
	.cfi_def_cfa_offset 16
	pushq	%r14
	.cfi_def_cfa_offset 24
	pushq	%r12
	.cfi_def_cfa_offset 32
	pushq	%rbx
	.cfi_def_cfa_offset 40
	subq	$344, %rsp
	.cfi_def_cfa_offset 384
	.cfi_offset %rbx, -40
	.cfi_offset %r12, -32
	.cfi_offset %r14, -24
	.cfi_offset %r15, -16
	movq	%rsi, %r15
	movq	%rdi, %rbx
	leaq	144(%rsp), %rdi
	movl	$200, %edx
	callq	*memcpy@GOTPCREL(%rip)
	movq	336(%r15), %r14
	cmpq	$137, %r14
	jae	.LBB11_3
	cmpq	$136, %r14
	je	.LBB11_4
	addq	$200, %r15
	leaq	8(%rsp), %r12
	movl	$136, %edx
	movq	%r12, %rdi
	xorl	%esi, %esi
	callq	*memset@GOTPCREL(%rip)
	movq	%r12, %rdi
	movq	%r15, %rsi
	movq	%r14, %rdx
	callq	*memcpy@GOTPCREL(%rip)
	xorb	$1, 8(%rsp,%r14)
	xorb	$-128, 143(%rsp)
	movq	8(%rsp), %rax
	xorq	%rax, 144(%rsp)
	movq	16(%rsp), %rax
	xorq	%rax, 152(%rsp)
	movq	24(%rsp), %rax
	xorq	%rax, 160(%rsp)
	movq	32(%rsp), %rax
	xorq	%rax, 168(%rsp)
	movq	40(%rsp), %rax
	xorq	%rax, 176(%rsp)
	movq	48(%rsp), %rax
	xorq	%rax, 184(%rsp)
	movq	56(%rsp), %rax
	xorq	%rax, 192(%rsp)
	movq	64(%rsp), %rax
	xorq	%rax, 200(%rsp)
	movq	72(%rsp), %rax
	xorq	%rax, 208(%rsp)
	movq	80(%rsp), %rax
	xorq	%rax, 216(%rsp)
	movq	88(%rsp), %rax
	xorq	%rax, 224(%rsp)
	movq	96(%rsp), %rax
	xorq	%rax, 232(%rsp)
	movq	104(%rsp), %rax
	xorq	%rax, 240(%rsp)
	movq	112(%rsp), %rax
	xorq	%rax, 248(%rsp)
	movq	120(%rsp), %rax
	xorq	%rax, 256(%rsp)
	movq	128(%rsp), %rax
	xorq	%rax, 264(%rsp)
	movq	136(%rsp), %rax
	xorq	%rax, 272(%rsp)
	leaq	144(%rsp), %rdi
	callq	_RNvCsndc0WgnAaH_9keccak2568keccak_f
	movq	168(%rsp), %rax
	movq	%rax, 24(%rbx)
	movq	160(%rsp), %rax
	movq	%rax, 16(%rbx)
	movq	144(%rsp), %rax
	movq	152(%rsp), %rcx
	movq	%rcx, 8(%rbx)
	movq	%rax, (%rbx)
	addq	$344, %rsp
	.cfi_def_cfa_offset 40
	popq	%rbx
	.cfi_def_cfa_offset 32
	popq	%r12
	.cfi_def_cfa_offset 24
	popq	%r14
	.cfi_def_cfa_offset 16
	popq	%r15
	.cfi_def_cfa_offset 8
	retq
.LBB11_3:
	.cfi_def_cfa_offset 384
	movl	$136, %edx
	xorl	%edi, %edi
	movq	%r14, %rsi
	callq	_RNvNtNtCs1gUZZmupoa8_4core5slice5index16slice_index_fail
.LBB11_4:
	callq	_RNvNtCs1gUZZmupoa8_4core9panicking9panic_fmt
.Lfunc_end11:
	.size	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher8finalize, .Lfunc_end11-_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher8finalize
	.cfi_endproc

	.section	.text._RNvMs_NtCs7Pyp4CbMBld_9lean_xmss6schemeNtB4_14LayerSignature4read,"ax",@progbits
	.p2align	4
	.type	_RNvMs_NtCs7Pyp4CbMBld_9lean_xmss6schemeNtB4_14LayerSignature4read,@function
_RNvMs_NtCs7Pyp4CbMBld_9lean_xmss6schemeNtB4_14LayerSignature4read:
.Lfunc_begin12:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	pushq	%r15
	.cfi_def_cfa_offset 24
	pushq	%r14
	.cfi_def_cfa_offset 32
	pushq	%r13
	.cfi_def_cfa_offset 40
	pushq	%r12
	.cfi_def_cfa_offset 48
	pushq	%rbx
	.cfi_def_cfa_offset 56
	subq	$1880, %rsp
	.cfi_def_cfa_offset 1936
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	8(%rsi), %r12
	cmpq	$15, %r12
	jbe	.LBB12_22
	movq	%rsi, %r14
	movq	%rdi, 16(%rsp)
	leaq	24(%rsp), %rsi
	movq	(%r14), %r11
	leaq	-16(%r12), %rax
	shrq	$4, %rax
	xorl	%ecx, %ecx
	movq	%rax, %rdx
	xorl	%edi, %edi
	.p2align	4
.LBB12_2:
	testq	%rdx, %rdx
	je	.LBB12_22
	movq	%r12, %rbx
	leaq	(%r11,%rcx), %r13
	addq	$16, %r13
	leaq	32(%r11,%rcx), %r8
	addq	$-32, %r12
	movq	%r8, (%r14)
	movq	%r12, 8(%r14)
	movq	(%r13), %r9
	movq	8(%r13), %r10
	movq	%r10, 8(%rsi,%rcx)
	movq	%r9, (%rsi,%rcx)
	leaq	1(%rdi), %r9
	cmpq	%rax, %r9
	je	.LBB12_22
	leaq	(%r11,%rcx), %r15
	addq	$48, %r15
	leaq	-48(%rbx), %rbp
	movq	%r15, (%r14)
	movq	%rbp, 8(%r14)
	movq	(%r8), %r9
	movq	8(%r8), %r8
	movq	%r8, 24(%rsi,%rcx)
	movq	%r9, 16(%rsi,%rcx)
	addq	$2, %rdi
	addq	$32, %rcx
	addq	$-2, %rdx
	cmpq	$58, %rdi
	jne	.LBB12_2
	movq	%r11, 8(%rsp)
	leaq	952(%rsp), %rdi
	movl	$928, %edx
	callq	*memcpy@GOTPCREL(%rip)
	cmpq	$15, %rbp
	jbe	.LBB12_22
	movq	(%r15), %rax
	movq	8(%r15), %rcx
	movq	%rcx, 32(%rsp)
	movq	%rax, 24(%rsp)
	andq	$-16, %rbp
	cmpq	$16, %rbp
	je	.LBB12_22
	movq	48(%r13), %rax
	movq	56(%r13), %rcx
	movq	%rcx, 48(%rsp)
	movq	%rax, 40(%rsp)
	cmpq	$32, %rbp
	je	.LBB12_22
	movq	64(%r13), %rax
	movq	72(%r13), %rcx
	movq	%rcx, 64(%rsp)
	movq	%rax, 56(%rsp)
	cmpq	$48, %rbp
	je	.LBB12_22
	movq	80(%r13), %rax
	movq	88(%r13), %rcx
	movq	%rcx, 80(%rsp)
	movq	%rax, 72(%rsp)
	cmpq	$64, %rbp
	je	.LBB12_22
	movq	96(%r13), %rax
	movq	104(%r13), %rcx
	movq	%rcx, 96(%rsp)
	movq	%rax, 88(%rsp)
	cmpq	$80, %rbp
	je	.LBB12_22
	movq	112(%r13), %rax
	movq	120(%r13), %rcx
	movq	%rcx, 112(%rsp)
	movq	%rax, 104(%rsp)
	cmpq	$96, %rbp
	je	.LBB12_22
	movq	128(%r13), %rax
	movq	136(%r13), %rcx
	movq	%rcx, 128(%rsp)
	movq	%rax, 120(%rsp)
	cmpq	$112, %rbp
	je	.LBB12_22
	movq	144(%r13), %rax
	movq	152(%r13), %rcx
	movq	%rcx, 144(%rsp)
	movq	%rax, 136(%rsp)
	andq	$-16, %r12
	cmpq	$144, %r12
	je	.LBB12_22
	movq	160(%r13), %rax
	movq	168(%r13), %rcx
	movq	%rcx, 160(%rsp)
	movq	%rax, 152(%rsp)
	cmpq	$144, %rbp
	je	.LBB12_22
	movq	176(%r13), %rax
	movq	184(%r13), %rcx
	movq	%rcx, 176(%rsp)
	movq	%rax, 168(%rsp)
	cmpq	$160, %rbp
	je	.LBB12_22
	movq	192(%r13), %rax
	movq	200(%r13), %rcx
	movq	%rcx, 192(%rsp)
	movq	%rax, 184(%rsp)
	cmpq	$176, %rbp
	je	.LBB12_22
	movq	208(%r13), %rax
	movq	216(%r13), %rcx
	movq	%rcx, 208(%rsp)
	movq	%rax, 200(%rsp)
	cmpq	$192, %rbp
	je	.LBB12_22
	movq	224(%r13), %rax
	movq	232(%r13), %rcx
	movq	%rcx, 224(%rsp)
	movq	%rax, 216(%rsp)
	cmpq	$208, %rbp
	je	.LBB12_22
	movq	240(%r13), %rax
	movq	248(%r13), %rcx
	movq	%rcx, 240(%rsp)
	movq	%rax, 232(%rsp)
	cmpq	$224, %rbp
	je	.LBB12_22
	movq	256(%r13), %rax
	movq	264(%r13), %rcx
	movq	%rcx, 256(%rsp)
	movq	%rax, 248(%rsp)
	cmpq	$240, %rbp
	je	.LBB12_22
	addq	$-16, %rbx
	leaq	288(%r13), %rax
	addq	$-288, %rbx
	movq	%rax, (%r14)
	movq	%rbx, 8(%r14)
	movq	272(%r13), %rax
	movq	280(%r13), %rcx
	movq	%rcx, 272(%rsp)
	movq	%rax, 264(%rsp)
	leaq	24(%rsp), %rsi
	movq	memcpy@GOTPCREL(%rip), %rbx
	movl	$256, %edx
	movq	16(%rsp), %r14
	movq	%r14, %rdi
	callq	*%rbx
	movq	8(%rsp), %rcx
	movq	(%rcx), %rax
	movq	8(%rcx), %rcx
	movq	%rcx, 1192(%r14)
	movq	%rax, 1184(%r14)
	addq	$256, %r14
	leaq	952(%rsp), %rsi
	movl	$928, %edx
	movq	%r14, %rdi
	callq	*%rbx
	addq	$1880, %rsp
	.cfi_def_cfa_offset 56
	popq	%rbx
	.cfi_def_cfa_offset 48
	popq	%r12
	.cfi_def_cfa_offset 40
	popq	%r13
	.cfi_def_cfa_offset 32
	popq	%r14
	.cfi_def_cfa_offset 24
	popq	%r15
	.cfi_def_cfa_offset 16
	popq	%rbp
	.cfi_def_cfa_offset 8
	retq
.LBB12_22:
	.cfi_def_cfa_offset 1936
	callq	_RNvNtCs1gUZZmupoa8_4core6option13unwrap_failed
.Lfunc_end12:
	.size	_RNvMs_NtCs7Pyp4CbMBld_9lean_xmss6schemeNtB4_14LayerSignature4read, .Lfunc_end12-_RNvMs_NtCs7Pyp4CbMBld_9lean_xmss6schemeNtB4_14LayerSignature4read
	.cfi_endproc

	.section	.text._RNvNtCs7Pyp4CbMBld_9lean_xmss4wots9wots_leaf,"ax",@progbits
	.p2align	4
	.type	_RNvNtCs7Pyp4CbMBld_9lean_xmss4wots9wots_leaf,@function
_RNvNtCs7Pyp4CbMBld_9lean_xmss4wots9wots_leaf:
.Lfunc_begin13:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	pushq	%r15
	.cfi_def_cfa_offset 24
	pushq	%r14
	.cfi_def_cfa_offset 32
	pushq	%r13
	.cfi_def_cfa_offset 40
	pushq	%r12
	.cfi_def_cfa_offset 48
	pushq	%rbx
	.cfi_def_cfa_offset 56
	subq	$2712, %rsp
	.cfi_def_cfa_offset 2768
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	%r9, %r14
	movq	%r8, %r15
	movq	%rsi, %r13
	movq	%rdi, 96(%rsp)
	movq	2768(%rsp), %rbx
	movl	%ecx, 52(%rsp)
	movl	%ecx, 112(%rsp)
	movq	%rdx, %rax
	movq	%rdx, 8(%rsp)
	shll	$7, %eax
	movb	%al, 118(%rsp)
	movw	$0, 116(%rsp)
	movb	$12, 119(%rsp)
	movq	$0, 120(%rsp)
	leaq	2008(%rsp), %r12
	movl	$344, %edx
	movq	%r12, %rdi
	xorl	%esi, %esi
	callq	*memset@GOTPCREL(%rip)
	movl	$16, %edx
	movq	%r12, %rdi
	movq	%r13, 104(%rsp)
	movq	%r13, %rsi
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	leaq	112(%rsp), %rsi
	movl	$16, %edx
	movq	%r12, %rdi
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	movq	%r12, %rdi
	movq	%r15, %rsi
	movq	%r14, %rdx
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	movl	$16, %edx
	movq	%r12, %rdi
	movq	%rbx, %rsi
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	leaq	112(%rsp), %rdi
	movq	%r12, %rsi
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher8finalize
	movq	120(%rsp), %rdx
	movq	%rdx, %rax
	shrq	$52, %rax
	jne	.LBB13_25
	movq	112(%rsp), %rsi
	movabsq	$1229782938247303441, %rax
	movq	%rsi, %rcx
	andq	%rax, %rcx
	movq	%rsi, %rdi
	shrq	$2, %rdi
	andq	%rax, %rdi
	addq	%rcx, %rdi
	movq	%rdi, %r8
	shrq	$4, %r8
	addq	%rdi, %r8
	movabsq	$1085102592571150095, %rax
	andq	%rax, %r8
	movabsq	$72340172838076673, %rcx
	imulq	%rcx, %r8
	shrq	$56, %r8
	movabsq	$300239975158033, %rdi
	movq	%rdx, %r9
	andq	%rdi, %r9
	movq	%rdx, %r10
	shrq	$2, %r10
	andq	%rdi, %r10
	addq	%r9, %r10
	movq	%r10, %rdi
	shrq	$4, %rdi
	addq	%r10, %rdi
	andq	%rax, %rdi
	imulq	%rcx, %rdi
	shrq	$56, %rdi
	addl	%r8d, %edi
	movabsq	$3002399751580330, %r8
	andq	%rdx, %r8
	movabsq	$-6148914691236517206, %r10
	andq	%rsi, %r10
	movq	%r10, %r9
	shrq	%r9
	subq	%r9, %r10
	movabsq	$3689348814741910323, %r11
	movq	%r10, %r9
	andq	%r11, %r9
	shrq	$2, %r10
	andq	%r11, %r10
	addq	%r9, %r10
	movq	%r10, %r9
	shrq	$4, %r9
	addq	%r10, %r9
	andq	%rax, %r9
	imulq	%rcx, %r9
	shrq	$56, %r9
	movq	%r8, %r10
	shrq	%r10
	subq	%r10, %r8
	movq	%r8, %r10
	andq	%r11, %r10
	shrq	$2, %r8
	andq	%r11, %r8
	addq	%r10, %r8
	movq	%r8, %r10
	shrq	$4, %r10
	addq	%r8, %r10
	andq	%rax, %r10
	imulq	%rcx, %r10
	shrq	$56, %r10
	addl	%r9d, %r10d
	leal	(%rdi,%r10,2), %eax
	cmpl	$106, %eax
	jne	.LBB13_25
	movq	8(%rsp), %rax
	shll	$23, %eax
	movq	%rax, 8(%rsp)
	leaq	615(%rsp), %rdi
	xorl	%eax, %eax
	.p2align	4
.LBB13_3:
	movq	%rsi, %r8
	movl	%eax, %ecx
	shrdq	%cl, %rdx, %r8
	movq	%rdx, %r9
	shrq	%cl, %r9
	testb	$64, %al
	cmoveq	%r8, %r9
	leal	2(%rax), %ecx
	movq	%rsi, %r8
	shrdq	%cl, %rdx, %r8
	andb	$3, %r9b
	movb	%r9b, -1(%rdi)
	movq	%rdx, %r9
	shrq	%cl, %r9
	testb	$64, %cl
	cmoveq	%r8, %r9
	andb	$3, %r9b
	movb	%r9b, (%rdi)
	addq	$4, %rax
	addq	$2, %rdi
	cmpq	$116, %rax
	jne	.LBB13_3
	xorl	%edx, %edx
	movq	8(%rsp), %rax
	shrl	$16, %eax
	movl	%eax, 48(%rsp)
	leaq	112(%rsp), %r12
	movq	memset@GOTPCREL(%rip), %rbx
	movq	memcpy@GOTPCREL(%rip), %r13
	jmp	.LBB13_5
.LBB13_25:
	movq	96(%rsp), %rax
	movb	$0, (%rax)
.LBB13_26:
	addq	$2712, %rsp
	.cfi_def_cfa_offset 56
	popq	%rbx
	.cfi_def_cfa_offset 48
	popq	%r12
	.cfi_def_cfa_offset 40
	popq	%r13
	.cfi_def_cfa_offset 32
	popq	%r14
	.cfi_def_cfa_offset 24
	popq	%r15
	.cfi_def_cfa_offset 16
	popq	%rbp
	.cfi_def_cfa_offset 8
	retq
	.p2align	4
.LBB13_23:
	.cfi_def_cfa_offset 2768
	movq	80(%rsp), %rax
	movq	88(%rsp), %rcx
	movq	456(%rsp), %rsi
	movq	%rax, 1080(%rsp,%rsi)
	movq	%rcx, 1088(%rsp,%rsi)
	incq	%rdx
	cmpq	$58, %rdx
	je	.LBB13_24
.LBB13_5:
	movzbl	614(%rsp,%rdx), %r14d
	movq	%rdx, %rsi
	shlq	$4, %rsi
	movq	2776(%rsp), %rcx
	movq	(%rcx,%rsi), %rax
	movq	%rsi, 456(%rsp)
	movq	8(%rcx,%rsi), %rcx
	movq	%rax, 80(%rsp)
	movq	%rcx, 88(%rsp)
	cmpq	$2, %r14
	ja	.LBB13_23
	movq	%rdx, 464(%rsp)
	.p2align	4
.LBB13_7:
	movq	80(%rsp), %rax
	movq	88(%rsp), %rcx
	movq	%rcx, 680(%rsp)
	movq	%rax, 672(%rsp)
	movq	%rdx, 688(%rsp)
	movq	$0, 696(%rsp)
	movl	%r14d, %eax
	shlb	$5, %al
	incb	%al
	movl	52(%rsp), %ecx
	movl	%ecx, 472(%rsp)
	movl	48(%rsp), %ecx
	movb	%cl, 478(%rsp)
	movq	8(%rsp), %rcx
	movw	%cx, 476(%rsp)
	movb	%al, 479(%rsp)
	movq	$0, 480(%rsp)
	movl	$344, %edx
	movq	%r12, %rdi
	xorl	%esi, %esi
	callq	*%rbx
	movq	104(%rsp), %rcx
	movq	(%rcx), %rax
	movq	8(%rcx), %rcx
	leaq	312(%rsp), %rdx
	movq	%rax, (%rdx)
	movq	%rcx, 8(%rdx)
	movq	448(%rsp), %rdi
	addq	$16, %rdi
	movq	%rdi, 448(%rsp)
	cmpq	$136, %rdi
	jne	.LBB13_9
	movq	312(%rsp), %rax
	movq	%rax, 24(%rsp)
	movq	320(%rsp), %rcx
	movq	328(%rsp), %rdx
	movq	336(%rsp), %rsi
	movq	344(%rsp), %rdi
	movq	352(%rsp), %r8
	movq	360(%rsp), %r9
	movq	368(%rsp), %r10
	movq	376(%rsp), %r11
	movq	384(%rsp), %rbx
	movq	%r14, 56(%rsp)
	movq	392(%rsp), %r14
	movq	400(%rsp), %r15
	movq	408(%rsp), %r12
	movq	416(%rsp), %rbp
	movq	%rbp, 40(%rsp)
	movq	424(%rsp), %rbp
	movq	432(%rsp), %rax
	movq	%rax, 32(%rsp)
	movq	440(%rsp), %rax
	movq	%rax, 16(%rsp)
	movq	24(%rsp), %rax
	xorq	%rax, 112(%rsp)
	xorq	%rcx, 120(%rsp)
	xorq	%rdx, 128(%rsp)
	xorq	%rsi, 136(%rsp)
	xorq	%rdi, 144(%rsp)
	xorq	%r8, 152(%rsp)
	xorq	%r9, 160(%rsp)
	xorq	%r10, 168(%rsp)
	xorq	%r11, 176(%rsp)
	xorq	%rbx, 184(%rsp)
	xorq	%r14, 192(%rsp)
	movq	56(%rsp), %r14
	xorq	%r15, 200(%rsp)
	xorq	%r12, 208(%rsp)
	leaq	112(%rsp), %r12
	movq	40(%rsp), %rax
	xorq	%rax, 216(%rsp)
	xorq	%rbp, 224(%rsp)
	movq	32(%rsp), %rax
	xorq	%rax, 232(%rsp)
	movq	16(%rsp), %rax
	xorq	%rax, 240(%rsp)
	movq	%r12, %rdi
	callq	_RNvCsndc0WgnAaH_9keccak2568keccak_f
	movq	$0, 448(%rsp)
	xorl	%edi, %edi
.LBB13_9:
	incq	%r14
	movq	%r14, 56(%rsp)
	movl	$16, %r14d
	leaq	472(%rsp), %rbx
	jmp	.LBB13_10
	.p2align	4
.LBB13_14:
	subq	%r15, %r14
	addq	%r15, %rbx
	testq	%r14, %r14
	je	.LBB13_15
.LBB13_10:
	movl	$136, %r15d
	subq	%rdi, %r15
	cmpq	%r15, %r14
	cmovbq	%r14, %r15
	leaq	(%r15,%rdi), %rsi
	cmpq	%rdi, %rsi
	jb	.LBB13_27
	cmpq	$137, %rsi
	jae	.LBB13_27
	leaq	312(%rsp), %rax
	addq	%rax, %rdi
	movq	%rbx, %rsi
	movq	%r15, %rdx
	callq	*%r13
	movq	448(%rsp), %rdi
	addq	%r15, %rdi
	movq	%rdi, 448(%rsp)
	cmpq	$136, %rdi
	jne	.LBB13_14
	movq	312(%rsp), %rax
	movq	%rax, 32(%rsp)
	movq	320(%rsp), %rcx
	movq	328(%rsp), %rdx
	movq	336(%rsp), %rsi
	movq	344(%rsp), %rdi
	movq	352(%rsp), %r8
	movq	360(%rsp), %r9
	movq	368(%rsp), %r10
	movq	376(%rsp), %r11
	movq	384(%rsp), %r12
	movq	392(%rsp), %rbp
	movq	400(%rsp), %r13
	movq	408(%rsp), %rax
	movq	%rax, 40(%rsp)
	movq	416(%rsp), %rax
	movq	%rax, 24(%rsp)
	movq	424(%rsp), %rax
	movq	%rax, 16(%rsp)
	movq	432(%rsp), %rax
	movq	%rax, 72(%rsp)
	movq	440(%rsp), %rax
	movq	%rax, 64(%rsp)
	movq	32(%rsp), %rax
	xorq	%rax, 112(%rsp)
	xorq	%rcx, 120(%rsp)
	xorq	%rdx, 128(%rsp)
	xorq	%rsi, 136(%rsp)
	xorq	%rdi, 144(%rsp)
	xorq	%r8, 152(%rsp)
	xorq	%r9, 160(%rsp)
	xorq	%r10, 168(%rsp)
	xorq	%r11, 176(%rsp)
	xorq	%r12, 184(%rsp)
	leaq	112(%rsp), %r12
	xorq	%rbp, 192(%rsp)
	xorq	%r13, 200(%rsp)
	movq	memcpy@GOTPCREL(%rip), %r13
	movq	40(%rsp), %rax
	xorq	%rax, 208(%rsp)
	movq	24(%rsp), %rax
	xorq	%rax, 216(%rsp)
	movq	16(%rsp), %rax
	xorq	%rax, 224(%rsp)
	movq	72(%rsp), %rax
	xorq	%rax, 232(%rsp)
	movq	64(%rsp), %rax
	xorq	%rax, 240(%rsp)
	movq	%r12, %rdi
	callq	_RNvCsndc0WgnAaH_9keccak2568keccak_f
	movq	$0, 448(%rsp)
	xorl	%edi, %edi
	jmp	.LBB13_14
	.p2align	4
.LBB13_15:
	movl	$344, %edx
	leaq	704(%rsp), %rdi
	movq	%r12, %rsi
	callq	*%r13
	movl	$32, %r12d
	movq	1040(%rsp), %r15
	leaq	672(%rsp), %rbx
	jmp	.LBB13_16
	.p2align	4
.LBB13_20:
	subq	%r14, %r12
	addq	%r14, %rbx
	testq	%r12, %r12
	je	.LBB13_21
.LBB13_16:
	movl	$136, %r14d
	subq	%r15, %r14
	cmpq	%r14, %r12
	cmovbq	%r12, %r14
	leaq	(%r14,%r15), %rsi
	cmpq	%r15, %rsi
	jb	.LBB13_28
	cmpq	$137, %rsi
	jae	.LBB13_28
	leaq	904(%rsp), %rax
	addq	%rax, %r15
	movq	%r15, %rdi
	movq	%rbx, %rsi
	movq	%r14, %rdx
	callq	*%r13
	movq	1040(%rsp), %r15
	addq	%r14, %r15
	movq	%r15, 1040(%rsp)
	cmpq	$136, %r15
	jne	.LBB13_20
	movq	904(%rsp), %rax
	movq	%rax, 32(%rsp)
	movq	912(%rsp), %rcx
	movq	920(%rsp), %rdx
	movq	928(%rsp), %rsi
	movq	936(%rsp), %rdi
	movq	944(%rsp), %r8
	movq	952(%rsp), %r9
	movq	960(%rsp), %r10
	movq	968(%rsp), %r11
	movq	976(%rsp), %r15
	movq	984(%rsp), %r13
	movq	992(%rsp), %rbp
	movq	1000(%rsp), %rax
	movq	%rax, 40(%rsp)
	movq	1008(%rsp), %rax
	movq	%rax, 24(%rsp)
	movq	1016(%rsp), %rax
	movq	%rax, 16(%rsp)
	movq	1024(%rsp), %rax
	movq	%rax, 72(%rsp)
	movq	1032(%rsp), %rax
	movq	%rax, 64(%rsp)
	movq	32(%rsp), %rax
	xorq	%rax, 704(%rsp)
	xorq	%rcx, 712(%rsp)
	xorq	%rdx, 720(%rsp)
	xorq	%rsi, 728(%rsp)
	xorq	%rdi, 736(%rsp)
	xorq	%r8, 744(%rsp)
	xorq	%r9, 752(%rsp)
	xorq	%r10, 760(%rsp)
	xorq	%r11, 768(%rsp)
	xorq	%r15, 776(%rsp)
	xorq	%r13, 784(%rsp)
	movq	memcpy@GOTPCREL(%rip), %r13
	xorq	%rbp, 792(%rsp)
	movq	40(%rsp), %rax
	xorq	%rax, 800(%rsp)
	movq	24(%rsp), %rax
	xorq	%rax, 808(%rsp)
	movq	16(%rsp), %rax
	xorq	%rax, 816(%rsp)
	movq	72(%rsp), %rax
	xorq	%rax, 824(%rsp)
	movq	64(%rsp), %rax
	xorq	%rax, 832(%rsp)
	leaq	704(%rsp), %rdi
	callq	_RNvCsndc0WgnAaH_9keccak2568keccak_f
	movq	$0, 1040(%rsp)
	xorl	%r15d, %r15d
	jmp	.LBB13_20
	.p2align	4
.LBB13_21:
	movl	$200, %edx
	leaq	112(%rsp), %r12
	movq	%r12, %rdi
	leaq	704(%rsp), %rsi
	callq	*%r13
	movl	$136, %edx
	cmpq	$137, %r15
	jae	.LBB13_29
	leaq	472(%rsp), %r14
	movq	%r14, %rdi
	xorl	%esi, %esi
	movq	memset@GOTPCREL(%rip), %rbx
	callq	*%rbx
	movq	%r14, %rdi
	leaq	904(%rsp), %rsi
	movq	%r15, %rdx
	callq	*%r13
	xorb	$1, 472(%rsp,%r15)
	xorb	$-128, 607(%rsp)
	movq	472(%rsp), %rax
	xorq	%rax, 112(%rsp)
	movq	480(%rsp), %rax
	xorq	%rax, 120(%rsp)
	movq	488(%rsp), %rax
	xorq	%rax, 128(%rsp)
	movq	496(%rsp), %rax
	xorq	%rax, 136(%rsp)
	movq	504(%rsp), %rax
	xorq	%rax, 144(%rsp)
	movq	512(%rsp), %rax
	xorq	%rax, 152(%rsp)
	movq	520(%rsp), %rax
	xorq	%rax, 160(%rsp)
	movq	528(%rsp), %rax
	xorq	%rax, 168(%rsp)
	movq	536(%rsp), %rax
	xorq	%rax, 176(%rsp)
	movq	544(%rsp), %rax
	xorq	%rax, 184(%rsp)
	movq	552(%rsp), %rax
	xorq	%rax, 192(%rsp)
	movq	560(%rsp), %rax
	xorq	%rax, 200(%rsp)
	movq	568(%rsp), %rax
	xorq	%rax, 208(%rsp)
	movq	576(%rsp), %rax
	xorq	%rax, 216(%rsp)
	movq	584(%rsp), %rax
	xorq	%rax, 224(%rsp)
	movq	592(%rsp), %rax
	xorq	%rax, 232(%rsp)
	movq	600(%rsp), %rax
	xorq	%rax, 240(%rsp)
	movq	%r12, %rdi
	callq	_RNvCsndc0WgnAaH_9keccak2568keccak_f
	movq	136(%rsp), %rax
	movq	%rax, 496(%rsp)
	movq	112(%rsp), %rax
	movq	120(%rsp), %rcx
	movq	%rax, 472(%rsp)
	movq	%rax, 80(%rsp)
	movq	%rcx, 88(%rsp)
	movq	56(%rsp), %r14
	cmpq	$3, %r14
	movq	464(%rsp), %rdx
	jne	.LBB13_7
	jmp	.LBB13_23
.LBB13_27:
	movl	$136, %edx
	callq	_RNvNtNtCs1gUZZmupoa8_4core5slice5index16slice_index_fail
.LBB13_28:
	movl	$136, %edx
	movq	%r15, %rdi
	callq	_RNvNtNtCs1gUZZmupoa8_4core5slice5index16slice_index_fail
.LBB13_24:
	movl	52(%rsp), %eax
	movl	%eax, 112(%rsp)
	movq	8(%rsp), %rax
	movw	%ax, 116(%rsp)
	movl	48(%rsp), %eax
	movb	%al, 118(%rsp)
	movb	$2, 119(%rsp)
	movq	$0, 120(%rsp)
	leaq	2352(%rsp), %rbx
	movl	$344, %edx
	movq	%rbx, %rdi
	xorl	%esi, %esi
	callq	*memset@GOTPCREL(%rip)
	movl	$16, %edx
	movq	%rbx, %rdi
	movq	104(%rsp), %rsi
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	leaq	112(%rsp), %rsi
	movl	$16, %edx
	movq	%rbx, %rdi
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	leaq	1080(%rsp), %rsi
	movl	$928, %edx
	movq	%rbx, %rdi
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	leaq	1048(%rsp), %rdi
	movq	%rbx, %rsi
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher8finalize
	movzwl	670(%rsp), %eax
	movw	%ax, 168(%rsp)
	movq	662(%rsp), %rax
	movq	%rax, 160(%rsp)
	movq	654(%rsp), %rax
	movq	%rax, 152(%rsp)
	movq	646(%rsp), %rax
	movq	%rax, 144(%rsp)
	movq	638(%rsp), %rax
	movq	%rax, 136(%rsp)
	movq	630(%rsp), %rax
	movq	%rax, 128(%rsp)
	movq	614(%rsp), %rax
	movq	622(%rsp), %rcx
	movq	%rcx, 120(%rsp)
	movq	%rax, 112(%rsp)
	movq	1048(%rsp), %rax
	movq	1056(%rsp), %rcx
	movq	%rax, 170(%rsp)
	movq	%rcx, 178(%rsp)
	movq	96(%rsp), %rbx
	leaq	1(%rbx), %rdi
	leaq	112(%rsp), %rsi
	movl	$74, %edx
	callq	*memcpy@GOTPCREL(%rip)
	movb	$1, (%rbx)
	jmp	.LBB13_26
.LBB13_29:
	xorl	%edi, %edi
	movq	%r15, %rsi
	callq	_RNvNtNtCs1gUZZmupoa8_4core5slice5index16slice_index_fail
.Lfunc_end13:
	.size	_RNvNtCs7Pyp4CbMBld_9lean_xmss4wots9wots_leaf, .Lfunc_end13-_RNvNtCs7Pyp4CbMBld_9lean_xmss4wots9wots_leaf
	.cfi_endproc

	.type	.Lanon.5ef9b7c546f4dc64388b910df55ec241.1,@object
	.section	.rodata..Lanon.5ef9b7c546f4dc64388b910df55ec241.1,"a",@progbits
	.p2align	3, 0x0
.Lanon.5ef9b7c546f4dc64388b910df55ec241.1:
	.ascii	"\001\000\000\000\000\000\000\000\202\200\000\000\000\000\000\000\212\200\000\000\000\000\000\200\000\200\000\200\000\000\000\200\213\200\000\000\000\000\000\000\001\000\000\200\000\000\000\000\201\200\000\200\000\000\000\200\t\200\000\000\000\000\000\200\212\000\000\000\000\000\000\000\210\000\000\000\000\000\000\000\t\200\000\200\000\000\000\000\n\000\000\200\000\000\000\000\213\200\000\200\000\000\000\000\213\000\000\000\000\000\000\200\211\200\000\000\000\000\000\200\003\200\000\000\000\000\000\200\002\200\000\000\000\000\000\200\200\000\000\000\000\000\000\200\n\200\000\000\000\000\000\000\n\000\000\200\000\000\000\200\201\200\000\200\000\000\000\200\200\200\000\000\000\000\000\200\001\000\000\200\000\000\000\000\b\200\000\200\000\000\000\200"
	.size	.Lanon.5ef9b7c546f4dc64388b910df55ec241.1, 192

	.type	.Lanon.440213f1c62d8b61420e6860e9721951.8,@object
	.section	.rodata..Lanon.440213f1c62d8b61420e6860e9721951.8,"a",@progbits
	.p2align	3, 0x0
.Lanon.440213f1c62d8b61420e6860e9721951.8:
	.asciz	"\b\000\000\000\000\000\000\000\b\000\000\000\000\000\000\000\n\000\000\000\000\000\000"
	.size	.Lanon.440213f1c62d8b61420e6860e9721951.8, 24

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
	.byte	54
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
	.long	.Ldebug_info_end0-.Ldebug_info_start0
.Ldebug_info_start0:
	.short	4
	.long	.debug_abbrev
	.byte	8
	.byte	1
	.long	.Linfo_string0
	.short	28
	.long	.Linfo_string1
	.long	.Lline_table_start0
	.long	.Linfo_string2
	.quad	0
	.long	.Ldebug_ranges0
	.byte	2
	.long	.Linfo_string3
	.byte	2
	.long	.Linfo_string4
	.byte	3
	.quad	.Lfunc_begin5
	.long	.Lfunc_end5-.Lfunc_begin5
	.byte	1
	.byte	86
	.long	.Linfo_string8
	.long	.Linfo_string9
	.byte	1
	.byte	60
	.byte	3


	.byte	3
	.quad	.Lfunc_begin7
	.long	.Lfunc_end7-.Lfunc_begin7
	.byte	1
	.byte	86
	.long	.Linfo_string12
	.long	.Linfo_string13
	.byte	1
	.byte	138
	.byte	3


	.byte	0
	.byte	2
	.long	.Linfo_string5
	.byte	2
	.long	.Linfo_string6
	.byte	3
	.quad	.Lfunc_begin6
	.long	.Lfunc_end6-.Lfunc_begin6
	.byte	1
	.byte	86
	.long	.Linfo_string10
	.long	.Linfo_string11
	.byte	2
	.byte	39
	.byte	3


	.byte	0
	.byte	0
	.byte	2
	.long	.Linfo_string7
	.byte	4
	.quad	.Lfunc_begin8
	.long	.Lfunc_end8-.Lfunc_begin8
	.byte	1
	.byte	86
	.long	.Linfo_string14
	.long	.Linfo_string15
	.byte	4
	.short	2247
	.byte	3


	.byte	0
	.byte	0
	.byte	0
.Ldebug_info_end0:
	.section	.text.unlikely._RNvNtCs1gUZZmupoa8_4core9panicking9panic_fmt,"ax",@progbits
.Lsec_end0:
	.section	.text.unlikely._RNvNtNtCs1gUZZmupoa8_4core5slice5index16slice_index_fail,"ax",@progbits
.Lsec_end1:
	.section	.text.unlikely._RNvNtCs1gUZZmupoa8_4core9panicking5panic,"ax",@progbits
.Lsec_end2:
	.section	.text.unlikely._RNvNtCs1gUZZmupoa8_4core6option13unwrap_failed,"ax",@progbits
.Lsec_end3:
	.section	.debug_aranges,"",@progbits
	.long	92
	.short	2
	.long	.Lcu_begin0
	.byte	8
	.byte	0
	.zero	4,255
	.quad	.Lfunc_begin5
	.quad	.Lsec_end0-.Lfunc_begin5
	.quad	.Lfunc_begin6
	.quad	.Lsec_end1-.Lfunc_begin6
	.quad	.Lfunc_begin7
	.quad	.Lsec_end2-.Lfunc_begin7
	.quad	.Lfunc_begin8
	.quad	.Lsec_end3-.Lfunc_begin8
	.quad	0
	.quad	0
	.section	.debug_ranges,"",@progbits
.Ldebug_ranges0:
	.quad	.Lfunc_begin5
	.quad	.Lfunc_end5
	.quad	.Lfunc_begin6
	.quad	.Lfunc_end6
	.quad	.Lfunc_begin7
	.quad	.Lfunc_end7
	.quad	.Lfunc_begin8
	.quad	.Lfunc_end8
	.quad	0
	.quad	0
	.section	.debug_str,"MS",@progbits,1
.Linfo_string0:
	.asciz	"clang LLVM (rustc version 1.99.1 (58cf8f9c3 2026-10-13))"
.Linfo_string1:
	.asciz	"/rustc/58cf8f9c35b355199727627d07ae34a4e2846d67/library/core/src/lib.rs/@/core.ed37fd7903368ee-cgu.0"
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
	.asciz	"option"
.Linfo_string8:
	.asciz	"_RNvNtCs1gUZZmupoa8_4core9panicking9panic_fmt"
.Linfo_string9:
	.asciz	"panic_fmt"
.Linfo_string10:
	.asciz	"_RNvNtNtCs1gUZZmupoa8_4core5slice5index16slice_index_fail"
.Linfo_string11:
	.asciz	"slice_index_fail"
.Linfo_string12:
	.asciz	"_RNvNtCs1gUZZmupoa8_4core9panicking5panic"
.Linfo_string13:
	.asciz	"panic"
.Linfo_string14:
	.asciz	"_RNvNtCs1gUZZmupoa8_4core6option13unwrap_failed"
.Linfo_string15:
	.asciz	"unwrap_failed"
	.ident	"rustc version 1.99.1 (58cf8f9c3 2026-10-13)"
	.section	".note.GNU-stack","",@progbits
	.section	.debug_line,"",@progbits
.Lline_table_start0:
