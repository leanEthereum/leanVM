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
	subq	$1096, %rsp
	.cfi_def_cfa_offset 21632
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	%rdx, %rbx
	movq	%rsi, 8(%rsp)
	movq	16(%rdi), %rax
	movq	24(%rdi), %rcx
	movq	%rcx, 136(%rsp)
	movq	%rax, 128(%rsp)
	movq	(%rdi), %rax
	movq	8(%rdi), %rcx
	movq	%rax, 112(%rsp)
	movq	%rcx, 120(%rsp)
	leaq	576(%rsp), %r15
	movl	$176, %r12d
	leaq	12780(%rsp), %r14
	leaq	560(%rsp), %r13
	movq	memcpy@GOTPCREL(%rip), %rbp
	.p2align	4
.LBB3_1:
	movq	-160(%rbx,%r12), %rax
	movq	-152(%rbx,%r12), %rcx
	leaq	12940(%rsp), %rdx
	movq	%rcx, 8(%rdx)
	movq	%rax, (%rdx)
	movq	-144(%rbx,%r12), %rax
	movq	-136(%rbx,%r12), %rcx
	movq	%rcx, 568(%rsp)
	movq	%rax, 560(%rsp)
	movq	-128(%rbx,%r12), %rax
	movq	-120(%rbx,%r12), %rcx
	movq	%rcx, 8(%r15)
	movq	%rax, (%r15)
	movq	-112(%rbx,%r12), %rax
	movq	-104(%rbx,%r12), %rcx
	movq	%rcx, 24(%r15)
	movq	%rax, 16(%r15)
	movq	-96(%rbx,%r12), %rax
	movq	-88(%rbx,%r12), %rcx
	movq	%rcx, 40(%r15)
	movq	%rax, 32(%r15)
	movq	-80(%rbx,%r12), %rax
	movq	-72(%rbx,%r12), %rcx
	movq	%rcx, 56(%r15)
	movq	%rax, 48(%r15)
	movq	-64(%rbx,%r12), %rax
	movq	-56(%rbx,%r12), %rcx
	movq	%rcx, 72(%r15)
	movq	%rax, 64(%r15)
	movq	-48(%rbx,%r12), %rax
	movq	-40(%rbx,%r12), %rcx
	movq	%rcx, 88(%r15)
	movq	%rax, 80(%r15)
	movq	-32(%rbx,%r12), %rax
	movq	-24(%rbx,%r12), %rcx
	movq	%rcx, 104(%r15)
	movq	%rax, 96(%r15)
	movq	-16(%rbx,%r12), %rax
	movq	-8(%rbx,%r12), %rcx
	movq	%rcx, 120(%r15)
	movq	%rax, 112(%r15)
	movq	(%rbx,%r12), %rax
	movq	8(%rbx,%r12), %rcx
	movq	%rcx, 136(%r15)
	movq	%rax, 128(%r15)
	movl	$160, %edx
	movq	%r14, %rdi
	movq	%r13, %rsi
	callq	*%rbp
	movl	$176, %edx
	movq	%r13, %rdi
	movq	%r14, %rsi
	callq	*%rbp
	leaq	(%rsp,%r12), %rdi
	addq	$3896, %rdi
	movl	$176, %edx
	movq	%r13, %rsi
	callq	*%rbp
	addq	$176, %r12
	cmpq	$4400, %r12
	jne	.LBB3_1
	leaq	1720(%rsp), %r14
	xorl	%r15d, %r15d
	movl	$288, %edx
	movq	%r14, %rdi
	xorl	%esi, %esi
	callq	*memset@GOTPCREL(%rip)
	movl	4240(%rbx), %eax
	movl	%eax, 24(%rsp)
	.p2align	4
.LBB3_3:
	movq	4244(%rbx,%r15), %rax
	movq	4252(%rbx,%r15), %rcx
	movq	%rcx, 12788(%rsp,%r15)
	movq	%rax, 12780(%rsp,%r15)
	movq	4260(%rbx,%r15), %rax
	movq	4268(%rbx,%r15), %rcx
	movq	%rax, 12796(%rsp,%r15)
	movq	%rcx, 12804(%rsp,%r15)
	addq	$32, %r15
	cmpq	$1024, %r15
	jne	.LBB3_3
	leaq	560(%rsp), %r13
	leaq	12780(%rsp), %rsi
	movl	$1024, %edx
	movq	%r13, %rdi
	movq	memcpy@GOTPCREL(%rip), %r15
	callq	*%r15
	movq	5268(%rbx), %rax
	movq	5276(%rbx), %rcx
	movq	%rcx, 1600(%rsp)
	movq	%rax, 1592(%rsp)
	movq	5284(%rbx), %rax
	movq	5292(%rbx), %rcx
	movq	%rcx, 1616(%rsp)
	movq	%rax, 1608(%rsp)
	movq	5300(%rbx), %rax
	movq	5308(%rbx), %rcx
	movq	%rcx, 1632(%rsp)
	movq	%rax, 1624(%rsp)
	movq	5316(%rbx), %rax
	movq	5324(%rbx), %rcx
	movq	%rcx, 1648(%rsp)
	movq	%rax, 1640(%rsp)
	movq	5332(%rbx), %rax
	movq	5340(%rbx), %rcx
	movq	%rcx, 1664(%rsp)
	movq	%rax, 1656(%rsp)
	movq	5348(%rbx), %rax
	movq	5356(%rbx), %rcx
	movq	%rcx, 1680(%rsp)
	movq	%rax, 1672(%rsp)
	movq	5364(%rbx), %rax
	movq	5372(%rbx), %rcx
	movq	%rcx, 1696(%rsp)
	movq	%rax, 1688(%rsp)
	movq	5380(%rbx), %rax
	movq	5388(%rbx), %rcx
	movq	%rcx, 1712(%rsp)
	movq	%rax, 1704(%rsp)
	leaq	2024(%rsp), %rbp
	movl	$1024, %edx
	movq	%rbp, %rdi
	movq	%r13, %rsi
	callq	*%r15
	leaq	3048(%rsp), %r13
	movl	$1024, %edx
	movq	%r13, %rdi
	movq	%rbp, %rsi
	callq	*%r15
	leaq	11368(%rsp), %rbp
	movl	$1024, %edx
	movq	%rbp, %rdi
	movq	%r13, %rsi
	callq	*%r15
	leaq	10344(%rsp), %r13
	movl	$1024, %edx
	movq	%r13, %rdi
	movq	%rbp, %rsi
	callq	*%r15
	leaq	9320(%rsp), %rdi
	movl	$1024, %edx
	movq	%r13, %rsi
	callq	*%r15
	movl	5396(%rbx), %r12d
	xorl	%eax, %eax
	.p2align	4
.LBB3_5:
	movq	5400(%rbx,%rax), %rcx
	movq	5408(%rbx,%rax), %rdx
	movq	%rdx, 12788(%rsp,%rax)
	movq	%rcx, 12780(%rsp,%rax)
	movq	5416(%rbx,%rax), %rcx
	movq	5424(%rbx,%rax), %rdx
	movq	%rcx, 12796(%rsp,%rax)
	movq	%rdx, 12804(%rsp,%rax)
	addq	$32, %rax
	cmpq	$1024, %rax
	jne	.LBB3_5
	leaq	560(%rsp), %r13
	leaq	12780(%rsp), %rsi
	movl	$1024, %edx
	movq	%r13, %rdi
	movq	memcpy@GOTPCREL(%rip), %r15
	callq	*%r15
	movq	6424(%rbx), %rax
	movq	6432(%rbx), %rcx
	movq	%rcx, 8(%r14)
	movq	%rax, (%r14)
	movq	6440(%rbx), %rax
	movq	6448(%rbx), %rcx
	movq	%rcx, 1744(%rsp)
	movq	%rax, 1736(%rsp)
	movq	6456(%rbx), %rax
	movq	6464(%rbx), %rcx
	movq	%rcx, 1760(%rsp)
	movq	%rax, 1752(%rsp)
	movq	6472(%rbx), %rax
	movq	6480(%rbx), %rcx
	movq	%rcx, 1776(%rsp)
	movq	%rax, 1768(%rsp)
	movq	6488(%rbx), %rax
	movq	6496(%rbx), %rcx
	movq	%rcx, 1792(%rsp)
	movq	%rax, 1784(%rsp)
	movq	6504(%rbx), %rax
	movq	6512(%rbx), %rcx
	movq	%rcx, 1808(%rsp)
	movq	%rax, 1800(%rsp)
	movq	6520(%rbx), %rax
	movq	6528(%rbx), %rcx
	movq	%rax, 1816(%rsp)
	movq	%rcx, 1824(%rsp)
	movq	6536(%rbx), %rax
	movq	6544(%rbx), %rcx
	movq	%rax, 1832(%rsp)
	movq	%rcx, 1840(%rsp)
	leaq	2024(%rsp), %r14
	movl	$1024, %edx
	movq	%r14, %rdi
	movq	%r13, %rsi
	callq	*%r15
	leaq	3048(%rsp), %r13
	movl	$1024, %edx
	movq	%r13, %rdi
	movq	%r14, %rsi
	callq	*%r15
	leaq	11368(%rsp), %r14
	movl	$1024, %edx
	movq	%r14, %rdi
	movq	%r13, %rsi
	callq	*%r15
	leaq	10344(%rsp), %r13
	movl	$1024, %edx
	movq	%r13, %rdi
	movq	%r14, %rsi
	callq	*%r15
	leaq	8296(%rsp), %rdi
	movl	$1024, %edx
	movq	%r13, %rsi
	callq	*%r15
	movl	6552(%rbx), %r15d
	xorl	%eax, %eax
	.p2align	4
.LBB3_7:
	movq	6556(%rbx,%rax), %rcx
	movq	6564(%rbx,%rax), %rdx
	movq	%rdx, 12788(%rsp,%rax)
	movq	%rcx, 12780(%rsp,%rax)
	movq	6572(%rbx,%rax), %rcx
	movq	6580(%rbx,%rax), %rdx
	movq	%rcx, 12796(%rsp,%rax)
	movq	%rdx, 12804(%rsp,%rax)
	addq	$32, %rax
	cmpq	$1024, %rax
	jne	.LBB3_7
	leaq	560(%rsp), %r14
	leaq	12780(%rsp), %rsi
	movl	$1024, %edx
	movq	%r14, %rdi
	movq	memcpy@GOTPCREL(%rip), %rbp
	callq	*%rbp
	movq	7580(%rbx), %rax
	movq	7588(%rbx), %rcx
	movq	%rcx, 1856(%rsp)
	movq	%rax, 1848(%rsp)
	movq	7596(%rbx), %rax
	movq	7604(%rbx), %rcx
	movq	%rcx, 1872(%rsp)
	movq	%rax, 1864(%rsp)
	movq	7612(%rbx), %rax
	movq	7620(%rbx), %rcx
	movq	%rcx, 1888(%rsp)
	movq	%rax, 1880(%rsp)
	movq	7628(%rbx), %rax
	movq	7636(%rbx), %rcx
	movq	%rcx, 1904(%rsp)
	movq	%rax, 1896(%rsp)
	movq	7644(%rbx), %rax
	movq	7652(%rbx), %rcx
	movq	%rcx, 1920(%rsp)
	movq	%rax, 1912(%rsp)
	movq	7660(%rbx), %rax
	movq	7668(%rbx), %rcx
	movq	%rcx, 1936(%rsp)
	movq	%rax, 1928(%rsp)
	movq	7676(%rbx), %rax
	movq	7684(%rbx), %rcx
	movq	%rcx, 1952(%rsp)
	movq	%rax, 1944(%rsp)
	movq	7692(%rbx), %rax
	movq	7700(%rbx), %rcx
	movq	%rcx, 1968(%rsp)
	movq	%rax, 1960(%rsp)
	movq	7708(%rbx), %rax
	movq	7716(%rbx), %rcx
	movq	%rcx, 1984(%rsp)
	movq	%rax, 1976(%rsp)
	bswapl	%r12d
	movl	%r12d, 16(%rsp)
	movl	24(%rsp), %r12d
	bswapl	%r12d
	movq	7724(%rbx), %rax
	movq	7732(%rbx), %rcx
	movq	%rcx, 2000(%rsp)
	movq	%rax, 1992(%rsp)
	bswapl	%r15d
	leaq	2024(%rsp), %r13
	movl	$1024, %edx
	movq	%r13, %rdi
	movq	%r14, %rsi
	callq	*%rbp
	leaq	3048(%rsp), %r14
	movl	$1024, %edx
	movq	%r14, %rdi
	movq	%r13, %rsi
	callq	*%rbp
	leaq	11368(%rsp), %r13
	movl	$1024, %edx
	movq	%r13, %rdi
	movq	%r14, %rsi
	callq	*%rbp
	leaq	10344(%rsp), %r14
	movl	$1024, %edx
	movq	%r14, %rdi
	movq	%r13, %rsi
	callq	*%rbp
	leaq	17420(%rsp), %r13
	movq	(%rbx), %rax
	movq	8(%rbx), %rcx
	movq	%rax, 17420(%rsp)
	movq	%rcx, 17428(%rsp)
	leaq	12780(%rsp), %rdi
	leaq	4072(%rsp), %rsi
	movl	$4224, %edx
	callq	*%rbp
	leaq	17436(%rsp), %rdi
	leaq	9320(%rsp), %rsi
	movl	$1024, %edx
	movq	%rdi, 184(%rsp)
	callq	*%rbp
	movl	%r12d, 18460(%rsp)
	leaq	18464(%rsp), %rdi
	leaq	8296(%rsp), %rsi
	movl	$1024, %edx
	callq	*%rbp
	movl	16(%rsp), %eax
	movl	%eax, 19488(%rsp)
	leaq	19492(%rsp), %rdi
	movl	$1024, %edx
	movq	%r14, %rsi
	callq	*%rbp
	movl	%r15d, 20516(%rsp)
	leaq	17004(%rsp), %rdi
	leaq	1592(%rsp), %rsi
	movl	$416, %edx
	callq	*%rbp
	leaq	560(%rsp), %r14
	xorl	%r12d, %r12d
	movl	$344, %edx
	movq	%r14, %rdi
	xorl	%esi, %esi
	callq	*memset@GOTPCREL(%rip)
	movl	$16, %edx
	movq	%r14, %rdi
	movq	%r13, %rsi
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	leaq	112(%rsp), %rsi
	movl	$16, %edx
	movq	%r14, %rdi
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	movl	$16, %edx
	movq	%r14, %rdi
	leaq	128(%rsp), %rsi
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	movl	$32, %edx
	movq	%r14, %rdi
	movq	8(%rsp), %rsi
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	leaq	4072(%rsp), %r13
	movl	$344, %edx
	movq	%r13, %rdi
	movq	%r14, %rsi
	callq	*%rbp
	movl	$0, 3048(%rsp)
	leaq	3048(%rsp), %rbx
	movl	$4, %edx
	movq	%r13, %rdi
	movq	%rbx, %rsi
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	leaq	10344(%rsp), %r15
	movq	%r15, %rdi
	movq	%r13, %rsi
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher8finalize
	movq	10368(%rsp), %rax
	movq	%rax, 2048(%rsp)
	movq	10360(%rsp), %rax
	movq	%rax, 2040(%rsp)
	movq	10344(%rsp), %rax
	movq	10352(%rsp), %rcx
	movq	%rcx, 2032(%rsp)
	movq	%rax, 2024(%rsp)
	movl	$344, %edx
	movq	%r13, %rdi
	movq	%r14, %rsi
	callq	*%rbp
	movl	$16777216, 3048(%rsp)
	movl	$4, %edx
	movq	%r13, %rdi
	movq	%rbx, %rsi
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	movq	%r15, %rdi
	movq	%r13, %rsi
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher8finalize
	movq	10368(%rsp), %rax
	movq	%rax, 2080(%rsp)
	movq	10360(%rsp), %rax
	movq	%rax, 2072(%rsp)
	movq	10344(%rsp), %rax
	movq	10352(%rsp), %rcx
	movq	%rcx, 2064(%rsp)
	movq	%rax, 2056(%rsp)
	.p2align	4
.LBB3_9:
	movq	%r12, %rax
	shrq	$3, %rax
	leaq	2(%r12), %rsi
	movq	%rsi, %r15
	shrq	$3, %r15
	leaq	4(%r12), %rdx
	movq	%rdx, %r14
	shrq	$3, %r14
	leaq	6(%r12), %r10
	movq	%r10, %r11
	shrq	$3, %r11
	leaq	8(%r12), %r9
	shrq	$3, %r9
	leaq	9(%r12), %r8
	movq	%r8, %rcx
	shrq	$3, %rcx
	movq	%rcx, 8(%rsp)
	movzbl	2024(%rsp,%rax), %ebp
	movq	%r13, %rax
	movl	%r12d, %r13d
	andb	$6, %r13b
	movl	%r13d, %edi
	xorb	$7, %dil
	movl	%ebp, %ebx
	movl	%edi, %ecx
	shrb	%cl, %bl
	addb	%bl, %bl
	andb	$2, %bl
	xorb	$6, %r13b
	movzbl	%r13b, %ecx
	movq	%rax, %r13
	btl	%ecx, %ebp
	setb	%bpl
	movzbl	2024(%rsp,%r15), %r15d
	andb	$6, %sil
	xorb	$7, %sil
	movl	%esi, %ecx
	shrb	%cl, %r15b
	orb	%bl, %bpl
	shlb	$2, %bpl
	addb	%r15b, %r15b
	andb	$2, %r15b
	orb	%bpl, %r15b
	leaq	3(%r12), %rcx
	movq	%rcx, %rsi
	shrq	$3, %rsi
	notb	%cl
	movzbl	2024(%rsp,%rsi), %esi
	movzbl	%cl, %ecx
	andl	$6, %ecx
	btl	%ecx, %esi
	setb	%sil
	orb	%r15b, %sil
	shlb	$2, %sil
	movzbl	2024(%rsp,%r14), %ebx
	andb	$6, %dl
	xorb	$7, %dl
	movl	%edx, %ecx
	shrb	%cl, %bl
	addb	%bl, %bl
	andb	$2, %bl
	orb	%sil, %bl
	leaq	5(%r12), %rcx
	movq	%rcx, %rdx
	shrq	$3, %rdx
	notb	%cl
	movzbl	2024(%rsp,%rdx), %edx
	movzbl	%cl, %ecx
	andl	$6, %ecx
	btl	%ecx, %edx
	setb	%cl
	orb	%bl, %cl
	addb	%cl, %cl
	andb	$6, %r10b
	xorb	$7, %r10b
	movzbl	2024(%rsp,%r11), %edx
	movzbl	%r10b, %esi
	btl	%esi, %edx
	setb	%dl
	orb	%cl, %dl
	movzbl	%dl, %edx
	leaq	7(%r12), %rcx
	movq	%rcx, %rsi
	shrq	$3, %rsi
	movzbl	2024(%rsp,%rsi), %esi
	notb	%cl
	andb	$6, %cl
	shrq	%cl, %rsi
	andl	$1, %esi
	addl	%esi, %esi
	leal	(%rsi,%rdx,4), %ecx
	movzbl	2024(%rsp,%r9), %edx
	movzbl	%dil, %eax
	xorl	%esi, %esi
	btl	%eax, %edx
	setb	%sil
	orl	%ecx, %esi
	movq	8(%rsp), %rax
	movzbl	2024(%rsp,%rax), %eax
	notb	%r8b
	movzbl	%r8b, %ecx
	andl	$6, %ecx
	xorl	%edx, %edx
	btl	%ecx, %eax
	setb	%dl
	leaq	(%rdx,%rsi,2), %rax
	movq	%rax, (%r13)
	addq	$10, %r12
	addq	$8, %r13
	cmpq	$240, %r12
	jne	.LBB3_9
	leaq	10352(%rsp), %rdi
	movzbl	2054(%rsp), %eax
	movzbl	2055(%rsp), %ebx
	movzbl	2056(%rsp), %ecx
	shll	$16, %eax
	shll	$8, %ebx
	orl	%eax, %ebx
	orl	%ecx, %ebx
	shll	$8, %ebx
	andl	$67108608, %ebx
	movzbl	2057(%rsp), %ebp
	orl	%ebp, %ebx
	movq	%rbx, 10344(%rsp)
	leaq	4072(%rsp), %r12
	movl	$192, %edx
	movq	%r12, %rsi
	callq	*memcpy@GOTPCREL(%rip)
	movq	%rbx, 552(%rsp)
	movq	%rbx, %r13
	bswapq	%r13
	shlq	$8, %r13
	shll	$24, %ebp
	xorl	%esi, %esi
	movq	memset@GOTPCREL(%rip), %rbx
	leaq	112(%rsp), %r14
	leaq	560(%rsp), %r15
	movl	%ebp, 68(%rsp)
	movq	%r13, 80(%rsp)
.LBB3_11:
	movq	10352(%rsp,%rsi,8), %rcx
	imulq	$176, %rsi, %rax
	leaq	(%rsp,%rax), %rdx
	addq	$12780, %rdx
	movq	%rdx, 104(%rsp)
	leaq	12940(%rsp,%rax), %rax
	movq	%rax, 8(%rsp)
	movq	%rsi, 88(%rsp)
	movl	%esi, %eax
	shll	$10, %eax
	movq	%rcx, 72(%rsp)
	addl	%ecx, %eax
	bswapl	%eax
	movq	$0, 2024(%rsp)
	movq	%r13, 2032(%rsp)
	movl	$50331648, 2040(%rsp)
	movl	%ebp, 2044(%rsp)
	movl	$0, 2048(%rsp)
	movl	%eax, 2052(%rsp)
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
	leaq	2024(%rsp), %rsi
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	movl	$344, %edx
	movq	%r15, %rdi
	movq	%r12, %rsi
	movq	memcpy@GOTPCREL(%rip), %r14
	callq	*%r14
	movl	$16, %edx
	movq	%r15, %rdi
	movq	8(%rsp), %rsi
	movq	memset@GOTPCREL(%rip), %rbx
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	leaq	8296(%rsp), %rdi
	movq	%r15, %rsi
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher8finalize
	xorl	%ecx, %ecx
	movq	%r12, %r15
	leaq	2024(%rsp), %r12
	.p2align	4
.LBB3_12:
	movq	8296(%rsp), %rax
	movq	8304(%rsp), %rdx
	movq	%rdx, 9328(%rsp)
	movq	%rax, 9320(%rsp)
	movq	%rcx, %rax
	shlq	$4, %rax
	addq	104(%rsp), %rax
	movq	72(%rsp), %rdi
	btq	%rcx, %rdi
	movq	%rax, %r8
	leaq	9320(%rsp), %rdx
	cmovaeq	%rdx, %r8
	cmovbq	%rdx, %rax
	movl	%ecx, %edx
	movq	(%r8), %rsi
	movq	8(%r8), %r8
	movq	%r8, 11376(%rsp)
	movq	%rsi, 11368(%rsp)
	movq	(%rax), %r8
	movq	8(%rax), %rax
	leaq	11384(%rsp), %rsi
	movq	%rax, 8(%rsi)
	movq	%r8, (%rsi)
	incq	%rcx
	movq	%rdi, %rax
	shrq	%cl, %rax
	movq	%rcx, 56(%rsp)
	movl	%ecx, %esi
	bswapl	%esi
	movb	$9, %cl
	subb	%dl, %cl
	movq	88(%rsp), %rdx
	shll	%cl, %edx
	addl	%edx, %eax
	bswapl	%eax
	movq	$0, 3048(%rsp)
	movq	%r13, 3056(%rsp)
	movl	$50331648, 3064(%rsp)
	movl	%ebp, 3068(%rsp)
	movl	%esi, 3072(%rsp)
	movl	%eax, 3076(%rsp)
	movl	$344, %edx
	movq	%r15, %rdi
	xorl	%esi, %esi
	callq	*%rbx
	movq	112(%rsp), %rax
	movq	120(%rsp), %rcx
	leaq	4272(%rsp), %rdx
	movq	%rax, (%rdx)
	movq	%rcx, 8(%rdx)
	movq	4408(%rsp), %rdi
	addq	$16, %rdi
	movq	%rdi, 4408(%rsp)
	cmpq	$136, %rdi
	jne	.LBB3_14
	movq	4272(%rsp), %rax
	movq	%rax, 24(%rsp)
	movq	4280(%rsp), %rcx
	movq	4288(%rsp), %rdx
	movq	4296(%rsp), %rsi
	movq	4304(%rsp), %rdi
	movq	4312(%rsp), %r8
	movq	4320(%rsp), %r9
	movq	4328(%rsp), %r10
	movq	4336(%rsp), %r11
	movq	4344(%rsp), %rbx
	movq	4352(%rsp), %r15
	movq	4360(%rsp), %r13
	movq	4368(%rsp), %rbp
	movq	4376(%rsp), %r14
	movq	4384(%rsp), %r12
	movq	4392(%rsp), %rax
	movq	%rax, 8(%rsp)
	movq	4400(%rsp), %rax
	movq	%rax, 16(%rsp)
	movq	24(%rsp), %rax
	xorq	%rax, 4072(%rsp)
	xorq	%rcx, 4080(%rsp)
	xorq	%rdx, 4088(%rsp)
	xorq	%rsi, 4096(%rsp)
	xorq	%rdi, 4104(%rsp)
	xorq	%r8, 4112(%rsp)
	xorq	%r9, 4120(%rsp)
	xorq	%r10, 4128(%rsp)
	xorq	%r11, 4136(%rsp)
	xorq	%rbx, 4144(%rsp)
	xorq	%r15, 4152(%rsp)
	leaq	4072(%rsp), %r15
	xorq	%r13, 4160(%rsp)
	xorq	%rbp, 4168(%rsp)
	xorq	%r14, 4176(%rsp)
	movq	memcpy@GOTPCREL(%rip), %r14
	xorq	%r12, 4184(%rsp)
	leaq	2024(%rsp), %r12
	movq	8(%rsp), %rax
	xorq	%rax, 4192(%rsp)
	movq	16(%rsp), %rax
	xorq	%rax, 4200(%rsp)
	movq	%r15, %rdi
	callq	_RNvCsndc0WgnAaH_9keccak2568keccak_f
	movq	$0, 4408(%rsp)
	xorl	%edi, %edi
.LBB3_14:
	movl	$32, %ebx
	leaq	3048(%rsp), %rbp
	jmp	.LBB3_15
	.p2align	4
.LBB3_19:
	subq	%r13, %rbx
	addq	%r13, %rbp
	testq	%rbx, %rbx
	je	.LBB3_20
.LBB3_15:
	movl	$136, %r13d
	subq	%rdi, %r13
	cmpq	%r13, %rbx
	cmovbq	%rbx, %r13
	leaq	(%rdi,%r13), %rsi
	cmpq	%rdi, %rsi
	jb	.LBB3_78
	cmpq	$137, %rsi
	jae	.LBB3_78
	leaq	4272(%rsp), %rax
	addq	%rax, %rdi
	movq	%rbp, %rsi
	movq	%r13, %rdx
	callq	*%r14
	movq	4408(%rsp), %rdi
	addq	%r13, %rdi
	movq	%rdi, 4408(%rsp)
	cmpq	$136, %rdi
	jne	.LBB3_19
	movq	4272(%rsp), %rax
	movq	%rax, 24(%rsp)
	movq	4280(%rsp), %rcx
	movq	4288(%rsp), %rdx
	movq	4296(%rsp), %rsi
	movq	4304(%rsp), %rdi
	movq	4312(%rsp), %r8
	movq	4320(%rsp), %r9
	movq	4328(%rsp), %r10
	movq	4336(%rsp), %r11
	movq	4344(%rsp), %r14
	movq	4352(%rsp), %r15
	movq	4360(%rsp), %r12
	movq	4368(%rsp), %rax
	movq	%rax, 8(%rsp)
	movq	4376(%rsp), %rax
	movq	%rax, 16(%rsp)
	movq	4384(%rsp), %rax
	movq	%rax, 48(%rsp)
	movq	4392(%rsp), %rax
	movq	%rax, 40(%rsp)
	movq	4400(%rsp), %rax
	movq	%rax, 32(%rsp)
	movq	24(%rsp), %rax
	xorq	%rax, 4072(%rsp)
	xorq	%rcx, 4080(%rsp)
	xorq	%rdx, 4088(%rsp)
	xorq	%rsi, 4096(%rsp)
	xorq	%rdi, 4104(%rsp)
	xorq	%r8, 4112(%rsp)
	xorq	%r9, 4120(%rsp)
	xorq	%r10, 4128(%rsp)
	xorq	%r11, 4136(%rsp)
	xorq	%r14, 4144(%rsp)
	movq	memcpy@GOTPCREL(%rip), %r14
	xorq	%r15, 4152(%rsp)
	leaq	4072(%rsp), %r15
	xorq	%r12, 4160(%rsp)
	leaq	2024(%rsp), %r12
	movq	8(%rsp), %rax
	xorq	%rax, 4168(%rsp)
	movq	16(%rsp), %rax
	xorq	%rax, 4176(%rsp)
	movq	48(%rsp), %rax
	xorq	%rax, 4184(%rsp)
	movq	40(%rsp), %rax
	xorq	%rax, 4192(%rsp)
	movq	32(%rsp), %rax
	xorq	%rax, 4200(%rsp)
	movq	%r15, %rdi
	callq	_RNvCsndc0WgnAaH_9keccak2568keccak_f
	movq	$0, 4408(%rsp)
	xorl	%edi, %edi
	jmp	.LBB3_19
	.p2align	4
.LBB3_20:
	movl	$344, %edx
	leaq	560(%rsp), %rdi
	movq	%r15, %rsi
	callq	*%r14
	movl	$32, %ebx
	movq	896(%rsp), %r13
	leaq	11368(%rsp), %rbp
	jmp	.LBB3_21
	.p2align	4
.LBB3_25:
	subq	%r15, %rbx
	addq	%r15, %rbp
	testq	%rbx, %rbx
	je	.LBB3_26
.LBB3_21:
	movl	$136, %r15d
	subq	%r13, %r15
	cmpq	%r15, %rbx
	cmovbq	%rbx, %r15
	leaq	(%r15,%r13), %rsi
	cmpq	%r13, %rsi
	jb	.LBB3_79
	cmpq	$137, %rsi
	jae	.LBB3_79
	leaq	760(%rsp), %rax
	addq	%rax, %r13
	movq	%r13, %rdi
	movq	%rbp, %rsi
	movq	%r15, %rdx
	callq	*%r14
	movq	896(%rsp), %r13
	addq	%r15, %r13
	movq	%r13, 896(%rsp)
	cmpq	$136, %r13
	jne	.LBB3_25
	movq	760(%rsp), %rax
	movq	%rax, 24(%rsp)
	movq	768(%rsp), %rcx
	movq	776(%rsp), %rdx
	movq	784(%rsp), %rsi
	movq	792(%rsp), %rdi
	movq	800(%rsp), %r8
	movq	808(%rsp), %r9
	movq	816(%rsp), %r10
	movq	824(%rsp), %r11
	movq	832(%rsp), %r14
	movq	840(%rsp), %r12
	movq	848(%rsp), %r13
	movq	856(%rsp), %rax
	movq	%rax, 8(%rsp)
	movq	864(%rsp), %rax
	movq	%rax, 16(%rsp)
	movq	872(%rsp), %rax
	movq	%rax, 48(%rsp)
	movq	880(%rsp), %rax
	movq	%rax, 40(%rsp)
	movq	888(%rsp), %rax
	movq	%rax, 32(%rsp)
	movq	24(%rsp), %rax
	xorq	%rax, 560(%rsp)
	xorq	%rcx, 568(%rsp)
	xorq	%rdx, 576(%rsp)
	xorq	%rsi, 584(%rsp)
	xorq	%rdi, 592(%rsp)
	xorq	%r8, 600(%rsp)
	xorq	%r9, 608(%rsp)
	xorq	%r10, 616(%rsp)
	xorq	%r11, 624(%rsp)
	xorq	%r14, 632(%rsp)
	movq	memcpy@GOTPCREL(%rip), %r14
	xorq	%r12, 640(%rsp)
	leaq	2024(%rsp), %r12
	xorq	%r13, 648(%rsp)
	movq	8(%rsp), %rax
	xorq	%rax, 656(%rsp)
	movq	16(%rsp), %rax
	xorq	%rax, 664(%rsp)
	movq	48(%rsp), %rax
	xorq	%rax, 672(%rsp)
	movq	40(%rsp), %rax
	xorq	%rax, 680(%rsp)
	movq	32(%rsp), %rax
	xorq	%rax, 688(%rsp)
	leaq	560(%rsp), %rdi
	callq	_RNvCsndc0WgnAaH_9keccak2568keccak_f
	movq	$0, 896(%rsp)
	xorl	%r13d, %r13d
	jmp	.LBB3_25
	.p2align	4
.LBB3_26:
	movl	$200, %edx
	leaq	4072(%rsp), %r15
	movq	%r15, %rdi
	leaq	560(%rsp), %rsi
	callq	*%r14
	movl	$136, %edx
	cmpq	$137, %r13
	jae	.LBB3_80
	movq	%r12, %rdi
	xorl	%esi, %esi
	movq	memset@GOTPCREL(%rip), %rbx
	callq	*%rbx
	movq	%r12, %rdi
	leaq	760(%rsp), %rsi
	movq	%r13, %rdx
	callq	*%r14
	xorb	$1, 2024(%rsp,%r13)
	xorb	$-128, 2159(%rsp)
	movq	2024(%rsp), %rax
	xorq	%rax, 4072(%rsp)
	movq	2032(%rsp), %rax
	xorq	%rax, 4080(%rsp)
	movq	2040(%rsp), %rax
	xorq	%rax, 4088(%rsp)
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
	movq	%r15, %rdi
	callq	_RNvCsndc0WgnAaH_9keccak2568keccak_f
	movq	4072(%rsp), %rax
	movq	4080(%rsp), %rcx
	movq	%rcx, 2032(%rsp)
	movq	%rax, 2024(%rsp)
	movq	%rax, 8296(%rsp)
	movq	%rcx, 8304(%rsp)
	movq	56(%rsp), %rcx
	cmpq	$10, %rcx
	movl	68(%rsp), %ebp
	movq	80(%rsp), %r13
	jne	.LBB3_12
	movq	8296(%rsp), %rax
	movq	8304(%rsp), %rcx
	movq	88(%rsp), %rsi
	movq	%rsi, %rdx
	shlq	$4, %rdx
	movq	%rax, 12396(%rsp,%rdx)
	movq	%rcx, 12404(%rsp,%rdx)
	incq	%rsi
	cmpq	$24, %rsi
	movq	%r15, %r12
	leaq	112(%rsp), %r14
	leaq	560(%rsp), %r15
	jne	.LBB3_11
	movq	$0, 2024(%rsp)
	movq	%r13, 2032(%rsp)
	movl	$67108864, 2040(%rsp)
	movl	%ebp, 2044(%rsp)
	movq	$0, 2048(%rsp)
	leaq	4072(%rsp), %r12
	xorl	%ebx, %ebx
	movl	$344, %edx
	movq	%r12, %rdi
	xorl	%esi, %esi
	callq	*memset@GOTPCREL(%rip)
	leaq	112(%rsp), %rsi
	movl	$16, %edx
	movq	%r12, %rdi
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	leaq	2024(%rsp), %r13
	movl	$32, %edx
	movq	%r12, %rdi
	movq	%r13, %rsi
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	leaq	560(%rsp), %rbp
	movl	$344, %edx
	movq	%rbp, %rdi
	movq	%r12, %rsi
	callq	*memcpy@GOTPCREL(%rip)
	leaq	12396(%rsp), %rsi
	movl	$384, %edx
	movq	%rbp, %rdi
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	leaq	4072(%rsp), %rdi
	movq	%rbp, %rsi
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher8finalize
	movq	4072(%rsp), %rax
	movq	4080(%rsp), %rcx
	movq	%rcx, 152(%rsp)
	movq	%rax, 144(%rsp)
	movl	$4656, %ecx
	leaq	.Lanon.bee145f0cb2eac5728ff95be1b200579.2(%rip), %rdx
	leaq	144(%rsp), %r15
	xorl	%esi, %esi
	movq	memcpy@GOTPCREL(%rip), %r14
.LBB3_30:
	addq	$1028, %rcx
	movq	%rcx, 200(%rsp)
	cmpq	$1, %rsi
	setne	%al
	shlb	$3, %al
	addb	$8, %al
	testq	%rsi, %rsi
	movzbl	%al, %ecx
	cmovel	%ebx, %ecx
	movq	552(%rsp), %rdi
	shrq	%cl, %rdi
	movq	(%rdx,%rsi,8), %rcx
	movq	%rdi, %r8
	shrq	%cl, %r8
	movq	$-1, %rax
	movq	%rcx, 168(%rsp)
	shlq	%cl, %rax
	leaq	1(%rsi), %rcx
	movq	%rcx, 192(%rsp)
	notl	%eax
	andl	%eax, %edi
	movq	184(%rsp), %rax
	movl	1024(%rax), %ebx
	movq	%rsi, 96(%rsp)
	movl	%esi, %eax
	bswapl	%eax
	bswapq	%r8
	movq	%rdi, 208(%rsp)
	movl	%edi, %ecx
	bswapl	%ecx
	movl	%eax, 104(%rsp)
	movl	%eax, 2024(%rsp)
	movl	$0, 2028(%rsp)
	movq	%r8, 88(%rsp)
	movq	%r8, 2032(%rsp)
	movl	$117440512, 2040(%rsp)
	movl	%ecx, 68(%rsp)
	movl	%ecx, 2044(%rsp)
	movq	$0, 2048(%rsp)
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
	movl	%ebx, 2024(%rsp)
	movl	$4, %edx
	movq	%r12, %rdi
	movq	%r13, %rsi
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	movq	%rbp, %rdi
	movq	%r12, %rsi
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher8finalize
	movq	560(%rsp), %rax
	movq	568(%rsp), %rdx
	bswapq	%rax
	bswapq	%rdx
	leaq	561(%rsp), %rsi
	xorl	%edi, %edi
	.p2align	4
.LBB3_31:
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
	jne	.LBB3_31
	movzbl	560(%rsp), %edx
	movzbl	561(%rsp), %eax
	movzbl	562(%rsp), %ecx
	movzbl	563(%rsp), %esi
	movzbl	564(%rsp), %edi
	movzbl	565(%rsp), %r8d
	movzbl	566(%rsp), %r9d
	movzbl	567(%rsp), %r10d
	movzbl	568(%rsp), %r11d
	movzbl	569(%rsp), %ebx
	movzbl	570(%rsp), %r15d
	movzbl	571(%rsp), %r12d
	movzbl	572(%rsp), %r13d
	movq	%rax, 8(%rsp)
	movq	%rdx, 24(%rsp)
	addq	%rdx, %rax
	movq	%rcx, 48(%rsp)
	movq	%rsi, 16(%rsp)
	addq	%rsi, %rcx
	addq	%rax, %rcx
	movq	%rdi, 56(%rsp)
	movq	%r8, 40(%rsp)
	leaq	(%rdi,%r8), %rax
	movq	%r9, 32(%rsp)
	addq	%r9, %rax
	addq	%rcx, %rax
	movq	%r10, 544(%rsp)
	movq	%r11, 72(%rsp)
	leaq	(%r10,%r11), %rcx
	movq	%rbx, 80(%rsp)
	addq	%rbx, %rcx
	movq	%r15, 176(%rsp)
	addq	%r15, %rcx
	addq	%rax, %rcx
	movzbl	573(%rsp), %edx
	movq	%r12, 520(%rsp)
	movq	%r13, 536(%rsp)
	leaq	(%r12,%r13), %rax
	movq	%rdx, 528(%rsp)
	addq	%rdx, %rax
	movzbl	574(%rsp), %edx
	movq	%rdx, 512(%rsp)
	addq	%rdx, %rax
	movzbl	575(%rsp), %edx
	movq	%rdx, 504(%rsp)
	addq	%rdx, %rax
	addq	%rcx, %rax
	movzbl	576(%rsp), %ecx
	movzbl	577(%rsp), %edx
	movzbl	578(%rsp), %esi
	movq	%rcx, 480(%rsp)
	movq	%rdx, 496(%rsp)
	addq	%rdx, %rcx
	movq	%rsi, 488(%rsp)
	addq	%rsi, %rcx
	movzbl	579(%rsp), %edx
	movq	%rdx, 472(%rsp)
	addq	%rdx, %rcx
	movzbl	580(%rsp), %edx
	movq	%rdx, 464(%rsp)
	addq	%rdx, %rcx
	movzbl	581(%rsp), %edx
	movq	%rdx, 456(%rsp)
	addq	%rdx, %rcx
	addq	%rax, %rcx
	movzbl	582(%rsp), %eax
	movzbl	583(%rsp), %edx
	movzbl	584(%rsp), %esi
	movq	%rax, 432(%rsp)
	movq	%rdx, 448(%rsp)
	addq	%rdx, %rax
	movq	%rsi, 440(%rsp)
	addq	%rsi, %rax
	movzbl	585(%rsp), %edx
	movq	%rdx, 424(%rsp)
	addq	%rdx, %rax
	movzbl	586(%rsp), %edx
	movq	%rdx, 416(%rsp)
	addq	%rdx, %rax
	movzbl	587(%rsp), %edx
	movq	%rdx, 408(%rsp)
	addq	%rdx, %rax
	movzbl	588(%rsp), %edx
	movq	%rdx, 400(%rsp)
	addq	%rdx, %rax
	addq	%rcx, %rax
	movzbl	589(%rsp), %ecx
	movzbl	590(%rsp), %edx
	movzbl	591(%rsp), %esi
	movq	%rcx, 376(%rsp)
	movq	%rdx, 392(%rsp)
	addq	%rdx, %rcx
	movq	%rsi, 384(%rsp)
	addq	%rsi, %rcx
	movzbl	592(%rsp), %edx
	movq	%rdx, 368(%rsp)
	addq	%rdx, %rcx
	movzbl	593(%rsp), %edx
	movq	%rdx, 360(%rsp)
	addq	%rdx, %rcx
	movzbl	594(%rsp), %edx
	movq	%rdx, 352(%rsp)
	addq	%rdx, %rcx
	movzbl	595(%rsp), %edx
	movq	%rdx, 344(%rsp)
	addq	%rdx, %rcx
	movzbl	596(%rsp), %edx
	movq	%rdx, 336(%rsp)
	addq	%rdx, %rcx
	addq	%rax, %rcx
	movzbl	597(%rsp), %eax
	movzbl	598(%rsp), %edx
	movzbl	599(%rsp), %esi
	movq	%rax, 312(%rsp)
	movq	%rdx, 328(%rsp)
	addq	%rdx, %rax
	movq	%rsi, 320(%rsp)
	addq	%rsi, %rax
	movzbl	600(%rsp), %edx
	movq	%rdx, 304(%rsp)
	addq	%rdx, %rax
	movzbl	601(%rsp), %edx
	movq	%rdx, 296(%rsp)
	addq	%rdx, %rax
	movzbl	602(%rsp), %edx
	movq	%rdx, 288(%rsp)
	addq	%rdx, %rax
	movzbl	603(%rsp), %edx
	movq	%rdx, 280(%rsp)
	addq	%rdx, %rax
	movzbl	604(%rsp), %edx
	movq	%rdx, 272(%rsp)
	addq	%rdx, %rax
	movzbl	605(%rsp), %edx
	movq	%rdx, 264(%rsp)
	addq	%rdx, %rax
	addq	%rcx, %rax
	movzbl	606(%rsp), %ecx
	movzbl	607(%rsp), %edx
	movzbl	608(%rsp), %esi
	movq	%rcx, 240(%rsp)
	movq	%rdx, 256(%rsp)
	leaq	(%rcx,%rdx), %r12
	movq	%rsi, 248(%rsp)
	addq	%rsi, %r12
	movzbl	609(%rsp), %ecx
	movq	%rcx, 232(%rsp)
	addq	%rcx, %r12
	movzbl	610(%rsp), %ecx
	movq	%rcx, 224(%rsp)
	addq	%rcx, %r12
	movzbl	611(%rsp), %ecx
	movq	%rcx, 216(%rsp)
	addq	%rcx, %r12
	movzbl	612(%rsp), %ecx
	movq	%rcx, %rbp
	addq	%rcx, %r12
	movzbl	613(%rsp), %ecx
	addq	%rcx, %r12
	movzbl	614(%rsp), %edx
	addq	%rdx, %r12
	movzbl	615(%rsp), %esi
	addq	%rsi, %r12
	addq	%rax, %r12
	movzbl	616(%rsp), %edi
	movzbl	617(%rsp), %r8d
	movzbl	618(%rsp), %r9d
	leaq	(%rdi,%r8), %r13
	addq	%r9, %r13
	movzbl	619(%rsp), %r10d
	addq	%r10, %r13
	movzbl	620(%rsp), %r11d
	addq	%r11, %r13
	movzbl	621(%rsp), %ebx
	addq	%rbx, %r13
	movzbl	622(%rsp), %r15d
	addq	%r15, %r13
	movzbl	623(%rsp), %eax
	addq	%rax, %r13
	addq	%r12, %r13
	cmpq	$128, %r13
	jne	.LBB3_76
	movq	24(%rsp), %r12
	movb	%r12b, 3048(%rsp)
	movq	8(%rsp), %r12
	movb	%r12b, 3049(%rsp)
	movq	48(%rsp), %r12
	movb	%r12b, 3050(%rsp)
	movq	16(%rsp), %r12
	movb	%r12b, 3051(%rsp)
	movq	56(%rsp), %r12
	movb	%r12b, 3052(%rsp)
	movq	40(%rsp), %r12
	movb	%r12b, 3053(%rsp)
	movq	32(%rsp), %r12
	movb	%r12b, 3054(%rsp)
	movq	544(%rsp), %r12
	movb	%r12b, 3055(%rsp)
	movq	72(%rsp), %r12
	movb	%r12b, 3056(%rsp)
	movq	80(%rsp), %r12
	movb	%r12b, 3057(%rsp)
	movq	176(%rsp), %r12
	movb	%r12b, 3058(%rsp)
	movq	520(%rsp), %r12
	movb	%r12b, 3059(%rsp)
	movq	536(%rsp), %r12
	movb	%r12b, 3060(%rsp)
	movq	528(%rsp), %r12
	movb	%r12b, 3061(%rsp)
	movq	512(%rsp), %r12
	movb	%r12b, 3062(%rsp)
	movq	504(%rsp), %r12
	movb	%r12b, 3063(%rsp)
	movq	480(%rsp), %r12
	movb	%r12b, 3064(%rsp)
	movq	496(%rsp), %r12
	movb	%r12b, 3065(%rsp)
	movq	488(%rsp), %r12
	movb	%r12b, 3066(%rsp)
	movq	472(%rsp), %r12
	movb	%r12b, 3067(%rsp)
	movq	464(%rsp), %r12
	movb	%r12b, 3068(%rsp)
	movq	456(%rsp), %r12
	movb	%r12b, 3069(%rsp)
	movq	432(%rsp), %r12
	movb	%r12b, 3070(%rsp)
	movq	448(%rsp), %r12
	movb	%r12b, 3071(%rsp)
	movq	440(%rsp), %r12
	movb	%r12b, 3072(%rsp)
	movq	424(%rsp), %r12
	movb	%r12b, 3073(%rsp)
	movq	416(%rsp), %r12
	movb	%r12b, 3074(%rsp)
	movq	408(%rsp), %r12
	movb	%r12b, 3075(%rsp)
	movq	400(%rsp), %r12
	movb	%r12b, 3076(%rsp)
	movq	376(%rsp), %r12
	movb	%r12b, 3077(%rsp)
	movq	392(%rsp), %r12
	movb	%r12b, 3078(%rsp)
	movq	384(%rsp), %r12
	movb	%r12b, 3079(%rsp)
	movq	368(%rsp), %r12
	movb	%r12b, 3080(%rsp)
	movq	360(%rsp), %r12
	movb	%r12b, 3081(%rsp)
	movq	352(%rsp), %r12
	movb	%r12b, 3082(%rsp)
	movq	344(%rsp), %r12
	movb	%r12b, 3083(%rsp)
	movq	336(%rsp), %r12
	movb	%r12b, 3084(%rsp)
	movq	312(%rsp), %r12
	movb	%r12b, 3085(%rsp)
	movq	328(%rsp), %r12
	movb	%r12b, 3086(%rsp)
	movq	320(%rsp), %r12
	movb	%r12b, 3087(%rsp)
	movq	304(%rsp), %r12
	movb	%r12b, 3088(%rsp)
	movq	296(%rsp), %r12
	movb	%r12b, 3089(%rsp)
	movq	288(%rsp), %r12
	movb	%r12b, 3090(%rsp)
	movq	280(%rsp), %r12
	movb	%r12b, 3091(%rsp)
	movq	272(%rsp), %r12
	movb	%r12b, 3092(%rsp)
	movq	264(%rsp), %r12
	movb	%r12b, 3093(%rsp)
	movq	240(%rsp), %r12
	movb	%r12b, 3094(%rsp)
	movq	256(%rsp), %r12
	movb	%r12b, 3095(%rsp)
	movq	248(%rsp), %r12
	movb	%r12b, 3096(%rsp)
	movq	232(%rsp), %r12
	movb	%r12b, 3097(%rsp)
	movq	224(%rsp), %r12
	movb	%r12b, 3098(%rsp)
	movq	216(%rsp), %r12
	movb	%r12b, 3099(%rsp)
	movb	%bpl, 3100(%rsp)
	movb	%cl, 3101(%rsp)
	movb	%dl, 3102(%rsp)
	movb	%sil, 3103(%rsp)
	movb	%dil, 3104(%rsp)
	movb	%r8b, 3105(%rsp)
	movb	%r9b, 3106(%rsp)
	movb	%r10b, 3107(%rsp)
	movb	%r11b, 3108(%rsp)
	movb	%bl, 3109(%rsp)
	movb	%r15b, 3110(%rsp)
	movb	%al, 3111(%rsp)
	xorl	%eax, %eax
	movq	memset@GOTPCREL(%rip), %rbx
	leaq	8296(%rsp), %r13
	leaq	4072(%rsp), %r12
	jmp	.LBB3_34
.LBB3_52:
	movq	1592(%rsp), %rax
	movq	1600(%rsp), %rcx
	movq	176(%rsp), %rdx
	movq	%rax, 20520(%rsp,%rdx)
	movq	%rcx, 20528(%rsp,%rdx)
	movq	80(%rsp), %rax
	incq	%rax
	cmpq	$64, %rax
	je	.LBB3_53
.LBB3_34:
	movzbl	3048(%rsp,%rax), %ebp
	movq	%rax, 80(%rsp)
	movq	%rax, %rdx
	shlq	$4, %rdx
	movq	184(%rsp), %rcx
	movq	(%rcx,%rdx), %rax
	movq	%rdx, 176(%rsp)
	movq	8(%rcx,%rdx), %rcx
	movq	%rax, 1592(%rsp)
	movq	%rcx, 1600(%rsp)
	cmpq	$2, %rbp
	ja	.LBB3_52
	movq	80(%rsp), %rax
	shll	$24, %eax
	movl	%eax, 72(%rsp)
	.p2align	4
.LBB3_36:
	movq	1592(%rsp), %rax
	movq	1600(%rsp), %rcx
	movq	%rcx, 8304(%rsp)
	movq	%rax, 8296(%rsp)
	movq	%rbp, 8312(%rsp)
	movl	104(%rsp), %eax
	movl	%eax, 9320(%rsp)
	movl	$0, 9324(%rsp)
	movq	88(%rsp), %rax
	movq	%rax, 9328(%rsp)
	movl	$0, 9336(%rsp)
	movl	68(%rsp), %eax
	movl	%eax, 9340(%rsp)
	movl	72(%rsp), %eax
	movl	%eax, 9344(%rsp)
	movl	%ebp, %eax
	bswapl	%eax
	movl	%eax, 9348(%rsp)
	movl	$344, %edx
	movq	%r12, %rdi
	xorl	%esi, %esi
	callq	*%rbx
	movq	112(%rsp), %rax
	movq	120(%rsp), %rcx
	leaq	4272(%rsp), %rdx
	movq	%rax, (%rdx)
	movq	%rcx, 8(%rdx)
	movq	4408(%rsp), %rdi
	addq	$16, %rdi
	movq	%rdi, 4408(%rsp)
	cmpq	$136, %rdi
	jne	.LBB3_38
	movq	4272(%rsp), %rax
	movq	%rax, 24(%rsp)
	movq	4280(%rsp), %rcx
	movq	4288(%rsp), %rdx
	movq	4296(%rsp), %rsi
	movq	4304(%rsp), %rdi
	movq	4312(%rsp), %r8
	movq	4320(%rsp), %r9
	movq	4328(%rsp), %r10
	movq	4336(%rsp), %r11
	movq	4344(%rsp), %rbx
	movq	4352(%rsp), %r15
	movq	4360(%rsp), %r12
	movq	4368(%rsp), %r14
	movq	%rbp, 56(%rsp)
	movq	4376(%rsp), %rbp
	movq	4384(%rsp), %r13
	movq	4392(%rsp), %rax
	movq	%rax, 8(%rsp)
	movq	4400(%rsp), %rax
	movq	%rax, 16(%rsp)
	movq	24(%rsp), %rax
	xorq	%rax, 4072(%rsp)
	xorq	%rcx, 4080(%rsp)
	xorq	%rdx, 4088(%rsp)
	xorq	%rsi, 4096(%rsp)
	xorq	%rdi, 4104(%rsp)
	xorq	%r8, 4112(%rsp)
	xorq	%r9, 4120(%rsp)
	xorq	%r10, 4128(%rsp)
	xorq	%r11, 4136(%rsp)
	xorq	%rbx, 4144(%rsp)
	xorq	%r15, 4152(%rsp)
	xorq	%r12, 4160(%rsp)
	xorq	%r14, 4168(%rsp)
	movq	memcpy@GOTPCREL(%rip), %r14
	xorq	%rbp, 4176(%rsp)
	movq	56(%rsp), %rbp
	xorq	%r13, 4184(%rsp)
	leaq	8296(%rsp), %r13
	movq	8(%rsp), %rax
	xorq	%rax, 4192(%rsp)
	movq	16(%rsp), %rax
	xorq	%rax, 4200(%rsp)
	leaq	4072(%rsp), %rdi
	callq	_RNvCsndc0WgnAaH_9keccak2568keccak_f
	movq	$0, 4408(%rsp)
	xorl	%edi, %edi
.LBB3_38:
	incq	%rbp
	movq	%rbp, 56(%rsp)
	movl	$32, %r12d
	leaq	9320(%rsp), %rbx
	leaq	560(%rsp), %rbp
	jmp	.LBB3_39
	.p2align	4
.LBB3_43:
	subq	%r15, %r12
	addq	%r15, %rbx
	testq	%r12, %r12
	je	.LBB3_44
.LBB3_39:
	movl	$136, %r15d
	subq	%rdi, %r15
	cmpq	%r15, %r12
	cmovbq	%r12, %r15
	leaq	(%r15,%rdi), %rsi
	cmpq	%rdi, %rsi
	jb	.LBB3_78
	cmpq	$137, %rsi
	jae	.LBB3_78
	leaq	4272(%rsp), %rax
	addq	%rax, %rdi
	movq	%rbx, %rsi
	movq	%r15, %rdx
	callq	*%r14
	movq	4408(%rsp), %rdi
	addq	%r15, %rdi
	movq	%rdi, 4408(%rsp)
	cmpq	$136, %rdi
	jne	.LBB3_43
	movq	4272(%rsp), %rax
	movq	%rax, 24(%rsp)
	movq	4280(%rsp), %rcx
	movq	4288(%rsp), %rdx
	movq	4296(%rsp), %rsi
	movq	4304(%rsp), %rdi
	movq	4312(%rsp), %r8
	movq	4320(%rsp), %r9
	movq	4328(%rsp), %r10
	movq	4336(%rsp), %r11
	movq	4344(%rsp), %r14
	movq	4352(%rsp), %r13
	movq	4360(%rsp), %rbp
	movq	4368(%rsp), %rax
	movq	%rax, 8(%rsp)
	movq	4376(%rsp), %rax
	movq	%rax, 16(%rsp)
	movq	4384(%rsp), %rax
	movq	%rax, 48(%rsp)
	movq	4392(%rsp), %rax
	movq	%rax, 40(%rsp)
	movq	4400(%rsp), %rax
	movq	%rax, 32(%rsp)
	movq	24(%rsp), %rax
	xorq	%rax, 4072(%rsp)
	xorq	%rcx, 4080(%rsp)
	xorq	%rdx, 4088(%rsp)
	xorq	%rsi, 4096(%rsp)
	xorq	%rdi, 4104(%rsp)
	xorq	%r8, 4112(%rsp)
	xorq	%r9, 4120(%rsp)
	xorq	%r10, 4128(%rsp)
	xorq	%r11, 4136(%rsp)
	xorq	%r14, 4144(%rsp)
	movq	memcpy@GOTPCREL(%rip), %r14
	xorq	%r13, 4152(%rsp)
	leaq	8296(%rsp), %r13
	xorq	%rbp, 4160(%rsp)
	leaq	560(%rsp), %rbp
	movq	8(%rsp), %rax
	xorq	%rax, 4168(%rsp)
	movq	16(%rsp), %rax
	xorq	%rax, 4176(%rsp)
	movq	48(%rsp), %rax
	xorq	%rax, 4184(%rsp)
	movq	40(%rsp), %rax
	xorq	%rax, 4192(%rsp)
	movq	32(%rsp), %rax
	xorq	%rax, 4200(%rsp)
	leaq	4072(%rsp), %rdi
	callq	_RNvCsndc0WgnAaH_9keccak2568keccak_f
	movq	$0, 4408(%rsp)
	xorl	%edi, %edi
	jmp	.LBB3_43
	.p2align	4
.LBB3_44:
	movl	$344, %edx
	movq	%rbp, %rdi
	leaq	4072(%rsp), %rsi
	callq	*%r14
	movl	$16, %r12d
	movq	896(%rsp), %rdi
	movq	%r13, %rbx
	jmp	.LBB3_45
	.p2align	4
.LBB3_49:
	subq	%r15, %r12
	addq	%r15, %rbx
	testq	%r12, %r12
	je	.LBB3_50
.LBB3_45:
	movl	$136, %r15d
	subq	%rdi, %r15
	cmpq	%r15, %r12
	cmovbq	%r12, %r15
	leaq	(%r15,%rdi), %rsi
	cmpq	%rdi, %rsi
	jb	.LBB3_78
	cmpq	$137, %rsi
	jae	.LBB3_78
	leaq	760(%rsp), %rax
	addq	%rax, %rdi
	movq	%rbx, %rsi
	movq	%r15, %rdx
	callq	*%r14
	movq	896(%rsp), %rdi
	addq	%r15, %rdi
	movq	%rdi, 896(%rsp)
	cmpq	$136, %rdi
	jne	.LBB3_49
	movq	760(%rsp), %rax
	movq	%rax, 24(%rsp)
	movq	768(%rsp), %rcx
	movq	776(%rsp), %rdx
	movq	784(%rsp), %rsi
	movq	792(%rsp), %rdi
	movq	800(%rsp), %r8
	movq	808(%rsp), %r9
	movq	816(%rsp), %r10
	movq	824(%rsp), %r11
	movq	832(%rsp), %r14
	movq	840(%rsp), %r13
	movq	848(%rsp), %rbp
	movq	856(%rsp), %rax
	movq	%rax, 8(%rsp)
	movq	864(%rsp), %rax
	movq	%rax, 16(%rsp)
	movq	872(%rsp), %rax
	movq	%rax, 48(%rsp)
	movq	880(%rsp), %rax
	movq	%rax, 40(%rsp)
	movq	888(%rsp), %rax
	movq	%rax, 32(%rsp)
	movq	24(%rsp), %rax
	xorq	%rax, 560(%rsp)
	xorq	%rcx, 568(%rsp)
	xorq	%rdx, 576(%rsp)
	xorq	%rsi, 584(%rsp)
	xorq	%rdi, 592(%rsp)
	xorq	%r8, 600(%rsp)
	xorq	%r9, 608(%rsp)
	xorq	%r10, 616(%rsp)
	xorq	%r11, 624(%rsp)
	xorq	%r14, 632(%rsp)
	movq	memcpy@GOTPCREL(%rip), %r14
	xorq	%r13, 640(%rsp)
	leaq	8296(%rsp), %r13
	xorq	%rbp, 648(%rsp)
	leaq	560(%rsp), %rbp
	movq	8(%rsp), %rax
	xorq	%rax, 656(%rsp)
	movq	16(%rsp), %rax
	xorq	%rax, 664(%rsp)
	movq	48(%rsp), %rax
	xorq	%rax, 672(%rsp)
	movq	40(%rsp), %rax
	xorq	%rax, 680(%rsp)
	movq	32(%rsp), %rax
	xorq	%rax, 688(%rsp)
	movq	%rbp, %rdi
	callq	_RNvCsndc0WgnAaH_9keccak2568keccak_f
	movq	$0, 896(%rsp)
	xorl	%edi, %edi
	jmp	.LBB3_49
	.p2align	4
.LBB3_50:
	movl	$200, %edx
	movq	%r14, %r15
	movq	%rdi, %r14
	leaq	4072(%rsp), %r12
	movq	%r12, %rdi
	movq	%rbp, %rsi
	callq	*%r15
	movq	%r14, %rbx
	cmpq	$137, %r14
	jae	.LBB3_81
	movl	$136, %edx
	leaq	2024(%rsp), %rbp
	movq	%rbp, %rdi
	xorl	%esi, %esi
	movq	memset@GOTPCREL(%rip), %r14
	callq	*%r14
	movq	%rbp, %rdi
	leaq	760(%rsp), %rsi
	movq	%rbx, %rdx
	callq	*%r15
	xorb	$1, 2024(%rsp,%rbx)
	movq	%r14, %rbx
	xorb	$-128, 2159(%rsp)
	movq	2024(%rsp), %rax
	xorq	%rax, 4072(%rsp)
	movq	2032(%rsp), %rax
	xorq	%rax, 4080(%rsp)
	movq	2040(%rsp), %rax
	xorq	%rax, 4088(%rsp)
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
	movq	%r12, %rdi
	callq	_RNvCsndc0WgnAaH_9keccak2568keccak_f
	movq	4096(%rsp), %rax
	movq	%rax, 2048(%rsp)
	movq	4072(%rsp), %rax
	movq	4080(%rsp), %rcx
	movq	%rax, 2024(%rsp)
	movq	%rax, 1592(%rsp)
	movq	%rcx, 1600(%rsp)
	movq	56(%rsp), %rbp
	cmpq	$3, %rbp
	movq	%r15, %r14
	jne	.LBB3_36
	jmp	.LBB3_52
.LBB3_53:
	movl	104(%rsp), %eax
	movl	%eax, 2024(%rsp)
	movl	$0, 2028(%rsp)
	movq	88(%rsp), %rax
	movq	%rax, 2032(%rsp)
	movl	$16777216, 2040(%rsp)
	movl	68(%rsp), %eax
	movl	%eax, 2044(%rsp)
	movq	$0, 2048(%rsp)
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
	leaq	2024(%rsp), %r13
	movq	%r13, %rsi
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	movl	$344, %edx
	leaq	560(%rsp), %rbp
	movq	%rbp, %rdi
	movq	%r12, %rsi
	callq	*%r14
	movl	$1024, %edx
	movq	%rbp, %rdi
	leaq	20520(%rsp), %rsi
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update
	leaq	11368(%rsp), %rdi
	movq	%rbp, %rsi
	callq	_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher8finalize
	xorl	%eax, %eax
	movq	96(%rsp), %rsi
	cmpq	$1, %rsi
	setne	%al
	testq	%rsi, %rsi
	movq	11368(%rsp), %rcx
	movq	11376(%rsp), %rdx
	movq	%rdx, 2016(%rsp)
	movq	%rcx, 2008(%rsp)
	movq	%rdx, 1600(%rsp)
	movq	%rcx, 1592(%rsp)
	leaq	8(,%rax,8), %rcx
	cmoveq	%rsi, %rcx
	movq	168(%rsp), %rax
	leaq	(%rcx,%rax), %rsi
	movq	%rcx, %rdi
	cmpq	%rcx, %rsi
	jb	.LBB3_82
	cmpq	$27, %rsi
	jae	.LBB3_82
	cmpq	$0, 168(%rsp)
	je	.LBB3_83
	shlq	$4, %rdi
	leaq	17004(%rsp), %rax
	addq	%rax, %rdi
	movq	%rdi, 72(%rsp)
	movq	1592(%rsp), %rax
	movq	1600(%rsp), %rcx
	movq	%rcx, 8304(%rsp)
	movq	%rax, 8296(%rsp)
	movq	96(%rsp), %rax
	shll	$24, %eax
	movq	%rax, 96(%rsp)
	xorl	%ecx, %ecx
.LBB3_57:
	movq	8296(%rsp), %rax
	movq	8304(%rsp), %rdx
	movq	%rdx, 9328(%rsp)
	movq	%rcx, %rdx
	movl	$1, %esi
	shlq	%cl, %rsi
	shlq	$4, %rdx
	addq	72(%rsp), %rdx
	movq	208(%rsp), %rdi
	testl	%edi, %esi
	movq	%rdx, %r8
	leaq	9320(%rsp), %rsi
	cmoveq	%rsi, %r8
	cmovneq	%rsi, %rdx
	movq	%rax, 9320(%rsp)
	movq	(%r8), %rax
	movq	8(%r8), %rsi
	movq	%rsi, 11376(%rsp)
	movq	%rax, 11368(%rsp)
	movq	(%rdx), %rax
	movq	8(%rdx), %rsi
	leaq	11384(%rsp), %rdx
	movq	%rsi, 8(%rdx)
	movq	%rax, (%rdx)
	incq	%rcx
	movq	%rdi, %rax
	shrq	%cl, %rax
	movq	%rcx, 56(%rsp)
	bswapl	%ecx
	bswapl	%eax
	movq	96(%rsp), %rdx
	movl	%edx, 3048(%rsp)
	movl	$0, 3052(%rsp)
	movq	88(%rsp), %rdx
	movq	%rdx, 3056(%rsp)
	movq	$33554432, 3064(%rsp)
	movl	%ecx, 3072(%rsp)
	movl	%eax, 3076(%rsp)
	movl	$344, %edx
	movq	%r12, %rdi
	xorl	%esi, %esi
	callq	*%rbx
	movq	112(%rsp), %rax
	movq	120(%rsp), %rcx
	leaq	4272(%rsp), %rdx
	movq	%rax, (%rdx)
	movq	%rcx, 8(%rdx)
	movq	4408(%rsp), %rdi
	addq	$16, %rdi
	movq	%rdi, 4408(%rsp)
	cmpq	$136, %rdi
	jne	.LBB3_59
	movq	4272(%rsp), %rax
	movq	%rax, 24(%rsp)
	movq	4280(%rsp), %rcx
	movq	4288(%rsp), %rdx
	movq	4296(%rsp), %rsi
	movq	4304(%rsp), %rdi
	movq	4312(%rsp), %r8
	movq	4320(%rsp), %r9
	movq	4328(%rsp), %r10
	movq	4336(%rsp), %r11
	movq	4344(%rsp), %rbx
	movq	4352(%rsp), %r14
	movq	4360(%rsp), %r15
	movq	4368(%rsp), %r12
	movq	4376(%rsp), %r13
	movq	4384(%rsp), %rbp
	movq	4392(%rsp), %rax
	movq	%rax, 8(%rsp)
	movq	4400(%rsp), %rax
	movq	%rax, 16(%rsp)
	movq	24(%rsp), %rax
	xorq	%rax, 4072(%rsp)
	xorq	%rcx, 4080(%rsp)
	xorq	%rdx, 4088(%rsp)
	xorq	%rsi, 4096(%rsp)
	xorq	%rdi, 4104(%rsp)
	xorq	%r8, 4112(%rsp)
	xorq	%r9, 4120(%rsp)
	xorq	%r10, 4128(%rsp)
	xorq	%r11, 4136(%rsp)
	xorq	%rbx, 4144(%rsp)
	xorq	%r14, 4152(%rsp)
	movq	memcpy@GOTPCREL(%rip), %r14
	xorq	%r15, 4160(%rsp)
	xorq	%r12, 4168(%rsp)
	leaq	4072(%rsp), %r12
	xorq	%r13, 4176(%rsp)
	xorq	%rbp, 4184(%rsp)
	leaq	560(%rsp), %rbp
	movq	8(%rsp), %rax
	xorq	%rax, 4192(%rsp)
	movq	16(%rsp), %rax
	xorq	%rax, 4200(%rsp)
	movq	%r12, %rdi
	callq	_RNvCsndc0WgnAaH_9keccak2568keccak_f
	movq	$0, 4408(%rsp)
	xorl	%edi, %edi
.LBB3_59:
	movl	$32, %r15d
	leaq	3048(%rsp), %r13
	jmp	.LBB3_60
.LBB3_64:
	subq	%rbx, %r15
	addq	%rbx, %r13
	testq	%r15, %r15
	je	.LBB3_65
.LBB3_60:
	movl	$136, %ebx
	subq	%rdi, %rbx
	cmpq	%rbx, %r15
	cmovbq	%r15, %rbx
	leaq	(%rbx,%rdi), %rsi
	cmpq	%rdi, %rsi
	jb	.LBB3_78
	cmpq	$137, %rsi
	jae	.LBB3_78
	leaq	4272(%rsp), %rax
	addq	%rax, %rdi
	movq	%r13, %rsi
	movq	%rbx, %rdx
	callq	*%r14
	movq	4408(%rsp), %rdi
	addq	%rbx, %rdi
	movq	%rdi, 4408(%rsp)
	cmpq	$136, %rdi
	jne	.LBB3_64
	movq	4272(%rsp), %rax
	movq	%rax, 24(%rsp)
	movq	4280(%rsp), %rcx
	movq	4288(%rsp), %rdx
	movq	4296(%rsp), %rsi
	movq	4304(%rsp), %rdi
	movq	4312(%rsp), %r8
	movq	4320(%rsp), %r9
	movq	4328(%rsp), %r10
	movq	4336(%rsp), %r11
	movq	4344(%rsp), %r14
	movq	4352(%rsp), %r12
	movq	4360(%rsp), %rbp
	movq	4368(%rsp), %rax
	movq	%rax, 8(%rsp)
	movq	4376(%rsp), %rax
	movq	%rax, 16(%rsp)
	movq	4384(%rsp), %rax
	movq	%rax, 48(%rsp)
	movq	4392(%rsp), %rax
	movq	%rax, 40(%rsp)
	movq	4400(%rsp), %rax
	movq	%rax, 32(%rsp)
	movq	24(%rsp), %rax
	xorq	%rax, 4072(%rsp)
	xorq	%rcx, 4080(%rsp)
	xorq	%rdx, 4088(%rsp)
	xorq	%rsi, 4096(%rsp)
	xorq	%rdi, 4104(%rsp)
	xorq	%r8, 4112(%rsp)
	xorq	%r9, 4120(%rsp)
	xorq	%r10, 4128(%rsp)
	xorq	%r11, 4136(%rsp)
	xorq	%r14, 4144(%rsp)
	movq	memcpy@GOTPCREL(%rip), %r14
	xorq	%r12, 4152(%rsp)
	leaq	4072(%rsp), %r12
	xorq	%rbp, 4160(%rsp)
	leaq	560(%rsp), %rbp
	movq	8(%rsp), %rax
	xorq	%rax, 4168(%rsp)
	movq	16(%rsp), %rax
	xorq	%rax, 4176(%rsp)
	movq	48(%rsp), %rax
	xorq	%rax, 4184(%rsp)
	movq	40(%rsp), %rax
	xorq	%rax, 4192(%rsp)
	movq	32(%rsp), %rax
	xorq	%rax, 4200(%rsp)
	movq	%r12, %rdi
	callq	_RNvCsndc0WgnAaH_9keccak2568keccak_f
	movq	$0, 4408(%rsp)
	xorl	%edi, %edi
	jmp	.LBB3_64
.LBB3_65:
	movl	$344, %edx
	movq	%rbp, %rdi
	movq	%r12, %rsi
	callq	*%r14
	movl	$32, %r12d
	movq	896(%rsp), %rbx
	leaq	11368(%rsp), %r13
	jmp	.LBB3_66
.LBB3_70:
	subq	%r15, %r12
	addq	%r15, %r13
	testq	%r12, %r12
	je	.LBB3_71
.LBB3_66:
	movl	$136, %r15d
	subq	%rbx, %r15
	cmpq	%r15, %r12
	cmovbq	%r12, %r15
	leaq	(%r15,%rbx), %rsi
	cmpq	%rbx, %rsi
	jb	.LBB3_84
	cmpq	$137, %rsi
	jae	.LBB3_84
	leaq	760(%rsp), %rax
	addq	%rax, %rbx
	movq	%rbx, %rdi
	movq	%r13, %rsi
	movq	%r15, %rdx
	callq	*%r14
	movq	896(%rsp), %rbx
	addq	%r15, %rbx
	movq	%rbx, 896(%rsp)
	cmpq	$136, %rbx
	jne	.LBB3_70
	movq	760(%rsp), %rax
	movq	%rax, 24(%rsp)
	movq	768(%rsp), %rcx
	movq	776(%rsp), %rdx
	movq	784(%rsp), %rsi
	movq	792(%rsp), %rdi
	movq	800(%rsp), %r8
	movq	808(%rsp), %r9
	movq	816(%rsp), %r10
	movq	824(%rsp), %r11
	movq	832(%rsp), %rbx
	movq	840(%rsp), %r14
	movq	848(%rsp), %rbp
	movq	856(%rsp), %rax
	movq	%rax, 8(%rsp)
	movq	864(%rsp), %rax
	movq	%rax, 16(%rsp)
	movq	872(%rsp), %rax
	movq	%rax, 48(%rsp)
	movq	880(%rsp), %rax
	movq	%rax, 40(%rsp)
	movq	888(%rsp), %rax
	movq	%rax, 32(%rsp)
	movq	24(%rsp), %rax
	xorq	%rax, 560(%rsp)
	xorq	%rcx, 568(%rsp)
	xorq	%rdx, 576(%rsp)
	xorq	%rsi, 584(%rsp)
	xorq	%rdi, 592(%rsp)
	xorq	%r8, 600(%rsp)
	xorq	%r9, 608(%rsp)
	xorq	%r10, 616(%rsp)
	xorq	%r11, 624(%rsp)
	xorq	%rbx, 632(%rsp)
	xorq	%r14, 640(%rsp)
	movq	memcpy@GOTPCREL(%rip), %r14
	xorq	%rbp, 648(%rsp)
	leaq	560(%rsp), %rbp
	movq	8(%rsp), %rax
	xorq	%rax, 656(%rsp)
	movq	16(%rsp), %rax
	xorq	%rax, 664(%rsp)
	movq	48(%rsp), %rax
	xorq	%rax, 672(%rsp)
	movq	40(%rsp), %rax
	xorq	%rax, 680(%rsp)
	movq	32(%rsp), %rax
	xorq	%rax, 688(%rsp)
	movq	%rbp, %rdi
	callq	_RNvCsndc0WgnAaH_9keccak2568keccak_f
	movq	$0, 896(%rsp)
	xorl	%ebx, %ebx
	jmp	.LBB3_70
.LBB3_71:
	movl	$200, %edx
	leaq	4072(%rsp), %r12
	movq	%r12, %rdi
	movq	%rbp, %rsi
	callq	*%r14
	cmpq	$137, %rbx
	jae	.LBB3_81
	movl	$136, %edx
	leaq	2024(%rsp), %r13
	movq	%r13, %rdi
	xorl	%esi, %esi
	movq	memset@GOTPCREL(%rip), %r15
	callq	*%r15
	movq	%r13, %rdi
	leaq	760(%rsp), %rsi
	movq	%rbx, %rdx
	callq	*%r14
	xorb	$1, 2024(%rsp,%rbx)
	movq	%r15, %rbx
	xorb	$-128, 2159(%rsp)
	movq	2024(%rsp), %rax
	xorq	%rax, 4072(%rsp)
	movq	2032(%rsp), %rax
	xorq	%rax, 4080(%rsp)
	movq	2040(%rsp), %rax
	xorq	%rax, 4088(%rsp)
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
	movq	%r12, %rdi
	callq	_RNvCsndc0WgnAaH_9keccak2568keccak_f
	movq	4072(%rsp), %rax
	movq	4080(%rsp), %rcx
	movq	%rcx, 2032(%rsp)
	movq	%rax, 2024(%rsp)
	movq	%rax, 8296(%rsp)
	movq	%rcx, 8304(%rsp)
	movq	56(%rsp), %rcx
	cmpq	168(%rsp), %rcx
	jne	.LBB3_57
	movq	8296(%rsp), %rax
	movq	8304(%rsp), %rcx
	jmp	.LBB3_74
.LBB3_83:
	movq	1592(%rsp), %rax
	movq	1600(%rsp), %rcx
.LBB3_74:
	movq	%rcx, 4080(%rsp)
	movq	%rax, 4072(%rsp)
	movq	4072(%rsp), %rax
	movq	4080(%rsp), %rcx
	movq	%rcx, 152(%rsp)
	movq	%rax, 144(%rsp)
	movq	200(%rsp), %rcx
	leaq	(%rsp,%rcx), %rax
	addq	$12780, %rax
	movq	%rax, 184(%rsp)
	cmpq	$7740, %rcx
	movl	$0, %ebx
	leaq	.Lanon.bee145f0cb2eac5728ff95be1b200579.2(%rip), %rdx
	leaq	144(%rsp), %r15
	movq	192(%rsp), %rsi
	jne	.LBB3_30
	movq	144(%rsp), %rcx
	movq	152(%rsp), %rdx
	xorq	136(%rsp), %rdx
	xorq	128(%rsp), %rcx
	xorl	%eax, %eax
	orq	%rdx, %rcx
	sete	%al
	jmp	.LBB3_77
.LBB3_78:
	movl	$136, %edx
	callq	_RNvNtNtCs1gUZZmupoa8_4core5slice5index16slice_index_fail
.LBB3_79:
	movl	$136, %edx
	movq	%r13, %rdi
	callq	_RNvNtNtCs1gUZZmupoa8_4core5slice5index16slice_index_fail
.LBB3_80:
	xorl	%edi, %edi
	movq	%r13, %rsi
	callq	_RNvNtNtCs1gUZZmupoa8_4core5slice5index16slice_index_fail
.LBB3_76:
	xorl	%eax, %eax
.LBB3_77:
	addq	$21576, %rsp
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
.LBB3_81:
	.cfi_def_cfa_offset 21632
	movl	$136, %edx
	xorl	%edi, %edi
	movq	%rbx, %rsi
	callq	_RNvNtNtCs1gUZZmupoa8_4core5slice5index16slice_index_fail
.LBB3_84:
	movl	$136, %edx
	movq	%rbx, %rdi
	callq	_RNvNtNtCs1gUZZmupoa8_4core5slice5index16slice_index_fail
.LBB3_82:
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
	movq	(%rdi), %r13
	movq	8(%rdi), %r10
	movq	40(%rdi), %rdx
	movq	120(%rdi), %rax
	movq	160(%rdi), %rcx
	movq	%rdx, -48(%rsp)
	xorq	%r13, %rdx
	movq	%rax, -56(%rsp)
	movq	%rcx, -40(%rsp)
	xorq	%rcx, %rax
	xorq	%rdx, %rax
	movq	48(%rdi), %rdx
	movq	88(%rdi), %r14
	movq	168(%rdi), %rcx
	movq	%rdx, -112(%rsp)
	xorq	%r10, %rdx
	movq	%r14, -72(%rsp)
	movq	%rcx, -24(%rsp)
	xorq	%rcx, %r14
	xorq	%rdx, %r14
	movq	16(%rdi), %rcx
	movq	56(%rdi), %rdx
	movq	96(%rdi), %rbx
	movq	%rdx, -96(%rsp)
	movq	%rcx, -64(%rsp)
	xorq	%rcx, %rdx
	movq	136(%rdi), %r15
	movq	%r15, -120(%rsp)
	xorq	%rbx, %r15
	xorq	%rdx, %r15
	movq	24(%rdi), %r8
	movq	64(%rdi), %rdx
	movq	%rdx, 40(%rsp)
	xorq	%r8, %rdx
	movq	104(%rdi), %rcx
	movq	184(%rdi), %rbp
	movq	%rbp, -32(%rsp)
	movq	%rcx, -88(%rsp)
	xorq	%rcx, %rbp
	xorq	%rdx, %rbp
	movq	32(%rdi), %rcx
	movq	72(%rdi), %rdx
	movq	%rdx, -104(%rsp)
	movq	%rcx, 32(%rsp)
	xorq	%rcx, %rdx
	movq	112(%rdi), %rcx
	movq	152(%rdi), %rsi
	movq	%rcx, -16(%rsp)
	movq	%rsi, -128(%rsp)
	xorq	%rsi, %rcx
	xorq	%rdx, %rcx
	movq	80(%rdi), %rdx
	movq	%rdx, -80(%rsp)
	xorq	%rdx, %rax
	movq	128(%rdi), %rsi
	movq	%rsi, %rdx
	xorq	%rsi, %r14
	movq	176(%rdi), %r11
	xorq	%r11, %r15
	movq	144(%rdi), %r12
	xorq	%r12, %rbp
	movq	%rdi, 88(%rsp)
	movq	192(%rdi), %r9
	xorq	%r9, %rcx
	movl	$8, %edi
	movq	%rdi, 48(%rsp)
	.p2align	4
.LBB9_1:
	movq	%r14, %rsi
	rolq	%rsi
	xorq	%rcx, %rsi
	movq	%rsi, %rdi
	movq	%rsi, 16(%rsp)
	movq	%rbp, %rsi
	rolq	%rsi
	rolq	%rcx
	xorq	%r14, %rsi
	movq	%rsi, %r14
	movq	%rsi, 96(%rsp)
	movq	%r15, %rsi
	rolq	%rsi
	xorq	%r15, %rcx
	xorq	%rax, %rsi
	movq	%rsi, 8(%rsp)
	rolq	%rax
	xorq	%rbp, %rax
	xorq	%rdi, %r13
	xorq	%r14, %rbx
	movq	-112(%rsp), %rbp
	xorq	%rsi, %rbp
	rolq	$43, %rbx
	rolq	$44, %rbp
	xorq	%rcx, %r12
	rolq	$21, %r12
	xorq	%rax, %r9
	movq	%rbx, %r14
	notq	%r14
	rolq	$14, %r9
	andq	%r12, %r14
	movq	%r13, %r15
	notq	%r15
	xorq	%rbp, %r14
	movq	%r14, 56(%rsp)
	andq	%rbp, %r15
	movq	%rbp, %rdi
	notq	%rdi
	andq	%rbx, %rdi
	movq	%r9, %rsi
	notq	%rsi
	andq	%r13, %rsi
	xorq	%r12, %rsi
	movq	%rsi, -112(%rsp)
	notq	%r12
	andq	%r9, %r12
	xorq	%rbx, %r12
	movq	%r12, 80(%rsp)
	xorq	%r9, %r15
	movq	%r15, (%rsp)
	leaq	.Lanon.5ef9b7c546f4dc64388b910df55ec241.5(%rip), %r15
	movq	48(%rsp), %rsi
	xorq	-8(%rsi,%r15), %rdi
	xorq	%r13, %rdi
	movq	%rdi, 104(%rsp)
	xorq	%rcx, %r8
	movq	-80(%rsp), %rdi
	movq	16(%rsp), %r13
	xorq	%r13, %rdi
	rolq	$28, %r8
	rolq	$3, %rdi
	movq	8(%rsp), %r12
	xorq	%r12, %rdx
	movq	-104(%rsp), %r14
	xorq	%rax, %r14
	rolq	$45, %rdx
	rolq	$20, %r14
	movq	96(%rsp), %r15
	xorq	%r15, %r11
	rolq	$61, %r11
	movq	%r14, %rsi
	notq	%rsi
	movq	%rdx, %rbx
	notq	%rbx
	andq	%rdi, %rsi
	movq	%rsi, %r9
	andq	%r11, %rbx
	xorq	%rdi, %rbx
	movq	%rbx, 64(%rsp)
	notq	%rdi
	movq	%r11, %rsi
	notq	%rsi
	andq	%r8, %rsi
	andq	%rdx, %rdi
	xorq	%rdx, %rsi
	movq	%rsi, 72(%rsp)
	xorq	%r8, %r9
	movq	%r9, -80(%rsp)
	notq	%r8
	xorq	%r14, %rdi
	movq	%rdi, -104(%rsp)
	andq	%r14, %r8
	xorq	%r11, %r8
	movq	%r8, 24(%rsp)
	movq	-96(%rsp), %r11
	xorq	%r15, %r11
	rolq	$6, %r11
	movq	-88(%rsp), %rsi
	xorq	%rcx, %rsi
	xorq	%r12, %r10
	rolq	$25, %rsi
	rolq	%r10
	movq	-128(%rsp), %r9
	xorq	%rax, %r9
	movq	-40(%rsp), %r8
	movq	%r13, %r14
	xorq	%r13, %r8
	rolq	$8, %r9
	rolq	$18, %r8
	movq	%r11, %rdx
	notq	%rdx
	andq	%rsi, %rdx
	movq	%rdx, %rdi
	movq	%r9, %rdx
	notq	%rdx
	andq	%r8, %rdx
	xorq	%rsi, %rdx
	movq	%rdx, -8(%rsp)
	notq	%rsi
	movq	%r8, %rbp
	notq	%rbp
	andq	%r10, %rbp
	xorq	%r9, %rbp
	movq	%rbp, -88(%rsp)
	andq	%r9, %rsi
	movq	%rsi, -128(%rsp)
	xorq	%r10, %rdi
	movq	%rdi, -96(%rsp)
	notq	%r10
	andq	%r11, %r10
	movq	%r10, %r13
	xorq	%r8, %r13
	movq	%r13, -40(%rsp)
	movq	-48(%rsp), %r8
	xorq	%r14, %r8
	rolq	$36, %r8
	movq	-72(%rsp), %rdx
	xorq	%r12, %rdx
	movq	-120(%rsp), %r10
	xorq	%r15, %r10
	rolq	$10, %rdx
	rolq	$15, %r10
	movq	-32(%rsp), %rdi
	xorq	%rcx, %rdi
	movq	32(%rsp), %r9
	xorq	%rax, %r9
	rolq	$56, %rdi
	rolq	$27, %r9
	xorq	-64(%rsp), %r15
	movq	%r8, %rsi
	notq	%rsi
	andq	%rdx, %rsi
	movq	%r10, %r14
	notq	%r14
	andq	%rdi, %r14
	xorq	%rdx, %r14
	movq	%r14, -72(%rsp)
	notq	%rdx
	andq	%r10, %rdx
	movq	%rdi, %r12
	notq	%r12
	andq	%r9, %r12
	xorq	%r10, %r12
	xorq	%r9, %rsi
	movq	%rsi, -32(%rsp)
	xorq	%r8, %rdx
	movq	%rdx, -48(%rsp)
	notq	%r9
	andq	%r8, %r9
	xorq	%rdi, %r9
	movq	%r9, %rdi
	movq	%r9, -120(%rsp)
	movq	80(%rsp), %r8
	xorq	64(%rsp), %r8
	movq	-8(%rsp), %rbx
	xorq	%r14, %rbx
	xorq	%r8, %rbx
	movq	-112(%rsp), %r9
	xorq	72(%rsp), %r9
	movq	%rbp, %r8
	xorq	%r12, %r8
	xorq	%r9, %r8
	movq	-128(%rsp), %r14
	xorq	%r11, %r14
	movq	%r14, -128(%rsp)
	movq	(%rsp), %r9
	xorq	24(%rsp), %r9
	xorq	%rdi, %r13
	xorq	%r9, %r13
	movq	%r13, -64(%rsp)
	xorq	40(%rsp), %rcx
	movq	-16(%rsp), %r9
	xorq	%rax, %r9
	movq	56(%rsp), %rax
	xorq	-104(%rsp), %rax
	movq	%r14, %r10
	xorq	%rdx, %r10
	xorq	%rax, %r10
	movq	16(%rsp), %rbp
	xorq	-56(%rsp), %rbp
	movq	8(%rsp), %r11
	xorq	-24(%rsp), %r11
	rolq	$62, %r15
	rolq	$41, %rbp
	rolq	$55, %rcx
	rolq	$2, %r11
	rolq	$39, %r9
	movq	%rcx, %rax
	notq	%rax
	andq	%r9, %rax
	movq	%rax, %r14
	movq	%rbp, %r13
	notq	%r13
	andq	%r11, %r13
	xorq	%r9, %r13
	notq	%r9
	movq	%r11, %rax
	notq	%rax
	andq	%rbp, %r9
	andq	%r15, %rax
	xorq	%rbp, %rax
	movq	%rax, %rbp
	movq	%rax, -56(%rsp)
	xorq	%r15, %r14
	movq	%r14, 8(%rsp)
	xorq	%rcx, %r9
	movq	%r9, 16(%rsp)
	notq	%r15
	andq	%rcx, %r15
	xorq	%r11, %r15
	movq	%r15, %rdi
	movq	-80(%rsp), %rax
	xorq	-96(%rsp), %rax
	xorq	%rsi, %rax
	xorq	%r14, %rax
	movq	104(%rsp), %rcx
	xorq	%rcx, %rax
	xorq	%r13, %rbx
	xorq	%rbp, %r8
	movq	-64(%rsp), %r11
	xorq	%r15, %r11
	xorq	%r9, %r10
	movq	%r8, %r9
	rolq	%r9
	xorq	%r10, %r9
	movq	%r10, %rdx
	rolq	%rdx
	xorq	%r11, %rdx
	movq	%rbx, %rsi
	rolq	%rsi
	xorq	%rax, %rsi
	movq	%rsi, %r14
	rolq	%r11
	rolq	%rax
	xorq	%rbx, %r11
	xorq	%r8, %rax
	xorq	%rax, %rdi
	movq	24(%rsp), %rbp
	xorq	%rax, %rbp
	xorq	%rax, -120(%rsp)
	xorq	%rax, (%rsp)
	xorq	-40(%rsp), %rax
	movq	%rax, -16(%rsp)
	movq	-8(%rsp), %rax
	xorq	%r9, %rax
	rolq	$43, %rax
	xorq	%r11, %r12
	movq	-104(%rsp), %r15
	xorq	%rsi, %r15
	rolq	$21, %r12
	rolq	$44, %r15
	xorq	%rdx, %rcx
	rolq	$14, %rdi
	movq	%rax, %rsi
	notq	%rsi
	andq	%r12, %rsi
	xorq	%r15, %rsi
	movq	%rsi, -8(%rsp)
	movq	%rcx, %rsi
	notq	%rsi
	andq	%r15, %rsi
	notq	%r15
	andq	%rax, %r15
	movq	%rdi, %r8
	notq	%r8
	andq	%rcx, %r8
	movq	%rcx, %r10
	xorq	%r12, %r8
	notq	%r12
	andq	%rdi, %r12
	xorq	%rax, %r12
	movq	%r12, -64(%rsp)
	xorq	%rdi, %rsi
	movq	%rsi, 32(%rsp)
	movq	48(%rsp), %rcx
	leaq	.Lanon.5ef9b7c546f4dc64388b910df55ec241.5(%rip), %rsi
	xorq	(%rcx,%rsi), %r15
	xorq	%r10, %r15
	movq	%r15, 24(%rsp)
	movq	-112(%rsp), %r10
	xorq	%r11, %r10
	rolq	$28, %r10
	movq	-96(%rsp), %rsi
	xorq	%rdx, %rsi
	movq	%rdx, %r15
	rolq	$3, %rsi
	movq	%r14, %rbx
	movq	-48(%rsp), %rax
	xorq	%r14, %rax
	rolq	$45, %rax
	rolq	$20, %rbp
	xorq	%r9, %r13
	rolq	$61, %r13
	movq	%rbp, %rdx
	notq	%rdx
	movq	%rax, %r14
	notq	%r14
	andq	%rsi, %rdx
	andq	%r13, %r14
	xorq	%rsi, %r14
	movq	%r14, -96(%rsp)
	notq	%rsi
	movq	%r13, %r14
	notq	%r14
	andq	%r10, %r14
	andq	%rax, %rsi
	xorq	%rax, %r14
	movq	%r14, 40(%rsp)
	xorq	%r10, %rdx
	movq	%rdx, -48(%rsp)
	notq	%r10
	xorq	%rbp, %rsi
	movq	%rsi, -112(%rsp)
	andq	%rbp, %r10
	xorq	%r13, %r10
	movq	%r10, -104(%rsp)
	movq	64(%rsp), %rdi
	xorq	%r9, %rdi
	movq	-72(%rsp), %rax
	xorq	%r9, %rax
	xorq	80(%rsp), %r9
	rolq	$6, %rdi
	movq	56(%rsp), %r14
	xorq	%rbx, %r14
	movq	-88(%rsp), %rdx
	movq	%r11, %r10
	xorq	%r11, %rdx
	rolq	%r14
	rolq	$25, %rdx
	movq	%rdx, -88(%rsp)
	movq	-120(%rsp), %rsi
	rolq	$8, %rsi
	movq	%rsi, -120(%rsp)
	movq	8(%rsp), %r12
	movq	%r15, %rcx
	movq	%r15, -24(%rsp)
	xorq	%r15, %r12
	rolq	$18, %r12
	movq	%rdi, %rbp
	notq	%rbp
	andq	%rdx, %rbp
	xorq	%r14, %rbp
	movq	%rdx, %r11
	notq	%r11
	movq	%r12, %rdx
	movq	%r12, %r13
	notq	%rdx
	andq	%rsi, %r11
	andq	%r14, %rdx
	movq	%rdx, %rsi
	notq	%r14
	andq	%rdi, %r14
	movq	%r14, 56(%rsp)
	xorq	%rdi, %r11
	movq	%r11, -72(%rsp)
	movq	-80(%rsp), %r15
	xorq	%rcx, %r15
	rolq	$36, %r15
	movq	-128(%rsp), %r12
	xorq	%rbx, %r12
	movq	%rbx, %rcx
	rolq	$15, %rax
	rolq	$10, %r12
	movq	-56(%rsp), %r11
	xorq	%r10, %r11
	movq	%r10, %r14
	rolq	$56, %r11
	movq	%r15, %rdi
	movq	%r15, %r10
	notq	%rdi
	movq	%rax, %r15
	notq	%r15
	andq	%r12, %rdi
	andq	%r11, %r15
	xorq	%r12, %r15
	movq	%r12, %rdx
	movq	(%rsp), %rbx
	rolq	$27, %rbx
	notq	%rdx
	andq	%rax, %rdx
	movq	%r11, %r12
	notq	%r12
	andq	%rbx, %r12
	xorq	%rax, %r12
	xorq	%rbx, %rdi
	movq	%rdi, -56(%rsp)
	xorq	%r10, %rdx
	movq	%rdx, (%rsp)
	notq	%rbx
	andq	%r10, %rbx
	xorq	%r11, %rbx
	movq	%rbx, -128(%rsp)
	movq	%rcx, %rax
	xorq	16(%rsp), %rax
	movq	-120(%rsp), %rbx
	movq	%rsi, %rdx
	xorq	%rbx, %rdx
	notq	%rbx
	movq	56(%rsp), %rdi
	xorq	%r13, %rdi
	andq	%r13, %rbx
	xorq	72(%rsp), %r14
	movq	-24(%rsp), %rcx
	xorq	-32(%rsp), %rcx
	rolq	$62, %r9
	rolq	$41, %rcx
	rolq	$55, %r14
	rolq	$2, %rax
	movq	-16(%rsp), %r10
	rolq	$39, %r10
	movq	%r14, %r13
	notq	%r13
	andq	%r10, %r13
	movq	%rcx, %r11
	notq	%r11
	andq	%rax, %r11
	xorq	%r10, %r11
	notq	%r10
	movq	%rax, %rsi
	notq	%rsi
	andq	%rcx, %r10
	andq	%r9, %rsi
	xorq	%rcx, %rsi
	xorq	%r9, %r13
	xorq	%r14, %r10
	notq	%r9
	andq	%r14, %r9
	xorq	%rax, %r9
	xorq	-88(%rsp), %rbx
	movq	-64(%rsp), %rax
	xorq	-96(%rsp), %rax
	xorq	%rbx, %rax
	movq	%r15, -120(%rsp)
	xorq	%r11, %r15
	xorq	%rax, %r15
	movq	-48(%rsp), %rax
	movq	%rbp, -80(%rsp)
	xorq	%rbp, %rax
	movq	40(%rsp), %rbp
	movq	%rdx, -88(%rsp)
	xorq	%rdx, %rbp
	movq	-8(%rsp), %r14
	xorq	-112(%rsp), %r14
	movq	32(%rsp), %rcx
	movq	%rdi, -16(%rsp)
	xorq	%rdi, %rcx
	xorq	-104(%rsp), %rcx
	movq	(%rsp), %rdi
	xorq	-72(%rsp), %r14
	xorq	-56(%rsp), %rax
	xorq	%r12, %rbp
	xorq	%r8, %rbp
	movq	%rdi, %rdx
	xorq	%rdi, %r14
	xorq	-128(%rsp), %rcx
	movq	%r13, -40(%rsp)
	xorq	%r13, %rax
	movq	24(%rsp), %r13
	xorq	%r13, %rax
	movq	%r10, -24(%rsp)
	xorq	%r10, %r14
	movq	-8(%rsp), %r10
	movq	%rsi, -32(%rsp)
	xorq	%rsi, %rbp
	xorq	%r9, %rcx
	movq	48(%rsp), %rsi
	addq	$16, %rsi
	movq	%rsi, 48(%rsp)
	cmpq	$200, %rsi
	jne	.LBB9_1
	movq	88(%rsp), %rax
	movq	%r13, (%rax)
	movq	-112(%rsp), %rcx
	movq	%rcx, 48(%rax)
	movq	%r8, 24(%rax)
	movq	-104(%rsp), %rcx
	movq	%rcx, 72(%rax)
	movq	%r10, 8(%rax)
	movq	-96(%rsp), %rcx
	movq	%rcx, 56(%rax)
	movq	-40(%rsp), %rcx
	movq	%rcx, 160(%rax)
	movq	32(%rsp), %rcx
	movq	%rcx, 32(%rax)
	movq	-48(%rsp), %rcx
	movq	%rcx, 40(%rax)
	movq	-72(%rsp), %rcx
	movq	%rcx, 88(%rax)
	movq	-120(%rsp), %rcx
	movq	%rcx, 136(%rax)
	movq	-32(%rsp), %rcx
	movq	%rcx, 184(%rax)
	movq	-64(%rsp), %rcx
	movq	%rcx, 16(%rax)
	movq	40(%rsp), %rcx
	movq	%rcx, 64(%rax)
	movq	-16(%rsp), %rcx
	movq	%rcx, 112(%rax)
	movq	-56(%rsp), %rcx
	movq	%rcx, 120(%rax)
	movq	-24(%rsp), %rcx
	movq	%rcx, 168(%rax)
	movq	-80(%rsp), %rcx
	movq	%rcx, 80(%rax)
	movq	%rbx, 96(%rax)
	movq	-88(%rsp), %rcx
	movq	%rcx, 104(%rax)
	movq	%rdx, 128(%rax)
	movq	%r12, 144(%rax)
	movq	-128(%rsp), %rcx
	movq	%rcx, 152(%rax)
	movq	%r11, 176(%rax)
	movq	%r9, 192(%rax)
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

	.type	.Lanon.5ef9b7c546f4dc64388b910df55ec241.5,@object
	.section	.rodata..Lanon.5ef9b7c546f4dc64388b910df55ec241.5,"a",@progbits
	.p2align	3, 0x0
.Lanon.5ef9b7c546f4dc64388b910df55ec241.5:
	.ascii	"\001\000\000\000\000\000\000\000\202\200\000\000\000\000\000\000\212\200\000\000\000\000\000\200\000\200\000\200\000\000\000\200\213\200\000\000\000\000\000\000\001\000\000\200\000\000\000\000\201\200\000\200\000\000\000\200\t\200\000\000\000\000\000\200\212\000\000\000\000\000\000\000\210\000\000\000\000\000\000\000\t\200\000\200\000\000\000\000\n\000\000\200\000\000\000\000\213\200\000\200\000\000\000\000\213\000\000\000\000\000\000\200\211\200\000\000\000\000\000\200\003\200\000\000\000\000\000\200\002\200\000\000\000\000\000\200\200\000\000\000\000\000\000\200\n\200\000\000\000\000\000\000\n\000\000\200\000\000\000\200\201\200\000\200\000\000\000\200\200\200\000\000\000\000\000\200\001\000\000\200\000\000\000\000\b\200\000\200\000\000\000\200"
	.size	.Lanon.5ef9b7c546f4dc64388b910df55ec241.5, 192

	.type	.Lanon.bee145f0cb2eac5728ff95be1b200579.2,@object
	.section	.rodata..Lanon.bee145f0cb2eac5728ff95be1b200579.2,"a",@progbits
	.p2align	3, 0x0
.Lanon.bee145f0cb2eac5728ff95be1b200579.2:
	.asciz	"\b\000\000\000\000\000\000\000\b\000\000\000\000\000\000\000\n\000\000\000\000\000\000"
	.size	.Lanon.bee145f0cb2eac5728ff95be1b200579.2, 24

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
