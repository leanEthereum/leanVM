	.att_syntax
	.file	"native_vm.a73d193de09a3cff-cgu.0"
	.section	.text._RINvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB6_6TState8sumcheckNCNvB2_14sumcheck_plain0EB8_,"ax",@progbits
	.p2align	4
	.type	_RINvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB6_6TState8sumcheckNCNvB2_14sumcheck_plain0EB8_,@function
_RINvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB6_6TState8sumcheckNCNvB2_14sumcheck_plain0EB8_:
.Lfunc_begin0:
	.cfi_sections .debug_frame
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
	subq	$120, %rsp
	.cfi_def_cfa_offset 176
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	%rdx, %rax
	movq	%rdi, 8(%rsp)
	movq	176(%rsp), %rbx
	movq	$0, 16(%rsp)
	movq	$0, 24(%rsp)
	movq	$0, 32(%rsp)
	movq	$0, 40(%rsp)
	movq	$0, 48(%rsp)
	movq	$0, 56(%rsp)
	movq	$0, 64(%rsp)
	movq	$0, 72(%rsp)
	movq	$0, 80(%rsp)
	movq	$0, 88(%rsp)
	testq	%rbx, %rbx
	je	.LBB0_5
	movq	%r9, %r14
	movq	%r8, %r15
	movq	%rsi, %r12
	shlq	$4, %rbx
	addq	%r9, %rbx
	leaq	96(%rsp), %r13
	leaq	16(%rsp), %rbp
	.p2align	4
.LBB0_2:
	movq	$0, 96(%rsp)
	movq	%r12, %rdi
	movq	%r15, %rsi
	movq	%rax, %rdx
	movq	%r13, %r8
	movq	%rbp, %r9
	callq	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState19sumcheck_round_poly
	testb	%al, %al
	je	.LBB0_3
	movq	%r12, %rdi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW7squeeze
	movq	%rdx, %rcx
	movq	%rax, (%r14)
	movq	%rdx, 8(%r14)
	movq	%rbp, %rdi
	movq	%r15, %rsi
	movq	%rax, %rdx
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field9poly_eval
	movq	%rdx, %rcx
	addq	$16, %r14
	cmpq	%rbx, %r14
	jne	.LBB0_2
.LBB0_5:
	movq	8(%rsp), %rdx
	movq	%rax, 8(%rdx)
	movq	%rcx, 16(%rdx)
	movl	$1, %eax
	jmp	.LBB0_6
.LBB0_3:
	movq	8(%rsp), %rdx
	xorl	%eax, %eax
.LBB0_6:
	movq	%rax, (%rdx)
	addq	$120, %rsp
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
.Lfunc_end0:
	.size	_RINvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB6_6TState8sumcheckNCNvB2_14sumcheck_plain0EB8_, .Lfunc_end0-_RINvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB6_6TState8sumcheckNCNvB2_14sumcheck_plain0EB8_
	.cfi_endproc

	.section	.text._RINvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB6_6TState8sumcheckNCNvNtB8_10keccak_gkr12verify_layers1_0EB8_,"ax",@progbits
	.p2align	4
	.type	_RINvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB6_6TState8sumcheckNCNvNtB8_10keccak_gkr12verify_layers1_0EB8_,@function
_RINvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB6_6TState8sumcheckNCNvNtB8_10keccak_gkr12verify_layers1_0EB8_:
.Lfunc_begin1:
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
	subq	$136, %rsp
	.cfi_def_cfa_offset 192
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	%r9, 24(%rsp)
	movq	%r8, 16(%rsp)
	movq	%rdx, %rax
	movq	%rdi, 8(%rsp)
	movq	200(%rsp), %rbx
	movq	$0, 56(%rsp)
	movq	$0, 64(%rsp)
	movq	$0, 72(%rsp)
	movq	$0, 80(%rsp)
	movq	$0, 88(%rsp)
	movq	$0, 96(%rsp)
	movq	$0, 104(%rsp)
	movq	$0, 112(%rsp)
	movq	$0, 120(%rsp)
	movq	$0, 128(%rsp)
	testq	%rbx, %rbx
	je	.LBB1_8
	movq	%rsi, %r12
	shlq	$4, %rbx
	addq	192(%rsp), %rbx
	leaq	56(%rsp), %rbp
	xorl	%r13d, %r13d
	xorl	%r14d, %r14d
	.p2align	4
.LBB1_2:
	cmpq	24(%rsp), %r14
	jae	.LBB1_3
	movq	16(%rsp), %rsi
	movq	(%rsi,%r13), %rdx
	movq	8(%rsi,%r13), %rsi
	movq	%rdx, 40(%rsp)
	movq	%rsi, 48(%rsp)
	movl	$1, %edx
	jmp	.LBB1_5
	.p2align	4
.LBB1_3:
	xorl	%edx, %edx
.LBB1_5:
	movq	%rdx, 32(%rsp)
	movl	$3, %esi
	movq	%r12, %rdi
	movq	%rax, %rdx
	leaq	32(%rsp), %r8
	movq	%rbp, %r9
	callq	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState19sumcheck_round_poly
	testb	%al, %al
	je	.LBB1_6
	movq	192(%rsp), %rax
	leaq	(%rax,%r13), %r15
	movq	%r12, %rdi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW7squeeze
	movq	%rdx, %rcx
	movq	%rax, (%r15)
	movq	%rdx, 8(%r15)
	movl	$3, %esi
	movq	%rbp, %rdi
	movq	%rax, %rdx
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field9poly_eval
	movq	%rdx, %rcx
	addq	$16, %r13
	addq	$16, %r15
	incq	%r14
	cmpq	%rbx, %r15
	jne	.LBB1_2
.LBB1_8:
	movq	8(%rsp), %rdx
	movq	%rax, 8(%rdx)
	movq	%rdx, %rax
	movq	%rcx, 16(%rdx)
	movl	$1, %ecx
	jmp	.LBB1_9
.LBB1_6:
	movq	8(%rsp), %rax
	xorl	%ecx, %ecx
.LBB1_9:
	movq	%rcx, (%rax)
	addq	$136, %rsp
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
.Lfunc_end1:
	.size	_RINvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB6_6TState8sumcheckNCNvNtB8_10keccak_gkr12verify_layers1_0EB8_, .Lfunc_end1-_RINvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB6_6TState8sumcheckNCNvNtB8_10keccak_gkr12verify_layers1_0EB8_
	.cfi_endproc

	.section	.text._RINvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB6_6TState8sumcheckNCNvNtB8_3gkr8gkr_step0EB8_,"ax",@progbits
	.p2align	4
	.type	_RINvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB6_6TState8sumcheckNCNvNtB8_3gkr8gkr_step0EB8_,@function
_RINvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB6_6TState8sumcheckNCNvNtB8_3gkr8gkr_step0EB8_:
.Lfunc_begin2:
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
	subq	$136, %rsp
	.cfi_def_cfa_offset 192
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	%r9, 24(%rsp)
	movq	%rdx, %rax
	movq	%rdi, 8(%rsp)
	movq	208(%rsp), %rbx
	movq	$0, 56(%rsp)
	movq	$0, 64(%rsp)
	movq	$0, 72(%rsp)
	movq	$0, 80(%rsp)
	movq	$0, 88(%rsp)
	movq	$0, 96(%rsp)
	movq	$0, 104(%rsp)
	movq	$0, 112(%rsp)
	movq	$0, 120(%rsp)
	movq	$0, 128(%rsp)
	testq	%rbx, %rbx
	je	.LBB2_8
	movq	%r8, %r15
	movq	%rsi, 16(%rsp)
	shlq	$4, %rbx
	addq	200(%rsp), %rbx
	xorl	%r13d, %r13d
	xorl	%r14d, %r14d
	.p2align	4
.LBB2_2:
	cmpq	192(%rsp), %r14
	jae	.LBB2_3
	movq	24(%rsp), %rsi
	movq	(%rsi,%r13), %rdx
	movq	8(%rsi,%r13), %rsi
	movq	%rdx, 40(%rsp)
	movq	%rsi, 48(%rsp)
	movl	$1, %edx
	jmp	.LBB2_5
	.p2align	4
.LBB2_3:
	xorl	%edx, %edx
.LBB2_5:
	leaq	56(%rsp), %rbp
	movq	16(%rsp), %r12
	movq	%rdx, 32(%rsp)
	movq	%r12, %rdi
	movq	%r15, %rsi
	movq	%rax, %rdx
	leaq	32(%rsp), %r8
	movq	%rbp, %r9
	callq	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState19sumcheck_round_poly
	testb	%al, %al
	je	.LBB2_6
	movq	200(%rsp), %rax
	movq	%r12, %rdi
	movq	%r15, %r12
	movq	%rbx, %r15
	movq	%rbp, %rbx
	leaq	(%rax,%r13), %rbp
	callq	_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW7squeeze
	movq	%rdx, %rcx
	movq	%rax, (%rbp)
	movq	%rdx, 8(%rbp)
	movq	%rbx, %rdi
	movq	%r15, %rbx
	movq	%r12, %r15
	movq	%r12, %rsi
	movq	%rax, %rdx
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field9poly_eval
	movq	%rdx, %rcx
	addq	$16, %r13
	addq	$16, %rbp
	incq	%r14
	cmpq	%rbx, %rbp
	jne	.LBB2_2
.LBB2_8:
	movq	8(%rsp), %rdx
	movq	%rax, 8(%rdx)
	movq	%rdx, %rax
	movq	%rcx, 16(%rdx)
	movl	$1, %ecx
	jmp	.LBB2_9
.LBB2_6:
	movq	8(%rsp), %rax
	xorl	%ecx, %ecx
.LBB2_9:
	movq	%rcx, (%rax)
	addq	$136, %rsp
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
.Lfunc_end2:
	.size	_RINvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB6_6TState8sumcheckNCNvNtB8_3gkr8gkr_step0EB8_, .Lfunc_end2-_RINvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB6_6TState8sumcheckNCNvNtB8_3gkr8gkr_step0EB8_
	.cfi_endproc

	.section	.text._RINvNtCsemcRClSg8DH_9native_vm4whir8each_rowNCNvB2_10next_level0EB4_,"ax",@progbits
	.p2align	4
	.type	_RINvNtCsemcRClSg8DH_9native_vm4whir8each_rowNCNvB2_10next_level0EB4_,@function
_RINvNtCsemcRClSg8DH_9native_vm4whir8each_rowNCNvB2_10next_level0EB4_:
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
	subq	$1928, %rsp
	.cfi_def_cfa_offset 1984
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	%r9, 80(%rsp)
	movq	%rcx, %r12
	movq	%rdx, %rbx
	movq	%rsi, %r15
	movq	%rdi, 88(%rsp)
	leaq	144(%rsp), %rdi
	movq	%r8, %rsi
	callq	_RNvNtCsemcRClSg8DH_9native_vm4whir14subspace_table
	cmpl	$1, 144(%rsp)
	jne	.LBB3_14
	movq	152(%rsp), %r14
	leaq	160(%rsp), %rsi
	leaq	1432(%rsp), %r13
	movl	$496, %edx
	movq	%r13, %rdi
	callq	*memcpy@GOTPCREL(%rip)
	movq	%r14, 1424(%rsp)
	movq	16(%r12), %rdx
	movb	$1, %al
	testq	%rdx, %rdx
	je	.LBB3_15
	movq	%r12, %rdi
	movq	1992(%rsp), %rax
	xorl	%esi, %esi
	cmpq	$32, %r14
	movl	$8, %ecx
	cmovaeq	%rcx, %r13
	cmovaeq	%rsi, %r14
	leaq	(%r15,%rbx,8), %rcx
	movq	%rcx, 72(%rsp)
	movq	(%rax), %rcx
	movq	%rcx, 56(%rsp)
	movq	8(%rax), %rcx
	movq	%rcx, 48(%rsp)
	movq	16(%rax), %rcx
	movq	%rcx, 40(%rsp)
	movq	24(%rax), %rcx
	movq	%rcx, 24(%rsp)
	movq	40(%rax), %rcx
	movq	%rcx, 8(%rsp)
	movq	32(%rax), %rax
	movq	%rax, (%rsp)
	xorl	%ebx, %ebx
	movq	%r14, 64(%rsp)
	movq	%r13, 32(%rsp)
	movq	%r12, 16(%rsp)
	movq	24(%rsp), %r14
	jmp	.LBB3_5
	.p2align	4
.LBB3_3:
	movq	%rbx, %rcx
	shlq	$4, %rcx
	movq	(%rsp), %rdx
	movq	(%rdx,%rcx), %rdi
	movq	8(%rdx,%rcx), %rsi
.LBB3_4:
	addq	$8, %r15
	incq	%rbx
	movq	(%r14), %r12
	movq	8(%r14), %r13
	xorq	104(%rsp), %rbp
	xorq	96(%rsp), %rax
	movq	%rbp, %rdx
	movq	%rax, %rcx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	xorq	%r12, %rax
	xorq	%r13, %rdx
	movq	%rax, (%r14)
	movq	%rdx, 8(%r14)
	movq	112(%rsp), %rdx
	testq	%rdx, %rdx
	movq	16(%rsp), %rdi
	movq	32(%rsp), %r13
	je	.LBB3_17
.LBB3_5:
	cmpq	72(%rsp), %r15
	je	.LBB3_17
	decq	%rdx
	movq	%rdx, 112(%rsp)
	movq	(%r15), %rbp
	movl	$56, %eax
	.p2align	4
.LBB3_7:
	movq	$0, 88(%rsp,%rax)
	movq	$0, 96(%rsp,%rax)
	movq	$0, 104(%rsp,%rax)
	movq	$0, 112(%rsp,%rax)
	movq	$0, 120(%rsp,%rax)
	movq	$0, 128(%rsp,%rax)
	movq	$0, 136(%rsp,%rax)
	movq	$0, 144(%rsp,%rax)
	addq	$64, %rax
	cmpq	$1080, %rax
	jne	.LBB3_7
	movq	%rbx, %rsi
	callq	_RNvMs_NtCsemcRClSg8DH_9native_vm10transcriptNtB4_4Rows3row
	movq	88(%rsp), %rdi
	movq	%rax, %rsi
	leaq	144(%rsp), %r12
	movq	%r12, %rcx
	callq	_RNvNtCsemcRClSg8DH_9native_vm4whir8lanes_of
	cmpq	$1, %rax
	jne	.LBB3_14
	movq	%r12, %rdi
	movq	%rdx, %rsi
	movq	%rbp, %rdx
	movq	80(%rsp), %rcx
	movq	1984(%rsp), %r8
	callq	_RNvNtCsemcRClSg8DH_9native_vm4whir8fold_row
	movq	%rax, 104(%rsp)
	movq	%rdx, %r12
	leaq	1168(%rsp), %rdi
	movq	%r13, %rsi
	movq	64(%rsp), %rdx
	movq	%rbp, %rcx
	callq	_RNvNtCsemcRClSg8DH_9native_vm4whir17subspace_at_table
	movq	1168(%rsp), %r8
	cmpq	$32, %r8
	movl	$8, %ecx
	leaq	1176(%rsp), %rax
	cmovbq	%rax, %rcx
	movl	$0, %eax
	cmovaeq	%rax, %r8
	movq	56(%rsp), %rax
	movq	(%rax), %rax
	movl	$0, %r13d
	cmpq	%r8, %rax
	jae	.LBB3_11
	movq	(%rcx,%rax,8), %r13
.LBB3_11:
	leaq	120(%rsp), %rdi
	movq	48(%rsp), %rsi
	movq	40(%rsp), %rdx
	callq	_RNvNtCsemcRClSg8DH_9native_vm4whir10novel_eval
	cmpl	$1, 120(%rsp)
	jne	.LBB3_14
	movq	%r12, 96(%rsp)
	movq	128(%rsp), %rsi
	movq	136(%rsp), %r12
	movq	%r13, %rdi
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field4kmul
	movq	%rax, %rbp
	movq	%r13, %rdi
	movq	%r12, %rsi
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field4kmul
	cmpq	8(%rsp), %rbx
	jb	.LBB3_3
	xorl	%edi, %edi
	xorl	%esi, %esi
	jmp	.LBB3_4
.LBB3_14:
	xorl	%eax, %eax
.LBB3_15:
	addq	$1928, %rsp
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
.LBB3_17:
	.cfi_def_cfa_offset 1984
	movb	$1, %al
	jmp	.LBB3_15
.Lfunc_end3:
	.size	_RINvNtCsemcRClSg8DH_9native_vm4whir8each_rowNCNvB2_10next_level0EB4_, .Lfunc_end3-_RINvNtCsemcRClSg8DH_9native_vm4whir8each_rowNCNvB2_10next_level0EB4_
	.cfi_endproc

	.section	.text._RINvNtCsemcRClSg8DH_9native_vm4whir8each_rowNCNvB2_11final_level0EB4_,"ax",@progbits
	.p2align	4
	.type	_RINvNtCsemcRClSg8DH_9native_vm4whir8each_rowNCNvB2_11final_level0EB4_,@function
_RINvNtCsemcRClSg8DH_9native_vm4whir8each_rowNCNvB2_11final_level0EB4_:
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
	subq	$1880, %rsp
	.cfi_def_cfa_offset 1936
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	%r9, 24(%rsp)
	movq	%rcx, %r14
	movq	%rdx, %rbx
	movq	%rsi, %rbp
	movq	%rdi, 32(%rsp)
	leaq	96(%rsp), %rdi
	movq	%r8, %rsi
	callq	_RNvNtCsemcRClSg8DH_9native_vm4whir14subspace_table
	cmpl	$1, 96(%rsp)
	jne	.LBB4_12
	movq	104(%rsp), %r12
	leaq	112(%rsp), %rsi
	leaq	1384(%rsp), %r15
	movl	$496, %edx
	movq	%r15, %rdi
	callq	*memcpy@GOTPCREL(%rip)
	movq	%r12, 1376(%rsp)
	movq	16(%r14), %r13
	movb	$1, %al
	testq	%r13, %r13
	je	.LBB4_13
	xorl	%ecx, %ecx
	cmpq	$32, %r12
	movl	$8, %eax
	cmovaeq	%rax, %r15
	leaq	(%rbp,%rbx,8), %rax
	movq	%rax, 16(%rsp)
	cmovaeq	%rcx, %r12
	leaq	96(%rsp), %rbx
	xorl	%esi, %esi
	movq	%r14, 8(%rsp)
	.p2align	4
.LBB4_3:
	cmpq	16(%rsp), %rbp
	je	.LBB4_14
	decq	%r13
	movq	(%rbp), %rax
	movq	%rax, 64(%rsp)
	movl	$56, %eax
	.p2align	4
.LBB4_5:
	movq	$0, 40(%rsp,%rax)
	movq	$0, 48(%rsp,%rax)
	movq	$0, 56(%rsp,%rax)
	movq	$0, 64(%rsp,%rax)
	movq	$0, 72(%rsp,%rax)
	movq	$0, 80(%rsp,%rax)
	movq	$0, 88(%rsp,%rax)
	movq	$0, 96(%rsp,%rax)
	addq	$64, %rax
	cmpq	$1080, %rax
	jne	.LBB4_5
	movq	%r14, %rdi
	movq	%rsi, 56(%rsp)
	callq	_RNvMs_NtCsemcRClSg8DH_9native_vm10transcriptNtB4_4Rows3row
	movq	32(%rsp), %rdi
	movq	%rax, %rsi
	movq	%rbx, %rcx
	callq	_RNvNtCsemcRClSg8DH_9native_vm4whir8lanes_of
	cmpq	$1, %rax
	jne	.LBB4_12
	movq	%r13, 48(%rsp)
	movq	%rbp, 40(%rsp)
	movq	%rbx, %rdi
	movq	%rdx, %rsi
	movq	64(%rsp), %r13
	movq	%r13, %rdx
	movq	24(%rsp), %rcx
	movq	1936(%rsp), %r8
	callq	_RNvNtCsemcRClSg8DH_9native_vm4whir8fold_row
	movq	%rax, %rbp
	movq	%rdx, %r14
	leaq	1120(%rsp), %rdi
	movq	%r15, %rbx
	movq	%r15, %rsi
	movq	%r12, %r15
	movq	%r12, %rdx
	movq	%r13, %rcx
	callq	_RNvNtCsemcRClSg8DH_9native_vm4whir17subspace_at_table
	movq	1120(%rsp), %r8
	cmpq	$32, %r8
	movl	$8, %ecx
	leaq	1128(%rsp), %rax
	cmovbq	%rax, %rcx
	movl	$0, %eax
	cmovaeq	%rax, %r8
	leaq	72(%rsp), %rdi
	movq	1944(%rsp), %rsi
	movq	1952(%rsp), %rdx
	callq	_RNvNtCsemcRClSg8DH_9native_vm4whir10novel_eval
	cmpb	$0, 72(%rsp)
	je	.LBB4_12
	cmpq	80(%rsp), %rbp
	jne	.LBB4_12
	cmpq	88(%rsp), %r14
	jne	.LBB4_12
	movq	40(%rsp), %rbp
	addq	$8, %rbp
	movq	56(%rsp), %rsi
	incq	%rsi
	movq	48(%rsp), %r13
	testq	%r13, %r13
	movq	8(%rsp), %r14
	movq	%r15, %r12
	movq	%rbx, %r15
	leaq	96(%rsp), %rbx
	jne	.LBB4_3
.LBB4_14:
	movb	$1, %al
	jmp	.LBB4_13
.LBB4_12:
	xorl	%eax, %eax
.LBB4_13:
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
.Lfunc_end4:
	.size	_RINvNtCsemcRClSg8DH_9native_vm4whir8each_rowNCNvB2_11final_level0EB4_, .Lfunc_end4-_RINvNtCsemcRClSg8DH_9native_vm4whir8each_rowNCNvB2_11final_level0EB4_
	.cfi_endproc

	.section	.text._RINvNtCsemcRClSg8DH_9native_vm5field10eq_eval_fnNCNvNtB4_6layout8eq_above0EB4_,"ax",@progbits
	.p2align	4
	.type	_RINvNtCsemcRClSg8DH_9native_vm5field10eq_eval_fnNCNvNtB4_6layout8eq_above0EB4_,@function
_RINvNtCsemcRClSg8DH_9native_vm5field10eq_eval_fnNCNvNtB4_6layout8eq_above0EB4_:
.Lfunc_begin5:
	.cfi_startproc
	pushq	%r15
	.cfi_def_cfa_offset 16
	pushq	%r14
	.cfi_def_cfa_offset 24
	pushq	%r12
	.cfi_def_cfa_offset 32
	pushq	%rbx
	.cfi_def_cfa_offset 40
	pushq	%rax
	.cfi_def_cfa_offset 48
	.cfi_offset %rbx, -40
	.cfi_offset %r12, -32
	.cfi_offset %r14, -24
	.cfi_offset %r15, -16
	movq	%rdi, %r15
	cmpq	%rdi, %rcx
	cmovbq	%rcx, %r15
	testq	%r15, %r15
	je	.LBB5_1
	movq	%rdx, %rbx
	movq	%rsi, %r14
	addq	$8, %rbx
	movl	$1, %eax
	xorl	%edx, %edx
	xorl	%esi, %esi
	.p2align	4
.LBB5_3:
	leaq	1(%rsi), %r12
	movq	(%rbx), %rcx
	xorl	%r8d, %r8d
	btq	%rsi, %r14
	setb	%r8b
	xorq	-8(%rbx), %r8
	xorq	$1, %r8
	movq	%rax, %rdi
	movq	%rdx, %rsi
	movq	%r8, %rdx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	addq	$16, %rbx
	movq	%r12, %rsi
	cmpq	%r12, %r15
	jne	.LBB5_3
	jmp	.LBB5_4
.LBB5_1:
	movl	$1, %eax
	xorl	%edx, %edx
.LBB5_4:
	addq	$8, %rsp
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
.Lfunc_end5:
	.size	_RINvNtCsemcRClSg8DH_9native_vm5field10eq_eval_fnNCNvNtB4_6layout8eq_above0EB4_, .Lfunc_end5-_RINvNtCsemcRClSg8DH_9native_vm5field10eq_eval_fnNCNvNtB4_6layout8eq_above0EB4_
	.cfi_endproc

	.section	.text._RINvNtCsemcRClSg8DH_9native_vm5field19multilinear_eval_byNCNvB2_16multilinear_eval0EB4_,"ax",@progbits
	.p2align	4
	.type	_RINvNtCsemcRClSg8DH_9native_vm5field19multilinear_eval_byNCNvB2_16multilinear_eval0EB4_,@function
_RINvNtCsemcRClSg8DH_9native_vm5field19multilinear_eval_byNCNvB2_16multilinear_eval0EB4_:
.Lfunc_begin6:
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
	subq	$1160, %rsp
	.cfi_def_cfa_offset 1216
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	%rcx, 48(%rsp)
	xorl	%eax, %eax
	.p2align	4
.LBB6_1:
	movq	$0, 136(%rsp,%rax)
	movq	$0, 144(%rsp,%rax)
	movq	$0, 152(%rsp,%rax)
	movq	$0, 160(%rsp,%rax)
	movq	$0, 168(%rsp,%rax)
	movq	$0, 176(%rsp,%rax)
	movq	$0, 184(%rsp,%rax)
	movq	$0, 192(%rsp,%rax)
	addq	$64, %rax
	cmpq	$1024, %rax
	jne	.LBB6_1
	movq	$0, 128(%rsp)
	movq	$0, 120(%rsp)
	movq	$0, 112(%rsp)
	movq	$0, 104(%rsp)
	movq	$0, 96(%rsp)
	movq	$0, 88(%rsp)
	movq	$0, 80(%rsp)
	movq	$0, 72(%rsp)
	testq	%rdi, %rdi
	je	.LBB6_3
	testq	%r8, %r8
	je	.LBB6_13
	movq	%rdi, 24(%rsp)
	movq	%rdx, 32(%rsp)
	movq	%rsi, 16(%rsp)
	shlq	$4, %r8
	movq	$0, 8(%rsp)
	movq	%r8, 40(%rsp)
.LBB6_6:
	movq	8(%rsp), %rdx
	cmpq	32(%rsp), %rdx
	jae	.LBB6_7
	movq	%rdx, %rax
	shlq	$4, %rax
	movq	16(%rsp), %rcx
	movq	(%rcx,%rax), %r15
	movq	8(%rcx,%rax), %rbp
	jmp	.LBB6_9
	.p2align	4
.LBB6_7:
	xorl	%r15d, %r15d
	xorl	%ebp, %ebp
.LBB6_9:
	incq	%rdx
	movq	%rdx, 8(%rsp)
	leaq	72(%rsp), %r14
	xorl	%r12d, %r12d
	.p2align	4
.LBB6_10:
	cmpb	$0, (%r14)
	je	.LBB6_11
	movb	$0, (%r14)
	movq	136(%rsp,%r12), %rdi
	movq	144(%rsp,%r12), %rsi
	movq	48(%rsp), %rax
	movq	(%rax,%r12), %rbx
	movq	8(%rax,%r12), %r13
	movq	%rbx, %rdx
	xorq	$1, %rdx
	movq	%r13, %rcx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	movq	%rax, 56(%rsp)
	movq	%rdx, 64(%rsp)
	movq	%r15, %rdi
	movq	%rbp, %rsi
	movq	%rbx, %rdx
	movq	%r13, %rcx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	movq	40(%rsp), %r8
	movq	%rax, %r15
	movq	%rdx, %rbp
	xorq	56(%rsp), %r15
	xorq	64(%rsp), %rbp
	addq	$16, %r12
	incq	%r14
	cmpq	%r12, %r8
	jne	.LBB6_10
	jmp	.LBB6_15
	.p2align	4
.LBB6_11:
	movb	$1, (%r14)
	movq	%r15, 136(%rsp,%r12)
	movq	%rbp, 144(%rsp,%r12)
	movl	$0, %ebp
	movl	$0, %r15d
	movq	8(%rsp), %rax
	cmpq	24(%rsp), %rax
	jne	.LBB6_6
	jmp	.LBB6_15
.LBB6_13:
	testq	%rdx, %rdx
	je	.LBB6_3
	movq	(%rsi), %r15
	movq	8(%rsi), %rbp
	jmp	.LBB6_15
.LBB6_3:
	xorl	%ebp, %ebp
	xorl	%r15d, %r15d
.LBB6_15:
	movq	%r15, %rax
	movq	%rbp, %rdx
	addq	$1160, %rsp
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
.Lfunc_end6:
	.size	_RINvNtCsemcRClSg8DH_9native_vm5field19multilinear_eval_byNCNvB2_16multilinear_eval0EB4_, .Lfunc_end6-_RINvNtCsemcRClSg8DH_9native_vm5field19multilinear_eval_byNCNvB2_16multilinear_eval0EB4_
	.cfi_endproc

	.section	.text._RINvNtCsemcRClSg8DH_9native_vm5field19multilinear_eval_byNCNvNtB4_3bus23computed_bytecode_value0EB4_,"ax",@progbits
	.p2align	4
	.type	_RINvNtCsemcRClSg8DH_9native_vm5field19multilinear_eval_byNCNvNtB4_3bus23computed_bytecode_value0EB4_,@function
_RINvNtCsemcRClSg8DH_9native_vm5field19multilinear_eval_byNCNvNtB4_3bus23computed_bytecode_value0EB4_:
.Lfunc_begin7:
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
	subq	$1160, %rsp
	.cfi_def_cfa_offset 1216
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	%rcx, 48(%rsp)
	cmpq	$63, %r8
	ja	.LBB7_1
	xorl	%eax, %eax
	.p2align	4
.LBB7_3:
	movq	$0, 136(%rsp,%rax)
	movq	$0, 144(%rsp,%rax)
	movq	$0, 152(%rsp,%rax)
	movq	$0, 160(%rsp,%rax)
	movq	$0, 168(%rsp,%rax)
	movq	$0, 176(%rsp,%rax)
	movq	$0, 184(%rsp,%rax)
	movq	$0, 192(%rsp,%rax)
	addq	$64, %rax
	cmpq	$1024, %rax
	jne	.LBB7_3
	movq	$0, 128(%rsp)
	movq	$0, 120(%rsp)
	movq	$0, 112(%rsp)
	movq	$0, 104(%rsp)
	movq	$0, 96(%rsp)
	movq	$0, 88(%rsp)
	movq	$0, 80(%rsp)
	movq	$0, 72(%rsp)
	testq	%rdi, %rdi
	je	.LBB7_1
	testq	%r8, %r8
	je	.LBB7_14
	movq	%rdi, 24(%rsp)
	movq	%rdx, 32(%rsp)
	movq	%rsi, 16(%rsp)
	shlq	$4, %r8
	movq	$0, 8(%rsp)
	movq	%r8, 40(%rsp)
.LBB7_7:
	movq	8(%rsp), %rcx
	cmpq	32(%rsp), %rcx
	jae	.LBB7_8
	movq	16(%rsp), %rax
	movq	(%rax,%rcx,8), %r13
	jmp	.LBB7_10
.LBB7_8:
	xorl	%r13d, %r13d
.LBB7_10:
	incq	%rcx
	movq	%rcx, 8(%rsp)
	leaq	72(%rsp), %rbx
	xorl	%r15d, %r15d
	xorl	%ebp, %ebp
	.p2align	4
.LBB7_11:
	cmpb	$0, (%rbx)
	je	.LBB7_12
	movb	$0, (%rbx)
	movq	136(%rsp,%r15), %rdi
	movq	144(%rsp,%r15), %rsi
	movq	48(%rsp), %rax
	movq	(%rax,%r15), %r14
	movq	8(%rax,%r15), %r12
	movq	%r14, %rdx
	xorq	$1, %rdx
	movq	%r12, %rcx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	movq	%rax, 56(%rsp)
	movq	%rdx, 64(%rsp)
	movq	%r13, %rdi
	movq	%rbp, %rsi
	movq	%r14, %rdx
	movq	%r12, %rcx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	movq	40(%rsp), %r8
	movq	%rax, %r13
	movq	%rdx, %rbp
	xorq	56(%rsp), %r13
	xorq	64(%rsp), %rbp
	addq	$16, %r15
	incq	%rbx
	cmpq	%r15, %r8
	jne	.LBB7_11
	jmp	.LBB7_16
.LBB7_12:
	movb	$1, (%rbx)
	movq	%r13, 136(%rsp,%r15)
	movq	%rbp, 144(%rsp,%r15)
	movl	$0, %ebp
	movl	$0, %r13d
	movq	8(%rsp), %rax
	cmpq	24(%rsp), %rax
	jne	.LBB7_7
	jmp	.LBB7_16
.LBB7_14:
	testq	%rdx, %rdx
	je	.LBB7_1
	movq	(%rsi), %r13
	xorl	%ebp, %ebp
	jmp	.LBB7_16
.LBB7_1:
	xorl	%ebp, %ebp
	xorl	%r13d, %r13d
.LBB7_16:
	movq	%r13, %rax
	movq	%rbp, %rdx
	addq	$1160, %rsp
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
.Lfunc_end7:
	.size	_RINvNtCsemcRClSg8DH_9native_vm5field19multilinear_eval_byNCNvNtB4_3bus23computed_bytecode_value0EB4_, .Lfunc_end7-_RINvNtCsemcRClSg8DH_9native_vm5field19multilinear_eval_byNCNvNtB4_3bus23computed_bytecode_value0EB4_
	.cfi_endproc

	.section	.text._RINvNtCsemcRClSg8DH_9native_vm6keccak15keccak256_wordsNCNvB2_10hash_words0EB4_,"ax",@progbits
	.p2align	4
	.type	_RINvNtCsemcRClSg8DH_9native_vm6keccak15keccak256_wordsNCNvB2_10hash_words0EB4_,@function
_RINvNtCsemcRClSg8DH_9native_vm6keccak15keccak256_wordsNCNvB2_10hash_words0EB4_:
.Lfunc_begin8:
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
	subq	$232, %rsp
	.cfi_def_cfa_offset 288
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	%r8, %r12
	movq	%rcx, %r15
	movq	%rdx, %r14
	movq	%rsi, %rbp
	movq	%rdi, 24(%rsp)
	leaq	32(%rsp), %rdi
	movl	$200, %edx
	xorl	%esi, %esi
	callq	*memset@GOTPCREL(%rip)
	movabsq	$-1085102592571150095, %rcx
	movq	%r14, %rax
	mulq	%rcx
	movq	%rdx, 8(%rsp)
	shrq	$7, %rdx
	movq	%rdx, 16(%rsp)
	cmpq	%r12, %rbp
	cmovbq	%rbp, %r12
	cmpq	$136, %r14
	jae	.LBB8_1
.LBB8_4:
	movq	16(%rsp), %rsi
	movq	%rsi, %rax
	shlq	$4, %rax
	addq	%rsi, %rax
	cmpq	%r12, %rax
	jae	.LBB8_5
	movq	(%r15,%rax,8), %rcx
	xorq	%rcx, 32(%rsp)
	leaq	1(%rax), %rcx
	cmpq	%r12, %rcx
	jb	.LBB8_9
.LBB8_8:
	xorl	%ecx, %ecx
	jmp	.LBB8_10
.LBB8_1:
	movq	16(%rsp), %rax
	movq	%rax, %r13
	shlq	$4, %r13
	addq	%rax, %r13
	xorl	%ebx, %ebx
	leaq	32(%rsp), %rbp
	jmp	.LBB8_2
	.p2align	4
.LBB8_104:
	movq	128(%r15,%rbx,8), %rax
.LBB8_105:
	xorq	%rax, 160(%rsp)
	movq	%rbp, %rdi
	callq	_RNvNtCsemcRClSg8DH_9native_vm6keccak8keccak_f
	addq	$17, %rbx
	cmpq	%rbx, %r13
	je	.LBB8_4
.LBB8_2:
	cmpq	%r12, %rbx
	jae	.LBB8_3
	movq	(%r15,%rbx,8), %rax
	xorq	%rax, 32(%rsp)
	leaq	1(%rbx), %rax
	cmpq	%r12, %rax
	jb	.LBB8_59
.LBB8_58:
	xorl	%eax, %eax
	xorq	%rax, 40(%rsp)
	leaq	2(%rbx), %rax
	cmpq	%r12, %rax
	jb	.LBB8_62
.LBB8_61:
	xorl	%eax, %eax
	xorq	%rax, 48(%rsp)
	leaq	3(%rbx), %rax
	cmpq	%r12, %rax
	jb	.LBB8_65
.LBB8_64:
	xorl	%eax, %eax
	xorq	%rax, 56(%rsp)
	leaq	4(%rbx), %rax
	cmpq	%r12, %rax
	jb	.LBB8_68
.LBB8_67:
	xorl	%eax, %eax
	xorq	%rax, 64(%rsp)
	leaq	5(%rbx), %rax
	cmpq	%r12, %rax
	jb	.LBB8_71
.LBB8_70:
	xorl	%eax, %eax
	xorq	%rax, 72(%rsp)
	leaq	6(%rbx), %rax
	cmpq	%r12, %rax
	jb	.LBB8_74
.LBB8_73:
	xorl	%eax, %eax
	xorq	%rax, 80(%rsp)
	leaq	7(%rbx), %rax
	cmpq	%r12, %rax
	jb	.LBB8_77
.LBB8_76:
	xorl	%eax, %eax
	xorq	%rax, 88(%rsp)
	leaq	8(%rbx), %rax
	cmpq	%r12, %rax
	jb	.LBB8_80
.LBB8_79:
	xorl	%eax, %eax
	xorq	%rax, 96(%rsp)
	leaq	9(%rbx), %rax
	cmpq	%r12, %rax
	jb	.LBB8_83
.LBB8_82:
	xorl	%eax, %eax
	xorq	%rax, 104(%rsp)
	leaq	10(%rbx), %rax
	cmpq	%r12, %rax
	jb	.LBB8_86
.LBB8_85:
	xorl	%eax, %eax
	xorq	%rax, 112(%rsp)
	leaq	11(%rbx), %rax
	cmpq	%r12, %rax
	jb	.LBB8_89
.LBB8_88:
	xorl	%eax, %eax
	xorq	%rax, 120(%rsp)
	leaq	12(%rbx), %rax
	cmpq	%r12, %rax
	jb	.LBB8_92
.LBB8_91:
	xorl	%eax, %eax
	xorq	%rax, 128(%rsp)
	leaq	13(%rbx), %rax
	cmpq	%r12, %rax
	jb	.LBB8_95
.LBB8_94:
	xorl	%eax, %eax
	xorq	%rax, 136(%rsp)
	leaq	14(%rbx), %rax
	cmpq	%r12, %rax
	jb	.LBB8_98
.LBB8_97:
	xorl	%eax, %eax
	xorq	%rax, 144(%rsp)
	leaq	15(%rbx), %rax
	cmpq	%r12, %rax
	jb	.LBB8_101
.LBB8_100:
	xorl	%eax, %eax
	xorq	%rax, 152(%rsp)
	leaq	16(%rbx), %rax
	cmpq	%r12, %rax
	jb	.LBB8_104
	jmp	.LBB8_103
	.p2align	4
.LBB8_3:
	xorl	%eax, %eax
	xorq	%rax, 32(%rsp)
	leaq	1(%rbx), %rax
	cmpq	%r12, %rax
	jae	.LBB8_58
.LBB8_59:
	movq	8(%r15,%rbx,8), %rax
	xorq	%rax, 40(%rsp)
	leaq	2(%rbx), %rax
	cmpq	%r12, %rax
	jae	.LBB8_61
.LBB8_62:
	movq	16(%r15,%rbx,8), %rax
	xorq	%rax, 48(%rsp)
	leaq	3(%rbx), %rax
	cmpq	%r12, %rax
	jae	.LBB8_64
.LBB8_65:
	movq	24(%r15,%rbx,8), %rax
	xorq	%rax, 56(%rsp)
	leaq	4(%rbx), %rax
	cmpq	%r12, %rax
	jae	.LBB8_67
.LBB8_68:
	movq	32(%r15,%rbx,8), %rax
	xorq	%rax, 64(%rsp)
	leaq	5(%rbx), %rax
	cmpq	%r12, %rax
	jae	.LBB8_70
.LBB8_71:
	movq	40(%r15,%rbx,8), %rax
	xorq	%rax, 72(%rsp)
	leaq	6(%rbx), %rax
	cmpq	%r12, %rax
	jae	.LBB8_73
.LBB8_74:
	movq	48(%r15,%rbx,8), %rax
	xorq	%rax, 80(%rsp)
	leaq	7(%rbx), %rax
	cmpq	%r12, %rax
	jae	.LBB8_76
.LBB8_77:
	movq	56(%r15,%rbx,8), %rax
	xorq	%rax, 88(%rsp)
	leaq	8(%rbx), %rax
	cmpq	%r12, %rax
	jae	.LBB8_79
.LBB8_80:
	movq	64(%r15,%rbx,8), %rax
	xorq	%rax, 96(%rsp)
	leaq	9(%rbx), %rax
	cmpq	%r12, %rax
	jae	.LBB8_82
.LBB8_83:
	movq	72(%r15,%rbx,8), %rax
	xorq	%rax, 104(%rsp)
	leaq	10(%rbx), %rax
	cmpq	%r12, %rax
	jae	.LBB8_85
.LBB8_86:
	movq	80(%r15,%rbx,8), %rax
	xorq	%rax, 112(%rsp)
	leaq	11(%rbx), %rax
	cmpq	%r12, %rax
	jae	.LBB8_88
.LBB8_89:
	movq	88(%r15,%rbx,8), %rax
	xorq	%rax, 120(%rsp)
	leaq	12(%rbx), %rax
	cmpq	%r12, %rax
	jae	.LBB8_91
.LBB8_92:
	movq	96(%r15,%rbx,8), %rax
	xorq	%rax, 128(%rsp)
	leaq	13(%rbx), %rax
	cmpq	%r12, %rax
	jae	.LBB8_94
.LBB8_95:
	movq	104(%r15,%rbx,8), %rax
	xorq	%rax, 136(%rsp)
	leaq	14(%rbx), %rax
	cmpq	%r12, %rax
	jae	.LBB8_97
.LBB8_98:
	movq	112(%r15,%rbx,8), %rax
	xorq	%rax, 144(%rsp)
	leaq	15(%rbx), %rax
	cmpq	%r12, %rax
	jae	.LBB8_100
.LBB8_101:
	movq	120(%r15,%rbx,8), %rax
	xorq	%rax, 152(%rsp)
	leaq	16(%rbx), %rax
	cmpq	%r12, %rax
	jb	.LBB8_104
.LBB8_103:
	xorl	%eax, %eax
	jmp	.LBB8_105
.LBB8_5:
	xorl	%ecx, %ecx
	xorq	%rcx, 32(%rsp)
	leaq	1(%rax), %rcx
	cmpq	%r12, %rcx
	jae	.LBB8_8
.LBB8_9:
	movq	8(%r15,%rax,8), %rcx
.LBB8_10:
	movq	8(%rsp), %rdx
	xorq	%rcx, 40(%rsp)
	leaq	2(%rax), %rcx
	cmpq	%r12, %rcx
	jae	.LBB8_11
	movq	16(%r15,%rax,8), %rcx
	xorq	%rcx, 48(%rsp)
	leaq	3(%rax), %rcx
	cmpq	%r12, %rcx
	jb	.LBB8_15
.LBB8_14:
	xorl	%ecx, %ecx
	xorq	%rcx, 56(%rsp)
	leaq	4(%rax), %rcx
	cmpq	%r12, %rcx
	jb	.LBB8_18
.LBB8_17:
	xorl	%ecx, %ecx
	xorq	%rcx, 64(%rsp)
	leaq	5(%rax), %rcx
	cmpq	%r12, %rcx
	jb	.LBB8_21
.LBB8_20:
	xorl	%ecx, %ecx
	xorq	%rcx, 72(%rsp)
	leaq	6(%rax), %rcx
	cmpq	%r12, %rcx
	jb	.LBB8_24
.LBB8_23:
	xorl	%ecx, %ecx
	xorq	%rcx, 80(%rsp)
	leaq	7(%rax), %rcx
	cmpq	%r12, %rcx
	jb	.LBB8_27
.LBB8_26:
	xorl	%ecx, %ecx
	xorq	%rcx, 88(%rsp)
	leaq	8(%rax), %rcx
	cmpq	%r12, %rcx
	jb	.LBB8_30
.LBB8_29:
	xorl	%ecx, %ecx
	xorq	%rcx, 96(%rsp)
	leaq	9(%rax), %rcx
	cmpq	%r12, %rcx
	jb	.LBB8_33
.LBB8_32:
	xorl	%ecx, %ecx
	xorq	%rcx, 104(%rsp)
	leaq	10(%rax), %rcx
	cmpq	%r12, %rcx
	jb	.LBB8_36
.LBB8_35:
	xorl	%ecx, %ecx
	xorq	%rcx, 112(%rsp)
	leaq	11(%rax), %rcx
	cmpq	%r12, %rcx
	jb	.LBB8_39
.LBB8_38:
	xorl	%ecx, %ecx
	xorq	%rcx, 120(%rsp)
	leaq	12(%rax), %rcx
	cmpq	%r12, %rcx
	jb	.LBB8_42
.LBB8_41:
	xorl	%ecx, %ecx
	xorq	%rcx, 128(%rsp)
	leaq	13(%rax), %rcx
	cmpq	%r12, %rcx
	jb	.LBB8_45
.LBB8_44:
	xorl	%ecx, %ecx
	jmp	.LBB8_46
.LBB8_11:
	xorl	%ecx, %ecx
	xorq	%rcx, 48(%rsp)
	leaq	3(%rax), %rcx
	cmpq	%r12, %rcx
	jae	.LBB8_14
.LBB8_15:
	movq	24(%r15,%rax,8), %rcx
	xorq	%rcx, 56(%rsp)
	leaq	4(%rax), %rcx
	cmpq	%r12, %rcx
	jae	.LBB8_17
.LBB8_18:
	movq	32(%r15,%rax,8), %rcx
	xorq	%rcx, 64(%rsp)
	leaq	5(%rax), %rcx
	cmpq	%r12, %rcx
	jae	.LBB8_20
.LBB8_21:
	movq	40(%r15,%rax,8), %rcx
	xorq	%rcx, 72(%rsp)
	leaq	6(%rax), %rcx
	cmpq	%r12, %rcx
	jae	.LBB8_23
.LBB8_24:
	movq	48(%r15,%rax,8), %rcx
	xorq	%rcx, 80(%rsp)
	leaq	7(%rax), %rcx
	cmpq	%r12, %rcx
	jae	.LBB8_26
.LBB8_27:
	movq	56(%r15,%rax,8), %rcx
	xorq	%rcx, 88(%rsp)
	leaq	8(%rax), %rcx
	cmpq	%r12, %rcx
	jae	.LBB8_29
.LBB8_30:
	movq	64(%r15,%rax,8), %rcx
	xorq	%rcx, 96(%rsp)
	leaq	9(%rax), %rcx
	cmpq	%r12, %rcx
	jae	.LBB8_32
.LBB8_33:
	movq	72(%r15,%rax,8), %rcx
	xorq	%rcx, 104(%rsp)
	leaq	10(%rax), %rcx
	cmpq	%r12, %rcx
	jae	.LBB8_35
.LBB8_36:
	movq	80(%r15,%rax,8), %rcx
	xorq	%rcx, 112(%rsp)
	leaq	11(%rax), %rcx
	cmpq	%r12, %rcx
	jae	.LBB8_38
.LBB8_39:
	movq	88(%r15,%rax,8), %rcx
	xorq	%rcx, 120(%rsp)
	leaq	12(%rax), %rcx
	cmpq	%r12, %rcx
	jae	.LBB8_41
.LBB8_42:
	movq	96(%r15,%rax,8), %rcx
	xorq	%rcx, 128(%rsp)
	leaq	13(%rax), %rcx
	cmpq	%r12, %rcx
	jae	.LBB8_44
.LBB8_45:
	movq	104(%r15,%rax,8), %rcx
.LBB8_46:
	xorq	%rcx, 136(%rsp)
	andq	$-128, %rdx
	leaq	14(%rax), %rcx
	cmpq	%r12, %rcx
	jae	.LBB8_47
	movq	112(%r15,%rax,8), %rcx
	jmp	.LBB8_49
.LBB8_47:
	xorl	%ecx, %ecx
.LBB8_49:
	xorq	%rcx, 144(%rsp)
	leaq	(%rdx,%rsi,8), %rcx
	leaq	15(%rax), %rdx
	cmpq	%r12, %rdx
	jae	.LBB8_50
	movq	120(%r15,%rax,8), %rdx
	jmp	.LBB8_52
.LBB8_50:
	xorl	%edx, %edx
.LBB8_52:
	xorq	%rdx, 152(%rsp)
	subq	%rcx, %r14
	leaq	16(%rax), %rcx
	cmpq	%r12, %rcx
	jae	.LBB8_53
	movq	128(%r15,%rax,8), %rax
	jmp	.LBB8_55
.LBB8_53:
	xorl	%eax, %eax
.LBB8_55:
	xorq	%rax, 160(%rsp)
	leal	(,%r14,8), %ecx
	movl	$1, %eax
	shlq	%cl, %rax
	andq	$-8, %r14
	xorq	%rax, 32(%rsp,%r14)
	xorb	$-128, 167(%rsp)
	leaq	32(%rsp), %rdi
	callq	_RNvNtCsemcRClSg8DH_9native_vm6keccak8keccak_f
	movq	32(%rsp), %rax
	movq	40(%rsp), %rcx
	movq	48(%rsp), %rdx
	movq	56(%rsp), %rsi
	movq	24(%rsp), %rdi
	movq	%rax, (%rdi)
	movq	%rcx, 8(%rdi)
	movq	%rdx, 16(%rdi)
	movq	%rsi, 24(%rdi)
	addq	$232, %rsp
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
.Lfunc_end8:
	.size	_RINvNtCsemcRClSg8DH_9native_vm6keccak15keccak256_wordsNCNvB2_10hash_words0EB4_, .Lfunc_end8-_RINvNtCsemcRClSg8DH_9native_vm6keccak15keccak256_wordsNCNvB2_10hash_words0EB4_
	.cfi_endproc

	.section	.text._RINvNtCsemcRClSg8DH_9native_vm6keccak15keccak256_wordsNCNvNtB4_6verify14fiat_shamir_iv0EB4_,"ax",@progbits
	.p2align	4
	.type	_RINvNtCsemcRClSg8DH_9native_vm6keccak15keccak256_wordsNCNvNtB4_6verify14fiat_shamir_iv0EB4_,@function
_RINvNtCsemcRClSg8DH_9native_vm6keccak15keccak256_wordsNCNvNtB4_6verify14fiat_shamir_iv0EB4_:
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
	subq	$232, %rsp
	.cfi_def_cfa_offset 288
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	%r8, %r15
	movq	%rcx, %r12
	movq	%rdx, %rbx
	movq	%rsi, %r13
	movq	%rdi, 24(%rsp)
	leaq	32(%rsp), %rdi
	movl	$200, %edx
	xorl	%esi, %esi
	callq	*memset@GOTPCREL(%rip)
	movl	%ebx, %eax
	movl	$4042322161, %ecx
	imulq	%rax, %rcx
	shrq	$39, %rcx
	movq	%rcx, 8(%rsp)
	movq	%rbx, 16(%rsp)
	cmpq	$136, %rbx
	jae	.LBB9_1
.LBB9_4:
	movq	8(%rsp), %rax
	movl	%eax, %ebx
	shll	$4, %ebx
	addq	%rax, %rbx
	cmpq	%r13, %rbx
	jae	.LBB9_5
	movq	%r12, %rdi
	movq	%r15, %rsi
	movq	%rbx, %rdx
	callq	_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word
	xorq	%rax, 32(%rsp)
	leaq	1(%rbx), %rdx
	cmpq	%r13, %rdx
	jb	.LBB9_9
.LBB9_8:
	xorl	%eax, %eax
	xorq	%rax, 40(%rsp)
	leaq	2(%rbx), %rdx
	cmpq	%r13, %rdx
	jb	.LBB9_12
.LBB9_11:
	xorl	%eax, %eax
	xorq	%rax, 48(%rsp)
	leaq	3(%rbx), %rdx
	cmpq	%r13, %rdx
	jb	.LBB9_15
.LBB9_14:
	xorl	%eax, %eax
	xorq	%rax, 56(%rsp)
	leaq	4(%rbx), %rdx
	cmpq	%r13, %rdx
	jb	.LBB9_18
.LBB9_17:
	xorl	%eax, %eax
	xorq	%rax, 64(%rsp)
	leaq	5(%rbx), %rdx
	cmpq	%r13, %rdx
	jb	.LBB9_21
.LBB9_20:
	xorl	%eax, %eax
	xorq	%rax, 72(%rsp)
	leaq	6(%rbx), %rdx
	cmpq	%r13, %rdx
	jb	.LBB9_24
.LBB9_23:
	xorl	%eax, %eax
	xorq	%rax, 80(%rsp)
	leaq	7(%rbx), %rdx
	cmpq	%r13, %rdx
	jb	.LBB9_27
.LBB9_26:
	xorl	%eax, %eax
	xorq	%rax, 88(%rsp)
	leaq	8(%rbx), %rdx
	cmpq	%r13, %rdx
	jb	.LBB9_30
.LBB9_29:
	xorl	%eax, %eax
	xorq	%rax, 96(%rsp)
	leaq	9(%rbx), %rdx
	cmpq	%r13, %rdx
	jb	.LBB9_33
.LBB9_32:
	xorl	%eax, %eax
	xorq	%rax, 104(%rsp)
	leaq	10(%rbx), %rdx
	cmpq	%r13, %rdx
	jb	.LBB9_36
.LBB9_35:
	xorl	%eax, %eax
	xorq	%rax, 112(%rsp)
	leaq	11(%rbx), %rdx
	cmpq	%r13, %rdx
	jb	.LBB9_39
.LBB9_38:
	xorl	%eax, %eax
	xorq	%rax, 120(%rsp)
	leaq	12(%rbx), %rdx
	cmpq	%r13, %rdx
	jb	.LBB9_42
.LBB9_41:
	xorl	%eax, %eax
	xorq	%rax, 128(%rsp)
	leaq	13(%rbx), %rdx
	cmpq	%r13, %rdx
	jb	.LBB9_45
.LBB9_44:
	xorl	%eax, %eax
	xorq	%rax, 136(%rsp)
	leaq	14(%rbx), %rdx
	cmpq	%r13, %rdx
	jb	.LBB9_48
.LBB9_47:
	xorl	%eax, %eax
	xorq	%rax, 144(%rsp)
	leaq	15(%rbx), %rdx
	cmpq	%r13, %rdx
	jb	.LBB9_51
.LBB9_50:
	xorl	%eax, %eax
	xorq	%rax, 152(%rsp)
	addq	$16, %rbx
	cmpq	%r13, %rbx
	jb	.LBB9_54
.LBB9_53:
	xorl	%eax, %eax
	jmp	.LBB9_55
.LBB9_1:
	movq	8(%rsp), %rax
	movl	%eax, %r14d
	shll	$4, %r14d
	addq	%rax, %r14
	xorl	%ebp, %ebp
	leaq	32(%rsp), %rbx
	jmp	.LBB9_2
	.p2align	4
.LBB9_104:
	movq	%r12, %rdi
	movq	%r15, %rsi
	callq	_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word
.LBB9_105:
	xorq	%rax, 160(%rsp)
	movq	%rbx, %rdi
	callq	_RNvNtCsemcRClSg8DH_9native_vm6keccak8keccak_f
	addq	$17, %rbp
	cmpq	%rbp, %r14
	je	.LBB9_4
.LBB9_2:
	cmpq	%r13, %rbp
	jae	.LBB9_3
	movq	%r12, %rdi
	movq	%r15, %rsi
	movq	%rbp, %rdx
	callq	_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word
	xorq	%rax, 32(%rsp)
	leaq	1(%rbp), %rdx
	cmpq	%r13, %rdx
	jb	.LBB9_59
.LBB9_58:
	xorl	%eax, %eax
	xorq	%rax, 40(%rsp)
	leaq	2(%rbp), %rdx
	cmpq	%r13, %rdx
	jb	.LBB9_62
.LBB9_61:
	xorl	%eax, %eax
	xorq	%rax, 48(%rsp)
	leaq	3(%rbp), %rdx
	cmpq	%r13, %rdx
	jb	.LBB9_65
.LBB9_64:
	xorl	%eax, %eax
	xorq	%rax, 56(%rsp)
	leaq	4(%rbp), %rdx
	cmpq	%r13, %rdx
	jb	.LBB9_68
.LBB9_67:
	xorl	%eax, %eax
	xorq	%rax, 64(%rsp)
	leaq	5(%rbp), %rdx
	cmpq	%r13, %rdx
	jb	.LBB9_71
.LBB9_70:
	xorl	%eax, %eax
	xorq	%rax, 72(%rsp)
	leaq	6(%rbp), %rdx
	cmpq	%r13, %rdx
	jb	.LBB9_74
.LBB9_73:
	xorl	%eax, %eax
	xorq	%rax, 80(%rsp)
	leaq	7(%rbp), %rdx
	cmpq	%r13, %rdx
	jb	.LBB9_77
.LBB9_76:
	xorl	%eax, %eax
	xorq	%rax, 88(%rsp)
	leaq	8(%rbp), %rdx
	cmpq	%r13, %rdx
	jb	.LBB9_80
.LBB9_79:
	xorl	%eax, %eax
	xorq	%rax, 96(%rsp)
	leaq	9(%rbp), %rdx
	cmpq	%r13, %rdx
	jb	.LBB9_83
.LBB9_82:
	xorl	%eax, %eax
	xorq	%rax, 104(%rsp)
	leaq	10(%rbp), %rdx
	cmpq	%r13, %rdx
	jb	.LBB9_86
.LBB9_85:
	xorl	%eax, %eax
	xorq	%rax, 112(%rsp)
	leaq	11(%rbp), %rdx
	cmpq	%r13, %rdx
	jb	.LBB9_89
.LBB9_88:
	xorl	%eax, %eax
	xorq	%rax, 120(%rsp)
	leaq	12(%rbp), %rdx
	cmpq	%r13, %rdx
	jb	.LBB9_92
.LBB9_91:
	xorl	%eax, %eax
	xorq	%rax, 128(%rsp)
	leaq	13(%rbp), %rdx
	cmpq	%r13, %rdx
	jb	.LBB9_95
.LBB9_94:
	xorl	%eax, %eax
	xorq	%rax, 136(%rsp)
	leaq	14(%rbp), %rdx
	cmpq	%r13, %rdx
	jb	.LBB9_98
.LBB9_97:
	xorl	%eax, %eax
	xorq	%rax, 144(%rsp)
	leaq	15(%rbp), %rdx
	cmpq	%r13, %rdx
	jb	.LBB9_101
.LBB9_100:
	xorl	%eax, %eax
	xorq	%rax, 152(%rsp)
	leaq	16(%rbp), %rdx
	cmpq	%r13, %rdx
	jb	.LBB9_104
	jmp	.LBB9_103
	.p2align	4
.LBB9_3:
	xorl	%eax, %eax
	xorq	%rax, 32(%rsp)
	leaq	1(%rbp), %rdx
	cmpq	%r13, %rdx
	jae	.LBB9_58
.LBB9_59:
	movq	%r12, %rdi
	movq	%r15, %rsi
	callq	_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word
	xorq	%rax, 40(%rsp)
	leaq	2(%rbp), %rdx
	cmpq	%r13, %rdx
	jae	.LBB9_61
.LBB9_62:
	movq	%r12, %rdi
	movq	%r15, %rsi
	callq	_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word
	xorq	%rax, 48(%rsp)
	leaq	3(%rbp), %rdx
	cmpq	%r13, %rdx
	jae	.LBB9_64
.LBB9_65:
	movq	%r12, %rdi
	movq	%r15, %rsi
	callq	_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word
	xorq	%rax, 56(%rsp)
	leaq	4(%rbp), %rdx
	cmpq	%r13, %rdx
	jae	.LBB9_67
.LBB9_68:
	movq	%r12, %rdi
	movq	%r15, %rsi
	callq	_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word
	xorq	%rax, 64(%rsp)
	leaq	5(%rbp), %rdx
	cmpq	%r13, %rdx
	jae	.LBB9_70
.LBB9_71:
	movq	%r12, %rdi
	movq	%r15, %rsi
	callq	_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word
	xorq	%rax, 72(%rsp)
	leaq	6(%rbp), %rdx
	cmpq	%r13, %rdx
	jae	.LBB9_73
.LBB9_74:
	movq	%r12, %rdi
	movq	%r15, %rsi
	callq	_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word
	xorq	%rax, 80(%rsp)
	leaq	7(%rbp), %rdx
	cmpq	%r13, %rdx
	jae	.LBB9_76
.LBB9_77:
	movq	%r12, %rdi
	movq	%r15, %rsi
	callq	_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word
	xorq	%rax, 88(%rsp)
	leaq	8(%rbp), %rdx
	cmpq	%r13, %rdx
	jae	.LBB9_79
.LBB9_80:
	movq	%r12, %rdi
	movq	%r15, %rsi
	callq	_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word
	xorq	%rax, 96(%rsp)
	leaq	9(%rbp), %rdx
	cmpq	%r13, %rdx
	jae	.LBB9_82
.LBB9_83:
	movq	%r12, %rdi
	movq	%r15, %rsi
	callq	_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word
	xorq	%rax, 104(%rsp)
	leaq	10(%rbp), %rdx
	cmpq	%r13, %rdx
	jae	.LBB9_85
.LBB9_86:
	movq	%r12, %rdi
	movq	%r15, %rsi
	callq	_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word
	xorq	%rax, 112(%rsp)
	leaq	11(%rbp), %rdx
	cmpq	%r13, %rdx
	jae	.LBB9_88
.LBB9_89:
	movq	%r12, %rdi
	movq	%r15, %rsi
	callq	_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word
	xorq	%rax, 120(%rsp)
	leaq	12(%rbp), %rdx
	cmpq	%r13, %rdx
	jae	.LBB9_91
.LBB9_92:
	movq	%r12, %rdi
	movq	%r15, %rsi
	callq	_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word
	xorq	%rax, 128(%rsp)
	leaq	13(%rbp), %rdx
	cmpq	%r13, %rdx
	jae	.LBB9_94
.LBB9_95:
	movq	%r12, %rdi
	movq	%r15, %rsi
	callq	_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word
	xorq	%rax, 136(%rsp)
	leaq	14(%rbp), %rdx
	cmpq	%r13, %rdx
	jae	.LBB9_97
.LBB9_98:
	movq	%r12, %rdi
	movq	%r15, %rsi
	callq	_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word
	xorq	%rax, 144(%rsp)
	leaq	15(%rbp), %rdx
	cmpq	%r13, %rdx
	jae	.LBB9_100
.LBB9_101:
	movq	%r12, %rdi
	movq	%r15, %rsi
	callq	_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word
	xorq	%rax, 152(%rsp)
	leaq	16(%rbp), %rdx
	cmpq	%r13, %rdx
	jb	.LBB9_104
.LBB9_103:
	xorl	%eax, %eax
	jmp	.LBB9_105
.LBB9_5:
	xorl	%eax, %eax
	xorq	%rax, 32(%rsp)
	leaq	1(%rbx), %rdx
	cmpq	%r13, %rdx
	jae	.LBB9_8
.LBB9_9:
	movq	%r12, %rdi
	movq	%r15, %rsi
	callq	_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word
	xorq	%rax, 40(%rsp)
	leaq	2(%rbx), %rdx
	cmpq	%r13, %rdx
	jae	.LBB9_11
.LBB9_12:
	movq	%r12, %rdi
	movq	%r15, %rsi
	callq	_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word
	xorq	%rax, 48(%rsp)
	leaq	3(%rbx), %rdx
	cmpq	%r13, %rdx
	jae	.LBB9_14
.LBB9_15:
	movq	%r12, %rdi
	movq	%r15, %rsi
	callq	_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word
	xorq	%rax, 56(%rsp)
	leaq	4(%rbx), %rdx
	cmpq	%r13, %rdx
	jae	.LBB9_17
.LBB9_18:
	movq	%r12, %rdi
	movq	%r15, %rsi
	callq	_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word
	xorq	%rax, 64(%rsp)
	leaq	5(%rbx), %rdx
	cmpq	%r13, %rdx
	jae	.LBB9_20
.LBB9_21:
	movq	%r12, %rdi
	movq	%r15, %rsi
	callq	_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word
	xorq	%rax, 72(%rsp)
	leaq	6(%rbx), %rdx
	cmpq	%r13, %rdx
	jae	.LBB9_23
.LBB9_24:
	movq	%r12, %rdi
	movq	%r15, %rsi
	callq	_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word
	xorq	%rax, 80(%rsp)
	leaq	7(%rbx), %rdx
	cmpq	%r13, %rdx
	jae	.LBB9_26
.LBB9_27:
	movq	%r12, %rdi
	movq	%r15, %rsi
	callq	_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word
	xorq	%rax, 88(%rsp)
	leaq	8(%rbx), %rdx
	cmpq	%r13, %rdx
	jae	.LBB9_29
.LBB9_30:
	movq	%r12, %rdi
	movq	%r15, %rsi
	callq	_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word
	xorq	%rax, 96(%rsp)
	leaq	9(%rbx), %rdx
	cmpq	%r13, %rdx
	jae	.LBB9_32
.LBB9_33:
	movq	%r12, %rdi
	movq	%r15, %rsi
	callq	_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word
	xorq	%rax, 104(%rsp)
	leaq	10(%rbx), %rdx
	cmpq	%r13, %rdx
	jae	.LBB9_35
.LBB9_36:
	movq	%r12, %rdi
	movq	%r15, %rsi
	callq	_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word
	xorq	%rax, 112(%rsp)
	leaq	11(%rbx), %rdx
	cmpq	%r13, %rdx
	jae	.LBB9_38
.LBB9_39:
	movq	%r12, %rdi
	movq	%r15, %rsi
	callq	_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word
	xorq	%rax, 120(%rsp)
	leaq	12(%rbx), %rdx
	cmpq	%r13, %rdx
	jae	.LBB9_41
.LBB9_42:
	movq	%r12, %rdi
	movq	%r15, %rsi
	callq	_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word
	xorq	%rax, 128(%rsp)
	leaq	13(%rbx), %rdx
	cmpq	%r13, %rdx
	jae	.LBB9_44
.LBB9_45:
	movq	%r12, %rdi
	movq	%r15, %rsi
	callq	_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word
	xorq	%rax, 136(%rsp)
	leaq	14(%rbx), %rdx
	cmpq	%r13, %rdx
	jae	.LBB9_47
.LBB9_48:
	movq	%r12, %rdi
	movq	%r15, %rsi
	callq	_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word
	xorq	%rax, 144(%rsp)
	leaq	15(%rbx), %rdx
	cmpq	%r13, %rdx
	jae	.LBB9_50
.LBB9_51:
	movq	%r12, %rdi
	movq	%r15, %rsi
	callq	_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word
	xorq	%rax, 152(%rsp)
	addq	$16, %rbx
	cmpq	%r13, %rbx
	jae	.LBB9_53
.LBB9_54:
	movq	%r12, %rdi
	movq	%r15, %rsi
	movq	%rbx, %rdx
	callq	_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word
.LBB9_55:
	xorq	%rax, 160(%rsp)
	movq	16(%rsp), %rdx
	movl	%edx, %eax
	movl	$4042322161, %ecx
	imulq	%rax, %rcx
	shrq	$39, %rcx
	movl	%ecx, %eax
	shll	$7, %ecx
	leal	(%rcx,%rax,8), %eax
	subl	%eax, %edx
	leal	(,%rdx,8), %ecx
	movl	$1, %eax
	shlq	%cl, %rax
	andl	$248, %edx
	xorq	%rax, 32(%rsp,%rdx)
	xorb	$-128, 167(%rsp)
	leaq	32(%rsp), %rdi
	callq	_RNvNtCsemcRClSg8DH_9native_vm6keccak8keccak_f
	movq	32(%rsp), %rax
	movq	40(%rsp), %rcx
	movq	48(%rsp), %rdx
	movq	56(%rsp), %rsi
	movq	24(%rsp), %rdi
	movq	%rax, (%rdi)
	movq	%rcx, 8(%rdi)
	movq	%rdx, 16(%rdi)
	movq	%rsi, 24(%rdi)
	addq	$232, %rsp
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
	.size	_RINvNtCsemcRClSg8DH_9native_vm6keccak15keccak256_wordsNCNvNtB4_6verify14fiat_shamir_iv0EB4_, .Lfunc_end9-_RINvNtCsemcRClSg8DH_9native_vm6keccak15keccak256_wordsNCNvNtB4_6verify14fiat_shamir_iv0EB4_
	.cfi_endproc

	.section	.text._RINvNtCsemcRClSg8DH_9native_vm6layout14insertion_sortNCNvB2_13stack_offsetss_0EB4_,"ax",@progbits
	.p2align	4
	.type	_RINvNtCsemcRClSg8DH_9native_vm6layout14insertion_sortNCNvB2_13stack_offsetss_0EB4_,@function
_RINvNtCsemcRClSg8DH_9native_vm6layout14insertion_sortNCNvB2_13stack_offsetss_0EB4_:
.Lfunc_begin10:
	.cfi_startproc
	testq	%rsi, %rsi
	je	.LBB10_19
	pushq	%r14
	.cfi_def_cfa_offset 16
	pushq	%rbx
	.cfi_def_cfa_offset 24
	.cfi_offset %rbx, -24
	.cfi_offset %r14, -16
	movq	$-1, %rax
	xorl	%r8d, %r8d
	jmp	.LBB10_2
	.p2align	4
.LBB10_17:
	incq	%r8
	incq	%rax
	cmpq	%rsi, %r8
	je	.LBB10_18
.LBB10_2:
	testq	%r8, %r8
	je	.LBB10_17
	movq	(%rdi,%r8,8), %r9
	movq	%rax, %r10
	.p2align	4
.LBB10_4:
	movq	(%rdi,%r10,8), %r11
	cmpq	%rcx, %r11
	jae	.LBB10_5
	movq	(%rdx,%r11,8), %r14
	cmpq	%rcx, %r9
	jb	.LBB10_9
.LBB10_8:
	xorl	%ebx, %ebx
	jmp	.LBB10_10
	.p2align	4
.LBB10_5:
	xorl	%r14d, %r14d
	cmpq	%rcx, %r9
	jae	.LBB10_8
.LBB10_9:
	movq	(%rdx,%r9,8), %rbx
	cmpq	%rbx, %r14
	jb	.LBB10_15
.LBB10_10:
	cmpq	%rcx, %r11
	jae	.LBB10_11
	movq	(%rdx,%r11,8), %r14
	cmpq	%r11, %r9
	jb	.LBB10_14
	jmp	.LBB10_17
	.p2align	4
.LBB10_11:
	xorl	%r14d, %r14d
	cmpq	%r11, %r9
	jae	.LBB10_17
.LBB10_14:
	cmpq	%r14, %rbx
	jne	.LBB10_17
.LBB10_15:
	movq	%r11, 8(%rdi,%r10,8)
	movq	%r9, (%rdi,%r10,8)
	movq	%r10, %r11
	addq	$-1, %r11
	jae	.LBB10_17
	cmpq	%rsi, %r10
	movq	%r11, %r10
	jb	.LBB10_4
	jmp	.LBB10_17
.LBB10_18:
	popq	%rbx
	.cfi_def_cfa_offset 16
	popq	%r14
	.cfi_def_cfa_offset 8
	.cfi_restore %rbx
	.cfi_restore %r14
.LBB10_19:
	retq
.Lfunc_end10:
	.size	_RINvNtCsemcRClSg8DH_9native_vm6layout14insertion_sortNCNvB2_13stack_offsetss_0EB4_, .Lfunc_end10-_RINvNtCsemcRClSg8DH_9native_vm6layout14insertion_sortNCNvB2_13stack_offsetss_0EB4_
	.cfi_endproc

	.section	.text._RNCNvNtCsemcRClSg8DH_9native_vm3bus18verify_bus_balance0B5_,"ax",@progbits
	.p2align	4
	.type	_RNCNvNtCsemcRClSg8DH_9native_vm3bus18verify_bus_balance0B5_,@function
_RNCNvNtCsemcRClSg8DH_9native_vm3bus18verify_bus_balance0B5_:
.Lfunc_begin11:
	.cfi_startproc
	pushq	%r15
	.cfi_def_cfa_offset 16
	pushq	%r14
	.cfi_def_cfa_offset 24
	pushq	%rbx
	.cfi_def_cfa_offset 32
	.cfi_offset %rbx, -32
	.cfi_offset %r14, -24
	.cfi_offset %r15, -16
	movq	%r9, %rax
	movq	%r8, %r10
	movq	%rcx, %r11
	movq	%rdx, %rbx
	movq	%rsi, %r14
	movq	(%rsi), %rsi
	movq	8(%r14), %rdx
	movq	16(%r14), %rcx
	movq	24(%r14), %r8
	movq	32(%r14), %r9
	movq	48(%r14), %r15
	pushq	32(%rsp)
	.cfi_adjust_cfa_offset 8
	pushq	%rax
	.cfi_adjust_cfa_offset 8
	pushq	%r10
	.cfi_adjust_cfa_offset 8
	pushq	%r11
	.cfi_adjust_cfa_offset 8
	pushq	%rbx
	.cfi_adjust_cfa_offset 8
	pushq	8(%r15)
	.cfi_adjust_cfa_offset 8
	pushq	(%r15)
	.cfi_adjust_cfa_offset 8
	pushq	40(%r14)
	.cfi_adjust_cfa_offset 8
	callq	_RNvNtCsemcRClSg8DH_9native_vm3bus12fingerprints
	addq	$64, %rsp
	.cfi_adjust_cfa_offset -64
	popq	%rbx
	.cfi_def_cfa_offset 24
	popq	%r14
	.cfi_def_cfa_offset 16
	popq	%r15
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end11:
	.size	_RNCNvNtCsemcRClSg8DH_9native_vm3bus18verify_bus_balance0B5_, .Lfunc_end11-_RNCNvNtCsemcRClSg8DH_9native_vm3bus18verify_bus_balance0B5_
	.cfi_endproc

	.section	.text._RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW12absorb_nonce,"ax",@progbits
	.p2align	4
	.type	_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW12absorb_nonce,@function
_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW12absorb_nonce:
.Lfunc_begin12:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rdi, %rbx
	movl	$4, %ecx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW6absorb
	movq	%rbx, %rdi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW6duplex
	movq	(%rbx), %rax
	movq	8(%rbx), %rcx
	movq	$1, 304(%rbx)
	movq	%rax, 312(%rbx)
	movq	%rcx, 320(%rbx)
	movq	16(%rbx), %rax
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end12:
	.size	_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW12absorb_nonce, .Lfunc_end12-_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW12absorb_nonce
	.cfi_endproc

	.section	.text._RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW12duplex_input,"ax",@progbits
	.p2align	4
	.type	_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW12duplex_input,@function
_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW12duplex_input:
.Lfunc_begin13:
	.cfi_startproc
	movq	296(%rdi), %rax
	testq	%rax, %rax
	je	.LBB13_1
	movq	200(%rdi), %rcx
	movq	208(%rdi), %rdx
	movq	216(%rdi), %rsi
	movq	%rcx, (%rdi)
	movq	%rdx, 8(%rdi)
	movq	$0, 16(%rdi)
	movq	%rsi, 24(%rdi)
	cmpq	$1, %rax
	je	.LBB13_3
	movq	224(%rdi), %rcx
	movq	232(%rdi), %rdx
	movq	240(%rdi), %rsi
	movq	%rcx, 32(%rdi)
	movq	%rdx, 40(%rdi)
	movq	$0, 48(%rdi)
	movq	%rsi, 56(%rdi)
	cmpq	$2, %rax
	jbe	.LBB13_5
	movq	248(%rdi), %rcx
	movq	256(%rdi), %rdx
	movq	264(%rdi), %rsi
	movq	%rcx, 64(%rdi)
	movq	%rdx, 72(%rdi)
	movq	$0, 80(%rdi)
	movq	%rsi, 88(%rdi)
	cmpq	$3, %rax
	je	.LBB13_7
	movq	272(%rdi), %rdx
	movq	280(%rdi), %rcx
	movq	288(%rdi), %rax
	jmp	.LBB13_9
.LBB13_1:
	movq	$0, (%rdi)
	movq	$0, 8(%rdi)
	movq	$0, 16(%rdi)
	movq	$0, 24(%rdi)
.LBB13_3:
	movq	$0, 32(%rdi)
	movq	$0, 40(%rdi)
	movq	$0, 48(%rdi)
	movq	$0, 56(%rdi)
.LBB13_5:
	movq	$0, 64(%rdi)
	movq	$0, 72(%rdi)
	movq	$0, 80(%rdi)
	movq	$0, 88(%rdi)
.LBB13_7:
	xorl	%eax, %eax
	xorl	%ecx, %ecx
	xorl	%edx, %edx
.LBB13_9:
	movq	%rdx, 96(%rdi)
	movq	%rcx, 104(%rdi)
	movq	$0, 112(%rdi)
	movq	%rax, 120(%rdi)
	retq
.Lfunc_end13:
	.size	_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW12duplex_input, .Lfunc_end13-_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW12duplex_input
	.cfi_endproc

	.section	.text._RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW6absorb,"ax",@progbits
	.p2align	4
	.type	_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW6absorb,@function
_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW6absorb:
.Lfunc_begin14:
	.cfi_startproc
	pushq	%r15
	.cfi_def_cfa_offset 16
	pushq	%r14
	.cfi_def_cfa_offset 24
	pushq	%r12
	.cfi_def_cfa_offset 32
	pushq	%rbx
	.cfi_def_cfa_offset 40
	pushq	%rax
	.cfi_def_cfa_offset 48
	.cfi_offset %rbx, -40
	.cfi_offset %r12, -32
	.cfi_offset %r14, -24
	.cfi_offset %r15, -16
	movq	%rcx, %r14
	movq	%rdx, %r15
	movq	%rsi, %r12
	movq	%rdi, %rbx
	movq	296(%rdi), %rax
	cmpq	$4, %rax
	jb	.LBB14_2
	movq	%rbx, %rdi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW6duplex
	movq	296(%rbx), %rax
	cmpq	$3, %rax
	ja	.LBB14_3
.LBB14_2:
	leaq	(%rax,%rax,2), %rcx
	movq	%r12, 200(%rbx,%rcx,8)
	movq	%r15, 208(%rbx,%rcx,8)
	movq	%r14, 216(%rbx,%rcx,8)
	incq	%rax
	movq	%rax, 296(%rbx)
.LBB14_3:
	addq	$8, %rsp
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
.Lfunc_end14:
	.size	_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW6absorb, .Lfunc_end14-_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW6absorb
	.cfi_endproc

	.section	.text._RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW6duplex,"ax",@progbits
	.p2align	4
	.type	_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW6duplex,@function
_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW6duplex:
.Lfunc_begin15:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rdi, %rbx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW12duplex_input
	movq	%rbx, %rdi
	callq	_RNvNtCsemcRClSg8DH_9native_vm6keccak8keccak_f
	movq	$0, 296(%rbx)
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end15:
	.size	_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW6duplex, .Lfunc_end15-_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW6duplex
	.cfi_endproc

	.section	.text._RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW7squeeze,"ax",@progbits
	.p2align	4
	.type	_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW7squeeze,@function
_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW7squeeze:
.Lfunc_begin16:
	.cfi_startproc
	movq	312(%rdi), %rax
	movq	320(%rdi), %rdx
	testb	$1, 304(%rdi)
	movq	$0, 304(%rdi)
	jne	.LBB16_2
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rdi, %rbx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW6duplex
	movq	(%rbx), %rax
	movq	8(%rbx), %rdx
	popq	%rbx
	.cfi_def_cfa_offset 8
	.cfi_restore %rbx
.LBB16_2:
	retq
.Lfunc_end16:
	.size	_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW7squeeze, .Lfunc_end16-_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW7squeeze
	.cfi_endproc

	.section	.text._RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKj1e_E6extendB4_,"ax",@progbits
	.p2align	4
	.type	_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKj1e_E6extendB4_,@function
_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKj1e_E6extendB4_:
.Lfunc_begin17:
	.cfi_startproc
	movb	$1, %al
	testq	%rdx, %rdx
	je	.LBB17_6
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	shlq	$4, %rdx
	movq	(%rdi), %r9
	cmpq	$31, %r9
	movl	$30, %ecx
	cmovaeq	%r9, %rcx
	leaq	1(%r9), %r8
	shlq	$4, %r9
	addq	%rdi, %r9
	addq	$16, %r9
	negq	%rcx
	xorl	%r10d, %r10d
	.p2align	4
.LBB17_2:
	leaq	(%rcx,%r8), %r11
	cmpq	$1, %r11
	je	.LBB17_3
	movq	(%rsi,%r10), %r11
	movq	8(%rsi,%r10), %rbx
	movq	%r11, -8(%r9,%r10)
	movq	%rbx, (%r9,%r10)
	movq	%r8, (%rdi)
	addq	$16, %r10
	incq	%r8
	cmpq	%r10, %rdx
	jne	.LBB17_2
	jmp	.LBB17_5
.LBB17_3:
	xorl	%eax, %eax
.LBB17_5:
	popq	%rbx
	.cfi_def_cfa_offset 8
	.cfi_restore %rbx
.LBB17_6:
	retq
.Lfunc_end17:
	.size	_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKj1e_E6extendB4_, .Lfunc_end17-_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKj1e_E6extendB4_
	.cfi_endproc

	.section	.text._RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKj24_E6extendB4_,"ax",@progbits
	.p2align	4
	.type	_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKj24_E6extendB4_,@function
_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKj24_E6extendB4_:
.Lfunc_begin18:
	.cfi_startproc
	movb	$1, %al
	testq	%rdx, %rdx
	je	.LBB18_6
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	shlq	$4, %rdx
	movq	(%rdi), %r9
	cmpq	$37, %r9
	movl	$36, %ecx
	cmovaeq	%r9, %rcx
	leaq	1(%r9), %r8
	shlq	$4, %r9
	addq	%rdi, %r9
	addq	$16, %r9
	negq	%rcx
	xorl	%r10d, %r10d
	.p2align	4
.LBB18_2:
	leaq	(%rcx,%r8), %r11
	cmpq	$1, %r11
	je	.LBB18_3
	movq	(%rsi,%r10), %r11
	movq	8(%rsi,%r10), %rbx
	movq	%r11, -8(%r9,%r10)
	movq	%rbx, (%r9,%r10)
	movq	%r8, (%rdi)
	addq	$16, %r10
	incq	%r8
	cmpq	%r10, %rdx
	jne	.LBB18_2
	jmp	.LBB18_5
.LBB18_3:
	xorl	%eax, %eax
.LBB18_5:
	popq	%rbx
	.cfi_def_cfa_offset 8
	.cfi_restore %rbx
.LBB18_6:
	retq
.Lfunc_end18:
	.size	_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKj24_E6extendB4_, .Lfunc_end18-_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKj24_E6extendB4_
	.cfi_endproc

	.section	.text._RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKj3f_E6extendB4_,"ax",@progbits
	.p2align	4
	.type	_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKj3f_E6extendB4_,@function
_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKj3f_E6extendB4_:
.Lfunc_begin19:
	.cfi_startproc
	movb	$1, %al
	testq	%rdx, %rdx
	je	.LBB19_6
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	shlq	$4, %rdx
	movq	(%rdi), %r9
	cmpq	$64, %r9
	movl	$63, %ecx
	cmovaeq	%r9, %rcx
	leaq	1(%r9), %r8
	shlq	$4, %r9
	addq	%rdi, %r9
	addq	$16, %r9
	negq	%rcx
	xorl	%r10d, %r10d
	.p2align	4
.LBB19_2:
	leaq	(%rcx,%r8), %r11
	cmpq	$1, %r11
	je	.LBB19_3
	movq	(%rsi,%r10), %r11
	movq	8(%rsi,%r10), %rbx
	movq	%r11, -8(%r9,%r10)
	movq	%rbx, (%r9,%r10)
	movq	%r8, (%rdi)
	addq	$16, %r10
	incq	%r8
	cmpq	%r10, %rdx
	jne	.LBB19_2
	jmp	.LBB19_5
.LBB19_3:
	xorl	%eax, %eax
.LBB19_5:
	popq	%rbx
	.cfi_def_cfa_offset 8
	.cfi_restore %rbx
.LBB19_6:
	retq
.Lfunc_end19:
	.size	_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKj3f_E6extendB4_, .Lfunc_end19-_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKj3f_E6extendB4_
	.cfi_endproc

	.section	.text._RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKje6_E6extendB4_,"ax",@progbits
	.p2align	4
	.type	_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKje6_E6extendB4_,@function
_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKje6_E6extendB4_:
.Lfunc_begin20:
	.cfi_startproc
	movb	$1, %al
	testq	%rdx, %rdx
	je	.LBB20_6
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	shlq	$4, %rdx
	movq	(%rdi), %r9
	cmpq	$231, %r9
	movl	$230, %ecx
	cmovaeq	%r9, %rcx
	leaq	1(%r9), %r8
	shlq	$4, %r9
	addq	%rdi, %r9
	addq	$16, %r9
	negq	%rcx
	xorl	%r10d, %r10d
	.p2align	4
.LBB20_2:
	leaq	(%rcx,%r8), %r11
	cmpq	$1, %r11
	je	.LBB20_3
	movq	(%rsi,%r10), %r11
	movq	8(%rsi,%r10), %rbx
	movq	%r11, -8(%r9,%r10)
	movq	%rbx, (%r9,%r10)
	movq	%r8, (%rdi)
	addq	$16, %r10
	incq	%r8
	cmpq	%r10, %rdx
	jne	.LBB20_2
	jmp	.LBB20_5
.LBB20_3:
	xorl	%eax, %eax
.LBB20_5:
	popq	%rbx
	.cfi_def_cfa_offset 8
	.cfi_restore %rbx
.LBB20_6:
	retq
.Lfunc_end20:
	.size	_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKje6_E6extendB4_, .Lfunc_end20-_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKje6_E6extendB4_
	.cfi_endproc

	.section	.text._RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufyKje6_E6extendB4_,"ax",@progbits
	.p2align	4
	.type	_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufyKje6_E6extendB4_,@function
_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufyKje6_E6extendB4_:
.Lfunc_begin21:
	.cfi_startproc
	movb	$1, %al
	testq	%rdx, %rdx
	je	.LBB21_5
	shlq	$3, %rdx
	movq	(%rdi), %rcx
	cmpq	$231, %rcx
	movl	$230, %r8d
	cmovaeq	%rcx, %r8
	incq	%rcx
	negq	%r8
	.p2align	4
.LBB21_2:
	leaq	(%r8,%rcx), %r9
	cmpq	$1, %r9
	je	.LBB21_3
	movq	(%rsi), %r9
	addq	$8, %rsi
	movq	%r9, (%rdi,%rcx,8)
	movq	%rcx, (%rdi)
	incq	%rcx
	addq	$-8, %rdx
	jne	.LBB21_2
.LBB21_5:
	retq
.LBB21_3:
	xorl	%eax, %eax
	retq
.Lfunc_end21:
	.size	_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufyKje6_E6extendB4_, .Lfunc_end21-_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufyKje6_E6extendB4_
	.cfi_endproc

	.section	.text._RNvMNtCsemcRClSg8DH_9native_vm4whirNtB2_6BasisW4eval,"ax",@progbits
	.p2align	4
	.type	_RNvMNtCsemcRClSg8DH_9native_vm4whirNtB2_6BasisW4eval,@function
_RNvMNtCsemcRClSg8DH_9native_vm4whirNtB2_6BasisW4eval:
.Lfunc_begin22:
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
	subq	$88, %rsp
	.cfi_def_cfa_offset 144
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	%rcx, 24(%rsp)
	movq	%rdx, 16(%rsp)
	movq	%rsi, %rbx
	movq	%rdi, 8(%rsp)
	movq	(%rsi), %rbp
	movq	8(%rsi), %r15
	movq	16(%rsi), %rdi
	movl	$4, %esi
	movq	%rdi, 48(%rsp)
	callq	_RNvMs2_NtCsemcRClSg8DH_9native_vm6layoutNtB5_7LayoutW9placement
	testq	%r15, %r15
	je	.LBB22_1
	leaq	16(%rbp), %r13
	movq	(%rbp), %r14
	movq	8(%rbp), %rcx
	movq	%rcx, (%rsp)
	jmp	.LBB22_3
.LBB22_1:
	movq	$0, (%rsp)
	xorl	%r14d, %r14d
	movq	%rbp, %r13
.LBB22_3:
	movq	32(%rbx), %rcx
	movq	(%rcx), %rsi
	addq	$8, %rcx
	xorl	%r8d, %r8d
	cmpq	$37, %rsi
	movl	$8, %r12d
	cmovaeq	%r12, %rcx
	movq	24(%rbx), %r9
	cmovbq	%rsi, %r8
	addq	$16, %r9
	leaq	56(%rsp), %rdi
	movq	%rax, %rsi
	pushq	24(%rsp)
	.cfi_adjust_cfa_offset 8
	pushq	24(%rsp)
	.cfi_adjust_cfa_offset 8
	callq	_RNvNtCsemcRClSg8DH_9native_vm5stack17ring_claim_weight
	addq	$16, %rsp
	.cfi_adjust_cfa_offset -16
	cmpl	$1, 56(%rsp)
	jne	.LBB22_16
	shlq	$4, %r15
	addq	%r15, %rbp
	movq	64(%rsp), %rdx
	movq	72(%rsp), %rcx
	movq	%r14, %rdi
	movq	(%rsp), %rsi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	movq	%rax, (%rsp)
	movq	%rbx, 32(%rsp)
	movq	40(%rbx), %rax
	movq	(%rax), %rcx
	addq	$8, %rax
	imulq	$608, %rcx, %rsi
	xorl	%ebx, %ebx
	cmpq	$161, %rcx
	cmovbq	%rax, %r12
	movq	%rdx, 40(%rsp)
	cmovbq	%rsi, %rbx
	testq	%rbx, %rbx
	je	.LBB22_10
	movq	48(%rsp), %rax
	leaq	120(%rax), %rcx
	addq	$16, %r12
	movq	%rcx, 80(%rsp)
	jmp	.LBB22_6
	.p2align	4
.LBB22_15:
	addq	$608, %r12
	addq	$-608, %rbx
	je	.LBB22_10
.LBB22_6:
	movq	-16(%r12), %rax
	cmpq	$158, %rax
	jae	.LBB22_15
	leaq	(%rax,%rax,2), %rax
	cmpq	$0, (%rcx,%rax,8)
	je	.LBB22_15
	leaq	(%rcx,%rax,8), %rax
	movq	8(%rax), %rsi
	movq	16(%rax), %rdx
	cmpq	%rbp, %r13
	je	.LBB22_9
	movq	(%r13), %r14
	movq	8(%r13), %r15
	addq	$16, %r13
	jmp	.LBB22_13
.LBB22_9:
	xorl	%r14d, %r14d
	xorl	%r15d, %r15d
	movq	%rbp, %r13
.LBB22_13:
	movq	-8(%r12), %r8
	cmpq	$37, %r8
	movl	$8, %ecx
	cmovbq	%r12, %rcx
	movl	$0, %eax
	cmovaeq	%rax, %r8
	movq	48(%rsp), %rax
	movq	16(%rax), %r9
	leaq	56(%rsp), %rdi
	pushq	24(%rsp)
	.cfi_adjust_cfa_offset 8
	pushq	24(%rsp)
	.cfi_adjust_cfa_offset 8
	callq	_RNvNtCsemcRClSg8DH_9native_vm5stack13column_weight
	addq	$16, %rsp
	.cfi_adjust_cfa_offset -16
	cmpl	$1, 56(%rsp)
	jne	.LBB22_16
	movq	64(%rsp), %rdx
	movq	72(%rsp), %rcx
	movq	%r14, %rdi
	movq	%r15, %rsi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	xorq	%rax, (%rsp)
	xorq	%rdx, 40(%rsp)
	movq	80(%rsp), %rcx
	jmp	.LBB22_15
.LBB22_16:
	xorl	%eax, %eax
	movq	8(%rsp), %rcx
	jmp	.LBB22_17
.LBB22_10:
	cmpq	%rbp, %r13
	je	.LBB22_11
	movq	(%r13), %r14
	movq	8(%r13), %r15
	jmp	.LBB22_19
.LBB22_11:
	xorl	%r14d, %r14d
	xorl	%r15d, %r15d
.LBB22_19:
	movq	32(%rsp), %rax
	movq	48(%rax), %rax
	movq	(%rax), %rcx
	addq	$8, %rax
	xorl	%esi, %esi
	cmpq	$31, %rcx
	movl	$8, %edi
	cmovbq	%rax, %rdi
	cmovbq	%rcx, %rsi
	movq	16(%rsp), %rdx
	movq	24(%rsp), %rcx
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field7eq_eval
	movq	%rdx, %rcx
	movq	%r14, %rdi
	movq	%r15, %rsi
	movq	%rax, %rdx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	xorq	(%rsp), %rax
	xorq	40(%rsp), %rdx
	movq	8(%rsp), %rcx
	movq	%rax, 8(%rcx)
	movq	%rdx, 16(%rcx)
	movl	$1, %eax
.LBB22_17:
	movq	%rax, (%rcx)
	addq	$88, %rsp
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
.Lfunc_end22:
	.size	_RNvMNtCsemcRClSg8DH_9native_vm4whirNtB2_6BasisW4eval, .Lfunc_end22-_RNvMNtCsemcRClSg8DH_9native_vm4whirNtB2_6BasisW4eval
	.cfi_endproc

	.section	.text._RNvMNtCsemcRClSg8DH_9native_vm4wireNtB2_6Reader2le,"ax",@progbits
	.p2align	4
	.type	_RNvMNtCsemcRClSg8DH_9native_vm4wireNtB2_6Reader2le,@function
_RNvMNtCsemcRClSg8DH_9native_vm4wireNtB2_6Reader2le:
.Lfunc_begin23:
	.cfi_startproc
	movq	16(%rdi), %rcx
	xorl	%eax, %eax
	movq	%rcx, %r8
	addq	%rsi, %r8
	jb	.LBB23_7
	cmpq	8(%rdi), %r8
	ja	.LBB23_7
	movq	%r8, 16(%rdi)
	addq	(%rdi), %rcx
	movl	-4(%rsi,%rcx), %edx
	movl	$1, %eax
	cmpq	$4, %rsi
	je	.LBB23_7
	movzbl	-5(%rcx,%rsi), %edi
	shlq	$8, %rdx
	orq	%rdi, %rdx
	cmpq	$5, %rsi
	je	.LBB23_7
	movzbl	-6(%rcx,%rsi), %edi
	shlq	$8, %rdx
	orq	%rdi, %rdx
	cmpq	$6, %rsi
	je	.LBB23_7
	movzbl	-7(%rcx,%rsi), %edi
	shlq	$8, %rdx
	orq	%rdi, %rdx
	cmpq	$7, %rsi
	je	.LBB23_7
	movzbl	-8(%rcx,%rsi), %ecx
	shlq	$8, %rdx
	orq	%rcx, %rdx
.LBB23_7:
	retq
.Lfunc_end23:
	.size	_RNvMNtCsemcRClSg8DH_9native_vm4wireNtB2_6Reader2le, .Lfunc_end23-_RNvMNtCsemcRClSg8DH_9native_vm4wireNtB2_6Reader2le
	.cfi_endproc

	.section	.text._RNvMNtCsemcRClSg8DH_9native_vm4wireNtB2_6Reader5words,"ax",@progbits
	.p2align	4
	.type	_RNvMNtCsemcRClSg8DH_9native_vm4wireNtB2_6Reader5words,@function
_RNvMNtCsemcRClSg8DH_9native_vm4wireNtB2_6Reader5words:
.Lfunc_begin24:
	.cfi_startproc
	pushq	%r15
	.cfi_def_cfa_offset 16
	pushq	%r14
	.cfi_def_cfa_offset 24
	pushq	%r12
	.cfi_def_cfa_offset 32
	pushq	%rbx
	.cfi_def_cfa_offset 40
	pushq	%rax
	.cfi_def_cfa_offset 48
	.cfi_offset %rbx, -40
	.cfi_offset %r12, -32
	.cfi_offset %r14, -24
	.cfi_offset %r15, -16
	leaq	(,%rdx,8), %r15
	xorl	%eax, %eax
	movq	16(%rdi), %rcx
	addq	%r15, %rcx
	jb	.LBB24_8
	movq	%rdi, %r14
	cmpq	8(%rdi), %rcx
	ja	.LBB24_8
	movb	$1, %al
	testq	%rdx, %rdx
	je	.LBB24_8
	movq	%rsi, %rbx
	xorl	%r12d, %r12d
	.p2align	4
.LBB24_4:
	movl	$8, %esi
	movq	%r14, %rdi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm4wireNtB2_6Reader2le
	cmpq	$1, %rax
	jne	.LBB24_5
	movq	%rdx, (%rbx,%r12)
	addq	$8, %r12
	cmpq	%r12, %r15
	jne	.LBB24_4
	movb	$1, %al
	jmp	.LBB24_8
.LBB24_5:
	xorl	%eax, %eax
.LBB24_8:
	addq	$8, %rsp
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
.Lfunc_end24:
	.size	_RNvMNtCsemcRClSg8DH_9native_vm4wireNtB2_6Reader5words, .Lfunc_end24-_RNvMNtCsemcRClSg8DH_9native_vm4wireNtB2_6Reader5words
	.cfi_endproc

	.section	.text._RNvMNtCsemcRClSg8DH_9native_vm4wireNtB2_6Reader6digest,"ax",@progbits
	.p2align	4
	.type	_RNvMNtCsemcRClSg8DH_9native_vm4wireNtB2_6Reader6digest,@function
_RNvMNtCsemcRClSg8DH_9native_vm4wireNtB2_6Reader6digest:
.Lfunc_begin25:
	.cfi_startproc
	pushq	%r15
	.cfi_def_cfa_offset 16
	pushq	%r14
	.cfi_def_cfa_offset 24
	pushq	%r13
	.cfi_def_cfa_offset 32
	pushq	%r12
	.cfi_def_cfa_offset 40
	pushq	%rbx
	.cfi_def_cfa_offset 48
	.cfi_offset %rbx, -48
	.cfi_offset %r12, -40
	.cfi_offset %r13, -32
	.cfi_offset %r14, -24
	.cfi_offset %r15, -16
	movq	%rsi, %r14
	movq	%rdi, %rbx
	movl	$8, %esi
	movq	%r14, %rdi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm4wireNtB2_6Reader2le
	cmpq	$1, %rax
	jne	.LBB25_8
	movq	%rdx, %r12
	movl	$8, %esi
	movq	%r14, %rdi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm4wireNtB2_6Reader2le
	cmpq	$1, %rax
	jne	.LBB25_8
	movq	%rdx, %r13
	movl	$8, %esi
	movq	%r14, %rdi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm4wireNtB2_6Reader2le
	cmpq	$1, %rax
	jne	.LBB25_8
	movq	%rdx, %r15
	movl	$8, %esi
	movq	%r14, %rdi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm4wireNtB2_6Reader2le
	cmpq	$1, %rax
	jne	.LBB25_8
	movq	%r12, 8(%rbx)
	movq	%r13, 16(%rbx)
	movq	%r15, 24(%rbx)
	movq	%rdx, 32(%rbx)
	movl	$1, %eax
	jmp	.LBB25_9
.LBB25_8:
	xorl	%eax, %eax
.LBB25_9:
	movq	%rax, (%rbx)
	popq	%rbx
	.cfi_def_cfa_offset 40
	popq	%r12
	.cfi_def_cfa_offset 32
	popq	%r13
	.cfi_def_cfa_offset 24
	popq	%r14
	.cfi_def_cfa_offset 16
	popq	%r15
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end25:
	.size	_RNvMNtCsemcRClSg8DH_9native_vm4wireNtB2_6Reader6digest, .Lfunc_end25-_RNvMNtCsemcRClSg8DH_9native_vm4wireNtB2_6Reader6digest
	.cfi_endproc

	.section	.text._RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul,"ax",@progbits
	.p2align	4
	.type	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul,@function
_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul:
.Lfunc_begin26:
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
	subq	$96, %rsp
	.cfi_def_cfa_offset 152
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	%rcx, 8(%rsp)
	movq	%rsi, 32(%rsp)
	movq	%rdi, (%rsp)
	movabsq	$1229782938247303441, %rax
	movq	%rdi, %rsi
	movq	%rdi, %rcx
	movq	%rdi, %r8
	movq	%rdi, %r9
	andq	%rax, %r9
	movabsq	$2459565876494606882, %r14
	andq	%r14, %rsi
	movabsq	$-8608480567731124088, %r11
	movq	%rdx, %r10
	movq	%rdx, %rbp
	movq	%rdx, %r12
	movq	%rdx, 24(%rsp)
	andq	%rax, %rbp
	andq	%r11, %r10
	movq	%rbp, %rax
	imulq	%r9, %rax
	movq	%r10, %rbx
	imulq	%rsi, %rbx
	xorq	%rax, %rbx
	movabsq	$4919131752989213764, %rdi
	andq	%rdi, %rcx
	andq	%r11, %r8
	movq	%rdx, %r15
	andq	%r14, %r15
	movq	%r14, %rdx
	movq	%r12, %r14
	andq	%rdi, %r14
	movq	%r14, %rax
	imulq	%rcx, %rax
	movq	%r15, %r11
	imulq	%r8, %r11
	xorq	%rax, %r11
	xorq	%rbx, %r11
	movq	%r15, %rax
	imulq	%r9, %rax
	movq	%rbp, %r12
	imulq	%rsi, %r12
	xorq	%rax, %r12
	movq	%r10, %rax
	imulq	%rcx, %rax
	movq	%r14, %rbx
	imulq	%r8, %rbx
	xorq	%rax, %rbx
	xorq	%r12, %rbx
	movq	%r14, %rax
	imulq	%r9, %rax
	movq	%r15, %r12
	imulq	%rsi, %r12
	xorq	%rax, %r12
	movq	%rbp, %r13
	imulq	%rcx, %r13
	movq	%r10, %rax
	imulq	%r8, %rax
	xorq	%r13, %rax
	xorq	%r12, %rax
	imulq	%r9, %r10
	imulq	%rsi, %r14
	xorq	%r10, %r14
	imulq	%rcx, %r15
	imulq	%r8, %rbp
	xorq	%r15, %rbp
	xorq	%r14, %rbp
	movabsq	$1229782938247303441, %rcx
	andq	%rcx, %r11
	andq	%rdx, %rbx
	movq	%rdx, %r9
	orq	%r11, %rbx
	andq	%rdi, %rax
	movq	%rdi, %r12
	orq	%rbx, %rax
	movq	32(%rsp), %rcx
	movq	%rcx, 72(%rsp)
	movq	%rcx, 64(%rsp)
	movq	%rcx, 16(%rsp)
	movq	%rcx, 80(%rsp)
	movq	%rcx, 56(%rsp)
	movq	(%rsp), %rdi
	xorq	%rdi, %rcx
	movq	%rcx, 32(%rsp)
	movabsq	$-8608480567731124088, %rsi
	andq	%rsi, %rbp
	bswapq	%rdi
	orq	%rax, %rbp
	movq	%rbp, 88(%rsp)
	movq	%rdi, %rax
	shrq	$4, %rax
	movabsq	$1085102592571150095, %r10
	andq	%r10, %rax
	andq	%r10, %rdi
	shlq	$4, %rdi
	orq	%rax, %rdi
	movabsq	$3689348814741910323, %r8
	movq	%rdi, %rax
	andq	%r8, %rax
	shrq	$2, %rdi
	andq	%r8, %rdi
	leaq	(%rdi,%rax,4), %rax
	movq	8(%rsp), %rcx
	movq	%rcx, (%rsp)
	movq	%rcx, 48(%rsp)
	movq	%rcx, %rbp
	movq	%rcx, 40(%rsp)
	movq	%rcx, %r13
	movq	24(%rsp), %rdx
	xorq	%rdx, %rcx
	movq	%rcx, 8(%rsp)
	movabsq	$6148914691236517205, %rdi
	movq	%rax, %rcx
	andq	%rdi, %rcx
	shrq	%rax
	andq	%rdi, %rax
	bswapq	%rdx
	leaq	(%rax,%rcx,2), %r11
	movq	%rdx, %rax
	shrq	$4, %rax
	andq	%r10, %rax
	andq	%r10, %rdx
	shlq	$4, %rdx
	orq	%rax, %rdx
	movq	%rdx, %rax
	andq	%r8, %rax
	shrq	$2, %rdx
	andq	%r8, %rdx
	leaq	(%rdx,%rax,4), %rax
	movq	%rax, %rcx
	andq	%rdi, %rcx
	shrq	%rax
	andq	%rdi, %rax
	leaq	(%rax,%rcx,2), %rdx
	movq	%r11, %r14
	movabsq	$1229782938247303441, %rcx
	andq	%rcx, %r14
	movq	%r11, %r15
	andq	%r9, %r15
	movq	%rdx, %rax
	andq	%rcx, %rax
	movq	%rdx, %r10
	movq	%rdx, %r8
	andq	%rsi, %rdx
	movq	%rax, %rcx
	imulq	%r14, %rcx
	movq	%rdx, %rdi
	imulq	%r15, %rdi
	xorq	%rcx, %rdi
	movq	%r11, %rbx
	andq	%r12, %rbx
	andq	%rsi, %r11
	andq	%r9, %r10
	andq	%r12, %r8
	movq	%r8, %rsi
	imulq	%rbx, %rsi
	movq	%r10, %rcx
	imulq	%r11, %rcx
	xorq	%rsi, %rcx
	xorq	%rdi, %rcx
	movq	%r10, %rdi
	imulq	%r14, %rdi
	movq	%rax, %rsi
	imulq	%r15, %rsi
	xorq	%rdi, %rsi
	movq	%rdx, %rdi
	imulq	%rbx, %rdi
	movq	%r8, %r12
	imulq	%r11, %r12
	xorq	%rdi, %r12
	xorq	%rsi, %r12
	movq	%r8, %rdi
	imulq	%r14, %rdi
	movq	%r10, %rsi
	imulq	%r15, %rsi
	xorq	%rdi, %rsi
	movq	%rax, %r9
	imulq	%rbx, %r9
	movq	%rdx, %rdi
	imulq	%r11, %rdi
	xorq	%r9, %rdi
	xorq	%rsi, %rdi
	imulq	%r14, %rdx
	imulq	%r15, %r8
	xorq	%rdx, %r8
	imulq	%rbx, %r10
	imulq	%r11, %rax
	xorq	%r10, %rax
	xorq	%r8, %rax
	movabsq	$1229782938247303441, %r8
	andq	%r8, %rcx
	movabsq	$2459565876494606882, %r11
	andq	%r11, %r12
	orq	%rcx, %r12
	movabsq	$4919131752989213764, %rbx
	andq	%rbx, %rdi
	orq	%r12, %rdi
	movabsq	$-8608480567731124088, %rdx
	andq	%rdx, %rax
	orq	%rdi, %rax
	bswapq	%rax
	movq	%rax, %rcx
	shrq	$4, %rcx
	movabsq	$1085102592571150095, %rdi
	andq	%rdi, %rcx
	andq	%rdi, %rax
	shlq	$4, %rax
	orq	%rcx, %rax
	movq	%rax, %rcx
	movabsq	$3689348814741910323, %rdi
	andq	%rdi, %rcx
	shrq	$2, %rax
	andq	%rdi, %rax
	leaq	(%rax,%rcx,4), %rax
	movq	%rax, %rcx
	movabsq	$6148914691236517205, %rdi
	andq	%rdi, %rcx
	shrq	%rax
	andq	%rdi, %rax
	leaq	(%rax,%rcx,2), %rax
	movq	%rax, 24(%rsp)
	movq	72(%rsp), %r14
	andq	%r8, %r14
	movq	64(%rsp), %r10
	andq	%r11, %r10
	movq	(%rsp), %r15
	andq	%r8, %r15
	movq	40(%rsp), %rdi
	andq	%rdx, %rdi
	movq	%r15, %rax
	imulq	%r14, %rax
	movq	%rdi, %rsi
	imulq	%r10, %rsi
	xorq	%rax, %rsi
	movq	%rbx, %r12
	movq	16(%rsp), %rax
	andq	%rbx, %rax
	movq	80(%rsp), %r8
	andq	%rdx, %r8
	movq	48(%rsp), %rcx
	andq	%r11, %rcx
	andq	%rbx, %rbp
	movq	%rbp, %rdx
	imulq	%rax, %rdx
	movq	%rax, %r11
	movq	%rcx, %rax
	imulq	%r8, %rax
	movq	%r8, %rbx
	xorq	%rdx, %rax
	xorq	%rsi, %rax
	movq	%rcx, %rsi
	movq	%rcx, %r9
	imulq	%r14, %rsi
	movq	%r15, %rdx
	imulq	%r10, %rdx
	xorq	%rsi, %rdx
	movq	%rdi, %rcx
	imulq	%r11, %rcx
	movq	%rbp, %rsi
	imulq	%r8, %rsi
	xorq	%rcx, %rsi
	xorq	%rdx, %rsi
	movq	%rbp, %rcx
	imulq	%r14, %rcx
	movq	%r9, %rdx
	imulq	%r10, %rdx
	xorq	%rcx, %rdx
	movq	%r15, %rcx
	imulq	%r11, %rcx
	movq	%rdi, %r8
	imulq	%rbx, %r8
	xorq	%rcx, %r8
	xorq	%rdx, %r8
	imulq	%r14, %rdi
	imulq	%r10, %rbp
	xorq	%rdi, %rbp
	imulq	%r11, %r9
	movq	%r15, %rcx
	imulq	%rbx, %rcx
	xorq	%r9, %rcx
	xorq	%rbp, %rcx
	movq	%rcx, (%rsp)
	movabsq	$1229782938247303441, %r15
	andq	%r15, %rax
	movabsq	$2459565876494606882, %r9
	andq	%r9, %rsi
	orq	%rax, %rsi
	andq	%r12, %r8
	orq	%rsi, %r8
	movq	%rcx, %rax
	movabsq	$-8608480567731124088, %rbx
	andq	%rbx, %rax
	orq	%r8, %rax
	movq	%rax, 16(%rsp)
	movq	56(%rsp), %rdx
	bswapq	%rdx
	movq	%rdx, %rax
	shrq	$4, %rax
	movabsq	$1085102592571150095, %rdi
	andq	%rdi, %rax
	andq	%rdi, %rdx
	shlq	$4, %rdx
	orq	%rax, %rdx
	movq	%rdx, %rax
	movabsq	$3689348814741910323, %rbp
	andq	%rbp, %rax
	shrq	$2, %rdx
	andq	%rbp, %rdx
	leaq	(%rdx,%rax,4), %rax
	movq	%rax, %rcx
	movabsq	$6148914691236517205, %rdx
	andq	%rdx, %rcx
	shrq	%rax
	andq	%rdx, %rax
	leaq	(%rax,%rcx,2), %rsi
	bswapq	%r13
	movq	%r13, %rax
	shrq	$4, %rax
	andq	%rdi, %rax
	andq	%rdi, %r13
	shlq	$4, %r13
	orq	%rax, %r13
	movq	%r13, %rax
	andq	%rbp, %rax
	shrq	$2, %r13
	andq	%rbp, %r13
	leaq	(,%rax,4), %rax
	addq	%r13, %rax
	movq	%rax, %rcx
	andq	%rdx, %rcx
	shrq	%rax
	andq	%rdx, %rax
	leaq	(%rax,%rcx,2), %rax
	movq	%rsi, %r8
	movq	%r15, %rdi
	andq	%r15, %r8
	movq	%rsi, %rdx
	movq	%r9, %r15
	andq	%r9, %rdx
	movq	%rax, %rcx
	andq	%rdi, %rcx
	movq	%rax, %r10
	movq	%rax, %r9
	andq	%rbx, %rax
	movq	%rcx, %r11
	imulq	%r8, %r11
	movq	%rax, %r14
	imulq	%rdx, %r14
	xorq	%r11, %r14
	movq	%rsi, %r11
	movabsq	$4919131752989213764, %rdi
	andq	%rdi, %r11
	andq	%rbx, %rsi
	andq	%r15, %r10
	andq	%rdi, %r9
	movq	%r9, %r15
	imulq	%r11, %r15
	movq	%r10, %rbx
	imulq	%rsi, %rbx
	xorq	%r15, %rbx
	xorq	%r14, %rbx
	movq	%r10, %r14
	imulq	%r8, %r14
	movq	%rcx, %r15
	imulq	%rdx, %r15
	xorq	%r14, %r15
	movq	%rax, %r14
	imulq	%r11, %r14
	movq	%r9, %r12
	imulq	%rsi, %r12
	xorq	%r14, %r12
	xorq	%r15, %r12
	movq	%r9, %r14
	imulq	%r8, %r14
	movq	%r10, %r15
	imulq	%rdx, %r15
	xorq	%r14, %r15
	movq	%rcx, %r14
	imulq	%r11, %r14
	movq	%rax, %r13
	imulq	%rsi, %r13
	xorq	%r14, %r13
	xorq	%r15, %r13
	imulq	%r8, %rax
	imulq	%rdx, %r9
	xorq	%rax, %r9
	imulq	%r11, %r10
	imulq	%rsi, %rcx
	xorq	%r10, %rcx
	xorq	%r9, %rcx
	movabsq	$1229782938247303441, %r9
	andq	%r9, %rbx
	movabsq	$2459565876494606882, %rdi
	andq	%rdi, %r12
	orq	%rbx, %r12
	movabsq	$4919131752989213764, %r11
	andq	%r11, %r13
	orq	%r12, %r13
	movabsq	$-8608480567731124088, %r14
	andq	%r14, %rcx
	orq	%r13, %rcx
	bswapq	%rcx
	movq	%rcx, %rax
	shrq	$4, %rax
	movabsq	$1085102592571150095, %rdx
	andq	%rdx, %rax
	andq	%rdx, %rcx
	shlq	$4, %rcx
	orq	%rax, %rcx
	movq	%rcx, %rax
	andq	%rbp, %rax
	shrq	$2, %rcx
	andq	%rbp, %rcx
	leaq	(%rcx,%rax,4), %r15
	movq	32(%rsp), %rsi
	movq	%rsi, %r8
	movq	%r9, %rax
	andq	%r9, %r8
	movq	%rsi, %r9
	andq	%rdi, %r9
	movq	%rdi, %rbx
	movq	8(%rsp), %rdx
	movq	%rdx, %rdi
	andq	%rax, %rdi
	movq	%rdx, %r10
	andq	%r14, %r10
	movq	%rdi, %rax
	imulq	%r8, %rax
	movq	%r10, %rcx
	imulq	%r9, %rcx
	xorq	%rax, %rcx
	movq	%rsi, %r12
	andq	%r11, %r12
	movq	%rsi, %rbp
	andq	%r14, %rbp
	movq	%rdx, %rax
	andq	%rbx, %rax
	movq	%rdx, %rbx
	andq	%r11, %rbx
	movq	%rbx, %rdx
	imulq	%r12, %rdx
	movq	%rax, %r11
	imulq	%rbp, %r11
	xorq	%rdx, %r11
	xorq	%rcx, %r11
	movq	%rax, %rcx
	imulq	%r8, %rcx
	movq	%rdi, %rdx
	imulq	%r9, %rdx
	xorq	%rcx, %rdx
	movq	%r10, %r14
	imulq	%r12, %r14
	movq	%rbx, %rcx
	imulq	%rbp, %rcx
	xorq	%r14, %rcx
	xorq	%rdx, %rcx
	movq	%rbx, %rdx
	imulq	%r8, %rdx
	movq	%rax, %r14
	imulq	%r9, %r14
	xorq	%rdx, %r14
	movq	%rdi, %r13
	imulq	%r12, %r13
	movq	%r10, %rdx
	imulq	%rbp, %rdx
	xorq	%r13, %rdx
	xorq	%r14, %rdx
	imulq	%r8, %r10
	imulq	%r9, %rbx
	xorq	%r10, %rbx
	imulq	%r12, %rax
	imulq	%rbp, %rdi
	xorq	%rax, %rdi
	xorq	%rbx, %rdi
	movabsq	$1229782938247303441, %rbx
	andq	%rbx, %r11
	movabsq	$2459565876494606882, %r13
	andq	%r13, %rcx
	orq	%r11, %rcx
	movabsq	$4919131752989213764, %r12
	andq	%r12, %rdx
	orq	%rcx, %rdx
	movabsq	$-8608480567731124088, %r14
	andq	%r14, %rdi
	orq	%rdx, %rdi
	movq	%rsi, %rcx
	bswapq	%rcx
	movq	%rcx, %rax
	shrq	$4, %rax
	movabsq	$1085102592571150095, %r8
	andq	%r8, %rax
	andq	%r8, %rcx
	shlq	$4, %rcx
	orq	%rax, %rcx
	movq	%rcx, %rax
	movabsq	$3689348814741910323, %rsi
	andq	%rsi, %rax
	shrq	$2, %rcx
	andq	%rsi, %rcx
	leaq	(%rcx,%rax,4), %rax
	movq	%rax, %rcx
	movabsq	$6148914691236517205, %r9
	andq	%r9, %rcx
	shrq	%rax
	andq	%r9, %rax
	movq	8(%rsp), %rdx
	bswapq	%rdx
	leaq	(%rax,%rcx,2), %r11
	movq	%rdx, %rax
	shrq	$4, %rax
	andq	%r8, %rax
	andq	%r8, %rdx
	shlq	$4, %rdx
	orq	%rax, %rdx
	movq	%rdx, %rax
	andq	%rsi, %rax
	shrq	$2, %rdx
	andq	%rsi, %rdx
	leaq	(%rdx,%rax,4), %rax
	movq	%rax, %rcx
	andq	%r9, %rcx
	shrq	%rax
	andq	%r9, %rax
	leaq	(%rax,%rcx,2), %r10
	movq	%r11, %rsi
	movq	%rbx, %rax
	andq	%rbx, %rsi
	movq	%r11, %rbx
	andq	%r13, %rbx
	movq	%r10, %r8
	andq	%rax, %r8
	movq	%r10, %rdx
	movq	%r10, %rcx
	movq	%r14, %rax
	andq	%r14, %r10
	movq	%r8, %r9
	imulq	%rsi, %r9
	movq	%r10, %r14
	imulq	%rbx, %r14
	xorq	%r9, %r14
	movq	%r11, %r9
	andq	%r12, %r9
	andq	%rax, %r11
	andq	%r13, %rdx
	andq	%r12, %rcx
	movq	%rcx, %r12
	imulq	%r9, %r12
	movq	%rdx, %rbp
	imulq	%r11, %rbp
	xorq	%r12, %rbp
	xorq	%r14, %rbp
	movq	%rdx, %r14
	imulq	%rsi, %r14
	movq	%r8, %r13
	imulq	%rbx, %r13
	xorq	%r14, %r13
	movq	%r10, %r14
	imulq	%r9, %r14
	movq	%rcx, %r12
	imulq	%r11, %r12
	xorq	%r14, %r12
	xorq	%r13, %r12
	movq	%rcx, %r14
	imulq	%rsi, %r14
	movq	%rdx, %r13
	imulq	%rbx, %r13
	xorq	%r14, %r13
	movq	%r8, %rax
	imulq	%r9, %rax
	movq	%r10, %r14
	imulq	%r11, %r14
	xorq	%rax, %r14
	xorq	%r13, %r14
	imulq	%rsi, %r10
	imulq	%rbx, %rcx
	xorq	%r10, %rcx
	imulq	%r9, %rdx
	imulq	%r11, %r8
	xorq	%rdx, %r8
	xorq	%rcx, %r8
	movabsq	$1229782938247303441, %rax
	andq	%rax, %rbp
	movabsq	$2459565876494606882, %rax
	andq	%rax, %r12
	orq	%rbp, %r12
	movabsq	$4919131752989213764, %rax
	andq	%rax, %r14
	orq	%r12, %r14
	movabsq	$-8608480567731124088, %rax
	andq	%rax, %r8
	orq	%r14, %r8
	bswapq	%r8
	movq	%r8, %rax
	shrq	$4, %rax
	movabsq	$1085102592571150095, %rcx
	andq	%rcx, %rax
	andq	%rcx, %r8
	shlq	$4, %r8
	orq	%rax, %r8
	movq	%r8, %rax
	movabsq	$3689348814741910323, %rcx
	andq	%rcx, %rax
	shrq	$2, %r8
	andq	%rcx, %r8
	movq	%r15, %r9
	movabsq	$6148914691236517205, %rcx
	andq	%rcx, %r9
	shrq	%r15
	andq	%rcx, %r15
	leaq	(%r8,%rax,4), %rax
	andq	%rax, %rcx
	movq	%rcx, %rdx
	shrq	%rax
	movabsq	$6148914691236517204, %rcx
	andq	%rax, %rcx
	leaq	(%rcx,%rdx,2), %rax
	leaq	(%r15,%r9,2), %rcx
	movq	24(%rsp), %rdx
	xorq	%rcx, %rdx
	xorq	%rdx, %rax
	shrq	%rax
	andq	$-2, %rcx
	movq	(%rsp), %r11
	shrq	$63, %r11
	orq	%rcx, %r11
	xorq	%rax, %r11
	movq	%rdx, %rax
	shrq	%rax
	movq	%rdx, %rcx
	shrq	$62, %rcx
	shrq	$61, %rdx
	xorq	%rcx, %rdx
	xorq	%rax, %rdx
	leaq	(%rdx,%rdx), %rax
	leaq	(,%rdx,8), %rcx
	xorq	%rax, %rcx
	movq	16(%rsp), %r10
	movq	%r10, %rax
	xorq	%rdx, %rax
	shlq	$4, %rdx
	movq	88(%rsp), %rsi
	xorq	%rsi, %rdx
	xorq	%rcx, %rdx
	addq	%r9, %r9
	xorq	%rax, %rdx
	movq	%rdx, %rax
	shrq	$63, %r9
	movq	%r11, %r8
	shrq	$60, %r8
	xorq	%r11, %r8
	movq	%r11, %rcx
	shrq	$61, %rcx
	xorq	%r9, %rcx
	xorq	%rcx, %r8
	leaq	(,%r8,8), %rcx
	xorq	%rdi, %rcx
	movq	%r10, %rdi
	xorq	%r8, %rdi
	shlq	$4, %r8
	xorq	%rcx, %r8
	leaq	(%rdi,%rdi), %rdx
	xorq	%rsi, %rdx
	xorq	%r8, %rdx
	xorq	%rdi, %rdx
	addq	$96, %rsp
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
.Lfunc_end26:
	.size	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul, .Lfunc_end26-_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	.cfi_endproc

	.section	.text._RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW7sq_iter,"ax",@progbits
	.p2align	4
	.type	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW7sq_iter,@function
_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW7sq_iter:
.Lfunc_begin27:
	.cfi_startproc
	movq	%rdx, %rcx
	movq	%rsi, %rax
	testq	%rdi, %rdi
	je	.LBB27_4
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rdi, %rbx
	.p2align	4
.LBB27_2:
	movq	%rax, %rdi
	movq	%rcx, %rsi
	movq	%rax, %rdx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	movq	%rdx, %rcx
	decq	%rbx
	jne	.LBB27_2
	popq	%rbx
	.cfi_def_cfa_offset 8
	.cfi_restore %rbx
.LBB27_4:
	movq	%rcx, %rdx
	retq
.Lfunc_end27:
	.size	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW7sq_iter, .Lfunc_end27-_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW7sq_iter
	.cfi_endproc

	.section	.text._RNvMNtCsemcRClSg8DH_9native_vm5inputNtB2_7Decoded11phase_count,"ax",@progbits
	.p2align	4
	.type	_RNvMNtCsemcRClSg8DH_9native_vm5inputNtB2_7Decoded11phase_count,@function
_RNvMNtCsemcRClSg8DH_9native_vm5inputNtB2_7Decoded11phase_count:
.Lfunc_begin28:
	.cfi_startproc
	movq	16(%rdi), %rax
	shrq	$3, %rax
	orq	$1, %rax
	cmpq	8(%rdi), %rax
	jae	.LBB28_1
	movq	(%rdi), %rcx
	movq	(%rcx,%rax,8), %rax
	retq
.LBB28_1:
	xorl	%eax, %eax
	retq
.Lfunc_end28:
	.size	_RNvMNtCsemcRClSg8DH_9native_vm5inputNtB2_7Decoded11phase_count, .Lfunc_end28-_RNvMNtCsemcRClSg8DH_9native_vm5inputNtB2_7Decoded11phase_count
	.cfi_endproc

	.section	.text._RNvMNtCsemcRClSg8DH_9native_vm5inputNtB2_7Decoded14stream_element,"ax",@progbits
	.p2align	4
	.type	_RNvMNtCsemcRClSg8DH_9native_vm5inputNtB2_7Decoded14stream_element,@function
_RNvMNtCsemcRClSg8DH_9native_vm5inputNtB2_7Decoded14stream_element:
.Lfunc_begin29:
	.cfi_startproc
	testq	%rdx, %rdx
	je	.LBB29_4
	cmpq	(%rsi), %rcx
	jae	.LBB29_4
	addq	%rcx, %rcx
	movq	%rcx, %rax
	subq	$-3, %rax
	setae	%r8b
	cmpq	%rdx, %rax
	seta	%al
	orb	%r8b, %al
	je	.LBB29_6
.LBB29_4:
	xorl	%eax, %eax
	movq	%rax, (%rdi)
	retq
.LBB29_6:
	movq	8(%rsi,%rcx,8), %rax
	movq	16(%rsi,%rcx,8), %rcx
	movq	%rax, 8(%rdi)
	movq	%rcx, 16(%rdi)
	movl	$1, %eax
	movq	%rax, (%rdi)
	retq
.Lfunc_end29:
	.size	_RNvMNtCsemcRClSg8DH_9native_vm5inputNtB2_7Decoded14stream_element, .Lfunc_end29-_RNvMNtCsemcRClSg8DH_9native_vm5inputNtB2_7Decoded14stream_element
	.cfi_endproc

	.section	.text._RNvMNtCsemcRClSg8DH_9native_vm5inputNtB2_7Decoded5phase,"ax",@progbits
	.p2align	4
	.type	_RNvMNtCsemcRClSg8DH_9native_vm5inputNtB2_7Decoded5phase,@function
_RNvMNtCsemcRClSg8DH_9native_vm5inputNtB2_7Decoded5phase:
.Lfunc_begin30:
	.cfi_startproc
	pushq	%r14
	.cfi_def_cfa_offset 16
	pushq	%rbx
	.cfi_def_cfa_offset 24
	pushq	%rax
	.cfi_def_cfa_offset 32
	.cfi_offset %rbx, -24
	.cfi_offset %r14, -16
	movq	%rsi, %r14
	movq	%rdi, %rbx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5inputNtB2_7Decoded11phase_count
	movq	%rax, %rcx
	xorl	%eax, %eax
	cmpq	$7, %r14
	ja	.LBB30_5
	cmpq	%rcx, %r14
	jae	.LBB30_5
	movq	16(%rbx), %rax
	shrq	$3, %rax
	orq	$1, %rax
	imulq	$49411, %r14, %rcx
	leaq	(%rcx,%rax), %rdx
	addq	$49412, %rdx
	cmpq	8(%rbx), %rdx
	jbe	.LBB30_4
	xorl	%eax, %eax
.LBB30_5:
	addq	$8, %rsp
	.cfi_def_cfa_offset 24
	popq	%rbx
	.cfi_def_cfa_offset 16
	popq	%r14
	.cfi_def_cfa_offset 8
	retq
.LBB30_4:
	.cfi_def_cfa_offset 32
	addq	%rcx, %rax
	incq	%rax
	shlq	$3, %rax
	addq	(%rbx), %rax
	addq	$8, %rsp
	.cfi_def_cfa_offset 24
	popq	%rbx
	.cfi_def_cfa_offset 16
	popq	%r14
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end30:
	.size	_RNvMNtCsemcRClSg8DH_9native_vm5inputNtB2_7Decoded5phase, .Lfunc_end30-_RNvMNtCsemcRClSg8DH_9native_vm5inputNtB2_7Decoded5phase
	.cfi_endproc

	.section	.text._RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState11next_scalar,"ax",@progbits
	.p2align	4
	.type	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState11next_scalar,@function
_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState11next_scalar:
.Lfunc_begin31:
	.cfi_startproc
	pushq	%r15
	.cfi_def_cfa_offset 16
	pushq	%r14
	.cfi_def_cfa_offset 24
	pushq	%rbx
	.cfi_def_cfa_offset 32
	subq	$32, %rsp
	.cfi_def_cfa_offset 64
	.cfi_offset %rbx, -32
	.cfi_offset %r14, -24
	.cfi_offset %r15, -16
	movq	%rdi, %rbx
	cmpb	$0, 304(%rsi)
	jne	.LBB31_3
	movq	352(%rsi), %r14
	movq	328(%rsi), %rax
	movq	%rsi, %r15
	movq	336(%rsi), %rdx
	leaq	8(%rsp), %rdi
	movq	%rax, %rsi
	movq	%r14, %rcx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5inputNtB2_7Decoded14stream_element
	cmpl	$1, 8(%rsp)
	jne	.LBB31_3
	movq	16(%rsp), %rax
	movq	24(%rsp), %rcx
	incq	%r14
	movq	%r14, 352(%r15)
	movq	%rax, 8(%rbx)
	movq	%rcx, 16(%rbx)
	movl	$1, %eax
	jmp	.LBB31_4
.LBB31_3:
	xorl	%eax, %eax
.LBB31_4:
	movq	%rax, (%rbx)
	addq	$32, %rsp
	.cfi_def_cfa_offset 32
	popq	%rbx
	.cfi_def_cfa_offset 24
	popq	%r14
	.cfi_def_cfa_offset 16
	popq	%r15
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end31:
	.size	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState11next_scalar, .Lfunc_end31-_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState11next_scalar
	.cfi_endproc

	.section	.text._RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState11read_scalar,"ax",@progbits
	.p2align	4
	.type	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState11read_scalar,@function
_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState11read_scalar:
.Lfunc_begin32:
	.cfi_startproc
	pushq	%r15
	.cfi_def_cfa_offset 16
	pushq	%r14
	.cfi_def_cfa_offset 24
	pushq	%r13
	.cfi_def_cfa_offset 32
	pushq	%r12
	.cfi_def_cfa_offset 40
	pushq	%rbx
	.cfi_def_cfa_offset 48
	subq	$32, %rsp
	.cfi_def_cfa_offset 80
	.cfi_offset %rbx, -48
	.cfi_offset %r12, -40
	.cfi_offset %r13, -32
	.cfi_offset %r14, -24
	.cfi_offset %r15, -16
	movq	%rsi, %r14
	movq	%rdi, %rbx
	leaq	8(%rsp), %rdi
	callq	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState11next_scalar
	cmpl	$1, 8(%rsp)
	jne	.LBB32_2
	movq	16(%rsp), %r15
	movq	24(%rsp), %r12
	movl	$1, %r13d
	movl	$1, %ecx
	movq	%r14, %rdi
	movq	%r15, %rsi
	movq	%r12, %rdx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW6absorb
	movq	%r15, 8(%rbx)
	movq	%r12, 16(%rbx)
	jmp	.LBB32_3
.LBB32_2:
	xorl	%r13d, %r13d
.LBB32_3:
	movq	%r13, (%rbx)
	addq	$32, %rsp
	.cfi_def_cfa_offset 48
	popq	%rbx
	.cfi_def_cfa_offset 40
	popq	%r12
	.cfi_def_cfa_offset 32
	popq	%r13
	.cfi_def_cfa_offset 24
	popq	%r14
	.cfi_def_cfa_offset 16
	popq	%r15
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end32:
	.size	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState11read_scalar, .Lfunc_end32-_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState11read_scalar
	.cfi_endproc

	.section	.text._RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState12read_scalars,"ax",@progbits
	.p2align	4
	.type	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState12read_scalars,@function
_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState12read_scalars:
.Lfunc_begin33:
	.cfi_startproc
	pushq	%r15
	.cfi_def_cfa_offset 16
	pushq	%r14
	.cfi_def_cfa_offset 24
	pushq	%r13
	.cfi_def_cfa_offset 32
	pushq	%r12
	.cfi_def_cfa_offset 40
	pushq	%rbx
	.cfi_def_cfa_offset 48
	subq	$32, %rsp
	.cfi_def_cfa_offset 80
	.cfi_offset %rbx, -48
	.cfi_offset %r12, -40
	.cfi_offset %r13, -32
	.cfi_offset %r14, -24
	.cfi_offset %r15, -16
	movb	$1, %bl
	testq	%rdx, %rdx
	je	.LBB33_5
	movq	%rdx, %r14
	movq	%rsi, %r15
	movq	%rdi, %r12
	shlq	$4, %r14
	addq	%rsi, %r14
	leaq	8(%rsp), %r13
	.p2align	4
.LBB33_2:
	movq	%r13, %rdi
	movq	%r12, %rsi
	callq	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState11read_scalar
	cmpl	$1, 8(%rsp)
	jne	.LBB33_4
	movq	16(%rsp), %rax
	movq	24(%rsp), %rcx
	movq	%rax, (%r15)
	movq	%rcx, 8(%r15)
	addq	$16, %r15
	cmpq	%r14, %r15
	jne	.LBB33_2
	jmp	.LBB33_5
.LBB33_4:
	xorl	%ebx, %ebx
.LBB33_5:
	movl	%ebx, %eax
	addq	$32, %rsp
	.cfi_def_cfa_offset 48
	popq	%rbx
	.cfi_def_cfa_offset 40
	popq	%r12
	.cfi_def_cfa_offset 32
	popq	%r13
	.cfi_def_cfa_offset 24
	popq	%r14
	.cfi_def_cfa_offset 16
	popq	%r15
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end33:
	.size	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState12read_scalars, .Lfunc_end33-_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState12read_scalars
	.cfi_endproc

	.section	.text._RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState14query_openings,"ax",@progbits
	.p2align	4
	.type	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState14query_openings,@function
_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState14query_openings:
.Lfunc_begin34:
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
	subq	$40, %rsp
	.cfi_def_cfa_offset 96
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	%rcx, %r13
	movq	%rdi, %r14
	movq	752(%rsi), %rax
	cmpq	$9, %rax
	setae	%cl
	cmpq	%rax, %rdx
	setae	%al
	orb	%cl, %al
	jne	.LBB34_4
	movq	%r8, %r12
	movq	%rdx, %rbp
	movq	%rsi, %rbx
	leaq	328(%rsi), %rdi
	movq	360(%rsi), %r15
	movq	%r15, %rsi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5inputNtB2_7Decoded5phase
	testq	%rax, %rax
	je	.LBB34_4
	leaq	(,%rbp,2), %rcx
	addq	%rbp, %rcx
	shlq	$4, %rcx
	leaq	(%rbx,%rcx), %rsi
	addq	$368, %rsi
	movq	400(%rbx,%rcx), %rdx
	movq	408(%rbx,%rcx), %rcx
	movq	%rax, (%rsp)
	leaq	8(%rsp), %rdi
	movq	%r13, %r8
	movq	%r12, %r9
	callq	_RNvNtCsemcRClSg8DH_9native_vm10transcript10open_phase
	cmpq	$0, 8(%rsp)
	je	.LBB34_4
	movq	32(%rsp), %rax
	movq	%rax, 24(%r14)
	movq	24(%rsp), %rax
	movq	%rax, 16(%r14)
	movq	8(%rsp), %rax
	movq	16(%rsp), %rcx
	movq	%rcx, 8(%r14)
	movq	%rax, (%r14)
	incq	%r15
	movq	%r15, 360(%rbx)
	jmp	.LBB34_5
.LBB34_4:
	movq	$0, (%r14)
.LBB34_5:
	addq	$40, %rsp
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
.Lfunc_end34:
	.size	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState14query_openings, .Lfunc_end34-_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState14query_openings
	.cfi_endproc

	.section	.text._RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState15read_commitment,"ax",@progbits
	.p2align	4
	.type	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState15read_commitment,@function
_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState15read_commitment:
.Lfunc_begin35:
	.cfi_startproc
	pushq	%r15
	.cfi_def_cfa_offset 16
	pushq	%r14
	.cfi_def_cfa_offset 24
	pushq	%r13
	.cfi_def_cfa_offset 32
	pushq	%r12
	.cfi_def_cfa_offset 40
	pushq	%rbx
	.cfi_def_cfa_offset 48
	subq	$32, %rsp
	.cfi_def_cfa_offset 80
	.cfi_offset %rbx, -48
	.cfi_offset %r12, -40
	.cfi_offset %r13, -32
	.cfi_offset %r14, -24
	.cfi_offset %r15, -16
	movq	%rdx, %rbx
	movq	%rsi, %r15
	movq	%rdi, %r14
	leaq	8(%rsp), %rdi
	movq	%r14, %rsi
	callq	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState11read_scalar
	cmpl	$1, 8(%rsp)
	jne	.LBB35_5
	movq	16(%rsp), %r12
	movq	24(%rsp), %r13
	leaq	8(%rsp), %rdi
	movq	%r14, %rsi
	callq	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState11read_scalar
	cmpb	$0, 8(%rsp)
	je	.LBB35_5
	movq	752(%r14), %rax
	cmpq	$8, %rax
	jae	.LBB35_5
	movq	16(%rsp), %rcx
	movq	24(%rsp), %rdx
	leaq	(%rax,%rax,2), %rax
	shlq	$4, %rax
	movq	%r12, 368(%r14,%rax)
	movq	%r13, 376(%r14,%rax)
	movq	%rcx, 384(%r14,%rax)
	movq	%rdx, 392(%r14,%rax)
	movq	%r15, 400(%r14,%rax)
	movq	%rbx, 408(%r14,%rax)
	incq	752(%r14)
	movb	$1, %al
	jmp	.LBB35_6
.LBB35_5:
	xorl	%eax, %eax
.LBB35_6:
	addq	$32, %rsp
	.cfi_def_cfa_offset 48
	popq	%rbx
	.cfi_def_cfa_offset 40
	popq	%r12
	.cfi_def_cfa_offset 32
	popq	%r13
	.cfi_def_cfa_offset 24
	popq	%r14
	.cfi_def_cfa_offset 16
	popq	%r15
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end35:
	.size	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState15read_commitment, .Lfunc_end35-_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState15read_commitment
	.cfi_endproc

	.section	.text._RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState17sample_challenges,"ax",@progbits
	.p2align	4
	.type	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState17sample_challenges,@function
_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState17sample_challenges:
.Lfunc_begin36:
	.cfi_startproc
	testq	%rdx, %rdx
	je	.LBB36_4
	pushq	%r15
	.cfi_def_cfa_offset 16
	pushq	%r14
	.cfi_def_cfa_offset 24
	pushq	%rbx
	.cfi_def_cfa_offset 32
	.cfi_offset %rbx, -32
	.cfi_offset %r14, -24
	.cfi_offset %r15, -16
	movq	%rdx, %rbx
	movq	%rsi, %r14
	movq	%rdi, %r15
	shlq	$4, %rbx
	addq	%rsi, %rbx
	.p2align	4
.LBB36_2:
	movq	%r15, %rdi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW7squeeze
	movq	%rax, (%r14)
	movq	%rdx, 8(%r14)
	addq	$16, %r14
	cmpq	%rbx, %r14
	jne	.LBB36_2
	popq	%rbx
	.cfi_def_cfa_offset 24
	popq	%r14
	.cfi_def_cfa_offset 16
	popq	%r15
	.cfi_def_cfa_offset 8
	.cfi_restore %rbx
	.cfi_restore %r14
	.cfi_restore %r15
.LBB36_4:
	retq
.Lfunc_end36:
	.size	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState17sample_challenges, .Lfunc_end36-_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState17sample_challenges
	.cfi_endproc

	.section	.text._RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState19sumcheck_round_poly,"ax",@progbits
	.p2align	4
	.type	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState19sumcheck_round_poly,@function
_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState19sumcheck_round_poly:
.Lfunc_begin37:
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
	movq	%r9, %rbx
	movq	%rcx, %r14
	movq	%rsi, %r13
	movq	%rdi, %r12
	cmpb	$0, (%r8)
	je	.LBB37_4
	movq	%r14, 8(%rsp)
	movq	%rdx, (%rsp)
	movq	8(%r8), %rax
	movq	%rax, 24(%rsp)
	movq	16(%r8), %r15
	decq	%r13
	leaq	16(%rbx), %r14
	movq	%r12, %rdi
	movq	%r14, %rsi
	movq	%r13, %rdx
	callq	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState12read_scalars
	xorl	%ebp, %ebp
	testb	%al, %al
	je	.LBB37_9
	movq	%r14, %rdi
	movq	%r13, %rsi
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field5sum_e
	movq	%rax, %r14
	movq	%rdx, 16(%rsp)
	movq	%r13, %rdi
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field10bit_length
	subl	$3, %eax
	cmovbl	%ebp, %eax
	movq	%r12, %rdi
	movl	%eax, %esi
	callq	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState5grind
	testb	%al, %al
	je	.LBB37_9
	movq	24(%rsp), %rdi
	movq	%r15, %rsi
	movq	%r14, %rdx
	movq	16(%rsp), %rcx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	xorq	8(%rsp), %rdx
	xorq	(%rsp), %rax
	movq	%rax, (%rbx)
	movq	%rdx, 8(%rbx)
	movb	$1, %bpl
	jmp	.LBB37_9
.LBB37_4:
	movq	%rdx, %r15
	leaq	32(%rsp), %rdi
	movq	%r12, %rsi
	callq	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState11read_scalar
	cmpl	$1, 32(%rsp)
	jne	.LBB37_8
	movq	%r14, 8(%rsp)
	movq	40(%rsp), %rax
	movq	48(%rsp), %rcx
	movq	%rax, (%rbx)
	movq	%rcx, 8(%rbx)
	addq	$-2, %r13
	leaq	32(%rbx), %r14
	movq	%r12, %rdi
	movq	%r14, %rsi
	movq	%r13, %rdx
	callq	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState12read_scalars
	xorl	%ebp, %ebp
	testb	%al, %al
	je	.LBB37_9
	movq	%r15, (%rsp)
	movq	%r14, %rdi
	movq	%r13, %rsi
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field5sum_e
	movq	%rax, %r15
	movq	%rdx, %r14
	movq	%r13, %rdi
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field10bit_length
	subl	$3, %eax
	cmovbl	%ebp, %eax
	movq	%r12, %rdi
	movl	%eax, %esi
	callq	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState5grind
	testb	%al, %al
	je	.LBB37_9
	xorq	8(%rsp), %r14
	xorq	(%rsp), %r15
	movq	%r15, 16(%rbx)
	movq	%r14, 24(%rbx)
	movb	$1, %bpl
	jmp	.LBB37_9
.LBB37_8:
	xorl	%ebp, %ebp
.LBB37_9:
	movl	%ebp, %eax
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
.Lfunc_end37:
	.size	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState19sumcheck_round_poly, .Lfunc_end37-_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState19sumcheck_round_poly
	.cfi_endproc

	.section	.text._RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState5grind,"ax",@progbits
	.p2align	4
	.type	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState5grind,@function
_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState5grind:
.Lfunc_begin38:
	.cfi_startproc
	testl	%esi, %esi
	je	.LBB38_3
	pushq	%r14
	.cfi_def_cfa_offset 16
	pushq	%rbx
	.cfi_def_cfa_offset 24
	subq	$24, %rsp
	.cfi_def_cfa_offset 48
	.cfi_offset %rbx, -24
	.cfi_offset %r14, -16
	movl	%esi, %ebx
	movq	%rdi, %r14
	movq	%rsp, %rdi
	movq	%r14, %rsi
	callq	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState11next_scalar
	cmpb	$0, (%rsp)
	je	.LBB38_4
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rdx
	movq	%r14, %rdi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW12absorb_nonce
	movq	$-1, %rdx
	movl	%ebx, %ecx
	shlq	%cl, %rdx
	notq	%rdx
	testq	%rdx, %rax
	sete	%al
	addq	$24, %rsp
	.cfi_def_cfa_offset 24
	popq	%rbx
	.cfi_def_cfa_offset 16
	popq	%r14
	.cfi_def_cfa_offset 8
	.cfi_restore %rbx
	.cfi_restore %r14
	retq
.LBB38_3:
	movb	$1, %al
	retq
.LBB38_4:
	.cfi_def_cfa_offset 48
	.cfi_offset %rbx, -24
	.cfi_offset %r14, -16
	xorl	%eax, %eax
	addq	$24, %rsp
	.cfi_def_cfa_offset 24
	popq	%rbx
	.cfi_def_cfa_offset 16
	popq	%r14
	.cfi_def_cfa_offset 8
	.cfi_restore %rbx
	.cfi_restore %r14
	retq
.Lfunc_end38:
	.size	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState5grind, .Lfunc_end38-_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState5grind
	.cfi_endproc

	.section	.text._RNvMs0_NtCsemcRClSg8DH_9native_vm6layoutNtB5_7FormBuf10add_scaled,"ax",@progbits
	.p2align	4
	.type	_RNvMs0_NtCsemcRClSg8DH_9native_vm6layoutNtB5_7FormBuf10add_scaled,@function
_RNvMs0_NtCsemcRClSg8DH_9native_vm6layoutNtB5_7FormBuf10add_scaled:
.Lfunc_begin39:
	.cfi_startproc
	testq	%rdx, %rdx
	je	.LBB39_1
	pushq	%r15
	.cfi_def_cfa_offset 16
	pushq	%r14
	.cfi_def_cfa_offset 24
	pushq	%r13
	.cfi_def_cfa_offset 32
	pushq	%r12
	.cfi_def_cfa_offset 40
	pushq	%rbx
	.cfi_def_cfa_offset 48
	.cfi_offset %rbx, -48
	.cfi_offset %r12, -40
	.cfi_offset %r13, -32
	.cfi_offset %r14, -24
	.cfi_offset %r15, -16
	movq	%r8, %rbx
	movq	%rcx, %r14
	movq	%rsi, %r15
	movq	%rdi, %r12
	shlq	$3, %rdx
	leaq	(%rdx,%rdx,4), %r13
	addq	$-40, %r13
	.p2align	4
.LBB39_4:
	movq	24(%r15), %rdx
	movq	32(%r15), %rcx
	movq	%r14, %rdi
	movq	%rbx, %rsi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	movq	%rdx, %rcx
	movq	%r12, %rdi
	movq	%r15, %rsi
	movq	%rax, %rdx
	callq	_RNvMs0_NtCsemcRClSg8DH_9native_vm6layoutNtB5_7FormBuf8add_term
	testb	%al, %al
	je	.LBB39_6
	addq	$40, %r15
	testq	%r13, %r13
	leaq	-40(%r13), %r13
	jne	.LBB39_4
.LBB39_6:
	popq	%rbx
	.cfi_def_cfa_offset 40
	popq	%r12
	.cfi_def_cfa_offset 32
	popq	%r13
	.cfi_def_cfa_offset 24
	popq	%r14
	.cfi_def_cfa_offset 16
	popq	%r15
	.cfi_def_cfa_offset 8
	.cfi_restore %rbx
	.cfi_restore %r12
	.cfi_restore %r13
	.cfi_restore %r14
	.cfi_restore %r15
	retq
.LBB39_1:
	movb	$1, %al
	retq
.Lfunc_end39:
	.size	_RNvMs0_NtCsemcRClSg8DH_9native_vm6layoutNtB5_7FormBuf10add_scaled, .Lfunc_end39-_RNvMs0_NtCsemcRClSg8DH_9native_vm6layoutNtB5_7FormBuf10add_scaled
	.cfi_endproc

	.section	.text._RNvMs0_NtCsemcRClSg8DH_9native_vm6layoutNtB5_7FormBuf8add_term,"ax",@progbits
	.p2align	4
	.type	_RNvMs0_NtCsemcRClSg8DH_9native_vm6layoutNtB5_7FormBuf8add_term,@function
_RNvMs0_NtCsemcRClSg8DH_9native_vm6layoutNtB5_7FormBuf8add_term:
.Lfunc_begin40:
	.cfi_startproc
	movq	(%rdi), %rax
	cmpq	$148, %rax
	ja	.LBB40_1
	pushq	%r15
	.cfi_def_cfa_offset 16
	pushq	%r14
	.cfi_def_cfa_offset 24
	pushq	%r13
	.cfi_def_cfa_offset 32
	pushq	%r12
	.cfi_def_cfa_offset 40
	pushq	%rbx
	.cfi_def_cfa_offset 48
	.cfi_offset %rbx, -48
	.cfi_offset %r12, -40
	.cfi_offset %r13, -32
	.cfi_offset %r14, -24
	.cfi_offset %r15, -16
	leaq	(%rax,%rax,4), %r8
	leaq	(%rdi,%r8,8), %r8
	addq	$8, %r8
	movq	(%rsi), %r9
	testq	%rax, %rax
	je	.LBB40_12
	leaq	8(%rdi), %r10
	leaq	8(%rsi), %r11
	xorl	%ebx, %ebx
	cmpq	$3, %r9
	movl	$8, %r14d
	cmovaeq	%r14, %r11
	cmovbq	%r9, %rbx
	jmp	.LBB40_5
	.p2align	4
.LBB40_9:
	addq	$40, %r10
	cmpq	%r8, %r10
	je	.LBB40_10
.LBB40_5:
	cmpq	%r9, (%r10)
	jne	.LBB40_9
	leaq	8(%r10), %r15
	cmpq	$3, %r9
	cmovaeq	%r14, %r15
	xorl	%r12d, %r12d
	.p2align	4
.LBB40_7:
	cmpq	%r12, %rbx
	je	.LBB40_13
	movq	(%r15,%r12,8), %r13
	cmpq	(%r11,%r12,8), %r13
	leaq	1(%r12), %r12
	je	.LBB40_7
	jmp	.LBB40_9
.LBB40_1:
	.cfi_def_cfa_offset 8
	.cfi_restore %rbx
	.cfi_restore %r12
	.cfi_restore %r13
	.cfi_restore %r14
	.cfi_restore %r15
	xorl	%eax, %eax
	retq
.LBB40_13:
	.cfi_def_cfa_offset 48
	.cfi_offset %rbx, -48
	.cfi_offset %r12, -40
	.cfi_offset %r13, -32
	.cfi_offset %r14, -24
	.cfi_offset %r15, -16
	xorq	%rdx, 24(%r10)
	xorq	%rcx, 32(%r10)
	jmp	.LBB40_14
.LBB40_10:
	cmpq	$148, %rax
	jne	.LBB40_12
	xorl	%eax, %eax
	jmp	.LBB40_15
.LBB40_12:
	movq	%r9, (%r8)
	movq	8(%rsi), %r9
	movq	16(%rsi), %rsi
	movq	%r9, 8(%r8)
	movq	%rsi, 16(%r8)
	movq	%rdx, 24(%r8)
	movq	%rcx, 32(%r8)
	incq	%rax
	movq	%rax, (%rdi)
.LBB40_14:
	movb	$1, %al
.LBB40_15:
	popq	%rbx
	.cfi_def_cfa_offset 40
	popq	%r12
	.cfi_def_cfa_offset 32
	popq	%r13
	.cfi_def_cfa_offset 24
	popq	%r14
	.cfi_def_cfa_offset 16
	popq	%r15
	.cfi_def_cfa_offset 8
	.cfi_restore %rbx
	.cfi_restore %r12
	.cfi_restore %r13
	.cfi_restore %r14
	.cfi_restore %r15
	retq
.Lfunc_end40:
	.size	_RNvMs0_NtCsemcRClSg8DH_9native_vm6layoutNtB5_7FormBuf8add_term, .Lfunc_end40-_RNvMs0_NtCsemcRClSg8DH_9native_vm6layoutNtB5_7FormBuf8add_term
	.cfi_endproc

	.section	.text._RNvMs2_NtCsemcRClSg8DH_9native_vm6layoutNtB5_7LayoutW9placement,"ax",@progbits
	.p2align	4
	.type	_RNvMs2_NtCsemcRClSg8DH_9native_vm6layoutNtB5_7LayoutW9placement,@function
_RNvMs2_NtCsemcRClSg8DH_9native_vm6layoutNtB5_7LayoutW9placement:
.Lfunc_begin41:
	.cfi_startproc
	leaq	(%rsi,%rsi,2), %rax
	cmpq	$0, 120(%rdi,%rax,8)
	je	.LBB41_1
	leaq	(%rdi,%rax,8), %rcx
	addq	$120, %rcx
	movq	8(%rcx), %rax
	movq	16(%rcx), %rdx
	retq
.LBB41_1:
	xorl	%edx, %edx
	xorl	%eax, %eax
	retq
.Lfunc_end41:
	.size	_RNvMs2_NtCsemcRClSg8DH_9native_vm6layoutNtB5_7LayoutW9placement, .Lfunc_end41-_RNvMs2_NtCsemcRClSg8DH_9native_vm6layoutNtB5_7LayoutW9placement
	.cfi_endproc

	.section	.text._RNvMs_NtCsemcRClSg8DH_9native_vm10transcriptNtB4_4Rows3row,"ax",@progbits
	.p2align	4
	.type	_RNvMs_NtCsemcRClSg8DH_9native_vm10transcriptNtB4_4Rows3row,@function
_RNvMs_NtCsemcRClSg8DH_9native_vm10transcriptNtB4_4Rows3row:
.Lfunc_begin42:
	.cfi_startproc
	imulq	$193, %rsi, %rax
	leaq	1(%rax), %rcx
	movq	24(%rdi), %rsi
	addq	%rsi, %rcx
	setb	%dl
	cmpq	8(%rdi), %rcx
	seta	%cl
	orb	%dl, %cl
	leaq	8(,%rax,8), %r8
	addq	(%rdi), %r8
	xorl	%edx, %edx
	testb	%cl, %cl
	cmoveq	%rsi, %rdx
	movl	$8, %eax
	cmoveq	%r8, %rax
	retq
.Lfunc_end42:
	.size	_RNvMs_NtCsemcRClSg8DH_9native_vm10transcriptNtB4_4Rows3row, .Lfunc_end42-_RNvMs_NtCsemcRClSg8DH_9native_vm10transcriptNtB4_4Rows3row
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr11first_claim,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr11first_claim,@function
_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr11first_claim:
.Lfunc_begin43:
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
	subq	$1320, %rsp
	.cfi_def_cfa_offset 1376
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	%r9, %r13
	movq	%rcx, %r14
	movq	%rdx, %r15
	movq	%rsi, %r12
	movq	%rdi, %rbx
	movq	$0, 320(%rsp)
	movq	$0, 328(%rsp)
	movq	$0, 336(%rsp)
	movq	$0, 344(%rsp)
	movq	$0, 352(%rsp)
	movq	$0, 360(%rsp)
	movq	$0, 368(%rsp)
	movq	$0, 376(%rsp)
	movq	$0, 384(%rsp)
	movq	$0, 392(%rsp)
	movq	$0, 400(%rsp)
	movq	$0, 408(%rsp)
	movq	$0, 416(%rsp)
	movq	$0, 424(%rsp)
	movq	$0, 432(%rsp)
	movq	$0, 440(%rsp)
	movq	$0, 448(%rsp)
	movq	$0, 456(%rsp)
	movq	$0, 464(%rsp)
	movq	$0, 472(%rsp)
	movq	$0, 480(%rsp)
	movq	$0, 488(%rsp)
	movq	$0, 496(%rsp)
	movq	$0, 504(%rsp)
	movq	$0, 512(%rsp)
	movq	$0, 520(%rsp)
	movq	$0, 528(%rsp)
	movq	$0, 536(%rsp)
	movq	$0, 544(%rsp)
	movq	$0, 552(%rsp)
	movq	$0, 560(%rsp)
	movq	$0, 568(%rsp)
	movq	$0, 576(%rsp)
	movq	$0, 584(%rsp)
	movq	$0, 592(%rsp)
	movq	$0, 600(%rsp)
	movq	$0, 608(%rsp)
	movq	$0, 616(%rsp)
	movq	$0, 624(%rsp)
	movq	$0, 632(%rsp)
	movq	$0, 640(%rsp)
	movq	$0, 648(%rsp)
	movq	$0, 656(%rsp)
	movq	$0, 664(%rsp)
	movq	$0, 672(%rsp)
	movq	$0, 680(%rsp)
	movq	$0, 688(%rsp)
	movq	$0, 696(%rsp)
	movq	$0, 704(%rsp)
	movq	$0, 712(%rsp)
	movq	$0, 720(%rsp)
	movq	$0, 728(%rsp)
	movq	$0, 736(%rsp)
	movq	$0, 744(%rsp)
	movq	$0, 752(%rsp)
	movq	$0, 760(%rsp)
	movq	$0, 768(%rsp)
	movq	$0, 776(%rsp)
	movq	$0, 784(%rsp)
	movq	$0, 792(%rsp)
	movq	$0, 800(%rsp)
	movq	$0, 808(%rsp)
	movq	$0, 816(%rsp)
	movq	$0, 824(%rsp)
	leaq	320(%rsp), %rdx
	movl	$5, %esi
	movl	$32, %ecx
	movq	%r8, %rdi
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field9eq_kernel
	cmpq	$1, %rax
	jne	.LBB43_8
	movq	%r12, 8(%rsp)
	movq	%r15, 16(%rsp)
	movq	%rbx, %r15
	movq	%r14, %rbx
	movq	1392(%rsp), %r14
	movl	$8, %ebp
	xorl	%ecx, %ecx
	.p2align	4
.LBB43_2:
	leaq	1(%rcx), %r12
	movl	%ecx, %eax
	shrl	$2, %eax
	andl	$496, %eax
	movq	320(%rsp,%rax), %rdi
	movq	328(%rsp,%rax), %rsi
	movl	$1, %edx
	shlq	%cl, %rdx
	xorl	%ecx, %ecx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	movq	%rax, -8(%r14,%rbp)
	movq	%rdx, (%r14,%rbp)
	addq	$16, %rbp
	movq	%r12, %rcx
	cmpq	$25608, %rbp
	jne	.LBB43_2
	movq	$0, 24(%rsp)
	movq	$0, 32(%rsp)
	movq	$0, 40(%rsp)
	movq	$0, 48(%rsp)
	leaq	24(%rsp), %rdx
	movl	$1, %esi
	movl	$2, %ecx
	movq	%rbx, %r12
	movq	%rbx, %rdi
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field9eq_kernel
	testb	$1, %al
	je	.LBB43_9
	movq	40(%rsp), %rbp
	movq	48(%rsp), %r14
	leaq	320(%rsp), %rdi
	movl	$25, %esi
	movl	$25, %ecx
	movq	%r13, %rdx
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field3dot
	movq	%rdx, %rcx
	movq	%rbp, %rdi
	movq	%r14, %rsi
	movq	%rax, %rdx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	movq	%rax, %r13
	movq	%rdx, %rbp
	movq	$0, 56(%rsp)
	leaq	64(%rsp), %rdx
	movq	$0, 64(%rsp)
	movq	$0, 72(%rsp)
	movq	$0, 80(%rsp)
	movq	$0, 88(%rsp)
	movq	$0, 96(%rsp)
	movq	$0, 104(%rsp)
	movq	$0, 112(%rsp)
	movq	$0, 120(%rsp)
	movq	$0, 128(%rsp)
	movq	$0, 136(%rsp)
	movq	$0, 144(%rsp)
	movq	$0, 152(%rsp)
	movq	$0, 160(%rsp)
	movq	$0, 168(%rsp)
	movq	$0, 176(%rsp)
	movq	$0, 184(%rsp)
	movq	$0, 192(%rsp)
	movq	$0, 200(%rsp)
	movq	$0, 208(%rsp)
	movq	$0, 216(%rsp)
	movq	$0, 224(%rsp)
	movq	$0, 232(%rsp)
	movq	$0, 240(%rsp)
	movq	$0, 248(%rsp)
	movq	$0, 256(%rsp)
	movq	$0, 264(%rsp)
	movq	$0, 272(%rsp)
	movq	$0, 280(%rsp)
	movq	$0, 288(%rsp)
	movq	$0, 296(%rsp)
	movq	$0, 304(%rsp)
	movq	$0, 312(%rsp)
	movq	16(%rsp), %rbx
	cmpq	$4, %rbx
	movl	$4, %esi
	cmovbq	%rbx, %rsi
	movl	$16, %ecx
	movq	8(%rsp), %r14
	movq	%r14, %rdi
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field9eq_kernel
	testb	$1, %al
	je	.LBB43_9
	movq	%rdx, 56(%rsp)
	movq	$0, 840(%rsp)
	movq	$0, 848(%rsp)
	movq	$0, 856(%rsp)
	movq	$0, 864(%rsp)
	movq	$0, 872(%rsp)
	movq	$0, 880(%rsp)
	movq	$0, 888(%rsp)
	movq	$0, 896(%rsp)
	movq	$0, 904(%rsp)
	movq	$0, 912(%rsp)
	movq	$0, 920(%rsp)
	movq	$0, 928(%rsp)
	movq	$0, 936(%rsp)
	movq	$0, 944(%rsp)
	movq	$0, 952(%rsp)
	movq	$0, 960(%rsp)
	movq	$0, 968(%rsp)
	movq	$0, 976(%rsp)
	movq	$0, 984(%rsp)
	movq	$0, 992(%rsp)
	movq	$0, 1000(%rsp)
	movq	$0, 1008(%rsp)
	movq	$0, 1016(%rsp)
	movq	$0, 1024(%rsp)
	movq	$0, 1032(%rsp)
	movq	$0, 1040(%rsp)
	movq	$0, 1048(%rsp)
	movq	$0, 1056(%rsp)
	movq	$0, 1064(%rsp)
	movq	$0, 1072(%rsp)
	movq	$0, 1080(%rsp)
	movq	$0, 1088(%rsp)
	movq	$0, 1096(%rsp)
	movq	$0, 1104(%rsp)
	movq	$0, 1112(%rsp)
	movq	$0, 1120(%rsp)
	movq	$0, 1128(%rsp)
	movq	$0, 1136(%rsp)
	movq	$0, 1144(%rsp)
	movq	$0, 1152(%rsp)
	movq	$0, 1160(%rsp)
	movq	$0, 1168(%rsp)
	movq	$0, 1176(%rsp)
	movq	$0, 1184(%rsp)
	movq	$0, 1192(%rsp)
	movq	$0, 1200(%rsp)
	movq	$0, 1208(%rsp)
	movq	$0, 1216(%rsp)
	movq	$0, 1224(%rsp)
	movq	$0, 1232(%rsp)
	movq	$0, 1240(%rsp)
	movq	$0, 1248(%rsp)
	movq	$0, 1256(%rsp)
	movq	$0, 1264(%rsp)
	movq	$0, 1272(%rsp)
	movq	$0, 1280(%rsp)
	movq	$0, 1288(%rsp)
	movq	$0, 1296(%rsp)
	movq	$0, 1304(%rsp)
	addq	$64, %r14
	xorl	%edx, %edx
	subq	$4, %rbx
	movl	$8, %esi
	cmovaeq	%r14, %rsi
	movq	$0, 1312(%rsp)
	cmovaeq	%rbx, %rdx
	movq	$0, 832(%rsp)
	leaq	832(%rsp), %rdi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKj1e_E6extendB4_
	testb	%al, %al
	je	.LBB43_9
	leaq	832(%rsp), %rdi
	movl	$1, %edx
	movq	%r12, %rsi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKj1e_E6extendB4_
	testb	%al, %al
	je	.LBB43_9
	xorq	1376(%rsp), %r13
	xorq	1384(%rsp), %rbp
	leaq	24(%r15), %rdi
	leaq	56(%rsp), %rsi
	movq	memcpy@GOTPCREL(%rip), %r14
	movl	$264, %edx
	callq	*%r14
	leaq	288(%r15), %rdi
	leaq	832(%rsp), %rsi
	movl	$488, %edx
	callq	*%r14
	movq	%r13, 8(%r15)
	movq	%rbp, 16(%r15)
	movq	$1, (%r15)
	jmp	.LBB43_10
.LBB43_8:
	movq	$0, (%rbx)
	jmp	.LBB43_10
.LBB43_9:
	movq	$0, (%r15)
.LBB43_10:
	addq	$1320, %rsp
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
.Lfunc_end43:
	.size	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr11first_claim, .Lfunc_end43-_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr11first_claim
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr11keccak_open,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr11keccak_open,@function
_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr11keccak_open:
.Lfunc_begin44:
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
	subq	$2152, %rsp
	.cfi_def_cfa_offset 2208
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	%r9, %r14
	movq	%r8, %r12
	movq	%rcx, %r13
	movq	%rdx, %rbp
	movq	%rdi, %rbx
	movq	2240(%rsp), %r9
	movq	2224(%rsp), %rdx
	movq	2232(%rsp), %rcx
	movq	$6, (%rsp)
	leaq	80(%rsp), %rdi
	movl	$3, %r8d
	callq	_RINvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB6_6TState8sumcheckNCNvB2_14sumcheck_plain0EB8_
	cmpl	$1, 80(%rsp)
	jne	.LBB44_2
	movq	2248(%rsp), %r15
	movq	2216(%rsp), %r9
	movq	2208(%rsp), %r8
	movq	88(%rsp), %rax
	movq	%rax, 72(%rsp)
	movq	96(%rsp), %rax
	movq	%rax, 64(%rsp)
	movq	%r15, (%rsp)
	movq	%rbp, %rdi
	movq	%r13, %rsi
	movq	%r12, %rdx
	movq	%r14, %rcx
	callq	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr12slot_weights
	testb	%al, %al
	je	.LBB44_2
	movq	%rbx, 56(%rsp)
	movq	2240(%rsp), %rax
	movq	(%rax), %r12
	movq	8(%rax), %r13
	xorl	%ebx, %ebx
	movq	%r15, %r14
	.p2align	4
.LBB44_41:
	movq	%rbx, 8(%rsp)
	shlq	$11, %rbx
	movq	2248(%rsp), %r15
	leaq	(%r15,%rbx), %rsi
	movl	$1024, %edx
	leaq	104(%rsp), %rdi
	movq	memcpy@GOTPCREL(%rip), %rbp
	callq	*%rbp
	leaq	(%r15,%rbx), %rsi
	addq	$1024, %rsi
	movl	$1024, %edx
	leaq	1128(%rsp), %rdi
	callq	*%rbp
	movl	$8, %ebx
	.p2align	4
.LBB44_42:
	movq	96(%rsp,%rbx), %rbp
	movq	104(%rsp,%rbx), %r15
	movq	1120(%rsp,%rbx), %rdx
	xorq	%rbp, %rdx
	movq	1128(%rsp,%rbx), %rcx
	xorq	%r15, %rcx
	movq	%r12, %rdi
	movq	%r13, %rsi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	xorq	%rbp, %rax
	xorq	%r15, %rdx
	movq	%rax, -8(%r14,%rbx)
	movq	%rdx, (%r14,%rbx)
	addq	$16, %rbx
	cmpq	$1032, %rbx
	jne	.LBB44_42
	movq	8(%rsp), %rbx
	incq	%rbx
	addq	$1024, %r14
	cmpq	$32, %rbx
	jne	.LBB44_41
	movq	2240(%rsp), %rax
	movq	16(%rax), %r12
	movq	24(%rax), %r13
	xorl	%ebp, %ebp
	movq	2248(%rsp), %rbx
	.p2align	4
.LBB44_5:
	movq	%rbp, 8(%rsp)
	shlq	$11, %rbp
	movq	2248(%rsp), %r14
	leaq	(%r14,%rbp), %rsi
	movl	$1024, %edx
	leaq	104(%rsp), %rdi
	movq	memcpy@GOTPCREL(%rip), %r15
	callq	*%r15
	leaq	(%r14,%rbp), %rsi
	addq	$1024, %rsi
	movl	$1024, %edx
	leaq	1128(%rsp), %rdi
	callq	*%r15
	movl	$8, %ebp
	.p2align	4
.LBB44_6:
	movq	96(%rsp,%rbp), %r14
	movq	104(%rsp,%rbp), %r15
	movq	1120(%rsp,%rbp), %rdx
	xorq	%r14, %rdx
	movq	1128(%rsp,%rbp), %rcx
	xorq	%r15, %rcx
	movq	%r12, %rdi
	movq	%r13, %rsi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	xorq	%r14, %rax
	xorq	%r15, %rdx
	movq	%rax, -8(%rbx,%rbp)
	movq	%rdx, (%rbx,%rbp)
	addq	$16, %rbp
	cmpq	$1032, %rbp
	jne	.LBB44_6
	movq	8(%rsp), %rbp
	incq	%rbp
	addq	$1024, %rbx
	cmpq	$16, %rbp
	jne	.LBB44_5
	movq	2240(%rsp), %rax
	movq	32(%rax), %rbp
	movq	40(%rax), %r12
	leaq	104(%rsp), %rdi
	movl	$1024, %edx
	movq	2248(%rsp), %r13
	movq	%r13, %rsi
	movq	memcpy@GOTPCREL(%rip), %rbx
	callq	*%rbx
	leaq	1024(%r13), %rsi
	leaq	1128(%rsp), %rdi
	movl	$1024, %edx
	movq	%rsi, 8(%rsp)
	callq	*%rbx
	movl	$8, %ebx
	.p2align	4
.LBB44_9:
	movq	96(%rsp,%rbx), %r14
	movq	104(%rsp,%rbx), %r15
	movq	1120(%rsp,%rbx), %rdx
	xorq	%r14, %rdx
	movq	1128(%rsp,%rbx), %rcx
	xorq	%r15, %rcx
	movq	%rbp, %rdi
	movq	%r12, %rsi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	xorq	%r14, %rax
	xorq	%r15, %rdx
	movq	%rax, -8(%r13,%rbx)
	movq	%rdx, (%r13,%rbx)
	addq	$16, %rbx
	cmpq	$1032, %rbx
	jne	.LBB44_9
	leaq	2048(%r13), %rsi
	leaq	104(%rsp), %rdi
	movl	$1024, %edx
	movq	%rsi, 24(%rsp)
	movq	memcpy@GOTPCREL(%rip), %rbx
	callq	*%rbx
	leaq	3072(%r13), %rsi
	leaq	1128(%rsp), %rdi
	movl	$1024, %edx
	movq	%rsi, 16(%rsp)
	callq	*%rbx
	movl	$1032, %ebx
	.p2align	4
.LBB44_11:
	movq	-928(%rsp,%rbx), %r14
	movq	-920(%rsp,%rbx), %r15
	movq	96(%rsp,%rbx), %rdx
	xorq	%r14, %rdx
	movq	104(%rsp,%rbx), %rcx
	xorq	%r15, %rcx
	movq	%rbp, %rdi
	movq	%r12, %rsi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	xorq	%r14, %rax
	xorq	%r15, %rdx
	movq	%rax, -8(%r13,%rbx)
	movq	%rdx, (%r13,%rbx)
	addq	$16, %rbx
	cmpq	$2056, %rbx
	jne	.LBB44_11
	leaq	4096(%r13), %rsi
	leaq	104(%rsp), %rdi
	movl	$1024, %edx
	movq	%rsi, 48(%rsp)
	movq	memcpy@GOTPCREL(%rip), %rbx
	callq	*%rbx
	leaq	5120(%r13), %rsi
	leaq	1128(%rsp), %rdi
	movl	$1024, %edx
	movq	%rsi, 40(%rsp)
	callq	*%rbx
	movl	$2048, %ebx
	.p2align	4
.LBB44_13:
	movq	-1944(%rsp,%rbx), %r14
	movq	-1936(%rsp,%rbx), %r15
	movq	-920(%rsp,%rbx), %rdx
	xorq	%r14, %rdx
	movq	-912(%rsp,%rbx), %rcx
	xorq	%r15, %rcx
	movq	%rbp, %rdi
	movq	%r12, %rsi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	xorq	%r14, %rax
	xorq	%r15, %rdx
	movq	%rax, (%r13,%rbx)
	movq	%rdx, 8(%r13,%rbx)
	addq	$16, %rbx
	cmpq	$3072, %rbx
	jne	.LBB44_13
	leaq	6144(%r13), %rsi
	leaq	104(%rsp), %rdi
	movl	$1024, %edx
	movq	%rsi, 32(%rsp)
	movq	memcpy@GOTPCREL(%rip), %rbx
	callq	*%rbx
	leaq	7168(%r13), %rsi
	leaq	1128(%rsp), %rdi
	movl	$1024, %edx
	callq	*%rbx
	movl	$3072, %ebx
	.p2align	4
.LBB44_15:
	movq	-2968(%rsp,%rbx), %r14
	movq	-2960(%rsp,%rbx), %r15
	movq	-1944(%rsp,%rbx), %rdx
	xorq	%r14, %rdx
	movq	-1936(%rsp,%rbx), %rcx
	xorq	%r15, %rcx
	movq	%rbp, %rdi
	movq	%r12, %rsi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	xorq	%r14, %rax
	xorq	%r15, %rdx
	movq	%rax, (%r13,%rbx)
	movq	%rdx, 8(%r13,%rbx)
	addq	$16, %rbx
	cmpq	$4096, %rbx
	jne	.LBB44_15
	leaq	8192(%r13), %rsi
	leaq	104(%rsp), %rdi
	movl	$1024, %edx
	movq	memcpy@GOTPCREL(%rip), %rbx
	callq	*%rbx
	leaq	9216(%r13), %rsi
	leaq	1128(%rsp), %rdi
	movl	$1024, %edx
	callq	*%rbx
	movl	$4096, %ebx
	.p2align	4
.LBB44_17:
	movq	-3992(%rsp,%rbx), %r14
	movq	-3984(%rsp,%rbx), %r15
	movq	-2968(%rsp,%rbx), %rdx
	xorq	%r14, %rdx
	movq	-2960(%rsp,%rbx), %rcx
	xorq	%r15, %rcx
	movq	%rbp, %rdi
	movq	%r12, %rsi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	xorq	%r14, %rax
	xorq	%r15, %rdx
	movq	%rax, (%r13,%rbx)
	movq	%rdx, 8(%r13,%rbx)
	addq	$16, %rbx
	cmpq	$5120, %rbx
	jne	.LBB44_17
	leaq	10240(%r13), %rsi
	leaq	104(%rsp), %rdi
	movl	$1024, %edx
	movq	memcpy@GOTPCREL(%rip), %rbx
	callq	*%rbx
	leaq	11264(%r13), %rsi
	leaq	1128(%rsp), %rdi
	movl	$1024, %edx
	callq	*%rbx
	movl	$5128, %ebx
	.p2align	4
.LBB44_19:
	movq	-5024(%rsp,%rbx), %r14
	movq	-5016(%rsp,%rbx), %r15
	movq	-4000(%rsp,%rbx), %rdx
	xorq	%r14, %rdx
	movq	-3992(%rsp,%rbx), %rcx
	xorq	%r15, %rcx
	movq	%rbp, %rdi
	movq	%r12, %rsi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	xorq	%r14, %rax
	xorq	%r15, %rdx
	movq	%rax, -8(%r13,%rbx)
	movq	%rdx, (%r13,%rbx)
	addq	$16, %rbx
	cmpq	$6152, %rbx
	jne	.LBB44_19
	leaq	12288(%r13), %rsi
	leaq	104(%rsp), %rdi
	movl	$1024, %edx
	movq	memcpy@GOTPCREL(%rip), %rbx
	callq	*%rbx
	leaq	13312(%r13), %rsi
	leaq	1128(%rsp), %rdi
	movl	$1024, %edx
	callq	*%rbx
	movl	$6152, %ebx
	.p2align	4
.LBB44_21:
	movq	-6048(%rsp,%rbx), %r14
	movq	-6040(%rsp,%rbx), %r15
	movq	-5024(%rsp,%rbx), %rdx
	xorq	%r14, %rdx
	movq	-5016(%rsp,%rbx), %rcx
	xorq	%r15, %rcx
	movq	%rbp, %rdi
	movq	%r12, %rsi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	xorq	%r14, %rax
	xorq	%r15, %rdx
	movq	%rax, -8(%r13,%rbx)
	movq	%rdx, (%r13,%rbx)
	addq	$16, %rbx
	cmpq	$7176, %rbx
	jne	.LBB44_21
	leaq	14336(%r13), %rsi
	leaq	104(%rsp), %rdi
	movl	$1024, %edx
	movq	memcpy@GOTPCREL(%rip), %rbx
	callq	*%rbx
	leaq	15360(%r13), %rsi
	leaq	1128(%rsp), %rdi
	movl	$1024, %edx
	callq	*%rbx
	movl	$7168, %ebx
	.p2align	4
.LBB44_23:
	movq	-7064(%rsp,%rbx), %r14
	movq	-7056(%rsp,%rbx), %r15
	movq	-6040(%rsp,%rbx), %rdx
	xorq	%r14, %rdx
	movq	-6032(%rsp,%rbx), %rcx
	xorq	%r15, %rcx
	movq	%rbp, %rdi
	movq	%r12, %rsi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	xorq	%r14, %rax
	xorq	%r15, %rdx
	movq	%rax, (%r13,%rbx)
	movq	%rdx, 8(%r13,%rbx)
	addq	$16, %rbx
	cmpq	$8192, %rbx
	jne	.LBB44_23
	movq	2240(%rsp), %rax
	movq	48(%rax), %r12
	movq	56(%rax), %rbp
	leaq	104(%rsp), %rdi
	movl	$1024, %edx
	movq	%r13, %rsi
	movq	memcpy@GOTPCREL(%rip), %rbx
	callq	*%rbx
	leaq	1128(%rsp), %rdi
	movl	$1024, %edx
	movq	8(%rsp), %rsi
	callq	*%rbx
	movl	$8, %ebx
	.p2align	4
.LBB44_25:
	movq	96(%rsp,%rbx), %r14
	movq	104(%rsp,%rbx), %r15
	movq	1120(%rsp,%rbx), %rdx
	xorq	%r14, %rdx
	movq	1128(%rsp,%rbx), %rcx
	xorq	%r15, %rcx
	movq	%r12, %rdi
	movq	%rbp, %rsi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	xorq	%r14, %rax
	xorq	%r15, %rdx
	movq	%rax, -8(%r13,%rbx)
	movq	%rdx, (%r13,%rbx)
	addq	$16, %rbx
	cmpq	$1032, %rbx
	jne	.LBB44_25
	leaq	104(%rsp), %rdi
	movl	$1024, %edx
	movq	24(%rsp), %rsi
	movq	memcpy@GOTPCREL(%rip), %rbx
	callq	*%rbx
	leaq	1128(%rsp), %rdi
	movl	$1024, %edx
	movq	16(%rsp), %rsi
	callq	*%rbx
	movl	$1032, %ebx
	.p2align	4
.LBB44_27:
	movq	-928(%rsp,%rbx), %r14
	movq	-920(%rsp,%rbx), %r15
	movq	96(%rsp,%rbx), %rdx
	xorq	%r14, %rdx
	movq	104(%rsp,%rbx), %rcx
	xorq	%r15, %rcx
	movq	%r12, %rdi
	movq	%rbp, %rsi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	xorq	%r14, %rax
	xorq	%r15, %rdx
	movq	%rax, -8(%r13,%rbx)
	movq	%rdx, (%r13,%rbx)
	addq	$16, %rbx
	cmpq	$2056, %rbx
	jne	.LBB44_27
	leaq	104(%rsp), %rdi
	movl	$1024, %edx
	movq	48(%rsp), %rsi
	movq	memcpy@GOTPCREL(%rip), %rbx
	callq	*%rbx
	leaq	1128(%rsp), %rdi
	movl	$1024, %edx
	movq	40(%rsp), %rsi
	callq	*%rbx
	movl	$2048, %ebx
	.p2align	4
.LBB44_29:
	movq	-1944(%rsp,%rbx), %r14
	movq	-1936(%rsp,%rbx), %r15
	movq	-920(%rsp,%rbx), %rdx
	xorq	%r14, %rdx
	movq	-912(%rsp,%rbx), %rcx
	xorq	%r15, %rcx
	movq	%r12, %rdi
	movq	%rbp, %rsi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	xorq	%r14, %rax
	xorq	%r15, %rdx
	movq	%rax, (%r13,%rbx)
	movq	%rdx, 8(%r13,%rbx)
	addq	$16, %rbx
	cmpq	$3072, %rbx
	jne	.LBB44_29
	leaq	104(%rsp), %rdi
	movl	$1024, %edx
	movq	32(%rsp), %rsi
	movq	memcpy@GOTPCREL(%rip), %rbx
	callq	*%rbx
	leaq	1128(%rsp), %rdi
	movl	$1024, %edx
	leaq	7168(%r13), %rsi
	callq	*%rbx
	movl	$3072, %ebx
	.p2align	4
.LBB44_31:
	movq	-2968(%rsp,%rbx), %r14
	movq	-2960(%rsp,%rbx), %r15
	movq	-1944(%rsp,%rbx), %rdx
	xorq	%r14, %rdx
	movq	-1936(%rsp,%rbx), %rcx
	xorq	%r15, %rcx
	movq	%r12, %rdi
	movq	%rbp, %rsi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	xorq	%r14, %rax
	xorq	%r15, %rdx
	movq	%rax, (%r13,%rbx)
	movq	%rdx, 8(%r13,%rbx)
	addq	$16, %rbx
	cmpq	$4096, %rbx
	jne	.LBB44_31
	movq	2240(%rsp), %rax
	movq	64(%rax), %r12
	movq	%r13, %rbp
	movq	72(%rax), %r13
	leaq	104(%rsp), %rdi
	movl	$1024, %edx
	movq	%rbp, %rsi
	movq	memcpy@GOTPCREL(%rip), %rbx
	callq	*%rbx
	leaq	1128(%rsp), %rdi
	movl	$1024, %edx
	movq	8(%rsp), %rsi
	callq	*%rbx
	movl	$8, %ebx
	.p2align	4
.LBB44_33:
	movq	96(%rsp,%rbx), %r14
	movq	104(%rsp,%rbx), %r15
	movq	1120(%rsp,%rbx), %rdx
	xorq	%r14, %rdx
	movq	1128(%rsp,%rbx), %rcx
	xorq	%r15, %rcx
	movq	%r12, %rdi
	movq	%r13, %rsi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	xorq	%r14, %rax
	xorq	%r15, %rdx
	movq	%rax, -8(%rbp,%rbx)
	movq	%rdx, (%rbp,%rbx)
	addq	$16, %rbx
	cmpq	$1032, %rbx
	jne	.LBB44_33
	leaq	104(%rsp), %rdi
	movl	$1024, %edx
	movq	24(%rsp), %rsi
	movq	memcpy@GOTPCREL(%rip), %rbx
	callq	*%rbx
	leaq	1128(%rsp), %rdi
	movl	$1024, %edx
	movq	16(%rsp), %rsi
	callq	*%rbx
	movl	$1032, %ebx
	.p2align	4
.LBB44_35:
	movq	-928(%rsp,%rbx), %r14
	movq	-920(%rsp,%rbx), %r15
	movq	96(%rsp,%rbx), %rdx
	xorq	%r14, %rdx
	movq	104(%rsp,%rbx), %rcx
	xorq	%r15, %rcx
	movq	%r12, %rdi
	movq	%r13, %rsi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	xorq	%r14, %rax
	xorq	%r15, %rdx
	movq	%rax, -8(%rbp,%rbx)
	movq	%rdx, (%rbp,%rbx)
	addq	$16, %rbx
	cmpq	$2056, %rbx
	jne	.LBB44_35
	movq	2240(%rsp), %rax
	movq	80(%rax), %r14
	movq	88(%rax), %r15
	leaq	104(%rsp), %rdi
	movl	$1024, %edx
	movq	%rbp, %rsi
	movq	memcpy@GOTPCREL(%rip), %rbx
	callq	*%rbx
	leaq	1128(%rsp), %rdi
	movl	$1024, %edx
	movq	8(%rsp), %rsi
	callq	*%rbx
	xorl	%ebx, %ebx
	.p2align	4
.LBB44_37:
	leaq	16(%rbx), %r12
	movq	104(%rsp,%rbx), %r13
	movq	112(%rsp,%rbx), %rbp
	movq	1128(%rsp,%rbx), %rdx
	xorq	%r13, %rdx
	movq	1136(%rsp,%rbx), %rcx
	xorq	%rbp, %rcx
	movq	%r14, %rdi
	movq	%r15, %rsi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	xorq	%r13, %rax
	movq	2248(%rsp), %rcx
	xorq	%rbp, %rdx
	movq	%rax, (%rcx,%rbx)
	movq	%rdx, 8(%rcx,%rbx)
	movq	%r12, %rbx
	cmpq	$1024, %r12
	jne	.LBB44_37
	movq	56(%rsp), %rbx
	movq	72(%rsp), %rax
	movq	%rax, 8(%rbx)
	movq	64(%rsp), %rax
	movq	%rax, 16(%rbx)
	movl	$1, %eax
	jmp	.LBB44_3
.LBB44_2:
	xorl	%eax, %eax
.LBB44_3:
	movq	%rax, (%rbx)
	addq	$2152, %rsp
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
.Lfunc_end44:
	.size	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr11keccak_open, .Lfunc_end44-_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr11keccak_open
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr12keccak_phase,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr12keccak_phase,@function
_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr12keccak_phase:
.Lfunc_begin45:
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
	subq	$408, %rsp
	.cfi_def_cfa_offset 464
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	10328(%rdx), %r11
	movq	$0, 8(%rsp)
	movq	$0, 16(%rsp)
	movq	$0, 24(%rsp)
	movq	$0, 32(%rsp)
	movq	$0, 40(%rsp)
	movq	$0, 48(%rsp)
	movq	$0, 56(%rsp)
	movq	$0, 64(%rsp)
	movq	$0, 72(%rsp)
	movq	$0, 80(%rsp)
	movq	$0, 88(%rsp)
	movq	$0, 96(%rsp)
	movq	$0, 104(%rsp)
	movq	$0, 112(%rsp)
	movq	$0, 120(%rsp)
	movq	$0, 128(%rsp)
	movq	$0, 136(%rsp)
	movq	$0, 144(%rsp)
	movq	$0, 152(%rsp)
	movq	$0, 160(%rsp)
	movq	$0, 168(%rsp)
	movq	$0, 176(%rsp)
	movq	$0, 184(%rsp)
	movq	$0, 192(%rsp)
	movq	$0, 200(%rsp)
	movq	$0, 208(%rsp)
	movq	$0, 216(%rsp)
	movq	$0, 224(%rsp)
	movq	$0, 232(%rsp)
	movq	$0, 240(%rsp)
	movq	$0, 248(%rsp)
	movq	$0, 256(%rsp)
	movq	$0, 264(%rsp)
	movq	$0, 272(%rsp)
	movq	$0, 280(%rsp)
	movq	$0, 288(%rsp)
	movq	$0, 296(%rsp)
	movq	$0, 304(%rsp)
	movq	$0, 312(%rsp)
	movq	$0, 320(%rsp)
	movq	$0, 328(%rsp)
	movq	$0, 336(%rsp)
	movq	$0, 344(%rsp)
	movq	$0, 352(%rsp)
	movq	$0, 360(%rsp)
	movq	$0, 368(%rsp)
	movq	$0, 376(%rsp)
	movq	$0, 384(%rsp)
	movq	$0, 392(%rsp)
	movq	$0, 400(%rsp)
	xorl	%eax, %eax
	cmpq	$93, %r11
	movl	$0, %ebx
	cmovbq	%r11, %rbx
	movq	%rbx, %r10
	subq	$40, %r10
	cmovbq	%rax, %r10
	cmpq	$25, %r10
	movl	$25, %r15d
	cmovbq	%r10, %r15
	leaq	40(%r15), %r10
	cmpq	%rbx, %r10
	ja	.LBB45_2
	leaq	10336(%rdx), %rax
	cmpq	$93, %r11
	movq	%rcx, %r14
	movl	$8, %ecx
	cmovaeq	%rcx, %rax
	addq	$640, %rax
	shlq	$4, %r15
	leaq	8(%rsp), %rcx
	movq	%rdi, %r13
	movq	%rcx, %rdi
	movq	%rsi, %rbp
	movq	%rax, %rsi
	movq	%r9, %r12
	movq	%rdx, %rbx
	movq	%r15, %rdx
	movq	%r8, %r15
	callq	*memcpy@GOTPCREL(%rip)
	movq	9840(%rbx), %rax
	addq	$9848, %rbx
	xorl	%ecx, %ecx
	cmpq	$31, %rax
	movl	$8, %edx
	cmovaeq	%rdx, %rbx
	cmovbq	%rax, %rcx
	movq	%r13, %rdi
	movq	%rbp, %rsi
	movq	%rbx, %rdx
	leaq	8(%rsp), %r8
	movq	%r14, %r9
	pushq	%r12
	.cfi_adjust_cfa_offset 8
	pushq	%r15
	.cfi_adjust_cfa_offset 8
	callq	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr13verify_keccak
	addq	$16, %rsp
	.cfi_adjust_cfa_offset -16
.LBB45_2:
	addq	$408, %rsp
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
.Lfunc_end45:
	.size	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr12keccak_phase, .Lfunc_end45-_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr12keccak_phase
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr12slot_weights,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr12slot_weights,@function
_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr12slot_weights:
.Lfunc_begin46:
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
	subq	$104, %rsp
	.cfi_def_cfa_offset 160
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	%r9, 16(%rsp)
	movq	%r8, 8(%rsp)
	movq	%rcx, 32(%rsp)
	movq	$0, 40(%rsp)
	movq	$0, 48(%rsp)
	movq	$0, 56(%rsp)
	movq	$0, 64(%rsp)
	movq	$0, 72(%rsp)
	movq	$0, 80(%rsp)
	movq	$0, 88(%rsp)
	movq	$0, 96(%rsp)
	xorl	%eax, %eax
	subq	$4, %rdi
	cmovbq	%rax, %rdi
	movq	%rdi, %rcx
	shlq	$4, %rcx
	addq	%rsi, %rcx
	subq	%rdi, %rdx
	movl	$8, %edi
	cmovaeq	%rcx, %rdi
	cmovaeq	%rdx, %rax
	leaq	40(%rsp), %rdx
	movl	$4, %ecx
	movq	%rax, %rsi
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field9eq_kernel
	movq	%rax, (%rsp)
	cmpq	$1, %rax
	jne	.LBB46_11
	movq	160(%rsp), %rax
	addq	$56, %rax
	xorl	%ecx, %ecx
	.p2align	4
.LBB46_2:
	xorl	%edx, %edx
	.p2align	4
.LBB46_3:
	movq	$0, -56(%rax,%rdx)
	movq	$0, -48(%rax,%rdx)
	movq	$0, -40(%rax,%rdx)
	movq	$0, -32(%rax,%rdx)
	movq	$0, -24(%rax,%rdx)
	movq	$0, -16(%rax,%rdx)
	movq	$0, -8(%rax,%rdx)
	movq	$0, (%rax,%rdx)
	addq	$64, %rdx
	cmpq	$1024, %rdx
	jne	.LBB46_3
	addq	$1024, %rcx
	addq	$1024, %rax
	cmpq	$65536, %rcx
	jne	.LBB46_2
	xorl	%ecx, %ecx
	jmp	.LBB46_7
	.p2align	4
.LBB46_6:
	movq	24(%rsp), %rcx
	incq	%rcx
	cmpq	16(%rsp), %rcx
	je	.LBB46_11
.LBB46_7:
	movq	%rcx, %rax
	shlq	$4, %rax
	movq	40(%rsp,%rax), %r13
	movq	48(%rsp,%rax), %rbp
	movq	8(%rsp), %rax
	movq	%rcx, 24(%rsp)
	addq	%rcx, %rax
	leaq	(%rax,%rax,4), %rax
	leaq	(%rax,%rax,4), %r14
	xorl	%r15d, %r15d
	xorl	%ebx, %ebx
	jmp	.LBB46_8
	.p2align	4
.LBB46_10:
	addq	$16, %rbx
	incq	%r15
	cmpq	$25600, %rbx
	je	.LBB46_6
.LBB46_8:
	movq	%r15, %r12
	shrq	$6, %r12
	addq	%r14, %r12
	cmpq	$63, %r12
	ja	.LBB46_10
	movq	32(%rsp), %rax
	movq	(%rax,%rbx), %rdx
	movq	8(%rax,%rbx), %rcx
	movq	%r13, %rdi
	movq	%rbp, %rsi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	movl	%r15d, %ecx
	andl	$63, %ecx
	shlq	$10, %r12
	addq	160(%rsp), %r12
	shll	$4, %ecx
	movq	%rax, (%rcx,%r12)
	movq	%rdx, 8(%rcx,%r12)
	jmp	.LBB46_10
.LBB46_11:
	movq	(%rsp), %rax
	andb	$1, %al
	addq	$104, %rsp
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
.Lfunc_end46:
	.size	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr12slot_weights, .Lfunc_end46-_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr12slot_weights
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr12verify_layer,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr12verify_layer,@function
_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr12verify_layer:
.Lfunc_begin47:
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
	subq	$1944, %rsp
	.cfi_def_cfa_offset 2000
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	%r8, %r15
	movq	%rcx, %r14
	movq	%rdx, %r13
	movq	%rdi, %r12
	movq	$0, 448(%rsp)
	movq	$0, 456(%rsp)
	movq	$0, 464(%rsp)
	movq	$0, 472(%rsp)
	movq	$0, 480(%rsp)
	movq	$0, 488(%rsp)
	movq	$0, 496(%rsp)
	movq	$0, 504(%rsp)
	movq	$0, 512(%rsp)
	movq	$0, 520(%rsp)
	movq	$0, 528(%rsp)
	movq	$0, 536(%rsp)
	movq	$0, 544(%rsp)
	movq	$0, 552(%rsp)
	movq	$0, 560(%rsp)
	movq	$0, 568(%rsp)
	movq	$0, 576(%rsp)
	movq	$0, 584(%rsp)
	movq	$0, 592(%rsp)
	movq	$0, 600(%rsp)
	movq	$0, 608(%rsp)
	movq	$0, 616(%rsp)
	movq	$0, 624(%rsp)
	movq	$0, 632(%rsp)
	movq	$0, 640(%rsp)
	movq	$0, 648(%rsp)
	movq	$0, 656(%rsp)
	movq	$0, 664(%rsp)
	movq	$0, 672(%rsp)
	movq	$0, 680(%rsp)
	movq	$0, 688(%rsp)
	movq	$0, 696(%rsp)
	movq	$0, 704(%rsp)
	movq	$0, 712(%rsp)
	movq	$0, 720(%rsp)
	movq	$0, 728(%rsp)
	movq	$0, 736(%rsp)
	movq	$0, 744(%rsp)
	movq	$0, 752(%rsp)
	movq	$0, 760(%rsp)
	movq	$0, 768(%rsp)
	movq	$0, 776(%rsp)
	movq	$0, 784(%rsp)
	movq	$0, 792(%rsp)
	movq	$0, 800(%rsp)
	movq	$0, 808(%rsp)
	movq	$0, 816(%rsp)
	movq	$0, 824(%rsp)
	movq	$0, 832(%rsp)
	movq	$0, 840(%rsp)
	movq	$0, 848(%rsp)
	movq	$0, 856(%rsp)
	movq	$0, 864(%rsp)
	movq	$0, 872(%rsp)
	movq	$0, 880(%rsp)
	movq	$0, 888(%rsp)
	movq	$0, 896(%rsp)
	movq	$0, 904(%rsp)
	movq	$0, 912(%rsp)
	movq	$0, 920(%rsp)
	movq	$0, 928(%rsp)
	movq	$0, 936(%rsp)
	movq	$0, 944(%rsp)
	movq	$0, 952(%rsp)
	movq	$0, 960(%rsp)
	movq	$0, 968(%rsp)
	movq	$0, 976(%rsp)
	movq	$0, 984(%rsp)
	movq	$0, 992(%rsp)
	movq	$0, 1000(%rsp)
	movq	$0, 1008(%rsp)
	movq	$0, 1016(%rsp)
	movq	$0, 1024(%rsp)
	movq	$0, 1032(%rsp)
	movq	$0, 1040(%rsp)
	movq	$0, 1048(%rsp)
	movq	$0, 1056(%rsp)
	movq	$0, 1064(%rsp)
	movq	$0, 1072(%rsp)
	movq	$0, 1080(%rsp)
	movq	$0, 1088(%rsp)
	movq	$0, 1096(%rsp)
	movq	$0, 1104(%rsp)
	movq	$0, 1112(%rsp)
	movq	$0, 1120(%rsp)
	movq	$0, 1128(%rsp)
	movq	$0, 1136(%rsp)
	movq	$0, 1144(%rsp)
	movq	$0, 1152(%rsp)
	movq	$0, 1160(%rsp)
	movq	$0, 1168(%rsp)
	movq	$0, 1176(%rsp)
	movq	$0, 1184(%rsp)
	movq	$0, 1192(%rsp)
	xorl	%ebx, %ebx
	subq	$4, %rsi
	movl	$0, %ebp
	cmovaeq	%rsi, %rbp
	leaq	448(%rsp), %rsi
	movl	$47, %edx
	callq	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState12read_scalars
	testb	%al, %al
	je	.LBB47_50
	movq	%rbp, (%rsp)
	movq	%r13, 32(%rsp)
	movq	%r12, 16(%rsp)
	movq	%r15, 56(%rsp)
	movq	16(%r14), %rsi
	leaq	24(%r14), %rcx
	xorl	%eax, %eax
	cmpq	$17, %rsi
	movl	$8, %edx
	cmovbq	%rcx, %rdx
	cmovaeq	%rax, %rsi
	movq	%r14, 72(%rsp)
	leaq	16(%r14), %rcx
	movq	%rcx, 200(%rsp)
	movl	%esi, %ebx
	andl	$30, %ebx
	movq	%rdx, 24(%rsp)
	leaq	24(%rdx), %rcx
	movq	%rcx, 40(%rsp)
	leaq	.Lanon.a75d6d9e6a8990b4224ef13f18552af8.0(%rip), %r15
	xorl	%r13d, %r13d
	xorl	%r14d, %r14d
	xorl	%r12d, %r12d
	movq	%rsi, 8(%rsp)
	jmp	.LBB47_4
	.p2align	4
.LBB47_2:
	xorq	%r8, %rdi
	xorq	%rdx, %rsi
.LBB47_3:
	leaq	16(%rax), %rbp
	incq	%r14
	movq	448(%rsp,%rax), %rdx
	movq	456(%rsp,%rax), %rcx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	xorq	%rax, %r12
	xorq	%rdx, %r13
	movq	%rbp, %rax
	cmpq	$752, %rbp
	movq	8(%rsp), %rsi
	je	.LBB47_17
.LBB47_4:
	testq	%rsi, %rsi
	je	.LBB47_7
	movl	$1, %edx
	movl	%r14d, %ecx
	shlq	%cl, %rdx
	cmpq	$1, %rsi
	jne	.LBB47_8
	xorl	%edi, %edi
	xorl	%esi, %esi
	xorl	%ecx, %ecx
	jmp	.LBB47_15
	.p2align	4
.LBB47_7:
	xorl	%esi, %esi
	xorl	%edi, %edi
	jmp	.LBB47_3
	.p2align	4
.LBB47_8:
	movq	40(%rsp), %r8
	xorl	%edi, %edi
	xorl	%esi, %esi
	xorl	%ecx, %ecx
	jmp	.LBB47_10
	.p2align	4
.LBB47_9:
	xorq	%r9, %rsi
	xorq	%r11, %rsi
	xorq	%r10, %rdi
	xorq	%rbp, %rdi
	addq	$2, %rcx
	addq	$32, %r8
	cmpq	%rcx, %rbx
	je	.LBB47_14
.LBB47_10:
	movq	(%r15,%rcx,8), %r9
	andq	%rdx, %r9
	movq	%r9, %r10
	je	.LBB47_12
	movq	-16(%r8), %r9
	movq	-24(%r8), %r10
.LBB47_12:
	movq	8(%r15,%rcx,8), %r11
	andq	%rdx, %r11
	movq	%r11, %rbp
	je	.LBB47_9
	movq	(%r8), %r11
	movq	-8(%r8), %rbp
	jmp	.LBB47_9
	.p2align	4
.LBB47_14:
	testb	$1, 8(%rsp)
	je	.LBB47_3
.LBB47_15:
	andq	(%r15,%rcx,8), %rdx
	movq	%rdx, %r8
	je	.LBB47_2
	shlq	$4, %rcx
	movq	24(%rsp), %r8
	movq	8(%r8,%rcx), %rdx
	movq	(%r8,%rcx), %r8
	jmp	.LBB47_2
.LBB47_17:
	movq	$0, 208(%rsp)
	movq	$0, 216(%rsp)
	movq	$0, 224(%rsp)
	movq	$0, 232(%rsp)
	movq	$0, 240(%rsp)
	movq	$0, 248(%rsp)
	movq	$0, 256(%rsp)
	movq	$0, 264(%rsp)
	movq	72(%rsp), %r14
	leaq	288(%r14), %rdx
	movq	280(%r14), %rsi
	xorl	%ebx, %ebx
	cmpq	$31, %rsi
	movl	$8, %eax
	movl	$8, %ecx
	movq	%rdx, 40(%rsp)
	cmovbq	%rdx, %rcx
	cmovaeq	%rbx, %rsi
	movq	(%rsp), %rdx
	movq	%rdx, %rdi
	shlq	$4, %rdi
	addq	%rcx, %rdi
	subq	%rdx, %rsi
	cmovbq	%rax, %rdi
	cmovbq	%rbx, %rsi
	leaq	208(%rsp), %rdx
	movl	$4, %ecx
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field9eq_kernel
	testb	$1, %al
	je	.LBB47_50
	leaq	280(%r14), %rax
	movq	%rax, 104(%rsp)
	movq	56(%rsp), %r15
	leaq	25600(%r15), %rax
	movq	%rax, 96(%rsp)
	movq	208(%rsp), %rdi
	movq	216(%rsp), %rsi
	movl	$11, %eax
	subl	32(%rsp), %eax
	shll	$3, %eax
	leaq	.Lanon.a75d6d9e6a8990b4224ef13f18552af8.1(%rip), %r8
	movq	(%rax,%r8), %r9
	leaq	25624(%r15), %r10
	xorl	%ecx, %ecx
	xorl	%eax, %eax
	xorl	%edx, %edx
	jmp	.LBB47_21
	.p2align	4
.LBB47_19:
	movq	-16(%r10), %r11
	movq	-24(%r10), %rbx
.LBB47_20:
	movq	%rdx, %r14
	xorq	%rbx, %r14
	movq	%rax, %rbx
	movq	%r9, %rdx
	shrq	%cl, %rdx
	xorq	%r11, %rbx
	shlq	$62, %rdx
	sarq	$63, %rdx
	movq	(%r10), %rax
	andq	%rdx, %rax
	xorq	%rbx, %rax
	andq	-8(%r10), %rdx
	xorq	%r14, %rdx
	addq	$2, %rcx
	addq	$32, %r10
	cmpq	$64, %rcx
	je	.LBB47_23
.LBB47_21:
	btq	%rcx, %r9
	jb	.LBB47_19
	xorl	%r11d, %r11d
	xorl	%ebx, %ebx
	jmp	.LBB47_20
.LBB47_23:
	movq	224(%rsp), %rcx
	movq	%rcx, (%rsp)
	movq	232(%rsp), %rcx
	movq	%rcx, 48(%rsp)
	movl	$23, %ecx
	subl	32(%rsp), %ecx
	shll	$3, %ecx
	movq	(%rcx,%r8), %r8
	leaq	25624(%r15), %r9
	xorl	%ecx, %ecx
	xorl	%ebx, %ebx
	xorl	%r15d, %r15d
	jmp	.LBB47_26
	.p2align	4
.LBB47_24:
	movq	-16(%r9), %r10
	movq	-24(%r9), %r11
.LBB47_25:
	movq	%r15, %r14
	xorq	%r11, %r14
	movq	%rbx, %r11
	movq	%r8, %r15
	shrq	%cl, %r15
	xorq	%r10, %r11
	shlq	$62, %r15
	sarq	$63, %r15
	movq	(%r9), %rbx
	andq	%r15, %rbx
	xorq	%r11, %rbx
	andq	-8(%r9), %r15
	xorq	%r14, %r15
	addq	$2, %rcx
	addq	$32, %r9
	cmpq	$64, %rcx
	je	.LBB47_28
.LBB47_26:
	btq	%rcx, %r8
	jb	.LBB47_24
	xorl	%r10d, %r10d
	xorl	%r11d, %r11d
	jmp	.LBB47_25
.LBB47_28:
	movq	%rax, %rcx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	movq	%rax, %r14
	movq	%rdx, %rbp
	movq	(%rsp), %rdi
	movq	48(%rsp), %rsi
	movq	%r15, %rdx
	movq	%rbx, %rcx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	xorq	%rdx, %rbp
	xorq	%rax, %r14
	movq	24(%rsp), %rdi
	movq	8(%rsp), %rsi
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field5sum_e
	movq	%rdx, %rcx
	movq	%r14, %rdi
	movq	%rbp, %rsi
	movq	%rax, %rdx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	xorq	%r12, %rax
	xorl	%ebx, %ebx
	movq	72(%rsp), %rcx
	cmpq	(%rcx), %rax
	jne	.LBB47_50
	xorq	%r13, %rdx
	cmpq	8(%rcx), %rdx
	jne	.LBB47_50
	movl	$45, %edi
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field10bit_length
	xorl	%ebx, %ebx
	subl	$3, %eax
	cmovbl	%ebx, %eax
	movq	16(%rsp), %rdi
	movl	%eax, %esi
	callq	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState5grind
	testb	%al, %al
	je	.LBB47_50
	movq	16(%rsp), %r14
	movq	%r14, %rdi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW7squeeze
	movq	%rax, %r12
	movq	%rdx, %r13
	leaq	1680(%rsp), %rdi
	movq	%rax, %rsi
	callq	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr16instance_weights
	movq	1680(%rsp), %rsi
	xorl	%r15d, %r15d
	cmpq	$17, %rsi
	leaq	1688(%rsp), %rdi
	movl	$8, %ebx
	cmovaeq	%rbx, %rdi
	cmovaeq	%r15, %rsi
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field5sum_e
	movq	%rax, 8(%rsp)
	movq	%rdx, 24(%rsp)
	movq	$0, 1200(%rsp)
	movq	$0, 1208(%rsp)
	movq	$0, 1216(%rsp)
	movq	$0, 1224(%rsp)
	movq	$0, 1232(%rsp)
	movq	$0, 1240(%rsp)
	movq	$0, 1248(%rsp)
	movq	$0, 1256(%rsp)
	movq	$0, 1264(%rsp)
	movq	$0, 1272(%rsp)
	movq	$0, 1280(%rsp)
	movq	$0, 1288(%rsp)
	movq	$0, 1296(%rsp)
	movq	$0, 1304(%rsp)
	movq	$0, 1312(%rsp)
	movq	$0, 1320(%rsp)
	movq	$0, 1328(%rsp)
	movq	$0, 1336(%rsp)
	movq	$0, 1344(%rsp)
	movq	$0, 1352(%rsp)
	movq	$0, 1360(%rsp)
	movq	$0, 1368(%rsp)
	movq	$0, 1376(%rsp)
	movq	$0, 1384(%rsp)
	movq	$0, 1392(%rsp)
	movq	$0, 1400(%rsp)
	movq	$0, 1408(%rsp)
	movq	$0, 1416(%rsp)
	movq	$0, 1424(%rsp)
	movq	$0, 1432(%rsp)
	movq	$0, 1440(%rsp)
	movq	$0, 1448(%rsp)
	movq	$0, 1456(%rsp)
	movq	$0, 1464(%rsp)
	movq	$0, 1472(%rsp)
	movq	$0, 1480(%rsp)
	movq	$0, 1488(%rsp)
	movq	$0, 1496(%rsp)
	movq	$0, 1504(%rsp)
	movq	$0, 1512(%rsp)
	movq	$0, 1520(%rsp)
	movq	$0, 1528(%rsp)
	movq	$0, 1536(%rsp)
	movq	$0, 1544(%rsp)
	movq	$0, 1552(%rsp)
	movq	$0, 1560(%rsp)
	movq	$0, 1568(%rsp)
	movq	$0, 1576(%rsp)
	movq	$0, 1584(%rsp)
	movq	$0, 1592(%rsp)
	movq	$0, 1600(%rsp)
	movq	$0, 1608(%rsp)
	movq	$0, 1616(%rsp)
	movq	$0, 1624(%rsp)
	movq	$0, 1632(%rsp)
	movq	$0, 1640(%rsp)
	movq	$0, 1648(%rsp)
	movq	$0, 1656(%rsp)
	movq	$0, 1664(%rsp)
	movq	$0, 1672(%rsp)
	movq	104(%rsp), %rax
	movq	(%rax), %rax
	cmpq	$31, %rax
	movq	40(%rsp), %rbp
	cmovaeq	%rbx, %rbp
	cmovbq	%rax, %r15
	leaq	448(%rsp), %rdi
	movl	$47, %esi
	movq	%r12, %rdx
	movq	%r14, %r12
	movq	%r13, %rcx
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field9poly_eval
	movq	%rdx, %rcx
	leaq	1200(%rsp), %r10
	leaq	272(%rsp), %rdi
	movq	%r14, %rsi
	movq	%rax, %rdx
	movq	%rbp, %r8
	movq	%r15, %r9
	movq	%r15, 40(%rsp)
	pushq	%r15
	.cfi_adjust_cfa_offset 8
	pushq	%r10
	.cfi_adjust_cfa_offset 8
	callq	_RINvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB6_6TState8sumcheckNCNvNtB8_10keccak_gkr12verify_layers1_0EB8_
	addq	$16, %rsp
	.cfi_adjust_cfa_offset -16
	cmpl	$1, 272(%rsp)
	movq	56(%rsp), %r15
	jne	.LBB47_49
	movq	280(%rsp), %rdx
	movq	288(%rsp), %rcx
	movq	$0, 272(%rsp)
	movq	$0, 280(%rsp)
	movq	$0, 288(%rsp)
	movq	$0, 296(%rsp)
	movq	$0, 304(%rsp)
	movq	$0, 312(%rsp)
	movq	$0, 320(%rsp)
	movq	$0, 328(%rsp)
	movq	$0, 336(%rsp)
	movq	$0, 344(%rsp)
	movq	$0, 352(%rsp)
	movq	$0, 360(%rsp)
	movq	$0, 368(%rsp)
	movq	$0, 376(%rsp)
	movq	$0, 384(%rsp)
	movq	$0, 392(%rsp)
	movq	$0, 400(%rsp)
	movq	$0, 408(%rsp)
	movq	$0, 416(%rsp)
	movq	$0, 424(%rsp)
	movq	$0, 432(%rsp)
	movq	$0, 440(%rsp)
	subq	$8, %rsp
	.cfi_adjust_cfa_offset 8
	leaq	120(%rsp), %rdi
	leaq	280(%rsp), %r9
	movl	$4, %r8d
	movq	%r12, %rsi
	pushq	$11
	.cfi_adjust_cfa_offset 8
	callq	_RINvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB6_6TState8sumcheckNCNvB2_14sumcheck_plain0EB8_
	addq	$16, %rsp
	.cfi_adjust_cfa_offset -16
	cmpb	$0, 112(%rsp)
	je	.LBB47_49
	movq	120(%rsp), %r14
	movq	128(%rsp), %rbx
	movq	$0, 112(%rsp)
	movq	$0, 120(%rsp)
	movq	$0, 128(%rsp)
	movq	$0, 136(%rsp)
	movq	$0, 144(%rsp)
	movq	$0, 152(%rsp)
	leaq	112(%rsp), %rsi
	movl	$3, %edx
	movq	%r12, %rdi
	callq	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState12read_scalars
	testb	%al, %al
	je	.LBB47_49
	leaq	107520(%r15), %rdx
	leaq	272(%rsp), %rdi
	movl	$11, %esi
	movl	$2048, %ecx
	movq	%rdx, 32(%rsp)
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field9eq_kernel
	testb	$1, %al
	je	.LBB47_49
	movq	112(%rsp), %r12
	movq	120(%rsp), %r13
	movq	128(%rsp), %rbp
	movq	136(%rsp), %rax
	movq	%rax, 48(%rsp)
	movq	144(%rsp), %rax
	movq	%rax, 88(%rsp)
	movq	152(%rsp), %rax
	movq	%rax, 80(%rsp)
	movl	$1600, %esi
	movl	$1600, %ecx
	leaq	107520(%r15), %rdi
	movq	96(%rsp), %rdx
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field3dot
	movq	%rax, 192(%rsp)
	movq	%rdx, 184(%rsp)
	movq	%r14, 64(%rsp)
	movq	8(%rsp), %r14
	movq	%r14, %rdi
	movq	%rbx, (%rsp)
	movq	24(%rsp), %rbx
	movq	%rbx, %rsi
	movq	%r12, 168(%rsp)
	movq	%r12, %rdx
	movq	%r13, 176(%rsp)
	movq	%r13, %rcx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	movq	%rax, %r12
	movq	%rdx, %r13
	movq	%rbp, 160(%rsp)
	xorq	%rbp, %r14
	xorq	48(%rsp), %rbx
	movq	%r14, %rdi
	movq	%rbx, %rsi
	movq	(%rsp), %rbx
	movq	88(%rsp), %rdx
	movq	80(%rsp), %rcx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	xorq	%rax, %r12
	xorq	%rdx, %r13
	movq	192(%rsp), %rdi
	movq	184(%rsp), %rsi
	movq	%r12, %rdx
	movq	16(%rsp), %r12
	movq	%r13, %rcx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	cmpq	64(%rsp), %rax
	jne	.LBB47_49
	cmpq	%rbx, %rdx
	jne	.LBB47_49
	movl	$1, %edi
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field10bit_length
	xorl	%esi, %esi
	subl	$3, %eax
	cmovael	%eax, %esi
	movq	%r12, %rdi
	callq	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState5grind
	testb	%al, %al
	je	.LBB47_49
	movabsq	$288230376151711742, %r13
	movq	%r12, %rdi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW7squeeze
	movq	%rax, (%rsp)
	movq	%rdx, 16(%rsp)
	leaq	51200(%r15), %rax
	movq	%rax, 64(%rsp)
	xorl	%ebp, %ebp
	xorl	%ebx, %ebx
	jmp	.LBB47_42
.LBB47_40:
	shlq	$4, %rax
	addq	32(%rsp), %rax
	shll	$4, %esi
	movq	(%rsi,%rax), %rdx
	movq	8(%rsi,%rax), %rcx
.LBB47_41:
	movq	107520(%r15,%rbx), %rax
	movq	%rax, 24(%rsp)
	movq	56(%rsp), %rax
	movq	107528(%rax,%rbx), %rax
	movq	%rax, 8(%rsp)
	movq	(%rsp), %r15
	movq	%r15, %rdi
	movq	16(%rsp), %r13
	movq	%r13, %rsi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	xorq	%rax, %r14
	xorq	%rdx, %r12
	movq	%r15, %rdi
	movq	%r13, %rsi
	movq	%r14, %rdx
	movq	%r12, %rcx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	xorq	24(%rsp), %rax
	xorq	8(%rsp), %rdx
	movq	56(%rsp), %r15
	movq	%rax, 51200(%r15,%rbx)
	movq	%rdx, 51208(%r15,%rbx)
	addq	$16, %rbx
	incq	%rbp
	cmpq	$25600, %rbx
	movabsq	$288230376151711742, %r13
	je	.LBB47_47
.LBB47_42:
	movq	%rbp, %rcx
	shrq	$6, %rcx
	movl	%ebp, %esi
	movq	%rcx, %rax
	movabsq	$3689348814741910324, %rdx
	mulq	%rdx
	andl	$63, %esi
	leaq	(%rdx,%rdx,4), %rax
	subq	%rax, %rcx
	leaq	1(%r13,%rcx), %rdi
	movl	$4, %eax
	cmoveq	%rax, %rdi
	movq	%rbp, %rax
	movabsq	$-3689348814741910323, %rdx
	mulq	%rdx
	shrq	$8, %rdx
	leaq	(%rdx,%rdx,4), %rax
	addq	%rax, %rdi
	shlq	$6, %rdi
	cmpq	$2047, %rdi
	ja	.LBB47_44
	shlq	$4, %rdi
	addq	32(%rsp), %rdi
	movl	%esi, %edx
	shll	$4, %edx
	movq	(%rdx,%rdi), %r14
	movq	8(%rdx,%rdi), %r12
	jmp	.LBB47_45
.LBB47_44:
	xorl	%r14d, %r14d
	xorl	%r12d, %r12d
.LBB47_45:
	cmpq	$2, %rcx
	movq	%r13, %rdx
	movl	$3, %edi
	cmovbq	%rdi, %rdx
	addq	%rcx, %rax
	addq	%rdx, %rax
	shlq	$6, %rax
	cmpq	$2047, %rax
	jbe	.LBB47_40
	xorl	%edx, %edx
	xorl	%ecx, %ecx
	jmp	.LBB47_41
.LBB47_47:
	leaq	76800(%r15), %rsi
	addq	$102400, %r15
	movq	64(%rsp), %rdi
	movq	%r15, %rdx
	movq	96(%rsp), %rcx
	callq	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr16linear_transpose
	movq	(%rsp), %rbx
	movq	%rbx, %rdi
	movq	16(%rsp), %r14
	movq	%r14, %rsi
	movq	88(%rsp), %rdx
	movq	80(%rsp), %rcx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	movq	160(%rsp), %r8
	xorq	%rax, %r8
	movq	48(%rsp), %rcx
	xorq	%rdx, %rcx
	movq	%rbx, %rdi
	movq	%r14, %rsi
	movq	%r8, %rdx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	xorq	168(%rsp), %rax
	xorq	176(%rsp), %rdx
	movq	72(%rsp), %rbx
	movq	%rax, (%rbx)
	movq	%rdx, 8(%rbx)
	leaq	1680(%rsp), %rsi
	movl	$264, %edx
	movq	200(%rsp), %rdi
	callq	*memcpy@GOTPCREL(%rip)
	movq	$0, 280(%rbx)
	leaq	1200(%rsp), %rsi
	movq	104(%rsp), %rdi
	movq	40(%rsp), %rdx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKj1e_E6extendB4_
	testb	%al, %al
	je	.LBB47_49
	movb	$1, %bl
	jmp	.LBB47_50
.LBB47_49:
	xorl	%ebx, %ebx
.LBB47_50:
	movl	%ebx, %eax
	addq	$1944, %rsp
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
.Lfunc_end47:
	.size	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr12verify_layer, .Lfunc_end47-_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr12verify_layer
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr13verify_keccak,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr13verify_keccak,@function
_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr13verify_keccak:
.Lfunc_begin48:
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
	subq	$3240, %rsp
	.cfi_def_cfa_offset 3296
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	%r9, (%rsp)
	movq	%r8, %r14
	movq	%rcx, %r15
	movq	%rsi, %rbx
	xorl	%r13d, %r13d
	movq	%rsi, 16(%rsp)
	subq	$4, %rbx
	cmovbq	%r13, %rbx
	movq	%rdi, %rbp
	movq	%rcx, %r12
	subq	$4, %r12
	movl	$4, %eax
	cmovbq	%rcx, %rax
	movq	%rax, 88(%rsp)
	cmovbq	%r13, %r12
	movq	%rdx, 24(%rsp)
	leaq	64(%rdx), %rax
	movl	$8, %ecx
	cmovaeq	%rax, %rcx
	movq	%rcx, 80(%rsp)
	movl	$5, %edi
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field10bit_length
	subl	$3, %eax
	cmovbl	%r13d, %eax
	movq	%rbp, %rdi
	movl	%eax, %esi
	callq	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState5grind
	testb	%al, %al
	je	.LBB48_32
	movq	$0, 96(%rsp)
	movq	$0, 104(%rsp)
	leaq	96(%rsp), %rsi
	movl	$1, %edx
	movq	%rbp, %rdi
	callq	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState17sample_challenges
	movq	$0, 272(%rsp)
	movq	$0, 280(%rsp)
	movq	$0, 288(%rsp)
	movq	$0, 296(%rsp)
	movq	$0, 304(%rsp)
	movq	$0, 312(%rsp)
	movq	$0, 320(%rsp)
	movq	$0, 328(%rsp)
	movq	$0, 336(%rsp)
	movq	$0, 344(%rsp)
	leaq	272(%rsp), %rsi
	movl	$5, %edx
	movq	%rbp, %rdi
	callq	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState17sample_challenges
	leaq	936(%rsp), %rdi
	movq	%rbp, %rsi
	callq	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState11read_scalar
	cmpl	$1, 936(%rsp)
	jne	.LBB48_31
	movq	944(%rsp), %r13
	movq	952(%rsp), %rax
	subq	$8, %rsp
	.cfi_adjust_cfa_offset 8
	leaq	944(%rsp), %rdi
	leaq	104(%rsp), %rcx
	leaq	280(%rsp), %r8
	movq	32(%rsp), %rsi
	movq	%r15, %rdx
	movq	%r14, %r9
	pushq	8(%rsp)
	.cfi_adjust_cfa_offset 8
	movq	%rax, 48(%rsp)
	pushq	%rax
	.cfi_adjust_cfa_offset 8
	pushq	%r13
	.cfi_adjust_cfa_offset 8
	callq	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr11first_claim
	addq	$32, %rsp
	.cfi_adjust_cfa_offset -32
	cmpb	$0, 936(%rsp)
	je	.LBB48_31
	movq	%r13, 72(%rsp)
	leaq	944(%rsp), %rsi
	leaq	2480(%rsp), %r14
	movq	%rbp, 8(%rsp)
	movq	memcpy@GOTPCREL(%rip), %r13
	movl	$280, %edx
	movq	%r14, %rdi
	callq	*%r13
	movq	1224(%rsp), %rbp
	leaq	1232(%rsp), %rsi
	leaq	2760(%rsp), %r15
	movl	$480, %edx
	movq	%r15, %rdi
	callq	*%r13
	leaq	1712(%rsp), %rdi
	movl	$280, %edx
	movq	%r14, %rsi
	callq	*%r13
	movq	%rbp, 1992(%rsp)
	leaq	2000(%rsp), %rdi
	movl	$480, %edx
	movq	%r15, %rsi
	callq	*%r13
	leaq	936(%rsp), %rdi
	movl	$280, %edx
	movq	%r14, %rsi
	callq	*%r13
	movq	%rbp, 64(%rsp)
	movq	%rbp, 1216(%rsp)
	leaq	1224(%rsp), %rdi
	movl	$480, %edx
	movq	%r15, %rsi
	callq	*%r13
	movq	(%rsp), %rax
	leaq	25600(%rax), %rbp
	movl	$25600, %edx
	movq	%rbp, %rdi
	movq	(%rsp), %rsi
	callq	*%r13
	movq	(%rsp), %r13
	movq	8(%rsp), %r14
	movq	%r14, %rdi
	movq	16(%rsp), %r15
	movq	%r15, %rsi
	xorl	%edx, %edx
	leaq	936(%rsp), %rcx
	movq	%r13, %r8
	callq	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr12verify_layer
	testb	%al, %al
	je	.LBB48_31
	leaq	936(%rsp), %rcx
	movl	$1, %edx
	movq	%r14, %rdi
	movq	%r15, %rsi
	movq	%r13, %r8
	callq	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr12verify_layer
	testb	%al, %al
	je	.LBB48_31
	leaq	936(%rsp), %rcx
	movl	$2, %edx
	movq	%r14, %rdi
	movq	%r15, %rsi
	movq	%r13, %r8
	callq	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr12verify_layer
	testb	%al, %al
	je	.LBB48_31
	leaq	936(%rsp), %rcx
	movl	$3, %edx
	movq	%r14, %rdi
	movq	%r15, %rsi
	movq	%r13, %r8
	callq	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr12verify_layer
	testb	%al, %al
	je	.LBB48_31
	leaq	936(%rsp), %rcx
	movl	$4, %edx
	movq	%r14, %rdi
	movq	%r15, %rsi
	movq	%r13, %r8
	callq	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr12verify_layer
	testb	%al, %al
	je	.LBB48_31
	leaq	936(%rsp), %rcx
	movl	$5, %edx
	movq	%r14, %rdi
	movq	%r15, %rsi
	movq	%r13, %r8
	callq	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr12verify_layer
	testb	%al, %al
	je	.LBB48_31
	leaq	936(%rsp), %rcx
	movl	$6, %edx
	movq	%r14, %rdi
	movq	%r15, %rsi
	movq	%r13, %r8
	callq	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr12verify_layer
	testb	%al, %al
	je	.LBB48_31
	leaq	936(%rsp), %rcx
	movl	$7, %edx
	movq	%r14, %rdi
	movq	%r15, %rsi
	movq	%r13, %r8
	callq	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr12verify_layer
	testb	%al, %al
	je	.LBB48_31
	leaq	936(%rsp), %rcx
	movl	$8, %edx
	movq	%r14, %rdi
	movq	%r15, %rsi
	movq	%r13, %r8
	callq	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr12verify_layer
	testb	%al, %al
	je	.LBB48_31
	leaq	936(%rsp), %rcx
	movl	$9, %edx
	movq	%r14, %rdi
	movq	%r15, %rsi
	movq	%r13, %r8
	callq	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr12verify_layer
	testb	%al, %al
	je	.LBB48_31
	leaq	936(%rsp), %rcx
	movl	$10, %edx
	movq	%r14, %rdi
	movq	%r15, %rsi
	movq	%r13, %r8
	callq	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr12verify_layer
	testb	%al, %al
	je	.LBB48_31
	leaq	936(%rsp), %rcx
	movl	$11, %edx
	movq	%r14, %rdi
	movq	%r15, %rsi
	movq	%r13, %r8
	callq	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr12verify_layer
	testb	%al, %al
	je	.LBB48_31
	movq	$0, 176(%rsp)
	movq	$0, 184(%rsp)
	movq	$0, 192(%rsp)
	movq	$0, 200(%rsp)
	movq	$0, 208(%rsp)
	movq	$0, 216(%rsp)
	movq	$0, 224(%rsp)
	movq	$0, 232(%rsp)
	movq	$0, 240(%rsp)
	movq	$0, 248(%rsp)
	movq	$0, 256(%rsp)
	xorl	%r8d, %r8d
	movq	64(%rsp), %rax
	cmpq	$31, %rax
	movl	$8, %ecx
	leaq	2000(%rsp), %rdx
	cmovbq	%rdx, %rcx
	movq	$0, 264(%rsp)
	cmovbq	%rax, %r8
	leaq	140288(%r13), %r10
	leaq	176(%rsp), %rax
	leaq	352(%rsp), %rdi
	movq	%r14, %rsi
	movq	%r15, %rdx
	movq	%r13, %r9
	movq	%r10, %r13
	pushq	%r10
	.cfi_adjust_cfa_offset 8
	pushq	%rax
	.cfi_adjust_cfa_offset 8
	pushq	48(%rsp)
	.cfi_adjust_cfa_offset 8
	pushq	96(%rsp)
	.cfi_adjust_cfa_offset 8
	pushq	$1
	.cfi_adjust_cfa_offset 8
	pushq	$1
	.cfi_adjust_cfa_offset 8
	callq	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr11keccak_open
	addq	$48, %rsp
	.cfi_adjust_cfa_offset -48
	cmpl	$1, 352(%rsp)
	jne	.LBB48_31
	movq	360(%rsp), %r15
	movq	368(%rsp), %r14
	leaq	352(%rsp), %rdi
	movq	8(%rsp), %rsi
	callq	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState11read_scalar
	cmpb	$0, 352(%rsp)
	je	.LBB48_31
	movq	360(%rsp), %rdx
	movq	368(%rsp), %rcx
	movq	(%rsp), %rax
	movq	140288(%rax), %rdi
	movq	140296(%rax), %rsi
	movq	%rdx, (%rsp)
	movq	%rcx, 32(%rsp)
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	cmpq	%r15, %rax
	jne	.LBB48_31
	cmpq	%r14, %rdx
	jne	.LBB48_31
	movq	$0, 360(%rsp)
	movq	$0, 368(%rsp)
	movq	$0, 376(%rsp)
	movq	$0, 384(%rsp)
	movq	$0, 392(%rsp)
	movq	$0, 400(%rsp)
	movq	$0, 408(%rsp)
	movq	$0, 416(%rsp)
	movq	$0, 424(%rsp)
	movq	$0, 432(%rsp)
	movq	$0, 440(%rsp)
	movq	$0, 448(%rsp)
	movq	$0, 456(%rsp)
	movq	$0, 464(%rsp)
	movq	$0, 472(%rsp)
	movq	$0, 480(%rsp)
	movq	$0, 488(%rsp)
	movq	$0, 496(%rsp)
	movq	$0, 504(%rsp)
	movq	$0, 512(%rsp)
	movq	$0, 520(%rsp)
	movq	$0, 528(%rsp)
	movq	$0, 536(%rsp)
	movq	$0, 544(%rsp)
	movq	$0, 552(%rsp)
	movq	$0, 560(%rsp)
	movq	$0, 568(%rsp)
	movq	$0, 576(%rsp)
	movq	$0, 584(%rsp)
	movq	$0, 592(%rsp)
	movq	$0, 600(%rsp)
	movq	$0, 608(%rsp)
	movq	$0, 616(%rsp)
	movq	$0, 624(%rsp)
	movq	$0, 632(%rsp)
	movq	$0, 640(%rsp)
	movq	$0, 648(%rsp)
	movq	$0, 656(%rsp)
	movq	$0, 664(%rsp)
	movq	$0, 672(%rsp)
	movq	$0, 680(%rsp)
	movq	$0, 688(%rsp)
	movq	$0, 696(%rsp)
	movq	$0, 704(%rsp)
	movq	$0, 712(%rsp)
	movq	$0, 720(%rsp)
	movq	$0, 728(%rsp)
	movq	$0, 736(%rsp)
	movq	$0, 744(%rsp)
	movq	$0, 752(%rsp)
	movq	$0, 760(%rsp)
	movq	$0, 768(%rsp)
	movq	$0, 776(%rsp)
	movq	$0, 784(%rsp)
	movq	$0, 792(%rsp)
	movq	$0, 800(%rsp)
	movq	$0, 808(%rsp)
	movq	$0, 816(%rsp)
	movq	$0, 824(%rsp)
	movq	$0, 832(%rsp)
	movq	$0, 840(%rsp)
	movq	$0, 848(%rsp)
	movq	$0, 856(%rsp)
	movq	$0, 864(%rsp)
	movq	$0, 872(%rsp)
	movq	$0, 880(%rsp)
	movq	$0, 888(%rsp)
	movq	$0, 896(%rsp)
	movq	$0, 904(%rsp)
	movq	$0, 912(%rsp)
	movq	$0, 920(%rsp)
	movq	$0, 928(%rsp)
	movq	$0, 352(%rsp)
	leaq	352(%rsp), %rdi
	movq	24(%rsp), %rsi
	movq	88(%rsp), %rdx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKj24_E6extendB4_
	testb	%al, %al
	je	.LBB48_31
	leaq	352(%rsp), %rdi
	movq	80(%rsp), %rsi
	movq	%r12, %rdx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKj24_E6extendB4_
	testb	%al, %al
	je	.LBB48_31
	leaq	352(%rsp), %rdi
	leaq	176(%rsp), %r12
	movl	$6, %edx
	movq	%r12, %rsi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKj24_E6extendB4_
	testb	%al, %al
	je	.LBB48_31
	movq	3296(%rsp), %rdi
	leaq	360(%rsp), %rax
	movq	352(%rsp), %rsi
	xorl	%ecx, %ecx
	cmpq	$37, %rsi
	movl	$8, %edx
	cmovbq	%rax, %rdx
	cmovbq	%rsi, %rcx
	movl	$4, %esi
	movq	(%rsp), %r8
	movq	32(%rsp), %r9
	callq	_RNvNtCsemcRClSg8DH_9native_vm5stack10push_claim
	testb	%al, %al
	je	.LBB48_31
	movq	$0, 112(%rsp)
	movq	$0, 120(%rsp)
	movq	$0, 128(%rsp)
	movq	$0, 136(%rsp)
	movq	$0, 144(%rsp)
	movq	$0, 152(%rsp)
	movq	$0, 160(%rsp)
	movq	$0, 168(%rsp)
	movq	936(%rsp), %rdx
	movq	944(%rsp), %rcx
	subq	$8, %rsp
	.cfi_adjust_cfa_offset 8
	leaq	48(%rsp), %rdi
	leaq	120(%rsp), %r9
	movl	$3, %r8d
	movq	16(%rsp), %rsi
	pushq	$4
	.cfi_adjust_cfa_offset 8
	callq	_RINvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB6_6TState8sumcheckNCNvB2_14sumcheck_plain0EB8_
	addq	$16, %rsp
	.cfi_adjust_cfa_offset -16
	cmpl	$1, 40(%rsp)
	jne	.LBB48_31
	movq	1216(%rsp), %rax
	xorl	%r14d, %r14d
	cmpq	$31, %rax
	movl	$8, %r15d
	leaq	1224(%rsp), %rcx
	cmovbq	%rcx, %r15
	cmovbq	%rax, %r14
	leaq	40(%rsp), %rdi
	movq	8(%rsp), %rsi
	movq	16(%rsp), %rdx
	movq	%r15, %rcx
	movq	%r14, %r8
	movq	%rbp, %r9
	pushq	%r13
	.cfi_adjust_cfa_offset 8
	pushq	%r12
	.cfi_adjust_cfa_offset 8
	pushq	72(%rsp)
	.cfi_adjust_cfa_offset 8
	pushq	72(%rsp)
	.cfi_adjust_cfa_offset 8
	pushq	$2
	.cfi_adjust_cfa_offset 8
	pushq	$0
	.cfi_adjust_cfa_offset 8
	callq	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr11keccak_open
	addq	$48, %rsp
	.cfi_adjust_cfa_offset -48
	cmpb	$0, 40(%rsp)
	je	.LBB48_31
	movq	3304(%rsp), %rax
	movq	48(%rsp), %rcx
	movq	%rcx, (%rsp)
	movq	56(%rsp), %rcx
	movq	%rcx, 16(%rsp)
	leaq	584(%rax), %rsi
	movl	$64, %edx
	movq	8(%rsp), %rdi
	movq	%rsi, 24(%rsp)
	callq	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState12read_scalars
	testb	%al, %al
	je	.LBB48_31
	movq	952(%rsp), %rax
	xorl	%edi, %edi
	cmpq	$17, %rax
	leaq	960(%rsp), %rcx
	movl	$8, %esi
	cmovbq	%rcx, %rsi
	cmovbq	%rax, %rdi
	leaq	112(%rsp), %rcx
	movl	$4, %r8d
	movq	%rdi, %rdx
	callq	_RINvNtCsemcRClSg8DH_9native_vm5field19multilinear_eval_byNCNvB2_16multilinear_eval0EB4_
	movq	%rax, %r12
	movq	%rdx, %rbp
	movl	$64, %esi
	movl	$64, %ecx
	movq	%r13, %rdi
	movq	24(%rsp), %rdx
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field3dot
	movq	%rdx, %rcx
	movq	%r12, %rdi
	movq	%rbp, %rsi
	movq	%rax, %rdx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	cmpq	(%rsp), %rax
	jne	.LBB48_31
	cmpq	16(%rsp), %rdx
	jne	.LBB48_31
	movq	3304(%rsp), %rdi
	movq	$0, (%rdi)
	leaq	112(%rsp), %rsi
	movl	$4, %edx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKj24_E6extendB4_
	testb	%al, %al
	je	.LBB48_31
	cmpq	%r14, %rbx
	cmovbq	%rbx, %r14
	movq	3304(%rsp), %rdi
	movq	%r15, %rsi
	movq	%r14, %rdx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKj24_E6extendB4_
	testb	%al, %al
	je	.LBB48_31
	leaq	176(%rsp), %rsi
	movl	$6, %edx
	movq	3304(%rsp), %rdi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKj24_E6extendB4_
	movl	%eax, %r13d
	jmp	.LBB48_32
.LBB48_31:
	xorl	%r13d, %r13d
.LBB48_32:
	movl	%r13d, %eax
	addq	$3240, %rsp
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
.Lfunc_end48:
	.size	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr13verify_keccak, .Lfunc_end48-_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr13verify_keccak
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr16instance_weights,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr16instance_weights,@function
_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr16instance_weights:
.Lfunc_begin49:
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
	subq	$984, %rsp
	.cfi_def_cfa_offset 1040
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	%rdi, 496(%rsp)
	movq	$0, 96(%rsp)
	movq	$0, 104(%rsp)
	movq	$0, 112(%rsp)
	movq	$0, 120(%rsp)
	movq	$0, 128(%rsp)
	movq	$0, 136(%rsp)
	movq	$0, 144(%rsp)
	movq	$0, 152(%rsp)
	movq	$0, 160(%rsp)
	movq	$0, 168(%rsp)
	movq	$0, 176(%rsp)
	movq	$0, 184(%rsp)
	movq	$0, 192(%rsp)
	movq	$0, 200(%rsp)
	movq	$0, 208(%rsp)
	movq	$0, 216(%rsp)
	movq	$0, 224(%rsp)
	movq	$0, 232(%rsp)
	movq	$0, 240(%rsp)
	movq	$0, 248(%rsp)
	movq	$0, 256(%rsp)
	movq	$0, 264(%rsp)
	movq	$0, 272(%rsp)
	movq	$0, 280(%rsp)
	movq	$0, 288(%rsp)
	movq	$0, 296(%rsp)
	movq	$0, 304(%rsp)
	movq	$0, 312(%rsp)
	movq	$0, 320(%rsp)
	movq	$0, 328(%rsp)
	movq	$0, 336(%rsp)
	movq	$0, 344(%rsp)
	movq	$0, 352(%rsp)
	movq	$0, 360(%rsp)
	movq	$0, 368(%rsp)
	movq	$0, 376(%rsp)
	movq	$0, 384(%rsp)
	movq	$0, 392(%rsp)
	movq	$0, 400(%rsp)
	movq	$0, 408(%rsp)
	movq	$0, 416(%rsp)
	movq	$0, 424(%rsp)
	movq	$0, 432(%rsp)
	movq	$0, 440(%rsp)
	movq	$0, 448(%rsp)
	movq	$0, 456(%rsp)
	movq	$0, 464(%rsp)
	movq	$0, 472(%rsp)
	leaq	96(%rsp), %rax
	movl	$24, %ecx
	movq	%rsi, %rdi
	movq	%rdx, %rsi
	movq	%rax, %rdx
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field6powers
	movq	$16, 720(%rsp)
	movq	$0, 728(%rsp)
	movq	$0, 736(%rsp)
	movq	$0, 744(%rsp)
	movq	$0, 752(%rsp)
	movq	$0, 760(%rsp)
	movq	$0, 768(%rsp)
	movq	$0, 776(%rsp)
	movq	$0, 784(%rsp)
	movq	$0, 792(%rsp)
	movq	$0, 800(%rsp)
	movq	$0, 808(%rsp)
	movq	$0, 816(%rsp)
	movq	$0, 824(%rsp)
	movq	$0, 832(%rsp)
	movq	$0, 840(%rsp)
	movq	$0, 848(%rsp)
	movq	$0, 856(%rsp)
	movq	$0, 864(%rsp)
	movq	$0, 872(%rsp)
	movq	$0, 880(%rsp)
	movq	$0, 888(%rsp)
	movq	$0, 896(%rsp)
	movq	$0, 904(%rsp)
	movq	$0, 912(%rsp)
	movq	$0, 920(%rsp)
	movq	$0, 928(%rsp)
	movq	$0, 936(%rsp)
	movq	$0, 944(%rsp)
	movq	$0, 952(%rsp)
	movq	$0, 960(%rsp)
	movq	$0, 968(%rsp)
	movq	$0, 976(%rsp)
	movq	112(%rsp), %rdx
	movq	120(%rsp), %rcx
	movq	144(%rsp), %rdi
	movq	152(%rsp), %r8
	movq	224(%rsp), %r9
	movq	232(%rsp), %r10
	movq	256(%rsp), %rbx
	movq	264(%rsp), %r14
	movq	320(%rsp), %r15
	movq	328(%rsp), %r12
	movq	336(%rsp), %rsi
	movq	344(%rsp), %r11
	movq	104(%rsp), %rax
	movq	%rcx, 80(%rsp)
	xorq	%rcx, %rax
	movq	96(%rsp), %rcx
	movq	%rdx, 88(%rsp)
	xorq	%rdx, %rcx
	movq	%r8, 704(%rsp)
	movq	%r8, %rdx
	movq	%r10, 688(%rsp)
	xorq	%r10, %rdx
	xorq	%rax, %rdx
	movq	%rdi, 712(%rsp)
	movq	%rdi, %rax
	movq	%r9, 696(%rsp)
	xorq	%r9, %rax
	xorq	%rcx, %rax
	movq	%r14, 672(%rsp)
	movq	%r14, %rcx
	movq	%r12, 656(%rsp)
	xorq	%r12, %rcx
	movq	%r11, 64(%rsp)
	xorq	%r11, %rcx
	xorq	%rdx, %rcx
	movq	%rbx, 680(%rsp)
	movq	%rbx, %rdx
	movq	%r15, 664(%rsp)
	xorq	%r15, %rdx
	movq	%rsi, 72(%rsp)
	xorq	%rsi, %rdx
	xorq	%rax, %rdx
	movq	448(%rsp), %rax
	movq	%rax, 648(%rsp)
	xorq	%rax, %rdx
	movq	%rdx, 728(%rsp)
	movq	456(%rsp), %rax
	movq	%rax, 640(%rsp)
	xorq	%rax, %rcx
	movq	%rcx, 736(%rsp)
	leaq	752(%rsp), %r9
	movq	128(%rsp), %rbp
	movq	136(%rsp), %r13
	movq	160(%rsp), %rax
	movq	%rax, 56(%rsp)
	movq	168(%rsp), %rax
	movq	%rax, 24(%rsp)
	movq	176(%rsp), %rax
	movq	%rax, 632(%rsp)
	movq	184(%rsp), %rax
	movq	%rax, 624(%rsp)
	movq	192(%rsp), %rax
	movq	%rax, 616(%rsp)
	movq	200(%rsp), %rax
	movq	%rax, 608(%rsp)
	movq	208(%rsp), %rax
	movq	%rax, 600(%rsp)
	movq	216(%rsp), %rax
	movq	%rax, 592(%rsp)
	movq	240(%rsp), %rax
	movq	%rax, 48(%rsp)
	movq	248(%rsp), %rax
	movq	%rax, 16(%rsp)
	movq	272(%rsp), %rax
	movq	%rax, 40(%rsp)
	movq	280(%rsp), %rax
	movq	%rax, 8(%rsp)
	movq	288(%rsp), %rax
	movq	%rax, 584(%rsp)
	movq	296(%rsp), %rax
	movq	%rax, 576(%rsp)
	movq	304(%rsp), %rax
	movq	%rax, 568(%rsp)
	movq	312(%rsp), %rax
	movq	%rax, 560(%rsp)
	movq	352(%rsp), %rax
	movq	%rax, 32(%rsp)
	movq	360(%rsp), %rax
	movq	%rax, (%rsp)
	movq	368(%rsp), %rax
	movq	%rax, 552(%rsp)
	movq	376(%rsp), %rax
	movq	%rax, 544(%rsp)
	movq	384(%rsp), %rax
	movq	%rax, 536(%rsp)
	movq	392(%rsp), %rax
	movq	%rax, 528(%rsp)
	movq	400(%rsp), %rax
	movq	%rax, 520(%rsp)
	movq	408(%rsp), %rax
	movq	%rax, 512(%rsp)
	movq	416(%rsp), %rax
	movq	%rax, 504(%rsp)
	movq	424(%rsp), %r12
	movq	432(%rsp), %rdi
	movq	440(%rsp), %r15
	movq	464(%rsp), %rax
	movq	%rax, 488(%rsp)
	movq	472(%rsp), %rax
	movq	%rax, 480(%rsp)
	movl	$1, %edx
	.p2align	4
.LBB49_1:
	movl	$15624, %eax
	btq	%rdx, %rax
	movl	$0, %eax
	cmovaeq	80(%rsp), %rax
	movl	$0, %r8d
	cmovaeq	88(%rsp), %r8
	movl	$12311, %ecx
	btq	%rdx, %rcx
	movl	$0, %r10d
	movl	$0, %esi
	cmovaeq	%r13, %r10
	cmovaeq	%rbp, %rsi
	xorq	%rax, %r10
	xorq	%r8, %rsi
	movl	$58498, %eax
	btq	%rdx, %rax
	movl	$0, %r8d
	cmovaeq	704(%rsp), %r8
	movl	$0, %ecx
	cmovaeq	712(%rsp), %rcx
	movl	$20685, %eax
	btq	%rdx, %rax
	movl	$0, %ebx
	cmovaeq	24(%rsp), %rbx
	movl	$0, %eax
	cmovaeq	56(%rsp), %rax
	xorq	%r8, %rbx
	xorq	%r10, %rbx
	xorq	%rcx, %rax
	xorq	%rsi, %rax
	movl	$54717, %ecx
	btq	%rdx, %rcx
	movl	$0, %ecx
	cmovaeq	624(%rsp), %rcx
	movl	$0, %esi
	cmovaeq	632(%rsp), %rsi
	movl	$49197, %r8d
	btq	%rdx, %r8
	movl	$0, %r11d
	movl	$0, %r14d
	cmovaeq	608(%rsp), %r11
	cmovaeq	616(%rsp), %r14
	xorq	%rcx, %r11
	xorq	%rsi, %r14
	movl	$42701, %ecx
	btq	%rdx, %rcx
	movl	$0, %r10d
	cmovaeq	592(%rsp), %r10
	movl	$0, %r8d
	cmovaeq	600(%rsp), %r8
	xorq	%r11, %r10
	xorq	%rbx, %r10
	xorq	%r14, %r8
	xorq	%rax, %r8
	movl	$40940, %eax
	btq	%rdx, %rax
	movl	$0, %eax
	cmovaeq	688(%rsp), %rax
	movl	$0, %ecx
	cmovaeq	696(%rsp), %rcx
	movl	$7467, %esi
	btq	%rdx, %rsi
	movl	$0, %esi
	cmovaeq	16(%rsp), %rsi
	movl	$0, %r11d
	cmovaeq	48(%rsp), %r11
	xorq	%rax, %rsi
	xorq	%rcx, %r11
	movl	$49282, %eax
	btq	%rdx, %rax
	movl	$0, %ecx
	movl	$0, %r14d
	cmovaeq	672(%rsp), %rcx
	cmovaeq	680(%rsp), %r14
	xorq	%rsi, %rcx
	xorq	%r11, %r14
	movl	$25753, %eax
	btq	%rdx, %rax
	movl	$0, %eax
	cmovaeq	8(%rsp), %rax
	movl	$0, %ebx
	cmovaeq	40(%rsp), %rbx
	xorq	%rcx, %rax
	xorq	%r10, %rax
	xorq	%r14, %rbx
	xorq	%r8, %rbx
	movl	$32773, %ecx
	btq	%rdx, %rcx
	movl	$0, %ecx
	cmovaeq	576(%rsp), %rcx
	movl	$0, %esi
	cmovaeq	584(%rsp), %rsi
	movl	$42677, %r8d
	btq	%rdx, %r8
	movl	$0, %r8d
	movl	$0, %r10d
	cmovaeq	560(%rsp), %r8
	cmovaeq	568(%rsp), %r10
	xorq	%rcx, %r8
	xorq	%rsi, %r10
	movl	$36448, %ecx
	btq	%rdx, %rcx
	movl	$0, %ecx
	cmovaeq	656(%rsp), %rcx
	movl	$0, %esi
	cmovaeq	664(%rsp), %rsi
	xorq	%r8, %rcx
	xorq	%r10, %rsi
	movl	$28094, %r8d
	btq	%rdx, %r8
	movl	$0, %r11d
	movl	$0, %r14d
	cmovaeq	64(%rsp), %r11
	cmovaeq	72(%rsp), %r14
	xorq	%rcx, %r11
	xorq	%rsi, %r14
	movl	$21193, %ecx
	btq	%rdx, %rcx
	movl	$0, %r8d
	cmovaeq	(%rsp), %r8
	movl	$0, %r10d
	cmovaeq	32(%rsp), %r10
	xorq	%r11, %r8
	xorq	%rax, %r8
	xorq	%r14, %r10
	xorq	%rbx, %r10
	movl	$56289, %eax
	btq	%rdx, %rax
	movl	$0, %eax
	cmovaeq	544(%rsp), %rax
	movl	$0, %ecx
	cmovaeq	552(%rsp), %rcx
	movl	$52125, %esi
	btq	%rdx, %rsi
	movl	$0, %esi
	cmovaeq	528(%rsp), %rsi
	movl	$0, %r11d
	cmovaeq	536(%rsp), %r11
	xorq	%rax, %rsi
	xorq	%rcx, %r11
	movl	$43609, %eax
	btq	%rdx, %rax
	movl	$0, %eax
	movl	$0, %ecx
	cmovaeq	512(%rsp), %rax
	cmovaeq	520(%rsp), %rcx
	xorq	%rsi, %rax
	xorq	%r11, %rcx
	movl	$39237, %esi
	btq	%rdx, %rsi
	movl	$0, %esi
	cmovaeq	%r12, %rsi
	movl	$0, %r11d
	cmovaeq	504(%rsp), %r11
	xorq	%rax, %rsi
	xorq	%rcx, %r11
	movl	$55157, %eax
	btq	%rdx, %rax
	movl	$0, %eax
	movl	$0, %ecx
	cmovaeq	%r15, %rax
	cmovaeq	%rdi, %rcx
	xorq	%rsi, %rax
	xorq	%r11, %rcx
	movl	$53088, %esi
	btq	%rdx, %rsi
	movl	$0, %esi
	cmovaeq	640(%rsp), %rsi
	movl	$0, %r11d
	cmovaeq	648(%rsp), %r11
	xorq	%rax, %rsi
	xorq	%r8, %rsi
	xorq	%rcx, %r11
	xorq	%r10, %r11
	movq	%r11, -8(%r9)
	movq	%rsi, (%r9)
	incq	%rdx
	addq	$16, %r9
	cmpq	$15, %rdx
	jne	.LBB49_1
	xorq	480(%rsp), %r13
	xorq	80(%rsp), %r13
	xorq	24(%rsp), %r13
	xorq	16(%rsp), %r13
	xorq	8(%rsp), %r13
	xorq	64(%rsp), %r13
	xorq	(%rsp), %r13
	xorq	488(%rsp), %rbp
	xorq	88(%rsp), %rbp
	xorq	56(%rsp), %rbp
	xorq	48(%rsp), %rbp
	xorq	40(%rsp), %rbp
	xorq	72(%rsp), %rbp
	xorq	32(%rsp), %rbp
	movq	%rbp, 968(%rsp)
	movq	%r13, 976(%rsp)
	leaq	720(%rsp), %rsi
	movl	$264, %edx
	movq	496(%rsp), %rdi
	callq	*memcpy@GOTPCREL(%rip)
	addq	$984, %rsp
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
.Lfunc_end49:
	.size	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr16instance_weights, .Lfunc_end49-_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr16instance_weights
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr16linear_transpose,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr16linear_transpose,@function
_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr16linear_transpose:
.Lfunc_begin50:
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
	pushq	%rax
	.cfi_def_cfa_offset 64
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	%rcx, %rbx
	movq	%rdx, %r14
	movq	%rsi, %r15
	movq	%rdi, %r12
	leaq	24(%rsi), %rbp
	xorl	%r13d, %r13d
	.p2align	4
.LBB50_1:
	movq	%r13, %rdi
	callq	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr9keccak_pi
	leaq	.Lanon.a75d6d9e6a8990b4224ef13f18552af8.2(%rip), %rcx
	movl	(%rcx,%r13,4), %ecx
	shll	$10, %eax
	addq	%r12, %rax
	xorl	%edx, %edx
	.p2align	4
.LBB50_2:
	movl	%ecx, %esi
	andl	$63, %esi
	shll	$4, %esi
	movq	(%rax,%rsi), %rdi
	movq	8(%rax,%rsi), %rsi
	movq	%rdi, -24(%rbp,%rdx)
	movq	%rsi, -16(%rbp,%rdx)
	leal	1(%rcx), %esi
	andl	$63, %esi
	shll	$4, %esi
	movq	(%rax,%rsi), %rdi
	movq	8(%rax,%rsi), %rsi
	movq	%rdi, -8(%rbp,%rdx)
	movq	%rsi, (%rbp,%rdx)
	addq	$32, %rdx
	addq	$2, %rcx
	cmpq	$1024, %rdx
	jne	.LBB50_2
	incq	%r13
	addq	$1024, %rbp
	cmpq	$25, %r13
	jne	.LBB50_1
	xorl	%eax, %eax
	.p2align	4
.LBB50_5:
	movq	5120(%r15,%rax), %rcx
	movq	5128(%r15,%rax), %rdx
	xorq	(%r15,%rax), %rcx
	xorq	8(%r15,%rax), %rdx
	xorq	10240(%r15,%rax), %rcx
	xorq	10248(%r15,%rax), %rdx
	xorq	15360(%r15,%rax), %rcx
	xorq	15368(%r15,%rax), %rdx
	xorq	20480(%r15,%rax), %rcx
	xorq	20488(%r15,%rax), %rdx
	movq	%rcx, (%r14,%rax)
	movq	%rdx, 8(%r14,%rax)
	addq	$16, %rax
	cmpq	$1024, %rax
	jne	.LBB50_5
	xorl	%eax, %eax
	.p2align	4
.LBB50_7:
	movq	6144(%r15,%rax), %rcx
	movq	6152(%r15,%rax), %rdx
	xorq	1024(%r15,%rax), %rcx
	xorq	1032(%r15,%rax), %rdx
	xorq	11264(%r15,%rax), %rcx
	xorq	11272(%r15,%rax), %rdx
	xorq	16384(%r15,%rax), %rcx
	xorq	16392(%r15,%rax), %rdx
	xorq	21504(%r15,%rax), %rcx
	xorq	21512(%r15,%rax), %rdx
	movq	%rcx, 1024(%r14,%rax)
	movq	%rdx, 1032(%r14,%rax)
	addq	$16, %rax
	cmpq	$1024, %rax
	jne	.LBB50_7
	xorl	%eax, %eax
	.p2align	4
.LBB50_9:
	movq	7168(%r15,%rax), %rcx
	movq	7176(%r15,%rax), %rdx
	xorq	2048(%r15,%rax), %rcx
	xorq	2056(%r15,%rax), %rdx
	xorq	12288(%r15,%rax), %rcx
	xorq	12296(%r15,%rax), %rdx
	xorq	17408(%r15,%rax), %rcx
	xorq	17416(%r15,%rax), %rdx
	xorq	22528(%r15,%rax), %rcx
	xorq	22536(%r15,%rax), %rdx
	movq	%rcx, 2048(%r14,%rax)
	movq	%rdx, 2056(%r14,%rax)
	addq	$16, %rax
	cmpq	$1024, %rax
	jne	.LBB50_9
	xorl	%eax, %eax
	.p2align	4
.LBB50_11:
	movq	8192(%r15,%rax), %rcx
	movq	8200(%r15,%rax), %rdx
	xorq	3072(%r15,%rax), %rcx
	xorq	3080(%r15,%rax), %rdx
	xorq	13312(%r15,%rax), %rcx
	xorq	13320(%r15,%rax), %rdx
	xorq	18432(%r15,%rax), %rcx
	xorq	18440(%r15,%rax), %rdx
	xorq	23552(%r15,%rax), %rcx
	xorq	23560(%r15,%rax), %rdx
	movq	%rcx, 3072(%r14,%rax)
	movq	%rdx, 3080(%r14,%rax)
	addq	$16, %rax
	cmpq	$1024, %rax
	jne	.LBB50_11
	xorl	%eax, %eax
	.p2align	4
.LBB50_13:
	movq	9216(%r15,%rax), %rcx
	movq	9224(%r15,%rax), %rdx
	xorq	4096(%r15,%rax), %rcx
	xorq	4104(%r15,%rax), %rdx
	xorq	14336(%r15,%rax), %rcx
	xorq	14344(%r15,%rax), %rdx
	xorq	19456(%r15,%rax), %rcx
	xorq	19464(%r15,%rax), %rdx
	xorq	24576(%r15,%rax), %rcx
	xorq	24584(%r15,%rax), %rdx
	movq	%rcx, 4096(%r14,%rax)
	movq	%rdx, 4104(%r14,%rax)
	addq	$16, %rax
	cmpq	$1024, %rax
	jne	.LBB50_13
	leaq	8(%r14), %rsi
	addq	$8, %rbx
	addq	$8, %r15
	xorl	%edi, %edi
	movabsq	$-3689348814741910323, %r8
	movl	$4096, %r9d
	xorl	%ecx, %ecx
	.p2align	4
.LBB50_16:
	movq	%rcx, %rax
	mulq	%r8
	shrq	$2, %rdx
	leaq	(%rdx,%rdx,4), %rax
	movq	%rcx, %r10
	subq	%rax, %r10
	negq	%rax
	leaq	(%rcx,%rax), %r11
	incq	%r11
	movl	%r11d, %eax
	shll	$6, %eax
	movl	%r10d, %edx
	shll	$10, %edx
	addq	$-1024, %rdx
	testq	%r10, %r10
	cmoveq	%r9, %rdx
	addq	%r14, %rdx
	cmpq	$5, %r11
	cmovel	%edi, %eax
	shll	$4, %eax
	addq	%rsi, %rax
	movl	$1, %r10d
	xorl	%r11d, %r11d
	.p2align	4
.LBB50_17:
	movq	(%rax,%r11), %r12
	xorq	(%r15,%r11), %r12
	movq	-8(%rax,%r11), %r13
	movl	%r10d, %ebp
	andl	$63, %ebp
	shll	$4, %ebp
	xorq	8(%rdx,%rbp), %r12
	xorq	-8(%r15,%r11), %r13
	xorq	(%rdx,%rbp), %r13
	movq	%r13, -8(%rbx,%r11)
	movq	%r12, (%rbx,%r11)
	addq	$16, %r11
	incq	%r10
	cmpq	$1024, %r11
	jne	.LBB50_17
	incq	%rcx
	addq	$1024, %rbx
	addq	$1024, %r15
	cmpq	$25, %rcx
	jne	.LBB50_16
	addq	$8, %rsp
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
.Lfunc_end50:
	.size	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr16linear_transpose, .Lfunc_end50-_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr16linear_transpose
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr9keccak_pi,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr9keccak_pi,@function
_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr9keccak_pi:
.Lfunc_begin51:
	.cfi_startproc
	imull	$205, %edi, %eax
	movzwl	%ax, %esi
	shrl	$10, %esi
	movl	%esi, %eax
	shll	$3, %eax
	movq	%rsi, %rcx
	subq	%rax, %rcx
	leaq	(%rcx,%rdi,2), %rcx
	movabsq	$-3689348814741910323, %rdx
	movq	%rcx, %rax
	mulq	%rdx
	shrq	$2, %rdx
	leaq	(%rdx,%rdx,4), %rax
	subq	%rax, %rcx
	leaq	(%rcx,%rcx,4), %rax
	addq	%rsi, %rax
	retq
.Lfunc_end51:
	.size	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr9keccak_pi, .Lfunc_end51-_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr9keccak_pi
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm10transcript10open_phase,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm10transcript10open_phase,@function
_RNvNtCsemcRClSg8DH_9native_vm10transcript10open_phase:
.Lfunc_begin52:
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
	subq	$120, %rsp
	.cfi_def_cfa_offset 176
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	176(%rsp), %r15
	movq	(%r15), %r13
	movq	8(%r15), %r10
	movq	16(%r15), %r14
	testq	%r13, %r13
	je	.LBB52_1
	cmpq	%rcx, %r14
	jne	.LBB52_16
	xorq	%r10, %rdx
	movq	%r13, %rax
	xorq	%r9, %rax
	orq	%rdx, %rax
	je	.LBB52_2
	jmp	.LBB52_16
.LBB52_1:
	testq	%r9, %r9
	jne	.LBB52_16
.LBB52_2:
	leaq	24(%r15), %rbp
	imulq	$1544, %r9, %rax
	xorl	%ecx, %ecx
	.p2align	4
.LBB52_3:
	cmpq	%rcx, %rax
	je	.LBB52_4
	movq	(%rbp,%rcx), %rdx
	addq	$1544, %rcx
	cmpq	(%r8), %rdx
	leaq	8(%r8), %r8
	je	.LBB52_3
.LBB52_16:
	movq	$0, (%rdi)
.LBB52_17:
	addq	$120, %rsp
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
.LBB52_4:
	.cfi_def_cfa_offset 176
	movq	%rdi, 8(%rsp)
	movq	%r10, 48(%rsp)
	testq	%r13, %r13
	je	.LBB52_13
	cmpq	$192, %r14
	ja	.LBB52_19
	movq	(%rsi), %rax
	movq	%rax, 40(%rsp)
	movq	8(%rsi), %rax
	movq	%rax, 32(%rsp)
	movq	16(%rsi), %rax
	movq	%rax, 24(%rsp)
	movq	24(%rsi), %rax
	movq	%rax, 16(%rsp)
	addq	$544, %r15
	xorl	%r12d, %r12d
	.p2align	4
.LBB52_7:
	cmpq	$256, %r12
	je	.LBB52_19
	leaq	-512(%r15), %rcx
	leaq	88(%rsp), %rbx
	movq	%rbx, %rdi
	movq	%r14, %rsi
	leaq	(,%r14,8), %rdx
	movq	%r14, %r8
	callq	_RINvNtCsemcRClSg8DH_9native_vm6keccak15keccak256_wordsNCNvB2_10hash_words0EB4_
	movq	-520(%r15), %rdx
	leaq	56(%rsp), %rdi
	movq	%rbx, %rsi
	movq	%r15, %rcx
	movq	48(%rsp), %r8
	callq	_RNvNtCsemcRClSg8DH_9native_vm10transcript5climb
	movq	40(%rsp), %rax
	cmpq	%rax, 56(%rsp)
	jne	.LBB52_19
	movq	32(%rsp), %rax
	cmpq	%rax, 64(%rsp)
	jne	.LBB52_19
	movq	24(%rsp), %rax
	cmpq	%rax, 72(%rsp)
	jne	.LBB52_19
	movq	16(%rsp), %rax
	cmpq	%rax, 80(%rsp)
	jne	.LBB52_19
	incq	%r12
	addq	$1544, %r15
	cmpq	%r12, %r13
	jne	.LBB52_7
.LBB52_13:
	movq	8(%rsp), %rax
	movq	%rbp, (%rax)
	movq	$49408, 8(%rax)
	movq	%r13, 16(%rax)
	movq	%r14, 24(%rax)
	jmp	.LBB52_17
.LBB52_19:
	movq	8(%rsp), %rax
	movq	$0, (%rax)
	jmp	.LBB52_17
.Lfunc_end52:
	.size	_RNvNtCsemcRClSg8DH_9native_vm10transcript10open_phase, .Lfunc_end52-_RNvNtCsemcRClSg8DH_9native_vm10transcript10open_phase
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm10transcript5climb,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm10transcript5climb,@function
_RNvNtCsemcRClSg8DH_9native_vm10transcript5climb:
.Lfunc_begin53:
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
	subq	$104, %rsp
	.cfi_def_cfa_offset 160
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	%rcx, %r15
	movq	%rdi, 64(%rsp)
	movq	24(%rsi), %rax
	movq	%rax, 24(%rsp)
	movq	16(%rsi), %rax
	movq	%rax, 16(%rsp)
	movq	(%rsi), %rax
	movq	8(%rsi), %rcx
	movq	%rcx, 8(%rsp)
	movq	%rax, (%rsp)
	testq	%r8, %r8
	je	.LBB53_9
	movq	%r8, %r14
	movq	%rdx, %r12
	xorl	%r13d, %r13d
	movq	%rsp, %rbp
	leaq	32(%rsp), %rbx
	jmp	.LBB53_2
	.p2align	4
.LBB53_6:
	movq	%rbp, %rsi
	movq	%rbx, %rdx
.LBB53_8:
	callq	_RNvNtCsemcRClSg8DH_9native_vm6keccak9hash_pair
	movq	96(%rsp), %rax
	movq	%rax, 24(%rsp)
	movq	88(%rsp), %rax
	movq	%rax, 16(%rsp)
	movq	72(%rsp), %rax
	movq	80(%rsp), %rcx
	movq	%rcx, 8(%rsp)
	movq	%rax, (%rsp)
	shrq	%r12
	addq	$4, %r13
	decq	%r14
	je	.LBB53_9
.LBB53_2:
	cmpq	$124, %r13
	ja	.LBB53_4
	movq	(%r15,%r13,8), %rax
	movq	8(%r15,%r13,8), %rcx
	movq	16(%r15,%r13,8), %rdx
	movq	24(%r15,%r13,8), %rsi
	movq	%rax, 32(%rsp)
	movq	%rcx, 40(%rsp)
	movq	%rdx, 48(%rsp)
	movq	%rsi, 56(%rsp)
	leaq	72(%rsp), %rdi
	testb	$1, %r12b
	je	.LBB53_6
	jmp	.LBB53_7
	.p2align	4
.LBB53_4:
	movq	$0, 56(%rsp)
	movq	$0, 48(%rsp)
	movq	$0, 40(%rsp)
	movq	$0, 32(%rsp)
	leaq	72(%rsp), %rdi
	testb	$1, %r12b
	je	.LBB53_6
.LBB53_7:
	movq	%rbx, %rsi
	movq	%rbp, %rdx
	jmp	.LBB53_8
.LBB53_9:
	movq	24(%rsp), %rax
	movq	64(%rsp), %rdx
	movq	%rax, 24(%rdx)
	movq	16(%rsp), %rax
	movq	%rax, 16(%rdx)
	movq	(%rsp), %rax
	movq	8(%rsp), %rcx
	movq	%rcx, 8(%rdx)
	movq	%rax, (%rdx)
	addq	$104, %rsp
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
.Lfunc_end53:
	.size	_RNvNtCsemcRClSg8DH_9native_vm10transcript5climb, .Lfunc_end53-_RNvNtCsemcRClSg8DH_9native_vm10transcript5climb
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm11ring_switch11ring_switch,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm11ring_switch11ring_switch,@function
_RNvNtCsemcRClSg8DH_9native_vm11ring_switch11ring_switch:
.Lfunc_begin54:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	pushq	%r15
	.cfi_def_cfa_offset 24
	pushq	%r14
	.cfi_def_cfa_offset 32
	pushq	%r12
	.cfi_def_cfa_offset 40
	pushq	%rbx
	.cfi_def_cfa_offset 48
	subq	$384, %rsp
	.cfi_def_cfa_offset 432
	.cfi_offset %rbx, -48
	.cfi_offset %r12, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	%rdx, %rbx
	movq	%rsi, %r14
	movq	%rdi, %r12
	movl	$13, %esi
	callq	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState5grind
	testb	%al, %al
	je	.LBB54_2
	movq	$0, (%rsp)
	movq	$0, 8(%rsp)
	movq	$0, 16(%rsp)
	movq	$0, 24(%rsp)
	movq	$0, 32(%rsp)
	movq	$0, 40(%rsp)
	movq	$0, 48(%rsp)
	movq	$0, 56(%rsp)
	movq	$0, 64(%rsp)
	movq	$0, 72(%rsp)
	movq	$0, 80(%rsp)
	movq	$0, 88(%rsp)
	movq	$0, 96(%rsp)
	movq	$0, 104(%rsp)
	movq	$0, 112(%rsp)
	movq	$0, 120(%rsp)
	movq	$0, 128(%rsp)
	movq	$0, 136(%rsp)
	movq	$0, 144(%rsp)
	movq	$0, 152(%rsp)
	movq	$0, 160(%rsp)
	movq	$0, 168(%rsp)
	movq	$0, 176(%rsp)
	movq	$0, 184(%rsp)
	movq	$0, 192(%rsp)
	movq	$0, 200(%rsp)
	movq	$0, 208(%rsp)
	movq	$0, 216(%rsp)
	movq	$0, 224(%rsp)
	movq	$0, 232(%rsp)
	movq	$0, 240(%rsp)
	movq	$0, 248(%rsp)
	movq	%rsp, %r15
	movl	$16, %edx
	movq	%r12, %rdi
	movq	%r15, %rsi
	movl	%eax, %ebp
	callq	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState17sample_challenges
	movq	128(%rsp), %rax
	movq	%rax, 256(%rsp)
	movq	136(%rsp), %rax
	movq	%rax, 264(%rsp)
	movq	144(%rsp), %rax
	movq	%rax, 272(%rsp)
	movq	152(%rsp), %rax
	movq	%rax, 280(%rsp)
	movq	160(%rsp), %rax
	movq	%rax, 288(%rsp)
	movq	168(%rsp), %rax
	movq	%rax, 296(%rsp)
	movq	176(%rsp), %rax
	movq	%rax, 304(%rsp)
	movq	184(%rsp), %rax
	movq	%rax, 312(%rsp)
	movq	192(%rsp), %rax
	movq	%rax, 320(%rsp)
	movq	200(%rsp), %rax
	movq	%rax, 328(%rsp)
	movq	208(%rsp), %rax
	movq	%rax, 336(%rsp)
	movq	216(%rsp), %rax
	movq	%rax, 344(%rsp)
	movq	224(%rsp), %rax
	movq	%rax, 352(%rsp)
	movq	232(%rsp), %rax
	movq	%rax, 360(%rsp)
	movq	240(%rsp), %rax
	movq	%rax, 368(%rsp)
	movq	248(%rsp), %rax
	movq	%rax, 376(%rsp)
	leaq	16(%rbx), %rdx
	leaq	256(%rsp), %r12
	movq	%r15, %rdi
	movq	%r12, %rsi
	callq	_RNvNtCsemcRClSg8DH_9native_vm11ring_switch17ring_coefficients
	movq	%r14, %rdi
	movq	%r15, %rsi
	movq	%r12, %rdx
	callq	_RNvNtCsemcRClSg8DH_9native_vm11ring_switch11ring_target
	movq	%rax, %rcx
	movl	%ebp, %eax
	movq	%rcx, (%rbx)
	movq	%rdx, 8(%rbx)
.LBB54_2:
	addq	$384, %rsp
	.cfi_def_cfa_offset 48
	popq	%rbx
	.cfi_def_cfa_offset 40
	popq	%r12
	.cfi_def_cfa_offset 32
	popq	%r14
	.cfi_def_cfa_offset 24
	popq	%r15
	.cfi_def_cfa_offset 16
	popq	%rbp
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end54:
	.size	_RNvNtCsemcRClSg8DH_9native_vm11ring_switch11ring_switch, .Lfunc_end54-_RNvNtCsemcRClSg8DH_9native_vm11ring_switch11ring_switch
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm11ring_switch11ring_target,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm11ring_switch11ring_target,@function
_RNvNtCsemcRClSg8DH_9native_vm11ring_switch11ring_target:
.Lfunc_begin55:
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
	subq	$2296, %rsp
	.cfi_def_cfa_offset 2352
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	%rdx, %rbx
	movq	%rsi, %r12
	movq	%rdi, %r14
	movl	$8, %r15d
	.p2align	4
.LBB55_1:
	movq	-8(%r14,%r15), %rdi
	movq	(%r14,%r15), %rsi
	movq	%rbx, %rdx
	callq	_RNvNtCsemcRClSg8DH_9native_vm11ring_switch8ring_psi
	movq	%rax, 240(%rsp,%r15)
	movq	%rdx, 248(%rsp,%r15)
	addq	$16, %r15
	cmpq	$1032, %r15
	jne	.LBB55_1
	leaq	1272(%rsp), %r15
	leaq	248(%rsp), %rsi
	movl	$1024, %edx
	movq	%r15, %rdi
	callq	*memcpy@GOTPCREL(%rip)
	movl	$8, %edi
	movl	$2, %esi
	xorl	%edx, %edx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW7sq_iter
	movq	%rax, %rbx
	movq	%rdx, %r14
	movq	112(%r12), %rax
	movq	%rax, 240(%rsp)
	movq	120(%r12), %rax
	movq	%rax, 232(%rsp)
	movl	$64, %esi
	movq	%r15, %rdi
	movq	%rbx, %rdx
	movq	%r14, %rcx
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field9poly_eval
	movl	$56, %edi
	movq	%rax, %rsi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW7sq_iter
	movq	%rax, 224(%rsp)
	movq	%rdx, 216(%rsp)
	movl	$8, %edi
	movq	%rbx, %rsi
	movq	%r14, %rdx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW7sq_iter
	movq	%rax, %rbx
	movq	%rdx, %r14
	movq	96(%r12), %rax
	movq	%rax, 208(%rsp)
	movq	104(%r12), %rax
	movq	%rax, 200(%rsp)
	movl	$64, %esi
	movq	%r15, %rdi
	movq	%rbx, %rdx
	movq	%r14, %rcx
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field9poly_eval
	movl	$48, %edi
	movq	%rax, %rsi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW7sq_iter
	movq	%rax, 192(%rsp)
	movq	%rdx, 184(%rsp)
	movl	$8, %edi
	movq	%rbx, %rsi
	movq	%r14, %rdx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW7sq_iter
	movq	%rax, %rbx
	movq	%rdx, %r14
	movq	80(%r12), %rax
	movq	%rax, 56(%rsp)
	movq	88(%r12), %rax
	movq	%rax, 176(%rsp)
	movl	$64, %esi
	movq	%r15, %rdi
	movq	%rbx, %rdx
	movq	%r14, %rcx
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field9poly_eval
	movl	$40, %edi
	movq	%rax, %rsi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW7sq_iter
	movq	%rax, 168(%rsp)
	movq	%rdx, 160(%rsp)
	movl	$8, %edi
	movq	%rbx, %rsi
	movq	%r14, %rdx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW7sq_iter
	movq	%rax, %rbx
	movq	%rdx, %r14
	movq	64(%r12), %rax
	movq	%rax, 48(%rsp)
	movq	72(%r12), %rax
	movq	%rax, 152(%rsp)
	movl	$64, %esi
	movq	%r15, %rdi
	movq	%rbx, %rdx
	movq	%r14, %rcx
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field9poly_eval
	movl	$32, %edi
	movq	%rax, %rsi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW7sq_iter
	movq	%rax, 144(%rsp)
	movq	%rdx, 136(%rsp)
	movl	$8, %edi
	movq	%rbx, %rsi
	movq	%r14, %rdx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW7sq_iter
	movq	%rax, %rbx
	movq	%rdx, %r14
	movq	48(%r12), %rax
	movq	%rax, 40(%rsp)
	movq	56(%r12), %rax
	movq	%rax, 32(%rsp)
	movl	$64, %esi
	movq	%r15, %rdi
	movq	%rbx, %rdx
	movq	%r14, %rcx
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field9poly_eval
	movl	$24, %edi
	movq	%rax, %rsi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW7sq_iter
	movq	%rax, 96(%rsp)
	movq	%rdx, 88(%rsp)
	movl	$8, %edi
	movq	%rbx, %rsi
	movq	%r14, %rdx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW7sq_iter
	movq	%rax, %r14
	movq	%rdx, %rbp
	movq	32(%r12), %rax
	movq	%rax, 16(%rsp)
	movq	40(%r12), %rax
	movq	%rax, 8(%rsp)
	movl	$64, %esi
	movq	%r15, %rdi
	movq	%r14, %rdx
	movq	%rbp, %rcx
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field9poly_eval
	movl	$16, %edi
	movq	%rax, %rsi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW7sq_iter
	movq	%rax, 72(%rsp)
	movq	%rdx, 64(%rsp)
	movl	$8, %edi
	movq	%r14, %rsi
	movq	%rbp, %rdx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW7sq_iter
	movq	%rax, %r13
	movq	%rdx, %rbx
	movq	16(%r12), %rbp
	movq	24(%r12), %rax
	movq	%rax, 24(%rsp)
	movl	$64, %esi
	movq	%r15, %rdi
	movq	%r13, %rdx
	movq	%rbx, %rcx
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field9poly_eval
	movl	$8, %edi
	movq	%rax, %rsi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW7sq_iter
	movq	%rax, %r15
	movq	%rdx, %r14
	movl	$8, %edi
	movq	%r13, %rsi
	movq	%rbx, %rdx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW7sq_iter
	movq	%rax, 112(%rsp)
	movq	%rdx, 104(%rsp)
	movq	(%r12), %rax
	movq	%rax, 128(%rsp)
	movq	8(%r12), %rax
	movq	%rax, 120(%rsp)
	movq	%rbp, %rdi
	movq	24(%rsp), %rsi
	movq	%r15, %rdx
	movq	%r14, %rcx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	movq	%rax, 24(%rsp)
	movq	%rdx, 80(%rsp)
	movq	16(%rsp), %rdi
	movq	8(%rsp), %rsi
	movq	72(%rsp), %rdx
	movq	64(%rsp), %rcx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	movq	%rax, 16(%rsp)
	movq	%rdx, 8(%rsp)
	movq	40(%rsp), %rdi
	movq	32(%rsp), %rsi
	movq	96(%rsp), %rdx
	movq	88(%rsp), %rcx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	movq	%rax, 40(%rsp)
	movq	%rdx, 32(%rsp)
	movq	48(%rsp), %rdi
	movq	152(%rsp), %rsi
	movq	144(%rsp), %rdx
	movq	136(%rsp), %rcx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	movq	%rax, 48(%rsp)
	movq	%rdx, %r13
	movq	56(%rsp), %rdi
	movq	176(%rsp), %rsi
	movq	168(%rsp), %rdx
	movq	160(%rsp), %rcx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	movq	%rax, 56(%rsp)
	movq	%rdx, %r14
	movq	208(%rsp), %rdi
	movq	200(%rsp), %rsi
	movq	192(%rsp), %rdx
	movq	184(%rsp), %rcx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	movq	%rax, %rbp
	movq	%rdx, %rbx
	movq	240(%rsp), %rdi
	movq	232(%rsp), %rsi
	movq	224(%rsp), %rdx
	movq	216(%rsp), %rcx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	movq	%rax, %r12
	movq	%rdx, %r15
	xorq	%rbx, %r15
	xorq	%r14, %r15
	xorq	%r13, %r15
	xorq	32(%rsp), %r15
	xorq	8(%rsp), %r15
	xorq	80(%rsp), %r15
	xorq	%rbp, %r12
	xorq	56(%rsp), %r12
	xorq	48(%rsp), %r12
	xorq	40(%rsp), %r12
	xorq	16(%rsp), %r12
	xorq	24(%rsp), %r12
	movl	$64, %esi
	leaq	1272(%rsp), %rdi
	movq	112(%rsp), %rdx
	movq	104(%rsp), %rcx
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field9poly_eval
	xorl	%edi, %edi
	movq	%rax, %rsi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW7sq_iter
	movq	%rdx, %rcx
	movq	128(%rsp), %rdi
	movq	120(%rsp), %rsi
	movq	%rax, %rdx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	xorq	%r12, %rax
	xorq	%r15, %rdx
	addq	$2296, %rsp
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
.Lfunc_end55:
	.size	_RNvNtCsemcRClSg8DH_9native_vm11ring_switch11ring_target, .Lfunc_end55-_RNvNtCsemcRClSg8DH_9native_vm11ring_switch11ring_target
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm11ring_switch17ring_coefficients,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm11ring_switch17ring_coefficients,@function
_RNvNtCsemcRClSg8DH_9native_vm11ring_switch17ring_coefficients:
.Lfunc_begin56:
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
	subq	$120, %rsp
	.cfi_def_cfa_offset 176
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	%rdx, %rbx
	movq	%rdi, 112(%rsp)
	movq	120(%rsi), %rdx
	movq	112(%rsi), %rax
	movq	104(%rsi), %r14
	movq	96(%rsi), %r15
	movq	88(%rsi), %rcx
	movq	%rcx, 8(%rsp)
	movq	80(%rsi), %rcx
	movq	%rcx, (%rsp)
	movq	72(%rsi), %rcx
	movq	%rcx, 88(%rsp)
	movq	64(%rsi), %rcx
	movq	%rcx, 80(%rsp)
	movq	56(%rsi), %rcx
	movq	%rcx, 72(%rsp)
	movq	48(%rsi), %rcx
	movq	%rcx, 64(%rsp)
	movq	40(%rsi), %rcx
	movq	%rcx, 56(%rsp)
	movq	32(%rsi), %rcx
	movq	%rcx, 48(%rsp)
	movq	24(%rsi), %rcx
	movq	%rcx, 40(%rsp)
	movq	16(%rsi), %rcx
	movq	%rcx, 32(%rsp)
	movq	(%rsi), %rcx
	movq	%rcx, 24(%rsp)
	movq	8(%rsi), %rcx
	movq	%rcx, 16(%rsp)
	xorl	%ebp, %ebp
	.p2align	4
.LBB56_1:
	movq	%rdx, 96(%rsp)
	movq	%rax, 104(%rsp)
	movq	112(%rsp), %rax
	movq	(%rax,%rbp), %r12
	movq	8(%rax,%rbp), %r13
	movq	%r12, %rdi
	movq	%r13, %rsi
	movq	24(%rsp), %rdx
	movq	16(%rsp), %rcx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	movq	%rax, (%rbx,%rbp,8)
	movq	%rdx, 8(%rbx,%rbp,8)
	movq	%r12, %rdi
	movq	%r13, %rsi
	movq	32(%rsp), %rdx
	movq	40(%rsp), %rcx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	movq	%rax, 16(%rbx,%rbp,8)
	movq	%rdx, 24(%rbx,%rbp,8)
	movq	%r12, %rdi
	movq	%r13, %rsi
	movq	48(%rsp), %rdx
	movq	56(%rsp), %rcx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	movq	%rax, 32(%rbx,%rbp,8)
	movq	%rdx, 40(%rbx,%rbp,8)
	movq	%r12, %rdi
	movq	%r13, %rsi
	movq	64(%rsp), %rdx
	movq	72(%rsp), %rcx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	movq	%rax, 48(%rbx,%rbp,8)
	movq	%rdx, 56(%rbx,%rbp,8)
	movq	%r12, %rdi
	movq	%r13, %rsi
	movq	80(%rsp), %rdx
	movq	88(%rsp), %rcx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	movq	%rax, 64(%rbx,%rbp,8)
	movq	%rdx, 72(%rbx,%rbp,8)
	movq	%r12, %rdi
	movq	%r13, %rsi
	movq	(%rsp), %rdx
	movq	8(%rsp), %rcx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	movq	%rax, 80(%rbx,%rbp,8)
	movq	%rdx, 88(%rbx,%rbp,8)
	movq	%r12, %rdi
	movq	%r13, %rsi
	movq	%r15, %rdx
	movq	%r14, %rcx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	movq	%rax, 96(%rbx,%rbp,8)
	movq	%rdx, 104(%rbx,%rbp,8)
	movq	%r12, %rdi
	movq	%r13, %rsi
	movq	104(%rsp), %rdx
	movq	96(%rsp), %rcx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	movq	%rax, 112(%rbx,%rbp,8)
	movq	%rdx, 120(%rbx,%rbp,8)
	movl	$8, %edi
	movq	24(%rsp), %rsi
	movq	16(%rsp), %rdx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW7sq_iter
	movq	%rax, 24(%rsp)
	movq	%rdx, 16(%rsp)
	movl	$8, %edi
	movq	32(%rsp), %rsi
	movq	40(%rsp), %rdx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW7sq_iter
	movq	%rax, 32(%rsp)
	movq	%rdx, 40(%rsp)
	movl	$8, %edi
	movq	48(%rsp), %rsi
	movq	56(%rsp), %rdx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW7sq_iter
	movq	%rax, 48(%rsp)
	movq	%rdx, 56(%rsp)
	movl	$8, %edi
	movq	64(%rsp), %rsi
	movq	72(%rsp), %rdx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW7sq_iter
	movq	%rax, 64(%rsp)
	movq	%rdx, 72(%rsp)
	movl	$8, %edi
	movq	80(%rsp), %rsi
	movq	88(%rsp), %rdx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW7sq_iter
	movq	%rax, 80(%rsp)
	movq	%rdx, 88(%rsp)
	movl	$8, %edi
	movq	(%rsp), %rsi
	movq	8(%rsp), %rdx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW7sq_iter
	movq	%rax, (%rsp)
	movq	%rdx, 8(%rsp)
	movl	$8, %edi
	movq	%r15, %rsi
	movq	%r14, %rdx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW7sq_iter
	movq	%rax, %r15
	movq	%rdx, %r14
	movl	$8, %edi
	movq	104(%rsp), %rsi
	movq	96(%rsp), %rdx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW7sq_iter
	addq	$16, %rbp
	cmpq	$128, %rbp
	jne	.LBB56_1
	addq	$120, %rsp
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
.Lfunc_end56:
	.size	_RNvNtCsemcRClSg8DH_9native_vm11ring_switch17ring_coefficients, .Lfunc_end56-_RNvNtCsemcRClSg8DH_9native_vm11ring_switch17ring_coefficients
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm11ring_switch8ring_psi,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm11ring_switch8ring_psi,@function
_RNvNtCsemcRClSg8DH_9native_vm11ring_switch8ring_psi:
.Lfunc_begin57:
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
	subq	$24, %rsp
	.cfi_def_cfa_offset 80
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	%rdx, %rbx
	movq	%rsi, %r14
	movq	%rdi, %r15
	movq	(%rdx), %rdi
	movq	8(%rdx), %rsi
	movq	%r15, %rdx
	movq	%r14, %rcx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	movq	%rax, %rbp
	movq	%rdx, %r12
	movq	%r15, %rdi
	movq	%r14, %rsi
	movq	%r15, %rdx
	movq	%r14, %rcx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	movq	%rax, %r14
	movq	%rdx, %r15
	movq	16(%rbx), %rdi
	movq	24(%rbx), %rsi
	movq	%rax, %rdx
	movq	%r15, %rcx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	movq	%rax, %r13
	xorq	%rbp, %r13
	xorq	%r12, %rdx
	movq	%rdx, 16(%rsp)
	movq	%r14, %rdi
	movq	%r15, %rsi
	movq	%r14, %rdx
	movq	%r15, %rcx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	movq	%rax, %r14
	movq	%rdx, %r15
	movq	32(%rbx), %rdi
	movq	40(%rbx), %rsi
	movq	%rax, %rdx
	movq	%r15, %rcx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	movq	%rax, 8(%rsp)
	movq	%rdx, (%rsp)
	movq	%r14, %rdi
	movq	%r15, %rsi
	movq	%r14, %rdx
	movq	%r15, %rcx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	movq	%rax, %rbp
	movq	%rdx, %r12
	movq	48(%rbx), %rdi
	movq	56(%rbx), %rsi
	movq	%rax, %rdx
	movq	%r12, %rcx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	xorq	8(%rsp), %rax
	xorq	%r13, %rax
	movq	%rax, 8(%rsp)
	xorq	(%rsp), %rdx
	xorq	16(%rsp), %rdx
	movq	%rdx, 16(%rsp)
	movq	%rbp, %rdi
	movq	%r12, %rsi
	movq	%rbp, %rdx
	movq	%r12, %rcx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	movq	%rax, %r12
	movq	%rdx, %r13
	movq	64(%rbx), %rdi
	movq	72(%rbx), %rsi
	movq	%rax, %rdx
	movq	%r13, %rcx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	movq	%rax, %r15
	movq	%rdx, %r14
	movq	%r12, %rdi
	movq	%r13, %rsi
	movq	%r12, %rdx
	movq	%r13, %rcx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	movq	%rax, %r12
	movq	%rdx, %r13
	movq	80(%rbx), %rdi
	movq	88(%rbx), %rsi
	movq	%rax, %rdx
	movq	%r13, %rcx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	movq	%rax, %rbp
	xorq	%r15, %rbp
	xorq	%r14, %rdx
	movq	%rdx, (%rsp)
	movq	%r12, %rdi
	movq	%r13, %rsi
	movq	%r12, %rdx
	movq	%r13, %rcx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	movq	%rax, %r15
	movq	%rdx, %r14
	movq	96(%rbx), %rdi
	movq	104(%rbx), %rsi
	movq	%rax, %rdx
	movq	%r14, %rcx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	movq	%rax, %r13
	movq	%rdx, %r12
	xorq	%rbp, %r13
	xorq	8(%rsp), %r13
	xorq	(%rsp), %r12
	xorq	16(%rsp), %r12
	movq	%r15, %rdi
	movq	%r14, %rsi
	movq	%r15, %rdx
	movq	%r14, %rcx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	movq	%rdx, %rcx
	movq	112(%rbx), %rdi
	movq	120(%rbx), %rsi
	movq	%rax, %rdx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	xorq	%r13, %rax
	xorq	%r12, %rdx
	addq	$24, %rsp
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
.Lfunc_end57:
	.size	_RNvNtCsemcRClSg8DH_9native_vm11ring_switch8ring_psi, .Lfunc_end57-_RNvNtCsemcRClSg8DH_9native_vm11ring_switch8ring_psi
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm3bus10block_form,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm3bus10block_form,@function
_RNvNtCsemcRClSg8DH_9native_vm3bus10block_form:
.Lfunc_begin58:
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
	subq	$24, %rsp
	.cfi_def_cfa_offset 80
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	%r9, %rbx
	movq	%rdx, 16(%rsp)
	movq	%rsi, %r15
	movq	$0, 8(%r9)
	movq	$0, 16(%r9)
	movq	$0, 24(%r9)
	movq	%rcx, 32(%r9)
	movq	%r8, 40(%r9)
	movq	$1, (%r9)
	cmpq	$146, %rdi
	ja	.LBB58_1
	shlq	$4, %rdi
	leaq	.Lanon.a75d6d9e6a8990b4224ef13f18552af8.3(%rip), %rax
	movq	(%rdi,%rax), %rbp
	movq	8(%rdi,%rax), %r14
	addq	%rbp, %r14
	jmp	.LBB58_3
.LBB58_1:
	xorl	%r14d, %r14d
	xorl	%ebp, %ebp
.LBB58_3:
	xorl	%r13d, %r13d
	movq	%r14, 8(%rsp)
	subq	%rbp, %r14
	cmovbq	%r13, %r14
	addq	$8, %r15
	jmp	.LBB58_4
	.p2align	4
.LBB58_7:
	movq	-8(%r15), %rcx
	movq	(%r15), %r8
.LBB58_8:
	movq	%rbx, %rdi
	movq	%rax, %rsi
	callq	_RNvMs0_NtCsemcRClSg8DH_9native_vm6layoutNtB5_7FormBuf10add_scaled
	addq	$16, %r15
	incq	%r13
	testb	%al, %al
	je	.LBB58_9
.LBB58_4:
	movq	%rbp, %r12
	addq	%r13, %r12
	cmpq	%r13, %r14
	je	.LBB58_9
	movq	%r12, %rdi
	callq	_RNvNtCsemcRClSg8DH_9native_vm6layout10form_terms
	cmpq	16(%rsp), %r13
	jb	.LBB58_7
	xorl	%r8d, %r8d
	xorl	%ecx, %ecx
	jmp	.LBB58_8
.LBB58_9:
	cmpq	8(%rsp), %r12
	setae	%al
	addq	$24, %rsp
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
.Lfunc_end58:
	.size	_RNvNtCsemcRClSg8DH_9native_vm3bus10block_form, .Lfunc_end58-_RNvNtCsemcRClSg8DH_9native_vm3bus10block_form
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm3bus10bus_layout,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm3bus10bus_layout,@function
_RNvNtCsemcRClSg8DH_9native_vm3bus10bus_layout:
.Lfunc_begin59:
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
	subq	$1752, %rsp
	.cfi_def_cfa_offset 1808
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	%r9, %r12
	movq	%r8, %rbp
	movq	%rcx, %r13
	movq	%rdx, %r14
	movq	%rsi, %r15
	movq	%rdi, %rbx
	leaq	888(%rsp), %rdi
	movl	$432, %edx
	xorl	%esi, %esi
	callq	*memset@GOTPCREL(%rip)
	testq	%r14, %r14
	je	.LBB59_4
	movq	(%r15), %rax
	movq	%rax, 888(%rsp)
	cmpq	$1, %r14
	je	.LBB59_4
	movq	8(%r15), %rax
	movq	%rax, 896(%rsp)
	cmpq	$2, %r14
	je	.LBB59_4
	movq	16(%r15), %rax
	movq	%rax, 904(%rsp)
.LBB59_4:
	leaq	(%r14,%rbp), %r15
	leaq	(%rsp,%r14,8), %rax
	addq	$888, %rax
	movl	%ebp, %edx
	andl	$62, %edx
	leaq	16(%r13), %rsi
	xorl	%ecx, %ecx
	jmp	.LBB59_7
	.p2align	4
.LBB59_5:
	movq	24(%r12,%rdi,8), %rdi
.LBB59_6:
	movq	%rdi, 8(%rax,%rcx,8)
	addq	$2, %rcx
	addq	$32, %rsi
	cmpq	%rcx, %rdx
	je	.LBB59_11
.LBB59_7:
	movq	-16(%rsi), %rdi
	cmpq	$5, %rdi
	ja	.LBB59_9
	movq	24(%r12,%rdi,8), %rdi
	movq	%rdi, (%rax,%rcx,8)
	movq	(%rsi), %rdi
	cmpq	$5, %rdi
	jbe	.LBB59_5
	jmp	.LBB59_10
	.p2align	4
.LBB59_9:
	xorl	%edi, %edi
	movq	%rdi, (%rax,%rcx,8)
	movq	(%rsi), %rdi
	cmpq	$5, %rdi
	jbe	.LBB59_5
.LBB59_10:
	xorl	%edi, %edi
	jmp	.LBB59_6
.LBB59_11:
	testb	$1, %bpl
	je	.LBB59_16
	movq	%rcx, %rdx
	shlq	$4, %rdx
	movq	(%r13,%rdx), %rdx
	cmpq	$5, %rdx
	ja	.LBB59_14
	movq	24(%r12,%rdx,8), %rdx
	jmp	.LBB59_15
.LBB59_14:
	xorl	%edx, %edx
.LBB59_15:
	movq	%rdx, (%rax,%rcx,8)
.LBB59_16:
	leaq	1320(%rsp), %r12
	movl	$432, %edx
	movq	%r12, %rdi
	xorl	%esi, %esi
	callq	*memset@GOTPCREL(%rip)
	leaq	888(%rsp), %rdi
	movl	$54, %ecx
	movq	%r15, %rsi
	movq	%r12, %rdx
	callq	_RNvNtCsemcRClSg8DH_9native_vm6layout13stack_offsets
	cmpq	$1, %rax
	jne	.LBB59_25
	movq	%rdx, (%rsp)
	movq	$0, 8(%rsp)
	leaq	16(%rsp), %rax
	movq	$0, 16(%rsp)
	movq	$0, 24(%rsp)
	movq	$0, 32(%rsp)
	movq	$0, 40(%rsp)
	movq	$0, 48(%rsp)
	movq	$0, 56(%rsp)
	movq	$0, 64(%rsp)
	movq	$0, 72(%rsp)
	movq	$0, 80(%rsp)
	movq	$0, 88(%rsp)
	movq	$0, 96(%rsp)
	movq	$0, 104(%rsp)
	movq	$0, 112(%rsp)
	movq	$0, 120(%rsp)
	movq	$0, 128(%rsp)
	movq	$0, 136(%rsp)
	movq	$0, 144(%rsp)
	movq	$0, 152(%rsp)
	movq	$0, 160(%rsp)
	movq	$0, 168(%rsp)
	movq	$0, 176(%rsp)
	movq	$0, 184(%rsp)
	movq	$0, 192(%rsp)
	movq	$0, 200(%rsp)
	movq	$0, 208(%rsp)
	movq	$0, 216(%rsp)
	movq	$0, 224(%rsp)
	movq	$0, 232(%rsp)
	movq	$0, 240(%rsp)
	movq	$0, 248(%rsp)
	movq	$0, 256(%rsp)
	movq	$0, 264(%rsp)
	movq	$0, 272(%rsp)
	movq	$0, 280(%rsp)
	movq	$0, 288(%rsp)
	movq	$0, 296(%rsp)
	movq	$0, 304(%rsp)
	movq	$0, 312(%rsp)
	movq	$0, 320(%rsp)
	movq	$0, 328(%rsp)
	movq	$0, 336(%rsp)
	movq	$0, 344(%rsp)
	movq	$0, 352(%rsp)
	movq	$0, 360(%rsp)
	movq	$0, 368(%rsp)
	movq	$0, 376(%rsp)
	movq	$0, 384(%rsp)
	movq	$0, 392(%rsp)
	movq	$0, 400(%rsp)
	movq	$0, 408(%rsp)
	movq	$0, 416(%rsp)
	movq	$0, 424(%rsp)
	movq	$0, 432(%rsp)
	movq	$0, 440(%rsp)
	movq	$0, 448(%rsp)
	movq	$0, 456(%rsp)
	movq	$0, 464(%rsp)
	movq	$0, 472(%rsp)
	movq	$0, 480(%rsp)
	movq	$0, 488(%rsp)
	movq	$0, 496(%rsp)
	movq	$0, 504(%rsp)
	movq	$0, 512(%rsp)
	movq	$0, 520(%rsp)
	movq	$0, 528(%rsp)
	movq	$0, 536(%rsp)
	movq	$0, 544(%rsp)
	movq	$0, 552(%rsp)
	movq	$0, 560(%rsp)
	movq	$0, 568(%rsp)
	movq	$0, 576(%rsp)
	movq	$0, 584(%rsp)
	movq	$0, 592(%rsp)
	movq	$0, 600(%rsp)
	movq	$0, 608(%rsp)
	movq	$0, 616(%rsp)
	movq	$0, 624(%rsp)
	movq	$0, 632(%rsp)
	movq	$0, 640(%rsp)
	movq	$0, 648(%rsp)
	movq	$0, 656(%rsp)
	movq	$0, 664(%rsp)
	movq	$0, 672(%rsp)
	movq	$0, 680(%rsp)
	movq	$0, 688(%rsp)
	movq	$0, 696(%rsp)
	movq	$0, 704(%rsp)
	movq	$0, 712(%rsp)
	movq	$0, 720(%rsp)
	movq	$0, 728(%rsp)
	movq	$0, 736(%rsp)
	movq	$0, 744(%rsp)
	movq	$0, 752(%rsp)
	movq	$0, 760(%rsp)
	movq	$0, 768(%rsp)
	movq	$0, 776(%rsp)
	movq	$0, 784(%rsp)
	movq	$0, 792(%rsp)
	movq	$0, 800(%rsp)
	movq	$0, 808(%rsp)
	movq	$0, 816(%rsp)
	movq	$0, 824(%rsp)
	movq	$0, 832(%rsp)
	movq	$0, 840(%rsp)
	movq	$0, 848(%rsp)
	movq	$0, 856(%rsp)
	movq	$0, 864(%rsp)
	movq	$0, 872(%rsp)
	movq	$0, 880(%rsp)
	xorl	%ecx, %ecx
	movq	8(%rsp), %rdx
	jmp	.LBB59_19
	.p2align	4
.LBB59_18:
	incq	%rcx
	cmpq	%rcx, %r15
	je	.LBB59_26
.LBB59_19:
	movq	888(%rsp,%rcx,8), %rdi
	movq	1320(%rsp,%rcx,8), %rsi
	cmpq	%r14, %rcx
	jae	.LBB59_22
	cmpq	$3, %rdx
	jae	.LBB59_25
	movq	%rdx, %r8
	shlq	$4, %r8
	movq	%rdi, (%rax,%r8)
	movq	%rsi, 8(%rax,%r8)
	incq	%rdx
	jmp	.LBB59_18
	.p2align	4
.LBB59_22:
	movq	64(%rsp), %r8
	cmpq	$51, %r8
	jae	.LBB59_25
	movq	%r8, %r9
	shlq	$4, %r9
	movq	%rdi, 56(%rax,%r9)
	movq	%rsi, 64(%rax,%r9)
	incq	%r8
	movq	%r8, 64(%rsp)
	jmp	.LBB59_18
.LBB59_25:
	movq	$0, (%rbx)
	jmp	.LBB59_27
.LBB59_26:
	movq	%rdx, 8(%rsp)
	leaq	8(%rbx), %rdi
	movq	%rsp, %rsi
	movl	$888, %edx
	callq	*memcpy@GOTPCREL(%rip)
	movq	$1, (%rbx)
.LBB59_27:
	addq	$1752, %rsp
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
.Lfunc_end59:
	.size	_RNvNtCsemcRClSg8DH_9native_vm3bus10bus_layout, .Lfunc_end59-_RNvNtCsemcRClSg8DH_9native_vm3bus10bus_layout
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm3bus12fingerprints,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm3bus12fingerprints,@function
_RNvNtCsemcRClSg8DH_9native_vm3bus12fingerprints:
.Lfunc_begin60:
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
	subq	$200, %rsp
	.cfi_def_cfa_offset 256
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	%r9, 16(%rsp)
	movq	%r8, %r15
	movq	%rcx, %r13
	movq	%rdx, %r12
	movq	%rsi, %r14
	movq	%rdi, %rbx
	movq	280(%rsp), %rbp
	xorl	%edi, %edi
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field4kpow
	movq	$1, 24(%rsp)
	movq	$0, 32(%rsp)
	movq	%rbp, 40(%rsp)
	movq	$0, 48(%rsp)
	movq	%rax, 56(%rsp)
	movq	$0, 64(%rsp)
	leaq	24(%rsp), %rdx
	movl	$3, %esi
	movl	$3, %ecx
	movq	%r14, %rdi
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field3dot
	movq	%rax, 8(%rsp)
	movq	%rdx, %rbp
	movq	%r13, %rdi
	movq	%r15, %rsi
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field14index_mle_from
	movq	(%r12), %rcx
	movq	8(%r12), %rsi
	movq	16(%r12), %rdi
	movq	24(%r12), %r8
	movq	$2, 120(%rsp)
	movq	$0, 128(%rsp)
	movq	%rax, 136(%rsp)
	movq	%rdx, 144(%rsp)
	movq	288(%rsp), %rax
	movq	%rax, 152(%rsp)
	movq	296(%rsp), %rax
	movq	%rax, 160(%rsp)
	movq	%rcx, 168(%rsp)
	movq	%rsi, 176(%rsp)
	movq	%rdi, 184(%rsp)
	movq	%r8, 192(%rsp)
	leaq	120(%rsp), %rdx
	movl	$5, %esi
	movl	$5, %ecx
	movq	%r14, %rdi
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field3dot
	movq	%rax, %r15
	movq	%rdx, %r12
	movl	$2, %edi
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field4kpow
	movq	%rax, %r13
	movq	16(%rsp), %rdi
	movq	256(%rsp), %rsi
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field14index_mle_from
	movq	%r13, 72(%rsp)
	movq	$0, 80(%rsp)
	movq	%rax, 88(%rsp)
	movq	%rdx, 96(%rsp)
	movq	304(%rsp), %rax
	movq	%rax, 104(%rsp)
	movq	312(%rsp), %rax
	movq	%rax, 112(%rsp)
	leaq	72(%rsp), %rdx
	movl	$3, %esi
	movl	$3, %ecx
	movq	%r14, %rdi
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field3dot
	xorq	264(%rsp), %rax
	xorq	272(%rsp), %rdx
	movq	8(%rsp), %rcx
	movq	%rcx, (%rbx)
	movq	%rbp, 8(%rbx)
	movq	%r15, 16(%rbx)
	movq	%r12, 24(%rbx)
	movq	%rax, 32(%rbx)
	movq	%rdx, 40(%rbx)
	addq	$200, %rsp
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
.Lfunc_end60:
	.size	_RNvNtCsemcRClSg8DH_9native_vm3bus12fingerprints, .Lfunc_end60-_RNvNtCsemcRClSg8DH_9native_vm3bus12fingerprints
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm3bus14bytecode_share,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm3bus14bytecode_share,@function
_RNvNtCsemcRClSg8DH_9native_vm3bus14bytecode_share:
.Lfunc_begin61:
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
	subq	$376, %rsp
	.cfi_def_cfa_offset 432
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	%r9, %r12
	movq	%r8, %rbp
	movq	%rcx, %r13
	movq	%rdx, %r14
	movq	%rsi, %r15
	movq	%rdi, %rbx
	leaq	120(%rsp), %rdi
	callq	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState11read_scalar
	cmpl	$1, 120(%rsp)
	jne	.LBB61_14
	movq	128(%rsp), %rdx
	movq	136(%rsp), %rcx
	movq	$0, 24(%rsp)
	movq	$0, 32(%rsp)
	movq	$0, 40(%rsp)
	movq	$0, 48(%rsp)
	movq	$0, 56(%rsp)
	movq	$0, 64(%rsp)
	movq	$0, 72(%rsp)
	movq	$0, 80(%rsp)
	movq	$4, (%rsp)
	leaq	120(%rsp), %rdi
	leaq	24(%rsp), %r9
	movl	$3, %r8d
	movq	%r15, %rsi
	movq	%rdx, 112(%rsp)
	movq	%rcx, 104(%rsp)
	callq	_RINvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB6_6TState8sumcheckNCNvB2_14sumcheck_plain0EB8_
	cmpb	$0, 120(%rsp)
	je	.LBB61_14
	movq	128(%rsp), %rax
	movq	%rax, 96(%rsp)
	movq	136(%rsp), %rax
	movq	%rax, 88(%rsp)
	leaq	120(%rsp), %rdi
	movq	%r15, %rsi
	callq	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState11read_scalar
	cmpb	$0, 120(%rsp)
	je	.LBB61_14
	movq	128(%rsp), %r15
	movq	136(%rsp), %rax
	movq	%rax, 16(%rsp)
	movq	$0, 120(%rsp)
	movq	$0, 128(%rsp)
	movq	$0, 136(%rsp)
	movq	$0, 144(%rsp)
	movq	$0, 152(%rsp)
	movq	$0, 160(%rsp)
	movq	$0, 168(%rsp)
	movq	$0, 176(%rsp)
	movq	$0, 184(%rsp)
	movq	$0, 192(%rsp)
	movq	$0, 200(%rsp)
	movq	$0, 208(%rsp)
	movq	$0, 216(%rsp)
	movq	$0, 224(%rsp)
	movq	$0, 232(%rsp)
	movq	$0, 240(%rsp)
	movq	$0, 248(%rsp)
	movq	$0, 256(%rsp)
	movq	$0, 264(%rsp)
	movq	$0, 272(%rsp)
	movq	$0, 280(%rsp)
	movq	$0, 288(%rsp)
	movq	$0, 296(%rsp)
	movq	$0, 304(%rsp)
	movq	$0, 312(%rsp)
	movq	$0, 320(%rsp)
	movq	$0, 328(%rsp)
	movq	$0, 336(%rsp)
	movq	$0, 344(%rsp)
	movq	$0, 352(%rsp)
	movq	$0, 360(%rsp)
	movq	$0, 368(%rsp)
	leaq	24(%rsp), %rdi
	leaq	120(%rsp), %rdx
	movl	$4, %esi
	movl	$16, %ecx
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field9eq_kernel
	testb	$1, %al
	je	.LBB61_14
	leaq	120(%rsp), %rdi
	movl	$16, %esi
	movl	$16, %ecx
	movq	%r14, %rdx
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field3dot
	movq	%rax, %rdi
	movq	%rdx, %rsi
	movq	%r15, %rdx
	movq	16(%rsp), %rcx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	cmpq	%rax, 96(%rsp)
	jne	.LBB61_14
	cmpq	%rdx, 88(%rsp)
	jne	.LBB61_14
	leaq	4(%rbp), %rax
	movq	%rbp, %rcx
	shlq	$4, %rcx
	addq	%r12, %rcx
	testq	%rbp, %rbp
	je	.LBB61_11
	cmpq	$1, %rbp
	jne	.LBB61_12
	xorl	%edx, %edx
	jmp	.LBB61_10
.LBB61_14:
	movq	$0, (%rbx)
.LBB61_15:
	addq	$376, %rsp
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
.LBB61_12:
	.cfi_def_cfa_offset 432
	movl	%ebp, %esi
	andl	$62, %esi
	movl	$24, %edi
	xorl	%edx, %edx
	.p2align	4
.LBB61_13:
	movq	-24(%r13,%rdi), %r8
	movq	-16(%r13,%rdi), %r9
	movq	%r8, -24(%r12,%rdi)
	movq	%r9, -16(%r12,%rdi)
	addq	$2, %rdx
	movq	-8(%r13,%rdi), %r8
	movq	(%r13,%rdi), %r9
	movq	%r8, -8(%r12,%rdi)
	movq	%r9, (%r12,%rdi)
	addq	$32, %rdi
	cmpq	%rdx, %rsi
	jne	.LBB61_13
	testb	$1, %bpl
	je	.LBB61_11
.LBB61_10:
	shlq	$4, %rdx
	movq	(%r13,%rdx), %rsi
	movq	8(%r13,%rdx), %rdi
	movq	%rsi, (%r12,%rdx)
	movq	%rdi, 8(%r12,%rdx)
.LBB61_11:
	movq	24(%rsp), %rdx
	movq	32(%rsp), %rsi
	movq	%rdx, (%rcx)
	movq	%rsi, 8(%rcx)
	movq	40(%rsp), %rdx
	movq	48(%rsp), %rsi
	movq	%rdx, 16(%rcx)
	movq	%rsi, 24(%rcx)
	movq	56(%rsp), %rdx
	movq	64(%rsp), %rsi
	movq	%rdx, 32(%rcx)
	movq	%rsi, 40(%rcx)
	movq	72(%rsp), %rdx
	movq	80(%rsp), %rsi
	movq	%rdx, 48(%rcx)
	movq	%rsi, 56(%rcx)
	movq	112(%rsp), %rcx
	movq	%rcx, 8(%rbx)
	movq	104(%rsp), %rcx
	movq	%rcx, 16(%rbx)
	movq	%rax, 24(%rbx)
	movq	%r15, 32(%rbx)
	movq	16(%rsp), %rax
	movq	%rax, 40(%rbx)
	movq	$1, (%rbx)
	jmp	.LBB61_15
.Lfunc_end61:
	.size	_RNvNtCsemcRClSg8DH_9native_vm3bus14bytecode_share, .Lfunc_end61-_RNvNtCsemcRClSg8DH_9native_vm3bus14bytecode_share
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm3bus15accumulate_side,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm3bus15accumulate_side,@function
_RNvNtCsemcRClSg8DH_9native_vm3bus15accumulate_side:
.Lfunc_begin62:
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
	subq	$3784, %rsp
	.cfi_def_cfa_offset 12032
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	%r9, 96(%rsp)
	movq	%r8, 32(%rsp)
	movq	%rcx, 88(%rsp)
	movq	%rdx, 8(%rsp)
	movq	%rsi, 80(%rsp)
	movq	%rdi, 72(%rsp)
	movq	12112(%rsp), %rax
	movq	%rax, 64(%rsp)
	movq	12104(%rsp), %rax
	movq	%rax, 56(%rsp)
	movq	12096(%rsp), %rbp
	movq	12032(%rsp), %rcx
	movq	8(%rcx), %rax
	leaq	16(%rcx), %r12
	xorl	%r13d, %r13d
	cmpq	$4, %rax
	movl	$8, %r9d
	cmovaeq	%r9, %r12
	cmovbq	%rax, %r13
	movq	12048(%rsp), %rdx
	cmpq	%r13, %rdx
	cmovaeq	%r13, %rdx
	movq	12088(%rsp), %rdi
	movq	12080(%rsp), %r8
	movq	12072(%rsp), %rax
	movq	%rdx, 16(%rsp)
	testq	%rdx, %rdx
	je	.LBB62_4
	movq	%r13, 48(%rsp)
	shlq	$4, 16(%rsp)
	xorl	%ebp, %ebp
	xorl	%r13d, %r13d
	xorl	%r15d, %r15d
	.p2align	4
.LBB62_2:
	movq	(%r12,%rbp), %rcx
	movq	8(%r12,%rbp), %rsi
	movq	%rcx, %rdx
	shlq	$4, %rdx
	addq	%rdi, %rdx
	movq	12096(%rsp), %rdi
	subq	%rcx, %rdi
	cmovbq	%r9, %rdx
	movl	$0, %r9d
	cmovbq	%r9, %rdi
	shrq	%cl, %rsi
	cmpq	$64, %rcx
	cmovaeq	%r9, %rsi
	movq	12040(%rsp), %rcx
	movq	(%rcx,%rbp), %rbx
	xorq	%rax, %rbx
	movq	8(%rcx,%rbp), %r14
	xorq	%r8, %r14
	movq	%rdi, %rcx
	callq	_RINvNtCsemcRClSg8DH_9native_vm5field10eq_eval_fnNCNvNtB4_6layout8eq_above0EB4_
	movq	%rax, %rdi
	movq	%rdx, %rsi
	movq	%rbx, %rdx
	movq	%r14, %rcx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	movl	$8, %r9d
	movq	12080(%rsp), %r8
	movq	12088(%rsp), %rdi
	xorq	%rax, %r15
	movq	12072(%rsp), %rax
	xorq	%rdx, %r13
	addq	$16, %rbp
	cmpq	%rbp, 16(%rsp)
	jne	.LBB62_2
	xorq	%r15, 56(%rsp)
	xorq	%r13, 64(%rsp)
	movq	12096(%rsp), %rbp
	movq	48(%rsp), %r13
.LBB62_4:
	testq	%r13, %r13
	je	.LBB62_5
	shlq	$4, %r13
	addq	%r12, %r13
	movl	$1, %r14d
	xorl	%ebx, %ebx
	xorl	%r15d, %r15d
	.p2align	4
.LBB62_7:
	movq	(%r12), %rcx
	movq	8(%r12), %rsi
	movq	%rcx, %rdx
	shlq	$4, %rdx
	addq	%rdi, %rdx
	movq	%rbp, %rdi
	subq	%rcx, %rdi
	movl	$8, %eax
	cmovbq	%rax, %rdx
	cmovbq	%rbx, %rdi
	shrq	%cl, %rsi
	cmpq	$64, %rcx
	cmovaeq	%rbx, %rsi
	movq	%rdi, %rcx
	callq	_RINvNtCsemcRClSg8DH_9native_vm5field10eq_eval_fnNCNvNtB4_6layout8eq_above0EB4_
	movq	12088(%rsp), %rdi
	xorq	%rax, %r14
	xorq	%rdx, %r15
	addq	$16, %r12
	cmpq	%r13, %r12
	jne	.LBB62_7
	jmp	.LBB62_8
.LBB62_5:
	movl	$1, %r14d
	xorl	%r15d, %r15d
.LBB62_8:
	movl	$72, %eax
	.p2align	4
.LBB62_9:
	movq	$0, 56(%rsp,%rax)
	movq	$0, 64(%rsp,%rax)
	movq	$0, 72(%rsp,%rax)
	movq	$0, 80(%rsp,%rax)
	movq	$0, 88(%rsp,%rax)
	movq	$0, 96(%rsp,%rax)
	movq	$0, 104(%rsp,%rax)
	movq	$0, 112(%rsp,%rax)
	movq	$0, 120(%rsp,%rax)
	movq	$0, 128(%rsp,%rax)
	addq	$80, %rax
	cmpq	$5992, %rax
	jne	.LBB62_9
	leaq	6056(%rsp), %rdi
	leaq	128(%rsp), %rsi
	movl	$5920, %edx
	callq	*memcpy@GOTPCREL(%rip)
	movq	12032(%rsp), %rax
	movq	64(%rax), %rax
	movq	32(%rsp), %rcx
	cmpq	%rax, %rcx
	cmovaeq	%rax, %rcx
	decq	%rax
	cmpq	$50, %rax
	ja	.LBB62_11
	imulq	$5928, 8(%rsp), %rax
	addq	%rax, 80(%rsp)
	shlq	$4, %rcx
	xorl	%r8d, %r8d
	movl	$8, %r9d
	xorl	%r12d, %r12d
	xorl	%edx, %edx
	xorl	%esi, %esi
	movq	12088(%rsp), %rdi
	movq	%rcx, 32(%rsp)
	movq	%r8, 24(%rsp)
	.p2align	4
.LBB62_15:
	movq	%rdx, 120(%rsp)
	movq	%rsi, 48(%rsp)
	movq	12032(%rsp), %rax
	movq	72(%rax,%r12), %rcx
	movq	80(%rax,%r12), %rsi
	movq	%rcx, %rdx
	shlq	$4, %rdx
	addq	%rdi, %rdx
	movq	%rbp, %rdi
	subq	%rcx, %rdi
	cmovbq	%r9, %rdx
	cmovbq	%r8, %rdi
	shrq	%cl, %rsi
	cmpq	$64, %rcx
	cmovaeq	%r8, %rsi
	movq	%rdi, %rcx
	movq	$0, 24(%rsp)
	callq	_RINvNtCsemcRClSg8DH_9native_vm5field10eq_eval_fnNCNvNtB4_6layout8eq_above0EB4_
	movq	%rax, %r13
	movq	%rdx, %rbp
	movq	88(%rsp), %rax
	movq	8(%rax,%r12), %rdi
	movq	12056(%rsp), %rsi
	movq	12064(%rsp), %rdx
	movq	12072(%rsp), %rcx
	movq	12080(%rsp), %r8
	leaq	6048(%rsp), %r9
	callq	_RNvNtCsemcRClSg8DH_9native_vm3bus10block_form
	testb	%al, %al
	je	.LBB62_13
	movq	88(%rsp), %rax
	movq	(%rax,%r12), %rsi
	cmpq	$5, %rsi
	ja	.LBB62_17
	movq	%rbp, %r9
	movq	%r13, %r8
	leaq	(%rsi,%rsi,4), %rax
	leaq	.Lanon.a75d6d9e6a8990b4224ef13f18552af8.4(%rip), %rcx
	movq	%r12, 112(%rsp)
	movq	24(%rcx,%rax,8), %r12
	movq	32(%rcx,%rax,8), %rax
	movq	%rax, 16(%rsp)
	movq	%rsi, 40(%rsp)
	imulq	$17784, %rsi, %rdi
	addq	80(%rsp), %rdi
	movq	6048(%rsp), %r13
	cmpq	$149, %r13
	movl	$8, %ebp
	leaq	6056(%rsp), %rax
	cmovbq	%rax, %rbp
	movl	$0, %ecx
	cmovaeq	%rcx, %r13
	movq	%rbp, %rsi
	movq	%r13, %rdx
	movq	%r8, %rcx
	movq	%r8, %rbx
	movq	%r9, %r8
	movq	%r9, 8(%rsp)
	callq	_RNvMs0_NtCsemcRClSg8DH_9native_vm6layoutNtB5_7FormBuf10add_scaled
	testb	%al, %al
	je	.LBB62_13
	movq	%rbx, 104(%rsp)
	xorq	%rbx, %r14
	xorq	8(%rsp), %r15
	movq	16(%rsp), %rsi
	leaq	(%rsi,%r12), %rax
	cmpq	%r12, %rax
	setae	%cl
	cmpq	$154, %rax
	setb	%al
	shlq	$4, %r12
	leaq	.Lanon.a75d6d9e6a8990b4224ef13f18552af8.5(%rip), %rdx
	addq	%rdx, %r12
	testb	%al, %cl
	movl	$0, %eax
	cmoveq	%rax, %rsi
	movq	%rsi, 16(%rsp)
	movl	$8, %eax
	cmoveq	%rax, %r12
	movq	96(%rsp), %rax
	movq	40(%rsp), %rcx
	movq	24(%rax,%rcx,8), %rsi
	movq	72(%rax,%rcx,8), %rdx
	movq	12096(%rsp), %rbx
	cmpq	%rbx, %rsi
	cmovaeq	%rbx, %rsi
	movq	12088(%rsp), %rdi
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field14padding_weight
	movq	%rdx, %rcx
	movq	104(%rsp), %rdi
	movq	8(%rsp), %rsi
	movq	%rax, %rdx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	movq	%rax, 8(%rsp)
	movq	%rdx, 40(%rsp)
	movq	%rbp, %rdi
	movq	%rbx, %rbp
	movq	%r13, %rsi
	movq	%r12, %rdx
	movq	16(%rsp), %rcx
	callq	_RNvNtCsemcRClSg8DH_9native_vm6layout8evaluate
	movq	%rdx, %rcx
	xorq	$1, %rax
	movq	8(%rsp), %rdi
	movq	40(%rsp), %rsi
	movq	%rax, %rdx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	movq	12088(%rsp), %rdi
	movl	$8, %r9d
	movq	48(%rsp), %rsi
	xorq	%rax, %rsi
	movq	120(%rsp), %rax
	xorq	%rdx, %rax
	movq	%rax, %rdx
	movq	112(%rsp), %r12
	addq	$16, %r12
	movq	32(%rsp), %rcx
	cmpq	%r12, %rcx
	movl	$0, %r8d
	jne	.LBB62_15
	jmp	.LBB62_12
.LBB62_11:
	xorl	%esi, %esi
	xorl	%edx, %edx
.LBB62_12:
	movq	64(%rsp), %rcx
	xorq	%r15, %rcx
	xorq	%rdx, %rcx
	movq	56(%rsp), %rdx
	xorq	%r14, %rdx
	xorq	%rsi, %rdx
	movq	72(%rsp), %rax
	movq	%rdx, 8(%rax)
	movq	%rcx, 16(%rax)
	movl	$1, %eax
	movq	%rax, 24(%rsp)
.LBB62_13:
	movq	72(%rsp), %rax
	movq	24(%rsp), %rcx
	movq	%rcx, (%rax)
	addq	$11976, %rsp
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
.LBB62_17:
	.cfi_def_cfa_offset 12032
	movq	$0, 24(%rsp)
	jmp	.LBB62_13
.Lfunc_end62:
	.size	_RNvNtCsemcRClSg8DH_9native_vm3bus15accumulate_side, .Lfunc_end62-_RNvNtCsemcRClSg8DH_9native_vm3bus15accumulate_side
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm3bus18verify_bus_balance,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm3bus18verify_bus_balance,@function
_RNvNtCsemcRClSg8DH_9native_vm3bus18verify_bus_balance:
.Lfunc_begin63:
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
	subq	$1272, %rsp
	.cfi_def_cfa_offset 5424
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	%r9, %r15
	movq	%r8, %r12
	movq	%rcx, 32(%rsp)
	movq	%rdx, 24(%rsp)
	movq	%rsi, %r14
	movq	%rdi, %rbx
	movq	(%rsi), %rbp
	movq	8(%rsi), %r13
	movq	$0, 224(%rsp)
	movq	%rbp, 232(%rsp)
	movq	%r13, 240(%rsp)
	leaq	.Lanon.a75d6d9e6a8990b4224ef13f18552af8.6(%rip), %rcx
	leaq	568(%rsp), %rdi
	leaq	224(%rsp), %rsi
	movl	$3, %edx
	movl	$51, %r8d
	movq	%r14, %r9
	callq	_RNvNtCsemcRClSg8DH_9native_vm3bus10bus_layout
	cmpl	$1, 568(%rsp)
	jne	.LBB63_27
	movq	%r12, 8(%rsp)
	movq	576(%rsp), %r12
	leaq	584(%rsp), %rsi
	leaq	2712(%rsp), %rdi
	movl	$880, %edx
	callq	*memcpy@GOTPCREL(%rip)
	movq	%r12, 2704(%rsp)
	leaq	.Lanon.a75d6d9e6a8990b4224ef13f18552af8.7(%rip), %rcx
	leaq	568(%rsp), %rdi
	leaq	224(%rsp), %rsi
	movl	$3, %edx
	movl	$51, %r8d
	movq	%r14, %r9
	callq	_RNvNtCsemcRClSg8DH_9native_vm3bus10bus_layout
	cmpb	$0, 568(%rsp)
	je	.LBB63_27
	leaq	576(%rsp), %rsi
	leaq	3592(%rsp), %rdi
	movl	$888, %edx
	callq	*memcpy@GOTPCREL(%rip)
	leaq	.Lanon.a75d6d9e6a8990b4224ef13f18552af8.8(%rip), %rcx
	leaq	568(%rsp), %rdi
	movl	$8, %esi
	movl	$45, %r8d
	xorl	%edx, %edx
	movq	%r14, %r9
	callq	_RNvNtCsemcRClSg8DH_9native_vm3bus10bus_layout
	cmpb	$0, 568(%rsp)
	je	.LBB63_27
	leaq	576(%rsp), %rsi
	leaq	4480(%rsp), %rdi
	movl	$888, %edx
	callq	*memcpy@GOTPCREL(%rip)
	cmpq	$64, %r12
	jae	.LBB63_27
	movq	$-1, %rdi
	movl	%r12d, %ecx
	shlq	%cl, %rdi
	notq	%rdi
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field10bit_length
	xorl	%esi, %esi
	subl	$3, %eax
	cmovael	%eax, %esi
	movq	%rbx, %rdi
	callq	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState5grind
	testb	%al, %al
	je	.LBB63_27
	movq	$0, 264(%rsp)
	movq	$0, 272(%rsp)
	movq	$0, 280(%rsp)
	movq	$0, 288(%rsp)
	movq	$0, 296(%rsp)
	movq	$0, 304(%rsp)
	movq	$0, 312(%rsp)
	movq	$0, 320(%rsp)
	movq	$0, 328(%rsp)
	movq	$0, 336(%rsp)
	movq	$0, 344(%rsp)
	movq	$0, 352(%rsp)
	movq	$0, 360(%rsp)
	movq	$0, 368(%rsp)
	movq	$0, 376(%rsp)
	movq	$0, 384(%rsp)
	movq	$0, 392(%rsp)
	movq	$0, 400(%rsp)
	movq	$0, 408(%rsp)
	movq	$0, 416(%rsp)
	movq	$0, 424(%rsp)
	movq	$0, 432(%rsp)
	movq	$0, 440(%rsp)
	movq	$0, 448(%rsp)
	movq	$0, 456(%rsp)
	movq	$0, 464(%rsp)
	movq	$0, 472(%rsp)
	movq	$0, 480(%rsp)
	movq	$0, 488(%rsp)
	movq	$0, 496(%rsp)
	movq	$0, 504(%rsp)
	movq	$0, 512(%rsp)
	leaq	264(%rsp), %rsi
	movl	$16, %edx
	movq	%rbx, %rdi
	callq	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState17sample_challenges
	movq	%rbx, %rdi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW7squeeze
	movq	%rax, 80(%rsp)
	movq	%rdx, 72(%rsp)
	movl	$40, %eax
	.p2align	4
.LBB63_6:
	movq	$0, 528(%rsp,%rax)
	movq	$0, 536(%rsp,%rax)
	movq	$0, 544(%rsp,%rax)
	movq	$0, 552(%rsp,%rax)
	movq	$0, 560(%rsp,%rax)
	movq	$0, 568(%rsp,%rax)
	addq	$48, %rax
	cmpq	$1048, %rax
	jne	.LBB63_6
	leaq	1696(%rsp), %rdi
	leaq	568(%rsp), %rsi
	movl	$1008, %edx
	callq	*memcpy@GOTPCREL(%rip)
	movq	$0, 1640(%rsp)
	movq	$0, 1648(%rsp)
	movq	$0, 1656(%rsp)
	movq	$0, 1664(%rsp)
	movq	$0, 1672(%rsp)
	movq	$0, 1680(%rsp)
	movq	$0, 1688(%rsp)
	leaq	568(%rsp), %rdi
	leaq	1640(%rsp), %rcx
	movq	%rbx, %rsi
	movq	%r12, %rdx
	callq	_RNvNtCsemcRClSg8DH_9native_vm3gkr25verify_gkr_grand_products
	cmpl	$1, 568(%rsp)
	jne	.LBB63_27
	movq	584(%rsp), %rax
	orq	576(%rsp), %rax
	je	.LBB63_27
	movq	1688(%rsp), %rax
	movq	$0, 112(%rsp)
	movq	$0, 120(%rsp)
	xorl	%r12d, %r12d
	cmpq	$64, %rax
	cmovbq	%rax, %r12
	movq	$0, 128(%rsp)
	movl	$8, %ecx
	leaq	1696(%rsp), %rax
	cmovbq	%rax, %rcx
	movq	%rcx, (%rsp)
	movq	$0, 136(%rsp)
	cmpq	%r12, %rbp
	cmovaeq	%r12, %rbp
	cmpq	%r12, %r13
	movq	%r12, 16(%rsp)
	cmovbq	%r13, %r12
	leaq	112(%rsp), %rsi
	movl	$2, %edx
	movq	%rbx, %rdi
	callq	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState12read_scalars
	testb	%al, %al
	je	.LBB63_27
	leaq	568(%rsp), %rdi
	movq	%rbx, %rsi
	callq	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState11read_scalar
	cmpb	$0, 568(%rsp)
	je	.LBB63_27
	movq	576(%rsp), %rax
	movq	%rax, 64(%rsp)
	movq	584(%rsp), %rax
	movq	%rax, 56(%rsp)
	leaq	568(%rsp), %rdi
	movq	%rbx, %rsi
	callq	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState11read_scalar
	cmpb	$0, 568(%rsp)
	je	.LBB63_27
	movq	576(%rsp), %rax
	movq	%rax, 48(%rsp)
	movq	584(%rsp), %rax
	movq	%rax, 40(%rsp)
	movq	$0, (%r15)
	movq	112(%rsp), %r8
	movq	120(%rsp), %r9
	movq	%r15, %rdi
	xorl	%esi, %esi
	movq	(%rsp), %rdx
	movq	%rbp, %rcx
	callq	_RNvNtCsemcRClSg8DH_9native_vm5stack10push_claim
	testb	%al, %al
	je	.LBB63_27
	movq	128(%rsp), %r8
	movq	136(%rsp), %r9
	movl	$1, %esi
	movq	%r15, %rdi
	movq	(%rsp), %rdx
	movq	%rbp, %rcx
	callq	_RNvNtCsemcRClSg8DH_9native_vm5stack10push_claim
	testb	%al, %al
	je	.LBB63_27
	movl	$2, %esi
	movq	%r15, %rdi
	movq	(%rsp), %rdx
	movq	%rbp, %rcx
	movq	64(%rsp), %r8
	movq	56(%rsp), %r9
	callq	_RNvNtCsemcRClSg8DH_9native_vm5stack10push_claim
	testb	%al, %al
	je	.LBB63_27
	movl	$3, %esi
	movq	%r15, %rdi
	movq	(%rsp), %rdx
	movq	%r12, %rcx
	movq	48(%rsp), %r8
	movq	40(%rsp), %r9
	callq	_RNvNtCsemcRClSg8DH_9native_vm5stack10push_claim
	testb	%al, %al
	je	.LBB63_27
	movl	$56, %eax
.LBB63_17:
	movq	$0, 512(%rsp,%rax)
	movq	$0, 520(%rsp,%rax)
	movq	$0, 528(%rsp,%rax)
	movq	$0, 536(%rsp,%rax)
	movq	$0, 544(%rsp,%rax)
	movq	$0, 552(%rsp,%rax)
	cmpq	$1080, %rax
	je	.LBB63_19
	movq	$0, 560(%rsp,%rax)
	movq	$0, 568(%rsp,%rax)
	addq	$64, %rax
	jmp	.LBB63_17
.LBB63_19:
	leaq	144(%rsp), %rdi
	leaq	264(%rsp), %r15
	leaq	568(%rsp), %r9
	movq	%rbx, %rsi
	movq	%r15, %rdx
	movq	(%rsp), %rcx
	movq	%r12, %r8
	callq	_RNvNtCsemcRClSg8DH_9native_vm3bus14bytecode_share
	cmpl	$1, 144(%rsp)
	jne	.LBB63_27
	movq	152(%rsp), %rax
	movq	160(%rsp), %rdx
	movq	168(%rsp), %rcx
	movq	176(%rsp), %r8
	movq	184(%rsp), %r9
	movq	%rax, 248(%rsp)
	movq	%rdx, 256(%rsp)
	cmpq	$68, %rcx
	jae	.LBB63_27
	leaq	568(%rsp), %rdx
	movq	24(%rsp), %rdi
	movq	32(%rsp), %rsi
	callq	_RNvNtCsemcRClSg8DH_9native_vm3bus23computed_bytecode_value
	testb	%al, %al
	je	.LBB63_27
	movq	%r15, 144(%rsp)
	leaq	112(%rsp), %rax
	movq	%rax, 152(%rsp)
	movq	(%rsp), %rbx
	movq	%rbx, 160(%rsp)
	movq	%rbp, 168(%rsp)
	movq	%rbx, 176(%rsp)
	movq	%r12, 184(%rsp)
	leaq	248(%rsp), %rax
	movq	%rax, 192(%rsp)
	movq	$-1, %rdi
	movl	%r13d, %ecx
	shlq	%cl, %rdi
	notq	%rdi
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field4kpow
	movq	%rax, 24(%rsp)
	movq	8(%rsp), %rbp
	movq	$0, (%rbp)
	movq	$0, 5928(%rbp)
	movq	$0, 11856(%rbp)
	movq	$0, 17784(%rbp)
	movq	$0, 23712(%rbp)
	movq	$0, 29640(%rbp)
	movq	$0, 35568(%rbp)
	movq	$0, 41496(%rbp)
	movq	$0, 47424(%rbp)
	movq	$0, 53352(%rbp)
	movq	$0, 59280(%rbp)
	movq	$0, 65208(%rbp)
	movq	$0, 71136(%rbp)
	movq	$0, 77064(%rbp)
	movq	$0, 82992(%rbp)
	movq	$0, 88920(%rbp)
	movq	$0, 94848(%rbp)
	movq	$0, 100776(%rbp)
	movq	1640(%rsp), %r13
	movq	1648(%rsp), %r12
	movq	1656(%rsp), %rax
	movq	%rax, 32(%rsp)
	movq	1664(%rsp), %rax
	movq	%rax, 216(%rsp)
	movq	1672(%rsp), %rax
	movq	%rax, 208(%rsp)
	movq	1680(%rsp), %rax
	movq	%rax, 200(%rsp)
	xorl	%edi, %edi
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field4kpow
	subq	$8, %rsp
	.cfi_adjust_cfa_offset 8
	leaq	528(%rsp), %rdi
	leaq	152(%rsp), %rsi
	movl	$1, %ecx
	movl	$1, %r9d
	movq	%rax, %rdx
	xorl	%r8d, %r8d
	pushq	$0
	.cfi_adjust_cfa_offset 8
	callq	_RNCNvNtCsemcRClSg8DH_9native_vm3bus18verify_bus_balance0B5_
	addq	$8, %rsp
	.cfi_adjust_cfa_offset -8
	leaq	2712(%rsp), %rax
	leaq	.Lanon.a75d6d9e6a8990b4224ef13f18552af8.6(%rip), %rcx
	leaq	96(%rsp), %rdi
	movl	$51, %r8d
	movq	%rbp, %rsi
	xorl	%edx, %edx
	movq	%r14, %r9
	pushq	%r12
	.cfi_adjust_cfa_offset 8
	pushq	%r13
	.cfi_adjust_cfa_offset 8
	pushq	40(%rsp)
	.cfi_adjust_cfa_offset 8
	pushq	%rbx
	.cfi_adjust_cfa_offset 8
	pushq	112(%rsp)
	.cfi_adjust_cfa_offset 8
	pushq	128(%rsp)
	.cfi_adjust_cfa_offset 8
	pushq	$16
	.cfi_adjust_cfa_offset 8
	pushq	%r15
	.cfi_adjust_cfa_offset 8
	pushq	$3
	.cfi_adjust_cfa_offset 8
	leaq	600(%rsp), %r10
	movq	%r10, %rbx
	pushq	%r10
	.cfi_adjust_cfa_offset 8
	pushq	%rax
	.cfi_adjust_cfa_offset 8
	callq	_RNvNtCsemcRClSg8DH_9native_vm3bus15accumulate_side
	addq	$96, %rsp
	.cfi_adjust_cfa_offset -96
	cmpl	$1, 88(%rsp)
	jne	.LBB63_27
	movq	96(%rsp), %r13
	movq	104(%rsp), %rbp
	subq	$8, %rsp
	.cfi_adjust_cfa_offset 8
	leaq	152(%rsp), %rsi
	movq	%rbx, %rdi
	movq	32(%rsp), %rdx
	movq	72(%rsp), %rcx
	movq	64(%rsp), %r8
	movq	56(%rsp), %r9
	pushq	48(%rsp)
	.cfi_adjust_cfa_offset 8
	callq	_RNCNvNtCsemcRClSg8DH_9native_vm3bus18verify_bus_balance0B5_
	addq	$8, %rsp
	.cfi_adjust_cfa_offset -8
	leaq	.Lanon.a75d6d9e6a8990b4224ef13f18552af8.7(%rip), %rcx
	leaq	96(%rsp), %rdi
	movl	$1, %edx
	movl	$51, %r8d
	movq	16(%rsp), %rsi
	movq	%r14, %r9
	pushq	224(%rsp)
	.cfi_adjust_cfa_offset 8
	pushq	48(%rsp)
	.cfi_adjust_cfa_offset 8
	pushq	40(%rsp)
	.cfi_adjust_cfa_offset 8
	pushq	32(%rsp)
	.cfi_adjust_cfa_offset 8
	pushq	112(%rsp)
	.cfi_adjust_cfa_offset 8
	pushq	128(%rsp)
	.cfi_adjust_cfa_offset 8
	pushq	$16
	.cfi_adjust_cfa_offset 8
	pushq	%r15
	.cfi_adjust_cfa_offset 8
	pushq	$3
	.cfi_adjust_cfa_offset 8
	pushq	%rbx
	.cfi_adjust_cfa_offset 8
	leaq	3680(%rsp), %rax
	pushq	%rax
	.cfi_adjust_cfa_offset 8
	callq	_RNvNtCsemcRClSg8DH_9native_vm3bus15accumulate_side
	addq	$96, %rsp
	.cfi_adjust_cfa_offset -96
	cmpb	$0, 88(%rsp)
	je	.LBB63_27
	movq	96(%rsp), %rbx
	movq	104(%rsp), %r15
	subq	$8, %rsp
	.cfi_adjust_cfa_offset 8
	leaq	.Lanon.a75d6d9e6a8990b4224ef13f18552af8.9(%rip), %rax
	leaq	.Lanon.a75d6d9e6a8990b4224ef13f18552af8.8(%rip), %rcx
	leaq	528(%rsp), %rdi
	movl	$2, %edx
	movl	$45, %r8d
	movq	16(%rsp), %rsi
	movq	%r14, %r9
	pushq	208(%rsp)
	.cfi_adjust_cfa_offset 8
	pushq	224(%rsp)
	.cfi_adjust_cfa_offset 8
	pushq	40(%rsp)
	.cfi_adjust_cfa_offset 8
	pushq	32(%rsp)
	.cfi_adjust_cfa_offset 8
	pushq	$0
	.cfi_adjust_cfa_offset 8
	pushq	$0
	.cfi_adjust_cfa_offset 8
	pushq	$1
	.cfi_adjust_cfa_offset 8
	pushq	%rax
	.cfi_adjust_cfa_offset 8
	pushq	$0
	.cfi_adjust_cfa_offset 8
	pushq	$8
	.cfi_adjust_cfa_offset 8
	leaq	4568(%rsp), %rax
	pushq	%rax
	.cfi_adjust_cfa_offset 8
	callq	_RNvNtCsemcRClSg8DH_9native_vm3bus15accumulate_side
	addq	$96, %rsp
	.cfi_adjust_cfa_offset -96
	cmpb	$0, 520(%rsp)
	je	.LBB63_27
	movq	8(%rsp), %rax
	leaq	106704(%rax), %rdi
	movq	528(%rsp), %r14
	movq	536(%rsp), %r12
	movq	$0, (%rdi)
	movq	(%rsp), %rsi
	movq	16(%rsp), %rdx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKj3f_E6extendB4_
	testb	%al, %al
	je	.LBB63_27
	movq	8(%rsp), %rax
	movq	%r13, 107720(%rax)
	movq	%rbp, 107728(%rax)
	movq	%rbx, 107736(%rax)
	movq	%r15, 107744(%rax)
	movq	%r14, 107752(%rax)
	movq	%r12, 107760(%rax)
	movb	$1, %al
	jmp	.LBB63_28
.LBB63_27:
	xorl	%eax, %eax
.LBB63_28:
	addq	$5368, %rsp
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
.Lfunc_end63:
	.size	_RNvNtCsemcRClSg8DH_9native_vm3bus18verify_bus_balance, .Lfunc_end63-_RNvNtCsemcRClSg8DH_9native_vm3bus18verify_bus_balance
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm3bus23computed_bytecode_value,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm3bus23computed_bytecode_value,@function
_RNvNtCsemcRClSg8DH_9native_vm3bus23computed_bytecode_value:
.Lfunc_begin64:
	.cfi_startproc
	pushq	%r14
	.cfi_def_cfa_offset 16
	pushq	%rbx
	.cfi_def_cfa_offset 24
	pushq	%rax
	.cfi_def_cfa_offset 32
	.cfi_offset %rbx, -24
	.cfi_offset %r14, -16
	movq	%r9, %rbx
	movq	%r8, %r14
	movq	%rcx, %r8
	movq	%rdx, %rcx
	movq	%rsi, %rdx
	movq	%rdi, %rsi
	movq	%rdx, %rdi
	callq	_RINvNtCsemcRClSg8DH_9native_vm5field19multilinear_eval_byNCNvNtB4_3bus23computed_bytecode_value0EB4_
	xorq	%r14, %rax
	xorq	%rbx, %rdx
	orq	%rax, %rdx
	sete	%al
	addq	$8, %rsp
	.cfi_def_cfa_offset 24
	popq	%rbx
	.cfi_def_cfa_offset 16
	popq	%r14
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end64:
	.size	_RNvNtCsemcRClSg8DH_9native_vm3bus23computed_bytecode_value, .Lfunc_end64-_RNvNtCsemcRClSg8DH_9native_vm3bus23computed_bytecode_value
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm3gkr10gkr_layers,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm3gkr10gkr_layers,@function
_RNvNtCsemcRClSg8DH_9native_vm3gkr10gkr_layers:
.Lfunc_begin65:
	.cfi_startproc
	pushq	%r15
	.cfi_def_cfa_offset 16
	pushq	%r14
	.cfi_def_cfa_offset 24
	pushq	%r12
	.cfi_def_cfa_offset 32
	pushq	%rbx
	.cfi_def_cfa_offset 40
	pushq	%rax
	.cfi_def_cfa_offset 48
	.cfi_offset %rbx, -40
	.cfi_offset %r12, -32
	.cfi_offset %r14, -24
	.cfi_offset %r15, -16
	movb	$1, %bl
	testq	%rsi, %rsi
	je	.LBB65_11
	movq	%rdx, %r14
	movq	%rsi, %r12
	movq	%rdi, %r15
	jmp	.LBB65_4
	.p2align	4
.LBB65_2:
	xorl	%edx, %edx
	addq	$-2, %r12
	sete	%dl
	movl	$2, %esi
	movq	%r15, %rdi
	movq	%r14, %rcx
	callq	_RNvNtCsemcRClSg8DH_9native_vm3gkr8gkr_step
	testb	%al, %al
	je	.LBB65_10
	testq	%r12, %r12
	je	.LBB65_11
.LBB65_4:
	cmpq	$1, %r12
	je	.LBB65_8
	testb	$1, %r12b
	je	.LBB65_2
	movl	$1, %esi
	movq	%r15, %rdi
	xorl	%edx, %edx
	movq	%r14, %rcx
	callq	_RNvNtCsemcRClSg8DH_9native_vm3gkr8gkr_step
	testb	%al, %al
	je	.LBB65_10
	decq	%r12
	testq	%r12, %r12
	jne	.LBB65_4
	jmp	.LBB65_11
.LBB65_8:
	movl	$1, %esi
	movq	%r15, %rdi
	movl	$1, %edx
	movq	%r14, %rcx
	addq	$8, %rsp
	.cfi_def_cfa_offset 40
	popq	%rbx
	.cfi_def_cfa_offset 32
	popq	%r12
	.cfi_def_cfa_offset 24
	popq	%r14
	.cfi_def_cfa_offset 16
	popq	%r15
	.cfi_def_cfa_offset 8
	jmp	_RNvNtCsemcRClSg8DH_9native_vm3gkr8gkr_step
.LBB65_10:
	.cfi_def_cfa_offset 48
	xorl	%ebx, %ebx
.LBB65_11:
	movl	%ebx, %eax
	addq	$8, %rsp
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
.Lfunc_end65:
	.size	_RNvNtCsemcRClSg8DH_9native_vm3gkr10gkr_layers, .Lfunc_end65-_RNvNtCsemcRClSg8DH_9native_vm3gkr10gkr_layers
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm3gkr25verify_gkr_grand_products,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm3gkr25verify_gkr_grand_products,@function
_RNvNtCsemcRClSg8DH_9native_vm3gkr25verify_gkr_grand_products:
.Lfunc_begin66:
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
	subq	$24, %rsp
	.cfi_def_cfa_offset 80
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	%rcx, %r14
	movq	%rdx, %r15
	movq	%rsi, %r12
	movq	%rdi, %rbx
	movq	%rsp, %rdi
	callq	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState11read_scalar
	cmpl	$1, (%rsp)
	jne	.LBB66_5
	movq	8(%rsp), %r13
	movq	16(%rsp), %rbp
	movq	%rsp, %rdi
	movq	%r12, %rsi
	callq	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState11read_scalar
	cmpb	$0, (%rsp)
	je	.LBB66_5
	movq	8(%rsp), %rax
	movq	16(%rsp), %rcx
	movq	%r13, (%r14)
	movq	%rbp, 8(%r14)
	movq	%r13, 16(%r14)
	movq	%rax, %r13
	movq	%rbp, 24(%r14)
	movq	%rcx, %rbp
	movq	%rax, 32(%r14)
	movq	%rcx, 40(%r14)
	movq	$0, 48(%r14)
	movq	%r12, %rdi
	movq	%r15, %rsi
	movq	%r14, %rdx
	callq	_RNvNtCsemcRClSg8DH_9native_vm3gkr10gkr_layers
	testb	%al, %al
	je	.LBB66_5
	movq	%r13, 8(%rbx)
	movq	%rbp, 16(%rbx)
	movl	$1, %eax
	jmp	.LBB66_6
.LBB66_5:
	xorl	%eax, %eax
.LBB66_6:
	movq	%rax, (%rbx)
	addq	$24, %rsp
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
.Lfunc_end66:
	.size	_RNvNtCsemcRClSg8DH_9native_vm3gkr25verify_gkr_grand_products, .Lfunc_end66-_RNvNtCsemcRClSg8DH_9native_vm3gkr25verify_gkr_grand_products
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm3gkr8gkr_step,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm3gkr8gkr_step,@function
_RNvNtCsemcRClSg8DH_9native_vm3gkr8gkr_step:
.Lfunc_begin67:
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
	subq	$1320, %rsp
	.cfi_def_cfa_offset 1376
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	%rcx, %r14
	movl	%edx, %r12d
	movq	%rsi, %rbx
	movq	%rdi, %r15
	movl	$1, %edi
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field10bit_length
	xorl	%ebp, %ebp
	subl	$3, %eax
	cmovbl	%ebp, %eax
	movq	%r15, %rdi
	movl	%eax, %esi
	callq	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState5grind
	testb	%al, %al
	je	.LBB67_18
	movl	%r12d, 4(%rsp)
	movq	%r15, %rdi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW7squeeze
	movq	%rdx, %rbp
	movl	$3, %esi
	movq	%r14, %rdi
	movq	%rax, 64(%rsp)
	movq	%rax, %rdx
	movq	%rbp, %rcx
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field9poly_eval
	movq	%rdx, %r10
	movl	$40, %ecx
	.p2align	4
.LBB67_2:
	movq	$0, 272(%rsp,%rcx)
	movq	$0, 280(%rsp,%rcx)
	movq	$0, 288(%rsp,%rcx)
	movq	$0, 296(%rsp,%rcx)
	movq	$0, 304(%rsp,%rcx)
	movq	$0, 312(%rsp,%rcx)
	addq	$48, %rcx
	cmpq	$1048, %rcx
	jne	.LBB67_2
	leaq	56(%r14), %rdx
	movq	48(%r14), %rcx
	xorl	%r13d, %r13d
	cmpq	$64, %rcx
	movl	$8, %r9d
	movq	%rdx, 56(%rsp)
	cmovbq	%rdx, %r9
	cmovbq	%rcx, %r13
	movl	$1, %r8d
	movl	$1, %r12d
	movl	%ebx, %ecx
	shlq	%cl, %r12
	btsq	%rbx, %r8
	subq	$8, %rsp
	.cfi_adjust_cfa_offset 8
	leaq	320(%rsp), %r11
	leaq	80(%rsp), %rdi
	movq	%r15, %rsi
	movq	%rax, %rdx
	movq	%r10, %rcx
	pushq	%r13
	.cfi_adjust_cfa_offset 8
	pushq	%r11
	.cfi_adjust_cfa_offset 8
	pushq	%r13
	.cfi_adjust_cfa_offset 8
	callq	_RINvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB6_6TState8sumcheckNCNvNtB8_3gkr8gkr_step0EB8_
	addq	$32, %rsp
	.cfi_adjust_cfa_offset -32
	cmpl	$1, 72(%rsp)
	jne	.LBB67_17
	movq	80(%rsp), %rax
	movq	%rax, 48(%rsp)
	movq	88(%rsp), %rax
	movq	%rax, 40(%rsp)
	movq	$0, 72(%rsp)
	movq	$0, 80(%rsp)
	movq	$0, 88(%rsp)
	movq	$0, 96(%rsp)
	movq	$0, 104(%rsp)
	movq	$0, 112(%rsp)
	movq	$0, 120(%rsp)
	movq	$0, 128(%rsp)
	movq	$0, 136(%rsp)
	movq	$0, 144(%rsp)
	movq	$0, 152(%rsp)
	movq	$0, 160(%rsp)
	movq	$0, 168(%rsp)
	movq	$0, 176(%rsp)
	movq	$0, 184(%rsp)
	movq	$0, 192(%rsp)
	movq	$0, 200(%rsp)
	movq	$0, 208(%rsp)
	movq	$0, 216(%rsp)
	movq	$0, 224(%rsp)
	movq	$0, 232(%rsp)
	movq	$0, 240(%rsp)
	movq	$0, 248(%rsp)
	movq	$0, 256(%rsp)
	leaq	72(%rsp), %rsi
	movq	%r15, %rdi
	movq	%r12, %rdx
	callq	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState12read_scalars
	testb	%al, %al
	je	.LBB67_17
	leaq	136(%rsp), %rsi
	movq	%r15, %rdi
	movq	%r12, %rdx
	callq	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState12read_scalars
	testb	%al, %al
	je	.LBB67_17
	leaq	200(%rsp), %rsi
	movq	%r15, %rdi
	movq	%r12, %rdx
	callq	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState12read_scalars
	testb	%al, %al
	je	.LBB67_17
	leaq	72(%rsp), %rdi
	movq	%r12, %rsi
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field6prod_e
	movq	%rax, 264(%rsp)
	movq	%rdx, 272(%rsp)
	leaq	136(%rsp), %rdi
	movq	%r12, %rsi
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field6prod_e
	movq	%rax, 280(%rsp)
	movq	%rdx, 288(%rsp)
	leaq	200(%rsp), %rdi
	movq	%r12, %rsi
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field6prod_e
	movq	%rax, 296(%rsp)
	movq	%rdx, 304(%rsp)
	leaq	264(%rsp), %rdi
	movl	$3, %esi
	movq	64(%rsp), %rdx
	movq	%rbp, %rcx
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field9poly_eval
	cmpq	%rax, 48(%rsp)
	jne	.LBB67_17
	cmpq	%rdx, 40(%rsp)
	jne	.LBB67_17
	movq	%rbx, %rdi
	movl	4(%rsp), %ecx
	shlq	%cl, %rdi
	decq	%rdi
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field10bit_length
	xorl	%esi, %esi
	subl	$3, %eax
	cmovael	%eax, %esi
	movq	%r15, %rdi
	callq	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState5grind
	testb	%al, %al
	je	.LBB67_17
	movq	$0, 8(%rsp)
	movq	$0, 16(%rsp)
	movq	$0, 24(%rsp)
	movq	$0, 32(%rsp)
	leaq	8(%rsp), %rbp
	movq	%r15, %rdi
	movq	%rbp, %rsi
	movq	%rbx, %rdx
	callq	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState17sample_challenges
	leaq	72(%rsp), %rsi
	movq	%r12, %rdi
	movq	%r12, %rdx
	movq	%rbp, %rcx
	movq	%rbx, %r8
	callq	_RINvNtCsemcRClSg8DH_9native_vm5field19multilinear_eval_byNCNvB2_16multilinear_eval0EB4_
	movq	%rax, (%r14)
	movq	%rdx, 8(%r14)
	movq	%r12, %rdi
	leaq	136(%rsp), %rsi
	movq	%r12, %rdx
	movq	%rbp, %rcx
	movq	%rbx, %r8
	callq	_RINvNtCsemcRClSg8DH_9native_vm5field19multilinear_eval_byNCNvB2_16multilinear_eval0EB4_
	movq	%rax, 16(%r14)
	movq	%rdx, 24(%r14)
	movq	%r12, %rdi
	leaq	200(%rsp), %rsi
	movq	%r12, %rdx
	movq	%rbp, %rcx
	movq	%rbx, %r8
	callq	_RINvNtCsemcRClSg8DH_9native_vm5field19multilinear_eval_byNCNvB2_16multilinear_eval0EB4_
	movq	%rax, 32(%r14)
	movq	%rdx, 40(%r14)
	leaq	(%rbx,%r13), %rax
	cmpq	$63, %rax
	ja	.LBB67_17
	movq	%rax, 48(%r14)
	movq	8(%rsp), %rax
	movq	16(%rsp), %rcx
	movq	%rax, 56(%r14)
	movq	%rcx, 64(%r14)
	cmpq	$1, %rbx
	je	.LBB67_13
	movq	24(%rsp), %rax
	movq	32(%rsp), %rcx
	movq	%rax, 72(%r14)
	movq	%rcx, 80(%r14)
.LBB67_13:
	testq	%r13, %r13
	je	.LBB67_23
	shlq	$4, %rbx
	cmpq	$1, %r13
	jne	.LBB67_19
	xorl	%eax, %eax
	jmp	.LBB67_22
.LBB67_17:
	xorl	%ebp, %ebp
.LBB67_18:
	movl	%ebp, %eax
	addq	$1320, %rsp
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
.LBB67_19:
	.cfi_def_cfa_offset 1376
	movl	%r13d, %ecx
	andl	$62, %ecx
	addq	%rbx, %r14
	movl	$56, %edx
	xorl	%eax, %eax
.LBB67_20:
	movq	256(%rsp,%rdx), %rsi
	movq	264(%rsp,%rdx), %rdi
	movq	%rsi, (%r14,%rdx)
	movq	%rdi, 8(%r14,%rdx)
	addq	$2, %rax
	movq	272(%rsp,%rdx), %rsi
	movq	280(%rsp,%rdx), %rdi
	movq	%rsi, 16(%r14,%rdx)
	movq	%rdi, 24(%r14,%rdx)
	addq	$32, %rdx
	cmpq	%rax, %rcx
	jne	.LBB67_20
	testb	$1, %r13b
	je	.LBB67_23
.LBB67_22:
	movq	56(%rsp), %rsi
	addq	%rbx, %rsi
	shlq	$4, %rax
	movq	312(%rsp,%rax), %rcx
	movq	320(%rsp,%rax), %rdx
	movq	%rcx, (%rsi,%rax)
	movq	%rdx, 8(%rsi,%rax)
.LBB67_23:
	movb	$1, %bpl
	jmp	.LBB67_18
.Lfunc_end67:
	.size	_RNvNtCsemcRClSg8DH_9native_vm3gkr8gkr_step, .Lfunc_end67-_RNvNtCsemcRClSg8DH_9native_vm3gkr8gkr_step
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm4whir10fold_round,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm4whir10fold_round,@function
_RNvNtCsemcRClSg8DH_9native_vm4whir10fold_round:
.Lfunc_begin68:
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
	subq	$120, %rsp
	.cfi_def_cfa_offset 176
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	%rdx, %r14
	movq	%rsi, %r13
	movq	%rdi, %rbx
	movq	%rsp, %rdi
	callq	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState11read_scalar
	cmpl	$1, (%rsp)
	jne	.LBB68_7
	movq	8(%rsp), %r12
	movq	16(%rsp), %rbp
	movq	%rsp, %rdi
	movq	%r13, %rsi
	callq	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState11read_scalar
	cmpb	$0, (%rsp)
	je	.LBB68_7
	movq	8(%rsp), %r15
	movq	16(%rsp), %rax
	movq	%rax, 56(%rsp)
	movq	%rsp, %rdi
	movq	%r13, %rsi
	callq	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState11read_scalar
	cmpb	$0, (%rsp)
	je	.LBB68_7
	movq	8(%rsp), %rax
	movq	%rax, 64(%rsp)
	movq	16(%rsp), %rax
	movq	%rax, 72(%rsp)
	movq	%rsp, %rdi
	movq	%r13, %rsi
	callq	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState11read_scalar
	cmpb	$0, (%rsp)
	je	.LBB68_7
	movq	8(%rsp), %rax
	movq	%rax, 112(%rsp)
	movq	16(%rsp), %rax
	movq	%rax, 104(%rsp)
	movq	%r13, %rdi
	movl	$7, %esi
	callq	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState5grind
	testb	%al, %al
	je	.LBB68_7
	movq	%r13, %rdi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW7squeeze
	movq	%rax, 48(%rsp)
	movq	%rdx, 24(%rsp)
	movq	%r13, %rdi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW7squeeze
	movq	%rax, 40(%rsp)
	movq	%rdx, 32(%rsp)
	movq	(%r14), %rdx
	xorq	%r12, %rdx
	movq	8(%r14), %rcx
	xorq	%rbp, %rcx
	movq	48(%rsp), %r13
	movq	%r13, %rdi
	movq	24(%rsp), %rsi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	movq	%rax, 88(%rsp)
	movq	%rdx, 96(%rsp)
	movq	%r13, %rdi
	movq	24(%rsp), %rcx
	movq	%rcx, %rsi
	movq	%r13, %rdx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	movq	%rax, %rdi
	movq	%rdx, %rsi
	movq	%r15, %rdx
	movq	56(%rsp), %rcx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	movq	%rax, 80(%rsp)
	movq	%rdx, 56(%rsp)
	movq	40(%rsp), %rdi
	movq	32(%rsp), %rsi
	movq	64(%rsp), %rdx
	movq	72(%rsp), %rcx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	movq	%rax, %r15
	movq	%rdx, %r13
	movq	48(%rsp), %rdi
	movq	24(%rsp), %rsi
	movq	40(%rsp), %rdx
	movq	32(%rsp), %rcx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	movq	112(%rsp), %r8
	xorq	64(%rsp), %r8
	movq	104(%rsp), %rcx
	xorq	72(%rsp), %rcx
	movq	%rax, %rdi
	movq	%rdx, %rsi
	movq	%r8, %rdx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	xorq	80(%rsp), %r15
	xorq	88(%rsp), %r15
	xorq	%r12, %rax
	xorq	%r15, %rax
	xorq	56(%rsp), %r13
	xorq	96(%rsp), %r13
	xorq	%rbp, %rdx
	xorq	%r13, %rdx
	movq	%rax, (%r14)
	movq	%rdx, 8(%r14)
	movq	16(%r14), %rax
	cmpq	$29, %rax
	ja	.LBB68_7
	movq	%rax, %rcx
	shlq	$4, %rcx
	movq	48(%rsp), %rdx
	movq	%rdx, 24(%r14,%rcx)
	movq	24(%rsp), %rsi
	movq	%rsi, 32(%r14,%rcx)
	incq	%rax
	movq	%rax, 16(%r14)
	movq	%rdx, 8(%rbx)
	movq	%rsi, 16(%rbx)
	movq	40(%rsp), %rax
	movq	%rax, 24(%rbx)
	movq	32(%rsp), %rax
	movq	%rax, 32(%rbx)
	movl	$1, %eax
	jmp	.LBB68_8
.LBB68_7:
	xorl	%eax, %eax
.LBB68_8:
	movq	%rax, (%rbx)
	addq	$120, %rsp
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
.Lfunc_end68:
	.size	_RNvNtCsemcRClSg8DH_9native_vm4whir10fold_round, .Lfunc_end68-_RNvNtCsemcRClSg8DH_9native_vm4whir10fold_round
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm4whir10glue_level,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm4whir10glue_level,@function
_RNvNtCsemcRClSg8DH_9native_vm4whir10glue_level:
.Lfunc_begin69:
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
	subq	$40, %rsp
	.cfi_def_cfa_offset 96
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	%r9, 32(%rsp)
	movq	%r8, 24(%rsp)
	movq	%rcx, 16(%rsp)
	movq	%rdx, %rbp
	movq	%rsi, %r14
	movq	%rdi, %rbx
	movq	96(%rsp), %rdx
	movq	104(%rsp), %rcx
	movq	(%rdi), %r12
	movq	8(%rdi), %rax
	movq	%rax, 8(%rsp)
	movq	%rsi, %rdi
	movq	%rbp, %rsi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	movq	%rax, %r13
	movq	%rdx, %r15
	xorq	%r12, %r13
	xorq	8(%rsp), %r15
	movq	%r14, %rdi
	movq	%rbp, %rsi
	movq	%r14, %rdx
	movq	%rbp, %rcx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	movq	%rdx, %r12
	movq	%rax, 8(%rsp)
	movq	%rax, %rdi
	movq	%rdx, %rsi
	movq	144(%rsp), %rdx
	movq	152(%rsp), %rcx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	xorq	%r13, %rax
	xorq	%r15, %rdx
	movq	%rax, (%rbx)
	movq	%rdx, 8(%rbx)
	movq	504(%rbx), %rax
	cmpq	$9, %rax
	ja	.LBB69_10
	movq	16(%rbx), %r15
	leaq	512(%rbx), %r13
	imulq	$6064, %rax, %rax
	movq	%r14, (%r13,%rax)
	movq	%rbp, 8(%r13,%rax)
	movq	%r15, 16(%r13,%rax)
	movq	$0, 24(%r13,%rax)
	leaq	40(%r13,%rax), %rdi
	movq	$0, 40(%r13,%rax)
	movq	24(%rsp), %rsi
	movq	32(%rsp), %rdx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKj1e_E6extendB4_
	testb	%al, %al
	je	.LBB69_10
	movq	504(%rbx), %rax
	incq	%rax
	movq	%rax, 504(%rbx)
	cmpq	$9, %rax
	ja	.LBB69_10
	movq	120(%rsp), %rdx
	movq	112(%rsp), %rsi
	imulq	$6064, %rax, %r14
	movq	8(%rsp), %rax
	movq	%rax, (%r13,%r14)
	movq	%r12, 8(%r13,%r14)
	movq	%r15, 16(%r13,%r14)
	movq	$1, 24(%r13,%r14)
	movq	16(%rsp), %rax
	movq	%rax, 32(%r13,%r14)
	leaq	(%r14,%r13), %rdi
	addq	$528, %rdi
	movq	$0, 528(%r13,%r14)
	callq	_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufyKje6_E6extendB4_
	testb	%al, %al
	je	.LBB69_10
	movq	136(%rsp), %rdx
	movq	128(%rsp), %rsi
	addq	%r14, %r13
	movq	$0, 2376(%r13)
	addq	$2376, %r13
	movq	%r13, %rdi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKje6_E6extendB4_
	testb	%al, %al
	je	.LBB69_10
	incq	504(%rbx)
	movb	$1, %al
	jmp	.LBB69_11
.LBB69_10:
	xorl	%eax, %eax
.LBB69_11:
	addq	$40, %rsp
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
.Lfunc_end69:
	.size	_RNvNtCsemcRClSg8DH_9native_vm4whir10glue_level, .Lfunc_end69-_RNvNtCsemcRClSg8DH_9native_vm4whir10glue_level
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm4whir10glued_eval,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm4whir10glued_eval,@function
_RNvNtCsemcRClSg8DH_9native_vm4whir10glued_eval:
.Lfunc_begin70:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	%rcx, %r10
	movq	%rdx, %rax
	movq	%rsi, %r8
	cmpq	$0, 24(%rsi)
	je	.LBB70_1
	movq	528(%r8), %rcx
	xorl	%r9d, %r9d
	cmpq	$231, %rcx
	cmovaeq	%r9, %rcx
	leaq	536(%r8), %rdx
	movl	$8, %r11d
	cmovaeq	%r11, %rdx
	movq	32(%r8), %rsi
	movq	2376(%r8), %rbx
	addq	$2384, %r8
	cmpq	$231, %rbx
	cmovbq	%rbx, %r9
	cmovaeq	%r11, %r8
	pushq	%r10
	.cfi_adjust_cfa_offset 8
	pushq	%rax
	.cfi_adjust_cfa_offset 8
	callq	_RNvNtCsemcRClSg8DH_9native_vm4whir14induced_weight
	addq	$16, %rsp
	.cfi_adjust_cfa_offset -16
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.LBB70_1:
	.cfi_def_cfa_offset 16
	movq	40(%r8), %rcx
	addq	$48, %r8
	xorl	%esi, %esi
	cmpq	$31, %rcx
	cmovbq	%rcx, %rsi
	movl	$8, %ecx
	cmovbq	%r8, %rcx
	movq	%rdi, %rbx
	movq	%rcx, %rdi
	movq	%rax, %rdx
	movq	%r10, %rcx
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field7eq_eval
	movq	%rax, 8(%rbx)
	movq	%rdx, 16(%rbx)
	movq	$1, (%rbx)
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end70:
	.size	_RNvNtCsemcRClSg8DH_9native_vm4whir10glued_eval, .Lfunc_end70-_RNvNtCsemcRClSg8DH_9native_vm4whir10glued_eval
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm4whir10next_level,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm4whir10next_level,@function
_RNvNtCsemcRClSg8DH_9native_vm4whir10next_level:
.Lfunc_begin71:
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
	subq	$3960, %rsp
	.cfi_def_cfa_offset 8112
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	%rdx, %rbp
	movq	%rsi, %rbx
	movq	%rdi, %r14
	movq	%r9, 8(%rsp)
	movl	$2, %edx
	shlq	%cl, %rdx
	movq	8(%rbp), %r13
	addq	%r9, %r13
	xorl	%r15d, %r15d
	subq	%rcx, %r9
	movl	$0, %esi
	cmovaeq	%r9, %rsi
	addq	%r8, %rsi
	callq	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState15read_commitment
	testb	%al, %al
	je	.LBB71_14
	movq	$0, 104(%rsp)
	movq	$0, 112(%rsp)
	movq	$0, 120(%rsp)
	movq	$0, 128(%rsp)
	movq	$0, 136(%rsp)
	movq	$0, 144(%rsp)
	movq	$0, 152(%rsp)
	movq	$0, 160(%rsp)
	movq	$0, 168(%rsp)
	movq	$0, 176(%rsp)
	movq	$0, 184(%rsp)
	movq	$0, 192(%rsp)
	movq	(%rbp), %r15
	cmpq	$6, %r15
	ja	.LBB71_13
	leaq	104(%rsp), %rsi
	movq	%r14, %rdi
	movq	%r15, %rdx
	callq	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState12read_scalars
	testb	%al, %al
	je	.LBB71_13
	movq	%r14, %rdi
	movl	$15, %esi
	callq	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState5grind
	testb	%al, %al
	je	.LBB71_13
	movq	$0, 200(%rsp)
	movq	$0, 208(%rsp)
	movq	$0, 216(%rsp)
	movq	$0, 224(%rsp)
	movq	$0, 232(%rsp)
	movq	$0, 240(%rsp)
	movq	$0, 248(%rsp)
	movq	$0, 256(%rsp)
	movq	$0, 264(%rsp)
	movq	$0, 272(%rsp)
	movq	$0, 280(%rsp)
	movq	$0, 288(%rsp)
	movq	$0, 296(%rsp)
	movq	$0, 304(%rsp)
	movq	$0, 312(%rsp)
	movq	$0, 320(%rsp)
	movq	$0, 328(%rsp)
	movq	$0, 336(%rsp)
	movq	$0, 344(%rsp)
	movq	$0, 352(%rsp)
	movq	$0, 360(%rsp)
	movq	$0, 368(%rsp)
	movq	$0, 376(%rsp)
	movq	$0, 384(%rsp)
	movq	$0, 392(%rsp)
	movq	$0, 400(%rsp)
	movq	$0, 408(%rsp)
	movq	$0, 416(%rsp)
	movq	$0, 424(%rsp)
	movq	$0, 432(%rsp)
	movq	$0, 440(%rsp)
	movq	$0, 448(%rsp)
	movq	$0, 456(%rsp)
	movq	$0, 464(%rsp)
	movq	$0, 472(%rsp)
	movq	$0, 480(%rsp)
	movq	$0, 488(%rsp)
	movq	$0, 496(%rsp)
	movq	$0, 504(%rsp)
	movq	$0, 512(%rsp)
	movq	$0, 520(%rsp)
	movq	$0, 528(%rsp)
	movq	$0, 536(%rsp)
	movq	$0, 544(%rsp)
	movq	$0, 552(%rsp)
	movq	$0, 560(%rsp)
	movq	$0, 568(%rsp)
	movq	$0, 576(%rsp)
	movq	$0, 584(%rsp)
	movq	$0, 592(%rsp)
	movq	$0, 600(%rsp)
	movq	$0, 608(%rsp)
	movq	$0, 616(%rsp)
	movq	$0, 624(%rsp)
	movq	$0, 632(%rsp)
	movq	$0, 640(%rsp)
	movq	$0, 648(%rsp)
	movq	$0, 656(%rsp)
	movq	$0, 664(%rsp)
	movq	$0, 672(%rsp)
	movq	$0, 680(%rsp)
	movq	8(%rsp), %r12
	cmpq	$30, %r12
	ja	.LBB71_13
	leaq	208(%rsp), %rsi
	movq	%r12, 200(%rsp)
	movq	%r14, %rdi
	movq	%r12, %rdx
	callq	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState17sample_challenges
	leaq	4368(%rsp), %rdi
	movq	%r14, %rsi
	callq	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState11read_scalar
	cmpl	$1, 4368(%rsp)
	jne	.LBB71_13
	movq	4376(%rsp), %rax
	movq	%rax, 64(%rsp)
	movq	4384(%rsp), %rax
	movq	%rax, 56(%rsp)
	movq	%r14, %rdi
	movl	$17, %esi
	callq	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState5grind
	testb	%al, %al
	je	.LBB71_13
	movq	8112(%rsp), %rax
	movq	16(%rbp), %rdx
	leaq	61352(%rax), %rbp
	movq	%r14, %rdi
	movq	%r13, %rsi
	movq	%rbp, %rcx
	callq	_RNvNtCsemcRClSg8DH_9native_vm4whir14sample_queries
	testb	%al, %al
	je	.LBB71_13
	movq	%r14, %rdi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW7squeeze
	movq	%rax, 24(%rsp)
	movq	%rdx, 16(%rsp)
	movq	(%rbp), %rax
	movl	$72, %ecx
.LBB71_9:
	movq	$0, 616(%rsp,%rcx)
	movq	$0, 624(%rsp,%rcx)
	movq	$0, 632(%rsp,%rcx)
	movq	$0, 640(%rsp,%rcx)
	movq	$0, 648(%rsp,%rcx)
	movq	$0, 656(%rsp,%rcx)
	movq	$0, 664(%rsp,%rcx)
	movq	$0, 672(%rsp,%rcx)
	movq	$0, 680(%rsp,%rcx)
	movq	$0, 688(%rsp,%rcx)
	addq	$80, %rcx
	cmpq	$3752, %rcx
	jne	.LBB71_9
	movq	8112(%rsp), %rcx
	leaq	61360(%rcx), %r13
	xorl	%ebp, %ebp
	cmpq	$231, %rax
	movl	$8, %ecx
	cmovaeq	%rcx, %r13
	cmovbq	%rax, %rbp
	leaq	4376(%rsp), %rdi
	leaq	688(%rsp), %rsi
	movl	$3680, %edx
	callq	*memcpy@GOTPCREL(%rip)
	movq	%rbp, 4368(%rsp)
	movq	24(%rsp), %rdi
	movq	16(%rsp), %rsi
	leaq	4376(%rsp), %rdx
	movq	%rbp, %rcx
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field6powers
	leaq	688(%rsp), %rdi
	movq	%r14, %rsi
	movq	%rbx, %rdx
	movq	%r13, 48(%rsp)
	movq	%r13, %rcx
	movq	%rbp, %r8
	callq	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState14query_openings
	cmpq	$0, 688(%rsp)
	je	.LBB71_13
	movq	712(%rsp), %rax
	movq	%rax, 96(%rsp)
	movq	704(%rsp), %rax
	movq	%rax, 88(%rsp)
	movq	688(%rsp), %rcx
	movq	696(%rsp), %rax
	movq	%rax, 80(%rsp)
	movq	4368(%rsp), %r14
	xorl	%eax, %eax
	cmpq	$231, %r14
	leaq	4376(%rsp), %r13
	movl	$8, %esi
	cmovaeq	%rsi, %r13
	movq	%rcx, 72(%rsp)
	cmovaeq	%rax, %r14
	movq	$0, 32(%rsp)
	movq	$0, 40(%rsp)
	movq	8112(%rsp), %rdx
	movq	61152(%rdx), %rcx
	leaq	61160(%rdx), %r9
	cmpq	$7, %rcx
	cmovaeq	%rsi, %r9
	cmovbq	%rcx, %rax
	leaq	8(%rsp), %rcx
	movq	%rcx, 688(%rsp)
	leaq	104(%rsp), %rcx
	movq	%rcx, 696(%rsp)
	movq	%r15, 704(%rsp)
	leaq	32(%rsp), %rcx
	movq	%rcx, 712(%rsp)
	movq	%r13, 720(%rsp)
	movq	%r14, 728(%rsp)
	leaq	72(%rsp), %rcx
	movq	%rbx, %rdi
	movq	48(%rsp), %rbx
	movq	%rbx, %rsi
	movq	%rbp, %rdx
	movq	%r12, %r8
	leaq	688(%rsp), %r10
	pushq	%r10
	.cfi_adjust_cfa_offset 8
	pushq	%rax
	.cfi_adjust_cfa_offset 8
	callq	_RINvNtCsemcRClSg8DH_9native_vm4whir8each_rowNCNvB2_10next_level0EB4_
	addq	$16, %rsp
	.cfi_adjust_cfa_offset -16
	testb	%al, %al
	je	.LBB71_13
	movq	200(%rsp), %rax
	xorl	%r9d, %r9d
	cmpq	$31, %rax
	movl	$8, %r8d
	leaq	208(%rsp), %rcx
	cmovbq	%rcx, %r8
	cmovbq	%rax, %r9
	movq	8(%rsp), %rcx
	movq	8112(%rsp), %rdi
	movq	24(%rsp), %rsi
	movq	16(%rsp), %rdx
	pushq	40(%rsp)
	.cfi_adjust_cfa_offset 8
	pushq	40(%rsp)
	.cfi_adjust_cfa_offset 8
	pushq	%r14
	.cfi_adjust_cfa_offset 8
	pushq	%r13
	.cfi_adjust_cfa_offset 8
	pushq	%rbp
	.cfi_adjust_cfa_offset 8
	pushq	%rbx
	.cfi_adjust_cfa_offset 8
	pushq	104(%rsp)
	.cfi_adjust_cfa_offset 8
	pushq	120(%rsp)
	.cfi_adjust_cfa_offset 8
	callq	_RNvNtCsemcRClSg8DH_9native_vm4whir10glue_level
	addq	$64, %rsp
	.cfi_adjust_cfa_offset -64
	movl	%eax, %r15d
	jmp	.LBB71_14
.LBB71_13:
	xorl	%r15d, %r15d
.LBB71_14:
	movl	%r15d, %eax
	addq	$8056, %rsp
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
.Lfunc_end71:
	.size	_RNvNtCsemcRClSg8DH_9native_vm4whir10next_level, .Lfunc_end71-_RNvNtCsemcRClSg8DH_9native_vm4whir10next_level
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm4whir10novel_eval,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm4whir10novel_eval,@function
_RNvNtCsemcRClSg8DH_9native_vm4whir10novel_eval:
.Lfunc_begin72:
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
	subq	$1048, %rsp
	.cfi_def_cfa_offset 1104
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	%r8, %r13
	movq	%rcx, %r12
	movq	%rdx, %r14
	movq	%rsi, %rbp
	movq	%rdi, %r15
	leaq	32(%rsp), %rdi
	xorl	%ebx, %ebx
	movl	$1016, %edx
	xorl	%esi, %esi
	callq	*memset@GOTPCREL(%rip)
	cmpq	$64, %r14
	ja	.LBB72_12
	movq	%rbp, 16(%rsp)
	movq	%r15, 8(%rsp)
	movq	$1, 24(%rsp)
	movl	$1, %ebp
	cmpq	$2, %r14
	jb	.LBB72_7
	leaq	(%r12,%r13,8), %rax
	movq	%rax, (%rsp)
	.p2align	4
.LBB72_3:
	cmpq	(%rsp), %r12
	je	.LBB72_7
	movq	%r14, %rbx
	movq	(%r12), %r13
	movq	%rbp, %r15
	leaq	24(%rsp), %r14
	.p2align	4
.LBB72_5:
	movq	(%r14), %rdi
	movq	%r13, %rsi
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field4kmul
	movq	%rax, (%r14,%rbp,8)
	addq	$8, %r14
	decq	%r15
	jne	.LBB72_5
	addq	$8, %r12
	addq	%rbp, %rbp
	movq	%rbx, %r14
	cmpq	%rbp, %rbx
	ja	.LBB72_3
.LBB72_7:
	cmpq	%r14, %rbp
	cmovbq	%rbp, %r14
	testq	%r14, %r14
	je	.LBB72_8
	shlq	$3, %r14
	movq	%r14, (%rsp)
	xorl	%r14d, %r14d
	xorl	%r15d, %r15d
	xorl	%ebx, %ebx
	.p2align	4
.LBB72_10:
	movq	16(%rsp), %rax
	movq	(%rax,%r15,2), %rsi
	movq	8(%rax,%r15,2), %r12
	movq	24(%rsp,%r15), %r13
	movq	%r13, %rdi
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field4kmul
	movq	%rax, %rbp
	movq	%r13, %rdi
	movq	%r12, %rsi
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field4kmul
	xorq	%rbp, %r14
	xorq	%rax, %rbx
	addq	$8, %r15
	cmpq	%r15, (%rsp)
	jne	.LBB72_10
	jmp	.LBB72_11
.LBB72_8:
	xorl	%ebx, %ebx
	xorl	%r14d, %r14d
.LBB72_11:
	movq	8(%rsp), %r15
	movq	%r14, 8(%r15)
	movq	%rbx, 16(%r15)
	movl	$1, %ebx
.LBB72_12:
	movq	%rbx, (%r15)
	addq	$1048, %rsp
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
.Lfunc_end72:
	.size	_RNvNtCsemcRClSg8DH_9native_vm4whir10novel_eval, .Lfunc_end72-_RNvNtCsemcRClSg8DH_9native_vm4whir10novel_eval
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm4whir10query_bits,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm4whir10query_bits,@function
_RNvNtCsemcRClSg8DH_9native_vm4whir10query_bits:
.Lfunc_begin73:
	.cfi_startproc
	movq	%rcx, %r8
	testq	%rdx, %rdx
	je	.LBB73_6
	cmpq	$64, %rdx
	jae	.LBB73_2
	movl	%edx, %ecx
	shrdq	%cl, %rsi, %rdi
	jmp	.LBB73_6
.LBB73_2:
	cmpq	$128, %rdx
	jae	.LBB73_3
	movl	%edx, %ecx
	shrq	%cl, %rsi
	movq	%rsi, %rdi
	jmp	.LBB73_6
.LBB73_3:
	xorl	%edi, %edi
.LBB73_6:
	movq	$-1, %rax
	movl	%r8d, %ecx
	shlq	%cl, %rax
	movq	$-1, %rcx
	cmpq	$64, %r8
	notq	%rax
	cmovaeq	%rcx, %rax
	andq	%rdi, %rax
	retq
.Lfunc_end73:
	.size	_RNvNtCsemcRClSg8DH_9native_vm4whir10query_bits, .Lfunc_end73-_RNvNtCsemcRClSg8DH_9native_vm4whir10query_bits
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm4whir11final_level,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm4whir11final_level,@function
_RNvNtCsemcRClSg8DH_9native_vm4whir11final_level:
.Lfunc_begin74:
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
	subq	$2584, %rsp
	.cfi_def_cfa_offset 2640
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	%rdx, %rbp
	movq	8(%rdx), %rbx
	movl	$56, %eax
	.p2align	4
.LBB74_1:
	movq	$0, 1504(%rsp,%rax)
	movq	$0, 1512(%rsp,%rax)
	movq	$0, 1520(%rsp,%rax)
	movq	$0, 1528(%rsp,%rax)
	movq	$0, 1536(%rsp,%rax)
	movq	$0, 1544(%rsp,%rax)
	movq	$0, 1552(%rsp,%rax)
	movq	$0, 1560(%rsp,%rax)
	addq	$64, %rax
	cmpq	$1080, %rax
	jne	.LBB74_1
	cmpq	$63, %rcx
	ja	.LBB74_5
	movl	$1, %r14d
	movq	%rcx, (%rsp)
	shlq	%cl, %r14
	movq	(%rbp), %r13
	addq	%r14, %r13
	cmpq	%r14, %r13
	setb	%al
	cmpq	$65, %r13
	setae	%cl
	orb	%al, %cl
	jne	.LBB74_5
	movq	%rsi, %r15
	movq	%r8, 8(%rsp)
	movq	%r9, 16(%rsp)
	leaq	1560(%rsp), %rsi
	movq	%rdi, %r12
	movq	%r13, %rdx
	callq	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState12read_scalars
	testb	%al, %al
	je	.LBB74_5
	movq	%r12, %rdi
	movl	$17, %esi
	callq	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState5grind
	testb	%al, %al
	je	.LBB74_5
	addq	(%rsp), %rbx
	movq	16(%rbp), %rdx
	movq	2640(%rsp), %rbp
	leaq	61352(%rbp), %rcx
	movq	%r12, %rdi
	movq	%rbx, %rsi
	callq	_RNvNtCsemcRClSg8DH_9native_vm4whir14sample_queries
	testb	%al, %al
	je	.LBB74_5
	movq	61352(%rbp), %rax
	xorl	%ebx, %ebx
	cmpq	$231, %rax
	cmovbq	%rax, %rbx
	leaq	61360(%rbp), %rbp
	movl	$8, %eax
	cmovaeq	%rax, %rbp
	leaq	104(%rsp), %rdi
	movq	%r12, %rsi
	movq	%r15, %rdx
	movq	%rbp, %rcx
	movq	%rbx, %r8
	callq	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState14query_openings
	cmpq	$0, 104(%rsp)
	je	.LBB74_5
	movq	128(%rsp), %rax
	movq	%rax, 96(%rsp)
	movq	120(%rsp), %rax
	movq	%rax, 88(%rsp)
	movq	104(%rsp), %rax
	movq	112(%rsp), %rcx
	movq	%rcx, 80(%rsp)
	movq	%rax, 72(%rsp)
	movq	2640(%rsp), %rcx
	movq	61152(%rcx), %rax
	addq	$61160, %rcx
	xorl	%edx, %edx
	cmpq	$7, %rax
	cmovaeq	%rdx, %rax
	movl	$8, %r9d
	cmovbq	%rcx, %r9
	subq	$8, %rsp
	.cfi_adjust_cfa_offset 8
	leaq	80(%rsp), %rcx
	movq	%r15, %rdi
	movq	%rbp, %rsi
	movq	%rbx, %rdx
	movq	8(%rsp), %r8
	pushq	%r13
	.cfi_adjust_cfa_offset 8
	leaq	1576(%rsp), %r10
	pushq	%r10
	.cfi_adjust_cfa_offset 8
	pushq	%rax
	.cfi_adjust_cfa_offset 8
	callq	_RINvNtCsemcRClSg8DH_9native_vm4whir8each_rowNCNvB2_11final_level0EB4_
	addq	$32, %rsp
	.cfi_adjust_cfa_offset -32
	movl	%eax, %ecx
	xorl	%eax, %eax
	testb	%cl, %cl
	je	.LBB74_6
	movq	$0, 1080(%rsp)
	movq	$0, 1088(%rsp)
	movq	$0, 1096(%rsp)
	movq	$0, 1104(%rsp)
	movq	$0, 1112(%rsp)
	movq	$0, 1120(%rsp)
	movq	$0, 1128(%rsp)
	movq	$0, 1136(%rsp)
	movq	$0, 1144(%rsp)
	movq	$0, 1152(%rsp)
	movq	$0, 1160(%rsp)
	movq	$0, 1168(%rsp)
	movq	$0, 1176(%rsp)
	movq	$0, 1184(%rsp)
	movq	$0, 1192(%rsp)
	movq	$0, 1200(%rsp)
	movq	$0, 1208(%rsp)
	movq	$0, 1216(%rsp)
	movq	$0, 1224(%rsp)
	movq	$0, 1232(%rsp)
	movq	$0, 1240(%rsp)
	movq	$0, 1248(%rsp)
	movq	$0, 1256(%rsp)
	movq	$0, 1264(%rsp)
	movq	$0, 1272(%rsp)
	movq	$0, 1280(%rsp)
	movq	$0, 1288(%rsp)
	movq	$0, 1296(%rsp)
	movq	$0, 1304(%rsp)
	movq	$0, 1312(%rsp)
	movq	$0, 1320(%rsp)
	movq	$0, 1328(%rsp)
	movq	$0, 1336(%rsp)
	movq	$0, 1344(%rsp)
	movq	$0, 1352(%rsp)
	movq	$0, 1360(%rsp)
	movq	$0, 1368(%rsp)
	movq	$0, 1376(%rsp)
	movq	$0, 1384(%rsp)
	movq	$0, 1392(%rsp)
	movq	$0, 1400(%rsp)
	movq	$0, 1408(%rsp)
	movq	$0, 1416(%rsp)
	movq	$0, 1424(%rsp)
	movq	$0, 1432(%rsp)
	movq	$0, 1440(%rsp)
	movq	$0, 1448(%rsp)
	movq	$0, 1456(%rsp)
	movq	$0, 1464(%rsp)
	movq	$0, 1472(%rsp)
	movq	$0, 1480(%rsp)
	movq	$0, 1488(%rsp)
	movq	$0, 1496(%rsp)
	movq	$0, 1504(%rsp)
	movq	$0, 1512(%rsp)
	movq	$0, 1520(%rsp)
	movq	$0, 1528(%rsp)
	movq	$0, 1536(%rsp)
	movq	$0, 1544(%rsp)
	movq	$0, 1552(%rsp)
	movq	(%rsp), %rax
	cmpq	$30, %rax
	ja	.LBB74_5
	movq	2640(%rsp), %rbx
	movq	(%rbx), %rdx
	movq	8(%rbx), %rcx
	subq	$8, %rsp
	.cfi_adjust_cfa_offset 8
	leaq	112(%rsp), %rdi
	leaq	1088(%rsp), %r9
	movl	$3, %r8d
	movq	%r12, %rsi
	pushq	%rax
	.cfi_adjust_cfa_offset 8
	callq	_RINvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB6_6TState8sumcheckNCNvB2_14sumcheck_plain0EB8_
	addq	$16, %rsp
	.cfi_adjust_cfa_offset -16
	cmpl	$1, 104(%rsp)
	jne	.LBB74_5
	movq	112(%rsp), %r12
	movq	120(%rsp), %r15
	movq	$0, 600(%rsp)
	movq	$0, 608(%rsp)
	movq	$0, 616(%rsp)
	movq	$0, 624(%rsp)
	movq	$0, 632(%rsp)
	movq	$0, 640(%rsp)
	movq	$0, 648(%rsp)
	movq	$0, 656(%rsp)
	movq	$0, 664(%rsp)
	movq	$0, 672(%rsp)
	movq	$0, 680(%rsp)
	movq	$0, 688(%rsp)
	movq	$0, 696(%rsp)
	movq	$0, 704(%rsp)
	movq	$0, 712(%rsp)
	movq	$0, 720(%rsp)
	movq	$0, 728(%rsp)
	movq	$0, 736(%rsp)
	movq	$0, 744(%rsp)
	movq	$0, 752(%rsp)
	movq	$0, 760(%rsp)
	movq	$0, 768(%rsp)
	movq	$0, 776(%rsp)
	movq	$0, 784(%rsp)
	movq	$0, 792(%rsp)
	movq	$0, 800(%rsp)
	movq	$0, 808(%rsp)
	movq	$0, 816(%rsp)
	movq	$0, 824(%rsp)
	movq	$0, 832(%rsp)
	movq	$0, 840(%rsp)
	movq	$0, 848(%rsp)
	movq	$0, 856(%rsp)
	movq	$0, 864(%rsp)
	movq	$0, 872(%rsp)
	movq	$0, 880(%rsp)
	movq	$0, 888(%rsp)
	movq	$0, 896(%rsp)
	movq	$0, 904(%rsp)
	movq	$0, 912(%rsp)
	movq	$0, 920(%rsp)
	movq	$0, 928(%rsp)
	movq	$0, 936(%rsp)
	movq	$0, 944(%rsp)
	movq	$0, 952(%rsp)
	movq	$0, 960(%rsp)
	movq	$0, 968(%rsp)
	movq	$0, 976(%rsp)
	movq	$0, 984(%rsp)
	movq	$0, 992(%rsp)
	movq	$0, 1000(%rsp)
	movq	$0, 1008(%rsp)
	movq	$0, 1016(%rsp)
	movq	$0, 1024(%rsp)
	movq	$0, 1032(%rsp)
	movq	$0, 1040(%rsp)
	movq	$0, 1048(%rsp)
	movq	$0, 1056(%rsp)
	movq	$0, 1064(%rsp)
	movq	$0, 1072(%rsp)
	movq	16(%rbx), %rax
	leaq	24(%rbx), %rcx
	xorl	%edx, %edx
	cmpq	$31, %rax
	cmovbq	%rax, %rdx
	movl	$8, %esi
	cmovbq	%rcx, %rsi
	movq	$0, 592(%rsp)
	leaq	592(%rsp), %rdi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKj1e_E6extendB4_
	testb	%al, %al
	je	.LBB74_5
	leaq	592(%rsp), %rdi
	leaq	1080(%rsp), %rsi
	movq	(%rsp), %rdx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKj1e_E6extendB4_
	testb	%al, %al
	je	.LBB74_5
	leaq	600(%rsp), %rbx
	movq	592(%rsp), %r13
	xorl	%eax, %eax
	cmpq	$31, %r13
	cmovaeq	%rax, %r13
	movl	$8, %ecx
	cmovaeq	%rcx, %rbx
	movq	$0, 112(%rsp)
	movq	$0, 120(%rsp)
	movq	$0, 128(%rsp)
	movq	$0, 136(%rsp)
	movq	$0, 144(%rsp)
	movq	$0, 152(%rsp)
	movq	$0, 160(%rsp)
	movq	$0, 168(%rsp)
	movq	$0, 176(%rsp)
	movq	$0, 184(%rsp)
	movq	$0, 192(%rsp)
	movq	$0, 200(%rsp)
	movq	$0, 208(%rsp)
	movq	$0, 216(%rsp)
	movq	$0, 224(%rsp)
	movq	$0, 232(%rsp)
	movq	$0, 240(%rsp)
	movq	$0, 248(%rsp)
	movq	$0, 256(%rsp)
	movq	$0, 264(%rsp)
	movq	$0, 272(%rsp)
	movq	$0, 280(%rsp)
	movq	$0, 288(%rsp)
	movq	$0, 296(%rsp)
	movq	$0, 304(%rsp)
	movq	$0, 312(%rsp)
	movq	$0, 320(%rsp)
	movq	$0, 328(%rsp)
	movq	$0, 336(%rsp)
	movq	$0, 344(%rsp)
	movq	$0, 352(%rsp)
	movq	$0, 360(%rsp)
	movq	$0, 368(%rsp)
	movq	$0, 376(%rsp)
	movq	$0, 384(%rsp)
	movq	$0, 392(%rsp)
	movq	$0, 400(%rsp)
	movq	$0, 408(%rsp)
	movq	$0, 416(%rsp)
	movq	$0, 424(%rsp)
	movq	$0, 432(%rsp)
	movq	$0, 440(%rsp)
	movq	$0, 448(%rsp)
	movq	$0, 456(%rsp)
	movq	$0, 464(%rsp)
	movq	$0, 472(%rsp)
	movq	$0, 480(%rsp)
	movq	$0, 488(%rsp)
	movq	$0, 496(%rsp)
	movq	$0, 504(%rsp)
	movq	$0, 512(%rsp)
	movq	$0, 520(%rsp)
	movq	$0, 528(%rsp)
	movq	$0, 536(%rsp)
	movq	$0, 544(%rsp)
	movq	$0, 552(%rsp)
	movq	$0, 560(%rsp)
	movq	$0, 568(%rsp)
	movq	$0, 576(%rsp)
	movq	8(%rsp), %rdi
	movq	%rdi, %rsi
	shlq	$4, %rsi
	addq	%rbx, %rsi
	movq	%r13, %rdx
	subq	%rdi, %rdx
	cmovbq	%rcx, %rsi
	movq	$0, 584(%rsp)
	cmovbq	%rax, %rdx
	movq	$0, 104(%rsp)
	leaq	104(%rsp), %rdi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKj1e_E6extendB4_
	testb	%al, %al
	je	.LBB74_5
	movq	8(%rsp), %rdx
	cmpq	%rdx, %r13
	cmovbq	%r13, %rdx
	leaq	104(%rsp), %rdi
	movq	%rbx, %rsi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKj1e_E6extendB4_
	testb	%al, %al
	je	.LBB74_5
	movq	%r13, 8(%rsp)
	movq	104(%rsp), %rax
	xorl	%ecx, %ecx
	cmpq	$31, %rax
	cmovbq	%rax, %rcx
	leaq	112(%rsp), %rdx
	movl	$8, %r13d
	cmovaeq	%r13, %rdx
	leaq	24(%rsp), %rdi
	movq	16(%rsp), %rsi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm4whirNtB2_6BasisW4eval
	cmpl	$1, 24(%rsp)
	jne	.LBB74_5
	movq	%rbx, 16(%rsp)
	movq	%r12, 48(%rsp)
	movq	%r15, 56(%rsp)
	movq	32(%rsp), %r15
	movq	2640(%rsp), %rdx
	movq	504(%rdx), %rax
	addq	$512, %rdx
	imulq	$6064, %rax, %rcx
	xorl	%esi, %esi
	cmpq	$11, %rax
	cmovbq	%rdx, %r13
	movq	40(%rsp), %rbp
	cmovbq	%rcx, %rsi
	testq	%rsi, %rsi
	je	.LBB74_23
	addq	%r13, %rsi
	movq	%rsi, 64(%rsp)
.LBB74_21:
	movq	(%r13), %rbx
	movq	8(%r13), %r12
	movq	16(%r13), %rax
	movq	%rax, %rdx
	shlq	$4, %rdx
	addq	16(%rsp), %rdx
	movq	8(%rsp), %rcx
	subq	%rax, %rcx
	movl	$8, %eax
	cmovbq	%rax, %rdx
	movl	$0, %eax
	cmovbq	%rax, %rcx
	leaq	24(%rsp), %rdi
	movq	%r13, %rsi
	callq	_RNvNtCsemcRClSg8DH_9native_vm4whir10glued_eval
	cmpl	$1, 24(%rsp)
	jne	.LBB74_5
	movq	32(%rsp), %rdx
	movq	40(%rsp), %rcx
	movq	%rbx, %rdi
	movq	%r12, %rsi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	xorq	%rax, %r15
	xorq	%rdx, %rbp
	addq	$6064, %r13
	cmpq	64(%rsp), %r13
	jne	.LBB74_21
.LBB74_23:
	leaq	1560(%rsp), %rsi
	leaq	1080(%rsp), %rcx
	movq	%r14, %rdi
	movq	%r14, %rdx
	movq	(%rsp), %r8
	callq	_RINvNtCsemcRClSg8DH_9native_vm5field19multilinear_eval_byNCNvB2_16multilinear_eval0EB4_
	movq	%rdx, %rcx
	movq	%r15, %rdi
	movq	%rbp, %rsi
	movq	%rax, %rdx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	xorq	48(%rsp), %rax
	xorq	56(%rsp), %rdx
	orq	%rax, %rdx
	sete	%al
	jmp	.LBB74_6
.LBB74_5:
	xorl	%eax, %eax
.LBB74_6:
	addq	$2584, %rsp
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
.Lfunc_end74:
	.size	_RNvNtCsemcRClSg8DH_9native_vm4whir11final_level, .Lfunc_end74-_RNvNtCsemcRClSg8DH_9native_vm4whir11final_level
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm4whir11fold_rounds,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm4whir11fold_rounds,@function
_RNvNtCsemcRClSg8DH_9native_vm4whir11fold_rounds:
.Lfunc_begin75:
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
	subq	$104, %rsp
	.cfi_def_cfa_offset 160
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	$0, (%rcx)
	movb	$1, %bl
	testq	%rsi, %rsi
	je	.LBB75_3
	movq	%rcx, %r12
	movq	%rdx, %r14
	movq	%rsi, %r13
	movq	%rdi, %r15
	leaq	32(%rsp), %rdi
	movq	%r15, %rsi
	callq	_RNvNtCsemcRClSg8DH_9native_vm4whir10fold_round
	cmpb	$0, 32(%rsp)
	je	.LBB75_2
	leaq	40(%rsp), %rbp
	movq	24(%rbp), %rax
	movq	16(%rbp), %rcx
	movq	(%rbp), %rdx
	movq	8(%rbp), %rsi
	movq	%rdx, (%rsp)
	movq	%rsi, 8(%rsp)
	movq	%rcx, 16(%rsp)
	movq	%rax, 24(%rsp)
	movq	%rax, 32(%r12)
	movq	%rcx, 24(%r12)
	movq	%rsi, 16(%r12)
	movq	%rdx, 8(%r12)
	movq	$1, (%r12)
	cmpq	$1, %r13
	je	.LBB75_3
	leaq	32(%rsp), %rdi
	movq	%r15, %rsi
	movq	%r14, %rdx
	callq	_RNvNtCsemcRClSg8DH_9native_vm4whir10fold_round
	cmpl	$1, 32(%rsp)
	jne	.LBB75_2
	movq	24(%rbp), %rax
	movq	16(%rbp), %rcx
	movq	(%rbp), %rdx
	movq	8(%rbp), %rsi
	movq	%rdx, (%rsp)
	movq	%rsi, 8(%rsp)
	movq	%rcx, 16(%rsp)
	movq	%rax, 24(%rsp)
	movq	%rax, 64(%r12)
	movq	%rcx, 56(%r12)
	movq	%rsi, 48(%r12)
	movq	%rdx, 40(%r12)
	movq	$2, (%r12)
	cmpq	$2, %r13
	je	.LBB75_3
	leaq	32(%rsp), %rdi
	movq	%r15, %rsi
	movq	%r14, %rdx
	callq	_RNvNtCsemcRClSg8DH_9native_vm4whir10fold_round
	cmpl	$1, 32(%rsp)
	jne	.LBB75_2
	movq	24(%rbp), %rax
	movq	16(%rbp), %rcx
	movq	(%rbp), %rdx
	movq	8(%rbp), %rsi
	movq	%rdx, (%rsp)
	movq	%rsi, 8(%rsp)
	movq	%rcx, 16(%rsp)
	movq	%rax, 24(%rsp)
	movq	%rax, 96(%r12)
	movq	%rcx, 88(%r12)
	movq	%rsi, 80(%r12)
	movq	%rdx, 72(%r12)
	movq	$3, (%r12)
	cmpq	$3, %r13
	je	.LBB75_3
	leaq	32(%rsp), %rdi
	movq	%r15, %rsi
	movq	%r14, %rdx
	callq	_RNvNtCsemcRClSg8DH_9native_vm4whir10fold_round
	cmpl	$1, 32(%rsp)
	jne	.LBB75_2
	movq	24(%rbp), %rax
	movq	16(%rbp), %rcx
	movq	(%rbp), %rdx
	movq	8(%rbp), %rsi
	movq	%rdx, (%rsp)
	movq	%rsi, 8(%rsp)
	movq	%rcx, 16(%rsp)
	movq	%rax, 24(%rsp)
	movq	%rax, 128(%r12)
	movq	%rcx, 120(%r12)
	movq	%rsi, 112(%r12)
	movq	%rdx, 104(%r12)
	movq	$4, (%r12)
	cmpq	$4, %r13
	je	.LBB75_3
	leaq	32(%rsp), %rdi
	movq	%r15, %rsi
	movq	%r14, %rdx
	callq	_RNvNtCsemcRClSg8DH_9native_vm4whir10fold_round
	cmpl	$1, 32(%rsp)
	jne	.LBB75_2
	movq	24(%rbp), %rax
	movq	16(%rbp), %rcx
	movq	(%rbp), %rdx
	movq	8(%rbp), %rsi
	movq	%rdx, (%rsp)
	movq	%rsi, 8(%rsp)
	movq	%rcx, 16(%rsp)
	movq	%rax, 24(%rsp)
	movq	%rax, 160(%r12)
	movq	%rcx, 152(%r12)
	movq	%rsi, 144(%r12)
	movq	%rdx, 136(%r12)
	movq	$5, (%r12)
	cmpq	$5, %r13
	je	.LBB75_3
	leaq	32(%rsp), %rdi
	movq	%r15, %rsi
	movq	%r14, %rdx
	callq	_RNvNtCsemcRClSg8DH_9native_vm4whir10fold_round
	cmpl	$1, 32(%rsp)
	jne	.LBB75_2
	movq	24(%rbp), %rax
	movq	16(%rbp), %rcx
	movq	(%rbp), %rdx
	movq	8(%rbp), %rsi
	movq	%rdx, (%rsp)
	movq	%rsi, 8(%rsp)
	movq	%rcx, 16(%rsp)
	movq	%rax, 24(%rsp)
	movq	%rax, 192(%r12)
	movq	%rcx, 184(%r12)
	movq	%rsi, 176(%r12)
	movq	%rdx, 168(%r12)
	movq	$6, (%r12)
	cmpq	$6, %r13
	je	.LBB75_3
	leaq	32(%rsp), %rdi
	movq	%r15, %rsi
	movq	%r14, %rdx
	callq	_RNvNtCsemcRClSg8DH_9native_vm4whir10fold_round
.LBB75_2:
	xorl	%ebx, %ebx
.LBB75_3:
	movl	%ebx, %eax
	addq	$104, %rsp
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
.Lfunc_end75:
	.size	_RNvNtCsemcRClSg8DH_9native_vm4whir11fold_rounds, .Lfunc_end75-_RNvNtCsemcRClSg8DH_9native_vm4whir11fold_rounds
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm4whir11whir_levels,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm4whir11whir_levels,@function
_RNvNtCsemcRClSg8DH_9native_vm4whir11whir_levels:
.Lfunc_begin76:
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
	movq	%r8, %rbx
	movq	%rcx, 32(%rsp)
	movq	%rdx, 24(%rsp)
	movq	%rsi, 48(%rsp)
	movq	%rdi, %r15
	movq	112(%rsp), %rbp
	xorl	%ecx, %ecx
	movq	%r9, %rax
	subq	$1, %rax
	cmovaeq	%rax, %rcx
	movq	%rcx, 16(%rsp)
	movl	$1, %eax
	cmovbq	%r9, %rax
	subq	%r9, %rax
	movq	%rax, 40(%rsp)
	shlq	$3, %r9
	leaq	(%r9,%r9,2), %r12
	movq	$-1, %r13
	.p2align	4
.LBB76_1:
	testq	%r12, %r12
	je	.LBB76_5
	movq	(%rbx), %rsi
	movq	%r15, %rdi
	movq	%rbp, %rdx
	leaq	61152(%rbp), %rcx
	callq	_RNvNtCsemcRClSg8DH_9native_vm4whir11fold_rounds
	testb	%al, %al
	je	.LBB76_5
	movq	40(%rsp), %rax
	addq	%r13, %rax
	movq	48(%rsp), %rcx
	subq	16(%rbp), %rcx
	movl	$0, %r9d
	cmovaeq	%rcx, %r9
	cmpq	$-1, %rax
	je	.LBB76_6
	leaq	24(%rbx), %r14
	movq	24(%rbx), %rcx
	movq	32(%rbx), %r8
	incq	%r13
	addq	$-24, %r12
	movq	%rbp, (%rsp)
	movq	%r15, %rdi
	movq	%r13, %rsi
	movq	%rbx, %rdx
	callq	_RNvNtCsemcRClSg8DH_9native_vm4whir10next_level
	movq	%r14, %rbx
	testb	%al, %al
	jne	.LBB76_1
.LBB76_5:
	xorl	%eax, %eax
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
.LBB76_6:
	.cfi_def_cfa_offset 112
	movq	%r15, %rdi
	movq	16(%rsp), %rsi
	movq	%rbx, %rdx
	movq	%r9, %rcx
	movq	24(%rsp), %r8
	movq	32(%rsp), %r9
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
	jmp	_RNvNtCsemcRClSg8DH_9native_vm4whir11final_level
.Lfunc_end76:
	.size	_RNvNtCsemcRClSg8DH_9native_vm4whir11whir_levels, .Lfunc_end76-_RNvNtCsemcRClSg8DH_9native_vm4whir11whir_levels
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm4whir14induced_weight,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm4whir14induced_weight,@function
_RNvNtCsemcRClSg8DH_9native_vm4whir14induced_weight:
.Lfunc_begin77:
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
	subq	$1112, %rsp
	.cfi_def_cfa_offset 1168
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	%r9, %r15
	movq	%r8, 56(%rsp)
	movq	%rcx, %rbx
	movq	%rdx, 48(%rsp)
	movq	%rdi, %r14
	leaq	96(%rsp), %rdi
	callq	_RNvNtCsemcRClSg8DH_9native_vm4whir14subspace_table
	cmpl	$1, 96(%rsp)
	jne	.LBB77_3
	movq	%r14, 16(%rsp)
	movq	104(%rsp), %r14
	leaq	112(%rsp), %rsi
	leaq	616(%rsp), %r12
	movl	$496, %edx
	movq	%r12, %rdi
	callq	*memcpy@GOTPCREL(%rip)
	movq	%r14, 608(%rsp)
	cmpq	%r15, %rbx
	cmovbq	%rbx, %r15
	testq	%r15, %r15
	je	.LBB77_2
	movq	%r14, %rdx
	xorl	%eax, %eax
	cmpq	$32, %r14
	movl	$8, %ecx
	cmovbq	%r12, %rcx
	movq	%rcx, 24(%rsp)
	cmovaeq	%rax, %rdx
	movq	1168(%rsp), %r14
	xorl	%ecx, %ecx
	xorl	%esi, %esi
	movq	%r15, 40(%rsp)
	movq	%rdx, 32(%rsp)
	jmp	.LBB77_6
	.p2align	4
.LBB77_9:
	movq	80(%rsp), %rax
	xorq	%r12, %rax
	movq	72(%rsp), %rcx
	xorq	%rbx, %rcx
	movq	64(%rsp), %rsi
	incq	%rsi
	movq	40(%rsp), %r15
	cmpq	%r15, %rsi
	movq	32(%rsp), %rdx
	je	.LBB77_10
.LBB77_6:
	movq	%rcx, 72(%rsp)
	movq	%rax, 80(%rsp)
	movq	%rsi, %rax
	shlq	$4, %rax
	movq	56(%rsp), %rcx
	movq	(%rcx,%rax), %rbx
	movq	8(%rcx,%rax), %r12
	movq	48(%rsp), %rax
	movq	%rsi, 64(%rsp)
	movq	(%rax,%rsi,8), %rcx
	leaq	96(%rsp), %rdi
	movq	24(%rsp), %rsi
	callq	_RNvNtCsemcRClSg8DH_9native_vm4whir17subspace_at_table
	movq	96(%rsp), %rdx
	cmpq	$32, %rdx
	setae	%al
	movq	1176(%rsp), %rcx
	cmpq	%rcx, %rdx
	cmovaeq	%rcx, %rdx
	movq	%rdx, 8(%rsp)
	testq	%rdx, %rdx
	sete	%cl
	orb	%al, %cl
	jne	.LBB77_9
	shlq	$3, 8(%rsp)
	xorl	%r15d, %r15d
	.p2align	4
.LBB77_8:
	movq	%r12, 88(%rsp)
	movq	(%r14,%r15,2), %rsi
	movq	%rbx, %r12
	movq	8(%r14,%r15,2), %rbx
	movq	104(%rsp,%r15), %r13
	xorq	$1, %r13
	movq	%r13, %rdi
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field4kmul
	movq	%rax, %rbp
	movq	%r13, %rdi
	movq	%rbx, %rsi
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field4kmul
	xorq	$1, %rbp
	movq	%r12, %rdi
	movq	88(%rsp), %rsi
	movq	%rbp, %rdx
	movq	%rax, %rcx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	movq	%rax, %rbx
	movq	%rdx, %r12
	addq	$8, %r15
	cmpq	%r15, 8(%rsp)
	jne	.LBB77_8
	jmp	.LBB77_9
.LBB77_3:
	xorl	%eax, %eax
	jmp	.LBB77_4
.LBB77_2:
	xorl	%ecx, %ecx
	xorl	%eax, %eax
.LBB77_10:
	movq	16(%rsp), %r14
	movq	%rcx, 8(%r14)
	movq	%rax, 16(%r14)
	movl	$1, %eax
.LBB77_4:
	movq	%rax, (%r14)
	addq	$1112, %rsp
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
.Lfunc_end77:
	.size	_RNvNtCsemcRClSg8DH_9native_vm4whir14induced_weight, .Lfunc_end77-_RNvNtCsemcRClSg8DH_9native_vm4whir14induced_weight
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm4whir14sample_queries,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm4whir14sample_queries,@function
_RNvNtCsemcRClSg8DH_9native_vm4whir14sample_queries:
.Lfunc_begin78:
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
	subq	$72, %rsp
	.cfi_def_cfa_offset 128
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	%rcx, 64(%rsp)
	movq	$0, (%rcx)
	movb	$1, %al
	testq	%rdx, %rdx
	je	.LBB78_13
	movq	%rdx, %r14
	movq	%rsi, %r13
	movq	%rdi, %rbx
	cmpq	$129, %rsi
	jae	.LBB78_11
	xorl	%r15d, %r15d
	leaq	.Lanon.a75d6d9e6a8990b4224ef13f18552af8.10(%rip), %r12
	movq	%r14, %rax
	xorl	%ebp, %ebp
	movq	%rbx, 16(%rsp)
	jmp	.LBB78_3
	.p2align	4
.LBB78_11:
	movq	%rbx, %rdi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW7squeeze
	decq	%r14
	jne	.LBB78_11
.LBB78_12:
	movb	$1, %al
	jmp	.LBB78_13
	.p2align	4
.LBB78_9:
	decq	%rbp
	movq	16(%rsp), %rbx
	movq	24(%rsp), %r15
	leaq	.Lanon.a75d6d9e6a8990b4224ef13f18552af8.10(%rip), %r12
	movq	8(%rsp), %rax
.LBB78_10:
	incq	%r15
	subq	%rcx, %rax
	cmpq	%r14, %r15
	je	.LBB78_12
.LBB78_3:
	testq	%rax, %rax
	je	.LBB78_12
	movq	%rbx, %rdi
	movq	%rax, 8(%rsp)
	callq	_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW7squeeze
	movq	%rax, 56(%rsp)
	movq	8(%rsp), %rax
	movq	%rdx, 48(%rsp)
	movzbl	(%r13,%r12), %ecx
	cmpq	%rcx, %rax
	cmovbq	%rax, %rcx
	testq	%r13, %r13
	je	.LBB78_10
	movq	%r15, 24(%rsp)
	cmpq	$1, %rcx
	movq	%rcx, %rax
	adcq	$0, %rax
	shlq	$3, %rax
	movq	%rax, 32(%rsp)
	cmpq	$230, %rbp
	movl	$230, %eax
	cmovbq	%rbp, %rax
	movl	%eax, %eax
	leaq	-1840(,%rax,8), %rax
	movq	%rax, 40(%rsp)
	incq	%rbp
	xorl	%r15d, %r15d
	xorl	%r12d, %r12d
	.p2align	4
.LBB78_6:
	cmpq	%r12, 40(%rsp)
	je	.LBB78_7
	movq	56(%rsp), %rdi
	movq	48(%rsp), %rsi
	movq	%r15, %rdx
	movq	%rcx, %rbx
	movq	%r13, %rcx
	callq	_RNvNtCsemcRClSg8DH_9native_vm4whir10query_bits
	movq	64(%rsp), %rcx
	movq	%rax, (%rcx,%rbp,8)
	movq	%rbp, (%rcx)
	movq	%rbx, %rcx
	addq	$-8, %r12
	addq	%r13, %r15
	incq	%rbp
	movq	32(%rsp), %rax
	addq	%r12, %rax
	jne	.LBB78_6
	jmp	.LBB78_9
.LBB78_7:
	xorl	%eax, %eax
.LBB78_13:
	addq	$72, %rsp
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
.Lfunc_end78:
	.size	_RNvNtCsemcRClSg8DH_9native_vm4whir14sample_queries, .Lfunc_end78-_RNvNtCsemcRClSg8DH_9native_vm4whir14sample_queries
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm4whir14subspace_table,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm4whir14subspace_table,@function
_RNvNtCsemcRClSg8DH_9native_vm4whir14subspace_table:
.Lfunc_begin79:
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
	subq	$792, %rsp
	.cfi_def_cfa_offset 848
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	%rsi, %r14
	movq	%rdi, %rbx
	leaq	544(%rsp), %r15
	movl	$248, %edx
	movq	%r15, %rdi
	xorl	%esi, %esi
	callq	*memset@GOTPCREL(%rip)
	cmpq	$32, %r14
	jae	.LBB79_1
	movq	%rbx, (%rsp)
	testq	%r14, %r14
	je	.LBB79_11
	leaq	-1(%r14), %rax
	movabsq	$2305843009213693951, %rcx
	andq	%rax, %rcx
	leaq	1(%rcx), %rsi
	movl	%esi, %eax
	andl	$7, %eax
	cmpq	$7, %rcx
	jae	.LBB79_6
	xorl	%edx, %edx
	jmp	.LBB79_9
.LBB79_1:
	movq	$0, (%rbx)
	jmp	.LBB79_2
.LBB79_6:
	andq	$-8, %rsi
	leaq	544(%rsp), %r15
	xorl	%edx, %edx
	.p2align	4
.LBB79_7:
	movl	%edx, %ecx
	movl	$2, %edi
	shlq	%cl, %rdi
	movl	$4, %r8d
	shlq	%cl, %r8
	movl	$8, %r9d
	shlq	%cl, %r9
	movq	%rdi, (%r15)
	movq	%r8, 8(%r15)
	movl	$16, %edi
	shlq	%cl, %rdi
	movl	$32, %r8d
	shlq	%cl, %r8
	movq	%r9, 16(%r15)
	movq	%rdi, 24(%r15)
	movl	$64, %edi
	shlq	%cl, %rdi
	movl	$128, %r9d
	shlq	%cl, %r9
	movq	%r8, 32(%r15)
	movq	%rdi, 40(%r15)
	movq	%r9, 48(%r15)
	movl	$256, %edi
	shlq	%cl, %rdi
	addq	$8, %rdx
	movq	%rdi, 56(%r15)
	addq	$64, %r15
	cmpq	%rdx, %rsi
	jne	.LBB79_7
	testq	%rax, %rax
	je	.LBB79_11
.LBB79_9:
	xorl	%esi, %esi
	.p2align	4
.LBB79_10:
	leal	(%rdx,%rsi), %ecx
	movl	$2, %edi
	shlq	%cl, %rdi
	movq	%rdi, (%r15,%rsi,8)
	incq	%rsi
	cmpq	%rsi, %rax
	jne	.LBB79_10
.LBB79_11:
	movq	$0, 40(%rsp)
	movq	$0, 64(%rsp)
	movq	$0, 72(%rsp)
	movq	$0, 80(%rsp)
	movq	$0, 88(%rsp)
	movq	$0, 96(%rsp)
	movq	$0, 104(%rsp)
	movq	$0, 112(%rsp)
	movq	$0, 120(%rsp)
	movq	$0, 128(%rsp)
	movq	$0, 136(%rsp)
	movq	$0, 144(%rsp)
	movq	$0, 152(%rsp)
	movq	$0, 160(%rsp)
	movq	$0, 168(%rsp)
	movq	$0, 176(%rsp)
	movq	$0, 184(%rsp)
	movq	$0, 192(%rsp)
	movq	$0, 200(%rsp)
	movq	$0, 208(%rsp)
	movq	$0, 216(%rsp)
	movq	$0, 224(%rsp)
	movq	$0, 232(%rsp)
	movq	$0, 240(%rsp)
	movq	$0, 248(%rsp)
	movq	$0, 256(%rsp)
	movq	$0, 264(%rsp)
	movq	$0, 272(%rsp)
	movq	$0, 280(%rsp)
	movq	$0, 288(%rsp)
	movq	$0, 296(%rsp)
	movq	$0, 304(%rsp)
	movq	$0, 312(%rsp)
	movq	$0, 320(%rsp)
	movq	$0, 328(%rsp)
	movq	$0, 336(%rsp)
	movq	$0, 344(%rsp)
	movq	$0, 352(%rsp)
	movq	$0, 360(%rsp)
	movq	$0, 368(%rsp)
	movq	$0, 376(%rsp)
	movq	$0, 384(%rsp)
	movq	$0, 392(%rsp)
	movq	$0, 400(%rsp)
	movq	$0, 408(%rsp)
	movq	$0, 416(%rsp)
	movq	$0, 424(%rsp)
	movq	$0, 432(%rsp)
	movq	$0, 440(%rsp)
	movq	$0, 448(%rsp)
	movq	$0, 456(%rsp)
	movq	$0, 464(%rsp)
	movq	$0, 472(%rsp)
	movq	$0, 480(%rsp)
	movq	$0, 488(%rsp)
	movq	$0, 496(%rsp)
	movq	$0, 504(%rsp)
	movq	$0, 512(%rsp)
	movq	$0, 520(%rsp)
	movq	$0, 528(%rsp)
	movq	$0, 536(%rsp)
	movl	$1, %r12d
	movl	$1, %edi
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field4kinv
	movq	$1, 48(%rsp)
	movq	%rax, 56(%rsp)
	testq	%r14, %r14
	je	.LBB79_18
	leaq	(,%r14,8), %rax
	movq	%rax, 16(%rsp)
	movl	$1, %r15d
	leaq	544(%rsp), %rbx
	xorl	%r13d, %r13d
	movl	$1, %r12d
	movq	%r14, 8(%rsp)
	.p2align	4
.LBB79_13:
	movq	%r12, 24(%rsp)
	cmpq	%r13, %r14
	movq	%r13, 32(%rsp)
	movq	%r13, %rax
	cmovbq	%r14, %rax
	shlq	$3, %rax
	movq	16(%rsp), %rbp
	subq	%rax, %rbp
	xorl	%r14d, %r14d
	.p2align	4
.LBB79_14:
	movq	(%rbx,%r14), %r12
	movq	%r12, %rdi
	movq	%r12, %rsi
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field4kmul
	movq	%rax, %r13
	movq	%r15, %rdi
	movq	%r12, %rsi
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field4kmul
	xorq	%r13, %rax
	movq	%rax, (%rbx,%r14)
	addq	$8, %r14
	cmpq	%r14, %rbp
	jne	.LBB79_14
	movq	32(%rsp), %r13
	movq	544(%rsp,%r13,8), %r15
	movq	%r15, %rdi
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field4kinv
	cmpq	$30, %r13
	je	.LBB79_16
	incq	%r13
	movq	24(%rsp), %r12
	movq	%r12, %rcx
	shlq	$4, %rcx
	leaq	48(%rsp), %rdx
	movq	%r15, (%rdx,%rcx)
	movq	%rax, 8(%rdx,%rcx)
	incq	%r12
	addq	$8, %rbx
	movq	8(%rsp), %r14
	cmpq	%r14, %r13
	jne	.LBB79_13
.LBB79_18:
	movq	%r12, 40(%rsp)
	movq	(%rsp), %rbx
	leaq	8(%rbx), %rdi
	leaq	40(%rsp), %rsi
	movl	$504, %edx
	callq	*memcpy@GOTPCREL(%rip)
	movq	$1, (%rbx)
	jmp	.LBB79_2
.LBB79_16:
	movq	(%rsp), %rax
	movq	$0, (%rax)
.LBB79_2:
	addq	$792, %rsp
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
.Lfunc_end79:
	.size	_RNvNtCsemcRClSg8DH_9native_vm4whir14subspace_table, .Lfunc_end79-_RNvNtCsemcRClSg8DH_9native_vm4whir14subspace_table
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm4whir17subspace_at_table,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm4whir17subspace_at_table,@function
_RNvNtCsemcRClSg8DH_9native_vm4whir17subspace_at_table:
.Lfunc_begin80:
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
	subq	$280, %rsp
	.cfi_def_cfa_offset 336
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	%rcx, %r12
	movq	%rdx, %rbx
	movq	%rsi, %r15
	movq	%rdi, 16(%rsp)
	leaq	32(%rsp), %rdi
	movl	$248, %edx
	xorl	%esi, %esi
	callq	*memset@GOTPCREL(%rip)
	movq	%rbx, 8(%rsp)
	testq	%rbx, %rbx
	je	.LBB80_3
	movq	8(%rsp), %rax
	leaq	(,%rax,8), %rbx
	xorl	%r14d, %r14d
	.p2align	4
.LBB80_2:
	movq	(%r15,%r14,2), %r13
	movq	8(%r15,%r14,2), %rsi
	movq	%r12, %rdi
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field4kmul
	movq	%rax, 32(%rsp,%r14)
	movq	%r12, %rdi
	movq	%r12, %rsi
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field4kmul
	movq	%rax, %rbp
	movq	%r13, %rdi
	movq	%r12, %rsi
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field4kmul
	movq	%rax, %r12
	xorq	%rbp, %r12
	addq	$8, %r14
	cmpq	%r14, %rbx
	jne	.LBB80_2
.LBB80_3:
	movq	8(%rsp), %rax
	movq	%rax, 24(%rsp)
	leaq	24(%rsp), %rsi
	movl	$256, %edx
	movq	16(%rsp), %rdi
	callq	*memcpy@GOTPCREL(%rip)
	addq	$280, %rsp
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
.Lfunc_end80:
	.size	_RNvNtCsemcRClSg8DH_9native_vm4whir17subspace_at_table, .Lfunc_end80-_RNvNtCsemcRClSg8DH_9native_vm4whir17subspace_at_table
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm4whir22verify_stacked_opening,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm4whir22verify_stacked_opening,@function
_RNvNtCsemcRClSg8DH_9native_vm4whir22verify_stacked_opening:
.Lfunc_begin81:
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
	subq	$456, %rsp
	.cfi_def_cfa_offset 512
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	%r9, %r12
	movq	%rcx, 56(%rsp)
	movq	%rdx, %r14
	movq	%rsi, %rbp
	movq	(%r9), %rax
	leaq	8(%r9), %rcx
	xorl	%r15d, %r15d
	cmpq	$161, %rax
	cmovbq	%rax, %r15
	movl	$8, %r13d
	cmovbq	%rcx, %r13
	testq	%r15, %r15
	je	.LBB81_3
	leaq	120(%rbp), %rax
	cmpq	$1, %r15
	jne	.LBB81_4
	xorl	%ecx, %ecx
	xorl	%ebx, %ebx
	jmp	.LBB81_12
.LBB81_3:
	movq	%r8, 48(%rsp)
	movq	%r12, 32(%rsp)
	movq	%r14, 40(%rsp)
	movq	%rdi, 16(%rsp)
	callq	_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW7squeeze
	movl	$2, %ebx
	jmp	.LBB81_19
.LBB81_4:
	movl	%r15d, %edx
	andl	$254, %edx
	xorl	%ecx, %ecx
	movq	%r13, %rsi
	xorl	%ebx, %ebx
	jmp	.LBB81_7
	.p2align	4
.LBB81_5:
	leaq	(%r9,%r9,2), %r10
	xorl	%r9d, %r9d
	cmpq	$0, (%rax,%r10,8)
	setne	%r9b
.LBB81_6:
	addq	%r11, %rbx
	addq	%r9, %rbx
	addq	$2, %rcx
	addq	$1216, %rsi
	cmpq	%rcx, %rdx
	je	.LBB81_11
.LBB81_7:
	movq	(%rsi), %r9
	cmpq	$157, %r9
	ja	.LBB81_9
	leaq	(%r9,%r9,2), %r9
	xorl	%r11d, %r11d
	cmpq	$0, (%rax,%r9,8)
	setne	%r11b
	movq	608(%rsi), %r9
	cmpq	$157, %r9
	jbe	.LBB81_5
	jmp	.LBB81_10
	.p2align	4
.LBB81_9:
	xorl	%r11d, %r11d
	movq	608(%rsi), %r9
	cmpq	$157, %r9
	jbe	.LBB81_5
.LBB81_10:
	xorl	%r9d, %r9d
	jmp	.LBB81_6
.LBB81_11:
	testb	$1, %r15b
	je	.LBB81_16
.LBB81_12:
	imulq	$608, %rcx, %rcx
	movq	(%r13,%rcx), %rcx
	cmpq	$157, %rcx
	ja	.LBB81_14
	leaq	(%rcx,%rcx,2), %rdx
	xorl	%ecx, %ecx
	cmpq	$0, (%rax,%rdx,8)
	setne	%cl
	jmp	.LBB81_15
.LBB81_14:
	xorl	%ecx, %ecx
.LBB81_15:
	addq	%rcx, %rbx
.LBB81_16:
	addq	$2, %rbx
	cmpq	$512, %rbx
	ja	.LBB81_40
	movq	%r8, 48(%rsp)
	movq	%rdi, 16(%rsp)
	callq	_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW7squeeze
	cmpq	$162, %rbx
	ja	.LBB81_40
	movq	%r12, 32(%rsp)
	movq	%r14, 40(%rsp)
.LBB81_19:
	movq	520(%rsp), %r14
	leaq	8(%r14), %r12
	movq	%rbx, (%r14)
	movq	%rax, %rdi
	movq	%rdx, %rsi
	movq	%r12, %rdx
	movq	%rbx, %rcx
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field6powers
	movq	(%r14), %rax
	xorl	%esi, %esi
	cmpq	$163, %rax
	cmovaeq	%rsi, %rax
	movl	$8, %ecx
	cmovbq	%r12, %rcx
	movq	%rax, %r12
	shlq	$4, %r12
	movq	%rcx, %r14
	movl	$0, %edi
	movq	%rax, 80(%rsp)
	testq	%rax, %rax
	je	.LBB81_21
	leaq	16(%rcx), %r14
	movq	(%rcx), %rdi
	movq	8(%rcx), %rsi
.LBB81_21:
	movq	%rcx, 72(%rsp)
	addq	%rcx, %r12
	movq	56(%rsp), %rax
	movq	(%rax), %rdx
	movq	8(%rax), %rcx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	movq	%rax, %rbx
	movq	%rdx, 64(%rsp)
	testq	%r15, %r15
	movq	%rbp, 24(%rsp)
	je	.LBB81_30
	imulq	$608, %r15, %r15
	leaq	120(%rbp), %rax
	movq	%rax, 88(%rsp)
	xorl	%ebp, %ebp
	jmp	.LBB81_26
.LBB81_23:
	xorl	%esi, %esi
	xorl	%edi, %edi
.LBB81_24:
	movq	592(%r13,%rbp), %rdx
	movq	600(%r13,%rbp), %rcx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	xorq	%rax, %rbx
	xorq	%rdx, 64(%rsp)
.LBB81_25:
	addq	$608, %rbp
	cmpq	%rbp, %r15
	je	.LBB81_30
.LBB81_26:
	movq	(%r13,%rbp), %rax
	cmpq	$157, %rax
	ja	.LBB81_25
	leaq	(%rax,%rax,2), %rax
	movq	88(%rsp), %rcx
	cmpq	$0, (%rcx,%rax,8)
	je	.LBB81_25
	cmpq	%r12, %r14
	je	.LBB81_23
	movq	(%r14), %rdi
	movq	8(%r14), %rsi
	addq	$16, %r14
	jmp	.LBB81_24
.LBB81_30:
	movq	512(%rsp), %r15
	cmpq	%r12, %r14
	je	.LBB81_33
	movq	(%r14), %rdi
	movq	8(%r14), %rsi
	jmp	.LBB81_34
.LBB81_33:
	xorl	%esi, %esi
	xorl	%edi, %edi
.LBB81_34:
	movq	24(%rsp), %r14
	movq	488(%r15), %rdx
	movq	496(%r15), %rcx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	movq	%rax, %r12
	movq	%rdx, %r13
	movq	72(%rsp), %rax
	movq	%rax, 96(%rsp)
	movq	80(%rsp), %rax
	movq	%rax, 104(%rsp)
	movq	%r14, 112(%rsp)
	movq	56(%rsp), %rax
	movq	%rax, 120(%rsp)
	movq	48(%rsp), %rax
	movq	%rax, 128(%rsp)
	movq	32(%rsp), %rax
	movq	%rax, 136(%rsp)
	movq	%r15, 144(%rsp)
	movq	16(%r14), %r14
	leaq	152(%rsp), %rdi
	movq	%r14, %rsi
	movq	40(%rsp), %rdx
	callq	_RNvNtCsemcRClSg8DH_9native_vm4whir6ladder
	cmpb	$0, 152(%rsp)
	je	.LBB81_40
	leaq	160(%rsp), %rsi
	leaq	312(%rsp), %rdi
	movl	$144, %edx
	callq	*memcpy@GOTPCREL(%rip)
	movq	304(%rsp), %r9
	cmpq	$7, %r9
	jae	.LBB81_40
	movq	528(%rsp), %rax
	xorq	%rbx, %r12
	xorq	64(%rsp), %r13
	movq	%r9, %rdx
	testq	%r9, %r9
	je	.LBB81_38
	movq	312(%rsp), %rdx
.LBB81_38:
	movq	%r12, (%rax)
	movq	%r13, 8(%rax)
	movq	$0, 16(%rax)
	movq	$0, 504(%rax)
	movq	%rax, (%rsp)
	leaq	96(%rsp), %rcx
	leaq	312(%rsp), %r8
	movq	16(%rsp), %rdi
	movq	%r14, %rsi
	callq	_RNvNtCsemcRClSg8DH_9native_vm4whir11whir_levels
	jmp	.LBB81_41
.LBB81_40:
	xorl	%eax, %eax
.LBB81_41:
	addq	$456, %rsp
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
.Lfunc_end81:
	.size	_RNvNtCsemcRClSg8DH_9native_vm4whir22verify_stacked_opening, .Lfunc_end81-_RNvNtCsemcRClSg8DH_9native_vm4whir22verify_stacked_opening
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm4whir6ladder,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm4whir6ladder,@function
_RNvNtCsemcRClSg8DH_9native_vm4whir6ladder:
.Lfunc_begin82:
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
	subq	$24, %rsp
	.cfi_def_cfa_offset 80
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	leaq	-16(%rsi), %r14
	cmpq	$15, %r14
	setb	%al
	leaq	-1(%rdx), %r15
	cmpq	$4, %r15
	setb	%cl
	testb	%cl, %al
	je	.LBB82_11
	cmpq	$20, %rsi
	jge	.LBB82_3
	movl	$3, %ecx
	xorl	%r9d, %r9d
	xorl	%r12d, %r12d
	xorl	%r13d, %r13d
	xorl	%r10d, %r10d
	xorl	%r11d, %r11d
	xorl	%ebx, %ebx
	jmp	.LBB82_8
.LBB82_3:
	leaq	9(%rdx), %r9
	cmpq	$24, %rsi
	jge	.LBB82_5
	movl	$4, %r12d
	xorl	%r13d, %r13d
	xorl	%r10d, %r10d
	xorl	%r11d, %r11d
	xorl	%ebx, %ebx
	movl	$4, %ecx
	jmp	.LBB82_8
.LBB82_5:
	leaq	12(%rdx), %r10
	cmpq	$28, %rsi
	jge	.LBB82_7
	movl	$5, %ecx
	movl	$4, %r12d
	xorl	%r11d, %r11d
	movl	$4, %r13d
	xorl	%ebx, %ebx
	jmp	.LBB82_8
.LBB82_7:
	leaq	15(%rdx), %rbx
	movl	$6, %ecx
	movl	$4, %r12d
	movl	$4, %r13d
	movl	$4, %r11d
.LBB82_8:
	imulq	$120, %r15, %rax
	leaq	.Lanon.a75d6d9e6a8990b4224ef13f18552af8.12(%rip), %r8
	addq	%rax, %r8
	cmpq	%rcx, -128(%r8,%rsi,8)
	jne	.LBB82_11
	movq	%r13, (%rsp)
	movq	%r12, 8(%rsp)
	movq	%r10, 16(%rsp)
	movq	%r9, %r10
	leaq	3(%rdx), %r12
	leaq	6(%rdx), %rsi
	imulq	$720, %r15, %rax
	leaq	.Lanon.a75d6d9e6a8990b4224ef13f18552af8.11(%rip), %r9
	leaq	(%r14,%r14,2), %r8
	shlq	$4, %r8
	addq	%r9, %r8
	addq	%rax, %r8
	leaq	-1(%rcx), %r9
	movq	(%r8), %rbp
	movq	8(%r8), %r15
	movq	16(%r8), %r14
	cmpq	$2, %r9
	jne	.LBB82_12
	xorl	%r13d, %r13d
	jmp	.LBB82_13
.LBB82_11:
	xorl	%eax, %eax
	jmp	.LBB82_16
.LBB82_12:
	movq	24(%r8), %r13
	cmpl	$3, %r9d
	jne	.LBB82_17
.LBB82_13:
	xorl	%eax, %eax
.LBB82_14:
	xorl	%r8d, %r8d
.LBB82_15:
	movq	$6, 8(%rdi)
	movq	%rdx, 16(%rdi)
	movq	%rbp, 24(%rdi)
	movq	$4, 32(%rdi)
	movq	%r12, 40(%rdi)
	movq	%r15, 48(%rdi)
	movq	$4, 56(%rdi)
	movq	%rsi, 64(%rdi)
	movq	%r14, 72(%rdi)
	movq	8(%rsp), %rdx
	movq	%rdx, 80(%rdi)
	movq	%r10, 88(%rdi)
	movq	%r13, 96(%rdi)
	movq	(%rsp), %rdx
	movq	%rdx, 104(%rdi)
	movq	16(%rsp), %rdx
	movq	%rdx, 112(%rdi)
	movq	%rax, 120(%rdi)
	movq	%r11, 128(%rdi)
	movq	%rbx, 136(%rdi)
	movq	%r8, 144(%rdi)
	movq	%rcx, 152(%rdi)
	movl	$1, %eax
.LBB82_16:
	movq	%rax, (%rdi)
	addq	$24, %rsp
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
.LBB82_17:
	.cfi_def_cfa_offset 80
	movq	32(%r8), %rax
	cmpl	$4, %r9d
	je	.LBB82_14
	movq	40(%r8), %r8
	jmp	.LBB82_15
.Lfunc_end82:
	.size	_RNvNtCsemcRClSg8DH_9native_vm4whir6ladder, .Lfunc_end82-_RNvNtCsemcRClSg8DH_9native_vm4whir6ladder
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm4whir8fold_row,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm4whir8fold_row,@function
_RNvNtCsemcRClSg8DH_9native_vm4whir8fold_row:
.Lfunc_begin83:
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
	subq	$40, %rsp
	.cfi_def_cfa_offset 96
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	%rdx, 24(%rsp)
	movq	%rsi, %rbx
	movq	%rdi, %r14
	testq	%r8, %r8
	je	.LBB83_8
	shlq	$5, %r8
	addq	%rcx, %r8
	movq	%r8, 16(%rsp)
	jmp	.LBB83_3
	.p2align	4
.LBB83_2:
	movq	32(%rsp), %rcx
	addq	$32, %rcx
	movq	16(%rsp), %r8
	cmpq	%r8, %rcx
	je	.LBB83_8
.LBB83_3:
	movq	(%rcx), %r13
	movq	8(%rcx), %r12
	movq	16(%rcx), %rsi
	movq	%rcx, 32(%rsp)
	movq	24(%rcx), %r15
	movq	24(%rsp), %rbp
	movq	%rbp, %rdi
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field4kmul
	movq	%rax, 8(%rsp)
	movq	%rbp, %rdi
	movq	%r15, %rsi
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field4kmul
	movq	%rax, (%rsp)
	shrq	%rbx
	je	.LBB83_2
	xorq	%r13, 8(%rsp)
	xorq	%r12, (%rsp)
	movl	$8, %r13d
	xorl	%r12d, %r12d
	jmp	.LBB83_5
	.p2align	4
.LBB83_7:
	incq	%r12
	addq	$16, %r13
	cmpq	%r12, %rbx
	je	.LBB83_2
.LBB83_5:
	cmpq	$31, %r12
	ja	.LBB83_7
	movq	-16(%r14,%r13,2), %rdx
	movq	-8(%r14,%r13,2), %rcx
	movq	(%r14,%r13,2), %rbp
	movq	8(%r14,%r13,2), %r15
	movq	8(%rsp), %rdi
	movq	(%rsp), %rsi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	xorq	%r15, %rdx
	xorq	%rbp, %rax
	movq	%rax, -8(%r14,%r13)
	movq	%rdx, (%r14,%r13)
	jmp	.LBB83_7
.LBB83_8:
	movq	%rbx, %rax
	testq	%rbx, %rbx
	je	.LBB83_10
	movq	8(%r14), %rbx
	movq	(%r14), %rax
.LBB83_10:
	movq	%rbx, %rdx
	addq	$40, %rsp
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
.Lfunc_end83:
	.size	_RNvNtCsemcRClSg8DH_9native_vm4whir8fold_row, .Lfunc_end83-_RNvNtCsemcRClSg8DH_9native_vm4whir8fold_row
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm4whir8lanes_of,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm4whir8lanes_of,@function
_RNvNtCsemcRClSg8DH_9native_vm4whir8lanes_of:
.Lfunc_begin84:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	testq	%rdi, %rdi
	je	.LBB84_1
	cmpq	$130, %rdx
	jae	.LBB84_2
	movq	%rdx, %r8
	shrq	%rdx
	movl	$1, %eax
	je	.LBB84_14
	cmpq	$1, %rdx
	jne	.LBB84_15
	xorl	%edi, %edi
	jmp	.LBB84_13
.LBB84_1:
	cmpq	$65, %rdx
	jae	.LBB84_2
	movl	$1, %eax
	testq	%rdx, %rdx
	je	.LBB84_8
	movq	%rdx, %rdi
	shlq	$4, %rdi
	addq	%rcx, %rdi
	leaq	-8(,%rdx,8), %r8
	.p2align	4
.LBB84_10:
	movq	(%rsi,%r8), %r9
	movq	%r9, (%rcx)
	movq	$0, 8(%rcx)
	addq	$16, %rcx
	cmpq	%rdi, %rcx
	je	.LBB84_14
	testq	%r8, %r8
	leaq	-8(%r8), %r8
	jne	.LBB84_10
.LBB84_14:
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.LBB84_2:
	.cfi_def_cfa_offset 16
	xorl	%eax, %eax
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.LBB84_15:
	.cfi_def_cfa_offset 16
	movl	%edx, %r9d
	andl	$126, %r9d
	movl	$24, %r10d
	xorl	%edi, %edi
	.p2align	4
.LBB84_16:
	movq	-24(%rsi,%r10), %r11
	movq	-16(%rsi,%r10), %rbx
	movq	%r11, -24(%rcx,%r10)
	movq	%rbx, -16(%rcx,%r10)
	addq	$2, %rdi
	movq	-8(%rsi,%r10), %r11
	movq	(%rsi,%r10), %rbx
	movq	%r11, -8(%rcx,%r10)
	movq	%rbx, (%rcx,%r10)
	addq	$32, %r10
	cmpq	%rdi, %r9
	jne	.LBB84_16
	testb	$2, %r8b
	je	.LBB84_14
.LBB84_13:
	shlq	$4, %rdi
	movq	(%rsi,%rdi), %r8
	movq	8(%rsi,%rdi), %rsi
	movq	%r8, (%rcx,%rdi)
	movq	%rsi, 8(%rcx,%rdi)
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.LBB84_8:
	.cfi_def_cfa_offset 16
	xorl	%edx, %edx
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end84:
	.size	_RNvNtCsemcRClSg8DH_9native_vm4whir8lanes_of, .Lfunc_end84-_RNvNtCsemcRClSg8DH_9native_vm4whir8lanes_of
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm4wire11climb_level,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm4wire11climb_level,@function
_RNvNtCsemcRClSg8DH_9native_vm4wire11climb_level:
.Lfunc_begin85:
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
	subq	$152, %rsp
	.cfi_def_cfa_offset 208
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	%rdi, 32(%rsp)
	movl	$1, %eax
	testq	%rdx, %rdx
	je	.LBB85_1
	movq	%r8, %r14
	movq	%rcx, %r15
	movq	%rsi, %rbp
	shlq	$3, %rdx
	leaq	(%rdx,%rdx,4), %rax
	movq	%rax, 56(%rsp)
	addq	%rsi, %rax
	movq	%rax, 40(%rsp)
	leaq	-40(%rsi), %rax
	movq	%rax, 48(%rsp)
	xorl	%ebx, %ebx
	xorl	%r12d, %r12d
	jmp	.LBB85_3
	.p2align	4
.LBB85_7:
	movq	72(%rsp), %rbp
	cmpq	40(%rsp), %rbp
	movq	64(%rsp), %r12
	je	.LBB85_8
.LBB85_3:
	leaq	40(%rbp), %rax
	movq	%rax, 72(%rsp)
	leaq	1(%r12), %rax
	movq	%rax, 64(%rsp)
	movq	56(%rsp), %rcx
	movq	48(%rsp), %rax
	.p2align	4
.LBB85_4:
	testq	%rcx, %rcx
	je	.LBB85_9
	movq	(%rbp), %r13
	movq	40(%rax), %rsi
	xorq	%r13, %rsi
	addq	$40, %rax
	addq	$-40, %rcx
	cmpq	$1, %rsi
	jne	.LBB85_4
	movq	32(%rax), %rcx
	movq	%rcx, 24(%rsp)
	movq	24(%rax), %rcx
	movq	%rcx, 16(%rsp)
	movq	8(%rax), %rcx
	movq	16(%rax), %rdx
	movq	%rdx, 8(%rsp)
	movq	%rcx, (%rsp)
	leaq	(%r12,%r12,4), %rcx
	movq	%r13, (%r15,%rcx,8)
	movq	8(%rax), %rdx
	movq	16(%rax), %rsi
	movq	%rdx, 8(%r15,%rcx,8)
	movq	%rsi, 16(%r15,%rcx,8)
	movq	24(%rax), %rdx
	movq	%rdx, 24(%r15,%rcx,8)
	movq	32(%rax), %rax
	movq	%rax, 32(%r15,%rcx,8)
	testb	$1, %r13b
	jne	.LBB85_7
	jmp	.LBB85_13
	.p2align	4
.LBB85_9:
	leaq	112(%rsp), %rdi
	movq	32(%rsp), %rsi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm4wireNtB2_6Reader6digest
	cmpb	$0, 112(%rsp)
	je	.LBB85_10
	leaq	120(%rsp), %rcx
	movq	24(%rcx), %rax
	movq	%rax, 24(%rsp)
	movq	16(%rcx), %rax
	movq	%rax, 16(%rsp)
	movq	(%rcx), %rax
	movq	8(%rcx), %rcx
	movq	%rcx, 8(%rsp)
	movq	%rax, (%rsp)
	movq	(%rbp), %r13
	leaq	(%r12,%r12,4), %rax
	movq	%r13, (%r15,%rax,8)
	movq	(%rsp), %rcx
	movq	8(%rsp), %rdx
	movq	%rcx, 8(%r15,%rax,8)
	movq	%rdx, 16(%r15,%rax,8)
	movq	16(%rsp), %rcx
	movq	%rcx, 24(%r15,%rax,8)
	movq	24(%rsp), %rcx
	movq	%rcx, 32(%r15,%rax,8)
	testb	$1, %r13b
	jne	.LBB85_16
.LBB85_13:
	addq	$8, %rbp
	leaq	80(%rsp), %rdi
	movq	%rbp, %rsi
	movq	%rsp, %rdx
	callq	_RNvNtCsemcRClSg8DH_9native_vm6keccak9hash_pair
	cmpq	$256, %rbx
	jb	.LBB85_17
	jmp	.LBB85_15
	.p2align	4
.LBB85_16:
	addq	$8, %rbp
	leaq	80(%rsp), %rdi
	movq	%rsp, %rsi
	movq	%rbp, %rdx
	callq	_RNvNtCsemcRClSg8DH_9native_vm6keccak9hash_pair
	cmpq	$256, %rbx
	jae	.LBB85_15
.LBB85_17:
	shrq	%r13
	leaq	(%rbx,%rbx,4), %rax
	movq	%r13, (%r14,%rax,8)
	movq	80(%rsp), %rcx
	movq	88(%rsp), %rsi
	movq	%rcx, 8(%r14,%rax,8)
	movq	%rsi, 16(%r14,%rax,8)
	movq	96(%rsp), %rcx
	movq	%rcx, 24(%r14,%rax,8)
	movq	104(%rsp), %rcx
	movq	%rcx, 32(%r14,%rax,8)
	incq	%rbx
	jmp	.LBB85_7
.LBB85_1:
	xorl	%ebx, %ebx
	jmp	.LBB85_11
.LBB85_8:
	movl	$1, %eax
	jmp	.LBB85_11
.LBB85_15:
	xorl	%eax, %eax
	jmp	.LBB85_11
.LBB85_10:
	xorl	%eax, %eax
.LBB85_11:
	movq	%rbx, %rdx
	addq	$152, %rsp
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
.Lfunc_end85:
	.size	_RNvNtCsemcRClSg8DH_9native_vm4wire11climb_level, .Lfunc_end85-_RNvNtCsemcRClSg8DH_9native_vm4wire11climb_level
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm4wire14write_openings,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm4wire14write_openings,@function
_RNvNtCsemcRClSg8DH_9native_vm4wire14write_openings:
.Lfunc_begin86:
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
	subq	$104, %rsp
	.cfi_def_cfa_offset 160
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	184(%rsp), %rbp
	movq	160(%rsp), %rax
	movq	%rsi, (%rbp)
	movq	%rax, 8(%rbp)
	movq	%r9, 16(%rbp)
	leaq	(%rdi,%rsi,8), %r14
	shlq	$3, %rcx
	testq	%rax, %rax
	je	.LBB86_20
	movq	168(%rsp), %rbx
	movl	%r9d, %r13d
	andl	$3, %r13d
	movq	%r9, 24(%rsp)
	andl	$124, %r9d
	movq	%r9, 80(%rsp)
	leaq	24(%r8), %r9
	leaq	56(%rbp), %r12
	leaq	32(%rbp), %rax
	movq	%rax, 32(%rsp)
	leaq	568(%rbp), %rax
	movq	%rax, 8(%rsp)
	xorl	%esi, %esi
	movq	%r8, %r11
	movq	%r9, 88(%rsp)
.LBB86_2:
	movq	(%rdi), %r15
	addq	$8, %rdi
	imulq	$1544, %rsi, %rax
	incq	%rsi
	movq	%rsi, 96(%rsp)
	movq	%r15, 24(%rbp,%rax)
	movq	%r11, %rax
	movq	%rcx, %r8
	xorl	%esi, %esi
	movq	24(%rsp), %r10
	.p2align	4
.LBB86_3:
	cmpq	%r15, (%rdx,%rsi,8)
	je	.LBB86_5
	incq	%rsi
	addq	$512, %r9
	addq	$512, %rax
	addq	$-8, %r8
	jne	.LBB86_3
	jmp	.LBB86_45
	.p2align	4
.LBB86_5:
	movq	%r14, 48(%rsp)
	movq	%rdi, 56(%rsp)
	movq	%rcx, 72(%rsp)
	testq	%r10, %r10
	je	.LBB86_12
	xorl	%ecx, %ecx
	cmpq	$4, %r10
	jb	.LBB86_10
	movq	80(%rsp), %rdi
	.p2align	4
.LBB86_8:
	movq	-24(%r9), %rsi
	movq	%rsi, -24(%r12,%rcx,8)
	movq	-16(%r9), %rsi
	movq	%rsi, -16(%r12,%rcx,8)
	movq	-8(%r9), %rsi
	movq	%rsi, -8(%r12,%rcx,8)
	movq	(%r9), %rsi
	movq	%rsi, (%r12,%rcx,8)
	addq	$4, %rcx
	addq	$32, %r9
	cmpq	%rcx, %rdi
	jne	.LBB86_8
	testq	%r13, %r13
	je	.LBB86_12
.LBB86_10:
	leaq	(%rax,%rcx,8), %rax
	movq	32(%rsp), %rsi
	leaq	(%rsi,%rcx,8), %rcx
	xorl	%edi, %edi
	.p2align	4
.LBB86_11:
	movq	(%rax,%rdi,8), %rsi
	movq	%rsi, (%rcx,%rdi,8)
	incq	%rdi
	cmpq	%rdi, %r13
	jne	.LBB86_11
.LBB86_12:
	movq	%r13, 40(%rsp)
	movq	%r11, 16(%rsp)
	movq	%rdx, 64(%rsp)
	movq	%rbx, %rbp
	movq	8(%rsp), %r14
	xorl	%r13d, %r13d
	jmp	.LBB86_15
	.p2align	4
.LBB86_13:
	leaq	(%rdx,%rdx,4), %rax
	movq	8(%rbp,%rax,8), %rsi
	movq	16(%rbp,%rax,8), %rdx
	movq	24(%rbp,%rax,8), %rcx
	movq	32(%rbp,%rax,8), %rax
.LBB86_14:
	incq	%r13
	movq	%rsi, -24(%r14)
	movq	%rdx, -16(%r14)
	movq	%rcx, -8(%r14)
	movq	%rax, (%r14)
	addq	$32, %r14
	addq	$10240, %rbp
	cmpq	%r13, 160(%rsp)
	je	.LBB86_18
.LBB86_15:
	movq	176(%rsp), %rax
	movq	(%rax,%r13,8), %rbx
	cmpq	$256, %rbx
	ja	.LBB86_45
	movq	%r15, %rdx
	movl	%r13d, %ecx
	shrq	%cl, %rdx
	movq	%rbp, %rdi
	movq	%rbx, %rsi
	callq	_RNvNtCsemcRClSg8DH_9native_vm4wire4find
	cmpq	%rbx, %rdx
	setb	%cl
	andb	%al, %cl
	cmpb	$1, %cl
	je	.LBB86_13
	xorl	%eax, %eax
	xorl	%ecx, %ecx
	xorl	%edx, %edx
	xorl	%esi, %esi
	jmp	.LBB86_14
	.p2align	4
.LBB86_18:
	addq	$1544, %r12
	addq	$1544, 32(%rsp)
	addq	$1544, 8(%rsp)
	movb	$1, %al
	movq	56(%rsp), %rdi
	movq	48(%rsp), %r14
	cmpq	%r14, %rdi
	movq	72(%rsp), %rcx
	movq	64(%rsp), %rdx
	movq	184(%rsp), %rbp
	movq	16(%rsp), %r11
	movq	168(%rsp), %rbx
	movq	40(%rsp), %r13
	movq	88(%rsp), %r9
	movq	96(%rsp), %rsi
	jne	.LBB86_2
	jmp	.LBB86_46
.LBB86_20:
	testq	%r9, %r9
	je	.LBB86_35
	movl	%r9d, %r15d
	andl	$3, %r15d
	movq	%r9, 24(%rsp)
	movl	%r9d, %r12d
	andl	$124, %r12d
	leaq	24(%r8), %rbx
	movq	%r8, %r10
	leaq	56(%rbp), %r13
	leaq	32(%rbp), %r8
	xorl	%r9d, %r9d
	movq	%r10, 16(%rsp)
	movq	%rbx, 8(%rsp)
.LBB86_22:
	movq	%r14, %rsi
	movq	(%rdi), %r11
	addq	$8, %rdi
	imulq	$1544, %r9, %rax
	incq	%r9
	movq	%r11, 24(%rbp,%rax)
	movq	%r10, %rax
	movq	%rbx, %r10
	movq	%rcx, %rbx
	xorl	%r14d, %r14d
	.p2align	4
.LBB86_23:
	cmpq	%r11, (%rdx,%r14,8)
	je	.LBB86_25
	incq	%r14
	addq	$512, %r10
	addq	$512, %rax
	addq	$-8, %rbx
	jne	.LBB86_23
	jmp	.LBB86_45
	.p2align	4
.LBB86_25:
	cmpq	$4, 24(%rsp)
	jae	.LBB86_27
	xorl	%r11d, %r11d
	movq	%rsi, %r14
	jmp	.LBB86_30
.LBB86_27:
	xorl	%r11d, %r11d
	movq	%rsi, %r14
	.p2align	4
.LBB86_28:
	movq	-24(%r10), %rbx
	movq	%rbx, -24(%r13,%r11,8)
	movq	-16(%r10), %rbx
	movq	%rbx, -16(%r13,%r11,8)
	movq	-8(%r10), %rbx
	movq	%rbx, -8(%r13,%r11,8)
	movq	(%r10), %rbx
	movq	%rbx, (%r13,%r11,8)
	addq	$4, %r11
	addq	$32, %r10
	cmpq	%r11, %r12
	jne	.LBB86_28
	testq	%r15, %r15
	je	.LBB86_32
.LBB86_30:
	leaq	(%rax,%r11,8), %rax
	leaq	(%r8,%r11,8), %r10
	xorl	%r11d, %r11d
	.p2align	4
.LBB86_31:
	movq	(%rax,%r11,8), %rbx
	movq	%rbx, (%r10,%r11,8)
	incq	%r11
	cmpq	%r11, %r15
	jne	.LBB86_31
.LBB86_32:
	addq	$1544, %r13
	addq	$1544, %r8
	movb	$1, %al
	cmpq	%r14, %rdi
	movq	16(%rsp), %r10
	movq	8(%rsp), %rbx
	jne	.LBB86_22
	jmp	.LBB86_46
.LBB86_35:
	xorl	%r9d, %r9d
.LBB86_36:
	leaq	8(%rdi), %rsi
	movq	(%rdi), %rax
	imulq	$1544, %r9, %r10
	movq	%rax, 24(%rbp,%r10)
	movq	%rcx, %r11
	xorl	%r8d, %r8d
	.p2align	4
.LBB86_37:
	cmpq	%rax, (%rdx,%r8,8)
	je	.LBB86_39
	incq	%r8
	addq	$-8, %r11
	jne	.LBB86_37
	jmp	.LBB86_45
.LBB86_39:
	movb	$1, %al
	cmpq	%r14, %rsi
	je	.LBB86_46
	addq	$2, %r9
	movq	8(%rdi), %rsi
	addq	$16, %rdi
	movq	%rsi, 1568(%rbp,%r10)
	movq	%rcx, %r8
	xorl	%r10d, %r10d
	.p2align	4
.LBB86_41:
	cmpq	%rsi, (%rdx,%r10,8)
	je	.LBB86_43
	incq	%r10
	addq	$-8, %r8
	jne	.LBB86_41
	jmp	.LBB86_45
.LBB86_43:
	cmpq	%r14, %rdi
	jne	.LBB86_36
	jmp	.LBB86_46
.LBB86_45:
	xorl	%eax, %eax
.LBB86_46:
	addq	$104, %rsp
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
.Lfunc_end86:
	.size	_RNvNtCsemcRClSg8DH_9native_vm4wire14write_openings, .Lfunc_end86-_RNvNtCsemcRClSg8DH_9native_vm4wire14write_openings
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm4wire4find,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm4wire4find,@function
_RNvNtCsemcRClSg8DH_9native_vm4wire4find:
.Lfunc_begin87:
	.cfi_startproc
	testq	%rsi, %rsi
	je	.LBB87_1
	movq	%rdx, %rcx
	shlq	$3, %rsi
	leaq	(%rsi,%rsi,4), %rsi
	xorl	%eax, %eax
	xorl	%r8d, %r8d
	xorl	%edx, %edx
	.p2align	4
.LBB87_3:
	cmpq	%rcx, (%rdi,%r8)
	je	.LBB87_4
	incq	%rdx
	addq	$40, %r8
	cmpq	%r8, %rsi
	jne	.LBB87_3
	retq
.LBB87_1:
	xorl	%eax, %eax
	retq
.LBB87_4:
	movl	$1, %eax
	retq
.Lfunc_end87:
	.size	_RNvNtCsemcRClSg8DH_9native_vm4wire4find, .Lfunc_end87-_RNvNtCsemcRClSg8DH_9native_vm4wire4find
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm4wire5ins_d,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm4wire5ins_d,@function
_RNvNtCsemcRClSg8DH_9native_vm4wire5ins_d:
.Lfunc_begin88:
	.cfi_startproc
	movq	%rsi, %rax
	xorl	%ecx, %ecx
	testq	%rsi, %rsi
	je	.LBB88_1
	.p2align	4
.LBB88_7:
	movzbl	%cl, %esi
	cmpq	%rdx, (%rdi,%rsi,8)
	jae	.LBB88_11
	incq	%rcx
	cmpq	%rcx, %rax
	jne	.LBB88_7
	movq	%rax, %rcx
	movzbl	%cl, %ecx
	movq	%rdx, (%rdi,%rcx,8)
	incq	%rax
	retq
.LBB88_11:
	jne	.LBB88_1
	retq
.LBB88_1:
	cmpq	$255, %rax
	movl	$255, %r8d
	cmovbq	%rax, %r8
	cmpq	%rcx, %r8
	jbe	.LBB88_10
	movl	%r8d, %r9d
	subl	%ecx, %r9d
	movq	%r8, %rsi
	andl	$3, %r9d
	je	.LBB88_5
	movq	%r8, %r10
	.p2align	4
.LBB88_4:
	leaq	-1(%r10), %rsi
	movzbl	%r10b, %r10d
	movzbl	%sil, %r11d
	movq	(%rdi,%r11,8), %r11
	movq	%r11, (%rdi,%r10,8)
	movq	%rsi, %r10
	decq	%r9
	jne	.LBB88_4
.LBB88_5:
	movq	%rcx, %r9
	subq	%r8, %r9
	cmpq	$-4, %r9
	ja	.LBB88_10
	.p2align	4
.LBB88_6:
	leal	-1(%rsi), %r8d
	movzbl	%sil, %r9d
	movzbl	%r8b, %r8d
	movq	(%rdi,%r8,8), %r10
	movq	%r10, (%rdi,%r9,8)
	leal	-2(%rsi), %r9d
	movzbl	%r9b, %r9d
	movq	(%rdi,%r9,8), %r10
	movq	%r10, (%rdi,%r8,8)
	leal	-3(%rsi), %r8d
	movzbl	%r8b, %r8d
	movq	(%rdi,%r8,8), %r10
	movq	%r10, (%rdi,%r9,8)
	addq	$-4, %rsi
	movzbl	%sil, %r9d
	movq	(%rdi,%r9,8), %r9
	movq	%r9, (%rdi,%r8,8)
	cmpq	%rcx, %rsi
	ja	.LBB88_6
.LBB88_10:
	movzbl	%cl, %ecx
	movq	%rdx, (%rdi,%rcx,8)
	incq	%rax
	retq
.Lfunc_end88:
	.size	_RNvNtCsemcRClSg8DH_9native_vm4wire5ins_d, .Lfunc_end88-_RNvNtCsemcRClSg8DH_9native_vm4wire5ins_d
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm4wire6decode,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm4wire6decode,@function
_RNvNtCsemcRClSg8DH_9native_vm4wire6decode:
.Lfunc_begin89:
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
	subq	$24, %rsp
	.cfi_def_cfa_offset 80
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	%r8, %rbx
	movq	%rcx, %r14
	movq	%rdx, %r13
	movq	%rsi, %r15
	movq	%rdi, (%rsp)
	movq	%rsi, 8(%rsp)
	movq	$0, 16(%rsp)
	movq	%rsp, %rdi
	movl	$4, %esi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm4wireNtB2_6Reader2le
	cmpq	$1, %rax
	jne	.LBB89_9
	movq	%rdx, %rcx
	addq	%rdx, %rdx
	cmpq	%r14, %rdx
	jae	.LBB89_9
	movq	%rcx, %r12
	leaq	8(%r13), %rsi
	movq	%rsp, %rdi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm4wireNtB2_6Reader5words
	testb	%al, %al
	je	.LBB89_9
	movq	%r12, (%r13)
	movq	%rsp, %rdi
	movl	$4, %esi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm4wireNtB2_6Reader2le
	cmpq	$9, %rdx
	setb	%cl
	andb	%al, %cl
	cmpb	$1, %cl
	jne	.LBB89_9
	movq	%r15, %rax
	shrq	$3, %rax
	orq	$1, %rax
	cmpq	%r14, %rax
	jae	.LBB89_9
	movq	%rdx, %r12
	movq	%rdx, (%r13,%rax,8)
	leaq	-395280(%r13,%rax,8), %r13
	notq	%rax
	addq	%rax, %r14
	movabsq	$6019990451287497113, %rcx
	movq	%r14, %rax
	mulq	%rcx
	subq	%rdx, %r14
	shrq	%r14
	addq	%rdx, %r14
	shrq	$15, %r14
	incq	%r14
	xorl	%ebp, %ebp
	.p2align	4
.LBB89_6:
	cmpq	%rbp, %r12
	je	.LBB89_7
	incq	%rbp
	cmpq	%rbp, %r14
	je	.LBB89_9
	addq	$395288, %r13
	movq	%rsp, %rdi
	movq	%r13, %rsi
	movq	%rbx, %rdx
	callq	_RNvNtCsemcRClSg8DH_9native_vm4wire7phase_m
	movl	%eax, %ecx
	xorl	%eax, %eax
	testb	%cl, %cl
	jne	.LBB89_6
	jmp	.LBB89_10
.LBB89_9:
	xorl	%eax, %eax
.LBB89_10:
	addq	$24, %rsp
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
.LBB89_7:
	.cfi_def_cfa_offset 80
	cmpq	%r15, 16(%rsp)
	sete	%al
	jmp	.LBB89_10
.Lfunc_end89:
	.size	_RNvNtCsemcRClSg8DH_9native_vm4wire6decode, .Lfunc_end89-_RNvNtCsemcRClSg8DH_9native_vm4wire6decode
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm4wire7phase_m,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm4wire7phase_m,@function
_RNvNtCsemcRClSg8DH_9native_vm4wire7phase_m:
.Lfunc_begin90:
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
	subq	$104, %rsp
	.cfi_def_cfa_offset 160
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	%rdx, %r14
	movq	%rsi, 40(%rsp)
	movq	%rdi, %r12
	movl	$4, %esi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm4wireNtB2_6Reader2le
	movq	%rdx, 32(%rsp)
	cmpq	$257, %rdx
	setb	%cl
	andb	%al, %cl
	cmpb	$1, %cl
	jne	.LBB90_23
	movq	32(%rsp), %rax
	leaq	(,%rax,8), %r13
	testq	%rax, %rax
	je	.LBB90_5
	xorl	%r15d, %r15d
	.p2align	4
.LBB90_3:
	movl	$4, %esi
	movq	%r12, %rdi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm4wireNtB2_6Reader2le
	testb	$1, %al
	je	.LBB90_23
	movq	%rdx, (%r14,%r15)
	addq	$8, %r15
	cmpq	%r15, %r13
	jne	.LBB90_3
.LBB90_5:
	movl	$4, %esi
	movq	%r12, %rdi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm4wireNtB2_6Reader2le
	movq	%rdx, 24(%rsp)
	testb	$1, %al
	je	.LBB90_23
	movl	$4, %esi
	movq	%r12, %rdi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm4wireNtB2_6Reader2le
	movq	%rdx, 8(%rsp)
	cmpq	$1, %rax
	jne	.LBB90_23
	cmpq	$0, 32(%rsp)
	sete	%bpl
	movl	$4, %esi
	movq	%r12, %rdi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm4wireNtB2_6Reader2le
	notb	%al
	orb	%bpl, %al
	testb	$1, %al
	jne	.LBB90_23
	movq	%rdx, 16(%rsp)
	leaq	2048(%r14), %rdi
	xorl	%ebp, %ebp
	xorl	%r15d, %r15d
	.p2align	4
.LBB90_9:
	movq	(%r14,%r15), %rdx
	movq	%rbp, %rsi
	movq	%rdi, %rbx
	callq	_RNvNtCsemcRClSg8DH_9native_vm4wire5ins_d
	movq	%rbx, %rdi
	movq	%rax, %rbp
	addq	$8, %r15
	cmpq	%r15, %r13
	jne	.LBB90_9
	leaq	-257(%rbp), %rax
	cmpq	$-256, %rax
	movq	16(%rsp), %r15
	jae	.LBB90_11
.LBB90_23:
	xorl	%eax, %eax
	addq	$104, %rsp
	.cfi_def_cfa_offset 56
.LBB90_24:
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
.LBB90_11:
	.cfi_def_cfa_offset 160
	movq	-8(%rdi,%rbp,8), %rax
	movq	24(%rsp), %rcx
	shrq	%cl, %rax
	cmpq	$32, %rcx
	ja	.LBB90_23
	cmpq	$64, 8(%rsp)
	ja	.LBB90_23
	cmpq	8(%rsp), %r15
	ja	.LBB90_23
	testq	%rax, %rax
	jne	.LBB90_23
	leaq	352512(%r14), %r8
	movq	%r12, %rdi
	movq	%rbp, %rsi
	movq	8(%rsp), %rdx
	movq	%r15, %rcx
	movq	%r8, 48(%rsp)
	callq	_RNvNtCsemcRClSg8DH_9native_vm4wire7rd_rows
	cmpb	$2, %al
	sete	%cl
	testq	%r15, %r15
	setne	%dl
	andb	%al, %dl
	orb	%cl, %dl
	jne	.LBB90_23
	movq	8(%rsp), %r9
	movq	%r9, %rax
	shlq	$3, %rax
	movq	%rax, 56(%rsp)
	movl	$513, %r13d
	xorl	%r15d, %r15d
	leaq	352512(%r14), %rcx
.LBB90_17:
	movq	%rcx, 16(%rsp)
	movq	2048(%r14,%r15,8), %rax
	movq	%rax, 64(%rsp)
	incq	%r15
	leaq	72(%rsp), %rdi
	movq	%r9, %rsi
	movq	56(%rsp), %rdx
	movq	16(%rsp), %rcx
	movq	%r9, %r8
	callq	_RINvNtCsemcRClSg8DH_9native_vm6keccak15keccak256_wordsNCNvB2_10hash_words0EB4_
	movq	8(%rsp), %r9
	movq	64(%rsp), %rax
	movq	%rax, -8(%r14,%r13,8)
	movq	72(%rsp), %rax
	movq	80(%rsp), %rcx
	movq	%rax, (%r14,%r13,8)
	movq	%rcx, 8(%r14,%r13,8)
	movq	16(%rsp), %rcx
	movq	88(%rsp), %rax
	movq	%rax, 16(%r14,%r13,8)
	movq	96(%rsp), %rax
	movq	%rax, 24(%r14,%r13,8)
	addq	$512, %rcx
	addq	$5, %r13
	cmpq	%r15, %rbp
	jne	.LBB90_17
	leaq	24832(%r14), %r11
	cmpq	$0, 24(%rsp)
	je	.LBB90_19
	xorl	%edi, %edi
	xorl	%r13d, %r13d
	movq	%rbp, %rdx
.LBB90_22:
	cmpq	$257, %rdx
	jae	.LBB90_23
	testb	$1, %r13b
	leaq	14336(%r14), %rax
	movq	%rax, %rsi
	leaq	4096(%r14), %r8
	cmoveq	%r8, %rsi
	cmoveq	%rax, %r8
	leaq	(%r11,%rdi), %rcx
	movq	%rdi, 16(%rsp)
	movq	%r12, %rdi
	movq	%rdx, %r15
	callq	_RNvNtCsemcRClSg8DH_9native_vm4wire11climb_level
	movq	16(%rsp), %rdi
	leaq	24832(%r14), %r11
	cmpq	$1, %rax
	jne	.LBB90_23
	movq	%r15, -256(%r11,%r13,8)
	incq	%r13
	addq	$10240, %rdi
	movq	24(%rsp), %r10
	cmpq	%r13, %r10
	jne	.LBB90_22
	movq	%rbx, %rcx
	movq	8(%rsp), %r9
	movq	40(%rsp), %r15
	jmp	.LBB90_20
.LBB90_19:
	xorl	%r10d, %r10d
	movq	40(%rsp), %r15
	movq	%rbx, %rcx
.LBB90_20:
	leaq	24576(%r14), %rax
	movq	%r14, %rdi
	movq	32(%rsp), %rsi
	movq	%rcx, %rdx
	movq	%rbp, %rcx
	movq	48(%rsp), %r8
	pushq	%r15
	.cfi_adjust_cfa_offset 8
	pushq	%rax
	.cfi_adjust_cfa_offset 8
	pushq	%r11
	.cfi_adjust_cfa_offset 8
	pushq	%r10
	.cfi_adjust_cfa_offset 8
	callq	_RNvNtCsemcRClSg8DH_9native_vm4wire14write_openings
	addq	$136, %rsp
	.cfi_adjust_cfa_offset -136
	jmp	.LBB90_24
.Lfunc_end90:
	.size	_RNvNtCsemcRClSg8DH_9native_vm4wire7phase_m, .Lfunc_end90-_RNvNtCsemcRClSg8DH_9native_vm4wire7phase_m
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm4wire7rd_rows,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm4wire7rd_rows,@function
_RNvNtCsemcRClSg8DH_9native_vm4wire7rd_rows:
.Lfunc_begin91:
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
	subq	$24, %rsp
	.cfi_def_cfa_offset 80
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	%rdx, %r15
	movq	%rdi, 8(%rsp)
	movq	%rdx, (%rsp)
	movb	$2, %bl
	subq	%rcx, %r15
	jae	.LBB91_2
.LBB91_20:
	movb	$2, %bl
.LBB91_21:
	movl	%ebx, %eax
	addq	$24, %rsp
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
.LBB91_2:
	.cfi_def_cfa_offset 80
	movq	%r8, %r14
	movq	%rcx, %rbp
	movq	%rsi, %r12
	shlq	$9, %r12
	addq	%r8, %r12
	testq	%rcx, %rcx
	je	.LBB91_9
	shlq	$3, %r15
	movb	$1, %bl
	.p2align	4
.LBB91_4:
	cmpq	%rbp, (%rsp)
	je	.LBB91_7
	xorl	%eax, %eax
	.p2align	4
.LBB91_6:
	movq	$0, (%r14,%rax)
	addq	$8, %rax
	cmpq	%rax, %r15
	jne	.LBB91_6
.LBB91_7:
	leaq	(%r14,%r15), %r13
	movq	8(%rsp), %rdi
	movq	%r13, %rsi
	movq	%rbp, %rdx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm4wireNtB2_6Reader5words
	testb	%al, %al
	je	.LBB91_20
	addq	$512, %r14
	cmpq	$0, (%r13)
	movzbl	%bl, %ebx
	movl	$0, %eax
	cmovnel	%eax, %ebx
	cmpq	%r12, %r14
	jne	.LBB91_4
	jmp	.LBB91_21
.LBB91_9:
	movq	(%rsp), %rax
	leaq	(,%rax,8), %rcx
	movq	%rcx, 16(%rsp)
	leaq	-8(,%rax,8), %r13
	movq	%r13, %r15
	shrl	$3, %r13d
	incl	%r13d
	andl	$7, %r13d
	movl	%r13d, %ebp
	shll	$3, %ebp
	.p2align	4
.LBB91_10:
	movq	16(%rsp), %rax
	leaq	(%r14,%rax), %rsi
	cmpq	$0, (%rsp)
	je	.LBB91_17
	movq	%r14, %rax
	testq	%r13, %r13
	je	.LBB91_15
	xorl	%eax, %eax
	.p2align	4
.LBB91_13:
	movq	$0, (%r14,%rax)
	addq	$8, %rax
	cmpq	%rax, %rbp
	jne	.LBB91_13
	addq	%r14, %rax
.LBB91_15:
	cmpq	$56, %r15
	jb	.LBB91_17
	.p2align	4
.LBB91_16:
	movq	$0, (%rax)
	movq	$0, 8(%rax)
	movq	$0, 16(%rax)
	movq	$0, 24(%rax)
	movq	$0, 32(%rax)
	movq	$0, 40(%rax)
	movq	$0, 48(%rax)
	movq	$0, 56(%rax)
	addq	$64, %rax
	cmpq	%rsi, %rax
	jne	.LBB91_16
.LBB91_17:
	movq	8(%rsp), %rdi
	xorl	%edx, %edx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm4wireNtB2_6Reader5words
	testb	%al, %al
	je	.LBB91_21
	addq	$512, %r14
	cmpq	%r12, %r14
	jne	.LBB91_10
	movb	$1, %bl
	jmp	.LBB91_21
.Lfunc_end91:
	.size	_RNvNtCsemcRClSg8DH_9native_vm4wire7rd_rows, .Lfunc_end91-_RNvNtCsemcRClSg8DH_9native_vm4wire7rd_rows
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm5field10bit_length,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm5field10bit_length,@function
_RNvNtCsemcRClSg8DH_9native_vm5field10bit_length:
.Lfunc_begin92:
	.cfi_startproc
	xorl	%eax, %eax
	movq	%rdi, %rcx
	shrq	$32, %rcx
	setne	%al
	cmoveq	%rdi, %rcx
	shll	$5, %eax
	xorl	%edx, %edx
	movq	%rcx, %rsi
	shrq	$16, %rsi
	cmoveq	%rcx, %rsi
	setne	%dl
	shll	$4, %edx
	orl	%eax, %edx
	xorl	%eax, %eax
	movq	%rsi, %rcx
	shrq	$8, %rcx
	setne	%al
	leal	(%rdx,%rax,8), %eax
	cmoveq	%rsi, %rcx
	xorl	%edx, %edx
	movq	%rcx, %rsi
	shrq	$4, %rsi
	setne	%dl
	cmoveq	%rcx, %rsi
	leal	(%rax,%rdx,4), %eax
	xorl	%ecx, %ecx
	movq	%rsi, %rdx
	shrq	$2, %rdx
	setne	%cl
	leal	(%rax,%rcx,2), %ecx
	cmoveq	%rsi, %rdx
	xorl	%eax, %eax
	cmpq	$2, %rdx
	setae	%al
	orq	%rcx, %rax
	cmpq	$1, %rdx
	sbbq	$-1, %rax
	retq
.Lfunc_end92:
	.size	_RNvNtCsemcRClSg8DH_9native_vm5field10bit_length, .Lfunc_end92-_RNvNtCsemcRClSg8DH_9native_vm5field10bit_length
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm5field14index_mle_from,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm5field14index_mle_from,@function
_RNvNtCsemcRClSg8DH_9native_vm5field14index_mle_from:
.Lfunc_begin93:
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
	pushq	%rax
	.cfi_def_cfa_offset 64
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	testq	%rsi, %rsi
	je	.LBB93_1
	movq	%rsi, %rbx
	movq	%rdi, %r14
	shlq	$4, %rbx
	addq	%rdi, %rbx
	movl	$1, %r15d
	movl	$2, %r13d
	xorl	%ebp, %ebp
	xorl	%r12d, %r12d
	.p2align	4
.LBB93_3:
	movq	(%r14), %rdi
	movq	8(%r14), %rsi
	movq	%r13, %rdx
	xorq	$1, %rdx
	movq	%rbp, %rcx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	movq	%rdx, %rcx
	xorq	$1, %rax
	movq	%r15, %rdi
	movq	%r12, %rsi
	movq	%rax, %rdx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	movq	%rax, %r15
	movq	%rdx, %r12
	movq	%r13, %rdi
	movq	%rbp, %rsi
	movq	%r13, %rdx
	movq	%rbp, %rcx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	movq	%rax, %r13
	movq	%rdx, %rbp
	addq	$16, %r14
	cmpq	%rbx, %r14
	jne	.LBB93_3
	jmp	.LBB93_4
.LBB93_1:
	movl	$1, %r15d
	xorl	%r12d, %r12d
.LBB93_4:
	movq	%r15, %rax
	movq	%r12, %rdx
	addq	$8, %rsp
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
.Lfunc_end93:
	.size	_RNvNtCsemcRClSg8DH_9native_vm5field14index_mle_from, .Lfunc_end93-_RNvNtCsemcRClSg8DH_9native_vm5field14index_mle_from
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm5field14padding_weight,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm5field14padding_weight,@function
_RNvNtCsemcRClSg8DH_9native_vm5field14padding_weight:
.Lfunc_begin94:
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
	movq	%rdx, %rbp
	testq	%rsi, %rsi
	movq	%rsi, 8(%rsp)
	je	.LBB94_1
	movq	%rdi, %r13
	shlq	$4, %rsi
	addq	%rdi, %rsi
	movq	%rsi, 16(%rsp)
	movl	$1, %r15d
	xorl	%ecx, %ecx
	xorl	%r12d, %r12d
	movq	%rbp, 24(%rsp)
	.p2align	4
.LBB94_3:
	leaq	1(%rcx), %rax
	movq	%rax, 48(%rsp)
	shrq	%cl, %rbp
	movq	(%r13), %r14
	movq	8(%r13), %rbx
	notl	%ebp
	andl	$1, %ebp
	movq	%rbp, %rdi
	xorl	%esi, %esi
	movq	%r14, %rdx
	movq	%rbx, %rcx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	movq	%rax, 32(%rsp)
	movq	%rdx, 40(%rsp)
	xorq	%rbp, %r14
	movq	%r14, %rdi
	movq	%rbx, %rsi
	movq	%r15, %rdx
	movq	%r12, %rcx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	movq	%rax, %r15
	movq	%rdx, %r12
	movq	24(%rsp), %rbp
	xorq	32(%rsp), %r15
	xorq	40(%rsp), %r12
	addq	$16, %r13
	movq	48(%rsp), %rcx
	cmpq	16(%rsp), %r13
	jne	.LBB94_3
	jmp	.LBB94_4
.LBB94_1:
	movl	$1, %r15d
	xorl	%r12d, %r12d
.LBB94_4:
	movq	8(%rsp), %rcx
	shrq	%cl, %rbp
	notl	%ebp
	andl	$1, %ebp
	movq	%rbp, %rdi
	xorl	%esi, %esi
	movq	%r15, %rdx
	movq	%r12, %rcx
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
	jmp	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
.Lfunc_end94:
	.size	_RNvNtCsemcRClSg8DH_9native_vm5field14padding_weight, .Lfunc_end94-_RNvNtCsemcRClSg8DH_9native_vm5field14padding_weight
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm5field14selector_point,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm5field14selector_point,@function
_RNvNtCsemcRClSg8DH_9native_vm5field14selector_point:
.Lfunc_begin95:
	.cfi_startproc
	testq	%rdx, %rdx
	je	.LBB95_8
	movabsq	$1152921504606846975, %rax
	addq	%rax, %rdx
	andq	%rdx, %rax
	je	.LBB95_2
	incq	%rax
	andq	$-2, %rax
	xorl	%ecx, %ecx
	xorl	%r8d, %r8d
	.p2align	4
.LBB95_4:
	xorl	%r9d, %r9d
	btq	%r8, %rdi
	setb	%r9b
	leal	1(%r8), %r10d
	movzbl	%r10b, %r10d
	xorl	%r11d, %r11d
	btq	%r10, %rdi
	setb	%r11b
	cmpq	$64, %r8
	cmovaeq	%rcx, %r9
	movq	%r9, (%rsi)
	movq	$0, 8(%rsi)
	cmovaeq	%rcx, %r11
	movq	%r11, 16(%rsi)
	movq	$0, 24(%rsi)
	addq	$32, %rsi
	addq	$2, %r8
	cmpq	%rax, %r8
	jne	.LBB95_4
	testb	$1, %dl
	jne	.LBB95_8
	xorl	%eax, %eax
	btq	%r8, %rdi
	setb	%al
	xorl	%edi, %edi
	cmpq	$64, %r8
	cmovbq	%rax, %rdi
	jmp	.LBB95_7
.LBB95_2:
	andl	$1, %edi
.LBB95_7:
	movq	%rdi, (%rsi)
	movq	$0, 8(%rsi)
.LBB95_8:
	retq
.Lfunc_end95:
	.size	_RNvNtCsemcRClSg8DH_9native_vm5field14selector_point, .Lfunc_end95-_RNvNtCsemcRClSg8DH_9native_vm5field14selector_point
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm5field3dot,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm5field3dot,@function
_RNvNtCsemcRClSg8DH_9native_vm5field3dot:
.Lfunc_begin96:
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
	pushq	%rax
	.cfi_def_cfa_offset 64
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	%rsi, %r14
	cmpq	%rsi, %rcx
	cmovbq	%rcx, %r14
	testq	%r14, %r14
	je	.LBB96_1
	movq	%rdx, %rbx
	movq	%rdi, %r15
	shlq	$4, %r14
	xorl	%r13d, %r13d
	xorl	%ebp, %ebp
	xorl	%r12d, %r12d
	.p2align	4
.LBB96_3:
	movq	(%r15,%rbp), %rdi
	movq	8(%r15,%rbp), %rsi
	movq	(%rbx,%rbp), %rdx
	movq	8(%rbx,%rbp), %rcx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	xorq	%rax, %r13
	xorq	%rdx, %r12
	addq	$16, %rbp
	cmpq	%rbp, %r14
	jne	.LBB96_3
	jmp	.LBB96_4
.LBB96_1:
	xorl	%r12d, %r12d
	xorl	%r13d, %r13d
.LBB96_4:
	movq	%r13, %rax
	movq	%r12, %rdx
	addq	$8, %rsp
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
.Lfunc_end96:
	.size	_RNvNtCsemcRClSg8DH_9native_vm5field3dot, .Lfunc_end96-_RNvNtCsemcRClSg8DH_9native_vm5field3dot
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm5field4kinv,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm5field4kinv,@function
_RNvNtCsemcRClSg8DH_9native_vm5field4kinv:
.Lfunc_begin97:
	.cfi_startproc
	pushq	%r15
	.cfi_def_cfa_offset 16
	pushq	%r14
	.cfi_def_cfa_offset 24
	pushq	%rbx
	.cfi_def_cfa_offset 32
	.cfi_offset %rbx, -32
	.cfi_offset %r14, -24
	.cfi_offset %r15, -16
	movq	%rdi, %rbx
	movl	$1, %esi
	callq	_RNvNvNtCsemcRClSg8DH_9native_vm5field4kinv2sq
	movq	%rax, %rdi
	movq	%rbx, %rsi
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field4kmul
	movq	%rax, %rdi
	movl	$1, %esi
	callq	_RNvNvNtCsemcRClSg8DH_9native_vm5field4kinv2sq
	movq	%rax, %rdi
	movq	%rbx, %rsi
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field4kmul
	movq	%rax, %rbx
	movq	%rax, %rdi
	movl	$3, %esi
	callq	_RNvNvNtCsemcRClSg8DH_9native_vm5field4kinv2sq
	movq	%rax, %rdi
	movq	%rbx, %rsi
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field4kmul
	movq	%rax, %r14
	movq	%rax, %rdi
	movl	$6, %esi
	callq	_RNvNvNtCsemcRClSg8DH_9native_vm5field4kinv2sq
	movq	%rax, %rdi
	movq	%r14, %rsi
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field4kmul
	movq	%rax, %r14
	movq	%rax, %rdi
	movl	$12, %esi
	callq	_RNvNvNtCsemcRClSg8DH_9native_vm5field4kinv2sq
	movq	%rax, %rdi
	movq	%r14, %rsi
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field4kmul
	movq	%rax, %r15
	movq	%rax, %rdi
	movl	$24, %esi
	callq	_RNvNvNtCsemcRClSg8DH_9native_vm5field4kinv2sq
	movq	%rax, %rdi
	movq	%r15, %rsi
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field4kmul
	movq	%rax, %rdi
	movl	$12, %esi
	callq	_RNvNvNtCsemcRClSg8DH_9native_vm5field4kinv2sq
	movq	%rax, %rdi
	movq	%r14, %rsi
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field4kmul
	movq	%rax, %rdi
	movl	$3, %esi
	callq	_RNvNvNtCsemcRClSg8DH_9native_vm5field4kinv2sq
	movq	%rax, %rdi
	movq	%rbx, %rsi
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field4kmul
	movq	%rax, %rdi
	movl	$1, %esi
	popq	%rbx
	.cfi_def_cfa_offset 24
	popq	%r14
	.cfi_def_cfa_offset 16
	popq	%r15
	.cfi_def_cfa_offset 8
	jmp	_RNvNvNtCsemcRClSg8DH_9native_vm5field4kinv2sq
.Lfunc_end97:
	.size	_RNvNtCsemcRClSg8DH_9native_vm5field4kinv, .Lfunc_end97-_RNvNtCsemcRClSg8DH_9native_vm5field4kinv
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm5field4kmul,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm5field4kmul,@function
_RNvNtCsemcRClSg8DH_9native_vm5field4kmul:
.Lfunc_begin98:
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
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movabsq	$1229782938247303441, %rdx
	movq	%rdi, %r10
	andq	%rdx, %r10
	movabsq	$2459565876494606882, %rax
	movq	%rdi, %rbx
	andq	%rax, %rbx
	movabsq	$4919131752989213764, %r9
	movq	%rdi, %r11
	andq	%r9, %r11
	movabsq	$-8608480567731124088, %rcx
	movq	%rdi, %r14
	andq	%rcx, %r14
	movq	%rsi, %r8
	andq	%rdx, %r8
	movq	%rsi, %r15
	andq	%rax, %r15
	movq	%rsi, %rax
	andq	%rcx, %rax
	movq	%r8, %rcx
	imulq	%r10, %rcx
	movq	%rax, %rdx
	imulq	%rbx, %rdx
	xorq	%rcx, %rdx
	movq	%rsi, %r13
	andq	%r9, %r13
	movq	%r13, %rcx
	imulq	%r11, %rcx
	movq	%r15, %r12
	imulq	%r14, %r12
	xorq	%rcx, %r12
	xorq	%rdx, %r12
	movq	%r15, %rcx
	imulq	%r10, %rcx
	movq	%r8, %rdx
	imulq	%rbx, %rdx
	xorq	%rcx, %rdx
	movq	%rax, %r9
	imulq	%r11, %r9
	movq	%r13, %rcx
	imulq	%r14, %rcx
	xorq	%r9, %rcx
	xorq	%rdx, %rcx
	movq	%r13, %rdx
	imulq	%r10, %rdx
	movq	%r15, %r9
	imulq	%rbx, %r9
	xorq	%rdx, %r9
	movq	%r8, %rbp
	imulq	%r11, %rbp
	movq	%rax, %rdx
	imulq	%r14, %rdx
	xorq	%rbp, %rdx
	xorq	%r9, %rdx
	imulq	%r10, %rax
	imulq	%rbx, %r13
	xorq	%rax, %r13
	imulq	%r11, %r15
	movq	%r8, %r10
	imulq	%r14, %r10
	xorq	%r15, %r10
	xorq	%r13, %r10
	movabsq	$1229782938247303441, %r8
	andq	%r8, %r12
	movabsq	$2459565876494606882, %r13
	andq	%r13, %rcx
	orq	%r12, %rcx
	movabsq	$4919131752989213764, %rbp
	andq	%rbp, %rdx
	orq	%rcx, %rdx
	movabsq	$-8608480567731124088, %rbx
	andq	%rbx, %r10
	orq	%rdx, %r10
	bswapq	%rdi
	movq	%rdi, %rax
	shrq	$4, %rax
	movabsq	$1085102592571150095, %r11
	andq	%r11, %rax
	andq	%r11, %rdi
	shlq	$4, %rdi
	orq	%rax, %rdi
	movabsq	$3689348814741910323, %rdx
	movq	%rdi, %rax
	andq	%rdx, %rax
	shrq	$2, %rdi
	andq	%rdx, %rdi
	leaq	(%rdi,%rax,4), %rax
	movabsq	$6148914691236517205, %rdi
	movq	%rax, %rcx
	andq	%rdi, %rcx
	shrq	%rax
	andq	%rdi, %rax
	bswapq	%rsi
	leaq	(%rax,%rcx,2), %r15
	movq	%rsi, %rax
	shrq	$4, %rax
	andq	%r11, %rax
	andq	%r11, %rsi
	shlq	$4, %rsi
	orq	%rax, %rsi
	movq	%rsi, %rax
	andq	%rdx, %rax
	shrq	$2, %rsi
	andq	%rdx, %rsi
	leaq	(%rsi,%rax,4), %rax
	movq	%rax, %rcx
	andq	%rdi, %rcx
	shrq	%rax
	andq	%rdi, %rax
	leaq	(%rax,%rcx,2), %rcx
	movq	%r15, %r9
	andq	%r8, %r9
	movq	%r15, %r12
	andq	%r13, %r12
	movq	%rcx, %rsi
	andq	%r8, %rsi
	movq	%rcx, %r8
	movq	%rcx, %rdx
	movq	%rbx, %rdi
	andq	%rbx, %rcx
	movq	%rsi, %rbx
	imulq	%r9, %rbx
	movq	%rcx, %r14
	imulq	%r12, %r14
	xorq	%rbx, %r14
	movq	%r15, %rbx
	andq	%rbp, %rbx
	andq	%rdi, %r15
	andq	%r13, %r8
	andq	%rbp, %rdx
	movq	%rdx, %r13
	imulq	%rbx, %r13
	movq	%r8, %rbp
	imulq	%r15, %rbp
	xorq	%r13, %rbp
	xorq	%r14, %rbp
	movq	%r8, %r14
	imulq	%r9, %r14
	movq	%rsi, %rax
	imulq	%r12, %rax
	xorq	%r14, %rax
	movq	%rcx, %r14
	imulq	%rbx, %r14
	movq	%rdx, %r13
	imulq	%r15, %r13
	xorq	%r14, %r13
	xorq	%rax, %r13
	movq	%rdx, %rax
	imulq	%r9, %rax
	movq	%r8, %rdi
	imulq	%r12, %rdi
	xorq	%rax, %rdi
	movq	%rsi, %rax
	imulq	%rbx, %rax
	movq	%rcx, %r14
	imulq	%r15, %r14
	xorq	%rax, %r14
	xorq	%rdi, %r14
	imulq	%r9, %rcx
	imulq	%r12, %rdx
	xorq	%rcx, %rdx
	imulq	%rbx, %r8
	imulq	%r15, %rsi
	xorq	%r8, %rsi
	xorq	%rdx, %rsi
	movabsq	$1229782938247303441, %rax
	andq	%rax, %rbp
	movabsq	$2459565876494606882, %rax
	andq	%rax, %r13
	orq	%rbp, %r13
	movabsq	$4919131752989213764, %rax
	andq	%rax, %r14
	orq	%r13, %r14
	movabsq	$-8608480567731124088, %rax
	andq	%rax, %rsi
	orq	%r14, %rsi
	bswapq	%rsi
	movq	%rsi, %rax
	shrq	$4, %rax
	andq	%r11, %rax
	andq	%r11, %rsi
	shlq	$4, %rsi
	orq	%rax, %rsi
	movq	%rsi, %rax
	movabsq	$3689348814741910323, %rcx
	andq	%rcx, %rax
	shrq	$2, %rsi
	andq	%rcx, %rsi
	leaq	(%rsi,%rax,4), %rax
	movq	%rax, %rcx
	movabsq	$6148914691236517205, %rdx
	andq	%rdx, %rcx
	shrq	%rax
	andq	%rdx, %rax
	leaq	(%rax,%rcx,2), %rcx
	movq	%rcx, %rax
	shrq	%rax
	movq	%rcx, %rdx
	shrq	$62, %rdx
	shrq	$61, %rcx
	xorq	%rdx, %rcx
	xorq	%rax, %rcx
	leaq	(%rcx,%rcx), %rdx
	xorq	%r10, %rdx
	leaq	(,%rcx,8), %rsi
	movq	%rcx, %rax
	shlq	$4, %rax
	xorq	%rsi, %rax
	xorq	%rdx, %rax
	xorq	%rcx, %rax
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
.Lfunc_end98:
	.size	_RNvNtCsemcRClSg8DH_9native_vm5field4kmul, .Lfunc_end98-_RNvNtCsemcRClSg8DH_9native_vm5field4kmul
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm5field4kpow,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm5field4kpow,@function
_RNvNtCsemcRClSg8DH_9native_vm5field4kpow:
.Lfunc_begin99:
	.cfi_startproc
	pushq	%r15
	.cfi_def_cfa_offset 16
	pushq	%r14
	.cfi_def_cfa_offset 24
	pushq	%rbx
	.cfi_def_cfa_offset 32
	.cfi_offset %rbx, -32
	.cfi_offset %r14, -24
	.cfi_offset %r15, -16
	testq	%rdi, %rdi
	je	.LBB99_1
	movq	%rdi, %rbx
	movl	$1, %r14d
	movl	$2, %r15d
	jmp	.LBB99_4
	.p2align	4
.LBB99_6:
	movq	%r15, %rdi
	movq	%r15, %rsi
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field4kmul
	movq	%rax, %r15
	shrq	%rbx
	je	.LBB99_2
.LBB99_4:
	testb	$1, %bl
	je	.LBB99_6
	movq	%r14, %rdi
	movq	%r15, %rsi
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field4kmul
	movq	%rax, %r14
	jmp	.LBB99_6
.LBB99_1:
	movl	$1, %r14d
.LBB99_2:
	movq	%r14, %rax
	popq	%rbx
	.cfi_def_cfa_offset 24
	popq	%r14
	.cfi_def_cfa_offset 16
	popq	%r15
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end99:
	.size	_RNvNtCsemcRClSg8DH_9native_vm5field4kpow, .Lfunc_end99-_RNvNtCsemcRClSg8DH_9native_vm5field4kpow
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm5field5sum_e,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm5field5sum_e,@function
_RNvNtCsemcRClSg8DH_9native_vm5field5sum_e:
.Lfunc_begin100:
	.cfi_startproc
	testq	%rsi, %rsi
	je	.LBB100_1
	movl	%esi, %ecx
	andl	$3, %ecx
	cmpq	$4, %rsi
	jae	.LBB100_4
	xorl	%r8d, %r8d
	xorl	%edx, %edx
	xorl	%eax, %eax
	jmp	.LBB100_7
.LBB100_1:
	xorl	%edx, %edx
	xorl	%eax, %eax
	retq
.LBB100_4:
	andl	$28, %esi
	leaq	56(%rdi), %r9
	xorl	%r8d, %r8d
	xorl	%edx, %edx
	xorl	%eax, %eax
	.p2align	4
.LBB100_5:
	xorq	-56(%r9), %rax
	xorq	-48(%r9), %rdx
	xorq	-40(%r9), %rax
	xorq	-32(%r9), %rdx
	xorq	-24(%r9), %rax
	xorq	-16(%r9), %rdx
	xorq	-8(%r9), %rax
	xorq	(%r9), %rdx
	addq	$4, %r8
	addq	$64, %r9
	cmpq	%r8, %rsi
	jne	.LBB100_5
	testq	%rcx, %rcx
	je	.LBB100_9
.LBB100_7:
	shlq	$4, %r8
	leaq	(%r8,%rdi), %rsi
	addq	$8, %rsi
	shll	$4, %ecx
	xorl	%edi, %edi
	.p2align	4
.LBB100_8:
	xorq	-8(%rsi,%rdi), %rax
	xorq	(%rsi,%rdi), %rdx
	addq	$16, %rdi
	cmpq	%rdi, %rcx
	jne	.LBB100_8
.LBB100_9:
	retq
.Lfunc_end100:
	.size	_RNvNtCsemcRClSg8DH_9native_vm5field5sum_e, .Lfunc_end100-_RNvNtCsemcRClSg8DH_9native_vm5field5sum_e
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm5field6powers,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm5field6powers,@function
_RNvNtCsemcRClSg8DH_9native_vm5field6powers:
.Lfunc_begin101:
	.cfi_startproc
	testq	%rcx, %rcx
	je	.LBB101_4
	pushq	%r15
	.cfi_def_cfa_offset 16
	pushq	%r14
	.cfi_def_cfa_offset 24
	pushq	%r12
	.cfi_def_cfa_offset 32
	pushq	%rbx
	.cfi_def_cfa_offset 40
	pushq	%rax
	.cfi_def_cfa_offset 48
	.cfi_offset %rbx, -40
	.cfi_offset %r12, -32
	.cfi_offset %r14, -24
	.cfi_offset %r15, -16
	movq	%rcx, %rbx
	movq	%rdx, %r14
	movq	%rsi, %r15
	movq	%rdi, %r12
	shlq	$4, %rbx
	addq	%rdx, %rbx
	movl	$1, %eax
	xorl	%edx, %edx
	.p2align	4
.LBB101_2:
	movq	%rax, (%r14)
	movq	%rdx, 8(%r14)
	movq	%rax, %rdi
	movq	%rdx, %rsi
	movq	%r12, %rdx
	movq	%r15, %rcx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	addq	$16, %r14
	cmpq	%rbx, %r14
	jne	.LBB101_2
	addq	$8, %rsp
	.cfi_def_cfa_offset 40
	popq	%rbx
	.cfi_def_cfa_offset 32
	popq	%r12
	.cfi_def_cfa_offset 24
	popq	%r14
	.cfi_def_cfa_offset 16
	popq	%r15
	.cfi_def_cfa_offset 8
	.cfi_restore %rbx
	.cfi_restore %r12
	.cfi_restore %r14
	.cfi_restore %r15
.LBB101_4:
	retq
.Lfunc_end101:
	.size	_RNvNtCsemcRClSg8DH_9native_vm5field6powers, .Lfunc_end101-_RNvNtCsemcRClSg8DH_9native_vm5field6powers
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm5field6prod_e,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm5field6prod_e,@function
_RNvNtCsemcRClSg8DH_9native_vm5field6prod_e:
.Lfunc_begin102:
	.cfi_startproc
	pushq	%r15
	.cfi_def_cfa_offset 16
	pushq	%r14
	.cfi_def_cfa_offset 24
	pushq	%rbx
	.cfi_def_cfa_offset 32
	.cfi_offset %rbx, -32
	.cfi_offset %r14, -24
	.cfi_offset %r15, -16
	movq	%rsi, %rbx
	movq	%rdi, %r14
	shlq	$4, %rbx
	movl	$1, %eax
	xorl	%edx, %edx
	xorl	%r15d, %r15d
	.p2align	4
.LBB102_1:
	movq	(%r14,%r15), %r8
	movq	8(%r14,%r15), %rcx
	movq	%rax, %rdi
	movq	%rdx, %rsi
	movq	%r8, %rdx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	addq	$16, %r15
	cmpq	%r15, %rbx
	jne	.LBB102_1
	popq	%rbx
	.cfi_def_cfa_offset 24
	popq	%r14
	.cfi_def_cfa_offset 16
	popq	%r15
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end102:
	.size	_RNvNtCsemcRClSg8DH_9native_vm5field6prod_e, .Lfunc_end102-_RNvNtCsemcRClSg8DH_9native_vm5field6prod_e
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm5field7eq_eval,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm5field7eq_eval,@function
_RNvNtCsemcRClSg8DH_9native_vm5field7eq_eval:
.Lfunc_begin103:
	.cfi_startproc
	pushq	%r15
	.cfi_def_cfa_offset 16
	pushq	%r14
	.cfi_def_cfa_offset 24
	pushq	%r12
	.cfi_def_cfa_offset 32
	pushq	%rbx
	.cfi_def_cfa_offset 40
	pushq	%rax
	.cfi_def_cfa_offset 48
	.cfi_offset %rbx, -40
	.cfi_offset %r12, -32
	.cfi_offset %r14, -24
	.cfi_offset %r15, -16
	movq	%rsi, %r14
	cmpq	%rsi, %rcx
	cmovbq	%rcx, %r14
	testq	%r14, %r14
	je	.LBB103_1
	movq	%rdx, %rbx
	movq	%rdi, %r15
	shlq	$4, %r14
	movl	$1, %eax
	xorl	%edx, %edx
	xorl	%r12d, %r12d
	.p2align	4
.LBB103_3:
	movq	(%r15,%r12), %r8
	xorq	(%rbx,%r12), %r8
	movq	8(%rbx,%r12), %rcx
	xorq	$1, %r8
	xorq	8(%r15,%r12), %rcx
	movq	%rax, %rdi
	movq	%rdx, %rsi
	movq	%r8, %rdx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	addq	$16, %r12
	cmpq	%r12, %r14
	jne	.LBB103_3
	jmp	.LBB103_4
.LBB103_1:
	movl	$1, %eax
	xorl	%edx, %edx
.LBB103_4:
	addq	$8, %rsp
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
.Lfunc_end103:
	.size	_RNvNtCsemcRClSg8DH_9native_vm5field7eq_eval, .Lfunc_end103-_RNvNtCsemcRClSg8DH_9native_vm5field7eq_eval
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm5field9eq_kernel,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm5field9eq_kernel,@function
_RNvNtCsemcRClSg8DH_9native_vm5field9eq_kernel:
.Lfunc_begin104:
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
	movq	%rcx, %r8
	movq	%rdx, %r15
	movq	%rsi, %rcx
	movq	%rdi, (%rsp)
	movl	$1, %eax
	movl	$1, %edx
	shlq	%cl, %rdx
	cmpq	%rdx, %r8
	jae	.LBB104_2
	xorl	%eax, %eax
	jmp	.LBB104_11
.LBB104_2:
	movq	$1, (%r15)
	movq	$0, 8(%r15)
	testq	%rcx, %rcx
	je	.LBB104_11
	movq	%rdx, 8(%rsp)
	shlq	$4, %rcx
	addq	(%rsp), %rcx
	addq	$8, %r15
	movl	$1, %edx
	movq	%r8, 32(%rsp)
	movq	%rcx, 24(%rsp)
	jmp	.LBB104_4
	.p2align	4
.LBB104_9:
	movq	(%rsp), %rax
	addq	$16, %rax
	movq	16(%rsp), %rdx
	addq	%rdx, %rdx
	movq	24(%rsp), %rcx
	movq	%rax, (%rsp)
	cmpq	%rcx, %rax
	movq	32(%rsp), %r8
	je	.LBB104_10
.LBB104_4:
	movq	%r8, %rbp
	subq	%rdx, %rbp
	jb	.LBB104_5
	cmpq	%rdx, %rbp
	cmovaeq	%rdx, %rbp
	movq	%rdx, 16(%rsp)
	cmpq	%rdx, %r8
	je	.LBB104_9
	movq	(%rsp), %rax
	movq	(%rax), %rcx
	movq	%rcx, 48(%rsp)
	movq	8(%rax), %rax
	movq	%rax, 40(%rsp)
	movq	16(%rsp), %r12
	shlq	$4, %r12
	addq	%r15, %r12
	shlq	$4, %rbp
	xorl	%ebx, %ebx
	.p2align	4
.LBB104_8:
	movq	-8(%r15,%rbx), %r13
	movq	(%r15,%rbx), %r14
	movq	%r13, %rdi
	movq	%r14, %rsi
	movq	48(%rsp), %rdx
	movq	40(%rsp), %rcx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	movq	%rax, -8(%r12,%rbx)
	movq	%rdx, (%r12,%rbx)
	xorq	%rax, %r13
	xorq	%rdx, %r14
	movq	%r13, -8(%r15,%rbx)
	movq	%r14, (%r15,%rbx)
	addq	$16, %rbx
	cmpq	%rbx, %rbp
	jne	.LBB104_8
	jmp	.LBB104_9
.LBB104_5:
	movq	8(%rsp), %rdx
	xorl	%eax, %eax
	jmp	.LBB104_11
.LBB104_10:
	movl	$1, %eax
	movq	8(%rsp), %rdx
.LBB104_11:
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
.Lfunc_end104:
	.size	_RNvNtCsemcRClSg8DH_9native_vm5field9eq_kernel, .Lfunc_end104-_RNvNtCsemcRClSg8DH_9native_vm5field9eq_kernel
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm5field9poly_eval,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm5field9poly_eval,@function
_RNvNtCsemcRClSg8DH_9native_vm5field9poly_eval:
.Lfunc_begin105:
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
	pushq	%rax
	.cfi_def_cfa_offset 64
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	%rcx, %rbx
	movq	%rdx, %r14
	movq	%rsi, %r15
	movq	%rdi, %r12
	shlq	$4, %r15
	xorl	%eax, %eax
	xorl	%edx, %edx
	.p2align	4
.LBB105_1:
	movq	-16(%r12,%r15), %r13
	movq	-8(%r12,%r15), %rbp
	movq	%rax, %rdi
	movq	%rdx, %rsi
	movq	%r14, %rdx
	movq	%rbx, %rcx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	xorq	%r13, %rax
	xorq	%rbp, %rdx
	addq	$-16, %r15
	jne	.LBB105_1
	addq	$8, %rsp
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
.Lfunc_end105:
	.size	_RNvNtCsemcRClSg8DH_9native_vm5field9poly_eval, .Lfunc_end105-_RNvNtCsemcRClSg8DH_9native_vm5field9poly_eval
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm5stack10push_claim,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm5stack10push_claim,@function
_RNvNtCsemcRClSg8DH_9native_vm5stack10push_claim:
.Lfunc_begin106:
	.cfi_startproc
	movq	(%rdi), %rax
	cmpq	$159, %rax
	ja	.LBB106_1
	pushq	%r15
	.cfi_def_cfa_offset 16
	pushq	%r14
	.cfi_def_cfa_offset 24
	pushq	%r12
	.cfi_def_cfa_offset 32
	pushq	%rbx
	.cfi_def_cfa_offset 40
	pushq	%rax
	.cfi_def_cfa_offset 48
	.cfi_offset %rbx, -40
	.cfi_offset %r12, -32
	.cfi_offset %r14, -24
	.cfi_offset %r15, -16
	movq	%r9, %rbx
	movq	%r8, %r14
	movq	%rdi, %r15
	imulq	$608, %rax, %r12
	movq	%rsi, 8(%rdi,%r12)
	addq	%r12, %rdi
	addq	$16, %rdi
	movq	$0, 16(%r15,%r12)
	movq	%rdx, %rsi
	movq	%rcx, %rdx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKj24_E6extendB4_
	testb	%al, %al
	je	.LBB106_4
	leaq	(%r15,%r12), %rax
	addq	$8, %rax
	movq	%r14, 592(%rax)
	movq	%rbx, 600(%rax)
	incq	(%r15)
	movb	$1, %al
	jmp	.LBB106_6
.LBB106_1:
	.cfi_def_cfa_offset 8
	.cfi_restore %rbx
	.cfi_restore %r12
	.cfi_restore %r14
	.cfi_restore %r15
	xorl	%eax, %eax
	retq
.LBB106_4:
	.cfi_def_cfa_offset 48
	.cfi_offset %rbx, -40
	.cfi_offset %r12, -32
	.cfi_offset %r14, -24
	.cfi_offset %r15, -16
	xorl	%eax, %eax
.LBB106_6:
	addq	$8, %rsp
	.cfi_def_cfa_offset 40
	popq	%rbx
	.cfi_def_cfa_offset 32
	popq	%r12
	.cfi_def_cfa_offset 24
	popq	%r14
	.cfi_def_cfa_offset 16
	popq	%r15
	.cfi_def_cfa_offset 8
	.cfi_restore %rbx
	.cfi_restore %r12
	.cfi_restore %r14
	.cfi_restore %r15
	retq
.Lfunc_end106:
	.size	_RNvNtCsemcRClSg8DH_9native_vm5stack10push_claim, .Lfunc_end106-_RNvNtCsemcRClSg8DH_9native_vm5stack10push_claim
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm5stack11ring_weight,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm5stack11ring_weight,@function
_RNvNtCsemcRClSg8DH_9native_vm5stack11ring_weight:
.Lfunc_begin107:
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
	subq	$616, %rsp
	.cfi_def_cfa_offset 672
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	$0, 40(%rsp)
	movq	$0, 48(%rsp)
	movq	$0, 56(%rsp)
	movq	$0, 64(%rsp)
	movq	$0, 72(%rsp)
	movq	$0, 80(%rsp)
	movq	$0, 88(%rsp)
	movq	$0, 96(%rsp)
	movq	$0, 104(%rsp)
	movq	$0, 112(%rsp)
	movq	$0, 120(%rsp)
	movq	$0, 128(%rsp)
	movq	$0, 136(%rsp)
	movq	$0, 144(%rsp)
	movq	$0, 152(%rsp)
	movq	$0, 160(%rsp)
	movq	$0, 168(%rsp)
	movq	$0, 176(%rsp)
	movq	$0, 184(%rsp)
	movq	$0, 192(%rsp)
	movq	$0, 200(%rsp)
	movq	$0, 208(%rsp)
	movq	$0, 216(%rsp)
	movq	$0, 224(%rsp)
	movq	$0, 232(%rsp)
	movq	$0, 240(%rsp)
	movq	$0, 248(%rsp)
	movq	$0, 256(%rsp)
	movq	$0, 264(%rsp)
	movq	$0, 272(%rsp)
	movq	$0, 280(%rsp)
	movq	$0, 288(%rsp)
	movq	$0, 296(%rsp)
	movq	$0, 304(%rsp)
	movq	$0, 312(%rsp)
	movq	$0, 320(%rsp)
	movq	$0, 328(%rsp)
	movq	$0, 336(%rsp)
	movq	$0, 344(%rsp)
	movq	$0, 352(%rsp)
	movq	$0, 360(%rsp)
	movq	$0, 368(%rsp)
	movq	$0, 376(%rsp)
	movq	$0, 384(%rsp)
	movq	$0, 392(%rsp)
	movq	$0, 400(%rsp)
	movq	$0, 408(%rsp)
	movq	$0, 416(%rsp)
	movq	$0, 424(%rsp)
	movq	$0, 432(%rsp)
	movq	$0, 440(%rsp)
	movq	$0, 448(%rsp)
	movq	$0, 456(%rsp)
	movq	$0, 464(%rsp)
	movq	$0, 472(%rsp)
	movq	$0, 480(%rsp)
	movq	$0, 488(%rsp)
	movq	$0, 496(%rsp)
	movq	$0, 504(%rsp)
	movq	$0, 512(%rsp)
	movq	$0, 520(%rsp)
	movq	$0, 528(%rsp)
	movq	$0, 536(%rsp)
	movq	$0, 544(%rsp)
	movq	$0, 552(%rsp)
	movq	$0, 560(%rsp)
	movq	$0, 568(%rsp)
	movq	$0, 576(%rsp)
	movq	$0, 584(%rsp)
	movq	$0, 592(%rsp)
	movq	$0, 600(%rsp)
	movq	$0, 608(%rsp)
	testq	%rdx, %rdx
	movq	%rdi, 16(%rsp)
	je	.LBB107_1
	movq	%rcx, %r15
	movq	%rdx, %r12
	movq	%rdx, %rax
	shlq	$4, %rax
	cmpq	$1, %rdx
	jne	.LBB107_14
	xorl	%ecx, %ecx
	jmp	.LBB107_6
.LBB107_1:
	xorl	%r13d, %r13d
	xorl	%ebp, %ebp
	xorl	%eax, %eax
	.p2align	4
.LBB107_2:
	xorq	(%r9,%rax), %rbp
	xorq	8(%r9,%rax), %r13
	xorq	16(%r9,%rax), %rbp
	xorq	24(%r9,%rax), %r13
	xorq	32(%r9,%rax), %rbp
	xorq	40(%r9,%rax), %r13
	xorq	48(%r9,%rax), %rbp
	xorq	56(%r9,%rax), %r13
	addq	$64, %rax
	cmpq	$1024, %rax
	jne	.LBB107_2
	jmp	.LBB107_13
.LBB107_14:
	movl	%r12d, %edx
	andl	$62, %edx
	movl	$24, %edi
	xorl	%ecx, %ecx
	.p2align	4
.LBB107_15:
	movq	-24(%rsi,%rdi), %r11
	movq	-16(%rsi,%rdi), %r10
	movq	%r11, 16(%rsp,%rdi)
	movq	%r10, 24(%rsp,%rdi)
	addq	$2, %rcx
	movq	-8(%rsi,%rdi), %r11
	movq	(%rsi,%rdi), %r10
	movq	%r11, 32(%rsp,%rdi)
	movq	%r10, 40(%rsp,%rdi)
	addq	$32, %rdi
	cmpq	%rcx, %rdx
	jne	.LBB107_15
	testb	$1, %r12b
	je	.LBB107_7
.LBB107_6:
	shlq	$4, %rcx
	movq	(%rsi,%rcx), %rdx
	movq	8(%rsi,%rcx), %rsi
	movq	%rdx, 40(%rsp,%rcx)
	movq	%rsi, 48(%rsp,%rcx)
.LBB107_7:
	leaq	(%rsp,%rax), %rbx
	addq	$40, %rbx
	cmpq	%r12, %r8
	cmovbq	%r8, %r12
	testq	%r8, %r8
	movq	%r9, 8(%rsp)
	je	.LBB107_9
	shlq	$4, %r12
	xorl	%r13d, %r13d
	xorl	%ebp, %ebp
	xorl	%ecx, %ecx
	.p2align	4
.LBB107_17:
	movq	(%r9,%rcx), %rax
	movq	%rcx, 24(%rsp)
	movq	8(%r9,%rcx), %rdx
	xorl	%r14d, %r14d
	.p2align	4
.LBB107_18:
	movq	40(%rsp,%r14), %r8
	xorq	(%r15,%r14), %r8
	movq	8(%r15,%r14), %rcx
	xorq	$1, %r8
	xorq	48(%rsp,%r14), %rcx
	movq	%rax, %rdi
	movq	%rdx, %rsi
	movq	%r8, %rdx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	addq	$16, %r14
	cmpq	%r14, %r12
	jne	.LBB107_18
	movq	%rax, 32(%rsp)
	movq	%rdx, (%rsp)
	leaq	40(%rsp), %r14
	.p2align	4
.LBB107_20:
	movq	(%r14), %rdi
	movq	8(%r14), %rcx
	movq	%rcx, %rsi
	movq	%rdi, %rdx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	movq	%rax, (%r14)
	movq	%rdx, 8(%r14)
	addq	$16, %r14
	cmpq	%rbx, %r14
	jne	.LBB107_20
	movq	24(%rsp), %rcx
	addq	$16, %rcx
	xorq	32(%rsp), %rbp
	xorq	(%rsp), %r13
	cmpq	$1024, %rcx
	movq	8(%rsp), %r9
	jne	.LBB107_17
	jmp	.LBB107_13
.LBB107_9:
	xorl	%r13d, %r13d
	xorl	%ebp, %ebp
	xorl	%r15d, %r15d
	.p2align	4
.LBB107_10:
	movq	(%r9,%r15), %r14
	movq	8(%r9,%r15), %rax
	movq	%rax, (%rsp)
	leaq	40(%rsp), %r12
	.p2align	4
.LBB107_11:
	movq	(%r12), %rdi
	movq	8(%r12), %rcx
	movq	%rcx, %rsi
	movq	%rdi, %rdx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	movq	%rax, (%r12)
	movq	%rdx, 8(%r12)
	addq	$16, %r12
	cmpq	%rbx, %r12
	jne	.LBB107_11
	addq	$16, %r15
	xorq	%r14, %rbp
	xorq	(%rsp), %r13
	cmpq	$1024, %r15
	movq	8(%rsp), %r9
	jne	.LBB107_10
.LBB107_13:
	movq	16(%rsp), %rax
	movq	%rbp, 8(%rax)
	movq	%r13, 16(%rax)
	movq	$1, (%rax)
	addq	$616, %rsp
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
.Lfunc_end107:
	.size	_RNvNtCsemcRClSg8DH_9native_vm5stack11ring_weight, .Lfunc_end107-_RNvNtCsemcRClSg8DH_9native_vm5stack11ring_weight
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm5stack12commit_stack,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm5stack12commit_stack,@function
_RNvNtCsemcRClSg8DH_9native_vm5stack12commit_stack:
.Lfunc_begin108:
	.cfi_startproc
	pushq	%r14
	.cfi_def_cfa_offset 16
	pushq	%rbx
	.cfi_def_cfa_offset 24
	subq	$168, %rsp
	.cfi_def_cfa_offset 192
	.cfi_offset %rbx, -24
	.cfi_offset %r14, -16
	movq	%rsi, %r14
	movq	%rdi, %rbx
	leaq	8(%rsp), %rdi
	callq	_RNvNtCsemcRClSg8DH_9native_vm4whir6ladder
	cmpl	$1, 8(%rsp)
	jne	.LBB108_2
	movq	160(%rsp), %rax
	addq	$-7, %rax
	cmpq	$-6, %rax
	jae	.LBB108_3
.LBB108_2:
	xorl	%eax, %eax
	addq	$168, %rsp
	.cfi_def_cfa_offset 24
	popq	%rbx
	.cfi_def_cfa_offset 16
	popq	%r14
	.cfi_def_cfa_offset 8
	retq
.LBB108_3:
	.cfi_def_cfa_offset 192
	movq	16(%rsp), %rcx
	movl	$1, %edx
	shlq	%cl, %rdx
	xorl	%esi, %esi
	subq	%rcx, %r14
	cmovaeq	%r14, %rsi
	addq	24(%rsp), %rsi
	movq	%rbx, %rdi
	addq	$168, %rsp
	.cfi_def_cfa_offset 24
	popq	%rbx
	.cfi_def_cfa_offset 16
	popq	%r14
	.cfi_def_cfa_offset 8
	jmp	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState15read_commitment
.Lfunc_end108:
	.size	_RNvNtCsemcRClSg8DH_9native_vm5stack12commit_stack, .Lfunc_end108-_RNvNtCsemcRClSg8DH_9native_vm5stack12commit_stack
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm5stack13column_weight,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm5stack13column_weight,@function
_RNvNtCsemcRClSg8DH_9native_vm5stack13column_weight:
.Lfunc_begin109:
	.cfi_startproc
	pushq	%r15
	.cfi_def_cfa_offset 16
	pushq	%r14
	.cfi_def_cfa_offset 24
	pushq	%rbx
	.cfi_def_cfa_offset 32
	subq	$1056, %rsp
	.cfi_def_cfa_offset 1088
	.cfi_offset %rbx, -32
	.cfi_offset %r14, -24
	.cfi_offset %r15, -16
	movq	%r9, %rax
	movq	%rdi, %rbx
	movq	1096(%rsp), %r14
	movq	1088(%rsp), %r15
	movl	$40, %edi
	.p2align	4
.LBB109_1:
	movq	$0, -40(%rsp,%rdi)
	movq	$0, -32(%rsp,%rdi)
	movq	$0, -24(%rsp,%rdi)
	movq	$0, -16(%rsp,%rdi)
	movq	$0, -8(%rsp,%rdi)
	movq	$0, (%rsp,%rdi)
	addq	$48, %rdi
	cmpq	$1096, %rdi
	jne	.LBB109_1
	movq	%rsp, %r9
	movq	%rsi, %rdi
	movq	%rdx, %rsi
	movq	%rcx, %rdx
	movq	%r8, %rcx
	movq	%rax, %r8
	callq	_RNvNtCsemcRClSg8DH_9native_vm6layout11stack_point
	cmpq	$1, %rax
	jne	.LBB109_3
	movq	%rsp, %rdi
	movq	%rdx, %rsi
	movq	%r15, %rdx
	movq	%r14, %rcx
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field7eq_eval
	movq	%rax, 8(%rbx)
	movq	%rdx, 16(%rbx)
	movl	$1, %eax
	jmp	.LBB109_5
.LBB109_3:
	xorl	%eax, %eax
.LBB109_5:
	movq	%rax, (%rbx)
	addq	$1056, %rsp
	.cfi_def_cfa_offset 32
	popq	%rbx
	.cfi_def_cfa_offset 24
	popq	%r14
	.cfi_def_cfa_offset 16
	popq	%r15
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end109:
	.size	_RNvNtCsemcRClSg8DH_9native_vm5stack13column_weight, .Lfunc_end109-_RNvNtCsemcRClSg8DH_9native_vm5stack13column_weight
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm5stack17ring_claim_weight,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm5stack17ring_claim_weight,@function
_RNvNtCsemcRClSg8DH_9native_vm5stack17ring_claim_weight:
.Lfunc_begin110:
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
	subq	$40, %rsp
	.cfi_def_cfa_offset 96
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	%r9, 8(%rsp)
	movq	%r8, %r15
	movq	%rcx, %r12
	movq	%rsi, %rcx
	movq	104(%rsp), %rax
	shlq	$4, %rsi
	addq	96(%rsp), %rsi
	cmpq	%rax, %rcx
	movq	%rax, %rbp
	cmovbq	%rcx, %rbp
	movl	$8, %r8d
	cmovbeq	%rsi, %r8
	xorl	%esi, %esi
	subq	%rcx, %rax
	cmovbq	%rsi, %rax
	shrq	%cl, %rdx
	movq	%rdi, %rbx
	cmpq	$64, %rcx
	cmovbq	%rdx, %rsi
	movq	%rax, %rdi
	movq	%r8, %rdx
	movq	%rax, %rcx
	callq	_RINvNtCsemcRClSg8DH_9native_vm5field10eq_eval_fnNCNvNtB4_6layout8eq_above0EB4_
	movq	%rax, %r13
	movq	%rdx, %r14
	leaq	16(%rsp), %rdi
	movq	%r12, %rsi
	movq	%r15, %rdx
	movq	96(%rsp), %rcx
	movq	%rbp, %r8
	movq	8(%rsp), %r9
	callq	_RNvNtCsemcRClSg8DH_9native_vm5stack11ring_weight
	cmpl	$1, 16(%rsp)
	jne	.LBB110_2
	movq	24(%rsp), %rdx
	movq	32(%rsp), %rcx
	movq	%r13, %rdi
	movq	%r14, %rsi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	movq	%rax, 8(%rbx)
	movq	%rdx, 16(%rbx)
	movl	$1, %eax
	jmp	.LBB110_3
.LBB110_2:
	xorl	%eax, %eax
.LBB110_3:
	movq	%rax, (%rbx)
	addq	$40, %rsp
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
.Lfunc_end110:
	.size	_RNvNtCsemcRClSg8DH_9native_vm5stack17ring_claim_weight, .Lfunc_end110-_RNvNtCsemcRClSg8DH_9native_vm5stack17ring_claim_weight
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm5stack8read_ood,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm5stack8read_ood,@function
_RNvNtCsemcRClSg8DH_9native_vm5stack8read_ood:
.Lfunc_begin111:
	.cfi_startproc
	pushq	%r15
	.cfi_def_cfa_offset 16
	pushq	%r14
	.cfi_def_cfa_offset 24
	pushq	%rbx
	.cfi_def_cfa_offset 32
	subq	$32, %rsp
	.cfi_def_cfa_offset 64
	.cfi_offset %rbx, -32
	.cfi_offset %r14, -24
	.cfi_offset %r15, -16
	movq	%rdx, %rbx
	movq	%rsi, %r15
	movq	%rdi, %r14
	movl	$15, %esi
	callq	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState5grind
	movl	%eax, %ecx
	xorl	%eax, %eax
	cmpq	$30, %r15
	ja	.LBB111_5
	testb	%cl, %cl
	je	.LBB111_5
	leaq	8(%rbx), %rsi
	movq	%r15, (%rbx)
	movq	%r14, %rdi
	movq	%r15, %rdx
	callq	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState17sample_challenges
	leaq	8(%rsp), %rdi
	movq	%r14, %rsi
	callq	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState11read_scalar
	cmpl	$1, 8(%rsp)
	jne	.LBB111_4
	movq	16(%rsp), %rax
	movq	24(%rsp), %rcx
	movq	%rax, 488(%rbx)
	movq	%rcx, 496(%rbx)
	movb	$1, %al
	jmp	.LBB111_5
.LBB111_4:
	xorl	%eax, %eax
.LBB111_5:
	addq	$32, %rsp
	.cfi_def_cfa_offset 32
	popq	%rbx
	.cfi_def_cfa_offset 24
	popq	%r14
	.cfi_def_cfa_offset 16
	popq	%r15
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end111:
	.size	_RNvNtCsemcRClSg8DH_9native_vm5stack8read_ood, .Lfunc_end111-_RNvNtCsemcRClSg8DH_9native_vm5stack8read_ood
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm6keccak8keccak_f,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm6keccak8keccak_f,@function
_RNvNtCsemcRClSg8DH_9native_vm6keccak8keccak_f:
.Lfunc_begin112:
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
	subq	$424, %rsp
	.cfi_def_cfa_offset 480
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	%rdi, %rbx
	leaq	232(%rsp), %rdi
	leaq	.Lanon.a75d6d9e6a8990b4224ef13f18552af8.1(%rip), %rsi
	movl	$192, %edx
	callq	*memcpy@GOTPCREL(%rip)
	movq	(%rbx), %rax
	movq	%rax, 32(%rsp)
	movq	8(%rbx), %rax
	movq	%rax, 104(%rsp)
	movq	80(%rbx), %rax
	movq	%rax, 24(%rsp)
	movq	120(%rbx), %r8
	movq	160(%rbx), %rax
	movq	%rax, 88(%rsp)
	movq	48(%rbx), %r15
	movq	88(%rbx), %r11
	movq	128(%rbx), %rsi
	movq	168(%rbx), %rax
	movq	%rax, 64(%rsp)
	movq	56(%rbx), %r14
	movq	96(%rbx), %rbp
	movq	136(%rbx), %r9
	movq	176(%rbx), %rax
	movq	%rax, 80(%rsp)
	movq	64(%rbx), %r13
	movq	104(%rbx), %rdi
	movq	144(%rbx), %r10
	movq	184(%rbx), %rax
	movq	%rax, 72(%rsp)
	movq	72(%rbx), %rax
	movq	%rax, 40(%rsp)
	movq	112(%rbx), %rax
	movq	%rax, (%rsp)
	movq	152(%rbx), %rax
	movq	%rax, 8(%rsp)
	movq	192(%rbx), %rax
	movq	%rax, 16(%rsp)
	movq	40(%rbx), %rax
	movq	%rax, 48(%rsp)
	movq	16(%rbx), %rax
	movq	%rax, 96(%rsp)
	movq	24(%rbx), %r12
	movq	%rbx, 176(%rsp)
	movq	32(%rbx), %rax
	movq	%rax, 112(%rsp)
	movl	$2, %eax
	.p2align	4
.LBB112_1:
	movq	%rsi, 56(%rsp)
	movq	%r11, 168(%rsp)
	movq	%rax, 208(%rsp)
	movq	%r9, %rax
	movq	%r9, 160(%rsp)
	movq	24(%rsp), %r9
	xorq	%r8, %r9
	movq	%rdi, %rdx
	movq	%rdi, 152(%rsp)
	movq	88(%rsp), %rdi
	movq	32(%rsp), %rcx
	xorq	%rcx, %rdi
	xorq	%r9, %rdi
	movq	%r11, %r9
	xorq	%rsi, %r9
	movq	64(%rsp), %rbx
	xorq	104(%rsp), %rbx
	xorq	%r9, %rbx
	movq	%r14, %r11
	movq	%rbp, %r14
	xorq	%rax, %r14
	movq	80(%rsp), %r9
	xorq	96(%rsp), %r9
	xorq	%r14, %r9
	movq	%r13, %rax
	xorq	%rdx, %rax
	movq	%r10, %r14
	xorq	72(%rsp), %r14
	xorq	%rax, %r14
	movq	40(%rsp), %rax
	xorq	(%rsp), %rax
	movq	8(%rsp), %rsi
	xorq	16(%rsp), %rsi
	xorq	%rax, %rsi
	xorq	%r15, %rbx
	movq	%r11, 144(%rsp)
	xorq	%r11, %r9
	xorq	%r12, %r14
	movq	%r14, %rdx
	rolq	%rdx
	xorq	%rbx, %rdx
	movq	%rbx, %rax
	rolq	%rax
	xorq	112(%rsp), %rsi
	xorq	%rsi, %rax
	rolq	%rsi
	xorq	%r9, %rsi
	movq	%r9, %rbx
	rolq	%rbx
	movq	48(%rsp), %r9
	xorq	%r9, %rdi
	xorq	%rdi, %rbx
	rolq	%rdi
	xorq	%r14, %rdi
	movq	%rcx, %r11
	xorq	%rax, %r11
	movq	%r11, %r14
	xorq	%rax, %r9
	movq	%r9, 48(%rsp)
	xorq	%rax, 24(%rsp)
	xorq	%rax, %r8
	xorq	88(%rsp), %rax
	movq	%rax, 200(%rsp)
	movq	%rbx, %r9
	movq	104(%rsp), %rcx
	xorq	%rbx, %rcx
	xorq	%rbx, %r15
	xorq	%rbx, 168(%rsp)
	xorq	%rbx, 56(%rsp)
	xorq	64(%rsp), %r9
	movq	%r8, %r11
	movq	96(%rsp), %r8
	xorq	%rdx, %r8
	xorq	%rdx, 144(%rsp)
	xorq	%rdx, %rbp
	xorq	%rdx, 160(%rsp)
	xorq	80(%rsp), %rdx
	movq	%rdx, 192(%rsp)
	xorq	%rsi, %r12
	xorq	%rsi, %r13
	xorq	%rsi, 152(%rsp)
	xorq	%rsi, %r10
	xorq	72(%rsp), %rsi
	movq	%rsi, 128(%rsp)
	movq	112(%rsp), %rax
	xorq	%rdi, %rax
	xorq	%rdi, 40(%rsp)
	movq	(%rsp), %rbx
	xorq	%rdi, %rbx
	xorq	%rdi, 8(%rsp)
	xorq	16(%rsp), %rdi
	movq	%rdi, %rdx
	movq	%rcx, (%rsp)
	movq	%r8, %rdi
	rolq	$62, %rdi
	rolq	$28, %r12
	rolq	$44, %r15
	rolq	$43, %rbp
	rolq	$21, %r10
	movq	%rax, 120(%rsp)
	rolq	$14, %rdx
	movq	%r15, %rax
	notq	%rax
	andq	%rbp, %rax
	movq	%rax, 32(%rsp)
	movq	%r10, %rax
	notq	%rax
	andq	%rdx, %rax
	xorq	%rbp, %rax
	movq	%rax, 96(%rsp)
	notq	%rbp
	andq	%r10, %rbp
	xorq	%r15, %rbp
	movq	%rbp, 104(%rsp)
	movq	%r14, 136(%rsp)
	notq	%r14
	andq	%r15, %r14
	rolq	$55, %r13
	rolq	$39, %rbx
	movq	%r11, %r8
	rolq	$41, %r8
	rolq	$2, %r9
	movq	%r13, %r15
	notq	%r15
	andq	%rbx, %r15
	xorq	%rdi, %r15
	movq	%r15, 88(%rsp)
	movq	%r8, %r15
	notq	%r15
	movq	%r9, 184(%rsp)
	andq	%r9, %r15
	xorq	%rbx, %r15
	movq	%r15, 80(%rsp)
	notq	%rbx
	andq	%r8, %rbx
	xorq	%r13, %rbx
	movq	%rbx, 64(%rsp)
	movq	%r9, %rbp
	notq	%rbp
	andq	%rdi, %rbp
	notq	%rdi
	andq	%r13, %rdi
	movq	%rdi, 16(%rsp)
	movq	48(%rsp), %rsi
	movq	40(%rsp), %r9
	rolq	$20, %r9
	movq	24(%rsp), %rcx
	rolq	$3, %rcx
	movq	56(%rsp), %rbx
	rolq	$45, %rbx
	movq	192(%rsp), %r11
	rolq	$61, %r11
	movq	%r9, %rax
	notq	%rax
	andq	%rcx, %rax
	xorq	%r12, %rax
	movq	%rax, 48(%rsp)
	movq	%rcx, %r15
	movq	%rcx, %rdi
	notq	%r15
	andq	%rbx, %r15
	xorq	%r9, %r15
	movq	%r11, %r13
	notq	%r13
	andq	%r12, %r13
	notq	%r12
	andq	%r12, %r9
	movq	%rdx, %r12
	notq	%r12
	andq	136(%rsp), %r12
	xorq	%r10, %r12
	xorq	%rdx, %r14
	movq	%r14, 112(%rsp)
	movq	144(%rsp), %rcx
	movq	%rbx, %r14
	notq	%r14
	andq	%r11, %r14
	xorq	%rdi, %r14
	xorq	%rbx, %r13
	xorq	%r11, %r9
	movq	%r9, 40(%rsp)
	xorq	%r8, %rbp
	movq	%rbp, 72(%rsp)
	movq	120(%rsp), %rdx
	rolq	$27, %rdx
	movq	%rdx, 120(%rsp)
	rolq	$36, %rsi
	movq	%rsi, 56(%rsp)
	movq	168(%rsp), %rax
	rolq	$10, %rax
	movq	160(%rsp), %r9
	rolq	$15, %r9
	movq	128(%rsp), %rdi
	rolq	$56, %rdi
	movq	%rdi, 128(%rsp)
	movq	%rsi, %r8
	notq	%r8
	andq	%rax, %r8
	movq	%rax, %rsi
	notq	%rsi
	andq	%r9, %rsi
	movq	%rdi, %r10
	notq	%r10
	andq	%rdx, %r10
	xorq	%r9, %r10
	notq	%r9
	andq	%rdi, %r9
	xorq	%rax, %r9
	rolq	(%rsp)
	rolq	$6, %rcx
	movq	152(%rsp), %rdi
	rolq	$25, %rdi
	movq	8(%rsp), %rax
	rolq	$8, %rax
	movq	%rax, 8(%rsp)
	movq	200(%rsp), %rbx
	rolq	$18, %rbx
	movq	%rcx, %rdx
	notq	%rdx
	andq	%rdi, %rdx
	movq	%rax, %rbp
	notq	%rbp
	andq	%rbx, %rbp
	xorq	%rdi, %rbp
	movq	%rdi, %r11
	notq	%r11
	andq	%rax, %r11
	movq	%rbx, %rdi
	notq	%rdi
	movq	(%rsp), %rax
	andq	%rax, %rdi
	xorq	8(%rsp), %rdi
	xorq	%rax, %rdx
	movq	%rdx, 24(%rsp)
	xorq	%rcx, %r11
	notq	%rax
	andq	%rcx, %rax
	xorq	%rbx, %rax
	movq	%rax, (%rsp)
	movq	120(%rsp), %rax
	xorq	%rax, %r8
	movq	56(%rsp), %rcx
	xorq	%rcx, %rsi
	notq	%rax
	andq	%rcx, %rax
	xorq	128(%rsp), %rax
	movq	%rax, 8(%rsp)
	movq	208(%rsp), %rax
	movq	32(%rsp), %rcx
	xorq	216(%rsp,%rax,8), %rcx
	movq	16(%rsp), %rdx
	xorq	184(%rsp), %rdx
	movq	%rdx, 16(%rsp)
	xorq	136(%rsp), %rcx
	movq	%rcx, 32(%rsp)
	incq	%rax
	cmpq	$26, %rax
	jne	.LBB112_1
	movq	176(%rsp), %rax
	movq	%r13, 64(%rax)
	movq	40(%rsp), %rdx
	movq	%rdx, 72(%rax)
	movq	24(%rsp), %rcx
	movq	%rcx, 80(%rax)
	movq	%r11, 88(%rax)
	movq	%rbp, 96(%rax)
	movq	%rdi, 104(%rax)
	movq	(%rsp), %rdx
	movq	%rdx, 112(%rax)
	movq	%r8, 120(%rax)
	movq	%rsi, 128(%rax)
	movq	%r9, 136(%rax)
	movq	%r10, 144(%rax)
	movq	8(%rsp), %rcx
	movq	%rcx, 152(%rax)
	movq	88(%rsp), %rcx
	movq	%rcx, 160(%rax)
	movq	64(%rsp), %rcx
	movq	%rcx, 168(%rax)
	movq	80(%rsp), %rcx
	movq	%rcx, 176(%rax)
	movq	72(%rsp), %rcx
	movq	%rcx, 184(%rax)
	movq	16(%rsp), %rcx
	movq	%rcx, 192(%rax)
	movq	104(%rsp), %rcx
	movq	%rcx, 8(%rax)
	movq	96(%rsp), %rcx
	movq	%rcx, 16(%rax)
	movq	%r12, 24(%rax)
	movq	112(%rsp), %rcx
	movq	%rcx, 32(%rax)
	movq	48(%rsp), %rcx
	movq	%rcx, 40(%rax)
	movq	%r15, 48(%rax)
	movq	%r14, 56(%rax)
	movq	32(%rsp), %rcx
	movq	%rcx, (%rax)
	addq	$424, %rsp
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
.Lfunc_end112:
	.size	_RNvNtCsemcRClSg8DH_9native_vm6keccak8keccak_f, .Lfunc_end112-_RNvNtCsemcRClSg8DH_9native_vm6keccak8keccak_f
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm6keccak9hash_pair,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm6keccak9hash_pair,@function
_RNvNtCsemcRClSg8DH_9native_vm6keccak9hash_pair:
.Lfunc_begin113:
	.cfi_startproc
	subq	$72, %rsp
	.cfi_def_cfa_offset 80
	movq	(%rsi), %rax
	movq	8(%rsi), %rcx
	movq	16(%rsi), %r8
	movq	24(%rsi), %rsi
	movq	(%rdx), %r9
	movq	8(%rdx), %r10
	movq	16(%rdx), %r11
	movq	24(%rdx), %rdx
	movq	%rax, 8(%rsp)
	movq	%rcx, 16(%rsp)
	movq	%r8, 24(%rsp)
	movq	%rsi, 32(%rsp)
	movq	%r9, 40(%rsp)
	movq	%r10, 48(%rsp)
	movq	%r11, 56(%rsp)
	movq	%rdx, 64(%rsp)
	leaq	8(%rsp), %rcx
	movl	$8, %esi
	movl	$64, %edx
	movl	$8, %r8d
	callq	_RINvNtCsemcRClSg8DH_9native_vm6keccak15keccak256_wordsNCNvB2_10hash_words0EB4_
	addq	$72, %rsp
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end113:
	.size	_RNvNtCsemcRClSg8DH_9native_vm6keccak9hash_pair, .Lfunc_end113-_RNvNtCsemcRClSg8DH_9native_vm6keccak9hash_pair
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm6layout10form_terms,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm6layout10form_terms,@function
_RNvNtCsemcRClSg8DH_9native_vm6layout10form_terms:
.Lfunc_begin114:
	.cfi_startproc
	cmpq	$592, %rdi
	ja	.LBB114_1
	shlq	$4, %rdi
	leaq	.Lanon.a75d6d9e6a8990b4224ef13f18552af8.13(%rip), %rax
	movq	(%rdi,%rax), %rcx
	movq	8(%rdi,%rax), %rax
	leaq	(%rax,%rcx), %rdx
	cmpq	%rcx, %rdx
	setae	%sil
	cmpq	$770, %rdx
	setb	%dil
	leaq	(%rcx,%rcx,4), %rcx
	xorl	%edx, %edx
	testb	%dil, %sil
	leaq	.Lanon.a75d6d9e6a8990b4224ef13f18552af8.14(%rip), %rsi
	cmovneq	%rax, %rdx
	leaq	(%rsi,%rcx,8), %rcx
	movl	$8, %eax
	cmovneq	%rcx, %rax
	retq
.LBB114_1:
	movl	$8, %eax
	xorl	%edx, %edx
	retq
.Lfunc_end114:
	.size	_RNvNtCsemcRClSg8DH_9native_vm6layout10form_terms, .Lfunc_end114-_RNvNtCsemcRClSg8DH_9native_vm6layout10form_terms
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm6layout11stack_point,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm6layout11stack_point,@function
_RNvNtCsemcRClSg8DH_9native_vm6layout11stack_point:
.Lfunc_begin115:
	.cfi_startproc
	pushq	%r15
	.cfi_def_cfa_offset 16
	pushq	%r14
	.cfi_def_cfa_offset 24
	pushq	%r12
	.cfi_def_cfa_offset 32
	pushq	%rbx
	.cfi_def_cfa_offset 40
	pushq	%rax
	.cfi_def_cfa_offset 48
	.cfi_offset %rbx, -40
	.cfi_offset %r12, -32
	.cfi_offset %r14, -24
	.cfi_offset %r15, -16
	xorl	%eax, %eax
	subq	%rdi, %r8
	cmovbq	%rax, %r8
	leaq	(%r8,%rcx), %rbx
	cmpq	%rcx, %rbx
	setb	%r10b
	cmpq	$67, %rbx
	setae	%r11b
	orb	%r10b, %r11b
	jne	.LBB115_9
	movq	%rcx, %rax
	shlq	$4, %rax
	addq	%r9, %rax
	testq	%rcx, %rcx
	je	.LBB115_8
	cmpq	$1, %rcx
	jne	.LBB115_4
	xorl	%r10d, %r10d
	jmp	.LBB115_7
.LBB115_4:
	movl	%ecx, %r11d
	andl	$62, %r11d
	movl	$24, %r14d
	xorl	%r10d, %r10d
	.p2align	4
.LBB115_5:
	movq	-24(%rdx,%r14), %r15
	movq	-16(%rdx,%r14), %r12
	movq	%r15, -24(%r9,%r14)
	movq	%r12, -16(%r9,%r14)
	addq	$2, %r10
	movq	-8(%rdx,%r14), %r15
	movq	(%rdx,%r14), %r12
	movq	%r15, -8(%r9,%r14)
	movq	%r12, (%r9,%r14)
	addq	$32, %r14
	cmpq	%r10, %r11
	jne	.LBB115_5
	testb	$1, %cl
	je	.LBB115_8
.LBB115_7:
	shlq	$4, %r10
	movq	(%rdx,%r10), %rcx
	movq	8(%rdx,%r10), %rdx
	movq	%rcx, (%r9,%r10)
	movq	%rdx, 8(%r9,%r10)
.LBB115_8:
	movl	%edi, %ecx
	shrq	%cl, %rsi
	xorl	%ecx, %ecx
	cmpq	$64, %rdi
	cmovbq	%rsi, %rcx
	movq	%rcx, %rdi
	movq	%rax, %rsi
	movq	%r8, %rdx
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field14selector_point
	movl	$1, %eax
.LBB115_9:
	movq	%rbx, %rdx
	addq	$8, %rsp
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
.Lfunc_end115:
	.size	_RNvNtCsemcRClSg8DH_9native_vm6layout11stack_point, .Lfunc_end115-_RNvNtCsemcRClSg8DH_9native_vm6layout11stack_point
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm6layout12build_layout,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm6layout12build_layout,@function
_RNvNtCsemcRClSg8DH_9native_vm6layout12build_layout:
.Lfunc_begin116:
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
	subq	$1304, %rsp
	.cfi_def_cfa_offset 1360
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	%rdx, %r14
	leaq	-1(%rdi), %rax
	movq	%rdi, %rdx
	xorq	%rax, %rdx
	cmpq	%rax, %rdx
	jbe	.LBB116_17
	movq	%rsi, %rbx
	movq	%rcx, %r13
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field10bit_length
	addq	$-5, %rax
	cmpq	$-4, %rax
	setae	%cl
	leaq	-1(%rbx), %rdx
	cmpq	$30, %rdx
	setae	%dl
	orb	%cl, %dl
	jne	.LBB116_17
	movq	(%r14), %r12
	cmpq	$1073741824, %r12
	ja	.LBB116_17
	movq	8(%r14), %rbp
	cmpq	$1073741824, %rbp
	ja	.LBB116_17
	movq	16(%r14), %r15
	cmpq	$1073741824, %r15
	ja	.LBB116_17
	movq	24(%r14), %r8
	cmpq	$1073741824, %r8
	ja	.LBB116_17
	movq	32(%r14), %rdi
	cmpq	$1073741824, %rdi
	ja	.LBB116_17
	movq	40(%r14), %rsi
	cmpq	$1073741825, %rsi
	setae	%cl
	cmpl	$31, %eax
	setae	%dl
	orb	%cl, %dl
	jne	.LBB116_17
	movq	%rbx, (%r13)
	movq	%rax, 8(%r13)
	xorl	%ecx, %ecx
	movq	%rsi, 24(%rsp)
	movq	%rdi, 16(%rsp)
	movq	%r12, %rdi
	subq	$1, %rdi
	cmovbq	%rcx, %rdi
	movq	%rax, 32(%rsp)
	movq	%r8, 8(%rsp)
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field10bit_length
	movq	%rax, 24(%r13)
	movq	%r12, 72(%r13)
	movq	%rbp, %rdi
	subq	$1, %rdi
	movl	$0, %eax
	cmovbq	%rax, %rdi
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field10bit_length
	movq	%rax, 32(%r13)
	movq	%rbp, 80(%r13)
	movq	%r15, %rdi
	subq	$1, %rdi
	movl	$0, %r12d
	cmovbq	%r12, %rdi
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field10bit_length
	movq	%rax, 40(%r13)
	movq	%r15, 88(%r13)
	movq	8(%rsp), %r15
	movq	%r15, %rdi
	subq	$1, %rdi
	cmovbq	%r12, %rdi
	xorl	%r12d, %r12d
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field10bit_length
	movq	%rax, 48(%r13)
	movq	%r15, 96(%r13)
	movq	16(%rsp), %r15
	movq	%r15, %rdi
	subq	$1, %rdi
	cmovbq	%r12, %rdi
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field10bit_length
	movq	%rax, 56(%r13)
	movq	%r15, 104(%r13)
	movq	24(%rsp), %r15
	movq	%r15, %rdi
	subq	$1, %rdi
	cmovbq	%r12, %rdi
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field10bit_length
	cmpq	$10, %rax
	movl	$9, %ecx
	cmovaeq	%rax, %rcx
	movq	%rcx, 64(%r13)
	movq	%r15, 112(%r13)
	leaq	40(%rsp), %r12
	movq	%r12, %rdi
	movq	%rbx, %rsi
	movq	32(%rsp), %rdx
	leaq	24(%r13), %rcx
	callq	_RNvNtCsemcRClSg8DH_9native_vm6layout13column_kappas
	leaq	120(%r13), %rsi
	movq	%r12, %rdi
	callq	_RNvNtCsemcRClSg8DH_9native_vm6layout13placements_of
	cmpq	$1, %rax
	jne	.LBB116_18
	movq	%rdx, 16(%r13)
	jmp	.LBB116_18
.LBB116_17:
	xorl	%eax, %eax
.LBB116_18:
	andb	$1, %al
	addq	$1304, %rsp
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
.Lfunc_end116:
	.size	_RNvNtCsemcRClSg8DH_9native_vm6layout12build_layout, .Lfunc_end116-_RNvNtCsemcRClSg8DH_9native_vm6layout12build_layout
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm6layout13column_kappas,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm6layout13column_kappas,@function
_RNvNtCsemcRClSg8DH_9native_vm6layout13column_kappas:
.Lfunc_begin117:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movq	40(%rcx), %rax
	movq	32(%rcx), %r8
	movq	24(%rcx), %r9
	movq	16(%rcx), %r10
	movq	(%rcx), %r11
	movq	8(%rcx), %rcx
	leaq	6(%rax), %rbx
	movq	%rsi, (%rdi)
	movq	%rsi, 8(%rdi)
	movq	%rsi, 16(%rdi)
	movq	%rdx, 24(%rdi)
	movq	%rbx, 32(%rdi)
	movq	%r11, 40(%rdi)
	movq	%r11, 48(%rdi)
	movq	%r11, 56(%rdi)
	movq	%r11, 64(%rdi)
	movq	%r11, 72(%rdi)
	movq	%r11, 80(%rdi)
	movq	%r11, 88(%rdi)
	movq	%r11, 96(%rdi)
	movq	%r11, 104(%rdi)
	movq	%r11, 112(%rdi)
	movq	%r11, 120(%rdi)
	movq	%r11, 128(%rdi)
	movq	%r11, 136(%rdi)
	movq	%rcx, 144(%rdi)
	movq	%rcx, 152(%rdi)
	movq	%rcx, 160(%rdi)
	movq	%rcx, 168(%rdi)
	movq	%rcx, 176(%rdi)
	movq	%rcx, 184(%rdi)
	movq	%rcx, 192(%rdi)
	movq	%rcx, 200(%rdi)
	movq	%rcx, 208(%rdi)
	movq	%rcx, 216(%rdi)
	movq	%rcx, 224(%rdi)
	movq	%rcx, 232(%rdi)
	movq	%rcx, 240(%rdi)
	movq	%r10, 248(%rdi)
	movq	%r10, 256(%rdi)
	movq	%r10, 264(%rdi)
	movq	%r10, 272(%rdi)
	movq	%r10, 280(%rdi)
	movq	%r10, 288(%rdi)
	movq	%r10, 296(%rdi)
	movq	%r9, 304(%rdi)
	movq	%r9, 312(%rdi)
	movq	%r9, 320(%rdi)
	movq	%r9, 328(%rdi)
	movq	%r9, 336(%rdi)
	movq	%r9, 344(%rdi)
	movq	%r9, 352(%rdi)
	movq	%r9, 360(%rdi)
	movq	%r9, 368(%rdi)
	movq	%r9, 376(%rdi)
	movq	%r9, 384(%rdi)
	movq	%r9, 392(%rdi)
	movq	%r9, 400(%rdi)
	movq	%r9, 408(%rdi)
	movq	%r8, 416(%rdi)
	movq	%r8, 424(%rdi)
	movq	%r8, 432(%rdi)
	movq	%r8, 440(%rdi)
	movq	%r8, 448(%rdi)
	movq	%r8, 456(%rdi)
	movq	%r8, 464(%rdi)
	movq	%r8, 472(%rdi)
	movq	%r8, 480(%rdi)
	movq	%r8, 488(%rdi)
	movq	%r8, 496(%rdi)
	movq	%r8, 504(%rdi)
	movq	%r8, 512(%rdi)
	movq	%r8, 520(%rdi)
	movq	%rax, 528(%rdi)
	movq	%rax, 536(%rdi)
	movq	%rax, 544(%rdi)
	movq	%rax, 552(%rdi)
	movq	%rax, 560(%rdi)
	movq	%rax, 568(%rdi)
	movq	%rax, 576(%rdi)
	movq	%rax, 584(%rdi)
	movq	%rax, 592(%rdi)
	movq	%rax, 600(%rdi)
	movq	%rax, 608(%rdi)
	movq	%rax, 616(%rdi)
	movq	%rax, 624(%rdi)
	movq	%rax, 632(%rdi)
	movq	%rax, 640(%rdi)
	movq	%rax, 648(%rdi)
	movq	%rax, 656(%rdi)
	movq	%rax, 664(%rdi)
	movq	%rax, 672(%rdi)
	movq	%rax, 680(%rdi)
	movq	%rax, 688(%rdi)
	movq	%rax, 696(%rdi)
	movq	%rax, 704(%rdi)
	movq	%rax, 712(%rdi)
	movq	%rax, 720(%rdi)
	movq	%rax, 728(%rdi)
	movq	%rax, 736(%rdi)
	movq	%rax, 744(%rdi)
	movq	%rax, 752(%rdi)
	movq	%rax, 760(%rdi)
	movq	%rax, 768(%rdi)
	movq	%rax, 776(%rdi)
	movq	%rax, 784(%rdi)
	movq	%rax, 792(%rdi)
	movq	%rax, 800(%rdi)
	movq	%rax, 808(%rdi)
	movq	%rax, 816(%rdi)
	movq	%rax, 824(%rdi)
	movq	%rax, 832(%rdi)
	movq	%rax, 840(%rdi)
	movq	%rax, 848(%rdi)
	movq	%rax, 856(%rdi)
	movq	%rax, 864(%rdi)
	movq	%rax, 872(%rdi)
	movq	%rax, 880(%rdi)
	movq	%rax, 888(%rdi)
	movq	%rax, 896(%rdi)
	movq	%rax, 904(%rdi)
	movq	%rax, 912(%rdi)
	movq	%rax, 920(%rdi)
	movq	%rax, 928(%rdi)
	movq	%rax, 936(%rdi)
	movq	%rax, 944(%rdi)
	movq	%rax, 952(%rdi)
	movq	%rax, 960(%rdi)
	movq	%rax, 968(%rdi)
	movq	%rax, 976(%rdi)
	movq	%rax, 984(%rdi)
	movq	%rax, 992(%rdi)
	movq	%rax, 1000(%rdi)
	movq	%rax, 1008(%rdi)
	movq	%rax, 1016(%rdi)
	movq	%rax, 1024(%rdi)
	movq	%rax, 1032(%rdi)
	movq	%rax, 1040(%rdi)
	movq	%rax, 1048(%rdi)
	movq	%rax, 1056(%rdi)
	movq	%rax, 1064(%rdi)
	movq	%rax, 1072(%rdi)
	movq	%rax, 1080(%rdi)
	movq	%rax, 1088(%rdi)
	movq	%rax, 1096(%rdi)
	movq	%rax, 1104(%rdi)
	movq	%rax, 1112(%rdi)
	movq	%rax, 1120(%rdi)
	movq	%rax, 1128(%rdi)
	movq	%rax, 1136(%rdi)
	movq	%rax, 1144(%rdi)
	movq	%rax, 1152(%rdi)
	movq	%rax, 1160(%rdi)
	movq	%rax, 1168(%rdi)
	movq	%rax, 1176(%rdi)
	movq	%rax, 1184(%rdi)
	movq	%rax, 1192(%rdi)
	movq	%rax, 1200(%rdi)
	movq	%rax, 1208(%rdi)
	movq	%rax, 1216(%rdi)
	movq	%rax, 1224(%rdi)
	movq	%rax, 1232(%rdi)
	movq	%rax, 1240(%rdi)
	movq	%rax, 1248(%rdi)
	movq	%rax, 1256(%rdi)
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end117:
	.size	_RNvNtCsemcRClSg8DH_9native_vm6layout13column_kappas, .Lfunc_end117-_RNvNtCsemcRClSg8DH_9native_vm6layout13column_kappas
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm6layout13constraints_w,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm6layout13constraints_w,@function
_RNvNtCsemcRClSg8DH_9native_vm6layout13constraints_w:
.Lfunc_begin118:
	.cfi_startproc
	cmpq	$4, %rdi
	jne	.LBB118_1
	pushq	%r15
	.cfi_def_cfa_offset 16
	pushq	%r14
	.cfi_def_cfa_offset 24
	pushq	%r13
	.cfi_def_cfa_offset 32
	pushq	%r12
	.cfi_def_cfa_offset 40
	pushq	%rbx
	.cfi_def_cfa_offset 48
	.cfi_offset %rbx, -48
	.cfi_offset %r12, -40
	.cfi_offset %r13, -32
	.cfi_offset %r14, -24
	.cfi_offset %r15, -16
	movq	%rcx, %rbx
	cmpq	$6, %rdx
	jb	.LBB118_3
	movq	80(%rsi), %r15
	movq	88(%rsi), %r14
	cmpq	$13, %rdx
	jb	.LBB118_5
	movq	192(%rsi), %rdx
	movq	200(%rsi), %rcx
	je	.LBB118_7
	movq	208(%rsi), %r13
	movq	216(%rsi), %r12
	jmp	.LBB118_9
.LBB118_1:
	.cfi_def_cfa_offset 8
	.cfi_restore %rbx
	.cfi_restore %r12
	.cfi_restore %r13
	.cfi_restore %r14
	.cfi_restore %r15
	xorl	%eax, %eax
	retq
.LBB118_3:
	.cfi_def_cfa_offset 48
	.cfi_offset %rbx, -48
	.cfi_offset %r12, -40
	.cfi_offset %r13, -32
	.cfi_offset %r14, -24
	.cfi_offset %r15, -16
	xorl	%edx, %edx
	xorl	%ecx, %ecx
	xorl	%r14d, %r14d
	xorl	%r15d, %r15d
	jmp	.LBB118_7
.LBB118_5:
	xorl	%edx, %edx
	xorl	%ecx, %ecx
.LBB118_7:
	xorl	%r12d, %r12d
	xorl	%r13d, %r13d
.LBB118_9:
	movq	%r15, %rdi
	movq	%r14, %rsi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	xorq	%r13, %rax
	xorq	%r12, %rdx
	movq	%rax, (%rbx)
	movq	%rdx, 8(%rbx)
	xorq	$1, %r13
	movq	%r15, %rdi
	movq	%r14, %rsi
	movq	%r13, %rdx
	movq	%r12, %rcx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	movq	%rax, 16(%rbx)
	movq	%rdx, 24(%rbx)
	movl	$2, %eax
	popq	%rbx
	.cfi_def_cfa_offset 40
	popq	%r12
	.cfi_def_cfa_offset 32
	popq	%r13
	.cfi_def_cfa_offset 24
	popq	%r14
	.cfi_def_cfa_offset 16
	popq	%r15
	.cfi_def_cfa_offset 8
	.cfi_restore %rbx
	.cfi_restore %r12
	.cfi_restore %r13
	.cfi_restore %r14
	.cfi_restore %r15
	retq
.Lfunc_end118:
	.size	_RNvNtCsemcRClSg8DH_9native_vm6layout13constraints_w, .Lfunc_end118-_RNvNtCsemcRClSg8DH_9native_vm6layout13constraints_w
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm6layout13placements_of,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm6layout13placements_of,@function
_RNvNtCsemcRClSg8DH_9native_vm6layout13placements_of:
.Lfunc_begin119:
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
	subq	$968, %rsp
	.cfi_def_cfa_offset 5120
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	%rsi, %rbx
	movq	%rdi, %r14
	leaq	1272(%rsp), %rdi
	movl	$1264, %r15d
	movq	memset@GOTPCREL(%rip), %r12
	movl	$1264, %edx
	xorl	%esi, %esi
	callq	*%r12
	leaq	2536(%rsp), %rdi
	movl	$1264, %edx
	xorl	%esi, %esi
	callq	*%r12
	leaq	.Lanon.a75d6d9e6a8990b4224ef13f18552af8.15(%rip), %rbp
	leaq	.Lanon.a75d6d9e6a8990b4224ef13f18552af8.16(%rip), %r12
	xorl	%r13d, %r13d
	xorl	%eax, %eax
	jmp	.LBB119_2
	.p2align	4
.LBB119_1:
	incq	%rax
	addq	$-8, %r15
	je	.LBB119_6
.LBB119_2:
	cmpb	$-1, (%rax,%rbp)
	jne	.LBB119_1
	cmpb	$1, (%rax,%r12)
	je	.LBB119_1
	cmpq	$158, %r13
	jae	.LBB119_22
	movq	(%r14,%rax,8), %rcx
	movq	%rax, 1272(%rsp,%r13,8)
	movq	%rcx, 2536(%rsp,%r13,8)
	incq	%r13
	jmp	.LBB119_1
.LBB119_6:
	leaq	3800(%rsp), %rdi
	xorl	%r15d, %r15d
	movl	$1264, %edx
	xorl	%esi, %esi
	callq	*memset@GOTPCREL(%rip)
	cmpq	$159, %r13
	jae	.LBB119_25
	leaq	2536(%rsp), %rdi
	leaq	3800(%rsp), %rdx
	movl	$158, %ecx
	movq	%r13, %rsi
	callq	_RNvNtCsemcRClSg8DH_9native_vm6layout13stack_offsets
	cmpq	$1, %rax
	jne	.LBB119_23
	movq	%rdx, (%rsp)
	leaq	8(%rsp), %rdi
	xorl	%r15d, %r15d
	movl	$1264, %edx
	xorl	%esi, %esi
	callq	*memset@GOTPCREL(%rip)
	testq	%r13, %r13
	je	.LBB119_13
	xorl	%r15d, %r15d
	xorl	%eax, %eax
	.p2align	4
.LBB119_10:
	movq	1272(%rsp,%rax,8), %rcx
	cmpq	$158, %rcx
	jae	.LBB119_25
	movq	3800(%rsp,%rax,8), %rdx
	incq	%rax
	movq	%rdx, 8(%rsp,%rcx,8)
	cmpq	%rax, %r13
	jne	.LBB119_10
	movq	40(%rsp), %r15
.LBB119_13:
	addq	$16, %rbx
	xorl	%eax, %eax
	jmp	.LBB119_16
.LBB119_14:
	movq	8(%rsp,%rax,8), %rdx
	movl	$1, %esi
	.p2align	4
.LBB119_15:
	incq	%rax
	movq	%rsi, -16(%rbx)
	movq	%rcx, -8(%rbx)
	movq	%rdx, (%rbx)
	addq	$24, %rbx
	cmpq	$158, %rax
	je	.LBB119_24
.LBB119_16:
	movq	(%r14,%rax,8), %rcx
	movzbl	(%rax,%rbp), %edx
	cmpq	$255, %rdx
	je	.LBB119_19
	cmpq	$64, %rcx
	jae	.LBB119_22
	shlq	%cl, %rdx
	movl	$1, %esi
	addq	%r15, %rdx
	jae	.LBB119_15
	jmp	.LBB119_22
	.p2align	4
.LBB119_19:
	cmpb	$0, (%rax,%r12)
	je	.LBB119_14
	xorl	%esi, %esi
	xorl	%ecx, %ecx
	xorl	%edx, %edx
	jmp	.LBB119_15
.LBB119_22:
	xorl	%r15d, %r15d
	jmp	.LBB119_26
.LBB119_23:
	xorl	%r15d, %r15d
.LBB119_25:
.LBB119_26:
	movq	%r15, %rax
	addq	$5064, %rsp
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
.LBB119_24:
	.cfi_def_cfa_offset 5120
	movq	(%rsp), %rax
	cmpq	$17, %rax
	movl	$16, %edx
	cmovaeq	%rax, %rdx
	movl	$1, %r15d
	jmp	.LBB119_26
.Lfunc_end119:
	.size	_RNvNtCsemcRClSg8DH_9native_vm6layout13placements_of, .Lfunc_end119-_RNvNtCsemcRClSg8DH_9native_vm6layout13placements_of
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm6layout13stack_offsets,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm6layout13stack_offsets,@function
_RNvNtCsemcRClSg8DH_9native_vm6layout13stack_offsets:
.Lfunc_begin120:
	.cfi_startproc
	cmpq	%rsi, %rcx
	jae	.LBB120_3
	xorl	%eax, %eax
	retq
.LBB120_3:
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
	subq	$1272, %rsp
	.cfi_def_cfa_offset 1328
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	%rcx, %rbx
	movq	%rdx, %r14
	movq	%rsi, %r15
	movq	%rdi, %r12
	leaq	8(%rsp), %r13
	movl	$1264, %edx
	movq	%r13, %rdi
	xorl	%esi, %esi
	callq	*memset@GOTPCREL(%rip)
	leaq	(,%r15,8), %rbp
	testq	%r15, %r15
	je	.LBB120_6
	leaq	-8(%rbp), %rcx
	movq	%rcx, %rdx
	shrq	$3, %rdx
	incq	%rdx
	movl	%edx, %eax
	andl	$7, %eax
	cmpq	$56, %rcx
	jae	.LBB120_7
	xorl	%ecx, %ecx
	jmp	.LBB120_10
.LBB120_6:
	leaq	8(%rsp), %rdi
	xorl	%esi, %esi
	movq	%r12, %rdx
	xorl	%ecx, %ecx
	jmp	.LBB120_13
.LBB120_7:
	andq	$-8, %rdx
	leaq	8(%rsp), %r13
	xorl	%ecx, %ecx
	.p2align	4
.LBB120_8:
	movq	%rcx, %rsi
	movq	%rcx, (%r13)
	incq	%rcx
	movq	%rcx, 8(%r13)
	leaq	2(%rsi), %rcx
	movq	%rcx, 16(%r13)
	leaq	3(%rsi), %rcx
	movq	%rcx, 24(%r13)
	leaq	4(%rsi), %rcx
	movq	%rcx, 32(%r13)
	leaq	5(%rsi), %rcx
	movq	%rcx, 40(%r13)
	leaq	6(%rsi), %rcx
	movq	%rcx, 48(%r13)
	leaq	8(%rsi), %rcx
	addq	$7, %rsi
	movq	%rsi, 56(%r13)
	addq	$64, %r13
	cmpq	%rdx, %rcx
	jne	.LBB120_8
	testq	%rax, %rax
	je	.LBB120_12
.LBB120_10:
	xorl	%edx, %edx
	.p2align	4
.LBB120_11:
	leaq	(%rcx,%rdx), %rsi
	movq	%rsi, (%r13,%rdx,8)
	incq	%rdx
	cmpq	%rdx, %rax
	jne	.LBB120_11
.LBB120_12:
	leaq	8(%rsp), %rdi
	movq	%r15, %rsi
	movq	%r12, %rdx
	movq	%r15, %rcx
.LBB120_13:
	callq	_RINvNtCsemcRClSg8DH_9native_vm6layout14insertion_sortNCNvB2_13stack_offsetss_0EB4_
	xorl	%eax, %eax
	xorl	%esi, %esi
	xorl	%edx, %edx
	jmp	.LBB120_14
	.p2align	4
.LBB120_17:
	xorl	%ecx, %ecx
.LBB120_19:
	movl	$1, %edi
	shlq	%cl, %rdi
	addq	$8, %rsi
	addq	%rdi, %rdx
	jb	.LBB120_20
.LBB120_14:
	cmpq	%rsi, %rbp
	je	.LBB120_22
	movq	8(%rsp,%rsi), %rcx
	cmpq	%rbx, %rcx
	jae	.LBB120_20
	movq	%rdx, (%r14,%rcx,8)
	cmpq	%r15, %rcx
	jae	.LBB120_17
	movq	(%r12,%rcx,8), %rcx
	cmpq	$63, %rcx
	jbe	.LBB120_19
.LBB120_20:
	jmp	.LBB120_21
.LBB120_22:
	xorl	%edi, %edi
	subq	$1, %rdx
	cmovaeq	%rdx, %rdi
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field10bit_length
	movq	%rax, %rdx
	movl	$1, %eax
.LBB120_21:
	addq	$1272, %rsp
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
	.cfi_restore %rbx
	.cfi_restore %r12
	.cfi_restore %r13
	.cfi_restore %r14
	.cfi_restore %r15
	.cfi_restore %rbp
	retq
.Lfunc_end120:
	.size	_RNvNtCsemcRClSg8DH_9native_vm6layout13stack_offsets, .Lfunc_end120-_RNvNtCsemcRClSg8DH_9native_vm6layout13stack_offsets
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm6layout20read_announced_sizes,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm6layout20read_announced_sizes,@function
_RNvNtCsemcRClSg8DH_9native_vm6layout20read_announced_sizes:
.Lfunc_begin121:
	.cfi_startproc
	pushq	%r15
	.cfi_def_cfa_offset 16
	pushq	%r14
	.cfi_def_cfa_offset 24
	pushq	%rbx
	.cfi_def_cfa_offset 32
	subq	$176, %rsp
	.cfi_def_cfa_offset 208
	.cfi_offset %rbx, -32
	.cfi_offset %r14, -24
	.cfi_offset %r15, -16
	movq	%rdx, %rbx
	movq	%rsi, %r14
	movq	$0, (%rsp)
	movq	$0, 8(%rsp)
	movq	$0, 16(%rsp)
	movq	$0, 24(%rsp)
	movq	$0, 32(%rsp)
	movq	$0, 40(%rsp)
	movq	$0, 48(%rsp)
	movq	$0, 56(%rsp)
	movq	$0, 64(%rsp)
	movq	$0, 72(%rsp)
	movq	$0, 80(%rsp)
	movq	$0, 88(%rsp)
	movq	$0, 96(%rsp)
	movq	$0, 104(%rsp)
	movq	$0, 112(%rsp)
	movq	$0, 120(%rsp)
	movq	%rsp, %rsi
	movl	$8, %edx
	callq	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState12read_scalars
	movl	%eax, %ecx
	xorl	%eax, %eax
	testb	%cl, %cl
	je	.LBB121_21
	cmpq	$0, 8(%rsp)
	jne	.LBB121_21
	cmpq	$0, 24(%rsp)
	jne	.LBB121_21
	cmpq	$0, 40(%rsp)
	jne	.LBB121_21
	cmpq	$0, 56(%rsp)
	jne	.LBB121_21
	cmpq	$0, 72(%rsp)
	jne	.LBB121_21
	cmpq	$0, 88(%rsp)
	jne	.LBB121_21
	cmpq	$0, 104(%rsp)
	jne	.LBB121_21
	cmpq	$0, 120(%rsp)
	jne	.LBB121_22
	movq	(%rsp), %rsi
	movq	16(%rsp), %rax
	movq	32(%rsp), %rcx
	movq	48(%rsp), %rdx
	movq	64(%rsp), %rdi
	movq	80(%rsp), %r8
	movq	96(%rsp), %r9
	movq	%rax, 128(%rsp)
	movq	%rcx, 136(%rsp)
	movq	%rdx, 144(%rsp)
	movq	%rdi, 152(%rsp)
	movq	%r8, 160(%rsp)
	movq	%r9, 168(%rsp)
	movq	112(%rsp), %r15
	leaq	-1(%r15), %rax
	cmpq	$3, %rax
	ja	.LBB121_13
	leaq	128(%rsp), %rdx
	movq	%r14, %rdi
	movq	%rbx, %rcx
	callq	_RNvNtCsemcRClSg8DH_9native_vm6layout12build_layout
	testb	%al, %al
	je	.LBB121_13
	movq	16(%rbx), %rcx
	addq	$-16, %rcx
	xorl	%eax, %eax
	cmpq	$15, %rcx
	setb	%al
	jmp	.LBB121_22
.LBB121_13:
	xorl	%eax, %eax
	jmp	.LBB121_22
.LBB121_21:
.LBB121_22:
	movq	%r15, %rdx
	addq	$176, %rsp
	.cfi_def_cfa_offset 32
	popq	%rbx
	.cfi_def_cfa_offset 24
	popq	%r14
	.cfi_def_cfa_offset 16
	popq	%r15
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end121:
	.size	_RNvNtCsemcRClSg8DH_9native_vm6layout20read_announced_sizes, .Lfunc_end121-_RNvNtCsemcRClSg8DH_9native_vm6layout20read_announced_sizes
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm6layout8evaluate,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm6layout8evaluate,@function
_RNvNtCsemcRClSg8DH_9native_vm6layout8evaluate:
.Lfunc_begin122:
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
	subq	$40, %rsp
	.cfi_def_cfa_offset 96
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	%rdi, 8(%rsp)
	movq	%rsi, 16(%rsp)
	testq	%rsi, %rsi
	je	.LBB122_1
	movq	%rcx, %r14
	movq	%rdx, %r15
	xorl	%edx, %edx
	xorl	%r12d, %r12d
	xorl	%eax, %eax
	jmp	.LBB122_3
	.p2align	4
.LBB122_9:
	movq	32(%rsp), %rcx
	xorq	%rdx, %rcx
	movq	%rcx, %rdx
	movq	24(%rsp), %rcx
	xorq	%rax, %rcx
	movq	%rcx, %rax
	incq	%r12
	cmpq	16(%rsp), %r12
	je	.LBB122_10
.LBB122_3:
	movq	%rax, 24(%rsp)
	movq	%rdx, 32(%rsp)
	leaq	(%r12,%r12,4), %rcx
	movq	8(%rsp), %rdx
	movq	(%rdx,%rcx,8), %r13
	movq	24(%rdx,%rcx,8), %rax
	movq	%r13, %rsi
	subq	$3, %rsi
	leaq	8(%rdx,%rcx,8), %rbx
	movl	$8, %edi
	cmovaeq	%rdi, %rbx
	movq	32(%rdx,%rcx,8), %rdx
	cmpq	$-2, %rsi
	jb	.LBB122_9
	xorl	%ebp, %ebp
	jmp	.LBB122_5
	.p2align	4
.LBB122_7:
	shlq	$4, %rcx
	movq	(%r15,%rcx), %r8
	movq	8(%r15,%rcx), %rcx
.LBB122_8:
	movq	%rax, %rdi
	movq	%rdx, %rsi
	movq	%r8, %rdx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	incq	%rbp
	cmpq	%rbp, %r13
	je	.LBB122_9
.LBB122_5:
	movq	(%rbx,%rbp,8), %rcx
	cmpq	%r14, %rcx
	jb	.LBB122_7
	xorl	%ecx, %ecx
	xorl	%r8d, %r8d
	jmp	.LBB122_8
.LBB122_1:
	xorl	%edx, %edx
	xorl	%eax, %eax
.LBB122_10:
	addq	$40, %rsp
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
.Lfunc_end122:
	.size	_RNvNtCsemcRClSg8DH_9native_vm6layout8evaluate, .Lfunc_end122-_RNvNtCsemcRClSg8DH_9native_vm6layout8evaluate
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm6tables11table_phase,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm6tables11table_phase,@function
_RNvNtCsemcRClSg8DH_9native_vm6tables11table_phase:
.Lfunc_begin123:
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
	subq	$88, %rsp
	.cfi_def_cfa_offset 144
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	%rcx, %rbx
	movq	%rdx, %r14
	movq	%rsi, %r15
	movq	%rdi, %r12
	movl	$3, %edi
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field10bit_length
	xorl	%ebp, %ebp
	subl	$3, %eax
	cmovbl	%ebp, %eax
	movq	%r12, %rdi
	movl	%eax, %esi
	callq	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState5grind
	testb	%al, %al
	je	.LBB123_2
	movq	%r12, %rdi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW7squeeze
	movq	$0, 8(%rsp)
	movq	$0, 16(%rsp)
	movq	$0, 24(%rsp)
	movq	$0, 32(%rsp)
	leaq	40(%rsp), %r13
	movq	$0, 40(%rsp)
	movq	$0, 48(%rsp)
	movq	$0, 56(%rsp)
	movq	$0, 64(%rsp)
	movq	$0, 72(%rsp)
	movq	$0, 80(%rsp)
	leaq	8(%rsp), %rbp
	movl	$5, %ecx
	movq	%rax, %rdi
	movq	%rdx, %rsi
	movq	%rbp, %rdx
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field6powers
	leaq	107720(%r14), %rdx
	movl	$3, %esi
	movl	$3, %ecx
	movq	%r13, %rdi
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field3dot
	movq	%rdx, %r10
	addq	$24, %r15
	movq	%r12, %rdi
	movq	%r15, %rsi
	movq	%r14, %rdx
	movq	%rbp, %rcx
	movq	%r13, %r8
	movq	%rax, %r9
	pushq	%rbx
	.cfi_adjust_cfa_offset 8
	pushq	%r10
	.cfi_adjust_cfa_offset 8
	callq	_RNvNtCsemcRClSg8DH_9native_vm6tables14table_sumcheck
	addq	$16, %rsp
	.cfi_adjust_cfa_offset -16
	movl	%eax, %ebp
.LBB123_2:
	movl	%ebp, %eax
	addq	$88, %rsp
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
.Lfunc_end123:
	.size	_RNvNtCsemcRClSg8DH_9native_vm6tables11table_phase, .Lfunc_end123-_RNvNtCsemcRClSg8DH_9native_vm6tables11table_phase
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm6tables11table_terms,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm6tables11table_terms,@function
_RNvNtCsemcRClSg8DH_9native_vm6tables11table_terms:
.Lfunc_begin124:
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
	subq	$216, %rsp
	.cfi_def_cfa_offset 272
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	%r9, 40(%rsp)
	movq	%r8, 32(%rsp)
	movq	%rcx, 24(%rsp)
	movq	%rdx, 16(%rsp)
	movq	%rsi, 48(%rsp)
	movq	%rdi, (%rsp)
	movq	296(%rsp), %rax
	movq	%rax, 8(%rsp)
	movl	$11864, %r13d
	addq	280(%rsp), %r13
	movl	$16, %r14d
	leaq	.Lanon.a75d6d9e6a8990b4224ef13f18552af8.4(%rip), %rbp
	xorl	%eax, %eax
	xorl	%r15d, %r15d
	xorl	%ecx, %ecx
	xorl	%edx, %edx
	.p2align	4
.LBB124_1:
	movq	-8(%r14,%rbp), %r12
	cmpq	$93, %r12
	jae	.LBB124_6
	movq	%rdx, 112(%rsp)
	movq	%rcx, 120(%rsp)
	movq	%rax, 128(%rsp)
	movq	8(%rsp), %rax
	leaq	496(%rax), %rsi
	movq	%r12, 488(%rax)
	movq	48(%rsp), %rdi
	movq	%rsi, %rbx
	movq	%r12, %rdx
	callq	_RNvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB5_6TState12read_scalars
	testb	%al, %al
	je	.LBB124_6
	movq	$0, 136(%rsp)
	movq	$0, 144(%rsp)
	movq	$0, 152(%rsp)
	movq	$0, 160(%rsp)
	movq	%r14, 104(%rsp)
	movq	-16(%r14,%rbp), %rdi
	movq	(%r14,%rbp), %r14
	movq	%rbx, %rsi
	movq	%r12, %rdx
	leaq	136(%rsp), %rbp
	movq	%rbp, %rcx
	callq	_RNvNtCsemcRClSg8DH_9native_vm6layout13constraints_w
	movq	%r15, %rdi
	shlq	$4, %rdi
	addq	16(%rsp), %rdi
	cmpq	$3, %r15
	movl	$8, %ecx
	cmovaeq	%rcx, %rdi
	movl	$2, %esi
	movq	%r15, 96(%rsp)
	subq	%r15, %rsi
	movl	$0, %r15d
	cmovbq	%r15, %rsi
	cmpq	%rsi, %r14
	movq	%r14, 88(%rsp)
	cmovbq	%r14, %rsi
	movq	%rbp, %rdx
	movq	%rax, %rcx
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field3dot
	movq	%rax, 72(%rsp)
	movq	%rdx, 80(%rsp)
	movq	-11864(%r13), %rsi
	leaq	-11856(%r13), %rdi
	cmpq	$149, %rsi
	movl	$8, %r14d
	cmovaeq	%r14, %rdi
	cmovaeq	%r15, %rsi
	movq	%rbx, %rdx
	movq	%r12, %rcx
	callq	_RNvNtCsemcRClSg8DH_9native_vm6layout8evaluate
	movq	%rax, 168(%rsp)
	movq	%rdx, 176(%rsp)
	movq	-5936(%r13), %rsi
	leaq	-5928(%r13), %rdi
	cmpq	$149, %rsi
	cmovaeq	%r14, %rdi
	cmovaeq	%r15, %rsi
	movq	%rbx, %rdx
	movq	%r12, %rcx
	callq	_RNvNtCsemcRClSg8DH_9native_vm6layout8evaluate
	movq	%rax, 184(%rsp)
	movq	%rdx, 192(%rsp)
	movq	-8(%r13), %rsi
	cmpq	$149, %rsi
	movl	$8, %edi
	cmovbq	%r13, %rdi
	cmovaeq	%r15, %rsi
	movq	%rbx, %rdx
	movq	%r12, %rcx
	callq	_RNvNtCsemcRClSg8DH_9native_vm6layout8evaluate
	movq	%rax, 200(%rsp)
	movq	%rdx, 208(%rsp)
	movq	288(%rsp), %rax
	movq	128(%rsp), %r12
	movq	(%rax,%r12,2), %rcx
	movq	%rcx, 64(%rsp)
	movq	8(%rax,%r12,2), %rax
	movq	%rax, 56(%rsp)
	movl	$3, %esi
	movl	$3, %ecx
	movq	24(%rsp), %rdi
	leaq	168(%rsp), %rdx
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field3dot
	movq	8(%rsp), %rbx
	movq	104(%rsp), %rbp
	movq	%rax, %r14
	movq	%r13, %r15
	movq	%rdx, %r13
	movq	272(%rsp), %rax
	movq	(%rax,%r12), %rdx
	movq	40(%rsp), %rax
	cmpq	%rax, %rdx
	cmovaeq	%rax, %rdx
	movq	$0, (%rbx)
	movq	%rbx, %rdi
	movq	32(%rsp), %rsi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm3bufINtB2_3BufNtNtB4_5field2EWKj1e_E6extendB4_
	testb	%al, %al
	je	.LBB124_6
	xorq	72(%rsp), %r14
	xorq	80(%rsp), %r13
	movq	64(%rsp), %rdi
	movq	56(%rsp), %rsi
	movq	%r14, %rdx
	movq	%r13, %rcx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	movq	120(%rsp), %rcx
	xorq	%rdx, %rcx
	movq	112(%rsp), %rdx
	xorq	%rax, %rdx
	movq	96(%rsp), %rsi
	addq	88(%rsp), %rsi
	addq	$40, %rbp
	addq	$8, %r12
	addq	$17784, %r15
	addq	$1968, %rbx
	movq	%rbx, 8(%rsp)
	cmpq	$256, %rbp
	movq	%rbp, %r14
	movq	%r15, %r13
	leaq	.Lanon.a75d6d9e6a8990b4224ef13f18552af8.4(%rip), %rbp
	movq	%r12, %rax
	movq	%rsi, %r15
	jne	.LBB124_1
	movq	(%rsp), %rax
	movq	%rdx, 8(%rax)
	movq	%rcx, 16(%rax)
	movq	$1, (%rax)
	jmp	.LBB124_7
.LBB124_6:
	movq	(%rsp), %rax
	movq	$0, (%rax)
.LBB124_7:
	addq	$216, %rsp
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
.Lfunc_end124:
	.size	_RNvNtCsemcRClSg8DH_9native_vm6tables11table_terms, .Lfunc_end124-_RNvNtCsemcRClSg8DH_9native_vm6tables11table_terms
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm6tables13table_weights,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm6tables13table_weights,@function
_RNvNtCsemcRClSg8DH_9native_vm6tables13table_weights:
.Lfunc_begin125:
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
	subq	$200, %rsp
	.cfi_def_cfa_offset 256
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	%rcx, 168(%rsp)
	movq	%rdx, 96(%rsp)
	movq	%rdi, 88(%rsp)
	testq	%r9, %r9
	je	.LBB125_1
	shlq	$4, %r9
	addq	%r8, %r9
	movq	(%rsi), %rax
	movq	%rax, 144(%rsp)
	movq	8(%rsi), %rax
	movq	%rax, 136(%rsp)
	movq	16(%rsi), %rax
	movq	%rax, 128(%rsp)
	movq	24(%rsi), %rax
	movq	%rax, 120(%rsp)
	movq	32(%rsi), %rax
	movq	%rax, 112(%rsp)
	movq	40(%rsi), %rax
	movq	%rax, 104(%rsp)
	movl	$1, %eax
	xorl	%ebp, %ebp
	xorl	%edx, %edx
	movq	$0, 72(%rsp)
	movl	$1, %ecx
	movq	%rcx, 80(%rsp)
	movq	$0, 64(%rsp)
	movq	%rcx, 56(%rsp)
	movq	$0, 48(%rsp)
	movq	%rcx, 40(%rsp)
	movq	$0, 32(%rsp)
	movq	%rcx, 24(%rsp)
	movq	$0, 16(%rsp)
	movq	%rcx, 8(%rsp)
	xorl	%ebx, %ebx
	movq	%r9, 160(%rsp)
	movq	%r8, 152(%rsp)
	jmp	.LBB125_3
	.p2align	4
.LBB125_5:
	leaq	(%r8,%rbp), %rax
	movq	%rax, 176(%rsp)
	movq	(%r8,%rbp), %r12
	cmpq	144(%rsp), %rbx
	movl	$0, %edx
	cmovbq	%r15, %rdx
	movq	%r14, %rcx
	cmovbq	%r13, %rcx
	xorq	%r12, %rdx
	movq	8(%rsp), %rdi
	movq	16(%rsp), %rsi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	movq	%rax, 8(%rsp)
	movq	%rdx, 16(%rsp)
	cmpq	136(%rsp), %rbx
	movl	$0, %edx
	cmovbq	%r15, %rdx
	movq	%r14, %rcx
	cmovbq	%r13, %rcx
	xorq	%r12, %rdx
	movq	24(%rsp), %rdi
	movq	32(%rsp), %rsi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	movq	%rax, 24(%rsp)
	movq	%rdx, 32(%rsp)
	cmpq	128(%rsp), %rbx
	movl	$0, %edx
	cmovbq	%r15, %rdx
	movq	%r14, %rcx
	cmovbq	%r13, %rcx
	xorq	%r12, %rdx
	movq	40(%rsp), %rdi
	movq	48(%rsp), %rsi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	movq	%rax, 40(%rsp)
	movq	%rdx, 48(%rsp)
	cmpq	120(%rsp), %rbx
	movl	$0, %edx
	cmovbq	%r15, %rdx
	movq	%r14, %rcx
	cmovbq	%r13, %rcx
	xorq	%r12, %rdx
	movq	56(%rsp), %rdi
	movq	64(%rsp), %rsi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	movq	%rax, 56(%rsp)
	movq	%rdx, 64(%rsp)
	cmpq	112(%rsp), %rbx
	movl	$0, %edx
	cmovbq	%r15, %rdx
	movq	%r14, %rcx
	cmovbq	%r13, %rcx
	xorq	%r12, %rdx
	movq	80(%rsp), %rdi
	movq	72(%rsp), %rsi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	movq	%rax, 80(%rsp)
	cmpq	104(%rsp), %rbx
	movl	$0, %eax
	cmovaeq	%rax, %r15
	movq	%rdx, 72(%rsp)
	cmovbq	%r13, %r14
	xorq	%r12, %r15
	movq	192(%rsp), %rdi
	movq	184(%rsp), %rsi
	movq	%r15, %rdx
	movq	%r14, %rcx
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5fieldNtB2_2EW3mul
	movq	152(%rsp), %r8
	addq	$16, %rbp
	movq	176(%rsp), %rcx
	addq	$16, %rcx
	incq	%rbx
	movq	160(%rsp), %r9
	cmpq	%r9, %rcx
	je	.LBB125_6
.LBB125_3:
	movq	%rdx, 184(%rsp)
	movq	%rax, 192(%rsp)
	movq	8(%r8,%rbp), %r14
	movl	$1, %r15d
	movq	%r14, %r13
	cmpq	168(%rsp), %rbx
	jae	.LBB125_5
	movq	96(%rsp), %rax
	movq	(%rax,%rbp), %r15
	xorq	$1, %r15
	movq	8(%rax,%rbp), %r13
	xorq	%r14, %r13
	jmp	.LBB125_5
.LBB125_1:
	movl	$1, %eax
	xorl	%edx, %edx
	movq	$0, 72(%rsp)
	movl	$1, %ecx
	movq	%rcx, 80(%rsp)
	movq	$0, 64(%rsp)
	movq	%rcx, 56(%rsp)
	movq	$0, 48(%rsp)
	movq	%rcx, 40(%rsp)
	movq	$0, 32(%rsp)
	movq	%rcx, 24(%rsp)
	movq	$0, 16(%rsp)
	movq	%rcx, 8(%rsp)
.LBB125_6:
	movq	88(%rsp), %rcx
	movq	8(%rsp), %rsi
	movq	%rsi, (%rcx)
	movq	16(%rsp), %rsi
	movq	%rsi, 8(%rcx)
	movq	24(%rsp), %rsi
	movq	%rsi, 16(%rcx)
	movq	32(%rsp), %rsi
	movq	%rsi, 24(%rcx)
	movq	40(%rsp), %rsi
	movq	%rsi, 32(%rcx)
	movq	48(%rsp), %rsi
	movq	%rsi, 40(%rcx)
	movq	56(%rsp), %rsi
	movq	%rsi, 48(%rcx)
	movq	64(%rsp), %rsi
	movq	%rsi, 56(%rcx)
	movq	80(%rsp), %rsi
	movq	%rsi, 64(%rcx)
	movq	72(%rsp), %rsi
	movq	%rsi, 72(%rcx)
	movq	%rax, 80(%rcx)
	movq	%rdx, 88(%rcx)
	addq	$200, %rsp
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
.Lfunc_end125:
	.size	_RNvNtCsemcRClSg8DH_9native_vm6tables13table_weights, .Lfunc_end125-_RNvNtCsemcRClSg8DH_9native_vm6tables13table_weights
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm6tables14table_sumcheck,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm6tables14table_sumcheck,@function
_RNvNtCsemcRClSg8DH_9native_vm6tables14table_sumcheck:
.Lfunc_begin126:
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
	subq	$648, %rsp
	.cfi_def_cfa_offset 704
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	%rcx, %rbp
	movq	%rdx, %r14
	movq	%rsi, %rbx
	movq	%rdi, %r10
	movq	(%rsi), %r13
	movq	8(%rsi), %rdi
	movq	16(%rsi), %rsi
	movq	24(%rbx), %rdx
	movq	32(%rbx), %rcx
	movq	40(%rbx), %rax
	movq	$0, 72(%rsp)
	movq	$0, 80(%rsp)
	movq	$0, 88(%rsp)
	movq	$0, 96(%rsp)
	movq	$0, 104(%rsp)
	movq	$0, 112(%rsp)
	movq	$0, 120(%rsp)
	movq	$0, 128(%rsp)
	movq	$0, 136(%rsp)
	movq	$0, 144(%rsp)
	movq	$0, 152(%rsp)
	movq	$0, 160(%rsp)
	movq	$0, 168(%rsp)
	movq	$0, 176(%rsp)
	movq	$0, 184(%rsp)
	movq	$0, 192(%rsp)
	movq	$0, 200(%rsp)
	movq	$0, 208(%rsp)
	movq	$0, 216(%rsp)
	movq	$0, 224(%rsp)
	movq	$0, 232(%rsp)
	movq	$0, 240(%rsp)
	movq	$0, 248(%rsp)
	movq	$0, 256(%rsp)
	movq	$0, 264(%rsp)
	movq	$0, 272(%rsp)
	movq	$0, 280(%rsp)
	movq	$0, 288(%rsp)
	movq	$0, 296(%rsp)
	movq	$0, 304(%rsp)
	movq	$0, 312(%rsp)
	movq	$0, 320(%rsp)
	movq	$0, 328(%rsp)
	movq	$0, 336(%rsp)
	movq	$0, 344(%rsp)
	movq	$0, 352(%rsp)
	movq	$0, 360(%rsp)
	movq	$0, 368(%rsp)
	movq	$0, 376(%rsp)
	movq	$0, 384(%rsp)
	movq	$0, 392(%rsp)
	movq	$0, 400(%rsp)
	movq	$0, 408(%rsp)
	movq	$0, 416(%rsp)
	movq	$0, 424(%rsp)
	movq	$0, 432(%rsp)
	movq	$0, 440(%rsp)
	movq	$0, 448(%rsp)
	movq	$0, 456(%rsp)
	movq	$0, 464(%rsp)
	movq	$0, 472(%rsp)
	movq	$0, 480(%rsp)
	movq	$0, 488(%rsp)
	movq	$0, 496(%rsp)
	movq	$0, 504(%rsp)
	movq	$0, 512(%rsp)
	movq	$0, 520(%rsp)
	movq	$0, 528(%rsp)
	movq	$0, 536(%rsp)
	movq	$0, 544(%rsp)
	cmpq	%r13, %rdi
	cmovaq	%rdi, %r13
	cmpq	%r13, %rsi
	cmovaq	%rsi, %r13
	cmpq	%r13, %rdx
	cmovaq	%rdx, %r13
	cmpq	%r13, %rcx
	cmovaq	%rcx, %r13
	cmpq	%r13, %rax
	cmovaq	%rax, %r13
	cmpq	$30, %r13
	ja	.LBB126_11
	movq	%r8, %r12
	movq	704(%rsp), %rcx
	subq	$8, %rsp
	.cfi_adjust_cfa_offset 8
	leaq	560(%rsp), %rdi
	leaq	80(%rsp), %r15
	movl	$4, %r8d
	movq	%r10, 48(%rsp)
	movq	%r10, %rsi
	movq	%r9, %rdx
	movq	%r15, %r9
	pushq	%r13
	.cfi_adjust_cfa_offset 8
	callq	_RINvMs0_NtCsemcRClSg8DH_9native_vm10transcriptNtB6_6TState8sumcheckNCNvB2_14sumcheck_plain0EB8_
	addq	$16, %rsp
	.cfi_adjust_cfa_offset -16
	cmpl	$1, 552(%rsp)
	jne	.LBB126_11
	movq	%rbp, 16(%rsp)
	movq	%r12, 24(%rsp)
	movq	%r14, 32(%rsp)
	movq	%r13, %rdx
	shrq	%rdx
	je	.LBB126_9
	movq	%r13, %rcx
	shlq	$4, %rcx
	leaq	(%rsp,%rcx), %rax
	addq	$72, %rax
	cmpq	$1, %rdx
	jne	.LBB126_5
	xorl	%ecx, %ecx
	jmp	.LBB126_8
.LBB126_5:
	andl	$14, %edx
	leaq	(%rcx,%r15), %rsi
	addq	$-16, %rsi
	xorl	%ecx, %ecx
	movabsq	$1152921504606846974, %rdi
	.p2align	4
.LBB126_6:
	movq	(%r15), %r8
	movq	8(%r15), %r9
	movq	(%rsi), %r10
	movq	8(%rsi), %r11
	movq	%r11, 8(%r15)
	movq	%r10, (%r15)
	movq	%r8, (%rsi)
	movq	%r9, 8(%rsi)
	movq	%rcx, %r8
	xorq	%rdi, %r8
	shlq	$4, %r8
	movq	16(%r15), %r9
	movq	24(%r15), %r10
	movq	(%rax,%r8), %r11
	movq	8(%rax,%r8), %r14
	movq	%r14, 24(%r15)
	movq	%r11, 16(%r15)
	movq	%r9, (%rax,%r8)
	movq	%r10, 8(%rax,%r8)
	addq	$2, %rcx
	addq	$32, %r15
	addq	$-32, %rsi
	cmpq	%rcx, %rdx
	jne	.LBB126_6
	testb	$2, %r13b
	je	.LBB126_9
.LBB126_8:
	movq	%rcx, %rdx
	notq	%rdx
	shlq	$4, %rcx
	shlq	$4, %rdx
	movq	72(%rsp,%rcx), %rsi
	movq	80(%rsp,%rcx), %rdi
	movq	(%rax,%rdx), %r8
	movq	8(%rax,%rdx), %r9
	movq	%r9, 80(%rsp,%rcx)
	movq	%r8, 72(%rsp,%rcx)
	movq	%rsi, (%rax,%rdx)
	movq	%rdi, 8(%rax,%rdx)
.LBB126_9:
	movq	560(%rsp), %rax
	movq	%rax, 8(%rsp)
	movq	568(%rsp), %r14
	movq	32(%rsp), %rbp
	movq	106704(%rbp), %rax
	leaq	106712(%rbp), %rsi
	xorl	%ecx, %ecx
	cmpq	$64, %rax
	movl	$8, %edx
	cmovbq	%rsi, %rdx
	cmovbq	%rax, %rcx
	leaq	72(%rsp), %r15
	leaq	552(%rsp), %r12
	movq	%r12, %rdi
	movq	%rbx, %rsi
	movq	%r15, %r8
	movq	%r13, %r9
	callq	_RNvNtCsemcRClSg8DH_9native_vm6tables13table_weights
	leaq	48(%rsp), %rdi
	movq	40(%rsp), %rsi
	movq	16(%rsp), %rdx
	movq	24(%rsp), %rcx
	movq	%r15, %r8
	movq	%r13, %r9
	pushq	712(%rsp)
	.cfi_adjust_cfa_offset 8
	pushq	%r12
	.cfi_adjust_cfa_offset 8
	pushq	%rbp
	.cfi_adjust_cfa_offset 8
	pushq	%rbx
	.cfi_adjust_cfa_offset 8
	callq	_RNvNtCsemcRClSg8DH_9native_vm6tables11table_terms
	addq	$32, %rsp
	.cfi_adjust_cfa_offset -32
	cmpb	$0, 48(%rsp)
	je	.LBB126_11
	movq	8(%rsp), %rax
	xorq	56(%rsp), %rax
	xorq	64(%rsp), %r14
	orq	%rax, %r14
	sete	%al
	jmp	.LBB126_12
.LBB126_11:
	xorl	%eax, %eax
.LBB126_12:
	addq	$648, %rsp
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
.Lfunc_end126:
	.size	_RNvNtCsemcRClSg8DH_9native_vm6tables14table_sumcheck, .Lfunc_end126-_RNvNtCsemcRClSg8DH_9native_vm6tables14table_sumcheck
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm6tables18public_input_phase,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm6tables18public_input_phase,@function
_RNvNtCsemcRClSg8DH_9native_vm6tables18public_input_phase:
.Lfunc_begin127:
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
	subq	$552, %rsp
	.cfi_def_cfa_offset 608
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	%rcx, %rbx
	movq	%rdx, %r14
	movq	%rsi, %r13
	callq	_RNvMNtCsemcRClSg8DH_9native_vm10transcriptNtB2_7SpongeW7squeeze
	movq	%rax, %r15
	movq	%rdx, %r12
	movq	$0, 56(%rsp)
	movq	$0, 64(%rsp)
	movq	$0, 72(%rsp)
	movq	$0, 80(%rsp)
	movq	$0, 88(%rsp)
	movq	$0, 96(%rsp)
	movq	$0, 104(%rsp)
	movq	$0, 112(%rsp)
	movq	$0, 120(%rsp)
	movq	$0, 128(%rsp)
	movq	$0, 136(%rsp)
	movq	$0, 144(%rsp)
	movq	$0, 152(%rsp)
	movq	$0, 160(%rsp)
	movq	$0, 168(%rsp)
	movq	$0, 176(%rsp)
	movq	$0, 184(%rsp)
	movq	$0, 192(%rsp)
	movq	$0, 200(%rsp)
	movq	$0, 208(%rsp)
	movq	$0, 216(%rsp)
	movq	$0, 224(%rsp)
	movq	$0, 232(%rsp)
	movq	$0, 240(%rsp)
	movq	$0, 248(%rsp)
	movq	$0, 256(%rsp)
	movq	$0, 264(%rsp)
	movq	$0, 272(%rsp)
	movq	$0, 280(%rsp)
	movq	$0, 288(%rsp)
	movq	$0, 296(%rsp)
	movq	$0, 304(%rsp)
	movq	$0, 312(%rsp)
	movq	$0, 320(%rsp)
	movq	$0, 328(%rsp)
	movq	$0, 336(%rsp)
	movq	$0, 344(%rsp)
	movq	$0, 352(%rsp)
	movq	$0, 360(%rsp)
	movq	$0, 368(%rsp)
	movq	$0, 376(%rsp)
	movq	$0, 384(%rsp)
	movq	$0, 392(%rsp)
	movq	$0, 400(%rsp)
	movq	$0, 408(%rsp)
	movq	$0, 416(%rsp)
	movq	$0, 424(%rsp)
	movq	$0, 432(%rsp)
	movq	$0, 440(%rsp)
	movq	$0, 448(%rsp)
	movq	$0, 456(%rsp)
	movq	$0, 464(%rsp)
	movq	$0, 472(%rsp)
	movq	$0, 480(%rsp)
	movq	$0, 488(%rsp)
	movq	$0, 496(%rsp)
	movq	$0, 504(%rsp)
	movq	$0, 512(%rsp)
	movq	$0, 520(%rsp)
	movq	$0, 528(%rsp)
	movq	$0, 536(%rsp)
	movq	$0, 544(%rsp)
	xorl	%ebp, %ebp
	movq	%r13, %rdi
	xorl	%esi, %esi
	callq	_RNvMs2_NtCsemcRClSg8DH_9native_vm6layoutNtB5_7LayoutW9placement
	cmpq	$1, %rax
	movq	%rax, %r13
	adcq	$0, %r13
	cmpq	$31, %rax
	ja	.LBB127_3
	movq	%r15, 56(%rsp)
	movq	%r12, 64(%rsp)
	movq	(%r14), %rax
	movq	16(%r14), %rcx
	movq	%rax, 24(%rsp)
	movq	$0, 32(%rsp)
	movq	%rcx, 40(%rsp)
	movq	$0, 48(%rsp)
	movq	%r15, 8(%rsp)
	movq	%r12, 16(%rsp)
	leaq	24(%rsp), %rsi
	leaq	8(%rsp), %rcx
	movl	$2, %edi
	movl	$2, %edx
	movl	$1, %r8d
	callq	_RINvNtCsemcRClSg8DH_9native_vm5field19multilinear_eval_byNCNvB2_16multilinear_eval0EB4_
	movq	%rdx, %r9
	xorl	%ebp, %ebp
	leaq	56(%rsp), %rdx
	movq	%rbx, %rdi
	xorl	%esi, %esi
	movq	%r13, %rcx
	movq	%rax, %r8
	callq	_RNvNtCsemcRClSg8DH_9native_vm5stack10push_claim
	testb	%al, %al
	je	.LBB127_3
	movq	8(%r14), %rax
	movq	24(%r14), %rcx
	movq	%rax, 24(%rsp)
	movq	$0, 32(%rsp)
	movq	%rcx, 40(%rsp)
	movq	$0, 48(%rsp)
	movq	%r15, 8(%rsp)
	movq	%r12, 16(%rsp)
	leaq	24(%rsp), %rsi
	leaq	8(%rsp), %rcx
	movl	$2, %edi
	movl	$2, %edx
	movl	$1, %r8d
	callq	_RINvNtCsemcRClSg8DH_9native_vm5field19multilinear_eval_byNCNvB2_16multilinear_eval0EB4_
	movq	%rdx, %r9
	leaq	56(%rsp), %rdx
	movl	$1, %esi
	movq	%rbx, %rdi
	movq	%r13, %rcx
	movq	%rax, %r8
	callq	_RNvNtCsemcRClSg8DH_9native_vm5stack10push_claim
	movl	%eax, %ebp
.LBB127_3:
	movl	%ebp, %eax
	addq	$552, %rsp
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
.Lfunc_end127:
	.size	_RNvNtCsemcRClSg8DH_9native_vm6tables18public_input_phase, .Lfunc_end127-_RNvNtCsemcRClSg8DH_9native_vm6tables18public_input_phase
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm6tables19table_column_claims,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm6tables19table_column_claims,@function
_RNvNtCsemcRClSg8DH_9native_vm6tables19table_column_claims:
.Lfunc_begin128:
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
	pushq	%rax
	.cfi_def_cfa_offset 64
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	%rsi, %rbx
	movq	(%rdi), %rax
	movq	488(%rdi), %rbp
	leaq	496(%rdi), %rcx
	xorl	%r15d, %r15d
	cmpq	$93, %rbp
	movl	$8, %edx
	cmovaeq	%rdx, %rcx
	cmovaeq	%r15, %rbp
	movq	%rdi, (%rsp)
	leaq	8(%rdi), %r12
	cmpq	$31, %rax
	cmovaeq	%rdx, %r12
	cmovbq	%rax, %r15
	shlq	$4, %rbp
	movl	$4, %r13d
	.p2align	4
.LBB128_1:
	testq	%rbp, %rbp
	je	.LBB128_2
	leaq	16(%rcx), %r14
	movq	(%rcx), %r8
	movq	8(%rcx), %r9
	incq	%r13
	addq	$-16, %rbp
	movq	%rbx, %rdi
	movq	%r13, %rsi
	movq	%r12, %rdx
	movq	%r15, %rcx
	callq	_RNvNtCsemcRClSg8DH_9native_vm5stack10push_claim
	movq	%r14, %rcx
	testb	%al, %al
	jne	.LBB128_1
	jmp	.LBB128_19
.LBB128_2:
	movq	(%rsp), %rsi
	movq	1968(%rsi), %rax
	movq	2456(%rsi), %rbp
	leaq	2464(%rsi), %rcx
	xorl	%r15d, %r15d
	cmpq	$93, %rbp
	movl	$8, %edx
	cmovaeq	%rdx, %rcx
	cmovaeq	%r15, %rbp
	leaq	1976(%rsi), %r12
	cmpq	$31, %rax
	cmovaeq	%rdx, %r12
	cmovbq	%rax, %r15
	shlq	$4, %rbp
	movl	$17, %r13d
	.p2align	4
.LBB128_3:
	testq	%rbp, %rbp
	je	.LBB128_5
	leaq	16(%rcx), %r14
	movq	(%rcx), %r8
	movq	8(%rcx), %r9
	incq	%r13
	addq	$-16, %rbp
	movq	%rbx, %rdi
	movq	%r13, %rsi
	movq	%r12, %rdx
	movq	%r15, %rcx
	callq	_RNvNtCsemcRClSg8DH_9native_vm5stack10push_claim
	movq	%r14, %rcx
	testb	%al, %al
	jne	.LBB128_3
	jmp	.LBB128_19
.LBB128_5:
	movq	(%rsp), %rsi
	movq	3936(%rsi), %rax
	movq	4424(%rsi), %rbp
	leaq	4432(%rsi), %rcx
	xorl	%r15d, %r15d
	cmpq	$93, %rbp
	movl	$8, %edx
	cmovaeq	%rdx, %rcx
	cmovaeq	%r15, %rbp
	leaq	3944(%rsi), %r12
	cmpq	$31, %rax
	cmovaeq	%rdx, %r12
	cmovbq	%rax, %r15
	shlq	$4, %rbp
	movl	$30, %r13d
	.p2align	4
.LBB128_6:
	testq	%rbp, %rbp
	je	.LBB128_8
	leaq	16(%rcx), %r14
	movq	(%rcx), %r8
	movq	8(%rcx), %r9
	incq	%r13
	addq	$-16, %rbp
	movq	%rbx, %rdi
	movq	%r13, %rsi
	movq	%r12, %rdx
	movq	%r15, %rcx
	callq	_RNvNtCsemcRClSg8DH_9native_vm5stack10push_claim
	movq	%r14, %rcx
	testb	%al, %al
	jne	.LBB128_6
	jmp	.LBB128_19
.LBB128_8:
	movq	(%rsp), %rsi
	movq	5904(%rsi), %rax
	movq	6392(%rsi), %rbp
	leaq	6400(%rsi), %rcx
	xorl	%r15d, %r15d
	cmpq	$93, %rbp
	movl	$8, %edx
	cmovaeq	%rdx, %rcx
	cmovaeq	%r15, %rbp
	leaq	5912(%rsi), %r12
	cmpq	$31, %rax
	cmovaeq	%rdx, %r12
	cmovbq	%rax, %r15
	shlq	$4, %rbp
	movl	$37, %r13d
	.p2align	4
.LBB128_9:
	testq	%rbp, %rbp
	je	.LBB128_11
	leaq	16(%rcx), %r14
	movq	(%rcx), %r8
	movq	8(%rcx), %r9
	incq	%r13
	addq	$-16, %rbp
	movq	%rbx, %rdi
	movq	%r13, %rsi
	movq	%r12, %rdx
	movq	%r15, %rcx
	callq	_RNvNtCsemcRClSg8DH_9native_vm5stack10push_claim
	movq	%r14, %rcx
	testb	%al, %al
	jne	.LBB128_9
	jmp	.LBB128_19
.LBB128_11:
	movq	(%rsp), %rsi
	movq	7872(%rsi), %rax
	movq	8360(%rsi), %rbp
	leaq	8368(%rsi), %rcx
	xorl	%r15d, %r15d
	cmpq	$93, %rbp
	movl	$8, %edx
	cmovaeq	%rdx, %rcx
	cmovaeq	%r15, %rbp
	leaq	7880(%rsi), %r12
	cmpq	$31, %rax
	cmovaeq	%rdx, %r12
	cmovbq	%rax, %r15
	shlq	$4, %rbp
	movl	$51, %r13d
	.p2align	4
.LBB128_12:
	testq	%rbp, %rbp
	je	.LBB128_14
	leaq	16(%rcx), %r14
	movq	(%rcx), %r8
	movq	8(%rcx), %r9
	incq	%r13
	addq	$-16, %rbp
	movq	%rbx, %rdi
	movq	%r13, %rsi
	movq	%r12, %rdx
	movq	%r15, %rcx
	callq	_RNvNtCsemcRClSg8DH_9native_vm5stack10push_claim
	movq	%r14, %rcx
	testb	%al, %al
	jne	.LBB128_12
.LBB128_19:
	xorl	%eax, %eax
.LBB128_20:
	addq	$8, %rsp
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
.LBB128_14:
	.cfi_def_cfa_offset 64
	movq	(%rsp), %rbp
	movq	9840(%rbp), %rax
	movq	10328(%rbp), %r13
	leaq	10336(%rbp), %rdx
	xorl	%r15d, %r15d
	cmpq	$93, %r13
	movl	$8, %ecx
	cmovaeq	%rcx, %rdx
	cmovaeq	%r15, %r13
	addq	$9848, %rbp
	cmpq	$31, %rax
	cmovaeq	%rcx, %rbp
	cmovbq	%rax, %r15
	shlq	$4, %r13
	movl	$65, %r12d
	.p2align	4
.LBB128_15:
	testq	%r13, %r13
	je	.LBB128_16
	leaq	16(%rdx), %r14
	movq	(%rdx), %r8
	movq	8(%rdx), %r9
	incq	%r12
	addq	$-16, %r13
	movq	%rbx, %rdi
	movq	%r12, %rsi
	movq	%rbp, %rdx
	movq	%r15, %rcx
	callq	_RNvNtCsemcRClSg8DH_9native_vm5stack10push_claim
	movl	%eax, %ecx
	xorl	%eax, %eax
	movq	%r14, %rdx
	testb	%cl, %cl
	jne	.LBB128_15
	jmp	.LBB128_20
.LBB128_16:
	movb	$1, %al
	jmp	.LBB128_20
.Lfunc_end128:
	.size	_RNvNtCsemcRClSg8DH_9native_vm6tables19table_column_claims, .Lfunc_end128-_RNvNtCsemcRClSg8DH_9native_vm6tables19table_column_claims
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm6verify16verify_execution,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm6verify16verify_execution,@function
_RNvNtCsemcRClSg8DH_9native_vm6verify16verify_execution:
.Lfunc_begin129:
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
	pushq	%rax
	.cfi_def_cfa_offset 64
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	%r8, %rbx
	movq	%rcx, (%rsp)
	movq	%rdx, %r13
	movq	%rsi, %r12
	movq	%rdi, %r14
	movq	%rdx, %rsi
	movq	%r8, %rdx
	callq	_RNvNtCsemcRClSg8DH_9native_vm6layout20read_announced_sizes
	cmpq	$1, %rax
	jne	.LBB129_10
	movq	%rdx, %r15
	movq	16(%rbx), %rbp
	movq	%r14, %rdi
	movq	%rbp, %rsi
	callq	_RNvNtCsemcRClSg8DH_9native_vm5stack12commit_stack
	testb	%al, %al
	je	.LBB129_10
	leaq	3912(%rbx), %rax
	movq	%r14, %rdi
	movq	%rbp, %rsi
	movq	%rax, %rbp
	movq	%rax, %rdx
	callq	_RNvNtCsemcRClSg8DH_9native_vm5stack8read_ood
	testb	%al, %al
	je	.LBB129_10
	leaq	4416(%rbx), %r8
	leaq	123992(%rbx), %r9
	movq	%r14, %rdi
	movq	%rbx, %rsi
	movq	%r12, %rdx
	movq	%r13, %rcx
	movq	%r8, %r12
	movq	%r9, %r13
	callq	_RNvNtCsemcRClSg8DH_9native_vm3bus18verify_bus_balance
	testb	%al, %al
	je	.LBB129_10
	leaq	112184(%rbx), %rax
	movq	%r14, %rdi
	movq	%rbx, %rsi
	movq	%r12, %rdx
	movq	%rax, %r12
	movq	%rax, %rcx
	callq	_RNvNtCsemcRClSg8DH_9native_vm6tables11table_phase
	testb	%al, %al
	je	.LBB129_10
	movq	%r12, %rdi
	movq	%r13, %rsi
	callq	_RNvNtCsemcRClSg8DH_9native_vm6tables19table_column_claims
	testb	%al, %al
	je	.LBB129_10
	movq	%r14, %rdi
	movq	%rbx, %rsi
	movq	(%rsp), %rdx
	movq	%r13, %rcx
	callq	_RNvNtCsemcRClSg8DH_9native_vm6tables18public_input_phase
	testb	%al, %al
	je	.LBB129_10
	leaq	289728(%rbx), %rcx
	leaq	221280(%rbx), %r9
	movq	64(%rbx), %rsi
	movq	%r14, %rdi
	movq	%r12, %rdx
	movq	%r13, %r8
	movq	%r9, (%rsp)
	callq	_RNvNtCsemcRClSg8DH_9native_vm10keccak_gkr12keccak_phase
	testb	%al, %al
	je	.LBB129_10
	leaq	221864(%rbx), %rsi
	leaq	222888(%rbx), %r12
	movq	%r14, %rdi
	movq	%r12, %rdx
	callq	_RNvNtCsemcRClSg8DH_9native_vm11ring_switch11ring_switch
	testb	%al, %al
	je	.LBB129_10
	leaq	223928(%rbx), %rax
	leaq	226528(%rbx), %r10
	subq	$8, %rsp
	.cfi_adjust_cfa_offset 8
	movq	%r14, %rdi
	movq	%rbx, %rsi
	movq	%r15, %rdx
	movq	%r12, %rcx
	movq	8(%rsp), %r8
	movq	%r13, %r9
	pushq	%r10
	.cfi_adjust_cfa_offset 8
	pushq	%rax
	.cfi_adjust_cfa_offset 8
	pushq	%rbp
	.cfi_adjust_cfa_offset 8
	callq	_RNvNtCsemcRClSg8DH_9native_vm4whir22verify_stacked_opening
	addq	$40, %rsp
	.cfi_adjust_cfa_offset -40
	jmp	.LBB129_11
.LBB129_10:
	.cfi_def_cfa_offset 64
	xorl	%eax, %eax
	addq	$8, %rsp
	.cfi_def_cfa_offset 56
.LBB129_11:
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
.Lfunc_end129:
	.size	_RNvNtCsemcRClSg8DH_9native_vm6verify16verify_execution, .Lfunc_end129-_RNvNtCsemcRClSg8DH_9native_vm6verify16verify_execution
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm6verify4seed,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm6verify4seed,@function
_RNvNtCsemcRClSg8DH_9native_vm6verify4seed:
.Lfunc_begin130:
	.cfi_startproc
	pushq	%r15
	.cfi_def_cfa_offset 16
	pushq	%r14
	.cfi_def_cfa_offset 24
	pushq	%rbx
	.cfi_def_cfa_offset 32
	subq	$208, %rsp
	.cfi_def_cfa_offset 240
	.cfi_offset %rbx, -32
	.cfi_offset %r14, -24
	.cfi_offset %r15, -16
	movq	%rcx, %r15
	movq	%rdx, %r8
	movq	%rsi, %rcx
	movq	%rdi, %rbx
	leaq	2(%rdx), %rsi
	leaq	9(,%rdx,8), %rdx
	leaq	8(%rsp), %r14
	movq	%r14, %rdi
	callq	_RINvNtCsemcRClSg8DH_9native_vm6keccak15keccak256_wordsNCNvNtB4_6verify14fiat_shamir_iv0EB4_
	leaq	72(%rsp), %rdi
	movl	$136, %edx
	xorl	%esi, %esi
	callq	*memset@GOTPCREL(%rip)
	movq	(%r15), %rax
	movq	8(%r15), %rcx
	movq	%rax, 40(%rsp)
	movq	%rcx, 48(%rsp)
	movq	16(%r15), %rax
	movq	%rax, 56(%rsp)
	movq	24(%r15), %rax
	movq	%rax, 64(%rsp)
	movq	%r14, %rdi
	callq	_RNvNtCsemcRClSg8DH_9native_vm6keccak8keccak_f
	movl	$200, %edx
	movq	%rbx, %rdi
	movq	%r14, %rsi
	callq	*memcpy@GOTPCREL(%rip)
	addq	$208, %rsp
	.cfi_def_cfa_offset 32
	popq	%rbx
	.cfi_def_cfa_offset 24
	popq	%r14
	.cfi_def_cfa_offset 16
	popq	%r15
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end130:
	.size	_RNvNtCsemcRClSg8DH_9native_vm6verify4seed, .Lfunc_end130-_RNvNtCsemcRClSg8DH_9native_vm6verify4seed
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm6verify6verify,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm6verify6verify,@function
_RNvNtCsemcRClSg8DH_9native_vm6verify6verify:
.Lfunc_begin131:
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
	subq	$760, %rsp
	.cfi_def_cfa_offset 816
	.cfi_offset %rbx, -56
	.cfi_offset %r12, -48
	.cfi_offset %r13, -40
	.cfi_offset %r14, -32
	.cfi_offset %r15, -24
	.cfi_offset %rbp, -16
	movq	%r8, %r14
	movq	%rcx, %rbx
	movq	%rdx, %r15
	movq	%rsi, %r12
	movq	%rdi, %r13
	movq	%rsp, %rbp
	movq	%rbp, %rdi
	movq	%r13, %rsi
	movq	%r12, %rdx
	movq	%r15, %rcx
	callq	_RNvNtCsemcRClSg8DH_9native_vm6verify4seed
	movq	$0, 200(%rsp)
	movq	$0, 208(%rsp)
	movq	$0, 216(%rsp)
	movq	$0, 224(%rsp)
	movq	$0, 232(%rsp)
	movq	$0, 240(%rsp)
	movq	$0, 248(%rsp)
	movq	$0, 256(%rsp)
	movq	$0, 264(%rsp)
	movq	$0, 272(%rsp)
	movq	$0, 280(%rsp)
	movq	$0, 288(%rsp)
	movq	$0, 296(%rsp)
	movq	$0, 304(%rsp)
	movq	(%rbx), %rax
	movq	8(%rbx), %rcx
	movq	%rax, 328(%rsp)
	movq	%rcx, 336(%rsp)
	movq	16(%rbx), %rax
	movq	%rax, 344(%rsp)
	movq	$0, 352(%rsp)
	movq	$0, 360(%rsp)
	movq	$0, 368(%rsp)
	movq	$0, 376(%rsp)
	movq	$0, 384(%rsp)
	movq	$0, 392(%rsp)
	movq	$0, 400(%rsp)
	movq	$0, 408(%rsp)
	movq	$0, 416(%rsp)
	movq	$0, 424(%rsp)
	movq	$0, 432(%rsp)
	movq	$0, 440(%rsp)
	movq	$0, 448(%rsp)
	movq	$0, 456(%rsp)
	movq	$0, 464(%rsp)
	movq	$0, 472(%rsp)
	movq	$0, 480(%rsp)
	movq	$0, 488(%rsp)
	movq	$0, 496(%rsp)
	movq	$0, 504(%rsp)
	movq	$0, 512(%rsp)
	movq	$0, 520(%rsp)
	movq	$0, 528(%rsp)
	movq	$0, 536(%rsp)
	movq	$0, 544(%rsp)
	movq	$0, 552(%rsp)
	movq	$0, 560(%rsp)
	movq	$0, 568(%rsp)
	movq	$0, 576(%rsp)
	movq	$0, 584(%rsp)
	movq	$0, 592(%rsp)
	movq	$0, 600(%rsp)
	movq	$0, 608(%rsp)
	movq	$0, 616(%rsp)
	movq	$0, 624(%rsp)
	movq	$0, 632(%rsp)
	movq	$0, 640(%rsp)
	movq	$0, 648(%rsp)
	movq	$0, 656(%rsp)
	movq	$0, 664(%rsp)
	movq	$0, 672(%rsp)
	movq	$0, 680(%rsp)
	movq	$0, 688(%rsp)
	movq	$0, 696(%rsp)
	movq	$0, 704(%rsp)
	movq	$0, 712(%rsp)
	movq	$0, 720(%rsp)
	movq	$0, 728(%rsp)
	movq	$0, 736(%rsp)
	movq	$0, 744(%rsp)
	movq	$0, 752(%rsp)
	movq	%rbp, %rdi
	movq	%r13, %rsi
	movq	%r12, %rdx
	movq	%r15, %rcx
	movq	%r14, %r8
	callq	_RNvNtCsemcRClSg8DH_9native_vm6verify16verify_execution
	testb	%al, %al
	je	.LBB131_5
	movq	352(%rsp), %rax
	cmpq	$0, 8(%rbx)
	je	.LBB131_2
	movq	(%rbx), %rcx
	movq	(%rcx), %rcx
	cmpq	%rcx, %rax
	jne	.LBB131_5
.LBB131_7:
	movq	360(%rsp), %r14
	movq	%rbx, %rdi
	callq	_RNvMNtCsemcRClSg8DH_9native_vm5inputNtB2_7Decoded11phase_count
	cmpq	%rax, %r14
	sete	%al
	jmp	.LBB131_6
.LBB131_2:
	xorl	%ecx, %ecx
	cmpq	%rcx, %rax
	je	.LBB131_7
.LBB131_5:
	xorl	%eax, %eax
.LBB131_6:
	addq	$760, %rsp
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
.Lfunc_end131:
	.size	_RNvNtCsemcRClSg8DH_9native_vm6verify6verify, .Lfunc_end131-_RNvNtCsemcRClSg8DH_9native_vm6verify6verify
	.cfi_endproc

	.section	.text._RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word,"ax",@progbits
	.p2align	4
	.type	_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word,@function
_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word:
.Lfunc_begin132:
	.cfi_startproc
	testq	%rdx, %rdx
	je	.LBB132_1
	movq	%rdx, %rcx
	decq	%rcx
	je	.LBB132_3
	leaq	-2(%rdx), %rax
	cmpq	%rsi, %rax
	jae	.LBB132_5
	movzbl	-9(%rdi,%rdx,8), %eax
	cmpq	%rsi, %rcx
	jb	.LBB132_8
	jmp	.LBB132_9
.LBB132_1:
	movabsq	$8515582825852921196, %rax
	retq
.LBB132_3:
	movl	$49, %eax
	cmpq	%rsi, %rcx
	jae	.LBB132_9
.LBB132_8:
	movq	-8(%rdi,%rdx,8), %rcx
	shlq	$8, %rcx
	orq	%rcx, %rax
.LBB132_9:
	retq
.LBB132_5:
	xorl	%eax, %eax
	cmpq	%rsi, %rcx
	jb	.LBB132_8
	jmp	.LBB132_9
.Lfunc_end132:
	.size	_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word, .Lfunc_end132-_RNvNtCsemcRClSg8DH_9native_vm6verify7iv_word
	.cfi_endproc

	.section	.text._RNvNvNtCsemcRClSg8DH_9native_vm5field4kinv2sq,"ax",@progbits
	.p2align	4
	.type	_RNvNvNtCsemcRClSg8DH_9native_vm5field4kinv2sq,@function
_RNvNvNtCsemcRClSg8DH_9native_vm5field4kinv2sq:
.Lfunc_begin133:
	.cfi_startproc
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset %rbx, -16
	movl	%esi, %ebx
	movq	%rdi, %rax
	.p2align	4
.LBB133_1:
	movq	%rax, %rdi
	movq	%rax, %rsi
	callq	_RNvNtCsemcRClSg8DH_9native_vm5field4kmul
	decl	%ebx
	jne	.LBB133_1
	popq	%rbx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end133:
	.size	_RNvNvNtCsemcRClSg8DH_9native_vm5field4kinv2sq, .Lfunc_end133-_RNvNvNtCsemcRClSg8DH_9native_vm5field4kinv2sq
	.cfi_endproc

	.section	.text.leanvm_verify,"ax",@progbits
	.globl	leanvm_verify
	.p2align	4
	.type	leanvm_verify,@function
leanvm_verify:
.Lfunc_begin134:
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
	movq	8(%rdi), %rbx
	xorl	%eax, %eax
	movq	%rbx, %rcx
	shrq	$32, %rcx
	jne	.LBB134_18
	movq	24(%rdi), %r14
	cmpq	$536870910, %r14
	ja	.LBB134_18
	movq	%rbx, %r15
	shrq	$3, %r15
	orq	$1, %r15
	addq	$395289, %r15
	cmpq	%r15, 72(%rdi)
	jb	.LBB134_18
	cmpq	$61944, 88(%rdi)
	jb	.LBB134_18
	movq	64(%rdi), %r12
	testq	%r12, %r12
	sete	%al
	testb	$7, %r12b
	setne	%cl
	orb	%al, %cl
	jne	.LBB134_17
	movq	80(%rdi), %r13
	testq	%r13, %r13
	sete	%al
	testb	$7, %r13b
	setne	%cl
	orb	%al, %cl
	jne	.LBB134_17
	movq	(%rdi), %rax
	movq	16(%rdi), %rbp
	movq	32(%rdi), %r8
	movq	40(%rdi), %rsi
	movq	48(%rdi), %rdx
	movq	56(%rdi), %rcx
	testq	%r14, %r14
	je	.LBB134_8
	testq	%rbp, %rbp
	setne	%dil
	testb	$7, %bpl
	sete	%r9b
	testb	%r9b, %dil
	je	.LBB134_17
.LBB134_8:
	testq	%rbx, %rbx
	je	.LBB134_15
	testq	%rax, %rax
	je	.LBB134_17
	movq	%r8, (%rsp)
	movq	%rsi, 8(%rsp)
	movq	%rdx, 16(%rsp)
	movq	%rcx, 24(%rsp)
	movq	%rax, %rdi
	movq	%rbx, %rsi
	movq	%r12, %rdx
	movq	%r15, %rcx
	movq	%r13, %r8
	callq	_RNvNtCsemcRClSg8DH_9native_vm4wire6decode
	testb	%al, %al
	jne	.LBB134_16
.LBB134_17:
	xorl	%eax, %eax
.LBB134_18:
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
.LBB134_15:
	.cfi_def_cfa_offset 112
	movq	%r8, (%rsp)
	movq	%rsi, 8(%rsp)
	movq	%rdx, 16(%rsp)
	movq	%rcx, 24(%rsp)
	movl	$1, %edi
	xorl	%esi, %esi
	movq	%r12, %rdx
	movq	%r15, %rcx
	movq	%r13, %r8
	callq	_RNvNtCsemcRClSg8DH_9native_vm4wire6decode
	movl	%eax, %ecx
	xorl	%eax, %eax
	testb	%cl, %cl
	je	.LBB134_18
.LBB134_16:
	testq	%r14, %r14
	movl	$8, %eax
	cmoveq	%rax, %rbp
	movq	%r12, 32(%rsp)
	movq	%r15, 40(%rsp)
	movq	%rbx, 48(%rsp)
	movq	%rsp, %rdx
	leaq	32(%rsp), %rcx
	movq	%rbp, %rdi
	movq	%r14, %rsi
	movq	%r13, %r8
	callq	_RNvNtCsemcRClSg8DH_9native_vm6verify6verify
	movzbl	%al, %eax
	jmp	.LBB134_18
.Lfunc_end134:
	.size	leanvm_verify, .Lfunc_end134-leanvm_verify
	.cfi_endproc

	.section	.text.memcpy,"ax",@progbits
	.globl	memcpy
	.p2align	4
	.type	memcpy,@function
memcpy:
.Lfunc_begin135:
	.cfi_startproc
	movq	%rdi, %rax
	movl	%esi, %ecx
	orl	%eax, %ecx
	movl	%edx, %edi
	orl	%ecx, %edi
	testb	$7, %dil
	je	.LBB135_4
	testq	%rdx, %rdx
	je	.LBB135_7
	xorl	%ecx, %ecx
	.p2align	4
.LBB135_3:
	movzbl	(%rsi,%rcx), %edi
	movb	%dil, (%rax,%rcx)
	incq	%rcx
	#APP
	#NO_APP
	cmpq	%rcx, %rdx
	jne	.LBB135_3
	jmp	.LBB135_7
.LBB135_4:
	testq	%rdx, %rdx
	je	.LBB135_7
	xorl	%ecx, %ecx
	.p2align	4
.LBB135_6:
	movq	(%rsi,%rcx), %rdi
	movq	%rdi, (%rax,%rcx)
	addq	$8, %rcx
	#APP
	#NO_APP
	cmpq	%rdx, %rcx
	jb	.LBB135_6
.LBB135_7:
	retq
.Lfunc_end135:
	.size	memcpy, .Lfunc_end135-memcpy
	.cfi_endproc

	.section	.text.memset,"ax",@progbits
	.globl	memset
	.p2align	4
	.type	memset,@function
memset:
.Lfunc_begin136:
	.cfi_startproc
	movq	%rdi, %rax
	movl	%edx, %ecx
	orl	%eax, %ecx
	testb	$7, %cl
	je	.LBB136_4
	testq	%rdx, %rdx
	je	.LBB136_7
	xorl	%ecx, %ecx
	.p2align	4
.LBB136_3:
	movb	%sil, (%rax,%rcx)
	incq	%rcx
	#APP
	#NO_APP
	cmpq	%rcx, %rdx
	jne	.LBB136_3
	jmp	.LBB136_7
.LBB136_4:
	testq	%rdx, %rdx
	je	.LBB136_7
	movzbl	%sil, %esi
	movabsq	$72340172838076673, %rcx
	imulq	%rsi, %rcx
	xorl	%esi, %esi
	.p2align	4
.LBB136_6:
	movq	%rcx, (%rax,%rsi)
	addq	$8, %rsi
	#APP
	#NO_APP
	cmpq	%rdx, %rsi
	jb	.LBB136_6
.LBB136_7:
	retq
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
