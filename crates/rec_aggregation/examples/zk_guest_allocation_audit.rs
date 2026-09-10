fn main() {
    lean_vm::init_prover_pool();
    let mut prove = false;
    let args: Vec<usize> = std::env::args()
        .skip(1)
        .filter_map(|n| {
            if n == "--prove" {
                assert!(!prove, "duplicate --prove");
                prove = true;
                None
            } else {
                Some(n.parse().expect("nonnegative signature count"))
            }
        })
        .collect();
    assert!(
        args.len() <= 2,
        "optional arguments: XMSS count, SPHINCS count, --prove"
    );
    rec_aggregation::aggregation::zk_research::audit_leaf(
        args.first().copied().unwrap_or(6),
        args.get(1).copied().unwrap_or(0),
        prove,
    );
}
