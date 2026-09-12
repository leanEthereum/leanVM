fn main() {
    lean_vm::init_prover_pool();
    let mut prove = false;
    let mut local_digits = false;
    let mut local_ranges = false;
    let mut children = None;
    let args: Vec<usize> = std::env::args()
        .skip(1)
        .filter_map(|n| {
            if n == "--prove" {
                assert!(!prove, "duplicate --prove");
                prove = true;
                None
            } else if n == "--local-digits" {
                assert!(!local_digits, "duplicate --local-digits");
                local_digits = true;
                None
            } else if n == "--local-ranges" {
                assert!(!local_ranges, "duplicate --local-ranges");
                local_ranges = true;
                None
            } else if let Some(count) = n.strip_prefix("--children=") {
                assert!(children.is_none(), "duplicate --children");
                children = Some(count.parse().expect("child count"));
                None
            } else {
                Some(n.parse().expect("nonnegative signature count"))
            }
        })
        .collect();
    assert!(
        args.len() <= 2,
        "optional arguments: XMSS count, SPHINCS count, --prove, --local-digits, --local-ranges, --children=N"
    );
    if let Some(children) = children {
        assert!(!local_digits, "recursive audit uses local exponent checks");
        rec_aggregation::aggregation::zk_research::audit_recursion(
            args.first().copied().unwrap_or(1),
            args.get(1).copied().unwrap_or(0),
            children,
            prove,
        );
        return;
    }
    rec_aggregation::aggregation::zk_research::audit_leaf(
        args.first().copied().unwrap_or(6),
        args.get(1).copied().unwrap_or(0),
        prove,
        local_digits,
        local_ranges,
    );
}
