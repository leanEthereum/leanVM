// Credits: whir-p3 (https://github.com/tcoratger/whir-p3) (MIT and Apache-2.0 licenses).

mod commit;
pub use commit::*;
use poly::*;

mod open;
pub use open::*;

mod verify;
pub use verify::*;

mod dft;
pub use dft::*;

mod config;
pub use config::*;

mod merkle;
pub use merkle::DIGEST_ELEMS;
pub(crate) use merkle::*;

mod utils;
pub use utils::precompute_dft_twiddles;
pub(crate) use utils::*;

mod matrix;
pub(crate) use matrix::*;

#[derive(Clone, Debug)]
pub struct SparseStatement<EF> {
    pub total_num_variables: usize,
    pub point: MultilinearPoint<EF>,
    pub values: Vec<SparseValue<EF>>,
    /// When true, the weight polynomial is `next_mle(point, .)` instead of `eq(point, .)`.
    pub is_next: bool,
    /// Optional tensor tail occupying the lowest `log2(tail.len())` inner
    /// variables: the inner weight becomes `eq(point, hi) * MLE(tail)(lo)`
    /// where `lo` indexes the fastest-varying coordinates (for `is_next`,
    /// the shift-by-one of that weight). `tail.len()` must be a power of two.
    pub tail: Option<Vec<EF>>,
}

impl<EF> SparseStatement<EF> {
    pub fn new(total_num_variables: usize, point: MultilinearPoint<EF>, values: Vec<SparseValue<EF>>) -> Self {
        assert!(
            total_num_variables >= point.len(),
            "total_num_variables ({}) must be >= point.len() ({})",
            total_num_variables,
            point.len()
        );
        Self {
            total_num_variables,
            point,
            values,
            is_next: false,
            tail: None,
        }
    }

    pub fn new_next(total_num_variables: usize, point: MultilinearPoint<EF>, values: Vec<SparseValue<EF>>) -> Self {
        assert!(
            total_num_variables >= point.len(),
            "total_num_variables ({}) must be >= point.len() ({})",
            total_num_variables,
            point.len()
        );
        Self {
            total_num_variables,
            point,
            values,
            is_next: true,
            tail: None,
        }
    }

    pub fn new_with_tail(
        total_num_variables: usize,
        point: MultilinearPoint<EF>,
        tail: Vec<EF>,
        values: Vec<SparseValue<EF>>,
    ) -> Self {
        let mut smt = Self::new(total_num_variables, point, values);
        smt.set_tail(tail);
        smt
    }

    pub fn new_next_with_tail(
        total_num_variables: usize,
        point: MultilinearPoint<EF>,
        tail: Vec<EF>,
        values: Vec<SparseValue<EF>>,
    ) -> Self {
        let mut smt = Self::new_next(total_num_variables, point, values);
        smt.set_tail(tail);
        smt
    }

    fn set_tail(&mut self, tail: Vec<EF>) {
        assert!(tail.len().is_power_of_two(), "tail length must be a power of two");
        let tail_log = tail.len().trailing_zeros() as usize;
        assert!(
            self.total_num_variables >= self.point.len() + tail_log,
            "total_num_variables ({}) must be >= point.len() ({}) + tail_log ({})",
            self.total_num_variables,
            self.point.len(),
            tail_log
        );
        self.tail = Some(tail);
    }

    pub fn unique_value(total_num_variables: usize, index: usize, value: EF) -> Self {
        Self {
            total_num_variables,
            point: MultilinearPoint(vec![]),
            values: vec![SparseValue { selector: index, value }],
            is_next: false,
            tail: None,
        }
    }

    pub fn dense(point: MultilinearPoint<EF>, value: EF) -> Self {
        Self {
            total_num_variables: point.len(),
            point,
            values: vec![SparseValue { selector: 0, value }],
            is_next: false,
            tail: None,
        }
    }

    pub fn selector_num_variables(&self) -> usize {
        self.total_num_variables
            .checked_sub(self.inner_num_variables())
            .expect("invariant violated: total_num_variables < point.len()")
    }

    pub fn tail_num_variables(&self) -> usize {
        self.tail.as_ref().map_or(0, |t| t.len().trailing_zeros() as usize)
    }

    pub fn inner_num_variables(&self) -> usize {
        self.point.len() + self.tail_num_variables()
    }
}

#[derive(Clone, Debug)]
pub struct SparseValue<EF> {
    pub selector: usize,
    pub value: EF,
}

impl<EF> SparseValue<EF> {
    pub fn new(selector: usize, value: EF) -> Self {
        Self { selector, value }
    }
}
