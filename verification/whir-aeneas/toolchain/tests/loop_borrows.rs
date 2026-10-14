//! Minimal loop shapes for the pinned Aeneas loop translation.
//!
//! Functions named `rejected_*` reproduce the verifier's remaining loop failures; `accepted_*`
//! are the source shapes that translate. `check-loop-borrows.py` checks each outcome.

pub struct Ring {
    pub claims: Vec<u64>,
}

pub struct View<'a> {
    pub rings: &'a [Ring],
}

pub struct Shared<'a> {
    pub rings: &'a [Ring],
    pub scales: Vec<u64>,
}

pub struct Outer<'a> {
    pub inner: &'a View<'a>,
    pub points: &'a [u64],
}

#[derive(Clone, Copy)]
pub struct Copied<'a> {
    pub rings: &'a [Ring],
}

pub struct Claim {
    pub point: Vec<u64>,
    pub slices: Vec<u64>,
}

pub struct Region {
    pub vars: usize,
    pub claims: Vec<Claim>,
}

/// A shared borrow of a shared borrow, read in a loop.
pub fn rejected_ref_ref(s: &&[u64]) -> u64 {
    let mut index = 0;
    let mut last = 0;
    while index < s.len() {
        last = s[index];
        index += 1;
    }
    last
}

/// A shared borrow of a value holding a shared slice, read in a loop.
pub fn rejected_view(s: &View<'_>) -> bool {
    let mut index = 0;
    let mut empty = true;
    while index < s.rings.len() {
        empty = s.rings[index].claims.is_empty();
        index += 1;
    }
    empty
}

/// The same, with an owned field next to the borrowed one.
pub fn rejected_shared(s: &Shared<'_>) -> u64 {
    let mut index = 0;
    let mut last = 0;
    while index < s.scales.len() {
        last = s.scales[index];
        index += 1;
    }
    last
}

/// A by-value input whose field is a borrow of a value holding a borrow.
pub fn rejected_outer(w: Outer<'_>) -> u64 {
    let mut index = 0;
    let mut last = 0;
    while index < w.points.len() {
        last = w.points[index];
        index += 1;
    }
    last
}

/// A borrow returned by a call, read across loop iterations.
pub fn rejected_split_last(terms: &[u64]) -> u64 {
    let (&last, rest) = terms.split_last().expect("nonempty");
    let mut acc = last;
    let mut index = rest.len();
    while index > 0 {
        index -= 1;
        acc ^= rest[index];
    }
    acc
}

/// A short-circuit branch inside the loop while an indexed borrow is live.
pub fn rejected_branch_on_borrow(region: &Region) -> bool {
    let mut index = 0;
    let mut all = true;
    while index < region.claims.len() && all {
        let claim = &region.claims[index];
        all = claim.point.len() == region.vars && claim.slices.len() == 64;
        index += 1;
    }
    all
}

/// The direct slice parameter translates.
pub fn accepted_slice(rings: &[Ring]) -> bool {
    let mut index = 0;
    let mut empty = true;
    while index < rings.len() && empty {
        empty = rings[index].claims.is_empty();
        index += 1;
    }
    empty
}

/// A copied value holding the slice translates.
pub fn accepted_copied(s: Copied<'_>) -> bool {
    let mut index = 0;
    let mut empty = true;
    while index < s.rings.len() && empty {
        empty = s.rings[index].claims.is_empty();
        index += 1;
    }
    empty
}

/// Indexing instead of a returned borrow translates.
pub fn accepted_indexed(terms: &[u64]) -> u64 {
    let mut index = terms.len() - 1;
    let mut acc = terms[index];
    while index > 0 {
        index -= 1;
        acc ^= terms[index];
    }
    acc
}

fn spans(claim: &Claim, vars: usize) -> bool {
    claim.point.len() == vars && claim.slices.len() == 64
}

/// The branch moved into a callee translates.
pub fn accepted_branch_in_callee(region: &Region) -> bool {
    let mut index = 0;
    let mut all = true;
    while index < region.claims.len() && all {
        all = spans(&region.claims[index], region.vars);
        index += 1;
    }
    all
}

pub struct Source {
    pub n: u64,
}

impl Source {
    fn next(&mut self, k: usize) -> Result<u64, u32> {
        if self.n == 0 {
            return Err(1);
        }
        self.n -= 1;
        Ok(self.n + k as u64)
    }
}

/// A collecting closure that captures a mutable borrow, inside a loop.
pub fn rejected_closure_in_loop(source: &mut Source, counts: &[usize]) -> Result<usize, u32> {
    let mut total = 0;
    let mut i = 0;
    while i < counts.len() {
        let read: Vec<u64> = (0..counts[i]).map(|_| source.next(i)).collect::<Result<_, _>>()?;
        total += read.len();
        i += 1;
    }
    Ok(total)
}

fn read_all(source: &mut Source, count: usize, k: usize) -> Result<Vec<u64>, u32> {
    let mut read = Vec::new();
    let mut j = 0;
    while j < count {
        read.push(source.next(k)?);
        j += 1;
    }
    Ok(read)
}

/// The same reads as an explicit loop in a callee translate.
pub fn accepted_loop_in_callee(source: &mut Source, counts: &[usize]) -> Result<usize, u32> {
    let mut total = 0;
    let mut i = 0;
    while i < counts.len() {
        total += read_all(source, counts[i], i)?.len();
        i += 1;
    }
    Ok(total)
}

pub trait Arith {
    type E: Copy;
    fn add(&mut self, a: Self::E, b: Self::E) -> Self::E;
}

pub trait Verifier: Arith {
    fn sample(&mut self) -> Self::E;
}

pub trait Opening: Verifier {
    type Root: Copy;
}

pub trait Weight<V: Opening> {
    fn call(self, v: &mut V, point: &[V::E]) -> V::E;
}

pub trait NamedWeight<E, V: Opening<E = E>> {
    fn call(self, v: &mut V, point: &[E]) -> E;
}

/// A weight whose point and value are written through the verifier's projection.
pub fn rejected_projected_weight<V: Opening>(v: &mut V, point: &[V::E], weight: impl Weight<V>) -> V::E {
    weight.call(v, point)
}

/// The weight with its element type as a parameter translates.
pub fn accepted_named_weight<V: Opening>(v: &mut V, point: &[V::E], weight: impl NamedWeight<V::E, V>) -> V::E {
    weight.call(v, point)
}

/// A loop that calls only inherited arithmetic methods of the opening verifier.
pub fn rejected_inherited_loop<V: Opening>(v: &mut V, point: &[V::E]) -> V::E {
    let mut acc = v.sample();
    let mut k = 0;
    while k < point.len() {
        acc = v.add(acc, point[k]);
        k += 1;
    }
    acc
}

fn arith_sum<E: Copy, A: Arith<E = E>>(a: &mut A, point: &[E], mut acc: E) -> E {
    let mut k = 0;
    while k < point.len() {
        acc = a.add(acc, point[k]);
        k += 1;
    }
    acc
}

/// The loop in a callee generic over the arithmetic trait translates.
pub fn accepted_arith_loop<V: Opening>(v: &mut V, point: &[V::E]) -> V::E {
    let acc = v.sample();
    arith_sum(v, point, acc)
}
