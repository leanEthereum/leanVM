//! The pool primitives of `crates/parallel/src/lib.rs` that the NTT driver uses, with permissions for
//! the memory their tasks touch.
//!
//! A buffer's memory is a map of permissions, one `vstd::raw_ptr::PointsTo` per element, keyed by the
//! element's index from an origin pointer ([`owns`]). Only the holder of an element's permission can
//! read or write it, and a permission cannot be duplicated, so tasks that hold disjoint maps cannot race.
//!
//! The trusted specifications are collected under "Trust base" below: the dispatch of the pool
//! ([`for_each_chunk`]), the passage between a slice and the permissions it stands for
//! ([`slice_as_mut_ptr`], [`slice_as_ptr`], [`from_raw_parts_mut`], [`from_raw_parts`]), and the core
//! functions vstd does not specify (`<*mut T>::add`, `<*const T>::cast_mut`, `div_ceil`,
//! `std::ptr::eq`), plus the worker count. [`for_each`], [`SendPtr`], [`RawMut`],
//! [`Chunks`] and [`chunks_mut`] are verified copies/adapters with explicit specifications.
use vstd::prelude::*;
use vstd::raw_ptr::*;

verus! {

broadcast use vstd::raw_ptr::group_raw_ptr_axioms;

// ---------------------------------------------------------------------------------------------
// Permissions
// ---------------------------------------------------------------------------------------------
/// The pointer to element `k` of the buffer at `o`: `o.add(k)`.
pub open spec fn ptr_at<T>(o: *mut T, k: int) -> *mut T {
    ptr_mut_from_data(PtrData::<T> { addr: (o@.addr + k * size_of::<T>()) as usize, ..o@ })
}

/// The elements `lo..lo + len` of the buffer at `o` are initialized, `perms` holds exactly their
/// permissions, and the range does not wrap the address space.
pub open spec fn owns<T>(perms: Map<int, PointsTo<T>>, o: *mut T, lo: int, len: int) -> bool {
    &&& 0 <= lo
    &&& 0 <= len
    &&& o@.addr + (lo + len) * size_of::<T>() <= usize::MAX
    &&& forall|k: int| #[trigger] perms.dom().contains(k) <==> lo <= k < lo + len
    &&& forall|k: int| lo <= k < lo + len ==> (#[trigger] perms[k]).ptr() == ptr_at(o, k) && perms[k].is_init()
}

/// As [`owns`], for a map that may hold more permissions than the range's.
pub open spec fn covers<T>(perms: Map<int, PointsTo<T>>, o: *mut T, lo: int, len: int) -> bool {
    &&& 0 <= lo
    &&& 0 <= len
    &&& o@.addr + (lo + len) * size_of::<T>() <= usize::MAX
    &&& forall|k: int|
        lo <= k < lo + len ==> #[trigger] perms.dom().contains(k) && perms[k].ptr() == ptr_at(o, k) && perms[k].is_init()
}

/// The values of the elements `lo..lo + len`.
pub open spec fn vals<T>(perms: Map<int, PointsTo<T>>, lo: int, len: int) -> Seq<T> {
    Seq::new(len as nat, |j: int| perms[lo + j].value())
}

/// The keys of `perms` whose owner lies in `lo..hi`.
pub open spec fn keys_of<V>(perms: Map<int, V>, owner: spec_fn(int) -> int, lo: int, hi: int) -> Set<int> {
    perms.dom().filter(|k: int| lo <= owner(k) < hi)
}

/// The permissions of the items `lo..hi`, item `owner(k)` holding key `k`.
pub open spec fn claimed<V>(perms: Map<int, V>, owner: spec_fn(int) -> int, lo: int, hi: int) -> Map<int, V> {
    perms.restrict(keys_of(perms, owner, lo, hi))
}

/// Disjoint item ranges cannot receive any of the same element permissions.
pub proof fn lemma_claims_disjoint<V>(perms: Map<int, V>, owner: spec_fn(int) -> int,
    a: int, b: int, c: int, d: int)
    requires a <= b <= c <= d,
    ensures claimed(perms, owner, a, b).dom().disjoint(claimed(perms, owner, c, d).dom()),
{
    assert forall|k: int| claimed(perms, owner, a, b).dom().contains(k)
        implies !claimed(perms, owner, c, d).dom().contains(k) by {}
}

// ---------------------------------------------------------------------------------------------
// Trust base
// ---------------------------------------------------------------------------------------------
/// `p.add(count)` is the pointer `count` elements on.
///
/// Rust also requires the result to stay inside the allocation of `p`. Every call in this crate
/// dereferences the result through the permission of that element (or builds a slice of length
/// at least one there), which puts it inside the allocation.
pub assume_specification<T>[ <*mut T>::add ](p: *mut T, count: usize) -> (q: *mut T)
    requires
        p@.addr + count * size_of::<T>() <= usize::MAX,
    ensures
        q == ptr_at(p, count as int),
;

/// `p.cast_mut()` is the same pointer.
pub assume_specification<T: core::marker::PointeeSized>[ <*const T>::cast_mut ](p: *const T) -> (q: *mut T)
    ensures
        q@ == p@,
;

/// `a.div_ceil(b)` rounds the quotient up.
pub assume_specification[ <usize>::div_ceil ](a: usize, b: usize) -> (r: usize)
    requires
        b > 0,
    ensures
        r == (a + b - 1) / (b as int),
;

/// `std::ptr::eq` compares addresses and metadata (as vstd's `==` on pointers).
pub assume_specification<T: core::marker::PointeeSized>[ core::ptr::eq::<T> ](a: *const T, b: *const T) -> (r: bool)
    ensures
        r == (a@.addr == b@.addr && a@.metadata == b@.metadata),
;

/// A mutable slice is the permission to its elements, at its address, for as long as it is borrowed.
///
/// The permissions come back to the slice when the borrow ends: if the map then still holds them, the
/// slice's new contents are their values. (A caller that kept a permission past the borrow could not
/// prove anything about the slice afterwards; every caller here proves the slice's final contents.)
#[verifier::external_body]
pub fn slice_as_mut_ptr<'a, T>(s: &'a mut [T]) -> (r: (*mut T, Tracked<&'a mut Map<int, PointsTo<T>>>))
    ensures
        owns(*r.1@, r.0, 0, old(s)@.len() as int),
        vals(*r.1@, 0, old(s)@.len() as int) == old(s)@,
        owns(*final(r.1@), r.0, 0, old(s)@.len() as int) ==> final(s)@ == vals(*final(r.1@), 0, old(s)@.len() as int),
{
    (s.as_mut_ptr(), Tracked::assume_new())
}

/// A shared slice is a shared permission to its elements, at its address.
#[verifier::external_body]
pub fn slice_as_ptr<'a, T>(s: &'a [T]) -> (r: (*const T, Tracked<&'a Map<int, PointsTo<T>>>))
    ensures
        owns(*r.1@, r.0 as *mut T, 0, s@.len() as int),
        vals(*r.1@, 0, s@.len() as int) == s@,
{
    (s.as_ptr(), Tracked::assume_new())
}

/// `std::slice::from_raw_parts_mut(ptr, len)`, given the permissions of its elements, which it borrows.
#[verifier::external_body]
pub fn from_raw_parts_mut<'a, T>(
    ptr: *mut T,
    len: usize,
    Ghost(o): Ghost<*mut T>,
    Ghost(lo): Ghost<int>,
    Tracked(perms): Tracked<&'a mut Map<int, PointsTo<T>>>,
) -> (s: &'a mut [T])
    requires
        owns(*old(perms), o, lo, len as int),
        ptr == ptr_at(o, lo),
    ensures
        s@ == vals(*old(perms), lo, len as int),
        owns(*final(perms), o, lo, len as int),
        final(s)@ == vals(*final(perms), lo, len as int),
{
    unsafe { std::slice::from_raw_parts_mut(ptr, len) }
}

/// `std::slice::from_raw_parts(ptr, len)`, given shared permissions of its elements.
#[verifier::external_body]
pub fn from_raw_parts<'a, T>(
    ptr: *const T,
    len: usize,
    Ghost(o): Ghost<*mut T>,
    Ghost(lo): Ghost<int>,
    Tracked(perms): Tracked<&'a Map<int, PointsTo<T>>>,
) -> (s: &'a [T])
    requires
        covers(*perms, o, lo, len as int),
        ptr as *mut T == ptr_at(o, lo),
    ensures
        s@ == vals(*perms, lo, len as int),
{
    unsafe { std::slice::from_raw_parts(ptr, len) }
}

/// Worker count including the dispatcher.
#[verifier::external_body]
pub fn num_threads() -> (r: usize)
    ensures
        r >= 1,
{
    ::parallel::num_threads()
}

/// The pool's dispatch: `f(lo, hi)` runs on disjoint ranges that tile `0..n_tasks`, each exactly once,
/// concurrently, and the call returns after all of them.
///
/// Specification: the permissions `perms` are split by item, key `k` going to item `owner(k)`; a
/// call `f(lo, hi)` receives the permissions of its items and returns them, satisfying `post` for every
/// item of its range. The dispatcher gets back the permissions of every item, each satisfying `post`.
///
/// The body delegates to production's `parallel::for_each_chunk`. Its atomic claim counter,
/// worker lifetime, synchronization and exactly-once behavior are trusted, not verified here.
#[verifier::external_body]
pub fn for_each_chunk<V: Send + Sync, F: Fn(usize, usize, Tracked<Map<int, V>>) -> Tracked<Map<int, V>> + Sync>(
    n_tasks: usize,
    f: F,
    Tracked(perms): Tracked<Map<int, V>>,
    Ghost(owner): Ghost<spec_fn(int) -> int>,
    Ghost(post): Ghost<spec_fn(int, Map<int, V>) -> bool>,
) -> (out: Tracked<Map<int, V>>)
    requires
        forall|k: int| #[trigger] perms.dom().contains(k) ==> 0 <= owner(k) < n_tasks,
        forall|lo: usize, hi: usize|
            lo < hi <= n_tasks ==> #[trigger] f.requires((lo, hi, Tracked(claimed(perms, owner, lo as int, hi as int)))),
        forall|lo: usize, hi: usize, r: Tracked<Map<int, V>>|
            lo < hi <= n_tasks && #[trigger] f.ensures((lo, hi, Tracked(claimed(perms, owner, lo as int, hi as int))), r) ==> {
                &&& r@.dom() == keys_of(perms, owner, lo as int, hi as int)
                &&& forall|i: int| lo <= i < hi ==> #[trigger] post(i, r@.restrict(keys_of(perms, owner, i, i + 1)))
            },
    ensures
        out@.dom() == perms.dom(),
        forall|i: int| 0 <= i < n_tasks ==> #[trigger] post(i, out@.restrict(keys_of(perms, owner, i, i + 1))),
{
    ::parallel::for_each_chunk(n_tasks, |lo, hi| {
        f(lo, hi, Tracked::assume_new());
    });
    Tracked::assume_new()
}

// ---------------------------------------------------------------------------------------------
// Verified copies
// ---------------------------------------------------------------------------------------------
/// The permissions of one item, taken out of the claimed range `lo..hi` and put back.
proof fn lemma_claimed_split<V>(perms: Map<int, V>, owner: spec_fn(int) -> int, lo: int, i: int, hi: int)
    requires
        lo <= i < hi,
    ensures
        keys_of(perms, owner, i, i + 1) <= keys_of(perms, owner, lo, hi),
        claimed(perms, owner, lo, hi).restrict(keys_of(perms, owner, i, i + 1)) == claimed(perms, owner, i, i + 1),
        keys_of(perms, owner, lo, hi) == keys_of(perms, owner, lo, i).union(keys_of(perms, owner, i, hi)),
{
    assert(claimed(perms, owner, lo, hi).restrict(keys_of(perms, owner, i, i + 1)) =~= claimed(perms, owner, i, i + 1));
    assert(keys_of(perms, owner, lo, hi) =~= keys_of(perms, owner, lo, i).union(keys_of(perms, owner, i, hi)));
}

/// `f(i)` for every `i` in `0..n_tasks`, in parallel. `#[inline]` folds the
/// range-to-index adapter into the monomorphized [`for_each_chunk`].
///
/// Specification: as [`for_each_chunk`], one item at a time. `f` takes and returns the permissions of
/// its item (a ghost addition to production's `Fn(usize)`).
#[inline]
pub fn for_each<V: Send + Sync, F: Fn(usize, Tracked<Map<int, V>>) -> Tracked<Map<int, V>> + Sync>(
    n_tasks: usize,
    f: F,
    Tracked(perms): Tracked<Map<int, V>>,
    Ghost(owner): Ghost<spec_fn(int) -> int>,
    Ghost(post): Ghost<spec_fn(int, Map<int, V>) -> bool>,
) -> (out: Tracked<Map<int, V>>)
    requires
        forall|k: int| #[trigger] perms.dom().contains(k) ==> 0 <= owner(k) < n_tasks,
        forall|i: usize| i < n_tasks ==> #[trigger] f.requires((i, Tracked(claimed(perms, owner, i as int, i + 1)))),
        forall|i: usize, r: Tracked<Map<int, V>>|
            i < n_tasks && #[trigger] f.ensures((i, Tracked(claimed(perms, owner, i as int, i + 1))), r) ==> {
                &&& r@.dom() == keys_of(perms, owner, i as int, i + 1)
                &&& post(i as int, r@)
            },
    ensures
        out@.dom() == perms.dom(),
        forall|i: int| 0 <= i < n_tasks ==> #[trigger] post(i, out@.restrict(keys_of(perms, owner, i, i + 1))),
{
    let ghost p0 = perms;
    for_each_chunk(
        n_tasks,
        |start: usize, end: usize, tp: Tracked<Map<int, V>>| -> (r: Tracked<Map<int, V>>)
            requires
                start < end <= n_tasks,
                tp@ == claimed(p0, owner, start as int, end as int),
            ensures
                r@.dom() == keys_of(p0, owner, start as int, end as int),
                forall|i: int| start <= i < end ==> #[trigger] post(i, r@.restrict(keys_of(p0, owner, i, i + 1))),
        {
            // Rewritten from `for i in start..end { f(i); }`: the loop also threads the permissions.
            let tracked mut rest = tp.get();
            let tracked mut done = Map::<int, V>::tracked_empty();
            let mut i = start;
            while i < end
                invariant
                    start <= i <= end <= n_tasks,
                    rest == claimed(p0, owner, i as int, end as int),
                    done.dom() == keys_of(p0, owner, start as int, i as int),
                    forall|j: int| start <= j < i ==> #[trigger] post(j, done.restrict(keys_of(p0, owner, j, j + 1))),
                    forall|i: usize| i < n_tasks ==> #[trigger] f.requires((i, Tracked(claimed(p0, owner, i as int, i + 1)))),
                    forall|i: usize, r: Tracked<Map<int, V>>|
                        i < n_tasks && #[trigger] f.ensures((i, Tracked(claimed(p0, owner, i as int, i + 1))), r) ==> {
                            &&& r@.dom() == keys_of(p0, owner, i as int, i + 1)
                            &&& post(i as int, r@)
                        },
                decreases end - i,
            {
                proof {
                    lemma_claimed_split(p0, owner, i as int, i as int, end as int);
                    lemma_claimed_split(p0, owner, start as int, i as int, i + 1);
                }
                let tracked one = rest.tracked_remove_keys(keys_of(p0, owner, i as int, i + 1));
                proof {
                    assert(one == claimed(p0, owner, i as int, i + 1));
                    assert(rest =~= claimed(p0, owner, i + 1, end as int));
                }
                let Tracked(r) = f(i, Tracked(one));
                let ghost old_done = done;
                let ghost rv = r;
                proof {
                    done.tracked_union_prefer_right(r);
                    assert(done.dom() =~= keys_of(p0, owner, start as int, i + 1));
                    assert forall|j: int| start <= j < i + 1 implies #[trigger] post(j, done.restrict(keys_of(p0, owner, j, j + 1))) by {
                        if j < i {
                            assert(done.restrict(keys_of(p0, owner, j, j + 1)) =~= old_done.restrict(keys_of(p0, owner, j, j + 1)));
                        } else {
                            assert(done.restrict(keys_of(p0, owner, j, j + 1)) =~= rv);
                        }
                    }
                }
                i += 1;
            }
            Tracked(done)
        },
        Tracked(perms),
        Ghost(owner),
        Ghost(post),
    )
}

/// A base `*mut` that can cross into the task closures. Sound only because
/// callers partition the allocation by item index; every dereference site
/// restates that.
///
/// The `Clone`/`Copy` derives are kept; the `Debug` derive and the `Send`/`Sync` impls are outside
/// `verus!` below.
#[derive(Clone, Copy)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct SendPtr<T>(pub *mut T);

impl<T> SendPtr<T> {
    /// Offset the base by `n` elements.
    ///
    /// # Safety
    /// `n` stays inside the allocation, and any write targets a slot no
    /// concurrent task touches.
    ///
    /// Verified: the address does not wrap, which the caller shows with a permission covering element `n`.
    #[inline]
    pub const unsafe fn add(&self, n: usize) -> (r: *mut T)
        requires
            self.0@.addr + n * size_of::<T>() <= usize::MAX,
        ensures
            r == ptr_at(self.0, n as int),
    {
        // SAFETY: the caller keeps `n` inside the allocation.
        unsafe { self.0.add(n) }
    }

    /// Rebuild the `len`-element slice at element offset `off`.
    ///
    /// # Safety
    /// `off`/`len` are in bounds and disjoint from every other concurrent task's
    /// slice, and the underlying buffer outlives `'a`.
    ///
    /// Verified: the caller lends the permissions of exactly the elements `off..off + len` for `'a`
    /// (a ghost argument), which makes the slice in bounds and exclusive.
    #[inline]
    pub unsafe fn slice<'a>(&self, off: usize, len: usize, Tracked(perms): Tracked<&'a mut Map<int, PointsTo<T>>>) -> (s: &'a mut [T])
        requires
            owns(*old(perms), self.0, off as int, len as int),
        ensures
            s@ == vals(*old(perms), off as int, len as int),
            owns(*final(perms), self.0, off as int, len as int),
            final(s)@ == vals(*final(perms), off as int, len as int),
    {
        proof {
            lemma_mul_le(off as int, (off + len) as int, size_of::<T>() as int);
        }
        // SAFETY: the caller guarantees `off..off + len` is in bounds, borrowed by no other task, and alive for `'a`.
        unsafe { from_raw_parts_mut(self.0.add(off), len, Ghost(self.0), Ghost(off as int), Tracked(perms)) }
    }
}

/// A mutable slice in raw parts, its address and length; its permissions travel beside it as a ghost
/// argument.
///
/// Not in production: the verified driver passes its buffer this way where production passes
/// `&mut [F64]`, because the in-place message is that very address, and Verus does not relate the
/// pointers of two `as_mut_ptr` calls on one slice. `len` and `as_mut_ptr` keep the call sites' text.
#[derive(Clone, Copy)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct RawMut<T> {
    pub ptr: *mut T,
    pub len: usize,
}

impl<T> RawMut<T> {
    /// The slice's raw parts, and the permissions it lends for `'a`.
    pub fn new<'a>(data: &'a mut [T]) -> (r: (Self, Tracked<&'a mut Map<int, PointsTo<T>>>))
        ensures
            r.0.len == old(data)@.len(),
            owns(*r.1@, r.0.ptr, 0, old(data)@.len() as int),
            vals(*r.1@, 0, old(data)@.len() as int) == old(data)@,
            owns(*final(r.1@), r.0.ptr, 0, old(data)@.len() as int) ==> final(data)@ == vals(*final(r.1@), 0, old(data)@.len() as int),
    {
        let len = data.len();
        let (ptr, perms) = slice_as_mut_ptr(data);
        (Self { ptr, len }, perms)
    }

    pub fn len(&self) -> (r: usize)
        ensures
            r == self.len,
    {
        self.len
    }

    pub fn as_mut_ptr(&self) -> (r: *mut T)
        ensures
            r == self.ptr,
    {
        self.ptr
    }

    /// The slice again, borrowing its permissions for `'a`.
    pub fn as_mut_slice<'a>(&self, Tracked(perms): Tracked<&'a mut Map<int, PointsTo<T>>>) -> (s: &'a mut [T])
        requires
            owns(*old(perms), self.ptr, 0, self.len as int),
        ensures
            s@ == vals(*old(perms), 0, self.len as int),
            owns(*final(perms), self.ptr, 0, self.len as int),
            final(s)@ == vals(*final(perms), 0, self.len as int),
    {
        proof {
            assert(ptr_at(self.ptr, 0) == self.ptr);
        }
        from_raw_parts_mut(self.ptr, self.len, Ghost(self.ptr), Ghost(0), Tracked(perms))
    }
}

/// A `chunks_mut` view that can be handed to tasks: `chunk(i)` is item `i`'s
/// slice. Composes to any number of buffers, which the zip-based helpers do not:
/// a kernel writing four tables at two different widths builds one of these per
/// table and indexes them all by the same item.
#[derive(Clone, Copy)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct Chunks<T> {
    pub base: SendPtr<T>,
    pub width: usize,
    pub len: usize,
}

/// The chunk that element `k` falls in.
pub open spec fn chunk_of(width: nat) -> spec_fn(int) -> int {
    |k: int| k / (width as int)
}

/// The length of chunk `i` of a `len`-element buffer cut every `width` elements.
pub open spec fn chunk_len(len: nat, width: nat, i: int) -> int {
    if i * width + width <= len {
        width as int
    } else {
        len - i * width
    }
}

impl<T> Chunks<T> {
    /// View `data` as `len.div_ceil(width)` chunks of `width` (the last shorter).
    ///
    /// Rewritten: the `assert!` is a precondition, and the view comes with the permissions of `data`
    /// (production's `data.as_mut_ptr()` is [`slice_as_mut_ptr`]), which `data` lends for their lifetime.
    pub fn new<'a>(data: &'a mut [T], width: usize) -> (r: (Self, Tracked<&'a mut Map<int, PointsTo<T>>>))
        requires
            width > 0,
        ensures
            r.0.width == width,
            r.0.len == old(data)@.len(),
            owns(*r.1@, r.0.base.0, 0, old(data)@.len() as int),
            vals(*r.1@, 0, old(data)@.len() as int) == old(data)@,
            owns(*final(r.1@), r.0.base.0, 0, old(data)@.len() as int) ==> final(data)@ == vals(*final(r.1@), 0, old(data)@.len() as int),
    {
        // Rewritten: the length is read before the slice lends its permissions.
        let len = data.len();
        let (ptr, perms) = slice_as_mut_ptr(data);
        (Self { base: SendPtr(ptr), width, len }, perms)
    }

    /// Number of chunks.
    pub const fn count(&self) -> (r: usize)
        requires
            self.width > 0,
        ensures
            r == (self.len + self.width - 1) / (self.width as int),
    {
        self.len.div_ceil(self.width)
    }

    /// Chunk `i`.
    ///
    /// # Safety
    /// `i < self.count()`, no other live borrow covers chunk `i`, and the
    /// underlying buffer outlives `'a`. Calling this once per `i` inside a
    /// [`for_each`] body satisfies all three.
    ///
    /// Verified: the caller lends the permissions of chunk `i` for `'a` (a ghost argument); the
    /// `debug_assert!` is proven.
    #[inline]
    pub unsafe fn get<'a>(&self, i: usize, Tracked(perms): Tracked<&'a mut Map<int, PointsTo<T>>>) -> (s: &'a mut [T])
        requires
            self.width > 0,
            i < (self.len + self.width - 1) / (self.width as int),
            owns(*old(perms), self.base.0, i * self.width, chunk_len(self.len as nat, self.width as nat, i as int)),
        ensures
            s@ == vals(*old(perms), i * self.width, chunk_len(self.len as nat, self.width as nat, i as int)),
            owns(*final(perms), self.base.0, i * self.width, chunk_len(self.len as nat, self.width as nat, i as int)),
            final(s)@ == vals(*final(perms), i * self.width, chunk_len(self.len as nat, self.width as nat, i as int)),
    {
        proof {
            lemma_chunk_start(self.len as nat, self.width as nat, i as int);
        }
        let start = i * self.width;
        assert(start < self.len);
        // SAFETY: `i < count()` puts `start` below `len`, so `start..start + min(width, len - start)` lies in
        // the slice `new` took; the caller guarantees no other borrow of it and that it outlives `'a`.
        unsafe { self.base.slice(start, self.width.min(self.len - start), Tracked(perms)) }
    }
}

/// A chunk below the count starts inside the buffer.
proof fn lemma_chunk_start(len: nat, width: nat, i: int)
    requires
        width > 0,
        0 <= i < (len + width - 1) / (width as int),
    ensures
        i * width < len,
        0 < chunk_len(len, width, i) <= width,
        i * width + chunk_len(len, width, i) <= len,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod((len + width - 1) as int, width as int);
    vstd::arithmetic::div_mod::lemma_mod_bound((len + width - 1) as int, width as int);
    let q = (len + width - 1) / (width as int);
    assert(i * width + width <= q * width) by (nonlinear_arith)
        requires
            i + 1 <= q,
            width > 0,
    ;
}

/// The permissions of a sub-range of an owned range, and their values.
pub proof fn lemma_restrict_owns<T>(p: Map<int, PointsTo<T>>, o: *mut T, total: int, keys: Set<int>, lo: int, n: int)
    requires
        owns(p, o, 0, total),
        0 <= lo,
        0 <= n,
        lo + n <= total,
        forall|k: int| #[trigger] keys.contains(k) <==> lo <= k < lo + n,
    ensures
        owns(p.restrict(keys), o, lo, n),
        vals(p.restrict(keys), lo, n) == vals(p, 0, total).subrange(lo, lo + n),
{
    lemma_mul_le(lo + n, total, size_of::<T>() as int);
    assert forall|k: int| #[trigger] p.restrict(keys).dom().contains(k) <==> lo <= k < lo + n by {}
    assert(vals(p.restrict(keys), lo, n) =~= vals(p, 0, total).subrange(lo, lo + n));
}

/// `a <= b` scales by a non-negative factor.
pub proof fn lemma_mul_le(a: int, b: int, c: int)
    requires
        a <= b,
        0 <= c,
    ensures
        a * c <= b * c,
{
    assert(a * c <= b * c) by (nonlinear_arith)
        requires
            a <= b,
            0 <= c,
    ;
}

/// An index below `len` lies in a chunk below the count.
proof fn lemma_chunk_index(k: int, len: int, w: int)
    requires
        0 <= k < len,
        w > 0,
    ensures
        0 <= k / w < (len + w - 1) / w,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(k, w);
    vstd::arithmetic::div_mod::lemma_div_pos_is_pos(k, w);
    let q = k / w;
    vstd::arithmetic::div_mod::lemma_mod_bound(k, w);
    assert((q + 1) * w <= len + w - 1) by (nonlinear_arith)
        requires
            k == w * q + k % w,
            0 <= k % w < w,
            k < len,
    ;
    vstd::arithmetic::div_mod::lemma_div_is_ordered((q + 1) * w, len + w - 1, w);
    vstd::arithmetic::div_mod::lemma_div_multiples_vanish(q + 1, w);
    assert((q + 1) * w == w * (q + 1)) by (nonlinear_arith);
}

/// Parallel `data.chunks_mut(chunk).enumerate().for_each(f)`; the final chunk may
/// be shorter.
///
/// Specification: `f(i, chunk_i)` runs once for every chunk, concurrently; `post(i, old, new)` holds of
/// every chunk's contents before and after its call, given that it holds of every call of `f`.
/// Rewritten: `chunk > 0` is a precondition (production's `Chunks::new` asserts it), and the
/// permissions pass through [`for_each`] (ghost additions).
pub fn chunks_mut<T: Send + Sync, F>(data: &mut [T], chunk: usize, f: F, Ghost(post): Ghost<spec_fn(int, Seq<T>, Seq<T>) -> bool>)
where
    F: Fn(usize, &mut [T]) + Sync,
    requires
        chunk > 0,
        forall|i: usize, s: &mut [T]|
            i < (old(data)@.len() + chunk - 1) / (chunk as int) && s@ == old(data)@.subrange(i * chunk, i * chunk + chunk_len(old(data)@.len(), chunk as nat, i as int))
                ==> #[trigger] f.requires((i, s)),
        forall|i: usize, s: &mut [T]|
            #[trigger] f.ensures((i, s), ()) ==> final(s)@.len() == s@.len() && post(i as int, s@, final(s)@),
    ensures
        final(data)@.len() == old(data)@.len(),
        forall|i: int|
            0 <= i < (old(data)@.len() + chunk - 1) / (chunk as int) ==> #[trigger] post(
                i,
                old(data)@.subrange(i * chunk, i * chunk + chunk_len(old(data)@.len(), chunk as nat, i)),
                final(data)@.subrange(i * chunk, i * chunk + chunk_len(old(data)@.len(), chunk as nat, i)),
            ),
{
    let ghost d0 = data@;
    let ghost len = d0.len() as int;
    let (view, Tracked(perms)) = Chunks::new(data, chunk);
    let ghost base = view.base;
    let ghost owner = chunk_of(chunk as nat);
    let ghost item_post = |i: int, m: Map<int, PointsTo<T>>|
        {
            let lo = i * chunk;
            let n = chunk_len(d0.len(), chunk as nat, i);
            owns(m, base.0, lo, n) && post(i, d0.subrange(lo, lo + n), vals(m, lo, n))
        };
    let ghost pre = *perms;
    let tracked all = perms.tracked_remove_keys(perms.dom());
    let ghost p0 = all;
    let count = view.count();
    proof {
        assert(p0 =~= pre);
        assert forall|k: int| #[trigger] p0.dom().contains(k) implies 0 <= owner(k) < count by {
            lemma_chunk_index(k, len, chunk as int);
        }
        assert forall|i: usize, k: int| i < count implies (#[trigger] keys_of(p0, owner, i as int, i + 1).contains(k) <==> i
            * chunk <= k < i * chunk + chunk_len(d0.len(), chunk as nat, i as int)) by {
            lemma_chunk_start(d0.len(), chunk as nat, i as int);
            lemma_chunk_keys(k, i as int, chunk as int);
        }
    }
    assert(owns(p0, base.0, 0, len));
    assert(vals(p0, 0, len) == d0);
    assert(count == (len + chunk - 1) / (chunk as int));
    assert(view.base == base && view.width == chunk && view.len == len);
    assert(forall|i: usize, s: &mut [T]|
        i < count && s@ == d0.subrange(i * chunk, i * chunk + chunk_len(d0.len(), chunk as nat, i as int))
            ==> #[trigger] f.requires((i, s)));
    assert(forall|i: usize, s: &mut [T]|
        #[trigger] f.ensures((i, s), ()) ==> final(s)@.len() == s@.len() && post(i as int, s@, final(s)@));
    let Tracked(out) = for_each(
        count,
        |i: usize, tp: Tracked<Map<int, PointsTo<T>>>| -> (r: Tracked<Map<int, PointsTo<T>>>)
            requires
                i < count,
                tp@ == claimed(p0, owner, i as int, i + 1),
                chunk > 0,
                view.base == base,
                view.width == chunk,
                view.len == len,
                count == (len + chunk - 1) / (chunk as int),
                owns(p0, base.0, 0, len),
                vals(p0, 0, len) == d0,
                forall|i: usize, k: int| i < count ==> (#[trigger] keys_of(p0, owner, i as int, i + 1).contains(k) <==> i
                    * chunk <= k < i * chunk + chunk_len(d0.len(), chunk as nat, i as int)),
                forall|i: usize, s: &mut [T]|
                    i < count && s@ == d0.subrange(i * chunk, i * chunk + chunk_len(d0.len(), chunk as nat, i as int))
                        ==> #[trigger] f.requires((i, s)),
                forall|i: usize, s: &mut [T]|
                    #[trigger] f.ensures((i, s), ()) ==> final(s)@.len() == s@.len() && post(i as int, s@, final(s)@),
            ensures
                r@.dom() == keys_of(p0, owner, i as int, i + 1),
                item_post(i as int, r@),
        {
            let tracked mut m = tp.get();
            let ghost lo = i * chunk;
            let ghost n = chunk_len(d0.len(), chunk as nat, i as int);
            proof {
                lemma_chunk_start(d0.len(), chunk as nat, i as int);
                lemma_restrict_owns(p0, base.0, len, keys_of(p0, owner, i as int, i + 1), lo, n);
            }
            // SAFETY: distinct `i` give disjoint in-bounds chunks, and `data` stays
            // borrowed for the whole dispatch.
            f(i, unsafe { view.get(i, Tracked(&mut m)) });
            proof {
                assert(m.dom() =~= keys_of(p0, owner, i as int, i + 1));
            }
            Tracked(m)
        },
        Tracked(all),
        Ghost(owner),
        Ghost(item_post),
    );
    proof {
        perms.tracked_union_prefer_right(out);
        assert(perms.dom() =~= out.dom());
        assert forall|k: int| 0 <= k < len implies (#[trigger] perms[k]).ptr() == ptr_at(base.0, k) && perms[k].is_init() by {
            let i = owner(k);
            lemma_chunk_index(k, len, chunk as int);
            assert(p0.dom().contains(k));
            let iu = i as usize;
            assert(keys_of(p0, owner, iu as int, iu + 1).contains(k));
            let mi = out.restrict(keys_of(p0, owner, i, i + 1));
            assert(item_post(i, mi));
            assert(mi[k] == out[k]);
            assert(perms[k] == out[k]);
        }
        assert(owns(*perms, base.0, 0, len));
        assert forall|i: int| 0 <= i < count implies #[trigger] post(
            i,
            d0.subrange(i * chunk, i * chunk + chunk_len(d0.len(), chunk as nat, i)),
            vals(*perms, 0, len).subrange(i * chunk, i * chunk + chunk_len(d0.len(), chunk as nat, i)),
        ) by {
            let lo = i * chunk;
            let n = chunk_len(d0.len(), chunk as nat, i);
            let mi = out.restrict(keys_of(p0, owner, i, i + 1));
            assert(item_post(i, mi));
            lemma_chunk_start(d0.len(), chunk as nat, i);
            assert(vals(mi, lo, n) =~= vals(*perms, 0, len).subrange(lo, lo + n));
        }
    }
}

/// Key `k` falls in chunk `i` exactly when it lies in `i * w .. (i + 1) * w`.
pub proof fn lemma_chunk_keys(k: int, i: int, w: int)
    requires
        w > 0,
    ensures
        (i <= k / w < i + 1) <==> (i * w <= k < i * w + w),
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(k, w);
    vstd::arithmetic::div_mod::lemma_mod_bound(k, w);
    if i <= k / w < i + 1 {
        assert(k / w == i);
    } else if i * w <= k < i * w + w {
        vstd::arithmetic::div_mod::lemma_div_is_ordered(i * w, k, w);
        vstd::arithmetic::div_mod::lemma_div_multiples_vanish(i, w);
        assert(k / w <= i) by {
            vstd::arithmetic::div_mod::lemma_div_is_ordered(k, i * w + w - 1, w);
            assert(i * w + w - 1 == i * w + (w - 1));
            vstd::arithmetic::div_mod::lemma_div_multiples_vanish_fancy(i, w - 1, w);
        }
    }
}

} // verus!

impl<T> core::fmt::Debug for SendPtr<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_tuple("SendPtr").field(&self.0).finish()
    }
}

// SAFETY: `SendPtr` grants no access by itself; every dereference is inside an
// `unsafe` block whose comment establishes that the range being touched belongs
// to exactly one task.
unsafe impl<T> Send for SendPtr<T> {}
// SAFETY: sharing the pointer value is as harmless as sending it, for the reason above.
unsafe impl<T> Sync for SendPtr<T> {}
