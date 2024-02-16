use builtin::*;
use vstd::prelude::{verus, arbitrary};

verus! {

/// `Seq<A>` is a sequence type for specifications.
/// To use a "sequence" in compiled code, use an `exec` type like [`vec::Vec`](crate::vec::Vec)
/// that has `Seq<A>` as its specification type.
///
/// An object `seq: Seq<A>` has a length, given by [`seq.len()`](Seq::len),
/// and a value at each `i` for `0 <= i < seq.len()`, given by [`seq[i]`](Seq::index).
///
/// Sequences can be constructed in a few different ways:
///  * [`Seq::empty`] construct an empty sequence (`len() == 0`)
///  * [`Seq::new`] construct a sequence of a given length, initialized according
///     to a given function mapping indices `i` to values `A`.
///  * The [`seq!`] macro, to construct small sequences of a fixed size (analagous to the
///     [`std::vec!`] macro).
///  * By manipulating an existing sequence with [`Seq::push`], [`Seq::update`],
///    or [`Seq::add`].
///
/// To prove that two sequences are equal, it is usually easiest to use the
/// extensional equality operator `=~=`.

#[verifier::accept_recursive_types(A)]
#[verifier::ext_equal]
pub enum Seq<A> {
    Nil,
    Cons(A, Box<Seq<A>>),
}

impl<A> Seq<A> {
    /// An empty sequence (i.e., a sequence of length 0).

    pub closed spec fn empty() -> Seq<A> {
        Seq::Nil
    }

    /// Construct a sequence `s` of length `len` where entry `s[i]` is given by `f(i)`.

    pub closed spec fn new(len: nat, f: spec_fn(int) -> A) -> Seq<A>
        decreases len
    {
        if len == 0 { Seq::Nil }
        else {
            Self::new((len-1) as nat, f).push(f(len-1))
        }
    }

    /// The length of a sequence.

    pub closed spec fn len(self) -> nat
        decreases self
    {
        match self {
            Seq::Nil => 0,
            Seq::Cons(_, l) => 1 + l.len(),
        }
    }

    /// Gets the value at the given index `i`.
    ///
    /// If `i` is not in the range `[0, self.len())`, then the resulting value
    /// is arbitrary().

    pub closed spec fn index(self, i: int) -> A
        recommends 0 <= i < self.len()
        decreases self
    {
        match self {
            Seq::Nil => arbitrary(),
            Seq::Cons(a, l) => if i == 0 { a } else { l.index(i-1) }
        }
    }

    /// `[]` operator, synonymous with `index`

    #[verifier(inline)]
    pub open spec fn spec_index(self, i: int) -> A
        recommends 0 <= i < self.len()
    {
        self.index(i)
    }

    /// Appends the value `a` to the end of the sequence.
    /// This always increases the length of the sequence by 1.
    ///
    /// ## Example
    ///
    /// ```rust
    /// proof fn push_test() {
    ///     assert(seq![10, 11, 12].push(13) =~= seq![10, 11, 12, 13]);
    /// }
    /// ```

    pub closed spec fn push(self, a: A) -> Seq<A>
        decreases self
    {
        match self {
            Seq::Nil => Seq::Cons(a, Box::new(Seq::Nil)),
            Seq::Cons(x, l) => Seq::Cons(x, Box::new(l.push(a))),
        }
    }

    /// Updates the sequence at the given index, replacing the element with the given
    /// value, and leaves all other entries unchanged.
    ///
    /// ## Example
    ///
    /// ```rust
    /// proof fn update_test() {
    ///     let s = seq![10, 11, 12, 13, 14];
    ///     let t = s.update(2, -5);
    ///     assert(t =~= seq![10, 11, -5, 13, 14]);
    /// }
    /// ```

    pub closed spec fn update(self, i: int, a: A) -> Seq<A>
        recommends 0 <= i < self.len()
        decreases self
    {
        if !(0 <= i < self.len()) {
            // makes some additional lemmas hold for out-of-bounds updates
            self
        } else {
            match self {
                Seq::Nil => Seq::Nil,
                Seq::Cons(x, l) =>
                if i == 0 {
                    Seq::Cons(a, l)
                } else {
                    Seq::Cons(x, Box::new(l.update(i-1, a)))
                }
            }
        }
    }

    /// DEPRECATED: use =~= or =~~= instead.
    /// Returns `true` if the two sequences are pointwise equal, i.e.,
    /// they have the same length and the corresponding values are equal
    /// at each index. This is equivalent to the sequences being actually equal
    /// by [`axiom_seq_ext_equal`].
    ///
    /// To prove that two sequences are equal via extensionality, it may be easier
    /// to use the general-purpose `=~=` or `=~~=` or
    /// to use the [`assert_seqs_equal!`](crate::seq_lib::assert_seqs_equal) macro,
    /// rather than using `.ext_equal` directly.

    #[deprecated = "use =~= or =~~= instead"]
    pub open spec fn ext_equal(self, s2: Seq<A>) -> bool {
        self =~= s2
    }

    /// Returns a sequence for the given subrange.
    ///
    /// ## Example
    ///
    /// ```rust
    /// proof fn subrange_test() {
    ///     let s = seq![10, 11, 12, 13, 14];
    ///     //                  ^-------^
    ///     //          0   1   2   3   4   5
    ///     let sub = s.subrange(2, 4);
    ///     assert(sub =~= seq![12, 13]);
    /// }
    /// ```

    pub closed spec fn subrange(self, start_inclusive: int, end_exclusive: int) -> Seq<A>
        recommends 0 <= start_inclusive <= end_exclusive <= self.len()
        decreases start_inclusive, end_exclusive-start_inclusive
    {
        match self {
            Seq::Nil => Seq::Nil,
            Seq::Cons(a, l) =>
            // skip elements until start_inclusive becomes 0
            if start_inclusive > 0 {
                l.subrange(start_inclusive-1, end_exclusive-1)
            } else {
                if end_exclusive <= 0 {
                    Seq::Nil
                } else {
                    Seq::Cons(a, Box::new(l.subrange(start_inclusive, end_exclusive-1)))
                }
            }
        }
    }

    /// Returns a sequence containing only the first n elements of the original sequence

    #[verifier(inline)]
    pub open spec fn take(self, n: int) -> Seq<A>{
        self.subrange(0,n)
    }

    /// Returns a sequence without the first n elements of the original sequence

    #[verifier(inline)]
    pub open spec fn skip(self, n: int) -> Seq<A>{
        self.subrange(n,self.len() as int)
    }

    /// Concatenates the sequences.
    ///
    /// ## Example
    ///
    /// ```rust
    /// proof fn add_test() {
    ///     assert(seq![10int, 11].add(seq![12, 13, 14])
    ///             =~= seq![10, 11, 12, 13, 14]);
    /// }
    /// ```

    pub closed spec fn add(self, rhs: Seq<A>) -> Seq<A>
        decreases self
    {
        match self {
            Seq::Nil => rhs,
            Seq::Cons(a, l) => Seq::Cons(a, Box::new(l.add(rhs))),
        }
    }

    /// `+` operator, synonymous with `add`

    #[verifier(inline)]
    pub open spec fn spec_add(self, rhs: Seq<A>) -> Seq<A> {
        self.add(rhs)
    }

    /// Returns the last element of the sequence.

    pub open spec fn last(self) -> A
        recommends 0 < self.len()
    {
        self[self.len() as int - 1]
    }

    /// Returns the first element of the sequence.

    pub open spec fn first(self) -> A
        recommends 0 < self.len()
    {
        self[0]
    }
}

proof fn seq_len_0_empty<A>(s: Seq<A>)
    requires s.len() == 0
    ensures s == Seq::<A>::empty()
{
    match s {
        Seq::Nil => {}
        Seq::Cons(_, l) => {
            assert(s.len() == 1 + l.len());
            assert(s.len() > 0);
        }
    }
}

// Trusted axioms

proof fn lemma_seq_index_decreases<A>(s: Seq<A>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        #[trigger](decreases_to!(s => s[i])),
    decreases i
{
    match s {
        Seq::Nil => { assert(false); }
        Seq::Cons(a, l) => {
            if i == 0 {}
            else {
                lemma_seq_index_decreases(*l, i-1);
            }
        }
    }
}

proof fn seq_index_out_of_bounds<A>(s: Seq<A>, i: int)
    requires !(0 <= i < s.len())
    ensures s[i] == arbitrary::<A>()
    decreases s
{
    match s {
        Seq::Nil => {
        }
        Seq::Cons(_, l) => {
            seq_index_out_of_bounds(*l, i-1);
            if i < 0 {
                assert(i-1 < 0);
            } else {
                assert(i-1 >= l.len());
            }
            assert(s[i] == l[i-1]);
        }
    }
}

#[verifier(external_body)]
// #[verifier(broadcast_forall)]
pub proof fn axiom_seq_index_decreases<A>(s: Seq<A>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        #[trigger](decreases_to!(s => s[i])),
{
}

proof fn lemma_seq_empty<A>()
    ensures
        #[trigger] Seq::<A>::empty().len() == 0,
{
}

#[verifier(external_body)]
// #[verifier(broadcast_forall)]
pub proof fn axiom_seq_empty<A>()
    ensures
        #[trigger] Seq::<A>::empty().len() == 0,
{
}

proof fn lemma_seq_new_len<A>(len: nat, f: spec_fn(int) -> A)
    ensures
        #[trigger] Seq::new(len, f).len() == len,
    decreases len
{
    if len == 0 {}
    else {
        lemma_seq_new_len((len-1) as nat, f);
        lemma_seq_push_len(Seq::new((len-1) as nat, f), f(len-1));
    }
}

#[verifier(external_body)]
// #[verifier(broadcast_forall)]
pub proof fn axiom_seq_new_len<A>(len: nat, f: spec_fn(int) -> A)
    ensures
        #[trigger] Seq::new(len, f).len() == len,
{
}

proof fn lemma_seq_new_index<A>(len: nat, f: spec_fn(int) -> A, i: int)
    requires
        0 <= i < len,
    ensures
        Seq::new(len, f)[i] == f(i),
    decreases len
{
    lemma_seq_new_len(len, f);
    if len == 0 {
        assert(false);
    } else {
        lemma_seq_new_len((len-1) as nat, f);
        if i == len-1 {
            lemma_seq_push_index_same(Seq::new((len-1) as nat, f), f(len-1), len-1);
            assert(Seq::new(len, f)[i] == f(i));
            return;
        }
        lemma_seq_new_index((len-1) as nat, f, i);
        assert(i < len-1);
        lemma_seq_push_index_different(Seq::new((len-1) as nat, f), f(len-1), i);
    }
}

#[verifier(external_body)]
// #[verifier(broadcast_forall)]
pub proof fn axiom_seq_new_index<A>(len: nat, f: spec_fn(int) -> A, i: int)
    requires
        0 <= i < len,
    ensures
        Seq::new(len, f)[i] == f(i),
{
}

proof fn lemma_seq_push_len<A>(s: Seq<A>, a: A)
    ensures
        #[trigger] s.push(a).len() == s.len() + 1,
    decreases s
{
    match s {
        Seq::Nil => {
            assert(s.len() == 0);
        }
        Seq::Cons(_, l) => {
            lemma_seq_push_len(*l, a);
        }
    }
}

#[verifier(external_body)]
// #[verifier(broadcast_forall)]
pub proof fn axiom_seq_push_len<A>(s: Seq<A>, a: A)
    ensures
        #[trigger] s.push(a).len() == s.len() + 1,
{
}

proof fn lemma_seq_push_index_same<A>(s: Seq<A>, a: A, i: int)
    requires
        i == s.len(),
    ensures
        #[trigger] s.push(a)[i] == a,
    decreases s
{
    match s {
        Seq::Nil => {}
        Seq::Cons(x, l) => {
            lemma_seq_push_index_same(*l, a, i-1);
            lemma_seq_push_len(*l, a);
        }
    }
}

#[verifier(external_body)]
// #[verifier(broadcast_forall)]
pub proof fn axiom_seq_push_index_same<A>(s: Seq<A>, a: A, i: int)
    requires
        i == s.len(),
    ensures
        #[trigger] s.push(a)[i] == a,
{
}

proof fn lemma_seq_push_index_different<A>(s: Seq<A>, a: A, i: int)
    // 0 <= i not required
    requires
        i < s.len(),
    ensures
        s.push(a)[i] == s[i],
    decreases s
{
    match s {
        Seq::Nil => {
            seq_index_out_of_bounds(s.push(a), i);
        }
        Seq::Cons(x, l) => {
            lemma_seq_push_index_different(*l, a, i-1);
        }
    }
}

#[verifier(external_body)]
// #[verifier(broadcast_forall)]
pub proof fn axiom_seq_push_index_different<A>(s: Seq<A>, a: A, i: int)
    requires
        0 <= i < s.len(),
    ensures
        s.push(a)[i] == s[i],
{
}

proof fn lemma_seq_update_len<A>(s: Seq<A>, i: int, a: A)
    // precondition is not required
    // requires
    //     0 <= i < s.len(),
    ensures
        #[trigger] s.update(i, a).len() == s.len(),
    decreases s
{
    if !(0 <= i < s.len()) {
        return;
    }
    match s {
        Seq::Nil => {}
        Seq::Cons(x, l) => {
            if i == 0 {}
            else {
                lemma_seq_update_len(*l, i-1, a);
            }
        }
    }
}

#[verifier(external_body)]
// #[verifier(broadcast_forall)]
pub proof fn axiom_seq_update_len<A>(s: Seq<A>, i: int, a: A)
    requires
        0 <= i < s.len(),
    ensures
        #[trigger] s.update(i, a).len() == s.len(),
{
}

proof fn lemma_seq_update_same<A>(s: Seq<A>, i: int, a: A)
    requires
        0 <= i < s.len(),
    ensures
        #[trigger] s.update(i, a)[i] == a,
    decreases s
{
    match s {
        Seq::Nil => {}
        Seq::Cons(x, l) => {
            if i == 0 {}
            else {
                lemma_seq_update_same(*l, i-1, a);
            }
        }
    }
}

#[verifier(external_body)]
// #[verifier(broadcast_forall)]
pub proof fn axiom_seq_update_same<A>(s: Seq<A>, i: int, a: A)
    requires
        0 <= i < s.len(),
    ensures
        #[trigger] s.update(i, a)[i] == a,
{
}

proof fn lemma_seq_update_different<A>(s: Seq<A>, i1: int, i2: int, a: A)
    requires
        // these conditions are not required
        // 0 <= i1 < s.len(),
        // 0 <= i2 < s.len(),
        i1 != i2,
    ensures
        s.update(i2, a)[i1] == s[i1],
    decreases s
{
    match s {
        Seq::Nil => {
        }
        Seq::Cons(x, l) => {
            if i2 == 0 {
            } else {
                lemma_seq_update_different(*l, i1-1, i2-1, a);
            }
        }
    }
}

#[verifier(external_body)]
// #[verifier(broadcast_forall)]
pub proof fn axiom_seq_update_different<A>(s: Seq<A>, i1: int, i2: int, a: A)
    requires
        0 <= i1 < s.len(),
        0 <= i2 < s.len(),
    ensures
        s.update(i2, a)[i1] == s[i1],
{
}

proof fn seq_extensional_equality_index<A>(s1: Seq<A>, s2: Seq<A>)
    requires s1.len() == s2.len(),
             forall |i: int| 0 <= i < s1.len() ==> s1[i] == s2[i],
    ensures s1 == s2
    decreases s1
{
    match s1 {
        Seq::Nil => {
            seq_len_0_empty(s2);
        }
        Seq::Cons(a, l1) => {
            assert(s1.len() == 1 + l1.len());
            match s2 {
                Seq::Nil => {},
                Seq::Cons(b, l2) => {
                    assert(s2.len() == 1 + l2.len());
                    assert(s1[0] == a);
                    assert(s2[0] == b);
                    assert forall |i: int| 0 <= i < l1.len() implies l1[i] == l2[i] by {
                        assert(l1[i] == s1[i+1]);
                        assert(l2[i] == s2[i+1]);
                    }
                    seq_extensional_equality_index(*l1, *l2);
                }
            }
        }
    }
}

proof fn lemma_seq_ext_equal<A>(s1: Seq<A>, s2: Seq<A>)
    ensures
        #[trigger] (s1 =~= s2) <==> {
            &&& s1.len() == s2.len()
            &&& forall|i: int| 0 <= i < s1.len() ==> s1[i] == s2[i]
        },
{
    if s1.len() =~= s2.len()
        && forall|i: int| 0 <= i < s1.len() ==> s1[i] == s2[i] {
        seq_extensional_equality_index(s1, s2);
    }
}

#[verifier(external_body)]
// #[verifier(broadcast_forall)]
pub proof fn axiom_seq_ext_equal<A>(s1: Seq<A>, s2: Seq<A>)
    ensures
        #[trigger] (s1 =~= s2) <==> {
            &&& s1.len() == s2.len()
            &&& forall|i: int| 0 <= i < s1.len() ==> s1[i] == s2[i]
        },
{
}

proof fn lemma_seq_ext_equal_deep<A>(s1: Seq<A>, s2: Seq<A>)
    ensures
        #[trigger] (s1 =~~= s2) <==> {
            &&& s1.len() == s2.len()
            &&& forall|i: int| 0 <= i < s1.len() ==> s1[i] =~~= s2[i]
        },
{
    if s1.len() =~~= s2.len()
        && forall|i: int| 0 <= i < s1.len() ==> s1[i] =~~= s2[i] {
        seq_extensional_equality_index(s1, s2);
    }
}

#[verifier(external_body)]
// #[verifier(broadcast_forall)]
pub proof fn axiom_seq_ext_equal_deep<A>(s1: Seq<A>, s2: Seq<A>)
    ensures
        #[trigger] (s1 =~~= s2) <==> {
            &&& s1.len() == s2.len()
            &&& forall|i: int| 0 <= i < s1.len() ==> s1[i] =~~= s2[i]
        },
{
}

proof fn lemma_seq_subrange_len<A>(s: Seq<A>, j: int, k: int)
    requires
        0 <= j <= k <= s.len(),
    ensures
        #[trigger] s.subrange(j, k).len() == k - j,
    decreases s
{
    match s {
        Seq::Nil => {}
        Seq::Cons(a, l) => {
            if j > 0 {
                lemma_seq_subrange_len(*l, j-1, k-1);
            } else {
                if k > 0 {
                    lemma_seq_subrange_len(*l, j, k-1);
                }
            }
        }
    }
}

#[verifier(external_body)]
// #[verifier(broadcast_forall)]
pub proof fn axiom_seq_subrange_len<A>(s: Seq<A>, j: int, k: int)
    requires
        0 <= j <= k <= s.len(),
    ensures
        #[trigger] s.subrange(j, k).len() == k - j,
{
}

proof fn lemma_seq_subrange_index<A>(s: Seq<A>, j: int, k: int, i: int)
    requires
        0 <= j <= k <= s.len(),
        0 <= i < k - j,
    ensures
        s.subrange(j, k)[i] == s[i + j],
    decreases s
{
    match s {
        Seq::Nil => {}
        Seq::Cons(a, l) => {
            if j > 0 {
                lemma_seq_subrange_index(*l, j-1, k-1, i);
            } else {
                if k > 0 && i > 0 {
                    lemma_seq_subrange_index(*l, j, k-1, i-1);
                }
            }
        }
    }
}

#[verifier(external_body)]
// #[verifier(broadcast_forall)]
pub proof fn axiom_seq_subrange_index<A>(s: Seq<A>, j: int, k: int, i: int)
    requires
        0 <= j <= k <= s.len(),
        0 <= i < k - j,
    ensures
        s.subrange(j, k)[i] == s[i + j],
{
}

proof fn lemma_seq_add_len<A>(s1: Seq<A>, s2: Seq<A>)
    ensures #[trigger] s1.add(s2).len() == s1.len() + s2.len()
    decreases s1
{
    match s1 {
        Seq::Nil => {}
        Seq::Cons(x, l) => {
            lemma_seq_add_len(*l, s2);
        }
    }
}

#[verifier(external_body)]
// #[verifier(broadcast_forall)]
pub proof fn axiom_seq_add_len<A>(s1: Seq<A>, s2: Seq<A>)
    ensures #[trigger] s1.add(s2).len() == s1.len() + s2.len()
{
}

proof fn lemma_seq_add_index1<A>(s1: Seq<A>, s2: Seq<A>, i: int)
    // 0 <= i not required
    requires
        i < s1.len(),
    ensures
        s1.add(s2)[i] == s1[i],
    decreases s1
{
    if !(0 <= i) {
        seq_index_out_of_bounds(s1.add(s2), i);
        seq_index_out_of_bounds(s1, i);
        return;
    }
    match s1 {
        Seq::Nil => {}
        Seq::Cons(a, l) => {
            lemma_seq_add_index1(*l, s2, i-1);
        }
    }
}

#[verifier(external_body)]
// #[verifier(broadcast_forall)]
pub proof fn axiom_seq_add_index1<A>(s1: Seq<A>, s2: Seq<A>, i: int)
    requires
        0 <= i < s1.len(),
    ensures
        s1.add(s2)[i] == s1[i],
{
}

proof fn lemma_seq_add_index2<A>(s1: Seq<A>, s2: Seq<A>, i: int)
    requires
        0 <= s1.len() <= i,
        // precondition not required
        // i < s1.len() as int + s2.len(),
    ensures
        s1.add(s2)[i] == s2[i - s1.len()],
    decreases s1
{
    lemma_seq_add_len(s1, s2);
    if !(i < s1.len() as int + s2.len()) {
        seq_index_out_of_bounds(s1.add(s2), i);
        seq_index_out_of_bounds(s2, i - s1.len());
        return;
    }
    match s1 {
        Seq::Nil => {}
        Seq::Cons(a, l) => {
            lemma_seq_add_index2(*l, s2, i-1);
        }
    }
}

#[verifier(external_body)]
// #[verifier(broadcast_forall)]
pub proof fn axiom_seq_add_index2<A>(s1: Seq<A>, s2: Seq<A>, i: int)
    requires
        0 <= s1.len(),
        i < s1.len() as int + s2.len(),
    ensures
        s1.add(s2)[i] == s2[i - s1.len()],
{
}

} // verus!
